use crate::front::compile::{CompileItemContext, CompileRefs, ImportValue};
use crate::front::diagnostic::{DiagError, DiagResult, DiagnosticError, Diagnostics};
use crate::front::function::{FunctionBody, FunctionValue};
use crate::front::item::{ElaboratedEnum, ElaboratedStruct, FunctionItemBody, UniqueDeclaration};
use crate::front::types::Type;
use crate::front::value::{CompileCompoundValue, CompileValue, EnumValue, SimpleCompileValue, StructValue};
use crate::syntax::pos::{Span, Spanned};
use crate::syntax::source::FileId;
use crate::util::big_int::{BigInt, BigUint};
use crate::util::iter::IterExt;
use crate::util::range_multi::{AnyMultiRange, MultiRange};
use itertools::{Itertools, zip_eq};
use json_syntax::{JsonCodeMap, JsonParse, JsonValue};
use std::sync::Arc;

struct Schema {
    ty: Spanned<Type>,
    kind: SchemaKind,
}

enum SchemaKind {
    Bool,
    String,
    Int(MultiRange<BigInt>),
    Array(Box<Schema>, Option<BigUint>),
    Tuple(Vec<Schema>),
    Struct(ElaboratedStruct, Vec<Schema>),
    Enum(ElaboratedEnum, Vec<Option<Schema>>),
    Option(ElaboratedEnum, usize, usize, Box<Schema>),
}

#[derive(Copy, Clone)]
struct SchemaCtx<'a, 's> {
    refs: CompileRefs<'a, 's>,
    span_caller: Span,
    option: UniqueDeclaration,
}

impl Schema {
    fn from_ty(ctx: SchemaCtx, span_ty: Span, ty: &Type) -> Result<Self, DiagError> {
        let refs = ctx.refs;
        let diags = refs.diags;
        let elab = &refs.shared.elaboration_arenas;

        let kind = match ty {
            Type::Bool => SchemaKind::Bool,
            Type::String => SchemaKind::String,
            Type::Int(range) => SchemaKind::Int(range.clone()),
            Type::Array(inner, len) => SchemaKind::Array(Box::new(Schema::from_ty(ctx, span_ty, inner)?), len.clone()),
            Type::Tuple(Some(types)) => SchemaKind::Tuple(
                types
                    .iter()
                    .map(|t| Schema::from_ty(ctx, span_ty, t))
                    .try_collect_all_vec()?,
            ),
            &Type::Struct(elab_struct) => {
                let info = elab.struct_info(elab_struct);
                let fields = info
                    .fields
                    .values()
                    .map(|(_, ty)| Schema::from_ty(ctx, ty.span, &ty.inner))
                    .try_collect_all_vec()?;
                SchemaKind::Struct(elab_struct, fields)
            }
            &Type::Enum(elab_enum) => {
                let info = elab.enum_info(elab_enum);

                if info.unique == ctx.option {
                    let index_none = info
                        .variants
                        .keys()
                        .position(|id| id.str(&refs.shared.interner) == "None")
                        .unwrap();
                    let index_some = info
                        .variants
                        .keys()
                        .position(|id| id.str(&refs.shared.interner) == "Some")
                        .unwrap();

                    let payload_ty = info
                        .variants
                        .get_index(index_some)
                        .unwrap()
                        .1
                        .payload_ty
                        .as_ref()
                        .unwrap();

                    let payload_schema = Schema::from_ty(ctx, payload_ty.span, &payload_ty.inner)?;
                    if payload_schema.accepts_null() {
                        let ty_str = ty.value_string(refs);
                        let payload_ty_str = payload_ty.inner.value_string(refs);
                        let e = DiagnosticError::new(
                            "JSON: ambiguous option type",
                            ctx.span_caller,
                            "during json loading here",
                        )
                        .add_info(span_ty, format!("type set to `{ty_str}`"))
                        .add_info(payload_ty.span, format!("payload type set to `{payload_ty_str}`"))
                        .add_footer_info("json `null` is ambiguous between `None` and `Some(None)`")
                        .report(diags);
                        return Err(e);
                    }
                    SchemaKind::Option(elab_enum, index_none, index_some, Box::new(payload_schema))
                } else {
                    let variants = info
                        .variants
                        .values()
                        .map(|v| {
                            v.payload_ty
                                .as_ref()
                                .map(|payload_ty| Schema::from_ty(ctx, payload_ty.span, &payload_ty.inner))
                                .transpose()
                        })
                        .try_collect_all_vec()?;
                    SchemaKind::Enum(elab_enum, variants)
                }
            }
            _ => {
                let ty_str = ty.value_string(refs);
                let e = DiagnosticError::new(
                    format!("JSON: unsupported destination type `{ty_str}`"),
                    ctx.span_caller,
                    "JSON conversion here",
                )
                .add_info(span_ty, "type set here")
                .report(diags);
                return Err(e);
            }
        };
        Ok(Schema {
            ty: Spanned::new(span_ty, ty.clone()),
            kind,
        })
    }

    fn accepts_null(&self) -> bool {
        // Extend this predicate when we implement arbitrary `any` conversion, which is also ambiguous.
        matches!(self.kind, SchemaKind::Option(..))
    }

    fn decode(
        &self,
        refs: CompileRefs,
        span_caller: Span,
        doc: &Document,
        path: &str,
        offset: usize,
        value: &JsonValue,
    ) -> Result<CompileValue, DiagError> {
        let diags = refs.diags;
        let elab = &refs.shared.elaboration_arenas;
        let interner = &refs.shared.interner;

        let value_span = doc.span(offset);

        let error = |title: &str| {
            let title = format!("JSON: {title}");
            DiagnosticError::new(title, value_span, "here")
                .add_info(
                    self.ty.span,
                    format!("type `{}` set here", self.ty.inner.value_string(refs)),
                )
                .add_info(span_caller, "during json loading here")
                .add_footer_info(format!("while parsing `{path}`"))
        };

        let decode_int = |range: &MultiRange<BigInt>, text: &str| {
            let (negative, magnitude) = match text.strip_prefix('-') {
                None => (false, text),
                Some(magnitude) => (true, magnitude),
            };
            let magnitude =
                BigUint::from_str_radix(magnitude, 10).map_err(|_| error("invalid integer literal").report(diags))?;
            let value = if negative { -magnitude } else { magnitude.into() };

            if !range.contains(&value) {
                return Err(error("integer value out of range").report(diags));
            }
            Ok(CompileValue::new_int(value))
        };

        match (&self.kind, value) {
            // trivial cases
            (SchemaKind::Bool, &JsonValue::Boolean(v)) => Ok(CompileValue::new_bool(v)),
            (SchemaKind::String, JsonValue::String(v)) => Ok(CompileValue::Compound(CompileCompoundValue::String(
                Arc::new(v.to_string()),
            ))),

            // int: accept both number and string
            (SchemaKind::Int(range), JsonValue::Number(_)) => {
                // re-parse to preserve full precision
                let text = &doc.content[value_span.start_byte..value_span.end_byte];
                decode_int(range, text)
            }
            (SchemaKind::Int(range), JsonValue::String(s)) => {
                // also accept string to help languages that cannot write full-precision json numbers
                decode_int(range, s.as_str())
            }

            // compound values
            (SchemaKind::Array(inner, length), JsonValue::Array(values)) => {
                if let Some(length) = length
                    && length != &BigUint::from(values.len())
                {
                    let title = format!("array length mismatch: expected {length}, got {}", values.len());
                    return Err(error(&title).report(diags));
                }

                let mut child = offset + 1;
                let mut result = Vec::with_capacity(values.len());
                for (i, v) in values.iter().enumerate() {
                    let child_path = format!("{path}[{i}]");
                    result.push(inner.decode(refs, span_caller, doc, &child_path, child, v)?);
                    child += doc.map[child].volume;
                }

                Ok(CompileValue::Simple(SimpleCompileValue::Array(Arc::new(result))))
            }
            (SchemaKind::Tuple(types), JsonValue::Array(values)) => {
                if types.len() != values.len() {
                    return Err(error("tuple length mismatch").report(diags));
                }

                let mut child = offset + 1;
                let mut result = Vec::with_capacity(values.len());
                for (i, (schema, v)) in types.iter().zip(values.iter()).enumerate() {
                    let child_path = format!("{path}[{i}]");
                    result.push(schema.decode(refs, span_caller, doc, &child_path, child, v)?);
                    child += doc.map[child].volume;
                }

                Ok(CompileValue::Compound(CompileCompoundValue::Tuple(result)))
            }
            (&SchemaKind::Struct(ty, ref fields), JsonValue::Object(object)) => {
                let info = elab.struct_info(ty);

                let mut entries = object_entries(diags, object, offset, doc)?;
                let mut result = Vec::with_capacity(fields.len());
                for ((_, (field_id, _)), field_schema) in zip_eq(&info.fields, fields) {
                    let field_id_str = field_id.inner.str(interner);
                    let (field_value, child, _) = entries.shift_remove(field_id_str).ok_or_else(|| {
                        // TODO fallback to default field value once those exist?
                        error(&format!("missing struct field `{field_id_str}`"))
                            .add_info(field_id.span, "struct field declared here")
                            .report(diags)
                    })?;

                    let child_path = format!("{path}[{field_id_str:?}]");
                    let field_value = field_schema.decode(refs, span_caller, doc, &child_path, child, field_value)?;

                    result.push(field_value);
                }

                if !entries.is_empty() {
                    let fields = if entries.len() > 1 { "fields" } else { "field" };
                    let ids = entries.keys().map(|k| format!("`{k}`")).join(", ");
                    let e = error(&format!("leftover struct {fields}: {ids}"))
                        .add_info(info.span_body, "struct fields declared here")
                        .report(diags);
                    return Err(e);
                }

                let result = StructValue { ty, fields: result };
                Ok(CompileValue::Compound(CompileCompoundValue::Struct(result)))
            }
            (&SchemaKind::Enum(ty, ref variant_schemas), _) => {
                let info = elab.enum_info(ty);

                let (variant_str, payload_value, tag_span) = match value {
                    JsonValue::String(name) => (name.as_str(), None, value_span),
                    JsonValue::Object(object) if object.len() == 1 => {
                        let entries = object_entries(diags, object, offset, doc)?;
                        let (name, (value, child, key)) = entries.into_iter().next().unwrap();
                        (name, Some((value, child)), key)
                    }
                    _ => {
                        let e = error("failed to parse as enum")
                            .add_footer_info("enums should be encoded as  `\"variant\"` or `{ \"variant\": payload }`")
                            .report(diags);
                        return Err(e);
                    }
                };

                let variant_id = interner.push(variant_str);
                let (variant_index, _, variant_info) = info.variants.get_full(&variant_id).ok_or_else(|| {
                    error(&format!("unknown enum variant `{variant_str}`"))
                        .add_info(tag_span, "variant set here")
                        .add_info(info.span_body, "enum variants declared here")
                        .report(diags)
                })?;

                let payload = match (&variant_schemas[variant_index], payload_value) {
                    (None, None) => None,
                    (Some(payload_schema), Some((v, child))) => {
                        let child_path = format!("{path}[{variant_str:?}]");
                        let payload_value = payload_schema.decode(refs, span_caller, doc, &child_path, child, v)?;
                        Some(Box::new(payload_value))
                    }
                    _ => {
                        let (decl_span, with) = match &variant_info.payload_ty {
                            Some(payload_ty) => (payload_ty.span, "with"),
                            None => (variant_info.id.span, "without"),
                        };
                        let e = error("enum payload mismatch")
                            .add_info(decl_span, format!("variant declared {with} payload here"))
                            .report(diags);
                        return Err(e);
                    }
                };

                let result = EnumValue {
                    ty,
                    variant: variant_index,
                    payload,
                };
                Ok(CompileValue::Compound(CompileCompoundValue::Enum(result)))
            }

            // option special case
            (&SchemaKind::Option(elab, none, some, ref inner), _) => {
                let (variant, payload) = match value {
                    JsonValue::Null => (none, None),
                    _ => {
                        let inner = inner.decode(refs, span_caller, doc, path, offset, value)?;
                        (some, Some(Box::new(inner)))
                    }
                };
                let result = EnumValue {
                    ty: elab,
                    variant,
                    payload,
                };
                Ok(CompileValue::Compound(CompileCompoundValue::Enum(result)))
            }

            // mismatch
            _ => {
                let value_kind = value.kind();
                Err(error(&format!("type mismatch, got value kind {value_kind}")).report(diags))
            }
        }
    }
}

struct Document<'a> {
    file: FileId,
    content: &'a str,
    map: JsonCodeMap,
}

impl Document<'_> {
    fn span(&self, offset: usize) -> Span {
        let span = self.map[offset].span;
        self.file.span(span.start..span.end)
    }
}

fn object_entries<'a>(
    diags: &Diagnostics,
    object: &'a json_syntax::JsonObject,
    offset: usize,
    doc: &Document,
) -> Result<indexmap::IndexMap<&'a str, (&'a JsonValue, usize, Span)>, DiagError> {
    let mut entries = indexmap::IndexMap::new();
    let mut child = offset + 1;
    for (name, value) in object.entries() {
        let span = doc.span(child + 1);
        if let Some(&(_, _, previous)) = entries.get(name.as_str()) {
            let e = DiagnosticError::new(
                "JSON: duplicate object field",
                span,
                format!("duplicate field `{name}`"),
            )
            .add_info(previous, "first occurrence here")
            .report(diags);
            return Err(e);
        }
        entries.insert(name.as_str(), (value, child + 2, span));
        child += doc.map[child].volume;
    }
    Ok(entries)
}

impl CompileItemContext<'_, '_> {
    pub fn load_json(&mut self, path: Spanned<&str>, ty: Spanned<Type>, span: Span) -> DiagResult<CompileValue> {
        let refs = self.refs;
        let diags = refs.diags;

        // find std option type
        let item = match refs.resolve_path(Spanned::new(span, "std.types.Option"), false)? {
            ImportValue::Item(item) => item,
            _ => return Err(diags.report_error_internal(span, "failed to find option")),
        };
        let option = match refs.eval_item(item)? {
            CompileValue::Simple(SimpleCompileValue::Function(FunctionValue::User(function))) => {
                match &function.body.inner {
                    &FunctionBody::ItemBody(FunctionItemBody::Enum(unique, _)) => unique,
                    _ => return Err(diags.report_error_internal(span, "unexpected option kind")),
                }
            }
            _ => return Err(diags.report_error_internal(span, "unexpected option kind")),
        };

        // prepare schema
        let schema_ctx = SchemaCtx {
            refs,
            span_caller: span,
            option,
        };
        let schema = Schema::from_ty(schema_ctx, ty.span, &ty.inner)?;

        // find data
        let file = refs.fixed.data_inputs.find(path.inner).ok_or_else(|| {
            DiagnosticError::new(
                format!("could not find data path `{}`", path.inner),
                span,
                "during json loading here",
            )
            .add_footer_info("data inputs must be declared in the manifest")
            .report(diags)
        })?;
        let content = &refs.fixed.source[file].content;

        // parse string to json
        let (value, map) = JsonValue::parse_str(content).map_err(|e| {
            let range = e.span();
            let end = if range.start == range.end {
                content[range.start..]
                    .chars()
                    .next()
                    .map_or(range.end, |c| range.start + c.len_utf8())
            } else {
                range.end
            };
            DiagnosticError::new("invalid JSON", file.span(range.start..end), e.to_string()).report(diags)
        })?;

        // convert json to value
        let doc = Document { file, content, map };
        let result = schema.decode(refs, span, &doc, path.inner, 0, &value)?;

        Ok(result)
    }
}
