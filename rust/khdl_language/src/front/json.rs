//! Pure, typed JSON conversion. Inputs are collected before elaboration; this module does no IO.
use crate::front::compile::{CompileItemContext, CompileRefs, ImportValue, StackEntry};
use crate::front::diagnostic::{DiagResult, DiagnosticError};
use crate::front::function::{FunctionBody, FunctionValue};
use crate::front::item::{ElaboratedEnum, ElaboratedStruct, FunctionItemBody, UniqueDeclaration};
use crate::front::types::{Type, Typed};
use crate::front::value::{CompileCompoundValue, CompileValue, EnumValue, SimpleCompileValue, StructValue};
use crate::syntax::pos::{Span, Spanned};
use crate::syntax::source::FileId;
use crate::syntax::token::str_is_valid_identifier;
use crate::util::big_int::{BigInt, BigUint};
use json_syntax::{JsonCodeMap, JsonParse, JsonValue};
use std::collections::HashMap;
use std::sync::Arc;

struct Schema {
    name: String,
    // Only declaration spans are reusable across cached calls; primitive root targets have none.
    span: Option<Span>,
    kind: SchemaKind,
}

enum SchemaKind {
    Bool,
    String,
    Int(Type),
    Array(Box<Schema>, Option<BigUint>),
    Tuple(Vec<Schema>),
    Struct(ElaboratedStruct, Vec<(String, Schema)>),
    Enum(ElaboratedEnum, Vec<(String, Option<Schema>)>),
    Option(ElaboratedEnum, usize, usize, Box<Schema>),
}

impl Schema {
    fn prepare(
        refs: CompileRefs,
        ty: &Type,
        option: UniqueDeclaration,
        mut span: Option<Span>,
        caller: Span,
    ) -> Result<Self, DiagnosticError> {
        let name = ty.value_string(refs);
        let arenas = &refs.shared.elaboration_arenas;
        let kind = match ty {
            Type::Bool => SchemaKind::Bool,
            Type::String => SchemaKind::String,
            Type::Int(_) => SchemaKind::Int(ty.clone()),
            Type::Array(inner, len) => {
                SchemaKind::Array(Box::new(Self::prepare(refs, inner, option, span, caller)?), len.clone())
            }
            Type::Tuple(Some(types)) => SchemaKind::Tuple(
                types
                    .iter()
                    .map(|t| Self::prepare(refs, t, option, span, caller))
                    .collect::<Result<_, _>>()?,
            ),
            &Type::Struct(elab) => {
                let info = arenas.struct_info(elab);
                span.get_or_insert(info.span_body);
                let fields = info
                    .fields
                    .iter()
                    .map(|(id, (_, ty))| {
                        Ok((
                            id.str(&refs.shared.interner).to_owned(),
                            Self::prepare(refs, &ty.inner, option, Some(ty.span), caller)?,
                        ))
                    })
                    .collect::<Result<_, DiagnosticError>>()?;
                SchemaKind::Struct(elab, fields)
            }
            &Type::Enum(elab) => {
                let info = arenas.enum_info(elab);
                span.get_or_insert(info.span_body);
                if info.unique == option {
                    let none = info
                        .variants
                        .keys()
                        .position(|id| id.str(&refs.shared.interner) == "None")
                        .unwrap();
                    let some = info
                        .variants
                        .keys()
                        .position(|id| id.str(&refs.shared.interner) == "Some")
                        .unwrap();
                    let payload = info.variants.get_index(some).unwrap().1.payload_ty.as_ref().unwrap();
                    let inner = Self::prepare(refs, &payload.inner, option, Some(payload.span), caller)?;
                    if inner.accepts_json_null() {
                        return Err(DiagnosticError::new(
                            "ambiguous JSON option schema",
                            caller,
                            "an option payload must not itself accept JSON null",
                        )
                        .add_info(span.unwrap_or(caller), "option schema defined here")
                        .add_info(
                            inner.span.unwrap_or(caller),
                            "null cannot distinguish None from Some(None)",
                        ));
                    }
                    SchemaKind::Option(elab, none, some, Box::new(inner))
                } else {
                    let variants = info
                        .variants
                        .iter()
                        .map(|(id, v)| {
                            Ok((
                                id.str(&refs.shared.interner).to_owned(),
                                v.payload_ty
                                    .as_ref()
                                    .map(|ty| Self::prepare(refs, &ty.inner, option, Some(ty.span), caller))
                                    .transpose()?,
                            ))
                        })
                        .collect::<Result<_, DiagnosticError>>()?;
                    SchemaKind::Enum(elab, variants)
                }
            }
            _ => {
                return Err(DiagnosticError::new(
                    "unsupported JSON destination type",
                    caller,
                    format!("JSON conversion to `{name}` is not supported yet"),
                )
                .add_info(span.unwrap_or(caller), "unsupported schema member defined here"));
            }
        };
        Ok(Self { name, span, kind })
    }

    fn annotate(&self, error: DiagnosticError) -> DiagnosticError {
        let expected = format!("expected `{}`", self.name);
        match self.span {
            Some(span) => error.add_info(span, expected),
            None => error.add_footer_info(expected),
        }
    }

    fn accepts_json_null(&self) -> bool {
        // Extend this predicate when arbitrary `any` conversion gains a null representation.
        matches!(self.kind, SchemaKind::Option(..))
    }

    fn decode(
        &self,
        value: &JsonValue,
        offset: usize,
        doc: &Document,
        path: &str,
    ) -> Result<CompileValue, DiagnosticError> {
        let span = doc.span(offset);
        let error = |message: String| {
            let error = DiagnosticError::new(
                "JSON value does not match destination type",
                span,
                format!("{path}: {message}"),
            );
            self.annotate(error)
        };
        let compound = |v| CompileValue::Compound(v);
        match (&self.kind, value) {
            (SchemaKind::Option(ty, none, some, inner), _) => {
                let (variant, payload) = if matches!(value, JsonValue::Null) {
                    (*none, None)
                } else {
                    (*some, Some(Box::new(inner.decode(value, offset, doc, path)?)))
                };
                Ok(compound(CompileCompoundValue::Enum(EnumValue {
                    ty: *ty,
                    variant,
                    payload,
                })))
            }
            (SchemaKind::Bool, JsonValue::Boolean(v)) => Ok(CompileValue::new_bool(*v)),
            (SchemaKind::String, JsonValue::String(v)) => {
                Ok(compound(CompileCompoundValue::String(Arc::new(v.to_string()))))
            }
            (SchemaKind::Int(ty), JsonValue::Number(_)) => {
                let text = &doc.text[span.start_byte..span.end_byte];
                if text.contains(['.', 'e', 'E']) {
                    return Err(error("fractional and exponent notation are not supported".into()));
                }
                let magnitude = BigUint::from_str_radix(text.trim_start_matches('-'), 10)
                    .map_err(|_| error("invalid integer".into()))?;
                let integer = BigInt::from(magnitude);
                let v = CompileValue::new_int(if text.starts_with('-') { -integer } else { integer });
                if !ty.contains_type(&v.ty()) {
                    return Err(error("integer is outside the destination range".into()));
                }
                Ok(v)
            }
            (SchemaKind::Array(inner, length), JsonValue::Array(values)) => {
                if length.as_ref().is_some_and(|n| n != &BigUint::from(values.len())) {
                    return Err(error(format!("wrong array length: got {}", values.len())));
                }
                let mut child = offset + 1;
                let mut result = Vec::with_capacity(values.len());
                for (i, v) in values.iter().enumerate() {
                    result.push(inner.decode(v, child, doc, &format!("{path}[{i}]"))?);
                    child += doc.map[child].volume;
                }
                Ok(CompileValue::Simple(SimpleCompileValue::Array(Arc::new(result))))
            }
            (SchemaKind::Tuple(types), JsonValue::Array(values)) => {
                if types.len() != values.len() {
                    return Err(error(format!("wrong tuple length: got {}", values.len())));
                }
                let mut child = offset + 1;
                let mut result = Vec::with_capacity(values.len());
                for (i, (schema, v)) in types.iter().zip(values.iter()).enumerate() {
                    result.push(schema.decode(v, child, doc, &format!("{path}[{i}]"))?);
                    child += doc.map[child].volume;
                }
                Ok(compound(CompileCompoundValue::Tuple(result)))
            }
            (SchemaKind::Struct(ty, fields), JsonValue::Object(object)) => {
                let mut entries = object_entries(object, offset, doc);
                for (name, (_, _, key_span)) in &entries {
                    if !fields.iter().any(|(field, _)| field == name) {
                        return Err(self.annotate(DiagnosticError::new(
                            "unknown JSON field",
                            *key_span,
                            format!("{path}: unexpected field `{name}`"),
                        )));
                    }
                }
                let mut result = Vec::with_capacity(fields.len());
                for (name, schema) in fields {
                    // Future language-defined field defaults belong at this missing-field boundary.
                    let (v, child, _) = entries
                        .shift_remove(name.as_str())
                        .ok_or_else(|| error(format!("missing field `{name}`")))?;
                    result.push(schema.decode(v, child, doc, &format!("{path}[{name:?}]"))?);
                }
                Ok(compound(CompileCompoundValue::Struct(StructValue {
                    ty: *ty,
                    fields: result,
                })))
            }
            (SchemaKind::Enum(ty, variants), _) => {
                let (name, payload, tag_span) = match value {
                    JsonValue::String(name) => (name.as_str(), None, span),
                    JsonValue::Object(object) if object.len() == 1 => {
                        let entries = object_entries(object, offset, doc);
                        let (name, (value, child, key)) = entries.into_iter().next().unwrap();
                        (name, Some((value, child)), key)
                    }
                    _ => return Err(error("expected a variant name or single-entry tagged object".into())),
                };
                let variant = variants.iter().position(|(n, _)| n == name).ok_or_else(|| {
                    self.annotate(DiagnosticError::new(
                        "unknown JSON enum variant",
                        tag_span,
                        format!("{path}: unknown variant `{name}`"),
                    ))
                })?;
                let payload = match (&variants[variant].1, payload) {
                    (None, None) => None,
                    (Some(schema), Some((v, child))) => {
                        Some(Box::new(schema.decode(v, child, doc, &format!("{path}[{name:?}]"))?))
                    }
                    _ => return Err(error("variant payload does not match its declaration".into())),
                };
                Ok(compound(CompileCompoundValue::Enum(EnumValue {
                    ty: *ty,
                    variant,
                    payload,
                })))
            }
            _ => Err(error("wrong JSON value kind".into())),
        }
    }
}

struct Document<'a> {
    file: FileId,
    text: &'a str,
    map: JsonCodeMap,
}
impl Document<'_> {
    fn span(&self, offset: usize) -> Span {
        let span = self.map[offset].span;
        self.file.span(span.start..span.end)
    }
}

fn object_entries<'a>(
    object: &'a json_syntax::JsonObject,
    offset: usize,
    doc: &Document,
) -> indexmap::IndexMap<&'a str, (&'a JsonValue, usize, Span)> {
    let mut entries = indexmap::IndexMap::new();
    let mut child = offset + 1;
    for (name, value) in object.entries() {
        entries.insert(name.as_str(), (value, child + 2, doc.span(child + 1)));
        child += doc.map[child].volume;
    }
    entries
}

// Check the complete document, including payloads whose schema conversion may fail earlier.
fn check_duplicates(value: &JsonValue, offset: usize, doc: &Document) -> Result<(), DiagnosticError> {
    let mut child = offset + 1;
    match value {
        JsonValue::Object(object) => {
            let mut seen = HashMap::new();
            for (name, value) in object.entries() {
                let span = doc.span(child + 1);
                if let Some(previous) = seen.insert(name.as_str(), span) {
                    return Err(DiagnosticError::new(
                        "duplicate JSON field",
                        span,
                        format!("duplicate field `{name}`"),
                    )
                    .add_info(previous, "first occurrence here"));
                }
                check_duplicates(value, child + 2, doc)?;
                child += doc.map[child].volume;
            }
        }
        JsonValue::Array(values) => {
            for value in values.iter() {
                check_duplicates(value, child, doc)?;
                child += doc.map[child].volume;
            }
        }
        _ => {}
    }
    Ok(())
}

impl CompileItemContext<'_, '_> {
    pub fn load_json(
        &mut self,
        name: Spanned<&str>,
        ty: Spanned<Type>,
        builtin_span: Span,
    ) -> DiagResult<CompileValue> {
        let refs = self.refs;
        let caller = self
            .call_stack
            .iter()
            .rev()
            .find_map(|entry| match entry {
                StackEntry::FunctionCall(span) => Some(*span),
                _ => None,
            })
            .unwrap_or(builtin_span);
        let report = |error: DiagnosticError| error.add_info(caller, "JSON loaded here").report(refs.diags);
        refs.check_should_stop(caller)?;
        if name.inner.split('.').any(|s| !str_is_valid_identifier(s)) {
            return Err(report(DiagnosticError::new(
                "invalid data alias",
                caller,
                "expected a dot-separated path of identifiers, not a filesystem path",
            )));
        }
        let file = refs.fixed.data.find(name.inner).ok_or_else(|| {
            report(DiagnosticError::new(
                format!("unknown data alias `{}`", name.inner),
                caller,
                "data inputs must be declared in the manifest",
            ))
        })?;
        let item = match refs.resolve_path(Spanned::new(builtin_span, "std.types.Option"), false)? {
            ImportValue::Item(item) => item,
            _ => unreachable!(),
        };
        let option = match refs.eval_item(item)? {
            CompileValue::Simple(SimpleCompileValue::Function(FunctionValue::User(function))) => {
                match &function.body.inner {
                    FunctionBody::ItemBody(FunctionItemBody::Enum(unique, _)) => *unique,
                    _ => unreachable!(),
                }
            }
            _ => unreachable!(),
        };
        // Prepare before OnceLock initialization: no user elaboration occurs inside the cache computation.
        let schema = Schema::prepare(refs, &ty.inner, option, None, caller).map_err(report)?;
        let result = refs
            .shared
            .elaboration_arenas
            .json_values
            .get_or_compute((file, ty.inner), |_| {
                let text = &refs.fixed.source[file].content;
                let (value, map) = JsonValue::parse_str(text).map_err(|error| {
                    let range = error.span();
                    let end = if range.start == range.end {
                        text[range.start..]
                            .chars()
                            .next()
                            .map_or(range.end, |c| range.start + c.len_utf8())
                    } else {
                        range.end
                    };
                    DiagnosticError::new("invalid JSON", file.span(range.start..end), error.to_string())
                })?;
                let doc = Document { file, text, map };
                check_duplicates(&value, 0, &doc)?;
                schema.decode(&value, 0, &doc, "$")
            });
        result.clone().map_err(report)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::front::diagnostic::Diagnostics;
    use crate::syntax::source::SourceDatabase;
    use crate::util::range_multi::MultiRange;

    #[test]
    fn duplicate_keys_keep_both_original_byte_ranges() {
        let text = " {\"é\":1,\"\\u00e9\":2}";
        let mut source = SourceDatabase::new();
        let file = source.add_file("input.json".into(), text.into());
        let (value, map) = JsonValue::parse_str(text).unwrap();
        let doc = Document { file, text, map };
        let diags = Diagnostics::new();
        let _ = check_duplicates(&value, 0, &doc).unwrap_err().report(&diags);
        let diagnostics = diags.finish();
        let content = &diagnostics[0].content;
        assert_eq!(
            source.span_str(content.messages.iter().next().unwrap().0),
            "\"\\u00e9\""
        );
        assert_eq!(source.span_str(content.infos[0].0), "\"é\"");
    }

    #[test]
    fn integer_roots_at_eof_preserve_precision_and_full_spans() {
        for text in ["1", "-12", "1234567890123456789012345678901234567890"] {
            let mut source = SourceDatabase::new();
            let file = source.add_file("input.json".into(), text.into());
            let (value, map) = JsonValue::parse_str(text).unwrap();
            let doc = Document { file, text, map };
            assert_eq!(source.span_str(doc.span(0)), text);
            let schema = Schema {
                name: "int".into(),
                span: Some(doc.span(0)),
                kind: SchemaKind::Int(Type::Int(MultiRange::open())),
            };
            let CompileValue::Simple(SimpleCompileValue::Int(result)) = schema.decode(&value, 0, &doc, "$").unwrap()
            else {
                panic!()
            };
            assert_eq!(result.to_string(), text);
        }
    }
}
