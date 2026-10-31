use crate::front::diagnostic::{DiagResult, Diagnostics};
use crate::syntax::pos::Span;
use crate::syntax::source::{FileId, SourceDatabase};
use crate::syntax::token::str_is_valid_identifier;
use crate::util::data::VecExt;
use toml::Spanned;
use toml::de::{DeTable, DeValue};

// TODO maybe add default elaboration root(s)
// TODO allow manifests to refer to other manifests
// TODO add external verilog filelist, at some point we can parse it to avoid manual "external" declarations
// TODO allow marking certain files as "external", meaning that eg. format should not format them
#[derive(Debug, Clone)]
pub struct Manifest {
    pub source: ManifestFiles,
    pub data: ManifestFiles,
}

#[derive(Debug, Clone, Default)]
pub struct ManifestFiles {
    entries: Vec<FileEntry>,
}

impl Manifest {
    pub fn parse_toml(diags: &Diagnostics, source: &SourceDatabase, file: FileId) -> DiagResult<Manifest> {
        // Note: it's important that the `toml` crate feature `preserve_order` is enabled,
        //   since the order of fields in the manifest can be significant, especially for the resulting error messages.
        let content = &source[file].content;

        let root = DeTable::parse(content).map_err(|e| {
            let span = match e.span() {
                None => source.full_span(file),
                Some(range) => file.span(range),
            };
            diags.report_error_simple(
                format!("failed to parse manifest: {}", e.message()),
                span,
                "while parsing manifest here",
            )
        })?;

        let mut manifest_source = None;
        let mut manifest_data = None;
        for (key, value) in root.get_ref() {
            match key.get_ref().as_ref() {
                "source" => manifest_source = Some(collect_manifest_files(diags, file, value)?),
                "data" => manifest_data = Some(collect_manifest_files(diags, file, value)?),
                other => {
                    return Err(diags.report_error_simple(
                        format!("unknown manifest field `{other}`"),
                        file.span(key.span()),
                        "unknown field here",
                    ));
                }
            }
        }

        let source = manifest_source.ok_or_else(|| {
            diags.report_error_simple(
                "manifest is missing the `source` field",
                Span::empty_at(source.full_span(file).start()),
                "expected `source` field in this manifest",
            )
        })?;
        let data = manifest_data.unwrap_or_default();
        Ok(Manifest { source, data })
    }
}

fn collect_manifest_files(diags: &Diagnostics, file: FileId, node: &Spanned<DeValue>) -> DiagResult<ManifestFiles> {
    let mut entries = vec![];
    collect_manifest_files_impl(diags, file, &mut vec![], node, &mut entries)?;
    Ok(ManifestFiles { entries })
}

fn collect_manifest_files_impl(
    diags: &Diagnostics,
    file: FileId,
    steps: &mut Vec<String>,
    node: &Spanned<DeValue>,
    entries: &mut Vec<FileEntry>,
) -> DiagResult {
    match node.get_ref() {
        DeValue::String(path) => {
            entries.push(FileEntry {
                span_path: file.span(node.span()),
                steps: steps.clone(),
                path_relative: path.to_string(),
            });
            Ok(())
        }
        DeValue::Table(table) => {
            for (key, value) in table {
                let key_str = key.get_ref().as_ref();
                if key_str == "_" {
                    collect_manifest_files_impl(diags, file, steps, value, entries)?;
                } else {
                    if !str_is_valid_identifier(key_str) {
                        return Err(diags.report_error_simple(
                            format!("invalid identifier `{key_str}` in package path"),
                            file.span(key.span()),
                            "invalid identifier here",
                        ));
                    }
                    steps.with_pushed(key_str.to_owned(), |steps| {
                        collect_manifest_files_impl(diags, file, steps, value, entries)
                    })?;
                }
            }
            Ok(())
        }
        _ => Err(diags.report_error_simple(
            "invalid manifest file entry",
            file.span(node.span()),
            "expected a path string or a table of entries",
        )),
    }
}

#[derive(Debug, Clone)]
pub struct FileEntry {
    pub span_path: Span,

    pub steps: Vec<String>,
    pub path_relative: String,
}

impl ManifestFiles {
    pub fn entries(&self) -> &[FileEntry] {
        &self.entries
    }
}
