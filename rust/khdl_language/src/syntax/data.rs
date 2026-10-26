//! Manifest-authorized data, collected before elaboration and kept outside the KHDL hierarchy.
use crate::front::diagnostic::{DiagResult, DiagnosticError, Diagnostics};
use crate::syntax::collect::collect_files_from_tree;
use crate::syntax::manifest::ManifestSource;
use crate::syntax::pos::Span;
use crate::syntax::source::{FileId, SourceDatabase};
use crate::syntax::token::str_is_valid_identifier;
use indexmap::IndexMap;
use path_clean::PathClean;
use std::path::{Path, PathBuf};

#[derive(Clone, Default)]
pub struct DataInputs {
    entries: IndexMap<Vec<String>, (FileId, Span)>,
}

impl DataInputs {
    pub fn new() -> Self {
        Self::default()
    }

    pub fn add(
        &mut self,
        diags: &Diagnostics,
        source: &SourceDatabase,
        steps: Vec<String>,
        file: FileId,
        span: Span,
    ) -> DiagResult {
        if steps.is_empty() || steps.iter().any(|s| !str_is_valid_identifier(s)) {
            return Err(diags.report_error_simple(
                format!("invalid data alias `{}`", steps.join(".")),
                span,
                format!(
                    "expected a nonempty path of identifiers for `{}`",
                    source[file].debug_info_path
                ),
            ));
        }
        if let Some(&(previous_file, previous_span)) = self.entries.get(&steps) {
            return Err(DiagnosticError::new(
                format!("duplicate data alias `{}`", steps.join(".")),
                span,
                format!("data file `{}` declared here", source[file].debug_info_path),
            )
            .add_info(
                previous_span,
                format!(
                    "previous data file `{}` declared here",
                    source[previous_file].debug_info_path
                ),
            )
            .report(diags));
        }
        self.entries.insert(steps, (file, span));
        Ok(())
    }

    pub fn find(&self, name: &str) -> Option<FileId> {
        let steps: Vec<_> = name.split('.').map(str::to_owned).collect();
        self.entries.get(&steps).map(|&(file, _)| file)
    }
}

pub fn collect_data_from_manifest(
    diags: &Diagnostics,
    source: &mut SourceDatabase,
    base: &Path,
    manifest: &ManifestSource,
    mut read: impl FnMut(&Path) -> Result<String, String>,
) -> DiagResult<(DataInputs, IndexMap<FileId, PathBuf>)> {
    let mut data = DataInputs::new();
    let mut paths = IndexMap::new();
    for entry in manifest.entries() {
        let path = base.join(&entry.path_relative).clean();
        let files = collect_files_from_tree(diags, entry.span_path, path, "json")?;
        for (relative_steps, path) in files {
            let mut steps = entry.steps.clone();
            steps.extend(relative_steps);
            let meta = std::fs::metadata(&path).map_err(|e| {
                diags.report_error_simple(
                    format!("cannot read metadata for data file `{}`: {e}", path.display()),
                    entry.span_path,
                    "data declared here",
                )
            })?;
            if !meta.is_file() {
                return Err(diags.report_error_simple(
                    "data input must be a regular file",
                    entry.span_path,
                    format!("unsupported file `{}`", path.display()),
                ));
            }
            let content =
                read(&path).map_err(|e| diags.report_error_simple(e, entry.span_path, "data declared here"))?;
            let file = source.add_file(path.to_string_lossy().into_owned(), content);
            data.add(diags, source, steps, file, entry.span_path)?;
            paths.insert(file, path);
        }
    }
    Ok((data, paths))
}
