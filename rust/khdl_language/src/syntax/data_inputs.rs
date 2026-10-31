use crate::front::diagnostic::{DiagResult, DiagnosticError, Diagnostics};
use crate::syntax::pos::Span;
use crate::syntax::source::{FileId, SourceDatabase};
use crate::syntax::token::str_is_valid_identifier;
use indexmap::IndexMap;

/// Similar to [SourceHierarchy], but for data instead of source files.
#[derive(Clone, Default)]
pub struct DataInputs {
    entries: IndexMap<Vec<String>, (FileId, Span)>,
}

impl DataInputs {
    pub fn new() -> Self {
        Self::default()
    }

    pub fn add_file(
        &mut self,
        diags: &Diagnostics,
        source: &SourceDatabase,
        span: Span,
        steps: &[String],
        file: FileId,
    ) -> DiagResult {
        if steps.is_empty() || steps.iter().any(|s| !str_is_valid_identifier(s)) {
            return Err(diags.report_error_simple(
                format!("invalid data path `{}`", steps.join(".")),
                span,
                format!(
                    "expected a nonempty path of identifiers for `{}`",
                    source[file].debug_info_path
                ),
            ));
        }
        if let Some(&(previous_file, previous_span)) = self.entries.get(steps) {
            return Err(DiagnosticError::new(
                format!("duplicate data path `{}`", steps.join(".")),
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
        self.entries.insert(steps.to_vec(), (file, span));
        Ok(())
    }

    pub fn files(&self) -> impl Iterator<Item = FileId> {
        self.entries.values().map(|&(file, _)| file)
    }

    pub fn find(&self, name: &str) -> Option<FileId> {
        let steps: Vec<_> = name.split('.').map(str::to_owned).collect();
        self.entries.get(&steps).map(|&(file, _)| file)
    }
}
