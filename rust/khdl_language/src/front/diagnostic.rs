//! This module is strongly inspired by the Rust compiler,
//! see <https://rustc-dev-guide.rust-lang.org/diagnostics.html>.

use crate::syntax::pos::Span;
use crate::syntax::source::{FileId, SourceDatabase};
use crate::util::data::NonEmptyVec;
use annotate_snippets::renderer::{AnsiColor, Color, DEFAULT_HELP_STYLE, DEFAULT_NOTE_STYLE, Style};
use annotate_snippets::{AnnotationKind, Group, Level, Renderer, Snippet};
use indexmap::IndexMap;
use std::backtrace::Backtrace;
use std::cell::RefCell;

/// Indicates that an error was reported as a diagnostic.
///
/// Anything encountering this value should do one of, in order of preference:
/// * Continue on a best-effort basis,
///   allowing future errors that are definitely independent of the previous one to also be reported.
///   The compiler should make optimistic assumptions about whatever value is instead [DiagError].
/// * Propagate this value,
///   blocking any downstream errors that are potentially just caused by the previous error
///   and which would just be noise.
///
/// This value is not publicly constructible, use [Diagnostics::report].
///
/// This concept is the same as
/// [ErrorGuaranteed](https://rustc-dev-guide.rust-lang.org/diagnostics/error-guaranteed.html)
/// from the rust compiler.
#[must_use]
#[derive(Debug, Copy, Clone, Eq, PartialEq, Hash)]
pub struct DiagError(());

pub type DiagResult<T = ()> = Result<T, DiagError>;

#[must_use]
#[derive(Debug, Clone)]
pub struct Diagnostics {
    diagnostics: RefCell<Vec<Diagnostic>>,
}

impl Diagnostics {
    pub fn new() -> Self {
        Self {
            diagnostics: RefCell::new(vec![]),
        }
    }

    pub fn push(&self, diag: Diagnostic) {
        self.diagnostics.borrow_mut().push(diag);
    }

    pub fn report_error_simple(&self, title: impl Into<String>, span: Span, label: impl Into<String>) -> DiagError {
        DiagnosticError::new(title, span, label).report(self)
    }

    #[track_caller]
    pub fn report_error_todo(&self, span: Span, feature: impl AsRef<str>) -> DiagError {
        DiagnosticError::new_todo(feature, span).report(self)
    }

    pub fn report_error_internal(&self, span: Span, reason: impl AsRef<str>) -> DiagError {
        DiagnosticError::new_internal_compiler_error(reason, span).report(self)
    }

    pub fn finish(self) -> Vec<Diagnostic> {
        self.diagnostics.into_inner()
    }

    pub fn len(&self) -> usize {
        self.diagnostics.borrow().len()
    }
}

impl DiagError {
    /// Create a [DiagError], promising that an error has already been reported.
    /// This is very rarely useful outside the diagnostics module itself to statically initialize constants.
    pub const fn promise_error_has_been_reported() -> DiagError {
        DiagError(())
    }
}

#[derive(Debug, Clone)]
pub struct Diagnostic {
    pub level: DiagnosticLevel,
    pub content: DiagnosticContent,
}

#[derive(Debug, Copy, Clone, Eq, PartialEq, Ord, PartialOrd)]
pub enum DiagnosticLevel {
    Error,
    Warning,
}

#[derive(Debug, Copy, Clone, Eq, PartialEq)]
pub enum FooterKind {
    Info,
    Hint,
}

#[must_use]
#[derive(Debug, Clone)]
pub struct DiagnosticError {
    content: DiagnosticContent,
}

#[must_use]
#[derive(Debug, Clone)]
pub struct DiagnosticWarning {
    content: DiagnosticContent,
}

#[derive(Debug, Clone)]
pub struct DiagnosticContent {
    pub title: String,
    pub messages: NonEmptyVec<(Span, String)>,
    pub infos: Vec<(Span, String)>,
    pub footers: Vec<(FooterKind, String)>,
    pub backtrace: Option<String>,
}

impl DiagnosticError {
    pub fn new(title: impl Into<String>, span: Span, message: impl Into<String>) -> Self {
        let content = DiagnosticContent::new(title, span, message);
        Self { content }
    }

    pub fn new_multiple(title: impl Into<String>, messages: NonEmptyVec<(Span, String)>) -> Self {
        let content = DiagnosticContent::new_multiple(title, messages);
        Self { content }
    }

    pub fn new_todo(feature: impl AsRef<str>, span: Span) -> Self {
        let message = format!("feature not yet implemented: {}", feature.as_ref());
        Self::new(message, span, "used here")
    }

    #[track_caller]
    pub fn new_internal_compiler_error(reason: impl AsRef<str>, span: Span) -> Self {
        let message = format!("internal compiler error: {}", reason.as_ref());
        let mut diag = Self::new(message, span, "triggered here");
        diag.content.backtrace = Some(Backtrace::force_capture().to_string());
        diag
    }

    pub fn add_info(mut self, span: Span, info: impl Into<String>) -> Self {
        self.content.add_info(span, info.into());
        self
    }

    pub fn add_footer_info(mut self, message: impl Into<String>) -> Self {
        self.content.add_footer(FooterKind::Info, message);
        self
    }

    pub fn add_footer_hint(mut self, message: impl Into<String>) -> Self {
        self.content.add_footer(FooterKind::Hint, message);
        self
    }

    pub fn report(self, diagnostics: &Diagnostics) -> DiagError {
        diagnostics.push(Diagnostic {
            level: DiagnosticLevel::Error,
            content: self.content,
        });
        DiagError::promise_error_has_been_reported()
    }
}

impl DiagnosticWarning {
    pub fn new(title: impl Into<String>, span: Span, message: impl Into<String>) -> Self {
        let content = DiagnosticContent::new(title, span, message);
        Self { content }
    }

    pub fn new_multiple(title: impl Into<String>, messages: NonEmptyVec<(Span, String)>) -> Self {
        let content = DiagnosticContent::new_multiple(title, messages);
        Self { content }
    }

    pub fn add_info(mut self, span: Span, info: impl Into<String>) -> Self {
        self.content.add_info(span, info.into());
        self
    }

    pub fn add_footer_info(mut self, message: impl Into<String>) -> Self {
        self.content.add_footer(FooterKind::Info, message);
        self
    }

    pub fn add_footer_hint(mut self, message: impl Into<String>) -> Self {
        self.content.add_footer(FooterKind::Hint, message);
        self
    }

    pub fn report(self, diagnostics: &Diagnostics) {
        diagnostics.push(Diagnostic {
            level: DiagnosticLevel::Warning,
            content: self.content,
        });
    }
}

#[derive(Debug, Copy, Clone)]
pub struct DiagnosticStringSettings {
    /// Whether to include a backtrace in todo and internal compiler error diagnostics.
    backtrace: bool,
    /// Whether to use ANSI color codes in the output.
    ansi_color: bool,
}

impl DiagnosticStringSettings {
    pub fn default(ansi_color: bool) -> Self {
        DiagnosticStringSettings {
            backtrace: false,
            ansi_color,
        }
    }
}

impl Diagnostic {
    pub fn to_string(&self, database: &SourceDatabase, settings: DiagnosticStringSettings) -> String {
        self.content.to_string(database, settings, self.level)
    }

    pub fn sort_key(&self) -> impl Ord + '_ {
        // TODO expand until it contains all info, guaranteeing a single sort order
        (self.content.messages.first().0, self.level)
    }
}

impl DiagnosticContent {
    fn new(title: impl Into<String>, span: Span, message: impl Into<String>) -> Self {
        Self::new_multiple(title, NonEmptyVec::new_single((span, message.into())))
    }

    fn new_multiple(title: impl Into<String>, messages: NonEmptyVec<(Span, String)>) -> Self {
        DiagnosticContent {
            title: title.into(),
            messages,
            infos: vec![],
            footers: vec![],
            backtrace: None,
        }
    }

    fn add_info(&mut self, span: Span, info: impl Into<String>) {
        self.infos.push((span, info.into()));
    }

    fn add_footer(&mut self, kind: FooterKind, message: impl Into<String>) {
        self.footers.push((kind, message.into()));
    }

    fn to_string(
        &self,
        database: &SourceDatabase,
        settings: DiagnosticStringSettings,
        level: DiagnosticLevel,
    ) -> String {
        let Self {
            title,
            messages,
            infos,
            footers,
            backtrace,
        } = self;

        // group annotations by file
        let mut by_file: IndexMap<FileId, Vec<(AnnotationKind, Span, String)>> = IndexMap::new();
        for (span, label) in messages {
            by_file
                .entry(span.file)
                .or_default()
                .push((AnnotationKind::Primary, *span, label.clone()));
        }
        for (span, label) in infos {
            by_file
                .entry(span.file)
                .or_default()
                .push((AnnotationKind::Context, *span, label.clone()));
        }

        // Build the group: title, one snippet per file, then footers.
        let top_level = match level {
            DiagnosticLevel::Error => Level::ERROR,
            DiagnosticLevel::Warning => Level::WARNING,
        };
        let mut group = Group::with_title(top_level.primary_title(title.as_str()));

        for (file_id, annotations) in &by_file {
            let file_info = &database[*file_id];
            let file_source = file_info.content.as_str();
            let file_path = file_info.debug_info_path.as_str();

            let mut snippet = Snippet::source(file_source).path(file_path);
            for (kind, span, label) in annotations {
                snippet = snippet.annotation(kind.span(span.range_bytes()).label(label.as_str()));
            }
            group = group.element(snippet);
        }

        // TODO revert to plain level messages when https://github.com/rust-lang/annotate-snippets-rs/issues/498 is fixed,
        //   for now we render the level names ourselves because messages don't use the level style
        let footer_element = |kind: FooterKind, message: &str| {
            let (name, style) = match kind {
                FooterKind::Info => ("note", DEFAULT_NOTE_STYLE),
                FooterKind::Hint => ("help", DEFAULT_HELP_STYLE),
            };
            let label = if settings.ansi_color {
                format!("{style}{name}{style:#}")
            } else {
                name.to_owned()
            };
            let message = message.replace('\n', &format!("\n{}", " ".repeat(name.len() + 2)));
            Level::NOTE.no_name().message(format!("{label}: {message}"))
        };

        for (footer_kind, footer_message) in footers {
            group = group.element(footer_element(*footer_kind, footer_message));
        }

        if let Some(backtrace) = &backtrace
            && settings.backtrace
        {
            group = group.element(footer_element(FooterKind::Info, backtrace));
        }

        // format into string
        let renderer = if settings.ansi_color {
            let color = match level {
                DiagnosticLevel::Error => AnsiColor::BrightRed,
                DiagnosticLevel::Warning => AnsiColor::Yellow,
            };
            Renderer::styled().emphasis(Style::new().bold().fg_color(Some(Color::Ansi(color))))
        } else {
            Renderer::plain()
        };

        renderer.render(&[group])
    }
}

pub fn diag_to_string(source: &SourceDatabase, diag: &Diagnostic, ansi_color: bool) -> String {
    let settings = DiagnosticStringSettings::default(ansi_color);
    diag.to_string(source, settings)
}

pub fn diags_to_string(source: &SourceDatabase, diags: &[Diagnostic], ansi_color: bool) -> String {
    let settings = DiagnosticStringSettings::default(ansi_color);

    let mut s = String::new();
    for diag in diags {
        s.push_str(&diag.to_string(source, settings));
        s.push('\n');
        s.push('\n');
    }
    s
}

pub fn diags_to_string_vec(source: &SourceDatabase, diags: &[Diagnostic], ansi_color: bool) -> Vec<String> {
    let settings = DiagnosticStringSettings::default(ansi_color);

    let mut s = vec![];
    for diag in diags {
        s.push(diag.to_string(source, settings));
    }
    s
}
