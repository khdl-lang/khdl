use khdl_language::syntax::pos::Span;
use khdl_language::syntax::source::SourceDatabase;
use khdl_util::constants::{DUMMY_FILE_CMDLINE, KHDL_BINARY_NAME};
use khdl_util::swrite;

/// A virtual file that contains an approximation of the commandline arguments.
/// This is useful to allow spans to point at commandline arguments.
///
/// A proper implementation would require https://github.com/clap-rs/clap/issues/4948.
pub struct CommandLineFile {
    span: Span,
    args_start: Vec<(String, usize)>,
}

impl CommandLineFile {
    /// Create a new [CommandLineFile].
    /// `args` must be the commandline arguments, without the initial binary name.
    pub fn new(source: &mut SourceDatabase, args: impl IntoIterator<Item = String>) -> Self {
        let mut f = KHDL_BINARY_NAME.to_owned();
        let mut args_start = vec![];

        for arg in args {
            let safe = !arg.is_empty() && arg.chars().all(is_safe_char);

            swrite!(f, " ");
            let start = if safe {
                let start = f.len();
                swrite!(f, "{arg}");
                start
            } else {
                let arg_escaped = arg.replace('"', "\\\"");
                swrite!(f, " \"");
                let start = f.len();
                swrite!(f, "{arg_escaped}\"");
                start
            };

            args_start.push((arg, start));
        }

        let file = source.add_file(DUMMY_FILE_CMDLINE.to_owned(), f);
        CommandLineFile {
            span: source.full_span(file),
            args_start,
        }
    }

    pub fn full_span(&self) -> Span {
        self.span
    }

    /// Find the span of the given value, might return false positives.
    pub fn value_span(&self, value: &str) -> Option<Span> {
        self.args_start.iter().find_map(|&(ref arg, start)| {
            if let Some(prefix) = arg.strip_suffix(value) {
                if prefix.is_empty() || prefix.ends_with('=') {
                    let span = Span::new(self.span.file, start + prefix.len(), start + arg.len());
                    return Some(span);
                }
            }
            None
        })
    }
}

fn is_safe_char(c: char) -> bool {
    c.is_alphanumeric() || "_-./=".contains(c)
}

#[cfg(test)]
mod tests {
    use super::CommandLineFile;
    use khdl_language::syntax::source::SourceDatabase;

    #[test]
    fn value_span() {
        let mut source = SourceDatabase::new();

        let args = ["build", "--top", "a.b", "--top=c", "--manifest", "x y.toml"];
        let cmd = CommandLineFile::new(&mut source, args.map(str::to_owned));

        let content = source.span_str(cmd.span);
        assert_eq!(content, r#"khdl build --top a.b --top=c --manifest "x y.toml""#);

        for value in ["a.b", "c", "x y.toml"] {
            assert_eq!(&content[cmd.value_span(value).unwrap().range_bytes()], value);
        }
        assert_eq!(cmd.value_span("missing"), None);
    }
}
