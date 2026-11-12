use clap::{Parser, Subcommand};
use khdl_util::constants::KHDL_VERSION;
use khdl_util::khdl_manifest_file_name_macro;
use std::num::NonZeroUsize;
use std::path::PathBuf;

#[derive(Parser, Debug)]
#[command(version=KHDL_VERSION)]
pub struct Args {
    #[command(subcommand)]
    pub command: ArgsCommand,
}

#[derive(Subcommand, Debug)]
pub enum ArgsCommand {
    Build(ArgsBuild),
    Fmt(ArgsFormat),
}

/// Build a project.
#[derive(Parser, Debug)]
pub struct ArgsBuild {
    #[arg(long, help=MANIFEST_DOC)]
    pub manifest: Option<PathBuf>,

    // elaboration
    /// The top module to elaborate and use as the root module of the outputs.
    ///
    /// This option can be passed multiple times, in which case there multiple tops will be elaborated.
    /// Must be a full path to a public module with no generic parameters.
    #[arg(long)]
    pub top: Vec<String>,
    /// Elaborate only the top modules, instead of all items.
    ///
    /// This can be useful to speed up compilation or to avoid type-checking unnecessary items.
    #[arg(long)]
    pub top_only: bool,

    // outputs
    #[arg(long)]
    pub output_verilog: Option<PathBuf>,

    // performance
    // TODO maybe make this a common option?
    /// The number of threads to use. Defaults to the number of hardware threads.
    #[arg(long, short = 'j')]
    pub thread_count: Option<NonZeroUsize>,

    // debug
    #[arg(long)]
    pub debug_profile: bool,
    #[arg(long)]
    pub debug_print_files: bool,
    #[arg(long)]
    pub debug_keep_main_stack: bool,
    #[arg(long)]
    pub debug_output_ir: Option<PathBuf>,
}

/// Format source files.
#[derive(Parser, Debug)]
pub struct ArgsFormat {
    #[arg(long, help=MANIFEST_DOC)]
    pub manifest: Option<PathBuf>,

    /// Check if files are formatted correctly without making any changes,
    /// exiting with a non-zero code if any files would be changed by formatting.
    #[arg(long)]
    pub check: bool,

    /// File or directory to format. If not provided all files in the project manifest will be formatted.
    #[arg(conflicts_with = "manifest")]
    pub path: Option<PathBuf>,

    /// Verbose output, set to print some more information about the formatting process.
    #[arg(long, short)]
    pub verbose: bool,
    /// Debug output file path. Set to get debug output of the internal formatting IRs and the final output.
    /// When this is used, the source files are not modified.
    #[arg(long, short)]
    pub debug: Option<PathBuf>,
}

const MANIFEST_DOC: &str = concat!(
    "Path to the project manifest file.",
    " If not provided, the current directory and its parents will be searched for a file named `",
    khdl_manifest_file_name_macro!(),
    "`.",
);

#[test]
fn args() {
    use clap::CommandFactory;
    Args::command().debug_assert();
}
