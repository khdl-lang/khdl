use std::num::NonZeroUsize;

#[macro_export]
macro_rules! khdl_manifest_file_name_macro {
    () => {
        "khdl.toml"
    };
}

pub const KHDL_LANGUAGE_NAME: &str = "KHDL";
pub const KHDL_BINARY_NAME: &str = "khdl";
pub const KHDL_FILE_EXTENSION: &str = "kh";
pub const KHDL_DATA_FILE_EXTENSION: &str = "json";
pub const KHDL_MANIFEST_FILE_NAME: &str = khdl_manifest_file_name_macro!();
pub const KHDL_LSP_NAME: &str = "KHDL-LSP";
pub const KHDL_VERSION: &str = env!("CARGO_PKG_VERSION");
pub const KHDL_FMT_DIRECTIVE: &str = "khdl-fmt";

pub const DUMMY_FILE_CMDLINE: &str = "<command line>";
pub const DUMMY_FILE_PYTHON: &str = "<python caller>";
pub const DUMMY_FILE_PYTHON_CONTENT: &str = "/* python caller */";

// TODO make all of these configurable
// TODO maybe we can reduce this by now, module elaboration does not count towards the stack any more
//   it might also not matter, maybe every platform pre-commits stack space by now
pub const COMPILE_THREAD_STACK_SIZE: usize = 1024 * 1024 * 1024;

// wasm has very shallow stacks, so set a low limit
pub const STACK_OVERFLOW_STACK_LIMIT: usize = if cfg!(target_family = "wasm") { 60 } else { 1000 };
pub const STACK_OVERFLOW_ERROR_ENTRIES_SHOWN: usize = 15;

pub const MAX_DRIVER_INFO_PATHS: usize = 20;

pub const MAX_IMPORT_SUGGESTIONS: NonZeroUsize = NonZeroUsize::new(4).unwrap();
pub const MAX_IDENTIFIER_SUGGESTIONS: NonZeroUsize = NonZeroUsize::new(4).unwrap();
