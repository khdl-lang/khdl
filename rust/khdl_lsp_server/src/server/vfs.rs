use crate::util::uri::NormalizeError;
use indexmap::IndexMap;
use khdl_util::constants::KHDL_MANIFEST_FILE_NAME;
use khdl_util::io::{IoAction, IoErrorExt, IoErrorWithPath};
use lsp_types::Uri;
use std::ffi::OsStr;
use std::path::{Path, PathBuf};
use std::str::Utf8Error;

// TODO make sure we only track manifest files and files with the right extension,
// TODO clarify what this is: this is just an overlay over the underlying file system, and is not guaranteed to contain every file
// TODO somehow collect all files referenced by the manifest file and add listeners for them
pub struct Vfs {
    any_changed: bool,
    any_manifest_changed: bool,
    files: IndexMap<PathBuf, Vec<u8>>,
}

pub type VfsResult<T> = Result<T, VfsError>;

// TODO cleanup, mostly remove unused variants
#[derive(Debug)]
pub enum VfsError {
    InvalidPathUri(Uri),
    Io(IoErrorWithPath),
    ExpectedAbsolutePath(PathBuf),
    FailedToConvertPathToUri(PathBuf, String, fluent_uri::ParseError),
    AlreadyExists(Uri),
    DoesNotExist(PathBuf),
    // TODO this should not really be a VfsError
    ContentInvalidUtf8(Utf8Error),
    PathInvalidUtf8(PathBuf),
    FailedNormalization(NormalizeError),
}

// TODO log VFS operations
impl Vfs {
    pub fn new() -> Self {
        Vfs {
            any_changed: true,
            any_manifest_changed: true,

            files: IndexMap::new(),
        }
    }

    fn update_changed(&mut self, path: &Path) {
        self.any_changed = true;
        if let Some(name) = path.file_name()
            && name == OsStr::new(KHDL_MANIFEST_FILE_NAME)
        {
            self.any_manifest_changed = true;
        }
    }

    pub fn create_or_update(&mut self, path: PathBuf, content: Vec<u8>) {
        self.update_changed(&path);
        self.files.insert(path, content);
    }

    pub fn delete(&mut self, path: &Path) -> Result<(), VfsError> {
        if self.delete_if_exists(path) {
            Ok(())
        } else {
            Err(VfsError::DoesNotExist(path.to_owned()))
        }
    }

    pub fn delete_if_exists(&mut self, path: &Path) -> bool {
        match self.files.swap_remove(path) {
            None => false,
            Some(_) => {
                self.update_changed(path);
                true
            }
        }
    }

    pub fn read_maybe_from_disk(&mut self, path: &Path) -> Result<&[u8], VfsError> {
        // https://github.com/rust-lang/rust/issues/54663
        if self.files.contains_key(path) {
            return Ok(self.files.get(path).unwrap());
        }

        let content = std::fs::read(path).map_err(|e| e.with_context(IoAction::Read, path))?;

        let slot = self.files.entry(path.to_owned()).or_default();
        *slot = content;
        Ok(slot)
    }

    pub fn read_str_maybe_from_disk(&mut self, path: &Path) -> Result<&str, VfsError> {
        let content = self.read_maybe_from_disk(path)?;
        std::str::from_utf8(content).map_err(VfsError::ContentInvalidUtf8)
    }

    pub fn any_changed(&mut self) -> bool {
        self.any_changed
    }

    pub fn any_manifest_changed(&mut self) -> bool {
        self.any_manifest_changed
    }

    pub fn clear_changed(&mut self) {
        self.any_changed = false;
        self.any_manifest_changed = false;
    }
}

impl From<IoErrorWithPath> for VfsError {
    fn from(e: IoErrorWithPath) -> Self {
        VfsError::Io(e)
    }
}
