use std::ffi::OsString;
use std::fmt::{Display, Formatter};
use std::io;
use std::path::{Path, PathBuf};

// TODO make this only accept strings, nothing else will accept non-utf8 paths anyway
pub fn recurse_for_each_file<E: From<IoErrorWithPath>>(
    dir: &Path,
    mut f: impl FnMut(&[OsString], &Path) -> Result<(), E>,
) -> Result<(), E> {
    let mut stack = vec![];
    recurse_for_each_file_impl(dir, &mut stack, &mut f)
}

fn recurse_for_each_file_impl<E: From<IoErrorWithPath>>(
    root: &Path,
    stack: &mut Vec<OsString>,
    f: &mut impl FnMut(&[OsString], &Path) -> Result<(), E>,
) -> Result<(), E> {
    let read_dir = std::fs::read_dir(root).map_err(|e| e.with_context(IoAction::ReadDir, root))?;
    for entry in read_dir {
        let entry = entry.map_err(|e| e.with_context(IoAction::ReadDir, root))?;
        let next = entry.path();
        if next.is_dir() {
            stack.push(entry.file_name());
            recurse_for_each_file_impl(&next, stack, f)?;
            assert!(stack.pop().is_some());
        } else {
            f(stack, &entry.path())?;
        }
    }
    Ok(())
}

/// The operation that caused an [IoErrorWithPath], used to construct readable error messages.
#[derive(Debug, Copy, Clone, Eq, PartialEq)]
pub enum IoAction {
    Read,
    Write,
    ReadDir,
    CreateDir,
    Metadata,
    Absolute,
}

#[derive(Debug)]
pub struct IoErrorWithPath {
    pub action: IoAction,
    pub path: PathBuf,
    pub error: io::Error,
}

impl IoAction {
    pub fn description(self) -> &'static str {
        match self {
            IoAction::Read => "read",
            IoAction::Write => "write",
            IoAction::ReadDir => "read directory",
            IoAction::CreateDir => "create directory",
            IoAction::Metadata => "read metadata of",
            IoAction::Absolute => "get absolute path of",
        }
    }
}

impl Display for IoErrorWithPath {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        let IoErrorWithPath { action, path, error } = self;
        write!(f, "cannot {} `{}`: {}", action.description(), path.display(), error)
    }
}

pub trait IoErrorExt {
    fn with_context(self, action: IoAction, path: impl Into<PathBuf>) -> IoErrorWithPath;
}

impl IoErrorExt for io::Error {
    fn with_context(self, action: IoAction, path: impl Into<PathBuf>) -> IoErrorWithPath {
        IoErrorWithPath {
            action,
            path: path.into(),
            error: self,
        }
    }
}

pub fn read_file_to_string(path: &Path) -> Result<String, IoErrorWithPath> {
    std::fs::read_to_string(path).map_err(|e| e.with_context(IoAction::Read, path))
}
