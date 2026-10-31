use crate::front::diagnostic::{DiagResult, Diagnostics};
use crate::syntax::data_inputs::DataInputs;
use crate::syntax::hierarchy::SourceHierarchy;
use crate::syntax::manifest::{FileEntry, Manifest, ManifestFiles};
use crate::syntax::pos::Span;
use crate::syntax::source::{FileId, SourceDatabase};
use indexmap::IndexMap;
use itertools::{Itertools, chain};
use khdl_std::{STD_SOURCE_FILES, StdSourceFile};
use khdl_util::constants::{KHDL_DATA_FILE_EXTENSION, KHDL_FILE_EXTENSION};
use khdl_util::io::{IoAction, IoErrorExt, IoErrorWithPath, recurse_for_each_file};
use path_clean::PathClean;
use std::ffi::{OsStr, OsString};
use std::fmt::Display;
use std::path::{Path, PathBuf};

pub struct ManifestCollected {
    pub hierarchy: SourceHierarchy,
    pub data_inputs: DataInputs,
    pub source_paths: IndexMap<FileId, PathBuf>,
    pub data_paths: IndexMap<FileId, PathBuf>,
}

pub enum CollectionKind<'a> {
    Source(&'a mut SourceHierarchy),
    Data(&'a mut DataInputs),
}

impl CollectionKind<'_> {
    pub fn extension(&self) -> &'static str {
        match self {
            CollectionKind::Source(_) => KHDL_FILE_EXTENSION,
            CollectionKind::Data(_) => KHDL_DATA_FILE_EXTENSION,
        }
    }

    fn add_file(
        &mut self,
        diags: &Diagnostics,
        source: &SourceDatabase,
        span: Span,
        steps: &[String],
        file: FileId,
    ) -> DiagResult {
        match self {
            CollectionKind::Source(hierarchy) => hierarchy.add_file(diags, source, span, steps, file).map(|_| ()),
            CollectionKind::Data(data_inputs) => data_inputs.add_file(diags, source, span, steps, file),
        }
    }
}

pub type FilesWithSteps = Vec<(Vec<String>, PathBuf)>;

pub fn collect_from_manifest<E: Display>(
    diags: &Diagnostics,
    source: &mut SourceDatabase,
    manifest_path: &Path,
    manifest: &Manifest,
    mut read: impl FnMut(&Path) -> Result<String, E>,
) -> DiagResult<ManifestCollected> {
    let Manifest {
        source: manifest_source,
        data: manifest_data,
    } = manifest;

    let mut hierarchy = SourceHierarchy::new();
    let mut data_inputs = DataInputs::new();

    add_std_sources(diags, source, &mut hierarchy)?;

    let source_paths = collect_manifest_files(
        diags,
        source,
        manifest_path,
        manifest_source,
        &mut CollectionKind::Source(&mut hierarchy),
        &mut read,
    )?;
    let data_paths = collect_manifest_files(
        diags,
        source,
        manifest_path,
        manifest_data,
        &mut CollectionKind::Data(&mut data_inputs),
        &mut read,
    )?;

    Ok(ManifestCollected {
        hierarchy,
        data_inputs,
        source_paths,
        data_paths,
    })
}

pub fn collect_manifest_files<E: Display>(
    diags: &Diagnostics,
    source: &mut SourceDatabase,
    manifest_path: &Path,
    manifest: &ManifestFiles,
    kind: &mut CollectionKind,
    mut read: impl FnMut(&Path) -> Result<String, E>,
) -> DiagResult<IndexMap<FileId, PathBuf>> {
    let mut file_map = IndexMap::new();

    for entry in manifest.entries() {
        let &FileEntry {
            span_path,
            ref steps,
            ref path_relative,
        } = entry;
        let entry_path = manifest_path.join(path_relative).clean();

        let paths = add_tree(diags, source, kind, span_path, steps, entry_path, &mut read)?;
        file_map.extend(paths);
    }

    Ok(file_map)
}

pub fn add_tree<E: Display>(
    diags: &Diagnostics,
    source: &mut SourceDatabase,
    kind: &mut CollectionKind,
    span: Span,
    steps: &[String],
    entry_path: PathBuf,
    mut read: impl FnMut(&Path) -> Result<String, E>,
) -> DiagResult<IndexMap<FileId, PathBuf>> {
    let files = collect_files_from_tree(diags, span, entry_path, kind.extension())?;

    let mut file_map = IndexMap::new();

    // TODO maybe allow storing errors for non-UTF8 files into source?
    for (relative_steps, path) in files {
        let all_steps = chain(steps, &relative_steps).cloned().collect_vec();

        let content =
            read(&path).map_err(|e| diags.report_error_simple(e.to_string(), span, "while reading files here"))?;

        let file = source.add_file(path.to_string_lossy().into_owned(), content);
        kind.add_file(diags, source, span, &all_steps, file)?;

        file_map.insert(file, path);
    }

    Ok(file_map)
}

pub fn collect_files_from_tree(
    diags: &Diagnostics,
    span: Span,
    entry_path: PathBuf,
    extension: &str,
) -> DiagResult<FilesWithSteps> {
    let report_error = |m: String| diags.report_error_simple(m, span, "while collecting files here");

    let meta = std::fs::metadata(&entry_path)
        .map_err(|e| report_error(e.with_context(IoAction::Metadata, &entry_path).to_string()))?;
    if meta.is_file() {
        return Ok(vec![(vec![], entry_path)]);
    }
    if !meta.is_dir() {
        return Err(report_error(format!(
            "expected a regular file or directory: {}",
            entry_path.display()
        )));
    }

    let mut files = vec![];
    let mut step_err = Ok(());
    recurse_for_each_file(&entry_path, |relative_steps, path_file| {
        // short-circuit on error
        if step_err.is_err() {
            return Ok(());
        }

        // filter by extension
        if path_file.extension() != Some(OsStr::new(extension)) {
            return Ok(());
        }

        // add filename to steps
        let Some(file_stem) = path_file.file_stem() else {
            return Ok(());
        };
        let all_steps = chain(relative_steps.iter().map(OsString::as_os_str), [file_stem]);

        // convert steps to strings
        let mut relative_steps_str = vec![];
        for step in all_steps {
            match step.to_str() {
                Some(step) => relative_steps_str.push(step.to_owned()),
                None => {
                    step_err = Err(report_error(format!("Encountered non-UTF8 path {path_file:?}")));
                    return Ok(());
                }
            }
        }

        files.push((relative_steps_str, path_file.to_owned()));
        Ok(())
    })
    .map_err(|e: IoErrorWithPath| report_error(e.to_string()))?;

    step_err?;

    // sort by steps to keep order platform independant
    files.sort_by(|a, b| a.0.cmp(&b.0));

    Ok(files)
}

pub fn add_std_sources(
    diags: &Diagnostics,
    source: &mut SourceDatabase,
    hierarchy: &mut SourceHierarchy,
) -> DiagResult {
    for file in STD_SOURCE_FILES {
        let &StdSourceFile { path, steps, content } = file;

        let id = source.add_file(path.to_owned(), content.to_owned());

        let dummy_span = source.full_span(id);
        let steps = steps.iter().copied().map(str::to_owned).collect_vec();
        hierarchy.add_file(diags, source, dummy_span, &steps, id)?;
    }

    Ok(())
}
