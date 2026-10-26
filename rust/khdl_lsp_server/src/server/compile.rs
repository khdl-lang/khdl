use crate::server::settings::{PositionEncoding, Settings};
use crate::server::state::{RequestError, ServerState};
use crate::server::vfs::{Vfs, VfsError, VfsResult};
use crate::util::encode::span_to_lsp;
use crate::util::sender::SendErrorOr;
use crate::util::uri::{
    NormalizeError, abs_path_to_uri, build_watcher_any_file_with_name, path_join_normalized, uri_to_path,
};
use indexmap::{IndexMap, IndexSet};
use itertools::{Itertools, enumerate, zip_eq};
use khdl_language::front::compile::{CompileFixed, CompileRefs, CompileSettings, CompileShared, QueueItems};
use khdl_language::front::diagnostic::{
    DiagResult, Diagnostic, DiagnosticContent, DiagnosticLevel, Diagnostics, FooterKind,
};
use khdl_language::front::print::IgnorePrintHandler;
use khdl_language::syntax::collect::{add_source_files_to_tree, add_std_sources, collect_source_files_from_tree};
use khdl_language::syntax::hierarchy::SourceHierarchy;
use khdl_language::syntax::manifest::{Manifest, SourceEntry};
use khdl_language::syntax::parsed::ParsedDatabase;
use khdl_language::syntax::source::{FileId, SourceDatabase};
use khdl_language::try_inner;
use khdl_language::util::NON_ZERO_USIZE_ONE;
use khdl_util::constants::{KHDL_FILE_EXTENSION, KHDL_LSP_NAME, KHDL_MANIFEST_FILE_NAME};
use khdl_util::io::recurse_for_each_file;
use khdl_util::swrite;
use lsp_types::{
    DiagnosticRelatedInformation, DiagnosticSeverity, Location, PublishDiagnosticsParams, Uri, notification,
};
use std::ffi::OsStr;
use std::path::{Path, PathBuf};
use std::sync::OnceLock;
use std::sync::atomic::{AtomicBool, Ordering};

#[derive(Clone)]
struct ManifestCommon {
    manifest_folder: PathBuf,

    diags: Diagnostics,
    source: SourceDatabase,
    file_to_path: IndexMap<FileId, PathBuf>,
}

pub struct ManifestFound {
    common: ManifestCommon,
    parsed: DiagResult<Manifest>,
}

struct ManifestCollected {
    common: ManifestCommon,
    inner: DiagResult<ManifestCollectedInner>,
}

struct ManifestCollectedInner {
    data: khdl_language::syntax::data::DataInputs,
    #[allow(dead_code)]
    parsed: Manifest,
    hierarchy: SourceHierarchy,
}

impl ServerState {
    pub fn compile_projects_and_send_diagnostics(
        &mut self,
        should_stop: &(impl Fn() -> bool + Sync),
    ) -> Result<(), SendErrorOr<RequestError>> {
        self.log("try compile");

        // if nothing has changed we don't need to do any work
        if !self.vfs.any_changed() {
            self.log("no vfs changes");
            return Ok(());
        }

        // collect manifests and set watchers
        //   setting watchers and scanning the entire workspace tree is expensive,
        //   so we want to avoid doing this as much as possible
        if self.vfs.any_manifest_changed() || self.cache_manifests_found.is_none() {
            self.log("manifest change");
            self.cache_manifests_found = Some(self.collect_manifests_and_set_watchers()?);
        } else {
            self.log("no manifest change");
        }
        let manifests_found = self.cache_manifests_found.as_ref().unwrap();

        // collect sources
        let mut manifests_collected = vec![];
        for found in manifests_found {
            let ManifestFound { common, parsed } = found;

            let mut common = common.clone();
            let parsed = parsed.clone();

            let inner = match parsed {
                Ok(parsed) => collect_manifest_sources(&mut self.vfs, &mut common, parsed)
                    .map_err(|e| SendErrorOr::Other(RequestError::Vfs(VfsError::FailedNormalization(e))))?,
                Err(e) => Err(e),
            };

            manifests_collected.push(ManifestCollected { common, inner });
        }

        // compile all manifests
        // TODO parallel loop over everything?
        let mut grouped_diags = IndexMap::new();
        for manifest in manifests_collected {
            let diags = manifest.common.diags;
            let source = &manifest.common.source;

            if let Ok(inner) = &manifest.inner {
                let hierarchy = &inner.hierarchy;
                let parsed = ParsedDatabase::new(&diags, source, hierarchy);

                // TODO at this point we can clear/update all parsing diagnostics already
                // TODO compile all items in the open files first, then later the rest for increased interactivity
                // TODO propagate prints to a separate output channel or log file
                let early_stop = AtomicBool::new(false);
                let should_stop_inner = || {
                    let should_stop_new = should_stop();
                    let should_stop_old = early_stop.fetch_or(should_stop_new, Ordering::Relaxed);
                    should_stop_new || should_stop_old
                };

                let settings = CompileSettings {
                    // we will discard the IR anyway, so no need to spend time cleaning it up
                    do_ir_cleanup: false,
                };
                let fixed = CompileFixed {
                    data: &inner.data,
                    settings: &settings,
                    source,
                    hierarchy,
                    parsed: &parsed,
                };

                let thread_count = self.pool.as_ref().map_or(NON_ZERO_USIZE_ONE, |p| p.thread_count());
                let shared = CompileShared::new(&diags, fixed, QueueItems::All, thread_count);
                let refs = CompileRefs {
                    diags: &diags,
                    fixed,
                    shared: &shared,
                    print_handler: &IgnorePrintHandler,
                    should_stop: &should_stop_inner,
                    interrupted_local: &OnceLock::new(),
                };

                self.log("compile: start compile loop");
                refs.run_compile_loop(self.pool.as_ref());
                self.log("compile: end compile loop");

                if early_stop.load(Ordering::Relaxed) {
                    // return immediately without reporting any diagnostics, they would include interrupts
                    return Ok(());
                }
            }

            let file_to_uri = manifest
                .common
                .file_to_path
                .into_iter()
                .map(|(k, b)| Ok((k, abs_path_to_uri(&b)?)))
                .try_collect()
                .map_err(|e| SendErrorOr::Other(RequestError::Vfs(e)))?;

            add_grouped_diagnostic_to_lsp(&mut grouped_diags, &self.settings, source, &file_to_uri, diags.finish())?;
        }

        self.log(format!(
            "sending diagnostics: {}",
            grouped_diags.values().map(|v| v.len()).sum::<usize>()
        ));
        self.send_diagnostics(grouped_diags)?;

        // we've completed all work
        self.vfs.clear_changed();
        Ok(())
    }

    fn collect_manifests_and_set_watchers(&mut self) -> Result<Vec<ManifestFound>, SendErrorOr<RequestError>> {
        // TODO support multiple workspaces, root_path, no workspace
        //   also register change listeners for workspaces when we add support for them
        #[allow(deprecated)]
        let root_uri = self
            .settings
            .initialize_params
            .root_uri
            .as_ref()
            .ok_or_else(|| {
                SendErrorOr::Other(RequestError::Internal(
                    "no root URI set in initialize params".to_string(),
                ))
            })?
            .clone();
        let root_path = uri_to_path(&root_uri).map_err(|e| SendErrorOr::Other(RequestError::Vfs(e)))?;

        // start collecting watchers, they need to be set before reading the corresponding files
        let root_watcher = build_watcher_any_file_with_name(root_uri.clone(), KHDL_MANIFEST_FILE_NAME);
        let mut watchers = vec![root_watcher];
        if self.curr_watchers.is_empty() {
            self.set_watchers(watchers.clone())?;
        }

        // find manifests
        let mut manifest_folders = vec![];
        recurse_for_each_file(&root_path, |_, entry_path| {
            if entry_path.file_name() != Some(OsStr::new(KHDL_MANIFEST_FILE_NAME)) {
                return Ok(());
            }
            manifest_folders.push(entry_path.parent().unwrap().to_owned());
            Ok(())
        })
        .map_err(|e| SendErrorOr::Other(RequestError::Vfs(e)))?;

        // parse manifests and add watchers to their files
        let mut manifests: Vec<ManifestFound> = vec![];
        for manifest_folder in manifest_folders {
            let manifest_path = manifest_folder.join(KHDL_MANIFEST_FILE_NAME);
            let manifest_source = self
                .vfs
                .read_str_maybe_from_disk(&manifest_path)
                .map_err(|e| SendErrorOr::Other(RequestError::Vfs(e)))?;

            let diags = Diagnostics::new();
            let mut source = SourceDatabase::new();
            let mut file_to_path = IndexMap::new();

            let manifest_file =
                source.add_file(manifest_path.to_string_lossy().into_owned(), manifest_source.to_owned());
            file_to_path.insert(manifest_file, manifest_path);

            let parsed = Manifest::parse_toml(&diags, &source, manifest_file);

            if let Ok(manifest) = &parsed {
                for entry in manifest.source.entries() {
                    let SourceEntry {
                        span_path: _,
                        steps: _,
                        path_relative,
                    } = entry;

                    let entry_path = path_join_normalized(&manifest_folder, Path::new(path_relative))
                        .map_err(|e| SendErrorOr::Other(RequestError::Vfs(VfsError::FailedNormalization(e))))?;

                    watchers.push(build_watcher_any_file_with_name(
                        abs_path_to_uri(&entry_path).map_err(|e| SendErrorOr::Other(RequestError::Vfs(e)))?,
                        &format!("*.{KHDL_FILE_EXTENSION}"),
                    ));
                }
                for entry in manifest.data.entries() {
                    let entry_path = path_join_normalized(&manifest_folder, Path::new(&entry.path_relative))
                        .map_err(|e| SendErrorOr::Other(RequestError::Vfs(VfsError::FailedNormalization(e))))?;
                    if entry_path.is_dir() {
                        watchers.push(build_watcher_any_file_with_name(
                            abs_path_to_uri(&entry_path).map_err(|e| SendErrorOr::Other(RequestError::Vfs(e)))?,
                            "*.json",
                        ));
                    } else if let (Some(parent), Some(name)) = (entry_path.parent(), entry_path.file_name()) {
                        let pattern: String = name
                            .to_string_lossy()
                            .chars()
                            .map(|c| {
                                if "*?[]{}".contains(c) {
                                    format!("[{c}]")
                                } else {
                                    c.to_string()
                                }
                            })
                            .collect();
                        watchers.push(lsp_types::FileSystemWatcher {
                            glob_pattern: lsp_types::GlobPattern::Relative(lsp_types::RelativePattern {
                                base_uri: lsp_types::OneOf::Right(
                                    abs_path_to_uri(parent).map_err(|e| SendErrorOr::Other(RequestError::Vfs(e)))?,
                                ),
                                pattern,
                            }),
                            kind: None,
                        });
                    }
                }
            }

            let common = ManifestCommon {
                manifest_folder,
                diags,
                source,
                file_to_path,
            };
            let manifest_found = ManifestFound { common, parsed };
            manifests.push(manifest_found);
        }
        self.set_watchers(watchers)?;

        Ok(manifests)
    }

    fn send_diagnostics(
        &mut self,
        grouped: IndexMap<Uri, Vec<lsp_types::Diagnostic>>,
    ) -> Result<(), SendErrorOr<RequestError>> {
        let mut prev_files_leftover = std::mem::take(&mut self.curr_files_with_diagnostics);
        let mut next_files = IndexSet::new();

        // send new diagnostics
        for (uri, diags) in grouped {
            if diags.is_empty() {
                continue;
            }

            prev_files_leftover.swap_remove(&uri);
            next_files.insert(uri.clone());

            self.sender
                .send_notification::<notification::PublishDiagnostics>(PublishDiagnosticsParams {
                    uri: uri.clone(),
                    diagnostics: diags,
                    // TODO version
                    version: None,
                })?;
        }

        // clear files that no longer have diagnostics
        for uri in prev_files_leftover {
            self.sender
                .send_notification::<notification::PublishDiagnostics>(PublishDiagnosticsParams {
                    uri: uri.clone(),
                    diagnostics: vec![],
                    // TODO version
                    version: None,
                })?;
        }

        // store current files with diagnostics
        self.curr_files_with_diagnostics = next_files;

        Ok(())
    }
}

fn collect_manifest_sources(
    vfs: &mut Vfs,
    common: &mut ManifestCommon,
    parsed: Manifest,
) -> Result<DiagResult<ManifestCollectedInner>, NormalizeError> {
    let diags = &common.diags;
    let source = &mut common.source;
    let mut hierarchy = SourceHierarchy::new();

    try_inner!(add_std_sources(diags, source, &mut hierarchy));

    for entry in parsed.source.entries() {
        let &SourceEntry {
            span_path,
            ref steps,
            ref path_relative,
        } = entry;

        let entry_path = path_join_normalized(&common.manifest_folder, Path::new(path_relative))?;

        // TODO don't early exit, visit all entries before returning error
        // TODO insert extra files from Vfs that don't yet exist on disk
        let files = try_inner!(collect_source_files_from_tree(diags, span_path, entry_path));

        let file_paths = files.iter().map(|(_, p)| p.to_owned()).collect_vec();

        let file_ids = add_source_files_to_tree(
            diags,
            source,
            &mut hierarchy,
            span_path,
            steps.clone(),
            &files,
            |file_path| match vfs.read_str_maybe_from_disk(file_path) {
                Ok(s) => Ok(s.to_owned()),
                Err(e) => Err(format!("{e:?}")),
            },
        );
        let file_ids = try_inner!(file_ids);

        for (file_id, file_path) in zip_eq(file_ids, file_paths) {
            common.file_to_path.insert(file_id, file_path);
        }
    }

    let (data, paths) = try_inner!(khdl_language::syntax::data::collect_data_from_manifest(
        diags,
        source,
        &common.manifest_folder,
        &parsed.data,
        |path| vfs
            .read_str_maybe_from_disk(path)
            .map(str::to_owned)
            .map_err(|e| format!("{e:?}")),
    ));
    common.file_to_path.extend(paths);
    Ok(Ok(ManifestCollectedInner {
        data,
        parsed,
        hierarchy,
    }))
}

fn add_grouped_diagnostic_to_lsp(
    grouped: &mut IndexMap<Uri, Vec<lsp_types::Diagnostic>>,
    settings: &Settings,
    source: &SourceDatabase,
    file_to_uri: &IndexMap<FileId, Uri>,
    diags: Vec<Diagnostic>,
) -> Result<(), SendErrorOr<RequestError>> {
    for diagnostic in diags {
        let diags = diagnostic_to_lsp(settings.position_encoding, source, file_to_uri, diagnostic)
            .map_err(|e| SendErrorOr::Other(RequestError::Vfs(e)))?;
        for (file, diag) in diags {
            if let Some(uri) = file_to_uri.get(&file) {
                grouped.entry(uri.clone()).or_default().push(diag);
            }
        }
    }
    Ok(())
}

fn diagnostic_to_lsp(
    encoding: PositionEncoding,
    source: &SourceDatabase,
    file_to_uri: &IndexMap<FileId, Uri>,
    diagnostic: Diagnostic,
) -> VfsResult<Vec<(FileId, lsp_types::Diagnostic)>> {
    // TODO check client diagnostic capabilities
    // TODO better handle uri-less errors, eg. for std

    let Diagnostic { level, content } = diagnostic;
    let DiagnosticContent {
        title,
        messages,
        infos,
        footers,
        backtrace: _,
    } = content;

    // LSP does not allow us to express "a single diagnostic with multiple top-level spans",
    //   so instead we turn multiple top-level messages into multiple separate diagnostics, with duplicated content.
    let mut diags = vec![];

    for (curr_i, &(curr_top_span, ref curr_top_message)) in enumerate(&messages) {
        let mut related_information = vec![];

        // add other top-level messages as related information
        for (other_i, &(other_top_span, ref other_top_message)) in enumerate(&messages) {
            if curr_i == other_i {
                continue;
            }

            let file = other_top_span.file;
            let file_info = &source[file];

            if let Some(uri) = file_to_uri.get(&file) {
                related_information.push(DiagnosticRelatedInformation {
                    location: Location {
                        uri: uri.clone(),
                        range: span_to_lsp(encoding, &file_info.offsets, &file_info.content, other_top_span),
                    },
                    message: format!("{}: {}", level_to_str(level), other_top_message),
                });
            }
        }

        // add infos as related information
        for &(info_span, ref info_message) in &infos {
            let file = info_span.file;
            let file_info = &source[file];

            if let Some(uri) = file_to_uri.get(&file) {
                related_information.push(DiagnosticRelatedInformation {
                    location: Location {
                        uri: uri.clone(),
                        range: span_to_lsp(encoding, &file_info.offsets, &file_info.content, info_span),
                    },
                    message: format!("{}: {}", level_to_str(level), info_message),
                });
            }
        }

        // combine current top-level message and footers into lsp message
        let curr_file = curr_top_span.file;
        let curr_file_info = &source[curr_file];

        let mut lsp_message = format!("{}\n{}", title, curr_top_message);
        for &(footer_kind, ref footer_message) in &footers {
            swrite!(
                lsp_message,
                "\n{}: {}",
                footer_kind_to_string(footer_kind),
                footer_message
            );
        }

        let diag = lsp_types::Diagnostic {
            range: span_to_lsp(
                encoding,
                &curr_file_info.offsets,
                &curr_file_info.content,
                curr_top_span,
            ),
            severity: Some(level_to_severity(level)),
            code: None,
            code_description: None,
            source: Some(KHDL_LSP_NAME.to_owned()),
            message: lsp_message,
            related_information: Some(related_information),
            // TODO set tags once we support those
            tags: None,
            // TODO data for auto-fixes
            data: None,
        };
        diags.push((curr_file, diag));
    }

    Ok(diags)
}

fn level_to_severity(level: DiagnosticLevel) -> DiagnosticSeverity {
    match level {
        DiagnosticLevel::Error => DiagnosticSeverity::ERROR,
        DiagnosticLevel::Warning => DiagnosticSeverity::WARNING,
    }
}

fn level_to_str(level: DiagnosticLevel) -> &'static str {
    match level {
        DiagnosticLevel::Error => "error",
        DiagnosticLevel::Warning => "warning",
    }
}

fn footer_kind_to_string(kind: FooterKind) -> &'static str {
    match kind {
        FooterKind::Info => "info",
        FooterKind::Hint => "hint",
    }
}

#[cfg(test)]
mod data_tests {
    use super::*;

    #[test]
    fn data_collection_uses_editor_overlay_and_reenumerates_trees() {
        struct Project(PathBuf);
        impl Drop for Project {
            fn drop(&mut self) {
                std::fs::remove_dir_all(&self.0).unwrap();
            }
        }
        let project = Project(std::env::temp_dir().join(
            format!("khdl-lsp-data-{}-{}",
            std::process::id(), std::time::SystemTime::now().duration_since(std::time::UNIX_EPOCH).unwrap().as_nanos()),
        ));
        std::fs::create_dir_all(project.0.join("data")).unwrap();
        std::fs::write(project.0.join("top.kh"), "").unwrap();
        let a = project.0.join("data/a.json");
        std::fs::write(&a, "1").unwrap();
        let mut vfs = Vfs::new();
        vfs.create_or_update(a.clone(), b"2".to_vec());

        let collect = |vfs: &mut Vfs| {
            let mut source = SourceDatabase::new();
            let file = source.add_file(
                "khdl.toml".into(),
                "[source]\ntop = 'top.kh'\n[data]\ntables = 'data'\n".into(),
            );
            let diags = Diagnostics::new();
            let parsed = Manifest::parse_toml(&diags, &source, file).unwrap();
            let mut common = ManifestCommon {
                manifest_folder: project.0.clone(),
                diags,
                source,
                file_to_path: IndexMap::new(),
            };
            let collected = collect_manifest_sources(vfs, &mut common, parsed).unwrap().unwrap();
            assert_eq!(common.diags.len(), 0);
            assert!(
                collected
                    .hierarchy
                    .files()
                    .all(|id| !common.source[id].debug_info_path.ends_with(".json"))
            );
            (common, collected)
        };
        let (first, collected) = collect(&mut vfs);
        let file = collected.data.find("tables.a").unwrap();
        assert_eq!(first.source[file].content, "2");
        assert_eq!(first.file_to_path[&file], a);

        vfs.clear_changed();
        vfs.create_or_update(a.clone(), b"unsaved invalid JSON".to_vec());
        std::fs::write(project.0.join("data/b.json"), "4").unwrap();
        assert!(vfs.any_changed());
        let (second, collected) = collect(&mut vfs);
        assert_eq!(
            second.source[collected.data.find("tables.a").unwrap()].content,
            "unsaved invalid JSON"
        );
        assert!(collected.data.find("tables.b").is_some());

        std::fs::remove_file(&a).unwrap();
        vfs.delete_if_exists(&a);
        let (_, collected) = collect(&mut vfs);
        assert!(collected.data.find("tables.a").is_none());
        assert!(collected.data.find("tables.b").is_some());
    }
}
