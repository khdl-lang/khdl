use crate::handlers::dispatch::NotificationHandler;
use crate::server::state::{RequestError, RequestResult, ServerState};
use crate::server::vfs::VfsError;
use crate::util::uri::uri_to_path;
use khdl_util::io::{IoAction, IoErrorExt};
use lsp_types::notification::{
    DidChangeTextDocument, DidChangeWatchedFiles, DidCloseTextDocument, DidOpenTextDocument,
};
use lsp_types::{
    DidChangeTextDocumentParams, DidChangeWatchedFilesParams, DidCloseTextDocumentParams, DidOpenTextDocumentParams,
    FileChangeType, FileEvent, TextDocumentContentChangeEvent, TextDocumentIdentifier, TextDocumentItem,
    VersionedTextDocumentIdentifier,
};
use std::io::ErrorKind;

impl NotificationHandler<DidOpenTextDocument> for ServerState {
    fn handle_notification(&mut self, params: DidOpenTextDocumentParams) -> RequestResult<()> {
        let DidOpenTextDocumentParams { text_document } = params;
        let TextDocumentItem {
            uri,
            text,
            language_id: _,
            version: _,
        } = text_document;

        if !self.open_files.insert(uri.clone()) {
            return Err(RequestError::Invalid(format!(
                "trying to open file {uri:?} which is already open"
            )));
        }

        let path = uri_to_path(&uri)?;
        self.vfs.create_or_update(path, text.into_bytes());

        Ok(())
    }
}

impl NotificationHandler<DidCloseTextDocument> for ServerState {
    fn handle_notification(&mut self, params: DidCloseTextDocumentParams) -> RequestResult<()> {
        let DidCloseTextDocumentParams { text_document } = params;
        let TextDocumentIdentifier { uri } = text_document;

        if !self.open_files.swap_remove(&uri) {
            return Err(RequestError::Invalid(format!(
                "trying to close file {uri:?} which is not open"
            )));
        }

        // leave the file content in the VFS
        Ok(())
    }
}

impl NotificationHandler<DidChangeTextDocument> for ServerState {
    fn handle_notification(&mut self, params: DidChangeTextDocumentParams) -> RequestResult<()> {
        let DidChangeTextDocumentParams {
            text_document,
            content_changes,
        } = params;
        let VersionedTextDocumentIdentifier { uri, version: _ } = text_document;

        if !self.open_files.contains(&uri) {
            return Err(RequestError::Invalid(format!(
                "trying to change file {uri:?} which is not open"
            )));
        }

        // TODO support incremental changes
        for change in content_changes {
            let TextDocumentContentChangeEvent {
                range,
                range_length,
                text,
            } = change;
            assert!(range.is_none() && range_length.is_none());

            let path = uri_to_path(&uri)?;
            self.vfs.create_or_update(path, text.into_bytes());
        }

        Ok(())
    }
}

impl NotificationHandler<DidChangeWatchedFiles> for ServerState {
    fn handle_notification(&mut self, params: DidChangeWatchedFilesParams) -> RequestResult<()> {
        let DidChangeWatchedFilesParams { changes } = params;

        for change in changes {
            let FileEvent { uri, typ } = change;
            match typ {
                FileChangeType::CREATED | FileChangeType::CHANGED => {
                    let path = uri_to_path(&uri)?;
                    match std::fs::read(&path) {
                        Ok(content) => {
                            self.vfs.create_or_update(path, content);
                        }
                        Err(e) => {
                            match e.kind() {
                                ErrorKind::IsADirectory => {
                                    // ignore, this is apparently allowed but we don't track folders
                                }
                                ErrorKind::NotFound => {
                                    // race condition, this file has been deleted by now
                                    self.vfs.delete_if_exists(&path);
                                }
                                _ => {
                                    // other error, could be important
                                    return Err(RequestError::Vfs(VfsError::Io(e.with_context(IoAction::Read, path))));
                                }
                            }
                        }
                    }
                }
                FileChangeType::DELETED => {
                    let path = uri_to_path(&uri)?;
                    self.vfs.delete_if_exists(&path);
                }
                _ => {
                    return Err(RequestError::Invalid(format!(
                        "unknown file change type {typ:?} for uri {uri:?}"
                    )));
                }
            };
        }

        Ok(())
    }
}
