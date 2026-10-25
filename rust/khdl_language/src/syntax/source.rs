use crate::new_index_type;
use crate::syntax::pos::{LineOffsets, Pos, PosFull, Span, SpanFull};
use crate::util::arena::{Arena, IndexType};
use std::ops::Range;

/// The full set of source files that are part of this compilation. This type is immutable.
#[derive(Clone)]
pub struct SourceDatabase {
    files: Arena<FileId, FileSourceInfo>,
}

new_index_type!(pub FileId: Ord);

#[derive(Clone)]
pub struct FileSourceInfo {
    pub debug_info_path: String,
    pub content: String,
    pub offsets: LineOffsets,
}

impl SourceDatabase {
    pub fn new() -> SourceDatabase {
        SourceDatabase { files: Arena::new() }
    }

    pub fn add_file(&mut self, debug_info_path: String, content: String) -> FileId {
        let offsets = LineOffsets::new(&content);
        let info = FileSourceInfo {
            debug_info_path,
            content,
            offsets,
        };
        self.files.push(info)
    }

    pub fn files(&self) -> impl Iterator<Item = FileId> + Clone + '_ {
        self.files.keys()
    }

    pub fn file_count(&self) -> usize {
        self.files.len()
    }

    pub fn total_lines_of_code(&self) -> u64 {
        self.files
            .values()
            .map(|file_info| file_info.offsets.line_count() as u64)
            .sum()
    }

    pub fn expand_pos(&self, pos: Pos) -> PosFull {
        self[pos.file].offsets.expand_pos(pos)
    }

    pub fn expand_span(&self, span: Span) -> SpanFull {
        self[span.file].offsets.expand_span(span)
    }

    pub fn span_str(&self, span: Span) -> &str {
        &self[span.file].content[span.start_byte..span.end_byte]
    }

    pub fn full_span(&self, file: FileId) -> Span {
        self[file].offsets.full_span(file)
    }
}

impl std::ops::Index<FileId> for SourceDatabase {
    type Output = FileSourceInfo;
    fn index(&self, index: FileId) -> &Self::Output {
        &self.files[index]
    }
}

impl FileId {
    pub fn dummy() -> FileId {
        let mut arena = Arena::new();
        arena.push(())
    }

    pub fn span(self, bytes: Range<usize>) -> Span {
        Span::new(self, bytes.start, bytes.end)
    }
}
