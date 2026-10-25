use crate::args::ArgsFormat;
use crate::util::{ErrorExit, manifest_find_read_parse, print_diagnostics};
use indexmap::IndexMap;
use itertools::{Itertools, zip_eq};
use khdl_language::front::diagnostic::Diagnostics;
use khdl_language::syntax::collect::collect_source_from_manifest;
use khdl_language::syntax::format::{FormatError, FormatSettings, format_file};
use khdl_language::syntax::source::SourceDatabase;
use khdl_language::util::data::IndexMapExt;
use khdl_util::constants::KHDL_FILE_EXTENSION;
use khdl_util::io::{IoAction, IoErrorExt, IoErrorWithPath, recurse_for_each_file};
use khdl_util::{swrite, swriteln};
use std::ffi::OsStr;
use std::io;
use std::process::ExitCode;

// TODO project:
//   * format all existing khdl code
//   * add CI check that everything is indeed formatted?

pub fn main_fmt(args: ArgsFormat) -> ExitCode {
    let ArgsFormat {
        manifest,
        check,
        path,
        verbose,
        debug,
    } = args;

    // figure out which files to format
    let diags = Diagnostics::new();
    let mut source = SourceDatabase::new();

    let files = match path {
        None => {
            let manifest = match manifest_find_read_parse(&mut source, manifest) {
                Ok(m) => m,
                Err(ErrorExit) => return ExitCode::FAILURE,
            };
            let (_, files) = match collect_source_from_manifest(
                &diags,
                &mut source,
                manifest.file,
                &manifest.path_parent,
                &manifest.parsed.source,
            ) {
                Ok(s) => s,
                Err(_) => {
                    print_diagnostics(&source, diags);
                    return ExitCode::FAILURE;
                }
            };

            files
        }
        Some(path) => {
            let mut files = IndexMap::new();

            // try reading as a single file
            let io_result = match std::fs::read_to_string(&path) {
                Ok(content) => {
                    let file = source.add_file(path.to_string_lossy().into_owned(), content);
                    files.insert_first(file, path);
                    Ok(())
                }
                Err(e) if e.kind() == io::ErrorKind::IsADirectory => {
                    // switch to recursive directory reading
                    recurse_for_each_file::<IoErrorWithPath>(&path, |_, entry_path| {
                        if entry_path.extension() == Some(OsStr::new(KHDL_FILE_EXTENSION)) {
                            let content = std::fs::read_to_string(entry_path)
                                .map_err(|e| e.with_context(IoAction::Read, entry_path))?;
                            let file = source.add_file(entry_path.to_string_lossy().into_owned(), content);
                            files.insert_first(file, entry_path.to_owned());
                        }
                        Ok(())
                    })
                }
                Err(e) => Err(e.with_context(IoAction::Read, &path)),
            };

            if let Err(e) = io_result {
                eprintln!("error: {e}");
                return ExitCode::FAILURE;
            }

            files
        }
    };

    // format all files
    // TODO multithread this (and sort by size to get extra good utilization)
    let settings = FormatSettings::default();
    let results = files
        .keys()
        .map(|&file| format_file(&diags, &source, &settings, file))
        .collect_vec();

    // print diagnostics and stats
    let any_errors = print_diagnostics(&source, diags);

    let mut count_unchanged: usize = 0;
    let mut count_changed: usize = 0;
    let mut count_error_syntax: usize = 0;
    let mut count_error_internal: usize = 0;

    let mut debug_output = String::new();

    for ((&file, file_path), result) in zip_eq(&files, &results) {
        let msg = match result {
            Ok(result) => {
                if debug.is_some() {
                    swriteln!(debug_output, "{}", result.debug_str());
                }

                if result.new_content == source[file].content {
                    count_unchanged += 1;
                    None
                } else {
                    count_changed += 1;
                    Some("changed")
                }
            }
            Err(FormatError::Syntax(_)) => {
                count_error_syntax += 1;
                Some("syntax error")
            }
            Err(FormatError::Internal(_)) => {
                count_error_internal += 1;
                Some("internal error")
            }
        };

        if verbose || (check && msg.is_some()) {
            eprintln!("{}: {}", file_path.display(), msg.unwrap_or("unchanged"));
        }
    }
    if verbose {
        let mut msg_stats = format!(
            "Formatted {} file{}: {count_unchanged} unchanged, {count_changed} changed, {count_error_syntax} with syntax errors",
            files.len(),
            if files.len() == 1 { "" } else { "s" },
        );
        if count_error_internal > 0 {
            swrite!(msg_stats, ", {count_error_internal} with internal formatter errors");
        }
        eprintln!("{msg_stats}");
    }

    // do something with the results
    if let Some(debug) = &debug {
        // write to debug file,
        //   don't actually change any files
        let io_result = std::fs::write(debug, debug_output).map_err(|e| e.with_context(IoAction::Write, debug));
        if let Err(e) = io_result {
            eprintln!("error: {e}");
            return ExitCode::FAILURE;
        }
    } else if check {
        // set exit code depending on whether any files would be changed,
        //   don't actually change any files
        if count_unchanged != files.len() {
            eprintln!("\nCheck failed, not all files are formatted correctly");
            return ExitCode::FAILURE;
        } else {
            eprintln!("Check passed, all files are formatted correctly");
        }
    } else {
        // write results to disk
        for ((&file, path), result) in zip_eq(&files, &results) {
            if let Ok(result) = result
                && result.new_content != source[file].content
            {
                let io_result =
                    std::fs::write(path, &result.new_content).map_err(|e| e.with_context(IoAction::Write, path));
                if let Err(e) = io_result {
                    eprintln!("error: {e}");
                    return ExitCode::FAILURE;
                }
            }
        }
    }

    if any_errors {
        ExitCode::FAILURE
    } else {
        ExitCode::SUCCESS
    }
}
