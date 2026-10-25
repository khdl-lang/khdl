use crate::syntax::token::{
    REGEX_ID_CONTINUE, REGEX_ID_START, REGEX_INT_CONTINUE, REGEX_INT_START, REGEX_STRING_ESCAPE_CHARS, TokenType,
    str_is_valid_identifier,
};
use itertools::Itertools;
use khdl_util::constants::KHDL_LANGUAGE_NAME;
use serde_json::json;

/// Generate a TextMate grammar that highlights source code consistently with the tokenizer.
/// The `fuzz_textmate` fuzz target checks that this is actually the case.
pub fn generate_textmate_language_json() -> String {
    let scope = |ty| token_scope(ty).unwrap();

    // TextMate always continues matching at the end of the previous token, preferring the earliest match.
    //   If multiple patterns match at the same position, the first one in this list wins.
    let mut patterns = vec![];

    // comments, block comments can nest so they need to refer to themselves through the repository
    patterns.push(json!({ "name": scope(TokenType::LineComment), "match": "//.*$" }));
    patterns.push(json!({ "include": "#block_comment" }));
    let block_comment = json!({
        "name": scope(TokenType::BlockComment),
        "begin": "/\\*",
        "end": "\\*/",
        "patterns": [{ "include": "#block_comment" }],
    });

    // strings, escapes are matched separately so they don't end the string or start a substitution.
    // braces can nest inside a substitution, so they refer to themselves through the repository,
    //   and the braces are scoped separately to match the OpenC/CloseC tokens the tokenizer emits.
    let escape = json!({ "match": format!("\\\\{}", REGEX_STRING_ESCAPE_CHARS) });
    let nested_brace = json!({
        "begin": "\\{",
        "end": "\\}",
        "beginCaptures": { "0": { "name": scope(TokenType::OpenC) } },
        "endCaptures": { "0": { "name": scope(TokenType::CloseC) } },
        "patterns": [{ "include": "#nested_brace" }, { "include": "$self" }],
    });
    let substitution = json!({
        "name": scope(TokenType::StringSubStart),
        "begin": "\\{",
        "end": "\\}",
        "patterns": [{ "include": "#nested_brace" }, { "include": "$self" }],
    });
    patterns.push(json!({
        "name": scope(TokenType::StringStart),
        "begin": "r\"",
        "end": "\"",
        "patterns": [escape],
    }));
    patterns.push(json!({
        "name": scope(TokenType::StringStart),
        "begin": "\"",
        "end": "\"",
        "patterns": [escape, substitution],
    }));

    // int literals, the exact format is validated by the tokenizer later
    patterns.push(json!({
        "name": scope(TokenType::IntLiteralDecimal),
        "match": format!("{REGEX_INT_START}{REGEX_INT_CONTINUE}*"),
    }));

    // fixed tokens, longer ones first so eg. `+=` wins over `+`
    for info in TokenType::FIXED_TOKENS
        .iter()
        .sorted_by_key(|info| std::cmp::Reverse(info.literal.len()))
    {
        let Some(scope) = token_scope(info.ty) else {
            continue;
        };
        let literal = escape_textmate_regex(info.literal);
        let pattern = if str_is_valid_identifier(info.literal) {
            // keywords should not match a prefix of a longer identifier
            format!("{literal}(?!{REGEX_ID_CONTINUE})")
        } else if info.literal.ends_with('/') {
            // symbols should not steal the start of a comment, matching the tokenizer
            format!("{literal}(?![/*])")
        } else {
            literal
        };
        patterns.push(json!({ "name": scope, "match": pattern }));
    }

    // identifiers, after keywords so those take priority
    patterns.push(json!({
        "name": scope(TokenType::Identifier),
        "match": format!("{REGEX_ID_START}{REGEX_ID_CONTINUE}*"),
    }));

    let lang = json!({
        "$schema": "https://raw.githubusercontent.com/martinring/tmlanguage/master/tmlanguage.json",
        "name": KHDL_LANGUAGE_NAME,
        "scopeName": source_scope(),
        "patterns": patterns,
        "repository": {
            "block_comment": { "patterns": [block_comment] },
            "nested_brace": { "patterns": [nested_brace] },
        },
    });
    serde_json::to_string_pretty(&lang).unwrap()
}

/// The scope of the entire source file.
pub fn source_scope() -> String {
    name("source")
}

/// The innermost scope that the generated grammar assigns to tokens of the given type,
///   or `None` if the grammar does not match tokens of this type at all.
pub fn token_scope(ty: TokenType) -> Option<String> {
    let base = match ty {
        TokenType::LineComment => "comment.line.double-slash".to_owned(),
        TokenType::BlockComment => "comment.block".to_owned(),
        TokenType::Identifier => "identifier".to_owned(),
        TokenType::IntLiteralBinary | TokenType::IntLiteralDecimal | TokenType::IntLiteralHexadecimal => {
            "constant.numeric".to_owned()
        }
        TokenType::StringStart | TokenType::StringMiddle | TokenType::StringEnd => "string.quoted.double".to_owned(),
        TokenType::StringSubStart | TokenType::StringSubEnd => "meta.string_substitution".to_owned(),
        _ => format!("{}.{}", fixed_token_category(ty)?, ty.name().to_lowercase()),
    };
    Some(name(&base))
}

/// Add the per-language suffix to a scope name.
fn name(base: &str) -> String {
    format!("{base}.{}", KHDL_LANGUAGE_NAME.to_ascii_lowercase())
}

fn fixed_token_category(ty: TokenType) -> Option<&'static str> {
    match ty {
        // custom tokens are handled in `token_scope`
        TokenType::BlockComment
        | TokenType::LineComment
        | TokenType::Identifier
        | TokenType::IntLiteralBinary
        | TokenType::IntLiteralDecimal
        | TokenType::IntLiteralHexadecimal
        | TokenType::StringStart
        | TokenType::StringEnd
        | TokenType::StringSubStart
        | TokenType::StringSubEnd
        | TokenType::StringMiddle => None,
        // control
        TokenType::Import
        | TokenType::Return
        | TokenType::Break
        | TokenType::Continue
        | TokenType::If
        | TokenType::Else
        | TokenType::Loop
        | TokenType::Match
        | TokenType::For
        | TokenType::While => Some("keyword.control"),
        // type and variable defs
        TokenType::Type
        | TokenType::Struct
        | TokenType::Enum
        | TokenType::Module
        | TokenType::Const
        | TokenType::Val
        | TokenType::Var
        | TokenType::Wire
        | TokenType::Reg
        | TokenType::Ref
        | TokenType::Deref => Some("storage.type"),
        // storage modifiers
        TokenType::External => Some("storage.modifier"),
        // literals
        TokenType::True | TokenType::False | TokenType::Undef => Some("constant.language"),
        // other keywords
        TokenType::Interface
        | TokenType::View
        | TokenType::Ports
        | TokenType::Port
        | TokenType::Slf
        | TokenType::Instance
        | TokenType::Connect
        | TokenType::Fn
        | TokenType::Comb
        | TokenType::Clock
        | TokenType::Clocked
        | TokenType::In
        | TokenType::Out
        | TokenType::Async
        | TokenType::Sync
        | TokenType::Pub
        | TokenType::As
        | TokenType::Builtin
        | TokenType::UnsafeValueWithDomain
        | TokenType::Ident => Some("keyword.other"),
        // punctuation
        TokenType::Semi
        | TokenType::Colon
        | TokenType::Comma
        | TokenType::Arrow
        | TokenType::DoubleArrow
        | TokenType::Underscore
        | TokenType::ColonColon
        | TokenType::OpenC
        | TokenType::CloseC
        | TokenType::OpenR
        | TokenType::CloseR
        | TokenType::OpenS
        | TokenType::CloseS => Some("punctuation"),
        // operators
        TokenType::Dot
        | TokenType::DotDot
        | TokenType::DotDotEq
        | TokenType::PlusDotDot
        | TokenType::AmperAmper
        | TokenType::PipePipe
        | TokenType::CaretCaret
        | TokenType::EqEq
        | TokenType::Neq
        | TokenType::Gte
        | TokenType::Gt
        | TokenType::Lte
        | TokenType::Lt
        | TokenType::Amper
        | TokenType::Pipe
        | TokenType::Caret
        | TokenType::LtLt
        | TokenType::GtGt
        | TokenType::Plus
        | TokenType::Minus
        | TokenType::Star
        | TokenType::Slash
        | TokenType::PlusSlash
        | TokenType::Percent
        | TokenType::Bang
        | TokenType::StarStar
        | TokenType::Eq
        | TokenType::PlusEq
        | TokenType::MinusEq
        | TokenType::StarEq
        | TokenType::SlashEq
        | TokenType::PercentEq
        | TokenType::AmperEq
        | TokenType::PipeEq
        | TokenType::CaretEq => Some("keyword.operator"),
    }
}

/// Escape a literal string.
/// The result, when used as a regex in a TextMate language, will only match exactly the given string.
fn escape_textmate_regex(literal: &str) -> String {
    let mut f = String::new();
    for c in literal.chars() {
        if ".*+?[](){}|^$\\".contains(c) {
            f.push('\\');
        }
        f.push(c);
    }
    f
}

#[cfg(test)]
mod tests {
    use crate::syntax::external::textmate::generate_textmate_language_json;
    use khdl_util::io::{IoAction, IoErrorExt};

    #[test]
    fn matches_textmate_grammar() {
        let expected = generate_textmate_language_json();

        let path_rel = "../../lsp_client/syntaxes/khdl.tmLanguage.json";
        let path_abs = std::env::current_dir().unwrap().join(path_rel);

        // TODO find a batter way to update the actual grammar
        // std::fs::write(&path_abs, &expected).unwrap();

        let actual = std::fs::read_to_string(&path_abs)
            .map_err(|e| e.with_context(IoAction::Read, path_abs))
            .unwrap();

        assert_eq!(expected, actual);
    }
}
