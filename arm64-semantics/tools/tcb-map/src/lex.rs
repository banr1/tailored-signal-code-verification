// Copyright 2026 Google LLC
//
// All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
// limitations under the License.

//! Lean 4 lexical scanner: comment/string stripping, `import` edges, `@[...]` attributes,
//! and docstrings (`[OUTSIDE TCB]`, `[AUDIT/LINTER]` front-end).
//!
//! # Purpose & Trust Role
//! - **Trust Role:** `[OUTSIDE TCB]`. Shared lexical front-end for `tcb-map` and `repo-common`,
//!   so comments and string/char literals can neither mask nor trigger matches in audit tools.
//!   It never affects what the Lean kernel checks.
//! - **Purpose:** [`lex`] blanks `--` line comments, nested `/- ... -/` block comments
//!   (including `/-- ... -/` docstrings and `/-! ... -/` module docs), `"..."` strings, `r#"..."#`
//!   raw strings, and `'c'` char literals with spaces, preserving every `\n` and the byte length,
//!   so byte offsets and line numbers in the stripped code match the raw source exactly.
//!
//! # Key Types & Functions
//! - [`strip_comments_and_strings`], [`lex`] / [`Stripped`], [`Comment`], [`CommentKind`].
//! - [`ImportEdge`] / [`extract_imports`] / [`extract_imports_from_str`].
//! - [`Attribute`] / [`declaration_attributes`].
//! - [`clean_doc_comment`]: `/-- ... -/` text -> dedented docstring body.
//! - [`ident_char_before`], [`line_starts`], [`skip_ws`]: low-level byte helpers shared with
//!   `repo-common::lean_scan`.

use regex::Regex;
use std::sync::LazyLock;

// ---------------------------------------------------------------------------------------------
// Lexing
// ---------------------------------------------------------------------------------------------

/// The syntactic kind of a Lean comment.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum CommentKind {
    /// `-- ...` up to (not including) the newline.
    Line,
    /// `/- ... -/` (nestable).
    Block,
    /// `/-- ... -/` declaration docstring.
    Doc,
    /// `/-! ... -/` module/section documentation.
    ModuleDoc,
}

/// A comment's kind and byte range `[start, end)` in the source.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct Comment {
    pub kind: CommentKind,
    pub start: usize,
    pub end: usize,
}

/// Result of [`lex`]: the stripped code and every top-level comment in source order.
#[derive(Debug, Clone)]
pub struct Stripped {
    /// The source with comments and string/char literals replaced by spaces (newlines kept).
    pub code: String,
    /// Top-level comments in source order (nested block comments are part of their parent).
    pub comments: Vec<Comment>,
}

/// Blank out Lean comments (`--` line comments and nestable `/- ... -/` block comments), string
/// literals (`"..."`, `r#"..."#`), and char literals (`'c'`) with spaces, preserving `\n` line
/// breaks and byte length so line numbers and byte offsets remain exact.
pub fn strip_comments_and_strings(source: &str) -> String {
    lex(source).code
}

/// Can the character ending at byte `i` of `source` continue an identifier? Used to tell a
/// char literal `'a'` from a primed identifier `x'` and a raw string `r"..."` from `fooR"`.
pub fn ident_char_before(source: &str, i: usize) -> bool {
    source[..i]
        .chars()
        .next_back()
        .is_some_and(|c| c.is_alphanumeric() || matches!(c, '_' | '\'' | '!' | '?'))
}

/// If a char literal starts at byte `i` (`source[i] == '\''`), return the byte just past it.
fn char_literal_end(source: &str, i: usize) -> Option<usize> {
    let rest = &source[i + 1..];
    let mut chars = rest.char_indices();
    let (_, c) = chars.next()?;
    let body_end = match c {
        '\'' | '\n' => return None,
        '\\' => {
            let (j, e) = chars.next()?;
            let mut end = j + e.len_utf8();
            match e {
                'x' => end += 2,
                'u' if rest.get(end..)?.starts_with('{') => end += rest[end..].find('}')? + 1,
                'u' => end += 4,
                _ => {}
            }
            end
        }
        _ => c.len_utf8(),
    };
    rest.get(body_end..)?
        .starts_with('\'')
        .then_some(i + 1 + body_end + 1)
}

/// If a raw string `r"..."` / `r#"..."#` starts at byte `i`, return the byte just past it (or
/// the end of input if it is unterminated).
fn raw_string_end(source: &str, i: usize) -> Option<usize> {
    let bytes = source.as_bytes();
    let mut j = i + 1;
    while j < bytes.len() && bytes[j] == b'#' {
        j += 1;
    }
    if bytes.get(j) != Some(&b'"') {
        return None;
    }
    let closing = format!("\"{}", "#".repeat(j - i - 1));
    let body = j + 1;
    Some(
        source[body..]
            .find(&closing)
            .map_or(source.len(), |k| body + k + closing.len()),
    )
}

/// Lex `source`, blanking comments and string/char literals (see [`strip_comments_and_strings`])
/// and recording the byte range and kind of every top-level comment.
pub fn lex(source: &str) -> Stripped {
    let bytes = source.as_bytes();
    let n = bytes.len();
    let mut out: Vec<u8> = bytes.to_vec();
    let mut comments = Vec::new();
    let blank = |out: &mut [u8], start: usize, stop: usize| {
        for b in &mut out[start..stop] {
            if *b != b'\n' {
                *b = b' ';
            }
        }
    };

    let mut i = 0;
    while i < n {
        let next = bytes.get(i + 1).copied();
        if bytes[i] == b'/' && next == Some(b'-') {
            let kind = match bytes.get(i + 2) {
                Some(b'-') => CommentKind::Doc,
                Some(b'!') => CommentKind::ModuleDoc,
                _ => CommentKind::Block,
            };
            let start = i;
            let mut depth = 1usize;
            i += 2;
            while i < n && depth > 0 {
                if bytes[i] == b'/' && bytes.get(i + 1) == Some(&b'-') {
                    depth += 1;
                    i += 2;
                } else if bytes[i] == b'-' && bytes.get(i + 1) == Some(&b'/') {
                    depth -= 1;
                    i += 2;
                } else {
                    i += 1;
                }
            }
            let end = i.min(n);
            blank(&mut out, start, end);
            comments.push(Comment { kind, start, end });
            i = end;
        } else if bytes[i] == b'-' && next == Some(b'-') {
            let end = source[i..].find('\n').map_or(n, |k| i + k);
            blank(&mut out, i, end);
            comments.push(Comment {
                kind: CommentKind::Line,
                start: i,
                end,
            });
            i = end;
        } else if bytes[i] == b'"' {
            let mut j = i + 1;
            while j < n {
                match bytes[j] {
                    b'\\' => j += 2,
                    b'"' => {
                        j += 1;
                        break;
                    }
                    _ => j += 1,
                }
            }
            let stop = j.min(n);
            blank(&mut out, i, stop);
            i = stop;
        } else if bytes[i] == b'\''
            && !ident_char_before(source, i)
            && let Some(end) = char_literal_end(source, i)
        {
            blank(&mut out, i, end);
            i = end;
        } else if bytes[i] == b'r'
            && !ident_char_before(source, i)
            && let Some(end) = raw_string_end(source, i)
        {
            blank(&mut out, i, end);
            i = end;
        } else {
            i += 1;
        }
    }

    let code = String::from_utf8(out)
        .expect("blanking ranges delimited by ASCII bytes with spaces preserves UTF-8");
    Stripped { code, comments }
}

/// Strip the `/--` (or `/-!`) opener and `-/` closer from a doc comment, drop up to four
/// leading spaces of indentation per line, and trim the result.
pub fn clean_doc_comment(comment_text: &str) -> String {
    let t = comment_text.trim();
    let t = t
        .strip_prefix("/--")
        .or_else(|| t.strip_prefix("/-!"))
        .unwrap_or(t);
    let t = t.trim_end();
    let t = t.strip_suffix("-/").unwrap_or(t);
    t.lines()
        .map(|l| {
            let drop = l.bytes().take(4).take_while(|&b| b == b' ').count();
            &l[drop..]
        })
        .collect::<Vec<_>>()
        .join("\n")
        .trim()
        .to_string()
}

// ---------------------------------------------------------------------------------------------
// Imports and attributes
// ---------------------------------------------------------------------------------------------

static HEADER_IMPORT_LINE_RE: LazyLock<Regex> = LazyLock::new(|| {
    Regex::new(r"^\s*(?:(?:module|prelude)\s+)*(?:(?:public|meta)\s+)*import\s+").unwrap()
});

static IMPORT_CLAUSE_RE: LazyLock<Regex> = LazyLock::new(|| {
    Regex::new(
        r"((?:(?:public|meta)\s+)*)\bimport\s+(all\s+)?((?:(?:[A-Za-z0-9_']+|«[^»]+»)\.)*(?:[A-Za-z0-9_']+|«[^»]+»))",
    )
    .unwrap()
});

/// A direct `import` edge in a Lean source file.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ImportEdge {
    /// Imported module name with `«»` quotes removed.
    pub imported: String,
    /// 1-based line of the `import`.
    pub line: usize,
    /// The trimmed raw source line.
    pub raw_line: String,
    /// Whether this import clause carries the `public` modifier (`public import ...`).
    pub is_public: bool,
    /// Whether this import clause carries the `meta` modifier (`meta import ...`).
    pub is_meta: bool,
    /// Whether this import clause carries `all` (`import all ...`).
    pub is_all: bool,
}

fn collect_imports_on_line(
    code_line: &str,
    raw_line: Option<&str>,
    line_num: usize,
    out: &mut Vec<ImportEdge>,
) {
    if !code_line.contains("import") || !HEADER_IMPORT_LINE_RE.is_match(code_line) {
        return;
    }
    let raw_trimmed = raw_line
        .map(|s| s.trim().to_string())
        .unwrap_or_else(|| code_line.trim().to_string());
    let bytes = code_line.as_bytes();
    for caps in IMPORT_CLAUSE_RE.captures_iter(code_line) {
        let full = caps.get(0).unwrap();
        let before_ok = full.start() == 0 || bytes[full.start() - 1].is_ascii_whitespace();
        let after_ok = full.end() == bytes.len() || bytes[full.end()].is_ascii_whitespace();
        if before_ok && after_ok {
            let mods = caps.get(1).map_or("", |m| m.as_str());
            let is_public = mods.split_whitespace().any(|t| t == "public");
            let is_meta = mods.split_whitespace().any(|t| t == "meta");
            let is_all = caps.get(2).is_some();
            let imported = caps.get(3).unwrap().as_str().replace(['«', '»'], "");
            out.push(ImportEdge {
                imported,
                line: line_num,
                raw_line: raw_trimmed.clone(),
                is_public,
                is_meta,
                is_all,
            });
        }
    }
}

/// Extract all `import <Module>` edges from stripped code lines and raw source lines.
pub fn extract_imports<S: AsRef<str>>(code_lines: &[S], raw_lines: &[S]) -> Vec<ImportEdge> {
    let mut imports = Vec::new();
    for (idx, code_line) in code_lines.iter().enumerate() {
        collect_imports_on_line(
            code_line.as_ref(),
            raw_lines.get(idx).map(S::as_ref),
            idx + 1,
            &mut imports,
        );
    }
    imports
}

/// Extract all `import <Module>` edges directly from whole-file `code` and raw `source` strings
/// without allocating intermediate `Vec<String>` line slices.
pub fn extract_imports_from_str(code: &str, source: &str) -> Vec<ImportEdge> {
    if !code.contains("import") {
        return Vec::new();
    }
    let mut imports = Vec::new();
    let mut raw_iter = source.lines();
    for (idx, code_line) in code.lines().enumerate() {
        let raw_opt = raw_iter.next();
        collect_imports_on_line(code_line, raw_opt, idx + 1, &mut imports);
    }
    imports
}

/// A single attribute in a declaration's `@[...]` list.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Attribute {
    /// 1-based line on which the attribute's entry starts.
    pub line: usize,
    /// Byte offset at which the attribute's entry starts.
    pub offset: usize,
    /// Attribute name, e.g. `simp` or `implemented_by`.
    pub name: String,
}

/// Byte offsets of the start of every line of `text` (line `k` (1-based) starts at `[k - 1]`).
pub fn line_starts(text: &str) -> Vec<usize> {
    std::iter::once(0)
        .chain(text.match_indices('\n').map(|(i, _)| i + 1))
        .collect()
}

/// Advance `p` past ASCII whitespace in `bytes`.
pub fn skip_ws(bytes: &[u8], mut p: usize) -> usize {
    while p < bytes.len() && bytes[p].is_ascii_whitespace() {
        p += 1;
    }
    p
}

/// Extract every attribute from the `@[attr₁, attr₂ args, ...]` and
/// `attribute [attr₁, attr₂ args, ...]` lists in `code` (comments and strings already stripped).
/// Lists may span lines, entries are split at top-level commas (commas nested in `()`/`[]`/`{}`
/// belong to an entry's arguments), and `local`/`scoped` modifiers are skipped so that the
/// attribute's own name is reported.
pub fn declaration_attributes(code: &str) -> Vec<Attribute> {
    if !code.contains("@[") && !code.contains("attribute") {
        return Vec::new();
    }
    let bytes = code.as_bytes();
    let starts = line_starts(code);
    let line_at = |pos: usize| starts.partition_point(|&s| s <= pos);
    let mut attrs = Vec::new();
    let mut entry_name = |start: usize, end: usize| {
        let entry = code[start..end].trim_start();
        let entry = ["local", "scoped"]
            .iter()
            .find_map(|m| {
                entry
                    .strip_prefix(m)
                    .filter(|rest| rest.starts_with(char::is_whitespace))
            })
            .unwrap_or(entry)
            .trim_start();
        let name: String = entry
            .chars()
            .take_while(|c| {
                c.is_alphanumeric() || matches!(c, '_' | '.' | '!' | '?' | '\'' | '«' | '»')
            })
            .filter(|&c| !matches!(c, '«' | '»'))
            .collect();
        if !name.is_empty() {
            let offset = start + (code[start..end].len() - code[start..end].trim_start().len());
            attrs.push(Attribute {
                line: line_at(offset),
                offset,
                name,
            });
        }
    };

    let next_bracket = |from: usize| -> Option<usize> {
        let mut best = code[from..].find("@[").map(|rel| from + rel + 1);
        let mut p = from;
        while let Some(rel) = code[p..].find("attribute") {
            let kw = p + rel;
            let after_kw = kw + "attribute".len();
            p = after_kw;
            if ident_char_before(code, kw) {
                continue;
            }
            let open = skip_ws(bytes, after_kw);
            if bytes.get(open) == Some(&b'[') {
                best = Some(best.map_or(open, |b| b.min(open)));
                break;
            }
        }
        best
    };

    let mut i = 0;
    while let Some(open) = next_bracket(i) {
        let mut depth = 1;
        let mut entry_start = open + 1;
        let mut j = open + 1;
        while j < bytes.len() && depth > 0 {
            match bytes[j] {
                b'(' | b'[' | b'{' => depth += 1,
                b')' | b']' | b'}' => {
                    depth -= 1;
                    if depth == 0 {
                        entry_name(entry_start, j);
                    }
                }
                b',' if depth == 1 => {
                    entry_name(entry_start, j);
                    entry_start = j + 1;
                }
                _ => {}
            }
            j += 1;
        }
        if depth > 0 {
            entry_name(entry_start, bytes.len());
        }
        i = j;
    }
    attrs
}
