//! Support for fixing the `exported_private_dependencies` lint by modifying Cargo.toml.
//!
//! When a crate's public API exposes types from a private dependency, rustc emits the
//! `exported_private_dependencies` warning. This module constructs machine-applicable
//! suggestions that add `public = true` to the affected dependencies in Cargo.toml.
//!
//! # Approach
//!
//! This module constructs `rustfix::Suggestion` objects that modify Cargo.toml. These
//! suggestions flow through the same rustfix infrastructure as source code fixes,
//! using byte ranges to specify replacements.
//!
//! # Rustc Message Format
//!
//! This module depends on the specific format of rustc's `exported_private_dependencies` lint
//! message. The expected format is:
//!
//! ```text
//! <type> `<type_name>` from private dependency '<crate_name>' in public interface
//! ```
//!
//! If rustc changes this message format, this module will need to be updated accordingly.

use std::collections::HashSet;
use std::fs;
use std::path::Path;

use cargo_util::paths;
use rustfix::diagnostics::Diagnostic;
use rustfix::{LinePosition, LineRange, Replacement, Snippet, Solution, Suggestion};
use tracing::trace;

/// Collects machine-applicable suggestions for fixing `exported_private_dependencies` lint.
///
/// Parses diagnostics looking for the `exported_private_dependencies` lint, then constructs
/// suggestions that add `public = true` to the affected dependencies in Cargo.toml.
pub fn collect_public_dep_suggestions(
    diagnostics: &[Diagnostic],
    source_file: &Path,
) -> Vec<Suggestion> {
    // Find the Cargo.toml for this source file
    let Some(manifest_path) = find_cargo_toml(source_file) else {
        trace!("no Cargo.toml found for {:?}", source_file);
        return Vec::new();
    };

    // Read and parse the manifest
    let Ok(manifest_content) = fs::read_to_string(&manifest_path) else {
        trace!("failed to read {:?}", manifest_path);
        return Vec::new();
    };

    let Ok(document) = manifest_content.parse::<toml_edit::DocumentMut>() else {
        trace!("failed to parse {:?} as TOML", manifest_path);
        return Vec::new();
    };

    // Collect unique dependency names from the lint diagnostics
    let dep_names: HashSet<String> = diagnostics
        .iter()
        .filter(|d| is_exported_private_deps_lint(d))
        .filter_map(|d| parse_dep_name_from_message(&d.message))
        .collect();

    if dep_names.is_empty() {
        return Vec::new();
    }

    trace!(
        "found {} unique private deps to fix: {:?}",
        dep_names.len(),
        dep_names
    );

    let manifest_path_str = manifest_path.to_string_lossy().to_string();

    // Generate suggestions for each dependency
    dep_names
        .into_iter()
        .filter_map(|dep_name| {
            create_suggestion_for_dep(&document, &manifest_content, &manifest_path_str, &dep_name)
        })
        .collect()
}

/// Finds Cargo.toml by walking up from the source file directory.
fn find_cargo_toml(source_file: &Path) -> Option<std::path::PathBuf> {
    let start_dir = source_file.parent()?;
    for dir in paths::ancestors(start_dir, None) {
        let candidate = dir.join("Cargo.toml");
        if candidate.exists() {
            return Some(candidate);
        }
    }
    None
}

/// Checks if a diagnostic is the `exported_private_dependencies` lint.
fn is_exported_private_deps_lint(diagnostic: &Diagnostic) -> bool {
    diagnostic
        .code
        .as_ref()
        .is_some_and(|c| c.code == "exported_private_dependencies")
}

/// Extracts the dependency crate name from the lint message.
///
/// Expected format: `<type> from private dependency '<crate_name>' in public interface`
fn parse_dep_name_from_message(message: &str) -> Option<String> {
    let marker = "from private dependency '";
    let start = message.find(marker)? + marker.len();
    let rest = &message[start..];
    let end = rest.find('\'')?;
    Some(rest[..end].to_string())
}

/// Creates a suggestion to add `public = true` to a dependency.
fn create_suggestion_for_dep(
    document: &toml_edit::DocumentMut,
    manifest_content: &str,
    manifest_path: &str,
    dep_name: &str,
) -> Option<Suggestion> {
    // Try standard [dependencies] table first
    try_create_suggestion(
        document,
        manifest_content,
        manifest_path,
        &["dependencies"],
        dep_name,
    )
    .or_else(|| find_in_target_deps(document, manifest_content, manifest_path, dep_name))
    .or_else(|| {
        trace!("dependency '{}' not found in manifest", dep_name);
        None
    })
}

/// Searches for a dependency in target-specific tables (e.g., [target.'cfg(...)'.dependencies]).
fn find_in_target_deps(
    document: &toml_edit::DocumentMut,
    manifest_content: &str,
    manifest_path: &str,
    dep_name: &str,
) -> Option<Suggestion> {
    document
        .get("target")?
        .as_table_like()?
        .iter()
        .find_map(|(target_name, target_value)| {
            let deps = target_value
                .as_table_like()?
                .get("dependencies")?
                .as_table_like()?;
            try_create_suggestion_in_table(
                deps,
                manifest_content,
                manifest_path,
                dep_name,
                &format!("target.{}.dependencies", target_name),
            )
        })
}

/// Tries to create a suggestion for a dependency in a specific table path.
fn try_create_suggestion(
    document: &toml_edit::DocumentMut,
    manifest_content: &str,
    manifest_path: &str,
    table_path: &[&str],
    dep_name: &str,
) -> Option<Suggestion> {
    let mut item = document.as_item();
    for key in table_path {
        item = item.get(key)?;
    }
    let deps_table = item.as_table_like()?;

    try_create_suggestion_in_table(
        deps_table,
        manifest_content,
        manifest_path,
        dep_name,
        &table_path.join("."),
    )
}

/// Creates a suggestion for a dependency found in a dependencies table.
fn try_create_suggestion_in_table(
    deps_table: &dyn toml_edit::TableLike,
    manifest_content: &str,
    manifest_path: &str,
    dep_name: &str,
    table_path: &str,
) -> Option<Suggestion> {
    // Look for the dependency by name (could be aliased via `package`)
    let (key, dep_item) = find_dependency_entry(deps_table, dep_name)?;

    // Check if already has `public` key - if so, skip
    if has_public_key(dep_item) {
        trace!(
            "dependency '{}' already has public key in {}",
            dep_name, table_path
        );
        return None;
    }

    // Handle different dependency formats
    if let Some(dep_value) = dep_item.as_value() {
        // Case 1 & 2: Simple version string or inline table
        create_suggestion_for_value(&key, dep_value, manifest_content, manifest_path, dep_name)
    } else if dep_item.is_table() {
        // Case 3: Full table format [dependencies.foo]
        create_suggestion_for_full_table(
            &key,
            manifest_content,
            manifest_path,
            dep_name,
            table_path,
        )
    } else {
        trace!(
            "dependency '{}' has unexpected format in {}",
            dep_name, table_path
        );
        None
    }
}

/// Creates a suggestion for a dependency specified as a value (string or inline table).
fn create_suggestion_for_value(
    key: &str,
    dep_value: &toml_edit::Value,
    manifest_content: &str,
    manifest_path: &str,
    dep_name: &str,
) -> Option<Suggestion> {
    // Find the span using string searching since toml_edit doesn't preserve spans.
    // Look for patterns like: `key = "..."` or `key = { ... }`
    let span = find_value_span(manifest_content, key, dep_value)?;

    // Compute the replacement text
    let old_text = &manifest_content[span.clone()];
    let new_text = compute_replacement_for_value(old_text, dep_value);

    // Compute line/column info for the snippet
    let line_range = compute_line_range(manifest_content, &span);

    let snippet = Snippet {
        file_name: manifest_path.to_string(),
        line_range,
        range: span,
    };

    let replacement = Replacement {
        snippet: snippet.clone(),
        replacement: new_text,
    };

    let solution = Solution {
        message: format!("mark `{}` as a public dependency", key),
        replacements: vec![replacement],
    };

    Some(Suggestion {
        message: format!(
            "crate `{}` is a private dependency but is used in public interface",
            dep_name
        ),
        snippets: vec![snippet],
        solutions: vec![solution],
    })
}

/// Finds the byte span of a dependency value in the manifest content.
///
/// This uses string searching since toml_edit::DocumentMut doesn't preserve spans
/// after parsing (they're replaced with strings to support editing).
fn find_value_span(
    content: &str,
    key: &str,
    value: &toml_edit::Value,
) -> Option<std::ops::Range<usize>> {
    let pattern = format!("{} = ", key);

    let mut search_start = 0;
    while let Some(key_pos) = content[search_start..].find(&pattern) {
        let abs_key_pos = search_start + key_pos;
        let value_start = abs_key_pos + pattern.len();

        // Only match keys at the start of a line (after optional whitespace)
        if !is_at_line_start(content, abs_key_pos) {
            search_start = abs_key_pos + 1;
            continue;
        }

        if let Some(end) = find_value_end(content, value_start, value) {
            return Some(value_start..end);
        }

        search_start = abs_key_pos + 1;
    }

    None
}

/// Checks if a position is at the start of a line (after optional whitespace).
fn is_at_line_start(content: &str, pos: usize) -> bool {
    let line_start = content[..pos].rfind('\n').map(|p| p + 1).unwrap_or(0);
    content[line_start..pos].chars().all(|c| c.is_whitespace())
}

/// Finds the end position of a TOML value based on its type.
fn find_value_end(content: &str, value_start: usize, value: &toml_edit::Value) -> Option<usize> {
    let rest = &content[value_start..];
    match value {
        toml_edit::Value::String(_) if rest.starts_with('"') => {
            find_string_end(rest).map(|end| value_start + end)
        }
        toml_edit::Value::InlineTable(_) if rest.starts_with('{') => {
            find_brace_end(rest).map(|end| value_start + end)
        }
        _ => None,
    }
}

/// Finds the end of a TOML string value (including the closing quote).
fn find_string_end(s: &str) -> Option<usize> {
    if !s.starts_with('"') {
        return None;
    }

    let mut chars = s.char_indices().skip(1);
    while let Some((i, c)) = chars.next() {
        if c == '\\' {
            // Skip escaped character
            chars.next();
        } else if c == '"' {
            return Some(i + 1);
        }
    }
    None
}

/// Finds the end of an inline table (including the closing brace).
fn find_brace_end(s: &str) -> Option<usize> {
    if !s.starts_with('{') {
        return None;
    }

    let mut depth = 0;
    let mut in_string = false;
    let mut escape_next = false;

    for (i, c) in s.char_indices() {
        if escape_next {
            escape_next = false;
            continue;
        }

        if c == '\\' && in_string {
            escape_next = true;
            continue;
        }

        if c == '"' {
            in_string = !in_string;
            continue;
        }

        if in_string {
            continue;
        }

        match c {
            '{' => depth += 1,
            '}' => {
                depth -= 1;
                if depth == 0 {
                    return Some(i + 1);
                }
            }
            _ => {}
        }
    }
    None
}

/// Creates a suggestion for a dependency specified as a full table [dependencies.foo].
fn create_suggestion_for_full_table(
    key: &str,
    manifest_content: &str,
    manifest_path: &str,
    dep_name: &str,
    table_path: &str,
) -> Option<Suggestion> {
    // Build the table header pattern, e.g., "[dependencies.foo]" or "[target.x.dependencies.foo]"
    let header = format!("[{}.{}]", table_path, key);

    // Find the header in the manifest
    let header_start = manifest_content.find(&header)?;

    // Find the end of the section (next section header or EOF)
    let section_start = header_start + header.len();
    let remaining = &manifest_content[section_start..];
    let section_end = remaining
        .find("\n[")
        .map(|p| section_start + p)
        .unwrap_or(manifest_content.len());

    // Find the insertion point (end of last line in section, before trailing whitespace)
    let section = &manifest_content[section_start..section_end];
    let trimmed_section = section.trim_end();
    let insert_offset = section_start + trimmed_section.len();

    // Determine the indentation to use (match existing lines in section)
    let indent = detect_indent(section);

    // Create replacement: insert a new line with public = true
    let new_line = format!("\n{}public = true", indent);

    // We'll use a zero-width insertion at the insert point
    let span = insert_offset..insert_offset;
    let line_range = compute_line_range(manifest_content, &span);

    let snippet = Snippet {
        file_name: manifest_path.to_string(),
        line_range,
        range: span,
    };

    let replacement = Replacement {
        snippet: snippet.clone(),
        replacement: new_line,
    };

    let solution = Solution {
        message: format!("mark `{}` as a public dependency", key),
        replacements: vec![replacement],
    };

    Some(Suggestion {
        message: format!(
            "crate `{}` is a private dependency but is used in public interface",
            dep_name
        ),
        snippets: vec![snippet],
        solutions: vec![solution],
    })
}

/// Detects the indentation used in a TOML section.
fn detect_indent(section: &str) -> &str {
    for line in section.lines() {
        if !line.trim().is_empty() {
            let indent_len = line.len() - line.trim_start().len();
            return &line[..indent_len];
        }
    }
    ""
}

/// Finds a dependency entry by crate name, handling both direct names and aliases.
fn find_dependency_entry<'a>(
    deps_table: &'a dyn toml_edit::TableLike,
    crate_name: &str,
) -> Option<(String, &'a toml_edit::Item)> {
    // First, try direct lookup by name
    if let Some(item) = deps_table.get(crate_name) {
        return Some((crate_name.to_string(), item));
    }

    // Search for entries where `package = "<crate_name>"` (renamed deps)
    deps_table
        .iter()
        .find(|(_, item)| get_package_name(item) == Some(crate_name))
        .map(|(key, item)| (key.to_string(), item))
}

/// Extracts the `package` value from a dependency item if present.
fn get_package_name(item: &toml_edit::Item) -> Option<&str> {
    // Inline table: `foo = { package = "bar", version = "1.0" }`
    let from_inline = || item.as_value()?.as_inline_table()?.get("package")?.as_str();

    // Full table: `[dependencies.foo]\npackage = "bar"`
    let from_full = || item.as_table_like()?.get("package")?.as_value()?.as_str();

    from_inline().or_else(from_full)
}

/// Checks if a dependency item already has a `public` key.
fn has_public_key(item: &toml_edit::Item) -> bool {
    // Check inline table (value)
    if let Some(value) = item.as_value() {
        if let Some(table) = value.as_inline_table() {
            return table.contains_key("public");
        }
    }
    // Check full table
    if let Some(table) = item.as_table_like() {
        return table.contains_key("public");
    }
    false
}

/// Computes the replacement text for a dependency value.
///
/// Handles two cases:
/// 1. Simple version string: `"1.0"` -> `{ version = "1.0", public = true }`
/// 2. Inline table: `{ version = "1.0" }` -> `{ version = "1.0", public = true }`
fn compute_replacement_for_value(old_text: &str, value: &toml_edit::Value) -> String {
    match value {
        toml_edit::Value::String(s) => {
            // Simple version string - convert to inline table
            format!("{{ version = {}, public = true }}", s)
        }
        toml_edit::Value::InlineTable(_) => {
            // Inline table - append public = true before closing brace
            let trimmed = old_text.trim_end();
            if let Some(pos) = trimmed.rfind('}') {
                let before_brace = &trimmed[..pos].trim_end();
                // Check if we need a comma
                let needs_comma = !before_brace.ends_with(',') && !before_brace.ends_with('{');
                if needs_comma {
                    format!("{}, public = true }}", before_brace)
                } else {
                    format!("{} public = true }}", before_brace)
                }
            } else {
                // Fallback - shouldn't happen for valid inline tables
                old_text.to_string()
            }
        }
        _ => {
            // Other value types (shouldn't happen for dependencies)
            old_text.to_string()
        }
    }
}

/// Computes line and column positions from byte offsets.
fn compute_line_range(content: &str, span: &std::ops::Range<usize>) -> LineRange {
    let start_pos = byte_offset_to_position(content, span.start);
    let end_pos = byte_offset_to_position(content, span.end);
    LineRange {
        start: start_pos,
        end: end_pos,
    }
}

/// Converts a byte offset to a line/column position.
fn byte_offset_to_position(content: &str, offset: usize) -> LinePosition {
    let prefix = &content[..offset.min(content.len())];
    let line = prefix.matches('\n').count() + 1;
    let last_newline = prefix.rfind('\n').map(|p| p + 1).unwrap_or(0);
    let column = offset - last_newline + 1;
    LinePosition { line, column }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn make_diagnostic(message: &str, code: Option<&str>) -> Diagnostic {
        let code_json = match code {
            Some(c) => format!(r#"{{"code": "{c}", "explanation": null}}"#),
            None => "null".to_string(),
        };
        let json = format!(
            r#"{{
                "message": "{message}",
                "code": {code_json},
                "level": "warning",
                "spans": [],
                "children": [],
                "rendered": null
            }}"#
        );
        serde_json::from_str(&json).expect("valid diagnostic JSON")
    }

    #[test]
    fn test_is_exported_private_deps_lint_true() {
        let diag = make_diagnostic(
            "type `Foo` from private dependency 'bar' in public interface",
            Some("exported_private_dependencies"),
        );
        assert!(is_exported_private_deps_lint(&diag));
    }

    #[test]
    fn test_is_exported_private_deps_lint_wrong_code() {
        let diag = make_diagnostic("some warning", Some("dead_code"));
        assert!(!is_exported_private_deps_lint(&diag));
    }

    #[test]
    fn test_is_exported_private_deps_lint_no_code() {
        let diag = make_diagnostic("some warning without code", None);
        assert!(!is_exported_private_deps_lint(&diag));
    }

    #[test]
    fn test_parse_dep_name_simple() {
        let msg = "type `Foo` from private dependency 'bar' in public interface";
        assert_eq!(parse_dep_name_from_message(msg), Some("bar".to_string()));
    }

    #[test]
    fn test_parse_dep_name_with_hyphens() {
        let msg = "struct `MyStruct` from private dependency 'my-crate-name' in public interface";
        assert_eq!(
            parse_dep_name_from_message(msg),
            Some("my-crate-name".to_string())
        );
    }

    #[test]
    fn test_parse_dep_name_no_match() {
        let msg = "some other error message";
        assert_eq!(parse_dep_name_from_message(msg), None);
    }

    #[test]
    fn test_compute_replacement_simple_version() {
        let old = r#""1.0""#;
        let value: toml_edit::Value = old.parse().unwrap();
        let result = compute_replacement_for_value(old, &value);
        assert_eq!(result, r#"{ version = "1.0", public = true }"#);
    }

    #[test]
    fn test_compute_replacement_inline_table() {
        let old = r#"{ version = "1.0" }"#;
        let value: toml_edit::Value = old.parse().unwrap();
        let result = compute_replacement_for_value(old, &value);
        assert_eq!(result, r#"{ version = "1.0", public = true }"#);
    }

    #[test]
    fn test_compute_replacement_inline_table_with_features() {
        let old = r#"{ version = "1.0", features = ["foo"] }"#;
        let value: toml_edit::Value = old.parse().unwrap();
        let result = compute_replacement_for_value(old, &value);
        assert_eq!(
            result,
            r#"{ version = "1.0", features = ["foo"], public = true }"#
        );
    }

    #[test]
    fn test_byte_offset_to_position() {
        let content = "line1\nline2\nline3";
        assert_eq!(
            byte_offset_to_position(content, 0),
            LinePosition { line: 1, column: 1 }
        );
        assert_eq!(
            byte_offset_to_position(content, 6),
            LinePosition { line: 2, column: 1 }
        );
        assert_eq!(
            byte_offset_to_position(content, 8),
            LinePosition { line: 2, column: 3 }
        );
    }

    #[test]
    fn test_find_string_end() {
        assert_eq!(find_string_end(r#""1.0""#), Some(5));
        assert_eq!(find_string_end(r#""hello world""#), Some(13));
        assert_eq!(find_string_end(r#""with \"escaped\" quotes""#), Some(25));
        assert_eq!(find_string_end(r#""#), None); // incomplete
    }

    #[test]
    fn test_find_brace_end() {
        assert_eq!(find_brace_end(r#"{ version = "1.0" }"#), Some(19));
        assert_eq!(
            find_brace_end(r#"{ version = "1.0", features = ["a", "b"] }"#),
            Some(42)
        );
        assert_eq!(find_brace_end(r#"{ nested = { inner = 1 } }"#), Some(26));
        assert_eq!(find_brace_end(r#"{"#), None); // incomplete
    }

    #[test]
    fn test_find_value_span_string() {
        let content = r#"[dependencies]
foo = "1.0"
bar = "2.0"
"#;
        let value: toml_edit::Value = r#""1.0""#.parse().unwrap();
        let span = find_value_span(content, "foo", &value);
        assert!(span.is_some());
        let span = span.unwrap();
        assert_eq!(&content[span.clone()], r#""1.0""#);
    }

    #[test]
    fn test_find_value_span_inline_table() {
        let content = r#"[dependencies]
foo = { version = "1.0" }
bar = "2.0"
"#;
        let value: toml_edit::Value = r#"{ version = "1.0" }"#.parse().unwrap();
        let span = find_value_span(content, "foo", &value);
        assert!(span.is_some());
        let span = span.unwrap();
        assert_eq!(&content[span.clone()], r#"{ version = "1.0" }"#);
    }

    #[test]
    fn test_create_suggestion_for_dep() {
        let manifest = r#"[package]
name = "test"
version = "0.1.0"

[dependencies]
priv_dep = "0.1.0"
"#;
        let doc: toml_edit::DocumentMut = manifest.parse().unwrap();
        let suggestion =
            create_suggestion_for_dep(&doc, manifest, "/path/to/Cargo.toml", "priv_dep");

        assert!(
            suggestion.is_some(),
            "should create a suggestion for priv_dep"
        );

        let suggestion = suggestion.unwrap();
        assert_eq!(suggestion.solutions.len(), 1);

        let replacement = &suggestion.solutions[0].replacements[0];
        assert!(
            replacement.replacement.contains("public = true"),
            "replacement should add public = true"
        );
    }

    #[test]
    fn test_create_suggestion_for_dep_inline_table() {
        let manifest = r#"[package]
name = "test"
version = "0.1.0"

[dependencies]
priv_dep = { version = "0.1.0" }
"#;
        let doc: toml_edit::DocumentMut = manifest.parse().unwrap();
        let suggestion =
            create_suggestion_for_dep(&doc, manifest, "/path/to/Cargo.toml", "priv_dep");

        assert!(
            suggestion.is_some(),
            "should create a suggestion for priv_dep"
        );

        let suggestion = suggestion.unwrap();
        let replacement = &suggestion.solutions[0].replacements[0];
        assert!(
            replacement.replacement.contains("public = true"),
            "replacement should add public = true"
        );
    }
}
