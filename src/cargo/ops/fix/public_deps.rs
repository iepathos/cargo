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

use std::path::Path;

use rustfix::diagnostics::Diagnostic;
use rustfix::{LinePosition, Suggestion};

/// Collects machine-applicable suggestions for fixing `exported_private_dependencies` lint.
///
/// Parses diagnostics looking for the `exported_private_dependencies` lint, then constructs
/// suggestions that add `public = true` to the affected dependencies in Cargo.toml.
pub fn collect_public_dep_suggestions(
    diagnostics: &[Diagnostic],
    _source_file: &Path,
) -> Vec<Suggestion> {
    // Filter to only exported_private_dependencies diagnostics
    let relevant: Vec<_> = diagnostics
        .iter()
        .filter(|d| is_exported_private_deps_lint(d))
        .collect();

    if relevant.is_empty() {
        return Vec::new();
    }

    // Extract dependency names from relevant diagnostics
    let dep_names: Vec<_> = relevant
        .iter()
        .filter_map(|d| parse_dep_name_from_message(&d.message))
        .collect();

    if dep_names.is_empty() {
        return Vec::new();
    }

    // TODO: Parse manifest and create suggestions
    // Placeholder manifest content - will be replaced with actual file reading
    let manifest_content = "";
    let Ok(document) = manifest_content.parse::<toml_edit::DocumentMut>() else {
        return Vec::new();
    };

    // Generate suggestions for each dependency
    dep_names
        .into_iter()
        .filter_map(|dep_name| {
            create_suggestion_for_dep(&document, manifest_content, "", &dep_name)
        })
        .collect()
}

/// Creates a suggestion to add `public = true` to a dependency.
fn create_suggestion_for_dep(
    _document: &toml_edit::DocumentMut,
    manifest_content: &str,
    _manifest_path: &str,
    dep_name: &str,
) -> Option<Suggestion> {
    // Try to find the dependency value span
    // TODO: Actually look up the dependency in the document
    let value: toml_edit::Value = r#""0.0.0""#.parse().ok()?;
    let span = find_value_span(manifest_content, dep_name, &value)?;

    // Compute replacement
    let old_text = &manifest_content[span.clone()];
    let _new_text = compute_replacement_for_value(old_text, &value);

    // Compute line range
    let _line_range = compute_line_range(manifest_content, &span);

    // TODO: Build and return actual suggestion
    None
}

/// Computes line and column positions from byte offsets.
fn compute_line_range(content: &str, span: &std::ops::Range<usize>) -> rustfix::LineRange {
    let start_pos = byte_offset_to_position(content, span.start);
    let end_pos = byte_offset_to_position(content, span.end);
    rustfix::LineRange {
        start: start_pos,
        end: end_pos,
    }
}

/// Checks if a diagnostic is the `exported_private_dependencies` lint.
fn is_exported_private_deps_lint(_diagnostic: &Diagnostic) -> bool {
    // TODO: Implement lint detection
    false
}

/// Extracts the dependency crate name from the lint message.
///
/// Expected format: `<type> from private dependency '<crate_name>' in public interface`
fn parse_dep_name_from_message(_message: &str) -> Option<String> {
    // TODO: Implement message parsing
    None
}

/// Finds the byte span of a dependency value in the manifest content.
///
/// This uses string searching since toml_edit::DocumentMut doesn't preserve spans
/// after parsing (they're replaced with strings to support editing).
fn find_value_span(
    content: &str,
    _key: &str,
    value: &toml_edit::Value,
) -> Option<std::ops::Range<usize>> {
    // TODO: Implement proper span finding
    // For now, just exercise the helper functions
    let _ = find_string_end(content);
    let _ = find_brace_end(content);

    // Check value type to determine end-finding strategy
    match value {
        toml_edit::Value::String(_) => {
            // Would use find_string_end
        }
        toml_edit::Value::InlineTable(_) => {
            // Would use find_brace_end
        }
        _ => {}
    }

    None
}

/// Computes the replacement text for a dependency value.
///
/// Handles two cases:
/// 1. Simple version string: `"1.0"` -> `{ version = "1.0", public = true }`
/// 2. Inline table: `{ version = "1.0" }` -> `{ version = "1.0", public = true }`
fn compute_replacement_for_value(old_text: &str, _value: &toml_edit::Value) -> String {
    // TODO: Implement replacement computation
    old_text.to_string()
}

/// Converts a byte offset to a line/column position.
fn byte_offset_to_position(content: &str, offset: usize) -> LinePosition {
    let prefix = &content[..offset.min(content.len())];
    let line = prefix.matches('\n').count() + 1;
    let last_newline = prefix.rfind('\n').map(|p| p + 1).unwrap_or(0);
    let column = offset - last_newline + 1;
    LinePosition { line, column }
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

    // Tests for is_exported_private_deps_lint - currently returns false (no-op)
    #[test]
    fn test_is_exported_private_deps_lint_true() {
        let diag = make_diagnostic(
            "type `Foo` from private dependency 'bar' in public interface",
            Some("exported_private_dependencies"),
        );
        // No-op: always returns false until implemented
        assert!(!is_exported_private_deps_lint(&diag));
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

    // Tests for parse_dep_name_from_message - currently returns None (no-op)
    #[test]
    fn test_parse_dep_name_simple() {
        let msg = "type `Foo` from private dependency 'bar' in public interface";
        // No-op: always returns None until implemented
        assert_eq!(parse_dep_name_from_message(msg), None);
    }

    #[test]
    fn test_parse_dep_name_with_hyphens() {
        let msg = "struct `MyStruct` from private dependency 'my-crate-name' in public interface";
        // No-op: always returns None until implemented
        assert_eq!(parse_dep_name_from_message(msg), None);
    }

    #[test]
    fn test_parse_dep_name_no_match() {
        let msg = "some other error message";
        assert_eq!(parse_dep_name_from_message(msg), None);
    }

    // Tests for compute_replacement_for_value - currently returns input unchanged (no-op)
    #[test]
    fn test_compute_replacement_simple_version() {
        let old = r#""1.0""#;
        let value: toml_edit::Value = old.parse().unwrap();
        let result = compute_replacement_for_value(old, &value);
        // No-op: returns original text unchanged until implemented
        assert_eq!(result, old);
    }

    #[test]
    fn test_compute_replacement_inline_table() {
        let old = r#"{ version = "1.0" }"#;
        let value: toml_edit::Value = old.parse().unwrap();
        let result = compute_replacement_for_value(old, &value);
        // No-op: returns original text unchanged until implemented
        assert_eq!(result, old);
    }

    #[test]
    fn test_compute_replacement_inline_table_with_features() {
        let old = r#"{ version = "1.0", features = ["foo"] }"#;
        let value: toml_edit::Value = old.parse().unwrap();
        let result = compute_replacement_for_value(old, &value);
        // No-op: returns original text unchanged until implemented
        assert_eq!(result, old);
    }

    // Tests for byte_offset_to_position - fully implemented (pure utility)
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

    // Tests for find_string_end - fully implemented (pure utility)
    #[test]
    fn test_find_string_end() {
        assert_eq!(find_string_end(r#""1.0""#), Some(5));
        assert_eq!(find_string_end(r#""hello world""#), Some(13));
        assert_eq!(find_string_end(r#""with \"escaped\" quotes""#), Some(25));
        assert_eq!(find_string_end(r#""#), None); // incomplete
    }

    // Tests for find_brace_end - fully implemented (pure utility)
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

    // Tests for find_value_span - currently returns None (no-op)
    #[test]
    fn test_find_value_span_string() {
        let content = r#"[dependencies]
foo = "1.0"
bar = "2.0"
"#;
        let value: toml_edit::Value = r#""1.0""#.parse().unwrap();
        let span = find_value_span(content, "foo", &value);
        // No-op: always returns None until implemented
        assert!(span.is_none());
    }

    #[test]
    fn test_find_value_span_inline_table() {
        let content = r#"[dependencies]
foo = { version = "1.0" }
bar = "2.0"
"#;
        let value: toml_edit::Value = r#"{ version = "1.0" }"#.parse().unwrap();
        let span = find_value_span(content, "foo", &value);
        // No-op: always returns None until implemented
        assert!(span.is_none());
    }

    // Tests for create_suggestion_for_dep - currently returns None (no-op)
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

        // No-op: always returns None until implemented
        assert!(suggestion.is_none(), "should return None until implemented");
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

        // No-op: always returns None until implemented
        assert!(suggestion.is_none(), "should return None until implemented");
    }
}
