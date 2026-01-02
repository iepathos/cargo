//! Support for fixing the `exported_private_dependencies` lint by modifying Cargo.toml.
//!
//! When a crate's public API exposes types from a private dependency, rustc emits the
//! `exported_private_dependencies` warning. This module provides the ability to automatically
//! fix these warnings by adding `public = true` to the affected dependencies in Cargo.toml.
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

use std::collections::{HashMap, HashSet};
use std::path::{Path, PathBuf};

use anyhow::Context as _;
use rustfix::diagnostics::Diagnostic;

use crate::CargoResult;
use crate::util::toml_mut::manifest::LocalManifest;

/// Represents a dependency that needs to be marked as public.
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct PublicDepFix {
    /// Name of the dependency package (the actual crate name, not the rename/alias).
    pub package_name: String,
    /// Path to the Cargo.toml manifest file.
    pub manifest_path: PathBuf,
}

/// Result of applying public dependency fixes.
#[derive(Debug, Default)]
pub struct PublicDepFixResult {
    /// Number of fixes successfully applied.
    pub applied: usize,
    /// Errors encountered while applying fixes (manifest path, error).
    pub errors: Vec<(PathBuf, anyhow::Error)>,
}

/// Collects public dependency fixes from rustc diagnostics.
///
/// Parses diagnostics looking for the `exported_private_dependencies` lint and extracts
/// the dependency names that need to be marked as public.
pub fn collect_public_dep_fixes(
    diagnostics: &[Diagnostic],
    source_file: &Path,
) -> Vec<PublicDepFix> {
    let manifest_path = match find_manifest_from_source(source_file) {
        Some(path) => path,
        None => return Vec::new(),
    };

    let mut fixes = HashSet::new();

    for diagnostic in diagnostics {
        if !is_exported_private_deps_lint(diagnostic) {
            continue;
        }

        if let Some(dep_name) = parse_dep_name_from_message(&diagnostic.message) {
            fixes.insert(PublicDepFix {
                package_name: dep_name,
                manifest_path: manifest_path.clone(),
            });
        }
    }

    fixes.into_iter().collect()
}

/// Applies public dependency fixes to manifest files.
///
/// Modifies Cargo.toml files to add `public = true` to the specified dependencies.
/// Returns a result containing the number of fixes applied and any errors encountered.
pub fn apply_public_dep_fixes(fixes: &[PublicDepFix]) -> PublicDepFixResult {
    let mut result = PublicDepFixResult::default();

    // Group fixes by manifest path to avoid multiple reads/writes
    let mut by_manifest: HashMap<&PathBuf, Vec<&str>> = HashMap::new();
    for fix in fixes {
        by_manifest
            .entry(&fix.manifest_path)
            .or_default()
            .push(&fix.package_name);
    }

    for (manifest_path, dep_names) in by_manifest {
        match apply_fixes_to_manifest(manifest_path, &dep_names) {
            Ok(count) => result.applied += count,
            Err(e) => result.errors.push((manifest_path.clone(), e)),
        }
    }

    result
}

/// Finds the Cargo.toml manifest file from a source file path.
///
/// Walks up the directory tree looking for Cargo.toml.
/// Returns an absolute path since LocalManifest requires it.
fn find_manifest_from_source(source_file: &Path) -> Option<PathBuf> {
    // Canonicalize the source file to get an absolute path
    let source_file = source_file.canonicalize().ok()?;
    let mut dir = source_file.parent()?;
    loop {
        let manifest = dir.join("Cargo.toml");
        if manifest.exists() {
            return Some(manifest);
        }
        dir = dir.parent()?;
    }
}

/// Applies fixes to a single manifest file.
fn apply_fixes_to_manifest(manifest_path: &Path, dep_names: &[&str]) -> CargoResult<usize> {
    let mut manifest = LocalManifest::try_new(manifest_path)
        .with_context(|| format!("failed to read `{}`", manifest_path.display()))?;

    let mut count = 0;
    for dep_name in dep_names {
        if mark_dependency_public(&mut manifest, dep_name) {
            count += 1;
        }
    }

    if count > 0 {
        manifest
            .write()
            .with_context(|| format!("failed to write `{}`", manifest_path.display()))?;
    }

    Ok(count)
}

/// Marks a dependency as public in the manifest.
///
/// Searches `[dependencies]` and `[target.*.dependencies]` tables for the dependency.
fn mark_dependency_public(manifest: &mut LocalManifest, dep_name: &str) -> bool {
    let document = manifest.data.as_table_mut();

    let modified_top = mark_dep_in_table(document, dep_name);
    let modified_targets = mark_dep_in_target_tables(document, dep_name);

    modified_top || modified_targets
}

/// Marks a dependency as public in the `[dependencies]` table.
///
/// Only checks `[dependencies]`, not `[dev-dependencies]` or `[build-dependencies]`,
/// since the `exported_private_dependencies` lint only fires for regular dependencies
/// that are exposed in the public API.
fn mark_dep_in_table(table: &mut toml_edit::Table, dep_name: &str) -> bool {
    if let Some(deps) = table.get_mut("dependencies").and_then(|v| v.as_table_mut()) {
        return add_public_to_dependency(deps, dep_name);
    }
    false
}

/// Marks a dependency as public in target-specific `[target.*.dependencies]` tables.
fn mark_dep_in_target_tables(document: &mut toml_edit::Table, dep_name: &str) -> bool {
    let Some(target_table) = document.get_mut("target").and_then(|v| v.as_table_mut()) else {
        return false;
    };

    let mut modified = false;
    for (_target, target_value) in target_table.iter_mut() {
        if let Some(target_deps) = target_value.as_table_mut() {
            if mark_dep_in_table(target_deps, dep_name) {
                modified = true;
            }
        }
    }
    modified
}

/// Checks if a diagnostic is the `exported_private_dependencies` lint.
fn is_exported_private_deps_lint(diagnostic: &Diagnostic) -> bool {
    diagnostic
        .code
        .as_ref()
        .is_some_and(|c| c.code == "exported_private_dependencies")
}

/// Parses the dependency name from an `exported_private_dependencies` lint message.
///
/// Expected format: `<type> `<type_name>` from private dependency '<crate_name>' in public interface`
fn parse_dep_name_from_message(message: &str) -> Option<String> {
    // Look for the pattern: from private dependency '<name>'
    let marker = "from private dependency '";
    let start = message.find(marker)? + marker.len();
    let rest = &message[start..];
    let end = rest.find('\'')?;
    Some(rest[..end].to_string())
}

/// Adds `public = true` to a dependency in a dependencies table.
///
/// Handles both simple version strings and inline tables.
fn add_public_to_dependency(deps_table: &mut toml_edit::Table, dep_name: &str) -> bool {
    // Try direct name match first
    if let Some(dep_value) = deps_table.get_mut(dep_name) {
        return set_public_true(dep_value);
    }

    // Check for renamed dependencies (package = "dep_name")
    for (_key, value) in deps_table.iter_mut() {
        if let Some(table) = value.as_table_like_mut() {
            if let Some(pkg) = table.get("package") {
                if pkg.as_str() == Some(dep_name) {
                    return set_public_true(value);
                }
            }
        }
    }

    false
}

/// Sets `public = true` on a dependency value.
///
/// Converts simple version strings to inline tables as needed.
/// Skips if `public` is already explicitly set (to any value).
fn set_public_true(dep_value: &mut toml_edit::Item) -> bool {
    // Skip if public is already explicitly set (to any value)
    if let Some(table) = dep_value.as_table_like() {
        if table.get("public").is_some() {
            return false;
        }
    }

    match dep_value {
        toml_edit::Item::Value(toml_edit::Value::String(version_str)) => {
            // Convert "version" to { version = "...", public = true }
            let version = version_str.value().clone();
            let mut inline = toml_edit::InlineTable::new();
            inline.insert("version", toml_edit::Value::from(version));
            inline.insert("public", toml_edit::Value::from(true));
            *dep_value = toml_edit::Item::Value(toml_edit::Value::InlineTable(inline));
            true
        }
        toml_edit::Item::Value(toml_edit::Value::InlineTable(table)) => {
            table.insert("public", toml_edit::Value::from(true));
            true
        }
        toml_edit::Item::Table(table) => {
            table.insert("public", toml_edit::value(true));
            true
        }
        _ => false,
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    /// Helper to create a Diagnostic from JSON for testing.
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
    fn test_set_public_true_version_string() {
        let mut item = toml_edit::Item::Value(toml_edit::Value::from("1.0"));
        assert!(set_public_true(&mut item));
        let table = item.as_inline_table().unwrap();
        assert_eq!(table.get("version").and_then(|v| v.as_str()), Some("1.0"));
        assert_eq!(table.get("public").and_then(|v| v.as_bool()), Some(true));
    }

    #[test]
    fn test_set_public_true_inline_table() {
        let mut inline = toml_edit::InlineTable::new();
        inline.insert("version", toml_edit::Value::from("1.0"));
        let mut item = toml_edit::Item::Value(toml_edit::Value::InlineTable(inline));
        assert!(set_public_true(&mut item));
        let table = item.as_inline_table().unwrap();
        assert_eq!(table.get("public").and_then(|v| v.as_bool()), Some(true));
    }

    #[test]
    fn test_set_public_true_skips_existing_true() {
        let mut inline = toml_edit::InlineTable::new();
        inline.insert("version", toml_edit::Value::from("1.0"));
        inline.insert("public", toml_edit::Value::from(true));
        let mut item = toml_edit::Item::Value(toml_edit::Value::InlineTable(inline));
        assert!(!set_public_true(&mut item)); // Returns false, no change needed
    }

    #[test]
    fn test_set_public_true_skips_existing_false() {
        let mut inline = toml_edit::InlineTable::new();
        inline.insert("version", toml_edit::Value::from("1.0"));
        inline.insert("public", toml_edit::Value::from(false));
        let mut item = toml_edit::Item::Value(toml_edit::Value::InlineTable(inline));
        assert!(!set_public_true(&mut item)); // Respects explicit false
    }

    #[test]
    fn test_add_public_to_dependency_direct_match() {
        let mut table = toml_edit::Table::new();
        table.insert(
            "my_dep",
            toml_edit::Item::Value(toml_edit::Value::from("1.0")),
        );
        assert!(add_public_to_dependency(&mut table, "my_dep"));
        let dep = table.get("my_dep").unwrap().as_inline_table().unwrap();
        assert_eq!(dep.get("public").and_then(|v| v.as_bool()), Some(true));
    }

    #[test]
    fn test_add_public_to_dependency_renamed() {
        let mut inline = toml_edit::InlineTable::new();
        inline.insert("version", toml_edit::Value::from("1.0"));
        inline.insert("package", toml_edit::Value::from("actual_name"));
        let mut table = toml_edit::Table::new();
        table.insert(
            "alias",
            toml_edit::Item::Value(toml_edit::Value::InlineTable(inline)),
        );
        assert!(add_public_to_dependency(&mut table, "actual_name"));
        let dep = table.get("alias").unwrap().as_inline_table().unwrap();
        assert_eq!(dep.get("public").and_then(|v| v.as_bool()), Some(true));
    }

    #[test]
    fn test_add_public_to_dependency_not_found() {
        let mut table = toml_edit::Table::new();
        table.insert(
            "other_dep",
            toml_edit::Item::Value(toml_edit::Value::from("1.0")),
        );
        assert!(!add_public_to_dependency(&mut table, "missing_dep"));
    }
}
