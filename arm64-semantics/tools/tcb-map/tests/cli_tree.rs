// Copyright 2026 Google LLC
//
// All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
// limitations under the License.

//! CLI integration tests for `tcb-map --tree`, `--tree-json`, `--check-imports`, and `--check`
//! (`[AUDIT/LINTER]`).
//!
//! # Purpose & Trust Role
//! - **Trust Role:** `[AUDIT/LINTER]` (`testing` in `tcb-map --tree`).
//! - **Purpose:** Verifies that `--tree`, `--tree-json`, `--check-imports`, and `--check` work
//!   cleanly in an unbuilt checkout without `Generated/*Obj.lean` symbol tables on disk, while
//!   failing with exit code `1` (and GitHub Actions annotations when enabled) on unclassified
//!   paths or trust-boundary violations.

use std::fs;
use std::path::Path;
use std::process::Command;

fn write_unbuilt_fixture(root: &Path) {
    fs::create_dir_all(root.join("Arm64/Trusted/ISA")).unwrap();
    fs::create_dir_all(root.join("CaseStudies/Alpha")).unwrap();
    fs::write(
        root.join("Arm64/Trusted/ISA/Syntax.lean"),
        "def dummy : Nat := 0\n",
    )
    .unwrap();
    // Symbol lookup whose `CaseStudies/Alpha/Generated/AlphaPlacedObj.lean` is not materialized on disk.
    fs::write(
        root.join("CaseStudies/Alpha/Spec.lean"),
        "import CaseStudies.Alpha.Generated.AlphaPlacedObj\ndef off := alphaLib.fnOff \"alpha_fn\"\n",
    )
    .unwrap();
}

#[test]
fn cli_tree_and_check_succeed_in_unbuilt_checkout_without_generated_obj() {
    let tmp = tempfile::Builder::new()
        .prefix("tcb-map-tree-")
        .tempdir_in(env!("CARGO_TARGET_TMPDIR"))
        .expect("create temp fixture dir");
    let root = tmp.path();
    write_unbuilt_fixture(root);

    let bin = env!("CARGO_BIN_EXE_tcb-map");

    // `--check` and `--check-imports` succeed on an unbuilt checkout without `AlphaObj.lean`.
    for flag in ["--check", "--check-imports"] {
        let out = Command::new(bin)
            .arg("--root")
            .arg(root)
            .arg(flag)
            .env_remove("GITHUB_ACTIONS")
            .output()
            .expect("run tcb-map");
        assert!(
            out.status.success(),
            "expected {flag} to succeed on unbuilt checkout; stderr: {}",
            String::from_utf8_lossy(&out.stderr)
        );
    }

    // `--tree` succeeds on the same unbuilt checkout and prints the rendered hierarchy.
    let tree = Command::new(bin)
        .arg("--root")
        .arg(root)
        .arg("--tree")
        .env_remove("GITHUB_ACTIONS")
        .output()
        .expect("run tcb-map --tree");
    assert!(
        tree.status.success(),
        "expected --tree to succeed; stderr: {}",
        String::from_utf8_lossy(&tree.stderr)
    );
    assert!(tree.stderr.is_empty());
    let stdout = String::from_utf8_lossy(&tree.stdout);
    assert!(
        stdout.contains("Repository trust hierarchy (2 files, 3 loc):"),
        "{stdout}"
    );
    assert!(stdout.contains("Arm64/"), "{stdout}");
    assert!(stdout.contains("CaseStudies/"), "{stdout}");
    assert!(stdout.contains("Trust category totals:"), "{stdout}");

    // `--tree --no-case-studies` omits `CaseStudies/` and `[case-studies-tcb]`.
    let no_cs = Command::new(bin)
        .arg("--root")
        .arg(root)
        .arg("--tree")
        .arg("--no-case-studies")
        .env_remove("GITHUB_ACTIONS")
        .output()
        .expect("run tcb-map --tree --no-case-studies");
    assert!(no_cs.status.success());
    let no_cs_stdout = String::from_utf8_lossy(&no_cs.stdout);
    assert!(no_cs_stdout.contains("Arm64/"), "{no_cs_stdout}");
    assert!(!no_cs_stdout.contains("CaseStudies/"), "{no_cs_stdout}");
    assert!(
        !no_cs_stdout.contains("[case-studies-tcb]"),
        "{no_cs_stdout}"
    );

    // `--tree-json` emits valid JSON for the same unbuilt fixture.
    let json_out = Command::new(bin)
        .arg("--root")
        .arg(root)
        .arg("--tree-json")
        .env_remove("GITHUB_ACTIONS")
        .output()
        .expect("run tcb-map --tree-json");
    assert!(json_out.status.success());
    let parsed: serde_json::Value =
        serde_json::from_slice(&json_out.stdout).expect("parse --tree-json stdout");
    assert_eq!(parsed["children"]["Arm64/"]["category"], "tcb");
}

#[test]
fn cli_tree_and_check_fail_on_unclassified_path() {
    let tmp = tempfile::Builder::new()
        .prefix("tcb-map-unclassified-")
        .tempdir_in(env!("CARGO_TARGET_TMPDIR"))
        .expect("create temp fixture dir");
    let root = tmp.path();
    write_unbuilt_fixture(root);
    fs::create_dir_all(root.join("mystery_dir")).unwrap();
    fs::write(root.join("mystery_dir/unclassified.txt"), "hello\n").unwrap();

    let bin = env!("CARGO_BIN_EXE_tcb-map");

    let local = Command::new(bin)
        .arg("--root")
        .arg(root)
        .arg("--tree")
        .env_remove("GITHUB_ACTIONS")
        .output()
        .expect("run tcb-map --tree");
    assert_eq!(local.status.code(), Some(1));
    assert!(
        local.stdout.is_empty(),
        "{}",
        String::from_utf8_lossy(&local.stdout)
    );
    let local_stderr = String::from_utf8_lossy(&local.stderr);
    assert!(
        local_stderr.contains("mystery_dir/unclassified.txt:1: [unclassified-path]:"),
        "{local_stderr}"
    );

    // `--check` also fails on an unclassified path, while `--check-imports` only checks imports.
    let check_out = Command::new(bin)
        .arg("--root")
        .arg(root)
        .arg("--check")
        .env_remove("GITHUB_ACTIONS")
        .output()
        .expect("run tcb-map --check");
    assert_eq!(check_out.status.code(), Some(1));
    assert!(
        String::from_utf8_lossy(&check_out.stderr)
            .contains("mystery_dir/unclassified.txt:1: [unclassified-path]:")
    );

    let imports_only = Command::new(bin)
        .arg("--root")
        .arg(root)
        .arg("--check-imports")
        .env_remove("GITHUB_ACTIONS")
        .output()
        .expect("run tcb-map --check-imports");
    assert!(imports_only.status.success());

    let gha = Command::new(bin)
        .arg("--root")
        .arg(root)
        .arg("--tree")
        .env("GITHUB_ACTIONS", "true")
        .output()
        .expect("run tcb-map --tree in GITHUB_ACTIONS");
    assert_eq!(gha.status.code(), Some(1));
    let gha_stdout = String::from_utf8_lossy(&gha.stdout);
    let gha_stderr = String::from_utf8_lossy(&gha.stderr);
    assert!(
        gha_stdout
            .contains("::error file=mystery_dir/unclassified.txt,line=1::[unclassified-path]:"),
        "{gha_stdout}"
    );
    assert!(
        gha_stderr.contains("mystery_dir/unclassified.txt:1: [unclassified-path]:"),
        "{gha_stderr}"
    );
}
