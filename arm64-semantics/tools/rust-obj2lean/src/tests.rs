// Copyright 2026 Google LLC
//
// All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
// limitations under the License.

//! Unit and integration tests for the `rust-obj2lean` crate root (`Role::Test`, `[TEST ONLY]`).
//!
//! Covers `translation.toml` loading and resolution, CLI flag handling, `--check` diffing
//! (`write_or_check`), `print-cflags`, end-to-end C archive builds, DWARF index hints, and the
//! structural check that `[TCB]` modules never import `untrusted_lemmas`. Tests that need `zig`
//! or `cargo` toolchains are skipped (with a message) when unavailable.

use super::*;
use crate::untrusted_driver::pipeline::{
    GeneratedFile, generate_config, generate_config_with, write_or_check,
};
use crate::untrusted_driver::{
    Cli, CommandName, Toolchain, apply_overrides, load_config, load_configs,
    native_cflags_string, normalize_path, select_configs,
};
use clap::Parser;
use std::fs;
use std::path::{Path, PathBuf};

fn test_repo_root() -> PathBuf {
    Path::new(env!("CARGO_MANIFEST_DIR"))
        .parent()
        .and_then(|p| p.parent())
        .expect("CARGO_MANIFEST_DIR must be at <repo>/tools/rust-obj2lean")
        .to_path_buf()
}

/// Every `translation.toml` under the in-repo campaign roots that exists on disk, sorted.
///
/// Discovered instead of hardcoded so the tests keep passing in partial exports of this
/// repository that drop some `CaseStudies/<Campaign>` directories.
fn discover_repo_config_paths(roots: &[&str]) -> Vec<PathBuf> {
    fn walk(dir: &Path, out: &mut Vec<PathBuf>) {
        let Ok(entries) = fs::read_dir(dir) else {
            return;
        };
        for entry in entries.flatten() {
            let path = entry.path();
            let name = entry.file_name();
            let name = name.to_string_lossy();
            let Ok(ft) = entry.file_type() else { continue };
            if ft.is_dir() {
                if name.starts_with('.')
                    || matches!(
                        name.as_ref(),
                        "target" | "vendor" | "Generated" | "node_modules" | "build"
                    )
                {
                    continue;
                }
                walk(&path, out);
            } else if ft.is_file() && name == "translation.toml" {
                out.push(path);
            }
        }
    }
    let repo_root = test_repo_root();
    let mut out = Vec::new();
    for root in roots {
        walk(&repo_root.join(root), &mut out);
    }
    out.sort();
    out
}

/// Writes a Rust crate stub (`Cargo.toml`, `Cargo.lock`, `src/lib.rs`) plus `translation.toml`
/// at `<repo_root>/<crate_rel>/` and returns the config path.
fn write_fixture_crate(repo_root: &Path, crate_rel: &str, package: &str, toml: &str) -> PathBuf {
    let crate_dir = repo_root.join(crate_rel);
    fs::create_dir_all(crate_dir.join("src")).unwrap();
    fs::write(
        crate_dir.join("Cargo.toml"),
        format!("[package]\nname = \"{package}\"\nversion = \"0.1.0\"\nedition = \"2024\"\n"),
    )
    .unwrap();
    fs::write(crate_dir.join("Cargo.lock"), "version = 4\n").unwrap();
    fs::write(crate_dir.join("src/lib.rs"), "").unwrap();
    let toml_path = crate_dir.join("translation.toml");
    fs::write(&toml_path, toml).unwrap();
    toml_path
}

/// Synthetic repository with three per-crate configs laid out like real campaigns:
///
/// - `CaseStudies/Alpha`: one crate, explicit `namespace_prefix`, crate- and target-level
///   `hashed_inputs`, `placed_only`;
/// - `CaseStudies/Beta`: one crate with a default (inferred) `namespace_prefix`;
/// - `CaseStudies/Gamma`: two crates (`widget-toy`, `widget`), `lemma_shards = 8`,
///   `placed_only`, no `namespace_prefix` (so `--out-dir GeneratedLean` infers it).
struct FixtureRepo {
    dir: tempfile::TempDir,
    alpha: PathBuf,
    beta: PathBuf,
    gamma: PathBuf,
}

impl FixtureRepo {
    fn new() -> Self {
        let dir = tempfile::tempdir().unwrap();
        let root = normalize_path(dir.path());
        let alpha = write_fixture_crate(
            &root,
            "CaseStudies/Alpha/Implementation",
            "alpha",
            r#"
crates = ["alpha"]
obj_name = "alpha"
namespace_prefix = "Examples"
hashed_inputs = ["Cargo.toml", "Cargo.lock", "src/lib.rs"]

[[targets]]
name = "alpha"
lean_file = "Generated/AlphaFns.lean"
prog_name = "alphaBin"
title = "Alpha"
hashed_inputs = ["src/alpha.rs"]
lemma_allowlist = ["alpha_encode", "alpha_decode"]

[placed]
placed_only = true
exports = ["alpha::alpha::alpha_encode", "alpha::alpha::alpha_decode"]
"#,
        );
        let beta = write_fixture_crate(
            &root,
            "CaseStudies/Beta/Implementation",
            "beta",
            r#"
crates = ["beta"]
obj_name = "beta"
hashed_inputs = ["Cargo.toml", "Cargo.lock", "src/lib.rs"]

[[targets]]
name = "beta_fns"
lean_file = "Generated/BetaFns.lean"
prog_name = "betaBin"
title = "Beta"
lemma_allowlist = ["beta_add"]
"#,
        );
        let gamma = write_fixture_crate(
            &root,
            "CaseStudies/Gamma/Implementation",
            "widget-toy",
            r#"
crates = ["widget-toy", "widget"]
obj_name = "widgetToy"
hashed_inputs = ["Cargo.toml", "Cargo.lock", "src/lib.rs"]

[[targets]]
name = "widget_toy"
lean_file = "Generated/WidgetToyFetch.lean"
prog_name = "widgetToyBin"
title = "Gamma"
lemma_shards = 8
lemma_allowlist = ["widget_toy_encode", "widget::encoding::.*"]

[placed]
placed_only = true
exports = []
"#,
        );
        Self {
            dir,
            alpha,
            beta,
            gamma,
        }
    }

    fn root(&self) -> PathBuf {
        normalize_path(self.dir.path())
    }

    fn config_paths(&self) -> Vec<PathBuf> {
        vec![self.alpha.clone(), self.beta.clone(), self.gamma.clone()]
    }
}

#[test]
fn placed_shards_resolves_sibling_shard_modules_and_requires_multi() {
    let dir = tempfile::tempdir().unwrap();
    let root = normalize_path(dir.path());
    let cfg = |shards: &str, multi: &str| {
        format!(
            "crates = [\"delta\"]\nobj_name = \"delta\"\n\n[placed]\nplaced_only = true\n{multi}{shards}exports = []\n"
        )
    };
    let path = write_fixture_crate(
        &root,
        "CaseStudies/Delta/Implementation",
        "delta",
        &cfg("placed_shards = 3\n", "multi = true\n"),
    );
    let configs = load_configs(std::slice::from_ref(&path), &root, None).unwrap();
    let p = configs[0].placed.as_ref().unwrap();
    assert_eq!(p.placed_shards, 3);
    assert!(p.lib_file.ends_with("Generated/DeltaPlacedObj.lean"));
    assert_eq!(
        p.shard_files(),
        (0..3)
            .map(|k| p.lib_file.with_file_name(format!("DeltaPlacedObjShard{k}.lean")))
            .collect::<Vec<_>>()
    );
    assert_eq!(p.shard_module(2), format!("{}Shard2", p.lib_module));
    assert!(p.lib_module.ends_with("Generated.DeltaPlacedObj"));

    // Omitted, `0` and `1` all mean a single module with no shard files.
    for shards in ["", "placed_shards = 0\n", "placed_shards = 1\n"] {
        fs::write(&path, cfg(shards, "multi = true\n")).unwrap();
        let configs = load_configs(std::slice::from_ref(&path), &root, None).unwrap();
        let p = configs[0].placed.as_ref().unwrap();
        assert_eq!(p.placed_shards, 1);
        assert!(p.shard_files().is_empty());
    }

    // Sharding applies only to the multi-block library.
    fs::write(&path, cfg("placed_shards = 2\n", "")).unwrap();
    let err = load_configs(std::slice::from_ref(&path), &root, None).unwrap_err();
    assert!(format!("{err:#}").contains("requires `multi = true`"), "{err:#}");
}

#[test]
fn extern_boundary_parses_and_requires_multi() {
    let dir = tempfile::tempdir().unwrap();
    let root = normalize_path(dir.path());
    let cfg = |multi: &str, boundary: &str| {
        format!(
            "crates = [\"delta\"]\nobj_name = \"delta\"\n\n[placed]\nplaced_only = true\n{multi}{boundary}exports = [\"alpha\"]\n"
        )
    };
    let path = write_fixture_crate(
        &root,
        "CaseStudies/Delta/Implementation",
        "delta",
        &cfg("multi = true\n", "extern_boundary = [\"beta\", \"gamma\"]\n"),
    );
    let configs = load_configs(std::slice::from_ref(&path), &root, None).unwrap();
    let p = configs[0].placed.as_ref().unwrap();
    assert_eq!(p.extern_boundary, vec!["beta".to_string(), "gamma".to_string()]);
    // Omitted: empty.
    fs::write(&path, cfg("multi = true\n", "")).unwrap();
    let configs = load_configs(std::slice::from_ref(&path), &root, None).unwrap();
    assert!(configs[0].placed.as_ref().unwrap().extern_boundary.is_empty());
    // The boundary prunes the multi-block reachability cone only.
    fs::write(&path, cfg("", "extern_boundary = [\"beta\"]\n")).unwrap();
    let err = load_configs(std::slice::from_ref(&path), &root, None).unwrap_err();
    assert!(format!("{err:#}").contains("`[placed] extern_boundary` requires `multi = true`"), "{err:#}");
}

#[test]
fn per_crate_configs_parse_and_resolve() {
    let fx = FixtureRepo::new();
    let repo_root = fx.root();

    let configs = load_configs(&fx.config_paths(), &repo_root, None)
        .expect("all per-crate translation.toml configs should parse cleanly");
    let names: Vec<&str> = configs
        .iter()
        .flat_map(|c| c.targets.iter().map(|t| t.name.as_str()))
        .collect();
    assert_eq!(names, vec!["alpha", "beta_fns", "widget_toy"]);

    let alpha = &configs[0];
    assert_eq!(alpha.crate_dir, repo_root.join("CaseStudies/Alpha/Implementation"));
    assert_eq!(alpha.crates, vec!["alpha".to_string()]);
    assert_eq!(alpha.config_rel, "CaseStudies/Alpha/Implementation/translation.toml");
    assert_eq!(
        alpha.obj_file,
        repo_root.join("CaseStudies/Alpha/Generated/AlphaObj.lean")
    );
    assert_eq!(alpha.obj_module, "CaseStudies.Alpha.Generated.AlphaObj");
    assert_eq!(alpha.namespace_prefix, "Examples");
    assert_eq!(
        alpha.code_bin_file(),
        repo_root.join("CaseStudies/Alpha/Generated/AlphaObj.code.bin")
    );
    assert_eq!(alpha.obj_def_name("alpha"), "alphaObj");
    assert_eq!(alpha.image_def_name(), "alphaImage");
    let placed = alpha.placed.as_ref().expect("alpha has [placed]");
    assert!(placed.placed_only);
    assert_eq!(
        placed.lib_file,
        repo_root.join("CaseStudies/Alpha/Generated/AlphaPlacedObj.lean")
    );
    assert_eq!(placed.lib_module, "CaseStudies.Alpha.Generated.AlphaPlacedObj");

    let beta = &configs[1];
    assert_eq!(beta.crate_dir, repo_root.join("CaseStudies/Beta/Implementation"));
    assert_eq!(beta.config_rel, "CaseStudies/Beta/Implementation/translation.toml");
    assert_eq!(beta.obj_def_name("beta"), "betaObj");
    assert_eq!(beta.namespace_prefix, "Examples");
    assert!(beta.placed.is_none());

    let gamma = &configs[2];
    assert_eq!(gamma.crate_dir, repo_root.join("CaseStudies/Gamma/Implementation"));
    assert_eq!(gamma.config_rel, "CaseStudies/Gamma/Implementation/translation.toml");
    assert_eq!(
        gamma.crates,
        vec!["widget_toy".to_string(), "widget".to_string()]
    );
    assert_eq!(gamma.object_names(), vec!["widget_toy", "widget"]);
    assert_eq!(gamma.obj_def_name("widget"), "widgetToyWidgetObj");
    assert_eq!(gamma.image_def_name(), "widgetToyImage");
    assert_eq!(
        gamma.code_bin_file(),
        repo_root.join("CaseStudies/Gamma/Generated/WidgetToyObj.code.bin")
    );
    assert_eq!(gamma.targets[0].lemma_shards, 8);
    assert_eq!(gamma.targets[0].explicit_lemma_shards, Some(8));

    let alpha_tgt = &alpha.targets[0];
    assert_eq!(
        alpha_tgt.lean_file,
        repo_root.join("CaseStudies/Alpha/Generated/AlphaFns.lean")
    );
    assert_eq!(alpha_tgt.lean_module, "CaseStudies.Alpha.Generated.AlphaFns");
    assert_eq!(
        alpha_tgt.hashed_inputs,
        vec!["Cargo.toml", "Cargo.lock", "src/lib.rs", "src/alpha.rs"]
    );
}

#[test]
fn all_in_repo_translation_configs_parse_and_resolve() {
    // Coverage check over whatever configs are present on disk (partial exports of this
    // repository drop some campaigns, so the list is discovered rather than hardcoded).
    let repo_root = test_repo_root();
    let cfg_paths =
        discover_repo_config_paths(&["CaseStudies", "VerifiedLibraries", "Arm64/Testing"]);
    for p in &cfg_paths {
        let cfg = load_config(p, &repo_root, None)
            .unwrap_or_else(|e| panic!("`{}` should parse: {e:#}", p.display()));
        if !cfg.crates.is_empty() {
            assert!(
                cfg.crate_dir.join("Cargo.toml").is_file(),
                "Rust config `{}` resolves crate_dir `{}` without a Cargo.toml",
                cfg.config_rel,
                cfg.crate_dir.display()
            );
        }
        assert!(
            !cfg.targets.is_empty() || cfg.placed.is_some(),
            "config `{}` defines neither targets nor [placed]",
            cfg.config_rel
        );
    }
}

#[test]
fn out_dir_resolves_generated_files_to_external_directory() {
    let fx = FixtureRepo::new();
    let repo_root = fx.root();
    let temp_out = tempfile::tempdir().unwrap();

    let configs = load_configs(&fx.config_paths(), &repo_root, Some(temp_out.path()))
        .expect("configs should load with custom --out-dir");
    let out = temp_out.path();
    assert_eq!(configs[0].obj_file, out.join("Generated/AlphaObj.lean"));
    assert_eq!(
        configs[0].targets[0].lean_file,
        out.join("Generated/AlphaFns.lean")
    );
    assert_eq!(configs[1].obj_file, out.join("Generated/BetaObj.lean"));
    assert_eq!(configs[2].obj_file, out.join("Generated/WidgetToyObj.lean"));
    // Crate sources still resolve against the repository, not the output directory.
    assert_eq!(
        configs[2].crate_dir,
        repo_root.join("CaseStudies/Gamma/Implementation")
    );
}

#[test]
fn out_dir_pointing_to_generated_subdir_places_file_directly_and_infers_namespace() {
    let fx = FixtureRepo::new();
    let repo_root = fx.root();
    let temp_out = tempfile::tempdir().unwrap();
    let gen_dir = temp_out.path().join("GeneratedLean");

    let cfg = load_config(&fx.gamma, &repo_root, Some(&gen_dir))
        .expect("gamma config should load with --out-dir GeneratedLean");
    assert_eq!(cfg.targets.len(), 1);
    assert_eq!(cfg.targets[0].lean_file, gen_dir.join("WidgetToyFetch.lean"));
    assert_eq!(cfg.obj_file, gen_dir.join("WidgetToyObj.lean"));
    assert_eq!(cfg.namespace_prefix, "GeneratedLean");
}

#[test]
fn lemma_shards_default_and_shard_file_naming() {
    use crate::untrusted_lemmas::code::{
        AUTO_LEMMA_SHARD_DECL_THRESHOLD, MAX_AUTO_LEMMA_SHARDS, effective_lemma_shards,
    };

    let fx = FixtureRepo::new();
    let repo_root = fx.root();
    let cfg = load_config(&fx.alpha, &repo_root, None).unwrap();
    let functions = &cfg.targets[0];
    assert_eq!(functions.lemma_shards, 1);
    assert_eq!(functions.explicit_lemma_shards, None);
    let (path, module) = functions.shard_file(2);
    assert_eq!(
        path,
        repo_root.join("CaseStudies/Alpha/Generated/AlphaFnsShard2.lean")
    );
    assert_eq!(module, "CaseStudies.Alpha.Generated.AlphaFnsShard2");

    // When `lemma_shards` is omitted in `.toml`, modules <= 2,500 declarations remain 1 file,
    // while modules > 2,500 declarations auto-shard into ceil(decls / 2500) capped at 8.
    assert_eq!(effective_lemma_shards(functions, 0), 1);
    assert_eq!(
        effective_lemma_shards(functions, AUTO_LEMMA_SHARD_DECL_THRESHOLD),
        1
    );
    assert_eq!(
        effective_lemma_shards(functions, AUTO_LEMMA_SHARD_DECL_THRESHOLD + 1),
        2
    );
    assert_eq!(effective_lemma_shards(functions, 7_563), 4);
    assert_eq!(
        effective_lemma_shards(functions, 25_000),
        MAX_AUTO_LEMMA_SHARDS
    );

    // Explicit `lemma_shards = 1` in `.toml` opts out of auto-sharding.
    let mut explicit_one = functions.clone();
    explicit_one.explicit_lemma_shards = Some(1);
    assert_eq!(effective_lemma_shards(&explicit_one, 10_000), 1);

    // Explicit `lemma_shards = 4` overrides auto-sharding regardless of declaration count.
    let mut explicit_four = functions.clone();
    explicit_four.lemma_shards = 4;
    explicit_four.explicit_lemma_shards = Some(4);
    assert_eq!(effective_lemma_shards(&explicit_four, 500), 4);
}

#[test]
fn output_flag_and_namespace_overrides_work() {
    let fx = FixtureRepo::new();
    let repo_root = fx.root();
    let mut cfg = load_config(&fx.alpha, &repo_root, None).unwrap();
    cfg.targets.push(cfg.targets[0].clone());
    assert_eq!(cfg.targets.len(), 2);

    let custom_out = PathBuf::from("/tmp/custom/CustomOutput.lean");
    let mut multi = vec![cfg.clone()];
    let err = apply_overrides(&mut multi, Some(&custom_out), None, None)
        .expect_err("--output with several targets must fail");
    assert!(err.to_string().contains("single target"));

    let mut single = vec![cfg];
    single[0].targets.truncate(1);
    apply_overrides(
        &mut single,
        Some(&custom_out),
        Some("RootProject"),
        Some("Functions"),
    )
    .expect("--output on a single target should succeed");
    assert_eq!(single[0].targets[0].lean_file, custom_out);
    assert_eq!(
        single[0].obj_file,
        PathBuf::from("/tmp/custom/AlphaObj.lean")
    );
    assert_eq!(single[0].namespace_prefix, "RootProject");
    assert_eq!(
        single[0].targets[0].sub_namespace.as_deref(),
        Some("Functions")
    );
    assert_eq!(
        single[0].target_namespace(&single[0].targets[0]),
        "RootProject.Functions"
    );
}

#[test]
fn select_configs_filters_by_target_name() {
    let fx = FixtureRepo::new();
    let configs = load_configs(&fx.config_paths(), &fx.root(), None).unwrap();
    let selected = select_configs(configs.clone(), &["beta_fns".to_string()]).unwrap();
    assert_eq!(selected.len(), 1);
    assert_eq!(selected[0].obj_name, configs[1].obj_name);
    let selected = select_configs(
        configs.clone(),
        &["alpha".to_string(), "widget_toy".to_string()],
    )
    .unwrap();
    assert_eq!(
        selected.iter().map(|c| c.obj_name.as_str()).collect::<Vec<_>>(),
        vec!["alpha", "widgetToy"]
    );
    let err = select_configs(configs, &["nope".to_string()]).unwrap_err();
    assert!(err.to_string().contains("unknown target `nope`"));
}

fn write_tmp_crate(name: &str, toml: &str) -> (tempfile::TempDir, PathBuf) {
    let tmp_crate = tempfile::tempdir().unwrap();
    fs::write(
        tmp_crate.path().join("Cargo.toml"),
        format!("[package]\nname = \"{name}\"\nversion = \"0.1.0\"\nedition = \"2024\"\n"),
    )
    .unwrap();
    let toml_path = tmp_crate.path().join("translation.toml");
    fs::write(&toml_path, toml).unwrap();
    (tmp_crate, toml_path)
}

#[test]
fn self_contained_crate_config_defaults_crate_dir_and_infers_package_name() {
    let tmp_out = tempfile::tempdir().unwrap();
    let (tmp_crate, toml_path) = write_tmp_crate(
        "external-crypto-crate",
        r#"
obj_name = "extCrypto"

[[targets]]
name = "ext-target"
lean_file = "Generated/ExtCrypto.lean"
prog_name = "extCryptoBin"
title = "External Crypto Crate"
lemma_allowlist = ["ext_encrypt"]
"#,
    );
    let cfg = load_config(&toml_path, &test_repo_root(), Some(tmp_out.path()))
        .expect("self-contained translation.toml should parse and infer package name");
    assert_eq!(cfg.crate_dir, normalize_path(tmp_crate.path()));
    assert_eq!(cfg.crates, vec!["external_crypto_crate".to_string()]);
    assert_eq!(cfg.title, "External Crypto Crate");
    assert_eq!(
        cfg.targets[0].lean_file,
        normalize_path(&tmp_out.path().join("Generated/ExtCrypto.lean"))
    );
    assert_eq!(
        cfg.obj_file,
        normalize_path(&tmp_out.path().join("Generated/ExtCryptoObj.lean"))
    );
    assert_eq!(
        cfg.data_bin_file(),
        normalize_path(&tmp_out.path().join("Generated/ExtCryptoObj.data.bin"))
    );
}

#[test]
fn multi_crate_config_names_each_object() {
    let (_tmp, toml_path) = write_tmp_crate(
        "multi-crate-demo",
        r#"
crates = ["multi-crate-demo", "helper_crate"]
obj_name = "demo"

[[targets]]
name = "demo"
lean_file = "Generated/Demo.lean"
prog_name = "demoBin"
title = "Demo"
lemma_allowlist = ["demo_entry"]
"#,
    );
    let cfg = load_config(&toml_path, &test_repo_root(), None).unwrap();
    assert_eq!(
        cfg.crates,
        vec!["multi_crate_demo".to_string(), "helper_crate".to_string()]
    );
    assert_eq!(cfg.obj_def_name("helper_crate"), "demoHelperCrateObj");
    assert_eq!(cfg.image_def_name(), "demoImage");
}

#[test]
fn rejects_removed_config_fields() {
    for removed in [
        "symbol_allowlist = [\"x\"]",
        "stub_crates = [\"aes-gcm\"]",
        "stub_external_symbols = true",
        "link_workspace_crates = true",
        "link_crates = [\"helper\"]",
        "emit_obj_dump = true",
        "base_addr = \"0x0\"",
        "rodata_addr = \"0x0\"",
        "words_def = true",
        "target_crate = \"x\"",
    ] {
        let (_tmp, toml_path) = write_tmp_crate(
            "old-crate",
            &format!(
                r#"
obj_name = "old"

[[targets]]
name = "old"
lean_file = "Generated/Old.lean"
prog_name = "oldBin"
title = "Old"
lemma_allowlist = ["f"]
{removed}
"#
            ),
        );
        let err = load_config(&toml_path, &test_repo_root(), None)
            .expect_err("removed field must be rejected");
        assert!(
            format!("{err:#}").contains("unknown field"),
            "{removed}: {err:#}"
        );
    }
}

#[test]
fn rejects_bad_obj_name_and_duplicate_crates() {
    let (_tmp, bad_name) = write_tmp_crate(
        "c",
        r#"
obj_name = "1bad-name"
[[targets]]
name = "t"
lean_file = "G/T.lean"
prog_name = "p"
title = "T"
lemma_allowlist = []
"#,
    );
    let err = load_config(&bad_name, &test_repo_root(), None).unwrap_err();
    assert!(err.to_string().contains("not a simple Lean identifier"));

    let (_tmp2, dup) = write_tmp_crate(
        "c",
        r#"
obj_name = "ok"
crates = ["a-b", "a_b"]
[[targets]]
name = "t"
lean_file = "G/T.lean"
prog_name = "p"
title = "T"
lemma_allowlist = []
"#,
    );
    let err = load_config(&dup, &test_repo_root(), None).unwrap_err();
    assert!(err.to_string().contains("duplicate crate `a_b`"));
}

#[test]
fn rustflags_config() {
    const TARGET: &str = r#"
[[targets]]
name = "t"
lean_file = "G/T.lean"
prog_name = "p"
title = "T"
lemma_allowlist = []
"#;
    let cfg_with = |flags: &str| format!("obj_name = \"ok\"\nrustflags = {flags}\n{TARGET}");
    let (_t, ok) = write_tmp_crate("c", &cfg_with(r#"["--cfg", 'k="v"']"#));
    let cfg = load_config(&ok, &test_repo_root(), None).unwrap();
    assert_eq!(cfg.rustflags, ["--cfg", "k=\"v\""]);
    let (_t, none) = write_tmp_crate("c", &format!("obj_name = \"ok\"\n{TARGET}"));
    assert!(
        load_config(&none, &test_repo_root(), None)
            .unwrap()
            .rustflags
            .is_empty()
    );

    for (what, flags) in [
        ("flag with space", r#"["-C opt-level=3"]"#),
        ("empty flag", r#"[""]"#),
    ] {
        let (_t, path) = write_tmp_crate("c", &cfg_with(flags));
        let err = load_config(&path, &test_repo_root(), None).unwrap_err();
        assert!(
            format!("{err:#}").contains("without whitespace"),
            "{what}: {err:#}"
        );
    }
}

#[test]
fn reproducible_paths() {
    use crate::untrusted_driver::{
        check_no_host_paths, host_path_check_dirs, path_remaps, rustc_commit_hash,
    };
    let ver = "rustc 1.98.1 (48a229cea 2026-09-21)\nbinary: rustc\n\
                   commit-hash: 48a229ceaefd4985c50990b14116b6d856af0985\ncommit-date: 2026-09-21";
    let commit = rustc_commit_hash(ver).unwrap();
    assert_eq!(commit, "48a229ceaefd4985c50990b14116b6d856af0985");
    assert!(rustc_commit_hash("rustc 1.98.1\ncommit-hash: unknown\n").is_err());
    assert!(rustc_commit_hash("rustc 1.98.1\n").is_err());
    assert!(rustc_commit_hash("commit-hash: bad=hash\n").is_err());

    // A symlinked CARGO_HOME, target dir and sysroot: both spellings are remapped, each as given
    // then canonicalized, in a fixed order of kinds (not by length, which differs between hosts).
    let tmp = tempfile::tempdir().unwrap();
    let root = tmp.path().canonicalize().unwrap();
    let real_home = root.join("real-cargo-home");
    // Leave `git/checkouts` and `lib/rustlib/src/rust` non-existent on disk to verify
    // canonicalization via existing ancestor (e.g. when `rust-src` is not installed).
    fs::create_dir_all(real_home.join("registry/src")).unwrap();
    let home = root.join("h");
    std::os::unix::fs::symlink(&real_home, &home).unwrap();
    let real_target = root.join("checkout-with-a-long-name/target");
    fs::create_dir_all(&real_target).unwrap();
    let target = root.join("t");
    std::os::unix::fs::symlink(&real_target, &target).unwrap();
    let real_sysroot = root.join("toolchains/1.98.1-x86_64-unknown-linux-gnu");
    fs::create_dir_all(real_sysroot.join("lib/rustlib")).unwrap();
    let sysroot = root.join("s");
    std::os::unix::fs::symlink(&real_sysroot, &sysroot).unwrap();
    let s = |p: &Path| p.to_str().unwrap().to_string();
    let remaps = path_remaps(&target, &home, &sysroot, commit, None).unwrap();
    let link_reg = s(&home.join("registry/src"));
    let real_reg = s(&real_home.join("registry/src"));
    let link_git = s(&home.join("git/checkouts"));
    let real_git = s(&real_home.join("git/checkouts"));
    let link_src = s(&sysroot.join("lib/rustlib/src/rust"));
    let real_src = s(&real_sysroot.join("lib/rustlib/src/rust"));
    let rustc_to = format!("/rustc/{commit}");
    let flag = |d: &str, to: &str| (d.to_string(), format!("--remap-path-prefix={d}={to}"));
    assert_eq!(
        remaps,
        [
            flag(&link_reg, "/cargo-registry"),
            flag(&real_reg, "/cargo-registry"),
            flag(&s(&target), "/cargo-target"),
            flag(&s(&real_target), "/cargo-target"),
            flag(&link_git, "/cargo-git"),
            flag(&real_git, "/cargo-git"),
            flag(&link_src, &rustc_to),
            flag(&real_src, &rustc_to),
        ]
    );
    // The order does not depend on the directories' lengths: the same kinds at other lengths.
    let other = root.join("another-much-longer-host-directory-name");
    let (o_home, o_target, o_sysroot) = (other.join("h"), root.join("t2"), other.join("s"));
    let kinds = |r: &[(String, String)]| -> Vec<String> {
        r.iter()
            .map(|(_, f)| f.rsplit_once('=').unwrap().1.to_string())
            .collect()
    };
    assert_eq!(
        kinds(&path_remaps(&o_target, &o_home, &o_sysroot, commit, None).unwrap()),
        [
            "/cargo-registry",
            "/cargo-target",
            "/cargo-git",
            rustc_to.as_str()
        ]
    );
    // Without symlinks, one spelling each.
    assert_eq!(
        path_remaps(&real_target, &real_home, &real_sysroot, commit, None)
            .unwrap()
            .len(),
        4
    );
    assert!(
        path_remaps(
            Path::new("/has space/target"),
            &home,
            &sysroot,
            commit,
            None
        )
        .is_err()
    );
    assert!(
        path_remaps(
            &target,
            Path::new("/has space/.cargo"),
            &sysroot,
            commit,
            None
        )
        .is_err()
    );
    assert!(
        path_remaps(
            &target,
            &home,
            Path::new("/has space/sysroot"),
            commit,
            None
        )
        .is_err()
    );
    assert!(path_remaps(Path::new("/has=eq/target"), &home, &sysroot, commit, None).is_err());
    assert!(path_remaps(&target, Path::new("/has=eq/.cargo"), &sysroot, commit, None).is_err());
    assert!(path_remaps(&target, &home, Path::new("/has=eq/sysroot"), commit, None).is_err());
    assert!(path_remaps(&target, &home, &sysroot, "", None).is_err());
    assert!(path_remaps(&target, &home, &sysroot, "bad=commit", None).is_err());

    // Nested directories: the longer (more specific) prefix comes last, so rustc applies it.
    let nested = path_remaps(
        &real_home.join("git"),
        &real_home,
        &real_sysroot,
        commit,
        None,
    )
    .unwrap();
    assert!(
        nested
            .iter()
            .position(|x| x == &flag(&s(&real_home.join("git")), "/cargo-target"))
            < nested
                .iter()
                .position(|x| x == &flag(&real_git, "/cargo-git"))
    );

    // The check covers the remapped dirs (including <sysroot>/lib/rustlib/src/rust), the
    // sysroot itself, the crate dir and the upstream source.
    let crate_dir = root.join("checkout-with-a-long-name");
    let upstream = root.join("upstream-src");
    fs::create_dir_all(&upstream).unwrap();
    let check = host_path_check_dirs(&remaps, &sysroot, &crate_dir, Some(&upstream));
    assert!(
        check.contains(&s(&sysroot))
            && check.contains(&s(&real_sysroot))
            && check.contains(&link_src)
            && check.contains(&real_src)
            && check.contains(&s(&crate_dir))
            && check.contains(&s(&upstream))
    );
    for leaked in [
        format!("xx{real_reg}/index.crates.io-x/hkdf-0.13.0/src/hmac_impl.rs\0"),
        format!("xx{}/out/signal.proto.wire.rs\0", s(&real_target)),
        format!("xx{real_git}/spqr-b58d/06959b4/src/lib.rs\0"),
        format!("xx{real_src}/library/core/src/slice/index.rs\0"),
        format!(
            "xx{}/lib/rustlib/aarch64-unknown-linux-gnu/lib/libcore.rlib\0",
            s(&real_sysroot)
        ),
        format!("xx{}/vendor/x/src/lib.rs\0", s(&crate_dir)),
        format!("xx{}/rust/protocol/src/lib.rs\0", s(&upstream)),
    ] {
        assert!(
            check_no_host_paths("o", leaked.as_bytes(), &check).is_err(),
            "{leaked}"
        );
    }
    let clean = format!(
        "xx/cargo-registry/index.crates.io-x/hkdf-0.13.0/src/hmac_impl.rs\0\
             /cargo-target/out/a.rs\0/cargo-git/spqr/src/lib.rs\0\
             {rustc_to}/library/core/src/slice/index.rs\0vendor/x/src/lib.rs\0"
    );
    assert!(check_no_host_paths("o", clean.as_bytes(), &check).is_ok());
    // Relative sysroot/crate dirs are only checked in their canonical (absolute) spelling.
    let rel = host_path_check_dirs(&[], Path::new("."), Path::new("."), None);
    assert_eq!(rel, [s(&Path::new(".").canonicalize().unwrap())]);
}

#[test]
fn upstream_source_remap() {
    use crate::untrusted_driver::{path_remaps, upstream_remap_target};
    let commit = "48a229ceaefd4985c50990b14116b6d856af0985";
    let up_a = "ba133bd3457f556fbf56db0a5ab985de0af79da6";
    let up_b = "0123456789abcdef0123456789abcdef01234567";
    let to_a = upstream_remap_target("widget", up_a).unwrap();
    let to_b = upstream_remap_target("widget", up_b).unwrap();
    assert_eq!(to_a, format!("/upstream/widget/{up_a}"));
    for (name, c) in [
        ("", up_a),
        ("a b", up_a),
        ("a=b", up_a),
        ("a/b", up_a),
        ("widget", ""),
        ("widget", "HEAD"),
        ("widget", "ab=cd"),
    ] {
        assert!(upstream_remap_target(name, c).is_err(), "`{name}` `{c}`");
    }

    // A crate whose `vendor/widget` symlink points to one of two upstream trees.
    let tmp = tempfile::tempdir().unwrap();
    let root = tmp.path().canonicalize().unwrap();
    let home = root.join("cargo-home");
    let target = root.join("crate/target");
    let sysroot = root.join("sysroot");
    let tree_a = root.join("trees/widget-a");
    let tree_b = root.join("trees/widget-b");
    fs::create_dir_all(&tree_a).unwrap();
    fs::create_dir_all(&tree_b).unwrap();
    fs::create_dir_all(root.join("crate/vendor")).unwrap();
    let link = root.join("crate/vendor/widget");
    std::os::unix::fs::symlink(&tree_a, &link).unwrap();
    let flags = |up: Option<(&Path, &str)>| -> Vec<String> {
        path_remaps(&target, &home, &sysroot, commit, up)
            .unwrap()
            .into_iter()
            .map(|(_, f)| f)
            .collect()
    };
    let flag = |d: &Path, to: &str| format!("--remap-path-prefix={}={to}", d.to_str().unwrap());

    // Both spellings of the upstream directory are added to the fixed remaps.
    let base = flags(None);
    let with_a = flags(Some((&link, &to_a)));
    assert_eq!(with_a.len(), base.len() + 2, "{with_a:?}");
    assert!(base.iter().all(|f| with_a.contains(f)));
    assert!(with_a.contains(&flag(&link, &to_a)), "{with_a:?}");
    assert!(with_a.contains(&flag(&tree_a, &to_a)), "{with_a:?}");

    // Retargeting the symlink, or another upstream commit in the same directory, changes
    // RUSTFLAGS, so cargo rebuilds every unit instead of trusting source mtimes.
    fs::remove_file(&link).unwrap();
    std::os::unix::fs::symlink(&tree_b, &link).unwrap();
    let retargeted = flags(Some((&link, &to_a)));
    assert_ne!(retargeted, with_a);
    assert!(retargeted.contains(&flag(&tree_b, &to_a)), "{retargeted:?}");
    assert_ne!(flags(Some((&link, &to_b))), retargeted);

    // An upstream checkout nested in a remapped directory: its own (longer) prefix comes last,
    // so rustc applies it.
    let nested = home.join("git/checkouts/widget-1234");
    fs::create_dir_all(&nested).unwrap();
    let nested_flags = flags(Some((&nested, &to_a)));
    let pos = |f: &str| nested_flags.iter().position(|x| x == f).unwrap();
    assert!(pos(&flag(&home.join("git/checkouts"), "/cargo-git")) < pos(&flag(&nested, &to_a)));

    // A relative spelling is not remapped: it could match the relative source paths of path
    // packages below the workspace root. Unusable paths are rejected.
    let rel = path_remaps(
        &target,
        &home,
        &sysroot,
        commit,
        Some((Path::new("no-such-dir/widget"), &to_a)),
    )
    .unwrap();
    assert!(
        rel.iter().all(|(d, _)| Path::new(d).is_absolute()),
        "{rel:?}"
    );
    assert_eq!(rel.len(), base.len());
    for bad in ["/has space/widget", "/has=eq/widget"] {
        assert!(
            path_remaps(
                &target,
                &home,
                &sysroot,
                commit,
                Some((Path::new(bad), &to_a))
            )
            .is_err(),
            "{bad}"
        );
    }

    // A target dir inside the upstream checkout, or the other way round: the nested directory
    // comes last whichever is longer, and unrelated directories keep their fixed order.
    let up = root.join("up");
    let kinds = |r: Vec<(String, String)>| -> Vec<String> {
        r.into_iter()
            .map(|(_, f)| f.rsplit_once('=').unwrap().1.to_string())
            .collect()
    };
    let rustc_to = format!("/rustc/{commit}");
    assert_eq!(
        kinds(
            path_remaps(
                &up.join("target"),
                &home,
                &sysroot,
                commit,
                Some((&up, &to_a))
            )
            .unwrap()
        ),
        [
            "/cargo-registry",
            "/cargo-git",
            rustc_to.as_str(),
            to_a.as_str(),
            "/cargo-target"
        ]
    );
    let t = root.join("t");
    assert_eq!(
        kinds(path_remaps(&t, &home, &sysroot, commit, Some((&t.join("up"), &to_a))).unwrap()),
        [
            "/cargo-registry",
            "/cargo-target",
            "/cargo-git",
            rustc_to.as_str(),
            to_a.as_str()
        ]
    );
}

#[test]
fn host_independent_provenance_paths() {
    use crate::untrusted_driver::{Toolchain, checkout_root, crate_dir_display};
    // Commands show the longest aliased host path first, whatever order the aliases were added
    // in: an upstream checkout below the crate's repository shows as its own alias.
    let argv = [
        "--remap-path-prefix=/w/super/c/vendor/up=/upstream/up/0123",
        "--remap-path-prefix=/w/super/c/target=/cargo-target",
    ];
    let expected = "--remap-path-prefix=$UP_SRC=/upstream/up/0123 \
                    --remap-path-prefix=$CRATE_REPO/c/target=/cargo-target";
    for aliases in [
        [
            ("/w/super", "$CRATE_REPO"),
            ("/w/super/c/vendor/up", "$UP_SRC"),
        ],
        [
            ("/w/super/c/vendor/up", "$UP_SRC"),
            ("/w/super", "$CRATE_REPO"),
        ],
    ] {
        let mut tc = Toolchain {
            repo_root: PathBuf::from("/w/super/engine"),
            rustc_version: String::new(),
            path_aliases: vec![],
        };
        for (real, alias) in aliases {
            tc.add_alias(Path::new(real), alias);
        }
        assert_eq!(tc.format_cmd(&argv, &[]), expected);
    }

    // The crate directory is shown relative to this repository, else to its own checkout.
    let tmp = tempfile::tempdir().unwrap();
    let sup = tmp.path().canonicalize().unwrap().join("super");
    let engine = sup.join("engine");
    fs::create_dir_all(sup.join(".git")).unwrap();
    fs::create_dir_all(engine.join("examples/demo")).unwrap();
    fs::write(engine.join(".git"), "gitdir: ../.git/modules/engine\n").unwrap();
    let outside = sup.join("third_party/lib/lib-session");
    fs::create_dir_all(&outside).unwrap();
    assert_eq!(checkout_root(&outside), Some(sup.as_path()));
    assert_eq!(
        checkout_root(&engine.join("examples/demo")),
        Some(engine.as_path())
    );
    assert_eq!(
        crate_dir_display(&engine, &engine.join("examples/demo")),
        "examples/demo"
    );
    assert_eq!(
        crate_dir_display(&engine, &outside),
        "third_party/lib/lib-session"
    );
    assert_eq!(crate_dir_display(&engine, &sup), ".");
    let no_git = tmp.path().canonicalize().unwrap().join("plain/crate");
    fs::create_dir_all(&no_git).unwrap();
    if checkout_root(&no_git).is_none() {
        assert_eq!(
            crate_dir_display(&engine, &no_git),
            no_git.to_str().unwrap()
        );
    }
}

#[test]
fn native_objects_config() {
    const TARGET: &str = r#"
[[targets]]
name = "t"
lean_file = "G/T.lean"
prog_name = "p"
title = "T"
lemma_allowlist = []
"#;
    let native = |compiler: &str, obj: &str| {
        format!("obj_name = \"ok\"\n{compiler}\n[[native_objects]]\n{obj}\n{TARGET}")
    };
    let good_obj = r#"name = "shim"
source = "csrc/shim.c"
include_dirs = ["csrc/include"]
defines = ["FOO", "BAR=1"]"#;
    let compiler = "[native_compiler]\nzig_version = \"0.16.0\"";
    let c_dir = tempfile::tempdir().unwrap();
    let ok = c_dir.path().join("translation.toml");
    fs::write(&ok, native(compiler, good_obj)).unwrap();
    let cfg = load_config(&ok, &test_repo_root(), None).unwrap();
    assert!(cfg.crates.is_empty());
    assert_eq!(cfg.object_names(), ["shim"]);
    assert_eq!(cfg.native_compiler.as_ref().unwrap().zig_version, "0.16.0");
    let args =
        crate::untrusted_driver::native_cc_args_with_flags(&cfg.native_objects[0], &[], "shim.o");
    assert_eq!(args[0], "cc");
    assert!(
        args.windows(2)
            .any(|w| w == ["-target", "aarch64-linux-musl"])
    );
    assert!(args.contains(&"-fno-pic".to_string()));
    assert_eq!(
        args[args.len() - 7..],
        [
            "-Icsrc/include",
            "-DFOO",
            "-DBAR=1",
            "-c",
            "csrc/shim.c",
            "-o",
            "shim.o"
        ]
    );

    let cases: &[(&str, String, &str)] = &[
        (
            "missing compiler",
            native("", good_obj),
            "[native_compiler]",
        ),
        (
            "compiler without objects",
            format!("obj_name = \"ok\"\n{compiler}\n{TARGET}"),
            "[native_compiler]",
        ),
        (
            "bad name",
            native(compiler, &good_obj.replace("\"shim\"", "\"a-b\"")),
            "not a C identifier",
        ),
        (
            "roots rejected",
            native(compiler, &format!("{good_obj}\nroots = [\"f\"]")),
            "unknown field `roots`",
        ),
        (
            "absolute source",
            native(
                compiler,
                &good_obj.replace("\"csrc/shim.c\"", "\"/etc/shim.c\""),
            ),
            "must be non-empty and relative",
        ),
        (
            "empty source",
            native(compiler, &good_obj.replace("\"csrc/shim.c\"", "\"\"")),
            "must be non-empty and relative",
        ),
        (
            "bad define",
            native(compiler, &good_obj.replace("\"FOO\"", "\"-O0\"")),
            "bad define",
        ),
        (
            "digit-leading define",
            native(compiler, &good_obj.replace("\"FOO\"", "\"0FOO=1\"")),
            "bad define",
        ),
        (
            "whitespace in define value",
            native(compiler, &good_obj.replace("\"BAR=1\"", "\"BAR=1 2\"")),
            "bad define",
        ),
        (
            "duplicate native object name",
            format!(
                "obj_name = \"ok\"\n{compiler}\n[[native_objects]]\n{good_obj}\n[[native_objects]]\n{good_obj}\n{TARGET}"
            ),
            "duplicate object name `shim`",
        ),
        (
            "empty crates in mixed Rust+C config",
            format!("crates = []\n{}", native(compiler, good_obj)),
            "defines no crates",
        ),
        (
            "empty crates in pure-Rust config",
            format!("crates = []\nobj_name = \"ok\"\n{TARGET}"),
            "defines no crates",
        ),
        (
            "bad sysroot object name",
            format!(
                "crates = [\"c\"]\nobj_name = \"ok\"\n[[sysroot_objects]]\ncrate = \"core\"\nname = \"bad-name\"\nroots = [\"f\"]\n{TARGET}"
            ),
            "not a C identifier",
        ),
        (
            "duplicate sysroot object names",
            format!(
                "crates = [\"c\"]\nobj_name = \"ok\"\n[[sysroot_objects]]\ncrate = \"core\"\nname = \"dup_s\"\nroots = [\"f\"]\n[[sysroot_objects]]\ncrate = \"alloc\"\nname = \"dup_s\"\nroots = [\"g\"]\n{TARGET}"
            ),
            "duplicate object name `dup_s`",
        ),
    ];
    for (what, toml, expect) in cases {
        let dir = tempfile::tempdir().unwrap();
        let path = dir.path().join("translation.toml");
        fs::write(&path, toml).unwrap();
        let err = load_config(&path, &test_repo_root(), None).expect_err(what);
        assert!(format!("{err:#}").contains(expect), "{what}: {err:#}");
    }

    // Reject `[[native_objects]]` in a directory that contains a `Cargo.toml` unless `crates = [...]` is explicit.
    let (_t, mixed_cargo) = write_tmp_crate("c", &native(compiler, good_obj));
    let err = load_config(&mixed_cargo, &test_repo_root(), None).unwrap_err();
    assert!(
        format!("{err:#}").contains("cannot combine Rust crates"),
        "{err:#}"
    );

    // Explicit `crates = [...]` may be combined with C inputs and multi-entry `[[sysroot_objects]]`,
    // ordered `crates` -> C inputs -> `sysroot_objects`.
    let (_t2, explicit_mixed) = write_tmp_crate(
        "c",
        &format!(
            "crates = [\"c\"]\n{}\n[[sysroot_objects]]\ncrate = \"compiler_builtins\"\nname = \"cb_a\"\nroots = [\"__aarch64_cas4_acq\"]\n[[sysroot_objects]]\ncrate = \"compiler_builtins\"\nname = \"cb_b\"\nroots = [\"__aarch64_have_lse_atomics\"]\n",
            native(compiler, good_obj)
        ),
    );
    let mixed_cfg = load_config(&explicit_mixed, &test_repo_root(), None).unwrap();
    assert_eq!(mixed_cfg.crates, ["c"]);
    assert_eq!(mixed_cfg.object_names(), ["c", "shim", "cb_a", "cb_b"]);
}

#[test]
fn cli_accepts_multiple_configs_and_out_dir() {
    let cli = Cli::try_parse_from([
        "rust-obj2lean",
        "--config",
        "Implementation/examples/translation.toml",
        "--config",
        "Implementation/my_lib/translation.toml",
        "--out-dir",
        "/tmp/out",
        "--only",
        "functions",
        "--check",
    ])
    .expect("CLI flags should parse");
    assert_eq!(cli.config.len(), 2);
    assert_eq!(cli.out_dir, Some(PathBuf::from("/tmp/out")));
    assert_eq!(cli.only, vec!["functions".to_string()]);
    assert!(cli.check);
}

#[test]
fn write_or_check_reports_changes() {
    let tmp = tempfile::tempdir().unwrap();
    let file = GeneratedFile {
        path: tmp.path().join("sub/A.lean"),
        contents: b"hello\n".to_vec(),
        text: true,
    };
    assert!(!write_or_check(&file, tmp.path(), true).unwrap());
    assert!(write_or_check(&file, tmp.path(), false).unwrap());
    assert_eq!(fs::read(&file.path).unwrap(), b"hello\n");
    assert!(write_or_check(&file, tmp.path(), true).unwrap());
}

#[test]
fn write_or_check_unlinks_hardlink_instead_of_truncating_shared_inode() {
    use std::os::unix::fs::MetadataExt;

    let tmp = tempfile::tempdir().unwrap();
    let main_dir = tmp.path().join("main");
    let wt_dir = tmp.path().join("worktree");
    fs::create_dir_all(&main_dir).unwrap();
    fs::create_dir_all(&wt_dir).unwrap();

    let main_file = main_dir.join("AlphaFns.lean");
    let wt_file = wt_dir.join("AlphaFns.lean");
    fs::write(&main_file, b"original-v1\n").unwrap();
    fs::hard_link(&main_file, &wt_file).unwrap();
    assert_eq!(
        fs::metadata(&main_file).unwrap().ino(),
        fs::metadata(&wt_file).unwrap().ino()
    );
    assert_eq!(fs::metadata(&main_file).unwrap().nlink(), 2);

    let updated = GeneratedFile {
        path: wt_file.clone(),
        contents: b"updated-v2-in-worktree\n".to_vec(),
        text: true,
    };
    assert!(write_or_check(&updated, &wt_dir, false).unwrap());

    assert_eq!(fs::read(&wt_file).unwrap(), b"updated-v2-in-worktree\n");
    assert_eq!(fs::read(&main_file).unwrap(), b"original-v1\n");
    assert_ne!(
        fs::metadata(&main_file).unwrap().ino(),
        fs::metadata(&wt_file).unwrap().ino()
    );
    assert_eq!(fs::metadata(&main_file).unwrap().nlink(), 1);
    assert_eq!(fs::metadata(&wt_file).unwrap().nlink(), 1);
    for entry in fs::read_dir(&wt_dir).unwrap() {
        let name = entry.unwrap().file_name().into_string().unwrap();
        assert!(!name.contains(".tmp."), "stray temp file left behind: {name}");
    }
}

#[test]
fn lakefile_ensure_rust_exports_atomic_stamps_and_imported_outputs() {
    let repo_root = test_repo_root();
    let mut combined_lakefiles = fs::read_to_string(repo_root.join("lakefile.lean")).unwrap();
    let lake_exports_path = repo_root.join("scripts/LakeExports.lean");
    if lake_exports_path.is_file() {
        combined_lakefiles.push('\n');
        combined_lakefiles.push_str(&fs::read_to_string(&lake_exports_path).unwrap());
    }
    let vl_lf = repo_root.join("VerifiedLibraries/lakefile.lean");
    if vl_lf.is_file() {
        combined_lakefiles.push('\n');
        combined_lakefiles.push_str(&fs::read_to_string(&vl_lf).unwrap());
    }
    let cs_root = repo_root.join("CaseStudies");
    if let Ok(entries) = fs::read_dir(&cs_root) {
        for entry in entries.flatten() {
            let lf = entry.path().join("lakefile.lean");
            if lf.is_file() {
                combined_lakefiles.push('\n');
                combined_lakefiles.push_str(&fs::read_to_string(&lf).unwrap());
            }
        }
    }

    // 1. `writeFileAtomic` writes to a temp file and renames it over the target.
    let (_, after_atomic) = combined_lakefiles
        .split_once("def writeFileAtomic")
        .expect("lakefile.lean / scripts/LakeExports.lean must define writeFileAtomic");
    let (atomic_body, _) = after_atomic
        .split_once("def generatedImportsOfFile")
        .expect("lakefile.lean / scripts/LakeExports.lean must define generatedImportsOfFile after writeFileAtomic");
    assert!(
        atomic_body.contains(".tmp.") && atomic_body.contains("IO.FS.rename"),
        "writeFileAtomic must write to a .tmp. file and rename over target"
    );

    // 2. `ensureRustExports` never uses raw `IO.FS.writeFile` (which truncates hardlinked stamps
    //    in place) and checks `generatedImportsOfFile` so missing `*Shard*.lean` imports fail closed.
    let (_, after_ensure) = combined_lakefiles
        .split_once("def ensureRustExports")
        .expect("lakefile.lean / scripts/LakeExports.lean must define ensureRustExports");
    let (ensure_body, _) = after_ensure
        .split_once("partial def sanitizePackageBuildDir")
        .expect("sanitizePackageBuildDir must follow ensureRustExports");
    assert!(
        !ensure_body.contains("IO.FS.writeFile"),
        "ensureRustExports must use writeFileAtomic instead of IO.FS.writeFile"
    );
    assert!(
        ensure_body.contains("writeFileAtomic (buildDir /")
            && ensure_body.contains("writeFileAtomic (genDir /")
            && ensure_body.contains("writeFileAtomic buildStamp")
            && ensure_body.contains("writeFileAtomic genStamp")
            && ensure_body.contains("writeFileAtomic genInputsStamp"),
        "ensureRustExports must write all buildDir and genDir stamps via writeFileAtomic"
    );
    assert!(
        ensure_body.matches("generatedImportsOfFile").count() >= 3,
        "ensureRustExports must check generatedImportsOfFile in allExist, error cleanup, and post-export verification"
    );

    // 3. Every configured target's `lean_file` (or `placed.lib_file` when `placed_only = true`)
    //    is covered in `exportTargetSpecs` (directly or via `shardOutputs`). Configs are
    //    discovered on disk so partial exports that drop campaigns still check what remains.
    let configs = load_configs(
        &discover_repo_config_paths(&["CaseStudies"]),
        &repo_root,
        None,
    )
    .unwrap();
    for cfg in &configs {
        if let Some(placed) = &cfg.placed
            && placed.placed_only
        {
            let rel = placed
                .lib_file
                .strip_prefix(&repo_root)
                .unwrap_or(&placed.lib_file)
                .to_string_lossy();
            let rel_norm = if let Some(rest) = rel.strip_prefix("CaseStudies/")
                && let Some((_lib, after_lib)) = rest.split_once('/')
            {
                after_lib.to_string()
            } else {
                rel.to_string()
            };
            if placed.placed_shards > 1 {
                // Sharded placed library: the barrel and every shard via `shardOutputs`.
                let stem = rel_norm.strip_suffix(".lean").unwrap_or(&rel_norm);
                assert!(
                    combined_lakefiles
                        .contains(&format!("shardOutputs \"{stem}\" {}", placed.placed_shards)),
                    "placed_only config `{}` with `placed_shards = {}` needs \
                     `shardOutputs \"{stem}\" {}` in lakefile.lean exportTargetSpecs",
                    cfg.config_rel,
                    placed.placed_shards,
                    placed.placed_shards
                );
                continue;
            }
            assert!(
                combined_lakefiles.contains(&format!("\"{rel_norm}\"")),
                "placed_only config `{}` output `{rel_norm}` is missing from lakefile.lean exportTargetSpecs",
                cfg.config_rel
            );
            continue;
        }
        for target in &cfg.targets {
            let rel = target
                .lean_file
                .strip_prefix(&repo_root)
                .unwrap_or(&target.lean_file)
                .to_string_lossy();
            let rel_norm = if let Some(rest) = rel.strip_prefix("CaseStudies/")
                && let Some((_lib, after_lib)) = rest.split_once('/')
            {
                after_lib.to_string()
            } else {
                rel.to_string()
            };
            let stem = rel_norm.strip_suffix(".lean").unwrap_or(&rel_norm);
            assert!(
                combined_lakefiles.contains(&format!("\"{rel_norm}\""))
                    || combined_lakefiles.contains(&format!("shardOutputs \"{stem}\"")),
                "target `{}` output `{rel_norm}` is missing from lakefile.lean exportTargetSpecs",
                target.name
            );
        }
    }
}

#[test]
fn print_cflags_cli_and_verification_flags() {
    let cli_sub = Cli::try_parse_from(["rust-obj2lean", "print-cflags"]).unwrap();
    assert!(matches!(cli_sub.command, Some(CommandName::PrintCflags)));

    let cli_alias = Cli::try_parse_from(["rust-obj2lean", "cflags"]).unwrap();
    assert!(matches!(cli_alias.command, Some(CommandName::PrintCflags)));

    let cli_flag = Cli::try_parse_from(["rust-obj2lean", "--print-cflags"]).unwrap();
    assert!(cli_flag.print_cflags);

    let flags = native_cflags_string(&["-Iinclude".into(), "-DHAVE_CONFIG_H".into()]);
    assert!(flags.contains("-O2"), "{flags}");
    assert!(flags.contains("-fno-jump-tables"), "{flags}");
    assert!(flags.contains("-fno-common"), "{flags}");
    assert!(flags.contains("-fno-vectorize"), "{flags}");
    assert!(flags.contains("-fno-slp-vectorize"), "{flags}");
    assert!(flags.ends_with("-Iinclude -DHAVE_CONFIG_H"), "{flags}");

    // Optimization-level overrides in `c_flags` / `[[native_objects]].c_flags` are rejected.
    const TARGET: &str = "[[targets]]\nname = \"t\"\nlean_file = \"G/T.lean\"\nprog_name = \"p\"\ntitle = \"T\"\nlemma_allowlist = []\n";
    let dir = tempfile::tempdir().unwrap();
    let cfg_path = dir.path().join("translation.toml");
    for bad in [
        "-O0",
        "-O1",
        "-Os",
        "-Oz",
        "-Og",
        "-Ofast",
        "-O",
        "--optimize",
        "--optimize=1",
        "-fno-inline -O0",
    ] {
        let top_toml = format!(
            "obj_name = \"ok\"\nc_flags = [{bad:?}]\n[native_compiler]\nzig_version = \"0.16.0\"\n\
             [[native_objects]]\nname = \"shim\"\nsource = \"csrc/shim.c\"\n{TARGET}"
        );
        fs::write(&cfg_path, &top_toml).unwrap();
        let err = load_config(&cfg_path, &test_repo_root(), None).unwrap_err();
        assert!(
            format!("{err:#}").contains("overrides `-O2` optimization level"),
            "top-level {bad}: {err:#}"
        );

        let obj_toml = format!(
            "obj_name = \"ok\"\n[native_compiler]\nzig_version = \"0.16.0\"\n\
             [[native_objects]]\nname = \"shim\"\nsource = \"csrc/shim.c\"\nc_flags = [{bad:?}]\n{TARGET}"
        );
        fs::write(&cfg_path, &obj_toml).unwrap();
        let err = load_config(&cfg_path, &test_repo_root(), None).unwrap_err();
        assert!(
            format!("{err:#}").contains("overrides `-O2` optimization level"),
            "native_objects {bad}: {err:#}"
        );
    }
    for good in ["-O2", "-O3"] {
        let ok_toml = format!(
            "obj_name = \"ok\"\nc_flags = [{good:?}, \"-fno-inline\"]\n[native_compiler]\n\
             zig_version = \"0.16.0\"\n[[native_objects]]\nname = \"shim\"\n\
             source = \"csrc/shim.c\"\nc_flags = [{good:?}]\n{TARGET}"
        );
        fs::write(&cfg_path, &ok_toml).unwrap();
        load_config(&cfg_path, &test_repo_root(), None).unwrap();
    }

    // `name_selected` does not truncate Rust slice/array types (`<impl [T]>`) and
    // matches unnamespaced leaf names on local-suffixed symbols.
    let pat_impl = [regex::Regex::new("^(?:core::slice::<impl)$").unwrap()];
    assert!(!crate::untrusted_lemmas::name_selected(
        "core::slice::<impl [T]>::len",
        &pat_impl
    ));
    let pat_helper = [regex::Regex::new("^(?:helper)$").unwrap()];
    assert!(crate::untrusted_lemmas::name_selected(
        "my_crate::helper#1 [obj]",
        &pat_helper
    ));

    // Zero-sized data/tls `[[externs]]` entries are rejected by `load_config`.
    let dir = tempfile::tempdir().unwrap();
    let zero_toml = dir.path().join("translation.toml");
    fs::write(
        &zero_toml,
        r#"
obj_name = "ok"
c_objects = ["a.o"]
[[externs]]
name = "zero_data"
kind = { data = 0 }
[[targets]]
name = "t"
lean_file = "G/T.lean"
prog_name = "p"
title = "T"
lemma_allowlist = []
"#,
    )
    .unwrap();
    let err = load_config(&zero_toml, &test_repo_root(), None).unwrap_err();
    assert!(
        format!("{err:#}").contains("data/tls externs cannot have size 0"),
        "{err:#}"
    );
}

#[test]
fn c_library_archive_build_script_and_local_disambiguation() {
    if crate::untrusted_driver::find_zig_binary("test").is_err() {
        eprintln!("skipping: zig not available");
        return;
    }
    let dir = tempfile::tempdir().unwrap();
    let root = dir.path();
    fs::create_dir_all(root.join("include")).unwrap();
    fs::create_dir_all(root.join("src")).unwrap();

    fs::write(
        root.join("include/demo.h"),
        "#pragma once\n\
             extern void *malloc(unsigned long);\n\
             extern void free(void *);\n\
             extern int ext_counter;\n\
             extern long ext_explicit[2];\n\
             int alpha_entry(int x);\n\
             int beta_entry(int x);\n\
             int gamma_entry(int x);\n",
    )
    .unwrap();

    // alpha.c: defines `static const int k_table[4]`, `static int helper(int)`,
    // two function-scoped `static int acc` variables, a tentative global `int g_tentative;`
    // (requires `-fno-common`), a dense switch statement (requires `-fno-jump-tables`),
    // and takes the addresses of external `malloc` and `free`.
    fs::write(
        root.join("src/alpha.c"),
        "#include \"demo.h\"\n\
             int g_tentative;\n\
             static const int k_table[4] = {10, 20, 30, 40};\n\
             struct AllocHooks { void *(*alloc_fn)(unsigned long); void (*free_fn)(void *); };\n\
             static const struct AllocHooks k_hooks = { malloc, free };\n\
             static __attribute__((noinline)) int helper(int x) {\n\
                 static int acc = 1;\n\
                 acc += k_table[x & 3];\n\
                 switch (x & 7) {\n\
                     case 0: return acc + 3;\n\
                     case 1: return acc + 7;\n\
                     case 2: return acc + 11;\n\
                     case 3: return acc + 19;\n\
                     case 4: return acc + 23;\n\
                     case 5: return acc + 29;\n\
                     case 6: return acc + 31;\n\
                     default: return acc + 37;\n\
                 }\n\
             }\n\
             int alpha_entry(int x) {\n\
                 static int acc = 5;\n\
                 const struct AllocHooks * volatile hp = &k_hooks;\n\
                 void *p = hp->alloc_fn(16);\n\
                 if (p) hp->free_fn(p);\n\
                 g_tentative += acc;\n\
                 return helper(x) * DEMO_SCALE + ext_counter + (int)ext_explicit[0];\n\
             }\n",
    )
    .unwrap();

    // beta.c: ALSO defines `static const int k_table[4]` and `static int helper(int)`
    // with the exact same local names as `alpha.c`.
    fs::write(
        root.join("src/beta.c"),
        "#include \"demo.h\"\n\
             static const int k_table[4] = {1, 2, 3, 4};\n\
             static __attribute__((noinline)) int helper(int x) {\n\
                 return k_table[x & 3] + x;\n\
             }\n\
             int beta_entry(int x) {\n\
                 return helper(x) + alpha_entry(x);\n\
             }\n",
    )
    .unwrap();

    // gamma.c: compiled to a standalone `.o` and loaded via `c_objects`.
    fs::write(
        root.join("src/gamma.c"),
        "#include \"demo.h\"\n\
             static __attribute__((noinline)) int helper(int x) { return x ^ 0x55; }\n\
             int gamma_entry(int x) { return helper(x) + beta_entry(x); }\n",
    )
    .unwrap();

    fs::write(
        root.join("build.sh"),
        "#!/bin/sh\n\
             set -eu\n\
             mkdir -p build\n\
             $CC $CFLAGS -c src/alpha.c -o build/alpha.o\n\
             $CC $CFLAGS -c src/beta.c -o build/beta.o\n\
             rm -f build/libdemo.a\n\
             $AR rcs build/libdemo.a build/alpha.o build/beta.o\n\
             $CC $CFLAGS -c src/gamma.c -o build/gamma.o\n",
    )
    .unwrap();

    let toml = r#"
obj_name = "cDemo"
obj_file = "Generated/CDemoObj.lean"
code_file = "Generated/CDemoCode.lean"
namespace_prefix = "CDemo"
title = "C Demo Archive"
legacy_linked_image = true
build_script = "build.sh"
c_flags = ["-Iinclude", "-DDEMO_SCALE=2"]
c_archives = ["build/libdemo.a"]
c_objects = ["build/gamma.o"]

[[externs]]
name = "ext_explicit"
kind = { data = 16 }

[[targets]]
name = "demo"
lean_file = "Generated/CDemoLemmas.lean"
prog_name = "cDemoProg"
title = "C Demo Lemmas"
lemma_allowlist = ["alpha_entry", "beta_entry", "gamma_entry", "helper"]

[[targets]]
name = "demo_sharded"
lean_file = "Generated/CDemoShardedLemmas.lean"
prog_name = "cDemoShardedProg"
title = "C Demo Sharded Lemmas"
lemma_allowlist = ["alpha_entry", "beta_entry"]
lemma_shards = 2
"#;
    let toml_path = root.join("translation.toml");
    fs::write(&toml_path, toml).unwrap();

    let out_dir = root.join("out");
    let cfg = load_config(&toml_path, root, Some(&out_dir)).unwrap();
    let mut tc = Toolchain::new(root.to_path_buf()).unwrap();
    let files = generate_config(&cfg, &mut tc).unwrap();

    let find_text = |suffix: &str| -> String {
        let f = files
            .iter()
            .find(|f| f.path.to_string_lossy().ends_with(suffix))
            .unwrap_or_else(|| panic!("missing generated file `{suffix}`"));
        String::from_utf8(f.contents.clone()).unwrap()
    };

    let obj_lean = find_text("CDemoObj.lean");
    assert!(
        obj_lean.contains("* **Compile flags (CFLAGS)**: `-target aarch64-linux-musl -mcpu=generic -O2")
            && obj_lean.contains("-Iinclude -DDEMO_SCALE=2`"),
        "{obj_lean}"
    );
    assert!(
        obj_lean.contains("def cDemoAlphaObj : Obj.ObjectInfo where"),
        "{obj_lean}"
    );
    assert!(
        obj_lean.contains("def cDemoBetaObj : Obj.ObjectInfo where"),
        "{obj_lean}"
    );
    assert!(
        obj_lean.contains("def cDemoGammaObj : Obj.ObjectInfo where"),
        "{obj_lean}"
    );
    assert!(
        obj_lean.contains("def cDemoImage : Obj.LinkedImage where"),
        "{obj_lean}"
    );
    assert!(
        obj_lean
            .contains("  objects := [\n    cDemoGammaObj,\n    cDemoAlphaObj,\n    cDemoBetaObj]"),
        "{obj_lean}"
    );
    // Address-taken external functions `malloc` and `free` resolve as functions (stubs).
    let stubs = &obj_lean[obj_lean.find("  stubs := [").expect("stubs")..];
    assert!(stubs.contains("(\"malloc\", "), "{obj_lean}");
    assert!(stubs.contains("(\"free\", "), "{obj_lean}");
    // Inferred external data symbol `ext_counter` and configured `ext_explicit`.
    let extern_data = &obj_lean[obj_lean.find("  externData := [").expect("externData")..];
    assert!(
        extern_data.contains("(\"ext_counter\", ") && extern_data.contains(", 8)"),
        "{obj_lean}"
    );
    assert!(
        extern_data.contains("(\"ext_explicit\", ") && extern_data.contains(", 16)"),
        "{obj_lean}"
    );

    let code_lean = find_text("CDemoCode.lean");
    assert!(
        code_lean.contains("noncomputable def cDemoCode : Program := cDemoImage.toProgram"),
        "{code_lean}"
    );
    assert!(
            code_lean.contains("theorem cDemoCode_symbols_fresh : allFreshCharSymbols cDemoCode_symChars = true := by rfl_kernel"),
            "{code_lean}"
        );
    // By default (`emit_symbol_unique_lemmas = false`), output is byte-identical to main:
    // no `_symEnc`, `_stubEnc`, `_lookup_0x`, or `_unique_0x` declarations are emitted.
    assert!(!cfg.emit_symbol_unique_lemmas);
    assert!(
        !code_lean.contains("_symEnc")
            && !code_lean.contains("_stubEnc")
            && !code_lean.contains("_lookup_0x")
            && !code_lean.contains("_unique_0x"),
        "{code_lean}"
    );
    // Opting in via `emit_symbol_unique_lemmas = true` emits `_symEnc`, `_stubEnc`, correspondence
    // lemmas, and `_lookup_0x` / `_unique_0x` lemmas as a pure line-level superset of the default
    // `CDemoCode.lean`, leaving all other generated files byte-identical.
    let mut cfg_opt_in = cfg.clone();
    cfg_opt_in.emit_symbol_unique_lemmas = true;
    let files_opt_in = generate_config_with(&cfg_opt_in, &mut tc, false).unwrap();
    let files_default_no_dwarf = generate_config_with(&cfg, &mut tc, false).unwrap();
    assert_eq!(files_opt_in.len(), files_default_no_dwarf.len());
    for (def_f, opt_f) in files_default_no_dwarf.iter().zip(&files_opt_in) {
        assert_eq!(def_f.path, opt_f.path);
        if def_f.path.to_string_lossy().ends_with("CDemoCode.lean") {
            let def_code = String::from_utf8(def_f.contents.clone()).unwrap();
            let opt_code = String::from_utf8(opt_f.contents.clone()).unwrap();
            assert_eq!(def_code, code_lean);
            assert!(
                opt_code.contains(
                    "noncomputable def cDemoCode_symEnc : ProofLib.ObjectLoad.EncSymTable Nat := sym_enc_of% cDemoCode"
                ),
                "{opt_code}"
            );
            assert!(
                opt_code.contains(
                    "theorem cDemoCode_symEnc_eq : ProofLib.ObjectLoad.prepareCharAssocVal cDemoCode_symChars = cDemoCode_symEnc := by rfl_kernel"
                ),
                "{opt_code}"
            );
            assert!(
                opt_code.contains("theorem cDemoCode_lookupUnique_eq_symEnc"),
                "{opt_code}"
            );
            assert!(
                opt_code.contains("theorem cDemoCode_lookup_0x")
                    && opt_code.contains("theorem cDemoCode_unique_0x"),
                "{opt_code}"
            );
            let stripped: String = opt_code
                .lines()
                .filter(|ln| {
                    !ln.contains("_symEnc")
                        && !ln.contains("_stubEnc")
                        && !ln.starts_with("theorem cDemoCode_lookup_0x")
                        && !ln.starts_with("  lookup_of_allFresh ")
                        && !ln.starts_with("theorem cDemoCode_unique_0x")
                        && !ln.starts_with("  lookupUnique_of_allFresh ")
                })
                .collect::<Vec<_>>()
                .join("\n")
                + "\n";
            assert_eq!(stripped, def_code);
        } else {
            assert_eq!(
                def_f.contents,
                opt_f.contents,
                "non-Code file {} must be byte-identical regardless of emit_symbol_unique_lemmas",
                def_f.path.display()
            );
        }
    }
    assert!(!cfg.slice_stubs_in_code);
    let mut cfg_sliced = cfg.clone();
    cfg_sliced.slice_stubs_in_code = true;
    let files_sliced = generate_config_with(&cfg_sliced, &mut tc, false).unwrap();
    let sliced_code = files_sliced
        .iter()
        .find(|f| f.path.to_string_lossy().ends_with("CDemoCode.lean"))
        .map(|f| String::from_utf8(f.contents.clone()).unwrap())
        .unwrap();
    assert!(
        sliced_code.contains(
            "noncomputable def cDemoCode : Program :=\n  { cDemoImage.toProgram with code := cDemoImage.code.take cDemoCodeTextEnd }"
        ),
        "{sliced_code}"
    );
    assert!(
        sliced_code.contains("Program.ofImage_take_eq_rebase cDemoCode_canonical h")
            && sliced_code.contains("Program.codeLoaded_rebase_take_of_loaded cDemoCode_canonical h hL")
            && sliced_code.contains("fnSize_of_wordTree_take cDemoImage"),
        "{sliced_code}"
    );
    // Local symbols from alpha.o, beta.o, gamma.o are disambiguated and fresh.
    assert!(code_lean.contains("\"helper [alpha]\""), "{code_lean}");
    assert!(code_lean.contains("\"helper [beta]\""), "{code_lean}");
    assert!(code_lean.contains("\"helper [gamma]\""), "{code_lean}");
    assert!(code_lean.contains("def cDemoCode_funcTable"), "{code_lean}");
    assert!(
        code_lean.contains("theorem cDemoCode_fnSize_"),
        "{code_lean}"
    );
    // Symbol-keyed constants (backwards-compatible additions).
    assert!(
        code_lean.contains("abbrev cDemoCodeTextEnd : Nat := "),
        "{code_lean}"
    );
    assert!(
        code_lean.contains("abbrev cDemoCode_symOff_alpha_entry : Nat := 0x"),
        "{code_lean}"
    );
    assert!(
        code_lean.contains("abbrev cDemoCode_symAddr_alpha_entry : BitVec 64 := 0x"),
        "{code_lean}"
    );
    assert!(
        code_lean.contains("abbrev cDemoCode_symOff_helper_alpha : Nat := 0x"),
        "{code_lean}"
    );
    assert!(
        code_lean.contains("abbrev cDemoCode_symOff_helper_beta : Nat := 0x"),
        "{code_lean}"
    );
    assert!(
        code_lean.contains("abbrev cDemoCode_hookOff_malloc : Nat := 0x"),
        "{code_lean}"
    );
    // The `0x<hex>`-keyed hook theorem is kept, with a symbol-keyed alias right below it.
    let malloc_off = code_lean
        .lines()
        .find_map(|ln| ln.strip_prefix("abbrev cDemoCode_hookOff_malloc : Nat := "))
        .expect("malloc hookOff")
        .to_string();
    let hook_thm = format!("theorem cDemoCode_hookAtOff?_{malloc_off} {{b : BitVec 64}}");
    let alias = "theorem cDemoCode_hookAtOff?_malloc {b : BitVec 64}";
    let (hi, ai) = (
        code_lean
            .find(&hook_thm)
            .unwrap_or_else(|| panic!("{hook_thm}\n{code_lean}")),
        code_lean
            .find(alias)
            .unwrap_or_else(|| panic!("{alias}\n{code_lean}")),
    );
    assert!(hi < ai, "{code_lean}");
    assert!(
        code_lean.contains(
            "    (cDemoCode.rebase b H).hookAtOff? cDemoCode_hookOff_malloc = H \"malloc\" :=\n  \
                 cDemoCode_hookAtOff?_"
        ),
        "{code_lean}"
    );

    let lemmas_lean = find_text("CDemoLemmas.lean");
    assert!(
        code_lean.contains("set_option Elab.async false"),
        "{code_lean}"
    );
    assert!(
        lemmas_lean.contains("set_option Elab.async false"),
        "{lemmas_lean}"
    );
    assert!(lemmas_lean.contains("### `alpha_entry`"), "{lemmas_lean}");
    assert!(
        lemmas_lean.contains("### `helper [alpha]`"),
        "{lemmas_lean}"
    );
    assert!(lemmas_lean.contains("### `helper [beta]`"), "{lemmas_lean}");
    assert!(
        lemmas_lean.contains("register_fn_entry \"alpha_entry\""),
        "{lemmas_lean}"
    );
    // The `Code` module registers the function entries of every target (with that target's
    // decode prefix), so importing it alone populates `fnEntryExt`.
    let reg_lines = |text: &str| -> Vec<String> {
        text.lines()
            .filter(|ln| ln.starts_with("register_fn_entry "))
            .map(str::to_string)
            .collect()
    };
    let demo_regs = reg_lines(&lemmas_lean);
    assert!(!demo_regs.is_empty(), "{lemmas_lean}");
    let code_regs = reg_lines(&code_lean);
    for r in &demo_regs {
        assert!(code_regs.contains(r), "missing `{r}` in Code module:\n{code_lean}");
    }
    // Sharded target: the barrel and every shard carry the same full set of registrations.
    let sharded_barrel = find_text("CDemoShardedLemmas.lean");
    let sharded_regs = reg_lines(&sharded_barrel);
    assert_eq!(sharded_regs.len(), 2, "{sharded_barrel}");
    assert!(
        sharded_regs
            .iter()
            .all(|r| r.contains(" cDemoShardedProg ") || r.contains(".cDemoShardedProg ")),
        "{sharded_barrel}"
    );
    for r in &sharded_regs {
        assert!(code_regs.contains(r), "missing `{r}` in Code module:\n{code_lean}");
    }
    for i in 0..2 {
        let shard = find_text(&format!("CDemoShardedLemmasShard{i}.lean"));
        assert_eq!(reg_lines(&shard), sharded_regs, "{shard}");
        assert!(
            shard.find("register_fn_entry ").unwrap() < shard.rfind("\nend ").unwrap(),
            "{shard}"
        );
    }
    assert!(
        lemmas_lean.contains("gen_fetches cDemoCode cDemoProg true ["),
        "expected gen_fetches invocation in CDemoLemmas.lean: {lemmas_lean}"
    );
    assert!(
        !lemmas_lean.contains("unmodeled instruction"),
        "switch statement should compile without indirect jump tables: {lemmas_lean}"
    );

    let target_idx_json = find_text("CDemoLemmasIndex.json");
    assert!(
        target_idx_json.contains("\"schema_version\": 1"),
        "{target_idx_json}"
    );
    assert!(
        target_idx_json.contains("\"target\": \"demo\""),
        "{target_idx_json}"
    );
    assert!(
        target_idx_json.contains("\"code_file\": \"Generated/CDemoCode.lean\""),
        "{target_idx_json}"
    );
    assert!(
        target_idx_json.contains("\"lean_file\": \"Generated/CDemoLemmas.lean\""),
        "{target_idx_json}"
    );
    assert!(
        target_idx_json.contains("\"alpha_entry\""),
        "{target_idx_json}"
    );
    assert!(
        target_idx_json.contains("\"fn_off_lemma\""),
        "{target_idx_json}"
    );
    assert!(
        target_idx_json.contains("\"hook_at_off_lemma\""),
        "{target_idx_json}"
    );
    let code_idx_json = find_text("CDemoIndex.json");
    assert!(
        code_idx_json.contains("\"schema_version\": 1"),
        "{code_idx_json}"
    );
    assert!(
        code_idx_json.contains("\"target\": null"),
        "{code_idx_json}"
    );
    assert!(code_idx_json.contains("\"alpha_entry\""), "{code_idx_json}");
}

#[test]
fn tcb_modules_never_import_untrusted_lemmas() {
    let root_src = include_str!("lib.rs");
    let common_src = include_str!("trusted_common/mod.rs");
    let extractor_src = include_str!("trusted_extractor/mod.rs");
    let extracted_obj_src = include_str!("trusted_extractor/extracted_obj.rs");
    for (name, src) in [
        ("lib.rs", root_src),
        ("trusted_common/mod.rs", common_src),
        ("trusted_extractor/mod.rs", extractor_src),
        ("trusted_extractor/extracted_obj.rs", extracted_obj_src),
    ] {
        for line in src.lines() {
            let trimmed = line.trim();
            if trimmed.starts_with("//") {
                continue;
            }
            // The crate root may *declare* the untrusted modules, but not use them.
            if name == "lib.rs" && (trimmed.starts_with("pub mod ") || trimmed.starts_with("mod ")) {
                continue;
            }
            assert!(
                !trimmed.contains("untrusted_driver")
                    && !trimmed.contains("untrusted_lemmas")
                    && !trimmed.contains("untrusted_legacy_linker")
                    && !trimmed.contains("untrusted_placed")
                    && !trimmed.contains("decode_word_to_lean")
                    && !trimmed.contains("objdump")
                    && !trimmed.contains("theorem ")
                    && !trimmed.contains("std::process::Command")
                    && !trimmed.contains("cargo_metadata")
                    && !trimmed.contains("ArchiveFile")
                    && !trimmed.contains("root_section_closure"),
                "TCB module {name} must not reference untrusted modules, subprocesses, archive unpacking, or reachability pruning: {trimmed}"
            );
        }
    }
}

/// DWARF hints only change `*Index.json`: the trusted `Obj` module, `.bin` files, `Code` and
/// lemma modules are byte-identical with and without them (the trusted build stays `-g0`).
/// Also checks the index DWARF and the `symexec` source annotations derived from it.
#[test]
fn dwarf_hints_change_only_the_index() {
    if crate::untrusted_driver::find_zig_binary("test").is_err() {
        eprintln!("skipping: zig not available");
        return;
    }
    let dir = tempfile::tempdir().unwrap();
    let root = dir.path();
    fs::write(root.join("sample.c"), untrusted_lemmas::dwarf::SAMPLE_C).unwrap();
    let toml = r#"
obj_name = "dwSample"
obj_file = "Generated/DwSampleObj.lean"
code_file = "Generated/DwSampleCode.lean"
namespace_prefix = "DwSample"
title = "DWARF sample"
legacy_linked_image = true
c_sources = ["sample.c"]

[[targets]]
name = "dw"
lean_file = "Generated/DwSample.lean"
prog_name = "dwProg"
title = "DWARF sample"
lemma_allowlist = ["sum_list", "set_flags"]
"#;
    let toml_path = root.join("translation.toml");
    fs::write(&toml_path, toml).unwrap();
    let cfg = load_config(&toml_path, root, Some(&root.join("out"))).unwrap();
    let mut tc = Toolchain::new(root.to_path_buf()).unwrap();
    let with = generate_config_with(&cfg, &mut tc, true).unwrap();
    let without = generate_config_with(&cfg, &mut tc, false).unwrap();
    assert_eq!(with.len(), without.len());
    let mut idx_json = None;
    for (a, b) in with.iter().zip(&without) {
        assert_eq!(a.path, b.path);
        if a.path.to_string_lossy().ends_with("Index.json") {
            assert_ne!(a.contents, b.contents, "{}", a.path.display());
            idx_json.get_or_insert(String::from_utf8(a.contents.clone()).unwrap());
        } else {
            assert!(
                a.contents == b.contents,
                "{} depends on DWARF",
                a.path.display()
            );
        }
    }
    let idx: crate::untrusted_lemmas::index::TargetSymbolIndex =
        serde_json::from_str(&idx_json.unwrap()).unwrap();
    let f = idx.functions.iter().find(|f| f.name == "sum_list").unwrap();
    let d = f.dwarf.as_ref().expect("DWARF for sum_list");
    assert_eq!(
        d.signature(),
        "int sum_list(node_t * p, int unused, uint32_t k)"
    );
    assert_eq!(d.decl_file, "/src/sample.c");
    assert!(idx.dwarf_types.iter().any(|l| l.name == "struct node"));

    // `symexec` on the exported code: field names, lines and variables.
    let code = &with
        .iter()
        .find(|f| f.path.to_string_lossy().ends_with(".code.bin"))
        .unwrap()
        .contents;
    let bytes = &code[f.offset as usize..(f.offset + f.size_bytes) as usize];
    let mut report = untrusted_lemmas::symexec::analyze_and_execute(
        &f.name,
        f.offset,
        bytes,
        Some(f),
        0,
        &Default::default(),
        &Default::default(),
        &[],
        256,
        16,
    )
    .unwrap();
    report.source = Some(untrusted_lemmas::symexec::source::annotate(
        d,
        &idx.dwarf_types,
        &report,
    ));
    let text = untrusted_lemmas::symexec::format_report_text(&report);
    assert!(text.contains("--- DWARF Source"), "{text}");
    assert!(text.contains("param p = x0 (node_t *)"), "{text}");
    assert!(text.contains("DWARF vars @ +0x0: p = x0"), "{text}");
    assert!(text.contains("p->in.b : uint16_t"), "{text}");
    assert!(text.contains("p->buf[1] : uint32_t"), "{text}");
    assert!(text.contains("p->next : struct node *"), "{text}");
    assert!(text.contains("sample.c:"), "{text}");
}

#[test]
fn registry_facts_emits_rodata_abs64_lemmas() {
    if crate::untrusted_driver::find_zig_binary("test").is_err() {
        eprintln!("skipping: zig not available");
        return;
    }
    let dir = tempfile::tempdir().unwrap();
    let root = dir.path();
    let src = r#"
int alpha(int x) { return x + 1; }
int widget(int x) { return x * 2; }

typedef struct {
    int (*apply)(int);
} codec_op_t;

const codec_op_t vtable[2] = {
    { alpha },
    { widget },
};
"#;
    fs::write(root.join("vtable.c"), src).unwrap();
    let toml = r#"
obj_name = "regSample"
obj_file = "Generated/RegSampleObj.lean"
code_file = "Generated/RegSampleCode.lean"
registry_facts = true
namespace_prefix = "RegSample"
title = "Registry sample"
legacy_linked_image = true
c_sources = ["vtable.c"]

[[targets]]
name = "reg"
lean_file = "Generated/RegSample.lean"
prog_name = "regProg"
title = "Registry sample"
lemma_allowlist = ["alpha", "widget"]
"#;
    let toml_path = root.join("translation.toml");
    fs::write(&toml_path, toml).unwrap();
    let cfg = load_config(&toml_path, root, Some(&root.join("out"))).unwrap();
    let mut tc = Toolchain::new(root.to_path_buf()).unwrap();
    let files = generate_config_with(&cfg, &mut tc, false).unwrap();
    let reg_file = files
        .iter()
        .find(|f| f.path.to_string_lossy().ends_with("RegSampleRegistryFacts.lean"))
        .expect("expected RegSampleRegistryFacts.lean");
    let text = String::from_utf8(reg_file.contents.clone()).unwrap();
    assert!(text.contains("+ 0) = img.fnAddr \"alpha\""), "{text}");
    assert!(text.contains("+ 8) = img.fnAddr \"widget\""), "{text}");
    assert!(text.contains("rodataPtr_eq_fnAddr_of_loads himg (by rfl_kernel)"), "{text}");
}

#[test]
fn perturb_layout_cli_config_and_end_to_end_generation() {
    use crate::untrusted_driver::{
        PERTURB_LAYOUT_ENV, apply_perturb_layout_override, resolve_perturb_layout_bytes,
    };
    use clap::CommandFactory;

    // 1. `--help` documents `--perturb-layout` and `RUST_OBJ2LEAN_PERTURB_BYTES`.
    let mut help_buf = Vec::new();
    Cli::command().write_long_help(&mut help_buf).unwrap();
    let help_text = String::from_utf8(help_buf).unwrap();
    assert!(help_text.contains("--perturb-layout"), "{help_text}");
    assert!(help_text.contains(PERTURB_LAYOUT_ENV), "{help_text}");

    // 2. CLI parsing accepts multiples of 4 and rejects non-multiples of 4.
    let cli_ok = Cli::try_parse_from(["rust-obj2lean", "--perturb-layout", "64"]).unwrap();
    assert_eq!(cli_ok.perturb_layout, Some(64));
    let cli_bad = Cli::try_parse_from(["rust-obj2lean", "--perturb-layout", "62"]);
    assert!(cli_bad.is_err(), "non-multiple-of-4 CLI --perturb-layout must fail");

    // 3. Precedence: CLI > env > 0.
    assert_eq!(
        resolve_perturb_layout_bytes(Some(64), Some("4096")).unwrap(),
        64
    );
    assert_eq!(
        resolve_perturb_layout_bytes(None, Some("4096")).unwrap(),
        4096
    );
    assert_eq!(
        resolve_perturb_layout_bytes(None, Some("")).unwrap(),
        0
    );
    assert_eq!(
        resolve_perturb_layout_bytes(None, None).unwrap(),
        0
    );
    assert!(resolve_perturb_layout_bytes(None, Some("13")).is_err());

    // 4. `translation.toml` rejects persistent `perturb_layout_bytes` knob (CLI/env opt-in only).
    let (_tmp_bad, bad_toml) = write_tmp_crate(
        "bad-perturb",
        r#"
obj_name = "badPerturb"
perturb_layout_bytes = 64

[[targets]]
name = "t"
lean_file = "G/T.lean"
prog_name = "p"
title = "T"
lemma_allowlist = []
"#,
    );
    let err = load_config(&bad_toml, &test_repo_root(), None)
        .expect_err("persistent perturb_layout_bytes in translation.toml must be rejected");
    assert!(
        format!("{err:#}").contains("unknown field `perturb_layout_bytes`"),
        "{err:#}"
    );

    let (_tmp_ok, ok_toml) = write_tmp_crate(
        "ok-perturb",
        r#"
obj_name = "okPerturb"

[[targets]]
name = "t"
lean_file = "G/T.lean"
prog_name = "p"
title = "T"
lemma_allowlist = []
"#,
    );
    let mut cfg = load_config(&ok_toml, &test_repo_root(), None).unwrap();
    assert_eq!(cfg.perturb_layout_bytes, 0);
    let mut cfgs = vec![cfg.clone()];
    apply_perturb_layout_override(&mut cfgs, Some(4096)).unwrap();
    assert_eq!(cfgs[0].perturb_layout_bytes, 4096);

    // 5. End-to-end C compilation with `perturb_layout_bytes = 0` vs `64`.
    if crate::untrusted_driver::find_zig_binary("test").is_err() {
        eprintln!("skipping end-to-end C perturb test: zig not available");
        return;
    }
    let dir = tempfile::tempdir().unwrap();
    let root = dir.path();
    let src = r#"
int op_add(int a, int b) { return a + b; }
int op_sub(int a, int b) { return a - b; }
typedef int (*binop_t)(int, int);
const binop_t ops[2] = { op_add, op_sub };
int dispatch(int idx, int a, int b) { return ops[idx & 1](a, b); }
"#;
    fs::write(root.join("ops.c"), src).unwrap();
    let c_toml = r#"
obj_name = "pSample"
obj_file = "Generated/PSampleObj.lean"
code_file = "Generated/PSampleCode.lean"
registry_facts = true
namespace_prefix = "PSample"
title = "Perturb sample"
legacy_linked_image = true
c_sources = ["ops.c"]

[[targets]]
name = "ps"
lean_file = "Generated/PSample.lean"
prog_name = "psProg"
title = "Perturb sample"
lemma_allowlist = ["op_add", "op_sub", "dispatch"]
"#;
    let c_toml_path = root.join("translation.toml");
    fs::write(&c_toml_path, c_toml).unwrap();
    cfg = load_config(&c_toml_path, root, Some(&root.join("out0"))).unwrap();
    let mut cfg0_explicit = load_config(&c_toml_path, root, Some(&root.join("out0"))).unwrap();
    apply_perturb_layout_override(std::slice::from_mut(&mut cfg0_explicit), Some(0)).unwrap();
    let mut cfg64 = load_config(&c_toml_path, root, Some(&root.join("out64"))).unwrap();
    apply_perturb_layout_override(std::slice::from_mut(&mut cfg64), Some(64)).unwrap();

    let mut tc = Toolchain::new(root.to_path_buf()).unwrap();
    let files0 = generate_config_with(&cfg, &mut tc, false).unwrap();
    let files0_explicit = generate_config_with(&cfg0_explicit, &mut tc, false).unwrap();
    let files64 = generate_config_with(&cfg64, &mut tc, false).unwrap();

    // Verify byte-identical output across all generated files when perturbation is off (`0`).
    assert_eq!(files0.len(), files0_explicit.len());
    for (a, b) in files0.iter().zip(&files0_explicit) {
        assert_eq!(a.path, b.path);
        assert_eq!(
            a.contents,
            b.contents,
            "generated file {} must be byte-identical when perturbation is off",
            a.path.display()
        );
    }

    let get_text = |files: &[GeneratedFile], suffix: &str| -> String {
        let f = files
            .iter()
            .find(|f| f.path.to_string_lossy().ends_with(suffix))
            .unwrap();
        String::from_utf8(f.contents.clone()).unwrap()
    };
    let code0 = get_text(&files0, "PSampleCode.lean");
    let code64 = get_text(&files64, "PSampleCode.lean");

    let parse_sym_off = |text: &str, sym: &str| -> u64 {
        let prefix = format!("abbrev pSampleCode_symOff_{sym} : Nat := 0x");
        let hex = text
            .lines()
            .find_map(|l| l.strip_prefix(&prefix))
            .unwrap_or_else(|| panic!("missing {prefix} in:\n{text}"));
        u64::from_str_radix(hex.trim(), 16).unwrap()
    };
    for sym in ["op_add", "op_sub", "dispatch", "ops"] {
        assert_eq!(
            parse_sym_off(&code64, sym),
            parse_sym_off(&code0, sym) + 64,
            "symbol {sym} offset should shift by +64 bytes"
        );
    }
}

#[test]
fn placed_only_multi_config_emits_only_placed_obj() {
    let dir = tempfile::tempdir().unwrap();
    fs::write(dir.path().join("alpha.c"), "int alpha(int x) { return x + 1; }\n").unwrap();
    let cfg_path = dir.path().join("translation.toml");
    fs::write(
        &cfg_path,
        r#"
obj_name = "alpha"
title = "`alpha`"
c_sources = ["alpha.c"]

[native_compiler]
zig_version = "0.16.0"

[placed]
placed_only = true
multi = true
exports = ["alpha"]
"#,
    )
    .unwrap();
    let out_dir = dir.path().join("out");
    let cfg = load_config(&cfg_path, &test_repo_root(), Some(&out_dir)).unwrap();
    assert!(cfg.targets.is_empty());
    let mut tc = Toolchain::new(test_repo_root()).unwrap();
    let files = generate_config_with(&cfg, &mut tc, false).unwrap();
    let names: Vec<String> = files
        .iter()
        .map(|f| f.path.file_name().unwrap().to_string_lossy().into_owned())
        .collect();
    assert!(names.contains(&"AlphaPlacedObj.lean".to_string()));
    assert!(!names.contains(&"AlphaObj.lean".to_string()));
    assert!(!names.contains(&"AlphaCode.lean".to_string()));
    assert!(!names.contains(&"AlphaIndex.json".to_string()));
}

#[test]
fn legacy_linked_image_gate_rejects_default_and_accepts_opt_in() {
    let dir = tempfile::tempdir().unwrap();
    fs::write(dir.path().join("alpha.c"), "int alpha(int x) { return x + 1; }\n").unwrap();
    let cfg_path = dir.path().join("translation.toml");
    fs::write(
        &cfg_path,
        r#"
obj_name = "alpha"
title = "`alpha`"
c_sources = ["alpha.c"]

[native_compiler]
zig_version = "0.16.0"

[[targets]]
name = "alpha"
lean_file = "Generated/Alpha.lean"
sub_namespace = "Alpha"
prog_name = "alphaProg"
title = "Alpha"
lemma_allowlist = ["alpha"]
"#,
    )
    .unwrap();
    let out_dir = dir.path().join("out");
    let mut cfg = load_config(&cfg_path, &test_repo_root(), Some(&out_dir)).unwrap();
    assert!(!cfg.legacy_linked_image);
    let mut tc = Toolchain::new(test_repo_root()).unwrap();
    let err = match generate_config_with(&cfg, &mut tc, false) {
        Ok(_) => panic!("non-placed_only config without legacy_linked_image must fail"),
        Err(e) => e,
    };
    let msg = format!("{err:#}");
    assert!(
        msg.contains("--legacy-linked-image") && msg.contains("placed_only = true"),
        "unexpected gate error: {msg}"
    );

    // CLI flag parse check (`--legacy-linked-image`).
    let cli = Cli::try_parse_from(["rust-obj2lean", "--legacy-linked-image"]).unwrap();
    assert!(cli.legacy_linked_image);
    cfg.legacy_linked_image = true;
    let files = generate_config_with(&cfg, &mut tc, false).unwrap();
    let obj = files
        .iter()
        .find(|f| f.path.to_string_lossy().ends_with("AlphaObj.lean"))
        .expect("AlphaObj.lean emitted with legacy_linked_image = true");
    let obj_text = String::from_utf8(obj.contents.clone()).unwrap();
    assert!(
        obj_text.contains("public import Arm64.Legacy"),
        "legacy Obj module must import Arm64.Legacy:\n{obj_text}"
    );
}

#[test]
fn placed_only_with_extracted_obj_never_calls_legacy_linker_and_matches_hybrid_mode() {
    if crate::untrusted_driver::find_zig_binary("test").is_err() {
        eprintln!("skipping end-to-end C placed_only extracted_obj test: zig not available");
        return;
    }
    let cli = Cli::try_parse_from(["rust-obj2lean", "--placed-only", "--extracted-obj"]).unwrap();
    assert!(cli.placed_only);
    assert!(cli.extracted_obj);

    let dir = tempfile::tempdir().unwrap();
    fs::write(
        dir.path().join("alpha.c"),
        "extern int ext_fn(int); static int slot = 7; int alpha(int x) { return ext_fn(x + slot); }\n",
    )
    .unwrap();
    let cfg_path = dir.path().join("translation.toml");
    fs::write(
        &cfg_path,
        r#"
obj_name = "alpha"
title = "`alpha`"
c_sources = ["alpha.c"]

[native_compiler]
zig_version = "0.16.0"

[[externs]]
name = "ext_fn"
kind = "func"

[placed]
placed_only = true
multi = true
emit_extracted_obj = true
exports = ["alpha"]
"#,
    )
    .unwrap();
    let out_dir = dir.path().join("out");
    let cfg = load_config(&cfg_path, &test_repo_root(), Some(&out_dir)).unwrap();
    let mut tc = Toolchain::new(test_repo_root()).unwrap();
    crate::untrusted_driver::pipeline::reset_legacy_linker_calls();
    let files = generate_config_with(&cfg, &mut tc, false).unwrap();
    assert_eq!(
        crate::untrusted_driver::pipeline::legacy_linker_calls(),
        0,
        "placed_only + emit_extracted_obj must never invoke untrusted_legacy_linker"
    );
    let names: Vec<String> = files
        .iter()
        .map(|f| f.path.file_name().unwrap().to_string_lossy().into_owned())
        .collect();
    assert!(names.contains(&"AlphaPlacedObj.lean".to_string()));
    assert!(names.contains(&"AlphaExtractedObj.lean".to_string()));
    assert!(names.contains(&"AlphaExtractedObj.bin".to_string()));
    assert!(!names.contains(&"AlphaObj.lean".to_string()));

    let placed_only_lean = files
        .iter()
        .find(|f| f.path.to_string_lossy().ends_with("AlphaExtractedObj.lean"))
        .unwrap()
        .contents
        .clone();
    let placed_only_bin = files
        .iter()
        .find(|f| f.path.to_string_lossy().ends_with("AlphaExtractedObj.bin"))
        .unwrap()
        .contents
        .clone();

    // When `legacy_linked_image = true` and `placed_only = false`, `ExtractedObj` outputs remain
    // byte-for-byte identical because they are emitted directly from `&ex` independently of `li`.
    let mut hybrid_cfg = cfg.clone();
    hybrid_cfg.legacy_linked_image = true;
    hybrid_cfg.placed.as_mut().unwrap().placed_only = false;
    let hybrid_files = generate_config_with(&hybrid_cfg, &mut tc, false).unwrap();
    let hybrid_lean = hybrid_files
        .iter()
        .find(|f| f.path.to_string_lossy().ends_with("AlphaExtractedObj.lean"))
        .unwrap()
        .contents
        .clone();
    let hybrid_bin = hybrid_files
        .iter()
        .find(|f| f.path.to_string_lossy().ends_with("AlphaExtractedObj.bin"))
        .unwrap()
        .contents
        .clone();
    assert_eq!(placed_only_lean, hybrid_lean);
    assert_eq!(placed_only_bin, hybrid_bin);
}
