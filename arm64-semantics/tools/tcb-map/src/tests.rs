// Copyright 2026 Google LLC
//
// All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
// limitations under the License.

//! Unit and regression tests for `tcb-map` (`[TEST ONLY]`).
//!
//! # Purpose & Trust Role
//! - **Trust Role:** `[TEST ONLY]` (`#[cfg(test)]` unit test suite for `tcb-map`).
//! - **Purpose:** Verifies module classification ([`discovery::classify`]), comment and string
//!   stripping ([`lex::strip_comments_and_strings`]), library layering, `Spec`/`Proof`/`Theorems`
//!   import isolation, forbidden soundness/role-purity line constructs (`sorry`, `axiom`,
//!   `unsafe`, `native_decide`, `rfl_kernel`), forbidden declaration attributes, `tcb` Rust
//!   imports (`tcb_rust_import_*`), pairwise standalone-package isolation (`package_isolation_*`,
//!   `sibling_case_studies_*`), and `README.md` / `policy.rs` convention-table synchronization.
//!
//! # Key Types & Functions
//! - `check`: Builds an in-memory [`Workspace::from_sources`] and returns all [`Violation`]s.
//! - `has`: Checks whether a specific file and rule substring appear in the violation list.
//!
//! # When to Read This File
//! - Read this file when adding regression tests for new policy rules in [`policy.rs`](policy.rs)
//!   or lexer edge cases in [`lex.rs`](lex.rs); otherwise the header suffices.

use super::*;
use std::collections::BTreeSet;
use std::fs;
use std::path::Path;

fn check(sources: &[(&str, &str)]) -> Vec<Violation> {
    Workspace::from_sources(sources.iter().copied())
        .unwrap()
        .check_all()
}

fn has(violations: &[Violation], path: &str, needle: &str) -> bool {
    violations
        .iter()
        .any(|v| v.path == path && v.rule.contains(needle))
}

#[test]
fn classification() {
    let cases = [
        ("Arm64", Lib::Arm64, Role::Spec),
        ("Arm64.Hoare", Lib::Arm64, Role::Spec),
        ("Arm64.Trusted.Spec.AsciiNum", Lib::Arm64, Role::Spec),
        ("Arm64.Trusted.Surface.Abi", Lib::Arm64, Role::Spec),
        ("Arm64.Trusted.Surface.Ascii", Lib::Arm64, Role::Spec),
        ("Arm64.Trusted.Surface.CType", Lib::Arm64, Role::Spec),
        ("Arm64.Trusted.Object.Labels", Lib::Arm64, Role::Spec),
        ("ProofLib.SimpAttrs", Lib::ProofLib, Role::Proof),
        ("ProofLib.Frame.Spec", Lib::ProofLib, Role::Proof),
        ("ProofLib.Frame", Lib::ProofLib, Role::Proof),
        ("ProofLib.CoreLemmas", Lib::ProofLib, Role::Proof),
        ("ProofLib.Placed.LabelsCheck", Lib::ProofLib, Role::Proof),
        ("ProofLib.Placed.LabelsInterned", Lib::ProofLib, Role::Proof),
        ("ProofLib.Placed.LabelsCoverage", Lib::ProofLib, Role::Proof),
        ("VerifiedLibraries", Lib::VerifiedLibraries, Role::Proof),
        ("VerifiedLibraries.Common", Lib::VerifiedLibraries, Role::Proof),
        (
            "VerifiedLibraries.Common.Spec",
            Lib::VerifiedLibraries,
            Role::Spec,
        ),
        (
            "VerifiedLibraries.Common.Spec.Sha512",
            Lib::VerifiedLibraries,
            Role::Spec,
        ),
        ("CaseStudies.Alpha", Lib::Examples, Role::Proof),
        ("CaseStudies.Alpha.Spec", Lib::Examples, Role::Spec),
        ("CaseStudies.Alpha.Spec.Top", Lib::Examples, Role::Spec),
        ("CaseStudies.Alpha.Proofs.Main", Lib::Examples, Role::Proof),
        ("CaseStudies.Alpha.Witness", Lib::Examples, Role::Proof),
        ("CaseStudies.Alpha.Witness.Foo", Lib::Examples, Role::Proof),
        ("CaseStudies.Alpha.Spec.Witness", Lib::Examples, Role::Spec),
        (
            "VerifiedLibraries.Gamma.Witness.Foo",
            Lib::VerifiedLibraries,
            Role::Proof,
        ),
        ("CaseStudies.Alpha.Generated", Lib::Examples, Role::Proof),
        (
            "CaseStudies.Alpha.Generated.AlphaPlacedObj",
            Lib::Examples,
            Role::Spec,
        ),
        (
            "CaseStudies.Alpha.Generated.AlphaExtractedObj",
            Lib::Examples,
            Role::Spec,
        ),
        (
            "CaseStudies.Alpha.Generated.AlphaElfObj",
            Lib::Examples,
            Role::Spec,
        ),
        (
            "CaseStudies.Alpha.Generated.AlphaObj",
            Lib::Examples,
            Role::Proof,
        ),
        (
            "CaseStudies.Alpha.Generated.AlphaPlacedObjShard0",
            Lib::Examples,
            Role::Spec,
        ),
        (
            "CaseStudies.Alpha.Generated.AlphaPlacedObjShard12",
            Lib::Examples,
            Role::Spec,
        ),
        (
            "CaseStudies.Alpha.Generated.AlphaPlacedObjShard",
            Lib::Examples,
            Role::Proof,
        ),
        (
            "CaseStudies.Alpha.Generated.AlphaShard0",
            Lib::Examples,
            Role::Proof,
        ),
        (
            "CaseStudies.Alpha.Generated.AlphaCode",
            Lib::Examples,
            Role::Proof,
        ),
        // Per-ELF facts modules (parsed ELF + parse theorem) are proofs, not trusted data.
        (
            "CaseStudies.Alpha.Generated.AlphaElfFacts",
            Lib::Examples,
            Role::Proof,
        ),
        ("Arm64.Testing.UnitTests", Lib::Arm64Testing, Role::Test),
        ("ProofLib.Testing.SepLogic", Lib::Testing, Role::Test),
        ("ProofLib.Testing.LabelsCoverage", Lib::Testing, Role::Test),
        ("ProofLib.Testing.AxiomAudit.Fixtures", Lib::Testing, Role::Fixture),
        (
            "CaseStudies.Alpha.Testing.SpecAudit",
            Lib::Testing,
            Role::Test,
        ),
        (
            "CaseStudies.Alpha.Testing.AxiomAudit.Fixtures",
            Lib::Testing,
            Role::Fixture,
        ),
    ];
    for (module, lib, role) in cases {
        assert_eq!(
            classify(module),
            Some(ModuleClass { lib, role }),
            "{module}"
        );
    }
    for unknown in [
        "Specifications.NS",
        "Specs",
        "Specs.Abi.Aapcs",
        "Examples",
        "Examples.CaseStudies.Alpha.Spec",
        "Examples.Generated.AlphaObj",
        "Theorems",
        "Theorems.Alpha",
        "CaseStudies",
        "CaseStudies.Common.Sha512",
        "CaseStudies.Alpha.RandomHelper",
        "CaseStudies.Alpha.SpecHelpers",
        "CaseStudies.Alpha.Aux.Foo",
        "VerifiedLibraries.Alpha.Stray",
        "CaseStudies.Alpha.Witnesses.Foo",
        "CaseStudies.Alpha.WitnessHelpers",
    ] {
        assert_eq!(classify(unknown), None, "{unknown}");
    }
    assert!(Workspace::from_sources([("Proofs/Foo.lean", "")]).is_err());
    assert!(Workspace::from_sources([("CaseStudies/Alpha/Stray.lean", "")]).is_err());
}

#[test]
fn strip_comments_and_strings_preserves_lines() {
    let src = "\
-- theorem fake_thm : True := sorry
/- nested /- block sorry axiom -/ still comment -/
def msg : String := \"sorry axiom native_decide\"
theorem real_thm : True := by sorry
";
    let lines: Vec<String> = strip_comments_and_strings(src)
        .lines()
        .map(String::from)
        .collect();
    assert_eq!(lines.len(), 4);
    assert!(lines[..3].iter().all(|l| !l.contains("sorry")));
    assert!(lines[3].contains("theorem real_thm") && lines[3].contains("sorry"));
}

#[test]
fn spec_may_only_import_spec() {
    let v = check(&[
        ("Arm64.lean", "def Base := Nat\n"),
        (
            "ProofLib/Lemmas.lean",
            "import Arm64\ntheorem t : True := trivial\n",
        ),
        (
            "CaseStudies/Alpha/Spec.lean",
            "import Arm64\nimport ProofLib.Lemmas\n",
        ),
        ("CaseStudies/Alpha.lean", "import CaseStudies.Alpha.Spec\n"),
    ]);
    assert!(
        has(&v, "CaseStudies/Alpha/Spec.lean", "may only import Spec modules"),
        "{v:#?}"
    );
    assert!(
        !has(&v, "CaseStudies/Alpha.lean", "may only import Spec"),
        "{v:#?}"
    );
}

#[test]
fn external_iris_imports_forbidden_everywhere() {
    let v = check(&[
        ("Arm64.lean", "def Base := Nat\n"),
        (
            "Arm64/Trusted/Spec/SepLogic.lean",
            "import Iris.BI\ndef X := 1\n",
        ),
        (
            "CaseStudies/Alpha/Spec.lean",
            "import Arm64\nimport Iris.BI\n",
        ),
        (
            "CaseStudies/Alpha/Theorems.lean",
            "import CaseStudies.Alpha.Spec\nimport Iris.BI\n",
        ),
        (
            "CaseStudies/Alpha.lean",
            "import CaseStudies.Alpha.Spec\n",
        ),
        (
            "ProofLib/SepLogic/Basic.lean",
            "import Arm64\nimport Iris.BI\nimport Iris.ProofMode\n",
        ),
        (
            "ProofLib/Testing/UnitTests.lean",
            "import Iris.BI\n",
        ),
    ]);
    for path in [
        "Arm64/Trusted/Spec/SepLogic.lean",
        "CaseStudies/Alpha/Spec.lean",
        "CaseStudies/Alpha/Theorems.lean",
        "ProofLib/SepLogic/Basic.lean",
        "ProofLib/Testing/UnitTests.lean",
    ] {
        assert!(
            has(&v, path, "import of unknown library `Iris.BI`"),
            "expected `{path}` to reject `Iris.BI`, got {v:#?}"
        );
    }
    assert!(
        !v.iter().any(|x| x.path == "CaseStudies/Alpha.lean"),
        "{v:#?}"
    );
}

#[test]
fn trusted_specs_never_import_prooflib() {
    let v = check(&[
        ("Arm64.lean", "def Base := Nat\n"),
        ("Arm64/Trusted/Surface/Abi.lean", "import Arm64\ndef Spec := Nat\n"),
        (
            "Arm64/Trusted/Spec/Bad.lean",
            "import Arm64\nimport ProofLib.Abi.Spec\n",
        ),
        ("Arm64/Trusted/Spec/BadMathlib.lean", "import Mathlib.Tactic\n"),
        (
            "ProofLib/Abi/Spec.lean",
            "import Arm64.Trusted.Surface.Abi\ndef Y := 1\n",
        ),
        (
            "ProofLib/Abi.lean",
            "import Arm64.Trusted.Surface.Abi\ntheorem t : True := trivial\n",
        ),
        (
            "CaseStudies/Alpha/Spec.lean",
            "import Arm64\nimport Arm64.Trusted.Surface.Abi\nimport ProofLib.Abi.Spec\n",
        ),
        (
            "CaseStudies/Alpha.lean",
            "import CaseStudies.Alpha.Spec\nimport ProofLib.Abi\n",
        ),
        (
            "CaseStudies/Alpha/Theorems.lean",
            "import CaseStudies.Alpha.Spec\nimport CaseStudies.Alpha\nimport Arm64.Trusted.Surface.Abi\nimport ProofLib.Abi\n",
        ),
    ]);
    // Even a `ProofLib` module named `Spec` is untrusted `Proof`.
    assert!(
        has(
            &v,
            "CaseStudies/Alpha/Spec.lean",
            "may only import Spec modules, not `ProofLib.Abi.Spec`"
        ),
        "{v:#?}"
    );
    assert!(
        has(&v, "ProofLib/Abi/Spec.lean", "ProofLib module named `Spec`"),
        "{v:#?}"
    );
    assert!(has(&v, "Arm64/Trusted/Spec/Bad.lean", "layering"), "{v:#?}");
    assert!(
        has(&v, "Arm64/Trusted/Spec/Bad.lean", "may only import Spec modules"),
        "{v:#?}"
    );
    assert!(
        has(&v, "Arm64/Trusted/Spec/BadMathlib.lean", "import of unknown library `Mathlib.Tactic`"),
        "{v:#?}"
    );
    // Allowed edges: Spec -> Arm64 spec vocabulary, Proof -> ProofLib, ProofLib -> Arm64,
    // Theorems -> Arm64 + Spec + Proof + ProofLib.
    for (path, needle) in [
        ("CaseStudies/Alpha/Spec.lean", "`Arm64.Trusted.Surface.Abi`"),
        ("CaseStudies/Alpha.lean", "may only import"),
        ("CaseStudies/Alpha.lean", "layering"),
        ("ProofLib/Abi.lean", "layering"),
        ("Arm64/Trusted/Surface/Abi.lean", "layering"),
        ("CaseStudies/Alpha/Theorems.lean", "layering"),
        ("CaseStudies/Alpha/Theorems.lean", "may only import"),
    ] {
        assert!(!has(&v, path, needle), "{path}: {needle}: {v:#?}");
    }
}

#[test]
fn spec_top_naming_forbids_spec_cli() {
    let v = check(&[
        ("CaseStudies/Alpha/Spec/Cli.lean", "def X := 1\n"),
        ("VerifiedLibraries/Alpha/Spec/Cli.lean", "def Y := 1\n"),
        ("CaseStudies/Widget/Spec/Top.lean", "def Z := 1\n"),
        ("CaseStudies/Widget/Spec/Client.lean", "def C := 1\n"),
        ("CaseStudies/Widget/Proofs/Cli.lean", "def P := 1\n"),
    ]);
    assert!(
        has(
            &v,
            "CaseStudies/Alpha/Spec/Cli.lean",
            "non-uniform top-level Spec filename"
        ),
        "{v:#?}"
    );
    assert!(
        has(
            &v,
            "VerifiedLibraries/Alpha/Spec/Cli.lean",
            "non-uniform top-level Spec filename"
        ),
        "{v:#?}"
    );
    for ok in [
        "CaseStudies/Widget/Spec/Top.lean",
        "CaseStudies/Widget/Spec/Client.lean",
        "CaseStudies/Widget/Proofs/Cli.lean",
    ] {
        assert!(!v.iter().any(|x| x.path == ok), "{ok}: {v:#?}");
    }
}

#[test]
fn layering() {
    let v = check(&[
        (
            "CaseStudies/Alpha/Spec.lean",
            "import Mathlib.Data.Matrix.Basic\ndef X := 1\n",
        ),
        ("ProofLib/Bad.lean", "import CaseStudies.Alpha.Spec\n"),
        ("ProofLib/BadMathlib.lean", "import Mathlib.Tactic\n"),
        ("Arm64/Bad.lean", "import Arm64.Testing.UnitTests\n"),
        (
            "Arm64/BadMathlib.lean",
            "import Mathlib.Data.Matrix.Basic\n",
        ),
        ("Arm64/BadProofLib.lean", "import ProofLib\n"),
        ("ProofLib.lean", "import Arm64.Bad\n"),
        ("Arm64/Testing/UnitTests.lean", "import CaseStudies.Alpha.Spec\n"),
    ]);
    assert!(
        has(
            &v,
            "CaseStudies/Alpha/Spec.lean",
            "import of unknown library `Mathlib.Data.Matrix.Basic`"
        ),
        "{v:#?}"
    );
    assert!(has(&v, "ProofLib/Bad.lean", "layering"), "{v:#?}");
    assert!(
        has(&v, "ProofLib/BadMathlib.lean", "unknown library `Mathlib.Tactic`"),
        "{v:#?}"
    );
    assert!(has(&v, "Arm64/Bad.lean", "layering"), "{v:#?}");
    assert!(
        has(&v, "Arm64/BadMathlib.lean", "unknown library `Mathlib.Data.Matrix.Basic`"),
        "{v:#?}"
    );
    assert!(has(&v, "Arm64/BadProofLib.lean", "layering"), "{v:#?}");
    assert!(!has(&v, "ProofLib.lean", "layering"), "{v:#?}");
    assert!(
        has(&v, "Arm64/Testing/UnitTests.lean", "layering"),
        "{v:#?}"
    );
}

#[test]
fn arm64_testing_is_decoupled_from_examples_and_case_studies() {
    let v = check(&[
        ("Arm64.lean", "def Base := Nat\n"),
        ("ProofLib/Lemmas.lean", "import Arm64\n"),
        ("VerifiedLibraries/Alpha/Spec.lean", "import Arm64\n"),
        ("CaseStudies/Alpha/Spec.lean", "import Arm64\n"),
        (
            "Arm64/Testing/Good.lean",
            "import Arm64\nimport ProofLib.Lemmas\n-- VerifiedLibraries/ and CaseStudies/ in comments are fine\ndef p := \"Arm64/Testing/Regression/fixtures/echo_stdin.elf\"\n",
        ),
        (
            "Arm64/Testing/BadImport.lean",
            "import VerifiedLibraries.Alpha.Spec\nimport CaseStudies.Alpha.Spec\n",
        ),
        (
            "Arm64/Testing/BadPath.lean",
            "import Arm64\ndef elf := file_bytes% \"Examples/Fixtures/cp/cp.elf\"\ndef cfg := \"CaseStudies/Alpha/Implementation/translation.toml\"\n",
        ),
        (
            "Arm64/Testing/BadLibPath.lean",
            "import Arm64\ndef elf := file_bytes% \"../VerifiedLibraries/Alpha/fixture.elf\"\n",
        ),
        (
            "CaseStudies/Alpha/Proofs/BadImportArm64Testing.lean",
            "import Arm64.Testing.Good\n",
        ),
    ]);
    assert!(
        !v.iter().any(|x| x.path == "Arm64/Testing/Good.lean"),
        "{v:#?}"
    );
    assert!(
        has(
            &v,
            "Arm64/Testing/BadImport.lean",
            "layering: `Arm64.Testing.BadImport` (Arm64Testing) may not import `VerifiedLibraries.Alpha.Spec` (VerifiedLibraries)"
        ),
        "{v:#?}"
    );
    assert!(
        has(
            &v,
            "Arm64/Testing/BadImport.lean",
            "layering: `Arm64.Testing.BadImport` (Arm64Testing) may not import `CaseStudies.Alpha.Spec` (Examples)"
        ),
        "{v:#?}"
    );
    assert!(
        v.iter().any(|x| x.path == "Arm64/Testing/BadPath.lean"
            && x.rule == ARM64_TESTING_DECOUPLING_RULE
            && x.text.contains("references `Examples/`")),
        "{v:#?}"
    );
    assert!(
        v.iter().any(|x| x.path == "Arm64/Testing/BadPath.lean"
            && x.rule == ARM64_TESTING_DECOUPLING_RULE
            && x.text.contains("references `Implementation/`")),
        "{v:#?}"
    );
    assert!(
        v.iter().any(|x| x.path == "Arm64/Testing/BadLibPath.lean"
            && x.rule == ARM64_TESTING_DECOUPLING_RULE
            && x.text.contains("references `VerifiedLibraries/`")),
        "{v:#?}"
    );
    assert!(
        has(
            &v,
            "CaseStudies/Alpha/Proofs/BadImportArm64Testing.lean",
            "layering: `CaseStudies.Alpha.Proofs.BadImportArm64Testing` (Examples) may not import `Arm64.Testing.Good` (Arm64Testing)"
        ),
        "{v:#?}"
    );
}

#[test]
fn colocated_testing_subtrees() {
    let v = check(&[
        ("Arm64.lean", "import Arm64.Trusted\n"),
        ("Arm64/Trusted.lean", "import Arm64.Trusted.ISA.Decode\n"),
        ("Arm64/Trusted/ISA/Decode.lean", "def decode := 1\n"),
        ("Arm64/Trusted/Bad.lean", "import Arm64.Testing.UnitTests\n"),
        (
            "Arm64/Trusted/Surface/Abi.lean",
            "import Arm64\ndef abi := 1\n",
        ),
        (
            "Arm64/Trusted/Spec/Bad.lean",
            "import ProofLib.Testing.SpecAudit\n",
        ),
        ("ProofLib/Bad.lean", "import ProofLib.Testing.SpecAudit\n"),
        (
            "CaseStudies/Alpha/Spec.lean",
            "import Arm64.Trusted.Surface.Abi\ndef g := 1\n",
        ),
        (
            "CaseStudies/Alpha.lean",
            "import CaseStudies.Alpha.Spec\nimport CaseStudies.Beta.Testing.SpecAudit\n",
        ),
        (
            "CaseStudies/Beta/Spec.lean",
            "import CaseStudies.Beta.Spec.Inflate\nimport CaseStudies.Beta.Testing.SpecAudit\n",
        ),
        (
            "CaseStudies/Beta/Spec/Inflate.lean",
            "import CaseStudies.Beta.Generated.BetaPlacedObj\nimport CaseStudies.Beta.Generated.BetaElfObj\ndef i := 1\n",
        ),
        (
            "CaseStudies/Beta/Spec/LegacyBad.lean",
            "import CaseStudies.Beta.Generated.BetaObj\n",
        ),
        (
            "CaseStudies/Beta/Proofs/Inflate.lean",
            "import CaseStudies.Beta.Spec\ntheorem t : True := trivial\n",
        ),
        (
            "CaseStudies/Beta.lean",
            "import CaseStudies.Beta.Spec\nimport CaseStudies.Beta.Proofs.Inflate\n",
        ),
        ("CaseStudies/Beta/Generated.lean", ""),
        (
            "Arm64/Testing/UnitTests.lean",
            "import Arm64.Trusted.ISA.Decode\nimport ProofLib.Bad\ntheorem u : True := trivial\n",
        ),
        (
            "ProofLib/Testing/SpecAudit.lean",
            "import Arm64.Trusted.Surface.Abi\nimport Arm64.Testing.UnitTests\ntheorem s : True := trivial\n\
             def k (ax : Name) : Bool := ax == ``Lean.ofReduceBool\n",
        ),
        (
            "CaseStudies/Beta/Testing/SpecAudit.lean",
            "import CaseStudies.Beta.Spec\nimport CaseStudies.Beta.Proofs.Inflate\n\
             theorem a (x : BitVec 8) : x = x := by bv_decide\n",
        ),
        ("CaseStudies/Beta/Testing/Spec.lean", "theorem z : True := trivial\n"),
        ("CaseStudies/Beta/Testing/Bad.lean", "import CaseStudies.Beta.Theorems\n"),
        ("CaseStudies/Beta/Theorems.lean", "import CaseStudies.Beta.Spec\nimport CaseStudies.Beta\n"),
    ]);
    for bad in [
        "Arm64/Trusted/Bad.lean",
        "Arm64/Trusted/Spec/Bad.lean",
        "ProofLib/Bad.lean",
        "CaseStudies/Alpha.lean",
        "CaseStudies/Beta/Spec.lean",
        "CaseStudies/Beta/Testing/Bad.lean",
    ] {
        assert!(has(&v, bad, "layering"), "{bad}: {v:#?}");
    }
    assert!(
        has(&v, "CaseStudies/Beta/Spec.lean", "may only import Spec modules"),
        "{v:#?}"
    );
    assert!(
        has(
            &v,
            "CaseStudies/Beta/Spec/LegacyBad.lean",
            "may only import Spec modules"
        ),
        "{v:#?}"
    );
    for ok in [
        "Arm64/Testing/UnitTests.lean",
        "ProofLib/Testing/SpecAudit.lean",
        "CaseStudies/Beta/Testing/SpecAudit.lean",
        "CaseStudies/Beta/Testing/Spec.lean",
        "CaseStudies/Beta/Spec/Inflate.lean",
        "CaseStudies/Beta/Proofs/Inflate.lean",
        "CaseStudies/Beta.lean",
        "CaseStudies/Beta/Generated.lean",
        "CaseStudies/Beta/Theorems.lean",
    ] {
        assert!(!v.iter().any(|x| x.path == ok), "{ok}: {v:#?}");
    }
}

#[test]
fn unresolved_and_unknown_imports() {
    let v = check(&[(
        "CaseStudies/Alpha/Proofs/A.lean",
        "import Lean\nimport ProofLib.Missing\nimport UnknownPkg.Foo\nimport CaseStudies.Alpha.Generated.AlphaObj\n",
    )]);
    assert!(
        has(
            &v,
            "CaseStudies/Alpha/Proofs/A.lean",
            "unresolved import `ProofLib.Missing`"
        ),
        "{v:#?}"
    );
    assert!(
        has(
            &v,
            "CaseStudies/Alpha/Proofs/A.lean",
            "unknown library `UnknownPkg.Foo`"
        ),
        "{v:#?}"
    );
    assert!(
        !has(
            &v,
            "CaseStudies/Alpha/Proofs/A.lean",
            "unresolved import `CaseStudies.Alpha.Generated"
        ),
        "{v:#?}"
    );
}

#[test]
fn tour_only_imported_by_arm64_testing_umbrella() {
    let v = check(&[
        ("Arm64/Testing/Tours/SepLogicLawsTour.lean", "def x := 1\n"),
        (
            "Arm64/Testing.lean",
            "import Arm64.Testing.Tours.SepLogicLawsTour\n",
        ),
        (
            "Arm64/Testing/Proofs/SpecAdequacyKit.lean",
            "import Arm64.Testing.Tours.SepLogicLawsTour\n",
        ),
        (
            "CaseStudies/Alpha/Testing/DemoAdequacy.lean",
            "import Arm64.Testing.Tours.SepLogicLawsTour\n",
        ),
    ]);
    assert!(
        !v.iter().any(|x| x.path == "Arm64/Testing.lean"),
        "{v:#?}"
    );
    assert!(
        has(
            &v,
            "Arm64/Testing/Proofs/SpecAdequacyKit.lean",
            "tour `Arm64.Testing.Tours.SepLogicLawsTour` may only be imported by `Arm64.Testing`"
        ),
        "{v:#?}"
    );
    assert!(
        has(
            &v,
            "CaseStudies/Alpha/Testing/DemoAdequacy.lean",
            "tour `Arm64.Testing.Tours.SepLogicLawsTour` may only be imported by `Arm64.Testing`"
        ),
        "{v:#?}"
    );
}

#[test]
fn line_rules() {
    let v = check(&[
        (
            "CaseStudies/Alpha/Spec.lean",
            "theorem not_allowed : True := trivial\npartial def bad (x : Nat) : Nat := bad x\nset_option autoImplicit true\n",
        ),
        (
            "CaseStudies/Alpha.lean",
            "import CaseStudies.Alpha.Spec\ntheorem t : True := by sorry\n",
        ),
        (
            "ProofLib/X.lean",
            "axiom bad : False\nexample : True := by native_decide\n",
        ),
    ]);
    assert!(
        has(&v, "CaseStudies/Alpha/Spec.lean", "theorem/lemma"),
        "{v:#?}"
    );
    assert!(
        has(&v, "CaseStudies/Alpha/Spec.lean", "partial def"),
        "{v:#?}"
    );
    assert!(
        has(
            &v,
            "CaseStudies/Alpha/Spec.lean",
            "set_option autoImplicit true"
        ),
        "{v:#?}"
    );
    assert!(has(&v, "CaseStudies/Alpha.lean", "sorry"), "{v:#?}");
    assert!(has(&v, "ProofLib/X.lean", "axiom"), "{v:#?}");
    assert!(has(&v, "ProofLib/X.lean", "native_decide"), "{v:#?}");
}

#[test]
fn module_system_imports_and_modifiers() {
    let v = check(&[
        (
            "Arm64/Trusted/BadImport.lean",
            "module\npublic import ProofLib.Lemmas\nmeta import Arm64.Testing.UnitTests\npublic meta import all Mathlib.Tactic\n",
        ),
        (
            "CaseStudies/Alpha/Spec.lean",
            "module\npublic theorem not_allowed : True := trivial\npublic partial def bad1 (x : Nat) : Nat := bad1 x\npartial meta def bad2 (x : Nat) : Nat := bad2 x\n",
        ),
        (
            "CaseStudies/Alpha/Theorems.lean",
            "module\npublic import CaseStudies.Alpha.Spec\npublic def sneak : Nat := 0\n",
        ),
        (
            "ProofLib/Lemmas.lean",
            "module\npublic axiom bad_pub : False\nmeta axiom bad_meta : False\n@[expose] public axiom bad_attr : False\n",
        ),
        ("Arm64/Testing/UnitTests.lean", "module\n"),
    ]);
    assert!(
        has(&v, "Arm64/Trusted/BadImport.lean", "layering: `Arm64.Trusted.BadImport`"),
        "{v:#?}"
    );
    assert!(
        has(&v, "Arm64/Trusted/BadImport.lean", "Spec module `Arm64.Trusted.BadImport` may only import Spec modules, not `Arm64.Testing.UnitTests`"),
        "{v:#?}"
    );
    assert!(
        has(&v, "Arm64/Trusted/BadImport.lean", "import of unknown library `Mathlib.Tactic`"),
        "{v:#?}"
    );
    let spec_violations: Vec<_> = v
        .iter()
        .filter(|x| x.path == "CaseStudies/Alpha/Spec.lean")
        .collect();
    assert_eq!(spec_violations.len(), 3, "{spec_violations:#?}");
    assert!(
        has(&v, "CaseStudies/Alpha/Theorems.lean", "`def` in Theorems module"),
        "{v:#?}"
    );
    let axiom_violations: Vec<_> = v
        .iter()
        .filter(|x| x.path == "ProofLib/Lemmas.lean" && x.rule == "axiom")
        .collect();
    assert_eq!(axiom_violations.len(), 3, "{axiom_violations:#?}");
}

#[test]
fn forbidden_attributes() {
    let v = check(&[(
        "ProofLib/A.lean",
        "@[simp, implemented_by fImpl] def f := 1\n\
             @[inline,\n  extern \"g\"]\ndef g := 1\n\
             @[local simp] theorem t : True := trivial\n\
             -- @[extern \"c\"] in a comment\n\
             def extern := 1\n",
    )]);
    let attrs: Vec<_> = v.iter().map(|x| (x.line, x.rule.as_str())).collect();
    assert_eq!(
        attrs,
        [
            (1, "@[implemented_by] (swaps in unverified code)"),
            (3, "@[extern] (swaps in unverified foreign code)"),
        ],
        "{v:#?}"
    );
}

#[test]
fn theorems_modules() {
    assert_eq!(
        classify("VerifiedLibraries.Alpha.Theorems.Top"),
        Some(ModuleClass {
            lib: Lib::Theorems,
            role: Role::Theorems
        })
    );
    assert_eq!(
        classify("CaseStudies.Alpha.Theorems.Top"),
        Some(ModuleClass {
            lib: Lib::Theorems,
            role: Role::Theorems
        })
    );
    let v = check(&[
        ("Arm64.lean", "module\npublic def Base := Nat\n"),
        ("ProofLib/Lemmas.lean", "module\npublic import Arm64\n"),
        ("CaseStudies/Beta/Spec.lean", "import Arm64\ndef s := 1\n"),
        (
            "CaseStudies/Beta/Proofs/Main.lean",
            "import CaseStudies.Beta.Spec\ntheorem beta_ok : s = 1 := rfl\n",
        ),
        (
            "CaseStudies/Beta.lean",
            "import CaseStudies.Beta.Spec\nimport CaseStudies.Beta.Theorems.Good\n",
        ),
        (
            "CaseStudies/Alpha/Spec.lean",
            "module\npublic import Arm64\npublic import CaseStudies.Alpha.Theorems\npublic def aspec := 1\n",
        ),
        (
            "CaseStudies/Alpha/Proofs/Top.lean",
            "module\npublic import CaseStudies.Alpha.Spec\npublic section\ntheorem alpha_ok : aspec = 1 := rfl\nend\n",
        ),
        (
            "CaseStudies/Alpha/Theorems/Top.lean",
            "module\npublic import CaseStudies.Alpha.Spec\nimport CaseStudies.Alpha.Proofs.Top\nimport ProofLib.Lemmas\n\
             public section\n\
             theorem alphaTop_ok : _root_.CaseStudies.Alpha.aspec = 1 := _root_.CaseStudies.Alpha.Proofs.alpha_ok\n\
             end\n",
        ),
        (
            "CaseStudies/Alpha/Theorems.lean",
            "module\npublic import CaseStudies.Alpha.Theorems.Top\n",
        ),
        ("Arm64/Testing/UnitTests.lean", "import Arm64\n"),
        (
            "CaseStudies/Beta/Theorems/Good.lean",
            "import CaseStudies.Beta.Spec\nimport CaseStudies.Beta.Proofs.Main\nimport ProofLib.Lemmas\n\
             theorem betaTop_ok : _root_.CaseStudies.Beta.s = 1 := _root_.CaseStudies.Beta.Proofs.beta_ok\n",
        ),
        (
            "CaseStudies/Alpha/Theorems/Bad.lean",
            "import Arm64.Testing.UnitTests\n\
             open CaseStudies.Alpha\n\
             export CaseStudies.Alpha (aspec)\n\
             private theorem hidden : True := trivial\n\
             lemma bad_lemma : True := trivial\n\
             set_option autoImplicit true\n\
             set_option maxHeartbeats 0\n\
             def helper := 1\n@[simp] abbrev h2 := 2\nnoncomputable instance : Inhabited Nat := ⟨0⟩\n\
             @[simp] @[inline] structure S where\nnoncomputable @[simp] opaque opq : Nat\n\
             namespace X macro_rules | `(s) => `(1) end X\n\
             run_cmd pure ()\n\
             run_elab pure ()\n\
             run_meta pure ()\n\
             #eval 1\n\
             theorem ch_num : 1notation \"s\" => 1 = 1 := rfl\n\
             theorem ch_hash : x#eval 1 = 1 := rfl\n\
             theorem ch_uhash : é#eval 1 = 1 := rfl\n\
             theorem ch_sorry : True := by sorry\n\
             attribute[term_elab ident] helper\n\
             axiom cheat : False\ntheorem t : True := by native_decide\n",
        ),
    ]);
    for ok in [
        "CaseStudies/Beta/Theorems/Good.lean",
        "CaseStudies/Alpha/Theorems/Top.lean",
        "CaseStudies/Alpha/Theorems.lean",
        "CaseStudies/Alpha/Proofs/Top.lean",
        "CaseStudies/Beta/Proofs/Main.lean",
    ] {
        assert!(!v.iter().any(|x| x.path == ok), "{ok}: {v:#?}");
    }
    assert!(has(&v, "CaseStudies/Beta.lean", "layering"), "{v:#?}");
    assert!(has(&v, "CaseStudies/Alpha/Spec.lean", "layering"), "{v:#?}");
    assert!(
        has(&v, "CaseStudies/Alpha/Spec.lean", "may only import Spec modules"),
        "{v:#?}"
    );
    assert_eq!(
        v.iter()
            .filter(|x| x.path == "CaseStudies/Alpha/Theorems/Bad.lean"
                && x.rule.contains("`#eval` in Theorems"))
            .count(),
        3,
        "expected `#eval`, `x#eval`, and `é#eval` to be flagged in Theorems: {v:#?}"
    );
    for needle in [
        "layering",
        "`open` in Theorems",
        "`export` in Theorems",
        "`private` in Theorems",
        "`lemma` in Theorems",
        "set_option autoImplicit true",
        "set_option maxHeartbeats 0",
        "`def` in Theorems",
        "`abbrev` in Theorems",
        "`instance` in Theorems",
        "`structure` in Theorems",
        "`opaque` in Theorems",
        "`macro_rules` in Theorems",
        "`notation` in Theorems",
        "`run_cmd` in Theorems",
        "`run_elab` in Theorems",
        "`run_meta` in Theorems",
        "`#eval` in Theorems",
        "sorry",
        "@[term_elab] in Theorems",
        "axiom",
        "native_decide",
    ] {
        assert!(
            has(&v, "CaseStudies/Alpha/Theorems/Bad.lean", needle),
            "{needle}: {v:#?}"
        );
    }
}

#[test]
fn theorems_module_isolation_and_proof_notations() {
    let v = check(&[
        ("Arm64.lean", "module\npublic def Base := Nat\n"),
        (
            "CaseStudies/Alpha/Spec.lean",
            "module\npublic import Arm64\npublic def AlphaStmt : Prop := True\n",
        ),
        (
            "CaseStudies/Alpha/Proofs/GoodNotations.lean",
            "module\npublic import CaseStudies.Alpha.Spec\n\
             local notation \"ALPHA_LOCAL\" => True\n\
             scoped notation \"ALPHA_SCOPED\" => True\n",
        ),
        (
            "CaseStudies/Alpha/Proofs/BadNotations.lean",
            "module\npublic import CaseStudies.Alpha.Spec\n\
             notation \"AlphaStmt\" => True\n\
             infixl:65 \" +++ \" => Nat.add\n",
        ),
        (
            "CaseStudies/Alpha/Theorems/PubProof.lean",
            "module\npublic import CaseStudies.Alpha.Spec\npublic import CaseStudies.Alpha.Proofs.GoodNotations\n\
             public section\ntheorem t : _root_.CaseStudies.Alpha.AlphaStmt := trivial\nend\n",
        ),
        (
            "CaseStudies/Alpha/Theorems/PrivSpecAndMeta.lean",
            "module\nimport CaseStudies.Alpha.Spec\nmeta import CaseStudies.Alpha.Proofs.GoodNotations\n",
        ),
        (
            "CaseStudies/Alpha/Theorems/MissingModule.lean",
            "import CaseStudies.Alpha.Spec\nimport CaseStudies.Alpha.Proofs.GoodNotations\n\
             theorem t : _root_.CaseStudies.Alpha.AlphaStmt := trivial\n",
        ),
        (
            "CaseStudies/Alpha/Theorems/MissingPubSection.lean",
            "module\npublic import CaseStudies.Alpha.Spec\nimport CaseStudies.Alpha.Proofs.GoodNotations\n\
             theorem t : _root_.CaseStudies.Alpha.AlphaStmt := trivial\n",
        ),
        (
            "CaseStudies/Alpha/Theorems/ClosedEarlyPubSection.lean",
            "module\npublic import CaseStudies.Alpha.Spec\nimport CaseStudies.Alpha.Proofs.GoodNotations\n\
             public section\nend\ntheorem t : _root_.CaseStudies.Alpha.AlphaStmt := trivial\n",
        ),
        (
            "CaseStudies/Alpha/Theorems/SingleLineClosedPubSection.lean",
            "module\npublic import CaseStudies.Alpha.Spec\nimport CaseStudies.Alpha.Proofs.GoodNotations\n\
             public section end theorem t : _root_.CaseStudies.Alpha.AlphaStmt := trivial\n",
        ),
        (
            "CaseStudies/Alpha/Theorems/ValidScopedPubSection.lean",
            "module\npublic import CaseStudies.Alpha.Spec\nimport CaseStudies.Alpha.Proofs.GoodNotations\n\
             public section\nnamespace CaseStudies.Alpha.Theorems\n\
             theorem t : _root_.CaseStudies.Alpha.AlphaStmt := trivial\n\
             end CaseStudies.Alpha.Theorems\nend\n",
        ),
        (
            "CaseStudies/Alpha/Theorems/Testing/BadTestingPath.lean",
            "module\npublic import CaseStudies.Alpha.Spec\n\
             public section\ntheorem t : _root_.CaseStudies.Alpha.AlphaStmt := trivial\nend\n",
        ),
        (
            "CaseStudies/Alpha/Theorems/Fixtures.lean",
            "module\npublic import CaseStudies.Alpha.Spec\n\
             public section\ntheorem t : _root_.CaseStudies.Alpha.AlphaStmt := trivial\nend\n",
        ),
        (
            "CaseStudies/Alpha/Theorems/_HiddenMod.lean",
            "module\npublic import CaseStudies.Alpha.Spec\n\
             public section\ntheorem t : _root_.CaseStudies.Alpha.AlphaStmt := trivial\nend\n",
        ),
        (
            "CaseStudies/Alpha/Theorems/UnderscoreNames.lean",
            "module\npublic import CaseStudies.Alpha.Spec\n\
             public section\nnamespace _Internal\n\
             theorem _hidden_ok : _root_.CaseStudies.Alpha.AlphaStmt := trivial\n\
             end _Internal\nend\n",
        ),
    ]);
    assert!(
        !v.iter()
            .any(|x| x.path == "CaseStudies/Alpha/Proofs/GoodNotations.lean"),
        "expected `local` and `scoped` notations in Proofs to pass: {v:#?}"
    );
    assert!(
        !v.iter()
            .any(|x| x.path == "CaseStudies/Alpha/Theorems/ValidScopedPubSection.lean"),
        "expected valid `public section` + `namespace` + `end` to pass: {v:#?}"
    );
    assert!(
        has(
            &v,
            "CaseStudies/Alpha/Proofs/BadNotations.lean",
            "unscoped `notation` in Examples proof module"
        ),
        "{v:#?}"
    );
    assert!(
        has(
            &v,
            "CaseStudies/Alpha/Proofs/BadNotations.lean",
            "unscoped `infixl` in Examples proof module"
        ),
        "{v:#?}"
    );
    assert!(
        has(
            &v,
            "CaseStudies/Alpha/Theorems/PubProof.lean",
            "must use private `import` (not `public import`) for Proof module"
        ),
        "{v:#?}"
    );
    assert!(
        has(
            &v,
            "CaseStudies/Alpha/Theorems/PrivSpecAndMeta.lean",
            "must use `public import` for Spec module"
        ),
        "{v:#?}"
    );
    assert!(
        has(
            &v,
            "CaseStudies/Alpha/Theorems/PrivSpecAndMeta.lean",
            "may not `meta import`"
        ),
        "{v:#?}"
    );
    assert!(
        has(
            &v,
            "CaseStudies/Alpha/Theorems/MissingModule.lean",
            "must start with `module` when all imported modules use `module`"
        ),
        "{v:#?}"
    );
    assert!(
        has(
            &v,
            "CaseStudies/Alpha/Theorems/MissingPubSection.lean",
            "must declare `public section`"
        ),
        "{v:#?}"
    );
    assert!(
        has(
            &v,
            "CaseStudies/Alpha/Theorems/ClosedEarlyPubSection.lean",
            "must declare `public section`"
        ),
        "{v:#?}"
    );
    assert!(
        has(
            &v,
            "CaseStudies/Alpha/Theorems/SingleLineClosedPubSection.lean",
            "must declare `public section`"
        ),
        "{v:#?}"
    );
    for bad_path in [
        "CaseStudies/Alpha/Theorems/Testing/BadTestingPath.lean",
        "CaseStudies/Alpha/Theorems/Fixtures.lean",
        "CaseStudies/Alpha/Theorems/_HiddenMod.lean",
    ] {
        assert!(
            has(
                &v,
                bad_path,
                "may not contain `Testing`, `Fixtures`, or `_`-prefixed path components"
            ),
            "{bad_path}: {v:#?}"
        );
    }
    assert!(
        has(
            &v,
            "CaseStudies/Alpha/Theorems/UnderscoreNames.lean",
            "`namespace _Internal` uses `_`-prefixed internal name"
        ),
        "{v:#?}"
    );
    assert!(
        has(
            &v,
            "CaseStudies/Alpha/Theorems/UnderscoreNames.lean",
            "`theorem _hidden_ok` uses `_`-prefixed internal name"
        ),
        "{v:#?}"
    );
}

#[test]
fn fixture_modules() {
    assert_eq!(
        classify("ProofLib.Testing.AxiomAudit.Fixtures").map(|c| c.role),
        Some(Role::Fixture)
    );
    assert_eq!(
        classify("ProofLib.Testing.Fixtures").map(|c| c.role),
        Some(Role::Test)
    );
    assert_eq!(classify("Testing.A.Fixtures"), None);
    let v = check(&[
        (
            "ProofLib/Testing/AxiomAudit/Fixtures.lean",
            "axiom ax : False\ntheorem s : False := sorry\ntheorem n : True := by native_decide\n",
        ),
        (
            "ProofLib/Testing/AxiomAudit.lean",
            "import ProofLib.Testing.AxiomAudit.Fixtures\n",
        ),
        (
            "ProofLib/Testing/Other.lean",
            "import ProofLib.Testing.AxiomAudit.Fixtures\n",
        ),
        (
            "ProofLib/Testing/Other/Fixtures.lean",
            "unsafe def u : Nat := 0\n",
        ),
    ]);
    assert!(
        !v.iter()
            .any(|x| x.path == "ProofLib/Testing/AxiomAudit/Fixtures.lean"
                || x.path == "ProofLib/Testing/AxiomAudit.lean"),
        "{v:#?}"
    );
    assert!(
        has(
            &v,
            "ProofLib/Testing/Other.lean",
            "may only be imported by `ProofLib.Testing.AxiomAudit`"
        ),
        "{v:#?}"
    );
    assert!(
        has(&v, "ProofLib/Testing/Other/Fixtures.lean", "unsafe"),
        "{v:#?}"
    );
}

#[test]
fn package_passes() {
    let root = std::path::PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("../..");
    let ws = Workspace::load(&root).unwrap();
    assert!(
        ws.modules.len() > 50,
        "expected the arm64-semantics modules"
    );
    let v = ws.check_all();
    assert!(v.is_empty(), "trust guard violations:\n{v:#?}");
    let tree = ws.trust_tree().unwrap();
    assert!(
        tree.violations.is_empty(),
        "unclassified repository paths:\n{:#?}",
        tree.violations
    );
    let rendered = tree.render();
    assert!(
        rendered.contains("Arm64/")
            && rendered.contains("[mixed: tcb + proof + testing + infra + doc]")
            && rendered.contains("Arm64/Legacy/"),
        "{rendered}"
    );
    assert!(
        rendered.contains("Arm64/Trusted/") && rendered.contains("[mixed: tcb + doc]"),
        "{rendered}"
    );
    assert!(
        rendered.contains("Arm64/Testing/") && rendered.contains("[mixed: testing + infra + doc]"),
        "{rendered}"
    );
    assert!(
        rendered.contains("CaseStudies/")
            && rendered.contains("[mixed: case-studies-tcb + proof + testing + infra + doc]"),
        "{rendered}"
    );
    assert!(!rendered.contains("Examples/"), "{rendered}");
    assert!(
        rendered.contains("tools/rust-obj2lean/src/")
            && rendered.contains("tools/rust-obj2lean/src/trusted_common/")
            && rendered.contains("tools/rust-obj2lean/src/untrusted_lemmas/")
            && rendered.contains("tools/rust-obj2lean/src/test_infra/"),
        "{rendered}"
    );
}

#[test]
fn compiler_trust_identifiers() {
    let v = check(&[
        (
            "ProofLib/Tac.lean",
            "def mk : MetaM Expr := pure (mkConst ``Lean.ofReduceBool)\n\
             def mk2 : MetaM Expr := pure (mkConst ``trustCompiler)\n\
             -- comment mentioning ofReduceNat is fine\n",
        ),
        (
            "ProofLib/Testing/AxiomAudit/Core.lean",
            "def kind (ax : Name) : Bool := ax == ``Lean.ofReduceBool || ax == ``Lean.trustCompiler\n",
        ),
    ]);
    assert!(
        has(
            &v,
            "ProofLib/Tac.lean",
            "Lean.ofReduceBool (trusts the compiler"
        ),
        "{v:#?}"
    );
    assert!(
        has(
            &v,
            "ProofLib/Tac.lean",
            "trustCompiler (trusts the compiler"
        ),
        "{v:#?}"
    );
    assert!(!has(&v, "ProofLib/Tac.lean", "ofReduceNat"), "{v:#?}");
    assert!(
        !has(&v, "ProofLib/Testing/AxiomAudit/Core.lean", "trusts the compiler"),
        "{v:#?}"
    );
}

#[test]
fn decide_native_rejected() {
    let v = check(&[
        ("CaseStudies/Alpha/Spec.lean", "def x : Nat := 0\n"),
        (
            "CaseStudies/Alpha.lean",
            "import CaseStudies.Alpha.Spec\n\
             theorem t1 : True := by decide +native\n",
        ),
    ]);
    assert!(
        has(
            &v,
            "CaseStudies/Alpha.lean",
            "decide +native (trusts the compiler)"
        ),
        "{v:#?}"
    );
}

#[test]
fn trust_category_classification() {
    use crate::policy::{TrustCategory::*, classify_path};

    let cases = [
        // Core engine TCB
        ("Arm64.lean", Some(Tcb)),
        ("Arm64/Trusted/ISA/Decode.lean", Some(Tcb)),
        ("Arm64/Trusted/Object/Labels.lean", Some(Tcb)),
        ("Arm64/Trusted/Spec/AsciiNum.lean", Some(Tcb)),
        ("Arm64/Trusted/Surface/Abi.lean", Some(Tcb)),
        ("Arm64/Trusted/Surface/Ascii.lean", Some(Tcb)),
        ("Arm64/Trusted/Surface/CType.lean", Some(Tcb)),
        ("tools/rust-obj2lean/src/trusted_common/mod.rs", Some(Tcb)),
        ("tools/rust-obj2lean/src/trusted_extractor/mod.rs", Some(Tcb)),
        ("tools/rust-obj2lean/src/trusted_extractor/extracted_obj.rs", Some(Tcb)),
        ("tools/rust-obj2lean/src/untrusted_legacy_linker/mod.rs", Some(Proof)),
        ("tools/rust-obj2lean/src/lib.rs", Some(Tcb)),
        ("tools/arm64-verification-engine/src/lib.rs", None),
        ("tools/proc-snapshot/src/untrusted_foo.rs", Some(Infra)),
        ("tools/snapshot-link/src/main.rs", Some(Infra)),
        ("tools/proc-snapshot/src/main.rs", Some(Infra)),
        ("tools/proc-snapshot/tests/snapshot.rs", Some(Testing)),
        // Case-study TCB
        ("tools/proc-snapshot/src/rsp.rs", Some(CaseStudiesTcb)),
        ("VerifiedLibraries/Common/Spec/Sha512.lean", Some(CaseStudiesTcb)),
        ("CaseStudies/Widget/Spec.lean", Some(CaseStudiesTcb)),
        ("CaseStudies/Widget/Spec/Model.lean", Some(CaseStudiesTcb)),
        ("CaseStudies/Widget/Generated/WidgetPlacedObj.bin", Some(CaseStudiesTcb)),
        ("CaseStudies/Widget/Generated/WidgetPlacedObj.lean", Some(CaseStudiesTcb)),
        ("CaseStudies/Widget/Generated/WidgetExtractedObj.bin", Some(CaseStudiesTcb)),
        ("CaseStudies/Widget/Generated/WidgetExtractedObj.lean", Some(CaseStudiesTcb)),
        ("CaseStudies/Widget/Generated/WidgetElfObj.lean", Some(CaseStudiesTcb)),
        ("CaseStudies/Widget/Generated/WidgetPlacedObjShard1.lean", Some(CaseStudiesTcb)),
        ("CaseStudies/Widget/Theorems.lean", Some(CaseStudiesTcb)),
        ("CaseStudies/Widget/Theorems/Top.lean", Some(CaseStudiesTcb)),
        ("CaseStudies/Widget/Implementation/translation.toml", Some(CaseStudiesTcb)),
        ("CaseStudies/Widget/Implementation/csrc/client_suite.c", Some(CaseStudiesTcb)),
        ("CaseStudies/Widget/Implementation/tests/harness.c", Some(CaseStudiesTcb)),
        ("CaseStudies/Widget/Implementation/tests/harness.h", Some(CaseStudiesTcb)),
        ("VerifiedLibraries/Widget/Implementation/src/tests/helper.c", Some(CaseStudiesTcb)),
        ("third_party/widget-1.0/widget.c", Some(CaseStudiesTcb)),
        // Testing
        ("Arm64/Testing/UnitTests.lean", Some(Testing)),
        ("ProofLib/Testing/SpecAudit.lean", Some(Testing)),
        ("ProofLib/Testing/LabelsCoverage.lean", Some(Testing)),
        ("CaseStudies/Widget/Testing/Audit.lean", Some(Testing)),
        ("CaseStudies/Widget/Testing/unit_tests_main.c", Some(Testing)),
        ("CaseStudies/Widget/Testing/run-widget-unit-tests.sh", Some(Testing)),
        ("CaseStudies/Widget/Implementation/src/tests.rs", Some(Testing)),
        ("CaseStudies/Widget/Implementation/tests/integration.rs", Some(Testing)),
        ("tools/isa-oracle/src/lib.rs", Some(Testing)),
        ("tools/isa-oracle/Cargo.toml", Some(Testing)),
        ("tools/run-trusted-tests/src/main.rs", Some(Testing)),
        ("tools/run-trusted-tests/Cargo.toml", Some(Testing)),
        ("tools/sail-aarch64/src/lib.rs", Some(Testing)),
        ("tools/sail-aarch64/Cargo.toml", Some(Testing)),
        ("tools/unicorn-aarch64/src/lib.rs", Some(Testing)),
        ("tools/unicorn-aarch64/Cargo.toml", Some(Testing)),
        ("tools/tcb-map/src/lib.rs", Some(Testing)),
        ("tools/tcb-map/Cargo.toml", Some(Testing)),
        ("tools/rust-obj2lean/src/test_infra/placed_lld_diff.rs", Some(Testing)),
        ("tools/rust-obj2lean/src/tests.rs", Some(Testing)),
        ("tools/rust-obj2lean/src/untrusted_legacy_linker/tests.rs", Some(Testing)),
        ("tools/rust-obj2lean/src/trusted_common/reloc_tests.rs", Some(Testing)),
        ("tools/rust-obj2lean/src/trusted_extractor/test_util.rs", Some(Testing)),
        ("tools/rust-obj2lean/src/trusted_common/attestation.rs", Some(Tcb)),
        ("tools/rust-obj2lean/src/trusted_common/testsuite.rs", Some(Tcb)),
        ("scripts/tcb-map", Some(Testing)),
        ("scripts/dev/check-trust-guards.sh", Some(Testing)),
        ("ProofLib/TrustedClosure.lean", Some(Testing)),
        // Proof
        ("Arm64/Legacy.lean", Some(Proof)),
        ("Arm64/Legacy/Object/LinkedImage.lean", Some(Proof)),
        ("Arm64/Legacy/Spec/Library.lean", Some(Proof)),
        ("ProofLib.lean", Some(Proof)),
        ("ProofLib/Placed/LabelsCheck.lean", Some(Proof)),
        ("ProofLib/Placed/LabelsCoverage.lean", Some(Proof)),
        ("ProofLib/SepLogic/WP.lean", Some(Proof)),
        ("VerifiedLibraries/Common.lean", Some(Proof)),
        ("CaseStudies/Widget.lean", Some(Proof)),
        ("CaseStudies/Widget/Proofs/ParseProof.lean", Some(Proof)),
        ("CaseStudies/Widget/Proofs/ParseSym.lean", Some(Proof)),
        ("CaseStudies/Widget/Witness/ParseWitness.lean", Some(Proof)),
        ("CaseStudies/Widget/Generated/WidgetObj.lean", Some(Proof)),
        ("CaseStudies/Widget/Generated/WidgetObj.code.bin", Some(Proof)),
        ("CaseStudies/Widget/Generated/WidgetObj.data.bin", Some(Proof)),
        ("CaseStudies/Widget/Generated/WidgetCode.lean", Some(Proof)),
        ("CaseStudies/Widget/Generated/WidgetElfFacts.lean", Some(Proof)),
        ("tools/rust-obj2lean/src/untrusted_lemmas/mod.rs", Some(Proof)),
        // Infra
        ("tools/dev/repo-common/src/discovery.rs", Some(Infra)),
        ("tools/rust-obj2lean/src/untrusted_placed/facts.rs", Some(Infra)),
        ("tools/dev/arm-asl-extract/src/lib.rs", Some(Infra)),
        ("tools/dev/repo-lints/src/lib.rs", Some(Infra)),
        ("tools/dev/repo-lints/Cargo.toml", Some(Infra)),
        ("tools/dev/ci-tools/src/main.rs", Some(Infra)),
        ("tools/dev/spec-oracle/src/lib.rs", Some(Infra)),
        ("tools/rust-obj2lean/src/main.rs", Some(Infra)),
        ("tools/rust-obj2lean/src/untrusted_driver/mod.rs", Some(Infra)),
        ("tools/rust-obj2lean/src/untrusted_driver/pipeline.rs", Some(Infra)),
        ("lakefile.lean", Some(Infra)),
        (".githooks/pre-push", Some(Infra)),
        ("lake-manifest.json", Some(Infra)),
        ("Arm64/lakefile.toml", Some(Infra)),
        ("Arm64/lake-manifest.json", Some(Infra)),
        ("Arm64/Testing/lakefile.lean", Some(Infra)),
        ("Arm64/Testing/lake-manifest.json", Some(Infra)),
        ("ProofLib/lakefile.toml", Some(Infra)),
        ("ProofLib/lake-manifest.json", Some(Infra)),
        ("CaseStudies/Widget/lakefile.lean", Some(Infra)),
        ("CaseStudies/Widget/ci.toml", Some(Infra)),
        ("lean-toolchain", Some(Infra)),
        ("LICENSE", Some(Infra)),
        ("copy.bara.sky", Some(Infra)),
        (".github/workflows/ci.yml", Some(Infra)),
        ("scripts/fetch-upstream-sources.sh", Some(Infra)),
        ("scripts/dev/pre-push-check", Some(Infra)),
        ("scripts/ci/build-shard.sh", Some(Infra)),
        ("scripts/Scratch.lean", Some(Infra)),
        ("docs/scratch/Site1.lean", Some(Infra)),
        ("tools/rust-obj2lean/Cargo.toml", Some(Infra)),
        // Doc
        ("README.md", Some(Doc)),
        ("docs/guides/module-map.md", Some(Doc)),
        ("Arm64/Trusted/README.md", Some(Doc)),
        ("CaseStudies/Widget/Implementation/README.md", Some(Doc)),
        ("tools/rust-obj2lean/README.md", Some(Doc)),
        ("tools/tcb-map/README.md", Some(Doc)),
        // Unknown / fail-closed
        ("unknown_top_level/foo.txt", None),
        ("Specs/Abi.lean", None),
        ("Examples/UnitTests/Graph/Spec.lean", None),
        ("Theorems/Widget.lean", None),
        ("Implementation/widget/widget.c", None),
        ("tools/repo-common/Cargo.toml", None),
        ("CaseStudies/Widget/RandomHelper.lean", None),
        ("CaseStudies/Widget/Witnesses/Foo.lean", None),
        ("CaseStudies/Widget/stray.sh", None),
    ];
    for (path, expected) in cases {
        assert_eq!(classify_path(path), expected, "{path}");
    }
}

#[test]
fn trust_tree_mixed_and_homogeneous_leaves_and_json() {
    let report = tree::TreeReport::from_entries([
        ("Arm64/Trusted/ISA/Decode.lean".to_string(), 100),
        ("Arm64/Trusted/README.md".to_string(), 25),
        ("Arm64/Testing/UnitTests.lean".to_string(), 50),
        ("ProofLib/SepLogic/WP.lean".to_string(), 200),
        ("CaseStudies/Widget/Spec.lean".to_string(), 40),
        ("CaseStudies/Widget/Spec/Model.lean".to_string(), 60),
        (
            "CaseStudies/Widget/Proofs/ParseProof.lean".to_string(),
            300,
        ),
        ("CaseStudies/Widget/Testing/Audit.lean".to_string(), 30),
        ("tools/rust-obj2lean/src/lib.rs".to_string(), 40),
        ("tools/rust-obj2lean/src/main.rs".to_string(), 20),
        (
            "tools/rust-obj2lean/src/trusted_common/mod.rs".to_string(),
            80,
        ),
        (
            "tools/rust-obj2lean/src/untrusted_lemmas/mod.rs".to_string(),
            120,
        ),
        ("tools/rust-obj2lean/src/test_infra/lld.rs".to_string(), 70),
        ("tools/tcb-map/src/lib.rs".to_string(), 90),
    ]);
    assert!(report.violations.is_empty(), "{:#?}", report.violations);
    assert_eq!(
        report.root.subdirs["Arm64"].tag(),
        "[mixed: tcb + testing + doc]"
    );
    assert_eq!(
        report.root.subdirs["Arm64"].subdirs["Trusted"].tag(),
        "[mixed: tcb + doc]"
    );
    assert!(
        report.root.subdirs["Arm64"].subdirs["Trusted"].is_code_homogeneous()
    );
    assert_eq!(
        report.root.subdirs["Arm64"].subdirs["Testing"].tag(),
        "[testing]"
    );
    assert_eq!(report.root.subdirs["ProofLib"].tag(), "[proof]");
    assert_eq!(
        report.root.subdirs["CaseStudies"].tag(),
        "[mixed: case-studies-tcb + proof + testing]"
    );
    assert_eq!(
        report.root.subdirs["tools"].subdirs["rust-obj2lean"].subdirs["src"].tag(),
        "[mixed: tcb + proof + testing + infra]"
    );
    let rendered = report.render();
    assert!(
        rendered.contains("tools/rust-obj2lean/src/lib.rs") && rendered.contains("[infra]"),
        "{rendered}"
    );

    let json_str = report.to_json_pretty();
    let val: serde_json::Value = serde_json::from_str(&json_str).unwrap();
    assert_eq!(
        val["children"]["Arm64/"]["category"],
        "mixed: tcb + testing + doc"
    );
    assert_eq!(val["children"]["Arm64/"]["code_lines"], 175);
    assert_eq!(
        val["children"]["Arm64/"]["rollup"]["categories"],
        serde_json::json!(["tcb", "testing", "doc"])
    );
    assert_eq!(
        val["children"]["Arm64/"]["rollup"]["totals"]["code_lines"],
        175
    );
    assert_eq!(
        val["children"]["Arm64/"]["rollup"]["by_category"]["tcb"]["code_lines"],
        100
    );
    assert_eq!(
        val["children"]["Arm64/"]["rollup"]["by_category"]["testing"]["code_lines"],
        50
    );
    assert_eq!(
        val["children"]["Arm64/"]["rollup"]["by_category"]["doc"]["code_lines"],
        25
    );
    assert_eq!(
        val["children"]["Arm64/"]["children"]["Trusted/"]["category"],
        "mixed: tcb + doc"
    );
    assert_eq!(
        val["children"]["Arm64/"]["children"]["Trusted/"]["children"]["README.md"]["category"],
        "doc"
    );
    assert!(
        val["children"]["Arm64/"]["children"]["Trusted/"]["children"]["README.md"]
            .get("rollup")
            .is_none()
    );
}

#[test]
fn trust_tree_reports_unclassified_path() {
    let report = tree::TreeReport::from_entries([
        ("Arm64/Trusted/ISA/Decode.lean".to_string(), 10),
        ("mystery_dir/foo.txt".to_string(), 5),
    ]);
    assert_eq!(report.violations.len(), 1);
    assert_eq!(report.violations[0].path, "mystery_dir/foo.txt");
    assert_eq!(report.violations[0].rule, tree::RULE);
}

#[test]
fn tcb_rust_import_allows_module_declarations_and_external_crates() {
    use crate::tcb_rust_import::check_source;
    let ok = "//! Docs may mention `untrusted_lemmas::decode` and `repo_common::lean_scan`.\n\
              /// `crate::untrusted_driver::extract` feeds this. // and so does test_infra::x\n\
              #[cfg(test)]\n\
              mod test_infra;\n\
              pub mod trusted_common;\n\
              pub mod untrusted_driver;\n\
              pub mod untrusted_lemmas;\n\
              use object::read::elf::ElfFile64; // ELF parsing via the `object` crate\n\
              use crate::trusted_common::{ObjObject, RelocType};\n\
              use sha2::Sha256;\n\
              pub fn f(x: &ObjObject) -> usize { x.sections.len() }\n";
    let v = check_source("tools/rust-obj2lean/src/lib.rs", ok, &["repo_common", "spec_oracle"]);
    assert!(v.is_empty(), "{v:?}");
}

#[test]
fn tcb_rust_import_rejects_untrusted_modules_and_non_tcb_crates() {
    use crate::tcb_rust_import::{RULE, check_source};
    let bad = "use crate::untrusted_driver::{Cli, Toolchain};\n\
               use repo_common::discovery::walk_lean_files;\n\
               extern crate repo_common;\n\
               pub fn g() { let _ = super::untrusted_lemmas::code::func_ranges; }\n\
               pub fn h() { let _ = test_infra::placed_lld_diff::helper(); }\n\
               pub fn t1() { let _ = crate::tests::helper(); }\n\
               pub fn t2() { let _ = self::reloc_tests::helper(); }\n\
               pub fn ok() { let _ = repo_common_like::thing; }\n";
    let v = check_source(
        "tools/rust-obj2lean/src/trusted_extractor/mod.rs",
        bad,
        &["repo_common"],
    );
    assert_eq!(
        v.iter().map(|v| v.line).collect::<Vec<_>>(),
        vec![1, 2, 3, 4, 5, 6, 7],
        "{v:#?}"
    );
    assert!(v.iter().all(|v| v.rule == RULE));
    assert!(v[0].text.contains("untrusted_driver"), "{}", v[0].text);
    assert!(v[1].text.contains("repo_common"), "{}", v[1].text);
    assert!(v[4].text.contains("test_infra"), "{}", v[4].text);
    assert!(v[5].text.contains("tests"), "{}", v[5].text);
    assert!(v[6].text.contains("reloc_tests"), "{}", v[6].text);
}

#[test]
fn tcb_rust_import_workspace_crates_follow_classify_path() {
    use crate::tcb_rust_import::workspace_crates;
    let paths = [
        "tools/dev/repo-common/Cargo.toml".to_string(),
        "tools/rust-obj2lean/Cargo.toml".to_string(),
        "tools/proc-snapshot/Cargo.toml".to_string(),
        "tools/dev/spec-oracle/Cargo.toml".to_string(),
        "tools/Cargo.toml".to_string(),
        "tools/dev/Cargo.toml".to_string(),
        "CaseStudies/Widget/Implementation/Cargo.toml".to_string(),
    ];
    assert_eq!(
        workspace_crates(&paths),
        vec![
            ("proc_snapshot".to_string(), false),
            ("repo_common".to_string(), false),
            ("rust_obj2lean".to_string(), true),
            ("spec_oracle".to_string(), false),
        ]
    );
}

#[test]
fn tcb_rust_import_repo_is_clean() {
    let root = crate::discovery::default_repo_root();
    if !root.join("tools/rust-obj2lean/src/lib.rs").exists() {
        return;
    }
    let v = crate::tcb_rust_import::check(&root).unwrap();
    assert!(v.is_empty(), "{v:#?}");
}

#[test]
fn spec_allowlists_have_no_stale_entries() {
    assert!(
        crate::policy::SPEC_MACRO_SYNTAX_ALLOWLIST
            .windows(2)
            .all(|w| w[0] < w[1]),
        "SPEC_MACRO_SYNTAX_ALLOWLIST must be strictly sorted"
    );
    let root = crate::discovery::default_repo_root();
    let mut allowed_paths: Vec<String> = crate::policy::SPEC_MACRO_SYNTAX_ALLOWLIST
        .iter()
        .map(|s| (*s).to_string())
        .collect();
    for entry in fs::read_dir(root.join("Arm64/Trusted/Surface")).unwrap() {
        let entry = entry.unwrap();
        let name = entry.file_name().to_string_lossy().to_string();
        if name.ends_with(".lean") {
            allowed_paths.push(format!("Arm64/Trusted/Surface/{name}"));
        }
    }
    for path in allowed_paths {
        let full = root.join(&path);
        assert!(
            full.exists(),
            "stale allowlist entry `{path}`: file does not exist; remove it from SPEC_MACRO_SYNTAX_ALLOWLIST"
        );
        let code = strip_comments_and_strings(&fs::read_to_string(&full).unwrap());
        let has_spec_line_rule = crate::policy::LINE_RULES
            .iter()
            .filter(|r| matches!(r.scope, crate::policy::Scope::SpecNonSurface))
            .any(|r| code.lines().any(|line| r.pattern.is_match(line)));
        let has_spec_attr = crate::lex::declaration_attributes(&code)
            .iter()
            .any(|a| {
                let base = a.name.rsplit('.').next().unwrap_or(&a.name);
                crate::policy::SPEC_FORBIDDEN_ATTRIBUTES
                    .iter()
                    .any(|(n, _)| *n == a.name || *n == base)
            });
        assert!(
            has_spec_line_rule || has_spec_attr,
            "`{path}` is permitted to define macros/syntax/notations, so it must actually use one (move pure definitions to `Arm64/Trusted/Spec/` or remove stale `SPEC_MACRO_SYNTAX_ALLOWLIST` entries)"
        );
    }
    assert!(
        crate::policy::LEGACY_LINKED_IMAGE_IMPORTERS
            .windows(2)
            .all(|w| w[0] < w[1]),
        "LEGACY_LINKED_IMAGE_IMPORTERS must be strictly sorted"
    );
    for &mod_name in crate::policy::LEGACY_LINKED_IMAGE_IMPORTERS {
        let rel = format!("{}.lean", mod_name.replace('.', "/"));
        let full = root.join(&rel);
        assert!(
            full.exists(),
            "stale allowlist entry `{mod_name}` (`{rel}`): file does not exist; remove it from LEGACY_LINKED_IMAGE_IMPORTERS"
        );
        let source = fs::read_to_string(&full).unwrap();
        let code = strip_comments_and_strings(&source);
        let imports = crate::lex::extract_imports_from_str(&code, &source);
        assert!(
            imports.iter().any(|e| {
                e.imported == "Arm64.Legacy" || e.imported.starts_with("Arm64.Legacy.")
            }),
            "`{mod_name}` (`{rel}`) no longer directly imports `Arm64.Legacy*`; remove it from LEGACY_LINKED_IMAGE_IMPORTERS"
        );
    }
}

#[test]
fn surface_macro_exemption_is_direct_children_only() {
    use crate::policy::is_spec_macro_syntax_allowed;
    assert!(is_spec_macro_syntax_allowed("Arm64/Trusted/Surface/Abi.lean"));
    assert!(is_spec_macro_syntax_allowed("Arm64/Trusted/Spec/SepLogic.lean"));
    // Nested files would escape the non-recursive self-audit above, so they are never exempt.
    assert!(!is_spec_macro_syntax_allowed("Arm64/Trusted/Surface/Sub/X.lean"));
    assert!(!is_spec_macro_syntax_allowed("Arm64/Trusted/Surface/"));
    assert!(!is_spec_macro_syntax_allowed("Arm64/Trusted/Surface/README.md"));
    assert!(!is_spec_macro_syntax_allowed("Arm64/Trusted/Spec/Hoare.lean"));
    assert!(!is_spec_macro_syntax_allowed("CaseStudies/Alpha/Spec/Surface/X.lean"));
    // The real tree has no nested `Surface/` directories (keep it that way).
    let root = crate::discovery::default_repo_root();
    for entry in fs::read_dir(root.join("Arm64/Trusted/Surface")).unwrap() {
        let entry = entry.unwrap();
        assert!(
            !entry.file_type().unwrap().is_dir(),
            "`Arm64/Trusted/Surface/{}` is a directory; surface macro modules must be direct children",
            entry.file_name().to_string_lossy()
        );
    }
}

fn is_lean_letter_like(c: char) -> bool {
    let u = c as u32;
    c.is_ascii_alphabetic()
        || (0x03b1..=0x03c9).contains(&u) && u != 0x03bb
        || (0x0391..=0x03a9).contains(&u) && u != 0x03a0 && u != 0x03a3
        || (0x03ca..=0x03fb).contains(&u)
        || (0x1f00..=0x1ffe).contains(&u)
        || (0x2100..=0x214f).contains(&u)
        || (0x1d49c..=0x1d59f).contains(&u)
        || (0x00c0..=0x00ff).contains(&u) && u != 0x00d7 && u != 0x00f7
        || (0x0100..=0x017f).contains(&u)
}

fn is_lean_subscript_alnum(c: char) -> bool {
    let u = c as u32;
    (0x2080..=0x2089).contains(&u)
        || (0x2090..=0x209c).contains(&u)
        || (0x1d62..=0x1d6a).contains(&u)
        || u == 0x2c7c
}

fn is_ident_continue(c: char) -> bool {
    is_lean_letter_like(c)
        || c.is_ascii_digit()
        || matches!(c, '_' | '\'' | '!' | '?')
        || is_lean_subscript_alnum(c)
}

fn is_ident_start(c: char) -> bool {
    is_lean_letter_like(c) || c == '_'
}

#[test]
fn spec_modules_reject_macro_syntax_elab_and_notation_extensions() {
    let lean_id_first_re =
        regex::Regex::new(&format!("^[{}]$", crate::policy::LEAN_ID_FIRST)).unwrap();
    let lean_id_non_first_re =
        regex::Regex::new(&format!("^[{}]$", crate::policy::LEAN_ID_NON_FIRST)).unwrap();
    let lean_id_re =
        regex::Regex::new(&format!("^[{}]$", crate::policy::LEAN_ID_REST)).unwrap();
    for cp in 0u32..=0x10ffff {
        let Some(c) = char::from_u32(cp) else {
            continue;
        };
        let mut buf = [0u8; 4];
        let s = c.encode_utf8(&mut buf);
        let is_first = is_ident_start(c);
        let is_cont = is_ident_continue(c);
        assert_eq!(
            lean_id_first_re.is_match(s),
            is_first,
            "LEAN_ID_FIRST vs is_ident_start mismatch at U+{cp:04X} ({c:?})"
        );
        assert_eq!(
            lean_id_non_first_re.is_match(s),
            is_cont && !is_first,
            "LEAN_ID_NON_FIRST vs (is_ident_continue && !is_ident_start) mismatch at U+{cp:04X} ({c:?})"
        );
        assert_eq!(
            lean_id_re.is_match(s),
            is_cont,
            "LEAN_ID_REST vs is_ident_continue mismatch at U+{cp:04X} ({c:?})"
        );
    }

    let v = check(&[
        ("Arm64.lean", "def Base := Nat\n"),
        (
            "Arm64/Trusted/Surface/Abi.lean",
            "import Arm64\nsyntax \"c_spec\" : command\nmacro_rules | `(c_spec) => `(command| )\n",
        ),
        (
            "Arm64/Trusted/ISA/Float.lean",
            "import Init.Data.BitVec\n\
             def bvInt (intWidth : Nat) : BitVec intWidth := 0#(intWidth)\n\
             def bvFmt (w : Nat) : BitVec w := 0#(fmt.width)\n",
        ),
        (
            "CaseStudies/Beta/Spec.lean",
            "import Arm64\n\
             def prefixSum := 0\n\
             def notationHelper := 0\n\
             def αmacro_rules := 0\n\
             def ℮macro_rules := 0\n\
             def ℘notation := 1\n\
             def énotation := 1\n\
             def ŝmacro := 1\n\
             def xⱼnotation := 1\n\
             def x1notation := 0\n\
             def épartial := 0\n\
             def g := Lean.Syntax.missing\n\
             def vecConst := #v[1, 2, 3]\n\
             def bvConst := 0#64\n\
             def bvParen (w : Nat) : BitVec (w + 1) := 0#(w + 1)\n\
             def bvParen1 (w : Nat) : BitVec w := 1#(w)\n",
        ),
        (
            "CaseStudies/Alpha/Spec.lean",
            "import Arm64\n\
             macro_rules | `(Memory) => `(False)\n\
             local notation \"Memory\" => False\n\
             syntax \"bad_syn\" : term\n\
             macro \"bad_mac\" : term => `(True)\n\
             elab \"bad_elab\" : term => sorry\n\
             infixl:65 \" +++ \" => Nat.add\n\
             prefix:100 \"!!\" => Not\n\
             postfix:100 \"!?\" => id\n\
             namespace X macro_rules | `(ElfSafe) => `(True) end X\n\
             namespace Y notation \"ElfSafe\" => True end Y\n\
             run_cmd Lean.Elab.Command.elabCommand (← `(def x := 1))\n\
             run_elab pure ()\n\
             run_meta pure ()\n\
             run_tac pure ()\n\
             notation3 \"Memory\" => False\n\
             binder_predicate x \" ≺ \" y:term => `(True)\n\
             declare_simp_like_tactic my_simp `my_simp_attr\n\
             register_simp_attr my_simp_attr\n\
             register_option my_opt : Bool := { defValue := false }\n\
             declare_config_elab elabMyCfg MyCfg\n\
             unif_hint (x : Nat) where |- x =?= x\n\
             simproc my_simproc (_) := fun _ => pure .continue\n\
             builtin_simproc my_bsimproc (_) := fun _ => pure .continue\n\
             dsimproc my_dsimproc (_) := fun _ => pure .continue\n\
             builtin_dsimproc my_bdsimproc (_) := fun _ => pure .continue\n\
             #eval 1 + 1\n\
             def e1 := (0)#eval 1\n\
             def e2 := 0;#eval 1\n\
             #exit\n\
             @[term_elab ident] def myTermElab : Nat := 0\n\
             @[«term_elab» ident] def myQuotedTermElab : Nat := 0\n\
             @[command_elab] def myCmdElab : Nat := 0\n\
             @[tactic] def myTacElab : Nat := 0\n\
             @[macro] def myMacroElab : Nat := 0\n\
             attribute [term_elab ident] myTermElab\n\
             attribute[term_elab ident] myQuotedTermElab\n",
        ),
        (
            "CaseStudies/Alpha/Spec/UnicodeBinders.lean",
            "import Arm64\n\
             notation \"ElfSafe\" α:max β:max => (fun (_ _ : Nat) => True) α β\n\
             macro \"ElfSafe\" α:term:max β:term:max : term => `((fun (_ _ : Nat) => True) $α $β)\n\
             elab \"ElfSafe\" α:term : term => return Lean.mkConst ``True\n\
             notation α \" ⊕⊕ \" β => True\n\
             notation \"ElfSafe\" ℓ₁:max ℓ₂:max => (fun (_ _ : Nat) => True) ℓ₁ ℓ₂\n\
             notation \"ElfSafe\" «a»:max «b»:max => (fun (_ _ : Nat) => True) «a» «b>\n\
             macro «x»:term \" +++ \" «y»:term : term => `(True)\n\
             notation\n\
               \"ElfSafe\" α:max β:max => (fun (_ _ : Nat) => True) α β\n\
             macro\n\
               \"ElfSafe\" α:term:max β:term:max : term => `((fun (_ _ : Nat) => True) $α $β)\n\
             namespace X notation\n\
               \"ElfSafe\" α:max β:max => True\n\
             end X\n",
        ),
        (
            "CaseStudies/Alpha/Spec/Multiline.lean",
            "import Arm64\n\
             notation\n\
               \"ElfSafe\" a:max b:max => (fun (_ _ : Nat) => True) a b\n\
             macro\n\
               \"ElfSafe\" a:term:max b:term:max : term => `((fun (_ _ : Nat) => True) $a $b)\n\
             syntax\n\
               \"ElfSafe\" term:max term:max : term\n\
             elab\n\
               \"ElfSafe\" : term => return Lean.mkConst ``True\n\
             infix\n\
               :50 \" ≺ \" => Nat.lt\n",
        ),
        (
            "CaseStudies/Beta/Proofs/X.lean",
            "import Arm64\ndef p := 0\n",
        ),
        (
            "CaseStudies/Alpha/Spec/MultiImport.lean",
            "import Arm64 import CaseStudies.Beta.Proofs.X\ndef m := 0\n",
        ),
        (
            "CaseStudies/Alpha/Spec/PreludeImport.lean",
            "prelude import CaseStudies.Beta.Proofs.X\ndef m2 := 0\n",
        ),
    ]);
    assert!(
        !v.iter().any(|x| x.path == "Arm64/Trusted/Surface/Abi.lean"),
        "expected Surface/Abi.lean to pass: {v:#?}"
    );
    assert!(
        !v.iter().any(|x| x.path == "Arm64/Trusted/ISA/Float.lean"),
        "expected `0#(intWidth)` and `0#(fmt.width)` in Float.lean to pass: {v:#?}"
    );
    assert!(
        !v.iter().any(|x| x.path == "CaseStudies/Beta/Spec.lean"),
        "expected valid Lean identifiers with keyword substrings and `#v[...]` in Beta/Spec.lean to pass: {v:#?}"
    );
    for kw in [
        "`macro_rules` in Spec module",
        "`notation` in Spec module",
        "`notation3` in Spec module",
        "`binder_predicate` in Spec module",
        "`declare_simp_like_tactic` in Spec module",
        "`register_simp_attr` in Spec module",
        "`register_option` in Spec module",
        "`declare_config_elab` in Spec module",
        "`unif_hint` in Spec module",
        "`simproc` in Spec module",
        "`builtin_simproc` in Spec module",
        "`dsimproc` in Spec module",
        "`builtin_dsimproc` in Spec module",
        "`syntax` in Spec module",
        "`macro` in Spec module",
        "`elab` in Spec module",
        "`infixl` in Spec module",
        "`prefix` in Spec module",
        "`postfix` in Spec module",
        "`run_cmd` in Spec module",
        "`run_elab` in Spec module",
        "`run_meta` in Spec module",
        "`run_tac` in Spec module",
        "`#eval` command in Spec module",
        "`#exit` command in Spec module",
        "@[term_elab] in Spec module",
        "@[command_elab] in Spec module",
        "@[tactic] in Spec module",
        "@[macro] in Spec module",
    ] {
        assert!(
            has(&v, "CaseStudies/Alpha/Spec.lean", kw),
            "expected `{kw}` violation in Alpha/Spec.lean, got {v:#?}"
        );
    }
    assert_eq!(
        v.iter()
            .filter(|x| x.path == "CaseStudies/Alpha/Spec.lean"
                && x.rule.contains("@[term_elab] in Spec module"))
            .count(),
        4,
        "expected `@[term_elab]`, `@[«term_elab»]`, `attribute [term_elab]`, and `attribute[term_elab]` to be flagged: {v:#?}"
    );
    for kw in [
        "`notation` in Spec module",
        "`macro` in Spec module",
        "`syntax` in Spec module",
        "`elab` in Spec module",
        "`infix` in Spec module",
    ] {
        assert!(
            has(&v, "CaseStudies/Alpha/Spec/Multiline.lean", kw),
            "expected multiline `{kw}` violation in Alpha/Spec/Multiline.lean, got {v:#?}"
        );
    }
    let unicode_hits: Vec<_> = v
        .iter()
        .filter(|x| x.path == "CaseStudies/Alpha/Spec/UnicodeBinders.lean")
        .collect();
    for line in [2, 3, 4, 5, 6, 7, 8, 9, 11, 13] {
        assert!(
            unicode_hits.iter().any(|x| x.line == line),
            "expected Unicode/guillemet binder violation at line {line} in Alpha/Spec/UnicodeBinders.lean, got {unicode_hits:#?}"
        );
    }
    for imp_spec in [
        "CaseStudies/Alpha/Spec/MultiImport.lean",
        "CaseStudies/Alpha/Spec/PreludeImport.lean",
    ] {
        assert!(
            has(&v, imp_spec, "may only import Spec modules, not `CaseStudies.Beta.Proofs.X`"),
            "expected `{imp_spec}` to flag Proofs import: {v:#?}"
        );
    }
}

#[test]
fn package_isolation_and_standalone_case_study_classification() {
    let ws = Workspace::from_sources([
        ("Arm64.lean", "def a := 1\n"),
        (
            "CaseStudies/Alpha/Spec.lean",
            "import Arm64\ndef spec := 1\n",
        ),
        (
            "CaseStudies/Alpha/Proofs/Core.lean",
            "import CaseStudies.Alpha.Spec\ntheorem t : True := trivial\n",
        ),
        (
            "CaseStudies/Alpha/Proofs/CrossPkg.lean",
            "import CaseStudies.Beta.Spec\ntheorem t2 : True := trivial\n",
        ),
        (
            "CaseStudies/Beta/Spec.lean",
            "import Arm64\ndef betaSpec := 1\n",
        ),
    ])
    .unwrap();
    let v = ws.check_all();
    assert!(
        v.iter().any(|x| x.path == "CaseStudies/Alpha/Proofs/CrossPkg.lean"
            && x.rule.starts_with("package-isolation")),
        "{v:#?}"
    );

    let ws_vl = Workspace::from_sources([
        ("Arm64.lean", "def a := 1\n"),
        (
            "CaseStudies/Alpha/Spec.lean",
            "import Arm64\ndef spec := 1\n",
        ),
        (
            "VerifiedLibraries/Widget/Theorems/Top.lean",
            "module\npublic import CaseStudies.Alpha.Spec\n@[expose] public section\ntheorem t : True := trivial\nend\n",
        ),
        (
            "VerifiedLibraries/Widget/Testing/SpecAudit.lean",
            "import CaseStudies.Alpha.Spec\ntheorem test_ok : True := trivial\n",
        ),
    ])
    .unwrap();
    let v_vl = ws_vl.check_imports();
    assert!(
        v_vl.iter()
            .any(|x| x.path == "VerifiedLibraries/Widget/Theorems/Top.lean"
                && x.rule.starts_with("package-isolation:")),
        "{v_vl:#?}"
    );
    assert!(
        v_vl.iter()
            .any(|x| x.path == "VerifiedLibraries/Widget/Testing/SpecAudit.lean"
                && x.rule.starts_with("package-isolation:")),
        "{v_vl:#?}"
    );
}

fn isolation_paths(v: &[Violation]) -> BTreeSet<String> {
    v.iter()
        .filter(|x| x.rule.starts_with("package-isolation:"))
        .map(|x| format!("{}:{}", x.path, x.line))
        .collect()
}

#[test]
fn sibling_case_studies_forbidden_and_verified_libraries_layered() {
    let sources = [
        ("Arm64.lean", "def a := 1\n"),
        (
            "VerifiedLibraries/Gamma.lean",
            "import VerifiedLibraries.Gamma.Spec\ndef gu := 1\n",
        ),
        ("VerifiedLibraries/Gamma/Spec.lean", "import Arm64\ndef gs := 1\n"),
        (
            "VerifiedLibraries/Gamma/Proofs/Core.lean",
            "import Arm64\ntheorem gp : True := trivial\n",
        ),
        (
            "VerifiedLibraries/Common/Spec/Math.lean",
            "import Arm64\ndef cm := 1\n",
        ),
        ("CaseStudies/Beta.lean", "import CaseStudies.Beta.Spec\ndef bu := 1\n"),
        ("CaseStudies/Beta/Spec.lean", "import Arm64\ndef b := 1\n"),
        (
            "CaseStudies/Alpha/Spec.lean",
            "import VerifiedLibraries.Gamma.Spec\nimport VerifiedLibraries.Common.Spec.Math\nimport CaseStudies.Beta.Spec\ndef aspec := b\n",
        ),
        (
            "CaseStudies/Alpha/Proofs/Core.lean",
            "import CaseStudies.Alpha.Spec\nimport VerifiedLibraries.Gamma\nimport VerifiedLibraries.Gamma.Proofs.Core\nimport CaseStudies.Beta\ntheorem at1 : True := trivial\n",
        ),
        (
            "CaseStudies/Alpha/Testing/Smoke.lean",
            "import VerifiedLibraries.Gamma\nimport CaseStudies.Beta.Spec\ndef t := b\n",
        ),
    ];

    // VerifiedLibraries (including VerifiedLibraries.Common.Spec.*) imports pass cleanly, while
    // all sibling `CaseStudies.Beta*` imports fail `package-isolation`.
    let v = Workspace::from_sources(sources).unwrap().check_imports();
    assert_eq!(
        isolation_paths(&v),
        BTreeSet::from([
            "CaseStudies/Alpha/Proofs/Core.lean:4".to_string(),
            "CaseStudies/Alpha/Spec.lean:3".to_string(),
            "CaseStudies/Alpha/Testing/Smoke.lean:2".to_string(),
        ]),
        "{v:#?}"
    );

    // Even a hypothetical `CaseStudies/Common/Spec/Math.lean` has zero sibling exception:
    // `CaseStudies` packages are strictly pairwise independent.
    let no_common_exception = Workspace::from_sources([
        ("Arm64.lean", "def a := 1\n"),
        ("CaseStudies/Common/Spec/Math.lean", "import Arm64\ndef cm := 1\n"),
        (
            "CaseStudies/Alpha/Spec.lean",
            "import CaseStudies.Common.Spec.Math\ndef aspec := cm\n",
        ),
    ])
    .unwrap()
    .check_imports();
    assert_eq!(
        isolation_paths(&no_common_exception),
        BTreeSet::from(["CaseStudies/Alpha/Spec.lean:1".to_string()]),
        "{no_common_exception:#?}"
    );

    // VerifiedLibraries may never import CaseStudies, and CaseStudies Spec may never import
    // VerifiedLibraries Proof.
    let bad_layering = Workspace::from_sources([
        ("Arm64.lean", "def a := 1\n"),
        ("CaseStudies/Alpha/Spec.lean", "import VerifiedLibraries.Gamma\ndef s := 1\n"),
        (
            "VerifiedLibraries/Gamma.lean",
            "import VerifiedLibraries.Gamma.Spec\nimport CaseStudies.Alpha.Spec\ndef g := 1\n",
        ),
        ("VerifiedLibraries/Gamma/Spec.lean", "import Arm64\ndef gs := 1\n"),
    ])
    .unwrap()
    .check_imports();
    assert!(
        bad_layering
            .iter()
            .any(|x| x.path == "CaseStudies/Alpha/Spec.lean" && x.rule.contains("may only import Spec")),
        "{bad_layering:#?}"
    );
    assert!(
        bad_layering
            .iter()
            .any(|x| x.path == "VerifiedLibraries/Gamma.lean" && x.rule.starts_with("layering:")),
        "{bad_layering:#?}"
    );
}

#[test]
fn core_tcb_closure_rejects_lean_std_and_surface_macro_imports() {
    let v = check(&[
        ("Arm64/Trusted/ISA/Syntax.lean", "import Init.Data.BitVec\ndef x := 0\n"),
        (
            "Arm64/Trusted/ISA/Semantics.lean",
            "import Arm64.Trusted.ISA.Syntax\nimport Lean.Elab.Term\n",
        ),
        (
            "Arm64/Trusted/Object/Placed.lean",
            "import Std.Tactic.BVDecide\ndef y := 0\n",
        ),
        (
            "Arm64/Trusted/Process/Semantics.lean",
            "import Arm64.Trusted.Process\ndef p := 0\n",
        ),
        (
            "Arm64/Trusted/Spec/Hoare.lean",
            "import Arm64.Trusted.Surface.HexCode\ndef z := 0\n",
        ),
        (
            "Arm64/Trusted/Surface/HexCode.lean",
            "import Lean.Elab.Term\nimport Arm64.Trusted.ISA.Syntax\n",
        ),
    ]);
    assert!(!v.iter().any(|x| x.path == "Arm64/Trusted/ISA/Syntax.lean"), "{v:#?}");
    assert!(!v.iter().any(|x| x.path == "Arm64/Trusted/Surface/HexCode.lean"), "{v:#?}");
    assert!(
        has(&v, "Arm64/Trusted/ISA/Semantics.lean", "core-tcb-init-only"),
        "{v:#?}"
    );
    assert!(
        has(&v, "Arm64/Trusted/Object/Placed.lean", "core-tcb-init-only"),
        "{v:#?}"
    );
    assert!(
        has(&v, "Arm64/Trusted/Process/Semantics.lean", "core-tcb-init-only"),
        "{v:#?}"
    );
    assert!(
        has(&v, "Arm64/Trusted/Spec/Hoare.lean", "core-tcb-init-only"),
        "{v:#?}"
    );
}

#[test]
fn trusted_tcb_directory_classification_fails_closed_on_unclassified_modules() {
    use crate::policy::{TrustedTcbTier, classify_trusted_tcb_module};

    let root = crate::discovery::default_repo_root();
    let live_ws = Workspace::load(&root).unwrap();
    for (name, m) in &live_ws.modules {
        if m.class.lib == Lib::Arm64 && m.class.role == Role::Spec {
            assert!(
                classify_trusted_tcb_module(name).is_some(),
                "live `Arm64` TCB module `{name}` (`{}`) must be classified",
                m.path
            );
        }
    }

    for core in [
        "Arm64.Trusted.ISA.Syntax",
        "Arm64.Trusted.Object.Placed",
        "Arm64.Trusted.Process.Types",
        "Arm64.Trusted.Syscalls",
        "Arm64.Trusted.Syscalls.Common",
        "Arm64.Trusted.Spec.AsciiNum",
        "Arm64.Trusted.Spec.RustHeap",
    ] {
        assert_eq!(
            classify_trusted_tcb_module(core),
            Some(TrustedTcbTier::CoreInitOnly),
            "{core}"
        );
    }
    for surface in [
        "Arm64",
        "Arm64.Trusted",
        "Arm64.Trusted.Process",
        "Arm64.Trusted.Surface.Abi",
        "Arm64.Trusted.Surface.Ascii",
        "Arm64.Trusted.Surface.CType",
        "Arm64.Trusted.Surface.FileBytes",
        "Arm64.Trusted.Surface.HexCode",
        "Arm64.Trusted.Surface.IncludeBytes",
    ] {
        assert_eq!(
            classify_trusted_tcb_module(surface),
            Some(TrustedTcbTier::SurfaceMacro),
            "{surface}"
        );
    }

    let v = check(&[
        ("Arm64/Trusted/ISA/NewIsa.lean", "import Init.Data.BitVec\ndef i := 0\n"),
        ("Arm64/Trusted/Object/NewObj.lean", "def o := 0\n"),
        ("Arm64/Trusted/Process/NewProc.lean", "def p := 0\n"),
        ("Arm64/Trusted/Surface/NewMacro.lean", "import Lean.Elab.Term\ndef m := 0\n"),
        ("Arm64/Trusted/Spec/NewSemanticSpec.lean", "import Lean.Elab.Term\ndef s := 0\n"),
        ("Arm64/NewRoot.lean", "def r := 0\n"),
        ("Arm64/Trusted/NewTop.lean", "def t := 0\n"),
        ("Arm64/Trusted/Surface.lean", "def u := 0\n"),
        ("Arm64/Trusted/Unknown/Foo.lean", "def f := 0\n"),
    ]);
    for ok in [
        "Arm64/Trusted/ISA/NewIsa.lean",
        "Arm64/Trusted/Object/NewObj.lean",
        "Arm64/Trusted/Process/NewProc.lean",
        "Arm64/Trusted/Surface/NewMacro.lean",
    ] {
        assert!(!v.iter().any(|x| x.path == ok), "expected `{ok}` to pass: {v:#?}");
    }
    assert!(
        has(
            &v,
            "Arm64/Trusted/Spec/NewSemanticSpec.lean",
            "core-tcb-init-only: semantic core module"
        ),
        "{v:#?}"
    );
    for unclassified in [
        "Arm64/NewRoot.lean",
        "Arm64/Trusted/NewTop.lean",
        "Arm64/Trusted/Surface.lean",
        "Arm64/Trusted/Unknown/Foo.lean",
    ] {
        assert!(
            has(&v, unclassified, "core-tcb-init-only: unclassified `Arm64` TCB module"),
            "expected `{unclassified}` to fail closed: {v:#?}"
        );
    }
}

#[test]
fn no_case_studies_excludes_case_study_paths_from_tree_and_totals() {
    use crate::policy::{TrustCategory, is_case_study_path};
    use crate::tree::{SizeMetrics, TreeReport};

    assert!(is_case_study_path("VerifiedLibraries.lean"));
    assert!(is_case_study_path("VerifiedLibraries/Common/Spec/CAlloc.lean"));
    assert!(is_case_study_path("CaseStudies/Alpha/Spec/Top.lean"));
    assert!(is_case_study_path("CaseStudies/Alpha/Theorems/Top.lean"));
    assert!(is_case_study_path("CaseStudies/Alpha/Implementation/src/lib.rs"));
    assert!(is_case_study_path("third_party/alpha/foo.c"));
    assert!(is_case_study_path("tools/proc-snapshot/src/lib.rs"));
    assert!(!is_case_study_path("Arm64/Trusted/ISA/Syntax.lean"));
    assert!(!is_case_study_path("ProofLib/SepLogic.lean"));
    assert!(!is_case_study_path("tools/rust-obj2lean/src/lib.rs"));

    let entries = vec![
        (
            "Arm64/Trusted/ISA/Syntax.lean".to_string(),
            SizeMetrics {
                files: 1,
                code_lines: 100,
            },
        ),
        (
            "ProofLib/SepLogic.lean".to_string(),
            SizeMetrics {
                files: 1,
                code_lines: 200,
            },
        ),
        (
            "VerifiedLibraries/Common/Spec/CAlloc.lean".to_string(),
            SizeMetrics {
                files: 1,
                code_lines: 50,
            },
        ),
        (
            "CaseStudies/Alpha/Spec/Top.lean".to_string(),
            SizeMetrics {
                files: 1,
                code_lines: 75,
            },
        ),
    ];
    let report = TreeReport::from_file_metrics_filtered(entries, true);
    assert!(report.violations.is_empty());
    assert_eq!(report.root.files, 2);
    assert_eq!(report.root.code_lines, 300);
    assert_eq!(
        report.totals.get(&TrustCategory::CaseStudiesTcb).copied().unwrap_or_default().files,
        0
    );
    let rendered = report.render();
    assert!(!rendered.contains("VerifiedLibraries/"), "{rendered}");
    assert!(!rendered.contains("CaseStudies/"), "{rendered}");
    assert!(!rendered.contains("[case-studies-tcb]"), "{rendered}");
    assert!(rendered.contains("Arm64/"), "{rendered}");
    assert!(rendered.contains("ProofLib/"), "{rendered}");
}

fn extract_convention_table<'a>(lines: impl Iterator<Item = &'a str>) -> String {
    let mut inside = false;
    let mut out = Vec::new();
    for line in lines {
        let trimmed = line.trim();
        if trimmed == "<!-- BEGIN CANONICAL CONVENTION TABLE -->" {
            inside = true;
            continue;
        }
        if trimmed == "<!-- END CANONICAL CONVENTION TABLE -->" {
            return out.join("\n");
        }
        if inside {
            out.push(line);
        }
    }
    panic!("missing CANONICAL CONVENTION TABLE markers");
}

#[test]
fn canonical_convention_table_in_readme_and_policy_matches_live_classifier() {
    use crate::policy::{
        TrustCategory, TrustedTcbTier, classify_path, classify_trusted_tcb_module,
    };

    let manifest = Path::new(env!("CARGO_MANIFEST_DIR"));
    let readme = fs::read_to_string(manifest.join("README.md")).unwrap();
    let policy_rs = fs::read_to_string(manifest.join("src/policy.rs")).unwrap();

    let readme_table = extract_convention_table(readme.lines());
    let policy_doc_lines: Vec<&str> = policy_rs
        .lines()
        .filter_map(|l| l.strip_prefix("//! ").or_else(|| l.strip_prefix("//!")))
        .collect();
    let policy_table = extract_convention_table(policy_doc_lines.into_iter());
    assert_eq!(
        readme_table, policy_table,
        "`tools/tcb-map/README.md` and `tools/tcb-map/src/policy.rs` convention tables drifted"
    );

    let data_rows: Vec<&str> = readme_table.lines().skip(2).collect();
    assert!(!data_rows.is_empty());
    for row in data_rows {
        let cells: Vec<&str> = row.trim().trim_matches('|').split('|').map(str::trim).collect();
        assert_eq!(cells.len(), 5, "expected 5 columns in row: {row}");
        let sample_path = cells[1].trim_matches('`');
        let expected_cat = match cells[2].trim_matches('`') {
            "tcb" => TrustCategory::Tcb,
            "case-studies-tcb" => TrustCategory::CaseStudiesTcb,
            "proof" => TrustCategory::Proof,
            "testing" => TrustCategory::Testing,
            "infra" => TrustCategory::Infra,
            "doc" => TrustCategory::Doc,
            other => panic!("unknown trust bucket `{other}` in row: {row}"),
        };
        assert_eq!(
            classify_path(sample_path),
            Some(expected_cat),
            "sample path `{sample_path}` in convention table disagreed with `classify_path`"
        );
        let role_cell = cells[3];
        if role_cell.trim_matches('`') == "-" {
            assert!(
                !sample_path.ends_with(".lean"),
                "Lean sample path `{sample_path}` must declare its `(Lib, Role)` in table"
            );
        } else {
            let mod_name = crate::discovery::module_name_of_path(sample_path);
            let cls = classify(&mod_name).unwrap_or_else(|| {
                panic!("sample Lean module `{mod_name}` (`{sample_path}`) returned `None`")
            });
            let (lib_role_raw, tier_raw) = match role_cell.split_once(' ') {
                Some((lr, t)) => (lr, Some(t)),
                None => (role_cell, None),
            };
            assert_eq!(
                format!("{:?}:{:?}", cls.lib, cls.role),
                lib_role_raw.trim_matches('`'),
                "sample `{sample_path}` disagreed with `discovery::classify`"
            );
            match tier_raw {
                None => assert!(
                    !(cls.lib == Lib::Arm64 && cls.role == Role::Spec),
                    "`Arm64:Spec` row `{sample_path}` must specify its `TrustedTcbTier`"
                ),
                Some("(`CoreInitOnly`)") => assert_eq!(
                    classify_trusted_tcb_module(&mod_name),
                    Some(TrustedTcbTier::CoreInitOnly),
                    "{sample_path}"
                ),
                Some("(`SurfaceMacro`)") => assert_eq!(
                    classify_trusted_tcb_module(&mod_name),
                    Some(TrustedTcbTier::SurfaceMacro),
                    "{sample_path}"
                ),
                Some(other) => panic!("unexpected tier `{other}` in row: {row}"),
            }
        }
    }
}

#[test]
fn equivalence_spec_modules_are_trusted_case_studies_tcb() {
    use crate::policy::{TrustCategory, classify_path, is_case_study_path};
    for module in ["Equivalence.Spec", "Equivalence.Spec.Basic"] {
        assert_eq!(
            classify(module),
            Some(ModuleClass {
                lib: Lib::Equivalence,
                role: Role::Spec,
            }),
            "{module}"
        );
    }
    assert_eq!(
        classify_path("Equivalence/Spec/Basic.lean"),
        Some(TrustCategory::CaseStudiesTcb)
    );
    assert!(discovery::is_spec_path("Equivalence/Spec/Basic.lean"));
    assert!(is_case_study_path("Equivalence/Spec/Basic.lean"));
}

#[test]
fn equivalence_proofs_modules_are_untrusted_proof() {
    use crate::policy::{TrustCategory, classify_path};
    for module in ["Equivalence.Proofs", "Equivalence.Proofs.Basic"] {
        assert_eq!(
            classify(module),
            Some(ModuleClass {
                lib: Lib::Equivalence,
                role: Role::Proof,
            }),
            "{module}"
        );
    }
    assert_eq!(
        classify_path("Equivalence/Proofs/Basic.lean"),
        Some(TrustCategory::Proof)
    );
    assert!(!discovery::is_spec_path("Equivalence/Proofs/Basic.lean"));
    // Tests, package configuration, and fail-closed strays.
    assert_eq!(
        classify("Equivalence.Testing.Smoke"),
        Some(ModuleClass {
            lib: Lib::Testing,
            role: Role::Test,
        })
    );
    for (path, category) in [
        ("Equivalence/lakefile.toml", TrustCategory::Infra),
        ("Equivalence/lake-manifest.json", TrustCategory::Infra),
        ("Equivalence/Testing/vectors.json", TrustCategory::Testing),
        ("Equivalence/README.md", TrustCategory::Doc),
    ] {
        assert_eq!(classify_path(path), Some(category), "{path}");
    }
    for unknown in ["Equivalence", "Equivalence.Stray", "Equivalence.Helpers.Foo"] {
        assert_eq!(classify(unknown), None, "{unknown}");
    }
    assert_eq!(classify_path("Equivalence/stray.txt"), None);
}

#[test]
fn equivalence_package_layering() {
    let v = check(&[
        ("Arm64.lean", "def a := 1\n"),
        ("ProofLib/Core.lean", "import Arm64\ntheorem p : True := trivial\n"),
        (
            "Equivalence/Spec/Basic.lean",
            "import Arm64\ndef equivSpec := 1\n",
        ),
        (
            "Equivalence/Spec/BadProofImport.lean",
            "import Equivalence.Proofs.Core\ndef bad := 1\n",
        ),
        (
            "Equivalence/Proofs/Core.lean",
            "import Equivalence.Spec.Basic\nimport ProofLib.Core\ntheorem e : True := trivial\n",
        ),
        (
            "Equivalence/Proofs/BadUp.lean",
            "import VerifiedLibraries.Gamma.Spec\nimport CaseStudies.Alpha.Spec\ntheorem e2 : True := trivial\n",
        ),
        ("VerifiedLibraries/Gamma/Spec.lean", "import Arm64\ndef gs := 1\n"),
        (
            "VerifiedLibraries/Gamma/Proofs/Core.lean",
            "import Equivalence.Spec.Basic\ntheorem gp : True := trivial\n",
        ),
        (
            "Arm64/Testing/EquivTest.lean",
            "import Equivalence.Spec.Basic\ntheorem at1 : True := trivial\n",
        ),
        (
            "CaseStudies/Alpha/Spec.lean",
            "import Equivalence.Spec.Basic\ndef aspec := 1\n",
        ),
        (
            "CaseStudies/Alpha/Proofs/Core.lean",
            "import Equivalence.Proofs.Core\ntheorem ap : True := trivial\n",
        ),
    ]);
    // Case studies may import both halves of `Equivalence`; `Equivalence.Proofs` may import its
    // own spec and `ProofLib`.
    for ok in [
        "Equivalence/Spec/Basic.lean",
        "Equivalence/Proofs/Core.lean",
        "CaseStudies/Alpha/Spec.lean",
        "CaseStudies/Alpha/Proofs/Core.lean",
    ] {
        assert!(!v.iter().any(|x| x.path == ok), "{ok}: {v:#?}");
    }
    assert!(has(
        &v,
        "Equivalence/Spec/BadProofImport.lean",
        "may only import Spec modules"
    ));
    assert_eq!(
        v.iter()
            .filter(|x| x.path == "Equivalence/Proofs/BadUp.lean" && x.rule.contains("layering"))
            .count(),
        2,
        "{v:#?}"
    );
    assert!(has(&v, "VerifiedLibraries/Gamma/Proofs/Core.lean", "layering"));
    assert!(has(&v, "Arm64/Testing/EquivTest.lean", "layering"));
}

#[test]
fn no_case_studies_exempts_filtered_equivalence_imports_from_unresolved() {
    // `--no-case-studies` drops `Equivalence/` from the workspace (`is_case_study_path`), so an
    // engine-side `Testing` module importing `Equivalence.*` must not report the (filtered-out)
    // target as unresolved. Without the filter the missing module still fails closed.
    let sources = [(
        "ProofLib/Testing/WidgetEquiv.lean",
        "import Equivalence.Proofs.Basic\n",
    )];
    let path = "ProofLib/Testing/WidgetEquiv.lean";
    let needle = "unresolved import `Equivalence.Proofs.Basic`";

    let full = check(&sources);
    assert!(has(&full, path, needle), "{full:#?}");

    let mut ws = Workspace::from_sources(sources.iter().copied()).unwrap();
    ws.no_case_studies = true;
    let filtered = ws.check_all();
    assert!(!has(&filtered, path, needle), "{filtered:#?}");
    assert!(
        !filtered
            .iter()
            .any(|v| v.path == path && v.rule.contains("layering")),
        "{filtered:#?}"
    );

    // An unrelated missing engine import is still reported under `--no-case-studies`.
    let mut ws = Workspace::from_sources([(path, "import ProofLib.Missing\n")]).unwrap();
    ws.no_case_studies = true;
    let filtered = ws.check_all();
    assert!(
        has(&filtered, path, "unresolved import `ProofLib.Missing`"),
        "{filtered:#?}"
    );
}

#[test]
fn legacy_linked_image_import_allowlist_enforced() {
    let v = check(&[
        ("Arm64/Legacy.lean", "def l := 0\n"),
        (
            "Arm64/Legacy/Object/LinkedImage.lean",
            "import Arm64.Legacy\ndef li := 0\n",
        ),
        (
            "ProofLib/ObjectLoad.lean",
            "import Arm64.Legacy\ndef ok := 0\n",
        ),
        (
            "ProofLib/NewUnlisted.lean",
            "import Arm64.Legacy\ndef bad := 0\n",
        ),
        (
            "CaseStudies/Alpha/Proofs/Main.lean",
            "import Arm64.Legacy\ndef bad2 := 0\n",
        ),
    ]);
    assert!(
        !v.iter().any(|x| x.path == "Arm64/Legacy/Object/LinkedImage.lean"),
        "{v:#?}"
    );
    assert!(
        !v.iter().any(|x| x.path == "ProofLib/ObjectLoad.lean"),
        "{v:#?}"
    );
    assert!(
        has(&v, "ProofLib/NewUnlisted.lean", "legacy-linked-image-import"),
        "{v:#?}"
    );
    assert!(
        has(
            &v,
            "CaseStudies/Alpha/Proofs/Main.lean",
            "legacy-linked-image-import"
        ),
        "{v:#?}"
    );
}

/// Engine fixture for `whole-process-no-library-specs`: a `Process` barrel over the loader plus
/// the library-spec modules `Process.OverrideWellBehaved -> Spec.Hoare -> Spec.SepLogic`.
fn whole_process_engine(barrel_reexports_owb: bool) -> Vec<(&'static str, &'static str)> {
    vec![
        ("Arm64/Trusted/Process/Loader.lean", "def load := 0\n"),
        ("Arm64/Trusted/Spec/SepLogic.lean", "def sep := 0\n"),
        (
            "Arm64/Trusted/Spec/Hoare.lean",
            "import Arm64.Trusted.Spec.SepLogic\ndef hoare := 0\n",
        ),
        (
            "Arm64/Trusted/Process/OverrideWellBehaved.lean",
            "import Arm64.Trusted.Spec.Hoare\ndef wb := 0\n",
        ),
        (
            "Arm64/Trusted/Process.lean",
            if barrel_reexports_owb {
                "import Arm64.Trusted.Process.Loader\nimport Arm64.Trusted.Process.OverrideWellBehaved\n"
            } else {
                "import Arm64.Trusted.Process.Loader\n"
            },
        ),
        ("ProofLib/Hoare.lean", "import Arm64.Trusted.Spec.Hoare\n"),
    ]
}

fn whole_process_violations(sources: &[(&str, &str)]) -> Vec<Violation> {
    Workspace::from_sources(sources.iter().copied())
        .unwrap()
        .check_whole_process_no_library_specs()
}

#[test]
fn whole_process_no_library_specs_accepts_process_barrel() {
    let mut sources = whole_process_engine(false);
    sources.extend([
        ("CaseStudies/Cp/Spec.lean", "import Arm64.Trusted.Process\n"),
        // `Theorems` imports `Proof` privately: that edge is not trusted and is not followed.
        (
            "CaseStudies/Cp/Theorems.lean",
            "module\npublic import CaseStudies.Cp.Spec\nimport ProofLib.Hoare\n",
        ),
        // Generated `*ElfObj` modules are followed through their emitted header.
        (
            "CaseStudies/Hashbrown/Spec.lean",
            "import CaseStudies.Hashbrown.Generated.HashbrownElfObj\n",
        ),
    ]);
    let v = whole_process_violations(&sources);
    assert!(v.is_empty(), "{v:#?}");
    let ws = Workspace::from_sources(sources.iter().copied()).unwrap();
    let closure = ws.whole_process_trusted_closure("Hashbrown");
    assert!(closure.contains_key("Arm64.Trusted.Process.Loader"), "{closure:#?}");
    assert!(!closure.contains_key("ProofLib.Hoare"), "{closure:#?}");
    assert_eq!(ws.engine_closure_lines(closure.keys()), (2, 2));
}

#[test]
fn whole_process_no_library_specs_rejects_barrel_leak() {
    let mut sources = whole_process_engine(true);
    sources.extend([
        ("CaseStudies/Cp/Spec.lean", "import Arm64.Trusted.Process\n"),
        (
            "CaseStudies/Wasmi/Spec.lean",
            "import CaseStudies.Wasmi.Generated.WasmiElfObj\n",
        ),
    ]);
    let v = whole_process_violations(&sources);
    for (pkg, path) in [
        ("Cp", "Arm64/Trusted/Process.lean"),
        ("Wasmi", "Arm64/Trusted/Process.lean"),
    ] {
        for lib_mod in [
            "Arm64.Trusted.Process.OverrideWellBehaved",
            "Arm64.Trusted.Spec.Hoare",
            "Arm64.Trusted.Spec.SepLogic",
        ] {
            assert!(
                v.iter().any(|x| x.rule == policy::WHOLE_PROCESS_NO_LIBRARY_SPECS_RULE
                    && x.text.contains(&format!("`CaseStudies/{pkg}`"))
                    && x.text.contains(&format!("`{lib_mod}`"))
                    && (lib_mod != "Arm64.Trusted.Process.OverrideWellBehaved"
                        || x.path == path)),
                "{pkg} {lib_mod}: {v:#?}"
            );
        }
    }
    // The violation names the import chain.
    assert!(
        v.iter().any(|x| x.text.contains(
            "CaseStudies.Cp.Spec -> Arm64.Trusted.Process -> Arm64.Trusted.Process.OverrideWellBehaved -> Arm64.Trusted.Spec.Hoare"
        )),
        "{v:#?}"
    );
    // Library-style packages are not checked.
    let mut lib_sources = whole_process_engine(true);
    lib_sources.push(("CaseStudies/Widget/Spec.lean", "import Arm64.Trusted.Spec.Hoare\n"));
    assert!(whole_process_violations(&lib_sources).is_empty());
}

#[test]
fn whole_process_no_library_specs_direct_import_and_list_sync() {
    let mut sources = whole_process_engine(false);
    sources.push((
        "CaseStudies/Hashbrown/Spec/Top.lean",
        "import Arm64.Trusted.Process\nimport Arm64.Trusted.Spec.SepLogic\n",
    ));
    sources.push((
        "CaseStudies/IndexMap/Spec/Top.lean",
        "import Arm64.Trusted.Process\nimport Arm64.Trusted.Spec.Hoare\n",
    ));
    sources.push((
        "FormalRfcs/Rfc4648/Rust/Spec/Top.lean",
        "import Arm64.Trusted.Process\nimport Arm64.Trusted.Spec.SepLogic\n",
    ));
    let v = whole_process_violations(&sources);
    assert!(
        has(&v, "CaseStudies/Hashbrown/Spec/Top.lean", "whole-process-no-library-specs"),
        "{v:#?}"
    );
    assert!(
        has(
            &v,
            "CaseStudies/IndexMap/Spec/Top.lean",
            "whole-process-no-library-specs"
        ),
        "{v:#?}"
    );
    assert!(
        has(
            &v,
            "FormalRfcs/Rfc4648/Rust/Spec/Top.lean",
            "whole-process-no-library-specs"
        ),
        "{v:#?}"
    );
    assert_eq!(policy::LIBRARY_SPEC_MODULES.len(), 12);
    for m in policy::LIBRARY_SPEC_MODULES {
        assert!(policy::classify_trusted_tcb_module(m).is_some(), "{m}");
    }
    assert_eq!(
        policy::generated_spec_imports("CaseStudies.Cp.Generated.CpElfObj"),
        Some(&["Arm64.Trusted.Process"][..])
    );
    assert_eq!(
        policy::generated_spec_imports("CaseStudies.Cp.Generated.CpPlacedWitness"),
        None
    );
}

#[test]
fn formal_rfcs_model_modules_are_classified() {
    use crate::policy::classify_path;
    let cases = [
        ("FormalRfcs.Common.Spec.Cli", Lib::FormalRfcs, Role::Spec),
        ("FormalRfcs.Common.Spec", Lib::FormalRfcs, Role::Spec),
        ("FormalRfcs.Widget.Spec", Lib::FormalRfcs, Role::Spec),
        ("FormalRfcs.Widget.Spec.Top", Lib::FormalRfcs, Role::Spec),
        (
            "FormalRfcs.Common.Proofs.Basic",
            Lib::FormalRfcs,
            Role::Proof,
        ),
        (
            "FormalRfcs.Widget.Proofs.Basic",
            Lib::FormalRfcs,
            Role::Proof,
        ),
        (
            "FormalRfcs.Common.Testing.CliExamples",
            Lib::Testing,
            Role::Test,
        ),
        ("FormalRfcs.Widget.Testing", Lib::Testing, Role::Test),
        (
            "FormalRfcs.Widget.Testing.Audit.Fixtures",
            Lib::Testing,
            Role::Fixture,
        ),
    ];
    for (module, lib, role) in cases {
        assert_eq!(
            classify(module),
            Some(ModuleClass { lib, role }),
            "{module}"
        );
    }
    assert!(discovery::is_spec_path("FormalRfcs/Common/Spec/Cli.lean"));
    assert!(discovery::is_spec_path("FormalRfcs/Widget/Spec/Top.lean"));
    assert!(!discovery::is_spec_path(
        "FormalRfcs/Widget/Proofs/Basic.lean"
    ));
    // Fail closed: no umbrella modules, stray subdirectories, or `Common` implementation packages.
    for unknown in [
        "FormalRfcs",
        "FormalRfcs.Widget",
        "FormalRfcs.Common",
        "FormalRfcs.Common.Helpers",
        "FormalRfcs.Common.Alpha.Spec",
        "FormalRfcs.Testing.Foo",
        "FormalRfcs.Common.Drivers.Foo",
    ] {
        assert_eq!(classify(unknown), None, "{unknown}");
    }
    assert_eq!(classify_path("FormalRfcs/stray.txt"), None);
    assert_eq!(classify_path("FormalRfcs/Widget/notes.txt"), None);
}

#[test]
fn formal_rfcs_implementation_packages_are_classified_like_case_studies() {
    use crate::policy::{TrustCategory, classify_path};
    // Every `CaseStudies/Alpha/<rest>` classifies exactly like `FormalRfcs/Widget/Alpha/<rest>`.
    let rests = [
        "",
        ".Spec",
        ".Spec.Top",
        ".Proofs.Main",
        ".Witness.Foo",
        ".Generated",
        ".Generated.AlphaPlacedObj",
        ".Generated.AlphaElfObj",
        ".Generated.AlphaCode",
        ".Theorems",
        ".Theorems.Top",
        ".Testing.SpecAudit",
        ".Testing.Audit.Fixtures",
        ".Stray",
        ".Implementation.Foo",
    ];
    for rest in rests {
        let cs = format!("CaseStudies.Alpha{rest}");
        let fr = format!("FormalRfcs.Widget.Alpha{rest}");
        assert_eq!(classify(&fr), classify(&cs), "{fr} vs {cs}");
        assert_eq!(is_generated(&fr), is_generated(&cs), "{fr}");
        assert_eq!(
            discovery::is_testing_module(&fr),
            discovery::is_testing_module(&cs),
            "{fr}"
        );
    }
    assert_eq!(
        classify("FormalRfcs.Widget.Alpha.Spec.Top").map(|c| c.lib),
        Some(Lib::Examples)
    );
    assert_eq!(
        classify_path("FormalRfcs/Widget/Alpha/Spec/Top.lean"),
        Some(TrustCategory::CaseStudiesTcb)
    );
    assert_eq!(
        discovery::standalone_package_of("FormalRfcs.Widget.Alpha.Proofs.Main").as_deref(),
        Some("FormalRfcs.Widget.Alpha")
    );
    assert_eq!(
        discovery::standalone_package_of("CaseStudies.Alpha.Spec").as_deref(),
        Some("CaseStudies.Alpha")
    );
    for none in [
        "FormalRfcs.Widget.Spec.Top",
        "FormalRfcs.Common.Spec.Cli",
        "VerifiedLibraries.Gamma.Spec",
        "ProofLib.Core",
    ] {
        assert_eq!(discovery::standalone_package_of(none), None, "{none}");
    }
}

#[test]
fn discover_campaign_package_dirs_finds_case_studies_and_formal_rfc_implementations() {
    let dir = tempfile::tempdir().unwrap();
    let root = dir.path();
    for (rel, contents) in [
        ("CaseStudies/Alpha/lakefile.lean", "package alpha\n"),
        ("CaseStudies/Beta/lakefile.toml", "name = \"beta\"\n"),
        ("CaseStudies/_template/lakefile.lean", "package t\n"),
        ("CaseStudies/NoLake/Spec.lean", "def x := 1\n"),
        ("FormalRfcs/lakefile.toml", "name = \"formal-rfcs\"\n"),
        ("FormalRfcs/Common/Spec/Cli.lean", "def x := 1\n"),
        ("FormalRfcs/Common/Alpha/lakefile.toml", "name = \"bad\"\n"),
        ("FormalRfcs/Widget/Spec/Top.lean", "def y := 1\n"),
        (
            "FormalRfcs/Widget/Alpha/lakefile.toml",
            "name = \"widget-alpha\"\n",
        ),
        (
            "FormalRfcs/Widget/Beta/lakefile.lean",
            "package widgetBeta\n",
        ),
        (
            "FormalRfcs/Widget/Testing/lakefile.toml",
            "name = \"bad\"\n",
        ),
        ("FormalRfcs/Widget/NoLake/Spec/Top.lean", "def z := 1\n"),
    ] {
        let p = root.join(rel);
        fs::create_dir_all(p.parent().unwrap()).unwrap();
        fs::write(p, contents).unwrap();
    }
    assert_eq!(
        discovery::discover_campaign_package_dirs(root),
        vec![
            "CaseStudies/Alpha".to_string(),
            "CaseStudies/Beta".to_string(),
        ]
    );
}

#[test]
fn formal_rfcs_package_layering_and_isolation() {
    let v = check(&[
        ("Arm64.lean", "def a := 1\n"),
        (
            "ProofLib/Core.lean",
            "import Arm64\ntheorem p : True := trivial\n",
        ),
        (
            "VerifiedLibraries/Gamma/Spec.lean",
            "import Arm64\ndef gs := 1\n",
        ),
        ("Equivalence/Spec/Basic.lean", "import Arm64\ndef es := 1\n"),
        ("Arm64/Testing/Helper.lean", "import Arm64\ndef th := 1\n"),
        (
            "FormalRfcs/Common/Spec/Cli.lean",
            "import Arm64\nimport VerifiedLibraries.Gamma.Spec\ndef cli := 1\n",
        ),
        (
            "FormalRfcs/Widget/Spec/Top.lean",
            "import FormalRfcs.Common.Spec.Cli\ndef top := 1\n",
        ),
        (
            "FormalRfcs/Widget/Spec/BadProof.lean",
            "import FormalRfcs.Widget.Proofs.Basic\ndef bad := 1\n",
        ),
        (
            "FormalRfcs/Widget/Proofs/Basic.lean",
            "import FormalRfcs.Widget.Spec.Top\nimport ProofLib.Core\ntheorem b : True := trivial\n",
        ),
        (
            "FormalRfcs/Widget/Proofs/BadUp.lean",
            "import Equivalence.Spec.Basic\nimport Arm64.Testing.Helper\nimport CaseStudies.Alpha.Spec\nimport FormalRfcs.Widget.Alpha.Spec\ntheorem u : True := trivial\n",
        ),
        (
            "FormalRfcs/Common/Testing/CliExamples.lean",
            "import FormalRfcs.Common.Spec.Cli\ntheorem ex : True := trivial\n",
        ),
        (
            "FormalRfcs/Widget/Alpha/Spec.lean",
            "import FormalRfcs.Widget.Spec.Top\ndef aspec := 1\n",
        ),
        (
            "FormalRfcs/Widget/Alpha/Proofs/Core.lean",
            "import FormalRfcs.Widget.Alpha.Spec\nimport FormalRfcs.Widget.Proofs.Basic\ntheorem ac : True := trivial\n",
        ),
        (
            "FormalRfcs/Widget/Alpha/Proofs/Sibling.lean",
            "import FormalRfcs.Widget.Beta.Spec\ntheorem sib : True := trivial\n",
        ),
        (
            "FormalRfcs/Widget/Beta/Spec.lean",
            "import FormalRfcs.Widget.Spec.Top\ndef bspec := 1\n",
        ),
        (
            "VerifiedLibraries/Gamma/Proofs/BadUp.lean",
            "import FormalRfcs.Widget.Spec.Top\ntheorem g : True := trivial\n",
        ),
        (
            "ProofLib/BadUp.lean",
            "import FormalRfcs.Widget.Spec.Top\ntheorem pl : True := trivial\n",
        ),
        (
            "Arm64/Testing/BadUp.lean",
            "import FormalRfcs.Widget.Spec.Top\ntheorem at1 : True := trivial\n",
        ),
        (
            "CaseStudies/Alpha/Spec.lean",
            "import FormalRfcs.Widget.Spec.Top\ndef csa := 1\n",
        ),
        (
            "CaseStudies/Alpha/Proofs/Core.lean",
            "import FormalRfcs.Widget.Proofs.Basic\nimport FormalRfcs.Widget.Alpha.Spec\ntheorem cs : True := trivial\n",
        ),
    ]);
    for ok in [
        "FormalRfcs/Common/Spec/Cli.lean",
        "FormalRfcs/Widget/Spec/Top.lean",
        "FormalRfcs/Widget/Proofs/Basic.lean",
        "FormalRfcs/Common/Testing/CliExamples.lean",
        "FormalRfcs/Widget/Alpha/Spec.lean",
        "FormalRfcs/Widget/Alpha/Proofs/Core.lean",
        "FormalRfcs/Widget/Beta/Spec.lean",
        "CaseStudies/Alpha/Spec.lean",
    ] {
        assert!(!v.iter().any(|x| x.path == ok), "{ok}: {v:#?}");
    }
    assert!(has(
        &v,
        "FormalRfcs/Widget/Spec/BadProof.lean",
        "may only import Spec modules"
    ));
    // `FormalRfcs` may not import `Equivalence`, `Arm64Testing`, or case studies / implementation
    // packages (`Examples`).
    assert_eq!(
        v.iter()
            .filter(
                |x| x.path == "FormalRfcs/Widget/Proofs/BadUp.lean" && x.rule.contains("layering")
            )
            .count(),
        4,
        "{v:#?}"
    );
    assert!(has(
        &v,
        "VerifiedLibraries/Gamma/Proofs/BadUp.lean",
        "layering"
    ));
    assert!(has(&v, "ProofLib/BadUp.lean", "layering"));
    assert!(has(&v, "Arm64/Testing/BadUp.lean", "layering"));
    // Per-implementation packages are pairwise independent, from each other and from case studies.
    assert!(has(
        &v,
        "FormalRfcs/Widget/Alpha/Proofs/Sibling.lean",
        "package-isolation:"
    ));
    assert!(has(
        &v,
        "CaseStudies/Alpha/Proofs/Core.lean",
        "package-isolation:"
    ));
    assert_eq!(
        v.iter()
            .filter(|x| x.path == "CaseStudies/Alpha/Proofs/Core.lean")
            .count(),
        1,
        "{v:#?}"
    );
}

#[test]
fn formal_rfcs_trusted_impl_imports_are_own_rfc_only() {
    let v = check(&[
        ("Arm64.lean", "def a := 1\n"),
        (
            "Arm64/Trusted/Surface/FileBytes.lean",
            "import Arm64\ndef fb := 1\n",
        ),
        (
            "ProofLib/Core.lean",
            "import Arm64\ntheorem p : True := trivial\n",
        ),
        (
            "FormalRfcs/Common/Spec/Cli.lean",
            "import Arm64\ndef cli := 1\n",
        ),
        (
            "FormalRfcs/Widget/Spec/Top.lean",
            "import FormalRfcs.Common.Spec.Cli\ndef top := 1\n",
        ),
        (
            "FormalRfcs/Gadget/Spec/Top.lean",
            "import FormalRfcs.Common.Spec.Cli\ndef gtop := 1\n",
        ),
        (
            "FormalRfcs/Widget/Alpha/Spec/Top.lean",
            "import Arm64.Trusted.Surface.FileBytes\nimport Std\nimport FormalRfcs.Common.Spec.Cli\nimport FormalRfcs.Widget.Spec.Top\ndef aspec := 1\n",
        ),
        (
            "FormalRfcs/Widget/Alpha/Proofs/Main.lean",
            "import FormalRfcs.Widget.Alpha.Spec.Top\nimport ProofLib.Core\ntheorem am : True := trivial\n",
        ),
        (
            "FormalRfcs/Widget/Alpha/Theorems/Top.lean",
            "import FormalRfcs.Widget.Alpha.Spec.Top\nimport FormalRfcs.Widget.Alpha.Proofs.Main\ntheorem at1 : True := trivial\n",
        ),
        (
            "FormalRfcs/Widget/Beta/Spec/Top.lean",
            "import FormalRfcs.Gadget.Spec.Top\ndef bspec := 1\n",
        ),
        (
            "FormalRfcs/Widget/Beta/Theorems/Top.lean",
            "import FormalRfcs.Gadget.Spec.Top\nimport FormalRfcs.Widget.Beta.Spec.Top\ntheorem bt : True := trivial\n",
        ),
        (
            "FormalRfcs/Widget/Beta/Proofs/Main.lean",
            "import FormalRfcs.Gadget.Spec.Top\ntheorem bp : True := trivial\n",
        ),
        (
            "FormalRfcs/Widget/Alpha/Proofs/CrossImpl.lean",
            "import FormalRfcs.Widget.Beta.Proofs.Main\ntheorem ci : True := trivial\n",
        ),
    ]);
    for ok in [
        "FormalRfcs/Widget/Alpha/Spec/Top.lean",
        "FormalRfcs/Widget/Alpha/Proofs/Main.lean",
        "FormalRfcs/Widget/Alpha/Theorems/Top.lean",
    ] {
        assert!(!v.iter().any(|x| x.path == ok), "{ok}: {v:#?}");
    }
    // A trusted implementation module may not import another RFC's `Spec`.
    for bad in [
        "FormalRfcs/Widget/Beta/Spec/Top.lean",
        "FormalRfcs/Widget/Beta/Theorems/Top.lean",
    ] {
        assert!(
            has(
                &v,
                bad,
                "package-isolation: trusted formal RFC implementation module"
            ),
            "{bad}: {v:#?}"
        );
    }
    // Untrusted `Proofs`/`Testing` modules in an implementation may not import another RFC or a
    // sibling implementation's `Proofs`.
    assert!(
        has(
            &v,
            "FormalRfcs/Widget/Beta/Proofs/Main.lean",
            "package-isolation:"
        ),
        "{v:#?}"
    );
    assert!(
        has(
            &v,
            "FormalRfcs/Widget/Alpha/Proofs/CrossImpl.lean",
            "package-isolation:"
        ),
        "{v:#?}"
    );

    // F3: RFC-level (`FormalRfcs/<Rfc>/{Spec,Proofs,Testing}/**`) and `FormalRfcs/Common/**`
    // modules also obey cross-RFC, implementation, and case-study isolation, while
    // `CaseStudies/<Pkg>/Spec/** -> FormalRfcs/<Rfc>/Spec/**` remains allowed.
    let v_f3 = check(&[
        ("Arm64.lean", "def a := 1\n"),
        (
            "FormalRfcs/Common/Spec/Cli.lean",
            "import Arm64\ndef cli := 1\n",
        ),
        (
            "FormalRfcs/Common/Spec/BadDown.lean",
            "import FormalRfcs.Ogg.Spec.Dump\ndef bd := 1\n",
        ),
        (
            "FormalRfcs/Ogg/Spec/Dump.lean",
            "import FormalRfcs.Common.Spec.Cli\ndef oggDump := 1\n",
        ),
        (
            "FormalRfcs/Cbor/Spec/Dump.lean",
            "import FormalRfcs.Common.Spec.Cli\ndef cborDump := 1\n",
        ),
        (
            "FormalRfcs/Deflate/Spec/Zlib.lean",
            "import FormalRfcs.Common.Spec.Cli\ndef deflateZlib := 1\n",
        ),
        (
            "FormalRfcs/Ogg/Spec/CrossRfc.lean",
            "import FormalRfcs.Cbor.Spec.Dump\ndef x := 1\n",
        ),
        (
            "FormalRfcs/Ogg/Libogg/Proofs/Main.lean",
            "import FormalRfcs.Ogg.Spec.Dump\ntheorem m : True := trivial\n",
        ),
        (
            "CaseStudies/Zlib/Spec/ZlibFormat.lean",
            "import FormalRfcs.Deflate.Spec.Zlib\ndef zf := 1\n",
        ),
        (
            "CaseStudies/Zlib/Proofs/Main.lean",
            "import CaseStudies.Zlib.Spec.ZlibFormat\ntheorem zm : True := trivial\n",
        ),
        (
            "FormalRfcs/Ogg/Testing/BadImpl.lean",
            "import FormalRfcs.Ogg.Libogg.Proofs.Main\ntheorem bi : True := trivial\n",
        ),
        (
            "FormalRfcs/Ogg/Testing/BadCaseStudy.lean",
            "import CaseStudies.Zlib.Proofs.Main\ntheorem bcs : True := trivial\n",
        ),
    ]);
    assert!(
        !v_f3
            .iter()
            .any(|x| x.path == "CaseStudies/Zlib/Spec/ZlibFormat.lean"),
        "expected CaseStudies.Zlib.Spec.ZlibFormat -> FormalRfcs.Deflate.Spec.Zlib to pass: {v_f3:#?}"
    );
    for bad in [
        "FormalRfcs/Common/Spec/BadDown.lean",
        "FormalRfcs/Ogg/Spec/CrossRfc.lean",
        "FormalRfcs/Ogg/Testing/BadImpl.lean",
        "FormalRfcs/Ogg/Testing/BadCaseStudy.lean",
    ] {
        assert!(
            has(&v_f3, bad, "package-isolation:"),
            "expected package-isolation violation in `{bad}`: {v_f3:#?}"
        );
    }
}
