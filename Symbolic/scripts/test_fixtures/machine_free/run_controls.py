#!/usr/bin/env python3
# Copyright 2026 Google LLC
#
# All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0
#
# Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
# limitations under the License.

"""Compile scratch fixtures and run the machine-free check control suite.

Usage (from repository root or any directory):
    python3 Symbolic/scripts/test_fixtures/machine_free/run_controls.py \
      --root <WORKTREE> \
      --report-out /tmp/mfc_controls_verbatim.txt

Fixture sources are stored alongside this script as `*.lean.fixture` so repository-wide `.lean`
linters (`check_symbolic_deps.py`, `check_lib_roots.py`, `check_no_axiom_decls.py`, Lake globs)
do not treat synthetic negative controls as tracked library modules. Staging and `.olean`
compilation run in a temporary overlay directory; `<WORKTREE>/.lake` and tracked files are
untouched.
"""
import argparse
import os
import pathlib
import shutil
import subprocess
import sys
import tempfile
import time


FIXTURES_DIR = pathlib.Path(__file__).resolve().parent
SCRIPTS_DIR = FIXTURES_DIR.parents[1]
DEFAULT_REPO = SCRIPTS_DIR.parents[1]


FIXTURE_SOURCES_IN_ORDER = [
    "ScratchFixture/P2MixedCMod.lean",
    "ScratchFixture/P2Root.lean",
    "ScratchFixture/P3Wrapper.lean",
    "ScratchFixture/P3Root.lean",
    "ScratchFixture/P4PureTurnedMachine.lean",
    "ScratchFixture/P5M1.lean",
    "ScratchFixture/P5M2.lean",
    "ScratchFixture/P5Root.lean",
    "Computational/ScratchFixtureP6.lean",
    "Computational/ScratchFixtureP6Root.lean",
    "Symbolic/Specifications/ScratchFixtureP7.lean",
    "ScratchFixture/P8BvDecide.lean",
    "ScratchFixture/P8NativeDecide.lean",
    "ScratchFixture/P9ExemptRoot.lean",
    "ScratchFixture/P10DeniedMod.lean",
    "ScratchFixture/P10ProofMod.lean",
    "ScratchFixture/P10Root.lean",
    "ScratchFixture/PF2Pure.lean",
    "ScratchFixture/PF2Realizer.lean",
    "ScratchFixture/PF2Caller.lean",
    "ScratchFixture/PF5DeniedParent.lean",
    "ScratchFixture/PF5Realizer.lean",
    "ScratchFixture/PF5Caller.lean",
    "ScratchFixture/PRow87DeniedRealizer.lean",
    "ScratchFixture/PRow87CleanRealizer.lean",
    "ScratchFixture/PRow87CallerPureCore.lean",
    "ScratchFixture/PRow87CallerDeniedParent.lean",
    "ScratchFixture/PRow87CallerBadVal.lean",
    "ScratchFixture/PRow87CallerAxiom.lean",
    "ScratchFixture/PRow87CallerUserDecl.lean",
]


def symlink_tree_files(src_dir: pathlib.Path, dst_dir: pathlib.Path) -> None:
    """Mirror `src_dir`'s directory structure in `dst_dir` with file symlinks."""
    dst_dir.mkdir(parents=True, exist_ok=True)
    for entry in sorted(src_dir.iterdir()):
        dst = dst_dir / entry.name
        if entry.is_dir() and not entry.is_symlink():
            symlink_tree_files(entry, dst)
        else:
            if not dst.exists() and not dst.is_symlink():
                os.symlink(entry.resolve(), dst)


def stage_fixture_sources(fixtures_dir: pathlib.Path, tmp_dir: pathlib.Path) -> pathlib.Path:
    """Copy `*.lean.fixture` (or fallback `*.lean`) sources into `tmp_dir / 'fixture_src'`."""
    src_root = tmp_dir / "fixture_src"
    src_root.mkdir(parents=True, exist_ok=True)
    for rel_src in FIXTURE_SOURCES_IN_ORDER:
        cand_fixture = fixtures_dir / f"{rel_src}.fixture"
        cand_lean = fixtures_dir / rel_src
        if cand_fixture.is_file():
            src_file = cand_fixture
        elif cand_lean.is_file():
            src_file = cand_lean
        else:
            raise RuntimeError(f"missing fixture source: {cand_fixture}")
        dst_file = src_root / rel_src
        dst_file.parent.mkdir(parents=True, exist_ok=True)
        shutil.copyfile(src_file, dst_file)
    return src_root


def prepare_overlay_and_compile(
    repo_root: pathlib.Path,
    fixtures_dir: pathlib.Path,
    lean_bin: str,
    lean_path: str,
    merged_arm64: pathlib.Path | None,
    tmp_dir: pathlib.Path,
) -> pathlib.Path:
    """Build an isolated `LEAN_PATH` overlay and compile all scratch fixtures into it."""
    staged_src_dir = stage_fixture_sources(fixtures_dir, tmp_dir)
    overlay = tmp_dir / "overlay_lib"
    overlay.mkdir(parents=True, exist_ok=True)

    # Lean binds top-level package roots (`Symbolic`, `Computational`) to the first directory
    # on `LEAN_PATH` containing `Symbolic/` or `Computational/`, so mirror existing `.olean`s
    # of those two roots as symlinks inside `overlay` before compiling `ScratchFixtureP6`/`P7`.
    pkg_lean_lib = repo_root / ".lake" / "build" / "lib" / "lean"
    for pkg_prefix in ("Computational", "Symbolic"):
        for top in sorted(pkg_lean_lib.glob(f"{pkg_prefix}*")):
            dst = overlay / top.name
            if top.is_dir() and not top.is_symlink():
                symlink_tree_files(top, dst)
            else:
                if not dst.exists() and not dst.is_symlink():
                    os.symlink(top.resolve(), dst)

    lp_parts = [str(overlay)]
    if merged_arm64 is not None:
        lp_parts.append(str(merged_arm64))
    lp_parts.append(lean_path)
    env = os.environ.copy()
    env["LEAN_PATH"] = ":".join(lp_parts)
    env["LEAN_ABORT_ON_PANIC"] = "1"
    env.setdefault("LEAN_NUM_THREADS", "2")

    for rel_src in FIXTURE_SOURCES_IN_ORDER:
        src_file = staged_src_dir / rel_src
        out_olean = overlay / pathlib.Path(rel_src).with_suffix(".olean")
        out_olean.parent.mkdir(parents=True, exist_ok=True)
        cmd = [
            lean_bin,
            "-R",
            str(staged_src_dir),
            "-o",
            str(out_olean),
            str(src_file),
        ]
        proc = subprocess.run(
            cmd, cwd=str(repo_root), env=env, capture_output=True, text=True, check=False
        )
        if proc.returncode != 0:
            raise RuntimeError(
                f"failed compiling fixture {rel_src} (rc={proc.returncode}):\n"
                f"{proc.stdout}\n{proc.stderr}"
            )
    return overlay


def main() -> int:
    ap = argparse.ArgumentParser(description="Run machine-free controls P1–P10 + E2 check.")
    ap.add_argument("--root", default=str(DEFAULT_REPO), help="Repository/worktree root.")
    ap.add_argument(
        "--scripts-dir",
        default=str(SCRIPTS_DIR),
        help="Directory containing machine_free_check.py and MachineFreeCheck.lean.",
    )
    ap.add_argument(
        "--proofdeps-file",
        default=None,
        help="Path to machine_free_deny_proofdeps.txt (auto-emits statement-seed baseline in tmp if absent).",
    )
    ap.add_argument(
        "--report-out",
        default=None,
        help="Optional path to write full verbatim control transcript.",
    )
    args = ap.parse_args()

    repo_root = pathlib.Path(args.root).resolve()
    scripts_dir = pathlib.Path(args.scripts_dir).resolve()
    mfc_py = scripts_dir / "machine_free_check.py"
    sys.path.insert(0, str(scripts_dir))
    import machine_free_check as mfc  # type: ignore[import-not-found]

    deny_a = scripts_dir / "machine_free_deny.txt"
    deny_d2 = scripts_dir / "machine_free_deny_d2.txt"
    allow_stmt = repo_root / "Symbolic" / "scripts" / "machine_free_allow.txt"
    if not allow_stmt.is_file():
        allow_stmt = scripts_dir / "machine_free_allow.txt"
    allow_proof = scripts_dir / "machine_free_allow_proofdeps.txt"
    allow_q1 = scripts_dir / "machine_free_allow_proofdeps_q1.txt"
    exempt_e = scripts_dir / "machine_free_exempt_specs.txt"

    for req in (mfc_py, deny_a, allow_stmt, allow_proof, exempt_e):
        if not req.is_file():
            sys.stderr.write(f"[run-controls] error: required file missing: {req}\n")
            return 2

    deny_args = ["--deny-file", str(deny_a)]
    if deny_d2.is_file():
        deny_args += ["--deny-file", str(deny_d2)]
    deny_args += ["--exclude-deny-group", "5"]

    allow_args = ["--allow-file", str(allow_stmt), "--allow-file", str(allow_proof)]
    if allow_q1.is_file():
        allow_args += ["--allow-file", str(allow_q1)]

    lean_bin, lean_path = mfc.query_lake_env(repo_root)
    tmp_dir = pathlib.Path(tempfile.mkdtemp(prefix="mfc_controls_"))
    report_blocks: list[str] = []

    try:
        t0 = time.monotonic()
        merged_arm64 = mfc.build_merged_arm64_dir(repo_root, tmp_dir)
        overlay = prepare_overlay_and_compile(
            repo_root, FIXTURES_DIR, lean_bin, lean_path, merged_arm64, tmp_dir
        )
        compile_s = time.monotonic() - t0
        print(f"[run-controls] compiled {len(FIXTURE_SOURCES_IN_ORDER)} fixtures in {compile_s:.2f}s")

        seed_base = "Symbolic.Specifications.Refinement.Statement"

        def run_case(
            label: str,
            cli_args: list[str],
            exp_rc: int,
            must_contain: list[str],
            must_not_contain: list[str] | None = None,
            override_root: pathlib.Path | None = None,
            include_overlay: bool = True,
        ) -> tuple[int, str]:
            eff_root = override_root if override_root is not None else repo_root
            cmd = [
                sys.executable,
                str(mfc_py),
                "--root",
                str(eff_root),
            ]
            if include_overlay:
                cmd.extend(["--extra-lean-path", str(overlay)])
            cmd.extend(cli_args)
            case_env = os.environ.copy()
            case_env["LEAN_ABORT_ON_PANIC"] = "1"
            proc = subprocess.run(
                cmd, cwd=str(eff_root), env=case_env, capture_output=True, text=True, check=False
            )
            out = proc.stdout
            err = proc.stderr
            combined = out + ("\n" + err if err else "")
            disp_cmd = "python3 Symbolic/scripts/machine_free_check.py " + " ".join(cli_args)
            block = (
                f"=== CONTROL {label} (expected_rc={exp_rc}, actual_rc={proc.returncode}) ===\n"
                f"$ {disp_cmd}\n"
                f"{out.rstrip()}\n"
                f"[stderr] {err.strip()}\n"
            )
            report_blocks.append(block)
            if proc.returncode != exp_rc:
                raise RuntimeError(
                    f"{label}: expected rc={exp_rc}, got rc={proc.returncode}\n{combined}"
                )
            for needle in must_contain:
                if needle not in combined:
                    raise RuntimeError(
                        f"{label}: missing expected substring {needle!r} in output:\n{combined}"
                    )
            for forbidden in must_not_contain or []:
                if forbidden in combined:
                    raise RuntimeError(
                        f"{label}: unexpected forbidden substring {forbidden!r} in output:\n{combined}"
                    )
            print(f"[run-controls] PASS {label} (rc={proc.returncode})")
            return proc.returncode, combined

        is_bootstrap = False
        if args.proofdeps_file:
            proofdeps_c = pathlib.Path(args.proofdeps_file).resolve()
            if not proofdeps_c.is_file():
                sys.stderr.write(f"[run-controls] error: --proofdeps-file missing: {proofdeps_c}\n")
                return 2
        else:
            cand_c = scripts_dir / "machine_free_deny_proofdeps.txt"
            if cand_c.is_file():
                proofdeps_c = cand_c
            else:
                is_bootstrap = True
                base_seeds = tmp_dir / "base_stmt_seeds.txt"
                base_seeds.write_text(
                    f"{seed_base}\nScratchFixture.P3Wrapper\n", encoding="utf-8"
                )
                proofdeps_c = tmp_dir / "auto_stmt_proofdeps.txt"
                run_case(
                    "P0_bootstrap_stmt_proofdeps",
                    [
                        *deny_args,
                        *allow_args,
                        "--exempt-specs-file",
                        str(exempt_e),
                        "--subset-allow",
                        "--allow-scratch-fixture-roots",
                        "--scratch-fixture-seeds-file",
                        str(base_seeds),
                        "--emit-proofdeps",
                        str(proofdeps_c),
                    ],
                    0,
                    ["SUMMARY_EMIT_PROOFDEPS=PASS (patterns=1"],
                )
        bootstrap_extra = "ScratchFixture.P3Wrapper\n" if is_bootstrap else ""

        # P1: Statement and pure model roots pass under deny sets A (minus group 5) and C.
        bridges_txt = tmp_dir / "p1_bridges.txt"
        bridges_txt.write_text(
            "DY.Libsignal.Composed.Refinement.Cli.CompRefinesCli : root statement\n"
            "DY.Libsignal.Composed.Refinement.Cli.CompRefinesCliR : generic CLI refinement\n"
            "Nat.add_comm : not in root cone sample\n",
            encoding="utf-8",
        )
        run_case(
            "P1a_statement_roots_under_A_plus_C",
            [
                *deny_args,
                "--deny-file",
                str(proofdeps_c),
                *allow_args,
                "--exempt-specs-file",
                str(exempt_e),
                "--subset-allow",
                "--all-module-consts",
                "--summary-only",
                "Symbolic.Specifications.Refinement.Statement",
                "--import",
                "Symbolic.Specifications.Refinement.CliSetup",
                "--import",
                "Symbolic.Specifications.Security.AsmSecure",
                "--import",
                "Symbolic.Specifications.Refinement.RefinementPreservation",
            ],
            0,
            ["SUMMARY_STATUS=PASS", "SUMMARY_MACHINE_FREE=yes", "SUMMARY_ROOTS_FAILING=0"],
        )

        run_case(
            "P1b_root_report_pass",
            [
                *deny_args,
                "--deny-file",
                str(proofdeps_c),
                *allow_args,
                "--exempt-specs-file",
                str(exempt_e),
                "--subset-allow",
                "--root-report",
                "--bridges-file",
                str(bridges_txt),
                "Symbolic.Specifications.Refinement.Statement",
                "DY.Libsignal.Composed.Refinement.Cli.CompRefinesCli",
            ],
            0,
            [
                "ROOT_DEFAULT_TARGET_SCOPE=PASS",
                "ROOT_TYPE_GHOST_FREE=PASS",
                "ROOT_AXIOMS_STD3=PASS",
                "ROOT_REDUCE_GUARD=PASS",
                "SUMMARY_ROOT_REPORT=PASS",
                "SUMMARY_STATUS=PASS",
            ],
        )

        # P2: Mixed C module (Arm64.State lemma + pure layoutOffset); root that uses only
        # layoutOffset fails.
        p2_seeds = tmp_dir / "p2_seeds.txt"
        p2_seeds.write_text(f"{seed_base}\nScratchFixture.P2Root\n", encoding="utf-8")
        p2_c_out = tmp_dir / "p2_proofdeps.txt"
        run_case(
            "P2_step0_emit_c_for_mixed_mod",
            [
                *deny_args,
                *allow_args,
                "--exempt-specs-file",
                str(exempt_e),
                "--subset-allow",
                "--allow-scratch-fixture-roots",
                "--scratch-fixture-seeds-file",
                str(p2_seeds),
                "--emit-proofdeps",
                str(p2_c_out),
            ],
            0,
            ["SUMMARY_EMIT_PROOFDEPS=PASS"],
        )
        run_case(
            "P2_mixed_c_module_pure_const_fail",
            [
                *deny_args,
                "--deny-file",
                str(p2_c_out),
                "--no-allow",
                "ScratchFixture.P2Root",
                "ScratchFixture.P2Root.p2_uses_pure_const_of_c_mod",
            ],
            1,
            [
                "SUMMARY_STATUS=FAIL",
                "ScratchFixture.P2MixedCMod.layoutOffset [ScratchFixture.P2MixedCMod]",
            ],
        )

        # P3: Root that references Arm64.State through a wrapper fails under deny set A alone.
        run_case(
            "P3_part_a_via_wrapper_fail",
            [
                *deny_args,
                "--no-allow",
                "ScratchFixture.P3Root",
                "ScratchFixture.P3Root.p3_uses_part_a_via_wrapper",
            ],
            1,
            [
                "SUMMARY_STATUS=FAIL",
                "ScratchFixture.P3Wrapper.WrappedStatePred -> Arm64.State [Arm64.Trusted.ISA.State]",
            ],
        )

        # P4: Drift check: pure module with a new Arm64.State lemma fails as an uncovered
        # machine-level module.
        p4_seeds = tmp_dir / "p4_seeds.txt"
        p4_seeds.write_text(
            f"{seed_base}\n{bootstrap_extra}ScratchFixture.P4PureTurnedMachine\n",
            encoding="utf-8",
        )
        run_case(
            "P4_drift_uncovered_machine_module_fail",
            [
                *deny_args,
                *allow_args,
                "--exempt-specs-file",
                str(exempt_e),
                "--subset-allow",
                "--allow-scratch-fixture-roots",
                "--scratch-fixture-seeds-file",
                str(p4_seeds),
                "--check-proofdeps",
                str(proofdeps_c),
            ],
            1,
            [
                "UNCOVERED_MACHINE_MODULE: ScratchFixture.P4PureTurnedMachine",
                "SUMMARY_CHECK_PROOFDEPS=FAIL",
            ],
        )

        # P5: Transitive fixed-point criterion vs. --one-step debug mode (plain --criterion only).
        p5_seeds = tmp_dir / "p5_seeds.txt"
        p5_seeds.write_text(f"{seed_base}\nScratchFixture.P5Root\n", encoding="utf-8")
        p5_trans_c = tmp_dir / "p5_transitive_c.txt"
        p5_onestep_tsv = tmp_dir / "p5_onestep.tsv"
        run_case(
            "P5a_emit_transitive_criterion",
            [
                *deny_args,
                *allow_args,
                "--exempt-specs-file",
                str(exempt_e),
                "--subset-allow",
                "--allow-scratch-fixture-roots",
                "--scratch-fixture-seeds-file",
                str(p5_seeds),
                "--emit-proofdeps",
                str(p5_trans_c),
            ],
            0,
            ["SUMMARY_ONE_STEP_DEBUG=false", "SUMMARY_FIXED_POINT=true", "SUMMARY_EMIT_PROOFDEPS=PASS"],
        )
        run_case(
            "P5a_root_fail_under_transitive_criterion",
            [
                *deny_args,
                "--deny-file",
                str(p5_trans_c),
                "--no-allow",
                "ScratchFixture.P5Root",
                "ScratchFixture.P5Root.p5_uses_only_runBound",
            ],
            1,
            [
                "SUMMARY_STATUS=FAIL",
                "ScratchFixture.P5M2.runBound [ScratchFixture.P5M2]",
            ],
        )

        run_case(
            "P5b_criterion_onestep_debug",
            [
                *deny_args,
                *allow_args,
                "--exempt-specs-file",
                str(exempt_e),
                "--subset-allow",
                "--allow-scratch-fixture-roots",
                "--scratch-fixture-seeds-file",
                str(p5_seeds),
                "--criterion",
                "--one-step",
                "--criterion-tsv",
                str(p5_onestep_tsv),
            ],
            0,
            [
                "SUMMARY_ONE_STEP_DEBUG=true",
                "SUMMARY_STATUS=PASS",
                "CRITERION_TREE: ScratchFixture candidate_modules=3 machine_level=1 clean=2",
            ],
        )
        p5_tsv_lines = p5_onestep_tsv.read_text(encoding="utf-8").splitlines()
        p5m2_lines = [ln for ln in p5_tsv_lines if ln.startswith("ScratchFixture.P5M2\t")]
        if len(p5m2_lines) != 1 or "\t0\t-\t-\t" not in p5m2_lines[0]:
            raise RuntimeError(
                f"P5b_criterion_onestep_debug: expected P5M2 n_tainted=0 in {p5_onestep_tsv}, got:\n"
                + "\n".join(p5_tsv_lines)
            )

        # P6: Mixed module under Computational.* (Arm64.State lemma + pure def) fails when a root
        # references the pure def.
        p6_seeds = tmp_dir / "p6_seeds.txt"
        p6_seeds.write_text(f"{seed_base}\nComputational.ScratchFixtureP6Root\n", encoding="utf-8")
        p6_c = tmp_dir / "p6_proofdeps.txt"
        run_case(
            "P6_emit_computational_tree",
            [
                *deny_args,
                *allow_args,
                "--exempt-specs-file",
                str(exempt_e),
                "--subset-allow",
                "--allow-scratch-fixture-roots",
                "--scratch-fixture-seeds-file",
                str(p6_seeds),
                "--emit-proofdeps",
                str(p6_c),
            ],
            0,
            ["CRITERION_TREE: Computational.ScratchFixtureP6", "SUMMARY_EMIT_PROOFDEPS=PASS"],
        )
        run_case(
            "P6_computational_mixed_mod_fail",
            [
                *deny_args,
                "--deny-file",
                str(p6_c),
                "--no-allow",
                "Computational.ScratchFixtureP6Root",
                "Computational.ScratchFixtureP6Root.p6_uses_core_only_def",
            ],
            1,
            [
                "SUMMARY_STATUS=FAIL",
                "Computational.ScratchFixtureP6.coreOnlyDef [Computational.ScratchFixtureP6]",
            ],
        )

        # P7: Module under *.Specifications.* outside A and E with an Arm64.State def triggers
        # D2_FINDING.
        p7_seeds = tmp_dir / "p7_seeds.txt"
        p7_seeds.write_text(
            f"{seed_base}\n{bootstrap_extra}Symbolic.Specifications.ScratchFixtureP7\n",
            encoding="utf-8",
        )
        run_case(
            "P7_specifications_d2_finding_fail",
            [
                *deny_args,
                *allow_args,
                "--exempt-specs-file",
                str(exempt_e),
                "--subset-allow",
                "--allow-scratch-fixture-roots",
                "--scratch-fixture-seeds-file",
                str(p7_seeds),
                "--check-proofdeps",
                str(proofdeps_c),
            ],
            1,
            [
                "D2_FINDING: Symbolic.Specifications.ScratchFixtureP7",
                "SUMMARY_D2_FINDINGS=1",
                "SUMMARY_CHECK_PROOFDEPS=FAIL",
            ],
        )

        # P8a: CaDiCaL bv_decide lemma passes ROOT_REDUCE_GUARD (counted in RESIDUAL_BVD_AUX)
        # and fails ROOT_AXIOMS_STD3 due to its certificate axiom.
        run_case(
            "P8a_bv_decide_recognised_fails_std3",
            [
                *deny_args,
                "--no-allow",
                "--exempt-specs-file",
                str(exempt_e),
                "--root-report",
                "--allow-scratch-fixture-roots",
                "ScratchFixture.P8BvDecide",
                "ScratchFixture.P8BvDecide.p8_bvd_lemma",
            ],
            1,
            [
                "ROOT_REDUCE_GUARD=PASS",
                "ROOT_AXIOMS_STD3=FAIL",
                "RESIDUAL_BVD_AUX=3",
                "_native.bv_decide.ax_",
                "_expr_def",
                "_cert_def",
            ],
        )

        # P8b: native_decide lemma fails both ROOT_AXIOMS_STD3 and ROOT_REDUCE_GUARD.
        run_case(
            "P8b_native_decide_fail",
            [
                *deny_args,
                "--no-allow",
                "--exempt-specs-file",
                str(exempt_e),
                "--root-report",
                "--allow-scratch-fixture-roots",
                "ScratchFixture.P8NativeDecide",
                "ScratchFixture.P8NativeDecide.p8_native_lemma",
            ],
            1,
            [
                "ROOT_AXIOMS_STD3=FAIL",
                "ROOT_REDUCE_GUARD=FAIL",
                "_native.native_decide.ax_",
                "native_decide axiom forbidden",
            ],
        )

        # P9: Root that uses a constant from an exempt E-set module passes and reports it under
        # tag `E`.
        run_case(
            "P9_exempt_e_residual_report_pass",
            [
                *deny_args,
                "--deny-file",
                str(proofdeps_c),
                *allow_args,
                "--exempt-specs-file",
                str(exempt_e),
                "--subset-allow",
                "--root-report",
                "--allow-scratch-fixture-roots",
                "ScratchFixture.P9ExemptRoot",
                "ScratchFixture.P9ExemptRoot.p9_uses_exempt_e",
            ],
            0,
            [
                "SUMMARY_STATUS=PASS",
                "E\tDY.Libsignal.HwEvents.CliEvent\tSymbolic.Specifications.Concrete.MachineEvents",
                "ScratchFixture.P9ExemptRoot.p9CoreLiteral",
                '"p9-exempt-marker"',
            ],
        )

        # P10: When `simp` in a proof module realizes `eq_1` for a denied constant, a root that
        # uses `eq_1` fails with `eq_1` attributed to the denied parent's module.
        p10_deny = tmp_dir / "p10_deny.txt"
        p10_deny.write_text("[group p10]\nScratchFixture.P10DeniedMod\n", encoding="utf-8")
        run_case(
            "P10_realized_eq_of_denied_const_fail",
            [
                "--deny-file",
                str(p10_deny),
                "--no-allow",
                "ScratchFixture.P10Root",
                "ScratchFixture.P10Root.p10_uses_realized_eq",
            ],
            1,
            [
                "SUMMARY_STATUS=FAIL",
                "ScratchFixture.P10DeniedMod.secretOffset.eq_1 [ScratchFixture.P10DeniedMod]",
            ],
        )

        # PE2: Orphan root outside default Lake targets fails without --allow-scratch-fixture-roots.
        run_case(
            "PE2_orphan_root_outside_default_targets_fail",
            [
                *deny_args,
                "--deny-file",
                str(proofdeps_c),
                *allow_args,
                "--exempt-specs-file",
                str(exempt_e),
                "--subset-allow",
                "--root-report",
                "ScratchFixture.P9ExemptRoot",
                "ScratchFixture.P9ExemptRoot.p9_uses_exempt_e",
            ],
            1,
            [
                "ROOT_DEFAULT_TARGET_SCOPE=FAIL",
                "SUMMARY_STATUS=FAIL",
            ],
        )

        # CLI flag, parser, and operational negative controls (PF1–PF4, PN1–PN6).

        # PF1: --one-step is rejected by --gate, --emit-proofdeps, and --check-proofdeps (rc=2).
        run_case(
            "PF1a_gate_rejects_one_step",
            [
                *deny_args,
                *allow_args,
                "--exempt-specs-file",
                str(exempt_e),
                "--subset-allow",
                "--gate",
                "--criterion",
                "--one-step",
            ],
            2,
            ["--gate cannot be combined with --one-step"],
            include_overlay=False,
        )
        run_case(
            "PF1b_emit_rejects_one_step",
            [
                *deny_args,
                *allow_args,
                "--exempt-specs-file",
                str(exempt_e),
                "--subset-allow",
                "--allow-scratch-fixture-roots",
                "--scratch-fixture-seeds-file",
                str(p5_seeds),
                "--one-step",
                "--emit-proofdeps",
                str(tmp_dir / "pf1b_out.txt"),
            ],
            2,
            ["--one-step is only permitted with plain --criterion"],
        )
        run_case(
            "PF1c_check_rejects_one_step",
            [
                *deny_args,
                *allow_args,
                "--exempt-specs-file",
                str(exempt_e),
                "--subset-allow",
                "--allow-scratch-fixture-roots",
                "--scratch-fixture-seeds-file",
                str(p5_seeds),
                "--one-step",
                "--check-proofdeps",
                str(proofdeps_c),
            ],
            2,
            ["--one-step is only permitted with plain --criterion"],
        )

        # PF2: Realized lemma (`PF2Pure.pureFn.eq_1`) generated in a denied module (`PF2Realizer`)
        # whose proof value mentions `Arm64.State` taints `PF2Caller` outside A (rc=1).
        pf2_extra_deny = tmp_dir / "pf2_extra_deny.txt"
        pf2_extra_deny.write_text("[group pf2]\nScratchFixture.PF2Realizer\n", encoding="utf-8")
        pf2_deny_args = [*deny_args, "--deny-file", str(pf2_extra_deny)]
        pf2_base_seeds = tmp_dir / "pf2_base_seeds.txt"
        pf2_base_seeds.write_text(
            f"{seed_base}\nScratchFixture.P3Wrapper\nScratchFixture.PF2Pure\n", encoding="utf-8"
        )
        pf2_base_c = tmp_dir / "pf2_base_c.txt"
        run_case(
            "PF2_step0_emit_baseline_pure_clean",
            [
                *pf2_deny_args,
                *allow_args,
                "--exempt-specs-file",
                str(exempt_e),
                "--subset-allow",
                "--allow-scratch-fixture-roots",
                "--scratch-fixture-seeds-file",
                str(pf2_base_seeds),
                "--emit-proofdeps",
                str(pf2_base_c),
            ],
            0,
            ["SUMMARY_EMIT_PROOFDEPS=PASS"],
            must_not_contain=["ScratchFixture.PF2Pure", "ScratchFixture.PF2Caller"],
        )
        pf2_caller_seeds = tmp_dir / "pf2_caller_seeds.txt"
        pf2_caller_seeds.write_text(
            f"{seed_base}\nScratchFixture.P3Wrapper\nScratchFixture.PF2Caller\n", encoding="utf-8"
        )
        run_case(
            "PF2_realized_lemma_machine_dep_fail",
            [
                *pf2_deny_args,
                *allow_args,
                "--exempt-specs-file",
                str(exempt_e),
                "--subset-allow",
                "--allow-scratch-fixture-roots",
                "--scratch-fixture-seeds-file",
                str(pf2_caller_seeds),
                "--check-proofdeps",
                str(pf2_base_c),
            ],
            1,
            [
                "UNCOVERED_MACHINE_MODULE: ScratchFixture.PF2Caller",
                "SUMMARY_CHECK_PROOFDEPS=FAIL",
            ],
        )

        # PF3: Fail-closed `lakefile.lean` parser controls (rc=2 on unparsed @[default_target],
        # unexpected 0-seed library, and `/-` inside a string literal before a 0-seed library).
        def make_temp_lake_repo(name: str, lakefile_body: str) -> pathlib.Path:
            rdir = tmp_dir / name
            rdir.mkdir(parents=True, exist_ok=True)
            subprocess.run(
                ["git", "init", "-q"], cwd=str(rdir), check=True, capture_output=True, text=True
            )
            (rdir / "OkMod.lean").write_text("def okVal : Nat := 1\n", encoding="utf-8")
            (rdir / "lakefile.lean").write_text(lakefile_body, encoding="utf-8")
            return rdir

        pf3a_repo = make_temp_lake_repo(
            "pf3a_repo",
            "@[default_target]\nlean_lib OkMod where\n  roots := #[`OkMod]\n\n"
            "@[default_target]\nlean_exe UnparsedDefaultExe where\n  root := `OkMod\n",
        )
        run_case(
            "PF3a_lakefile_unparsed_default_target_fail",
            [
                "--deny-file",
                str(deny_a),
                "--no-allow",
                "--exempt-specs-file",
                str(exempt_e),
                "--criterion",
            ],
            2,
            ["@[default_target] count mismatch"],
            override_root=pf3a_repo,
            include_overlay=False,
        )

        pf3b_repo = make_temp_lake_repo(
            "pf3b_repo",
            "@[default_target]\nlean_lib OkMod where\n  roots := #[`OkMod]\n\n"
            "@[default_target]\nlean_lib UnexpectedEmptyLib where\n  roots := #[]\n",
        )
        run_case(
            "PF3b_lakefile_empty_seeds_fail",
            [
                "--deny-file",
                str(deny_a),
                "--no-allow",
                "--exempt-specs-file",
                str(exempt_e),
                "--criterion",
            ],
            2,
            ["@[default_target] lean_lib UnexpectedEmptyLib resolved to 0 seed modules"],
            override_root=pf3b_repo,
            include_overlay=False,
        )

        pf3c_repo = make_temp_lake_repo(
            "pf3c_repo",
            'def strWithCommentToken : String := "/- not a comment"\n\n'
            "@[default_target]\nlean_lib OkMod where\n  roots := #[`OkMod]\n\n"
            "@[default_target]\nlean_lib EmptyAfterString where\n  roots := #[]\n",
        )
        run_case(
            "PF3c_lakefile_comment_token_in_string_fail",
            [
                "--deny-file",
                str(deny_a),
                "--no-allow",
                "--exempt-specs-file",
                str(exempt_e),
                "--criterion",
            ],
            2,
            ["@[default_target] lean_lib EmptyAfterString resolved to 0 seed modules"],
            override_root=pf3c_repo,
            include_overlay=False,
        )

        # PN1: Exact `--check-proofdeps` matching (re-emit pass, stale clean module fail,
        # unmatched pattern fail, edited comment header pass, non-canonical body fail,
        # in-body comment fail).
        pn1_seeds = tmp_dir / "pn1_seeds.txt"
        pn1_seeds.write_text(f"{seed_base}\nScratchFixture.P3Wrapper\n", encoding="utf-8")
        pn1_c = tmp_dir / "pn1_exact_c.txt"
        run_case(
            "PN1_step0_emit_exact_c",
            [
                *deny_args,
                *allow_args,
                "--exempt-specs-file",
                str(exempt_e),
                "--subset-allow",
                "--allow-scratch-fixture-roots",
                "--scratch-fixture-seeds-file",
                str(pn1_seeds),
                "--emit-proofdeps",
                str(pn1_c),
            ],
            0,
            ["SUMMARY_EMIT_PROOFDEPS=PASS"],
        )
        run_case(
            "PN1d_exact_reemit_check_pass",
            [
                *deny_args,
                *allow_args,
                "--exempt-specs-file",
                str(exempt_e),
                "--subset-allow",
                "--allow-scratch-fixture-roots",
                "--scratch-fixture-seeds-file",
                str(pn1_seeds),
                "--check-proofdeps",
                str(pn1_c),
            ],
            0,
            [
                "SUMMARY_PROOFDEPS_EXACT_MATCH=PASS",
                "SUMMARY_CHECK_PROOFDEPS=PASS",
            ],
        )

        pn1_orig_txt = pn1_c.read_text(encoding="utf-8")
        pn1a_c = tmp_dir / "pn1a_stale_clean_c.txt"
        pn1a_c.write_text(
            pn1_orig_txt + "Symbolic.Specifications.Refinement.CliSetup\n",
            encoding="utf-8",
        )
        run_case(
            "PN1a_stale_clean_pattern_fail",
            [
                *deny_args,
                *allow_args,
                "--exempt-specs-file",
                str(exempt_e),
                "--subset-allow",
                "--allow-scratch-fixture-roots",
                "--scratch-fixture-seeds-file",
                str(pn1_seeds),
                "--check-proofdeps",
                str(pn1a_c),
            ],
            1,
            [
                "STALE_COVERED_CLEAN_MODULE: Symbolic.Specifications.Refinement.CliSetup",
                "SUMMARY_CHECK_PROOFDEPS=FAIL",
            ],
        )

        pn1b_c = tmp_dir / "pn1b_unmatched_deleted_c.txt"
        pn1b_c.write_text(
            pn1_orig_txt + "ScratchFixture.DeletedNonexistentModule\n",
            encoding="utf-8",
        )
        run_case(
            "PN1b_unmatched_deleted_pattern_fail",
            [
                *deny_args,
                *allow_args,
                "--exempt-specs-file",
                str(exempt_e),
                "--subset-allow",
                "--allow-scratch-fixture-roots",
                "--scratch-fixture-seeds-file",
                str(pn1_seeds),
                "--check-proofdeps",
                str(pn1b_c),
            ],
            1,
            [
                "UNMATCHED_PROOFDEPS_PATTERN: ScratchFixture.DeletedNonexistentModule",
                "SUMMARY_CHECK_PROOFDEPS=FAIL",
            ],
        )

        # Leading `#` comment lines are informational and ignored by `--check-proofdeps`.
        pn1c_c = tmp_dir / "pn1c_edited_header_c.txt"
        pn1c_c.write_text(
            "# Edited comment header: --check-proofdeps compares only the body.\n" + pn1_orig_txt,
            encoding="utf-8",
        )
        run_case(
            "PN1c_edited_comment_header_pass",
            [
                *deny_args,
                *allow_args,
                "--exempt-specs-file",
                str(exempt_e),
                "--subset-allow",
                "--allow-scratch-fixture-roots",
                "--scratch-fixture-seeds-file",
                str(pn1_seeds),
                "--check-proofdeps",
                str(pn1c_c),
            ],
            0,
            [
                "SUMMARY_PROOFDEPS_EXACT_MATCH=PASS",
                "SUMMARY_CHECK_PROOFDEPS=PASS",
            ],
        )

        # Non-canonical body formatting (here, a trailing blank line) fails even when the covered
        # module set matches `--emit-proofdeps`.
        pn1e_c = tmp_dir / "pn1e_noncanonical_body_c.txt"
        pn1e_c.write_text(pn1_orig_txt + "\n", encoding="utf-8")
        run_case(
            "PN1e_noncanonical_body_fail",
            [
                *deny_args,
                *allow_args,
                "--exempt-specs-file",
                str(exempt_e),
                "--subset-allow",
                "--allow-scratch-fixture-roots",
                "--scratch-fixture-seeds-file",
                str(pn1_seeds),
                "--check-proofdeps",
                str(pn1e_c),
            ],
            1,
            [
                "PROOFDEPS_BODY_MISMATCH",
                "SUMMARY_UNCOVERED_MODULES=0",
                "SUMMARY_STALE_CLEAN_COVERED=0",
                "SUMMARY_UNMATCHED_PROOFDEPS_PATTERNS=0",
                "SUMMARY_PROOFDEPS_EXACT_MATCH=FAIL",
                "SUMMARY_CHECK_PROOFDEPS=FAIL",
            ],
        )

        # Only leading `#` and blank lines are ignored; comments inside the body fail.
        pn1f_c = tmp_dir / "pn1f_comment_in_body_c.txt"
        assert "[group proofdeps]\n" in pn1_orig_txt
        pn1f_c.write_text(
            pn1_orig_txt.replace("[group proofdeps]\n", "[group proofdeps]\n# note\n", 1),
            encoding="utf-8",
        )
        run_case(
            "PN1f_comment_inside_body_fail",
            [
                *deny_args,
                *allow_args,
                "--exempt-specs-file",
                str(exempt_e),
                "--subset-allow",
                "--allow-scratch-fixture-roots",
                "--scratch-fixture-seeds-file",
                str(pn1_seeds),
                "--check-proofdeps",
                str(pn1f_c),
            ],
            1,
            [
                "PROOFDEPS_BODY_MISMATCH",
                "SUMMARY_UNCOVERED_MODULES=0",
                "SUMMARY_STALE_CLEAN_COVERED=0",
                "SUMMARY_UNMATCHED_PROOFDEPS_PATTERNS=0",
                "SUMMARY_PROOFDEPS_EXACT_MATCH=FAIL",
                "SUMMARY_CHECK_PROOFDEPS=FAIL",
            ],
        )

        # PF4: `--gate --root-report` requires `--expected-root-type-file` (rc=2), checks that
        # `--expected-root-type-file` and `--bridges-file` match `HEAD` (rc=1), and fails on
        # expected-type mismatch (rc=1).
        run_case(
            "PF4a_gate_root_report_missing_expected_type_fail",
            [
                *deny_args,
                *allow_args,
                "--exempt-specs-file",
                str(exempt_e),
                "--subset-allow",
                "--gate",
                "--root-report",
                "Symbolic.Specifications.Refinement.Statement",
                "DY.Libsignal.Composed.Refinement.Cli.CompRefinesCli",
            ],
            2,
            ["--gate --root-report requires --expected-root-type-file <PATH>"],
            include_overlay=False,
        )

        pf4b_repo = tmp_dir / "pf4b_repo"
        pf4b_repo.mkdir(parents=True, exist_ok=True)
        subprocess.run(
            ["git", "init", "-q"], cwd=str(pf4b_repo), check=True, capture_output=True, text=True
        )
        subprocess.run(
            ["git", "config", "user.email", "test@example.com"],
            cwd=str(pf4b_repo),
            check=True,
            capture_output=True,
            text=True,
        )
        subprocess.run(
            ["git", "config", "user.name", "Test"],
            cwd=str(pf4b_repo),
            check=True,
            capture_output=True,
            text=True,
        )
        subprocess.run(
            ["git", "config", "commit.gpgsign", "false"],
            cwd=str(pf4b_repo),
            check=True,
            capture_output=True,
            text=True,
        )
        (pf4b_repo / "deny.txt").write_text("[group 1]\nArm64.*\n", encoding="utf-8")
        (pf4b_repo / "allow.txt").write_text(
            "# read at engine submodule 000000000\n", encoding="utf-8"
        )
        (pf4b_repo / "exempt.txt").write_text("# empty\n", encoding="utf-8")
        subprocess.run(
            ["git", "add", "deny.txt", "allow.txt", "exempt.txt"],
            cwd=str(pf4b_repo),
            check=True,
            capture_output=True,
            text=True,
        )
        subprocess.run(
            ["git", "commit", "-q", "-m", "init"],
            cwd=str(pf4b_repo),
            check=True,
            capture_output=True,
            text=True,
        )
        (pf4b_repo / "uncommitted_bridges.txt").write_text("Nat.add_comm : test\n", encoding="utf-8")
        (pf4b_repo / "uncommitted_expected_type.txt").write_text("Bool.true : Bool\n", encoding="utf-8")
        run_case(
            "PF4b_gate_uncommitted_expected_type_and_bridges_fail",
            [
                "--gate",
                "--deny-file",
                str(pf4b_repo / "deny.txt"),
                "--allow-file",
                str(pf4b_repo / "allow.txt"),
                "--exempt-specs-file",
                str(pf4b_repo / "exempt.txt"),
                "--root-report",
                "--bridges-file",
                str(pf4b_repo / "uncommitted_bridges.txt"),
                "--expected-root-type-file",
                str(pf4b_repo / "uncommitted_expected_type.txt"),
                "Init.Core",
                "Bool.true",
            ],
            1,
            [
                "BRIDGES_FILE uncommitted_bridges.txt",
                "EXPECTED_ROOT_TYPE_FILE uncommitted_expected_type.txt",
                "is not committed at HEAD=",
                "SUMMARY_GATE_STATUS=FAIL",
            ],
            override_root=pf4b_repo,
            include_overlay=False,
        )

        pf4c_bad_type = tmp_dir / "pf4c_bad_expected_type.txt"
        pf4c_bad_type.write_text(
            "DY.Libsignal.Composed.Refinement.Cli.CompRefinesCli : False\n",
            encoding="utf-8",
        )
        run_case(
            "PF4c_expected_root_type_mismatch_fail",
            [
                *deny_args,
                "--deny-file",
                str(proofdeps_c),
                *allow_args,
                "--exempt-specs-file",
                str(exempt_e),
                "--subset-allow",
                "--root-report",
                "--expected-root-type-file",
                str(pf4c_bad_type),
                "Symbolic.Specifications.Refinement.Statement",
                "DY.Libsignal.Composed.Refinement.Cli.CompRefinesCli",
            ],
            1,
            [
                "ROOT_EXPECTED_TYPE_MATCH=FAIL",
                "SUMMARY_ROOT_EXPECTED_TYPE=FAIL",
                "SUMMARY_STATUS=FAIL",
            ],
        )

        # PN2: `--exempt-specs-file` rejects modules without a `Specifications` path segment (rc=2).
        pn2_bad_exempt = tmp_dir / "pn2_bad_exempt.txt"
        pn2_bad_exempt.write_text("ScratchFixture.P3Wrapper\n", encoding="utf-8")
        run_case(
            "PN2_exempt_non_specifications_fail",
            [
                *deny_args,
                *allow_args,
                "--exempt-specs-file",
                str(pn2_bad_exempt),
                "--subset-allow",
                "--allow-scratch-fixture-roots",
                "--scratch-fixture-seeds-file",
                str(pn1_seeds),
                "--criterion",
            ],
            2,
            ["lacks a 'Specifications' path segment"],
        )

        # PN3: Plain `--criterion` exits with `rc=1` when `D2_FINDING` count > 0.
        run_case(
            "PN3_criterion_d2_rc_fail",
            [
                *deny_args,
                *allow_args,
                "--exempt-specs-file",
                str(exempt_e),
                "--subset-allow",
                "--allow-scratch-fixture-roots",
                "--scratch-fixture-seeds-file",
                str(p7_seeds),
                "--criterion",
            ],
            1,
            [
                "D2_FINDING: Symbolic.Specifications.ScratchFixtureP7",
                "SUMMARY_D2_FINDINGS=1",
                "SUMMARY_STATUS=FAIL",
            ],
        )

        # PN4: Unterminated block comment in a scanned module fails closed (`rc=2`) in
        # `--root-report`.
        pn4_repo = make_temp_lake_repo(
            "pn4_repo",
            "@[default_target]\nlean_lib OkMod where\n  roots := #[`OkMod]\n",
        )
        (pn4_repo / "OkMod.lean").write_text("/- unterminated comment\ndef x := 1\n", encoding="utf-8")
        run_case(
            "PN4_unterminated_comment_in_closure_fail",
            [
                "--deny-file",
                str(deny_a),
                "--no-allow",
                "--exempt-specs-file",
                str(exempt_e),
                "--root-report",
                "OkMod",
                "OkMod.x",
            ],
            2,
            ["unterminated block comment '/-' in Lean source"],
            override_root=pn4_repo,
            include_overlay=False,
        )

        # PN5: Lean child timeout sends `SIGKILL` and exits with `rc=2`.
        run_case(
            "PN5_child_timeout_fail",
            [
                *deny_args,
                *allow_args,
                "--subset-allow",
                "--timeout-sec",
                "0.001",
                "--all-module-consts",
                "Symbolic.Specifications.Refinement.Statement",
            ],
            2,
            ["lean child timed out after 0.001s"],
        )

        # PN6: Symlinked native cache directory fails closed (`rc=2`).
        pn6_tmp_parent = tmp_dir / "pn6_tmpdir"
        pn6_tmp_parent.mkdir(parents=True, exist_ok=True)
        pn6_target = tmp_dir / "pn6_real_dir"
        pn6_target.mkdir(parents=True, exist_ok=True)
        os.symlink(pn6_target, pn6_tmp_parent / f"mfc_native_cache_{os.getuid()}")
        pn6_env = os.environ.copy()
        pn6_env["TMPDIR"] = str(pn6_tmp_parent)
        pn6_env["LEAN_ABORT_ON_PANIC"] = "1"
        pn6_proc = subprocess.run(
            [
                sys.executable,
                str(mfc_py),
                "--root",
                str(repo_root),
                "--deny-file",
                str(deny_a),
                "--no-allow",
                "Init.Core",
                "Bool.true",
            ],
            cwd=str(repo_root),
            env=pn6_env,
            capture_output=True,
            text=True,
            check=False,
        )
        pn6_comb = pn6_proc.stdout + ("\n" + pn6_proc.stderr if pn6_proc.stderr else "")
        report_blocks.append(
            f"=== CONTROL PN6_symlink_native_cache_fail (expected_rc=2, actual_rc={pn6_proc.returncode}) ===\n"
            f"$ TMPDIR=<symlinked-cache> python3 Symbolic/scripts/machine_free_check.py --deny-file {deny_a} --no-allow Init.Core Bool.true\n"
            f"{pn6_proc.stdout.rstrip()}\n"
            f"[stderr] {pn6_proc.stderr.strip()}\n"
        )
        if pn6_proc.returncode != 2 or "unsafe native cache directory" not in pn6_comb:
            raise RuntimeError(
                f"PN6_symlink_native_cache_fail: expected rc=2 'unsafe native cache directory', got rc={pn6_proc.returncode}\n{pn6_comb}"
            )
        print("[run-controls] PASS PN6_symlink_native_cache_fail (rc=2)")

        # Allow-listed realized lemma soundness across all three analysis paths (PF5).

        # PF5: Allow-listed realized lemma (`PF5DeniedParent.parentFn.eq_1`) of a denied parent,
        # realized in an analyzed candidate module (`PF5Realizer`) with `Arm64.State` in its proof
        # value, must taint `PF5Caller` (`rc=1`) under the fast path, `--legacy-slow-edges`, and
        # `--root-report`.
        gitlink_sha, _ = mfc.read_repo_engine_gitlink(repo_root)
        pf5_extra_deny = tmp_dir / "pf5_extra_deny.txt"
        pf5_extra_deny.write_text("[group pf5]\nScratchFixture.PF5DeniedParent\n", encoding="utf-8")
        pf5_extra_allow = tmp_dir / "pf5_extra_allow.txt"
        pf5_extra_allow.write_text(
            f"# read at engine submodule {gitlink_sha[:12]}\n"
            "ScratchFixture.PF5DeniedParent.parentFn : pf5 allowed denied-module parent\n"
            "ScratchFixture.PF5DeniedParent.parentFn.eq_1 : pf5 allowed realized lemma in candidate mod\n",
            encoding="utf-8",
        )
        pf5_deny_args = [*deny_args, "--deny-file", str(pf5_extra_deny)]
        pf5_allow_args = [*allow_args, "--allow-file", str(pf5_extra_allow)]
        pf5_base_seeds = tmp_dir / "pf5_base_seeds.txt"
        pf5_base_seeds.write_text(f"{seed_base}\nScratchFixture.P3Wrapper\n", encoding="utf-8")
        pf5_base_c = tmp_dir / "pf5_base_c.txt"
        run_case(
            "PF5_step0_emit_baseline_clean",
            [
                *pf5_deny_args,
                *pf5_allow_args,
                "--exempt-specs-file",
                str(exempt_e),
                "--subset-allow",
                "--allow-scratch-fixture-roots",
                "--scratch-fixture-seeds-file",
                str(pf5_base_seeds),
                "--emit-proofdeps",
                str(pf5_base_c),
            ],
            0,
            ["SUMMARY_EMIT_PROOFDEPS=PASS"],
            must_not_contain=["ScratchFixture.PF5Realizer", "ScratchFixture.PF5Caller"],
        )

        pf5_caller_seeds = tmp_dir / "pf5_caller_seeds.txt"
        pf5_caller_seeds.write_text(
            f"{seed_base}\nScratchFixture.P3Wrapper\nScratchFixture.PF5Caller\n",
            encoding="utf-8",
        )
        run_case(
            "PF5a_allowed_denied_parent_realized_default_fail",
            [
                *pf5_deny_args,
                *pf5_allow_args,
                "--exempt-specs-file",
                str(exempt_e),
                "--subset-allow",
                "--allow-scratch-fixture-roots",
                "--scratch-fixture-seeds-file",
                str(pf5_caller_seeds),
                "--check-proofdeps",
                str(pf5_base_c),
            ],
            1,
            [
                "UNCOVERED_MACHINE_MODULE: ScratchFixture.PF5Caller",
                "UNCOVERED_MACHINE_MODULE: ScratchFixture.PF5Realizer",
                "ScratchFixture.PF5DeniedParent.parentFn.eq_1 -> Arm64.State [Arm64.Trusted.ISA.State]",
                "SUMMARY_CHECK_PROOFDEPS=FAIL",
            ],
        )
        run_case(
            "PF5b_allowed_denied_parent_realized_legacy_fail",
            [
                *pf5_deny_args,
                *pf5_allow_args,
                "--exempt-specs-file",
                str(exempt_e),
                "--subset-allow",
                "--allow-scratch-fixture-roots",
                "--scratch-fixture-seeds-file",
                str(pf5_caller_seeds),
                "--legacy-slow-edges",
                "--check-proofdeps",
                str(pf5_base_c),
            ],
            1,
            [
                "UNCOVERED_MACHINE_MODULE: ScratchFixture.PF5Caller",
                "UNCOVERED_MACHINE_MODULE: ScratchFixture.PF5Realizer",
                "ScratchFixture.PF5DeniedParent.parentFn.eq_1 -> Arm64.State [Arm64.Trusted.ISA.State]",
                "SUMMARY_CHECK_PROOFDEPS=FAIL",
            ],
        )
        run_case(
            "PF5c_allowed_denied_parent_realized_root_mode_fail",
            [
                *pf5_deny_args,
                "--deny-file",
                str(pf5_base_c),
                *pf5_allow_args,
                "--exempt-specs-file",
                str(exempt_e),
                "--subset-allow",
                "--root-report",
                "--allow-scratch-fixture-roots",
                "ScratchFixture.PF5Caller",
                "ScratchFixture.PF5Caller.pf5_caller",
            ],
            1,
            [
                "MACHINE_FREE=no",
                "ScratchFixture.PF5Caller.pf5_caller -> ScratchFixture.PF5DeniedParent.parentFn.eq_1 -> Arm64.State [Arm64.Trusted.ISA.State]",
                "SUMMARY_STATUS=FAIL",
            ],
        )

        # Parent attribution controls for `_simp_<digits>` declarations.
        prow87_extra_deny = tmp_dir / "prow87_extra_deny.txt"
        prow87_extra_deny.write_text(
            "[group prow87]\nScratchFixture.PRow87DeniedRealizer\n", encoding="utf-8"
        )
        prow87_deny_args = [*deny_args, "--deny-file", str(prow87_extra_deny)]
        prow87_base_seeds = tmp_dir / "prow87_base_seeds.txt"
        prow87_base_seeds.write_text(
            f"{seed_base}\nScratchFixture.P3Wrapper\n", encoding="utf-8"
        )
        prow87_base_c = tmp_dir / "prow87_base_c.txt"
        run_case(
            "PRow87_step0_emit_baseline_clean",
            [
                *prow87_deny_args,
                *allow_args,
                "--exempt-specs-file",
                str(exempt_e),
                "--subset-allow",
                "--allow-scratch-fixture-roots",
                "--scratch-fixture-seeds-file",
                str(prow87_base_seeds),
                "--emit-proofdeps",
                str(prow87_base_c),
            ],
            0,
            ["SUMMARY_EMIT_PROOFDEPS=PASS"],
        )

        # (a) Core parent with pure value realized in a denied module stays clean.
        prow87a_seeds = tmp_dir / "prow87a_seeds.txt"
        prow87a_seeds.write_text(
            f"{seed_base}\nScratchFixture.P3Wrapper\nScratchFixture.PRow87CallerPureCore\n",
            encoding="utf-8",
        )
        run_case(
            "PRow87a_core_parent_pure_criterion_clean",
            [
                *prow87_deny_args,
                *allow_args,
                "--exempt-specs-file",
                str(exempt_e),
                "--subset-allow",
                "--allow-scratch-fixture-roots",
                "--scratch-fixture-seeds-file",
                str(prow87a_seeds),
                "--check-proofdeps",
                str(prow87_base_c),
            ],
            0,
            [
                "SUMMARY_PROOFDEPS_EXACT_MATCH=PASS",
                "SUMMARY_CHECK_PROOFDEPS=PASS",
            ],
            must_not_contain=["ScratchFixture.PRow87CallerPureCore"],
        )
        run_case(
            "PRow87a_core_parent_pure_root_clean",
            [
                *prow87_deny_args,
                "--deny-file",
                str(prow87_base_c),
                *allow_args,
                "--exempt-specs-file",
                str(exempt_e),
                "--subset-allow",
                "--root-report",
                "--allow-scratch-fixture-roots",
                "ScratchFixture.PRow87CallerPureCore",
                "ScratchFixture.PRow87CallerPureCore.prow87_pure_core",
            ],
            0,
            [
                "MACHINE_FREE=yes",
                "SUMMARY_STATUS=PASS",
            ],
        )

        # (b) Denied parent realized in a clean module is tainted.
        prow87b_seeds = tmp_dir / "prow87b_seeds.txt"
        prow87b_seeds.write_text(
            f"{seed_base}\nScratchFixture.P3Wrapper\nScratchFixture.PRow87CallerDeniedParent\n",
            encoding="utf-8",
        )
        run_case(
            "PRow87b_denied_parent_criterion_fail",
            [
                *prow87_deny_args,
                *allow_args,
                "--exempt-specs-file",
                str(exempt_e),
                "--subset-allow",
                "--allow-scratch-fixture-roots",
                "--scratch-fixture-seeds-file",
                str(prow87b_seeds),
                "--check-proofdeps",
                str(prow87_base_c),
            ],
            1,
            [
                "UNCOVERED_MACHINE_MODULE: ScratchFixture.PRow87CallerDeniedParent",
                "ScratchFixture.PRow87DeniedRealizer.deniedParentThm._simp_8702 [ScratchFixture.PRow87DeniedRealizer]",
                "SUMMARY_CHECK_PROOFDEPS=FAIL",
            ],
        )
        run_case(
            "PRow87b_denied_parent_root_fail",
            [
                *prow87_deny_args,
                "--deny-file",
                str(prow87_base_c),
                *allow_args,
                "--exempt-specs-file",
                str(exempt_e),
                "--subset-allow",
                "--root-report",
                "--allow-scratch-fixture-roots",
                "ScratchFixture.PRow87CallerDeniedParent",
                "ScratchFixture.PRow87CallerDeniedParent.prow87_denied_parent",
            ],
            1,
            [
                "MACHINE_FREE=no",
                "ScratchFixture.PRow87DeniedRealizer.deniedParentThm._simp_8702 [ScratchFixture.PRow87DeniedRealizer]",
                "SUMMARY_STATUS=FAIL",
            ],
        )

        # (c) Core parent whose value mentions `Arm64.State` is tainted across all three paths.
        prow87c_seeds = tmp_dir / "prow87c_seeds.txt"
        prow87c_seeds.write_text(
            f"{seed_base}\nScratchFixture.P3Wrapper\nScratchFixture.PRow87CallerBadVal\n",
            encoding="utf-8",
        )
        run_case(
            "PRow87c1_bad_value_default_fail",
            [
                *prow87_deny_args,
                *allow_args,
                "--exempt-specs-file",
                str(exempt_e),
                "--subset-allow",
                "--allow-scratch-fixture-roots",
                "--scratch-fixture-seeds-file",
                str(prow87c_seeds),
                "--check-proofdeps",
                str(prow87_base_c),
            ],
            1,
            [
                "UNCOVERED_MACHINE_MODULE: ScratchFixture.PRow87CallerBadVal",
                "Classical.not_not._simp_8703 -> Arm64.State [Arm64.Trusted.ISA.State]",
                "SUMMARY_CHECK_PROOFDEPS=FAIL",
            ],
        )
        run_case(
            "PRow87c2_bad_value_legacy_fail",
            [
                *prow87_deny_args,
                *allow_args,
                "--exempt-specs-file",
                str(exempt_e),
                "--subset-allow",
                "--allow-scratch-fixture-roots",
                "--scratch-fixture-seeds-file",
                str(prow87c_seeds),
                "--legacy-slow-edges",
                "--check-proofdeps",
                str(prow87_base_c),
            ],
            1,
            [
                "UNCOVERED_MACHINE_MODULE: ScratchFixture.PRow87CallerBadVal",
                "Classical.not_not._simp_8703 -> Arm64.State [Arm64.Trusted.ISA.State]",
                "SUMMARY_CHECK_PROOFDEPS=FAIL",
            ],
        )
        run_case(
            "PRow87c3_bad_value_root_fail",
            [
                *prow87_deny_args,
                "--deny-file",
                str(prow87_base_c),
                *allow_args,
                "--exempt-specs-file",
                str(exempt_e),
                "--subset-allow",
                "--root-report",
                "--allow-scratch-fixture-roots",
                "ScratchFixture.PRow87CallerBadVal",
                "ScratchFixture.PRow87CallerBadVal.prow87_bad_val",
            ],
            1,
            [
                "MACHINE_FREE=no",
                "Classical.not_not._simp_8703 -> Arm64.State [Arm64.Trusted.ISA.State]",
                "SUMMARY_STATUS=FAIL",
            ],
        )

        # (d) `axiom Classical.not_not._simp_8704` (no declRange, `.axiomInfo`) in a denied module
        # is tainted.
        prow87d_seeds = tmp_dir / "prow87d_seeds.txt"
        prow87d_seeds.write_text(
            f"{seed_base}\nScratchFixture.P3Wrapper\nScratchFixture.PRow87CallerAxiom\n",
            encoding="utf-8",
        )
        run_case(
            "PRow87d_axiom_simp_suffix_criterion_fail",
            [
                *prow87_deny_args,
                *allow_args,
                "--exempt-specs-file",
                str(exempt_e),
                "--subset-allow",
                "--allow-scratch-fixture-roots",
                "--scratch-fixture-seeds-file",
                str(prow87d_seeds),
                "--check-proofdeps",
                str(prow87_base_c),
            ],
            1,
            [
                "UNCOVERED_MACHINE_MODULE: ScratchFixture.PRow87CallerAxiom",
                "Classical.not_not._simp_8704 [ScratchFixture.PRow87DeniedRealizer]",
                "SUMMARY_CHECK_PROOFDEPS=FAIL",
            ],
        )
        run_case(
            "PRow87d_axiom_simp_suffix_root_fail",
            [
                *prow87_deny_args,
                "--deny-file",
                str(prow87_base_c),
                *allow_args,
                "--exempt-specs-file",
                str(exempt_e),
                "--subset-allow",
                "--root-report",
                "--allow-scratch-fixture-roots",
                "ScratchFixture.PRow87CallerAxiom",
                "ScratchFixture.PRow87CallerAxiom.prow87_axiom",
            ],
            1,
            [
                "MACHINE_FREE=no",
                "Classical.not_not._simp_8704 [ScratchFixture.PRow87DeniedRealizer]",
                "SUMMARY_STATUS=FAIL",
            ],
        )

        # (e) User-written `theorem Nat.add_comm._simp_7` (has declRange) in a denied module is
        # tainted.
        prow87e_seeds = tmp_dir / "prow87e_seeds.txt"
        prow87e_seeds.write_text(
            f"{seed_base}\nScratchFixture.P3Wrapper\nScratchFixture.PRow87CallerUserDecl\n",
            encoding="utf-8",
        )
        run_case(
            "PRow87e_user_decl_declrange_criterion_fail",
            [
                *prow87_deny_args,
                *allow_args,
                "--exempt-specs-file",
                str(exempt_e),
                "--subset-allow",
                "--allow-scratch-fixture-roots",
                "--scratch-fixture-seeds-file",
                str(prow87e_seeds),
                "--check-proofdeps",
                str(prow87_base_c),
            ],
            1,
            [
                "UNCOVERED_MACHINE_MODULE: ScratchFixture.PRow87CallerUserDecl",
                "Nat.add_comm._simp_7 [ScratchFixture.PRow87DeniedRealizer]",
                "SUMMARY_CHECK_PROOFDEPS=FAIL",
            ],
        )
        run_case(
            "PRow87e_user_decl_declrange_root_fail",
            [
                *prow87_deny_args,
                "--deny-file",
                str(prow87_base_c),
                *allow_args,
                "--exempt-specs-file",
                str(exempt_e),
                "--subset-allow",
                "--root-report",
                "--allow-scratch-fixture-roots",
                "ScratchFixture.PRow87CallerUserDecl",
                "ScratchFixture.PRow87CallerUserDecl.prow87_user_decl",
            ],
            1,
            [
                "MACHINE_FREE=no",
                "Nat.add_comm._simp_7 [ScratchFixture.PRow87DeniedRealizer]",
                "SUMMARY_STATUS=FAIL",
            ],
        )

        full_report = "\n".join(report_blocks)
        if args.report_out:
            out_p = pathlib.Path(args.report_out).resolve()
            out_p.parent.mkdir(parents=True, exist_ok=True)
            out_p.write_text(full_report, encoding="utf-8")
            print(f"[run-controls] wrote verbatim report ({len(full_report)} bytes) to {out_p}")
        print("[run-controls] ALL CONTROLS P1–P10 + E2 + ROW-162/179/87 (PF1–PF5, PN1–PN6, PRow87a–e) PASSED")
        return 0
    finally:
        shutil.rmtree(tmp_dir, ignore_errors=True)


if __name__ == "__main__":
    sys.exit(main())
