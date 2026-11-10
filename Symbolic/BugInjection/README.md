# Bug Injection

## Overview

Each bug in this directory is a Rust patch against `libsignal`: either a reversed upstream fix commit (`kind = "upstream"`, the default) or a forward regression patch against `v0.105.4` (`kind = "synthetic"`, documented in [`Synthetic/README.md`](Synthetic/README.md)). A **witness** pairs a sequence of CLI calls and attacker inputs with the trace `evs` of structured `CliEvent` records produced by the patched `libsignal-cli` binary.

A witness refutes the headline theorem `signal_session_secure_placed : SignalSessionSecurePlaced cliElfBytes` (`Symbolic/Theorems/Security.lean`) on the patched binary by proving `¬ SignalSessionSecurePlaced mutantCliElfBytes` (or `¬ SignalSessionSecure mutantCliElfBytes` on the fixed-image companion predicate for synthetic mutants), where `mutantCliElfBytes` is the mutant's `libsignal-cli` AArch64 ELF built by the legacy snapshot recipe (D6) until M5 (`scripts/cli-elf --build`, from `cli-elf/inputs.lock`; `cliElfBytes` uses the stock `ld.lld` link) with the bug patch applied. Via `not_refines_of_witness` (`Split.lean`) and its CLI instantiation `not_signalSessionSecurePlaced_of_witness` (`Witnesses/CliShapePlaced.lean`, or `not_signalSessionSecure_of_witness` in `Witnesses/CliShape.lean`), the refutation splits into two halves:

- **Spec half `(S)`** (statement only): for every primitive interpretation and setup record satisfying `fits`, the records are well-formed and no symbolic execution (`Explains`) or collision excuse (`CollisionAtCli`) permitted by `SignalSessionSecurePlaced` accounts for `evs`.
- **Implementation half `(I)`** (mutant binary only): some pair satisfying `fits` meets the binary's external contracts, and the parsed ELF `mutantCliElfBytes` (at linked placements `(mpl, mmpl)`) produces `evs` under fresh randomness (`CoinsFresh`).

Together `(S)` and `(I)` imply `¬ SignalSessionSecurePlaced mutantCliElfBytes`. Because `SignalSessionSecurePlaced` holds for the unpatched `cliElfBytes`, `(S)` also implies the unpatched binary cannot produce `evs`.

External cryptographic primitives cannot be fixed to concrete X25519 or ML-KEM implementations inside the specification. Quantifying `(S)` universally and `(I)` existentially over a predicate `fits` keeps `(S)` independent of the machine image while restricting to well-behaved primitives: `cliCompFits` pairs `compFits` (well-formed setup records, `ExternCryptoLawsHold`, `X25519PubCanonical`, and `CompKyberCorrectOn` on trace ciphertexts) with the machine-free CLI contracts `ExternContractsHoldCli` and `HooksMatchInterpretation`.

Each `NonVacuity/<Witness>.lean` module proves `nonvacuous : ∃ i r, fits i r` in the default `lake build` (`decide +kernel` via `cliCompFits_satisfiable` in `NonVacuity/CliSatisfiable.lean`), ensuring `(S)` does not hold vacuously. Because `fits` constrains X25519, AES, and Kyber on `evs` while leaving HMAC, HKDF, XEdDSA, and SPQR uninterpreted, each witness documents which collision excuses (`CollisionAfterExplainedPrefix`) its spec argument assumes do not hold.

## Running

Prerequisites match [`README.md`](../../README.md): `elan`, the pinned Rust toolchain (`rust-toolchain.toml`), `protoc`, and the toolchain of the legacy snapshot recipe (D6) until M5, `scripts/cli-elf --build` (Zig `0.16.0` and the sysroot `ld.lld` pinned in `cli-elf/inputs.lock`).

```bash
lake exe cache get
lake build
python3 scripts/bug_injection.py verify-patches     # check stored diffs against upstream / v0.105.4
python3 scripts/bug_injection.py run                # replay witnesses on mutant and unpatched host builds
python3 scripts/bug_injection.py gen-ckpt <bug>     # materialize per-call execution checkpoints
python3 scripts/bug_injection.py disproof           # build mutant ELFs and kernel-check disproofs
```

`run` builds the host replayer (`third_party/libsignal/bug-injection/harness/`) against both the patched and unpatched Rust sources, executes each witness (`RunEvent` records `party`, `cmd`, `input`, `coins`, and `exit`; `clear` emits no event), verifies byte-for-byte agreement with `Witnesses/<Witness>.lean`, and classifies each witness as `live` (mutant produces `evs`, unpatched control does not), `refuted-by-control`, or `not-expressible`.

`disproof` re-extracts the patched AArch64 Lean model with `rust-obj2lean`, links the mutant's `libsignal-cli` ELF with the legacy snapshot recipe (D6) until M5 (`scripts/cli-elf --build`, every `cli-elf/inputs.lock` pin except the image's), pins its SHA-256 in `GeneratedLean.BugInjectionMutant` (`mutantCliElfBytes`), and elaborates `Disproofs/<Witness>.lean` under `CV_BUG_INJECTION=<bug>`. All build artifacts live under `.lake/bug-injection/`, and `#guard` checks reject unpatched or mismatched ELF images; nothing in the default `lake build` imports mutant overlays.

## Adding a Bug

1. **Save the Rust patch** and register a `[[bug]]` entry in `third_party/libsignal/bug-injection/bugs.toml` (or `synthetic/bugs.toml`):
   - **Upstream bug (`kind = "upstream"`, default)**: save `https://github.com/signalapp/libsignal/commit/<sha>.diff` to `third_party/libsignal/bug-injection/patches/<bug>/upstream-<sha>.diff` (applied reversed), plus `v0.105.4.diff` if backporting to `v0.105.4` is needed.
   - **Synthetic mutant (`kind = "synthetic"`)**: save a forward diff against `v0.105.4` to `third_party/libsignal/bug-injection/synthetic/patches/<slug>/v0.105.4.diff` with `patch` and `patch_sha256` in `synthetic/bugs.toml`.
2. **Select the target statement**: set `statement = "DY.Libsignal.Composed.Security.SignalSessionSecurePlaced"` on upstream `[[witness]]` entries (or `"DY.Libsignal.Composed.Security.SignalSessionSecure"` for synthetic mutants; keyed in `STATEMENTS` in `scripts/bug_injection.py`).
3. **Write the witness inputs** in `third_party/libsignal/bug-injection/witnesses/<witness>.json` (or `synthetic/witnesses/<slug>.json`), listing `init`, `send`, `recv`, `clear`, and disk-compromise `leak` steps (`KeyInDir`, optional `"with_opk": true`) with literal or derived byte arguments (`slice`, `replace`, `or_at`; see `harness/src/main.rs`).
4. **Record and generate Lean modules**: run `python3 scripts/bug_injection.py run <witness> --record` to write `Witnesses/<Witness>.lean`, `NonVacuity/<Witness>.lean`, and `Disproofs/<Witness>.lean` (under `Synthetic/` for synthetic mutants; add new disproof modules to `EXCLUDED` in `scripts/check_lib_roots.py`).

## Disproofs

Both historical bugs are kernel-refuted in their `CV_BUG_INJECTION=<bug>` builds, with `#print axioms disproof` depending only on `[propext, Classical.choice, Quot.sound]`.

Because `mutantCliElfBytes` depends only on the bug patch, every witness for a given bug shares the same obligation `¬ SignalSessionSecurePlaced mutantCliElfBytes`. `CARRIERS` in `scripts/bug_injection.py` discharges each bug's generated `Disproofs/<Witness>.lean` obligations from a single carrier theorem in `Disproofs/Impl/<CarrierWitness>.lean`:

- `cheval26-small-subgroup`: carrier `cheval26-small-subgroup-high-bit-cli`
- `cheval26-weak-state`: carrier `cheval26-weak-state-idx1-cli`

The alternate traces `cheval26-small-subgroup-torsion-cli` and `cheval26-weak-state-cli` are not separately kernel-stepped. In `cheval26-weak-state-cli`, call 6 reads an SPQR chain key at step index 2 that no prior wire message commits to, allowing an unconstrained `OpaqueSymbolSemantics` to satisfy a collision excuse; `cheval26-weak-state-idx1-cli` refutes the same mutant ELF at step index 1, which call 5 pins on the wire.

Each carrier applies `not_signalSessionSecurePlaced_of_witness` (`Witnesses/CliShapePlaced.lean`) at linked placements `(mpl, mmpl)` and the proof-layer predicate `cliCompFitsPinned setup` (`Proofs/Common/CompFitsPin.lean`), which extends `cliCompFits` with the table-driven interpretation `compI0`, unrecorded setup randomness, party identifiers, and torsion-shift facts:

- **Spec proofs `(S)`** build in the default `BugInjection` library (`Proofs/Cheval26SmallSubgroupHighBitComp443/`, `Proofs/Cheval26WeakStateIdx1/`, `Proofs/Common443/`, and `Proofs/Common/`).
- **Binary execution proofs `(I)`** evaluate `ElfImage.parse mutantCliElfBytes` in the kernel (`Disproofs/Impl/MutantParse.lean`), prove `ElfFullValid` (`Disproofs/Impl/<Bug>/Base*.lean`), step the CLI runs (3 for small subgroup, 7 for weak state) via `Proofs/CliExec/` across `2^0`- to `2^12`-step chunks defined in `Disproofs/Impl/ckpt_chunk_plan.json`, and combine `(S)` and `(I)` in `Disproofs/Impl/<Bug>/Nodes.lean`.
- **Checkpoints**: `Base*` and `Call<k>.lean` aggregators are tracked in git, while `Call<k>/{C*,Ckpt*}.lean` chunk files are gitignored and materialized by `scripts/bug_injection.py gen-ckpt` (using `Disproofs/Impl/CkptDump/{BasePlaced,RunPlaced}.lean` and `scripts/bug_injection_ckpt.py`, which enforces a pure-expression token allowlist and runs `check_axiom_tactics` and `sorry`/template checks before `rfl_kernel` verification).

### Limitations

- **Token-cell offsets**: `cliTokenPatch` zeroes `tokenStorageOff` and `tokenOnceOff` at offsets measured on the unpatched binary. On the weak-state mutant (`.text` is one page shorter), those writes land in an already-zero read-only page; misplacing the zeroing patch only restricts possible traces, and the Idx1 witness never reads those cells.
- **No `comparator` replay**: mutant disproofs are checked by Lean and `#print axioms` inside their `CV_BUG_INJECTION=<bug>` builds rather than replayed against a separate held-out challenge package.

## Status

| Witness | Bug (upstream fix commit) | Host replay | Obligation (`¬ SignalSessionSecurePlaced mutantCliElfBytes`) | `(S)` status |
|---|---|---|---|---|
| `cheval26-weak-state-cli` | weak state (`cd361186fba60c83186262d91b03af608fb8c7c3`) | `live` | proved via carrier `cheval26-weak-state-idx1-cli` | false under unconstrained SPQR `OpaqueSymbolSemantics` (step index 2 unpinned on wire); unused |
| `cheval26-weak-state-idx1-cli` | weak state (`cd361186fba60c83186262d91b03af608fb8c7c3`) | `live` | proved (carrier) | proved at `cliCompFitsPinned` (open at unpinned `cliCompFits` without SPQR pins) |
| `cheval26-small-subgroup-high-bit-cli` | small subgroup (`5293caa6cad81566b80f3c3731857bedaa78737b`) | `live` | proved (carrier) | proved at `cliCompFitsPinned` (open at unpinned `cliCompFits` on `BobSessionStartCollidesOrImplicitRejects` / `KyberCollisionAt`) |
| `cheval26-small-subgroup-torsion-cli` | small subgroup (`5293caa6cad81566b80f3c3731857bedaa78737b`) | `live` | proved via carrier `cheval26-small-subgroup-high-bit-cli` | open (`cliCompFits` does not pin the torsion shift) |

Synthetic specification-audit mutants (`synthetic-*`, all `live`) live under [`Synthetic/`](Synthetic/README.md), with patches and JSON witnesses in `third_party/libsignal/bug-injection/synthetic/`.
