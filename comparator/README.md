# Comparator check of the headline theorems

CI checks every headline theorem of `Computational/Theorems/` and `Symbolic/Theorems/` with
[`leanprover/comparator`](https://github.com/leanprover/comparator), the Lean FRO's judge for Lean
proofs. For each theorem it checks that:

1. the theorem in the solution has exactly the statement of the challenge, and every constant the
   statement uses (all the way down) is the same in both;
2. its proof uses only the axioms `propext`, `Quot.sound` and `Classical.choice`;
3. the whole solution environment, exported by `lean4export` (not loaded from `.olean` files),
   replays in a fresh Lean kernel.

## Files

| File | Role |
| --- | --- |
| `ComparatorChallenge/Computational/{Lemmas,Main}.lean`, `ComparatorChallenge/Symbolic/{ModelSecurity,RefinementPreservation,Refinement,Security}.lean` | **Trusted.** One file per theorem file. Each theorem has the same name and the same statement, byte for byte, as in `Computational/Theorems/` or `Symbolic/Theorems/`, and the proof `sorry`. They import only specification modules. |
| `ComparatorChallenge/{Computational,Symbolic}.lean` | `challenge_module`s: import the challenge files above. |
| `ComparatorSolution/{Computational,Symbolic}.lean` | `solution_module`s: import the theorem files and declare nothing. |
| `computational.json`, `symbolic.json` | The comparator configs: modules, the fully qualified `theorem_names`, `permitted_axioms`. |
| `install-tools.sh` | Builds comparator, lean4export (both at their `v4.34.0` tags) and landrun (pinned `main` commit). |
| `run.sh` | Runs comparator on both configs concurrently and fails unless both print `Your solution is okay!`. |

The two lake libraries `ComparatorChallenge` and `ComparatorSolution` (`lakefile.lean`) are not
default targets.

## Theorems checked

Computational (`computational.json`), every theorem of `Computational/Theorems/`:

| Paper | Theorem |
| --- | --- |
| Lemma 1 | `SignalPqxdh.Security.headlineδ` |
| Lemma 2 | `CryptoVerification.E2E.session_secure` |
| Lemma 3 | `CryptoVerification.E2E.model_secure_costed` |
| Lemma 4 (relocatable) | `CryptoVerification.SignalSession.libsignal_cli_pq_binary_correct_placed` |
| Main Theorem (relocatable) | `CryptoVerification.LibsignalCli.libsignal_cli_pq_secure_elf_binary_placed` |
| placement witness (`libsignalSessionLib`) | `CryptoVerification.SignalSession.libsignal_cli_elf_linked_in` |
| allocator placement witness (`mallocngLib`) | `CryptoVerification.SignalSession.libsignal_cli_elf_mallocng_linked_in` |
| label gate A | `CryptoVerification.SignalSession.libsignal_cli_labels_from_objects` |

Symbolic (`symbolic.json`), every theorem of `Symbolic/Theorems/`:

| File | Theorems |
| --- | --- |
| `Security.lean` (headline) | `Proven.Security.signal_session_secure_placed`, `Proven.Security.libsignal_cli_elf_linked_in`, `Proven.Security.libsignal_cli_elf_mallocng_linked_in`, `Proven.Security.libsignal_cli_labels_from_objects` |
| `Refinement.lean` | `Proven.Refinement.comp_refines_cli_placed` |
| `RefinementPreservation.lean` | `Proven.RefinementPreservation.comp_refinement_preservation_cli` |
| `ModelSecurity.lean` | `Proven.ForwardSecrecy.forward_secrecy`, `Proven.PostCompromiseSecurity.post_compromise_security`, and in `Proven.Handshake`: `alice_initiator_secrecy`, `bob_responder_secrecy`, `authentication`, `peer_authentication`, `handshake_forward_secrecy`, `kci_resistance`, `session_independence`, `hndl_resistance` |

## Running it

A run takes hours (the kernel replays each headline theorem's whole closure), so it is not part of
the per-PR `CI` workflow (`.github/workflows/ci.yml`). The workflow `Comparator (release)`
(`.github/workflows/comparator-release.yml`) runs it on every release tag (see
[Releases](#releases)), on `workflow_dispatch`, and on PRs that touch `comparator/` or the
comparator workflows. Its job (`.github/workflows/comparator-reusable.yml`) restores the Lean caches
that `ci.yml` saved for the same commit, builds the CLI ELF, `CliElfLib`, `ComparatorChallenge` and
`ComparatorSolution`, runs `run.sh`, and uploads the logs (with `/usr/bin/time -v` wall time and max
RSS) and `pin.txt` (commit, ref, `lean-toolchain`, tool pins, SHA-256 of every file here) as a
workflow artifact. Locally, on a tree where `lake build` and `lake build CliElfLib` have succeeded:

```bash
comparator/install-tools.sh /tmp/comparator-tools
set -a; source /tmp/comparator-tools/env; set +a
lake build ComparatorChallenge ComparatorSolution
comparator/run.sh            # or: comparator/run.sh comparator/symbolic.json
```

## Releases

A release marks the code shipped to the public: a tag `v<YYYY>.<MM>.<DD>` (e.g. `v2026.11.06`;
add `.1`, `.2`, ... for a second release on the same day) on a commit of `main` whose `CI` run
passed. Pushing any tag that matches `v*` starts `Comparator (release)` on the tagged commit, so
only push such tags for releases. To cut one:

```bash
git fetch origin && git checkout origin/main   # or the main commit to release
git tag -s v2026.11.06 -m 'Release v2026.11.06'
git push origin v2026.11.06
ggh release create v2026.11.06 --verify-tag --title v2026.11.06 --notes '...'
```

(`ggh release create v2026.11.06 --target main` alone also works: it creates the tag, which
starts the workflow.) The run takes several hours. When it ends, the logs and `pin.txt` are
attached to the release as `comparator-<tag>-<success|failure>.tar.gz` (if the release exists by
then) and are always kept as the run's artifact `comparator-<tag>` (90 days). Check the run's
summary for the verdict of each config before announcing the release. To re-run the check on an
existing tag, re-run the workflow run, or start `Comparator (release)` by hand
(`workflow_dispatch`) on the tag.

## Weekly run on main

The workflow `Comparator (weekly)` (`.github/workflows/comparator-weekly.yml`) runs the same job
(`comparator-reusable.yml`) on the head of `main` every Sunday at 03:17 UTC (03:17 London in winter,
04:17 London in summer), and on `workflow_dispatch`
(`ggh workflow run comparator-weekly.yml --ref <branch>`). So a PR that changes a headline statement
without its challenge file, or gives a proof another axiom, passes `CI` but is reported within a
week, not only at the next release. The logs are the run's artifact `comparator-weekly-<sha>`.

A scheduled run that fails (or times out) opens an issue titled *Weekly comparator check failed*,
or comments on it if it is already open; the next scheduled run that passes closes it. Its
`pull_request` trigger covers only the workflow file itself: PRs that touch `comparator/` are
already checked by `Comparator (release)`.

## Changing a headline theorem

Change the statement in the theorem file and in its challenge file in the same PR. A reviewer then
reads the challenge diff: the challenge files and the specification modules they import are what
the check trusts.

## What this check does not cover

- **The specifications.** The challenge imports the specification modules from the same commit as
  the solution, so the definitions the statements use are trusted as they are in that commit (as in
  every comparator setup, the challenge's import closure is trusted). Comparator does catch a
  theorem file whose statement differs from the challenge, a proof with any other axiom (`sorryAx`,
  `Lean.ofReduceBool`, `Lean.trustCompiler`, a custom `axiom`), and a proof the kernel rejects when
  replayed from the export.
- **A malicious PR.** The workflow builds the solution (`lake build CliElfLib`) before comparator
  builds the challenge, and comparator's `landrun` sandbox only confines comparator's own builds and
  exports. Code that runs while the solution is elaborated could change the challenge before it is
  built. Comparator's threat model (its README) assumes the solution has not been built before.
- **No sandbox on the CI runners.** Landlock needs Linux ≥ 5.13; the GitHub On-Prem runners run
  5.10 (`run.sh` prints the kernel), so `landrun --best-effort` confines nothing there and
  comparator's builds and exports run unsandboxed.
- **`bv_decide`.** No headline theorem depends on a `bv_decide` certificate axiom, so those axioms
  are not permitted, and comparator rejects any headline whose axioms include one. Outside
  `arm64-semantics/` no `.lean` file uses `bv_decide`; some engine lemmas in
  `arm64-semantics/ProofLib/` do, but no headline depends on them. Comparator `v4.34.0` matches
  `permitted_axioms` by exact name and cannot accept `bv_decide`'s per-proof certificate axioms.

## Lean versions

Comparator and lean4export are tagged per Lean release and must match `lean-toolchain`;
`install-tools.sh` fails if they do not. From Lean v4.35.0 on, comparator is part of core
(`lake comparator`, with `lake check`) and the standalone repository is deprecated; when the
repository moves to v4.35.0, switch to `lake comparator` instead of bumping the pins.
