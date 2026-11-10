# `ProofLib/Disproof/` — Machine-Code Memory Safety Disproof Infrastructure

Reusable untrusted verification infrastructure (`Role::Proof`) for refuting naive or buggy
subroutine specifications (`¬ subroutine_ok prog entry_pc spec`, `¬ safe_subroutine_ok prog entry_pc spec`)
and proving concrete fault traces (`ReachesException prog s0`).

## Which File to Import / Read

| Goal | Module | Key Declarations |
| :--- | :--- | :--- |
| Import the full disproof kit | [`ProofLib/Disproof.lean`](../Disproof.lean) | Re-exports `Basic`, `StrictHook`, `FaultWP`, `ModelBuilder` |
| Determinism of `Step` / terminal `Steps` | [`Basic.lean`](Basic.lean) | `Step.deterministic` (in `ProofLib/CoreLemmas.lean`), `Steps.eq_of_isTerminal`, `Steps.compare` (in `ProofLib/Hoare/Safety.lean`) |
| Refute `safe_subroutine_ok` via `.Exception` | [`Basic.lean`](Basic.lean) | `not_safe_subroutine_ok_of_exception`, `not_safe_subroutine_ok_of_stepsUntil_exception` |
| Refute `safe_subroutine_ok` / `subroutine_ok` via violated postcondition | [`Basic.lean`](Basic.lean) | `not_safe_subroutine_ok_of_post_false`, `not_subroutine_ok_of_panic_post_false` |
| Refute `subroutine_ok` via out-of-bounds write into adjacent canary | [`Basic.lean`](Basic.lean) | `not_subroutine_ok_of_frame_canary`, `not_safe_subroutine_ok_of_frame_canary` |
| Trap extern callee precondition violations (`NULL` / OOB / bad free) | [`StrictHook.lean`](StrictHook.lean) | `ValidHookCall`, `strictHook`, `strictHook_ok`, `strictMemcpyRegionHook` |
| Model deterministic OOM (`NULL` return) from `malloc` hooks | [`StrictHook.lean`](StrictHook.lean) | `oomAllocator`, `oomMallocRegionSpec`, `hookAllocNull_oomMallocRegion_ok` |
| Step into an unmapped / non-writable store or hook fault | [`FaultWP.lean`](FaultWP.lean) | `ReachesException`, `ReachesException.of_exec_step`, `ReachesException.of_store_unmapped`, `ReachesException.of_store_unmapped_at`, `ReachesException.of_strict_hook_call` |
| Extract a `reaches_pc` execution witness from `SepWP` | [`ProofLib/SepLogic/WP/StepsCore.lean`](../SepLogic/WP/StepsCore.lean) | `SepWP.reaches_of_sepWP` (`reaches_of_sepWP`) |
| Build a concrete initial `State` (`CodeLoaded`, `s0.mem ⊨ ...`, unmapped OOB) | [`ModelBuilder.lean`](ModelBuilder.lean) | `DisproofRegion`, `buildDisproofMem`, `mkDisproofState`, `mkDisproofState_satisfies`, `mkDisproofState_perm_none` |
| End-to-end reference counterexamples | [`Arm64/Testing/Regression/DisproofTests.lean`](../../Arm64/Testing/Regression/DisproofTests.lean) | Unmapped OOB store fault, unchecked OOM `NULL` into `strictHook`, adjacent canary corruption |
