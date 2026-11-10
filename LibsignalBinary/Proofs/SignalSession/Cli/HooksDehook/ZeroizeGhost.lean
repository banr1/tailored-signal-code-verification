/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.MemsetGhostK -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.WithAlloc -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.ZeroizeCode -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfSlicesPqOomH2FirstStopGeneric -- proof-setup: allow-public-import

/-!
# Ghost `zeroize` Drop Hooks, `HookOk` Suite & Stock-Safe `StepsVisitedIn` Replays (`HooksDehook.ZeroizeGhost`)

Stage `b` (`Card D23-b`) per-row ghost hooks for `<StaticSecret as Drop>::drop` (63-word
`MontgomeryPoint::zeroize`) and `<SharedSecret as Drop>::drop` (64-word contiguous hull
`sharedSecretDropHullWords`, entered at `m + sharedSecretDropEntryOff`), parallel to
`HooksDehook.MemsetGhost` and `HooksDehook.MemsetGhostK`:

1. **Ghost `zeroize` hooks (`zeroizeGhostHook{,K}`, `f3EmptyZeroizeGhostHook{,K}`)**:
   - `zeroizeGhostHook keep P_real P_sub entryTarget`: wraps `masterZeroizeSpec` via
     `linkedCallHook` with `W`-independent fallback `zeroizeSecretHook`.
   - `zeroizeGhostHookK keep P_real P_sub entryTarget`: wraps `zeroizeSpecK keep masterZeroizeSpec`.
   - `f3EmptyZeroizeGhostHook{,K} keep P_sub entryTarget`: `W`-independent `f3LinkedCallHook` forms
     at `P_real := emptyStdProg`, bridged to `zeroizeGhostHook{,K}` via
     `f3LinkedCallHook_const_eq_linkedCallHook`.
   - `sharedSecretDropGhostHook{,K}` and `f3EmptySharedSecretDropGhostHook{,K}`: hull-base
     abbreviations at `m + sharedSecretDropEntryOff` (`252#64`).
2. **Pointwise C11 §8.1 bundle properties**:
   Proves `.fs = s.fs`, `HookFsTraced IsFsC`, `.trace = s.trace`, `VmPreserved` (via Stage `a1`
   `processZeroizeSpec` + `ExecFrozen` + `KeepsFrozen`), `OomPreserved ∧ PoolPreserved`,
   `ExecFrozen`-preservation, `keep lr = false` extraction on `K`, and `keep lr = true` branch
   equations once under generic `hsub_proc : subroutine_ok P_sub entryTarget processZeroizeSpec`,
   then specializes to both `StaticSecret::drop` (`zeroize32Words`) and `SharedSecret::drop`
   (`sharedSecretDropHullWords` and 2-block `hasInstrs` + `hasWords`).
3. **Complete consumer `HookOk` suite**:
   Lifts `masterZeroizeSpec` + `VmPreserved` + `.fs` across every consumer contract in
   `HooksDehook.ZeroizeCode` (plain, `.keepsFs`, `withFsPred`, `withStack`, `CliExt.zeroizeSpec`,
   `withVmPreserved` / `zeroizeSecretBudgetSpec`, `withExecFrozen`, and `zeroizeSpecK`).
4. **Stock-safe `StepsVisitedIn` execution & replay bridges**:
   Uses `h2fsgen_StepsVisitedIn` pinned via `h2fsgen_stepsUntil_det` and `hLiftVis` premises ONLY
   (never legacy `StepsUntil` lifts or `h2fsgen_HooksUnfetched`).
-/

set_option autoImplicit false

public section

namespace LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.ZeroizeGhost

open Arm64 ProofLib SepProp
open Arm64.Process (pureWordsProg)
open CryptoVerification.LibsignalTripleRatchet (zeroizeSecretHook zeroizeSecretSpec withStack extHookStack)
open CryptoVerification.SignalSession.Cli.RunGlue (IsFsC)
open CryptoVerification.SignalSession.CliExt (zeroizeSpec)
open CryptoVerification.SignalSession.Cli.MainHops (hookOk_withStack)
open LibsignalBinary.Heap (AllocCostModel BudgetLimits RustCliAllocBudget FdsHiFrame VmPreserved OomPreserved PoolPreserved)
open LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.WithAlloc (withAlloc hookOk_withAlloc_of_withVmPreserved hookOk_withAlloc_withVmPreserved)
open LibsignalBinary.Heap.SpecBudget (withVmPreserved)
open LibsignalBinary.Heap.Fine (zeroizeSecretHook_vmPreserved)
open LibsignalBinary.Proofs.HookDischarge.Generics.ZeroizeDrop (zeroize32Words sharedSecretDropInstrs withFsPred)
open LibsignalBinary.Proofs.SignalSession.Cli.Main.Proofs.KeepsFsBudget (hookOk_withVmPreserved)
open LibsignalBinary.Proofs.SignalSession.Cli.AllocGhostLinkTransfer (
  ExecFrozen satisfies_stripExecOutside stepsUntil_of_stripS_standard
  SpecStripSInvariant SpecPreservesFsTrace keepFsTrace keepFsTrace_fs ActiveRealPre ActiveRealRun
  linkedCallHook linkedCallHook_fs linkedCallHook_fsT linkedCallHook_ok
)
open LibsignalBinary.Proofs.SignalSession.Cli.F3.L4B.F3AllocStdinGhostHooks (
  ActiveF3CallPre f3LinkedCallHook f3LinkedCallHook_fs f3LinkedCallHook_fsT
)
open LibsignalBinary.Proofs.SignalSession.Cli.F3.L4B.Ghost617Transfer (
  GhostExternReplaysOn GhostExternReplaysS StubReachesTargetOn
)
open LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.LinkedCallHookOn (
  ghostExternReplaysOn_of_single_stub ghostExternReplaysS_of_single_stub
  linkedCallHook_activeRealPre_of_noException
)
open LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.MemsetCode (
  memsetSpecK pureWordsProg_externAt_none hookOk_memsetSpecK_of_plain
)
open LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.MemsetGhost (withExecFrozen hookOk_withExecFrozen_of_plain)
open LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.MemsetGhostK (
  emptyStdProg emptyStdProg_svc emptyStdProg_externAt_none
  activeF3CallPre_const_iff f3LinkedCallHook_const_eq_linkedCallHook
)
open LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.ZeroizeCode (
  ZeroizeStatePreserved masterZeroizeSpec processZeroizeSpec masterZeroizeBudgetSpec zeroizeSpecK
  sharedSecretDropBackWord sharedSecretDropHullWords decode_sharedSecretDropBackWord
  pureWordsProg_zeroize32_hasWords
  pureWordsProg_sharedSecretDropHull_zeroize_hasWords pureWordsProg_sharedSecretDropHull_drop_hasWords
  processZeroize_pre_of_masterZeroize_pre subroutine_ok_processZeroize_of_hasWords
  subroutine_ok_sharedSecret_processZeroize_of_hasInstrs_hasWords subroutine_ok_sharedSecret_processZeroize_of_hasWords
  zeroizeSecretHook_masterZeroize_ok zeroizeSecretHook_masterZeroizeK_ok
  hookOk_withStack_pureAbort hookOk_zeroizeSpecK_withStack_pureAbort
  hookOk_withFsPred_of_keepsFs hookOk_zeroizeSpecK_withFsPred_of_keepsFs
  hookOk_zeroizeSecret_of_master hookOk_zeroizeSecretK_of_master
  hookOk_zeroizeSecret_keepsFs_of_master hookOk_zeroizeSecretK_keepsFs_of_master
  hookOk_zeroizeSecret_withFsPred_of_master hookOk_zeroizeSecretK_withFsPred_of_master
  hookOk_withStack_zeroizeSecret_of_master hookOk_withStack_zeroizeSecretK_of_master
  hookOk_cliZeroize_of_master hookOk_cliZeroizeK_of_master hookOk_cliZeroize_keepsFs_of_master
  hookOk_zeroizeSecretBudget_of_masterBudget hookOk_zeroizeSecretBudget_keepsFs_of_masterBudget
  hookOk_zeroizeSecretBudget_withFsPred_of_masterBudget zeroizeSpecK_keepsFs zeroizeSpecK_withVmPreserved
)
open LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfSlicesPqOomH2FirstStopGeneric (
  h2fsgen_StepsVisitedIn h2fsgen_stepsUntil_det h2fsgen_real_subroutine_run_visitedIn_of_stripS
)

/-! ## 1. Ghost `zeroize` Hook Definitions & `f3Empty` Bridges -/

/-- Byte offset (`252 = 63 * 4`) from `sharedSecretDropHullWords` base to `<SharedSecret as Drop>::drop`. -/
@[expose] def sharedSecretDropEntryOff : BitVec 64 := 252#64

/-- Plain ghost `zeroize` hook wrapping `masterZeroizeSpec` with fallback `zeroizeSecretHook`. -/
@[expose] noncomputable def zeroizeGhostHook (keep : BitVec 64 → Bool) (P_real P_sub : Program)
    (entryTarget : BitVec 64) : State → State :=
  linkedCallHook keep P_real P_sub entryTarget masterZeroizeSpec zeroizeSecretHook

/-- `K`-narrowed ghost `zeroize` hook wrapping `zeroizeSpecK keep masterZeroizeSpec`. -/
@[expose] noncomputable def zeroizeGhostHookK (keep : BitVec 64 → Bool) (P_real P_sub : Program)
    (entryTarget : BitVec 64) : State → State :=
  linkedCallHook keep P_real P_sub entryTarget (zeroizeSpecK keep masterZeroizeSpec) zeroizeSecretHook

/-- Plain `W`-independent K-convention `zeroize` ghost hook (`P_real := emptyStdProg`). -/
@[expose] noncomputable def f3EmptyZeroizeGhostHook (keep : BitVec 64 → Bool) (P_sub : Program)
    (entryTarget : BitVec 64) : State → State :=
  f3LinkedCallHook keep emptyStdProg P_sub entryTarget (fun _ _ => masterZeroizeSpec) zeroizeSecretHook

/-- `K`-narrowed `W`-independent K-convention `zeroize` ghost hook (`P_real := emptyStdProg`). -/
@[expose] noncomputable def f3EmptyZeroizeGhostHookK (keep : BitVec 64 → Bool) (P_sub : Program)
    (entryTarget : BitVec 64) : State → State :=
  f3LinkedCallHook keep emptyStdProg P_sub entryTarget (fun _ _ => zeroizeSpecK keep masterZeroizeSpec) zeroizeSecretHook

theorem f3EmptyZeroizeGhostHook_eq (keep : BitVec 64 → Bool) (P_sub : Program) (entryTarget : BitVec 64) :
    f3EmptyZeroizeGhostHook keep P_sub entryTarget = zeroizeGhostHook keep emptyStdProg P_sub entryTarget :=
  f3LinkedCallHook_const_eq_linkedCallHook keep emptyStdProg P_sub entryTarget masterZeroizeSpec zeroizeSecretHook

theorem f3EmptyZeroizeGhostHookK_eq (keep : BitVec 64 → Bool) (P_sub : Program) (entryTarget : BitVec 64) :
    f3EmptyZeroizeGhostHookK keep P_sub entryTarget = zeroizeGhostHookK keep emptyStdProg P_sub entryTarget :=
  f3LinkedCallHook_const_eq_linkedCallHook keep emptyStdProg P_sub entryTarget (zeroizeSpecK keep masterZeroizeSpec) zeroizeSecretHook

noncomputable abbrev sharedSecretDropGhostHook (keep : BitVec 64 → Bool) (P_real P_sub : Program) (m : BitVec 64) : State → State :=
  zeroizeGhostHook keep P_real P_sub (m + sharedSecretDropEntryOff)

noncomputable abbrev sharedSecretDropGhostHookK (keep : BitVec 64 → Bool) (P_real P_sub : Program) (m : BitVec 64) : State → State :=
  zeroizeGhostHookK keep P_real P_sub (m + sharedSecretDropEntryOff)

noncomputable abbrev f3EmptySharedSecretDropGhostHook (keep : BitVec 64 → Bool) (P_sub : Program) (m : BitVec 64) : State → State :=
  f3EmptyZeroizeGhostHook keep P_sub (m + sharedSecretDropEntryOff)

noncomputable abbrev f3EmptySharedSecretDropGhostHookK (keep : BitVec 64 → Bool) (P_sub : Program) (m : BitVec 64) : State → State :=
  f3EmptyZeroizeGhostHookK keep P_sub (m + sharedSecretDropEntryOff)

noncomputable abbrev zeroizeGhostHookPure63 (keep : BitVec 64 → Bool) (P_real : Program) (entry : BitVec 64) : State → State :=
  zeroizeGhostHook keep P_real (pureWordsProg entry zeroize32Words) entry

noncomputable abbrev zeroizeGhostHookPure63K (keep : BitVec 64 → Bool) (P_real : Program) (entry : BitVec 64) : State → State :=
  zeroizeGhostHookK keep P_real (pureWordsProg entry zeroize32Words) entry

noncomputable abbrev sharedSecretDropGhostHookPure64 (keep : BitVec 64 → Bool) (P_real : Program) (m : BitVec 64) : State → State :=
  sharedSecretDropGhostHook keep P_real (pureWordsProg m sharedSecretDropHullWords) m

noncomputable abbrev sharedSecretDropGhostHookPure64K (keep : BitVec 64 → Bool) (P_real : Program) (m : BitVec 64) : State → State :=
  sharedSecretDropGhostHookK keep P_real (pureWordsProg m sharedSecretDropHullWords) m

/-! ## 2. `SpecStripSInvariant`, `SpecPreservesFsTrace`, PC Invariance & `processZeroizeSpec` Lifts -/

theorem specStripSInvariant_masterZeroize (keep : BitVec 64 → Bool) :
    SpecStripSInvariant keep masterZeroizeSpec where
  pre_eq := fun _ s => by cases s; rfl
  post_eq := fun _ s0 sf => by cases s0; cases sf; rfl
  onPanic_eq := fun _ _ _ => rfl
  onExit_eq := fun _ _ _ _ => rfl
  onOom_eq := fun _ _ _ => rfl

theorem specStripSInvariant_masterZeroizeK (keep : BitVec 64 → Bool) :
    SpecStripSInvariant keep (zeroizeSpecK keep masterZeroizeSpec) where
  pre_eq := fun _ s => by cases s; rfl
  post_eq := fun _ s0 sf => by cases s0; cases sf; rfl
  onPanic_eq := fun _ _ _ => rfl
  onExit_eq := fun _ _ _ _ => rfl
  onOom_eq := fun _ _ _ => rfl

theorem specPreservesFsTrace_masterZeroize : SpecPreservesFsTrace masterZeroizeSpec := by
  intro a R s0 sf hout
  rcases hout with ⟨_, _, hpost⟩ | ⟨_, hpan⟩ | ⟨_, _, hex⟩ | ⟨_, hoom⟩
  · dsimp only [masterZeroizeSpec] at hpost; rw [sepConj_assoc, satisfies_pure_sepConj] at hpost
    exact ⟨hpost.1.1, FsTraced.of_eq hpost.1.2.1 (congrArg FsState.files hpost.1.1)⟩
  · dsimp only [masterZeroizeSpec] at hpan; rw [satisfies_pure_sepConj] at hpan; exact False.elim hpan.1
  · dsimp only [masterZeroizeSpec] at hex; rw [satisfies_pure_sepConj] at hex; exact False.elim hex.1
  · dsimp only [masterZeroizeSpec] at hoom; rw [satisfies_pure_sepConj] at hoom; exact False.elim hoom.1

theorem specPreservesFsTrace_masterZeroizeK (keep : BitVec 64 → Bool) :
    SpecPreservesFsTrace (zeroizeSpecK keep masterZeroizeSpec) := specPreservesFsTrace_masterZeroize

theorem masterZeroize_pre_setPC (a : BitVec 64) (s : State) (pc : BitVec 64) :
    masterZeroizeSpec.pre a (s.setPC pc) = masterZeroizeSpec.pre a s := by cases s; rfl

theorem masterZeroizeK_pre_setPC (keep : BitVec 64 → Bool) (a : BitVec 64) (s : State) (pc : BitVec 64) :
    (zeroizeSpecK keep masterZeroizeSpec).pre a (s.setPC pc) =
      (zeroizeSpecK keep masterZeroizeSpec).pre a s := by cases s; rfl

theorem masterZeroize_outcome_setPC (a : BitVec 64) (R : SepProp) (s0 sf : State) (pc : BitVec 64)
    (h : SubroutineOutcome masterZeroizeSpec a R (s0.setPC pc) sf) :
    SubroutineOutcome masterZeroizeSpec a R s0 sf := by cases s0; cases sf; exact h

theorem masterZeroizeK_outcome_setPC (keep : BitVec 64 → Bool) (a : BitVec 64) (R : SepProp)
    (s0 sf : State) (pc : BitVec 64)
    (h : SubroutineOutcome (zeroizeSpecK keep masterZeroizeSpec) a R (s0.setPC pc) sf) :
    SubroutineOutcome (zeroizeSpecK keep masterZeroizeSpec) a R s0 sf := by cases s0; cases sf; exact h

theorem keepFsTrace_zeroizeSecretHook_eq (s0 : State) :
    keepFsTrace zeroizeSecretHook s0 = zeroizeSecretHook s0 := by cases s0; rfl

theorem keepFsTrace_zeroizeSecretHook_master_ok : HookOk (keepFsTrace zeroizeSecretHook) masterZeroizeSpec := by
  rw [funext keepFsTrace_zeroizeSecretHook_eq]; exact zeroizeSecretHook_masterZeroize_ok

theorem keepFsTrace_zeroizeSecretHook_masterK_ok (keep : BitVec 64 → Bool) :
    HookOk (keepFsTrace zeroizeSecretHook) (zeroizeSpecK keep masterZeroizeSpec) := by
  rw [funext keepFsTrace_zeroizeSecretHook_eq]; exact zeroizeSecretHook_masterZeroizeK_ok keep

theorem zeroizeSecretHook_preserves_oom_pool (s0 : State) :
    OomPreserved s0 (zeroizeSecretHook s0) ∧ PoolPreserved s0 (zeroizeSecretHook s0) := by
  unfold zeroizeSecretHook; exact ⟨⟨rfl, rfl, rfl⟩, ⟨rfl, rfl, rfl⟩⟩

theorem zeroizeSecretHook_preserves_execFrozen {s0 : State} (hfr : ExecFrozen s0.mem) :
    ExecFrozen (zeroizeSecretHook s0).mem :=
  ExecFrozen.of_perm_eq hfr (zeroizeSecretHook_vmPreserved s0).2.2.1

private theorem hookFree_sub {prog : Program} {off len off' len' : Nat}
    (h : prog.hookFree off len) (h1 : off ≤ off') (h2 : off' + len' ≤ off + len) :
    prog.hookFree off' len' := by
  unfold Program.hookFree at h ⊢
  refine ⟨List.all_eq_true.mpr fun p hm => ?_, List.all_eq_true.mpr fun p hm => ?_⟩
  · have hso := List.all_eq_true.mp h.1 p hm; rcases p with ⟨n, o⟩; dsimp only at hso ⊢
    by_cases hlo : off' ≤ o
    · by_cases hhi : o < off' + len'
      · have hlo0 : off ≤ o := by omega
        have hhi0 : o < off + len := by omega
        simpa [hlo, hhi, hlo0, hhi0] using hso
      · simp [hhi]
    · simp [hlo]
  · have hoo := List.all_eq_true.mp h.2 p hm; rcases p with ⟨n, o⟩; dsimp only at hoo ⊢
    by_cases hlo : off' ≤ o
    · by_cases hhi : o < off' + len'
      · have hlo0 : off ≤ o := by omega
        have hhi0 : o < off + len := by omega
        simpa [hlo, hhi, hlo0, hhi0] using hoo
      · simp [hhi]
    · simp [hlo]

theorem hasWords_zeroize32_of_hull {P_sub : Program} {m : BitVec 64}
    (hwords : P_sub.hasWords m sharedSecretDropHullWords) :
    P_sub.hasWords m zeroize32Words := by
  unfold Program.hasWords Program.hasWordsOff at hwords ⊢
  have hlenH : sharedSecretDropHullWords.length = 64 := rfl
  have hlenZ : zeroize32Words.length = 63 := rfl
  refine ⟨by omega, fun i hi => ?_, hookFree_sub hwords.2.2 (Nat.le_refl _) (by omega)⟩
  have hiH : i < sharedSecretDropHullWords.length := by omega
  have hw := hwords.2.1 i hiH
  have heq : sharedSecretDropHullWords[i]'hiH = zeroize32Words[i]'hi := by
    dsimp only [sharedSecretDropHullWords]; exact List.getElem_append_left hi
  rwa [heq] at hw

theorem hasWords_dropBack_of_hull {P_sub : Program} {m : BitVec 64}
    (hwords : P_sub.hasWords m sharedSecretDropHullWords) :
    P_sub.hasWords (m + sharedSecretDropEntryOff) [sharedSecretDropBackWord] := by
  unfold Program.hasWords Program.hasWordsOff at hwords ⊢; unfold sharedSecretDropEntryOff
  have hlenH : sharedSecretDropHullWords.length = 64 := rfl
  have hbnd := hwords.1; rw [hlenH] at hbnd
  have hbv : m + 252#64 - P_sub.base = (m - P_sub.base) + 252#64 := by bv_omega
  have hoff : (m + 252#64 - P_sub.base).toNat = (m - P_sub.base).toNat + 252 := by
    rw [hbv, BitVec.toNat_add]; change ((m - P_sub.base).toNat + 252) % 2 ^ 64 = _; omega
  rw [hoff]
  refine ⟨by dsimp only [List.length_singleton]; omega, fun i hi => ?_,
    hookFree_sub hwords.2.2 (by omega) (by dsimp only [List.length_singleton]; omega)⟩
  have hi0 : i = 0 := by dsimp only [List.length_singleton] at hi; omega
  subst hi0
  have hw := hwords.2.1 63 (by rw [hlenH]; decide)
  have heq : sharedSecretDropHullWords[63]'(by rw [hlenH]; decide) = sharedSecretDropBackWord := rfl
  simpa [Nat.add_zero, heq] using hw

/-- Single-hull (`64`-word `sharedSecretDropHullWords`) region-local `subroutine_ok` for
    `processZeroizeSpec` at entry `m + sharedSecretDropEntryOff`. -/
theorem subroutine_ok_sharedSecretHull_processZeroize_of_hasWords
    {P_sub : Program} {m : BitVec 64}
    (hsub_no : ∀ pc, P_sub.externAt? pc = none)
    (hwords : P_sub.hasWords m sharedSecretDropHullWords) :
    subroutine_ok P_sub (m + sharedSecretDropEntryOff) processZeroizeSpec :=
  subroutine_ok_sharedSecret_processZeroize_of_hasWords hsub_no
    (hasWords_dropBack_of_hull hwords)
    (decode_sharedSecretDropBackWord m)
    (hasWords_zeroize32_of_hull hwords)

theorem subroutine_ok_masterZeroize_of_process {P_sub : Program} {entryTarget : BitVec 64}
    (hsub_proc : subroutine_ok P_sub entryTarget processZeroizeSpec) :
    subroutine_ok P_sub entryTarget masterZeroizeSpec := by
  refine subroutine_ok_mono hsub_proc (fun _ _ _ hp => hp) (fun _ _ _ _ hq => ?_)
  dsimp only [processZeroizeSpec, masterZeroizeSpec] at hq ⊢
  simp only [sepConj_assoc, satisfies_pure_sepConj] at hq ⊢
  exact ⟨ZeroizeStatePreserved.of_processFieldsPreserved hq.1, hq.2⟩

theorem subroutine_ok_masterZeroizeK_of_process (keep : BitVec 64 → Bool) {P_sub : Program} {entryTarget : BitVec 64}
    (hsub_proc : subroutine_ok P_sub entryTarget processZeroizeSpec) :
    subroutine_ok P_sub entryTarget (zeroizeSpecK keep masterZeroizeSpec) := by
  refine subroutine_ok_mono (subroutine_ok_masterZeroize_of_process hsub_proc) (fun _ _ _ hp => ?_) (fun _ _ _ _ hq => hq)
  dsimp only [zeroizeSpecK, memsetSpecK] at hp; rw [sepConj_assoc, satisfies_pure_sepConj] at hp; exact hp.2

/-! ## 3. Master `HookOk` & Pointwise State Preservation (`VmPreserved`, `OomPreserved`, `fs`, `ExecFrozen`) -/

/-- Recover exact `Memory.perm` equality across `stripExecOutside keep` from `ExecFrozen` +
    `KeepsFrozen` + stripped-permission equality. -/
private theorem perm_eq_of_stripExecOutside_keepsFrozen {keep : BitVec 64 → Bool} {m0 mf : Memory}
    (hfr0 : ExecFrozen m0) (hfrf : ExecFrozen mf) (hkf : m0.KeepsFrozen mf)
    (hstrip : ∀ a : BitVec 64, (stripExecOutside keep mf).perm a = (stripExecOutside keep m0).perm a) :
    ∀ a : BitVec 64, mf.perm a = m0.perm a := by
  intro a; have hst := hstrip a; rw [strip_perm, strip_perm] at hst
  have hfr0_a := hfr0 a; have hfrf_a := hfrf a
  by_cases hfrozen0 : m0.Frozen a
  · exact (hkf a hfrozen0).2.1
  · unfold Memory.Frozen Option.frozen Perm.frozen at hfrozen0
    cases hp0 : m0.perm a with
    | none =>
      cases hpf : mf.perm a with
      | none => rfl
      | some pf => rw [hp0, hpf] at hst; simp [Option.map] at hst
    | some p0 =>
      cases hpf : mf.perm a with
      | none => rw [hp0, hpf] at hst; simp [Option.map] at hst
      | some pf =>
        rw [hp0] at hfr0_a hfrozen0 hst; rw [hpf] at hfrf_a hst
        rcases p0 with ⟨r0, w0, x0, lf0, an0⟩; rcases pf with ⟨rf, wf, xf, lff, anf⟩
        unfold stripPerm at hst
        cases hk : keep a <;> cases r0 <;> cases w0 <;> cases x0 <;>
          cases rf <;> cases wf <;> cases xf <;> simp_all [Option.map, Option.x, Option.r, Option.w]

private theorem subroutineStop_of_processZeroizeOutcome {a : BitVec 64} {R : SepProp} {s0 sf : State}
    (h : SubroutineOutcome processZeroizeSpec a R s0 sf) :
    SubroutineStop s0 sf ∧ sf.status ≠ .Halted := by
  rcases h with ⟨hret, _, _⟩ | ⟨_, hpan⟩ | ⟨_, _, hex⟩ | ⟨_, hoom⟩
  · refine ⟨Or.inl hret, ?_⟩; rw [hret.2.2]; decide
  · dsimp only [processZeroizeSpec] at hpan; rw [satisfies_pure_sepConj] at hpan; exact False.elim hpan.1
  · dsimp only [processZeroizeSpec] at hex; rw [satisfies_pure_sepConj] at hex; exact False.elim hex.1
  · dsimp only [processZeroizeSpec] at hoom; rw [satisfies_pure_sepConj] at hoom; exact False.elim hoom.1

/-- Shared real-run `ProcessFieldsPreserved` + `mem.perm` equality extractor when `s0` satisfies
    `masterZeroizeSpec.pre` and `ActiveRealRun keep P_real P_sub entryTarget s0`. -/
private theorem activeRealRun_processZeroize {keep : BitVec 64 → Bool} {P_real P_sub : Program}
    {entryTarget : BitVec 64} (hsvc_real : P_real.svc = Syscall.standard) (hsvc_sub : P_sub.svc = Syscall.standard)
    (hreal_no : ∀ pc, keep pc = true → P_real.externAt? pc = none) (hsub_no : ∀ pc, P_sub.externAt? pc = none)
    (hsub_proc : subroutine_ok P_sub entryTarget processZeroizeSpec) {a : BitVec 64} {R : SepProp} {s0 : State}
    (hrun : s0.status = .Running) (hsp : s0.spAligned = true) (hpreM : s0.mem ⊨ masterZeroizeSpec.pre a s0 ∗ R)
    (hReal : ActiveRealRun keep P_real P_sub entryTarget s0) :
    ProcessFieldsPreserved s0 (Classical.choose hReal.2.2.2) := by
  have hpre : s0.mem ⊨ processZeroizeSpec.pre a s0 ∗ R := processZeroize_pre_of_masterZeroize_pre hpreM
  let s1 := s0.setPC entryTarget; let s1' := stripS keep s1
  have hs1_pre : s1.mem ⊨ processZeroizeSpec.pre a s1 ∗ R := by cases s0; exact hpre
  have hs1'_pre : s1'.mem ⊨ processZeroizeSpec.pre a s1' ∗ R := by
    have hsat := satisfies_stripExecOutside keep hs1_pre
    have heq : processZeroizeSpec.pre a s1' = processZeroizeSpec.pre a s1 := by dsimp only [s1']; cases s1; rfl
    rwa [heq]
  obtain ⟨sf', hsteps', hout'⟩ :=
    subroutine_ok_elim_steps_outcome hsub_proc a R s1' rfl hrun hs1'_pre hsp hReal.2.2.1
  obtain ⟨hstop1', hnhalt'⟩ := subroutineStop_of_processZeroizeOutcome hout'
  have hstop0' : SubroutineStop s0 sf' := hstop1'
  obtain ⟨sf, huntil, hstop_sf, hsf_eq, hfr_sf⟩ :=
    stepsUntil_of_stripS_standard (s0 := s0) hsvc_real hsvc_sub hreal_no
      (fun pc f he => nomatch hsub_no pc ▸ he) hReal.2.1 hsteps' hstop0' hnhalt' s1 rfl hReal.1
  have hchoose := Classical.choose_spec hReal.2.2.2
  have hdet : Classical.choose hReal.2.2.2 = sf := StepsUntil.deterministic hchoose.1 hchoose.2.1 huntil hstop_sf
  rw [hdet]
  rcases hout' with ⟨_, _, hpost'⟩ | ⟨_, hpan⟩ | ⟨_, _, hex⟩ | ⟨_, hoom⟩
  · dsimp only [processZeroizeSpec] at hpost'; rw [sepConj_assoc, satisfies_pure_sepConj] at hpost'
    have hproc' : ProcessFieldsPreserved s1' sf' := hpost'.1
    rw [hsf_eq] at hproc'
    have hperm : ∀ addr, sf.mem.perm addr = s0.mem.perm addr :=
      perm_eq_of_stripExecOutside_keepsFrozen hReal.1 hfr_sf huntil.toSteps.keepsFrozen hproc'.2.2.2.2.2.2.2
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, hperm⟩
    · cases s0; cases sf; exact hproc'.1
    · cases s0; cases sf; exact hproc'.2.1
    · cases s0; cases sf; exact hproc'.2.2.1
    · cases s0; cases sf; exact hproc'.2.2.2.1
    · cases s0; cases sf; exact hproc'.2.2.2.2.1
    · cases s0; cases sf; exact hproc'.2.2.2.2.2.1
    · cases s0; cases sf; exact hproc'.2.2.2.2.2.2.1
  · dsimp only [processZeroizeSpec] at hpan; rw [satisfies_pure_sepConj] at hpan; exact False.elim hpan.1
  · dsimp only [processZeroizeSpec] at hex; rw [satisfies_pure_sepConj] at hex; exact False.elim hex.1
  · dsimp only [processZeroizeSpec] at hoom; rw [satisfies_pure_sepConj] at hoom; exact False.elim hoom.1

private theorem vmPreserved_of_processFieldsPreserved {s0 sf : State} (h : ProcessFieldsPreserved s0 sf) :
    VmPreserved s0 sf :=
  ⟨⟨h.2.2.2.2.2.1, h.2.2.2.2.1, h.2.2.1⟩, h.2.2.2.2.2.2.1, h.2.2.2.2.2.2.2, FdsHiFrame.of_fs_eq h.1⟩

private theorem oomPoolPreserved_of_processFieldsPreserved {s0 sf : State} (h : ProcessFieldsPreserved s0 sf) :
    OomPreserved s0 sf ∧ PoolPreserved s0 sf :=
  ⟨⟨h.1, h.2.1, h.2.2.2.1⟩, ⟨h.2.2.2.2.2.1, h.2.2.2.2.1, h.2.2.1⟩⟩

-- 3.1 Unconditional `.fs`, `HookFsTraced`, `ExecFrozen`, and `lr` branch properties:

theorem zeroizeGhostHook_fs (keep : BitVec 64 → Bool) (P_real P_sub : Program) (entryTarget : BitVec 64) (s0 : State) :
    (zeroizeGhostHook keep P_real P_sub entryTarget s0).fs = s0.fs :=
  linkedCallHook_fs keep P_real P_sub entryTarget masterZeroizeSpec zeroizeSecretHook s0

theorem zeroizeGhostHookK_fs (keep : BitVec 64 → Bool) (P_real P_sub : Program) (entryTarget : BitVec 64) (s0 : State) :
    (zeroizeGhostHookK keep P_real P_sub entryTarget s0).fs = s0.fs :=
  linkedCallHook_fs keep P_real P_sub entryTarget (zeroizeSpecK keep masterZeroizeSpec) zeroizeSecretHook s0

theorem f3EmptyZeroizeGhostHook_fs (keep : BitVec 64 → Bool) (P_sub : Program) (entryTarget : BitVec 64) (s0 : State) :
    (f3EmptyZeroizeGhostHook keep P_sub entryTarget s0).fs = s0.fs :=
  f3LinkedCallHook_fs keep emptyStdProg P_sub entryTarget (fun _ _ => masterZeroizeSpec) zeroizeSecretHook s0

theorem f3EmptyZeroizeGhostHookK_fs (keep : BitVec 64 → Bool) (P_sub : Program) (entryTarget : BitVec 64) (s0 : State) :
    (f3EmptyZeroizeGhostHookK keep P_sub entryTarget s0).fs = s0.fs :=
  f3LinkedCallHook_fs keep emptyStdProg P_sub entryTarget (fun _ _ => zeroizeSpecK keep masterZeroizeSpec) zeroizeSecretHook s0

theorem zeroizeGhostHook_fsT (keep : BitVec 64 → Bool) (P_real P_sub : Program) (entryTarget : BitVec 64) :
    HookFsTraced IsFsC (zeroizeGhostHook keep P_real P_sub entryTarget) :=
  linkedCallHook_fsT keep P_real P_sub entryTarget masterZeroizeSpec zeroizeSecretHook

theorem zeroizeGhostHookK_fsT (keep : BitVec 64 → Bool) (P_real P_sub : Program) (entryTarget : BitVec 64) :
    HookFsTraced IsFsC (zeroizeGhostHookK keep P_real P_sub entryTarget) :=
  linkedCallHook_fsT keep P_real P_sub entryTarget (zeroizeSpecK keep masterZeroizeSpec) zeroizeSecretHook

theorem f3EmptyZeroizeGhostHook_fsT (keep : BitVec 64 → Bool) (P_sub : Program) (entryTarget : BitVec 64) :
    HookFsTraced IsFsC (f3EmptyZeroizeGhostHook keep P_sub entryTarget) :=
  f3LinkedCallHook_fsT keep emptyStdProg P_sub entryTarget (fun _ _ => masterZeroizeSpec) zeroizeSecretHook

theorem f3EmptyZeroizeGhostHookK_fsT (keep : BitVec 64 → Bool) (P_sub : Program) (entryTarget : BitVec 64) :
    HookFsTraced IsFsC (f3EmptyZeroizeGhostHookK keep P_sub entryTarget) :=
  f3LinkedCallHook_fsT keep emptyStdProg P_sub entryTarget (fun _ _ => zeroizeSpecK keep masterZeroizeSpec) zeroizeSecretHook

theorem zeroizeGhostHook_preserves_execFrozen (keep : BitVec 64 → Bool) (P_real P_sub : Program)
    (entryTarget : BitVec 64) {s0 : State} (hfr : ExecFrozen s0.mem) :
    ExecFrozen (zeroizeGhostHook keep P_real P_sub entryTarget s0).mem := by
  classical
  unfold zeroizeGhostHook linkedCallHook; split
  · split
    · rename_i _ hReal; exact (Classical.choose_spec hReal.2.2.2).2.2.2.2
    · rw [keepFsTrace_zeroizeSecretHook_eq]; exact zeroizeSecretHook_preserves_execFrozen hfr
  · exact hfr

theorem zeroizeGhostHookK_preserves_execFrozen (keep : BitVec 64 → Bool) (P_real P_sub : Program)
    (entryTarget : BitVec 64) {s0 : State} (hfr : ExecFrozen s0.mem) :
    ExecFrozen (zeroizeGhostHookK keep P_real P_sub entryTarget s0).mem := by
  classical
  unfold zeroizeGhostHookK linkedCallHook; split
  · split
    · rename_i _ hReal; exact (Classical.choose_spec hReal.2.2.2).2.2.2.2
    · rw [keepFsTrace_zeroizeSecretHook_eq]; exact zeroizeSecretHook_preserves_execFrozen hfr
  · exact hfr

theorem f3EmptyZeroizeGhostHook_preserves_execFrozen (keep : BitVec 64 → Bool) (P_sub : Program)
    (entryTarget : BitVec 64) {s0 : State} (hfr : ExecFrozen s0.mem) :
    ExecFrozen (f3EmptyZeroizeGhostHook keep P_sub entryTarget s0).mem := by
  rw [f3EmptyZeroizeGhostHook_eq]; exact zeroizeGhostHook_preserves_execFrozen keep emptyStdProg P_sub entryTarget hfr

theorem f3EmptyZeroizeGhostHookK_preserves_execFrozen (keep : BitVec 64 → Bool) (P_sub : Program)
    (entryTarget : BitVec 64) {s0 : State} (hfr : ExecFrozen s0.mem) :
    ExecFrozen (f3EmptyZeroizeGhostHookK keep P_sub entryTarget s0).mem := by
  rw [f3EmptyZeroizeGhostHookK_eq]; exact zeroizeGhostHookK_preserves_execFrozen keep emptyStdProg P_sub entryTarget hfr

theorem zeroizeGhostHookK_keepLr_false_of_noException {keep : BitVec 64 → Bool} {P_real P_sub : Program}
    {entryTarget : BitVec 64} {u : State}
    (hnoex : ∀ msg, (zeroizeGhostHookK keep P_real P_sub entryTarget u).status ≠ .Exception msg) :
    keep (u.readReg64 .lr) = false := by
  rcases linkedCallHook_activeRealPre_of_noException hnoex with ⟨_, _, a, R, hpre⟩
  dsimp only [zeroizeSpecK, memsetSpecK] at hpre; rw [sepConj_assoc, satisfies_pure_sepConj] at hpre; exact hpre.1

theorem f3EmptyZeroizeGhostHookK_keepLr_false_of_noException {keep : BitVec 64 → Bool} {P_sub : Program}
    {entryTarget : BitVec 64} {u : State}
    (hnoex : ∀ msg, (f3EmptyZeroizeGhostHookK keep P_sub entryTarget u).status ≠ .Exception msg) :
    keep (u.readReg64 .lr) = false := by
  rw [f3EmptyZeroizeGhostHookK_eq] at hnoex; exact zeroizeGhostHookK_keepLr_false_of_noException hnoex

theorem zeroizeGhostHook_of_keepLr_true {keep : BitVec 64 → Bool} {P_real P_sub : Program}
    {entryTarget : BitVec 64} {s0 : State} (hActPre : ActiveRealPre masterZeroizeSpec s0)
    (hlr_in : keep (s0.readReg64 .lr) = true) :
    zeroizeGhostHook keep P_real P_sub entryTarget s0 = zeroizeSecretHook s0 := by
  classical
  have hnReal : ¬ ActiveRealRun keep P_real P_sub entryTarget s0 := fun hR => by
    have hf := hR.2.1; rw [hlr_in] at hf; exact Bool.noConfusion hf
  unfold zeroizeGhostHook linkedCallHook; simp only [hActPre, hnReal, ↓reduceDIte]
  exact keepFsTrace_zeroizeSecretHook_eq s0

theorem zeroizeGhostHookK_of_keepLr_true {keep : BitVec 64 → Bool} {P_real P_sub : Program}
    {entryTarget : BitVec 64} {s0 : State} (hlr_in : keep (s0.readReg64 .lr) = true) :
    zeroizeGhostHookK keep P_real P_sub entryTarget s0 =
      { s0 with status := .Exception "ghost-hook precondition violated" } := by
  classical
  have hnAct : ¬ ActiveRealPre (zeroizeSpecK keep masterZeroizeSpec) s0 := by
    rintro ⟨_, _, a, R, hpre⟩; dsimp only [zeroizeSpecK, memsetSpecK] at hpre
    rw [sepConj_assoc, satisfies_pure_sepConj] at hpre
    have hf := hpre.1; rw [hlr_in] at hf; exact Bool.noConfusion hf
  unfold zeroizeGhostHookK linkedCallHook; simp only [hnAct, ↓reduceDIte]

theorem f3EmptyZeroizeGhostHook_of_keepLr_true {keep : BitVec 64 → Bool} {P_sub : Program}
    {entryTarget : BitVec 64} {s0 : State} (hActPre : ActiveRealPre masterZeroizeSpec s0)
    (hlr_in : keep (s0.readReg64 .lr) = true) :
    f3EmptyZeroizeGhostHook keep P_sub entryTarget s0 = zeroizeSecretHook s0 := by
  rw [f3EmptyZeroizeGhostHook_eq]; exact zeroizeGhostHook_of_keepLr_true hActPre hlr_in

theorem f3EmptyZeroizeGhostHookK_of_keepLr_true {keep : BitVec 64 → Bool} {P_sub : Program}
    {entryTarget : BitVec 64} {s0 : State} (hlr_in : keep (s0.readReg64 .lr) = true) :
    f3EmptyZeroizeGhostHookK keep P_sub entryTarget s0 =
      { s0 with status := .Exception "ghost-hook precondition violated" } := by
  rw [f3EmptyZeroizeGhostHookK_eq]; exact zeroizeGhostHookK_of_keepLr_true hlr_in

-- 3.2 Generic `hsub_proc` master `HookOk` & pointwise `VmPreserved` / `OomPoolPreserved` / `trace`:

section ProcessPointwiseSuite

variable {keep : BitVec 64 → Bool} {P_real P_sub : Program} {entryTarget : BitVec 64}
  (hsvc_real : P_real.svc = Syscall.standard) (hsvc_sub : P_sub.svc = Syscall.standard)
  (hreal_no : ∀ pc, keep pc = true → P_real.externAt? pc = none) (hsub_no : ∀ pc, P_sub.externAt? pc = none)
  (hsub_proc : subroutine_ok P_sub entryTarget processZeroizeSpec)
include hsvc_real hsvc_sub hreal_no hsub_no hsub_proc

theorem zeroizeGhostHook_master_ok_of_process :
    HookOk (zeroizeGhostHook keep P_real P_sub entryTarget) masterZeroizeSpec :=
  linkedCallHook_ok hsvc_real hsvc_sub hreal_no hsub_no
    (subroutine_ok_masterZeroize_of_process hsub_proc)
    (specStripSInvariant_masterZeroize keep) specPreservesFsTrace_masterZeroize
    masterZeroize_pre_setPC masterZeroize_outcome_setPC keepFsTrace_zeroizeSecretHook_master_ok

theorem zeroizeGhostHookK_masterK_ok_of_process :
    HookOk (zeroizeGhostHookK keep P_real P_sub entryTarget) (zeroizeSpecK keep masterZeroizeSpec) :=
  linkedCallHook_ok hsvc_real hsvc_sub hreal_no hsub_no
    (subroutine_ok_masterZeroizeK_of_process keep hsub_proc)
    (specStripSInvariant_masterZeroizeK keep) (specPreservesFsTrace_masterZeroizeK keep)
    (masterZeroizeK_pre_setPC keep) (masterZeroizeK_outcome_setPC keep)
    (keepFsTrace_zeroizeSecretHook_masterK_ok keep)

theorem zeroizeGhostHook_vmPreserved_of_process (s0 : State) :
    VmPreserved s0 (zeroizeGhostHook keep P_real P_sub entryTarget s0) := by
  classical
  unfold zeroizeGhostHook linkedCallHook; split
  · rename_i hActPre; split
    · rename_i hReal; rcases hActPre with ⟨hrun, hsp, a, R, hpre⟩
      exact vmPreserved_of_processFieldsPreserved
        (activeRealRun_processZeroize hsvc_real hsvc_sub hreal_no hsub_no hsub_proc hrun hsp hpre hReal)
    · rw [keepFsTrace_zeroizeSecretHook_eq]; exact zeroizeSecretHook_vmPreserved s0
  · exact VmPreserved.refl s0

theorem zeroizeGhostHookK_vmPreserved_of_process (s0 : State) :
    VmPreserved s0 (zeroizeGhostHookK keep P_real P_sub entryTarget s0) := by
  classical
  unfold zeroizeGhostHookK linkedCallHook; split
  · rename_i hActPre; split
    · rename_i hReal; rcases hActPre with ⟨hrun, hsp, a, R, hpre⟩
      dsimp only [zeroizeSpecK, memsetSpecK] at hpre; rw [sepConj_assoc, satisfies_pure_sepConj] at hpre
      exact vmPreserved_of_processFieldsPreserved
        (activeRealRun_processZeroize hsvc_real hsvc_sub hreal_no hsub_no hsub_proc hrun hsp hpre.2 hReal)
    · rw [keepFsTrace_zeroizeSecretHook_eq]; exact zeroizeSecretHook_vmPreserved s0
  · exact VmPreserved.refl s0

theorem zeroizeGhostHook_oomPoolPreserved_of_process (s0 : State) :
    OomPreserved s0 (zeroizeGhostHook keep P_real P_sub entryTarget s0) ∧
      PoolPreserved s0 (zeroizeGhostHook keep P_real P_sub entryTarget s0) := by
  classical
  unfold zeroizeGhostHook linkedCallHook; split
  · rename_i hActPre; split
    · rename_i hReal; rcases hActPre with ⟨hrun, hsp, a, R, hpre⟩
      exact oomPoolPreserved_of_processFieldsPreserved
        (activeRealRun_processZeroize hsvc_real hsvc_sub hreal_no hsub_no hsub_proc hrun hsp hpre hReal)
    · rw [keepFsTrace_zeroizeSecretHook_eq]; exact zeroizeSecretHook_preserves_oom_pool s0
  · exact ⟨⟨rfl, rfl, rfl⟩, ⟨rfl, rfl, rfl⟩⟩

theorem zeroizeGhostHookK_oomPoolPreserved_of_process (s0 : State) :
    OomPreserved s0 (zeroizeGhostHookK keep P_real P_sub entryTarget s0) ∧
      PoolPreserved s0 (zeroizeGhostHookK keep P_real P_sub entryTarget s0) := by
  classical
  unfold zeroizeGhostHookK linkedCallHook; split
  · rename_i hActPre; split
    · rename_i hReal; rcases hActPre with ⟨hrun, hsp, a, R, hpre⟩
      dsimp only [zeroizeSpecK, memsetSpecK] at hpre; rw [sepConj_assoc, satisfies_pure_sepConj] at hpre
      exact oomPoolPreserved_of_processFieldsPreserved
        (activeRealRun_processZeroize hsvc_real hsvc_sub hreal_no hsub_no hsub_proc hrun hsp hpre.2 hReal)
    · rw [keepFsTrace_zeroizeSecretHook_eq]; exact zeroizeSecretHook_preserves_oom_pool s0
  · exact ⟨⟨rfl, rfl, rfl⟩, ⟨rfl, rfl, rfl⟩⟩

theorem zeroizeGhostHook_trace_of_process (s0 : State) :
    (zeroizeGhostHook keep P_real P_sub entryTarget s0).trace = s0.trace := by
  classical
  unfold zeroizeGhostHook linkedCallHook; split
  · rename_i hActPre; split
    · rename_i hReal; rcases hActPre with ⟨hrun, hsp, a, R, hpre⟩
      exact (activeRealRun_processZeroize hsvc_real hsvc_sub hreal_no hsub_no hsub_proc hrun hsp hpre hReal).2.1
    · rfl
  · rfl

theorem zeroizeGhostHookK_trace_of_process (s0 : State) :
    (zeroizeGhostHookK keep P_real P_sub entryTarget s0).trace = s0.trace := by
  classical
  unfold zeroizeGhostHookK linkedCallHook; split
  · rename_i hActPre; split
    · rename_i hReal; rcases hActPre with ⟨hrun, hsp, a, R, hpre⟩
      dsimp only [zeroizeSpecK, memsetSpecK] at hpre; rw [sepConj_assoc, satisfies_pure_sepConj] at hpre
      exact (activeRealRun_processZeroize hsvc_real hsvc_sub hreal_no hsub_no hsub_proc hrun hsp hpre.2 hReal).2.1
    · rfl
  · rfl

end ProcessPointwiseSuite

-- 3.3 `f3Empty*` forwarding & `hasWords` specializations (`StaticSecret::drop` & `SharedSecret::drop`):

section F3EmptyProcessPointwise

variable {keep : BitVec 64 → Bool} {P_sub : Program} {entryTarget : BitVec 64}
  (hsvc_sub : P_sub.svc = Syscall.standard) (hsub_no : ∀ pc, P_sub.externAt? pc = none)
  (hsub_proc : subroutine_ok P_sub entryTarget processZeroizeSpec)
include hsvc_sub hsub_no hsub_proc

theorem f3EmptyZeroizeGhostHook_master_ok_of_process :
    HookOk (f3EmptyZeroizeGhostHook keep P_sub entryTarget) masterZeroizeSpec := by
  rw [f3EmptyZeroizeGhostHook_eq]
  exact zeroizeGhostHook_master_ok_of_process emptyStdProg_svc hsvc_sub (fun pc _ => emptyStdProg_externAt_none pc) hsub_no hsub_proc

theorem f3EmptyZeroizeGhostHookK_masterK_ok_of_process :
    HookOk (f3EmptyZeroizeGhostHookK keep P_sub entryTarget) (zeroizeSpecK keep masterZeroizeSpec) := by
  rw [f3EmptyZeroizeGhostHookK_eq]
  exact zeroizeGhostHookK_masterK_ok_of_process emptyStdProg_svc hsvc_sub (fun pc _ => emptyStdProg_externAt_none pc) hsub_no hsub_proc

theorem f3EmptyZeroizeGhostHook_vmPreserved_of_process (s0 : State) :
    VmPreserved s0 (f3EmptyZeroizeGhostHook keep P_sub entryTarget s0) := by
  rw [f3EmptyZeroizeGhostHook_eq]
  exact zeroizeGhostHook_vmPreserved_of_process emptyStdProg_svc hsvc_sub (fun pc _ => emptyStdProg_externAt_none pc) hsub_no hsub_proc s0

theorem f3EmptyZeroizeGhostHookK_vmPreserved_of_process (s0 : State) :
    VmPreserved s0 (f3EmptyZeroizeGhostHookK keep P_sub entryTarget s0) := by
  rw [f3EmptyZeroizeGhostHookK_eq]
  exact zeroizeGhostHookK_vmPreserved_of_process emptyStdProg_svc hsvc_sub (fun pc _ => emptyStdProg_externAt_none pc) hsub_no hsub_proc s0

theorem f3EmptyZeroizeGhostHook_oomPoolPreserved_of_process (s0 : State) :
    OomPreserved s0 (f3EmptyZeroizeGhostHook keep P_sub entryTarget s0) ∧
      PoolPreserved s0 (f3EmptyZeroizeGhostHook keep P_sub entryTarget s0) := by
  rw [f3EmptyZeroizeGhostHook_eq]
  exact zeroizeGhostHook_oomPoolPreserved_of_process emptyStdProg_svc hsvc_sub (fun pc _ => emptyStdProg_externAt_none pc) hsub_no hsub_proc s0

theorem f3EmptyZeroizeGhostHookK_oomPoolPreserved_of_process (s0 : State) :
    OomPreserved s0 (f3EmptyZeroizeGhostHookK keep P_sub entryTarget s0) ∧
      PoolPreserved s0 (f3EmptyZeroizeGhostHookK keep P_sub entryTarget s0) := by
  rw [f3EmptyZeroizeGhostHookK_eq]
  exact zeroizeGhostHookK_oomPoolPreserved_of_process emptyStdProg_svc hsvc_sub (fun pc _ => emptyStdProg_externAt_none pc) hsub_no hsub_proc s0

theorem f3EmptyZeroizeGhostHook_trace_of_process (s0 : State) :
    (f3EmptyZeroizeGhostHook keep P_sub entryTarget s0).trace = s0.trace := by
  rw [f3EmptyZeroizeGhostHook_eq]
  exact zeroizeGhostHook_trace_of_process emptyStdProg_svc hsvc_sub (fun pc _ => emptyStdProg_externAt_none pc) hsub_no hsub_proc s0

theorem f3EmptyZeroizeGhostHookK_trace_of_process (s0 : State) :
    (f3EmptyZeroizeGhostHookK keep P_sub entryTarget s0).trace = s0.trace := by
  rw [f3EmptyZeroizeGhostHookK_eq]
  exact zeroizeGhostHookK_trace_of_process emptyStdProg_svc hsvc_sub (fun pc _ => emptyStdProg_externAt_none pc) hsub_no hsub_proc s0

end F3EmptyProcessPointwise

section StaticSecretHasWords

variable {keep : BitVec 64 → Bool} {P_real P_sub : Program} {entryTarget : BitVec 64}
  (hsvc_real : P_real.svc = Syscall.standard) (hsvc_sub : P_sub.svc = Syscall.standard)
  (hreal_no : ∀ pc, keep pc = true → P_real.externAt? pc = none) (hsub_no : ∀ pc, P_sub.externAt? pc = none)
  (hwords : P_sub.hasWords entryTarget zeroize32Words)
include hsvc_real hsvc_sub hreal_no hsub_no hwords

theorem zeroizeGhostHook_master_ok : HookOk (zeroizeGhostHook keep P_real P_sub entryTarget) masterZeroizeSpec :=
  zeroizeGhostHook_master_ok_of_process hsvc_real hsvc_sub hreal_no hsub_no (subroutine_ok_processZeroize_of_hasWords hsub_no hwords)

theorem zeroizeGhostHookK_masterK_ok : HookOk (zeroizeGhostHookK keep P_real P_sub entryTarget) (zeroizeSpecK keep masterZeroizeSpec) :=
  zeroizeGhostHookK_masterK_ok_of_process hsvc_real hsvc_sub hreal_no hsub_no (subroutine_ok_processZeroize_of_hasWords hsub_no hwords)

theorem zeroizeGhostHook_vmPreserved (s0 : State) : VmPreserved s0 (zeroizeGhostHook keep P_real P_sub entryTarget s0) :=
  zeroizeGhostHook_vmPreserved_of_process hsvc_real hsvc_sub hreal_no hsub_no (subroutine_ok_processZeroize_of_hasWords hsub_no hwords) s0

theorem zeroizeGhostHookK_vmPreserved (s0 : State) : VmPreserved s0 (zeroizeGhostHookK keep P_real P_sub entryTarget s0) :=
  zeroizeGhostHookK_vmPreserved_of_process hsvc_real hsvc_sub hreal_no hsub_no (subroutine_ok_processZeroize_of_hasWords hsub_no hwords) s0

theorem zeroizeGhostHook_oomPoolPreserved (s0 : State) :
    OomPreserved s0 (zeroizeGhostHook keep P_real P_sub entryTarget s0) ∧ PoolPreserved s0 (zeroizeGhostHook keep P_real P_sub entryTarget s0) :=
  zeroizeGhostHook_oomPoolPreserved_of_process hsvc_real hsvc_sub hreal_no hsub_no (subroutine_ok_processZeroize_of_hasWords hsub_no hwords) s0

theorem zeroizeGhostHookK_oomPoolPreserved (s0 : State) :
    OomPreserved s0 (zeroizeGhostHookK keep P_real P_sub entryTarget s0) ∧ PoolPreserved s0 (zeroizeGhostHookK keep P_real P_sub entryTarget s0) :=
  zeroizeGhostHookK_oomPoolPreserved_of_process hsvc_real hsvc_sub hreal_no hsub_no (subroutine_ok_processZeroize_of_hasWords hsub_no hwords) s0

theorem zeroizeGhostHook_trace (s0 : State) : (zeroizeGhostHook keep P_real P_sub entryTarget s0).trace = s0.trace :=
  zeroizeGhostHook_trace_of_process hsvc_real hsvc_sub hreal_no hsub_no (subroutine_ok_processZeroize_of_hasWords hsub_no hwords) s0

theorem zeroizeGhostHookK_trace (s0 : State) : (zeroizeGhostHookK keep P_real P_sub entryTarget s0).trace = s0.trace :=
  zeroizeGhostHookK_trace_of_process hsvc_real hsvc_sub hreal_no hsub_no (subroutine_ok_processZeroize_of_hasWords hsub_no hwords) s0

end StaticSecretHasWords

section SharedSecretHullHasWords

variable {keep : BitVec 64 → Bool} {P_real P_sub : Program} {m : BitVec 64}
  (hsvc_real : P_real.svc = Syscall.standard) (hsvc_sub : P_sub.svc = Syscall.standard)
  (hreal_no : ∀ pc, keep pc = true → P_real.externAt? pc = none) (hsub_no : ∀ pc, P_sub.externAt? pc = none)
  (hwords : P_sub.hasWords m sharedSecretDropHullWords)
include hsvc_real hsvc_sub hreal_no hsub_no hwords

theorem sharedSecretDropGhostHook_master_ok : HookOk (sharedSecretDropGhostHook keep P_real P_sub m) masterZeroizeSpec :=
  zeroizeGhostHook_master_ok_of_process hsvc_real hsvc_sub hreal_no hsub_no (subroutine_ok_sharedSecretHull_processZeroize_of_hasWords hsub_no hwords)

theorem sharedSecretDropGhostHookK_masterK_ok : HookOk (sharedSecretDropGhostHookK keep P_real P_sub m) (zeroizeSpecK keep masterZeroizeSpec) :=
  zeroizeGhostHookK_masterK_ok_of_process hsvc_real hsvc_sub hreal_no hsub_no (subroutine_ok_sharedSecretHull_processZeroize_of_hasWords hsub_no hwords)

theorem sharedSecretDropGhostHook_vmPreserved (s0 : State) : VmPreserved s0 (sharedSecretDropGhostHook keep P_real P_sub m s0) :=
  zeroizeGhostHook_vmPreserved_of_process hsvc_real hsvc_sub hreal_no hsub_no (subroutine_ok_sharedSecretHull_processZeroize_of_hasWords hsub_no hwords) s0

theorem sharedSecretDropGhostHookK_vmPreserved (s0 : State) : VmPreserved s0 (sharedSecretDropGhostHookK keep P_real P_sub m s0) :=
  zeroizeGhostHookK_vmPreserved_of_process hsvc_real hsvc_sub hreal_no hsub_no (subroutine_ok_sharedSecretHull_processZeroize_of_hasWords hsub_no hwords) s0

theorem sharedSecretDropGhostHook_oomPoolPreserved (s0 : State) :
    OomPreserved s0 (sharedSecretDropGhostHook keep P_real P_sub m s0) ∧ PoolPreserved s0 (sharedSecretDropGhostHook keep P_real P_sub m s0) :=
  zeroizeGhostHook_oomPoolPreserved_of_process hsvc_real hsvc_sub hreal_no hsub_no (subroutine_ok_sharedSecretHull_processZeroize_of_hasWords hsub_no hwords) s0

theorem sharedSecretDropGhostHookK_oomPoolPreserved (s0 : State) :
    OomPreserved s0 (sharedSecretDropGhostHookK keep P_real P_sub m s0) ∧ PoolPreserved s0 (sharedSecretDropGhostHookK keep P_real P_sub m s0) :=
  zeroizeGhostHookK_oomPoolPreserved_of_process hsvc_real hsvc_sub hreal_no hsub_no (subroutine_ok_sharedSecretHull_processZeroize_of_hasWords hsub_no hwords) s0

theorem sharedSecretDropGhostHook_trace (s0 : State) : (sharedSecretDropGhostHook keep P_real P_sub m s0).trace = s0.trace :=
  zeroizeGhostHook_trace_of_process hsvc_real hsvc_sub hreal_no hsub_no (subroutine_ok_sharedSecretHull_processZeroize_of_hasWords hsub_no hwords) s0

theorem sharedSecretDropGhostHookK_trace (s0 : State) : (sharedSecretDropGhostHookK keep P_real P_sub m s0).trace = s0.trace :=
  zeroizeGhostHookK_trace_of_process hsvc_real hsvc_sub hreal_no hsub_no (subroutine_ok_sharedSecretHull_processZeroize_of_hasWords hsub_no hwords) s0

end SharedSecretHullHasWords

/-! ## 4. Complete Consumer `HookOk` Suite -/

section GenericHookOkSuite

variable {keep : BitVec 64 → Bool} {P_real P_sub : Program} {entryTarget : BitVec 64}
  (hsvc_real : P_real.svc = Syscall.standard) (hsvc_sub : P_sub.svc = Syscall.standard)
  (hreal_no : ∀ pc, keep pc = true → P_real.externAt? pc = none) (hsub_no : ∀ pc, P_sub.externAt? pc = none)
  (hsub_proc : subroutine_ok P_sub entryTarget processZeroizeSpec)
include hsvc_real hsvc_sub hreal_no hsub_no hsub_proc

-- 4.1 Plain contracts on `zeroizeGhostHook`:

theorem zeroizeGhostHook_zeroizeSecret_ok_of_process :
    HookOk (zeroizeGhostHook keep P_real P_sub entryTarget) zeroizeSecretSpec :=
  hookOk_zeroizeSecret_of_master (zeroizeGhostHook_master_ok_of_process hsvc_real hsvc_sub hreal_no hsub_no hsub_proc)

theorem zeroizeGhostHook_zeroizeSecret_keepsFs_ok_of_process :
    HookOk (zeroizeGhostHook keep P_real P_sub entryTarget) zeroizeSecretSpec.keepsFs :=
  hookOk_zeroizeSecret_keepsFs_of_master (zeroizeGhostHook_master_ok_of_process hsvc_real hsvc_sub hreal_no hsub_no hsub_proc)

theorem zeroizeGhostHook_zeroizeSecret_withFsPred_ok_of_process (Pfs : FsState → Prop) :
    HookOk (zeroizeGhostHook keep P_real P_sub entryTarget) (withFsPred Pfs zeroizeSecretSpec) :=
  hookOk_zeroizeSecret_withFsPred_of_master Pfs
    (zeroizeGhostHook_master_ok_of_process hsvc_real hsvc_sub hreal_no hsub_no hsub_proc)

theorem zeroizeGhostHook_zeroizeSecret_withStack_ok_of_process (stk : Nat) :
    HookOk (zeroizeGhostHook keep P_real P_sub entryTarget) (withStack zeroizeSecretSpec stk) :=
  hookOk_withStack_zeroizeSecret_of_master
    (zeroizeGhostHook_master_ok_of_process hsvc_real hsvc_sub hreal_no hsub_no hsub_proc) stk

theorem zeroizeGhostHook_cliZeroize_ok_of_process :
    HookOk (zeroizeGhostHook keep P_real P_sub entryTarget) zeroizeSpec :=
  hookOk_cliZeroize_of_master (zeroizeGhostHook_master_ok_of_process hsvc_real hsvc_sub hreal_no hsub_no hsub_proc)

theorem zeroizeGhostHook_cliZeroize_keepsFs_ok_of_process :
    HookOk (zeroizeGhostHook keep P_real P_sub entryTarget) zeroizeSpec.keepsFs :=
  hookOk_cliZeroize_keepsFs_of_master (zeroizeGhostHook_master_ok_of_process hsvc_real hsvc_sub hreal_no hsub_no hsub_proc)

theorem zeroizeGhostHook_zeroizeSecret_execFrozen_ok_of_process :
    HookOk (zeroizeGhostHook keep P_real P_sub entryTarget) (withExecFrozen zeroizeSecretSpec) :=
  hookOk_withExecFrozen_of_plain (zeroizeGhostHook_zeroizeSecret_ok_of_process hsvc_real hsvc_sub hreal_no hsub_no hsub_proc)

theorem zeroizeGhostHook_cliZeroize_execFrozen_ok_of_process :
    HookOk (zeroizeGhostHook keep P_real P_sub entryTarget) (withExecFrozen zeroizeSpec) :=
  hookOk_withExecFrozen_of_plain (zeroizeGhostHook_cliZeroize_ok_of_process hsvc_real hsvc_sub hreal_no hsub_no hsub_proc)

-- 4.2 Budget / `withVmPreserved` variants on `zeroizeGhostHook`:

theorem zeroizeGhostHook_masterBudget_ok_of_process :
    HookOk (zeroizeGhostHook keep P_real P_sub entryTarget) masterZeroizeBudgetSpec :=
  hookOk_withVmPreserved
    (zeroizeGhostHook_master_ok_of_process hsvc_real hsvc_sub hreal_no hsub_no hsub_proc)
    (zeroizeGhostHook_vmPreserved_of_process hsvc_real hsvc_sub hreal_no hsub_no hsub_proc)

theorem zeroizeGhostHook_zeroizeSecretBudget_ok_of_process :
    HookOk (zeroizeGhostHook keep P_real P_sub entryTarget) (withVmPreserved zeroizeSecretSpec) :=
  hookOk_withVmPreserved
    (zeroizeGhostHook_zeroizeSecret_ok_of_process hsvc_real hsvc_sub hreal_no hsub_no hsub_proc)
    (zeroizeGhostHook_vmPreserved_of_process hsvc_real hsvc_sub hreal_no hsub_no hsub_proc)

theorem zeroizeGhostHook_zeroizeSecretBudget_keepsFs_ok_of_process :
    HookOk (zeroizeGhostHook keep P_real P_sub entryTarget) (withVmPreserved zeroizeSecretSpec).keepsFs :=
  (zeroizeGhostHook_zeroizeSecretBudget_ok_of_process hsvc_real hsvc_sub hreal_no hsub_no hsub_proc).keepsFs
    (zeroizeGhostHook_fs keep P_real P_sub entryTarget)

theorem zeroizeGhostHook_zeroizeSecretBudget_withFsPred_ok_of_process (Pfs : FsState → Prop) :
    HookOk (zeroizeGhostHook keep P_real P_sub entryTarget)
      (withFsPred Pfs (withVmPreserved zeroizeSecretSpec)) :=
  hookOk_zeroizeSecretBudget_withFsPred_of_masterBudget Pfs
    (zeroizeGhostHook_masterBudget_ok_of_process hsvc_real hsvc_sub hreal_no hsub_no hsub_proc)

theorem zeroizeGhostHook_zeroizeSecretBudget_withStack_ok_of_process (stk : Nat) :
    HookOk (zeroizeGhostHook keep P_real P_sub entryTarget)
      (withStack (withVmPreserved zeroizeSecretSpec) stk) :=
  hookOk_withStack (zeroizeGhostHook_zeroizeSecretBudget_ok_of_process hsvc_real hsvc_sub hreal_no hsub_no hsub_proc) stk

theorem zeroizeGhostHook_cliZeroizeBudget_ok_of_process :
    HookOk (zeroizeGhostHook keep P_real P_sub entryTarget) (withVmPreserved zeroizeSpec) :=
  hookOk_withVmPreserved
    (zeroizeGhostHook_cliZeroize_ok_of_process hsvc_real hsvc_sub hreal_no hsub_no hsub_proc)
    (zeroizeGhostHook_vmPreserved_of_process hsvc_real hsvc_sub hreal_no hsub_no hsub_proc)

theorem zeroizeGhostHook_cliZeroizeBudget_keepsFs_ok_of_process :
    HookOk (zeroizeGhostHook keep P_real P_sub entryTarget) (withVmPreserved zeroizeSpec).keepsFs :=
  (zeroizeGhostHook_cliZeroizeBudget_ok_of_process hsvc_real hsvc_sub hreal_no hsub_no hsub_proc).keepsFs
    (zeroizeGhostHook_fs keep P_real P_sub entryTarget)

-- 4.2b C11 `withAlloc` pool-framed contracts on `zeroizeGhostHook`:

theorem zeroizeGhostHook_zeroizeSecret_withAlloc_ok_of_process {M : AllocCostModel}
    (A : RustCliAllocBudget M) (lim : BudgetLimits) :
    HookOk (zeroizeGhostHook keep P_real P_sub entryTarget) (withAlloc (M := M) A lim zeroizeSecretSpec) :=
  hookOk_withAlloc_of_withVmPreserved A lim
    (zeroizeGhostHook_zeroizeSecretBudget_ok_of_process hsvc_real hsvc_sub hreal_no hsub_no hsub_proc)

theorem zeroizeGhostHook_zeroizeSecretBudget_withAlloc_ok_of_process {M : AllocCostModel}
    (A : RustCliAllocBudget M) (lim : BudgetLimits) :
    HookOk (zeroizeGhostHook keep P_real P_sub entryTarget)
      (withAlloc (M := M) A lim (withVmPreserved zeroizeSecretSpec)) :=
  hookOk_withAlloc_withVmPreserved A lim
    (zeroizeGhostHook_zeroizeSecretBudget_ok_of_process hsvc_real hsvc_sub hreal_no hsub_no hsub_proc)

theorem zeroizeGhostHook_cliZeroize_withAlloc_ok_of_process {M : AllocCostModel}
    (A : RustCliAllocBudget M) (lim : BudgetLimits) :
    HookOk (zeroizeGhostHook keep P_real P_sub entryTarget) (withAlloc (M := M) A lim zeroizeSpec) :=
  hookOk_withAlloc_of_withVmPreserved A lim
    (zeroizeGhostHook_cliZeroizeBudget_ok_of_process hsvc_real hsvc_sub hreal_no hsub_no hsub_proc)

theorem zeroizeGhostHook_cliZeroizeBudget_withAlloc_ok_of_process {M : AllocCostModel}
    (A : RustCliAllocBudget M) (lim : BudgetLimits) :
    HookOk (zeroizeGhostHook keep P_real P_sub entryTarget) (withAlloc (M := M) A lim (withVmPreserved zeroizeSpec)) :=
  hookOk_withAlloc_withVmPreserved A lim
    (zeroizeGhostHook_cliZeroizeBudget_ok_of_process hsvc_real hsvc_sub hreal_no hsub_no hsub_proc)

-- 4.3 `zeroizeSpecK`-narrowed contracts on `zeroizeGhostHook` and `zeroizeGhostHookK`:

omit hsvc_real hsvc_sub hreal_no hsub_no hsub_proc in
theorem zeroizeGhostHook_any_zeroizeSpecK_ok {α : Type} {spec : Spec α} (keep' : BitVec 64 → Bool)
    (hh : HookOk (zeroizeGhostHook keep P_real P_sub entryTarget) spec) :
    HookOk (zeroizeGhostHook keep P_real P_sub entryTarget) (zeroizeSpecK keep' spec) :=
  hookOk_memsetSpecK_of_plain keep' hh

theorem zeroizeGhostHookK_zeroizeSecretK_ok_of_process :
    HookOk (zeroizeGhostHookK keep P_real P_sub entryTarget) (zeroizeSpecK keep zeroizeSecretSpec) :=
  hookOk_zeroizeSecretK_of_master keep (zeroizeGhostHookK_masterK_ok_of_process hsvc_real hsvc_sub hreal_no hsub_no hsub_proc)

theorem zeroizeGhostHookK_zeroizeSecretK_keepsFs_ok_of_process :
    HookOk (zeroizeGhostHookK keep P_real P_sub entryTarget) (zeroizeSpecK keep zeroizeSecretSpec).keepsFs :=
  hookOk_zeroizeSecretK_keepsFs_of_master keep (zeroizeGhostHookK_masterK_ok_of_process hsvc_real hsvc_sub hreal_no hsub_no hsub_proc)

theorem zeroizeGhostHookK_zeroizeSecretK_withFsPred_ok_of_process (Pfs : FsState → Prop) :
    HookOk (zeroizeGhostHookK keep P_real P_sub entryTarget) (zeroizeSpecK keep (withFsPred Pfs zeroizeSecretSpec)) :=
  hookOk_zeroizeSecretK_withFsPred_of_master keep Pfs (zeroizeGhostHookK_masterK_ok_of_process hsvc_real hsvc_sub hreal_no hsub_no hsub_proc)

theorem zeroizeGhostHookK_zeroizeSecretK_withStack_ok_of_process (stk : Nat) :
    HookOk (zeroizeGhostHookK keep P_real P_sub entryTarget) (zeroizeSpecK keep (withStack zeroizeSecretSpec stk)) :=
  hookOk_withStack_zeroizeSecretK_of_master keep (zeroizeGhostHookK_masterK_ok_of_process hsvc_real hsvc_sub hreal_no hsub_no hsub_proc) stk

theorem zeroizeGhostHookK_cliZeroizeK_ok_of_process :
    HookOk (zeroizeGhostHookK keep P_real P_sub entryTarget) (zeroizeSpecK keep zeroizeSpec) :=
  hookOk_cliZeroizeK_of_master keep (zeroizeGhostHookK_masterK_ok_of_process hsvc_real hsvc_sub hreal_no hsub_no hsub_proc)

theorem zeroizeGhostHookK_cliZeroizeK_keepsFs_ok_of_process :
    HookOk (zeroizeGhostHookK keep P_real P_sub entryTarget) (zeroizeSpecK keep zeroizeSpec).keepsFs :=
  (zeroizeGhostHookK_cliZeroizeK_ok_of_process hsvc_real hsvc_sub hreal_no hsub_no hsub_proc).keepsFs
    (zeroizeGhostHookK_fs keep P_real P_sub entryTarget)

theorem zeroizeGhostHookK_zeroizeSecretBudgetK_ok_of_process :
    HookOk (zeroizeGhostHookK keep P_real P_sub entryTarget) (zeroizeSpecK keep (withVmPreserved zeroizeSecretSpec)) := by
  rw [← zeroizeSpecK_withVmPreserved]
  exact hookOk_withVmPreserved
    (zeroizeGhostHookK_zeroizeSecretK_ok_of_process hsvc_real hsvc_sub hreal_no hsub_no hsub_proc)
    (zeroizeGhostHookK_vmPreserved_of_process hsvc_real hsvc_sub hreal_no hsub_no hsub_proc)

theorem zeroizeGhostHookK_zeroizeSecretBudgetK_keepsFs_ok_of_process :
    HookOk (zeroizeGhostHookK keep P_real P_sub entryTarget) (zeroizeSpecK keep (withVmPreserved zeroizeSecretSpec)).keepsFs :=
  (zeroizeGhostHookK_zeroizeSecretBudgetK_ok_of_process hsvc_real hsvc_sub hreal_no hsub_no hsub_proc).keepsFs
    (zeroizeGhostHookK_fs keep P_real P_sub entryTarget)

theorem zeroizeGhostHookK_zeroizeSecretBudgetK_withFsPred_ok_of_process (Pfs : FsState → Prop) :
    HookOk (zeroizeGhostHookK keep P_real P_sub entryTarget) (zeroizeSpecK keep (withFsPred Pfs (withVmPreserved zeroizeSecretSpec))) :=
  hookOk_zeroizeSpecK_withFsPred_of_keepsFs keep Pfs
    (zeroizeGhostHookK_zeroizeSecretBudgetK_keepsFs_ok_of_process hsvc_real hsvc_sub hreal_no hsub_no hsub_proc)
    (fun _ _ _ => rfl) (fun _ _ _ _ => rfl) (fun _ _ _ => rfl)

theorem zeroizeGhostHookK_zeroizeSecretBudgetK_withStack_ok_of_process (stk : Nat) :
    HookOk (zeroizeGhostHookK keep P_real P_sub entryTarget) (zeroizeSpecK keep (withStack (withVmPreserved zeroizeSecretSpec) stk)) :=
  hookOk_zeroizeSpecK_withStack_pureAbort keep
    (zeroizeGhostHookK_zeroizeSecretBudgetK_ok_of_process hsvc_real hsvc_sub hreal_no hsub_no hsub_proc) stk
    (fun _ _ _ => rfl) (fun _ _ _ _ => rfl) (fun _ _ _ => rfl)

theorem zeroizeGhostHookK_cliZeroizeBudgetK_ok_of_process :
    HookOk (zeroizeGhostHookK keep P_real P_sub entryTarget) (zeroizeSpecK keep (withVmPreserved zeroizeSpec)) := by
  rw [← zeroizeSpecK_withVmPreserved]
  exact hookOk_withVmPreserved
    (zeroizeGhostHookK_cliZeroizeK_ok_of_process hsvc_real hsvc_sub hreal_no hsub_no hsub_proc)
    (zeroizeGhostHookK_vmPreserved_of_process hsvc_real hsvc_sub hreal_no hsub_no hsub_proc)

theorem zeroizeGhostHookK_cliZeroizeBudgetK_keepsFs_ok_of_process :
    HookOk (zeroizeGhostHookK keep P_real P_sub entryTarget) (zeroizeSpecK keep (withVmPreserved zeroizeSpec)).keepsFs :=
  (zeroizeGhostHookK_cliZeroizeBudgetK_ok_of_process hsvc_real hsvc_sub hreal_no hsub_no hsub_proc).keepsFs
    (zeroizeGhostHookK_fs keep P_real P_sub entryTarget)

end GenericHookOkSuite

-- 4.4 `hasWords`, `withAlloc`, & `f3Empty*` consumer `HookOk` specializations:

section HasWordsRealConsumerHookOk

variable {keep : BitVec 64 → Bool} {P_real P_sub : Program} {entryTarget m : BitVec 64}
  (hsvc_real : P_real.svc = Syscall.standard) (hsvc_sub : P_sub.svc = Syscall.standard)
  (hreal_no : ∀ pc, keep pc = true → P_real.externAt? pc = none) (hsub_no : ∀ pc, P_sub.externAt? pc = none)
include hsvc_real hsvc_sub hreal_no hsub_no

theorem zeroizeGhostHook_zeroizeSecret_ok (hwords : P_sub.hasWords entryTarget zeroize32Words) :
    HookOk (zeroizeGhostHook keep P_real P_sub entryTarget) zeroizeSecretSpec :=
  zeroizeGhostHook_zeroizeSecret_ok_of_process hsvc_real hsvc_sub hreal_no hsub_no (subroutine_ok_processZeroize_of_hasWords hsub_no hwords)

theorem zeroizeGhostHook_zeroizeSecretBudget_ok (hwords : P_sub.hasWords entryTarget zeroize32Words) :
    HookOk (zeroizeGhostHook keep P_real P_sub entryTarget) (withVmPreserved zeroizeSecretSpec) :=
  zeroizeGhostHook_zeroizeSecretBudget_ok_of_process hsvc_real hsvc_sub hreal_no hsub_no (subroutine_ok_processZeroize_of_hasWords hsub_no hwords)

theorem zeroizeGhostHook_zeroizeSecretBudget_withAlloc_ok {M : AllocCostModel} (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (hwords : P_sub.hasWords entryTarget zeroize32Words) :
    HookOk (zeroizeGhostHook keep P_real P_sub entryTarget) (withAlloc (M := M) A lim (withVmPreserved zeroizeSecretSpec)) :=
  zeroizeGhostHook_zeroizeSecretBudget_withAlloc_ok_of_process hsvc_real hsvc_sub hreal_no hsub_no
    (subroutine_ok_processZeroize_of_hasWords hsub_no hwords) A lim

theorem zeroizeGhostHook_cliZeroize_ok (hwords : P_sub.hasWords entryTarget zeroize32Words) :
    HookOk (zeroizeGhostHook keep P_real P_sub entryTarget) zeroizeSpec :=
  zeroizeGhostHook_cliZeroize_ok_of_process hsvc_real hsvc_sub hreal_no hsub_no (subroutine_ok_processZeroize_of_hasWords hsub_no hwords)

theorem sharedSecretDropGhostHook_zeroizeSecretBudget_ok (hwords : P_sub.hasWords m sharedSecretDropHullWords) :
    HookOk (sharedSecretDropGhostHook keep P_real P_sub m) (withVmPreserved zeroizeSecretSpec) :=
  zeroizeGhostHook_zeroizeSecretBudget_ok_of_process hsvc_real hsvc_sub hreal_no hsub_no (subroutine_ok_sharedSecretHull_processZeroize_of_hasWords hsub_no hwords)

theorem sharedSecretDropGhostHook_zeroizeSecretBudget_withAlloc_ok {M : AllocCostModel} (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (hwords : P_sub.hasWords m sharedSecretDropHullWords) :
    HookOk (sharedSecretDropGhostHook keep P_real P_sub m) (withAlloc (M := M) A lim (withVmPreserved zeroizeSecretSpec)) :=
  zeroizeGhostHook_zeroizeSecretBudget_withAlloc_ok_of_process hsvc_real hsvc_sub hreal_no hsub_no
    (subroutine_ok_sharedSecretHull_processZeroize_of_hasWords hsub_no hwords) A lim

end HasWordsRealConsumerHookOk

section F3EmptyConsumerHookOk

variable {keep : BitVec 64 → Bool} {P_sub : Program} {entryTarget m : BitVec 64}
  (hsvc_sub : P_sub.svc = Syscall.standard) (hsub_no : ∀ pc, P_sub.externAt? pc = none)
include hsvc_sub hsub_no

theorem f3EmptyZeroizeGhostHook_zeroizeSecretBudget_ok_of_process (hsub_proc : subroutine_ok P_sub entryTarget processZeroizeSpec) :
    HookOk (f3EmptyZeroizeGhostHook keep P_sub entryTarget) (withVmPreserved zeroizeSecretSpec) := by
  rw [f3EmptyZeroizeGhostHook_eq]
  exact zeroizeGhostHook_zeroizeSecretBudget_ok_of_process emptyStdProg_svc hsvc_sub (fun pc _ => emptyStdProg_externAt_none pc) hsub_no hsub_proc

theorem f3EmptyZeroizeGhostHook_zeroizeSecretBudget_withAlloc_ok_of_process {M : AllocCostModel}
    (A : RustCliAllocBudget M) (lim : BudgetLimits) (hsub_proc : subroutine_ok P_sub entryTarget processZeroizeSpec) :
    HookOk (f3EmptyZeroizeGhostHook keep P_sub entryTarget) (withAlloc (M := M) A lim (withVmPreserved zeroizeSecretSpec)) :=
  hookOk_withAlloc_withVmPreserved A lim (f3EmptyZeroizeGhostHook_zeroizeSecretBudget_ok_of_process hsvc_sub hsub_no hsub_proc)

theorem f3EmptyZeroizeGhostHookK_zeroizeSecretBudgetK_ok_of_process (hsub_proc : subroutine_ok P_sub entryTarget processZeroizeSpec) :
    HookOk (f3EmptyZeroizeGhostHookK keep P_sub entryTarget) (zeroizeSpecK keep (withVmPreserved zeroizeSecretSpec)) := by
  rw [f3EmptyZeroizeGhostHookK_eq]
  exact zeroizeGhostHookK_zeroizeSecretBudgetK_ok_of_process emptyStdProg_svc hsvc_sub (fun pc _ => emptyStdProg_externAt_none pc) hsub_no hsub_proc

theorem f3EmptyZeroizeGhostHook_zeroizeSecretBudget_ok (hwords : P_sub.hasWords entryTarget zeroize32Words) :
    HookOk (f3EmptyZeroizeGhostHook keep P_sub entryTarget) (withVmPreserved zeroizeSecretSpec) :=
  f3EmptyZeroizeGhostHook_zeroizeSecretBudget_ok_of_process hsvc_sub hsub_no (subroutine_ok_processZeroize_of_hasWords hsub_no hwords)

theorem f3EmptyZeroizeGhostHook_zeroizeSecretBudget_withAlloc_ok {M : AllocCostModel}
    (A : RustCliAllocBudget M) (lim : BudgetLimits) (hwords : P_sub.hasWords entryTarget zeroize32Words) :
    HookOk (f3EmptyZeroizeGhostHook keep P_sub entryTarget) (withAlloc (M := M) A lim (withVmPreserved zeroizeSecretSpec)) :=
  hookOk_withAlloc_withVmPreserved A lim (f3EmptyZeroizeGhostHook_zeroizeSecretBudget_ok hsvc_sub hsub_no hwords)

theorem f3EmptySharedSecretDropGhostHook_zeroizeSecretBudget_ok (hwords : P_sub.hasWords m sharedSecretDropHullWords) :
    HookOk (f3EmptySharedSecretDropGhostHook keep P_sub m) (withVmPreserved zeroizeSecretSpec) :=
  f3EmptyZeroizeGhostHook_zeroizeSecretBudget_ok_of_process hsvc_sub hsub_no (subroutine_ok_sharedSecretHull_processZeroize_of_hasWords hsub_no hwords)

theorem f3EmptySharedSecretDropGhostHook_zeroizeSecretBudget_withAlloc_ok {M : AllocCostModel}
    (A : RustCliAllocBudget M) (lim : BudgetLimits) (hwords : P_sub.hasWords m sharedSecretDropHullWords) :
    HookOk (f3EmptySharedSecretDropGhostHook keep P_sub m) (withAlloc (M := M) A lim (withVmPreserved zeroizeSecretSpec)) :=
  hookOk_withAlloc_withVmPreserved A lim (f3EmptySharedSecretDropGhostHook_zeroizeSecretBudget_ok hsvc_sub hsub_no hwords)

end F3EmptyConsumerHookOk

/-! ## 5. Stock-Safe `StepsVisitedIn` Witnesses & `hLiftVis` Guarded Replays -/

/-- Stock-safe `h2fsgen_StepsVisitedIn` execution witness for `zeroizeGhostHook` on `P_run`. -/
theorem zeroizeGhostHook_visitedIn_of_process {keep : BitVec 64 → Bool} {P_run P_sub : Program}
    {entryTarget : BitVec 64} (hsvc_run : P_run.svc = Syscall.standard) (hsvc_sub : P_sub.svc = Syscall.standard)
    (hrun_no : ∀ pc, keep pc = true → P_run.externAt? pc = none) (hsub_no : ∀ pc, P_sub.externAt? pc = none)
    (hsub_proc : subroutine_ok P_sub entryTarget processZeroizeSpec) {u : State} (hrun : u.status = .Running)
    (hnoex : ∀ msg, (zeroizeGhostHook keep P_run P_sub entryTarget u).status ≠ .Exception msg)
    (hFr : ExecFrozen u.mem) (hlr_out : keep (u.readReg64 .lr) = false)
    (hCodeSub : P_sub.CodeLoaded (stripExecOutside keep u.mem)) :
    let sf_g := zeroizeGhostHook keep P_run P_sub entryTarget u
    h2fsgen_StepsVisitedIn keep P_run (u.setPC entryTarget) sf_g ∧ ExecFrozen sf_g.mem ∧ sf_g.fs = u.fs := by
  classical
  have hActPre : ActiveRealPre masterZeroizeSpec u := linkedCallHook_activeRealPre_of_noException hnoex
  have ⟨_, hsp, a, R, hpre⟩ := hActPre
  obtain ⟨sf, huntil, hstop, _, hfs, hfst, hfr_sf, hvis⟩ :=
    h2fsgen_real_subroutine_run_visitedIn_of_stripS hsvc_run hsvc_sub hrun_no hsub_no
      (subroutine_ok_masterZeroize_of_process hsub_proc)
      (specStripSInvariant_masterZeroize keep) specPreservesFsTrace_masterZeroize
      masterZeroize_pre_setPC masterZeroize_outcome_setPC hrun hsp hpre hFr hlr_out hCodeSub
  have hReal : ActiveRealRun keep P_run P_sub entryTarget u := ⟨hFr, hlr_out, hCodeSub, sf, huntil, hstop, hfs, hfst, hfr_sf⟩
  have heq : zeroizeGhostHook keep P_run P_sub entryTarget u = sf := by
    unfold zeroizeGhostHook linkedCallHook; simp only [hActPre, hReal, ↓reduceDIte]
    have hchoose := Classical.choose_spec hReal.2.2.2
    exact h2fsgen_stepsUntil_det hchoose.1 hchoose.2.1 huntil hstop
  dsimp only; rw [heq]; exact ⟨hvis, hfr_sf, hfs⟩

/-- Stock-safe `h2fsgen_StepsVisitedIn` execution witness for `zeroizeGhostHookK` on `P_run`. -/
theorem zeroizeGhostHookK_visitedIn_of_process {keep : BitVec 64 → Bool} {P_run P_sub : Program}
    {entryTarget : BitVec 64} (hsvc_run : P_run.svc = Syscall.standard) (hsvc_sub : P_sub.svc = Syscall.standard)
    (hrun_no : ∀ pc, keep pc = true → P_run.externAt? pc = none) (hsub_no : ∀ pc, P_sub.externAt? pc = none)
    (hsub_proc : subroutine_ok P_sub entryTarget processZeroizeSpec) {u : State} (hrun : u.status = .Running)
    (hnoex : ∀ msg, (zeroizeGhostHookK keep P_run P_sub entryTarget u).status ≠ .Exception msg)
    (hFr : ExecFrozen u.mem) (hCodeSub : P_sub.CodeLoaded (stripExecOutside keep u.mem)) :
    let sf_g := zeroizeGhostHookK keep P_run P_sub entryTarget u
    h2fsgen_StepsVisitedIn keep P_run (u.setPC entryTarget) sf_g ∧ ExecFrozen sf_g.mem ∧ sf_g.fs = u.fs := by
  classical
  have hlr_out : keep (u.readReg64 .lr) = false := zeroizeGhostHookK_keepLr_false_of_noException hnoex
  have hActPre : ActiveRealPre (zeroizeSpecK keep masterZeroizeSpec) u := linkedCallHook_activeRealPre_of_noException hnoex
  have ⟨_, hsp, a, R, hpre⟩ := hActPre
  obtain ⟨sf, huntil, hstop, _, hfs, hfst, hfr_sf, hvis⟩ :=
    h2fsgen_real_subroutine_run_visitedIn_of_stripS hsvc_run hsvc_sub hrun_no hsub_no
      (subroutine_ok_masterZeroizeK_of_process keep hsub_proc)
      (specStripSInvariant_masterZeroizeK keep) (specPreservesFsTrace_masterZeroizeK keep)
      (masterZeroizeK_pre_setPC keep) (masterZeroizeK_outcome_setPC keep) hrun hsp hpre hFr hlr_out hCodeSub
  have hReal : ActiveRealRun keep P_run P_sub entryTarget u := ⟨hFr, hlr_out, hCodeSub, sf, huntil, hstop, hfs, hfst, hfr_sf⟩
  have heq : zeroizeGhostHookK keep P_run P_sub entryTarget u = sf := by
    unfold zeroizeGhostHookK linkedCallHook; simp only [hActPre, hReal, ↓reduceDIte]
    have hchoose := Classical.choose_spec hReal.2.2.2
    exact h2fsgen_stepsUntil_det hchoose.1 hchoose.2.1 huntil hstop
  dsimp only; rw [heq]; exact ⟨hvis, hfr_sf, hfs⟩

/-- `W`-independent `h2fsgen_StepsVisitedIn keep emptyStdProg` witness for `f3EmptyZeroizeGhostHook`. -/
theorem f3EmptyZeroizeGhostHook_visitedIn_of_process {keep : BitVec 64 → Bool} {P_sub : Program}
    {entryTarget : BitVec 64} (hsvc_sub : P_sub.svc = Syscall.standard) (hsub_no : ∀ pc, P_sub.externAt? pc = none)
    (hsub_proc : subroutine_ok P_sub entryTarget processZeroizeSpec) {u : State} (hrun : u.status = .Running)
    (hnoex : ∀ msg, (f3EmptyZeroizeGhostHook keep P_sub entryTarget u).status ≠ .Exception msg)
    (hFr : ExecFrozen u.mem) (hlr_out : keep (u.readReg64 .lr) = false)
    (hCodeSub : P_sub.CodeLoaded (stripExecOutside keep u.mem)) :
    let sf_g := f3EmptyZeroizeGhostHook keep P_sub entryTarget u
    h2fsgen_StepsVisitedIn keep emptyStdProg (u.setPC entryTarget) sf_g ∧ ExecFrozen sf_g.mem ∧ sf_g.fs = u.fs := by
  dsimp only; rw [f3EmptyZeroizeGhostHook_eq] at hnoex ⊢
  exact zeroizeGhostHook_visitedIn_of_process emptyStdProg_svc hsvc_sub
    (fun pc _ => emptyStdProg_externAt_none pc) hsub_no hsub_proc hrun hnoex hFr hlr_out hCodeSub

/-- `W`-independent `h2fsgen_StepsVisitedIn keep emptyStdProg` witness for `f3EmptyZeroizeGhostHookK`. -/
theorem f3EmptyZeroizeGhostHookK_visitedIn_of_process {keep : BitVec 64 → Bool} {P_sub : Program}
    {entryTarget : BitVec 64} (hsvc_sub : P_sub.svc = Syscall.standard) (hsub_no : ∀ pc, P_sub.externAt? pc = none)
    (hsub_proc : subroutine_ok P_sub entryTarget processZeroizeSpec) {u : State} (hrun : u.status = .Running)
    (hnoex : ∀ msg, (f3EmptyZeroizeGhostHookK keep P_sub entryTarget u).status ≠ .Exception msg)
    (hFr : ExecFrozen u.mem) (hCodeSub : P_sub.CodeLoaded (stripExecOutside keep u.mem)) :
    let sf_g := f3EmptyZeroizeGhostHookK keep P_sub entryTarget u
    h2fsgen_StepsVisitedIn keep emptyStdProg (u.setPC entryTarget) sf_g ∧ ExecFrozen sf_g.mem ∧ sf_g.fs = u.fs := by
  dsimp only; rw [f3EmptyZeroizeGhostHookK_eq] at hnoex ⊢
  exact zeroizeGhostHookK_visitedIn_of_process emptyStdProg_svc hsvc_sub
    (fun pc _ => emptyStdProg_externAt_none pc) hsub_no hsub_proc hrun hnoex hFr hCodeSub

/-- `StaticSecret::drop` (`zeroize32Words`) `StepsVisitedIn` corollary for `f3EmptyZeroizeGhostHook`. -/
theorem f3EmptyZeroizeGhostHook_visitedIn {keep : BitVec 64 → Bool} {P_sub : Program} {entryTarget : BitVec 64}
    (hsvc_sub : P_sub.svc = Syscall.standard) (hsub_no : ∀ pc, P_sub.externAt? pc = none)
    (hwords : P_sub.hasWords entryTarget zeroize32Words) {u : State} (hrun : u.status = .Running)
    (hnoex : ∀ msg, (f3EmptyZeroizeGhostHook keep P_sub entryTarget u).status ≠ .Exception msg)
    (hFr : ExecFrozen u.mem) (hlr_out : keep (u.readReg64 .lr) = false)
    (hCodeSub : P_sub.CodeLoaded (stripExecOutside keep u.mem)) :
    let sf_g := f3EmptyZeroizeGhostHook keep P_sub entryTarget u
    h2fsgen_StepsVisitedIn keep emptyStdProg (u.setPC entryTarget) sf_g ∧ ExecFrozen sf_g.mem ∧ sf_g.fs = u.fs :=
  f3EmptyZeroizeGhostHook_visitedIn_of_process hsvc_sub hsub_no
    (subroutine_ok_processZeroize_of_hasWords hsub_no hwords) hrun hnoex hFr hlr_out hCodeSub

/-- `StaticSecret::drop` (`zeroize32Words`) `StepsVisitedIn` corollary for `f3EmptyZeroizeGhostHookK`. -/
theorem f3EmptyZeroizeGhostHookK_visitedIn {keep : BitVec 64 → Bool} {P_sub : Program} {entryTarget : BitVec 64}
    (hsvc_sub : P_sub.svc = Syscall.standard) (hsub_no : ∀ pc, P_sub.externAt? pc = none)
    (hwords : P_sub.hasWords entryTarget zeroize32Words) {u : State} (hrun : u.status = .Running)
    (hnoex : ∀ msg, (f3EmptyZeroizeGhostHookK keep P_sub entryTarget u).status ≠ .Exception msg)
    (hFr : ExecFrozen u.mem) (hCodeSub : P_sub.CodeLoaded (stripExecOutside keep u.mem)) :
    let sf_g := f3EmptyZeroizeGhostHookK keep P_sub entryTarget u
    h2fsgen_StepsVisitedIn keep emptyStdProg (u.setPC entryTarget) sf_g ∧ ExecFrozen sf_g.mem ∧ sf_g.fs = u.fs :=
  f3EmptyZeroizeGhostHookK_visitedIn_of_process hsvc_sub hsub_no
    (subroutine_ok_processZeroize_of_hasWords hsub_no hwords) hrun hnoex hFr hCodeSub

/-- `SharedSecret::drop` (`sharedSecretDropHullWords` at `m + sharedSecretDropEntryOff`) `StepsVisitedIn` corollary. -/
theorem f3EmptySharedSecretDropGhostHook_visitedIn {keep : BitVec 64 → Bool} {P_sub : Program} {m : BitVec 64}
    (hsvc_sub : P_sub.svc = Syscall.standard) (hsub_no : ∀ pc, P_sub.externAt? pc = none)
    (hwords : P_sub.hasWords m sharedSecretDropHullWords) {u : State} (hrun : u.status = .Running)
    (hnoex : ∀ msg, (f3EmptySharedSecretDropGhostHook keep P_sub m u).status ≠ .Exception msg)
    (hFr : ExecFrozen u.mem) (hlr_out : keep (u.readReg64 .lr) = false)
    (hCodeSub : P_sub.CodeLoaded (stripExecOutside keep u.mem)) :
    let sf_g := f3EmptySharedSecretDropGhostHook keep P_sub m u
    h2fsgen_StepsVisitedIn keep emptyStdProg (u.setPC (m + sharedSecretDropEntryOff)) sf_g ∧
      ExecFrozen sf_g.mem ∧ sf_g.fs = u.fs :=
  f3EmptyZeroizeGhostHook_visitedIn_of_process hsvc_sub hsub_no
    (subroutine_ok_sharedSecretHull_processZeroize_of_hasWords hsub_no hwords) hrun hnoex hFr hlr_out hCodeSub

/-- `SharedSecret::drop` (`sharedSecretDropHullWords` at `m + sharedSecretDropEntryOff`) `StepsVisitedIn` `K` corollary. -/
theorem f3EmptySharedSecretDropGhostHookK_visitedIn {keep : BitVec 64 → Bool} {P_sub : Program} {m : BitVec 64}
    (hsvc_sub : P_sub.svc = Syscall.standard) (hsub_no : ∀ pc, P_sub.externAt? pc = none)
    (hwords : P_sub.hasWords m sharedSecretDropHullWords) {u : State} (hrun : u.status = .Running)
    (hnoex : ∀ msg, (f3EmptySharedSecretDropGhostHookK keep P_sub m u).status ≠ .Exception msg)
    (hFr : ExecFrozen u.mem) (hCodeSub : P_sub.CodeLoaded (stripExecOutside keep u.mem)) :
    let sf_g := f3EmptySharedSecretDropGhostHookK keep P_sub m u
    h2fsgen_StepsVisitedIn keep emptyStdProg (u.setPC (m + sharedSecretDropEntryOff)) sf_g ∧
      ExecFrozen sf_g.mem ∧ sf_g.fs = u.fs :=
  f3EmptyZeroizeGhostHookK_visitedIn_of_process hsvc_sub hsub_no
    (subroutine_ok_sharedSecretHull_processZeroize_of_hasWords hsub_no hwords) hrun hnoex hFr hCodeSub

section StockSafeVisitedInReplays

variable {InvMem : Memory → Prop} {keep : BitVec 64 → Bool} {P_real P_sub : Program}
  {stubPc entryTarget : BitVec 64}
  (hsvc_sub : P_sub.svc = Syscall.standard) (hsub_no : ∀ pc, P_sub.externAt? pc = none)
  (hsub_proc : subroutine_ok P_sub entryTarget processZeroizeSpec)
  (hreal_stub_none : P_real.externAt? stubPc = none)
  (hStub : StubReachesTargetOn InvMem P_real stubPc entryTarget)
  (hInvLoaded : ∀ m : Memory, ExecFrozen m → InvMem m → P_sub.CodeLoaded (stripExecOutside keep m))
  (hInvKf : ∀ m m' : Memory, InvMem m → m.KeepsFrozen m' → InvMem m')
  (hLiftVis : ∀ u sf : State, u.status = .Running → ExecFrozen u.mem → InvMem u.mem →
    h2fsgen_StepsVisitedIn keep emptyStdProg (u.setPC entryTarget) sf → Steps P_real (u.setPC entryTarget) sf)
include hsvc_sub hsub_no hsub_proc hreal_stub_none hStub hInvLoaded hInvKf hLiftVis

/-- Stock-safe `emptyStdProg → P_real` replay for `f3EmptyZeroizeGhostHook` via `hLiftVis`. -/
theorem f3EmptyZeroizeGhostHook_replayOn_of_visitedIn_process :
    P_real.externAt? stubPc = none ∧
    ∀ u : State, u.pc = stubPc → u.status = .Running →
      (∀ msg, (f3EmptyZeroizeGhostHook keep P_sub entryTarget u).status ≠ .Exception msg) →
      ExecFrozen u.mem → keep (u.readReg64 .lr) = false → InvMem u.mem →
      Steps P_real u (f3EmptyZeroizeGhostHook keep P_sub entryTarget u) ∧
      ExecFrozen (f3EmptyZeroizeGhostHook keep P_sub entryTarget u).mem ∧
      InvMem (f3EmptyZeroizeGhostHook keep P_sub entryTarget u).mem ∧
      (f3EmptyZeroizeGhostHook keep P_sub entryTarget u).fs = u.fs := by
  refine ⟨hreal_stub_none, fun u hpc hrun hnoex hfr hlr hinv => ?_⟩
  obtain ⟨hvis, hfr_sf, hfs_sf⟩ := f3EmptyZeroizeGhostHook_visitedIn_of_process hsvc_sub hsub_no
    hsub_proc hrun hnoex hfr hlr (hInvLoaded u.mem hfr hinv)
  have hSteps := (hStub u hpc hrun hfr hinv).trans (hLiftVis u _ hrun hfr hinv hvis)
  exact ⟨hSteps, hfr_sf, hInvKf u.mem _ hinv hSteps.keepsFrozen, hfs_sf⟩

/-- Stock-safe `emptyStdProg → P_real` replay for `f3EmptyZeroizeGhostHookK` via `hLiftVis` (zero `lr` premise). -/
theorem f3EmptyZeroizeGhostHookK_replayOn_of_visitedIn_process :
    P_real.externAt? stubPc = none ∧
    ∀ u : State, u.pc = stubPc → u.status = .Running →
      (∀ msg, (f3EmptyZeroizeGhostHookK keep P_sub entryTarget u).status ≠ .Exception msg) →
      ExecFrozen u.mem → InvMem u.mem →
      Steps P_real u (f3EmptyZeroizeGhostHookK keep P_sub entryTarget u) ∧
      ExecFrozen (f3EmptyZeroizeGhostHookK keep P_sub entryTarget u).mem ∧
      InvMem (f3EmptyZeroizeGhostHookK keep P_sub entryTarget u).mem ∧
      (f3EmptyZeroizeGhostHookK keep P_sub entryTarget u).fs = u.fs := by
  refine ⟨hreal_stub_none, fun u hpc hrun hnoex hfr hinv => ?_⟩
  obtain ⟨hvis, hfr_sf, hfs_sf⟩ := f3EmptyZeroizeGhostHookK_visitedIn_of_process hsvc_sub hsub_no
    hsub_proc hrun hnoex hfr (hInvLoaded u.mem hfr hinv)
  have hSteps := (hStub u hpc hrun hfr hinv).trans (hLiftVis u _ hrun hfr hinv hvis)
  exact ⟨hSteps, hfr_sf, hInvKf u.mem _ hinv hSteps.keepsFrozen, hfs_sf⟩

/-- Single-row `GhostExternReplaysS` packager for `f3EmptyZeroizeGhostHook` via `hLiftVis`. -/
theorem f3EmptyZeroizeGhostHook_replaysS_of_visitedIn_process {P_ghost : Program}
    (hghost_stub : P_ghost.externAt? stubPc = some (f3EmptyZeroizeGhostHook keep P_sub entryTarget))
    (hother : ∀ pc, pc ≠ stubPc → P_ghost.externAt? pc = P_real.externAt? pc)
    (hreal_pres : ∀ pc f, P_real.externAt? pc = some f → ∀ u : State, u.status = .Running →
      u.mem.KeepsFrozen (f u).mem → ExecFrozen u.mem → InvMem u.mem → ExecFrozen (f u).mem ∧ InvMem (f u).mem) :
    GhostExternReplaysS keep (fun u => InvMem u.mem) P_ghost P_real := by
  have ⟨hnone, hstep⟩ := f3EmptyZeroizeGhostHook_replayOn_of_visitedIn_process hsvc_sub hsub_no
    hsub_proc hreal_stub_none hStub hInvLoaded hInvKf hLiftVis
  exact ghostExternReplaysS_of_single_stub hghost_stub hother hreal_pres
    ⟨hnone, fun u hpc hrun hnoex hfr hlr hinv =>
      let ⟨hs, hfr', hinv', _⟩ := hstep u hpc hrun hnoex hfr hlr hinv; ⟨hs, hfr', hinv'⟩⟩

/-- Single-row `GhostExternReplaysS keep_any` packager for `f3EmptyZeroizeGhostHookK` via `hLiftVis`. -/
theorem f3EmptyZeroizeGhostHookK_replaysS_of_visitedIn_process {keep_any : BitVec 64 → Bool} {P_ghost : Program}
    (hghost_stub : P_ghost.externAt? stubPc = some (f3EmptyZeroizeGhostHookK keep P_sub entryTarget))
    (hother : ∀ pc, pc ≠ stubPc → P_ghost.externAt? pc = P_real.externAt? pc)
    (hreal_pres : ∀ pc f, P_real.externAt? pc = some f → ∀ u : State, u.status = .Running →
      u.mem.KeepsFrozen (f u).mem → ExecFrozen u.mem → InvMem u.mem → ExecFrozen (f u).mem ∧ InvMem (f u).mem) :
    GhostExternReplaysS keep_any (fun u => InvMem u.mem) P_ghost P_real := by
  have ⟨hnone, hstep⟩ := f3EmptyZeroizeGhostHookK_replayOn_of_visitedIn_process hsvc_sub hsub_no
    hsub_proc hreal_stub_none hStub hInvLoaded hInvKf hLiftVis
  exact ghostExternReplaysS_of_single_stub hghost_stub hother hreal_pres
    ⟨hnone, fun u hpc hrun hnoex hfr _ hinv =>
      let ⟨hs, hfr', hinv', _⟩ := hstep u hpc hrun hnoex hfr hinv; ⟨hs, hfr', hinv'⟩⟩

end StockSafeVisitedInReplays

end LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.ZeroizeGhost
