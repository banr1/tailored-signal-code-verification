/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.WithLsRet -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.LinkedCallHookOn -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.SignalSession.Cli.AllocGhostLinkTransfer -- proof-setup: allow-public-import

/-!
# `withLsRet`-Narrowed `ActiveRealPre` / `linkedCallHook` Extractors & Generic `HookOk` Lifts (`HooksDehook.LinkedCallHookLs`)

Shared `K`-route ghost-hook bridge (Card **K2**, `r0_nonleaf_lr.md` §2.6, §3, §4; `rev_s1.md` F2)
for the 3 non-leaf `cliHookTablePlaced` rows (`memrchr`, `duration_since`, `SystemTime::add`):

1. **`ActiveRealPre` & `noException` `LsRetAddr624` extractors**:
   - **Primary `ActiveRealPre` form (`lsRetAddr624_of_activeRealPre_withLsRet`)**:
     `ActiveRealPre (withLsRet master) s0 → LsRetAddr624 (s0.readReg64 .lr)` (plus K3-chained
     `keepLr_false_of_activeRealPre_withLsRet`). Stated over `ActiveRealPre` per `rev_s1.md` F2 so
     it composes identically with both plain `linkedCallHook` (`linkedCallHook_activeRealPre_of_noException`)
     and guarded `linkedCallHookG` (`linkedCallHookG_activeRealPre_of_noException`) with zero S1
     changes.
   - **Generic `f : State → State` `noException` wrapper (`lsRetAddr624_of_noException_via_activeRealPre`)**
     and **concrete `linkedCallHook` corollaries (`linkedCallHook_lsRetAddr624_of_noException`,
     `linkedCallHook_keepLr_false_of_noException`)**, modeled on
     `memsetGhostHookK_keepLr_false_of_noException` (`MemsetGhost.lean:626`) and
     `h2k_keepSubLr_false_of_noException` (`ElfSlicesPqOomH2KHooks.lean:1759`), plus the dual
     `¬ LsRetAddr624` `.Exception` characterization (`linkedCallHook_withLsRet_of_not_lsRetAddr624`).
2. **`SpecStripSInvariant`, `SpecPreservesFsTrace`, `withRoData`, & `linkedCallHook_ok` lifts**:
   - `specStripSInvariant_withLsRet`: lifts `SpecStripSInvariant keep master` to `withLsRet master`.
   - `specPreservesFsTrace_withLsRet`: lifts `SpecPreservesFsTrace master` to `withLsRet master`.
   - `subroutine_ok_withRoData_withLsRet`: commutes `subroutine_ok P entry (withRoData addr bytes master)`
     to `subroutine_ok P entry (withRoData addr bytes (withLsRet master))` for S1 `roTableGuard`.
   - `linkedCallHook_withLsRet_ok`: packages `linkedCallHook_ok` on `withLsRet master`.
3. **Generic `HookOk` lifts from `withLsRet master` to `withLsRet consumer`**:
   Completely row-agnostic lifts over any hook `f : State → State` (applicable to both
   `linkedCallHook` and `linkedCallHookG`) and specialized to `linkedCallHook`:
   - `hookOk_withLsRet_of_simulates` / `linkedCallHook_withLsRet_consumer_ok_of_simulates`
     (via `SpecSimulates master consumer`, supporting panicking contracts such as `timeAddSpec`);
   - `hookOk_withLsRet_map_frame` / `linkedCallHook_withLsRet_consumer_ok_map_frame`
     (ghost reindexing `g : β → α` + frame `F : β → State → SepProp` with general `onPanic` /
     `onExit` / `onOom` entailments);
   - `hookOk_withLsRet_map_frame_pureAbort` / `linkedCallHook_withLsRet_consumer_ok_pureAbort`
     (`⌜False⌝`-abort convenience wrapper matching `MemcpyCode.hookOk_memcpySpecK_map_frame_pureAbort`);
   - `hookOk_withLsRet_conseq` / `hookOk_withLsRet_of_pre_post` (direct `Satisfies`-level and
     same-ghost pre/post entailment lifts).
-/

set_option autoImplicit false

public section

namespace LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.LinkedCallHookLs

open Arm64 ProofLib
open CryptoVerification (LibsignalPlacement)
open LibsignalBinary.Proofs.HookDischarge.RustStd.Common (SpecSimulates withRoData)
open LibsignalBinary.Proofs.Placed.ElfLsRetAddr (LsRetAddr624)
open LibsignalBinary.Proofs.SignalSession.Cli.AllocGhostLinkTransfer (
  ActiveRealPre SpecPreservesFsTrace SpecStripSInvariant
  keepFsTrace linkedCallHook linkedCallHook_ok
)
open LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.LinkedCallHookOn (
  linkedCallHook_activeRealPre_of_noException
)
open LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.WithLsRet (
  extract_withLsRet hookOk_withLsRet intro_withLsRet specSimulates_withLsRet
  subroutine_ok_withLsRet withLsRet withLsRet_outcome_setPC withLsRet_pre_setPC
  withLsRet_withRoData
)

/-! ## 1. `ActiveRealPre` & `noException` `LsRetAddr624` Extractors -/

/-- **Primary `ActiveRealPre` extractor (`rev_s1.md` F2):** `ActiveRealPre (withLsRet master) s0`
    implies `LsRetAddr624 (s0.readReg64 .lr)`. Applies uniformly to both plain `linkedCallHook` and
    guarded `linkedCallHookG`. -/
theorem lsRetAddr624_of_activeRealPre_withLsRet [LibsignalPlacement] {α : Type}
    {master : Spec α} {s0 : State}
    (hAct : ActiveRealPre (withLsRet master) s0) :
    LsRetAddr624 (s0.readReg64 .lr) := by
  rcases hAct with ⟨_, _, x, R, hpre⟩
  exact (extract_withLsRet hpre).1

/-- Chain `lsRetAddr624_of_activeRealPre_withLsRet` with a layout disjointness lemma
    `∀ lr, LsRetAddr624 lr → keepR lr = false` (Card K3) to obtain `keepR (s0.readReg64 .lr) = false`. -/
theorem keepLr_false_of_activeRealPre_withLsRet [LibsignalPlacement] {α : Type}
    {keepR : BitVec 64 → Bool} {master : Spec α} {s0 : State}
    (hKeep : ∀ lr, LsRetAddr624 lr → keepR lr = false)
    (hAct : ActiveRealPre (withLsRet master) s0) :
    keepR (s0.readReg64 .lr) = false :=
  hKeep _ (lsRetAddr624_of_activeRealPre_withLsRet hAct)

/-- Generic `noException ⇒ LsRetAddr624` extractor for any ghost hook `f : State → State` whose
    non-`.Exception` executions establish `ActiveRealPre (withLsRet master) s0` (covering both
    `linkedCallHook` and S1's `linkedCallHookG`). -/
theorem lsRetAddr624_of_noException_via_activeRealPre [LibsignalPlacement] {α : Type}
    {f : State → State} {master : Spec α} {s0 : State}
    (hActOfNoEx :
      (∀ msg, (f s0).status ≠ .Exception msg) → ActiveRealPre (withLsRet master) s0)
    (hnoex : ∀ msg, (f s0).status ≠ .Exception msg) :
    LsRetAddr624 (s0.readReg64 .lr) :=
  lsRetAddr624_of_activeRealPre_withLsRet (hActOfNoEx hnoex)

/-- K3-chained `noException ⇒ keepR (s0.readReg64 .lr) = false` extractor via `ActiveRealPre`. -/
theorem keepLr_false_of_noException_via_activeRealPre [LibsignalPlacement] {α : Type}
    {keepR : BitVec 64 → Bool} {f : State → State} {master : Spec α} {s0 : State}
    (hKeep : ∀ lr, LsRetAddr624 lr → keepR lr = false)
    (hActOfNoEx :
      (∀ msg, (f s0).status ≠ .Exception msg) → ActiveRealPre (withLsRet master) s0)
    (hnoex : ∀ msg, (f s0).status ≠ .Exception msg) :
    keepR (s0.readReg64 .lr) = false :=
  hKeep _ (lsRetAddr624_of_noException_via_activeRealPre hActOfNoEx hnoex)

/-- **Concrete `linkedCallHook` `noException ⇒ LsRetAddr624` lemma (K2 item 1):**
    Along any non-`.Exception` call step of
    `linkedCallHook keepR P_real P_sub entryTarget (withLsRet master) fallback`,
    `LsRetAddr624 (s0.readReg64 .lr)` holds. -/
theorem linkedCallHook_lsRetAddr624_of_noException [LibsignalPlacement] {α : Type}
    {keepR : BitVec 64 → Bool} {P_real P_sub : Program}
    {entryTarget : BitVec 64} {master : Spec α} {fallback : State → State}
    {s0 : State}
    (hnoex : ∀ msg,
      (linkedCallHook keepR P_real P_sub entryTarget (withLsRet master) fallback s0).status ≠
        .Exception msg) :
    LsRetAddr624 (s0.readReg64 .lr) :=
  lsRetAddr624_of_activeRealPre_withLsRet (linkedCallHook_activeRealPre_of_noException hnoex)

/-- K3-chained `linkedCallHook` `noException ⇒ keepR (s0.readReg64 .lr) = false` corollary
    (matching `memsetGhostHookK_keepLr_false_of_noException` in `MemsetGhost.lean:626`). -/
theorem linkedCallHook_keepLr_false_of_noException [LibsignalPlacement] {α : Type}
    {keepR : BitVec 64 → Bool} {P_real P_sub : Program}
    {entryTarget : BitVec 64} {master : Spec α} {fallback : State → State}
    {s0 : State}
    (hKeep : ∀ lr, LsRetAddr624 lr → keepR lr = false)
    (hnoex : ∀ msg,
      (linkedCallHook keepR P_real P_sub entryTarget (withLsRet master) fallback s0).status ≠
        .Exception msg) :
    keepR (s0.readReg64 .lr) = false :=
  hKeep _ (linkedCallHook_lsRetAddr624_of_noException hnoex)

/-- Dual contrapositive: if `¬ LsRetAddr624 (s0.readReg64 .lr)`, then `ActiveRealPre (withLsRet master) s0`
    is false regardless of memory contents. -/
theorem not_activeRealPre_withLsRet_of_not_lsRetAddr624 [LibsignalPlacement] {α : Type}
    {master : Spec α} {s0 : State}
    (hnLr : ¬ LsRetAddr624 (s0.readReg64 .lr)) :
    ¬ ActiveRealPre (withLsRet master) s0 :=
  fun hAct => hnLr (lsRetAddr624_of_activeRealPre_withLsRet hAct)

/-- Behavior of `linkedCallHook … (withLsRet master) …` when `¬ LsRetAddr624 (s0.readReg64 .lr)`:
    returns `{ s0 with status := .Exception "ghost-hook precondition violated" }` (paralleling
    `memsetGhostHookK_of_keepLr_true` in `MemsetGhost.lean:669`). -/
theorem linkedCallHook_withLsRet_of_not_lsRetAddr624 [LibsignalPlacement] {α : Type}
    {keepR : BitVec 64 → Bool} {P_real P_sub : Program}
    {entryTarget : BitVec 64} {master : Spec α} {fallback : State → State}
    {s0 : State}
    (hnLr : ¬ LsRetAddr624 (s0.readReg64 .lr)) :
    linkedCallHook keepR P_real P_sub entryTarget (withLsRet master) fallback s0 =
      { s0 with status := .Exception "ghost-hook precondition violated" } := by
  classical
  have hnAct : ¬ ActiveRealPre (withLsRet master) s0 :=
    not_activeRealPre_withLsRet_of_not_lsRetAddr624 hnLr
  unfold linkedCallHook
  simp only [hnAct, ↓reduceDIte]

/-! ## 2. `SpecStripSInvariant`, `SpecPreservesFsTrace`, `withRoData`, & Master `linkedCallHook_ok` -/

/-- Lift `SpecStripSInvariant keepR master` to `SpecStripSInvariant keepR (withLsRet master)`
    (since `stripS` preserves general-purpose registers including `.lr`). -/
theorem specStripSInvariant_withLsRet [LibsignalPlacement] {α : Type}
    {keepR : BitVec 64 → Bool} {master : Spec α}
    (hInv : SpecStripSInvariant keepR master) :
    SpecStripSInvariant keepR (withLsRet master) where
  pre_eq := fun x s => by
    dsimp only [withLsRet]
    have hlr : (stripS keepR s).readReg64 .lr = s.readReg64 .lr := by cases s; rfl
    rw [hlr, hInv.pre_eq x s]
  post_eq := hInv.post_eq
  onPanic_eq := hInv.onPanic_eq
  onExit_eq := hInv.onExit_eq
  onOom_eq := hInv.onOom_eq

/-- Lift `SpecPreservesFsTrace master` to `SpecPreservesFsTrace (withLsRet master)`
    (`SubroutineOutcome` is definitionally unchanged under `withLsRet`). -/
theorem specPreservesFsTrace_withLsRet [LibsignalPlacement] {α : Type}
    {master : Spec α} (hFsT : SpecPreservesFsTrace master) :
    SpecPreservesFsTrace (withLsRet master) :=
  hFsT

/-- Commute `subroutine_ok P_sub entry (withRoData addr bytes master)` directly to
    `subroutine_ok P_sub entry (withRoData addr bytes (withLsRet master))` (`rev_s1.md` F2: feeds
    S1's `withStateGuard (roTableGuard addr bytes) (withLsRet master)` with zero adapter). -/
theorem subroutine_ok_withRoData_withLsRet [LibsignalPlacement] {α : Type}
    {P_sub : Program} {entry addr : BitVec 64} {bytes : List (BitVec 8)} {master : Spec α}
    (hOk : subroutine_ok P_sub entry (withRoData addr bytes master)) :
    subroutine_ok P_sub entry (withRoData addr bytes (withLsRet master)) := by
  rw [← withLsRet_withRoData addr bytes master]
  exact subroutine_ok_withLsRet hOk

/-- Package `linkedCallHook_ok` on `withLsRet master` from unnarrowed `master` structural
    obligations (`subroutine_ok`, `SpecStripSInvariant`, `SpecPreservesFsTrace`, `setPC` invariance,
    and fallback `HookOk`). -/
theorem linkedCallHook_withLsRet_ok [LibsignalPlacement] {α : Type}
    {keepR : BitVec 64 → Bool} {P_real P_sub : Program}
    {entryTarget : BitVec 64} {master : Spec α} {fallback : State → State}
    (hsvc_real : P_real.svc = Syscall.standard)
    (hsvc_sub : P_sub.svc = Syscall.standard)
    (hreal_no : ∀ pc, keepR pc = true → P_real.externAt? pc = none)
    (hsub_no : ∀ pc, P_sub.externAt? pc = none)
    (hOk : subroutine_ok P_sub entryTarget (withLsRet master))
    (hInv : SpecStripSInvariant keepR master)
    (hFsT : SpecPreservesFsTrace master)
    (hPrePC : ∀ x (s : State) (pc : BitVec 64), master.pre x (s.setPC pc) = master.pre x s)
    (hOutPC : ∀ x (R : SepProp) (s0 sf : State) (pc : BitVec 64),
      SubroutineOutcome master x R (s0.setPC pc) sf → SubroutineOutcome master x R s0 sf)
    (hFallbackOk : HookOk (keepFsTrace fallback) (withLsRet master)) :
    HookOk (linkedCallHook keepR P_real P_sub entryTarget (withLsRet master) fallback)
      (withLsRet master) :=
  linkedCallHook_ok hsvc_real hsvc_sub hreal_no hsub_no hOk
    (specStripSInvariant_withLsRet hInv)
    (specPreservesFsTrace_withLsRet hFsT)
    (withLsRet_pre_setPC hPrePC)
    (withLsRet_outcome_setPC hOutPC)
    hFallbackOk

/-! ## 3. Generic `HookOk` Consequence Lifts from `withLsRet master` to `withLsRet consumer` -/

/-- Transport `HookOk` along `SpecSimulates spec₁ spec₂` (preserving normal returns as well as
    `onPanic`, `onExit`, and `onOom` outcomes). -/
theorem hookOk_of_simulates {α β : Type} {f : State → State}
    {spec₁ : Spec α} {spec₂ : Spec β}
    (hsim : SpecSimulates spec₁ spec₂) (hh : HookOk f spec₁) :
    HookOk f spec₂ := by
  intro y R s0 hrun hpre₂ hsp
  obtain ⟨x, R₁, hpre₁, hm⟩ := hsim y R s0 hpre₂
  obtain ⟨hkf, hsym, hout⟩ := hh x R₁ s0 hrun hpre₁ hsp
  exact ⟨hkf, hsym, hm (f s0) hout⟩

/-- Lift `HookOk f (withLsRet master)` to `HookOk f (withLsRet consumer)` along
    `SpecSimulates master consumer` (applicable to any ghost hook `f`, including `linkedCallHook`
    and `linkedCallHookG`, and to panicking specs such as `timeAddSpec`). -/
theorem hookOk_withLsRet_of_simulates [LibsignalPlacement] {α β : Type} {f : State → State}
    {master : Spec α} {consumer : Spec β}
    (hsim : SpecSimulates master consumer)
    (hh : HookOk f (withLsRet master)) :
    HookOk f (withLsRet consumer) :=
  hookOk_of_simulates (specSimulates_withLsRet hsim) hh

/-- Most general `Satisfies`-level consequence lift from `HookOk f (withLsRet master)` to
    `HookOk f (withLsRet consumer)`: given `s0.status = .Running`, `s0.spAligned = true`,
    `LsRetAddr624 (s0.readReg64 .lr)`, and `s0.mem ⊨ consumer.pre y s0 ∗ R`, the caller chooses
    master ghost `x` and frame `R'` with `s0.mem ⊨ master.pre x s0 ∗ R'` and transports
    `SubroutineOutcome master x R' s0 (f s0)` to `SubroutineOutcome consumer y R s0 (f s0)`. -/
theorem hookOk_withLsRet_conseq [LibsignalPlacement] {α β : Type} {f : State → State}
    {master : Spec α} {consumer : Spec β}
    (hh : HookOk f (withLsRet master))
    (himp : ∀ (y : β) (R : SepProp) (s0 : State),
      s0.status = .Running → s0.spAligned = true →
      LsRetAddr624 (s0.readReg64 .lr) →
      (s0.mem ⊨ consumer.pre y s0 ∗ R) →
      ∃ (x : α) (R' : SepProp),
        (s0.mem ⊨ master.pre x s0 ∗ R') ∧
        (∀ sf, sf = f s0 → s0.mem.KeepsFrozen sf.mem → sf.symtab = s0.symtab →
          SubroutineOutcome master x R' s0 sf → SubroutineOutcome consumer y R s0 sf)) :
    HookOk f (withLsRet consumer) := by
  intro y R s0 hrun hpre hsp
  obtain ⟨hlr, hpre_c⟩ := extract_withLsRet hpre
  obtain ⟨x, R', hpre_m, hm⟩ := himp y R s0 hrun hsp hlr hpre_c
  obtain ⟨hkf, hsym, hout⟩ := hh x R' s0 hrun (intro_withLsRet hlr hpre_m) hsp
  exact ⟨hkf, hsym, hm (f s0) rfl hkf hsym hout⟩

/-- Ghost-reindexing + frame `HookOk` lift across `withLsRet` supporting general `onPanic`,
    `onExit`, and `onOom` consequence entailments (covering both non-panicking rows and panicking
    `SystemTime::add`). -/
theorem hookOk_withLsRet_map_frame [LibsignalPlacement] {α β : Type} {f : State → State}
    {master : Spec α} {consumer : Spec β}
    (g : β → α) (F : β → State → SepProp)
    (hh : HookOk f (withLsRet master))
    (hpre : ∀ y s0, consumer.pre y s0 ⊢ master.pre (g y) s0 ∗ F y s0)
    (hpost : ∀ y s0 sf, sf = f s0 → s0.mem.KeepsFrozen sf.mem → sf.symtab = s0.symtab →
      master.post (g y) s0 sf ∗ F y s0 ⊢ consumer.post y s0 sf)
    (hpan : ∀ y s0 sf, sf = f s0 → s0.mem.KeepsFrozen sf.mem → sf.symtab = s0.symtab →
      master.onPanic (g y) s0 sf ∗ F y s0 ⊢ consumer.onPanic y s0 sf)
    (hex : ∀ y code s0 sf, sf = f s0 → s0.mem.KeepsFrozen sf.mem → sf.symtab = s0.symtab →
      master.onExit (g y) code s0 sf ∗ F y s0 ⊢ consumer.onExit y code s0 sf)
    (hoom : ∀ y s0 sf, sf = f s0 → s0.mem.KeepsFrozen sf.mem → sf.symtab = s0.symtab →
      master.onOom (g y) s0 sf ∗ F y s0 ⊢ consumer.onOom y s0 sf) :
    HookOk f (withLsRet consumer) := by
  refine hookOk_withLsRet_conseq hh fun y R s0 _ _ _ hp => ?_
  refine ⟨g y, F y s0 ∗ R, ?_, fun sf hsf hkf hsym hout => ?_⟩
  · rw [← sepConj_assoc]
    exact Satisfies.mono (sepConj_mono_left (hpre y s0)) hp
  · rcases hout with ⟨hret, hcc, hq⟩ | ⟨hpan_st, hp_sat⟩ | ⟨code, hex_st, he_sat⟩ | ⟨hoom_st, ho_sat⟩
    · refine Or.inl ⟨hret, hcc, ?_⟩
      rw [← sepConj_assoc] at hq
      exact Satisfies.mono (sepConj_mono_left (hpost y s0 sf hsf hkf hsym)) hq
    · refine Or.inr (Or.inl ⟨hpan_st, ?_⟩)
      rw [← sepConj_assoc] at hp_sat
      exact Satisfies.mono (sepConj_mono_left (hpan y s0 sf hsf hkf hsym)) hp_sat
    · refine Or.inr (Or.inr (Or.inl ⟨code, hex_st, ?_⟩))
      rw [← sepConj_assoc] at he_sat
      exact Satisfies.mono (sepConj_mono_left (hex y code s0 sf hsf hkf hsym)) he_sat
    · refine Or.inr (Or.inr (Or.inr ⟨hoom_st, ?_⟩))
      rw [← sepConj_assoc] at ho_sat
      exact Satisfies.mono (sepConj_mono_left (hoom y s0 sf hsf hkf hsym)) ho_sat

/-- Non-aborting (`⌜False⌝`) ghost-reindexing + frame `HookOk` lift across `withLsRet`
    (matching `MemcpyCode.hookOk_memcpySpecK_map_frame_pureAbort` for `memrchr` and
    `duration_since`). -/
theorem hookOk_withLsRet_map_frame_pureAbort [LibsignalPlacement] {α β : Type} {f : State → State}
    {master : Spec α} {consumer : Spec β}
    (g : β → α) (F : β → State → SepProp)
    (hh : HookOk f (withLsRet master))
    (hpre : ∀ y s0, consumer.pre y s0 ⊢ master.pre (g y) s0 ∗ F y s0)
    (hpost : ∀ y s0 sf, sf = f s0 → s0.mem.KeepsFrozen sf.mem → sf.symtab = s0.symtab →
      master.post (g y) s0 sf ∗ F y s0 ⊢ consumer.post y s0 sf)
    (hpan : ∀ x s0 sf, master.onPanic x s0 sf = ⌜False⌝ := by intros; rfl)
    (hex : ∀ x code s0 sf, master.onExit x code s0 sf = ⌜False⌝ := by intros; rfl)
    (hoom : ∀ x s0 sf, master.onOom x s0 sf = ⌜False⌝ := by intros; rfl) :
    HookOk f (withLsRet consumer) := by
  refine hookOk_withLsRet_map_frame g F hh hpre hpost
    (fun y s0 sf _ _ _ => ?_)
    (fun y code s0 sf _ _ _ => ?_)
    (fun y s0 sf _ _ _ => ?_)
  · rw [hpan (g y) s0 sf]; exact Entails.pure_left False.elim
  · rw [hex (g y) code s0 sf]; exact Entails.pure_left False.elim
  · rw [hoom (g y) s0 sf]; exact Entails.pure_left False.elim

/-- Same-ghost (`F = emp`) consequence lift across `withLsRet` when `consumer.pre` implies
    `master.pre` and `master` outcomes entail `consumer` outcomes. -/
theorem hookOk_withLsRet_of_pre_post [LibsignalPlacement] {α : Type} {f : State → State}
    {master consumer : Spec α}
    (hh : HookOk f (withLsRet master))
    (hpre : ∀ x s0, consumer.pre x s0 ⊢ master.pre x s0)
    (hpost : ∀ x s0 sf, sf = f s0 → s0.mem.KeepsFrozen sf.mem → sf.symtab = s0.symtab →
      master.post x s0 sf ⊢ consumer.post x s0 sf)
    (hpan : ∀ x s0 sf, master.onPanic x s0 sf ⊢ consumer.onPanic x s0 sf :=
      by intros; exact Entails.refl _)
    (hex : ∀ x code s0 sf, master.onExit x code s0 sf ⊢ consumer.onExit x code s0 sf :=
      by intros; exact Entails.refl _)
    (hoom : ∀ x s0 sf, master.onOom x s0 sf ⊢ consumer.onOom x s0 sf :=
      by intros; exact Entails.refl _) :
    HookOk f (withLsRet consumer) := by
  refine hookOk_withLsRet_map_frame id (fun _ _ => emp) hh
    (fun x s0 => by rw [sepConj_emp]; exact hpre x s0)
    (fun x s0 sf hsf hkf hsym => by rw [sepConj_emp]; exact hpost x s0 sf hsf hkf hsym)
    (fun x s0 sf _ _ _ => by rw [sepConj_emp]; exact hpan x s0 sf)
    (fun x code s0 sf _ _ _ => by rw [sepConj_emp]; exact hex x code s0 sf)
    (fun x s0 sf _ _ _ => by rw [sepConj_emp]; exact hoom x s0 sf)

/-! ## 4. Named `linkedCallHook` Specializations (K2 Item 2) -/

/-- Lift `HookOk (linkedCallHook … (withLsRet master) …) (withLsRet master)` to `withLsRet consumer`
    via `SpecSimulates master consumer`. -/
theorem linkedCallHook_withLsRet_consumer_ok_of_simulates [LibsignalPlacement] {α β : Type}
    {keepR : BitVec 64 → Bool} {P_real P_sub : Program}
    {entryTarget : BitVec 64} {master : Spec α} {consumer : Spec β}
    {fallback : State → State}
    (hh : HookOk (linkedCallHook keepR P_real P_sub entryTarget (withLsRet master) fallback)
      (withLsRet master))
    (hsim : SpecSimulates master consumer) :
    HookOk (linkedCallHook keepR P_real P_sub entryTarget (withLsRet master) fallback)
      (withLsRet consumer) :=
  hookOk_withLsRet_of_simulates hsim hh

/-- Lift `HookOk (linkedCallHook … (withLsRet master) …) (withLsRet master)` to `withLsRet consumer`
    via general `Satisfies`-level consequence `hookOk_withLsRet_conseq`. -/
theorem linkedCallHook_withLsRet_consumer_ok_conseq [LibsignalPlacement] {α β : Type}
    {keepR : BitVec 64 → Bool} {P_real P_sub : Program}
    {entryTarget : BitVec 64} {master : Spec α} {consumer : Spec β}
    {fallback : State → State}
    (hh : HookOk (linkedCallHook keepR P_real P_sub entryTarget (withLsRet master) fallback)
      (withLsRet master))
    (himp : ∀ (y : β) (R : SepProp) (s0 : State),
      s0.status = .Running → s0.spAligned = true →
      LsRetAddr624 (s0.readReg64 .lr) →
      (s0.mem ⊨ consumer.pre y s0 ∗ R) →
      ∃ (x : α) (R' : SepProp),
        (s0.mem ⊨ master.pre x s0 ∗ R') ∧
        (∀ sf, sf = linkedCallHook keepR P_real P_sub entryTarget (withLsRet master) fallback s0 →
          s0.mem.KeepsFrozen sf.mem → sf.symtab = s0.symtab →
          SubroutineOutcome master x R' s0 sf → SubroutineOutcome consumer y R s0 sf)) :
    HookOk (linkedCallHook keepR P_real P_sub entryTarget (withLsRet master) fallback)
      (withLsRet consumer) :=
  hookOk_withLsRet_conseq hh himp

/-- Lift `HookOk (linkedCallHook … (withLsRet master) …) (withLsRet master)` to `withLsRet consumer`
    via ghost-reindexing + frame with general abort entailments. -/
theorem linkedCallHook_withLsRet_consumer_ok_map_frame [LibsignalPlacement] {α β : Type}
    {keepR : BitVec 64 → Bool} {P_real P_sub : Program}
    {entryTarget : BitVec 64} {master : Spec α} {consumer : Spec β}
    {fallback : State → State}
    (g : β → α) (F : β → State → SepProp)
    (hh : HookOk (linkedCallHook keepR P_real P_sub entryTarget (withLsRet master) fallback)
      (withLsRet master))
    (hpre : ∀ y s0, consumer.pre y s0 ⊢ master.pre (g y) s0 ∗ F y s0)
    (hpost : ∀ y s0 sf,
      sf = linkedCallHook keepR P_real P_sub entryTarget (withLsRet master) fallback s0 →
      s0.mem.KeepsFrozen sf.mem → sf.symtab = s0.symtab →
      master.post (g y) s0 sf ∗ F y s0 ⊢ consumer.post y s0 sf)
    (hpan : ∀ y s0 sf,
      sf = linkedCallHook keepR P_real P_sub entryTarget (withLsRet master) fallback s0 →
      s0.mem.KeepsFrozen sf.mem → sf.symtab = s0.symtab →
      master.onPanic (g y) s0 sf ∗ F y s0 ⊢ consumer.onPanic y s0 sf)
    (hex : ∀ y code s0 sf,
      sf = linkedCallHook keepR P_real P_sub entryTarget (withLsRet master) fallback s0 →
      s0.mem.KeepsFrozen sf.mem → sf.symtab = s0.symtab →
      master.onExit (g y) code s0 sf ∗ F y s0 ⊢ consumer.onExit y code s0 sf)
    (hoom : ∀ y s0 sf,
      sf = linkedCallHook keepR P_real P_sub entryTarget (withLsRet master) fallback s0 →
      s0.mem.KeepsFrozen sf.mem → sf.symtab = s0.symtab →
      master.onOom (g y) s0 sf ∗ F y s0 ⊢ consumer.onOom y s0 sf) :
    HookOk (linkedCallHook keepR P_real P_sub entryTarget (withLsRet master) fallback)
      (withLsRet consumer) :=
  hookOk_withLsRet_map_frame g F hh hpre hpost hpan hex hoom

/-- Non-aborting (`⌜False⌝`) `linkedCallHook` consumer `HookOk` lift across `withLsRet`. -/
theorem linkedCallHook_withLsRet_consumer_ok_pureAbort [LibsignalPlacement] {α β : Type}
    {keepR : BitVec 64 → Bool} {P_real P_sub : Program}
    {entryTarget : BitVec 64} {master : Spec α} {consumer : Spec β}
    {fallback : State → State}
    (g : β → α) (F : β → State → SepProp)
    (hh : HookOk (linkedCallHook keepR P_real P_sub entryTarget (withLsRet master) fallback)
      (withLsRet master))
    (hpre : ∀ y s0, consumer.pre y s0 ⊢ master.pre (g y) s0 ∗ F y s0)
    (hpost : ∀ y s0 sf,
      sf = linkedCallHook keepR P_real P_sub entryTarget (withLsRet master) fallback s0 →
      s0.mem.KeepsFrozen sf.mem → sf.symtab = s0.symtab →
      master.post (g y) s0 sf ∗ F y s0 ⊢ consumer.post y s0 sf)
    (hpan : ∀ x s0 sf, master.onPanic x s0 sf = ⌜False⌝ := by intros; rfl)
    (hex : ∀ x code s0 sf, master.onExit x code s0 sf = ⌜False⌝ := by intros; rfl)
    (hoom : ∀ x s0 sf, master.onOom x s0 sf = ⌜False⌝ := by intros; rfl) :
    HookOk (linkedCallHook keepR P_real P_sub entryTarget (withLsRet master) fallback)
      (withLsRet consumer) :=
  hookOk_withLsRet_map_frame_pureAbort g F hh hpre hpost hpan hex hoom

/-- Same-ghost (`consumer.pre ⊢ master.pre`, `master.post ⊢ consumer.post`) `linkedCallHook`
    consumer `HookOk` lift across `withLsRet`. -/
theorem linkedCallHook_withLsRet_consumer_ok_of_pre_post [LibsignalPlacement] {α : Type}
    {keepR : BitVec 64 → Bool} {P_real P_sub : Program}
    {entryTarget : BitVec 64} {master consumer : Spec α}
    {fallback : State → State}
    (hh : HookOk (linkedCallHook keepR P_real P_sub entryTarget (withLsRet master) fallback)
      (withLsRet master))
    (hpre : ∀ x s0, consumer.pre x s0 ⊢ master.pre x s0)
    (hpost : ∀ x s0 sf,
      sf = linkedCallHook keepR P_real P_sub entryTarget (withLsRet master) fallback s0 →
      s0.mem.KeepsFrozen sf.mem → sf.symtab = s0.symtab →
      master.post x s0 sf ⊢ consumer.post x s0 sf)
    (hpan : ∀ x s0 sf, master.onPanic x s0 sf ⊢ consumer.onPanic x s0 sf :=
      by intros; exact Entails.refl _)
    (hex : ∀ x code s0 sf, master.onExit x code s0 sf ⊢ consumer.onExit x code s0 sf :=
      by intros; exact Entails.refl _)
    (hoom : ∀ x s0 sf, master.onOom x s0 sf ⊢ consumer.onOom x s0 sf :=
      by intros; exact Entails.refl _) :
    HookOk (linkedCallHook keepR P_real P_sub entryTarget (withLsRet master) fallback)
      (withLsRet consumer) :=
  hookOk_withLsRet_of_pre_post hh hpre hpost hpan hex hoom

end LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.LinkedCallHookLs
