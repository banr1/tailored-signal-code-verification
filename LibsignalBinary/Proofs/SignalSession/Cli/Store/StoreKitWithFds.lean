/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.PublicApi.StoreKit.PlacedBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.Heap.AllocWithFds
import LibsignalBinary.Proofs.Common.SharedHelpers
public meta import LibsignalBinary.Proofs.Common.SharedHelpers -- shake: keep
import Arm64.Trusted.Spec.Hoare
import Arm64.Trusted.Spec.SepLogic

/-!
# `StoreKit` Bridges from `FdsGe3Closed` Bundles at `A` to `withFds A`

When `lim.enforced = true` and a store kit's `fdsOk` is equivalent to `FdsGe3Closed`,
`(withFds A).pool lim st s` equals `⌜FdsGe3Closed s.fs⌝ ∗ A.pool lim st s` while preserving `live`
and `repAlloc` definitionally. Lifts all six `fds = true` CLI store-kit bundles at `A` to
`fds = false` store-kit bundles at `withFds A`.
-/

@[expose] public section

set_option autoImplicit false

namespace LibsignalBinary.Proofs.SignalSession.Cli.Store.StoreKitWithFds

open Arm64 ProofLib ProofLib.SepLogic SepProp
open CryptoGames.LibsignalSessionApi (SessionRecord)
open CryptoVerification (LibsignalHooks LibsignalPlacement lsmpl)
open CryptoVerification.LibsignalPublicApi.StoreKit
  (IdentitySelfStoreSpec IdentityStoreSpec KyberPreKeyStoreSpec PreKeyStoreSpec
   SessionStoreSpec SignedPreKeyStoreSpec withEnvPre withLsLogOff withLsRoCl)
open LibsignalBinary.Heap (AllocCostModel AllocEvent BudgetLimits RustCliAllocBudget)
open LibsignalBinary.Proofs.PublicApi.StoreKit.IdentitySelfStoreKitBudget
  (IdentitySelfStoreBudgetEnv kitKpPollSpec kitKpPollSpecE kitKpShimSpec
   kitRegIdPollSpec kitRegIdPollSpecE kitRegIdShimSpec)
open LibsignalBinary.Proofs.PublicApi.StoreKit.IdentityStoreKitBudget
  (IdentityStoreBudgetEnv kitSaveShimSpec kitTrustShimSpec)
open LibsignalBinary.Proofs.PublicApi.StoreKit.KyberPreKeyStoreKitBudget
  (KyberPreKeyStoreBudgetEnv kitKpkGetPollSpec kitKpkGetPollSpecE kitKpkGetShimSpec
   kitKpkMarkPollSpec kitKpkMarkPollSpecE kitKpkMarkShimSpec)
open LibsignalBinary.Proofs.PublicApi.StoreKit.PlacedBudget
  (IdentitySelfStoreKitPlacedOkI IdentitySelfStoreKitPlacedOkIFds
   IdentityStoreKitPlacedOkI IdentityStoreKitPlacedOkIFds
   KyberPreKeyStoreKitPlacedOk KyberPreKeyStoreKitPlacedOkFds
   PreKeyStoreKitPlacedOk PreKeyStoreKitPlacedOkFds
   SessionOnlyKitPlacedOkSE SessionOnlyKitPlacedOkSEFds
   SignedPreKeyStoreKitPlacedOk SignedPreKeyStoreKitPlacedOkFds
   kitKpPollPlacedSpecI kitLoadPollPlacedSpecS kitLoadPollPlacedSpecSE
   kitRegIdPollPlacedSpecI kitSavePollPlacedSpec kitSavePollPlacedSpecE kitSavePollPlacedSpecI
   kitStorePollPlacedSpec kitStorePollPlacedSpecE
   kitTrustPollPlacedSpec kitTrustPollPlacedSpecE kitTrustPollPlacedSpecI)
open LibsignalBinary.Proofs.PublicApi.StoreKit.PreKeyStoreKitBudget
  (PreKeyStoreBudgetEnv futDropBudgetSpec
   kitPreKeyGetPollSpec kitPreKeyGetPollSpecE kitPreKeyGetShimSpec
   kitPreKeyRemovePollSpec kitPreKeyRemovePollSpecE kitPreKeyRemoveShimSpec)
open LibsignalBinary.Proofs.PublicApi.StoreKit.SessionStoreKitBudget
  (SessionStoreBudgetEnv kitLoadShimSpec kitStoreShimSpec)
open LibsignalBinary.Proofs.PublicApi.StoreKit.SignedPreKeyStoreKitBudget
  (SignedPreKeyStoreBudgetEnv kitSpkGetPollSpec kitSpkGetPollSpecE kitSpkGetShimSpec)
open LibsignalBinary.Proofs.SignalSession.Cli.F3.HRead.ReadFileBudgetPlaced (FdsGe3Closed)
open LibsignalBinary.Proofs.SignalSession.Cli.Heap.AllocWithFds
  (withFds withFds_live withFds_pool_enforced withFds_repAlloc)

/-! ## 1. Wrapper-Monotonicity Combinators (`withLsRoCl`, `withLsLogOff`, `futDropBudgetSpec`) -/

private theorem subroutine_ok_withLsRoCl_mono {α : Type} {pl : Arm64.Obj.MultiPlacement}
    {prog : Program} {entry : BitVec 64} {spec₁ spec₂ : Spec α}
    (h : subroutine_ok prog entry (withLsRoCl pl spec₁))
    (hpre : ∀ x R s0, s0.mem ⊨ spec₂.pre x s0 ∗ R → s0.mem ⊨ spec₁.pre x s0 ∗ R)
    (hpost : ∀ x R s0 sf, sf.mem ⊨ spec₁.post x s0 sf ∗ R → sf.mem ⊨ spec₂.post x s0 sf ∗ R)
    (hpan : spec₁.onPanic = spec₂.onPanic := by rfl)
    (hexit : spec₁.onExit = spec₂.onExit := by rfl)
    (hoom : spec₁.onOom = spec₂.onOom := by rfl) :
    subroutine_ok prog entry (withLsRoCl pl spec₂) := by
  refine subroutine_ok_mono h (fun x R s0 hp => ?_) (fun x R s0 sf hq => ?_)
    (fun x R s0 sf hq => ?_) (fun x code R s0 sf hq => ?_) (fun x R s0 sf hq => ?_)
  · dsimp only [withLsRoCl] at hp ⊢
    rw [sepConj_assoc] at hp ⊢
    exact hpre x _ s0 hp
  · dsimp only [withLsRoCl] at hq ⊢
    rw [sepConj_assoc, satisfies_pure_sepConj] at hq ⊢
    exact ⟨hq.1, hpost x R s0 sf hq.2⟩
  · dsimp only [withLsRoCl] at hq ⊢; rwa [← hpan]
  · dsimp only [withLsRoCl] at hq ⊢; rwa [← hexit]
  · dsimp only [withLsRoCl] at hq ⊢; rwa [← hoom]

private theorem subroutine_ok_withLsRoCl_withLsLogOff_mono [LibsignalPlacement]
    {α : Type} {pl : Arm64.Obj.MultiPlacement}
    {prog : Program} {entry : BitVec 64} {spec₁ spec₂ : Spec α}
    (h : subroutine_ok prog entry (withLsRoCl pl (withLsLogOff spec₁)))
    (hpre : ∀ x R s0, s0.mem ⊨ spec₂.pre x s0 ∗ R → s0.mem ⊨ spec₁.pre x s0 ∗ R)
    (hpost : ∀ x R s0 sf, sf.mem ⊨ spec₁.post x s0 sf ∗ R → sf.mem ⊨ spec₂.post x s0 sf ∗ R)
    (hpan : spec₁.onPanic = spec₂.onPanic := by rfl)
    (hexit : spec₁.onExit = spec₂.onExit := by rfl)
    (hoom : spec₁.onOom = spec₂.onOom := by rfl) :
    subroutine_ok prog entry (withLsRoCl pl (withLsLogOff spec₂)) := by
  refine subroutine_ok_withLsRoCl_mono h (fun x R s0 hp => ?_) (fun x R s0 sf hq => ?_)
    (by dsimp only [withLsLogOff]; rw [hpan])
    (by dsimp only [withLsLogOff]; rw [hexit])
    (by dsimp only [withLsLogOff]; rw [hoom])
  · dsimp only [withLsLogOff] at hp ⊢
    rw [sepConj_assoc] at hp ⊢
    exact hpre x _ s0 hp
  · dsimp only [withLsLogOff] at hq ⊢
    rw [sepConj_assoc] at hq ⊢
    exact hpost x _ s0 sf hq

private theorem subroutine_ok_futDrop_rocl_false_of_true
    {pl : Arm64.Obj.MultiPlacement} {prog : Program} {entry : BitVec 64} {fdsOk : FsState → Prop}
    (h : subroutine_ok prog entry (withLsRoCl pl (futDropBudgetSpec fdsOk true))) :
    subroutine_ok prog entry (withLsRoCl pl (futDropBudgetSpec fdsOk false)) := by
  refine subroutine_ok_withLsRoCl_mono h (fun _ _ _ hp => hp) (fun _ _ s0 sf hq => ?_)
  dsimp only [futDropBudgetSpec] at hq ⊢
  rw [satisfies_pure_sepConj] at hq ⊢
  exact ⟨⟨hq.1.1, hq.1.2.1⟩, hq.2⟩

/-! ## 2. First-Order Separation-Logic Frame Helpers for Shims & Polls -/

private theorem shim_pre_inner {M : AllocCostModel} {A : RustCliAllocBudget M}
    {lim : BudgetLimits} (henf : lim.enforced = true) {fdsOk : FsState → Prop}
    (hfds : ∀ fs, fdsOk fs ↔ FdsGe3Closed fs)
    {P P' : Prop} {S R : SepProp} {st : M.σ} {s0 : State}
    (h : s0.mem ⊨ (⌜P⌝ ∗ (withFds A).pool lim st s0 ∗ S) ∗ R)
    (himp : P ∧ fdsOk s0.fs → P' := by
      simp (config := { failIfUnchanged := false }) only [and_assoc]; exact id) :
    s0.mem ⊨ (⌜P'⌝ ∗ A.pool lim st s0 ∗ S) ∗ R := by
  rw [withFds_pool_enforced A henf] at h
  have hEq1 :
      (⌜P⌝ ∗ (⌜FdsGe3Closed s0.fs⌝ ∗ A.pool lim st s0) ∗ S) ∗ R =
      ⌜P⌝ ∗ (⌜FdsGe3Closed s0.fs⌝ ∗ ((A.pool lim st s0 ∗ S) ∗ R)) := by
    sep_ac_rfl
  rw [hEq1, satisfies_pure_sepConj, satisfies_pure_sepConj] at h
  rcases h with ⟨hP, hClosed, hRest⟩
  have hEq2 :
      (⌜P'⌝ ∗ A.pool lim st s0 ∗ S) ∗ R =
      ⌜P'⌝ ∗ ((A.pool lim st s0 ∗ S) ∗ R) := by
    sep_ac_rfl
  rw [hEq2, satisfies_pure_sepConj]
  exact ⟨himp ⟨hP, (hfds s0.fs).mpr hClosed⟩, hRest⟩

private theorem shim_post_inner {M : AllocCostModel} {A : RustCliAllocBudget M}
    {lim : BudgetLimits} (henf : lim.enforced = true) {fdsOk : FsState → Prop}
    (hfds : ∀ fs, fdsOk fs ↔ FdsGe3Closed fs)
    {Q' Q : Prop} {L B S R : SepProp} {st : M.σ} {evs : List AllocEvent} {sf : State}
    (h : sf.mem ⊨ (⌜Q'⌝ ∗ L ∗ B ∗ A.pool lim (M.stepEvents evs st) sf ∗ S) ∗ R)
    (himp : Q' → Q ∧ fdsOk sf.fs := by
      simp (config := { failIfUnchanged := false }) only [and_assoc]; exact id) :
    sf.mem ⊨ (⌜Q⌝ ∗ L ∗ B ∗ (withFds A).pool lim (M.stepEvents evs st) sf ∗ S) ∗ R := by
  have hEq1 :
      (⌜Q'⌝ ∗ L ∗ B ∗ A.pool lim (M.stepEvents evs st) sf ∗ S) ∗ R =
      ⌜Q'⌝ ∗ ((L ∗ B ∗ A.pool lim (M.stepEvents evs st) sf ∗ S) ∗ R) := by
    sep_ac_rfl
  rw [hEq1, satisfies_pure_sepConj] at h
  rcases h with ⟨hQ', hRest⟩
  obtain ⟨hQ, hfdsF⟩ := himp hQ'
  rw [withFds_pool_enforced A henf]
  have hEq2 :
      (⌜Q⌝ ∗ L ∗ B ∗
        (⌜FdsGe3Closed sf.fs⌝ ∗ A.pool lim (M.stepEvents evs st) sf) ∗ S) ∗ R =
      ⌜Q⌝ ∗ (⌜FdsGe3Closed sf.fs⌝ ∗
        ((L ∗ B ∗ A.pool lim (M.stepEvents evs st) sf ∗ S) ∗ R)) := by
    sep_ac_rfl
  rw [hEq2, satisfies_pure_sepConj, satisfies_pure_sepConj]
  exact ⟨hQ, (hfds sf.fs).mp hfdsF, hRest⟩

private theorem poll_pre4_inner {M : AllocCostModel} {A : RustCliAllocBudget M}
    {lim : BudgetLimits} (henf : lim.enforced = true) {fdsOk : FsState → Prop}
    (hfds : ∀ fs, fdsOk fs ↔ FdsGe3Closed fs)
    {E : Prop} {P0 P1 P2 P3 S R : SepProp} {st : M.σ} {s0 : State}
    (h : s0.mem ⊨ (⌜E⌝ ∗ (P0 ∗ P1 ∗ P2 ∗ P3 ∗ (withFds A).pool lim st s0 ∗ S)) ∗ R) :
    s0.mem ⊨ (⌜E ∧ fdsOk s0.fs⌝ ∗ (P0 ∗ P1 ∗ P2 ∗ P3 ∗ A.pool lim st s0 ∗ S)) ∗ R := by
  rw [withFds_pool_enforced A henf] at h
  have hEq1 :
      (⌜E⌝ ∗ (P0 ∗ P1 ∗ P2 ∗ P3 ∗ (⌜FdsGe3Closed s0.fs⌝ ∗ A.pool lim st s0) ∗ S)) ∗ R =
      ⌜E⌝ ∗ (⌜FdsGe3Closed s0.fs⌝ ∗ ((P0 ∗ P1 ∗ P2 ∗ P3 ∗ A.pool lim st s0 ∗ S) ∗ R)) := by
    sep_ac_rfl
  rw [hEq1, satisfies_pure_sepConj, satisfies_pure_sepConj] at h
  rcases h with ⟨hE, hClosed, hRest⟩
  have hEq2 :
      (⌜E ∧ fdsOk s0.fs⌝ ∗ (P0 ∗ P1 ∗ P2 ∗ P3 ∗ A.pool lim st s0 ∗ S)) ∗ R =
      ⌜E ∧ fdsOk s0.fs⌝ ∗ ((P0 ∗ P1 ∗ P2 ∗ P3 ∗ A.pool lim st s0 ∗ S) ∗ R) := by
    sep_ac_rfl
  rw [hEq2, satisfies_pure_sepConj]
  exact ⟨⟨hE, (hfds s0.fs).mpr hClosed⟩, hRest⟩

private theorem poll_pre5_inner {M : AllocCostModel} {A : RustCliAllocBudget M}
    {lim : BudgetLimits} (henf : lim.enforced = true) {fdsOk : FsState → Prop}
    (hfds : ∀ fs, fdsOk fs ↔ FdsGe3Closed fs)
    {E : Prop} {P0 P1 P2 P3 P4 S R : SepProp} {st : M.σ} {s0 : State}
    (h : s0.mem ⊨ (⌜E⌝ ∗ (P0 ∗ P1 ∗ P2 ∗ P3 ∗ P4 ∗ (withFds A).pool lim st s0 ∗ S)) ∗ R) :
    s0.mem ⊨ (⌜E ∧ fdsOk s0.fs⌝ ∗ (P0 ∗ P1 ∗ P2 ∗ P3 ∗ P4 ∗ A.pool lim st s0 ∗ S)) ∗ R := by
  rw [withFds_pool_enforced A henf] at h
  have hEq1 :
      (⌜E⌝ ∗ (P0 ∗ P1 ∗ P2 ∗ P3 ∗ P4 ∗ (⌜FdsGe3Closed s0.fs⌝ ∗ A.pool lim st s0) ∗ S)) ∗ R =
      ⌜E⌝ ∗ (⌜FdsGe3Closed s0.fs⌝ ∗ ((P0 ∗ P1 ∗ P2 ∗ P3 ∗ P4 ∗ A.pool lim st s0 ∗ S) ∗ R)) := by
    sep_ac_rfl
  rw [hEq1, satisfies_pure_sepConj, satisfies_pure_sepConj] at h
  rcases h with ⟨hE, hClosed, hRest⟩
  have hEq2 :
      (⌜E ∧ fdsOk s0.fs⌝ ∗ (P0 ∗ P1 ∗ P2 ∗ P3 ∗ P4 ∗ A.pool lim st s0 ∗ S)) ∗ R =
      ⌜E ∧ fdsOk s0.fs⌝ ∗ ((P0 ∗ P1 ∗ P2 ∗ P3 ∗ P4 ∗ A.pool lim st s0 ∗ S) ∗ R) := by
    sep_ac_rfl
  rw [hEq2, satisfies_pure_sepConj]
  exact ⟨⟨hE, (hfds s0.fs).mpr hClosed⟩, hRest⟩

private theorem poll_pre6_inner {M : AllocCostModel} {A : RustCliAllocBudget M}
    {lim : BudgetLimits} (henf : lim.enforced = true) {fdsOk : FsState → Prop}
    (hfds : ∀ fs, fdsOk fs ↔ FdsGe3Closed fs)
    {E : Prop} {P0 P1 P2 P3 P4 P5 S R : SepProp} {st : M.σ} {s0 : State}
    (h : s0.mem ⊨ (⌜E⌝ ∗ (P0 ∗ P1 ∗ P2 ∗ P3 ∗ P4 ∗ P5 ∗ (withFds A).pool lim st s0 ∗ S)) ∗ R) :
    s0.mem ⊨ (⌜E ∧ fdsOk s0.fs⌝ ∗ (P0 ∗ P1 ∗ P2 ∗ P3 ∗ P4 ∗ P5 ∗ A.pool lim st s0 ∗ S)) ∗ R := by
  rw [withFds_pool_enforced A henf] at h
  have hEq1 :
      (⌜E⌝ ∗ (P0 ∗ P1 ∗ P2 ∗ P3 ∗ P4 ∗ P5 ∗
        (⌜FdsGe3Closed s0.fs⌝ ∗ A.pool lim st s0) ∗ S)) ∗ R =
      ⌜E⌝ ∗ (⌜FdsGe3Closed s0.fs⌝ ∗
        ((P0 ∗ P1 ∗ P2 ∗ P3 ∗ P4 ∗ P5 ∗ A.pool lim st s0 ∗ S) ∗ R)) := by
    sep_ac_rfl
  rw [hEq1, satisfies_pure_sepConj, satisfies_pure_sepConj] at h
  rcases h with ⟨hE, hClosed, hRest⟩
  have hEq2 :
      (⌜E ∧ fdsOk s0.fs⌝ ∗ (P0 ∗ P1 ∗ P2 ∗ P3 ∗ P4 ∗ P5 ∗ A.pool lim st s0 ∗ S)) ∗ R =
      ⌜E ∧ fdsOk s0.fs⌝ ∗ ((P0 ∗ P1 ∗ P2 ∗ P3 ∗ P4 ∗ P5 ∗ A.pool lim st s0 ∗ S) ∗ R) := by
    sep_ac_rfl
  rw [hEq2, satisfies_pure_sepConj]
  exact ⟨⟨hE, (hfds s0.fs).mpr hClosed⟩, hRest⟩

private theorem poll_post3_inner {M : AllocCostModel} {A : RustCliAllocBudget M}
    {lim : BudgetLimits} (henf : lim.enforced = true) {fdsOk : FsState → Prop}
    (hfds : ∀ fs, fdsOk fs ↔ FdsGe3Closed fs)
    {Q' Q : Prop} {Q1 Q2 Q3 S R : SepProp} {st : M.σ} {evs : List AllocEvent} {sf : State}
    (h : sf.mem ⊨
      (⌜Q'⌝ ∗ Q1 ∗ Q2 ∗ Q3 ∗ A.pool lim (M.stepEvents evs st) sf ∗ S) ∗ R)
    (himp : Q' → Q ∧ fdsOk sf.fs := by
      simp (config := { failIfUnchanged := false }) only [and_assoc]; exact id) :
    sf.mem ⊨
      (⌜Q⌝ ∗ Q1 ∗ Q2 ∗ Q3 ∗ (withFds A).pool lim (M.stepEvents evs st) sf ∗ S) ∗ R := by
  have hEq1 :
      (⌜Q'⌝ ∗ Q1 ∗ Q2 ∗ Q3 ∗ A.pool lim (M.stepEvents evs st) sf ∗ S) ∗ R =
      ⌜Q'⌝ ∗ ((Q1 ∗ Q2 ∗ Q3 ∗ A.pool lim (M.stepEvents evs st) sf ∗ S) ∗ R) := by
    sep_ac_rfl
  rw [hEq1, satisfies_pure_sepConj] at h
  rcases h with ⟨hQ', hRest⟩
  obtain ⟨hQ, hfdsF⟩ := himp hQ'
  rw [withFds_pool_enforced A henf]
  have hEq2 :
      (⌜Q⌝ ∗ Q1 ∗ Q2 ∗ Q3 ∗
        (⌜FdsGe3Closed sf.fs⌝ ∗ A.pool lim (M.stepEvents evs st) sf) ∗ S) ∗ R =
      ⌜Q⌝ ∗ (⌜FdsGe3Closed sf.fs⌝ ∗
        ((Q1 ∗ Q2 ∗ Q3 ∗ A.pool lim (M.stepEvents evs st) sf ∗ S) ∗ R)) := by
    sep_ac_rfl
  rw [hEq2, satisfies_pure_sepConj, satisfies_pure_sepConj]
  exact ⟨hQ, (hfds sf.fs).mp hfdsF, hRest⟩

private theorem poll_post4_inner {M : AllocCostModel} {A : RustCliAllocBudget M}
    {lim : BudgetLimits} (henf : lim.enforced = true) {fdsOk : FsState → Prop}
    (hfds : ∀ fs, fdsOk fs ↔ FdsGe3Closed fs)
    {Q' Q : Prop} {Q1 Q2 Q3 Q4 S R : SepProp} {st : M.σ} {evs : List AllocEvent} {sf : State}
    (h : sf.mem ⊨
      (⌜Q'⌝ ∗ Q1 ∗ Q2 ∗ Q3 ∗ Q4 ∗ A.pool lim (M.stepEvents evs st) sf ∗ S) ∗ R)
    (himp : Q' → Q ∧ fdsOk sf.fs := by
      simp (config := { failIfUnchanged := false }) only [and_assoc]; exact id) :
    sf.mem ⊨
      (⌜Q⌝ ∗ Q1 ∗ Q2 ∗ Q3 ∗ Q4 ∗ (withFds A).pool lim (M.stepEvents evs st) sf ∗ S) ∗ R := by
  have hEq1 :
      (⌜Q'⌝ ∗ Q1 ∗ Q2 ∗ Q3 ∗ Q4 ∗ A.pool lim (M.stepEvents evs st) sf ∗ S) ∗ R =
      ⌜Q'⌝ ∗
        ((Q1 ∗ Q2 ∗ Q3 ∗ Q4 ∗ A.pool lim (M.stepEvents evs st) sf ∗ S) ∗ R) := by
    sep_ac_rfl
  rw [hEq1, satisfies_pure_sepConj] at h
  rcases h with ⟨hQ', hRest⟩
  obtain ⟨hQ, hfdsF⟩ := himp hQ'
  rw [withFds_pool_enforced A henf]
  have hEq2 :
      (⌜Q⌝ ∗ Q1 ∗ Q2 ∗ Q3 ∗ Q4 ∗
        (⌜FdsGe3Closed sf.fs⌝ ∗ A.pool lim (M.stepEvents evs st) sf) ∗ S) ∗ R =
      ⌜Q⌝ ∗ (⌜FdsGe3Closed sf.fs⌝ ∗
        ((Q1 ∗ Q2 ∗ Q3 ∗ Q4 ∗ A.pool lim (M.stepEvents evs st) sf ∗ S) ∗ R)) := by
    sep_ac_rfl
  rw [hEq2, satisfies_pure_sepConj, satisfies_pure_sepConj]
  exact ⟨hQ, (hfds sf.fs).mp hfdsF, hRest⟩

private theorem poll_post5_inner {M : AllocCostModel} {A : RustCliAllocBudget M}
    {lim : BudgetLimits} (henf : lim.enforced = true) {fdsOk : FsState → Prop}
    (hfds : ∀ fs, fdsOk fs ↔ FdsGe3Closed fs)
    {Q' Q : Prop} {Q1 Q2 Q3 Q4 Q5 S R : SepProp} {st : M.σ} {evs : List AllocEvent} {sf : State}
    (h : sf.mem ⊨
      (⌜Q'⌝ ∗ Q1 ∗ Q2 ∗ Q3 ∗ Q4 ∗ Q5 ∗
        A.pool lim (M.stepEvents evs st) sf ∗ S) ∗ R)
    (himp : Q' → Q ∧ fdsOk sf.fs := by
      simp (config := { failIfUnchanged := false }) only [and_assoc]; exact id) :
    sf.mem ⊨
      (⌜Q⌝ ∗ Q1 ∗ Q2 ∗ Q3 ∗ Q4 ∗ Q5 ∗
        (withFds A).pool lim (M.stepEvents evs st) sf ∗ S) ∗ R := by
  have hEq1 :
      (⌜Q'⌝ ∗ Q1 ∗ Q2 ∗ Q3 ∗ Q4 ∗ Q5 ∗
        A.pool lim (M.stepEvents evs st) sf ∗ S) ∗ R =
      ⌜Q'⌝ ∗
        ((Q1 ∗ Q2 ∗ Q3 ∗ Q4 ∗ Q5 ∗ A.pool lim (M.stepEvents evs st) sf ∗ S) ∗ R) := by
    sep_ac_rfl
  rw [hEq1, satisfies_pure_sepConj] at h
  rcases h with ⟨hQ', hRest⟩
  obtain ⟨hQ, hfdsF⟩ := himp hQ'
  rw [withFds_pool_enforced A henf]
  have hEq2 :
      (⌜Q⌝ ∗ Q1 ∗ Q2 ∗ Q3 ∗ Q4 ∗ Q5 ∗
        (⌜FdsGe3Closed sf.fs⌝ ∗ A.pool lim (M.stepEvents evs st) sf) ∗ S) ∗ R =
      ⌜Q⌝ ∗ (⌜FdsGe3Closed sf.fs⌝ ∗
        ((Q1 ∗ Q2 ∗ Q3 ∗ Q4 ∗ Q5 ∗ A.pool lim (M.stepEvents evs st) sf ∗ S) ∗ R)) := by
    sep_ac_rfl
  rw [hEq2, satisfies_pure_sepConj, satisfies_pure_sepConj]
  exact ⟨hQ, (hfds sf.fs).mp hfdsF, hRest⟩

/-! ## 3. Bundle Bridges (`fds = true` at `A` → `fds = false` at `withFds A`) -/

/-- Lift `SessionOnlyKitPlacedOkSEFds A` (`fds = true`) to
    `SessionOnlyKitPlacedOkSE (withFds A) ... false` whenever `lim.enforced = true` and
    `kit.fdsOk ↔ FdsGe3Closed`. -/
theorem sessionOnlyKitPlacedOkSE_withFds_of_fds [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {kit : SessionStoreSpec A.repAlloc 0#64} {kitEnv : SessionStoreBudgetEnv kit}
    {Scope : SessionRecord (List (BitVec 8)) → Prop}
    {encRecord : SessionRecord (List (BitVec 8)) → List (BitVec 8)}
    {H : LibsignalHooks}
    (henf : lim.enforced = true)
    (h : SessionOnlyKitPlacedOkSEFds A lim kit kitEnv Scope encRecord H)
    (hfds : ∀ fs, kit.fdsOk fs ↔ FdsGe3Closed fs := by intro _; exact Iff.rfl) :
    SessionOnlyKitPlacedOkSE (withFds A) lim kit kitEnv Scope encRecord H false where
  loadShim hblk := by
    refine subroutine_ok_withLsRoCl_mono (h.loadShim hblk) (fun ⟨x, st⟩ R s0 hp => ?_)
      (fun ⟨x, st⟩ R s0 sf hq => ?_)
    · dsimp only [kitLoadShimSpec] at hp ⊢
      exact shim_pre_inner henf hfds hp
    · dsimp only [kitLoadShimSpec, withFds_live] at hq ⊢
      rw [sepExists_sepConj_left, satisfies_sepExists] at hq ⊢
      rcases hq with ⟨evs, hq⟩
      exact ⟨evs, shim_post_inner henf hfds hq⟩
  loadPoll hblk := by
    refine subroutine_ok_withLsRoCl_mono (h.loadPoll hblk)
      (fun ⟨x, self, st0, st⟩ R s0 hp => ?_) (fun ⟨x, self, st0, st⟩ R s0 sf hq => ?_)
    · dsimp only [kitLoadPollPlacedSpecSE, withEnvPre, kitLoadPollPlacedSpecS,
        withFds_repAlloc] at hp ⊢
      exact poll_pre5_inner henf hfds hp
    · dsimp only [kitLoadPollPlacedSpecSE, withEnvPre, kitLoadPollPlacedSpecS,
        withFds_repAlloc] at hq ⊢
      rw [sepExists_sepConj_left, satisfies_sepExists] at hq ⊢
      rcases hq with ⟨ans, hq⟩
      refine ⟨ans, ?_⟩
      rw [sepExists_sepConj_left, satisfies_sepExists] at hq ⊢
      rcases hq with ⟨evs, hq⟩
      exact ⟨evs, poll_post4_inner henf hfds hq⟩
  loadFutDrop hblk := subroutine_ok_futDrop_rocl_false_of_true (h.loadFutDrop hblk)
  storeShim hblk := by
    refine subroutine_ok_withLsRoCl_mono (h.storeShim hblk) (fun ⟨x, st⟩ R s0 hp => ?_)
      (fun ⟨x, st⟩ R s0 sf hq => ?_)
    · dsimp only [kitStoreShimSpec] at hp ⊢
      exact shim_pre_inner henf hfds hp
    · dsimp only [kitStoreShimSpec, withFds_live] at hq ⊢
      rw [sepExists_sepConj_left, satisfies_sepExists] at hq ⊢
      rcases hq with ⟨evs, hq⟩
      exact ⟨evs, shim_post_inner henf hfds hq⟩
  storePoll hblk := by
    refine subroutine_ok_withLsRoCl_mono (h.storePoll hblk)
      (fun ⟨x, self, st0, st⟩ R s0 hp => ?_) (fun ⟨x, self, st0, st⟩ R s0 sf hq => ?_)
    · dsimp only [kitStorePollPlacedSpecE, withEnvPre, kitStorePollPlacedSpec,
        withFds_repAlloc] at hp ⊢
      exact poll_pre6_inner henf hfds hp
    · dsimp only [kitStorePollPlacedSpecE, withEnvPre, kitStorePollPlacedSpec,
        withFds_repAlloc] at hq ⊢
      rw [sepExists_sepConj_left, satisfies_sepExists] at hq ⊢
      rcases hq with ⟨ans, hq⟩
      refine ⟨ans, ?_⟩
      rw [sepExists_sepConj_left, satisfies_sepExists] at hq ⊢
      rcases hq with ⟨evs, hq⟩
      exact ⟨evs, poll_post5_inner henf hfds hq⟩
  storeFutDrop hblk := subroutine_ok_futDrop_rocl_false_of_true (h.storeFutDrop hblk)

/-- Lift `IdentityStoreKitPlacedOkIFds A` (`fds = true`) to
    `IdentityStoreKitPlacedOkI (withFds A) ... false` whenever `lim.enforced = true` and
    `ikit.fdsOk ↔ FdsGe3Closed`. -/
theorem identityStoreKitPlacedOkI_withFds_of_fds [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {ikit : IdentityStoreSpec A.repAlloc 0#64} {ikitEnv : IdentityStoreBudgetEnv ikit}
    {H : LibsignalHooks}
    (henf : lim.enforced = true)
    (h : IdentityStoreKitPlacedOkIFds A lim ikit ikitEnv H)
    (hfds : ∀ fs, ikit.fdsOk fs ↔ FdsGe3Closed fs := by intro _; exact Iff.rfl) :
    IdentityStoreKitPlacedOkI (withFds A) lim ikit ikitEnv H false where
  trustShim hblk := by
    refine subroutine_ok_withLsRoCl_mono (h.trustShim hblk) (fun ⟨x, d, st⟩ R s0 hp => ?_)
      (fun ⟨x, d, st⟩ R s0 sf hq => ?_)
    · dsimp only [kitTrustShimSpec] at hp ⊢
      exact shim_pre_inner henf hfds hp
    · dsimp only [kitTrustShimSpec, withFds_live] at hq ⊢
      rw [sepExists_sepConj_left, satisfies_sepExists] at hq ⊢
      rcases hq with ⟨evs, hq⟩
      exact ⟨evs, shim_post_inner henf hfds hq⟩
  trustPoll hblk := by
    refine subroutine_ok_withLsRoCl_withLsLogOff_mono (h.trustPoll hblk)
      (fun ⟨x, d, self, ist0, st⟩ R s0 hp => ?_) (fun ⟨x, d, self, ist0, st⟩ R s0 sf hq => ?_)
    · dsimp only [kitTrustPollPlacedSpecE, withEnvPre, kitTrustPollPlacedSpec,
        withFds_repAlloc] at hp ⊢
      exact poll_pre6_inner henf hfds hp
    · dsimp only [kitTrustPollPlacedSpecE, withEnvPre, kitTrustPollPlacedSpec,
        withFds_repAlloc] at hq ⊢
      rw [sepExists_sepConj_left, satisfies_sepExists] at hq ⊢
      rcases hq with ⟨ans, hq⟩
      refine ⟨ans, ?_⟩
      rw [sepExists_sepConj_left, satisfies_sepExists] at hq ⊢
      rcases hq with ⟨evs, hq⟩
      exact ⟨evs, poll_post5_inner henf hfds hq⟩
  trustFutDrop hblk := subroutine_ok_futDrop_rocl_false_of_true (h.trustFutDrop hblk)
  saveShim hblk := by
    refine subroutine_ok_withLsRoCl_mono (h.saveShim hblk) (fun ⟨x, st⟩ R s0 hp => ?_)
      (fun ⟨x, st⟩ R s0 sf hq => ?_)
    · dsimp only [kitSaveShimSpec] at hp ⊢
      exact shim_pre_inner henf hfds hp
    · dsimp only [kitSaveShimSpec, withFds_live] at hq ⊢
      rw [sepExists_sepConj_left, satisfies_sepExists] at hq ⊢
      rcases hq with ⟨evs, hq⟩
      exact ⟨evs, shim_post_inner henf hfds hq⟩
  savePoll hblk := by
    refine subroutine_ok_withLsRoCl_withLsLogOff_mono (h.savePoll hblk)
      (fun ⟨x, self, ist0, st⟩ R s0 hp => ?_) (fun ⟨x, self, ist0, st⟩ R s0 sf hq => ?_)
    · dsimp only [kitSavePollPlacedSpecE, withEnvPre, kitSavePollPlacedSpec,
        withFds_repAlloc] at hp ⊢
      exact poll_pre6_inner henf hfds hp
    · dsimp only [kitSavePollPlacedSpecE, withEnvPre, kitSavePollPlacedSpec,
        withFds_repAlloc] at hq ⊢
      rw [sepExists_sepConj_left, satisfies_sepExists] at hq ⊢
      rcases hq with ⟨ans, hq⟩
      refine ⟨ans, ?_⟩
      rw [sepExists_sepConj_left, satisfies_sepExists] at hq ⊢
      rcases hq with ⟨evs, hq⟩
      exact ⟨evs, poll_post5_inner henf hfds hq⟩
  saveFutDrop hblk := subroutine_ok_futDrop_rocl_false_of_true (h.saveFutDrop hblk)

/-- Lift `PreKeyStoreKitPlacedOkFds A` (`fds = true`) to
    `PreKeyStoreKitPlacedOk (withFds A) ... false` whenever `lim.enforced = true` and
    `kit.fdsOk ↔ FdsGe3Closed`. -/
theorem preKeyStoreKitPlacedOk_withFds_of_fds [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {kit : PreKeyStoreSpec A.repAlloc 0#64} {kitEnv : PreKeyStoreBudgetEnv kit}
    {H : LibsignalHooks}
    (henf : lim.enforced = true)
    (h : PreKeyStoreKitPlacedOkFds A lim kit kitEnv H)
    (hfds : ∀ fs, kit.fdsOk fs ↔ FdsGe3Closed fs := by intro _; exact Iff.rfl) :
    PreKeyStoreKitPlacedOk (withFds A) lim kit kitEnv H false where
  getShim hblk := by
    refine subroutine_ok_withLsRoCl_mono (h.getShim hblk) (fun ⟨x, st⟩ R s0 hp => ?_)
      (fun ⟨x, st⟩ R s0 sf hq => ?_)
    · dsimp only [kitPreKeyGetShimSpec] at hp ⊢
      exact shim_pre_inner henf hfds hp
    · dsimp only [kitPreKeyGetShimSpec, withFds_live] at hq ⊢
      rw [sepExists_sepConj_left, satisfies_sepExists] at hq ⊢
      rcases hq with ⟨evs, hq⟩
      exact ⟨evs, shim_post_inner henf hfds hq⟩
  getPoll hblk := by
    refine subroutine_ok_withLsRoCl_mono (h.getPoll hblk)
      (fun ⟨x, st0, st⟩ R s0 hp => ?_) (fun ⟨x, st0, st⟩ R s0 sf hq => ?_)
    · dsimp only [kitPreKeyGetPollSpecE, withEnvPre, kitPreKeyGetPollSpec] at hp ⊢
      exact poll_pre4_inner henf hfds hp
    · dsimp only [kitPreKeyGetPollSpecE, withEnvPre, kitPreKeyGetPollSpec] at hq ⊢
      rw [sepExists_sepConj_left, satisfies_sepExists] at hq ⊢
      rcases hq with ⟨ans, hq⟩
      refine ⟨ans, ?_⟩
      rw [sepExists_sepConj_left, satisfies_sepExists] at hq ⊢
      rcases hq with ⟨evs, hq⟩
      exact ⟨evs, poll_post3_inner henf hfds hq⟩
  getFutDrop hblk := subroutine_ok_futDrop_rocl_false_of_true (h.getFutDrop hblk)
  removeShim hblk := by
    refine subroutine_ok_withLsRoCl_mono (h.removeShim hblk) (fun ⟨x, st⟩ R s0 hp => ?_)
      (fun ⟨x, st⟩ R s0 sf hq => ?_)
    · dsimp only [kitPreKeyRemoveShimSpec] at hp ⊢
      exact shim_pre_inner henf hfds hp
    · dsimp only [kitPreKeyRemoveShimSpec, withFds_live] at hq ⊢
      rw [sepExists_sepConj_left, satisfies_sepExists] at hq ⊢
      rcases hq with ⟨evs, hq⟩
      exact ⟨evs, shim_post_inner henf hfds hq⟩
  removePoll hblk := by
    refine subroutine_ok_withLsRoCl_mono (h.removePoll hblk)
      (fun ⟨x, st0, st⟩ R s0 hp => ?_) (fun ⟨x, st0, st⟩ R s0 sf hq => ?_)
    · dsimp only [kitPreKeyRemovePollSpecE, withEnvPre, kitPreKeyRemovePollSpec] at hp ⊢
      exact poll_pre4_inner henf hfds hp
    · dsimp only [kitPreKeyRemovePollSpecE, withEnvPre, kitPreKeyRemovePollSpec] at hq ⊢
      rw [sepExists_sepConj_left, satisfies_sepExists] at hq ⊢
      rcases hq with ⟨ans, hq⟩
      refine ⟨ans, ?_⟩
      rw [sepExists_sepConj_left, satisfies_sepExists] at hq ⊢
      rcases hq with ⟨evs, hq⟩
      exact ⟨evs, poll_post3_inner henf hfds hq⟩
  removeFutDrop hblk := subroutine_ok_futDrop_rocl_false_of_true (h.removeFutDrop hblk)

/-- Lift `SignedPreKeyStoreKitPlacedOkFds A` (`fds = true`) to
    `SignedPreKeyStoreKitPlacedOk (withFds A) ... false` whenever `lim.enforced = true` and
    `kit.fdsOk ↔ FdsGe3Closed`. -/
theorem signedPreKeyStoreKitPlacedOk_withFds_of_fds [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {kit : SignedPreKeyStoreSpec A.repAlloc 0#64} {kitEnv : SignedPreKeyStoreBudgetEnv kit}
    {H : LibsignalHooks}
    (henf : lim.enforced = true)
    (h : SignedPreKeyStoreKitPlacedOkFds A lim kit kitEnv H)
    (hfds : ∀ fs, kit.fdsOk fs ↔ FdsGe3Closed fs := by intro _; exact Iff.rfl) :
    SignedPreKeyStoreKitPlacedOk (withFds A) lim kit kitEnv H false where
  getShim hblk := by
    refine subroutine_ok_withLsRoCl_mono (h.getShim hblk) (fun ⟨x, st⟩ R s0 hp => ?_)
      (fun ⟨x, st⟩ R s0 sf hq => ?_)
    · dsimp only [kitSpkGetShimSpec] at hp ⊢
      exact shim_pre_inner henf hfds hp
    · dsimp only [kitSpkGetShimSpec, withFds_live] at hq ⊢
      rw [sepExists_sepConj_left, satisfies_sepExists] at hq ⊢
      rcases hq with ⟨evs, hq⟩
      exact ⟨evs, shim_post_inner henf hfds hq⟩
  getPoll hblk := by
    refine subroutine_ok_withLsRoCl_mono (h.getPoll hblk)
      (fun ⟨x, st0, st⟩ R s0 hp => ?_) (fun ⟨x, st0, st⟩ R s0 sf hq => ?_)
    · dsimp only [kitSpkGetPollSpecE, withEnvPre, kitSpkGetPollSpec] at hp ⊢
      exact poll_pre4_inner henf hfds hp
    · dsimp only [kitSpkGetPollSpecE, withEnvPre, kitSpkGetPollSpec] at hq ⊢
      rw [sepExists_sepConj_left, satisfies_sepExists] at hq ⊢
      rcases hq with ⟨ans, hq⟩
      refine ⟨ans, ?_⟩
      rw [sepExists_sepConj_left, satisfies_sepExists] at hq ⊢
      rcases hq with ⟨evs, hq⟩
      exact ⟨evs, poll_post3_inner henf hfds hq⟩
  getFutDrop hblk := subroutine_ok_futDrop_rocl_false_of_true (h.getFutDrop hblk)

/-- Lift `KyberPreKeyStoreKitPlacedOkFds A` (`fds = true`) to
    `KyberPreKeyStoreKitPlacedOk (withFds A) ... false` whenever `lim.enforced = true` and
    `kit.fdsOk ↔ FdsGe3Closed`. -/
theorem kyberPreKeyStoreKitPlacedOk_withFds_of_fds [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {kit : KyberPreKeyStoreSpec A.repAlloc 0#64} {kitEnv : KyberPreKeyStoreBudgetEnv kit}
    {H : LibsignalHooks}
    (henf : lim.enforced = true)
    (h : KyberPreKeyStoreKitPlacedOkFds A lim kit kitEnv H)
    (hfds : ∀ fs, kit.fdsOk fs ↔ FdsGe3Closed fs := by intro _; exact Iff.rfl) :
    KyberPreKeyStoreKitPlacedOk (withFds A) lim kit kitEnv H false where
  getShim hblk := by
    refine subroutine_ok_withLsRoCl_mono (h.getShim hblk) (fun ⟨x, st⟩ R s0 hp => ?_)
      (fun ⟨x, st⟩ R s0 sf hq => ?_)
    · dsimp only [kitKpkGetShimSpec] at hp ⊢
      exact shim_pre_inner henf hfds hp
    · dsimp only [kitKpkGetShimSpec, withFds_live] at hq ⊢
      rw [sepExists_sepConj_left, satisfies_sepExists] at hq ⊢
      rcases hq with ⟨evs, hq⟩
      exact ⟨evs, shim_post_inner henf hfds hq⟩
  getPoll hblk := by
    refine subroutine_ok_withLsRoCl_mono (h.getPoll hblk)
      (fun ⟨x, st0, st⟩ R s0 hp => ?_) (fun ⟨x, st0, st⟩ R s0 sf hq => ?_)
    · dsimp only [kitKpkGetPollSpecE, withEnvPre, kitKpkGetPollSpec] at hp ⊢
      exact poll_pre4_inner henf hfds hp
    · dsimp only [kitKpkGetPollSpecE, withEnvPre, kitKpkGetPollSpec] at hq ⊢
      rw [sepExists_sepConj_left, satisfies_sepExists] at hq ⊢
      rcases hq with ⟨ans, hq⟩
      refine ⟨ans, ?_⟩
      rw [sepExists_sepConj_left, satisfies_sepExists] at hq ⊢
      rcases hq with ⟨evs, hq⟩
      exact ⟨evs, poll_post3_inner henf hfds hq⟩
  getFutDrop hblk := subroutine_ok_futDrop_rocl_false_of_true (h.getFutDrop hblk)
  markShim hblk := by
    refine subroutine_ok_withLsRoCl_mono (h.markShim hblk) (fun ⟨x, st⟩ R s0 hp => ?_)
      (fun ⟨x, st⟩ R s0 sf hq => ?_)
    · dsimp only [kitKpkMarkShimSpec] at hp ⊢
      exact shim_pre_inner henf hfds hp
    · dsimp only [kitKpkMarkShimSpec, withFds_live] at hq ⊢
      rw [sepExists_sepConj_left, satisfies_sepExists] at hq ⊢
      rcases hq with ⟨evs, hq⟩
      exact ⟨evs, shim_post_inner henf hfds hq⟩
  markPoll hblk := by
    refine subroutine_ok_withLsRoCl_mono (h.markPoll hblk)
      (fun ⟨x, st0, st⟩ R s0 hp => ?_) (fun ⟨x, st0, st⟩ R s0 sf hq => ?_)
    · dsimp only [kitKpkMarkPollSpecE, withEnvPre, kitKpkMarkPollSpec] at hp ⊢
      exact poll_pre5_inner henf hfds hp
    · dsimp only [kitKpkMarkPollSpecE, withEnvPre, kitKpkMarkPollSpec] at hq ⊢
      rw [sepExists_sepConj_left, satisfies_sepExists] at hq ⊢
      rcases hq with ⟨ans, hq⟩
      refine ⟨ans, ?_⟩
      rw [sepExists_sepConj_left, satisfies_sepExists] at hq ⊢
      rcases hq with ⟨evs, hq⟩
      exact ⟨evs, poll_post4_inner henf hfds hq⟩
  markFutDrop hblk := subroutine_ok_futDrop_rocl_false_of_true (h.markFutDrop hblk)

/-- Lift `IdentitySelfStoreKitPlacedOkIFds A` (`fds = true`) to
    `IdentitySelfStoreKitPlacedOkI (withFds A) ... false` whenever `lim.enforced = true` and
    `skit.fdsOk ↔ FdsGe3Closed`. -/
theorem identitySelfStoreKitPlacedOkI_withFds_of_fds [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {ikit : IdentityStoreSpec A.repAlloc 0#64}
    {skit : IdentitySelfStoreSpec ikit} {senv : IdentitySelfStoreBudgetEnv skit}
    {H : LibsignalHooks}
    (henf : lim.enforced = true)
    (h : IdentitySelfStoreKitPlacedOkIFds A lim ikit skit senv H)
    (hfds : ∀ fs, skit.fdsOk fs ↔ FdsGe3Closed fs := by intro _; exact Iff.rfl) :
    IdentitySelfStoreKitPlacedOkI (withFds A) lim ikit skit senv H false where
  kpShim hblk := by
    refine subroutine_ok_withLsRoCl_mono (h.kpShim hblk) (fun ⟨self, st⟩ R s0 hp => ?_)
      (fun ⟨self, st⟩ R s0 sf hq => ?_)
    · dsimp only [kitKpShimSpec] at hp ⊢
      exact shim_pre_inner henf hfds hp
    · dsimp only [kitKpShimSpec, withFds_live] at hq ⊢
      rw [sepExists_sepConj_left, satisfies_sepExists] at hq ⊢
      rcases hq with ⟨evs, hq⟩
      exact ⟨evs, shim_post_inner henf hfds hq⟩
  kpPoll hblk := by
    refine subroutine_ok_withLsRoCl_withLsLogOff_mono (h.kpPoll hblk)
      (fun ⟨fut, out, self, ist0, st⟩ R s0 hp => ?_)
      (fun ⟨fut, out, self, ist0, st⟩ R s0 sf hq => ?_)
    · dsimp only [kitKpPollPlacedSpecI, kitKpPollSpecE, withEnvPre, kitKpPollSpec] at hp ⊢
      exact poll_pre4_inner henf hfds hp
    · dsimp only [kitKpPollPlacedSpecI, kitKpPollSpecE, withEnvPre, kitKpPollSpec] at hq ⊢
      rw [sepExists_sepConj_left, satisfies_sepExists] at hq ⊢
      rcases hq with ⟨ans, hq⟩
      refine ⟨ans, ?_⟩
      rw [sepExists_sepConj_left, satisfies_sepExists] at hq ⊢
      rcases hq with ⟨evs, hq⟩
      exact ⟨evs, poll_post3_inner henf hfds hq⟩
  kpFutDrop hblk := subroutine_ok_futDrop_rocl_false_of_true (h.kpFutDrop hblk)
  regIdShim hblk := by
    refine subroutine_ok_withLsRoCl_mono (h.regIdShim hblk) (fun ⟨self, st⟩ R s0 hp => ?_)
      (fun ⟨self, st⟩ R s0 sf hq => ?_)
    · dsimp only [kitRegIdShimSpec] at hp ⊢
      exact shim_pre_inner henf hfds hp
    · dsimp only [kitRegIdShimSpec, withFds_live] at hq ⊢
      rw [sepExists_sepConj_left, satisfies_sepExists] at hq ⊢
      rcases hq with ⟨evs, hq⟩
      exact ⟨evs, shim_post_inner henf hfds hq⟩
  regIdPoll hblk := by
    refine subroutine_ok_withLsRoCl_withLsLogOff_mono (h.regIdPoll hblk)
      (fun ⟨fut, out, self, ist0, st⟩ R s0 hp => ?_)
      (fun ⟨fut, out, self, ist0, st⟩ R s0 sf hq => ?_)
    · dsimp only [kitRegIdPollPlacedSpecI, kitRegIdPollSpecE, withEnvPre, kitRegIdPollSpec] at hp ⊢
      exact poll_pre4_inner henf hfds hp
    · dsimp only [kitRegIdPollPlacedSpecI, kitRegIdPollSpecE, withEnvPre, kitRegIdPollSpec] at hq ⊢
      rw [sepExists_sepConj_left, satisfies_sepExists] at hq ⊢
      rcases hq with ⟨ans, hq⟩
      refine ⟨ans, ?_⟩
      rw [sepExists_sepConj_left, satisfies_sepExists] at hq ⊢
      rcases hq with ⟨evs, hq⟩
      exact ⟨evs, poll_post3_inner henf hfds hq⟩
  regIdFutDrop hblk := subroutine_ok_futDrop_rocl_false_of_true (h.regIdFutDrop hblk)

end LibsignalBinary.Proofs.SignalSession.Cli.Store.StoreKitWithFds
