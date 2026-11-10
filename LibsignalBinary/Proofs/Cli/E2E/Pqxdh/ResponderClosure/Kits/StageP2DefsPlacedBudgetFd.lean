/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Kits.StageP2DefsPlacedBudget
public import LibsignalBinary.Proofs.PublicApi.StoreKit.PlacedBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.F3.HRead.ReadFileBudgetPlaced
public import LibsignalBinary.Proofs.SignalSession.Cli.Heap.AllocWithFds
import Arm64.Trusted.Spec.Hoare
import Arm64.Trusted.Spec.SepLogic
import LibsignalBinary.Proofs.Common.SharedHelpers
meta import LibsignalBinary.Proofs.Common.SharedHelpers -- shake: keep
import ProofLib.SepLogic.WPp

/-!
# Descriptor-Threaded Stage P2 Store-Kit `withFds` Lifts

Lifts `StageP2ClosureHooksPlaced` and the four Stage P2 `*PlacedOkFds` store-kit bundles to
`AllocWithFds.withFds A` under `lim.enforced = true` and `FdsGe3Closed`, along with pool-rewriting
and pure-extraction helpers.
-/

@[expose] public section

set_option autoImplicit false
set_option maxHeartbeats 400000

namespace LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Kits.StageP2DefsPlacedBudgetFd

open Arm64 ProofLib SepProp
open CryptoVerification (LibsignalHooks LibsignalPlacement lsmpl withLsCodeLoaded)
open CryptoVerification.LibsignalPublicApi.StoreKit (
  IdentitySelfStoreSpec IdentityStoreSpec KyberPreKeyStoreSpec PreKeyStoreSpec
  SignedPreKeyStoreSpec extract_withLsRoCl withEnvPre withLsLogOff withLsRoCl
)
open CryptoVerification.LibsignalTripleRatchet.FromRecordCallees (lsLogOff)
open LibsignalBinary.Heap (AllocCostModel BudgetLimits RustCliAllocBudget)
open LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Kits.StageP2DefsPlacedBudget (
  StageP2ClosureHooksPlaced
)
open LibsignalBinary.Proofs.PublicApi.StoreKit.IdentitySelfStoreKitBudget (
  IdentitySelfStoreBudgetEnv kitKpPollSpec kitKpPollSpecE kitKpShimSpec
  kitRegIdPollSpec kitRegIdPollSpecE kitRegIdShimSpec
)
open LibsignalBinary.Proofs.PublicApi.StoreKit.KyberPreKeyStoreKitBudget (
  KyberPreKeyStoreBudgetEnv kitKpkGetPollSpec kitKpkGetPollSpecE kitKpkGetShimSpec
  kitKpkMarkPollSpec kitKpkMarkPollSpecE kitKpkMarkShimSpec
)
open LibsignalBinary.Proofs.PublicApi.StoreKit.PlacedBudget (
  IdentitySelfStoreKitPlacedOkI IdentitySelfStoreKitPlacedOkIFds
  KyberPreKeyStoreKitPlacedOk KyberPreKeyStoreKitPlacedOkFds
  PreKeyStoreKitPlacedOk PreKeyStoreKitPlacedOkFds
  SignedPreKeyStoreKitPlacedOk SignedPreKeyStoreKitPlacedOkFds
  kitKpPollPlacedSpecI kitRegIdPollPlacedSpecI
)
open LibsignalBinary.Proofs.PublicApi.StoreKit.PreKeyStoreKitBudget (
  PreKeyStoreBudgetEnv futDropBudgetSpec kitPreKeyGetPollSpec kitPreKeyGetPollSpecE
  kitPreKeyGetShimSpec kitPreKeyRemovePollSpec kitPreKeyRemovePollSpecE kitPreKeyRemoveShimSpec
)
open LibsignalBinary.Proofs.PublicApi.StoreKit.SignedPreKeyStoreKitBudget (
  SignedPreKeyStoreBudgetEnv kitSpkGetPollSpec kitSpkGetPollSpecE kitSpkGetShimSpec
)
open LibsignalBinary.Proofs.SignalSession.Cli.F3.HRead.ReadFileBudgetPlaced (
  FdsGe3Closed
)
open LibsignalBinary.Proofs.SignalSession.Cli.Heap.AllocWithFds (
  subroutine_ok_allocBudget_withFds subroutine_ok_deallocBudget_withFds
  withFds withFds_live withFds_pool_enforced
)

/-! ## 1. Lifting `StageP2ClosureHooksPlaced` to `withFds A` -/

theorem stageP2ClosureHooks_toWithFds [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {ext : String → Option (State → State)}
    (h : StageP2ClosureHooksPlaced A lim ext) :
    StageP2ClosureHooksPlaced (withFds A) lim ext where
  shim := h.shim
  alloc := subroutine_ok_allocBudget_withFds h.alloc
  dealloc := subroutine_ok_deallocBudget_withFds h.dealloc
  memcpy4K := h.memcpy4K

/-! ## 2. Lifting `fds = true` Store-Kit Bundles to `withFds A` -/

private theorem subroutine_ok_withLsRoCl_mono [LibsignalPlacement] {α : Type}
    {prog : Program} {entry : BitVec 64} {spec₁ spec₂ : Spec α}
    (h : subroutine_ok prog entry (withLsRoCl lsmpl spec₁))
    (hpre : ∀ x R s, (s.mem ⊨ spec₂.pre x s ∗ R) → (s.mem ⊨ spec₁.pre x s ∗ R))
    (hpost : ∀ x R s0 sf, (sf.mem ⊨ spec₁.post x s0 sf ∗ R) → (sf.mem ⊨ spec₂.post x s0 sf ∗ R))
    (hexit : spec₁.onExit = spec₂.onExit := by rfl)
    (hpan : spec₁.onPanic = spec₂.onPanic := by rfl)
    (hoom : spec₁.onOom = spec₂.onOom := by rfl) :
    subroutine_ok prog entry (withLsRoCl lsmpl spec₂) := by
  refine subroutine_ok_mono h
    (fun x R s hp => ?_)
    (fun x R s0 sf hq => ?_)
    (fun x R s0 sf hq => hpan ▸ hq)
    (fun x code R s0 sf hq => hexit ▸ hq)
    (fun x R s0 sf hq => hoom ▸ hq)
  · obtain ⟨hcrl, hp'⟩ := extract_withLsRoCl hp
    dsimp only [withLsRoCl]
    rw [sepConj_assoc, sepConj_left_comm, satisfies_pure_sepConj]
    exact ⟨hcrl, hpre x R s hp'⟩
  · dsimp only [withLsRoCl] at hq ⊢
    rw [sepConj_assoc, satisfies_pure_sepConj] at hq ⊢
    exact ⟨hq.1, hpost x R s0 sf hq.2⟩

theorem subroutine_ok_withLsCodeLoaded_mono [LibsignalPlacement] {α : Type}
    {prog : Program} {entry : BitVec 64} {spec₁ spec₂ : Spec α}
    (h : subroutine_ok prog entry (withLsCodeLoaded lsmpl spec₁))
    (hpre : ∀ x R s, (s.mem ⊨ spec₂.pre x s ∗ R) → (s.mem ⊨ spec₁.pre x s ∗ R))
    (hpost : ∀ x R s0 sf, (sf.mem ⊨ spec₁.post x s0 sf ∗ R) → (sf.mem ⊨ spec₂.post x s0 sf ∗ R))
    (hexit : spec₁.onExit = spec₂.onExit := by rfl)
    (hpan : spec₁.onPanic = spec₂.onPanic := by rfl)
    (hoom : spec₁.onOom = spec₂.onOom := by rfl) :
    subroutine_ok prog entry (withLsCodeLoaded lsmpl spec₂) := by
  refine subroutine_ok_mono h
    (fun x R s hp => ?_)
    hpost
    (fun x R s0 sf hq => hpan ▸ hq)
    (fun x code R s0 sf hq => hexit ▸ hq)
    (fun x R s0 sf hq => hoom ▸ hq)
  dsimp only [withLsCodeLoaded] at hp ⊢
  rw [sepConj_assoc, sepConj_left_comm, satisfies_pure_sepConj] at hp ⊢
  exact ⟨hp.1, hpre x R s hp.2⟩

private theorem subroutine_ok_futDrop_false_of_true [LibsignalPlacement]
    {prog : Program} {entry : BitVec 64} {fdsOk : FsState → Prop}
    (h : subroutine_ok prog entry (withLsRoCl lsmpl (futDropBudgetSpec fdsOk true))) :
    subroutine_ok prog entry (withLsRoCl lsmpl (futDropBudgetSpec fdsOk false)) := by
  refine subroutine_ok_withLsRoCl_mono h (fun _ _ _ hp => hp) (fun _ _ _ _ hq => ?_)
  dsimp only [futDropBudgetSpec] at hq ⊢
  rw [satisfies_pure_sepConj] at hq ⊢
  exact ⟨⟨hq.1.1, hq.1.2.1⟩, hq.2⟩

private theorem satisfies_insert_pure {m : Memory} {φ : Prop} {P Q : SepProp}
    (hφ : φ) (hm : m ⊨ P) (hEq : ⌜φ⌝ ∗ P = Q) : m ⊨ Q := by
  rw [← hEq, satisfies_pure_sepConj]
  exact ⟨hφ, hm⟩

theorem spkKitFds_toWithFds [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} (henf : lim.enforced = true)
    {kit : SignedPreKeyStoreSpec A.repAlloc 0#64} {kitEnv : SignedPreKeyStoreBudgetEnv kit}
    {H : LibsignalHooks} (hkit : kit.fdsOk = FdsGe3Closed)
    (h : SignedPreKeyStoreKitPlacedOkFds A lim kit kitEnv H) :
    SignedPreKeyStoreKitPlacedOk (withFds A) lim kit kitEnv H false where
  getShim hblk := by
    refine subroutine_ok_withLsRoCl_mono (h.getShim hblk) (fun ⟨x, st⟩ R s hp => ?_)
      (fun ⟨x, st⟩ R s0 sf hq => ?_)
    · dsimp only [kitSpkGetShimSpec] at hp ⊢
      rw [withFds_pool_enforced A henf] at hp
      simp only [sepConj_assoc, satisfies_pure_sepConj] at hp ⊢
      rcases hp with ⟨⟨hb, hx0, hx1, hfits⟩, hfds, hmem⟩
      exact ⟨⟨hb, hx0, hx1, hfits, hkit ▸ hfds⟩, hmem⟩
    · dsimp only [kitSpkGetShimSpec, withFds_live] at hq ⊢
      rw [sepExists_sepConj_left, satisfies_sepExists] at hq ⊢
      rcases hq with ⟨evs, hq⟩
      refine ⟨evs, ?_⟩
      rw [withFds_pool_enforced A henf]
      simp only [sepConj_assoc, satisfies_pure_sepConj] at hq ⊢
      rcases hq with ⟨⟨hr1, hr0, hal, htr, hbox, hfds⟩, hmem⟩
      refine ⟨⟨hr1, hr0, hal, htr, hbox⟩, ?_⟩
      exact satisfies_insert_pure (hkit ▸ hfds) hmem (by sep_ac_rfl)
  getPoll hblk := by
    refine subroutine_ok_withLsRoCl_mono (h.getPoll hblk) (fun ⟨x, st0, st⟩ R s hp => ?_)
      (fun ⟨x, st0, st⟩ R s0 sf hq => ?_)
    · dsimp only [kitSpkGetPollSpecE, withEnvPre, kitSpkGetPollSpec] at hp ⊢
      rw [withFds_pool_enforced A henf] at hp
      simp only [sepConj_assoc, satisfies_pure_sepConj] at hp ⊢
      rcases hp with ⟨henv, hpure, hmem⟩
      have hmem' : s.mem ⊨ ⌜FdsGe3Closed s.fs⌝ ∗
          (kit.getBoxAt x.fut x.self x.id 0#8 ∗ kit.storeAt x.self st0 ∗ memRegion x.out 88 ∗
            A.pool lim st s ∗ stackAt s.sp kit.getPollStack ∗ R) :=
        Satisfies.of_eq hmem (by sep_ac_rfl)
      rw [satisfies_pure_sepConj] at hmem'
      exact ⟨⟨henv, hkit ▸ hmem'.1⟩, hpure, hmem'.2⟩
    · dsimp only [kitSpkGetPollSpecE, withEnvPre, kitSpkGetPollSpec] at hq ⊢
      rw [sepExists_sepConj_left, satisfies_sepExists] at hq ⊢
      rcases hq with ⟨ans, hq⟩
      refine ⟨ans, ?_⟩
      rw [sepExists_sepConj_left, satisfies_sepExists] at hq ⊢
      rcases hq with ⟨evs, hq⟩
      refine ⟨evs, ?_⟩
      rw [withFds_pool_enforced A henf]
      simp only [sepConj_assoc, satisfies_pure_sepConj] at hq ⊢
      rcases hq with ⟨⟨hrel, htr, henv, hfds⟩, hmem⟩
      refine ⟨⟨hrel, htr, henv⟩, ?_⟩
      exact satisfies_insert_pure (hkit ▸ hfds) hmem (by sep_ac_rfl)
  getFutDrop hblk := subroutine_ok_futDrop_false_of_true (h.getFutDrop hblk)

theorem pkKitFds_toWithFds [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} (henf : lim.enforced = true)
    {kit : PreKeyStoreSpec A.repAlloc 0#64} {kitEnv : PreKeyStoreBudgetEnv kit}
    {H : LibsignalHooks} (hkit : kit.fdsOk = FdsGe3Closed)
    (h : PreKeyStoreKitPlacedOkFds A lim kit kitEnv H) :
    PreKeyStoreKitPlacedOk (withFds A) lim kit kitEnv H false where
  getShim hblk := by
    refine subroutine_ok_withLsRoCl_mono (h.getShim hblk) (fun ⟨x, st⟩ R s hp => ?_)
      (fun ⟨x, st⟩ R s0 sf hq => ?_)
    · dsimp only [kitPreKeyGetShimSpec] at hp ⊢
      rw [withFds_pool_enforced A henf] at hp
      simp only [sepConj_assoc, satisfies_pure_sepConj] at hp ⊢
      rcases hp with ⟨⟨hb, hx0, hx1, hfits⟩, hfds, hmem⟩
      exact ⟨⟨hb, hx0, hx1, hfits, hkit ▸ hfds⟩, hmem⟩
    · dsimp only [kitPreKeyGetShimSpec, withFds_live] at hq ⊢
      rw [sepExists_sepConj_left, satisfies_sepExists] at hq ⊢
      rcases hq with ⟨evs, hq⟩
      refine ⟨evs, ?_⟩
      rw [withFds_pool_enforced A henf]
      simp only [sepConj_assoc, satisfies_pure_sepConj] at hq ⊢
      rcases hq with ⟨⟨hr1, hr0, hal, htr, hbox, hfds⟩, hmem⟩
      refine ⟨⟨hr1, hr0, hal, htr, hbox⟩, ?_⟩
      exact satisfies_insert_pure (hkit ▸ hfds) hmem (by sep_ac_rfl)
  getPoll hblk := by
    refine subroutine_ok_withLsRoCl_mono (h.getPoll hblk) (fun ⟨x, st0, st⟩ R s hp => ?_)
      (fun ⟨x, st0, st⟩ R s0 sf hq => ?_)
    · dsimp only [kitPreKeyGetPollSpecE, withEnvPre, kitPreKeyGetPollSpec] at hp ⊢
      rw [withFds_pool_enforced A henf] at hp
      simp only [sepConj_assoc, satisfies_pure_sepConj] at hp ⊢
      rcases hp with ⟨henv, hpure, hmem⟩
      have hmem' : s.mem ⊨ ⌜FdsGe3Closed s.fs⌝ ∗
          (kit.getBoxAt x.fut x.self x.id 0#8 ∗ kit.storeAt x.self st0 ∗ memRegion x.out 56 ∗
            A.pool lim st s ∗ stackAt s.sp kit.getPollStack ∗ R) :=
        Satisfies.of_eq hmem (by sep_ac_rfl)
      rw [satisfies_pure_sepConj] at hmem'
      exact ⟨⟨henv, hkit ▸ hmem'.1⟩, hpure, hmem'.2⟩
    · dsimp only [kitPreKeyGetPollSpecE, withEnvPre, kitPreKeyGetPollSpec] at hq ⊢
      rw [sepExists_sepConj_left, satisfies_sepExists] at hq ⊢
      rcases hq with ⟨ans, hq⟩
      refine ⟨ans, ?_⟩
      rw [sepExists_sepConj_left, satisfies_sepExists] at hq ⊢
      rcases hq with ⟨evs, hq⟩
      refine ⟨evs, ?_⟩
      rw [withFds_pool_enforced A henf]
      simp only [sepConj_assoc, satisfies_pure_sepConj] at hq ⊢
      rcases hq with ⟨⟨hrel, htr, henv, hfds⟩, hmem⟩
      refine ⟨⟨hrel, htr, henv⟩, ?_⟩
      exact satisfies_insert_pure (hkit ▸ hfds) hmem (by sep_ac_rfl)
  getFutDrop hblk := subroutine_ok_futDrop_false_of_true (h.getFutDrop hblk)
  removeShim hblk := by
    refine subroutine_ok_withLsRoCl_mono (h.removeShim hblk) (fun ⟨x, st⟩ R s hp => ?_)
      (fun ⟨x, st⟩ R s0 sf hq => ?_)
    · dsimp only [kitPreKeyRemoveShimSpec] at hp ⊢
      rw [withFds_pool_enforced A henf] at hp
      simp only [sepConj_assoc, satisfies_pure_sepConj] at hp ⊢
      rcases hp with ⟨⟨hb, hx0, hx1, hfits⟩, hfds, hmem⟩
      exact ⟨⟨hb, hx0, hx1, hfits, hkit ▸ hfds⟩, hmem⟩
    · dsimp only [kitPreKeyRemoveShimSpec, withFds_live] at hq ⊢
      rw [sepExists_sepConj_left, satisfies_sepExists] at hq ⊢
      rcases hq with ⟨evs, hq⟩
      refine ⟨evs, ?_⟩
      rw [withFds_pool_enforced A henf]
      simp only [sepConj_assoc, satisfies_pure_sepConj] at hq ⊢
      rcases hq with ⟨⟨hr1, hr0, hal, htr, hbox, hfds⟩, hmem⟩
      refine ⟨⟨hr1, hr0, hal, htr, hbox⟩, ?_⟩
      exact satisfies_insert_pure (hkit ▸ hfds) hmem (by sep_ac_rfl)
  removePoll hblk := by
    refine subroutine_ok_withLsRoCl_mono (h.removePoll hblk) (fun ⟨x, st0, st⟩ R s hp => ?_)
      (fun ⟨x, st0, st⟩ R s0 sf hq => ?_)
    · dsimp only [kitPreKeyRemovePollSpecE, withEnvPre, kitPreKeyRemovePollSpec] at hp ⊢
      rw [withFds_pool_enforced A henf] at hp
      simp only [sepConj_assoc, satisfies_pure_sepConj] at hp ⊢
      rcases hp with ⟨henv, hpure, hmem⟩
      have hmem' : s.mem ⊨ ⌜FdsGe3Closed s.fs⌝ ∗
          (kit.removeBoxAt x.fut x.self x.id 0#8 ∗ kit.storeAt x.self st0 ∗ memRegion x.out 48 ∗
            A.pool lim st s ∗ stackAt s.sp kit.removePollStack ∗ R) :=
        Satisfies.of_eq hmem (by sep_ac_rfl)
      rw [satisfies_pure_sepConj] at hmem'
      exact ⟨⟨henv, hkit ▸ hmem'.1⟩, hpure, hmem'.2⟩
    · dsimp only [kitPreKeyRemovePollSpecE, withEnvPre, kitPreKeyRemovePollSpec] at hq ⊢
      rw [sepExists_sepConj_left, satisfies_sepExists] at hq ⊢
      rcases hq with ⟨ans, hq⟩
      refine ⟨ans, ?_⟩
      rw [sepExists_sepConj_left, satisfies_sepExists] at hq ⊢
      rcases hq with ⟨evs, hq⟩
      refine ⟨evs, ?_⟩
      rw [withFds_pool_enforced A henf]
      simp only [sepConj_assoc, satisfies_pure_sepConj] at hq ⊢
      rcases hq with ⟨⟨hrel, htr, henv, hfds⟩, hmem⟩
      refine ⟨⟨hrel, htr, henv⟩, ?_⟩
      exact satisfies_insert_pure (hkit ▸ hfds) hmem (by sep_ac_rfl)
  removeFutDrop hblk := subroutine_ok_futDrop_false_of_true (h.removeFutDrop hblk)

theorem kpkKitFds_toWithFds [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} (henf : lim.enforced = true)
    {kit : KyberPreKeyStoreSpec A.repAlloc 0#64} {kitEnv : KyberPreKeyStoreBudgetEnv kit}
    {H : LibsignalHooks} (hkit : kit.fdsOk = FdsGe3Closed)
    (h : KyberPreKeyStoreKitPlacedOkFds A lim kit kitEnv H) :
    KyberPreKeyStoreKitPlacedOk (withFds A) lim kit kitEnv H false where
  getShim hblk := by
    refine subroutine_ok_withLsRoCl_mono (h.getShim hblk) (fun ⟨x, st⟩ R s hp => ?_)
      (fun ⟨x, st⟩ R s0 sf hq => ?_)
    · dsimp only [kitKpkGetShimSpec] at hp ⊢
      rw [withFds_pool_enforced A henf] at hp
      simp only [sepConj_assoc, satisfies_pure_sepConj] at hp ⊢
      rcases hp with ⟨⟨hb, hx0, hx1, hfits⟩, hfds, hmem⟩
      exact ⟨⟨hb, hx0, hx1, hfits, hkit ▸ hfds⟩, hmem⟩
    · dsimp only [kitKpkGetShimSpec, withFds_live] at hq ⊢
      rw [sepExists_sepConj_left, satisfies_sepExists] at hq ⊢
      rcases hq with ⟨evs, hq⟩
      refine ⟨evs, ?_⟩
      rw [withFds_pool_enforced A henf]
      simp only [sepConj_assoc, satisfies_pure_sepConj] at hq ⊢
      rcases hq with ⟨⟨hr1, hr0, hal, htr, hbox, hfds⟩, hmem⟩
      refine ⟨⟨hr1, hr0, hal, htr, hbox⟩, ?_⟩
      exact satisfies_insert_pure (hkit ▸ hfds) hmem (by sep_ac_rfl)
  getPoll hblk := by
    refine subroutine_ok_withLsRoCl_mono (h.getPoll hblk) (fun ⟨x, st0, st⟩ R s hp => ?_)
      (fun ⟨x, st0, st⟩ R s0 sf hq => ?_)
    · dsimp only [kitKpkGetPollSpecE, withEnvPre, kitKpkGetPollSpec] at hp ⊢
      rw [withFds_pool_enforced A henf] at hp
      simp only [sepConj_assoc, satisfies_pure_sepConj] at hp ⊢
      rcases hp with ⟨henv, hpure, hmem⟩
      have hmem' : s.mem ⊨ ⌜FdsGe3Closed s.fs⌝ ∗
          (kit.getBoxAt x.fut x.self x.id 0#8 ∗ kit.storeAt x.self st0 ∗ memRegion x.out 88 ∗
            A.pool lim st s ∗ stackAt s.sp kit.getPollStack ∗ R) :=
        Satisfies.of_eq hmem (by sep_ac_rfl)
      rw [satisfies_pure_sepConj] at hmem'
      exact ⟨⟨henv, hkit ▸ hmem'.1⟩, hpure, hmem'.2⟩
    · dsimp only [kitKpkGetPollSpecE, withEnvPre, kitKpkGetPollSpec] at hq ⊢
      rw [sepExists_sepConj_left, satisfies_sepExists] at hq ⊢
      rcases hq with ⟨ans, hq⟩
      refine ⟨ans, ?_⟩
      rw [sepExists_sepConj_left, satisfies_sepExists] at hq ⊢
      rcases hq with ⟨evs, hq⟩
      refine ⟨evs, ?_⟩
      rw [withFds_pool_enforced A henf]
      simp only [sepConj_assoc, satisfies_pure_sepConj] at hq ⊢
      rcases hq with ⟨⟨hrel, htr, henv, hfds⟩, hmem⟩
      refine ⟨⟨hrel, htr, henv⟩, ?_⟩
      exact satisfies_insert_pure (hkit ▸ hfds) hmem (by sep_ac_rfl)
  getFutDrop hblk := subroutine_ok_futDrop_false_of_true (h.getFutDrop hblk)
  markShim hblk := by
    refine subroutine_ok_withLsRoCl_mono (h.markShim hblk) (fun ⟨x, st⟩ R s hp => ?_)
      (fun ⟨x, st⟩ R s0 sf hq => ?_)
    · dsimp only [kitKpkMarkShimSpec] at hp ⊢
      rw [withFds_pool_enforced A henf] at hp
      simp only [sepConj_assoc, satisfies_pure_sepConj] at hp ⊢
      rcases hp with ⟨⟨hb, hx0, hx1, hx2, hx3, hfits⟩, hfds, hmem⟩
      exact ⟨⟨hb, hx0, hx1, hx2, hx3, hfits, hkit ▸ hfds⟩, hmem⟩
    · dsimp only [kitKpkMarkShimSpec, withFds_live] at hq ⊢
      rw [sepExists_sepConj_left, satisfies_sepExists] at hq ⊢
      rcases hq with ⟨evs, hq⟩
      refine ⟨evs, ?_⟩
      rw [withFds_pool_enforced A henf]
      simp only [sepConj_assoc, satisfies_pure_sepConj] at hq ⊢
      rcases hq with ⟨⟨hr1, hr0, hal, htr, hbox, hfds⟩, hmem⟩
      refine ⟨⟨hr1, hr0, hal, htr, hbox⟩, ?_⟩
      exact satisfies_insert_pure (hkit ▸ hfds) hmem (by sep_ac_rfl)
  markPoll hblk := by
    refine subroutine_ok_withLsRoCl_mono (h.markPoll hblk) (fun ⟨x, st0, st⟩ R s hp => ?_)
      (fun ⟨x, st0, st⟩ R s0 sf hq => ?_)
    · dsimp only [kitKpkMarkPollSpecE, withEnvPre, kitKpkMarkPollSpec] at hp ⊢
      rw [withFds_pool_enforced A henf] at hp
      simp only [sepConj_assoc, satisfies_pure_sepConj] at hp ⊢
      rcases hp with ⟨henv, hpure, hmem⟩
      have hmem' : s.mem ⊨ ⌜FdsGe3Closed s.fs⌝ ∗
          (kit.markBoxAt x.fut x.self x.baseKeyA x.id x.signedId 0#8 ∗
            kit.storeAt x.self st0 ∗ memRegion x.out 48 ∗
            (x.baseKeyA ↦ₛ x.baseKey.bytes.toList) ∗
            A.pool lim st s ∗ stackAt s.sp kit.markPollStack ∗ R) :=
        Satisfies.of_eq hmem (by sep_ac_rfl)
      rw [satisfies_pure_sepConj] at hmem'
      exact ⟨⟨henv, hkit ▸ hmem'.1⟩, hpure, hmem'.2⟩
    · dsimp only [kitKpkMarkPollSpecE, withEnvPre, kitKpkMarkPollSpec] at hq ⊢
      rw [sepExists_sepConj_left, satisfies_sepExists] at hq ⊢
      rcases hq with ⟨ans, hq⟩
      refine ⟨ans, ?_⟩
      rw [sepExists_sepConj_left, satisfies_sepExists] at hq ⊢
      rcases hq with ⟨evs, hq⟩
      refine ⟨evs, ?_⟩
      rw [withFds_pool_enforced A henf]
      simp only [sepConj_assoc, satisfies_pure_sepConj] at hq ⊢
      rcases hq with ⟨⟨hrel, htr, henv, hfds⟩, hmem⟩
      refine ⟨⟨hrel, htr, henv⟩, ?_⟩
      exact satisfies_insert_pure (hkit ▸ hfds) hmem (by sep_ac_rfl)
  markFutDrop hblk := subroutine_ok_futDrop_false_of_true (h.markFutDrop hblk)

theorem selfKitFds_toWithFds [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} (henf : lim.enforced = true)
    {ikit : IdentityStoreSpec A.repAlloc 0#64} {skit : IdentitySelfStoreSpec ikit}
    {skitEnv : IdentitySelfStoreBudgetEnv skit} {H : LibsignalHooks}
    (hkit : skit.fdsOk = FdsGe3Closed)
    (h : IdentitySelfStoreKitPlacedOkIFds A lim ikit skit skitEnv H) :
    IdentitySelfStoreKitPlacedOkI (withFds A) lim ikit skit skitEnv H false where
  kpShim hblk := by
    refine subroutine_ok_withLsRoCl_mono (h.kpShim hblk) (fun ⟨self, st⟩ R s hp => ?_)
      (fun ⟨self, st⟩ R s0 sf hq => ?_)
    · dsimp only [kitKpShimSpec] at hp ⊢
      rw [withFds_pool_enforced A henf] at hp
      simp only [sepConj_assoc, satisfies_pure_sepConj] at hp ⊢
      rcases hp with ⟨⟨hx0, hfits⟩, hfds, hmem⟩
      exact ⟨⟨hx0, hfits, hkit ▸ hfds⟩, hmem⟩
    · dsimp only [kitKpShimSpec, withFds_live] at hq ⊢
      rw [sepExists_sepConj_left, satisfies_sepExists] at hq ⊢
      rcases hq with ⟨evs, hq⟩
      refine ⟨evs, ?_⟩
      rw [withFds_pool_enforced A henf]
      simp only [sepConj_assoc, satisfies_pure_sepConj] at hq ⊢
      rcases hq with ⟨⟨hr1, hr0, hal, htr, hbox, hfds⟩, hmem⟩
      refine ⟨⟨hr1, hr0, hal, htr, hbox⟩, ?_⟩
      exact satisfies_insert_pure (hkit ▸ hfds) hmem (by sep_ac_rfl)
  kpPoll hblk := by
    refine subroutine_ok_withLsRoCl_mono (h.kpPoll hblk)
      (fun ⟨fut, out, self, ist0, st⟩ R s hp => ?_)
      (fun ⟨fut, out, self, ist0, st⟩ R s0 sf hq => ?_)
    · dsimp only [kitKpPollPlacedSpecI, withLsLogOff, kitKpPollSpecE, withEnvPre, kitKpPollSpec] at hp ⊢
      rw [withFds_pool_enforced A henf] at hp
      simp only [sepConj_assoc, satisfies_pure_sepConj] at hp ⊢
      rcases hp with ⟨henv, hpure, hmem⟩
      have hmem' : s.mem ⊨ ⌜FdsGe3Closed s.fs⌝ ∗
          (skit.kpBoxAt fut self 0#8 ∗ ikit.identityAt self ist0 ∗ memRegion out 72 ∗
            A.pool lim st s ∗ stackAt s.sp skit.kpPollStack ∗
            lsLogOff ∗ R) :=
        Satisfies.of_eq hmem (by sep_ac_rfl)
      rw [satisfies_pure_sepConj] at hmem'
      exact ⟨⟨henv, hkit ▸ hmem'.1⟩, hpure, hmem'.2⟩
    · dsimp only [kitKpPollPlacedSpecI, withLsLogOff, kitKpPollSpecE, withEnvPre, kitKpPollSpec] at hq ⊢
      simp only [sepConj_assoc, sepExists_sepConj_left, satisfies_sepExists] at hq ⊢
      rcases hq with ⟨ans, evs, hq⟩
      refine ⟨ans, evs, ?_⟩
      rw [withFds_pool_enforced A henf]
      simp only [sepConj_assoc, satisfies_pure_sepConj] at hq ⊢
      rcases hq with ⟨⟨hrel, htr, henv, hfds⟩, hmem⟩
      refine ⟨⟨hrel, htr, henv⟩, ?_⟩
      exact satisfies_insert_pure (hkit ▸ hfds) hmem (by sep_ac_rfl)
  kpFutDrop hblk := subroutine_ok_futDrop_false_of_true (h.kpFutDrop hblk)
  regIdShim hblk := by
    refine subroutine_ok_withLsRoCl_mono (h.regIdShim hblk) (fun ⟨self, st⟩ R s hp => ?_)
      (fun ⟨self, st⟩ R s0 sf hq => ?_)
    · dsimp only [kitRegIdShimSpec] at hp ⊢
      rw [withFds_pool_enforced A henf] at hp
      simp only [sepConj_assoc, satisfies_pure_sepConj] at hp ⊢
      rcases hp with ⟨⟨hx0, hfits⟩, hfds, hmem⟩
      exact ⟨⟨hx0, hfits, hkit ▸ hfds⟩, hmem⟩
    · dsimp only [kitRegIdShimSpec, withFds_live] at hq ⊢
      rw [sepExists_sepConj_left, satisfies_sepExists] at hq ⊢
      rcases hq with ⟨evs, hq⟩
      refine ⟨evs, ?_⟩
      rw [withFds_pool_enforced A henf]
      simp only [sepConj_assoc, satisfies_pure_sepConj] at hq ⊢
      rcases hq with ⟨⟨hr1, hr0, hal, htr, hbox, hfds⟩, hmem⟩
      refine ⟨⟨hr1, hr0, hal, htr, hbox⟩, ?_⟩
      exact satisfies_insert_pure (hkit ▸ hfds) hmem (by sep_ac_rfl)
  regIdPoll hblk := by
    refine subroutine_ok_withLsRoCl_mono (h.regIdPoll hblk)
      (fun ⟨fut, out, self, ist0, st⟩ R s hp => ?_)
      (fun ⟨fut, out, self, ist0, st⟩ R s0 sf hq => ?_)
    · dsimp only [kitRegIdPollPlacedSpecI, withLsLogOff, kitRegIdPollSpecE, withEnvPre,
        kitRegIdPollSpec] at hp ⊢
      rw [withFds_pool_enforced A henf] at hp
      simp only [sepConj_assoc, satisfies_pure_sepConj] at hp ⊢
      rcases hp with ⟨henv, hpure, hmem⟩
      have hmem' : s.mem ⊨ ⌜FdsGe3Closed s.fs⌝ ∗
          (skit.regIdBoxAt fut self 0#8 ∗ ikit.identityAt self ist0 ∗ memRegion out 48 ∗
            A.pool lim st s ∗ stackAt s.sp skit.regIdPollStack ∗
            lsLogOff ∗ R) :=
        Satisfies.of_eq hmem (by sep_ac_rfl)
      rw [satisfies_pure_sepConj] at hmem'
      exact ⟨⟨henv, hkit ▸ hmem'.1⟩, hpure, hmem'.2⟩
    · dsimp only [kitRegIdPollPlacedSpecI, withLsLogOff, kitRegIdPollSpecE, withEnvPre,
        kitRegIdPollSpec] at hq ⊢
      simp only [sepConj_assoc, sepExists_sepConj_left, satisfies_sepExists] at hq ⊢
      rcases hq with ⟨ans, evs, hq⟩
      refine ⟨ans, evs, ?_⟩
      rw [withFds_pool_enforced A henf]
      simp only [sepConj_assoc, satisfies_pure_sepConj] at hq ⊢
      rcases hq with ⟨⟨hrel, htr, henv, hfds⟩, hmem⟩
      refine ⟨⟨hrel, htr, henv⟩, ?_⟩
      exact satisfies_insert_pure (hkit ▸ hfds) hmem (by sep_ac_rfl)
  regIdFutDrop hblk := subroutine_ok_futDrop_false_of_true (h.regIdFutDrop hblk)

/-! ## 3. Pool Rewriting & `SepWPp` Pure-Extraction Helpers -/

theorem withFds_pool_eq_of_fdsGe3Closed {M : AllocCostModel} (A : RustCliAllocBudget M)
    {lim : BudgetLimits} (henf : lim.enforced = true)
    (st : M.σ) {s : State} (hfds : FdsGe3Closed s.fs) :
    (withFds A).pool lim st s = A.pool lim st s := by
  rw [withFds_pool_enforced A henf, pure_sepConj_of_true hfds]

theorem withFds_pool_eq_pure_false_of_not_fdsGe3Closed {M : AllocCostModel}
    (A : RustCliAllocBudget M) {lim : BudgetLimits} (henf : lim.enforced = true)
    (st : M.σ) {s : State} (hnot : ¬ FdsGe3Closed s.fs) :
    (withFds A).pool lim st s = ⌜False⌝ := by
  have hp : FdsGe3Closed s.fs = False := eq_false hnot
  rw [withFds_pool_enforced A henf, hp, pure_false_sepConj]

theorem entails_of_pure_false {Q : SepProp} : (⌜False⌝ : SepProp) ⊢ Q := by
  rw [← pure_false_sepConj Q]
  exact Entails.pure_left False.elim

theorem sepWPp_pure_false {prog : Program} {ret : BitVec 64} {s : State}
    {post Qp : State → SepProp → Prop} {oom : State → SepProp} :
    SepWPp prog ret s ⌜False⌝ post Qp oom :=
  SepWPp.congr_pre (pure_false_sepConj ⌜True⌝).symm (SepWPp.pure_left False.elim)

theorem withFds_pool_drop {M : AllocCostModel} (A : RustCliAllocBudget M)
    {lim : BudgetLimits} (henf : lim.enforced = true)
    (st : M.σ) (s : State) :
    (withFds A).pool lim st s ⊢ A.pool lim st s := by
  rw [withFds_pool_enforced A henf]
  exact Entails.pure_left fun _ => Entails.refl _

theorem entails_drop_pure_sep {φ : Prop} {P Q : SepProp}
    (hEq : P = ⌜φ⌝ ∗ Q) : P ⊢ Q := by
  rw [hEq]
  exact Entails.pure_left fun _ => Entails.refl _

theorem sepWPp_extract_pure_sep {prog : Program} {ret : BitVec 64} {s : State}
    {φ : Prop} {P Q : SepProp} {post Qp : State → SepProp → Prop} {oom : State → SepProp}
    (hEq : P = ⌜φ⌝ ∗ Q)
    (h : φ → SepWPp prog ret s Q post Qp oom) :
    SepWPp prog ret s P post Qp oom :=
  SepWPp.congr_pre hEq (SepWPp.pure_left h)

end LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Kits.StageP2DefsPlacedBudgetFd
