/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.Cli.TripleRatchet.Decrypt.DefsPlacedBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.F3.HRead.FdThreadKit
public import LibsignalBinary.Proofs.SignalSession.Cli.Heap.AllocWithFds
import Arm64.Trusted.Spec.Hoare
import Arm64.Trusted.Spec.SepLogic
import LibsignalBinary.Proofs.Common.SharedHelpers
meta import LibsignalBinary.Proofs.Common.SharedHelpers -- shake: keep

/-!
# `FdsGe3Closed` Conversion Seams for CLI `try_decrypt_with_state`

Lifts `subroutine_ok` contracts for relocatable budget-threaded `try_decrypt_with_state` specs
from `withFds A` (`lim.enforced = true`) to `withFdsGe3Closed`.
-/

@[expose] public section

set_option autoImplicit false

namespace LibsignalBinary.Proofs.Cli.TripleRatchet.Decrypt.DefsPlacedBudgetFd

open Arm64 Arm64.Obj ProofLib SepProp
open CryptoGames.LibsignalSession (Crypto)
open CryptoVerification (LibsignalPlacement lsmpl)
open CryptoVerification.Cli.CoinsTape (cliTapeAfter)
open CryptoVerification.LibsignalTripleRatchet (
  SpqrModel TryDecryptGhost rootStack withLsCodeRoLoaded
)
open CryptoVerification.LibsignalTripleRatchetRepr (
  SessionGhost UuidParser decryptDraws protocolAddressAt sessionStateAt
  signalMessageAt vecResultAt
)
open LibsignalBinary.Heap (
  AllocCostModel AllocEvent BudgetLimits RustCliAllocBudget
)
open LibsignalBinary.Proofs.Cli.E2E.Pqxdh.DecryptPq.TightPTrapPlacedBudget (
  tryDecryptPlacedSpecP tryDecryptPlacedSpecQF_PTight tryDecryptPlacedTightSpec
)
open LibsignalBinary.Proofs.Cli.TripleRatchet.Decrypt.DefsPlacedBudget (
  cliTryDecryptSpecPPlaced cliTryDecryptSpecPlaced cliTryDecryptTightSpecPlaced
  tryDecryptRawSpecTPTightAt tryDecryptSpecTPTightAt
)
open LibsignalBinary.Proofs.SignalSession.Cli.F3.HRead.ReadFileBudgetPlaced (
  FdsGe3Closed withFdsGe3Closed
)
open LibsignalBinary.Proofs.SignalSession.Cli.Heap.AllocWithFds (
  withFds withFds_pool_enforced withFds_repAlloc
)
open LibsignalBinary.Proofs.TripleRatchet.Record.DefsBudget (
  TryDecryptEnvArgs tryDecryptEnvArgs
)

private theorem subroutine_ok_of_pre_post {α : Type} {P : Program} {entry : BitVec 64}
    {spec1 spec2 : Spec α}
    (hok : subroutine_ok P entry spec1)
    (hpan : spec2.onPanic = spec1.onPanic)
    (hexc : spec2.onExit = spec1.onExit)
    (hoom : spec2.onOom = spec1.onOom)
    (hpre : ∀ x R s0, (s0.mem ⊨ spec2.pre x s0 ∗ R) → (s0.mem ⊨ spec1.pre x s0 ∗ R))
    (hpost : ∀ x R s0 sf, (sf.mem ⊨ spec1.post x s0 sf ∗ R) →
      (sf.mem ⊨ spec2.post x s0 sf ∗ R)) :
    subroutine_ok P entry spec2 := by
  refine subroutine_ok_outcome_intro fun x R s0 hpc hrun hpre2 hsp => ?_
  refine hok.mono_outcome x R s0 hpc hrun (hpre x R s0 hpre2) hsp ?_
  rintro sf (⟨hret, hcc, hp1⟩ | ⟨hp, hpan1⟩ | ⟨c, hc, hexc1⟩ | ⟨ho, hoom1⟩)
  · exact Or.inl ⟨hret, hcc, hpost x R s0 sf hp1⟩
  · exact Or.inr (Or.inl ⟨hp, hpan ▸ hpan1⟩)
  · exact Or.inr (Or.inr (Or.inl ⟨c, hc, hexc ▸ hexc1⟩))
  · exact Or.inr (Or.inr (Or.inr ⟨ho, hoom ▸ hoom1⟩))

private structure SpecImp {α : Type} (spec1 spec2 : Spec α) : Prop where
  onPanic_eq : spec2.onPanic = spec1.onPanic
  onExit_eq : spec2.onExit = spec1.onExit
  onOom_eq : spec2.onOom = spec1.onOom
  pre_eq : ∀ x s0, spec2.pre x s0 = spec1.pre x s0
  post_imp : ∀ x R s0 sf,
    (sf.mem ⊨ spec1.post x s0 sf ∗ R) → (sf.mem ⊨ spec2.post x s0 sf ∗ R)

private theorem SpecImp.to_subroutine_ok {α : Type} {P : Program} {entry : BitVec 64}
    {spec1 spec2 : Spec α} (h : SpecImp spec1 spec2)
    (hok : subroutine_ok P entry spec1) :
    subroutine_ok P entry spec2 :=
  subroutine_ok_of_pre_post hok h.onPanic_eq h.onExit_eq h.onOom_eq
    (fun x _ s0 hp => by rwa [← h.pre_eq x s0]) h.post_imp

private theorem SpecImp.withLsCodeRoLoaded {α : Type} (pl : MultiPlacement)
    {spec1 spec2 : Spec α} (h : SpecImp spec1 spec2) :
    SpecImp (CryptoVerification.LibsignalTripleRatchet.withLsCodeRoLoaded pl spec1)
      (CryptoVerification.LibsignalTripleRatchet.withLsCodeRoLoaded pl spec2) where
  onPanic_eq := h.onPanic_eq
  onExit_eq := h.onExit_eq
  onOom_eq := h.onOom_eq
  pre_eq := fun x s0 => by
    dsimp only [CryptoVerification.LibsignalTripleRatchet.withLsCodeRoLoaded]
    rw [h.pre_eq x s0]
  post_imp := h.post_imp

private theorem SpecImp.withStoreKitCodeRoLoaded {α : Type} (pl : MultiPlacement)
    {spec1 spec2 : Spec α} (h : SpecImp spec1 spec2) :
    SpecImp (CryptoVerification.LibsignalPublicApi.StoreKit.withLsCodeRoLoaded pl spec1)
      (CryptoVerification.LibsignalPublicApi.StoreKit.withLsCodeRoLoaded pl spec2) where
  onPanic_eq := h.onPanic_eq
  onExit_eq := h.onExit_eq
  onOom_eq := h.onOom_eq
  pre_eq := fun x s0 => by
    dsimp only [CryptoVerification.LibsignalPublicApi.StoreKit.withLsCodeRoLoaded]
    rw [h.pre_eq x s0]
  post_imp := h.post_imp

theorem subroutine_ok_withFdsGe3Closed_withLsCodeRoLoaded_of_inner {α : Type}
    {P : Program} {entry : BitVec 64} {pl : MultiPlacement} {spec : Spec α}
    (hok : subroutine_ok P entry (withLsCodeRoLoaded pl (withFdsGe3Closed spec))) :
    subroutine_ok P entry (withFdsGe3Closed (withLsCodeRoLoaded pl spec)) := by
  refine subroutine_ok_of_pre_post hok rfl rfl rfl (fun _ _ s0 hpre => ?_) (fun _ _ _ _ hpost => hpost)
  dsimp only [withLsCodeRoLoaded, withFdsGe3Closed] at hpre ⊢
  exact Eq.mp (congrArg (s0.mem ⊨ ·) (by sep_ac_rfl)) hpre

theorem subroutine_ok_withLsCodeRoLoaded_withFdsGe3Closed_of_outer {α : Type}
    {P : Program} {entry : BitVec 64} {pl : MultiPlacement} {spec : Spec α}
    (hok : subroutine_ok P entry (withFdsGe3Closed (withLsCodeRoLoaded pl spec))) :
    subroutine_ok P entry (withLsCodeRoLoaded pl (withFdsGe3Closed spec)) := by
  refine subroutine_ok_of_pre_post hok rfl rfl rfl (fun _ _ s0 hpre => ?_) (fun _ _ _ _ hpost => hpost)
  dsimp only [withLsCodeRoLoaded, withFdsGe3Closed] at hpre ⊢
  exact Eq.mp (congrArg (s0.mem ⊨ ·) (by sep_ac_rfl)) hpre

/-! ## Core `SpecImp` Conversions -/

private theorem sessionStateAt_budgetAtState {M : AllocCostModel}
    (B : RustCliAllocBudget M) (lim : BudgetLimits) (st : M.σ) (s : State) :
    sessionStateAt (B.atState lim st s) = sessionStateAt B.repAlloc :=
  rfl

private theorem protocolAddressAt_budgetAtState {M : AllocCostModel}
    (B : RustCliAllocBudget M) (lim : BudgetLimits) (st : M.σ) (s : State) :
    protocolAddressAt (B.atState lim st s) = protocolAddressAt B.repAlloc :=
  rfl

private theorem signalMessageAt_budgetAtState {M : AllocCostModel}
    (B : RustCliAllocBudget M) (lim : BudgetLimits) (st : M.σ) (s : State) :
    signalMessageAt (B.atState lim st s) = signalMessageAt B.repAlloc :=
  rfl

private theorem decResultAt_budgetAtState {M : AllocCostModel}
    (B : RustCliAllocBudget M) (lim : BudgetLimits) (st : M.σ) (s : State) :
    vecResultAt (B.atState lim st s) = vecResultAt B.repAlloc :=
  rfl

private theorem specImp_recordTryDecryptPlacedSpec [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    (C : Crypto) (ctl : BitVec 64) (parse : UuidParser) (S : SpqrModel)
    (tdEnv : TryDecryptEnvArgs → List AllocEvent → Prop)
    (henf : lim.enforced = true) :
    SpecImp
      (LibsignalBinary.Proofs.Cli.TripleRatchet.Record.DefsPlacedBudget.tryDecryptPlacedSpec
        C (withFds A) lim ctl parse S tdEnv)
      (withFdsGe3Closed
        (LibsignalBinary.Proofs.Cli.TripleRatchet.Record.DefsPlacedBudget.tryDecryptPlacedSpec
          C A lim ctl parse S tdEnv)) where
  onPanic_eq := rfl
  onExit_eq := rfl
  onOom_eq := rfl
  pre_eq := by
    rintro ⟨x, st⟩ s0
    dsimp only [withFdsGe3Closed,
      LibsignalBinary.Proofs.Cli.TripleRatchet.Record.DefsPlacedBudget.tryDecryptPlacedSpec,
      CryptoVerification.Cli.LibsignalTripleRatchet.Record.tryDecryptPlacedSpec,
      RustCliAllocBudget.atState_pool,
      sessionStateAt_budgetAtState,
      protocolAddressAt_budgetAtState,
      signalMessageAt_budgetAtState,
      withFds_repAlloc]
    rw [withFds_pool_enforced A henf]
    sep_ac_rfl
  post_imp := by
    rintro ⟨x, st⟩ R s0 sf hpost
    dsimp only [withFdsGe3Closed,
      LibsignalBinary.Proofs.Cli.TripleRatchet.Record.DefsPlacedBudget.tryDecryptPlacedSpec,
      CryptoVerification.Cli.LibsignalTripleRatchet.Record.tryDecryptPlacedSpec,
      RustCliAllocBudget.atState_pool,
      sessionStateAt_budgetAtState,
      protocolAddressAt_budgetAtState,
      signalMessageAt_budgetAtState,
      decResultAt_budgetAtState,
      withFds_repAlloc] at hpost ⊢
    rw [sepExists_sepConj_left, satisfies_sepExists] at hpost
    rcases hpost with ⟨evs, hevs⟩
    rw [withFds_pool_enforced A henf] at hevs
    let Body : SepProp :=
      ⌜tdEnv (tryDecryptEnvArgs x) evs⌝ ∗
      ⌜(x.model C S parse).1 ≠ .error .panic ∧ sf.trace = s0.trace⌝ ∗
      (∃∗ G' : SessionGhost,
        ⌜x.G.AfterTryDecrypt (x.model C S parse).1.toBool G'⌝ ∗
        sessionStateAt A.repAlloc x.ss G' (x.model C S parse).2) ∗
      vecResultAt A.repAlloc x.ret (x.model C S parse).1 ∗
      protocolAddressAt A.repAlloc x.rem x.remA ∗
      protocolAddressAt A.repAlloc x.loc x.locA ∗
      signalMessageAt A.repAlloc x.msgG x.msgA x.msg ∗
      cliTapeAfter ctl x.cur x.rest (decryptDraws C x.st x.msg.senderRatchetKey x.rest) ∗
      CryptoVerification.LibsignalTripleRatchet.FromRecordCallees.lsLogOff ∗
      stackAt s0.sp rootStack
    have hevs' : sf.mem ⊨ ⌜FdsGe3Closed sf.fs⌝ ∗ ((Body ∗ A.pool lim (M.stepEvents evs st) sf) ∗ R) :=
      Eq.mp (congrArg (sf.mem ⊨ ·) (by dsimp only [Body]; sep_ac_rfl)) hevs
    obtain ⟨hClosedF, hbody⟩ := (satisfies_pure_sepConj _ _ _).mp hevs'
    rw [sepConj_assoc, satisfies_pure_sepConj]
    refine ⟨hClosedF, ?_⟩
    rw [sepExists_sepConj_left, satisfies_sepExists]
    exact ⟨evs, Eq.mp (congrArg (sf.mem ⊨ ·) (by dsimp only [Body]; sep_ac_rfl)) hbody⟩

private theorem specImp_tryDecryptPlacedTightSpec [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    (C : Crypto) (ctl : BitVec 64) (parse : UuidParser) (S : SpqrModel)
    (tdEnv : TryDecryptEnvArgs → List AllocEvent → Prop)
    (henf : lim.enforced = true) :
    SpecImp
      (tryDecryptPlacedTightSpec C (withFds A) lim ctl parse S tdEnv)
      (withFdsGe3Closed (tryDecryptPlacedTightSpec C A lim ctl parse S tdEnv)) where
  onPanic_eq := rfl
  onExit_eq := rfl
  onOom_eq := rfl
  pre_eq := (specImp_recordTryDecryptPlacedSpec C ctl parse S tdEnv henf).pre_eq
  post_imp := (specImp_recordTryDecryptPlacedSpec C ctl parse S tdEnv henf).post_imp

private theorem specImp_tryDecryptPlacedSpecP [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    (C : Crypto) (ctl : BitVec 64) (parse : UuidParser) (S : SpqrModel)
    (tdEnv : TryDecryptEnvArgs → List AllocEvent → Prop)
    (henf : lim.enforced = true) :
    SpecImp
      (tryDecryptPlacedSpecP C (withFds A) lim ctl parse S tdEnv)
      (withFdsGe3Closed (tryDecryptPlacedSpecP C A lim ctl parse S tdEnv)) where
  onPanic_eq := rfl
  onExit_eq := rfl
  onOom_eq := rfl
  pre_eq := by
    rintro ⟨x, st⟩ s0
    dsimp only [withFdsGe3Closed, tryDecryptPlacedSpecP,
      CryptoVerification.Cli.LibsignalTripleRatchet.tryDecryptPlacedSpecP,
      RustCliAllocBudget.atState_pool,
      sessionStateAt_budgetAtState,
      protocolAddressAt_budgetAtState,
      signalMessageAt_budgetAtState,
      withFds_repAlloc]
    rw [withFds_pool_enforced A henf]
    sep_ac_rfl
  post_imp := (specImp_recordTryDecryptPlacedSpec C ctl parse S tdEnv henf).post_imp

private theorem specImp_tryDecryptPlacedSpecQF_PTight [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    (Q : List (BitVec 8) → Prop) (F : SepProp)
    (C : Crypto) (ctl : BitVec 64) (parse : UuidParser) (S : SpqrModel)
    (tdEnv : TryDecryptEnvArgs → List AllocEvent → Prop)
    (henf : lim.enforced = true) :
    SpecImp
      (tryDecryptPlacedSpecQF_PTight Q F C (withFds A) lim ctl parse S tdEnv)
      (withFdsGe3Closed (tryDecryptPlacedSpecQF_PTight Q F C A lim ctl parse S tdEnv)) where
  onPanic_eq := rfl
  onExit_eq := rfl
  onOom_eq := rfl
  pre_eq := by
    rintro ⟨x, st⟩ s0
    dsimp only [withFdsGe3Closed, tryDecryptPlacedSpecQF_PTight]
    have hp := (specImp_tryDecryptPlacedSpecP (A := A) C ctl parse S tdEnv henf).pre_eq (x, st) s0
    dsimp only [withFdsGe3Closed] at hp
    rw [← hp]
    sep_ac_rfl
  post_imp := by
    rintro ⟨x, st⟩ R s0 sf hpost
    dsimp only [withFdsGe3Closed, tryDecryptPlacedSpecQF_PTight] at hpost ⊢
    have h1 : sf.mem ⊨
        (tryDecryptPlacedSpecP C (withFds A) lim ctl parse S tdEnv).post (x, st) s0 sf ∗ (F ∗ R) :=
      Eq.mp (congrArg (sf.mem ⊨ ·) (by sep_ac_rfl)) hpost
    have h2 := (specImp_tryDecryptPlacedSpecP C ctl parse S tdEnv henf).post_imp
      (x, st) (F ∗ R) s0 sf h1
    dsimp only [withFdsGe3Closed] at h2
    exact Eq.mp (congrArg (sf.mem ⊨ ·) (by sep_ac_rfl)) h2

/-! ## `subroutine_ok` Conversion Seams (`withFds A` to `withFdsGe3Closed`) -/

theorem subroutine_ok_tryDecryptRawSpecTPTightAt_withFdsGe3Closed_of_withFds
    [LibsignalPlacement] {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {P : Program} {entry : BitVec 64}
    {C : Crypto} {ctl : BitVec 64} {parse : UuidParser} {S : SpqrModel}
    {tdEnv : TryDecryptEnvArgs → List AllocEvent → Prop}
    (henf : lim.enforced = true)
    (hok : subroutine_ok P entry
      (tryDecryptRawSpecTPTightAt C (withFds A) lim ctl parse S tdEnv)) :
    subroutine_ok P entry
      (withFdsGe3Closed (tryDecryptRawSpecTPTightAt C A lim ctl parse S tdEnv)) :=
  (specImp_tryDecryptPlacedSpecQF_PTight _ _ C ctl parse S tdEnv henf).to_subroutine_ok hok

theorem subroutine_ok_tryDecryptSpecTPTightAt_inner_withFdsGe3Closed_of_withFds
    [LibsignalPlacement] {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {P : Program} {entry : BitVec 64}
    {C : Crypto} {ctl : BitVec 64} {parse : UuidParser} {S : SpqrModel}
    {tdEnv : TryDecryptEnvArgs → List AllocEvent → Prop}
    (henf : lim.enforced = true)
    (hok : subroutine_ok P entry
      (tryDecryptSpecTPTightAt C (withFds A) lim ctl parse S tdEnv)) :
    subroutine_ok P entry
      (withLsCodeRoLoaded lsmpl
        (withFdsGe3Closed (tryDecryptRawSpecTPTightAt C A lim ctl parse S tdEnv))) :=
  ((specImp_tryDecryptPlacedSpecQF_PTight _ _ C ctl parse S tdEnv henf).withLsCodeRoLoaded
    lsmpl).to_subroutine_ok hok

theorem subroutine_ok_tryDecryptSpecTPTightAt_withFdsGe3Closed_of_withFds
    [LibsignalPlacement] {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {P : Program} {entry : BitVec 64}
    {C : Crypto} {ctl : BitVec 64} {parse : UuidParser} {S : SpqrModel}
    {tdEnv : TryDecryptEnvArgs → List AllocEvent → Prop}
    (henf : lim.enforced = true)
    (hok : subroutine_ok P entry
      (tryDecryptSpecTPTightAt C (withFds A) lim ctl parse S tdEnv)) :
    subroutine_ok P entry
      (withFdsGe3Closed (tryDecryptSpecTPTightAt C A lim ctl parse S tdEnv)) :=
  subroutine_ok_withFdsGe3Closed_withLsCodeRoLoaded_of_inner
    (subroutine_ok_tryDecryptSpecTPTightAt_inner_withFdsGe3Closed_of_withFds henf hok)

theorem subroutine_ok_storeKitCodeRoLoaded_tryDecryptRawSpecTPTightAt_withFdsGe3Closed_of_withFds
    [LibsignalPlacement] {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {P : Program} {entry : BitVec 64}
    {C : Crypto} {ctl : BitVec 64} {parse : UuidParser} {S : SpqrModel}
    {tdEnv : TryDecryptEnvArgs → List AllocEvent → Prop}
    (henf : lim.enforced = true)
    (hok : subroutine_ok P entry
      (CryptoVerification.LibsignalPublicApi.StoreKit.withLsCodeRoLoaded lsmpl
        (tryDecryptRawSpecTPTightAt C (withFds A) lim ctl parse S tdEnv))) :
    subroutine_ok P entry
      (CryptoVerification.LibsignalPublicApi.StoreKit.withLsCodeRoLoaded lsmpl
        (withFdsGe3Closed (tryDecryptRawSpecTPTightAt C A lim ctl parse S tdEnv))) :=
  ((specImp_tryDecryptPlacedSpecQF_PTight _ _ C ctl parse S tdEnv henf).withStoreKitCodeRoLoaded
    lsmpl).to_subroutine_ok hok

theorem subroutine_ok_cliTryDecryptSpecPlaced_withFdsGe3Closed_of_withFds
    [LibsignalPlacement] {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {P : Program} {entry : BitVec 64}
    {C : Crypto} {ctl : BitVec 64} {parse : UuidParser} {S : SpqrModel}
    {tdEnv : TryDecryptEnvArgs → List AllocEvent → Prop}
    (henf : lim.enforced = true)
    (hok : subroutine_ok P entry
      (cliTryDecryptSpecPlaced C (withFds A) lim ctl parse S tdEnv)) :
    subroutine_ok P entry
      (withFdsGe3Closed (cliTryDecryptSpecPlaced C A lim ctl parse S tdEnv)) :=
  subroutine_ok_withFdsGe3Closed_withLsCodeRoLoaded_of_inner
    (((specImp_recordTryDecryptPlacedSpec C ctl parse S tdEnv henf).withLsCodeRoLoaded
      lsmpl).to_subroutine_ok hok)

theorem subroutine_ok_cliTryDecryptTightSpecPlaced_withFdsGe3Closed_of_withFds
    [LibsignalPlacement] {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {P : Program} {entry : BitVec 64}
    {C : Crypto} {ctl : BitVec 64} {parse : UuidParser} {S : SpqrModel}
    {tdEnv : TryDecryptEnvArgs → List AllocEvent → Prop}
    (henf : lim.enforced = true)
    (hok : subroutine_ok P entry
      (cliTryDecryptTightSpecPlaced C (withFds A) lim ctl parse S tdEnv)) :
    subroutine_ok P entry
      (withFdsGe3Closed (cliTryDecryptTightSpecPlaced C A lim ctl parse S tdEnv)) :=
  subroutine_ok_withFdsGe3Closed_withLsCodeRoLoaded_of_inner
    (((specImp_tryDecryptPlacedTightSpec C ctl parse S tdEnv henf).withLsCodeRoLoaded
      lsmpl).to_subroutine_ok hok)

theorem subroutine_ok_cliTryDecryptSpecPPlaced_withFdsGe3Closed_of_withFds
    [LibsignalPlacement] {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {P : Program} {entry : BitVec 64}
    {C : Crypto} {ctl : BitVec 64} {parse : UuidParser} {S : SpqrModel}
    {tdEnv : TryDecryptEnvArgs → List AllocEvent → Prop}
    (henf : lim.enforced = true)
    (hok : subroutine_ok P entry
      (cliTryDecryptSpecPPlaced C (withFds A) lim ctl parse S tdEnv)) :
    subroutine_ok P entry
      (withFdsGe3Closed (cliTryDecryptSpecPPlaced C A lim ctl parse S tdEnv)) :=
  subroutine_ok_withFdsGe3Closed_withLsCodeRoLoaded_of_inner
    (((specImp_tryDecryptPlacedSpecP C ctl parse S tdEnv henf).withLsCodeRoLoaded
      lsmpl).to_subroutine_ok hok)

end LibsignalBinary.Proofs.Cli.TripleRatchet.Decrypt.DefsPlacedBudgetFd
