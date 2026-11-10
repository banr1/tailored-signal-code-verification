/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.CodecCalleesFsPlacedBudgetFd
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Slots.CliHookSatPlacedBudget
import Arm64.Trusted.Spec.Hoare
import Arm64.Trusted.Spec.SepLogic
import LibsignalBinary.Heap.IfaceSimp
import LibsignalBinary.Proofs.Common.SharedHelpers

/-!
# On-Trajectory Single-Step `SubroutineOutcome` Transport at `strippedMallocngBudget`

Transports single-step `SubroutineOutcome`s for `g.alloc`, `g.dealloc`, and `g.realloc` from
`CliGhostAllocHooks` at `mallocngHookRustCliAllocBudget` to `strippedMallocngBudget` across
`Stripped → Stripped`, `Unstripped → Unstripped`, and `Unstripped → Stripped` modes.
-/

set_option autoImplicit false
set_option linter.dupNamespace false

namespace LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.CodecCalleesFsStepTransportRFd

public section

open Arm64 ProofLib SepProp
open CryptoVerification (LibsignalPlacement)
open CryptoVerification.SignalSession.Cli.RunGlue (CliGhostHooks)
open LibsignalBinary.Heap (
  AllocCallPreserved AllocCostModel BudgetLimits MallocngCostModelIface MallocngCostModelSound
  OomPreserved rustCliAllocBudgetSpec rustCliDeallocBudgetSpec rustCliReallocBudgetSpec
)
open LibsignalBinary.Heap.IfaceSimp (
  allocCallPreserved_setMem allocCallPreserved_setMem_left oomPreserved_setMem
  oomPreserved_setMem_left
)
open LibsignalBinary.Proofs.HookDischarge.CryptoMallocngBudgetBase (
  CodeBlocksPermRX mallocngHookBudgetPool mallocngHookRustCliAllocBudget
)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.CodecCalleesFsPlacedBudgetFd (
  CodeBlocksPermStripped satisfies_mallocngPool_of_stripped satisfies_stripCodec_iff
  satisfies_strippedPool_of_mallocng sc_r64 sc_sp sc_st stripCodecMem stripCodecPerm
  stripCodecS strippedMallocngBudget strippedMallocngBudget_live strippedMallocngPool
)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Slots.CliHookSatPlacedBudget (
  CliGhostAllocHooks
)

/-! ## 1. Pure Frame & Calling-Convention Invariances of `stripCodecS` -/

private theorem sc_spAligned (keep : BitVec 64 → Bool) (s : State) :
    (stripCodecS keep s).spAligned = s.spAligned := by
  cases s; rfl

private theorem returned_sc_right (keep : BitVec 64 → Bool) (u v : State) :
    Returned u (stripCodecS keep v) ↔ Returned u v := by
  cases u; cases v; exact Iff.rfl

private theorem returned_sc_both (keep : BitVec 64 → Bool) (u v : State) :
    Returned (stripCodecS keep u) (stripCodecS keep v) ↔ Returned u v := by
  cases u; cases v; exact Iff.rfl

private theorem ccp_sc_right (keep : BitVec 64 → Bool) (u v : State) :
    CallingConventionPreserved u (stripCodecS keep v) ↔ CallingConventionPreserved u v := by
  cases u; cases v; exact Iff.rfl

private theorem ccp_sc_both (keep : BitVec 64 → Bool) (u v : State) :
    CallingConventionPreserved (stripCodecS keep u) (stripCodecS keep v) ↔
      CallingConventionPreserved u v := by
  cases u; cases v; exact Iff.rfl

private theorem acp_sc_right (keep : BitVec 64 → Bool) (u v : State) :
    AllocCallPreserved u (stripCodecS keep v) = AllocCallPreserved u v :=
  propext (allocCallPreserved_setMem u v (stripCodecMem keep v.mem))

private theorem acp_sc_both (keep : BitVec 64 → Bool) (u v : State) :
    AllocCallPreserved (stripCodecS keep u) (stripCodecS keep v) = AllocCallPreserved u v :=
  propext ((allocCallPreserved_setMem_left u (stripCodecS keep v) (stripCodecMem keep u.mem)).trans
    (allocCallPreserved_setMem u v (stripCodecMem keep v.mem)))

private theorem oomp_sc_right (keep : BitVec 64 → Bool) (u v : State) :
    OomPreserved u (stripCodecS keep v) = OomPreserved u v :=
  propext (oomPreserved_setMem u v (stripCodecMem keep v.mem))

private theorem oomp_sc_both (keep : BitVec 64 → Bool) (u v : State) :
    OomPreserved (stripCodecS keep u) (stripCodecS keep v) = OomPreserved u v :=
  propext ((oomPreserved_setMem_left u (stripCodecS keep v) (stripCodecMem keep u.mem)).trans
    (oomPreserved_setMem u v (stripCodecMem keep v.mem)))

/-! ## 2. Pool & Spec Equalities Outside `mallocng` (`hOut`) -/

theorem strippedMallocngPool_eq_of_hOut
    {keep : BitVec 64 → Bool}
    {M : AllocCostModel} {I : MallocngCostModelIface M} {hS : MallocngCostModelSound M I}
    {γ : GhostName} {mmpl : Obj.MultiPlacement} {tp brkStart : BitVec 64}
    {lim : BudgetLimits}
    (hOut : lim.enforced = false ∨
      ∀ a, (VerifiedLibraries.mallocngLib.findCodeBlock mmpl a).isSome = true → keep a = true)
    (st : M.σ) (s : State) :
    (strippedMallocngBudget keep M I hS γ mmpl tp brkStart).pool lim st s =
      (mallocngHookRustCliAllocBudget M I hS γ mmpl tp brkStart).pool lim st s := by
  change strippedMallocngPool keep M I γ mmpl tp brkStart lim st s =
    mallocngHookBudgetPool M I γ mmpl tp brkStart lim st s
  unfold strippedMallocngPool
  by_cases henf : lim.enforced = true
  · rcases hOut with hfalse | hkeep
    · rw [henf] at hfalse; cases hfalse
    · have hperm : CodeBlocksPermStripped keep mmpl s = CodeBlocksPermRX mmpl s := by
        apply propext
        constructor <;> intro h a ha
        · have ha' := h a ha
          rw [hkeep a ha] at ha'
          exact ha'
        · have ha' := h a ha
          rw [hkeep a ha]
          exact ha'
      unfold mallocngHookBudgetPool
      simp only [henf, ↓reduceIte, hperm]
  · simp only [henf]
    rfl

theorem rustCliAllocBudgetSpec_eq_of_hOut [LibsignalPlacement]
    {keep : BitVec 64 → Bool}
    {M : AllocCostModel} {I : MallocngCostModelIface M} {hS : MallocngCostModelSound M I}
    {γ : GhostName} {mmpl : Obj.MultiPlacement} {tp brkStart : BitVec 64}
    {lim : BudgetLimits} {zeroed : Bool}
    (hOut : lim.enforced = false ∨
      ∀ a, (VerifiedLibraries.mallocngLib.findCodeBlock mmpl a).isSome = true → keep a = true) :
    rustCliAllocBudgetSpec M (strippedMallocngBudget keep M I hS γ mmpl tp brkStart) lim zeroed =
      rustCliAllocBudgetSpec M (mallocngHookRustCliAllocBudget M I hS γ mmpl tp brkStart) lim zeroed := by
  have hpool :
      (strippedMallocngBudget keep M I hS γ mmpl tp brkStart).pool lim =
        (mallocngHookRustCliAllocBudget M I hS γ mmpl tp brkStart).pool lim := by
    funext st s
    exact strippedMallocngPool_eq_of_hOut hOut st s
  have hlive :
      (strippedMallocngBudget keep M I hS γ mmpl tp brkStart).live =
        (mallocngHookRustCliAllocBudget M I hS γ mmpl tp brkStart).live := rfl
  unfold rustCliAllocBudgetSpec
  rw [hpool, hlive]

theorem rustCliDeallocBudgetSpec_eq_of_hOut [LibsignalPlacement]
    {keep : BitVec 64 → Bool}
    {M : AllocCostModel} {I : MallocngCostModelIface M} {hS : MallocngCostModelSound M I}
    {γ : GhostName} {mmpl : Obj.MultiPlacement} {tp brkStart : BitVec 64}
    {lim : BudgetLimits}
    (hOut : lim.enforced = false ∨
      ∀ a, (VerifiedLibraries.mallocngLib.findCodeBlock mmpl a).isSome = true → keep a = true) :
    rustCliDeallocBudgetSpec M (strippedMallocngBudget keep M I hS γ mmpl tp brkStart) lim =
      rustCliDeallocBudgetSpec M (mallocngHookRustCliAllocBudget M I hS γ mmpl tp brkStart) lim := by
  have hpool :
      (strippedMallocngBudget keep M I hS γ mmpl tp brkStart).pool lim =
        (mallocngHookRustCliAllocBudget M I hS γ mmpl tp brkStart).pool lim := by
    funext st s
    exact strippedMallocngPool_eq_of_hOut hOut st s
  have hlive :
      (strippedMallocngBudget keep M I hS γ mmpl tp brkStart).live =
        (mallocngHookRustCliAllocBudget M I hS γ mmpl tp brkStart).live := rfl
  unfold rustCliDeallocBudgetSpec
  rw [hpool, hlive]

theorem rustCliReallocBudgetSpec_eq_of_hOut [LibsignalPlacement]
    {keep : BitVec 64 → Bool}
    {M : AllocCostModel} {I : MallocngCostModelIface M} {hS : MallocngCostModelSound M I}
    {γ : GhostName} {mmpl : Obj.MultiPlacement} {tp brkStart : BitVec 64}
    {lim : BudgetLimits}
    (hOut : lim.enforced = false ∨
      ∀ a, (VerifiedLibraries.mallocngLib.findCodeBlock mmpl a).isSome = true → keep a = true) :
    rustCliReallocBudgetSpec M (strippedMallocngBudget keep M I hS γ mmpl tp brkStart) lim =
      rustCliReallocBudgetSpec M (mallocngHookRustCliAllocBudget M I hS γ mmpl tp brkStart) lim := by
  have hpool :
      (strippedMallocngBudget keep M I hS γ mmpl tp brkStart).pool lim =
        (mallocngHookRustCliAllocBudget M I hS γ mmpl tp brkStart).pool lim := by
    funext st s
    exact strippedMallocngPool_eq_of_hOut hOut st s
  have hlive :
      (strippedMallocngBudget keep M I hS γ mmpl tp brkStart).live =
        (mallocngHookRustCliAllocBudget M I hS γ mmpl tp brkStart).live := rfl
  unfold rustCliReallocBudgetSpec
  rw [hpool, hlive]

/-! ## 3. Framed Pool Swaps Inside `(Q ∗ A.pool lim st s ∗ Rest) ∗ R` -/

private theorem swap_pool_stripped_to_mallocng
    {keep : BitVec 64 → Bool}
    {M : AllocCostModel} {I : MallocngCostModelIface M} {hS : MallocngCostModelSound M I}
    {γ : GhostName} {mmpl : Obj.MultiPlacement} {tp brkStart : BitVec 64}
    {lim : BudgetLimits} {st : M.σ} {u : State} {Q Rest R : SepProp}
    (hrx : lim.enforced = true → CodeBlocksPermRX mmpl u)
    (hsat : (stripCodecS keep u).mem ⊨
      (Q ∗ (strippedMallocngBudget keep M I hS γ mmpl tp brkStart).pool lim st (stripCodecS keep u) ∗ Rest) ∗ R) :
    u.mem ⊨
      (Q ∗ (mallocngHookRustCliAllocBudget M I hS γ mmpl tp brkStart).pool lim st u ∗ Rest) ∗ R := by
  have h1 :
      ((Q ∗ (strippedMallocngBudget keep M I hS γ mmpl tp brkStart).pool lim st (stripCodecS keep u) ∗ Rest) ∗ R) =
      ((strippedMallocngBudget keep M I hS γ mmpl tp brkStart).pool lim st (stripCodecS keep u) ∗ (Q ∗ Rest ∗ R)) := by
    sep_ac_rfl
  rw [h1] at hsat
  have h2 := satisfies_mallocngPool_of_stripped keep hrx hsat
  have h3 :
      ((mallocngHookRustCliAllocBudget M I hS γ mmpl tp brkStart).pool lim st u ∗ (Q ∗ Rest ∗ R)) =
      ((Q ∗ (mallocngHookRustCliAllocBudget M I hS γ mmpl tp brkStart).pool lim st u ∗ Rest) ∗ R) := by
    sep_ac_rfl
  rwa [h3] at h2

private theorem swap_pool_mallocng_to_stripped
    (keep : BitVec 64 → Bool)
    {M : AllocCostModel} {I : MallocngCostModelIface M} {hS : MallocngCostModelSound M I}
    {γ : GhostName} {mmpl : Obj.MultiPlacement} {tp brkStart : BitVec 64}
    {lim : BudgetLimits} {st : M.σ} {v : State} {Q Rest R : SepProp}
    (hsat : v.mem ⊨
      (Q ∗ (mallocngHookRustCliAllocBudget M I hS γ mmpl tp brkStart).pool lim st v ∗ Rest) ∗ R) :
    (stripCodecS keep v).mem ⊨
      (Q ∗ (strippedMallocngBudget keep M I hS γ mmpl tp brkStart).pool lim st (stripCodecS keep v) ∗ Rest) ∗ R := by
  have h1 :
      ((Q ∗ (mallocngHookRustCliAllocBudget M I hS γ mmpl tp brkStart).pool lim st v ∗ Rest) ∗ R) =
      ((mallocngHookRustCliAllocBudget M I hS γ mmpl tp brkStart).pool lim st v ∗ (Q ∗ Rest ∗ R)) := by
    sep_ac_rfl
  rw [h1] at hsat
  have h2 := satisfies_strippedPool_of_mallocng keep hsat
  have h3 :
      ((strippedMallocngBudget keep M I hS γ mmpl tp brkStart).pool lim st (stripCodecS keep v) ∗ (Q ∗ Rest ∗ R)) =
      ((Q ∗ (strippedMallocngBudget keep M I hS γ mmpl tp brkStart).pool lim st (stripCodecS keep v) ∗ Rest) ∗ R) := by
    sep_ac_rfl
  rwa [h3] at h2

/-! ## 4. Entry Precondition & Exit `SubroutineOutcome` Pool Transports -/

private theorem alloc_pre_mallocng_of_stripped [LibsignalPlacement]
    {keep : BitVec 64 → Bool}
    {M : AllocCostModel} {I : MallocngCostModelIface M} {hS : MallocngCostModelSound M I}
    {γ : GhostName} {mmpl : Obj.MultiPlacement} {tp brkStart : BitVec 64}
    {lim : BudgetLimits} {zeroed : Bool} {x : Nat × Nat × M.σ} {R : SepProp} {u : State}
    (hrx : lim.enforced = true → CodeBlocksPermRX mmpl u)
    (hpre : (stripCodecS keep u).mem ⊨
      (rustCliAllocBudgetSpec M (strippedMallocngBudget keep M I hS γ mmpl tp brkStart) lim zeroed).pre
        x (stripCodecS keep u) ∗ R) :
    u.mem ⊨
      (rustCliAllocBudgetSpec M (mallocngHookRustCliAllocBudget M I hS γ mmpl tp brkStart) lim zeroed).pre
        x u ∗ R := by
  rcases x with ⟨size, align, st⟩
  dsimp only [rustCliAllocBudgetSpec] at hpre ⊢
  simp only [sc_r64, sc_sp] at hpre
  exact swap_pool_stripped_to_mallocng hrx hpre

private theorem dealloc_pre_mallocng_of_stripped [LibsignalPlacement]
    {keep : BitVec 64 → Bool}
    {M : AllocCostModel} {I : MallocngCostModelIface M} {hS : MallocngCostModelSound M I}
    {γ : GhostName} {mmpl : Obj.MultiPlacement} {tp brkStart : BitVec 64}
    {lim : BudgetLimits} {x : BitVec 64 × Nat × Nat × M.σ} {R : SepProp} {u : State}
    (hrx : lim.enforced = true → CodeBlocksPermRX mmpl u)
    (hpre : (stripCodecS keep u).mem ⊨
      (rustCliDeallocBudgetSpec M (strippedMallocngBudget keep M I hS γ mmpl tp brkStart) lim).pre
        x (stripCodecS keep u) ∗ R) :
    u.mem ⊨
      (rustCliDeallocBudgetSpec M (mallocngHookRustCliAllocBudget M I hS γ mmpl tp brkStart) lim).pre
        x u ∗ R := by
  rcases x with ⟨p, size, align, st⟩
  dsimp only [rustCliDeallocBudgetSpec] at hpre ⊢
  simp only [sc_r64, sc_sp, strippedMallocngBudget_live] at hpre
  exact swap_pool_stripped_to_mallocng hrx hpre

private theorem realloc_pre_mallocng_of_stripped [LibsignalPlacement]
    {keep : BitVec 64 → Bool}
    {M : AllocCostModel} {I : MallocngCostModelIface M} {hS : MallocngCostModelSound M I}
    {γ : GhostName} {mmpl : Obj.MultiPlacement} {tp brkStart : BitVec 64}
    {lim : BudgetLimits} {x : BitVec 64 × Nat × Nat × Nat × List (BitVec 8) × M.σ}
    {R : SepProp} {u : State}
    (hrx : lim.enforced = true → CodeBlocksPermRX mmpl u)
    (hpre : (stripCodecS keep u).mem ⊨
      (rustCliReallocBudgetSpec M (strippedMallocngBudget keep M I hS γ mmpl tp brkStart) lim).pre
        x (stripCodecS keep u) ∗ R) :
    u.mem ⊨
      (rustCliReallocBudgetSpec M (mallocngHookRustCliAllocBudget M I hS γ mmpl tp brkStart) lim).pre
        x u ∗ R := by
  rcases x with ⟨p, old, align, new, bs, st⟩
  dsimp only [rustCliReallocBudgetSpec] at hpre ⊢
  simp only [sc_r64, sc_sp, strippedMallocngBudget_live] at hpre
  exact swap_pool_stripped_to_mallocng hrx hpre

private theorem alloc_outcome_strip_both [LibsignalPlacement]
    (keep : BitVec 64 → Bool)
    {M : AllocCostModel} {I : MallocngCostModelIface M} {hS : MallocngCostModelSound M I}
    {γ : GhostName} {mmpl : Obj.MultiPlacement} {tp brkStart : BitVec 64}
    {lim : BudgetLimits} {zeroed : Bool} {x : Nat × Nat × M.σ} {R : SepProp} {u v : State}
    (hout : SubroutineOutcome
      (rustCliAllocBudgetSpec M (mallocngHookRustCliAllocBudget M I hS γ mmpl tp brkStart) lim zeroed)
      x R u v) :
    SubroutineOutcome
      (rustCliAllocBudgetSpec M (strippedMallocngBudget keep M I hS γ mmpl tp brkStart) lim zeroed)
      x R (stripCodecS keep u) (stripCodecS keep v) := by
  rcases x with ⟨size, align, st⟩
  rcases hout with ⟨hret, hcc, hpost⟩ | ⟨hpan, hpansat⟩ | ⟨code, hexit, hexitsat⟩ | ⟨hoom, hoomsat⟩
  · refine Or.inl ⟨(returned_sc_both keep u v).mpr hret, (ccp_sc_both keep u v).mpr hcc, ?_⟩
    dsimp only [rustCliAllocBudgetSpec] at hpost ⊢
    simp only [sc_r64, sc_sp, strippedMallocngBudget_live, acp_sc_both]
    exact swap_pool_mallocng_to_stripped keep hpost
  · refine Or.inr (Or.inl ⟨by rw [sc_st]; exact hpan, ?_⟩)
    dsimp only [rustCliAllocBudgetSpec] at hpansat ⊢
    exact (satisfies_stripCodec_iff keep v.mem _).mpr hpansat
  · refine Or.inr (Or.inr (Or.inl ⟨code, by rw [sc_st]; exact hexit, ?_⟩))
    dsimp only [rustCliAllocBudgetSpec] at hexitsat ⊢
    exact (satisfies_stripCodec_iff keep v.mem _).mpr hexitsat
  · refine Or.inr (Or.inr (Or.inr ⟨by rw [sc_st]; exact hoom, ?_⟩))
    dsimp only [rustCliAllocBudgetSpec] at hoomsat ⊢
    simp only [oomp_sc_both]
    exact (satisfies_stripCodec_iff keep v.mem _).mpr hoomsat

private theorem alloc_outcome_strip_right [LibsignalPlacement]
    (keep : BitVec 64 → Bool)
    {M : AllocCostModel} {I : MallocngCostModelIface M} {hS : MallocngCostModelSound M I}
    {γ : GhostName} {mmpl : Obj.MultiPlacement} {tp brkStart : BitVec 64}
    {lim : BudgetLimits} {zeroed : Bool} {x : Nat × Nat × M.σ} {R : SepProp} {u v : State}
    (hout : SubroutineOutcome
      (rustCliAllocBudgetSpec M (mallocngHookRustCliAllocBudget M I hS γ mmpl tp brkStart) lim zeroed)
      x R u v) :
    SubroutineOutcome
      (rustCliAllocBudgetSpec M (strippedMallocngBudget keep M I hS γ mmpl tp brkStart) lim zeroed)
      x R u (stripCodecS keep v) := by
  rcases x with ⟨size, align, st⟩
  rcases hout with ⟨hret, hcc, hpost⟩ | ⟨hpan, hpansat⟩ | ⟨code, hexit, hexitsat⟩ | ⟨hoom, hoomsat⟩
  · refine Or.inl ⟨(returned_sc_right keep u v).mpr hret, (ccp_sc_right keep u v).mpr hcc, ?_⟩
    dsimp only [rustCliAllocBudgetSpec] at hpost ⊢
    simp only [sc_r64, strippedMallocngBudget_live, acp_sc_right]
    exact swap_pool_mallocng_to_stripped keep hpost
  · refine Or.inr (Or.inl ⟨by rw [sc_st]; exact hpan, ?_⟩)
    dsimp only [rustCliAllocBudgetSpec] at hpansat ⊢
    exact (satisfies_stripCodec_iff keep v.mem _).mpr hpansat
  · refine Or.inr (Or.inr (Or.inl ⟨code, by rw [sc_st]; exact hexit, ?_⟩))
    dsimp only [rustCliAllocBudgetSpec] at hexitsat ⊢
    exact (satisfies_stripCodec_iff keep v.mem _).mpr hexitsat
  · refine Or.inr (Or.inr (Or.inr ⟨by rw [sc_st]; exact hoom, ?_⟩))
    dsimp only [rustCliAllocBudgetSpec] at hoomsat ⊢
    simp only [oomp_sc_right]
    exact (satisfies_stripCodec_iff keep v.mem _).mpr hoomsat

private theorem dealloc_outcome_strip_both [LibsignalPlacement]
    (keep : BitVec 64 → Bool)
    {M : AllocCostModel} {I : MallocngCostModelIface M} {hS : MallocngCostModelSound M I}
    {γ : GhostName} {mmpl : Obj.MultiPlacement} {tp brkStart : BitVec 64}
    {lim : BudgetLimits} {x : BitVec 64 × Nat × Nat × M.σ} {R : SepProp} {u v : State}
    (hout : SubroutineOutcome
      (rustCliDeallocBudgetSpec M (mallocngHookRustCliAllocBudget M I hS γ mmpl tp brkStart) lim)
      x R u v) :
    SubroutineOutcome
      (rustCliDeallocBudgetSpec M (strippedMallocngBudget keep M I hS γ mmpl tp brkStart) lim)
      x R (stripCodecS keep u) (stripCodecS keep v) := by
  rcases x with ⟨p, size, align, st⟩
  rcases hout with ⟨hret, hcc, hpost⟩ | ⟨hpan, hpansat⟩ | ⟨code, hexit, hexitsat⟩ | ⟨hoom, hoomsat⟩
  · refine Or.inl ⟨(returned_sc_both keep u v).mpr hret, (ccp_sc_both keep u v).mpr hcc, ?_⟩
    dsimp only [rustCliDeallocBudgetSpec] at hpost ⊢
    simp only [sc_sp, acp_sc_both]
    exact swap_pool_mallocng_to_stripped keep hpost
  · refine Or.inr (Or.inl ⟨by rw [sc_st]; exact hpan, ?_⟩)
    dsimp only [rustCliDeallocBudgetSpec] at hpansat ⊢
    exact (satisfies_stripCodec_iff keep v.mem _).mpr hpansat
  · refine Or.inr (Or.inr (Or.inl ⟨code, by rw [sc_st]; exact hexit, ?_⟩))
    dsimp only [rustCliDeallocBudgetSpec] at hexitsat ⊢
    exact (satisfies_stripCodec_iff keep v.mem _).mpr hexitsat
  · refine Or.inr (Or.inr (Or.inr ⟨by rw [sc_st]; exact hoom, ?_⟩))
    dsimp only [rustCliDeallocBudgetSpec] at hoomsat ⊢
    exact (satisfies_stripCodec_iff keep v.mem _).mpr hoomsat

private theorem dealloc_outcome_strip_right [LibsignalPlacement]
    (keep : BitVec 64 → Bool)
    {M : AllocCostModel} {I : MallocngCostModelIface M} {hS : MallocngCostModelSound M I}
    {γ : GhostName} {mmpl : Obj.MultiPlacement} {tp brkStart : BitVec 64}
    {lim : BudgetLimits} {x : BitVec 64 × Nat × Nat × M.σ} {R : SepProp} {u v : State}
    (hout : SubroutineOutcome
      (rustCliDeallocBudgetSpec M (mallocngHookRustCliAllocBudget M I hS γ mmpl tp brkStart) lim)
      x R u v) :
    SubroutineOutcome
      (rustCliDeallocBudgetSpec M (strippedMallocngBudget keep M I hS γ mmpl tp brkStart) lim)
      x R u (stripCodecS keep v) := by
  rcases x with ⟨p, size, align, st⟩
  rcases hout with ⟨hret, hcc, hpost⟩ | ⟨hpan, hpansat⟩ | ⟨code, hexit, hexitsat⟩ | ⟨hoom, hoomsat⟩
  · refine Or.inl ⟨(returned_sc_right keep u v).mpr hret, (ccp_sc_right keep u v).mpr hcc, ?_⟩
    dsimp only [rustCliDeallocBudgetSpec] at hpost ⊢
    simp only [acp_sc_right]
    exact swap_pool_mallocng_to_stripped keep hpost
  · refine Or.inr (Or.inl ⟨by rw [sc_st]; exact hpan, ?_⟩)
    dsimp only [rustCliDeallocBudgetSpec] at hpansat ⊢
    exact (satisfies_stripCodec_iff keep v.mem _).mpr hpansat
  · refine Or.inr (Or.inr (Or.inl ⟨code, by rw [sc_st]; exact hexit, ?_⟩))
    dsimp only [rustCliDeallocBudgetSpec] at hexitsat ⊢
    exact (satisfies_stripCodec_iff keep v.mem _).mpr hexitsat
  · refine Or.inr (Or.inr (Or.inr ⟨by rw [sc_st]; exact hoom, ?_⟩))
    dsimp only [rustCliDeallocBudgetSpec] at hoomsat ⊢
    exact (satisfies_stripCodec_iff keep v.mem _).mpr hoomsat

private theorem realloc_outcome_strip_both [LibsignalPlacement]
    (keep : BitVec 64 → Bool)
    {M : AllocCostModel} {I : MallocngCostModelIface M} {hS : MallocngCostModelSound M I}
    {γ : GhostName} {mmpl : Obj.MultiPlacement} {tp brkStart : BitVec 64}
    {lim : BudgetLimits} {x : BitVec 64 × Nat × Nat × Nat × List (BitVec 8) × M.σ}
    {R : SepProp} {u v : State}
    (hout : SubroutineOutcome
      (rustCliReallocBudgetSpec M (mallocngHookRustCliAllocBudget M I hS γ mmpl tp brkStart) lim)
      x R u v) :
    SubroutineOutcome
      (rustCliReallocBudgetSpec M (strippedMallocngBudget keep M I hS γ mmpl tp brkStart) lim)
      x R (stripCodecS keep u) (stripCodecS keep v) := by
  rcases x with ⟨p, old, align, new, bs, st⟩
  rcases hout with ⟨hret, hcc, hpost⟩ | ⟨hpan, hpansat⟩ | ⟨code, hexit, hexitsat⟩ | ⟨hoom, hoomsat⟩
  · refine Or.inl ⟨(returned_sc_both keep u v).mpr hret, (ccp_sc_both keep u v).mpr hcc, ?_⟩
    dsimp only [rustCliReallocBudgetSpec] at hpost ⊢
    simp only [sc_r64, sc_sp, strippedMallocngBudget_live, acp_sc_both]
    exact swap_pool_mallocng_to_stripped keep hpost
  · refine Or.inr (Or.inl ⟨by rw [sc_st]; exact hpan, ?_⟩)
    dsimp only [rustCliReallocBudgetSpec] at hpansat ⊢
    exact (satisfies_stripCodec_iff keep v.mem _).mpr hpansat
  · refine Or.inr (Or.inr (Or.inl ⟨code, by rw [sc_st]; exact hexit, ?_⟩))
    dsimp only [rustCliReallocBudgetSpec] at hexitsat ⊢
    exact (satisfies_stripCodec_iff keep v.mem _).mpr hexitsat
  · refine Or.inr (Or.inr (Or.inr ⟨by rw [sc_st]; exact hoom, ?_⟩))
    dsimp only [rustCliReallocBudgetSpec] at hoomsat ⊢
    simp only [oomp_sc_both]
    exact (satisfies_stripCodec_iff keep v.mem _).mpr hoomsat

private theorem realloc_outcome_strip_right [LibsignalPlacement]
    (keep : BitVec 64 → Bool)
    {M : AllocCostModel} {I : MallocngCostModelIface M} {hS : MallocngCostModelSound M I}
    {γ : GhostName} {mmpl : Obj.MultiPlacement} {tp brkStart : BitVec 64}
    {lim : BudgetLimits} {x : BitVec 64 × Nat × Nat × Nat × List (BitVec 8) × M.σ}
    {R : SepProp} {u v : State}
    (hout : SubroutineOutcome
      (rustCliReallocBudgetSpec M (mallocngHookRustCliAllocBudget M I hS γ mmpl tp brkStart) lim)
      x R u v) :
    SubroutineOutcome
      (rustCliReallocBudgetSpec M (strippedMallocngBudget keep M I hS γ mmpl tp brkStart) lim)
      x R u (stripCodecS keep v) := by
  rcases x with ⟨p, old, align, new, bs, st⟩
  rcases hout with ⟨hret, hcc, hpost⟩ | ⟨hpan, hpansat⟩ | ⟨code, hexit, hexitsat⟩ | ⟨hoom, hoomsat⟩
  · refine Or.inl ⟨(returned_sc_right keep u v).mpr hret, (ccp_sc_right keep u v).mpr hcc, ?_⟩
    dsimp only [rustCliReallocBudgetSpec] at hpost ⊢
    simp only [sc_r64, strippedMallocngBudget_live, acp_sc_right]
    exact swap_pool_mallocng_to_stripped keep hpost
  · refine Or.inr (Or.inl ⟨by rw [sc_st]; exact hpan, ?_⟩)
    dsimp only [rustCliReallocBudgetSpec] at hpansat ⊢
    exact (satisfies_stripCodec_iff keep v.mem _).mpr hpansat
  · refine Or.inr (Or.inr (Or.inl ⟨code, by rw [sc_st]; exact hexit, ?_⟩))
    dsimp only [rustCliReallocBudgetSpec] at hexitsat ⊢
    exact (satisfies_stripCodec_iff keep v.mem _).mpr hexitsat
  · refine Or.inr (Or.inr (Or.inr ⟨by rw [sc_st]; exact hoom, ?_⟩))
    dsimp only [rustCliReallocBudgetSpec] at hoomsat ⊢
    simp only [oomp_sc_right]
    exact (satisfies_stripCodec_iff keep v.mem _).mpr hoomsat

/-! ## 5. Generic `HookOk` On-Trajectory Single-Step Transport -/

theorem hookOk_alloc_stripped_to_stripped [LibsignalPlacement]
    {keep : BitVec 64 → Bool}
    {M : AllocCostModel} {I : MallocngCostModelIface M} {hS : MallocngCostModelSound M I}
    {γ : GhostName} {mmpl : Obj.MultiPlacement} {tp brkStart : BitVec 64}
    {lim : BudgetLimits} {zeroed : Bool} {fn : State → State}
    (hok : HookOk fn
      (rustCliAllocBudgetSpec M (mallocngHookRustCliAllocBudget M I hS γ mmpl tp brkStart) lim zeroed))
    (u : State) (hrx : lim.enforced = true → CodeBlocksPermRX mmpl u) :
    ∀ x R,
      (stripCodecS keep u).status = .Running →
      ((stripCodecS keep u).mem ⊨
        (rustCliAllocBudgetSpec M (strippedMallocngBudget keep M I hS γ mmpl tp brkStart) lim zeroed).pre
          x (stripCodecS keep u) ∗ R) →
      (stripCodecS keep u).spAligned = true →
      SubroutineOutcome
        (rustCliAllocBudgetSpec M (strippedMallocngBudget keep M I hS γ mmpl tp brkStart) lim zeroed)
        x R (stripCodecS keep u) (stripCodecS keep (fn u)) := by
  intro x R hrun hpre hsp
  rw [sc_st] at hrun
  rw [sc_spAligned] at hsp
  exact alloc_outcome_strip_both keep
    (hok x R u hrun (alloc_pre_mallocng_of_stripped hrx hpre) hsp).2.2

theorem hookOk_dealloc_stripped_to_stripped [LibsignalPlacement]
    {keep : BitVec 64 → Bool}
    {M : AllocCostModel} {I : MallocngCostModelIface M} {hS : MallocngCostModelSound M I}
    {γ : GhostName} {mmpl : Obj.MultiPlacement} {tp brkStart : BitVec 64}
    {lim : BudgetLimits} {fn : State → State}
    (hok : HookOk fn
      (rustCliDeallocBudgetSpec M (mallocngHookRustCliAllocBudget M I hS γ mmpl tp brkStart) lim))
    (u : State) (hrx : lim.enforced = true → CodeBlocksPermRX mmpl u) :
    ∀ x R,
      (stripCodecS keep u).status = .Running →
      ((stripCodecS keep u).mem ⊨
        (rustCliDeallocBudgetSpec M (strippedMallocngBudget keep M I hS γ mmpl tp brkStart) lim).pre
          x (stripCodecS keep u) ∗ R) →
      (stripCodecS keep u).spAligned = true →
      SubroutineOutcome
        (rustCliDeallocBudgetSpec M (strippedMallocngBudget keep M I hS γ mmpl tp brkStart) lim)
        x R (stripCodecS keep u) (stripCodecS keep (fn u)) := by
  intro x R hrun hpre hsp
  rw [sc_st] at hrun
  rw [sc_spAligned] at hsp
  exact dealloc_outcome_strip_both keep
    (hok x R u hrun (dealloc_pre_mallocng_of_stripped hrx hpre) hsp).2.2

theorem hookOk_realloc_stripped_to_stripped [LibsignalPlacement]
    {keep : BitVec 64 → Bool}
    {M : AllocCostModel} {I : MallocngCostModelIface M} {hS : MallocngCostModelSound M I}
    {γ : GhostName} {mmpl : Obj.MultiPlacement} {tp brkStart : BitVec 64}
    {lim : BudgetLimits} {fn : State → State}
    (hok : HookOk fn
      (rustCliReallocBudgetSpec M (mallocngHookRustCliAllocBudget M I hS γ mmpl tp brkStart) lim))
    (u : State) (hrx : lim.enforced = true → CodeBlocksPermRX mmpl u) :
    ∀ x R,
      (stripCodecS keep u).status = .Running →
      ((stripCodecS keep u).mem ⊨
        (rustCliReallocBudgetSpec M (strippedMallocngBudget keep M I hS γ mmpl tp brkStart) lim).pre
          x (stripCodecS keep u) ∗ R) →
      (stripCodecS keep u).spAligned = true →
      SubroutineOutcome
        (rustCliReallocBudgetSpec M (strippedMallocngBudget keep M I hS γ mmpl tp brkStart) lim)
        x R (stripCodecS keep u) (stripCodecS keep (fn u)) := by
  intro x R hrun hpre hsp
  rw [sc_st] at hrun
  rw [sc_spAligned] at hsp
  exact realloc_outcome_strip_both keep
    (hok x R u hrun (realloc_pre_mallocng_of_stripped hrx hpre) hsp).2.2

theorem hookOk_alloc_unstripped_to_unstripped [LibsignalPlacement]
    {keep : BitVec 64 → Bool}
    {M : AllocCostModel} {I : MallocngCostModelIface M} {hS : MallocngCostModelSound M I}
    {γ : GhostName} {mmpl : Obj.MultiPlacement} {tp brkStart : BitVec 64}
    {lim : BudgetLimits} {zeroed : Bool} {fn : State → State}
    (hok : HookOk fn
      (rustCliAllocBudgetSpec M (mallocngHookRustCliAllocBudget M I hS γ mmpl tp brkStart) lim zeroed))
    (hOut : lim.enforced = false ∨
      ∀ a, (VerifiedLibraries.mallocngLib.findCodeBlock mmpl a).isSome = true → keep a = true)
    (u : State) :
    ∀ x R,
      u.status = .Running →
      (u.mem ⊨
        (rustCliAllocBudgetSpec M (strippedMallocngBudget keep M I hS γ mmpl tp brkStart) lim zeroed).pre
          x u ∗ R) →
      u.spAligned = true →
      SubroutineOutcome
        (rustCliAllocBudgetSpec M (strippedMallocngBudget keep M I hS γ mmpl tp brkStart) lim zeroed)
        x R u (fn u) := by
  intro x R hrun hpre hsp
  rw [rustCliAllocBudgetSpec_eq_of_hOut hOut] at hpre ⊢
  exact (hok x R u hrun hpre hsp).2.2

theorem hookOk_dealloc_unstripped_to_unstripped [LibsignalPlacement]
    {keep : BitVec 64 → Bool}
    {M : AllocCostModel} {I : MallocngCostModelIface M} {hS : MallocngCostModelSound M I}
    {γ : GhostName} {mmpl : Obj.MultiPlacement} {tp brkStart : BitVec 64}
    {lim : BudgetLimits} {fn : State → State}
    (hok : HookOk fn
      (rustCliDeallocBudgetSpec M (mallocngHookRustCliAllocBudget M I hS γ mmpl tp brkStart) lim))
    (hOut : lim.enforced = false ∨
      ∀ a, (VerifiedLibraries.mallocngLib.findCodeBlock mmpl a).isSome = true → keep a = true)
    (u : State) :
    ∀ x R,
      u.status = .Running →
      (u.mem ⊨
        (rustCliDeallocBudgetSpec M (strippedMallocngBudget keep M I hS γ mmpl tp brkStart) lim).pre
          x u ∗ R) →
      u.spAligned = true →
      SubroutineOutcome
        (rustCliDeallocBudgetSpec M (strippedMallocngBudget keep M I hS γ mmpl tp brkStart) lim)
        x R u (fn u) := by
  intro x R hrun hpre hsp
  rw [rustCliDeallocBudgetSpec_eq_of_hOut hOut] at hpre ⊢
  exact (hok x R u hrun hpre hsp).2.2

theorem hookOk_realloc_unstripped_to_unstripped [LibsignalPlacement]
    {keep : BitVec 64 → Bool}
    {M : AllocCostModel} {I : MallocngCostModelIface M} {hS : MallocngCostModelSound M I}
    {γ : GhostName} {mmpl : Obj.MultiPlacement} {tp brkStart : BitVec 64}
    {lim : BudgetLimits} {fn : State → State}
    (hok : HookOk fn
      (rustCliReallocBudgetSpec M (mallocngHookRustCliAllocBudget M I hS γ mmpl tp brkStart) lim))
    (hOut : lim.enforced = false ∨
      ∀ a, (VerifiedLibraries.mallocngLib.findCodeBlock mmpl a).isSome = true → keep a = true)
    (u : State) :
    ∀ x R,
      u.status = .Running →
      (u.mem ⊨
        (rustCliReallocBudgetSpec M (strippedMallocngBudget keep M I hS γ mmpl tp brkStart) lim).pre
          x u ∗ R) →
      u.spAligned = true →
      SubroutineOutcome
        (rustCliReallocBudgetSpec M (strippedMallocngBudget keep M I hS γ mmpl tp brkStart) lim)
        x R u (fn u) := by
  intro x R hrun hpre hsp
  rw [rustCliReallocBudgetSpec_eq_of_hOut hOut] at hpre ⊢
  exact (hok x R u hrun hpre hsp).2.2

theorem hookOk_alloc_unstripped_to_stripped [LibsignalPlacement]
    {keep : BitVec 64 → Bool}
    {M : AllocCostModel} {I : MallocngCostModelIface M} {hS : MallocngCostModelSound M I}
    {γ : GhostName} {mmpl : Obj.MultiPlacement} {tp brkStart : BitVec 64}
    {lim : BudgetLimits} {zeroed : Bool} {fn : State → State}
    (hok : HookOk fn
      (rustCliAllocBudgetSpec M (mallocngHookRustCliAllocBudget M I hS γ mmpl tp brkStart) lim zeroed))
    (hOut : lim.enforced = false ∨
      ∀ a, (VerifiedLibraries.mallocngLib.findCodeBlock mmpl a).isSome = true → keep a = true)
    (u : State) :
    ∀ x R,
      u.status = .Running →
      (u.mem ⊨
        (rustCliAllocBudgetSpec M (strippedMallocngBudget keep M I hS γ mmpl tp brkStart) lim zeroed).pre
          x u ∗ R) →
      u.spAligned = true →
      SubroutineOutcome
        (rustCliAllocBudgetSpec M (strippedMallocngBudget keep M I hS γ mmpl tp brkStart) lim zeroed)
        x R u (stripCodecS keep (fn u)) := by
  intro x R hrun hpre hsp
  rw [rustCliAllocBudgetSpec_eq_of_hOut hOut] at hpre
  exact alloc_outcome_strip_right keep (hok x R u hrun hpre hsp).2.2

theorem hookOk_dealloc_unstripped_to_stripped [LibsignalPlacement]
    {keep : BitVec 64 → Bool}
    {M : AllocCostModel} {I : MallocngCostModelIface M} {hS : MallocngCostModelSound M I}
    {γ : GhostName} {mmpl : Obj.MultiPlacement} {tp brkStart : BitVec 64}
    {lim : BudgetLimits} {fn : State → State}
    (hok : HookOk fn
      (rustCliDeallocBudgetSpec M (mallocngHookRustCliAllocBudget M I hS γ mmpl tp brkStart) lim))
    (hOut : lim.enforced = false ∨
      ∀ a, (VerifiedLibraries.mallocngLib.findCodeBlock mmpl a).isSome = true → keep a = true)
    (u : State) :
    ∀ x R,
      u.status = .Running →
      (u.mem ⊨
        (rustCliDeallocBudgetSpec M (strippedMallocngBudget keep M I hS γ mmpl tp brkStart) lim).pre
          x u ∗ R) →
      u.spAligned = true →
      SubroutineOutcome
        (rustCliDeallocBudgetSpec M (strippedMallocngBudget keep M I hS γ mmpl tp brkStart) lim)
        x R u (stripCodecS keep (fn u)) := by
  intro x R hrun hpre hsp
  rw [rustCliDeallocBudgetSpec_eq_of_hOut hOut] at hpre
  exact dealloc_outcome_strip_right keep (hok x R u hrun hpre hsp).2.2

theorem hookOk_realloc_unstripped_to_stripped [LibsignalPlacement]
    {keep : BitVec 64 → Bool}
    {M : AllocCostModel} {I : MallocngCostModelIface M} {hS : MallocngCostModelSound M I}
    {γ : GhostName} {mmpl : Obj.MultiPlacement} {tp brkStart : BitVec 64}
    {lim : BudgetLimits} {fn : State → State}
    (hok : HookOk fn
      (rustCliReallocBudgetSpec M (mallocngHookRustCliAllocBudget M I hS γ mmpl tp brkStart) lim))
    (hOut : lim.enforced = false ∨
      ∀ a, (VerifiedLibraries.mallocngLib.findCodeBlock mmpl a).isSome = true → keep a = true)
    (u : State) :
    ∀ x R,
      u.status = .Running →
      (u.mem ⊨
        (rustCliReallocBudgetSpec M (strippedMallocngBudget keep M I hS γ mmpl tp brkStart) lim).pre
          x u ∗ R) →
      u.spAligned = true →
      SubroutineOutcome
        (rustCliReallocBudgetSpec M (strippedMallocngBudget keep M I hS γ mmpl tp brkStart) lim)
        x R u (stripCodecS keep (fn u)) := by
  intro x R hrun hpre hsp
  rw [rustCliReallocBudgetSpec_eq_of_hOut hOut] at hpre
  exact realloc_outcome_strip_right keep (hok x R u hrun hpre hsp).2.2

/-! ## 6. `CliGhostAllocHooks` Specializations (All 3 Modes + Disjunctive) -/

/-! ### Mode 1: `Stripped → Stripped` -/

theorem alloc_stripped_to_stripped [LibsignalPlacement]
    {keep : BitVec 64 → Bool}
    {M : AllocCostModel} {I : MallocngCostModelIface M} {hS : MallocngCostModelSound M I}
    {γ : GhostName} {mmpl : Obj.MultiPlacement} {tp brkStart : BitVec 64}
    {lim : BudgetLimits} {g : CliGhostHooks}
    (hG : CliGhostAllocHooks M (mallocngHookRustCliAllocBudget M I hS γ mmpl tp brkStart) lim g)
    (u : State) (hrx : lim.enforced = true → CodeBlocksPermRX mmpl u) :
    ∀ x R,
      (stripCodecS keep u).status = .Running →
      ((stripCodecS keep u).mem ⊨
        (rustCliAllocBudgetSpec M (strippedMallocngBudget keep M I hS γ mmpl tp brkStart) lim false).pre
          x (stripCodecS keep u) ∗ R) →
      (stripCodecS keep u).spAligned = true →
      SubroutineOutcome
        (rustCliAllocBudgetSpec M (strippedMallocngBudget keep M I hS γ mmpl tp brkStart) lim false)
        x R (stripCodecS keep u) (stripCodecS keep (g.alloc u)) :=
  hookOk_alloc_stripped_to_stripped hG.alloc u hrx

theorem dealloc_stripped_to_stripped [LibsignalPlacement]
    {keep : BitVec 64 → Bool}
    {M : AllocCostModel} {I : MallocngCostModelIface M} {hS : MallocngCostModelSound M I}
    {γ : GhostName} {mmpl : Obj.MultiPlacement} {tp brkStart : BitVec 64}
    {lim : BudgetLimits} {g : CliGhostHooks}
    (hG : CliGhostAllocHooks M (mallocngHookRustCliAllocBudget M I hS γ mmpl tp brkStart) lim g)
    (u : State) (hrx : lim.enforced = true → CodeBlocksPermRX mmpl u) :
    ∀ x R,
      (stripCodecS keep u).status = .Running →
      ((stripCodecS keep u).mem ⊨
        (rustCliDeallocBudgetSpec M (strippedMallocngBudget keep M I hS γ mmpl tp brkStart) lim).pre
          x (stripCodecS keep u) ∗ R) →
      (stripCodecS keep u).spAligned = true →
      SubroutineOutcome
        (rustCliDeallocBudgetSpec M (strippedMallocngBudget keep M I hS γ mmpl tp brkStart) lim)
        x R (stripCodecS keep u) (stripCodecS keep (g.dealloc u)) :=
  hookOk_dealloc_stripped_to_stripped hG.dealloc u hrx

theorem realloc_stripped_to_stripped [LibsignalPlacement]
    {keep : BitVec 64 → Bool}
    {M : AllocCostModel} {I : MallocngCostModelIface M} {hS : MallocngCostModelSound M I}
    {γ : GhostName} {mmpl : Obj.MultiPlacement} {tp brkStart : BitVec 64}
    {lim : BudgetLimits} {g : CliGhostHooks}
    (hG : CliGhostAllocHooks M (mallocngHookRustCliAllocBudget M I hS γ mmpl tp brkStart) lim g)
    (u : State) (hrx : lim.enforced = true → CodeBlocksPermRX mmpl u) :
    ∀ x R,
      (stripCodecS keep u).status = .Running →
      ((stripCodecS keep u).mem ⊨
        (rustCliReallocBudgetSpec M (strippedMallocngBudget keep M I hS γ mmpl tp brkStart) lim).pre
          x (stripCodecS keep u) ∗ R) →
      (stripCodecS keep u).spAligned = true →
      SubroutineOutcome
        (rustCliReallocBudgetSpec M (strippedMallocngBudget keep M I hS γ mmpl tp brkStart) lim)
        x R (stripCodecS keep u) (stripCodecS keep (g.realloc u)) :=
  hookOk_realloc_stripped_to_stripped hG.realloc u hrx

/-! ### Mode 2: `Unstripped → Unstripped` under `hOut` -/

theorem alloc_unstripped_to_unstripped [LibsignalPlacement]
    {keep : BitVec 64 → Bool}
    {M : AllocCostModel} {I : MallocngCostModelIface M} {hS : MallocngCostModelSound M I}
    {γ : GhostName} {mmpl : Obj.MultiPlacement} {tp brkStart : BitVec 64}
    {lim : BudgetLimits} {g : CliGhostHooks}
    (hG : CliGhostAllocHooks M (mallocngHookRustCliAllocBudget M I hS γ mmpl tp brkStart) lim g)
    (hOut : lim.enforced = false ∨
      ∀ a, (VerifiedLibraries.mallocngLib.findCodeBlock mmpl a).isSome = true → keep a = true)
    (u : State) :
    ∀ x R,
      u.status = .Running →
      (u.mem ⊨
        (rustCliAllocBudgetSpec M (strippedMallocngBudget keep M I hS γ mmpl tp brkStart) lim false).pre
          x u ∗ R) →
      u.spAligned = true →
      SubroutineOutcome
        (rustCliAllocBudgetSpec M (strippedMallocngBudget keep M I hS γ mmpl tp brkStart) lim false)
        x R u (g.alloc u) :=
  hookOk_alloc_unstripped_to_unstripped hG.alloc hOut u

theorem dealloc_unstripped_to_unstripped [LibsignalPlacement]
    {keep : BitVec 64 → Bool}
    {M : AllocCostModel} {I : MallocngCostModelIface M} {hS : MallocngCostModelSound M I}
    {γ : GhostName} {mmpl : Obj.MultiPlacement} {tp brkStart : BitVec 64}
    {lim : BudgetLimits} {g : CliGhostHooks}
    (hG : CliGhostAllocHooks M (mallocngHookRustCliAllocBudget M I hS γ mmpl tp brkStart) lim g)
    (hOut : lim.enforced = false ∨
      ∀ a, (VerifiedLibraries.mallocngLib.findCodeBlock mmpl a).isSome = true → keep a = true)
    (u : State) :
    ∀ x R,
      u.status = .Running →
      (u.mem ⊨
        (rustCliDeallocBudgetSpec M (strippedMallocngBudget keep M I hS γ mmpl tp brkStart) lim).pre
          x u ∗ R) →
      u.spAligned = true →
      SubroutineOutcome
        (rustCliDeallocBudgetSpec M (strippedMallocngBudget keep M I hS γ mmpl tp brkStart) lim)
        x R u (g.dealloc u) :=
  hookOk_dealloc_unstripped_to_unstripped hG.dealloc hOut u

theorem realloc_unstripped_to_unstripped [LibsignalPlacement]
    {keep : BitVec 64 → Bool}
    {M : AllocCostModel} {I : MallocngCostModelIface M} {hS : MallocngCostModelSound M I}
    {γ : GhostName} {mmpl : Obj.MultiPlacement} {tp brkStart : BitVec 64}
    {lim : BudgetLimits} {g : CliGhostHooks}
    (hG : CliGhostAllocHooks M (mallocngHookRustCliAllocBudget M I hS γ mmpl tp brkStart) lim g)
    (hOut : lim.enforced = false ∨
      ∀ a, (VerifiedLibraries.mallocngLib.findCodeBlock mmpl a).isSome = true → keep a = true)
    (u : State) :
    ∀ x R,
      u.status = .Running →
      (u.mem ⊨
        (rustCliReallocBudgetSpec M (strippedMallocngBudget keep M I hS γ mmpl tp brkStart) lim).pre
          x u ∗ R) →
      u.spAligned = true →
      SubroutineOutcome
        (rustCliReallocBudgetSpec M (strippedMallocngBudget keep M I hS γ mmpl tp brkStart) lim)
        x R u (g.realloc u) :=
  hookOk_realloc_unstripped_to_unstripped hG.realloc hOut u

/-! ### Mode 3: `Unstripped → Stripped` under `hOut` -/

theorem alloc_unstripped_to_stripped [LibsignalPlacement]
    {keep : BitVec 64 → Bool}
    {M : AllocCostModel} {I : MallocngCostModelIface M} {hS : MallocngCostModelSound M I}
    {γ : GhostName} {mmpl : Obj.MultiPlacement} {tp brkStart : BitVec 64}
    {lim : BudgetLimits} {g : CliGhostHooks}
    (hG : CliGhostAllocHooks M (mallocngHookRustCliAllocBudget M I hS γ mmpl tp brkStart) lim g)
    (hOut : lim.enforced = false ∨
      ∀ a, (VerifiedLibraries.mallocngLib.findCodeBlock mmpl a).isSome = true → keep a = true)
    (u : State) :
    ∀ x R,
      u.status = .Running →
      (u.mem ⊨
        (rustCliAllocBudgetSpec M (strippedMallocngBudget keep M I hS γ mmpl tp brkStart) lim false).pre
          x u ∗ R) →
      u.spAligned = true →
      SubroutineOutcome
        (rustCliAllocBudgetSpec M (strippedMallocngBudget keep M I hS γ mmpl tp brkStart) lim false)
        x R u (stripCodecS keep (g.alloc u)) :=
  hookOk_alloc_unstripped_to_stripped hG.alloc hOut u

theorem dealloc_unstripped_to_stripped [LibsignalPlacement]
    {keep : BitVec 64 → Bool}
    {M : AllocCostModel} {I : MallocngCostModelIface M} {hS : MallocngCostModelSound M I}
    {γ : GhostName} {mmpl : Obj.MultiPlacement} {tp brkStart : BitVec 64}
    {lim : BudgetLimits} {g : CliGhostHooks}
    (hG : CliGhostAllocHooks M (mallocngHookRustCliAllocBudget M I hS γ mmpl tp brkStart) lim g)
    (hOut : lim.enforced = false ∨
      ∀ a, (VerifiedLibraries.mallocngLib.findCodeBlock mmpl a).isSome = true → keep a = true)
    (u : State) :
    ∀ x R,
      u.status = .Running →
      (u.mem ⊨
        (rustCliDeallocBudgetSpec M (strippedMallocngBudget keep M I hS γ mmpl tp brkStart) lim).pre
          x u ∗ R) →
      u.spAligned = true →
      SubroutineOutcome
        (rustCliDeallocBudgetSpec M (strippedMallocngBudget keep M I hS γ mmpl tp brkStart) lim)
        x R u (stripCodecS keep (g.dealloc u)) :=
  hookOk_dealloc_unstripped_to_stripped hG.dealloc hOut u

theorem realloc_unstripped_to_stripped [LibsignalPlacement]
    {keep : BitVec 64 → Bool}
    {M : AllocCostModel} {I : MallocngCostModelIface M} {hS : MallocngCostModelSound M I}
    {γ : GhostName} {mmpl : Obj.MultiPlacement} {tp brkStart : BitVec 64}
    {lim : BudgetLimits} {g : CliGhostHooks}
    (hG : CliGhostAllocHooks M (mallocngHookRustCliAllocBudget M I hS γ mmpl tp brkStart) lim g)
    (hOut : lim.enforced = false ∨
      ∀ a, (VerifiedLibraries.mallocngLib.findCodeBlock mmpl a).isSome = true → keep a = true)
    (u : State) :
    ∀ x R,
      u.status = .Running →
      (u.mem ⊨
        (rustCliReallocBudgetSpec M (strippedMallocngBudget keep M I hS γ mmpl tp brkStart) lim).pre
          x u ∗ R) →
      u.spAligned = true →
      SubroutineOutcome
        (rustCliReallocBudgetSpec M (strippedMallocngBudget keep M I hS γ mmpl tp brkStart) lim)
        x R u (stripCodecS keep (g.realloc u)) :=
  hookOk_realloc_unstripped_to_stripped hG.realloc hOut u

/-! ### Combined Disjunctive Mode 2 ∨ Mode 3 (`v' ∈ {g.fn u, stripCodecS keep (g.fn u)}`) -/

theorem alloc_unstripped_of_hOut [LibsignalPlacement]
    {keep : BitVec 64 → Bool}
    {M : AllocCostModel} {I : MallocngCostModelIface M} {hS : MallocngCostModelSound M I}
    {γ : GhostName} {mmpl : Obj.MultiPlacement} {tp brkStart : BitVec 64}
    {lim : BudgetLimits} {g : CliGhostHooks}
    (hG : CliGhostAllocHooks M (mallocngHookRustCliAllocBudget M I hS γ mmpl tp brkStart) lim g)
    (hOut : lim.enforced = false ∨
      ∀ a, (VerifiedLibraries.mallocngLib.findCodeBlock mmpl a).isSome = true → keep a = true)
    (u v' : State) (hv' : v' = g.alloc u ∨ v' = stripCodecS keep (g.alloc u)) :
    ∀ x R,
      u.status = .Running →
      (u.mem ⊨
        (rustCliAllocBudgetSpec M (strippedMallocngBudget keep M I hS γ mmpl tp brkStart) lim false).pre
          x u ∗ R) →
      u.spAligned = true →
      SubroutineOutcome
        (rustCliAllocBudgetSpec M (strippedMallocngBudget keep M I hS γ mmpl tp brkStart) lim false)
        x R u v' := by
  rcases hv' with rfl | rfl
  · exact alloc_unstripped_to_unstripped hG hOut u
  · exact alloc_unstripped_to_stripped hG hOut u

theorem dealloc_unstripped_of_hOut [LibsignalPlacement]
    {keep : BitVec 64 → Bool}
    {M : AllocCostModel} {I : MallocngCostModelIface M} {hS : MallocngCostModelSound M I}
    {γ : GhostName} {mmpl : Obj.MultiPlacement} {tp brkStart : BitVec 64}
    {lim : BudgetLimits} {g : CliGhostHooks}
    (hG : CliGhostAllocHooks M (mallocngHookRustCliAllocBudget M I hS γ mmpl tp brkStart) lim g)
    (hOut : lim.enforced = false ∨
      ∀ a, (VerifiedLibraries.mallocngLib.findCodeBlock mmpl a).isSome = true → keep a = true)
    (u v' : State) (hv' : v' = g.dealloc u ∨ v' = stripCodecS keep (g.dealloc u)) :
    ∀ x R,
      u.status = .Running →
      (u.mem ⊨
        (rustCliDeallocBudgetSpec M (strippedMallocngBudget keep M I hS γ mmpl tp brkStart) lim).pre
          x u ∗ R) →
      u.spAligned = true →
      SubroutineOutcome
        (rustCliDeallocBudgetSpec M (strippedMallocngBudget keep M I hS γ mmpl tp brkStart) lim)
        x R u v' := by
  rcases hv' with rfl | rfl
  · exact dealloc_unstripped_to_unstripped hG hOut u
  · exact dealloc_unstripped_to_stripped hG hOut u

theorem realloc_unstripped_of_hOut [LibsignalPlacement]
    {keep : BitVec 64 → Bool}
    {M : AllocCostModel} {I : MallocngCostModelIface M} {hS : MallocngCostModelSound M I}
    {γ : GhostName} {mmpl : Obj.MultiPlacement} {tp brkStart : BitVec 64}
    {lim : BudgetLimits} {g : CliGhostHooks}
    (hG : CliGhostAllocHooks M (mallocngHookRustCliAllocBudget M I hS γ mmpl tp brkStart) lim g)
    (hOut : lim.enforced = false ∨
      ∀ a, (VerifiedLibraries.mallocngLib.findCodeBlock mmpl a).isSome = true → keep a = true)
    (u v' : State) (hv' : v' = g.realloc u ∨ v' = stripCodecS keep (g.realloc u)) :
    ∀ x R,
      u.status = .Running →
      (u.mem ⊨
        (rustCliReallocBudgetSpec M (strippedMallocngBudget keep M I hS γ mmpl tp brkStart) lim).pre
          x u ∗ R) →
      u.spAligned = true →
      SubroutineOutcome
        (rustCliReallocBudgetSpec M (strippedMallocngBudget keep M I hS γ mmpl tp brkStart) lim)
        x R u v' := by
  rcases hv' with rfl | rfl
  · exact realloc_unstripped_to_unstripped hG hOut u
  · exact realloc_unstripped_to_stripped hG hOut u

end
end LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.CodecCalleesFsStepTransportRFd
