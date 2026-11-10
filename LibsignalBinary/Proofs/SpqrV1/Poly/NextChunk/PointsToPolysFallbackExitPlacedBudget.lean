/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Heap.SpecBudget
public import LibsignalBinary.Proofs.SpqrV1.Poly.NextChunk.Block416SegBudget
public meta import LibsignalBinary.Proofs.SpqrV1.Poly.NextChunk.Block416SegBudget -- shake: keep
public import LibsignalBinary.Proofs.SpqrV1.Poly.NextChunk.DefsBudget
public import LibsignalBinary.Proofs.SpqrV1.Poly.NextChunk.EpiloguePlacedBudget
public import LibsignalBinary.Proofs.SpqrV1.Poly.NextChunk.PointsToPolysConst30PlacedBudget
public import LibsignalBinary.Proofs.SpqrV1.Poly.NextChunk.PointsToPolysConst5PlacedBudget
public import LibsignalBinary.Proofs.SpqrV1.Poly.NextChunk.PointsToPolysConstLoopPlacedBudget
public import LibsignalBinary.Proofs.SpqrV1.Poly.NextChunk.PointsToPolysConstLoopPlacedBudgetAux
public import LibsignalBinary.Proofs.SpqrV1.Poly.NextChunk.PointsToPolysConstPlacedBudget
public import LibsignalBinary.Proofs.SpqrV1.Poly.NextChunk.PointsToPolysFallbackExit
public import LibsignalBinary.Proofs.SpqrV1.Poly.NextChunk.PointsToPolysFallbackExitPlaced
public import LibsignalBinary.Proofs.SpqrV1.Poly.NextChunk.PointsToPolysFallbackPlacedBudget
public import LibsignalBinary.Proofs.SpqrV1.Poly.NextChunk.PointsToPolysSetupPlacedBudget
public import LibsignalBinary.Proofs.SpqrV1.Poly.NextChunk.RodataPlacedBudget
public meta import LibsignalBinary.Proofs.Common.SharedHelpers -- shake: keep
import LibsignalBinary.Proofs.Common.SharedHelpers
import LibsignalBinary.Proofs.SpqrV1.Poly.LagrangePrepare.Loop
import LibsignalBinary.Proofs.SpqrV1.Poly.NextChunk.PointsToPolysFallbackLoopPlacedBudget
import LibsignalBinary.Proofs.SpqrV1.Poly.NextChunk.Rodata
import ProofLib.SepLogic.WPp

/-!
# `<PolyEncoder as Encoder>::next_chunk` (Block `416`): Budget-Threaded Placed Fallback Exit and Unified Basis

Relocatable `[LibsignalPlacement]` verification of `lagrangeBasisExit_placed_sepWPp`,
`basis_fallback_placed_sepWPp`, and `basis_pos_placed_sepWPp` (`+1136 -> +2608`) threading
`RustCliAllocBudget M`, `BudgetLimits`, `FallbackBasisExitEnv`, `FallbackBasisEnv`, and
`BasisPosEnv`.
-/

@[expose] public section

set_option autoImplicit false

namespace LibsignalBinary.Proofs.SpqrV1.Poly.NextChunk.PointsToPolysFallbackExitPlacedBudget

open Arm64 ProofLib ProofLib.ProgramReflection SepProp
open CryptoVerification
  (LibsignalCodeLoaded LibsignalHooks LibsignalPlacement blkPC_373 blkPC_416 blkPl_373 blkPl_416
   lsmpl lsρ withLsCodeLoaded)
open scoped CryptoVerification
open scoped CryptoVerification.CodeLayout
open CryptoVerification.RustHeap (allocHookStack)
open CryptoVerification.LibsignalSpqrV1
  (COMPLETE_POINTS_POLYS_1 COMPLETE_POINTS_POLYS_3 COMPLETE_POINTS_POLYS_5
   COMPLETE_POINTS_POLYS_30 COMPLETE_POINTS_POLYS_34 COMPLETE_POINTS_POLYS_36 Pt)
open CryptoVerification.SpqrV1.Alloc (spqrRustAllocSym spqrRustNoAllocShimSym)
open CryptoVerification.SpqrV1.GF.Mul2U16 (tokenInitPlacedAt)
open CryptoVerification.SpqrV1.GF.UnacceleratedMul (reduceTablePlacedAt)
open CryptoVerification.SpqrV1.Poly (polyListOf ptSliceAt)
open CryptoVerification.SpqrV1.Poly.ComputeAt
  (readReg32_setMem_pre readReg64_setMem_pre readReg_setMem_pre sp_setMem_pre spqrRustDeallocSym)
open CryptoVerification.SpqrV1.Poly.LagrangeComplete (lagrangeCompletePlacedSpec)
open CryptoVerification.SpqrV1.Poly.LagrangePrepare
  (lagrangePrepareStack readReg32_setMem_setPC_pre readReg32_setPC_pre
   readReg64_setMem_setPC_pre readReg64_setPC_pre readReg_setMem_setPC_pre readReg_setPC_pre
   sp_setMem_setPC_pre sp_setPC_pre)
open CryptoVerification.SpqrV1.Poly.NextChunk
  (basisVecAt completePointsBasisPure completePointsPolys5PlacedAt
   completePointsPolys30PlacedAt completePointsPolys34PlacedAt completePointsPolys36PlacedAt
   completePointsPolysPlacedAt extractCompletePolys
   lagrangeBasisFrom lagrangeBasisFrom_zero_eq lagrangeBasisPure lagrangeBasisPure_length
   memRegion24_off_eq_polyHeader ofNat_add_one_eq_succ_fb ofNat_succ_add_neg_one_fb
   ofNat_succ_sub_one_fb polyHeader_entails_memRegion24_off ptSliceAt_entails_memRegion
   sepWPp_seq_lscl_fb shl_one_ofNat_eq shl_one_ofNat_eq_nat stackAt_lagrangePrepare_split_alloc
   toOnePts toOnePts_length toOnePts_ne_nil)
open LibsignalBinary.Heap
  (AllocCallPreserved AllocCostModel AllocEvent BudgetLimits FitsEnv FitsEvent FitsEvents
   FreeOnlyEvs RustCliAllocBudget RustLayoutOk SeqEnv fitsEvents_append rustAllocEvents
   rustCliAllocNoOomSpec rustCliDeallocBudgetSpec rustDeallocEvents)
open LibsignalBinary.Heap.SpecBudget (withVmPreserved)
open LibsignalBinary.Proofs.Placed.BudgetPoolSync (hooksException)
open LibsignalBinary.Proofs.SpqrV1.Poly.NextChunk.Block416SegBudget (sepWP_seg_416)
open LibsignalBinary.Proofs.SpqrV1.Poly.NextChunk.DefsBudget
  (FallbackBasisStepEnv LagrangeSumStepEnv PointsToPolysIterEnv RepeatSeqEnv
   fallbackBasisStepEnv_nonempty isPrecomputedBasisLen repeatSeqEnv_nonempty)
open LibsignalBinary.Proofs.SpqrV1.Poly.NextChunk.EpiloguePlacedBudget (AllocContractsPlaced)
open LibsignalBinary.Proofs.SpqrV1.Poly.NextChunk.PointsToPolysConstPlacedBudget
  (BasisN1Env BasisN3Env basisN1Events basisN3Events basis_n1_placed_sepWPp basis_n3_placed_sepWPp)
open LibsignalBinary.Proofs.SpqrV1.Poly.NextChunk.PointsToPolysConst5PlacedBudget
  (BasisN5Env basisN5Events basis_n5_placed_sepWPp)
open LibsignalBinary.Proofs.SpqrV1.Poly.NextChunk.PointsToPolysConst30PlacedBudget
  (BasisN30Env basisN30Events basis_n30_placed_sepWPp)
open LibsignalBinary.Proofs.SpqrV1.Poly.NextChunk.PointsToPolysConstLoopPlacedBudget
  (BasisN34Env basisN34Events basis_n34_placed_sepWPp)
open LibsignalBinary.Proofs.SpqrV1.Poly.NextChunk.PointsToPolysConstLoopPlacedBudgetAux
  (BasisN36Env basisN36Events basis_n36_placed_sepWPp)
open LibsignalBinary.Proofs.SpqrV1.Poly.NextChunk.PointsToPolysFallbackLoopPlacedBudget
  (lagrangeBasisLoop_placed_sepWPp)
open LibsignalBinary.Proofs.SpqrV1.Poly.NextChunk.PointsToPolysFallbackPlacedBudget
  (AllocXsAndBasisEnv allocXsAndBasisEvents allocXsAndBasis_placed_sepWPp
   dispatch_fallback_placed_sepWPp)
open LibsignalBinary.Proofs.SpqrV1.Poly.NextChunk.PointsToPolysSetupPlacedBudget
  (SetupPtVecEnv fitsEnv_setupPtVec_iff setupPtVecEvents)
open LibsignalBinary.Proofs.TripleRatchet.Alloc.DefsBudget (noAllocShimBudgetSpec noAllocShimSpec)

set_option maxRecDepth 200000
set_option maxHeartbeats 400000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

private theorem pc_setMem_pre (s : State) (m : Memory) : (s.setMem m).pc = s.pc := by cases s; rfl
private theorem status_setMem_pre (s : State) (m : Memory) : (s.setMem m).status = s.status := by
  cases s; rfl
private theorem pstate_setMem_pre (s : State) (m : Memory) : (s.setMem m).pstate = s.pstate := by
  cases s; rfl
private theorem trace_setMem_pre (s : State) (m : Memory) : (s.setMem m).trace = s.trace := by
  cases s; rfl
private theorem fs_setMem_pre (s : State) (m : Memory) : (s.setMem m).fs = s.fs := by cases s; rfl
private theorem sigActions_setMem_pre (s : State) (m : Memory) :
    (s.setMem m).sigActions = s.sigActions := by cases s; rfl
private theorem tpidrEl0_setMem_pre (s : State) (m : Memory) :
    (s.setMem m).tpidrEl0 = s.tpidrEl0 := by cases s; rfl
private theorem brkStart_setMem_pre (s : State) (m : Memory) :
    (s.setMem m).brkStart = s.brkStart := by cases s; rfl
private theorem oracle_setMem_pre (s : State) (m : Memory) :
    (s.setMem m).oracle = s.oracle := by cases s; rfl
private theorem symtab_setMem_pre (s : State) (m : Memory) :
    (s.setMem m).symtab = s.symtab := by cases s; rfl
private theorem calleeSavedVRegs_setMem_pre (s : State) (m : Memory) :
    calleeSavedVRegs (s.setMem m) = calleeSavedVRegs s := by cases s; rfl

attribute [local irreducible] Program.fetch Program.externAt? Program.fnOff
attribute [local arm64_norm, local wp_norm] bv_sub_add_lit BitVec.toNat_zero
attribute [local arm64_norm ↓, local wp_norm ↓]
  sp_setMem_pre pc_setMem_pre status_setMem_pre pstate_setMem_pre trace_setMem_pre
  fs_setMem_pre sigActions_setMem_pre tpidrEl0_setMem_pre brkStart_setMem_pre
  oracle_setMem_pre symtab_setMem_pre calleeSavedVRegs_setMem_pre
  readReg64_setMem_pre readReg32_setMem_pre readReg_setMem_pre
  sp_setPC_pre sp_setMem_setPC_pre
  readReg64_setPC_pre readReg64_setMem_setPC_pre
  readReg32_setPC_pre readReg32_setMem_setPC_pre
  readReg_setPC_pre readReg_setMem_setPC_pre

@[local arm64_norm, local wp_norm] private theorem exists_pow_two_eq_two_fbe_bud :
    (∃ k : Nat, 2 = 2 ^ k) ↔ True :=
  iff_true_intro ⟨1, rfl⟩

@[local arm64_norm, local wp_norm] private theorem exists_pow_two_eq_eight_fbe_bud :
    (∃ k : Nat, 8 = 2 ^ k) ↔ True :=
  iff_true_intro ⟨3, rfl⟩

attribute [local simp, local arm64_norm, local wp_norm]
  ofNat_succ_sub_one_fb ofNat_succ_add_neg_one_fb ofNat_add_one_eq_succ_fb
  shl_one_ofNat_eq shl_one_ofNat_eq_nat

attribute [local simp, local arm64_norm ↓, local wp_norm ↓]
  conditionHolds_mi_subsPState64 conditionHolds_pl_subsPState64
  conditionHolds_eq_addsPState64 conditionHolds_ne_addsPState64

/-! ## 1. Allocator Event Envelopes and `PointsToPolysIterEnv` Bridges -/

/-- Exact allocator event sequence of the precomputed constant basis paths (`n ∈ {1, 3, 5, 30, 34, 36}`,
    `+1136..+2608`): `24 * k` bytes (align `8`) for `basisPtr`, `k` polynomial buffers of `2 * k`
    bytes (align `2`), and `2 * k` bytes (align `2`) for `accPtr`. -/
def constBasisEvents (k : Nat) : List AllocEvent :=
  rustAllocEvents (24 * k) 8 ++ (List.replicate (k + 1) (rustAllocEvents (2 * k) 2)).flatten

theorem constBasisEvents_1 : constBasisEvents 1 = basisN1Events := rfl
theorem constBasisEvents_3 : constBasisEvents 3 = basisN3Events := rfl
theorem constBasisEvents_5 : constBasisEvents 5 = basisN5Events := rfl
theorem constBasisEvents_30 : constBasisEvents 30 = basisN30Events := rfl
theorem constBasisEvents_34 : constBasisEvents 34 = basisN34Events := rfl
theorem constBasisEvents_36 : constBasisEvents 36 = basisN36Events := rfl

/-- Event envelope of `lagrangeBasisExit_placed_sepWPp` (`+4116..+2608`, Block `416`):
    `k` `FallbackBasisStepEnv k` iterations (including `xsPtr` deallocation absorbed into the
    trailing `FreeOnlyEvs`), followed by `accPtr` allocation (`2 * k` bytes, align `2`). -/
def FallbackBasisExitEnv (k : Nat) : List AllocEvent → Prop :=
  SeqEnv (RepeatSeqEnv k (FallbackBasisStepEnv k))
    (SeqEnv (· = rustAllocEvents (2 * k) 2) FreeOnlyEvs)

/-- Event envelope of `basis_fallback_placed_sepWPp` (`+1136..+2608`, Block `416`). -/
def FallbackBasisEnv (k : Nat) : List AllocEvent → Prop :=
  SeqEnv (AllocXsAndBasisEnv k) (FallbackBasisExitEnv k)

/-- Unified event envelope of `basis_pos_placed_sepWPp` (`+1136..+2608`, Block `416`) for `k > 0`. -/
def BasisPosEnv (k : Nat) (evs : List AllocEvent) : Prop :=
  if isPrecomputedBasisLen k then
    evs = constBasisEvents k
  else
    FallbackBasisEnv k evs

theorem fallbackBasisExitEnv_nonempty (k : Nat) : ∃ evs, FallbackBasisExitEnv k evs := by
  rcases repeatSeqEnv_nonempty (fallbackBasisStepEnv_nonempty k) k with ⟨el, hel⟩
  exact ⟨el ++ rustAllocEvents (2 * k) 2, SeqEnv.append hel (SeqEnv.inl rfl)⟩

theorem fallbackBasisEnv_nonempty (k : Nat) : ∃ evs, FallbackBasisEnv k evs := by
  rcases fallbackBasisExitEnv_nonempty k with ⟨ee, hee⟩
  exact ⟨allocXsAndBasisEvents k ++ ee, SeqEnv.append rfl hee⟩

theorem basisPosEnv_nonempty (k : Nat) : ∃ evs, BasisPosEnv k evs := by
  unfold BasisPosEnv
  split
  · exact ⟨constBasisEvents k, rfl⟩
  · exact fallbackBasisEnv_nonempty k

example : ∃ evs, FallbackBasisExitEnv 8 evs := fallbackBasisExitEnv_nonempty 8
example : ∃ evs, FallbackBasisEnv 8 evs := fallbackBasisEnv_nonempty 8
example : ∃ evs, BasisPosEnv 1 evs := basisPosEnv_nonempty 1
example : ∃ evs, BasisPosEnv 8 evs := basisPosEnv_nonempty 8

/-- `FallbackBasisStepEnv k` is closed on the right under appending `FreeOnlyEvs`. -/
theorem fallbackBasisStepEnv_append_freeOnly {k : Nat} {evs d : List AllocEvent}
    (h : FallbackBasisStepEnv k evs) (hd : FreeOnlyEvs d) :
    FallbackBasisStepEnv k (evs ++ d) := by
  rcases h with rfl | ⟨e1, e2, rfl, he1, he2⟩
  · exact SeqEnv.append rfl hd
  · rw [List.append_assoc]
    exact SeqEnv.append he1 (he2.append hd)

/-- `RepeatSeqEnv (n + 1) (FallbackBasisStepEnv k)` is closed on the right under appending
    `FreeOnlyEvs` (`__rust_dealloc` of `xsPtr` after the last loop step). -/
theorem repeatSeqEnv_fallbackBasisStep_append_freeOnly :
    ∀ {n k : Nat} {evs d : List AllocEvent},
      RepeatSeqEnv (n + 1) (FallbackBasisStepEnv k) evs →
      FreeOnlyEvs d →
      RepeatSeqEnv (n + 1) (FallbackBasisStepEnv k) (evs ++ d)
  | 0, _, _, _, Or.inl h, hd =>
    Or.inl (fallbackBasisStepEnv_append_freeOnly h hd)
  | 0, _, _, _, Or.inr ⟨_, _, rfl, h1, rfl⟩, hd => by
    rw [List.append_nil]
    exact Or.inl (fallbackBasisStepEnv_append_freeOnly h1 hd)
  | _ + 1, _, _, _, Or.inl h, hd =>
    Or.inl (fallbackBasisStepEnv_append_freeOnly h hd)
  | _ + 1, _, _, _, Or.inr ⟨_, _, rfl, h1, h2⟩, hd => by
    rw [List.append_assoc]
    exact SeqEnv.append h1 (repeatSeqEnv_fallbackBasisStep_append_freeOnly h2 hd)

/-- Project `SetupPtVecEnv k` admissibility from `PointsToPolysIterEnv k` when `k ≠ 0`. -/
theorem fitsEnv_setupPtVec_of_pointsToPolysIter {M : AllocCostModel} {lim : BudgetLimits}
    {st : M.σ} {k : Nat} (hk : k ≠ 0) (hfit : FitsEnv M lim st (PointsToPolysIterEnv k)) :
    FitsEnv M lim st (SetupPtVecEnv k) := by
  rw [fitsEnv_setupPtVec_iff]
  simp only [setupPtVecEvents, hk, ↓reduceIte]
  by_cases hpre : isPrecomputedBasisLen k
  · have hall : FitsEvents M lim st
        (rustAllocEvents (4 * k) 2 ++ rustAllocEvents (24 * k) 8 ++
          (List.replicate (k + 1) (rustAllocEvents (2 * k) 2)).flatten) :=
      hfit _ (by simp [PointsToPolysIterEnv, hk, hpre]; exact Or.inl rfl)
    rw [List.append_assoc] at hall
    exact ((fitsEvents_append M lim _ _ st).mp hall).1
  · have hall : FitsEvents M lim st
        (rustAllocEvents (4 * k) 2 ++ rustAllocEvents (4 * k) 2 ++ rustAllocEvents (24 * k) 8) :=
      hfit _ (by simp [PointsToPolysIterEnv, hk, hpre]; exact Or.inl rfl)
    rw [List.append_assoc] at hall
    exact ((fitsEvents_append M lim _ _ st).mp hall).1

/-- Project `BasisPosEnv k` admissibility after `setupPtVecEvents k` from `PointsToPolysIterEnv k`
    when `k ≠ 0`. -/
theorem fitsEnv_basisPos_of_pointsToPolysIter {M : AllocCostModel} {lim : BudgetLimits}
    {st : M.σ} {k : Nat} (hk : k ≠ 0) (hfit : FitsEnv M lim st (PointsToPolysIterEnv k)) :
    FitsEnv M lim (M.stepEvents (setupPtVecEvents k) st) (BasisPosEnv k) := by
  intro evs hevs
  have hsetup : setupPtVecEvents k = rustAllocEvents (4 * k) 2 := by
    simp [setupPtVecEvents, hk]
  rw [hsetup]
  unfold BasisPosEnv at hevs
  by_cases hpre : isPrecomputedBasisLen k
  · simp only [hpre, ↓reduceIte] at hevs
    subst hevs
    have hall : FitsEvents M lim st
        (rustAllocEvents (4 * k) 2 ++ rustAllocEvents (24 * k) 8 ++
          (List.replicate (k + 1) (rustAllocEvents (2 * k) 2)).flatten) :=
      hfit _ (by simp [PointsToPolysIterEnv, hk, hpre]; exact Or.inl rfl)
    rw [List.append_assoc] at hall
    exact ((fitsEvents_append M lim (rustAllocEvents (4 * k) 2) (constBasisEvents k) st).mp hall).2
  · simp only [hpre, Bool.false_eq_true, ↓reduceIte] at hevs
    rcases hevs with rfl | ⟨e1, e2, rfl, rfl, he2⟩
    · have hall : FitsEvents M lim st
          (rustAllocEvents (4 * k) 2 ++ rustAllocEvents (4 * k) 2 ++ rustAllocEvents (24 * k) 8) :=
        hfit _ (by simp [PointsToPolysIterEnv, hk, hpre]; exact Or.inl rfl)
      rw [List.append_assoc] at hall
      exact ((fitsEvents_append M lim (rustAllocEvents (4 * k) 2)
        (allocXsAndBasisEvents k) st).mp hall).2
    · have he2_lift :
          SeqEnv (RepeatSeqEnv k (FallbackBasisStepEnv k))
            (SeqEnv (SeqEnv (· = rustAllocEvents (2 * k) 2) FreeOnlyEvs)
              (SeqEnv (RepeatSeqEnv k (LagrangeSumStepEnv k)) FreeOnlyEvs)) e2 := by
        rcases he2 with hloop | ⟨el, ex, rfl, hloop, hex⟩
        · exact Or.inl hloop
        · exact SeqEnv.append hloop (Or.inl hex)
      have hiter :
          FitsEvents M lim st
            ((rustAllocEvents (4 * k) 2 ++ rustAllocEvents (4 * k) 2 ++
              rustAllocEvents (24 * k) 8) ++ e2) :=
        hfit _ (by
          simp only [PointsToPolysIterEnv, hk, hpre, Bool.false_eq_true, ↓reduceIte]
          exact SeqEnv.append rfl he2_lift)
      have hassoc :
          (rustAllocEvents (4 * k) 2 ++ rustAllocEvents (4 * k) 2 ++
            rustAllocEvents (24 * k) 8) ++ e2 =
          rustAllocEvents (4 * k) 2 ++ (allocXsAndBasisEvents k ++ e2) := by
        simp [allocXsAndBasisEvents, List.append_assoc]
      rw [hassoc] at hiter
      exact ((fitsEvents_append M lim (rustAllocEvents (4 * k) 2)
        (allocXsAndBasisEvents k ++ e2) st).mp hiter).2

/-- Project the post-`basis_pos` `LagrangeSum` + cleanup tail `FitsEnv` from `PointsToPolysIterEnv k`
    using the normal-return tail-extension witness delivered by `basis_pos_placed_sepWPp`. -/
theorem fitsEnv_lagrangeSumTail_of_pointsToPolysIter {M : AllocCostModel} {lim : BudgetLimits}
    {st : M.σ} {k : Nat} {evs : List AllocEvent}
    (hfit : FitsEnv M lim st (PointsToPolysIterEnv k))
    (hext : ∀ evs_tail,
      SeqEnv (RepeatSeqEnv k (LagrangeSumStepEnv k)) FreeOnlyEvs evs_tail →
      PointsToPolysIterEnv k ((setupPtVecEvents k ++ evs) ++ evs_tail)) :
    FitsEnv M lim (M.stepEvents evs (M.stepEvents (setupPtVecEvents k) st))
      (SeqEnv (RepeatSeqEnv k (LagrangeSumStepEnv k)) FreeOnlyEvs) := by
  intro evs_tail htail
  rw [← M.stepEvents_append]
  exact ((fitsEvents_append M lim (setupPtVecEvents k ++ evs) evs_tail st).mp
    (hfit _ (hext evs_tail htail))).2

/-! ## 2. `LibsignalCodeLoaded`-Preserving CPS & Segment Helpers -/

private theorem sepWPp_seg_lscl_416 [LibsignalPlacement] {H : LibsignalHooks}
    {mid ret : BitVec 64} {s : State} {Pre : SepProp}
    {Q Qp : State → SepProp → Prop}
    (hcl : LibsignalCodeLoaded lsmpl s.mem)
    (hseg : ∀ m_strip : Memory,
      SepWP ((blkPC_416).rebase (blkPl_416).base (hooksException H)) mid (s.setMem m_strip) Pre
        (fun sm' Pm =>
          ∀ m_real : Memory,
            ProofLib.NonSyscallPreserved s (sm'.setMem m_real) →
            LibsignalCodeLoaded lsmpl m_real →
            SepWPp ((blkPC_416).rebase (blkPl_416).base H) ret (sm'.setMem m_real) Pm Q Qp)) :
    SepWPp ((blkPC_416).rebase (blkPl_416).base H) ret s Pre Q Qp := by
  apply sepWPp_seq_lscl_fb hcl (mid := mid)
  apply sepWP_seg_416 (mid := mid) (target := mid)
  intro m_strip
  refine SepWP.seq (hseg m_strip) fun sm' Pm hpc hrun hcont => ?_
  refine SepWP.done hpc hrun fun m_real hnsp => ?_
  exact SepWP.done (by cases sm'; exact hpc) (by cases sm'; exact hrun)
    fun hcl' => hcont m_real hnsp (by cases sm'; exact hcl')

private def s0WithLr (s0 : State) (mid : BitVec 64) : State :=
  s0.writeReg64 (Reg.gpr 30#5) mid

private theorem s0WithLr_trace (s0 : State) (mid : BitVec 64) :
    (s0WithLr s0 mid).trace = s0.trace := rfl

private theorem s0WithLr_lr (s0 : State) (mid : BitVec 64) :
    (s0WithLr s0 mid).readReg64 (Reg.gpr 30#5) = mid := by
  simp [s0WithLr, arm64_norm, wp_norm]

private theorem sepWPp_bind_lscl [LibsignalPlacement] {prog : Program} {mid ret : BitVec 64}
    {s : State} {P : SepProp} {Q Qp : State → SepProp → Prop}
    (hcl : LibsignalCodeLoaded lsmpl s.mem)
    (h : SepWPp prog mid s P
      (fun sm Pm => LibsignalCodeLoaded lsmpl sm.mem → SepWPp prog ret sm Pm Q Qp) Qp) :
    SepWPp prog ret s P Q Qp := by
  intro R hm hL
  obtain ⟨sm, hsteps, ⟨_, _, Pm, hmm, hcont⟩ | hpan_or_oom⟩ := h R hm hL
  · obtain ⟨sf, hsteps', hout⟩ :=
      hcont (hcl.of_keepsFrozen hsteps.keepsFrozen) R hmm (hsteps.codeLoaded hL)
    exact ⟨sf, hsteps.trans hsteps', hout⟩
  · exact ⟨sm, hsteps, Or.inr hpan_or_oom⟩

private theorem sepWPp_cut_s0WithLr [LibsignalPlacement]
    {ext : String → Option (State → State)}
    {Q Q_panic : State → SepProp → Prop}
    {s0 s : State} {mid : BitVec 64} {P : SepProp}
    (hcl : LibsignalCodeLoaded lsmpl s.mem)
    (h : SepWPp ((blkPC_416).rebase (blkPl_416).base (Rust.withPanics ext))
      ((s0WithLr s0 mid).readReg64 (Reg.gpr 30#5)) s P
      (fun sm Pm => LibsignalCodeLoaded lsmpl sm.mem →
        SepWPp ((blkPC_416).rebase (blkPl_416).base (Rust.withPanics ext))
          (s0.readReg64 (Reg.gpr 30#5)) sm Pm Q Q_panic)
      Q_panic) :
    SepWPp ((blkPC_416).rebase (blkPl_416).base (Rust.withPanics ext))
      (s0.readReg64 (Reg.gpr 30#5)) s P Q Q_panic := by
  rw [s0WithLr_lr] at h
  exact sepWPp_bind_lscl hcl h

private theorem sepWPp_done_s0WithLr [LibsignalPlacement]
    {ext : String → Option (State → State)}
    {Q Q_panic : State → SepProp → Prop}
    {s0 s1 : State} {mid : BitVec 64} {P1 : SepProp}
    (hpc1 : s1.pc = mid) (hrun1 : s1.status = .Running)
    (hcont : LibsignalCodeLoaded lsmpl s1.mem →
      SepWPp ((blkPC_416).rebase (blkPl_416).base (Rust.withPanics ext))
        (s0.readReg64 (Reg.gpr 30#5)) s1 P1 Q Q_panic) :
    SepWPp ((blkPC_416).rebase (blkPl_416).base (Rust.withPanics ext))
      ((s0WithLr s0 mid).readReg64 (Reg.gpr 30#5)) s1 P1
      (fun sm Pm => LibsignalCodeLoaded lsmpl sm.mem →
        SepWPp ((blkPC_416).rebase (blkPl_416).base (Rust.withPanics ext))
          (s0.readReg64 (Reg.gpr 30#5)) sm Pm Q Q_panic)
      Q_panic :=
  SepWPp.done (by rw [s0WithLr_lr]; exact hpc1) hrun1 hcont

/-! ## 3. Dynamic Lagrange Basis Loop Entry/Exit (`+4116 -> +2608`, Block `416`) -/

/-- `+4116 -> +2608`: budget-threaded execution of `lagrangeBasisLoop_placed_sepWPp` on
    `toOnePts pts`, deallocating `xsPtr` (`4 * pts.length`, align `2`) and allocating `accPtr`
    (`2 * pts.length`, align `2`) under `FallbackBasisExitEnv pts.length`. -/
theorem lagrangeBasisExit_placed_sepWPp [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits} {st : M.σ}
    {ext : String → Option (State → State)}
    {Q Q_panic : State → SepProp → Prop}
    (hA : AllocContractsPlaced M A lim ext)
    (hcomp_ok : subroutine_ok ((blkPC_373).rebase (blkPl_373).base (Rust.withPanics ext))
      (blkPl_373).base (withLsCodeLoaded lsmpl (withVmPreserved lagrangeCompletePlacedSpec)))
    (pts : List Pt) (hpts_ne : pts ≠ []) (hbound : pts.length ≤ 0x0555555555555555)
    (s0 s : State) (hcl : LibsignalCodeLoaded lsmpl s.mem)
    (fsp ptVecPtr xsPtr basisPtr : BitVec 64)
    (hfsp_align : (fsp &&& 15#64 == 0#64) = true)
    (hxs_ne : xsPtr ≠ 0#64) (hbasis_ne : basisPtr ≠ 0#64)
    (u72 u216 u224 u1040 u1048 u1056 : BitVec 64) (Frame R : SepProp)
    (hpc : s.pc = (blkPl_416).base + 4116#64)
    (hrun : s.status = .Running) (hsp : s.sp = fsp) (htrace : s.trace = s0.trace)
    (hx20 : s.readReg64 .x20 = xsPtr)
    (hx21 : s.readReg64 .x21 = basisPtr)
    (hx24 : s.readReg64 .x24 = BitVec.ofNat 64 (4 * pts.length))
    (hx29 : s.readReg64 .x29 = fsp + 1104#64)
    (hfit : FitsEnv M lim st (FallbackBasisExitEnv pts.length))
    (hcont : ∀ (evs : List AllocEvent) s1 accPtr u216' u224' u1040' u1048' u1056',
      FallbackBasisExitEnv pts.length evs →
      (∀ (Tail : List AllocEvent → Prop) (evs_tail : List AllocEvent),
        Tail evs_tail →
        SeqEnv (RepeatSeqEnv pts.length (FallbackBasisStepEnv pts.length))
          (SeqEnv (SeqEnv (· = rustAllocEvents (2 * pts.length) 2) FreeOnlyEvs) Tail)
          (evs ++ evs_tail)) →
      LibsignalCodeLoaded lsmpl s1.mem →
      accPtr ≠ 0#64 →
      s1.pc = (blkPl_416).base + 2608#64 →
      s1.status = .Running → s1.sp = fsp → s1.trace = s0.trace →
      calleeSavedVRegs s1 = calleeSavedVRegs s →
      s1.readReg64 .x0 = accPtr →
      s1.readReg64 .x20 = s.readReg64 .x25 →
      s1.readReg64 .x24 = basisPtr →
      s1.readReg64 .x25 = BitVec.ofNat 64 pts.length →
      s1.readReg64 .x26 = ptVecPtr →
      s1.readReg64 .x27 = s.readReg64 .x27 →
      s1.readReg64 .x28 = s.readReg64 .x28 →
      s1.readReg64 .x29 = fsp + 1104#64 →
      SepWPp ((blkPC_416).rebase (blkPl_416).base (Rust.withPanics ext))
        (s0.readReg64 (Reg.gpr 30#5)) s1
        (A.pool lim (M.stepEvents evs st) s1 ∗
         basisVecAt A.repAlloc basisPtr (lagrangeBasisPure (toOnePts pts)) ∗
         A.live accPtr (2 * pts.length) 2 ∗ memRegion accPtr (2 * pts.length) ∗
         ((fsp + 72#64) ↦₆₄ basisPtr) ∗ ((fsp + 80#64) ↦₆₄ ptVecPtr) ∗
         ((fsp + 96#64) ↦₆₄ BitVec.ofNat 64 pts.length) ∗
         ((fsp + 216#64) ↦₆₄ u216') ∗ ((fsp + 224#64) ↦₆₄ u224') ∗
         memRegion (fsp + 656#64) 24 ∗
         ((fsp + 1040#64) ↦₆₄ u1040') ∗ ((fsp + 1048#64) ↦₆₄ u1048') ∗
         ((fsp + 1056#64) ↦₆₄ u1056') ∗
         reduceTablePlacedAt ∗ tokenInitPlacedAt ∗ stackAt fsp lagrangePrepareStack ∗ Frame)
        Q Q_panic) :
    SepWPp ((blkPC_416).rebase (blkPl_416).base (Rust.withPanics ext))
      (s0.readReg64 (Reg.gpr 30#5)) s
      (A.pool lim st s ∗
       A.live xsPtr (4 * pts.length) 2 ∗ ptSliceAt xsPtr (toOnePts pts) ∗
       A.live basisPtr (24 * pts.length) 8 ∗ memRegion basisPtr (24 * pts.length) ∗
       ((fsp + 72#64) ↦₆₄ u72) ∗ ((fsp + 80#64) ↦₆₄ ptVecPtr) ∗
       ((fsp + 96#64) ↦₆₄ BitVec.ofNat 64 pts.length) ∗
       ((fsp + 216#64) ↦₆₄ u216) ∗ ((fsp + 224#64) ↦₆₄ u224) ∗
       memRegion (fsp + 656#64) 24 ∗
       ((fsp + 1040#64) ↦₆₄ u1040) ∗ ((fsp + 1048#64) ↦₆₄ u1048) ∗
       ((fsp + 1056#64) ↦₆₄ u1056) ∗
       reduceTablePlacedAt ∗ tokenInitPlacedAt ∗ stackAt fsp lagrangePrepareStack ∗ Frame)
      Q Q_panic := by
  have hn_pos : 0 < pts.length := List.length_pos_iff.mpr hpts_ne
  have hpos_sub : pts.length - 1 + 1 = pts.length := by omega
  have hones_ne : toOnePts pts ≠ [] := toOnePts_ne_nil hpts_ne
  have hones_len : (toOnePts pts).length = pts.length := toOnePts_length pts
  have hones_bound : (toOnePts pts).length ≤ 0x0555555555555555 := by rw [hones_len]; exact hbound
  have hsum : 0 + ((toOnePts pts).length - 1 + 1) = (toOnePts pts).length := by
    rw [hones_len]; omega
  have h24_eq : 24 * ((toOnePts pts).length - 1 + 1) = 24 * (toOnePts pts).length := by
    rw [hones_len]; omega
  have hfit_loop : FitsEnv M lim st (RepeatSeqEnv pts.length (FallbackBasisStepEnv pts.length)) :=
    hfit.seq_left
  have hshim := hA.noAllocShim_ok
  dsimp only [noAllocShimSpec, noAllocShimBudgetSpec] at hshim
  have halloc := hA.allocNoOom_ok
  dsimp only [rustCliAllocNoOomSpec] at halloc
  have hdealloc := hA.dealloc_ok
  dsimp only [rustCliDeallocBudgetSpec] at hdealloc
  try dsimp only [BitVec.ofNat_eq_ofNat] at hpc hshim halloc hdealloc hcont ⊢
  apply sepWPp_seg_lscl_416 hcl (mid := (blkPl_416).base + 4128#64)
  intro _m_strip0
  wp_steps
  refine SepWP.done (by wp_norm_goal) (by wp_norm_lhs) fun _m_real0 _hnsp0 hcl0 => ?_
  refine SepWPp.transport_budgetPool
    (_hnsp0.toVmPreserved (by simp only [arm64_norm, wp_norm]))
    (hnext := ?_)
  simp only [State.setMem_setMem]
  rw [← hones_len, ← h24_eq]
  refine SepWPp.weaken_pre (Entails.of_eq (by sep_ac_rfl))
    (lagrangeBasisLoop_placed_sepWPp hA hcomp_ok ((toOnePts pts).length - 1) 0 (toOnePts pts)
      hones_ne hones_bound hsum
      s0 _ hcl0 fsp xsPtr basisPtr hfsp_align u216 u224 u1040 u1048 u1056
      (A.live xsPtr (4 * (toOnePts pts).length) 2 ∗
       A.live basisPtr (24 * (((toOnePts pts).length - 1) + 1)) 8 ∗
       ((fsp + 72#64) ↦₆₄ basisPtr) ∗ ((fsp + 80#64) ↦₆₄ ptVecPtr) ∗ Frame) R
      (by wp_norm_goal)
      (by wp_norm_lhs)
      (by simp only [arm64_norm, wp_norm, hsp])
      (by simp only [arm64_norm, wp_norm, htrace])
      (by wp_norm_lhs)
      (by simp only [arm64_norm, wp_norm, hx20])
      (by simp only [arm64_norm, wp_norm, hx21])
      (by rw [hones_len]; wp_norm_lhs)
      (by simp only [arm64_norm, wp_norm, hx29])
      (by rw [hones_len, hpos_sub]; exact hfit_loop) ?_)
  intro evs_loop s1 u216' u224' u1040' u1048' u1056' hevs_loop hcl1
    hpc1 hrun1 hsp1 htr1 hvregs1 hx20_1 hx22_1 hx24_1 hx25_1 hx27_1 hx28_1 hx29_1
  clear hA
  have hfrom_eq : lagrangeBasisFrom (toOnePts pts) 0 (((toOnePts pts).length - 1) + 1) =
      lagrangeBasisPure (toOnePts pts) := by
    rw [show ((toOnePts pts).length - 1) + 1 = (toOnePts pts).length by rw [hones_len]; omega]
    exact lagrangeBasisFrom_zero_eq (toOnePts pts)
  rw [hfrom_eq, h24_eq, hones_len]
  rw [hones_len] at hx22_1
  rw [hones_len, hpos_sub] at hevs_loop
  simp only [arm64_norm, wp_norm] at hvregs1 hx24_1 hx25_1 hx27_1 hx28_1
  rw [hx24] at hx24_1
  let evs_lf := evs_loop ++ rustDeallocEvents (4 * pts.length) 2
  have hevs_lf : RepeatSeqEnv pts.length (FallbackBasisStepEnv pts.length) evs_lf := by
    have hloop_sub :
        RepeatSeqEnv ((pts.length - 1) + 1) (FallbackBasisStepEnv pts.length) evs_loop := by
      rwa [hpos_sub]
    have hlf_sub :
        RepeatSeqEnv ((pts.length - 1) + 1) (FallbackBasisStepEnv pts.length) evs_lf :=
      repeatSeqEnv_fallbackBasisStep_append_freeOnly hloop_sub
        (FreeOnlyEvs.singleton 2 (4 * pts.length))
    rwa [hpos_sub] at hlf_sub
  have hfit_acc : FitsEvents M lim (M.stepEvents evs_lf st) (rustAllocEvents (2 * pts.length) 2) :=
    (hfit.seq_right hevs_lf).seq_left _ rfl
  have hfit_acc_ev : FitsEvent M lim (M.stepEvents evs_lf st) (.alloc (2 * pts.length)) := by
    have hle2n : 2 ≤ 2 * pts.length := by omega
    simpa [rustAllocEvents, hle2n] using hfit_acc
  rcases hfit_acc_ev with ⟨_hwmax_acc, henf_acc, hram_acc, hva_acc⟩
  have hlayout2 : RustLayoutOk (2 * pts.length) 2 := ⟨⟨by omega, ⟨1, rfl⟩, by omega⟩, by decide⟩
  have h4n_toNat : (BitVec.ofNat 64 (4 * pts.length)).toNat = 4 * pts.length :=
    Nat.mod_eq_of_lt (by omega)
  have h2n_toNat : (BitVec.ofNat 64 (2 * pts.length)).toNat = 2 * pts.length :=
    Nat.mod_eq_of_lt (by omega)
  have h2_toNat : (2#64 : BitVec 64).toNat = 2 := rfl
  have hxs_mem : ptSliceAt xsPtr (toOnePts pts) ⊢ memRegion xsPtr (4 * pts.length) := by
    rw [← hones_len]
    exact ptSliceAt_entails_memRegion xsPtr (toOnePts pts) hones_bound
  have hsp72_al : ((fsp + 72#64) &&& 7#64 == 0#64) = true := by
    revert hfsp_align; bv_bits
  rw [stackAt_lagrangePrepare_split_alloc fsp]
  apply sepWPp_seq_lscl_fb hcl1 (mid := (blkPl_416).base + 4416#64)
  apply SepWP.fold hxs_mem (by sep_frame)
  wp_steps_sync_416 (lsρ spqrRustDeallocSym)
  simp only [State.setMem_setMem]
  wp_call hdealloc (xsPtr, 4 * pts.length, 2, M.stepEvents evs_loop st)
  clear hdealloc
  have hsp_sf : sf.sp = fsp := by simp only [arm64_norm, wp_norm, hsp1, *]
  have htr_sf : sf.trace = s0.trace := by
    have ht := (by assumption : AllocCallPreserved _ sf).2.1
    simp only [arm64_norm, wp_norm, htr1, *] at ht
    exact ht
  have hvregs_sf : calleeSavedVRegs sf = calleeSavedVRegs s := by
    simp only [arm64_norm, wp_norm, hvregs1, *]
  have hx22_sf : sf.readReg64 (Reg.gpr 22#5) = BitVec.ofNat 64 pts.length := by
    simp only [arm64_norm, wp_norm, Reg.x22, hx22_1, *]
  have hx25_sf : sf.readReg64 (Reg.gpr 25#5) = s.readReg64 .x25 := by
    simp only [arm64_norm, wp_norm, Reg.x25, hx25_1, *]
  have hx27_sf : sf.readReg64 (Reg.gpr 27#5) = s.readReg64 .x27 := by
    simp only [arm64_norm, wp_norm, Reg.x27, hx27_1, *]
  have hx28_sf : sf.readReg64 (Reg.gpr 28#5) = s.readReg64 .x28 := by
    simp only [arm64_norm, wp_norm, Reg.x28, hx28_1, *]
  have hx29_sf : sf.readReg64 (Reg.gpr 29#5) = fsp + 1104#64 := by
    simp only [arm64_norm, wp_norm, Reg.x29, hx29_1, *]
  rw [show M.stepEvents (rustDeallocEvents (4 * pts.length) 2) (M.stepEvents evs_loop st) =
      M.stepEvents evs_lf st from
    (M.stepEvents_append evs_loop (rustDeallocEvents (4 * pts.length) 2) st).symm]
  wp_steps_sync_416 (lsρ spqrRustNoAllocShimSym)
  simp only [State.setMem_setMem]
  wp_call hshim ()
  clear hshim
  have hsp_sf1 : sf_1.sp = fsp := by simp only [arm64_norm, wp_norm, hsp_sf, *]
  have htr_sf1 : sf_1.trace = s0.trace := by simp only [arm64_norm, wp_norm, htr_sf, *]
  have hvregs_sf1 : calleeSavedVRegs sf_1 = calleeSavedVRegs s := by
    simp only [arm64_norm, wp_norm, hvregs_sf, *]
  have hx20_sf1 : sf_1.readReg64 (Reg.gpr 20#5) = s.readReg64 .x25 := by
    simp only [arm64_norm, wp_norm, Reg.x20, Reg.x25, hx25_sf, *]
  have hx22_sf1 : sf_1.readReg64 (Reg.gpr 22#5) = BitVec.ofNat 64 pts.length := by
    simp only [arm64_norm, wp_norm, Reg.x22, hx22_sf, *]
  have hx24_sf1 : sf_1.readReg64 (Reg.gpr 24#5) = basisPtr := by
    simp only [arm64_norm, wp_norm, Reg.x24, *]
  have hx25_sf1 : sf_1.readReg64 (Reg.gpr 25#5) = BitVec.ofNat 64 pts.length := by
    simp only [arm64_norm, wp_norm, Reg.x25, Reg.x22, hx22_sf, *]
  have hx26_sf1 : sf_1.readReg64 (Reg.gpr 26#5) = ptVecPtr := by
    simp only [arm64_norm, wp_norm, Reg.x26, *]
  have hx27_sf1 : sf_1.readReg64 (Reg.gpr 27#5) = s.readReg64 .x27 := by
    simp only [arm64_norm, wp_norm, Reg.x27, hx27_sf, *]
  have hx28_sf1 : sf_1.readReg64 (Reg.gpr 28#5) = s.readReg64 .x28 := by
    simp only [arm64_norm, wp_norm, Reg.x28, hx28_sf, *]
  have hx29_sf1 : sf_1.readReg64 (Reg.gpr 29#5) = fsp + 1104#64 := by
    simp only [arm64_norm, wp_norm, Reg.x29, hx29_sf, *]
  refine SepWP.transport_budgetPool (by assumption) (hnext := ?_)
  wp_steps_sync_416 (lsρ spqrRustAllocSym)
  simp only [State.setMem_setMem]
  wp_call halloc (2 * pts.length, 2, M.stepEvents evs_lf st)
  clear halloc
  have hoom : sf_2.readReg64 (Reg.gpr 0#5) ≠ 0#64 := by assumption
  have hbeq_oom : (sf_2.readReg64 (Reg.gpr 0#5) == 0#64) = false := beq_eq_false_iff_ne.mpr hoom
  have hcond_oom : ¬(sf_2.readReg64 (Reg.gpr 0#5) == 0#64) = true := by
    simpa [beq_iff_eq] using hoom
  have hcond_ne : (sf_2.readReg64 (Reg.gpr 0#5) != 0#64) = true := by
    simpa [bne_iff_ne] using hoom
  have hsp_sf2 : sf_2.sp = fsp := by simp only [arm64_norm, wp_norm, hsp_sf1, *]
  have htr_sf2 : sf_2.trace = s0.trace := by
    have ht := (by assumption : AllocCallPreserved _ sf_2).2.1
    simp only [arm64_norm, wp_norm, htr_sf1, *] at ht
    exact ht
  have hvregs_sf2 : calleeSavedVRegs sf_2 = calleeSavedVRegs s := by
    simp only [arm64_norm, wp_norm, hvregs_sf1, *]
  have hx20_sf2 : sf_2.readReg64 (Reg.gpr 20#5) = s.readReg64 .x25 := by
    simp only [arm64_norm, wp_norm, Reg.x20, hx20_sf1, *]
  have hx24_sf2 : sf_2.readReg64 (Reg.gpr 24#5) = basisPtr := by
    simp only [arm64_norm, wp_norm, Reg.x24, hx24_sf1, *]
  have hx25_sf2 : sf_2.readReg64 (Reg.gpr 25#5) = BitVec.ofNat 64 pts.length := by
    simp only [arm64_norm, wp_norm, Reg.x25, hx25_sf1, *]
  have hx26_sf2 : sf_2.readReg64 (Reg.gpr 26#5) = ptVecPtr := by
    simp only [arm64_norm, wp_norm, Reg.x26, hx26_sf1, *]
  have hx27_sf2 : sf_2.readReg64 (Reg.gpr 27#5) = s.readReg64 .x27 := by
    simp only [arm64_norm, wp_norm, Reg.x27, hx27_sf1, *]
  have hx28_sf2 : sf_2.readReg64 (Reg.gpr 28#5) = s.readReg64 .x28 := by
    simp only [arm64_norm, wp_norm, Reg.x28, hx28_sf1, *]
  have hx29_sf2 : sf_2.readReg64 (Reg.gpr 29#5) = fsp + 1104#64 := by
    simp only [arm64_norm, wp_norm, Reg.x29, hx29_sf1, *]
  refine SepWP.done hpc_sf_2 hrun_sf_2 ?_
  intro hcl2
  apply sepWPp_seg_lscl_416 hcl2 (mid := (blkPl_416).base + 2608#64)
  intro _m_strip3
  wp_steps
  refine SepWP.done
    (by simp only [arm64_norm, wp_norm, hbeq_oom, hcond_ne, hcond_oom, Bool.false_eq_true, ↓reduceIte])
    (by wp_norm_lhs)
    fun _m_real3 _hnsp3 hcl3 => ?_
  refine SepWPp.transport_budgetPool
    (_hnsp3.toVmPreserved
      (by simp only [arm64_norm, wp_norm, hbeq_oom, hcond_ne, hcond_oom, Bool.false_eq_true, ↓reduceIte]))
    (hnext := ?_)
  simp only [State.setMem_setMem]
  let evs_exit := evs_lf ++ rustAllocEvents (2 * pts.length) 2
  have hevs_exit : FallbackBasisExitEnv pts.length evs_exit :=
    SeqEnv.append hevs_lf (SeqEnv.inl rfl)
  have hext_exit :
      ∀ (Tail : List AllocEvent → Prop) (evs_tail : List AllocEvent),
        Tail evs_tail →
        SeqEnv (RepeatSeqEnv pts.length (FallbackBasisStepEnv pts.length))
          (SeqEnv (SeqEnv (· = rustAllocEvents (2 * pts.length) 2) FreeOnlyEvs) Tail)
          (evs_exit ++ evs_tail) := by
    intro Tail evs_tail htail
    dsimp only [evs_exit]
    rw [List.append_assoc]
    exact SeqEnv.append hevs_lf (SeqEnv.append (SeqEnv.inl rfl) htail)
  have hstep_exit :
      M.stepEvents (rustAllocEvents (2 * pts.length) 2) (M.stepEvents evs_lf st) =
        M.stepEvents evs_exit st :=
    (M.stepEvents_append evs_lf (rustAllocEvents (2 * pts.length) 2) st).symm
  have hbasis :
      (A.live basisPtr (24 * pts.length) 8 ∗
       polyListOf A.repAlloc basisPtr (lagrangeBasisPure (toOnePts pts))) ⊢
      basisVecAt A.repAlloc basisPtr (lagrangeBasisPure (toOnePts pts)) := by
    unfold basisVecAt
    rw [lagrangeBasisPure_length, hones_len, A.repAlloc_live]
    exact Entails.pure_right hbasis_ne (Entails.refl _)
  refine SepWPp.weaken_pre ?_
    (hcont evs_exit _ (sf_2.readReg64 (Reg.gpr 0#5)) u216' u224' u1040' u1048' u1056'
      hevs_exit hext_exit hcl3 hoom
      (by simp only [arm64_norm, wp_norm, hbeq_oom, hcond_ne, hcond_oom, Bool.false_eq_true, ↓reduceIte])
      (by wp_norm_lhs)
      (by simp only [arm64_norm, wp_norm, hsp_sf2])
      (by simp only [arm64_norm, wp_norm, htr_sf2])
      (by simp only [arm64_norm, wp_norm, hvregs_sf2])
      (by simp only [arm64_norm, wp_norm, Reg.x0])
      (by simp only [arm64_norm, wp_norm, Reg.x20, hx20_sf2])
      (by simp only [arm64_norm, wp_norm, Reg.x24, hx24_sf2])
      (by simp only [arm64_norm, wp_norm, Reg.x25, hx25_sf2])
      (by simp only [arm64_norm, wp_norm, Reg.x26, hx26_sf2])
      (by simp only [arm64_norm, wp_norm, Reg.x27, hx27_sf2])
      (by simp only [arm64_norm, wp_norm, Reg.x28, hx28_sf2])
      (by simp only [arm64_norm, wp_norm, Reg.x29, hx29_sf2]))
  simp only [arm64_norm, wp_norm, hstep_exit, hbeq_oom, Bool.false_eq_true, ↓reduceIte,
    h2n_toNat, hsp_sf2, hsp_sf1, hsp_sf, hsp1, hx22_sf1, hx24_sf1, *]
  rw [stackAt_lagrangePrepare_split_alloc fsp,
      show BitVec.ofNat 64 lagrangePrepareStack = 4304#64 from rfl]
  refine Entails.trans (Entails.of_eq (show _ =
    (A.live basisPtr (24 * pts.length) 8 ∗
     polyListOf A.repAlloc basisPtr (lagrangeBasisPure (toOnePts pts))) ∗
    (A.pool lim (M.stepEvents evs_exit st) _ ∗
     A.live (sf_2.readReg64 (Reg.gpr 0#5)) (2 * pts.length) 2 ∗
     memRegion (sf_2.readReg64 (Reg.gpr 0#5)) (2 * pts.length) ∗
     ((fsp + 72#64) ↦₆₄ basisPtr) ∗ ((fsp + 80#64) ↦₆₄ ptVecPtr) ∗
     ((fsp + 96#64) ↦₆₄ BitVec.ofNat 64 pts.length) ∗
     ((fsp + 216#64) ↦₆₄ u216') ∗ ((fsp + 224#64) ↦₆₄ u224') ∗
     memRegion (fsp + 656#64) 24 ∗
     ((fsp + 1040#64) ↦₆₄ u1040') ∗ ((fsp + 1048#64) ↦₆₄ u1048') ∗
     ((fsp + 1056#64) ↦₆₄ u1056') ∗
     reduceTablePlacedAt ∗ tokenInitPlacedAt ∗
     stackAt fsp allocHookStack ∗
     memRegion (fsp - 4304#64) (lagrangePrepareStack - allocHookStack) ∗
     Frame) by sep_ac_rfl)) ?_
  refine Entails.trans (sepConj_mono_left hbasis) ?_
  exact Entails.of_eq (by sep_ac_rfl)

/-! ## 4. Full Dynamic Lagrange Fallback (`+1136 -> +2608`, Block `416`) -/

/-- Full dynamic Lagrange fallback (`+1136 -> +1804 -> +4116 -> +2608`) for
    `pts.length ∉ {0, 1, 3, 5, 30, 34, 36}` under `FallbackBasisEnv pts.length`. -/
theorem basis_fallback_placed_sepWPp [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits} {st : M.σ}
    {ext : String → Option (State → State)}
    {Q Q_panic : State → SepProp → Prop}
    (hA : AllocContractsPlaced M A lim ext)
    (hcomp_ok : subroutine_ok ((blkPC_373).rebase (blkPl_373).base (Rust.withPanics ext))
      (blkPl_373).base (withLsCodeLoaded lsmpl (withVmPreserved lagrangeCompletePlacedSpec)))
    (pts : List Pt) (hpts_ne : pts ≠ [])
    (hn1 : pts.length ≠ 1) (hn3 : pts.length ≠ 3) (hn5 : pts.length ≠ 5)
    (hn30 : pts.length ≠ 30) (hn34 : pts.length ≠ 34) (hn36 : pts.length ≠ 36)
    (hbound : pts.length ≤ 0x0555555555555555)
    (s0 s : State) (hcl : LibsignalCodeLoaded lsmpl s.mem)
    (fsp ptVecPtr : BitVec 64)
    (hfsp_align : (fsp &&& 15#64 == 0#64) = true)
    (u24 u72 u80 u96 u216 u224 u1040 u1048 u1056 : BitVec 64) (Frame R : SepProp)
    (hpc : s.pc = (blkPl_416).base + 1136#64)
    (hrun : s.status = .Running) (hsp : s.sp = fsp) (htrace : s.trace = s0.trace)
    (hx24 : s.readReg64 .x24 = BitVec.ofNat 64 (4 * pts.length))
    (hx25 : s.readReg64 .x25 = BitVec.ofNat 64 pts.length)
    (hx26 : s.readReg64 .x26 = ptVecPtr)
    (hx29 : s.readReg64 .x29 = fsp + 1104#64)
    (hfit : FitsEnv M lim st (FallbackBasisEnv pts.length))
    (hcont : ∀ (evs : List AllocEvent) s1 basisPtr accPtr u72' u80' u216' u224' u1040' u1048' u1056',
      FallbackBasisEnv pts.length evs →
      (∀ evs_tail,
        SeqEnv (RepeatSeqEnv pts.length (LagrangeSumStepEnv pts.length)) FreeOnlyEvs evs_tail →
        PointsToPolysIterEnv pts.length ((setupPtVecEvents pts.length ++ evs) ++ evs_tail)) →
      LibsignalCodeLoaded lsmpl s1.mem →
      basisPtr ≠ 0#64 →
      accPtr ≠ 0#64 →
      s1.pc = (blkPl_416).base + 2608#64 →
      s1.status = .Running → s1.sp = fsp → s1.trace = s0.trace →
      calleeSavedVRegs s1 = calleeSavedVRegs s →
      s1.readReg64 .x0 = accPtr →
      s1.readReg64 .x20 = s.readReg64 .x20 →
      s1.readReg64 .x24 = basisPtr →
      s1.readReg64 .x25 = BitVec.ofNat 64 pts.length →
      s1.readReg64 .x26 = ptVecPtr →
      s1.readReg64 .x27 = s.readReg64 .x27 →
      s1.readReg64 .x28 = s.readReg64 .x28 →
      s1.readReg64 .x29 = fsp + 1104#64 →
      SepWPp ((blkPC_416).rebase (blkPl_416).base (Rust.withPanics ext))
        (s0.readReg64 (Reg.gpr 30#5)) s1
        (A.pool lim (M.stepEvents evs st) s1 ∗ ptSliceAt ptVecPtr pts ∗
         basisVecAt A.repAlloc basisPtr (lagrangeBasisPure (toOnePts pts)) ∗
         A.live accPtr (2 * pts.length) 2 ∗ memRegion accPtr (2 * pts.length) ∗
         ((fsp + 24#64) ↦₆₄ BitVec.ofNat 64 pts.length) ∗
         ((fsp + 72#64) ↦₆₄ u72') ∗ ((fsp + 80#64) ↦₆₄ u80') ∗
         ((fsp + 96#64) ↦₆₄ BitVec.ofNat 64 pts.length) ∗
         ((fsp + 216#64) ↦₆₄ u216') ∗ ((fsp + 224#64) ↦₆₄ u224') ∗
         memRegion (fsp + 656#64) 24 ∗
         ((fsp + 1040#64) ↦₆₄ u1040') ∗ ((fsp + 1048#64) ↦₆₄ u1048') ∗
         ((fsp + 1056#64) ↦₆₄ u1056') ∗
         reduceTablePlacedAt ∗ tokenInitPlacedAt ∗ stackAt fsp lagrangePrepareStack ∗ Frame)
        Q Q_panic) :
    SepWPp ((blkPC_416).rebase (blkPl_416).base (Rust.withPanics ext))
      (s0.readReg64 (Reg.gpr 30#5)) s
      (A.pool lim st s ∗ ptSliceAt ptVecPtr pts ∗
       ((fsp + 24#64) ↦₆₄ u24) ∗
       ((fsp + 72#64) ↦₆₄ u72) ∗ ((fsp + 80#64) ↦₆₄ u80) ∗
       ((fsp + 96#64) ↦₆₄ u96) ∗
       ((fsp + 216#64) ↦₆₄ u216) ∗ ((fsp + 224#64) ↦₆₄ u224) ∗
       memRegion (fsp + 656#64) 24 ∗
       ((fsp + 1040#64) ↦₆₄ u1040) ∗ ((fsp + 1048#64) ↦₆₄ u1048) ∗
       ((fsp + 1056#64) ↦₆₄ u1056) ∗
       reduceTablePlacedAt ∗ tokenInitPlacedAt ∗ stackAt fsp lagrangePrepareStack ∗ Frame)
      Q Q_panic := by
  have hn0 : pts.length ≠ 0 := by intro h0; exact hpts_ne (List.eq_nil_of_length_eq_zero h0)
  have hfit_alloc : FitsEnv M lim st (AllocXsAndBasisEnv pts.length) := hfit.seq_left
  have hfit_exit :
      FitsEnv M lim (M.stepEvents (allocXsAndBasisEvents pts.length) st)
        (FallbackBasisExitEnv pts.length) :=
    hfit.seq_right rfl
  apply sepWPp_cut_s0WithLr hcl (mid := (blkPl_416).base + 1804#64)
  refine SepWPp.weaken_pre (Entails.of_eq (by sep_ac_rfl))
    (dispatch_fallback_placed_sepWPp (M := M) (A := A) (lim := lim) (st := st)
      (s0WithLr s0 ((blkPl_416).base + 1804#64)) s fsp hfsp_align
      pts.length hn0 hn1 hn3 hn5 hn30 hn34 hn36 hbound u96
      (ptSliceAt ptVecPtr pts ∗
       ((fsp + 24#64) ↦₆₄ u24) ∗ ((fsp + 72#64) ↦₆₄ u72) ∗ ((fsp + 80#64) ↦₆₄ u80) ∗
       ((fsp + 216#64) ↦₆₄ u216) ∗ ((fsp + 224#64) ↦₆₄ u224) ∗
       memRegion (fsp + 656#64) 24 ∗
       ((fsp + 1040#64) ↦₆₄ u1040) ∗ ((fsp + 1048#64) ↦₆₄ u1048) ∗
       ((fsp + 1056#64) ↦₆₄ u1056) ∗
       reduceTablePlacedAt ∗ tokenInitPlacedAt ∗ stackAt fsp lagrangePrepareStack ∗ Frame) R
      hpc hrun hsp htrace hx25 ?_)
  intro s1 hpc1 hrun1 hsp1 htr1 hvregs1 hx19_1 hx20_1 hx24_1 hx25_1 hx26_1 hx27_1 hx28_1 hx29_1
  apply sepWPp_done_s0WithLr hpc1 hrun1; intro hcl1
  rw [s0WithLr_trace] at htr1
  rw [stackAt_lagrangePrepare_split_alloc fsp]
  apply sepWPp_cut_s0WithLr hcl1 (mid := (blkPl_416).base + 4116#64)
  refine SepWPp.weaken_pre (Entails.of_eq (by sep_ac_rfl))
    (allocXsAndBasis_placed_sepWPp hA (s0WithLr s0 ((blkPl_416).base + 4116#64)) s1
      fsp ptVecPtr hfsp_align pts hpts_ne hbound u24 u80
      (memRegion (fsp - BitVec.ofNat 64 lagrangePrepareStack)
         (lagrangePrepareStack - allocHookStack) ∗
       ((fsp + 72#64) ↦₆₄ u72) ∗
       ((fsp + 216#64) ↦₆₄ u216) ∗ ((fsp + 224#64) ↦₆₄ u224) ∗
       memRegion (fsp + 656#64) 24 ∗
       ((fsp + 1040#64) ↦₆₄ u1040) ∗ ((fsp + 1048#64) ↦₆₄ u1048) ∗
       ((fsp + 1056#64) ↦₆₄ u1056) ∗
       reduceTablePlacedAt ∗ tokenInitPlacedAt ∗ Frame) R
      hpc1 hrun1 hsp1 htr1 hx19_1 (by rw [hx24_1, hx24]) (by rw [hx26_1, hx26]) hfit_alloc ?_)
  intro s2 xsPtr basisPtr hxs_ne hbasis_ne _ hpc2 hrun2 hsp2 htr2 hvregs2
    hx20_2 hx21_2 hx24_2 hx25_2 hx26_2 hx27_2 hx28_2 hx29_2
  apply sepWPp_done_s0WithLr hpc2 hrun2; intro hcl2
  rw [s0WithLr_trace] at htr2
  refine SepWPp.weaken_pre
    (by
      have hst := (stackAt_lagrangePrepare_split_alloc fsp).symm
      refine Entails.trans (Entails.of_eq (show _ =
        (stackAt fsp allocHookStack ∗
         memRegion (fsp - BitVec.ofNat 64 lagrangePrepareStack)
           (lagrangePrepareStack - allocHookStack)) ∗
        (A.pool lim (M.stepEvents (allocXsAndBasisEvents pts.length) st) s2 ∗
         ptSliceAt ptVecPtr pts ∗
         A.live xsPtr (4 * pts.length) 2 ∗ ptSliceAt xsPtr (toOnePts pts) ∗
         A.live basisPtr (24 * pts.length) 8 ∗ memRegion basisPtr (24 * pts.length) ∗
         ((fsp + 24#64) ↦₆₄ BitVec.ofNat 64 pts.length) ∗
         ((fsp + 72#64) ↦₆₄ u72) ∗ ((fsp + 80#64) ↦₆₄ ptVecPtr) ∗
         ((fsp + 96#64) ↦₆₄ BitVec.ofNat 64 pts.length) ∗
         ((fsp + 216#64) ↦₆₄ u216) ∗ ((fsp + 224#64) ↦₆₄ u224) ∗
         memRegion (fsp + 656#64) 24 ∗
         ((fsp + 1040#64) ↦₆₄ u1040) ∗ ((fsp + 1048#64) ↦₆₄ u1048) ∗
         ((fsp + 1056#64) ↦₆₄ u1056) ∗
         reduceTablePlacedAt ∗ tokenInitPlacedAt ∗ Frame) by sep_ac_rfl)) ?_
      rw [← hst]
      exact Entails.of_eq (by sep_ac_rfl))
    (lagrangeBasisExit_placed_sepWPp hA hcomp_ok pts hpts_ne hbound s0 s2 hcl2
      fsp ptVecPtr xsPtr basisPtr hfsp_align hxs_ne hbasis_ne u72 u216 u224 u1040 u1048 u1056
      (ptSliceAt ptVecPtr pts ∗ ((fsp + 24#64) ↦₆₄ BitVec.ofNat 64 pts.length) ∗ Frame) R
      hpc2 hrun2 hsp2 htr2 hx20_2 hx21_2 hx24_2 (by rw [hx29_2, hx29_1, hx29]) hfit_exit ?_)
  intro evs_exit s3 accPtr u216' u224' u1040' u1048' u1056' hevs_exit hext_exit hcl3 hacc_ne
    hpc3 hrun3 hsp3 htr3 hvregs3 hx0_3 hx20_3 hx24_3 hx25_3 hx26_3 hx27_3 hx28_3 hx29_3
  let evs := allocXsAndBasisEvents pts.length ++ evs_exit
  have hevs : FallbackBasisEnv pts.length evs :=
    SeqEnv.append rfl hevs_exit
  have hpre_false : isPrecomputedBasisLen pts.length = false := by
    simp [isPrecomputedBasisLen, hn1, hn3, hn5, hn30, hn34, hn36]
  have hext_iter :
      ∀ evs_tail,
        SeqEnv (RepeatSeqEnv pts.length (LagrangeSumStepEnv pts.length)) FreeOnlyEvs evs_tail →
        PointsToPolysIterEnv pts.length ((setupPtVecEvents pts.length ++ evs) ++ evs_tail) := by
    intro evs_tail htail
    unfold PointsToPolysIterEnv
    simp only [hn0, hpre_false, Bool.false_eq_true, ↓reduceIte]
    have hconcat :
        (setupPtVecEvents pts.length ++ evs) ++ evs_tail =
        (rustAllocEvents (4 * pts.length) 2 ++ rustAllocEvents (4 * pts.length) 2 ++
          rustAllocEvents (24 * pts.length) 8) ++ (evs_exit ++ evs_tail) := by
      simp [setupPtVecEvents, hn0, evs, allocXsAndBasisEvents, List.append_assoc]
    rw [hconcat]
    exact SeqEnv.append rfl (hext_exit _ evs_tail htail)
  have hstep_eq :
      M.stepEvents evs_exit (M.stepEvents (allocXsAndBasisEvents pts.length) st) =
        M.stepEvents evs st :=
    (M.stepEvents_append (allocXsAndBasisEvents pts.length) evs_exit st).symm
  refine SepWPp.weaken_pre
    (by rw [hstep_eq]; exact Entails.of_eq (by sep_ac_rfl))
    (hcont evs s3 basisPtr accPtr basisPtr ptVecPtr u216' u224' u1040' u1048' u1056'
      hevs hext_iter hcl3 hbasis_ne hacc_ne hpc3 hrun3 hsp3 htr3
      (by rw [hvregs3, hvregs2, hvregs1]) hx0_3
      (by rw [hx20_3, hx25_2, hx20_1]) hx24_3 hx25_3 hx26_3
      (by rw [hx27_3, hx27_2, hx27_1]) (by rw [hx28_3, hx28_2, hx28_1]) hx29_3)

/-! ## 5. Unified Basis Construction for `0 < pts.length` (`basis_pos_placed_sepWPp`) -/

private theorem pointsToPolysIterEnv_of_precomputed {k : Nat} (hk0 : k ≠ 0)
    (hpre : isPrecomputedBasisLen k = true) {evs_tail : List AllocEvent}
    (htail : SeqEnv (RepeatSeqEnv k (LagrangeSumStepEnv k)) FreeOnlyEvs evs_tail) :
    PointsToPolysIterEnv k ((setupPtVecEvents k ++ constBasisEvents k) ++ evs_tail) := by
  unfold PointsToPolysIterEnv
  simp only [hk0, hpre, ↓reduceIte]
  have hconcat :
      setupPtVecEvents k ++ constBasisEvents k =
      rustAllocEvents (4 * k) 2 ++ rustAllocEvents (24 * k) 8 ++
        (List.replicate (k + 1) (rustAllocEvents (2 * k) 2)).flatten := by
    simp [setupPtVecEvents, hk0, constBasisEvents, List.append_assoc]
  rw [hconcat]
  exact SeqEnv.append rfl htail

/-- Unified budget-threaded basis construction (`+1136 -> +2608`) for all `pts ≠ []` with
    `pts.length ≤ 0x0555555555555555` under `BasisPosEnv pts.length`. -/
theorem basis_pos_placed_sepWPp [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits} {st : M.σ}
    {ext : String → Option (State → State)}
    {Q Q_panic : State → SepProp → Prop}
    (hA : AllocContractsPlaced M A lim ext)
    (hcomp_ok : subroutine_ok ((blkPC_373).rebase (blkPl_373).base (Rust.withPanics ext))
      (blkPl_373).base (withLsCodeLoaded lsmpl (withVmPreserved lagrangeCompletePlacedSpec)))
    (pts : List Pt) (hpts_ne : pts ≠ []) (hbound : pts.length ≤ 0x0555555555555555)
    (s0 s : State) (hcl : LibsignalCodeLoaded lsmpl s.mem)
    (fsp ptVecPtr : BitVec 64)
    (hfsp_align : (fsp &&& 15#64 == 0#64) = true)
    (u24 u72 u80 u96 u216 u224 u1040 u1048 u1056 : BitVec 64) (Frame R : SepProp)
    (hpc : s.pc = (blkPl_416).base + 1136#64)
    (hrun : s.status = .Running) (hsp : s.sp = fsp) (htrace : s.trace = s0.trace)
    (hx24 : s.readReg64 .x24 = BitVec.ofNat 64 (4 * pts.length))
    (hx25 : s.readReg64 .x25 = BitVec.ofNat 64 pts.length)
    (hx26 : s.readReg64 .x26 = ptVecPtr)
    (hx29 : s.readReg64 .x29 = fsp + 1104#64)
    (hfit : FitsEnv M lim st (BasisPosEnv pts.length))
    (hcont : ∀ (evs : List AllocEvent) s1 basisPtr accPtr u72' u80' u216' u224' u1040' u1048' u1056',
      BasisPosEnv pts.length evs →
      (∀ evs_tail,
        SeqEnv (RepeatSeqEnv pts.length (LagrangeSumStepEnv pts.length)) FreeOnlyEvs evs_tail →
        PointsToPolysIterEnv pts.length ((setupPtVecEvents pts.length ++ evs) ++ evs_tail)) →
      LibsignalCodeLoaded lsmpl s1.mem →
      basisPtr ≠ 0#64 →
      accPtr ≠ 0#64 →
      s1.pc = (blkPl_416).base + 2608#64 →
      s1.status = .Running → s1.sp = fsp → s1.trace = s0.trace →
      calleeSavedVRegs s1 = calleeSavedVRegs s →
      s1.readReg64 .x0 = accPtr →
      s1.readReg64 .x20 = s.readReg64 .x20 →
      s1.readReg64 .x24 = basisPtr →
      s1.readReg64 .x25 = BitVec.ofNat 64 pts.length →
      s1.readReg64 .x26 = ptVecPtr →
      s1.readReg64 .x27 = s.readReg64 .x27 →
      s1.readReg64 .x28 = s.readReg64 .x28 →
      s1.readReg64 .x29 = fsp + 1104#64 →
      SepWPp ((blkPC_416).rebase (blkPl_416).base (Rust.withPanics ext))
        (s0.readReg64 (Reg.gpr 30#5)) s1
        (A.pool lim (M.stepEvents evs st) s1 ∗ ptSliceAt ptVecPtr pts ∗
         basisVecAt A.repAlloc basisPtr (completePointsBasisPure pts) ∗
         A.live accPtr (2 * pts.length) 2 ∗ memRegion accPtr (2 * pts.length) ∗
         ((fsp + 24#64) ↦₆₄ BitVec.ofNat 64 pts.length) ∗
         ((fsp + 72#64) ↦₆₄ u72') ∗ ((fsp + 80#64) ↦₆₄ u80') ∗
         ((fsp + 96#64) ↦₆₄ BitVec.ofNat 64 pts.length) ∗
         ((fsp + 216#64) ↦₆₄ u216') ∗ ((fsp + 224#64) ↦₆₄ u224') ∗
         memRegion (fsp + 656#64) 24 ∗
         ((fsp + 1040#64) ↦₆₄ u1040') ∗ ((fsp + 1048#64) ↦₆₄ u1048') ∗
         ((fsp + 1056#64) ↦₆₄ u1056') ∗
         completePointsPolysPlacedAt ∗ reduceTablePlacedAt ∗ tokenInitPlacedAt ∗
         stackAt fsp lagrangePrepareStack ∗ Frame)
        Q Q_panic) :
    SepWPp ((blkPC_416).rebase (blkPl_416).base (Rust.withPanics ext))
      (s0.readReg64 (Reg.gpr 30#5)) s
      (A.pool lim st s ∗ ptSliceAt ptVecPtr pts ∗
       ((fsp + 24#64) ↦₆₄ u24) ∗
       ((fsp + 72#64) ↦₆₄ u72) ∗ ((fsp + 80#64) ↦₆₄ u80) ∗
       ((fsp + 96#64) ↦₆₄ u96) ∗
       ((fsp + 216#64) ↦₆₄ u216) ∗ ((fsp + 224#64) ↦₆₄ u224) ∗
       memRegion (fsp + 656#64) 24 ∗
       ((fsp + 1040#64) ↦₆₄ u1040) ∗ ((fsp + 1048#64) ↦₆₄ u1048) ∗
       ((fsp + 1056#64) ↦₆₄ u1056) ∗
       completePointsPolysPlacedAt ∗ reduceTablePlacedAt ∗ tokenInitPlacedAt ∗
       stackAt fsp lagrangePrepareStack ∗ Frame)
      Q Q_panic := by
  by_cases hn1 : pts.length = 1
  · have hbasis_eq : completePointsBasisPure pts = extractCompletePolys COMPLETE_POINTS_POLYS_1 := by
      unfold completePointsBasisPure; simp [hn1]
    have hfit1 : FitsEnv M lim st BasisN1Env := by
      intro evs hevs
      apply hfit evs
      simp [BasisPosEnv, hn1, isPrecomputedBasisLen, constBasisEvents_1, BasisN1Env] at hevs ⊢
      exact hevs
    rw [stackAt_lagrangePrepare_split_alloc fsp]
    apply sepWPp_cut_s0WithLr hcl (mid := (blkPl_416).base + 2608#64)
    refine SepWPp.weaken_pre (Entails.of_eq (by sep_ac_rfl))
      (basis_n1_placed_sepWPp hA (s0WithLr s0 ((blkPl_416).base + 2608#64)) s fsp hfsp_align u24 u96
        (memRegion (fsp - BitVec.ofNat 64 lagrangePrepareStack)
           (lagrangePrepareStack - allocHookStack) ∗
         ptSliceAt ptVecPtr pts ∗
         ((fsp + 72#64) ↦₆₄ u72) ∗ ((fsp + 80#64) ↦₆₄ u80) ∗
         ((fsp + 216#64) ↦₆₄ u216) ∗ ((fsp + 224#64) ↦₆₄ u224) ∗
         memRegion (fsp + 656#64) 24 ∗
         ((fsp + 1040#64) ↦₆₄ u1040) ∗ ((fsp + 1048#64) ↦₆₄ u1048) ∗
         ((fsp + 1056#64) ↦₆₄ u1056) ∗
         completePointsPolysPlacedAt ∗ reduceTablePlacedAt ∗ tokenInitPlacedAt ∗ Frame) R
        hpc hrun hsp htrace (by rw [hx25, hn1]) hfit1 ?_)
    intro s1 basisPtr accPtr hbasis_ne hacc_ne hpc1 hrun1 hsp1 htr1 hvregs1
      hx0_1 hx20_1 hx24_1 hx25_1 hx26_1 hx27_1 hx28_1 hx29_1
    apply sepWPp_done_s0WithLr hpc1 hrun1; intro hcl1
    rw [s0WithLr_trace] at htr1
    have hevs1 : BasisPosEnv pts.length basisN1Events := by
      simp [BasisPosEnv, hn1, isPrecomputedBasisLen, constBasisEvents_1]
    have hext1 :
        ∀ evs_tail,
          SeqEnv (RepeatSeqEnv pts.length (LagrangeSumStepEnv pts.length)) FreeOnlyEvs evs_tail →
          PointsToPolysIterEnv pts.length ((setupPtVecEvents pts.length ++ basisN1Events) ++ evs_tail) := by
      intro evs_tail htail
      rw [hn1, ← constBasisEvents_1]
      exact pointsToPolysIterEnv_of_precomputed (by decide) rfl (by simpa [hn1] using htail)
    refine SepWPp.weaken_pre
      (by
        rw [hbasis_eq, hn1, stackAt_lagrangePrepare_split_alloc fsp]
        exact Entails.of_eq (by sep_ac_rfl))
      (hcont basisN1Events s1 basisPtr accPtr u72 u80 u216 u224 u1040 u1048 u1056
        hevs1 hext1 hcl1 hbasis_ne hacc_ne hpc1 hrun1 hsp1 htr1 hvregs1 hx0_1 hx20_1 hx24_1
        (by rw [hx25_1, hn1]) (by rw [hx26_1, hx26]) hx27_1 hx28_1 (by rw [hx29_1, hx29]))
  · by_cases hn3 : pts.length = 3
    · have hbasis_eq : completePointsBasisPure pts = extractCompletePolys COMPLETE_POINTS_POLYS_3 := by
        unfold completePointsBasisPure; simp [hn3]
      have hfit3 : FitsEnv M lim st BasisN3Env := by
        intro evs hevs
        apply hfit evs
        simp [BasisPosEnv, hn3, isPrecomputedBasisLen, constBasisEvents_3, BasisN3Env] at hevs ⊢
        exact hevs
      rw [stackAt_lagrangePrepare_split_alloc fsp]
      apply sepWPp_cut_s0WithLr hcl (mid := (blkPl_416).base + 2608#64)
      refine SepWPp.weaken_pre (Entails.of_eq (by sep_ac_rfl))
        (basis_n3_placed_sepWPp hA (s0WithLr s0 ((blkPl_416).base + 2608#64)) s fsp hfsp_align u24 u96
          (memRegion (fsp - BitVec.ofNat 64 lagrangePrepareStack)
             (lagrangePrepareStack - allocHookStack) ∗
           ptSliceAt ptVecPtr pts ∗
           ((fsp + 72#64) ↦₆₄ u72) ∗ ((fsp + 80#64) ↦₆₄ u80) ∗
           ((fsp + 216#64) ↦₆₄ u216) ∗ ((fsp + 224#64) ↦₆₄ u224) ∗
           memRegion (fsp + 656#64) 24 ∗
           ((fsp + 1040#64) ↦₆₄ u1040) ∗ ((fsp + 1048#64) ↦₆₄ u1048) ∗
           ((fsp + 1056#64) ↦₆₄ u1056) ∗
           completePointsPolysPlacedAt ∗ reduceTablePlacedAt ∗ tokenInitPlacedAt ∗ Frame) R
          hpc hrun hsp htrace (by rw [hx25, hn3]) hfit3 ?_)
      intro s1 basisPtr accPtr hbasis_ne hacc_ne hpc1 hrun1 hsp1 htr1 hvregs1
        hx0_1 hx20_1 hx24_1 hx25_1 hx26_1 hx27_1 hx28_1 hx29_1
      apply sepWPp_done_s0WithLr hpc1 hrun1; intro hcl1
      rw [s0WithLr_trace] at htr1
      have hevs3 : BasisPosEnv pts.length basisN3Events := by
        simp [BasisPosEnv, hn3, isPrecomputedBasisLen, constBasisEvents_3]
      have hext3 :
          ∀ evs_tail,
            SeqEnv (RepeatSeqEnv pts.length (LagrangeSumStepEnv pts.length)) FreeOnlyEvs evs_tail →
            PointsToPolysIterEnv pts.length ((setupPtVecEvents pts.length ++ basisN3Events) ++ evs_tail) := by
        intro evs_tail htail
        rw [hn3, ← constBasisEvents_3]
        exact pointsToPolysIterEnv_of_precomputed (by decide) rfl (by simpa [hn3] using htail)
      refine SepWPp.weaken_pre
        (by
          rw [hbasis_eq, hn3, stackAt_lagrangePrepare_split_alloc fsp]
          exact Entails.of_eq (by sep_ac_rfl))
        (hcont basisN3Events s1 basisPtr accPtr u72 u80 u216 u224 u1040 u1048 u1056
          hevs3 hext3 hcl1 hbasis_ne hacc_ne hpc1 hrun1 hsp1 htr1 hvregs1 hx0_1 hx20_1 hx24_1
          (by rw [hx25_1, hn3]) (by rw [hx26_1, hx26]) hx27_1 hx28_1 (by rw [hx29_1, hx29]))
    · by_cases hn5 : pts.length = 5
      · have hbasis_eq : completePointsBasisPure pts = extractCompletePolys COMPLETE_POINTS_POLYS_5 := by
          unfold completePointsBasisPure; simp [hn5]
        have hfit5 : FitsEnv M lim st BasisN5Env := by
          intro evs hevs
          apply hfit evs
          simp [BasisPosEnv, hn5, isPrecomputedBasisLen, constBasisEvents_5, BasisN5Env] at hevs ⊢
          exact hevs
        unfold completePointsPolysPlacedAt
        rw [stackAt_lagrangePrepare_split_alloc fsp]
        apply sepWPp_cut_s0WithLr hcl (mid := (blkPl_416).base + 2608#64)
        refine SepWPp.weaken_pre (Entails.of_eq (by sep_ac_rfl))
          (basis_n5_placed_sepWPp hA (s0WithLr s0 ((blkPl_416).base + 2608#64)) s fsp hfsp_align u24 u96
            (memRegion (fsp - BitVec.ofNat 64 lagrangePrepareStack)
               (lagrangePrepareStack - allocHookStack) ∗
             ptSliceAt ptVecPtr pts ∗
             ((fsp + 72#64) ↦₆₄ u72) ∗ ((fsp + 80#64) ↦₆₄ u80) ∗
             ((fsp + 216#64) ↦₆₄ u216) ∗ ((fsp + 224#64) ↦₆₄ u224) ∗
             memRegion (fsp + 656#64) 24 ∗
             ((fsp + 1040#64) ↦₆₄ u1040) ∗ ((fsp + 1048#64) ↦₆₄ u1048) ∗
             ((fsp + 1056#64) ↦₆₄ u1056) ∗
             completePointsPolys30PlacedAt ∗ completePointsPolys34PlacedAt ∗
             completePointsPolys36PlacedAt ∗
             reduceTablePlacedAt ∗ tokenInitPlacedAt ∗ Frame) R
            hpc hrun hsp htrace (by rw [hx25, hn5]) hfit5 ?_)
        intro s1 basisPtr accPtr hbasis_ne hacc_ne hpc1 hrun1 hsp1 htr1 hvregs1
          hx0_1 hx20_1 hx24_1 hx25_1 hx26_1 hx27_1 hx28_1 hx29_1
        apply sepWPp_done_s0WithLr hpc1 hrun1; intro hcl1
        rw [s0WithLr_trace] at htr1
        have hevs5 : BasisPosEnv pts.length basisN5Events := by
          simp [BasisPosEnv, hn5, isPrecomputedBasisLen, constBasisEvents_5]
        have hext5 :
            ∀ evs_tail,
              SeqEnv (RepeatSeqEnv pts.length (LagrangeSumStepEnv pts.length)) FreeOnlyEvs evs_tail →
              PointsToPolysIterEnv pts.length ((setupPtVecEvents pts.length ++ basisN5Events) ++ evs_tail) := by
          intro evs_tail htail
          rw [hn5, ← constBasisEvents_5]
          exact pointsToPolysIterEnv_of_precomputed (by decide) rfl (by simpa [hn5] using htail)
        refine SepWPp.weaken_pre
          (by
            unfold completePointsPolysPlacedAt
            rw [hbasis_eq, hn5, stackAt_lagrangePrepare_split_alloc fsp]
            exact Entails.of_eq (by sep_ac_rfl))
          (hcont basisN5Events s1 basisPtr accPtr u72 u80 u216 u224 u1040 u1048 u1056
            hevs5 hext5 hcl1 hbasis_ne hacc_ne hpc1 hrun1 hsp1 htr1 hvregs1 hx0_1 hx20_1 hx24_1
            (by rw [hx25_1, hn5]) (by rw [hx26_1, hx26]) hx27_1 hx28_1 (by rw [hx29_1, hx29]))
      · by_cases hn30 : pts.length = 30
        · have hbasis_eq : completePointsBasisPure pts = extractCompletePolys COMPLETE_POINTS_POLYS_30 := by
            unfold completePointsBasisPure; simp [hn30]
          have hfit30 : FitsEnv M lim st BasisN30Env := by
            intro evs hevs
            apply hfit evs
            simp [BasisPosEnv, hn30, isPrecomputedBasisLen, constBasisEvents_30, BasisN30Env] at hevs ⊢
            exact hevs
          unfold completePointsPolysPlacedAt
          rw [stackAt_lagrangePrepare_split_alloc fsp, memRegion24_off_eq_polyHeader fsp]
          simp only [sepExists_sepConj_left, sepExists_sepConj_right]
          apply SepWPp.exists_elim; intro u672
          apply SepWPp.exists_elim; intro u664
          apply SepWPp.exists_elim; intro u656
          apply sepWPp_cut_s0WithLr hcl (mid := (blkPl_416).base + 2608#64)
          refine SepWPp.weaken_pre (Entails.of_eq (by sep_ac_rfl))
            (basis_n30_placed_sepWPp hA (s0WithLr s0 ((blkPl_416).base + 2608#64)) s fsp hfsp_align
              u24 u96 u656 u664 u672
              (memRegion (fsp - BitVec.ofNat 64 lagrangePrepareStack)
                 (lagrangePrepareStack - allocHookStack) ∗
               ptSliceAt ptVecPtr pts ∗
               ((fsp + 72#64) ↦₆₄ u72) ∗ ((fsp + 80#64) ↦₆₄ u80) ∗
               ((fsp + 216#64) ↦₆₄ u216) ∗ ((fsp + 224#64) ↦₆₄ u224) ∗
               ((fsp + 1040#64) ↦₆₄ u1040) ∗ ((fsp + 1048#64) ↦₆₄ u1048) ∗
               ((fsp + 1056#64) ↦₆₄ u1056) ∗
               completePointsPolys5PlacedAt ∗ completePointsPolys34PlacedAt ∗
               completePointsPolys36PlacedAt ∗
               reduceTablePlacedAt ∗ tokenInitPlacedAt ∗ Frame) R
              hpc hrun hsp htrace (by rw [hx25, hn30]) hfit30 ?_)
          intro s1 basisPtr accPtr hbasis_ne hacc_ne hpc1 hrun1 hsp1 htr1 hvregs1
            hx0_1 hx20_1 hx24_1 hx25_1 hx26_1 hx27_1 hx28_1 hx29_1
          apply sepWPp_done_s0WithLr hpc1 hrun1; intro hcl1
          rw [s0WithLr_trace] at htr1
          have hevs30 : BasisPosEnv pts.length basisN30Events := by
            simp [BasisPosEnv, hn30, isPrecomputedBasisLen, constBasisEvents_30]
          have hext30 :
              ∀ evs_tail,
                SeqEnv (RepeatSeqEnv pts.length (LagrangeSumStepEnv pts.length)) FreeOnlyEvs evs_tail →
                PointsToPolysIterEnv pts.length ((setupPtVecEvents pts.length ++ basisN30Events) ++ evs_tail) := by
            intro evs_tail htail
            rw [hn30, ← constBasisEvents_30]
            exact pointsToPolysIterEnv_of_precomputed (by decide) rfl (by simpa [hn30] using htail)
          refine SepWPp.weaken_pre
            (by
              unfold completePointsPolysPlacedAt
              rw [hbasis_eq, hn30, stackAt_lagrangePrepare_split_alloc fsp]
              refine Entails.trans (Entails.of_eq (show _ =
                (((fsp + 656#64) ↦₆₄ 30#64) ∗ ((fsp + 664#64) ↦₆₄ basisPtr) ∗
                 ((fsp + 672#64) ↦₆₄ 30#64)) ∗
                (A.pool lim (M.stepEvents basisN30Events st) s1 ∗ ptSliceAt ptVecPtr pts ∗
                 basisVecAt A.repAlloc basisPtr (extractCompletePolys COMPLETE_POINTS_POLYS_30) ∗
                 A.live accPtr 60 2 ∗ memRegion accPtr 60 ∗
                 ((fsp + 24#64) ↦₆₄ 30#64) ∗
                 ((fsp + 72#64) ↦₆₄ u72) ∗ ((fsp + 80#64) ↦₆₄ u80) ∗
                 ((fsp + 96#64) ↦₆₄ 30#64) ∗
                 ((fsp + 216#64) ↦₆₄ u216) ∗ ((fsp + 224#64) ↦₆₄ u224) ∗
                 ((fsp + 1040#64) ↦₆₄ u1040) ∗ ((fsp + 1048#64) ↦₆₄ u1048) ∗
                 ((fsp + 1056#64) ↦₆₄ u1056) ∗
                 (completePointsPolys5PlacedAt ∗ completePointsPolys30PlacedAt ∗
                  completePointsPolys34PlacedAt ∗ completePointsPolys36PlacedAt) ∗
                 reduceTablePlacedAt ∗ tokenInitPlacedAt ∗
                 (stackAt fsp allocHookStack ∗
                  memRegion (fsp - BitVec.ofNat 64 lagrangePrepareStack)
                    (lagrangePrepareStack - allocHookStack)) ∗ Frame) by sep_ac_rfl)) ?_
              refine Entails.trans
                (sepConj_mono_left (polyHeader_entails_memRegion24_off fsp 30#64 basisPtr 30#64)) ?_
              exact Entails.of_eq (by sep_ac_rfl))
            (hcont basisN30Events s1 basisPtr accPtr u72 u80 u216 u224 u1040 u1048 u1056
              hevs30 hext30 hcl1 hbasis_ne hacc_ne hpc1 hrun1 hsp1 htr1 hvregs1 hx0_1 hx20_1 hx24_1
              (by rw [hx25_1, hn30]) (by rw [hx26_1, hx26]) hx27_1 hx28_1 (by rw [hx29_1, hx29]))
        · by_cases hn34 : pts.length = 34
          · have hbasis_eq : completePointsBasisPure pts = extractCompletePolys COMPLETE_POINTS_POLYS_34 := by
              unfold completePointsBasisPure; simp [hn34]
            have hfit34 : FitsEnv M lim st BasisN34Env := by
              intro evs hevs
              apply hfit evs
              simp [BasisPosEnv, hn34, isPrecomputedBasisLen, constBasisEvents_34, BasisN34Env] at hevs ⊢
              exact hevs
            unfold completePointsPolysPlacedAt
            rw [stackAt_lagrangePrepare_split_alloc fsp, memRegion24_off_eq_polyHeader fsp]
            simp only [sepExists_sepConj_left, sepExists_sepConj_right]
            apply SepWPp.exists_elim; intro u672
            apply SepWPp.exists_elim; intro u664
            apply SepWPp.exists_elim; intro u656
            apply sepWPp_cut_s0WithLr hcl (mid := (blkPl_416).base + 2608#64)
            refine SepWPp.weaken_pre (Entails.of_eq (by sep_ac_rfl))
              (basis_n34_placed_sepWPp hA (s0WithLr s0 ((blkPl_416).base + 2608#64)) s fsp hfsp_align
                u24 u96 u656 u664 u672
                (memRegion (fsp - BitVec.ofNat 64 lagrangePrepareStack)
                   (lagrangePrepareStack - allocHookStack) ∗
                 ptSliceAt ptVecPtr pts ∗
                 ((fsp + 72#64) ↦₆₄ u72) ∗ ((fsp + 80#64) ↦₆₄ u80) ∗
                 ((fsp + 216#64) ↦₆₄ u216) ∗ ((fsp + 224#64) ↦₆₄ u224) ∗
                 ((fsp + 1040#64) ↦₆₄ u1040) ∗ ((fsp + 1048#64) ↦₆₄ u1048) ∗
                 ((fsp + 1056#64) ↦₆₄ u1056) ∗
                 completePointsPolys5PlacedAt ∗ completePointsPolys30PlacedAt ∗
                 completePointsPolys36PlacedAt ∗
                 reduceTablePlacedAt ∗ tokenInitPlacedAt ∗ Frame) R
                hpc hrun hsp htrace (by rw [hx25, hn34]) hfit34 ?_)
            intro s1 basisPtr accPtr hbasis_ne hacc_ne hpc1 hrun1 hsp1 htr1 hvregs1
              hx0_1 hx20_1 hx24_1 hx25_1 hx26_1 hx27_1 hx28_1 hx29_1
            apply sepWPp_done_s0WithLr hpc1 hrun1; intro hcl1
            rw [s0WithLr_trace] at htr1
            have hevs34 : BasisPosEnv pts.length basisN34Events := by
              simp [BasisPosEnv, hn34, isPrecomputedBasisLen, constBasisEvents_34]
            have hext34 :
                ∀ evs_tail,
                  SeqEnv (RepeatSeqEnv pts.length (LagrangeSumStepEnv pts.length)) FreeOnlyEvs evs_tail →
                  PointsToPolysIterEnv pts.length ((setupPtVecEvents pts.length ++ basisN34Events) ++ evs_tail) := by
              intro evs_tail htail
              rw [hn34, ← constBasisEvents_34]
              exact pointsToPolysIterEnv_of_precomputed (by decide) rfl (by simpa [hn34] using htail)
            refine SepWPp.weaken_pre
              (by
                unfold completePointsPolysPlacedAt
                rw [hbasis_eq, hn34, stackAt_lagrangePrepare_split_alloc fsp]
                refine Entails.trans (Entails.of_eq (show _ =
                  (((fsp + 656#64) ↦₆₄ 34#64) ∗ ((fsp + 664#64) ↦₆₄ basisPtr) ∗
                   ((fsp + 672#64) ↦₆₄ 34#64)) ∗
                  (A.pool lim (M.stepEvents basisN34Events st) s1 ∗ ptSliceAt ptVecPtr pts ∗
                   basisVecAt A.repAlloc basisPtr (extractCompletePolys COMPLETE_POINTS_POLYS_34) ∗
                   A.live accPtr 68 2 ∗ memRegion accPtr 68 ∗
                   ((fsp + 24#64) ↦₆₄ 34#64) ∗
                   ((fsp + 72#64) ↦₆₄ u72) ∗ ((fsp + 80#64) ↦₆₄ u80) ∗
                   ((fsp + 96#64) ↦₆₄ 34#64) ∗
                   ((fsp + 216#64) ↦₆₄ u216) ∗ ((fsp + 224#64) ↦₆₄ u224) ∗
                   ((fsp + 1040#64) ↦₆₄ u1040) ∗ ((fsp + 1048#64) ↦₆₄ u1048) ∗
                   ((fsp + 1056#64) ↦₆₄ u1056) ∗
                   (completePointsPolys5PlacedAt ∗ completePointsPolys30PlacedAt ∗
                    completePointsPolys34PlacedAt ∗ completePointsPolys36PlacedAt) ∗
                   reduceTablePlacedAt ∗ tokenInitPlacedAt ∗
                   (stackAt fsp allocHookStack ∗
                    memRegion (fsp - BitVec.ofNat 64 lagrangePrepareStack)
                      (lagrangePrepareStack - allocHookStack)) ∗ Frame) by sep_ac_rfl)) ?_
                refine Entails.trans
                  (sepConj_mono_left (polyHeader_entails_memRegion24_off fsp 34#64 basisPtr 34#64)) ?_
                exact Entails.of_eq (by sep_ac_rfl))
              (hcont basisN34Events s1 basisPtr accPtr u72 u80 u216 u224 u1040 u1048 u1056
                hevs34 hext34 hcl1 hbasis_ne hacc_ne hpc1 hrun1 hsp1 htr1 hvregs1 hx0_1 hx20_1 hx24_1
                (by rw [hx25_1, hn34]) (by rw [hx26_1, hx26]) hx27_1 hx28_1 (by rw [hx29_1, hx29]))
          · by_cases hn36 : pts.length = 36
            · have hbasis_eq : completePointsBasisPure pts = extractCompletePolys COMPLETE_POINTS_POLYS_36 := by
                unfold completePointsBasisPure; simp [hn36]
              have hfit36 : FitsEnv M lim st BasisN36Env := by
                intro evs hevs
                apply hfit evs
                simp [BasisPosEnv, hn36, isPrecomputedBasisLen, constBasisEvents_36, BasisN36Env] at hevs ⊢
                exact hevs
              unfold completePointsPolysPlacedAt
              rw [stackAt_lagrangePrepare_split_alloc fsp, memRegion24_off_eq_polyHeader fsp]
              simp only [sepExists_sepConj_left, sepExists_sepConj_right]
              apply SepWPp.exists_elim; intro u672
              apply SepWPp.exists_elim; intro u664
              apply SepWPp.exists_elim; intro u656
              apply sepWPp_cut_s0WithLr hcl (mid := (blkPl_416).base + 2608#64)
              refine SepWPp.weaken_pre (Entails.of_eq (by sep_ac_rfl))
                (basis_n36_placed_sepWPp hA (s0WithLr s0 ((blkPl_416).base + 2608#64)) s fsp hfsp_align
                  u24 u96 u656 u664 u672
                  (memRegion (fsp - BitVec.ofNat 64 lagrangePrepareStack)
                     (lagrangePrepareStack - allocHookStack) ∗
                   ptSliceAt ptVecPtr pts ∗
                   ((fsp + 72#64) ↦₆₄ u72) ∗ ((fsp + 80#64) ↦₆₄ u80) ∗
                   ((fsp + 216#64) ↦₆₄ u216) ∗ ((fsp + 224#64) ↦₆₄ u224) ∗
                   ((fsp + 1040#64) ↦₆₄ u1040) ∗ ((fsp + 1048#64) ↦₆₄ u1048) ∗
                   ((fsp + 1056#64) ↦₆₄ u1056) ∗
                   completePointsPolys5PlacedAt ∗ completePointsPolys30PlacedAt ∗
                   completePointsPolys34PlacedAt ∗
                   reduceTablePlacedAt ∗ tokenInitPlacedAt ∗ Frame) R
                  hpc hrun hsp htrace (by rw [hx25, hn36]) hfit36 ?_)
              intro s1 basisPtr accPtr hbasis_ne hacc_ne hpc1 hrun1 hsp1 htr1 hvregs1
                hx0_1 hx20_1 hx24_1 hx25_1 hx26_1 hx27_1 hx28_1 hx29_1
              apply sepWPp_done_s0WithLr hpc1 hrun1; intro hcl1
              rw [s0WithLr_trace] at htr1
              have hevs36 : BasisPosEnv pts.length basisN36Events := by
                simp [BasisPosEnv, hn36, isPrecomputedBasisLen, constBasisEvents_36]
              have hext36 :
                  ∀ evs_tail,
                    SeqEnv (RepeatSeqEnv pts.length (LagrangeSumStepEnv pts.length)) FreeOnlyEvs evs_tail →
                    PointsToPolysIterEnv pts.length ((setupPtVecEvents pts.length ++ basisN36Events) ++ evs_tail) := by
                intro evs_tail htail
                rw [hn36, ← constBasisEvents_36]
                exact pointsToPolysIterEnv_of_precomputed (by decide) rfl (by simpa [hn36] using htail)
              refine SepWPp.weaken_pre
                (by
                  unfold completePointsPolysPlacedAt
                  rw [hbasis_eq, hn36, stackAt_lagrangePrepare_split_alloc fsp]
                  refine Entails.trans (Entails.of_eq (show _ =
                    (((fsp + 656#64) ↦₆₄ 36#64) ∗ ((fsp + 664#64) ↦₆₄ basisPtr) ∗
                     ((fsp + 672#64) ↦₆₄ 36#64)) ∗
                    (A.pool lim (M.stepEvents basisN36Events st) s1 ∗ ptSliceAt ptVecPtr pts ∗
                     basisVecAt A.repAlloc basisPtr (extractCompletePolys COMPLETE_POINTS_POLYS_36) ∗
                     A.live accPtr 72 2 ∗ memRegion accPtr 72 ∗
                     ((fsp + 24#64) ↦₆₄ 36#64) ∗
                     ((fsp + 72#64) ↦₆₄ u72) ∗ ((fsp + 80#64) ↦₆₄ u80) ∗
                     ((fsp + 96#64) ↦₆₄ 36#64) ∗
                     ((fsp + 216#64) ↦₆₄ u216) ∗ ((fsp + 224#64) ↦₆₄ u224) ∗
                     ((fsp + 1040#64) ↦₆₄ u1040) ∗ ((fsp + 1048#64) ↦₆₄ u1048) ∗
                     ((fsp + 1056#64) ↦₆₄ u1056) ∗
                     (completePointsPolys5PlacedAt ∗ completePointsPolys30PlacedAt ∗
                      completePointsPolys34PlacedAt ∗ completePointsPolys36PlacedAt) ∗
                     reduceTablePlacedAt ∗ tokenInitPlacedAt ∗
                     (stackAt fsp allocHookStack ∗
                      memRegion (fsp - BitVec.ofNat 64 lagrangePrepareStack)
                        (lagrangePrepareStack - allocHookStack)) ∗ Frame) by sep_ac_rfl)) ?_
                  refine Entails.trans
                    (sepConj_mono_left (polyHeader_entails_memRegion24_off fsp 36#64 basisPtr 36#64)) ?_
                  exact Entails.of_eq (by sep_ac_rfl))
                (hcont basisN36Events s1 basisPtr accPtr u72 u80 u216 u224 u1040 u1048 u1056
                  hevs36 hext36 hcl1 hbasis_ne hacc_ne hpc1 hrun1 hsp1 htr1 hvregs1 hx0_1 hx20_1 hx24_1
                  (by rw [hx25_1, hn36]) (by rw [hx26_1, hx26]) hx27_1 hx28_1 (by rw [hx29_1, hx29]))
            · have hn0 : pts.length ≠ 0 := by
                intro h0; exact hpts_ne (List.eq_nil_of_length_eq_zero h0)
              have hbasis_eq : completePointsBasisPure pts = lagrangeBasisPure (toOnePts pts) := by
                unfold completePointsBasisPure; simp [hn0, hn1, hn3, hn5, hn30, hn34, hn36]
              have hpre_false : isPrecomputedBasisLen pts.length = false := by
                simp [isPrecomputedBasisLen, hn1, hn3, hn5, hn30, hn34, hn36]
              have hfit_fb : FitsEnv M lim st (FallbackBasisEnv pts.length) := by
                intro evs hevs
                apply hfit evs
                simp [BasisPosEnv, hpre_false, hevs]
              refine SepWPp.weaken_pre (Entails.of_eq (by sep_ac_rfl))
                (basis_fallback_placed_sepWPp hA hcomp_ok pts hpts_ne hn1 hn3 hn5 hn30 hn34 hn36
                  hbound s0 s hcl fsp ptVecPtr hfsp_align u24 u72 u80 u96 u216 u224 u1040 u1048 u1056
                  (completePointsPolysPlacedAt ∗ Frame) R
                  hpc hrun hsp htrace hx24 hx25 hx26 hx29 hfit_fb ?_)
              intro evs s1 basisPtr accPtr u72' u80' u216' u224' u1040' u1048' u1056'
                hevs_fb hext_fb hcl1 hbasis_ne hacc_ne hpc1 hrun1 hsp1 htr1 hvregs1
                hx0_1 hx20_1 hx24_1 hx25_1 hx26_1 hx27_1 hx28_1 hx29_1
              have hevs_pos : BasisPosEnv pts.length evs := by
                simp [BasisPosEnv, hpre_false, hevs_fb]
              refine SepWPp.weaken_pre
                (by rw [hbasis_eq]; exact Entails.of_eq (by sep_ac_rfl))
                (hcont evs s1 basisPtr accPtr u72' u80' u216' u224' u1040' u1048' u1056'
                  hevs_pos hext_fb hcl1 hbasis_ne hacc_ne hpc1 hrun1 hsp1 htr1 hvregs1
                  hx0_1 hx20_1 hx24_1 hx25_1 hx26_1 hx27_1 hx28_1 hx29_1)

end LibsignalBinary.Proofs.SpqrV1.Poly.NextChunk.PointsToPolysFallbackExitPlacedBudget
