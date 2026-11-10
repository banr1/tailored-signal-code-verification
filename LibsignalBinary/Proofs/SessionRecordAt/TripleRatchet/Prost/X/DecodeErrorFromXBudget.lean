/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Heap.SpecBudget
public import LibsignalBinary.Proofs.Placed.BudgetPoolSync
public meta import LibsignalBinary.Proofs.Placed.BudgetPoolSync -- shake: keep
public import LibsignalBinary.Proofs.Placed.BudgetVmSteps
public meta import LibsignalBinary.Proofs.Placed.BudgetVmSteps -- shake: keep
public import LibsignalBinary.Proofs.SessionRecordAt.Stage1X.GrowOneXBudget
public import LibsignalBinary.Proofs.SessionRecordAt.TripleRatchet.Wire.X.CalleesWBudget
public import LibsignalBinary.Proofs.SessionRecordAt.TripleRatchet.Prost.X.DecodeErrorFromX
import LibsignalBinary.Proofs.Common.SharedHelpers
meta import LibsignalBinary.Proofs.Common.SharedHelpers -- shake: keep
import LibsignalBinary.Proofs.TripleRatchet.InImage.DecodeErrorFrom.Core
import ProofLib.SepLogic.WPp

/-!
# Budget-Threaded `<DecodeError as From<DecodeErrorKind>>::from`

Proves `DecodeErrorFromPlacedOkW A lim H` (block `261`) under `RustCliAllocBudget M` and
`FitsEnv M lim st DecodeErrorFromEnv` from `AllocContractsPlaced M A lim H`.
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 2000000

namespace LibsignalBinary.Proofs.SessionRecordAt.TripleRatchet.Prost.X.DecodeErrorFromXBudget

open Arm64 ProofLib SepProp
open CryptoVerification (
  LibsignalPlacement LibsignalHooks lsmpl withLsCodeLoaded
  lsρ lsRustAllocSym lsRustNoAllocShimSym sepWP_seq_lscl
  blkPC_261 blkPl_261
)
open CryptoVerification.LibsignalTripleRatchet (KindNoHeap)
open CryptoVerification.LibsignalTripleRatchet.InImage.DecodeErrorFrom (
  memRegion_40_cells memRegion_72_cells decodeErrorWith_zero_entails cells6_entails_memRegion48
)
open CryptoVerification.LibsignalTripleRatchet.Prost.X (
  stackAt_decodeErrorFromX_slack stackAt_decodeErrorFromX_cells
)
open Proofs.libsignal.Stage1X (lscall_of_withLsCl)
open LibsignalBinary.Heap (
  AllocEvent AllocCostModel BudgetLimits RustCliAllocBudget RustLayoutOk
  AllocCallPreserved FitsEvents FitsEnv VmPreserved rustAllocEvents
)
open LibsignalBinary.Heap.SpecBudget (
  DecodeErrorFromEnv decodeErrorFromBudgetSpecWithStack
)
open LibsignalBinary.Proofs.SessionRecordAt.Stage1X.GrowOneXBudget (AllocContractsPlaced)
open LibsignalBinary.Proofs.SessionRecordAt.TripleRatchet.Prost.DefsWBudget (decodeErrorFromSpecX)
open LibsignalBinary.Proofs.SessionRecordAt.TripleRatchet.Wire.X.CalleesWBudget (
  DecodeErrorFromPlacedOkW
)

attribute [local irreducible] Program.fetch Program.externAt? Program.fnOff
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero

/-- Relocatable `<DecodeError as From<DecodeErrorKind>>::from` (Block `261`) meets
`DecodeErrorFromPlacedOkW A lim H` under `AllocContractsPlaced M A lim H`. -/
theorem decodeErrorFrom_placed_okW [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {H : LibsignalHooks}
    (hA : AllocContractsPlaced M A lim H) :
    DecodeErrorFromPlacedOkW A lim H := by
  unfold DecodeErrorFromPlacedOkW withLsCodeLoaded decodeErrorFromSpecX
    decodeErrorFromBudgetSpecWithStack
  simp only [stackAt_decodeErrorFromX_slack, stackAt_decodeErrorFromX_cells, sepExists_sepConj_right]
  wp_init xst s0
  obtain ⟨k, w, st⟩ := xst
  dsimp only at *
  have hpow2 : ∃ j, 8 = 2 ^ j := ⟨3, rfl⟩
  have hlay : RustLayoutOk 72 8 := ⟨⟨by decide, hpow2, by decide⟩, by decide⟩
  have hfits : FitsEvents M lim st (rustAllocEvents 72 8) :=
    ‹FitsEnv M lim st DecodeErrorFromEnv› _ rfl
  rcases hfits.1 with ⟨_, henf, hphys, hva⟩
  apply sepWP_seq_lscl (mid := lsρ lsRustNoAllocShimSym) ‹_›
  wp_steps_sync_pool (lsρ lsRustNoAllocShimSym)
  apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
  intro hcl1
  apply sepWP_seq_lscl (mid := lsρ lsRustAllocSym) hcl1
  have hshim_call := lscall_of_withLsCl
    (hA.shim (callerProg := (blkPC_261).rebase (blkPl_261).base H)) hcl1
  wp_call hshim_call ()
  have htr1 : sf.trace = s0.trace := by simpa only [wp_norm] using ‹sf.trace = _›
  refine ProofLib.SepWP.transport_budgetPool ‹VmPreserved _ _› (hnext := ?_)
  wp_steps_sync_pool (lsρ lsRustAllocSym)
  apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
  intro hcl2
  have halloc_call := hA.allocNoOom_call (callerProg := (blkPC_261).rebase (blkPl_261).base H) hcl2
  wp_call halloc_call (72, 8, st)
  have htr2 : sf_1.trace = s0.trace := ‹AllocCallPreserved sf sf_1›.2.1.trans htr1
  have hoom_beq : (sf_1.readReg64 Reg.x0 == 0#64) = false :=
    beq_eq_false_iff_ne.mpr ‹sf_1.readReg64 Reg.x0 ≠ 0#64›
  conv =>
    arg 4
    simp only [memRegion_40_cells (k + 8#64), memRegion_72_cells,
      sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc,
      BitVec.add_assoc, BitVec.reduceAdd]
  apply SepWP.exists_elim; intro k0
  apply SepWP.exists_elim; intro k1
  apply SepWP.exists_elim; intro k2
  apply SepWP.exists_elim; intro k3
  apply SepWP.exists_elim; intro k4
  apply SepWP.exists_elim; intro u0
  apply SepWP.exists_elim; intro u1
  apply SepWP.exists_elim; intro u2
  apply SepWP.exists_elim; intro u3
  apply SepWP.exists_elim; intro u4
  apply SepWP.exists_elim; intro u5
  apply SepWP.exists_elim; intro u6
  apply SepWP.exists_elim; intro u7
  apply SepWP.exists_elim; intro u8
  wp_steps_sync_pool (s0.readReg64 .lr)
  apply SepWP.fold (decodeErrorWith_zero_entails A.repAlloc _ w _ _ _ _ _ ‹KindNoHeap w›)
    (by sep_frame)
  apply SepWP.fold (cells6_entails_memRegion48 k w _ _ _ _ _) (by sep_frame)
  have hfold_pool : ∀ s : State,
      A.pool lim (M.stepEvents (rustAllocEvents 72 8) st) s ⊢
        ∃∗ evs : List AllocEvent, ⌜DecodeErrorFromEnv evs⌝ ∗
          A.pool lim (M.stepEvents evs st) s :=
    fun _ => Entails.sepExists_right (rustAllocEvents 72 8)
      (Entails.pure_right rfl (Entails.refl _))
  apply SepWP.fold (hfold_pool _) (by sep_frame)
  rw [hsp_sf]
  wp_done

end LibsignalBinary.Proofs.SessionRecordAt.TripleRatchet.Prost.X.DecodeErrorFromXBudget
