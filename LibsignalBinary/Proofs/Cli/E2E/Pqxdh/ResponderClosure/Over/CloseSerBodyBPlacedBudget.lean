/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Over.CloseSerBodyBBudget
public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Over.CloseSerBodyBPlaced
public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Over.CloseSerDefsPlacedBudget
public import LibsignalBinary.Proofs.SessionRecordAt.Hooks2.Ser.CommonBudget
import Arm64.Trusted.Spec.Hoare
import Arm64.Trusted.Spec.SepLogic
import ProofLib.SepLogic.WPp

/-!
# Budget-Threaded Relocatable `SessionRecord::serialize`: Epilogue Tail Re-Exports

Re-exports the budget-threaded `[LibsignalPlacement]` epilogue tail theorems (`+692 .. ret` on
Block `52`) and element-cell folding helpers from `CloseSerBodyBBudget`.
-/

@[expose] public section

set_option autoImplicit false
set_option linter.unusedVariables false

namespace LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Over.CloseSerBodyBPlacedBudget

open Arm64 ProofLib SepProp
open CryptoGames.LibsignalSessionApi (Session)
open CryptoVerification (
  LibsignalPlacement LibsignalHooks LibsignalCodeLoaded lsmpl
)
open CryptoVerification.RustHeap (vecU8 vecU8At vecU8Buf)
open CryptoVerification.LibsignalPublicApiRepr (sessionStateReprAt)
open CryptoVerification.LibsignalTripleRatchetRepr (SessionGhost okTagVec)
open CryptoVerification.E2E.Record.Placed (lsProg_52 blkPl_52)
open CryptoVerification.E2E.Record.Serialization.SerializeBodyAuxX (serializeSubStackX)
open CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.Over (serSavedCells)
open LibsignalBinary.Heap (
  AllocEvent AllocCostModel BudgetLimits FreeOnlyEvs RustCliAllocBudget
)
open LibsignalBinary.Proofs.SessionRecordAt.Hooks2.SerDefsXBudget (
  serializeStackX SerContractsXPlaced
)
open LibsignalBinary.Proofs.SessionRecordAt.Hooks2.Ser.CommonBudget (
  SepWPpLsCl DropSessionStructureLocal1PlacedOkX
)

/-! ## Precondition-folding helper -/

theorem sepWPpLsCl_fold {pl : Obj.MultiPlacement} {prog : Program} {ret : BitVec 64} {s : State}
    {P T T' F : SepProp} {Q Qp : State → SepProp → Prop}
    (hent : T ⊢ T') (hf : P = T ∗ F) (h : SepWPpLsCl pl prog ret s (T' ∗ F) Q Qp) :
    SepWPpLsCl pl prog ret s P Q Qp :=
  LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Over.CloseSerBodyBBudget.sepWPpLsCl_fold
    hent hf h

/-! ## Shared epilogue (`+812 .. ret`) and tail (`+692 .. ret`) -/

abbrev SerPrev1PlacedTailStmt :=
  @LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Over.CloseSerBodyBBudget.SerPrev1PlacedTailStmt

theorem serPrev1Tail_placed_epilogue_sepWP [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits} {H : LibsignalHooks}
    (out q' cap' ptr' : BitVec 64) (bs : List (BitVec 8)) (st : M.σ)
    {ret : BitVec 64} {s0 s : State} {P Fx : SepProp} {Q : State → SepProp → Prop}
    (hQ : ∀ sf : State, sf.trace = s0.trace → sf.sp = s0.sp → CalleeSavedPreserved s0 sf →
      Q sf (((out ↦₆₄ okTagVec) ∗ vecU8 A.repAlloc (out + 8#64) bs ∗ A.pool lim st sf ∗
        stackAt s0.sp serializeStackX) ∗ Fx))
    (hal0 : s0.sp &&& 15#64 = 0#64)
    (hpc : s.pc = (blkPl_52).base + bv% (812))
    (hrun : s.status = .Running)
    (hsp : s.sp = s0.sp - 800#64)
    (htr : s.trace = s0.trace)
    (hvr : calleeSavedVRegs s = calleeSavedVRegs s0)
    (hP : P =
      (stackAt (s0.sp - 800#64) serializeSubStackX ∗
        ((s0.sp - 800#64) ↦₆₄ 1#64) ∗ ((s0.sp - 792#64) ↦₆₄ q') ∗
        ((s0.sp - 784#64) ↦₆₄ 1#64) ∗ memRegion (s0.sp - 776#64) 344 ∗
        ((s0.sp - 432#64) ↦₆₄ cap') ∗ ((s0.sp - 424#64) ↦₆₄ ptr') ∗
        ((s0.sp - 416#64) ↦₆₄ BitVec.ofNat 64 bs.length) ∗
        vecU8Buf A.repAlloc cap' ptr' bs ∗
        memRegion (s0.sp - 408#64) 312 ∗
        (out ↦₆₄ okTagVec) ∗ ((out + 8#64) ↦₆₄ cap') ∗
        ((out + 16#64) ↦₆₄ ptr') ∗ ((out + 24#64) ↦₆₄ BitVec.ofNat 64 bs.length) ∗
        A.pool lim st s ∗ serSavedCells s0 ret) ∗ Fx) :
    SepWP (lsProg_52 H) ret s P Q :=
  LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Over.CloseSerBodyBBudget.serPrev1Tail_placed_epilogue_sepWP
    out q' cap' ptr' bs st hQ hal0 hpc hrun hsp htr hvr hP

theorem serPrev1Tail_placed_epilogue [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits} {H : LibsignalHooks}
    (out q' cap' ptr' : BitVec 64) (bs : List (BitVec 8)) (st : M.σ)
    {ret : BitVec 64} {s0 s : State} {P Fx : SepProp} {Q Qp : State → SepProp → Prop}
    (hQ : ∀ sf : State, sf.trace = s0.trace → sf.sp = s0.sp → CalleeSavedPreserved s0 sf →
      Q sf (((out ↦₆₄ okTagVec) ∗ vecU8 A.repAlloc (out + 8#64) bs ∗ A.pool lim st sf ∗
        stackAt s0.sp serializeStackX) ∗ Fx))
    (hal0 : s0.sp &&& 15#64 = 0#64)
    (hpc : s.pc = (blkPl_52).base + bv% (812))
    (hrun : s.status = .Running)
    (hsp : s.sp = s0.sp - 800#64)
    (htr : s.trace = s0.trace)
    (hvr : calleeSavedVRegs s = calleeSavedVRegs s0)
    (hP : P =
      (stackAt (s0.sp - 800#64) serializeSubStackX ∗
        ((s0.sp - 800#64) ↦₆₄ 1#64) ∗ ((s0.sp - 792#64) ↦₆₄ q') ∗
        ((s0.sp - 784#64) ↦₆₄ 1#64) ∗ memRegion (s0.sp - 776#64) 344 ∗
        ((s0.sp - 432#64) ↦₆₄ cap') ∗ ((s0.sp - 424#64) ↦₆₄ ptr') ∗
        ((s0.sp - 416#64) ↦₆₄ BitVec.ofNat 64 bs.length) ∗
        vecU8Buf A.repAlloc cap' ptr' bs ∗
        memRegion (s0.sp - 408#64) 312 ∗
        (out ↦₆₄ okTagVec) ∗ ((out + 8#64) ↦₆₄ cap') ∗
        ((out + 16#64) ↦₆₄ ptr') ∗ ((out + 24#64) ↦₆₄ BitVec.ofNat 64 bs.length) ∗
        A.pool lim st s ∗ serSavedCells s0 ret) ∗ Fx) :
    SepWPpLsCl lsmpl (lsProg_52 H) ret s P Q Qp :=
  LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Over.CloseSerBodyBBudget.serPrev1Tail_placed_epilogue
    out q' cap' ptr' bs st hQ hal0 hpc hrun hsp htr hvr hP

theorem serPrev1Tail_placed_sepWP [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits} {H : LibsignalHooks}
    (hC : SerContractsXPlaced M A lim H)
    (hDrop : DropSessionStructureLocal1PlacedOkX M A lim H)
    (out q' capE ptrE cap' ptr' o0 o1 o2 o3 : BitVec 64) (bs enc : List (BitVec 8))
    (w : SessionGhost) (sess' : Session (List (BitVec 8))) (st : M.σ)
    {ret : BitVec 64} {s0 sm : State} {Fx : SepProp} {Q : State → SepProp → Prop}
    (hQ : ∀ (sf : State) (evs : List AllocEvent),
      sf.trace = s0.trace → sf.sp = s0.sp → CalleeSavedPreserved s0 sf →
      FreeOnlyEvs evs →
      Q sf (((out ↦₆₄ okTagVec) ∗ vecU8 A.repAlloc (out + 8#64) bs ∗
        A.pool lim (M.stepEvents evs st) sf ∗
        stackAt s0.sp serializeStackX) ∗ Fx))
    (hal0 : s0.sp &&& 15#64 = 0#64)
    (hpc : sm.pc = (blkPl_52).base + bv% (692))
    (hrun : sm.status = .Running)
    (hsp : sm.sp = s0.sp - 800#64)
    (htr : sm.trace = s0.trace)
    (hx19 : sm.readReg64 .x19 = out)
    (hx23 : (sm.readReg64 .x23 + 1#64 == 0#64) = false)
    (hx24 : sm.readReg64 .x24 = s0.sp - 800#64)
    (hvr : calleeSavedVRegs sm = calleeSavedVRegs s0)
    (hcl : LibsignalCodeLoaded lsmpl sm.mem) :
    SepWP (lsProg_52 H) ret sm
      ((vecU8At A.repAlloc (s0.sp - 432#64) cap' ptr' bs ∗
        vecU8At A.repAlloc q' capE ptrE enc ∗
        A.pool lim st sm ∗
        stackAt (s0.sp - 800#64) serializeSubStackX) ∗
      (((s0.sp - 800#64) ↦₆₄ 1#64) ∗ ((s0.sp - 792#64) ↦₆₄ q') ∗
        ((s0.sp - 784#64) ↦₆₄ 1#64) ∗ A.live q' 24 8 ∗
        sessionStateReprAt A.repAlloc (s0.sp - 776#64) w sess' ∗
        memRegion (s0.sp - 408#64) 312 ∗
        (out ↦₆₄ o0) ∗ ((out + 8#64) ↦₆₄ o1) ∗ ((out + 16#64) ↦₆₄ o2) ∗
        ((out + 24#64) ↦₆₄ o3) ∗
        serSavedCells s0 ret ∗ Fx))
      Q :=
  LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Over.CloseSerBodyBBudget.serPrev1Tail_placed_sepWP
    hC hDrop out q' capE ptrE cap' ptr' o0 o1 o2 o3 bs enc w sess' st
    hQ hal0 hpc hrun hsp htr hx19 hx23 hx24 hvr hcl

theorem serPrev1Tail_placed_ok [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits} {H : LibsignalHooks}
    (hC : SerContractsXPlaced M A lim H)
    (hDrop : DropSessionStructureLocal1PlacedOkX M A lim H) :
    SerPrev1PlacedTailStmt M A lim H :=
  LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Over.CloseSerBodyBBudget.serPrev1Tail_placed_ok
    hC hDrop

/-! ## Element-cell folding helpers -/

theorem k5_fold_q_placed {pl : Obj.MultiPlacement} {prog : Program} {ret : BitVec 64} {s : State}
    {Q Qp : State → SepProp → Prop} {M : AllocCostModel} (A : RustCliAllocBudget M)
    (q capE ptrE : BitVec 64) (enc : List (BitVec 8)) {P F : SepProp}
    (hP : P = ((q ↦₆₄ capE) ∗ ((q + 8#64) ↦₆₄ ptrE) ∗
      ((q + 16#64) ↦₆₄ BitVec.ofNat 64 enc.length) ∗ vecU8Buf A.repAlloc capE ptrE enc) ∗ F)
    (h : SepWPpLsCl pl prog ret s (vecU8At A.repAlloc q capE ptrE enc ∗ F) Q Qp) :
    SepWPpLsCl pl prog ret s P Q Qp :=
  LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Over.CloseSerBodyBBudget.k5_fold_q_placed
    A q capE ptrE enc hP h

theorem k5_fold_q_sepWP {prog : Program} {target : BitVec 64} {s : State}
    {Q : State → SepProp → Prop} {M : AllocCostModel} (A : RustCliAllocBudget M)
    (q capE ptrE : BitVec 64) (enc : List (BitVec 8)) {P F : SepProp}
    (hP : P = ((q ↦₆₄ capE) ∗ ((q + 8#64) ↦₆₄ ptrE) ∗
      ((q + 16#64) ↦₆₄ BitVec.ofNat 64 enc.length) ∗ vecU8Buf A.repAlloc capE ptrE enc) ∗ F)
    (h : SepWP prog target s (vecU8At A.repAlloc q capE ptrE enc ∗ F) Q) :
    SepWP prog target s P Q :=
  LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Over.CloseSerBodyBBudget.k5_fold_q_sepWP
    A q capE ptrE enc hP h

end LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Over.CloseSerBodyBPlacedBudget
