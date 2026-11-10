/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Heap.IfaceBudget
public import LibsignalBinary.Heap.IfaceBudgetLemmas
public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Over.CloseDefsBudget
public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Over.CloseSerDefs
public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Over.VecVecDefsBudget
public import LibsignalBinary.Proofs.E2E.Record.Serialization.EncodeRawAux.BaseBudget
public import LibsignalBinary.Proofs.E2E.Record.Serialization.SerializeBodyAux.HelpersBudget
public import LibsignalBinary.Proofs.SessionRecordAt.Hooks2.Ser.SerializeBodyHelpersXBudget
import LibsignalBinary.Proofs.Common.SharedHelpers
meta import LibsignalBinary.Proofs.Common.SharedHelpers -- shake: keep
import LibsignalBinary.Proofs.E2E.Record.Serialization.SerializeBodyAux.Helpers
import ProofLib.SepLogic.WPp

/-!
# Budget-Threaded `SessionRecord::serialize` (`Prev1`) Body Specs and Helpers

Budget-threaded (`RustCliAllocBudget M`) body contract `serializePrev1BodySpecX`, lifted
`serializeSubStackX` callee contracts, and `A.repAlloc` heap-splitting lemmas for
`SessionRecord::serialize` on a record with one previous session.
-/

@[expose] public section

set_option autoImplicit false

namespace LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Over.CloseSerDefsBudget

open Arm64 ProofLib SepProp
open CryptoGames.LibsignalSessionApi (Session)
open CryptoVerification (
  LibsignalPlacement LibsignalHooks IsLsBlockProg lsmpl withLsCodeLoaded withLsCl
  lsρ lsRustDeallocSym
)
open CryptoVerification.RustHeap (LayoutOk arrayAt vecBuf vecU8 vecU8At vecU8Buf)
open CryptoVerification.LibsignalPublicApiRepr (sessionStateReprAt)
open CryptoVerification.LibsignalTripleRatchetRepr (SessionGhost okTagVec)
open CryptoVerification.LibsignalTripleRatchet (extHookStack)
open CryptoVerification.E2E.Record.Serialization.SerializeBodyAux (
  subroutine_ok_withLsCodeLoaded_frame_weaken
  subroutine_ok_withLsCl_of_withLsCodeLoaded
)
open CryptoVerification.E2E.Record.Serialization.SerializeBodyAuxX (
  serializeSubStackX stackAt_serializeSub_splitX
  subroutine_ok_withLsCodeLoaded_of_withLsCl
)
open CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.Over (prevElem prevVecAt)
open LibsignalBinary.Heap (
  AllocCostModel AllocEvent BudgetLimits FitsEnv RustCliAllocBudget RustLayoutOk
  rustCliDeallocBudgetExternSpecWithStack
)
open LibsignalBinary.Proofs.SessionRecordAt.Hooks2.SerDefsXBudget (
  serializeStackX SerContractsXPlaced
)
open LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Over.VecVecDefsBudget (
  VecVecClone1Env VecVecClone1Ghost vecVecClone1SpecX vecVecClone1StackX
)
open LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Over.CloseDefsBudget (
  SerializePrev1Env
)

/-! ## Re-Exported Definitions and Layout Helpers -/

abbrev encodeRecordPrev1Mem :=
  CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.Over.encodeRecordPrev1Mem
abbrev encodeRecordPrev1Mem_eq_of_canon :=
  @CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.Over.encodeRecordPrev1Mem_eq_of_canon
abbrev SerializePrev1BodyGhost :=
  CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.Over.SerializePrev1BodyGhost
abbrev SerField2Saved :=
  CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.Over.SerField2Saved
abbrev serSavedCells :=
  CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.Over.serSavedCells
abbrev memRegion_zero_ser :=
  @CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.Over.memRegion_zero_ser
abbrev prevVec1_cap1_merge :=
  @CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.Over.prevVec1_cap1_merge
abbrev repack_stack_hdr_cellsX :=
  @CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.Over.repack_stack_hdr_cellsX
abbrev lenField_two_eq :=
  @CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.Over.lenField_two_eq
abbrev lenField_two_length :=
  @CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.Over.lenField_two_length
abbrev layoutOk_cap_u8_ser :=
  @CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.Over.layoutOk_cap_u8_ser
abbrev layoutOk_24_8_ser :=
  CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.Over.layoutOk_24_8_ser

theorem rustLayoutOk_cap_u8_ser {cap : BitVec 64} (h0 : cap ≠ 0#64) (hlt : cap.toNat < 2 ^ 63) :
    RustLayoutOk cap.toNat 1 :=
  ⟨layoutOk_cap_u8_ser h0 hlt, by decide⟩

theorem rustLayoutOk_24_8_ser : RustLayoutOk 24 8 :=
  ⟨layoutOk_24_8_ser, by decide⟩

/-! ## Budget-Threaded Body Specification -/

/-- Budget-threaded body contract for `SessionRecord::serialize` on a record with current session
`x.sess` (ghost `x.G`) and `previous_sessions = [x.enc]` under `SerializePrev1Env`. -/
def serializePrev1BodySpecX (M : AllocCostModel) (A : RustCliAllocBudget M)
    (lim : BudgetLimits) : Spec (SerializePrev1BodyGhost × M.σ) where
  pre := fun (x, st) s =>
    ⌜s.readReg64 .x0 = x.self ∧ s.readReg64 .x8 = x.out ∧
      (encodeRecordPrev1Mem x.G x.sess x.enc).length < 2 ^ 32 ∧
      FitsEnv M lim st (SerializePrev1Env x.G x.sess x.enc)⌝ ∗
      prevVecAt A.repAlloc x.self x.prevCap x.prevPtr [x.enc] ∗
      sessionStateReprAt A.repAlloc (x.self + 24#64) x.G x.sess ∗
      memRegion x.out 32 ∗ A.pool lim st s ∗ stackAt s.sp serializeStackX
  post := fun (x, st) s0 sf =>
    ∃∗ evs : List AllocEvent,
      ⌜sf.trace = s0.trace ∧ SerializePrev1Env x.G x.sess x.enc evs⌝ ∗
        prevVecAt A.repAlloc x.self x.prevCap x.prevPtr [x.enc] ∗
        sessionStateReprAt A.repAlloc (x.self + 24#64) x.G x.sess ∗
        (x.out ↦₆₄ okTagVec) ∗
        vecU8 A.repAlloc (x.out + 8#64) (encodeRecordPrev1Mem x.G x.sess x.enc) ∗
        A.pool lim (M.stepEvents evs st) sf ∗ stackAt s0.sp serializeStackX

/-! ## Lifted Callee Contracts at `serializeSubStackX` -/

def vecVecClone1SubSpecX (M : AllocCostModel) (A : RustCliAllocBudget M)
    (lim : BudgetLimits) : Spec (VecVecClone1Ghost × M.σ) where
  pre := fun (x, st) s =>
    ⌜s.readReg64 .x0 = x.dst ∧ s.readReg64 .x1 = x.src ∧ s.readReg64 .x2 = 1#64 ∧
      FitsEnv M lim st (VecVecClone1Env x)⌝ ∗
      arrayAt (prevElem A.repAlloc) 24 x.src [x.enc] ∗ memRegion x.dst 24 ∗
      A.pool lim st s ∗ stackAt s.sp serializeSubStackX
  post := fun (x, st) s0 sf =>
    ∃∗ evs : List AllocEvent,
      ⌜sf.trace = s0.trace ∧ VecVecClone1Env x evs⌝ ∗
        arrayAt (prevElem A.repAlloc) 24 x.src [x.enc] ∗
        (∃∗ q' : BitVec 64, prevVecAt A.repAlloc x.dst 1#64 q' [x.enc]) ∗
        A.pool lim (M.stepEvents evs st) sf ∗ stackAt s0.sp serializeSubStackX

theorem vecVecClone1_withLsCodeLoaded_sub_okX {pl : Obj.MultiPlacement}
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {prog : Program} {entry : BitVec 64}
    (h : subroutine_ok prog entry (withLsCl pl (vecVecClone1SpecX M A lim))) :
    subroutine_ok prog entry (withLsCodeLoaded pl (vecVecClone1SubSpecX M A lim)) := by
  refine subroutine_ok_withLsCodeLoaded_frame_weaken
    (fun _ s0 => memRegion (s0.sp - BitVec.ofNat 64 serializeSubStackX)
      (serializeSubStackX - vecVecClone1StackX))
    (subroutine_ok_withLsCodeLoaded_of_withLsCl h)
    (fun ⟨x, st⟩ s0 => ?_)
    (fun ⟨x, st⟩ s0 sf => ?_)
    (fun _ _ _ => Entails.pure_left False.elim)
    (fun _ _ _ _ => rfl)
  · simp only [vecVecClone1SubSpecX, vecVecClone1SpecX,
      stackAt_serializeSub_splitX s0.sp vecVecClone1StackX (by decide)]
    exact Entails.of_eq (by sep_ac_rfl)
  · dsimp only [vecVecClone1SubSpecX, vecVecClone1SpecX]
    rw [sepExists_sepConj_left]
    refine Entails.sepExists_mono fun evs => ?_
    rw [stackAt_serializeSub_splitX s0.sp vecVecClone1StackX (by decide)]
    exact Entails.of_eq (by sep_ac_rfl)

theorem vecVecClone1_withLsCl_sub_okX {pl : Obj.MultiPlacement}
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {prog : Program} {entry : BitVec 64}
    (h : subroutine_ok prog entry (withLsCl pl (vecVecClone1SpecX M A lim))) :
    subroutine_ok prog entry (withLsCl pl (vecVecClone1SubSpecX M A lim)) :=
  subroutine_ok_withLsCl_of_withLsCodeLoaded (vecVecClone1_withLsCodeLoaded_sub_okX h)

abbrev deallocSubSpecX [LibsignalPlacement] (M : AllocCostModel) (A : RustCliAllocBudget M)
    (lim : BudgetLimits) : Spec (BitVec 64 × Nat × Nat × M.σ) :=
  rustCliDeallocBudgetExternSpecWithStack M A lim serializeSubStackX

theorem dealloc_placed_sub_okX [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {callerProg : Program} {callerBlk : Nat} {H : LibsignalHooks}
    [IsLsBlockProg callerProg callerBlk H]
    (hC : SerContractsXPlaced M A lim H) :
    subroutine_ok callerProg (lsρ lsRustDeallocSym)
      (withLsCodeLoaded lsmpl (deallocSubSpecX M A lim)) := by
  refine subroutine_ok_withLsCodeLoaded_frame_weaken
    (fun _ s0 => memRegion (s0.sp - BitVec.ofNat 64 serializeSubStackX)
      (serializeSubStackX - extHookStack))
    (subroutine_ok_withLsCodeLoaded_of_withLsCl (hC.alloc.dealloc (callerProg := callerProg)))
    (fun ⟨p, size, align, st⟩ s0 => ?_)
    (fun ⟨p, size, align, st⟩ s0 sf => ?_)
    (fun _ _ _ => Entails.pure_left False.elim)
    (fun _ _ _ _ => rfl)
  · simp only [deallocSubSpecX, rustCliDeallocBudgetExternSpecWithStack,
      stackAt_serializeSub_splitX s0.sp extHookStack (by decide)]
    exact Entails.of_eq (by sep_ac_rfl)
  · simp only [deallocSubSpecX, rustCliDeallocBudgetExternSpecWithStack,
      stackAt_serializeSub_splitX s0.sp extHookStack (by decide)]
    exact Entails.of_eq (by sep_ac_rfl)

theorem dealloc_placed_sub_clX [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {callerProg : Program} {callerBlk : Nat} {H : LibsignalHooks}
    [IsLsBlockProg callerProg callerBlk H]
    (hC : SerContractsXPlaced M A lim H) :
    subroutine_ok callerProg (lsρ lsRustDeallocSym)
      (withLsCl lsmpl (deallocSubSpecX M A lim)) :=
  subroutine_ok_withLsCl_of_withLsCodeLoaded (dealloc_placed_sub_okX hC)

/-! ## Heap Shape Lemmas -/

theorem vecBuf_prev_one_split_ser {M : AllocCostModel} (A : RustCliAllocBudget M)
    (cap q : BitVec 64) (enc : List (BitVec 8)) :
    vecBuf A.repAlloc 24 8 (prevElem A.repAlloc) cap q [enc] =
      ⌜cap ≠ 0#64 ∧ cap.toNat * 24 < 2 ^ 63 ∧ q ≠ 0#64⌝ ∗
        (A.live q (cap.toNat * 24) 8 ∗ arrayAt (prevElem A.repAlloc) 24 q [enc] ∗
          memRegion (q + 24#64) ((cap.toNat - 1) * 24)) :=
  CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.Over.vecBuf_prev_one_split_ser
    A.repAlloc cap q enc

theorem prevVecAt_one_cells_ser {M : AllocCostModel} (A : RustCliAllocBudget M)
    (r cap q : BitVec 64) (enc : List (BitVec 8)) :
    prevVecAt A.repAlloc r cap q [enc] =
      (r ↦₆₄ cap) ∗ ((r + 8#64) ↦₆₄ q) ∗ ((r + 16#64) ↦₆₄ 1#64) ∗
        ⌜cap ≠ 0#64 ∧ cap.toNat * 24 < 2 ^ 63 ∧ q ≠ 0#64⌝ ∗
        (A.live q (cap.toNat * 24) 8 ∗ arrayAt (prevElem A.repAlloc) 24 q [enc] ∗
          memRegion (q + 24#64) ((cap.toNat - 1) * 24)) :=
  CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.Over.prevVecAt_one_cells_ser
    A.repAlloc r cap q enc

theorem prevVecAt_cap1_cells {M : AllocCostModel} (A : RustCliAllocBudget M)
    (r q : BitVec 64) (enc : List (BitVec 8)) :
    prevVecAt A.repAlloc r 1#64 q [enc] =
      (r ↦₆₄ 1#64) ∗ ((r + 8#64) ↦₆₄ q) ∗ ((r + 16#64) ↦₆₄ 1#64) ∗ ⌜q ≠ 0#64⌝ ∗
        A.live q 24 8 ∗ vecU8 A.repAlloc q enc :=
  CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.Over.prevVecAt_cap1_cells A.repAlloc r q enc

theorem vecU8At_cells {M : AllocCostModel} (A : RustCliAllocBudget M)
    (v cap ptr : BitVec 64) (bs : List (BitVec 8)) :
    vecU8At A.repAlloc v cap ptr bs =
      (v ↦₆₄ cap) ∗ ((v + 8#64) ↦₆₄ ptr) ∗ ((v + 16#64) ↦₆₄ BitVec.ofNat 64 bs.length) ∗
        vecU8Buf A.repAlloc cap ptr bs :=
  CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.Over.vecU8At_cells A.repAlloc v cap ptr bs

theorem vecU8Buf_drop_view {M : AllocCostModel} (A : RustCliAllocBudget M)
    (cap ptr : BitVec 64) (bs : List (BitVec 8)) :
    vecU8Buf A.repAlloc cap ptr bs ⊢
      ⌜cap.toNat < 2 ^ 63⌝ ∗
        (if cap = 0#64 then emp else A.live ptr cap.toNat 1 ∗ memRegion ptr cap.toNat) :=
  CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.Over.vecU8Buf_drop_view A.repAlloc cap ptr bs

end LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Over.CloseSerDefsBudget
