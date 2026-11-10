/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Over.CloseSerDefsBudget
public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Over.CloseSerBodyB
public import LibsignalBinary.Proofs.SessionRecordAt.Hooks2.Ser.SerializeBodyNoneXBudget
public import LibsignalBinary.Proofs.SessionRecordAt.Hooks2.Ser.SerializeBodySomeXBudget
public import LibsignalBinary.Proofs.SessionRecordAt.Hooks2.Ser.CommonBudget
public import LibsignalBinary.Proofs.SessionRecordAt.Hooks2.Ser.SerializeBodyHelpersXBudget
import LibsignalBinary.Proofs.Placed.BudgetPoolSync
meta import LibsignalBinary.Proofs.Placed.BudgetPoolSync -- shake: keep
import LibsignalBinary.Proofs.Common.SharedHelpers
meta import LibsignalBinary.Proofs.Common.SharedHelpers -- shake: keep
import LibsignalBinary.Proofs.E2E.Record.Serialization.SerializeBodyAux.Helpers
import LibsignalBinary.Proofs.TripleRatchet.RawByteMove.Move
import ProofLib.SepLogic.WPp
import Arm64.Trusted.Spec.Hoare
import Arm64.Trusted.Spec.SepLogic

/-!
# Budget-Threaded `SessionRecord::serialize`: Epilogue Tail and Framing Helpers

Proves the budget-threaded `[LibsignalPlacement]` tail `serPrev1Tail_placed_ok : SerPrev1PlacedTailStmt`
(`+692 .. ret` on Block `52`, advancing `A.pool` by `FreeOnlyEvs`), together with pool-aware heap
and precondition-folding helpers used by `CloseSerBody`.
-/

@[expose] public section

set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option maxRecDepth 2000000

namespace LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Over.CloseSerBodyBBudget

open Arm64 ProofLib SepProp
open CryptoGames.LibsignalSessionApi (Session)
open CryptoVerification (
  LibsignalPlacement LibsignalHooks LibsignalCodeLoaded
  lsmpl withLsCl sepWP_seq_lscl lsρ lsRustDeallocSym
)
open CryptoVerification.RustHeap (arrayAt vecU8 vecU8At vecU8Buf)
open CryptoVerification.LibsignalPublicApiRepr (sessionStateReprAt)
open CryptoVerification.LibsignalTripleRatchetRepr (SessionGhost okTagVec sessionStateAt)
open CryptoVerification.E2E.Record.Placed (lsProg_52 blkPl_52 blkLib_eq_52)
open CryptoVerification.E2E.Record.Serialization.SerializeBodyAux (
  sessionAt_entails_sessionStateAt cells_12_pack
)
open CryptoVerification.E2E.Record.Serialization.SerializeBodyAuxX (
  serializeSubStackX sepWP_pure_left_sepX vecU8_from_out_cellsX
  vecU8At_unpack_cells_432X vecU8At_init_byte_432X
)
open CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.Over (
  prevElem prevVecAt serSavedCells prevVec1_cap1_merge repack_stack_hdr_cellsX
)
open Proofs.libsignal.Hooks2 (SepWPpIn)
open LibsignalBinary.Heap (
  VmPreserved AllocEvent AllocCostModel BudgetLimits RustCliAllocBudget
  RustLayoutOk FreeOnlyEvs rustDeallocEvents
)
open LibsignalBinary.Heap.IfaceBudgetLemmas (rustCliDeallocBudgetExternSpecWithStack)
open LibsignalBinary.Proofs.Placed.BudgetPoolSync (hooksException sepWP_seg_ls_vm)
open LibsignalBinary.Proofs.SessionRecordAt.Hooks2.SerDefsXBudget (
  serializeStackX SerContractsXPlaced
)
open LibsignalBinary.Proofs.SessionRecordAt.Hooks2.Ser.CommonBudget (
  SepWPpLsCl DropSessionStructureLocal1PlacedOkX
)
open LibsignalBinary.Proofs.SessionRecordAt.Hooks2.Ser.SerializeBodyHelpersXBudget (
  dropLocal1SubSpecX dropLocal1_placed_sub_clX
)
open LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Over.CloseSerDefsBudget (
  deallocSubSpecX dealloc_placed_sub_clX
  rustLayoutOk_cap_u8_ser rustLayoutOk_24_8_ser
  prevVecAt_one_cells_ser prevVecAt_cap1_cells vecU8At_cells vecU8Buf_drop_view
)

private theorem bv_sub_add_lit (x a b : BitVec 64) : x - a + b = x - (a - b) := by
  bv_omega

private theorem spAligned_sub_800 (sp : BitVec 64) (h0 : sp &&& 15#64 = 0#64) :
    ((sp - 800#64) &&& 15#64 == 0#64) = true := by
  have e : ∀ x : BitVec 64, (x &&& 15#64).toNat = x.toNat % 16 := fun x => by
    simp only [BitVec.toNat_and]
    exact Nat.and_two_pow_sub_one_eq_mod x.toNat 4
  have h' := congrArg BitVec.toNat h0
  rw [beq_iff_eq]
  apply BitVec.eq_of_toNat_eq
  rw [e] at h' ⊢
  simp only [BitVec.toNat_sub, BitVec.toNat_ofNat] at h' ⊢
  have hlt := sp.isLt
  omega

attribute [local irreducible] Program.fetch Program.externAt?
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero
attribute [local wp_norm] calleeSavedVRegs_advancePC calleeSavedVRegs_setPC calleeSavedVRegs_setMem
  calleeSavedVRegs_setPState calleeSavedVRegs_writeReg64 calleeSavedVRegs_writeReg32
  calleeSavedVRegs_writeReg calleeSavedVRegs_writeVReg128_ite calleeSavedVRegs_writeVReg64_ite
  calleeSavedVRegs_writeVReg32_ite isCalleeSavedVReg updateCalleeSavedVRegs

/-! ## Precondition-folding helpers -/

abbrev k5t_false_left :=
  @CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.Over.k5t_false_left
abbrev sepWPpIn_fold :=
  @CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.Over.sepWPpIn_fold
abbrev ult_ofNat_add_false :=
  @CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.Over.ult_ofNat_add_false
abbrev ofNat_add_bits :=
  @CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.Over.ofNat_add_bits

theorem sepWPpLsCl_fold {pl : Obj.MultiPlacement} {prog : Program} {ret : BitVec 64} {s : State}
    {P T T' F : SepProp} {Q Qp : State → SepProp → Prop}
    (hent : T ⊢ T') (hf : P = T ∗ F) (h : SepWPpLsCl pl prog ret s (T' ∗ F) Q Qp) :
    SepWPpLsCl pl prog ret s P Q Qp :=
  SepWPpLsCl.weaken_pre (hf ▸ sepConj_mono_left hent) h

private theorem freeOnlyEvs_rustDealloc (size align : Nat) :
    FreeOnlyEvs (rustDeallocEvents size align) := by
  intro ev hev
  simp only [rustDeallocEvents, List.mem_singleton] at hev
  subst hev
  exact ⟨align, size, rfl⟩

/-! ## Relocatable tail statement (`+692 .. ret`) -/

/-- Budget-threaded `[LibsignalPlacement]` epilogue contract (`+692 .. ret` on `lsProg_52 H`):
writes `Ok(vec)` to `out`, drops the cloned `SessionStructure` and temporary `Vec<Vec<u8>>`
(`FreeOnlyEvs`), and returns. -/
def SerPrev1PlacedTailStmt [LibsignalPlacement] (M : AllocCostModel)
    (A : RustCliAllocBudget M) (lim : BudgetLimits) (H : LibsignalHooks) : Prop :=
  ∀ (out q' capE ptrE cap' ptr' o0 o1 o2 o3 : BitVec 64) (bs enc : List (BitVec 8))
    (w : SessionGhost) (sess' : Session (List (BitVec 8))) (st : M.σ)
    {ret : BitVec 64} {s0 sm : State} {Fx : SepProp} {Q Qp : State → SepProp → Prop},
    (∀ (sf : State) (evs : List AllocEvent),
      sf.trace = s0.trace → sf.sp = s0.sp → CalleeSavedPreserved s0 sf →
      FreeOnlyEvs evs →
      Q sf (((out ↦₆₄ okTagVec) ∗ vecU8 A.repAlloc (out + 8#64) bs ∗
        A.pool lim (M.stepEvents evs st) sf ∗
        stackAt s0.sp serializeStackX) ∗ Fx)) →
    s0.sp &&& 15#64 = 0#64 →
    sm.pc = (blkPl_52).base + bv% (692) →
    sm.status = .Running →
    sm.sp = s0.sp - 800#64 →
    sm.trace = s0.trace →
    sm.readReg64 .x19 = out →
    (sm.readReg64 .x23 + 1#64 == 0#64) = false →
    sm.readReg64 .x24 = s0.sp - 800#64 →
    calleeSavedVRegs sm = calleeSavedVRegs s0 →
    SepWPpLsCl lsmpl (lsProg_52 H) ret sm
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
      Q Qp

/-! ## Shared epilogue (`+812 .. ret`) and tail (`+692 .. ret`) -/

section TailProof

attribute [local irreducible] sessionStateReprAt sessionStateAt FreeOnlyEvs

local macro "wp_seg_sync52 " hseg:ident mid:term : tactic =>
  `(tactic| (
    apply ($hseg:ident (mid := $mid))
    intro _m_strip
    wp_steps
    refine SepWP.done
      (by simp only [arm64_norm])
      (by simp only [arm64_norm]; assumption)
      fun _m_real _hnsp => ?_
    refine SepWP.transport_budgetPool
      (_hnsp.toVmPreserved (by simp only [arm64_norm]))
      (hnext := ?_)
    clear _hnsp
    try clear _m_strip))

local macro "wp_done_call52 " hcl:ident : tactic =>
  `(tactic| (
    apply SepWP.done
      (by simp only [arm64_norm])
      (by simp only [arm64_norm]; assumption)
    intro $hcl:ident
    simp only [arm64_norm] at $hcl:ident))

private theorem sepWP_epilogue_finish {prog : Program} {ret : BitVec 64} {sf : State}
    {P Fx : SepProp} {Q : State → SepProp → Prop} {M : AllocCostModel}
    (A : RustCliAllocBudget M) (lim : BudgetLimits) (st : M.σ)
    (out : BitVec 64) (bs : List (BitVec 8)) (sp0 : BitVec 64)
    (heq : P = ((out ↦₆₄ okTagVec) ∗ vecU8 A.repAlloc (out + 8#64) bs ∗
      A.pool lim st sf ∗ stackAt sp0 serializeStackX) ∗ Fx)
    (hpc : sf.pc = ret) (hrun : sf.status = .Running)
    (hq : Q sf (((out ↦₆₄ okTagVec) ∗ vecU8 A.repAlloc (out + 8#64) bs ∗
      A.pool lim st sf ∗ stackAt sp0 serializeStackX) ∗ Fx)) :
    SepWP prog ret sf P Q := by
  rw [heq]
  exact SepWP.done hpc hrun hq

private theorem sepWP_bind_drop_evs {prog : Program} {ret : BitVec 64} {sf : State}
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {evs : List AllocEvent} {st : M.σ} {sp776 : BitVec 64} {R : SepProp}
    {Q : State → SepProp → Prop}
    (hfree : FreeOnlyEvs evs)
    (hk : ∀ (evs_drop : List AllocEvent), FreeOnlyEvs evs_drop →
      SepWP prog ret sf (memRegion sp776 344 ∗ A.pool lim (M.stepEvents evs_drop st) sf ∗ R) Q) :
    SepWP prog ret sf (memRegion sp776 344 ∗ A.pool lim (M.stepEvents evs st) sf ∗ R) Q :=
  hk evs hfree

set_option maxHeartbeats 400000 in
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
    SepWP (lsProg_52 H) ret s P Q := by
  have hal0' : (s0.sp &&& 15#64 == 0#64) = true := by simp only [hal0, beq_self_eq_true]
  have hal : ((s0.sp - 800#64) &&& 15#64 == 0#64) = true := spAligned_sub_800 s0.sp hal0
  subst hP
  unfold serSavedCells
  simp only [sepConj_assoc]
  change s.pc = (blkPl_52).base + 812#64 at hpc
  wp_steps_sync_pool ret
  refine SepWP.fold (vecU8_from_out_cellsX A.repAlloc out cap' ptr' bs) (by sep_frame) ?_
  refine SepWP.fold (cells_12_pack s0.sp _ _ _ _ _ _ _ _ _ _ _ _) (by sep_frame) ?_
  refine SepWP.fold (repack_stack_hdr_cellsX s0.sp 1#64 q' 1#64 cap' ptr'
    (BitVec.ofNat 64 bs.length)) (by sep_frame) ?_
  refine sepWP_epilogue_finish A lim st out bs s0.sp (by sep_ac_rfl)
    (by wp_norm_goal) (by wp_norm_lhs) (hQ _ ?_ ?_ ?_)
  · simp only [wp_norm, arm64_norm, *]
  · simp only [wp_norm, arm64_norm, *]
  · refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> simp only [wp_norm, arm64_norm, *]

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
  SepWPpLsCl.of_sepWP_ret
    (serPrev1Tail_placed_epilogue_sepWP out q' cap' ptr' bs st hQ hal0 hpc hrun hsp htr hvr hP)

set_option maxHeartbeats 800000 in
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
      Q := by
  have hdrop := dropLocal1_placed_sub_clX (callerProg := lsProg_52 H) hDrop
  have hdealloc := dealloc_placed_sub_clX (callerProg := lsProg_52 H) hC
  change subroutine_ok (lsProg_52 H) (lsmpl.base 6)
    (withLsCl lsmpl (dropLocal1SubSpecX M A lim)) at hdrop
  change subroutine_ok (lsProg_52 H) (lsρ lsRustDeallocSym)
    (withLsCl lsmpl (deallocSubSpecX M A lim)) at hdealloc
  dsimp only [withLsCl, dropLocal1SubSpecX, deallocSubSpecX,
    rustCliDeallocBudgetExternSpecWithStack] at hdrop hdealloc
  have hx19' : sm.readReg64 (Reg.gpr 19#5) = out := hx19
  have hx23' : (sm.readReg64 (Reg.gpr 23#5) + 1#64 == 0#64) = false := hx23
  have hx24' : sm.readReg64 (Reg.gpr 24#5) = s0.sp - 800#64 := hx24
  have hal0' : (s0.sp &&& 15#64 == 0#64) = true := by simp only [hal0, beq_self_eq_true]
  have hal : ((s0.sp - 800#64) &&& 15#64 == 0#64) = true := spAligned_sub_800 s0.sp hal0
  have hrl24 : RustLayoutOk 24 8 := rustLayoutOk_24_8_ser
  have hpow8 : ∃ k, 8 = 2 ^ k := ⟨3, rfl⟩
  have hpow1 : ∃ k, 1 = 2 ^ k := ⟨0, rfl⟩
  clear hx19 hx23 hx24
  have hseg52 := fun {mid target : BitVec 64} {s : State} {Pre : SepProp}
      {post : State → SepProp → Prop} {oom : State → SepProp} =>
    sepWP_seg_ls_vm (prog := lsProg_52 H) (Q := lsProg_52 (hooksException H))
      blkLib_eq_52 (by rfl) (mid := mid) (target := target) (s := s) (Pre := Pre)
      (post := post) (oom := oom)
  rw [vecU8At_unpack_cells_432X, vecU8At_cells A q' capE ptrE enc]
  simp only [sepConj_assoc]
  change sm.pc = (blkPl_52).base + 692#64 at hpc
  refine SepWP.fold (vecU8Buf_drop_view A capE ptrE enc) (by sep_frame) ?_
  apply sepWP_pure_left_sepX; intro hcapE63
  apply sepWP_seq_lscl hcl (mid := lsmpl.base 6)
  wp_seg_sync52 hseg52 (lsmpl.base 6)
  refine SepWP.fold (sessionAt_entails_sessionStateAt A.repAlloc (s0.sp - 776#64) w sess')
    (by sep_frame) ?_
  wp_done_call52 hcl1
  wp_call hdrop (⟨s0.sp - 776#64, w, sess'.state⟩, st)
  refine sepWP_bind_drop_evs (by assumption) fun evs_drop hfree_drop => ?_
  by_cases hc : capE = 0#64
  · rw [ite_eq_left hc, emp_sepConj]
    subst hc
    apply sepWP_seq_lscl (pl := lsmpl) (mid := lsρ lsRustDeallocSym); · assumption
    wp_seg_sync52 hseg52 (lsρ lsRustDeallocSym)
    refine SepWP.fold (prevVec1_cap1_merge q' 0#64 ptrE (BitVec.ofNat 64 enc.length))
      (by sep_frame) ?_
    wp_done_call52 hcl2
    wp_call hdealloc (q', 24, 8, M.stepEvents evs_drop st)
    conv => arg 4; simp only [← AllocCostModel.stepEvents_append]
    let evs_all := evs_drop ++ rustDeallocEvents 24 8
    have hfree_all : FreeOnlyEvs evs_all :=
      FreeOnlyEvs.append hfree_drop (freeOnlyEvs_rustDealloc 24 8)
    exact serPrev1Tail_placed_epilogue_sepWP out q' cap' ptr' bs
      (M.stepEvents evs_all st)
      (fun sf htr_f hsp_f hcs_f => hQ sf evs_all htr_f hsp_f hcs_f hfree_all)
      hal0
      (by simp only [wp_norm, arm64_norm, *])
      (by simp only [wp_norm, arm64_norm, *])
      (by simp only [wp_norm, arm64_norm, *])
      (by simp only [wp_norm, arm64_norm, *])
      (by simp only [wp_norm, arm64_norm, *])
      (by simp only [okTagVec]; sep_frame)
  · have hrlE : RustLayoutOk capE.toNat 1 := rustLayoutOk_cap_u8_ser hc hcapE63
    have hcE : (capE == 0#64) = false := beq_false_of_ne hc
    rw [ite_eq_right hc]
    simp only [sepConj_assoc]
    apply sepWP_seq_lscl (pl := lsmpl) (mid := lsρ lsRustDeallocSym); · assumption
    wp_seg_sync52 hseg52 (lsρ lsRustDeallocSym)
    wp_done_call52 hcl2
    wp_call hdealloc (ptrE, capE.toNat, 1, M.stepEvents evs_drop st)
    apply sepWP_seq_lscl (pl := lsmpl) (mid := lsρ lsRustDeallocSym); · assumption
    wp_seg_sync52 hseg52 (lsρ lsRustDeallocSym)
    refine SepWP.fold (prevVec1_cap1_merge q' capE ptrE (BitVec.ofNat 64 enc.length))
      (by sep_frame) ?_
    wp_done_call52 hcl3
    wp_call hdealloc (q', 24, 8, M.stepEvents (rustDeallocEvents capE.toNat 1) (M.stepEvents evs_drop st))
    conv => arg 4; simp only [← AllocCostModel.stepEvents_append, List.append_assoc]
    let evs_all := evs_drop ++ (rustDeallocEvents capE.toNat 1 ++ rustDeallocEvents 24 8)
    have hfree_all : FreeOnlyEvs evs_all :=
      FreeOnlyEvs.append hfree_drop
        (FreeOnlyEvs.append (freeOnlyEvs_rustDealloc capE.toNat 1) (freeOnlyEvs_rustDealloc 24 8))
    exact serPrev1Tail_placed_epilogue_sepWP out q' cap' ptr' bs
      (M.stepEvents evs_all st)
      (fun sf htr_f hsp_f hcs_f => hQ sf evs_all htr_f hsp_f hcs_f hfree_all)
      hal0
      (by simp only [wp_norm, arm64_norm, *])
      (by simp only [wp_norm, arm64_norm, *])
      (by simp only [wp_norm, arm64_norm, *])
      (by simp only [wp_norm, arm64_norm, *])
      (by simp only [wp_norm, arm64_norm, *])
      (by simp only [okTagVec]; sep_frame)

theorem serPrev1Tail_placed_ok [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits} {H : LibsignalHooks}
    (hC : SerContractsXPlaced M A lim H)
    (hDrop : DropSessionStructureLocal1PlacedOkX M A lim H) :
    SerPrev1PlacedTailStmt M A lim H := by
  intro out q' capE ptrE cap' ptr' o0 o1 o2 o3 bs enc w sess' st ret s0 sm Fx Q Qp
    hQ hal0 hpc hrun hsp htr hx19 hx23 hx24 hvr hcl
  exact SepWPpLsCl.of_sepWP_ret (pl := lsmpl) (Qp := Qp)
    (serPrev1Tail_placed_sepWP hC hDrop out q' capE ptrE cap' ptr' o0 o1 o2 o3 bs enc w sess' st
      hQ hal0 hpc hrun hsp htr hx19 hx23 hx24 hvr hcl)
    hcl

end TailProof

/-! ## Pool-threaded heap-folding helpers -/

theorem prevVecAt_one_fold_ser {M : AllocCostModel} (A : RustCliAllocBudget M)
    (r cap q : BitVec 64) (enc : List (BitVec 8))
    (h : cap ≠ 0#64 ∧ cap.toNat * 24 < 2 ^ 63 ∧ q ≠ 0#64) :
    ((r ↦₆₄ cap) ∗ ((r + 8#64) ↦₆₄ q) ∗ ((r + 16#64) ↦₆₄ 1#64) ∗
        A.live q (cap.toNat * 24) 8 ∗ arrayAt (prevElem A.repAlloc) 24 q [enc] ∗
        memRegion (q + 24#64) ((cap.toNat - 1) * 24)) ⊢
      prevVecAt A.repAlloc r cap q [enc] := by
  rw [prevVecAt_one_cells_ser A r cap q enc]
  exact sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
    (Entails.pure_right h (Entails.refl _))))

theorem prevVecAt_one_pure_first {M : AllocCostModel} (A : RustCliAllocBudget M)
    (r cap q : BitVec 64) (enc : List (BitVec 8)) :
    prevVecAt A.repAlloc r cap q [enc] =
      ⌜cap ≠ 0#64 ∧ cap.toNat * 24 < 2 ^ 63 ∧ q ≠ 0#64⌝ ∗
        ((r ↦₆₄ cap) ∗ ((r + 8#64) ↦₆₄ q) ∗ ((r + 16#64) ↦₆₄ 1#64) ∗
          A.live q (cap.toNat * 24) 8 ∗ arrayAt (prevElem A.repAlloc) 24 q [enc] ∗
          memRegion (q + 24#64) ((cap.toNat - 1) * 24)) := by
  rw [prevVecAt_one_cells_ser A r cap q enc]
  sep_ac_rfl

theorem prevVecAt_800_open {M : AllocCostModel} (A : RustCliAllocBudget M)
    (sp q : BitVec 64) (enc : List (BitVec 8)) :
    prevVecAt A.repAlloc (sp - 800#64) 1#64 q [enc] =
      (∃∗ capE : BitVec 64, ∃∗ ptrE : BitVec 64,
        ⌜q ≠ 0#64⌝ ∗
          (((sp - 800#64) ↦₆₄ 1#64) ∗ ((sp - 792#64) ↦₆₄ q) ∗ ((sp - 784#64) ↦₆₄ 1#64) ∗
            A.live q 24 8 ∗
            (q ↦₆₄ capE) ∗ ((q + 8#64) ↦₆₄ ptrE) ∗
            ((q + 16#64) ↦₆₄ BitVec.ofNat 64 enc.length) ∗
            vecU8Buf A.repAlloc capE ptrE enc)) := by
  have e8 : sp - 800#64 + 8#64 = sp - 792#64 := bv_sub_add_lit sp 800#64 8#64
  have e16 : sp - 800#64 + 16#64 = sp - 784#64 := bv_sub_add_lit sp 800#64 16#64
  rw [prevVecAt_cap1_cells A (sp - 800#64) q enc, e8, e16]
  unfold vecU8
  simp only [vecU8At_cells A, sepExists_sepConj_right]
  refine ProofLib.sepExists_congr fun capE => ProofLib.sepExists_congr fun ptrE => ?_
  sep_ac_rfl

theorem memRegion_out32_pool_stack_swap {M : AllocCostModel} (A : RustCliAllocBudget M)
    (lim : BudgetLimits) (st : M.σ) (s : State) (out sp : BitVec 64) :
    (memRegion out 32 ∗ A.pool lim st s ∗ stackAt sp serializeStackX) =
      (A.pool lim st s ∗ (memRegion out 32 ∗ stackAt sp serializeStackX)) := by
  sep_ac_rfl

theorem vecU8At_init_byte_432_cap {M : AllocCostModel} (A : RustCliAllocBudget M)
    (sp ptr c : BitVec 64) (n : Nat) (b0 : BitVec 8)
    (hc : c.toNat = n) (hpos : 1 ≤ n) (hlt : n < 2 ^ 32) (hptr : ptr ≠ 0) :
    (((sp - 432#64) ↦₆₄ c) ∗ ((sp - 424#64) ↦₆₄ ptr) ∗ ((sp - 416#64) ↦₆₄ 1#64) ∗
      A.live ptr n 1 ∗ (ptr ↦₈ b0) ∗ memRegion (ptr + 1#64) (n - 1)) ⊢
      vecU8At A.repAlloc (sp - 432#64) (BitVec.ofNat 64 n) ptr [b0] := by
  have e : c = BitVec.ofNat 64 n := by
    apply BitVec.eq_of_toNat_eq
    rw [hc, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  subst e
  have hv := vecU8At_init_byte_432X A.repAlloc sp ptr n b0 hpos hlt hptr
  rwa [A.repAlloc_live_norm] at hv

theorem k5_fold_q {img : Obj.Image} {prog : Program} {ret : BitVec 64} {s : State}
    {Q Qp : State → SepProp → Prop} {M : AllocCostModel} (A : RustCliAllocBudget M)
    (q capE ptrE : BitVec 64) (enc : List (BitVec 8)) {P F : SepProp}
    (hP : P = ((q ↦₆₄ capE) ∗ ((q + 8#64) ↦₆₄ ptrE) ∗
      ((q + 16#64) ↦₆₄ BitVec.ofNat 64 enc.length) ∗ vecU8Buf A.repAlloc capE ptrE enc) ∗ F)
    (h : SepWPpIn img prog ret s (vecU8At A.repAlloc q capE ptrE enc ∗ F) Q Qp) :
    SepWPpIn img prog ret s P Q Qp := by
  subst hP
  exact SepWPpIn.weaken_pre
    (sepConj_mono_left (Entails.of_eq (vecU8At_cells A q capE ptrE enc).symm)) h

theorem k5_fold_q_placed {pl : Obj.MultiPlacement} {prog : Program} {ret : BitVec 64} {s : State}
    {Q Qp : State → SepProp → Prop} {M : AllocCostModel} (A : RustCliAllocBudget M)
    (q capE ptrE : BitVec 64) (enc : List (BitVec 8)) {P F : SepProp}
    (hP : P = ((q ↦₆₄ capE) ∗ ((q + 8#64) ↦₆₄ ptrE) ∗
      ((q + 16#64) ↦₆₄ BitVec.ofNat 64 enc.length) ∗ vecU8Buf A.repAlloc capE ptrE enc) ∗ F)
    (h : SepWPpLsCl pl prog ret s (vecU8At A.repAlloc q capE ptrE enc ∗ F) Q Qp) :
    SepWPpLsCl pl prog ret s P Q Qp := by
  subst hP
  exact SepWPpLsCl.weaken_pre
    (sepConj_mono_left (Entails.of_eq (vecU8At_cells A q capE ptrE enc).symm)) h

theorem k5_fold_q_sepWP {prog : Program} {target : BitVec 64} {s : State}
    {Q : State → SepProp → Prop} {M : AllocCostModel} (A : RustCliAllocBudget M)
    (q capE ptrE : BitVec 64) (enc : List (BitVec 8)) {P F : SepProp}
    (hP : P = ((q ↦₆₄ capE) ∗ ((q + 8#64) ↦₆₄ ptrE) ∗
      ((q + 16#64) ↦₆₄ BitVec.ofNat 64 enc.length) ∗ vecU8Buf A.repAlloc capE ptrE enc) ∗ F)
    (h : SepWP prog target s (vecU8At A.repAlloc q capE ptrE enc ∗ F) Q) :
    SepWP prog target s P Q := by
  subst hP
  exact SepWP.weaken_pre
    (sepConj_mono_left (Entails.of_eq (vecU8At_cells A q capE ptrE enc).symm)) h

end LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Over.CloseSerBodyBBudget
