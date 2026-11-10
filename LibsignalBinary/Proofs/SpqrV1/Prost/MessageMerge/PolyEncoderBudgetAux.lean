/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SpqrV1.Prost.MessageMerge.PolyDecoderBudgetAux
public import LibsignalBinary.Proofs.SpqrV1.Prost.MessageMerge.PolyEncoder
public import LibsignalBinary.Proofs.SpqrV1.Prost.MessageMerge.PolyEncoderClPlaced
public meta import LibsignalBinary.Proofs.Placed.BudgetPoolSync -- shake: keep
public meta import LibsignalBinary.Proofs.Placed.BudgetVmSteps -- shake: keep
import LibsignalBinary.Proofs.Common.SharedHelpers
meta import LibsignalBinary.Proofs.Common.SharedHelpers -- shake: keep
import LibsignalBinary.Proofs.ProtoCodecRoundTrip
import LibsignalBinary.Proofs.SpqrV1.Prost.MessageMerge.EpochDirection
import LibsignalBinary.Proofs.TripleRatchet.Prost.BytesMerge.Phase1
import GeneratedLean.LibsignalSessionCode -- shake: keep
import LibsignalBinary.Specifications.LibsignalSpqrV1.Wire -- shake: keep

/-!
# Shared Exit/Skip & Tag-1 Budget Lemmas for `PolynomialEncoder::merge` (Block `297`)

Provides `PolyEncoderMergeEnv` fuel helpers, relocatable `[LibsignalPlacement]` shared error-exit
and unknown-tag skip lemmas, and the `withLsCodeRoLoaded` tag-1 (`idx`) varint step on Block `297`.
-/

@[expose] public section

set_option autoImplicit false

namespace LibsignalBinary.Proofs.SpqrV1.Prost.MessageMerge.PolyEncoderBudgetAux

open Arm64 ProofLib SepProp
open scoped CryptoVerification
open scoped CryptoVerification.CodeLayout
open scoped CryptoVerification.SpqrV1.Prost.MessageMerge
open CryptoVerification (LibsignalHooks LibsignalPlacement lsmpl)
open CryptoVerification.LibsignalProtoCodec
  (WireType decodeVarint decodeVarint_length skipField skip_length)
open CryptoVerification.LibsignalTripleRatchet
  (KindNoHeap LibsignalCodeRoLoaded decodeErrorAtStackLen withLsCodeRoLoaded)
open CryptoVerification.LibsignalTripleRatchet.Prost
  (IsDropSuffix pointsTo64_pair_entails_memRegion16 pointsToBytes_prefix_join
   sliceCursorAfter sliceCursorAfter_eq_split sliceCursorAfter_join sliceCursorAt)
open CryptoVerification.LibsignalSpqrV1 (PolynomialEncoder growOneVecU8Name)
open CryptoVerification.LibsignalSpqrV1.Proto (mergeMessage)
open CryptoVerification.SpqrV1.Poly
  (protoPolynomialEncoderAt protoPolynomialEncoderIdxOff)
open CryptoVerification.SpqrV1.Prost.MessageMerge
  (PolyCalleeSaved PolyEncoderMergeGhost SepWPp.call_frame_lscro
   SepWPp.of_sepWP_lscro WppPost blkPC_297 blkPl_297 bv64_add_zero bv64_ofNat_add_one
   codecWireTypeToProto decodeErrorWith_one_entails_le1 decodeErrorWith_zero_entails_le1
   extractLsb'_append64_0 extractLsb'_append64_64 iwt_cbnz_true_of_ne_varint
   madd_24_eq madd_24_eq' memRegion8_memRegion40_entails_48_160 memRegion_48_cells1_160
   memRegion_48_wtErr160 pointsTo64_memRegion40_entails_48_160 polyBelowStack
   polyBelow_decodeErrorHook polyBelow_decodeErrorHook_entails polyBelow_decodeVarint2
   polyBelow_decodeVarint2_entails polyEncoderToProto polySavedRegs polySavedRegsAny
   protoPolynomialEncoderAt_entails_exists setWidth8_ofNat64_wt stackAt_polyMerge_epilogue
   wtErr160_entails_memRegion40)
open LibsignalBinary.Heap
  (AllocCostModel AllocEvent BudgetLimits FitsEnv RustCliAllocBudget)
open LibsignalBinary.Heap.SpecBudget (DecodeErrorFromEnv decodeErrorFromBudgetSpec)
open LibsignalBinary.Proofs.Placed.BudgetPoolSync (hooksException sepWP_seg_ls_vm)
open LibsignalBinary.Proofs.SpqrV1.Prost.MessageMerge.ChunkedDefsBudget
  (DecodeErrorPushMergeEnv decodeErrorPushMergeBudgetSpec)
open LibsignalBinary.Proofs.SpqrV1.Prost.MessageMerge.PolyCommonBudget
  (FitsEnv.polyMergeLoop_head FitsEnv.polyMergeLoop_mono FitsEnv.polyMergeLoop_split
   FitsEnv.polyMergeLoop_tail PolyEncoderMergeEnv PolyEncoderMergePostEnv PolyMergeIterEnv
   PolyMergeLoopEnv WppBudgetPanic polyEncoderCapBound polyEncoderErrFrame
   polyEncoderLoopPre polyEncoderMergeSpec polyEncoderMergeSpecOfEnv wppBudgetPanic_false)
open LibsignalBinary.Proofs.SpqrV1.Prost.MessageMerge.PolyDecoderBudgetAux
  (decodeVarint2Stack_eq decodeVarint2_pool_of_some)
open LibsignalBinary.Proofs.SpqrV1.Varint.DecodeVarint2Budget
  (DecodeVarint2Env decodeVarint2Spec decodeVarint2SpecGen)
open LibsignalBinary.Proofs.SpqrV1.Varint.SkipField3Budget (SkipField3Env skipField3Spec)
open LibsignalBinary.Proofs.TripleRatchet.Prost.DefsBudget (SkipFieldEnv skipFieldEventsCore)

private theorem sp_setMem_pre (s : State) (m : Memory) : (s.setMem m).sp = s.sp := by cases s; rfl
private theorem pc_setMem_pre (s : State) (m : Memory) : (s.setMem m).pc = s.pc := by cases s; rfl
private theorem status_setMem_pre (s : State) (m : Memory) : (s.setMem m).status = s.status := by cases s; rfl
private theorem pstate_setMem_pre (s : State) (m : Memory) : (s.setMem m).pstate = s.pstate := by cases s; rfl
private theorem trace_setMem_pre (s : State) (m : Memory) : (s.setMem m).trace = s.trace := by cases s; rfl
private theorem readReg64_setMem_pre (s : State) (m : Memory) (r : Reg) : (s.setMem m).readReg64 r = s.readReg64 r := by cases s; rfl
private theorem readReg32_setMem_pre (s : State) (m : Memory) (r : Reg) : (s.setMem m).readReg32 r = s.readReg32 r := by cases s; rfl
private theorem readReg_setMem_pre (s : State) (m : Memory) (w : Width) (r : Reg) : (s.setMem m).readReg w r = s.readReg w r := by cases s; rfl
private theorem calleeSavedVRegs_setMem_pre (s : State) (m : Memory) : calleeSavedVRegs (s.setMem m) = calleeSavedVRegs s := by cases s; rfl

attribute [local irreducible] Program.fetch Program.externAt?
attribute [local arm64_norm]
  bv_sub_add_lit BitVec.toNat_zero growOneVecU8Name bv64_add_zero bv64_ofNat_add_one
  madd_24_eq madd_24_eq' extractLsb'_append64_0 extractLsb'_append64_64
attribute [local arm64_norm ↓, local wp_norm ↓]
  sp_setMem_pre pc_setMem_pre status_setMem_pre pstate_setMem_pre trace_setMem_pre
  readReg64_setMem_pre readReg32_setMem_pre readReg_setMem_pre calleeSavedVRegs_setMem_pre

/-! ## 1. Fuel & PostEnv Helpers for `PolynomialEncoder::merge` -/

theorem polyEncoderMergePostEnv_of_none {x : PolyEncoderMergeGhost} {f : Nat}
    {evs : List AllocEvent}
    (hnone : (mergeMessage PolynomialEncoder.mergeField (codecWireTypeToProto x.wt) x.msg x.bs 98).toOption = none)
    (hf : f ≤ 2 * x.bs.length + 2)
    (hevs : PolyMergeLoopEnv f x.bs.length (polyEncoderCapBound x) evs) :
    PolyEncoderMergePostEnv x evs := by
  dsimp only [PolyEncoderMergePostEnv]
  rw [hnone]
  exact hevs.mono_fuel hf

theorem polyEncoderMergePostEnv_of_some {x : PolyEncoderMergeGhost} {m' : PolynomialEncoder}
    {rest : List (BitVec 8)} {evs : List AllocEvent}
    (hsome : (mergeMessage PolynomialEncoder.mergeField (codecWireTypeToProto x.wt) x.msg x.bs 98).toOption = some (m', rest))
    (hevs : PolyMergeLoopEnv (2 * (x.bs.length - rest.length)) x.bs.length (polyEncoderCapBound x) evs) :
    PolyEncoderMergePostEnv x evs := by
  dsimp only [PolyEncoderMergePostEnv]
  rw [hsome]
  exact hevs

theorem fitsEnv_rem_of_encoder_loop {M : AllocCostModel} {lim : BudgetLimits} {st0 st_cur : M.σ}
    {x : PolyEncoderMergeGhost} {f_acc f_rem : Nat} {evs_acc : List AllocEvent}
    (hFit0 : FitsEnv M lim st0 (PolyEncoderMergeEnv x))
    (hf : f_acc + f_rem ≤ 2 * x.bs.length + 2)
    (hevs_acc : PolyMergeLoopEnv f_acc x.bs.length (polyEncoderCapBound x) evs_acc)
    (hst_cur : st_cur = M.stepEvents evs_acc st0) :
    FitsEnv M lim st_cur (PolyMergeLoopEnv f_rem x.bs.length (polyEncoderCapBound x)) := by
  subst hst_cur
  have h1 : FitsEnv M lim st0
      (PolyMergeLoopEnv (f_acc + f_rem) x.bs.length (polyEncoderCapBound x)) :=
    FitsEnv.polyMergeLoop_mono hf (Nat.le_refl _) (Nat.le_refl _) hFit0
  exact FitsEnv.polyMergeLoop_split hevs_acc h1

/-! ## 2. Envelope-Parameterized & Concrete Shared Exit/Skip Lemmas (Block `297`) -/

set_option maxRecDepth 200000 in
set_option maxHeartbeats 400000 in
set_option linter.unusedSimpArgs false in
/-- Placed shared exit from `+0x07c` (`(blkPl_297).base + 124#64`) when `x1 = err ≠ 0#64` owns
`decodeErrorAtStackLen A.repAlloc err 0`. -/
theorem polyEncoder_err0_ret_exit_placed [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {H : LibsignalHooks}
    {PreEnv PostEnv : PolyEncoderMergeGhost → List AllocEvent → Prop}
    {x : PolyEncoderMergeGhost} {st0 st_cur : M.σ} {R : SepProp}
    {s0 s : State} {m : PolynomialEncoder} {err : BitVec 64}
    (hnone : (mergeMessage PolynomialEncoder.mergeField (codecWireTypeToProto x.wt) x.msg x.bs 98).toOption = none)
    (hevs : ∃ evs, PostEnv x evs ∧ st_cur = M.stepEvents evs st0)
    (hsp_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hpc : s.pc = (blkPl_297).base + 124#64)
    (hrun : s.status = .Running) (hsp : s.sp = s0.sp - 160#64) (htr : s.trace = s0.trace)
    (hx1 : s.readReg64 (Reg.gpr 1#5) = err) (herr : err ≠ 0#64) (hcs : PolyCalleeSaved s0 s) :
    SepWPp ((blkPC_297).rebase (blkPl_297).base H) (s0.readReg64 Reg.lr) s
      (decodeErrorAtStackLen A.repAlloc err 0 ∗ stackAt (s0.sp - 160#64) polyBelowStack ∗
        memRegion (s0.sp - 160#64) 32 ∗ memRegion (s0.sp - 128#64) 48 ∗
        polyEncoderErrFrame A lim st_cur s0 s x.msgPtr x.bufRef x.slot x.ptr m x.bs)
      (WppPost (polyEncoderMergeSpecOfEnv A lim PreEnv PostEnv) (x, st0) R s0)
      (WppBudgetPanic (polyEncoderMergeSpecOfEnv A lim PreEnv PostEnv) (x, st0) R s0) := by
  obtain ⟨hx26, hx27, hx28, hvregs⟩ := hcs
  rcases hevs with ⟨evs, hevs_post, rfl⟩
  apply SepWPp.of_sepWP_ret
  unfold WppPost polyEncoderMergeSpecOfEnv
  simp only [hnone, polyEncoderErrFrame, polySavedRegsAny, polySavedRegs,
    sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc, arm64_norm, htr, hsp, hx1]
  apply SepWP.exists_elim; intro v_pad
  apply SepWP.fold (decodeErrorWith_zero_entails_le1 A.repAlloc err) (by sep_focus)
  apply SepWP.fold (protoPolynomialEncoderAt_entails_exists A.repAlloc x.msgPtr m) (by sep_focus)
  wp_steps_sync_pool (s0.readReg64 Reg.lr)
  simp only [State.setMem_setMem]
  apply SepWP.fold (stackAt_polyMerge_epilogue s0.sp s0 v_pad) (by unfold polySavedRegs; sep_focus)
  wp_done

set_option maxRecDepth 200000 in
set_option maxHeartbeats 400000 in
set_option linter.unusedSimpArgs false in
/-- Code-loaded placed shared exit from `+0x070` (`(blkPl_297).base + 112#64`): calls
`DecodeError::from` on `(s0.sp - 128#64, w, st_cur)` and returns at `+0x078..+0x098`. -/
theorem polyEncoder_from_err_exit_placed [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {H : LibsignalHooks}
    {PreEnv PostEnv : PolyEncoderMergeGhost → List AllocEvent → Prop}
    (hFromCall : subroutine_ok ((blkPC_297).rebase (blkPl_297).base H) (lsmpl.base 261)
      (withLsCodeRoLoaded lsmpl (decodeErrorFromBudgetSpec M A lim)))
    {x : PolyEncoderMergeGhost} {st0 st_cur : M.σ} {R : SepProp}
    {s0 s : State} {m : PolynomialEncoder} {w : BitVec 64}
    (hnone : (mergeMessage PolynomialEncoder.mergeField (codecWireTypeToProto x.wt) x.msg x.bs 98).toOption = none)
    (hw : KindNoHeap w)
    (hfits_from : FitsEnv M lim st_cur DecodeErrorFromEnv)
    (hevs_from : ∀ evs_f, DecodeErrorFromEnv evs_f →
      ∃ evs, PostEnv x evs ∧ M.stepEvents evs_f st_cur = M.stepEvents evs st0)
    (hsp_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hpc : s.pc = (blkPl_297).base + 112#64)
    (hrun : s.status = .Running) (hsp : s.sp = s0.sp - 160#64)
    (htr : s.trace = s0.trace) (hcs : PolyCalleeSaved s0 s) (hinv : LibsignalCodeRoLoaded lsmpl s.mem) :
    SepWPp ((blkPC_297).rebase (blkPl_297).base H) (s0.readReg64 Reg.lr) s
      (((s0.sp - 128#64) ↦₆₄ w) ∗ memRegion (s0.sp - 120#64) 40 ∗
        stackAt (s0.sp - 160#64) polyBelowStack ∗ memRegion (s0.sp - 160#64) 32 ∗
        polyEncoderErrFrame A lim st_cur s0 s x.msgPtr x.bufRef x.slot x.ptr m x.bs)
      (WppPost (polyEncoderMergeSpecOfEnv A lim PreEnv PostEnv) (x, st0) R s0)
      (WppBudgetPanic (polyEncoderMergeSpecOfEnv A lim PreEnv PostEnv) (x, st0) R s0) := by
  obtain ⟨hx26, hx27, hx28, hvregs⟩ := hcs
  apply SepWPp.of_sepWP_lscro (mid := lsmpl.base 261) hinv
  conv => arg 4; rw [polyBelow_decodeErrorHook s0.sp, polyEncoderErrFrame]; simp only [sepConj_assoc]
  wp_steps_sync_pool (lsmpl.base 261)
  simp only [State.setMem_setMem]
  wp_reach; intro hinv
  refine SepWPp.call_frame_lscro (spec := decodeErrorFromBudgetSpec M A lim)
    (x := (s0.sp - 128#64, w, st_cur))
    (ret_pc := (blkPl_297).base + 120#64) hFromCall hinv
    (by simp only [arm64_norm]) (by simp only [arm64_norm, hrun])
    (by simp only [State.spAligned, hsp, arm64_norm]; exact hsp_align) (by simp only [arm64_norm])
    rfl ⟨by simp only [arm64_norm, hsp], hw, hfits_from⟩ (by sep_focus)
    (fun _ _ _ _ hex => False.elim (not_satisfies_false_sepConj hex))
    (fun _ _ => wppBudgetPanic_false) ?_
  intro sm hpcm hrunm hspm hcsm _hinvm; simp only [CalleeSavedPreserved] at hcsm
  obtain ⟨_, _, _, _, _, _, _, hx26_m, hx27_m, hx28_m, _, hvregs_m⟩ := hcsm
  simp (config := { decide := true }) only [arm64_norm, hsp, hx26, hx27, hx28, hvregs]
    at hpcm hspm hx26_m hx27_m hx28_m hvregs_m
  apply SepWPp.of_sepWP_ret
  unfold WppPost polyEncoderMergeSpecOfEnv
  simp only [decodeErrorFromBudgetSpec, hnone, polySavedRegsAny, polySavedRegs,
    sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc, htr, hsp, hspm]
  apply SepWP.exists_elim; intro v_pad
  apply SepWP.exists_elim; intro evs_f
  wp_focus_pure; rintro ⟨_herr, htrm⟩
  wp_focus_pure; intro hevs_f
  obtain ⟨evs, hevs_post, hst_eq⟩ := hevs_from evs_f hevs_f
  conv => arg 4; simp only [hst_eq, arm64_norm]
  apply SepWP.fold (polyBelow_decodeErrorHook_entails s0.sp) (by sep_focus)
  apply SepWP.fold (memRegion8_memRegion40_entails_48_160 s0.sp) (by sep_focus)
  wp_steps_sync_pool (s0.readReg64 Reg.lr)
  simp only [State.setMem_setMem]
  apply SepWP.fold (decodeErrorWith_zero_entails_le1 A.repAlloc _) (by sep_focus)
  apply SepWP.fold (protoPolynomialEncoderAt_entails_exists A.repAlloc x.msgPtr m) (by sep_focus)
  apply SepWP.fold (stackAt_polyMerge_epilogue s0.sp s0 v_pad) (by unfold polySavedRegs; sep_focus)
  wp_done

set_option maxRecDepth 200000 in
set_option maxHeartbeats 400000 in
set_option linter.unusedSimpArgs false in
/-- Code-loaded placed shared exit from `+0x344` (`(blkPl_297).base + 836#64`): calls
`DecodeError::push` on `(s0.sp - 128#64, err, 0, st_cur)` and returns at `+0x348..+0x34c` +
`+0x07c..+0x098`. -/
theorem polyEncoder_push_err_exit_placed [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {H : LibsignalHooks}
    {PreEnv PostEnv : PolyEncoderMergeGhost → List AllocEvent → Prop}
    (hPushCall : subroutine_ok ((blkPC_297).rebase (blkPl_297).base H) (lsmpl.base 257)
      (withLsCodeRoLoaded lsmpl (decodeErrorPushMergeBudgetSpec M A lim)))
    {x : PolyEncoderMergeGhost} {st0 st_cur : M.σ} {R : SepProp}
    {s0 s : State} {m : PolynomialEncoder} {err : BitVec 64}
    (hnone : (mergeMessage PolynomialEncoder.mergeField (codecWireTypeToProto x.wt) x.msg x.bs 98).toOption = none)
    (herr : err ≠ 0#64)
    (hfits_push : FitsEnv M lim st_cur (DecodeErrorPushMergeEnv 0))
    (hevs_push : ∀ evs_p, DecodeErrorPushMergeEnv 0 evs_p →
      ∃ evs, PostEnv x evs ∧ M.stepEvents evs_p st_cur = M.stepEvents evs st0)
    (hsp_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hpc : s.pc = (blkPl_297).base + 836#64)
    (hrun : s.status = .Running) (hsp : s.sp = s0.sp - 160#64)
    (htr : s.trace = s0.trace) (hx0 : s.readReg64 (Reg.gpr 0#5) = s0.sp - 128#64)
    (hcs : PolyCalleeSaved s0 s) (hinv : LibsignalCodeRoLoaded lsmpl s.mem) :
    SepWPp ((blkPC_297).rebase (blkPl_297).base H) (s0.readReg64 Reg.lr) s
      (((s0.sp - 128#64) ↦₆₄ err) ∗ decodeErrorAtStackLen A.repAlloc err 0 ∗
        memRegion (s0.sp - 120#64) 40 ∗ stackAt (s0.sp - 160#64) polyBelowStack ∗
        memRegion (s0.sp - 160#64) 32 ∗
        polyEncoderErrFrame A lim st_cur s0 s x.msgPtr x.bufRef x.slot x.ptr m x.bs)
      (WppPost (polyEncoderMergeSpecOfEnv A lim PreEnv PostEnv) (x, st0) R s0)
      (WppBudgetPanic (polyEncoderMergeSpecOfEnv A lim PreEnv PostEnv) (x, st0) R s0) := by
  obtain ⟨hx26, hx27, hx28, hvregs⟩ := hcs
  apply SepWPp.of_sepWP_lscro (mid := lsmpl.base 257) hinv
  conv => arg 4; rw [polyBelow_decodeErrorHook s0.sp, polyEncoderErrFrame]; simp only [sepConj_assoc]
  wp_steps_sync_pool (lsmpl.base 257)
  simp only [State.setMem_setMem]
  wp_reach; intro hinv
  refine SepWPp.call_frame_lscro (spec := decodeErrorPushMergeBudgetSpec M A lim)
    (x := (s0.sp - 128#64, err, 0, st_cur))
    (ret_pc := (blkPl_297).base + 840#64) hPushCall hinv
    (by simp only [arm64_norm]) (by simp only [arm64_norm, hrun])
    (by simp only [State.spAligned, hsp, arm64_norm]; exact hsp_align) (by simp only [arm64_norm])
    rfl ⟨by simp only [arm64_norm, hsp, hx0], by decide, hfits_push⟩ (by sep_focus)
    (fun _ _ _ _ hex => False.elim (not_satisfies_false_sepConj hex))
    (fun _ _ => wppBudgetPanic_false) ?_
  intro sm hpcm hrunm hspm hcsm _hinvm; simp only [CalleeSavedPreserved] at hcsm
  obtain ⟨_, _, _, _, _, _, _, hx26_m, hx27_m, hx28_m, _, hvregs_m⟩ := hcsm
  simp (config := { decide := true }) only [arm64_norm, hsp, hx26, hx27, hx28, hvregs]
    at hpcm hspm hx26_m hx27_m hx28_m hvregs_m
  apply SepWPp.of_sepWP_ret
  unfold WppPost polyEncoderMergeSpecOfEnv
  simp only [decodeErrorPushMergeBudgetSpec, hnone, polySavedRegsAny, polySavedRegs,
    sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc, htr, hsp, hspm]
  apply SepWP.exists_elim; intro v_pad
  apply SepWP.exists_elim; intro evs_p
  wp_focus_pure; intro htrm
  wp_focus_pure; intro hevs_p
  obtain ⟨evs, hevs_post, hst_eq⟩ := hevs_push evs_p hevs_p
  conv => arg 4; simp only [hst_eq, arm64_norm]
  apply SepWP.fold (polyBelow_decodeErrorHook_entails s0.sp) (by sep_focus)
  wp_steps_sync_pool (s0.readReg64 Reg.lr)
  simp only [State.setMem_setMem]
  apply SepWP.fold (decodeErrorWith_one_entails_le1 A.repAlloc err) (by sep_focus)
  apply SepWP.fold (protoPolynomialEncoderAt_entails_exists A.repAlloc x.msgPtr m) (by sep_focus)
  apply SepWP.fold (pointsTo64_memRegion40_entails_48_160 s0.sp err) (by sep_focus)
  apply SepWP.fold (stackAt_polyMerge_epilogue s0.sp s0 v_pad) (by unfold polySavedRegs; sep_focus)
  wp_done

set_option maxRecDepth 200000 in
set_option maxHeartbeats 400000 in
set_option linter.unusedSimpArgs false in
/-- Code-loaded placed step lemma for unknown field tags (`tag ∉ {1, 2, 3}`) at `+0x1d0`
(`(blkPl_297).base + 464#64`). -/
theorem polyEncoder_skip_step_placed [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {H : LibsignalHooks}
    {PreEnv PostEnv : PolyEncoderMergeGhost → List AllocEvent → Prop}
    (hSkipCall : subroutine_ok ((blkPC_297).rebase (blkPl_297).base H) (lsmpl.base 263)
      (withLsCodeRoLoaded lsmpl (skipField3Spec A lim)))
    {x : PolyEncoderMergeGhost} {st0 st_cur : M.σ} {R : SepProp}
    {s0 s : State} {m : PolynomialEncoder} {rest : List (BitVec 8)} {iwt : WireType} {tag limit : Nat}
    (hsp_align : (s0.sp &&& 15#64 == 0#64) = true) (hrest_le : rest.length ≤ x.bs.length)
    (hrest_lt : rest.length < 2 ^ 63) (hrest_suf : IsDropSuffix x.bs rest)
    (htag_lt : tag < 2 ^ 32)
    (hfits_sf : FitsEnv M lim st_cur
      (SkipField3Env ⟨iwt, tag, 97, x.bufRef, x.slot, x.ptr + BitVec.ofNat 64 (x.bs.length - rest.length), rest⟩))
    (hevs_sf_err : skipField (2 * rest.length + 2) 97 tag iwt rest = none →
      ∀ evs_sf,
        SkipField3Env ⟨iwt, tag, 97, x.bufRef, x.slot, x.ptr + BitVec.ofNat 64 (x.bs.length - rest.length), rest⟩ evs_sf →
        ∃ evs, PostEnv x evs ∧ M.stepEvents evs_sf st_cur = M.stepEvents evs st0)
    (hnone_of_sf : skipField (2 * rest.length + 2) 97 tag iwt rest = none →
      (mergeMessage PolynomialEncoder.mergeField (codecWireTypeToProto x.wt) x.msg x.bs 98).toOption = none)
    (hcont : ∀ (rest' : List (BitVec 8)) (s' : State),
      skipField (2 * rest.length + 2) 97 tag iwt rest = some rest' →
      s'.pc = (blkPl_297).base + 164#64 →
      s'.status = .Running → s'.sp = s0.sp - 160#64 → s'.trace = s0.trace →
      s'.readReg64 (Reg.gpr 19#5) = x.bufRef → s'.readReg64 (Reg.gpr 20#5) = x.msgPtr →
      s'.readReg64 (Reg.gpr 21#5) = x.slot → s'.readReg64 (Reg.gpr 22#5) = BitVec.ofNat 64 limit →
      s'.readReg64 (Reg.gpr 23#5) = 1#64 → s'.readReg64 (Reg.gpr 24#5) = 24#64 →
      PolyCalleeSaved s0 s' → LibsignalCodeRoLoaded lsmpl s'.mem →
      SepWPp ((blkPC_297).rebase (blkPl_297).base H) (s0.readReg64 Reg.lr) s'
        (polyEncoderLoopPre A lim st_cur s0 s' x.msgPtr x.bufRef x.slot x.ptr m x.bs rest')
        (WppPost (polyEncoderMergeSpecOfEnv A lim PreEnv PostEnv) (x, st0) R s0)
        (WppBudgetPanic (polyEncoderMergeSpecOfEnv A lim PreEnv PostEnv) (x, st0) R s0))
    (hpc : s.pc = (blkPl_297).base + 464#64)
    (hrun : s.status = .Running) (hsp : s.sp = s0.sp - 160#64) (htr : s.trace = s0.trace)
    (hx0 : s.readReg64 (Reg.gpr 0#5) = BitVec.ofNat 64 iwt.toNat)
    (hx1 : (s.readReg64 (Reg.gpr 1#5)).setWidth 32 = BitVec.ofNat 32 tag)
    (hx19 : s.readReg64 (Reg.gpr 19#5) = x.bufRef) (hx20 : s.readReg64 (Reg.gpr 20#5) = x.msgPtr)
    (hx21 : s.readReg64 (Reg.gpr 21#5) = x.slot) (hx22 : s.readReg64 (Reg.gpr 22#5) = BitVec.ofNat 64 limit)
    (hx23 : s.readReg64 (Reg.gpr 23#5) = 1#64) (hx24 : s.readReg64 (Reg.gpr 24#5) = 24#64)
    (hcs : PolyCalleeSaved s0 s) (hinv : LibsignalCodeRoLoaded lsmpl s.mem) :
    SepWPp ((blkPC_297).rebase (blkPl_297).base H) (s0.readReg64 Reg.lr) s
      (polyEncoderLoopPre A lim st_cur s0 s x.msgPtr x.bufRef x.slot x.ptr m x.bs rest)
      (WppPost (polyEncoderMergeSpecOfEnv A lim PreEnv PostEnv) (x, st0) R s0)
      (WppBudgetPanic (polyEncoderMergeSpecOfEnv A lim PreEnv PostEnv) (x, st0) R s0) := by
  obtain ⟨hx26, hx27, hx28, hvregs⟩ := hcs
  let restPtr : BitVec 64 := x.ptr + BitVec.ofNat 64 (x.bs.length - rest.length)
  apply SepWPp.of_sepWP_lscro (mid := lsmpl.base 263) hinv
  conv => arg 4; rw [polyEncoderLoopPre, sliceCursorAfter_eq_split hrest_le hrest_suf]; simp only [sepConj_assoc]
  wp_steps_sync_pool (lsmpl.base 263)
  simp only [State.setMem_setMem]
  wp_reach; intro hinv
  refine SepWPp.call_frame_lscro (spec := skipField3Spec A lim)
    (x := (⟨iwt, tag, 97, x.bufRef, x.slot, restPtr, rest⟩, st_cur))
    (ret_pc := (blkPl_297).base + 476#64) hSkipCall hinv
    (by simp only [arm64_norm]) (by simp only [arm64_norm, hrun])
    (by simp only [State.spAligned, hsp, arm64_norm]; exact hsp_align) (by simp only [arm64_norm])
    rfl
    ⟨by simp only [arm64_norm, hsp, hx0, setWidth8_ofNat64_wt],
     by simp only [arm64_norm, hsp, hx1], htag_lt,
     by simp only [arm64_norm, hsp, hx19],
     by simp only [arm64_norm, hsp], (by decide : 97 < 2 ^ 32), hrest_lt, hfits_sf⟩
    (by sep_focus)
    (fun _ _ _ _ hex => False.elim (not_satisfies_false_sepConj hex))
    (fun _ _ => wppBudgetPanic_false) ?_
  intro sm hpcm hrunm hspm hcsm hinvm; simp only [CalleeSavedPreserved] at hcsm
  obtain ⟨hx19_m, hx20_m, hx21_m, hx22_m, hx23_m, hx24_m, _, hx26_m, hx27_m, hx28_m, _, hvregs_m⟩ := hcsm
  simp (config := { decide := true }) only [arm64_norm, hsp, hx19, hx20, hx21, hx22, hx23, hx24, hx26, hx27, hx28, hvregs]
    at hpcm hrunm hspm hx19_m hx20_m hx21_m hx22_m hx23_m hx24_m hx26_m hx27_m hx28_m hvregs_m
  cases hsf : skipField (2 * rest.length + 2) 97 tag iwt rest with
  | none =>
    have hnone := hnone_of_sf hsf
    apply SepWPp.of_sepWP_lscro (mid := (blkPl_297).base + 124#64) hinvm
    (conv => arg 4; simp only [skipField3Spec, hsf, sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc])
    apply SepWP.exists_elim; intro evs_sf
    wp_focus_pure; intro htrm
    wp_focus_pure; intro hevs_sf
    wp_focus_pure; intro hsm0
    conv => arg 4; simp only [arm64_norm, hsp]
    have hcbnz : (sm.readReg64 (Reg.gpr 0#5) == 0#64) = false := beq_eq_false_iff_ne.mpr hsm0
    apply SepWP.fold (pointsToBytes_prefix_join hrest_le hrest_suf) (by sep_focus)
    wp_steps_sync_pool ((blkPl_297).base + 124#64)
    simp only [State.setMem_setMem]
    wp_reach; intro _hinvm'
    refine SepWPp.weaken_pre (Entails.of_eq (by dsimp only [polyEncoderErrFrame]; sep_ac_rfl))
      (polyEncoder_err0_ret_exit_placed hnone (hevs_sf_err hsf evs_sf hevs_sf) hsp_align
        (by simp only [arm64_norm]) (by simp only [arm64_norm, hrunm]) (by simp only [arm64_norm, hspm])
        (by simp only [arm64_norm, htrm, htr]) (by simp only [arm64_norm]) hsm0
        ⟨by simp only [arm64_norm, hx26_m], by simp only [arm64_norm, hx27_m],
         by simp only [arm64_norm, hx28_m], by simp only [arm64_norm, hvregs_m]⟩)
  | some rest' =>
    have hrest'_le : rest'.length ≤ rest.length := (skip_length _).1 _ _ _ _ _ hsf
    apply SepWPp.of_sepWP_lscro (mid := (blkPl_297).base + 164#64) hinvm
    (conv => arg 4; simp only [skipField3Spec, hsf, sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc])
    apply SepWP.exists_elim; intro evs_sf
    wp_focus_pure; intro htrm
    wp_focus_pure; intro hevs_sf
    wp_focus_pure; intro hsm0
    have hevs_nil : evs_sf = [] := by
      change SkipFieldEnv _ evs_sf at hevs_sf
      simpa [SkipFieldEnv, skipFieldEventsCore, hsf] using hevs_sf
    subst hevs_nil
    conv => arg 4; dsimp only [AllocCostModel.stepEvents, List.foldl]; simp only [arm64_norm, hsp]
    apply SepWP.fold (sliceCursorAfter_join hrest_le hrest_suf hrest'_le) (by sep_focus)
    wp_steps_sync_pool ((blkPl_297).base + 164#64)
    simp only [State.setMem_setMem]
    wp_reach; intro hinvm'
    refine SepWPp.weaken_pre (Entails.of_eq (by dsimp only [polyEncoderLoopPre]; sep_ac_rfl))
      (hcont rest' _ hsf
        (by simp only [arm64_norm]) (by simp only [arm64_norm, hrunm]) (by simp only [arm64_norm, hspm])
        (by simp only [arm64_norm, htrm, htr])
        (by simp only [arm64_norm, hx19_m]) (by simp only [arm64_norm, hx20_m])
        (by simp only [arm64_norm, hx21_m]) (by simp only [arm64_norm, hx22_m])
        (by simp only [arm64_norm, hx23_m]) (by simp only [arm64_norm, hx24_m])
        ⟨by simp only [arm64_norm, hx26_m], by simp only [arm64_norm, hx27_m],
         by simp only [arm64_norm, hx28_m], by simp only [arm64_norm, hvregs_m]⟩ hinvm')

/-- Code-loaded placed shared exit from `+0x07c` (`(blkPl_297).base + 124#64`) for
`polyEncoderMergeSpec`. -/
theorem polyEncoder_err0_ret_exit_cl_placed [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {H : LibsignalHooks}
    {x : PolyEncoderMergeGhost} {st0 st_cur : M.σ} {R : SepProp}
    {s0 s : State} {m : PolynomialEncoder} {err : BitVec 64}
    {f_acc : Nat} {evs_acc : List AllocEvent}
    (hnone : (mergeMessage PolynomialEncoder.mergeField (codecWireTypeToProto x.wt) x.msg x.bs 98).toOption = none)
    (hf_acc : f_acc ≤ 2 * x.bs.length + 2)
    (hevs_acc : PolyMergeLoopEnv f_acc x.bs.length (polyEncoderCapBound x) evs_acc)
    (hst_cur : st_cur = M.stepEvents evs_acc st0)
    (hsp_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hpc : s.pc = (blkPl_297).base + 124#64)
    (hrun : s.status = .Running) (hsp : s.sp = s0.sp - 160#64) (htr : s.trace = s0.trace)
    (hx1 : s.readReg64 (Reg.gpr 1#5) = err) (herr : err ≠ 0#64) (hcs : PolyCalleeSaved s0 s) :
    SepWPp ((blkPC_297).rebase (blkPl_297).base H) (s0.readReg64 Reg.lr) s
      (decodeErrorAtStackLen A.repAlloc err 0 ∗ stackAt (s0.sp - 160#64) polyBelowStack ∗
        memRegion (s0.sp - 160#64) 32 ∗ memRegion (s0.sp - 128#64) 48 ∗
        polyEncoderErrFrame A lim st_cur s0 s x.msgPtr x.bufRef x.slot x.ptr m x.bs)
      (WppPost (polyEncoderMergeSpec A lim) (x, st0) R s0)
      (WppBudgetPanic (polyEncoderMergeSpec A lim) (x, st0) R s0) :=
  polyEncoder_err0_ret_exit_placed hnone
    ⟨evs_acc, polyEncoderMergePostEnv_of_none hnone hf_acc hevs_acc, hst_cur⟩
    hsp_align hpc hrun hsp htr hx1 herr hcs

/-- Code-loaded placed shared exit from `+0x070` (`(blkPl_297).base + 112#64`): calls
`DecodeError::from` (`261`) and closes `polyEncoderMergeSpec`. -/
theorem polyEncoder_from_err_exit_cl_placed [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {H : LibsignalHooks}
    (hFromCall : subroutine_ok ((blkPC_297).rebase (blkPl_297).base H) (lsmpl.base 261)
      (withLsCodeRoLoaded lsmpl (decodeErrorFromBudgetSpec M A lim)))
    {x : PolyEncoderMergeGhost} {st0 st_cur : M.σ} {R : SepProp}
    {s0 s : State} {m : PolynomialEncoder} {w : BitVec 64}
    {f_acc f_rem : Nat} {evs_acc : List AllocEvent}
    (hnone : (mergeMessage PolynomialEncoder.mergeField (codecWireTypeToProto x.wt) x.msg x.bs 98).toOption = none)
    (hw : KindNoHeap w)
    (hf_rem : 1 ≤ f_rem)
    (hf_tot : f_acc + 1 ≤ 2 * x.bs.length + 2)
    (hevs_acc : PolyMergeLoopEnv f_acc x.bs.length (polyEncoderCapBound x) evs_acc)
    (hst_cur : st_cur = M.stepEvents evs_acc st0)
    (hfits_rem : FitsEnv M lim st_cur
      (PolyMergeLoopEnv f_rem x.bs.length (polyEncoderCapBound x)))
    (hsp_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hpc : s.pc = (blkPl_297).base + 112#64)
    (hrun : s.status = .Running) (hsp : s.sp = s0.sp - 160#64)
    (htr : s.trace = s0.trace) (hcs : PolyCalleeSaved s0 s) (hinv : LibsignalCodeRoLoaded lsmpl s.mem) :
    SepWPp ((blkPC_297).rebase (blkPl_297).base H) (s0.readReg64 Reg.lr) s
      (((s0.sp - 128#64) ↦₆₄ w) ∗ memRegion (s0.sp - 120#64) 40 ∗
        stackAt (s0.sp - 160#64) polyBelowStack ∗ memRegion (s0.sp - 160#64) 32 ∗
        polyEncoderErrFrame A lim st_cur s0 s x.msgPtr x.bufRef x.slot x.ptr m x.bs)
      (WppPost (polyEncoderMergeSpec A lim) (x, st0) R s0)
      (WppBudgetPanic (polyEncoderMergeSpec A lim) (x, st0) R s0) := by
  have hfits1 : FitsEnv M lim st_cur
      (PolyMergeLoopEnv 1 x.bs.length (polyEncoderCapBound x)) :=
    FitsEnv.polyMergeLoop_mono hf_rem (Nat.le_refl _) (Nat.le_refl _) hfits_rem
  refine polyEncoder_from_err_exit_placed hFromCall hnone hw
    (FitsEnv.polyMergeLoop_head (fuel := 0) (fun _ => PolyMergeIterEnv.of_decodeErrorFrom) hfits1)
    (fun evs_f hf =>
      ⟨evs_acc ++ evs_f,
       polyEncoderMergePostEnv_of_none hnone hf_tot
         (hevs_acc.append (PolyMergeLoopEnv.single (fuel := 0) (PolyMergeIterEnv.of_decodeErrorFrom hf))),
       by rw [hst_cur, ← AllocCostModel.stepEvents_append]⟩)
    hsp_align hpc hrun hsp htr hcs hinv

/-- Code-loaded placed shared exit from `+0x344` (`(blkPl_297).base + 836#64`): calls
`DecodeError::push` (`257`) and closes `polyEncoderMergeSpec`. -/
theorem polyEncoder_push_err_exit_cl_placed [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {H : LibsignalHooks}
    (hPushCall : subroutine_ok ((blkPC_297).rebase (blkPl_297).base H) (lsmpl.base 257)
      (withLsCodeRoLoaded lsmpl (decodeErrorPushMergeBudgetSpec M A lim)))
    {x : PolyEncoderMergeGhost} {st0 st_cur : M.σ} {R : SepProp}
    {s0 s : State} {m : PolynomialEncoder} {err : BitVec 64}
    {f_acc f_rem : Nat} {evs_acc : List AllocEvent}
    (hnone : (mergeMessage PolynomialEncoder.mergeField (codecWireTypeToProto x.wt) x.msg x.bs 98).toOption = none)
    (herr : err ≠ 0#64)
    (hf_rem : 1 ≤ f_rem)
    (hf_tot : f_acc + 1 ≤ 2 * x.bs.length + 2)
    (hevs_acc : PolyMergeLoopEnv f_acc x.bs.length (polyEncoderCapBound x) evs_acc)
    (hst_cur : st_cur = M.stepEvents evs_acc st0)
    (hfits_rem : FitsEnv M lim st_cur
      (PolyMergeLoopEnv f_rem x.bs.length (polyEncoderCapBound x)))
    (hsp_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hpc : s.pc = (blkPl_297).base + 836#64)
    (hrun : s.status = .Running) (hsp : s.sp = s0.sp - 160#64)
    (htr : s.trace = s0.trace) (hx0 : s.readReg64 (Reg.gpr 0#5) = s0.sp - 128#64)
    (hcs : PolyCalleeSaved s0 s) (hinv : LibsignalCodeRoLoaded lsmpl s.mem) :
    SepWPp ((blkPC_297).rebase (blkPl_297).base H) (s0.readReg64 Reg.lr) s
      (((s0.sp - 128#64) ↦₆₄ err) ∗ decodeErrorAtStackLen A.repAlloc err 0 ∗
        memRegion (s0.sp - 120#64) 40 ∗ stackAt (s0.sp - 160#64) polyBelowStack ∗
        memRegion (s0.sp - 160#64) 32 ∗
        polyEncoderErrFrame A lim st_cur s0 s x.msgPtr x.bufRef x.slot x.ptr m x.bs)
      (WppPost (polyEncoderMergeSpec A lim) (x, st0) R s0)
      (WppBudgetPanic (polyEncoderMergeSpec A lim) (x, st0) R s0) := by
  have hfits1 : FitsEnv M lim st_cur
      (PolyMergeLoopEnv 1 x.bs.length (polyEncoderCapBound x)) :=
    FitsEnv.polyMergeLoop_mono hf_rem (Nat.le_refl _) (Nat.le_refl _) hfits_rem
  refine polyEncoder_push_err_exit_placed hPushCall hnone herr
    (FitsEnv.polyMergeLoop_head (fuel := 0) (fun _ => PolyMergeIterEnv.of_decodeErrorPush0) hfits1)
    (fun evs_p hp =>
      ⟨evs_acc ++ evs_p,
       polyEncoderMergePostEnv_of_none hnone hf_tot
         (hevs_acc.append (PolyMergeLoopEnv.single (fuel := 0) (PolyMergeIterEnv.of_decodeErrorPush0 hp))),
       by rw [hst_cur, ← AllocCostModel.stepEvents_append]⟩)
    hsp_align hpc hrun hsp htr hx0 hcs hinv

/-- Code-loaded placed step lemma for unknown field tags (`tag ∉ {1, 2, 3}`) at `+0x1d0`
(`(blkPl_297).base + 464#64`) for `polyEncoderMergeSpec`. -/
theorem polyEncoder_skip_step_cl_placed [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {H : LibsignalHooks}
    (hSkipCall : subroutine_ok ((blkPC_297).rebase (blkPl_297).base H) (lsmpl.base 263)
      (withLsCodeRoLoaded lsmpl (skipField3Spec A lim)))
    {x : PolyEncoderMergeGhost} {st0 st_cur : M.σ} {R : SepProp}
    {s0 s : State} {m : PolynomialEncoder} {rest : List (BitVec 8)} {iwt : WireType} {tag limit : Nat}
    {f_acc f_rem : Nat} {evs_acc : List AllocEvent}
    (hsp_align : (s0.sp &&& 15#64 == 0#64) = true) (hrest_le : rest.length ≤ x.bs.length)
    (hrest_lt : rest.length < 2 ^ 63) (hrest_suf : IsDropSuffix x.bs rest)
    (htag_lt : tag < 2 ^ 32)
    (hf_rem : 1 ≤ f_rem)
    (hf_tot : f_acc + 1 ≤ 2 * x.bs.length + 2)
    (hevs_acc : PolyMergeLoopEnv f_acc x.bs.length (polyEncoderCapBound x) evs_acc)
    (hst_cur : st_cur = M.stepEvents evs_acc st0)
    (hfits_rem : FitsEnv M lim st_cur
      (PolyMergeLoopEnv f_rem x.bs.length (polyEncoderCapBound x)))
    (hnone_of_sf : skipField (2 * rest.length + 2) 97 tag iwt rest = none →
      (mergeMessage PolynomialEncoder.mergeField (codecWireTypeToProto x.wt) x.msg x.bs 98).toOption = none)
    (hcont : ∀ (rest' : List (BitVec 8)) (s' : State),
      skipField (2 * rest.length + 2) 97 tag iwt rest = some rest' →
      s'.pc = (blkPl_297).base + 164#64 →
      s'.status = .Running → s'.sp = s0.sp - 160#64 → s'.trace = s0.trace →
      s'.readReg64 (Reg.gpr 19#5) = x.bufRef → s'.readReg64 (Reg.gpr 20#5) = x.msgPtr →
      s'.readReg64 (Reg.gpr 21#5) = x.slot → s'.readReg64 (Reg.gpr 22#5) = BitVec.ofNat 64 limit →
      s'.readReg64 (Reg.gpr 23#5) = 1#64 → s'.readReg64 (Reg.gpr 24#5) = 24#64 →
      PolyCalleeSaved s0 s' → LibsignalCodeRoLoaded lsmpl s'.mem →
      SepWPp ((blkPC_297).rebase (blkPl_297).base H) (s0.readReg64 Reg.lr) s'
        (polyEncoderLoopPre A lim st_cur s0 s' x.msgPtr x.bufRef x.slot x.ptr m x.bs rest')
        (WppPost (polyEncoderMergeSpec A lim) (x, st0) R s0)
        (WppBudgetPanic (polyEncoderMergeSpec A lim) (x, st0) R s0))
    (hpc : s.pc = (blkPl_297).base + 464#64)
    (hrun : s.status = .Running) (hsp : s.sp = s0.sp - 160#64) (htr : s.trace = s0.trace)
    (hx0 : s.readReg64 (Reg.gpr 0#5) = BitVec.ofNat 64 iwt.toNat)
    (hx1 : (s.readReg64 (Reg.gpr 1#5)).setWidth 32 = BitVec.ofNat 32 tag)
    (hx19 : s.readReg64 (Reg.gpr 19#5) = x.bufRef) (hx20 : s.readReg64 (Reg.gpr 20#5) = x.msgPtr)
    (hx21 : s.readReg64 (Reg.gpr 21#5) = x.slot) (hx22 : s.readReg64 (Reg.gpr 22#5) = BitVec.ofNat 64 limit)
    (hx23 : s.readReg64 (Reg.gpr 23#5) = 1#64) (hx24 : s.readReg64 (Reg.gpr 24#5) = 24#64)
    (hcs : PolyCalleeSaved s0 s) (hinv : LibsignalCodeRoLoaded lsmpl s.mem) :
    SepWPp ((blkPC_297).rebase (blkPl_297).base H) (s0.readReg64 Reg.lr) s
      (polyEncoderLoopPre A lim st_cur s0 s x.msgPtr x.bufRef x.slot x.ptr m x.bs rest)
      (WppPost (polyEncoderMergeSpec A lim) (x, st0) R s0)
      (WppBudgetPanic (polyEncoderMergeSpec A lim) (x, st0) R s0) := by
  have hfits1 : FitsEnv M lim st_cur
      (PolyMergeLoopEnv 1 x.bs.length (polyEncoderCapBound x)) :=
    FitsEnv.polyMergeLoop_mono hf_rem (Nat.le_refl _) (Nat.le_refl _) hfits_rem
  refine polyEncoder_skip_step_placed hSkipCall hsp_align hrest_le hrest_lt hrest_suf htag_lt
    (FitsEnv.polyMergeLoop_head (fuel := 0) (fun _ => PolyMergeIterEnv.of_skipField3) hfits1)
    (fun hsf evs_sf hsf_ev =>
      ⟨evs_acc ++ evs_sf,
       polyEncoderMergePostEnv_of_none (hnone_of_sf hsf) hf_tot
         (hevs_acc.append (PolyMergeLoopEnv.single (fuel := 0) (PolyMergeIterEnv.of_skipField3 hsf_ev))),
       by rw [hst_cur, ← AllocCostModel.stepEvents_append]⟩)
    hnone_of_sf hcont hpc hrun hsp htr hx0 hx1 hx19 hx20 hx21 hx22 hx23 hx24 hcs hinv

/-! ## 3. Tag-1 Step Lemma (`_cro`: `idx : u32` at `msgPtr + 48#64`) -/

set_option maxRecDepth 200000 in
set_option maxHeartbeats 400000 in
set_option linter.unusedSimpArgs false in
/-- Code-RO-loaded placed step lemma for tag 1 (`idx : u32` at `msgPtr + 48#64`) at `+0x1b0`
(`(blkPl_297).base + 432#64`). -/
theorem polyEncoder_tag1_step_cro [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {H : LibsignalHooks}
    (hFromCall : subroutine_ok ((blkPC_297).rebase (blkPl_297).base H) (lsmpl.base 261)
      (withLsCodeRoLoaded lsmpl (decodeErrorFromBudgetSpec M A lim)))
    (hPushCall : subroutine_ok ((blkPC_297).rebase (blkPl_297).base H) (lsmpl.base 257)
      (withLsCodeRoLoaded lsmpl (decodeErrorPushMergeBudgetSpec M A lim)))
    (hVarintCall : subroutine_ok ((blkPC_297).rebase (blkPl_297).base H) (lsmpl.base 291)
      (withLsCodeRoLoaded lsmpl (decodeVarint2Spec A lim)))
    {x : PolyEncoderMergeGhost} {st0 st_cur : M.σ} {R : SepProp}
    {s0 s : State} {m : PolynomialEncoder} {rest : List (BitVec 8)} {iwt : WireType} {limit : Nat}
    {f_acc f_rem : Nat} {evs_acc : List AllocEvent}
    (hsp_align : (s0.sp &&& 15#64 == 0#64) = true) (hrest_le : rest.length ≤ x.bs.length)
    (hrest_lt : rest.length < 2 ^ 63) (hrest_suf : IsDropSuffix x.bs rest)
    (hf_rem : 2 ≤ f_rem)
    (hf_tot : f_acc + 2 ≤ 2 * x.bs.length + 2)
    (hevs_acc : PolyMergeLoopEnv f_acc x.bs.length (polyEncoderCapBound x) evs_acc)
    (hst_cur : st_cur = M.stepEvents evs_acc st0)
    (hfits_rem : FitsEnv M lim st_cur
      (PolyMergeLoopEnv f_rem x.bs.length (polyEncoderCapBound x)))
    (hnone_of_wt : iwt ≠ .varint →
      (mergeMessage PolynomialEncoder.mergeField (codecWireTypeToProto x.wt) x.msg x.bs 98).toOption = none)
    (hnone_of_dv : iwt = .varint → decodeVarint rest = none →
      (mergeMessage PolynomialEncoder.mergeField (codecWireTypeToProto x.wt) x.msg x.bs 98).toOption = none)
    (hcont : ∀ (v : BitVec 64) (rest' : List (BitVec 8)) (s' : State),
      iwt = .varint → decodeVarint rest = some (v, rest') →
      s'.pc = (blkPl_297).base + 164#64 →
      s'.status = .Running → s'.sp = s0.sp - 160#64 → s'.trace = s0.trace →
      s'.readReg64 (Reg.gpr 19#5) = x.bufRef → s'.readReg64 (Reg.gpr 20#5) = x.msgPtr →
      s'.readReg64 (Reg.gpr 21#5) = x.slot → s'.readReg64 (Reg.gpr 22#5) = BitVec.ofNat 64 limit →
      s'.readReg64 (Reg.gpr 23#5) = 1#64 → s'.readReg64 (Reg.gpr 24#5) = 24#64 →
      PolyCalleeSaved s0 s' → LibsignalCodeRoLoaded lsmpl s'.mem →
      SepWPp ((blkPC_297).rebase (blkPl_297).base H) (s0.readReg64 Reg.lr) s'
        (polyEncoderLoopPre A lim st_cur s0 s' x.msgPtr x.bufRef x.slot x.ptr
          { m with idx := v.truncate 32 } x.bs rest')
        (WppPost (polyEncoderMergeSpec A lim) (x, st0) R s0)
        (WppBudgetPanic (polyEncoderMergeSpec A lim) (x, st0) R s0))
    (hpc : s.pc = (blkPl_297).base + 432#64)
    (hrun : s.status = .Running) (hsp : s.sp = s0.sp - 160#64) (htr : s.trace = s0.trace)
    (hx0 : s.readReg64 (Reg.gpr 0#5) = BitVec.ofNat 64 iwt.toNat)
    (hx19 : s.readReg64 (Reg.gpr 19#5) = x.bufRef) (hx20 : s.readReg64 (Reg.gpr 20#5) = x.msgPtr)
    (hx21 : s.readReg64 (Reg.gpr 21#5) = x.slot) (hx22 : s.readReg64 (Reg.gpr 22#5) = BitVec.ofNat 64 limit)
    (hx23 : s.readReg64 (Reg.gpr 23#5) = 1#64) (hx24 : s.readReg64 (Reg.gpr 24#5) = 24#64)
    (hcs : PolyCalleeSaved s0 s) (hinv : LibsignalCodeRoLoaded lsmpl s.mem) :
    SepWPp ((blkPC_297).rebase (blkPl_297).base H) (s0.readReg64 Reg.lr) s
      (polyEncoderLoopPre A lim st_cur s0 s x.msgPtr x.bufRef x.slot x.ptr m x.bs rest)
      (WppPost (polyEncoderMergeSpec A lim) (x, st0) R s0)
      (WppBudgetPanic (polyEncoderMergeSpec A lim) (x, st0) R s0) := by
  obtain ⟨hx26, hx27, hx28, hvregs⟩ := hcs
  let restPtr : BitVec 64 := x.ptr + BitVec.ofNat 64 (x.bs.length - rest.length)
  have hfits2 : FitsEnv M lim st_cur
      (PolyMergeLoopEnv 2 x.bs.length (polyEncoderCapBound x)) :=
    FitsEnv.polyMergeLoop_mono hf_rem (Nat.le_refl _) (Nat.le_refl _) hfits_rem
  by_cases hiwt : iwt = .varint
  · subst hiwt; dsimp [WireType.toNat] at hx0
    have hfits_dv : FitsEnv M lim st_cur (DecodeVarint2Env rest) :=
      FitsEnv.polyMergeLoop_head (fuel := 1) (fun _ => PolyMergeIterEnv.of_decodeVarint2) hfits2
    apply SepWPp.of_sepWP_lscro (mid := lsmpl.base 291) hinv
    conv => arg 4; rw [polyEncoderLoopPre, sliceCursorAfter_eq_split hrest_le hrest_suf,
      polyBelow_decodeVarint2 s0.sp]
    conv => arg 4; simp only [sepConj_assoc]
    wp_steps_sync_pool (lsmpl.base 291)
    simp only [State.setMem_setMem]
    wp_reach; intro hinv
    refine SepWPp.call_frame_lscro (spec := decodeVarint2Spec A lim)
      (x := (⟨x.bufRef, x.slot, restPtr, rest⟩, st_cur))
      (ret_pc := (blkPl_297).base + 444#64) hVarintCall hinv
      (by simp only [arm64_norm]) (by simp only [arm64_norm, hrun])
      (by simp only [State.spAligned, hsp, arm64_norm]; exact hsp_align) (by simp only [arm64_norm])
      rfl ⟨by simp only [arm64_norm, hsp, hx19], hrest_lt, hfits_dv⟩
      (by rw [decodeVarint2Stack_eq]; sep_focus)
      (fun _ _ _ _ hex => False.elim (not_satisfies_false_sepConj hex))
      (fun _ _ => wppBudgetPanic_false) ?_
    intro sm hpcm hrunm hspm hcsm hinvm; simp only [CalleeSavedPreserved] at hcsm
    obtain ⟨hx19_m, hx20_m, hx21_m, hx22_m, hx23_m, hx24_m, _, hx26_m, hx27_m, hx28_m, _, hvregs_m⟩ := hcsm
    simp (config := { decide := true }) only [arm64_norm, hsp, hx19, hx20, hx21, hx22, hx23, hx24, hx26, hx27, hx28, hvregs]
      at hpcm hrunm hspm hx19_m hx20_m hx21_m hx22_m hx23_m hx24_m hx26_m hx27_m hx28_m hvregs_m
    cases hdv : decodeVarint rest with
    | none =>
      have hnone := hnone_of_dv rfl hdv
      apply SepWPp.of_sepWP_lscro (mid := (blkPl_297).base + 836#64) hinvm
      (conv => arg 4; simp only [decodeVarint2Spec, decodeVarint2SpecGen, hdv,
        sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc])
      apply SepWP.exists_elim; intro evs_dv
      wp_focus_pure; intro hsm0
      wp_focus_pure; intro htrm
      wp_focus_pure; intro hevs_dv
      wp_focus_pure; intro hsm1
      conv => arg 4; rw [decodeVarint2Stack_eq, memRegion_48_cells1_160 s0.sp]
      conv => arg 4; simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc, arm64_norm, hsp]
      apply SepWP.exists_elim; intro v_stk0
      have hcbnz_err : (sm.readReg64 (Reg.gpr 1#5) == 0#64) = false := beq_eq_false_iff_ne.mpr hsm1
      apply SepWP.fold (polyBelow_decodeVarint2_entails s0.sp) (by sep_focus)
      apply SepWP.fold (pointsToBytes_prefix_join hrest_le hrest_suf) (by sep_focus)
      wp_steps_sync_pool ((blkPl_297).base + 836#64)
      simp only [State.setMem_setMem]
      wp_reach; intro hinvm'
      have hiter_dv : PolyMergeIterEnv x.bs.length (polyEncoderCapBound x) evs_dv :=
        PolyMergeIterEnv.of_decodeVarint2 hevs_dv
      have hfits_st1 : FitsEnv M lim (M.stepEvents evs_dv st_cur)
          (PolyMergeLoopEnv 1 x.bs.length (polyEncoderCapBound x)) :=
        FitsEnv.polyMergeLoop_tail hiter_dv hfits2
      have hevs_acc1 : PolyMergeLoopEnv (f_acc + 1) x.bs.length (polyEncoderCapBound x)
          (evs_acc ++ evs_dv) :=
        hevs_acc.append (PolyMergeLoopEnv.single (fuel := 0) hiter_dv)
      have hst1 : M.stepEvents evs_dv st_cur = M.stepEvents (evs_acc ++ evs_dv) st0 := by
        rw [hst_cur, ← AllocCostModel.stepEvents_append]
      refine SepWPp.weaken_pre (Entails.of_eq (by dsimp only [polyEncoderErrFrame]; sep_ac_rfl))
        (polyEncoder_push_err_exit_cl_placed hPushCall hnone hsm1 (Nat.le_refl 1) hf_tot
          hevs_acc1 hst1 hfits_st1 hsp_align
          (by simp only [arm64_norm]) (by simp only [arm64_norm, hrunm]) (by simp only [arm64_norm, hspm])
          (by simp only [arm64_norm, htrm, htr]) (by simp only [arm64_norm, hspm])
          ⟨by simp only [arm64_norm, hx26_m], by simp only [arm64_norm, hx27_m],
           by simp only [arm64_norm, hx28_m], by simp only [arm64_norm, hvregs_m]⟩ hinvm')
    | some p =>
      rcases p with ⟨v, rest'⟩
      have hrest'_le : rest'.length ≤ rest.length := Nat.le_of_lt (decodeVarint_length hdv)
      apply SepWPp.of_sepWP_lscro (mid := (blkPl_297).base + 164#64) hinvm
      conv => arg 4; dsimp only [decodeVarint2Spec, decodeVarint2SpecGen]
      conv => arg 4; rw [decodeVarint2_pool_of_some A lim hdv, decodeVarint2Stack_eq]
      conv => arg 4; simp only [hdv, sepConj_assoc]
      wp_focus_pure; rintro ⟨hsm0, hsm1⟩
      wp_focus_pure; intro htrm
      conv => arg 4; simp only [protoPolynomialEncoderAt, protoPolynomialEncoderIdxOff,
        polyEncoderToProto, sepConj_assoc, arm64_norm, hsp]
      apply SepWP.fold (polyBelow_decodeVarint2_entails s0.sp) (by sep_focus)
      apply SepWP.fold (sliceCursorAfter_join hrest_le hrest_suf hrest'_le) (by sep_focus)
      wp_steps_sync_pool ((blkPl_297).base + 164#64)
      simp only [State.setMem_setMem]
      wp_reach; intro hinvm'
      refine SepWPp.weaken_pre
        (Entails.of_eq (by dsimp only [polyEncoderLoopPre, protoPolynomialEncoderAt, protoPolynomialEncoderIdxOff, polyEncoderToProto]; sep_ac_rfl))
        (hcont v rest' _ rfl hdv
          (by simp only [arm64_norm]) (by simp only [arm64_norm, hrunm]) (by simp only [arm64_norm, hspm])
          (by simp only [arm64_norm, htrm, htr])
          (by simp only [arm64_norm, hx19_m]) (by simp only [arm64_norm, hx20_m])
          (by simp only [arm64_norm, hx21_m]) (by simp only [arm64_norm, hx22_m])
          (by simp only [arm64_norm, hx23_m]) (by simp only [arm64_norm, hx24_m])
          ⟨by simp only [arm64_norm, hx26_m], by simp only [arm64_norm, hx27_m],
           by simp only [arm64_norm, hx28_m], by simp only [arm64_norm, hvregs_m]⟩ hinvm')
  · have hnone := hnone_of_wt hiwt
    have hcbnz := iwt_cbnz_true_of_ne_varint hiwt
    have hfits_from : FitsEnv M lim st_cur DecodeErrorFromEnv :=
      FitsEnv.polyMergeLoop_head (fuel := 1) (fun _ => PolyMergeIterEnv.of_decodeErrorFrom) hfits2
    apply SepWPp.of_sepWP_lscro (mid := lsmpl.base 261) hinv
    conv => arg 4; rw [polyEncoderLoopPre, sliceCursorAfter_eq_split hrest_le hrest_suf,
      sliceCursorAt, memRegion_48_wtErr160 s0.sp, polyBelow_decodeErrorHook s0.sp]
    conv => arg 4; simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
    apply SepWP.exists_elim; intro b_wt1
    apply SepWP.exists_elim; intro b_wt0
    apply SepWP.exists_elim; intro v_wt0
    wp_steps_sync_pool (lsmpl.base 261)
    simp only [State.setMem_setMem]
    apply SepWP.fold (wtErr160_entails_memRegion40 s0.sp _ _) (by sep_focus)
    apply SepWP.fold (pointsTo64_pair_entails_memRegion16 x.slot restPtr (BitVec.ofNat 64 rest.length)) (by sep_focus)
    apply SepWP.fold (pointsToBytes_prefix_join hrest_le hrest_suf) (by sep_focus)
    wp_reach; intro hinv
    refine SepWPp.call_frame_lscro (spec := decodeErrorFromBudgetSpec M A lim)
      (x := (s0.sp - 128#64, 0x8000000000000006#64, st_cur))
      (ret_pc := (blkPl_297).base + 604#64) hFromCall hinv
      (by simp only [arm64_norm]) (by simp only [arm64_norm, hrun])
      (by simp only [State.spAligned, hsp, arm64_norm]; exact hsp_align) (by simp only [arm64_norm])
      rfl ⟨by simp only [arm64_norm, hsp], (by decide : KindNoHeap 0x8000000000000006#64), hfits_from⟩
      (by sep_focus)
      (fun _ _ _ _ hex => False.elim (not_satisfies_false_sepConj hex))
      (fun _ _ => wppBudgetPanic_false) ?_
    intro sm hpcm hrunm hspm hcsm hinvm; simp only [CalleeSavedPreserved] at hcsm
    obtain ⟨_, _, _, _, _, _, _, hx26_m, hx27_m, hx28_m, _, hvregs_m⟩ := hcsm
    simp (config := { decide := true }) only [arm64_norm, hsp, hx26, hx27, hx28, hvregs]
      at hpcm hrunm hspm hx26_m hx27_m hx28_m hvregs_m
    apply SepWPp.of_sepWP_lscro (mid := (blkPl_297).base + 836#64) hinvm
    (conv => arg 4; simp only [decodeErrorFromBudgetSpec, sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc])
    apply SepWP.exists_elim; intro evs_f
    wp_focus_pure; rintro ⟨hve_ne, htrm⟩
    wp_focus_pure; intro hevs_f
    conv => arg 4; rw [memRegion_48_cells1_160 s0.sp]
    conv => arg 4; simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc, arm64_norm, hsp]
    apply SepWP.exists_elim; intro v_stk0
    apply SepWP.fold (polyBelow_decodeErrorHook_entails s0.sp) (by sep_focus)
    wp_steps_sync_pool ((blkPl_297).base + 836#64)
    simp only [State.setMem_setMem]
    wp_reach; intro hinvm'
    have hiter_f : PolyMergeIterEnv x.bs.length (polyEncoderCapBound x) evs_f :=
      PolyMergeIterEnv.of_decodeErrorFrom hevs_f
    have hfits_st1 : FitsEnv M lim (M.stepEvents evs_f st_cur)
        (PolyMergeLoopEnv 1 x.bs.length (polyEncoderCapBound x)) :=
      FitsEnv.polyMergeLoop_tail hiter_f hfits2
    have hevs_acc1 : PolyMergeLoopEnv (f_acc + 1) x.bs.length (polyEncoderCapBound x)
        (evs_acc ++ evs_f) :=
      hevs_acc.append (PolyMergeLoopEnv.single (fuel := 0) hiter_f)
    have hst1 : M.stepEvents evs_f st_cur = M.stepEvents (evs_acc ++ evs_f) st0 := by
      rw [hst_cur, ← AllocCostModel.stepEvents_append]
    refine SepWPp.weaken_pre (Entails.of_eq (by dsimp only [polyEncoderErrFrame]; sep_ac_rfl))
      (polyEncoder_push_err_exit_cl_placed hPushCall hnone hve_ne (Nat.le_refl 1) hf_tot
        hevs_acc1 hst1 hfits_st1 hsp_align
        (by simp only [arm64_norm]) (by simp only [arm64_norm, hrunm]) (by simp only [arm64_norm, hspm])
        (by simp only [arm64_norm, htrm, htr]) (by simp only [arm64_norm, hspm])
        ⟨by simp only [arm64_norm, hx26_m], by simp only [arm64_norm, hx27_m],
         by simp only [arm64_norm, hx28_m], by simp only [arm64_norm, hvregs_m]⟩ hinvm')

end LibsignalBinary.Proofs.SpqrV1.Prost.MessageMerge.PolyEncoderBudgetAux
