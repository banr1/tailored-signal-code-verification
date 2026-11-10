/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SpqrV1.Prost.MessageMerge.PolyDecoderBudgetAux
public meta import LibsignalBinary.Proofs.Placed.BudgetPoolSync -- shake: keep
public meta import LibsignalBinary.Proofs.Placed.BudgetVmSteps -- shake: keep
import LibsignalBinary.Proofs.Common.SharedHelpers
meta import LibsignalBinary.Proofs.Common.SharedHelpers -- shake: keep
import LibsignalBinary.Proofs.ProtoCodecRoundTrip
import LibsignalBinary.Proofs.SpqrV1.Prost.MessageMerge.EpochDirection
import LibsignalBinary.Proofs.TripleRatchet.Prost.BytesMerge.Phase1
import ProofLib.SepLogic.WPp
import GeneratedLean.LibsignalSessionCode -- shake: keep
import LibsignalBinary.Specifications.LibsignalSpqrV1.Wire -- shake: keep

/-!
# Budget-Threaded Verification of `PolynomialDecoder::merge` (Block `296`)

Proves the `withLsCodeRoLoaded`, `withLsCodeLoaded`, and bare-callee `[LibsignalPlacement]` loop
induction and top-level budget contracts (`polyDecoderMerge_cro_placed_ok_of_contracts`,
`polyDecoderMerge_cl_placed_ok_of_contracts`, `polyDecoderMerge_placed_ok_of_contracts`) on Block `296`.
-/

@[expose] public section

set_option autoImplicit false

namespace LibsignalBinary.Proofs.SpqrV1.Prost.MessageMerge.PolyDecoderBudget

open Arm64 ProofLib SepProp
open scoped CryptoVerification
open scoped CryptoVerification.CodeLayout
open scoped CryptoVerification.SpqrV1.Prost.MessageMerge
open CryptoVerification
  (LibsignalCodeLoaded LibsignalHooks LibsignalPlacement lsmpl withLsCodeLoaded)
open CryptoVerification.LibsignalProtoCodec
  (WireType decodeVarint decodeVarint_length mergeBytes skipField skip_length)
open CryptoVerification.LibsignalTripleRatchet
  (KindNoHeap LibsignalCodeRoLoaded decodeErrorAtStackLen extract_withLsCodeRoLoaded
   withLsCodeRoLoaded)
open CryptoVerification.LibsignalTripleRatchet.Prost
  (IsDropSuffix bv32_zeroExtend_ofNat decodeVarint_suffix itag_beq_tag_false key_shr32_of_ge
   key_shr32_of_lt key_wt_none key_wt_some pointsTo64_pair_entails_memRegion16
   pointsToBytes_prefix_join sf_truncate32_ofNat64 skip_suffix sliceCursorAfter
   sliceCursorAfter_eq_split sliceCursorAfter_join sliceCursorAt suffix_trans tag_cbz_false
   ule_len_of_ge ule_len_of_lt w1_tag_eq)
open CryptoVerification.LibsignalTripleRatchet.Prost.BytesMergeFacts
  (truncate32_zeroExtend64_and_255_eq)
open CryptoVerification.LibsignalSpqrV1 (PolynomialDecoder growOneVecU8Name)
open CryptoVerification.LibsignalSpqrV1.Proto (mergeMessage)
open CryptoVerification.SpqrV1.Poly (protoPolynomialDecoderAt)
open CryptoVerification.SpqrV1.Prost.BytesMerge (proto_decodeVarint_toOption)
open CryptoVerification.SpqrV1.Prost.MessageMerge
  (PolyCalleeSaved PolyDecoderMergeGhost SepWPp.call_frame_lscro SepWPp.elim_lscroProp
   SepWPp.of_sepWP_lscro WppPost blkPC_296 blkPl_296 bv64_add_zero bv64_ofNat_add_one
   bv_len_sub_limit cells2_memRegion32_entails_40_160 cmp_len_limit_of_eq cmp_len_limit_of_gt
   cmp_len_limit_of_lt codecWireTypeToProto extractLsb'_append64_0 extractLsb'_append64_64
   madd_24_eq madd_24_eq' memRegion_48_cells1_160 memRegion_48_cells2_160 memRegion_48_wtErr160
   mergeBytes_length mergeBytes_suffix mergeLoopBin mergeLoopBin_eq_limit mergeLoopBin_lt_limit
   mergeLoopBin_of_decodeVarint_none mergeLoopBin_of_key_ge mergeLoopBin_of_key_ok
   mergeLoopBin_of_tag_zero mergeLoopBin_of_wt_none mergeMessageBin
   mergeMessageBin_eq_proto_mergeMessage polyBelowStack polyBelow_decodeVarint2
   polyBelow_decodeVarint2_entails polyDecoderToProto polyMergeStack polySavedRegs polySavedRegsAny
   polySavedRegs_entails_any polynomialDecoder_mergeField_other polynomialDecoder_mergeField_tag1
   polynomialDecoder_mergeField_tag2 polynomialDecoder_mergeField_tag3
   polynomialDecoder_mergeField_tag4 protoPrefixStep_polynomialDecoder_mergeField
   slt_two_ofNat32_true stackAt_polyMerge_epilogue stackAt_polyMerge_prologue
   subroutine_ok_withLsCodeRoLoaded_of_withLsCodeLoaded_mm
   subroutine_ok_withLsCodeRoLoaded_of_withLscroProp withLscroProp wtErr160_entails_memRegion40
   wt_beq_two_of_lengthDelimited wt_beq_two_of_ne_lengthDelimited)
open LibsignalBinary.Heap
  (AllocCostModel AllocEvent BudgetLimits FitsEnv RustCliAllocBudget)
open LibsignalBinary.Heap.RustStdAllocBudgetBridge (growOneVecU8BudgetSpec)
open LibsignalBinary.Heap.SpecBudget (decodeErrorFromBudgetSpec)
open LibsignalBinary.Proofs.Placed.BudgetPoolSync (hooksException sepWP_seg_ls_vm)
open LibsignalBinary.Proofs.SpqrV1.Prost.MessageMerge.ChunkedDefsBudget
  (decodeErrorPushMergeBudgetSpec mergeBytes_len_bound)
open LibsignalBinary.Proofs.SpqrV1.Prost.MessageMerge.PolyCommonBudget
  (FitsEnv.polyMergeLoop_head FitsEnv.polyMergeLoop_mono PolyDecoderMergeEnv
   PolyDecoderMergePostEnv PolyMergeIterEnv PolyMergeLoopEnv WppBudgetPanic
   bytesMerge3RawBudgetSpec polyDecoderCapBound polyDecoderErrFrame polyDecoderLoopPre
   polyDecoderMergeSpec polyDecoderMergeSpecOfEnv wppBudgetPanic_false)
open LibsignalBinary.Proofs.SpqrV1.Prost.MessageMerge.PolyCommonClPlacedBudget
  (polyDecoder_err0_ret_exit_cl_placed polyDecoder_from_err_exit_cl_placed
   polyDecoder_skip_step_cl_placed)
open LibsignalBinary.Proofs.SpqrV1.Prost.MessageMerge.PolyDecoderBudgetAux
  (decodeVarint2Stack_eq decodeVarint2_pool_of_some fitsEnv_rem_of_loop
   polyDecoderMergePostEnv_of_some polyDecoder_tag1_step_cro polyDecoder_tag2_step_cro
   polyDecoder_tag3_step_cro polyDecoder_tag4_step_cro)
open LibsignalBinary.Proofs.SpqrV1.Varint.DecodeVarint2Budget
  (DecodeVarint2Env decodeVarint2Spec decodeVarint2SpecGen)
open LibsignalBinary.Proofs.SpqrV1.Varint.SkipField3Budget (skipField3Spec)

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

theorem subroutine_ok_withLsCodeRoLoaded_of_plain {α : Type} {prog : Program}
    {pl : Obj.MultiPlacement} {entry : BitVec 64} {spec : Spec α}
    (h : subroutine_ok prog entry spec) :
    subroutine_ok prog entry (withLsCodeRoLoaded pl spec) :=
  subroutine_ok_mono h (fun _ _ _ hp => (extract_withLsCodeRoLoaded hp).2) (fun _ _ _ _ hq => hq)

/-! ## 1. Code-RO-Loaded Loop Exit, Key Decode, Loop Induction & Top-Level Contract -/

set_option maxRecDepth 200000 in
set_option maxHeartbeats 400000 in
set_option linter.unusedSimpArgs false in
/-- Code-RO-loaded placed loop exit lemma at `+0x0a4` (`(blkPl_296).base + 164#64`) when
`cur.length ≤ limit`. -/
theorem polyDecoder_loop_le_exit_cro [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {H : LibsignalHooks}
    (hFromCall : subroutine_ok ((blkPC_296).rebase (blkPl_296).base H) (lsmpl.base 261)
      (withLsCodeRoLoaded lsmpl (decodeErrorFromBudgetSpec M A lim)))
    {x : PolyDecoderMergeGhost} {st0 st_cur : M.σ} {R : SepProp}
    {s0 s : State} {m : PolynomialDecoder} {cur : List (BitVec 8)} {limit : Nat}
    {evs_acc : List AllocEvent}
    (hle_lim : cur.length ≤ limit) (hsp_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hcur_le : cur.length ≤ x.bs.length) (hcur_suf : IsDropSuffix x.bs cur)
    (hlim_lt : limit < 2 ^ 63)
    (hevs_acc : PolyMergeLoopEnv (2 * (x.bs.length - cur.length)) x.bs.length
      (polyDecoderCapBound x) evs_acc)
    (hst_cur : st_cur = M.stepEvents evs_acc st0)
    (hfits_rem : FitsEnv M lim st_cur
      (PolyMergeLoopEnv (2 * cur.length + 2) x.bs.length (polyDecoderCapBound x)))
    (hres_cur : (mergeMessage PolynomialDecoder.mergeField (codecWireTypeToProto x.wt) x.msg x.bs 98).toOption =
      (mergeLoopBin PolynomialDecoder.mergeField (cur.length - limit) m cur limit 97).map
        (fun m' => (m', x.bs.drop (x.bs.length - limit))))
    (hpc : s.pc = (blkPl_296).base + 164#64)
    (hrun : s.status = .Running) (hsp : s.sp = s0.sp - 160#64)
    (htr : s.trace = s0.trace) (hx21 : s.readReg64 (Reg.gpr 21#5) = x.slot)
    (hx22 : s.readReg64 (Reg.gpr 22#5) = BitVec.ofNat 64 limit)
    (hcs : PolyCalleeSaved s0 s) (hinv : LibsignalCodeRoLoaded lsmpl s.mem) :
    SepWPp ((blkPC_296).rebase (blkPl_296).base H) (s0.readReg64 Reg.lr) s
      (polyDecoderLoopPre A lim st_cur s0 s x.msgPtr x.bufRef x.slot x.ptr m x.bs cur)
      (WppPost (polyDecoderMergeSpec A lim) (x, st0) R s0)
      (WppBudgetPanic (polyDecoderMergeSpec A lim) (x, st0) R s0) := by
  obtain ⟨hx26, hx27, hx28, hvregs⟩ := hcs
  let curPtr : BitVec 64 := x.ptr + BitVec.ofNat 64 (x.bs.length - cur.length)
  by_cases heq_lim : cur.length = limit
  · obtain ⟨hcmp1, hcmp2, hcmp3⟩ := cmp_len_limit_of_eq heq_lim
    have hcur_eq_drop : x.bs.drop (x.bs.length - limit) = cur := by
      rw [← heq_lim]; exact hcur_suf.symm
    have hsome :
        (mergeMessage PolynomialDecoder.mergeField (codecWireTypeToProto x.wt) x.msg x.bs 98).toOption =
          some (m, cur) := by
      rw [hres_cur, mergeLoopBin_eq_limit _ _ _ _ _ _ heq_lim, Option.map_some, hcur_eq_drop]
    have hevs_post : PolyDecoderMergePostEnv x evs_acc :=
      polyDecoderMergePostEnv_of_some hsome hevs_acc
    subst hst_cur
    apply SepWPp.of_sepWP_ret
    unfold WppPost polyDecoderMergeSpec polyDecoderMergeSpecOfEnv
    simp only [hsome, polyDecoderLoopPre, polySavedRegsAny, polySavedRegs,
      sliceCursorAfter_eq_split hcur_le hcur_suf, sliceCursorAt,
      sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc, arm64_norm, htr, hsp]
    apply SepWP.exists_elim; intro v_pad
    wp_steps_sync_pool (s0.readReg64 Reg.lr)
    simp only [State.setMem_setMem]
    apply SepWP.fold (stackAt_polyMerge_epilogue s0.sp s0 v_pad) (by unfold polySavedRegs; sep_focus)
    wp_done
  · have hlt_lim : cur.length < limit := Nat.lt_of_le_of_ne hle_lim heq_lim
    obtain ⟨hcmp1, hcmp2, hcmp3⟩ := cmp_len_limit_of_lt hlt_lim hlim_lt
    have hnone :
        (mergeMessage PolynomialDecoder.mergeField (codecWireTypeToProto x.wt) x.msg x.bs 98).toOption = none := by
      rw [hres_cur, mergeLoopBin_lt_limit _ _ _ _ _ _ hlt_lim, Option.map_none]
    apply SepWPp.of_sepWP_lscro (mid := (blkPl_296).base + 112#64) hinv
    conv => arg 4; rw [polyDecoderLoopPre, sliceCursorAfter_eq_split hcur_le hcur_suf,
      sliceCursorAt, memRegion_48_cells1_160 s0.sp]
    conv => arg 4; simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
    apply SepWP.exists_elim; intro v_stk0
    wp_steps_sync_pool ((blkPl_296).base + 112#64)
    simp only [State.setMem_setMem]
    apply SepWP.fold (pointsTo64_pair_entails_memRegion16 x.slot curPtr (BitVec.ofNat 64 cur.length)) (by sep_focus)
    apply SepWP.fold (pointsToBytes_prefix_join hcur_le hcur_suf) (by sep_focus)
    wp_reach; intro hinvm
    refine SepWPp.weaken_pre (Entails.of_eq (by dsimp only [polyDecoderErrFrame]; sep_ac_rfl))
      (polyDecoder_from_err_exit_cl_placed hFromCall hnone (by decide : KindNoHeap 0x8000000000000008#64)
        (by omega) (by omega) hevs_acc hst_cur hfits_rem hsp_align
        (by simp only [arm64_norm]) (by simp only [arm64_norm, hrun]) (by simp only [arm64_norm, hsp])
        (by simp only [arm64_norm, htr])
        ⟨by simp only [arm64_norm, hx26], by simp only [arm64_norm, hx27],
         by simp only [arm64_norm, hx28], by simp only [arm64_norm, hvregs]⟩ hinvm)

set_option maxRecDepth 200000 in
set_option maxHeartbeats 400000 in
set_option linter.unusedSimpArgs false in
/-- Code-RO-loaded placed loop key-decoding step at `+0x0a4` (`(blkPl_296).base + 164#64`) when
`¬ cur.length ≤ limit`. -/
theorem polyDecoder_decode_key_step_cro [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {H : LibsignalHooks}
    (hFromCall : subroutine_ok ((blkPC_296).rebase (blkPl_296).base H) (lsmpl.base 261)
      (withLsCodeRoLoaded lsmpl (decodeErrorFromBudgetSpec M A lim)))
    (hVarintCall : subroutine_ok ((blkPC_296).rebase (blkPl_296).base H) (lsmpl.base 291)
      (withLsCodeRoLoaded lsmpl (decodeVarint2Spec A lim)))
    {x : PolyDecoderMergeGhost} {st0 st_cur : M.σ} {R : SepProp}
    {s0 s : State} {m : PolynomialDecoder} {cur : List (BitVec 8)} {limit : Nat}
    {evs_acc : List AllocEvent}
    (hgt_lim : ¬ cur.length ≤ limit) (hsp_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hcur_le : cur.length ≤ x.bs.length) (hcur_lt : cur.length < 2 ^ 63)
    (hcur_suf : IsDropSuffix x.bs cur)
    (hevs_acc : PolyMergeLoopEnv (2 * (x.bs.length - cur.length)) x.bs.length
      (polyDecoderCapBound x) evs_acc)
    (hst_cur : st_cur = M.stepEvents evs_acc st0)
    (hfits_rem : FitsEnv M lim st_cur
      (PolyMergeLoopEnv (2 * cur.length + 2) x.bs.length (polyDecoderCapBound x)))
    (hres_cur : (mergeMessage PolynomialDecoder.mergeField (codecWireTypeToProto x.wt) x.msg x.bs 98).toOption =
      (mergeLoopBin PolynomialDecoder.mergeField (cur.length - limit) m cur limit 97).map
        (fun m' => (m', x.bs.drop (x.bs.length - limit))))
    (hcont : ∀ (key : BitVec 64) (iwt : WireType) (rest : List (BitVec 8)) (s' : State),
      decodeVarint cur = some (key, rest) → ¬ 2 ^ 32 ≤ key.toNat →
      WireType.ofNat? (key.toNat % 8) = some iwt → ¬ key.toNat / 8 < 1 →
      s'.pc = (blkPl_296).base + 216#64 →
      s'.status = .Running → s'.sp = s0.sp - 160#64 → s'.trace = s0.trace →
      s'.readReg64 (Reg.gpr 0#5) = BitVec.ofNat 64 iwt.toNat →
      s'.readReg64 (Reg.gpr 1#5) = BitVec.ofNat 64 (key.toNat / 8) →
      s'.readReg64 (Reg.gpr 19#5) = x.bufRef → s'.readReg64 (Reg.gpr 20#5) = x.msgPtr →
      s'.readReg64 (Reg.gpr 21#5) = x.slot → s'.readReg64 (Reg.gpr 22#5) = BitVec.ofNat 64 limit →
      s'.readReg64 (Reg.gpr 23#5) = 1#64 → s'.readReg64 (Reg.gpr 24#5) = 24#64 →
      PolyCalleeSaved s0 s' → LibsignalCodeRoLoaded lsmpl s'.mem →
      SepWPp ((blkPC_296).rebase (blkPl_296).base H) (s0.readReg64 Reg.lr) s'
        (polyDecoderLoopPre A lim st_cur s0 s' x.msgPtr x.bufRef x.slot x.ptr m x.bs rest)
        (WppPost (polyDecoderMergeSpec A lim) (x, st0) R s0)
        (WppBudgetPanic (polyDecoderMergeSpec A lim) (x, st0) R s0))
    (hpc : s.pc = (blkPl_296).base + 164#64)
    (hrun : s.status = .Running) (hsp : s.sp = s0.sp - 160#64) (htr : s.trace = s0.trace)
    (hx19 : s.readReg64 (Reg.gpr 19#5) = x.bufRef) (hx20 : s.readReg64 (Reg.gpr 20#5) = x.msgPtr)
    (hx21 : s.readReg64 (Reg.gpr 21#5) = x.slot) (hx22 : s.readReg64 (Reg.gpr 22#5) = BitVec.ofNat 64 limit)
    (hx23 : s.readReg64 (Reg.gpr 23#5) = 1#64) (hx24 : s.readReg64 (Reg.gpr 24#5) = 24#64)
    (hcs : PolyCalleeSaved s0 s) (hinv : LibsignalCodeRoLoaded lsmpl s.mem) :
    SepWPp ((blkPC_296).rebase (blkPl_296).base H) (s0.readReg64 Reg.lr) s
      (polyDecoderLoopPre A lim st_cur s0 s x.msgPtr x.bufRef x.slot x.ptr m x.bs cur)
      (WppPost (polyDecoderMergeSpec A lim) (x, st0) R s0)
      (WppBudgetPanic (polyDecoderMergeSpec A lim) (x, st0) R s0) := by
  obtain ⟨hx26, hx27, hx28, hvregs⟩ := hcs
  let curPtr : BitVec 64 := x.ptr + BitVec.ofNat 64 (x.bs.length - cur.length)
  obtain ⟨hcmp1, hcmp2⟩ := cmp_len_limit_of_gt hgt_lim hcur_lt
  have hfits2 : FitsEnv M lim st_cur
      (PolyMergeLoopEnv 2 x.bs.length (polyDecoderCapBound x)) :=
    FitsEnv.polyMergeLoop_mono (by omega) (Nat.le_refl _) (Nat.le_refl _) hfits_rem
  have hfits_dv : FitsEnv M lim st_cur (DecodeVarint2Env cur) :=
    FitsEnv.polyMergeLoop_head (fuel := 1) (fun _ => PolyMergeIterEnv.of_decodeVarint2) hfits2
  apply SepWPp.of_sepWP_lscro (mid := lsmpl.base 291) hinv
  conv => arg 4; rw [polyDecoderLoopPre, sliceCursorAfter_eq_split hcur_le hcur_suf,
    sliceCursorAt, polyBelow_decodeVarint2 s0.sp]
  conv => arg 4; simp only [sepConj_assoc]
  wp_steps_sync_pool (lsmpl.base 291)
  simp only [State.setMem_setMem]
  wp_reach; intro hinv
  refine SepWPp.call_frame_lscro (spec := decodeVarint2Spec A lim)
    (x := (⟨x.bufRef, x.slot, curPtr, cur⟩, st_cur))
    (ret_pc := (blkPl_296).base + 184#64) hVarintCall hinv
    (by simp only [arm64_norm]) (by simp only [arm64_norm, hrun])
    (by simp only [State.spAligned, hsp, arm64_norm]; exact hsp_align) (by simp only [arm64_norm])
    rfl ⟨by simp only [arm64_norm, hsp, hx19], hcur_lt, hfits_dv⟩
    (by dsimp only [sliceCursorAt, curPtr]; rw [decodeVarint2Stack_eq]; sep_focus)
    (fun _ _ _ _ hex => False.elim (not_satisfies_false_sepConj hex))
    (fun _ _ => wppBudgetPanic_false) ?_
  intro sm hpcm hrunm hspm hcsm hinvm; simp only [CalleeSavedPreserved] at hcsm
  obtain ⟨hx19_m, hx20_m, hx21_m, hx22_m, hx23_m, hx24_m, _, hx26_m, hx27_m, hx28_m, _, hvregs_m⟩ := hcsm
  simp (config := { decide := true }) only [arm64_norm, hsp, hx19, hx20, hx21, hx22, hx23, hx24, hx26, hx27, hx28, hvregs]
    at hpcm hrunm hspm hx19_m hx20_m hx21_m hx22_m hx23_m hx24_m hx26_m hx27_m hx28_m hvregs_m
  cases hd : decodeVarint cur with
  | none =>
    have hnone :
        (mergeMessage PolynomialDecoder.mergeField (codecWireTypeToProto x.wt) x.msg x.bs 98).toOption = none := by
      rw [hres_cur, mergeLoopBin_of_decodeVarint_none protoPrefixStep_polynomialDecoder_mergeField hgt_lim hd, Option.map_none]
    apply SepWPp.of_sepWP_lscro (mid := (blkPl_296).base + 124#64) hinvm
    conv => arg 4; simp only [decodeVarint2Spec, decodeVarint2SpecGen, hd,
      sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
    apply SepWP.exists_elim; intro evs_dv
    wp_focus_pure; intro hsm0
    wp_focus_pure; intro htrm
    wp_focus_pure; intro hevs_dv
    wp_focus_pure; intro hsm1
    conv => arg 4; rw [decodeVarint2Stack_eq]
    conv => arg 4; simp only [sepConj_assoc, arm64_norm, hsp]
    apply SepWP.fold (polyBelow_decodeVarint2_entails s0.sp) (by sep_focus)
    apply SepWP.fold (pointsToBytes_prefix_join hcur_le hcur_suf) (by sep_focus)
    wp_steps_sync_pool ((blkPl_296).base + 124#64)
    simp only [State.setMem_setMem]
    wp_reach; intro _hinvm'
    have hevs_acc1 : PolyMergeLoopEnv (2 * (x.bs.length - cur.length) + 1) x.bs.length
        (polyDecoderCapBound x) (evs_acc ++ evs_dv) :=
      hevs_acc.append (PolyMergeLoopEnv.single (fuel := 0) (PolyMergeIterEnv.of_decodeVarint2 hevs_dv))
    have hst1 : M.stepEvents evs_dv st_cur = M.stepEvents (evs_acc ++ evs_dv) st0 := by
      rw [hst_cur, ← AllocCostModel.stepEvents_append]
    refine SepWPp.weaken_pre (Entails.of_eq (by dsimp only [polyDecoderErrFrame]; sep_ac_rfl))
      (polyDecoder_err0_ret_exit_cl_placed hnone (by omega) hevs_acc1 hst1 hsp_align
        (by simp only [arm64_norm]) (by simp only [arm64_norm, hrunm]) (by simp only [arm64_norm, hspm])
        (by simp only [arm64_norm, htrm, htr]) (by simp only [arm64_norm]) hsm1
        ⟨by simp only [arm64_norm, hx26_m], by simp only [arm64_norm, hx27_m],
         by simp only [arm64_norm, hx28_m], by simp only [arm64_norm, hvregs_m]⟩)
  | some p =>
    rcases p with ⟨key, rest⟩
    have hrest_lt_cur : rest.length < cur.length := decodeVarint_length hd
    have hrest_le_cur : rest.length ≤ cur.length := Nat.le_of_lt hrest_lt_cur
    have hrest_le : rest.length ≤ x.bs.length := Nat.le_trans hrest_le_cur hcur_le
    have hrest_suf : IsDropSuffix x.bs rest :=
      suffix_trans hcur_le hcur_suf hrest_le_cur (decodeVarint_suffix hd)
    let restPtr : BitVec 64 := x.ptr + BitVec.ofNat 64 (x.bs.length - rest.length)
    by_cases hk_ge : 2 ^ 32 ≤ key.toNat
    · have hnone :
          (mergeMessage PolynomialDecoder.mergeField (codecWireTypeToProto x.wt) x.msg x.bs 98).toOption = none := by
        rw [hres_cur, mergeLoopBin_of_key_ge protoPrefixStep_polynomialDecoder_mergeField hgt_lim hd hk_ge, Option.map_none]
      have hshr := key_shr32_of_ge hk_ge
      apply SepWPp.of_sepWP_lscro (mid := (blkPl_296).base + 112#64) hinvm
      conv => arg 4; dsimp only [decodeVarint2Spec, decodeVarint2SpecGen]
      conv => arg 4; rw [decodeVarint2_pool_of_some A lim hd, decodeVarint2Stack_eq]
      conv => arg 4; simp only [hd, sepConj_assoc]
      wp_focus_pure; rintro ⟨hsm0, hsm1⟩
      wp_focus_pure; intro htrm
      conv => arg 4; simp only [sepConj_assoc, arm64_norm, hsp]
      apply SepWP.fold (polyBelow_decodeVarint2_entails s0.sp) (by sep_focus)
      apply SepWP.fold (sliceCursorAfter_join hcur_le hcur_suf hrest_le_cur) (by sep_focus)
      conv => arg 4; rw [sliceCursorAfter_eq_split hrest_le hrest_suf, sliceCursorAt,
        memRegion_48_cells2_160 s0.sp]
      conv => arg 4; simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
      apply SepWP.exists_elim; intro v_err1
      apply SepWP.exists_elim; intro v_err0
      wp_steps_sync_pool ((blkPl_296).base + 112#64)
      simp only [State.setMem_setMem]
      apply SepWP.fold (pointsTo64_pair_entails_memRegion16 x.slot restPtr (BitVec.ofNat 64 rest.length)) (by sep_focus)
      apply SepWP.fold (pointsToBytes_prefix_join hrest_le hrest_suf) (by sep_focus)
      apply SepWP.fold (cells2_memRegion32_entails_40_160 s0.sp key) (by sep_focus)
      wp_reach; intro hinvm'
      refine SepWPp.weaken_pre (Entails.of_eq (by dsimp only [polyDecoderErrFrame]; sep_ac_rfl))
        (polyDecoder_from_err_exit_cl_placed hFromCall hnone (by decide : KindNoHeap 0x8000000000000004#64)
          (by omega) (by omega) hevs_acc hst_cur hfits_rem hsp_align
          (by simp only [arm64_norm]) (by simp only [arm64_norm, hrunm]) (by simp only [arm64_norm, hspm])
          (by simp only [arm64_norm, htrm, htr])
          ⟨by simp only [arm64_norm, hx26_m], by simp only [arm64_norm, hx27_m],
           by simp only [arm64_norm, hx28_m], by simp only [arm64_norm, hvregs_m]⟩ hinvm')
    · have hshr := key_shr32_of_lt hk_ge
      cases hwt : WireType.ofNat? (key.toNat % 8) with
      | none =>
        have hnone :
            (mergeMessage PolynomialDecoder.mergeField (codecWireTypeToProto x.wt) x.msg x.bs 98).toOption = none := by
          rw [hres_cur, mergeLoopBin_of_wt_none protoPrefixStep_polynomialDecoder_mergeField hgt_lim hd hk_ge hwt, Option.map_none]
        obtain ⟨hcs1, hcs2⟩ := key_wt_none hwt
        apply SepWPp.of_sepWP_lscro (mid := (blkPl_296).base + 112#64) hinvm
        conv => arg 4; dsimp only [decodeVarint2Spec, decodeVarint2SpecGen]
        conv => arg 4; rw [decodeVarint2_pool_of_some A lim hd, decodeVarint2Stack_eq]
        conv => arg 4; simp only [hd, sepConj_assoc]
        wp_focus_pure; rintro ⟨hsm0, hsm1⟩
        wp_focus_pure; intro htrm
        conv => arg 4; simp only [sepConj_assoc, arm64_norm, hsp]
        apply SepWP.fold (polyBelow_decodeVarint2_entails s0.sp) (by sep_focus)
        apply SepWP.fold (sliceCursorAfter_join hcur_le hcur_suf hrest_le_cur) (by sep_focus)
        conv => arg 4; rw [sliceCursorAfter_eq_split hrest_le hrest_suf, sliceCursorAt,
          memRegion_48_cells2_160 s0.sp]
        conv => arg 4; simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
        apply SepWP.exists_elim; intro v_err1; apply SepWP.exists_elim; intro v_err0
        wp_steps_sync_pool ((blkPl_296).base + 112#64)
        simp only [State.setMem_setMem]
        apply SepWP.fold (pointsTo64_pair_entails_memRegion16 x.slot restPtr (BitVec.ofNat 64 rest.length)) (by sep_focus)
        apply SepWP.fold (pointsToBytes_prefix_join hrest_le hrest_suf) (by sep_focus)
        apply SepWP.fold (cells2_memRegion32_entails_40_160 s0.sp (key &&& 7#64)) (by sep_focus)
        wp_reach; intro hinvm'
        refine SepWPp.weaken_pre (Entails.of_eq (by dsimp only [polyDecoderErrFrame]; sep_ac_rfl))
          (polyDecoder_from_err_exit_cl_placed hFromCall hnone (by decide : KindNoHeap 0x8000000000000003#64)
            (by omega) (by omega) hevs_acc hst_cur hfits_rem hsp_align
            (by simp only [arm64_norm]) (by simp only [arm64_norm, hrunm]) (by simp only [arm64_norm, hspm])
            (by simp only [arm64_norm, htrm, htr])
            ⟨by simp only [arm64_norm, hx26_m], by simp only [arm64_norm, hx27_m],
             by simp only [arm64_norm, hx28_m], by simp only [arm64_norm, hvregs_m]⟩ hinvm')
      | some iwt =>
        obtain ⟨hcc1, hcc2, hand_wt, hcc1_wt, hcc2_wt⟩ := key_wt_some hwt
        obtain ⟨hw1, hw1_2⟩ := w1_tag_eq hk_ge
        obtain ⟨hw1_zext1, hw1_zext2⟩ := bv32_zeroExtend_ofNat (n := key.toNat / 8) (by omega)
        by_cases hitag0 : key.toNat / 8 < 1
        · have hnone :
              (mergeMessage PolynomialDecoder.mergeField (codecWireTypeToProto x.wt) x.msg x.bs 98).toOption = none := by
            rw [hres_cur, mergeLoopBin_of_tag_zero protoPrefixStep_polynomialDecoder_mergeField hgt_lim hd hk_ge hwt hitag0, Option.map_none]
          have htag_zero : key.toNat / 8 = 0 := by omega
          apply SepWPp.of_sepWP_lscro (mid := (blkPl_296).base + 112#64) hinvm
          conv => arg 4; dsimp only [decodeVarint2Spec, decodeVarint2SpecGen]
          conv => arg 4; rw [decodeVarint2_pool_of_some A lim hd, decodeVarint2Stack_eq]
          conv => arg 4; simp only [hd, sepConj_assoc]
          wp_focus_pure; rintro ⟨hsm0, hsm1⟩
          wp_focus_pure; intro htrm
          conv => arg 4; simp only [sepConj_assoc, arm64_norm, hsp]
          apply SepWP.fold (polyBelow_decodeVarint2_entails s0.sp) (by sep_focus)
          apply SepWP.fold (sliceCursorAfter_join hcur_le hcur_suf hrest_le_cur) (by sep_focus)
          conv => arg 4; rw [sliceCursorAfter_eq_split hrest_le hrest_suf, sliceCursorAt,
            memRegion_48_cells1_160 s0.sp]
          conv => arg 4; simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
          apply SepWP.exists_elim; intro v_err0
          wp_steps_sync_pool ((blkPl_296).base + 112#64)
          simp only [State.setMem_setMem]
          apply SepWP.fold (pointsTo64_pair_entails_memRegion16 x.slot restPtr (BitVec.ofNat 64 rest.length)) (by sep_focus)
          apply SepWP.fold (pointsToBytes_prefix_join hrest_le hrest_suf) (by sep_focus)
          wp_reach; intro hinvm'
          refine SepWPp.weaken_pre (Entails.of_eq (by dsimp only [polyDecoderErrFrame]; sep_ac_rfl))
            (polyDecoder_from_err_exit_cl_placed hFromCall hnone (by decide : KindNoHeap 0x8000000000000005#64)
              (by omega) (by omega) hevs_acc hst_cur hfits_rem hsp_align
              (by simp only [arm64_norm]) (by simp only [arm64_norm, hrunm]) (by simp only [arm64_norm, hspm])
              (by simp only [arm64_norm, htrm, htr])
              ⟨by simp only [arm64_norm, hx26_m], by simp only [arm64_norm, hx27_m],
               by simp only [arm64_norm, hx28_m], by simp only [arm64_norm, hvregs_m]⟩ hinvm')
        · obtain ⟨hcbz_tag1, hcbz_tag2⟩ := tag_cbz_false hk_ge hitag0
          have hcbz_tag64 : (BitVec.ofNat 64 (key.toNat / 8) == 0#64) = false := by
            rw [beq_eq_false_iff_ne]; intro h; have h1 := congrArg BitVec.toNat h
            simp only [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega : key.toNat / 8 < 2 ^ 64)] at h1; omega
          apply SepWPp.of_sepWP_lscro (mid := (blkPl_296).base + 216#64) hinvm
          conv => arg 4; dsimp only [decodeVarint2Spec, decodeVarint2SpecGen]
          conv => arg 4; rw [decodeVarint2_pool_of_some A lim hd, decodeVarint2Stack_eq]
          conv => arg 4; simp only [hd, sepConj_assoc]
          wp_focus_pure; rintro ⟨hsm0, hsm1⟩
          wp_focus_pure; intro htrm
          conv => arg 4; simp only [sepConj_assoc, arm64_norm, hsp]
          apply SepWP.fold (polyBelow_decodeVarint2_entails s0.sp) (by sep_focus)
          apply SepWP.fold (sliceCursorAfter_join hcur_le hcur_suf hrest_le_cur) (by sep_focus)
          wp_steps_sync_pool ((blkPl_296).base + 216#64)
          simp only [State.setMem_setMem]
          wp_reach; intro hinvm'
          refine SepWPp.weaken_pre (Entails.of_eq (by dsimp only [polyDecoderLoopPre]; sep_ac_rfl))
            (hcont key iwt rest _ hd hk_ge hwt hitag0
              (by simp only [arm64_norm]) (by simp only [arm64_norm, hrunm]) (by simp only [arm64_norm, hspm])
              (by simp only [arm64_norm, htrm, htr])
              (by simp only [arm64_norm, hsm1, hand_wt])
              (by simp only [arm64_norm, hsm1, hw1, hw1_2, hw1_zext1, hw1_zext2])
              (by simp only [arm64_norm, hx19_m]) (by simp only [arm64_norm, hx20_m])
              (by simp only [arm64_norm, hx21_m]) (by simp only [arm64_norm, hx22_m])
              (by simp only [arm64_norm, hx23_m]) (by simp only [arm64_norm, hx24_m])
              ⟨by simp only [arm64_norm, hx26_m], by simp only [arm64_norm, hx27_m],
               by simp only [arm64_norm, hx28_m], by simp only [arm64_norm, hvregs_m]⟩ hinvm')

set_option maxRecDepth 200000 in
set_option maxHeartbeats 600000 in
set_option linter.unusedSimpArgs false in
/-- Code-RO-loaded placed main loop induction for `PolynomialDecoder::merge` at `+0x0a4`
(`(blkPl_296).base + 164#64`). -/
theorem polyDecoder_loop_ok_cro [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {H : LibsignalHooks}
    (hFromCall : subroutine_ok ((blkPC_296).rebase (blkPl_296).base H) (lsmpl.base 261)
      (withLsCodeRoLoaded lsmpl (decodeErrorFromBudgetSpec M A lim)))
    (hPushCall : subroutine_ok ((blkPC_296).rebase (blkPl_296).base H) (lsmpl.base 257)
      (withLsCodeRoLoaded lsmpl (decodeErrorPushMergeBudgetSpec M A lim)))
    (hVarintCall : subroutine_ok ((blkPC_296).rebase (blkPl_296).base H) (lsmpl.base 291)
      (withLsCodeRoLoaded lsmpl (decodeVarint2Spec A lim)))
    (hSkipCall : subroutine_ok ((blkPC_296).rebase (blkPl_296).base H) (lsmpl.base 263)
      (withLsCodeRoLoaded lsmpl (skipField3Spec A lim)))
    (hBytesCall : subroutine_ok ((blkPC_296).rebase (blkPl_296).base H) (lsmpl.base 290)
      (withLsCodeRoLoaded lsmpl (bytesMerge3RawBudgetSpec A lim)))
    (hGrowCall : subroutine_ok ((blkPC_296).rebase (blkPl_296).base H)
      (lsmpl.base 621)
      (withLsCodeRoLoaded lsmpl (growOneVecU8BudgetSpec M A lim)))
    {x : PolyDecoderMergeGhost} {st0 : M.σ} {R : SepProp} {s0 : State} {limit : Nat}
    (hFit0 : FitsEnv M lim st0 (PolyDecoderMergeEnv x))
    (hsp_align : (s0.sp &&& 15#64 == 0#64) = true) (hlim_lt : limit < 2 ^ 63) :
    ∀ (n : Nat) (m : PolynomialDecoder) (cur : List (BitVec 8)) (st_cur : M.σ)
        (evs_acc : List AllocEvent) (s : State),
      cur.length ≤ n →
      cur.length ≤ x.bs.length →
      m.pts.length + cur.length < 2 ^ 56 →
      m.pts.length + cur.length ≤ polyDecoderCapBound x →
      IsDropSuffix x.bs cur →
      PolyMergeLoopEnv (2 * (x.bs.length - cur.length)) x.bs.length
        (polyDecoderCapBound x) evs_acc →
      st_cur = M.stepEvents evs_acc st0 →
      (mergeMessage PolynomialDecoder.mergeField (codecWireTypeToProto x.wt) x.msg x.bs 98).toOption =
        (mergeLoopBin PolynomialDecoder.mergeField (cur.length - limit) m cur limit 97).map
          (fun m' => (m', x.bs.drop (x.bs.length - limit))) →
      s.pc = (blkPl_296).base + 164#64 →
      s.status = .Running → s.sp = s0.sp - 160#64 → s.trace = s0.trace →
      s.readReg64 (Reg.gpr 19#5) = x.bufRef → s.readReg64 (Reg.gpr 20#5) = x.msgPtr →
      s.readReg64 (Reg.gpr 21#5) = x.slot → s.readReg64 (Reg.gpr 22#5) = BitVec.ofNat 64 limit →
      s.readReg64 (Reg.gpr 23#5) = 1#64 → s.readReg64 (Reg.gpr 24#5) = 24#64 →
      PolyCalleeSaved s0 s → LibsignalCodeRoLoaded lsmpl s.mem →
      SepWPp ((blkPC_296).rebase (blkPl_296).base H) (s0.readReg64 Reg.lr) s
        (polyDecoderLoopPre A lim st_cur s0 s x.msgPtr x.bufRef x.slot x.ptr m x.bs cur)
        (WppPost (polyDecoderMergeSpec A lim) (x, st0) R s0)
        (WppBudgetPanic (polyDecoderMergeSpec A lim) (x, st0) R s0) := by
  intro n; induction n with
  | zero =>
    intro m cur st_cur evs_acc s hcur_n hcur_le _ _ hcur_suf hevs_acc hst_cur hres_cur
      hpc hrun hsp htr _ _ hx21 hx22 _ _ hcs hinv
    have hfits_rem := fitsEnv_rem_of_loop hFit0 (f_rem := 2 * cur.length + 2) (by omega) hevs_acc hst_cur
    exact polyDecoder_loop_le_exit_cro hFromCall (by omega) hsp_align hcur_le hcur_suf hlim_lt
      hevs_acc hst_cur hfits_rem hres_cur hpc hrun hsp htr hx21 hx22 hcs hinv
  | succ n ih =>
    intro m cur st_cur evs_acc s hcur_n hcur_le hpts_bound hcap_cur hcur_suf hevs_acc hst_cur
      hres_cur hpc hrun hsp htr hx19 hx20 hx21 hx22 hx23 hx24 hcs hinv
    have hfits_rem := fitsEnv_rem_of_loop hFit0 (f_rem := 2 * cur.length + 2) (by omega) hevs_acc hst_cur
    by_cases hle_lim : cur.length ≤ limit
    · exact polyDecoder_loop_le_exit_cro hFromCall hle_lim hsp_align hcur_le hcur_suf hlim_lt
        hevs_acc hst_cur hfits_rem hres_cur hpc hrun hsp htr hx21 hx22 hcs hinv
    · have hcur_lt : cur.length < 2 ^ 63 := by omega
      refine polyDecoder_decode_key_step_cro hFromCall hVarintCall hle_lim hsp_align
        hcur_le hcur_lt hcur_suf hevs_acc hst_cur hfits_rem hres_cur ?_
        hpc hrun hsp htr hx19 hx20 hx21 hx22 hx23 hx24 hcs hinv
      intro key iwt rest s' hd hk_ge hwt hitag0 hpc' hrun' hsp' htr' hx0' hx1'
        hx19' hx20' hx21' hx22' hx23' hx24' hcs' hinv'
      obtain ⟨hx26', hx27', hx28', hvregs'⟩ := hcs'
      have hrest_lt_cur : rest.length < cur.length := decodeVarint_length hd
      have hrest_le_cur : rest.length ≤ cur.length := Nat.le_of_lt hrest_lt_cur
      have hrest_le : rest.length ≤ x.bs.length := Nat.le_trans hrest_le_cur hcur_le
      have hrest_lt : rest.length < 2 ^ 63 := by omega
      have hrest_suf : IsDropSuffix x.bs rest :=
        suffix_trans hcur_le hcur_suf hrest_le_cur (decodeVarint_suffix hd)
      have hloop_ok := mergeLoopBin_of_key_ok (m := m) (depth' := 97)
        protoPrefixStep_polynomialDecoder_mergeField hle_lim hd hk_ge hwt hitag0
      by_cases htag1 : key.toNat / 8 = 1
      · rw [htag1] at hx1' hloop_ok; rw [polynomialDecoder_mergeField_tag1] at hloop_ok
        apply SepWPp.of_sepWP_lscro (mid := (blkPl_296).base + 344#64) hinv'
        conv => arg 4; dsimp only [polyDecoderLoopPre]
        wp_steps_sync_pool ((blkPl_296).base + 344#64); simp only [State.setMem_setMem]; wp_reach; intro hinvm'
        refine SepWPp.weaken_pre (Entails.of_eq (by dsimp only [polyDecoderLoopPre]; sep_ac_rfl))
          (polyDecoder_tag1_step_cro (limit := limit) hFromCall hPushCall hVarintCall
          hsp_align hrest_le hrest_lt hrest_suf (by omega) (by omega) hevs_acc hst_cur hfits_rem
          (fun (hiwt : iwt ≠ .varint) => by simp only [hres_cur, hloop_ok, hiwt, ↓reduceIte, Option.map_none])
          (fun (hiwt : iwt = .varint) (hdv : decodeVarint rest = none) => by simp only [hres_cur, hloop_ok, hiwt, ↓reduceIte, hdv, Option.map_none])
          (fun v rest' s'' hiwt hdv hpc'' hrun'' hsp'' htr'' hx19'' hx20'' hx21'' hx22'' hx23'' hx24'' hcs'' hinv'' => ?_)
          (by simp only [arm64_norm]) (by simp only [arm64_norm, hrun']) (by simp only [arm64_norm, hsp'])
          (by simp only [arm64_norm, htr'])
          (by simp only [arm64_norm, hx0']) (by simp only [arm64_norm, hx19']) (by simp only [arm64_norm, hx20'])
          (by simp only [arm64_norm, hx21']) (by simp only [arm64_norm, hx22']) (by simp only [arm64_norm, hx23'])
          (by simp only [arm64_norm, hx24'])
          ⟨by simp only [arm64_norm, hx26'], by simp only [arm64_norm, hx27'],
           by simp only [arm64_norm, hx28'], by simp only [arm64_norm, hvregs']⟩ hinvm')
        have hrest'_lt : rest'.length < rest.length := decodeVarint_length hdv
        have hrest'_le_rest : rest'.length ≤ rest.length := Nat.le_of_lt hrest'_lt
        have hres_next :
            (mergeMessage PolynomialDecoder.mergeField (codecWireTypeToProto x.wt) x.msg x.bs 98).toOption =
              (mergeLoopBin PolynomialDecoder.mergeField (rest'.length - limit)
                { m with ptsNeeded := v.truncate 32 } rest' limit 97).map
                  (fun m' => (m', x.bs.drop (x.bs.length - limit))) := by
          simp only [hres_cur, hloop_ok, hiwt, ↓reduceIte, hdv, Option.map_some]
        exact ih { m with ptsNeeded := v.truncate 32 } rest' st_cur evs_acc s''
          (by omega) (by omega) (by dsimp; omega) (by dsimp; omega)
          (suffix_trans hrest_le hrest_suf hrest'_le_rest (decodeVarint_suffix hdv))
          (hevs_acc.mono_fuel (by omega)) hst_cur hres_next
          hpc'' hrun'' hsp'' htr'' hx19'' hx20'' hx21'' hx22'' hx23'' hx24'' hcs'' hinv''
      · by_cases htag2 : key.toNat / 8 = 2
        · rw [htag2] at hx1' hloop_ok; rw [polynomialDecoder_mergeField_tag2] at hloop_ok
          apply SepWPp.of_sepWP_lscro (mid := (blkPl_296).base + 240#64) hinv'
          conv => arg 4; dsimp only [polyDecoderLoopPre]
          wp_steps_sync_pool ((blkPl_296).base + 240#64); simp only [State.setMem_setMem]; wp_reach; intro hinvm'
          refine SepWPp.weaken_pre (Entails.of_eq (by dsimp only [polyDecoderLoopPre]; sep_ac_rfl))
            (polyDecoder_tag2_step_cro (limit := limit) hFromCall hPushCall hVarintCall
            hsp_align hrest_le hrest_lt hrest_suf (by omega) (by omega) hevs_acc hst_cur hfits_rem
            (fun (hiwt : iwt ≠ .varint) => by simp only [hres_cur, hloop_ok, hiwt, ↓reduceIte, Option.map_none])
            (fun (hiwt : iwt = .varint) (hdv : decodeVarint rest = none) => by simp only [hres_cur, hloop_ok, hiwt, ↓reduceIte, hdv, Option.map_none])
            (fun v rest' s'' hiwt hdv hpc'' hrun'' hsp'' htr'' hx19'' hx20'' hx21'' hx22'' hx23'' hx24'' hcs'' hinv'' => ?_)
            (by simp only [arm64_norm]) (by simp only [arm64_norm, hrun']) (by simp only [arm64_norm, hsp'])
            (by simp only [arm64_norm, htr'])
            (by simp only [arm64_norm, hx0']) (by simp only [arm64_norm, hx19']) (by simp only [arm64_norm, hx20'])
            (by simp only [arm64_norm, hx21']) (by simp only [arm64_norm, hx22']) (by simp only [arm64_norm, hx23'])
            (by simp only [arm64_norm, hx24'])
            ⟨by simp only [arm64_norm, hx26'], by simp only [arm64_norm, hx27'],
             by simp only [arm64_norm, hx28'], by simp only [arm64_norm, hvregs']⟩ hinvm')
          have hrest'_lt : rest'.length < rest.length := decodeVarint_length hdv
          have hrest'_le_rest : rest'.length ≤ rest.length := Nat.le_of_lt hrest'_lt
          have hres_next :
              (mergeMessage PolynomialDecoder.mergeField (codecWireTypeToProto x.wt) x.msg x.bs 98).toOption =
                (mergeLoopBin PolynomialDecoder.mergeField (rest'.length - limit)
                  { m with polys := v.truncate 32 } rest' limit 97).map
                    (fun m' => (m', x.bs.drop (x.bs.length - limit))) := by
            simp only [hres_cur, hloop_ok, hiwt, ↓reduceIte, hdv, Option.map_some]
          exact ih { m with polys := v.truncate 32 } rest' st_cur evs_acc s''
            (by omega) (by omega) (by dsimp; omega) (by dsimp; omega)
            (suffix_trans hrest_le hrest_suf hrest'_le_rest (decodeVarint_suffix hdv))
            (hevs_acc.mono_fuel (by omega)) hst_cur hres_next
            hpc'' hrun'' hsp'' htr'' hx19'' hx20'' hx21'' hx22'' hx23'' hx24'' hcs'' hinv''
        · by_cases htag3 : key.toNat / 8 = 3
          · rw [htag3] at hx1' hloop_ok; rw [polynomialDecoder_mergeField_tag3] at hloop_ok
            apply SepWPp.of_sepWP_lscro (mid := (blkPl_296).base + 376#64) hinv'
            conv => arg 4; dsimp only [polyDecoderLoopPre]
            wp_steps_sync_pool ((blkPl_296).base + 376#64); simp only [State.setMem_setMem]; wp_reach; intro hinvm'
            have hnone_mb : mergeBytes iwt rest = none →
                (mergeMessage PolynomialDecoder.mergeField (codecWireTypeToProto x.wt) x.msg x.bs 98).toOption = none := by
              intro hmb; simp only [hres_cur, hloop_ok, hmb, Option.map_none]
            refine SepWPp.weaken_pre (Entails.of_eq (by dsimp only [polyDecoderLoopPre]; sep_ac_rfl))
              (polyDecoder_tag3_step_cro (limit := limit) hFromCall hPushCall hBytesCall hGrowCall
              hsp_align hrest_le (by omega) hrest_suf (by omega) (by omega) (by omega)
              hevs_acc hst_cur hfits_rem hnone_mb
              (fun v rest' st_next evs_step s'' hmb hevs_step hst_next
                  hpc'' hrun'' hsp'' htr'' hx19'' hx20'' hx21'' hx22'' hx23'' hx24'' hcs'' hinv'' => ?_)
              (by simp only [arm64_norm]) (by simp only [arm64_norm, hrun']) (by simp only [arm64_norm, hsp'])
              (by simp only [arm64_norm, htr'])
              (by simp only [arm64_norm, hx0']) (by simp only [arm64_norm, hx19']) (by simp only [arm64_norm, hx20'])
              (by simp only [arm64_norm, hx21']) (by simp only [arm64_norm, hx22']) (by simp only [arm64_norm, hx23'])
              (by simp only [arm64_norm, hx24'])
              ⟨by simp only [arm64_norm, hx26'], by simp only [arm64_norm, hx27'],
               by simp only [arm64_norm, hx28'], by simp only [arm64_norm, hvregs']⟩ hinvm')
            have hrest'_le_rest : rest'.length ≤ rest.length := mergeBytes_length hmb
            have hmb_len := mergeBytes_len_bound hmb
            have hres_next :
                (mergeMessage PolynomialDecoder.mergeField (codecWireTypeToProto x.wt) x.msg x.bs 98).toOption =
                  (mergeLoopBin PolynomialDecoder.mergeField (rest'.length - limit)
                    { m with pts := m.pts ++ [v] } rest' limit 97).map
                      (fun m' => (m', x.bs.drop (x.bs.length - limit))) := by
              simp only [hres_cur, hloop_ok, hmb, Option.map_some]
            have hevs_next : PolyMergeLoopEnv (2 * (x.bs.length - rest'.length)) x.bs.length
                (polyDecoderCapBound x) (evs_acc ++ evs_step) :=
              (hevs_acc.append hevs_step).mono_fuel (by omega)
            have hst_next' : st_next = M.stepEvents (evs_acc ++ evs_step) st0 := by
              rw [hst_next, hst_cur, ← AllocCostModel.stepEvents_append]
            exact ih { m with pts := m.pts ++ [v] } rest' st_next (evs_acc ++ evs_step) s''
              (by omega) (by omega) (by simp; omega) (by simp; omega)
              (suffix_trans hrest_le hrest_suf hrest'_le_rest (mergeBytes_suffix hmb))
              hevs_next hst_next' hres_next
              hpc'' hrun'' hsp'' htr'' hx19'' hx20'' hx21'' hx22'' hx23'' hx24'' hcs'' hinv''
          · by_cases htag4 : key.toNat / 8 = 4
            · rw [htag4] at hx1' hloop_ok; rw [polynomialDecoder_mergeField_tag4] at hloop_ok
              apply SepWPp.of_sepWP_lscro (mid := (blkPl_296).base + 288#64) hinv'
              conv => arg 4; dsimp only [polyDecoderLoopPre]
              wp_steps_sync_pool ((blkPl_296).base + 288#64); simp only [State.setMem_setMem]; wp_reach; intro hinvm'
              refine SepWPp.weaken_pre (Entails.of_eq (by dsimp only [polyDecoderLoopPre]; sep_ac_rfl))
                (polyDecoder_tag4_step_cro (limit := limit) hFromCall hPushCall hVarintCall
                hsp_align hrest_le hrest_lt hrest_suf (by omega) (by omega) hevs_acc hst_cur hfits_rem
                (fun (hiwt : iwt ≠ .varint) => by simp only [hres_cur, hloop_ok, hiwt, ↓reduceIte, Option.map_none])
                (fun (hiwt : iwt = .varint) (hdv : decodeVarint rest = none) => by simp only [hres_cur, hloop_ok, hiwt, ↓reduceIte, hdv, Option.map_none])
                (fun v rest' s'' hiwt hdv hpc'' hrun'' hsp'' htr'' hx19'' hx20'' hx21'' hx22'' hx23'' hx24'' hcs'' hinv'' => ?_)
                (by simp only [arm64_norm]) (by simp only [arm64_norm, hrun']) (by simp only [arm64_norm, hsp'])
                (by simp only [arm64_norm, htr'])
                (by simp only [arm64_norm, hx0']) (by simp only [arm64_norm, hx19']) (by simp only [arm64_norm, hx20'])
                (by simp only [arm64_norm, hx21']) (by simp only [arm64_norm, hx22']) (by simp only [arm64_norm, hx23'])
                (by simp only [arm64_norm, hx24'])
                ⟨by simp only [arm64_norm, hx26'], by simp only [arm64_norm, hx27'],
                 by simp only [arm64_norm, hx28'], by simp only [arm64_norm, hvregs']⟩ hinvm')
              have hrest'_lt : rest'.length < rest.length := decodeVarint_length hdv
              have hrest'_le_rest : rest'.length ≤ rest.length := Nat.le_of_lt hrest'_lt
              have hres_next :
                  (mergeMessage PolynomialDecoder.mergeField (codecWireTypeToProto x.wt) x.msg x.bs 98).toOption =
                    (mergeLoopBin PolynomialDecoder.mergeField (rest'.length - limit)
                      { m with isComplete := v != 0#64 } rest' limit 97).map
                        (fun m' => (m', x.bs.drop (x.bs.length - limit))) := by
                simp only [hres_cur, hloop_ok, hiwt, ↓reduceIte, hdv, Option.map_some]
              exact ih { m with isComplete := v != 0#64 } rest' st_cur evs_acc s''
                (by omega) (by omega) (by dsimp; omega) (by dsimp; omega)
                (suffix_trans hrest_le hrest_suf hrest'_le_rest (decodeVarint_suffix hdv))
                (hevs_acc.mono_fuel (by omega)) hst_cur hres_next
                hpc'' hrun'' hsp'' htr'' hx19'' hx20'' hx21'' hx22'' hx23'' hx24'' hcs'' hinv''
            · have hitag_lt : key.toNat / 8 < 2 ^ 32 := by omega
              obtain ⟨hslt1, hslt2⟩ := slt_two_ofNat32_true (n := key.toNat / 8) (by omega) (by omega)
              obtain ⟨hb3_1, _⟩ := itag_beq_tag_false htag3 hitag_lt (by decide : 3 < 2 ^ 32)
              obtain ⟨hb4_1, _⟩ := itag_beq_tag_false htag4 hitag_lt (by decide : 4 < 2 ^ 32)
              have hb3_2 : (BitVec.truncate 32 (BitVec.ofNat 64 (key.toNat / 8)) == 3#32) = false := by
                rw [sf_truncate32_ofNat64]; exact hb3_1
              have hb4_2 : (BitVec.truncate 32 (BitVec.ofNat 64 (key.toNat / 8)) == 4#32) = false := by
                rw [sf_truncate32_ofNat64]; exact hb4_1
              have hb4_bne1 : (BitVec.ofNat 32 (key.toNat / 8) != 4#32) = true := by
                simp only [bne, hb4_1, Bool.not_false]
              have hb4_bne2 : (BitVec.truncate 32 (BitVec.ofNat 64 (key.toNat / 8)) != 4#32) = true := by
                simp only [bne, hb4_2, Bool.not_false]
              rw [polynomialDecoder_mergeField_other m iwt rest 97 hitag_lt htag1 htag2 htag3 htag4] at hloop_ok
              apply SepWPp.of_sepWP_lscro (mid := (blkPl_296).base + 320#64) hinv'
              conv => arg 4; dsimp only [polyDecoderLoopPre]
              wp_steps_sync_pool ((blkPl_296).base + 320#64); simp only [State.setMem_setMem]; wp_reach; intro hinvm'
              have hnone_sf : skipField (2 * rest.length + 2) 97 (key.toNat / 8) iwt rest = none →
                  (mergeMessage PolynomialDecoder.mergeField (codecWireTypeToProto x.wt) x.msg x.bs 98).toOption = none := by
                intro hsf; rw [hres_cur, hloop_ok, hsf]; rfl
              refine SepWPp.weaken_pre (Entails.of_eq (by dsimp only [polyDecoderLoopPre]; sep_ac_rfl))
                (polyDecoder_skip_step_cl_placed (limit := limit) hSkipCall
                hsp_align hrest_le hrest_lt hrest_suf hitag_lt (by omega) (by omega)
                hevs_acc hst_cur hfits_rem hnone_sf
                (fun rest' s'' hsf hpc'' hrun'' hsp'' htr'' hx19'' hx20'' hx21'' hx22'' hx23'' hx24'' hcs'' hinv'' => ?_)
                (by simp only [arm64_norm]) (by simp only [arm64_norm, hrun']) (by simp only [arm64_norm, hsp'])
                (by simp only [arm64_norm, htr'])
                (by simp only [arm64_norm, hx0']) (by simp only [arm64_norm, hx1', sf_truncate32_ofNat64])
                (by simp only [arm64_norm, hx19']) (by simp only [arm64_norm, hx20'])
                (by simp only [arm64_norm, hx21']) (by simp only [arm64_norm, hx22']) (by simp only [arm64_norm, hx23'])
                (by simp only [arm64_norm, hx24'])
                ⟨by simp only [arm64_norm, hx26'], by simp only [arm64_norm, hx27'],
                 by simp only [arm64_norm, hx28'], by simp only [arm64_norm, hvregs']⟩ hinvm')
              have hrest'_le_rest : rest'.length ≤ rest.length := (skip_length (2 * rest.length + 2)).1 _ _ _ _ _ hsf
              have hres_next :
                  (mergeMessage PolynomialDecoder.mergeField (codecWireTypeToProto x.wt) x.msg x.bs 98).toOption =
                    (mergeLoopBin PolynomialDecoder.mergeField (rest'.length - limit) m rest' limit 97).map
                      (fun m' => (m', x.bs.drop (x.bs.length - limit))) := by
                rw [hres_cur, hloop_ok, hsf]; rfl
              exact ih m rest' st_cur evs_acc s''
                (by omega) (by omega) (by omega) (by omega)
                (suffix_trans hrest_le hrest_suf hrest'_le_rest ((skip_suffix (2 * rest.length + 2)).1 _ _ _ _ _ hsf))
                (hevs_acc.mono_fuel (by omega)) hst_cur hres_next
                hpc'' hrun'' hsp'' htr'' hx19'' hx20'' hx21'' hx22'' hx23'' hx24'' hcs'' hinv''

set_option maxRecDepth 200000 in
set_option maxHeartbeats 600000 in
set_option linter.unusedSimpArgs false in
/-- `withLsCodeRoLoaded`-callee contract-parameterized `[LibsignalPlacement]` budget verification of
`prost::encoding::message::merge::<PolynomialDecoder, &mut &[u8]>` (Block `296`). -/
theorem polyDecoderMerge_cro_placed_ok_of_contracts [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {H : LibsignalHooks}
    (hFromCall : subroutine_ok ((blkPC_296).rebase (blkPl_296).base H) (lsmpl.base 261)
      (withLsCodeRoLoaded lsmpl (decodeErrorFromBudgetSpec M A lim)))
    (hPushCall : subroutine_ok ((blkPC_296).rebase (blkPl_296).base H) (lsmpl.base 257)
      (withLsCodeRoLoaded lsmpl (decodeErrorPushMergeBudgetSpec M A lim)))
    (hVarintCall : subroutine_ok ((blkPC_296).rebase (blkPl_296).base H) (lsmpl.base 291)
      (withLsCodeRoLoaded lsmpl (decodeVarint2Spec A lim)))
    (hSkipCall : subroutine_ok ((blkPC_296).rebase (blkPl_296).base H) (lsmpl.base 263)
      (withLsCodeRoLoaded lsmpl (skipField3Spec A lim)))
    (hBytesCall : subroutine_ok ((blkPC_296).rebase (blkPl_296).base H) (lsmpl.base 290)
      (withLsCodeRoLoaded lsmpl (bytesMerge3RawBudgetSpec A lim)))
    (hGrowCall : subroutine_ok ((blkPC_296).rebase (blkPl_296).base H)
      (lsmpl.base 621)
      (withLsCodeRoLoaded lsmpl (growOneVecU8BudgetSpec M A lim))) :
    subroutine_ok ((blkPC_296).rebase (blkPl_296).base H) (blkPl_296).base
      (withLsCodeRoLoaded lsmpl (polyDecoderMergeSpec A lim)) := by
  apply subroutine_ok_withLsCodeRoLoaded_of_withLscroProp
  unfold withLscroProp polyDecoderMergeSpec polyDecoderMergeSpecOfEnv
  apply subroutine_ok_of_sepWPp_init
  rintro ⟨x, st0⟩ R s0 hpc hrun hpre hsp_align
  have hsp_align' : (s0.sp &&& 15#64 == 0#64) = true := hsp_align
  refine ⟨_, hpre, ?_⟩
  dsimp only
  apply SepWPp.elim_lscroProp; intro hinv0
  change SepWPp _ _ _ _
    (WppPost (polyDecoderMergeSpec A lim) (x, st0) R s0)
    (WppBudgetPanic (polyDecoderMergeSpec A lim) (x, st0) R s0)
  apply SepWPp.pure_elim
  rintro ⟨h_1, h_2, h_3, h_bound, hFit0⟩
  have hbs_lt : x.bs.length < 2 ^ 63 := by omega
  have hevs0 : PolyMergeLoopEnv 0 x.bs.length (polyDecoderCapBound x) [] := .nil
  have hfits0 : FitsEnv M lim st0
      (PolyMergeLoopEnv (2 * x.bs.length + 2) x.bs.length (polyDecoderCapBound x)) := hFit0
  by_cases hwt_ld : x.wt = .lengthDelimited
  · have h_1' : (s0.readReg64 (Reg.gpr 0#5)).setWidth 8 = 2#8 := by rw [h_1, hwt_ld]; rfl
    have hbeq := wt_beq_two_of_lengthDelimited h_1'
    have hbne1 : (BitVec.truncate 32 (s0.readReg64 (Reg.gpr 0#5)) &&& 255#32 != 2#32) = false := by
      simp only [bne, hbeq, Bool.not_true]
    have hbne2 : (BitVec.truncate 32 (BitVec.zeroExtend 64 (BitVec.truncate 32 (s0.readReg64 (Reg.gpr 0#5))) &&& 255#64) != 2#32) = false := by
      rw [truncate32_zeroExtend64_and_255_eq, h_1']; decide
    have hbne3 : (BitVec.truncate 32 (BitVec.zeroExtend 64 (BitVec.truncate 32 (s0.readReg64 (Reg.gpr 0#5)) &&& 255#32)) != 2#32) = false := by
      revert h_1'; bv_bits
    have hfits_dv0 : FitsEnv M lim st0 (DecodeVarint2Env x.bs) :=
      FitsEnv.polyMergeLoop_head (fuel := 2 * x.bs.length + 1)
        (fun _ => PolyMergeIterEnv.of_decodeVarint2) hfits0
    apply SepWPp.of_sepWP_lscro (mid := lsmpl.base 291) hinv0
    conv => arg 4; rw [stackAt_polyMerge_prologue s0.sp, polyBelow_decodeVarint2 s0.sp]
    conv => arg 4; simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
    apply SepWP.exists_elim; intro v0; apply SepWP.exists_elim; intro v1; apply SepWP.exists_elim; intro v2
    apply SepWP.exists_elim; intro v3; apply SepWP.exists_elim; intro v4; apply SepWP.exists_elim; intro v5
    apply SepWP.exists_elim; intro v6; apply SepWP.exists_elim; intro v7; apply SepWP.exists_elim; intro v8
    apply SepWP.exists_elim; intro v9
    wp_steps_sync_pool (lsmpl.base 291)
    simp only [State.setMem_setMem]
    apply SepWP.fold (polySavedRegs_entails_any s0.sp s0 v3) (by unfold polySavedRegs; sep_focus)
    wp_reach; intro hinv0'
    refine SepWPp.call_frame_lscro (spec := decodeVarint2Spec A lim)
      (x := (⟨x.bufRef, x.slot, x.ptr, x.bs⟩, st0))
      (ret_pc := (blkPl_296).base + 56#64) hVarintCall hinv0'
      (by simp only [arm64_norm]) (by simp only [arm64_norm, hrun])
      (by simp only [State.spAligned, arm64_norm]; exact hsp_align') (by simp only [arm64_norm])
      rfl ⟨by simp only [arm64_norm, h_3], hbs_lt, hfits_dv0⟩
      (by rw [decodeVarint2Stack_eq]; sep_focus)
      (fun _ _ _ _ hex => False.elim (not_satisfies_false_sepConj hex))
      (fun _ _ => wppBudgetPanic_false) ?_
    intro sm hpcm hrunm hspm hcsm hinvm; simp only [CalleeSavedPreserved] at hcsm
    obtain ⟨hx19_m, hx20_m, hx21_m, hx22_m, hx23_m, hx24_m, hx25_m, hx26_m, hx27_m, hx28_m, hfp_m, hvregs_m⟩ := hcsm
    simp (config := { decide := true }) only [arm64_norm, h_2, h_3]
      at hpcm hrunm hspm hx19_m hx20_m hx21_m hx22_m hx23_m hx24_m hx25_m hx26_m hx27_m hx28_m hfp_m hvregs_m
    cases hdv0 : decodeVarint x.bs with
    | none =>
      have hnone :
          (mergeMessage PolynomialDecoder.mergeField (codecWireTypeToProto x.wt) x.msg x.bs 98).toOption = none := by
        rw [hwt_ld, ← mergeMessageBin_eq_proto_mergeMessage protoPrefixStep_polynomialDecoder_mergeField]
        simp [mergeMessageBin, codecWireTypeToProto, proto_decodeVarint_toOption, hdv0]
      apply SepWPp.of_sepWP_lscro (mid := (blkPl_296).base + 124#64) hinvm
      conv => arg 4; simp only [decodeVarint2Spec, decodeVarint2SpecGen, hdv0,
        sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
      apply SepWP.exists_elim; intro evs_dv
      wp_focus_pure; intro hsm0
      wp_focus_pure; intro htrm
      wp_focus_pure; intro hevs_dv
      wp_focus_pure; intro hsm1
      conv => arg 4; rw [decodeVarint2Stack_eq]
      conv => arg 4; simp only [sepConj_assoc, arm64_norm]
      apply SepWP.fold (polyBelow_decodeVarint2_entails s0.sp) (by sep_focus)
      wp_steps_sync_pool ((blkPl_296).base + 124#64)
      simp only [State.setMem_setMem]
      wp_reach; intro _hinvm'
      have hevs_dv1 : PolyMergeLoopEnv 1 x.bs.length (polyDecoderCapBound x) evs_dv :=
        PolyMergeLoopEnv.single (fuel := 0) (PolyMergeIterEnv.of_decodeVarint2 hevs_dv)
      refine SepWPp.weaken_pre (Entails.of_eq (by dsimp only [polyDecoderErrFrame]; sep_ac_rfl))
        (polyDecoder_err0_ret_exit_cl_placed hnone (by omega) hevs_dv1 rfl hsp_align'
          (by simp only [arm64_norm]) (by simp only [arm64_norm, hrunm]) (by simp only [arm64_norm, hspm])
          (by simp only [arm64_norm, htrm]) (by simp only [arm64_norm]) hsm1
          ⟨by simp only [arm64_norm, hx26_m], by simp only [arm64_norm, hx27_m],
           by simp only [arm64_norm, hx28_m], by simp only [arm64_norm, hvregs_m]⟩)
    | some p =>
      rcases p with ⟨len, rest0⟩
      have hrest0_lt_bs : rest0.length < x.bs.length := decodeVarint_length hdv0
      have hrest0_le : rest0.length ≤ x.bs.length := Nat.le_of_lt hrest0_lt_bs
      have hrest0_lt : rest0.length < 2 ^ 63 := Nat.lt_of_lt_of_le hrest0_lt_bs (Nat.le_of_lt hbs_lt)
      have hrest0_suf : IsDropSuffix x.bs rest0 := decodeVarint_suffix hdv0
      let rest0Ptr : BitVec 64 := x.ptr + BitVec.ofNat 64 (x.bs.length - rest0.length)
      by_cases hlt_len : rest0.length < len.toNat
      · have hule := ule_len_of_lt hlt_len hrest0_lt
        have hnone :
            (mergeMessage PolynomialDecoder.mergeField (codecWireTypeToProto x.wt) x.msg x.bs 98).toOption = none := by
          rw [hwt_ld, ← mergeMessageBin_eq_proto_mergeMessage protoPrefixStep_polynomialDecoder_mergeField]
          simp [mergeMessageBin, codecWireTypeToProto, proto_decodeVarint_toOption, hdv0, hlt_len]
        apply SepWPp.of_sepWP_lscro (mid := (blkPl_296).base + 112#64) hinvm
        conv => arg 4; dsimp only [decodeVarint2Spec, decodeVarint2SpecGen]
        conv => arg 4; rw [decodeVarint2_pool_of_some A lim hdv0, decodeVarint2Stack_eq]
        conv => arg 4; simp only [hdv0, sepConj_assoc]
        wp_focus_pure; rintro ⟨hsm0, hsm1⟩
        wp_focus_pure; intro htrm
        conv => arg 4; simp only [sepConj_assoc, arm64_norm]
        apply SepWP.fold (polyBelow_decodeVarint2_entails s0.sp) (by sep_focus)
        conv => arg 4; rw [sliceCursorAfter_eq_split hrest0_le hrest0_suf, sliceCursorAt,
          memRegion_48_cells1_160 s0.sp]
        conv => arg 4; simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
        apply SepWP.exists_elim; intro v_stk0
        wp_steps_sync_pool ((blkPl_296).base + 112#64)
        simp only [State.setMem_setMem]
        apply SepWP.fold (pointsTo64_pair_entails_memRegion16 x.slot rest0Ptr (BitVec.ofNat 64 rest0.length)) (by sep_focus)
        apply SepWP.fold (pointsToBytes_prefix_join hrest0_le hrest0_suf) (by sep_focus)
        wp_reach; intro hinvm'
        refine SepWPp.weaken_pre (Entails.of_eq (by dsimp only [polyDecoderErrFrame]; sep_ac_rfl))
          (polyDecoder_from_err_exit_cl_placed hFromCall hnone (by decide : KindNoHeap 0x8000000000000007#64)
            (by omega) (by omega) hevs0 rfl hfits0 hsp_align'
            (by simp only [arm64_norm]) (by simp only [arm64_norm, hrunm]) (by simp only [arm64_norm, hspm])
            (by simp only [arm64_norm, htrm])
            ⟨by simp only [arm64_norm, hx26_m], by simp only [arm64_norm, hx27_m],
             by simp only [arm64_norm, hx28_m], by simp only [arm64_norm, hvregs_m]⟩ hinvm')
      · have hule := ule_len_of_ge hlt_len hrest0_lt
        have hsub := bv_len_sub_limit hlt_len
        have hlim_lt : rest0.length - len.toNat < 2 ^ 63 := by omega
        have hdrop_eq : x.bs.drop (x.bs.length - (rest0.length - len.toNat)) = rest0.drop len.toNat := by
          have hsuf := hrest0_suf; unfold IsDropSuffix at hsuf; conv => rhs; rw [hsuf, List.drop_drop]
          exact congrArg (List.drop · x.bs) (by omega)
        have hres0 :
            (mergeMessage PolynomialDecoder.mergeField (codecWireTypeToProto x.wt) x.msg x.bs 98).toOption =
              (mergeLoopBin PolynomialDecoder.mergeField
                (rest0.length - (rest0.length - len.toNat)) x.msg rest0 (rest0.length - len.toNat) 97).map
                  (fun m' => (m', x.bs.drop (x.bs.length - (rest0.length - len.toNat)))) := by
          rw [hwt_ld, ← mergeMessageBin_eq_proto_mergeMessage protoPrefixStep_polynomialDecoder_mergeField]
          simp only [mergeMessageBin, codecWireTypeToProto, bne_self_eq_false, Bool.false_eq_true,
            ↓reduceIte, proto_decodeVarint_toOption, hdv0, hlt_len, hdrop_eq]
          rcases mergeLoopBin PolynomialDecoder.mergeField
            (rest0.length - (rest0.length - len.toNat)) x.msg rest0 (rest0.length - len.toNat) 97 with _ | m' <;> rfl
        apply SepWPp.of_sepWP_lscro (mid := (blkPl_296).base + 164#64) hinvm
        conv => arg 4; dsimp only [decodeVarint2Spec, decodeVarint2SpecGen]
        conv => arg 4; rw [decodeVarint2_pool_of_some A lim hdv0, decodeVarint2Stack_eq]
        conv => arg 4; simp only [hdv0, sepConj_assoc]
        wp_focus_pure; rintro ⟨hsm0, hsm1⟩
        wp_focus_pure; intro htrm
        conv => arg 4; simp only [sepConj_assoc, arm64_norm]
        apply SepWP.fold (polyBelow_decodeVarint2_entails s0.sp) (by sep_focus)
        conv => arg 4; rw [sliceCursorAfter_eq_split hrest0_le hrest0_suf, sliceCursorAt]
        conv => arg 4; simp only [sepConj_assoc]
        wp_steps_sync_pool ((blkPl_296).base + 164#64)
        simp only [State.setMem_setMem]
        wp_reach; intro hinvm'
        have hevs_init : PolyMergeLoopEnv (2 * (x.bs.length - rest0.length)) x.bs.length
            (polyDecoderCapBound x) [] := .nil
        have hcap_init : x.msg.pts.length + rest0.length ≤ polyDecoderCapBound x := by
          dsimp only [polyDecoderCapBound]; omega
        refine SepWPp.weaken_pre
          (Entails.of_eq (by rw [polyDecoderLoopPre, sliceCursorAfter_eq_split hrest0_le hrest0_suf, sliceCursorAt]; sep_ac_rfl))
          (polyDecoder_loop_ok_cro hFromCall hPushCall hVarintCall hSkipCall hBytesCall hGrowCall
            hFit0 hsp_align' hlim_lt rest0.length x.msg rest0 st0 [] _
            (Nat.le_refl _) hrest0_le (by omega) hcap_init hrest0_suf hevs_init rfl hres0
            (by simp only [arm64_norm]) (by simp only [arm64_norm, hrunm]) (by simp only [arm64_norm, hspm])
            (by simp only [arm64_norm, htrm])
            (by simp only [arm64_norm, hx19_m]) (by simp only [arm64_norm, hx20_m])
            (by simp only [arm64_norm]) (by simp only [arm64_norm, hsm1, hsub])
            (by simp only [arm64_norm]) (by simp only [arm64_norm])
            ⟨by simp only [arm64_norm, hx26_m], by simp only [arm64_norm, hx27_m],
             by simp only [arm64_norm, hx28_m], by simp only [arm64_norm, hvregs_m]⟩ hinvm')
  · have hbeq := wt_beq_two_of_ne_lengthDelimited h_1 hwt_ld
    have hbne1 : (BitVec.truncate 32 (s0.readReg64 (Reg.gpr 0#5)) &&& 255#32 != 2#32) = true := by
      simp only [bne, hbeq, Bool.not_false]
    have hbne2 : (BitVec.truncate 32 (BitVec.zeroExtend 64 (BitVec.truncate 32 (s0.readReg64 (Reg.gpr 0#5))) &&& 255#64) != 2#32) = true := by
      rw [truncate32_zeroExtend64_and_255_eq, h_1]
      cases hxwt : x.wt <;> first | exact absurd hxwt hwt_ld | decide
    have hbne3 : (BitVec.truncate 32 (BitVec.zeroExtend 64 (BitVec.truncate 32 (s0.readReg64 (Reg.gpr 0#5)) &&& 255#32)) != 2#32) = true := by
      rw [← hbne1]; congr 2; bv_bits
    have hnone :
        (mergeMessage PolynomialDecoder.mergeField (codecWireTypeToProto x.wt) x.msg x.bs 98).toOption = none := by
      rw [← mergeMessageBin_eq_proto_mergeMessage protoPrefixStep_polynomialDecoder_mergeField]
      cases hxwt : x.wt <;> first | exact absurd hxwt hwt_ld | rfl
    apply SepWPp.of_sepWP_lscro (mid := (blkPl_296).base + 112#64) hinv0
    conv => arg 4; rw [stackAt_polyMerge_prologue s0.sp, sliceCursorAt, memRegion_48_wtErr160 s0.sp]
    conv => arg 4; simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
    apply SepWP.exists_elim; intro v0; apply SepWP.exists_elim; intro v1; apply SepWP.exists_elim; intro v2
    apply SepWP.exists_elim; intro v3; apply SepWP.exists_elim; intro v4; apply SepWP.exists_elim; intro v5
    apply SepWP.exists_elim; intro v6; apply SepWP.exists_elim; intro v7; apply SepWP.exists_elim; intro v8
    apply SepWP.exists_elim; intro v9
    apply SepWP.exists_elim; intro b_wt1; apply SepWP.exists_elim; intro b_wt0; apply SepWP.exists_elim; intro v_wt0
    wp_steps_sync_pool ((blkPl_296).base + 112#64)
    simp only [State.setMem_setMem]
    apply SepWP.fold (polySavedRegs_entails_any s0.sp s0 v3) (by unfold polySavedRegs; sep_focus)
    apply SepWP.fold (wtErr160_entails_memRegion40 s0.sp _ _) (by sep_focus)
    apply SepWP.fold (pointsTo64_pair_entails_memRegion16 x.slot x.ptr (BitVec.ofNat 64 x.bs.length)) (by sep_focus)
    wp_reach; intro hinv0'
    refine SepWPp.weaken_pre (Entails.of_eq (by dsimp only [polyDecoderErrFrame]; sep_ac_rfl))
      (polyDecoder_from_err_exit_cl_placed hFromCall hnone (by decide : KindNoHeap 0x8000000000000006#64)
        (by omega) (by omega) hevs0 rfl hfits0 hsp_align'
        (by simp only [arm64_norm]) (by simp only [arm64_norm, hrun]) (by simp only [arm64_norm])
        (by simp only [arm64_norm])
        ⟨by simp only [arm64_norm], by simp only [arm64_norm],
         by simp only [arm64_norm], by simp only [arm64_norm]⟩ hinv0')

/-! ## 2. Code-Loaded (`withLsCodeLoaded`) & Plain-Callee `[LibsignalPlacement]` Wrappers -/

/-- Code-loaded (`withLsCodeLoaded` on `261/257/291/263` + `withLsCodeRoLoaded` on `290` +
`growOneVecU8BudgetSpec`) contract-parameterized `[LibsignalPlacement]` verification of
`PolynomialDecoder::merge` (Block `296`). -/
theorem polyDecoderMerge_cl_placed_ok_of_contracts [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {H : LibsignalHooks}
    (hFromCall : subroutine_ok ((blkPC_296).rebase (blkPl_296).base H) (lsmpl.base 261)
      (withLsCodeLoaded lsmpl (decodeErrorFromBudgetSpec M A lim)))
    (hPushCall : subroutine_ok ((blkPC_296).rebase (blkPl_296).base H) (lsmpl.base 257)
      (withLsCodeLoaded lsmpl (decodeErrorPushMergeBudgetSpec M A lim)))
    (hVarintCall : subroutine_ok ((blkPC_296).rebase (blkPl_296).base H) (lsmpl.base 291)
      (withLsCodeLoaded lsmpl (decodeVarint2Spec A lim)))
    (hSkipCall : subroutine_ok ((blkPC_296).rebase (blkPl_296).base H) (lsmpl.base 263)
      (withLsCodeLoaded lsmpl (skipField3Spec A lim)))
    (hBytesCall : subroutine_ok ((blkPC_296).rebase (blkPl_296).base H) (lsmpl.base 290)
      (withLsCodeRoLoaded lsmpl (bytesMerge3RawBudgetSpec A lim)))
    (hGrowCall : subroutine_ok ((blkPC_296).rebase (blkPl_296).base H)
      (lsmpl.base 621)
      (withLsCodeRoLoaded lsmpl (growOneVecU8BudgetSpec M A lim))) :
    subroutine_ok ((blkPC_296).rebase (blkPl_296).base H) (blkPl_296).base
      (withLsCodeRoLoaded lsmpl (polyDecoderMergeSpec A lim)) :=
  polyDecoderMerge_cro_placed_ok_of_contracts
    (subroutine_ok_withLsCodeRoLoaded_of_withLsCodeLoaded_mm hFromCall)
    (subroutine_ok_withLsCodeRoLoaded_of_withLsCodeLoaded_mm hPushCall)
    (subroutine_ok_withLsCodeRoLoaded_of_withLsCodeLoaded_mm hVarintCall)
    (subroutine_ok_withLsCodeRoLoaded_of_withLsCodeLoaded_mm hSkipCall) hBytesCall hGrowCall

/-- Plain-callee `[LibsignalPlacement]` step wrapper for tag 1 (`pts_needed : u32`). -/
theorem polyDecoder_tag1_step_placed [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {H : LibsignalHooks}
    (hFromCall : subroutine_ok ((blkPC_296).rebase (blkPl_296).base H) (lsmpl.base 261) (decodeErrorFromBudgetSpec M A lim))
    (hPushCall : subroutine_ok ((blkPC_296).rebase (blkPl_296).base H) (lsmpl.base 257) (decodeErrorPushMergeBudgetSpec M A lim))
    (hVarintCall : subroutine_ok ((blkPC_296).rebase (blkPl_296).base H) (lsmpl.base 291) (decodeVarint2Spec A lim))
    {x : PolyDecoderMergeGhost} {st0 st_cur : M.σ} {R : SepProp} {s0 s : State}
    {m : PolynomialDecoder} {rest : List (BitVec 8)} {iwt : WireType} {limit f_acc f_rem : Nat} {evs_acc : List AllocEvent} :
    (s0.sp &&& 15#64 == 0#64) = true → rest.length ≤ x.bs.length → rest.length < 2 ^ 63 → IsDropSuffix x.bs rest →
    2 ≤ f_rem → f_acc + 2 ≤ 2 * x.bs.length + 2 →
    PolyMergeLoopEnv f_acc x.bs.length (polyDecoderCapBound x) evs_acc → st_cur = M.stepEvents evs_acc st0 →
    FitsEnv M lim st_cur (PolyMergeLoopEnv f_rem x.bs.length (polyDecoderCapBound x)) →
    (iwt ≠ .varint → (mergeMessage PolynomialDecoder.mergeField (codecWireTypeToProto x.wt) x.msg x.bs 98).toOption = none) →
    (iwt = .varint → decodeVarint rest = none → (mergeMessage PolynomialDecoder.mergeField (codecWireTypeToProto x.wt) x.msg x.bs 98).toOption = none) →
    (∀ (v : BitVec 64) (rest' : List (BitVec 8)) (s' : State), iwt = .varint → decodeVarint rest = some (v, rest') →
      s'.pc = (blkPl_296).base + 164#64 → s'.status = .Running → s'.sp = s0.sp - 160#64 → s'.trace = s0.trace →
      s'.readReg64 (Reg.gpr 19#5) = x.bufRef → s'.readReg64 (Reg.gpr 20#5) = x.msgPtr →
      s'.readReg64 (Reg.gpr 21#5) = x.slot → s'.readReg64 (Reg.gpr 22#5) = BitVec.ofNat 64 limit →
      s'.readReg64 (Reg.gpr 23#5) = 1#64 → s'.readReg64 (Reg.gpr 24#5) = 24#64 → PolyCalleeSaved s0 s' → LibsignalCodeRoLoaded lsmpl s'.mem →
      SepWPp ((blkPC_296).rebase (blkPl_296).base H) (s0.readReg64 Reg.lr) s'
        (polyDecoderLoopPre A lim st_cur s0 s' x.msgPtr x.bufRef x.slot x.ptr { m with ptsNeeded := v.truncate 32 } x.bs rest')
        (WppPost (polyDecoderMergeSpec A lim) (x, st0) R s0) (WppBudgetPanic (polyDecoderMergeSpec A lim) (x, st0) R s0)) →
    s.pc = (blkPl_296).base + 344#64 → s.status = .Running → s.sp = s0.sp - 160#64 → s.trace = s0.trace →
    s.readReg64 (Reg.gpr 0#5) = BitVec.ofNat 64 iwt.toNat → s.readReg64 (Reg.gpr 19#5) = x.bufRef → s.readReg64 (Reg.gpr 20#5) = x.msgPtr →
    s.readReg64 (Reg.gpr 21#5) = x.slot → s.readReg64 (Reg.gpr 22#5) = BitVec.ofNat 64 limit →
    s.readReg64 (Reg.gpr 23#5) = 1#64 → s.readReg64 (Reg.gpr 24#5) = 24#64 → PolyCalleeSaved s0 s → LibsignalCodeRoLoaded lsmpl s.mem →
    SepWPp ((blkPC_296).rebase (blkPl_296).base H) (s0.readReg64 Reg.lr) s
      (polyDecoderLoopPre A lim st_cur s0 s x.msgPtr x.bufRef x.slot x.ptr m x.bs rest)
      (WppPost (polyDecoderMergeSpec A lim) (x, st0) R s0) (WppBudgetPanic (polyDecoderMergeSpec A lim) (x, st0) R s0) :=
  polyDecoder_tag1_step_cro (subroutine_ok_withLsCodeRoLoaded_of_plain hFromCall)
    (subroutine_ok_withLsCodeRoLoaded_of_plain hPushCall) (subroutine_ok_withLsCodeRoLoaded_of_plain hVarintCall)

/-- Plain-callee `[LibsignalPlacement]` step wrapper for tag 2 (`polys : u32`). -/
theorem polyDecoder_tag2_step_placed [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {H : LibsignalHooks}
    (hFromCall : subroutine_ok ((blkPC_296).rebase (blkPl_296).base H) (lsmpl.base 261) (decodeErrorFromBudgetSpec M A lim))
    (hPushCall : subroutine_ok ((blkPC_296).rebase (blkPl_296).base H) (lsmpl.base 257) (decodeErrorPushMergeBudgetSpec M A lim))
    (hVarintCall : subroutine_ok ((blkPC_296).rebase (blkPl_296).base H) (lsmpl.base 291) (decodeVarint2Spec A lim))
    {x : PolyDecoderMergeGhost} {st0 st_cur : M.σ} {R : SepProp} {s0 s : State}
    {m : PolynomialDecoder} {rest : List (BitVec 8)} {iwt : WireType} {limit f_acc f_rem : Nat} {evs_acc : List AllocEvent} :
    (s0.sp &&& 15#64 == 0#64) = true → rest.length ≤ x.bs.length → rest.length < 2 ^ 63 → IsDropSuffix x.bs rest →
    2 ≤ f_rem → f_acc + 2 ≤ 2 * x.bs.length + 2 →
    PolyMergeLoopEnv f_acc x.bs.length (polyDecoderCapBound x) evs_acc → st_cur = M.stepEvents evs_acc st0 →
    FitsEnv M lim st_cur (PolyMergeLoopEnv f_rem x.bs.length (polyDecoderCapBound x)) →
    (iwt ≠ .varint → (mergeMessage PolynomialDecoder.mergeField (codecWireTypeToProto x.wt) x.msg x.bs 98).toOption = none) →
    (iwt = .varint → decodeVarint rest = none → (mergeMessage PolynomialDecoder.mergeField (codecWireTypeToProto x.wt) x.msg x.bs 98).toOption = none) →
    (∀ (v : BitVec 64) (rest' : List (BitVec 8)) (s' : State), iwt = .varint → decodeVarint rest = some (v, rest') →
      s'.pc = (blkPl_296).base + 164#64 → s'.status = .Running → s'.sp = s0.sp - 160#64 → s'.trace = s0.trace →
      s'.readReg64 (Reg.gpr 19#5) = x.bufRef → s'.readReg64 (Reg.gpr 20#5) = x.msgPtr →
      s'.readReg64 (Reg.gpr 21#5) = x.slot → s'.readReg64 (Reg.gpr 22#5) = BitVec.ofNat 64 limit →
      s'.readReg64 (Reg.gpr 23#5) = 1#64 → s'.readReg64 (Reg.gpr 24#5) = 24#64 → PolyCalleeSaved s0 s' → LibsignalCodeRoLoaded lsmpl s'.mem →
      SepWPp ((blkPC_296).rebase (blkPl_296).base H) (s0.readReg64 Reg.lr) s'
        (polyDecoderLoopPre A lim st_cur s0 s' x.msgPtr x.bufRef x.slot x.ptr { m with polys := v.truncate 32 } x.bs rest')
        (WppPost (polyDecoderMergeSpec A lim) (x, st0) R s0) (WppBudgetPanic (polyDecoderMergeSpec A lim) (x, st0) R s0)) →
    s.pc = (blkPl_296).base + 240#64 → s.status = .Running → s.sp = s0.sp - 160#64 → s.trace = s0.trace →
    s.readReg64 (Reg.gpr 0#5) = BitVec.ofNat 64 iwt.toNat → s.readReg64 (Reg.gpr 19#5) = x.bufRef → s.readReg64 (Reg.gpr 20#5) = x.msgPtr →
    s.readReg64 (Reg.gpr 21#5) = x.slot → s.readReg64 (Reg.gpr 22#5) = BitVec.ofNat 64 limit →
    s.readReg64 (Reg.gpr 23#5) = 1#64 → s.readReg64 (Reg.gpr 24#5) = 24#64 → PolyCalleeSaved s0 s → LibsignalCodeRoLoaded lsmpl s.mem →
    SepWPp ((blkPC_296).rebase (blkPl_296).base H) (s0.readReg64 Reg.lr) s
      (polyDecoderLoopPre A lim st_cur s0 s x.msgPtr x.bufRef x.slot x.ptr m x.bs rest)
      (WppPost (polyDecoderMergeSpec A lim) (x, st0) R s0) (WppBudgetPanic (polyDecoderMergeSpec A lim) (x, st0) R s0) :=
  polyDecoder_tag2_step_cro (subroutine_ok_withLsCodeRoLoaded_of_plain hFromCall)
    (subroutine_ok_withLsCodeRoLoaded_of_plain hPushCall) (subroutine_ok_withLsCodeRoLoaded_of_plain hVarintCall)

/-- Plain-callee `[LibsignalPlacement]` step wrapper for tag 3 (`pts : Vec<Vec<u8>>`). -/
theorem polyDecoder_tag3_step_placed [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {H : LibsignalHooks}
    (hFromCall : subroutine_ok ((blkPC_296).rebase (blkPl_296).base H) (lsmpl.base 261) (decodeErrorFromBudgetSpec M A lim))
    (hPushCall : subroutine_ok ((blkPC_296).rebase (blkPl_296).base H) (lsmpl.base 257) (decodeErrorPushMergeBudgetSpec M A lim))
    (hBytesCall : subroutine_ok ((blkPC_296).rebase (blkPl_296).base H) (lsmpl.base 290) (withLsCodeRoLoaded lsmpl (bytesMerge3RawBudgetSpec A lim)))
    (hGrowCall : subroutine_ok ((blkPC_296).rebase (blkPl_296).base H)
      (lsmpl.base 621)
      (withLsCodeRoLoaded lsmpl (growOneVecU8BudgetSpec M A lim)))
    {x : PolyDecoderMergeGhost} {st0 st_cur : M.σ} {R : SepProp} {s0 s : State}
    {m : PolynomialDecoder} {rest : List (BitVec 8)} {iwt : WireType} {limit f_acc f_rem : Nat} {evs_acc : List AllocEvent} :
    (s0.sp &&& 15#64 == 0#64) = true → rest.length ≤ x.bs.length →
    m.pts.length + rest.length < 2 ^ 56 → IsDropSuffix x.bs rest → m.pts.length < polyDecoderCapBound x →
    2 * rest.length + 2 ≤ f_rem → f_acc + 2 ≤ 2 * x.bs.length + 2 →
    PolyMergeLoopEnv f_acc x.bs.length (polyDecoderCapBound x) evs_acc → st_cur = M.stepEvents evs_acc st0 →
    FitsEnv M lim st_cur (PolyMergeLoopEnv f_rem x.bs.length (polyDecoderCapBound x)) →
    (mergeBytes iwt rest = none → (mergeMessage PolynomialDecoder.mergeField (codecWireTypeToProto x.wt) x.msg x.bs 98).toOption = none) →
    (∀ (v rest' : List (BitVec 8)) (st_next : M.σ) (evs_step : List AllocEvent) (s' : State),
      mergeBytes iwt rest = some (v, rest') →
      PolyMergeLoopEnv (2 * v.length + 2) x.bs.length (polyDecoderCapBound x) evs_step → st_next = M.stepEvents evs_step st_cur →
      s'.pc = (blkPl_296).base + 164#64 → s'.status = .Running → s'.sp = s0.sp - 160#64 → s'.trace = s0.trace →
      s'.readReg64 (Reg.gpr 19#5) = x.bufRef → s'.readReg64 (Reg.gpr 20#5) = x.msgPtr →
      s'.readReg64 (Reg.gpr 21#5) = x.slot → s'.readReg64 (Reg.gpr 22#5) = BitVec.ofNat 64 limit →
      s'.readReg64 (Reg.gpr 23#5) = 1#64 → s'.readReg64 (Reg.gpr 24#5) = 24#64 → PolyCalleeSaved s0 s' → LibsignalCodeRoLoaded lsmpl s'.mem →
      SepWPp ((blkPC_296).rebase (blkPl_296).base H) (s0.readReg64 Reg.lr) s'
        (polyDecoderLoopPre A lim st_next s0 s' x.msgPtr x.bufRef x.slot x.ptr { m with pts := m.pts ++ [v] } x.bs rest')
        (WppPost (polyDecoderMergeSpec A lim) (x, st0) R s0) (WppBudgetPanic (polyDecoderMergeSpec A lim) (x, st0) R s0)) →
    s.pc = (blkPl_296).base + 376#64 → s.status = .Running → s.sp = s0.sp - 160#64 → s.trace = s0.trace →
    s.readReg64 (Reg.gpr 0#5) = BitVec.ofNat 64 iwt.toNat → s.readReg64 (Reg.gpr 19#5) = x.bufRef → s.readReg64 (Reg.gpr 20#5) = x.msgPtr →
    s.readReg64 (Reg.gpr 21#5) = x.slot → s.readReg64 (Reg.gpr 22#5) = BitVec.ofNat 64 limit →
    s.readReg64 (Reg.gpr 23#5) = 1#64 → s.readReg64 (Reg.gpr 24#5) = 24#64 → PolyCalleeSaved s0 s → LibsignalCodeRoLoaded lsmpl s.mem →
    SepWPp ((blkPC_296).rebase (blkPl_296).base H) (s0.readReg64 Reg.lr) s
      (polyDecoderLoopPre A lim st_cur s0 s x.msgPtr x.bufRef x.slot x.ptr m x.bs rest)
      (WppPost (polyDecoderMergeSpec A lim) (x, st0) R s0) (WppBudgetPanic (polyDecoderMergeSpec A lim) (x, st0) R s0) :=
  polyDecoder_tag3_step_cro (subroutine_ok_withLsCodeRoLoaded_of_plain hFromCall)
    (subroutine_ok_withLsCodeRoLoaded_of_plain hPushCall) hBytesCall hGrowCall

/-- Plain-callee `[LibsignalPlacement]` step wrapper for tag 4 (`is_complete : bool`). -/
theorem polyDecoder_tag4_step_placed [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {H : LibsignalHooks}
    (hFromCall : subroutine_ok ((blkPC_296).rebase (blkPl_296).base H) (lsmpl.base 261) (decodeErrorFromBudgetSpec M A lim))
    (hPushCall : subroutine_ok ((blkPC_296).rebase (blkPl_296).base H) (lsmpl.base 257) (decodeErrorPushMergeBudgetSpec M A lim))
    (hVarintCall : subroutine_ok ((blkPC_296).rebase (blkPl_296).base H) (lsmpl.base 291) (decodeVarint2Spec A lim))
    {x : PolyDecoderMergeGhost} {st0 st_cur : M.σ} {R : SepProp} {s0 s : State}
    {m : PolynomialDecoder} {rest : List (BitVec 8)} {iwt : WireType} {limit f_acc f_rem : Nat} {evs_acc : List AllocEvent} :
    (s0.sp &&& 15#64 == 0#64) = true → rest.length ≤ x.bs.length → rest.length < 2 ^ 63 → IsDropSuffix x.bs rest →
    2 ≤ f_rem → f_acc + 2 ≤ 2 * x.bs.length + 2 →
    PolyMergeLoopEnv f_acc x.bs.length (polyDecoderCapBound x) evs_acc → st_cur = M.stepEvents evs_acc st0 →
    FitsEnv M lim st_cur (PolyMergeLoopEnv f_rem x.bs.length (polyDecoderCapBound x)) →
    (iwt ≠ .varint → (mergeMessage PolynomialDecoder.mergeField (codecWireTypeToProto x.wt) x.msg x.bs 98).toOption = none) →
    (iwt = .varint → decodeVarint rest = none → (mergeMessage PolynomialDecoder.mergeField (codecWireTypeToProto x.wt) x.msg x.bs 98).toOption = none) →
    (∀ (v : BitVec 64) (rest' : List (BitVec 8)) (s' : State), iwt = .varint → decodeVarint rest = some (v, rest') →
      s'.pc = (blkPl_296).base + 164#64 → s'.status = .Running → s'.sp = s0.sp - 160#64 → s'.trace = s0.trace →
      s'.readReg64 (Reg.gpr 19#5) = x.bufRef → s'.readReg64 (Reg.gpr 20#5) = x.msgPtr →
      s'.readReg64 (Reg.gpr 21#5) = x.slot → s'.readReg64 (Reg.gpr 22#5) = BitVec.ofNat 64 limit →
      s'.readReg64 (Reg.gpr 23#5) = 1#64 → s'.readReg64 (Reg.gpr 24#5) = 24#64 → PolyCalleeSaved s0 s' → LibsignalCodeRoLoaded lsmpl s'.mem →
      SepWPp ((blkPC_296).rebase (blkPl_296).base H) (s0.readReg64 Reg.lr) s'
        (polyDecoderLoopPre A lim st_cur s0 s' x.msgPtr x.bufRef x.slot x.ptr { m with isComplete := v != 0#64 } x.bs rest')
        (WppPost (polyDecoderMergeSpec A lim) (x, st0) R s0) (WppBudgetPanic (polyDecoderMergeSpec A lim) (x, st0) R s0)) →
    s.pc = (blkPl_296).base + 288#64 → s.status = .Running → s.sp = s0.sp - 160#64 → s.trace = s0.trace →
    s.readReg64 (Reg.gpr 0#5) = BitVec.ofNat 64 iwt.toNat → s.readReg64 (Reg.gpr 19#5) = x.bufRef → s.readReg64 (Reg.gpr 20#5) = x.msgPtr →
    s.readReg64 (Reg.gpr 21#5) = x.slot → s.readReg64 (Reg.gpr 22#5) = BitVec.ofNat 64 limit →
    s.readReg64 (Reg.gpr 23#5) = 1#64 → s.readReg64 (Reg.gpr 24#5) = 24#64 → PolyCalleeSaved s0 s → LibsignalCodeRoLoaded lsmpl s.mem →
    SepWPp ((blkPC_296).rebase (blkPl_296).base H) (s0.readReg64 Reg.lr) s
      (polyDecoderLoopPre A lim st_cur s0 s x.msgPtr x.bufRef x.slot x.ptr m x.bs rest)
      (WppPost (polyDecoderMergeSpec A lim) (x, st0) R s0) (WppBudgetPanic (polyDecoderMergeSpec A lim) (x, st0) R s0) :=
  polyDecoder_tag4_step_cro (subroutine_ok_withLsCodeRoLoaded_of_plain hFromCall)
    (subroutine_ok_withLsCodeRoLoaded_of_plain hPushCall) (subroutine_ok_withLsCodeRoLoaded_of_plain hVarintCall)

/-- Plain-callee `[LibsignalPlacement]` loop-exit wrapper at `+0x0a4`. -/
theorem polyDecoder_loop_le_exit_placed [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {H : LibsignalHooks}
    (hFromCall : subroutine_ok ((blkPC_296).rebase (blkPl_296).base H) (lsmpl.base 261) (decodeErrorFromBudgetSpec M A lim))
    {x : PolyDecoderMergeGhost} {st0 st_cur : M.σ} {R : SepProp} {s0 s : State}
    {m : PolynomialDecoder} {cur : List (BitVec 8)} {limit : Nat} {evs_acc : List AllocEvent} :
    cur.length ≤ limit → (s0.sp &&& 15#64 == 0#64) = true → cur.length ≤ x.bs.length → IsDropSuffix x.bs cur → limit < 2 ^ 63 →
    PolyMergeLoopEnv (2 * (x.bs.length - cur.length)) x.bs.length (polyDecoderCapBound x) evs_acc → st_cur = M.stepEvents evs_acc st0 →
    FitsEnv M lim st_cur (PolyMergeLoopEnv (2 * cur.length + 2) x.bs.length (polyDecoderCapBound x)) →
    (mergeMessage PolynomialDecoder.mergeField (codecWireTypeToProto x.wt) x.msg x.bs 98).toOption =
      (mergeLoopBin PolynomialDecoder.mergeField (cur.length - limit) m cur limit 97).map (fun m' => (m', x.bs.drop (x.bs.length - limit))) →
    s.pc = (blkPl_296).base + 164#64 → s.status = .Running → s.sp = s0.sp - 160#64 → s.trace = s0.trace →
    s.readReg64 (Reg.gpr 21#5) = x.slot → s.readReg64 (Reg.gpr 22#5) = BitVec.ofNat 64 limit →
    PolyCalleeSaved s0 s → LibsignalCodeRoLoaded lsmpl s.mem →
    SepWPp ((blkPC_296).rebase (blkPl_296).base H) (s0.readReg64 Reg.lr) s
      (polyDecoderLoopPre A lim st_cur s0 s x.msgPtr x.bufRef x.slot x.ptr m x.bs cur)
      (WppPost (polyDecoderMergeSpec A lim) (x, st0) R s0) (WppBudgetPanic (polyDecoderMergeSpec A lim) (x, st0) R s0) :=
  polyDecoder_loop_le_exit_cro (subroutine_ok_withLsCodeRoLoaded_of_plain hFromCall)

/-- Plain-callee `[LibsignalPlacement]` key-decoding step wrapper at `+0x0a4`. -/
theorem polyDecoder_decode_key_step_placed [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {H : LibsignalHooks}
    (hFromCall : subroutine_ok ((blkPC_296).rebase (blkPl_296).base H) (lsmpl.base 261) (decodeErrorFromBudgetSpec M A lim))
    (hVarintCall : subroutine_ok ((blkPC_296).rebase (blkPl_296).base H) (lsmpl.base 291) (decodeVarint2Spec A lim))
    {x : PolyDecoderMergeGhost} {st0 st_cur : M.σ} {R : SepProp} {s0 s : State}
    {m : PolynomialDecoder} {cur : List (BitVec 8)} {limit : Nat} {evs_acc : List AllocEvent} :
    ¬ cur.length ≤ limit → (s0.sp &&& 15#64 == 0#64) = true → cur.length ≤ x.bs.length → cur.length < 2 ^ 63 → IsDropSuffix x.bs cur →
    PolyMergeLoopEnv (2 * (x.bs.length - cur.length)) x.bs.length (polyDecoderCapBound x) evs_acc → st_cur = M.stepEvents evs_acc st0 →
    FitsEnv M lim st_cur (PolyMergeLoopEnv (2 * cur.length + 2) x.bs.length (polyDecoderCapBound x)) →
    (mergeMessage PolynomialDecoder.mergeField (codecWireTypeToProto x.wt) x.msg x.bs 98).toOption =
      (mergeLoopBin PolynomialDecoder.mergeField (cur.length - limit) m cur limit 97).map (fun m' => (m', x.bs.drop (x.bs.length - limit))) →
    (∀ (key : BitVec 64) (iwt : WireType) (rest : List (BitVec 8)) (s' : State),
      decodeVarint cur = some (key, rest) → ¬ 2 ^ 32 ≤ key.toNat → WireType.ofNat? (key.toNat % 8) = some iwt → ¬ key.toNat / 8 < 1 →
      s'.pc = (blkPl_296).base + 216#64 → s'.status = .Running → s'.sp = s0.sp - 160#64 → s'.trace = s0.trace →
      s'.readReg64 (Reg.gpr 0#5) = BitVec.ofNat 64 iwt.toNat → s'.readReg64 (Reg.gpr 1#5) = BitVec.ofNat 64 (key.toNat / 8) →
      s'.readReg64 (Reg.gpr 19#5) = x.bufRef → s'.readReg64 (Reg.gpr 20#5) = x.msgPtr →
      s'.readReg64 (Reg.gpr 21#5) = x.slot → s'.readReg64 (Reg.gpr 22#5) = BitVec.ofNat 64 limit →
      s'.readReg64 (Reg.gpr 23#5) = 1#64 → s'.readReg64 (Reg.gpr 24#5) = 24#64 → PolyCalleeSaved s0 s' → LibsignalCodeRoLoaded lsmpl s'.mem →
      SepWPp ((blkPC_296).rebase (blkPl_296).base H) (s0.readReg64 Reg.lr) s'
        (polyDecoderLoopPre A lim st_cur s0 s' x.msgPtr x.bufRef x.slot x.ptr m x.bs rest)
        (WppPost (polyDecoderMergeSpec A lim) (x, st0) R s0) (WppBudgetPanic (polyDecoderMergeSpec A lim) (x, st0) R s0)) →
    s.pc = (blkPl_296).base + 164#64 → s.status = .Running → s.sp = s0.sp - 160#64 → s.trace = s0.trace →
    s.readReg64 (Reg.gpr 19#5) = x.bufRef → s.readReg64 (Reg.gpr 20#5) = x.msgPtr →
    s.readReg64 (Reg.gpr 21#5) = x.slot → s.readReg64 (Reg.gpr 22#5) = BitVec.ofNat 64 limit →
    s.readReg64 (Reg.gpr 23#5) = 1#64 → s.readReg64 (Reg.gpr 24#5) = 24#64 → PolyCalleeSaved s0 s → LibsignalCodeRoLoaded lsmpl s.mem →
    SepWPp ((blkPC_296).rebase (blkPl_296).base H) (s0.readReg64 Reg.lr) s
      (polyDecoderLoopPre A lim st_cur s0 s x.msgPtr x.bufRef x.slot x.ptr m x.bs cur)
      (WppPost (polyDecoderMergeSpec A lim) (x, st0) R s0) (WppBudgetPanic (polyDecoderMergeSpec A lim) (x, st0) R s0) :=
  polyDecoder_decode_key_step_cro (subroutine_ok_withLsCodeRoLoaded_of_plain hFromCall)
    (subroutine_ok_withLsCodeRoLoaded_of_plain hVarintCall)

/-- Plain-callee `[LibsignalPlacement]` main-loop wrapper at `+0x0a4`. -/
theorem polyDecoder_loop_ok_placed [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {H : LibsignalHooks}
    (hFromCall : subroutine_ok ((blkPC_296).rebase (blkPl_296).base H) (lsmpl.base 261) (decodeErrorFromBudgetSpec M A lim))
    (hPushCall : subroutine_ok ((blkPC_296).rebase (blkPl_296).base H) (lsmpl.base 257) (decodeErrorPushMergeBudgetSpec M A lim))
    (hVarintCall : subroutine_ok ((blkPC_296).rebase (blkPl_296).base H) (lsmpl.base 291) (decodeVarint2Spec A lim))
    (hSkipCall : subroutine_ok ((blkPC_296).rebase (blkPl_296).base H) (lsmpl.base 263) (skipField3Spec A lim))
    (hBytesCall : subroutine_ok ((blkPC_296).rebase (blkPl_296).base H) (lsmpl.base 290) (withLsCodeRoLoaded lsmpl (bytesMerge3RawBudgetSpec A lim)))
    (hGrowCall : subroutine_ok ((blkPC_296).rebase (blkPl_296).base H)
      (lsmpl.base 621)
      (withLsCodeRoLoaded lsmpl (growOneVecU8BudgetSpec M A lim)))
    {x : PolyDecoderMergeGhost} {st0 : M.σ} {R : SepProp} {s0 : State} {limit : Nat} :
    FitsEnv M lim st0 (PolyDecoderMergeEnv x) → (s0.sp &&& 15#64 == 0#64) = true → limit < 2 ^ 63 →
    ∀ (n : Nat) (m : PolynomialDecoder) (cur : List (BitVec 8)) (st_cur : M.σ) (evs_acc : List AllocEvent) (s : State),
      cur.length ≤ n → cur.length ≤ x.bs.length →
      m.pts.length + cur.length < 2 ^ 56 → m.pts.length + cur.length ≤ polyDecoderCapBound x → IsDropSuffix x.bs cur →
      PolyMergeLoopEnv (2 * (x.bs.length - cur.length)) x.bs.length (polyDecoderCapBound x) evs_acc → st_cur = M.stepEvents evs_acc st0 →
      (mergeMessage PolynomialDecoder.mergeField (codecWireTypeToProto x.wt) x.msg x.bs 98).toOption =
        (mergeLoopBin PolynomialDecoder.mergeField (cur.length - limit) m cur limit 97).map (fun m' => (m', x.bs.drop (x.bs.length - limit))) →
      s.pc = (blkPl_296).base + 164#64 → s.status = .Running → s.sp = s0.sp - 160#64 → s.trace = s0.trace →
      s.readReg64 (Reg.gpr 19#5) = x.bufRef → s.readReg64 (Reg.gpr 20#5) = x.msgPtr →
      s.readReg64 (Reg.gpr 21#5) = x.slot → s.readReg64 (Reg.gpr 22#5) = BitVec.ofNat 64 limit →
      s.readReg64 (Reg.gpr 23#5) = 1#64 → s.readReg64 (Reg.gpr 24#5) = 24#64 → PolyCalleeSaved s0 s → LibsignalCodeRoLoaded lsmpl s.mem →
      SepWPp ((blkPC_296).rebase (blkPl_296).base H) (s0.readReg64 Reg.lr) s
        (polyDecoderLoopPre A lim st_cur s0 s x.msgPtr x.bufRef x.slot x.ptr m x.bs cur)
        (WppPost (polyDecoderMergeSpec A lim) (x, st0) R s0) (WppBudgetPanic (polyDecoderMergeSpec A lim) (x, st0) R s0) :=
  polyDecoder_loop_ok_cro (subroutine_ok_withLsCodeRoLoaded_of_plain hFromCall)
    (subroutine_ok_withLsCodeRoLoaded_of_plain hPushCall) (subroutine_ok_withLsCodeRoLoaded_of_plain hVarintCall)
    (subroutine_ok_withLsCodeRoLoaded_of_plain hSkipCall) hBytesCall hGrowCall

/-- Contract-parameterized placed budget verification of
`prost::encoding::message::merge::<PolynomialDecoder, &mut &[u8]>` (Block `296`), matching
`PolyDecoder.lean`'s `polyDecoderMerge_placed_ok_of_contracts`. -/
theorem polyDecoderMerge_placed_ok_of_contracts [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {H : LibsignalHooks}
    (hFromCall : subroutine_ok ((blkPC_296).rebase (blkPl_296).base H) (lsmpl.base 261) (decodeErrorFromBudgetSpec M A lim))
    (hPushCall : subroutine_ok ((blkPC_296).rebase (blkPl_296).base H) (lsmpl.base 257) (decodeErrorPushMergeBudgetSpec M A lim))
    (hVarintCall : subroutine_ok ((blkPC_296).rebase (blkPl_296).base H) (lsmpl.base 291) (decodeVarint2Spec A lim))
    (hSkipCall : subroutine_ok ((blkPC_296).rebase (blkPl_296).base H) (lsmpl.base 263) (skipField3Spec A lim))
    (hBytesCall : subroutine_ok ((blkPC_296).rebase (blkPl_296).base H) (lsmpl.base 290) (withLsCodeRoLoaded lsmpl (bytesMerge3RawBudgetSpec A lim)))
    (hGrowCall : subroutine_ok ((blkPC_296).rebase (blkPl_296).base H)
      (lsmpl.base 621)
      (withLsCodeRoLoaded lsmpl (growOneVecU8BudgetSpec M A lim))) :
    subroutine_ok ((blkPC_296).rebase (blkPl_296).base H) (blkPl_296).base
      (withLsCodeRoLoaded lsmpl (polyDecoderMergeSpec A lim)) :=
  polyDecoderMerge_cro_placed_ok_of_contracts
    (subroutine_ok_withLsCodeRoLoaded_of_plain hFromCall) (subroutine_ok_withLsCodeRoLoaded_of_plain hPushCall)
    (subroutine_ok_withLsCodeRoLoaded_of_plain hVarintCall) (subroutine_ok_withLsCodeRoLoaded_of_plain hSkipCall)
    hBytesCall hGrowCall

end LibsignalBinary.Proofs.SpqrV1.Prost.MessageMerge.PolyDecoderBudget
