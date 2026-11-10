/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SpqrV1.Prost.MessageMerge.PolyEncoderBudgetAux
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
# Tag-2 & Tag-3 `Vec<Vec<u8>>` Budget Step Lemmas for `PolynomialEncoder::merge` (Block `297`)

Proves the `withLsCodeRoLoaded`-threaded `Vec<Vec<u8>>` push step lemmas for tag 2 (`pts` at
`msgPtr`) and tag 3 (`polys` at `msgPtr + 24#64`) in `PolynomialEncoder::merge` on Block `297`.
-/

@[expose] public section

set_option autoImplicit false

namespace LibsignalBinary.Proofs.SpqrV1.Prost.MessageMerge.PolyEncoderBudgetSteps

open Arm64 ProofLib SepProp
open scoped CryptoVerification
open scoped CryptoVerification.CodeLayout
open scoped CryptoVerification.SpqrV1.Prost.MessageMerge
open CryptoVerification (LibsignalHooks LibsignalPlacement lsmpl)
open CryptoVerification.RustHeap
  (RustAlloc arrayAt vecAt vecBuf vecHeader vecOf vecU8 vecU8At)
open CryptoVerification.LibsignalProtoCodec (WireType mergeBytes)
open CryptoVerification.LibsignalTripleRatchet
  (KindNoHeap LibsignalCodeRoLoaded decodeErrorAtStackLen withLsCodeRoLoaded)
open CryptoVerification.LibsignalTripleRatchet.Prost
  (BytesMergeCapOk IsDropSuffix pointsTo64_pair_entails_memRegion16 pointsToBytes_prefix_join
   sliceCursorAfter sliceCursorAfter_eq_split sliceCursorAfter_join sliceCursorAt)
open CryptoVerification.LibsignalSpqrV1
  (PolynomialEncoder growOneVecU8Name newCapVecU8)
open CryptoVerification.LibsignalSpqrV1.Proto (mergeMessage)
open CryptoVerification.SpqrV1.Poly
  (protoPolynomialEncoderAt protoPolynomialEncoderIdxOff protoPolynomialEncoderPadOff
   protoPolynomialEncoderPadSize protoPolynomialEncoderPolysOff vecHeaderBytes vecVecU8At)
open CryptoVerification.SpqrV1.Prost.MessageMerge
  (PolyCalleeSaved PolyEncoderMergeGhost SepWPp.call_frame_keep_lscro SepWPp.call_frame_lscro
   SepWPp.of_sepWP_lscro WppPost blkPC_297 blkPl_297 bv64_add24_add8 bv64_add24_add16
   bv64_add_zero bv64_ofNat_add_one cells160_entails_memRegion32 codecWireTypeToProto
   extractLsb'_append64_0 extractLsb'_append64_64 grow_post_entails_ready
   iwt_bne_two_true_of_ne_len len_eq_cap_bne_false len_lt_cap_bne_true madd_24_eq madd_24_eq'
   memRegion_32_cells160 memRegion_48_cells1_160 memRegion_48_wtErr160 memRegion_split_24_cells
   mergeBytes_eq_none_of_ne_len mergeBytes_length polyBelowStack polyBelow_bytesMerge3
   polyBelow_bytesMerge3_entails polyBelow_decodeErrorHook polyBelow_decodeErrorHook_entails
   polyBelow_extHook polyBelow_extHook_entails polyEncoderToProto polySavedRegsAny
   vecBuf_vecU8_entails_grow_pre vecU8ArrayBytes vecU8At_stack_to_cells vecU8At_zero_eq_cells
   vecVecU8At_after_push vecVecU8At_after_push_24 wtErr160_entails_memRegion40)
open LibsignalBinary.Heap
  (AllocCostModel AllocEvent BudgetLimits FitsEnv RustCliAllocBudget)
open LibsignalBinary.Heap.RustStdAllocBudgetBridge
  (GrowOneVecU8Env growOneVecU8BudgetSpec rawVecGrowBudgetSpec rawVecNewCap)
open LibsignalBinary.Heap.SpecBudget (DecodeErrorFromEnv decodeErrorFromBudgetSpec)
open LibsignalBinary.Proofs.Placed.BudgetPoolSync (hooksException sepWP_seg_ls_vm)
open LibsignalBinary.Proofs.SpqrV1.Prost.MessageMerge.ChunkedDefsBudget
  (decodeErrorPushMergeBudgetSpec mergeBytes_len_bound)
open LibsignalBinary.Proofs.SpqrV1.Prost.MessageMerge.PolyCommonBudget
  (BytesMerge3Env FitsEnv.polyMergeLoop_bytesHead FitsEnv.polyMergeLoop_bytesTail
   FitsEnv.polyMergeLoop_head FitsEnv.polyMergeLoop_mono FitsEnv.polyMergeLoop_tail
   PolyMergeIterEnv PolyMergeLoopEnv WppBudgetPanic bytesMerge3RawBudgetSpec
   polyEncoderCapBound polyEncoderErrFrame polyEncoderLoopPre polyEncoderMergeSpec
   wppBudgetPanic_false)
open LibsignalBinary.Proofs.SpqrV1.Prost.MessageMerge.PolyDecoderBudgetAux
  (sepWPp_focus_pure sepWPp_fold)
open LibsignalBinary.Proofs.SpqrV1.Prost.MessageMerge.PolyEncoderBudgetAux
  (polyEncoder_push_err_exit_cl_placed)

private theorem sp_setMem_pre (s : State) (m : Memory) : (s.setMem m).sp = s.sp := by cases s; rfl
private theorem pc_setMem_pre (s : State) (m : Memory) : (s.setMem m).pc = s.pc := by cases s; rfl
private theorem status_setMem_pre (s : State) (m : Memory) : (s.setMem m).status = s.status := by cases s; rfl
private theorem pstate_setMem_pre (s : State) (m : Memory) : (s.setMem m).pstate = s.pstate := by cases s; rfl
private theorem trace_setMem_pre (s : State) (m : Memory) : (s.setMem m).trace = s.trace := by cases s; rfl
private theorem readReg64_setMem_pre (s : State) (m : Memory) (r : Reg) : (s.setMem m).readReg64 r = s.readReg64 r := by cases s; rfl
private theorem readReg32_setMem_pre (s : State) (m : Memory) (r : Reg) : (s.setMem m).readReg32 r = s.readReg32 r := by cases s; rfl
private theorem readReg_setMem_pre (s : State) (m : Memory) (w : Width) (r : Reg) : (s.setMem m).readReg w r = s.readReg w r := by cases s; rfl
private theorem calleeSavedVRegs_setMem_pre (s : State) (m : Memory) : calleeSavedVRegs (s.setMem m) = calleeSavedVRegs s := by cases s; rfl

private theorem protoPolynomialEncoderAt_unfold_pts (A : RustAlloc) (a : BitVec 64)
    (m : PolynomialEncoder) :
    protoPolynomialEncoderAt A a (polyEncoderToProto m) =
      (∃∗ cap : BitVec 64, ∃∗ ptr : BitVec 64,
        (a ↦₆₄ cap) ∗ ((a + 8#64) ↦₆₄ ptr) ∗ ((a + 16#64) ↦₆₄ BitVec.ofNat 64 m.pts.length) ∗
        ⌜m.pts.length ≤ cap.toNat ∧ cap.toNat * 24 < 2 ^ 63 ∧ ptr ≠ 0⌝ ∗
        (if cap = 0 then emp
         else A.live ptr (cap.toNat * 24) 8 ∗ arrayAt (fun bs addr => vecU8 A addr bs) 24 ptr m.pts ∗
           memRegion (ptr + BitVec.ofNat 64 (m.pts.length * 24)) ((cap.toNat - m.pts.length) * 24))) ∗
      vecVecU8At A (a + protoPolynomialEncoderPolysOff) m.polys ∗
      ((a + protoPolynomialEncoderIdxOff) ↦₃₂ m.idx) ∗
      memRegion (a + protoPolynomialEncoderPadOff) protoPolynomialEncoderPadSize := by
  unfold protoPolynomialEncoderAt polyEncoderToProto vecVecU8At vecHeaderBytes vecOf vecAt vecHeader vecBuf
  simp only [sepConj_assoc]

private theorem protoPolynomialEncoderAt_unfold_polys (A : RustAlloc) (a : BitVec 64)
    (m : PolynomialEncoder) :
    protoPolynomialEncoderAt A a (polyEncoderToProto m) =
      vecVecU8At A a m.pts ∗
      (∃∗ cap : BitVec 64, ∃∗ ptr : BitVec 64,
        ((a + 24#64) ↦₆₄ cap) ∗ ((a + 24#64 + 8#64) ↦₆₄ ptr) ∗
        ((a + 40#64) ↦₆₄ BitVec.ofNat 64 m.polys.length) ∗
        ⌜m.polys.length ≤ cap.toNat ∧ cap.toNat * 24 < 2 ^ 63 ∧ ptr ≠ 0⌝ ∗
        (if cap = 0 then emp
         else A.live ptr (cap.toNat * 24) 8 ∗ arrayAt (fun bs addr => vecU8 A addr bs) 24 ptr m.polys ∗
           memRegion (ptr + BitVec.ofNat 64 (m.polys.length * 24)) ((cap.toNat - m.polys.length) * 24))) ∗
      ((a + protoPolynomialEncoderIdxOff) ↦₃₂ m.idx) ∗
      memRegion (a + protoPolynomialEncoderPadOff) protoPolynomialEncoderPadSize := by
  unfold protoPolynomialEncoderAt polyEncoderToProto vecVecU8At vecHeaderBytes vecOf vecAt vecHeader vecBuf protoPolynomialEncoderPolysOff
  simp only [bv64_add24_add16, sepConj_assoc]

attribute [local irreducible] Program.fetch Program.externAt?
attribute [local arm64_norm]
  bv_sub_add_lit BitVec.toNat_zero growOneVecU8Name bv64_add_zero bv64_ofNat_add_one
  madd_24_eq madd_24_eq' extractLsb'_append64_0 extractLsb'_append64_64
attribute [local arm64_norm ↓, local wp_norm ↓]
  sp_setMem_pre pc_setMem_pre status_setMem_pre pstate_setMem_pre trace_setMem_pre
  readReg64_setMem_pre readReg32_setMem_pre readReg_setMem_pre calleeSavedVRegs_setMem_pre

/-! ## 1. Tag 2 (`pts : Vec<Vec<u8>>` at `msgPtr`) -/

set_option maxRecDepth 200000 in
set_option maxHeartbeats 400000 in
set_option linter.unusedSimpArgs false in
/-- Placed shared element-copy join block at `+0x188` (`(blkPl_297).base + 392#64`) for tag 2
(`pts : Vec<Vec<u8>>`). -/
theorem polyEncoder_tag2_copy_step_cro [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {H : LibsignalHooks}
    {x : PolyEncoderMergeGhost} {st0 st_next : M.σ} {R : SepProp}
    {s0 : State} {m : PolynomialEncoder} {s : State}
    {v rest' : List (BitVec 8)} {limit : Nat} {v_stk0 cap' ptr' cap_e ptr_e : BitVec 64}
    (_hsp_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hlt : m.pts.length < cap'.toNat) (hbound : cap'.toNat * 24 < 2 ^ 63) (hptr : ptr' ≠ 0)
    (hcont : ∀ (s' : State),
      s'.pc = (blkPl_297).base + 164#64 →
      s'.status = .Running → s'.sp = s0.sp - 160#64 → s'.trace = s0.trace →
      s'.readReg64 (Reg.gpr 19#5) = x.bufRef → s'.readReg64 (Reg.gpr 20#5) = x.msgPtr →
      s'.readReg64 (Reg.gpr 21#5) = x.slot → s'.readReg64 (Reg.gpr 22#5) = BitVec.ofNat 64 limit →
      s'.readReg64 (Reg.gpr 23#5) = 1#64 → s'.readReg64 (Reg.gpr 24#5) = 24#64 →
      PolyCalleeSaved s0 s' → LibsignalCodeRoLoaded lsmpl s'.mem →
      SepWPp ((blkPC_297).rebase (blkPl_297).base H) (s0.readReg64 Reg.lr) s'
        (polyEncoderLoopPre A lim st_next s0 s' x.msgPtr x.bufRef x.slot x.ptr
          { m with pts := m.pts ++ [v] } x.bs rest')
        (WppPost (polyEncoderMergeSpec A lim) (x, st0) R s0)
        (WppBudgetPanic (polyEncoderMergeSpec A lim) (x, st0) R s0))
    (hpc : s.pc = (blkPl_297).base + 392#64)
    (hrun : s.status = .Running) (hsp : s.sp = s0.sp - 160#64) (htr : s.trace = s0.trace)
    (hx19 : s.readReg64 (Reg.gpr 19#5) = x.bufRef) (hx20 : s.readReg64 (Reg.gpr 20#5) = x.msgPtr)
    (hx21 : s.readReg64 (Reg.gpr 21#5) = x.slot) (hx22 : s.readReg64 (Reg.gpr 22#5) = BitVec.ofNat 64 limit)
    (hx23 : s.readReg64 (Reg.gpr 23#5) = 1#64) (hx24 : s.readReg64 (Reg.gpr 24#5) = 24#64)
    (hx25 : s.readReg64 (Reg.gpr 25#5) = BitVec.ofNat 64 m.pts.length)
    (hcs : PolyCalleeSaved s0 s) (hinv : LibsignalCodeRoLoaded lsmpl s.mem) :
    SepWPp ((blkPC_297).rebase (blkPl_297).base H) (s0.readReg64 Reg.lr) s
      (((s0.sp - 160#64) ↦₆₄ v_stk0) ∗ vecU8At A.repAlloc (s0.sp - 152#64) cap_e ptr_e v ∗
        (x.msgPtr ↦₆₄ cap') ∗ ((x.msgPtr + 8#64) ↦₆₄ ptr') ∗
        ((x.msgPtr + 16#64) ↦₆₄ BitVec.ofNat 64 m.pts.length) ∗
        A.repAlloc.live ptr' (cap'.toNat * 24) 8 ∗
        arrayAt (fun bs addr => vecU8 A.repAlloc addr bs) 24 ptr' m.pts ∗
        memRegion (ptr' + BitVec.ofNat 64 (m.pts.length * 24)) ((cap'.toNat - m.pts.length) * 24) ∗
        vecVecU8At A.repAlloc (x.msgPtr + protoPolynomialEncoderPolysOff) m.polys ∗
        ((x.msgPtr + protoPolynomialEncoderIdxOff) ↦₃₂ m.idx) ∗
        memRegion (x.msgPtr + protoPolynomialEncoderPadOff) protoPolynomialEncoderPadSize ∗
        stackAt (s0.sp - 160#64) polyBelowStack ∗ memRegion (s0.sp - 128#64) 48 ∗
        polySavedRegsAny s0.sp s0 ∗ (x.bufRef ↦₆₄ x.slot) ∗
        sliceCursorAfter x.slot x.ptr x.bs rest' ∗ A.pool lim st_next s)
      (WppPost (polyEncoderMergeSpec A lim) (x, st0) R s0)
      (WppBudgetPanic (polyEncoderMergeSpec A lim) (x, st0) R s0) := by
  obtain ⟨hx26, hx27, hx28, hvregs⟩ := hcs
  apply SepWPp.of_sepWP_lscro (mid := (blkPl_297).base + 164#64) hinv
  conv => arg 4; rw [vecU8At_stack_to_cells A.repAlloc s0.sp cap_e ptr_e v,
    memRegion_split_24_cells ptr' m.pts.length cap'.toNat hlt hbound]
  conv => arg 4; simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
  apply SepWP.exists_elim; intro w2
  apply SepWP.exists_elim; intro w1
  apply SepWP.exists_elim; intro w0
  wp_steps_sync_pool ((blkPl_297).base + 164#64)
  simp only [State.setMem_setMem]
  apply SepWP.fold (cells160_entails_memRegion32 s0.sp v_stk0 cap_e ptr_e (BitVec.ofNat 64 v.length)) (by sep_focus)
  apply SepWP.fold (vecVecU8At_after_push A.repAlloc x.msgPtr cap' ptr' cap_e ptr_e m.pts v hlt hbound hptr) (by sep_focus)
  wp_reach; intro hinvm
  refine SepWPp.weaken_pre
    (Entails.of_eq (by dsimp only [polyEncoderLoopPre, protoPolynomialEncoderAt, polyEncoderToProto]; sep_ac_rfl))
    (hcont _
      (by simp only [arm64_norm]) (by simp only [arm64_norm, hrun]) (by simp only [arm64_norm, hsp])
      (by simp only [arm64_norm, htr])
      (by simp only [arm64_norm, hx19]) (by simp only [arm64_norm, hx20])
      (by simp only [arm64_norm, hx21]) (by simp only [arm64_norm, hx22])
      (by simp only [arm64_norm, hx23]) (by simp only [arm64_norm, hx24])
      ⟨by simp only [arm64_norm, hx26], by simp only [arm64_norm, hx27],
       by simp only [arm64_norm, hx28], by simp only [arm64_norm, hvregs]⟩ hinvm)

set_option maxRecDepth 200000 in
set_option maxHeartbeats 400000 in
set_option linter.unusedSimpArgs false in
/-- Code-RO-loaded placed step lemma for tag 2 (`pts : Vec<Vec<u8>>` at `msgPtr`) at `+0x150`
(`(blkPl_297).base + 336#64`). -/
theorem polyEncoder_tag2_step_cro [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {H : LibsignalHooks}
    (hFromCall : subroutine_ok ((blkPC_297).rebase (blkPl_297).base H) (lsmpl.base 261)
      (withLsCodeRoLoaded lsmpl (decodeErrorFromBudgetSpec M A lim)))
    (hPushCall : subroutine_ok ((blkPC_297).rebase (blkPl_297).base H) (lsmpl.base 257)
      (withLsCodeRoLoaded lsmpl (decodeErrorPushMergeBudgetSpec M A lim)))
    (hBytesCall : subroutine_ok ((blkPC_297).rebase (blkPl_297).base H) (lsmpl.base 290)
      (withLsCodeRoLoaded lsmpl (bytesMerge3RawBudgetSpec A lim)))
    (hGrowCall : subroutine_ok ((blkPC_297).rebase (blkPl_297).base H)
      (lsmpl.base 621)
      (withLsCodeRoLoaded lsmpl (growOneVecU8BudgetSpec M A lim)))
    {x : PolyEncoderMergeGhost} {st0 st_cur : M.σ} {R : SepProp}
    {s0 s : State} {m : PolynomialEncoder} {rest : List (BitVec 8)} {iwt : WireType} {limit : Nat}
    {f_acc f_rem : Nat} {evs_acc : List AllocEvent}
    (hsp_align : (s0.sp &&& 15#64 == 0#64) = true) (hrest_le : rest.length ≤ x.bs.length)
    (hpts_bound : m.pts.length + rest.length < 2 ^ 56) (hrest_suf : IsDropSuffix x.bs rest)
    (hcap_lt : m.pts.length < polyEncoderCapBound x)
    (hf_rem : 2 * rest.length + 2 ≤ f_rem)
    (hf_tot : f_acc + 2 ≤ 2 * x.bs.length + 2)
    (hevs_acc : PolyMergeLoopEnv f_acc x.bs.length (polyEncoderCapBound x) evs_acc)
    (hst_cur : st_cur = M.stepEvents evs_acc st0)
    (hfits_rem : FitsEnv M lim st_cur
      (PolyMergeLoopEnv f_rem x.bs.length (polyEncoderCapBound x)))
    (hnone_of_mb : mergeBytes iwt rest = none →
      (mergeMessage PolynomialEncoder.mergeField (codecWireTypeToProto x.wt) x.msg x.bs 98).toOption = none)
    (hcont : ∀ (v : List (BitVec 8)) (rest' : List (BitVec 8)) (st_next : M.σ)
        (evs_step : List AllocEvent) (s' : State),
      mergeBytes iwt rest = some (v, rest') →
      PolyMergeLoopEnv (2 * v.length + 2) x.bs.length (polyEncoderCapBound x) evs_step →
      st_next = M.stepEvents evs_step st_cur →
      s'.pc = (blkPl_297).base + 164#64 →
      s'.status = .Running → s'.sp = s0.sp - 160#64 → s'.trace = s0.trace →
      s'.readReg64 (Reg.gpr 19#5) = x.bufRef → s'.readReg64 (Reg.gpr 20#5) = x.msgPtr →
      s'.readReg64 (Reg.gpr 21#5) = x.slot → s'.readReg64 (Reg.gpr 22#5) = BitVec.ofNat 64 limit →
      s'.readReg64 (Reg.gpr 23#5) = 1#64 → s'.readReg64 (Reg.gpr 24#5) = 24#64 →
      PolyCalleeSaved s0 s' → LibsignalCodeRoLoaded lsmpl s'.mem →
      SepWPp ((blkPC_297).rebase (blkPl_297).base H) (s0.readReg64 Reg.lr) s'
        (polyEncoderLoopPre A lim st_next s0 s' x.msgPtr x.bufRef x.slot x.ptr
          { m with pts := m.pts ++ [v] } x.bs rest')
        (WppPost (polyEncoderMergeSpec A lim) (x, st0) R s0)
        (WppBudgetPanic (polyEncoderMergeSpec A lim) (x, st0) R s0))
    (hpc : s.pc = (blkPl_297).base + 336#64)
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
    FitsEnv.polyMergeLoop_mono (by omega) (Nat.le_refl _) (Nat.le_refl _) hfits_rem
  by_cases hiwt : iwt = .lengthDelimited
  · subst hiwt; dsimp [WireType.toNat] at hx0
    have hfits_mb : FitsEnv M lim st_cur
        (BytesMerge3Env ⟨.lengthDelimited, s0.sp - 152#64, 0#64, 1#64, [], x.bufRef, x.slot, restPtr, rest⟩) :=
      FitsEnv.polyMergeLoop_bytesHead (bs := rest) hrest_le (Nat.max_le.mpr ⟨by omega, by omega⟩) hfits_rem
    apply SepWPp.of_sepWP_lscro (mid := lsmpl.base 290) hinv
    conv => arg 4; rw [polyEncoderLoopPre, sliceCursorAfter_eq_split hrest_le hrest_suf,
      memRegion_32_cells160 s0.sp, polyBelow_bytesMerge3 s0.sp]
    conv => arg 4; simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
    apply SepWP.exists_elim; intro v_stk3; apply SepWP.exists_elim; intro v_stk2
    apply SepWP.exists_elim; intro v_stk1; apply SepWP.exists_elim; intro v_stk0
    wp_steps_sync_pool (lsmpl.base 290)
    simp only [State.setMem_setMem]
    apply SepWP.fold (Entails.of_eq (vecU8At_zero_eq_cells A.repAlloc s0.sp).symm) (by sep_focus)
    wp_reach; intro hinv
    refine SepWPp.call_frame_lscro (spec := bytesMerge3RawBudgetSpec A lim)
      (x := (⟨.lengthDelimited, s0.sp - 152#64, 0#64, 1#64, [], x.bufRef, x.slot, restPtr, rest⟩, st_cur))
      (ret_pc := (blkPl_297).base + 364#64) hBytesCall hinv
      (by simp only [arm64_norm]) (by simp only [arm64_norm, hrun])
      (by simp only [State.spAligned, hsp, arm64_norm]; exact hsp_align) (by simp only [arm64_norm])
      rfl
      ⟨by simp only [arm64_norm, hsp, hx0], by simp only [arm64_norm, hsp],
       by simp only [arm64_norm, hsp, hx19], show rest.length < 2 ^ 63 by omega, Or.inl rfl, hfits_mb⟩
      (by sep_focus)
      (fun _ _ _ _ hex => False.elim (not_satisfies_false_sepConj hex))
      (fun _ _ => wppBudgetPanic_false) ?_
    intro sm hpcm hrunm hspm hcsm hinvm; simp only [CalleeSavedPreserved] at hcsm
    obtain ⟨hx19_m, hx20_m, hx21_m, hx22_m, hx23_m, hx24_m, _, hx26_m, hx27_m, hx28_m, _, hvregs_m⟩ := hcsm
    simp (config := { decide := true }) only [arm64_norm, hsp, hx19, hx20, hx21, hx22, hx23, hx24, hx26, hx27, hx28, hvregs]
      at hpcm hrunm hspm hx19_m hx20_m hx21_m hx22_m hx23_m hx24_m hx26_m hx27_m hx28_m hvregs_m
    cases hmb : mergeBytes .lengthDelimited rest with
    | none =>
      have hnone := hnone_of_mb hmb
      apply SepWPp.of_sepWP_lscro (mid := (blkPl_297).base + 836#64) hinvm
      conv => arg 4; dsimp only [bytesMerge3RawBudgetSpec]
      conv => arg 4; simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
      apply SepWP.exists_elim; intro evs_mb
      conv => arg 4; simp only [hmb, vecU8At_zero_eq_cells A.repAlloc s0.sp,
        memRegion_48_cells1_160 s0.sp, sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
      apply SepWP.exists_elim; intro v_err0
      wp_focus_pure; intro htrm; wp_focus_pure; intro hevs_mb; wp_focus_pure; intro hsm0
      conv => arg 4; simp only [sepConj_assoc, arm64_norm, hsp]
      have hcbnz_err : (sm.readReg64 (Reg.gpr 0#5) == 0#64) = false := beq_eq_false_iff_ne.mpr hsm0
      apply SepWP.fold (polyBelow_bytesMerge3_entails s0.sp) (by sep_focus)
      apply SepWP.fold (pointsToBytes_prefix_join hrest_le hrest_suf) (by sep_focus)
      wp_steps_sync_pool ((blkPl_297).base + 836#64)
      simp only [State.setMem_setMem]
      apply SepWP.fold (cells160_entails_memRegion32 s0.sp v_stk0 0#64 1#64 0#64) (by sep_focus)
      wp_reach; intro hinvm'
      have hiter_mb : PolyMergeIterEnv x.bs.length (polyEncoderCapBound x) evs_mb :=
        PolyMergeIterEnv.of_bytesMerge3Err hmb hevs_mb
      have hfits_st1 : FitsEnv M lim (M.stepEvents evs_mb st_cur)
          (PolyMergeLoopEnv 1 x.bs.length (polyEncoderCapBound x)) :=
        FitsEnv.polyMergeLoop_tail hiter_mb hfits2
      have hevs_acc1 : PolyMergeLoopEnv (f_acc + 1) x.bs.length (polyEncoderCapBound x)
          (evs_acc ++ evs_mb) :=
        hevs_acc.append (PolyMergeLoopEnv.single (fuel := 0) hiter_mb)
      have hst1 : M.stepEvents evs_mb st_cur = M.stepEvents (evs_acc ++ evs_mb) st0 := by
        rw [hst_cur, ← AllocCostModel.stepEvents_append]
      refine SepWPp.weaken_pre (Entails.of_eq (by dsimp only [polyEncoderErrFrame]; sep_ac_rfl))
        (polyEncoder_push_err_exit_cl_placed hPushCall hnone hsm0 (Nat.le_refl 1) hf_tot
          hevs_acc1 hst1 hfits_st1 hsp_align
          (by simp only [arm64_norm]) (by simp only [arm64_norm, hrunm]) (by simp only [arm64_norm, hspm])
          (by simp only [arm64_norm, htrm, htr]) (by simp only [arm64_norm, hspm])
          ⟨by simp only [arm64_norm, hx26_m], by simp only [arm64_norm, hx27_m],
           by simp only [arm64_norm, hx28_m], by simp only [arm64_norm, hvregs_m]⟩ hinvm')
    | some p =>
      rcases p with ⟨v, rest'⟩
      have hrest'_le : rest'.length ≤ rest.length := mergeBytes_length hmb
      have hmb_len := mergeBytes_len_bound hmb
      conv => arg 4; dsimp only [bytesMerge3RawBudgetSpec]
      conv => arg 4; simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
      apply SepWPp.exists_elim; intro evs_mb
      conv => arg 4; simp only [hmb, sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
      apply SepWPp.exists_elim; intro cap_e; apply SepWPp.exists_elim; intro ptr_e
      conv => arg 4; rw [protoPolynomialEncoderAt_unfold_pts]
      conv => arg 4; simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
      apply SepWPp.exists_elim; intro cap; apply SepWPp.exists_elim; intro ptr
      apply sepWPp_focus_pure (by sep_focus); intro htrm; apply sepWPp_focus_pure (by sep_focus); intro hevs_mb
      apply sepWPp_focus_pure (by sep_focus); intro hsm0; apply sepWPp_focus_pure (by sep_focus); intro _hcap_ok
      apply sepWPp_focus_pure (by sep_focus); rintro ⟨hlen_le, hcap_bound, hptr_ne⟩
      conv => arg 4; simp only [sepConj_assoc, arm64_norm, hsp]
      have hfits_mb_tail : FitsEnv M lim (M.stepEvents evs_mb st_cur)
          (PolyMergeLoopEnv 1 x.bs.length (polyEncoderCapBound x)) :=
        FitsEnv.polyMergeLoop_bytesTail (bs := rest) hmb hrest_le hevs_mb
          (FitsEnv.polyMergeLoop_mono (by omega) (Nat.le_refl _) (Nat.le_refl _) hfits_rem)
      by_cases hcap_eq : m.pts.length = cap.toNat
      · have hbne : (BitVec.ofNat 64 m.pts.length != cap) = false := len_eq_cap_bne_false hcap_eq
        have hgrow_bound : max (2 * cap.toNat) 4 * 24 + 8 ≤ 2 ^ 63 := by omega
        apply SepWPp.of_sepWP_lscro (mid := lsmpl.base 621) hinvm
        apply SepWP.fold (polyBelow_bytesMerge3_entails s0.sp) (by sep_focus)
        apply SepWP.fold (sliceCursorAfter_join hrest_le hrest_suf hrest'_le) (by sep_focus)
        apply SepWP.fold (vecBuf_vecU8_entails_grow_pre A.repAlloc cap ptr m.pts hcap_eq) (by sep_focus)
        conv => arg 4; rw [polyBelow_extHook s0.sp]
        conv => arg 4; simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
        apply SepWP.exists_elim; intro pins
        wp_focus_pure; rintro ⟨hpins_len, hbytes_len⟩
        wp_steps_sync_pool (lsmpl.base 621)
        simp only [State.setMem_setMem]
        wp_reach; intro hinvm'
        have hfits_grow : FitsEnv M lim (M.stepEvents evs_mb st_cur)
            (GrowOneVecU8Env ⟨x.msgPtr, cap, ptr, vecU8ArrayBytes pins m.pts⟩) :=
          FitsEnv.polyMergeLoop_head (fuel := 0)
            (fun _ hg => PolyMergeIterEnv.of_growOneVecU8 (by dsimp; omega) hg) hfits_mb_tail
        refine SepWPp.call_frame_lscro (spec := growOneVecU8BudgetSpec M A lim)
          (x := (⟨x.msgPtr, cap, ptr, vecU8ArrayBytes pins m.pts⟩, M.stepEvents evs_mb st_cur))
          (ret_pc := (blkPl_297).base + 392#64) hGrowCall hinvm'
          (by simp only [arm64_norm]) (by simp only [arm64_norm, hrunm])
          (by simp only [State.spAligned, hspm, arm64_norm]; exact hsp_align) (by simp only [arm64_norm])
          rfl
          ⟨by simp only [arm64_norm, hspm, hx20_m], hbytes_len, hptr_ne,
           by dsimp only [rawVecNewCap]; exact hgrow_bound, hfits_grow⟩
          (by dsimp only [RustCliAllocBudget.live]; sep_focus)
          (fun _ _ _ _ hex => False.elim (not_satisfies_false_sepConj hex))
          (fun _ _ => wppBudgetPanic_false) ?_
        intro sm2 hpcm2 hrunm2 hspm2 hcsm2 hinvm2; simp only [CalleeSavedPreserved] at hcsm2
        obtain ⟨hx19_2, hx20_2, hx21_2, hx22_2, hx23_2, hx24_2, hx25_2, hx26_2, hx27_2, hx28_2, _, hvregs_2⟩ := hcsm2
        simp (config := { decide := true }) only [arm64_norm, hspm, hx19_m, hx20_m, hx21_m, hx22_m, hx23_m, hx24_m, hx26_m, hx27_m, hx28_m, hvregs_m]
          at hpcm2 hrunm2 hspm2 hx19_2 hx20_2 hx21_2 hx22_2 hx23_2 hx24_2 hx25_2 hx26_2 hx27_2 hx28_2 hvregs_2
        conv => arg 4; dsimp only [growOneVecU8BudgetSpec, rawVecGrowBudgetSpec]
        conv => arg 4; simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
        apply SepWPp.exists_elim; intro evs_g
        apply SepWPp.exists_elim; intro p'
        apply sepWPp_focus_pure (by sep_focus); rintro ⟨htrm2, hevs_g⟩
        apply sepWPp_focus_pure (by sep_focus); rintro ⟨hp'_ne, _⟩
        conv => arg 4; simp only [sepConj_assoc, arm64_norm, hspm]
        have hnew_toNat : (newCapVecU8 cap).toNat = max (2 * cap.toNat) 4 := by
          unfold newCapVecU8; rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
        have hlt_new : m.pts.length < (newCapVecU8 cap).toNat := by rw [hnew_toNat]; omega
        have hbound_new : (newCapVecU8 cap).toNat * 24 < 2 ^ 63 := by rw [hnew_toNat]; omega
        have hevs_step : PolyMergeLoopEnv (2 * v.length + 2) x.bs.length (polyEncoderCapBound x)
            (evs_mb ++ evs_g) := by
          have h1 : PolyMergeLoopEnv (2 * v.length + 1) x.bs.length (polyEncoderCapBound x) evs_mb := by
            simpa using
              (PolyMergeLoopEnv.bytesSingle (fuel := 0)
                (maxLen := x.bs.length) (polyCapBound := polyEncoderCapBound x)
                hmb hrest_le hevs_mb)
          have h2 : PolyMergeLoopEnv 1 x.bs.length (polyEncoderCapBound x) evs_g :=
            PolyMergeLoopEnv.single (fuel := 0)
              (PolyMergeIterEnv.of_growOneVecU8 (by dsimp; omega) hevs_g)
          exact h1.append h2
        have hst_next : M.stepEvents evs_g (M.stepEvents evs_mb st_cur) =
            M.stepEvents (evs_mb ++ evs_g) st_cur :=
          (AllocCostModel.stepEvents_append M evs_mb evs_g st_cur).symm
        conv => arg 4; dsimp only [rawVecNewCap]
        conv => arg 4; rw [show A.live p' (max (2 * cap.toNat) 4 * 24) 8 =
          A.repAlloc.live p' (max (2 * cap.toNat) 4 * 24) 8 from rfl,
          show BitVec.ofNat 64 (max (2 * cap.toNat) 4) = newCapVecU8 cap from rfl, hst_next]
        apply sepWPp_fold
          (grow_post_entails_ready A.repAlloc cap p' pins m.pts hcap_eq hpins_len hgrow_bound)
          (by sep_focus)
        apply sepWPp_fold (polyBelow_extHook_entails s0.sp) (by sep_focus)
        refine SepWPp.weaken_pre ?_
          (polyEncoder_tag2_copy_step_cro (st_next := M.stepEvents (evs_mb ++ evs_g) st_cur)
            (v_stk0 := v_stk0) (cap' := newCapVecU8 cap) (ptr' := p')
            (cap_e := cap_e) (ptr_e := ptr_e) hsp_align hlt_new hbound_new hp'_ne
            (fun s' => hcont v rest' _ (evs_mb ++ evs_g) s' hmb hevs_step rfl)
            hpcm2 hrunm2 hspm2 (htrm2.trans (htrm.trans htr))
            hx19_2 hx20_2 hx21_2 hx22_2 hx23_2 hx24_2
            (hx25_2.trans (by rw [hcap_eq, BitVec.ofNat_toNat, BitVec.setWidth_eq]))
            ⟨hx26_2, hx27_2, hx28_2, hvregs_2⟩ hinvm2)
        exact Entails.of_eq (by sep_ac_rfl)
      · have hlt : m.pts.length < cap.toNat := Nat.lt_of_le_of_ne hlen_le hcap_eq
        have hbne : (BitVec.ofNat 64 m.pts.length != cap) = true := len_lt_cap_bne_true hlt
        have hcap_ne0 : cap ≠ 0 := by intro h0; subst h0; change m.pts.length < 0 at hlt; omega
        have hevs_step : PolyMergeLoopEnv (2 * v.length + 2) x.bs.length (polyEncoderCapBound x)
            evs_mb :=
          (PolyMergeLoopEnv.bytesSingle (fuel := 0)
            (maxLen := x.bs.length) (polyCapBound := polyEncoderCapBound x)
            hmb hrest_le hevs_mb).mono_fuel (by omega)
        apply SepWPp.of_sepWP_lscro (mid := (blkPl_297).base + 392#64) hinvm
        (conv => arg 4; simp only [hcap_ne0, ↓reduceIte, sepConj_assoc])
        apply SepWP.fold (polyBelow_bytesMerge3_entails s0.sp) (by sep_focus)
        apply SepWP.fold (sliceCursorAfter_join hrest_le hrest_suf hrest'_le) (by sep_focus)
        wp_steps_sync_pool ((blkPl_297).base + 392#64)
        simp only [State.setMem_setMem]
        wp_reach; intro hinvm'
        refine SepWPp.weaken_pre ?_
          (polyEncoder_tag2_copy_step_cro (st_next := M.stepEvents evs_mb st_cur)
            (v_stk0 := v_stk0) (cap' := cap) (ptr' := ptr) (cap_e := cap_e) (ptr_e := ptr_e)
            hsp_align hlt hcap_bound hptr_ne
            (fun s' => hcont v rest' _ evs_mb s' hmb hevs_step rfl)
            (by simp only [arm64_norm]) (by simp only [arm64_norm, hrunm]) (by simp only [arm64_norm, hspm])
            (by simp only [arm64_norm, htrm, htr])
            (by simp only [arm64_norm, hx19_m]) (by simp only [arm64_norm, hx20_m])
            (by simp only [arm64_norm, hx21_m]) (by simp only [arm64_norm, hx22_m])
            (by simp only [arm64_norm, hx23_m]) (by simp only [arm64_norm, hx24_m])
            (by simp only [arm64_norm])
            ⟨by simp only [arm64_norm, hx26_m], by simp only [arm64_norm, hx27_m],
             by simp only [arm64_norm, hx28_m], by simp only [arm64_norm, hvregs_m]⟩ hinvm')
        exact Entails.of_eq (by sep_ac_rfl)
  · have hnone := hnone_of_mb (mergeBytes_eq_none_of_ne_len hiwt)
    obtain ⟨hbne2_64, hbne2_32⟩ := iwt_bne_two_true_of_ne_len hiwt
    have hfits_from : FitsEnv M lim st_cur DecodeErrorFromEnv :=
      FitsEnv.polyMergeLoop_head (fuel := 1) (fun _ => PolyMergeIterEnv.of_decodeErrorFrom) hfits2
    apply SepWPp.of_sepWP_lscro (mid := lsmpl.base 261) hinv
    conv => arg 4; rw [polyEncoderLoopPre, sliceCursorAfter_eq_split hrest_le hrest_suf,
      sliceCursorAt, memRegion_48_wtErr160 s0.sp, polyBelow_decodeErrorHook s0.sp]
    conv => arg 4; simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
    apply SepWP.exists_elim; intro b_wt1; apply SepWP.exists_elim; intro b_wt0; apply SepWP.exists_elim; intro v_wt0
    wp_steps_sync_pool (lsmpl.base 261)
    simp only [State.setMem_setMem]
    apply SepWP.fold (wtErr160_entails_memRegion40 s0.sp _ _) (by sep_focus)
    apply SepWP.fold (pointsTo64_pair_entails_memRegion16 x.slot restPtr (BitVec.ofNat 64 rest.length)) (by sep_focus)
    apply SepWP.fold (pointsToBytes_prefix_join hrest_le hrest_suf) (by sep_focus)
    wp_reach; intro hinv
    refine SepWPp.call_frame_lscro (spec := decodeErrorFromBudgetSpec M A lim)
      (x := (s0.sp - 128#64, 0x8000000000000006#64, st_cur))
      (ret_pc := (blkPl_297).base + 664#64) hFromCall hinv
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

/-! ## 2. Tag 3 (`polys : Vec<Vec<u8>>` at `msgPtr + 24#64`) -/

set_option maxRecDepth 200000 in
set_option maxHeartbeats 400000 in
set_option linter.unusedSimpArgs false in
/-- Placed shared element-copy join block at `+0x128` (`(blkPl_297).base + 296#64`) for tag 3
(`polys : Vec<Vec<u8>>`). -/
theorem polyEncoder_tag3_copy_step_cro [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {H : LibsignalHooks}
    {x : PolyEncoderMergeGhost} {st0 st_next : M.σ} {R : SepProp}
    {s0 : State} {m : PolynomialEncoder} {s : State}
    {v rest' : List (BitVec 8)} {limit : Nat} {v_stk0 cap' ptr' cap_e ptr_e : BitVec 64}
    (_hsp_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hlt : m.polys.length < cap'.toNat) (hbound : cap'.toNat * 24 < 2 ^ 63) (hptr : ptr' ≠ 0)
    (hcont : ∀ (s' : State),
      s'.pc = (blkPl_297).base + 164#64 →
      s'.status = .Running → s'.sp = s0.sp - 160#64 → s'.trace = s0.trace →
      s'.readReg64 (Reg.gpr 19#5) = x.bufRef → s'.readReg64 (Reg.gpr 20#5) = x.msgPtr →
      s'.readReg64 (Reg.gpr 21#5) = x.slot → s'.readReg64 (Reg.gpr 22#5) = BitVec.ofNat 64 limit →
      s'.readReg64 (Reg.gpr 23#5) = 1#64 → s'.readReg64 (Reg.gpr 24#5) = 24#64 →
      PolyCalleeSaved s0 s' → LibsignalCodeRoLoaded lsmpl s'.mem →
      SepWPp ((blkPC_297).rebase (blkPl_297).base H) (s0.readReg64 Reg.lr) s'
        (polyEncoderLoopPre A lim st_next s0 s' x.msgPtr x.bufRef x.slot x.ptr
          { m with polys := m.polys ++ [v] } x.bs rest')
        (WppPost (polyEncoderMergeSpec A lim) (x, st0) R s0)
        (WppBudgetPanic (polyEncoderMergeSpec A lim) (x, st0) R s0))
    (hpc : s.pc = (blkPl_297).base + 296#64)
    (hrun : s.status = .Running) (hsp : s.sp = s0.sp - 160#64) (htr : s.trace = s0.trace)
    (hx19 : s.readReg64 (Reg.gpr 19#5) = x.bufRef) (hx20 : s.readReg64 (Reg.gpr 20#5) = x.msgPtr)
    (hx21 : s.readReg64 (Reg.gpr 21#5) = x.slot) (hx22 : s.readReg64 (Reg.gpr 22#5) = BitVec.ofNat 64 limit)
    (hx23 : s.readReg64 (Reg.gpr 23#5) = 1#64) (hx24 : s.readReg64 (Reg.gpr 24#5) = 24#64)
    (hx25 : s.readReg64 (Reg.gpr 25#5) = BitVec.ofNat 64 m.polys.length)
    (hcs : PolyCalleeSaved s0 s) (hinv : LibsignalCodeRoLoaded lsmpl s.mem) :
    SepWPp ((blkPC_297).rebase (blkPl_297).base H) (s0.readReg64 Reg.lr) s
      (((s0.sp - 160#64) ↦₆₄ v_stk0) ∗ vecU8At A.repAlloc (s0.sp - 152#64) cap_e ptr_e v ∗
        vecVecU8At A.repAlloc x.msgPtr m.pts ∗
        ((x.msgPtr + 24#64) ↦₆₄ cap') ∗ ((x.msgPtr + 32#64) ↦₆₄ ptr') ∗
        ((x.msgPtr + 40#64) ↦₆₄ BitVec.ofNat 64 m.polys.length) ∗
        A.repAlloc.live ptr' (cap'.toNat * 24) 8 ∗
        arrayAt (fun bs addr => vecU8 A.repAlloc addr bs) 24 ptr' m.polys ∗
        memRegion (ptr' + BitVec.ofNat 64 (m.polys.length * 24)) ((cap'.toNat - m.polys.length) * 24) ∗
        ((x.msgPtr + protoPolynomialEncoderIdxOff) ↦₃₂ m.idx) ∗
        memRegion (x.msgPtr + protoPolynomialEncoderPadOff) protoPolynomialEncoderPadSize ∗
        stackAt (s0.sp - 160#64) polyBelowStack ∗ memRegion (s0.sp - 128#64) 48 ∗
        polySavedRegsAny s0.sp s0 ∗ (x.bufRef ↦₆₄ x.slot) ∗
        sliceCursorAfter x.slot x.ptr x.bs rest' ∗ A.pool lim st_next s)
      (WppPost (polyEncoderMergeSpec A lim) (x, st0) R s0)
      (WppBudgetPanic (polyEncoderMergeSpec A lim) (x, st0) R s0) := by
  obtain ⟨hx26, hx27, hx28, hvregs⟩ := hcs
  apply SepWPp.of_sepWP_lscro (mid := (blkPl_297).base + 164#64) hinv
  conv => arg 4; rw [vecU8At_stack_to_cells A.repAlloc s0.sp cap_e ptr_e v,
    memRegion_split_24_cells ptr' m.polys.length cap'.toNat hlt hbound]
  conv => arg 4; simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
  apply SepWP.exists_elim; intro w2
  apply SepWP.exists_elim; intro w1
  apply SepWP.exists_elim; intro w0
  wp_steps_sync_pool ((blkPl_297).base + 164#64)
  simp only [State.setMem_setMem]
  apply SepWP.fold (cells160_entails_memRegion32 s0.sp v_stk0 cap_e ptr_e (BitVec.ofNat 64 v.length)) (by sep_focus)
  apply SepWP.fold (vecVecU8At_after_push_24 A.repAlloc x.msgPtr cap' ptr' cap_e ptr_e m.polys v hlt hbound hptr) (by sep_focus)
  wp_reach; intro hinvm
  refine SepWPp.weaken_pre
    (Entails.of_eq (by dsimp only [polyEncoderLoopPre, protoPolynomialEncoderAt, polyEncoderToProto]; sep_ac_rfl))
    (hcont _
      (by simp only [arm64_norm]) (by simp only [arm64_norm, hrun]) (by simp only [arm64_norm, hsp])
      (by simp only [arm64_norm, htr])
      (by simp only [arm64_norm, hx19]) (by simp only [arm64_norm, hx20])
      (by simp only [arm64_norm, hx21]) (by simp only [arm64_norm, hx22])
      (by simp only [arm64_norm, hx23]) (by simp only [arm64_norm, hx24])
      ⟨by simp only [arm64_norm, hx26], by simp only [arm64_norm, hx27],
       by simp only [arm64_norm, hx28], by simp only [arm64_norm, hvregs]⟩ hinvm)

set_option maxRecDepth 200000 in
set_option maxHeartbeats 400000 in
set_option linter.unusedSimpArgs false in
/-- Code-RO-loaded placed step lemma for tag 3 (`polys : Vec<Vec<u8>>` at `msgPtr + 24#64`) at `+0x0f0`
(`(blkPl_297).base + 240#64`). -/
theorem polyEncoder_tag3_step_cro [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {H : LibsignalHooks}
    (hFromCall : subroutine_ok ((blkPC_297).rebase (blkPl_297).base H) (lsmpl.base 261)
      (withLsCodeRoLoaded lsmpl (decodeErrorFromBudgetSpec M A lim)))
    (hPushCall : subroutine_ok ((blkPC_297).rebase (blkPl_297).base H) (lsmpl.base 257)
      (withLsCodeRoLoaded lsmpl (decodeErrorPushMergeBudgetSpec M A lim)))
    (hBytesCall : subroutine_ok ((blkPC_297).rebase (blkPl_297).base H) (lsmpl.base 290)
      (withLsCodeRoLoaded lsmpl (bytesMerge3RawBudgetSpec A lim)))
    (hGrowCall : subroutine_ok ((blkPC_297).rebase (blkPl_297).base H)
      (lsmpl.base 621)
      (withLsCodeRoLoaded lsmpl (growOneVecU8BudgetSpec M A lim)))
    {x : PolyEncoderMergeGhost} {st0 st_cur : M.σ} {R : SepProp}
    {s0 s : State} {m : PolynomialEncoder} {rest : List (BitVec 8)} {iwt : WireType} {limit : Nat}
    {f_acc f_rem : Nat} {evs_acc : List AllocEvent}
    (hsp_align : (s0.sp &&& 15#64 == 0#64) = true) (hrest_le : rest.length ≤ x.bs.length)
    (hpolys_bound : m.polys.length + rest.length < 2 ^ 56) (hrest_suf : IsDropSuffix x.bs rest)
    (hcap_lt : m.polys.length < polyEncoderCapBound x)
    (hf_rem : 2 * rest.length + 2 ≤ f_rem)
    (hf_tot : f_acc + 2 ≤ 2 * x.bs.length + 2)
    (hevs_acc : PolyMergeLoopEnv f_acc x.bs.length (polyEncoderCapBound x) evs_acc)
    (hst_cur : st_cur = M.stepEvents evs_acc st0)
    (hfits_rem : FitsEnv M lim st_cur
      (PolyMergeLoopEnv f_rem x.bs.length (polyEncoderCapBound x)))
    (hnone_of_mb : mergeBytes iwt rest = none →
      (mergeMessage PolynomialEncoder.mergeField (codecWireTypeToProto x.wt) x.msg x.bs 98).toOption = none)
    (hcont : ∀ (v : List (BitVec 8)) (rest' : List (BitVec 8)) (st_next : M.σ)
        (evs_step : List AllocEvent) (s' : State),
      mergeBytes iwt rest = some (v, rest') →
      PolyMergeLoopEnv (2 * v.length + 2) x.bs.length (polyEncoderCapBound x) evs_step →
      st_next = M.stepEvents evs_step st_cur →
      s'.pc = (blkPl_297).base + 164#64 →
      s'.status = .Running → s'.sp = s0.sp - 160#64 → s'.trace = s0.trace →
      s'.readReg64 (Reg.gpr 19#5) = x.bufRef → s'.readReg64 (Reg.gpr 20#5) = x.msgPtr →
      s'.readReg64 (Reg.gpr 21#5) = x.slot → s'.readReg64 (Reg.gpr 22#5) = BitVec.ofNat 64 limit →
      s'.readReg64 (Reg.gpr 23#5) = 1#64 → s'.readReg64 (Reg.gpr 24#5) = 24#64 →
      PolyCalleeSaved s0 s' → LibsignalCodeRoLoaded lsmpl s'.mem →
      SepWPp ((blkPC_297).rebase (blkPl_297).base H) (s0.readReg64 Reg.lr) s'
        (polyEncoderLoopPre A lim st_next s0 s' x.msgPtr x.bufRef x.slot x.ptr
          { m with polys := m.polys ++ [v] } x.bs rest')
        (WppPost (polyEncoderMergeSpec A lim) (x, st0) R s0)
        (WppBudgetPanic (polyEncoderMergeSpec A lim) (x, st0) R s0))
    (hpc : s.pc = (blkPl_297).base + 240#64)
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
    FitsEnv.polyMergeLoop_mono (by omega) (Nat.le_refl _) (Nat.le_refl _) hfits_rem
  by_cases hiwt : iwt = .lengthDelimited
  · subst hiwt; dsimp [WireType.toNat] at hx0
    have hfits_mb : FitsEnv M lim st_cur
        (BytesMerge3Env ⟨.lengthDelimited, s0.sp - 152#64, 0#64, 1#64, [], x.bufRef, x.slot, restPtr, rest⟩) :=
      FitsEnv.polyMergeLoop_bytesHead (bs := rest) hrest_le (Nat.max_le.mpr ⟨by omega, by omega⟩) hfits_rem
    apply SepWPp.of_sepWP_lscro (mid := lsmpl.base 290) hinv
    conv => arg 4; rw [polyEncoderLoopPre, sliceCursorAfter_eq_split hrest_le hrest_suf,
      memRegion_32_cells160 s0.sp, polyBelow_bytesMerge3 s0.sp]
    conv => arg 4; simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
    apply SepWP.exists_elim; intro v_stk3; apply SepWP.exists_elim; intro v_stk2
    apply SepWP.exists_elim; intro v_stk1; apply SepWP.exists_elim; intro v_stk0
    wp_steps_sync_pool (lsmpl.base 290)
    simp only [State.setMem_setMem]
    apply SepWP.fold (Entails.of_eq (vecU8At_zero_eq_cells A.repAlloc s0.sp).symm) (by sep_focus)
    wp_reach; intro hinv
    refine SepWPp.call_frame_lscro (spec := bytesMerge3RawBudgetSpec A lim)
      (x := (⟨.lengthDelimited, s0.sp - 152#64, 0#64, 1#64, [], x.bufRef, x.slot, restPtr, rest⟩, st_cur))
      (ret_pc := (blkPl_297).base + 268#64) hBytesCall hinv
      (by simp only [arm64_norm]) (by simp only [arm64_norm, hrun])
      (by simp only [State.spAligned, hsp, arm64_norm]; exact hsp_align) (by simp only [arm64_norm])
      rfl
      ⟨by simp only [arm64_norm, hsp, hx0], by simp only [arm64_norm, hsp],
       by simp only [arm64_norm, hsp, hx19], show rest.length < 2 ^ 63 by omega, Or.inl rfl, hfits_mb⟩
      (by sep_focus)
      (fun _ _ _ _ hex => False.elim (not_satisfies_false_sepConj hex))
      (fun _ _ => wppBudgetPanic_false) ?_
    intro sm hpcm hrunm hspm hcsm hinvm; simp only [CalleeSavedPreserved] at hcsm
    obtain ⟨hx19_m, hx20_m, hx21_m, hx22_m, hx23_m, hx24_m, _, hx26_m, hx27_m, hx28_m, _, hvregs_m⟩ := hcsm
    simp (config := { decide := true }) only [arm64_norm, hsp, hx19, hx20, hx21, hx22, hx23, hx24, hx26, hx27, hx28, hvregs]
      at hpcm hrunm hspm hx19_m hx20_m hx21_m hx22_m hx23_m hx24_m hx26_m hx27_m hx28_m hvregs_m
    cases hmb : mergeBytes .lengthDelimited rest with
    | none =>
      have hnone := hnone_of_mb hmb
      apply SepWPp.of_sepWP_lscro (mid := (blkPl_297).base + 836#64) hinvm
      conv => arg 4; dsimp only [bytesMerge3RawBudgetSpec]
      conv => arg 4; simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
      apply SepWP.exists_elim; intro evs_mb
      conv => arg 4; simp only [hmb, vecU8At_zero_eq_cells A.repAlloc s0.sp,
        memRegion_48_cells1_160 s0.sp, sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
      apply SepWP.exists_elim; intro v_err0
      wp_focus_pure; intro htrm; wp_focus_pure; intro hevs_mb; wp_focus_pure; intro hsm0
      conv => arg 4; simp only [sepConj_assoc, arm64_norm, hsp]
      have hcbnz_err : (sm.readReg64 (Reg.gpr 0#5) == 0#64) = false := beq_eq_false_iff_ne.mpr hsm0
      apply SepWP.fold (polyBelow_bytesMerge3_entails s0.sp) (by sep_focus)
      apply SepWP.fold (pointsToBytes_prefix_join hrest_le hrest_suf) (by sep_focus)
      wp_steps_sync_pool ((blkPl_297).base + 836#64)
      simp only [State.setMem_setMem]
      apply SepWP.fold (cells160_entails_memRegion32 s0.sp v_stk0 0#64 1#64 0#64) (by sep_focus)
      wp_reach; intro hinvm'
      have hiter_mb : PolyMergeIterEnv x.bs.length (polyEncoderCapBound x) evs_mb :=
        PolyMergeIterEnv.of_bytesMerge3Err hmb hevs_mb
      have hfits_st1 : FitsEnv M lim (M.stepEvents evs_mb st_cur)
          (PolyMergeLoopEnv 1 x.bs.length (polyEncoderCapBound x)) :=
        FitsEnv.polyMergeLoop_tail hiter_mb hfits2
      have hevs_acc1 : PolyMergeLoopEnv (f_acc + 1) x.bs.length (polyEncoderCapBound x)
          (evs_acc ++ evs_mb) :=
        hevs_acc.append (PolyMergeLoopEnv.single (fuel := 0) hiter_mb)
      have hst1 : M.stepEvents evs_mb st_cur = M.stepEvents (evs_acc ++ evs_mb) st0 := by
        rw [hst_cur, ← AllocCostModel.stepEvents_append]
      refine SepWPp.weaken_pre (Entails.of_eq (by dsimp only [polyEncoderErrFrame]; sep_ac_rfl))
        (polyEncoder_push_err_exit_cl_placed hPushCall hnone hsm0 (Nat.le_refl 1) hf_tot
          hevs_acc1 hst1 hfits_st1 hsp_align
          (by simp only [arm64_norm]) (by simp only [arm64_norm, hrunm]) (by simp only [arm64_norm, hspm])
          (by simp only [arm64_norm, htrm, htr]) (by simp only [arm64_norm, hspm])
          ⟨by simp only [arm64_norm, hx26_m], by simp only [arm64_norm, hx27_m],
           by simp only [arm64_norm, hx28_m], by simp only [arm64_norm, hvregs_m]⟩ hinvm')
    | some p =>
      rcases p with ⟨v, rest'⟩
      have hrest'_le : rest'.length ≤ rest.length := mergeBytes_length hmb
      have hmb_len := mergeBytes_len_bound hmb
      conv => arg 4; dsimp only [bytesMerge3RawBudgetSpec]
      conv => arg 4; simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
      apply SepWPp.exists_elim; intro evs_mb
      conv => arg 4; simp only [hmb, sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
      apply SepWPp.exists_elim; intro cap_e; apply SepWPp.exists_elim; intro ptr_e
      conv => arg 4; rw [protoPolynomialEncoderAt_unfold_polys]
      conv => arg 4; simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
      apply SepWPp.exists_elim; intro cap; apply SepWPp.exists_elim; intro ptr
      apply sepWPp_focus_pure (by sep_focus); intro htrm; apply sepWPp_focus_pure (by sep_focus); intro hevs_mb
      apply sepWPp_focus_pure (by sep_focus); intro hsm0; apply sepWPp_focus_pure (by sep_focus); intro _hcap_ok
      apply sepWPp_focus_pure (by sep_focus); rintro ⟨hlen_le, hcap_bound, hptr_ne⟩
      conv => arg 4; simp only [sepConj_assoc, arm64_norm, hsp]
      have hfits_mb_tail : FitsEnv M lim (M.stepEvents evs_mb st_cur)
          (PolyMergeLoopEnv 1 x.bs.length (polyEncoderCapBound x)) :=
        FitsEnv.polyMergeLoop_bytesTail (bs := rest) hmb hrest_le hevs_mb
          (FitsEnv.polyMergeLoop_mono (by omega) (Nat.le_refl _) (Nat.le_refl _) hfits_rem)
      by_cases hcap_eq : m.polys.length = cap.toNat
      · have hbne : (BitVec.ofNat 64 m.polys.length != cap) = false := len_eq_cap_bne_false hcap_eq
        have hgrow_bound : max (2 * cap.toNat) 4 * 24 + 8 ≤ 2 ^ 63 := by omega
        apply SepWPp.of_sepWP_lscro (mid := lsmpl.base 621) hinvm
        apply SepWP.fold (polyBelow_bytesMerge3_entails s0.sp) (by sep_focus)
        apply SepWP.fold (sliceCursorAfter_join hrest_le hrest_suf hrest'_le) (by sep_focus)
        apply SepWP.fold (vecBuf_vecU8_entails_grow_pre A.repAlloc cap ptr m.polys hcap_eq) (by sep_focus)
        conv => arg 4; rw [polyBelow_extHook s0.sp]
        conv => arg 4; simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
        apply SepWP.exists_elim; intro pins
        wp_focus_pure; rintro ⟨hpins_len, hbytes_len⟩
        wp_steps_sync_pool (lsmpl.base 621)
        simp only [State.setMem_setMem]
        wp_reach; intro hinvm'
        have hfits_grow : FitsEnv M lim (M.stepEvents evs_mb st_cur)
            (GrowOneVecU8Env ⟨x.msgPtr + 24#64, cap, ptr, vecU8ArrayBytes pins m.polys⟩) :=
          FitsEnv.polyMergeLoop_head (fuel := 0)
            (fun _ hg => PolyMergeIterEnv.of_growOneVecU8 (by dsimp; omega) hg) hfits_mb_tail
        refine SepWPp.call_frame_lscro (spec := growOneVecU8BudgetSpec M A lim)
          (x := (⟨x.msgPtr + 24#64, cap, ptr, vecU8ArrayBytes pins m.polys⟩, M.stepEvents evs_mb st_cur))
          (ret_pc := (blkPl_297).base + 296#64) hGrowCall hinvm'
          (by simp only [arm64_norm]) (by simp only [arm64_norm, hrunm])
          (by simp only [State.spAligned, hspm, arm64_norm]; exact hsp_align) (by simp only [arm64_norm])
          rfl
          ⟨by simp only [arm64_norm, hspm, hx20_m], hbytes_len, hptr_ne,
           by dsimp only [rawVecNewCap]; exact hgrow_bound, hfits_grow⟩
          (by dsimp only [RustCliAllocBudget.live]; rw [bv64_add24_add8]; sep_focus)
          (fun _ _ _ _ hex => False.elim (not_satisfies_false_sepConj hex))
          (fun _ _ => wppBudgetPanic_false) ?_
        intro sm2 hpcm2 hrunm2 hspm2 hcsm2 hinvm2; simp only [CalleeSavedPreserved] at hcsm2
        obtain ⟨hx19_2, hx20_2, hx21_2, hx22_2, hx23_2, hx24_2, hx25_2, hx26_2, hx27_2, hx28_2, _, hvregs_2⟩ := hcsm2
        simp (config := { decide := true }) only [arm64_norm, hspm, hx19_m, hx20_m, hx21_m, hx22_m, hx23_m, hx24_m, hx26_m, hx27_m, hx28_m, hvregs_m]
          at hpcm2 hrunm2 hspm2 hx19_2 hx20_2 hx21_2 hx22_2 hx23_2 hx24_2 hx25_2 hx26_2 hx27_2 hx28_2 hvregs_2
        conv => arg 4; dsimp only [growOneVecU8BudgetSpec, rawVecGrowBudgetSpec]
        conv => arg 4; simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
        apply SepWPp.exists_elim; intro evs_g
        apply SepWPp.exists_elim; intro p'
        apply sepWPp_focus_pure (by sep_focus); rintro ⟨htrm2, hevs_g⟩
        apply sepWPp_focus_pure (by sep_focus); rintro ⟨hp'_ne, _⟩
        conv => arg 4; simp only [sepConj_assoc, arm64_norm, hspm]
        have hnew_toNat : (newCapVecU8 cap).toNat = max (2 * cap.toNat) 4 := by
          unfold newCapVecU8; rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
        have hlt_new : m.polys.length < (newCapVecU8 cap).toNat := by rw [hnew_toNat]; omega
        have hbound_new : (newCapVecU8 cap).toNat * 24 < 2 ^ 63 := by rw [hnew_toNat]; omega
        have hevs_step : PolyMergeLoopEnv (2 * v.length + 2) x.bs.length (polyEncoderCapBound x)
            (evs_mb ++ evs_g) := by
          have h1 : PolyMergeLoopEnv (2 * v.length + 1) x.bs.length (polyEncoderCapBound x) evs_mb := by
            simpa using
              (PolyMergeLoopEnv.bytesSingle (fuel := 0)
                (maxLen := x.bs.length) (polyCapBound := polyEncoderCapBound x)
                hmb hrest_le hevs_mb)
          have h2 : PolyMergeLoopEnv 1 x.bs.length (polyEncoderCapBound x) evs_g :=
            PolyMergeLoopEnv.single (fuel := 0)
              (PolyMergeIterEnv.of_growOneVecU8 (by dsimp; omega) hevs_g)
          exact h1.append h2
        have hst_next : M.stepEvents evs_g (M.stepEvents evs_mb st_cur) =
            M.stepEvents (evs_mb ++ evs_g) st_cur :=
          (AllocCostModel.stepEvents_append M evs_mb evs_g st_cur).symm
        conv => arg 4; dsimp only [rawVecNewCap]
        conv => arg 4; rw [show A.live p' (max (2 * cap.toNat) 4 * 24) 8 =
          A.repAlloc.live p' (max (2 * cap.toNat) 4 * 24) 8 from rfl,
          show BitVec.ofNat 64 (max (2 * cap.toNat) 4) = newCapVecU8 cap from rfl, hst_next]
        apply sepWPp_fold
          (grow_post_entails_ready A.repAlloc cap p' pins m.polys hcap_eq hpins_len hgrow_bound)
          (by sep_focus)
        apply sepWPp_fold (polyBelow_extHook_entails s0.sp) (by sep_focus)
        refine SepWPp.weaken_pre ?_
          (polyEncoder_tag3_copy_step_cro (st_next := M.stepEvents (evs_mb ++ evs_g) st_cur)
            (v_stk0 := v_stk0) (cap' := newCapVecU8 cap) (ptr' := p')
            (cap_e := cap_e) (ptr_e := ptr_e) hsp_align hlt_new hbound_new hp'_ne
            (fun s' => hcont v rest' _ (evs_mb ++ evs_g) s' hmb hevs_step rfl)
            hpcm2 hrunm2 hspm2 (htrm2.trans (htrm.trans htr))
            hx19_2 hx20_2 hx21_2 hx22_2 hx23_2 hx24_2
            (hx25_2.trans (by rw [hcap_eq, BitVec.ofNat_toNat, BitVec.setWidth_eq]))
            ⟨hx26_2, hx27_2, hx28_2, hvregs_2⟩ hinvm2)
        exact Entails.of_eq (by sep_ac_rfl)
      · have hlt : m.polys.length < cap.toNat := Nat.lt_of_le_of_ne hlen_le hcap_eq
        have hbne : (BitVec.ofNat 64 m.polys.length != cap) = true := len_lt_cap_bne_true hlt
        have hcap_ne0 : cap ≠ 0 := by intro h0; subst h0; change m.polys.length < 0 at hlt; omega
        have hevs_step : PolyMergeLoopEnv (2 * v.length + 2) x.bs.length (polyEncoderCapBound x)
            evs_mb :=
          (PolyMergeLoopEnv.bytesSingle (fuel := 0)
            (maxLen := x.bs.length) (polyCapBound := polyEncoderCapBound x)
            hmb hrest_le hevs_mb).mono_fuel (by omega)
        apply SepWPp.of_sepWP_lscro (mid := (blkPl_297).base + 296#64) hinvm
        (conv => arg 4; simp only [hcap_ne0, ↓reduceIte, sepConj_assoc])
        apply SepWP.fold (polyBelow_bytesMerge3_entails s0.sp) (by sep_focus)
        apply SepWP.fold (sliceCursorAfter_join hrest_le hrest_suf hrest'_le) (by sep_focus)
        wp_steps_sync_pool ((blkPl_297).base + 296#64)
        simp only [State.setMem_setMem]
        wp_reach; intro hinvm'
        refine SepWPp.weaken_pre ?_
          (polyEncoder_tag3_copy_step_cro (st_next := M.stepEvents evs_mb st_cur)
            (v_stk0 := v_stk0) (cap' := cap) (ptr' := ptr) (cap_e := cap_e) (ptr_e := ptr_e)
            hsp_align hlt hcap_bound hptr_ne
            (fun s' => hcont v rest' _ evs_mb s' hmb hevs_step rfl)
            (by simp only [arm64_norm]) (by simp only [arm64_norm, hrunm]) (by simp only [arm64_norm, hspm])
            (by simp only [arm64_norm, htrm, htr])
            (by simp only [arm64_norm, hx19_m]) (by simp only [arm64_norm, hx20_m])
            (by simp only [arm64_norm, hx21_m]) (by simp only [arm64_norm, hx22_m])
            (by simp only [arm64_norm, hx23_m]) (by simp only [arm64_norm, hx24_m])
            (by simp only [arm64_norm])
            ⟨by simp only [arm64_norm, hx26_m], by simp only [arm64_norm, hx27_m],
             by simp only [arm64_norm, hx28_m], by simp only [arm64_norm, hvregs_m]⟩ hinvm')
        exact Entails.of_eq (by sep_ac_rfl)
  · have hnone := hnone_of_mb (mergeBytes_eq_none_of_ne_len hiwt)
    obtain ⟨hbne2_64, hbne2_32⟩ := iwt_bne_two_true_of_ne_len hiwt
    have hfits_from : FitsEnv M lim st_cur DecodeErrorFromEnv :=
      FitsEnv.polyMergeLoop_head (fuel := 1) (fun _ => PolyMergeIterEnv.of_decodeErrorFrom) hfits2
    apply SepWPp.of_sepWP_lscro (mid := lsmpl.base 261) hinv
    conv => arg 4; rw [polyEncoderLoopPre, sliceCursorAfter_eq_split hrest_le hrest_suf,
      sliceCursorAt, memRegion_48_wtErr160 s0.sp, polyBelow_decodeErrorHook s0.sp]
    conv => arg 4; simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
    apply SepWP.exists_elim; intro b_wt1; apply SepWP.exists_elim; intro b_wt0; apply SepWP.exists_elim; intro v_wt0
    wp_steps_sync_pool (lsmpl.base 261)
    simp only [State.setMem_setMem]
    apply SepWP.fold (wtErr160_entails_memRegion40 s0.sp _ _) (by sep_focus)
    apply SepWP.fold (pointsTo64_pair_entails_memRegion16 x.slot restPtr (BitVec.ofNat 64 rest.length)) (by sep_focus)
    apply SepWP.fold (pointsToBytes_prefix_join hrest_le hrest_suf) (by sep_focus)
    wp_reach; intro hinv
    refine SepWPp.call_frame_lscro (spec := decodeErrorFromBudgetSpec M A lim)
      (x := (s0.sp - 128#64, 0x8000000000000006#64, st_cur))
      (ret_pc := (blkPl_297).base + 700#64) hFromCall hinv
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

end LibsignalBinary.Proofs.SpqrV1.Prost.MessageMerge.PolyEncoderBudgetSteps
