/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SpqrV1.Prost.MessageMerge.EpochDirectionBudgetAux
public import LibsignalBinary.Proofs.Placed.BudgetPoolSync
public meta import LibsignalBinary.Proofs.Placed.BudgetPoolSync -- shake: keep
public import LibsignalBinary.Proofs.Placed.BudgetVmSteps
public meta import LibsignalBinary.Proofs.Placed.BudgetVmSteps -- shake: keep
import LibsignalBinary.Proofs.Common.SharedHelpers
meta import LibsignalBinary.Proofs.Common.SharedHelpers -- shake: keep
import LibsignalBinary.Proofs.FnOffEq
import LibsignalBinary.Proofs.ProtoCodecRoundTrip
import LibsignalBinary.Proofs.TripleRatchet.GeneralizeEntry
import LibsignalBinary.Proofs.TripleRatchet.Prost.BytesMerge.Phase1
import GeneratedLean.LibsignalSessionCode -- shake: keep
import LibsignalBinary.Specifications.LibsignalSpqrV1.Wire -- shake: keep

/-!
# Budget-Threaded Step Lemmas for `EpochDirection::merge` (Block `299`)

Proves the `withLsCodeRoLoaded`-threaded tag-2 (`next`), tag-3 (`prev`), loop-limit exit, and
key-decode step lemmas for `EpochDirection::merge` on Block `299`.
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 400000
set_option linter.unusedSimpArgs false

open CryptoVerification.LibsignalTripleRatchet.Prost (HighCalleeSaved IsDropSuffix bv32_zeroExtend_ofNat decodeVarint_suffix key_shr32_of_ge key_shr32_of_lt key_wt_none key_wt_some memRegion_48_split2 pointsTo64_memRegion32_entails_40 pointsTo64_pair_entails_memRegion16 pointsToBytes_prefix_join sliceCursorAfter_eq_split sliceCursorAfter_join sliceCursorAt suffix_trans tag_cbz_false w1_tag_eq)
open CryptoVerification.SpqrV1.Prost.MessageMerge (EpochDirectionMergeGhost WppPost blkPC_299 blkPl_299 cmp_len_limit_of_eq cmp_len_limit_of_gt cmp_len_limit_of_lt codecWireTypeToProto epochDirectionPBCapOkAt epochDirectionPBCapOkAt_entails_epochDirectionPBAt epochDirectionPBCapOkAt_mono epochDirectionPBCapOkAt_unfold_next epochDirectionPBCapOkAt_unfold_prev memRegion_48_split_96 mergeBytes_length mergeLoopBin mergeLoopBin_eq_limit mergeLoopBin_lt_limit mergeLoopBin_of_decodeVarint_none mergeLoopBin_of_key_ge mergeLoopBin_of_tag_zero mergeLoopBin_of_wt_none protoPrefixStep_epochDirectionPB_mergeField setWidth8_ofNat64_wt skipBelow3_bytesMerge3 skipBelow3_bytesMerge3_entails vecU8At_entails_rustBytesVecAt vecU8At_entails_vecU8CapOkAt vecU8CapOkAt_entails_rustBytesVecAt vecU8CapOkAt_mono)
open CryptoVerification.SpqrV1.Varint (skipBelow3_leaf skipBelow3_leaf_entails stackAt_skipField3)
open LibsignalBinary.Proofs.SpqrV1.Prost.MessageMerge.EpochDirectionBudgetAux (EpochDirectionLoopEnv EpochDirectionOkEnv bytesMergeEventsCore_effCap decodeVarint2Env_of_none decodeVarint2Env_of_some epochDirectionErrFrame epochDirectionLoopPre epochDirectionMergeSpecOfEnv epochDirection_err0_ret_exit_placed epochDirection_from_err_exit_cl_placed epochDirection_push_err_exit_cl_placed)

namespace LibsignalBinary.Proofs.SpqrV1.Prost.MessageMerge.EpochDirectionBudgetSteps

open Arm64 ProofLib SepProp
open CryptoVerification
  (LibsignalCodeLoaded LibsignalHooks LibsignalPlacement lsmpl withLsCodeLoaded)
open scoped CryptoVerification
open scoped CryptoVerification.CodeLayout
open scoped CryptoVerification.SpqrV1.Prost.MessageMerge
open CryptoVerification.RustHeap (vecU8At)
open CryptoVerification.LibsignalProtoCodec
  (WireType decodeVarint decodeVarint_length mergeBytes skipField skip_length)
open CryptoVerification.LibsignalTripleRatchet
  (KindNoHeap LibsignalCodeRoLoaded decodeErrorAtStackLen extract_withLsCodeRoLoaded
   withLsCodeRoLoaded)
open CryptoVerification.LibsignalSpqrV1 (EpochDirectionPB)
open CryptoVerification.LibsignalSpqrV1.Proto (mergeMessage)
open CryptoVerification.SpqrV1.ProtoRepr (epochDirectionPBAt)
open LibsignalBinary.Heap
  (AllocCostModel AllocEvent BudgetLimits FitsEnv RustCliAllocBudget
   fitsEvents_append rustAllocEvents)
open LibsignalBinary.Heap.SpecBudget
  (DecodeErrorFromEnv DecodeErrorPushEnv decodeErrorFromBudgetSpec decodeErrorPushBudgetSpec)
open LibsignalBinary.Proofs.Placed.BudgetPoolSync (hooksException sepWP_seg_ls_vm)
open LibsignalBinary.Proofs.SpqrV1.Prost.MessageMerge.PolyCommonBudget
  (BytesMerge3Env BytesMerge3EnvCore WppBudgetPanic bytesMerge3RawBudgetSpec wppBudgetPanic_false)
open LibsignalBinary.Proofs.SpqrV1.Varint.DecodeVarint2Budget
  (DecodeVarint2Env decodeVarint2Spec decodeVarint2SpecGen)
open LibsignalBinary.Proofs.SpqrV1.Varint.SkipField3Budget (SkipField3Env skipField3Spec)
open LibsignalBinary.Proofs.TripleRatchet.Prost.BytesMerge.Phase23BudgetAux (mergeBytes_length_sum)

private theorem sp_setMem_pre (s : State) (m : Memory) : (s.setMem m).sp = s.sp := by cases s; rfl
private theorem pc_setMem_pre (s : State) (m : Memory) : (s.setMem m).pc = s.pc := by cases s; rfl
private theorem status_setMem_pre (s : State) (m : Memory) : (s.setMem m).status = s.status := by
  cases s; rfl
private theorem pstate_setMem_pre (s : State) (m : Memory) : (s.setMem m).pstate = s.pstate := by
  cases s; rfl
private theorem trace_setMem_pre (s : State) (m : Memory) : (s.setMem m).trace = s.trace := by
  cases s; rfl
private theorem readReg64_setMem_pre (s : State) (m : Memory) (r : Reg) :
    (s.setMem m).readReg64 r = s.readReg64 r := by cases s; rfl
private theorem readReg32_setMem_pre (s : State) (m : Memory) (r : Reg) :
    (s.setMem m).readReg32 r = s.readReg32 r := by cases s; rfl
private theorem readReg_setMem_pre (s : State) (m : Memory) (w : Width) (r : Reg) :
    (s.setMem m).readReg w r = s.readReg w r := by cases s; rfl
private theorem calleeSavedVRegs_setMem_pre (s : State) (m : Memory) :
    calleeSavedVRegs (s.setMem m) = calleeSavedVRegs s := by cases s; rfl

@[local simp, local arm64_norm]
private theorem bv64_sub_zero (x : BitVec 64) : x - 0#64 = x := BitVec.sub_zero x

@[local simp, local arm64_norm]
private theorem bv64_add_zero (x : BitVec 64) : x + 0#64 = x := BitVec.add_zero x

attribute [local irreducible] Program.fetch Program.externAt?
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero
attribute [local arm64_norm ↓, local wp_norm ↓]
  sp_setMem_pre pc_setMem_pre status_setMem_pre pstate_setMem_pre trace_setMem_pre
  readReg64_setMem_pre readReg32_setMem_pre readReg_setMem_pre calleeSavedVRegs_setMem_pre

theorem subroutine_ok_withLsCodeRoLoaded_of_bare {α : Type} {prog : Program}
    {pl : Obj.MultiPlacement} {entry : BitVec 64} {spec : Spec α}
    (h : subroutine_ok prog entry spec) :
    subroutine_ok prog entry (withLsCodeRoLoaded pl spec) :=
  subroutine_ok_mono h
    (fun _ _ _ hp => (extract_withLsCodeRoLoaded hp).2)
    (fun _ _ _ _ hq => hq)
    (fun _ _ _ _ hpan => hpan)

/-! ## Tag 2 (`next`), Tag 3 (`prev`), Loop Exit, and Key Decode Step Lemmas (Block `299`) -/

/-- Code-loaded placed step lemma for tag 2 (`next`) at `+0x104` (`(blkPl_299).base + 260#64`). -/
theorem epochDirection_tag2_step_cl_placed [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {H : LibsignalHooks}
    {PreEnv PostEnv : EpochDirectionMergeGhost → List AllocEvent → Prop}
    (hPushCall : subroutine_ok ((blkPC_299).rebase (blkPl_299).base H) (lsmpl.base 257)
      (withLsCodeRoLoaded lsmpl (decodeErrorPushBudgetSpec M A lim)))
    (hBytesCall : subroutine_ok ((blkPC_299).rebase (blkPl_299).base H) (lsmpl.base 290)
      (withLsCodeRoLoaded lsmpl (bytesMerge3RawBudgetSpec A lim)))
    {x : EpochDirectionMergeGhost} {st0 st_cur : M.σ} {R : SepProp}
    {s0 s : State} {m : EpochDirectionPB} {rest : List (BitVec 8)} {iwt : WireType} {limit : Nat}
    (hsp_align : (s0.sp &&& 15#64 == 0#64) = true) (hrest_le : rest.length ≤ x.bs.length)
    (hrest_lt : rest.length < 2 ^ 63) (hrest_suf : IsDropSuffix x.bs rest)
    (hFit_cur : FitsEnv M lim st_cur (EpochDirectionLoopEnv (rest.length + 1)))
    (hlift_err : mergeBytes iwt rest = none →
      ∀ evs_rem, EpochDirectionLoopEnv (rest.length + 1) evs_rem →
        ∃ evs, PostEnv x evs ∧ M.stepEvents evs_rem st_cur = M.stepEvents evs st0)
    (hnone_of_mb : mergeBytes iwt rest = none →
      (mergeMessage CryptoVerification.LibsignalSpqrV1.EpochDirectionPB.mergeField (codecWireTypeToProto x.wt) x.msg x.bs 98).toOption = none)
    (hcont : ∀ (v : List (BitVec 8)) (rest' : List (BitVec 8)) (evs_bm : List AllocEvent)
        (effCap : BitVec 64) (s' : State),
      mergeBytes iwt rest = some (v, rest') →
      effCap.toNat ≤ rest.length →
      BytesMerge3EnvCore iwt effCap rest evs_bm →
      FitsEnv M lim (M.stepEvents evs_bm st_cur) (EpochDirectionLoopEnv rest.length) →
      s'.pc = (blkPl_299).base + 160#64 →
      s'.status = .Running → s'.sp = s0.sp - 96#64 → s'.trace = s0.trace →
      s'.readReg64 (Reg.gpr 19#5) = x.bufRef → s'.readReg64 (Reg.gpr 20#5) = x.msgPtr →
      s'.readReg64 (Reg.gpr 21#5) = x.slot → s'.readReg64 (Reg.gpr 22#5) = BitVec.ofNat 64 limit →
      HighCalleeSaved s0 s' → LibsignalCodeRoLoaded lsmpl s'.mem →
      SepWPp ((blkPC_299).rebase (blkPl_299).base H) (s0.readReg64 Reg.lr) s'
        (epochDirectionLoopPre A lim (M.stepEvents evs_bm st_cur) s0 s' x.msgPtr x.bufRef x.slot x.ptr
          { m with next := v } x.bs rest')
        (WppPost (epochDirectionMergeSpecOfEnv A lim PreEnv PostEnv) (x, st0) R s0)
        (WppBudgetPanic (epochDirectionMergeSpecOfEnv A lim PreEnv PostEnv) (x, st0) R s0))
    (hpc : s.pc = (blkPl_299).base + 260#64)
    (hrun : s.status = .Running) (hsp : s.sp = s0.sp - 96#64) (htr : s.trace = s0.trace)
    (hx0 : s.readReg64 (Reg.gpr 0#5) = BitVec.ofNat 64 iwt.toNat)
    (hx19 : s.readReg64 (Reg.gpr 19#5) = x.bufRef)
    (hx20 : s.readReg64 (Reg.gpr 20#5) = x.msgPtr)
    (hx21 : s.readReg64 (Reg.gpr 21#5) = x.slot)
    (hx22 : s.readReg64 (Reg.gpr 22#5) = BitVec.ofNat 64 limit)
    (hcs : HighCalleeSaved s0 s) (hinv : LibsignalCodeRoLoaded lsmpl s.mem) :
    SepWPp ((blkPC_299).rebase (blkPl_299).base H) (s0.readReg64 Reg.lr) s
      (epochDirectionLoopPre A lim st_cur s0 s x.msgPtr x.bufRef x.slot x.ptr m x.bs rest)
      (WppPost (epochDirectionMergeSpecOfEnv A lim PreEnv PostEnv) (x, st0) R s0)
      (WppBudgetPanic (epochDirectionMergeSpecOfEnv A lim PreEnv PostEnv) (x, st0) R s0) := by
  obtain ⟨hx23, hx24, hx25, hx26, hx27, hx28, hvregs⟩ := hcs
  let restPtr : BitVec 64 := x.ptr + BitVec.ofNat 64 (x.bs.length - rest.length)
  apply CryptoVerification.SpqrV1.Prost.MessageMerge.SepWPp.of_sepWP_lscro (mid := lsmpl.base 290) hinv
  conv => arg 4; rw [epochDirectionLoopPre, epochDirectionPBCapOkAt_unfold_next,
    sliceCursorAfter_eq_split hrest_le hrest_suf,
    skipBelow3_bytesMerge3 s0.sp 98 (by decide) (by decide)]
  conv => arg 4; simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
  apply SepWP.exists_elim; intro v_cap
  apply SepWP.exists_elim; intro v_ptr
  apply SepWP.pure_elim; intro hcap
  wp_steps_sync_pool (lsmpl.base 290)
  simp only [State.setMem_setMem]
  wp_reach; intro hinv
  have hfits_bm : FitsEnv M lim st_cur
      (BytesMerge3Env ⟨iwt, x.msgPtr, v_cap, v_ptr, m.next, x.bufRef, x.slot, restPtr, rest⟩) :=
    LibsignalBinary.Proofs.SpqrV1.Prost.MessageMerge.EpochDirectionBudgetAux.FitsEnv.epochDirection_bytesMerge3 (Nat.le_refl _) hrest_lt hFit_cur
  refine CryptoVerification.SpqrV1.Prost.MessageMerge.SepWPp.call_frame_lscro (spec := bytesMerge3RawBudgetSpec A lim)
    (x := (⟨iwt, x.msgPtr, v_cap, v_ptr, m.next, x.bufRef, x.slot, restPtr, rest⟩, st_cur))
    (ret_pc := (blkPl_299).base + 272#64) hBytesCall hinv
    (by simp only [arm64_norm]) (by simp only [arm64_norm, hrun])
    (by simp only [State.spAligned, hsp, arm64_norm]; exact hsp_align) (by simp only [arm64_norm])
    rfl
    ⟨by simp only [arm64_norm, hsp, hx0, setWidth8_ofNat64_wt],
     by simp only [arm64_norm, hsp, hx20],
     by simp only [arm64_norm, hsp, hx19],
     hrest_lt, hcap, hfits_bm⟩
    (by sep_focus)
    (fun _ _ _ _ hex => False.elim (not_satisfies_false_sepConj hex))
    (fun _ _ => wppBudgetPanic_false) ?_
  intro sm hpcm hrunm hspm hcsm hinvm; simp only [CalleeSavedPreserved] at hcsm
  obtain ⟨hx19_m, hx20_m, hx21_m, hx22_m, hx23_m, hx24_m, hx25_m, hx26_m, hx27_m, hx28_m, hfp_m, hvregs_m⟩ := hcsm
  simp (config := { decide := true }) only [arm64_norm, hsp, hx19, hx20, hx21, hx22, hx23, hx24, hx25, hx26, hx27, hx28, hvregs]
    at hpcm hrunm hspm hx19_m hx20_m hx21_m hx22_m hx23_m hx24_m hx25_m hx26_m hx27_m hx28_m hfp_m hvregs_m
  obtain ⟨hnone_core, hsome_core⟩ := bytesMergeEventsCore_effCap iwt v_cap rest hrest_lt
  cases hmb : mergeBytes iwt rest with
  | none =>
    have hnone := hnone_of_mb hmb
    apply CryptoVerification.SpqrV1.Prost.MessageMerge.SepWPp.of_sepWP_lscro (mid := (blkPl_299).base + 548#64) hinvm
    (conv => arg 4; simp only [bytesMerge3RawBudgetSpec, hmb,
      sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc])
    apply SepWP.exists_elim; intro evs_bm
    wp_focus_pure; intro htrm
    wp_focus_pure; intro hevs_bm
    wp_focus_pure; intro hsm0
    have hevs_eq : evs_bm = rustAllocEvents 72 8 := by
      change evs_bm = _ at hevs_bm
      rw [hevs_bm, hnone_core hmb]
    rw [hevs_eq]
    conv => arg 4; simp only [arm64_norm, hsp]
    have hcbnz_err : (sm.readReg64 (Reg.gpr 0#5) == 0#64) = false := beq_eq_false_iff_ne.mpr hsm0
    apply SepWP.fold (skipBelow3_bytesMerge3_entails s0.sp 98 (by decide) (by decide)) (by sep_focus)
    apply SepWP.fold (pointsToBytes_prefix_join hrest_le hrest_suf) (by sep_focus)
    apply SepWP.fold (vecU8At_entails_rustBytesVecAt A.repAlloc x.msgPtr v_cap v_ptr m.next) (by sep_focus)
    apply SepWP.fold (vecU8CapOkAt_entails_rustBytesVecAt A.repAlloc (x.msgPtr + 0x18#64) rest.length m.prev) (by sep_focus)
    (conv => arg 4; rw [memRegion_48_split_96 s0.sp]; simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc])
    apply SepWP.exists_elim; intro v_stk0
    wp_steps_sync_pool ((blkPl_299).base + 548#64)
    simp only [State.setMem_setMem]
    wp_reach; intro hinvm
    refine SepWPp.weaken_pre (by dsimp only [epochDirectionErrFrame, epochDirectionPBAt]; sep_entail)
      (epochDirection_push_err_exit_cl_placed hPushCall hnone hsm0
        (LibsignalBinary.Proofs.SpqrV1.Prost.MessageMerge.EpochDirectionBudgetAux.FitsEnv.epochDirection_push0_after_from hFit_cur)
        (fun evs_p hp => by
          obtain ⟨evs, hevs_post, hst_eq⟩ := hlift_err hmb (rustAllocEvents 72 8 ++ evs_p) (.errFromPush hp)
          exact ⟨evs, hevs_post, (M.stepEvents_append (rustAllocEvents 72 8) evs_p st_cur).symm.trans hst_eq⟩)
        hsp_align
        (by simp only [arm64_norm]) (by simp only [arm64_norm, hrunm]) (by simp only [arm64_norm, hspm])
        (by simp only [arm64_norm, htrm, htr]) (by simp only [arm64_norm, hspm])
        ⟨by simp only [arm64_norm, hx23_m], by simp only [arm64_norm, hx24_m],
         by simp only [arm64_norm, hx25_m], by simp only [arm64_norm, hx26_m],
         by simp only [arm64_norm, hx27_m], by simp only [arm64_norm, hx28_m],
         by simp only [arm64_norm, hvregs_m]⟩ hinvm)
  | some p =>
    rcases p with ⟨v, rest'⟩
    have hrest'_le : rest'.length ≤ rest.length := mergeBytes_length hmb
    obtain ⟨effCap, heff_le, heq_core⟩ := hsome_core v rest' hmb
    apply CryptoVerification.SpqrV1.Prost.MessageMerge.SepWPp.of_sepWP_lscro (mid := (blkPl_299).base + 160#64) hinvm
    (conv => arg 4; simp only [bytesMerge3RawBudgetSpec, hmb,
      sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc])
    apply SepWP.exists_elim; intro evs_bm
    apply SepWP.exists_elim; intro cap'
    apply SepWP.exists_elim; intro ptr'
    wp_focus_pure; intro htrm
    wp_focus_pure; intro hevs_bm
    wp_focus_pure; intro hsm0
    wp_focus_pure; intro hcap'
    have hbm_eff : BytesMerge3EnvCore iwt effCap rest evs_bm := by
      change evs_bm = _ at hevs_bm ⊢
      simpa [← heq_core] using hevs_bm
    have hFit_next : FitsEnv M lim (M.stepEvents evs_bm st_cur) (EpochDirectionLoopEnv rest.length) :=
      fun evs₂ he₂ =>
        ((fitsEvents_append M lim evs_bm evs₂ st_cur).mp
          (hFit_cur (evs_bm ++ evs₂) (.stepBytes iwt effCap rest (Nat.le_refl _) heff_le hbm_eff he₂))).2
    conv => arg 4; simp only [arm64_norm, hsp]
    apply SepWP.fold (skipBelow3_bytesMerge3_entails s0.sp 98 (by decide) (by decide)) (by sep_focus)
    apply SepWP.fold (sliceCursorAfter_join hrest_le hrest_suf hrest'_le) (by sep_focus)
    apply SepWP.fold (vecU8At_entails_vecU8CapOkAt hcap') (by sep_focus)
    apply SepWP.fold (@vecU8CapOkAt_mono A.repAlloc (x.msgPtr + 0x18#64) rest.length rest'.length m.prev hrest'_le) (by sep_focus)
    wp_steps_sync_pool ((blkPl_299).base + 160#64)
    simp only [State.setMem_setMem]
    wp_reach; intro hinvm
    refine SepWPp.weaken_pre (by dsimp only [epochDirectionLoopPre, epochDirectionPBCapOkAt]; sep_entail)
      (hcont v rest' evs_bm effCap _ hmb heff_le hbm_eff hFit_next
        (by simp only [arm64_norm]) (by simp only [arm64_norm, hrunm]) (by simp only [arm64_norm, hspm])
        (by simp only [arm64_norm, htrm, htr])
        (by simp only [arm64_norm, hx19_m]) (by simp only [arm64_norm, hx20_m])
        (by simp only [arm64_norm, hx21_m]) (by simp only [arm64_norm, hx22_m])
        ⟨by simp only [arm64_norm, hx23_m], by simp only [arm64_norm, hx24_m],
         by simp only [arm64_norm, hx25_m], by simp only [arm64_norm, hx26_m],
         by simp only [arm64_norm, hx27_m], by simp only [arm64_norm, hx28_m],
         by simp only [arm64_norm, hvregs_m]⟩ hinvm)

/-- Code-loaded placed step lemma for tag 3 (`prev`) at `+0x0ec` (`(blkPl_299).base + 236#64`). -/
theorem epochDirection_tag3_step_cl_placed [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {H : LibsignalHooks}
    {PreEnv PostEnv : EpochDirectionMergeGhost → List AllocEvent → Prop}
    (hPushCall : subroutine_ok ((blkPC_299).rebase (blkPl_299).base H) (lsmpl.base 257)
      (withLsCodeRoLoaded lsmpl (decodeErrorPushBudgetSpec M A lim)))
    (hBytesCall : subroutine_ok ((blkPC_299).rebase (blkPl_299).base H) (lsmpl.base 290)
      (withLsCodeRoLoaded lsmpl (bytesMerge3RawBudgetSpec A lim)))
    {x : EpochDirectionMergeGhost} {st0 st_cur : M.σ} {R : SepProp}
    {s0 s : State} {m : EpochDirectionPB} {rest : List (BitVec 8)} {iwt : WireType} {limit : Nat}
    (hsp_align : (s0.sp &&& 15#64 == 0#64) = true) (hrest_le : rest.length ≤ x.bs.length)
    (hrest_lt : rest.length < 2 ^ 63) (hrest_suf : IsDropSuffix x.bs rest)
    (hFit_cur : FitsEnv M lim st_cur (EpochDirectionLoopEnv (rest.length + 1)))
    (hlift_err : mergeBytes iwt rest = none →
      ∀ evs_rem, EpochDirectionLoopEnv (rest.length + 1) evs_rem →
        ∃ evs, PostEnv x evs ∧ M.stepEvents evs_rem st_cur = M.stepEvents evs st0)
    (hnone_of_mb : mergeBytes iwt rest = none →
      (mergeMessage CryptoVerification.LibsignalSpqrV1.EpochDirectionPB.mergeField (codecWireTypeToProto x.wt) x.msg x.bs 98).toOption = none)
    (hcont : ∀ (v : List (BitVec 8)) (rest' : List (BitVec 8)) (evs_bm : List AllocEvent)
        (effCap : BitVec 64) (s' : State),
      mergeBytes iwt rest = some (v, rest') →
      effCap.toNat ≤ rest.length →
      BytesMerge3EnvCore iwt effCap rest evs_bm →
      FitsEnv M lim (M.stepEvents evs_bm st_cur) (EpochDirectionLoopEnv rest.length) →
      s'.pc = (blkPl_299).base + 160#64 →
      s'.status = .Running → s'.sp = s0.sp - 96#64 → s'.trace = s0.trace →
      s'.readReg64 (Reg.gpr 19#5) = x.bufRef → s'.readReg64 (Reg.gpr 20#5) = x.msgPtr →
      s'.readReg64 (Reg.gpr 21#5) = x.slot → s'.readReg64 (Reg.gpr 22#5) = BitVec.ofNat 64 limit →
      HighCalleeSaved s0 s' → LibsignalCodeRoLoaded lsmpl s'.mem →
      SepWPp ((blkPC_299).rebase (blkPl_299).base H) (s0.readReg64 Reg.lr) s'
        (epochDirectionLoopPre A lim (M.stepEvents evs_bm st_cur) s0 s' x.msgPtr x.bufRef x.slot x.ptr
          { m with prev := v } x.bs rest')
        (WppPost (epochDirectionMergeSpecOfEnv A lim PreEnv PostEnv) (x, st0) R s0)
        (WppBudgetPanic (epochDirectionMergeSpecOfEnv A lim PreEnv PostEnv) (x, st0) R s0))
    (hpc : s.pc = (blkPl_299).base + 236#64)
    (hrun : s.status = .Running) (hsp : s.sp = s0.sp - 96#64) (htr : s.trace = s0.trace)
    (hx0 : s.readReg64 (Reg.gpr 0#5) = BitVec.ofNat 64 iwt.toNat)
    (hx19 : s.readReg64 (Reg.gpr 19#5) = x.bufRef)
    (hx20 : s.readReg64 (Reg.gpr 20#5) = x.msgPtr)
    (hx21 : s.readReg64 (Reg.gpr 21#5) = x.slot)
    (hx22 : s.readReg64 (Reg.gpr 22#5) = BitVec.ofNat 64 limit)
    (hcs : HighCalleeSaved s0 s) (hinv : LibsignalCodeRoLoaded lsmpl s.mem) :
    SepWPp ((blkPC_299).rebase (blkPl_299).base H) (s0.readReg64 Reg.lr) s
      (epochDirectionLoopPre A lim st_cur s0 s x.msgPtr x.bufRef x.slot x.ptr m x.bs rest)
      (WppPost (epochDirectionMergeSpecOfEnv A lim PreEnv PostEnv) (x, st0) R s0)
      (WppBudgetPanic (epochDirectionMergeSpecOfEnv A lim PreEnv PostEnv) (x, st0) R s0) := by
  obtain ⟨hx23, hx24, hx25, hx26, hx27, hx28, hvregs⟩ := hcs
  let restPtr : BitVec 64 := x.ptr + BitVec.ofNat 64 (x.bs.length - rest.length)
  apply CryptoVerification.SpqrV1.Prost.MessageMerge.SepWPp.of_sepWP_lscro (mid := lsmpl.base 290) hinv
  conv => arg 4; rw [epochDirectionLoopPre, epochDirectionPBCapOkAt_unfold_prev,
    sliceCursorAfter_eq_split hrest_le hrest_suf,
    skipBelow3_bytesMerge3 s0.sp 98 (by decide) (by decide)]
  conv => arg 4; simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
  apply SepWP.exists_elim; intro v_cap
  apply SepWP.exists_elim; intro v_ptr
  apply SepWP.pure_elim; intro hcap
  wp_steps_sync_pool (lsmpl.base 290)
  simp only [State.setMem_setMem]
  wp_reach; intro hinv
  have hfits_bm : FitsEnv M lim st_cur
      (BytesMerge3Env ⟨iwt, x.msgPtr + 0x18#64, v_cap, v_ptr, m.prev, x.bufRef, x.slot, restPtr, rest⟩) :=
    LibsignalBinary.Proofs.SpqrV1.Prost.MessageMerge.EpochDirectionBudgetAux.FitsEnv.epochDirection_bytesMerge3 (Nat.le_refl _) hrest_lt hFit_cur
  refine CryptoVerification.SpqrV1.Prost.MessageMerge.SepWPp.call_frame_lscro (spec := bytesMerge3RawBudgetSpec A lim)
    (x := (⟨iwt, x.msgPtr + 0x18#64, v_cap, v_ptr, m.prev, x.bufRef, x.slot, restPtr, rest⟩, st_cur))
    (ret_pc := (blkPl_299).base + 248#64) hBytesCall hinv
    (by simp only [arm64_norm]) (by simp only [arm64_norm, hrun])
    (by simp only [State.spAligned, hsp, arm64_norm]; exact hsp_align) (by simp only [arm64_norm])
    rfl
    ⟨by simp only [arm64_norm, hsp, hx0, setWidth8_ofNat64_wt],
     by simp only [arm64_norm, hsp, hx20],
     by simp only [arm64_norm, hsp, hx19],
     hrest_lt, hcap, hfits_bm⟩
    (by sep_focus)
    (fun _ _ _ _ hex => False.elim (not_satisfies_false_sepConj hex))
    (fun _ _ => wppBudgetPanic_false) ?_
  intro sm hpcm hrunm hspm hcsm hinvm; simp only [CalleeSavedPreserved] at hcsm
  obtain ⟨hx19_m, hx20_m, hx21_m, hx22_m, hx23_m, hx24_m, hx25_m, hx26_m, hx27_m, hx28_m, hfp_m, hvregs_m⟩ := hcsm
  simp (config := { decide := true }) only [arm64_norm, hsp, hx19, hx20, hx21, hx22, hx23, hx24, hx25, hx26, hx27, hx28, hvregs]
    at hpcm hrunm hspm hx19_m hx20_m hx21_m hx22_m hx23_m hx24_m hx25_m hx26_m hx27_m hx28_m hfp_m hvregs_m
  obtain ⟨hnone_core, hsome_core⟩ := bytesMergeEventsCore_effCap iwt v_cap rest hrest_lt
  cases hmb : mergeBytes iwt rest with
  | none =>
    have hnone := hnone_of_mb hmb
    apply CryptoVerification.SpqrV1.Prost.MessageMerge.SepWPp.of_sepWP_lscro (mid := (blkPl_299).base + 548#64) hinvm
    (conv => arg 4; simp only [bytesMerge3RawBudgetSpec, hmb,
      sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc])
    apply SepWP.exists_elim; intro evs_bm
    wp_focus_pure; intro htrm
    wp_focus_pure; intro hevs_bm
    wp_focus_pure; intro hsm0
    have hevs_eq : evs_bm = rustAllocEvents 72 8 := by
      change evs_bm = _ at hevs_bm
      rw [hevs_bm, hnone_core hmb]
    rw [hevs_eq]
    conv => arg 4; simp only [arm64_norm, hsp]
    have hcbnz_err : (sm.readReg64 (Reg.gpr 0#5) == 0#64) = false := beq_eq_false_iff_ne.mpr hsm0
    apply SepWP.fold (skipBelow3_bytesMerge3_entails s0.sp 98 (by decide) (by decide)) (by sep_focus)
    apply SepWP.fold (pointsToBytes_prefix_join hrest_le hrest_suf) (by sep_focus)
    apply SepWP.fold (vecU8CapOkAt_entails_rustBytesVecAt A.repAlloc x.msgPtr rest.length m.next) (by sep_focus)
    apply SepWP.fold (vecU8At_entails_rustBytesVecAt A.repAlloc (x.msgPtr + 0x18#64) v_cap v_ptr m.prev) (by sep_focus)
    (conv => arg 4; rw [memRegion_48_split_96 s0.sp]; simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc])
    apply SepWP.exists_elim; intro v_stk0
    wp_steps_sync_pool ((blkPl_299).base + 548#64)
    simp only [State.setMem_setMem]
    wp_reach; intro hinvm
    refine SepWPp.weaken_pre (by dsimp only [epochDirectionErrFrame, epochDirectionPBAt]; sep_entail)
      (epochDirection_push_err_exit_cl_placed hPushCall hnone hsm0
        (LibsignalBinary.Proofs.SpqrV1.Prost.MessageMerge.EpochDirectionBudgetAux.FitsEnv.epochDirection_push0_after_from hFit_cur)
        (fun evs_p hp => by
          obtain ⟨evs, hevs_post, hst_eq⟩ := hlift_err hmb (rustAllocEvents 72 8 ++ evs_p) (.errFromPush hp)
          exact ⟨evs, hevs_post, (M.stepEvents_append (rustAllocEvents 72 8) evs_p st_cur).symm.trans hst_eq⟩)
        hsp_align
        (by simp only [arm64_norm]) (by simp only [arm64_norm, hrunm]) (by simp only [arm64_norm, hspm])
        (by simp only [arm64_norm, htrm, htr]) (by simp only [arm64_norm, hspm])
        ⟨by simp only [arm64_norm, hx23_m], by simp only [arm64_norm, hx24_m],
         by simp only [arm64_norm, hx25_m], by simp only [arm64_norm, hx26_m],
         by simp only [arm64_norm, hx27_m], by simp only [arm64_norm, hx28_m],
         by simp only [arm64_norm, hvregs_m]⟩ hinvm)
  | some p =>
    rcases p with ⟨v, rest'⟩
    have hrest'_le : rest'.length ≤ rest.length := mergeBytes_length hmb
    obtain ⟨effCap, heff_le, heq_core⟩ := hsome_core v rest' hmb
    apply CryptoVerification.SpqrV1.Prost.MessageMerge.SepWPp.of_sepWP_lscro (mid := (blkPl_299).base + 160#64) hinvm
    (conv => arg 4; simp only [bytesMerge3RawBudgetSpec, hmb,
      sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc])
    apply SepWP.exists_elim; intro evs_bm
    apply SepWP.exists_elim; intro cap'
    apply SepWP.exists_elim; intro ptr'
    wp_focus_pure; intro htrm
    wp_focus_pure; intro hevs_bm
    wp_focus_pure; intro hsm0
    wp_focus_pure; intro hcap'
    have hbm_eff : BytesMerge3EnvCore iwt effCap rest evs_bm := by
      change evs_bm = _ at hevs_bm ⊢
      simpa [← heq_core] using hevs_bm
    have hFit_next : FitsEnv M lim (M.stepEvents evs_bm st_cur) (EpochDirectionLoopEnv rest.length) :=
      fun evs₂ he₂ =>
        ((fitsEvents_append M lim evs_bm evs₂ st_cur).mp
          (hFit_cur (evs_bm ++ evs₂) (.stepBytes iwt effCap rest (Nat.le_refl _) heff_le hbm_eff he₂))).2
    conv => arg 4; simp only [arm64_norm, hsp]
    apply SepWP.fold (skipBelow3_bytesMerge3_entails s0.sp 98 (by decide) (by decide)) (by sep_focus)
    apply SepWP.fold (sliceCursorAfter_join hrest_le hrest_suf hrest'_le) (by sep_focus)
    apply SepWP.fold (vecU8At_entails_vecU8CapOkAt hcap') (by sep_focus)
    apply SepWP.fold (@vecU8CapOkAt_mono A.repAlloc x.msgPtr rest.length rest'.length m.next hrest'_le) (by sep_focus)
    wp_steps_sync_pool ((blkPl_299).base + 160#64)
    simp only [State.setMem_setMem]
    wp_reach; intro hinvm
    refine SepWPp.weaken_pre (by dsimp only [epochDirectionLoopPre, epochDirectionPBCapOkAt]; sep_entail)
      (hcont v rest' evs_bm effCap _ hmb heff_le hbm_eff hFit_next
        (by simp only [arm64_norm]) (by simp only [arm64_norm, hrunm]) (by simp only [arm64_norm, hspm])
        (by simp only [arm64_norm, htrm, htr])
        (by simp only [arm64_norm, hx19_m]) (by simp only [arm64_norm, hx20_m])
        (by simp only [arm64_norm, hx21_m]) (by simp only [arm64_norm, hx22_m])
        ⟨by simp only [arm64_norm, hx23_m], by simp only [arm64_norm, hx24_m],
         by simp only [arm64_norm, hx25_m], by simp only [arm64_norm, hx26_m],
         by simp only [arm64_norm, hx27_m], by simp only [arm64_norm, hx28_m],
         by simp only [arm64_norm, hvregs_m]⟩ hinvm)

/-- Code-loaded placed loop-exit step at `+0x0a0` (`(blkPl_299).base + 160#64`) when `cur.length ≤ limit`. -/
theorem epochDirection_loop_le_exit_cl_placed [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {H : LibsignalHooks}
    {PreEnv PostEnv : EpochDirectionMergeGhost → List AllocEvent → Prop}
    (hFromCall : subroutine_ok ((blkPC_299).rebase (blkPl_299).base H) (lsmpl.base 261)
      (withLsCodeRoLoaded lsmpl (decodeErrorFromBudgetSpec M A lim)))
    {x : EpochDirectionMergeGhost} {st0 st_cur : M.σ} {R : SepProp}
    {s0 s : State} {m : EpochDirectionPB} {cur : List (BitVec 8)} {limit : Nat}
    (hle_lim : cur.length ≤ limit) (hsp_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hcur_le : cur.length ≤ x.bs.length) (hcur_suf : IsDropSuffix x.bs cur) (hlim_lt : limit < 2 ^ 63)
    (hFit_cur : FitsEnv M lim st_cur (EpochDirectionLoopEnv cur.length))
    (hlift_err : (mergeMessage CryptoVerification.LibsignalSpqrV1.EpochDirectionPB.mergeField (codecWireTypeToProto x.wt) x.msg x.bs 98).toOption = none →
      ∀ evs_rem, EpochDirectionLoopEnv cur.length evs_rem →
        ∃ evs, PostEnv x evs ∧ M.stepEvents evs_rem st_cur = M.stepEvents evs st0)
    (hlift_ok : ∀ m_out rest_out,
      (mergeMessage CryptoVerification.LibsignalSpqrV1.EpochDirectionPB.mergeField (codecWireTypeToProto x.wt) x.msg x.bs 98).toOption =
        some (m_out, rest_out) →
      ∀ evs_ok, EpochDirectionOkEnv cur.length (cur.length - limit) evs_ok →
        ∃ evs, PostEnv x evs ∧ M.stepEvents evs_ok st_cur = M.stepEvents evs st0)
    (hres_cur : (mergeMessage CryptoVerification.LibsignalSpqrV1.EpochDirectionPB.mergeField (codecWireTypeToProto x.wt) x.msg x.bs 98).toOption =
      (mergeLoopBin CryptoVerification.LibsignalSpqrV1.EpochDirectionPB.mergeField (cur.length - limit) m cur limit 97).map
        (fun m' => (m', x.bs.drop (x.bs.length - limit))))
    (hpc : s.pc = (blkPl_299).base + 160#64)
    (hrun : s.status = .Running) (hsp : s.sp = s0.sp - 96#64)
    (htr : s.trace = s0.trace) (hx21 : s.readReg64 (Reg.gpr 21#5) = x.slot)
    (hx22 : s.readReg64 (Reg.gpr 22#5) = BitVec.ofNat 64 limit)
    (hcs : HighCalleeSaved s0 s) (hinv : LibsignalCodeRoLoaded lsmpl s.mem) :
    SepWPp ((blkPC_299).rebase (blkPl_299).base H) (s0.readReg64 Reg.lr) s
      (epochDirectionLoopPre A lim st_cur s0 s x.msgPtr x.bufRef x.slot x.ptr m x.bs cur)
      (WppPost (epochDirectionMergeSpecOfEnv A lim PreEnv PostEnv) (x, st0) R s0)
      (WppBudgetPanic (epochDirectionMergeSpecOfEnv A lim PreEnv PostEnv) (x, st0) R s0) := by
  obtain ⟨hx23, hx24, hx25, hx26, hx27, hx28, hvregs⟩ := hcs
  let curPtr : BitVec 64 := x.ptr + BitVec.ofNat 64 (x.bs.length - cur.length)
  by_cases heq_lim : cur.length = limit
  · obtain ⟨hcmp1, hcmp2, hcmp3⟩ := cmp_len_limit_of_eq heq_lim
    have hcur_eq_drop : x.bs.drop (x.bs.length - limit) = cur := by
      rw [← heq_lim]; exact hcur_suf.symm
    have hsome : (mergeMessage CryptoVerification.LibsignalSpqrV1.EpochDirectionPB.mergeField (codecWireTypeToProto x.wt) x.msg x.bs 98).toOption =
        some (m, cur) := by
      rw [hres_cur, mergeLoopBin_eq_limit _ _ _ _ _ _ heq_lim, Option.map_some, hcur_eq_drop]
    obtain ⟨evs, hevs_post, hst_eq⟩ := hlift_ok m cur hsome [] .nil
    have hst_cur_eq : st_cur = M.stepEvents evs st0 := hst_eq
    apply SepWPp.of_sepWP_ret
    unfold WppPost epochDirectionMergeSpecOfEnv
    simp only [hsome, stackAt_skipField3 _ 98 (by decide), epochDirectionLoopPre,
      sliceCursorAfter_eq_split hcur_le hcur_suf, sliceCursorAt,
      sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc, hst_cur_eq, arm64_norm, htr, hsp]
    wp_steps_sync_pool (s0.readReg64 Reg.lr)
    simp only [State.setMem_setMem]
    wp_done
  · have hlt_lim : cur.length < limit := Nat.lt_of_le_of_ne hle_lim heq_lim
    obtain ⟨hcmp1, hcmp2, hcmp3⟩ := cmp_len_limit_of_lt hlt_lim hlim_lt
    have hnone : (mergeMessage CryptoVerification.LibsignalSpqrV1.EpochDirectionPB.mergeField (codecWireTypeToProto x.wt) x.msg x.bs 98).toOption = none := by
      rw [hres_cur, mergeLoopBin_lt_limit _ _ _ _ _ _ hlt_lim, Option.map_none]
    apply CryptoVerification.SpqrV1.Prost.MessageMerge.SepWPp.of_sepWP_lscro (mid := (blkPl_299).base + 104#64) hinv
    conv => arg 4; rw [epochDirectionLoopPre, sliceCursorAfter_eq_split hcur_le hcur_suf,
      sliceCursorAt, memRegion_48_split_96 s0.sp]
    conv => arg 4; simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
    apply SepWP.exists_elim; intro v_stk0
    wp_steps_sync_pool ((blkPl_299).base + 104#64)
    simp only [State.setMem_setMem]
    apply SepWP.fold (pointsTo64_pair_entails_memRegion16 x.slot curPtr (BitVec.ofNat 64 cur.length)) (by sep_focus)
    apply SepWP.fold (pointsToBytes_prefix_join hcur_le hcur_suf) (by sep_focus)
    apply SepWP.fold (epochDirectionPBCapOkAt_entails_epochDirectionPBAt A.repAlloc x.msgPtr cur.length m) (by sep_focus)
    wp_reach; intro hinv
    refine SepWPp.weaken_pre (by dsimp only [epochDirectionErrFrame]; sep_entail)
      (epochDirection_from_err_exit_cl_placed hFromCall hnone
        (by decide : KindNoHeap 0x8000000000000008#64)
        (LibsignalBinary.Proofs.SpqrV1.Prost.MessageMerge.EpochDirectionBudgetAux.FitsEnv.epochDirection_decodeErrorFrom hFit_cur)
        (fun evs_f hf => hlift_err hnone evs_f (hf ▸ .errFrom))
        hsp_align
        (by simp only [arm64_norm]) (by simp only [arm64_norm, hrun]) (by simp only [arm64_norm, hsp])
        (by simp only [arm64_norm, htr])
        ⟨by simp only [arm64_norm, hx23], by simp only [arm64_norm, hx24],
         by simp only [arm64_norm, hx25], by simp only [arm64_norm, hx26],
         by simp only [arm64_norm, hx27], by simp only [arm64_norm, hx28],
         by simp only [arm64_norm, hvregs]⟩ hinv)

/-- Code-loaded placed loop key-decoding step at `+0x0a0` (`(blkPl_299).base + 160#64`) when `¬ cur.length ≤ limit`. -/
theorem epochDirection_decode_key_step_cl_placed [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {H : LibsignalHooks}
    {PreEnv PostEnv : EpochDirectionMergeGhost → List AllocEvent → Prop}
    (hFromCall : subroutine_ok ((blkPC_299).rebase (blkPl_299).base H) (lsmpl.base 261)
      (withLsCodeRoLoaded lsmpl (decodeErrorFromBudgetSpec M A lim)))
    (hVarintCall : subroutine_ok ((blkPC_299).rebase (blkPl_299).base H) (lsmpl.base 291)
      (withLsCodeRoLoaded lsmpl (decodeVarint2Spec A lim)))
    {x : EpochDirectionMergeGhost} {st0 st_cur : M.σ} {R : SepProp}
    {s0 s : State} {m : EpochDirectionPB} {cur : List (BitVec 8)} {limit : Nat}
    (hgt_lim : ¬ cur.length ≤ limit) (hsp_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hcur_le : cur.length ≤ x.bs.length) (hcur_lt : cur.length < 2 ^ 63) (hcur_suf : IsDropSuffix x.bs cur)
    (hFit_cur : FitsEnv M lim st_cur (EpochDirectionLoopEnv cur.length))
    (hlift_err : (mergeMessage CryptoVerification.LibsignalSpqrV1.EpochDirectionPB.mergeField (codecWireTypeToProto x.wt) x.msg x.bs 98).toOption = none →
      ∀ evs_rem, EpochDirectionLoopEnv cur.length evs_rem →
        ∃ evs, PostEnv x evs ∧ M.stepEvents evs_rem st_cur = M.stepEvents evs st0)
    (hres_cur : (mergeMessage CryptoVerification.LibsignalSpqrV1.EpochDirectionPB.mergeField (codecWireTypeToProto x.wt) x.msg x.bs 98).toOption =
      (mergeLoopBin CryptoVerification.LibsignalSpqrV1.EpochDirectionPB.mergeField (cur.length - limit) m cur limit 97).map
        (fun m' => (m', x.bs.drop (x.bs.length - limit))))
    (hcont : ∀ (key : BitVec 64) (iwt : WireType) (rest : List (BitVec 8)) (s' : State),
      decodeVarint cur = some (key, rest) → ¬ 2 ^ 32 ≤ key.toNat →
      CryptoVerification.LibsignalProtoCodec.WireType.ofNat? (key.toNat % 8) = some iwt → ¬ key.toNat / 8 < 1 →
      s'.pc = (blkPl_299).base + 212#64 →
      s'.status = .Running → s'.sp = s0.sp - 96#64 → s'.trace = s0.trace →
      s'.readReg64 (Reg.gpr 0#5) = BitVec.ofNat 64 iwt.toNat →
      s'.readReg64 (Reg.gpr 1#5) = BitVec.ofNat 64 (key.toNat / 8) →
      s'.readReg64 (Reg.gpr 19#5) = x.bufRef → s'.readReg64 (Reg.gpr 20#5) = x.msgPtr →
      s'.readReg64 (Reg.gpr 21#5) = x.slot → s'.readReg64 (Reg.gpr 22#5) = BitVec.ofNat 64 limit →
      HighCalleeSaved s0 s' → LibsignalCodeRoLoaded lsmpl s'.mem →
      SepWPp ((blkPC_299).rebase (blkPl_299).base H) (s0.readReg64 Reg.lr) s'
        (epochDirectionLoopPre A lim st_cur s0 s' x.msgPtr x.bufRef x.slot x.ptr m x.bs rest)
        (WppPost (epochDirectionMergeSpecOfEnv A lim PreEnv PostEnv) (x, st0) R s0)
        (WppBudgetPanic (epochDirectionMergeSpecOfEnv A lim PreEnv PostEnv) (x, st0) R s0))
    (hpc : s.pc = (blkPl_299).base + 160#64)
    (hrun : s.status = .Running) (hsp : s.sp = s0.sp - 96#64)
    (htr : s.trace = s0.trace) (hx19 : s.readReg64 (Reg.gpr 19#5) = x.bufRef)
    (hx20 : s.readReg64 (Reg.gpr 20#5) = x.msgPtr) (hx21 : s.readReg64 (Reg.gpr 21#5) = x.slot)
    (hx22 : s.readReg64 (Reg.gpr 22#5) = BitVec.ofNat 64 limit)
    (hcs : HighCalleeSaved s0 s) (hinv : LibsignalCodeRoLoaded lsmpl s.mem) :
    SepWPp ((blkPC_299).rebase (blkPl_299).base H) (s0.readReg64 Reg.lr) s
      (epochDirectionLoopPre A lim st_cur s0 s x.msgPtr x.bufRef x.slot x.ptr m x.bs cur)
      (WppPost (epochDirectionMergeSpecOfEnv A lim PreEnv PostEnv) (x, st0) R s0)
      (WppBudgetPanic (epochDirectionMergeSpecOfEnv A lim PreEnv PostEnv) (x, st0) R s0) := by
  obtain ⟨hx23, hx24, hx25, hx26, hx27, hx28, hvregs⟩ := hcs
  let curPtr : BitVec 64 := x.ptr + BitVec.ofNat 64 (x.bs.length - cur.length)
  obtain ⟨hcmp1, hcmp2⟩ := cmp_len_limit_of_gt hgt_lim hcur_lt
  apply CryptoVerification.SpqrV1.Prost.MessageMerge.SepWPp.of_sepWP_lscro (mid := lsmpl.base 291) hinv
  conv => arg 4; rw [epochDirectionLoopPre, sliceCursorAfter_eq_split hcur_le hcur_suf,
    sliceCursorAt, skipBelow3_leaf s0.sp 98 (by decide)]; simp only [sepConj_assoc]
  wp_steps_sync_pool (lsmpl.base 291)
  simp only [State.setMem_setMem]
  wp_reach; intro hinv
  refine CryptoVerification.SpqrV1.Prost.MessageMerge.SepWPp.call_frame_lscro (spec := decodeVarint2Spec A lim)
    (x := (⟨x.bufRef, x.slot, curPtr, cur⟩, st_cur))
    (ret_pc := (blkPl_299).base + 180#64) hVarintCall hinv
    (by simp only [arm64_norm]) (by simp only [arm64_norm, hrun])
    (by simp only [State.spAligned, hsp, arm64_norm]; exact hsp_align) (by simp only [arm64_norm])
    rfl ⟨by simp only [arm64_norm, hsp, hx19], hcur_lt, LibsignalBinary.Proofs.SpqrV1.Prost.MessageMerge.EpochDirectionBudgetAux.FitsEnv.epochDirection_decodeVarint2 cur hFit_cur⟩
    (by dsimp only [sliceCursorAt, curPtr]; sep_focus)
    (fun _ _ _ _ hex => False.elim (not_satisfies_false_sepConj hex))
    (fun _ _ => wppBudgetPanic_false) ?_
  intro sm hpcm hrunm hspm hcsm hinvm; simp only [CalleeSavedPreserved] at hcsm
  obtain ⟨hx19_m, hx20_m, hx21_m, hx22_m, hx23_m, hx24_m, hx25_m, hx26_m, hx27_m, hx28_m, hfp_m, hvregs_m⟩ := hcsm
  simp (config := { decide := true }) only [arm64_norm, hsp, hx19, hx20, hx21, hx22, hx23, hx24, hx25, hx26, hx27, hx28, hvregs]
    at hpcm hrunm hspm hx19_m hx20_m hx21_m hx22_m hx23_m hx24_m hx25_m hx26_m hx27_m hx28_m hfp_m hvregs_m
  cases hd : decodeVarint cur with
  | none =>
    have hnone : (mergeMessage CryptoVerification.LibsignalSpqrV1.EpochDirectionPB.mergeField (codecWireTypeToProto x.wt) x.msg x.bs 98).toOption = none := by
      rw [hres_cur, mergeLoopBin_of_decodeVarint_none protoPrefixStep_epochDirectionPB_mergeField hgt_lim hd, Option.map_none]
    apply CryptoVerification.SpqrV1.Prost.MessageMerge.SepWPp.of_sepWP_lscro (mid := (blkPl_299).base + 116#64) hinvm
    (conv => arg 4; simp only [decodeVarint2Spec, decodeVarint2SpecGen, hd,
      sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc])
    apply SepWP.exists_elim; intro evs_dv
    wp_focus_pure; intro hsm0
    wp_focus_pure; intro htrm
    wp_focus_pure; intro hevs_dv
    wp_focus_pure; intro hsm1
    have hevs_eq : evs_dv = rustAllocEvents 72 8 := decodeVarint2Env_of_none hd hevs_dv
    conv => arg 4; simp only [arm64_norm, hsp]
    apply SepWP.fold (skipBelow3_leaf_entails s0.sp 98 (by decide)) (by sep_focus)
    apply SepWP.fold (pointsToBytes_prefix_join hcur_le hcur_suf) (by sep_focus)
    apply SepWP.fold (epochDirectionPBCapOkAt_entails_epochDirectionPBAt A.repAlloc x.msgPtr cur.length m) (by sep_focus)
    wp_steps_sync_pool ((blkPl_299).base + 116#64)
    simp only [State.setMem_setMem]
    wp_reach; intro _hinvm'
    refine SepWPp.weaken_pre (by dsimp only [epochDirectionErrFrame]; sep_entail)
      (epochDirection_err0_ret_exit_placed hnone
        (by
          obtain ⟨evs, hevs_post, hst_eq⟩ := hlift_err hnone evs_dv (hevs_eq ▸ .errFrom)
          exact ⟨evs, hevs_post, hst_eq⟩)
        hsp_align
        (by simp only [arm64_norm]) (by simp only [arm64_norm, hrunm]) (by simp only [arm64_norm, hspm])
        (by simp only [arm64_norm, htrm, htr]) (by simp only [arm64_norm]) hsm1
        ⟨by simp only [arm64_norm, hx23_m], by simp only [arm64_norm, hx24_m],
         by simp only [arm64_norm, hx25_m], by simp only [arm64_norm, hx26_m],
         by simp only [arm64_norm, hx27_m], by simp only [arm64_norm, hx28_m],
         by simp only [arm64_norm, hvregs_m]⟩)
  | some p =>
    rcases p with ⟨key, rest⟩
    have hrest_lt_cur : rest.length < cur.length := decodeVarint_length hd
    have hrest_le_cur : rest.length ≤ cur.length := Nat.le_of_lt hrest_lt_cur
    have hrest_le : rest.length ≤ x.bs.length := Nat.le_trans hrest_le_cur hcur_le
    have hrest_suf : IsDropSuffix x.bs rest :=
      suffix_trans hcur_le hcur_suf hrest_le_cur (decodeVarint_suffix hd)
    let restPtr : BitVec 64 := x.ptr + BitVec.ofNat 64 (x.bs.length - rest.length)
    by_cases hk_ge : 2 ^ 32 ≤ key.toNat
    · have hnone : (mergeMessage CryptoVerification.LibsignalSpqrV1.EpochDirectionPB.mergeField (codecWireTypeToProto x.wt) x.msg x.bs 98).toOption = none := by
        rw [hres_cur, mergeLoopBin_of_key_ge protoPrefixStep_epochDirectionPB_mergeField hgt_lim hd hk_ge, Option.map_none]
      have hshr := key_shr32_of_ge hk_ge
      apply CryptoVerification.SpqrV1.Prost.MessageMerge.SepWPp.of_sepWP_lscro (mid := (blkPl_299).base + 104#64) hinvm
      (conv => arg 4; simp only [decodeVarint2Spec, decodeVarint2SpecGen, hd,
        sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc])
      apply SepWP.exists_elim; intro evs_dv
      wp_focus_pure; rintro ⟨hsm0, hsm1⟩
      wp_focus_pure; intro htrm
      wp_focus_pure; intro hevs_dv
      have hevs_nil : evs_dv = [] := decodeVarint2Env_of_some hd hevs_dv
      subst hevs_nil
      conv => arg 4; dsimp only [LibsignalBinary.Heap.AllocCostModel.stepEvents, List.foldl]; simp only [arm64_norm, hsp]
      apply SepWP.fold (skipBelow3_leaf_entails s0.sp 98 (by decide)) (by sep_focus)
      apply SepWP.fold (sliceCursorAfter_join hcur_le hcur_suf hrest_le_cur) (by sep_focus)
      apply SepWP.fold (epochDirectionPBCapOkAt_entails_epochDirectionPBAt A.repAlloc x.msgPtr cur.length m) (by sep_focus)
      (conv => arg 4; rw [sliceCursorAfter_eq_split hrest_le hrest_suf, sliceCursorAt, memRegion_48_split2 s0.sp]; simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc])
      apply SepWP.exists_elim; intro v_err0; apply SepWP.exists_elim; intro v_err1
      wp_steps_sync_pool ((blkPl_299).base + 104#64)
      simp only [State.setMem_setMem]
      apply SepWP.fold (pointsTo64_pair_entails_memRegion16 x.slot restPtr (BitVec.ofNat 64 rest.length)) (by sep_focus)
      apply SepWP.fold (pointsToBytes_prefix_join hrest_le hrest_suf) (by sep_focus)
      have h40 := pointsTo64_memRegion32_entails_40 s0.sp key
      rw [← bv_sub_add_lit s0.sp 96 8] at h40
      apply SepWP.fold h40 (by sep_focus)
      wp_reach; intro hinvm
      refine SepWPp.weaken_pre (by dsimp only [epochDirectionErrFrame]; sep_entail)
        (epochDirection_from_err_exit_cl_placed hFromCall hnone
          (by decide : KindNoHeap 0x8000000000000004#64)
          (LibsignalBinary.Proofs.SpqrV1.Prost.MessageMerge.EpochDirectionBudgetAux.FitsEnv.epochDirection_decodeErrorFrom hFit_cur)
          (fun evs_f hf => hlift_err hnone evs_f (hf ▸ .errFrom))
          hsp_align
          (by simp only [arm64_norm]) (by simp only [arm64_norm, hrunm]) (by simp only [arm64_norm, hspm])
          (by simp only [arm64_norm, htrm, htr])
          ⟨by simp only [arm64_norm, hx23_m], by simp only [arm64_norm, hx24_m],
           by simp only [arm64_norm, hx25_m], by simp only [arm64_norm, hx26_m],
           by simp only [arm64_norm, hx27_m], by simp only [arm64_norm, hx28_m],
           by simp only [arm64_norm, hvregs_m]⟩ hinvm)
    · have hshr := key_shr32_of_lt hk_ge
      cases hwt : CryptoVerification.LibsignalProtoCodec.WireType.ofNat? (key.toNat % 8) with
      | none =>
        have hnone : (mergeMessage CryptoVerification.LibsignalSpqrV1.EpochDirectionPB.mergeField (codecWireTypeToProto x.wt) x.msg x.bs 98).toOption = none := by
          rw [hres_cur, mergeLoopBin_of_wt_none protoPrefixStep_epochDirectionPB_mergeField hgt_lim hd hk_ge hwt, Option.map_none]
        obtain ⟨hcs1, hcs2⟩ := key_wt_none hwt
        apply CryptoVerification.SpqrV1.Prost.MessageMerge.SepWPp.of_sepWP_lscro (mid := (blkPl_299).base + 104#64) hinvm
        (conv => arg 4; simp only [decodeVarint2Spec, decodeVarint2SpecGen, hd,
          sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc])
        apply SepWP.exists_elim; intro evs_dv
        wp_focus_pure; rintro ⟨hsm0, hsm1⟩
        wp_focus_pure; intro htrm
        wp_focus_pure; intro hevs_dv
        have hevs_nil : evs_dv = [] := decodeVarint2Env_of_some hd hevs_dv
        subst hevs_nil
        conv => arg 4; dsimp only [LibsignalBinary.Heap.AllocCostModel.stepEvents, List.foldl]; simp only [arm64_norm, hsp]
        apply SepWP.fold (skipBelow3_leaf_entails s0.sp 98 (by decide)) (by sep_focus)
        apply SepWP.fold (sliceCursorAfter_join hcur_le hcur_suf hrest_le_cur) (by sep_focus)
        apply SepWP.fold (epochDirectionPBCapOkAt_entails_epochDirectionPBAt A.repAlloc x.msgPtr cur.length m) (by sep_focus)
        (conv => arg 4; rw [sliceCursorAfter_eq_split hrest_le hrest_suf, sliceCursorAt, memRegion_48_split2 s0.sp]; simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc])
        apply SepWP.exists_elim; intro v_err0; apply SepWP.exists_elim; intro v_err1
        wp_steps_sync_pool ((blkPl_299).base + 104#64)
        simp only [State.setMem_setMem]
        apply SepWP.fold (pointsTo64_pair_entails_memRegion16 x.slot restPtr (BitVec.ofNat 64 rest.length)) (by sep_focus)
        apply SepWP.fold (pointsToBytes_prefix_join hrest_le hrest_suf) (by sep_focus)
        have h40 := pointsTo64_memRegion32_entails_40 s0.sp (key &&& 7#64)
        rw [← bv_sub_add_lit s0.sp 96 8] at h40
        apply SepWP.fold h40 (by sep_focus)
        wp_reach; intro hinvm
        refine SepWPp.weaken_pre (by dsimp only [epochDirectionErrFrame]; sep_entail)
          (epochDirection_from_err_exit_cl_placed hFromCall hnone
            (by decide : KindNoHeap 0x8000000000000003#64)
            (LibsignalBinary.Proofs.SpqrV1.Prost.MessageMerge.EpochDirectionBudgetAux.FitsEnv.epochDirection_decodeErrorFrom hFit_cur)
            (fun evs_f hf => hlift_err hnone evs_f (hf ▸ .errFrom))
            hsp_align
            (by simp only [arm64_norm]) (by simp only [arm64_norm, hrunm]) (by simp only [arm64_norm, hspm])
            (by simp only [arm64_norm, htrm, htr])
            ⟨by simp only [arm64_norm, hx23_m], by simp only [arm64_norm, hx24_m],
             by simp only [arm64_norm, hx25_m], by simp only [arm64_norm, hx26_m],
             by simp only [arm64_norm, hx27_m], by simp only [arm64_norm, hx28_m],
             by simp only [arm64_norm, hvregs_m]⟩ hinvm)
      | some iwt =>
        obtain ⟨hcc1, hcc2, hand_wt, hcc1_wt, hcc2_wt⟩ := key_wt_some hwt
        obtain ⟨hw1, hw1_2⟩ := w1_tag_eq hk_ge
        obtain ⟨hw1_zext1, hw1_zext2⟩ := bv32_zeroExtend_ofNat (n := key.toNat / 8) (by omega)
        by_cases hitag0 : key.toNat / 8 < 1
        · have hnone : (mergeMessage CryptoVerification.LibsignalSpqrV1.EpochDirectionPB.mergeField (codecWireTypeToProto x.wt) x.msg x.bs 98).toOption = none := by
            rw [hres_cur, mergeLoopBin_of_tag_zero protoPrefixStep_epochDirectionPB_mergeField hgt_lim hd hk_ge hwt hitag0, Option.map_none]
          have htag_zero : key.toNat / 8 = 0 := by omega
          apply CryptoVerification.SpqrV1.Prost.MessageMerge.SepWPp.of_sepWP_lscro (mid := (blkPl_299).base + 104#64) hinvm
          (conv => arg 4; simp only [decodeVarint2Spec, decodeVarint2SpecGen, hd,
            sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc])
          apply SepWP.exists_elim; intro evs_dv
          wp_focus_pure; rintro ⟨hsm0, hsm1⟩
          wp_focus_pure; intro htrm
          wp_focus_pure; intro hevs_dv
          have hevs_nil : evs_dv = [] := decodeVarint2Env_of_some hd hevs_dv
          subst hevs_nil
          conv => arg 4; dsimp only [LibsignalBinary.Heap.AllocCostModel.stepEvents, List.foldl]; simp only [arm64_norm, hsp]
          apply SepWP.fold (skipBelow3_leaf_entails s0.sp 98 (by decide)) (by sep_focus)
          apply SepWP.fold (sliceCursorAfter_join hcur_le hcur_suf hrest_le_cur) (by sep_focus)
          apply SepWP.fold (epochDirectionPBCapOkAt_entails_epochDirectionPBAt A.repAlloc x.msgPtr cur.length m) (by sep_focus)
          (conv => arg 4; rw [sliceCursorAfter_eq_split hrest_le hrest_suf, sliceCursorAt, memRegion_48_split_96 s0.sp]; simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc])
          apply SepWP.exists_elim; intro v_err0
          wp_steps_sync_pool ((blkPl_299).base + 104#64)
          simp only [State.setMem_setMem]
          apply SepWP.fold (pointsTo64_pair_entails_memRegion16 x.slot restPtr (BitVec.ofNat 64 rest.length)) (by sep_focus)
          apply SepWP.fold (pointsToBytes_prefix_join hrest_le hrest_suf) (by sep_focus)
          wp_reach; intro hinvm
          refine SepWPp.weaken_pre (by dsimp only [epochDirectionErrFrame]; sep_entail)
            (epochDirection_from_err_exit_cl_placed hFromCall hnone
              (by decide : KindNoHeap 0x8000000000000005#64)
              (LibsignalBinary.Proofs.SpqrV1.Prost.MessageMerge.EpochDirectionBudgetAux.FitsEnv.epochDirection_decodeErrorFrom hFit_cur)
              (fun evs_f hf => hlift_err hnone evs_f (hf ▸ .errFrom))
              hsp_align
              (by simp only [arm64_norm]) (by simp only [arm64_norm, hrunm]) (by simp only [arm64_norm, hspm])
              (by simp only [arm64_norm, htrm, htr])
              ⟨by simp only [arm64_norm, hx23_m], by simp only [arm64_norm, hx24_m],
               by simp only [arm64_norm, hx25_m], by simp only [arm64_norm, hx26_m],
               by simp only [arm64_norm, hx27_m], by simp only [arm64_norm, hx28_m],
               by simp only [arm64_norm, hvregs_m]⟩ hinvm)
        · obtain ⟨hcbz_tag1, hcbz_tag2⟩ := tag_cbz_false hk_ge hitag0
          have hcbz_tag64 : (BitVec.ofNat 64 (key.toNat / 8) == 0#64) = false := by
            rw [beq_eq_false_iff_ne]; intro h; have h1 := congrArg BitVec.toNat h
            simp only [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega : key.toNat / 8 < 2 ^ 64)] at h1; omega
          apply CryptoVerification.SpqrV1.Prost.MessageMerge.SepWPp.of_sepWP_lscro (mid := (blkPl_299).base + 212#64) hinvm
          (conv => arg 4; simp only [decodeVarint2Spec, decodeVarint2SpecGen, hd,
            sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc])
          apply SepWP.exists_elim; intro evs_dv
          wp_focus_pure; rintro ⟨hsm0, hsm1⟩
          wp_focus_pure; intro htrm
          wp_focus_pure; intro hevs_dv
          have hevs_nil : evs_dv = [] := decodeVarint2Env_of_some hd hevs_dv
          subst hevs_nil
          conv => arg 4; dsimp only [LibsignalBinary.Heap.AllocCostModel.stepEvents, List.foldl]; simp only [arm64_norm, hsp]
          apply SepWP.fold (skipBelow3_leaf_entails s0.sp 98 (by decide)) (by sep_focus)
          apply SepWP.fold (sliceCursorAfter_join hcur_le hcur_suf hrest_le_cur) (by sep_focus)
          apply SepWP.fold (epochDirectionPBCapOkAt_mono hrest_le_cur) (by sep_focus)
          wp_steps_sync_pool ((blkPl_299).base + 212#64)
          simp only [State.setMem_setMem]
          wp_reach; intro hinvm
          refine SepWPp.weaken_pre (by dsimp only [epochDirectionLoopPre]; sep_entail)
            (hcont key iwt rest _ hd hk_ge hwt hitag0
              (by simp only [arm64_norm]) (by simp only [arm64_norm, hrunm]) (by simp only [arm64_norm, hspm])
              (by simp only [arm64_norm, htrm, htr])
              (by simp only [arm64_norm, hsm1, hand_wt])
              (by simp only [arm64_norm, hsm1, hw1, hw1_2, hw1_zext1, hw1_zext2])
              (by simp only [arm64_norm, hx19_m]) (by simp only [arm64_norm, hx20_m])
              (by simp only [arm64_norm, hx21_m]) (by simp only [arm64_norm, hx22_m])
              ⟨by simp only [arm64_norm, hx23_m], by simp only [arm64_norm, hx24_m],
               by simp only [arm64_norm, hx25_m], by simp only [arm64_norm, hx26_m],
               by simp only [arm64_norm, hx27_m], by simp only [arm64_norm, hx28_m],
               by simp only [arm64_norm, hvregs_m]⟩ hinvm)

end LibsignalBinary.Proofs.SpqrV1.Prost.MessageMerge.EpochDirectionBudgetSteps
