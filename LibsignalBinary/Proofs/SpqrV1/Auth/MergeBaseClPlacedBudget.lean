/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SpqrV1.Auth.MergePlacedBudget
public import LibsignalBinary.Proofs.SpqrV1.Prost.MessageMerge.ChunkedDefsBudget
public meta import LibsignalBinary.Proofs.Common.SharedHelpers -- shake: keep
public meta import LibsignalBinary.Proofs.Placed.BudgetPoolSync -- shake: keep
public meta import LibsignalBinary.Proofs.Placed.BudgetVmSteps -- shake: keep
import LibsignalBinary.Proofs.Common.SharedHelpers
import LibsignalBinary.Proofs.E2E.Pqxdh.ResponderStore.ResponderStoreCodeSym
import LibsignalBinary.Proofs.ProtoCodecRoundTrip
import LibsignalBinary.Proofs.SpqrV1.Unchunked.UnchunkedCodeSym
import LibsignalBinary.Proofs.TripleRatchet.Prost.BytesMerge.Phase1
import ProofLib.SepLogic.WPp
import LibsignalBinary.Specifications.LibsignalSpqrV1.Wire -- shake: keep

/-!
# Budget-Threaded Relocatable Proof of `Authenticator::merge` (Block 295)

Verifies `prost::encoding::message::merge::<Authenticator, &mut &[u8]> [local#2]`
(block 295) against `withLsCodeRoLoaded lsmpl (MergeBaseBudget.authMergeSpec A lim)`
using `ChunkedDefsBudget.decodeErrorPushMergeBudgetSpec` on block 257.
-/

@[expose] public section

set_option autoImplicit false

namespace LibsignalBinary.Proofs.SpqrV1.Auth.MergeBaseClPlacedBudget

open Arm64 ProofLib SepProp
open scoped CryptoVerification
open scoped CryptoVerification.CodeLayout
open CryptoVerification (LibsignalHooks LibsignalPlacement blkPC_295 blkPl_295 lsmpl withLsCodeLoaded)
open CryptoVerification.RustHeap (vecU8At)
open CryptoVerification.LibsignalProtoCodec
  (WireType decodeVarint decodeVarint_length mergeBytes skipField skip_length)
open CryptoVerification.LibsignalTripleRatchet
  (KindNoHeap LibsignalCodeRoLoaded decodeErrorAtStackLen decodeErrorHookStack
   extract_withLsCodeRoLoaded subroutine_ok_withLsCodeRoLoaded_of_withLsCodeLoaded
   withLsCodeRoLoaded)
open CryptoVerification.LibsignalTripleRatchet.Prost
  (BytesMergeCapOk BytesMergeGhost HighCalleeSaved IsDropSuffix SkipFieldGhost
   bytesMergeCapOk_mono decodeVarint_suffix itag_beq_tag_false
   pointsTo64_pair_entails_memRegion16 pointsToBytes_prefix_join
   sf_truncate32_ofNat64 skip_suffix sliceCursorAfter sliceCursorAfter_eq_split
   sliceCursorAfter_join sliceCursorAt suffix_trans ule_len_of_ge ule_len_of_lt)
open CryptoVerification.LibsignalTripleRatchet.Prost.BytesMergeFacts
  (truncate32_zeroExtend64_and_255_eq)
open CryptoVerification.SpqrV1.Varint
  (decodeVarint2Stack skipBelow3 skipBelow3_err skipBelow3_err_entails skipBelow3_leaf
   skipBelow3_leaf_entails stackAt_skipField3)
open CryptoVerification.SpqrV1.ProtoRepr (authenticatorPBAt)
open CryptoVerification.SpqrV1.Prost.BytesMerge
  (proto_decodeVarint_toOption proto_mergeBytes_toOption)
open CryptoVerification.SpqrV1.Prost.MessageMerge
  (SepWPp.call_frame_lscro SepWPp.of_sepWP_lscro bv_len_sub_limit codecWireTypeToProto
   decodeErrorWith_one_entails_le1 memRegion_48_wtErr96 mergeLoopBin mergeLoopBin_lt_limit
   mergeLoopBin_of_key_ok mergeMessageBin mergeMessageBin_eq_proto_mergeMessage
   pointsTo64_memRegion40_entails_48 protoPrefixStep_mergeBytes
   protoPrefixStep_protoAuthenticator_mergeField protoWireTypeToCodec_codecWireTypeToProto
   skipBelow3_bytesMerge3 skipBelow3_bytesMerge3_entails wtErr96_entails_memRegion40
   wt_beq_two_of_lengthDelimited wt_beq_two_of_ne_lengthDelimited)
open CryptoVerification.LibsignalSpqrV1 (ProtoAuthenticator)
open CryptoVerification.LibsignalSpqrV1.Proto (mergeMessage)
open CryptoVerification.SpqrV1.Auth
  (AuthMergeGhost SepWPp.pure_elim2 WppPost authMergeStack
   authenticatorPBAt_entails_exists authenticatorPBCapAt
   authenticatorPBCapAt_entails_authenticatorPBAt authenticatorPBCapAt_mono bv64_add_zero
   bv64_sub_zero memRegion_48_split_96 mergeBytes_length mergeBytes_suffix
   protoAuthenticator_mergeField_other protoAuthenticator_mergeField_tag1
   protoAuthenticator_mergeField_tag2 setWidth8_ofNat64_wt)
open LibsignalBinary.Heap
  (AllocCostModel AllocEvent BudgetLimits FitsEnv RustCliAllocBudget)
open LibsignalBinary.Heap.SpecBudget
  (DecodeErrorFromEnv decodeErrorFromBudgetSpec)
open LibsignalBinary.Proofs.Placed.BudgetPoolSync (hooksException sepWP_seg_ls_vm)
open LibsignalBinary.Proofs.SpqrV1.Auth.MergeBaseBudget
  (AuthBytesMerge3EnvCore AuthMergeEnv AuthMergeLoopEnv AuthMergePostEnv
   DecodeErrorPushBoundedEnv authMergeSpec authMergeSpecOfEnv)
open LibsignalBinary.Proofs.SpqrV1.Auth.MergePlacedBudget
  (SepWPp.to_subroutineOutcome_auth_placed auth_decode_key_step_cl_placed auth_loop_le_exit_cl_placed)
open LibsignalBinary.Proofs.SpqrV1.Auth.MergePlacedBudgetAux
  (authBudgetErrFrame authBudgetLoopPre auth_err0_ret_exit_placed auth_from_err_exit_cl_placed
   auth_skip_step_cl_placed stepEvents_append)
open LibsignalBinary.Proofs.SpqrV1.Prost.MessageMerge.ChunkedDefsBudget
  (DecodeErrorPushMergeEnv decodeErrorPushMergeBudgetSpec mergeBytes_len_bound)
open LibsignalBinary.Proofs.SpqrV1.Prost.MessageMerge.PolyCommonBudget
  (BytesMerge3Env WppBudgetPanic bytesMerge3RawBudgetSpec wppBudgetPanic_false)
open LibsignalBinary.Proofs.SpqrV1.Varint.DecodeVarint2Budget
  (DecodeVarint2Env decodeVarint2Spec decodeVarint2SpecGen)
open LibsignalBinary.Proofs.SpqrV1.Varint.SkipField3Budget (SkipField3Env skipField3Spec)
open LibsignalBinary.Proofs.TripleRatchet.Prost.DefsBudget
  (DecodeVarintSliceEnv SkipFieldEnv decodeVarintSliceEvents skipFieldEventsCore)
open LibsignalBinary.Proofs.TripleRatchet.Prost.MergeDefsBudget (bytesMergeEventsCore)

private theorem sp_setMem_pre (s : State) (m : Memory) : (s.setMem m).sp = s.sp := by
  cases s; rfl
private theorem pc_setMem_pre (s : State) (m : Memory) : (s.setMem m).pc = s.pc := by
  cases s; rfl
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

attribute [local irreducible] Program.fetch Program.externAt?
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero
attribute [local simp, local arm64_norm] bv64_sub_zero bv64_add_zero
attribute [local arm64_norm ↓, local wp_norm ↓]
  sp_setMem_pre pc_setMem_pre status_setMem_pre pstate_setMem_pre trace_setMem_pre
  readReg64_setMem_pre readReg32_setMem_pre readReg_setMem_pre calleeSavedVRegs_setMem_pre

/-! ## `AuthMergeLoopEnv` Containment and Prefix-Shrinking Lemmas -/

private theorem decodeVarint2Env_eq_nil {bs : List (BitVec 8)} {v : BitVec 64}
    {rest : List (BitVec 8)} {evs : List AllocEvent}
    (hd : decodeVarint bs = some (v, rest)) (hdv : DecodeVarint2Env bs evs) :
    evs = [] := by
  change DecodeVarintSliceEnv bs evs at hdv
  simpa [DecodeVarintSliceEnv, decodeVarintSliceEvents, hd] using hdv

private theorem authMergeLoopEnv_of_decodeErrorFrom {evs : List AllocEvent}
    (h : DecodeErrorFromEnv evs) :
    AuthMergeLoopEnv 1 0 evs := by
  rw [h]
  simpa using AuthMergeLoopEnv.errFrom (errRem := 0) (byteRem := 0) .nil

private theorem authMergeLoopEnv_of_decodeErrorPush0 {evs : List AllocEvent}
    (h : DecodeErrorPushMergeEnv 0 evs) :
    AuthMergeLoopEnv 1 0 evs := by
  have hb : DecodeErrorPushBoundedEnv 0 evs := h
  simpa using AuthMergeLoopEnv.errPush (errRem := 0) (byteRem := 0) (Nat.zero_le 1) hb .nil

private theorem authMergeLoopEnv_of_decodeVarint2 {bs : List (BitVec 8)} {evs : List AllocEvent}
    (hdv : DecodeVarint2Env bs evs) :
    AuthMergeLoopEnv 1 0 evs := by
  change DecodeVarintSliceEnv bs evs at hdv
  rw [hdv]; unfold decodeVarintSliceEvents
  cases decodeVarint bs
  · exact authMergeLoopEnv_of_decodeErrorFrom rfl
  · exact .nil

private theorem authMergeLoopEnv_of_skipField3 {x : SkipFieldGhost} {evs : List AllocEvent}
    (hsf : SkipField3Env x evs) :
    AuthMergeLoopEnv 1 0 evs := by
  change SkipFieldEnv x evs at hsf
  rw [hsf]; unfold skipFieldEventsCore
  cases skipField (2 * x.bs.length + 2) x.depth x.tag x.wt x.bs
  · exact authMergeLoopEnv_of_decodeErrorFrom rfl
  · exact .nil

private theorem authMergeLoopEnv_of_bytesMerge3_none {x : BytesMergeGhost} {evs : List AllocEvent}
    (hmb : mergeBytes x.wt x.bs = none) (hbm : BytesMerge3Env x evs) :
    AuthMergeLoopEnv 1 0 evs := by
  change evs = bytesMergeEventsCore x.wt x.valCap x.bs at hbm
  rw [hbm]; simp only [bytesMergeEventsCore, hmb]
  exact authMergeLoopEnv_of_decodeErrorFrom rfl

private theorem authMergeLoopEnv_of_bytesMerge3_some {x : BytesMergeGhost}
    {v rest' : List (BitVec 8)} {evs : List AllocEvent}
    (hmb : mergeBytes x.wt x.bs = some (v, rest')) (hbm : BytesMerge3Env x evs) :
    AuthMergeLoopEnv 0 (x.bs.length - rest'.length) evs := by
  have hbound : rest'.length + v.length + 1 ≤ x.bs.length := mergeBytes_len_bound hmb
  let s : List (BitVec 8) := x.bs.take (x.bs.length - rest'.length)
  let a : List (BitVec 8) := x.bs.drop (x.bs.length - rest'.length)
  have hs_app : s ++ a = x.bs := List.take_append_drop (x.bs.length - rest'.length) x.bs
  have hs_len : s.length = x.bs.length - rest'.length := List.length_take_of_le (by omega)
  have ha_len : a.length = rest'.length := by
    dsimp only [a]
    rw [List.length_drop]
    omega
  have hpm0 :
      (CryptoVerification.LibsignalSpqrV1.Proto.mergeBytes (codecWireTypeToProto x.wt) x.bs).toOption =
        some (v, rest') := by
    rw [proto_mergeBytes_toOption, protoWireTypeToCodec_codecWireTypeToProto]
    exact hmb
  have hpm :
      CryptoVerification.LibsignalSpqrV1.Proto.mergeBytes (codecWireTypeToProto x.wt) (s ++ a) =
        .ok (v, rest') := by
    rw [hs_app]
    rcases h : CryptoVerification.LibsignalSpqrV1.Proto.mergeBytes (codecWireTypeToProto x.wt) x.bs with _ | p
    · rw [h] at hpm0; nomatch hpm0
    · rw [h] at hpm0; injection hpm0 with hp; subst hp; rfl
  obtain ⟨r', _hr'_eq, _hr'_le, hpm_s⟩ :=
    (protoPrefixStep_mergeBytes (codecWireTypeToProto x.wt)).ok_of_append_ok_of_le hpm (by omega)
  have hmb_s : mergeBytes x.wt s = some (v, r') := by
    rw [← protoWireTypeToCodec_codecWireTypeToProto x.wt, ← proto_mergeBytes_toOption, hpm_s]
    rfl
  have hcore_s : AuthBytesMerge3EnvCore x.wt x.valCap s evs := by
    change evs = bytesMergeEventsCore x.wt x.valCap x.bs at hbm
    change evs = bytesMergeEventsCore x.wt x.valCap s
    rw [hbm]
    simp only [bytesMergeEventsCore, hmb, hmb_s]
  simpa using
    AuthMergeLoopEnv.bytesStep (errRem := 0) (byteRem := x.bs.length - rest'.length) (byteRem' := 0)
      x.wt x.valCap s v r' hmb_s (by omega) (by omega) hcore_s .nil

private theorem fitsEnv_bytesMerge3_of_authMergeLoop {M : AllocCostModel} {lim : BudgetLimits}
    {st : M.σ} {errRem remLen : Nat} {x : BytesMergeGhost}
    (hlen : x.bs.length ≤ remLen)
    (hFit : FitsEnv M lim st (AuthMergeLoopEnv (errRem + 1) remLen)) :
    FitsEnv M lim st (BytesMerge3Env x) := by
  intro evs hbm
  cases hmb : mergeBytes x.wt x.bs with
  | none =>
    exact hFit evs ((authMergeLoopEnv_of_bytesMerge3_none hmb hbm).mono (by omega) (by omega))
  | some p =>
    rcases p with ⟨v, rest'⟩
    exact hFit evs ((authMergeLoopEnv_of_bytesMerge3_some hmb hbm).mono (by omega) (by omega))

/-! ## Block 295 Error-Push Exit and Tag 1/2 Steps -/

set_option maxRecDepth 200000 in
set_option maxHeartbeats 400000 in
set_option linter.unusedSimpArgs false in
theorem auth_push_err_exit_merge_cl_placed [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {H : LibsignalHooks}
    {PreEnv PostEnv : AuthMergeGhost → List AllocEvent → Prop}
    (hPushCall : subroutine_ok ((blkPC_295).rebase (blkPl_295).base H) (lsmpl.base 257)
      (withLsCodeRoLoaded lsmpl (decodeErrorPushMergeBudgetSpec M A lim)))
    {x : AuthMergeGhost} {st0 st_cur : M.σ} {R : SepProp} {s0 s : State}
    {m : ProtoAuthenticator} {err : BitVec 64}
    (hnone : (mergeMessage ProtoAuthenticator.mergeField (codecWireTypeToProto x.wt) x.msg x.bs 97).toOption = none)
    (herr : err ≠ 0#64)
    (hfits_push : FitsEnv M lim st_cur (DecodeErrorPushMergeEnv 0))
    (hevs_push : ∀ evs_p, DecodeErrorPushMergeEnv 0 evs_p →
      ∃ evs, PostEnv x evs ∧ M.stepEvents evs_p st_cur = M.stepEvents evs st0)
    (hsp_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hpc : s.pc = (blkPl_295).base + 436#64)
    (hrun : s.status = .Running) (hsp : s.sp = s0.sp - 96#64)
    (htr : s.trace = s0.trace) (hx0 : s.readReg64 (Reg.gpr 0#5) = s0.sp - 96#64)
    (hcs : HighCalleeSaved s0 s) (hinv : LibsignalCodeRoLoaded lsmpl s.mem) :
    SepWPp ((blkPC_295).rebase (blkPl_295).base H) (s0.readReg64 Reg.lr) s
      (((s0.sp - 96#64) ↦₆₄ err) ∗ decodeErrorAtStackLen A.repAlloc err 0 ∗
        memRegion (s0.sp - 88#64) 40 ∗ skipBelow3 s0.sp 97 ∗
        authBudgetErrFrame A lim st_cur s0 s x.msgPtr x.bufRef x.slot x.ptr m x.bs)
      (WppPost (authMergeSpecOfEnv A lim PreEnv PostEnv) (x, st0) R s0)
      (WppBudgetPanic (authMergeSpecOfEnv A lim PreEnv PostEnv) (x, st0) R s0) := by
  obtain ⟨hx23, hx24, hx25, hx26, hx27, hx28, hvregs⟩ := hcs
  apply SepWPp.of_sepWP_lscro (mid := lsmpl.base 257) hinv
  conv => arg 4; rw [skipBelow3_err s0.sp 97 (by decide), authBudgetErrFrame]; simp only [sepConj_assoc]
  wp_steps_sync_pool (lsmpl.base 257)
  simp only [State.setMem_setMem]
  wp_reach; intro hinv
  refine SepWPp.call_frame_lscro (spec := decodeErrorPushMergeBudgetSpec M A lim)
    (x := (s0.sp - 96#64, err, 0, st_cur))
    (ret_pc := (blkPl_295).base + 440#64) hPushCall hinv
    (by simp only [arm64_norm]) (by simp only [arm64_norm, hrun])
    (by simp only [State.spAligned, hsp, arm64_norm]; exact hsp_align)
    (by simp only [arm64_norm])
    rfl ⟨by simp only [arm64_norm, hsp, hx0], by decide, hfits_push⟩ (by sep_focus)
    (fun _ _ _ _ hex => False.elim (not_satisfies_false_sepConj hex))
    (fun _ _ => wppBudgetPanic_false) ?_
  intro sm hpcm hrunm hspm hcsm _hinvm
  simp only [CalleeSavedPreserved] at hcsm
  obtain ⟨hx19, hx20, hx21, hx22, hx23_m, hx24_m, hx25_m, hx26_m, hx27_m, hx28_m, hfp, hvregs_m⟩ := hcsm
  simp (config := { decide := true }) only [arm64_norm, hsp, hx23, hx24, hx25, hx26, hx27, hx28, hvregs]
    at hpcm hspm hx19 hx20 hx21 hx22 hx23_m hx24_m hx25_m hx26_m hx27_m hx28_m hfp hvregs_m
  apply SepWPp.of_sepWP_ret
  unfold WppPost authMergeSpecOfEnv
  simp only [decodeErrorPushMergeBudgetSpec, hnone, authMergeStack, stackAt_skipField3 _ 97 (by decide),
    sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc, htr, hsp, hspm]
  apply SepWP.exists_elim; intro evs_p
  wp_focus_pure; intro htrm
  wp_focus_pure; intro hevs_p
  obtain ⟨evs, hevs_post, hst_eq⟩ := hevs_push evs_p hevs_p
  conv => arg 4; simp only [hst_eq, arm64_norm]
  apply SepWP.fold (skipBelow3_err_entails s0.sp 97 (by decide)) (by sep_focus)
  wp_steps_sync_pool (s0.readReg64 Reg.lr)
  simp only [State.setMem_setMem]
  apply SepWP.fold (decodeErrorWith_one_entails_le1 A.repAlloc err) (by sep_focus)
  apply SepWP.fold (authenticatorPBAt_entails_exists A.repAlloc x.msgPtr m) (by sep_focus)
  apply SepWP.fold (pointsTo64_memRegion40_entails_48 s0.sp err) (by sep_focus)
  wp_done

set_option maxRecDepth 200000 in
set_option maxHeartbeats 400000 in
set_option linter.unusedSimpArgs false in
theorem auth_tag1_step_merge_cl_placed [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {H : LibsignalHooks}
    {PreEnv PostEnv : AuthMergeGhost → List AllocEvent → Prop}
    (hPushCall : subroutine_ok ((blkPC_295).rebase (blkPl_295).base H) (lsmpl.base 257)
      (withLsCodeRoLoaded lsmpl (decodeErrorPushMergeBudgetSpec M A lim)))
    (hBytesCall : subroutine_ok ((blkPC_295).rebase (blkPl_295).base H) (lsmpl.base 290)
      (withLsCodeRoLoaded lsmpl (bytesMerge3RawBudgetSpec A lim)))
    {x : AuthMergeGhost} {st0 st_cur : M.σ} {R : SepProp} {s0 s : State}
    {m : ProtoAuthenticator} {rest : List (BitVec 8)} {iwt : WireType} {limit : Nat}
    (hsp_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hrest_le : rest.length ≤ x.bs.length)
    (hrest_lt : rest.length < 2 ^ 63)
    (hrest_suf : IsDropSuffix x.bs rest)
    (hfits_bm : ∀ cap1 ptr1 : BitVec 64, BytesMergeCapOk cap1 rest.length →
      FitsEnv M lim st_cur
        (BytesMerge3Env ⟨iwt, x.msgPtr, cap1, ptr1, m.rootKey, x.bufRef, x.slot,
          x.ptr + BitVec.ofNat 64 (x.bs.length - rest.length), rest⟩))
    (hfits_push : ∀ (cap1 ptr1 : BitVec 64) (evs_bm : List AllocEvent),
      mergeBytes iwt rest = none →
      BytesMerge3Env ⟨iwt, x.msgPtr, cap1, ptr1, m.rootKey, x.bufRef, x.slot,
        x.ptr + BitVec.ofNat 64 (x.bs.length - rest.length), rest⟩ evs_bm →
      FitsEnv M lim (M.stepEvents evs_bm st_cur) (DecodeErrorPushMergeEnv 0))
    (hevs_bm_err : ∀ (cap1 ptr1 : BitVec 64) (evs_bm evs_p : List AllocEvent),
      mergeBytes iwt rest = none →
      BytesMerge3Env ⟨iwt, x.msgPtr, cap1, ptr1, m.rootKey, x.bufRef, x.slot,
        x.ptr + BitVec.ofNat 64 (x.bs.length - rest.length), rest⟩ evs_bm →
      DecodeErrorPushMergeEnv 0 evs_p →
      ∃ evs, PostEnv x evs ∧ M.stepEvents evs_p (M.stepEvents evs_bm st_cur) = M.stepEvents evs st0)
    (hnone_of_mb : mergeBytes iwt rest = none →
      (mergeMessage ProtoAuthenticator.mergeField (codecWireTypeToProto x.wt) x.msg x.bs 97).toOption = none)
    (hcont : ∀ (cap1 ptr1 : BitVec 64) (v rest' : List (BitVec 8))
      (evs_bm : List AllocEvent) (s' : State),
      mergeBytes iwt rest = some (v, rest') →
      BytesMerge3Env ⟨iwt, x.msgPtr, cap1, ptr1, m.rootKey, x.bufRef, x.slot,
        x.ptr + BitVec.ofNat 64 (x.bs.length - rest.length), rest⟩ evs_bm →
      s'.pc = (blkPl_295).base + 160#64 →
      s'.status = .Running → s'.sp = s0.sp - 96#64 → s'.trace = s0.trace →
      s'.readReg64 (Reg.gpr 19#5) = x.bufRef → s'.readReg64 (Reg.gpr 20#5) = x.msgPtr →
      s'.readReg64 (Reg.gpr 21#5) = x.slot → s'.readReg64 (Reg.gpr 22#5) = BitVec.ofNat 64 limit →
      HighCalleeSaved s0 s' → LibsignalCodeRoLoaded lsmpl s'.mem →
      SepWPp ((blkPC_295).rebase (blkPl_295).base H) (s0.readReg64 Reg.lr) s'
        (authBudgetLoopPre A lim (M.stepEvents evs_bm st_cur) s0 s'
          x.msgPtr x.bufRef x.slot x.ptr { m with rootKey := v } x.bs rest')
        (WppPost (authMergeSpecOfEnv A lim PreEnv PostEnv) (x, st0) R s0)
        (WppBudgetPanic (authMergeSpecOfEnv A lim PreEnv PostEnv) (x, st0) R s0))
    (hpc : s.pc = (blkPl_295).base + 252#64)
    (hrun : s.status = .Running) (hsp : s.sp = s0.sp - 96#64)
    (htr : s.trace = s0.trace) (hx0 : s.readReg64 (Reg.gpr 0#5) = BitVec.ofNat 64 iwt.toNat)
    (hx19 : s.readReg64 (Reg.gpr 19#5) = x.bufRef) (hx20 : s.readReg64 (Reg.gpr 20#5) = x.msgPtr)
    (hx21 : s.readReg64 (Reg.gpr 21#5) = x.slot) (hx22 : s.readReg64 (Reg.gpr 22#5) = BitVec.ofNat 64 limit)
    (hcs : HighCalleeSaved s0 s) (hinv : LibsignalCodeRoLoaded lsmpl s.mem) :
    SepWPp ((blkPC_295).rebase (blkPl_295).base H) (s0.readReg64 Reg.lr) s
      (authBudgetLoopPre A lim st_cur s0 s x.msgPtr x.bufRef x.slot x.ptr m x.bs rest)
      (WppPost (authMergeSpecOfEnv A lim PreEnv PostEnv) (x, st0) R s0)
      (WppBudgetPanic (authMergeSpecOfEnv A lim PreEnv PostEnv) (x, st0) R s0) := by
  obtain ⟨hx23, hx24, hx25, hx26, hx27, hx28, hvregs⟩ := hcs
  let restPtr : BitVec 64 := x.ptr + BitVec.ofNat 64 (x.bs.length - rest.length)
  conv =>
    arg 4
    rw [authBudgetLoopPre, authenticatorPBCapAt, sliceCursorAfter_eq_split hrest_le hrest_suf,
      skipBelow3_bytesMerge3 s0.sp 97 (by decide) (by decide)]
    simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
  apply SepWPp.exists_elim; intro cap2; apply SepWPp.exists_elim; intro ptr2
  apply SepWPp.exists_elim; intro cap1; apply SepWPp.exists_elim; intro ptr1
  apply CryptoVerification.SpqrV1.Auth.SepWPp.pure_elim; intro hcap1; apply SepWPp.pure_elim2; intro hcap2
  apply SepWPp.of_sepWP_lscro (mid := lsmpl.base 290) hinv
  wp_steps_sync_pool (lsmpl.base 290)
  simp only [State.setMem_setMem]
  wp_reach; intro hinv
  refine SepWPp.call_frame_lscro (spec := bytesMerge3RawBudgetSpec A lim)
    (x := (⟨iwt, x.msgPtr, cap1, ptr1, m.rootKey, x.bufRef, x.slot, restPtr, rest⟩, st_cur))
    (ret_pc := (blkPl_295).base + 264#64) hBytesCall hinv
    (by simp only [arm64_norm]) (by simp only [arm64_norm, hrun])
    (by simp only [State.spAligned, hsp, arm64_norm]; exact hsp_align)
    (by simp only [arm64_norm])
    rfl
    ⟨by simp only [arm64_norm, hsp, hx0, setWidth8_ofNat64_wt],
     by simp only [arm64_norm, hsp, hx20],
     by simp only [arm64_norm, hsp, hx19],
     hrest_lt, hcap1, hfits_bm cap1 ptr1 hcap1⟩
    (by sep_focus)
    (fun _ _ _ _ hex => False.elim (not_satisfies_false_sepConj hex))
    (fun _ _ => wppBudgetPanic_false) ?_
  intro sm hpcm hrunm hspm hcsm hinvm
  simp only [CalleeSavedPreserved] at hcsm
  obtain ⟨hx19_m, hx20_m, hx21_m, hx22_m, hx23_m, hx24_m, hx25_m, hx26_m, hx27_m, hx28_m, hfp_m, hvregs_m⟩ := hcsm
  simp (config := { decide := true }) only [arm64_norm, hsp, hx19, hx20, hx21, hx22, hx23, hx24, hx25, hx26, hx27, hx28, hvregs]
    at hpcm hrunm hspm hx19_m hx20_m hx21_m hx22_m hx23_m hx24_m hx25_m hx26_m hx27_m hx28_m hfp_m hvregs_m
  cases hmb : mergeBytes iwt rest with
  | none =>
    have hnone := hnone_of_mb hmb
    apply SepWPp.of_sepWP_lscro (mid := (blkPl_295).base + 436#64) hinvm
    (conv => arg 4; simp only [bytesMerge3RawBudgetSpec, hmb, memRegion_48_split_96 s0.sp,
      sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc])
    apply SepWP.exists_elim; intro v_stk0
    apply SepWP.exists_elim; intro evs_bm
    wp_focus_pure; intro htrm
    wp_focus_pure; intro hevs_bm
    wp_focus_pure; intro hsm0
    conv => arg 4; simp only [arm64_norm, hsp]
    have hcbnz : (sm.readReg64 (Reg.gpr 0#5) == 0#64) = false := beq_eq_false_iff_ne.mpr hsm0
    apply SepWP.fold (skipBelow3_bytesMerge3_entails s0.sp 97 (by decide) (by decide)) (by sep_focus)
    apply SepWP.fold (pointsToBytes_prefix_join hrest_le hrest_suf) (by sep_focus)
    have hpb : vecU8At A.repAlloc x.msgPtr cap1 ptr1 m.rootKey ∗
        vecU8At A.repAlloc (x.msgPtr + 0x18#64) cap2 ptr2 m.macKey ⊢
        authenticatorPBAt A.repAlloc x.msgPtr m :=
      sepConj_mono
        (Entails.sepExists_right cap1 (Entails.sepExists_right ptr1 (Entails.refl _)))
        (Entails.sepExists_right cap2 (Entails.sepExists_right ptr2 (Entails.refl _)))
    apply SepWP.fold hpb (by sep_focus)
    wp_steps_sync_pool ((blkPl_295).base + 436#64)
    simp only [State.setMem_setMem]
    wp_reach; intro hinvm'
    refine SepWPp.weaken_pre (Entails.of_eq (by dsimp only [authBudgetErrFrame]; sep_ac_rfl))
      (auth_push_err_exit_merge_cl_placed hPushCall hnone hsm0
        (hfits_push cap1 ptr1 evs_bm hmb hevs_bm)
        (fun evs_p hp => hevs_bm_err cap1 ptr1 evs_bm evs_p hmb hevs_bm hp)
        hsp_align
        (by simp only [arm64_norm]) (by simp only [arm64_norm, hrunm])
        (by simp only [arm64_norm, hspm]) (by simp only [arm64_norm, htrm, htr])
        (by simp only [arm64_norm, hspm])
        ⟨by simp only [arm64_norm, hx23_m], by simp only [arm64_norm, hx24_m],
         by simp only [arm64_norm, hx25_m], by simp only [arm64_norm, hx26_m],
         by simp only [arm64_norm, hx27_m], by simp only [arm64_norm, hx28_m],
         by simp only [arm64_norm, hvregs_m]⟩ hinvm')
  | some p =>
    rcases p with ⟨v, rest'⟩
    have hrest'_le : rest'.length ≤ rest.length := Nat.le_of_lt (mergeBytes_length hmb)
    have hcap2' : BytesMergeCapOk cap2 rest'.length := bytesMergeCapOk_mono hcap2 hrest'_le
    apply SepWPp.of_sepWP_lscro (mid := (blkPl_295).base + 160#64) hinvm
    (conv => arg 4; simp only [bytesMerge3RawBudgetSpec, hmb,
      sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc])
    apply SepWP.exists_elim; intro evs_bm
    apply SepWP.exists_elim; intro cap1'
    apply SepWP.exists_elim; intro ptr1'
    wp_focus_pure; intro htrm
    wp_focus_pure; intro hevs_bm
    wp_focus_pure; intro hsm0
    wp_focus_pure; intro hcap1'
    conv => arg 4; simp only [arm64_norm, hsp]
    apply SepWP.fold (skipBelow3_bytesMerge3_entails s0.sp 97 (by decide) (by decide)) (by sep_focus)
    apply SepWP.fold (sliceCursorAfter_join hrest_le hrest_suf hrest'_le) (by sep_focus)
    have hcap_fold :
        vecU8At A.repAlloc x.msgPtr cap1' ptr1' v ∗
          vecU8At A.repAlloc (x.msgPtr + 0x18#64) cap2 ptr2 m.macKey ⊢
          authenticatorPBCapAt A.repAlloc x.msgPtr rest'.length { m with rootKey := v } := by
      unfold authenticatorPBCapAt
      refine sepConj_mono ?_ ?_
      · refine Entails.trans (Entails.pure_right hcap1' (Entails.refl _)) ?_
        exact Entails.sepExists_right cap1' (Entails.sepExists_right ptr1' (Entails.refl _))
      · refine Entails.trans (Entails.pure_right hcap2' (Entails.refl _)) ?_
        exact Entails.sepExists_right cap2 (Entails.sepExists_right ptr2 (Entails.refl _))
    apply SepWP.fold hcap_fold (by sep_focus)
    wp_steps_sync_pool ((blkPl_295).base + 160#64)
    simp only [State.setMem_setMem]
    wp_reach; intro hinvm'
    refine SepWPp.weaken_pre (Entails.of_eq (by dsimp only [authBudgetLoopPre]; sep_ac_rfl))
      (hcont cap1 ptr1 v rest' evs_bm _ hmb hevs_bm
        (by simp only [arm64_norm]) (by simp only [arm64_norm, hrunm])
        (by simp only [arm64_norm, hspm]) (by simp only [arm64_norm, htrm, htr])
        (by simp only [arm64_norm, hx19_m]) (by simp only [arm64_norm, hx20_m])
        (by simp only [arm64_norm, hx21_m]) (by simp only [arm64_norm, hx22_m])
        ⟨by simp only [arm64_norm, hx23_m], by simp only [arm64_norm, hx24_m],
         by simp only [arm64_norm, hx25_m], by simp only [arm64_norm, hx26_m],
         by simp only [arm64_norm, hx27_m], by simp only [arm64_norm, hx28_m],
         by simp only [arm64_norm, hvregs_m]⟩ hinvm')

set_option maxRecDepth 200000 in
set_option maxHeartbeats 400000 in
set_option linter.unusedSimpArgs false in
theorem auth_tag2_step_merge_cl_placed [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {H : LibsignalHooks}
    {PreEnv PostEnv : AuthMergeGhost → List AllocEvent → Prop}
    (hPushCall : subroutine_ok ((blkPC_295).rebase (blkPl_295).base H) (lsmpl.base 257)
      (withLsCodeRoLoaded lsmpl (decodeErrorPushMergeBudgetSpec M A lim)))
    (hBytesCall : subroutine_ok ((blkPC_295).rebase (blkPl_295).base H) (lsmpl.base 290)
      (withLsCodeRoLoaded lsmpl (bytesMerge3RawBudgetSpec A lim)))
    {x : AuthMergeGhost} {st0 st_cur : M.σ} {R : SepProp} {s0 s : State}
    {m : ProtoAuthenticator} {rest : List (BitVec 8)} {iwt : WireType} {limit : Nat}
    (hsp_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hrest_le : rest.length ≤ x.bs.length)
    (hrest_lt : rest.length < 2 ^ 63)
    (hrest_suf : IsDropSuffix x.bs rest)
    (hfits_bm : ∀ cap2 ptr2 : BitVec 64, BytesMergeCapOk cap2 rest.length →
      FitsEnv M lim st_cur
        (BytesMerge3Env ⟨iwt, x.msgPtr + 0x18#64, cap2, ptr2, m.macKey, x.bufRef, x.slot,
          x.ptr + BitVec.ofNat 64 (x.bs.length - rest.length), rest⟩))
    (hfits_push : ∀ (cap2 ptr2 : BitVec 64) (evs_bm : List AllocEvent),
      mergeBytes iwt rest = none →
      BytesMerge3Env ⟨iwt, x.msgPtr + 0x18#64, cap2, ptr2, m.macKey, x.bufRef, x.slot,
        x.ptr + BitVec.ofNat 64 (x.bs.length - rest.length), rest⟩ evs_bm →
      FitsEnv M lim (M.stepEvents evs_bm st_cur) (DecodeErrorPushMergeEnv 0))
    (hevs_bm_err : ∀ (cap2 ptr2 : BitVec 64) (evs_bm evs_p : List AllocEvent),
      mergeBytes iwt rest = none →
      BytesMerge3Env ⟨iwt, x.msgPtr + 0x18#64, cap2, ptr2, m.macKey, x.bufRef, x.slot,
        x.ptr + BitVec.ofNat 64 (x.bs.length - rest.length), rest⟩ evs_bm →
      DecodeErrorPushMergeEnv 0 evs_p →
      ∃ evs, PostEnv x evs ∧ M.stepEvents evs_p (M.stepEvents evs_bm st_cur) = M.stepEvents evs st0)
    (hnone_of_mb : mergeBytes iwt rest = none →
      (mergeMessage ProtoAuthenticator.mergeField (codecWireTypeToProto x.wt) x.msg x.bs 97).toOption = none)
    (hcont : ∀ (cap2 ptr2 : BitVec 64) (v rest' : List (BitVec 8))
      (evs_bm : List AllocEvent) (s' : State),
      mergeBytes iwt rest = some (v, rest') →
      BytesMerge3Env ⟨iwt, x.msgPtr + 0x18#64, cap2, ptr2, m.macKey, x.bufRef, x.slot,
        x.ptr + BitVec.ofNat 64 (x.bs.length - rest.length), rest⟩ evs_bm →
      s'.pc = (blkPl_295).base + 160#64 →
      s'.status = .Running → s'.sp = s0.sp - 96#64 → s'.trace = s0.trace →
      s'.readReg64 (Reg.gpr 19#5) = x.bufRef → s'.readReg64 (Reg.gpr 20#5) = x.msgPtr →
      s'.readReg64 (Reg.gpr 21#5) = x.slot → s'.readReg64 (Reg.gpr 22#5) = BitVec.ofNat 64 limit →
      HighCalleeSaved s0 s' → LibsignalCodeRoLoaded lsmpl s'.mem →
      SepWPp ((blkPC_295).rebase (blkPl_295).base H) (s0.readReg64 Reg.lr) s'
        (authBudgetLoopPre A lim (M.stepEvents evs_bm st_cur) s0 s'
          x.msgPtr x.bufRef x.slot x.ptr { m with macKey := v } x.bs rest')
        (WppPost (authMergeSpecOfEnv A lim PreEnv PostEnv) (x, st0) R s0)
        (WppBudgetPanic (authMergeSpecOfEnv A lim PreEnv PostEnv) (x, st0) R s0))
    (hpc : s.pc = (blkPl_295).base + 228#64)
    (hrun : s.status = .Running) (hsp : s.sp = s0.sp - 96#64)
    (htr : s.trace = s0.trace) (hx0 : s.readReg64 (Reg.gpr 0#5) = BitVec.ofNat 64 iwt.toNat)
    (hx19 : s.readReg64 (Reg.gpr 19#5) = x.bufRef) (hx20 : s.readReg64 (Reg.gpr 20#5) = x.msgPtr)
    (hx21 : s.readReg64 (Reg.gpr 21#5) = x.slot) (hx22 : s.readReg64 (Reg.gpr 22#5) = BitVec.ofNat 64 limit)
    (hcs : HighCalleeSaved s0 s) (hinv : LibsignalCodeRoLoaded lsmpl s.mem) :
    SepWPp ((blkPC_295).rebase (blkPl_295).base H) (s0.readReg64 Reg.lr) s
      (authBudgetLoopPre A lim st_cur s0 s x.msgPtr x.bufRef x.slot x.ptr m x.bs rest)
      (WppPost (authMergeSpecOfEnv A lim PreEnv PostEnv) (x, st0) R s0)
      (WppBudgetPanic (authMergeSpecOfEnv A lim PreEnv PostEnv) (x, st0) R s0) := by
  obtain ⟨hx23, hx24, hx25, hx26, hx27, hx28, hvregs⟩ := hcs
  let restPtr : BitVec 64 := x.ptr + BitVec.ofNat 64 (x.bs.length - rest.length)
  conv =>
    arg 4
    rw [authBudgetLoopPre, authenticatorPBCapAt, sliceCursorAfter_eq_split hrest_le hrest_suf,
      skipBelow3_bytesMerge3 s0.sp 97 (by decide) (by decide)]
    simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
  apply SepWPp.exists_elim; intro cap2; apply SepWPp.exists_elim; intro ptr2
  apply SepWPp.exists_elim; intro cap1; apply SepWPp.exists_elim; intro ptr1
  apply CryptoVerification.SpqrV1.Auth.SepWPp.pure_elim; intro hcap1; apply SepWPp.pure_elim2; intro hcap2
  apply SepWPp.of_sepWP_lscro (mid := lsmpl.base 290) hinv
  wp_steps_sync_pool (lsmpl.base 290)
  simp only [State.setMem_setMem]
  wp_reach; intro hinv
  refine SepWPp.call_frame_lscro (spec := bytesMerge3RawBudgetSpec A lim)
    (x := (⟨iwt, x.msgPtr + 0x18#64, cap2, ptr2, m.macKey, x.bufRef, x.slot, restPtr, rest⟩, st_cur))
    (ret_pc := (blkPl_295).base + 240#64) hBytesCall hinv
    (by simp only [arm64_norm]) (by simp only [arm64_norm, hrun])
    (by simp only [State.spAligned, hsp, arm64_norm]; exact hsp_align)
    (by simp only [arm64_norm])
    rfl
    ⟨by simp only [arm64_norm, hsp, hx0, setWidth8_ofNat64_wt],
     by simp only [arm64_norm, hsp, hx20],
     by simp only [arm64_norm, hsp, hx19],
     hrest_lt, hcap2, hfits_bm cap2 ptr2 hcap2⟩
    (by sep_focus)
    (fun _ _ _ _ hex => False.elim (not_satisfies_false_sepConj hex))
    (fun _ _ => wppBudgetPanic_false) ?_
  intro sm hpcm hrunm hspm hcsm hinvm
  simp only [CalleeSavedPreserved] at hcsm
  obtain ⟨hx19_m, hx20_m, hx21_m, hx22_m, hx23_m, hx24_m, hx25_m, hx26_m, hx27_m, hx28_m, hfp_m, hvregs_m⟩ := hcsm
  simp (config := { decide := true }) only [arm64_norm, hsp, hx19, hx20, hx21, hx22, hx23, hx24, hx25, hx26, hx27, hx28, hvregs]
    at hpcm hrunm hspm hx19_m hx20_m hx21_m hx22_m hx23_m hx24_m hx25_m hx26_m hx27_m hx28_m hfp_m hvregs_m
  cases hmb : mergeBytes iwt rest with
  | none =>
    have hnone := hnone_of_mb hmb
    apply SepWPp.of_sepWP_lscro (mid := (blkPl_295).base + 436#64) hinvm
    (conv => arg 4; simp only [bytesMerge3RawBudgetSpec, hmb, memRegion_48_split_96 s0.sp,
      sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc])
    apply SepWP.exists_elim; intro v_stk0
    apply SepWP.exists_elim; intro evs_bm
    wp_focus_pure; intro htrm
    wp_focus_pure; intro hevs_bm
    wp_focus_pure; intro hsm0
    conv => arg 4; simp only [arm64_norm, hsp]
    have hcbnz : (sm.readReg64 (Reg.gpr 0#5) == 0#64) = false := beq_eq_false_iff_ne.mpr hsm0
    apply SepWP.fold (skipBelow3_bytesMerge3_entails s0.sp 97 (by decide) (by decide)) (by sep_focus)
    apply SepWP.fold (pointsToBytes_prefix_join hrest_le hrest_suf) (by sep_focus)
    have hpb : vecU8At A.repAlloc x.msgPtr cap1 ptr1 m.rootKey ∗
        vecU8At A.repAlloc (x.msgPtr + 24#64) cap2 ptr2 m.macKey ⊢
        authenticatorPBAt A.repAlloc x.msgPtr m :=
      sepConj_mono
        (Entails.sepExists_right cap1 (Entails.sepExists_right ptr1 (Entails.refl _)))
        (Entails.sepExists_right cap2 (Entails.sepExists_right ptr2 (Entails.refl _)))
    apply SepWP.fold hpb (by sep_focus)
    wp_steps_sync_pool ((blkPl_295).base + 436#64)
    simp only [State.setMem_setMem]
    wp_reach; intro hinvm'
    refine SepWPp.weaken_pre (Entails.of_eq (by dsimp only [authBudgetErrFrame]; sep_ac_rfl))
      (auth_push_err_exit_merge_cl_placed hPushCall hnone hsm0
        (hfits_push cap2 ptr2 evs_bm hmb hevs_bm)
        (fun evs_p hp => hevs_bm_err cap2 ptr2 evs_bm evs_p hmb hevs_bm hp)
        hsp_align
        (by simp only [arm64_norm]) (by simp only [arm64_norm, hrunm])
        (by simp only [arm64_norm, hspm]) (by simp only [arm64_norm, htrm, htr])
        (by simp only [arm64_norm, hspm])
        ⟨by simp only [arm64_norm, hx23_m], by simp only [arm64_norm, hx24_m],
         by simp only [arm64_norm, hx25_m], by simp only [arm64_norm, hx26_m],
         by simp only [arm64_norm, hx27_m], by simp only [arm64_norm, hx28_m],
         by simp only [arm64_norm, hvregs_m]⟩ hinvm')
  | some p =>
    rcases p with ⟨v, rest'⟩
    have hrest'_le : rest'.length ≤ rest.length := Nat.le_of_lt (mergeBytes_length hmb)
    have hcap1' : BytesMergeCapOk cap1 rest'.length := bytesMergeCapOk_mono hcap1 hrest'_le
    apply SepWPp.of_sepWP_lscro (mid := (blkPl_295).base + 160#64) hinvm
    (conv => arg 4; simp only [bytesMerge3RawBudgetSpec, hmb,
      sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc])
    apply SepWP.exists_elim; intro evs_bm
    apply SepWP.exists_elim; intro cap2'
    apply SepWP.exists_elim; intro ptr2'
    wp_focus_pure; intro htrm
    wp_focus_pure; intro hevs_bm
    wp_focus_pure; intro hsm0
    wp_focus_pure; intro hcap2'
    conv => arg 4; simp only [arm64_norm, hsp]
    apply SepWP.fold (skipBelow3_bytesMerge3_entails s0.sp 97 (by decide) (by decide)) (by sep_focus)
    apply SepWP.fold (sliceCursorAfter_join hrest_le hrest_suf hrest'_le) (by sep_focus)
    have hcap_fold :
        vecU8At A.repAlloc x.msgPtr cap1 ptr1 m.rootKey ∗
          vecU8At A.repAlloc (x.msgPtr + 24#64) cap2' ptr2' v ⊢
          authenticatorPBCapAt A.repAlloc x.msgPtr rest'.length { m with macKey := v } := by
      unfold authenticatorPBCapAt
      refine sepConj_mono ?_ ?_
      · refine Entails.trans (Entails.pure_right hcap1' (Entails.refl _)) ?_
        exact Entails.sepExists_right cap1 (Entails.sepExists_right ptr1 (Entails.refl _))
      · refine Entails.trans (Entails.pure_right hcap2' (Entails.refl _)) ?_
        exact Entails.sepExists_right cap2' (Entails.sepExists_right ptr2' (Entails.refl _))
    apply SepWP.fold hcap_fold (by sep_focus)
    wp_steps_sync_pool ((blkPl_295).base + 160#64)
    simp only [State.setMem_setMem]
    wp_reach; intro hinvm'
    refine SepWPp.weaken_pre (Entails.of_eq (by dsimp only [authBudgetLoopPre]; sep_ac_rfl))
      (hcont cap2 ptr2 v rest' evs_bm _ hmb hevs_bm
        (by simp only [arm64_norm]) (by simp only [arm64_norm, hrunm])
        (by simp only [arm64_norm, hspm]) (by simp only [arm64_norm, htrm, htr])
        (by simp only [arm64_norm, hx19_m]) (by simp only [arm64_norm, hx20_m])
        (by simp only [arm64_norm, hx21_m]) (by simp only [arm64_norm, hx22_m])
        ⟨by simp only [arm64_norm, hx23_m], by simp only [arm64_norm, hx24_m],
         by simp only [arm64_norm, hx25_m], by simp only [arm64_norm, hx26_m],
         by simp only [arm64_norm, hx27_m], by simp only [arm64_norm, hx28_m],
         by simp only [arm64_norm, hvregs_m]⟩ hinvm')

/-! ## Loop Induction and Top-Level `[LibsignalPlacement]` Contracts -/

set_option maxRecDepth 200000 in
set_option maxHeartbeats 400000 in
set_option linter.unusedSimpArgs false in
theorem auth_loop_base_ok_cl_placed [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {H : LibsignalHooks}
    {PreEnv PostEnv : AuthMergeGhost → List AllocEvent → Prop}
    (hFromCall : subroutine_ok ((blkPC_295).rebase (blkPl_295).base H) (lsmpl.base 261)
      (withLsCodeRoLoaded lsmpl (decodeErrorFromBudgetSpec M A lim)))
    (hPushCall : subroutine_ok ((blkPC_295).rebase (blkPl_295).base H) (lsmpl.base 257)
      (withLsCodeRoLoaded lsmpl (decodeErrorPushMergeBudgetSpec M A lim)))
    (hVarintCall : subroutine_ok ((blkPC_295).rebase (blkPl_295).base H) (lsmpl.base 291)
      (withLsCodeRoLoaded lsmpl (decodeVarint2Spec A lim)))
    (hSkipCall : subroutine_ok ((blkPC_295).rebase (blkPl_295).base H) (lsmpl.base 263)
      (withLsCodeRoLoaded lsmpl (skipField3Spec A lim)))
    (hBytesCall : subroutine_ok ((blkPC_295).rebase (blkPl_295).base H) (lsmpl.base 290)
      (withLsCodeRoLoaded lsmpl (bytesMerge3RawBudgetSpec A lim)))
    {x : AuthMergeGhost} {st0 : M.σ} {R : SepProp} {s0 : State} {limit : Nat}
    (hFit0 : FitsEnv M lim st0 (AuthMergeLoopEnv 4 x.bs.length))
    (hPost : ∀ evs, AuthMergePostEnv x evs → PostEnv x evs)
    (hsp_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hbs_lt : x.bs.length < 2 ^ 63) (hlim_lt : limit < 2 ^ 63) :
    ∀ (n : Nat) (m : ProtoAuthenticator) (cur : List (BitVec 8))
      (evs_acc : List AllocEvent) (st_cur : M.σ) (s : State),
      cur.length ≤ n → cur.length ≤ x.bs.length → IsDropSuffix x.bs cur →
      st_cur = M.stepEvents evs_acc st0 →
      AuthMergeLoopEnv 0 (x.bs.length - cur.length) evs_acc →
      (mergeMessage ProtoAuthenticator.mergeField (codecWireTypeToProto x.wt) x.msg x.bs 97).toOption =
        (mergeLoopBin ProtoAuthenticator.mergeField (cur.length - limit) m cur limit 96).map
          (fun m' => (m', x.bs.drop (x.bs.length - limit))) →
      s.pc = (blkPl_295).base + 160#64 →
      s.status = .Running → s.sp = s0.sp - 96#64 → s.trace = s0.trace →
      s.readReg64 (Reg.gpr 19#5) = x.bufRef → s.readReg64 (Reg.gpr 20#5) = x.msgPtr →
      s.readReg64 (Reg.gpr 21#5) = x.slot → s.readReg64 (Reg.gpr 22#5) = BitVec.ofNat 64 limit →
      HighCalleeSaved s0 s → LibsignalCodeRoLoaded lsmpl s.mem →
      SepWPp ((blkPC_295).rebase (blkPl_295).base H) (s0.readReg64 Reg.lr) s
        (authBudgetLoopPre A lim st_cur s0 s x.msgPtr x.bufRef x.slot x.ptr m x.bs cur)
        (WppPost (authMergeSpecOfEnv A lim PreEnv PostEnv) (x, st0) R s0)
        (WppBudgetPanic (authMergeSpecOfEnv A lim PreEnv PostEnv) (x, st0) R s0) := by
  have hpost_err : ∀ (hnone : (mergeMessage ProtoAuthenticator.mergeField (codecWireTypeToProto x.wt) x.msg x.bs 97).toOption = none)
      {e b : Nat} {evs : List AllocEvent},
      e ≤ 4 → b ≤ x.bs.length →
      AuthMergeLoopEnv e b evs →
      PostEnv x evs := fun hnone {_} {_} {_} he hb hevs => by
    apply hPost
    dsimp only [AuthMergePostEnv]
    rw [hnone]
    exact hevs.mono he hb
  intro n; induction n with
  | zero =>
    intro m cur evs_acc st_cur s hcur_n hcur_le hcur_suf hst_cur hevs_acc hres_cur
      hpc hrun hsp htr hx19 hx20 hx21 hx22 hcs hinv
    have hFit_rem : FitsEnv M lim st_cur (AuthMergeLoopEnv 4 cur.length) := by
      rw [hst_cur]
      apply MergeBaseBudget.FitsEnv.authMergeLoop_split hevs_acc
      simpa [show (x.bs.length - cur.length) + cur.length = x.bs.length by omega] using hFit0
    exact auth_loop_le_exit_cl_placed hFromCall (by omega) hsp_align hcur_le hcur_suf hlim_lt
      (fun _ hsome => ⟨evs_acc, hPost _ (by dsimp only [AuthMergePostEnv]; rw [hsome]; exact hevs_acc), hst_cur⟩)
      (fun _ evs_f hf => hFit_rem evs_f ((authMergeLoopEnv_of_decodeErrorFrom hf).mono (by omega) (by omega)))
      (fun hlt evs_f hf => by
        have hnone : (mergeMessage ProtoAuthenticator.mergeField (codecWireTypeToProto x.wt) x.msg x.bs 97).toOption = none := by
          rw [hres_cur, mergeLoopBin_lt_limit _ _ _ _ _ _ hlt, Option.map_none]
        exact ⟨evs_acc ++ evs_f,
          hpost_err hnone (by omega) (by omega)
            (hevs_acc.append (authMergeLoopEnv_of_decodeErrorFrom hf)),
          by rw [hst_cur, stepEvents_append]⟩)
      hres_cur hpc hrun hsp htr hx21 hx22 hcs hinv
  | succ n ih =>
    intro m cur evs_acc st_cur s hcur_n hcur_le hcur_suf hst_cur hevs_acc hres_cur
      hpc hrun hsp htr hx19 hx20 hx21 hx22 hcs hinv
    have hFit_rem : FitsEnv M lim st_cur (AuthMergeLoopEnv 4 cur.length) := by
      rw [hst_cur]
      apply MergeBaseBudget.FitsEnv.authMergeLoop_split hevs_acc
      simpa [show (x.bs.length - cur.length) + cur.length = x.bs.length by omega] using hFit0
    by_cases hle_lim : cur.length ≤ limit
    · exact auth_loop_le_exit_cl_placed hFromCall hle_lim hsp_align hcur_le hcur_suf hlim_lt
        (fun _ hsome => ⟨evs_acc, hPost _ (by dsimp only [AuthMergePostEnv]; rw [hsome]; exact hevs_acc), hst_cur⟩)
        (fun _ evs_f hf => hFit_rem evs_f ((authMergeLoopEnv_of_decodeErrorFrom hf).mono (by omega) (by omega)))
        (fun hlt evs_f hf => by
          have hnone : (mergeMessage ProtoAuthenticator.mergeField (codecWireTypeToProto x.wt) x.msg x.bs 97).toOption = none := by
            rw [hres_cur, mergeLoopBin_lt_limit _ _ _ _ _ _ hlt, Option.map_none]
          exact ⟨evs_acc ++ evs_f,
            hpost_err hnone (by omega) (by omega)
              (hevs_acc.append (authMergeLoopEnv_of_decodeErrorFrom hf)),
            by rw [hst_cur, stepEvents_append]⟩)
        hres_cur hpc hrun hsp htr hx21 hx22 hcs hinv
    · have hcur_lt : cur.length < 2 ^ 63 := Nat.lt_of_le_of_lt hcur_le hbs_lt
      refine auth_decode_key_step_cl_placed hFromCall hVarintCall hle_lim hsp_align
        hcur_le hcur_lt hcur_suf
        (fun evs_dv hdv => hFit_rem evs_dv ((authMergeLoopEnv_of_decodeVarint2 hdv).mono (by omega) (by omega)))
        (fun hd evs_dv hdv => by
          have hnone : (mergeMessage ProtoAuthenticator.mergeField (codecWireTypeToProto x.wt) x.msg x.bs 97).toOption = none := by
            rw [hres_cur,
              CryptoVerification.SpqrV1.Prost.MessageMerge.mergeLoopBin_of_decodeVarint_none
                protoPrefixStep_protoAuthenticator_mergeField hle_lim hd,
              Option.map_none]
          exact ⟨evs_acc ++ evs_dv,
            hpost_err hnone (by omega) (by omega)
              (hevs_acc.append (authMergeLoopEnv_of_decodeVarint2 hdv)),
            by rw [hst_cur, stepEvents_append]⟩)
        (fun evs_f hf => hFit_rem evs_f ((authMergeLoopEnv_of_decodeErrorFrom hf).mono (by omega) (by omega)))
        (fun hnone evs_f hf =>
          ⟨evs_acc ++ evs_f,
            hpost_err hnone (by omega) (by omega)
              (hevs_acc.append (authMergeLoopEnv_of_decodeErrorFrom hf)),
            by rw [hst_cur, stepEvents_append]⟩)
        hres_cur ?_ hpc hrun hsp htr hx19 hx20 hx21 hx22 hcs hinv
      intro key iwt rest s' hd hk_ge hwt hitag0 hpc' hrun' hsp' htr' hx0' hx1' hx19' hx20' hx21' hx22' hcs' hinv'
      obtain ⟨hx23', hx24', hx25', hx26', hx27', hx28', hvregs'⟩ := hcs'
      have hrest_lt_cur : rest.length < cur.length := decodeVarint_length hd
      have hrest_le_cur : rest.length ≤ cur.length := Nat.le_of_lt hrest_lt_cur
      have hrest_le : rest.length ≤ x.bs.length := Nat.le_trans hrest_le_cur hcur_le
      have hrest_lt : rest.length < 2 ^ 63 := Nat.lt_of_le_of_lt hrest_le hbs_lt
      have hrest_suf : IsDropSuffix x.bs rest := suffix_trans hcur_le hcur_suf hrest_le_cur (decodeVarint_suffix hd)
      have hloop_ok := mergeLoopBin_of_key_ok (m := m) (depth' := 96)
        protoPrefixStep_protoAuthenticator_mergeField hle_lim hd hk_ge hwt hitag0
      by_cases htag1 : key.toNat / 8 = 1
      · rw [htag1] at hx1' hloop_ok
        rw [protoAuthenticator_mergeField_tag1] at hloop_ok
        have hnone_mb : mergeBytes iwt rest = none →
            (mergeMessage ProtoAuthenticator.mergeField (codecWireTypeToProto x.wt) x.msg x.bs 97).toOption = none := by
          intro hmb; simp only [hres_cur, hloop_ok, hmb, Option.map_none]
        apply SepWPp.of_sepWP_lscro (mid := (blkPl_295).base + 252#64) hinv'
        conv => arg 4; rw [authBudgetLoopPre]; simp only [sepConj_assoc]
        wp_steps_sync_pool ((blkPl_295).base + 252#64)
        simp only [State.setMem_setMem]
        wp_reach; intro hinv'
        refine SepWPp.weaken_pre ?_
          (auth_tag1_step_merge_cl_placed (st0 := st0) (st_cur := st_cur) (m := m) (limit := limit) hPushCall hBytesCall hsp_align hrest_le hrest_lt hrest_suf
            (fun _ _ _ => fitsEnv_bytesMerge3_of_authMergeLoop (errRem := 3) hrest_le_cur hFit_rem)
            (fun _ _ evs_bm hmb hevs_bm evs_p hp => by
              have h1 := authMergeLoopEnv_of_bytesMerge3_none hmb hevs_bm
              have hFit_after : FitsEnv M lim (M.stepEvents evs_bm st_cur) (AuthMergeLoopEnv 3 cur.length) :=
                MergeBaseBudget.FitsEnv.authMergeLoop_split h1
                  (by simpa using hFit_rem)
              exact hFit_after evs_p ((authMergeLoopEnv_of_decodeErrorPush0 hp).mono (by omega) (by omega)))
            (fun _ _ evs_bm evs_p hmb hevs_bm hp =>
              ⟨(evs_acc ++ evs_bm) ++ evs_p,
                hpost_err (hnone_mb hmb) (by omega) (by omega)
                  ((hevs_acc.append (authMergeLoopEnv_of_bytesMerge3_none hmb hevs_bm)).append
                    (authMergeLoopEnv_of_decodeErrorPush0 hp)),
                by simp only [hst_cur, stepEvents_append]⟩)
            hnone_mb
            (fun _ _ v rest' evs_bm s'' hmb hevs_bm hpc'' hrun'' hsp'' htr'' hx19'' hx20'' hx21'' hx22'' hcs'' hinv'' => ?_)
            (by simp only [arm64_norm]) (by simp only [arm64_norm, hrun'])
            (by simp only [arm64_norm, hsp']) (by simp only [arm64_norm, htr'])
            (by simp only [arm64_norm, hx0'])
            (by simp only [arm64_norm, hx19']) (by simp only [arm64_norm, hx20'])
            (by simp only [arm64_norm, hx21']) (by simp only [arm64_norm, hx22'])
            ⟨by simp only [arm64_norm, hx23'], by simp only [arm64_norm, hx24'],
             by simp only [arm64_norm, hx25'], by simp only [arm64_norm, hx26'],
             by simp only [arm64_norm, hx27'], by simp only [arm64_norm, hx28'],
             by simp only [arm64_norm, hvregs']⟩ hinv')
        · exact Entails.of_eq (by dsimp only [authBudgetLoopPre]; sep_ac_rfl)
        · have hrest'_lt : rest'.length < rest.length := mergeBytes_length hmb
          have hrest'_le_rest : rest'.length ≤ rest.length := Nat.le_of_lt hrest'_lt
          have hres_next : (mergeMessage ProtoAuthenticator.mergeField (codecWireTypeToProto x.wt) x.msg x.bs 97).toOption =
              (mergeLoopBin ProtoAuthenticator.mergeField (rest'.length - limit) { m with rootKey := v } rest' limit 96).map
                (fun m' => (m', x.bs.drop (x.bs.length - limit))) := by
            simp only [hres_cur, hloop_ok, hmb, Option.map_some]
          exact ih { m with rootKey := v } rest' (evs_acc ++ evs_bm) (M.stepEvents evs_bm st_cur) s''
            (by omega) (by omega)
            (suffix_trans hrest_le hrest_suf hrest'_le_rest (mergeBytes_suffix hmb))
            (by rw [hst_cur, stepEvents_append])
            ((hevs_acc.append (authMergeLoopEnv_of_bytesMerge3_some hmb hevs_bm)).mono
              (Nat.le_refl 0) (by dsimp only; omega))
            hres_next hpc'' hrun'' hsp'' htr'' hx19'' hx20'' hx21'' hx22'' hcs'' hinv''
      · by_cases htag2 : key.toNat / 8 = 2
        · rw [htag2] at hx1' hloop_ok
          rw [protoAuthenticator_mergeField_tag2] at hloop_ok
          have hnone_mb : mergeBytes iwt rest = none →
              (mergeMessage ProtoAuthenticator.mergeField (codecWireTypeToProto x.wt) x.msg x.bs 97).toOption = none := by
            intro hmb; simp only [hres_cur, hloop_ok, hmb, Option.map_none]
          apply SepWPp.of_sepWP_lscro (mid := (blkPl_295).base + 228#64) hinv'
          conv => arg 4; rw [authBudgetLoopPre]; simp only [sepConj_assoc]
          wp_steps_sync_pool ((blkPl_295).base + 228#64)
          simp only [State.setMem_setMem]
          wp_reach; intro hinv'
          refine SepWPp.weaken_pre ?_
            (auth_tag2_step_merge_cl_placed (st0 := st0) (st_cur := st_cur) (m := m) (limit := limit) hPushCall hBytesCall hsp_align hrest_le hrest_lt hrest_suf
              (fun _ _ _ => fitsEnv_bytesMerge3_of_authMergeLoop (errRem := 3) hrest_le_cur hFit_rem)
              (fun _ _ evs_bm hmb hevs_bm evs_p hp => by
                have h1 := authMergeLoopEnv_of_bytesMerge3_none hmb hevs_bm
                have hFit_after : FitsEnv M lim (M.stepEvents evs_bm st_cur) (AuthMergeLoopEnv 3 cur.length) :=
                  MergeBaseBudget.FitsEnv.authMergeLoop_split h1
                    (by simpa using hFit_rem)
                exact hFit_after evs_p ((authMergeLoopEnv_of_decodeErrorPush0 hp).mono (by omega) (by omega)))
              (fun _ _ evs_bm evs_p hmb hevs_bm hp =>
                ⟨(evs_acc ++ evs_bm) ++ evs_p,
                  hpost_err (hnone_mb hmb) (by omega) (by omega)
                    ((hevs_acc.append (authMergeLoopEnv_of_bytesMerge3_none hmb hevs_bm)).append
                      (authMergeLoopEnv_of_decodeErrorPush0 hp)),
                  by simp only [hst_cur, stepEvents_append]⟩)
              hnone_mb
              (fun _ _ v rest' evs_bm s'' hmb hevs_bm hpc'' hrun'' hsp'' htr'' hx19'' hx20'' hx21'' hx22'' hcs'' hinv'' => ?_)
              (by simp only [arm64_norm]) (by simp only [arm64_norm, hrun'])
              (by simp only [arm64_norm, hsp']) (by simp only [arm64_norm, htr'])
              (by simp only [arm64_norm, hx0'])
              (by simp only [arm64_norm, hx19']) (by simp only [arm64_norm, hx20'])
              (by simp only [arm64_norm, hx21']) (by simp only [arm64_norm, hx22'])
              ⟨by simp only [arm64_norm, hx23'], by simp only [arm64_norm, hx24'],
               by simp only [arm64_norm, hx25'], by simp only [arm64_norm, hx26'],
               by simp only [arm64_norm, hx27'], by simp only [arm64_norm, hx28'],
               by simp only [arm64_norm, hvregs']⟩ hinv')
          · exact Entails.of_eq (by dsimp only [authBudgetLoopPre]; sep_ac_rfl)
          · have hrest'_lt : rest'.length < rest.length := mergeBytes_length hmb
            have hrest'_le_rest : rest'.length ≤ rest.length := Nat.le_of_lt hrest'_lt
            have hres_next : (mergeMessage ProtoAuthenticator.mergeField (codecWireTypeToProto x.wt) x.msg x.bs 97).toOption =
                (mergeLoopBin ProtoAuthenticator.mergeField (rest'.length - limit) { m with macKey := v } rest' limit 96).map
                  (fun m' => (m', x.bs.drop (x.bs.length - limit))) := by
              simp only [hres_cur, hloop_ok, hmb, Option.map_some]
            exact ih { m with macKey := v } rest' (evs_acc ++ evs_bm) (M.stepEvents evs_bm st_cur) s''
              (by omega) (by omega)
              (suffix_trans hrest_le hrest_suf hrest'_le_rest (mergeBytes_suffix hmb))
              (by rw [hst_cur, stepEvents_append])
              ((hevs_acc.append (authMergeLoopEnv_of_bytesMerge3_some hmb hevs_bm)).mono
                (Nat.le_refl 0) (by dsimp only; omega))
              hres_next hpc'' hrun'' hsp'' htr'' hx19'' hx20'' hx21'' hx22'' hcs'' hinv''
        · have hitag_lt : key.toNat / 8 < 2 ^ 32 := by omega
          obtain ⟨hb1_1, _⟩ := itag_beq_tag_false htag1 hitag_lt (by decide : 1 < 2 ^ 32)
          obtain ⟨hb2_1, _⟩ := itag_beq_tag_false htag2 hitag_lt (by decide : 2 < 2 ^ 32)
          have hb1_2 : (BitVec.truncate 32 (BitVec.ofNat 64 (key.toNat / 8)) == 1#32) = false := by
            rw [sf_truncate32_ofNat64]; exact hb1_1
          have hb2_2 : (BitVec.truncate 32 (BitVec.ofNat 64 (key.toNat / 8)) == 2#32) = false := by
            rw [sf_truncate32_ofNat64]; exact hb2_1
          have hb2_bne1 : (BitVec.ofNat 32 (key.toNat / 8) != 2#32) = true := by
            simp only [bne, hb2_1, Bool.not_false]
          have hb2_bne2 : (BitVec.truncate 32 (BitVec.ofNat 64 (key.toNat / 8)) != 2#32) = true := by
            simp only [bne, hb2_2, Bool.not_false]
          rw [protoAuthenticator_mergeField_other m iwt rest 96 hitag_lt htag1 htag2] at hloop_ok
          have hnone_sf : skipField (2 * rest.length + 2) 96 (key.toNat / 8) iwt rest = none →
              (mergeMessage ProtoAuthenticator.mergeField (codecWireTypeToProto x.wt) x.msg x.bs 97).toOption = none := by
            intro hsf; rw [hres_cur, hloop_ok, hsf]; rfl
          apply SepWPp.of_sepWP_lscro (mid := (blkPl_295).base + 140#64) hinv'
          conv => arg 4; rw [authBudgetLoopPre]; simp only [sepConj_assoc]
          wp_steps_sync_pool ((blkPl_295).base + 140#64)
          simp only [State.setMem_setMem]
          wp_reach; intro hinv'
          refine SepWPp.weaken_pre ?_
            (auth_skip_step_cl_placed (m := m) (limit := limit) hSkipCall hsp_align hrest_le hrest_lt hrest_suf hitag_lt
              (fun evs_sf hsf => hFit_rem evs_sf ((authMergeLoopEnv_of_skipField3 hsf).mono (by omega) (by omega)))
              (fun hsf evs_sf hevs_sf =>
                ⟨evs_acc ++ evs_sf,
                  hpost_err (hnone_sf hsf) (by omega) (by omega)
                    (hevs_acc.append (authMergeLoopEnv_of_skipField3 hevs_sf)),
                  by rw [hst_cur, stepEvents_append]⟩)
              hnone_sf
              (fun rest' s'' hsf hpc'' hrun'' hsp'' htr'' hx19'' hx20'' hx21'' hx22'' hcs'' hinv'' => ?_)
              (by simp only [arm64_norm]) (by simp only [arm64_norm, hrun'])
              (by simp only [arm64_norm, hsp']) (by simp only [arm64_norm, htr'])
              (by simp only [arm64_norm, hx0'])
              (by simp only [arm64_norm, hx1', sf_truncate32_ofNat64])
              (by simp only [arm64_norm, hx19']) (by simp only [arm64_norm, hx20'])
              (by simp only [arm64_norm, hx21']) (by simp only [arm64_norm, hx22'])
              ⟨by simp only [arm64_norm, hx23'], by simp only [arm64_norm, hx24'],
               by simp only [arm64_norm, hx25'], by simp only [arm64_norm, hx26'],
               by simp only [arm64_norm, hx27'], by simp only [arm64_norm, hx28'],
               by simp only [arm64_norm, hvregs']⟩ hinv')
          · exact Entails.of_eq (by dsimp only [authBudgetLoopPre]; sep_ac_rfl)
          · have hrest'_le_rest : rest'.length ≤ rest.length :=
              (skip_length (2 * rest.length + 2)).1 _ _ _ _ _ hsf
            have hres_next : (mergeMessage ProtoAuthenticator.mergeField (codecWireTypeToProto x.wt) x.msg x.bs 97).toOption =
                (mergeLoopBin ProtoAuthenticator.mergeField (rest'.length - limit) m rest' limit 96).map
                  (fun m' => (m', x.bs.drop (x.bs.length - limit))) := by
              rw [hres_cur, hloop_ok, hsf]; rfl
            exact ih m rest' evs_acc st_cur s'' (by omega) (by omega)
              (suffix_trans hrest_le hrest_suf hrest'_le_rest
                ((skip_suffix (2 * rest.length + 2)).1 _ _ _ _ _ hsf))
              hst_cur (hevs_acc.mono (Nat.le_refl 0) (by omega))
              hres_next hpc'' hrun'' hsp'' htr'' hx19'' hx20'' hx21'' hx22'' hcs'' hinv''

set_option maxRecDepth 200000 in
set_option maxHeartbeats 400000 in
set_option linter.unusedSimpArgs false in
/-- Envelope-parameterized `withLsCodeRoLoaded` correctness of `Authenticator::merge` (block 295). -/
theorem auth_merge_base_cl_placed_ok_of_cro_contracts_env [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {H : LibsignalHooks}
    {PreEnv PostEnv : AuthMergeGhost → List AllocEvent → Prop}
    (hPre : ∀ x evs, AuthMergeEnv x evs → PreEnv x evs)
    (hPost : ∀ x evs, AuthMergePostEnv x evs → PostEnv x evs)
    (hFromCall : subroutine_ok ((blkPC_295).rebase (blkPl_295).base H) (lsmpl.base 261)
      (withLsCodeRoLoaded lsmpl (decodeErrorFromBudgetSpec M A lim)))
    (hPushCall : subroutine_ok ((blkPC_295).rebase (blkPl_295).base H) (lsmpl.base 257)
      (withLsCodeRoLoaded lsmpl (decodeErrorPushMergeBudgetSpec M A lim)))
    (hVarintCall : subroutine_ok ((blkPC_295).rebase (blkPl_295).base H) (lsmpl.base 291)
      (withLsCodeRoLoaded lsmpl (decodeVarint2Spec A lim)))
    (hSkipCall : subroutine_ok ((blkPC_295).rebase (blkPl_295).base H) (lsmpl.base 263)
      (withLsCodeRoLoaded lsmpl (skipField3Spec A lim)))
    (hBytesCall : subroutine_ok ((blkPC_295).rebase (blkPl_295).base H) (lsmpl.base 290)
      (withLsCodeRoLoaded lsmpl (bytesMerge3RawBudgetSpec A lim))) :
    subroutine_ok ((blkPC_295).rebase (blkPl_295).base H)
      (blkPl_295).base
      (withLsCodeRoLoaded lsmpl (authMergeSpecOfEnv A lim PreEnv PostEnv)) := by
  refine subroutine_ok.of_codeLoaded fun ⟨x, st0⟩ R s0 hpc hrun hpre hsp_align_st hL => ?_
  obtain ⟨hinv0, hpre⟩ := extract_withLsCodeRoLoaded hpre
  dsimp only [authMergeSpecOfEnv] at hpre
  rw [sepConj_assoc, satisfies_pure_sepConj] at hpre
  obtain ⟨⟨h_1, h_2, h_3, h, hFit_pre⟩, hm⟩ := hpre
  change (s0.readReg64 (Reg.gpr 0#5)).setWidth 8 = BitVec.ofNat 8 x.wt.toNat at h_1
  change s0.readReg64 (Reg.gpr 1#5) = x.msgPtr at h_2
  change s0.readReg64 (Reg.gpr 2#5) = x.bufRef at h_3
  have hsp_align : (s0.sp &&& 15#64 == 0#64) = true := by
    rw [State.spAligned] at hsp_align_st; exact hsp_align_st
  have hFit0 : FitsEnv M lim st0 (AuthMergeLoopEnv 4 x.bs.length) :=
    hFit_pre.mono (hPre x)
  have hpost_err0 :
      ∀ (hnone : (mergeMessage ProtoAuthenticator.mergeField (codecWireTypeToProto x.wt) x.msg x.bs 97).toOption = none)
        {evs : List AllocEvent},
        AuthMergeLoopEnv 1 0 evs →
        PostEnv x evs := fun hnone {_} hevs => by
    apply hPost x
    dsimp only [AuthMergePostEnv]
    rw [hnone]
    exact hevs.mono (by omega) (by omega)
  refine Exists.elim (SepWPp.to_subroutineOutcome_auth_placed hm hL ?_)
    fun _ ⟨hsteps, hout⟩ => reaches_outcome_steps hsteps (reaches_outcome.of_outcome hout)
  by_cases hwt_ld : x.wt = .lengthDelimited
  · have h_1' : (s0.readReg64 (Reg.gpr 0#5)).setWidth 8 = 2#8 := by rw [h_1, hwt_ld]; rfl
    have hbeq := wt_beq_two_of_lengthDelimited h_1'
    have hbne1 : (BitVec.truncate 32 (s0.readReg64 (Reg.gpr 0#5)) &&& 255#32 != 2#32) = false := by
      simp only [bne, hbeq, Bool.not_true]
    have hbne2 : (BitVec.truncate 32 (BitVec.zeroExtend 64 (BitVec.truncate 32 (s0.readReg64 (Reg.gpr 0#5))) &&& 255#64) != 2#32) = false := by
      rw [truncate32_zeroExtend64_and_255_eq, h_1']; decide
    have hbne3 : (BitVec.truncate 32 (BitVec.zeroExtend 64 (BitVec.truncate 32 (s0.readReg64 (Reg.gpr 0#5)) &&& 255#32)) != 2#32) = false := by
      revert h_1'; bv_bits
    apply SepWPp.of_sepWP_lscro (mid := lsmpl.base 291) hinv0
    conv => arg 4; rw [authMergeStack, stackAt_skipField3 s0.sp 97 (by decide), skipBelow3_leaf s0.sp 97 (by decide)]; simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
    apply SepWP.exists_elim; intro v19; apply SepWP.exists_elim; intro v20
    apply SepWP.exists_elim; intro v21; apply SepWP.exists_elim; intro v22
    apply SepWP.exists_elim; intro v_lr; apply SepWP.exists_elim; intro v_fp
    wp_steps_sync_pool (lsmpl.base 291)
    simp only [State.setMem_setMem]
    wp_reach; intro hinv0
    refine SepWPp.call_frame_lscro (spec := decodeVarint2Spec A lim)
      (x := (⟨x.bufRef, x.slot, x.ptr, x.bs⟩, st0))
      (ret_pc := (blkPl_295).base + 48#64) hVarintCall hinv0
      (by simp only [arm64_norm]) (by simp only [arm64_norm, hrun])
      (by simp only [State.spAligned, arm64_norm]; exact hsp_align)
      (by simp only [arm64_norm])
      rfl
      ⟨by simp only [arm64_norm, h_3], h,
       fun evs_dv hdv => hFit0 evs_dv ((authMergeLoopEnv_of_decodeVarint2 hdv).mono (by omega) (by omega))⟩
      (by dsimp only [sliceCursorAt]; sep_focus)
      (fun _ _ _ _ hex => False.elim (not_satisfies_false_sepConj hex))
      (fun _ _ => wppBudgetPanic_false) ?_
    intro sm hpcm hrunm hspm hcsm hinvm
    simp only [CalleeSavedPreserved] at hcsm
    obtain ⟨hx19_m, hx20_m, hx21_m, hx22_m, hx23_m, hx24_m, hx25_m, hx26_m, hx27_m, hx28_m, hfp_m, hvregs_m⟩ := hcsm
    simp (config := { decide := true }) only [arm64_norm, h_2, h_3]
      at hpcm hrunm hspm hx19_m hx20_m hx21_m hx22_m hx23_m hx24_m hx25_m hx26_m hx27_m hx28_m hfp_m hvregs_m
    cases hdv0 : decodeVarint x.bs with
    | none =>
      have hnone : (mergeMessage ProtoAuthenticator.mergeField (codecWireTypeToProto x.wt) x.msg x.bs 97).toOption = none := by
        rw [hwt_ld, ← mergeMessageBin_eq_proto_mergeMessage protoPrefixStep_protoAuthenticator_mergeField]
        simp [mergeMessageBin, codecWireTypeToProto, proto_decodeVarint_toOption, hdv0]
      apply SepWPp.of_sepWP_lscro (mid := (blkPl_295).base + 116#64) hinvm
      (conv => arg 4; simp only [decodeVarint2Spec, decodeVarint2SpecGen, hdv0,
        show 0x40 + (0x40 + decodeErrorHookStack) = decodeVarint2Stack from rfl,
        sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc])
      apply SepWP.exists_elim; intro evs_dv
      wp_focus_pure; intro hsm0
      wp_focus_pure; intro htrm
      wp_focus_pure; intro hevs_dv
      wp_focus_pure; intro hsm1
      conv => arg 4; simp only [arm64_norm]
      apply SepWP.fold (skipBelow3_leaf_entails s0.sp 97 (by decide)) (by sep_focus)
      apply SepWP.fold (authenticatorPBCapAt_entails_authenticatorPBAt A.repAlloc x.msgPtr x.bs.length x.msg) (by sep_focus)
      wp_steps_sync_pool ((blkPl_295).base + 116#64)
      simp only [State.setMem_setMem]
      wp_reach; intro _hinvm'
      refine SepWPp.weaken_pre (P' :=
        decodeErrorAtStackLen A.repAlloc (sm.readReg64 (Reg.gpr 1#5)) 0 ∗ memRegion (s0.sp - 96#64) 48 ∗
          skipBelow3 s0.sp 97 ∗ authBudgetErrFrame A lim (M.stepEvents evs_dv st0) s0 _ x.msgPtr x.bufRef x.slot x.ptr x.msg x.bs)
        (Entails.of_eq (by dsimp only [authBudgetErrFrame]; sep_ac_rfl)) ?_
      exact auth_err0_ret_exit_placed hnone
        ⟨evs_dv, hpost_err0 hnone (authMergeLoopEnv_of_decodeVarint2 hevs_dv), rfl⟩
        hsp_align
        (by simp only [arm64_norm]) (by simp only [arm64_norm, hrunm])
        (by simp only [arm64_norm, hspm]) (by simp only [arm64_norm, htrm])
        (by simp only [arm64_norm]) hsm1
        ⟨by simp only [arm64_norm, hx23_m], by simp only [arm64_norm, hx24_m],
         by simp only [arm64_norm, hx25_m], by simp only [arm64_norm, hx26_m],
         by simp only [arm64_norm, hx27_m], by simp only [arm64_norm, hx28_m],
         by simp only [arm64_norm, hvregs_m]⟩
    | some p =>
      rcases p with ⟨len, rest0⟩
      have hrest0_lt_bs : rest0.length < x.bs.length := decodeVarint_length hdv0
      have hrest0_le : rest0.length ≤ x.bs.length := Nat.le_of_lt hrest0_lt_bs
      have hrest0_lt : rest0.length < 2 ^ 63 := Nat.lt_of_lt_of_le hrest0_lt_bs (Nat.le_of_lt h)
      have hrest0_suf : IsDropSuffix x.bs rest0 := decodeVarint_suffix hdv0
      let rest0Ptr : BitVec 64 := x.ptr + BitVec.ofNat 64 (x.bs.length - rest0.length)
      by_cases hlt_len : rest0.length < len.toNat
      · have hule := ule_len_of_lt hlt_len hrest0_lt
        have hnone : (mergeMessage ProtoAuthenticator.mergeField (codecWireTypeToProto x.wt) x.msg x.bs 97).toOption = none := by
          rw [hwt_ld, ← mergeMessageBin_eq_proto_mergeMessage protoPrefixStep_protoAuthenticator_mergeField]
          rcases hdv0_p : CryptoVerification.LibsignalSpqrV1.Proto.decodeVarint x.bs with e | ⟨len', rest0'⟩
          · have hdv0' : decodeVarint x.bs = none := by rw [← proto_decodeVarint_toOption x.bs, hdv0_p]; rfl
            rw [hdv0] at hdv0'; nomatch hdv0'
          · have hdv0' : decodeVarint x.bs = some (len', rest0') := by rw [← proto_decodeVarint_toOption x.bs, hdv0_p]; rfl
            rw [hdv0] at hdv0'
            injection hdv0' with hpair; injection hpair with hlen hr0; subst hlen hr0
            simp [mergeMessageBin, codecWireTypeToProto, hdv0_p, Except.toOption, hlt_len]
        apply SepWPp.of_sepWP_lscro (mid := (blkPl_295).base + 100#64) hinvm
        (conv => arg 4; simp only [decodeVarint2Spec, decodeVarint2SpecGen, hdv0,
          show 0x40 + (0x40 + decodeErrorHookStack) = decodeVarint2Stack from rfl,
          sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc])
        apply SepWP.exists_elim; intro evs_dv
        wp_focus_pure; rintro ⟨hsm0, hsm1⟩
        wp_focus_pure; intro htrm
        wp_focus_pure; intro hevs_dv
        have hevs_nil := decodeVarint2Env_eq_nil hdv0 hevs_dv
        subst hevs_nil
        conv => arg 4; dsimp only [AllocCostModel.stepEvents, List.foldl]; simp only [arm64_norm]
        apply SepWP.fold (skipBelow3_leaf_entails s0.sp 97 (by decide)) (by sep_focus)
        apply SepWP.fold (authenticatorPBCapAt_entails_authenticatorPBAt A.repAlloc x.msgPtr x.bs.length x.msg) (by sep_focus)
        conv => arg 4; rw [sliceCursorAfter_eq_split hrest0_le hrest0_suf, sliceCursorAt, memRegion_48_split_96 s0.sp]
        simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
        apply SepWP.exists_elim; intro v_stk0
        wp_steps_sync_pool ((blkPl_295).base + 100#64)
        simp only [State.setMem_setMem]
        apply SepWP.fold (pointsTo64_pair_entails_memRegion16 x.slot rest0Ptr (BitVec.ofNat 64 rest0.length)) (by sep_focus)
        apply SepWP.fold (pointsToBytes_prefix_join hrest0_le hrest0_suf) (by sep_focus)
        wp_reach; intro hinvm'
        refine SepWPp.weaken_pre (P' :=
          ((s0.sp - 96#64) ↦₆₄ v_stk0) ∗ memRegion (s0.sp - 88#64) 40 ∗
            skipBelow3 s0.sp 97 ∗ authBudgetErrFrame A lim st0 s0 _ x.msgPtr x.bufRef x.slot x.ptr x.msg x.bs)
          (Entails.of_eq (by dsimp only [authBudgetErrFrame]; sep_ac_rfl)) ?_
        exact auth_from_err_exit_cl_placed hFromCall hnone
          (by decide : KindNoHeap 0x8000000000000007#64)
          (fun evs_f hf => hFit0 evs_f ((authMergeLoopEnv_of_decodeErrorFrom hf).mono (by omega) (by omega)))
          (fun evs_f hf => ⟨evs_f, hpost_err0 hnone (authMergeLoopEnv_of_decodeErrorFrom hf), rfl⟩)
          hsp_align
          (by simp only [arm64_norm]) (by simp only [arm64_norm, hrunm])
          (by simp only [arm64_norm, hspm]) (by simp only [arm64_norm, htrm])
          (by simp only [arm64_norm])
          ⟨by simp only [arm64_norm, hx23_m], by simp only [arm64_norm, hx24_m],
           by simp only [arm64_norm, hx25_m], by simp only [arm64_norm, hx26_m],
           by simp only [arm64_norm, hx27_m], by simp only [arm64_norm, hx28_m],
           by simp only [arm64_norm, hvregs_m]⟩ hinvm'
      · have hule := ule_len_of_ge hlt_len hrest0_lt
        have hsub := bv_len_sub_limit hlt_len
        have hlim_lt : rest0.length - len.toNat < 2 ^ 63 := by omega
        have hres0 : (mergeMessage ProtoAuthenticator.mergeField (codecWireTypeToProto x.wt) x.msg x.bs 97).toOption =
            (mergeLoopBin ProtoAuthenticator.mergeField (rest0.length - (rest0.length - len.toNat)) x.msg rest0 (rest0.length - len.toNat) 96).map
              (fun m' => (m', x.bs.drop (x.bs.length - (rest0.length - len.toNat)))) := by
          rw [hwt_ld, ← mergeMessageBin_eq_proto_mergeMessage protoPrefixStep_protoAuthenticator_mergeField]
          rcases hdv0_p : CryptoVerification.LibsignalSpqrV1.Proto.decodeVarint x.bs with e | ⟨len', rest0'⟩
          · have hdv0' : decodeVarint x.bs = none := by rw [← proto_decodeVarint_toOption x.bs, hdv0_p]; rfl
            rw [hdv0] at hdv0'; nomatch hdv0'
          · have hdv0' : decodeVarint x.bs = some (len', rest0') := by rw [← proto_decodeVarint_toOption x.bs, hdv0_p]; rfl
            rw [hdv0] at hdv0'
            injection hdv0' with hpair; injection hpair with hlen hr0; subst hlen hr0
            have hdrop_eq : x.bs.drop (x.bs.length - (rest0.length - len.toNat)) = rest0.drop len.toNat := by
              conv_rhs => rw [hrest0_suf, List.drop_drop]
              congr 1; omega
            simp only [mergeMessageBin, codecWireTypeToProto, bne_self_eq_false, Bool.false_eq_true, ↓reduceIte,
              hdv0_p, Except.toOption, hlt_len, hdrop_eq]
            rcases mergeLoopBin ProtoAuthenticator.mergeField (rest0.length - (rest0.length - len.toNat)) x.msg rest0 (rest0.length - len.toNat) 96 with _ | m' <;> rfl
        apply SepWPp.of_sepWP_lscro (mid := (blkPl_295).base + 160#64) hinvm
        (conv => arg 4; simp only [decodeVarint2Spec, decodeVarint2SpecGen, hdv0,
          show 0x40 + (0x40 + decodeErrorHookStack) = decodeVarint2Stack from rfl,
          sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc])
        apply SepWP.exists_elim; intro evs_dv
        wp_focus_pure; rintro ⟨hsm0, hsm1⟩
        wp_focus_pure; intro htrm
        wp_focus_pure; intro hevs_dv
        have hevs_nil := decodeVarint2Env_eq_nil hdv0 hevs_dv
        subst hevs_nil
        conv => arg 4; dsimp only [AllocCostModel.stepEvents, List.foldl]; simp only [arm64_norm]
        apply SepWP.fold (skipBelow3_leaf_entails s0.sp 97 (by decide)) (by sep_focus)
        apply SepWP.fold (authenticatorPBCapAt_mono A.repAlloc x.msgPtr x.msg hrest0_le) (by sep_focus)
        conv => arg 4; rw [sliceCursorAfter_eq_split hrest0_le hrest0_suf, sliceCursorAt]; simp only [sepConj_assoc]
        wp_steps_sync_pool ((blkPl_295).base + 160#64)
        simp only [State.setMem_setMem]
        wp_reach; intro hinvm
        refine SepWPp.weaken_pre (P' :=
          authBudgetLoopPre A lim st0 s0 _ x.msgPtr x.bufRef x.slot x.ptr x.msg x.bs rest0)
          (Entails.of_eq (by
            dsimp only [authBudgetLoopPre]
            rw [sliceCursorAfter_eq_split hrest0_le hrest0_suf, sliceCursorAt]
            sep_ac_rfl)) ?_
        exact auth_loop_base_ok_cl_placed hFromCall hPushCall hVarintCall hSkipCall hBytesCall
          hFit0 (hPost x) hsp_align h hlim_lt
          rest0.length x.msg rest0 [] st0 _ (Nat.le_refl _) hrest0_le hrest0_suf rfl .nil hres0
          (by simp only [arm64_norm]) (by simp only [arm64_norm, hrunm])
          (by simp only [arm64_norm, hspm]) (by simp only [arm64_norm, htrm])
          (by simp only [arm64_norm, hx19_m]) (by simp only [arm64_norm, hx20_m])
          (by simp only [arm64_norm]) (by simp only [arm64_norm, hsm1, hsub])
          ⟨by simp only [arm64_norm, hx23_m], by simp only [arm64_norm, hx24_m],
           by simp only [arm64_norm, hx25_m], by simp only [arm64_norm, hx26_m],
           by simp only [arm64_norm, hx27_m], by simp only [arm64_norm, hx28_m],
           by simp only [arm64_norm, hvregs_m]⟩ hinvm
  · have hbeq := wt_beq_two_of_ne_lengthDelimited h_1 hwt_ld
    have hbne1 : (BitVec.truncate 32 (s0.readReg64 (Reg.gpr 0#5)) &&& 255#32 != 2#32) = true := by
      simp only [bne, hbeq, Bool.not_false]
    have hbne2 : (BitVec.truncate 32 (BitVec.zeroExtend 64 (BitVec.truncate 32 (s0.readReg64 (Reg.gpr 0#5))) &&& 255#64) != 2#32) = true := by
      rw [truncate32_zeroExtend64_and_255_eq, h_1]
      cases hxwt : x.wt <;> first | exact absurd hxwt hwt_ld | decide
    have hbne3 : (BitVec.truncate 32 (BitVec.zeroExtend 64 (BitVec.truncate 32 (s0.readReg64 (Reg.gpr 0#5)) &&& 255#32)) != 2#32) = true := by
      rw [← hbne1]; congr 2; bv_bits
    have hnone : (mergeMessage ProtoAuthenticator.mergeField (codecWireTypeToProto x.wt) x.msg x.bs 97).toOption = none := by
      rw [← mergeMessageBin_eq_proto_mergeMessage protoPrefixStep_protoAuthenticator_mergeField]
      cases hxwt : x.wt <;> first | exact absurd hxwt hwt_ld | rfl
    apply SepWPp.of_sepWP_lscro (mid := (blkPl_295).base + 100#64) hinv0
    conv => arg 4; rw [authMergeStack, stackAt_skipField3 s0.sp 97 (by decide), sliceCursorAt, memRegion_48_wtErr96 s0.sp]; simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
    apply SepWP.exists_elim; intro v19; apply SepWP.exists_elim; intro v20
    apply SepWP.exists_elim; intro v21; apply SepWP.exists_elim; intro v22
    apply SepWP.exists_elim; intro v_lr; apply SepWP.exists_elim; intro v_fp
    apply SepWP.exists_elim; intro b_wt1; apply SepWP.exists_elim; intro b_wt0
    apply SepWP.exists_elim; intro v_wt0
    wp_steps_sync_pool ((blkPl_295).base + 100#64)
    simp only [State.setMem_setMem]
    apply SepWP.fold (wtErr96_entails_memRegion40 s0.sp _ _) (by sep_focus)
    apply SepWP.fold (pointsTo64_pair_entails_memRegion16 x.slot x.ptr (BitVec.ofNat 64 x.bs.length)) (by sep_focus)
    apply SepWP.fold (authenticatorPBCapAt_entails_authenticatorPBAt A.repAlloc x.msgPtr x.bs.length x.msg) (by sep_focus)
    wp_reach; intro hinv0'
    refine SepWPp.weaken_pre (Entails.of_eq (by dsimp only [authBudgetErrFrame]; sep_ac_rfl))
      (auth_from_err_exit_cl_placed (m := x.msg) (v_stk0 := v_wt0) hFromCall hnone
        (by decide : KindNoHeap 0x8000000000000006#64)
        (fun evs_f hf => hFit0 evs_f ((authMergeLoopEnv_of_decodeErrorFrom hf).mono (by omega) (by omega)))
        (fun evs_f hf => ⟨evs_f, hpost_err0 hnone (authMergeLoopEnv_of_decodeErrorFrom hf), rfl⟩)
        hsp_align
        (by simp only [arm64_norm]) (by simp only [arm64_norm, hrun])
        (by simp only [arm64_norm]) (by simp only [arm64_norm])
        (by simp only [arm64_norm])
        ⟨by simp only [arm64_norm], by simp only [arm64_norm],
         by simp only [arm64_norm], by simp only [arm64_norm],
         by simp only [arm64_norm], by simp only [arm64_norm],
         by simp only [arm64_norm]⟩ hinv0')

/-- `withLsCodeRoLoaded` correctness of `Authenticator::merge` (block 295) against `MergeBaseBudget.authMergeSpec`. -/
theorem auth_merge_base_cl_placed_ok_of_cro_contracts [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {H : LibsignalHooks}
    (hFromCall : subroutine_ok ((blkPC_295).rebase (blkPl_295).base H) (lsmpl.base 261)
      (withLsCodeRoLoaded lsmpl (decodeErrorFromBudgetSpec M A lim)))
    (hPushCall : subroutine_ok ((blkPC_295).rebase (blkPl_295).base H) (lsmpl.base 257)
      (withLsCodeRoLoaded lsmpl (decodeErrorPushMergeBudgetSpec M A lim)))
    (hVarintCall : subroutine_ok ((blkPC_295).rebase (blkPl_295).base H) (lsmpl.base 291)
      (withLsCodeRoLoaded lsmpl (decodeVarint2Spec A lim)))
    (hSkipCall : subroutine_ok ((blkPC_295).rebase (blkPl_295).base H) (lsmpl.base 263)
      (withLsCodeRoLoaded lsmpl (skipField3Spec A lim)))
    (hBytesCall : subroutine_ok ((blkPC_295).rebase (blkPl_295).base H) (lsmpl.base 290)
      (withLsCodeRoLoaded lsmpl (bytesMerge3RawBudgetSpec A lim))) :
    subroutine_ok ((blkPC_295).rebase (blkPl_295).base H)
      (blkPl_295).base
      (withLsCodeRoLoaded lsmpl (authMergeSpec A lim)) :=
  auth_merge_base_cl_placed_ok_of_cro_contracts_env
    (fun _ _ h => h) (fun _ _ h => h)
    hFromCall hPushCall hVarintCall hSkipCall hBytesCall

/-- `withLsCodeLoaded` correctness of `Authenticator::merge` (block 295) against `MergeBaseBudget.authMergeSpec`. -/
theorem auth_merge_base_cl_placed_ok_of_contracts [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {H : LibsignalHooks}
    (hFromCall : subroutine_ok ((blkPC_295).rebase (blkPl_295).base H) (lsmpl.base 261)
      (withLsCodeLoaded lsmpl (decodeErrorFromBudgetSpec M A lim)))
    (hPushCall : subroutine_ok ((blkPC_295).rebase (blkPl_295).base H) (lsmpl.base 257)
      (withLsCodeLoaded lsmpl (decodeErrorPushMergeBudgetSpec M A lim)))
    (hVarintCall : subroutine_ok ((blkPC_295).rebase (blkPl_295).base H) (lsmpl.base 291)
      (withLsCodeLoaded lsmpl (decodeVarint2Spec A lim)))
    (hSkipCall : subroutine_ok ((blkPC_295).rebase (blkPl_295).base H) (lsmpl.base 263)
      (withLsCodeLoaded lsmpl (skipField3Spec A lim)))
    (hBytesCall : subroutine_ok ((blkPC_295).rebase (blkPl_295).base H) (lsmpl.base 290)
      (withLsCodeRoLoaded lsmpl (bytesMerge3RawBudgetSpec A lim))) :
    subroutine_ok ((blkPC_295).rebase (blkPl_295).base H)
      (blkPl_295).base
      (withLsCodeRoLoaded lsmpl (authMergeSpec A lim)) :=
  auth_merge_base_cl_placed_ok_of_cro_contracts
    (subroutine_ok_withLsCodeRoLoaded_of_withLsCodeLoaded hFromCall)
    (subroutine_ok_withLsCodeRoLoaded_of_withLsCodeLoaded hPushCall)
    (subroutine_ok_withLsCodeRoLoaded_of_withLsCodeLoaded hVarintCall)
    (subroutine_ok_withLsCodeRoLoaded_of_withLsCodeLoaded hSkipCall)
    hBytesCall

end LibsignalBinary.Proofs.SpqrV1.Auth.MergeBaseClPlacedBudget
