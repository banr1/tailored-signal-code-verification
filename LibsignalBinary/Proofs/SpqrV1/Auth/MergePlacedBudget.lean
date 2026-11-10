/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SpqrV1.Auth.MergePlacedBudgetAux
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
# Budget-Threaded `[LibsignalPlacement]` Proof of `Authenticator::merge` (Block `295`)

Loop exit, key decode, loop induction (`auth_loop_ok_cl_placed`), and top-level
`[LibsignalPlacement]` subroutine contracts for
`prost::encoding::message::merge::<Authenticator, &mut &[u8]> [local#2]` (Block `295`)
against `withLsCodeRoLoaded lsmpl (authMergeSpec A lim)`.
-/

@[expose] public section

set_option autoImplicit false

namespace LibsignalBinary.Proofs.SpqrV1.Auth.MergePlacedBudget

open Arm64 ProofLib SepProp
open scoped CryptoVerification
open scoped CryptoVerification.CodeLayout
open CryptoVerification (LibsignalHooks LibsignalPlacement blkPC_295 blkPl_295 lsmpl withLsCodeLoaded)
open CryptoVerification.LibsignalProtoCodec
  (WireType decodeVarint decodeVarint_length mergeBytes skipField skip_length)
open CryptoVerification.LibsignalTripleRatchet
  (KindNoHeap LibsignalCodeRoLoaded decodeErrorAtStackLen decodeErrorHookStack
   extract_withLsCodeRoLoaded subroutine_ok_withLsCodeRoLoaded_of_plain
   subroutine_ok_withLsCodeRoLoaded_of_withLsCodeLoaded withLsCodeRoLoaded)
open CryptoVerification.LibsignalTripleRatchet.Prost
  (HighCalleeSaved IsDropSuffix bv32_zeroExtend_ofNat decodeVarint_suffix itag_beq_tag_false
   key_shr32_of_ge key_shr32_of_lt key_wt_none key_wt_some memRegion_48_split2
   pointsTo64_memRegion32_entails_40 pointsTo64_pair_entails_memRegion16 pointsToBytes_prefix_join
   sf_truncate32_ofNat64 skip_suffix sliceCursorAfter sliceCursorAfter_eq_split sliceCursorAfter_join
   sliceCursorAt suffix_trans tag_cbz_false ule_len_of_ge ule_len_of_lt w1_tag_eq)
open CryptoVerification.LibsignalTripleRatchet.Prost.BytesMergeFacts
  (truncate32_zeroExtend64_and_255_eq)
open CryptoVerification.SpqrV1.Varint
  (decodeVarint2Stack skipBelow3 skipBelow3_leaf skipBelow3_leaf_entails stackAt_skipField3)
open CryptoVerification.SpqrV1.Prost.BytesMerge (proto_decodeVarint_toOption)
open CryptoVerification.SpqrV1.Prost.MessageMerge
  (SepWPp.call_frame_lscro SepWPp.of_sepWP_lscro bv_len_sub_limit cmp_len_limit_of_eq
   cmp_len_limit_of_gt cmp_len_limit_of_lt codecWireTypeToProto memRegion_48_wtErr96 mergeLoopBin
   mergeLoopBin_eq_limit mergeLoopBin_lt_limit mergeLoopBin_of_decodeVarint_none
   mergeLoopBin_of_key_ge mergeLoopBin_of_key_ok mergeLoopBin_of_tag_zero mergeLoopBin_of_wt_none
   mergeMessageBin mergeMessageBin_eq_proto_mergeMessage protoPrefixStep_protoAuthenticator_mergeField
   wtErr96_entails_memRegion40 wt_beq_two_of_lengthDelimited wt_beq_two_of_ne_lengthDelimited)
open CryptoVerification.LibsignalSpqrV1 (ProtoAuthenticator)
open CryptoVerification.LibsignalSpqrV1.Proto (mergeMessage)
open CryptoVerification.SpqrV1.Auth
  (AuthMergeGhost WppPost authMergeStack authenticatorPBCapAt
   authenticatorPBCapAt_entails_authenticatorPBAt authenticatorPBCapAt_mono bv64_add_zero
   bv64_sub_zero memRegion_48_split_96 mergeBytes_length mergeBytes_suffix
   protoAuthenticator_mergeField_other protoAuthenticator_mergeField_tag1
   protoAuthenticator_mergeField_tag2)
open LibsignalBinary.Heap
  (AllocCostModel AllocEvent BudgetLimits FitsEnv RustCliAllocBudget)
open LibsignalBinary.Heap.SpecBudget
  (DecodeErrorFromEnv DecodeErrorPushEnv decodeErrorFromBudgetSpec decodeErrorPushBudgetSpec)
open LibsignalBinary.Proofs.Placed.BudgetPoolSync (hooksException sepWP_seg_ls_vm)
open LibsignalBinary.Proofs.SpqrV1.Auth.MergeBaseBudget (authMergeSpecOfEnv)
open LibsignalBinary.Proofs.SpqrV1.Auth.MergePlacedBudgetAux
  (AuthPlacedMergeEnv AuthPlacedMergeIterEnv AuthPlacedMergeLoopEnv AuthPlacedMergePostEnv
   authBudgetErrFrame authBudgetLoopPre authMergeSpec auth_err0_ret_exit_placed
   auth_from_err_exit_cl_placed auth_skip_step_cl_placed auth_tag1_step_cl_placed
   auth_tag2_step_cl_placed stepEvents_append)
open LibsignalBinary.Proofs.SpqrV1.Prost.MessageMerge.PolyCommonBudget
  (BytesMerge3Env WppBudgetPanic bytesMerge3RawBudgetSpec wppBudgetPanic_false)
open LibsignalBinary.Proofs.SpqrV1.Varint.DecodeVarint2Budget
  (DecodeVarint2Env decodeVarint2Spec decodeVarint2SpecGen)
open LibsignalBinary.Proofs.SpqrV1.Varint.SkipField3Budget (SkipField3Env skipField3Spec)
open LibsignalBinary.Proofs.TripleRatchet.Prost.DefsBudget
  (DecodeVarintSliceEnv decodeVarintSliceEvents)

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

private theorem decodeVarint2Env_eq_nil {bs : List (BitVec 8)} {v : BitVec 64}
    {rest : List (BitVec 8)} {evs : List AllocEvent}
    (hd : decodeVarint bs = some (v, rest)) (hdv : DecodeVarint2Env bs evs) :
    evs = [] := by
  change DecodeVarintSliceEnv bs evs at hdv
  simpa [DecodeVarintSliceEnv, decodeVarintSliceEvents, hd] using hdv

theorem SepWPp.to_subroutineOutcome_auth_placed [LibsignalPlacement]
    {M : AllocCostModel} {prog : Program} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {PreEnv PostEnv : AuthMergeGhost → List AllocEvent → Prop}
    {x : AuthMergeGhost} {st0 : M.σ} {s0 : State} {P R : SepProp}
    (hm : s0.mem ⊨ P ∗ R) (hL : prog.CodeLoaded s0.mem)
    (h : SepWPp prog (s0.readReg64 .lr) s0 P
      (WppPost (authMergeSpecOfEnv A lim PreEnv PostEnv) (x, st0) R s0)
      (WppBudgetPanic (authMergeSpecOfEnv A lim PreEnv PostEnv) (x, st0) R s0)) :
    ∃ sf, Steps prog s0 sf ∧
      SubroutineOutcome (withLsCodeRoLoaded lsmpl (authMergeSpecOfEnv A lim PreEnv PostEnv))
        (x, st0) R s0 sf := by
  obtain ⟨sf, hsteps, ⟨hpc, hrun, P_f, hmf, hpost, hsp, hcs⟩ | ⟨hpan, P_f, hmf, hpanic⟩ | ⟨_, hfalse⟩⟩ :=
    h R hm hL
  · exact ⟨sf, hsteps, Or.inl ⟨⟨hpc, hsp, hrun⟩, ⟨hsp, hcs⟩, hpost hmf⟩⟩
  · exact ⟨sf, hsteps, Or.inr (Or.inl ⟨hpan, hpanic hmf⟩)⟩
  · exact False.elim (not_satisfies_false_sepConj hfalse)

/-! ## Loop Exit, Key Decode, and Main Loop Induction -/

set_option maxRecDepth 200000 in
set_option maxHeartbeats 400000 in
set_option linter.unusedSimpArgs false in
theorem auth_loop_le_exit_cl_placed [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {H : LibsignalHooks}
    {PreEnv PostEnv : AuthMergeGhost → List AllocEvent → Prop}
    (hFromCall : subroutine_ok ((blkPC_295).rebase (blkPl_295).base H) (lsmpl.base 261)
      (withLsCodeRoLoaded lsmpl (decodeErrorFromBudgetSpec M A lim)))
    {x : AuthMergeGhost} {st0 st_cur : M.σ} {R : SepProp} {s0 s : State}
    {m : ProtoAuthenticator} {cur : List (BitVec 8)} {limit : Nat}
    (hle_lim : cur.length ≤ limit) (hsp_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hcur_le : cur.length ≤ x.bs.length) (hcur_suf : IsDropSuffix x.bs cur) (hlim_lt : limit < 2 ^ 63)
    (hevs_ok : cur.length = limit →
      ((mergeMessage ProtoAuthenticator.mergeField (codecWireTypeToProto x.wt) x.msg x.bs 97).toOption =
        some (m, cur)) →
      ∃ evs, PostEnv x evs ∧ st_cur = M.stepEvents evs st0)
    (hfits_lt : cur.length < limit → FitsEnv M lim st_cur DecodeErrorFromEnv)
    (hevs_lt : cur.length < limit → ∀ evs_f, DecodeErrorFromEnv evs_f →
      ∃ evs, PostEnv x evs ∧ M.stepEvents evs_f st_cur = M.stepEvents evs st0)
    (hres_cur : (mergeMessage ProtoAuthenticator.mergeField (codecWireTypeToProto x.wt) x.msg x.bs 97).toOption =
      (mergeLoopBin ProtoAuthenticator.mergeField (cur.length - limit) m cur limit 96).map
        (fun m' => (m', x.bs.drop (x.bs.length - limit))))
    (hpc : s.pc = (blkPl_295).base + 160#64)
    (hrun : s.status = .Running) (hsp : s.sp = s0.sp - 96#64)
    (htr : s.trace = s0.trace) (hx21 : s.readReg64 (Reg.gpr 21#5) = x.slot)
    (hx22 : s.readReg64 (Reg.gpr 22#5) = BitVec.ofNat 64 limit)
    (hcs : HighCalleeSaved s0 s) (hinv : LibsignalCodeRoLoaded lsmpl s.mem) :
    SepWPp ((blkPC_295).rebase (blkPl_295).base H) (s0.readReg64 Reg.lr) s
      (authBudgetLoopPre A lim st_cur s0 s x.msgPtr x.bufRef x.slot x.ptr m x.bs cur)
      (WppPost (authMergeSpecOfEnv A lim PreEnv PostEnv) (x, st0) R s0)
      (WppBudgetPanic (authMergeSpecOfEnv A lim PreEnv PostEnv) (x, st0) R s0) := by
  obtain ⟨hx23, hx24, hx25, hx26, hx27, hx28, hvregs⟩ := hcs
  let curPtr : BitVec 64 := x.ptr + BitVec.ofNat 64 (x.bs.length - cur.length)
  by_cases heq_lim : cur.length = limit
  · obtain ⟨hcmp1, hcmp2, hcmp3⟩ := cmp_len_limit_of_eq heq_lim
    have hcur_eq_drop : x.bs.drop (x.bs.length - limit) = cur := by
      rw [← heq_lim]; exact hcur_suf.symm
    have hsome : (mergeMessage ProtoAuthenticator.mergeField (codecWireTypeToProto x.wt) x.msg x.bs 97).toOption =
        some (m, cur) := by
      rw [hres_cur, mergeLoopBin_eq_limit _ _ _ _ _ _ heq_lim, Option.map_some, hcur_eq_drop]
    obtain ⟨evs, hevs_post, rfl⟩ := hevs_ok heq_lim hsome
    apply SepWPp.of_sepWP_ret
    unfold WppPost authMergeSpecOfEnv
    simp only [hsome, authMergeStack, stackAt_skipField3 _ 97 (by decide), authBudgetLoopPre,
      sliceCursorAfter_eq_split hcur_le hcur_suf, sliceCursorAt,
      sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc, arm64_norm, htr, hsp]
    wp_steps_sync_pool (s0.readReg64 Reg.lr)
    simp only [State.setMem_setMem]
    wp_done
  · have hlt_lim : cur.length < limit := Nat.lt_of_le_of_ne hle_lim heq_lim
    obtain ⟨hcmp1, hcmp2, hcmp3⟩ := cmp_len_limit_of_lt hlt_lim hlim_lt
    have hnone : (mergeMessage ProtoAuthenticator.mergeField (codecWireTypeToProto x.wt) x.msg x.bs 97).toOption = none := by
      rw [hres_cur, mergeLoopBin_lt_limit _ _ _ _ _ _ hlt_lim, Option.map_none]
    apply SepWPp.of_sepWP_lscro (mid := (blkPl_295).base + 100#64) hinv
    conv => arg 4; rw [authBudgetLoopPre, sliceCursorAfter_eq_split hcur_le hcur_suf,
      sliceCursorAt, memRegion_48_split_96 s0.sp]
    simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
    apply SepWP.exists_elim; intro v_stk0
    wp_steps_sync_pool ((blkPl_295).base + 100#64)
    simp only [State.setMem_setMem]
    apply SepWP.fold (pointsTo64_pair_entails_memRegion16 x.slot curPtr (BitVec.ofNat 64 cur.length)) (by sep_focus)
    apply SepWP.fold (pointsToBytes_prefix_join hcur_le hcur_suf) (by sep_focus)
    apply SepWP.fold (authenticatorPBCapAt_entails_authenticatorPBAt A.repAlloc x.msgPtr cur.length m) (by sep_focus)
    wp_reach; intro hinv'
    refine SepWPp.weaken_pre (P' :=
      ((s0.sp - 96#64) ↦₆₄ v_stk0) ∗ memRegion (s0.sp - 88#64) 40 ∗
        skipBelow3 s0.sp 97 ∗ authBudgetErrFrame A lim st_cur s0 _ x.msgPtr x.bufRef x.slot x.ptr m x.bs)
      (Entails.of_eq (by dsimp only [authBudgetErrFrame]; sep_ac_rfl)) ?_
    exact auth_from_err_exit_cl_placed hFromCall hnone
      (by decide : KindNoHeap 0x8000000000000008#64)
      (hfits_lt hlt_lim) (hevs_lt hlt_lim) hsp_align
      (by simp only [arm64_norm]) (by simp only [arm64_norm, hrun])
      (by simp only [arm64_norm, hsp]) (by simp only [arm64_norm, htr])
      (by simp only [arm64_norm])
      ⟨by simp only [arm64_norm, hx23], by simp only [arm64_norm, hx24],
       by simp only [arm64_norm, hx25], by simp only [arm64_norm, hx26],
       by simp only [arm64_norm, hx27], by simp only [arm64_norm, hx28],
       by simp only [arm64_norm, hvregs]⟩ hinv'

set_option maxRecDepth 200000 in
set_option maxHeartbeats 400000 in
set_option linter.unusedSimpArgs false in
theorem auth_decode_key_step_cl_placed [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {H : LibsignalHooks}
    {PreEnv PostEnv : AuthMergeGhost → List AllocEvent → Prop}
    (hFromCall : subroutine_ok ((blkPC_295).rebase (blkPl_295).base H) (lsmpl.base 261)
      (withLsCodeRoLoaded lsmpl (decodeErrorFromBudgetSpec M A lim)))
    (hVarintCall : subroutine_ok ((blkPC_295).rebase (blkPl_295).base H) (lsmpl.base 291)
      (withLsCodeRoLoaded lsmpl (decodeVarint2Spec A lim)))
    {x : AuthMergeGhost} {st0 st_cur : M.σ} {R : SepProp} {s0 s : State}
    {m : ProtoAuthenticator} {cur : List (BitVec 8)} {limit : Nat}
    (hgt_lim : ¬ cur.length ≤ limit) (hsp_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hcur_le : cur.length ≤ x.bs.length) (hcur_lt : cur.length < 2 ^ 63) (hcur_suf : IsDropSuffix x.bs cur)
    (hfits_dv : FitsEnv M lim st_cur (DecodeVarint2Env cur))
    (hevs_dv_err : decodeVarint cur = none → ∀ evs_dv, DecodeVarint2Env cur evs_dv →
      ∃ evs, PostEnv x evs ∧ M.stepEvents evs_dv st_cur = M.stepEvents evs st0)
    (hfits_from : FitsEnv M lim st_cur DecodeErrorFromEnv)
    (hevs_from :
      (mergeMessage ProtoAuthenticator.mergeField (codecWireTypeToProto x.wt) x.msg x.bs 97).toOption = none →
      ∀ evs_f, DecodeErrorFromEnv evs_f →
        ∃ evs, PostEnv x evs ∧ M.stepEvents evs_f st_cur = M.stepEvents evs st0)
    (hres_cur : (mergeMessage ProtoAuthenticator.mergeField (codecWireTypeToProto x.wt) x.msg x.bs 97).toOption =
      (mergeLoopBin ProtoAuthenticator.mergeField (cur.length - limit) m cur limit 96).map
        (fun m' => (m', x.bs.drop (x.bs.length - limit))))
    (hcont : ∀ (key : BitVec 64) (iwt : WireType) (rest : List (BitVec 8)) (s' : State),
      decodeVarint cur = some (key, rest) → ¬ 2 ^ 32 ≤ key.toNat →
      WireType.ofNat? (key.toNat % 8) = some iwt → ¬ key.toNat / 8 < 1 →
      s'.pc = (blkPl_295).base + 212#64 →
      s'.status = .Running → s'.sp = s0.sp - 96#64 → s'.trace = s0.trace →
      s'.readReg64 (Reg.gpr 0#5) = BitVec.ofNat 64 iwt.toNat →
      s'.readReg64 (Reg.gpr 1#5) = BitVec.ofNat 64 (key.toNat / 8) →
      s'.readReg64 (Reg.gpr 19#5) = x.bufRef → s'.readReg64 (Reg.gpr 20#5) = x.msgPtr →
      s'.readReg64 (Reg.gpr 21#5) = x.slot → s'.readReg64 (Reg.gpr 22#5) = BitVec.ofNat 64 limit →
      HighCalleeSaved s0 s' → LibsignalCodeRoLoaded lsmpl s'.mem →
      SepWPp ((blkPC_295).rebase (blkPl_295).base H) (s0.readReg64 Reg.lr) s'
        (authBudgetLoopPre A lim st_cur s0 s' x.msgPtr x.bufRef x.slot x.ptr m x.bs rest)
        (WppPost (authMergeSpecOfEnv A lim PreEnv PostEnv) (x, st0) R s0)
        (WppBudgetPanic (authMergeSpecOfEnv A lim PreEnv PostEnv) (x, st0) R s0))
    (hpc : s.pc = (blkPl_295).base + 160#64)
    (hrun : s.status = .Running) (hsp : s.sp = s0.sp - 96#64)
    (htr : s.trace = s0.trace) (hx19 : s.readReg64 (Reg.gpr 19#5) = x.bufRef)
    (hx20 : s.readReg64 (Reg.gpr 20#5) = x.msgPtr) (hx21 : s.readReg64 (Reg.gpr 21#5) = x.slot)
    (hx22 : s.readReg64 (Reg.gpr 22#5) = BitVec.ofNat 64 limit)
    (hcs : HighCalleeSaved s0 s) (hinv : LibsignalCodeRoLoaded lsmpl s.mem) :
    SepWPp ((blkPC_295).rebase (blkPl_295).base H) (s0.readReg64 Reg.lr) s
      (authBudgetLoopPre A lim st_cur s0 s x.msgPtr x.bufRef x.slot x.ptr m x.bs cur)
      (WppPost (authMergeSpecOfEnv A lim PreEnv PostEnv) (x, st0) R s0)
      (WppBudgetPanic (authMergeSpecOfEnv A lim PreEnv PostEnv) (x, st0) R s0) := by
  obtain ⟨hx23, hx24, hx25, hx26, hx27, hx28, hvregs⟩ := hcs
  obtain ⟨hcmp1, hcmp2⟩ := cmp_len_limit_of_gt hgt_lim hcur_lt
  let curPtr : BitVec 64 := x.ptr + BitVec.ofNat 64 (x.bs.length - cur.length)
  apply SepWPp.of_sepWP_lscro (mid := lsmpl.base 291) hinv
  conv => arg 4; rw [authBudgetLoopPre, sliceCursorAfter_eq_split hcur_le hcur_suf,
    sliceCursorAt, skipBelow3_leaf s0.sp 97 (by decide)]; simp only [sepConj_assoc]
  wp_steps_sync_pool (lsmpl.base 291)
  simp only [State.setMem_setMem]
  wp_reach; intro hinv
  refine SepWPp.call_frame_lscro (spec := decodeVarint2Spec A lim)
    (x := (⟨x.bufRef, x.slot, curPtr, cur⟩, st_cur))
    (ret_pc := (blkPl_295).base + 180#64) hVarintCall hinv
    (by simp only [arm64_norm]) (by simp only [arm64_norm, hrun])
    (by simp only [State.spAligned, hsp, arm64_norm]; exact hsp_align)
    (by simp only [arm64_norm])
    rfl
    ⟨by simp only [arm64_norm, hsp, hx19], hcur_lt, hfits_dv⟩
    (by dsimp only [sliceCursorAt, curPtr]; sep_focus)
    (fun _ _ _ _ hex => False.elim (not_satisfies_false_sepConj hex))
    (fun _ _ => wppBudgetPanic_false) ?_
  intro sm hpcm hrunm hspm hcsm hinvm
  simp only [CalleeSavedPreserved] at hcsm
  obtain ⟨hx19_m, hx20_m, hx21_m, hx22_m, hx23_m, hx24_m, hx25_m, hx26_m, hx27_m, hx28_m, hfp_m, hvregs_m⟩ := hcsm
  simp (config := { decide := true }) only [arm64_norm, hsp, hx19, hx20, hx21, hx22, hx23, hx24, hx25, hx26, hx27, hx28, hvregs]
    at hpcm hrunm hspm hx19_m hx20_m hx21_m hx22_m hx23_m hx24_m hx25_m hx26_m hx27_m hx28_m hfp_m hvregs_m
  cases hd : decodeVarint cur with
  | none =>
    have hnone : (mergeMessage ProtoAuthenticator.mergeField (codecWireTypeToProto x.wt) x.msg x.bs 97).toOption = none := by
      rw [hres_cur, mergeLoopBin_of_decodeVarint_none protoPrefixStep_protoAuthenticator_mergeField hgt_lim hd, Option.map_none]
    apply SepWPp.of_sepWP_lscro (mid := (blkPl_295).base + 116#64) hinvm
    (conv => arg 4; simp only [decodeVarint2Spec, decodeVarint2SpecGen, hd,
      show 0x40 + (0x40 + decodeErrorHookStack) = decodeVarint2Stack from rfl,
      sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc])
    apply SepWP.exists_elim; intro evs_dv
    wp_focus_pure; intro hsm0
    wp_focus_pure; intro htrm
    wp_focus_pure; intro hevs_dv
    wp_focus_pure; intro hsm1
    conv => arg 4; simp only [arm64_norm, hsp]
    apply SepWP.fold (skipBelow3_leaf_entails s0.sp 97 (by decide)) (by sep_focus)
    apply SepWP.fold (pointsToBytes_prefix_join hcur_le hcur_suf) (by sep_focus)
    apply SepWP.fold (authenticatorPBCapAt_entails_authenticatorPBAt A.repAlloc x.msgPtr cur.length m) (by sep_focus)
    wp_steps_sync_pool ((blkPl_295).base + 116#64)
    simp only [State.setMem_setMem]
    wp_reach; intro _hinvm'
    refine SepWPp.weaken_pre (P' :=
      decodeErrorAtStackLen A.repAlloc (sm.readReg64 (Reg.gpr 1#5)) 0 ∗ memRegion (s0.sp - 96#64) 48 ∗
        skipBelow3 s0.sp 97 ∗ authBudgetErrFrame A lim (M.stepEvents evs_dv st_cur) s0 _ x.msgPtr x.bufRef x.slot x.ptr m x.bs)
      (Entails.of_eq (by dsimp only [authBudgetErrFrame]; sep_ac_rfl)) ?_
    exact auth_err0_ret_exit_placed hnone (hevs_dv_err hd evs_dv hevs_dv) hsp_align
      (by simp only [arm64_norm]) (by simp only [arm64_norm, hrunm])
      (by simp only [arm64_norm, hspm]) (by simp only [arm64_norm, htrm, htr])
      (by simp only [arm64_norm]) hsm1
      ⟨by simp only [arm64_norm, hx23_m], by simp only [arm64_norm, hx24_m],
       by simp only [arm64_norm, hx25_m], by simp only [arm64_norm, hx26_m],
       by simp only [arm64_norm, hx27_m], by simp only [arm64_norm, hx28_m],
       by simp only [arm64_norm, hvregs_m]⟩
  | some p =>
    rcases p with ⟨key, rest⟩
    have hrest_lt_cur : rest.length < cur.length := decodeVarint_length hd
    have hrest_le_cur : rest.length ≤ cur.length := Nat.le_of_lt hrest_lt_cur
    have hrest_le : rest.length ≤ x.bs.length := Nat.le_trans hrest_le_cur hcur_le
    have hrest_suf : IsDropSuffix x.bs rest := suffix_trans hcur_le hcur_suf hrest_le_cur (decodeVarint_suffix hd)
    let restPtr : BitVec 64 := x.ptr + BitVec.ofNat 64 (x.bs.length - rest.length)
    by_cases hk_ge : 2 ^ 32 ≤ key.toNat
    · have hnone : (mergeMessage ProtoAuthenticator.mergeField (codecWireTypeToProto x.wt) x.msg x.bs 97).toOption = none := by
        rw [hres_cur, mergeLoopBin_of_key_ge protoPrefixStep_protoAuthenticator_mergeField hgt_lim hd hk_ge, Option.map_none]
      have hshr := key_shr32_of_ge hk_ge
      apply SepWPp.of_sepWP_lscro (mid := (blkPl_295).base + 100#64) hinvm
      (conv => arg 4; simp only [decodeVarint2Spec, decodeVarint2SpecGen, hd,
        show 0x40 + (0x40 + decodeErrorHookStack) = decodeVarint2Stack from rfl,
        sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc])
      apply SepWP.exists_elim; intro evs_dv
      wp_focus_pure; rintro ⟨hsm0, hsm1⟩
      wp_focus_pure; intro htrm
      wp_focus_pure; intro hevs_dv
      have hevs_nil := decodeVarint2Env_eq_nil hd hevs_dv
      subst hevs_nil
      conv => arg 4; dsimp only [AllocCostModel.stepEvents, List.foldl]; simp only [arm64_norm, hsp]
      apply SepWP.fold (skipBelow3_leaf_entails s0.sp 97 (by decide)) (by sep_focus)
      apply SepWP.fold (sliceCursorAfter_join hcur_le hcur_suf hrest_le_cur) (by sep_focus)
      apply SepWP.fold (authenticatorPBCapAt_entails_authenticatorPBAt A.repAlloc x.msgPtr cur.length m) (by sep_focus)
      conv => arg 4; rw [sliceCursorAfter_eq_split hrest_le hrest_suf, sliceCursorAt, memRegion_48_split2 s0.sp]
      simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
      apply SepWP.exists_elim; intro v_err0; apply SepWP.exists_elim; intro v_err1
      wp_steps_sync_pool ((blkPl_295).base + 100#64)
      simp only [State.setMem_setMem]
      apply SepWP.fold (pointsTo64_pair_entails_memRegion16 x.slot restPtr (BitVec.ofNat 64 rest.length)) (by sep_focus)
      apply SepWP.fold (pointsToBytes_prefix_join hrest_le hrest_suf) (by sep_focus)
      have h40 := pointsTo64_memRegion32_entails_40 s0.sp key
      rw [← bv_sub_add_lit s0.sp 96 8] at h40
      apply SepWP.fold h40 (by sep_focus)
      wp_reach; intro hinvm'
      refine SepWPp.weaken_pre (P' :=
        ((s0.sp - 96#64) ↦₆₄ v_err1) ∗ memRegion (s0.sp - 88#64) 40 ∗
          skipBelow3 s0.sp 97 ∗ authBudgetErrFrame A lim st_cur s0 _ x.msgPtr x.bufRef x.slot x.ptr m x.bs)
        (Entails.of_eq (by dsimp only [authBudgetErrFrame]; sep_ac_rfl)) ?_
      exact auth_from_err_exit_cl_placed hFromCall hnone
        (by decide : KindNoHeap 0x8000000000000004#64)
        hfits_from (hevs_from hnone) hsp_align
        (by simp only [arm64_norm]) (by simp only [arm64_norm, hrunm])
        (by simp only [arm64_norm, hspm]) (by simp only [arm64_norm, htrm, htr])
        (by simp only [arm64_norm])
        ⟨by simp only [arm64_norm, hx23_m], by simp only [arm64_norm, hx24_m],
         by simp only [arm64_norm, hx25_m], by simp only [arm64_norm, hx26_m],
         by simp only [arm64_norm, hx27_m], by simp only [arm64_norm, hx28_m],
         by simp only [arm64_norm, hvregs_m]⟩ hinvm'
    · have hshr := key_shr32_of_lt hk_ge
      cases hwt : WireType.ofNat? (key.toNat % 8) with
      | none =>
        have hnone : (mergeMessage ProtoAuthenticator.mergeField (codecWireTypeToProto x.wt) x.msg x.bs 97).toOption = none := by
          rw [hres_cur, mergeLoopBin_of_wt_none protoPrefixStep_protoAuthenticator_mergeField hgt_lim hd hk_ge hwt, Option.map_none]
        obtain ⟨hcs1, hcs2⟩ := key_wt_none hwt
        apply SepWPp.of_sepWP_lscro (mid := (blkPl_295).base + 100#64) hinvm
        (conv => arg 4; simp only [decodeVarint2Spec, decodeVarint2SpecGen, hd,
          show 0x40 + (0x40 + decodeErrorHookStack) = decodeVarint2Stack from rfl,
          sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc])
        apply SepWP.exists_elim; intro evs_dv
        wp_focus_pure; rintro ⟨hsm0, hsm1⟩
        wp_focus_pure; intro htrm
        wp_focus_pure; intro hevs_dv
        have hevs_nil := decodeVarint2Env_eq_nil hd hevs_dv
        subst hevs_nil
        conv => arg 4; dsimp only [AllocCostModel.stepEvents, List.foldl]; simp only [arm64_norm, hsp]
        apply SepWP.fold (skipBelow3_leaf_entails s0.sp 97 (by decide)) (by sep_focus)
        apply SepWP.fold (sliceCursorAfter_join hcur_le hcur_suf hrest_le_cur) (by sep_focus)
        apply SepWP.fold (authenticatorPBCapAt_entails_authenticatorPBAt A.repAlloc x.msgPtr cur.length m) (by sep_focus)
        conv => arg 4; rw [sliceCursorAfter_eq_split hrest_le hrest_suf, sliceCursorAt, memRegion_48_split2 s0.sp]
        simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
        apply SepWP.exists_elim; intro v_err0; apply SepWP.exists_elim; intro v_err1
        wp_steps_sync_pool ((blkPl_295).base + 100#64)
        simp only [State.setMem_setMem]
        apply SepWP.fold (pointsTo64_pair_entails_memRegion16 x.slot restPtr (BitVec.ofNat 64 rest.length)) (by sep_focus)
        apply SepWP.fold (pointsToBytes_prefix_join hrest_le hrest_suf) (by sep_focus)
        have h40 := pointsTo64_memRegion32_entails_40 s0.sp (key &&& 7#64)
        rw [← bv_sub_add_lit s0.sp 96 8] at h40
        apply SepWP.fold h40 (by sep_focus)
        wp_reach; intro hinvm'
        refine SepWPp.weaken_pre (P' :=
          ((s0.sp - 96#64) ↦₆₄ v_err1) ∗ memRegion (s0.sp - 88#64) 40 ∗
            skipBelow3 s0.sp 97 ∗ authBudgetErrFrame A lim st_cur s0 _ x.msgPtr x.bufRef x.slot x.ptr m x.bs)
          (Entails.of_eq (by dsimp only [authBudgetErrFrame]; sep_ac_rfl)) ?_
        exact auth_from_err_exit_cl_placed hFromCall hnone
          (by decide : KindNoHeap 0x8000000000000003#64)
          hfits_from (hevs_from hnone) hsp_align
          (by simp only [arm64_norm]) (by simp only [arm64_norm, hrunm])
          (by simp only [arm64_norm, hspm]) (by simp only [arm64_norm, htrm, htr])
          (by simp only [arm64_norm])
          ⟨by simp only [arm64_norm, hx23_m], by simp only [arm64_norm, hx24_m],
           by simp only [arm64_norm, hx25_m], by simp only [arm64_norm, hx26_m],
           by simp only [arm64_norm, hx27_m], by simp only [arm64_norm, hx28_m],
           by simp only [arm64_norm, hvregs_m]⟩ hinvm'
      | some iwt =>
        obtain ⟨hcc1, hcc2, hand_wt, hcc1_wt, hcc2_wt⟩ := key_wt_some hwt
        obtain ⟨hw1, hw1_2⟩ := w1_tag_eq hk_ge
        obtain ⟨hw1_zext1, hw1_zext2⟩ := bv32_zeroExtend_ofNat (n := key.toNat / 8) (by omega)
        by_cases hitag0 : key.toNat / 8 < 1
        · have hnone : (mergeMessage ProtoAuthenticator.mergeField (codecWireTypeToProto x.wt) x.msg x.bs 97).toOption = none := by
            rw [hres_cur, mergeLoopBin_of_tag_zero protoPrefixStep_protoAuthenticator_mergeField hgt_lim hd hk_ge hwt hitag0, Option.map_none]
          have htag_zero : key.toNat / 8 = 0 := by omega
          apply SepWPp.of_sepWP_lscro (mid := (blkPl_295).base + 100#64) hinvm
          (conv => arg 4; simp only [decodeVarint2Spec, decodeVarint2SpecGen, hd,
            show 0x40 + (0x40 + decodeErrorHookStack) = decodeVarint2Stack from rfl,
            sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc])
          apply SepWP.exists_elim; intro evs_dv
          wp_focus_pure; rintro ⟨hsm0, hsm1⟩
          wp_focus_pure; intro htrm
          wp_focus_pure; intro hevs_dv
          have hevs_nil := decodeVarint2Env_eq_nil hd hevs_dv
          subst hevs_nil
          conv => arg 4; dsimp only [AllocCostModel.stepEvents, List.foldl]; simp only [arm64_norm, hsp]
          apply SepWP.fold (skipBelow3_leaf_entails s0.sp 97 (by decide)) (by sep_focus)
          apply SepWP.fold (sliceCursorAfter_join hcur_le hcur_suf hrest_le_cur) (by sep_focus)
          apply SepWP.fold (authenticatorPBCapAt_entails_authenticatorPBAt A.repAlloc x.msgPtr cur.length m) (by sep_focus)
          conv => arg 4; rw [sliceCursorAfter_eq_split hrest_le hrest_suf, sliceCursorAt, memRegion_48_split_96 s0.sp]
          simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
          apply SepWP.exists_elim; intro v_err0
          wp_steps_sync_pool ((blkPl_295).base + 100#64)
          simp only [State.setMem_setMem]
          apply SepWP.fold (pointsTo64_pair_entails_memRegion16 x.slot restPtr (BitVec.ofNat 64 rest.length)) (by sep_focus)
          apply SepWP.fold (pointsToBytes_prefix_join hrest_le hrest_suf) (by sep_focus)
          wp_reach; intro hinvm'
          refine SepWPp.weaken_pre (P' :=
            ((s0.sp - 96#64) ↦₆₄ v_err0) ∗ memRegion (s0.sp - 88#64) 40 ∗
              skipBelow3 s0.sp 97 ∗ authBudgetErrFrame A lim st_cur s0 _ x.msgPtr x.bufRef x.slot x.ptr m x.bs)
            (Entails.of_eq (by dsimp only [authBudgetErrFrame]; sep_ac_rfl)) ?_
          exact auth_from_err_exit_cl_placed hFromCall hnone
            (by decide : KindNoHeap 0x8000000000000005#64)
            hfits_from (hevs_from hnone) hsp_align
            (by simp only [arm64_norm]) (by simp only [arm64_norm, hrunm])
            (by simp only [arm64_norm, hspm]) (by simp only [arm64_norm, htrm, htr])
            (by simp only [arm64_norm])
            ⟨by simp only [arm64_norm, hx23_m], by simp only [arm64_norm, hx24_m],
             by simp only [arm64_norm, hx25_m], by simp only [arm64_norm, hx26_m],
             by simp only [arm64_norm, hx27_m], by simp only [arm64_norm, hx28_m],
             by simp only [arm64_norm, hvregs_m]⟩ hinvm'
        · obtain ⟨hcbz_tag1, hcbz_tag2⟩ := tag_cbz_false hk_ge hitag0
          have hcbz_tag64 : (BitVec.ofNat 64 (key.toNat / 8) == 0#64) = false := by
            rw [beq_eq_false_iff_ne]; intro h
            have h1 := congrArg BitVec.toNat h
            simp only [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega : key.toNat / 8 < 2 ^ 64)] at h1
            omega
          apply SepWPp.of_sepWP_lscro (mid := (blkPl_295).base + 212#64) hinvm
          (conv => arg 4; simp only [decodeVarint2Spec, decodeVarint2SpecGen, hd,
            show 0x40 + (0x40 + decodeErrorHookStack) = decodeVarint2Stack from rfl,
            sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc])
          apply SepWP.exists_elim; intro evs_dv
          wp_focus_pure; rintro ⟨hsm0, hsm1⟩
          wp_focus_pure; intro htrm
          wp_focus_pure; intro hevs_dv
          have hevs_nil := decodeVarint2Env_eq_nil hd hevs_dv
          subst hevs_nil
          conv => arg 4; dsimp only [AllocCostModel.stepEvents, List.foldl]; simp only [arm64_norm, hsp]
          apply SepWP.fold (skipBelow3_leaf_entails s0.sp 97 (by decide)) (by sep_focus)
          apply SepWP.fold (sliceCursorAfter_join hcur_le hcur_suf hrest_le_cur) (by sep_focus)
          apply SepWP.fold (authenticatorPBCapAt_mono A.repAlloc x.msgPtr m hrest_le_cur) (by sep_focus)
          wp_steps_sync_pool ((blkPl_295).base + 212#64)
          simp only [State.setMem_setMem]
          wp_reach; intro hinvm'
          refine SepWPp.weaken_pre (Entails.of_eq (by dsimp only [authBudgetLoopPre]; sep_ac_rfl))
            (hcont key iwt rest _ hd hk_ge hwt hitag0
              (by simp only [arm64_norm]) (by simp only [arm64_norm, hrunm])
              (by simp only [arm64_norm, hspm]) (by simp only [arm64_norm, htrm, htr])
              (by simp only [arm64_norm, hsm1, hand_wt])
              (by simp only [arm64_norm, hsm1, hw1, hw1_2, hw1_zext1, hw1_zext2])
              (by simp only [arm64_norm, hx19_m]) (by simp only [arm64_norm, hx20_m])
              (by simp only [arm64_norm, hx21_m]) (by simp only [arm64_norm, hx22_m])
              ⟨by simp only [arm64_norm, hx23_m], by simp only [arm64_norm, hx24_m],
               by simp only [arm64_norm, hx25_m], by simp only [arm64_norm, hx26_m],
               by simp only [arm64_norm, hx27_m], by simp only [arm64_norm, hx28_m],
               by simp only [arm64_norm, hvregs_m]⟩ hinvm')

set_option maxRecDepth 200000 in
set_option maxHeartbeats 400000 in
set_option linter.unusedSimpArgs false in
theorem auth_loop_ok_cl_placed [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {H : LibsignalHooks}
    {PreEnv PostEnv : AuthMergeGhost → List AllocEvent → Prop}
    (hFromCall : subroutine_ok ((blkPC_295).rebase (blkPl_295).base H) (lsmpl.base 261)
      (withLsCodeRoLoaded lsmpl (decodeErrorFromBudgetSpec M A lim)))
    (hPushCall : subroutine_ok ((blkPC_295).rebase (blkPl_295).base H) (lsmpl.base 257)
      (withLsCodeRoLoaded lsmpl (decodeErrorPushBudgetSpec M A lim)))
    (hVarintCall : subroutine_ok ((blkPC_295).rebase (blkPl_295).base H) (lsmpl.base 291)
      (withLsCodeRoLoaded lsmpl (decodeVarint2Spec A lim)))
    (hSkipCall : subroutine_ok ((blkPC_295).rebase (blkPl_295).base H) (lsmpl.base 263)
      (withLsCodeRoLoaded lsmpl (skipField3Spec A lim)))
    (hBytesCall : subroutine_ok ((blkPC_295).rebase (blkPl_295).base H) (lsmpl.base 290)
      (withLsCodeRoLoaded lsmpl (bytesMerge3RawBudgetSpec A lim)))
    {x : AuthMergeGhost} {st0 : M.σ} {R : SepProp} {s0 : State} {limit : Nat}
    (hFit0 : FitsEnv M lim st0 (AuthPlacedMergeLoopEnv (4 * x.bs.length + 8) x.bs.length))
    (hPost : ∀ evs, AuthPlacedMergePostEnv x evs → PostEnv x evs)
    (hsp_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hbs_lt : x.bs.length < 2 ^ 63) (hlim_lt : limit < 2 ^ 63) :
    ∀ (n : Nat) (m : ProtoAuthenticator) (cur : List (BitVec 8))
      (evs_acc : List AllocEvent) (st_cur : M.σ) (s : State),
      cur.length ≤ n → cur.length ≤ x.bs.length → IsDropSuffix x.bs cur →
      st_cur = M.stepEvents evs_acc st0 →
      AuthPlacedMergeLoopEnv (4 * (x.bs.length - cur.length)) x.bs.length evs_acc →
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
      {f : Nat} {evs : List AllocEvent},
      f ≤ 4 * x.bs.length + 8 →
      AuthPlacedMergeLoopEnv f x.bs.length evs →
      PostEnv x evs := fun hnone {_} {_} hf hevs => by
    apply hPost
    dsimp only [AuthPlacedMergePostEnv]
    rw [hnone]
    exact hevs.mono_fuel hf
  intro n; induction n with
  | zero =>
    intro m cur evs_acc st_cur s hcur_n hcur_le hcur_suf hst_cur hevs_acc hres_cur
      hpc hrun hsp htr hx19 hx20 hx21 hx22 hcs hinv
    have hFit_rem : FitsEnv M lim st_cur
        (AuthPlacedMergeLoopEnv (4 * cur.length + 8) x.bs.length) := by
      rw [hst_cur]
      apply MergePlacedBudgetAux.FitsEnv.authPlacedMergeLoop_split hevs_acc
      simpa [show 4 * (x.bs.length - cur.length) + (4 * cur.length + 8) =
        4 * x.bs.length + 8 by omega] using hFit0
    have hFit_rem1 : FitsEnv M lim st_cur (AuthPlacedMergeLoopEnv 1 x.bs.length) :=
      hFit_rem.mono fun _ h => h.mono_fuel (by omega)
    exact auth_loop_le_exit_cl_placed hFromCall (by omega) hsp_align hcur_le hcur_suf hlim_lt
      (fun _ hsome => ⟨evs_acc, hPost _ (by dsimp only [AuthPlacedMergePostEnv]; rw [hsome]; exact hevs_acc), hst_cur⟩)
      (fun _ => MergePlacedBudgetAux.FitsEnv.authPlacedMergeLoop_head
        (fun _ hf => AuthPlacedMergeIterEnv.of_decodeErrorFrom hf) hFit_rem1)
      (fun hlt evs_f hf => by
        have hnone : (mergeMessage ProtoAuthenticator.mergeField (codecWireTypeToProto x.wt) x.msg x.bs 97).toOption = none := by
          rw [hres_cur, mergeLoopBin_lt_limit _ _ _ _ _ _ hlt, Option.map_none]
        exact ⟨evs_acc ++ evs_f,
          hpost_err hnone (by omega)
            (hevs_acc.append (AuthPlacedMergeLoopEnv.single (fuel := 0) (AuthPlacedMergeIterEnv.of_decodeErrorFrom hf))),
          by rw [hst_cur, stepEvents_append]⟩)
      hres_cur hpc hrun hsp htr hx21 hx22 hcs hinv
  | succ n ih =>
    intro m cur evs_acc st_cur s hcur_n hcur_le hcur_suf hst_cur hevs_acc hres_cur
      hpc hrun hsp htr hx19 hx20 hx21 hx22 hcs hinv
    have hFit_rem : FitsEnv M lim st_cur
        (AuthPlacedMergeLoopEnv (4 * cur.length + 8) x.bs.length) := by
      rw [hst_cur]
      apply MergePlacedBudgetAux.FitsEnv.authPlacedMergeLoop_split hevs_acc
      simpa [show 4 * (x.bs.length - cur.length) + (4 * cur.length + 8) =
        4 * x.bs.length + 8 by omega] using hFit0
    have hFit_rem1 : FitsEnv M lim st_cur (AuthPlacedMergeLoopEnv 1 x.bs.length) :=
      hFit_rem.mono fun _ h => h.mono_fuel (by omega)
    by_cases hle_lim : cur.length ≤ limit
    · exact auth_loop_le_exit_cl_placed hFromCall hle_lim hsp_align hcur_le hcur_suf hlim_lt
        (fun _ hsome => ⟨evs_acc, hPost _ (by dsimp only [AuthPlacedMergePostEnv]; rw [hsome]; exact hevs_acc), hst_cur⟩)
        (fun _ => MergePlacedBudgetAux.FitsEnv.authPlacedMergeLoop_head
          (fun _ hf => AuthPlacedMergeIterEnv.of_decodeErrorFrom hf) hFit_rem1)
        (fun hlt evs_f hf => by
          have hnone : (mergeMessage ProtoAuthenticator.mergeField (codecWireTypeToProto x.wt) x.msg x.bs 97).toOption = none := by
            rw [hres_cur, mergeLoopBin_lt_limit _ _ _ _ _ _ hlt, Option.map_none]
          exact ⟨evs_acc ++ evs_f,
            hpost_err hnone (by omega)
              (hevs_acc.append (AuthPlacedMergeLoopEnv.single (fuel := 0) (AuthPlacedMergeIterEnv.of_decodeErrorFrom hf))),
            by rw [hst_cur, stepEvents_append]⟩)
        hres_cur hpc hrun hsp htr hx21 hx22 hcs hinv
    · have hcur_lt : cur.length < 2 ^ 63 := Nat.lt_of_le_of_lt hcur_le hbs_lt
      refine auth_decode_key_step_cl_placed hFromCall hVarintCall hle_lim hsp_align
        hcur_le hcur_lt hcur_suf
        (MergePlacedBudgetAux.FitsEnv.authPlacedMergeLoop_head
          (fun _ hdv => AuthPlacedMergeIterEnv.of_decodeVarint2 hdv) hFit_rem1)
        (fun hd evs_dv hdv => by
          have hnone : (mergeMessage ProtoAuthenticator.mergeField (codecWireTypeToProto x.wt) x.msg x.bs 97).toOption = none := by
            rw [hres_cur, mergeLoopBin_of_decodeVarint_none protoPrefixStep_protoAuthenticator_mergeField hle_lim hd, Option.map_none]
          exact ⟨evs_acc ++ evs_dv,
            hpost_err hnone (by omega)
              (hevs_acc.append (AuthPlacedMergeLoopEnv.single (fuel := 0) (AuthPlacedMergeIterEnv.of_decodeVarint2 hdv))),
            by rw [hst_cur, stepEvents_append]⟩)
        (MergePlacedBudgetAux.FitsEnv.authPlacedMergeLoop_head
          (fun _ hf => AuthPlacedMergeIterEnv.of_decodeErrorFrom hf) hFit_rem1)
        (fun hnone evs_f hf =>
          ⟨evs_acc ++ evs_f,
            hpost_err hnone (by omega)
              (hevs_acc.append (AuthPlacedMergeLoopEnv.single (fuel := 0) (AuthPlacedMergeIterEnv.of_decodeErrorFrom hf))),
            by rw [hst_cur, stepEvents_append]⟩)
        hres_cur ?_ hpc hrun hsp htr hx19 hx20 hx21 hx22 hcs hinv
      intro key iwt rest s' hd hk_ge hwt hitag0 hpc' hrun' hsp' htr' hx0' hx1' hx19' hx20' hx21' hx22' hcs' hinv'
      obtain ⟨hx23', hx24', hx25', hx26', hx27', hx28', hvregs'⟩ := hcs'
      have hrest_lt_cur : rest.length < cur.length := decodeVarint_length hd
      have hrest_le_cur : rest.length ≤ cur.length := Nat.le_of_lt hrest_lt_cur
      have hrest_le : rest.length ≤ x.bs.length := Nat.le_trans hrest_le_cur hcur_le
      have hrest_lt : rest.length < 2 ^ 63 := Nat.lt_of_le_of_lt hrest_le hbs_lt
      have hrest_suf : IsDropSuffix x.bs rest := suffix_trans hcur_le hcur_suf hrest_le_cur (decodeVarint_suffix hd)
      have hFit_rem2 : FitsEnv M lim st_cur (AuthPlacedMergeLoopEnv (1 + 1) x.bs.length) :=
        hFit_rem.mono fun _ h => h.mono_fuel (by omega)
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
          (auth_tag1_step_cl_placed (m := m) (limit := limit) hPushCall hBytesCall hsp_align hrest_le hrest_lt hrest_suf
            (fun _ _ _ => MergePlacedBudgetAux.FitsEnv.authPlacedMergeLoop_head
              (fun _ hbm => AuthPlacedMergeIterEnv.of_bytesMerge3 hrest_le hbm) hFit_rem1)
            (fun _ _ evs_bm _ hevs_bm =>
              MergePlacedBudgetAux.FitsEnv.authPlacedMergeLoop_head
                (fun _ hp => AuthPlacedMergeIterEnv.of_decodeErrorPush0 hp)
                (MergePlacedBudgetAux.FitsEnv.authPlacedMergeLoop_split
                  (AuthPlacedMergeLoopEnv.single (fuel := 0) (AuthPlacedMergeIterEnv.of_bytesMerge3 hrest_le hevs_bm))
                  hFit_rem2))
            (fun _ _ evs_bm evs_p hmb hevs_bm hp =>
              ⟨(evs_acc ++ evs_bm) ++ evs_p,
                hpost_err (hnone_mb hmb) (by omega)
                  ((hevs_acc.append
                    (AuthPlacedMergeLoopEnv.single (fuel := 0) (AuthPlacedMergeIterEnv.of_bytesMerge3 hrest_le hevs_bm))).append
                    (AuthPlacedMergeLoopEnv.single (fuel := 0) (AuthPlacedMergeIterEnv.of_decodeErrorPush0 hp))),
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
            ((hevs_acc.append
              (AuthPlacedMergeLoopEnv.single (fuel := 0) (AuthPlacedMergeIterEnv.of_bytesMerge3 hrest_le hevs_bm))).mono_fuel
              (by omega))
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
            (auth_tag2_step_cl_placed (m := m) (limit := limit) hPushCall hBytesCall hsp_align hrest_le hrest_lt hrest_suf
              (fun _ _ _ => MergePlacedBudgetAux.FitsEnv.authPlacedMergeLoop_head
                (fun _ hbm => AuthPlacedMergeIterEnv.of_bytesMerge3 hrest_le hbm) hFit_rem1)
              (fun _ _ evs_bm _ hevs_bm =>
                MergePlacedBudgetAux.FitsEnv.authPlacedMergeLoop_head
                  (fun _ hp => AuthPlacedMergeIterEnv.of_decodeErrorPush0 hp)
                  (MergePlacedBudgetAux.FitsEnv.authPlacedMergeLoop_split
                    (AuthPlacedMergeLoopEnv.single (fuel := 0) (AuthPlacedMergeIterEnv.of_bytesMerge3 hrest_le hevs_bm))
                    hFit_rem2))
              (fun _ _ evs_bm evs_p hmb hevs_bm hp =>
                ⟨(evs_acc ++ evs_bm) ++ evs_p,
                  hpost_err (hnone_mb hmb) (by omega)
                    ((hevs_acc.append
                      (AuthPlacedMergeLoopEnv.single (fuel := 0) (AuthPlacedMergeIterEnv.of_bytesMerge3 hrest_le hevs_bm))).append
                      (AuthPlacedMergeLoopEnv.single (fuel := 0) (AuthPlacedMergeIterEnv.of_decodeErrorPush0 hp))),
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
              ((hevs_acc.append
                (AuthPlacedMergeLoopEnv.single (fuel := 0) (AuthPlacedMergeIterEnv.of_bytesMerge3 hrest_le hevs_bm))).mono_fuel
                (by omega))
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
              (MergePlacedBudgetAux.FitsEnv.authPlacedMergeLoop_head
                (fun _ hsf => AuthPlacedMergeIterEnv.of_skipField3 hsf) hFit_rem1)
              (fun hsf evs_sf hevs_sf =>
                ⟨evs_acc ++ evs_sf,
                  hpost_err (hnone_sf hsf) (by omega)
                    (hevs_acc.append
                      (AuthPlacedMergeLoopEnv.single (fuel := 0) (AuthPlacedMergeIterEnv.of_skipField3 hevs_sf))),
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
              hst_cur (hevs_acc.mono_fuel (by omega))
              hres_next hpc'' hrun'' hsp'' htr'' hx19'' hx20'' hx21'' hx22'' hcs'' hinv''

/-! ## Entry Prelude and Top-Level Contracts -/

set_option maxRecDepth 200000 in
set_option maxHeartbeats 400000 in
set_option linter.unusedSimpArgs false in
theorem auth_merge_cl_placed_ok_of_cro_contracts_env [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {H : LibsignalHooks}
    {PreEnv PostEnv : AuthMergeGhost → List AllocEvent → Prop}
    (hPre : ∀ x evs, AuthPlacedMergeEnv x evs → PreEnv x evs)
    (hPost : ∀ x evs, AuthPlacedMergePostEnv x evs → PostEnv x evs)
    (hFromCall : subroutine_ok ((blkPC_295).rebase (blkPl_295).base H) (lsmpl.base 261)
      (withLsCodeRoLoaded lsmpl (decodeErrorFromBudgetSpec M A lim)))
    (hPushCall : subroutine_ok ((blkPC_295).rebase (blkPl_295).base H) (lsmpl.base 257)
      (withLsCodeRoLoaded lsmpl (decodeErrorPushBudgetSpec M A lim)))
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
  have hFit0 : FitsEnv M lim st0 (AuthPlacedMergeLoopEnv (4 * x.bs.length + 8) x.bs.length) :=
    hFit_pre.mono (hPre x)
  have hFit1 : FitsEnv M lim st0 (AuthPlacedMergeLoopEnv 1 x.bs.length) :=
    hFit0.mono fun _ hevs => hevs.mono_fuel (by omega)
  have hpost_err0 :
      ∀ (hnone : (mergeMessage ProtoAuthenticator.mergeField (codecWireTypeToProto x.wt) x.msg x.bs 97).toOption = none)
        {evs : List AllocEvent},
        AuthPlacedMergeIterEnv x.bs.length evs →
        PostEnv x evs := fun hnone {_} hevs => by
    apply hPost x
    dsimp only [AuthPlacedMergePostEnv]
    rw [hnone]
    exact (AuthPlacedMergeLoopEnv.single (fuel := 0) hevs).mono_fuel (by omega)
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
       MergePlacedBudgetAux.FitsEnv.authPlacedMergeLoop_head
         (fun _ hdv => AuthPlacedMergeIterEnv.of_decodeVarint2 hdv) hFit1⟩
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
        ⟨evs_dv, hpost_err0 hnone (AuthPlacedMergeIterEnv.of_decodeVarint2 hevs_dv), rfl⟩
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
          (MergePlacedBudgetAux.FitsEnv.authPlacedMergeLoop_head
            (fun _ hf => AuthPlacedMergeIterEnv.of_decodeErrorFrom hf) hFit1)
          (fun evs_f hf => ⟨evs_f, hpost_err0 hnone (AuthPlacedMergeIterEnv.of_decodeErrorFrom hf), rfl⟩)
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
        exact auth_loop_ok_cl_placed hFromCall hPushCall hVarintCall hSkipCall hBytesCall
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
        (MergePlacedBudgetAux.FitsEnv.authPlacedMergeLoop_head
          (fun _ hf => AuthPlacedMergeIterEnv.of_decodeErrorFrom hf) hFit1)
        (fun evs_f hf => ⟨evs_f, hpost_err0 hnone (AuthPlacedMergeIterEnv.of_decodeErrorFrom hf), rfl⟩)
        hsp_align
        (by simp only [arm64_norm]) (by simp only [arm64_norm, hrun])
        (by simp only [arm64_norm]) (by simp only [arm64_norm])
        (by simp only [arm64_norm])
        ⟨by simp only [arm64_norm], by simp only [arm64_norm],
         by simp only [arm64_norm], by simp only [arm64_norm],
         by simp only [arm64_norm], by simp only [arm64_norm],
         by simp only [arm64_norm]⟩ hinv0')

/-- `withLsCodeRoLoaded`-callee `[LibsignalPlacement]` verification of `Authenticator::merge`
(Block `295`) against `authMergeSpec A lim`. -/
theorem auth_merge_cl_placed_ok_of_cro_contracts [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {H : LibsignalHooks}
    (hFromCall : subroutine_ok ((blkPC_295).rebase (blkPl_295).base H) (lsmpl.base 261)
      (withLsCodeRoLoaded lsmpl (decodeErrorFromBudgetSpec M A lim)))
    (hPushCall : subroutine_ok ((blkPC_295).rebase (blkPl_295).base H) (lsmpl.base 257)
      (withLsCodeRoLoaded lsmpl (decodeErrorPushBudgetSpec M A lim)))
    (hVarintCall : subroutine_ok ((blkPC_295).rebase (blkPl_295).base H) (lsmpl.base 291)
      (withLsCodeRoLoaded lsmpl (decodeVarint2Spec A lim)))
    (hSkipCall : subroutine_ok ((blkPC_295).rebase (blkPl_295).base H) (lsmpl.base 263)
      (withLsCodeRoLoaded lsmpl (skipField3Spec A lim)))
    (hBytesCall : subroutine_ok ((blkPC_295).rebase (blkPl_295).base H) (lsmpl.base 290)
      (withLsCodeRoLoaded lsmpl (bytesMerge3RawBudgetSpec A lim))) :
    subroutine_ok ((blkPC_295).rebase (blkPl_295).base H)
      (blkPl_295).base
      (withLsCodeRoLoaded lsmpl (authMergeSpec A lim)) :=
  auth_merge_cl_placed_ok_of_cro_contracts_env
    (fun _ _ h => h) (fun _ _ h => h)
    hFromCall hPushCall hVarintCall hSkipCall hBytesCall

theorem auth_merge_placed_ok_of_contracts_env [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {H : LibsignalHooks}
    {PreEnv PostEnv : AuthMergeGhost → List AllocEvent → Prop}
    (hPre : ∀ x evs, AuthPlacedMergeEnv x evs → PreEnv x evs)
    (hPost : ∀ x evs, AuthPlacedMergePostEnv x evs → PostEnv x evs)
    (hFromCall : subroutine_ok ((blkPC_295).rebase (blkPl_295).base H) (lsmpl.base 261)
      (decodeErrorFromBudgetSpec M A lim))
    (hPushCall : subroutine_ok ((blkPC_295).rebase (blkPl_295).base H) (lsmpl.base 257)
      (decodeErrorPushBudgetSpec M A lim))
    (hVarintCall : subroutine_ok ((blkPC_295).rebase (blkPl_295).base H) (lsmpl.base 291)
      (decodeVarint2Spec A lim))
    (hSkipCall : subroutine_ok ((blkPC_295).rebase (blkPl_295).base H) (lsmpl.base 263)
      (skipField3Spec A lim))
    (hBytesCall : subroutine_ok ((blkPC_295).rebase (blkPl_295).base H) (lsmpl.base 290)
      (withLsCodeRoLoaded lsmpl (bytesMerge3RawBudgetSpec A lim))) :
    subroutine_ok ((blkPC_295).rebase (blkPl_295).base H)
      (blkPl_295).base
      (withLsCodeRoLoaded lsmpl (authMergeSpecOfEnv A lim PreEnv PostEnv)) :=
  auth_merge_cl_placed_ok_of_cro_contracts_env hPre hPost
    (subroutine_ok_withLsCodeRoLoaded_of_plain hFromCall)
    (subroutine_ok_withLsCodeRoLoaded_of_plain hPushCall)
    (subroutine_ok_withLsCodeRoLoaded_of_plain hVarintCall)
    (subroutine_ok_withLsCodeRoLoaded_of_plain hSkipCall)
    hBytesCall

/-- Contract-parameterized `[LibsignalPlacement]` verification of `Authenticator::merge`
(Block `295`) against `authMergeSpec A lim`. -/
theorem auth_merge_placed_ok_of_contracts [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {H : LibsignalHooks}
    (hFromCall : subroutine_ok ((blkPC_295).rebase (blkPl_295).base H) (lsmpl.base 261)
      (decodeErrorFromBudgetSpec M A lim))
    (hPushCall : subroutine_ok ((blkPC_295).rebase (blkPl_295).base H) (lsmpl.base 257)
      (decodeErrorPushBudgetSpec M A lim))
    (hVarintCall : subroutine_ok ((blkPC_295).rebase (blkPl_295).base H) (lsmpl.base 291)
      (decodeVarint2Spec A lim))
    (hSkipCall : subroutine_ok ((blkPC_295).rebase (blkPl_295).base H) (lsmpl.base 263)
      (skipField3Spec A lim))
    (hBytesCall : subroutine_ok ((blkPC_295).rebase (blkPl_295).base H) (lsmpl.base 290)
      (withLsCodeRoLoaded lsmpl (bytesMerge3RawBudgetSpec A lim))) :
    subroutine_ok ((blkPC_295).rebase (blkPl_295).base H)
      (blkPl_295).base
      (withLsCodeRoLoaded lsmpl (authMergeSpec A lim)) :=
  auth_merge_placed_ok_of_contracts_env (fun _ _ h => h) (fun _ _ h => h)
    hFromCall hPushCall hVarintCall hSkipCall hBytesCall

theorem auth_merge_cl_placed_ok_of_contracts_env [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {H : LibsignalHooks}
    {PreEnv PostEnv : AuthMergeGhost → List AllocEvent → Prop}
    (hPre : ∀ x evs, AuthPlacedMergeEnv x evs → PreEnv x evs)
    (hPost : ∀ x evs, AuthPlacedMergePostEnv x evs → PostEnv x evs)
    (hFromCall : subroutine_ok ((blkPC_295).rebase (blkPl_295).base H) (lsmpl.base 261)
      (withLsCodeLoaded lsmpl (decodeErrorFromBudgetSpec M A lim)))
    (hPushCall : subroutine_ok ((blkPC_295).rebase (blkPl_295).base H) (lsmpl.base 257)
      (withLsCodeLoaded lsmpl (decodeErrorPushBudgetSpec M A lim)))
    (hVarintCall : subroutine_ok ((blkPC_295).rebase (blkPl_295).base H) (lsmpl.base 291)
      (withLsCodeLoaded lsmpl (decodeVarint2Spec A lim)))
    (hSkipCall : subroutine_ok ((blkPC_295).rebase (blkPl_295).base H) (lsmpl.base 263)
      (withLsCodeLoaded lsmpl (skipField3Spec A lim)))
    (hBytesCall : subroutine_ok ((blkPC_295).rebase (blkPl_295).base H) (lsmpl.base 290)
      (withLsCodeRoLoaded lsmpl (bytesMerge3RawBudgetSpec A lim))) :
    subroutine_ok ((blkPC_295).rebase (blkPl_295).base H)
      (blkPl_295).base
      (withLsCodeRoLoaded lsmpl (authMergeSpecOfEnv A lim PreEnv PostEnv)) :=
  auth_merge_cl_placed_ok_of_cro_contracts_env hPre hPost
    (subroutine_ok_withLsCodeRoLoaded_of_withLsCodeLoaded hFromCall)
    (subroutine_ok_withLsCodeRoLoaded_of_withLsCodeLoaded hPushCall)
    (subroutine_ok_withLsCodeRoLoaded_of_withLsCodeLoaded hVarintCall)
    (subroutine_ok_withLsCodeRoLoaded_of_withLsCodeLoaded hSkipCall)
    hBytesCall

/-- Contract-parameterized code-loaded `[LibsignalPlacement]` verification of `Authenticator::merge`
(Block `295`) against `authMergeSpec A lim`. -/
theorem auth_merge_cl_placed_ok_of_contracts [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {H : LibsignalHooks}
    (hFromCall : subroutine_ok ((blkPC_295).rebase (blkPl_295).base H) (lsmpl.base 261)
      (withLsCodeLoaded lsmpl (decodeErrorFromBudgetSpec M A lim)))
    (hPushCall : subroutine_ok ((blkPC_295).rebase (blkPl_295).base H) (lsmpl.base 257)
      (withLsCodeLoaded lsmpl (decodeErrorPushBudgetSpec M A lim)))
    (hVarintCall : subroutine_ok ((blkPC_295).rebase (blkPl_295).base H) (lsmpl.base 291)
      (withLsCodeLoaded lsmpl (decodeVarint2Spec A lim)))
    (hSkipCall : subroutine_ok ((blkPC_295).rebase (blkPl_295).base H) (lsmpl.base 263)
      (withLsCodeLoaded lsmpl (skipField3Spec A lim)))
    (hBytesCall : subroutine_ok ((blkPC_295).rebase (blkPl_295).base H) (lsmpl.base 290)
      (withLsCodeRoLoaded lsmpl (bytesMerge3RawBudgetSpec A lim))) :
    subroutine_ok ((blkPC_295).rebase (blkPl_295).base H)
      (blkPl_295).base
      (withLsCodeRoLoaded lsmpl (authMergeSpec A lim)) :=
  auth_merge_cl_placed_ok_of_contracts_env (fun _ _ h => h) (fun _ _ h => h)
    hFromCall hPushCall hVarintCall hSkipCall hBytesCall

end LibsignalBinary.Proofs.SpqrV1.Auth.MergePlacedBudget
