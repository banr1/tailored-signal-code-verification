/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SpqrV1.Auth.MergeBase
public import LibsignalBinary.Proofs.SpqrV1.ProtoRepr.EncodedLen.Defs
import GeneratedLean.LibsignalSessionCode -- shake: keep
import LibsignalBinary.Proofs.FnOffEq
import LibsignalBinary.Proofs.ProtoCodecRoundTrip
import LibsignalBinary.Proofs.TripleRatchet.GeneralizeEntry
import LibsignalBinary.Proofs.TripleRatchet.Prost.BytesMerge.Phase1
import ProofLib.SepLogic.WPp
import LibsignalBinary.Specifications.LibsignalSpqrV1.Wire -- shake: keep

/-!
# `prost::encoding::message::merge::<Authenticator, &mut &[u8]>`

Proves the main loop induction (`auth_loop_ok`) and top-level contracts
(`auth_merge_ok_of_contracts`, `auth_merge_ok_of_fnAddr`, `AuthMergeOkX`) for
`prost::encoding::message::merge::<spqr::proto::pq_ratchet::Authenticator, &mut &[u8]>`
(`0x4df38`) against `Proto.mergeMessage ProtoAuthenticator.mergeField`.
-/

@[expose] public section

namespace CryptoVerification.SpqrV1.Auth

open Arm64 ProofLib ProofLib.ProgramReflection
open CryptoGames.LibsignalSession
open CryptoVerification.RustHeap CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchetRepr CryptoVerification.LibsignalProtoCodec
open CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalTripleRatchet.Prost
open CryptoVerification.SpqrV1.Varint
open CryptoVerification.SpqrV1.ProtoRepr
open CryptoVerification.SpqrV1.Prost.BytesMerge
open CryptoVerification.SpqrV1.Prost.MessageMerge
open CryptoVerification.LibsignalSpqrV1 hiding decodeVarint encodeVarint WireType
open CryptoVerification.CodeLayout

set_option maxRecDepth 200000
set_option maxHeartbeats 400000
set_option linter.unusedSimpArgs false

attribute [local irreducible] Program.fetch Program.externAt?
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero
attribute [local simp, local arm64_norm] bv64_sub_zero bv64_add_zero authMerge_fnOff

/-! ## Loop Exit, Key Decode, and Loop Induction -/

/-- Loop exit at `+0x0a0` when `cur.length ≤ limit` (`Ok(())` on equality, `Err(Truncated)` if strict). -/
theorem auth_loop_le_exit {b : BitVec 64} {A : RustAlloc}
    {H : String → Option (State → State)}
    (hFromCall : subroutine_ok (libsignalSessionCode.rebase b H)
      ((libsignalSessionCode.rebase b H).fnAddr authMergeName + 0xffffffffffffce68#64)
      (decodeErrorFromSpec A))
    {x : AuthMergeGhost} {R : SepProp} {s0 s : State}
    {m : ProtoAuthenticator} {cur : List (BitVec 8)} {limit : Nat}
    (hle_lim : cur.length ≤ limit)
    (hsp_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hcur_le : cur.length ≤ x.bs.length)
    (hcur_suf : IsDropSuffix x.bs cur)
    (hlim_lt : limit < 2 ^ 63)
    (hres_cur : (Proto.mergeMessage ProtoAuthenticator.mergeField (codecWireTypeToProto x.wt) x.msg x.bs 97).toOption =
      (mergeLoopBin ProtoAuthenticator.mergeField (cur.length - limit) m cur limit 96).map
        (fun m' => (m', x.bs.drop (x.bs.length - limit))))
    (hpc : s.pc = (libsignalSessionCode.rebase b H).fnAddr authMergeName + 160#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = s0.sp - 96#64)
    (htr : s.trace = s0.trace)
    (hx21 : s.readReg64 (Reg.gpr 21#5) = x.slot)
    (hx22 : s.readReg64 (Reg.gpr 22#5) = BitVec.ofNat 64 limit)
    (hcs : HighCalleeSaved s0 s) :
    SepWPp (libsignalSessionCode.rebase b H) (s0.readReg64 Reg.lr) s
      (authLoopPre A s0 x.msgPtr x.bufRef x.slot x.ptr m x.bs cur)
      (WppPost (authMergeSpec A) x R s0)
      (WppPanic R s0) := by
  obtain ⟨hx23, hx24, hx25, hx26, hx27, hx28, hvregs⟩ := hcs
  let curPtr : BitVec 64 := x.ptr + BitVec.ofNat 64 (x.bs.length - cur.length)
  by_cases heq_lim : cur.length = limit
  · obtain ⟨hcmp1, hcmp2, hcmp3⟩ := cmp_len_limit_of_eq heq_lim
    have hcur_eq_drop : x.bs.drop (x.bs.length - limit) = cur := by
      rw [← heq_lim]; exact hcur_suf.symm
    have hsome : (Proto.mergeMessage ProtoAuthenticator.mergeField (codecWireTypeToProto x.wt) x.msg x.bs 97).toOption =
        some (m, cur) := by
      rw [hres_cur, mergeLoopBin_eq_limit _ _ _ _ _ _ heq_lim, Option.map_some, hcur_eq_drop]
    authMerge_fetches b H 160 12
    authMerge_fetches b H 276 32
    generalize_entry (libsignalSessionCode.rebase b H).fnAddr authMergeName = entry
    examples_hide_fetches
    apply SepWPp.of_sepWP_ret
    unfold WppPost authMergeSpec
    simp only [hsome, authMergeStack, stackAt_skipField3 _ 97 (by decide), authLoopPre,
      sliceCursorAfter_eq_split hcur_le hcur_suf, sliceCursorAt,
      sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc, arm64_norm, htr, hsp]
    wp_steps
    wp_done
  · have hlt_lim : cur.length < limit := Nat.lt_of_le_of_ne hle_lim heq_lim
    obtain ⟨hcmp1, hcmp2, hcmp3⟩ := cmp_len_limit_of_lt hlt_lim hlim_lt
    have hnone : (Proto.mergeMessage ProtoAuthenticator.mergeField (codecWireTypeToProto x.wt) x.msg x.bs 97).toOption = none := by
      rw [hres_cur, mergeLoopBin_lt_limit _ _ _ _ _ _ hlt_lim, Option.map_none]
    have hfrom_exit := @auth_from_err_exit b A H hFromCall x R s0
    authMerge_fetches b H 160 12
    authMerge_fetches b H 276 4
    authMerge_fetches b H 352 16
    generalize_entry (libsignalSessionCode.rebase b H).fnAddr authMergeName = entry
    examples_hide_fetches
    apply SepWPp.of_sepWP (mid := entry + 100#64)
    conv => arg 4; rw [authLoopPre, sliceCursorAfter_eq_split hcur_le hcur_suf,
      sliceCursorAt, memRegion_48_split_96 s0.sp]
    simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
    apply SepWP.exists_elim; intro v_stk0
    wp_steps
    apply SepWP.fold (pointsTo64_pair_entails_memRegion16 x.slot curPtr (BitVec.ofNat 64 cur.length)) (by sep_focus)
    apply SepWP.fold (pointsToBytes_prefix_join hcur_le hcur_suf) (by sep_focus)
    apply SepWP.fold (authenticatorPBCapAt_entails_authenticatorPBAt A x.msgPtr cur.length m) (by sep_focus)
    wp_reach
    apply SepWPp.weaken_pre (P' :=
      ((s0.sp - 96#64) ↦₆₄ v_stk0) ∗
        memRegion (s0.sp - 88#64) 40 ∗
        skipBelow3 s0.sp 97 ∗
        authErrFrame A s0 x.msgPtr x.bufRef x.slot x.ptr m x.bs)
      (by dsimp only [authErrFrame]; sep_entail)
    exact hfrom_exit hnone (by decide : KindNoHeap 0x8000000000000008#64) hsp_align
      (by simp only [arm64_norm]) (by simp only [arm64_norm, hrun])
      (by simp only [arm64_norm, hsp]) (by simp only [arm64_norm, htr])
      (by simp only [arm64_norm])
      ⟨by simp only [arm64_norm, hx23], by simp only [arm64_norm, hx24],
       by simp only [arm64_norm, hx25], by simp only [arm64_norm, hx26],
       by simp only [arm64_norm, hx27], by simp only [arm64_norm, hx28],
       by simp only [arm64_norm, hvregs]⟩

/-- Key-decoding step at `+0x0a0` when `limit < cur.length`: decodes varint key and dispatches on wire type and tag. -/
theorem auth_decode_key_step {b : BitVec 64} {img : Obj.Image} {A : RustAlloc}
    {H : String → Option (State → State)}
    (hFromCall : subroutine_ok (libsignalSessionCode.rebase b H)
      ((libsignalSessionCode.rebase b H).fnAddr authMergeName + 0xffffffffffffce68#64)
      (decodeErrorFromSpec A))
    (hVarintCall : subroutine_ok (libsignalSessionCode.rebase b H)
      ((libsignalSessionCode.rebase b H).fnAddr authMergeName + 0xfffffffffffff594#64)
      (decodeVarint2Spec A))
    {x : AuthMergeGhost} {R : SepProp} {s0 s : State}
    {m : ProtoAuthenticator} {cur : List (BitVec 8)} {limit : Nat}
    (hgt_lim : ¬ cur.length ≤ limit)
    (hsp_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hcur_le : cur.length ≤ x.bs.length)
    (hcur_lt : cur.length < 2 ^ 63)
    (hcur_suf : IsDropSuffix x.bs cur)
    (hres_cur : (Proto.mergeMessage ProtoAuthenticator.mergeField (codecWireTypeToProto x.wt) x.msg x.bs 97).toOption =
      (mergeLoopBin ProtoAuthenticator.mergeField (cur.length - limit) m cur limit 96).map
        (fun m' => (m', x.bs.drop (x.bs.length - limit))))
    (hcont : ∀ (key : BitVec 64) (iwt : WireType) (rest : List (BitVec 8)) (s' : State),
      decodeVarint cur = some (key, rest) →
      ¬ 2 ^ 32 ≤ key.toNat →
      WireType.ofNat? (key.toNat % 8) = some iwt →
      ¬ key.toNat / 8 < 1 →
      s'.pc = (libsignalSessionCode.rebase b H).fnAddr authMergeName + 212#64 →
      s'.status = .Running →
      s'.sp = s0.sp - 96#64 →
      s'.trace = s0.trace →
      s'.readReg64 (Reg.gpr 0#5) = BitVec.ofNat 64 iwt.toNat →
      s'.readReg64 (Reg.gpr 1#5) = BitVec.ofNat 64 (key.toNat / 8) →
      s'.readReg64 (Reg.gpr 19#5) = x.bufRef →
      s'.readReg64 (Reg.gpr 20#5) = x.msgPtr →
      s'.readReg64 (Reg.gpr 21#5) = x.slot →
      s'.readReg64 (Reg.gpr 22#5) = BitVec.ofNat 64 limit →
      HighCalleeSaved s0 s' →
      ImgCallInv img s' →
      SepWPp (libsignalSessionCode.rebase b H) (s0.readReg64 Reg.lr) s'
        (authLoopPre A s0 x.msgPtr x.bufRef x.slot x.ptr m x.bs rest)
        (WppPost (authMergeSpec A) x R s0)
        (WppPanic R s0))
    (hpc : s.pc = (libsignalSessionCode.rebase b H).fnAddr authMergeName + 160#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = s0.sp - 96#64)
    (htr : s.trace = s0.trace)
    (hx19 : s.readReg64 (Reg.gpr 19#5) = x.bufRef)
    (hx20 : s.readReg64 (Reg.gpr 20#5) = x.msgPtr)
    (hx21 : s.readReg64 (Reg.gpr 21#5) = x.slot)
    (hx22 : s.readReg64 (Reg.gpr 22#5) = BitVec.ofNat 64 limit)
    (hcs : HighCalleeSaved s0 s)
    (hinv : ImgCallInv img s) :
    SepWPp (libsignalSessionCode.rebase b H) (s0.readReg64 Reg.lr) s
      (authLoopPre A s0 x.msgPtr x.bufRef x.slot x.ptr m x.bs cur)
      (WppPost (authMergeSpec A) x R s0)
      (WppPanic R s0) := by
  obtain ⟨hx23, hx24, hx25, hx26, hx27, hx28, hvregs⟩ := hcs
  obtain ⟨hcmp1, hcmp2⟩ := cmp_len_limit_of_gt hgt_lim hcur_lt
  let curPtr : BitVec 64 := x.ptr + BitVec.ofNat 64 (x.bs.length - cur.length)
  have herr0_exit := @auth_err0_ret_exit b A H x R s0
  have hfrom_exit := @auth_from_err_exit b A H hFromCall x R s0
  authMerge_fetches b H 160 52
  authMerge_fetches b H 308 44
  generalize_entry (libsignalSessionCode.rebase b H).fnAddr authMergeName = entry
  examples_hide_fetches
  apply SepWPp.of_sepWP_img (mid := entry + 0xfffffffffffff594#64) hinv
  conv => arg 4; rw [authLoopPre, sliceCursorAfter_eq_split hcur_le hcur_suf,
    sliceCursorAt, skipBelow3_leaf s0.sp 97 (by decide)]
  simp only [sepConj_assoc]
  wp_steps
  wp_reach; intro hinv
  refine SepWPp.call_frame_keep (x := ⟨x.bufRef, x.slot, curPtr, cur⟩)
    (ret_pc := entry + 180#64) hVarintCall hinv
    (by simp only [arm64_norm]) (by simp only [arm64_norm, hrun])
    (by simp only [State.spAligned, hsp, arm64_norm]; exact hsp_align)
    (by simp only [arm64_norm])
    (by dsimp only [decodeVarint2Spec]; simp only [arm64_norm, hsp, hx19]; rfl)
    hcur_lt (by dsimp only [sliceCursorAt, curPtr]; sep_focus)
    (fun _ _ _ _ hex => allowPanic_not_exited hex)
    (fun sf _ hpan => allowPanic_frame' (by simp only [arm64_norm, htr]) hpan) ?_
  intro sm hpcm hrunm hspm hcsm hinvm
  simp only [CalleeSavedPreserved] at hcsm
  obtain ⟨hx19_m, hx20_m, hx21_m, hx22_m, hx23_m, hx24_m, hx25_m, hx26_m, hx27_m, hx28_m, hfp_m, hvregs_m⟩ := hcsm
  simp (config := { decide := true }) only [arm64_norm, hsp, hx19, hx20, hx21, hx22, hx23, hx24, hx25, hx26, hx27, hx28, hvregs] at hpcm hrunm hspm hx19_m hx20_m hx21_m hx22_m hx23_m hx24_m hx25_m hx26_m hx27_m hx28_m hfp_m hvregs_m
  cases hd : decodeVarint cur with
  | none =>
    have hnone : (Proto.mergeMessage ProtoAuthenticator.mergeField (codecWireTypeToProto x.wt) x.msg x.bs 97).toOption = none := by
      rw [hres_cur, mergeLoopBin_of_decodeVarint_none protoPrefixStep_protoAuthenticator_mergeField hgt_lim hd, Option.map_none]
    apply SepWPp.of_sepWP (mid := entry + 116#64)
    conv => arg 4; simp only [decodeVarint2Spec, hd, sepConj_assoc, arm64_norm, hsp]
    apply SepWP.pure_elim; rintro ⟨htrm, hsm0, hsm1⟩
    apply SepWP.fold (skipBelow3_leaf_entails s0.sp 97 (by decide)) (by sep_focus)
    apply SepWP.fold (pointsToBytes_prefix_join hcur_le hcur_suf) (by sep_focus)
    apply SepWP.fold (authenticatorPBCapAt_entails_authenticatorPBAt A x.msgPtr cur.length m) (by sep_focus)
    wp_steps
    wp_reach
    apply SepWPp.weaken_pre (P' :=
      decodeErrorAtStackLen A (sm.readReg64 (Reg.gpr 1#5)) 0 ∗
        memRegion (s0.sp - 96#64) 48 ∗
        skipBelow3 s0.sp 97 ∗
        authErrFrame A s0 x.msgPtr x.bufRef x.slot x.ptr m x.bs)
      (by dsimp only [authErrFrame]; sep_entail)
    exact herr0_exit hnone hsp_align
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
    have hrest_suf : IsDropSuffix x.bs rest :=
      suffix_trans hcur_le hcur_suf hrest_le_cur (decodeVarint_suffix hd)
    let restPtr : BitVec 64 := x.ptr + BitVec.ofNat 64 (x.bs.length - rest.length)
    by_cases hk_ge : 2 ^ 32 ≤ key.toNat
    · have hnone : (Proto.mergeMessage ProtoAuthenticator.mergeField (codecWireTypeToProto x.wt) x.msg x.bs 97).toOption = none := by
        rw [hres_cur, mergeLoopBin_of_key_ge protoPrefixStep_protoAuthenticator_mergeField hgt_lim hd hk_ge, Option.map_none]
      have hshr := key_shr32_of_ge hk_ge
      apply SepWPp.of_sepWP (mid := entry + 100#64)
      conv => arg 4; simp only [decodeVarint2Spec, hd, sepConj_assoc, arm64_norm, hsp]
      apply SepWP.pure_elim; rintro ⟨htrm, hsm0, hsm1⟩
      apply SepWP.fold (skipBelow3_leaf_entails s0.sp 97 (by decide)) (by sep_focus)
      apply SepWP.fold (sliceCursorAfter_join hcur_le hcur_suf hrest_le_cur) (by sep_focus)
      apply SepWP.fold (authenticatorPBCapAt_entails_authenticatorPBAt A x.msgPtr cur.length m) (by sep_focus)
      conv => arg 4; rw [sliceCursorAfter_eq_split hrest_le hrest_suf, sliceCursorAt, memRegion_48_split2 s0.sp]
      simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
      apply SepWP.exists_elim; intro v_err0
      apply SepWP.exists_elim; intro v_err1
      wp_steps
      apply SepWP.fold (pointsTo64_pair_entails_memRegion16 x.slot restPtr (BitVec.ofNat 64 rest.length)) (by sep_focus)
      apply SepWP.fold (pointsToBytes_prefix_join hrest_le hrest_suf) (by sep_focus)
      have h40 := pointsTo64_memRegion32_entails_40 s0.sp key
      rw [← bv_sub_add_lit s0.sp 96 8] at h40
      apply SepWP.fold h40 (by sep_focus)
      wp_reach
      apply SepWPp.weaken_pre (P' :=
        ((s0.sp - 96#64) ↦₆₄ v_err1) ∗
          memRegion (s0.sp - 88#64) 40 ∗
          skipBelow3 s0.sp 97 ∗
          authErrFrame A s0 x.msgPtr x.bufRef x.slot x.ptr m x.bs)
        (by dsimp only [authErrFrame]; sep_entail)
      exact hfrom_exit hnone (by decide : KindNoHeap 0x8000000000000004#64) hsp_align
        (by simp only [arm64_norm]) (by simp only [arm64_norm, hrunm])
        (by simp only [arm64_norm, hspm]) (by simp only [arm64_norm, htrm, htr])
        (by simp only [arm64_norm])
        ⟨by simp only [arm64_norm, hx23_m], by simp only [arm64_norm, hx24_m],
         by simp only [arm64_norm, hx25_m], by simp only [arm64_norm, hx26_m],
         by simp only [arm64_norm, hx27_m], by simp only [arm64_norm, hx28_m],
       by simp only [arm64_norm, hvregs_m]⟩
    · have hshr := key_shr32_of_lt hk_ge
      cases hwt : WireType.ofNat? (key.toNat % 8) with
      | none =>
        have hnone : (Proto.mergeMessage ProtoAuthenticator.mergeField (codecWireTypeToProto x.wt) x.msg x.bs 97).toOption = none := by
          rw [hres_cur, mergeLoopBin_of_wt_none protoPrefixStep_protoAuthenticator_mergeField hgt_lim hd hk_ge hwt, Option.map_none]
        obtain ⟨hcs1, hcs2⟩ := key_wt_none hwt
        apply SepWPp.of_sepWP (mid := entry + 100#64)
        conv => arg 4; simp only [decodeVarint2Spec, hd, sepConj_assoc, arm64_norm, hsp]
        apply SepWP.pure_elim; rintro ⟨htrm, hsm0, hsm1⟩
        apply SepWP.fold (skipBelow3_leaf_entails s0.sp 97 (by decide)) (by sep_focus)
        apply SepWP.fold (sliceCursorAfter_join hcur_le hcur_suf hrest_le_cur) (by sep_focus)
        apply SepWP.fold (authenticatorPBCapAt_entails_authenticatorPBAt A x.msgPtr cur.length m) (by sep_focus)
        conv => arg 4; rw [sliceCursorAfter_eq_split hrest_le hrest_suf, sliceCursorAt, memRegion_48_split2 s0.sp]
        simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
        apply SepWP.exists_elim; intro v_err0
        apply SepWP.exists_elim; intro v_err1
        wp_steps
        apply SepWP.fold (pointsTo64_pair_entails_memRegion16 x.slot restPtr (BitVec.ofNat 64 rest.length)) (by sep_focus)
        apply SepWP.fold (pointsToBytes_prefix_join hrest_le hrest_suf) (by sep_focus)
        have h40 := pointsTo64_memRegion32_entails_40 s0.sp (key &&& 7#64)
        rw [← bv_sub_add_lit s0.sp 96 8] at h40
        apply SepWP.fold h40 (by sep_focus)
        wp_reach
        apply SepWPp.weaken_pre (P' :=
          ((s0.sp - 96#64) ↦₆₄ v_err1) ∗
            memRegion (s0.sp - 88#64) 40 ∗
            skipBelow3 s0.sp 97 ∗
            authErrFrame A s0 x.msgPtr x.bufRef x.slot x.ptr m x.bs)
          (by dsimp only [authErrFrame]; sep_entail)
        exact hfrom_exit hnone (by decide : KindNoHeap 0x8000000000000003#64) hsp_align
          (by simp only [arm64_norm]) (by simp only [arm64_norm, hrunm])
          (by simp only [arm64_norm, hspm]) (by simp only [arm64_norm, htrm, htr])
          (by simp only [arm64_norm])
          ⟨by simp only [arm64_norm, hx23_m], by simp only [arm64_norm, hx24_m],
           by simp only [arm64_norm, hx25_m], by simp only [arm64_norm, hx26_m],
           by simp only [arm64_norm, hx27_m], by simp only [arm64_norm, hx28_m],
       by simp only [arm64_norm, hvregs_m]⟩
      | some iwt =>
        obtain ⟨hcc1, hcc2, hand_wt, hcc1_wt, hcc2_wt⟩ := key_wt_some hwt
        obtain ⟨hw1, hw1_2⟩ := w1_tag_eq hk_ge
        obtain ⟨hw1_zext1, hw1_zext2⟩ := bv32_zeroExtend_ofNat (n := key.toNat / 8) (by omega)
        by_cases hitag0 : key.toNat / 8 < 1
        · have hnone : (Proto.mergeMessage ProtoAuthenticator.mergeField (codecWireTypeToProto x.wt) x.msg x.bs 97).toOption = none := by
            rw [hres_cur, mergeLoopBin_of_tag_zero protoPrefixStep_protoAuthenticator_mergeField hgt_lim hd hk_ge hwt hitag0, Option.map_none]
          have htag_zero : key.toNat / 8 = 0 := by omega
          apply SepWPp.of_sepWP (mid := entry + 100#64)
          conv => arg 4; simp only [decodeVarint2Spec, hd, sepConj_assoc, arm64_norm, hsp]
          apply SepWP.pure_elim; rintro ⟨htrm, hsm0, hsm1⟩
          apply SepWP.fold (skipBelow3_leaf_entails s0.sp 97 (by decide)) (by sep_focus)
          apply SepWP.fold (sliceCursorAfter_join hcur_le hcur_suf hrest_le_cur) (by sep_focus)
          apply SepWP.fold (authenticatorPBCapAt_entails_authenticatorPBAt A x.msgPtr cur.length m) (by sep_focus)
          conv => arg 4; rw [sliceCursorAfter_eq_split hrest_le hrest_suf, sliceCursorAt, memRegion_48_split_96 s0.sp]
          simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
          apply SepWP.exists_elim; intro v_err0
          wp_steps
          apply SepWP.fold (pointsTo64_pair_entails_memRegion16 x.slot restPtr (BitVec.ofNat 64 rest.length)) (by sep_focus)
          apply SepWP.fold (pointsToBytes_prefix_join hrest_le hrest_suf) (by sep_focus)
          wp_reach
          apply SepWPp.weaken_pre (P' :=
            ((s0.sp - 96#64) ↦₆₄ v_err0) ∗
              memRegion (s0.sp - 88#64) 40 ∗
              skipBelow3 s0.sp 97 ∗
              authErrFrame A s0 x.msgPtr x.bufRef x.slot x.ptr m x.bs)
            (by dsimp only [authErrFrame]; sep_entail)
          exact hfrom_exit hnone (by decide : KindNoHeap 0x8000000000000005#64) hsp_align
            (by simp only [arm64_norm]) (by simp only [arm64_norm, hrunm])
            (by simp only [arm64_norm, hspm]) (by simp only [arm64_norm, htrm, htr])
            (by simp only [arm64_norm])
            ⟨by simp only [arm64_norm, hx23_m], by simp only [arm64_norm, hx24_m],
             by simp only [arm64_norm, hx25_m], by simp only [arm64_norm, hx26_m],
             by simp only [arm64_norm, hx27_m], by simp only [arm64_norm, hx28_m],
       by simp only [arm64_norm, hvregs_m]⟩
        · obtain ⟨hcbz_tag1, hcbz_tag2⟩ := tag_cbz_false hk_ge hitag0
          have hcbz_tag64 : (BitVec.ofNat 64 (key.toNat / 8) == 0#64) = false := by
            rw [beq_eq_false_iff_ne]; intro h
            have h1 := congrArg BitVec.toNat h
            simp only [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega : key.toNat / 8 < 2 ^ 64)] at h1
            omega
          apply SepWPp.of_sepWP_img (mid := entry + 212#64) hinvm
          conv => arg 4; simp only [decodeVarint2Spec, hd, sepConj_assoc, arm64_norm, hsp]
          apply SepWP.pure_elim; rintro ⟨htrm, hsm0, hsm1⟩
          apply SepWP.fold (skipBelow3_leaf_entails s0.sp 97 (by decide)) (by sep_focus)
          apply SepWP.fold (sliceCursorAfter_join hcur_le hcur_suf hrest_le_cur) (by sep_focus)
          apply SepWP.fold (authenticatorPBCapAt_mono A x.msgPtr m hrest_le_cur) (by sep_focus)
          wp_steps
          wp_reach; intro hinvm
          apply SepWPp.weaken_pre (P' := authLoopPre A s0 x.msgPtr x.bufRef x.slot x.ptr m x.bs rest)
            (by dsimp only [authLoopPre]; sep_entail)
          exact hcont key iwt rest _ hd hk_ge hwt hitag0
            (by simp only [arm64_norm]) (by simp only [arm64_norm, hrunm])
            (by simp only [arm64_norm, hspm]) (by simp only [arm64_norm, htrm, htr])
            (by simp only [arm64_norm, hsm1, hand_wt]) (by simp only [arm64_norm, hsm1, hw1, hw1_2, hw1_zext1, hw1_zext2])
            (by simp only [arm64_norm, hx19_m]) (by simp only [arm64_norm, hx20_m])
            (by simp only [arm64_norm, hx21_m]) (by simp only [arm64_norm, hx22_m])
            ⟨by simp only [arm64_norm, hx23_m], by simp only [arm64_norm, hx24_m],
             by simp only [arm64_norm, hx25_m], by simp only [arm64_norm, hx26_m],
             by simp only [arm64_norm, hx27_m], by simp only [arm64_norm, hx28_m],
       by simp only [arm64_norm, hvregs_m]⟩
            hinvm

/-- Main field-decoding loop induction for `Authenticator::merge` at `+0x0a0`. -/
theorem auth_loop_ok {b : BitVec 64} {img : Obj.Image} {A : RustAlloc}
    {H : String → Option (State → State)}
    (hFromCall : subroutine_ok (libsignalSessionCode.rebase b H)
      ((libsignalSessionCode.rebase b H).fnAddr authMergeName + 0xffffffffffffce68#64)
      (decodeErrorFromSpec A))
    (hPushCall : subroutine_ok (libsignalSessionCode.rebase b H)
      ((libsignalSessionCode.rebase b H).fnAddr authMergeName + 0xffffffffffffcb70#64)
      (decodeErrorPushSpec A))
    (hVarintCall : subroutine_ok (libsignalSessionCode.rebase b H)
      ((libsignalSessionCode.rebase b H).fnAddr authMergeName + 0xfffffffffffff594#64)
      (decodeVarint2Spec A))
    (hSkipCall : subroutine_ok (libsignalSessionCode.rebase b H)
      ((libsignalSessionCode.rebase b H).fnAddr authMergeName + 0xffffffffffffdc3c#64)
      (skipField3Spec A))
    (hBytesCall : subroutine_ok (libsignalSessionCode.rebase b H)
      ((libsignalSessionCode.rebase b H).fnAddr authMergeName + 0xfffffffffffff204#64)
      ((bytesMerge3RawSpec A).inImage img))
    {x : AuthMergeGhost} {R : SepProp} {s0 : State}
    {limit : Nat}
    (hsp_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hbs_lt : x.bs.length < 2 ^ 63)
    (hlim_lt : limit < 2 ^ 63) :
    ∀ (n : Nat) (m : ProtoAuthenticator) (cur : List (BitVec 8)) (s : State),
      cur.length ≤ n →
      cur.length ≤ x.bs.length →
      IsDropSuffix x.bs cur →
      (Proto.mergeMessage ProtoAuthenticator.mergeField (codecWireTypeToProto x.wt) x.msg x.bs 97).toOption =
        (mergeLoopBin ProtoAuthenticator.mergeField (cur.length - limit) m cur limit 96).map
          (fun m' => (m', x.bs.drop (x.bs.length - limit))) →
      s.pc = (libsignalSessionCode.rebase b H).fnAddr authMergeName + 160#64 →
      s.status = .Running →
      s.sp = s0.sp - 96#64 →
      s.trace = s0.trace →
      s.readReg64 (Reg.gpr 19#5) = x.bufRef →
      s.readReg64 (Reg.gpr 20#5) = x.msgPtr →
      s.readReg64 (Reg.gpr 21#5) = x.slot →
      s.readReg64 (Reg.gpr 22#5) = BitVec.ofNat 64 limit →
      HighCalleeSaved s0 s →
      ImgCallInv img s →
      SepWPp (libsignalSessionCode.rebase b H) (s0.readReg64 Reg.lr) s
        (authLoopPre A s0 x.msgPtr x.bufRef x.slot x.ptr m x.bs cur)
        (WppPost (authMergeSpec A) x R s0)
        (WppPanic R s0) := by
  have htag1_step := fun {s m rest iwt} => @auth_tag1_step b img A H hPushCall hBytesCall x R s0 s m rest iwt limit
  have htag2_step := fun {s m rest iwt} => @auth_tag2_step b img A H hPushCall hBytesCall x R s0 s m rest iwt limit
  have hskip_step := fun {s m rest tag iwt} => @auth_skip_step b img A H hSkipCall x R s0 s m rest iwt tag limit
  intro n
  induction n with
  | zero =>
    intro m cur s hcur_n hcur_le hcur_suf hres_cur hpc hrun hsp htr hx19 hx20 hx21 hx22 hcs _
    have hle_lim : cur.length ≤ limit := by omega
    exact auth_loop_le_exit hFromCall hle_lim hsp_align hcur_le hcur_suf hlim_lt
      hres_cur hpc hrun hsp htr hx21 hx22 hcs
  | succ n ih =>
    intro m cur s hcur_n hcur_le hcur_suf hres_cur hpc hrun hsp htr hx19 hx20 hx21 hx22 hcs hinv
    by_cases hle_lim : cur.length ≤ limit
    · exact auth_loop_le_exit hFromCall hle_lim hsp_align hcur_le hcur_suf hlim_lt
        hres_cur hpc hrun hsp htr hx21 hx22 hcs
    · have hcur_lt : cur.length < 2 ^ 63 := Nat.lt_of_le_of_lt hcur_le hbs_lt
      refine auth_decode_key_step hFromCall hVarintCall hle_lim hsp_align
        hcur_le hcur_lt hcur_suf hres_cur ?_ hpc hrun hsp htr hx19 hx20 hx21 hx22 hcs hinv
      intro key iwt rest s' hd hk_ge hwt hitag0 hpc' hrun' hsp' htr' hx0' hx1' hx19' hx20' hx21' hx22' hcs' hinv'
      obtain ⟨hx23', hx24', hx25', hx26', hx27', hx28', hvregs'⟩ := hcs'
      have hrest_lt_cur : rest.length < cur.length := decodeVarint_length hd
      have hrest_le_cur : rest.length ≤ cur.length := Nat.le_of_lt hrest_lt_cur
      have hrest_le : rest.length ≤ x.bs.length := Nat.le_trans hrest_le_cur hcur_le
      have hrest_lt : rest.length < 2 ^ 63 := Nat.lt_of_le_of_lt hrest_le hbs_lt
      have hrest_suf : IsDropSuffix x.bs rest :=
        suffix_trans hcur_le hcur_suf hrest_le_cur (decodeVarint_suffix hd)
      have hloop_ok := mergeLoopBin_of_key_ok (m := m) (depth' := 96)
        protoPrefixStep_protoAuthenticator_mergeField hle_lim hd hk_ge hwt hitag0
      by_cases htag1 : key.toNat / 8 = 1
      · rw [htag1] at hx1' hloop_ok
        rw [protoAuthenticator_mergeField_tag1] at hloop_ok
        authMerge_fetches b H 212 8
        generalize_entry (libsignalSessionCode.rebase b H).fnAddr authMergeName = entry
        examples_hide_fetches
        apply SepWPp.of_sepWP_img (mid := entry + 252#64) hinv'
        wp_steps
        wp_reach; intro hinv'
        have hnone_mb : mergeBytes iwt rest = none →
            (Proto.mergeMessage ProtoAuthenticator.mergeField (codecWireTypeToProto x.wt) x.msg x.bs 97).toOption = none := by
          intro hmb; simp only [hres_cur, hloop_ok, hmb, Option.map_none]
        refine htag1_step hsp_align hrest_le hrest_lt hrest_suf hnone_mb
          (fun v rest' s'' hmb hpc'' hrun'' hsp'' htr'' hx19'' hx20'' hx21'' hx22'' hcs'' hinv'' => ?_)
          (by simp only [arm64_norm]) (by simp only [arm64_norm, hrun'])
          (by simp only [arm64_norm, hsp']) (by simp only [arm64_norm, htr'])
          (by simp only [arm64_norm, hx0'])
          (by simp only [arm64_norm, hx19']) (by simp only [arm64_norm, hx20'])
          (by simp only [arm64_norm, hx21']) (by simp only [arm64_norm, hx22'])
          ⟨by simp only [arm64_norm, hx23'], by simp only [arm64_norm, hx24'],
           by simp only [arm64_norm, hx25'], by simp only [arm64_norm, hx26'],
           by simp only [arm64_norm, hx27'], by simp only [arm64_norm, hx28'],
           by simp only [arm64_norm, hvregs']⟩
          hinv'
        have hrest'_lt : rest'.length < rest.length := mergeBytes_length hmb
        have hrest'_le_rest : rest'.length ≤ rest.length := Nat.le_of_lt hrest'_lt
        have hres_next : (Proto.mergeMessage ProtoAuthenticator.mergeField (codecWireTypeToProto x.wt) x.msg x.bs 97).toOption =
            (mergeLoopBin ProtoAuthenticator.mergeField (rest'.length - limit) { m with rootKey := v } rest' limit 96).map
              (fun m' => (m', x.bs.drop (x.bs.length - limit))) := by
          simp only [hres_cur, hloop_ok, hmb, Option.map_some]
        exact ih { m with rootKey := v } rest' s''
          (by omega) (by omega)
          (suffix_trans hrest_le hrest_suf hrest'_le_rest (mergeBytes_suffix hmb))
          hres_next hpc'' hrun'' hsp'' htr'' hx19'' hx20'' hx21'' hx22'' hcs'' hinv''
      · by_cases htag2 : key.toNat / 8 = 2
        · rw [htag2] at hx1' hloop_ok
          rw [protoAuthenticator_mergeField_tag2] at hloop_ok
          authMerge_fetches b H 212 16
          generalize_entry (libsignalSessionCode.rebase b H).fnAddr authMergeName = entry
          examples_hide_fetches
          apply SepWPp.of_sepWP_img (mid := entry + 228#64) hinv'
          wp_steps
          wp_reach; intro hinv'
          have hnone_mb : mergeBytes iwt rest = none →
              (Proto.mergeMessage ProtoAuthenticator.mergeField (codecWireTypeToProto x.wt) x.msg x.bs 97).toOption = none := by
            intro hmb; simp only [hres_cur, hloop_ok, hmb, Option.map_none]
          refine htag2_step hsp_align hrest_le hrest_lt hrest_suf hnone_mb
            (fun v rest' s'' hmb hpc'' hrun'' hsp'' htr'' hx19'' hx20'' hx21'' hx22'' hcs'' hinv'' => ?_)
            (by simp only [arm64_norm]) (by simp only [arm64_norm, hrun'])
            (by simp only [arm64_norm, hsp']) (by simp only [arm64_norm, htr'])
            (by simp only [arm64_norm, hx0'])
            (by simp only [arm64_norm, hx19']) (by simp only [arm64_norm, hx20'])
            (by simp only [arm64_norm, hx21']) (by simp only [arm64_norm, hx22'])
            ⟨by simp only [arm64_norm, hx23'], by simp only [arm64_norm, hx24'],
             by simp only [arm64_norm, hx25'], by simp only [arm64_norm, hx26'],
             by simp only [arm64_norm, hx27'], by simp only [arm64_norm, hx28'],
           by simp only [arm64_norm, hvregs']⟩
            hinv'
          have hrest'_lt : rest'.length < rest.length := mergeBytes_length hmb
          have hrest'_le_rest : rest'.length ≤ rest.length := Nat.le_of_lt hrest'_lt
          have hres_next : (Proto.mergeMessage ProtoAuthenticator.mergeField (codecWireTypeToProto x.wt) x.msg x.bs 97).toOption =
              (mergeLoopBin ProtoAuthenticator.mergeField (rest'.length - limit) { m with macKey := v } rest' limit 96).map
                (fun m' => (m', x.bs.drop (x.bs.length - limit))) := by
            simp only [hres_cur, hloop_ok, hmb, Option.map_some]
          exact ih { m with macKey := v } rest' s''
            (by omega) (by omega)
            (suffix_trans hrest_le hrest_suf hrest'_le_rest (mergeBytes_suffix hmb))
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
          authMerge_fetches b H 212 16
          generalize_entry (libsignalSessionCode.rebase b H).fnAddr authMergeName = entry
          examples_hide_fetches
          apply SepWPp.of_sepWP_img (mid := entry + 140#64) hinv'
          wp_steps
          wp_reach; intro hinv'
          have hnone_sf : skipField (2 * rest.length + 2) 96 (key.toNat / 8) iwt rest = none →
              (Proto.mergeMessage ProtoAuthenticator.mergeField (codecWireTypeToProto x.wt) x.msg x.bs 97).toOption = none := by
            intro hsf; rw [hres_cur, hloop_ok, hsf]; rfl
          refine hskip_step hsp_align hrest_le hrest_lt hrest_suf hitag_lt hnone_sf
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
           by simp only [arm64_norm, hvregs']⟩
            hinv'
          have hrest'_le_rest : rest'.length ≤ rest.length :=
            (skip_length (2 * rest.length + 2)).1 _ _ _ _ _ hsf
          have hres_next : (Proto.mergeMessage ProtoAuthenticator.mergeField (codecWireTypeToProto x.wt) x.msg x.bs 97).toOption =
              (mergeLoopBin ProtoAuthenticator.mergeField (rest'.length - limit) m rest' limit 96).map
                (fun m' => (m', x.bs.drop (x.bs.length - limit))) := by
            rw [hres_cur, hloop_ok, hsf]; rfl
          exact ih m rest' s''
            (by omega) (by omega)
            (suffix_trans hrest_le hrest_suf hrest'_le_rest
              ((skip_suffix (2 * rest.length + 2)).1 _ _ _ _ _ hsf))
            hres_next hpc'' hrun'' hsp'' htr'' hx19'' hx20'' hx21'' hx22'' hcs'' hinv''

/-! ## Entry Prelude and Top-Level Theorems -/

/-- Contract-parameterized correctness of `Authenticator::merge` (`0x4df38`). -/
theorem auth_merge_ok_of_contracts {b : BitVec 64} {img : Obj.Image} {A : RustAlloc}
    {H : String → Option (State → State)}
    (hFromCall : subroutine_ok (libsignalSessionCode.rebase b H)
      ((libsignalSessionCode.rebase b H).fnAddr authMergeName + 0xffffffffffffce68#64)
      (decodeErrorFromSpec A))
    (hPushCall : subroutine_ok (libsignalSessionCode.rebase b H)
      ((libsignalSessionCode.rebase b H).fnAddr authMergeName + 0xffffffffffffcb70#64)
      (decodeErrorPushSpec A))
    (hVarintCall : subroutine_ok (libsignalSessionCode.rebase b H)
      ((libsignalSessionCode.rebase b H).fnAddr authMergeName + 0xfffffffffffff594#64)
      (decodeVarint2Spec A))
    (hSkipCall : subroutine_ok (libsignalSessionCode.rebase b H)
      ((libsignalSessionCode.rebase b H).fnAddr authMergeName + 0xffffffffffffdc3c#64)
      (skipField3Spec A))
    (hBytesCall : subroutine_ok (libsignalSessionCode.rebase b H)
      ((libsignalSessionCode.rebase b H).fnAddr authMergeName + 0xfffffffffffff204#64)
      ((bytesMerge3RawSpec A).inImage img)) :
    subroutine_ok (libsignalSessionCode.rebase b H)
      ((libsignalSessionCode.rebase b H).fnAddr authMergeName)
      ((authMergeSpec A).inImage img) := by
  apply subroutine_ok_inImage_of_withImgProp
  unfold withImgProp authMergeSpec
  wpp_init x s0
  apply SepWPp.elim_imgCallInvProp; intro hinv0
  replace hpc : s0.pc = (libsignalSessionCode.rebase b H).fnAddr authMergeName := by
    simpa only [arm64_norm, authMerge_fnOff] using hpc
  conv => arg 6; ext sf P_f; rw [sepConj_assoc, satisfies_pure_sepConj]
  change SepWPp (libsignalSessionCode.rebase b H) (s0.readReg64 Reg.lr) s0
    _ (WppPost (authMergeSpec A) x R s0) (WppPanic R s0)
  have herr0_exit := @auth_err0_ret_exit b A H x R s0
  have hfrom_exit := @auth_from_err_exit b A H hFromCall x R s0
  have hloop := @auth_loop_ok b img A H hFromCall hPushCall hVarintCall hSkipCall hBytesCall x R s0
  authMerge_fetches b H 0 100
  generalize_entry (libsignalSessionCode.rebase b H).fnAddr authMergeName = entry
  examples_hide_fetches
  by_cases hwt_ld : x.wt = .lengthDelimited
  · have h_1' : (s0.readReg64 (Reg.gpr 0#5)).setWidth 8 = 2#8 := by rw [h_1, hwt_ld]; rfl
    have hbeq := wt_beq_two_of_lengthDelimited h_1'
    have hbne1 : (BitVec.truncate 32 (s0.readReg64 (Reg.gpr 0#5)) &&& 255#32 != 2#32) = false := by
      simp only [bne, hbeq, Bool.not_true]
    have hbne2 : (BitVec.truncate 32 (BitVec.zeroExtend 64 (BitVec.truncate 32 (s0.readReg64 (Reg.gpr 0#5))) &&& 255#64) != 2#32) = false := by
      rw [BytesMergeFacts.truncate32_zeroExtend64_and_255_eq, h_1']; decide
    have hbne3 : (BitVec.truncate 32 (BitVec.zeroExtend 64 (BitVec.truncate 32 (s0.readReg64 (Reg.gpr 0#5)) &&& 255#32)) != 2#32) = false := by
      revert h_1'; bv_bits
    apply SepWPp.of_sepWP_img (mid := entry + 0xfffffffffffff594#64) hinv0
    conv => arg 4; rw [authMergeStack, stackAt_skipField3 s0.sp 97 (by decide), skipBelow3_leaf s0.sp 97 (by decide)]; simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
    apply SepWP.exists_elim; intro v19
    apply SepWP.exists_elim; intro v20
    apply SepWP.exists_elim; intro v21
    apply SepWP.exists_elim; intro v22
    apply SepWP.exists_elim; intro v_lr
    apply SepWP.exists_elim; intro v_fp
    wp_steps
    wp_reach; intro hinv0
    refine SepWPp.call_frame_keep (x := ⟨x.bufRef, x.slot, x.ptr, x.bs⟩)
      (ret_pc := entry + 48#64) hVarintCall hinv0
      (by simp only [arm64_norm]) (by simp only [arm64_norm, hrun])
      (by simp only [State.spAligned, arm64_norm]; exact hsp_align)
      (by simp only [arm64_norm])
      (by dsimp only [decodeVarint2Spec]; simp only [arm64_norm]; rfl)
      h (by sep_focus)
      (fun _ _ _ _ hex => allowPanic_not_exited hex)
      (fun sf _ hpan => allowPanic_frame' (by simp only [arm64_norm]) hpan) ?_
    intro sm hpcm hrunm hspm hcsm hinvm
    simp only [CalleeSavedPreserved] at hcsm
    obtain ⟨hx19_m, hx20_m, hx21_m, hx22_m, hx23_m, hx24_m, hx25_m, hx26_m, hx27_m, hx28_m, hfp_m, hvregs_m⟩ := hcsm
    simp (config := { decide := true }) only [arm64_norm] at hpcm hrunm hspm hx19_m hx20_m hx21_m hx22_m hx23_m hx24_m hx25_m hx26_m hx27_m hx28_m hfp_m hvregs_m
    cases hdv0 : decodeVarint x.bs with
    | none =>
      have hnone : (Proto.mergeMessage ProtoAuthenticator.mergeField (codecWireTypeToProto .lengthDelimited) x.msg x.bs 97).toOption = none := by
        rw [← mergeMessageBin_eq_proto_mergeMessage protoPrefixStep_protoAuthenticator_mergeField]
        simp [mergeMessageBin, codecWireTypeToProto, proto_decodeVarint_toOption, hdv0]
      rw [hwt_ld] at herr0_exit
      apply SepWPp.of_sepWP (mid := entry + 116#64)
      conv => arg 4; simp only [decodeVarint2Spec, hdv0, sepConj_assoc, arm64_norm]
      apply SepWP.pure_elim; rintro ⟨hsm0, htrm, hsm1⟩
      apply SepWP.fold (skipBelow3_leaf_entails s0.sp 97 (by decide)) (by sep_focus)
      apply SepWP.fold (authenticatorPBCapAt_entails_authenticatorPBAt A x.msgPtr x.bs.length x.msg) (by sep_focus)
      wp_steps
      wp_reach
      apply SepWPp.weaken_pre (P' :=
        decodeErrorAtStackLen A (sm.readReg64 (Reg.gpr 1#5)) 0 ∗
          memRegion (s0.sp - 96#64) 48 ∗
          skipBelow3 s0.sp 97 ∗
          authErrFrame A s0 x.msgPtr x.bufRef x.slot x.ptr x.msg x.bs)
        (by dsimp only [authErrFrame]; sep_entail)
      exact herr0_exit hnone hsp_align
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
        have hnone : (Proto.mergeMessage ProtoAuthenticator.mergeField (codecWireTypeToProto .lengthDelimited) x.msg x.bs 97).toOption = none := by
          rw [← mergeMessageBin_eq_proto_mergeMessage protoPrefixStep_protoAuthenticator_mergeField]
          rcases hdv0_p : Proto.decodeVarint x.bs with e | ⟨len', rest0'⟩
          · have hdv0' : decodeVarint x.bs = none := by rw [← proto_decodeVarint_toOption x.bs, hdv0_p]; rfl
            rw [hdv0] at hdv0'; nomatch hdv0'
          · have hdv0' : decodeVarint x.bs = some (len', rest0') := by rw [← proto_decodeVarint_toOption x.bs, hdv0_p]; rfl
            rw [hdv0] at hdv0'
            injection hdv0' with hpair; injection hpair with hlen hr0; subst hlen hr0
            simp [mergeMessageBin, codecWireTypeToProto, hdv0_p, Except.toOption, hlt_len]
        rw [hwt_ld] at hfrom_exit
        apply SepWPp.of_sepWP (mid := entry + 100#64)
        conv => arg 4; simp only [decodeVarint2Spec, hdv0, sliceCursorAfter_eq_split hrest0_le hrest0_suf,
          sliceCursorAt, memRegion_48_split_96 s0.sp,
          sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc, arm64_norm]
        apply SepWP.exists_elim; intro v_stk0
        apply SepWP.pure_elim; rintro ⟨⟨hsm0, hsm1⟩, htrm⟩
        apply SepWP.fold (skipBelow3_leaf_entails s0.sp 97 (by decide)) (by sep_focus)
        apply SepWP.fold (authenticatorPBCapAt_entails_authenticatorPBAt A x.msgPtr x.bs.length x.msg) (by sep_focus)
        wp_steps
        apply SepWP.fold (pointsTo64_pair_entails_memRegion16 x.slot rest0Ptr (BitVec.ofNat 64 rest0.length)) (by sep_focus)
        apply SepWP.fold (pointsToBytes_prefix_join hrest0_le hrest0_suf) (by sep_focus)
        wp_reach
        apply SepWPp.weaken_pre (P' :=
          ((s0.sp - 96#64) ↦₆₄ v_stk0) ∗
            memRegion (s0.sp - 88#64) 40 ∗
            skipBelow3 s0.sp 97 ∗
            authErrFrame A s0 x.msgPtr x.bufRef x.slot x.ptr x.msg x.bs)
          (by dsimp only [authErrFrame]; sep_entail)
        exact hfrom_exit hnone (by decide : KindNoHeap 0x8000000000000007#64) hsp_align
          (by simp only [arm64_norm]) (by simp only [arm64_norm, hrunm])
          (by simp only [arm64_norm, hspm]) (by simp only [arm64_norm, htrm])
          (by simp only [arm64_norm])
          ⟨by simp only [arm64_norm, hx23_m], by simp only [arm64_norm, hx24_m],
           by simp only [arm64_norm, hx25_m], by simp only [arm64_norm, hx26_m],
           by simp only [arm64_norm, hx27_m], by simp only [arm64_norm, hx28_m],
       by simp only [arm64_norm, hvregs_m]⟩
      · have hule := ule_len_of_ge hlt_len hrest0_lt
        have hsub := bv_len_sub_limit hlt_len
        have hlim_lt : rest0.length - len.toNat < 2 ^ 63 := by omega
        have hres0 : (Proto.mergeMessage ProtoAuthenticator.mergeField (codecWireTypeToProto .lengthDelimited) x.msg x.bs 97).toOption =
            (mergeLoopBin ProtoAuthenticator.mergeField (rest0.length - (rest0.length - len.toNat)) x.msg rest0 (rest0.length - len.toNat) 96).map
              (fun m' => (m', x.bs.drop (x.bs.length - (rest0.length - len.toNat)))) := by
          rw [← mergeMessageBin_eq_proto_mergeMessage protoPrefixStep_protoAuthenticator_mergeField]
          rcases hdv0_p : Proto.decodeVarint x.bs with e | ⟨len', rest0'⟩
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
        rw [hwt_ld] at hloop
        apply SepWPp.of_sepWP_img (mid := entry + 160#64) hinvm
        conv => arg 4; simp only [decodeVarint2Spec, hdv0, sliceCursorAfter_eq_split hrest0_le hrest0_suf,
          sliceCursorAt, sepConj_assoc, arm64_norm]
        apply SepWP.pure_elim; rintro ⟨⟨hsm0, hsm1⟩, htrm⟩
        apply SepWP.fold (skipBelow3_leaf_entails s0.sp 97 (by decide)) (by sep_focus)
        apply SepWP.fold (authenticatorPBCapAt_mono A x.msgPtr x.msg hrest0_le) (by sep_focus)
        wp_steps
        wp_reach; intro hinvm
        apply SepWPp.weaken_pre (P' :=
          authLoopPre A s0 x.msgPtr x.bufRef x.slot x.ptr x.msg x.bs rest0)
          (by dsimp only [authLoopPre]; rw [sliceCursorAfter_eq_split hrest0_le hrest0_suf, sliceCursorAt]; sep_entail)
        exact hloop hsp_align h hlim_lt
          rest0.length x.msg rest0 _ (Nat.le_refl _) hrest0_le hrest0_suf hres0
          (by simp only [arm64_norm]) (by simp only [arm64_norm, hrunm])
          (by simp only [arm64_norm, hspm]) (by simp only [arm64_norm, htrm])
          (by simp only [arm64_norm, hx19_m]) (by simp only [arm64_norm, hx20_m])
          (by simp only [arm64_norm]) (by simp only [arm64_norm, hsm1, hsub])
          ⟨by simp only [arm64_norm, hx23_m], by simp only [arm64_norm, hx24_m],
           by simp only [arm64_norm, hx25_m], by simp only [arm64_norm, hx26_m],
           by simp only [arm64_norm, hx27_m], by simp only [arm64_norm, hx28_m],
       by simp only [arm64_norm, hvregs_m]⟩
          hinvm
  · have hbeq := wt_beq_two_of_ne_lengthDelimited h_1 hwt_ld
    have hbne1 : (BitVec.truncate 32 (s0.readReg64 (Reg.gpr 0#5)) &&& 255#32 != 2#32) = true := by
      simp only [bne, hbeq, Bool.not_false]
    have hbne2 : (BitVec.truncate 32 (BitVec.zeroExtend 64 (BitVec.truncate 32 (s0.readReg64 (Reg.gpr 0#5))) &&& 255#64) != 2#32) = true := by
      rw [BytesMergeFacts.truncate32_zeroExtend64_and_255_eq, h_1]
      cases hxwt : x.wt <;> simp_all [WireType.toNat]
    have hbne3 : (BitVec.truncate 32 (BitVec.zeroExtend 64 (BitVec.truncate 32 (s0.readReg64 (Reg.gpr 0#5)) &&& 255#32)) != 2#32) = true := by
      rw [show BitVec.truncate 32 (BitVec.zeroExtend 64 (BitVec.truncate 32 (s0.readReg64 (Reg.gpr 0#5)) &&& 255#32)) =
            BitVec.truncate 32 (s0.readReg64 (Reg.gpr 0#5)) &&& 255#32 by bv_bits]
      exact hbne1
    have hnone : (Proto.mergeMessage ProtoAuthenticator.mergeField (codecWireTypeToProto x.wt) x.msg x.bs 97).toOption = none := by
      rw [← mergeMessageBin_eq_proto_mergeMessage protoPrefixStep_protoAuthenticator_mergeField]
      unfold mergeMessageBin
      cases hwt_eq : x.wt <;> simp [hwt_eq, codecWireTypeToProto] at hwt_ld ⊢
    apply SepWPp.of_sepWP (mid := entry + 100#64)
    conv => arg 4; rw [authMergeStack, stackAt_skipField3 s0.sp 97 (by decide), sliceCursorAt, memRegion_48_wtErr96 s0.sp]; simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
    apply SepWP.exists_elim; intro v19
    apply SepWP.exists_elim; intro v20
    apply SepWP.exists_elim; intro v21
    apply SepWP.exists_elim; intro v22
    apply SepWP.exists_elim; intro v_lr
    apply SepWP.exists_elim; intro v_fp
    apply SepWP.exists_elim; intro b_wt1
    apply SepWP.exists_elim; intro b_wt0
    apply SepWP.exists_elim; intro v_wt0
    wp_steps
    apply SepWP.fold (wtErr96_entails_memRegion40 s0.sp _ _) (by sep_focus)
    apply SepWP.fold (pointsTo64_pair_entails_memRegion16 x.slot x.ptr (BitVec.ofNat 64 x.bs.length)) (by sep_focus)
    apply SepWP.fold (authenticatorPBCapAt_entails_authenticatorPBAt A x.msgPtr x.bs.length x.msg) (by sep_focus)
    wp_reach
    apply SepWPp.weaken_pre (P' :=
      ((s0.sp - 96#64) ↦₆₄ v_wt0) ∗
        memRegion (s0.sp - 88#64) 40 ∗
        skipBelow3 s0.sp 97 ∗
        authErrFrame A s0 x.msgPtr x.bufRef x.slot x.ptr x.msg x.bs)
      (by dsimp only [authErrFrame]; sep_entail)
    exact hfrom_exit hnone (by decide : KindNoHeap 0x8000000000000006#64) hsp_align
      (by simp only [arm64_norm]) (by simp only [arm64_norm, hrun])
      (by simp only [arm64_norm]) (by simp only [arm64_norm])
      (by simp only [arm64_norm])
      ⟨by simp only [arm64_norm], by simp only [arm64_norm],
       by simp only [arm64_norm], by simp only [arm64_norm],
       by simp only [arm64_norm], by simp only [arm64_norm],
       by simp only [arm64_norm]⟩

/-- Address-resolved correctness of `Authenticator::merge` (`0x4df38`). -/
theorem auth_merge_ok_of_fnAddr {b : BitVec 64} {img : Obj.Image} {A : RustAlloc}
    {H : String → Option (State → State)}
    (hFrom : subroutine_ok (libsignalSessionCode.rebase b H)
      ((libsignalSessionCode.rebase b H).fnAddr decodeErrorFromName)
      (decodeErrorFromSpec A))
    (hPush : subroutine_ok (libsignalSessionCode.rebase b H)
      ((libsignalSessionCode.rebase b H).fnAddr decodeErrorPushName)
      (decodeErrorPushSpec A))
    (hVarint : subroutine_ok (libsignalSessionCode.rebase b H)
      ((libsignalSessionCode.rebase b H).fnAddr Varint.decodeVarint2Name)
      (decodeVarint2Spec A))
    (hSkip : subroutine_ok (libsignalSessionCode.rebase b H)
      ((libsignalSessionCode.rebase b H).fnAddr skipField3Name)
      (skipField3Spec A))
    (hBytes : subroutine_ok (libsignalSessionCode.rebase b H)
      ((libsignalSessionCode.rebase b H).fnAddr bytesMerge3Name)
      ((bytesMerge3RawSpec A).inImage img)) :
    subroutine_ok (libsignalSessionCode.rebase b H)
      ((libsignalSessionCode.rebase b H).fnAddr authMergeName)
      ((authMergeSpec A).inImage img) := by
  have hFromCall : subroutine_ok (libsignalSessionCode.rebase b H)
      ((libsignalSessionCode.rebase b H).fnAddr authMergeName + 0xffffffffffffce68#64)
      (decodeErrorFromSpec A) := by
    rw [fnAddr_offset_eq_H (name := authMergeName) (callee := decodeErrorFromName)]
    exact hFrom
  have hPushCall : subroutine_ok (libsignalSessionCode.rebase b H)
      ((libsignalSessionCode.rebase b H).fnAddr authMergeName + 0xffffffffffffcb70#64)
      (decodeErrorPushSpec A) := by
    rw [fnAddr_offset_eq_H (name := authMergeName) (callee := decodeErrorPushName)]
    exact hPush
  have hVarintCall : subroutine_ok (libsignalSessionCode.rebase b H)
      ((libsignalSessionCode.rebase b H).fnAddr authMergeName + 0xfffffffffffff594#64)
      (decodeVarint2Spec A) := by
    rw [fnAddr_offset_eq_H (name := authMergeName) (callee := Varint.decodeVarint2Name)]
    exact hVarint
  have hSkipCall : subroutine_ok (libsignalSessionCode.rebase b H)
      ((libsignalSessionCode.rebase b H).fnAddr authMergeName + 0xffffffffffffdc3c#64)
      (skipField3Spec A) := by
    rw [fnAddr_offset_eq_H (name := authMergeName) (callee := skipField3Name)]
    exact hSkip
  have hBytesCall : subroutine_ok (libsignalSessionCode.rebase b H)
      ((libsignalSessionCode.rebase b H).fnAddr authMergeName + 0xfffffffffffff204#64)
      ((bytesMerge3RawSpec A).inImage img) := by
    rw [fnAddr_offset_eq_H (name := authMergeName) (callee := bytesMerge3Name)]
    exact hBytes
  exact auth_merge_ok_of_contracts hFromCall hPushCall hVarintCall hSkipCall hBytesCall

/-- `.inImage img` contract proposition for `authMergeSpec A`. -/
def AuthMergeOkX (img : Obj.Image) (A : RustAlloc) (ext : String → Option (State → State)) : Prop :=
  subroutine_ok (tripleRatchetProgAtExt img.base ext)
    ((tripleRatchetProgAtExt img.base ext).fnAddr authMergeName)
    ((authMergeSpec A).inImage img)

abbrev AuthMergeOkExt (img : Obj.Image) (A : RustAlloc) (ext : String → Option (State → State)) : Prop :=
  AuthMergeOkX img A ext

theorem auth_merge_ok_ext {img : Obj.Image} {A : RustAlloc}
    {ext : String → Option (State → State)}
    (hFrom : subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr decodeErrorFromName)
      (decodeErrorFromSpec A))
    (hPush : subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr decodeErrorPushName)
      (decodeErrorPushSpec A))
    (hVarint : subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr Varint.decodeVarint2Name)
      (decodeVarint2Spec A))
    (hSkip : subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr skipField3Name)
      (skipField3Spec A))
    (hBytes : BytesMerge3OkExt img A ext) :
    AuthMergeOkX img A ext :=
  auth_merge_ok_of_fnAddr hFrom hPush hVarint hSkip hBytes

theorem auth_merge_ok_ext_x {img : Obj.Image} {A : RustAlloc}
    {ext : String → Option (State → State)}
    (hFrom : subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr decodeErrorFromName)
      (decodeErrorFromSpec A))
    (hPush : subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr decodeErrorPushName)
      (decodeErrorPushSpec A))
    (hVarint : subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr Varint.decodeVarint2Name)
      (decodeVarint2Spec A))
    (hSkip : subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr skipField3Name)
      (skipField3Spec A))
    (hBytes : BytesMerge3OkExt img A ext) :
    AuthMergeOkX img A ext :=
  auth_merge_ok_ext hFrom hPush hVarint hSkip hBytes

/-- Instantiates `BytesMerge3OkExt` via `bytes_merge_3_ok_ext`. -/
theorem auth_merge_ok_ext_of_bytes_contracts {img : Obj.Image} {A : RustAlloc}
    {ext : String → Option (State → State)}
    (himg : Obj.Loads libsignalSessionImage img)
    (hAlloc : AllocContracts img.base A ext)
    (hFrom : subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr decodeErrorFromName)
      (decodeErrorFromSpec A))
    (hPush : subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr decodeErrorPushName)
      (decodeErrorPushSpec A))
    (hVarint : subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr Varint.decodeVarint2Name)
      (decodeVarint2Spec A))
    (hSkip : subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr skipField3Name)
      (skipField3Spec A))
    (hBytesFromVec : subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr bytesFromVecName)
      ((bytesFromVecSpec A img.base).inImage img))
    (hReserve7 : subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr doReserve7Name) (doReserveSpec A))
    (hVtableSlot : BytesVtableSlotLoadedStmt)
    (hVtableDrop : ∀ (tmpPtr : BitVec 64) (v : List (BitVec 8)),
      subroutine_ok (tripleRatchetProgAtExt img.base ext)
        (bytesDropFnAddr img.base tmpPtr v.length)
        ((bytesVtableDropSpec A tmpPtr v v.length).inImage img)) :
    AuthMergeOkX img A ext :=
  auth_merge_ok_ext hFrom hPush hVarint hSkip
    (bytes_merge_3_ok_ext himg hAlloc hFrom
      (subroutine_ok_inImage_of_subroutine_ok img hVarint)
      hBytesFromVec hReserve7 hVtableSlot hVtableDrop)

/-! ## `optAuthenticatorPBCapAt` Bridge Lemmas -/

/-- `Option<ProtoAuthenticator>` at `a` (48 bytes) with `BytesMergeCapOk cap bsLen` when `some`. -/
def optAuthenticatorPBCapAt (A : RustAlloc) (a : BitVec 64) (bsLen : Nat) :
    Option ProtoAuthenticator → SepProp
  | none => (a ↦₆₄ noneCap) ∗ memRegion (a + 8#64) 40
  | some auth => authenticatorPBCapAt A a bsLen auth

@[simp]
theorem optAuthenticatorPBCapAt_none (A : RustAlloc) (a : BitVec 64) (bsLen : Nat) :
    optAuthenticatorPBCapAt A a bsLen none = (a ↦₆₄ noneCap) ∗ memRegion (a + 8#64) 40 := rfl

@[simp]
theorem optAuthenticatorPBCapAt_some (A : RustAlloc) (a : BitVec 64) (bsLen : Nat)
    (auth : ProtoAuthenticator) :
    optAuthenticatorPBCapAt A a bsLen (some auth) = authenticatorPBCapAt A a bsLen auth := rfl

theorem optAuthenticatorPBCapAt_mono (A : RustAlloc) (a : BitVec 64)
    (opt : Option ProtoAuthenticator) {m n : Nat} (hle : m ≤ n) :
    optAuthenticatorPBCapAt A a n opt ⊢ optAuthenticatorPBCapAt A a m opt := by
  cases opt with
  | none => exact Entails.refl _
  | some auth => exact authenticatorPBCapAt_mono A a auth hle

theorem optAuthenticatorPBCapAt_entails_optAuthenticatorPBAt (A : RustAlloc) (a : BitVec 64)
    (n : Nat) (opt : Option ProtoAuthenticator) :
    optAuthenticatorPBCapAt A a n opt ⊢ optAuthenticatorPBAt A a opt := by
  cases opt with
  | none => exact Entails.refl _
  | some auth => exact authenticatorPBCapAt_entails_authenticatorPBAt A a n auth

theorem optAuthenticatorPBAt_entails_exists (A : RustAlloc) (a : BitVec 64)
    (opt : Option ProtoAuthenticator) :
    optAuthenticatorPBAt A a opt ⊢ ∃∗ opt' : Option ProtoAuthenticator, optAuthenticatorPBAt A a opt' :=
  Entails.sepExists_intro opt

theorem authenticatorPBAt_exists_entails_opt_exists (A : RustAlloc) (a : BitVec 64) :
    (∃∗ m' : ProtoAuthenticator, authenticatorPBAt A a m') ⊢
      ∃∗ opt' : Option ProtoAuthenticator, optAuthenticatorPBAt A a opt' :=
  Entails.sepExists_elim fun m' => Entails.sepExists_intro (P := optAuthenticatorPBAt A a) (some m')

theorem optAuthenticatorPBAt_entails_cap_of_lt32 (A : RustAlloc) (a : BitVec 64)
    {n : Nat} (hn : n < 2 ^ 32) (opt : Option ProtoAuthenticator) :
    optAuthenticatorPBAt A a opt ⊢ optAuthenticatorPBCapAt A a n opt := by
  cases opt with
  | none => exact Entails.refl _
  | some auth => exact authenticatorPBAt_entails_cap_of_lt32 A a hn auth

theorem memRegion_40_cells (a : BitVec 64) :
    memRegion (a + 8#64) 40 =
      (∃∗ w1 : BitVec 64, ∃∗ w2 : BitVec 64, ∃∗ w3 : BitVec 64,
       ∃∗ w4 : BitVec 64, ∃∗ w5 : BitVec 64,
        ((a + 8#64) ↦₆₄ w5) ∗ ((a + 16#64) ↦₆₄ w4) ∗ ((a + 24#64) ↦₆₄ w3) ∗
        ((a + 32#64) ↦₆₄ w2) ∗ ((a + 40#64) ↦₆₄ w1)) := by
  have s1 := ProofLib.memRegion_split (a + 8#64) 8 32 (by decide)
  have s2 := ProofLib.memRegion_split (a + 8#64 + 8#64) 8 24 (by decide)
  have s3 := ProofLib.memRegion_split (a + 8#64 + 8#64 + 8#64) 8 16 (by decide)
  have s4 := ProofLib.memRegion_split (a + 8#64 + 8#64 + 8#64 + 8#64) 8 8 (by decide)
  rw [s1, s2, s3, s4,
    ProofLib.memRegion_eight, ProofLib.memRegion_eight, ProofLib.memRegion_eight,
    ProofLib.memRegion_eight, ProofLib.memRegion_eight]
  simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc,
    BitVec.add_assoc, BitVec.reduceAdd]

/-- Folds default-initialized `Option::get_or_insert_with` cells into `authenticatorPBCapAt A a n default`. -/
theorem default_cells_entails_authenticatorPBCapAt (A : RustAlloc) (a : BitVec 64) (n : Nat) :
    (a ↦₆₄ 0#64) ∗ ((a + 8#64) ↦₆₄ 1#64) ∗ ((a + 16#64) ↦₆₄ 0#64) ∗
      ((a + 24#64) ↦₆₄ 0#64) ∗ ((a + 32#64) ↦₆₄ 1#64) ∗ ((a + 40#64) ↦₆₄ 0#64) ⊢
      authenticatorPBCapAt A a n (default : ProtoAuthenticator) := by
  refine Entails.trans ?_ (authenticatorPBPinnedAt_zero_entails_cap A 1#64 1#64 a n ⟨[], []⟩)
  unfold authenticatorPBPinnedAt vecU8At vecHeader
  have h1 : (a + 0x18#64) + 8#64 = a + 32#64 := by bv_omega
  have h2 : (a + 0x18#64) + 16#64 = a + 40#64 := by bv_omega
  have h0 : a + 0x18#64 = a + 24#64 := rfl
  rw [h1, h2, h0]
  dsimp only [List.length_nil]
  simp only [BitVec.ofNat_eq_ofNat, BitVec.toNat_ofNat, Nat.zero_mod, Nat.le_refl,
    true_and, ↓reduceIte, sepConj_emp]
  have hp : (0 : Nat) < 2 ^ 63 ∧ (1#64 : BitVec 64) ≠ 0#64 := ⟨by decide, by decide⟩
  refine Entails.trans (Entails.pure_right hp (Entails.refl _)) ?_
  refine Entails.trans (Entails.pure_right hp (Entails.refl _)) ?_
  exact Entails.of_eq (by ac_rfl)

end CryptoVerification.SpqrV1.Auth
