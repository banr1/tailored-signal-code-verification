/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SpqrV1.Prost.MessageMerge.UnchunkedEkSentCt1ReceivedStep
import GeneratedLean.LibsignalSessionCode -- shake: keep
import LibsignalBinary.Proofs.FnOffEq
import LibsignalBinary.Proofs.ProtoCodecRoundTrip
import LibsignalBinary.Proofs.SpqrV1.Auth.Merge
import LibsignalBinary.Proofs.SpqrV1.Prost.MessageMerge.EpochDirection
import LibsignalBinary.Proofs.TripleRatchet.GeneralizeEntry
import LibsignalBinary.Proofs.TripleRatchet.Prost.BytesMerge.Phase1
import ProofLib.SepLogic.WPp

/-!
# Verification of `Unchunked.EkSentCt1Received::merge` (`0x51c00`, Block `311`)

Proves tag-4 (`ct1`), loop-exit, key-decode, loop-induction, and top-level subroutine contracts for
`prost::encoding::message::merge::<spqr::proto::pq_ratchet::v1_state::unchunked::EkSentCt1Received, &mut &[u8]>`
in both `.inImage img` and `[LibsignalPlacement]` forms on Block `311`.
-/

@[expose] public section

namespace CryptoVerification.SpqrV1.Prost.MessageMerge

open Arm64 ProofLib ProofLib.ProgramReflection
open CryptoGames.LibsignalSession
open CryptoVerification.RustHeap CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchetRepr CryptoVerification.LibsignalProtoCodec
open CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalTripleRatchet.Prost
open CryptoVerification.SpqrV1.Varint
open CryptoVerification.SpqrV1.ProtoRepr
open CryptoVerification.SpqrV1.Prost.BytesMerge
open CryptoVerification.SpqrV1.Auth hiding bv64_sub_zero bv64_add_zero
open CryptoVerification.SpqrV1.Drop
open CryptoVerification.LibsignalSpqrV1 hiding decodeVarint encodeVarint WireType
open CryptoVerification.CodeLayout
open ChunkedMerge

set_option maxRecDepth 200000
set_option maxHeartbeats 400000
set_option linter.unusedSimpArgs false

attribute [local irreducible] Program.fetch Program.externAt?
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero
attribute [local simp, local arm64_norm] bv64_sub_zero_u bv64_add_zero_u unchunkedEkSentCt1ReceivedMerge_fnOff

/-! ## 1. Tag 4 (`ct1`) Step -/

/-- Step lemma for tag 4 (`ct1` at `msgPtr + 0x18`, `+0x124` = `entry + 292#64`):
calls `bytes::merge [local#3]` (`entry + 0xffffffffffffb53c#64`) and either exits via `+0x1e4..+0x204 -> +0x290`
on error or continues at `entry + 152#64` (`+0x098`). -/
theorem ekSent_tag4_step {img : Obj.Image} {b : BitVec 64} {A : RustAlloc}
    {H : String → Option (State → State)}
    (hPushCall : subroutine_ok (libsignalSessionCode.rebase b H)
      ((libsignalSessionCode.rebase b H).fnAddr unchunkedEkSentCt1ReceivedMergeName + 0xffffffffffff8ea8#64)
      (decodeErrorPushSpec A))
    (hBytesCall : subroutine_ok (libsignalSessionCode.rebase b H)
      ((libsignalSessionCode.rebase b H).fnAddr unchunkedEkSentCt1ReceivedMergeName + 0xffffffffffffb53c#64)
      ((bytesMerge3RawSpec A).inImage img))
    {x : UnchunkedEkSentCt1ReceivedMergeGhost} {R : SepProp} {s0 s : State}
    {m : V1State.Unchunked.EkSentCt1Received} {rest : List (BitVec 8)} {iwt : WireType} {limit : Nat}
    (hsp_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hrest_le : rest.length ≤ x.bs.length)
    (hrest_lt : rest.length < 2 ^ 63)
    (hrest_suf : IsDropSuffix x.bs rest)
    (hnone_of_mb : mergeBytes iwt rest = none →
      (Proto.mergeMessage V1State.Unchunked.EkSentCt1Received.mergeField (codecWireTypeToProto x.wt) x.msg x.bs 98).toOption = none)
    (hcont : ∀ (v rest' : List (BitVec 8)) (s' : State),
      mergeBytes iwt rest = some (v, rest') →
      s'.pc = (libsignalSessionCode.rebase b H).fnAddr unchunkedEkSentCt1ReceivedMergeName + 152#64 →
      s'.status = .Running →
      s'.sp = s0.sp - 112#64 →
      s'.trace = s0.trace →
      s'.readReg64 (Reg.gpr 19#5) = x.bufRef →
      s'.readReg64 (Reg.gpr 20#5) = x.msgPtr →
      s'.readReg64 (Reg.gpr 21#5) = x.slot →
      s'.readReg64 (Reg.gpr 22#5) = BitVec.ofNat 64 limit →
      s'.readReg64 (Reg.gpr 23#5) = 1#64 →
      HighCalleeSaved24 s0 s' →
      ImgCallInv img s' →
      SepWPp (libsignalSessionCode.rebase b H) (s0.readReg64 Reg.lr) s'
        (ekSentLoopPre A s0 x.msgPtr x.bufRef x.slot x.ptr { m with ct1 := v } x.bs rest')
        (WppPost (unchunkedEkSentCt1ReceivedMergeOwnSpec A) x R s0)
        (WppPanic R s0))
    (hpc : s.pc = (libsignalSessionCode.rebase b H).fnAddr unchunkedEkSentCt1ReceivedMergeName + 292#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = s0.sp - 112#64)
    (htr : s.trace = s0.trace)
    (hx0 : s.readReg64 (Reg.gpr 0#5) = BitVec.ofNat 64 iwt.toNat)
    (hx19 : s.readReg64 (Reg.gpr 19#5) = x.bufRef)
    (hx20 : s.readReg64 (Reg.gpr 20#5) = x.msgPtr)
    (hx21 : s.readReg64 (Reg.gpr 21#5) = x.slot)
    (hx22 : s.readReg64 (Reg.gpr 22#5) = BitVec.ofNat 64 limit)
    (hx23 : s.readReg64 (Reg.gpr 23#5) = 1#64)
    (hcs : HighCalleeSaved24 s0 s) (hinv : ImgCallInv img s) :
    SepWPp (libsignalSessionCode.rebase b H) (s0.readReg64 Reg.lr) s
      (ekSentLoopPre A s0 x.msgPtr x.bufRef x.slot x.ptr m x.bs rest)
      (WppPost (unchunkedEkSentCt1ReceivedMergeOwnSpec A) x R s0)
      (WppPanic R s0) := by
  obtain ⟨hx24, hx25, hx26, hx27, hx28, hvregs⟩ := hcs
  let restPtr : BitVec 64 := x.ptr + BitVec.ofNat 64 (x.bs.length - rest.length)
  have hpush_exit := @ekSent_push_err_exit b A H hPushCall x R s0
  ekSentMerge_fetches b H 292 24
  ekSentMerge_fetches b H 484 36
  generalize_entry (libsignalSessionCode.rebase b H).fnAddr unchunkedEkSentCt1ReceivedMergeName = entry
  examples_hide_fetches
  refine SepWPp.of_sepWP_img (mid := entry + 0xffffffffffffb53c#64) hinv ?_
  conv =>
    arg 4
    rw [ekSentLoopPre, protoUnchunkedEkSentCt1ReceivedCapAt,
      sliceCursorAfter_eq_split hrest_le hrest_suf,
      unchunkedMergeBelow_bytesMerge3 s0.sp]
  conv =>
    arg 4
    rw [show vecU8CapAt A (x.msgPtr + 0x18#64) rest.length m.ct1 =
      (∃∗ cap : BitVec 64, ∃∗ ptr : BitVec 64, ⌜BytesMergeCapOk cap rest.length⌝ ∗ vecU8At A (x.msgPtr + 0x18#64) cap ptr m.ct1) from rfl]
    simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
  apply SepWP.exists_elim; intro cap2
  apply SepWP.exists_elim; intro ptr2
  conv => arg 4; rw [← sepConj_assoc, sepConj_comm (vecU8CapAt A x.msgPtr rest.length m.dk), sepConj_assoc]
  apply SepWP.pure_elim; intro hcap2
  wp_steps
  wp_reach; intro hinv_c
  refine SepWPp.call_frame_inImage (hinv := hinv_c) (x := ⟨iwt, x.msgPtr + 0x18#64, cap2, ptr2, m.ct1, x.bufRef, x.slot, restPtr, rest⟩)
    (ret_pc := entry + 304#64) hBytesCall
    (by simp only [arm64_norm]) (by simp only [arm64_norm, hrun])
    (by simp only [State.spAligned, hsp, arm64_norm]; exact hsp_align)
    (by simp only [arm64_norm])
    (by dsimp only [bytesMerge3RawSpec]; simp only [arm64_norm, hsp, hx0, hx19, hx20, setWidth8_ofNat64_wt]; rfl)
    (⟨hrest_lt, hcap2⟩ : rest.length < 2 ^ 63 ∧ BytesMergeCapOk cap2 rest.length)
    (by sep_focus)
    (fun _ _ _ _ hex => allowPanic_not_exited hex)
    (fun sf _ hpan => by dsimp only [bytesMerge3RawSpec] at hpan; exact allowPanic_frame' (by simp only [arm64_norm, htr]) hpan)
    ?_
  intro sm hpcm hrunm hspm hcsm hinv_m
  simp only [CalleeSavedPreserved] at hcsm
  obtain ⟨hx19_m, hx20_m, hx21_m, hx22_m, hx23_m, hx24_m, hx25_m, hx26_m, hx27_m, hx28_m, hfp_m, hvregs_m⟩ := hcsm
  simp (config := { decide := true }) only [arm64_norm, hsp, hx19, hx20, hx21, hx22, hx23, hx24, hx25, hx26, hx27, hx28, hvregs] at hpcm hrunm hspm hx19_m hx20_m hx21_m hx22_m hx23_m hx24_m hx25_m hx26_m hx27_m hx28_m hfp_m hvregs_m hvregs_m
  cases hmb : mergeBytes iwt rest with
  | none =>
    have hnone := hnone_of_mb hmb
    apply SepWPp.of_sepWP (mid := entry + 656#64)
    conv => arg 4; simp only [bytesMerge3RawSpec, hmb, memRegion_48_split_112 s0.sp,
      sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc, arm64_norm, hsp]
    apply SepWP.exists_elim; intro v_stk0
    apply SepWP.pure_elim; rintro ⟨htrm, hsm0⟩
    have hcbnz : (sm.readReg64 (Reg.gpr 0#5) == 0#64) = false := beq_eq_false_iff_ne.mpr hsm0
    apply SepWP.fold (unchunkedMergeBelow_bytesMerge3_entails s0.sp) (by sep_focus)
    apply SepWP.fold (pointsToBytes_prefix_join hrest_le hrest_suf) (by sep_focus)
    have hct1 : vecU8At A (x.msgPtr + 24#64) cap2 ptr2 m.ct1 ⊢ vecU8 A (x.msgPtr + 0x18#64) m.ct1 :=
      Entails.sepExists_right cap2 (Entails.sepExists_right ptr2 (Entails.refl _))
    apply SepWP.fold hct1 (by sep_focus)
    apply SepWP.fold (vecU8CapAt_entails_vecU8_u A x.msgPtr rest.length m.dk) (by sep_focus)
    apply SepWP.fold (optProtoAuthenticatorCapAt_entails_optProtoAuthenticatorAt A (x.msgPtr + 0x30#64) rest.length m.auth) (by sep_focus)
    apply SepWP.fold (ekSent_fields_entails_exists A x.msgPtr m) (by sep_focus)
    wp_steps
    wp_reach
    apply SepWPp.weaken_pre (P' :=
      ((s0.sp - 112#64) ↦₆₄ sm.readReg64 (Reg.gpr 0#5)) ∗
        decodeErrorAtStackLen A (sm.readReg64 (Reg.gpr 0#5)) 0 ∗
        memRegion (s0.sp - 104#64) 40 ∗
        unchunkedMergeBelow s0.sp ∗
        ekSentErrFrame A s0 x.msgPtr x.bufRef x.slot x.ptr x.bs)
      (by dsimp only [ekSentErrFrame]; sep_entail)
    exact hpush_exit hnone hsm0 (Nat.zero_le 1) hsp_align
      (by simp only [arm64_norm]) (by simp only [arm64_norm, hrunm])
      (by simp only [arm64_norm, hspm]) (by simp only [arm64_norm, htrm, htr])
      (by simp only [arm64_norm, hspm])
      ⟨by simp only [arm64_norm, hx24_m], by simp only [arm64_norm, hx25_m],
       by simp only [arm64_norm, hx26_m], by simp only [arm64_norm, hx27_m],
       by simp only [arm64_norm, hx28_m], by simp only [arm64_norm, hvregs_m]⟩
  | some p =>
    rcases p with ⟨v, rest'⟩
    have hrest'_le : rest'.length ≤ rest.length := mergeBytes_length hmb
    refine SepWPp.of_sepWP_img (mid := entry + 152#64) hinv_m ?_
    conv => arg 4; simp only [bytesMerge3RawSpec, hmb, sepExists_sepConj_left, sepExists_sepConj_right,
      sepConj_assoc, arm64_norm, hsp]
    apply SepWP.exists_elim; intro cap2'
    apply SepWP.exists_elim; intro ptr2'
    apply SepWP.pure_elim; rintro ⟨htrm, hsm0, hcap2'⟩
    apply SepWP.fold (unchunkedMergeBelow_bytesMerge3_entails s0.sp) (by sep_focus)
    apply SepWP.fold (sliceCursorAfter_join hrest_le hrest_suf hrest'_le) (by sep_focus)
    have hct1_cap : vecU8At A (x.msgPtr + 24#64) cap2' ptr2' v ⊢ vecU8CapAt A (x.msgPtr + 0x18#64) rest'.length v := by
      unfold vecU8CapAt
      refine Entails.trans (Entails.pure_right hcap2' (Entails.refl _)) ?_
      exact Entails.sepExists_right cap2' (Entails.sepExists_right ptr2' (Entails.refl _))
    apply SepWP.fold hct1_cap (by sep_focus)
    apply SepWP.fold (vecU8CapAt_mono_u A x.msgPtr m.dk hrest'_le) (by sep_focus)
    apply SepWP.fold (optProtoAuthenticatorCapAt_mono A (x.msgPtr + 0x30#64) m.auth hrest'_le) (by sep_focus)
    wp_steps
    wp_reach; intro hinv_n
    apply SepWPp.weaken_pre (P' :=
      ekSentLoopPre A s0 x.msgPtr x.bufRef x.slot x.ptr { m with ct1 := v } x.bs rest')
      (by dsimp only [ekSentLoopPre, protoUnchunkedEkSentCt1ReceivedCapAt]; sep_entail)
    exact hcont v rest' _ hmb
      (by simp only [arm64_norm]) (by simp only [arm64_norm, hrunm])
      (by simp only [arm64_norm, hspm]) (by simp only [arm64_norm, htrm, htr])
      (by simp only [arm64_norm, hx19_m]) (by simp only [arm64_norm, hx20_m])
      (by simp only [arm64_norm, hx21_m]) (by simp only [arm64_norm, hx22_m])
      (by simp only [arm64_norm, hx23_m])
      ⟨by simp only [arm64_norm, hx24_m], by simp only [arm64_norm, hx25_m],
       by simp only [arm64_norm, hx26_m], by simp only [arm64_norm, hx27_m],
       by simp only [arm64_norm, hx28_m], by simp only [arm64_norm, hvregs_m]⟩ hinv_n

/-! ## 2. Loop Exit, Key Decode, and Main Loop Induction -/

/-- Loop exit lemma at `+0x098` (`entry + 152#64`) when `cur.length ≤ limit`. -/
theorem ekSent_loop_le_exit {b : BitVec 64} {A : RustAlloc}
    {H : String → Option (State → State)}
    (hFromCall : subroutine_ok (libsignalSessionCode.rebase b H)
      ((libsignalSessionCode.rebase b H).fnAddr unchunkedEkSentCt1ReceivedMergeName + 0xffffffffffff91a0#64)
      (decodeErrorFromSpec A))
    {x : UnchunkedEkSentCt1ReceivedMergeGhost} {R : SepProp} {s0 s : State}
    {m : V1State.Unchunked.EkSentCt1Received} {cur : List (BitVec 8)} {limit : Nat}
    (hle_lim : cur.length ≤ limit)
    (hsp_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hcur_le : cur.length ≤ x.bs.length)
    (hcur_suf : IsDropSuffix x.bs cur)
    (hlim_lt : limit < 2 ^ 63)
    (hres_cur : (Proto.mergeMessage V1State.Unchunked.EkSentCt1Received.mergeField (codecWireTypeToProto x.wt) x.msg x.bs 98).toOption =
      (mergeLoopBin V1State.Unchunked.EkSentCt1Received.mergeField (cur.length - limit) m cur limit 97).map
        (fun m' => (m', x.bs.drop (x.bs.length - limit))))
    (hpc : s.pc = (libsignalSessionCode.rebase b H).fnAddr unchunkedEkSentCt1ReceivedMergeName + 152#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = s0.sp - 112#64)
    (htr : s.trace = s0.trace)
    (hx21 : s.readReg64 (Reg.gpr 21#5) = x.slot)
    (hx22 : s.readReg64 (Reg.gpr 22#5) = BitVec.ofNat 64 limit)
    (hcs : HighCalleeSaved24 s0 s) :
    SepWPp (libsignalSessionCode.rebase b H) (s0.readReg64 Reg.lr) s
      (ekSentLoopPre A s0 x.msgPtr x.bufRef x.slot x.ptr m x.bs cur)
      (WppPost (unchunkedEkSentCt1ReceivedMergeOwnSpec A) x R s0)
      (WppPanic R s0) := by
  obtain ⟨hx24, hx25, hx26, hx27, hx28, hvregs⟩ := hcs
  let curPtr : BitVec 64 := x.ptr + BitVec.ofNat 64 (x.bs.length - cur.length)
  by_cases heq_lim : cur.length = limit
  · obtain ⟨hcmp1, hcmp2, hcmp3⟩ := cmp_len_limit_of_eq heq_lim
    have hcur_eq_drop : x.bs.drop (x.bs.length - limit) = cur := by
      rw [← heq_lim]; exact hcur_suf.symm
    have hsome : (Proto.mergeMessage V1State.Unchunked.EkSentCt1Received.mergeField (codecWireTypeToProto x.wt) x.msg x.bs 98).toOption =
        some (m, cur) := by
      rw [hres_cur, mergeLoopBin_eq_limit _ _ _ _ _ _ heq_lim, Option.map_some, hcur_eq_drop]
    ekSentMerge_fetches b H 152 12
    ekSentMerge_fetches b H 408 12
    ekSentMerge_fetches b H 120 28
    generalize_entry (libsignalSessionCode.rebase b H).fnAddr unchunkedEkSentCt1ReceivedMergeName = entry
    examples_hide_fetches
    apply SepWPp.of_sepWP_ret
    unfold WppPost unchunkedEkSentCt1ReceivedMergeOwnSpec
    simp only [hsome, stackAt_unchunkedMerge s0.sp, ekSentLoopPre,
      sliceCursorAfter_eq_split hcur_le hcur_suf, sliceCursorAt,
      sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc, arm64_norm, htr, hsp]
    wp_steps
    wp_done
  · have hlt_lim : cur.length < limit := Nat.lt_of_le_of_ne hle_lim heq_lim
    obtain ⟨hcmp1, hcmp2, hcmp3⟩ := cmp_len_limit_of_lt hlt_lim hlim_lt
    have hnone : (Proto.mergeMessage V1State.Unchunked.EkSentCt1Received.mergeField (codecWireTypeToProto x.wt) x.msg x.bs 98).toOption = none := by
      rw [hres_cur, mergeLoopBin_lt_limit _ _ _ _ _ _ hlt_lim, Option.map_none]
    have hfrom_exit := @ekSent_from_err_exit b A H hFromCall x R s0
    ekSentMerge_fetches b H 152 12
    ekSentMerge_fetches b H 408 4
    ekSentMerge_fetches b H 468 16
    ekSentMerge_fetches b H 76 8
    generalize_entry (libsignalSessionCode.rebase b H).fnAddr unchunkedEkSentCt1ReceivedMergeName = entry
    examples_hide_fetches
    apply SepWPp.of_sepWP (mid := entry + 108#64)
    conv => arg 4; rw [ekSentLoopPre, sliceCursorAfter_eq_split hcur_le hcur_suf,
      sliceCursorAt, memRegion_48_split_112 s0.sp]
    simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
    apply SepWP.exists_elim; intro v_stk0
    wp_steps
    apply SepWP.fold (pointsTo64_pair_entails_memRegion16 x.slot curPtr (BitVec.ofNat 64 cur.length)) (by sep_focus)
    apply SepWP.fold (pointsToBytes_prefix_join hcur_le hcur_suf) (by sep_focus)
    apply SepWP.fold (protoUnchunkedEkSentCt1ReceivedCapAt_entails_exists A x.msgPtr cur.length m) (by sep_focus)
    wp_reach
    apply SepWPp.weaken_pre (P' :=
      ((s0.sp - 112#64) ↦₆₄ 0x8000000000000008#64) ∗
        memRegion (s0.sp - 104#64) 40 ∗
        unchunkedMergeBelow s0.sp ∗
        ekSentErrFrame A s0 x.msgPtr x.bufRef x.slot x.ptr x.bs)
      (by dsimp only [ekSentErrFrame]; sep_entail)
    exact hfrom_exit hnone (by decide : KindNoHeap 0x8000000000000008#64) hsp_align
      (by simp only [arm64_norm]) (by simp only [arm64_norm, hrun])
      (by simp only [arm64_norm, hsp]) (by simp only [arm64_norm, htr])
      ⟨by simp only [arm64_norm, hx24], by simp only [arm64_norm, hx25],
       by simp only [arm64_norm, hx26], by simp only [arm64_norm, hx27],
       by simp only [arm64_norm, hx28], by simp only [arm64_norm, hvregs]⟩

/-- Key-decoding step at `+0x098` (`entry + 152#64`) when `¬ cur.length ≤ limit`:
calls `decode_varint [local#2]` at `+0x0a8`, checks key bounds/wire-type/tag at `+0x0ac..+0x0c8`,
exits on invalid key, or reaches `+0x0cc` (`entry + 204#64`) with `X0 = iwt.toNat` and `X1 = tag`. -/
theorem ekSent_decode_key_step {img : Obj.Image} {b : BitVec 64} {A : RustAlloc}
    {H : String → Option (State → State)}
    (hFromCall : subroutine_ok (libsignalSessionCode.rebase b H)
      ((libsignalSessionCode.rebase b H).fnAddr unchunkedEkSentCt1ReceivedMergeName + 0xffffffffffff91a0#64)
      (decodeErrorFromSpec A))
    (hVarintCall : subroutine_ok (libsignalSessionCode.rebase b H)
      ((libsignalSessionCode.rebase b H).fnAddr unchunkedEkSentCt1ReceivedMergeName + 0xffffffffffffb8cc#64)
      (decodeVarint2Spec A))
    {x : UnchunkedEkSentCt1ReceivedMergeGhost} {R : SepProp} {s0 s : State}
    {m : V1State.Unchunked.EkSentCt1Received} {cur : List (BitVec 8)} {limit : Nat}
    (hgt_lim : ¬ cur.length ≤ limit)
    (hsp_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hcur_le : cur.length ≤ x.bs.length)
    (hcur_lt : cur.length < 2 ^ 63)
    (hcur_suf : IsDropSuffix x.bs cur)
    (hres_cur : (Proto.mergeMessage V1State.Unchunked.EkSentCt1Received.mergeField (codecWireTypeToProto x.wt) x.msg x.bs 98).toOption =
      (mergeLoopBin V1State.Unchunked.EkSentCt1Received.mergeField (cur.length - limit) m cur limit 97).map
        (fun m' => (m', x.bs.drop (x.bs.length - limit))))
    (hcont : ∀ (key : BitVec 64) (iwt : WireType) (rest : List (BitVec 8)) (s' : State),
      decodeVarint cur = some (key, rest) →
      ¬ 2 ^ 32 ≤ key.toNat →
      WireType.ofNat? (key.toNat % 8) = some iwt →
      ¬ key.toNat / 8 < 1 →
      s'.pc = (libsignalSessionCode.rebase b H).fnAddr unchunkedEkSentCt1ReceivedMergeName + 204#64 →
      s'.status = .Running →
      s'.sp = s0.sp - 112#64 →
      s'.trace = s0.trace →
      s'.readReg64 (Reg.gpr 0#5) = BitVec.ofNat 64 iwt.toNat →
      s'.readReg64 (Reg.gpr 1#5) = BitVec.ofNat 64 (key.toNat / 8) →
      s'.readReg64 (Reg.gpr 19#5) = x.bufRef →
      s'.readReg64 (Reg.gpr 20#5) = x.msgPtr →
      s'.readReg64 (Reg.gpr 21#5) = x.slot →
      s'.readReg64 (Reg.gpr 22#5) = BitVec.ofNat 64 limit →
      s'.readReg64 (Reg.gpr 23#5) = 1#64 →
      HighCalleeSaved24 s0 s' →
      ImgCallInv img s' →
      SepWPp (libsignalSessionCode.rebase b H) (s0.readReg64 Reg.lr) s'
        (ekSentLoopPre A s0 x.msgPtr x.bufRef x.slot x.ptr m x.bs rest)
        (WppPost (unchunkedEkSentCt1ReceivedMergeOwnSpec A) x R s0)
        (WppPanic R s0))
    (hpc : s.pc = (libsignalSessionCode.rebase b H).fnAddr unchunkedEkSentCt1ReceivedMergeName + 152#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = s0.sp - 112#64)
    (htr : s.trace = s0.trace)
    (hx19 : s.readReg64 (Reg.gpr 19#5) = x.bufRef)
    (hx20 : s.readReg64 (Reg.gpr 20#5) = x.msgPtr)
    (hx21 : s.readReg64 (Reg.gpr 21#5) = x.slot)
    (hx22 : s.readReg64 (Reg.gpr 22#5) = BitVec.ofNat 64 limit)
    (hx23 : s.readReg64 (Reg.gpr 23#5) = 1#64)
    (hcs : HighCalleeSaved24 s0 s) (hinv : ImgCallInv img s) :
    SepWPp (libsignalSessionCode.rebase b H) (s0.readReg64 Reg.lr) s
      (ekSentLoopPre A s0 x.msgPtr x.bufRef x.slot x.ptr m x.bs cur)
      (WppPost (unchunkedEkSentCt1ReceivedMergeOwnSpec A) x R s0)
      (WppPanic R s0) := by
  obtain ⟨hx24, hx25, hx26, hx27, hx28, hvregs⟩ := hcs
  obtain ⟨hcmp1, hcmp2⟩ := cmp_len_limit_of_gt hgt_lim hcur_lt
  let curPtr : BitVec 64 := x.ptr + BitVec.ofNat 64 (x.bs.length - cur.length)
  have herr0_exit := @ekSent_err0_ret_exit b A H x R s0
  have hfrom_exit := @ekSent_from_err_exit b A H hFromCall x R s0
  ekSentMerge_fetches b H 152 52
  ekSentMerge_fetches b H 420 48
  ekSentMerge_fetches b H 76 8
  generalize_entry (libsignalSessionCode.rebase b H).fnAddr unchunkedEkSentCt1ReceivedMergeName = entry
  examples_hide_fetches
  refine SepWPp.of_sepWP_img (mid := entry + 0xffffffffffffb8cc#64) hinv ?_
  conv => arg 4; rw [ekSentLoopPre, sliceCursorAfter_eq_split hcur_le hcur_suf,
    sliceCursorAt, unchunkedMergeBelow_leaf s0.sp]
  simp only [sepConj_assoc]
  wp_steps
  wp_reach; intro hinv_c
  refine SepWPp.call_frame_keep (hinv := hinv_c) (x := ⟨x.bufRef, x.slot, curPtr, cur⟩)
    (ret_pc := entry + 172#64) hVarintCall
    (by simp only [arm64_norm]) (by simp only [arm64_norm, hrun])
    (by simp only [State.spAligned, hsp, arm64_norm]; exact hsp_align)
    (by simp only [arm64_norm])
    (by dsimp only [decodeVarint2Spec]; simp only [arm64_norm, hsp, hx19]; rfl)
    hcur_lt (by dsimp only [sliceCursorAt, curPtr]; sep_focus)
    (fun _ _ _ _ hex => allowPanic_not_exited hex)
    (fun sf _ hpan => allowPanic_frame' (by simp only [arm64_norm, htr]) hpan)
    ?_
  intro sm hpcm hrunm hspm hcsm hinv_m
  simp only [CalleeSavedPreserved] at hcsm
  obtain ⟨hx19_m, hx20_m, hx21_m, hx22_m, hx23_m, hx24_m, hx25_m, hx26_m, hx27_m, hx28_m, hfp_m, hvregs_m⟩ := hcsm
  simp (config := { decide := true }) only [arm64_norm, hsp, hx19, hx20, hx21, hx22, hx23, hx24, hx25, hx26, hx27, hx28, hvregs] at hpcm hrunm hspm hx19_m hx20_m hx21_m hx22_m hx23_m hx24_m hx25_m hx26_m hx27_m hx28_m hfp_m hvregs_m hvregs_m
  cases hd : decodeVarint cur with
  | none =>
    have hnone : (Proto.mergeMessage V1State.Unchunked.EkSentCt1Received.mergeField (codecWireTypeToProto x.wt) x.msg x.bs 98).toOption = none := by
      rw [hres_cur, mergeLoopBin_of_decodeVarint_none protoPrefixStep_unchunked_ekSentCt1Received_mergeField hgt_lim hd, Option.map_none]
    apply SepWPp.of_sepWP (mid := entry + 120#64)
    conv => arg 4; simp only [decodeVarint2Spec, hd, sepConj_assoc, arm64_norm, hsp]
    apply SepWP.pure_elim; rintro ⟨htrm, hsm0, hsm1⟩
    apply SepWP.fold (unchunkedMergeBelow_leaf_entails s0.sp) (by sep_focus)
    apply SepWP.fold (pointsToBytes_prefix_join hcur_le hcur_suf) (by sep_focus)
    apply SepWP.fold (protoUnchunkedEkSentCt1ReceivedCapAt_entails_exists A x.msgPtr cur.length m) (by sep_focus)
    wp_steps
    wp_reach
    apply SepWPp.weaken_pre (P' :=
      decodeErrorAtStackLen A (sm.readReg64 (Reg.gpr 1#5)) 0 ∗
        memRegion (s0.sp - 112#64) 48 ∗
        unchunkedMergeBelow s0.sp ∗
        ekSentErrFrame A s0 x.msgPtr x.bufRef x.slot x.ptr x.bs)
      (by dsimp only [ekSentErrFrame]; sep_entail)
    exact herr0_exit hnone hsp_align
      (by simp only [arm64_norm]) (by simp only [arm64_norm, hrunm])
      (by simp only [arm64_norm, hspm]) (by simp only [arm64_norm, htrm, htr])
      (by simp only [arm64_norm]) hsm1
      ⟨by simp only [arm64_norm, hx24_m], by simp only [arm64_norm, hx25_m],
       by simp only [arm64_norm, hx26_m], by simp only [arm64_norm, hx27_m],
       by simp only [arm64_norm, hx28_m], by simp only [arm64_norm, hvregs_m]⟩
  | some p =>
    rcases p with ⟨key, rest⟩
    have hrest_lt_cur : rest.length < cur.length := decodeVarint_length hd
    have hrest_le_cur : rest.length ≤ cur.length := Nat.le_of_lt hrest_lt_cur
    have hrest_le : rest.length ≤ x.bs.length := Nat.le_trans hrest_le_cur hcur_le
    have hrest_suf : IsDropSuffix x.bs rest :=
      suffix_trans hcur_le hcur_suf hrest_le_cur (decodeVarint_suffix hd)
    let restPtr : BitVec 64 := x.ptr + BitVec.ofNat 64 (x.bs.length - rest.length)
    by_cases hk_ge : 2 ^ 32 ≤ key.toNat
    · have hnone : (Proto.mergeMessage V1State.Unchunked.EkSentCt1Received.mergeField (codecWireTypeToProto x.wt) x.msg x.bs 98).toOption = none := by
        rw [hres_cur, mergeLoopBin_of_key_ge protoPrefixStep_unchunked_ekSentCt1Received_mergeField hgt_lim hd hk_ge, Option.map_none]
      have hshr := key_shr32_of_ge hk_ge
      apply SepWPp.of_sepWP (mid := entry + 108#64)
      conv => arg 4; simp only [decodeVarint2Spec, hd, sepConj_assoc, arm64_norm, hsp]
      apply SepWP.pure_elim; rintro ⟨htrm, hsm0, hsm1⟩
      apply SepWP.fold (unchunkedMergeBelow_leaf_entails s0.sp) (by sep_focus)
      apply SepWP.fold (sliceCursorAfter_join hcur_le hcur_suf hrest_le_cur) (by sep_focus)
      conv => arg 4; rw [sliceCursorAfter_eq_split hrest_le hrest_suf, sliceCursorAt, memRegion_48_split2_112 s0.sp]
      simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
      apply SepWP.exists_elim; intro v_err0
      apply SepWP.exists_elim; intro v_err1
      wp_steps
      apply SepWP.fold (protoUnchunkedEkSentCt1ReceivedCapAt_entails_exists A x.msgPtr cur.length m) (by sep_focus)
      apply SepWP.fold (pointsTo64_pair_entails_memRegion16 x.slot restPtr (BitVec.ofNat 64 rest.length)) (by sep_focus)
      apply SepWP.fold (pointsToBytes_prefix_join hrest_le hrest_suf) (by sep_focus)
      apply SepWP.fold (pointsTo64_memRegion32_entails_40_112 s0.sp key) (by sep_focus)
      wp_reach
      apply SepWPp.weaken_pre (P' :=
        ((s0.sp - 112#64) ↦₆₄ 0x8000000000000004#64) ∗
          memRegion (s0.sp - 104#64) 40 ∗
          unchunkedMergeBelow s0.sp ∗
          ekSentErrFrame A s0 x.msgPtr x.bufRef x.slot x.ptr x.bs)
        (by dsimp only [ekSentErrFrame]; sep_entail)
      exact hfrom_exit hnone (by decide : KindNoHeap 0x8000000000000004#64) hsp_align
        (by simp only [arm64_norm]) (by simp only [arm64_norm, hrunm])
        (by simp only [arm64_norm, hspm]) (by simp only [arm64_norm, htrm, htr])
        ⟨by simp only [arm64_norm, hx24_m], by simp only [arm64_norm, hx25_m],
         by simp only [arm64_norm, hx26_m], by simp only [arm64_norm, hx27_m],
         by simp only [arm64_norm, hx28_m], by simp only [arm64_norm, hvregs_m]⟩
    · have hshr := key_shr32_of_lt hk_ge
      cases hwt : WireType.ofNat? (key.toNat % 8) with
      | none =>
        have hnone : (Proto.mergeMessage V1State.Unchunked.EkSentCt1Received.mergeField (codecWireTypeToProto x.wt) x.msg x.bs 98).toOption = none := by
          rw [hres_cur, mergeLoopBin_of_wt_none protoPrefixStep_unchunked_ekSentCt1Received_mergeField hgt_lim hd hk_ge hwt, Option.map_none]
        obtain ⟨hcs1, hcs2⟩ := key_wt_none hwt
        apply SepWPp.of_sepWP (mid := entry + 108#64)
        conv => arg 4; simp only [decodeVarint2Spec, hd, sepConj_assoc, arm64_norm, hsp]
        apply SepWP.pure_elim; rintro ⟨htrm, hsm0, hsm1⟩
        apply SepWP.fold (unchunkedMergeBelow_leaf_entails s0.sp) (by sep_focus)
        apply SepWP.fold (sliceCursorAfter_join hcur_le hcur_suf hrest_le_cur) (by sep_focus)
        conv => arg 4; rw [sliceCursorAfter_eq_split hrest_le hrest_suf, sliceCursorAt, memRegion_48_split2_112 s0.sp]
        simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
        apply SepWP.exists_elim; intro v_err0
        apply SepWP.exists_elim; intro v_err1
        wp_steps
        apply SepWP.fold (protoUnchunkedEkSentCt1ReceivedCapAt_entails_exists A x.msgPtr cur.length m) (by sep_focus)
        apply SepWP.fold (pointsTo64_pair_entails_memRegion16 x.slot restPtr (BitVec.ofNat 64 rest.length)) (by sep_focus)
        apply SepWP.fold (pointsToBytes_prefix_join hrest_le hrest_suf) (by sep_focus)
        apply SepWP.fold (pointsTo64_memRegion32_entails_40_112 s0.sp (key &&& 7#64)) (by sep_focus)
        wp_reach
        apply SepWPp.weaken_pre (P' :=
          ((s0.sp - 112#64) ↦₆₄ 0x8000000000000003#64) ∗
            memRegion (s0.sp - 104#64) 40 ∗
            unchunkedMergeBelow s0.sp ∗
            ekSentErrFrame A s0 x.msgPtr x.bufRef x.slot x.ptr x.bs)
          (by dsimp only [ekSentErrFrame]; sep_entail)
        exact hfrom_exit hnone (by decide : KindNoHeap 0x8000000000000003#64) hsp_align
          (by simp only [arm64_norm]) (by simp only [arm64_norm, hrunm])
          (by simp only [arm64_norm, hspm]) (by simp only [arm64_norm, htrm, htr])
          ⟨by simp only [arm64_norm, hx24_m], by simp only [arm64_norm, hx25_m],
           by simp only [arm64_norm, hx26_m], by simp only [arm64_norm, hx27_m],
           by simp only [arm64_norm, hx28_m], by simp only [arm64_norm, hvregs_m]⟩
      | some iwt =>
        obtain ⟨hcc1, hcc2, hand_wt, hcc1_wt, hcc2_wt⟩ := key_wt_some hwt
        obtain ⟨hw1, hw1_2⟩ := w1_tag_eq hk_ge
        obtain ⟨hw1_zext1, hw1_zext2⟩ := bv32_zeroExtend_ofNat (n := key.toNat / 8) (by omega)
        by_cases hitag0 : key.toNat / 8 < 1
        · have hnone : (Proto.mergeMessage V1State.Unchunked.EkSentCt1Received.mergeField (codecWireTypeToProto x.wt) x.msg x.bs 98).toOption = none := by
            rw [hres_cur, mergeLoopBin_of_tag_zero protoPrefixStep_unchunked_ekSentCt1Received_mergeField hgt_lim hd hk_ge hwt hitag0, Option.map_none]
          have htag_zero : key.toNat / 8 = 0 := by omega
          apply SepWPp.of_sepWP (mid := entry + 108#64)
          conv => arg 4; simp only [decodeVarint2Spec, hd, sepConj_assoc, arm64_norm, hsp]
          apply SepWP.pure_elim; rintro ⟨htrm, hsm0, hsm1⟩
          apply SepWP.fold (unchunkedMergeBelow_leaf_entails s0.sp) (by sep_focus)
          apply SepWP.fold (sliceCursorAfter_join hcur_le hcur_suf hrest_le_cur) (by sep_focus)
          conv => arg 4; rw [sliceCursorAfter_eq_split hrest_le hrest_suf, sliceCursorAt, memRegion_48_split_112 s0.sp]
          simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
          apply SepWP.exists_elim; intro v_err0
          wp_steps
          apply SepWP.fold (protoUnchunkedEkSentCt1ReceivedCapAt_entails_exists A x.msgPtr cur.length m) (by sep_focus)
          apply SepWP.fold (pointsTo64_pair_entails_memRegion16 x.slot restPtr (BitVec.ofNat 64 rest.length)) (by sep_focus)
          apply SepWP.fold (pointsToBytes_prefix_join hrest_le hrest_suf) (by sep_focus)
          wp_reach
          apply SepWPp.weaken_pre (P' :=
            ((s0.sp - 112#64) ↦₆₄ 0x8000000000000005#64) ∗
              memRegion (s0.sp - 104#64) 40 ∗
              unchunkedMergeBelow s0.sp ∗
              ekSentErrFrame A s0 x.msgPtr x.bufRef x.slot x.ptr x.bs)
            (by dsimp only [ekSentErrFrame]; sep_entail)
          exact hfrom_exit hnone (by decide : KindNoHeap 0x8000000000000005#64) hsp_align
            (by simp only [arm64_norm]) (by simp only [arm64_norm, hrunm])
            (by simp only [arm64_norm, hspm]) (by simp only [arm64_norm, htrm, htr])
            ⟨by simp only [arm64_norm, hx24_m], by simp only [arm64_norm, hx25_m],
             by simp only [arm64_norm, hx26_m], by simp only [arm64_norm, hx27_m],
             by simp only [arm64_norm, hx28_m], by simp only [arm64_norm, hvregs_m]⟩
        · obtain ⟨hcbz_tag1, hcbz_tag2⟩ := tag_cbz_false hk_ge hitag0
          have hcbz_tag64 : (BitVec.ofNat 64 (key.toNat / 8) == 0#64) = false := by
            rw [beq_eq_false_iff_ne]; intro h
            have h1 := congrArg BitVec.toNat h
            simp only [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega : key.toNat / 8 < 2 ^ 64)] at h1
            omega
          refine SepWPp.of_sepWP_img (mid := entry + 204#64) hinv_m ?_
          conv => arg 4; simp only [decodeVarint2Spec, hd, sepConj_assoc, arm64_norm, hsp]
          apply SepWP.pure_elim; rintro ⟨htrm, hsm0, hsm1⟩
          apply SepWP.fold (unchunkedMergeBelow_leaf_entails s0.sp) (by sep_focus)
          apply SepWP.fold (sliceCursorAfter_join hcur_le hcur_suf hrest_le_cur) (by sep_focus)
          apply SepWP.fold (protoUnchunkedEkSentCt1ReceivedCapAt_mono A x.msgPtr m hrest_le_cur) (by sep_focus)
          wp_steps
          wp_reach; intro hinv_n
          apply SepWPp.weaken_pre (P' := ekSentLoopPre A s0 x.msgPtr x.bufRef x.slot x.ptr m x.bs rest)
            (by dsimp only [ekSentLoopPre]; sep_entail)
          exact hcont key iwt rest _ hd hk_ge hwt hitag0
            (by simp only [arm64_norm]) (by simp only [arm64_norm, hrunm])
            (by simp only [arm64_norm, hspm]) (by simp only [arm64_norm, htrm, htr])
            (by simp only [arm64_norm, hsm1, hand_wt]) (by simp only [arm64_norm, hsm1, hw1, hw1_2, hw1_zext1, hw1_zext2])
            (by simp only [arm64_norm, hx19_m]) (by simp only [arm64_norm, hx20_m])
            (by simp only [arm64_norm, hx21_m]) (by simp only [arm64_norm, hx22_m])
            (by simp only [arm64_norm, hx23_m])
            ⟨by simp only [arm64_norm, hx24_m], by simp only [arm64_norm, hx25_m],
             by simp only [arm64_norm, hx26_m], by simp only [arm64_norm, hx27_m],
             by simp only [arm64_norm, hx28_m], by simp only [arm64_norm, hvregs_m]⟩ hinv_n

/-- Main loop induction for `EkSentCt1Received::merge` (`0x51c00`) at `+0x098` (`entry + 152#64`). -/
theorem ekSent_loop_ok {img : Obj.Image} {b : BitVec 64} {A : RustAlloc} {H : String → Option (State → State)}
    (hFromCall : subroutine_ok (libsignalSessionCode.rebase b H)
      ((libsignalSessionCode.rebase b H).fnAddr unchunkedEkSentCt1ReceivedMergeName + 0xffffffffffff91a0#64)
      (decodeErrorFromSpec A))
    (hPushCall : subroutine_ok (libsignalSessionCode.rebase b H)
      ((libsignalSessionCode.rebase b H).fnAddr unchunkedEkSentCt1ReceivedMergeName + 0xffffffffffff8ea8#64)
      (decodeErrorPushSpec A))
    (hVarintCall : subroutine_ok (libsignalSessionCode.rebase b H)
      ((libsignalSessionCode.rebase b H).fnAddr unchunkedEkSentCt1ReceivedMergeName + 0xffffffffffffb8cc#64)
      (decodeVarint2Spec A))
    (hSkipCall : subroutine_ok (libsignalSessionCode.rebase b H)
      ((libsignalSessionCode.rebase b H).fnAddr unchunkedEkSentCt1ReceivedMergeName + 0xffffffffffff9f74#64)
      (skipField3Spec A))
    (hBytesCall : subroutine_ok (libsignalSessionCode.rebase b H)
      ((libsignalSessionCode.rebase b H).fnAddr unchunkedEkSentCt1ReceivedMergeName + 0xffffffffffffb53c#64)
      ((bytesMerge3RawSpec A).inImage img))
    (hAuthCall : subroutine_ok (libsignalSessionCode.rebase b H)
      ((libsignalSessionCode.rebase b H).fnAddr unchunkedEkSentCt1ReceivedMergeName + 0xffffffffffffc338#64)
      ((authMergeSpec A).inImage img))
    {x : UnchunkedEkSentCt1ReceivedMergeGhost} {R : SepProp} {s0 : State} {limit : Nat}
    (hsp_align : (s0.sp &&& 15#64 == 0#64) = true) (hbs_lt : x.bs.length < 2 ^ 63) (hlim_lt : limit < 2 ^ 63) :
    ∀ (n : Nat) (m : V1State.Unchunked.EkSentCt1Received) (cur : List (BitVec 8)) (s : State),
      cur.length ≤ n → cur.length ≤ x.bs.length → IsDropSuffix x.bs cur →
      (Proto.mergeMessage V1State.Unchunked.EkSentCt1Received.mergeField (codecWireTypeToProto x.wt) x.msg x.bs 98).toOption =
        (mergeLoopBin V1State.Unchunked.EkSentCt1Received.mergeField (cur.length - limit) m cur limit 97).map
          (fun m' => (m', x.bs.drop (x.bs.length - limit))) →
      s.pc = (libsignalSessionCode.rebase b H).fnAddr unchunkedEkSentCt1ReceivedMergeName + 152#64 →
      s.status = .Running → s.sp = s0.sp - 112#64 → s.trace = s0.trace →
      s.readReg64 (Reg.gpr 19#5) = x.bufRef → s.readReg64 (Reg.gpr 20#5) = x.msgPtr →
      s.readReg64 (Reg.gpr 21#5) = x.slot → s.readReg64 (Reg.gpr 22#5) = BitVec.ofNat 64 limit →
      s.readReg64 (Reg.gpr 23#5) = 1#64 →
      HighCalleeSaved24 s0 s →
      ImgCallInv img s →
      SepWPp (libsignalSessionCode.rebase b H) (s0.readReg64 Reg.lr) s
        (ekSentLoopPre A s0 x.msgPtr x.bufRef x.slot x.ptr m x.bs cur)
        (WppPost (unchunkedEkSentCt1ReceivedMergeOwnSpec A) x R s0) (WppPanic R s0) := by
  have htag1_varint := fun {s m rest} => @ekSent_tag1_varint_step b A img H hPushCall hVarintCall x R s0 s m rest limit
  have htag1_wt_err := @ekSent_tag1_wt_err_step b A H hFromCall hPushCall x R s0
  have htag2_step := fun {s m rest iwt} => @ekSent_tag2_step b A img H hPushCall hAuthCall x R s0 s m rest iwt limit
  have htag3_step := fun {s m rest iwt} => @ekSent_tag3_step b A img H hPushCall hBytesCall x R s0 s m rest iwt limit
  have htag4_step := fun {s m rest iwt} => @ekSent_tag4_step img b A H hPushCall hBytesCall x R s0 s m rest iwt limit
  have hskip_step := fun {s m rest tag iwt} => @ekSent_skip_step b A img H hSkipCall x R s0 s m rest tag iwt limit
  intro n; induction n with
  | zero =>
    intro m cur s hcur_n hcur_le hcur_suf hres_cur hpc hrun hsp htr hx19 hx20 hx21 hx22 hx23 hcs _
    exact ekSent_loop_le_exit hFromCall (by omega) hsp_align hcur_le hcur_suf hlim_lt
      hres_cur hpc hrun hsp htr hx21 hx22 hcs
  | succ n ih =>
    intro m cur s hcur_n hcur_le hcur_suf hres_cur hpc hrun hsp htr hx19 hx20 hx21 hx22 hx23 hcs hinv
    by_cases hle_lim : cur.length ≤ limit
    · exact ekSent_loop_le_exit hFromCall hle_lim hsp_align hcur_le hcur_suf hlim_lt
        hres_cur hpc hrun hsp htr hx21 hx22 hcs
    · have hcur_lt : cur.length < 2 ^ 63 := Nat.lt_of_le_of_lt hcur_le hbs_lt
      refine ekSent_decode_key_step hFromCall hVarintCall hle_lim hsp_align
        hcur_le hcur_lt hcur_suf hres_cur ?_ hpc hrun hsp htr hx19 hx20 hx21 hx22 hx23 hcs hinv
      intro key iwt rest s' hd hk_ge hwt hitag0 hpc' hrun' hsp' htr' hx0' hx1' hx19' hx20' hx21' hx22' hx23' hcs' hinv'
      obtain ⟨hx24', hx25', hx26', hx27', hx28', hvregs'⟩ := hcs'
      have hrest_lt_cur : rest.length < cur.length := decodeVarint_length hd
      have hrest_le_cur : rest.length ≤ cur.length := Nat.le_of_lt hrest_lt_cur
      have hrest_le : rest.length ≤ x.bs.length := Nat.le_trans hrest_le_cur hcur_le
      have hrest_lt : rest.length < 2 ^ 63 := Nat.lt_of_le_of_lt hrest_le hbs_lt
      have hrest_suf : IsDropSuffix x.bs rest := suffix_trans hcur_le hcur_suf hrest_le_cur (decodeVarint_suffix hd)
      have hloop_ok := mergeLoopBin_of_key_ok (m := m) (depth' := 97)
        protoPrefixStep_unchunked_ekSentCt1Received_mergeField hle_lim hd hk_ge hwt hitag0
      by_cases htag1 : key.toNat / 8 = 1
      · rw [htag1] at hx1' hloop_ok; rw [unchunkedEkSentCt1Received_mergeField_tag1] at hloop_ok
        ekSentMerge_fetches b H 204 16
        generalize_entry (libsignalSessionCode.rebase b H).fnAddr unchunkedEkSentCt1ReceivedMergeName = entry
        examples_hide_fetches
        refine SepWPp.of_sepWP_img (mid := entry + 340#64) hinv' ?_; wp_steps; wp_reach; intro hinv_t
        by_cases hiwt : iwt = .varint
        · subst hiwt
          have hnone_dv : decodeVarint rest = none →
              (Proto.mergeMessage V1State.Unchunked.EkSentCt1Received.mergeField (codecWireTypeToProto x.wt) x.msg x.bs 98).toOption = none := by
            intro hdv; simp only [hres_cur, hloop_ok, eq_self, ↓reduceIte, hdv, Option.map_none]
          refine htag1_varint hsp_align hrest_le hrest_lt hrest_suf hnone_dv
            (fun v rest' s'' hdv hpc'' hrun'' hsp'' htr'' hx19'' hx20'' hx21'' hx22'' hx23'' hcs'' hinv'' => ?_)
            (by simp only [arm64_norm]) (by simp only [arm64_norm, hrun']) (by simp only [arm64_norm, hsp']) (by simp only [arm64_norm, htr'])
            (by simp only [arm64_norm, hx0']) (by simp only [arm64_norm, hx19']) (by simp only [arm64_norm, hx20'])
            (by simp only [arm64_norm, hx21']) (by simp only [arm64_norm, hx22']) (by simp only [arm64_norm, hx23'])
            ⟨by simp only [arm64_norm, hx24'], by simp only [arm64_norm, hx25'],
             by simp only [arm64_norm, hx26'], by simp only [arm64_norm, hx27'],
             by simp only [arm64_norm, hx28'], by simp only [arm64_norm, hvregs']⟩ hinv_t
          have hrest'_lt : rest'.length < rest.length := decodeVarint_length hdv
          have hrest'_le_rest : rest'.length ≤ rest.length := Nat.le_of_lt hrest'_lt
          have hres_next : (Proto.mergeMessage V1State.Unchunked.EkSentCt1Received.mergeField (codecWireTypeToProto x.wt) x.msg x.bs 98).toOption =
              (mergeLoopBin V1State.Unchunked.EkSentCt1Received.mergeField (rest'.length - limit) { m with epoch := v } rest' limit 97).map
                (fun m' => (m', x.bs.drop (x.bs.length - limit))) := by
            simp only [hres_cur, hloop_ok, eq_self, ↓reduceIte, hdv, Option.map_some]
          exact ih { m with epoch := v } rest' s'' (by omega) (by omega)
            (suffix_trans hrest_le hrest_suf hrest'_le_rest (decodeVarint_suffix hdv))
            hres_next hpc'' hrun'' hsp'' htr'' hx19'' hx20'' hx21'' hx22'' hx23'' hcs'' hinv''
        · have hnone_wt : (Proto.mergeMessage V1State.Unchunked.EkSentCt1Received.mergeField (codecWireTypeToProto x.wt) x.msg x.bs 98).toOption = none := by
            simp only [hres_cur, hloop_ok, hiwt, ↓reduceIte, Option.map_none]
          exact htag1_wt_err hiwt hsp_align hrest_le hrest_suf hnone_wt
            (by simp only [arm64_norm]) (by simp only [arm64_norm, hrun']) (by simp only [arm64_norm, hsp']) (by simp only [arm64_norm, htr'])
            (by simp only [arm64_norm, hx0'])
            ⟨by simp only [arm64_norm, hx24'], by simp only [arm64_norm, hx25'],
             by simp only [arm64_norm, hx26'], by simp only [arm64_norm, hx27'],
             by simp only [arm64_norm, hx28'], by simp only [arm64_norm, hvregs']⟩
      · by_cases htag2 : key.toNat / 8 = 2
        · rw [htag2] at hx1' hloop_ok; rw [unchunkedEkSentCt1Received_mergeField_tag2] at hloop_ok
          ekSentMerge_fetches b H 204 24
          generalize_entry (libsignalSessionCode.rebase b H).fnAddr unchunkedEkSentCt1ReceivedMergeName = entry
          examples_hide_fetches
          refine SepWPp.of_sepWP_img (mid := entry + 228#64) hinv' ?_; wp_steps; wp_reach; intro hinv_t
          have hnone_am : (Proto.mergeMessage ProtoAuthenticator.mergeField (codecWireTypeToProto iwt) (m.auth.getD default) rest 97).toOption = none →
              (Proto.mergeMessage V1State.Unchunked.EkSentCt1Received.mergeField (codecWireTypeToProto x.wt) x.msg x.bs 98).toOption = none := by
            intro ham; simp only [hres_cur, hloop_ok, ham, Option.map_none]
          refine htag2_step hsp_align hrest_le hrest_lt hrest_suf hnone_am
            (fun v rest' s'' ham hpc'' hrun'' hsp'' htr'' hx19'' hx20'' hx21'' hx22'' hx23'' hcs'' hinv'' => ?_)
            (by simp only [arm64_norm]) (by simp only [arm64_norm, hrun']) (by simp only [arm64_norm, hsp']) (by simp only [arm64_norm, htr'])
            (by simp only [arm64_norm, hx0']) (by simp only [arm64_norm, hx19']) (by simp only [arm64_norm, hx20'])
            (by simp only [arm64_norm, hx21']) (by simp only [arm64_norm, hx22']) (by simp only [arm64_norm, hx23'])
            ⟨by simp only [arm64_norm, hx24'], by simp only [arm64_norm, hx25'],
             by simp only [arm64_norm, hx26'], by simp only [arm64_norm, hx27'],
             by simp only [arm64_norm, hx28'], by simp only [arm64_norm, hvregs']⟩ hinv_t
          have ⟨hrest'_le_rest, hrest'_suf⟩ := proto_mergeMessage_suffix ham
          have hres_next : (Proto.mergeMessage V1State.Unchunked.EkSentCt1Received.mergeField (codecWireTypeToProto x.wt) x.msg x.bs 98).toOption =
              (mergeLoopBin V1State.Unchunked.EkSentCt1Received.mergeField (rest'.length - limit) { m with auth := some v } rest' limit 97).map
                (fun m' => (m', x.bs.drop (x.bs.length - limit))) := by
            simp only [hres_cur, hloop_ok, ham, Option.map_some]
          exact ih { m with auth := some v } rest' s'' (by omega) (by omega)
            (suffix_trans hrest_le hrest_suf hrest'_le_rest hrest'_suf)
            hres_next hpc'' hrun'' hsp'' htr'' hx19'' hx20'' hx21'' hx22'' hx23'' hcs'' hinv''
        · by_cases htag3 : key.toNat / 8 = 3
          · rw [htag3] at hx1' hloop_ok; rw [unchunkedEkSentCt1Received_mergeField_tag3] at hloop_ok
            ekSentMerge_fetches b H 204 8
            ekSentMerge_fetches b H 276 8
            generalize_entry (libsignalSessionCode.rebase b H).fnAddr unchunkedEkSentCt1ReceivedMergeName = entry
            examples_hide_fetches
            refine SepWPp.of_sepWP_img (mid := entry + 372#64) hinv' ?_; wp_steps; wp_reach; intro hinv_t
            have hnone_mb : mergeBytes iwt rest = none →
                (Proto.mergeMessage V1State.Unchunked.EkSentCt1Received.mergeField (codecWireTypeToProto x.wt) x.msg x.bs 98).toOption = none := by
              intro hmb; simp only [hres_cur, hloop_ok, hmb, Option.map_none]
            refine htag3_step hsp_align hrest_le hrest_lt hrest_suf hnone_mb
              (fun v rest' s'' hmb hpc'' hrun'' hsp'' htr'' hx19'' hx20'' hx21'' hx22'' hx23'' hcs'' hinv'' => ?_)
              (by simp only [arm64_norm]) (by simp only [arm64_norm, hrun']) (by simp only [arm64_norm, hsp']) (by simp only [arm64_norm, htr'])
              (by simp only [arm64_norm, hx0']) (by simp only [arm64_norm, hx19']) (by simp only [arm64_norm, hx20'])
              (by simp only [arm64_norm, hx21']) (by simp only [arm64_norm, hx22']) (by simp only [arm64_norm, hx23'])
              ⟨by simp only [arm64_norm, hx24'], by simp only [arm64_norm, hx25'],
               by simp only [arm64_norm, hx26'], by simp only [arm64_norm, hx27'],
               by simp only [arm64_norm, hx28'], by simp only [arm64_norm, hvregs']⟩ hinv_t
            have hrest'_le_rest : rest'.length ≤ rest.length := mergeBytes_length hmb
            have hres_next : (Proto.mergeMessage V1State.Unchunked.EkSentCt1Received.mergeField (codecWireTypeToProto x.wt) x.msg x.bs 98).toOption =
                (mergeLoopBin V1State.Unchunked.EkSentCt1Received.mergeField (rest'.length - limit) { m with dk := v } rest' limit 97).map
                  (fun m' => (m', x.bs.drop (x.bs.length - limit))) := by
              simp only [hres_cur, hloop_ok, hmb, Option.map_some]
            exact ih { m with dk := v } rest' s'' (by omega) (by omega)
              (suffix_trans hrest_le hrest_suf hrest'_le_rest (mergeBytes_suffix hmb))
              hres_next hpc'' hrun'' hsp'' htr'' hx19'' hx20'' hx21'' hx22'' hx23'' hcs'' hinv''
          · by_cases htag4 : key.toNat / 8 = 4
            · rw [htag4] at hx1' hloop_ok; rw [unchunkedEkSentCt1Received_mergeField_tag4] at hloop_ok
              ekSentMerge_fetches b H 204 8
              ekSentMerge_fetches b H 276 16
              generalize_entry (libsignalSessionCode.rebase b H).fnAddr unchunkedEkSentCt1ReceivedMergeName = entry
              examples_hide_fetches
              refine SepWPp.of_sepWP_img (mid := entry + 292#64) hinv' ?_; wp_steps; wp_reach; intro hinv_t
              have hnone_mb : mergeBytes iwt rest = none →
                  (Proto.mergeMessage V1State.Unchunked.EkSentCt1Received.mergeField (codecWireTypeToProto x.wt) x.msg x.bs 98).toOption = none := by
                intro hmb; simp only [hres_cur, hloop_ok, hmb, Option.map_none]
              refine htag4_step hsp_align hrest_le hrest_lt hrest_suf hnone_mb
                (fun v rest' s'' hmb hpc'' hrun'' hsp'' htr'' hx19'' hx20'' hx21'' hx22'' hx23'' hcs'' hinv'' => ?_)
                (by simp only [arm64_norm]) (by simp only [arm64_norm, hrun']) (by simp only [arm64_norm, hsp']) (by simp only [arm64_norm, htr'])
                (by simp only [arm64_norm, hx0']) (by simp only [arm64_norm, hx19']) (by simp only [arm64_norm, hx20'])
                (by simp only [arm64_norm, hx21']) (by simp only [arm64_norm, hx22']) (by simp only [arm64_norm, hx23'])
                ⟨by simp only [arm64_norm, hx24'], by simp only [arm64_norm, hx25'],
                 by simp only [arm64_norm, hx26'], by simp only [arm64_norm, hx27'],
                 by simp only [arm64_norm, hx28'], by simp only [arm64_norm, hvregs']⟩ hinv_t
              have hrest'_le_rest : rest'.length ≤ rest.length := mergeBytes_length hmb
              have hres_next : (Proto.mergeMessage V1State.Unchunked.EkSentCt1Received.mergeField (codecWireTypeToProto x.wt) x.msg x.bs 98).toOption =
                  (mergeLoopBin V1State.Unchunked.EkSentCt1Received.mergeField (rest'.length - limit) { m with ct1 := v } rest' limit 97).map
                    (fun m' => (m', x.bs.drop (x.bs.length - limit))) := by
                simp only [hres_cur, hloop_ok, hmb, Option.map_some]
              exact ih { m with ct1 := v } rest' s'' (by omega) (by omega)
                (suffix_trans hrest_le hrest_suf hrest'_le_rest (mergeBytes_suffix hmb))
                hres_next hpc'' hrun'' hsp'' htr'' hx19'' hx20'' hx21'' hx22'' hx23'' hcs'' hinv''
            · have hitag_lt : key.toNat / 8 < 2 ^ 32 := by omega
              have hitag_lt29 : key.toNat / 8 < 2 ^ 29 := by omega
              obtain ⟨hgt2_1, hgt2_2, hgt2_3, hgt2_4⟩ := tag_gt_two_branch (by omega : 2 < key.toNat / 8) hitag_lt29
              obtain ⟨hb3_1, _⟩ := itag_beq_tag_false htag3 hitag_lt (by decide : 3 < 2 ^ 32)
              obtain ⟨hb4_1, _⟩ := itag_beq_tag_false htag4 hitag_lt (by decide : 4 < 2 ^ 32)
              have hb3_2 : (BitVec.truncate 32 (BitVec.ofNat 64 (key.toNat / 8)) == 3#32) = false := by rw [sf_truncate32_ofNat64]; exact hb3_1
              have hb4_2 : (BitVec.truncate 32 (BitVec.ofNat 64 (key.toNat / 8)) == 4#32) = false := by rw [sf_truncate32_ofNat64]; exact hb4_1
              have hb4_bne1 : (BitVec.ofNat 32 (key.toNat / 8) != 4#32) = true := by simp only [bne, hb4_1, Bool.not_false]
              have hb4_bne2 : (BitVec.truncate 32 (BitVec.ofNat 64 (key.toNat / 8)) != 4#32) = true := by simp only [bne, hb4_2, Bool.not_false]
              rw [unchunkedEkSentCt1Received_mergeField_other m iwt rest 97 hitag_lt htag1 htag2 htag3 htag4] at hloop_ok
              ekSentMerge_fetches b H 204 8
              ekSentMerge_fetches b H 276 16
              generalize_entry (libsignalSessionCode.rebase b H).fnAddr unchunkedEkSentCt1ReceivedMergeName = entry
              examples_hide_fetches
              refine SepWPp.of_sepWP_img (mid := entry + 316#64) hinv' ?_; wp_steps; wp_reach; intro hinv_t
              have hnone_sf : skipField (2 * rest.length + 2) 97 (key.toNat / 8) iwt rest = none →
                  (Proto.mergeMessage V1State.Unchunked.EkSentCt1Received.mergeField (codecWireTypeToProto x.wt) x.msg x.bs 98).toOption = none := by
                intro hsf; rw [hres_cur, hloop_ok, hsf]; rfl
              refine hskip_step hsp_align hrest_le hrest_lt hrest_suf hitag_lt hnone_sf
                (fun rest' s'' hsf hpc'' hrun'' hsp'' htr'' hx19'' hx20'' hx21'' hx22'' hx23'' hcs'' hinv'' => ?_)
                (by simp only [arm64_norm]) (by simp only [arm64_norm, hrun']) (by simp only [arm64_norm, hsp']) (by simp only [arm64_norm, htr'])
                (by simp only [arm64_norm, hx0']) (by simp only [arm64_norm, hx1', sf_truncate32_ofNat64])
                (by simp only [arm64_norm, hx19']) (by simp only [arm64_norm, hx20'])
                (by simp only [arm64_norm, hx21']) (by simp only [arm64_norm, hx22']) (by simp only [arm64_norm, hx23'])
                ⟨by simp only [arm64_norm, hx24'], by simp only [arm64_norm, hx25'],
                 by simp only [arm64_norm, hx26'], by simp only [arm64_norm, hx27'],
                 by simp only [arm64_norm, hx28'], by simp only [arm64_norm, hvregs']⟩ hinv_t
              have hrest'_le_rest : rest'.length ≤ rest.length := (skip_length (2 * rest.length + 2)).1 _ _ _ _ _ hsf
              have hres_next : (Proto.mergeMessage V1State.Unchunked.EkSentCt1Received.mergeField (codecWireTypeToProto x.wt) x.msg x.bs 98).toOption =
                  (mergeLoopBin V1State.Unchunked.EkSentCt1Received.mergeField (rest'.length - limit) m rest' limit 97).map
                    (fun m' => (m', x.bs.drop (x.bs.length - limit))) := by
                rw [hres_cur, hloop_ok, hsf]; rfl
              exact ih m rest' s'' (by omega) (by omega)
                (suffix_trans hrest_le hrest_suf hrest'_le_rest ((skip_suffix (2 * rest.length + 2)).1 _ _ _ _ _ hsf))
                hres_next hpc'' hrun'' hsp'' htr'' hx19'' hx20'' hx21'' hx22'' hx23'' hcs'' hinv''

/-! ## 3. Top-Level Subroutine Verification -/

/-- Contract-parameterized verification of `prost::encoding::message::merge::<unchunked::EkSentCt1Received, &mut &[u8]>` (`0x51c00`). -/
theorem unchunkedEkSentCt1ReceivedMerge_ok_of_contracts {img : Obj.Image} {b : BitVec 64} {A : RustAlloc}
    {H : String → Option (State → State)}
    (hFromCall : subroutine_ok (libsignalSessionCode.rebase b H)
      ((libsignalSessionCode.rebase b H).fnAddr unchunkedEkSentCt1ReceivedMergeName + 0xffffffffffff91a0#64)
      (decodeErrorFromSpec A))
    (hPushCall : subroutine_ok (libsignalSessionCode.rebase b H)
      ((libsignalSessionCode.rebase b H).fnAddr unchunkedEkSentCt1ReceivedMergeName + 0xffffffffffff8ea8#64)
      (decodeErrorPushSpec A))
    (hVarintCall : subroutine_ok (libsignalSessionCode.rebase b H)
      ((libsignalSessionCode.rebase b H).fnAddr unchunkedEkSentCt1ReceivedMergeName + 0xffffffffffffb8cc#64)
      (decodeVarint2Spec A))
    (hSkipCall : subroutine_ok (libsignalSessionCode.rebase b H)
      ((libsignalSessionCode.rebase b H).fnAddr unchunkedEkSentCt1ReceivedMergeName + 0xffffffffffff9f74#64)
      (skipField3Spec A))
    (hBytesCall : subroutine_ok (libsignalSessionCode.rebase b H)
      ((libsignalSessionCode.rebase b H).fnAddr unchunkedEkSentCt1ReceivedMergeName + 0xffffffffffffb53c#64)
      ((bytesMerge3RawSpec A).inImage img))
    (hAuthCall : subroutine_ok (libsignalSessionCode.rebase b H)
      ((libsignalSessionCode.rebase b H).fnAddr unchunkedEkSentCt1ReceivedMergeName + 0xffffffffffffc338#64)
      ((authMergeSpec A).inImage img)) :
    subroutine_ok (libsignalSessionCode.rebase b H)
      ((libsignalSessionCode.rebase b H).fnAddr unchunkedEkSentCt1ReceivedMergeName)
      ((unchunkedEkSentCt1ReceivedMergeOwnSpec A).inImage img) := by
  apply subroutine_ok_inImage_of_withImgProp
  unfold withImgProp unchunkedEkSentCt1ReceivedMergeOwnSpec
  wpp_init x s0
  replace hpc : s0.pc = (libsignalSessionCode.rebase b H).fnAddr unchunkedEkSentCt1ReceivedMergeName := hpc
  conv => arg 6; ext sf P_f; simp only [unchunkedEkSentCt1ReceivedMergeOwnSpec, sepConj_assoc, satisfies_pure_sepConj]
  change SepWPp _ _ _ _ (WppPost (unchunkedEkSentCt1ReceivedMergeOwnSpec A) x R s0) (WppPanic R s0)
  apply SepWPp.elim_imgCallInvProp; intro hinv0
  have herr0_exit := @ekSent_err0_ret_exit b A H x R s0
  have hfrom_exit := @ekSent_from_err_exit b A H hFromCall x R s0
  have hloop := fun {limit n m cur s} hlim_lt =>
    @ekSent_loop_ok img b A H hFromCall hPushCall hVarintCall hSkipCall hBytesCall hAuthCall x R s0 limit hsp_align h hlim_lt n m cur s
  ekSentMerge_fetches b H 0 108
  ekSentMerge_fetches b H 148 4
  generalize_entry (libsignalSessionCode.rebase b H).fnAddr unchunkedEkSentCt1ReceivedMergeName = entry
  examples_hide_fetches
  by_cases hwt_ld : x.wt = .lengthDelimited
  · have h_1' : (s0.readReg64 (Reg.gpr 0#5)).setWidth 8 = 2#8 := by rw [h_1, hwt_ld]; rfl
    have hbeq := wt_beq_two_of_lengthDelimited h_1'
    have hbne1 : (BitVec.truncate 32 (s0.readReg64 (Reg.gpr 0#5)) &&& 255#32 != 2#32) = false := by simp only [bne, hbeq, Bool.not_true]
    have hbne2 : (BitVec.truncate 32 (BitVec.zeroExtend 64 (BitVec.truncate 32 (s0.readReg64 (Reg.gpr 0#5))) &&& 255#64) != 2#32) = false := by
      rw [BytesMergeFacts.truncate32_zeroExtend64_and_255_eq, h_1']; decide
    have hbne3 : (BitVec.truncate 32 (BitVec.zeroExtend 64 (BitVec.truncate 32 (s0.readReg64 (Reg.gpr 0#5)) &&& 255#32)) != 2#32) = false := by
      revert h_1'; bv_bits
    refine SepWPp.of_sepWP_img (mid := entry + 0xffffffffffffb8cc#64) hinv0 ?_
    (conv => arg 4; rw [stackAt_unchunkedMerge s0.sp, unchunkedMergeBelow_leaf s0.sp]; simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc])
    apply SepWP.exists_elim; intro v29; apply SepWP.exists_elim; intro v30; apply SepWP.exists_elim; intro v23
    apply SepWP.exists_elim; intro v22; apply SepWP.exists_elim; intro v21; apply SepWP.exists_elim; intro v20; apply SepWP.exists_elim; intro v19
    wp_steps; wp_reach; intro hinv_c
    refine SepWPp.call_frame_keep (hinv := hinv_c) (x := ⟨x.bufRef, x.slot, x.ptr, x.bs⟩)
      (ret_pc := entry + 52#64) hVarintCall (by simp only [arm64_norm]) (by simp only [arm64_norm, hrun])
      (by simp only [State.spAligned, arm64_norm]; exact hsp_align) (by simp only [arm64_norm])
      (by dsimp only [decodeVarint2Spec]; simp only [arm64_norm, h_3]; rfl) h (by sep_focus)
      (fun _ _ _ _ hex => allowPanic_not_exited hex) (fun sf _ hpan => allowPanic_frame' (by simp only [arm64_norm]) hpan) ?_
    intro sm hpcm hrunm hspm hcsm hinv_m; simp only [CalleeSavedPreserved] at hcsm
    obtain ⟨hx19_m, hx20_m, hx21_m, hx22_m, hx23_m, hx24_m, hx25_m, hx26_m, hx27_m, hx28_m, hfp_m, hvregs_m⟩ := hcsm
    simp (config := { decide := true }) only [arm64_norm, h_2, h_3] at hpcm hrunm hspm hx19_m hx20_m hx21_m hx22_m hx23_m hx24_m hx25_m hx26_m hx27_m hx28_m hfp_m hvregs_m
    cases hdv0 : decodeVarint x.bs with
    | none =>
      have hnone : (Proto.mergeMessage V1State.Unchunked.EkSentCt1Received.mergeField (codecWireTypeToProto x.wt) x.msg x.bs 98).toOption = none := by
        rw [hwt_ld, ← mergeMessageBin_eq_proto_mergeMessage protoPrefixStep_unchunked_ekSentCt1Received_mergeField]
        simp [mergeMessageBin, codecWireTypeToProto, proto_decodeVarint_toOption, hdv0]
      apply SepWPp.of_sepWP (mid := entry + 120#64)
      (conv => arg 4; simp only [decodeVarint2Spec, hdv0, sepConj_assoc, arm64_norm]); apply SepWP.pure_elim; rintro ⟨hsm0, htrm, hsm1⟩
      apply SepWP.fold (unchunkedMergeBelow_leaf_entails s0.sp) (by sep_focus)
      apply SepWP.fold (protoUnchunkedEkSentCt1ReceivedCapAt_entails_exists A x.msgPtr x.bs.length x.msg) (by sep_focus)
      wp_steps; wp_reach
      apply SepWPp.weaken_pre (P' := decodeErrorAtStackLen A (sm.readReg64 (Reg.gpr 1#5)) 0 ∗ memRegion (s0.sp - 112#64) 48 ∗ unchunkedMergeBelow s0.sp ∗ ekSentErrFrame A s0 x.msgPtr x.bufRef x.slot x.ptr x.bs) (by dsimp only [ekSentErrFrame]; sep_entail)
      exact herr0_exit hnone hsp_align
        (by simp only [arm64_norm]) (by simp only [arm64_norm, hrunm]) (by simp only [arm64_norm, hspm]) (by simp only [arm64_norm, htrm])
        (by simp only [arm64_norm]) hsm1
        ⟨by simp only [arm64_norm, hx24_m], by simp only [arm64_norm, hx25_m], by simp only [arm64_norm, hx26_m], by simp only [arm64_norm, hx27_m], by simp only [arm64_norm, hx28_m], by simp only [arm64_norm, hvregs_m]⟩
    | some p =>
      rcases p with ⟨len, rest0⟩
      have hrest0_lt_bs : rest0.length < x.bs.length := decodeVarint_length hdv0; have hrest0_le : rest0.length ≤ x.bs.length := Nat.le_of_lt hrest0_lt_bs
      have hrest0_lt : rest0.length < 2 ^ 63 := Nat.lt_of_lt_of_le hrest0_lt_bs (Nat.le_of_lt h)
      have hrest0_suf : IsDropSuffix x.bs rest0 := decodeVarint_suffix hdv0
      let rest0Ptr : BitVec 64 := x.ptr + BitVec.ofNat 64 (x.bs.length - rest0.length)
      by_cases hlt_len : rest0.length < len.toNat
      · have hule := ule_len_of_lt hlt_len hrest0_lt
        have hnone : (Proto.mergeMessage V1State.Unchunked.EkSentCt1Received.mergeField (codecWireTypeToProto x.wt) x.msg x.bs 98).toOption = none := by
          rw [hwt_ld, ← mergeMessageBin_eq_proto_mergeMessage protoPrefixStep_unchunked_ekSentCt1Received_mergeField]
          simp [mergeMessageBin, codecWireTypeToProto, proto_decodeVarint_toOption, hdv0, hlt_len]
        apply SepWPp.of_sepWP (mid := entry + 108#64)
        (conv => arg 4; simp only [decodeVarint2Spec, hdv0, sepConj_assoc, arm64_norm]); apply SepWP.pure_elim; rintro ⟨⟨hsm0, hsm1⟩, htrm⟩
        apply SepWP.fold (unchunkedMergeBelow_leaf_entails s0.sp) (by sep_focus)
        (conv => arg 4; rw [sliceCursorAfter_eq_split hrest0_le hrest0_suf, sliceCursorAt, memRegion_48_split_112 s0.sp]; simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc])
        apply SepWP.exists_elim; intro v_stk0; wp_steps
        apply SepWP.fold (protoUnchunkedEkSentCt1ReceivedCapAt_entails_exists A x.msgPtr x.bs.length x.msg) (by sep_focus)
        apply SepWP.fold (pointsTo64_pair_entails_memRegion16 x.slot rest0Ptr (BitVec.ofNat 64 rest0.length)) (by sep_focus)
        apply SepWP.fold (pointsToBytes_prefix_join hrest0_le hrest0_suf) (by sep_focus); wp_reach
        apply SepWPp.weaken_pre (P' := ((s0.sp - 112#64) ↦₆₄ 0x8000000000000007#64) ∗ memRegion (s0.sp - 104#64) 40 ∗ unchunkedMergeBelow s0.sp ∗ ekSentErrFrame A s0 x.msgPtr x.bufRef x.slot x.ptr x.bs) (by dsimp only [ekSentErrFrame]; sep_entail)
        exact hfrom_exit hnone (by decide : KindNoHeap 0x8000000000000007#64) hsp_align
          (by simp only [arm64_norm]) (by simp only [arm64_norm, hrunm]) (by simp only [arm64_norm, hspm]) (by simp only [arm64_norm, htrm])
          ⟨by simp only [arm64_norm, hx24_m], by simp only [arm64_norm, hx25_m], by simp only [arm64_norm, hx26_m], by simp only [arm64_norm, hx27_m], by simp only [arm64_norm, hx28_m], by simp only [arm64_norm, hvregs_m]⟩
      · have hule := ule_len_of_ge hlt_len hrest0_lt; have hsub := bv_len_sub_limit hlt_len; have hlim_lt : rest0.length - len.toNat < 2 ^ 63 := by omega
        have hdrop_eq : x.bs.drop (x.bs.length - (rest0.length - len.toNat)) = rest0.drop len.toNat := by
          have hsuf := hrest0_suf; unfold IsDropSuffix at hsuf; conv => rhs; rw [hsuf, List.drop_drop]
          exact congrArg (List.drop · x.bs) (by omega)
        have hres0 : (Proto.mergeMessage V1State.Unchunked.EkSentCt1Received.mergeField (codecWireTypeToProto x.wt) x.msg x.bs 98).toOption =
            (mergeLoopBin V1State.Unchunked.EkSentCt1Received.mergeField (rest0.length - (rest0.length - len.toNat)) x.msg rest0 (rest0.length - len.toNat) 97).map
              (fun m' => (m', x.bs.drop (x.bs.length - (rest0.length - len.toNat)))) := by
          rw [hwt_ld, ← mergeMessageBin_eq_proto_mergeMessage protoPrefixStep_unchunked_ekSentCt1Received_mergeField]
          simp only [mergeMessageBin, codecWireTypeToProto, bne_self_eq_false, Bool.false_eq_true, ↓reduceIte, proto_decodeVarint_toOption, hdv0, hlt_len, hdrop_eq]
          rcases mergeLoopBin V1State.Unchunked.EkSentCt1Received.mergeField (rest0.length - (rest0.length - len.toNat)) x.msg rest0 (rest0.length - len.toNat) 97 with _ | m' <;> rfl
        refine SepWPp.of_sepWP_img (mid := entry + 152#64) hinv_m ?_
        (conv => arg 4; simp only [decodeVarint2Spec, hdv0, sepConj_assoc, arm64_norm]); apply SepWP.pure_elim; rintro ⟨⟨hsm0, hsm1⟩, htrm⟩
        apply SepWP.fold (unchunkedMergeBelow_leaf_entails s0.sp) (by sep_focus)
        apply SepWP.fold (protoUnchunkedEkSentCt1ReceivedCapAt_mono A x.msgPtr x.msg hrest0_le) (by sep_focus)
        (conv => arg 4; rw [sliceCursorAfter_eq_split hrest0_le hrest0_suf, sliceCursorAt]; simp only [sepConj_assoc]); wp_steps; wp_reach; intro hinv_l
        apply SepWPp.weaken_pre (P' := ekSentLoopPre A s0 x.msgPtr x.bufRef x.slot x.ptr x.msg x.bs rest0) (by rw [ekSentLoopPre, sliceCursorAfter_eq_split hrest0_le hrest0_suf, sliceCursorAt]; sep_entail)
        exact hloop hlim_lt (Nat.le_refl _) hrest0_le hrest0_suf hres0
          (by simp only [arm64_norm]) (by simp only [arm64_norm, hrunm]) (by simp only [arm64_norm, hspm]) (by simp only [arm64_norm, htrm])
          (by simp only [arm64_norm, hx19_m]) (by simp only [arm64_norm, hx20_m]) (by simp only [arm64_norm])
          (by simp only [arm64_norm, hsm1, hsub]) (by simp only [arm64_norm])
          ⟨by simp only [arm64_norm, hx24_m], by simp only [arm64_norm, hx25_m], by simp only [arm64_norm, hx26_m], by simp only [arm64_norm, hx27_m], by simp only [arm64_norm, hx28_m], by simp only [arm64_norm, hvregs_m]⟩ hinv_l
  · have hbeq := wt_beq_two_of_ne_lengthDelimited h_1 hwt_ld
    have hbne1 : (BitVec.truncate 32 (s0.readReg64 (Reg.gpr 0#5)) &&& 255#32 != 2#32) = true := by simp only [bne, hbeq, Bool.not_false]
    have hbne2 : (BitVec.truncate 32 (BitVec.zeroExtend 64 (BitVec.truncate 32 (s0.readReg64 (Reg.gpr 0#5))) &&& 255#64) != 2#32) = true := by
      rw [BytesMergeFacts.truncate32_zeroExtend64_and_255_eq, h_1]; cases hxwt : x.wt <;> first | exact absurd hxwt hwt_ld | decide
    have hbne3 : (BitVec.truncate 32 (BitVec.zeroExtend 64 (BitVec.truncate 32 (s0.readReg64 (Reg.gpr 0#5)) &&& 255#32)) != 2#32) = true := by
      rw [← hbne1]; congr 2; bv_bits
    have hnone : (Proto.mergeMessage V1State.Unchunked.EkSentCt1Received.mergeField (codecWireTypeToProto x.wt) x.msg x.bs 98).toOption = none := by
      rw [← mergeMessageBin_eq_proto_mergeMessage protoPrefixStep_unchunked_ekSentCt1Received_mergeField]
      cases hxwt : x.wt <;> first | exact absurd hxwt hwt_ld | rfl
    apply SepWPp.of_sepWP (mid := entry + 108#64)
    (conv => arg 4; rw [stackAt_unchunkedMerge s0.sp, sliceCursorAt, memRegion_48_wtErr112 s0.sp]; simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc])
    apply SepWP.exists_elim; intro v29; apply SepWP.exists_elim; intro v30; apply SepWP.exists_elim; intro v23
    apply SepWP.exists_elim; intro v22; apply SepWP.exists_elim; intro v21; apply SepWP.exists_elim; intro v20; apply SepWP.exists_elim; intro v19
    apply SepWP.exists_elim; intro b_wt1; apply SepWP.exists_elim; intro b_wt0; apply SepWP.exists_elim; intro v_wt0; wp_steps
    apply SepWP.fold (wtErr112_entails_memRegion40 s0.sp _ _) (by sep_focus)
    apply SepWP.fold (pointsTo64_pair_entails_memRegion16 x.slot x.ptr (BitVec.ofNat 64 x.bs.length)) (by sep_focus)
    apply SepWP.fold (protoUnchunkedEkSentCt1ReceivedCapAt_entails_exists A x.msgPtr x.bs.length x.msg) (by sep_focus); wp_reach
    apply SepWPp.weaken_pre (P' := ((s0.sp - 112#64) ↦₆₄ 0x8000000000000006#64) ∗ memRegion (s0.sp - 104#64) 40 ∗ unchunkedMergeBelow s0.sp ∗ ekSentErrFrame A s0 x.msgPtr x.bufRef x.slot x.ptr x.bs) (by dsimp only [ekSentErrFrame]; sep_entail)
    exact hfrom_exit hnone (by decide : KindNoHeap 0x8000000000000006#64) hsp_align
      (by simp only [arm64_norm]) (by simp only [arm64_norm, hrun]) (by simp only [arm64_norm]) (by simp only [arm64_norm])
      ⟨by simp only [arm64_norm], by simp only [arm64_norm], by simp only [arm64_norm], by simp only [arm64_norm], by simp only [arm64_norm]⟩

/-- Address-resolved verification of `prost::encoding::message::merge::<unchunked::EkSentCt1Received, &mut &[u8]>` (`0x51c00`). -/
theorem unchunkedEkSentCt1ReceivedMerge_ok_of_fnAddr {img : Obj.Image} {b : BitVec 64} {A : RustAlloc}
    {H : String → Option (State → State)}
    (hFromCall : subroutine_ok (libsignalSessionCode.rebase b H)
      ((libsignalSessionCode.rebase b H).fnAddr decodeErrorFromName) (decodeErrorFromSpec A))
    (hPushCall : subroutine_ok (libsignalSessionCode.rebase b H)
      ((libsignalSessionCode.rebase b H).fnAddr decodeErrorPushName) (decodeErrorPushSpec A))
    (hVarintCall : subroutine_ok (libsignalSessionCode.rebase b H)
      ((libsignalSessionCode.rebase b H).fnAddr Varint.decodeVarint2Name) (decodeVarint2Spec A))
    (hSkipCall : subroutine_ok (libsignalSessionCode.rebase b H)
      ((libsignalSessionCode.rebase b H).fnAddr skipField3Name) (skipField3Spec A))
    (hBytesCall : subroutine_ok (libsignalSessionCode.rebase b H)
      ((libsignalSessionCode.rebase b H).fnAddr bytesMerge3Name) ((bytesMerge3RawSpec A).inImage img))
    (hAuthCall : subroutine_ok (libsignalSessionCode.rebase b H)
      ((libsignalSessionCode.rebase b H).fnAddr authMergeName) ((authMergeSpec A).inImage img)) :
    subroutine_ok (libsignalSessionCode.rebase b H)
      ((libsignalSessionCode.rebase b H).fnAddr unchunkedEkSentCt1ReceivedMergeName)
      ((unchunkedEkSentCt1ReceivedMergeSpec A).inImage img) := by
  apply subroutine_ok_unchunkedEkSentCt1ReceivedMerge_of_own
  refine unchunkedEkSentCt1ReceivedMerge_ok_of_contracts ?_ ?_ ?_ ?_ ?_ ?_
  · rw [fnAddr_offset_eq_H (name := unchunkedEkSentCt1ReceivedMergeName) (callee := decodeErrorFromName)]; exact hFromCall
  · rw [fnAddr_offset_eq_H (name := unchunkedEkSentCt1ReceivedMergeName) (callee := decodeErrorPushName)]; exact hPushCall
  · rw [fnAddr_offset_eq_H (name := unchunkedEkSentCt1ReceivedMergeName) (callee := Varint.decodeVarint2Name)]; exact hVarintCall
  · rw [fnAddr_offset_eq_H (name := unchunkedEkSentCt1ReceivedMergeName) (callee := skipField3Name)]; exact hSkipCall
  · have h_off : (libsignalSessionCode.rebase b H).fnAddr unchunkedEkSentCt1ReceivedMergeName + 0xffffffffffffb53c#64 =
        (libsignalSessionCode.rebase b H).fnAddr bytesMerge3Name := by
      change (b + BitVec.ofNat 64 (libsignalSessionCode.fnOff unchunkedEkSentCt1ReceivedMergeName)) + 0xffffffffffffb53c#64 =
        b + BitVec.ofNat 64 (libsignalSessionCode.fnOff bytesMerge3Name)
      rw [unchunkedEkSentCt1ReceivedMerge_fnOff, bytesMerge3_fnOff]; bv_omega
    rw [h_off]; exact hBytesCall
  · have h_off : (libsignalSessionCode.rebase b H).fnAddr unchunkedEkSentCt1ReceivedMergeName + 0xffffffffffffc338#64 =
        (libsignalSessionCode.rebase b H).fnAddr authMergeName := by
      change (b + BitVec.ofNat 64 (libsignalSessionCode.fnOff unchunkedEkSentCt1ReceivedMergeName)) + 0xffffffffffffc338#64 =
        b + BitVec.ofNat 64 (libsignalSessionCode.fnOff authMergeName)
      rw [unchunkedEkSentCt1ReceivedMerge_fnOff, authMerge_fnOff]; bv_omega
    rw [h_off]; exact hAuthCall

/-- `prost::encoding::message::merge::<unchunked::EkSentCt1Received, &mut &[u8]>` (`0x51c00`) meets
`(unchunkedEkSentCt1ReceivedMergeSpec A).inImage img` on `tripleRatchetProgAtExt img.base ext`
given `(bytesMerge3RawSpec A).inImage img`. -/
theorem unchunkedEkSentCt1ReceivedMerge_ok_ext {img : Obj.Image} {C : Crypto} {A : RustAlloc} {ctl : BitVec 64}
    {S : SpqrModel} {ext : String → Option (State → State)} (hC : Stage2Contracts img.base C A ctl uuidTryParse S ext)
    (hBytes : subroutine_ok (tripleRatchetProgAtExt img.base ext) ((tripleRatchetProgAtExt img.base ext).fnAddr bytesMerge3Name)
      ((bytesMerge3RawSpec A).inImage img)) :
    subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr unchunkedEkSentCt1ReceivedMergeName)
      ((unchunkedEkSentCt1ReceivedMergeSpec A).inImage img) := by
  exact unchunkedEkSentCt1ReceivedMerge_ok_of_fnAddr
    hC.decode_error_from hC.decode_error_push
    (decodeVarint2_ok_ext hC) (skipField3_ok_ext hC)
    hBytes (auth_merge_ok_of_fnAddr hC.decode_error_from hC.decode_error_push (decodeVarint2_ok_ext hC) (skipField3_ok_ext hC) hBytes)

/-- End-to-end verification of `prost::encoding::message::merge::<unchunked::EkSentCt1Received, &mut &[u8]>` (`0x51c00`)
from `Stage2Contracts` and `BytesMerge3Contracts` (`bytes_merge_3_ok_ext`). -/
theorem unchunkedEkSentCt1ReceivedMerge_ok_ext_of_bytes_contracts {img : Obj.Image} {C : Crypto} {A : RustAlloc}
    {ctl : BitVec 64} {S : SpqrModel} {ext : String → Option (State → State)}
    (hC : Stage2Contracts img.base C A ctl uuidTryParse S ext)
    (hBC : BytesMerge3Contracts img A ext) :
    subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr unchunkedEkSentCt1ReceivedMergeName)
      ((unchunkedEkSentCt1ReceivedMergeSpec A).inImage img) :=
  unchunkedEkSentCt1ReceivedMerge_ok_ext hC hBC.ok_ext

/-! ## 4. Placed (`[LibsignalPlacement]`) Verification (Block 311) -/

theorem ekSent_tag4_step_placed [LibsignalPlacement] {A : RustAlloc}
    {H : String → Option (State → State)}
    (hPushCall : subroutine_ok ((blkPC_311).rebase (blkPl_311).base H) (lsmpl.base 257) (decodeErrorPushSpec A))
    (hBytesCall : subroutine_ok ((blkPC_311).rebase (blkPl_311).base H) (lsmpl.base 290) (withLsCodeRoLoaded lsmpl (bytesMerge3RawSpec A)))
    {x : UnchunkedEkSentCt1ReceivedMergeGhost} {R : SepProp} {s0 s : State}
    {m : V1State.Unchunked.EkSentCt1Received} {rest : List (BitVec 8)} {iwt : WireType} {limit : Nat}
    (hsp_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hrest_le : rest.length ≤ x.bs.length)
    (hrest_lt : rest.length < 2 ^ 63)
    (hrest_suf : IsDropSuffix x.bs rest)
    (hnone_of_mb : mergeBytes iwt rest = none →
      (Proto.mergeMessage V1State.Unchunked.EkSentCt1Received.mergeField (codecWireTypeToProto x.wt) x.msg x.bs 98).toOption = none)
    (hcont : ∀ (v rest' : List (BitVec 8)) (s' : State),
      mergeBytes iwt rest = some (v, rest') →
      s'.pc = (blkPl_311).base + 152#64 →
      s'.status = .Running →
      s'.sp = s0.sp - 112#64 →
      s'.trace = s0.trace →
      s'.readReg64 (Reg.gpr 19#5) = x.bufRef →
      s'.readReg64 (Reg.gpr 20#5) = x.msgPtr →
      s'.readReg64 (Reg.gpr 21#5) = x.slot →
      s'.readReg64 (Reg.gpr 22#5) = BitVec.ofNat 64 limit →
      s'.readReg64 (Reg.gpr 23#5) = 1#64 →
      HighCalleeSaved24 s0 s' →
      LibsignalCodeRoLoaded lsmpl s'.mem →
      SepWPp ((blkPC_311).rebase (blkPl_311).base H) (s0.readReg64 Reg.lr) s'
        (ekSentLoopPre A s0 x.msgPtr x.bufRef x.slot x.ptr { m with ct1 := v } x.bs rest')
        (WppPost (unchunkedEkSentCt1ReceivedMergeOwnSpec A) x R s0)
        (WppPanic R s0))
    (hpc : s.pc = (blkPl_311).base + 292#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = s0.sp - 112#64)
    (htr : s.trace = s0.trace)
    (hx0 : s.readReg64 (Reg.gpr 0#5) = BitVec.ofNat 64 iwt.toNat)
    (hx19 : s.readReg64 (Reg.gpr 19#5) = x.bufRef)
    (hx20 : s.readReg64 (Reg.gpr 20#5) = x.msgPtr)
    (hx21 : s.readReg64 (Reg.gpr 21#5) = x.slot)
    (hx22 : s.readReg64 (Reg.gpr 22#5) = BitVec.ofNat 64 limit)
    (hx23 : s.readReg64 (Reg.gpr 23#5) = 1#64)
    (hcs : HighCalleeSaved24 s0 s) (hinv : LibsignalCodeRoLoaded lsmpl s.mem) :
    SepWPp ((blkPC_311).rebase (blkPl_311).base H) (s0.readReg64 Reg.lr) s
      (ekSentLoopPre A s0 x.msgPtr x.bufRef x.slot x.ptr m x.bs rest)
      (WppPost (unchunkedEkSentCt1ReceivedMergeOwnSpec A) x R s0)
      (WppPanic R s0) := by
  obtain ⟨hx24, hx25, hx26, hx27, hx28, hvregs⟩ := hcs
  let restPtr : BitVec 64 := x.ptr + BitVec.ofNat 64 (x.bs.length - rest.length)
  have hpush_exit := @ekSent_push_err_exit_placed _ A H hPushCall x R s0
  refine SepWPp.of_sepWP_lscro (mid := lsmpl.base 290) hinv ?_
  conv =>
    arg 4
    rw [ekSentLoopPre, protoUnchunkedEkSentCt1ReceivedCapAt,
      sliceCursorAfter_eq_split hrest_le hrest_suf,
      unchunkedMergeBelow_bytesMerge3 s0.sp]
  conv =>
    arg 4
    rw [show vecU8CapAt A (x.msgPtr + 0x18#64) rest.length m.ct1 =
      (∃∗ cap : BitVec 64, ∃∗ ptr : BitVec 64, ⌜BytesMergeCapOk cap rest.length⌝ ∗ vecU8At A (x.msgPtr + 0x18#64) cap ptr m.ct1) from rfl]
    simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
  apply SepWP.exists_elim; intro cap2
  apply SepWP.exists_elim; intro ptr2
  conv => arg 4; rw [← sepConj_assoc, sepConj_comm (vecU8CapAt A x.msgPtr rest.length m.dk), sepConj_assoc]
  apply SepWP.pure_elim; intro hcap2
  wp_steps
  wp_reach; intro hinv_c
  refine SepWPp.call_frame_lscro (hinv := hinv_c) (x := ⟨iwt, x.msgPtr + 0x18#64, cap2, ptr2, m.ct1, x.bufRef, x.slot, restPtr, rest⟩)
    (ret_pc := (blkPl_311).base + 304#64) hBytesCall
    (by simp only [arm64_norm]) (by simp only [arm64_norm, hrun])
    (by simp only [State.spAligned, hsp, arm64_norm]; exact hsp_align)
    (by simp only [arm64_norm])
    (by dsimp only [bytesMerge3RawSpec]; simp only [arm64_norm, hsp, hx0, hx19, hx20, setWidth8_ofNat64_wt]; rfl)
    (⟨hrest_lt, hcap2⟩ : rest.length < 2 ^ 63 ∧ BytesMergeCapOk cap2 rest.length)
    (by sep_focus)
    (fun _ _ _ _ hex => allowPanic_not_exited hex)
    (fun sf _ hpan => by dsimp only [bytesMerge3RawSpec] at hpan; exact allowPanic_frame' (by simp only [arm64_norm, htr]) hpan)
    ?_
  intro sm hpcm hrunm hspm hcsm hinv_m
  simp only [CalleeSavedPreserved] at hcsm
  obtain ⟨hx19_m, hx20_m, hx21_m, hx22_m, hx23_m, hx24_m, hx25_m, hx26_m, hx27_m, hx28_m, hfp_m, hvregs_m⟩ := hcsm
  simp (config := { decide := true }) only [arm64_norm, hsp, hx19, hx20, hx21, hx22, hx23, hx24, hx25, hx26, hx27, hx28, hvregs] at hpcm hrunm hspm hx19_m hx20_m hx21_m hx22_m hx23_m hx24_m hx25_m hx26_m hx27_m hx28_m hfp_m hvregs_m hvregs_m
  cases hmb : mergeBytes iwt rest with
  | none =>
    have hnone := hnone_of_mb hmb
    apply SepWPp.of_sepWP (mid := (blkPl_311).base + 656#64)
    conv => arg 4; simp only [bytesMerge3RawSpec, hmb, memRegion_48_split_112 s0.sp,
      sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc, arm64_norm, hsp]
    apply SepWP.exists_elim; intro v_stk0
    apply SepWP.pure_elim; rintro ⟨htrm, hsm0⟩
    have hcbnz : (sm.readReg64 (Reg.gpr 0#5) == 0#64) = false := beq_eq_false_iff_ne.mpr hsm0
    apply SepWP.fold (unchunkedMergeBelow_bytesMerge3_entails s0.sp) (by sep_focus)
    apply SepWP.fold (pointsToBytes_prefix_join hrest_le hrest_suf) (by sep_focus)
    have hct1 : vecU8At A (x.msgPtr + 24#64) cap2 ptr2 m.ct1 ⊢ vecU8 A (x.msgPtr + 0x18#64) m.ct1 :=
      Entails.sepExists_right cap2 (Entails.sepExists_right ptr2 (Entails.refl _))
    apply SepWP.fold hct1 (by sep_focus)
    apply SepWP.fold (vecU8CapAt_entails_vecU8_u A x.msgPtr rest.length m.dk) (by sep_focus)
    apply SepWP.fold (optProtoAuthenticatorCapAt_entails_optProtoAuthenticatorAt A (x.msgPtr + 0x30#64) rest.length m.auth) (by sep_focus)
    apply SepWP.fold (ekSent_fields_entails_exists A x.msgPtr m) (by sep_focus)
    wp_steps
    wp_reach
    apply SepWPp.weaken_pre (P' :=
      ((s0.sp - 112#64) ↦₆₄ sm.readReg64 (Reg.gpr 0#5)) ∗
        decodeErrorAtStackLen A (sm.readReg64 (Reg.gpr 0#5)) 0 ∗
        memRegion (s0.sp - 104#64) 40 ∗
        unchunkedMergeBelow s0.sp ∗
        ekSentErrFrame A s0 x.msgPtr x.bufRef x.slot x.ptr x.bs)
      (by dsimp only [ekSentErrFrame]; sep_entail)
    exact hpush_exit hnone hsm0 (Nat.zero_le 1) hsp_align
      (by simp only [arm64_norm]) (by simp only [arm64_norm, hrunm])
      (by simp only [arm64_norm, hspm]) (by simp only [arm64_norm, htrm, htr])
      (by simp only [arm64_norm, hspm])
      ⟨by simp only [arm64_norm, hx24_m], by simp only [arm64_norm, hx25_m],
       by simp only [arm64_norm, hx26_m], by simp only [arm64_norm, hx27_m],
       by simp only [arm64_norm, hx28_m], by simp only [arm64_norm, hvregs_m]⟩
  | some p =>
    rcases p with ⟨v, rest'⟩
    have hrest'_le : rest'.length ≤ rest.length := mergeBytes_length hmb
    refine SepWPp.of_sepWP_lscro (mid := (blkPl_311).base + 152#64) hinv_m ?_
    conv => arg 4; simp only [bytesMerge3RawSpec, hmb, sepExists_sepConj_left, sepExists_sepConj_right,
      sepConj_assoc, arm64_norm, hsp]
    apply SepWP.exists_elim; intro cap2'
    apply SepWP.exists_elim; intro ptr2'
    apply SepWP.pure_elim; rintro ⟨htrm, hsm0, hcap2'⟩
    apply SepWP.fold (unchunkedMergeBelow_bytesMerge3_entails s0.sp) (by sep_focus)
    apply SepWP.fold (sliceCursorAfter_join hrest_le hrest_suf hrest'_le) (by sep_focus)
    have hct1_cap : vecU8At A (x.msgPtr + 24#64) cap2' ptr2' v ⊢ vecU8CapAt A (x.msgPtr + 0x18#64) rest'.length v := by
      unfold vecU8CapAt
      refine Entails.trans (Entails.pure_right hcap2' (Entails.refl _)) ?_
      exact Entails.sepExists_right cap2' (Entails.sepExists_right ptr2' (Entails.refl _))
    apply SepWP.fold hct1_cap (by sep_focus)
    apply SepWP.fold (vecU8CapAt_mono_u A x.msgPtr m.dk hrest'_le) (by sep_focus)
    apply SepWP.fold (optProtoAuthenticatorCapAt_mono A (x.msgPtr + 0x30#64) m.auth hrest'_le) (by sep_focus)
    wp_steps
    wp_reach; intro hinv_n
    apply SepWPp.weaken_pre (P' :=
      ekSentLoopPre A s0 x.msgPtr x.bufRef x.slot x.ptr { m with ct1 := v } x.bs rest')
      (by dsimp only [ekSentLoopPre, protoUnchunkedEkSentCt1ReceivedCapAt]; sep_entail)
    exact hcont v rest' _ hmb
      (by simp only [arm64_norm]) (by simp only [arm64_norm, hrunm])
      (by simp only [arm64_norm, hspm]) (by simp only [arm64_norm, htrm, htr])
      (by simp only [arm64_norm, hx19_m]) (by simp only [arm64_norm, hx20_m])
      (by simp only [arm64_norm, hx21_m]) (by simp only [arm64_norm, hx22_m])
      (by simp only [arm64_norm, hx23_m])
      ⟨by simp only [arm64_norm, hx24_m], by simp only [arm64_norm, hx25_m],
       by simp only [arm64_norm, hx26_m], by simp only [arm64_norm, hx27_m],
       by simp only [arm64_norm, hx28_m], by simp only [arm64_norm, hvregs_m]⟩ hinv_n

theorem ekSent_loop_le_exit_placed [LibsignalPlacement] {A : RustAlloc}
    {H : String → Option (State → State)}
    (hFromCall : subroutine_ok ((blkPC_311).rebase (blkPl_311).base H) (lsmpl.base 261) (decodeErrorFromSpec A))
    {x : UnchunkedEkSentCt1ReceivedMergeGhost} {R : SepProp} {s0 s : State}
    {m : V1State.Unchunked.EkSentCt1Received} {cur : List (BitVec 8)} {limit : Nat}
    (hle_lim : cur.length ≤ limit)
    (hsp_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hcur_le : cur.length ≤ x.bs.length)
    (hcur_suf : IsDropSuffix x.bs cur)
    (hlim_lt : limit < 2 ^ 63)
    (hres_cur : (Proto.mergeMessage V1State.Unchunked.EkSentCt1Received.mergeField (codecWireTypeToProto x.wt) x.msg x.bs 98).toOption =
      (mergeLoopBin V1State.Unchunked.EkSentCt1Received.mergeField (cur.length - limit) m cur limit 97).map
        (fun m' => (m', x.bs.drop (x.bs.length - limit))))
    (hpc : s.pc = (blkPl_311).base + 152#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = s0.sp - 112#64)
    (htr : s.trace = s0.trace)
    (hx21 : s.readReg64 (Reg.gpr 21#5) = x.slot)
    (hx22 : s.readReg64 (Reg.gpr 22#5) = BitVec.ofNat 64 limit)
    (hcs : HighCalleeSaved24 s0 s) :
    SepWPp ((blkPC_311).rebase (blkPl_311).base H) (s0.readReg64 Reg.lr) s
      (ekSentLoopPre A s0 x.msgPtr x.bufRef x.slot x.ptr m x.bs cur)
      (WppPost (unchunkedEkSentCt1ReceivedMergeOwnSpec A) x R s0)
      (WppPanic R s0) := by
  obtain ⟨hx24, hx25, hx26, hx27, hx28, hvregs⟩ := hcs
  let curPtr : BitVec 64 := x.ptr + BitVec.ofNat 64 (x.bs.length - cur.length)
  by_cases heq_lim : cur.length = limit
  · obtain ⟨hcmp1, hcmp2, hcmp3⟩ := cmp_len_limit_of_eq heq_lim
    have hcur_eq_drop : x.bs.drop (x.bs.length - limit) = cur := by
      rw [← heq_lim]; exact hcur_suf.symm
    have hsome : (Proto.mergeMessage V1State.Unchunked.EkSentCt1Received.mergeField (codecWireTypeToProto x.wt) x.msg x.bs 98).toOption =
        some (m, cur) := by
      rw [hres_cur, mergeLoopBin_eq_limit _ _ _ _ _ _ heq_lim, Option.map_some, hcur_eq_drop]
    apply SepWPp.of_sepWP_ret
    unfold WppPost unchunkedEkSentCt1ReceivedMergeOwnSpec
    simp only [hsome, stackAt_unchunkedMerge s0.sp, ekSentLoopPre,
      sliceCursorAfter_eq_split hcur_le hcur_suf, sliceCursorAt,
      sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc, arm64_norm, htr, hsp]
    wp_steps
    wp_done
  · have hlt_lim : cur.length < limit := Nat.lt_of_le_of_ne hle_lim heq_lim
    obtain ⟨hcmp1, hcmp2, hcmp3⟩ := cmp_len_limit_of_lt hlt_lim hlim_lt
    have hnone : (Proto.mergeMessage V1State.Unchunked.EkSentCt1Received.mergeField (codecWireTypeToProto x.wt) x.msg x.bs 98).toOption = none := by
      rw [hres_cur, mergeLoopBin_lt_limit _ _ _ _ _ _ hlt_lim, Option.map_none]
    have hfrom_exit := @ekSent_from_err_exit_placed _ A H hFromCall x R s0
    apply SepWPp.of_sepWP (mid := (blkPl_311).base + 108#64)
    conv => arg 4; rw [ekSentLoopPre, sliceCursorAfter_eq_split hcur_le hcur_suf,
      sliceCursorAt, memRegion_48_split_112 s0.sp]
    simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
    apply SepWP.exists_elim; intro v_stk0
    wp_steps
    apply SepWP.fold (pointsTo64_pair_entails_memRegion16 x.slot curPtr (BitVec.ofNat 64 cur.length)) (by sep_focus)
    apply SepWP.fold (pointsToBytes_prefix_join hcur_le hcur_suf) (by sep_focus)
    apply SepWP.fold (protoUnchunkedEkSentCt1ReceivedCapAt_entails_exists A x.msgPtr cur.length m) (by sep_focus)
    wp_reach
    apply SepWPp.weaken_pre (P' :=
      ((s0.sp - 112#64) ↦₆₄ 0x8000000000000008#64) ∗
        memRegion (s0.sp - 104#64) 40 ∗
        unchunkedMergeBelow s0.sp ∗
        ekSentErrFrame A s0 x.msgPtr x.bufRef x.slot x.ptr x.bs)
      (by dsimp only [ekSentErrFrame]; sep_entail)
    exact hfrom_exit hnone (by decide : KindNoHeap 0x8000000000000008#64) hsp_align
      (by simp only [arm64_norm]) (by simp only [arm64_norm, hrun])
      (by simp only [arm64_norm, hsp]) (by simp only [arm64_norm, htr])
      ⟨by simp only [arm64_norm, hx24], by simp only [arm64_norm, hx25],
       by simp only [arm64_norm, hx26], by simp only [arm64_norm, hx27],
       by simp only [arm64_norm, hx28], by simp only [arm64_norm, hvregs]⟩

theorem ekSent_decode_key_step_placed [LibsignalPlacement] {A : RustAlloc}
    {H : String → Option (State → State)}
    (hFromCall : subroutine_ok ((blkPC_311).rebase (blkPl_311).base H) (lsmpl.base 261) (decodeErrorFromSpec A))
    (hVarintCall : subroutine_ok ((blkPC_311).rebase (blkPl_311).base H) (lsmpl.base 291) (decodeVarint2Spec A))
    {x : UnchunkedEkSentCt1ReceivedMergeGhost} {R : SepProp} {s0 s : State}
    {m : V1State.Unchunked.EkSentCt1Received} {cur : List (BitVec 8)} {limit : Nat}
    (hgt_lim : ¬ cur.length ≤ limit)
    (hsp_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hcur_le : cur.length ≤ x.bs.length)
    (hcur_lt : cur.length < 2 ^ 63)
    (hcur_suf : IsDropSuffix x.bs cur)
    (hres_cur : (Proto.mergeMessage V1State.Unchunked.EkSentCt1Received.mergeField (codecWireTypeToProto x.wt) x.msg x.bs 98).toOption =
      (mergeLoopBin V1State.Unchunked.EkSentCt1Received.mergeField (cur.length - limit) m cur limit 97).map
        (fun m' => (m', x.bs.drop (x.bs.length - limit))))
    (hcont : ∀ (key : BitVec 64) (iwt : WireType) (rest : List (BitVec 8)) (s' : State),
      decodeVarint cur = some (key, rest) →
      ¬ 2 ^ 32 ≤ key.toNat →
      WireType.ofNat? (key.toNat % 8) = some iwt →
      ¬ key.toNat / 8 < 1 →
      s'.pc = (blkPl_311).base + 204#64 →
      s'.status = .Running →
      s'.sp = s0.sp - 112#64 →
      s'.trace = s0.trace →
      s'.readReg64 (Reg.gpr 0#5) = BitVec.ofNat 64 iwt.toNat →
      s'.readReg64 (Reg.gpr 1#5) = BitVec.ofNat 64 (key.toNat / 8) →
      s'.readReg64 (Reg.gpr 19#5) = x.bufRef →
      s'.readReg64 (Reg.gpr 20#5) = x.msgPtr →
      s'.readReg64 (Reg.gpr 21#5) = x.slot →
      s'.readReg64 (Reg.gpr 22#5) = BitVec.ofNat 64 limit →
      s'.readReg64 (Reg.gpr 23#5) = 1#64 →
      HighCalleeSaved24 s0 s' →
      LibsignalCodeRoLoaded lsmpl s'.mem →
      SepWPp ((blkPC_311).rebase (blkPl_311).base H) (s0.readReg64 Reg.lr) s'
        (ekSentLoopPre A s0 x.msgPtr x.bufRef x.slot x.ptr m x.bs rest)
        (WppPost (unchunkedEkSentCt1ReceivedMergeOwnSpec A) x R s0)
        (WppPanic R s0))
    (hpc : s.pc = (blkPl_311).base + 152#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = s0.sp - 112#64)
    (htr : s.trace = s0.trace)
    (hx19 : s.readReg64 (Reg.gpr 19#5) = x.bufRef)
    (hx20 : s.readReg64 (Reg.gpr 20#5) = x.msgPtr)
    (hx21 : s.readReg64 (Reg.gpr 21#5) = x.slot)
    (hx22 : s.readReg64 (Reg.gpr 22#5) = BitVec.ofNat 64 limit)
    (hx23 : s.readReg64 (Reg.gpr 23#5) = 1#64)
    (hcs : HighCalleeSaved24 s0 s) (hinv : LibsignalCodeRoLoaded lsmpl s.mem) :
    SepWPp ((blkPC_311).rebase (blkPl_311).base H) (s0.readReg64 Reg.lr) s
      (ekSentLoopPre A s0 x.msgPtr x.bufRef x.slot x.ptr m x.bs cur)
      (WppPost (unchunkedEkSentCt1ReceivedMergeOwnSpec A) x R s0)
      (WppPanic R s0) := by
  obtain ⟨hx24, hx25, hx26, hx27, hx28, hvregs⟩ := hcs
  obtain ⟨hcmp1, hcmp2⟩ := cmp_len_limit_of_gt hgt_lim hcur_lt
  let curPtr : BitVec 64 := x.ptr + BitVec.ofNat 64 (x.bs.length - cur.length)
  have herr0_exit := @ekSent_err0_ret_exit_placed _ A H x R s0
  have hfrom_exit := @ekSent_from_err_exit_placed _ A H hFromCall x R s0
  refine SepWPp.of_sepWP_lscro (mid := lsmpl.base 291) hinv ?_
  conv => arg 4; rw [ekSentLoopPre, sliceCursorAfter_eq_split hcur_le hcur_suf,
    sliceCursorAt, unchunkedMergeBelow_leaf s0.sp]
  simp only [sepConj_assoc]
  wp_steps
  wp_reach; intro hinv_c
  refine SepWPp.call_frame_keep_lscro (hinv := hinv_c) (x := ⟨x.bufRef, x.slot, curPtr, cur⟩)
    (ret_pc := (blkPl_311).base + 172#64) hVarintCall
    (by simp only [arm64_norm]) (by simp only [arm64_norm, hrun])
    (by simp only [State.spAligned, hsp, arm64_norm]; exact hsp_align)
    (by simp only [arm64_norm])
    (by dsimp only [decodeVarint2Spec]; simp only [arm64_norm, hsp, hx19]; rfl)
    hcur_lt (by dsimp only [sliceCursorAt, curPtr]; sep_focus)
    (fun _ _ _ _ hex => allowPanic_not_exited hex)
    (fun sf _ hpan => allowPanic_frame' (by simp only [arm64_norm, htr]) hpan)
    ?_
  intro sm hpcm hrunm hspm hcsm hinv_m
  simp only [CalleeSavedPreserved] at hcsm
  obtain ⟨hx19_m, hx20_m, hx21_m, hx22_m, hx23_m, hx24_m, hx25_m, hx26_m, hx27_m, hx28_m, hfp_m, hvregs_m⟩ := hcsm
  simp (config := { decide := true }) only [arm64_norm, hsp, hx19, hx20, hx21, hx22, hx23, hx24, hx25, hx26, hx27, hx28, hvregs] at hpcm hrunm hspm hx19_m hx20_m hx21_m hx22_m hx23_m hx24_m hx25_m hx26_m hx27_m hx28_m hfp_m hvregs_m hvregs_m
  cases hd : decodeVarint cur with
  | none =>
    have hnone : (Proto.mergeMessage V1State.Unchunked.EkSentCt1Received.mergeField (codecWireTypeToProto x.wt) x.msg x.bs 98).toOption = none := by
      rw [hres_cur, mergeLoopBin_of_decodeVarint_none protoPrefixStep_unchunked_ekSentCt1Received_mergeField hgt_lim hd, Option.map_none]
    apply SepWPp.of_sepWP (mid := (blkPl_311).base + 120#64)
    conv => arg 4; simp only [decodeVarint2Spec, hd, sepConj_assoc, arm64_norm, hsp]
    apply SepWP.pure_elim; rintro ⟨htrm, hsm0, hsm1⟩
    apply SepWP.fold (unchunkedMergeBelow_leaf_entails s0.sp) (by sep_focus)
    apply SepWP.fold (pointsToBytes_prefix_join hcur_le hcur_suf) (by sep_focus)
    apply SepWP.fold (protoUnchunkedEkSentCt1ReceivedCapAt_entails_exists A x.msgPtr cur.length m) (by sep_focus)
    wp_steps
    wp_reach
    apply SepWPp.weaken_pre (P' :=
      decodeErrorAtStackLen A (sm.readReg64 (Reg.gpr 1#5)) 0 ∗
        memRegion (s0.sp - 112#64) 48 ∗
        unchunkedMergeBelow s0.sp ∗
        ekSentErrFrame A s0 x.msgPtr x.bufRef x.slot x.ptr x.bs)
      (by dsimp only [ekSentErrFrame]; sep_entail)
    exact herr0_exit hnone hsp_align
      (by simp only [arm64_norm]) (by simp only [arm64_norm, hrunm])
      (by simp only [arm64_norm, hspm]) (by simp only [arm64_norm, htrm, htr])
      (by simp only [arm64_norm]) hsm1
      ⟨by simp only [arm64_norm, hx24_m], by simp only [arm64_norm, hx25_m],
       by simp only [arm64_norm, hx26_m], by simp only [arm64_norm, hx27_m],
       by simp only [arm64_norm, hx28_m], by simp only [arm64_norm, hvregs_m]⟩
  | some p =>
    rcases p with ⟨key, rest⟩
    have hrest_lt_cur : rest.length < cur.length := decodeVarint_length hd
    have hrest_le_cur : rest.length ≤ cur.length := Nat.le_of_lt hrest_lt_cur
    have hrest_le : rest.length ≤ x.bs.length := Nat.le_trans hrest_le_cur hcur_le
    have hrest_suf : IsDropSuffix x.bs rest :=
      suffix_trans hcur_le hcur_suf hrest_le_cur (decodeVarint_suffix hd)
    let restPtr : BitVec 64 := x.ptr + BitVec.ofNat 64 (x.bs.length - rest.length)
    by_cases hk_ge : 2 ^ 32 ≤ key.toNat
    · have hnone : (Proto.mergeMessage V1State.Unchunked.EkSentCt1Received.mergeField (codecWireTypeToProto x.wt) x.msg x.bs 98).toOption = none := by
        rw [hres_cur, mergeLoopBin_of_key_ge protoPrefixStep_unchunked_ekSentCt1Received_mergeField hgt_lim hd hk_ge, Option.map_none]
      have hshr := key_shr32_of_ge hk_ge
      apply SepWPp.of_sepWP (mid := (blkPl_311).base + 108#64)
      conv => arg 4; simp only [decodeVarint2Spec, hd, sepConj_assoc, arm64_norm, hsp]
      apply SepWP.pure_elim; rintro ⟨htrm, hsm0, hsm1⟩
      apply SepWP.fold (unchunkedMergeBelow_leaf_entails s0.sp) (by sep_focus)
      apply SepWP.fold (sliceCursorAfter_join hcur_le hcur_suf hrest_le_cur) (by sep_focus)
      conv => arg 4; rw [sliceCursorAfter_eq_split hrest_le hrest_suf, sliceCursorAt, memRegion_48_split2_112 s0.sp]
      simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
      apply SepWP.exists_elim; intro v_err0
      apply SepWP.exists_elim; intro v_err1
      wp_steps
      apply SepWP.fold (protoUnchunkedEkSentCt1ReceivedCapAt_entails_exists A x.msgPtr cur.length m) (by sep_focus)
      apply SepWP.fold (pointsTo64_pair_entails_memRegion16 x.slot restPtr (BitVec.ofNat 64 rest.length)) (by sep_focus)
      apply SepWP.fold (pointsToBytes_prefix_join hrest_le hrest_suf) (by sep_focus)
      apply SepWP.fold (pointsTo64_memRegion32_entails_40_112 s0.sp key) (by sep_focus)
      wp_reach
      apply SepWPp.weaken_pre (P' :=
        ((s0.sp - 112#64) ↦₆₄ 0x8000000000000004#64) ∗
          memRegion (s0.sp - 104#64) 40 ∗
          unchunkedMergeBelow s0.sp ∗
          ekSentErrFrame A s0 x.msgPtr x.bufRef x.slot x.ptr x.bs)
        (by dsimp only [ekSentErrFrame]; sep_entail)
      exact hfrom_exit hnone (by decide : KindNoHeap 0x8000000000000004#64) hsp_align
        (by simp only [arm64_norm]) (by simp only [arm64_norm, hrunm])
        (by simp only [arm64_norm, hspm]) (by simp only [arm64_norm, htrm, htr])
        ⟨by simp only [arm64_norm, hx24_m], by simp only [arm64_norm, hx25_m],
         by simp only [arm64_norm, hx26_m], by simp only [arm64_norm, hx27_m],
         by simp only [arm64_norm, hx28_m], by simp only [arm64_norm, hvregs_m]⟩
    · have hshr := key_shr32_of_lt hk_ge
      cases hwt : WireType.ofNat? (key.toNat % 8) with
      | none =>
        have hnone : (Proto.mergeMessage V1State.Unchunked.EkSentCt1Received.mergeField (codecWireTypeToProto x.wt) x.msg x.bs 98).toOption = none := by
          rw [hres_cur, mergeLoopBin_of_wt_none protoPrefixStep_unchunked_ekSentCt1Received_mergeField hgt_lim hd hk_ge hwt, Option.map_none]
        obtain ⟨hcs1, hcs2⟩ := key_wt_none hwt
        apply SepWPp.of_sepWP (mid := (blkPl_311).base + 108#64)
        conv => arg 4; simp only [decodeVarint2Spec, hd, sepConj_assoc, arm64_norm, hsp]
        apply SepWP.pure_elim; rintro ⟨htrm, hsm0, hsm1⟩
        apply SepWP.fold (unchunkedMergeBelow_leaf_entails s0.sp) (by sep_focus)
        apply SepWP.fold (sliceCursorAfter_join hcur_le hcur_suf hrest_le_cur) (by sep_focus)
        conv => arg 4; rw [sliceCursorAfter_eq_split hrest_le hrest_suf, sliceCursorAt, memRegion_48_split2_112 s0.sp]
        simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
        apply SepWP.exists_elim; intro v_err0
        apply SepWP.exists_elim; intro v_err1
        wp_steps
        apply SepWP.fold (protoUnchunkedEkSentCt1ReceivedCapAt_entails_exists A x.msgPtr cur.length m) (by sep_focus)
        apply SepWP.fold (pointsTo64_pair_entails_memRegion16 x.slot restPtr (BitVec.ofNat 64 rest.length)) (by sep_focus)
        apply SepWP.fold (pointsToBytes_prefix_join hrest_le hrest_suf) (by sep_focus)
        apply SepWP.fold (pointsTo64_memRegion32_entails_40_112 s0.sp (key &&& 7#64)) (by sep_focus)
        wp_reach
        apply SepWPp.weaken_pre (P' :=
          ((s0.sp - 112#64) ↦₆₄ 0x8000000000000003#64) ∗
            memRegion (s0.sp - 104#64) 40 ∗
            unchunkedMergeBelow s0.sp ∗
            ekSentErrFrame A s0 x.msgPtr x.bufRef x.slot x.ptr x.bs)
          (by dsimp only [ekSentErrFrame]; sep_entail)
        exact hfrom_exit hnone (by decide : KindNoHeap 0x8000000000000003#64) hsp_align
          (by simp only [arm64_norm]) (by simp only [arm64_norm, hrunm])
          (by simp only [arm64_norm, hspm]) (by simp only [arm64_norm, htrm, htr])
          ⟨by simp only [arm64_norm, hx24_m], by simp only [arm64_norm, hx25_m],
           by simp only [arm64_norm, hx26_m], by simp only [arm64_norm, hx27_m],
           by simp only [arm64_norm, hx28_m], by simp only [arm64_norm, hvregs_m]⟩
      | some iwt =>
        obtain ⟨hcc1, hcc2, hand_wt, hcc1_wt, hcc2_wt⟩ := key_wt_some hwt
        obtain ⟨hw1, hw1_2⟩ := w1_tag_eq hk_ge
        obtain ⟨hw1_zext1, hw1_zext2⟩ := bv32_zeroExtend_ofNat (n := key.toNat / 8) (by omega)
        by_cases hitag0 : key.toNat / 8 < 1
        · have hnone : (Proto.mergeMessage V1State.Unchunked.EkSentCt1Received.mergeField (codecWireTypeToProto x.wt) x.msg x.bs 98).toOption = none := by
            rw [hres_cur, mergeLoopBin_of_tag_zero protoPrefixStep_unchunked_ekSentCt1Received_mergeField hgt_lim hd hk_ge hwt hitag0, Option.map_none]
          have htag_zero : key.toNat / 8 = 0 := by omega
          apply SepWPp.of_sepWP (mid := (blkPl_311).base + 108#64)
          conv => arg 4; simp only [decodeVarint2Spec, hd, sepConj_assoc, arm64_norm, hsp]
          apply SepWP.pure_elim; rintro ⟨htrm, hsm0, hsm1⟩
          apply SepWP.fold (unchunkedMergeBelow_leaf_entails s0.sp) (by sep_focus)
          apply SepWP.fold (sliceCursorAfter_join hcur_le hcur_suf hrest_le_cur) (by sep_focus)
          conv => arg 4; rw [sliceCursorAfter_eq_split hrest_le hrest_suf, sliceCursorAt, memRegion_48_split_112 s0.sp]
          simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
          apply SepWP.exists_elim; intro v_err0
          wp_steps
          apply SepWP.fold (protoUnchunkedEkSentCt1ReceivedCapAt_entails_exists A x.msgPtr cur.length m) (by sep_focus)
          apply SepWP.fold (pointsTo64_pair_entails_memRegion16 x.slot restPtr (BitVec.ofNat 64 rest.length)) (by sep_focus)
          apply SepWP.fold (pointsToBytes_prefix_join hrest_le hrest_suf) (by sep_focus)
          wp_reach
          apply SepWPp.weaken_pre (P' :=
            ((s0.sp - 112#64) ↦₆₄ 0x8000000000000005#64) ∗
              memRegion (s0.sp - 104#64) 40 ∗
              unchunkedMergeBelow s0.sp ∗
              ekSentErrFrame A s0 x.msgPtr x.bufRef x.slot x.ptr x.bs)
            (by dsimp only [ekSentErrFrame]; sep_entail)
          exact hfrom_exit hnone (by decide : KindNoHeap 0x8000000000000005#64) hsp_align
            (by simp only [arm64_norm]) (by simp only [arm64_norm, hrunm])
            (by simp only [arm64_norm, hspm]) (by simp only [arm64_norm, htrm, htr])
            ⟨by simp only [arm64_norm, hx24_m], by simp only [arm64_norm, hx25_m],
             by simp only [arm64_norm, hx26_m], by simp only [arm64_norm, hx27_m],
             by simp only [arm64_norm, hx28_m], by simp only [arm64_norm, hvregs_m]⟩
        · obtain ⟨hcbz_tag1, hcbz_tag2⟩ := tag_cbz_false hk_ge hitag0
          have hcbz_tag64 : (BitVec.ofNat 64 (key.toNat / 8) == 0#64) = false := by
            rw [beq_eq_false_iff_ne]; intro h
            have h1 := congrArg BitVec.toNat h
            simp only [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega : key.toNat / 8 < 2 ^ 64)] at h1
            omega
          refine SepWPp.of_sepWP_lscro (mid := (blkPl_311).base + 204#64) hinv_m ?_
          conv => arg 4; simp only [decodeVarint2Spec, hd, sepConj_assoc, arm64_norm, hsp]
          apply SepWP.pure_elim; rintro ⟨htrm, hsm0, hsm1⟩
          apply SepWP.fold (unchunkedMergeBelow_leaf_entails s0.sp) (by sep_focus)
          apply SepWP.fold (sliceCursorAfter_join hcur_le hcur_suf hrest_le_cur) (by sep_focus)
          apply SepWP.fold (protoUnchunkedEkSentCt1ReceivedCapAt_mono A x.msgPtr m hrest_le_cur) (by sep_focus)
          wp_steps
          wp_reach; intro hinv_n
          apply SepWPp.weaken_pre (P' := ekSentLoopPre A s0 x.msgPtr x.bufRef x.slot x.ptr m x.bs rest)
            (by dsimp only [ekSentLoopPre]; sep_entail)
          exact hcont key iwt rest _ hd hk_ge hwt hitag0
            (by simp only [arm64_norm]) (by simp only [arm64_norm, hrunm])
            (by simp only [arm64_norm, hspm]) (by simp only [arm64_norm, htrm, htr])
            (by simp only [arm64_norm, hsm1, hand_wt]) (by simp only [arm64_norm, hsm1, hw1, hw1_2, hw1_zext1, hw1_zext2])
            (by simp only [arm64_norm, hx19_m]) (by simp only [arm64_norm, hx20_m])
            (by simp only [arm64_norm, hx21_m]) (by simp only [arm64_norm, hx22_m])
            (by simp only [arm64_norm, hx23_m])
            ⟨by simp only [arm64_norm, hx24_m], by simp only [arm64_norm, hx25_m],
             by simp only [arm64_norm, hx26_m], by simp only [arm64_norm, hx27_m],
             by simp only [arm64_norm, hx28_m], by simp only [arm64_norm, hvregs_m]⟩ hinv_n

theorem ekSent_loop_ok_placed [LibsignalPlacement] {A : RustAlloc} {H : String → Option (State → State)}
    (hFromCall : subroutine_ok ((blkPC_311).rebase (blkPl_311).base H) (lsmpl.base 261) (decodeErrorFromSpec A))
    (hPushCall : subroutine_ok ((blkPC_311).rebase (blkPl_311).base H) (lsmpl.base 257) (decodeErrorPushSpec A))
    (hVarintCall : subroutine_ok ((blkPC_311).rebase (blkPl_311).base H) (lsmpl.base 291) (decodeVarint2Spec A))
    (hSkipCall : subroutine_ok ((blkPC_311).rebase (blkPl_311).base H) (lsmpl.base 263) (skipField3Spec A))
    (hBytesCall : subroutine_ok ((blkPC_311).rebase (blkPl_311).base H) (lsmpl.base 290) (withLsCodeRoLoaded lsmpl (bytesMerge3RawSpec A)))
    (hAuthCall : subroutine_ok ((blkPC_311).rebase (blkPl_311).base H) (lsmpl.base 295) (withLsCodeRoLoaded lsmpl (authMergeSpec A)))
    {x : UnchunkedEkSentCt1ReceivedMergeGhost} {R : SepProp} {s0 : State} {limit : Nat}
    (hsp_align : (s0.sp &&& 15#64 == 0#64) = true) (hbs_lt : x.bs.length < 2 ^ 63) (hlim_lt : limit < 2 ^ 63) :
    ∀ (n : Nat) (m : V1State.Unchunked.EkSentCt1Received) (cur : List (BitVec 8)) (s : State),
      cur.length ≤ n → cur.length ≤ x.bs.length → IsDropSuffix x.bs cur →
      (Proto.mergeMessage V1State.Unchunked.EkSentCt1Received.mergeField (codecWireTypeToProto x.wt) x.msg x.bs 98).toOption =
        (mergeLoopBin V1State.Unchunked.EkSentCt1Received.mergeField (cur.length - limit) m cur limit 97).map
          (fun m' => (m', x.bs.drop (x.bs.length - limit))) →
      s.pc = (blkPl_311).base + 152#64 →
      s.status = .Running → s.sp = s0.sp - 112#64 → s.trace = s0.trace →
      s.readReg64 (Reg.gpr 19#5) = x.bufRef → s.readReg64 (Reg.gpr 20#5) = x.msgPtr →
      s.readReg64 (Reg.gpr 21#5) = x.slot → s.readReg64 (Reg.gpr 22#5) = BitVec.ofNat 64 limit →
      s.readReg64 (Reg.gpr 23#5) = 1#64 →
      HighCalleeSaved24 s0 s →
      LibsignalCodeRoLoaded lsmpl s.mem →
      SepWPp ((blkPC_311).rebase (blkPl_311).base H) (s0.readReg64 Reg.lr) s
        (ekSentLoopPre A s0 x.msgPtr x.bufRef x.slot x.ptr m x.bs cur)
        (WppPost (unchunkedEkSentCt1ReceivedMergeOwnSpec A) x R s0) (WppPanic R s0) := by
  have htag1_varint := fun {s m rest} => @ekSent_tag1_varint_step_placed _ A H hPushCall hVarintCall x R s0 s m rest limit
  have htag1_wt_err := @ekSent_tag1_wt_err_step_placed _ A H hFromCall hPushCall x R s0
  have htag2_step := fun {s m rest iwt} => @ekSent_tag2_step_placed _ A H hPushCall hAuthCall x R s0 s m rest iwt limit
  have htag3_step := fun {s m rest iwt} => @ekSent_tag3_step_placed _ A H hPushCall hBytesCall x R s0 s m rest iwt limit
  have htag4_step := fun {s m rest iwt} => @ekSent_tag4_step_placed _ A H hPushCall hBytesCall x R s0 s m rest iwt limit
  have hskip_step := fun {s m rest tag iwt} => @ekSent_skip_step_placed _ A H hSkipCall x R s0 s m rest tag iwt limit
  intro n; induction n with
  | zero =>
    intro m cur s hcur_n hcur_le hcur_suf hres_cur hpc hrun hsp htr hx19 hx20 hx21 hx22 hx23 hcs _
    exact ekSent_loop_le_exit_placed hFromCall (by omega) hsp_align hcur_le hcur_suf hlim_lt
      hres_cur hpc hrun hsp htr hx21 hx22 hcs
  | succ n ih =>
    intro m cur s hcur_n hcur_le hcur_suf hres_cur hpc hrun hsp htr hx19 hx20 hx21 hx22 hx23 hcs hinv
    by_cases hle_lim : cur.length ≤ limit
    · exact ekSent_loop_le_exit_placed hFromCall hle_lim hsp_align hcur_le hcur_suf hlim_lt
        hres_cur hpc hrun hsp htr hx21 hx22 hcs
    · have hcur_lt : cur.length < 2 ^ 63 := Nat.lt_of_le_of_lt hcur_le hbs_lt
      refine ekSent_decode_key_step_placed hFromCall hVarintCall hle_lim hsp_align
        hcur_le hcur_lt hcur_suf hres_cur ?_ hpc hrun hsp htr hx19 hx20 hx21 hx22 hx23 hcs hinv
      intro key iwt rest s' hd hk_ge hwt hitag0 hpc' hrun' hsp' htr' hx0' hx1' hx19' hx20' hx21' hx22' hx23' hcs' hinv'
      obtain ⟨hx24', hx25', hx26', hx27', hx28', hvregs'⟩ := hcs'
      have hrest_lt_cur : rest.length < cur.length := decodeVarint_length hd
      have hrest_le_cur : rest.length ≤ cur.length := Nat.le_of_lt hrest_lt_cur
      have hrest_le : rest.length ≤ x.bs.length := Nat.le_trans hrest_le_cur hcur_le
      have hrest_lt : rest.length < 2 ^ 63 := Nat.lt_of_le_of_lt hrest_le hbs_lt
      have hrest_suf : IsDropSuffix x.bs rest := suffix_trans hcur_le hcur_suf hrest_le_cur (decodeVarint_suffix hd)
      have hloop_ok := mergeLoopBin_of_key_ok (m := m) (depth' := 97)
        protoPrefixStep_unchunked_ekSentCt1Received_mergeField hle_lim hd hk_ge hwt hitag0
      by_cases htag1 : key.toNat / 8 = 1
      · rw [htag1] at hx1' hloop_ok; rw [unchunkedEkSentCt1Received_mergeField_tag1] at hloop_ok
        refine SepWPp.of_sepWP_lscro (mid := (blkPl_311).base + 340#64) hinv' ?_; wp_steps; wp_reach; intro hinv_t
        by_cases hiwt : iwt = .varint
        · subst hiwt
          have hnone_dv : decodeVarint rest = none →
              (Proto.mergeMessage V1State.Unchunked.EkSentCt1Received.mergeField (codecWireTypeToProto x.wt) x.msg x.bs 98).toOption = none := by
            intro hdv; simp only [hres_cur, hloop_ok, eq_self, ↓reduceIte, hdv, Option.map_none]
          refine htag1_varint hsp_align hrest_le hrest_lt hrest_suf hnone_dv
            (fun v rest' s'' hdv hpc'' hrun'' hsp'' htr'' hx19'' hx20'' hx21'' hx22'' hx23'' hcs'' hinv'' => ?_)
            (by simp only [arm64_norm]) (by simp only [arm64_norm, hrun']) (by simp only [arm64_norm, hsp']) (by simp only [arm64_norm, htr'])
            (by simp only [arm64_norm, hx0']) (by simp only [arm64_norm, hx19']) (by simp only [arm64_norm, hx20'])
            (by simp only [arm64_norm, hx21']) (by simp only [arm64_norm, hx22']) (by simp only [arm64_norm, hx23'])
            ⟨by simp only [arm64_norm, hx24'], by simp only [arm64_norm, hx25'],
             by simp only [arm64_norm, hx26'], by simp only [arm64_norm, hx27'],
             by simp only [arm64_norm, hx28'], by simp only [arm64_norm, hvregs']⟩ hinv_t
          have hrest'_lt : rest'.length < rest.length := decodeVarint_length hdv
          have hrest'_le_rest : rest'.length ≤ rest.length := Nat.le_of_lt hrest'_lt
          have hres_next : (Proto.mergeMessage V1State.Unchunked.EkSentCt1Received.mergeField (codecWireTypeToProto x.wt) x.msg x.bs 98).toOption =
              (mergeLoopBin V1State.Unchunked.EkSentCt1Received.mergeField (rest'.length - limit) { m with epoch := v } rest' limit 97).map
                (fun m' => (m', x.bs.drop (x.bs.length - limit))) := by
            simp only [hres_cur, hloop_ok, eq_self, ↓reduceIte, hdv, Option.map_some]
          exact ih { m with epoch := v } rest' s'' (by omega) (by omega)
            (suffix_trans hrest_le hrest_suf hrest'_le_rest (decodeVarint_suffix hdv))
            hres_next hpc'' hrun'' hsp'' htr'' hx19'' hx20'' hx21'' hx22'' hx23'' hcs'' hinv''
        · have hnone_wt : (Proto.mergeMessage V1State.Unchunked.EkSentCt1Received.mergeField (codecWireTypeToProto x.wt) x.msg x.bs 98).toOption = none := by
            simp only [hres_cur, hloop_ok, hiwt, ↓reduceIte, Option.map_none]
          exact htag1_wt_err hiwt hsp_align hrest_le hrest_suf hnone_wt
            (by simp only [arm64_norm]) (by simp only [arm64_norm, hrun']) (by simp only [arm64_norm, hsp']) (by simp only [arm64_norm, htr'])
            (by simp only [arm64_norm, hx0'])
            ⟨by simp only [arm64_norm, hx24'], by simp only [arm64_norm, hx25'],
             by simp only [arm64_norm, hx26'], by simp only [arm64_norm, hx27'],
             by simp only [arm64_norm, hx28'], by simp only [arm64_norm, hvregs']⟩
      · by_cases htag2 : key.toNat / 8 = 2
        · rw [htag2] at hx1' hloop_ok; rw [unchunkedEkSentCt1Received_mergeField_tag2] at hloop_ok
          refine SepWPp.of_sepWP_lscro (mid := (blkPl_311).base + 228#64) hinv' ?_; wp_steps; wp_reach; intro hinv_t
          have hnone_am : (Proto.mergeMessage ProtoAuthenticator.mergeField (codecWireTypeToProto iwt) (m.auth.getD default) rest 97).toOption = none →
              (Proto.mergeMessage V1State.Unchunked.EkSentCt1Received.mergeField (codecWireTypeToProto x.wt) x.msg x.bs 98).toOption = none := by
            intro ham; simp only [hres_cur, hloop_ok, ham, Option.map_none]
          refine htag2_step hsp_align hrest_le hrest_lt hrest_suf hnone_am
            (fun v rest' s'' ham hpc'' hrun'' hsp'' htr'' hx19'' hx20'' hx21'' hx22'' hx23'' hcs'' hinv'' => ?_)
            (by simp only [arm64_norm]) (by simp only [arm64_norm, hrun']) (by simp only [arm64_norm, hsp']) (by simp only [arm64_norm, htr'])
            (by simp only [arm64_norm, hx0']) (by simp only [arm64_norm, hx19']) (by simp only [arm64_norm, hx20'])
            (by simp only [arm64_norm, hx21']) (by simp only [arm64_norm, hx22']) (by simp only [arm64_norm, hx23'])
            ⟨by simp only [arm64_norm, hx24'], by simp only [arm64_norm, hx25'],
             by simp only [arm64_norm, hx26'], by simp only [arm64_norm, hx27'],
             by simp only [arm64_norm, hx28'], by simp only [arm64_norm, hvregs']⟩ hinv_t
          have ⟨hrest'_le_rest, hrest'_suf⟩ := proto_mergeMessage_suffix ham
          have hres_next : (Proto.mergeMessage V1State.Unchunked.EkSentCt1Received.mergeField (codecWireTypeToProto x.wt) x.msg x.bs 98).toOption =
              (mergeLoopBin V1State.Unchunked.EkSentCt1Received.mergeField (rest'.length - limit) { m with auth := some v } rest' limit 97).map
                (fun m' => (m', x.bs.drop (x.bs.length - limit))) := by
            simp only [hres_cur, hloop_ok, ham, Option.map_some]
          exact ih { m with auth := some v } rest' s'' (by omega) (by omega)
            (suffix_trans hrest_le hrest_suf hrest'_le_rest hrest'_suf)
            hres_next hpc'' hrun'' hsp'' htr'' hx19'' hx20'' hx21'' hx22'' hx23'' hcs'' hinv''
        · by_cases htag3 : key.toNat / 8 = 3
          · rw [htag3] at hx1' hloop_ok; rw [unchunkedEkSentCt1Received_mergeField_tag3] at hloop_ok
            refine SepWPp.of_sepWP_lscro (mid := (blkPl_311).base + 372#64) hinv' ?_; wp_steps; wp_reach; intro hinv_t
            have hnone_mb : mergeBytes iwt rest = none →
                (Proto.mergeMessage V1State.Unchunked.EkSentCt1Received.mergeField (codecWireTypeToProto x.wt) x.msg x.bs 98).toOption = none := by
              intro hmb; simp only [hres_cur, hloop_ok, hmb, Option.map_none]
            refine htag3_step hsp_align hrest_le hrest_lt hrest_suf hnone_mb
              (fun v rest' s'' hmb hpc'' hrun'' hsp'' htr'' hx19'' hx20'' hx21'' hx22'' hx23'' hcs'' hinv'' => ?_)
              (by simp only [arm64_norm]) (by simp only [arm64_norm, hrun']) (by simp only [arm64_norm, hsp']) (by simp only [arm64_norm, htr'])
              (by simp only [arm64_norm, hx0']) (by simp only [arm64_norm, hx19']) (by simp only [arm64_norm, hx20'])
              (by simp only [arm64_norm, hx21']) (by simp only [arm64_norm, hx22']) (by simp only [arm64_norm, hx23'])
              ⟨by simp only [arm64_norm, hx24'], by simp only [arm64_norm, hx25'],
               by simp only [arm64_norm, hx26'], by simp only [arm64_norm, hx27'],
               by simp only [arm64_norm, hx28'], by simp only [arm64_norm, hvregs']⟩ hinv_t
            have hrest'_le_rest : rest'.length ≤ rest.length := mergeBytes_length hmb
            have hres_next : (Proto.mergeMessage V1State.Unchunked.EkSentCt1Received.mergeField (codecWireTypeToProto x.wt) x.msg x.bs 98).toOption =
                (mergeLoopBin V1State.Unchunked.EkSentCt1Received.mergeField (rest'.length - limit) { m with dk := v } rest' limit 97).map
                  (fun m' => (m', x.bs.drop (x.bs.length - limit))) := by
              simp only [hres_cur, hloop_ok, hmb, Option.map_some]
            exact ih { m with dk := v } rest' s'' (by omega) (by omega)
              (suffix_trans hrest_le hrest_suf hrest'_le_rest (mergeBytes_suffix hmb))
              hres_next hpc'' hrun'' hsp'' htr'' hx19'' hx20'' hx21'' hx22'' hx23'' hcs'' hinv''
          · by_cases htag4 : key.toNat / 8 = 4
            · rw [htag4] at hx1' hloop_ok; rw [unchunkedEkSentCt1Received_mergeField_tag4] at hloop_ok
              refine SepWPp.of_sepWP_lscro (mid := (blkPl_311).base + 292#64) hinv' ?_; wp_steps; wp_reach; intro hinv_t
              have hnone_mb : mergeBytes iwt rest = none →
                  (Proto.mergeMessage V1State.Unchunked.EkSentCt1Received.mergeField (codecWireTypeToProto x.wt) x.msg x.bs 98).toOption = none := by
                intro hmb; simp only [hres_cur, hloop_ok, hmb, Option.map_none]
              refine htag4_step hsp_align hrest_le hrest_lt hrest_suf hnone_mb
                (fun v rest' s'' hmb hpc'' hrun'' hsp'' htr'' hx19'' hx20'' hx21'' hx22'' hx23'' hcs'' hinv'' => ?_)
                (by simp only [arm64_norm]) (by simp only [arm64_norm, hrun']) (by simp only [arm64_norm, hsp']) (by simp only [arm64_norm, htr'])
                (by simp only [arm64_norm, hx0']) (by simp only [arm64_norm, hx19']) (by simp only [arm64_norm, hx20'])
                (by simp only [arm64_norm, hx21']) (by simp only [arm64_norm, hx22']) (by simp only [arm64_norm, hx23'])
                ⟨by simp only [arm64_norm, hx24'], by simp only [arm64_norm, hx25'],
                 by simp only [arm64_norm, hx26'], by simp only [arm64_norm, hx27'],
                 by simp only [arm64_norm, hx28'], by simp only [arm64_norm, hvregs']⟩ hinv_t
              have hrest'_le_rest : rest'.length ≤ rest.length := mergeBytes_length hmb
              have hres_next : (Proto.mergeMessage V1State.Unchunked.EkSentCt1Received.mergeField (codecWireTypeToProto x.wt) x.msg x.bs 98).toOption =
                  (mergeLoopBin V1State.Unchunked.EkSentCt1Received.mergeField (rest'.length - limit) { m with ct1 := v } rest' limit 97).map
                    (fun m' => (m', x.bs.drop (x.bs.length - limit))) := by
                simp only [hres_cur, hloop_ok, hmb, Option.map_some]
              exact ih { m with ct1 := v } rest' s'' (by omega) (by omega)
                (suffix_trans hrest_le hrest_suf hrest'_le_rest (mergeBytes_suffix hmb))
                hres_next hpc'' hrun'' hsp'' htr'' hx19'' hx20'' hx21'' hx22'' hx23'' hcs'' hinv''
            · have hitag_lt : key.toNat / 8 < 2 ^ 32 := by omega
              have hitag_lt29 : key.toNat / 8 < 2 ^ 29 := by omega
              obtain ⟨hgt2_1, hgt2_2, hgt2_3, hgt2_4⟩ := tag_gt_two_branch (by omega : 2 < key.toNat / 8) hitag_lt29
              obtain ⟨hb3_1, _⟩ := itag_beq_tag_false htag3 hitag_lt (by decide : 3 < 2 ^ 32)
              obtain ⟨hb4_1, _⟩ := itag_beq_tag_false htag4 hitag_lt (by decide : 4 < 2 ^ 32)
              have hb3_2 : (BitVec.truncate 32 (BitVec.ofNat 64 (key.toNat / 8)) == 3#32) = false := by rw [sf_truncate32_ofNat64]; exact hb3_1
              have hb4_2 : (BitVec.truncate 32 (BitVec.ofNat 64 (key.toNat / 8)) == 4#32) = false := by rw [sf_truncate32_ofNat64]; exact hb4_1
              have hb4_bne1 : (BitVec.ofNat 32 (key.toNat / 8) != 4#32) = true := by simp only [bne, hb4_1, Bool.not_false]
              have hb4_bne2 : (BitVec.truncate 32 (BitVec.ofNat 64 (key.toNat / 8)) != 4#32) = true := by simp only [bne, hb4_2, Bool.not_false]
              rw [unchunkedEkSentCt1Received_mergeField_other m iwt rest 97 hitag_lt htag1 htag2 htag3 htag4] at hloop_ok
              refine SepWPp.of_sepWP_lscro (mid := (blkPl_311).base + 316#64) hinv' ?_; wp_steps; wp_reach; intro hinv_t
              have hnone_sf : skipField (2 * rest.length + 2) 97 (key.toNat / 8) iwt rest = none →
                  (Proto.mergeMessage V1State.Unchunked.EkSentCt1Received.mergeField (codecWireTypeToProto x.wt) x.msg x.bs 98).toOption = none := by
                intro hsf; rw [hres_cur, hloop_ok, hsf]; rfl
              refine hskip_step hsp_align hrest_le hrest_lt hrest_suf hitag_lt hnone_sf
                (fun rest' s'' hsf hpc'' hrun'' hsp'' htr'' hx19'' hx20'' hx21'' hx22'' hx23'' hcs'' hinv'' => ?_)
                (by simp only [arm64_norm]) (by simp only [arm64_norm, hrun']) (by simp only [arm64_norm, hsp']) (by simp only [arm64_norm, htr'])
                (by simp only [arm64_norm, hx0']) (by simp only [arm64_norm, hx1', sf_truncate32_ofNat64])
                (by simp only [arm64_norm, hx19']) (by simp only [arm64_norm, hx20'])
                (by simp only [arm64_norm, hx21']) (by simp only [arm64_norm, hx22']) (by simp only [arm64_norm, hx23'])
                ⟨by simp only [arm64_norm, hx24'], by simp only [arm64_norm, hx25'],
                 by simp only [arm64_norm, hx26'], by simp only [arm64_norm, hx27'],
                 by simp only [arm64_norm, hx28'], by simp only [arm64_norm, hvregs']⟩ hinv_t
              have hrest'_le_rest : rest'.length ≤ rest.length := (skip_length (2 * rest.length + 2)).1 _ _ _ _ _ hsf
              have hres_next : (Proto.mergeMessage V1State.Unchunked.EkSentCt1Received.mergeField (codecWireTypeToProto x.wt) x.msg x.bs 98).toOption =
                  (mergeLoopBin V1State.Unchunked.EkSentCt1Received.mergeField (rest'.length - limit) m rest' limit 97).map
                    (fun m' => (m', x.bs.drop (x.bs.length - limit))) := by
                rw [hres_cur, hloop_ok, hsf]; rfl
              exact ih m rest' s'' (by omega) (by omega)
                (suffix_trans hrest_le hrest_suf hrest'_le_rest ((skip_suffix (2 * rest.length + 2)).1 _ _ _ _ _ hsf))
                hres_next hpc'' hrun'' hsp'' htr'' hx19'' hx20'' hx21'' hx22'' hx23'' hcs'' hinv''

theorem unchunkedEkSentCt1ReceivedMerge_own_placed_ok_of_contracts [LibsignalPlacement] {A : RustAlloc}
    {H : String → Option (State → State)}
    (hFromCall : subroutine_ok ((blkPC_311).rebase (blkPl_311).base H) (lsmpl.base 261) (decodeErrorFromSpec A))
    (hPushCall : subroutine_ok ((blkPC_311).rebase (blkPl_311).base H) (lsmpl.base 257) (decodeErrorPushSpec A))
    (hVarintCall : subroutine_ok ((blkPC_311).rebase (blkPl_311).base H) (lsmpl.base 291) (decodeVarint2Spec A))
    (hSkipCall : subroutine_ok ((blkPC_311).rebase (blkPl_311).base H) (lsmpl.base 263) (skipField3Spec A))
    (hBytesCall : subroutine_ok ((blkPC_311).rebase (blkPl_311).base H) (lsmpl.base 290) (withLsCodeRoLoaded lsmpl (bytesMerge3RawSpec A)))
    (hAuthCall : subroutine_ok ((blkPC_311).rebase (blkPl_311).base H) (lsmpl.base 295) (withLsCodeRoLoaded lsmpl (authMergeSpec A))) :
    subroutine_ok ((blkPC_311).rebase (blkPl_311).base H)
      (blkPl_311).base
      (withLsCodeRoLoaded lsmpl (unchunkedEkSentCt1ReceivedMergeOwnSpec A)) := by
  apply subroutine_ok_withLsCodeRoLoaded_of_withLscroProp
  unfold withLscroProp unchunkedEkSentCt1ReceivedMergeOwnSpec
  wpp_init x s0
  replace hpc : s0.pc = (blkPl_311).base := hpc
  conv => arg 6; ext sf P_f; simp only [unchunkedEkSentCt1ReceivedMergeOwnSpec, sepConj_assoc, satisfies_pure_sepConj]
  change SepWPp _ _ _ _ (WppPost (unchunkedEkSentCt1ReceivedMergeOwnSpec A) x R s0) (WppPanic R s0)
  apply SepWPp.elim_lscroProp; intro hinv0
  have herr0_exit := @ekSent_err0_ret_exit_placed _ A H x R s0
  have hfrom_exit := @ekSent_from_err_exit_placed _ A H hFromCall x R s0
  have hloop := fun {limit n m cur s} hlim_lt =>
    @ekSent_loop_ok_placed _ A H hFromCall hPushCall hVarintCall hSkipCall hBytesCall hAuthCall x R s0 limit hsp_align h hlim_lt n m cur s
  by_cases hwt_ld : x.wt = .lengthDelimited
  · have h_1' : (s0.readReg64 (Reg.gpr 0#5)).setWidth 8 = 2#8 := by rw [h_1, hwt_ld]; rfl
    have hbeq := wt_beq_two_of_lengthDelimited h_1'
    have hbne1 : (BitVec.truncate 32 (s0.readReg64 (Reg.gpr 0#5)) &&& 255#32 != 2#32) = false := by simp only [bne, hbeq, Bool.not_true]
    have hbne2 : (BitVec.truncate 32 (BitVec.zeroExtend 64 (BitVec.truncate 32 (s0.readReg64 (Reg.gpr 0#5))) &&& 255#64) != 2#32) = false := by
      rw [BytesMergeFacts.truncate32_zeroExtend64_and_255_eq, h_1']; decide
    have hbne3 : (BitVec.truncate 32 (BitVec.zeroExtend 64 (BitVec.truncate 32 (s0.readReg64 (Reg.gpr 0#5)) &&& 255#32)) != 2#32) = false := by
      revert h_1'; bv_bits
    refine SepWPp.of_sepWP_lscro (mid := lsmpl.base 291) hinv0 ?_
    (conv => arg 4; rw [stackAt_unchunkedMerge s0.sp, unchunkedMergeBelow_leaf s0.sp]; simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc])
    apply SepWP.exists_elim; intro v29; apply SepWP.exists_elim; intro v30; apply SepWP.exists_elim; intro v23
    apply SepWP.exists_elim; intro v22; apply SepWP.exists_elim; intro v21; apply SepWP.exists_elim; intro v20; apply SepWP.exists_elim; intro v19
    wp_steps; wp_reach; intro hinv_c
    refine SepWPp.call_frame_keep_lscro (hinv := hinv_c) (x := ⟨x.bufRef, x.slot, x.ptr, x.bs⟩)
      (ret_pc := (blkPl_311).base + 52#64) hVarintCall (by simp only [arm64_norm]) (by simp only [arm64_norm, hrun])
      (by simp only [State.spAligned, arm64_norm]; exact hsp_align) (by simp only [arm64_norm])
      (by dsimp only [decodeVarint2Spec]; simp only [arm64_norm, h_3]; rfl) h (by sep_focus)
      (fun _ _ _ _ hex => allowPanic_not_exited hex) (fun sf _ hpan => allowPanic_frame' (by simp only [arm64_norm]) hpan) ?_
    intro sm hpcm hrunm hspm hcsm hinv_m; simp only [CalleeSavedPreserved] at hcsm
    obtain ⟨hx19_m, hx20_m, hx21_m, hx22_m, hx23_m, hx24_m, hx25_m, hx26_m, hx27_m, hx28_m, hfp_m, hvregs_m⟩ := hcsm
    simp (config := { decide := true }) only [arm64_norm, h_2, h_3] at hpcm hrunm hspm hx19_m hx20_m hx21_m hx22_m hx23_m hx24_m hx25_m hx26_m hx27_m hx28_m hfp_m hvregs_m
    cases hdv0 : decodeVarint x.bs with
    | none =>
      have hnone : (Proto.mergeMessage V1State.Unchunked.EkSentCt1Received.mergeField (codecWireTypeToProto x.wt) x.msg x.bs 98).toOption = none := by
        rw [hwt_ld, ← mergeMessageBin_eq_proto_mergeMessage protoPrefixStep_unchunked_ekSentCt1Received_mergeField]
        simp [mergeMessageBin, codecWireTypeToProto, proto_decodeVarint_toOption, hdv0]
      apply SepWPp.of_sepWP (mid := (blkPl_311).base + 120#64)
      (conv => arg 4; simp only [decodeVarint2Spec, hdv0, sepConj_assoc, arm64_norm]); apply SepWP.pure_elim; rintro ⟨hsm0, htrm, hsm1⟩
      apply SepWP.fold (unchunkedMergeBelow_leaf_entails s0.sp) (by sep_focus)
      apply SepWP.fold (protoUnchunkedEkSentCt1ReceivedCapAt_entails_exists A x.msgPtr x.bs.length x.msg) (by sep_focus)
      wp_steps; wp_reach
      apply SepWPp.weaken_pre (P' := decodeErrorAtStackLen A (sm.readReg64 (Reg.gpr 1#5)) 0 ∗ memRegion (s0.sp - 112#64) 48 ∗ unchunkedMergeBelow s0.sp ∗ ekSentErrFrame A s0 x.msgPtr x.bufRef x.slot x.ptr x.bs) (by dsimp only [ekSentErrFrame]; sep_entail)
      exact herr0_exit hnone hsp_align
        (by simp only [arm64_norm]) (by simp only [arm64_norm, hrunm]) (by simp only [arm64_norm, hspm]) (by simp only [arm64_norm, htrm])
        (by simp only [arm64_norm]) hsm1
        ⟨by simp only [arm64_norm, hx24_m], by simp only [arm64_norm, hx25_m], by simp only [arm64_norm, hx26_m], by simp only [arm64_norm, hx27_m], by simp only [arm64_norm, hx28_m], by simp only [arm64_norm, hvregs_m]⟩
    | some p =>
      rcases p with ⟨len, rest0⟩
      have hrest0_lt_bs : rest0.length < x.bs.length := decodeVarint_length hdv0; have hrest0_le : rest0.length ≤ x.bs.length := Nat.le_of_lt hrest0_lt_bs
      have hrest0_lt : rest0.length < 2 ^ 63 := Nat.lt_of_lt_of_le hrest0_lt_bs (Nat.le_of_lt h)
      have hrest0_suf : IsDropSuffix x.bs rest0 := decodeVarint_suffix hdv0
      let rest0Ptr : BitVec 64 := x.ptr + BitVec.ofNat 64 (x.bs.length - rest0.length)
      by_cases hlt_len : rest0.length < len.toNat
      · have hule := ule_len_of_lt hlt_len hrest0_lt
        have hnone : (Proto.mergeMessage V1State.Unchunked.EkSentCt1Received.mergeField (codecWireTypeToProto x.wt) x.msg x.bs 98).toOption = none := by
          rw [hwt_ld, ← mergeMessageBin_eq_proto_mergeMessage protoPrefixStep_unchunked_ekSentCt1Received_mergeField]
          simp [mergeMessageBin, codecWireTypeToProto, proto_decodeVarint_toOption, hdv0, hlt_len]
        apply SepWPp.of_sepWP (mid := (blkPl_311).base + 108#64)
        (conv => arg 4; simp only [decodeVarint2Spec, hdv0, sepConj_assoc, arm64_norm]); apply SepWP.pure_elim; rintro ⟨⟨hsm0, hsm1⟩, htrm⟩
        apply SepWP.fold (unchunkedMergeBelow_leaf_entails s0.sp) (by sep_focus)
        (conv => arg 4; rw [sliceCursorAfter_eq_split hrest0_le hrest0_suf, sliceCursorAt, memRegion_48_split_112 s0.sp]; simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc])
        apply SepWP.exists_elim; intro v_stk0; wp_steps
        apply SepWP.fold (protoUnchunkedEkSentCt1ReceivedCapAt_entails_exists A x.msgPtr x.bs.length x.msg) (by sep_focus)
        apply SepWP.fold (pointsTo64_pair_entails_memRegion16 x.slot rest0Ptr (BitVec.ofNat 64 rest0.length)) (by sep_focus)
        apply SepWP.fold (pointsToBytes_prefix_join hrest0_le hrest0_suf) (by sep_focus); wp_reach
        apply SepWPp.weaken_pre (P' := ((s0.sp - 112#64) ↦₆₄ 0x8000000000000007#64) ∗ memRegion (s0.sp - 104#64) 40 ∗ unchunkedMergeBelow s0.sp ∗ ekSentErrFrame A s0 x.msgPtr x.bufRef x.slot x.ptr x.bs) (by dsimp only [ekSentErrFrame]; sep_entail)
        exact hfrom_exit hnone (by decide : KindNoHeap 0x8000000000000007#64) hsp_align
          (by simp only [arm64_norm]) (by simp only [arm64_norm, hrunm]) (by simp only [arm64_norm, hspm]) (by simp only [arm64_norm, htrm])
          ⟨by simp only [arm64_norm, hx24_m], by simp only [arm64_norm, hx25_m], by simp only [arm64_norm, hx26_m], by simp only [arm64_norm, hx27_m], by simp only [arm64_norm, hx28_m], by simp only [arm64_norm, hvregs_m]⟩
      · have hule := ule_len_of_ge hlt_len hrest0_lt; have hsub := bv_len_sub_limit hlt_len; have hlim_lt : rest0.length - len.toNat < 2 ^ 63 := by omega
        have hdrop_eq : x.bs.drop (x.bs.length - (rest0.length - len.toNat)) = rest0.drop len.toNat := by
          have hsuf := hrest0_suf; unfold IsDropSuffix at hsuf; conv => rhs; rw [hsuf, List.drop_drop]
          exact congrArg (List.drop · x.bs) (by omega)
        have hres0 : (Proto.mergeMessage V1State.Unchunked.EkSentCt1Received.mergeField (codecWireTypeToProto x.wt) x.msg x.bs 98).toOption =
            (mergeLoopBin V1State.Unchunked.EkSentCt1Received.mergeField (rest0.length - (rest0.length - len.toNat)) x.msg rest0 (rest0.length - len.toNat) 97).map
              (fun m' => (m', x.bs.drop (x.bs.length - (rest0.length - len.toNat)))) := by
          rw [hwt_ld, ← mergeMessageBin_eq_proto_mergeMessage protoPrefixStep_unchunked_ekSentCt1Received_mergeField]
          simp only [mergeMessageBin, codecWireTypeToProto, bne_self_eq_false, Bool.false_eq_true, ↓reduceIte, proto_decodeVarint_toOption, hdv0, hlt_len, hdrop_eq]
          rcases mergeLoopBin V1State.Unchunked.EkSentCt1Received.mergeField (rest0.length - (rest0.length - len.toNat)) x.msg rest0 (rest0.length - len.toNat) 97 with _ | m' <;> rfl
        refine SepWPp.of_sepWP_lscro (mid := (blkPl_311).base + 152#64) hinv_m ?_
        (conv => arg 4; simp only [decodeVarint2Spec, hdv0, sepConj_assoc, arm64_norm]); apply SepWP.pure_elim; rintro ⟨⟨hsm0, hsm1⟩, htrm⟩
        apply SepWP.fold (unchunkedMergeBelow_leaf_entails s0.sp) (by sep_focus)
        apply SepWP.fold (protoUnchunkedEkSentCt1ReceivedCapAt_mono A x.msgPtr x.msg hrest0_le) (by sep_focus)
        (conv => arg 4; rw [sliceCursorAfter_eq_split hrest0_le hrest0_suf, sliceCursorAt]; simp only [sepConj_assoc]); wp_steps; wp_reach; intro hinv_l
        apply SepWPp.weaken_pre (P' := ekSentLoopPre A s0 x.msgPtr x.bufRef x.slot x.ptr x.msg x.bs rest0) (by rw [ekSentLoopPre, sliceCursorAfter_eq_split hrest0_le hrest0_suf, sliceCursorAt]; sep_entail)
        exact hloop hlim_lt (Nat.le_refl _) hrest0_le hrest0_suf hres0
          (by simp only [arm64_norm]) (by simp only [arm64_norm, hrunm]) (by simp only [arm64_norm, hspm]) (by simp only [arm64_norm, htrm])
          (by simp only [arm64_norm, hx19_m]) (by simp only [arm64_norm, hx20_m]) (by simp only [arm64_norm])
          (by simp only [arm64_norm, hsm1, hsub]) (by simp only [arm64_norm])
          ⟨by simp only [arm64_norm, hx24_m], by simp only [arm64_norm, hx25_m], by simp only [arm64_norm, hx26_m], by simp only [arm64_norm, hx27_m], by simp only [arm64_norm, hx28_m], by simp only [arm64_norm, hvregs_m]⟩ hinv_l
  · have hbeq := wt_beq_two_of_ne_lengthDelimited h_1 hwt_ld
    have hbne1 : (BitVec.truncate 32 (s0.readReg64 (Reg.gpr 0#5)) &&& 255#32 != 2#32) = true := by simp only [bne, hbeq, Bool.not_false]
    have hbne2 : (BitVec.truncate 32 (BitVec.zeroExtend 64 (BitVec.truncate 32 (s0.readReg64 (Reg.gpr 0#5))) &&& 255#64) != 2#32) = true := by
      rw [BytesMergeFacts.truncate32_zeroExtend64_and_255_eq, h_1]; cases hxwt : x.wt <;> first | exact absurd hxwt hwt_ld | decide
    have hbne3 : (BitVec.truncate 32 (BitVec.zeroExtend 64 (BitVec.truncate 32 (s0.readReg64 (Reg.gpr 0#5)) &&& 255#32)) != 2#32) = true := by
      rw [← hbne1]; congr 2; bv_bits
    have hnone : (Proto.mergeMessage V1State.Unchunked.EkSentCt1Received.mergeField (codecWireTypeToProto x.wt) x.msg x.bs 98).toOption = none := by
      rw [← mergeMessageBin_eq_proto_mergeMessage protoPrefixStep_unchunked_ekSentCt1Received_mergeField]
      cases hxwt : x.wt <;> first | exact absurd hxwt hwt_ld | rfl
    apply SepWPp.of_sepWP (mid := (blkPl_311).base + 108#64)
    (conv => arg 4; rw [stackAt_unchunkedMerge s0.sp, sliceCursorAt, memRegion_48_wtErr112 s0.sp]; simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc])
    apply SepWP.exists_elim; intro v29; apply SepWP.exists_elim; intro v30; apply SepWP.exists_elim; intro v23
    apply SepWP.exists_elim; intro v22; apply SepWP.exists_elim; intro v21; apply SepWP.exists_elim; intro v20; apply SepWP.exists_elim; intro v19
    apply SepWP.exists_elim; intro b_wt1; apply SepWP.exists_elim; intro b_wt0; apply SepWP.exists_elim; intro v_wt0; wp_steps
    apply SepWP.fold (wtErr112_entails_memRegion40 s0.sp _ _) (by sep_focus)
    apply SepWP.fold (pointsTo64_pair_entails_memRegion16 x.slot x.ptr (BitVec.ofNat 64 x.bs.length)) (by sep_focus)
    apply SepWP.fold (protoUnchunkedEkSentCt1ReceivedCapAt_entails_exists A x.msgPtr x.bs.length x.msg) (by sep_focus); wp_reach
    apply SepWPp.weaken_pre (P' := ((s0.sp - 112#64) ↦₆₄ 0x8000000000000006#64) ∗ memRegion (s0.sp - 104#64) 40 ∗ unchunkedMergeBelow s0.sp ∗ ekSentErrFrame A s0 x.msgPtr x.bufRef x.slot x.ptr x.bs) (by dsimp only [ekSentErrFrame]; sep_entail)
    exact hfrom_exit hnone (by decide : KindNoHeap 0x8000000000000006#64) hsp_align
      (by simp only [arm64_norm]) (by simp only [arm64_norm, hrun]) (by simp only [arm64_norm]) (by simp only [arm64_norm])
      ⟨by simp only [arm64_norm], by simp only [arm64_norm], by simp only [arm64_norm], by simp only [arm64_norm], by simp only [arm64_norm]⟩

theorem unchunkedEkSentCt1ReceivedMerge_placed_ok_of_contracts [LibsignalPlacement] {A : RustAlloc}
    {H : String → Option (State → State)}
    (hFromCall : subroutine_ok ((blkPC_311).rebase (blkPl_311).base H) (lsmpl.base 261) (decodeErrorFromSpec A))
    (hPushCall : subroutine_ok ((blkPC_311).rebase (blkPl_311).base H) (lsmpl.base 257) (decodeErrorPushSpec A))
    (hVarintCall : subroutine_ok ((blkPC_311).rebase (blkPl_311).base H) (lsmpl.base 291) (decodeVarint2Spec A))
    (hSkipCall : subroutine_ok ((blkPC_311).rebase (blkPl_311).base H) (lsmpl.base 263) (skipField3Spec A))
    (hBytesCall : subroutine_ok ((blkPC_311).rebase (blkPl_311).base H) (lsmpl.base 290) (withLsCodeRoLoaded lsmpl (bytesMerge3RawSpec A)))
    (hAuthCall : subroutine_ok ((blkPC_311).rebase (blkPl_311).base H) (lsmpl.base 295) (withLsCodeRoLoaded lsmpl (authMergeSpec A))) :
    subroutine_ok ((blkPC_311).rebase (blkPl_311).base H)
      (blkPl_311).base
      (withLsCodeRoLoaded lsmpl (unchunkedEkSentCt1ReceivedMergeSpec A)) := by
  apply subroutine_ok_unchunkedEkSentCt1ReceivedMerge_of_own_placed
  exact unchunkedEkSentCt1ReceivedMerge_own_placed_ok_of_contracts
    hFromCall hPushCall hVarintCall hSkipCall hBytesCall hAuthCall

end CryptoVerification.SpqrV1.Prost.MessageMerge
