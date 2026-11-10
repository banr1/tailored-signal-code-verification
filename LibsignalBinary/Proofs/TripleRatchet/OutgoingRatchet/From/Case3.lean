/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.TripleRatchet.OutgoingRatchet.From.Frame
import all Init.Data.String.Defs
import GeneratedLean.LibsignalSessionCode -- shake: keep
import LibsignalBinary.Proofs.Common.CallInv
import LibsignalBinary.Proofs.FnOffEq
import LibsignalBinary.Proofs.TripleRatchet.InImageCallees.InImageCalleesCodeSym
import ProofLib.SepLogic.WPp

/-!
# `OutgoingTripleRatchet::from_session_state` Case 3 (`st.remoteIdentity = none`)

Verifies the `missingRemoteIdentity` error branch (`st.remoteIdentity = none`) of
`<OutgoingTripleRatchet>::from_session_state`.
-/

@[expose] public section

namespace CryptoVerification.LibsignalTripleRatchet.OutgoingRatchet

open Arm64 ProofLib CryptoGames CryptoGames.HMAC CryptoGames.HKDF
open CryptoGames.Ratchet CryptoGames.LibsignalSession
open CryptoVerification.RustHeap CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchetRepr
open CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalTripleRatchet.Getters
open ProofLib.ProgramReflection

set_option maxRecDepth 200000
set_option maxHeartbeats 400000

attribute [local irreducible] Program.fetch Program.externAt?
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero
  zeroExtend64_setWidth32 zeroExtend64_setWidth16 zeroExtend32_setWidth16
  zeroExtend64_setWidth8 zeroExtend32_setWidth8
  localIk_bytes0_7_low32 localIk_bytes0_7_mid16 localIk_bytes0_7_hi8
  shift40_shift16_eq_shift56

theorem remoteIdentityOkAt_none_split_sp152 (sp : BitVec 64)
    (opt : Option IdentityKey) (h : opt = none) :
    remoteIdentityOkAt (sp - 152#64) opt ⊢
      ((sp - 152#64) ↦₈ 0#8) ∗
      ((sp - 151#64) ↦₈ 0#8) ∗
      (∃∗ m0 : BitVec 32, (sp - 150#64) ↦₃₂ m0) ∗
      (∃∗ m4 : BitVec 16, (sp - 146#64) ↦₁₆ m4) ∗
      (∃∗ m6 : BitVec 64, (sp - 144#64) ↦₆₄ m6) ∗
      (∃∗ m14 : BitVec 64, (sp - 136#64) ↦₆₄ m14) ∗
      (∃∗ m22 : BitVec 64, (sp - 128#64) ↦₆₄ m22) ∗
      (∃∗ m30 : BitVec 16, (sp - 120#64) ↦₁₆ m30) := by
  subst h
  dsimp only [remoteIdentityOkAt]
  rw [sub_add_eq_sub sp 1#64 152#64 151#64,
      sub_add_eq_sub sp 2#64 152#64 150#64]
  have h32 : memRegion (sp - BitVec.ofNat 64 150) 32 =
      (∃∗ m0 : BitVec 32, (sp - 150#64) ↦₃₂ m0) ∗
      (∃∗ m4 : BitVec 16, (sp - 146#64) ↦₁₆ m4) ∗
      (∃∗ m6 : BitVec 64, (sp - 144#64) ↦₆₄ m6) ∗
      (∃∗ m14 : BitVec 64, (sp - 136#64) ↦₆₄ m14) ∗
      (∃∗ m22 : BitVec 64, (sp - 128#64) ↦₆₄ m22) ∗
      (∃∗ m30 : BitVec 16, (sp - 120#64) ↦₁₆ m30) := by
    rw [mr_cut' sp 150 146 4 28 32 rfl rfl (by decide) (by decide) (by decide),
        mr_cut' sp 146 144 2 26 28 rfl rfl (by decide) (by decide) (by decide),
        mr_cut' sp 144 136 8 18 26 rfl rfl (by decide) (by decide) (by decide),
        mr_cut' sp 136 128 8 10 18 rfl rfl (by decide) (by decide) (by decide),
        mr_cut' sp 128 120 8 2 10 rfl rfl (by decide) (by decide) (by decide),
        memRegion_four (sp - BitVec.ofNat 64 150),
        memRegion_two (sp - BitVec.ofNat 64 146),
        memRegion_eight (sp - BitVec.ofNat 64 144),
        memRegion_eight (sp - BitVec.ofNat 64 136),
        memRegion_eight (sp - BitVec.ofNat 64 128),
        memRegion_two (sp - BitVec.ofNat 64 120)]
  rw [h32]
  exact Entails.refl _

theorem sp144_split_br3 (sp p m22 : BitVec 64) :
    (((sp - 144#64) ↦₆₄ p) ∗ ((sp - 136#64) ↦₆₄ 27#64) ∗ ((sp - 128#64) ↦₆₄ m22)) ⊢
      (((sp - 144#64) ↦₃₂ pack32 ((bs22 p 27#64 ((unpack64 m22).take 6)).take 4)) ∗
       ((sp - 140#64) ↦₁₆ pack16 (((bs22 p 27#64 ((unpack64 m22).take 6)).drop 4).take 2)) ∗
       ((sp - 138#64) ↦₆₄ pack64 (((bs22 p 27#64 ((unpack64 m22).take 6)).drop 6).take 8)) ∗
       ((sp - 130#64) ↦₆₄ pack64 ((bs22 p 27#64 ((unpack64 m22).take 6)).drop 14)) ∗
       ((sp - 122#64) ↦ₛ (unpack64 m22).drop 6)) := by
  have hm22 : ((sp - 128#64) ↦₆₄ m22) =
      ((sp - 128#64) ↦ₛ (unpack64 m22).take 6) ∗ ((sp - 122#64) ↦ₛ (unpack64 m22).drop 6) := by
    rw [pointsTo64_eq_pointsToBytes,
        pointsToBytes_cut (sp - 128#64) (sp - 122#64) (unpack64 m22) 6 (by simp) (by bv_lin)]
  have h22 := twentyTwoBytes_eq_4_2_8_8 (sp - 144#64) p 27#64 ((unpack64 m22).take 6) (by simp)
  rw [sub_add_eq_sub sp 8#64 144#64 136#64,
      sub_add_eq_sub sp 16#64 144#64 128#64,
      sub_add_eq_sub sp 4#64 144#64 140#64,
      sub_add_eq_sub sp 6#64 144#64 138#64,
      sub_add_eq_sub sp 14#64 144#64 130#64] at h22
  have hgrp :
      (((sp - 144#64) ↦₆₄ p) ∗ ((sp - 136#64) ↦₆₄ 27#64) ∗
        (((sp - 128#64) ↦ₛ (unpack64 m22).take 6) ∗ ((sp - 122#64) ↦ₛ (unpack64 m22).drop 6))) =
      (((sp - 144#64) ↦₆₄ p) ∗ ((sp - 136#64) ↦₆₄ 27#64) ∗
        ((sp - 128#64) ↦ₛ (unpack64 m22).take 6)) ∗ ((sp - 122#64) ↦ₛ (unpack64 m22).drop 6) := by
    ac_rfl
  rw [hm22, hgrp, h22]
  simp only [sepConj_assoc]
  exact Entails.refl _

theorem ret16_fold_br3 (ret p m22 : BitVec 64)
    (v16 : BitVec 32) (v20 : BitVec 16) (w22 w30 : BitVec 64)
    (hv16 : v16 = pack32 ((bs22 p 27#64 ((unpack64 m22).take 6)).take 4))
    (hv20 : v20 = pack16 (((bs22 p 27#64 ((unpack64 m22).take 6)).drop 4).take 2))
    (hw22 : w22 = pack64 (((bs22 p 27#64 ((unpack64 m22).take 6)).drop 6).take 8))
    (hw30 : w30 = pack64 ((bs22 p 27#64 ((unpack64 m22).take 6)).drop 14)) :
    (((ret + 16#64) ↦₃₂ v16) ∗
     ((ret + 20#64) ↦₁₆ v20) ∗
     ((ret + 22#64) ↦₆₄ w22) ∗
     ((ret + 30#64) ↦₆₄ w30) ∗
     memRegion (ret + 38#64) 18) ⊢
    (((ret + 16#64) ↦₆₄ p) ∗ ((ret + 24#64) ↦₆₄ 27#64) ∗ memRegion (ret + 32#64) 24) := by
  rw [hv16, hv20, hw22, hw30]
  have h22 := (twentyTwoBytes_eq_4_2_8_8 (ret + 16#64) p 27#64 ((unpack64 m22).take 6) (by simp)).symm
  simp only [BitVec.add_assoc, BitVec.reduceAdd] at h22
  have hgrp :
      (((ret + 16#64) ↦₃₂ pack32 ((bs22 p 27#64 ((unpack64 m22).take 6)).take 4)) ∗
       ((ret + 20#64) ↦₁₆ pack16 (((bs22 p 27#64 ((unpack64 m22).take 6)).drop 4).take 2)) ∗
       ((ret + 22#64) ↦₆₄ pack64 (((bs22 p 27#64 ((unpack64 m22).take 6)).drop 6).take 8)) ∗
       ((ret + 30#64) ↦₆₄ pack64 ((bs22 p 27#64 ((unpack64 m22).take 6)).drop 14)) ∗
       memRegion (ret + 38#64) 18) =
      (((ret + 16#64) ↦₃₂ pack32 ((bs22 p 27#64 ((unpack64 m22).take 6)).take 4)) ∗
       ((ret + 20#64) ↦₁₆ pack16 (((bs22 p 27#64 ((unpack64 m22).take 6)).drop 4).take 2)) ∗
       ((ret + 22#64) ↦₆₄ pack64 (((bs22 p 27#64 ((unpack64 m22).take 6)).drop 6).take 8)) ∗
       ((ret + 30#64) ↦₆₄ pack64 ((bs22 p 27#64 ((unpack64 m22).take 6)).drop 14))) ∗
      memRegion (ret + 38#64) 18 := by
    ac_rfl
  rw [hgrp, h22]
  simp only [sepConj_assoc]
  refine sepConj_mono_right (sepConj_mono_right ?_)
  have h6 := pointsToBytes_entails_memRegion (ret + 32#64) ((unpack64 m22).take 6)
  have hlen6 : ((unpack64 m22).take 6).length = 6 := by simp
  rw [hlen6] at h6
  rw [mr_cut_add ret 32 6 18 (by decide)]
  exact sepConj_mono h6 (Entails.refl _)

theorem sret_br3_entails_memRegion40 (sp w0 w14 w22 m22 : BitVec 64) (v8 : BitVec 32) (v12 v32 : BitVec 16) :
    (((sp - 152#64) ↦₆₄ w0) ∗
     ((sp - 144#64) ↦₃₂ v8) ∗
     ((sp - 140#64) ↦₁₆ v12) ∗
     ((sp - 138#64) ↦₆₄ w14) ∗
     ((sp - 130#64) ↦₆₄ w22) ∗
     ((sp - 122#64) ↦ₛ (unpack64 m22).drop 6) ∗
     ((sp - 120#64) ↦₁₆ v32) ∗
     memRegion (sp - 118#64) 6) ⊢
    memRegion (sp - 152#64) 40 := by
  rw [mr_cut' sp 152 144 8 32 40 rfl rfl (by decide) (by decide) (by decide),
      mr_cut' sp 144 140 4 28 32 rfl rfl (by decide) (by decide) (by decide),
      mr_cut' sp 140 138 2 26 28 rfl rfl (by decide) (by decide) (by decide),
      mr_cut' sp 138 130 8 18 26 rfl rfl (by decide) (by decide) (by decide),
      mr_cut' sp 130 122 8 10 18 rfl rfl (by decide) (by decide) (by decide),
      mr_cut' sp 122 120 2 8 10 rfl rfl (by decide) (by decide) (by decide),
      mr_cut' sp 120 118 2 6 8 rfl rfl (by decide) (by decide) (by decide)]
  have hd2 : ((sp - 122#64) ↦ₛ (unpack64 m22).drop 6) ⊢ memRegion (sp - 122#64) 2 := by
    have h := pointsToBytes_entails_memRegion (sp - 122#64) ((unpack64 m22).drop 6)
    have hl : ((unpack64 m22).drop 6).length = 2 := by simp
    rwa [hl] at h
  refine sepConj_mono (pointsTo64_entails_memRegion _ w0) (sepConj_mono (pointsTo32_entails_memRegion _ v8) ?_)
  refine sepConj_mono (pointsTo16_entails_memRegion _ v12) (sepConj_mono (pointsTo64_entails_memRegion _ w14) ?_)
  refine sepConj_mono (pointsTo64_entails_memRegion _ w22) (sepConj_mono hd2 ?_)
  exact sepConj_mono (pointsTo16_entails_memRegion _ v32) (Entails.refl _)

private theorem stackAt_deallocX' (sp : BitVec 64) :
    stackAt (sp - 384#64) 65152 =
      stackAt (sp - 16768#64) 48768 ∗ stackAt (sp - 384#64) extHookStack := by
  change memRegion (sp - 384#64 - 65152#64) (48768 + 16384) =
    memRegion (sp - 16768#64 - 48768#64) 48768 ∗ memRegion (sp - 384#64 - 16384#64) 16384
  rw [memRegion_split (sp - 384#64 - 65152#64) 48768 16384 (by decide)]
  have h1 : sp - 384#64 - 65152#64 = sp - 16768#64 - 48768#64 := by bv_lin
  have h2 : sp - 16768#64 - 48768#64 + BitVec.ofNat 64 48768 = sp - 384#64 - 16384#64 := by bv_lin
  rw [h1, h2]

set_option maxHeartbeats 3200000 in
theorem otrFrom_case3_ok_ext_x {img : Obj.Image} {A : RustAlloc}
    {ext : String → Option (State → State)}
    (himg : Obj.Loads libsignalSessionImage img)
    (hA : AllocContractsX img A ext)
    (hDeser : DeserializeExtOk img.base ext)
    (hRemIk : RemoteIdentityKeyExtOk img A ext) :
    subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr otrFromName)
      (otrFromCaseSpec A img
        (fun x => ∃ sc, x.st.senderChain = some sc ∧
          ¬ 256 ≤ x.st.version.toNat ∧ x.st.remoteIdentity = none)) := by
  dsimp only [otrFromCaseSpec, otrFromSpec, Spec.inImage]
  have hbase_align : img.base &&& 0xfff#64 = 0#64 :=
    ProofLib.ObjectLoad.base_aligned_of_loads himg
  have hdeser := deserialize_ok_at_otrFrom_ext hDeser
  have hpkTryFrom := pkTryFromOk_ok_at_ext (ext := ext) himg (name := otrFromName)
    (k := libsignalSessionCode.fnOff pkTryFromName - libsignalSessionCode.fnOff otrFromName)
  have hremIk := remoteIdentityKey_ok_at_otrFrom_ext hRemIk
  have hdealloc := dealloc_ok_at_norm_ext_x hA (name := otrFromName) (k := num% (ls_off% "__rustc::__rust_dealloc" - ls_off% "<libsignal_protocol::triple_ratchet::OutgoingTripleRatchet>::from_session_state"))
    (by rw [(ls_lemma% fnOff "<libsignal_protocol::triple_ratchet::OutgoingTripleRatchet>::from_session_state"), (ls_stub% "__rustc::__rust_dealloc")])
  code_fetches_range libsignalSessionCode CryptoVerification.LibsignalTripleRatchet.OutgoingRatchet.libsignalSessionBin img.base
    (Rust.withPanics ext) (ls_lemma% fnOff "<libsignal_protocol::triple_ratchet::OutgoingTripleRatchet>::from_session_state") (num% (ls_off% "<libsignal_protocol::triple_ratchet::OutgoingTripleRatchet>::from_session_state")) 0 816
  code_fetches_range libsignalSessionCode CryptoVerification.LibsignalTripleRatchet.OutgoingRatchet.libsignalSessionBin img.base
    (Rust.withPanics ext) (ls_lemma% fnOff "<libsignal_protocol::triple_ratchet::OutgoingTripleRatchet>::from_session_state") (num% (ls_off% "<libsignal_protocol::triple_ratchet::OutgoingTripleRatchet>::from_session_state")) 1228 80
  wp_init
  have hadrp3 := fnAddr_adrp_ba80 (b := img.base)
    (H := Rust.withPanics ext) hbase_align
  examples_generalize_entry
  examples_hide_fetches
  obtain ⟨ss, G, st, ret⟩ := a
  dsimp only at *
  rcases h_1 with ⟨sc, hsc, hver, hrem⟩
  apply SepWP.of_sepWP_inv (mid := entry + bv% (1240)) h_2 h_3
  refine SepWP.add_rodata (fun hm => rodata_missingRemoteIdentity_intro himg h_2.roData hm) ?_
  refine SepWP.fold (sessionStateAt_sender_some A ss G st sc hsc) (by sep_focus) ?_
  wp_simp_pre only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
  apply SepWP.exists_elim; intro sg
  refine SepWP.focus_pure (by sep_focus) fun hGs => ?_
  conv =>
    arg 4
    rw [sessionStateAt_eq_from_some_self A ss G st sg sc hGs hsc,
        sessionStateAt_eq_from_some A ss G st sg sc hGs hsc G.pq st.pqRatchetState,
        stackAt_prologue s0.sp,
        frame288_split_phaseA s0.sp,
        memRegion40_split_deser_sp s0.sp,
        ret200_split_br3 ret]
  wp_simp_pre only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
  apply SepWP.exists_elim; intro r11
  apply SepWP.exists_elim; intro r10
  apply SepWP.exists_elim; intro r9
  apply SepWP.exists_elim; intro r8
  apply SepWP.exists_elim; intro r7
  apply SepWP.exists_elim; intro r6
  apply SepWP.exists_elim; intro r5
  apply SepWP.exists_elim; intro r4
  apply SepWP.exists_elim; intro r3
  apply SepWP.exists_elim; intro r2
  apply SepWP.exists_elim; intro r1
  apply SepWP.exists_elim; intro r0
  apply SepWP.exists_elim; intro v_deser
  apply SepWP.exists_elim; intro tag0_deser
  apply SepWP.exists_elim; intro ue0
  apply SepWP.exists_elim; intro ud8
  apply SepWP.exists_elim; intro uc8
  apply SepWP.exists_elim; intro uc0
  apply SepWP.exists_elim; intro u9e
  apply SepWP.exists_elim; intro u9c
  apply SepWP.exists_elim; intro u98
  apply SepWP.exists_elim; intro u90
  apply SepWP.exists_elim; intro u88
  apply SepWP.exists_elim; intro u84
  apply SepWP.exists_elim; intro u80
  apply SepWP.exists_elim; intro w30
  apply SepWP.exists_elim; intro w22
  apply SepWP.exists_elim; intro v20
  apply SepWP.exists_elim; intro v16
  apply SepWP.exists_elim; intro w1
  apply SepWP.exists_elim; intro w0
  refine SepWP.focus_pure (by sep_focus) fun hinv1 => ?_
  refine SepWP.focus_pure (by sep_focus) fun hinv2 => ?_
  obtain ⟨hdeser_lik, hrem_inv, hchains_len, hpend_some, hreg_len, _, _⟩ := id hinv1
  have hrem_inv' : G.remoteIk.bytes = [] := by rwa [hrem] at hrem_inv
  rcases hinv2 with ⟨hdeser_srk, hpriv_eq, hpriv_clamp, hsrk_len⟩
  refine SepWP.fold (vecU8Buf_bounds A G.localIk.cap G.localIk.ptr G.localIk.bytes) (by sep_focus) ?_
  refine SepWP.focus_pure (by sep_focus) fun hlik_bds => ?_
  refine SepWP.fold (vecU8Buf_bounds A sg.srk.cap sg.srk.ptr sg.srk.bytes) (by sep_focus) ?_
  refine SepWP.focus_pure (by sep_focus) fun hsrk_bds => ?_
  refine SepWP.fold (vecU8Buf_bounds A sg.priv.cap sg.priv.ptr sg.priv.bytes) (by sep_focus) ?_
  refine SepWP.focus_pure (by sep_focus) fun hpriv_bds => ?_
  refine SepWP.fold (vecU8Buf_bounds A sg.ck.cap sg.ck.ptr (keyToBytes32 sc.chainKey.key)) (by sep_focus) ?_
  refine SepWP.focus_pure (by sep_focus) fun hck_bds => ?_
  refine SepWP.fold (vecU8Buf_dealloc A G.pq.cap G.pq.ptr st.pqRatchetState) (by sep_focus) ?_
  refine SepWP.focus_pure (by sep_focus) fun hpq_bds => ?_
  obtain ⟨_, hlik_ge33⟩ :=
    CryptoVerification.LibsignalSession.FindReceiverChainIndex.publicKey_deserialize_ok_inversion hdeser_lik
  have hlik_cap_ne0 : G.localIk.cap ≠ 0 :=
    vecU8_cap_ne_zero_of_ge hlik_bds.1 (by omega)
  have hlik_len_lt : G.localIk.bytes.length < 2 ^ 63 :=
    Nat.lt_of_le_of_lt hlik_bds.1 hlik_bds.2.1
  have hlik_len_toNat : (BitVec.ofNat 64 G.localIk.bytes.length).toNat = G.localIk.bytes.length := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  have hlik_pk_len : st.localIdentity.publicKey.bytes.toList.length = 32 :=
    st.localIdentity.publicKey.bytes.toList_length
  obtain ⟨_, hsrk_ge33⟩ :=
    CryptoVerification.LibsignalSession.FindReceiverChainIndex.publicKey_deserialize_ok_inversion hdeser_srk
  have hsrk_cap_ne0 : sg.srk.cap ≠ 0 :=
    vecU8_cap_ne_zero_of_ge hsrk_bds.1 (by omega)
  have hsrk_ne_neg1 : (sg.srk.cap + 1#64 == 0#64) = false :=
    addsPState64_neg1_eq_false hsrk_bds.2.1
  have hsrk_len_lt : sg.srk.bytes.length < 2 ^ 63 :=
    Nat.lt_of_le_of_lt hsrk_bds.1 hsrk_bds.2.1
  have hsrk_len_toNat : (BitVec.ofNat 64 sg.srk.bytes.length).toNat = sg.srk.bytes.length := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  have hpriv_len : sg.priv.bytes.length = 32 := by
    rw [hpriv_eq, List.Vector.toList_length]
  have hpriv_cap_ne0 : sg.priv.cap ≠ 0 :=
    vecU8_cap_ne_zero_of_ge hpriv_bds.1 (by omega)
  have hck_cap_ne0 : sg.ck.cap ≠ 0 := by
    have h1 := hck_bds.1
    rw [keyToBytes32_length] at h1
    exact vecU8_cap_ne_zero_of_ge h1 (by decide)
  have hck_ne_neg1 : (sg.ck.cap + 1#64 == 0#64) = false :=
    addsPState64_neg1_eq_false hck_bds.2.1
  have hv_deser_len : v_deser.toList.length = 32 := v_deser.toList_length
  have hsrk_pk_len : sc.ratchetKey.publicKey.bytes.toList.length = 32 :=
    sc.ratchetKey.publicKey.bytes.toList_length
  have hpriv_pk_len : sc.ratchetKey.privateKey.bytes.toList.length = 32 :=
    sc.ratchetKey.privateKey.bytes.toList_length
  have hck_key_len : (keyToBytes32 sc.chainKey.key).length = 32 :=
    keyToBytes32_length sc.chainKey.key
  have hver_ls :
      ConditionHolds CondCode.LS
        (subsPState32 (if (st.sessionVersion == 0#32) = true then 2#32 else st.sessionVersion) 255#32) =
      true := by
    rw [version_word_eq st, subsPState32_255_ls_iff st.version, decide_eq_true_eq]
    exact hver
  conv =>
    arg 4
    rw [vecU8Buf_eq_bytes_live_of_ne_zero A G.localIk.cap G.localIk.ptr G.localIk.bytes hlik_cap_ne0,
        vecU8Buf_eq_bytes_live_of_ne_zero A sg.srk.cap sg.srk.ptr sg.srk.bytes hsrk_cap_ne0,
        vecU8Buf_eq_bytes_live_of_ne_zero A sg.priv.cap sg.priv.ptr sg.priv.bytes hpriv_cap_ne0,
        vecU8Buf_eq_bytes_live_of_ne_zero A sg.ck.cap sg.ck.ptr (keyToBytes32 sc.chainKey.key) hck_cap_ne0,
        hpriv_eq, hpriv_pk_len,
        bytes32_eq_1_4_2_8_8_8_1 sg.priv.ptr sc.ratchetKey.privateKey.bytes.toList hpriv_pk_len,
        bytes32_eq_4_2_1_8_8_8_1 sg.ck.ptr (keyToBytes32 sc.chainKey.key) hck_key_len]
  dsimp only [logOff]
  wp_steps
  wp_call hdeser (sg.srk.ptr, sg.srk.bytes, sc.ratchetKey.publicKey,
    s0.sp - 152#64, tag0_deser, v_deser.toList)
  refine SepWP.fold (bytes32_split_sp151 s0.sp sc.ratchetKey.publicKey.bytes.toList hsrk_pk_len) (by sep_focus) ?_
  wp_steps
  refine SepWP.fold (sevenBytes_421_to_124_sp151 s0.sp sc.ratchetKey.publicKey.bytes.toList hsrk_pk_len) (by sep_focus) ?_
  wp_steps
  refine SepWP.fold (sevenBytes_after_store_at_0_sp232 s0.sp u9c u9e sc.ratchetKey.publicKey.bytes.toList hsrk_pk_len) (by sep_focus) ?_
  -- Stop before the `sturh` at entry+284: the `memRegion` folds below must run first.
  wp_steps 33
  refine SepWP.fold (sevenBytes_124_to_421_sp232 s0.sp sc.ratchetKey.publicKey.bytes.toList hsrk_pk_len) (by sep_focus) ?_
  refine SepWP.fold (sret_srk_entails_memRegion40 s0.sp _ _ _ _ _ _ _ _) (by sep_focus) ?_
  refine SepWP.fold (memRegion40_split_ck_sp_entails s0.sp) (by sep_focus) ?_
  wp_simp_pre only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
  apply SepWP.exists_elim; intro c3
  apply SepWP.exists_elim; intro c2
  apply SepWP.exists_elim; intro c0
  wp_steps
  refine SepWP.fold (elevenBytes_218_to_821_sp152 s0.sp (keyToBytes32 sc.chainKey.key) hck_key_len) (by sep_focus) ?_
  refine SepWP.fold (ent_of_eq (frame128_split_phaseB s0.sp)) (by sep_focus) ?_
  wp_simp_pre only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
  apply SepWP.exists_elim; intro s78
  apply SepWP.exists_elim; intro s70
  apply SepWP.exists_elim; intro s68
  apply SepWP.exists_elim; intro s64
  apply SepWP.exists_elim; intro s60
  apply SepWP.exists_elim; intro s5c
  apply SepWP.exists_elim; intro s50
  apply SepWP.exists_elim; intro s48
  apply SepWP.exists_elim; intro s40
  apply SepWP.exists_elim; intro s38
  apply SepWP.exists_elim; intro s30
  apply SepWP.exists_elim; intro s2c
  apply SepWP.exists_elim; intro s28
  apply SepWP.exists_elim; intro s24
  apply SepWP.exists_elim; intro s20
  apply SepWP.exists_elim; intro s18
  apply SepWP.exists_elim; intro s10
  apply SepWP.exists_elim; intro s08
  apply SepWP.exists_elim; intro s00
  refine SepWP.fold (ent_of_eq (frame33_split s0.sp)) (by sep_focus) ?_
  wp_simp_pre only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
  apply SepWP.exists_elim; intro ub8
  apply SepWP.exists_elim; intro ub4
  apply SepWP.exists_elim; intro ub0
  apply SepWP.exists_elim; intro ua8
  apply SepWP.exists_elim; intro ua0
  refine SepWP.fold (ent_of_eq (frame15_split s0.sp)) (by sep_focus) ?_
  wp_simp_pre only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
  apply SepWP.exists_elim; intro ud4
  apply SepWP.exists_elim; intro ud0
  apply SepWP.exists_elim; intro uc9
  wp_steps
  refine SepWP.fold (ck_scratch_entails_memRegion40_sp152 s0.sp _ _ _) (by sep_focus) ?_
  wp_call hpkTryFrom (G.localIk.ptr, G.localIk.bytes, st.localIdentity.publicKey, s0.sp - 152#64)
  refine SepWP.fold (bytes32_split_localIk_sp151 s0.sp st.localIdentity.publicKey.bytes.toList hlik_pk_len) (by sep_focus) ?_
  refine SepWP.fold (bytes32_fold_1_4_2_8_8_8_1 sg.priv.ptr sc.ratchetKey.privateKey.bytes.toList hpriv_pk_len) (by sep_focus) ?_
  refine SepWP.fold (vecU8Buf_fold_of_ne_zero A sg.priv.cap sg.priv.ptr sc.ratchetKey.privateKey.bytes.toList hpriv_cap_ne0) (by sep_focus) ?_
  refine SepWP.fold (bytes32_fold_4_2_1_8_8_8_1 sg.ck.ptr (keyToBytes32 sc.chainKey.key) hck_key_len) (by sep_focus) ?_
  refine SepWP.fold (vecU8Buf_fold_of_ne_zero A sg.ck.cap sg.ck.ptr (keyToBytes32 sc.chainKey.key) hck_cap_ne0) (by sep_focus) ?_
  refine SepWP.fold (vecU8Buf_fold_of_ne_zero A sg.srk.cap sg.srk.ptr sg.srk.bytes hsrk_cap_ne0) (by sep_focus) ?_
  refine SepWP.fold (vecU8Buf_fold_of_ne_zero A G.localIk.cap G.localIk.ptr G.localIk.bytes hlik_cap_ne0) (by sep_focus) ?_
  wp_steps
  refine SepWP.fold (sret_localIk_entails_memRegion34_6 s0.sp _ _ _ _ _ _ _ _ _ _ _) (by sep_focus) ?_
  refine SepWP.fold (ent_of_eq (stackAt_remoteIk s0.sp)) (by sep_focus) ?_
  wp_call hremIk ⟨ss, G.remoteIk, st.remoteIdentity, s0.sp - 152#64⟩
  try rw [hsp_sf_2]
  try rw [hsp_sf_1]
  try rw [hsp_sf]
  refine SepWP.fold (ent_of_eq (stackAt_remoteIk s0.sp).symm) (by sep_focus) ?_
  refine SepWP.fold (remoteIdentityOkAt_none_split_sp152 s0.sp st.remoteIdentity hrem) (by sep_focus) ?_
  refine SepWP.fold (sp184_pair8_to_16 s0.sp _ _) (by sep_focus) ?_
  wp_simp_pre only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
  apply SepWP.exists_elim; intro m30
  apply SepWP.exists_elim; intro m22
  apply SepWP.exists_elim; intro m14
  apply SepWP.exists_elim; intro m6
  apply SepWP.exists_elim; intro m4
  apply SepWP.exists_elim; intro m0
  wp_steps
  refine SepWP.fold (pointsTo64_of_1_1_4_2_sp152 s0.sp _ _ _ _) (by sep_focus) ?_
  wp_simp_pre only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
  apply SepWP.exists_elim; intro w152
  wp_steps
  refine SepWP.fold (sp144_split_br3 s0.sp (img.base + bv% (ls_xref% (ls_off% "<libsignal_protocol::triple_ratchet::OutgoingTripleRatchet>::from_session_state" + 748) (ls_off% "<libsignal_protocol::triple_ratchet::OutgoingTripleRatchet>::from_session_state" + 752))) m22) (by sep_focus) ?_
  wp_steps
  have hmod := otrFrom_model_noRemote ⟨ss, G, st, ret⟩ hsc hver hrem
  have hmod1 : (OtrFromGhost.model ⟨ss, G, st, ret⟩).1 =
      .error (.invalidSessionStructure .missingRemoteIdentity) :=
    congrArg Prod.fst hmod
  have hmod2 : (OtrFromGhost.model ⟨ss, G, st, ret⟩).2 = { st with pqRatchetState := [] } :=
    congrArg Prod.snd hmod
  have hnopanic : (.error (.invalidSessionStructure .missingRemoteIdentity) :
      Except SignalProtocolError (OutgoingTripleRatchet (List (BitVec 8)))) ≠ .error .panic := by
    decide
  have hagree : G.AgreeExceptPq { G with pq := ⟨0#64, 1#64⟩ } := rfl
  have hagree' : G.AgreeExceptPq { G with pq := ⟨0#64, 1#64⟩, sender := some sg } :=
    agreeExceptPq_of_sender G ⟨0#64, 1#64⟩ sg hGs
  refine SepWP.fold (sret_br3_entails_memRegion40 s0.sp _ _ _ m22 _ _ _) (by sep_focus) ?_
  refine SepWP.fold (FromSessionStateFacts.frame15_fold_16 s0.sp _ _ _) (by sep_focus) ?_
  refine SepWP.fold (frame33_fold s0.sp _ _ _ _ _) (by sep_focus) ?_
  refine SepWP.fold (frame128_fold_phaseB s0.sp _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) (by sep_focus) ?_
  refine SepWP.fold (frame288_fold_phaseA s0.sp _ _ _ _ _ _ _ _ _ _ _) (by sep_focus) ?_
  apply SepWP.done
    (by simp only [State.pc_setMem, State.pc_setPC])
    (by simp only [State.status_setMem, State.status_setPC, State.status_writeReg64,
      State.status_setPState, hrun_sf_2])
  intro hfrozen_m hsym_m
  have hinv_m : ImgCallInv img _ := ⟨hfrozen_m, hsym_m⟩
  by_cases hpq0 : G.pq.cap = (0 : BitVec 64)
  · -- `G.pq.cap = 0`: skip `__rust_dealloc`
    have hpq_beq : (G.pq.cap == 0#64) = true := beq_iff_eq.mpr hpq0
    rw [ite_eq_left_iff.mpr (fun h => absurd hpq0 h)]
    wp_steps
    try rw [hsp_sf_2]
    try rw [hsp_sf_1]
    try rw [hsp_sf]
    refine FromSessionStateFacts.finish_otrFrom ⟨ss, G, st, ret⟩ { G with pq := ⟨0#64, 1#64⟩ } _ _
      hmod1 hmod2 hnopanic hagree (by wp_done) ?_
    refine FromSessionStateFacts.fold_entails (ret16_fold_br3 ret (img.base + bv% (ls_xref% (ls_off% "<libsignal_protocol::triple_ratchet::OutgoingTripleRatchet>::from_session_state" + 748) (ls_off% "<libsignal_protocol::triple_ratchet::OutgoingTripleRatchet>::from_session_state" + 752))) m22 _ _ _ _ ?_ ?_ ?_ ?_) (by sep_focus) ?_
    · clear * -; bv_kernel
    · clear * -; bv_kernel
    · clear * -; bv_kernel
    · clear * -; bv_kernel
    refine FromSessionStateFacts.fold_entails (otrResultAt_iss_intro A ret (img.base + bv% (ls_xref% (ls_off% "<libsignal_protocol::triple_ratchet::OutgoingTripleRatchet>::from_session_state" + 748) (ls_off% "<libsignal_protocol::triple_ratchet::OutgoingTripleRatchet>::from_session_state" + 752))) 27#64 G.pq .missingRemoteIdentity) (by sep_focus) ?_
    refine FromSessionStateFacts.fold_entails (stackAt_prologue_fold s0.sp _ _ _ _ _ _ _ _ _ _ _ _) (by sep_focus) ?_
    refine FromSessionStateFacts.fold_entails (pq_empty_cells_intro A ss) (by sep_focus) ?_
    refine FromSessionStateFacts.fold_entails (sessionStateAt_from_some_pq_empty_fold A ss G st sg sc hGs hsc hinv1 hdeser_srk hpriv_eq hpriv_clamp hsrk_len) (by sep_focus) ?_
    exact ent_of_eq (by ac_rfl)
  · -- `G.pq.cap ≠ 0`: call `__rust_dealloc`
    have hpq_beq : (G.pq.cap == 0#64) = false := beq_eq_false_iff_ne.mpr hpq0
    have hpq_pos : 0 < G.pq.cap.toNat :=
      Nat.pos_of_ne_zero (fun h0 => hpq0 (BitVec.eq_of_toNat_eq h0))
    have hpow2 : ∃ k, 1 = 2 ^ k := ⟨0, rfl⟩
    have hlay_pq : LayoutOk G.pq.cap.toNat 1 :=
      ⟨hpq_pos, hpow2, by have := hpq_bds.2.1; omega⟩
    rw [ite_eq_right_iff.mpr (fun h => absurd h hpq0)]
    apply SepWP.seq_inImage (mid := entry + bv% (ls_off% "__rustc::__rust_dealloc" - ls_off% "<libsignal_protocol::triple_ratchet::OutgoingTripleRatchet>::from_session_state")) hinv_m
    wp_steps
    refine SepWP.fold (ent_of_eq (stackAt_deallocX' s0.sp)) (by sep_focus) ?_
    apply SepWP.done (by rfl) (by wp_norm_lhs)
    rintro ⟨hF_dealloc, hsym_dealloc⟩
    wp_call hdealloc (G.pq.ptr, G.pq.cap.toNat, 1)
    wp_steps
    try rw [hsp_sf_4]
    try rw [hsp_sf_3]
    try rw [hsp_sf_2]
    try rw [hsp_sf_1]
    try rw [hsp_sf]
    refine FromSessionStateFacts.finish_otrFrom ⟨ss, G, st, ret⟩ { G with pq := ⟨0#64, 1#64⟩ } _ _
      hmod1 hmod2 hnopanic hagree (by wp_done) ?_
    refine FromSessionStateFacts.fold_entails (ent_of_eq (stackAt_deallocX' s0.sp).symm) (by sep_focus) ?_
    refine FromSessionStateFacts.fold_entails (ret16_fold_br3 ret (img.base + bv% (ls_xref% (ls_off% "<libsignal_protocol::triple_ratchet::OutgoingTripleRatchet>::from_session_state" + 748) (ls_off% "<libsignal_protocol::triple_ratchet::OutgoingTripleRatchet>::from_session_state" + 752))) m22 _ _ _ _ ?_ ?_ ?_ ?_) (by sep_focus) ?_
    · clear * -; bv_kernel
    · clear * -; bv_kernel
    · clear * -; bv_kernel
    · clear * -; bv_kernel
    refine FromSessionStateFacts.fold_entails (otrResultAt_iss_intro A ret (img.base + bv% (ls_xref% (ls_off% "<libsignal_protocol::triple_ratchet::OutgoingTripleRatchet>::from_session_state" + 748) (ls_off% "<libsignal_protocol::triple_ratchet::OutgoingTripleRatchet>::from_session_state" + 752))) 27#64 G.pq .missingRemoteIdentity) (by sep_focus) ?_
    refine FromSessionStateFacts.fold_entails (stackAt_prologue_fold s0.sp _ _ _ _ _ _ _ _ _ _ _ _) (by sep_focus) ?_
    refine FromSessionStateFacts.fold_entails (pq_empty_cells_intro A ss) (by sep_focus) ?_
    refine FromSessionStateFacts.fold_entails (sessionStateAt_from_some_pq_empty_fold A ss G st sg sc hGs hsc hinv1 hdeser_srk hpriv_eq hpriv_clamp hsrk_len) (by sep_focus) ?_
    exact ent_of_eq (by ac_rfl)

theorem otrFrom_case3_ok_ext {img : Obj.Image} {A : RustAlloc}
    {ext : String → Option (State → State)}
    (himg : Obj.Loads libsignalSessionImage img)
    (hA : AllocContracts img.base A ext)
    (hDeser : DeserializeExtOk img.base ext)
    (hRemIk : RemoteIdentityKeyExtOk img A ext) :
    subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr otrFromName)
      (otrFromCaseSpec A img
        (fun x => ∃ sc, x.st.senderChain = some sc ∧
          ¬ 256 ≤ x.st.version.toNat ∧ x.st.remoteIdentity = none)) :=
  otrFrom_case3_ok_ext_x himg (AllocContractsX.of_AllocContracts hA) hDeser hRemIk

theorem otrFrom_case3_ok {img : Obj.Image} {C : Crypto} {A : RustAlloc}
    {ctl : BitVec 64} {abs : String → Option (State → State)}
    (himg : Obj.Loads libsignalSessionImage img)
    (hA : AllocHooks A abs)
    (hDeser : DeserializeOk img.base C ctl abs)
    (hRemIk : RemoteIdentityKeyOk img C A ctl abs) :
    subroutine_ok (tripleRatchetProgAt img.base C ctl abs)
      ((tripleRatchetProgAt img.base C ctl abs).fnAddr otrFromName)
      (otrFromCaseSpec A img
        (fun x => ∃ sc, x.st.senderChain = some sc ∧
          ¬ 256 ≤ x.st.version.toNat ∧ x.st.remoteIdentity = none)) :=
  otrFrom_case3_ok_ext himg (AllocContracts.of_tripleRatchetProgAt img.base C A ctl abs hA) hDeser hRemIk

/-! ## Relocatable `[LibsignalPlacement]` Case 3 (`st.remoteIdentity = none`) -/

set_option maxHeartbeats 3200000 in
theorem otrFrom_case3_placed_ok_of_contracts [LibsignalPlacement] {A : RustAlloc}
    {H : String → Option (State → State)}
    (hdealloc : subroutine_ok ((blkPC_19).rebase (blkPl_19).base H)
      (lsρ lsRustDeallocSym) (rustDeallocSpec A))
    (hdeser : subroutine_ok ((blkPC_201).rebase (blkPl_201).base H)
      (blkPl_201).base CryptoVerification.LibsignalSession.FindReceiverChainIndex.deserializePlacedSpec)
    (hremIk : subroutine_ok ((blkPC_29).rebase (blkPl_29).base H)
      (blkPl_29).base (withLsCodeLoaded lsmpl (remoteIdentityKeyPlacedSpec A))) :
    subroutine_ok ((blkPC_19).rebase (blkPl_19).base H) (blkPl_19).base
      (otrFromCasePlacedSpec A
        (fun x => ∃ sc, x.st.senderChain = some sc ∧
          ¬ 256 ≤ x.st.version.toNat ∧ x.st.remoteIdentity = none)) := by
  dsimp only [otrFromCasePlacedSpec, otrFromRawPlacedSpec]
  have hpkTryFrom := pkTryFromOk_placed_ok_at (prog := (blkPC_211).rebase (blkPl_211).base H)
  wp_init
  obtain ⟨ss, G, st, ret⟩ := a
  dsimp only at *
  rcases h_1 with ⟨sc, hsc, hver, hrem⟩
  apply sepWP_seq_lscl h_2 (mid := lsmpl.base 201)
  refine SepWP.add_rodata (fun hm => rodata_missingRemoteIdentity_placed_intro h_3 hm) ?_
  refine SepWP.fold (sessionStateAt_sender_some A ss G st sc hsc) (by sep_focus) ?_
  wp_simp_pre only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
  apply SepWP.exists_elim; intro sg
  refine SepWP.focus_pure (by sep_focus) fun hGs => ?_
  conv =>
    arg 4
    rw [sessionStateAt_eq_from_some_self A ss G st sg sc hGs hsc,
        sessionStateAt_eq_from_some A ss G st sg sc hGs hsc G.pq st.pqRatchetState,
        stackAt_prologue s0.sp,
        frame288_split_phaseA s0.sp,
        memRegion40_split_deser_sp s0.sp,
        ret200_split_br3 ret]
  wp_simp_pre only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
  apply SepWP.exists_elim; intro r11
  apply SepWP.exists_elim; intro r10
  apply SepWP.exists_elim; intro r9
  apply SepWP.exists_elim; intro r8
  apply SepWP.exists_elim; intro r7
  apply SepWP.exists_elim; intro r6
  apply SepWP.exists_elim; intro r5
  apply SepWP.exists_elim; intro r4
  apply SepWP.exists_elim; intro r3
  apply SepWP.exists_elim; intro r2
  apply SepWP.exists_elim; intro r1
  apply SepWP.exists_elim; intro r0
  apply SepWP.exists_elim; intro v_deser
  apply SepWP.exists_elim; intro tag0_deser
  apply SepWP.exists_elim; intro ue0
  apply SepWP.exists_elim; intro ud8
  apply SepWP.exists_elim; intro uc8
  apply SepWP.exists_elim; intro uc0
  apply SepWP.exists_elim; intro u9e
  apply SepWP.exists_elim; intro u9c
  apply SepWP.exists_elim; intro u98
  apply SepWP.exists_elim; intro u90
  apply SepWP.exists_elim; intro u88
  apply SepWP.exists_elim; intro u84
  apply SepWP.exists_elim; intro u80
  apply SepWP.exists_elim; intro w30
  apply SepWP.exists_elim; intro w22
  apply SepWP.exists_elim; intro v20
  apply SepWP.exists_elim; intro v16
  apply SepWP.exists_elim; intro w1
  apply SepWP.exists_elim; intro w0
  refine SepWP.focus_pure (by sep_focus) fun hinv1 => ?_
  refine SepWP.focus_pure (by sep_focus) fun hinv2 => ?_
  obtain ⟨hdeser_lik, hrem_inv, hchains_len, hpend_some, hreg_len, _, _⟩ := id hinv1
  have hrem_inv' : G.remoteIk.bytes = [] := by rwa [hrem] at hrem_inv
  rcases hinv2 with ⟨hdeser_srk, hpriv_eq, hpriv_clamp, hsrk_len⟩
  refine SepWP.fold (vecU8Buf_bounds A G.localIk.cap G.localIk.ptr G.localIk.bytes) (by sep_focus) ?_
  refine SepWP.focus_pure (by sep_focus) fun hlik_bds => ?_
  refine SepWP.fold (vecU8Buf_bounds A sg.srk.cap sg.srk.ptr sg.srk.bytes) (by sep_focus) ?_
  refine SepWP.focus_pure (by sep_focus) fun hsrk_bds => ?_
  refine SepWP.fold (vecU8Buf_bounds A sg.priv.cap sg.priv.ptr sg.priv.bytes) (by sep_focus) ?_
  refine SepWP.focus_pure (by sep_focus) fun hpriv_bds => ?_
  refine SepWP.fold (vecU8Buf_bounds A sg.ck.cap sg.ck.ptr (keyToBytes32 sc.chainKey.key)) (by sep_focus) ?_
  refine SepWP.focus_pure (by sep_focus) fun hck_bds => ?_
  refine SepWP.fold (vecU8Buf_dealloc A G.pq.cap G.pq.ptr st.pqRatchetState) (by sep_focus) ?_
  refine SepWP.focus_pure (by sep_focus) fun hpq_bds => ?_
  obtain ⟨_, hlik_ge33⟩ :=
    CryptoVerification.LibsignalSession.FindReceiverChainIndex.publicKey_deserialize_ok_inversion hdeser_lik
  have hlik_cap_ne0 : G.localIk.cap ≠ 0 :=
    vecU8_cap_ne_zero_of_ge hlik_bds.1 (by omega)
  have hlik_len_lt : G.localIk.bytes.length < 2 ^ 63 :=
    Nat.lt_of_le_of_lt hlik_bds.1 hlik_bds.2.1
  have hlik_len_toNat : (BitVec.ofNat 64 G.localIk.bytes.length).toNat = G.localIk.bytes.length := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  have hlik_pk_len : st.localIdentity.publicKey.bytes.toList.length = 32 :=
    st.localIdentity.publicKey.bytes.toList_length
  obtain ⟨_, hsrk_ge33⟩ :=
    CryptoVerification.LibsignalSession.FindReceiverChainIndex.publicKey_deserialize_ok_inversion hdeser_srk
  have hsrk_cap_ne0 : sg.srk.cap ≠ 0 :=
    vecU8_cap_ne_zero_of_ge hsrk_bds.1 (by omega)
  have hsrk_ne_neg1 : (sg.srk.cap + 1#64 == 0#64) = false :=
    addsPState64_neg1_eq_false hsrk_bds.2.1
  have hsrk_len_lt : sg.srk.bytes.length < 2 ^ 63 :=
    Nat.lt_of_le_of_lt hsrk_bds.1 hsrk_bds.2.1
  have hsrk_len_toNat : (BitVec.ofNat 64 sg.srk.bytes.length).toNat = sg.srk.bytes.length := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  have hpriv_len : sg.priv.bytes.length = 32 := by
    rw [hpriv_eq, List.Vector.toList_length]
  have hpriv_cap_ne0 : sg.priv.cap ≠ 0 :=
    vecU8_cap_ne_zero_of_ge hpriv_bds.1 (by omega)
  have hck_cap_ne0 : sg.ck.cap ≠ 0 := by
    have h1 := hck_bds.1
    rw [keyToBytes32_length] at h1
    exact vecU8_cap_ne_zero_of_ge h1 (by decide)
  have hck_ne_neg1 : (sg.ck.cap + 1#64 == 0#64) = false :=
    addsPState64_neg1_eq_false hck_bds.2.1
  have hv_deser_len : v_deser.toList.length = 32 := v_deser.toList_length
  have hsrk_pk_len : sc.ratchetKey.publicKey.bytes.toList.length = 32 :=
    sc.ratchetKey.publicKey.bytes.toList_length
  have hpriv_pk_len : sc.ratchetKey.privateKey.bytes.toList.length = 32 :=
    sc.ratchetKey.privateKey.bytes.toList_length
  have hck_key_len : (keyToBytes32 sc.chainKey.key).length = 32 :=
    keyToBytes32_length sc.chainKey.key
  have hver_ls :
      ConditionHolds CondCode.LS
        (subsPState32 (if (st.sessionVersion == 0#32) = true then 2#32 else st.sessionVersion) 255#32) =
      true := by
    rw [version_word_eq st, subsPState32_255_ls_iff st.version, decide_eq_true_eq]
    exact hver
  conv =>
    arg 4
    rw [vecU8Buf_eq_bytes_live_of_ne_zero A G.localIk.cap G.localIk.ptr G.localIk.bytes hlik_cap_ne0,
        vecU8Buf_eq_bytes_live_of_ne_zero A sg.srk.cap sg.srk.ptr sg.srk.bytes hsrk_cap_ne0,
        vecU8Buf_eq_bytes_live_of_ne_zero A sg.priv.cap sg.priv.ptr sg.priv.bytes hpriv_cap_ne0,
        vecU8Buf_eq_bytes_live_of_ne_zero A sg.ck.cap sg.ck.ptr (keyToBytes32 sc.chainKey.key) hck_cap_ne0,
        hpriv_eq, hpriv_pk_len,
        bytes32_eq_1_4_2_8_8_8_1 sg.priv.ptr sc.ratchetKey.privateKey.bytes.toList hpriv_pk_len,
        bytes32_eq_4_2_1_8_8_8_1 sg.ck.ptr (keyToBytes32 sc.chainKey.key) hck_key_len]
  wp_steps
  apply SepWP.done (by rfl) (by wp_norm_lhs)
  intro hcl_1
  apply sepWP_seq_lscl hcl_1 (mid := lsmpl.base 211)
  wp_call (lscall_blk (callerProg := (blkPC_19).rebase (blkPl_19).base H) hdeser hcl_1)
    (sg.srk.ptr, sg.srk.bytes, sc.ratchetKey.publicKey,
    s0.sp - 152#64, tag0_deser, v_deser.toList)
  refine SepWP.fold (bytes32_split_sp151 s0.sp sc.ratchetKey.publicKey.bytes.toList hsrk_pk_len) (by sep_focus) ?_
  wp_steps
  refine SepWP.fold (sevenBytes_421_to_124_sp151 s0.sp sc.ratchetKey.publicKey.bytes.toList hsrk_pk_len) (by sep_focus) ?_
  wp_steps
  refine SepWP.fold (sevenBytes_after_store_at_0_sp232 s0.sp u9c u9e sc.ratchetKey.publicKey.bytes.toList hsrk_pk_len) (by sep_focus) ?_
  wp_steps 33
  refine SepWP.fold (sevenBytes_124_to_421_sp232 s0.sp sc.ratchetKey.publicKey.bytes.toList hsrk_pk_len) (by sep_focus) ?_
  refine SepWP.fold (sret_srk_entails_memRegion40 s0.sp _ _ _ _ _ _ _ _) (by sep_focus) ?_
  refine SepWP.fold (memRegion40_split_ck_sp_entails s0.sp) (by sep_focus) ?_
  wp_simp_pre only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
  apply SepWP.exists_elim; intro c3
  apply SepWP.exists_elim; intro c2
  apply SepWP.exists_elim; intro c0
  wp_steps
  refine SepWP.fold (elevenBytes_218_to_821_sp152 s0.sp (keyToBytes32 sc.chainKey.key) hck_key_len) (by sep_focus) ?_
  refine SepWP.fold (ent_of_eq (frame128_split_phaseB s0.sp)) (by sep_focus) ?_
  wp_simp_pre only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
  apply SepWP.exists_elim; intro s78
  apply SepWP.exists_elim; intro s70
  apply SepWP.exists_elim; intro s68
  apply SepWP.exists_elim; intro s64
  apply SepWP.exists_elim; intro s60
  apply SepWP.exists_elim; intro s5c
  apply SepWP.exists_elim; intro s50
  apply SepWP.exists_elim; intro s48
  apply SepWP.exists_elim; intro s40
  apply SepWP.exists_elim; intro s38
  apply SepWP.exists_elim; intro s30
  apply SepWP.exists_elim; intro s2c
  apply SepWP.exists_elim; intro s28
  apply SepWP.exists_elim; intro s24
  apply SepWP.exists_elim; intro s20
  apply SepWP.exists_elim; intro s18
  apply SepWP.exists_elim; intro s10
  apply SepWP.exists_elim; intro s08
  apply SepWP.exists_elim; intro s00
  refine SepWP.fold (ent_of_eq (frame33_split s0.sp)) (by sep_focus) ?_
  wp_simp_pre only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
  apply SepWP.exists_elim; intro ub8
  apply SepWP.exists_elim; intro ub4
  apply SepWP.exists_elim; intro ub0
  apply SepWP.exists_elim; intro ua8
  apply SepWP.exists_elim; intro ua0
  refine SepWP.fold (ent_of_eq (frame15_split s0.sp)) (by sep_focus) ?_
  wp_simp_pre only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
  apply SepWP.exists_elim; intro ud4
  apply SepWP.exists_elim; intro ud0
  apply SepWP.exists_elim; intro uc9
  wp_steps
  refine SepWP.fold (ck_scratch_entails_memRegion40_sp152 s0.sp _ _ _) (by sep_focus) ?_
  apply SepWP.done (by rfl) (by wp_norm_lhs)
  intro hcl_2
  apply sepWP_seq_lscl hcl_2 (mid := lsmpl.base 29)
  wp_call (lscall_blk_cl (callerProg := (blkPC_19).rebase (blkPl_19).base H) (spec := pkTryFromOkPlacedSpec) hpkTryFrom hcl_2)
    (G.localIk.ptr, G.localIk.bytes, st.localIdentity.publicKey, s0.sp - 152#64)
  refine SepWP.fold (bytes32_split_localIk_sp151 s0.sp st.localIdentity.publicKey.bytes.toList hlik_pk_len) (by sep_focus) ?_
  refine SepWP.fold (bytes32_fold_1_4_2_8_8_8_1 sg.priv.ptr sc.ratchetKey.privateKey.bytes.toList hpriv_pk_len) (by sep_focus) ?_
  refine SepWP.fold (vecU8Buf_fold_of_ne_zero A sg.priv.cap sg.priv.ptr sc.ratchetKey.privateKey.bytes.toList hpriv_cap_ne0) (by sep_focus) ?_
  refine SepWP.fold (bytes32_fold_4_2_1_8_8_8_1 sg.ck.ptr (keyToBytes32 sc.chainKey.key) hck_key_len) (by sep_focus) ?_
  refine SepWP.fold (vecU8Buf_fold_of_ne_zero A sg.ck.cap sg.ck.ptr (keyToBytes32 sc.chainKey.key) hck_cap_ne0) (by sep_focus) ?_
  refine SepWP.fold (vecU8Buf_fold_of_ne_zero A sg.srk.cap sg.srk.ptr sg.srk.bytes hsrk_cap_ne0) (by sep_focus) ?_
  refine SepWP.fold (vecU8Buf_fold_of_ne_zero A G.localIk.cap G.localIk.ptr G.localIk.bytes hlik_cap_ne0) (by sep_focus) ?_
  wp_steps
  refine SepWP.fold (sret_localIk_entails_memRegion34_6 s0.sp _ _ _ _ _ _ _ _ _ _ _) (by sep_focus) ?_
  refine SepWP.fold (ent_of_eq (stackAt_remoteIk s0.sp)) (by sep_focus) ?_
  apply SepWP.done (by rfl) (by wp_norm_lhs)
  intro hcl_3
  wp_call (lscall_blk_cl (callerProg := (blkPC_19).rebase (blkPl_19).base H) (spec := remoteIdentityKeyPlacedSpec A) hremIk hcl_3)
    ⟨ss, G.remoteIk, st.remoteIdentity, s0.sp - 152#64⟩
  try rw [hsp_sf_2]
  try rw [hsp_sf_1]
  try rw [hsp_sf]
  refine SepWP.fold (ent_of_eq (stackAt_remoteIk s0.sp).symm) (by sep_focus) ?_
  refine SepWP.fold (remoteIdentityOkAt_none_split_sp152 s0.sp st.remoteIdentity hrem) (by sep_focus) ?_
  refine SepWP.fold (sp184_pair8_to_16 s0.sp _ _) (by sep_focus) ?_
  wp_simp_pre only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
  apply SepWP.exists_elim; intro m30
  apply SepWP.exists_elim; intro m22
  apply SepWP.exists_elim; intro m14
  apply SepWP.exists_elim; intro m6
  apply SepWP.exists_elim; intro m4
  apply SepWP.exists_elim; intro m0
  wp_steps
  refine SepWP.fold (pointsTo64_of_1_1_4_2_sp152 s0.sp _ _ _ _) (by sep_focus) ?_
  wp_simp_pre only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
  apply SepWP.exists_elim; intro w152
  wp_steps
  refine SepWP.fold (sp144_split_br3 s0.sp (lsρ missingRemoteIdentitySym) m22) (by sep_focus) ?_
  wp_steps
  have hmod := otrFrom_model_noRemote ⟨ss, G, st, ret⟩ hsc hver hrem
  have hmod1 : (OtrFromGhost.model ⟨ss, G, st, ret⟩).1 =
      .error (.invalidSessionStructure .missingRemoteIdentity) :=
    congrArg Prod.fst hmod
  have hmod2 : (OtrFromGhost.model ⟨ss, G, st, ret⟩).2 = { st with pqRatchetState := [] } :=
    congrArg Prod.snd hmod
  have hnopanic : (.error (.invalidSessionStructure .missingRemoteIdentity) :
      Except SignalProtocolError (OutgoingTripleRatchet (List (BitVec 8)))) ≠ .error .panic := by
    decide
  have hagree : G.AgreeExceptPq { G with pq := ⟨0#64, 1#64⟩ } := rfl
  have hagree' : G.AgreeExceptPq { G with pq := ⟨0#64, 1#64⟩, sender := some sg } :=
    agreeExceptPq_of_sender G ⟨0#64, 1#64⟩ sg hGs
  refine SepWP.fold (sret_br3_entails_memRegion40 s0.sp _ _ _ m22 _ _ _) (by sep_focus) ?_
  refine SepWP.fold (FromSessionStateFacts.frame15_fold_16 s0.sp _ _ _) (by sep_focus) ?_
  refine SepWP.fold (frame33_fold s0.sp _ _ _ _ _) (by sep_focus) ?_
  refine SepWP.fold (frame128_fold_phaseB s0.sp _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) (by sep_focus) ?_
  refine SepWP.fold (frame288_fold_phaseA s0.sp _ _ _ _ _ _ _ _ _ _ _) (by sep_focus) ?_
  by_cases hpq0 : G.pq.cap = (0 : BitVec 64)
  · have hpq_beq : (G.pq.cap == 0#64) = true := beq_iff_eq.mpr hpq0
    rw [ite_eq_left_iff.mpr (fun h => absurd hpq0 h)]
    wp_steps
    try rw [hsp_sf_2]
    try rw [hsp_sf_1]
    try rw [hsp_sf]
    refine FromSessionStateFacts.finish_otrFrom_placed ⟨ss, G, st, ret⟩ { G with pq := ⟨0#64, 1#64⟩ } _ _
      hmod1 hmod2 hnopanic hagree (by wp_done) ?_
    refine FromSessionStateFacts.fold_entails (ret16_fold_br3 ret (lsρ missingRemoteIdentitySym) m22 _ _ _ _ ?_ ?_ ?_ ?_) (by sep_focus) ?_
    · clear * -; bv_kernel
    · clear * -; bv_kernel
    · clear * -; bv_kernel
    · clear * -; bv_kernel
    refine FromSessionStateFacts.fold_entails (otrResultAt_iss_intro A ret (lsρ missingRemoteIdentitySym) 27#64 G.pq .missingRemoteIdentity) (by sep_focus) ?_
    refine FromSessionStateFacts.fold_entails (stackAt_prologue_fold s0.sp _ _ _ _ _ _ _ _ _ _ _ _) (by sep_focus) ?_
    refine FromSessionStateFacts.fold_entails (pq_empty_cells_intro A ss) (by sep_focus) ?_
    refine FromSessionStateFacts.fold_entails (sessionStateAt_from_some_pq_empty_fold A ss G st sg sc hGs hsc hinv1 hdeser_srk hpriv_eq hpriv_clamp hsrk_len) (by sep_focus) ?_
    exact ent_of_eq (by ac_rfl)
  · have hpq_beq : (G.pq.cap == 0#64) = false := beq_eq_false_iff_ne.mpr hpq0
    have hpq_pos : 0 < G.pq.cap.toNat :=
      Nat.pos_of_ne_zero (fun h0 => hpq0 (BitVec.eq_of_toNat_eq h0))
    have hpow2 : ∃ k, 1 = 2 ^ k := ⟨0, rfl⟩
    have hlay_pq : LayoutOk G.pq.cap.toNat 1 :=
      ⟨hpq_pos, hpow2, by have := hpq_bds.2.1; omega⟩
    rw [ite_eq_right_iff.mpr (fun h => absurd h hpq0)]
    wp_steps
    refine SepWP.fold (ent_of_eq (stackAt_dealloc s0.sp)) (by sep_focus) ?_
    wp_call hdealloc (G.pq.ptr, G.pq.cap.toNat, 1)
    wp_steps
    try rw [hsp_sf_3]
    try rw [hsp_sf_2]
    try rw [hsp_sf_1]
    try rw [hsp_sf]
    refine FromSessionStateFacts.finish_otrFrom_placed ⟨ss, G, st, ret⟩ { G with pq := ⟨0#64, 1#64⟩ } _ _
      hmod1 hmod2 hnopanic hagree (by wp_done) ?_
    refine FromSessionStateFacts.fold_entails (ent_of_eq (stackAt_dealloc s0.sp).symm) (by sep_focus) ?_
    refine FromSessionStateFacts.fold_entails (ret16_fold_br3 ret (lsρ missingRemoteIdentitySym) m22 _ _ _ _ ?_ ?_ ?_ ?_) (by sep_focus) ?_
    · clear * -; bv_kernel
    · clear * -; bv_kernel
    · clear * -; bv_kernel
    · clear * -; bv_kernel
    refine FromSessionStateFacts.fold_entails (otrResultAt_iss_intro A ret (lsρ missingRemoteIdentitySym) 27#64 G.pq .missingRemoteIdentity) (by sep_focus) ?_
    refine FromSessionStateFacts.fold_entails (stackAt_prologue_fold s0.sp _ _ _ _ _ _ _ _ _ _ _ _) (by sep_focus) ?_
    refine FromSessionStateFacts.fold_entails (pq_empty_cells_intro A ss) (by sep_focus) ?_
    refine FromSessionStateFacts.fold_entails (sessionStateAt_from_some_pq_empty_fold A ss G st sg sc hGs hsc hinv1 hdeser_srk hpriv_eq hpriv_clamp hsrk_len) (by sep_focus) ?_
    exact ent_of_eq (by ac_rfl)

theorem otrFrom_case3_placed_ok [LibsignalPlacement] {A : RustAlloc}
    {H : String → Option (State → State)}
    (h_dealloc : HookSat H lsRustDeallocSym (rustDeallocSpec A))
    (hremIk : subroutine_ok ((blkPC_29).rebase (blkPl_29).base H)
      (blkPl_29).base (withLsCodeLoaded lsmpl (remoteIdentityKeyPlacedSpec A))) :
    subroutine_ok ((blkPC_19).rebase (blkPl_19).base H) (blkPl_19).base
      (otrFromCasePlacedSpec A
        (fun x => ∃ sc, x.st.senderChain = some sc ∧
          ¬ 256 ≤ x.st.version.toNat ∧ x.st.remoteIdentity = none)) :=
  otrFrom_case3_placed_ok_of_contracts
    (ls_hook_ok_of_mem h_dealloc)
    (CryptoVerification.LibsignalSession.FindReceiverChainIndex.deserialize_placed_ok H)
    hremIk

end CryptoVerification.LibsignalTripleRatchet.OutgoingRatchet
