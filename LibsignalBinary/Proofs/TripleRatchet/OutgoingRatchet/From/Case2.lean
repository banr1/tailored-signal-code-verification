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
import ProofLib.SepLogic.WPp

/-!
# `OutgoingTripleRatchet::from_session_state` Case 2 (`256 ≤ st.version.toNat`)

Verifies the `versionTooLarge` error branch (`st.senderChain = some sc` and
`256 ≤ st.version.toNat`) of `<OutgoingTripleRatchet>::from_session_state`.
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

theorem stackAt_deallocX (sp : BitVec 64) :
    stackAt (sp - 384#64) 65152 =
      stackAt (sp - 16768#64) 48768 ∗ stackAt (sp - 384#64) extHookStack := by
  change memRegion (sp - 384#64 - 65152#64) (48768 + 16384) =
    memRegion (sp - 16768#64 - 48768#64) 48768 ∗ memRegion (sp - 384#64 - 16384#64) 16384
  rw [memRegion_split (sp - 384#64 - 65152#64) 48768 16384 (by decide)]
  have h1 : sp - 384#64 - 65152#64 = sp - 16768#64 - 48768#64 := by bv_lin
  have h2 : sp - 16768#64 - 48768#64 + BitVec.ofNat 64 48768 = sp - 384#64 - 16384#64 := by bv_lin
  rw [h1, h2]

theorem otrFrom_case2_ok_ext_x {img : Obj.Image} {A : RustAlloc}
    {ext : String → Option (State → State)}
    (himg : Obj.Loads libsignalSessionImage img)
    (hA : AllocContractsX img A ext)
    (hDeser : DeserializeExtOk img.base ext) :
    subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr otrFromName)
      (otrFromCaseSpec A img
        (fun x => ∃ sc, x.st.senderChain = some sc ∧ 256 ≤ x.st.version.toNat)) := by
  dsimp only [otrFromCaseSpec, otrFromSpec, Spec.inImage]
  have hbase_align : img.base &&& 0xfff#64 = 0#64 :=
    ProofLib.ObjectLoad.base_aligned_of_loads himg
  have hdeser := deserialize_ok_at_otrFrom_ext hDeser
  have hdealloc := dealloc_ok_at_norm_ext_x hA (name := otrFromName) (k := num% (ls_off% "__rustc::__rust_dealloc" - ls_off% "<libsignal_protocol::triple_ratchet::OutgoingTripleRatchet>::from_session_state"))
    (by rw [(ls_lemma% fnOff "<libsignal_protocol::triple_ratchet::OutgoingTripleRatchet>::from_session_state"), (ls_stub% "__rustc::__rust_dealloc")])
  code_fetches_range libsignalSessionCode CryptoVerification.LibsignalTripleRatchet.OutgoingRatchet.libsignalSessionBin img.base
    (Rust.withPanics ext) (ls_lemma% fnOff "<libsignal_protocol::triple_ratchet::OutgoingTripleRatchet>::from_session_state") (num% (ls_off% "<libsignal_protocol::triple_ratchet::OutgoingTripleRatchet>::from_session_state")) 0 460
  code_fetches_range libsignalSessionCode CryptoVerification.LibsignalTripleRatchet.OutgoingRatchet.libsignalSessionBin img.base
    (Rust.withPanics ext) (ls_lemma% fnOff "<libsignal_protocol::triple_ratchet::OutgoingTripleRatchet>::from_session_state") (num% (ls_off% "<libsignal_protocol::triple_ratchet::OutgoingTripleRatchet>::from_session_state")) 1236 40
  wp_init
  have hadrp2 := fnAddr_adrp_b8f4 (b := img.base)
    (H := Rust.withPanics ext) hbase_align
  examples_generalize_entry
  examples_hide_fetches
  obtain ⟨ss, G, st, ret⟩ := a
  dsimp only at *
  rcases h_1 with ⟨sc, hsc, hver⟩
  apply SepWP.of_sepWP_inv (mid := entry + bv% (1240)) h_2 h_3
  refine SepWP.add_rodata (fun hm => rodata_versionTooLarge_intro himg h_2.roData hm) ?_
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
        ret200_split_br2 ret]
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
  apply SepWP.exists_elim; intro w3
  apply SepWP.exists_elim; intro b23
  apply SepWP.exists_elim; intro v21
  apply SepWP.exists_elim; intro v17
  apply SepWP.exists_elim; intro b16
  apply SepWP.exists_elim; intro w1
  apply SepWP.exists_elim; intro w0
  refine SepWP.focus_pure (by sep_focus) fun hinv1 => ?_
  refine SepWP.focus_pure (by sep_focus) fun hinv2 => ?_
  rcases hinv2 with ⟨hdeser_srk, hpriv_eq, hpriv_clamp, hsrk_len⟩
  refine SepWP.fold (vecU8Buf_bounds A sg.srk.cap sg.srk.ptr sg.srk.bytes) (by sep_focus) ?_
  refine SepWP.focus_pure (by sep_focus) fun hsrk_bds => ?_
  refine SepWP.fold (vecU8Buf_bounds A sg.priv.cap sg.priv.ptr sg.priv.bytes) (by sep_focus) ?_
  refine SepWP.focus_pure (by sep_focus) fun hpriv_bds => ?_
  refine SepWP.fold (vecU8Buf_bounds A sg.ck.cap sg.ck.ptr (keyToBytes32 sc.chainKey.key)) (by sep_focus) ?_
  refine SepWP.focus_pure (by sep_focus) fun hck_bds => ?_
  refine SepWP.fold (vecU8Buf_dealloc A G.pq.cap G.pq.ptr st.pqRatchetState) (by sep_focus) ?_
  refine SepWP.focus_pure (by sep_focus) fun hpq_bds => ?_
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
      false := by
    rw [version_word_eq st, subsPState32_255_ls_iff st.version, decide_eq_false_iff_not, not_not]
    exact hver
  conv =>
    arg 4
    rw [vecU8Buf_eq_bytes_live_of_ne_zero A sg.srk.cap sg.srk.ptr sg.srk.bytes hsrk_cap_ne0,
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
  wp_steps
  have hmod := otrFrom_model_verTooLarge ⟨ss, G, st, ret⟩ hsc hver
  have hmod1 : (OtrFromGhost.model ⟨ss, G, st, ret⟩).1 =
      .error (.invalidSessionStructure .versionTooLarge) :=
    congrArg Prod.fst hmod
  have hmod2 : (OtrFromGhost.model ⟨ss, G, st, ret⟩).2 = { st with pqRatchetState := [] } :=
    congrArg Prod.snd hmod
  have hnopanic : (.error (.invalidSessionStructure .versionTooLarge) :
      Except SignalProtocolError (OutgoingTripleRatchet (List (BitVec 8)))) ≠ .error .panic := by
    decide
  have hagree : G.AgreeExceptPq { G with pq := ⟨0#64, 1#64⟩ } := rfl
  have hagree' : G.AgreeExceptPq { G with pq := ⟨0#64, 1#64⟩, sender := some sg } :=
    agreeExceptPq_of_sender G ⟨0#64, 1#64⟩ sg hGs
  refine SepWP.fold (ck_scratch_entails_memRegion40_sp152 s0.sp _ _ _) (by sep_focus) ?_
  refine SepWP.fold (frame288_fold_phaseA s0.sp _ _ _ _ _ _ _ _ _ _ _) (by sep_focus) ?_
  refine SepWP.fold (bytes32_fold_1_4_2_8_8_8_1 sg.priv.ptr sc.ratchetKey.privateKey.bytes.toList hpriv_pk_len) (by sep_focus) ?_
  refine SepWP.fold (vecU8Buf_fold_of_ne_zero A sg.priv.cap sg.priv.ptr sc.ratchetKey.privateKey.bytes.toList hpriv_cap_ne0) (by sep_focus) ?_
  refine SepWP.fold (bytes32_fold_4_2_1_8_8_8_1 sg.ck.ptr (keyToBytes32 sc.chainKey.key) hck_key_len) (by sep_focus) ?_
  refine SepWP.fold (vecU8Buf_fold_of_ne_zero A sg.ck.cap sg.ck.ptr (keyToBytes32 sc.chainKey.key) hck_cap_ne0) (by sep_focus) ?_
  refine SepWP.fold (vecU8Buf_fold_of_ne_zero A sg.srk.cap sg.srk.ptr sg.srk.bytes hsrk_cap_ne0) (by sep_focus) ?_
  apply SepWP.done
    (by simp only [State.pc_setMem, State.pc_setPC])
    (by simp only [State.status_setMem, State.status_setPC, State.status_writeReg64,
      State.status_setPState, hrun_sf])
  intro hfrozen_m hsym_m
  have hinv_m : ImgCallInv img _ := ⟨hfrozen_m, hsym_m⟩
  by_cases hpq0 : G.pq.cap = (0 : BitVec 64)
  · -- `G.pq.cap = 0`: skip `__rust_dealloc`
    have hpq_beq : (G.pq.cap == 0#64) = true := beq_iff_eq.mpr hpq0
    rw [ite_eq_left_iff.mpr (fun h => absurd hpq0 h)]
    wp_steps
    refine FromSessionStateFacts.finish_otrFrom ⟨ss, G, st, ret⟩ { G with pq := ⟨0#64, 1#64⟩ } _ _
      hmod1 hmod2 hnopanic hagree (by wp_done) ?_
    refine FromSessionStateFacts.fold_entails (ret16_pointsTo64_of_1_4_2_1 ret (img.base + bv% (ls_str% "version does not fit in u8")) _ _ _ _ ?_ ?_ ?_ ?_) (by sep_focus) ?_
    · clear * -; bv_kernel
    · clear * -; bv_kernel
    · clear * -; bv_kernel
    · clear * -; bv_kernel
    refine FromSessionStateFacts.fold_entails (otrResultAt_iss_intro A ret (img.base + bv% (ls_str% "version does not fit in u8")) 26#64 G.pq .versionTooLarge) (by sep_focus) ?_
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
    refine SepWP.fold (ent_of_eq (stackAt_deallocX s0.sp)) (by sep_focus) ?_
    apply SepWP.done (by rfl) (by wp_norm_lhs)
    rintro ⟨hF_dealloc, hsym_dealloc⟩
    wp_call hdealloc (G.pq.ptr, G.pq.cap.toNat, 1)
    wp_steps
    try rw [hsp_sf_1]
    try rw [hsp_sf]
    refine FromSessionStateFacts.finish_otrFrom ⟨ss, G, st, ret⟩ { G with pq := ⟨0#64, 1#64⟩ } _ _
      hmod1 hmod2 hnopanic hagree (by wp_done) ?_
    refine FromSessionStateFacts.fold_entails (ent_of_eq (stackAt_deallocX s0.sp).symm) (by sep_focus) ?_
    refine FromSessionStateFacts.fold_entails (ret16_pointsTo64_of_1_4_2_1 ret (img.base + bv% (ls_str% "version does not fit in u8")) _ _ _ _ ?_ ?_ ?_ ?_) (by sep_focus) ?_
    · clear * -; bv_kernel
    · clear * -; bv_kernel
    · clear * -; bv_kernel
    · clear * -; bv_kernel
    refine FromSessionStateFacts.fold_entails (otrResultAt_iss_intro A ret (img.base + bv% (ls_str% "version does not fit in u8")) 26#64 G.pq .versionTooLarge) (by sep_focus) ?_
    refine FromSessionStateFacts.fold_entails (stackAt_prologue_fold s0.sp _ _ _ _ _ _ _ _ _ _ _ _) (by sep_focus) ?_
    refine FromSessionStateFacts.fold_entails (pq_empty_cells_intro A ss) (by sep_focus) ?_
    refine FromSessionStateFacts.fold_entails (sessionStateAt_from_some_pq_empty_fold A ss G st sg sc hGs hsc hinv1 hdeser_srk hpriv_eq hpriv_clamp hsrk_len) (by sep_focus) ?_
    exact ent_of_eq (by ac_rfl)

theorem otrFrom_case2_ok_ext {img : Obj.Image} {A : RustAlloc}
    {ext : String → Option (State → State)}
    (himg : Obj.Loads libsignalSessionImage img)
    (hA : AllocContracts img.base A ext)
    (hDeser : DeserializeExtOk img.base ext) :
    subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr otrFromName)
      (otrFromCaseSpec A img
        (fun x => ∃ sc, x.st.senderChain = some sc ∧ 256 ≤ x.st.version.toNat)) :=
  otrFrom_case2_ok_ext_x himg (AllocContractsX.of_AllocContracts hA) hDeser

theorem otrFrom_case2_ok {img : Obj.Image} {C : Crypto} {A : RustAlloc}
    {ctl : BitVec 64} {abs : String → Option (State → State)}
    (himg : Obj.Loads libsignalSessionImage img)
    (hA : AllocHooks A abs)
    (hDeser : DeserializeOk img.base C ctl abs) :
    subroutine_ok (tripleRatchetProgAt img.base C ctl abs)
      ((tripleRatchetProgAt img.base C ctl abs).fnAddr otrFromName)
      (otrFromCaseSpec A img
        (fun x => ∃ sc, x.st.senderChain = some sc ∧ 256 ≤ x.st.version.toNat)) :=
  otrFrom_case2_ok_ext himg (AllocContracts.of_tripleRatchetProgAt img.base C A ctl abs hA) hDeser

/-! ## Relocatable `[LibsignalPlacement]` Case 2 (`versionTooLarge`) -/

theorem otrFrom_case2_placed_ok_of_contracts [LibsignalPlacement] {A : RustAlloc}
    {H : String → Option (State → State)}
    (hdealloc : subroutine_ok ((blkPC_19).rebase (blkPl_19).base H)
      (lsρ lsRustDeallocSym) (rustDeallocSpec A))
    (hdeser : subroutine_ok ((blkPC_201).rebase (blkPl_201).base H)
      (blkPl_201).base CryptoVerification.LibsignalSession.FindReceiverChainIndex.deserializePlacedSpec) :
    subroutine_ok ((blkPC_19).rebase (blkPl_19).base H) (blkPl_19).base
      (otrFromCasePlacedSpec A
        (fun x => ∃ sc, x.st.senderChain = some sc ∧ 256 ≤ x.st.version.toNat)) := by
  dsimp only [otrFromCasePlacedSpec, otrFromRawPlacedSpec]
  wp_init
  obtain ⟨ss, G, st, ret⟩ := a
  dsimp only at *
  rcases h_1 with ⟨sc, hsc, hver⟩
  apply sepWP_seq_lscl h_2 (mid := lsmpl.base 201)
  refine SepWP.add_rodata (fun hm => rodata_versionTooLarge_placed_intro h_3 hm) ?_
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
        ret200_split_br2 ret]
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
  apply SepWP.exists_elim; intro w3
  apply SepWP.exists_elim; intro b23
  apply SepWP.exists_elim; intro v21
  apply SepWP.exists_elim; intro v17
  apply SepWP.exists_elim; intro b16
  apply SepWP.exists_elim; intro w1
  apply SepWP.exists_elim; intro w0
  refine SepWP.focus_pure (by sep_focus) fun hinv1 => ?_
  refine SepWP.focus_pure (by sep_focus) fun hinv2 => ?_
  rcases hinv2 with ⟨hdeser_srk, hpriv_eq, hpriv_clamp, hsrk_len⟩
  refine SepWP.fold (vecU8Buf_bounds A sg.srk.cap sg.srk.ptr sg.srk.bytes) (by sep_focus) ?_
  refine SepWP.focus_pure (by sep_focus) fun hsrk_bds => ?_
  refine SepWP.fold (vecU8Buf_bounds A sg.priv.cap sg.priv.ptr sg.priv.bytes) (by sep_focus) ?_
  refine SepWP.focus_pure (by sep_focus) fun hpriv_bds => ?_
  refine SepWP.fold (vecU8Buf_bounds A sg.ck.cap sg.ck.ptr (keyToBytes32 sc.chainKey.key)) (by sep_focus) ?_
  refine SepWP.focus_pure (by sep_focus) fun hck_bds => ?_
  refine SepWP.fold (vecU8Buf_dealloc A G.pq.cap G.pq.ptr st.pqRatchetState) (by sep_focus) ?_
  refine SepWP.focus_pure (by sep_focus) fun hpq_bds => ?_
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
      false := by
    rw [version_word_eq st, subsPState32_255_ls_iff st.version, decide_eq_false_iff_not, not_not]
    exact hver
  conv =>
    arg 4
    rw [vecU8Buf_eq_bytes_live_of_ne_zero A sg.srk.cap sg.srk.ptr sg.srk.bytes hsrk_cap_ne0,
        vecU8Buf_eq_bytes_live_of_ne_zero A sg.priv.cap sg.priv.ptr sg.priv.bytes hpriv_cap_ne0,
        vecU8Buf_eq_bytes_live_of_ne_zero A sg.ck.cap sg.ck.ptr (keyToBytes32 sc.chainKey.key) hck_cap_ne0,
        hpriv_eq, hpriv_pk_len,
        bytes32_eq_1_4_2_8_8_8_1 sg.priv.ptr sc.ratchetKey.privateKey.bytes.toList hpriv_pk_len,
        bytes32_eq_4_2_1_8_8_8_1 sg.ck.ptr (keyToBytes32 sc.chainKey.key) hck_key_len]
  wp_steps
  apply SepWP.done (by rfl) (by wp_norm_lhs)
  intro hcl_deser
  wp_call (lscall_blk (callerProg := (blkPC_19).rebase (blkPl_19).base H) hdeser hcl_deser)
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
  wp_steps
  have hmod := otrFrom_model_verTooLarge ⟨ss, G, st, ret⟩ hsc hver
  have hmod1 : (OtrFromGhost.model ⟨ss, G, st, ret⟩).1 =
      .error (.invalidSessionStructure .versionTooLarge) :=
    congrArg Prod.fst hmod
  have hmod2 : (OtrFromGhost.model ⟨ss, G, st, ret⟩).2 = { st with pqRatchetState := [] } :=
    congrArg Prod.snd hmod
  have hnopanic : (.error (.invalidSessionStructure .versionTooLarge) :
      Except SignalProtocolError (OutgoingTripleRatchet (List (BitVec 8)))) ≠ .error .panic := by
    decide
  have hagree : G.AgreeExceptPq { G with pq := ⟨0#64, 1#64⟩ } := rfl
  have hagree' : G.AgreeExceptPq { G with pq := ⟨0#64, 1#64⟩, sender := some sg } :=
    agreeExceptPq_of_sender G ⟨0#64, 1#64⟩ sg hGs
  refine SepWP.fold (ck_scratch_entails_memRegion40_sp152 s0.sp _ _ _) (by sep_focus) ?_
  refine SepWP.fold (frame288_fold_phaseA s0.sp _ _ _ _ _ _ _ _ _ _ _) (by sep_focus) ?_
  refine SepWP.fold (bytes32_fold_1_4_2_8_8_8_1 sg.priv.ptr sc.ratchetKey.privateKey.bytes.toList hpriv_pk_len) (by sep_focus) ?_
  refine SepWP.fold (vecU8Buf_fold_of_ne_zero A sg.priv.cap sg.priv.ptr sc.ratchetKey.privateKey.bytes.toList hpriv_cap_ne0) (by sep_focus) ?_
  refine SepWP.fold (bytes32_fold_4_2_1_8_8_8_1 sg.ck.ptr (keyToBytes32 sc.chainKey.key) hck_key_len) (by sep_focus) ?_
  refine SepWP.fold (vecU8Buf_fold_of_ne_zero A sg.ck.cap sg.ck.ptr (keyToBytes32 sc.chainKey.key) hck_cap_ne0) (by sep_focus) ?_
  refine SepWP.fold (vecU8Buf_fold_of_ne_zero A sg.srk.cap sg.srk.ptr sg.srk.bytes hsrk_cap_ne0) (by sep_focus) ?_
  by_cases hpq0 : G.pq.cap = (0 : BitVec 64)
  · have hpq_beq : (G.pq.cap == 0#64) = true := beq_iff_eq.mpr hpq0
    rw [ite_eq_left_iff.mpr (fun h => absurd hpq0 h)]
    wp_steps
    try rw [hsp_sf]
    refine FromSessionStateFacts.finish_otrFrom_placed ⟨ss, G, st, ret⟩ { G with pq := ⟨0#64, 1#64⟩ } _ _
      hmod1 hmod2 hnopanic hagree (by wp_done) ?_
    refine FromSessionStateFacts.fold_entails (ret16_pointsTo64_of_1_4_2_1 ret (lsρ versionTooLargeSym) _ _ _ _ ?_ ?_ ?_ ?_) (by sep_focus) ?_
    · clear * -; bv_kernel
    · clear * -; bv_kernel
    · clear * -; bv_kernel
    · clear * -; bv_kernel
    refine FromSessionStateFacts.fold_entails (otrResultAt_iss_intro A ret (lsρ versionTooLargeSym) 26#64 G.pq .versionTooLarge) (by sep_focus) ?_
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
    try rw [hsp_sf_1]
    try rw [hsp_sf]
    refine FromSessionStateFacts.finish_otrFrom_placed ⟨ss, G, st, ret⟩ { G with pq := ⟨0#64, 1#64⟩ } _ _
      hmod1 hmod2 hnopanic hagree (by wp_done) ?_
    refine FromSessionStateFacts.fold_entails (ent_of_eq (stackAt_dealloc s0.sp).symm) (by sep_focus) ?_
    refine FromSessionStateFacts.fold_entails (ret16_pointsTo64_of_1_4_2_1 ret (lsρ versionTooLargeSym) _ _ _ _ ?_ ?_ ?_ ?_) (by sep_focus) ?_
    · clear * -; bv_kernel
    · clear * -; bv_kernel
    · clear * -; bv_kernel
    · clear * -; bv_kernel
    refine FromSessionStateFacts.fold_entails (otrResultAt_iss_intro A ret (lsρ versionTooLargeSym) 26#64 G.pq .versionTooLarge) (by sep_focus) ?_
    refine FromSessionStateFacts.fold_entails (stackAt_prologue_fold s0.sp _ _ _ _ _ _ _ _ _ _ _ _) (by sep_focus) ?_
    refine FromSessionStateFacts.fold_entails (pq_empty_cells_intro A ss) (by sep_focus) ?_
    refine FromSessionStateFacts.fold_entails (sessionStateAt_from_some_pq_empty_fold A ss G st sg sc hGs hsc hinv1 hdeser_srk hpriv_eq hpriv_clamp hsrk_len) (by sep_focus) ?_
    exact ent_of_eq (by ac_rfl)

theorem otrFrom_case2_placed_ok [LibsignalPlacement] {A : RustAlloc}
    {H : String → Option (State → State)}
    (h_dealloc : HookSat H lsRustDeallocSym (rustDeallocSpec A)) :
    subroutine_ok ((blkPC_19).rebase (blkPl_19).base H) (blkPl_19).base
      (otrFromCasePlacedSpec A
        (fun x => ∃ sc, x.st.senderChain = some sc ∧ 256 ≤ x.st.version.toNat)) :=
  otrFrom_case2_placed_ok_of_contracts
    (ls_hook_ok_of_mem h_dealloc)
    (CryptoVerification.LibsignalSession.FindReceiverChainIndex.deserialize_placed_ok H)

end CryptoVerification.LibsignalTripleRatchet.OutgoingRatchet
