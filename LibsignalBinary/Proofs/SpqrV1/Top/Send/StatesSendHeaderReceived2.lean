/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SpqrV1.Top.Send.StatesSendHeaderReceived1
public import LibsignalBinary.Proofs.SpqrV1.Top.Send.StatesSendKeysUnsampled3
import GeneratedLean.LibsignalSessionCode -- shake: keep
import LibsignalBinary.Proofs.SpqrV1.States.Leaves.SendCt2Encoder
import LibsignalBinary.Proofs.TripleRatchet.GeneralizeEntry
import LibsignalBinary.Proofs.TripleRatchet.GeneralizeEntryEq
import ProofLib.SepLogic.WP.Apply
import ProofLib.SepLogic.WPp

/-!
# `spqr::send::<HookRng>`: Inlined `States::send` `.headerReceived` Arm (Part 2: `+1680..+3068`)

**Checked by Lean.**

Verifies `+1680..+3068` (`PolyEncoder::encode_bytes`, `next_chunk`, and state/chunk
relocation) and assembles `step_send_arm_headerReceived` (`0x30d7c -> 0x31458`).
-/

@[expose] public section

namespace CryptoVerification.SpqrV1.Top.Send

open Arm64 ProofLib ProofLib.ProgramReflection
open CryptoGames.LibsignalSession (Crypto ShaCompress)
open CryptoVerification.RustHeap CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchetRepr CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalSpqrV1 CryptoVerification.SpqrV1.Alloc
open CryptoVerification.SpqrV1.Auth CryptoVerification.SpqrV1.Kdf
open CryptoVerification.SpqrV1.GF.UnacceleratedMul CryptoVerification.SpqrV1.GF.Mul2U16
open CryptoVerification.SpqrV1.Poly CryptoVerification.SpqrV1.Poly.EncodeBytes
open CryptoVerification.SpqrV1.Poly.NextChunk
open CryptoVerification.SpqrV1.Drop CryptoVerification.SpqrV1.States
open CryptoVerification.SpqrV1.States.Leaves CryptoVerification.CodeLayout

set_option maxRecDepth 200000
set_option maxHeartbeats 400000
set_option linter.unusedSimpArgs false

attribute [local irreducible] libsignalSessionCode Program.fetch Program.externAt? Program.fnOff
attribute [local arm64_norm] bv_sub_add_lit BitVec.sub_add_cancel BitVec.toNat_zero

ls_attribute [local simp, local arm64_norm ↓, local wp_norm ↓]
  (ls_lemma% fnOff "spqr::send::<libsignal_session::HookRng>")
  (ls_lemma% fnOff "<spqr::encoding::polynomial::PolyEncoder as spqr::encoding::Encoder>::encode_bytes")
  (ls_lemma% fnOff "<spqr::encoding::polynomial::PolyEncoder as spqr::encoding::Encoder>::next_chunk")
  (ls_stub% "__rustc::__rust_no_alloc_shim_is_unstable_v2")
  (ls_stub% "__rustc::__rust_alloc")
  (ls_stub% "__rustc::__rust_dealloc")
  (ls_stub% "memcpy")
  (ls_stub% "alloc::raw_vec::handle_error")
  (ls_stub% "core::panicking::panic")
  (ls_stub% "core::result::unwrap_failed")

theorem encodeBytesResult_ct1 (ct1 : List.Vector (BitVec 8) 960) :
    ∃ enc : PolyEncoder,
      encodeBytesResult ct1.toList = .ok enc ∧
      expectEncodeBytes spqrPolyApi "v1/chunked/send_ct.rs:131" ct1.toList = .ok enc := by
  have h960 : ct1.toList.length = 960 := List.Vector.toList_length _
  obtain ⟨enc, h1, _, h2⟩ := encodeBytesResult_of_len_even_le
    (msg := ct1.toList) (by omega) (by omega)
  exact ⟨enc, h1, h2⟩

theorem send_ct1_chunk_ok_elim {F : ShaCompress} (K : MlKem)
    (st : Chunked.SendCt.HeaderReceived spqrPolyApi (spqrAuthApi F))
    {tape tape' : Bytes}
    {outSt : Chunked.SendCt.Ct1Sampled spqrPolyApi (spqrAuthApi F)}
    {chunk : Chunk}
    {ek : EpochSecret}
    (hsend : st.send_ct1_chunk K tape = .ok (outSt, chunk, ek, tape')) :
    ∃ (h32 : 32 ≤ tape.length)
      (ct1 : List.Vector (BitVec 8) 960)
      (es : List.Vector (BitVec 8) 2080)
      (ss : List.Vector (BitVec 8) 32)
      (sending_ct1 : PolyEncoder),
      let rand : List.Vector (BitVec 8) 32 := ⟨tape.take 32, by rw [List.length_take]; omega⟩
      let info := sckaKeyInfoPrefix ++ epochBeBytes st.uc.epoch
      let secret := hkdfToVecUnchecked F (List.replicate 32 0#8) ss.toList info 32
      let auth' := st.uc.auth.update F st.uc.epoch secret
      K.encaps1 st.uc.hdr rand = some (ct1, es, ss) ∧
      encodeBytesResult ct1.toList = .ok sending_ct1 ∧
      sending_ct1.nextChunk = .ok (outSt.sending_ct1, chunk) ∧
      outSt.uc = { epoch := st.uc.epoch, auth := auth', hdr := st.uc.hdr, es := es.toList, ct1 := ct1.toList } ∧
      outSt.receiving_ek = st.receiving_ek ∧
      ek = { epoch := st.uc.epoch, secret := secret } ∧
      tape' = tape.drop 32 := by
  have h32 : 32 ≤ tape.length := by
    apply Classical.byContradiction
    intro hlt
    rw [send_ct1_chunk_of_lt_32 K st (by omega)] at hsend
    cases hsend
  refine ⟨h32, ?_⟩
  let rand : List.Vector (BitVec 8) 32 := ⟨tape.take 32, by rw [List.length_take]; omega⟩
  cases hencaps : K.encaps1 st.uc.hdr rand with
  | none =>
    rw [send_ct1_chunk_of_encaps1_none K st h32 hencaps] at hsend
    cases hsend
  | some triple =>
    rcases triple with ⟨ct1, es, ss⟩
    obtain ⟨sending_ct1, henc_res, henc_exp⟩ := encodeBytesResult_ct1 ct1
    refine ⟨ct1, es, ss, sending_ct1, hencaps, henc_res, ?_⟩
    cases hnc : sending_ct1.nextChunk with
    | error p =>
      rw [send_ct1_chunk_of_nextChunk_err K st h32 hencaps henc_exp hnc] at hsend
      cases hsend
    | ok pair =>
      rcases pair with ⟨sending_ct1', chunk'⟩
      have hok := send_ct1_chunk_of_ok K st h32 hencaps henc_exp hnc
      dsimp only at hok
      rw [hok] at hsend
      injection hsend with htuple
      injection htuple with hout hrest1
      injection hrest1 with hch hrest2
      injection hrest2 with hek htp
      have hsnd : sending_ct1' = outSt.sending_ct1 :=
        congrArg Chunked.SendCt.Ct1Sampled.sending_ct1 hout
      have huc : _ = outSt.uc :=
        congrArg Chunked.SendCt.Ct1Sampled.uc hout
      have hrek : st.receiving_ek = outSt.receiving_ek :=
        congrArg Chunked.SendCt.Ct1Sampled.receiving_ek hout
      rw [← hsnd, ← huc, ← hrek, ← hch, ← hek, ← htp]
      exact ⟨rfl, rfl, rfl, rfl, rfl⟩

/-! ## Sub-Step 3 (`entry + 1680#64 -> entry + 1896#64`) -/

theorem memRegion_961_split_48_913 (sp : BitVec 64) :
    memRegion (sp + 4704#64) 961 =
      (∃∗ d0 : BitVec 64, (sp + 4704#64) ↦₆₄ d0) ∗
      (∃∗ d1 : BitVec 64, (sp + 4712#64) ↦₆₄ d1) ∗
      (∃∗ d2 : BitVec 64, (sp + 4720#64) ↦₆₄ d2) ∗
      (∃∗ d3 : BitVec 64, (sp + 4728#64) ↦₆₄ d3) ∗
      (∃∗ d4 : BitVec 64, (sp + 4736#64) ↦₆₄ d4) ∗
      (∃∗ d5 : BitVec 64, (sp + 4744#64) ↦₆₄ d5) ∗
      memRegion (sp + 4752#64) 913 := by
  rw [ProofLib.memRegion_split' (b := sp + 4704#64) (n := 48) (k := 913) (b' := sp + 4752#64) rfl (by bv_omega) (by decide),
      memRegion_48_eq_words6 (sp + 4704#64)]
  simp only [BitVec.add_assoc, arm64_norm]

theorem memRegion_4080_48_eq_words6 (sp : BitVec 64) :
    memRegion (sp + 4080#64) 48 =
      (∃∗ d0 : BitVec 64, (sp + 4080#64) ↦₆₄ d0) ∗ (∃∗ d1 : BitVec 64, (sp + 4088#64) ↦₆₄ d1) ∗
      (∃∗ d2 : BitVec 64, (sp + 4096#64) ↦₆₄ d2) ∗ (∃∗ d3 : BitVec 64, (sp + 4104#64) ↦₆₄ d3) ∗
      (∃∗ d4 : BitVec 64, (sp + 4112#64) ↦₆₄ d4) ∗ (∃∗ d5 : BitVec 64, (sp + 4120#64) ↦₆₄ d5) := by
  rw [memRegion_48_eq_words6 (sp + 4080#64)]; simp only [BitVec.add_assoc, arm64_norm]

theorem memRegion_7104_24_eq_words3 (sp : BitVec 64) :
    memRegion (sp + 7104#64) 24 =
      (∃∗ d0 : BitVec 64, (sp + 7104#64) ↦₆₄ d0) ∗ (∃∗ d1 : BitVec 64, (sp + 7112#64) ↦₆₄ d1) ∗
      (∃∗ d2 : BitVec 64, (sp + 7120#64) ↦₆₄ d2) := by
  rw [memRegion_24_eq_words3 (sp + 7104#64)]; simp only [BitVec.add_assoc, arm64_norm]

theorem fold_7536_to_memRegion_400 (sp w0 w1 w2 : BitVec 64) :
    ((sp + 7536#64) ↦₆₄ w0) ∗ ((sp + 7544#64) ↦₆₄ w1) ∗ ((sp + 7552#64) ↦₆₄ w2) ∗
    memRegion (sp + 7560#64) 8 ∗ memRegion (sp + 7568#64) 368 ⊢
    memRegion (sp + 7536#64) 400 := by
  have h24 := words3_entails_memRegion (sp + 7536#64) w0 w1 w2
  simp only [BitVec.add_assoc, arm64_norm] at h24
  rw [ProofLib.memRegion_split' (b := sp + 7536#64) (n := 24) (k := 376) (b' := sp + 7560#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := sp + 7560#64) (n := 8) (k := 368) (b' := sp + 7568#64) rfl (by bv_omega) (by decide)]
  exact Entails.trans (Entails.of_eq (by ac_rfl)) (sepConj_mono h24 (Entails.refl _))

theorem fold_4080_and_4704 (sp : BitVec 64) (g : AuthenticatorGhost) (auth : Authenticator) :
    ((sp + 4080#64) ↦₆₄ g.rootKey.cap) ∗ ((sp + 4088#64) ↦₆₄ g.rootKey.ptr) ∗
    ((sp + 4096#64) ↦₆₄ BitVec.ofNat 64 auth.rootKey.length) ∗
    ((sp + 4104#64) ↦₆₄ g.macKey.cap) ∗ ((sp + 4112#64) ↦₆₄ g.macKey.ptr) ∗
    ((sp + 4120#64) ↦₆₄ BitVec.ofNat 64 auth.macKey.length) ∗
    ((sp + 4704#64) ↦₆₄ g.rootKey.cap) ∗ ((sp + 4712#64) ↦₆₄ g.rootKey.ptr) ∗
    ((sp + 4720#64) ↦₆₄ BitVec.ofNat 64 auth.rootKey.length) ∗
    ((sp + 4728#64) ↦₆₄ g.macKey.cap) ∗ ((sp + 4736#64) ↦₆₄ g.macKey.ptr) ∗
    ((sp + 4744#64) ↦₆₄ BitVec.ofNat 64 auth.macKey.length) ∗
    memRegion (sp + 4752#64) 913 ∗ memRegion (sp + 5665#64) 1439 ⊢
    authInlineWordsAt g (sp + 4080#64) auth ∗ memRegion (sp + 4704#64) 928 ∗
    memRegion (sp + 5632#64) 34 ∗ memRegion (sp + 5666#64) 1438 := by
  have h48 := authInlineWordsAt_entails_memRegion g (sp + 4704#64) auth
  have h2400 : memRegion (sp + 4704#64) 48 ∗ (memRegion (sp + 4752#64) 913 ∗ memRegion (sp + 5665#64) 1439) =
      memRegion (sp + 4704#64) 928 ∗ memRegion (sp + 5632#64) 34 ∗ memRegion (sp + 5666#64) 1438 := by
    rw [← ProofLib.memRegion_split' (b := sp + 4752#64) (n := 913) (k := 1439) (b' := sp + 5665#64) rfl (by bv_omega) (by decide),
        ← ProofLib.memRegion_split' (b := sp + 4704#64) (n := 48) (k := 2352) (b' := sp + 4752#64) rfl (by bv_omega) (by decide),
        ProofLib.memRegion_split' (b := sp + 4704#64) (n := 928) (k := 1472) (b' := sp + 5632#64) rfl (by bv_omega) (by decide),
        ProofLib.memRegion_split' (b := sp + 5632#64) (n := 34) (k := 1438) (b' := sp + 5666#64) rfl (by bv_omega) (by decide)]
  rw [← h2400]
  have h4080 : authInlineWordsAt g (sp + 4080#64) auth =
      ((sp + 4080#64) ↦₆₄ g.rootKey.cap) ∗ ((sp + 4088#64) ↦₆₄ g.rootKey.ptr) ∗
      ((sp + 4096#64) ↦₆₄ BitVec.ofNat 64 auth.rootKey.length) ∗
      ((sp + 4104#64) ↦₆₄ g.macKey.cap) ∗ ((sp + 4112#64) ↦₆₄ g.macKey.ptr) ∗
      ((sp + 4120#64) ↦₆₄ BitVec.ofNat 64 auth.macKey.length) := by
    dsimp only [authInlineWordsAt]; simp only [BitVec.add_assoc, arm64_norm, sepConj_assoc]
  have h4704 : authInlineWordsAt g (sp + 4704#64) auth =
      ((sp + 4704#64) ↦₆₄ g.rootKey.cap) ∗ ((sp + 4712#64) ↦₆₄ g.rootKey.ptr) ∗
      ((sp + 4720#64) ↦₆₄ BitVec.ofNat 64 auth.rootKey.length) ∗
      ((sp + 4728#64) ↦₆₄ g.macKey.cap) ∗ ((sp + 4736#64) ↦₆₄ g.macKey.ptr) ∗
      ((sp + 4744#64) ↦₆₄ BitVec.ofNat 64 auth.macKey.length) := by
    dsimp only [authInlineWordsAt]; simp only [BitVec.add_assoc, arm64_norm, sepConj_assoc]
  rw [h4080]
  refine Entails.trans (Entails.of_eq ?_) (sepConj_mono_right (sepConj_mono_left h48))
  rw [h4704]; ac_rfl

theorem step_headerReceived_1680_to_1896 {F : ShaCompress}
    {img : Obj.Image} {A : RustAlloc} {ext : String → Option (State → State)}
    (hA : AllocContracts img.base A ext) (hbase : img.base &&& 0xfff#64 = 0#64)
    (henc_call : EncodeBytesOkX img A ext) (hnc_call : PolyNextChunkOkX img A ext)
    (sp epoch hdr_cap hdr_ptr es_ptr ct1_tmp_ptr info_ptr ss_ptr secret_cap secret_ptr : BitVec 64)
    (auth' : Authenticator) (hdr info secret : Bytes)
    (ct1 : List.Vector (BitVec 8) 960) (ss : List.Vector (BitVec 8) 32)
    (sending_ct1 : PolyEncoder) (outSt : Chunked.SendCt.Ct1Sampled spqrPolyApi (spqrAuthApi F))
    (chunk : Chunk) (hinfo_len : info.length = 41)
    (henc_res : encodeBytesResult ct1.toList = .ok sending_ct1)
    (hnc : sending_ct1.nextChunk = .ok (outSt.sending_ct1, chunk))
    {ret : BitVec 64} {s0 s : State} {P Frame R : SepProp} {post : State → SepProp → Prop}
    (hinv : ImgCallInv img s) (hsp_align : (sp &&& 15#64 == 0#64) = true)
    (hpc : s.pc = (tripleRatchetProgAtExt img.base ext).fnAddr spqrSendName + 1680#64)
    (hrun : s.status = .Running) (hsp : s.sp = sp)
    (hx20 : s.readReg64 .x20 = ss_ptr) (hx21 : s.readReg64 .x21 = hdr_ptr)
    (hx22 : s.readReg64 .x22 = epoch) (hx24 : s.readReg64 .x24 = es_ptr)
    (hx25 : s.readReg64 .x25 = ct1_tmp_ptr) (hx26 : s.readReg64 .x26 = sp + 4704#64)
    (_hx27 : s.readReg64 .x27 = BitVec.ofNat 64 hdr.length) (hx28 : s.readReg64 .x28 = info_ptr)
    (htrace : s.trace = s0.trace)
    (hP : P = (
      ((sp + 32#64) ↦₆₄ BitVec.ofNat 64 hdr.length) ∗ ((sp + 40#64) ↦₆₄ hdr_cap) ∗
      authenticatorAt A (sp + 4192#64) auth' ∗ memRegion (sp + 4080#64) 48 ∗
      memRegion (sp + 4704#64) 961 ∗ memRegion (sp + 5665#64) 1439 ∗
      A.live ct1_tmp_ptr 960 1 ∗ (ct1_tmp_ptr ↦ₛ ct1.toList) ∗
      A.live info_ptr 41 1 ∗ (info_ptr ↦ₛ info) ∗
      A.live ss_ptr 32 1 ∗ (ss_ptr ↦ₛ ss.toList) ∗
      memRegion (sp + 7104#64) 24 ∗ memRegion (sp + 7136#64) 400 ∗
      ((sp + 7536#64) ↦₆₄ secret_cap) ∗ ((sp + 7544#64) ↦₆₄ secret_ptr) ∗ ((sp + 7552#64) ↦₆₄ 32#64) ∗
      A.live secret_ptr secret_cap.toNat 1 ∗ (secret_ptr ↦ₛ secret) ∗
      memRegion (secret_ptr + 32#64) (secret_cap.toNat - 32) ∗
      memRegion (sp + 7560#64) 8 ∗ memRegion (sp + 7568#64) 368 ∗
      tokenInitAt img.base ∗ reduceTableAt img.base ∗
      A.pool ∗ stackAt sp spqrSendCalleeStack) ∗ Frame)
    (hnext : ∀ (sf : State) (g' : AuthenticatorGhost) (ct1_ptr : BitVec 64),
      ImgCallInv img sf → ct1_ptr ≠ 0 → (ct1_ptr == 0#64) = false →
      sf.pc = (tripleRatchetProgAtExt img.base ext).fnAddr spqrSendName + 1896#64 →
      sf.status = .Running → sf.sp = sp →
      sf.readReg64 .x19 = s.readReg64 .x19 → sf.readReg64 .x20 = sp + 2384#64 →
      sf.readReg64 .x21 = hdr_ptr → sf.readReg64 .x22 = epoch →
      sf.readReg64 .x23 = s.readReg64 .x23 → sf.readReg64 .x24 = es_ptr →
      sf.readReg64 .x25 = ct1_tmp_ptr → sf.readReg64 .x26 = sp + 4704#64 →
      sf.readReg64 .x27 = ct1_ptr → sf.readReg64 .x28 = sp + 4704#64 →
      sf.trace = s0.trace →
      calleeSavedVRegs sf = calleeSavedVRegs s →
      SepWPp (tripleRatchetProgAtExt img.base ext) ret sf
        ((((sp + 32#64) ↦₆₄ BitVec.ofNat 64 hdr.length) ∗ ((sp + 40#64) ↦₆₄ hdr_cap) ∗
          authInlineWordsAt g' (sp + 4080#64) auth' ∗ authHeapBufs A g' auth' ∗
          memRegion (sp + 4192#64) 48 ∗ memRegion (sp + 4704#64) 928 ∗
          chunkAt (sp + 5632#64) chunk ∗ memRegion (sp + 5666#64) 1438 ∗
          A.live ct1_tmp_ptr 960 1 ∗ (ct1_tmp_ptr ↦ₛ ct1.toList) ∗
          A.live ct1_ptr 960 1 ∗ (ct1_ptr ↦ₛ ct1.toList) ∗
          ((sp + 7104#64) ↦₆₄ secret_cap) ∗ ((sp + 7112#64) ↦₆₄ secret_ptr) ∗ ((sp + 7120#64) ↦₆₄ 32#64) ∗
          A.live secret_ptr secret_cap.toNat 1 ∗ (secret_ptr ↦ₛ secret) ∗
          memRegion (secret_ptr + 32#64) (secret_cap.toNat - 32) ∗
          memRegion (sp + 7136#64) 400 ∗ polyEncoderAt A (sp + 7536#64) outSt.sending_ct1 ∗
          tokenInitAt img.base ∗ reduceTableAt img.base ∗
          A.pool ∗ stackAt sp spqrSendCalleeStack) ∗ Frame) post
        (fun sf P_f => (sf.mem ⊨ P_f ∗ R) →
          (sf.mem ⊨ (⌜allocFailedIn s0 sf ∧ s0.trace <+: sf.trace⌝ ∗ anyHeap) ∗ R))) :
    SepWPp (tripleRatchetProgAtExt img.base ext) ret s P post
      (fun sf P_f => (sf.mem ⊨ P_f ∗ R) →
        (sf.mem ⊨ (⌜allocFailedIn s0 sf ∧ s0.trace <+: sf.trace⌝ ∗ anyHeap) ∗ R)) := by
  have hshim := spqrSend_shim_ok hA
  have halloc := spqrSend_alloc_ok hA
  have hdealloc := spqrSend_dealloc_ok hA
  have hmemcpy_reg := spqrSend_memcpy_region_ok hA
  have hmemcpy := spqrSend_memcpy_ok hA
  have haerr := spqrSend_handle_error (b := img.base) (ext := ext)
  have henc_at := spqrSend_encodeBytes_ok henc_call
  have hnc_at := spqrSend_polyNextChunk_ok hnc_call
  have hct1_len : ct1.toList.length = 960 := List.Vector.toList_length _
  have hss_len : ss.toList.length = 32 := List.Vector.toList_length _
  spqr_send_fetches_range img.base (Rust.withPanics ext) 1680 220
  spqr_send_fetches_range img.base (Rust.withPanics ext) 13564 16
  generalize_entry hentry : (tripleRatchetProgAtExt img.base ext).fnAddr spqrSendName = entry
  examples_hide_fetches; subst hP
  simp only [Reg.x20, Reg.x21, Reg.x22, Reg.x24, Reg.x25, Reg.x26, Reg.x28]
    at hx20 hx21 hx22 hx24 hx25 hx26 hx28
  apply of_sepWP_inImage (mid := entry + bv% (ls_rel% "spqr::send::<libsignal_session::HookRng>" "__rustc::__rust_alloc")) img hinv
  refine SepWP.fold (authenticatorAt_entails_exists_inline_heap A (sp + 4192#64) auth') (by sep_focus) ?_
  rw [sepExists_sepConj_left]
  apply SepWP.exists_elim; intro g'
  rw [memRegion_961_split_48_913 sp]
  simp only [sepExists_sepConj_left, sepExists_sepConj_right]
  iterate 6 (apply SepWP.exists_elim; intro _)
  wp_conv_pre => dsimp only [authInlineWordsAt]; simp only [BitVec.add_assoc, arm64_norm]
  wp_steps; wp_apply; wp_steps
  have hfold_4192 :
      ((sp + 4192#64) ↦₆₄ g'.rootKey.cap) ∗ ((sp + 4200#64) ↦₆₄ g'.rootKey.ptr) ∗
      ((sp + 4208#64) ↦₆₄ BitVec.ofNat 64 auth'.rootKey.length) ∗
      ((sp + 4216#64) ↦₆₄ g'.macKey.cap) ∗ ((sp + 4224#64) ↦₆₄ g'.macKey.ptr) ∗
      ((sp + 4232#64) ↦₆₄ BitVec.ofNat 64 auth'.macKey.length) ⊢ memRegion (sp + 4192#64) 48 := by
    have h := authInlineWordsAt_entails_memRegion g' (sp + 4192#64) auth'
    dsimp only [authInlineWordsAt] at h
    simpa only [BitVec.add_assoc, arm64_norm, sepConj_assoc] using h
  refine SepWP.fold hfold_4192 (by sep_focus) ?_
  clear hfold_4192
  apply SepWP.done (by wp_norm_goal) (by simp only [wp_norm, arm64_norm, *])
  intro hinv1
  refine call_rustAlloc_inImage halloc 960 ⟨by decide, ⟨0, rfl⟩, by decide⟩
    (s0 := s0) (ret_pc := entry + 1720#64) (sp_call := sp) hinv1
    (by wp_norm_goal) (by simp only [wp_norm, arm64_norm, *])
    (by simp only [State.sp, arm64_norm, *]) hsp_align
    (by simp only [Reg.lr, arm64_norm, *]) (by simp only [arm64_norm, *])
    (by simp only [Reg.x0, arm64_norm, *]) (by simp only [Reg.x1, arm64_norm, *])
    (by sep_focus)
    (fun sf1 hinv_oom1 hpc1 hrun1 hsp1 _ h0_1 htr_oom1 => ?_)
    (fun sf1 hinv_ok1 hpc1 hrun1 hsp1 hcs1 hne0_1 h0b_1 htr_ok1 => ?_)
  · apply of_sepWP_inImage (mid := entry + bv% (ls_rel% "spqr::send::<libsignal_session::HookRng>" "alloc::raw_vec::handle_error")) img hinv_oom1
    wp_steps
    apply SepWP.done (by wp_norm_goal) (by simp only [wp_norm, arm64_norm, *])
    intro _
    exact finish_oom_panic (by simp only [wp_norm, arm64_norm, *]) (by simp only [wp_norm, arm64_norm, *])
      (by simp only [arm64_norm, *])
  · rcases hcs1 with ⟨hx19_1, hx20_1, hx21_1, hx22_1, hx23_1, hx24_1, hx25_1, hx26_1, hx27_1, hx28_1, hfp_1, hvregs_1⟩
    simp only [wp_norm, arm64_norm, *] at hx19_1 hx20_1 hx21_1 hx22_1 hx23_1 hx24_1 hx25_1 hx26_1 hx27_1 hx28_1 hfp_1 hvregs_1
    apply of_sepWP_inImage (mid := entry + bv% (ls_rel% "spqr::send::<libsignal_session::HookRng>" "<spqr::encoding::polynomial::PolyEncoder as spqr::encoding::Encoder>::encode_bytes")) img hinv_ok1
    have hct1_mem : memRegion (sf1.readReg64 (Reg.gpr 0#5)) 960 =
        memRegion (sf1.readReg64 (Reg.gpr 0#5)) ct1.toList.length := by rw [hct1_len]
    rw [memRegion_4080_48_eq_words6 sp, memRegion_7104_24_eq_words3 sp]
    simp only [sepExists_sepConj_left, sepExists_sepConj_right]
    iterate 9 (apply SepWP.exists_elim; intro _)
    wp_conv_pre => rw [hct1_mem]
    wp_steps; wp_apply; wp_steps
    have hinfo_mem := pointsToBytes_entails_memRegion info_ptr info
    rw [hinfo_len] at hinfo_mem
    have hss_mem := pointsToBytes_entails_memRegion ss_ptr ss.toList
    rw [hss_len] at hss_mem
    refine SepWP.fold hinfo_mem (by sep_focus) ?_
    refine SepWP.fold hss_mem (by sep_focus) ?_
    refine SepWP.fold (stackAt_spqrSendCallee_to_allocHook sp) (by sep_focus) ?_
    wp_apply; wp_steps; wp_apply
    refine SepWP.fold (stackAt_spqrSendCallee_from_allocHook sp)
      (by simp only [‹sf_2.sp = _›, ‹sf_1.sp = _›, ‹sf.sp = _›, hsp1]; sep_focus) ?_
    refine SepWP.fold (fold_7536_to_memRegion_400 sp secret_cap secret_ptr 32#64) (by sep_focus) ?_
    refine SepWP.fold (fold_4080_and_4704 sp g' auth') (by sep_focus) ?_
    wp_steps
    apply SepWP.done (by wp_norm_goal) (by simp only [wp_norm, arm64_norm, *])
    intro hinv2
    refine call_inImage_calleeStack
      (x := ({
        out := sp + 7136#64, msgRO := false, msgA := ct1_tmp_ptr,
        msg := ct1.toList } : EncodeBytesGhost))
      (s0 := s0) sp encodeBytesStackX (by decide)
      (T_pre := memRegion (sp + 7136#64) polyEncoderSize ∗
        (ct1_tmp_ptr ↦ₛ ct1.toList) ∗ A.pool)
      (T_post := fun _ => polyEncoderAt A (sp + 7136#64) sending_ct1 ∗
        (ct1_tmp_ptr ↦ₛ ct1.toList) ∗ A.pool)
      (F := ((sp + 32#64) ↦₆₄ BitVec.ofNat 64 hdr.length) ∗ ((sp + 40#64) ↦₆₄ hdr_cap) ∗
        authInlineWordsAt g' (sp + 4080#64) auth' ∗ authHeapBufs A g' auth' ∗
        memRegion (sp + 4192#64) 48 ∗
        memRegion (sp + 4704#64) 928 ∗ memRegion (sp + 5632#64) 34 ∗ memRegion (sp + 5666#64) 1438 ∗
        A.live ct1_tmp_ptr 960 1 ∗
        A.live (sf1.readReg64 (Reg.gpr 0#5)) 960 1 ∗ ((sf1.readReg64 (Reg.gpr 0#5)) ↦ₛ ct1.toList) ∗
        ((sp + 7104#64) ↦₆₄ secret_cap) ∗ ((sp + 7112#64) ↦₆₄ secret_ptr) ∗ ((sp + 7120#64) ↦₆₄ 32#64) ∗
        A.live secret_ptr secret_cap.toNat 1 ∗ (secret_ptr ↦ₛ secret) ∗
        memRegion (secret_ptr + 32#64) (secret_cap.toNat - 32) ∗
        memRegion (sp + 7536#64) 400 ∗
        tokenInitAt img.base ∗ reduceTableAt img.base ∗ Frame)
      (φ_pre := _) (φ_post := _) henc_at hinv2
      (by wp_norm_goal) (by simp only [wp_norm, arm64_norm, *]) (by simp only [State.sp, arm64_norm, *])
      hsp_align (by simp only [wp_norm, arm64_norm, *])
      (ret_pc := entry + 1832#64) (by simp only [Reg.lr, wp_norm, arm64_norm, *])
      (by dsimp only [encodeBytesSpecX, encodeBytesSpec]; rw [bytesAt_false_eq]; ac_rfl)
      (by simp only [hct1_len, Reg.x8, Reg.x0, Reg.x1, wp_norm, arm64_norm, *])
      (by dsimp only [polyEncoderSize, authInlineWordsAt]; simp only [BitVec.add_assoc, arm64_norm]; ac_rfl)
      (fun _ _ => rfl)
      (fun sf => encodeBytes_onPanic_of_ok _ henc_res _ sf)
      (by intro sf; dsimp only [encodeBytesSpecX, encodeBytesSpec]; rw [henc_res, resultPolyEncoderAt, bytesAt_false_eq]; ac_rfl) ?_
    intro sm1 hpc_sm1 hrun_sm1 hsp_sm1 htr_sm1 hinv_sm1
      hx19_sm1 hx20_sm1 hx21_sm1 hx22_sm1 hx23_sm1 hx24_sm1 hx25_sm1 hx26_sm1 hx27_sm1 hx28_sm1 hvregs_sm1
    simp only [Reg.x19, Reg.x20, Reg.x21, Reg.x22, Reg.x23, Reg.x24, Reg.x25, Reg.x26, Reg.x27, Reg.x28,
      wp_norm, arm64_norm, *] at htr_sm1 hx19_sm1 hx20_sm1 hx21_sm1 hx22_sm1 hx23_sm1 hx24_sm1 hx25_sm1 hx26_sm1 hx27_sm1 hx28_sm1 hvregs_sm1
    apply of_sepWP_inImage (mid := entry + bv% (ls_rel% "spqr::send::<libsignal_session::HookRng>" "<spqr::encoding::polynomial::PolyEncoder as spqr::encoding::Encoder>::next_chunk")) img hinv_sm1
    have h1868 : ∀ s_m : State,
        s_m.pc = entry + bv% (ls_rel% "spqr::send::<libsignal_session::HookRng>" "memcpy") → s_m.status = .Running → s_m.sp = sp → s_m.trace = s0.trace →
        calleeSavedVRegs s_m = calleeSavedVRegs s →
        s_m.readReg64 Reg.lr = entry + 1872#64 →
        s_m.readReg64 Reg.x0 = sp + 7536#64 → s_m.readReg64 Reg.x1 = sp + 7136#64 →
        (s_m.readReg64 Reg.x2).toNat = 400 →
        s_m.readReg64 .x19 = s.readReg64 .x19 → s_m.readReg64 .x20 = sp + 2384#64 →
        s_m.readReg64 .x21 = hdr_ptr → s_m.readReg64 .x22 = epoch →
        s_m.readReg64 .x23 = s.readReg64 .x23 → s_m.readReg64 .x24 = es_ptr →
        s_m.readReg64 .x25 = ct1_tmp_ptr → s_m.readReg64 .x26 = sp + 4704#64 →
        s_m.readReg64 .x27 = sf1.readReg64 (Reg.gpr 0#5) →
        SepWP (tripleRatchetProgAtExt img.base ext) (entry + bv% (ls_rel% "spqr::send::<libsignal_session::HookRng>" "<spqr::encoding::polynomial::PolyEncoder as spqr::encoding::Encoder>::next_chunk")) s_m
          ((stackAt sp spqrSendCalleeStack ∗
            (polyEncoderAt A (sp + 7136#64) sending_ct1 ∗
             (ct1_tmp_ptr ↦ₛ ct1.toList) ∗ A.pool)) ∗
           ((sp + 32#64) ↦₆₄ BitVec.ofNat 64 hdr.length) ∗ ((sp + 40#64) ↦₆₄ hdr_cap) ∗
           authInlineWordsAt g' (sp + 4080#64) auth' ∗ authHeapBufs A g' auth' ∗
           memRegion (sp + 4192#64) 48 ∗
           memRegion (sp + 4704#64) 928 ∗ memRegion (sp + 5632#64) 34 ∗ memRegion (sp + 5666#64) 1438 ∗
           A.live ct1_tmp_ptr 960 1 ∗
           A.live (sf1.readReg64 (Reg.gpr 0#5)) 960 1 ∗ ((sf1.readReg64 (Reg.gpr 0#5)) ↦ₛ ct1.toList) ∗
           ((sp + 7104#64) ↦₆₄ secret_cap) ∗ ((sp + 7112#64) ↦₆₄ secret_ptr) ∗ ((sp + 7120#64) ↦₆₄ 32#64) ∗
           A.live secret_ptr secret_cap.toNat 1 ∗ (secret_ptr ↦ₛ secret) ∗
           memRegion (secret_ptr + 32#64) (secret_cap.toNat - 32) ∗
           memRegion (sp + 7536#64) 400 ∗
           tokenInitAt img.base ∗ reduceTableAt img.base ∗ Frame)
          (fun sm Pm => ImgCallInv img sm → SepWPp (tripleRatchetProgAtExt img.base ext) ret sm Pm post
            (fun sf P_f => (sf.mem ⊨ P_f ∗ R) →
              (sf.mem ⊨ (⌜allocFailedIn s0 sf ∧ s0.trace <+: sf.trace⌝ ∗ anyHeap) ∗ R))) := by
      intro s_m hpcm hrunm hspm htrm hvregsm hlrm hx0m hx1m hx2m
        hx19m hx20m hx21m hx22m hx23m hx24m hx25m hx26m hx27m
      refine call_memcpy_relocate hmemcpy (Relocatable.of_polyEncoderAt A sending_ct1)
        (sp + 7536#64) (sp + 7136#64) (s0 := s0) (sp_call := sp)
        (Frame := stackAt sp spqrSendCalleeStack ∗
          (ct1_tmp_ptr ↦ₛ ct1.toList) ∗ A.pool ∗
          ((sp + 32#64) ↦₆₄ BitVec.ofNat 64 hdr.length) ∗ ((sp + 40#64) ↦₆₄ hdr_cap) ∗
          authInlineWordsAt g' (sp + 4080#64) auth' ∗ authHeapBufs A g' auth' ∗
          memRegion (sp + 4192#64) 48 ∗
          memRegion (sp + 4704#64) 928 ∗ memRegion (sp + 5632#64) 34 ∗ memRegion (sp + 5666#64) 1438 ∗
          A.live ct1_tmp_ptr 960 1 ∗
          A.live (sf1.readReg64 (Reg.gpr 0#5)) 960 1 ∗ ((sf1.readReg64 (Reg.gpr 0#5)) ↦ₛ ct1.toList) ∗
          ((sp + 7104#64) ↦₆₄ secret_cap) ∗ ((sp + 7112#64) ↦₆₄ secret_ptr) ∗ ((sp + 7120#64) ↦₆₄ 32#64) ∗
          A.live secret_ptr secret_cap.toNat 1 ∗ (secret_ptr ↦ₛ secret) ∗
          memRegion (secret_ptr + 32#64) (secret_cap.toNat - 32) ∗
          tokenInitAt img.base ∗ reduceTableAt img.base ∗ Frame)
        hpcm hrunm hspm hsp_align hlrm htrm hx0m hx1m hx2m
        (by ac_rfl) ?_
      intro sf2 hpc_sf2 hrun_sf2 hsp_sf2 htr_sf2
        hx19_sf2 hx20_sf2 hx21_sf2 hx22_sf2 hx23_sf2 hx24_sf2 hx25_sf2 hx26_sf2 hx27_sf2 _ hvregs_sf2
      simp only [Reg.x19, Reg.x20, Reg.x21, Reg.x22, Reg.x23, Reg.x24, Reg.x25, Reg.x26, Reg.x27,
        wp_norm, arm64_norm, *] at hx19_sf2 hx20_sf2 hx21_sf2 hx22_sf2 hx23_sf2 hx24_sf2 hx25_sf2 hx26_sf2 hx27_sf2 hvregs_sf2
      wp_steps
      apply SepWP.done (by wp_norm_goal) (by simp only [wp_norm, arm64_norm, *]); intro hinv3
      refine call_inImage_calleeStack
        (x := ({
          outA := sp + 5632#64, encA := sp + 7536#64,
          enc := sending_ct1, enc' := outSt.sending_ct1, chunk := chunk } : PolyNextChunkGhost))
        (s0 := s0) sp polyNextChunkStack (by decide)
        (T_pre := memRegion (sp + 5632#64) chunkSize ∗
          polyEncoderAt A (sp + 7536#64) sending_ct1 ∗
          tokenInitAt img.base ∗ reduceTableAt img.base ∗ A.pool)
        (T_post := fun _ => polyEncoderAt A (sp + 7536#64) outSt.sending_ct1 ∗
          chunkAt (sp + 5632#64) chunk ∗
          tokenInitAt img.base ∗ reduceTableAt img.base ∗ A.pool)
        (F := memRegion (sp + 7136#64) 400 ∗
          (ct1_tmp_ptr ↦ₛ ct1.toList) ∗
          ((sp + 32#64) ↦₆₄ BitVec.ofNat 64 hdr.length) ∗ ((sp + 40#64) ↦₆₄ hdr_cap) ∗
          authInlineWordsAt g' (sp + 4080#64) auth' ∗ authHeapBufs A g' auth' ∗
          memRegion (sp + 4192#64) 48 ∗
          memRegion (sp + 4704#64) 928 ∗ memRegion (sp + 5666#64) 1438 ∗
          A.live ct1_tmp_ptr 960 1 ∗
          A.live (sf1.readReg64 (Reg.gpr 0#5)) 960 1 ∗ ((sf1.readReg64 (Reg.gpr 0#5)) ↦ₛ ct1.toList) ∗
          ((sp + 7104#64) ↦₆₄ secret_cap) ∗ ((sp + 7112#64) ↦₆₄ secret_ptr) ∗ ((sp + 7120#64) ↦₆₄ 32#64) ∗
          A.live secret_ptr secret_cap.toNat 1 ∗ (secret_ptr ↦ₛ secret) ∗
          memRegion (secret_ptr + 32#64) (secret_cap.toNat - 32) ∗ Frame)
        (φ_pre := _) (φ_post := _) hnc_at hinv3
        (by wp_norm_goal) (by simp only [wp_norm, arm64_norm, *]) (by simp only [State.sp, arm64_norm, *])
        hsp_align (by simp only [wp_norm, arm64_norm, *])
        (ret_pc := entry + 1896#64) (by simp only [Reg.lr, wp_norm, arm64_norm, *])
        (by dsimp only [polyNextChunkSpec]; ac_rfl)
        (by simp only [hbase, hnc, Reg.x8, Reg.x0, wp_norm, arm64_norm, *])
        (by dsimp only [polyEncoderSize, chunkSize]; ac_rfl)
        (fun _ _ => rfl)
        (fun sf => polyNextChunk_onPanic_of_ok img.base _ hnc _ sf)
        (by intro sf; dsimp only [polyNextChunkSpec]; ac_rfl) ?_
      intro sm2 hpc_sm2 hrun_sm2 hsp_sm2 htr_sm2 hinv_sm2
        hx19_sm2 hx20_sm2 hx21_sm2 hx22_sm2 hx23_sm2 hx24_sm2 hx25_sm2 hx26_sm2 hx27_sm2 hx28_sm2 hvregs_sm2
      simp only [Reg.x19, Reg.x20, Reg.x21, Reg.x22, Reg.x23, Reg.x24, Reg.x25, Reg.x26, Reg.x27, Reg.x28,
        wp_norm, arm64_norm, *] at htr_sm2 hx19_sm2 hx20_sm2 hx21_sm2 hx22_sm2 hx23_sm2 hx24_sm2 hx25_sm2 hx26_sm2 hx27_sm2 hx28_sm2 hvregs_sm2
      apply of_sepWP_inImage (mid := entry + 1896#64) img hinv_sm2
      refine finish_sepWP_inImage hpc_sm2 hrun_sm2
        (fun hinv4 => hnext sm2 g' (sf1.readReg64 (Reg.gpr 0#5)) hinv4 hne0_1 h0b_1
          hpc_sm2 hrun_sm2 hsp_sm2
          hx19_sm2 hx20_sm2 hx21_sm2 hx22_sm2 hx23_sm2 hx24_sm2 hx25_sm2 hx26_sm2 hx27_sm2 hx28_sm2 htr_sm2 hvregs_sm2)
        (Entails.of_eq (by ac_rfl))
    obtain ⟨tag, htag01, encRest, henc_split⟩ := polyEncoderAt_split_tag A (sp + 7136#64) sending_ct1
    rcases htag01 with rfl | rfl
    · wp_conv_pre => rw [henc_split]
      wp_steps
      wp_conv_pre => rw [← henc_split]
      exact h1868 _ (by wp_norm_goal) (by simp only [wp_norm, arm64_norm, *])
        (by simp only [State.sp, arm64_norm, *]) (by simp only [wp_norm, arm64_norm, *])
        (by simp only [wp_norm, arm64_norm, *])
        (by simp only [Reg.lr, arm64_norm, *]) (by simp only [Reg.x0, arm64_norm, *])
        (by simp only [Reg.x1, arm64_norm, *]) (by simp only [Reg.x2, arm64_norm])
        (by simp only [Reg.x19, arm64_norm, *]) (by simp only [Reg.x20, arm64_norm, *])
        (by simp only [Reg.x21, arm64_norm, *]) (by simp only [Reg.x22, arm64_norm, *])
        (by simp only [Reg.x23, arm64_norm, *]) (by simp only [Reg.x24, arm64_norm, *])
        (by simp only [Reg.x25, arm64_norm, *]) (by simp only [Reg.x26, arm64_norm, *])
        (by simp only [Reg.x27, arm64_norm, *])
    · wp_conv_pre => rw [henc_split]
      wp_steps
      wp_conv_pre => rw [← henc_split]
      exact h1868 _ (by wp_norm_goal) (by simp only [wp_norm, arm64_norm, *])
        (by simp only [State.sp, arm64_norm, *]) (by simp only [wp_norm, arm64_norm, *])
        (by simp only [wp_norm, arm64_norm, *])
        (by simp only [Reg.lr, arm64_norm, *]) (by simp only [Reg.x0, arm64_norm, *])
        (by simp only [Reg.x1, arm64_norm, *]) (by simp only [Reg.x2, arm64_norm])
        (by simp only [Reg.x19, arm64_norm, *]) (by simp only [Reg.x20, arm64_norm, *])
        (by simp only [Reg.x21, arm64_norm, *]) (by simp only [Reg.x22, arm64_norm, *])
        (by simp only [Reg.x23, arm64_norm, *]) (by simp only [Reg.x24, arm64_norm, *])
        (by simp only [Reg.x25, arm64_norm, *]) (by simp only [Reg.x26, arm64_norm, *])
        (by simp only [Reg.x27, arm64_norm, *])

/-! ## Sub-Step 4 (`entry + 1896#64 -> entry + 3068#64`) -/

theorem fnAddr_adrp_310b4 {b : BitVec 64} {H : String → Option (State → State)}
    (hb : b &&& 0xfff#64 = 0#64) :
    (((libsignalSessionCode.rebase b H).fnAddr spqrSendName + 2136#64) &&&
      0xfffffffffffff000#64) = b + page% ((ls_off% "spqr::send::<libsignal_session::HookRng>") + 2136) := by
  rw [Program.fnAddr_rebase, spqrSend_fnOff]
  revert hb; bv_bits

theorem Relocatable.of_authenticatorAt (A : RustAlloc) (auth : Authenticator) :
    Relocatable 48 (fun a => authenticatorAt A a auth) := by
  intro src
  refine Entails.trans (authenticatorAt_extract A src auth) ?_
  apply ProofLib.Entails.sepExists_elim; intro g
  rw [wordsAt_eq_pointsToBytes]
  refine Entails.sepExists_right (wordsBytes (authWordsList g)) ?_
  have hlen : (wordsBytes (authWordsList g)).length = 48 := by
    rw [length_wordsBytes, length_authWordsList]
  exact Entails.pure_right hlen (Entails.refl _)

theorem Relocatable.of_polyEncoder_and_auth (A : RustAlloc) (enc : PolyEncoder) (auth : Authenticator) :
    Relocatable 448 (fun a => polyEncoderAt A a enc ∗ authenticatorAt A (a + 400#64) auth) :=
  Relocatable.sepConj (off := 400#64) (m := 448) rfl rfl
    (Relocatable.of_polyEncoderAt A enc) (Relocatable.of_authenticatorAt A auth)

theorem live_pointsTo_entails_vecU8 {A : RustAlloc} (a cap ptr : BitVec 64) (bs : Bytes)
    (hlen : bs.length = cap.toNat) (hpos : 0 < cap.toNat) (hlt : cap.toNat < 2 ^ 63)
    (hptr : ptr ≠ 0) :
    (a ↦₆₄ cap) ∗ ((a + 8#64) ↦₆₄ ptr) ∗ ((a + 16#64) ↦₆₄ cap) ∗
    A.live ptr cap.toNat 1 ∗ (ptr ↦ₛ bs) ⊢
    vecU8 A a bs := by
  have hlen_bv : BitVec.ofNat 64 bs.length = cap := by simp [hlen]
  refine Entails.trans (sepConj_mono (Entails.refl _) (sepConj_mono (Entails.refl _)
    (sepConj_mono (Entails.refl _) ?_))) (fold_vecU8_of_inline a cap ptr cap bs hlen_bv)
  unfold RustHeap.vecU8Buf
  have hc : cap ≠ 0 := by intro h0; subst h0; revert hpos; decide
  simp only [hlen, hc, ↓reduceIte, Nat.sub_self, ProofLib.memRegion_zero, sepConj_emp]
  exact Entails.pure_right ⟨Nat.le_refl _, hlt, hptr⟩ (Entails.refl _)

theorem fold_chunkedCt1SampledAt_4704 {F : ShaCompress} {A : RustAlloc}
    (sp epoch hdr_cap hdr_ptr es_ptr ct1_ptr : BitVec 64)
    (auth' : Authenticator) (hdr : Bytes)
    (es : List.Vector (BitVec 8) 2080) (ct1 : List.Vector (BitVec 8) 960)
    (st : Chunked.SendCt.HeaderReceived spqrPolyApi (spqrAuthApi F))
    (outSt : Chunked.SendCt.Ct1Sampled spqrPolyApi (spqrAuthApi F))
    (huc : outSt.uc = { epoch := epoch, auth := auth', hdr := hdr, es := es.toList, ct1 := ct1.toList })
    (hrek : outSt.receiving_ek = st.receiving_ek)
    (hct1_ne : ct1_ptr ≠ 0) :
    polyEncoderAt A (sp + 4704#64) outSt.sending_ct1 ∗
    authenticatorAt A (sp + 5104#64) auth' ∗
    (((sp + 5152#64) ↦₆₄ hdr_cap) ∗ ((sp + 5160#64) ↦₆₄ hdr_ptr) ∗
     ((sp + 5168#64) ↦₆₄ BitVec.ofNat 64 hdr.length) ∗ (hdr_ptr ↦ₛ hdr) ∗ vecU8Rest A hdr_cap hdr_ptr hdr) ∗
    (((sp + 5176#64) ↦₆₄ 2080#64) ∗ ((sp + 5184#64) ↦₆₄ es_ptr) ∗ ((sp + 5192#64) ↦₆₄ 2080#64) ∗
     RustHeap.vecU8Buf A 2080#64 es_ptr es.toList) ∗
    (((sp + 5200#64) ↦₆₄ 960#64) ∗ ((sp + 5208#64) ↦₆₄ ct1_ptr) ∗ ((sp + 5216#64) ↦₆₄ 960#64) ∗
     A.live ct1_ptr 960 1 ∗ (ct1_ptr ↦ₛ ct1.toList)) ∗
    ((sp + 5224#64) ↦₆₄ epoch) ∗
    polyDecoderAt A (sp + 5232#64) st.receiving_ek ⊢
    ((sp + 4704#64) ↦₆₄ polyEncoderTagVal outSt.sending_ct1.s) ∗
    chunkedCt1SampledTail920At A (sp + 4712#64) outSt := by
  rw [← show (sp + 4704#64) + 8#64 = sp + 4712#64 by bv_omega,
      ← chunkedCt1SampledAt_eq_tag_tail920 A (sp + 4704#64) outSt]
  unfold chunkedCt1SampledAt unchunkedCt1SentAt
  rw [huc, hrek]
  have hhdr := vecU8_fold_rest (A := A) (sp + 5152#64) hdr_cap hdr_ptr hdr
  have hes := fold_vecU8_of_inline (A := A) (sp + 5176#64) 2080#64 es_ptr 2080#64 es.toList
    (by rw [List.Vector.toList_length])
  have hct1 := live_pointsTo_entails_vecU8 (A := A) (sp + 5200#64) 960#64 ct1_ptr ct1.toList
    (List.Vector.toList_length ct1) (by decide) (by decide) hct1_ne
  simp only [BitVec.add_assoc, arm64_norm] at hhdr hes hct1
  refine Entails.trans (sepConj_mono (Entails.refl _)
    (sepConj_mono (Entails.refl _)
      (sepConj_mono hhdr (sepConj_mono hes (sepConj_mono hct1 (Entails.refl _)))))) ?_
  simp only [BitVec.add_assoc, arm64_norm]
  exact Entails.of_eq (by ac_rfl)

theorem chunkAt_5632_4192_1360_eq (sp : BitVec 64) (chunk : Chunk) (cw0 cw1 cw2 cw3 : BitVec 64)
    (hchunk : ∀ a : BitVec 64, chunkAt a chunk =
      (a ↦₆₄ cw0) ∗ ((a + 8#64) ↦₆₄ cw1) ∗ ((a + 16#64) ↦₆₄ cw2) ∗ ((a + 24#64) ↦₆₄ cw3) ∗ ((a + 32#64) ↦₁₆ chunk.index)) :
    chunkAt (sp + 5632#64) chunk =
      ((sp + 5632#64) ↦₆₄ cw0) ∗ ((sp + 5640#64) ↦₆₄ cw1) ∗ ((sp + 5648#64) ↦₆₄ cw2) ∗ ((sp + 5656#64) ↦₆₄ cw3) ∗ ((sp + 5664#64) ↦₁₆ chunk.index) ∧
    chunkAt (sp + 4192#64) chunk =
      ((sp + 4192#64) ↦₆₄ cw0) ∗ ((sp + 4200#64) ↦₆₄ cw1) ∗ ((sp + 4208#64) ↦₆₄ cw2) ∗ ((sp + 4216#64) ↦₆₄ cw3) ∗ ((sp + 4224#64) ↦₁₆ chunk.index) ∧
    chunkAt (sp + 1360#64) chunk =
      ((sp + 1360#64) ↦₆₄ cw0) ∗ ((sp + 1368#64) ↦₆₄ cw1) ∗ ((sp + 1376#64) ↦₆₄ cw2) ∗ ((sp + 1384#64) ↦₆₄ cw3) ∗ ((sp + 1392#64) ↦₁₆ chunk.index) :=
  ⟨chunkAt_sp_add_eq sp 5632#64 5640#64 5648#64 5656#64 5664#64 chunk cw0 cw1 cw2 cw3 hchunk,
   chunkAt_sp_add_eq sp 4192#64 4200#64 4208#64 4216#64 4224#64 chunk cw0 cw1 cw2 cw3 hchunk,
   chunkAt_sp_add_eq sp 1360#64 1368#64 1376#64 1384#64 1392#64 chunk cw0 cw1 cw2 cw3 hchunk⟩

theorem memRegion_4192_merge_400 (sp : BitVec 64) :
    memRegion (sp + 4192#64) 48 ∗ memRegion (sp + 4240#64) 352 = memRegion (sp + 4192#64) 400 :=
  (ProofLib.memRegion_split' (b := sp + 4192#64) (n := 48) (k := 352) (b' := sp + 4240#64) rfl (by bv_omega) (by decide)).symm

theorem memRegion_4704_928_split (sp : BitVec 64) :
    memRegion (sp + 4704#64) 928 =
      memRegion (sp + 4704#64) 448 ∗ memRegion (sp + 5152#64) 80 ∗ memRegion (sp + 5232#64) 400 := by
  rw [ProofLib.memRegion_split' (b := sp + 4704#64) (n := 448) (k := 480) (b' := sp + 5152#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := sp + 5152#64) (n := 80) (k := 400) (b' := sp + 5232#64) rfl (by bv_omega) (by decide)]

theorem memRegion_5666_1438_split (sp : BitVec 64) :
    memRegion (sp + 5666#64) 1438 =
      memRegion (sp + 5666#64) 6 ∗ memRegion (sp + 5672#64) 32 ∗ memRegion (sp + 5704#64) 1400 := by
  rw [ProofLib.memRegion_split' (b := sp + 5666#64) (n := 6) (k := 1432) (b' := sp + 5672#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := sp + 5672#64) (n := 32) (k := 1400) (b' := sp + 5704#64) rfl (by bv_omega) (by decide)]

theorem memRegion_5152_80_eq_words10 (sp : BitVec 64) :
    memRegion (sp + 5152#64) 80 =
      (∃∗ d0 : BitVec 64, (sp + 5152#64) ↦₆₄ d0) ∗ (∃∗ d1 : BitVec 64, (sp + 5160#64) ↦₆₄ d1) ∗
      (∃∗ d2 : BitVec 64, (sp + 5168#64) ↦₆₄ d2) ∗ (∃∗ d3 : BitVec 64, (sp + 5176#64) ↦₆₄ d3) ∗
      (∃∗ d4 : BitVec 64, (sp + 5184#64) ↦₆₄ d4) ∗ (∃∗ d5 : BitVec 64, (sp + 5192#64) ↦₆₄ d5) ∗
      (∃∗ d6 : BitVec 64, (sp + 5200#64) ↦₆₄ d6) ∗ (∃∗ d7 : BitVec 64, (sp + 5208#64) ↦₆₄ d7) ∗
      (∃∗ d8 : BitVec 64, (sp + 5216#64) ↦₆₄ d8) ∗ (∃∗ d9 : BitVec 64, (sp + 5224#64) ↦₆₄ d9) := by
  rw [ProofLib.memRegion_split' (b := sp + 5152#64) (n := 64) (k := 16) (b' := sp + 5216#64) rfl (by bv_omega) (by decide),
      memRegion_64_eq_words8 (sp + 5152#64),
      ProofLib.memRegion_split' (b := sp + 5216#64) (n := 8) (k := 8) (b' := sp + 5224#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_eight (sp + 5216#64), ProofLib.memRegion_eight (sp + 5224#64)]
  simp only [BitVec.add_assoc, arm64_norm, sepConj_assoc]

theorem memRegion_5672_32_eq_words4 (sp : BitVec 64) :
    memRegion (sp + 5672#64) 32 =
      (∃∗ d0 : BitVec 64, (sp + 5672#64) ↦₆₄ d0) ∗ (∃∗ d1 : BitVec 64, (sp + 5680#64) ↦₆₄ d1) ∗
      (∃∗ d2 : BitVec 64, (sp + 5688#64) ↦₆₄ d2) ∗ (∃∗ d3 : BitVec 64, (sp + 5696#64) ↦₆₄ d3) := by
  rw [memRegion_32_eq_words4 (sp + 5672#64)]; simp only [BitVec.add_assoc, arm64_norm, sepConj_assoc]

theorem memRegion_4592_48_eq_words6 (sp : BitVec 64) :
    memRegion (sp + 4592#64) 48 =
      (∃∗ d0 : BitVec 64, (sp + 4592#64) ↦₆₄ d0) ∗ (∃∗ d1 : BitVec 64, (sp + 4600#64) ↦₆₄ d1) ∗
      (∃∗ d2 : BitVec 64, (sp + 4608#64) ↦₆₄ d2) ∗ (∃∗ d3 : BitVec 64, (sp + 4616#64) ↦₆₄ d3) ∗
      (∃∗ d4 : BitVec 64, (sp + 4624#64) ↦₆₄ d4) ∗ (∃∗ d5 : BitVec 64, (sp + 4632#64) ↦₆₄ d5) := by
  rw [memRegion_48_eq_words6 (sp + 4592#64)]; simp only [BitVec.add_assoc, arm64_norm, sepConj_assoc]

theorem memRegion_448_expose_chunk_slot (sp : BitVec 64) :
    memRegion (sp + 4192#64) 448 =
      (∃∗ d0 : BitVec 64, (sp + 4192#64) ↦₆₄ d0) ∗ (∃∗ d1 : BitVec 64, (sp + 4200#64) ↦₆₄ d1) ∗
      (∃∗ d2 : BitVec 64, (sp + 4208#64) ↦₆₄ d2) ∗ (∃∗ d3 : BitVec 64, (sp + 4216#64) ↦₆₄ d3) ∗
      (∃∗ d4 : BitVec 16, (sp + 4224#64) ↦₁₆ d4) ∗ memRegion (sp + 4226#64) 414 := by
  rw [ProofLib.memRegion_split' (b := sp + 4192#64) (n := 8) (k := 440) (b' := sp + 4200#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := sp + 4200#64) (n := 8) (k := 432) (b' := sp + 4208#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := sp + 4208#64) (n := 8) (k := 424) (b' := sp + 4216#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := sp + 4216#64) (n := 8) (k := 416) (b' := sp + 4224#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := sp + 4224#64) (n := 2) (k := 414) (b' := sp + 4226#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_eight (sp + 4192#64), ProofLib.memRegion_eight (sp + 4200#64),
      ProofLib.memRegion_eight (sp + 4208#64), ProofLib.memRegion_eight (sp + 4216#64),
      ProofLib.memRegion_two (sp + 4224#64)]

theorem memRegion_4064_16_eq_words2 (sp : BitVec 64) :
    memRegion (sp + 4064#64) 16 =
      (∃∗ d0 : BitVec 64, (sp + 4064#64) ↦₆₄ d0) ∗ (∃∗ d1 : BitVec 64, (sp + 4072#64) ↦₆₄ d1) := by
  rw [ProofLib.memRegion_split' (b := sp + 4064#64) (n := 8) (k := 8) (b' := sp + 4072#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_eight (sp + 4064#64), ProofLib.memRegion_eight (sp + 4072#64)]

theorem memRegion_1408_16_eq_words2 (sp : BitVec 64) :
    memRegion (sp + 1408#64) 16 =
      (∃∗ d0 : BitVec 64, (sp + 1408#64) ↦₆₄ d0) ∗ (∃∗ d1 : BitVec 64, (sp + 1416#64) ↦₆₄ d1) := by
  rw [ProofLib.memRegion_split' (b := sp + 1408#64) (n := 8) (k := 8) (b' := sp + 1416#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_eight (sp + 1408#64), ProofLib.memRegion_eight (sp + 1416#64)]

theorem fold_headerReceived_step5_regions (sp : BitVec 64) (chunk : Chunk)
    (w_tag w_4064 w_4072 w_5672 w_5680 w_5688 w_5696 w_7104 w_7112 w_7120 : BitVec 64) :
    (((sp + 4064#64) ↦₆₄ w_4064) ∗ ((sp + 4072#64) ↦₆₄ w_4072)) ∗
    (chunkAt (sp + 4192#64) chunk ∗ memRegion (sp + 4226#64) 414) ∗
    (((sp + 4704#64) ↦₆₄ w_tag) ∗ memRegion (sp + 4712#64) 920 ∗
     chunkAt (sp + 5632#64) chunk ∗ memRegion (sp + 5666#64) 6 ∗
     (((sp + 5672#64) ↦₆₄ w_5672) ∗ ((sp + 5680#64) ↦₆₄ w_5680) ∗
      ((sp + 5688#64) ↦₆₄ w_5688) ∗ ((sp + 5696#64) ↦₆₄ w_5696)) ∗
     memRegion (sp + 5704#64) 1400) ∗
    (((sp + 7104#64) ↦₆₄ w_7104) ∗ ((sp + 7112#64) ↦₆₄ w_7112) ∗ ((sp + 7120#64) ↦₆₄ w_7120)) ⊢
    memRegion (sp + 4064#64) 16 ∗ memRegion (sp + 4192#64) 448 ∗
    memRegion (sp + 4704#64) 2400 ∗ memRegion (sp + 7104#64) 24 := by
  have h4064 : ((sp + 4064#64) ↦₆₄ w_4064) ∗ ((sp + 4072#64) ↦₆₄ w_4072) ⊢ memRegion (sp + 4064#64) 16 := by
    rw [ProofLib.memRegion_split' (b := sp + 4064#64) (n := 8) (k := 8) (b' := sp + 4072#64) rfl (by bv_omega) (by decide)]
    exact sepConj_mono (ProofLib.pointsTo64_entails_memRegion _ _) (ProofLib.pointsTo64_entails_memRegion _ _)
  have h4192 : chunkAt (sp + 4192#64) chunk ∗ memRegion (sp + 4226#64) 414 ⊢ memRegion (sp + 4192#64) 448 := by
    rw [ProofLib.memRegion_split' (b := sp + 4192#64) (n := 34) (k := 414) (b' := sp + 4226#64) rfl (by bv_omega) (by decide)]
    exact sepConj_mono_left (chunkAt_entails_memRegion _ _)
  have h5672 := words4At_entails_memRegion (sp + 5672#64) w_5672 w_5680 w_5688 w_5696
  dsimp only [words4At] at h5672; simp only [BitVec.add_assoc, arm64_norm, sepConj_assoc] at h5672
  have h4704 :
      ((sp + 4704#64) ↦₆₄ w_tag) ∗ memRegion (sp + 4712#64) 920 ∗
      chunkAt (sp + 5632#64) chunk ∗ memRegion (sp + 5666#64) 6 ∗
      (((sp + 5672#64) ↦₆₄ w_5672) ∗ ((sp + 5680#64) ↦₆₄ w_5680) ∗
       ((sp + 5688#64) ↦₆₄ w_5688) ∗ ((sp + 5696#64) ↦₆₄ w_5696)) ∗
      memRegion (sp + 5704#64) 1400 ⊢ memRegion (sp + 4704#64) 2400 := by
    rw [ProofLib.memRegion_split' (b := sp + 4704#64) (n := 8) (k := 2392) (b' := sp + 4712#64) rfl (by bv_omega) (by decide),
        ProofLib.memRegion_split' (b := sp + 4712#64) (n := 920) (k := 1472) (b' := sp + 5632#64) rfl (by bv_omega) (by decide),
        ProofLib.memRegion_split' (b := sp + 5632#64) (n := 34) (k := 1438) (b' := sp + 5666#64) rfl (by bv_omega) (by decide),
        ProofLib.memRegion_split' (b := sp + 5666#64) (n := 6) (k := 1432) (b' := sp + 5672#64) rfl (by bv_omega) (by decide),
        ProofLib.memRegion_split' (b := sp + 5672#64) (n := 32) (k := 1400) (b' := sp + 5704#64) rfl (by bv_omega) (by decide)]
    exact sepConj_mono (ProofLib.pointsTo64_entails_memRegion _ _)
      (sepConj_mono (Entails.refl _) (sepConj_mono (chunkAt_entails_memRegion _ _)
        (sepConj_mono (Entails.refl _) (sepConj_mono h5672 (Entails.refl _)))))
  have h7104 := words3_7104_entails_memRegion sp w_7104 w_7112 w_7120
  exact sepConj_mono h4064 (sepConj_mono h4192 (sepConj_mono h4704 h7104))

theorem step_headerReceived_1896_to_3068 {F : ShaCompress}
    {img : Obj.Image} {A : RustAlloc} {ext : String → Option (State → State)}
    (hA : AllocContracts img.base A ext) (hbase : img.base &&& 0xfff#64 = 0#64)
    (sp epoch hdr_cap hdr_ptr es_ptr ct1_tmp_ptr ct1_ptr secret_cap secret_ptr : BitVec 64)
    (g' : AuthenticatorGhost) (auth' : Authenticator) (hdr : Bytes)
    (ct1 : List.Vector (BitVec 8) 960) (es : List.Vector (BitVec 8) 2080)
    (st : Chunked.SendCt.HeaderReceived spqrPolyApi (spqrAuthApi F))
    (outSt : Chunked.SendCt.Ct1Sampled spqrPolyApi (spqrAuthApi F)) (chunk : Chunk)
    (huc : outSt.uc = { epoch := epoch, auth := auth', hdr := hdr, es := es.toList, ct1 := ct1.toList })
    (hrek : outSt.receiving_ek = st.receiving_ek) (hct1_ne : ct1_ptr ≠ 0)
    {ret : BitVec 64} {s0 s : State} {P Frame R : SepProp} {post : State → SepProp → Prop}
    (hinv : ImgCallInv img s) (hsp_align : (sp &&& 15#64 == 0#64) = true)
    (hpc : s.pc = (tripleRatchetProgAtExt img.base ext).fnAddr spqrSendName + 1896#64)
    (hrun : s.status = .Running) (hsp : s.sp = sp)
    (hx20 : s.readReg64 .x20 = sp + 2384#64) (hx21 : s.readReg64 .x21 = hdr_ptr)
    (hx22 : s.readReg64 .x22 = epoch) (hx24 : s.readReg64 .x24 = es_ptr)
    (hx25 : s.readReg64 .x25 = ct1_tmp_ptr) (hx26 : s.readReg64 .x26 = sp + 4704#64)
    (hx27 : s.readReg64 .x27 = ct1_ptr) (hx28 : s.readReg64 .x28 = sp + 4704#64)
    (htrace : s.trace = s0.trace)
    (hP : P = (
      ((sp + 32#64) ↦₆₄ BitVec.ofNat 64 hdr.length) ∗ ((sp + 40#64) ↦₆₄ hdr_cap) ∗
      memRegion (sp + 400#64) 920 ∗ memRegion (sp + 1360#64) 38 ∗ memRegion (sp + 1408#64) 16 ∗
      memRegion (sp + 1424#64) 920 ∗ polyDecoderAt A (sp + 2472#64) st.receiving_ek ∗
      memRegion (sp + 4064#64) 16 ∗ authInlineWordsAt g' (sp + 4080#64) auth' ∗ authHeapBufs A g' auth' ∗
      memRegion (sp + 4192#64) 48 ∗ memRegion (sp + 4240#64) 352 ∗ memRegion (sp + 4592#64) 48 ∗
      memRegion (sp + 4704#64) 928 ∗ chunkAt (sp + 5632#64) chunk ∗ memRegion (sp + 5666#64) 1438 ∗
      (hdr_ptr ↦ₛ hdr) ∗ vecU8Rest A hdr_cap hdr_ptr hdr ∗
      RustHeap.vecU8Buf A 2080#64 es_ptr es.toList ∗
      A.live ct1_tmp_ptr 960 1 ∗ (ct1_tmp_ptr ↦ₛ ct1.toList) ∗
      A.live ct1_ptr 960 1 ∗ (ct1_ptr ↦ₛ ct1.toList) ∗
      ((sp + 7104#64) ↦₆₄ secret_cap) ∗ ((sp + 7112#64) ↦₆₄ secret_ptr) ∗ ((sp + 7120#64) ↦₆₄ 32#64) ∗
      polyEncoderAt A (sp + 7536#64) outSt.sending_ct1 ∗
      spqrLogLevelZeroAt img.base ∗ A.pool ∗ stackAt sp spqrSendCalleeStack) ∗ Frame)
    (hnext : ∀ sf : State, ImgCallInv img sf →
      sf.pc = (tripleRatchetProgAtExt img.base ext).fnAddr spqrSendName + 3068#64 →
      sf.status = .Running → sf.sp = sp →
      sf.readReg64 .x19 = s.readReg64 .x19 → sf.readReg64 .x20 = polyEncoderTagVal outSt.sending_ct1.s →
      sf.readReg64 .x21 = secret_cap → sf.readReg64 .x22 = epoch →
      sf.readReg64 .x24 = 5#64 → sf.readReg64 .x25 = sp + 1360#64 →
      sf.readReg64 .x26 = sp + 4704#64 → sf.readReg64 .x27 = secret_ptr →
      sf.readReg64 .x28 = sp + 4192#64 → sf.trace = s0.trace →
      calleeSavedVRegs sf = calleeSavedVRegs s →
      SepWPp (tripleRatchetProgAtExt img.base ext) ret sf
        ((((sp + 32#64) ↦₆₄ BitVec.ofNat 64 hdr.length) ∗ ((sp + 40#64) ↦₆₄ hdr_cap) ∗
          memRegion (sp + 400#64) 920 ∗ chunkAt (sp + 1360#64) chunk ∗ memRegion (sp + 1394#64) 4 ∗
          ((sp + 1408#64) ↦₆₄ 32#64) ∗ ((sp + 1416#64) ↦₆₄ epoch) ∗
          chunkedCt1SampledTail920At A (sp + 1424#64) outSt ∗
          memRegion (sp + 2472#64) 400 ∗ memRegion (sp + 4064#64) 16 ∗ memRegion (sp + 4080#64) 48 ∗
          memRegion (sp + 4192#64) 448 ∗ memRegion (sp + 4704#64) 2400 ∗
          memRegion (sp + 7104#64) 24 ∗ memRegion (sp + 7536#64) 400 ∗
          spqrLogLevelZeroAt img.base ∗ A.pool ∗ stackAt sp spqrSendCalleeStack) ∗ Frame) post
        (fun sf P_f => (sf.mem ⊨ P_f ∗ R) →
          (sf.mem ⊨ (⌜allocFailedIn s0 sf ∧ s0.trace <+: sf.trace⌝ ∗ anyHeap) ∗ R))) :
    SepWPp (tripleRatchetProgAtExt img.base ext) ret s P post
      (fun sf P_f => (sf.mem ⊨ P_f ∗ R) →
        (sf.mem ⊨ (⌜allocFailedIn s0 sf ∧ s0.trace <+: sf.trace⌝ ∗ anyHeap) ∗ R)) := by
  have hmemcpy := spqrSend_memcpy_ok hA
  have hdealloc := spqrSend_dealloc_ok hA
  have hct1_len : ct1.toList.length = 960 := List.Vector.toList_length _
  have hadrp := fnAddr_adrp_310b4 (H := Rust.withPanics ext) hbase
  spqr_send_fetches_range img.base (Rust.withPanics ext) 1896 476
  generalize_entry hentry : (tripleRatchetProgAtExt img.base ext).fnAddr spqrSendName = entry
  examples_hide_fetches; subst hP
  simp only [Reg.x20, Reg.x21, Reg.x22, Reg.x24, Reg.x25, Reg.x26, Reg.x27, Reg.x28]
    at hx20 hx21 hx22 hx24 hx25 hx26 hx27 hx28
  apply of_sepWP_inImage (mid := entry + 3068#64) img hinv
  rw [← sepConj_assoc (memRegion (sp + 4192#64) 48) (memRegion (sp + 4240#64) 352),
      memRegion_4192_merge_400 sp, memRegion_4704_928_split sp, memRegion_5666_1438_split sp]
  wp_steps
  refine call_memcpy_relocate hmemcpy (Relocatable.of_polyEncoderAt A outSt.sending_ct1)
    (sp + 4192#64) (sp + 7536#64) (s0 := s0) (sp_call := sp)
    (Frame := ((sp + 32#64) ↦₆₄ BitVec.ofNat 64 hdr.length) ∗ ((sp + 40#64) ↦₆₄ hdr_cap) ∗ memRegion (sp + 400#64) 920 ∗
      memRegion (sp + 1360#64) 38 ∗ memRegion (sp + 1408#64) 16 ∗ memRegion (sp + 1424#64) 920 ∗
      polyDecoderAt A (sp + 2472#64) st.receiving_ek ∗ memRegion (sp + 4064#64) 16 ∗
      authInlineWordsAt g' (sp + 4080#64) auth' ∗ authHeapBufs A g' auth' ∗ memRegion (sp + 4592#64) 48 ∗
      memRegion (sp + 4704#64) 448 ∗ memRegion (sp + 5152#64) 80 ∗ memRegion (sp + 5232#64) 400 ∗ chunkAt (sp + 5632#64) chunk ∗
      memRegion (sp + 5666#64) 6 ∗ memRegion (sp + 5672#64) 32 ∗ memRegion (sp + 5704#64) 1400 ∗
      (hdr_ptr ↦ₛ hdr) ∗ vecU8Rest A hdr_cap hdr_ptr hdr ∗ RustHeap.vecU8Buf A 2080#64 es_ptr es.toList ∗
      A.live ct1_tmp_ptr 960 1 ∗ (ct1_tmp_ptr ↦ₛ ct1.toList) ∗ A.live ct1_ptr 960 1 ∗ (ct1_ptr ↦ₛ ct1.toList) ∗
      ((sp + 7104#64) ↦₆₄ secret_cap) ∗ ((sp + 7112#64) ↦₆₄ secret_ptr) ∗ ((sp + 7120#64) ↦₆₄ 32#64) ∗
      spqrLogLevelZeroAt img.base ∗ A.pool ∗ stackAt sp spqrSendCalleeStack ∗ Frame)
    (by wp_norm_goal) (by simp only [wp_norm, arm64_norm, *]) (by simp only [State.sp, arm64_norm, *])
    hsp_align (ret_pc := entry + 1920#64) (by simp only [Reg.lr, arm64_norm, *])
    (by simp only [wp_norm, arm64_norm, *]) (by simp only [Reg.x0, arm64_norm, *])
    (by simp only [Reg.x1, arm64_norm, *]) (by simp only [Reg.x2, arm64_norm]) (by ac_rfl) ?_
  intro sf1 hpc1 hrun1 hsp1 htr1 hx19_1 hx20_1 hx21_1 hx22_1 _ hx24_1 hx25_1 hx26_1 hx27_1 hx28_1 hvregs_1
  simp only [wp_norm, arm64_norm, *] at hx19_1 hx20_1 hx21_1 hx22_1 hx24_1 hx25_1 hx26_1 hx27_1 hx28_1 hvregs_1
  rw [memRegion_4592_48_eq_words6 sp]
  wp_conv_pre => dsimp only [authInlineWordsAt]; simp only [BitVec.add_assoc, arm64_norm, sepExists_sepConj_left, sepExists_sepConj_right]
  iterate 6 (apply SepWP.exists_elim; intro _); wp_steps
  have hfold_4080_4592 :
      (((sp + 4080#64) ↦₆₄ g'.rootKey.cap) ∗ ((sp + 4088#64) ↦₆₄ g'.rootKey.ptr) ∗ ((sp + 4096#64) ↦₆₄ BitVec.ofNat 64 auth'.rootKey.length) ∗
       ((sp + 4104#64) ↦₆₄ g'.macKey.cap) ∗ ((sp + 4112#64) ↦₆₄ g'.macKey.ptr) ∗ ((sp + 4120#64) ↦₆₄ BitVec.ofNat 64 auth'.macKey.length)) ∗
      (((sp + 4592#64) ↦₆₄ g'.rootKey.cap) ∗ ((sp + 4600#64) ↦₆₄ g'.rootKey.ptr) ∗ ((sp + 4608#64) ↦₆₄ BitVec.ofNat 64 auth'.rootKey.length) ∗
       ((sp + 4616#64) ↦₆₄ g'.macKey.cap) ∗ ((sp + 4624#64) ↦₆₄ g'.macKey.ptr) ∗ ((sp + 4632#64) ↦₆₄ BitVec.ofNat 64 auth'.macKey.length) ∗
       authHeapBufs A g' auth') ⊢
      memRegion (sp + 4080#64) 48 ∗ authenticatorAt A ((sp + 4192#64) + 400#64) auth' := by
    have h1 := authInlineWordsAt_entails_memRegion g' (sp + 4080#64) auth'
    have h2 := fold_authenticatorAt_of_inline (A := A) g' (sp + 4592#64) auth'
    dsimp only [authInlineWordsAt] at h1 h2; simp only [BitVec.add_assoc, arm64_norm] at h1 h2
    rw [show (sp + 4192#64) + 400#64 = sp + 4592#64 by bv_omega]; exact sepConj_mono h1 h2
  refine SepWP.fold hfold_4080_4592 (by sep_focus) ?_; clear hfold_4080_4592
  refine call_memcpy_relocate hmemcpy (Relocatable.of_polyDecoderAt A st.receiving_ek)
    (sp + 5232#64) (sp + 2472#64) (s0 := s0) (sp_call := sp)
    (Frame := memRegion (sp + 4080#64) 48 ∗ polyEncoderAt A (sp + 4192#64) outSt.sending_ct1 ∗
      authenticatorAt A ((sp + 4192#64) + 400#64) auth' ∗ memRegion (sp + 7536#64) 400 ∗
      ((sp + 32#64) ↦₆₄ BitVec.ofNat 64 hdr.length) ∗ ((sp + 40#64) ↦₆₄ hdr_cap) ∗ memRegion (sp + 400#64) 920 ∗
      memRegion (sp + 1360#64) 38 ∗ memRegion (sp + 1408#64) 16 ∗ memRegion (sp + 1424#64) 920 ∗
      memRegion (sp + 4064#64) 16 ∗ memRegion (sp + 4704#64) 448 ∗ memRegion (sp + 5152#64) 80 ∗ chunkAt (sp + 5632#64) chunk ∗
      memRegion (sp + 5666#64) 6 ∗ memRegion (sp + 5672#64) 32 ∗ memRegion (sp + 5704#64) 1400 ∗
      (hdr_ptr ↦ₛ hdr) ∗ vecU8Rest A hdr_cap hdr_ptr hdr ∗ RustHeap.vecU8Buf A 2080#64 es_ptr es.toList ∗
      A.live ct1_tmp_ptr 960 1 ∗ (ct1_tmp_ptr ↦ₛ ct1.toList) ∗ A.live ct1_ptr 960 1 ∗ (ct1_ptr ↦ₛ ct1.toList) ∗
      ((sp + 7104#64) ↦₆₄ secret_cap) ∗ ((sp + 7112#64) ↦₆₄ secret_ptr) ∗ ((sp + 7120#64) ↦₆₄ 32#64) ∗
      spqrLogLevelZeroAt img.base ∗ A.pool ∗ stackAt sp spqrSendCalleeStack ∗ Frame)
    (by wp_norm_goal) (by simp only [wp_norm, arm64_norm, *]) (by simp only [State.sp, arm64_norm, *])
    hsp_align (ret_pc := entry + 1960#64) (by simp only [Reg.lr, arm64_norm, *])
    (by simp only [wp_norm, arm64_norm, *]) (by simp only [Reg.x0, arm64_norm, *])
    (by simp only [Reg.x1, arm64_norm, *]) (by simp only [Reg.x2, arm64_norm]) (by ac_rfl) ?_
  intro sf2 hpc2 hrun2 hsp2 htr2 hx19_2 _ hx21_2 hx22_2 _ hx24_2 hx25_2 hx26_2 hx27_2 hx28_2 hvregs_2
  simp only [wp_norm, arm64_norm, *] at hx19_2 hx21_2 hx22_2 hx24_2 hx25_2 hx26_2 hx27_2 hx28_2 hvregs_2
  wp_steps
  refine call_memcpy_relocate hmemcpy (Relocatable.of_polyEncoder_and_auth A outSt.sending_ct1 auth')
    (sp + 4704#64) (sp + 4192#64) (s0 := s0) (sp_call := sp)
    (Frame := polyDecoderAt A (sp + 5232#64) st.receiving_ek ∗
      memRegion (sp + 2472#64) 400 ∗ memRegion (sp + 4080#64) 48 ∗ memRegion (sp + 7536#64) 400 ∗
      ((sp + 32#64) ↦₆₄ BitVec.ofNat 64 hdr.length) ∗ ((sp + 40#64) ↦₆₄ hdr_cap) ∗ memRegion (sp + 400#64) 920 ∗
      memRegion (sp + 1360#64) 38 ∗ memRegion (sp + 1408#64) 16 ∗ memRegion (sp + 1424#64) 920 ∗
      memRegion (sp + 4064#64) 16 ∗ memRegion (sp + 5152#64) 80 ∗ chunkAt (sp + 5632#64) chunk ∗
      memRegion (sp + 5666#64) 6 ∗ memRegion (sp + 5672#64) 32 ∗ memRegion (sp + 5704#64) 1400 ∗
      (hdr_ptr ↦ₛ hdr) ∗ vecU8Rest A hdr_cap hdr_ptr hdr ∗ RustHeap.vecU8Buf A 2080#64 es_ptr es.toList ∗
      A.live ct1_tmp_ptr 960 1 ∗ (ct1_tmp_ptr ↦ₛ ct1.toList) ∗ A.live ct1_ptr 960 1 ∗ (ct1_ptr ↦ₛ ct1.toList) ∗
      ((sp + 7104#64) ↦₆₄ secret_cap) ∗ ((sp + 7112#64) ↦₆₄ secret_ptr) ∗ ((sp + 7120#64) ↦₆₄ 32#64) ∗
      spqrLogLevelZeroAt img.base ∗ A.pool ∗ stackAt sp spqrSendCalleeStack ∗ Frame)
    (by wp_norm_goal) (by simp only [wp_norm, arm64_norm, *]) (by simp only [State.sp, arm64_norm, *])
    hsp_align (ret_pc := entry + 1984#64) (by simp only [Reg.lr, arm64_norm, *])
    (by simp only [wp_norm, arm64_norm, *]) (by simp only [Reg.x0, arm64_norm, *])
    (by simp only [Reg.x1, arm64_norm, *]) (by simp only [Reg.x2, arm64_norm]) (by ac_rfl) ?_
  intro sf3 hpc3 hrun3 hsp3 htr3 hx19_3 _ hx21_3 hx22_3 _ hx24_3 hx25_3 hx26_3 hx27_3 hx28_3 hvregs_3
  simp only [wp_norm, arm64_norm, *] at hx19_3 hx21_3 hx22_3 hx24_3 hx25_3 hx26_3 hx27_3 hx28_3 hvregs_3
  rw [memRegion_5152_80_eq_words10 sp, memRegion_5672_32_eq_words4 sp]
  simp only [sepExists_sepConj_left, sepExists_sepConj_right]; iterate 14 (apply SepWP.exists_elim; intro _)
  have hct1_tmp_mem := pointsToBytes_entails_memRegion ct1_tmp_ptr ct1.toList; rw [hct1_len] at hct1_tmp_mem
  refine SepWP.fold hct1_tmp_mem (by sep_focus) ?_
  refine SepWP.fold (stackAt_spqrSendCallee_to_allocHook sp) (by sep_focus) ?_
  wp_steps; wp_apply
  refine SepWP.fold (stackAt_spqrSendCallee_from_allocHook sp) (by simp only [‹sf.sp = _›, hsp3]; sep_focus) ?_
  refine SepWP.fold (fold_chunkedCt1SampledAt_4704 sp epoch hdr_cap hdr_ptr es_ptr ct1_ptr auth' hdr es ct1 st outSt huc hrek hct1_ne) (by sep_focus) ?_
  wp_steps
  refine call_memcpy_relocate hmemcpy (Relocatable.of_chunkedCt1SampledTail920At A outSt)
    (sp + 400#64) (sp + 4712#64) (s0 := s0) (sp_call := sp)
    (Frame := stackAt sp spqrSendCalleeStack ∗ A.pool ∗ ((sp + 4704#64) ↦₆₄ polyEncoderTagVal outSt.sending_ct1.s) ∗
      ((sp + 5672#64) ↦₆₄ secret_cap) ∗ ((sp + 5680#64) ↦₆₄ secret_ptr) ∗ ((sp + 5688#64) ↦₆₄ 32#64) ∗ ((sp + 5696#64) ↦₆₄ epoch) ∗
      memRegion (sp + 4192#64) 448 ∗ memRegion (sp + 2472#64) 400 ∗ memRegion (sp + 4080#64) 48 ∗ memRegion (sp + 7536#64) 400 ∗
      ((sp + 32#64) ↦₆₄ BitVec.ofNat 64 hdr.length) ∗ ((sp + 40#64) ↦₆₄ hdr_cap) ∗
      memRegion (sp + 1360#64) 38 ∗ memRegion (sp + 1408#64) 16 ∗ memRegion (sp + 1424#64) 920 ∗
      memRegion (sp + 4064#64) 16 ∗ chunkAt (sp + 5632#64) chunk ∗ memRegion (sp + 5666#64) 6 ∗ memRegion (sp + 5704#64) 1400 ∗
      ((sp + 7104#64) ↦₆₄ secret_cap) ∗ ((sp + 7112#64) ↦₆₄ secret_ptr) ∗ ((sp + 7120#64) ↦₆₄ 32#64) ∗
      spqrLogLevelZeroAt img.base ∗ Frame)
    (by wp_norm_goal) (by simp only [wp_norm, arm64_norm, *]) (by simp only [State.sp, arm64_norm, *])
    hsp_align (ret_pc := entry + 2096#64) (by simp only [Reg.lr, arm64_norm, *])
    (by simp only [wp_norm, arm64_norm, *]) (by simp only [Reg.x0, arm64_norm, *])
    (by simp only [Reg.x1, arm64_norm, *]) (by simp only [Reg.x2, arm64_norm]) (by ac_rfl) ?_
  intro sf4 hpc4 hrun4 hsp4 htr4 hx19_4 hx20_4 _ hx22_4 _ _ _ hx26_4 _ hx28_4 hvregs_4
  simp only [wp_norm, arm64_norm, *] at hx19_4 hx20_4 hx22_4 hx26_4 hx28_4 hvregs_4
  obtain ⟨cw0, cw1, cw2, cw3, hchunk⟩ := chunkAt_extract_words chunk
  obtain ⟨hchunk_5632, hchunk_4192, hchunk_1360⟩ := chunkAt_5632_4192_1360_eq sp chunk cw0 cw1 cw2 cw3 hchunk
  rw [hchunk_5632, memRegion_448_expose_chunk_slot sp, memRegion_38_eq_chunk_slot sp, memRegion_4064_16_eq_words2 sp, memRegion_1408_16_eq_words2 sp]
  wp_conv_pre => dsimp only [spqrLogLevelZeroAt]; simp only [sepExists_sepConj_left, sepExists_sepConj_right]
  iterate 14 (apply SepWP.exists_elim; intro _); wp_steps
  have hfold_step5 :
      (((sp + 1360#64) ↦₆₄ cw0) ∗ ((sp + 1368#64) ↦₆₄ cw1) ∗ ((sp + 1376#64) ↦₆₄ cw2) ∗ ((sp + 1384#64) ↦₆₄ cw3) ∗ ((sp + 1392#64) ↦₁₆ chunk.index)) ∗
      (((sp + 4064#64) ↦₆₄ 32#64) ∗ ((sp + 4072#64) ↦₆₄ epoch)) ∗
      ((((sp + 4192#64) ↦₆₄ cw0) ∗ ((sp + 4200#64) ↦₆₄ cw1) ∗ ((sp + 4208#64) ↦₆₄ cw2) ∗ ((sp + 4216#64) ↦₆₄ cw3) ∗ ((sp + 4224#64) ↦₁₆ chunk.index)) ∗ memRegion (sp + 4226#64) 414) ∗
      (((sp + 4704#64) ↦₆₄ polyEncoderTagVal outSt.sending_ct1.s) ∗ memRegion (sp + 4712#64) 920 ∗
       (((sp + 5632#64) ↦₆₄ cw0) ∗ ((sp + 5640#64) ↦₆₄ cw1) ∗ ((sp + 5648#64) ↦₆₄ cw2) ∗ ((sp + 5656#64) ↦₆₄ cw3) ∗ ((sp + 5664#64) ↦₁₆ chunk.index)) ∗ memRegion (sp + 5666#64) 6 ∗
       (((sp + 5672#64) ↦₆₄ secret_cap) ∗ ((sp + 5680#64) ↦₆₄ secret_ptr) ∗ ((sp + 5688#64) ↦₆₄ 32#64) ∗ ((sp + 5696#64) ↦₆₄ epoch)) ∗ memRegion (sp + 5704#64) 1400) ∗
      (((sp + 7104#64) ↦₆₄ secret_cap) ∗ ((sp + 7112#64) ↦₆₄ secret_ptr) ∗ ((sp + 7120#64) ↦₆₄ 32#64)) ⊢
      chunkAt (sp + 1360#64) chunk ∗ memRegion (sp + 4064#64) 16 ∗ memRegion (sp + 4192#64) 448 ∗ memRegion (sp + 4704#64) 2400 ∗ memRegion (sp + 7104#64) 24 := by
    rw [← hchunk_1360, ← hchunk_4192, ← hchunk_5632]
    exact sepConj_mono_right (fold_headerReceived_step5_regions sp chunk
      (polyEncoderTagVal outSt.sending_ct1.s) 32#64 epoch secret_cap secret_ptr 32#64 epoch secret_cap secret_ptr 32#64)
  refine SepWP.fold hfold_step5 (by sep_focus) ?_; clear hfold_step5
  refine call_memcpy_relocate hmemcpy (Relocatable.of_chunkedCt1SampledTail920At A outSt)
    (sp + 1424#64) (sp + 400#64) (s0 := s0) (sp_call := sp)
    (Frame := chunkAt (sp + 1360#64) chunk ∗ memRegion (sp + 4064#64) 16 ∗ memRegion (sp + 4192#64) 448 ∗
      memRegion (sp + 4704#64) 2400 ∗ memRegion (sp + 7104#64) 24 ∗
      ((sp + 1408#64) ↦₆₄ 32#64) ∗ ((sp + 1416#64) ↦₆₄ epoch) ∗ memRegion (sp + 1394#64) 4 ∗
      stackAt sp spqrSendCalleeStack ∗ A.pool ∗ memRegion (sp + 2472#64) 400 ∗ memRegion (sp + 4080#64) 48 ∗ memRegion (sp + 7536#64) 400 ∗
      ((sp + 32#64) ↦₆₄ BitVec.ofNat 64 hdr.length) ∗ ((sp + 40#64) ↦₆₄ hdr_cap) ∗ spqrLogLevelZeroAt img.base ∗ Frame)
    (by wp_norm_goal) (by simp only [wp_norm, arm64_norm, *]) (by simp only [State.sp, arm64_norm, *])
    hsp_align (ret_pc := entry + 2344#64) (by simp only [Reg.lr, arm64_norm, *])
    (by simp only [wp_norm, arm64_norm, *]) (by simp only [Reg.x0, arm64_norm, *])
    (by simp only [Reg.x1, arm64_norm, *]) (by simp only [Reg.x2, arm64_norm])
    (by dsimp only [spqrLogLevelZeroAt]; ac_rfl) ?_
  intro sf5 hpc5 hrun5 hsp5 htr5 hx19_5 hx20_5 hx21_5 hx22_5 _ _ hx25_5 hx26_5 hx27_5 _ hvregs_5
  simp only [wp_norm, arm64_norm, *] at hx19_5 hx20_5 hx21_5 hx22_5 hx25_5 hx26_5 hx27_5 hvregs_5
  wp_steps
  refine finish_sepWP_inImage (by wp_norm_goal) (by simp only [wp_norm, arm64_norm, *])
    (fun hinv_f => hnext _ hinv_f
      (by wp_norm_goal) (by simp only [wp_norm, arm64_norm, *]) (by simp only [State.sp, arm64_norm, *])
      (by simp only [Reg.x19, arm64_norm, *]) (by simp only [Reg.x20, arm64_norm, *]) (by simp only [Reg.x21, arm64_norm, *])
      (by simp only [Reg.x22, arm64_norm, *]) (by simp only [Reg.x24, arm64_norm, *]) (by simp only [Reg.x25, arm64_norm, *])
      (by simp only [Reg.x26, arm64_norm, *]) (by simp only [Reg.x27, arm64_norm, *]) (by simp only [Reg.x28, arm64_norm, *])
      (by simp only [wp_norm, arm64_norm, *]) (by simp only [wp_norm, arm64_norm, *]))
    (Entails.of_eq (by ac_rfl))

theorem chunkedStatesAt_headerReceived_expose {F : ShaCompress} {A : RustAlloc}
    (sp : BitVec 64) (st : Chunked.SendCt.HeaderReceived spqrPolyApi (spqrAuthApi F)) :
    chunkedStatesAt A (sp + 0x950#64) (.headerReceived st) ⊢
    ∃∗ g : AuthenticatorGhost, ∃∗ hdr_cap : BitVec 64, ∃∗ hdr_ptr : BitVec 64,
      ⌜st.uc.hdr.length < 2 ^ 63⌝ ∗
      (((sp + 0x950#64) ↦₆₄ 8#64) ∗
       authInlineWordsAt g (sp + 2392#64) st.uc.auth ∗ authHeapBufs A g st.uc.auth ∗
       ((sp + 2440#64) ↦₆₄ hdr_cap) ∗ ((sp + 2448#64) ↦₆₄ hdr_ptr) ∗
       ((sp + 2456#64) ↦₆₄ BitVec.ofNat 64 st.uc.hdr.length) ∗
       (hdr_ptr ↦ₛ st.uc.hdr) ∗ vecU8Rest A hdr_cap hdr_ptr st.uc.hdr ∗
       ((sp + 2464#64) ↦₆₄ st.uc.epoch) ∗
       polyDecoderAt A (sp + 2472#64) st.receiving_ek ∗ memRegion (sp + 2872#64) 440) := by
  rw [chunkedStatesAt_eq_word0_tail920 A (sp + 0x950#64) (.headerReceived st)]
  dsimp only [chunkedStatesWord0, chunkedStatesTail920At, chunkedHeaderReceivedAt, unchunkedHeaderReceivedAt]
  have hauth := authenticatorAt_entails_exists_inline_heap A (sp + 2392#64) st.uc.auth
  have hhdr : vecU8 A (sp + 2440#64) st.uc.hdr ⊢
      ∃∗ hdr_cap : BitVec 64, ∃∗ hdr_ptr : BitVec 64, ⌜st.uc.hdr.length < 2 ^ 63⌝ ∗
        (((sp + 2440#64) ↦₆₄ hdr_cap) ∗ ((sp + 2448#64) ↦₆₄ hdr_ptr) ∗
         ((sp + 2456#64) ↦₆₄ BitVec.ofNat 64 st.uc.hdr.length) ∗
         (hdr_ptr ↦ₛ st.uc.hdr) ∗ vecU8Rest A hdr_cap hdr_ptr st.uc.hdr) := by
    unfold vecU8
    apply ProofLib.Entails.sepExists_elim; intro cap; apply ProofLib.Entails.sepExists_elim; intro ptr
    refine Entails.sepExists_right cap (Entails.sepExists_right ptr ?_)
    have hex := vecU8At_expose_rest (A := A) (sp + 2440#64) cap ptr st.uc.hdr
    simp only [BitVec.add_assoc, arm64_norm] at hex ⊢; exact hex
  simp only [BitVec.add_assoc, arm64_norm] at hauth hhdr ⊢
  refine Entails.trans (sepConj_mono_right (sepConj_mono hauth (sepConj_mono_left hhdr))) ?_
  simp only [sepExists_sepConj_left, sepExists_sepConj_right]
  apply ProofLib.Entails.sepExists_elim; intro cap
  apply ProofLib.Entails.sepExists_elim; intro ptr
  apply ProofLib.Entails.sepExists_elim; intro g
  refine Entails.sepExists_right g (Entails.sepExists_right cap (Entails.sepExists_right ptr ?_))
  exact Entails.of_eq (by ac_rfl)

theorem fold_arm_headerReceived_950 {F : ShaCompress} (sp hdr_cap hdr_ptr : BitVec 64)
    (g : AuthenticatorGhost) (st : Chunked.SendCt.HeaderReceived spqrPolyApi (spqrAuthApi F)) :
    ((sp + 0x950#64) ↦₆₄ 8#64) ∗ authInlineWordsAt g (sp + 2392#64) st.uc.auth ∗
    (((sp + 2440#64) ↦₆₄ hdr_cap) ∗ ((sp + 2448#64) ↦₆₄ hdr_ptr) ∗
     ((sp + 2456#64) ↦₆₄ BitVec.ofNat 64 st.uc.hdr.length) ∗ ((sp + 2464#64) ↦₆₄ st.uc.epoch)) ∗
    memRegion (sp + 2472#64) 400 ∗ memRegion (sp + 2872#64) 440 ⊢
    memRegion (sp + 0x950#64) 928 := by
  have h1 := authInlineWordsAt_entails_memRegion g (sp + 2392#64) st.uc.auth
  have h2 := words4At_entails_memRegion (sp + 2440#64) hdr_cap hdr_ptr
    (BitVec.ofNat 64 st.uc.hdr.length) st.uc.epoch
  dsimp only [words4At] at h2; simp only [BitVec.add_assoc, arm64_norm] at h2
  have h480 : memRegion (sp + 2392#64) 48 ∗ memRegion (sp + 2440#64) 32 ∗
      memRegion (sp + 2472#64) 400 ∗ memRegion (sp + 2872#64) 440 = memRegion (sp + 0x958#64) 920 := by
    rw [ProofLib.memRegion_split' (b := sp + 0x958#64) (n := 48) (k := 872) (b' := sp + 2440#64) rfl (by bv_omega) (by decide),
        ProofLib.memRegion_split' (b := sp + 2440#64) (n := 32) (k := 840) (b' := sp + 2472#64) rfl (by bv_omega) (by decide),
        ProofLib.memRegion_split' (b := sp + 2472#64) (n := 400) (k := 440) (b' := sp + 2872#64) rfl (by bv_omega) (by decide)]
  refine Entails.trans (sepConj_mono_right (sepConj_mono h1 (sepConj_mono_left h2))) ?_
  rw [h480]; exact word0_tail920_entails_memRegion_928 sp 8#64

/-- Top-level `*Ext` arm theorem for `.headerReceived st` (`entry + 1312#64 -> entry + 3068#64`, `0x30d7c -> 0x31458`). -/
theorem step_send_arm_headerReceived_ext {F : ShaCompress} {K : MlKem} {ctl : BitVec 64}
    (img : Obj.Image) (A : RustAlloc) (ext : String → Option (State → State))
    (himg : Obj.Loads libsignalSessionImage img) (hbase : img.base &&& 0xfff#64 = 0#64)
    (hA : AllocContracts img.base A ext) (hZero : HookSat ext allocZeroedName (rustAllocZeroedSpec A))
    (hrng : HookSat ext rngFillName (rngFillSpec ctl))
    (henc1 : HookSat ext mlkemEncaps1Name (mlkemEncaps1Spec K))
    (hhkdf : HkdfToVecOkExt img A (spqrHkdfWith F) ext) (hupd : AuthUpdateOkExt img F A ext)
    (henc : EncodeBytesOkX img A ext) (hnextChunk : PolyNextChunkOkX img A ext)
    {s0 s : State} (sp cur : BitVec 64) (tape tape' : Bytes)
    (st : Chunked.SendCt.HeaderReceived spqrPolyApi (spqrAuthApi F))
    (outSt : Chunked.SendCt.Ct1Sampled spqrPolyApi (spqrAuthApi F)) (chunk : Chunk) (ek : EpochSecret)
    (hroot_len : st.uc.auth.rootKey.length + 32 < 2 ^ 63)
    (hsend : st.send_ct1_chunk K tape = .ok (outSt, chunk, ek, tape'))
    {ret : BitVec 64} {P Frame Fr : SepProp} {post : State → SepProp → Prop} (hinv : ImgCallInv img s)
    (hpc : s.pc = (tripleRatchetProgAtExt img.base ext).fnAddr spqrSendName + 1312#64)
    (hrun : s.status = .Running) (hsp : s.sp = sp) (hsp_align : (sp &&& 15#64 == 0#64) = true)
    (htr : s.trace = s0.trace) (hx19 : s.readReg64 .x19 = s0.readReg64 .x19)
    (hx24 : s.readReg64 .x24 = sp + 0x950#64) (hx26 : s.readReg64 .x26 = sp + 0x1260#64)
    (hx28 : s.readReg64 .x28 = sp + 0x1060#64) (hx28_0 : s.readReg64 .x28 = s0.readReg64 .x28)
    (hvregs : calleeSavedVRegs s = calleeSavedVRegs s0)
    (hP : P = (stackAt sp spqrSendCalleeStack ∗ A.pool ∗ tokenInitAt img.base ∗ reduceTableAt img.base ∗
      spqrLogLevelZeroAt img.base ∗ tapeAt ctl cur tape ∗ chunkedStatesAt A (sp + 0x950#64) (.headerReceived st) ∗
      memRegion (sp + 32#64) 16 ∗ memRegion (sp + 400#64) 920 ∗
      memRegion (sp + 0x550#64) 38 ∗ memRegion (sp + 0x580#64) 16 ∗ memRegion (sp + 0x590#64) 920 ∗
      memRegion (sp + 4056#64) 8 ∗ memRegion (sp + 4064#64) 16 ∗ memRegion (sp + 4080#64) 48 ∗
      memRegion (sp + 4192#64) 448 ∗ memRegion (sp + 0x1260#64) 2400 ∗
      memRegion (sp + 7104#64) 24 ∗ memRegion (sp + 7136#64) 400 ∗ memRegion (sp + 7536#64) 400) ∗ Frame)
    (hnext : ∀ sf : State, ImgCallInv img sf →
      SpqrSendJoinState img.base sp ext s0 sf { epoch := st.uc.epoch, payload := .ct1 chunk } (.ct1Sampled outSt) →
      SepWPp (tripleRatchetProgAtExt img.base ext) ret sf
        ((stackAt sp spqrSendCalleeStack ∗ A.pool ∗ tokenInitAt img.base ∗ reduceTableAt img.base ∗
          spqrLogLevelZeroAt img.base ∗ tapeAfter ctl cur tape (tape.length - tape'.length) ∗
          memRegion (sp + 0x950#64) 928 ∗ memRegion (sp + 32#64) 16 ∗ memRegion (sp + 400#64) 920 ∗
          memRegion (sp + 4056#64) 8 ∗ memRegion (sp + 4064#64) 16 ∗ memRegion (sp + 4080#64) 48 ∗
          memRegion (sp + 4192#64) 448 ∗ memRegion (sp + 0x1260#64) 2400 ∗
          memRegion (sp + 7104#64) 24 ∗ memRegion (sp + 7136#64) 400 ∗ memRegion (sp + 7536#64) 400 ∗
          spqrSendPayloadSlotAt sp ((sf.readReg64 .x24).setWidth 8) (.ct1 chunk) ∗
          spqrSendKeySlotAt A sp (sf.readReg64 .x21) (sf.readReg64 .x27) (some ek) ∗
          chunkedStatesTail920At A (sp + 0x590#64) (.ct1Sampled outSt)) ∗ Frame) post
        (fun sf P_f => (sf.mem ⊨ P_f ∗ Fr) →
          (sf.mem ⊨ (⌜allocFailedIn s0 sf ∧ s0.trace <+: sf.trace⌝ ∗ anyHeap) ∗ Fr))) :
    SepWPp (tripleRatchetProgAtExt img.base ext) ret s P post
      (fun sf P_f => (sf.mem ⊨ P_f ∗ Fr) →
        (sf.mem ⊨ (⌜allocFailedIn s0 sf ∧ s0.trace <+: sf.trace⌝ ∗ anyHeap) ∗ Fr)) := by
  have hhkdf' : HkdfToVecOkExt img A (hkdfToVecUnchecked F) ext := hhkdf
  obtain ⟨h32, ct1, es, ss, sending_ct1, hencaps, henc_res, hnext_chunk, huc, hrek, hek, htape'⟩ :=
    send_ct1_chunk_ok_elim K st hsend
  let rand : List.Vector (BitVec 8) 32 := ⟨tape.take 32, by rw [List.length_take]; omega⟩
  subst hP
  apply of_sepWP_inImage (mid := (tripleRatchetProgAtExt img.base ext).fnAddr spqrSendName + 1312#64) img hinv
  refine SepWP.fold (chunkedStatesAt_headerReceived_expose sp st) (by sep_focus) ?_
  rw [ProofLib.memRegion_eight (sp + 4056#64),
      ProofLib.memRegion_split' (b := sp + 4192#64) (n := 48) (k := 400) (b' := sp + 4240#64) rfl (by rw [BitVec.add_assoc]; rfl) (by decide),
      ProofLib.memRegion_split' (b := sp + 4240#64) (n := 352) (k := 48) (b' := sp + 4592#64) rfl (by rw [BitVec.add_assoc]; rfl) (by decide),
      ProofLib.memRegion_split' (b := sp + 0x1260#64) (n := 961) (k := 1439) (b' := sp + 5665#64) rfl (by rw [BitVec.add_assoc]; rfl) (by decide),
      ProofLib.memRegion_split' (b := sp + 7136#64) (n := 32) (k := 368) (b' := sp + 7168#64) rfl (by rw [BitVec.add_assoc]; rfl) (by decide),
      ProofLib.memRegion_split' (b := sp + 7536#64) (n := 32) (k := 368) (b' := sp + 7568#64) rfl (by rw [BitVec.add_assoc]; rfl) (by decide),
      show (sp + 0x550#64 : BitVec 64) = sp + 1360#64 from rfl, show (sp + 0x580#64 : BitVec 64) = sp + 1408#64 from rfl,
      show (sp + 0x590#64 : BitVec 64) = sp + 1424#64 from rfl, show (sp + 0x1260#64 : BitVec 64) = sp + 4704#64 from rfl]
  simp only [sepExists_sepConj_left, sepExists_sepConj_right]
  apply SepWP.exists_elim; intro d4056; apply SepWP.exists_elim; intro g
  apply SepWP.exists_elim; intro hdr_cap; apply SepWP.exists_elim; intro hdr_ptr
  refine SepWP.fold (Entails.refl ⌜st.uc.hdr.length < 2 ^ 63⌝) (by sep_focus) ?_
  refine SepWP.pure_elim fun hhdr_lt => ?_
  apply SepWP.done hpc hrun; intro hinv0
  refine step_headerReceived_1312_to_1504 hA hZero hrng henc1 g st.uc.auth st.uc.epoch
    hdr_cap hdr_ptr st.uc.hdr hhdr_lt sp cur tape h32 rand rfl hencaps d4056
    (Frame := tokenInitAt img.base ∗ reduceTableAt img.base ∗ spqrLogLevelZeroAt img.base ∗
      memRegion (sp + 32#64) 16 ∗ memRegion (sp + 400#64) 920 ∗ memRegion (sp + 1360#64) 38 ∗
      memRegion (sp + 1408#64) 16 ∗ memRegion (sp + 1424#64) 920 ∗ memRegion (sp + 2872#64) 440 ∗
      memRegion (sp + 4064#64) 16 ∗ memRegion (sp + 4080#64) 48 ∗ memRegion (sp + 4240#64) 352 ∗
      memRegion (sp + 4592#64) 48 ∗ memRegion (sp + 5665#64) 1439 ∗ memRegion (sp + 7104#64) 24 ∗
      memRegion (sp + 7168#64) 368 ∗ memRegion (sp + 7568#64) 368 ∗ ((sp + 0x950#64) ↦₆₄ 8#64) ∗
      polyDecoderAt A (sp + 2472#64) st.receiving_ek ∗ vecU8Rest A hdr_cap hdr_ptr st.uc.hdr ∗ Frame)
    hinv0 hsp_align hpc hrun hsp hx24 hx26 hx28 htr (by ac_rfl) ?_
  intro s1 es_ptr ss_ptr hinv1 hes_ne hes_b hss_ne hss_b hpc1 hrun1 hsp1
    hx19_1 hx20_1 hx21_1 hx22_1 _ hx24_1 hx25_1 hx26_1 hx27_1 hx28_1 htr1 hvregs1
  refine step_headerReceived_1504_to_1680_ext himg hbase hA hhkdf' hupd
    sp st.uc.epoch hdr_cap hdr_ptr es_ptr ss_ptr g st.uc.auth st.uc.hdr ct1 ss hroot_len
    (Frame := authInlineWordsAt g (sp + 2392#64) st.uc.auth ∗ ((sp + 2440#64) ↦₆₄ hdr_cap) ∗
      ((sp + 2448#64) ↦₆₄ hdr_ptr) ∗ ((sp + 2456#64) ↦₆₄ BitVec.ofNat 64 st.uc.hdr.length) ∗ (hdr_ptr ↦ₛ st.uc.hdr) ∗
      ((sp + 2464#64) ↦₆₄ st.uc.epoch) ∗ ((sp + 4056#64) ↦₆₄ st.uc.epoch) ∗
      RustHeap.vecU8Buf A 2080#64 es_ptr es.toList ∗ memRegion (sp + 7136#64) 32 ∗ tapeAfter ctl cur tape 32 ∗
      tokenInitAt img.base ∗ reduceTableAt img.base ∗ spqrLogLevelZeroAt img.base ∗
      memRegion (sp + 400#64) 920 ∗ memRegion (sp + 1360#64) 38 ∗ memRegion (sp + 1408#64) 16 ∗
      memRegion (sp + 1424#64) 920 ∗ memRegion (sp + 2872#64) 440 ∗ memRegion (sp + 4064#64) 16 ∗
      memRegion (sp + 4080#64) 48 ∗ memRegion (sp + 4240#64) 352 ∗ memRegion (sp + 4592#64) 48 ∗
      memRegion (sp + 5665#64) 1439 ∗ memRegion (sp + 7104#64) 24 ∗ memRegion (sp + 7168#64) 368 ∗
      memRegion (sp + 7568#64) 368 ∗ ((sp + 0x950#64) ↦₆₄ 8#64) ∗ polyDecoderAt A (sp + 2472#64) st.receiving_ek ∗
      vecU8Rest A hdr_cap hdr_ptr st.uc.hdr ∗ Frame)
    hinv1 hsp_align hpc1 hrun1 hsp1 hx20_1 hx21_1 hx22_1 hx24_1 hx25_1 hx26_1 hx27_1 htr1 (by ac_rfl) ?_
  intro s2 ct1_ptr info_ptr secret_cap secret_ptr info secret auth' hinv2
    hct1_ne hct1_b hinfo_ne hinfo_b hsec_ne hsec_b hsec_ge hsec_lt
    hpc2 hrun2 hsp2 hx19_2 hx20_2 hx21_2 hx22_2 _ hx24_2 hx25_2 hx26_2 hx27_2 hx28_2 htr2 hvregs2
  have hinfo_len : info.length = 41 := by dsimp only [info]; rw [List.length_append, epochBeBytes_length]; rfl
  have hsec_len : secret.length = 32 := by
    change (List.take 32 (CryptoGames.HKDF.hkdfBlocks F (hkdfExtractBytes F (List.replicate 32 0#8) ss.toList) info 1).flatten).length = 32
    dsimp only [CryptoGames.HKDF.hkdfBlocks, List.nil_append, List.flatten_cons, List.flatten_nil]
    rw [List.length_take, List.append_nil, LibsignalSpqrV1.length_hmacWith]; rfl
  have hmerge_7136 : memRegion (sp + 7136#64) 32 ∗ memRegion (sp + 7168#64) 368 = memRegion (sp + 7136#64) 400 :=
    (ProofLib.memRegion_split' (b := sp + 7136#64) (n := 32) (k := 368) (b' := sp + 7168#64) rfl (by rw [BitVec.add_assoc]; rfl) (by decide)).symm
  refine step_headerReceived_1680_to_1896 hA hbase henc hnextChunk
    sp st.uc.epoch hdr_cap hdr_ptr es_ptr ct1_ptr info_ptr ss_ptr secret_cap secret_ptr
    auth' st.uc.hdr info secret ct1 ss sending_ct1 outSt chunk hinfo_len henc_res hnext_chunk
    (Frame := spqrLogLevelZeroAt img.base ∗ memRegion (sp + 1360#64) 38 ∗ memRegion (sp + 4064#64) 16 ∗
      memRegion (sp + 4240#64) 352 ∗ memRegion (sp + 4592#64) 48 ∗ authInlineWordsAt g (sp + 2392#64) st.uc.auth ∗
      ((sp + 2440#64) ↦₆₄ hdr_cap) ∗ ((sp + 2448#64) ↦₆₄ hdr_ptr) ∗
      ((sp + 2456#64) ↦₆₄ BitVec.ofNat 64 st.uc.hdr.length) ∗ (hdr_ptr ↦ₛ st.uc.hdr) ∗
      ((sp + 2464#64) ↦₆₄ st.uc.epoch) ∗ ((sp + 4056#64) ↦₆₄ st.uc.epoch) ∗
      RustHeap.vecU8Buf A 2080#64 es_ptr es.toList ∗ tapeAfter ctl cur tape 32 ∗
      memRegion (sp + 400#64) 920 ∗ memRegion (sp + 1408#64) 16 ∗ memRegion (sp + 1424#64) 920 ∗
      memRegion (sp + 2872#64) 440 ∗ ((sp + 0x950#64) ↦₆₄ 8#64) ∗ polyDecoderAt A (sp + 2472#64) st.receiving_ek ∗
      vecU8Rest A hdr_cap hdr_ptr st.uc.hdr ∗ Frame)
    hinv2 hsp_align hpc2 hrun2 hsp2 hx20_2 hx21_2 hx22_2 hx24_2 hx25_2 hx26_2 hx27_2 hx28_2 htr2
    (by rw [← hmerge_7136]; ac_rfl) ?_
  intro s3 g' ct1_ptr' hinv3 hct1'_ne hct1'_b
    hpc3 hrun3 hsp3 hx19_3 hx20_3 hx21_3 hx22_3 _ hx24_3 hx25_3 hx26_3 hx27_3 hx28_3 htr3 hvregs3
  refine step_headerReceived_1896_to_3068 hA hbase
    sp st.uc.epoch hdr_cap hdr_ptr es_ptr ct1_ptr ct1_ptr' secret_cap secret_ptr
    g' auth' st.uc.hdr ct1 es st outSt chunk huc hrek hct1'_ne
    (Frame := A.live secret_ptr secret_cap.toNat 1 ∗ (secret_ptr ↦ₛ secret) ∗
      memRegion (secret_ptr + 32#64) (secret_cap.toNat - 32) ∗ memRegion (sp + 7136#64) 400 ∗
      ((sp + 4056#64) ↦₆₄ st.uc.epoch) ∗ tapeAfter ctl cur tape 32 ∗
      ((sp + 2440#64) ↦₆₄ hdr_cap) ∗ ((sp + 2448#64) ↦₆₄ hdr_ptr) ∗
      ((sp + 2456#64) ↦₆₄ BitVec.ofNat 64 st.uc.hdr.length) ∗ ((sp + 2464#64) ↦₆₄ st.uc.epoch) ∗
      authInlineWordsAt g (sp + 2392#64) st.uc.auth ∗ ((sp + 0x950#64) ↦₆₄ 8#64) ∗
      memRegion (sp + 2872#64) 440 ∗ tokenInitAt img.base ∗ reduceTableAt img.base ∗ Frame)
    hinv3 hsp_align hpc3 hrun3 hsp3 hx20_3 hx21_3 hx22_3 hx24_3 hx25_3 hx26_3 hx27_3 hx28_3 htr3 (by ac_rfl) ?_
  intro sf hinv_f hpc_f hrun_f hsp_f hx19_f hx20_f hx21_f hx22_f hx24_f hx25_f hx26_f hx27_f hx28_f htr_f hvregs_f
  have htape_sub : tape.length - tape'.length = 32 := by rw [htape', List.length_drop]; omega
  refine SepWPp.mono_pre' ?_
    (hnext sf hinv_f ⟨hpc_f, hrun_f, hsp_f, htr_f,
      by rw [hx19_f, hx19_3, hx19_2, hx19_1, hx19], hx20_f, hx22_f, hx25_f, hx26_f,
      by rw [hx28_f, ← show sp + 0x1060#64 = sp + 4192#64 from rfl, ← hx28, hx28_0],
      by rw [hvregs_f, hvregs3, hvregs2, hvregs1, hvregs]⟩)
  rw [htape_sub, hx24_f, hx21_f, hx27_f]
  have h32_16 : ((sp + 32#64) ↦₆₄ BitVec.ofNat 64 st.uc.hdr.length) ∗ ((sp + 40#64) ↦₆₄ hdr_cap) ⊢ memRegion (sp + 32#64) 16 := by
    rw [ProofLib.memRegion_split' (b := sp + 32#64) (n := 8) (k := 8) (b' := sp + 40#64) rfl (by rw [BitVec.add_assoc]; rfl) (by decide)]
    exact sepConj_mono (ProofLib.pointsTo64_entails_memRegion _ _) (ProofLib.pointsTo64_entails_memRegion _ _)
  have h4056 := ProofLib.pointsTo64_entails_memRegion (sp + 4056#64) st.uc.epoch
  have h950 := fold_arm_headerReceived_950 sp hdr_cap hdr_ptr g st
  have hpay : chunkAt (sp + 1360#64) chunk ∗ memRegion (sp + 1394#64) 4 ⊢
      spqrSendPayloadSlotAt sp ((5#64 : BitVec 64).setWidth 8) (.ct1 chunk) := by
    dsimp only [spqrSendPayloadSlotAt]
    rw [show (sp + 0x550#64 : BitVec 64) = sp + 1360#64 from rfl, show (sp + 0x572#64 : BitVec 64) = sp + 1394#64 from rfl]
    exact Entails.pure_right rfl (Entails.refl _)
  have hkey : A.live secret_ptr secret_cap.toNat 1 ∗ (secret_ptr ↦ₛ secret) ∗
      memRegion (secret_ptr + 32#64) (secret_cap.toNat - 32) ∗
      ((sp + 1408#64) ↦₆₄ 32#64) ∗ ((sp + 1416#64) ↦₆₄ st.uc.epoch) ⊢
      spqrSendKeySlotAt A sp secret_cap secret_ptr (some ek) := by
    have hek_sec : ek.secret = secret := by rw [hek]
    have hek_ep : ek.epoch = st.uc.epoch := by rw [hek]
    have hc : secret_cap ≠ 0 := by intro h0; rw [h0] at hsec_b; contradiction
    dsimp only [spqrSendKeySlotAt, RustHeap.vecU8Buf]
    rw [hek_sec, hek_ep, hsec_len, show (sp + 0x580#64 : BitVec 64) = sp + 1408#64 from rfl,
        show (sp + 0x588#64 : BitVec 64) = sp + 1416#64 from rfl]
    simp only [hc, ↓reduceIte, show BitVec.ofNat 64 32 = 32#64 from rfl]
    refine Entails.pure_right hsec_lt ?_; rw [sepConj_assoc]
    exact Entails.pure_right ⟨hsec_ge, hsec_lt, hsec_ne⟩ (Entails.of_eq (by ac_rfl))
  have hrearr :
      (((sp + 32#64) ↦₆₄ BitVec.ofNat 64 st.uc.hdr.length) ∗ ((sp + 40#64) ↦₆₄ hdr_cap) ∗
       memRegion (sp + 400#64) 920 ∗ chunkAt (sp + 1360#64) chunk ∗ memRegion (sp + 1394#64) 4 ∗
       ((sp + 1408#64) ↦₆₄ 32#64) ∗ ((sp + 1416#64) ↦₆₄ st.uc.epoch) ∗ chunkedCt1SampledTail920At A (sp + 1424#64) outSt ∗
       memRegion (sp + 2472#64) 400 ∗ memRegion (sp + 4064#64) 16 ∗ memRegion (sp + 4080#64) 48 ∗
       memRegion (sp + 4192#64) 448 ∗ memRegion (sp + 4704#64) 2400 ∗ memRegion (sp + 7104#64) 24 ∗ memRegion (sp + 7536#64) 400 ∗
       spqrLogLevelZeroAt img.base ∗ A.pool ∗ stackAt sp spqrSendCalleeStack) ∗
      (A.live secret_ptr secret_cap.toNat 1 ∗ (secret_ptr ↦ₛ secret) ∗ memRegion (secret_ptr + 32#64) (secret_cap.toNat - 32) ∗
       memRegion (sp + 7136#64) 400 ∗ ((sp + 4056#64) ↦₆₄ st.uc.epoch) ∗ tapeAfter ctl cur tape 32 ∗
       ((sp + 2440#64) ↦₆₄ hdr_cap) ∗ ((sp + 2448#64) ↦₆₄ hdr_ptr) ∗ ((sp + 2456#64) ↦₆₄ BitVec.ofNat 64 st.uc.hdr.length) ∗ ((sp + 2464#64) ↦₆₄ st.uc.epoch) ∗
       authInlineWordsAt g (sp + 2392#64) st.uc.auth ∗ ((sp + 0x950#64) ↦₆₄ 8#64) ∗
       memRegion (sp + 2872#64) 440 ∗ tokenInitAt img.base ∗ reduceTableAt img.base ∗ Frame) =
      (((sp + 32#64) ↦₆₄ BitVec.ofNat 64 st.uc.hdr.length) ∗ ((sp + 40#64) ↦₆₄ hdr_cap)) ∗ ((sp + 4056#64) ↦₆₄ st.uc.epoch) ∗
      (((sp + 0x950#64) ↦₆₄ 8#64) ∗ authInlineWordsAt g (sp + 2392#64) st.uc.auth ∗
       (((sp + 2440#64) ↦₆₄ hdr_cap) ∗ ((sp + 2448#64) ↦₆₄ hdr_ptr) ∗ ((sp + 2456#64) ↦₆₄ BitVec.ofNat 64 st.uc.hdr.length) ∗ ((sp + 2464#64) ↦₆₄ st.uc.epoch)) ∗
       memRegion (sp + 2472#64) 400 ∗ memRegion (sp + 2872#64) 440) ∗
      (chunkAt (sp + 1360#64) chunk ∗ memRegion (sp + 1394#64) 4) ∗
      (A.live secret_ptr secret_cap.toNat 1 ∗ (secret_ptr ↦ₛ secret) ∗ memRegion (secret_ptr + 32#64) (secret_cap.toNat - 32) ∗
       ((sp + 1408#64) ↦₆₄ 32#64) ∗ ((sp + 1416#64) ↦₆₄ st.uc.epoch)) ∗
      (stackAt sp spqrSendCalleeStack ∗ A.pool ∗ tokenInitAt img.base ∗ reduceTableAt img.base ∗ spqrLogLevelZeroAt img.base ∗
       tapeAfter ctl cur tape 32 ∗ memRegion (sp + 400#64) 920 ∗ memRegion (sp + 4064#64) 16 ∗ memRegion (sp + 4080#64) 48 ∗
       memRegion (sp + 4192#64) 448 ∗ memRegion (sp + 4704#64) 2400 ∗ memRegion (sp + 7104#64) 24 ∗ memRegion (sp + 7136#64) 400 ∗ memRegion (sp + 7536#64) 400 ∗
       chunkedCt1SampledTail920At A (sp + 1424#64) outSt ∗ Frame) := by ac_rfl
  rw [hrearr]
  refine Entails.trans (sepConj_mono h32_16 (sepConj_mono h4056 (sepConj_mono h950
    (sepConj_mono hpay (sepConj_mono hkey (Entails.refl _)))))) ?_
  dsimp only [chunkedStatesTail920At]
  rw [show (sp + 0x590#64 : BitVec 64) = sp + 1424#64 from rfl, show (sp + 0x1260#64 : BitVec 64) = sp + 4704#64 from rfl]
  exact Entails.of_eq (by ac_rfl)

/-- Top-level arm theorem for `.headerReceived st` (`entry + 1312#64 -> entry + 3068#64`, `0x30d7c -> 0x31458`). -/
theorem step_send_arm_headerReceived {F : ShaCompress} {K : MlKem} {ctl : BitVec 64}
    (img : Obj.Image) (A : RustAlloc) (ext : String → Option (State → State))
    (himg : Obj.Loads libsignalSessionImage img) (hbase : img.base &&& 0xfff#64 = 0#64)
    (hA : AllocContracts img.base A ext) (hZero : HookSat ext allocZeroedName (rustAllocZeroedSpec A))
    (hrng : HookSat ext rngFillName (rngFillSpec ctl)) (henc1 : HookSat ext mlkemEncaps1Name (mlkemEncaps1Spec K))
    (hhkdf : HkdfToVecOkX img A (spqrHkdfWith F) ext) (hupd : AuthUpdateOkX img F A ext)
    (henc : EncodeBytesOkX img A ext) (hnextChunk : PolyNextChunkOkX img A ext)
    {s0 s : State} (sp cur : BitVec 64) (tape tape' : Bytes)
    (st : Chunked.SendCt.HeaderReceived spqrPolyApi (spqrAuthApi F))
    (outSt : Chunked.SendCt.Ct1Sampled spqrPolyApi (spqrAuthApi F)) (chunk : Chunk) (ek : EpochSecret)
    (hroot_len : st.uc.auth.rootKey.length + 32 < 2 ^ 63) (hsend : st.send_ct1_chunk K tape = .ok (outSt, chunk, ek, tape'))
    {ret : BitVec 64} {P Frame Fr : SepProp} {post : State → SepProp → Prop} (hinv : ImgCallInv img s)
    (hpc : s.pc = (tripleRatchetProgAtExt img.base ext).fnAddr spqrSendName + 1312#64)
    (hrun : s.status = .Running) (hsp : s.sp = sp) (hsp_align : (sp &&& 15#64 == 0#64) = true)
    (htr : s.trace = s0.trace) (hx19 : s.readReg64 .x19 = s0.readReg64 .x19)
    (hx24 : s.readReg64 .x24 = sp + 0x950#64) (hx26 : s.readReg64 .x26 = sp + 0x1260#64)
    (hx28 : s.readReg64 .x28 = sp + 0x1060#64) (hx28_0 : s.readReg64 .x28 = s0.readReg64 .x28)
    (hvregs : calleeSavedVRegs s = calleeSavedVRegs s0)
    (hP : P = (stackAt sp spqrSendCalleeStack ∗ A.pool ∗ tokenInitAt img.base ∗ reduceTableAt img.base ∗
      spqrLogLevelZeroAt img.base ∗ tapeAt ctl cur tape ∗ chunkedStatesAt A (sp + 0x950#64) (.headerReceived st) ∗
      memRegion (sp + 32#64) 16 ∗ memRegion (sp + 400#64) 920 ∗
      memRegion (sp + 0x550#64) 38 ∗ memRegion (sp + 0x580#64) 16 ∗ memRegion (sp + 0x590#64) 920 ∗
      memRegion (sp + 4056#64) 8 ∗ memRegion (sp + 4064#64) 16 ∗ memRegion (sp + 4080#64) 48 ∗
      memRegion (sp + 4192#64) 448 ∗ memRegion (sp + 0x1260#64) 2400 ∗
      memRegion (sp + 7104#64) 24 ∗ memRegion (sp + 7136#64) 400 ∗ memRegion (sp + 7536#64) 400) ∗ Frame)
    (hnext : ∀ sf : State, ImgCallInv img sf →
      SpqrSendJoinState img.base sp ext s0 sf { epoch := st.uc.epoch, payload := .ct1 chunk } (.ct1Sampled outSt) →
      SepWPp (tripleRatchetProgAtExt img.base ext) ret sf
        ((stackAt sp spqrSendCalleeStack ∗ A.pool ∗ tokenInitAt img.base ∗ reduceTableAt img.base ∗
          spqrLogLevelZeroAt img.base ∗ tapeAfter ctl cur tape (tape.length - tape'.length) ∗
          memRegion (sp + 0x950#64) 928 ∗ memRegion (sp + 32#64) 16 ∗ memRegion (sp + 400#64) 920 ∗
          memRegion (sp + 4056#64) 8 ∗ memRegion (sp + 4064#64) 16 ∗ memRegion (sp + 4080#64) 48 ∗
          memRegion (sp + 4192#64) 448 ∗ memRegion (sp + 0x1260#64) 2400 ∗
          memRegion (sp + 7104#64) 24 ∗ memRegion (sp + 7136#64) 400 ∗ memRegion (sp + 7536#64) 400 ∗
          spqrSendPayloadSlotAt sp ((sf.readReg64 .x24).setWidth 8) (.ct1 chunk) ∗
          spqrSendKeySlotAt A sp (sf.readReg64 .x21) (sf.readReg64 .x27) (some ek) ∗
          chunkedStatesTail920At A (sp + 0x590#64) (.ct1Sampled outSt)) ∗ Frame) post
        (fun sf P_f => (sf.mem ⊨ P_f ∗ Fr) →
          (sf.mem ⊨ (⌜allocFailedIn s0 sf ∧ s0.trace <+: sf.trace⌝ ∗ anyHeap) ∗ Fr))) :
    SepWPp (tripleRatchetProgAtExt img.base ext) ret s P post
      (fun sf P_f => (sf.mem ⊨ P_f ∗ Fr) →
        (sf.mem ⊨ (⌜allocFailedIn s0 sf ∧ s0.trace <+: sf.trace⌝ ∗ anyHeap) ∗ Fr)) :=
  step_send_arm_headerReceived_ext img A ext himg hbase hA hZero hrng henc1
    (hkdfToVecOkExt_of_okX hhkdf) (authUpdateOkExt_of_okX hupd) henc hnextChunk
    sp cur tape tape' st outSt chunk ek hroot_len hsend hinv hpc hrun hsp hsp_align
    htr hx19 hx24 hx26 hx28 hx28_0 hvregs hP hnext

end CryptoVerification.SpqrV1.Top.Send
