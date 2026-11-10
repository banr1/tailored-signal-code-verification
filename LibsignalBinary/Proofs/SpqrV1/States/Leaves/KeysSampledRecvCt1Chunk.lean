/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SpqrV1.States.Leaves.SendCt2Encoder
import GeneratedLean.LibsignalSessionCode -- shake: keep
import LibsignalBinary.Proofs.SpqrV1.Drop.PolyEncoder
import LibsignalBinary.Proofs.SpqrV1.Kdf.HkdfToSliceExtract
import LibsignalBinary.Proofs.SpqrV1.States.Leaves.SendChunk1
import LibsignalBinary.Proofs.TripleRatchet.GeneralizeEntry
import ProofLib.SepLogic.WPp

/-!
# `<spqr::v1::chunked::send_ek::KeysSampled>::recv_ct1_chunk` (`0x61768`)

**Checked by Lean.**

Verifies `keys_sampled_recv_ct1_chunk_ok_ext` (`0x61768`, 107 instructions) against
`keysSampledRecvCt1ChunkSpec A F`.
-/

@[expose] public section

namespace CryptoVerification.SpqrV1.States.Leaves

open Arm64 ProofLib ProofLib.ProgramReflection
open CryptoGames.LibsignalSession (ShaCompress)
open CryptoVerification.RustHeap
open CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalTripleRatchetRepr
open CryptoVerification.LibsignalSpqrV1
open CryptoVerification.SpqrV1.Auth
open CryptoVerification.SpqrV1.Poly
open CryptoVerification.SpqrV1.Poly.EncodeBytes
open CryptoVerification.SpqrV1.Poly.AddChunk
open CryptoVerification.SpqrV1.Drop
open CryptoVerification.SpqrV1.Alloc
open CryptoVerification.CodeLayout

set_option maxRecDepth 200000
set_option maxHeartbeats 400000
set_option linter.unusedSimpArgs false

attribute [local irreducible] libsignalSessionCode Program.fetch Program.externAt? Program.fnOff
attribute [-arm64_norm] keysSampledRecvCt1Chunk_fnOff libsignalSessionCode_fnOff_0x5c370
attribute [-arm64_norm]
  CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.sp_sub_688_eq_hsp
  CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.sp_add_neg688_eq_hsp
  CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.sp_sub_96_eq_hsp_592
  CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.sp_add_neg96_eq_hsp_592
attribute [local arm64_norm] bv_sub_add_lit bv_sub_sub BitVec.sub_add_cancel BitVec.toNat_zero

/-! ## 1. Instruction Decode Tree (`0x61768..0x61910`) -/

gen_decodes libsignalSessionCode_tree spqrKeysSampledRecvCt1ChunkBin [
  0x5c370 → 0x5c518
]

/-! ## 2. Pure Unfolding & Stack / Region Helpers -/

theorem keys_sampled_recv_ct1_chunk_ok_elim {F : ShaCompress}
    {st : Chunked.SendEk.KeysSampled spqrPolyApi (spqrAuthApi F)}
    {chunk : Chunk}
    {outSt : Chunked.SendEk.HeaderSent spqrPolyApi (spqrAuthApi F)}
    (h : st.recv_ct1_chunk st.uc.epoch chunk = .ok outSt) :
    encodeBytesResult st.uc.ek = .ok outSt.sending_ek ∧
    st.uc.ek.length ≤ 1048576 ∧
    outSt = { uc := { epoch := st.uc.epoch, auth := st.uc.auth, dk := st.uc.dk },
              sending_ek := outSt.sending_ek,
              receiving_ct1 := addChunkTotal (emptyPolyDecoder 480) chunk } := by
  unfold Chunked.SendEk.KeysSampled.recv_ct1_chunk at h
  simp only [bne_self_eq_false, Bool.false_eq_true, ↓reduceIte] at h
  change (do
    let receivingCt1 ← expectDecoderNew spqrPolyApi "v1/chunked/send_ek.rs:88" 960
    let receivingCt1 ← spqrPolyApi.add_chunk receivingCt1 chunk
    let sendingEk ← expectEncodeBytes spqrPolyApi "v1/chunked/send_ek.rs:92" st.uc.ek
    Except.ok { uc := { epoch := st.uc.epoch, auth := st.uc.auth, dk := st.uc.dk },
                sending_ek := sendingEk, receiving_ct1 := receivingCt1 }) =
      Except.ok outSt at h
  rw [expectDecoderNew_960] at h
  cases henc : expectEncodeBytes spqrPolyApi "v1/chunked/send_ek.rs:92" st.uc.ek with
  | error e =>
    rw [henc] at h
    dsimp only [Bind.bind, Except.bind, spqrPolyApi, liftM, monadLift, MonadLift.monadLift,
      liftSpqrPanic] at h
    rw [addChunk_eq_ok (emptyPolyDecoder 480) chunk rfl] at h
    contradiction
  | ok enc' =>
    rw [henc] at h
    dsimp only [Bind.bind, Except.bind, spqrPolyApi, liftM, monadLift, MonadLift.monadLift,
      liftSpqrPanic] at h
    rw [addChunk_eq_ok (emptyPolyDecoder 480) chunk rfl] at h
    dsimp only [Except.mapError] at h
    injection h with h
    subst h
    obtain ⟨hres, hle⟩ := encodeBytesResult_of_expectEncodeBytes_ok henc
    exact ⟨hres, hle, rfl⟩

attribute [local irreducible] addChunkTotal emptyPolyDecoder

@[local arm64_norm, local wp_norm] theorem sp_sub_80_sub_896 (sp : BitVec 64) :
    (sp - 80#64) - 896#64 = sp - 976#64 := by bv_omega
@[local arm64_norm, local wp_norm] theorem sp_sub_976_add_896 (sp : BitVec 64) :
    (sp - 976#64) + 896#64 = sp - 80#64 := by bv_omega
@[local arm64_norm, local wp_norm] theorem sp_sub_80_sub_80 (sp : BitVec 64) :
    (sp - 80#64) - 80#64 = sp - 160#64 := by bv_omega
@[local arm64_norm, local wp_norm] theorem sp_sub_80_sub_16 (sp : BitVec 64) :
    (sp - 80#64) - 16#64 = sp - 96#64 := by bv_omega
@[local arm64_norm, local wp_norm] theorem sp_sub_80_add_16' (sp : BitVec 64) :
    (sp - 80#64) + 16#64 = sp - 64#64 := by bv_omega
@[local arm64_norm, local wp_norm] theorem sp_sub_80_add_24' (sp : BitVec 64) :
    (sp - 80#64) + 24#64 = sp - 56#64 := by bv_omega
@[local arm64_norm, local wp_norm] theorem sp_sub_80_add_32' (sp : BitVec 64) :
    (sp - 80#64) + 32#64 = sp - 48#64 := by bv_omega
@[local arm64_norm, local wp_norm] theorem sp_sub_80_add_40' (sp : BitVec 64) :
    (sp - 80#64) + 40#64 = sp - 40#64 := by bv_omega
@[local arm64_norm, local wp_norm] theorem sp_sub_80_add_48' (sp : BitVec 64) :
    (sp - 80#64) + 48#64 = sp - 32#64 := by bv_omega
@[local arm64_norm, local wp_norm] theorem sp_sub_80_add_56' (sp : BitVec 64) :
    (sp - 80#64) + 56#64 = sp - 24#64 := by bv_omega
@[local arm64_norm, local wp_norm] theorem sp_sub_80_add_64' (sp : BitVec 64) :
    (sp - 80#64) + 64#64 = sp - 16#64 := by bv_omega
@[local arm64_norm, local wp_norm] theorem sp_sub_80_add_72' (sp : BitVec 64) :
    (sp - 80#64) + 72#64 = sp - 8#64 := by bv_omega
@[local arm64_norm, local wp_norm] theorem sp_sub_80_add_80' (sp : BitVec 64) :
    (sp - 80#64) + 80#64 = sp := by bv_omega

theorem wordsAt_9 (a : BitVec 64)
    (w0 w1 w2 w3 w4 w5 w6 w7 w8 : BitVec 64) :
    wordsAt a [w0, w1, w2, w3, w4, w5, w6, w7, w8] =
      (a ↦₆₄ w0) ∗ ((a + 8#64) ↦₆₄ w1) ∗ ((a + 16#64) ↦₆₄ w2) ∗ ((a + 24#64) ↦₆₄ w3) ∗
      ((a + 32#64) ↦₆₄ w4) ∗ ((a + 40#64) ↦₆₄ w5) ∗ ((a + 48#64) ↦₆₄ w6) ∗ ((a + 56#64) ↦₆₄ w7) ∗
      ((a + 64#64) ↦₆₄ w8) := by
  conv_lhs => rw [wordsAt]
  simp only [wordsAt_cons_off, wordsAt_nil, sepConj_emp,
    show (8#64 + 8#64 : BitVec 64) = 16#64 from rfl, show (16#64 + 8#64 : BitVec 64) = 24#64 from rfl,
    show (24#64 + 8#64 : BitVec 64) = 32#64 from rfl, show (32#64 + 8#64 : BitVec 64) = 40#64 from rfl,
    show (40#64 + 8#64 : BitVec 64) = 48#64 from rfl, show (48#64 + 8#64 : BitVec 64) = 56#64 from rfl,
    show (56#64 + 8#64 : BitVec 64) = 64#64 from rfl]

theorem cells_9_unfold (a : BitVec 64) :
    memRegion a 72 ⊢
      ∃∗ v0, ∃∗ v1, ∃∗ v2, ∃∗ v3, ∃∗ v4, ∃∗ v5, ∃∗ v6, ∃∗ v7, ∃∗ v8,
        wordsAt a [v0, v1, v2, v3, v4, v5, v6, v7, v8] := by
  rw [ProofLib.memRegion_cells a 9 (by decide), ProofLib.cells_succ]
  simp only [wordsAt_9, cells_succ_off, ProofLib.cells_zero, sepConj_emp, sepExists_sepConj_right,
    show (8#64 + 8#64 : BitVec 64) = 16#64 from rfl, show (16#64 + 8#64 : BitVec 64) = 24#64 from rfl,
    show (24#64 + 8#64 : BitVec 64) = 32#64 from rfl, show (32#64 + 8#64 : BitVec 64) = 40#64 from rfl,
    show (40#64 + 8#64 : BitVec 64) = 48#64 from rfl, show (48#64 + 8#64 : BitVec 64) = 56#64 from rfl,
    show (56#64 + 8#64 : BitVec 64) = 64#64 from rfl]
  exact Entails.refl _

theorem stackAt_976_split (sp : BitVec 64) :
    stackAt sp keysSampledRecvCt1ChunkStack =
      memRegion (sp - 17920#64) 12640 ∗ stackAt (sp - 976#64) addChunkStack ∗
      memRegion (sp - 976#64) 8 ∗ memRegion (sp - 968#64) 8 ∗
      memRegion (sp - 960#64) 128 ∗ memRegion (sp - 832#64) 128 ∗ memRegion (sp - 704#64) 128 ∗
      memRegion (sp - 576#64) 8 ∗ memRegion (sp - 568#64) 1 ∗ memRegion (sp - 567#64) 7 ∗
      memRegion (sp - 560#64) 400 ∗
      memRegion (sp - 160#64) 72 ∗ memRegion (sp - 88#64) 8 ∗
      memRegion (sp - 80#64) 80 := by
  change memRegion (sp - 17920#64) 17920 =
    memRegion (sp - 17920#64) 12640 ∗ memRegion (sp - 976#64 - 4304#64) 4304 ∗ _
  have hsub : sp - 976#64 - 4304#64 = sp - 5280#64 := by bv_omega
  rw [hsub,
      ProofLib.memRegion_split' (b := sp - 17920#64) (n := 12640) (k := 5280) (b' := sp - 5280#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := sp - 5280#64) (n := 4304) (k := 976) (b' := sp - 976#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := sp - 976#64) (n := 8) (k := 968) (b' := sp - 968#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := sp - 968#64) (n := 8) (k := 960) (b' := sp - 960#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := sp - 960#64) (n := 128) (k := 832) (b' := sp - 832#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := sp - 832#64) (n := 128) (k := 704) (b' := sp - 704#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := sp - 704#64) (n := 128) (k := 576) (b' := sp - 576#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := sp - 576#64) (n := 8) (k := 568) (b' := sp - 568#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := sp - 568#64) (n := 1) (k := 567) (b' := sp - 567#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := sp - 567#64) (n := 7) (k := 560) (b' := sp - 560#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := sp - 560#64) (n := 400) (k := 160) (b' := sp - 160#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := sp - 160#64) (n := 72) (k := 88) (b' := sp - 88#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := sp - 88#64) (n := 8) (k := 80) (b' := sp - 80#64) rfl (by bv_omega) (by decide)]

theorem stackAt_976_addChunk_to_encodeBytesX (sp : BitVec 64) :
    memRegion (sp - 17920#64) 12640 ∗ stackAt (sp - 976#64) addChunkStack ⊢
    stackAt (sp - 976#64) encodeBytesStackX := by
  change memRegion (sp - 17920#64) 12640 ∗ memRegion (sp - 976#64 - 4304#64) 4304 ⊢
    memRegion (sp - 976#64 - 16944#64) 16944
  have h1 : sp - 976#64 - 4304#64 = sp - 5280#64 := by bv_omega
  have h2 : sp - 976#64 - 16944#64 = sp - 17920#64 := by bv_omega
  rw [h1, h2, ← ProofLib.memRegion_split' (b := sp - 17920#64) (n := 12640) (k := 4304) (b' := sp - 5280#64) rfl (by bv_omega) (by decide)]
  exact Entails.refl _

theorem unchunkedHeaderSentAt_400_eq (A : RustAlloc) {F : ShaCompress}
    (stA : BitVec 64) (st : Unchunked.SendEk.HeaderSent (spqrAuthApi F)) :
    unchunkedHeaderSentAt A (stA + 400#64) st =
      authenticatorAt A (stA + 400#64) st.auth ∗
      vecU8 A (stA + 448#64) st.ek ∗
      vecU8 A (stA + 472#64) st.dk ∗
      ((stA + 496#64) ↦₆₄ st.epoch) := by
  unfold unchunkedHeaderSentAt
  simp only [BitVec.add_assoc, arm64_norm]

theorem stA_400_104_fold (stA : BitVec 64) (g : AuthWords)
    (ekCap ekPtr ekLen : BitVec 64) (gdk : VecWords) (ep : BitVec 64) :
    wordsAt (stA + 400#64) (authWordsList g) ∗
      ((stA + 448#64) ↦₆₄ ekCap) ∗ ((stA + 456#64) ↦₆₄ ekPtr) ∗ ((stA + 464#64) ↦₆₄ ekLen) ∗
      wordsAt (stA + 472#64) (vecWordsList gdk) ∗
      ((stA + 496#64) ↦₆₄ ep) ⊢
    memRegion (stA + 400#64) 104 := by
  have h1 : wordsAt (stA + 400#64) (authWordsList g) ⊢ memRegion (stA + 400#64) 48 :=
    wordsAt_entails_memRegion (authWordsList g) (stA + 400#64) 48 rfl
  have h2 :
      ((stA + 448#64) ↦₆₄ ekCap) ∗ ((stA + 456#64) ↦₆₄ ekPtr) ∗ ((stA + 464#64) ↦₆₄ ekLen) ⊢
      memRegion (stA + 448#64) 24 := by
    have heq :
        (((stA + 448#64) ↦₆₄ ekCap) ∗ ((stA + 456#64) ↦₆₄ ekPtr) ∗ ((stA + 464#64) ↦₆₄ ekLen)) =
        wordsAt (stA + 448#64) [ekCap, ekPtr, ekLen] := by
      simp only [wordsAt, wordsAt_cons_off, wordsAt_nil, sepConj_emp, BitVec.add_assoc, arm64_norm]
    rw [heq]; exact wordsAt_entails_memRegion [ekCap, ekPtr, ekLen] (stA + 448#64) 24 rfl
  have h3 : wordsAt (stA + 472#64) (vecWordsList gdk) ⊢ memRegion (stA + 472#64) 24 :=
    wordsAt_entails_memRegion (vecWordsList gdk) (stA + 472#64) 24 rfl
  have h4 : ((stA + 496#64) ↦₆₄ ep) ⊢ memRegion (stA + 496#64) 8 :=
    ProofLib.pointsTo64_entails_memRegion (stA + 496#64) ep
  have hreord :
      wordsAt (stA + 400#64) (authWordsList g) ∗
      ((stA + 448#64) ↦₆₄ ekCap) ∗ ((stA + 456#64) ↦₆₄ ekPtr) ∗ ((stA + 464#64) ↦₆₄ ekLen) ∗
      wordsAt (stA + 472#64) (vecWordsList gdk) ∗
      ((stA + 496#64) ↦₆₄ ep) =
      wordsAt (stA + 400#64) (authWordsList g) ∗
      (((stA + 448#64) ↦₆₄ ekCap) ∗ ((stA + 456#64) ↦₆₄ ekPtr) ∗ ((stA + 464#64) ↦₆₄ ekLen)) ∗
      wordsAt (stA + 472#64) (vecWordsList gdk) ∗
      ((stA + 496#64) ↦₆₄ ep) := by ac_rfl
  rw [hreord]
  refine Entails.trans (sepConj_mono h1 (sepConj_mono h2 (sepConj_mono h3 h4))) ?_
  rw [← ProofLib.memRegion_split' (b := stA + 472#64) (n := 24) (k := 8) (b' := stA + 496#64) rfl (by bv_omega) (by decide),
      ← ProofLib.memRegion_split' (b := stA + 448#64) (n := 24) (k := 32) (b' := stA + 472#64) rfl (by bv_omega) (by decide),
      ← ProofLib.memRegion_split' (b := stA + 400#64) (n := 48) (k := 56) (b' := stA + 448#64) rfl (by bv_omega) (by decide)]
  exact Entails.refl _

theorem outA_headerSent_recompose (A : RustAlloc) {F : ShaCompress}
    (outA sp : BitVec 64)
    (auth : Authenticator) (dk : Bytes) (epoch : Epoch)
    (sending_ek : PolyEncoder) (receiving_ct1 : PolyDecoder)
    (outSt : Chunked.SendEk.HeaderSent spqrPolyApi (spqrAuthApi F))
    (hout : outSt = { uc := { epoch := epoch, auth := auth, dk := dk },
                      sending_ek := sending_ek, receiving_ct1 := receiving_ct1 })
    (g : AuthWords) (gdk : VecWords) :
    polyEncoderAt A outA sending_ek ∗
      wordsAt (outA + 400#64) (authWordsList g) ∗
      relocatedHeap (fun dst => authenticatorAt A dst auth) (wordsBytes (authWordsList g)) ∗
      wordsAt (outA + 448#64) (vecWordsList gdk) ∗
      relocatedHeap (fun dst => vecU8 A dst dk) (wordsBytes (vecWordsList gdk)) ∗
      ((outA + 472#64) ↦₆₄ epoch) ∗
      polyDecoderAt A (outA + 480#64) receiving_ct1 ∗
      wordsAt (sp - 160#64) (authWordsList g ++ vecWordsList gdk) ⊢
    chunkedHeaderSentAt A outA outSt ∗ memRegion (sp - 160#64) 72 := by
  subst hout
  have hauth :
      wordsAt (outA + 400#64) (authWordsList g) ∗
        relocatedHeap (fun dst => authenticatorAt A dst auth) (wordsBytes (authWordsList g)) ⊢
      authenticatorAt A (outA + 400#64) auth := by
    rw [wordsAt_eq_pointsToBytes]; exact relocatedHeap_recompose _ _ (outA + 400#64)
  have hdk :
      wordsAt (outA + 448#64) (vecWordsList gdk) ∗
        relocatedHeap (fun dst => vecU8 A dst dk) (wordsBytes (vecWordsList gdk)) ⊢
      vecU8 A (outA + 448#64) dk := by
    rw [wordsAt_eq_pointsToBytes]; exact relocatedHeap_recompose _ _ (outA + 448#64)
  have hsp72 :
      wordsAt (sp - 160#64) (authWordsList g ++ vecWordsList gdk) ⊢
      memRegion (sp - 160#64) 72 :=
    wordsAt_entails_memRegion (authWordsList g ++ vecWordsList gdk) (sp - 160#64) 72 rfl
  have huc_eq :
      unchunkedEkSentAt A (outA + 400#64) ({ epoch := epoch, auth := auth, dk := dk } : Unchunked.SendEk.EkSent (spqrAuthApi F)) =
        authenticatorAt A (outA + 400#64) auth ∗
        vecU8 A (outA + 448#64) dk ∗
        ((outA + 472#64) ↦₆₄ epoch) := by
    unfold unchunkedEkSentAt
    simp only [BitVec.add_assoc, arm64_norm]
  unfold chunkedHeaderSentAt
  rw [huc_eq]
  have hreord :
      polyEncoderAt A outA sending_ek ∗
      wordsAt (outA + 400#64) (authWordsList g) ∗
      relocatedHeap (fun dst => authenticatorAt A dst auth) (wordsBytes (authWordsList g)) ∗
      wordsAt (outA + 448#64) (vecWordsList gdk) ∗
      relocatedHeap (fun dst => vecU8 A dst dk) (wordsBytes (vecWordsList gdk)) ∗
      ((outA + 472#64) ↦₆₄ epoch) ∗
      polyDecoderAt A (outA + 480#64) receiving_ct1 ∗
      wordsAt (sp - 160#64) (authWordsList g ++ vecWordsList gdk) =
      (polyEncoderAt A outA sending_ek ∗
        ((wordsAt (outA + 400#64) (authWordsList g) ∗
          relocatedHeap (fun dst => authenticatorAt A dst auth) (wordsBytes (authWordsList g))) ∗
         (wordsAt (outA + 448#64) (vecWordsList gdk) ∗
          relocatedHeap (fun dst => vecU8 A dst dk) (wordsBytes (vecWordsList gdk))) ∗
         ((outA + 472#64) ↦₆₄ epoch)) ∗
        polyDecoderAt A (outA + 480#64) receiving_ct1) ∗
      wordsAt (sp - 160#64) (authWordsList g ++ vecWordsList gdk) := by ac_rfl
  rw [hreord]
  exact sepConj_mono
    (sepConj_mono_right (sepConj_mono_left (sepConj_mono hauth (sepConj_mono_left hdk))))
    hsp72

theorem stackAt_976_to_dropPoly16 (s0 : State) (w8 d56 : BitVec 64) :
    stackAt (s0.sp - 976#64) encodeBytesStackX ∗
      memRegion (s0.sp - 976#64) 8 ∗
      ((s0.sp - 968#64) ↦₆₄ w8) ∗
      memRegion (s0.sp - 960#64) 400 ∗
      memRegion (s0.sp - 560#64) 400 ∗
      memRegion (s0.sp - 160#64) 72 ∗
      memRegion (s0.sp - 88#64) 8 ∗
      sendCt2SavedCells s0 d56 ⊢
    memRegion (s0.sp - 17920#64) 13792 ∗ stackAt s0.sp dropGluePoly16Stack := by
  have hw8 := ProofLib.pointsTo64_entails_memRegion (s0.sp - 968#64) w8
  have hsaved := sendCt2SavedCells_entails_memRegion_80 s0 d56
  refine Entails.trans (sepConj_mono_right (sepConj_mono_right (sepConj_mono hw8
    (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right hsaved))))))) ?_
  change memRegion (s0.sp - 976#64 - 16944#64) 16944 ∗
      (memRegion (s0.sp - 976#64) 8 ∗ (memRegion (s0.sp - 968#64) 8 ∗
        (memRegion (s0.sp - 960#64) 400 ∗ (memRegion (s0.sp - 560#64) 400 ∗
          (memRegion (s0.sp - 160#64) 72 ∗ (memRegion (s0.sp - 88#64) 8 ∗
            memRegion (s0.sp - 80#64) 80)))))) ⊢
    memRegion (s0.sp - 17920#64) 13792 ∗ memRegion (s0.sp - 4128#64) 4128
  have hsub : s0.sp - 976#64 - 16944#64 = s0.sp - 17920#64 := by bv_omega
  rw [hsub,
      ← ProofLib.memRegion_split' (b := s0.sp - 88#64) (n := 8) (k := 80) (b' := s0.sp - 80#64) rfl (by bv_omega) (by decide),
      ← ProofLib.memRegion_split' (b := s0.sp - 160#64) (n := 72) (k := 88) (b' := s0.sp - 88#64) rfl (by bv_omega) (by decide),
      ← ProofLib.memRegion_split' (b := s0.sp - 560#64) (n := 400) (k := 160) (b' := s0.sp - 160#64) rfl (by bv_omega) (by decide),
      ← ProofLib.memRegion_split' (b := s0.sp - 960#64) (n := 400) (k := 560) (b' := s0.sp - 560#64) rfl (by bv_omega) (by decide),
      ← ProofLib.memRegion_split' (b := s0.sp - 968#64) (n := 8) (k := 960) (b' := s0.sp - 960#64) rfl (by bv_omega) (by decide),
      ← ProofLib.memRegion_split' (b := s0.sp - 976#64) (n := 8) (k := 968) (b' := s0.sp - 968#64) rfl (by bv_omega) (by decide),
      ← ProofLib.memRegion_split' (b := s0.sp - 17920#64) (n := 16944) (k := 976) (b' := s0.sp - 976#64) rfl (by bv_omega) (by decide),
      ← ProofLib.memRegion_split' (b := s0.sp - 17920#64) (n := 13792) (k := 4128) (b' := s0.sp - 4128#64) rfl (by bv_omega) (by decide)]
  exact Entails.refl _

theorem stackAt_976_from_dropPoly16 (sp : BitVec 64) :
    memRegion (sp - 17920#64) 13792 ∗ stackAt sp dropGluePoly16Stack ⊢
    stackAt sp keysSampledRecvCt1ChunkStack := by
  change memRegion (sp - 17920#64) 13792 ∗ memRegion (sp - 4128#64) 4128 ⊢
    memRegion (sp - 17920#64) 17920
  rw [← ProofLib.memRegion_split' (b := sp - 17920#64) (n := 13792) (k := 4128) (b' := sp - 4128#64) rfl (by bv_omega) (by decide)]
  exact Entails.refl _

/-- Framed call rule for `rustDeallocSpec A` (`__rust_dealloc`). -/
theorem call_rustDealloc_cs {A : RustAlloc} {prog : Program} {entry ret_pc target_pc : BitVec 64}
    (hcall : subroutine_ok prog entry (rustDeallocSpec A))
    (ptr : BitVec 64) (size align : Nat)
    {s0 s : State} {sp_call : BitVec 64} {P Frame : SepProp}
    {post : State → SepProp → Prop}
    (hpc : s.pc = entry)
    (hrun : s.status = .Running)
    (hsp : s.sp = sp_call)
    (hsp_align : (sp_call &&& 15#64 == 0#64) = true)
    (hlr : s.readReg64 Reg.lr = ret_pc)
    (htrace : s.trace = s0.trace)
    (hx0 : s.readReg64 Reg.x0 = ptr)
    (hx1 : (s.readReg64 Reg.x1).toNat = size)
    (hx2 : (s.readReg64 Reg.x2).toNat = align)
    (hsplit : P = (A.pool ∗ A.live ptr size align ∗ memRegion ptr size ∗
      stackAt sp_call allocHookStack) ∗ Frame)
    (hnext : ∀ sf : State, sf.pc = ret_pc → sf.status = .Running →
      sf.sp = sp_call → CalleeSavedPreserved s sf → sf.trace = s0.trace →
      SepWP prog target_pc sf ((A.pool ∗ stackAt sp_call allocHookStack) ∗ Frame) post) :
    SepWP prog target_pc s P post := by
  refine SepWP.call_subroutine_frame hcall (x := (ptr, size, align)) (F := Frame)
    hpc hrun (by rw [State.spAligned, hsp]; exact hsp_align) hlr ?_
    (fun _ _ _ h => ((satisfies_pure_sepConj _ _ _).mp h).1)
    (fun _ _ _ _ h => ((satisfies_pure_sepConj _ _ _).mp h).1)
    (fun sf hpc_sf hrun_sf hsp_sf hcs_sf => ?_)
  · intro R hm
    rw [hsplit] at hm
    dsimp only [rustDeallocSpec]
    rw [hsp, sepConj_assoc, satisfies_pure_sepConj]
    exact ⟨⟨hx0, hx1, hx2⟩, by simpa only [sepConj_assoc] using hm⟩
  · dsimp only [rustDeallocSpec]
    rw [hsp, sepConj_assoc]
    refine SepWP.pure_elim fun htr => ?_
    exact hnext sf hpc_sf hrun_sf (hsp_sf.trans hsp) hcs_sf (htr.trans htrace)

/-! ## 3. Phase 2 (`entry + 236#64` = `0x61854`): `memcpy`s, `uc` copy, `dealloc`, and `drop_glue::<Poly16>` -/

@[simp] theorem trace_writeVReg128 (s : State) (r : BitVec 5) (v : BitVec 128) :
    (s.writeVReg128 r v).trace = s.trace := rfl

theorem satisfies_ac {m : Memory} {P Q : SepProp} (h : P = Q) (hm : m ⊨ P) : m ⊨ Q :=
  h ▸ hm

theorem sepWP_congr_pre {prog : Program} {target : BitVec 64} {s : State} {P P' : SepProp}
    {post : State → SepProp → Prop} (h : P = P') (hwp : SepWP prog target s P' post) :
    SepWP prog target s P post :=
  h ▸ hwp

set_option maxHeartbeats 600000 in
theorem keys_sampled_recv_ct1_chunk_tail {A : RustAlloc} {F : ShaCompress} {b : BitVec 64}
    {ext : String → Option (State → State)}
    (hdealloc : subroutine_ok (leavesProgAtExt b ext)
      ((leavesProgAtExt b ext).fnAddr keysSampledRecvCt1ChunkName +
        (bv% (ls_rel% "<spqr::v1::chunked::send_ek::KeysSampled>::recv_ct1_chunk" "__rustc::__rust_dealloc")))
      (rustDeallocSpec A))
    (hpoly16 : subroutine_ok (leavesProgAtExt b ext)
      ((leavesProgAtExt b ext).fnAddr keysSampledRecvCt1ChunkName + 18446744073709463380#64)
      (dropGluePoly16Spec A))
    (outA stA chunkA : BitVec 64)
    (st : Chunked.SendEk.KeysSampled spqrPolyApi (spqrAuthApi F))
    (chunk : Chunk) (dec : PolyDecoder)
    (outSt : Chunked.SendEk.HeaderSent spqrPolyApi (spqrAuthApi F))
    (hout_eq : outSt = { uc := { epoch := st.uc.epoch, auth := st.uc.auth, dk := st.uc.dk },
                         sending_ek := outSt.sending_ek,
                         receiving_ct1 := dec })
    (g : AuthWords) (gdk : VecWords)
    (ekCap ekPtr d56 : BitVec 64)
    (hek_le : st.uc.ek.length ≤ ekCap.toNat) (hek_lt : ekCap.toNat < 2 ^ 63)
    {s0 sf2 : State} {P : SepProp}
    (hsp0_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hfsp_align : ((s0.sp - 976#64) &&& 15#64 == 0#64) = true)
    (hpc2 : sf2.pc = (leavesProgAtExt b ext).fnAddr keysSampledRecvCt1ChunkName + 280#64)
    (hrun2 : sf2.status = .Running)
    (hsp2 : sf2.sp = s0.sp - 976#64)
    (hx19_2 : sf2.readReg64 .x19 = stA)
    (hx20_2 : sf2.readReg64 .x20 = st.uc.epoch)
    (hx21_2 : sf2.readReg64 .x21 = outA)
    (hx22_2 : sf2.readReg64 .x22 = ekCap)
    (hx23_2 : sf2.readReg64 .x23 = ekPtr)
    (hx24_2 : sf2.readReg64 .x24 = s0.sp - 160#64)
    (hx25_2 : sf2.readReg64 .x25 = s0.readReg64 .x25)
    (hx26_2 : sf2.readReg64 .x26 = s0.readReg64 .x26)
    (hx27_2 : sf2.readReg64 .x27 = s0.readReg64 .x27)
    (hfp_2 : sf2.readReg64 .fp = s0.sp - 80#64)
    (htr2 : sf2.trace = s0.trace)
    (hvregs_2 : calleeSavedVRegs sf2 = calleeSavedVRegs s0)
    (hP : P = (
      (polyDecoderAt A (outA + 480#64) dec ∗
        memRegion (s0.sp - 960#64) 400) ∗
      (polyEncoderAt A outA outSt.sending_ek ∗ memRegion (s0.sp - 560#64) 400 ∗
       memRegion (outA + 400#64) 80 ∗
       polyEncoderAt A stA st.sending_hdr ∗ memRegion (stA + 400#64) 104 ∗
       chunkAt chunkA chunk ∗
       (ekPtr ↦ₛ st.uc.ek) ∗ vecU8Tail A ekCap ekPtr st.uc.ek ∗
       relocatedHeap (fun dst => authenticatorAt A dst st.uc.auth) (wordsBytes (authWordsList g)) ∗
       relocatedHeap (fun dst => vecU8 A dst st.uc.dk) (wordsBytes (vecWordsList gdk)) ∗
       wordsAt (s0.sp - 160#64) (authWordsList g ++ vecWordsList gdk) ∗
       memRegion (s0.sp - 976#64) 8 ∗ ((s0.sp - 968#64) ↦₆₄ st.uc.epoch) ∗
       memRegion (s0.sp - 88#64) 8 ∗ sendCt2SavedCells s0 d56 ∗
       A.pool ∗ stackAt (s0.sp - 976#64) encodeBytesStackX))) :
    SepWP (leavesProgAtExt b ext) (s0.readReg64 Reg.lr) sf2 P
      (fun sf P_f =>
        (∀ R : SepProp, sf.mem ⊨ P_f ∗ R →
          sf.mem ⊨ (⌜sf.trace = s0.trace⌝ ∗
            chunkedHeaderSentAt A outA outSt ∗
            memRegion stA 504 ∗
            chunkAt chunkA chunk ∗
            A.pool ∗
            stackAt s0.sp keysSampledRecvCt1ChunkStack) ∗ R) ∧
        sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf) := by
  rw [hP]
  have hfn : libsignalSessionCode.fnOff keysSampledRecvCt1ChunkName = 0x5c370 :=
    keysSampledRecvCt1Chunk_fnOff
  code_fetches libsignalSessionCode spqrKeysSampledRecvCt1ChunkBin b
    (Rust.withPanics ext) hfn 0x5c370 428
  dsimp only [leavesProgAtExt, keysSampledRecvCt1ChunkName,
    BitVec.ofNat_eq_ofNat] at *
  generalize_entry (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr
    "<spqr::v1::chunked::send_ek::KeysSampled>::recv_ct1_chunk" = entry
  examples_hide_fetches
  have hsp_words :
      wordsAt (s0.sp - 160#64) (authWordsList g ++ vecWordsList gdk) =
      (((s0.sp - 160#64) ↦₆₄ g.v1.w0) ∗ ((s0.sp - 152#64) ↦₆₄ g.v1.w1) ∗
       ((s0.sp - 144#64) ↦₆₄ g.v1.w2) ∗ ((s0.sp - 136#64) ↦₆₄ g.v2.w0) ∗
       ((s0.sp - 128#64) ↦₆₄ g.v2.w1) ∗ ((s0.sp - 120#64) ↦₆₄ g.v2.w2) ∗
       ((s0.sp - 112#64) ↦₆₄ gdk.w0) ∗ ((s0.sp - 104#64) ↦₆₄ gdk.w1) ∗
       ((s0.sp - 96#64) ↦₆₄ gdk.w2)) := by
    dsimp only [authWordsList, vecWordsList, List.append]
    simp only [wordsAt_9, arm64_norm]
  have hout_auth_words :
      wordsAt (outA + 400#64) (authWordsList g) =
      (((outA + 400#64) ↦₆₄ g.v1.w0) ∗ ((outA + 408#64) ↦₆₄ g.v1.w1) ∗
       ((outA + 416#64) ↦₆₄ g.v1.w2) ∗ ((outA + 424#64) ↦₆₄ g.v2.w0) ∗
       ((outA + 432#64) ↦₆₄ g.v2.w1) ∗ ((outA + 440#64) ↦₆₄ g.v2.w2)) := by
    dsimp only [authWordsList]
    simp only [wordsAt_6, BitVec.add_assoc, arm64_norm]
  have hout_dk_words :
      wordsAt (outA + 448#64) (vecWordsList gdk) =
      (((outA + 448#64) ↦₆₄ gdk.w0) ∗ ((outA + 456#64) ↦₆₄ gdk.w1) ∗
       ((outA + 464#64) ↦₆₄ gdk.w2)) := by
    dsimp only [vecWordsList]
    simp only [wordsAt, wordsAt_cons_off, wordsAt_nil, sepConj_emp, BitVec.add_assoc, arm64_norm]
  refine SepWP.fold (cells_10_unfold (outA + 400#64)) (by sep_focus) ?_
  wp_pull_exists
  wp_conv_pre => rw [hsp_words]; simp only [wordsAt_10, BitVec.add_assoc, arm64_norm]
  wp_steps
  refine SepWP.fold (Entails.of_eq hsp_words.symm) (by sep_focus) ?_
  refine SepWP.fold (Entails.of_eq hout_auth_words.symm) (by sep_focus) ?_
  refine SepWP.fold (Entails.of_eq hout_dk_words.symm) (by sep_focus) ?_
  refine SepWP.fold (outA_headerSent_recompose A outA s0.sp st.uc.auth st.uc.dk st.uc.epoch
    outSt.sending_ek dec outSt hout_eq g gdk) (by sep_focus) ?_
  refine SepWP.fold (slice_and_tail_entails_vecCapPtrDealloc A ekCap ekPtr st.uc.ek hek_le hek_lt)
    (by sep_focus) ?_
  refine SepWP.fold (polyEncoderAt_entails_tag_vecs_tail A stA st.sending_hdr) (by sep_focus) ?_
  wp_pull_exists; rename_i hdrTag vecs
  wp_focus_pure; intro hvecs_len
  dsimp only [vecCapPtrDealloc, sendCt2SavedCells]
  by_cases hcap0 : (ekCap == 0#64) = true <;>
    simp only [hcap0, Bool.false_eq_true, ↓reduceIte, sepConj_emp, emp_sepConj]
  · wp_steps
    refine SepWP.fold (stackAt_976_to_dropPoly16 s0 st.uc.epoch d56)
      (by dsimp only [sendCt2SavedCells]; sep_focus) ?_
    refine call_dropGluePoly16 hpoly16 (stA + 8#64) vecs
      (by wp_norm_goal) (by wp_norm_lhs)
      (by simp only [State.sp, arm64_norm, hsp2]) (by assumption)
      (by simp only [Reg.lr, arm64_norm, hsp2])
      (by simp only [trace_writeVReg128, arm64_norm, htr2])
      (by simp only [Reg.x0, arm64_norm, hx19_2]) hvecs_len (by sep_focus)
      (fun sf3 hpc3 hrun3 hsp3 hcs3 htr3 => ?_)
    refine SepWP.fold (chunked_400_join stA hdrTag 104 504 rfl (by decide)) (by sep_focus) ?_
    refine SepWP.fold (stackAt_976_from_dropPoly16 s0.sp) (by sep_focus) ?_
    refine SepWP.done hpc3 hrun3 ⟨fun R hm => ?_, hsp3,
      CalleeSavedPreserved.trans
        (by simp only [CalleeSavedPreserved, Reg.x19, Reg.x20, Reg.x21, Reg.x22, Reg.x23,
          Reg.x24, Reg.x25, Reg.x26, Reg.x27, Reg.x28, Reg.fp,
          arm64_norm, hx25_2, hx26_2, hx27_2, hsp2, hvregs_2]) hcs3⟩
    simp only [htr3, sepConj_assoc, satisfies_pure_sepConj, true_and]
    exact satisfies_ac (by ac_rfl) hm
  · wp_steps
    refine SepWP.fold (stackAt_encodeBytesX_to_allocHook (s0.sp - 976#64)) (by sep_focus) ?_
    refine call_rustDealloc_cs hdealloc ekPtr ekCap.toNat 1
      (ret_pc := entry + 324#64) (sp_call := s0.sp - 976#64)
      (by wp_norm_goal) (by wp_norm_lhs)
      (by simp only [State.sp, arm64_norm, hsp2]) hfsp_align
      (by simp only [Reg.lr, arm64_norm])
      htr2
      (by simp only [Reg.x0, arm64_norm, hx23_2])
      (by simp only [Reg.x1, arm64_norm, hx22_2])
      (by simp only [Reg.x2, arm64_norm])
      (by sep_focus)
      (fun sf3 hpc3 hrun3 hsp3 hcs3 htr3 => ?_)
    rcases hcs3 with ⟨hx19_3, hx20_3, hx21_3, hx22_3, hx23_3, hx24_3, hx25_3, hx26_3, hx27_3, hx28_3, hfp_3, hvregs_3⟩
    simp only [arm64_norm, hx19_2, hx25_2, hx26_2, hx27_2, hvregs_2] at hx19_3 hx20_3 hx21_3 hx22_3 hx23_3 hx24_3 hx25_3 hx26_3 hx27_3 hx28_3 hfp_3 hvregs_3
    refine SepWP.fold (stackAt_encodeBytesX_from_allocHook (s0.sp - 976#64)) (by sep_focus) ?_
    wp_steps
    refine SepWP.fold (stackAt_976_to_dropPoly16 s0 st.uc.epoch d56)
      (by dsimp only [sendCt2SavedCells]; sep_focus) ?_
    refine call_dropGluePoly16 hpoly16 (stA + 8#64) vecs
      (by wp_norm_goal) (by wp_norm_lhs)
      (by simp only [State.sp, arm64_norm, hsp3]) (by assumption)
      (by simp only [Reg.lr, arm64_norm, hsp3]) (by simp only [arm64_norm, htr3])
      (by simp only [Reg.x0, arm64_norm, hx19_3]) hvecs_len (by sep_focus)
      (fun sf4 hpc4 hrun4 hsp4 hcs4 htr4 => ?_)
    refine SepWP.fold (chunked_400_join stA hdrTag 104 504 rfl (by decide)) (by sep_focus) ?_
    refine SepWP.fold (stackAt_976_from_dropPoly16 s0.sp) (by sep_focus) ?_
    refine SepWP.done hpc4 hrun4 ⟨fun R hm => ?_, hsp4,
      CalleeSavedPreserved.trans
        (by simp only [CalleeSavedPreserved, Reg.x19, Reg.x20, Reg.x21, Reg.x22, Reg.x23,
          Reg.x24, Reg.x25, Reg.x26, Reg.x27, Reg.x28, Reg.fp,
          arm64_norm, hx25_3, hx26_3, hx27_3, hsp3, hvregs_3]) hcs4⟩
    simp only [htr4, sepConj_assoc, satisfies_pure_sepConj, true_and]
    exact satisfies_ac (by ac_rfl) hm

set_option maxHeartbeats 600000 in
theorem keys_sampled_recv_ct1_chunk_finish {A : RustAlloc} {F : ShaCompress} {b : BitVec 64}
    {ext : String → Option (State → State)}
    (hmemcpy : subroutine_ok (leavesProgAtExt b ext)
      ((leavesProgAtExt b ext).fnAddr keysSampledRecvCt1ChunkName +
        (bv% (ls_rel% "<spqr::v1::chunked::send_ek::KeysSampled>::recv_ct1_chunk" "memcpy")))
      sessionMemcpyRegionSpec)
    (hdealloc : subroutine_ok (leavesProgAtExt b ext)
      ((leavesProgAtExt b ext).fnAddr keysSampledRecvCt1ChunkName +
        (bv% (ls_rel% "<spqr::v1::chunked::send_ek::KeysSampled>::recv_ct1_chunk" "__rustc::__rust_dealloc")))
      (rustDeallocSpec A))
    (hpoly16 : subroutine_ok (leavesProgAtExt b ext)
      ((leavesProgAtExt b ext).fnAddr keysSampledRecvCt1ChunkName + 18446744073709463380#64)
      (dropGluePoly16Spec A))
    (outA stA chunkA : BitVec 64)
    (st : Chunked.SendEk.KeysSampled spqrPolyApi (spqrAuthApi F))
    (chunk : Chunk) (dec : PolyDecoder)
    (outSt : Chunked.SendEk.HeaderSent spqrPolyApi (spqrAuthApi F))
    (hout_eq : outSt = { uc := { epoch := st.uc.epoch, auth := st.uc.auth, dk := st.uc.dk },
                         sending_ek := outSt.sending_ek,
                         receiving_ct1 := dec })
    (g : AuthWords) (gdk : VecWords)
    (ekCap ekPtr d56 : BitVec 64)
    (hek_le : st.uc.ek.length ≤ ekCap.toNat) (hek_lt : ekCap.toNat < 2 ^ 63)
    {s0 s : State} {P : SepProp}
    (hsp0_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hfsp_align : ((s0.sp - 976#64) &&& 15#64 == 0#64) = true)
    (hpc : s.pc = (leavesProgAtExt b ext).fnAddr keysSampledRecvCt1ChunkName + 236#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = s0.sp - 976#64)
    (hx19 : s.readReg64 .x19 = stA)
    (hx20 : s.readReg64 .x20 = st.uc.epoch)
    (hx21 : s.readReg64 .x21 = outA)
    (hx22 : s.readReg64 .x22 = ekCap)
    (hx23 : s.readReg64 .x23 = ekPtr)
    (hx24 : s.readReg64 .x24 = s0.sp - 160#64)
    (hx25 : s.readReg64 .x25 = s0.readReg64 .x25)
    (hx26 : s.readReg64 .x26 = s0.readReg64 .x26)
    (hx27 : s.readReg64 .x27 = s0.readReg64 .x27)
    (hfp : s.readReg64 .fp = s0.sp - 80#64)
    (htrace : s.trace = s0.trace)
    (hvregs : calleeSavedVRegs s = calleeSavedVRegs s0)
    (hP : P = (
      memRegion outA 880 ∗
      polyEncoderAt A stA st.sending_hdr ∗
      memRegion (stA + 400#64) 104 ∗
      chunkAt chunkA chunk ∗
      polyDecoderAt A (s0.sp - 960#64) dec ∗
      polyEncoderAt A (s0.sp - 560#64) outSt.sending_ek ∗
      (ekPtr ↦ₛ st.uc.ek) ∗
      vecU8Tail A ekCap ekPtr st.uc.ek ∗
      relocatedHeap (fun dst => authenticatorAt A dst st.uc.auth) (wordsBytes (authWordsList g)) ∗
      relocatedHeap (fun dst => vecU8 A dst st.uc.dk) (wordsBytes (vecWordsList gdk)) ∗
      wordsAt (s0.sp - 160#64) (authWordsList g ++ vecWordsList gdk) ∗
      memRegion (s0.sp - 976#64) 8 ∗
      ((s0.sp - 968#64) ↦₆₄ st.uc.epoch) ∗
      memRegion (s0.sp - 88#64) 8 ∗
      sendCt2SavedCells s0 d56 ∗
      A.pool ∗
      stackAt (s0.sp - 976#64) encodeBytesStackX)) :
    SepWP (leavesProgAtExt b ext) (s0.readReg64 Reg.lr) s P
      (fun sf P_f =>
        (∀ R : SepProp, sf.mem ⊨ P_f ∗ R →
          sf.mem ⊨ (⌜sf.trace = s0.trace⌝ ∗
            chunkedHeaderSentAt A outA outSt ∗
            memRegion stA 504 ∗
            chunkAt chunkA chunk ∗
            A.pool ∗
            stackAt s0.sp keysSampledRecvCt1ChunkStack) ∗ R) ∧
        sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf) := by
  rw [hP]
  have h_tail := keys_sampled_recv_ct1_chunk_tail (F := F) hdealloc hpoly16
  have hfn : libsignalSessionCode.fnOff keysSampledRecvCt1ChunkName = 0x5c370 :=
    keysSampledRecvCt1Chunk_fnOff
  code_fetches libsignalSessionCode spqrKeysSampledRecvCt1ChunkBin b
    (Rust.withPanics ext) hfn 0x5c370 428
  dsimp only [leavesProgAtExt, tripleRatchetProgAtExt, keysSampledRecvCt1ChunkName,
    BitVec.ofNat_eq_ofNat] at *
  generalize_entry (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr
    "<spqr::v1::chunked::send_ek::KeysSampled>::recv_ct1_chunk" = entry
  examples_hide_fetches
  wp_conv_pre =>
    rw [ProofLib.memRegion_split' (b := outA) (n := 400) (k := 480) (b' := outA + 400#64) rfl rfl (by decide),
        ProofLib.memRegion_split' (b := outA + 400#64) (n := 80) (k := 400) (b' := outA + 480#64) rfl (by bv_omega) (by decide)]
  obtain ⟨tag, htag01, encRest, henc_split⟩ := polyEncoderAt_split_tag A (s0.sp - 560#64) outSt.sending_ek
  suffices h_mc1 : ∀ sf1 : State,
      sf1.pc = entry + 264#64 → sf1.status = .Running →
      sf1.sp = s0.sp - 976#64 → CalleeSavedPreserved s sf1 → sf1.trace = s0.trace →
      SepWP (libsignalSessionCode.rebase b (Rust.withPanics ext)) (s0.readReg64 Reg.lr) sf1
        ((polyEncoderAt A outA outSt.sending_ek ∗ memRegion (s0.sp - 560#64) 400) ∗
          (memRegion (outA + 400#64) 80 ∗ memRegion (outA + 480#64) 400 ∗
           polyEncoderAt A stA st.sending_hdr ∗ memRegion (stA + 400#64) 104 ∗
           chunkAt chunkA chunk ∗ polyDecoderAt A (s0.sp - 960#64) dec ∗
           (ekPtr ↦ₛ st.uc.ek) ∗ vecU8Tail A ekCap ekPtr st.uc.ek ∗
           relocatedHeap (fun dst => authenticatorAt A dst st.uc.auth) (wordsBytes (authWordsList g)) ∗
           relocatedHeap (fun dst => vecU8 A dst st.uc.dk) (wordsBytes (vecWordsList gdk)) ∗
           wordsAt (s0.sp - 160#64) (authWordsList g ++ vecWordsList gdk) ∗
           memRegion (s0.sp - 976#64) 8 ∗ ((s0.sp - 968#64) ↦₆₄ st.uc.epoch) ∗
           memRegion (s0.sp - 88#64) 8 ∗ sendCt2SavedCells s0 d56 ∗
           A.pool ∗ stackAt (s0.sp - 976#64) encodeBytesStackX))
        (fun sf P_f =>
          (∀ R : SepProp, sf.mem ⊨ P_f ∗ R →
            sf.mem ⊨ (⌜sf.trace = s0.trace⌝ ∗
              chunkedHeaderSentAt A outA outSt ∗
              memRegion stA 504 ∗
              chunkAt chunkA chunk ∗
              A.pool ∗
              stackAt s0.sp keysSampledRecvCt1ChunkStack) ∗ R) ∧
          sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf) by
    rcases htag01 with rfl | rfl
    · wp_conv_pre => rw [henc_split]
      wp_steps
      wp_conv_pre => rw [← henc_split]
      refine call_memcpy_relocate_cs hmemcpy (s0 := s0)
        (Relocatable.of_polyEncoderAt A outSt.sending_ek) outA (s0.sp - 560#64)
        (ret_pc := entry + 264#64) (sp_call := s0.sp - 976#64)
        (by wp_norm_goal) (by wp_norm_lhs)
        (by simp only [State.sp, arm64_norm, hsp]) hfsp_align
        (by simp only [Reg.lr, arm64_norm]) (by simp only [arm64_norm, htrace])
        (by simp only [Reg.x0, arm64_norm, hx21])
        (by simp only [Reg.x1, arm64_norm, hsp])
        (by simp only [Reg.x2, arm64_norm])
        (by sep_focus)
        (fun sf1 hpc1 hrun1 hsp1 hcs1 htr1 =>
          sepWP_congr_pre (by ac_rfl) (h_mc1 sf1 hpc1 hrun1 hsp1 (CalleeSavedPreserved.trans
            (by simp only [CalleeSavedPreserved, Reg.x19, Reg.x20, Reg.x21, Reg.x22, Reg.x23,
              Reg.x24, Reg.x25, Reg.x26, Reg.x27, Reg.x28, Reg.fp, arm64_norm]) hcs1) htr1))
    · wp_conv_pre => rw [henc_split]
      wp_steps
      wp_conv_pre => rw [← henc_split]
      refine call_memcpy_relocate_cs hmemcpy (s0 := s0)
        (Relocatable.of_polyEncoderAt A outSt.sending_ek) outA (s0.sp - 560#64)
        (ret_pc := entry + 264#64) (sp_call := s0.sp - 976#64)
        (by wp_norm_goal) (by wp_norm_lhs)
        (by simp only [State.sp, arm64_norm, hsp]) hfsp_align
        (by simp only [Reg.lr, arm64_norm]) (by simp only [arm64_norm, htrace])
        (by simp only [Reg.x0, arm64_norm, hx21])
        (by simp only [Reg.x1, arm64_norm, hsp])
        (by simp only [Reg.x2, arm64_norm])
        (by sep_focus)
        (fun sf1 hpc1 hrun1 hsp1 hcs1 htr1 =>
          sepWP_congr_pre (by ac_rfl) (h_mc1 sf1 hpc1 hrun1 hsp1 (CalleeSavedPreserved.trans
            (by simp only [CalleeSavedPreserved, Reg.x19, Reg.x20, Reg.x21, Reg.x22, Reg.x23,
              Reg.x24, Reg.x25, Reg.x26, Reg.x27, Reg.x28, Reg.fp, arm64_norm]) hcs1) htr1))
  intro sf1 hpc1 hrun1 hsp1 hcs1 htr1
  rcases hcs1 with ⟨hx19_1, hx20_1, hx21_1, hx22_1, hx23_1, hx24_1, hx25_1, hx26_1, hx27_1, hx28_1, hfp_1, hvregs_1⟩
  simp only [arm64_norm, hx19, hx20, hx21, hx22, hx23, hx24, hx25, hx26, hx27, hfp, hvregs] at hx19_1 hx20_1 hx21_1 hx22_1 hx23_1 hx24_1 hx25_1 hx26_1 hx27_1 hx28_1 hfp_1 hvregs_1
  wp_steps
  refine call_memcpy_relocate_cs hmemcpy (s0 := s0)
    (Relocatable.of_polyDecoderAt A dec) (outA + 480#64) (s0.sp - 960#64)
    (ret_pc := entry + 280#64) (sp_call := s0.sp - 976#64)
    (by wp_norm_goal) (by wp_norm_lhs)
    (by simp only [State.sp, arm64_norm, hsp1]) hfsp_align
    (by simp only [Reg.lr, arm64_norm]) (by simp only [arm64_norm, htr1])
    (by simp only [Reg.x0, arm64_norm, hx21_1])
    (by simp only [Reg.x1, arm64_norm, hsp1])
    (by simp only [Reg.x2, arm64_norm])
    (by sep_focus)
    (fun sf2 hpc2 hrun2 hsp2 hcs2 htr2 => ?_)
  rcases hcs2 with ⟨hx19_2, hx20_2, hx21_2, hx22_2, hx23_2, hx24_2, hx25_2, hx26_2, hx27_2, hx28_2, hfp_2, hvregs_2⟩
  simp only [arm64_norm, hx19_1, hx20_1, hx21_1, hx22_1, hx23_1, hx24_1, hx25_1, hx26_1, hx27_1, hfp_1, hvregs_1] at hx19_2 hx20_2 hx21_2 hx22_2 hx23_2 hx24_2 hx25_2 hx26_2 hx27_2 hx28_2 hfp_2 hvregs_2
  exact h_tail outA stA chunkA st chunk dec outSt
    hout_eq g gdk ekCap ekPtr d56 hek_le hek_lt hsp0_align hfsp_align
    hpc2 hrun2 hsp2 hx19_2 hx20_2 hx21_2 hx22_2 hx23_2 hx24_2 hx25_2 hx26_2 hx27_2 hfp_2 htr2 hvregs_2 (by ac_rfl)

/-- Framed call rule for `addChunkSpec A` (`0x6c420`) when followed by another `SepWPp` call at `next_pc`. -/
theorem call_addChunk_next {A : RustAlloc} {prog : Program} {entry ret_pc next_pc : BitVec 64}
    (hcall : subroutine_ok prog entry (addChunkSpec A))
    (decA chunkA : BitVec 64) (dec : PolyDecoder) (chunk : Chunk)
    (hsorted : PolyDecoderStrictSorted dec)
    {s0 s : State} {sp_call : BitVec 64} {P Frame R : SepProp}
    {post : State → SepProp → Prop}
    (hpc : s.pc = entry)
    (hrun : s.status = .Running)
    (hsp : s.sp = sp_call)
    (hsp_align : (sp_call &&& 15#64 == 0#64) = true)
    (hlr : s.readReg64 Reg.lr = ret_pc)
    (htrace : s.trace = s0.trace)
    (hx0 : s.readReg64 Reg.x0 = decA)
    (hx1 : s.readReg64 Reg.x1 = chunkA)
    (hsplit : P = (polyDecoderAt A decA dec ∗ chunkAt chunkA chunk ∗
      A.pool ∗ stackAt sp_call addChunkStack) ∗ Frame)
    (hnext : ∀ sf : State, sf.pc = ret_pc → sf.status = .Running →
      sf.sp = sp_call → CalleeSavedPreserved s sf → sf.trace = s0.trace →
      PolyDecoderStrictSorted (addChunkTotal dec chunk) →
      SepWP prog next_pc sf
        ((polyDecoderAt A decA (addChunkTotal dec chunk) ∗ chunkAt chunkA chunk ∗
          A.pool ∗ stackAt sp_call addChunkStack) ∗ Frame)
        (fun sm Pm =>
          SepWPp prog (s0.readReg64 Reg.lr) sm Pm post
            (fun sf P_f => (sf.mem ⊨ P_f ∗ R) →
              (sf.mem ⊨ ⌜allocFailedIn s0 sf ∧ s0.trace <+: sf.trace⌝ ∗ anyHeap ∗ R)))) :
    SepWP prog entry s P
      (fun sm Pm =>
        SepWPp prog (s0.readReg64 Reg.lr) sm Pm post
          (fun sf P_f => (sf.mem ⊨ P_f ∗ R) →
            (sf.mem ⊨ ⌜allocFailedIn s0 sf ∧ s0.trace <+: sf.trace⌝ ∗ anyHeap ∗ R))) := by
  apply SepWP.done hpc hrun
  refine SepWPp.call hcall (x := ⟨decA, chunkA, dec, chunk⟩) (F := Frame)
    hpc hrun (by rw [State.spAligned, hsp]; exact hsp_align) hlr ?_
    (fun _ _ _ _ h => allowPanic_not_exited h)
    (fun sf _ hmem => ?_)
    (fun sf hpc_sf hrun_sf hsp_sf hcs_sf => ?_)
  · intro R' hm
    rw [hsplit] at hm
    dsimp only [addChunkSpec]
    rw [hsp]
    simp only [sepConj_assoc, satisfies_pure_sepConj] at hm ⊢
    exact ⟨⟨hx0, hx1, hsorted⟩, hm⟩
  · rw [← sepConj_assoc]
    refine allowPanic_frame (fun ⟨haf, htr_sub⟩ => ?_) hmem
    unfold allocFailedIn at haf ⊢
    rw [htrace] at haf htr_sub
    exact ⟨haf, htr_sub⟩
  · dsimp only [addChunkSpec]
    rw [hsp, sepConj_assoc]
    refine SepWPp.pure_left fun ⟨htr, hsorted'⟩ => ?_
    apply SepWPp.of_sepWP (mid := next_pc)
    have hassoc :
        (polyDecoderAt A decA (addChunkTotal dec chunk) ∗ chunkAt chunkA chunk ∗
          A.pool ∗ stackAt sp_call addChunkStack) ∗ Frame =
        (polyDecoderAt A decA (addChunkTotal dec chunk) ∗
          (chunkAt chunkA chunk ∗ (A.pool ∗ stackAt sp_call addChunkStack))) ∗ Frame := by ac_rfl
    rw [← hassoc]
    exact hnext sf hpc_sf hrun_sf (hsp_sf.trans hsp) hcs_sf (htr.trans htrace) hsorted'

/-! ## 4. Main Proof: `<KeysSampled>::recv_ct1_chunk` (`0x61768`, 107 insns) -/

set_option maxHeartbeats 800000 in
theorem keys_sampled_recv_ct1_chunk_ok_ext {A : RustAlloc} {F : ShaCompress}
    {b : BitVec 64} {ext : String → Option (State → State)}
    (hdealloc : DeallocOkExt b A ext)
    (hmemcpy : subroutine_ok (leavesProgAtExt b ext)
      ((leavesProgAtExt b ext).fnAddr memcpyName) sessionMemcpyRegionSpec)
    (haddChunk : subroutine_ok (leavesProgAtExt b ext)
      ((leavesProgAtExt b ext).fnAddr addChunkName) (addChunkSpec A))
    (hencode : subroutine_ok (leavesProgAtExt b ext)
      ((leavesProgAtExt b ext).fnAddr encodeBytesName) (encodeBytesSpec A)) :
    subroutine_ok (leavesProgAtExt b ext)
      ((leavesProgAtExt b ext).fnAddr keysSampledRecvCt1ChunkName)
      (keysSampledRecvCt1ChunkSpec A F) := by
  have hfn : libsignalSessionCode.fnOff keysSampledRecvCt1ChunkName = 0x5c370 :=
    keysSampledRecvCt1Chunk_fnOff
  have hadd_raw : subroutine_ok (leavesProgAtExt b ext)
      ((leavesProgAtExt b ext).fnAddr keysSampledRecvCt1ChunkName + 44216#64)
      (addChunkSpec A) := sub_ok_of_addr_eq
    (fnAddr_fwd_eq (d := 44216) (b := b) (X := Rust.withPanics ext)
      hfn libsignalSessionCode_fnOff_0x67028 (by decide)).symm haddChunk
  have henc_raw : subroutine_ok (leavesProgAtExt b ext)
      ((leavesProgAtExt b ext).fnAddr keysSampledRecvCt1ChunkName + 40784#64)
      (encodeBytesSpecX A) := encodeBytesSpecX_of_encodeBytesSpec' (sub_ok_of_addr_eq
    (fnAddr_fwd_eq (d := 40784) (b := b) (X := Rust.withPanics ext)
      hfn libsignalSessionCode_fnOff_0x662c0 (by decide)).symm hencode)
  have hmemcpy_raw : subroutine_ok (leavesProgAtExt b ext)
      ((leavesProgAtExt b ext).fnAddr keysSampledRecvCt1ChunkName +
        (bv% (ls_rel% "<spqr::v1::chunked::send_ek::KeysSampled>::recv_ct1_chunk" "memcpy")))
      sessionMemcpyRegionSpec := sub_ok_of_addr_eq
    (fnAddr_fwd_eq (d := (num% (ls_rel% "<spqr::v1::chunked::send_ek::KeysSampled>::recv_ct1_chunk" "memcpy"))) (b := b) (X := Rust.withPanics ext)
      hfn (ls_stub% "memcpy") (by decide)).symm hmemcpy
  have hdealloc_raw : subroutine_ok (leavesProgAtExt b ext)
      ((leavesProgAtExt b ext).fnAddr keysSampledRecvCt1ChunkName +
        (bv% (ls_rel% "<spqr::v1::chunked::send_ek::KeysSampled>::recv_ct1_chunk" "__rustc::__rust_dealloc")))
      (rustDeallocSpec A) := sub_ok_of_addr_eq
    (Program.fnAddr_rel (k := (num% (ls_rel% "<spqr::v1::chunked::send_ek::KeysSampled>::recv_ct1_chunk" "__rustc::__rust_dealloc"))) (b := b) (X := Rust.withPanics ext)
      hfn (ls_stub% "__rustc::__rust_dealloc") (by decide)) hdealloc
  have hpoly16_raw : subroutine_ok (leavesProgAtExt b ext)
      ((leavesProgAtExt b ext).fnAddr keysSampledRecvCt1ChunkName + 18446744073709463380#64)
      (dropGluePoly16Spec A) := by
    have hrel : (leavesProgAtExt b ext).fnAddr keysSampledRecvCt1ChunkName =
        (leavesProgAtExt b ext).fnAddr dropPoly16Name + BitVec.ofNat 64 88236 :=
      Program.fnAddr_rel (k := 88236) (b := b) (X := Rust.withPanics ext)
        libsignalSessionCode_fnOff_0x46ac4 hfn (by decide)
    refine sub_ok_of_addr_eq ?_ (drop_glue_poly16_ok_ext hdealloc)
    dsimp only [dropProgAtExt, leavesProgAtExt] at hrel ⊢
    rw [hrel, BitVec.add_assoc]; simp
  code_fetches libsignalSessionCode spqrKeysSampledRecvCt1ChunkBin b
    (Rust.withPanics ext) hfn 0x5c370 428
  clear hfn
  unfold keysSampledRecvCt1ChunkSpec
  wpp_init x s0
  conv => arg 6; ext sf P_f; rw [sepConj_assoc]
  rcases x with ⟨outA, stA, chunkA, st, chunk, outSt⟩
  have h_finish := keys_sampled_recv_ct1_chunk_finish (F := F) hmemcpy_raw hdealloc_raw hpoly16_raw
  dsimp only [leavesProgAtExt, tripleRatchetProgAtExt, keysSampledRecvCt1ChunkName,
    chunkedHeaderSentSize,
    BitVec.ofNat_eq_ofNat] at *
  generalize_entry (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr
    "<spqr::v1::chunked::send_ek::KeysSampled>::recv_ct1_chunk" = entry
  examples_hide_fetches
  subst ‹s0.readReg64 (Reg.gpr 0#5) = outA›
    ‹s0.readReg64 (Reg.gpr 1#5) = stA› ‹s0.readReg64 (Reg.gpr 3#5) = chunkA›
  obtain ⟨henc_res, hek_len_le, hout_eq⟩ := keys_sampled_recv_ct1_chunk_ok_elim (by assumption)
  have hsp0_align : (s0.sp &&& 15#64 == 0#64) = true := by assumption
  have hfsp_align : ((s0.sp - 976#64) &&& 15#64 == 0#64) = true :=
    spAligned_sub s0.sp 976#64 hsp0_align (by decide)
  apply SepWPp.of_sepWP (mid := entry + 44216#64)
  wp_conv_pre =>
    rw [stackAt_976_split s0.sp]
    unfold chunkedKeysSampledAt
    rw [unchunkedHeaderSentAt_400_eq A (s0.readReg64 (Reg.gpr 1#5)) st.uc]
  refine SepWP.fold (cells_1_unfold (s0.sp - 968#64)) (by sep_focus) ?_
  refine SepWP.fold (cells_16_unfold (s0.sp - 960#64)) (by sep_focus) ?_
  refine SepWP.fold (cells_16_unfold (s0.sp - 832#64)) (by sep_focus) ?_
  refine SepWP.fold (cells_16_unfold (s0.sp - 704#64)) (by sep_focus) ?_
  refine SepWP.fold (cells_1_unfold (s0.sp - 576#64)) (by sep_focus) ?_
  refine SepWP.fold (byte_1_unfold (s0.sp - 568#64)) (by sep_focus) ?_
  refine SepWP.fold (cells_10_unfold (s0.sp - 80#64)) (by sep_focus) ?_
  wp_pull_exists
  wp_conv_pre => simp only [wordsAt_16, wordsAt_10, arm64_norm]
  wp_steps
  refine SepWP.fold (fold_sendCt2SavedCells s0 _) (by sep_focus) ?_
  have hdec0_1 :
      (((s0.sp - 960#64) ↦₆₄ 0#64) ∗ ((s0.sp - 952#64) ↦₆₄ 2#64) ∗
       ((s0.sp - 944#64) ↦₆₄ 0#64) ∗ ((s0.sp - 936#64) ↦₆₄ 0#64) ∗
       ((s0.sp - 928#64) ↦₆₄ 2#64) ∗ ((s0.sp - 920#64) ↦₆₄ 0#64) ∗
       ((s0.sp - 912#64) ↦₆₄ 0#64) ∗ ((s0.sp - 904#64) ↦₆₄ 2#64) ∗
       ((s0.sp - 896#64) ↦₆₄ 0#64) ∗ ((s0.sp - 888#64) ↦₆₄ 0#64) ∗
       ((s0.sp - 880#64) ↦₆₄ 2#64) ∗ ((s0.sp - 872#64) ↦₆₄ 0#64) ∗
       ((s0.sp - 864#64) ↦₆₄ 0#64) ∗ ((s0.sp - 856#64) ↦₆₄ 2#64) ∗
       ((s0.sp - 848#64) ↦₆₄ 0#64) ∗ ((s0.sp - 840#64) ↦₆₄ 0#64)) =
      wordsAt (s0.sp - 960#64)
        [0#64, 2#64, 0#64, 0#64, 2#64, 0#64, 0#64, 2#64,
         0#64, 0#64, 2#64, 0#64, 0#64, 2#64, 0#64, 0#64] := by simp only [wordsAt_16, arm64_norm]
  have hdec0_2 :
      (((s0.sp - 832#64) ↦₆₄ 2#64) ∗ ((s0.sp - 824#64) ↦₆₄ 0#64) ∗
       ((s0.sp - 816#64) ↦₆₄ 0#64) ∗ ((s0.sp - 808#64) ↦₆₄ 2#64) ∗
       ((s0.sp - 800#64) ↦₆₄ 0#64) ∗ ((s0.sp - 792#64) ↦₆₄ 0#64) ∗
       ((s0.sp - 784#64) ↦₆₄ 2#64) ∗ ((s0.sp - 776#64) ↦₆₄ 0#64) ∗
       ((s0.sp - 768#64) ↦₆₄ 0#64) ∗ ((s0.sp - 760#64) ↦₆₄ 2#64) ∗
       ((s0.sp - 752#64) ↦₆₄ 0#64) ∗ ((s0.sp - 744#64) ↦₆₄ 0#64) ∗
       ((s0.sp - 736#64) ↦₆₄ 2#64) ∗ ((s0.sp - 728#64) ↦₆₄ 0#64) ∗
       ((s0.sp - 720#64) ↦₆₄ 0#64) ∗ ((s0.sp - 712#64) ↦₆₄ 2#64)) =
      wordsAt ((s0.sp - 960#64) + 128#64)
        [2#64, 0#64, 0#64, 2#64, 0#64, 0#64, 2#64, 0#64,
         0#64, 2#64, 0#64, 0#64, 2#64, 0#64, 0#64, 2#64] := by simp only [wordsAt_16, arm64_norm]
  have hdec0_3 :
      (((s0.sp - 704#64) ↦₆₄ 0#64) ∗ ((s0.sp - 696#64) ↦₆₄ 0#64) ∗
       ((s0.sp - 688#64) ↦₆₄ 2#64) ∗ ((s0.sp - 680#64) ↦₆₄ 0#64) ∗
       ((s0.sp - 672#64) ↦₆₄ 0#64) ∗ ((s0.sp - 664#64) ↦₆₄ 2#64) ∗
       ((s0.sp - 656#64) ↦₆₄ 0#64) ∗ ((s0.sp - 648#64) ↦₆₄ 0#64) ∗
       ((s0.sp - 640#64) ↦₆₄ 2#64) ∗ ((s0.sp - 632#64) ↦₆₄ 0#64) ∗
       ((s0.sp - 624#64) ↦₆₄ 0#64) ∗ ((s0.sp - 616#64) ↦₆₄ 2#64) ∗
       ((s0.sp - 608#64) ↦₆₄ 0#64) ∗ ((s0.sp - 600#64) ↦₆₄ 0#64) ∗
       ((s0.sp - 592#64) ↦₆₄ 2#64) ∗ ((s0.sp - 584#64) ↦₆₄ 0#64)) =
      wordsAt ((s0.sp - 960#64) + 256#64)
        [0#64, 0#64, 2#64, 0#64, 0#64, 2#64, 0#64, 0#64,
         2#64, 0#64, 0#64, 2#64, 0#64, 0#64, 2#64, 0#64] := by simp only [wordsAt_16, arm64_norm]
  refine SepWP.fold (Entails.of_eq hdec0_1) (by sep_focus) ?_
  refine SepWP.fold (Entails.of_eq hdec0_2) (by sep_focus) ?_
  refine SepWP.fold (Entails.of_eq hdec0_3) (by sep_focus) ?_
  have hdec_recomp :
      wordsAt (s0.sp - 960#64)
        [0#64, 2#64, 0#64, 0#64, 2#64, 0#64, 0#64, 2#64,
         0#64, 0#64, 2#64, 0#64, 0#64, 2#64, 0#64, 0#64] ∗
      wordsAt ((s0.sp - 960#64) + 128#64)
        [2#64, 0#64, 0#64, 2#64, 0#64, 0#64, 2#64, 0#64,
         0#64, 2#64, 0#64, 0#64, 2#64, 0#64, 0#64, 2#64] ∗
      wordsAt ((s0.sp - 960#64) + 256#64)
        [0#64, 0#64, 2#64, 0#64, 0#64, 2#64, 0#64, 0#64,
         2#64, 0#64, 0#64, 2#64, 0#64, 0#64, 2#64, 0#64] ∗
      ((s0.sp - 576#64) ↦₆₄ 480#64) ∗ ((s0.sp - 568#64) ↦₈ 0#8) ∗ memRegion (s0.sp - 567#64) 7 ⊢
      polyDecoderAt A (s0.sp - 960#64) (emptyPolyDecoder 480) := by
    simpa only [arm64_norm] using emptyPolyDecoder_recompose A (s0.sp - 960#64) 480 (by decide)
  refine SepWP.fold hdec_recomp (by sep_focus) ?_
  refine call_addChunk_next hadd_raw
    (s0.sp - 960#64) (s0.readReg64 (Reg.gpr 3#5)) (emptyPolyDecoder 480) chunk
    (emptyPolyDecoder_strictSorted 480)
    (ret_pc := entry + 184#64) (next_pc := entry + 40784#64) (sp_call := s0.sp - 976#64)
    (by simp only [arm64_norm]) (by simpa only [arm64_norm] using ‹s0.status = .Running›)
    (by simp only [State.sp, arm64_norm]) hfsp_align (by simp only [Reg.lr, arm64_norm])
    (by simp only [arm64_norm]) (by simp only [Reg.x0, arm64_norm])
    (by simp only [Reg.x1, arm64_norm]) (by sep_focus)
    (fun sf1 hpc1 hrun1 hsp1 hcs1 htr1 _ => ?_)
  generalize (addChunkTotal (emptyPolyDecoder 480) chunk) = dec1 at hout_eq ⊢
  rcases hcs1 with ⟨hx19_1, hx20_1, hx21_1, hx22_1, hx23_1, hx24_1, hx25_1, hx26_1, hx27_1, hx28_1, hfp_1, hvregs_1⟩
  simp only [arm64_norm] at hx19_1 hx20_1 hx21_1 hx22_1 hx23_1 hx24_1 hx25_1 hx26_1 hx27_1 hx28_1 hfp_1 hvregs_1
  refine SepWP.fold (stackAt_976_addChunk_to_encodeBytesX s0.sp) (by sep_focus) ?_
  refine SepWP.fold (authenticatorAt_extract A (s0.readReg64 (Reg.gpr 1#5) + 400#64) st.uc.auth)
    (by sep_focus) ?_
  wp_pull_exists; rename_i g
  refine SepWP.fold (vecU8_entails_slice_and_tail A (s0.readReg64 (Reg.gpr 1#5) + 448#64) st.uc.ek)
    (by sep_focus) ?_
  wp_pull_exists; rename_i ekCap ekPtr
  wp_focus_pure; rintro ⟨hek_le, hek_lt, hek_ne⟩
  refine SepWP.fold (vecU8_extract A (s0.readReg64 (Reg.gpr 1#5) + 472#64) st.uc.dk)
    (by sep_focus) ?_
  wp_pull_exists; rename_i gdk
  refine SepWP.fold (cells_9_unfold (s0.sp - 160#64)) (by sep_focus) ?_
  wp_pull_exists
  have hst_auth_words :
      wordsAt (s0.readReg64 (Reg.gpr 1#5) + 400#64) (authWordsList g) =
      (((s0.readReg64 (Reg.gpr 1#5) + 400#64) ↦₆₄ g.v1.w0) ∗
       ((s0.readReg64 (Reg.gpr 1#5) + 408#64) ↦₆₄ g.v1.w1) ∗
       ((s0.readReg64 (Reg.gpr 1#5) + 416#64) ↦₆₄ g.v1.w2) ∗
       ((s0.readReg64 (Reg.gpr 1#5) + 424#64) ↦₆₄ g.v2.w0) ∗
       ((s0.readReg64 (Reg.gpr 1#5) + 432#64) ↦₆₄ g.v2.w1) ∗
       ((s0.readReg64 (Reg.gpr 1#5) + 440#64) ↦₆₄ g.v2.w2)) := by
    dsimp only [authWordsList]
    simp only [wordsAt_6, BitVec.add_assoc, arm64_norm]
  have hst_dk_words :
      wordsAt (s0.readReg64 (Reg.gpr 1#5) + 472#64) (vecWordsList gdk) =
      (((s0.readReg64 (Reg.gpr 1#5) + 472#64) ↦₆₄ gdk.w0) ∗
       ((s0.readReg64 (Reg.gpr 1#5) + 480#64) ↦₆₄ gdk.w1) ∗
       ((s0.readReg64 (Reg.gpr 1#5) + 488#64) ↦₆₄ gdk.w2)) := by
    dsimp only [vecWordsList]
    simp only [wordsAt, wordsAt_cons_off, wordsAt_nil, sepConj_emp, BitVec.add_assoc, arm64_norm]
  have hsp_words :
      wordsAt (s0.sp - 160#64) (authWordsList g ++ vecWordsList gdk) =
      (((s0.sp - 160#64) ↦₆₄ g.v1.w0) ∗ ((s0.sp - 152#64) ↦₆₄ g.v1.w1) ∗
       ((s0.sp - 144#64) ↦₆₄ g.v1.w2) ∗ ((s0.sp - 136#64) ↦₆₄ g.v2.w0) ∗
       ((s0.sp - 128#64) ↦₆₄ g.v2.w1) ∗ ((s0.sp - 120#64) ↦₆₄ g.v2.w2) ∗
       ((s0.sp - 112#64) ↦₆₄ gdk.w0) ∗ ((s0.sp - 104#64) ↦₆₄ gdk.w1) ∗
       ((s0.sp - 96#64) ↦₆₄ gdk.w2)) := by
    dsimp only [authWordsList, vecWordsList, List.append]
    simp only [wordsAt_9, arm64_norm]
  wp_conv_pre =>
    rw [hst_auth_words, hst_dk_words]
    simp only [wordsAt_9, BitVec.add_assoc, arm64_norm]
  wp_steps
  refine SepWP.fold (Entails.of_eq hst_auth_words.symm) (by sep_focus) ?_
  refine SepWP.fold (Entails.of_eq hst_dk_words.symm) (by sep_focus) ?_
  refine SepWP.fold (stA_400_104_fold (s0.readReg64 (Reg.gpr 1#5)) g
    ekCap ekPtr (BitVec.ofNat 64 st.uc.ek.length) gdk st.uc.epoch) (by sep_focus) ?_
  refine SepWP.fold (Entails.of_eq hsp_words.symm) (by sep_focus) ?_
  have hek_lt64 : st.uc.ek.length < 2 ^ 64 := by omega
  refine call_encodeBytesX henc_raw
    (s0.sp - 560#64) ekPtr st.uc.ek outSt.sending_ek henc_res hek_lt64
    (ret_pc := entry + 236#64) (sp_call := s0.sp - 976#64)
    (by wp_norm_goal) (by wp_norm_lhs)
    (by simp only [State.sp, arm64_norm, hsp1]) hfsp_align
    (by simp only [Reg.lr, arm64_norm]) (by simp only [arm64_norm, htr1])
    (by simp only [Reg.x8, arm64_norm, hsp1])
    (by simp only [Reg.x0, arm64_norm])
    (by simp only [Reg.x1, arm64_norm])
    (by sep_focus)
    (fun sf2 hpc2 hrun2 hsp2 hcs2 htr2 => ?_)
  rcases hcs2 with ⟨hx19_2, hx20_2, hx21_2, hx22_2, hx23_2, hx24_2, hx25_2, hx26_2, hx27_2, hx28_2, hfp_2, hvregs_2⟩
  simp only [arm64_norm, hx19_1, hx20_1, hx21_1, hx24_1, hx25_1, hx26_1, hx27_1, hfp_1, hvregs_1] at hx19_2 hx20_2 hx21_2 hx22_2 hx23_2 hx24_2 hx25_2 hx26_2 hx27_2 hx28_2 hfp_2 hvregs_2
  refine SepWP.mono (h_finish
    (s0.readReg64 (Reg.gpr 0#5)) (s0.readReg64 (Reg.gpr 1#5)) (s0.readReg64 (Reg.gpr 3#5))
    st chunk dec1 outSt hout_eq g gdk ekCap ekPtr _ hek_le hek_lt
    hsp0_align hfsp_align hpc2 hrun2 hsp2
    hx19_2 hx20_2 hx21_2 hx22_2 hx23_2 hx24_2 hx25_2 hx26_2 hx27_2 hfp_2 htr2 hvregs_2
    (by ac_rfl)) ?_
  intro sf P_f _ _ ⟨hmem, hsp_sf, hcs_sf⟩
  refine ⟨fun hm => ?_, hsp_sf, hcs_sf⟩
  have h1 := hmem R hm
  simp only [sepConj_assoc, satisfies_pure_sepConj] at h1 ⊢
  exact h1

end CryptoVerification.SpqrV1.States.Leaves
