/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SpqrV1.Poly.DecodedMessage.Defs
public import LibsignalBinary.Proofs.SpqrV1.States.Recv.ArmCt1SampledPart5
import LibsignalBinary.Proofs.SpqrV1.Kdf.HkdfToSliceExtract
import LibsignalBinary.Proofs.SpqrV1.States.FromPb.Defs
import LibsignalBinary.Proofs.SpqrV1.States.Leaves.SendChunk1
import LibsignalBinary.Proofs.SpqrV1.States.Recv.ArmCt1SampledPart1
import LibsignalBinary.Proofs.SpqrV1.States.Recv.ArmCt1SampledPart3
import LibsignalBinary.Proofs.SpqrV1.States.Recv.Dispatch
import ProofLib.SepLogic.WPp

/-!
# `<States>::recv` — `.ct1Sampled` Arm, Part 7 (Common Prefix & Path 4a)

`Split928` state-reconstruction equations, pure `States.recv` reductions on `.ct1Sampled`,
the common `recv_ek_chunk` prefix (`+11404 -> +11496`), and Path 4a (`outMsg = none, ack = false`:
`+11496 -> s0.x30`).
-/

@[expose] public section

namespace CryptoVerification.SpqrV1.States.Recv

open Arm64 ProofLib ProofLib.ProgramReflection
open CryptoGames.LibsignalSession (ShaCompress)
open CryptoVerification.RustHeap
open CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchetRepr
open CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalSpqrV1
open CryptoVerification.SpqrV1.Auth
open CryptoVerification.SpqrV1.Poly
open CryptoVerification.SpqrV1.Poly.AddChunk
open CryptoVerification.SpqrV1.Poly.DecodedMessage
open CryptoVerification.SpqrV1.Drop

open CryptoVerification.SpqrV1.States.Leaves
open CryptoVerification.SpqrV1.States.Leaves.RecvHdrChunk
open CryptoVerification.CodeLayout

set_option maxRecDepth 200000
set_option maxHeartbeats 400000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

attribute [local irreducible] Program.fetch Program.externAt? Program.fnOff
attribute [local arm64_norm, local wp_norm] bv_sub_add_lit BitVec.toNat_zero
attribute [-arm64_norm]
  Kdf.HkdfToSliceProof.sp_sub_688_eq_hsp
  Kdf.HkdfToSliceProof.sp_add_neg688_eq_hsp
  Kdf.HkdfToSliceProof.sp_sub_96_eq_hsp_592
  Kdf.HkdfToSliceProof.sp_add_neg96_eq_hsp_592

/-! ## 1. `Split928` State-Reconstruction Helpers (`Words50` & `Words16`) -/

def mkC3FromEnc2Uc14 (w48 w49 : BitVec 64) (c_uc : Words16) : Words16 where
  w0 := w48
  w1 := w49
  w2 := c_uc.w0
  w3 := c_uc.w1
  w4 := c_uc.w2
  w5 := c_uc.w3
  w6 := c_uc.w4
  w7 := c_uc.w5
  w8 := c_uc.w6
  w9 := c_uc.w7
  w10 := c_uc.w8
  w11 := c_uc.w9
  w12 := c_uc.w10
  w13 := c_uc.w11
  w14 := c_uc.w12
  w15 := c_uc.w13

theorem wordsAt_528_eq_words50_and_words16 (a : BitVec 64) (c_enc : Words50) (c_uc : Words16) :
    words50At a c_enc ∗ wordsAt (a + 400#64) c_uc.toList =
      wordsAt a c_enc.c0.toList ∗
      wordsAt (a + 128#64) c_enc.c1.toList ∗
      wordsAt (a + 256#64) c_enc.c2.toList ∗
      wordsAt (a + 384#64) (mkC3FromEnc2Uc14 c_enc.w48 c_enc.w49 c_uc).toList ∗
      ((a + 512#64) ↦₆₄ c_uc.w14) ∗
      ((a + 520#64) ↦₆₄ c_uc.w15) := by
  dsimp only [words50At, mkC3FromEnc2Uc14, Words16.toList]
  simp only [wordsAt_16, BitVec.add_assoc, BitVec.reduceAdd]
  ac_rfl

theorem split928At_mkSplit928From528And400_eq (outA : BitVec 64)
    (c_enc : Words50) (c_uc : Words16) (d400 : Split400) :
    split928At outA (mkSplit928From528And400 c_enc.c0 c_enc.c1 c_enc.c2
        (mkC3FromEnc2Uc14 c_enc.w48 c_enc.w49 c_uc) c_uc.w14 c_uc.w15 d400) =
      words50At outA c_enc ∗
      wordsAt (outA + 400#64) c_uc.toList ∗
      split400At (outA + 528#64) d400 := by
  dsimp only [split928At, mkSplit928From528And400, mkC3FromEnc2Uc14,
    words50At, split400At, Words16.toList, Words5.toList]
  rw [← mid376At_eq_pointsToBytes (outA + 512#64) c_uc.w14 c_uc.w15 d400.w0 d400.mid352]
  dsimp only [mid376At]
  simp only [wordsAt_16, wordsAt_5, BitVec.add_assoc, BitVec.reduceAdd]
  ac_rfl

def Words50.tailBytes (u : Words50) : List (BitVec 8) :=
  wordsBytes [u.c0.w1, u.c0.w2, u.c0.w3, u.c0.w4, u.c0.w5, u.c0.w6, u.c0.w7,
    u.c0.w8, u.c0.w9, u.c0.w10, u.c0.w11, u.c0.w12, u.c0.w13, u.c0.w14, u.c0.w15] ++
    (wordsBytes u.c1.toList ++ (wordsBytes u.c2.toList ++ wordsBytes [u.w48, u.w49]))

theorem words50At_eq_tag_and_tailBytes (a : BitVec 64) (u : Words50) :
    words50At a u = ((a ↦₆₄ u.c0.w0) ∗ ((a + 8#64) ↦ₛ u.tailBytes)) := by
  rw [words50At_eq_pointsToBytes a u]
  have hbytes : u.toBytes = unpack64 u.c0.w0 ++ u.tailBytes := by
    dsimp only [Words50.toBytes, Words50.tailBytes, Words16.toList, wordsBytes]
    rw [List.append_assoc]
  rw [hbytes, pointsToBytes_append a (unpack64 u.c0.w0) u.tailBytes,
      unpack64_length, ← pointsTo64_eq_pointsToBytes a u.c0.w0]

theorem exists_words50_with_tag {tag : BitVec 64} {bs : List (BitVec 8)} (h : bs.length = 392) :
    ∃ u : Words50, u.c0.w0 = tag ∧ bs = u.tailBytes := by
  have h0 : (bs.take 120).length = 8 * 15 := by simp [List.length_take]; omega
  have h1 : ((bs.drop 120).take 128).length = 128 := by simp [List.length_take, List.length_drop]; omega
  have h2 : (((bs.drop 120).drop 128).take 128).length = 128 := by
    simp [List.length_take, List.length_drop]; omega
  have h3 : (((bs.drop 120).drop 128).drop 128).length = 8 * 2 := by
    simp [List.length_drop]; omega
  obtain ⟨ws0, hlen0, hws0⟩ := exists_words_of_length 15 (bs.take 120) h0
  rcases ws0 with _ | ⟨w1, _ | ⟨w2, _ | ⟨w3, _ | ⟨w4, _ | ⟨w5, _ | ⟨w6, _ | ⟨w7,
    _ | ⟨w8, _ | ⟨w9, _ | ⟨w10, _ | ⟨w11, _ | ⟨w12, _ | ⟨w13, _ | ⟨w14, _ | ⟨w15, _ | _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩ <;>
    try simp at hlen0
  obtain ⟨c1, hc1⟩ := exists_words16_of_length_128 h1
  obtain ⟨c2, hc2⟩ := exists_words16_of_length_128 h2
  obtain ⟨ws3, hlen3, hws3⟩ := exists_words_of_length 2 _ h3
  rcases ws3 with _ | ⟨w48, _ | ⟨w49, _ | _⟩⟩ <;> try simp at hlen3
  refine ⟨⟨⟨tag, w1, w2, w3, w4, w5, w6, w7, w8, w9, w10, w11, w12, w13, w14, w15⟩,
    c1, c2, w48, w49⟩, rfl, ?_⟩
  dsimp only [Words50.tailBytes]
  rw [← hws0, ← hc1, ← hc2, ← hws3]
  simp only [List.take_append_drop]

theorem polyEncoderAt_extract_words50 (A : RustAlloc) (a : BitVec 64) (enc : PolyEncoder) :
    polyEncoderAt A a enc ⊢
    ∃∗ u : Words50,
      ⌜u.c0.w0 = polyEncoderTagVal enc⌝ ∗
      words50At a u ∗
      relocatedHeap (fun b => polyEncoderBodyAt A b enc) u.tailBytes := by
  rw [polyEncoderAt_eq_tag_body A a enc]
  refine Entails.trans (sepConj_mono_right (Relocatable.of_polyEncoderBodyAt A enc (a + 8#64))) ?_
  rw [sepExists_sepConj_right]
  apply Entails.sepExists_elim; intro bs
  rw [sepConj_left_comm]
  apply Entails.pure_left; intro hlen
  obtain ⟨u, htag, rfl⟩ := exists_words50_with_tag (tag := polyEncoderTagVal enc) hlen
  refine Entails.sepExists_right u ?_
  refine Entails.pure_right htag ?_
  rw [words50At_eq_tag_and_tailBytes a u, htag, ← sepConj_assoc]
  exact Entails.refl _

theorem polyEncoderAt_reconstruct_words50 (A : RustAlloc) (a : BitVec 64) (enc : PolyEncoder)
    (u : Words50) (htag : u.c0.w0 = polyEncoderTagVal enc) :
    words50At a u ∗ relocatedHeap (fun b => polyEncoderBodyAt A b enc) u.tailBytes ⊢
    polyEncoderAt A a enc := by
  rw [words50At_eq_tag_and_tailBytes a u, htag, polyEncoderAt_eq_tag_body A a enc, sepConj_assoc]
  exact sepConj_mono_right
    (relocatedHeap_recompose (fun b => polyEncoderBodyAt A b enc) u.tailBytes (a + 8#64))

theorem split928At_reconstruct_ct1Sampled_updated {A : RustAlloc} {F : ShaCompress}
    (outA : BitVec 64)
    (st : Chunked.SendCt.Ct1Sampled spqrPolyApi (spqrAuthApi F))
    (dec' : PolyDecoder)
    (c_enc : Words50) (c_uc : Words16) (d400 : Split400)
    (htag_enc : c_enc.c0.w0 = polyEncoderTagVal st.sending_ct1)
    (hmid352 : d400.mid352.length = 352) :
    split928At outA (mkSplit928From528And400 c_enc.c0 c_enc.c1 c_enc.c2
        (mkC3FromEnc2Uc14 c_enc.w48 c_enc.w49 c_uc) c_uc.w14 c_uc.w15 d400) ∗
      relocatedHeap (fun b => polyEncoderBodyAt A b st.sending_ct1) c_enc.tailBytes ∗
      relocatedHeap (fun a => unchunkedCt1SentAt A a st.uc) (wordsBytes c_uc.toList) ∗
      relocatedHeap (fun a => polyDecoderAt A a dec') d400.toBytes ⊢
    chunkedStatesAt A outA (.ct1Sampled { st with receiving_ek := dec' }) := by
  rw [split928At_mkSplit928From528And400_eq,
      split400At_eq_pointsToBytes (outA + 528#64) d400 hmid352]
  dsimp only [chunkedStatesAt, chunkedCt1SampledAt]
  have henc := polyEncoderAt_reconstruct_words50 A outA st.sending_ct1 c_enc htag_enc
  have huc := Relocatable.reconstruct_128 (fun a => unchunkedCt1SentAt A a st.uc) (outA + 400#64) c_uc
  have hdec := relocatedHeap_recompose (fun a => polyDecoderAt A a dec') d400.toBytes (outA + 528#64)
  refine Entails.trans (Entails.of_eq (show _ =
    (words50At outA c_enc ∗
      relocatedHeap (fun b => polyEncoderBodyAt A b st.sending_ct1) c_enc.tailBytes) ∗
    (wordsAt (outA + 400#64) c_uc.toList ∗
      relocatedHeap (fun a => unchunkedCt1SentAt A a st.uc) (wordsBytes c_uc.toList)) ∗
    (((outA + 528#64) ↦ₛ d400.toBytes) ∗
      relocatedHeap (fun a => polyDecoderAt A a dec') d400.toBytes) by ac_rfl)) ?_
  exact sepConj_mono henc (sepConj_mono huc hdec)

theorem split928At_mkSplit928Ct1Acknowledged_eq (outA : BitVec 64)
    (c_uc : Words16) (c_dec : Words50) (bs352 : List (BitVec 8)) (tail5 : Words5) :
    split928At outA (mkSplit928Ct1Acknowledged c_uc c_dec bs352 tail5) =
      (outA ↦₆₄ 11#64) ∗
      wordsAt (outA + 8#64) c_uc.toList ∗
      words50At (outA + 136#64) c_dec ∗
      ((outA + 536#64) ↦ₛ bs352) ∗
      wordsAt (outA + 888#64) tail5.toList := by
  dsimp only [split928At, mkSplit928Ct1Acknowledged, words50At, Words16.toList, Words5.toList]
  rw [← mid376At_eq_pointsToBytes (outA + 512#64) c_dec.c2.w15 c_dec.w48 c_dec.w49 bs352]
  dsimp only [mid376At]
  simp only [wordsAt_16, wordsAt_5, BitVec.add_assoc, BitVec.reduceAdd]
  ac_rfl

theorem split928At_reconstruct_ct1Acknowledged {A : RustAlloc} {F : ShaCompress}
    (outA : BitVec 64)
    (uc : Unchunked.SendCt.Ct1Sent (spqrAuthApi F))
    (dec' : PolyDecoder)
    (c_uc : Words16) (c_dec : Words50)
    (bs352 : List (BitVec 8)) (tail5 : Words5)
    (hbs352 : bs352.length = 352) :
    split928At outA (mkSplit928Ct1Acknowledged c_uc c_dec bs352 tail5) ∗
      relocatedHeap (fun a => unchunkedCt1SentAt A a uc) (wordsBytes c_uc.toList) ∗
      relocatedHeap (fun a => polyDecoderAt A a dec') c_dec.toBytes ⊢
    chunkedStatesAt A outA (.ct1Acknowledged { uc := uc, receiving_ek := dec' }) := by
  rw [split928At_mkSplit928Ct1Acknowledged_eq,
      words50At_eq_pointsToBytes (outA + 136#64) c_dec]
  dsimp only [chunkedStatesAt, chunkedCt1AcknowledgedAt, BitVec.ofNat_eq_ofNat]
  simp only [BitVec.add_assoc, BitVec.reduceAdd]
  have huc := Relocatable.reconstruct_128 (fun a => unchunkedCt1SentAt A a uc) (outA + 8#64) c_uc
  have hdec := relocatedHeap_recompose (fun a => polyDecoderAt A a dec') c_dec.toBytes (outA + 136#64)
  have hpad : ((outA + 536#64) ↦ₛ bs352) ∗ wordsAt (outA + 888#64) tail5.toList ⊢
      memRegion (outA + 536#64) 392 := by
    rw [ProofLib.memRegion_split' (b := outA + 536#64) (n := 352) (k := 40)
      (b' := outA + 888#64) rfl (by bv_omega) (by decide)]
    have h1 : ((outA + 536#64) ↦ₛ bs352) ⊢ memRegion (outA + 536#64) 352 := by
      rw [← hbs352]; exact ProofLib.pointsToBytes_entails_memRegion _ _
    exact sepConj_mono h1 (wordsAt_entails_memRegion tail5.toList (outA + 888#64) 40 rfl)
  refine Entails.trans (Entails.of_eq (show _ =
    (outA ↦₆₄ 11#64) ∗
    ((wordsAt (outA + 8#64) c_uc.toList ∗
      relocatedHeap (fun a => unchunkedCt1SentAt A a uc) (wordsBytes c_uc.toList)) ∗
     (((outA + 136#64) ↦ₛ c_dec.toBytes) ∗
      relocatedHeap (fun a => polyDecoderAt A a dec') c_dec.toBytes)) ∗
    (((outA + 536#64) ↦ₛ bs352) ∗ wordsAt (outA + 888#64) tail5.toList) by ac_rfl)) ?_
  exact sepConj_mono_right (sepConj_mono (sepConj_mono huc hdec) hpad)

theorem split928At_mkSplit928EkReceivedCt1Sampled_eq (outA : BitVec 64)
    (c_enc : Words50) (c_ek : Words16) (bs352 : List (BitVec 8)) (tail5 : Words5) :
    split928At outA (mkSplit928EkReceivedCt1Sampled c_enc c_ek bs352 tail5) =
      (outA ↦₆₄ 10#64) ∗
      words50At (outA + 8#64) c_enc ∗
      wordsAt (outA + 408#64) c_ek.toList ∗
      ((outA + 536#64) ↦ₛ bs352) ∗
      wordsAt (outA + 888#64) tail5.toList := by
  dsimp only [split928At, mkSplit928EkReceivedCt1Sampled, words50At, Words16.toList, Words5.toList]
  rw [← mid376At_eq_pointsToBytes (outA + 512#64) c_ek.w13 c_ek.w14 c_ek.w15 bs352]
  dsimp only [mid376At]
  simp only [wordsAt_16, wordsAt_5, BitVec.add_assoc, BitVec.reduceAdd]
  ac_rfl

theorem split928At_reconstruct_ekReceivedCt1Sampled {A : RustAlloc} {F : ShaCompress}
    (outA : BitVec 64)
    (enc : PolyEncoder)
    (uc_ek : Unchunked.SendCt.Ct1SentEkReceived (spqrAuthApi F))
    (c_enc : Words50) (c_ek : Words16)
    (bs352 : List (BitVec 8)) (tail5 : Words5)
    (htag_enc : c_enc.c0.w0 = polyEncoderTagVal enc)
    (hbs352 : bs352.length = 352) :
    split928At outA (mkSplit928EkReceivedCt1Sampled c_enc c_ek bs352 tail5) ∗
      relocatedHeap (fun b => polyEncoderBodyAt A b enc) c_enc.tailBytes ∗
      relocatedHeap (fun a => unchunkedCt1SentEkReceivedAt A a uc_ek) (wordsBytes c_ek.toList) ⊢
    chunkedStatesAt A outA (.ekReceivedCt1Sampled { uc := uc_ek, sending_ct1 := enc }) := by
  rw [split928At_mkSplit928EkReceivedCt1Sampled_eq]
  dsimp only [chunkedStatesAt, chunkedEkReceivedCt1SampledAt, BitVec.ofNat_eq_ofNat]
  simp only [BitVec.add_assoc, BitVec.reduceAdd]
  have henc := polyEncoderAt_reconstruct_words50 A (outA + 8#64) enc c_enc htag_enc
  have hek := Relocatable.reconstruct_128 (fun a => unchunkedCt1SentEkReceivedAt A a uc_ek) (outA + 408#64) c_ek
  have hpad : ((outA + 536#64) ↦ₛ bs352) ∗ wordsAt (outA + 888#64) tail5.toList ⊢
      memRegion (outA + 536#64) 392 := by
    rw [ProofLib.memRegion_split' (b := outA + 536#64) (n := 352) (k := 40)
      (b' := outA + 888#64) rfl (by bv_omega) (by decide)]
    have h1 : ((outA + 536#64) ↦ₛ bs352) ⊢ memRegion (outA + 536#64) 352 := by
      rw [← hbs352]; exact ProofLib.pointsToBytes_entails_memRegion _ _
    exact sepConj_mono h1 (wordsAt_entails_memRegion tail5.toList (outA + 888#64) 40 rfl)
  refine Entails.trans (Entails.of_eq (show _ =
    (outA ↦₆₄ 10#64) ∗
    ((words50At (outA + 8#64) c_enc ∗
      relocatedHeap (fun b => polyEncoderBodyAt A b enc) c_enc.tailBytes) ∗
     (wordsAt (outA + 408#64) c_ek.toList ∗
      relocatedHeap (fun a => unchunkedCt1SentEkReceivedAt A a uc_ek) (wordsBytes c_ek.toList))) ∗
    (((outA + 536#64) ↦ₛ bs352) ∗ wordsAt (outA + 888#64) tail5.toList) by ac_rfl)) ?_
  exact sepConj_mono_right (sepConj_mono (sepConj_mono henc hek) hpad)

/-! ## 2. Pure `States.recv` Reductions & Exit Combinators -/

theorem ct1Sampled_add_and_decode_eq_ok (dec : PolyDecoder) (chunk : Chunk)
    (hlen : dec.pts.length = 16) (hsort : PolyDecoderStrictSorted dec) :
    spqrPolyApi.add_chunk dec chunk = .ok (addChunkTotal dec chunk) ∧
    spqrPolyApi.decoded_message (addChunkTotal dec chunk) =
      .ok (decodedMessageTotal (addChunkTotal dec chunk)) ∧
    PolyDecoderStrictSorted (addChunkTotal dec chunk) ∧
    (addChunkTotal dec chunk).pts.length = 16 := by
  have hadd : dec.addChunk chunk = .ok (addChunkTotal dec chunk) :=
    addChunk_eq_ok dec chunk hlen
  have hlen' : (addChunkTotal dec chunk).pts.length = 16 :=
    addChunkTotal_pts_length dec chunk hlen
  have hsort' : PolyDecoderStrictSorted (addChunkTotal dec chunk) :=
    (addChunkBsearch_eq_addChunkTotal dec chunk hlen hsort).2
  have hdec : (addChunkTotal dec chunk).decodedMessage =
      .ok (decodedMessageTotal (addChunkTotal dec chunk)) :=
    decodedMessage_eq_ok (addChunkTotal dec chunk) hlen' hsort'
  refine ⟨?_, ?_, hsort', hlen'⟩
  · dsimp only [spqrPolyApi]
    rw [hadd]
    rfl
  · dsimp only [spqrPolyApi]
    rw [hdec]
    rfl

attribute [local irreducible] addChunkTotal decodedMessageTotal

/-- `Unchunked.SendCt.Ct1Sent.recv_ek K uc uc.epoch ek` is always `StatesResult.ofError res`
    with either `res = .ok { epoch := uc.epoch, auth := uc.auth, es := uc.es, ek := ek, ct1 := uc.ct1 }`
    or `res = .error .erroneousDataReceived`. -/
theorem ct1Sent_recv_ek_eq_ofError {F : ShaCompress} (K : MlKem)
    (uc : Unchunked.SendCt.Ct1Sent (spqrAuthApi F)) (ek : Bytes) :
    let res : Except Error (Unchunked.SendCt.Ct1SentEkReceived (spqrAuthApi F)) :=
      if K.validPkBytes uc.hdr ek then
        .ok { epoch := uc.epoch, auth := uc.auth, es := uc.es, ek := ek, ct1 := uc.ct1 }
      else
        .error .erroneousDataReceived
    uc.recv_ek K uc.epoch ek = StatesResult.ofError res := by
  by_cases h : K.validPkBytes uc.hdr ek = true
  · simp [Unchunked.SendCt.Ct1Sent.recv_ek, ek_matches_header, StatesResult.ofError, h]
  · have hf : K.validPkBytes uc.hdr ek = false := Bool.eq_false_iff.mpr h
    simp [Unchunked.SendCt.Ct1Sent.recv_ek, ek_matches_header, StatesResult.ofError, hf]

theorem states_recv_ct1Sampled_eq_none_no_ack {F : ShaCompress} (K : MlKem)
    (st : Chunked.SendCt.Ct1Sampled spqrPolyApi (spqrAuthApi F))
    (msg : Message spqrPolyApi) (chunk : Chunk)
    (heq : msg.epoch = st.uc.epoch)
    (hpay : msg.payload = .ek chunk)
    (hlen : st.receiving_ek.pts.length = 16)
    (hsort : PolyDecoderStrictSorted st.receiving_ek)
    (hdec : decodedMessageTotal (addChunkTotal st.receiving_ek chunk) = none) :
    (States.ct1Sampled st).recv K msg =
      .ok { key := none, state := .ct1Sampled { st with receiving_ek := addChunkTotal st.receiving_ek chunk } } := by
  have ⟨hadd, hdm, _, _⟩ := ct1Sampled_add_and_decode_eq_ok st.receiving_ek chunk hlen hsort
  have hirr : ¬ (st.uc.epoch < st.uc.epoch) := BitVec.lt_irrefl _
  simp only [States.recv, Chunked.SendCt.Ct1Sampled.epoch, Unchunked.SendCt.Ct1Sent.epoch,
    heq, gt_iff_lt, hirr, hpay, Bool.false_eq_true, ↓reduceIte,
    Chunked.SendCt.Ct1Sampled.recv_ek_chunk,
    hadd, hdm, hdec, StatesResult.ofPanic, Bind.bind, Except.bind]

theorem states_recv_ct1Sampled_eq_none_ack {F : ShaCompress} (K : MlKem)
    (st : Chunked.SendCt.Ct1Sampled spqrPolyApi (spqrAuthApi F))
    (msg : Message spqrPolyApi) (chunk : Chunk)
    (heq : msg.epoch = st.uc.epoch)
    (hpay : msg.payload = .ekCt1Ack chunk)
    (hlen : st.receiving_ek.pts.length = 16)
    (hsort : PolyDecoderStrictSorted st.receiving_ek)
    (hdec : decodedMessageTotal (addChunkTotal st.receiving_ek chunk) = none) :
    (States.ct1Sampled st).recv K msg =
      .ok { key := none, state := .ct1Acknowledged { uc := st.uc, receiving_ek := addChunkTotal st.receiving_ek chunk } } := by
  have ⟨hadd, hdm, _, _⟩ := ct1Sampled_add_and_decode_eq_ok st.receiving_ek chunk hlen hsort
  have hirr : ¬ (st.uc.epoch < st.uc.epoch) := BitVec.lt_irrefl _
  simp only [States.recv, Chunked.SendCt.Ct1Sampled.epoch, Unchunked.SendCt.Ct1Sent.epoch,
    heq, gt_iff_lt, hirr, hpay, Bool.false_eq_true, ↓reduceIte,
    Chunked.SendCt.Ct1Sampled.recv_ek_chunk,
    hadd, hdm, hdec, StatesResult.ofPanic, Bind.bind, Except.bind]

theorem states_recv_ct1Sampled_eq_some_err {F : ShaCompress} (K : MlKem)
    (st : Chunked.SendCt.Ct1Sampled spqrPolyApi (spqrAuthApi F))
    (msg : Message spqrPolyApi) (chunk : Chunk) (decoded : Bytes) (err : Error)
    (heq : msg.epoch = st.uc.epoch)
    (hpay : msg.payload = .ek chunk ∨ msg.payload = .ekCt1Ack chunk)
    (hlen : st.receiving_ek.pts.length = 16)
    (hsort : PolyDecoderStrictSorted st.receiving_ek)
    (hdec : decodedMessageTotal (addChunkTotal st.receiving_ek chunk) = some decoded)
    (hrek : st.uc.recv_ek K st.uc.epoch decoded = .error (.err err)) :
    (States.ct1Sampled st).recv K msg = .error (.err err) := by
  have ⟨hadd, hdm, _, _⟩ := ct1Sampled_add_and_decode_eq_ok st.receiving_ek chunk hlen hsort
  have hirr : ¬ (st.uc.epoch < st.uc.epoch) := BitVec.lt_irrefl _
  rcases hpay with hpay | hpay <;> {
    simp only [States.recv, Chunked.SendCt.Ct1Sampled.epoch, Unchunked.SendCt.Ct1Sent.epoch,
      heq, gt_iff_lt, hirr, hpay, Bool.false_eq_true, ↓reduceIte,
      Chunked.SendCt.Ct1Sampled.recv_ek_chunk,
      hadd, hdm, hdec, hrek, StatesResult.ofPanic, Bind.bind, Except.bind]
  }

theorem states_recv_ct1Sampled_eq_some_ok_no_ack {F : ShaCompress} (K : MlKem)
    (st : Chunked.SendCt.Ct1Sampled spqrPolyApi (spqrAuthApi F))
    (msg : Message spqrPolyApi) (chunk : Chunk) (decoded : Bytes)
    (uc_ek : Unchunked.SendCt.Ct1SentEkReceived (spqrAuthApi F))
    (heq : msg.epoch = st.uc.epoch)
    (hpay : msg.payload = .ek chunk)
    (hlen : st.receiving_ek.pts.length = 16)
    (hsort : PolyDecoderStrictSorted st.receiving_ek)
    (hdec : decodedMessageTotal (addChunkTotal st.receiving_ek chunk) = some decoded)
    (hrek : st.uc.recv_ek K st.uc.epoch decoded = .ok uc_ek) :
    (States.ct1Sampled st).recv K msg =
      .ok { key := none, state := .ekReceivedCt1Sampled { uc := uc_ek, sending_ct1 := st.sending_ct1 } } := by
  have ⟨hadd, hdm, _, _⟩ := ct1Sampled_add_and_decode_eq_ok st.receiving_ek chunk hlen hsort
  have hirr : ¬ (st.uc.epoch < st.uc.epoch) := BitVec.lt_irrefl _
  simp only [States.recv, Chunked.SendCt.Ct1Sampled.epoch, Unchunked.SendCt.Ct1Sent.epoch,
    heq, gt_iff_lt, hirr, hpay, Bool.false_eq_true, ↓reduceIte,
    Chunked.SendCt.Ct1Sampled.recv_ek_chunk,
    hadd, hdm, hdec, hrek, StatesResult.ofPanic, Bind.bind, Except.bind]

theorem states_recv_ct1Sampled_eq_some_ok_ack {F : ShaCompress} (K : MlKem)
    (st : Chunked.SendCt.Ct1Sampled spqrPolyApi (spqrAuthApi F))
    (msg : Message spqrPolyApi) (chunk : Chunk) (decoded : Bytes)
    (uc_ek : Unchunked.SendCt.Ct1SentEkReceived (spqrAuthApi F))
    (uc2 : Unchunked.SendCt.Ct2Sent (spqrAuthApi F)) (ct2 mac : Bytes) (enc2 : PolyEncoder)
    (heq : msg.epoch = st.uc.epoch)
    (hpay : msg.payload = .ekCt1Ack chunk)
    (hlen : st.receiving_ek.pts.length = 16)
    (hsort : PolyDecoderStrictSorted st.receiving_ek)
    (hdec : decodedMessageTotal (addChunkTotal st.receiving_ek chunk) = some decoded)
    (hrek : st.uc.recv_ek K st.uc.epoch decoded = .ok uc_ek)
    (hsc2 : uc_ek.send_ct2 K = .ok (uc2, ct2, mac))
    (henc2 : Chunked.SendCt.send_ct2_encoder spqrPolyApi ct2 mac = .ok enc2) :
    (States.ct1Sampled st).recv K msg =
      .ok { key := none, state := .ct2Sampled { uc := uc2, sending_ct2 := enc2 } } := by
  have ⟨hadd, hdm, _, _⟩ := ct1Sampled_add_and_decode_eq_ok st.receiving_ek chunk hlen hsort
  have hirr : ¬ (st.uc.epoch < st.uc.epoch) := BitVec.lt_irrefl _
  simp only [States.recv, Chunked.SendCt.Ct1Sampled.epoch, Unchunked.SendCt.Ct1Sent.epoch,
    heq, gt_iff_lt, hirr, hpay, Bool.false_eq_true, ↓reduceIte,
    Chunked.SendCt.Ct1Sampled.recv_ek_chunk,
    hadd, hdm, hdec, hrek, hsc2, henc2, StatesResult.ofPanic, Bind.bind, Except.bind]

open CryptoVerification.SpqrV1.Top.MessageSerialize

theorem sepWPp_intro_ex' {α : Type} {prog : Program} {target_pc : BitVec 64} {s : State}
    {P : α → SepProp} {Q Q_panic : State → SepProp → Prop} (hrun : s.status = .Running)
    (h : ∀ x, SepWPp prog target_pc s (P x) Q Q_panic) :
    SepWPp prog target_pc s (∃∗ x, P x) Q Q_panic := by
  apply SepWPp.of_sepWP
  rw [← emp_sepConj (∃∗ x, P x), sepExists_sepConj_right]
  apply ProofLib.SepWP.exists_left
  intro x; rw [emp_sepConj]
  exact SepWP.done rfl hrun (h x)

theorem sepWPp_of_ct1Sampled_exit {b : BitVec 64} {A : RustAlloc} {F : ShaCompress} {K : MlKem}
    {ext : String → Option (State → State)}
    (s0 s : State) (outA selfA msgA : BitVec 64)
    (self : States spqrPolyApi (spqrAuthApi F)) (msg : Message spqrPolyApi)
    (P R : SepProp)
    (hexit : SepWP (tripleRatchetProgAtExt b ext) (s0.readReg64 .x30) s P
      (fun sf Pf =>
        (Pf ⊢
          resultV1RecvAt A (F := F) outA (self.recv K msg) ∗
          memRegion selfA chunkedStatesSize ∗
          messageAt spqrPolyApi msgA msg ∗
          statesRecvRoAt b ∗
          A.pool ∗
          stackAt s0.sp statesRecvStackX) ∧
        sf.sp = s0.sp ∧
        CalleeSavedPreserved s0 sf ∧
        sf.trace = s0.trace)) :
    SepWPp (tripleRatchetProgAtExt b ext) (s0.readReg64 .x30) s P
      (fun sf P_f => sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf ∧
        (sf.mem ⊨ P_f ∗ R →
          sf.mem ⊨ ((statesRecvVariantSpec A F K b self msg).post ⟨outA, selfA, msgA⟩ s0 sf) ∗ R))
      (fun sf P_f => sf.mem ⊨ P_f ∗ R →
        sf.mem ⊨ ((statesRecvVariantSpec A F K b self msg).onPanic ⟨outA, selfA, msgA⟩ s0 sf) ∗ R) := by
  apply SepWPp.of_sepWP
  refine SepWP.mono hexit ?_
  intro sf Pf hpc_sf hrun_sf ⟨hPf, hsp_sf, hcs_sf, htr_sf⟩
  refine SepWPp.done hpc_sf hrun_sf ⟨hsp_sf, hcs_sf, fun hmem => ?_⟩
  dsimp only [statesRecvVariantSpec]
  exact Satisfies.mono (sepConj_mono_left (Entails.pure_right htr_sf hPf)) hmem

/-! ## 3. Stack Splits for `fsp + 976..4144` (`3168`B) and Common `recv_ek_chunk` Prefix (`+11404 -> +11496`) -/

theorem mid376At_entails_memRegion_376 (a w0 w8 w16 : BitVec 64)
    (bs352 : List (BitVec 8)) (h : bs352.length = 352) :
    mid376At a w0 w8 w16 bs352 ⊢ memRegion a 376 := by
  rw [mid376At_eq_pointsToBytes]
  exact pointsToBytes_entails_memRegion_376 a _ (mid376Bytes_length w0 w8 w16 h)

theorem memRegion_376_entails_mid376At (a : BitVec 64) :
    memRegion a 376 ⊢
    ∃∗ w0 : BitVec 64, ∃∗ w8 : BitVec 64, ∃∗ w16 : BitVec 64, ∃∗ bs352 : List (BitVec 8),
      ⌜bs352.length = 352⌝ ∗ mid376At a w0 w8 w16 bs352 := by
  rw [ProofLib.memRegion_split a 8 368 (by decide),
      ProofLib.memRegion_eight a,
      ProofLib.memRegion_split' (b := a + 8#64) (n := 8) (k := 360) (b' := a + 16#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_eight (a + 8#64),
      ProofLib.memRegion_split' (b := a + 16#64) (n := 8) (k := 352) (b' := a + 24#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_eight (a + 16#64),
      memRegion_eq_exists_bytes (a + 24#64) 352 (by decide)]
  simp only [sepExists_sepConj_left, sepExists_sepConj_right]
  apply Entails.sepExists_elim; intro bs352
  apply Entails.sepExists_elim; intro w16
  apply Entails.sepExists_elim; intro w8
  apply Entails.sepExists_elim; intro w0
  refine Entails.sepExists_right w0 (Entails.sepExists_right w8
    (Entails.sepExists_right w16 (Entails.sepExists_right bs352 ?_)))
  dsimp only [mid376At]
  exact Entails.of_eq (by ac_rfl)

theorem chunks528_and_400_entails_memRegion_928 (selfA : BitVec 64)
    (c0 c1 c2 c3 : Words16) (w512 w520 : BitVec 64) :
    wordsAt selfA c0.toList ∗
      wordsAt (selfA + 128#64) c1.toList ∗
      wordsAt (selfA + 256#64) c2.toList ∗
      wordsAt (selfA + 384#64) c3.toList ∗
      ((selfA + 512#64) ↦₆₄ w512) ∗
      ((selfA + 520#64) ↦₆₄ w520) ∗
      memRegion (selfA + 528#64) 400 ⊢
    memRegion selfA chunkedStatesSize := by
  unfold chunkedStatesSize
  have hc0 := words16_entails_memRegion_128 selfA c0
  have hc1 := words16_entails_memRegion_128 (selfA + 128#64) c1
  have hc2 := words16_entails_memRegion_128 (selfA + 256#64) c2
  have hc3 := words16_entails_memRegion_128 (selfA + 384#64) c3
  have hw512 := ProofLib.pointsTo64_entails_memRegion (selfA + 512#64) w512
  have hw520 := ProofLib.pointsTo64_entails_memRegion (selfA + 520#64) w520
  refine Entails.trans (sepConj_mono hc0 (sepConj_mono hc1 (sepConj_mono hc2 (sepConj_mono hc3
    (sepConj_mono hw512 (sepConj_mono_left hw520)))))) ?_
  rw [ProofLib.memRegion_split selfA 128 800 (by decide),
      ProofLib.memRegion_split' (b := selfA + 128#64) (n := 128) (k := 672) (b' := selfA + 256#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := selfA + 256#64) (n := 128) (k := 544) (b' := selfA + 384#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := selfA + 384#64) (n := 128) (k := 416) (b' := selfA + 512#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := selfA + 512#64) (n := 8) (k := 408) (b' := selfA + 520#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := selfA + 520#64) (n := 8) (k := 400) (b' := selfA + 528#64) rfl (by bv_omega) (by decide)]
  exact Entails.of_eq (by ac_rfl)

theorem words50_128_400_entails_memRegion_928 (selfA : BitVec 64) (c_enc : Words50) :
    words50At selfA c_enc ∗
      memRegion (selfA + 400#64) 128 ∗
      memRegion (selfA + 528#64) 400 ⊢
    memRegion selfA chunkedStatesSize := by
  unfold chunkedStatesSize
  rw [words50At_eq_pointsToBytes]
  have henc : (selfA ↦ₛ c_enc.toBytes) ⊢ memRegion selfA 400 := by
    have h := pointsToBytes_entails_memRegion selfA c_enc.toBytes
    rwa [Words50.toBytes_length] at h
  refine Entails.trans (sepConj_mono_left henc) ?_
  rw [ProofLib.memRegion_split selfA 400 528 (by decide),
      ProofLib.memRegion_split' (b := selfA + 400#64) (n := 128) (k := 400) (b' := selfA + 528#64) rfl (by bv_omega) (by decide)]
  exact Entails.of_eq (by ac_rfl)

theorem tag_384_8_128_400_entails_memRegion_928 (selfA tag : BitVec 64) :
    (selfA ↦₆₄ tag) ∗
      memRegion (selfA + 8#64) 384 ∗
      memRegion (selfA + 392#64) 8 ∗
      memRegion (selfA + 400#64) 128 ∗
      memRegion (selfA + 528#64) 400 ⊢
    memRegion selfA chunkedStatesSize := by
  unfold chunkedStatesSize
  refine Entails.trans (sepConj_mono_left (ProofLib.pointsTo64_entails_memRegion selfA tag)) ?_
  rw [ProofLib.memRegion_split selfA 8 920 (by decide),
      ProofLib.memRegion_split' (b := selfA + 8#64) (n := 384) (k := 536) (b' := selfA + 392#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := selfA + 392#64) (n := 8) (k := 528) (b' := selfA + 400#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := selfA + 400#64) (n := 128) (k := 400) (b' := selfA + 528#64) rfl (by bv_omega) (by decide)]
  exact Entails.of_eq (by ac_rfl)

theorem memRegion_3168_split_prefix (fsp : BitVec 64) :
    memRegion (fsp + 976#64) 3168 =
      memRegion (fsp + 976#64) 1776 ∗
      memRegion (fsp + 2752#64) 400 ∗
      memRegion (fsp + 3152#64) 544 ∗
      memRegion (fsp + 3696#64) 128 ∗
      memRegion (fsp + 3824#64) 8 ∗
      memRegion (fsp + 3832#64) 24 ∗
      memRegion (fsp + 3856#64) 288 := by
  rw [ProofLib.memRegion_split' (b := fsp + 976#64) (n := 1776) (k := 1392) (b' := fsp + 2752#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := fsp + 2752#64) (n := 400) (k := 992) (b' := fsp + 3152#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := fsp + 3152#64) (n := 544) (k := 448) (b' := fsp + 3696#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := fsp + 3696#64) (n := 128) (k := 320) (b' := fsp + 3824#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := fsp + 3824#64) (n := 8) (k := 312) (b' := fsp + 3832#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := fsp + 3832#64) (n := 24) (k := 288) (b' := fsp + 3856#64) rfl (by bv_omega) (by decide)]

set_option maxHeartbeats 1200000 in
/-- Common `recv_ek_chunk` prefix (`+11404 -> +11496`, `0x580e0 -> 0x5813c`):
    extracts the stack frame and `c_uc : Words16`, copies `st.uc` to `fsp + 3696` and `st.receiving_ek`
    to `fsp + 2752`, and calls `PolyDecoder::add_chunk` and `PolyDecoder::decoded_message`. -/
theorem ct1Sampled_recv_ek_common_prefix
    {b : BitVec 64} {A : RustAlloc} {F : ShaCompress} {P_pan : Prop}
    {ext : String → Option (State → State)}
    (hA : AllocContracts b A ext)
    (hmemcpy : subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr memcpyName) sessionMemcpyRegionSpec)
    (hdec_call : subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr polyDecoderDecodedMessageName)
      (polyDecoderDecodedMessageSpec A b))
    (hb : b &&& 0xfff#64 = 0#64)
    (s0 s_in : State) (fsp selfA outA msgA ack_val : BitVec 64)
    (st : Chunked.SendCt.Ct1Sampled spqrPolyApi (spqrAuthApi F))
    (chunk : Chunk)
    (hlen : st.receiving_ek.pts.length = 16)
    (hsort : PolyDecoderStrictSorted st.receiving_ek)
    (Rest R : SepProp)
    {post : State → SepProp → Prop}
    (hfsp_align : (fsp &&& 15#64 == 0#64) = true)
    (hpc : s_in.pc = (tripleRatchetProgAtExt b ext).fnAddr statesRecvName + 11404#64)
    (hrun : s_in.status = .Running)
    (hsp : s_in.sp = fsp)
    (hx1 : s_in.readReg64 .x1 = selfA)
    (hx19 : s_in.readReg64 .x19 = outA)
    (hx20 : s_in.readReg64 .x20 = st.uc.epoch)
    (hx21 : s_in.readReg64 .x21 = fsp + 3856#64)
    (hx22 : s_in.readReg64 .x22 = ack_val)
    (hx23 : s_in.readReg64 .x23 = polyEncoderTagVal st.sending_ct1)
    (hx24 : s_in.readReg64 .x24 = msgA)
    (hx28 : s_in.readReg64 .x28 = fsp + 3272#64)
    (hx29 : s_in.readReg64 .x29 = fsp + 4144#64)
    (htr : TraceCalleeSaved s_in s0)
    (hnext : ∀ (sf : State) (c_uc : Words16) (sc : CopyScratchStack) (k : EpilogueStoreStack),
      sf.pc = (tripleRatchetProgAtExt b ext).fnAddr statesRecvName + 11496#64 →
      sf.status = .Running →
      sf.sp = fsp →
      sf.readReg64 .x19 = outA →
      sf.readReg64 .x20 = st.uc.epoch →
      sf.readReg64 .x21 = fsp + 3856#64 →
      sf.readReg64 .x22 = ack_val →
      sf.readReg64 .x23 = polyEncoderTagVal st.sending_ct1 →
      sf.readReg64 .x24 = msgA →
      sf.readReg64 .x28 = fsp + 3272#64 →
      sf.readReg64 .x29 = fsp + 4144#64 →
      TraceCalleeSaved sf s0 →
      SepWPp (tripleRatchetProgAtExt b ext) (s0.readReg64 Reg.lr) sf
        (optVecU8At A (fsp + 3832#64) (decodedMessageTotal (addChunkTotal st.receiving_ek chunk)) ∗
          polyDecoderAt A (fsp + 2752#64) (addChunkTotal st.receiving_ek chunk) ∗
          chunkAt (msgA + 10#64) chunk ∗
          statesRecvRoAt b ∗
          A.pool ∗
          stackAt fsp statesRecvCalleeStackX ∗
          (polyEncoderAt A selfA st.sending_ct1 ∗
            wordsAt (selfA + 400#64) c_uc.toList ∗
            wordsAt (fsp + 3696#64) c_uc.toList ∗
            relocatedHeap (fun a => unchunkedCt1SentAt A a st.uc) (wordsBytes c_uc.toList) ∗
            memRegion (selfA + 528#64) 400 ∗
            copyScratchStackAt fsp sc ∗
            epilogueStoreStackPart1At fsp k ∗
            ((fsp + 232#64) ↦₆₄ selfA) ∗
            ((fsp + 512#64) ↦₆₄ k.w200) ∗
            ((fsp + 520#64) ↦₆₄ k.w208) ∗
            wordsAt (fsp + 528#64) k.tail.toList ∗
            memRegion (fsp + 576#64) 376 ∗
            memRegion (fsp + 568#64) 8 ∗
            memRegion (fsp + 952#64) 8 ∗
            memRegion (fsp + 976#64) 1776 ∗
            memRegion (fsp + 3152#64) 544 ∗
            memRegion (fsp + 3824#64) 8 ∗
            memRegion (fsp + 3856#64) 288 ∗
            Rest))
        post
        (fun sf P_f => (sf.mem ⊨ P_f ∗ R) →
          (sf.mem ⊨ (⌜(P_pan ∨ allocFailedIn s0 sf) ∧ s0.trace <+: sf.trace⌝ ∗ anyHeap) ∗ R))) :
    SepWPp (tripleRatchetProgAtExt b ext) (s0.readReg64 Reg.lr) s_in
      (polyEncoderAt A selfA st.sending_ct1 ∗
        unchunkedCt1SentAt A (selfA + 400#64) st.uc ∗
        polyDecoderAt A (selfA + 528#64) st.receiving_ek ∗
        chunkAt (msgA + 10#64) chunk ∗
        statesRecvRoAt b ∗
        A.pool ∗
        stackAt fsp statesRecvCalleeStackX ∗
        memRegion fsp 4144 ∗
        Rest)
      post
      (fun sf P_f => (sf.mem ⊨ P_f ∗ R) →
        (sf.mem ⊨ (⌜(P_pan ∨ allocFailedIn s0 sf) ∧ s0.trace <+: sf.trace⌝ ∗ anyHeap) ∗ R)) := by
  have ⟨_, hdm, _, _⟩ := ct1Sampled_add_and_decode_eq_ok st.receiving_ek chunk hlen hsort
  have hpre :
      polyEncoderAt A selfA st.sending_ct1 ∗
        unchunkedCt1SentAt A (selfA + 400#64) st.uc ∗
        polyDecoderAt A (selfA + 528#64) st.receiving_ek ∗
        chunkAt (msgA + 10#64) chunk ∗
        statesRecvRoAt b ∗
        A.pool ∗
        stackAt fsp statesRecvCalleeStackX ∗
        memRegion fsp 4144 ∗
        Rest ⊢
      ∃∗ c_uc : Words16, ∃∗ sc : CopyScratchStack, ∃∗ k : EpilogueStoreStack,
        wordsAt (selfA + 400#64) c_uc.toList ∗
        polyDecoderAt A (selfA + 528#64) st.receiving_ek ∗
        ((fsp + 232#64) ↦₆₄ k.we8) ∗
        memRegion (fsp + 2752#64) 400 ∗
        memRegion (fsp + 3696#64) 128 ∗
        (memRegion (fsp + 3832#64) 24 ∗
          chunkAt (msgA + 10#64) chunk ∗
          statesRecvRoAt b ∗
          A.pool ∗
          stackAt fsp statesRecvCalleeStackX ∗
          (polyEncoderAt A selfA st.sending_ct1 ∗
            relocatedHeap (fun a => unchunkedCt1SentAt A a st.uc) (wordsBytes c_uc.toList) ∗
            copyScratchStackAt fsp sc ∗
            epilogueStoreStackPart1At fsp k ∗
            ((fsp + 512#64) ↦₆₄ k.w200) ∗
            ((fsp + 520#64) ↦₆₄ k.w208) ∗
            wordsAt (fsp + 528#64) k.tail.toList ∗
            memRegion (fsp + 576#64) 376 ∗
            memRegion (fsp + 568#64) 8 ∗
            memRegion (fsp + 952#64) 8 ∗
            memRegion (fsp + 976#64) 1776 ∗
            memRegion (fsp + 3152#64) 544 ∗
            memRegion (fsp + 3824#64) 8 ∗
            memRegion (fsp + 3856#64) 288 ∗
            Rest)) := by
    refine Entails.trans (sepConj_mono_right
      (sepConj_mono (Relocatable.extract_128 (Relocatable.of_unchunkedCt1SentAt A st.uc) (selfA + 400#64))
        (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
          (sepConj_mono_right (sepConj_mono_left
            (memRegion_4144_entails_copyScratch_and_epilogueStack fsp))))))))) ?_
    simp only [sepExists_sepConj_left, sepExists_sepConj_right, memRegion_3168_split_prefix fsp]
    apply Entails.sepExists_elim; intro sc
    apply Entails.sepExists_elim; intro k
    apply Entails.sepExists_elim; intro c_uc
    refine Entails.sepExists_right c_uc (Entails.sepExists_right sc (Entails.sepExists_right k ?_))
    exact Entails.of_eq (by ac_rfl)
  refine SepWPp.weaken_pre hpre ?_
  apply sepWPp_intro_ex' hrun; intro c_uc
  apply sepWPp_intro_ex' hrun; intro sc
  apply sepWPp_intro_ex' hrun; intro k
  refine sepWPp_seq_clean
    (ct1Sampled_recv_ek_prefix_copy hmemcpy s_in fsp selfA k.we8 c_uc st.receiving_ek _
      hfsp_align hpc hrun hsp hx1) ?_
  intro s1 hpc1 hrun1 ⟨hsp1, hx19_1, hx20_1, hx21_1, hx22_1, hx23_1, hx24_1, hx28_1, hx29_1, htr1⟩
  have hreord :
      wordsAt (selfA + 400#64) c_uc.toList ∗
        wordsAt (fsp + 3696#64) c_uc.toList ∗
        polyDecoderAt A (fsp + 2752#64) st.receiving_ek ∗
        ((fsp + 232#64) ↦₆₄ selfA) ∗
        memRegion (selfA + 528#64) 400 ∗
        (memRegion (fsp + 3832#64) 24 ∗
          chunkAt (msgA + 10#64) chunk ∗
          statesRecvRoAt b ∗
          A.pool ∗
          stackAt fsp statesRecvCalleeStackX ∗
          (polyEncoderAt A selfA st.sending_ct1 ∗
            relocatedHeap (fun a => unchunkedCt1SentAt A a st.uc) (wordsBytes c_uc.toList) ∗
            copyScratchStackAt fsp sc ∗
            epilogueStoreStackPart1At fsp k ∗
            ((fsp + 512#64) ↦₆₄ k.w200) ∗
            ((fsp + 520#64) ↦₆₄ k.w208) ∗
            wordsAt (fsp + 528#64) k.tail.toList ∗
            memRegion (fsp + 576#64) 376 ∗
            memRegion (fsp + 568#64) 8 ∗
            memRegion (fsp + 952#64) 8 ∗
            memRegion (fsp + 976#64) 1776 ∗
            memRegion (fsp + 3152#64) 544 ∗
            memRegion (fsp + 3824#64) 8 ∗
            memRegion (fsp + 3856#64) 288 ∗
            Rest)) ⊢
      memRegion (fsp + 3832#64) 24 ∗
        polyDecoderAt A (fsp + 2752#64) st.receiving_ek ∗
        chunkAt (msgA + 10#64) chunk ∗
        statesRecvRoAt b ∗
        A.pool ∗
        stackAt fsp statesRecvCalleeStackX ∗
        (polyEncoderAt A selfA st.sending_ct1 ∗
          wordsAt (selfA + 400#64) c_uc.toList ∗
          wordsAt (fsp + 3696#64) c_uc.toList ∗
          relocatedHeap (fun a => unchunkedCt1SentAt A a st.uc) (wordsBytes c_uc.toList) ∗
          memRegion (selfA + 528#64) 400 ∗
          copyScratchStackAt fsp sc ∗
          epilogueStoreStackPart1At fsp k ∗
          ((fsp + 232#64) ↦₆₄ selfA) ∗
          ((fsp + 512#64) ↦₆₄ k.w200) ∗
          ((fsp + 520#64) ↦₆₄ k.w208) ∗
          wordsAt (fsp + 528#64) k.tail.toList ∗
          memRegion (fsp + 576#64) 376 ∗
          memRegion (fsp + 568#64) 8 ∗
          memRegion (fsp + 952#64) 8 ∗
          memRegion (fsp + 976#64) 1776 ∗
          memRegion (fsp + 3152#64) 544 ∗
          memRegion (fsp + 3824#64) 8 ∗
          memRegion (fsp + 3856#64) 288 ∗
          Rest) := Entails.of_eq (by ac_rfl)
  refine SepWPp.weaken_pre hreord ?_
  apply SepWPp.of_sepWP
  refine ct1Sampled_recv_ek_add_and_decode (P_pan := P_pan) hA hdec_call hb s0 s1 fsp msgA
    st.receiving_ek chunk (decodedMessageTotal (addChunkTotal st.receiving_ek chunk))
    hsort hdm _ R hfsp_align hpc1 hrun1 hsp1 (hx24_1.trans hx24) (htr1.trans htr) ?_
  intro sf hpc_sf hrun_sf hsp_sf hx19_sf hx20_sf hx21_sf hx22_sf hx23_sf hx24_sf hx28_sf hx29_sf htr_sf _
  apply SepWP.done hpc_sf hrun_sf
  exact hnext sf c_uc sc k hpc_sf hrun_sf hsp_sf
    (hx19_sf.trans (hx19_1.trans hx19))
    (hx20_sf.trans (hx20_1.trans hx20))
    (hx21_sf.trans (hx21_1.trans hx21))
    (hx22_sf.trans (hx22_1.trans hx22))
    (hx23_sf.trans (hx23_1.trans hx23))
    hx24_sf
    (hx28_sf.trans (hx28_1.trans hx28))
    (hx29_sf.trans (hx29_1.trans hx29))
    htr_sf

/-! ## 4. Path 4a (`outMsg = none, ack = false`: `+11496 -> s0.x30`) -/

theorem memRegion_none_no_ack_split (fsp : BitVec 64) (c_uc : Words16) :
    wordsAt (fsp + 3696#64) c_uc.toList ∗
      memRegion (fsp + 3832#64) 24 ∗
      memRegion (fsp + 976#64) 1776 ∗
      memRegion (fsp + 3152#64) 544 ∗
      memRegion (fsp + 3824#64) 8 ∗
      memRegion (fsp + 3856#64) 288 ⊢
    ∃∗ v976 : BitVec 64, ∃∗ v984 : BitVec 64, ∃∗ v992 : BitVec 64,
    ∃∗ vc90 : BitVec 64, ∃∗ vc98 : BitVec 64, ∃∗ c_ca0 : Words5,
    ∃∗ v4096 : BitVec 64, ∃∗ v4104 : BitVec 64, ∃∗ v4112 : BitVec 64,
      ((fsp + 976#64) ↦₆₄ v976) ∗
      ((fsp + 984#64) ↦₆₄ v984) ∗
      ((fsp + 992#64) ↦₆₄ v992) ∗
      memRegion (fsp + 1000#64) 392 ∗
      memRegion (fsp + 1872#64) 400 ∗
      ((fsp + 3216#64) ↦₆₄ vc90) ∗
      ((fsp + 3224#64) ↦₆₄ vc98) ∗
      wordsAt (fsp + 3232#64) c_ca0.toList ∗
      memRegion (fsp + 3272#64) 376 ∗
      ((fsp + 4096#64) ↦₆₄ v4096) ∗
      ((fsp + 4104#64) ↦₆₄ v4104) ∗
      ((fsp + 4112#64) ↦₆₄ v4112) ∗
      (memRegion (fsp + 1392#64) 480 ∗
        memRegion (fsp + 2272#64) 480 ∗
        memRegion (fsp + 3152#64) 64 ∗
        memRegion (fsp + 3648#64) 48 ∗
        memRegion (fsp + 3696#64) 128 ∗
        memRegion (fsp + 3824#64) 8 ∗
        memRegion (fsp + 3832#64) 24 ∗
        memRegion (fsp + 3856#64) 240 ∗
        memRegion (fsp + 4120#64) 24) := by
  refine Entails.trans (sepConj_mono_left (words16_entails_memRegion_128 (fsp + 3696#64) c_uc)) ?_
  rw [ProofLib.memRegion_split' (b := fsp + 976#64) (n := 8) (k := 1768) (b' := fsp + 984#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_eight (fsp + 976#64),
      ProofLib.memRegion_split' (b := fsp + 984#64) (n := 8) (k := 1760) (b' := fsp + 992#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_eight (fsp + 984#64),
      ProofLib.memRegion_split' (b := fsp + 992#64) (n := 8) (k := 1752) (b' := fsp + 1000#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_eight (fsp + 992#64),
      ProofLib.memRegion_split' (b := fsp + 1000#64) (n := 392) (k := 1360) (b' := fsp + 1392#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := fsp + 1392#64) (n := 480) (k := 880) (b' := fsp + 1872#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := fsp + 1872#64) (n := 400) (k := 480) (b' := fsp + 2272#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := fsp + 3152#64) (n := 64) (k := 480) (b' := fsp + 3216#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := fsp + 3216#64) (n := 8) (k := 472) (b' := fsp + 3224#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_eight (fsp + 3216#64),
      ProofLib.memRegion_split' (b := fsp + 3224#64) (n := 8) (k := 464) (b' := fsp + 3232#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_eight (fsp + 3224#64),
      ProofLib.memRegion_split' (b := fsp + 3232#64) (n := 40) (k := 424) (b' := fsp + 3272#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := fsp + 3272#64) (n := 376) (k := 48) (b' := fsp + 3648#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := fsp + 3856#64) (n := 240) (k := 48) (b' := fsp + 4096#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := fsp + 4096#64) (n := 8) (k := 40) (b' := fsp + 4104#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_eight (fsp + 4096#64),
      ProofLib.memRegion_split' (b := fsp + 4104#64) (n := 8) (k := 32) (b' := fsp + 4112#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_eight (fsp + 4104#64),
      ProofLib.memRegion_split' (b := fsp + 4112#64) (n := 8) (k := 24) (b' := fsp + 4120#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_eight (fsp + 4112#64)]
  refine Entails.trans (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
    (sepConj_mono (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
      (sepConj_mono_left (memRegion_40_entails_words5 (fsp + 3232#64)))))) (Entails.refl _))))) ?_
  simp only [sepExists_sepConj_left, sepExists_sepConj_right]
  apply Entails.sepExists_elim; intro v4112
  apply Entails.sepExists_elim; intro v4104
  apply Entails.sepExists_elim; intro v4096
  apply Entails.sepExists_elim; intro c_ca0
  apply Entails.sepExists_elim; intro vc98
  apply Entails.sepExists_elim; intro vc90
  apply Entails.sepExists_elim; intro v992
  apply Entails.sepExists_elim; intro v984
  apply Entails.sepExists_elim; intro v976
  refine Entails.sepExists_right v976 (Entails.sepExists_right v984
    (Entails.sepExists_right v992 (Entails.sepExists_right vc90
      (Entails.sepExists_right vc98 (Entails.sepExists_right c_ca0
        (Entails.sepExists_right v4096 (Entails.sepExists_right v4104
          (Entails.sepExists_right v4112 ?_))))))))
  exact Entails.of_eq (by ac_rfl)

theorem memRegion_none_no_ack_join (fsp : BitVec 64) :
    memRegion (fsp + 976#64) 376 ∗
      memRegion (fsp + 1352#64) 40 ∗
      memRegion (fsp + 2752#64) 400 ∗
      memRegion (fsp + 1872#64) 400 ∗
      memRegion (fsp + 3216#64) 16 ∗
      memRegion (fsp + 3232#64) 40 ∗
      memRegion (fsp + 3272#64) 376 ∗
      memRegion (fsp + 4096#64) 24 ∗
      (memRegion (fsp + 1392#64) 480 ∗
        memRegion (fsp + 2272#64) 480 ∗
        memRegion (fsp + 3152#64) 64 ∗
        memRegion (fsp + 3648#64) 48 ∗
        memRegion (fsp + 3696#64) 128 ∗
        memRegion (fsp + 3824#64) 8 ∗
        memRegion (fsp + 3832#64) 24 ∗
        memRegion (fsp + 3856#64) 240 ∗
        memRegion (fsp + 4120#64) 24) ⊢
    memRegion (fsp + 976#64) 3168 := by
  rw [ProofLib.memRegion_split' (b := fsp + 976#64) (n := 376) (k := 2792) (b' := fsp + 1352#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := fsp + 1352#64) (n := 40) (k := 2752) (b' := fsp + 1392#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := fsp + 1392#64) (n := 480) (k := 2272) (b' := fsp + 1872#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := fsp + 1872#64) (n := 400) (k := 1872) (b' := fsp + 2272#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := fsp + 2272#64) (n := 480) (k := 1392) (b' := fsp + 2752#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := fsp + 2752#64) (n := 400) (k := 992) (b' := fsp + 3152#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := fsp + 3152#64) (n := 64) (k := 928) (b' := fsp + 3216#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := fsp + 3216#64) (n := 16) (k := 912) (b' := fsp + 3232#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := fsp + 3232#64) (n := 40) (k := 872) (b' := fsp + 3272#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := fsp + 3272#64) (n := 376) (k := 496) (b' := fsp + 3648#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := fsp + 3648#64) (n := 48) (k := 448) (b' := fsp + 3696#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := fsp + 3696#64) (n := 128) (k := 320) (b' := fsp + 3824#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := fsp + 3824#64) (n := 8) (k := 312) (b' := fsp + 3832#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := fsp + 3832#64) (n := 24) (k := 288) (b' := fsp + 3856#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := fsp + 3856#64) (n := 240) (k := 48) (b' := fsp + 4096#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := fsp + 4096#64) (n := 24) (k := 24) (b' := fsp + 4120#64) rfl (by bv_omega) (by decide)]
  exact Entails.of_eq (by ac_rfl)

set_option maxHeartbeats 2000000 in
/-- Path 4a from `+11496 -> s0.x30` (`outMsg = none, ack = false`):
    returns `Ok { key := none, state := .ct1Sampled { st with receiving_ek := addChunkTotal st.receiving_ek chunk } }`. -/
theorem ct1Sampled_path_none_no_ack
    {b : BitVec 64} {A : RustAlloc} {F : ShaCompress}
    {ext : String → Option (State → State)}
    (hmemcpy : subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr memcpyName) sessionMemcpyRegionSpec)
    (s0 s_in : State) (fsp selfA outA : BitVec 64)
    (st : Chunked.SendCt.Ct1Sampled spqrPolyApi (spqrAuthApi F))
    (dec' : PolyDecoder) (c_uc : Words16) (sc : CopyScratchStack) (k : EpilogueStoreStack)
    (Rest : SepProp)
    (hfsp_align : (fsp &&& 15#64 == 0#64) = true)
    (hsp0_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hfsp : fsp = s0.sp - 4240#64)
    (hpc : s_in.pc = (tripleRatchetProgAtExt b ext).fnAddr statesRecvName + 11496#64)
    (hrun : s_in.status = .Running)
    (hsp : s_in.sp = fsp)
    (hx19 : s_in.readReg64 .x19 = outA)
    (hx22 : s_in.readReg64 .x22 = 0#64)
    (hx23 : s_in.readReg64 .x23 = polyEncoderTagVal st.sending_ct1)
    (hx29 : s_in.readReg64 .x29 = fsp + 4144#64)
    (htr : TraceCalleeSaved s_in s0) :
    SepWP (tripleRatchetProgAtExt b ext) (s0.readReg64 .x30) s_in
      (optVecU8At A (fsp + 3832#64) none ∗
        polyDecoderAt A (fsp + 2752#64) dec' ∗
        polyEncoderAt A selfA st.sending_ct1 ∗
        wordsAt (selfA + 400#64) c_uc.toList ∗
        wordsAt (fsp + 3696#64) c_uc.toList ∗
        relocatedHeap (fun a => unchunkedCt1SentAt A a st.uc) (wordsBytes c_uc.toList) ∗
        memRegion (selfA + 528#64) 400 ∗
        copyScratchStackAt fsp sc ∗
        epilogueStoreStackPart1At fsp k ∗
        ((fsp + 232#64) ↦₆₄ selfA) ∗
        ((fsp + 512#64) ↦₆₄ k.w200) ∗
        ((fsp + 520#64) ↦₆₄ k.w208) ∗
        wordsAt (fsp + 528#64) k.tail.toList ∗
        memRegion (fsp + 576#64) 376 ∗
        memRegion (fsp + 568#64) 8 ∗
        memRegion (fsp + 952#64) 8 ∗
        memRegion (fsp + 976#64) 1776 ∗
        memRegion (fsp + 3152#64) 544 ∗
        memRegion (fsp + 3824#64) 8 ∗
        memRegion (fsp + 3856#64) 288 ∗
        memRegion outA v1RecvSize ∗
        stackAt fsp statesRecvCalleeStackX ∗
        statesRecvSavedCells s0 ∗
        Rest)
      (fun sf Pf =>
        (Pf ⊢
          resultV1RecvAt A (F := F) outA (.ok { key := none, state := .ct1Sampled { st with receiving_ek := dec' } }) ∗
          memRegion selfA chunkedStatesSize ∗
          stackAt s0.sp statesRecvStackX ∗
          Rest) ∧
        sf.sp = s0.sp ∧
        CalleeSavedPreserved s0 sf ∧
        sf.trace = s0.trace) := by
  refine SepWP.seq
    (ct1Sampled_recv_ek_decode_branch_none s_in fsp _ hfsp_align hpc hrun hsp) ?_
  intro s1 P1 hpc1 hrun1 ⟨hP1, hsp1, hx19_1, _, _, hx22_1, hx23_1, _, _, hx29_1, htr1⟩
  refine SepWP.weaken_pre hP1 ?_
  refine SepWP.seq
    (ct1Sampled_none_branch_no_ack s1 _ hpc1 hrun1 (hx22_1.trans hx22)) ?_
  intro s2 P2 hpc2 hrun2 ⟨hP2, hs2⟩
  refine SepWP.weaken_pre hP2 ?_
  have hsp2 : s2.sp = fsp := by rw [hs2]; exact hsp1
  have hx19_2 : s2.readReg64 .x19 = outA := by rw [hs2, State.readReg64_setPC, hx19_1, hx19]
  have hx23_2 : s2.readReg64 .x23 = polyEncoderTagVal st.sending_ct1 := by
    rw [hs2, State.readReg64_setPC, hx23_1, hx23]
  have hx29_2 : s2.readReg64 .x29 = fsp + 4144#64 := by rw [hs2, State.readReg64_setPC, hx29_1, hx29]
  have htr2 : TraceCalleeSaved s2 s0 := by rw [hs2]; exact htr1.trans htr
  have hpre2 :
      memRegion (fsp + 3832#64) 24 ∗ polyDecoderAt A (fsp + 2752#64) dec' ∗
        polyEncoderAt A selfA st.sending_ct1 ∗ wordsAt (selfA + 400#64) c_uc.toList ∗
        wordsAt (fsp + 3696#64) c_uc.toList ∗
        relocatedHeap (fun a => unchunkedCt1SentAt A a st.uc) (wordsBytes c_uc.toList) ∗
        memRegion (selfA + 528#64) 400 ∗ copyScratchStackAt fsp sc ∗
        epilogueStoreStackPart1At fsp k ∗ ((fsp + 232#64) ↦₆₄ selfA) ∗
        ((fsp + 512#64) ↦₆₄ k.w200) ∗ ((fsp + 520#64) ↦₆₄ k.w208) ∗
        wordsAt (fsp + 528#64) k.tail.toList ∗ memRegion (fsp + 576#64) 376 ∗
        memRegion (fsp + 568#64) 8 ∗ memRegion (fsp + 952#64) 8 ∗
        memRegion (fsp + 976#64) 1776 ∗ memRegion (fsp + 3152#64) 544 ∗
        memRegion (fsp + 3824#64) 8 ∗ memRegion (fsp + 3856#64) 288 ∗
        memRegion outA v1RecvSize ∗ stackAt fsp statesRecvCalleeStackX ∗
        statesRecvSavedCells s0 ∗ Rest ⊢
      ∃∗ c_enc : Words50, ∃∗ d400 : Split400,
      ∃∗ v976 : BitVec 64, ∃∗ v984 : BitVec 64, ∃∗ v992 : BitVec 64,
      ∃∗ vc90 : BitVec 64, ∃∗ vc98 : BitVec 64, ∃∗ c_ca0 : Words5,
      ∃∗ v4096 : BitVec 64, ∃∗ v4104 : BitVec 64, ∃∗ v4112 : BitVec 64,
        ⌜c_enc.c0.w0 = polyEncoderTagVal st.sending_ct1⌝ ∗ ⌜d400.mid352.length = 352⌝ ∗
        wordsAt selfA c_enc.c0.toList ∗ wordsAt (selfA + 128#64) c_enc.c1.toList ∗
        wordsAt (selfA + 256#64) c_enc.c2.toList ∗
        wordsAt (selfA + 384#64) (mkC3FromEnc2Uc14 c_enc.w48 c_enc.w49 c_uc).toList ∗
        ((selfA + 512#64) ↦₆₄ c_uc.w14) ∗ ((selfA + 520#64) ↦₆₄ c_uc.w15) ∗
        ((fsp + 232#64) ↦₆₄ selfA) ∗ split400At (fsp + 2752#64) d400 ∗
        memRegion (fsp + 1872#64) 400 ∗ copyScratchStackAt fsp sc ∗
        epilogueStoreStackPart1At fsp k ∗ ((fsp + 976#64) ↦₆₄ v976) ∗
        ((fsp + 984#64) ↦₆₄ v984) ∗ ((fsp + 992#64) ↦₆₄ v992) ∗
        memRegion (fsp + 1000#64) 392 ∗ ((fsp + 3216#64) ↦₆₄ vc90) ∗
        ((fsp + 3224#64) ↦₆₄ vc98) ∗ ((fsp + 4096#64) ↦₆₄ v4096) ∗
        ((fsp + 4104#64) ↦₆₄ v4104) ∗ ((fsp + 4112#64) ↦₆₄ v4112) ∗
        (wordsAt (fsp + 3232#64) c_ca0.toList ∗ memRegion (fsp + 3272#64) 376 ∗
          ((fsp + 512#64) ↦₆₄ k.w200) ∗ ((fsp + 520#64) ↦₆₄ k.w208) ∗
          wordsAt (fsp + 528#64) k.tail.toList ∗ memRegion (fsp + 576#64) 376 ∗
          (relocatedHeap (fun b => polyEncoderBodyAt A b st.sending_ct1) c_enc.tailBytes ∗
            relocatedHeap (fun a => unchunkedCt1SentAt A a st.uc) (wordsBytes c_uc.toList) ∗
            relocatedHeap (fun a => polyDecoderAt A a dec') d400.toBytes ∗
            memRegion (selfA + 528#64) 400 ∗ memRegion (fsp + 568#64) 8 ∗
            memRegion (fsp + 952#64) 8 ∗
            (memRegion (fsp + 1392#64) 480 ∗ memRegion (fsp + 2272#64) 480 ∗
              memRegion (fsp + 3152#64) 64 ∗ memRegion (fsp + 3648#64) 48 ∗
              memRegion (fsp + 3696#64) 128 ∗ memRegion (fsp + 3824#64) 8 ∗
              memRegion (fsp + 3832#64) 24 ∗ memRegion (fsp + 3856#64) 240 ∗
              memRegion (fsp + 4120#64) 24) ∗
            memRegion outA v1RecvSize ∗ stackAt fsp statesRecvCalleeStackX ∗
            statesRecvSavedCells s0 ∗ Rest)) := by
    refine Entails.trans (Entails.of_eq (show _ =
        polyEncoderAt A selfA st.sending_ct1 ∗ polyDecoderAt A (fsp + 2752#64) dec' ∗
          (wordsAt (fsp + 3696#64) c_uc.toList ∗ memRegion (fsp + 3832#64) 24 ∗
            memRegion (fsp + 976#64) 1776 ∗ memRegion (fsp + 3152#64) 544 ∗
            memRegion (fsp + 3824#64) 8 ∗ memRegion (fsp + 3856#64) 288) ∗
          (wordsAt (selfA + 400#64) c_uc.toList ∗
            relocatedHeap (fun a => unchunkedCt1SentAt A a st.uc) (wordsBytes c_uc.toList) ∗
            memRegion (selfA + 528#64) 400 ∗ copyScratchStackAt fsp sc ∗
            epilogueStoreStackPart1At fsp k ∗ ((fsp + 232#64) ↦₆₄ selfA) ∗
            ((fsp + 512#64) ↦₆₄ k.w200) ∗ ((fsp + 520#64) ↦₆₄ k.w208) ∗
            wordsAt (fsp + 528#64) k.tail.toList ∗ memRegion (fsp + 576#64) 376 ∗
            memRegion (fsp + 568#64) 8 ∗ memRegion (fsp + 952#64) 8 ∗
            memRegion outA v1RecvSize ∗ stackAt fsp statesRecvCalleeStackX ∗
            statesRecvSavedCells s0 ∗ Rest) by ac_rfl)) ?_
    refine Entails.trans (sepConj_mono (polyEncoderAt_extract_words50 A selfA st.sending_ct1)
      (sepConj_mono (Relocatable.extract_split400 (Relocatable.of_polyDecoderAt A dec') (fsp + 2752#64))
        (sepConj_mono_left (memRegion_none_no_ack_split fsp c_uc)))) ?_
    simp only [sepExists_sepConj_left, sepExists_sepConj_right]
    apply Entails.sepExists_elim; intro v976; apply Entails.sepExists_elim; intro v984
    apply Entails.sepExists_elim; intro v992; apply Entails.sepExists_elim; intro vc90
    apply Entails.sepExists_elim; intro vc98; apply Entails.sepExists_elim; intro c_ca0
    apply Entails.sepExists_elim; intro v4096; apply Entails.sepExists_elim; intro v4104
    apply Entails.sepExists_elim; intro v4112; apply Entails.sepExists_elim; intro d400
    apply Entails.sepExists_elim; intro c_enc
    refine Entails.sepExists_right c_enc (Entails.sepExists_right d400
      (Entails.sepExists_right v976 (Entails.sepExists_right v984
        (Entails.sepExists_right v992 (Entails.sepExists_right vc90
          (Entails.sepExists_right vc98 (Entails.sepExists_right c_ca0
            (Entails.sepExists_right v4096 (Entails.sepExists_right v4104
              (Entails.sepExists_right v4112 ?_))))))))))
    dsimp only [words50At, mkC3FromEnc2Uc14, Words16.toList]
    simp only [wordsAt_16, BitVec.add_assoc, BitVec.reduceAdd]
    exact Entails.of_eq (by ac_rfl)
  refine SepWP.weaken_pre hpre2 ?_
  apply ProofLib.SepWP.exists_left; intro c_enc; apply ProofLib.SepWP.exists_left; intro d400
  apply ProofLib.SepWP.exists_left; intro v976; apply ProofLib.SepWP.exists_left; intro v984
  apply ProofLib.SepWP.exists_left; intro v992; apply ProofLib.SepWP.exists_left; intro vc90
  apply ProofLib.SepWP.exists_left; intro vc98; apply ProofLib.SepWP.exists_left; intro c_ca0
  apply ProofLib.SepWP.exists_left; intro v4096; apply ProofLib.SepWP.exists_left; intro v4104
  apply ProofLib.SepWP.exists_left; intro v4112
  wp_focus_pure; intro htag_enc
  wp_focus_pure; intro hmid352
  refine SepWP.seq
    (ct1Sampled_copy_none_no_ack_part1 hmemcpy s2 fsp selfA
      c_enc.c0 c_enc.c1 c_enc.c2 (mkC3FromEnc2Uc14 c_enc.w48 c_enc.w49 c_uc)
      c_uc.w14 c_uc.w15 d400 sc k v976 v984 v992 vc90 vc98 v4096 v4104 v4112 _
      hmid352 hfsp_align hpc2 hrun2 hsp2 hx29_2) ?_
  intro s3 P3 hpc3 hrun3 ⟨hP3, hsp3, hx19_3, hx23_3, hx29_3, htr3⟩
  let d := mkSplit928From528And400 c_enc.c0 c_enc.c1 c_enc.c2
    (mkC3FromEnc2Uc14 c_enc.w48 c_enc.w49 c_uc) c_uc.w14 c_uc.w15 d400
  have hP3' : P3 ⊢
      copyScratchStackAt fsp (copyFullScratch sc d) ∗
      epilogueStoreStackPart1At fsp
        { (epilogueStackOfSplit928 d selfA k.w200 k.w208) with
          we0 := k.we0, w3c0 := k.w3c0, w3c8 := k.w3c8 } ∗
      ((fsp + 232#64) ↦₆₄ selfA) ∗ ((fsp + 512#64) ↦₆₄ k.w200) ∗ ((fsp + 520#64) ↦₆₄ k.w208) ∗
      wordsAt (fsp + 528#64) k.tail.toList ∗ memRegion (fsp + 576#64) 376 ∗
      mid376At (fsp + 976#64) c_uc.w14 c_uc.w15 d400.w0 d400.mid352 ∗
      wordsAt (fsp + 1352#64) d400.tail.toList ∗
      ((fsp + 3216#64) ↦₆₄ (mkC3FromEnc2Uc14 c_enc.w48 c_enc.w49 c_uc).w13) ∗
      ((fsp + 3224#64) ↦₆₄ (mkC3FromEnc2Uc14 c_enc.w48 c_enc.w49 c_uc).w14) ∗
      wordsAt (fsp + 3232#64) c_ca0.toList ∗ memRegion (fsp + 3272#64) 376 ∗
      (wordsAt selfA c_enc.c0.toList ∗ wordsAt (selfA + 128#64) c_enc.c1.toList ∗
        wordsAt (selfA + 256#64) c_enc.c2.toList ∗
        wordsAt (selfA + 384#64) (mkC3FromEnc2Uc14 c_enc.w48 c_enc.w49 c_uc).toList ∗
        ((selfA + 512#64) ↦₆₄ c_uc.w14) ∗ ((selfA + 520#64) ↦₆₄ c_uc.w15) ∗
        memRegion (selfA + 528#64) 400 ∗ memRegion (fsp + 2752#64) 400 ∗
        memRegion (fsp + 1872#64) 400 ∗ memRegion (fsp + 4096#64) 24 ∗
        relocatedHeap (fun b => polyEncoderBodyAt A b st.sending_ct1) c_enc.tailBytes ∗
        relocatedHeap (fun a => unchunkedCt1SentAt A a st.uc) (wordsBytes c_uc.toList) ∗
        relocatedHeap (fun a => polyDecoderAt A a dec') d400.toBytes ∗
        memRegion (fsp + 568#64) 8 ∗ memRegion (fsp + 952#64) 8 ∗
        (memRegion (fsp + 1392#64) 480 ∗ memRegion (fsp + 2272#64) 480 ∗
          memRegion (fsp + 3152#64) 64 ∗ memRegion (fsp + 3648#64) 48 ∗
          memRegion (fsp + 3696#64) 128 ∗ memRegion (fsp + 3824#64) 8 ∗
          memRegion (fsp + 3832#64) 24 ∗ memRegion (fsp + 3856#64) 240 ∗
          memRegion (fsp + 4120#64) 24) ∗
        memRegion outA v1RecvSize ∗ stackAt fsp statesRecvCalleeStackX ∗
        statesRecvSavedCells s0 ∗ Rest) := Entails.trans hP3 (Entails.of_eq (by ac_rfl))
  refine SepWP.weaken_pre hP3' ?_
  have htag_01 : c_enc.c0.w0 = 0#64 ∨ c_enc.c0.w0 = 1#64 := by
    rw [htag_enc]; exact polyEncoderTagVal_zero_or_one st.sending_ct1
  refine SepWP.seq
    (ct1Sampled_copy_none_no_ack_part2 hmemcpy s3 fsp selfA outA
      c_enc.c0 c_enc.c1 c_enc.c2 (mkC3FromEnc2Uc14 c_enc.w48 c_enc.w49 c_uc)
      c_uc.w14 c_uc.w15 d400 sc k c_ca0 _
      htag_01 hmid352 hfsp_align hpc3 hrun3 hsp3
      (hx19_3.trans hx19_2) (hx23_3.trans (hx23_2.trans htag_enc.symm))) ?_
  intro s4 P4 hpc4 hrun4 ⟨hP4, hregs4, hsp4, hx19_4, _, htr4⟩
  let k' := epilogueStackOfSplit928 d noneCap k.w200 k.w208
  have hmid' : k'.mid.length = 376 := by
    dsimp only [k', epilogueStackOfSplit928, d, mkSplit928From528And400]
    exact mid376Bytes_length c_uc.w14 c_uc.w15 d400.w0 hmid352
  have hP4' : P4 ⊢
      epilogueStoreStackPart1At fsp k' ∗ epilogueStoreStackPart2At fsp k' ∗
      memRegion outA chunkedStatesSize ∗ memRegion (outA + 928#64) 32 ∗
      (copyScratchStackAt fsp (copyFullScratch sc d) ∗
        memRegion (fsp + 568#64) 8 ∗ memRegion (fsp + 952#64) 8 ∗
        memRegion (fsp + 976#64) 3168 ∗ memRegion selfA chunkedStatesSize ∗
        relocatedHeap (fun b => polyEncoderBodyAt A b st.sending_ct1) c_enc.tailBytes ∗
        relocatedHeap (fun a => unchunkedCt1SentAt A a st.uc) (wordsBytes c_uc.toList) ∗
        relocatedHeap (fun a => polyDecoderAt A a dec') d400.toBytes ∗
        stackAt fsp statesRecvCalleeStackX ∗ statesRecvSavedCells s0 ∗ Rest) := by
    refine Entails.trans hP4 ?_
    simp only [memRegion_out_960_split_states_key]
    have hself := chunks528_and_400_entails_memRegion_928 selfA
      c_enc.c0 c_enc.c1 c_enc.c2 (mkC3FromEnc2Uc14 c_enc.w48 c_enc.w49 c_uc) c_uc.w14 c_uc.w15
    have hstk3168 := memRegion_none_no_ack_join fsp
    refine Entails.trans (Entails.of_eq (show _ =
      epilogueStoreStackPart1At fsp k' ∗ epilogueStoreStackPart2At fsp k' ∗
      memRegion outA chunkedStatesSize ∗ memRegion (outA + 928#64) 32 ∗
      (copyScratchStackAt fsp (copyFullScratch sc d) ∗
        memRegion (fsp + 568#64) 8 ∗ memRegion (fsp + 952#64) 8 ∗
        (memRegion (fsp + 976#64) 376 ∗ memRegion (fsp + 1352#64) 40 ∗
          memRegion (fsp + 2752#64) 400 ∗ memRegion (fsp + 1872#64) 400 ∗
          memRegion (fsp + 3216#64) 16 ∗ memRegion (fsp + 3232#64) 40 ∗
          memRegion (fsp + 3272#64) 376 ∗ memRegion (fsp + 4096#64) 24 ∗
          (memRegion (fsp + 1392#64) 480 ∗ memRegion (fsp + 2272#64) 480 ∗
            memRegion (fsp + 3152#64) 64 ∗ memRegion (fsp + 3648#64) 48 ∗
            memRegion (fsp + 3696#64) 128 ∗ memRegion (fsp + 3824#64) 8 ∗
            memRegion (fsp + 3832#64) 24 ∗ memRegion (fsp + 3856#64) 240 ∗
            memRegion (fsp + 4120#64) 24)) ∗
        (wordsAt selfA c_enc.c0.toList ∗ wordsAt (selfA + 128#64) c_enc.c1.toList ∗
          wordsAt (selfA + 256#64) c_enc.c2.toList ∗
          wordsAt (selfA + 384#64) (mkC3FromEnc2Uc14 c_enc.w48 c_enc.w49 c_uc).toList ∗
          ((selfA + 512#64) ↦₆₄ c_uc.w14) ∗ ((selfA + 520#64) ↦₆₄ c_uc.w15) ∗
          memRegion (selfA + 528#64) 400) ∗
        relocatedHeap (fun b => polyEncoderBodyAt A b st.sending_ct1) c_enc.tailBytes ∗
        relocatedHeap (fun a => unchunkedCt1SentAt A a st.uc) (wordsBytes c_uc.toList) ∗
        relocatedHeap (fun a => polyDecoderAt A a dec') d400.toBytes ∗
        stackAt fsp statesRecvCalleeStackX ∗ statesRecvSavedCells s0 ∗ Rest) by ac_rfl)) ?_
    exact sepConj_mono_right (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
      (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
        (sepConj_mono hstk3168 (sepConj_mono_left hself))))))))
  refine SepWP.weaken_pre hP4' ?_
  refine SepWP.seq
    (ct1Sampled_epilogue_store hmemcpy s4 fsp outA k' _ hmid' hfsp_align hpc4 hrun4 hsp4 hx19_4) ?_
  intro s5 P5 hpc5 hrun5 ⟨hP5, hsp5, htr5⟩
  have heq_split : epilogueSplit928 s4 k' = d :=
    epilogueSplit928_of_eq s4 d noneCap k.w200 k.w208 hregs4
  have hP5' : P5 ⊢
      stackAt fsp statesRecvCalleeStackX ∗ memRegion fsp 4144 ∗ statesRecvSavedCells s0 ∗
      (resultV1RecvAt A (F := F) outA (.ok { key := none, state := .ct1Sampled { st with receiving_ek := dec' } }) ∗
        memRegion selfA chunkedStatesSize ∗ Rest) := by
    refine Entails.trans hP5 ?_
    simp only [heq_split]
    have hstk := copyScratch_and_epilogueStack_entails_memRegion_4144 fsp (copyFullScratch sc d) k' hmid'
    have hst_out := split928At_reconstruct_ct1Sampled_updated (A := A) outA st dec' c_enc c_uc d400 htag_enc hmid352
    have hkey := optEpochSecretAt_none_of_words4 A (outA + 928#64) (s4.readReg64 .x20) k.w200 k.w208
    dsimp only [resultV1RecvAt, v1RecvAt, k', epilogueStackOfSplit928] at hstk hkey ⊢
    simp only [BitVec.add_assoc, BitVec.reduceAdd] at hkey
    refine Entails.trans (Entails.of_eq (show _ =
      stackAt fsp statesRecvCalleeStackX ∗
      (copyScratchStackAt fsp (copyFullScratch sc d) ∗
        epilogueStoreStackPart1At fsp (epilogueStackOfSplit928 d noneCap k.w200 k.w208) ∗
        epilogueStoreStackPart2At fsp (epilogueStackOfSplit928 d noneCap k.w200 k.w208) ∗
        memRegion (fsp + 568#64) 8 ∗ memRegion (fsp + 952#64) 8 ∗ memRegion (fsp + 976#64) 3168) ∗
      statesRecvSavedCells s0 ∗
      (((split928At outA d ∗
          relocatedHeap (fun b => polyEncoderBodyAt A b st.sending_ct1) c_enc.tailBytes ∗
          relocatedHeap (fun a => unchunkedCt1SentAt A a st.uc) (wordsBytes c_uc.toList) ∗
          relocatedHeap (fun a => polyDecoderAt A a dec') d400.toBytes) ∗
        (((outA + 928#64) ↦₆₄ noneCap) ∗ ((outA + 936#64) ↦₆₄ s4.readReg64 .x20) ∗
          ((outA + 944#64) ↦₆₄ k.w200) ∗ ((outA + 952#64) ↦₆₄ k.w208))) ∗
        memRegion selfA chunkedStatesSize ∗ Rest) by ac_rfl)) ?_
    exact sepConj_mono_right (sepConj_mono hstk
      (sepConj_mono_right (sepConj_mono_left (sepConj_mono hst_out hkey))))
  subst hfsp
  refine SepWP.weaken_pre hP5' ?_
  refine SepWP.mono
    (ct1Sampled_epilogue_19324 s0 s5 _ hsp0_align hpc5 hrun5 hsp5 (htr5.trans (htr4.trans (htr3.trans htr2)))) ?_
  intro sf Pf _ _ ⟨hPf, hsp_f, hcs_f, htr_f⟩
  exact ⟨Entails.trans hPf (Entails.of_eq (by ac_rfl)), hsp_f, hcs_f, htr_f⟩

end CryptoVerification.SpqrV1.States.Recv

