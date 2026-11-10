/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SpqrV1Sync.SendTotal.SizeDefs
public import LibsignalBinary.Specifications.LibsignalSpqrV1.Auth
public import LibsignalBinary.Specifications.LibsignalSpqrV1.GF16
public import LibsignalBinary.Specifications.LibsignalSpqrV1.Proto
public import LibsignalBinary.Specifications.LibsignalTripleRatchet
public import ProofLib

set_option autoImplicit false

/-!
# Serialized Braid State Size Bound

Bounds `rawV1State st.into_pb ≤ 2 ^ 40` on any `BOk` braid state (`st_bSize`), using `EncWF`
message lengths (`≤ 1152`) and strictly `x`-sorted `GF16` point sets (`≤ 2 ^ 16` points per
polynomial).
-/

@[expose] public section

namespace CryptoVerification.SpqrV1Sync.SendTotal

open CryptoVerification.LibsignalSpqrV1
open CryptoGames.LibsignalSession (ShaCompress)
open CryptoVerification.SpqrV1Sync.InSync
open CryptoVerification.SpqrV1Sync.Braid
open CryptoVerification.SpqrV1.Top.StateSize (
  optRaw rawAuth rawPolyEnc rawPolyDec
  rawUcKeysUnsampled rawUcHeaderSent rawUcEkSent rawUcEkSentCt1Received
  rawUcNoHeaderReceived rawUcHeaderReceived rawUcCt1Sent rawUcCt1SentEkReceived rawUcCt2Sent
  rawChKeysUnsampled rawChKeysSampled rawChHeaderSent rawChCt1Received rawChEkSentCt1Received
  rawChNoHeaderReceived rawChHeaderReceived rawChCt1Sampled rawChEkReceivedCt1Sampled
  rawChCt1Acknowledged rawChCt2Sampled rawInnerState rawV1State)

private theorem bsz_sum_map_le {α : Type} (xs : List α) (f : α → Nat) (c : Nat)
    (h : ∀ x ∈ xs, f x ≤ c) : (xs.map f).sum ≤ xs.length * c := by
  induction xs with
  | nil => simp
  | cons x xs ih =>
    simp only [List.map_cons, List.sum_cons, List.length_cons]
    have hx := h x List.mem_cons_self
    have hxs := ih (fun y hy => h y (List.mem_cons_of_mem x hy))
    calc f x + (xs.map f).sum ≤ c + xs.length * c := Nat.add_le_add hx hxs
      _ = (xs.length + 1) * c := by rw [Nat.succ_mul, Nat.add_comm]

private theorem bsz_length_flatMap_const {α β : Type} (xs : List α) (f : α → List β) (k : Nat)
    (hf : ∀ x, (f x).length = k) : (xs.flatMap f).length = k * xs.length := by
  induction xs with
  | nil => simp
  | cons x xs ih =>
    simp only [List.flatMap_cons, List.length_append, hf x, ih, List.length_cons]
    rw [Nat.mul_add, Nat.mul_one, Nat.add_comm]

private theorem bsz_needed_le (len j : Nat) : Erasure.needed len j ≤ len + 1 := by
  unfold Erasure.needed
  split <;> omega

private theorem bsz_rawAuth_eq (F : ShaCompress) {a : Authenticator} (ha : AuthOk a) :
    rawAuth ((spqrAuthApi F).into_pb a) = 64 := by
  rcases ha with ⟨hr, hm⟩
  simp [spqrAuthApi, Authenticator.intoPb, rawAuth, hr, hm]

private theorem bsz_rawPolyEnc_le {len : Nat} {e : PolyEncoder} (he : EncWF len e) :
    rawPolyEnc (spqrPolyApi.encoder_into_pb e) ≤ 16 * (2 * len + 24) := by
  rcases he with ⟨msg, hinv, rfl⟩
  rcases hinv with hpts | ⟨polys, hpolys, hlen16, hcoeff⟩
  · simp only [spqrPolyApi, protoPolyEncoderToPb, PolyEncoder.intoPb, hpts, rawPolyEnc,
      List.map_nil, List.sum_nil, Nat.add_zero, List.map_map]
    have hmp_len : (Erasure.msgPoints msg).length = 16 := by simp [Erasure.msgPoints]
    rw [← hmp_len]
    apply bsz_sum_map_le
    intro pt hpt
    simp only [Erasure.msgPoints, List.mem_map, List.mem_range] at hpt
    rcases hpt with ⟨j, _, rfl⟩
    simp only [Function.comp_apply]
    rw [bsz_length_flatMap_const _ _ 2 (fun _ => rfl)]
    simp only [List.length_map, List.length_range]
    have hneed := bsz_needed_le msg.length j
    omega
  · simp only [spqrPolyApi, protoPolyEncoderToPb, PolyEncoder.intoPb, hpolys, rawPolyEnc,
      List.map_nil, List.sum_nil, Nat.zero_add, List.map_map]
    rw [← hlen16]
    apply bsz_sum_map_le
    intro p hp
    obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem hp
    simp only [Function.comp_apply, Poly.serialize]
    rw [bsz_length_flatMap_const _ _ 2 (fun _ => rfl), (hcoeff j hj).1]
    have hneed := bsz_needed_le msg.length j
    omega

private theorem bsz_pairwise_lt_length_le :
    ∀ (xs : List Nat) (lo hi : Nat),
      xs.Pairwise (· < ·) →
      (∀ x ∈ xs, lo ≤ x ∧ x < hi) →
      xs.length ≤ hi - lo
  | [], _, _, _, _ => Nat.zero_le _
  | x :: ys, lo, hi, hp, hbd => by
    rw [List.pairwise_cons] at hp
    have hx := hbd x List.mem_cons_self
    have ih := bsz_pairwise_lt_length_le ys (x + 1) hi hp.2 fun y hy =>
      ⟨hp.1 y hy, (hbd y (List.mem_cons_of_mem x hy)).2⟩
    simp only [List.length_cons]
    omega

private theorem bsz_sortedSetPt_length_le (s : SortedSetPt)
    (h : (s.vec.map fun pt => pt.x.value.toNat).Pairwise (· < ·)) :
    s.vec.length ≤ 65536 := by
  have hlen : (s.vec.map fun pt => pt.x.value.toNat).length ≤ 65536 - 0 := by
    apply bsz_pairwise_lt_length_le _ 0 65536 h
    intro m hm
    rcases List.mem_map.mp hm with ⟨pt, _, rfl⟩
    exact ⟨Nat.zero_le _, pt.x.value.isLt⟩
  simpa using hlen

private theorem bsz_rawPolyDec_le {n : Nat} {d : PolyDecoder} (hd : DecWF n d) :
    rawPolyDec (spqrPolyApi.decoder_into_pb d) ≤ 16 * (4 * 65536 + 22) := by
  rcases hd with ⟨_, hlen16, hsort⟩
  simp only [spqrPolyApi, protoPolyDecoderToPb, PolyDecoder.intoPb, rawPolyDec, List.map_map]
  rw [← hlen16]
  apply bsz_sum_map_le
  intro s hs
  obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem hs
  simp only [Function.comp_apply]
  rw [bsz_length_flatMap_const _ Pt.serialize 4 (fun _ => rfl)]
  have hvec := bsz_sortedSetPt_length_le d.pts[j] (hsort j hj)
  omega

/-- Every `BOk` braid state serializes to `rawV1State st.into_pb ≤ 2 ^ 40`. -/
theorem st_bSize (F : ShaCompress) : BSizeStmt F := by
  intro st hbok
  cases st with
  | keysUnsampled s =>
    have ha := bsz_rawAuth_eq F hbok
    simp only [States.into_pb, Chunked.SendEk.KeysUnsampled.into_pb,
      Unchunked.SendEk.KeysUnsampled.into_pb, rawV1State, rawInnerState,
      rawChKeysUnsampled, rawUcKeysUnsampled, optRaw, ha]
    omega
  | keysSampled s =>
    rcases hbok with ⟨ha0, ⟨hdk, hek⟩, henc⟩
    have ha := bsz_rawAuth_eq F ha0
    have he := bsz_rawPolyEnc_le henc
    simp only [States.into_pb, Chunked.SendEk.KeysSampled.into_pb,
      Unchunked.SendEk.HeaderSent.into_pb, rawV1State, rawInnerState,
      rawChKeysSampled, rawUcHeaderSent, optRaw, ha, hdk, hek,
      DECAPSULATION_KEY_SIZE, ENCAPSULATION_KEY_SIZE]
    omega
  | headerSent s =>
    rcases hbok with ⟨ha0, hdk, henc, hdec⟩
    have ha := bsz_rawAuth_eq F ha0
    have he := bsz_rawPolyEnc_le henc
    have hd := bsz_rawPolyDec_le hdec
    have hdk' : s.uc.dk.length = DECAPSULATION_KEY_SIZE := hdk
    simp only [States.into_pb, Chunked.SendEk.HeaderSent.into_pb,
      Unchunked.SendEk.EkSent.into_pb, rawV1State, rawInnerState,
      rawChHeaderSent, rawUcEkSent, optRaw, ha, hdk', DECAPSULATION_KEY_SIZE]
    omega
  | ct1Received s =>
    rcases hbok with ⟨ha0, ⟨hdk, hct1⟩, henc⟩
    have ha := bsz_rawAuth_eq F ha0
    have he := bsz_rawPolyEnc_le henc
    simp only [States.into_pb, Chunked.SendEk.Ct1Received.into_pb,
      Unchunked.SendEk.EkSentCt1Received.into_pb, rawV1State, rawInnerState,
      rawChCt1Received, rawUcEkSentCt1Received, optRaw, ha, hdk, hct1,
      DECAPSULATION_KEY_SIZE, CIPHERTEXT1_SIZE]
    omega
  | ekSentCt1Received s =>
    rcases hbok with ⟨ha0, ⟨hdk, hct1⟩, hdec⟩
    have ha := bsz_rawAuth_eq F ha0
    have hd := bsz_rawPolyDec_le hdec
    simp only [States.into_pb, Chunked.SendEk.EkSentCt1Received.into_pb,
      Unchunked.SendEk.EkSentCt1Received.into_pb, rawV1State, rawInnerState,
      rawChEkSentCt1Received, rawUcEkSentCt1Received, optRaw, ha, hdk, hct1,
      DECAPSULATION_KEY_SIZE, CIPHERTEXT1_SIZE]
    omega
  | noHeaderReceived s =>
    rcases hbok with ⟨ha0, hdec⟩
    have ha := bsz_rawAuth_eq F ha0
    have hd := bsz_rawPolyDec_le hdec
    simp only [States.into_pb, Chunked.SendCt.NoHeaderReceived.into_pb,
      Unchunked.SendCt.NoHeaderReceived.into_pb, rawV1State, rawInnerState,
      rawChNoHeaderReceived, rawUcNoHeaderReceived, optRaw, ha]
    omega
  | headerReceived s =>
    rcases hbok with ⟨ha0, hhdr, hdec⟩
    have ha := bsz_rawAuth_eq F ha0
    have hd := bsz_rawPolyDec_le hdec
    have hhdr' : s.uc.hdr.length = HEADER_SIZE := hhdr
    simp only [States.into_pb, Chunked.SendCt.HeaderReceived.into_pb,
      Unchunked.SendCt.HeaderReceived.into_pb, rawV1State, rawInnerState,
      rawChHeaderReceived, rawUcHeaderReceived, optRaw, ha, hhdr', HEADER_SIZE]
    omega
  | ct1Sampled s =>
    rcases hbok with ⟨ha0, ⟨hhdr, hes, hct1⟩, henc, hdec⟩
    have ha := bsz_rawAuth_eq F ha0
    have he := bsz_rawPolyEnc_le henc
    have hd := bsz_rawPolyDec_le hdec
    simp only [States.into_pb, Chunked.SendCt.Ct1Sampled.into_pb,
      Unchunked.SendCt.Ct1Sent.into_pb, rawV1State, rawInnerState,
      rawChCt1Sampled, rawUcCt1Sent, optRaw, ha, hhdr, hes, hct1,
      HEADER_SIZE, ENCAPSULATION_STATE_SIZE, CIPHERTEXT1_SIZE]
    omega
  | ekReceivedCt1Sampled s =>
    rcases hbok with ⟨ha0, ⟨hes, hct1, hek⟩, henc⟩
    have ha := bsz_rawAuth_eq F ha0
    have he := bsz_rawPolyEnc_le henc
    simp only [States.into_pb, Chunked.SendCt.EkReceivedCt1Sampled.into_pb,
      Unchunked.SendCt.Ct1SentEkReceived.into_pb, rawV1State, rawInnerState,
      rawChEkReceivedCt1Sampled, rawUcCt1SentEkReceived, optRaw, ha, hes, hct1, hek,
      ENCAPSULATION_STATE_SIZE, CIPHERTEXT1_SIZE, ENCAPSULATION_KEY_SIZE]
    omega
  | ct1Acknowledged s =>
    rcases hbok with ⟨ha0, ⟨hhdr, hes, hct1⟩, hdec⟩
    have ha := bsz_rawAuth_eq F ha0
    have hd := bsz_rawPolyDec_le hdec
    simp only [States.into_pb, Chunked.SendCt.Ct1Acknowledged.into_pb,
      Unchunked.SendCt.Ct1Sent.into_pb, rawV1State, rawInnerState,
      rawChCt1Acknowledged, rawUcCt1Sent, optRaw, ha, hhdr, hes, hct1,
      HEADER_SIZE, ENCAPSULATION_STATE_SIZE, CIPHERTEXT1_SIZE]
    omega
  | ct2Sampled s =>
    rcases hbok with ⟨ha0, henc⟩
    have ha := bsz_rawAuth_eq F ha0
    have he := bsz_rawPolyEnc_le henc
    simp only [States.into_pb, Chunked.SendCt.Ct2Sampled.into_pb,
      Unchunked.SendCt.Ct2Sent.into_pb, rawV1State, rawInnerState,
      rawChCt2Sampled, rawUcCt2Sent, optRaw, ha]
    omega

end CryptoVerification.SpqrV1Sync.SendTotal
