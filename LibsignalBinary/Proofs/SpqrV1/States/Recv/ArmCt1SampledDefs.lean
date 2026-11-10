/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SpqrV1.Poly.AddChunk.Defs
public import LibsignalBinary.Proofs.SpqrV1.States.Leaves.Defs
public import LibsignalBinary.Proofs.SpqrV1.States.Recv.Decodes

/-!
# `<States>::recv` — `.ct1Sampled` Arm Definitions

**Checked by Lean.** `ADRP` page lemmas, pure unfolding equations, and word/byte decomposition
helpers (`Words5`, `Words50`, `Split928`) for the inlined `.ct1Sampled` arm (`0x55a4c`, `+1528`).
-/

@[expose] public section

namespace CryptoVerification.SpqrV1.States.Recv

open Arm64 ProofLib ProofLib.ProgramReflection
open CryptoGames.LibsignalSession (ShaCompress)
open CryptoVerification.RustHeap
open CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalTripleRatchetRepr
open CryptoVerification.LibsignalSpqrV1
open CryptoVerification.SpqrV1.Auth
open CryptoVerification.SpqrV1.GF.UnacceleratedMul
open CryptoVerification.SpqrV1.GF.Mul2U16
open CryptoVerification.SpqrV1.Poly
open CryptoVerification.SpqrV1.Poly.NextChunk
open CryptoVerification.SpqrV1.Poly.AddChunk
open CryptoVerification.SpqrV1.Drop
open CryptoVerification.SpqrV1.Alloc
open CryptoVerification.SpqrV1.States.Leaves
open CryptoVerification.CodeLayout

set_option maxRecDepth 200000
set_option maxHeartbeats 400000
set_option linter.unusedSimpArgs false

attribute [local irreducible] Program.fetch Program.externAt? Program.fnOff

theorem fnAddr_adrp_59620 {b : BitVec 64} {H : String → Option (State → State)}
    (hb : b &&& 0xfff#64 = 0#64) :
    (((libsignalSessionCode.rebase b H).fnAddr statesRecvName + 16844#64) &&&
      0xfffffffffffff000#64) = b + 0x54000#64 := by
  rw [Program.fnAddr_rebase, statesRecv_fnOff]
  revert hb; bv_bits

theorem fnAddr_adrp_5977c {b : BitVec 64} {H : String → Option (State → State)}
    (hb : b &&& 0xfff#64 = 0#64) :
    (((libsignalSessionCode.rebase b H).fnAddr statesRecvName + 17192#64) &&&
      0xfffffffffffff000#64) = b + 0x54000#64 := by
  rw [Program.fnAddr_rebase, statesRecv_fnOff]
  revert hb; bv_bits

theorem fnAddr_adrp_5988c {b : BitVec 64} {H : String → Option (State → State)}
    (hb : b &&& 0xfff#64 = 0#64) :
    (((libsignalSessionCode.rebase b H).fnAddr statesRecvName + 17464#64) &&&
      0xfffffffffffff000#64) = b + 0x54000#64 := by
  rw [Program.fnAddr_rebase, statesRecv_fnOff]
  revert hb; bv_bits

/-! ## 1. Pure Equations for `States.recv` on `.ct1Sampled` -/

theorem states_recv_ct1Sampled_gt (K : MlKem) {F : ShaCompress}
    (st : Chunked.SendCt.Ct1Sampled spqrPolyApi (spqrAuthApi F))
    (msg : Message spqrPolyApi) (hgt : msg.epoch > st.uc.epoch) :
    States.recv K (.ct1Sampled st) msg = .error (.err (.epochOutOfRange msg.epoch)) := by
  have hgt' : msg.epoch > st.epoch := hgt
  dsimp only [States.recv]
  rw [ite_eq_left_iff.mpr (fun h => absurd hgt' h)]

theorem states_recv_ct1Sampled_lt (K : MlKem) {F : ShaCompress}
    (st : Chunked.SendCt.Ct1Sampled spqrPolyApi (spqrAuthApi F))
    (msg : Message spqrPolyApi) (hlt : msg.epoch < st.uc.epoch) :
    States.recv K (.ct1Sampled st) msg =
      .ok { key := none, state := .ct1Sampled st } := by
  have hlt' : msg.epoch < st.epoch := hlt
  have hnot_gt' : ¬ (msg.epoch > st.epoch) := by
    change ¬ (st.epoch < msg.epoch)
    exact BitVec.not_lt.mpr (BitVec.le_of_lt hlt')
  dsimp only [States.recv]
  rw [ite_eq_right_iff.mpr (fun h => absurd h hnot_gt'),
      ite_eq_left_iff.mpr (fun h => absurd hlt' h)]

theorem states_recv_ct1Sampled_eq_other (K : MlKem) {F : ShaCompress}
    (st : Chunked.SendCt.Ct1Sampled spqrPolyApi (spqrAuthApi F))
    (msg : Message spqrPolyApi) (heq : msg.epoch = st.uc.epoch)
    (hek : ∀ c, msg.payload ≠ .ek c)
    (hekAck : ∀ c, msg.payload ≠ .ekCt1Ack c) :
    States.recv K (.ct1Sampled st) msg =
      .ok { key := none, state := .ct1Sampled st } := by
  have heq' : msg.epoch = st.epoch := heq
  have hnot_gt' : ¬ (msg.epoch > st.epoch) := by
    rw [heq']; exact BitVec.lt_irrefl _
  have hnot_lt' : ¬ (msg.epoch < st.epoch) := by
    rw [heq']; exact BitVec.lt_irrefl _
  dsimp only [States.recv]
  rw [ite_eq_right_iff.mpr (fun h => absurd h hnot_gt'),
      ite_eq_right_iff.mpr (fun h => absurd h hnot_lt')]
  cases hpay : msg.payload with
  | ek c => exact absurd hpay (hek c)
  | ekCt1Ack c => exact absurd hpay (hekAck c)
  | _ => rfl

theorem states_recv_ct1Sampled_eq_ek (K : MlKem) {F : ShaCompress}
    (st : Chunked.SendCt.Ct1Sampled spqrPolyApi (spqrAuthApi F))
    (msg : Message spqrPolyApi) (chunk : Chunk)
    (heq : msg.epoch = st.uc.epoch)
    (hpay : msg.payload = .ek chunk) :
    States.recv K (.ct1Sampled st) msg =
      Except.bind (st.recv_ek_chunk K st.uc.epoch chunk false) (fun res =>
        match res with
        | .stillReceivingStillSending s' => .ok { key := none, state := .ct1Sampled s' }
        | .stillReceiving s' => .ok { key := none, state := .ct1Acknowledged s' }
        | .stillSending s' => .ok { key := none, state := .ekReceivedCt1Sampled s' }
        | .done s' => .ok { key := none, state := .ct2Sampled s' }) := by
  have heq' : msg.epoch = st.epoch := heq
  have hnot_gt' : ¬ (msg.epoch > st.epoch) := by
    rw [heq']; exact BitVec.lt_irrefl _
  have hnot_lt' : ¬ (msg.epoch < st.epoch) := by
    rw [heq']; exact BitVec.lt_irrefl _
  dsimp only [States.recv]
  rw [ite_eq_right_iff.mpr (fun h => absurd h hnot_gt'),
      ite_eq_right_iff.mpr (fun h => absurd h hnot_lt'),
      hpay, heq]
  dsimp only [Bind.bind]
  congr 1; ext res; cases res <;> rfl

theorem states_recv_ct1Sampled_eq_ekCt1Ack (K : MlKem) {F : ShaCompress}
    (st : Chunked.SendCt.Ct1Sampled spqrPolyApi (spqrAuthApi F))
    (msg : Message spqrPolyApi) (chunk : Chunk)
    (heq : msg.epoch = st.uc.epoch)
    (hpay : msg.payload = .ekCt1Ack chunk) :
    States.recv K (.ct1Sampled st) msg =
      Except.bind (st.recv_ek_chunk K st.uc.epoch chunk true) (fun res =>
        match res with
        | .stillReceivingStillSending s' => .ok { key := none, state := .ct1Sampled s' }
        | .stillReceiving s' => .ok { key := none, state := .ct1Acknowledged s' }
        | .stillSending s' => .ok { key := none, state := .ekReceivedCt1Sampled s' }
        | .done s' => .ok { key := none, state := .ct2Sampled s' }) := by
  have heq' : msg.epoch = st.epoch := heq
  have hnot_gt' : ¬ (msg.epoch > st.epoch) := by
    rw [heq']; exact BitVec.lt_irrefl _
  have hnot_lt' : ¬ (msg.epoch < st.epoch) := by
    rw [heq']; exact BitVec.lt_irrefl _
  dsimp only [States.recv]
  rw [ite_eq_right_iff.mpr (fun h => absurd h hnot_gt'),
      ite_eq_right_iff.mpr (fun h => absurd h hnot_lt'),
      hpay, heq]
  dsimp only [Bind.bind]
  congr 1; ext res; cases res <;> rfl

theorem Relocatable.of_chunkedCt1AcknowledgedAt (A : RustAlloc) {F : ShaCompress}
    (st : Chunked.SendCt.Ct1Acknowledged spqrPolyApi (spqrAuthApi F)) :
    Relocatable 528 (fun a => chunkedCt1AcknowledgedAt A a st) := by
  unfold chunkedCt1AcknowledgedAt
  exact Relocatable.sepConj (off := 128#64) (m := 528) rfl rfl
    (Relocatable.of_unchunkedCt1SentAt A st.uc)
    (Relocatable.of_polyDecoderAt A st.receiving_ek)

theorem spqrPolyApi_add_chunk_eq_ok (dec : PolyDecoder) (chunk : spqrPolyApi.Chunk)
    (hlen : dec.pts.length = 16) :
    spqrPolyApi.add_chunk dec chunk = .ok (addChunkTotal dec chunk) := by
  dsimp only [spqrPolyApi, liftSpqrPanic]
  rw [addChunk_eq_ok dec chunk hlen]
  rfl

theorem ct1Sampled_recv_ek_chunk_none (K : MlKem) {F : ShaCompress}
    (st : Chunked.SendCt.Ct1Sampled spqrPolyApi (spqrAuthApi F))
    (chunk : spqrPolyApi.Chunk) (ack : Bool)
    (dec' : spqrPolyApi.PolyDecoder)
    (hadd : spqrPolyApi.add_chunk st.receiving_ek chunk = .ok dec')
    (hdec : spqrPolyApi.decoded_message dec' = .ok none) :
    st.recv_ek_chunk K st.uc.epoch chunk ack =
      if ack then
        .ok (.stillReceiving { uc := st.uc, receiving_ek := dec' })
      else
        .ok (.stillReceivingStillSending
          { uc := st.uc,
            sending_ct1 := st.sending_ct1,
            receiving_ek := dec' }) := by
  unfold Chunked.SendCt.Ct1Sampled.recv_ek_chunk
  rw [hadd]
  change Except.bind (.ok dec') _ = _
  dsimp only [Except.bind]
  rw [hdec]
  rfl

theorem ct1Sampled_recv_ek_chunk_some (K : MlKem) {F : ShaCompress}
    (st : Chunked.SendCt.Ct1Sampled spqrPolyApi (spqrAuthApi F))
    (chunk : spqrPolyApi.Chunk) (ack : Bool)
    (dec' : spqrPolyApi.PolyDecoder)
    (decoded : Bytes)
    (hadd : spqrPolyApi.add_chunk st.receiving_ek chunk = .ok dec')
    (hdec : spqrPolyApi.decoded_message dec' = .ok (some decoded)) :
    st.recv_ek_chunk K st.uc.epoch chunk ack =
      Except.bind (st.uc.recv_ek K st.uc.epoch decoded) (fun uc =>
        if ack then
          Except.bind (StatesResult.ofPanic (uc.send_ct2 K)) (fun x =>
            Except.bind (StatesResult.ofPanic (Chunked.SendCt.send_ct2_encoder spqrPolyApi x.2.1 x.2.2))
              (fun sendingCt2 =>
                .ok (.done { uc := x.1, sending_ct2 := sendingCt2 })))
        else
          .ok (.stillSending { uc := uc, sending_ct1 := st.sending_ct1 })) := by
  unfold Chunked.SendCt.Ct1Sampled.recv_ek_chunk
  rw [hadd]
  change Except.bind (.ok dec') _ = _
  dsimp only [Except.bind]
  rw [hdec]
  rfl

/-! ## 2. Word-Decomposition Helpers (`400`B Encoder/Decoder & `928`B `States`) -/

theorem exists_words_of_length : ∀ (k : Nat) (bs : List (BitVec 8)),
    bs.length = 8 * k → ∃ ws : List (BitVec 64), ws.length = k ∧ bs = wordsBytes ws
  | 0, bs, h => by
      have h0 : bs = [] := List.eq_nil_of_length_eq_zero (by omega)
      exact ⟨[], rfl, by rw [h0]; rfl⟩
  | k + 1, bs, h => by
      have htake : (bs.take 8).length = 8 := by simp [List.length_take]; omega
      have hdrop : (bs.drop 8).length = 8 * k := by simp [List.length_drop]; omega
      obtain ⟨w, hw⟩ := exists_unpack64_of_length_8 htake
      obtain ⟨ws, hlen, hws⟩ := exists_words_of_length k (bs.drop 8) hdrop
      refine ⟨w :: ws, by simp [hlen], ?_⟩
      rw [← List.take_append_drop 8 bs, hw, hws]
      rfl

/-- Five 64-bit words (`40` bytes = `0x28`) for trailing state tail words. -/
structure Words5 where
  w0 : BitVec 64
  w1 : BitVec 64
  w2 : BitVec 64
  w3 : BitVec 64
  w4 : BitVec 64

def Words5.toList (u : Words5) : List (BitVec 64) :=
  [u.w0, u.w1, u.w2, u.w3, u.w4]

@[simp] theorem Words5.toList_length (u : Words5) : u.toList.length = 5 := rfl

theorem wordsAt_5 (a : BitVec 64) (w0 w1 w2 w3 w4 : BitVec 64) :
    wordsAt a [w0, w1, w2, w3, w4] =
      ((a ↦₆₄ w0) ∗ ((a + 8#64) ↦₆₄ w1) ∗ ((a + 16#64) ↦₆₄ w2) ∗
       ((a + 24#64) ↦₆₄ w3) ∗ ((a + 32#64) ↦₆₄ w4)) := by
  dsimp only [wordsAt]
  simp only [sepConj_emp, BitVec.add_assoc]
  ac_rfl

/-- Sixteen 64-bit words (`128` bytes = `0x80`). -/
structure Words16 where
  w0 : BitVec 64
  w1 : BitVec 64
  w2 : BitVec 64
  w3 : BitVec 64
  w4 : BitVec 64
  w5 : BitVec 64
  w6 : BitVec 64
  w7 : BitVec 64
  w8 : BitVec 64
  w9 : BitVec 64
  w10 : BitVec 64
  w11 : BitVec 64
  w12 : BitVec 64
  w13 : BitVec 64
  w14 : BitVec 64
  w15 : BitVec 64

def Words16.toList (u : Words16) : List (BitVec 64) :=
  [u.w0, u.w1, u.w2, u.w3, u.w4, u.w5, u.w6, u.w7,
   u.w8, u.w9, u.w10, u.w11, u.w12, u.w13, u.w14, u.w15]

@[simp] theorem Words16.toList_length (u : Words16) : u.toList.length = 16 := rfl

theorem exists_words16_of_length_128 {bs : List (BitVec 8)} (h : bs.length = 128) :
    ∃ u : Words16, bs = wordsBytes u.toList := by
  obtain ⟨ws, hlen, hws⟩ := exists_words_of_length 16 bs (by omega)
  rcases ws with _ | ⟨w0, _ | ⟨w1, _ | ⟨w2, _ | ⟨w3, _ | ⟨w4, _ | ⟨w5, _ | ⟨w6, _ | ⟨w7,
    _ | ⟨w8, _ | ⟨w9, _ | ⟨w10, _ | ⟨w11, _ | ⟨w12, _ | ⟨w13, _ | ⟨w14, _ | ⟨w15, _ | _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩ <;>
    try simp at hlen
  exact ⟨⟨w0, w1, w2, w3, w4, w5, w6, w7, w8, w9, w10, w11, w12, w13, w14, w15⟩, hws⟩

theorem exists_words5_of_length_40 {bs : List (BitVec 8)} (h : bs.length = 40) :
    ∃ u : Words5, bs = wordsBytes u.toList := by
  obtain ⟨ws, hlen, hws⟩ := exists_words_of_length 5 bs (by omega)
  rcases ws with _ | ⟨w0, _ | ⟨w1, _ | ⟨w2, _ | ⟨w3, _ | ⟨w4, _ | _⟩⟩⟩⟩⟩ <;>
    try simp at hlen
  exact ⟨⟨w0, w1, w2, w3, w4⟩, hws⟩

/-- `50` 64-bit words (`400` bytes = `3 × 128 + 16`) for `PolynomialEncoder` / `PolynomialDecoder`. -/
structure Words50 where
  c0 : Words16
  c1 : Words16
  c2 : Words16
  w48 : BitVec 64
  w49 : BitVec 64

def Words50.toBytes (u : Words50) : List (BitVec 8) :=
  wordsBytes u.c0.toList ++ (wordsBytes u.c1.toList ++
    (wordsBytes u.c2.toList ++ wordsBytes [u.w48, u.w49]))

theorem Words50.toBytes_length (u : Words50) : u.toBytes.length = 400 := by
  dsimp only [Words50.toBytes]
  simp only [List.length_append, length_wordsBytes, Words16.toList_length,
    List.length_cons, List.length_nil]

def words50At (a : BitVec 64) (u : Words50) : SepProp :=
  wordsAt a u.c0.toList ∗
    wordsAt (a + 128#64) u.c1.toList ∗
    wordsAt (a + 256#64) u.c2.toList ∗
    ((a + 384#64) ↦₆₄ u.w48) ∗
    ((a + 392#64) ↦₆₄ u.w49)

theorem words50At_eq_pointsToBytes (a : BitVec 64) (u : Words50) :
    words50At a u = (a ↦ₛ u.toBytes) := by
  dsimp only [words50At, Words50.toBytes]
  have h48 : (((a + 384#64) ↦₆₄ u.w48) ∗ ((a + 392#64) ↦₆₄ u.w49)) =
      wordsAt (a + 384#64) [u.w48, u.w49] := by
    dsimp only [wordsAt]
    have ha : a + 384#64 + 8#64 = a + 392#64 := by bv_omega
    rw [ha, sepConj_emp]
  rw [pointsToBytes_append, pointsToBytes_append, pointsToBytes_append]
  simp only [length_wordsBytes, Words16.toList_length,
    ← wordsAt_eq_pointsToBytes]
  have ha1 : a + BitVec.ofNat 64 (8 * 16) = a + 128#64 := rfl
  have ha2 : a + 128#64 + BitVec.ofNat 64 (8 * 16) = a + 256#64 := by bv_omega
  have ha3 : a + 256#64 + BitVec.ofNat 64 (8 * 16) = a + 384#64 := by bv_omega
  rw [ha1, ha2, ha3, ← h48]

theorem exists_words50_of_length_400 {bs : List (BitVec 8)} (h : bs.length = 400) :
    ∃ u : Words50, bs = u.toBytes := by
  have h0 : (bs.take 128).length = 128 := by simp [List.length_take]; omega
  have h1 : ((bs.drop 128).take 128).length = 128 := by simp [List.length_take, List.length_drop]; omega
  have h2 : (((bs.drop 128).drop 128).take 128).length = 128 := by
    simp [List.length_take, List.length_drop]; omega
  have h3 : (((bs.drop 128).drop 128).drop 128).length = 8 * 2 := by
    simp [List.length_drop]; omega
  obtain ⟨c0, hc0⟩ := exists_words16_of_length_128 h0
  obtain ⟨c1, hc1⟩ := exists_words16_of_length_128 h1
  obtain ⟨c2, hc2⟩ := exists_words16_of_length_128 h2
  obtain ⟨ws3, hlen3, hws3⟩ := exists_words_of_length 2 _ h3
  rcases ws3 with _ | ⟨w48, _ | ⟨w49, _ | _⟩⟩ <;> try simp at hlen3
  refine ⟨⟨c0, c1, c2, w48, w49⟩, ?_⟩
  dsimp only [Words50.toBytes]
  rw [← hc0, ← hc1, ← hc2, ← hws3]
  simp only [List.take_append_drop]

theorem Relocatable.extract_400 {F : BitVec 64 → SepProp} (hrel : Relocatable 400 F) (a : BitVec 64) :
    F a ⊢ ∃∗ u : Words50, words50At a u ∗ relocatedHeap F u.toBytes := by
  refine Entails.trans (hrel a) ?_
  apply Entails.sepExists_elim; intro bs
  apply Entails.pure_left; intro hlen
  obtain ⟨u, rfl⟩ := exists_words50_of_length_400 hlen
  refine Entails.sepExists_right u ?_
  rw [words50At_eq_pointsToBytes]
  exact Entails.refl _

theorem words50At_entails_memRegion (a : BitVec 64) (u : Words50) :
    words50At a u ⊢ memRegion a 400 := by
  rw [words50At_eq_pointsToBytes]
  have h := pointsToBytes_entails_memRegion a u.toBytes
  rwa [Words50.toBytes_length] at h

/-- Decomposition of a `928`-byte `States` buffer into:
    - `c0, c1, c2, c3 : Words16` (`4 × 128 = 512`B at `+0..+512`)
    - `mid : List (BitVec 8)` (`376`B at `+512..+888`, copied via `memcpy(..., 376)`)
    - `tail : Words5` (`40`B at `+888..+928`) -/
structure Split928 where
  c0 : Words16
  c1 : Words16
  c2 : Words16
  c3 : Words16
  mid : List (BitVec 8)
  tail : Words5

def Split928.toBytes (u : Split928) : List (BitVec 8) :=
  wordsBytes u.c0.toList ++ (wordsBytes u.c1.toList ++
    (wordsBytes u.c2.toList ++ (wordsBytes u.c3.toList ++
      (u.mid ++ wordsBytes u.tail.toList))))

def split928At (a : BitVec 64) (u : Split928) : SepProp :=
  wordsAt a u.c0.toList ∗
    wordsAt (a + 128#64) u.c1.toList ∗
    wordsAt (a + 256#64) u.c2.toList ∗
    wordsAt (a + 384#64) u.c3.toList ∗
    ((a + 512#64) ↦ₛ u.mid) ∗
    wordsAt (a + 888#64) u.tail.toList

theorem split928At_eq_pointsToBytes (a : BitVec 64) (u : Split928) (hmid : u.mid.length = 376) :
    split928At a u = (a ↦ₛ u.toBytes) := by
  dsimp only [split928At, Split928.toBytes]
  rw [pointsToBytes_append, pointsToBytes_append, pointsToBytes_append,
      pointsToBytes_append, pointsToBytes_append]
  simp only [length_wordsBytes, Words16.toList_length, Words5.toList_length,
    hmid, ← wordsAt_eq_pointsToBytes]
  have ha1 : a + BitVec.ofNat 64 (8 * 16) = a + 128#64 := rfl
  have ha2 : a + 128#64 + BitVec.ofNat 64 (8 * 16) = a + 256#64 := by bv_omega
  have ha3 : a + 256#64 + BitVec.ofNat 64 (8 * 16) = a + 384#64 := by bv_omega
  have ha4 : a + 384#64 + BitVec.ofNat 64 (8 * 16) = a + 512#64 := by bv_omega
  have ha5 : a + 512#64 + BitVec.ofNat 64 376 = a + 888#64 := by bv_omega
  rw [ha1, ha2, ha3, ha4, ha5]

theorem Split928.toBytes_length (u : Split928) (hmid : u.mid.length = 376) :
    u.toBytes.length = chunkedStatesSize := by
  dsimp only [Split928.toBytes, chunkedStatesSize]
  simp only [List.length_append, length_wordsBytes, Words16.toList_length,
    Words5.toList_length, hmid]

theorem split928At_entails_memRegion (a : BitVec 64) (u : Split928) (hmid : u.mid.length = 376) :
    split928At a u ⊢ memRegion a chunkedStatesSize := by
  rw [split928At_eq_pointsToBytes a u hmid]
  have h := pointsToBytes_entails_memRegion a u.toBytes
  rwa [Split928.toBytes_length u hmid] at h

theorem exists_split928_of_length_928 {bs : List (BitVec 8)} (h : bs.length = 928) :
    ∃ u : Split928, u.mid.length = 376 ∧ bs = u.toBytes := by
  have h0 : (bs.take 128).length = 128 := by simp [List.length_take]; omega
  have h1 : ((bs.drop 128).take 128).length = 128 := by simp [List.length_take, List.length_drop]; omega
  have h2 : (((bs.drop 128).drop 128).take 128).length = 128 := by
    simp [List.length_take, List.length_drop]; omega
  have h3 : ((((bs.drop 128).drop 128).drop 128).take 128).length = 128 := by
    simp [List.length_take, List.length_drop]; omega
  have hmid : (((((bs.drop 128).drop 128).drop 128).drop 128).take 376).length = 376 := by
    simp [List.length_take, List.length_drop]; omega
  have htail : (((((bs.drop 128).drop 128).drop 128).drop 128).drop 376).length = 40 := by
    simp [List.length_drop]; omega
  obtain ⟨c0, hc0⟩ := exists_words16_of_length_128 h0
  obtain ⟨c1, hc1⟩ := exists_words16_of_length_128 h1
  obtain ⟨c2, hc2⟩ := exists_words16_of_length_128 h2
  obtain ⟨c3, hc3⟩ := exists_words16_of_length_128 h3
  obtain ⟨tail, htail_eq⟩ := exists_words5_of_length_40 htail
  refine ⟨⟨c0, c1, c2, c3, _, tail⟩, hmid, ?_⟩
  dsimp only [Split928.toBytes]
  rw [← hc0, ← hc1, ← hc2, ← hc3, ← htail_eq]
  simp only [List.take_append_drop]

theorem Relocatable.extract_928 {F : BitVec 64 → SepProp} (hrel : Relocatable 928 F) (a : BitVec 64) :
    F a ⊢ ∃∗ u : Split928, ⌜u.mid.length = 376⌝ ∗ split928At a u ∗ relocatedHeap F u.toBytes := by
  refine Entails.trans (hrel a) ?_
  apply Entails.sepExists_elim; intro bs
  apply Entails.pure_left; intro hlen
  obtain ⟨u, hmid, rfl⟩ := exists_split928_of_length_928 hlen
  refine Entails.sepExists_right u ?_
  refine Entails.pure_right hmid ?_
  rw [split928At_eq_pointsToBytes a u hmid]
  exact Entails.refl _

/-- Tag word (`0#64` for `.points`, `1#64` for `.polys`) at offset `+0` of `PolyEncoder`. -/
def polyEncoderTagVal (enc : PolyEncoder) : BitVec 64 :=
  match enc.s with
  | .points _ => 0#64
  | .polys _ => 1#64

theorem polyEncoderTagVal_zero_or_one (enc : PolyEncoder) :
    polyEncoderTagVal enc = 0#64 ∨ polyEncoderTagVal enc = 1#64 := by
  unfold polyEncoderTagVal
  cases enc.s <;> simp

/-- The `392`-byte body of `PolyEncoder` at `b = a + 8#64`. -/
def polyEncoderBodyAt (A : RustAlloc) (b : BitVec 64) (enc : PolyEncoder) : SepProp :=
  (match enc.s with
   | .points pts =>
     ⌜pts.length = NUM_POLYS ∧ (∀ pt ∈ pts, pt.value.length ≤ 0x0555555555555555)⌝ ∗
       pointListOf A b pts
   | .polys ps => ⌜ps.length = NUM_POLYS⌝ ∗ polyListOf A b ps) ∗
  ((b + 384#64) ↦₃₂ enc.idx) ∗
  memRegion (b + 388#64) polyEncoderPadSize

theorem polyEncoderAt_eq_tag_body (A : RustAlloc) (a : BitVec 64) (enc : PolyEncoder) :
    polyEncoderAt A a enc =
      (a ↦₆₄ polyEncoderTagVal enc) ∗ polyEncoderBodyAt A (a + 8#64) enc := by
  unfold polyEncoderAt encoderStateAt polyEncoderTagVal polyEncoderBodyAt
    polyEncoderPointsTag polyEncoderPolysTag polyEncoderVecsOff polyEncoderIdxOff polyEncoderPadOff
  have h392 : a + 392#64 = (a + 8#64) + 384#64 := by bv_omega
  have h396 : a + 396#64 = (a + 8#64) + 388#64 := by bv_omega
  rw [h392, h396]
  cases enc.s
  · dsimp only
    rw [← sepConj_assoc (⌜_⌝), sepConj_comm (⌜_⌝) (a ↦₆₄ 0#64)]
    ac_rfl
  · dsimp only
    rw [← sepConj_assoc (⌜_⌝), sepConj_comm (⌜_⌝) (a ↦₆₄ 1#64)]
    ac_rfl

theorem Relocatable.of_polyEncoderBodyAt (A : RustAlloc) (enc : PolyEncoder) :
    Relocatable 392 (fun b => polyEncoderBodyAt A b enc) := by
  have hstate : Relocatable 384 (fun b =>
      match enc.s with
      | .points pts =>
        ⌜pts.length = NUM_POLYS ∧ (∀ pt ∈ pts, pt.value.length ≤ 0x0555555555555555)⌝ ∗
          pointListOf A b pts
      | .polys ps => ⌜ps.length = NUM_POLYS⌝ ∗ polyListOf A b ps) := by
    cases hs : enc.s with
    | points pts =>
      dsimp only
      refine Relocatable.pure_left
        (pts.length = NUM_POLYS ∧ (∀ pt ∈ pts, pt.value.length ≤ 0x0555555555555555))
        fun ⟨hlen, _⟩ => ?_
      exact Relocatable.arrayAt (elem := fun pt addr => pointOf A addr pt)
        (fun pt => Relocatable.vecOf A gf16Stride gf16Align gf16At pt.value)
        pts 384 (by rw [hlen]; rfl)
    | polys ps =>
      dsimp only
      refine Relocatable.pure_left (ps.length = NUM_POLYS) fun hlen => ?_
      exact Relocatable.arrayAt (elem := fun p addr => polyOf A addr p)
        (fun p => Relocatable.vecOf A gf16Stride gf16Align gf16At p.coefficients)
        ps 384 (by rw [hlen]; rfl)
  have htail : Relocatable 8 (fun b =>
      (b ↦₃₂ enc.idx) ∗ memRegion (b + 4#64) polyEncoderPadSize) :=
    Relocatable.sepConj (off := 4#64) (m := 8) rfl rfl
      (Relocatable.pointsTo32 enc.idx) (Relocatable.of_memRegion polyEncoderPadSize)
  have hall := Relocatable.sepConj (off := 384#64) (m := 392) rfl rfl hstate htail
  refine Relocatable.congr rfl (fun b => ?_) hall
  dsimp only [polyEncoderBodyAt]
  have h388 : b + 384#64 + 4#64 = b + 388#64 := by bv_omega
  rw [h388]

/-- The `920`-byte body of `Chunked.SendCt.Ct1Sampled` at `b = a + 8#64`. -/
def chunkedCt1SampledBodyAt (A : RustAlloc) {F : ShaCompress} (b : BitVec 64)
    (st : Chunked.SendCt.Ct1Sampled spqrPolyApi (spqrAuthApi F)) : SepProp :=
  polyEncoderBodyAt A b st.sending_ct1 ∗
    unchunkedCt1SentAt A (b + 392#64) st.uc ∗
    polyDecoderAt A (b + 520#64) st.receiving_ek

theorem chunkedCt1SampledAt_eq_tag_body (A : RustAlloc) {F : ShaCompress} (a : BitVec 64)
    (st : Chunked.SendCt.Ct1Sampled spqrPolyApi (spqrAuthApi F)) :
    chunkedCt1SampledAt A a st =
      (a ↦₆₄ polyEncoderTagVal st.sending_ct1) ∗ chunkedCt1SampledBodyAt A (a + 8#64) st := by
  unfold chunkedCt1SampledAt chunkedCt1SampledBodyAt
  rw [polyEncoderAt_eq_tag_body A a st.sending_ct1]
  have h400 : a + 400#64 = (a + 8#64) + 392#64 := by bv_omega
  have h528 : a + 528#64 = (a + 8#64) + 520#64 := by bv_omega
  rw [h400, h528]
  ac_rfl

theorem Relocatable.of_chunkedCt1SampledBodyAt (A : RustAlloc) {F : ShaCompress}
    (st : Chunked.SendCt.Ct1Sampled spqrPolyApi (spqrAuthApi F)) :
    Relocatable 920 (fun b => chunkedCt1SampledBodyAt A b st) := by
  have h23 := Relocatable.sepConj (off := 128#64) (m := 528) rfl rfl
    (Relocatable.of_unchunkedCt1SentAt A st.uc)
    (Relocatable.of_polyDecoderAt A st.receiving_ek)
  have h123 := Relocatable.sepConj (off := 392#64) (m := 920) rfl rfl
    (Relocatable.of_polyEncoderBodyAt A st.sending_ct1) h23
  refine Relocatable.congr rfl (fun b => ?_) h123
  dsimp only [chunkedCt1SampledBodyAt]
  have h520 : b + 392#64 + 128#64 = b + 520#64 := by bv_omega
  rw [h520]

def Split928.tailBytes (u : Split928) : List (BitVec 8) :=
  wordsBytes [u.c0.w1, u.c0.w2, u.c0.w3, u.c0.w4, u.c0.w5, u.c0.w6, u.c0.w7,
    u.c0.w8, u.c0.w9, u.c0.w10, u.c0.w11, u.c0.w12, u.c0.w13, u.c0.w14, u.c0.w15] ++
    (wordsBytes u.c1.toList ++ (wordsBytes u.c2.toList ++
      (wordsBytes u.c3.toList ++ (u.mid ++ wordsBytes u.tail.toList))))

theorem split928At_eq_tag_and_tailBytes (a : BitVec 64) (u : Split928) (hmid : u.mid.length = 376) :
    split928At a u = ((a ↦₆₄ u.c0.w0) ∗ ((a + 8#64) ↦ₛ u.tailBytes)) := by
  rw [split928At_eq_pointsToBytes a u hmid]
  have hbytes : u.toBytes = unpack64 u.c0.w0 ++ u.tailBytes := by
    dsimp only [Split928.toBytes, Split928.tailBytes, Words16.toList, wordsBytes]
    rw [List.append_assoc]
  rw [hbytes, pointsToBytes_append a (unpack64 u.c0.w0) u.tailBytes,
      unpack64_length, ← pointsTo64_eq_pointsToBytes a u.c0.w0]

theorem exists_split928_with_tag {tag : BitVec 64} {bs : List (BitVec 8)} (h : bs.length = 920) :
    ∃ u : Split928, u.c0.w0 = tag ∧ u.mid.length = 376 ∧ bs = u.tailBytes := by
  have hfull : (unpack64 tag ++ bs).length = 928 := by
    rw [List.length_append, unpack64_length, h]
  have h0 : (bs.take 120).length = 8 * 15 := by simp [List.length_take]; omega
  have h1 : ((bs.drop 120).take 128).length = 128 := by simp [List.length_take, List.length_drop]; omega
  have h2 : (((bs.drop 120).drop 128).take 128).length = 128 := by
    simp [List.length_take, List.length_drop]; omega
  have h3 : ((((bs.drop 120).drop 128).drop 128).take 128).length = 128 := by
    simp [List.length_take, List.length_drop]; omega
  have hmid : (((((bs.drop 120).drop 128).drop 128).drop 128).take 376).length = 376 := by
    simp [List.length_take, List.length_drop]; omega
  have htail : (((((bs.drop 120).drop 128).drop 128).drop 128).drop 376).length = 40 := by
    simp [List.length_drop]; omega
  obtain ⟨ws0, hlen0, hws0⟩ := exists_words_of_length 15 (bs.take 120) h0
  rcases ws0 with _ | ⟨w1, _ | ⟨w2, _ | ⟨w3, _ | ⟨w4, _ | ⟨w5, _ | ⟨w6, _ | ⟨w7,
    _ | ⟨w8, _ | ⟨w9, _ | ⟨w10, _ | ⟨w11, _ | ⟨w12, _ | ⟨w13, _ | ⟨w14, _ | ⟨w15, _ | _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩ <;>
    try simp at hlen0
  obtain ⟨c1, hc1⟩ := exists_words16_of_length_128 h1
  obtain ⟨c2, hc2⟩ := exists_words16_of_length_128 h2
  obtain ⟨c3, hc3⟩ := exists_words16_of_length_128 h3
  obtain ⟨tail, htail_eq⟩ := exists_words5_of_length_40 htail
  refine ⟨⟨⟨tag, w1, w2, w3, w4, w5, w6, w7, w8, w9, w10, w11, w12, w13, w14, w15⟩,
    c1, c2, c3, _, tail⟩, rfl, hmid, ?_⟩
  dsimp only [Split928.tailBytes]
  rw [← hws0, ← hc1, ← hc2, ← hc3, ← htail_eq]
  simp only [List.take_append_drop]

theorem chunkedCt1SampledAt_extract_split928 (A : RustAlloc) {F : ShaCompress}
    (a : BitVec 64) (st : Chunked.SendCt.Ct1Sampled spqrPolyApi (spqrAuthApi F)) :
    (a ↦₆₄ polyEncoderTagVal st.sending_ct1) ∗ chunkedCt1SampledBodyAt A (a + 8#64) st ⊢
    ∃∗ u : Split928,
      ⌜u.c0.w0 = polyEncoderTagVal st.sending_ct1⌝ ∗
      ⌜u.mid.length = 376⌝ ∗
      split928At a u ∗
      relocatedHeap (fun b => chunkedCt1SampledBodyAt A b st) u.tailBytes := by
  refine Entails.trans (sepConj_mono_right (Relocatable.of_chunkedCt1SampledBodyAt A st (a + 8#64))) ?_
  rw [sepExists_sepConj_right]
  apply Entails.sepExists_elim; intro bs
  rw [sepConj_left_comm]
  apply Entails.pure_left; intro hlen
  obtain ⟨u, htag, hmid, rfl⟩ := exists_split928_with_tag (tag := polyEncoderTagVal st.sending_ct1) hlen
  refine Entails.sepExists_right u ?_
  refine Entails.pure_right htag (Entails.pure_right hmid ?_)
  rw [split928At_eq_tag_and_tailBytes a u hmid, htag, ← sepConj_assoc]
  exact Entails.refl _

theorem chunkedCt1SampledAt_reconstruct_split928 (A : RustAlloc) {F : ShaCompress}
    (outA : BitVec 64) (st : Chunked.SendCt.Ct1Sampled spqrPolyApi (spqrAuthApi F))
    (u : Split928) (htag : u.c0.w0 = polyEncoderTagVal st.sending_ct1) (hmid : u.mid.length = 376) :
    split928At outA u ∗ relocatedHeap (fun b => chunkedCt1SampledBodyAt A b st) u.tailBytes ⊢
    chunkedCt1SampledAt A outA st := by
  rw [split928At_eq_tag_and_tailBytes outA u hmid, htag,
      chunkedCt1SampledAt_eq_tag_body A outA st, sepConj_assoc]
  exact sepConj_mono_right
    (relocatedHeap_recompose (fun b => chunkedCt1SampledBodyAt A b st) u.tailBytes (outA + 8#64))

end CryptoVerification.SpqrV1.States.Recv
