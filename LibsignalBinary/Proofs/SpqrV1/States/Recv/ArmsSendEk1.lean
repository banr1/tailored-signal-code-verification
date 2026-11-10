/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SpqrV1.States.Recv.ArmCt1Received2
import LibsignalBinary.Proofs.SpqrV1.Poly.DecodedMessage.Defs
import LibsignalBinary.Proofs.SpqrV1.States.Recv.ArmCt1Received1
import ProofLib.SepLogic.WPp

/-!
# `<States>::recv`: Pure & Layout Helpers for `SendEk` Arms

Payload tag lemmas, `resultV1RecvAt` writeback entailments, and pure `States.recv` reductions
for `.keysSampled`, `.headerSent`, and `.ekSentCt1Received`.
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
open CryptoVerification.SpqrV1.Poly.EncodeBytes
open CryptoVerification.SpqrV1.Poly.AddChunk
open CryptoVerification.SpqrV1.Poly.DecodedMessage
open CryptoVerification.SpqrV1.Drop
open CryptoVerification.SpqrV1.Top
open CryptoVerification.SpqrV1.Top.MessageSerialize
open CryptoVerification.SpqrV1.States.Leaves
open CryptoVerification.SpqrV1.States.Leaves.RecvHdrChunk
open CryptoVerification.SpqrV1.States.RecvCt2Chunk
open CryptoVerification.CodeLayout

set_option maxRecDepth 200000
set_option maxHeartbeats 400000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

attribute [local irreducible] libsignalSessionCode Program.fetch Program.externAt? Program.fnOff
attribute [local arm64_norm, local wp_norm] bv_sub_add_lit bv_sub_sub_recv BitVec.sub_add_cancel BitVec.toNat_zero
  Leaves.extractLsb'_0_64_append Leaves.extractLsb'_64_64_append
  sp_sub_96_add_16 sp_sub_96_add_32 sp_sub_96_add_48 sp_sub_96_add_64 sp_sub_96_add_80
  sp_sub_96_sub_4096 sp_sub_4192_sub_48 sp_sub_4240_add_48 sp_sub_4240_add_4096 sp_sub_144_add_48
  sp_sub_96_add_8_recv sp_sub_80_add_8_recv sp_sub_64_add_8_recv sp_sub_48_add_8_recv
  sp_sub_32_add_8_recv sp_sub_16_add_8_recv sp_sub_96_add_96_recv

theorem messagePayloadTag_eq_5_of_not_ct1 {p : MessagePayload spqrPolyApi}
    (h : ∀ c, p ≠ .ct1 c) :
    (BitVec.zeroExtend 32 (messagePayloadTag p) == 5#32) = false := by
  cases p with
  | ct1 c => exact absurd rfl (h c)
  | _ => rfl

theorem messagePayloadTag_bne_5_of_not_ct1 {p : MessagePayload spqrPolyApi}
    (h : ∀ c, p ≠ .ct1 c) :
    (BitVec.zeroExtend 32 (messagePayloadTag p) != 5#32) = true := by
  cases p with
  | ct1 c => exact absurd rfl (h c)
  | _ => rfl

theorem messagePayloadAt_ct1 (msgA : BitVec 64) (chunk : Chunk) :
    messagePayloadAt spqrPolyApi msgA (.ct1 chunk) =
      (((msgA + 8#64) ↦₈ 5#8) ∗ memRegion (msgA + 9#64) 1 ∗
        chunkAt (msgA + 10#64) chunk ∗ memRegion (msgA + 44#64) 4) := rfl

theorem self_880_40_entails_memRegion_928 (selfA tag : BitVec 64) :
    (selfA ↦₆₄ tag) ∗ memRegion (selfA + 8#64) 880 ∗ memRegion (selfA + 888#64) 40 ⊢
      memRegion selfA chunkedStatesSize := by
  unfold chunkedStatesSize
  rw [ProofLib.memRegion_split selfA 8 920 (by decide),
      ProofLib.memRegion_split' (b := selfA + 8#64) (n := 880) (k := 40)
        (b' := selfA + 888#64) rfl (by bv_omega) (by decide)]
  exact sepConj_mono_left (ProofLib.pointsTo64_entails_memRegion selfA tag)

theorem writeback_keysSampled_entails_resultV1RecvAt (A : RustAlloc) {F : ShaCompress}
    (outA : BitVec 64) (st : Chunked.SendEk.KeysSampled spqrPolyApi (spqrAuthApi F))
    (w : Words63) (w936 : BitVec 64) (q944 : BitVec 128) :
    (outA ↦₆₄ 3#64) ∗
    words63At (outA + 8#64) w ∗
    relocatedHeap (fun dst => chunkedKeysSampledAt A dst st) (wordsBytes (words63List w)) ∗
    memRegion (outA + 512#64) 376 ∗
    memRegion (outA + 888#64) 40 ∗
    ((outA + 928#64) ↦₆₄ noneCap) ∗
    ((outA + 936#64) ↦₆₄ w936) ∗
    ((outA + 944#64) ↦₁₂₈ q944) ⊢
      resultV1RecvAt A (F := F) outA (.ok { key := none, state := .keysSampled st }) := by
  dsimp only [resultV1RecvAt, v1RecvAt, chunkedStatesAt]
  have h416 : memRegion (outA + 512#64) 376 ∗ memRegion (outA + 888#64) 40 ⊢
      memRegion (outA + 512#64) 416 := by
    rw [ProofLib.memRegion_split' (b := outA + 512#64) (n := 376) (k := 40)
      (b' := outA + 888#64) rfl (by bv_omega) (by decide)]
    exact Entails.refl _
  have hnone := none_tail_entails_optEpochSecretAt_none A (outA + 928#64) w936 q944
  have h936 : (outA + 928#64) + 8#64 = outA + 936#64 := by bv_omega
  have h944 : (outA + 928#64) + 16#64 = outA + 944#64 := by bv_omega
  rw [h936, h944] at hnone
  refine Entails.trans (Entails.of_eq (show _ =
    ((outA ↦₆₄ 3#64) ∗
     (words63At (outA + 8#64) w ∗
      relocatedHeap (fun dst => chunkedKeysSampledAt A dst st) (wordsBytes (words63List w))) ∗
     (memRegion (outA + 512#64) 376 ∗ memRegion (outA + 888#64) 40)) ∗
    (((outA + 928#64) ↦₆₄ noneCap) ∗ ((outA + 936#64) ↦₆₄ w936) ∗ ((outA + 944#64) ↦₁₂₈ q944)) by ac_rfl)) ?_
  exact sepConj_mono
    (sepConj_mono_right (sepConj_mono (recompose63 (outA + 8#64) w) h416))
    hnone

theorem writeback_headerSent_entails_resultV1RecvAt (A : RustAlloc) {F : ShaCompress}
    (outA : BitVec 64) (st : Chunked.SendEk.HeaderSent spqrPolyApi (spqrAuthApi F))
    (w : Words63) (tailBytes : List (BitVec 8)) (w936 : BitVec 64) (q944 : BitVec 128) :
    (outA ↦₆₄ 4#64) ∗
    words63At (outA + 8#64) w ∗
    ((outA + 512#64) ↦ₛ tailBytes) ∗
    relocatedHeap (fun dst => chunkedHeaderSentAt A dst st) (wordsBytes (words63List w) ++ tailBytes) ∗
    memRegion (outA + 888#64) 40 ∗
    ((outA + 928#64) ↦₆₄ noneCap) ∗
    ((outA + 936#64) ↦₆₄ w936) ∗
    ((outA + 944#64) ↦₁₂₈ q944) ⊢
      resultV1RecvAt A (F := F) outA (.ok { key := none, state := .headerSent st }) := by
  dsimp only [resultV1RecvAt, v1RecvAt, chunkedStatesAt]
  have hrec := recompose63_376 (F_pred := fun dst => chunkedHeaderSentAt A dst st) (outA + 8#64) w tailBytes
  have h512 : (outA + 8#64) + 504#64 = outA + 512#64 := by bv_omega
  rw [h512] at hrec
  have hnone := none_tail_entails_optEpochSecretAt_none A (outA + 928#64) w936 q944
  have h936 : (outA + 928#64) + 8#64 = outA + 936#64 := by bv_omega
  have h944 : (outA + 928#64) + 16#64 = outA + 944#64 := by bv_omega
  rw [h936, h944] at hnone
  refine Entails.trans (Entails.of_eq (show _ =
    ((outA ↦₆₄ 4#64) ∗
     (words63At (outA + 8#64) w ∗ ((outA + 512#64) ↦ₛ tailBytes) ∗
      relocatedHeap (fun dst => chunkedHeaderSentAt A dst st) (wordsBytes (words63List w) ++ tailBytes)) ∗
     memRegion (outA + 888#64) 40) ∗
    (((outA + 928#64) ↦₆₄ noneCap) ∗ ((outA + 936#64) ↦₆₄ w936) ∗ ((outA + 944#64) ↦₁₂₈ q944)) by ac_rfl)) ?_
  exact sepConj_mono (sepConj_mono_right (sepConj_mono_left hrec)) hnone

theorem polyDecoderAt_pts_length (A : RustAlloc) (a : BitVec 64) (dec : PolyDecoder) :
    polyDecoderAt A a dec ⊢ ⌜dec.pts.length = 16⌝ ∗ polyDecoderAt A a dec := by
  unfold polyDecoderAt
  apply Entails.pure_left
  intro ⟨hlen, hneed⟩
  exact Entails.pure_right hlen (Entails.pure_right ⟨hlen, hneed⟩ (Entails.refl _))

theorem chunkedHeaderSentAt_pts_length (A : RustAlloc) {F : ShaCompress}
    (a : BitVec 64) (st : Chunked.SendEk.HeaderSent spqrPolyApi (spqrAuthApi F)) :
    chunkedHeaderSentAt A a st ⊢
      ⌜st.receiving_ct1.pts.length = 16⌝ ∗ chunkedHeaderSentAt A a st := by
  unfold chunkedHeaderSentAt
  refine Entails.trans (sepConj_mono_right (sepConj_mono_right
    (polyDecoderAt_pts_length A (a + 480#64) st.receiving_ct1))) ?_
  exact Entails.of_eq (by ac_rfl)

attribute [local irreducible] addChunkTotal decodedMessageTotal

theorem headerSent_recv_ct1_chunk_eq_ok {F : ShaCompress}
    (st : Chunked.SendEk.HeaderSent spqrPolyApi (spqrAuthApi F)) (chunk : Chunk)
    (hlen : st.receiving_ct1.pts.length = 16)
    (hsort : PolyDecoderStrictSorted st.receiving_ct1) :
    ∃ outRes,
      st.recv_ct1_chunk st.uc.epoch chunk = .ok outRes ∧
      (∀ s', outRes = .stillReceiving s' → PolyDecoderStrictSorted s'.receiving_ct1) := by
  have hadd : spqrPolyApi.add_chunk st.receiving_ct1 chunk =
      .ok (addChunkTotal st.receiving_ct1 chunk) :=
    spqrPolyApi_add_chunk_eq_ok2 st.receiving_ct1 chunk hlen
  have hlen' := addChunkTotal_pts_length st.receiving_ct1 chunk hlen
  have hsort' := (addChunkBsearch_eq_addChunkTotal st.receiving_ct1 chunk hlen hsort).2
  have hdec : spqrPolyApi.decoded_message (addChunkTotal st.receiving_ct1 chunk) =
      .ok (decodedMessageTotal (addChunkTotal st.receiving_ct1 chunk)) := by
    change ((addChunkTotal st.receiving_ct1 chunk).decodedMessage).mapError PolyPanic.toSpqrPanic = _
    rw [decodedMessage_eq_ok (addChunkTotal st.receiving_ct1 chunk) hlen' hsort']
    rfl
  have hstep : st.recv_ct1_chunk st.uc.epoch chunk =
      match decodedMessageTotal (addChunkTotal st.receiving_ct1 chunk) with
      | some decoded => do
        let uc ← st.uc.recv_ct1 st.uc.epoch decoded
        .ok (.done { uc := uc, sending_ek := st.sending_ek })
      | none =>
        .ok (.stillReceiving
          { uc := st.uc, sending_ek := st.sending_ek,
            receiving_ct1 := addChunkTotal st.receiving_ct1 chunk }) := by
    unfold Chunked.SendEk.HeaderSent.recv_ct1_chunk
    rw [bne_self_eq_false, ite_eq_right_iff.mpr (fun h => nomatch h)]
    rw [except_lift_bind_ok2 hadd]
    rw [except_lift_bind_ok2 hdec]
    rfl
  rw [hstep]
  cases decodedMessageTotal (addChunkTotal st.receiving_ct1 chunk) with
  | none =>
    let s1 : Chunked.SendEk.HeaderSent spqrPolyApi (spqrAuthApi F) :=
      { uc := st.uc, sending_ek := st.sending_ek, receiving_ct1 := addChunkTotal st.receiving_ct1 chunk }
    refine ⟨.stillReceiving s1, rfl, ?_⟩
    intro s' hs'
    cases hs'
    exact hsort'
  | some decoded =>
    let uc1 : Unchunked.SendEk.EkSentCt1Received (spqrAuthApi F) :=
      { epoch := st.uc.epoch, auth := st.uc.auth, dk := st.uc.dk, ct1 := decoded }
    let s1 : Chunked.SendEk.Ct1Received spqrPolyApi (spqrAuthApi F) :=
      { uc := uc1, sending_ek := st.sending_ek }
    refine ⟨.done s1, ?_, ?_⟩
    · change Except.bind (st.uc.recv_ct1 st.uc.epoch decoded) _ = _
      unfold Unchunked.SendEk.EkSent.recv_ct1
      rw [bne_self_eq_false]
      rfl
    · intro s' hs'
      nomatch hs'

/-! ## Pure `States.recv` Lemmas for `.keysSampled` and `.headerSent` -/

theorem states_recv_keysSampled_gt {F : ShaCompress} (K : MlKem)
    (st : Chunked.SendEk.KeysSampled spqrPolyApi (spqrAuthApi F))
    (msg : Message spqrPolyApi)
    (hgt : msg.epoch > st.uc.epoch) :
    States.recv K (.keysSampled st) msg = .error (.err (.epochOutOfRange msg.epoch)) := by
  have hgt' : msg.epoch > st.epoch := hgt
  dsimp only [States.recv]
  rw [ite_eq_left_iff.mpr (fun h => absurd hgt' h)]

theorem states_recv_keysSampled_lt {F : ShaCompress} (K : MlKem)
    (st : Chunked.SendEk.KeysSampled spqrPolyApi (spqrAuthApi F))
    (msg : Message spqrPolyApi)
    (hlt : msg.epoch < st.uc.epoch) :
    States.recv K (.keysSampled st) msg = .ok { key := none, state := .keysSampled st } := by
  have hlt' : msg.epoch < st.epoch := hlt
  have hnot_gt' : ¬ (msg.epoch > st.epoch) := by
    change ¬ (st.epoch < msg.epoch)
    exact BitVec.not_lt.mpr (BitVec.le_of_lt hlt')
  dsimp only [States.recv]
  rw [ite_eq_right_iff.mpr (fun h => absurd h hnot_gt'),
      ite_eq_left_iff.mpr (fun h => absurd hlt' h)]

theorem states_recv_keysSampled_eq_other {F : ShaCompress} (K : MlKem)
    (st : Chunked.SendEk.KeysSampled spqrPolyApi (spqrAuthApi F))
    (msg : Message spqrPolyApi)
    (heq : msg.epoch = st.uc.epoch)
    (hct1 : ∀ c, msg.payload ≠ .ct1 c) :
    States.recv K (.keysSampled st) msg = .ok { key := none, state := .keysSampled st } := by
  have heq' : msg.epoch = st.epoch := heq
  have hnot_gt' : ¬ (msg.epoch > st.epoch) := by
    rw [heq']; exact BitVec.lt_irrefl _
  have hnot_lt' : ¬ (msg.epoch < st.epoch) := by
    rw [heq']; exact BitVec.lt_irrefl _
  dsimp only [States.recv]
  rw [ite_eq_right_iff.mpr (fun h => absurd h hnot_gt'),
      ite_eq_right_iff.mpr (fun h => absurd h hnot_lt')]
  cases hpay : msg.payload with
  | ct1 c => exact absurd hpay (hct1 c)
  | _ => rfl

theorem states_recv_keysSampled_eq_ct1_ok {F : ShaCompress} (K : MlKem)
    (st : Chunked.SendEk.KeysSampled spqrPolyApi (spqrAuthApi F))
    (msg : Message spqrPolyApi) (chunk : Chunk)
    (outSt : Chunked.SendEk.HeaderSent spqrPolyApi (spqrAuthApi F))
    (heq : msg.epoch = st.uc.epoch)
    (hpay : msg.payload = .ct1 chunk)
    (hrecv : st.recv_ct1_chunk st.uc.epoch chunk = .ok outSt) :
    States.recv K (.keysSampled st) msg = .ok { key := none, state := .headerSent outSt } := by
  have heq' : msg.epoch = st.epoch := heq
  have hnot_gt' : ¬ (msg.epoch > st.epoch) := by
    rw [heq']; exact BitVec.lt_irrefl _
  have hnot_lt' : ¬ (msg.epoch < st.epoch) := by
    rw [heq']; exact BitVec.lt_irrefl _
  dsimp only [States.recv]
  rw [ite_eq_right_iff.mpr (fun h => absurd h hnot_gt'),
      ite_eq_right_iff.mpr (fun h => absurd h hnot_lt'),
      hpay, heq]
  change Except.bind (StatesResult.ofPanic (st.recv_ct1_chunk st.uc.epoch chunk)) _ = _
  rw [hrecv]
  rfl

theorem states_recv_keysSampled_eq_ct1_panic {F : ShaCompress} (K : MlKem)
    (st : Chunked.SendEk.KeysSampled spqrPolyApi (spqrAuthApi F))
    (msg : Message spqrPolyApi) (chunk : Chunk) (p : StatesPanic)
    (heq : msg.epoch = st.uc.epoch)
    (hpay : msg.payload = .ct1 chunk)
    (hrecv : st.recv_ct1_chunk st.uc.epoch chunk = .error p) :
    (States.recv K (.keysSampled st) msg).isPanic = true := by
  have heq' : msg.epoch = st.epoch := heq
  have hnot_gt' : ¬ (msg.epoch > st.epoch) := by
    rw [heq']; exact BitVec.lt_irrefl _
  have hnot_lt' : ¬ (msg.epoch < st.epoch) := by
    rw [heq']; exact BitVec.lt_irrefl _
  have hstep : States.recv K (.keysSampled st) msg = .error (.panic p) := by
    dsimp only [States.recv]
    rw [ite_eq_right_iff.mpr (fun h => absurd h hnot_gt'),
        ite_eq_right_iff.mpr (fun h => absurd h hnot_lt'),
        hpay, heq]
    change Except.bind (StatesResult.ofPanic (st.recv_ct1_chunk st.uc.epoch chunk)) _ = _
    rw [hrecv]
    rfl
  rw [hstep]
  rfl

theorem states_recv_headerSent_gt {F : ShaCompress} (K : MlKem)
    (st : Chunked.SendEk.HeaderSent spqrPolyApi (spqrAuthApi F))
    (msg : Message spqrPolyApi)
    (hgt : msg.epoch > st.uc.epoch) :
    States.recv K (.headerSent st) msg = .error (.err (.epochOutOfRange msg.epoch)) := by
  have hgt' : msg.epoch > st.epoch := hgt
  dsimp only [States.recv]
  rw [ite_eq_left_iff.mpr (fun h => absurd hgt' h)]

theorem states_recv_headerSent_lt {F : ShaCompress} (K : MlKem)
    (st : Chunked.SendEk.HeaderSent spqrPolyApi (spqrAuthApi F))
    (msg : Message spqrPolyApi)
    (hlt : msg.epoch < st.uc.epoch) :
    States.recv K (.headerSent st) msg = .ok { key := none, state := .headerSent st } := by
  have hlt' : msg.epoch < st.epoch := hlt
  have hnot_gt' : ¬ (msg.epoch > st.epoch) := by
    change ¬ (st.epoch < msg.epoch)
    exact BitVec.not_lt.mpr (BitVec.le_of_lt hlt')
  dsimp only [States.recv]
  rw [ite_eq_right_iff.mpr (fun h => absurd h hnot_gt'),
      ite_eq_left_iff.mpr (fun h => absurd hlt' h)]

theorem states_recv_headerSent_eq_other {F : ShaCompress} (K : MlKem)
    (st : Chunked.SendEk.HeaderSent spqrPolyApi (spqrAuthApi F))
    (msg : Message spqrPolyApi)
    (heq : msg.epoch = st.uc.epoch)
    (hct1 : ∀ c, msg.payload ≠ .ct1 c) :
    States.recv K (.headerSent st) msg = .ok { key := none, state := .headerSent st } := by
  have heq' : msg.epoch = st.epoch := heq
  have hnot_gt' : ¬ (msg.epoch > st.epoch) := by
    rw [heq']; exact BitVec.lt_irrefl _
  have hnot_lt' : ¬ (msg.epoch < st.epoch) := by
    rw [heq']; exact BitVec.lt_irrefl _
  dsimp only [States.recv]
  rw [ite_eq_right_iff.mpr (fun h => absurd h hnot_gt'),
      ite_eq_right_iff.mpr (fun h => absurd h hnot_lt')]
  cases hpay : msg.payload with
  | ct1 c => exact absurd hpay (hct1 c)
  | _ => rfl

theorem states_recv_headerSent_eq_ct1_done {F : ShaCompress} (K : MlKem)
    (st : Chunked.SendEk.HeaderSent spqrPolyApi (spqrAuthApi F))
    (msg : Message spqrPolyApi) (chunk : Chunk)
    (outSt : Chunked.SendEk.Ct1Received spqrPolyApi (spqrAuthApi F))
    (heq : msg.epoch = st.uc.epoch)
    (hpay : msg.payload = .ct1 chunk)
    (hrecv : st.recv_ct1_chunk st.uc.epoch chunk = .ok (.done outSt)) :
    States.recv K (.headerSent st) msg = .ok { key := none, state := .ct1Received outSt } := by
  have heq' : msg.epoch = st.epoch := heq
  have hnot_gt' : ¬ (msg.epoch > st.epoch) := by
    rw [heq']; exact BitVec.lt_irrefl _
  have hnot_lt' : ¬ (msg.epoch < st.epoch) := by
    rw [heq']; exact BitVec.lt_irrefl _
  dsimp only [States.recv]
  rw [ite_eq_right_iff.mpr (fun h => absurd h hnot_gt'),
      ite_eq_right_iff.mpr (fun h => absurd h hnot_lt'),
      hpay, heq]
  change Except.bind (StatesResult.ofPanic (st.recv_ct1_chunk st.uc.epoch chunk)) _ = _
  rw [hrecv]
  rfl

theorem states_recv_headerSent_eq_ct1_still {F : ShaCompress} (K : MlKem)
    (st : Chunked.SendEk.HeaderSent spqrPolyApi (spqrAuthApi F))
    (msg : Message spqrPolyApi) (chunk : Chunk)
    (outSt : Chunked.SendEk.HeaderSent spqrPolyApi (spqrAuthApi F))
    (heq : msg.epoch = st.uc.epoch)
    (hpay : msg.payload = .ct1 chunk)
    (hrecv : st.recv_ct1_chunk st.uc.epoch chunk = .ok (.stillReceiving outSt)) :
    States.recv K (.headerSent st) msg = .ok { key := none, state := .headerSent outSt } := by
  have heq' : msg.epoch = st.epoch := heq
  have hnot_gt' : ¬ (msg.epoch > st.epoch) := by
    rw [heq']; exact BitVec.lt_irrefl _
  have hnot_lt' : ¬ (msg.epoch < st.epoch) := by
    rw [heq']; exact BitVec.lt_irrefl _
  dsimp only [States.recv]
  rw [ite_eq_right_iff.mpr (fun h => absurd h hnot_gt'),
      ite_eq_right_iff.mpr (fun h => absurd h hnot_lt'),
      hpay, heq]
  change Except.bind (StatesResult.ofPanic (st.recv_ct1_chunk st.uc.epoch chunk)) _ = _
  rw [hrecv]
  rfl

/-! ## Pure `States.recv` Lemmas for `.ekSentCt1Received` -/

theorem states_recv_ekSentCt1Received_gt {F : ShaCompress} (K : MlKem)
    (st : Chunked.SendEk.EkSentCt1Received spqrPolyApi (spqrAuthApi F))
    (msg : Message spqrPolyApi)
    (hgt : msg.epoch > st.uc.epoch) :
    States.recv K (.ekSentCt1Received st) msg = .error (.err (.epochOutOfRange msg.epoch)) := by
  have hgt' : msg.epoch > st.epoch := hgt
  dsimp only [States.recv]
  rw [ite_eq_left_iff.mpr (fun h => absurd hgt' h)]

theorem states_recv_ekSentCt1Received_lt {F : ShaCompress} (K : MlKem)
    (st : Chunked.SendEk.EkSentCt1Received spqrPolyApi (spqrAuthApi F))
    (msg : Message spqrPolyApi)
    (hlt : msg.epoch < st.uc.epoch) :
    States.recv K (.ekSentCt1Received st) msg = .ok { key := none, state := .ekSentCt1Received st } := by
  have hlt' : msg.epoch < st.epoch := hlt
  have hnot_gt' : ¬ (msg.epoch > st.epoch) := by
    change ¬ (st.epoch < msg.epoch)
    exact BitVec.not_lt.mpr (BitVec.le_of_lt hlt')
  dsimp only [States.recv]
  rw [ite_eq_right_iff.mpr (fun h => absurd h hnot_gt'),
      ite_eq_left_iff.mpr (fun h => absurd hlt' h)]

theorem states_recv_ekSentCt1Received_eq_other {F : ShaCompress} (K : MlKem)
    (st : Chunked.SendEk.EkSentCt1Received spqrPolyApi (spqrAuthApi F))
    (msg : Message spqrPolyApi)
    (heq : msg.epoch = st.uc.epoch)
    (hct2 : ∀ c, msg.payload ≠ .ct2 c) :
    States.recv K (.ekSentCt1Received st) msg = .ok { key := none, state := .ekSentCt1Received st } := by
  have heq' : msg.epoch = st.epoch := heq
  have hnot_gt' : ¬ (msg.epoch > st.epoch) := by
    rw [heq']; exact BitVec.lt_irrefl _
  have hnot_lt' : ¬ (msg.epoch < st.epoch) := by
    rw [heq']; exact BitVec.lt_irrefl _
  dsimp only [States.recv]
  rw [ite_eq_right_iff.mpr (fun h => absurd h hnot_gt'),
      ite_eq_right_iff.mpr (fun h => absurd h hnot_lt')]
  cases hpay : msg.payload with
  | ct2 c => exact absurd hpay (hct2 c)
  | _ => rfl

theorem states_recv_ekSentCt1Received_eq_ct2_still {F : ShaCompress} (K : MlKem)
    (st : Chunked.SendEk.EkSentCt1Received spqrPolyApi (spqrAuthApi F))
    (msg : Message spqrPolyApi) (chunk : Chunk)
    (outSt : Chunked.SendEk.EkSentCt1Received spqrPolyApi (spqrAuthApi F))
    (heq : msg.epoch = st.uc.epoch)
    (hpay : msg.payload = .ct2 chunk)
    (hrecv : st.recv_ct2_chunk K st.uc.epoch chunk = .ok (.stillReceiving outSt)) :
    States.recv K (.ekSentCt1Received st) msg =
      .ok { key := none, state := .ekSentCt1Received outSt } := by
  have heq' : msg.epoch = st.epoch := heq
  have hnot_gt' : ¬ (msg.epoch > st.epoch) := by
    rw [heq']; exact BitVec.lt_irrefl _
  have hnot_lt' : ¬ (msg.epoch < st.epoch) := by
    rw [heq']; exact BitVec.lt_irrefl _
  dsimp only [States.recv]
  rw [ite_eq_right_iff.mpr (fun h => absurd h hnot_gt'),
      ite_eq_right_iff.mpr (fun h => absurd h hnot_lt'),
      hpay, heq]
  change Except.bind (st.recv_ct2_chunk K st.uc.epoch chunk) _ = _
  rw [hrecv]
  rfl

theorem states_recv_ekSentCt1Received_eq_ct2_done {F : ShaCompress} (K : MlKem)
    (st : Chunked.SendEk.EkSentCt1Received spqrPolyApi (spqrAuthApi F))
    (msg : Message spqrPolyApi) (chunk : Chunk)
    (nhr : Chunked.SendCt.NoHeaderReceived spqrPolyApi (spqrAuthApi F))
    (sec : EpochSecret)
    (heq : msg.epoch = st.uc.epoch)
    (hpay : msg.payload = .ct2 chunk)
    (hrecv : st.recv_ct2_chunk K st.uc.epoch chunk = .ok (.done (nhr, sec))) :
    States.recv K (.ekSentCt1Received st) msg =
      .ok { key := some sec, state := .noHeaderReceived nhr } := by
  have heq' : msg.epoch = st.epoch := heq
  have hnot_gt' : ¬ (msg.epoch > st.epoch) := by
    rw [heq']; exact BitVec.lt_irrefl _
  have hnot_lt' : ¬ (msg.epoch < st.epoch) := by
    rw [heq']; exact BitVec.lt_irrefl _
  dsimp only [States.recv]
  rw [ite_eq_right_iff.mpr (fun h => absurd h hnot_gt'),
      ite_eq_right_iff.mpr (fun h => absurd h hnot_lt'),
      hpay, heq]
  change Except.bind (st.recv_ct2_chunk K st.uc.epoch chunk) _ = _
  rw [hrecv]
  rfl

theorem states_recv_ekSentCt1Received_eq_ct2_err {F : ShaCompress} (K : MlKem)
    (st : Chunked.SendEk.EkSentCt1Received spqrPolyApi (spqrAuthApi F))
    (msg : Message spqrPolyApi) (chunk : Chunk) (e : Error)
    (heq : msg.epoch = st.uc.epoch)
    (hpay : msg.payload = .ct2 chunk)
    (hrecv : st.recv_ct2_chunk K st.uc.epoch chunk = .error (.err e)) :
    States.recv K (.ekSentCt1Received st) msg = .error (.err e) := by
  have heq' : msg.epoch = st.epoch := heq
  have hnot_gt' : ¬ (msg.epoch > st.epoch) := by
    rw [heq']; exact BitVec.lt_irrefl _
  have hnot_lt' : ¬ (msg.epoch < st.epoch) := by
    rw [heq']; exact BitVec.lt_irrefl _
  dsimp only [States.recv]
  rw [ite_eq_right_iff.mpr (fun h => absurd h hnot_gt'),
      ite_eq_right_iff.mpr (fun h => absurd h hnot_lt'),
      hpay, heq]
  change Except.bind (st.recv_ct2_chunk K st.uc.epoch chunk) _ = _
  rw [hrecv]
  rfl

theorem states_recv_ekSentCt1Received_eq_ct2_panic {F : ShaCompress} (K : MlKem)
    (st : Chunked.SendEk.EkSentCt1Received spqrPolyApi (spqrAuthApi F))
    (msg : Message spqrPolyApi) (chunk : Chunk)
    (heq : msg.epoch = st.uc.epoch)
    (hpay : msg.payload = .ct2 chunk)
    (hpan : (st.recv_ct2_chunk K st.uc.epoch chunk).isPanic = true) :
    (States.recv K (.ekSentCt1Received st) msg).isPanic = true := by
  have heq' : msg.epoch = st.epoch := heq
  have hnot_gt' : ¬ (msg.epoch > st.epoch) := by
    rw [heq']; exact BitVec.lt_irrefl _
  have hnot_lt' : ¬ (msg.epoch < st.epoch) := by
    rw [heq']; exact BitVec.lt_irrefl _
  cases h : st.recv_ct2_chunk K st.uc.epoch chunk with
  | ok _ => rw [h] at hpan; contradiction
  | error err =>
    cases err with
    | err _ => rw [h] at hpan; contradiction
    | panic p =>
      have hstep : States.recv K (.ekSentCt1Received st) msg = .error (.panic p) := by
        dsimp only [States.recv]
        rw [ite_eq_right_iff.mpr (fun h => absurd h hnot_gt'),
            ite_eq_right_iff.mpr (fun h => absurd h hnot_lt'),
            hpay, heq]
        change Except.bind (st.recv_ct2_chunk K st.uc.epoch chunk) _ = _
        rw [h]
        rfl
      rw [hstep]
      rfl

end CryptoVerification.SpqrV1.States.Recv
