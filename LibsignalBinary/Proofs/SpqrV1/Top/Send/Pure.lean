/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Specifications.LibsignalSpqrV1.Model
public import LibsignalBinary.Proofs.SpqrV1.States.FromPb.Defs
public import LibsignalBinary.Proofs.SpqrV1.Top.StateSizeBase
import LibsignalBinary.Proofs.SpqrV1.Top.MessageSerialize
import LibsignalBinary.Proofs.SpqrV1.Top.StateSize

/-!
# Pure Reduction and Size-Bound Lemmas for `spqr::send::<HookRng>` (`0x3085c`)

**Checked by Lean.**

Provides pure unfolding, early-return, and size-bound lemmas bridging `(spqrV1 F K).send`,
`draws`, and `sendPanics` to `LibsignalSpqrV1.send`, `spqrDecodeState`, `v1StatePtsBound`,
and `Message.serialize`.
-/

@[expose] public section

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace CryptoVerification.SpqrV1.Top.Send

open Arm64
open CryptoGames.LibsignalSession (ShaCompress)
open CryptoGames.HKDF (Salt)
open CryptoVerification
open CryptoVerification.LibsignalSpqrV1
open CryptoVerification.SpqrV1.Top.StateSize
open CryptoVerification.SpqrV1.Top.MessageSerialize
open CryptoVerification.SpqrV1.States.FromPb

/-! ## `spqrV1` Model Unfolding (`send`, `draws`, `sendPanics`) -/

theorem spqrV1_send_eq (F : ShaCompress) (K : MlKem) (stateBytes tape : Bytes) :
    (spqrV1 F K).send stateBytes tape =
      (toSpqrModel (spqrDeps F K) (spqrHkdfWith F)).send stateBytes tape := by
  rw [spqrV1_eq]

theorem spqrV1_draws_eq (F : ShaCompress) (K : MlKem) (stateBytes tape : Bytes) :
    (spqrV1 F K).draws stateBytes tape =
      tape.length - (LibsignalSpqrV1.send (spqrDeps F K) (spqrHkdfWith F) stateBytes tape).2.length := by
  rw [spqrV1_eq]; rfl

theorem spqrV1_sendPanics_eq (F : ShaCompress) (K : MlKem) (stateBytes tape : Bytes) :
    (spqrV1 F K).sendPanics stateBytes tape =
      (toSpqrModel (spqrDeps F K) (spqrHkdfWith F)).sendPanics stateBytes tape := by
  rw [spqrV1_eq]

theorem spqrV1_send_of_ok {F : ShaCompress} {K : MlKem}
    {stateBytes tape : Bytes} {s : Send} {salt : Salt}
    (h : (LibsignalSpqrV1.send (spqrDeps F K) (spqrHkdfWith F) stateBytes tape).1 = .ok s)
    (hsalt : messageKeyToSalt? s.key = some salt) :
    (spqrV1 F K).send stateBytes tape = some (s.state, salt, s.msg) := by
  rw [spqrV1_send_eq]
  simp [toSpqrModel, h, hsalt]

theorem spqrV1_send_of_err {F : ShaCompress} {K : MlKem}
    {stateBytes tape : Bytes} {e : SpqrApiError}
    (h : (LibsignalSpqrV1.send (spqrDeps F K) (spqrHkdfWith F) stateBytes tape).1 = .error e) :
    (spqrV1 F K).send stateBytes tape = none := by
  rw [spqrV1_send_eq]
  simp [toSpqrModel, h]

theorem spqrV1_sendPanics_of_panic {F : ShaCompress} {K : MlKem}
    {stateBytes tape : Bytes} {p : SpqrApiPanic}
    (h : (LibsignalSpqrV1.send (spqrDeps F K) (spqrHkdfWith F) stateBytes tape).1 = .error (.panic p)) :
    (spqrV1 F K).sendPanics stateBytes tape := by
  rw [spqrV1_sendPanics_eq]
  simp [toSpqrModel, sendPanicsPureB, h]

/-- A Rust-level `.ok` rules out a model panic (the `¬ sendPanics` conjunct of `spqrSendSpec.post`). -/
theorem spqrV1_not_sendPanics_of_ok {F : ShaCompress} {K : MlKem}
    {stateBytes tape : Bytes} {s : Send}
    (h : (LibsignalSpqrV1.send (spqrDeps F K) (spqrHkdfWith F) stateBytes tape).1 = .ok s) :
    ¬ (spqrV1 F K).sendPanics stateBytes tape := by
  rw [spqrV1_sendPanics_eq]
  simp [toSpqrModel, sendPanicsPureB, h]

/-- A Rust-level `.error (.err _)` rules out a model panic. -/
theorem spqrV1_not_sendPanics_of_err {F : ShaCompress} {K : MlKem}
    {stateBytes tape : Bytes} {e : LibsignalSpqrV1.Error}
    (h : (LibsignalSpqrV1.send (spqrDeps F K) (spqrHkdfWith F) stateBytes tape).1 =
      .error (.err e)) :
    ¬ (spqrV1 F K).sendPanics stateBytes tape := by
  rw [spqrV1_sendPanics_eq]
  simp [toSpqrModel, sendPanicsPureB, h]

theorem spqrV1_draws_zero_of_remaining_eq {F : ShaCompress} {K : MlKem}
    {stateBytes tape : Bytes}
    (h : (LibsignalSpqrV1.send (spqrDeps F K) (spqrHkdfWith F) stateBytes tape).2 = tape) :
    (spqrV1 F K).draws stateBytes tape = 0 := by
  rw [spqrV1_draws_eq, h, Nat.sub_self]

/-! ## `decodeState` and `spqrDecodeState` Bridges -/

theorem decodeState_spqrDeps_of_spqrDecodeState_error
    (F : ShaCompress) (K : MlKem) {stateBytes : Bytes} {e : LibsignalSpqrV1.Error}
    (h : Proto.spqrDecodeState stateBytes = .error e) :
    decodeState (spqrDeps F K) stateBytes = .error .stateDecode ∧ e = .stateDecode := by
  unfold Proto.spqrDecodeState at h
  unfold decodeState spqrDeps
  dsimp only
  split at h
  · contradiction
  · rename_i hne
    simp only [hne]
    unfold Proto.decodeState
    rcases hdec : PqRatchetState.decode stateBytes with _ | st
    · simp only [hdec, Except.error.injEq] at h
      exact ⟨rfl, h.symm⟩
    · simp [hdec] at h

theorem decodeState_spqrDeps_of_spqrDecodeState_ok
    (F : ShaCompress) (K : MlKem) {stateBytes : Bytes} {st : PqRatchetState}
    (h : Proto.spqrDecodeState stateBytes = .ok st) :
    decodeState (spqrDeps F K) stateBytes = .ok (pqRatchetStateToPb st) := by
  unfold Proto.spqrDecodeState at h
  unfold decodeState spqrDeps
  dsimp only
  split at h
  · rename_i hemp
    simp only [hemp]
    have hst : st = default := (Except.ok.inj h).symm
    subst hst
    rfl
  · rename_i hne
    simp only [hne]
    unfold Proto.decodeState
    rcases hdec : PqRatchetState.decode stateBytes with _ | st'
    · simp [hdec] at h
    · simp only [hdec, Except.ok.injEq] at h
      subst h
      rfl

/-! ## Phase 1 Early-Return Equations for `send` -/

theorem send_of_decodeState_error (D : SpqrApiDeps) (hkdf : HkdfFn)
    {stateBytes tape : Bytes} {e : LibsignalSpqrV1.Error}
    (hdec : decodeState D stateBytes = .error e) :
    LibsignalSpqrV1.send D hkdf stateBytes tape = (.error (.err e), tape) := by
  unfold LibsignalSpqrV1.send
  simp [hdec]

theorem send_of_inner_none (D : SpqrApiDeps) (hkdf : HkdfFn)
    {stateBytes tape : Bytes} {statePb : PqRatchetStatePB D.V1StatePB}
    (hdec : decodeState D stateBytes = .ok statePb)
    (hinner : statePb.inner = none) :
    LibsignalSpqrV1.send D hkdf stateBytes tape =
      (.ok { state := [], msg := [], key := none }, tape) := by
  unfold LibsignalSpqrV1.send
  simp [hdec, hinner]

theorem send_of_statesFromPb_error (D : SpqrApiDeps) (hkdf : HkdfFn)
    {stateBytes tape : Bytes} {statePb : PqRatchetStatePB D.V1StatePB}
    {pb : D.V1StatePB} {e : SpqrApiError}
    (hdec : decodeState D stateBytes = .ok statePb)
    (hinner : statePb.inner = some pb)
    (hfrom : D.statesFromPb pb = .error e) :
    LibsignalSpqrV1.send D hkdf stateBytes tape = (.error e, tape) := by
  unfold LibsignalSpqrV1.send
  simp [hdec, hinner, hfrom]

theorem send_of_statesFromPb_ok (D : SpqrApiDeps) (hkdf : HkdfFn)
    {stateBytes tape : Bytes} {statePb : PqRatchetStatePB D.V1StatePB}
    {pb : D.V1StatePB} {st0 : D.States}
    (hdec : decodeState D stateBytes = .ok statePb)
    (hinner : statePb.inner = some pb)
    (hfrom : D.statesFromPb pb = .ok st0) :
    LibsignalSpqrV1.send D hkdf stateBytes tape =
      let (sendRes, tape') := D.statesSend st0 tape
      match sendRes with
      | .error e => (.error e, tape')
      | .ok (msg, key, st1) => (sendAfterStates D hkdf statePb msg key st1, tape') := by
  unfold LibsignalSpqrV1.send
  simp only [hdec, hinner, hfrom]
  rfl

theorem spqrDeps_statesFromPb_of_err (F : ShaCompress) (K : MlKem)
    {pb : V1State} {e : LibsignalSpqrV1.Error}
    (h : States.from_pb spqrPolyApi (spqrAuthApi F) pb = .error (.err e)) :
    (spqrDeps F K).statesFromPb pb = .error (.err e) := by
  dsimp [spqrDeps]
  rw [h]; rfl

theorem spqrDeps_statesFromPb_of_panic (F : ShaCompress) (K : MlKem)
    {pb : V1State} {p : StatesPanic}
    (h : States.from_pb spqrPolyApi (spqrAuthApi F) pb = .error (.panic p)) :
    (spqrDeps F K).statesFromPb pb = .error (.panic .v1) := by
  dsimp [spqrDeps]
  rw [h]; rfl

theorem spqrDeps_statesFromPb_of_ok (F : ShaCompress) (K : MlKem)
    {pb : V1State} {st0 : States spqrPolyApi (spqrAuthApi F)}
    (h : States.from_pb spqrPolyApi (spqrAuthApi F) pb = .ok st0) :
    (spqrDeps F K).statesFromPb pb = .ok st0 := by
  dsimp [spqrDeps]
  rw [h]; rfl

/-! ## `v1StatePtsBound` from `stateBytes.length < 2 ^ 32` -/

private theorem list_le_sum_map {α : Type} (f : α → Nat) {x : α} {xs : List α}
    (hx : x ∈ xs) : f x ≤ (xs.map f).sum := by
  induction xs with
  | nil => contradiction
  | cons y ys ih =>
    simp only [List.map_cons, List.sum_cons]
    rcases List.mem_cons.mp hx with rfl | hmem
    · omega
    · have := ih hmem; omega

theorem optEncoderPtsBound_of_optRaw_lt {opt : Option PolynomialEncoder}
    (h : optRaw rawPolyEnc opt ≤ 2 * 0x0555555555555555) : optEncoderPtsBound opt := by
  cases opt with
  | none => trivial
  | some enc =>
    intro bs hbs
    simp only [optRaw_some, rawPolyEnc] at h
    have hle := list_le_sum_map (fun b : Bytes => b.length + 22) hbs
    omega

theorem v1StatePtsBound_of_rawV1State_lt {pb : V1State}
    (h : rawV1State pb ≤ 2 * 0x0555555555555555) : v1StatePtsBound pb := by
  unfold v1StatePtsBound rawV1State at *
  cases hinner : pb.innerState with
  | none => trivial
  | some is =>
    rw [hinner] at h
    rw [optRaw_some] at h
    cases is with
    | keysUnsampled _ | ekSentCt1Received _ | noHeaderReceived _
    | headerReceived _ | ct1Acknowledged _ => trivial
    | keysSampled s =>
      dsimp only [rawInnerState, rawChKeysSampled] at h
      exact optEncoderPtsBound_of_optRaw_lt (by omega)
    | headerSent s =>
      dsimp only [rawInnerState, rawChHeaderSent] at h
      exact optEncoderPtsBound_of_optRaw_lt (by omega)
    | ct1Received s =>
      dsimp only [rawInnerState, rawChCt1Received] at h
      exact optEncoderPtsBound_of_optRaw_lt (by omega)
    | ct1Sampled s =>
      dsimp only [rawInnerState, rawChCt1Sampled] at h
      exact optEncoderPtsBound_of_optRaw_lt (by omega)
    | ekReceivedCt1Sampled s =>
      dsimp only [rawInnerState, rawChEkReceivedCt1Sampled] at h
      exact optEncoderPtsBound_of_optRaw_lt (by omega)
    | ct2Sampled s =>
      dsimp only [rawInnerState, rawChCt2Sampled] at h
      exact optEncoderPtsBound_of_optRaw_lt (by omega)

theorem v1StatePtsBound_of_spqrDecodeState {F : ShaCompress} {K : MlKem}
    {stateBytes : Bytes} {st : PqRatchetState} {pb : V1State}
    (hlen : stateBytes.length < 2 ^ 32)
    (hdec : Proto.spqrDecodeState stateBytes = .ok st)
    (hinner : st.inner = some (.v1 pb)) :
    v1StatePtsBound pb := by
  have hd := decodeState_spqrDeps_of_spqrDecodeState_ok F K hdec
  have hraw := decodeState_spqrDeps_raw_le hd
  rw [pbToPqRatchetState_pqRatchetStateToPb] at hraw
  unfold rawPqState at hraw
  rw [hinner] at hraw
  simp only [optRaw_some, rawPqInner] at hraw
  apply v1StatePtsBound_of_rawV1State_lt
  omega

/-! ## `Message.serialize` Properties -/

theorem message_serialize_eq_cons {P : PolyApi} (m : Message P) (index : BitVec 32) :
    ∃ tail : Bytes, m.serialize index = 1#8 :: tail := by
  unfold Message.serialize
  cases m.payload <;>
    simp only [encode_chunk, encode_varint_eq_append, List.cons_append, List.nil_append] <;>
    exact ⟨_, rfl⟩

private theorem encode_chunk_length_le (epoch : Epoch) (index : BitVec 32) (b : BitVec 8)
    (c : spqrPolyApi.Chunk) :
    (encode_chunk c
      (encode_varint (index.zeroExtend 64) (encode_varint epoch [1#8]) ++ [b])).length ≤ 64 := by
  unfold encode_chunk
  have h1 := encode_varint_length_le epoch [1#8]
  have h2 := encode_varint_length_le (index.zeroExtend 64) (encode_varint epoch [1#8])
  have h3 := encode_varint_length_le ((spqrPolyApi.chunkIndex c).zeroExtend 64)
    (encode_varint (index.zeroExtend 64) (encode_varint epoch [1#8]) ++ [b])
  have hlen1 : ([1#8] : Bytes).length = 1 := rfl
  have hc : (spqrPolyApi.chunkData c).toList.length = 32 := List.Vector.toList_length _
  simp only [List.length_append, List.length_singleton, hc] at h3 ⊢
  omega

theorem message_serialize_length_le (m : Message spqrPolyApi) (index : BitVec 32) :
    (m.serialize index).length ≤ 64 := by
  rcases m with ⟨epoch, payload⟩
  unfold Message.serialize
  dsimp only
  have h1 := encode_varint_length_le epoch [1#8]
  have h2 := encode_varint_length_le (index.zeroExtend 64) (encode_varint epoch [1#8])
  have hlen1 : ([1#8] : Bytes).length = 1 := rfl
  cases payload with
  | none | ct1Ack _ =>
    simp only [List.length_append, List.length_singleton]
    omega
  | hdr c | ek c | ekCt1Ack c | ct1 c | ct2 c =>
    exact encode_chunk_length_le epoch index _ c

theorem message_serialize_length_lt_2_32 (m : Message spqrPolyApi) (index : BitVec 32) :
    (m.serialize index).length < 2 ^ 32 := by
  have := message_serialize_length_le m index
  omega

end CryptoVerification.SpqrV1.Top.Send
