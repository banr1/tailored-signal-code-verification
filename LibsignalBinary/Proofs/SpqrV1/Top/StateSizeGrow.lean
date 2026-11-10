/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Specifications.LibsignalSpqrV1.Init
public import LibsignalBinary.Proofs.SpqrV1.Top.StateSizeBase
import LibsignalBinary.Proofs.SpqrV1.Top.StateSize
import LibsignalBinary.Proofs.SpqrV1.Top.StateSizeStep
import LibsignalBinary.Proofs.SpqrV1Sync.Codec.PbState
import ProofLib.SepLogic.WP.StateNorm

/-!
# SPQR V1: One-Step State Size Growth Bounds for Valid States

Defines `ValidState` (either the V0 empty state `[]` or a canonical `Proto.encodeState st`
with `maxOooKeysOrDefault ≤ 2000`) and proves that one step of `send` or `recv` preserves
`ValidState` while growing the serialized state by at most `+ 1055000` bytes (`send`) or
`+ 1128000` bytes (`recv`), avoiding the `201 * s.length` decode slack and `2^32`-step
`keyAdvanceLoop` over-approximation of `StateSize.lean`.
-/

@[expose] public section

set_option autoImplicit false

namespace CryptoVerification.SpqrV1.Top.StateSize

open CryptoGames.LibsignalSession (SpqrDirection ShaCompress)
open CryptoGames.HKDF (Salt)
open CryptoVerification.LibsignalTripleRatchet (SpqrModel)
open CryptoVerification.LibsignalSpqrV1
open CryptoVerification.SpqrV1.ProtoRepr
open CryptoVerification.SpqrV1Sync.Codec (decodeState_spqrDeps_encodeState_pb)

@[simp] private theorem pure_bind_except {ε α β : Type} (x : α) (f : α → Except ε β) :
    (pure x >>= f) = f x := rfl

/-! ## Valid SPQR State Predicate (`ValidState`) -/

/-- A `ChainParamsPB` has valid out-of-order key limit (`≤ 2000`, matching `ChainParams.default`). -/
def ValidChainParams (p : ChainParamsPB) : Prop :=
  p.maxOooKeysOrDefault.toNat ≤ 2000

/-- A `PqRatchetState` is valid when any `ChainParamsPB` present in `versionNegotiation` or `chain`
satisfies `ValidChainParams`. -/
def ValidPqState (st : PqRatchetState) : Prop :=
  (∀ vn, st.versionNegotiation = some vn → ∀ p, vn.chainParams = some p → ValidChainParams p) ∧
  (∀ ch, st.chain = some ch → ∀ p, ch.params = some p → ValidChainParams p)

/-- A serialized SPQR state `s : Bytes` is valid if it is either the V0 empty state `[]` or the
canonical protobuf encoding `Proto.encodeState st` of a `ValidPqState st`.
Note that `ValidState` is a pure format predicate independent of `F` and `K`. -/
def ValidState (s : Bytes) : Prop :=
  s = [] ∨ ∃ st : PqRatchetState, s = Proto.encodeState st ∧ ValidPqState st

theorem validState_nil : ValidState [] := Or.inl rfl

/-- Any `ValidState s` can be written as `Proto.encodeState st` for some `ValidPqState st`
(since `[] = Proto.encodeState default`). -/
theorem ValidState.exists_encodeState {s : Bytes} (h : ValidState s) :
    ∃ st : PqRatchetState, s = Proto.encodeState st ∧ ValidPqState st := by
  rcases h with rfl | h
  · refine ⟨default, rfl, ?_, ?_⟩ <;> (intro _ h0; cases h0)
  · exact h

theorem validState_spqrV1Init (F : ShaCompress) (K : MlKem) (dir : SpqrDirection) (k : BitVec 256) :
    ValidState (spqrV1Init F K dir k) := by
  cases dir <;> refine Or.inr ⟨_, rfl, ?_, by intro _ hch; cases hch⟩ <;> {
    intro vn hvn p hp; cases hvn; cases hp; dsimp [libsignalSpqrParams, ValidChainParams]; decide
  }

/-! ## Primitive Wire Encoding and `raw*` Lower Bounds -/

theorem length_le_encodeBytesUncond (tag : BitVec 32) (v : Bytes) :
    v.length ≤ (Proto.encodeBytesUncond tag v).length := by
  unfold Proto.encodeBytesUncond; simp only [List.length_append]; omega

theorem length_le_encodeBytesField (tag : BitVec 32) (v : Bytes) :
    v.length ≤ (Proto.encodeBytesField tag v).length := by
  unfold Proto.encodeBytesField; split
  · rename_i h; cases v with | nil => rfl | cons _ _ => contradiction
  · exact length_le_encodeBytesUncond tag v

theorem length_le_encodeMessage {M : Type} (encodeRaw : M → Bytes) (tag : BitVec 32) (m : M) :
    (encodeRaw m).length ≤ (Proto.encodeMessage encodeRaw tag m).length := by
  unfold Proto.encodeMessage; simp only [List.length_append]; omega

theorem length_le_encodeOptMessage {M : Type} (encodeRaw : M → Bytes) (f : M → Nat)
    (hle : ∀ m, f m ≤ (encodeRaw m).length) (tag : BitVec 32) (opt : Option M) :
    optRaw f opt ≤ (Proto.encodeOptMessage encodeRaw tag opt).length := by
  cases opt with
  | none => simp [Proto.encodeOptMessage]
  | some m => simp only [Proto.encodeOptMessage, optRaw_some]; exact Nat.le_trans (hle m) (length_le_encodeMessage encodeRaw tag m)

theorem sum_length_le_encodeRepeatedBytes (tag : BitVec 32) (vs : List Bytes) :
    (vs.map List.length).sum ≤ (Proto.encodeRepeatedBytes tag vs).length := by
  induction vs with
  | nil => simp [Proto.encodeRepeatedBytes]
  | cons v rest ih =>
    simp only [Proto.encodeRepeatedBytes, List.foldr_cons, List.length_append, List.map_cons, List.sum_cons]
    have h1 := length_le_encodeBytesUncond tag v
    have h2 : (rest.map List.length).sum ≤ (List.foldr (fun v acc => Proto.encodeBytesUncond tag v ++ acc) [] rest).length := ih
    omega

theorem sum_map_length_add_const (vs : List Bytes) (c : Nat) :
    (vs.map (fun b => b.length + c)).sum = (vs.map List.length).sum + c * vs.length := by
  induction vs with
  | nil => simp
  | cons v rest ih => simp only [List.map_cons, List.sum_cons, List.length_cons, ih, Nat.mul_add, Nat.mul_one]; omega

theorem rawEpochDir_le_encodeRaw (m : EpochDirectionPB) :
    rawEpochDir m ≤ (EpochDirectionPB.encodeRaw m).length := by
  unfold EpochDirectionPB.encodeRaw rawEpochDir; simp only [List.length_append]
  have h1 := length_le_encodeBytesField 2#32 m.next; have h2 := length_le_encodeBytesField 3#32 m.prev; omega

theorem rawChainEpoch_le_encodeRaw (m : ChainEpochPB) :
    rawChainEpoch m ≤ (ChainEpochPB.encodeRaw m).length := by
  unfold ChainEpochPB.encodeRaw rawChainEpoch; rw [List.length_append]
  have h1 := length_le_encodeOptMessage EpochDirectionPB.encodeRaw rawEpochDir rawEpochDir_le_encodeRaw 1#32 m.send
  have h2 := length_le_encodeOptMessage EpochDirectionPB.encodeRaw rawEpochDir rawEpochDir_le_encodeRaw 2#32 m.recv; omega

theorem rawAuth_le_encodeRaw (m : ProtoAuthenticator) :
    rawAuth m ≤ (ProtoAuthenticator.encodeRaw m).length := by
  unfold ProtoAuthenticator.encodeRaw rawAuth; rw [List.length_append]
  have h1 := length_le_encodeBytesField 1#32 m.rootKey; have h2 := length_le_encodeBytesField 2#32 m.macKey; omega

theorem rawPolyEnc_le_encodeRaw (m : PolynomialEncoder) :
    rawPolyEnc m ≤ (PolynomialEncoder.encodeRaw m).length + 22 * (m.pts.length + m.polys.length) := by
  unfold PolynomialEncoder.encodeRaw rawPolyEnc; simp only [List.length_append]
  rw [sum_map_length_add_const m.pts 22, sum_map_length_add_const m.polys 22]
  have h1 := sum_length_le_encodeRepeatedBytes 2#32 m.pts; have h2 := sum_length_le_encodeRepeatedBytes 3#32 m.polys
  rw [Nat.mul_add]; omega

theorem rawPolyDec_le_encodeRaw (m : PolynomialDecoder) :
    rawPolyDec m ≤ (PolynomialDecoder.encodeRaw m).length + 22 * m.pts.length := by
  unfold PolynomialDecoder.encodeRaw rawPolyDec; simp only [List.length_append]
  rw [sum_map_length_add_const m.pts 22]; have h1 := sum_length_le_encodeRepeatedBytes 3#32 m.pts; omega

theorem rawUcKeysUnsampled_le_encodeRaw (m : V1State.Unchunked.KeysUnsampled) :
    rawUcKeysUnsampled m ≤ (V1State.Unchunked.KeysUnsampled.encodeRaw m).length := by
  unfold V1State.Unchunked.KeysUnsampled.encodeRaw rawUcKeysUnsampled; rw [List.length_append]
  have h1 := length_le_encodeOptMessage ProtoAuthenticator.encodeRaw rawAuth rawAuth_le_encodeRaw 2#32 m.auth; omega

theorem rawUcHeaderSent_le_encodeRaw (m : V1State.Unchunked.HeaderSent) :
    rawUcHeaderSent m ≤ (V1State.Unchunked.HeaderSent.encodeRaw m).length := by
  unfold V1State.Unchunked.HeaderSent.encodeRaw rawUcHeaderSent; simp only [List.length_append]
  have h1 := length_le_encodeOptMessage ProtoAuthenticator.encodeRaw rawAuth rawAuth_le_encodeRaw 2#32 m.auth
  have h2 := length_le_encodeBytesField 3#32 m.ek; have h3 := length_le_encodeBytesField 4#32 m.dk; omega

theorem rawUcEkSent_le_encodeRaw (m : V1State.Unchunked.EkSent) :
    rawUcEkSent m ≤ (V1State.Unchunked.EkSent.encodeRaw m).length := by
  unfold V1State.Unchunked.EkSent.encodeRaw rawUcEkSent; simp only [List.length_append]
  have h1 := length_le_encodeOptMessage ProtoAuthenticator.encodeRaw rawAuth rawAuth_le_encodeRaw 2#32 m.auth
  have h2 := length_le_encodeBytesField 3#32 m.dk; omega

theorem rawUcEkSentCt1Received_le_encodeRaw (m : V1State.Unchunked.EkSentCt1Received) :
    rawUcEkSentCt1Received m ≤ (V1State.Unchunked.EkSentCt1Received.encodeRaw m).length := by
  unfold V1State.Unchunked.EkSentCt1Received.encodeRaw rawUcEkSentCt1Received; simp only [List.length_append]
  have h1 := length_le_encodeOptMessage ProtoAuthenticator.encodeRaw rawAuth rawAuth_le_encodeRaw 2#32 m.auth
  have h2 := length_le_encodeBytesField 3#32 m.dk; have h3 := length_le_encodeBytesField 4#32 m.ct1; omega

theorem rawUcNoHeaderReceived_le_encodeRaw (m : V1State.Unchunked.NoHeaderReceived) :
    rawUcNoHeaderReceived m ≤ (V1State.Unchunked.NoHeaderReceived.encodeRaw m).length := by
  unfold V1State.Unchunked.NoHeaderReceived.encodeRaw rawUcNoHeaderReceived; rw [List.length_append]
  have h1 := length_le_encodeOptMessage ProtoAuthenticator.encodeRaw rawAuth rawAuth_le_encodeRaw 2#32 m.auth; omega

theorem rawUcHeaderReceived_le_encodeRaw (m : V1State.Unchunked.HeaderReceived) :
    rawUcHeaderReceived m ≤ (V1State.Unchunked.HeaderReceived.encodeRaw m).length := by
  unfold V1State.Unchunked.HeaderReceived.encodeRaw rawUcHeaderReceived; simp only [List.length_append]
  have h1 := length_le_encodeOptMessage ProtoAuthenticator.encodeRaw rawAuth rawAuth_le_encodeRaw 2#32 m.auth
  have h2 := length_le_encodeBytesField 3#32 m.hdr; omega

theorem rawUcCt1Sent_le_encodeRaw (m : V1State.Unchunked.Ct1Sent) :
    rawUcCt1Sent m ≤ (V1State.Unchunked.Ct1Sent.encodeRaw m).length := by
  unfold V1State.Unchunked.Ct1Sent.encodeRaw rawUcCt1Sent; simp only [List.length_append]
  have h1 := length_le_encodeOptMessage ProtoAuthenticator.encodeRaw rawAuth rawAuth_le_encodeRaw 2#32 m.auth
  have h2 := length_le_encodeBytesField 3#32 m.hdr; have h3 := length_le_encodeBytesField 4#32 m.es
  have h4 := length_le_encodeBytesField 5#32 m.ct1; omega

theorem rawUcCt1SentEkReceived_le_encodeRaw (m : V1State.Unchunked.Ct1SentEkReceived) :
    rawUcCt1SentEkReceived m ≤ (V1State.Unchunked.Ct1SentEkReceived.encodeRaw m).length := by
  unfold V1State.Unchunked.Ct1SentEkReceived.encodeRaw rawUcCt1SentEkReceived; simp only [List.length_append]
  have h1 := length_le_encodeOptMessage ProtoAuthenticator.encodeRaw rawAuth rawAuth_le_encodeRaw 2#32 m.auth
  have h2 := length_le_encodeBytesField 3#32 m.es; have h3 := length_le_encodeBytesField 4#32 m.ek
  have h4 := length_le_encodeBytesField 5#32 m.ct1; omega

theorem rawUcCt2Sent_le_encodeRaw (m : V1State.Unchunked.Ct2Sent) :
    rawUcCt2Sent m ≤ (V1State.Unchunked.Ct2Sent.encodeRaw m).length := by
  unfold V1State.Unchunked.Ct2Sent.encodeRaw rawUcCt2Sent; rw [List.length_append]
  have h1 := length_le_encodeOptMessage ProtoAuthenticator.encodeRaw rawAuth rawAuth_le_encodeRaw 2#32 m.auth; omega

/-! ## `States.from_pb` Lower Bound Relative to `V1State` Wire Length -/

theorem PolyDecoder.fromPb_pts_len {pb : PolynomialDecoder} {dec : PolyDecoder}
    (h : PolyDecoder.fromPb (pbToProtoPolyDecoder pb) = .ok (.ok dec)) : pb.pts.length = 16 := by
  unfold PolyDecoder.fromPb pbToProtoPolyDecoder at h; dsimp only [] at h; split at h
  · simp [pure, Except.pure] at h
  · rename_i hne; exact bne_eq_false_iff_eq.mp (Bool.not_eq_true _ ▸ hne)

theorem decoderFromPbStateDecode_raw_le_encode {pb? : Option PolynomialDecoder} {dec : PolyDecoder}
    (tag : BitVec 32) (h : decoderFromPbStateDecode spqrPolyApi pb? = .ok dec) :
    optRaw rawPolyDec pb? ≤ (Proto.encodeOptMessage PolynomialDecoder.encodeRaw tag pb?).length + 352 := by
  unfold decoderFromPbStateDecode spqrPolyApi at h; cases pb? with
  | none => contradiction
  | some pb =>
    dsimp only [] at h; rcases except_bind_eq_ok h with ⟨res, h1, h2⟩
    have h1' : PolyDecoder.fromPb (pbToProtoPolyDecoder pb) = .ok res := by
      cases hr : PolyDecoder.fromPb (pbToProtoPolyDecoder pb) <;> simp [hr, StatesResult.ofPanic, Except.mapError] at h1; exact h1 ▸ rfl
    cases res with
    | error _ => contradiction
    | ok _ =>
      have hlen := PolyDecoder.fromPb_pts_len h1'; have hraw := rawPolyDec_le_encodeRaw pb
      have hmsg := length_le_encodeMessage PolynomialDecoder.encodeRaw tag pb
      simp only [Proto.encodeOptMessage, optRaw_some]; omega

theorem PolyEncoder.fromPb_pts_polys_len {pb : PolynomialEncoder} {enc : PolyEncoder}
    (h : PolyEncoder.fromPb (pbToProtoPolyEncoder pb) = .ok (.ok enc)) :
    pb.pts.length + pb.polys.length = 16 := by
  unfold PolyEncoder.fromPb pbToProtoPolyEncoder NUM_POLYS at h; dsimp only [] at h; split at h
  · rename_i hpts_ne; split at h
    · simp [pure, Except.pure] at h
    · rename_i hpolys_emp; split at h
      · simp [pure, Except.pure] at h
      · rename_i hpts_len
        have h1 : pb.pts.length = 16 := bne_eq_false_iff_eq.mp (Bool.not_eq_true _ ▸ hpts_len)
        simp at hpolys_emp; simp [h1, hpolys_emp]
  · rename_i hpts_emp; split at h
    · rename_i hpolys_len; simp at hpts_emp
      have h2 : pb.polys.length = 16 := beq_iff_eq.mp hpolys_len; simp [hpts_emp, h2]
    · simp [pure, Except.pure] at h

theorem encoderFromPbStateDecode_raw_le_encode {pb? : Option PolynomialEncoder} {enc : PolyEncoder}
    (tag : BitVec 32) (h : encoderFromPbStateDecode spqrPolyApi pb? = .ok enc) :
    optRaw rawPolyEnc pb? ≤ (Proto.encodeOptMessage PolynomialEncoder.encodeRaw tag pb?).length + 352 := by
  unfold encoderFromPbStateDecode spqrPolyApi at h; cases pb? with
  | none => contradiction
  | some pb =>
    dsimp only [] at h; rcases except_bind_eq_ok h with ⟨res, h1, h2⟩
    have h1' : PolyEncoder.fromPb (pbToProtoPolyEncoder pb) = .ok res := by
      cases hr : PolyEncoder.fromPb (pbToProtoPolyEncoder pb) <;> simp [hr, StatesResult.ofPanic, Except.mapError] at h1; exact h1 ▸ rfl
    cases res with
    | error _ => contradiction
    | ok _ =>
      have hlen := PolyEncoder.fromPb_pts_polys_len h1'; have hraw := rawPolyEnc_le_encodeRaw pb
      have hmsg := length_le_encodeMessage PolynomialEncoder.encodeRaw tag pb
      simp only [Proto.encodeOptMessage, optRaw_some]; omega

set_option maxHeartbeats 400000 in
theorem States.from_pb_rawV1State_le_encode {F : ShaCompress} {pb : V1State}
    {st : States spqrPolyApi (spqrAuthApi F)}
    (h : States.from_pb spqrPolyApi (spqrAuthApi F) pb = .ok st) :
    rawV1State pb ≤ (Proto.encodeMessage V1State.encodeRaw 3#32 pb).length + 704 := by
  have hmsg := length_le_encodeMessage V1State.encodeRaw 3#32 pb
  unfold States.from_pb at h; cases hinner : pb.innerState with
  | none => rw [hinner] at h; contradiction
  | some inner =>
    rw [hinner] at h
    have hinner_eq : (V1State.encodeRaw pb).length = (V1State.InnerState.encode inner).length := by simp [V1State.encodeRaw, hinner]
    have hraw_eq : rawV1State pb = rawInnerState inner := by simp [rawV1State, hinner]
    rw [hraw_eq]; cases inner with
    | keysUnsampled s =>
      have h0 := length_le_encodeMessage V1State.Chunked.KeysUnsampled.encodeRaw 1#32 s
      have h1 := length_le_encodeOptMessage _ rawUcKeysUnsampled rawUcKeysUnsampled_le_encodeRaw 1#32 s.uc
      dsimp only [V1State.InnerState.encode, V1State.Chunked.KeysUnsampled.encodeRaw, rawInnerState, rawChKeysUnsampled] at h0 hinner_eq ⊢; omega
    | keysSampled s =>
      dsimp only [Functor.map, Except.map] at h; split at h <;> try contradiction
      rename_i v hv; unfold Chunked.SendEk.KeysSampled.from_pb at hv; cases huc : s.uc with
      | none => rw [huc] at hv; contradiction
      | some u =>
        rw [huc] at hv; dsimp only [Bind.bind, Except.bind] at hv
        rcases except_bind_eq_ok hv with ⟨_, _, hv2⟩; rcases except_bind_eq_ok hv2 with ⟨_, henc, _⟩
        have h0 := length_le_encodeMessage V1State.Chunked.KeysSampled.encodeRaw 2#32 s
        have h1 := length_le_encodeOptMessage _ rawUcHeaderSent rawUcHeaderSent_le_encodeRaw 1#32 s.uc
        have h2 := encoderFromPbStateDecode_raw_le_encode 2#32 henc
        dsimp only [V1State.InnerState.encode, V1State.Chunked.KeysSampled.encodeRaw, rawInnerState, rawChKeysSampled] at h0 hinner_eq ⊢; rw [List.length_append] at h0; omega
    | headerSent s =>
      dsimp only [Functor.map, Except.map] at h; split at h <;> try contradiction
      rename_i v hv; unfold Chunked.SendEk.HeaderSent.from_pb at hv
      have hchk : ∀ d, s.receivingCt1 = some d → d.ptsNeeded.toNat = CIPHERTEXT1_SIZE / 2 := by
        intro d hd; rw [hd] at hv; dsimp only [] at hv; by_contra hne; rw [bne_iff_ne.mpr hne] at hv; contradiction
      cases hrec : s.receivingCt1 with
      | none =>
        rw [hrec] at hv; dsimp only [Bind.bind, Except.bind] at hv; cases huc : s.uc with
        | none => rw [huc] at hv; contradiction
        | some u =>
          rw [huc] at hv; dsimp only [Bind.bind, Except.bind] at hv
          rcases except_bind_eq_ok hv with ⟨_, _, hv2⟩; rcases except_bind_eq_ok hv2 with ⟨_, _, hv3⟩; contradiction
      | some d0 =>
        have hfls : (d0.ptsNeeded.toNat != CIPHERTEXT1_SIZE / 2) = false := bne_eq_false_iff_eq.mpr (hchk d0 hrec)
        rw [hrec] at hv; dsimp only [] at hv; rw [hfls] at hv; cases huc : s.uc with
        | none => rw [huc] at hv; contradiction
        | some u =>
          rw [huc] at hv; dsimp only [Bind.bind, Except.bind] at hv
          rcases except_bind_eq_ok hv with ⟨_, _, hv2⟩; rcases except_bind_eq_ok hv2 with ⟨_, henc, hv3⟩
          rcases except_bind_eq_ok hv3 with ⟨_, hdec, _⟩
          have h0 := length_le_encodeMessage V1State.Chunked.HeaderSent.encodeRaw 3#32 s
          have h1 := length_le_encodeOptMessage _ rawUcEkSent rawUcEkSent_le_encodeRaw 1#32 s.uc
          have h2 := encoderFromPbStateDecode_raw_le_encode 2#32 henc
          have h3 := decoderFromPbStateDecode_raw_le_encode 3#32 (hrec.symm ▸ hdec)
          dsimp only [V1State.InnerState.encode, V1State.Chunked.HeaderSent.encodeRaw, rawInnerState, rawChHeaderSent] at h0 hinner_eq ⊢; simp only [List.length_append] at h0; omega
    | ct1Received s =>
      dsimp only [Functor.map, Except.map] at h; split at h <;> try contradiction
      rename_i v hv; unfold Chunked.SendEk.Ct1Received.from_pb at hv; cases huc : s.uc with
      | none => rw [huc] at hv; contradiction
      | some u =>
        rw [huc] at hv; dsimp only [Bind.bind, Except.bind] at hv
        rcases except_bind_eq_ok hv with ⟨_, _, hv2⟩; rcases except_bind_eq_ok hv2 with ⟨_, henc, _⟩
        have h0 := length_le_encodeMessage V1State.Chunked.Ct1Received.encodeRaw 4#32 s
        have h1 := length_le_encodeOptMessage _ rawUcEkSentCt1Received rawUcEkSentCt1Received_le_encodeRaw 1#32 s.uc
        have h2 := encoderFromPbStateDecode_raw_le_encode 2#32 henc
        dsimp only [V1State.InnerState.encode, V1State.Chunked.Ct1Received.encodeRaw, rawInnerState, rawChCt1Received] at h0 hinner_eq ⊢; rw [List.length_append] at h0; omega
    | ekSentCt1Received s =>
      dsimp only [Functor.map, Except.map] at h; split at h <;> try contradiction
      rename_i v hv; unfold Chunked.SendEk.EkSentCt1Received.from_pb at hv; dsimp only [Bind.bind, Except.bind] at hv; cases huc : s.uc with
      | none => rw [huc] at hv; split at hv <;> [split at hv <;> contradiction; contradiction]
      | some u =>
        rw [huc] at hv
        have hbody : (do let uc ← Unchunked.SendEk.EkSentCt1Received.from_pb (spqrAuthApi F) u; let receivingCt2 ← decoderFromPbStateDecode spqrPolyApi s.receivingCt2; Except.ok { uc := uc, receiving_ct2 := receivingCt2 }) = Except.ok v := by
          split at hv <;> [split at hv <;> [contradiction; exact hv]; exact hv]
        rcases except_bind_eq_ok hbody with ⟨_, _, hv2⟩; rcases except_bind_eq_ok hv2 with ⟨_, hdec, _⟩
        have h0 := length_le_encodeMessage V1State.Chunked.EkSentCt1Received.encodeRaw 5#32 s
        have h1 := length_le_encodeOptMessage _ rawUcEkSentCt1Received rawUcEkSentCt1Received_le_encodeRaw 1#32 s.uc
        have h2 := decoderFromPbStateDecode_raw_le_encode 3#32 hdec
        dsimp only [V1State.InnerState.encode, V1State.Chunked.EkSentCt1Received.encodeRaw, rawInnerState, rawChEkSentCt1Received] at h0 hinner_eq ⊢; rw [List.length_append] at h0; omega
    | noHeaderReceived s =>
      dsimp only [Functor.map, Except.map] at h; split at h <;> try contradiction
      rename_i v hv; unfold Chunked.SendCt.NoHeaderReceived.from_pb at hv; dsimp only [Bind.bind, Except.bind] at hv; cases huc : s.uc with
      | none => rw [huc] at hv; split at hv <;> [split at hv <;> contradiction; contradiction]
      | some u =>
        rw [huc] at hv
        have hbody : (do let uc ← Unchunked.SendCt.NoHeaderReceived.from_pb (spqrAuthApi F) u; let receivingHdr ← decoderFromPbStateDecode spqrPolyApi s.receivingHdr; Except.ok { uc := uc, receiving_hdr := receivingHdr }) = Except.ok v := by
          split at hv <;> [split at hv <;> [contradiction; exact hv]; exact hv]
        rcases except_bind_eq_ok hbody with ⟨_, _, hv2⟩; rcases except_bind_eq_ok hv2 with ⟨_, hdec, _⟩
        have h0 := length_le_encodeMessage V1State.Chunked.NoHeaderReceived.encodeRaw 6#32 s
        have h1 := length_le_encodeOptMessage _ rawUcNoHeaderReceived rawUcNoHeaderReceived_le_encodeRaw 1#32 s.uc
        have h2 := decoderFromPbStateDecode_raw_le_encode 2#32 hdec
        dsimp only [V1State.InnerState.encode, V1State.Chunked.NoHeaderReceived.encodeRaw, rawInnerState, rawChNoHeaderReceived] at h0 hinner_eq ⊢; rw [List.length_append] at h0; omega
    | headerReceived s =>
      dsimp only [Functor.map, Except.map] at h; split at h <;> try contradiction
      rename_i v hv; unfold Chunked.SendCt.HeaderReceived.from_pb at hv; dsimp only [Bind.bind, Except.bind] at hv; cases huc : s.uc with
      | none => rw [huc] at hv; split at hv <;> [split at hv <;> contradiction; contradiction]
      | some u =>
        rw [huc] at hv
        have hbody : (do let uc ← Unchunked.SendCt.HeaderReceived.from_pb (spqrAuthApi F) u; let receivingEk ← decoderFromPbStateDecode spqrPolyApi s.receivingEk; Except.ok { uc := uc, receiving_ek := receivingEk }) = Except.ok v := by
          split at hv <;> [split at hv <;> [contradiction; exact hv]; exact hv]
        rcases except_bind_eq_ok hbody with ⟨_, _, hv2⟩; rcases except_bind_eq_ok hv2 with ⟨_, hdec, _⟩
        have h0 := length_le_encodeMessage V1State.Chunked.HeaderReceived.encodeRaw 7#32 s
        have h1 := length_le_encodeOptMessage _ rawUcHeaderReceived rawUcHeaderReceived_le_encodeRaw 1#32 s.uc
        have h2 := decoderFromPbStateDecode_raw_le_encode 2#32 hdec
        dsimp only [V1State.InnerState.encode, V1State.Chunked.HeaderReceived.encodeRaw, rawInnerState, rawChHeaderReceived] at h0 hinner_eq ⊢; rw [List.length_append] at h0; omega
    | ct1Sampled s =>
      dsimp only [Functor.map, Except.map] at h; split at h <;> try contradiction
      rename_i v hv; unfold Chunked.SendCt.Ct1Sampled.from_pb at hv; dsimp only [Bind.bind, Except.bind] at hv; cases huc : s.uc with
      | none => rw [huc] at hv; split at hv <;> [split at hv <;> contradiction; contradiction]
      | some u =>
        rw [huc] at hv
        have hbody : (do let uc ← Unchunked.SendCt.Ct1Sent.from_pb (spqrAuthApi F) u; let sendingCt1 ← encoderFromPbStateDecode spqrPolyApi s.sendingCt1; let receivingEk ← decoderFromPbStateDecode spqrPolyApi s.receivingEk; Except.ok { uc := uc, sending_ct1 := sendingCt1, receiving_ek := receivingEk }) = Except.ok v := by
          split at hv <;> [split at hv <;> [contradiction; exact hv]; exact hv]
        rcases except_bind_eq_ok hbody with ⟨_, _, hv2⟩; rcases except_bind_eq_ok hv2 with ⟨_, henc, hv3⟩
        rcases except_bind_eq_ok hv3 with ⟨_, hdec, _⟩
        have h0 := length_le_encodeMessage V1State.Chunked.Ct1Sampled.encodeRaw 8#32 s
        have h1 := length_le_encodeOptMessage _ rawUcCt1Sent rawUcCt1Sent_le_encodeRaw 1#32 s.uc
        have h2 := encoderFromPbStateDecode_raw_le_encode 2#32 henc
        have h3 := decoderFromPbStateDecode_raw_le_encode 3#32 hdec
        dsimp only [V1State.InnerState.encode, V1State.Chunked.Ct1Sampled.encodeRaw, rawInnerState, rawChCt1Sampled] at h0 hinner_eq ⊢; simp only [List.length_append] at h0; omega
    | ekReceivedCt1Sampled s =>
      dsimp only [Functor.map, Except.map] at h; split at h <;> try contradiction
      rename_i v hv; unfold Chunked.SendCt.EkReceivedCt1Sampled.from_pb at hv; cases huc : s.uc with
      | none => rw [huc] at hv; contradiction
      | some u =>
        rw [huc] at hv; dsimp only [Bind.bind, Except.bind] at hv
        rcases except_bind_eq_ok hv with ⟨_, _, hv2⟩; rcases except_bind_eq_ok hv2 with ⟨_, henc, _⟩
        have h0 := length_le_encodeMessage V1State.Chunked.EkReceivedCt1Sampled.encodeRaw 9#32 s
        have h1 := length_le_encodeOptMessage _ rawUcCt1SentEkReceived rawUcCt1SentEkReceived_le_encodeRaw 1#32 s.uc
        have h2 := encoderFromPbStateDecode_raw_le_encode 2#32 henc
        dsimp only [V1State.InnerState.encode, V1State.Chunked.EkReceivedCt1Sampled.encodeRaw, rawInnerState, rawChEkReceivedCt1Sampled] at h0 hinner_eq ⊢; rw [List.length_append] at h0; omega
    | ct1Acknowledged s =>
      dsimp only [Functor.map, Except.map] at h; split at h <;> try contradiction
      rename_i v hv; unfold Chunked.SendCt.Ct1Acknowledged.from_pb at hv; dsimp only [Bind.bind, Except.bind] at hv; cases huc : s.uc with
      | none => rw [huc] at hv; split at hv <;> [split at hv <;> contradiction; contradiction]
      | some u =>
        rw [huc] at hv
        have hbody : (do let uc ← Unchunked.SendCt.Ct1Sent.from_pb (spqrAuthApi F) u; let receivingEk ← decoderFromPbStateDecode spqrPolyApi s.receivingEk; Except.ok { uc := uc, receiving_ek := receivingEk }) = Except.ok v := by
          split at hv <;> [split at hv <;> [contradiction; exact hv]; exact hv]
        rcases except_bind_eq_ok hbody with ⟨_, _, hv2⟩; rcases except_bind_eq_ok hv2 with ⟨_, hdec, _⟩
        have h0 := length_le_encodeMessage V1State.Chunked.Ct1Acknowledged.encodeRaw 10#32 s
        have h1 := length_le_encodeOptMessage _ rawUcCt1Sent rawUcCt1Sent_le_encodeRaw 1#32 s.uc
        have h2 := decoderFromPbStateDecode_raw_le_encode 2#32 hdec
        dsimp only [V1State.InnerState.encode, V1State.Chunked.Ct1Acknowledged.encodeRaw, rawInnerState, rawChCt1Acknowledged] at h0 hinner_eq ⊢; rw [List.length_append] at h0; omega
    | ct2Sampled s =>
      dsimp only [Functor.map, Except.map] at h; split at h <;> try contradiction
      rename_i v hv; unfold Chunked.SendCt.Ct2Sampled.from_pb at hv; cases huc : s.uc with
      | none => rw [huc] at hv; contradiction
      | some u =>
        rw [huc] at hv; dsimp only [Bind.bind, Except.bind] at hv
        rcases except_bind_eq_ok hv with ⟨_, _, hv2⟩; rcases except_bind_eq_ok hv2 with ⟨_, henc, _⟩
        have h0 := length_le_encodeMessage V1State.Chunked.Ct2Sampled.encodeRaw 11#32 s
        have h1 := length_le_encodeOptMessage _ rawUcCt2Sent rawUcCt2Sent_le_encodeRaw 1#32 s.uc
        have h2 := encoderFromPbStateDecode_raw_le_encode 2#32 henc
        dsimp only [V1State.InnerState.encode, V1State.Chunked.Ct2Sampled.encodeRaw, rawInnerState, rawChCt2Sampled] at h0 hinner_eq ⊢; rw [List.length_append] at h0; omega

/-! ## Tight `keyAdvanceLoop` OOO Bound and `chainWireCore` Transition Bounds -/

theorem ChainEpochDirection.keyAdvanceLoop_length_le_ooo (hkdf : HkdfFn) (ed : ChainEpochDirection)
    (atIdx : BitVec 32) (params : ChainParamsPB) {ed' : ChainEpochDirection}
    (h : ed.keyAdvanceLoop hkdf atIdx params = .ok ed') :
    ed'.next.length ≤ max ed.next.length 32 ∧
      ed'.prev.data.length ≤ ed.prev.data.length +
        36 * min (atIdx.toNat - 1 - ed.ctr.toNat) params.maxOooKeysOrDefault.toNat := by
  suffices ∀ n (ed : ChainEpochDirection), atIdx.toNat - ed.ctr.toNat ≤ n →
      ed.keyAdvanceLoop hkdf atIdx params = .ok ed' →
      ed'.next.length ≤ max ed.next.length 32 ∧
        ed'.prev.data.length ≤ ed.prev.data.length +
          36 * min (atIdx.toNat - 1 - ed.ctr.toNat) params.maxOooKeysOrDefault.toNat from
    this (atIdx.toNat - ed.ctr.toNat) ed (Nat.le_refl _) h
  intro n; induction n with
  | zero =>
    intro ed hn h; unfold ChainEpochDirection.keyAdvanceLoop at h; split at h
    · omega
    · split at h <;> [contradiction; (simp only [Except.ok.injEq] at h; subst h; exact ⟨by omega, by omega⟩)]
  | succ n ih =>
    intro ed hn h; unfold ChainEpochDirection.keyAdvanceLoop at h; split at h
    · rename_i hlt; split at h <;> [contradiction; skip]
      rename_i next' ctr' k hnk
      have hctr' := ChainEpochDirection.nextKeyInternal_ctr hkdf ed.next next' ed.ctr ctr' k hnk
      dsimp only [] at h; split at h <;> [contradiction; skip]
      obtain ⟨hnk1, hnk2⟩ := ChainEpochDirection.nextKeyInternal_length_le hkdf ed.next ed.ctr hnk
      obtain ⟨ihn, ihp⟩ := ih _ (by dsimp only []; omega) h
      dsimp only [] at ihn ihp; refine ⟨by omega, ?_⟩
      by_cases hcond : ctr' + params.maxOooKeysOrDefault ≥ atIdx
      · simp only [hcond, ↓reduceIte] at ihp
        have hadd := KeyHistory.add_length_le ed.prev k params hnk2
        have hle_at : atIdx.toNat ≤ ctr'.toNat + params.maxOooKeysOrDefault.toNat := by
          have hle_bv := (BitVec.le_def).mp hcond
          rw [BitVec.toNat_add, Nat.mod_eq_of_lt (by omega)] at hle_bv; exact hle_bv
        have hmin : min (atIdx.toNat - 1 - ed.ctr.toNat) params.maxOooKeysOrDefault.toNat =
            min (atIdx.toNat - 1 - ctr'.toNat) params.maxOooKeysOrDefault.toNat + 1 := by omega
        rw [hmin, Nat.mul_add]; omega
      · simp only [hcond, ↓reduceIte] at ihp
        have hmin : min (atIdx.toNat - 1 - ctr'.toNat) params.maxOooKeysOrDefault.toNat ≤
            min (atIdx.toNat - 1 - ed.ctr.toNat) params.maxOooKeysOrDefault.toNat := by omega
        have hmul := Nat.mul_le_mul_left 36 hmin; omega
    · split at h <;> [contradiction; (simp only [Except.ok.injEq] at h; subst h; exact ⟨by omega, by omega⟩)]

theorem ChainEpochDirection.key_raw_le_ooo (hkdf : HkdfFn) (ed : ChainEpochDirection)
    (atIdx : BitVec 32) (params : ChainParamsPB) {ed' : ChainEpochDirection} {out : Bytes}
    (h : ed.key hkdf atIdx params = .ok (ed', out)) :
    rawEpochDir ed'.intoPb ≤ rawEpochDir ed.intoPb + 32 + 36 * params.maxOooKeysOrDefault.toNat := by
  unfold ChainEpochDirection.key at h; dsimp only [] at h; split at h
  · rcases hget : ed.prev.get atIdx ed.ctr params with e | ⟨prev', out'⟩
    · simp [hget, Bind.bind, Except.bind] at h
    · simp only [hget, Bind.bind, Except.bind, pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at h
      rcases h with ⟨rfl, rfl⟩
      have hp := KeyHistory.get_length_le ed.prev atIdx ed.ctr params hget
      simp only [ChainEpochDirection.intoPb, rawEpochDir]; omega
  · split at h <;> [contradiction; skip]; split at h <;> [contradiction; skip]; split at h <;> [contradiction; skip]
    set self0 := if atIdx > ed.ctr + params.maxOooKeysOrDefault then { ed with prev := ed.prev.clear } else ed
    rcases hadv : self0.keyAdvanceLoop hkdf atIdx params with e | self1
    · simp [self0, hadv, Bind.bind, Except.bind] at h
    · simp only [self0, hadv, Bind.bind, Except.bind] at h
      rcases hgc : ChainResult.ofPanic (self1.prev.gc self1.ctr params) with e | prevGc
      · simp [hgc] at h
      · simp only [hgc] at h
        rcases hnk : ChainResult.ofPanic (ChainEpochDirection.nextKeyInternal hkdf self1.next self1.ctr) with e | ⟨next', ctr', _, outKey⟩
        · simp [hnk] at h
        · simp only [hnk, pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at h
          rcases h with ⟨rfl, rfl⟩
          have h0 : self0.prev.data.length ≤ ed.prev.data.length := by dsimp [self0]; split <;> simp [KeyHistory.clear]
          have ⟨_, hadvp⟩ := ChainEpochDirection.keyAdvanceLoop_length_le_ooo hkdf self0 atIdx params hadv
          have hgcp := KeyHistory.gc_length_le self1.prev self1.ctr params ((ChainResult.ofPanic_eq_ok).mp hgc)
          have ⟨hn, _⟩ := ChainEpochDirection.nextKeyInternal_length_le hkdf self1.next self1.ctr ((ChainResult.ofPanic_eq_ok).mp hnk)
          have hmul := Nat.mul_le_mul_left 36 (Nat.min_le_right (atIdx.toNat - 1 - self0.ctr.toNat) params.maxOooKeysOrDefault.toNat)
          simp only [ChainEpochDirection.intoPb, rawEpochDir]; omega

theorem ChainEpochDirection.key_raw_le_valid (hkdf : HkdfFn) (ed : ChainEpochDirection)
    (atIdx : BitVec 32) (params : ChainParamsPB) {ed' : ChainEpochDirection} {out : Bytes}
    (hval : ValidChainParams params) (h : ed.key hkdf atIdx params = .ok (ed', out)) :
    rawEpochDir ed'.intoPb ≤ rawEpochDir ed.intoPb + 72032 := by
  have h1 := ChainEpochDirection.key_raw_le_ooo hkdf ed atIdx params h
  unfold ValidChainParams at hval; omega

/-- Wire byte length of a single encoded `ChainEpochPB` link (`Proto.encodeMessage ChainEpochPB.encodeRaw 3#32`). -/
def linkWireLen (ep : ChainEpochPB) : Nat :=
  (Proto.encodeMessage ChainEpochPB.encodeRaw 3#32 ep).length

/-- Wire byte length of a model `ChainEpoch` link. -/
def linkModelWireLen (link : ChainEpoch) : Nat :=
  linkWireLen { send := some link.send.intoPb, recv := some link.recv.intoPb }

/-- Core wire payload of a `ChainPB` (`links` wire bytes + `nextRoot` bytes), avoiding the `200 * links.length`
slack of `rawChain`. -/
def chainWireCore (pb : ChainPB) : Nat :=
  (pb.links.map linkWireLen).sum + pb.nextRoot.length

theorem rawChainEpoch_le_linkWireLen (ep : ChainEpochPB) :
    rawChainEpoch ep ≤ linkWireLen ep :=
  Nat.le_trans (rawChainEpoch_le_encodeRaw ep) (length_le_encodeMessage ChainEpochPB.encodeRaw 3#32 ep)

theorem linkWireLen_le_rawChainEpoch (ep : ChainEpochPB) :
    linkWireLen ep ≤ rawChainEpoch ep + 198 := by
  unfold linkWireLen
  have h1 := encodeMessage_length_le ChainEpochPB.encodeRaw 3#32 ep
  have h2 := chainEpochPB_encodeRaw_length_le ep; omega

theorem encodeRepeatedMessage_links_eq (links : List ChainEpochPB) :
    (Proto.encodeRepeatedMessage ChainEpochPB.encodeRaw 3#32 links).length =
      (links.map linkWireLen).sum := by
  induction links with
  | nil => simp [Proto.encodeRepeatedMessage]
  | cons ep rest ih =>
    simp only [Proto.encodeRepeatedMessage, List.foldr_cons, List.length_append, List.map_cons, List.sum_cons]
    have h2 : (List.foldr (fun m acc => Proto.encodeMessage ChainEpochPB.encodeRaw 3#32 m ++ acc) [] rest).length = (rest.map linkWireLen).sum := ih
    rw [h2]; rfl

theorem chainWireCore_le_encodeRaw (pb : ChainPB) :
    chainWireCore pb ≤ (ChainPB.encodeRaw pb).length := by
  unfold ChainPB.encodeRaw chainWireCore; simp only [List.length_append]
  rw [encodeRepeatedMessage_links_eq]; have h4 := length_le_encodeBytesField 4#32 pb.nextRoot; omega

theorem chainWireCore_le_encodeOpt (opt : Option ChainPB) :
    optRaw chainWireCore opt ≤ (Proto.encodeOptMessage ChainPB.encodeRaw 2#32 opt).length :=
  length_le_encodeOptMessage ChainPB.encodeRaw chainWireCore chainWireCore_le_encodeRaw 2#32 opt

theorem chainPB_encodeRaw_le_chainWireCore (pb : ChainPB) :
    (ChainPB.encodeRaw pb).length ≤ chainWireCore pb + 154 := by
  unfold ChainPB.encodeRaw chainWireCore; simp only [List.length_append]; rw [encodeRepeatedMessage_links_eq]
  have h1 := encodeInt32Field_length_le 1#32 pb.direction; have h2 := encodeUint64Field_length_le 2#32 pb.currentEpoch
  have h4 := encodeBytesField_length_le 4#32 pb.nextRoot; have h5 := encodeUint64Field_length_le 5#32 pb.sendEpoch
  have h6 := encodeOptChainParams_length_le 6#32 pb.params; omega

theorem encodeOpt_chain_le_chainWireCore (opt : Option ChainPB) :
    (Proto.encodeOptMessage ChainPB.encodeRaw 2#32 opt).length ≤ optRaw chainWireCore opt + 176 :=
  encodeOptMessage_length_le ChainPB.encodeRaw chainWireCore 154 chainPB_encodeRaw_le_chainWireCore 2#32 opt

private theorem map_intoPb_linkWireLen (links : List ChainEpoch) :
    ((links.map fun link => ({ send := some link.send.intoPb, recv := some link.recv.intoPb } : ChainEpochPB)).map linkWireLen) =
    links.map linkModelWireLen := by
  induction links with
  | nil => rfl
  | cons l ls ih => rw [List.map_cons, List.map_cons, List.map_cons, ih]; rfl

theorem Chain.linksFromPb_wire_sum_eq {pbs : List ChainEpochPB} {links : List ChainEpoch}
    (h : Chain.linksFromPb pbs = .ok links) :
    (links.map linkModelWireLen).sum = (pbs.map linkWireLen).sum := by
  induction pbs generalizing links with
  | nil => simp only [Chain.linksFromPb, Except.ok.injEq] at h; subst h; rfl
  | cons pb rest ih =>
    unfold Chain.linksFromPb at h
    cases hs : pb.send with
    | none => simp [hs, Bind.bind, Except.bind] at h
    | some sendPb =>
      simp only [hs, Bind.bind, Except.bind] at h
      rcases hsf : ChainEpochDirection.fromPb sendPb with e | send
      · simp [hsf] at h
      · simp only [hsf] at h
        cases hr : pb.recv with
        | none => simp [hr] at h
        | some recvPb =>
          simp only [hr] at h
          rcases hrf : ChainEpochDirection.fromPb recvPb with e | recv
          · simp [hrf] at h
          · simp only [hrf] at h
            rcases htail : Chain.linksFromPb rest with e | tail
            · simp [htail] at h
            · simp only [htail, pure, Except.pure, Except.ok.injEq] at h; subst h
              have hpb : ({ send := some send.intoPb, recv := some recv.intoPb } : ChainEpochPB) = pb := by
                cases pb; dsimp only at hs hr; subst hs; subst hr
                simp [ChainEpochDirection.fromPb_intoPb hsf, ChainEpochDirection.fromPb_intoPb hrf]
              simp only [List.map_cons, List.sum_cons, linkModelWireLen, hpb, ih htail]

theorem Chain.fromPb_wire_eq {pb : ChainPB} {c : Chain} (h : Chain.fromPb pb = .ok c) :
    chainWireCore c.intoPb = chainWireCore pb ∧ pb.params = some c.params := by
  unfold Chain.fromPb at h
  cases hd : Direction.fromI32? pb.direction with
  | none => simp [hd, Bind.bind, Except.bind] at h
  | some d =>
    simp only [hd, Bind.bind, Except.bind] at h
    rcases hl : Chain.linksFromPb pb.links with e | links
    · simp [hl] at h
    · simp only [hl] at h
      cases hp : pb.params with
      | none => simp [hp] at h
      | some p =>
        simp only [hp, pure, Except.pure, Except.ok.injEq] at h; subst h
        exact ⟨by simp only [Chain.intoPb, chainWireCore, map_intoPb_linkWireLen, Chain.linksFromPb_wire_sum_eq hl], rfl⟩

theorem Chain.new_wire_le (hkdf : HkdfFn) (initialKey : Bytes) (dir : Direction)
    (params : ChainParamsPB) {c : Chain} (h : Chain.new hkdf initialKey dir params = .ok c) :
    chainWireCore c.intoPb ≤ 294 ∧ c.params = params := by
  unfold Chain.new at h; simp only [Except.ok.injEq] at h; subst h; refine ⟨?_, rfl⟩
  have hs := Chain.cedForDirection_raw_le (hkdf (List.replicate 32 0#8) initialKey chainStartInfo 96) dir
  have hr := Chain.cedForDirection_raw_le (hkdf (List.replicate 32 0#8) initialKey chainStartInfo 96) dir.switch
  have hroot : ((hkdf (List.replicate 32 0#8) initialKey chainStartInfo 96).take 32).length ≤ 32 := List.length_take_le _ _
  have hlink := linkWireLen_le_rawChainEpoch {
    send := some (Chain.cedForDirection (hkdf (List.replicate 32 0#8) initialKey chainStartInfo 96) dir).intoPb
    recv := some (Chain.cedForDirection (hkdf (List.replicate 32 0#8) initialKey chainStartInfo 96) dir.switch).intoPb }
  simp only [Chain.intoPb, chainWireCore, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, rawChainEpoch, optRaw] at hlink ⊢; omega

theorem chainFromVersionNegotiation_wire_le (hkdf : HkdfFn) (vn : VersionNegotiationPB) {c : Chain}
    (h : chainFromVersionNegotiation hkdf vn = .ok c) :
    chainWireCore c.intoPb ≤ 294 ∧ vn.chainParams = some c.params := by
  unfold chainFromVersionNegotiation at h
  cases hd : Direction.fromI32? vn.direction with
  | none => simp [hd, Bind.bind, Except.bind] at h
  | some d =>
    simp only [hd, Bind.bind, Except.bind] at h; cases hp : vn.chainParams with
    | none => simp [hp] at h
    | some p => simp only [hp] at h; obtain ⟨h1, h2⟩ := Chain.new_wire_le hkdf vn.authKey d p h; exact ⟨h1, h2 ▸ rfl⟩

theorem chainFrom_wire_le (hkdf : HkdfFn) (pb : Option ChainPB) (vn : Option VersionNegotiationPB)
    {c : Chain} (h : chainFrom hkdf pb vn = .ok c) :
    chainWireCore c.intoPb ≤ optRaw chainWireCore pb + 294 ∧
      ((∃ cpb, pb = some cpb ∧ cpb.params = some c.params) ∨
       (∃ vnpb, vn = some vnpb ∧ vnpb.chainParams = some c.params)) := by
  unfold chainFrom at h; cases pb with
  | some cpb =>
    obtain ⟨heq, hp⟩ := Chain.fromPb_wire_eq h
    exact ⟨by simp only [optRaw]; omega, Or.inl ⟨cpb, rfl, hp⟩⟩
  | none =>
    cases vn with
    | none => contradiction
    | some vnpb =>
      obtain ⟨hle, hp⟩ := chainFromVersionNegotiation_wire_le hkdf vnpb h
      exact ⟨by simp only [optRaw]; omega, Or.inr ⟨vnpb, rfl, hp⟩⟩

theorem Chain.addEpoch_wire_le (hkdf : HkdfFn) (c : Chain) (es : EpochSecret) {c' : Chain}
    (h : c.addEpoch hkdf es = .ok c') :
    chainWireCore c'.intoPb ≤ chainWireCore c.intoPb + 294 ∧ c'.params = c.params := by
  unfold Chain.addEpoch at h; split at h <;> [contradiction; skip]; split at h <;> [contradiction; skip]
  simp only [Except.ok.injEq] at h; subst h; refine ⟨?_, rfl⟩
  have hs := Chain.cedForDirection_raw_le (hkdf c.nextRoot es.secret chainAddEpochInfo 96) c.dir
  have hr := Chain.cedForDirection_raw_le (hkdf c.nextRoot es.secret chainAddEpochInfo 96) c.dir.switch
  have hroot : ((hkdf c.nextRoot es.secret chainAddEpochInfo 96).take 32).length ≤ 32 := List.length_take_le _ _
  have hlink := linkWireLen_le_rawChainEpoch {
    send := some (Chain.cedForDirection (hkdf c.nextRoot es.secret chainAddEpochInfo 96) c.dir).intoPb
    recv := some (Chain.cedForDirection (hkdf c.nextRoot es.secret chainAddEpochInfo 96) c.dir.switch).intoPb }
  simp only [Chain.intoPb, chainWireCore, List.map_append, List.sum_append, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, rawChainEpoch, optRaw] at hlink ⊢; omega

private theorem sum_map_drop_le_wire {α : Type} (f : α → Nat) (n : Nat) (l : List α) :
    ((l.drop n).map f).sum ≤ (l.map f).sum := by
  induction n generalizing l with
  | zero => simp
  | succ n ih => cases l with | nil => simp | cons x xs => simp only [List.drop_succ_cons, List.map_cons, List.sum_cons]; have := ih xs; omega

private theorem clearSendNextPrefix_wire_sum_le (n : Nat) (l : List ChainEpoch) :
    ((Chain.clearSendNextPrefix n l).map linkModelWireLen).sum ≤ (l.map linkModelWireLen).sum + 198 * n := by
  induction n generalizing l with
  | zero => simp [Chain.clearSendNextPrefix]
  | succ n ih =>
    cases l with
    | nil => simp [Chain.clearSendNextPrefix]
    | cons x xs =>
      simp only [Chain.clearSendNextPrefix, List.map_cons, List.sum_cons]
      have hih := ih xs
      have h1 := linkWireLen_le_rawChainEpoch { send := some x.send.clearNext.intoPb, recv := some x.recv.intoPb }
      have h2 := rawChainEpoch_le_linkWireLen { send := some x.send.intoPb, recv := some x.recv.intoPb }
      simp only [linkModelWireLen, rawChainEpoch, optRaw, ChainEpochDirection.clearNext, ChainEpochDirection.intoPb, rawEpochDir, List.length_nil] at h1 h2 ⊢
      rw [Nat.mul_add, Nat.mul_one]; omega

private theorem sendKey_tail_wire_le (hkdf : HkdfFn) {self1 : Chain} {epochIndex : Nat}
    {c' : Chain} {out : BitVec 32 × Bytes}
    (h : (match self1.links[epochIndex]? with
      | none => .error (.panic .linksOutOfBounds)
      | some link => do
        let (send', out) ← ChainResult.ofPanic (link.send.nextKey hkdf)
        let links' := self1.links.set epochIndex { link with send := send' }
        return ({ self1 with links := links' }, out) : ChainResult (Chain × (BitVec 32 × Bytes))) = .ok (c', out)) :
    chainWireCore c'.intoPb ≤ chainWireCore self1.intoPb + 230 ∧ c'.params = self1.params := by
  cases hlink : self1.links[epochIndex]? with
  | none => simp [hlink] at h
  | some link =>
    simp only [hlink] at h
    rcases hnk : ChainResult.ofPanic (link.send.nextKey hkdf) with e | ⟨send', out'⟩
    · simp [hnk, Bind.bind, Except.bind] at h
    · simp only [hnk, Bind.bind, Except.bind, pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at h
      rcases h with ⟨rfl, rfl⟩; refine ⟨?_, rfl⟩
      have hsend := ChainEpochDirection.nextKey_raw_le hkdf link.send ((ChainResult.ofPanic_eq_ok).mp hnk)
      have h1 := linkWireLen_le_rawChainEpoch { send := some send'.intoPb, recv := some link.recv.intoPb }
      have h2 := rawChainEpoch_le_linkWireLen { send := some link.send.intoPb, recv := some link.recv.intoPb }
      have hset := sum_map_set_le linkModelWireLen self1.links epochIndex link { link with send := send' } 230 hlink
        (by simp only [linkModelWireLen, rawChainEpoch, optRaw] at h1 h2 ⊢; omega)
      simp only [Chain.intoPb, chainWireCore, map_intoPb_linkWireLen]; omega

theorem Chain.sendKey_wire_le (hkdf : HkdfFn) (c : Chain) (epoch : Epoch) {c' : Chain}
    {out : BitVec 32 × Bytes} (h : c.sendKey hkdf epoch = .ok (c', out)) :
    chainWireCore c'.intoPb ≤ chainWireCore c.intoPb + 428 ∧ c'.params = c.params := by
  unfold Chain.sendKey at h; split at h <;> [contradiction; skip]
  rcases heidx : ChainResult.ofError (c.epochIdx epoch) with e | epochIndex0
  · simp [heidx, Bind.bind, Except.bind] at h
  · simp only [heidx, Bind.bind, Except.bind] at h
    obtain ⟨htail, hparams⟩ := sendKey_tail_wire_le hkdf h
    by_cases hne : c.sendEpoch != epoch
    · simp only [hne, ↓reduceIte, Chain.intoPb, chainWireCore, map_intoPb_linkWireLen] at htail hparams
      have h1 := clearSendNextPrefix_wire_sum_le
        (epochIndex0 - (epochIndex0 - EPOCHS_TO_KEEP_PRIOR_TO_SEND_EPOCH))
        (c.links.drop (epochIndex0 - EPOCHS_TO_KEEP_PRIOR_TO_SEND_EPOCH))
      have h2 := sum_map_drop_le_wire linkModelWireLen (epochIndex0 - EPOCHS_TO_KEEP_PRIOR_TO_SEND_EPOCH) c.links
      have hle1 : epochIndex0 - (epochIndex0 - EPOCHS_TO_KEEP_PRIOR_TO_SEND_EPOCH) ≤ 1 := by unfold EPOCHS_TO_KEEP_PRIOR_TO_SEND_EPOCH; omega
      have hmul : 198 * (epochIndex0 - (epochIndex0 - EPOCHS_TO_KEEP_PRIOR_TO_SEND_EPOCH)) ≤ 198 := by omega
      exact ⟨by simp only [Chain.intoPb, chainWireCore, map_intoPb_linkWireLen]; omega, hparams⟩
    · simp only [hne, Bool.false_eq_true, ↓reduceIte] at htail hparams; exact ⟨by omega, hparams⟩

theorem Chain.recvKey_wire_le (hkdf : HkdfFn) (c : Chain) (epoch : Epoch) (index : BitVec 32)
    {c' : Chain} {out : Bytes} (hval : ValidChainParams c.params)
    (h : c.recvKey hkdf epoch index = .ok (c', out)) :
    chainWireCore c'.intoPb ≤ chainWireCore c.intoPb + 72230 ∧ c'.params = c.params := by
  unfold Chain.recvKey at h; split at h
  · simp only [Except.ok.injEq, Prod.mk.injEq] at h; rcases h with ⟨rfl, _⟩; exact ⟨by omega, rfl⟩
  · rcases heidx : ChainResult.ofError (c.epochIdx epoch) with e | epochIndex
    · simp [heidx, Bind.bind, Except.bind] at h
    · simp only [heidx, Bind.bind, Except.bind] at h
      cases hlink : c.links[epochIndex]? with
      | none => simp [hlink] at h
      | some link =>
        simp only [hlink] at h
        rcases hkey : link.recv.key hkdf index c.params with e | ⟨recv', out'⟩
        · simp [hkey] at h
        · simp only [hkey, pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at h
          rcases h with ⟨rfl, rfl⟩; refine ⟨?_, rfl⟩
          have hrecv := ChainEpochDirection.key_raw_le_valid hkdf link.recv index c.params hval hkey
          have h1 := linkWireLen_le_rawChainEpoch { send := some link.send.intoPb, recv := some recv'.intoPb }
          have h2 := rawChainEpoch_le_linkWireLen { send := some link.send.intoPb, recv := some link.recv.intoPb }
          have hset := sum_map_set_le linkModelWireLen c.links epochIndex link { link with recv := recv' }
            72230 hlink (by simp only [linkModelWireLen, rawChainEpoch, optRaw] at h1 h2 ⊢; omega)
          simp only [Chain.intoPb, chainWireCore, map_intoPb_linkWireLen]; omega

/-! ## `PqRatchetState` Wire Decomposition and `send` / `recv` Proofs -/

theorem encodeState_length_eq (m : PqRatchetState) :
    (Proto.encodeState m).length =
      (Proto.encodeOptMessage VersionNegotiationPB.encodeRaw 1#32 m.versionNegotiation).length +
      (Proto.encodeOptMessage ChainPB.encodeRaw 2#32 m.chain).length +
      (match m.inner with | none => 0 | some i => (PqRatchetState.Inner.encode i).length) := by
  show (PqRatchetState.encodeRaw m).length = _; unfold PqRatchetState.encodeRaw
  cases m.inner <;> [simp [List.length_append]; (simp [List.length_append]; omega)]

theorem validChainParams_of_chainFrom {hkdf : HkdfFn} {st : PqRatchetState} {c : Chain}
    (hval : ValidPqState st)
    (h : chainFrom hkdf st.chain st.versionNegotiation = .ok c) :
    ValidChainParams c.params := by
  obtain ⟨_, hsrc⟩ := chainFrom_wire_le hkdf st.chain st.versionNegotiation h
  rcases hsrc with ⟨cpb, hch, hp⟩ | ⟨vnpb, hvn, hp⟩
  · exact hval.2 cpb hch c.params hp
  · exact hval.1 vnpb hvn c.params hp

theorem sendAfterStates_wire_le {F : ShaCompress} {K : MlKem} {hkdf : HkdfFn}
    {st : PqRatchetState} {msg : Message spqrPolyApi} {key : Option EpochSecret}
    {st1 : States spqrPolyApi (spqrAuthApi F)} {out : Send}
    (hval : ValidPqState st)
    (h : sendAfterStates (spqrDeps F K) hkdf (pqRatchetStateToPb st) msg key st1 = .ok out) :
    ∃ chainPb : Option ChainPB,
      optRaw chainWireCore chainPb ≤ optRaw chainWireCore st.chain + 1016 ∧
      (∀ ch, chainPb = some ch → ∀ p, ch.params = some p → ValidChainParams p) ∧
      out.state = Proto.encodeState (pbToPqRatchetState {
        inner := some st1.into_pb, versionNegotiation := st.versionNegotiation, chain := chainPb }) := by
  have hst_vn : (pqRatchetStateToPb st).versionNegotiation = st.versionNegotiation := rfl
  have hst_ch : (pqRatchetStateToPb st).chain = st.chain := rfl
  unfold sendAfterStates at h; simp only [pure_bind_except, hst_vn, hst_ch] at h
  have hchain? : ∃ chain? : Option Chain,
      (∀ c0, chain? = some c0 → chainWireCore c0.intoPb ≤ optRaw chainWireCore st.chain + 294 ∧ ValidChainParams c0.params) ∧
      ((do
        let (index, msgKey, chainPb) ← match chain? with
          | none =>
            if key.isNone then pure (0#32, ([] : Bytes), (none : Option ChainPB))
            else Except.error (SpqrApiError.panic SpqrApiPanic.sendKeySomeWithoutChain)
          | some chain0 => do
            let chain1 ← match key with
              | some epochSecret => SpqrApiResult.ofChainPanic (chain0.addEpoch hkdf epochSecret)
              | none => pure chain0
            let epoch := (spqrDeps F K).msgEpoch msg
            if epoch == 0#64 then Except.error (SpqrApiError.panic SpqrApiPanic.sendEpochUnderflow)
            else do
              let (chain2, (idx, mk)) ← SpqrApiResult.ofChainResult (chain1.sendKey hkdf (epoch - 1#64))
              pure (idx, mk, some chain2.intoPb)
        let msgBytes := (spqrDeps F K).msgSerialize msg index
        match msgBytes with
        | [] => Except.error (SpqrApiError.panic SpqrApiPanic.sendMsgEmpty)
        | b0 :: _ =>
          if b0 != Version.v1.toU8 then Except.error (SpqrApiError.panic SpqrApiPanic.sendMsgBadVersion)
          else
            let newStateBytes := (spqrDeps F K).encodeState {
              inner := some ((spqrDeps F K).statesIntoPb st1),
              versionNegotiation := st.versionNegotiation, chain := chainPb }
            let outKey : MessageKey := if msgKey.isEmpty then none else some msgKey
            Except.ok ({ state := newStateBytes, msg := msgBytes, key := outKey } : Send)) :
        SpqrApiResult Send) = .ok out := by
    cases hch_opt : st.chain with
    | none =>
      rw [hch_opt] at h; dsimp only [] at h; cases hvn : st.versionNegotiation with
      | none => rw [hvn] at h; contradiction
      | some vn =>
        rw [hvn] at h; dsimp only [] at h; split at h
        · rcases except_bind_eq_ok h with ⟨c, hc, h1⟩; rw [SpqrApiResult.ofError_eq_ok] at hc
          obtain ⟨hle, hp⟩ := chainFromVersionNegotiation_wire_le hkdf vn hc
          refine ⟨some c, ?_, h1⟩; intro c0 hc0; have heq := Option.some.inj hc0; subst heq
          exact ⟨by simp; omega, hval.1 vn hvn c.params hp⟩
        · refine ⟨none, ?_, h⟩; intro _ hc; nomatch hc
    | some pb =>
      rw [hch_opt] at h; dsimp only [] at h; rcases except_bind_eq_ok h with ⟨c, hc, h1⟩
      rw [SpqrApiResult.ofError_eq_ok] at hc; obtain ⟨heq, hp⟩ := Chain.fromPb_wire_eq hc
      refine ⟨some c, ?_, h1⟩; intro c0 hc0; have hc_eq := Option.some.inj hc0; subst hc_eq
      exact ⟨by simp [heq], hval.2 pb hch_opt c.params hp⟩
  rcases hchain? with ⟨chain?, hch_le, h1⟩; simp only [pure_bind_except] at h1; cases chain? with
  | none =>
    dsimp only [] at h1; split at h1
    · split at h1 <;> [contradiction; skip]; split at h1 <;> [contradiction; skip]
      have hinj := Except.ok.inj h1; subst hinj
      refine ⟨none, by simp, ?_, rfl⟩; intro _ hnone; cases hnone
    · dsimp only [Bind.bind, Except.bind] at h1; contradiction
  | some chain0 =>
    obtain ⟨hc0_le, hc0_val⟩ := hch_le chain0 rfl
    have htail : ∀ (chain1 : Chain),
        chainWireCore chain1.intoPb ≤ optRaw chainWireCore st.chain + 588 →
        ValidChainParams chain1.params →
        (if ((spqrDeps F K).msgEpoch msg == 0#64) = true then do
          let __x : BitVec 32 × Bytes × Option ChainPB ←
            Except.error (SpqrApiError.panic SpqrApiPanic.sendEpochUnderflow)
          match (spqrDeps F K).msgSerialize msg __x.1 with
          | [] => Except.error (SpqrApiError.panic SpqrApiPanic.sendMsgEmpty)
          | b0 :: _ =>
            if (b0 != Version.v1.toU8) = true then Except.error (SpqrApiError.panic SpqrApiPanic.sendMsgBadVersion)
            else Except.ok ({
              state := (spqrDeps F K).encodeState {
                inner := some ((spqrDeps F K).statesIntoPb st1),
                versionNegotiation := st.versionNegotiation, chain := __x.2.2 },
              msg := (spqrDeps F K).msgSerialize msg __x.1,
              key := if __x.2.1.isEmpty = true then none else some __x.2.1 } : Send)
        else do
          let __x ← SpqrApiResult.ofChainResult (chain1.sendKey hkdf ((spqrDeps F K).msgEpoch msg - 1#64))
          match (spqrDeps F K).msgSerialize msg __x.2.1 with
          | [] => Except.error (SpqrApiError.panic SpqrApiPanic.sendMsgEmpty)
          | b0 :: _ =>
            if (b0 != Version.v1.toU8) = true then Except.error (SpqrApiError.panic SpqrApiPanic.sendMsgBadVersion)
            else Except.ok ({
              state := (spqrDeps F K).encodeState {
                inner := some ((spqrDeps F K).statesIntoPb st1),
                versionNegotiation := st.versionNegotiation, chain := some __x.1.intoPb },
              msg := (spqrDeps F K).msgSerialize msg __x.2.1,
              key := if List.isEmpty __x.2.2 = true then none else some __x.2.2 } : Send)) = .ok out →
        ∃ chainPb : Option ChainPB,
          optRaw chainWireCore chainPb ≤ optRaw chainWireCore st.chain + 1016 ∧
          (∀ ch, chainPb = some ch → ∀ p, ch.params = some p → ValidChainParams p) ∧
          out.state = Proto.encodeState (pbToPqRatchetState {
            inner := some st1.into_pb, versionNegotiation := st.versionNegotiation, chain := chainPb }) := by
      intro chain1 hc1_le hc1_val hstep2; split at hstep2
      · dsimp only [Bind.bind, Except.bind] at hstep2; contradiction
      · rcases except_bind_eq_ok hstep2 with ⟨⟨chain2, idx, mk⟩, hc2, h2⟩
        rw [SpqrApiResult.ofChainResult_eq_ok] at hc2
        obtain ⟨hsend, hparams2⟩ := Chain.sendKey_wire_le hkdf chain1 _ hc2
        dsimp only [] at h2; split at h2 <;> [contradiction; skip]; split at h2 <;> [contradiction; skip]
        have hinj2 := Except.ok.inj h2; subst hinj2
        refine ⟨some chain2.intoPb, by simp; omega, ?_, rfl⟩
        intro ch hch p hp; cases hch; cases hp; exact hparams2 ▸ hc1_val
    cases key with
    | none => exact htail chain0 (by omega) hc0_val h1
    | some es =>
      dsimp only [] at h1; rcases except_bind_eq_ok h1 with ⟨chain1, hc1, hstep2⟩
      rw [SpqrApiResult.ofChainPanic_eq_ok] at hc1
      obtain ⟨hadd, hp1⟩ := Chain.addEpoch_wire_le hkdf chain0 es hc1
      exact htail chain1 (by omega) (hp1 ▸ hc0_val) hstep2

/-- One-step growth bound for `Top.send`: on any `ValidState s` with `s.length < 2^64`,
if `(send (spqrDeps F K) hkdf s rng).1 = .ok out`, then `ValidState out.state` and
`out.state.length ≤ s.length + 1055000`. -/
theorem send_validState_length_le (F : ShaCompress) (K : MlKem) (hkdf : HkdfFn)
    (s : SerializedState) (rng : Bytes) (out : Send)
    (hval : ValidState s) (hlen : s.length < 2 ^ 64)
    (hsend : (send (spqrDeps F K) hkdf s rng).1 = .ok out) :
    ValidState out.state ∧ out.state.length ≤ s.length + 1055000 := by
  obtain ⟨st, rfl, hst_val⟩ := hval.exists_encodeState
  have hdec := decodeState_spqrDeps_encodeState_pb F K st hlen
  unfold send at hsend; rw [hdec] at hsend; dsimp only [] at hsend
  cases hinner : (pqRatchetStateToPb st).inner with
  | none =>
    rw [hinner] at hsend; have hinj := Except.ok.inj hsend; subst hinj
    exact ⟨validState_nil, by simp⟩
  | some pb =>
    have hst_inner : st.inner = some (.v1 pb) := by
      cases hin : st.inner with
      | none => simp [pqRatchetStateToPb, hin] at hinner
      | some i => cases i with | v1 v => simp [pqRatchetStateToPb, hin] at hinner; subst hinner; rfl
    rw [hinner] at hsend; dsimp only [] at hsend
    cases hfrom : (spqrDeps F K).statesFromPb pb with
    | error _ => rw [hfrom] at hsend; contradiction
    | ok st0' =>
      rw [hfrom] at hsend; dsimp only [] at hsend
      unfold spqrDeps liftStatesResult at hfrom; dsimp only [] at hfrom
      cases hs0 : States.from_pb spqrPolyApi (spqrAuthApi F) pb with
      | error e => rw [hs0] at hfrom; cases e <;> contradiction
      | ok st0 =>
        have hfrom' := hfrom; rw [hs0] at hfrom'; have hst0_eq := Except.ok.inj hfrom'; subst hst0_eq
        rcases States.from_pb_raw_le hs0 with ⟨hst0_raw, hst0_pts⟩
        have hpb_enc := States.from_pb_rawV1State_le_encode hs0
        cases hsend_st : ((spqrDeps F K).statesSend st0 rng).1 with
        | error _ => rw [hsend_st] at hsend; contradiction
        | ok val =>
          rcases val with ⟨msg, key, st1⟩; rw [hsend_st] at hsend; dsimp only [] at hsend
          unfold spqrDeps at hsend_st; dsimp only [] at hsend_st
          cases hsend0 : st0.send K rng with
          | error se => rw [hsend0] at hsend_st; cases se <;> contradiction
          | ok p =>
            rcases p with ⟨sOut, tape'⟩; have hsend' := hsend_st; rw [hsend0] at hsend'
            have hst1 := (Prod.mk.inj (Prod.mk.inj (Except.ok.inj hsend')).2).2; subst hst1
            have hst1_raw := (States.send_raw_le hst0_pts hsend0).1
            rcases sendAfterStates_wire_le hst_val hsend with ⟨chainPb, hch_le, hch_val, hout_eq⟩
            refine ⟨Or.inr ⟨_, hout_eq, hst_val.1, hch_val⟩, ?_⟩
            rw [hout_eq, encodeState_length_eq, encodeState_length_eq st]
            have hch_low := chainWireCore_le_encodeOpt st.chain
            have hch_up := encodeOpt_chain_le_chainWireCore chainPb
            have hin_up := pqInner_encode_length_le (.v1 sOut.state.into_pb)
            simp only [pbToPqRatchetState, Option.map, hst_inner, PqRatchetState.Inner.encode, rawPqInner] at hin_up ⊢
            omega

private theorem if_error_eq_ok {ε α : Type} {c : Prop} [Decidable c] {e : ε} {rest : Except ε α}
    {v : α} (h : (if c then Except.error e else rest) = .ok v) : rest = .ok v := by
  by_cases hc : c <;> simp [hc] at h; exact h

private theorem if_eq_ok_cases {ε α : Type} {c : Prop} [Decidable c] {t f : Except ε α} {v : α}
    (h : (if c then t else f) = .ok v) : t = .ok v ∨ f = .ok v := by
  by_cases hc : c <;> simp [hc] at h <;> [exact Or.inl h; exact Or.inr h]

private theorem if_pure_bind_eq_ok {ε α β : Type} {c : Prop} [Decidable c]
    {a : α} {K : α → Except ε β} {f : Except ε β} {v : β}
    (h : (if c then (Pure.pure a >>= K) else f) = .ok v) (P : α → Prop) (ha : P a)
    (hf : f = .ok v → ∃ a', P a' ∧ K a' = .ok v) : ∃ a', P a' ∧ K a' = .ok v := by
  rcases if_eq_ok_cases h with h1 | h1; · (rw [pure_bind_except] at h1; exact ⟨a, ha, h1⟩)
  exact hf h1

set_option maxHeartbeats 400000 in
/-- One-step growth bound for `Top.recv`: on any `ValidState s` with `s.length < 2^64`,
if `recv (spqrDeps F K) hkdf s msgBytes = .ok out`, then `ValidState out.state` and
`out.state.length ≤ s.length + 1128000`. -/
theorem recv_validState_length_le (F : ShaCompress) (K : MlKem) (hkdf : HkdfFn)
    (s : SerializedState) (msgBytes : SerializedMessage) (out : Recv)
    (hval : ValidState s) (hlen : s.length < 2 ^ 64)
    (hrecv : recv (spqrDeps F K) hkdf s msgBytes = .ok out) :
    ValidState out.state ∧ out.state.length ≤ s.length + 1128000 := by
  obtain ⟨st, rfl, hst_val⟩ := hval.exists_encodeState
  have hdec_eq := decodeState_spqrDeps_encodeState_pb F K st hlen
  unfold recv at hrecv; dsimp only [] at hrecv
  rcases except_bind_eq_ok hrecv with ⟨msg, _, h1⟩; rcases except_bind_eq_ok h1 with ⟨prePb, hdec, h2⟩
  rw [SpqrApiResult.ofError_eq_ok, hdec_eq] at hdec
  have hpre := Except.ok.inj hdec; subst hpre
  have hpre_vn : (pqRatchetStateToPb st).versionNegotiation = st.versionNegotiation := rfl
  have hpre_ch : (pqRatchetStateToPb st).chain = st.chain := rfl
  replace h2 := if_error_eq_ok (if_error_eq_ok h2); rcases if_eq_ok_cases h2 with h2 | h2
  · have hinj := Except.ok.inj h2; subst hinj; exact ⟨validState_nil, by simp⟩
  · rcases if_eq_ok_cases h2 with h2 | h2
    · rcases except_bind_eq_ok h2 with ⟨chain0, hc0, h3⟩; rcases except_bind_eq_ok h3 with ⟨⟨chain1, rawKey⟩, hc1, h4⟩
      rw [SpqrApiResult.ofError_eq_ok] at hc0; rw [SpqrApiResult.ofChainResult_eq_ok] at hc1
      dsimp only [] at h4; have hinj := Except.ok.inj h4; subst hinj
      rw [hpre_ch, hpre_vn] at hc0
      have hc0_le := (chainFrom_wire_le hkdf st.chain st.versionNegotiation hc0).1
      have hc0_val := validChainParams_of_chainFrom hst_val hc0
      obtain ⟨hc1_le, hp1⟩ := Chain.recvKey_wire_le hkdf chain0 0#64 msg.index hc0_val hc1
      have hst' : ValidPqState (pbToPqRatchetState {
          inner := (pqRatchetStateToPb st).inner, versionNegotiation := st.versionNegotiation,
          chain := some chain1.intoPb }) := by
        refine ⟨hst_val.1, fun ch hch p hp => ?_⟩; cases hch; cases hp; exact hp1 ▸ hc0_val
      refine ⟨Or.inr ⟨_, rfl, hst'⟩, ?_⟩
      dsimp only [spqrDeps]; rw [encodeState_length_eq, encodeState_length_eq st]
      have hch_low := chainWireCore_le_encodeOpt st.chain
      have hch_up := encodeOpt_chain_le_chainWireCore (some chain1.intoPb)
      have hin_eq : ((pqRatchetStateToPb st).inner.map PqRatchetState.Inner.v1) = st.inner := by
        cases hin : st.inner with
        | none => simp [pqRatchetStateToPb, hin]
        | some i => cases i; simp [pqRatchetStateToPb, hin]
      simp only [pbToPqRatchetState, hin_eq, optRaw_some, hpre_vn] at hch_up ⊢; omega
    · have hinner_st : ∀ pb, (pqRatchetStateToPb st).inner = some pb →
          (Proto.encodeMessage V1State.encodeRaw 3#32 pb).length =
            (match st.inner with | none => 0 | some i => (PqRatchetState.Inner.encode i).length) := by
        intro pb hpb; cases hin : st.inner with
        | none => simp [pqRatchetStateToPb, hin] at hpb
        | some i => cases i with | v1 v => simp [pqRatchetStateToPb, hin] at hpb; subst hpb; rfl
      rcases if_pure_bind_eq_ok h2
        (fun statePb =>
          ValidPqState (pbToPqRatchetState statePb) ∧
          optRaw chainWireCore statePb.chain ≤ optRaw chainWireCore st.chain + 294 ∧
          (∀ pb, statePb.inner = some pb →
            (∀ st0, States.from_pb spqrPolyApi (spqrAuthApi F) pb = .ok st0 →
              rawV1State pb ≤ (match st.inner with | none => 0 | some i => (PqRatchetState.Inner.encode i).length) + 704)))
        ⟨⟨hst_val.1, hst_val.2⟩, by simp [hpre_ch],
          fun pb hpb st0 hs0 => by rw [← hinner_st pb hpb]; exact States.from_pb_rawV1State_le_encode hs0⟩
        (by
          intro h2; rcases if_eq_ok_cases h2 with h2 | h2
          · dsimp only [Bind.bind, Except.bind] at h2; contradiction
          · rw [hpre_vn, hpre_ch] at h2
            cases hvn : st.versionNegotiation with
            | none => rw [hvn] at h2; dsimp only [Bind.bind, Except.bind] at h2; contradiction
            | some vn =>
              rw [hvn] at h2; dsimp only [] at h2; rw [pure_bind_except] at h2
              cases hv : Version.fromU8? msg.version with
              | none => rw [hv] at h2; dsimp only [Bind.bind, Except.bind] at h2; contradiction
              | some v =>
                rw [hv] at h2; dsimp only [] at h2; rw [pure_bind_except] at h2
                cases hd : Direction.fromI32? vn.direction with
                | none => rw [hd] at h2; dsimp only [Bind.bind, Except.bind] at h2; contradiction
                | some dir =>
                  rw [hd] at h2; dsimp only [] at h2; rw [pure_bind_except] at h2
                  rcases except_bind_eq_ok h2 with ⟨inner', hinit, hst4⟩
                  rcases except_bind_eq_ok hst4 with ⟨chain', hch', hst5⟩
                  rw [SpqrApiResult.ofPanic_eq_ok] at hinit; rw [SpqrApiResult.ofError_eq_ok] at hch'
                  have hinit_le := initInner_spqrDeps_raw_le hinit
                  have hc'_le := (chainFrom_wire_le hkdf st.chain (some vn) hch').1
                  have hc'_val : ValidChainParams chain'.params := by
                    obtain ⟨_, hsrc⟩ := chainFrom_wire_le hkdf st.chain (some vn) hch'
                    rcases hsrc with ⟨cpb, hch, hp⟩ | ⟨vnpb, hv_eq, hp⟩
                    · exact hst_val.2 cpb hch chain'.params hp
                    · cases hv_eq; exact hst_val.1 vn hvn chain'.params hp
                  rw [pure_bind_except] at hst5
                  refine ⟨{ inner := inner', versionNegotiation := none, chain := some chain'.intoPb },
                    ⟨⟨(by intro _ hnone; cases hnone), ?_⟩, by simp; omega, ?_⟩, hst5⟩
                  · intro ch hch p hp; cases hch; cases hp; exact hc'_val
                  · intro pb hpb _ _
                    have : rawV1State pb ≤ 424 := by dsimp only at hpb; subst hpb; exact hinit_le
                    omega)
        with ⟨statePb, ⟨hstPb_val, hstPb_ch, hstPb_in⟩, h3⟩
      cases hinner : statePb.inner with
      | none =>
        rw [hinner] at h3; have hinj := Except.ok.inj h3; subst hinj; exact ⟨validState_nil, by simp⟩
      | some pb =>
        rw [hinner] at h3; dsimp only [] at h3
        rcases except_bind_eq_ok h3 with ⟨sckaMsg, _, h4⟩; rcases except_bind_eq_ok h4 with ⟨st0', hfrom, h5⟩
        rcases except_bind_eq_ok h5 with ⟨⟨key, st1⟩, hrecv_st, h6⟩
        unfold spqrDeps liftStatesResult at hfrom; dsimp only [] at hfrom
        cases hs0 : States.from_pb spqrPolyApi (spqrAuthApi F) pb with
        | error se => rw [hs0] at hfrom; cases se <;> contradiction
        | ok st0 =>
          have hfrom' := hfrom; rw [hs0] at hfrom'; have hst0_eq := Except.ok.inj hfrom'; subst hst0_eq
          rcases States.from_pb_raw_le hs0 with ⟨hst0_raw, hst0_pts⟩
          have hpb_le := hstPb_in pb hinner st0 hs0
          unfold spqrDeps at hrecv_st; dsimp only [] at hrecv_st; cases hr0 : st0.recv K sckaMsg with
          | error se => rw [hr0] at hrecv_st; cases se <;> contradiction
          | ok rOut =>
            have hrecv' := hrecv_st; rw [hr0] at hrecv'; have hst1_eq := (Prod.mk.inj (Except.ok.inj hrecv')).2; subst hst1_eq
            have hst1_raw := (States.recv_raw_le hst0_pts hr0).1
            dsimp only [] at h6; split at h6 <;> [contradiction; skip]
            rcases except_bind_eq_ok h6 with ⟨chain0, hc0, h7⟩; rw [SpqrApiResult.ofError_eq_ok] at hc0
            have hc0_le := (chainFrom_wire_le hkdf statePb.chain statePb.versionNegotiation hc0).1
            have hc0_val : ValidChainParams chain0.params := validChainParams_of_chainFrom hstPb_val hc0
            have htail : ∀ (chain1 : Chain),
                chainWireCore chain1.intoPb ≤ chainWireCore chain0.intoPb + 294 →
                ValidChainParams chain1.params →
                (do
                  let __x_1 ← SpqrApiResult.ofChainResult (Chain.recvKey hkdf chain1 (msg.epoch - 1#64) msg.index)
                  Except.ok ({
                    state := (spqrDeps F K).encodeState {
                      inner := some ((spqrDeps F K).statesIntoPb rOut.state),
                      versionNegotiation := none, chain := some __x_1.1.intoPb },
                    key := if List.isEmpty __x_1.2 = true then none else some __x_1.2 } : Recv)) = .ok out →
                ValidState out.state ∧ out.state.length ≤ (Proto.encodeState st).length + 1128000 := by
              intro chain1 hc1_le hc1_val h8; rcases except_bind_eq_ok h8 with ⟨⟨chain2, msgKey⟩, hc2, h9⟩
              rw [SpqrApiResult.ofChainResult_eq_ok] at hc2; have hinj := Except.ok.inj h9; subst hinj
              obtain ⟨hc2_le, hp2⟩ := Chain.recvKey_wire_le hkdf chain1 (msg.epoch - 1#64) msg.index hc1_val hc2
              have hval_out : ValidPqState (pbToPqRatchetState {
                  inner := some rOut.state.into_pb, versionNegotiation := none, chain := some chain2.intoPb }) := by
                refine ⟨(by intro _ hnone; cases hnone), ?_⟩
                intro ch hch p hp; cases hch; cases hp; exact hp2 ▸ hc1_val
              refine ⟨Or.inr ⟨_, rfl, hval_out⟩, ?_⟩
              dsimp only [spqrDeps]; rw [encodeState_length_eq, encodeState_length_eq st]
              have hch_low := chainWireCore_le_encodeOpt st.chain
              have hch_up := encodeOpt_chain_le_chainWireCore (some chain2.intoPb)
              have hin_up := pqInner_encode_length_le (.v1 rOut.state.into_pb)
              have hvn_none : (Proto.encodeOptMessage VersionNegotiationPB.encodeRaw 1#32 none).length = 0 := rfl
              simp only [pbToPqRatchetState, Option.map, hvn_none, optRaw_some, rawPqInner] at hch_up hin_up ⊢; omega
            cases key with
            | none => dsimp only [] at h7; rw [pure_bind_except] at h7; exact htail chain0 (by omega) hc0_val h7
            | some es =>
              dsimp only [] at h7; rcases except_bind_eq_ok h7 with ⟨chain1, hc1, h8⟩
              rw [SpqrApiResult.ofChainPanic_eq_ok] at hc1
              obtain ⟨hadd, hp1⟩ := Chain.addEpoch_wire_le hkdf chain0 es hc1
              exact htail chain1 hadd (hp1 ▸ hc0_val) h8

/-- Model-level one-step growth bound for `(spqrV1 F K).send`: preserves `ValidState` and grows
the state byte length by at most `1055000` bytes. -/
theorem spqrV1_send_validState_length_le (F : ShaCompress) (K : MlKem)
    (s : Bytes) (tape : Bytes) (s' : Bytes) (salt : Salt) (msg : Bytes)
    (hval : ValidState s) (hlen : s.length < 2 ^ 64)
    (h : (spqrV1 F K).send s tape = some (s', salt, msg)) :
    ValidState s' ∧ s'.length ≤ s.length + 1055000 := by
  rw [spqrV1_eq] at h; unfold toSpqrModel at h; dsimp only at h
  cases hsend : (send (spqrDeps F K) (spqrHkdfWith F) s tape).1 with
  | error _ => rw [hsend] at h; contradiction
  | ok out =>
    rw [hsend] at h; dsimp only [] at h; cases hsalt : messageKeyToSalt? out.key with
    | none => rw [hsalt] at h; contradiction
    | some _ =>
      rw [hsalt] at h; dsimp only [] at h; have hinj := (Prod.mk.inj (Option.some.inj h)).1; subst hinj
      exact send_validState_length_le F K (spqrHkdfWith F) s tape out hval hlen hsend

/-- Model-level one-step growth bound for `(spqrV1 F K).recv`: preserves `ValidState` and grows
the state byte length by at most `1128000` bytes. -/
theorem spqrV1_recv_validState_length_le (F : ShaCompress) (K : MlKem)
    (s msg : Bytes) (s' : Bytes) (salt : Salt)
    (hval : ValidState s) (hlen : s.length < 2 ^ 64)
    (h : (spqrV1 F K).recv s msg = .ok (s', salt)) :
    ValidState s' ∧ s'.length ≤ s.length + 1128000 := by
  rw [spqrV1_eq] at h; unfold toSpqrModel at h; dsimp only at h
  cases hrecv : recv (spqrDeps F K) (spqrHkdfWith F) s msg with
  | error e => rw [hrecv] at h; cases e <;> contradiction
  | ok out =>
    rw [hrecv] at h; dsimp only [] at h; cases hsalt : recvKeyToSalt? out.key with
    | none => rw [hsalt] at h; contradiction
    | some _ =>
      rw [hsalt] at h; dsimp only [] at h
      have hinj := (Prod.mk.inj (Except.ok.inj h)).1; subst hinj
      exact recv_validState_length_le F K (spqrHkdfWith F) s msg out hval hlen hrecv

/-- Model-level one-step growth bound for `(spqrV1Recv F K).recv`: preserves `ValidState` and grows
the state byte length by at most `1128000` bytes. -/
theorem spqrV1Recv_recv_validState_length_le (F : ShaCompress) (K : MlKem)
    (s msg : Bytes) (s' : Bytes) (key : MessageKey)
    (hval : ValidState s) (hlen : s.length < 2 ^ 64)
    (h : (spqrV1Recv F K).recv s msg = .ok (s', key)) :
    ValidState s' ∧ s'.length ≤ s.length + 1128000 := by
  rw [spqrV1Recv_eq] at h; unfold toSpqrRecvModel at h; dsimp only at h
  cases hrecv : recv (spqrDeps F K) (spqrHkdfWith F) s msg with
  | error e => rw [hrecv] at h; cases e <;> contradiction
  | ok out =>
    rw [hrecv] at h; dsimp only [] at h
    have hinj := (Prod.mk.inj (Except.ok.inj h)).1; subst hinj
    exact recv_validState_length_le F K (spqrHkdfWith F) s msg out hval hlen hrecv

/-- Any `ValidState s` with `s.length < 2^31` transitions under `(spqrV1 F K).send`
to a `ValidState s'` with `s'.length < 2^32`. -/
theorem spqrV1_send_validState_lt_2_32 (F : ShaCompress) (K : MlKem)
    (s : Bytes) (tape : Bytes) (s' : Bytes) (salt : Salt) (msg : Bytes)
    (hval : ValidState s) (hlen : s.length < 2 ^ 31)
    (h : (spqrV1 F K).send s tape = some (s', salt, msg)) :
    ValidState s' ∧ s'.length < 2 ^ 32 := by
  have ⟨hv', hle⟩ := spqrV1_send_validState_length_le F K s tape s' salt msg hval (by omega) h
  exact ⟨hv', by omega⟩

/-- Any `ValidState s` with `s.length < 2^31` transitions under `(spqrV1 F K).recv`
to a `ValidState s'` with `s'.length < 2^32`. -/
theorem spqrV1_recv_validState_lt_2_32 (F : ShaCompress) (K : MlKem)
    (s msg : Bytes) (s' : Bytes) (salt : Salt)
    (hval : ValidState s) (hlen : s.length < 2 ^ 31)
    (h : (spqrV1 F K).recv s msg = .ok (s', salt)) :
    ValidState s' ∧ s'.length < 2 ^ 32 := by
  have ⟨hv', hle⟩ := spqrV1_recv_validState_length_le F K s msg s' salt hval (by omega) h
  exact ⟨hv', by omega⟩

end CryptoVerification.SpqrV1.Top.StateSize
