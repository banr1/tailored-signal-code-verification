/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Specifications.LibsignalSpqrV1.States
public import LibsignalBinary.Specifications.LibsignalSpqrV1.Top

/-!
# SPQR V1: concrete model assembly (`spqrV1Assembled`)

**Trusted in part.** The theorems of `Computational/Theorems/` use every definition in this file
except `saltToMessageKey` and `spqrV1RecvAssembled`, which are checked by Lean (see
`Computational/docs/TRUSTED_BASE.md`).

Instantiates the abstract dependency bundles (`spqrPolyApi`, `spqrAuthApi`, `spqrDeps`) to produce
the concrete SPQR V1 models `spqrV1Assembled` and `spqrV1RecvAssembled` (DEV-SPQR2). Proves chain
and receive key-length invariants (`Chain.recvKey_key_length`, `recv_key_valid`,
`recv_key_valid_unless_greater_index_zero`, `recv_some_key_length_32_unless_greater_index_zero`)
and receive-panic monotonicity (`toSpqrModel_recvPanics_of_toSpqrRecvModel`).
-/

@[expose] public section

namespace CryptoVerification.LibsignalSpqrV1

open CryptoGames.HMAC (ShaState hmacWith)
open CryptoGames.HKDF (Salt hkdfBlocks hkdfExpand)
open CryptoGames.LibsignalSession (ShaCompress)
open CryptoVerification.LibsignalTripleRatchet (SpqrModel)

/-! ## 1. Concrete `PolyApi` and `AuthApi` instances -/

instance : Repr Chunk where
  reprPrec c p := reprPrec (c.index, c.data.toList) p

instance : Inhabited Chunk where
  default := { index := 0#16, data := List.Vector.replicate 32 0#8 }

def protoPolyEncoderToPb (pb : ProtoPolynomialEncoder) : PolynomialEncoder :=
  { idx := pb.idx, pts := pb.pts, polys := pb.polys }

def pbToProtoPolyEncoder (pb : PolynomialEncoder) : ProtoPolynomialEncoder :=
  { idx := pb.idx, pts := pb.pts, polys := pb.polys }

def protoPolyDecoderToPb (pb : ProtoPolynomialDecoder) : PolynomialDecoder :=
  { ptsNeeded := pb.ptsNeeded, polys := pb.polys, pts := pb.pts, isComplete := pb.isComplete }

def pbToProtoPolyDecoder (pb : PolynomialDecoder) : ProtoPolynomialDecoder :=
  { ptsNeeded := pb.ptsNeeded, polys := pb.polys, pts := pb.pts, isComplete := pb.isComplete }

/-- Concrete `PolyApi` instance backed by `PolyEncoder` and `PolyDecoder` (`Poly.lean`). -/
def spqrPolyApi : PolyApi where
  Chunk := Chunk
  PolynomialError := PolynomialError
  EncodingError := EncodingError
  PolyEncoder := PolyEncoder
  PolyDecoder := PolyDecoder
  mkChunk := Chunk.mk
  chunkIndex := Chunk.index
  chunkData := Chunk.data
  encode_bytes := fun msg =>
    (PolyEncoder.encodeBytes msg).mapError PolyPanic.toSpqrPanic
  next_chunk := fun enc =>
    enc.nextChunk.mapError PolyPanic.toSpqrPanic
  encoder_into_pb := fun enc =>
    protoPolyEncoderToPb enc.intoPb
  encoder_from_pb := fun pb =>
    (PolyEncoder.fromPb (pbToProtoPolyEncoder pb)).mapError PolyPanic.toSpqrPanic
  decoder_new := fun lenBytes =>
    (PolyDecoder.new lenBytes).mapError PolyPanic.toSpqrPanic
  add_chunk := fun dec chunk =>
    (dec.addChunk chunk).mapError PolyPanic.toSpqrPanic
  decoded_message := fun dec =>
    dec.decodedMessage.mapError PolyPanic.toSpqrPanic
  decoder_into_pb := fun dec =>
    protoPolyDecoderToPb dec.intoPb
  decoder_from_pb := fun pb =>
    (PolyDecoder.fromPb (pbToProtoPolyDecoder pb)).mapError PolyPanic.toSpqrPanic

/-- Concrete `AuthApi` instance backed by `Authenticator` (`Auth.lean`) and `hkdfToVec F`. -/
def spqrAuthApi (F : ShaCompress) : AuthApi where
  Authenticator := Authenticator
  new := fun rootKey ep => .ok (Authenticator.new F rootKey ep)
  update := fun auth ep k => .ok (auth.update F ep k)
  mac_hdr := fun auth ep hdr => auth.macHdr F ep hdr
  mac_ct := fun auth ep ct => auth.macCt F ep ct
  verify_hdr := fun auth ep hdr expectedMac => auth.verifyHdrError F ep hdr expectedMac
  verify_ct := fun auth ep ct expectedMac => auth.verifyCtError F ep ct expectedMac
  into_pb := Authenticator.intoPb
  from_pb := Authenticator.fromPb
  hkdf_to_vec := hkdfToVec F

/-! ## 2. Concrete `SpqrApiDeps` and Assembled Models (`spqrV1Assembled`, `spqrV1RecvAssembled`) -/

def liftStatesResult {α : Type} (r : StatesResult α) : SpqrApiResult α :=
  match r with
  | .ok v => .ok v
  | .error (.err e) => .error (.err e)
  | .error (.panic _) => .error (.panic .v1)

def pqRatchetStateToPb (st : PqRatchetState) : PqRatchetStatePB V1State :=
  { inner := st.inner.map fun (.v1 v) => v
    versionNegotiation := st.versionNegotiation
    chain := st.chain }

def pbToPqRatchetState (st : PqRatchetStatePB V1State) : PqRatchetState :=
  { inner := st.inner.map PqRatchetState.Inner.v1
    versionNegotiation := st.versionNegotiation
    chain := st.chain }

@[simp] theorem pqRatchetStateToPb_pbToPqRatchetState (st : PqRatchetStatePB V1State) :
    pqRatchetStateToPb (pbToPqRatchetState st) = st := by
  cases st with
  | mk inner vn chain =>
    cases inner <;> rfl

@[simp] theorem pbToPqRatchetState_pqRatchetStateToPb (st : PqRatchetState) :
    pbToPqRatchetState (pqRatchetStateToPb st) = st := by
  cases st with
  | mk vn chain inner =>
    cases inner with
    | none => rfl
    | some i => cases i; rfl

/-- Concrete `SpqrApiDeps` bundle wiring `Proto.lean` (`V1State`, `Proto.decodeState`, `Proto.encodeState`)
and `States.lean` (`States spqrPolyApi (spqrAuthApi F)`, `Message spqrPolyApi`) into `Top.lean`. -/
def spqrDeps (F : ShaCompress) (K : MlKem) : SpqrApiDeps where
  V1StatePB := V1State
  decodeState := fun bs =>
    match Proto.decodeState bs with
    | .ok st => .ok (pqRatchetStateToPb st)
    | .error _ => .error ()
  encodeState := fun st =>
    Proto.encodeState (pbToPqRatchetState st)
  States := States spqrPolyApi (spqrAuthApi F)
  statesFromPb := fun pb =>
    liftStatesResult (States.from_pb spqrPolyApi (spqrAuthApi F) pb)
  statesIntoPb := States.into_pb
  MessageV1 := Message spqrPolyApi
  statesSend := fun st tape =>
    match st.send K tape with
    | .ok (sOut, tape') => (.ok (sOut.msg, sOut.key, sOut.state), tape')
    | .error (.err e) => (.error (.err e), tape)
    -- On a panic the returned tape is irrelevant: `toSpqrModel`'s `onPanic` clause never reads
    -- `draws`.
    | .error (.panic _) => (.error (.panic .v1), tape)
  statesRecv := fun st msg =>
    match st.recv K msg with
    | .ok rOut => .ok (rOut.key, rOut.state)
    | .error (.err e) => .error (.err e)
    | .error (.panic _) => .error (.panic .v1)
  msgSerialize := Message.serialize
  msgDeserialize := fun ep rem =>
    match Message.deserialize spqrPolyApi ep rem with
    | .ok m => .ok m
    | .error e => .error (.err e)
  msgEpoch := Message.epoch
  -- `States.init_a` / `init_b` never return `.error`; `.error .v1` keeps the match total.
  initV1Inner := fun dir authKey =>
    match dir with
    | .a2b =>
      match States.init_a spqrPolyApi (spqrAuthApi F) authKey with
      | .ok st => .ok st.into_pb
      | .error _ => .error .v1
    | .b2a =>
      match States.init_b spqrPolyApi (spqrAuthApi F) authKey with
      | .ok st => .ok st.into_pb
      | .error _ => .error .v1

/-- Assembled SPQR V1 `SpqrModel` (`toSpqrModel (spqrDeps F K) (spqrHkdfWith F)`). -/
def spqrV1Assembled (F : ShaCompress) (K : MlKem) : SpqrModel :=
  toSpqrModel (spqrDeps F K) (spqrHkdfWith F)

/-- Assembled SPQR V1 `SpqrRecvModel` (DEV-SPQR2). -/
def spqrV1RecvAssembled (F : ShaCompress) (K : MlKem) : SpqrRecvModel :=
  toSpqrRecvModel (spqrDeps F K) (spqrHkdfWith F)

/-! ## 3. Agreement and Key-Length Theorems -/

private theorem except_bind_eq_ok {ε α β : Type} {m : Except ε α} {f : α → Except ε β} {b : β}
    (h : (m >>= f) = Except.ok b) : ∃ a, m = Except.ok a ∧ f a = Except.ok b := by
  cases m with
  | error e => contradiction
  | ok a => exact ⟨a, rfl, h⟩

@[simp] theorem ChainResult.ofPanic_eq_ok {α : Type} {r : Except ChainPanic α} {v : α} :
    ChainResult.ofPanic r = Except.ok v ↔ r = Except.ok v := by
  cases r <;> simp [ChainResult.ofPanic]

@[simp] theorem ChainResult.ofError_eq_ok {α : Type} {r : Except Error α} {v : α} :
    ChainResult.ofError r = Except.ok v ↔ r = Except.ok v := by
  cases r <;> simp [ChainResult.ofError]

@[simp] theorem SpqrApiResult.ofError_eq_ok {α : Type} {r : Except Error α} {v : α} :
    SpqrApiResult.ofError r = Except.ok v ↔ r = Except.ok v := by
  cases r <;> simp [SpqrApiResult.ofError]

@[simp] theorem SpqrApiResult.ofPanic_eq_ok {α : Type} {r : Except SpqrApiPanic α} {v : α} :
    SpqrApiResult.ofPanic r = Except.ok v ↔ r = Except.ok v := by
  cases r <;> simp [SpqrApiResult.ofPanic]

@[simp] theorem SpqrApiResult.ofChainPanic_eq_ok {α : Type} {r : Except ChainPanic α} {v : α} :
    SpqrApiResult.ofChainPanic r = Except.ok v ↔ r = Except.ok v := by
  cases r <;> simp [SpqrApiResult.ofChainPanic]

@[simp] theorem SpqrApiResult.ofChainResult_eq_ok {α : Type} {r : ChainResult α} {v : α} :
    SpqrApiResult.ofChainResult r = Except.ok v ↔ r = Except.ok v := by
  cases r <;> simp [SpqrApiResult.ofChainResult]

theorem length_flatten_hkdfBlocks (F : ShaCompress) (prk info : Bytes) (n : Nat) :
    (hkdfBlocks F prk info n).flatten.length = 32 * n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp [hkdfBlocks, List.flatten_append, ih, length_hmacWith]
    omega

@[simp] theorem length_hkdfExpand (F : ShaCompress) (prk info : Bytes) (L : Nat) :
    (hkdfExpand F prk info L).length = L := by
  simp only [hkdfExpand, List.length_take, length_flatten_hkdfBlocks]
  omega

@[simp] theorem length_spqrHkdfWith (F : ShaCompress) (salt ikm info : Bytes) (n : Nat) :
    (spqrHkdfWith F salt ikm info n).length = n := by
  simp [spqrHkdfWith, length_hkdfExpand]

private theorem KeyHistory.getLoop_key_length_aux (self : KeyHistory) (atIdx : BitVec 32)
    (want : Bytes) (params : ChainParamsPB) :
    ∀ (fuel i : Nat), self.data.length - i ≤ fuel →
    self.data.length % KeyHistory.KEY_SIZE = 0 →
    i % KeyHistory.KEY_SIZE = 0 →
    ∀ {hist' : KeyHistory} {k : Bytes},
    self.getLoop atIdx want params i = Except.ok (hist', k) →
    k.length = 32
  | 0, i, hfuel, _, _, _, _, hok => by
    have hi : ¬ (i < self.data.length) := by omega
    unfold KeyHistory.getLoop at hok
    simp [hi] at hok
  | fuel + 1, i, hfuel, halign, hi_mod, _, _, hok => by
    unfold KeyHistory.getLoop at hok
    split at hok
    · rename_i hi
      split at hok
      · simp only [Except.ok.injEq, Prod.mk.injEq] at hok
        rcases hok with ⟨_, rfl⟩
        simp only [KeyHistory.KEY_SIZE] at halign hi_mod
        rw [List.length_take, List.length_drop]
        omega
      · apply KeyHistory.getLoop_key_length_aux self atIdx want params fuel
          (i + KeyHistory.KEY_SIZE) _ halign _ hok
        · simp only [KeyHistory.KEY_SIZE]; omega
        · simp only [KeyHistory.KEY_SIZE] at hi_mod ⊢; omega
    · contradiction

/-- Whenever `KeyHistory.getLoop` succeeds at an aligned offset `i`, the returned key slice has
length 32. -/
theorem KeyHistory.getLoop_key_length (self : KeyHistory) (atIdx : BitVec 32) (want : Bytes)
    (params : ChainParamsPB) (i : Nat)
    (halign : self.data.length % KeyHistory.KEY_SIZE = 0)
    (hi_mod : i % KeyHistory.KEY_SIZE = 0)
    {hist' : KeyHistory} {k : Bytes}
    (hok : self.getLoop atIdx want params i = Except.ok (hist', k)) :
    k.length = 32 :=
  KeyHistory.getLoop_key_length_aux self atIdx want params (self.data.length - i) i
    (Nat.le_refl _) halign hi_mod hok

/-- Whenever `KeyHistory.get` succeeds, the returned key has length 32 (for any `KeyHistory`, even
one decoded from an arbitrary `ChainPB`, because `KeyHistory.get` enforces
`self.data.length % 36 == 0` at `src/chain.rs:191`). -/
theorem KeyHistory.get_key_length (self : KeyHistory) (atIdx currentCtr : BitVec 32)
    (params : ChainParamsPB) {hist' : KeyHistory} {k : Bytes}
    (hok : self.get atIdx currentCtr params = Except.ok (hist', k)) :
    k.length = 32 := by
  dsimp only [KeyHistory.get] at hok
  split at hok
  · contradiction
  · rename_i halign
    split at hok
    · contradiction
    · split at hok
      · contradiction
      · have hmod : self.data.length % KeyHistory.KEY_SIZE = 0 := by
          simpa using halign
        exact KeyHistory.getLoop_key_length self atIdx (CryptoGames.HMAC.toBEBytes 4 atIdx) params 0
          hmod (Nat.zero_mod _) hok

/-- Whenever `ChainEpochDirection.nextKeyInternal (spqrHkdfWith F)` succeeds, the returned 32-byte
message key has length 32. -/
theorem ChainEpochDirection.nextKeyInternal_key_length (F : ShaCompress)
    (next : Bytes) (ctr : BitVec 32)
    {next' : Bytes} {ctr' : BitVec 32} {idx : BitVec 32} {mk : Bytes}
    (hok : ChainEpochDirection.nextKeyInternal (spqrHkdfWith F) next ctr =
      Except.ok (next', ctr', (idx, mk))) :
    mk.length = 32 := by
  dsimp only [ChainEpochDirection.nextKeyInternal] at hok
  split at hok
  · contradiction
  · split at hok
    · contradiction
    · simp only [Except.ok.injEq, Prod.mk.injEq] at hok
      rcases hok with ⟨_, _, _, rfl⟩
      simp [length_spqrHkdfWith]

/-- Whenever `ChainEpochDirection.key (spqrHkdfWith F)` succeeds, the returned message key has
length 32. -/
theorem ChainEpochDirection.key_key_length (F : ShaCompress)
    (self : ChainEpochDirection) (atIdx : BitVec 32) (params : ChainParamsPB)
    {ced' : ChainEpochDirection} {mk : Bytes}
    (hok : self.key (spqrHkdfWith F) atIdx params = Except.ok (ced', mk)) :
    mk.length = 32 := by
  dsimp only [ChainEpochDirection.key] at hok
  split at hok
  · rcases except_bind_eq_ok hok with ⟨⟨prev', out⟩, hget, hok⟩
    simp only [Pure.pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at hok
    rcases hok with ⟨_, rfl⟩
    exact KeyHistory.get_key_length self.prev atIdx self.ctr params hget
  · split at hok
    · contradiction
    · split at hok
      · contradiction
      · split at hok
        · contradiction
        · rcases except_bind_eq_ok hok with ⟨self1, _, hok⟩
          rcases except_bind_eq_ok hok with ⟨prevGc, _, hok⟩
          rcases except_bind_eq_ok hok with ⟨⟨next', ctr', idx', outKey⟩, hnk, hok⟩
          simp only [ChainResult.ofPanic_eq_ok] at hnk
          simp only [Pure.pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at hok
          rcases hok with ⟨_, rfl⟩
          exact ChainEpochDirection.nextKeyInternal_key_length F self1.next self1.ctr hnk

/-- Whenever `Chain.recvKey (spqrHkdfWith F)` succeeds with `(chain', mk)`, either
`epoch = 0#64 ∧ index = 0#32 ∧ mk = []` or `mk.length = 32`. -/
theorem Chain.recvKey_key_length (F : ShaCompress) (self : Chain) (epoch : Epoch) (index : BitVec 32)
    {chain' : Chain} {mk : Bytes}
    (hok : self.recvKey (spqrHkdfWith F) epoch index = Except.ok (chain', mk)) :
    (epoch = 0#64 ∧ index = 0#32 ∧ mk = []) ∨ mk.length = 32 := by
  dsimp only [Chain.recvKey] at hok
  split at hok
  · rename_i hzero
    simp only [Bool.and_eq_true, beq_iff_eq] at hzero
    simp only [Except.ok.injEq, Prod.mk.injEq] at hok
    exact Or.inl ⟨hzero.1, hzero.2, hok.2.symm⟩
  · rcases except_bind_eq_ok hok with ⟨epochIndex, _, hok⟩
    split at hok
    · contradiction
    · rename_i link _
      rcases except_bind_eq_ok hok with ⟨⟨recv', out⟩, hkey, hok⟩
      simp only [Pure.pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at hok
      rcases hok with ⟨_, rfl⟩
      exact Or.inr (ChainEpochDirection.key_key_length F link.recv index self.params hkey)

/-- Convert `Salt` (`Option (List.Vector (BitVec 8) 32)`) back to `MessageKey`. -/
def saltToMessageKey (salt : Salt) : MessageKey :=
  salt.map List.Vector.toList

@[simp] theorem saltToMessageKey_messageKeyToSalt? {mk : MessageKey} {salt : Salt}
    (h : messageKeyToSalt? mk = some salt) :
    saltToMessageKey salt = mk := by
  cases mk with
  | none =>
    simp only [messageKeyToSalt?, Option.some.injEq] at h
    subst h
    rfl
  | some k =>
    dsimp only [messageKeyToSalt?] at h
    by_cases hlen : k.length = 32
    · rw [dite_eq_left hlen] at h
      injection h with h
      subst h
      rfl
    · rw [dite_eq_right hlen] at h
      nomatch h

theorem recvKeyToSalt?_isSome_of_messageKeyToSalt? {mk : MessageKey}
    (h : (messageKeyToSalt? mk).isSome = true) :
    (recvKeyToSalt? mk).isSome = true := by
  rwa [recvKeyToSalt?_of_isSome h]

/-- If `toSpqrRecvModel` panics on `(stateBytes, msgBytes)`, so does `toSpqrModel`. -/
theorem toSpqrModel_recvPanics_of_toSpqrRecvModel (D : SpqrApiDeps) (hkdf : HkdfFn)
    (stateBytes msgBytes : Bytes)
    (h : (toSpqrRecvModel D hkdf).recvPanics stateBytes msgBytes) :
    (toSpqrModel D hkdf).recvPanics stateBytes msgBytes := by
  simpa only [toSpqrRecvModel, toSpqrModel] using h

private theorem recv_v1_tail_key_valid (D : SpqrApiDeps) (F : ShaCompress)
    (pre : MsgPreamble) (statePb : PqRatchetStatePB D.V1StatePB) {r : Recv}
    (hok :
      (match statePb.inner with
      | none => Except.ok { state := [], key := none }
      | some pb => do
        let sckaMsg ← D.msgDeserialize pre.epoch pre.remaining
        let st0 ← D.statesFromPb pb
        let (key, st1) ← D.statesRecv st0 sckaMsg
        if pre.epoch == 0#64 then
          Except.error (.panic .recvEpochUnderflow)
        else do
          let msgKeyEpoch : Epoch := pre.epoch - 1#64
          let chain0 ← SpqrApiResult.ofError (chainFrom (spqrHkdfWith F) statePb.chain statePb.versionNegotiation)
          let chain1 ←
            match key with
            | some epochSecret => SpqrApiResult.ofChainPanic (chain0.addEpoch (spqrHkdfWith F) epochSecret)
            | none => pure chain0
          let (chain2, msgKey) ← SpqrApiResult.ofChainResult (chain1.recvKey (spqrHkdfWith F) msgKeyEpoch pre.index)
          let newStateBytes := D.encodeState {
            inner := some (D.statesIntoPb st1)
            versionNegotiation := none
            chain := some chain2.intoPb
          }
          let outKey : MessageKey := if msgKey.isEmpty then none else some msgKey
          Except.ok {
            state := newStateBytes
            key := outKey
          }) = Except.ok r) :
    (messageKeyToSalt? r.key).isSome = true := by
  cases hinner : statePb.inner <;> rw [hinner] at hok <;> dsimp only at hok
  · injection hok with hok
    subst hok
    rfl
  · rename_i pb
    rcases except_bind_eq_ok hok with ⟨sckaMsg, _, hok⟩
    rcases except_bind_eq_ok hok with ⟨st0, _, hok⟩
    rcases except_bind_eq_ok hok with ⟨⟨key, st1⟩, _, hok⟩
    by_cases hep : (pre.epoch == 0#64) = true
    · rw [ite_eq_left hep] at hok; nomatch hok
    · rw [ite_eq_right hep] at hok
      rcases except_bind_eq_ok hok with ⟨chain0, _, hok⟩
      cases key <;> dsimp only at hok <;>
      · rcases except_bind_eq_ok hok with ⟨chain1, _, hok⟩
        rcases except_bind_eq_ok hok with ⟨⟨chain2, msgKey⟩, hrecvKey, hok⟩
        simp only [SpqrApiResult.ofChainResult_eq_ok] at hrecvKey
        injection hok with hok
        subst hok
        rcases Chain.recvKey_key_length F chain1 (pre.epoch - 1#64) pre.index hrecvKey with ⟨_, _, rfl⟩ | hlen32
        · simp [messageKeyToSalt?]
        · by_cases hemp : msgKey.isEmpty
          · simp [hemp, messageKeyToSalt?]
          · simp [hemp, messageKeyToSalt?, hlen32]

/-- In `Top.recv D (spqrHkdfWith F)`, every `Ok(r)` outside the `Ordering::Greater` + `msg.index == 0`
special case (`src/lib.rs:406`, DEV-SPQR2) has `(messageKeyToSalt? r.key).isSome = true`:
* On the empty-version (`currentVersion == 0`) or `statePb.inner == none` paths, `r.key = none`.
* On the V1 `Ordering::Equal` / `Ordering::Less` paths (`src/lib.rs:478–482`), `if msgKey.isEmpty then none else some msgKey`
  filters out any empty key from `(0, 0)` and `Chain.recvKey_key_length` guarantees `msgKey.length = 32`.
* On the `Ordering::Greater` path when `msg.index != 0#32`, `Chain.recvKey_key_length` on `zeroEpoch = 0#64`
  guarantees `rawKey.length = 32`. -/
theorem recv_key_valid_unless_greater_index_zero (D : SpqrApiDeps) (F : ShaCompress)
    (stateBytes : SerializedState) (msgBytes : SerializedMessage) {r : Recv}
    (hok : recv D (spqrHkdfWith F) stateBytes msgBytes = Except.ok r)
    (hnot : ¬ ∃ pre stPb,
      msgPreamble msgBytes = Except.ok pre ∧
      decodeState D stateBytes = Except.ok stPb ∧
      (stateVersion stPb).toU8 ≠ 0#8 ∧
      pre.version > (stateVersion stPb).toU8 ∧
      pre.index = 0#32) :
    (messageKeyToSalt? r.key).isSome = true := by
  unfold recv at hok
  rcases except_bind_eq_ok hok with ⟨pre, hpre, hok⟩
  rcases except_bind_eq_ok hok with ⟨preStatePb, hdec, hok⟩
  simp only [SpqrApiResult.ofError_eq_ok] at hpre hdec
  cases hvn : preStatePb.versionNegotiation <;> rw [hvn] at hok <;> dsimp only at hok
  · by_cases hmin : pre.version < (stateVersion preStatePb).toU8
    · rw [ite_eq_left hmin] at hok; nomatch hok
    · rw [ite_eq_right hmin] at hok
      by_cases hmis : (pre.version != (stateVersion preStatePb).toU8 && !((stateVersion preStatePb).toU8 == 0#8)) = true
      · rw [ite_eq_left hmis] at hok; nomatch hok
      · rw [ite_eq_right hmis] at hok
        by_cases hcv0 : ((stateVersion preStatePb).toU8 == 0#8) = true
        · rw [ite_eq_left hcv0] at hok
          injection hok with hok
          subst hok
          rfl
        · rw [ite_eq_right hcv0] at hok
          by_cases hgt : pre.version > (stateVersion preStatePb).toU8
          · rw [ite_eq_left hgt] at hok
            rcases except_bind_eq_ok hok with ⟨chain0, _, hok⟩
            rcases except_bind_eq_ok hok with ⟨⟨chain1, rawKey⟩, hrecvKey, hok⟩
            simp only [SpqrApiResult.ofChainResult_eq_ok] at hrecvKey
            injection hok with hok
            subst hok
            rcases Chain.recvKey_key_length F chain0 0#64 pre.index hrecvKey with ⟨_, hidx0, _⟩ | hlen32
            · exfalso
              apply hnot
              exact ⟨pre, preStatePb, hpre, hdec, by simpa using hcv0, hgt, hidx0⟩
            · simp [messageKeyToSalt?, hlen32]
          · rw [ite_eq_right hgt] at hok
            by_cases heq : (pre.version == (stateVersion preStatePb).toU8) = true
            · rw [ite_eq_left heq] at hok
              exact recv_v1_tail_key_valid D F pre preStatePb hok
            · rw [ite_eq_right heq] at hok
              by_cases hneg : (!((stateVersion preStatePb).toU8 > 0#8 && ((stateVersion preStatePb).toU8 == 0#8))) = true
              · rw [ite_eq_left hneg] at hok; nomatch hok
              · rw [ite_eq_right hneg] at hok; nomatch hok
  · rename_i vn
    by_cases hmin : pre.version < vn.minVersion.truncate 8
    · rw [ite_eq_left hmin] at hok; nomatch hok
    · rw [ite_eq_right hmin] at hok
      by_cases hmis : (pre.version != (stateVersion preStatePb).toU8 && !true) = true
      · rw [ite_eq_left hmis] at hok; nomatch hok
      · rw [ite_eq_right hmis] at hok
        by_cases hcv0 : ((stateVersion preStatePb).toU8 == 0#8) = true
        · rw [ite_eq_left hcv0] at hok
          injection hok with hok
          subst hok
          rfl
        · rw [ite_eq_right hcv0] at hok
          by_cases hgt : pre.version > (stateVersion preStatePb).toU8
          · rw [ite_eq_left hgt] at hok
            rcases except_bind_eq_ok hok with ⟨chain0, _, hok⟩
            rcases except_bind_eq_ok hok with ⟨⟨chain1, rawKey⟩, hrecvKey, hok⟩
            simp only [SpqrApiResult.ofChainResult_eq_ok] at hrecvKey
            injection hok with hok
            subst hok
            rcases Chain.recvKey_key_length F chain0 0#64 pre.index hrecvKey with ⟨_, hidx0, _⟩ | hlen32
            · exfalso
              apply hnot
              exact ⟨pre, preStatePb, hpre, hdec, by simpa using hcv0, hgt, hidx0⟩
            · simp [messageKeyToSalt?, hlen32]
          · rw [ite_eq_right hgt] at hok
            by_cases heq : (pre.version == (stateVersion preStatePb).toU8) = true
            · rw [ite_eq_left heq] at hok
              exact recv_v1_tail_key_valid D F pre preStatePb hok
            · rw [ite_eq_right heq] at hok
              by_cases hneg : (!((stateVersion preStatePb).toU8 > 0#8 && true)) = true
              · rw [ite_eq_left hneg] at hok; nomatch hok
              · rw [ite_eq_right hneg] at hok
                rcases except_bind_eq_ok hok with ⟨vn', hvn', hok⟩
                injection hvn' with hvn'
                subst hvn'
                cases hv : Version.fromU8? pre.version <;> rw [hv] at hok <;> dsimp only at hok
                · nomatch hok
                · rename_i v
                  rcases except_bind_eq_ok hok with ⟨v', hv', hok⟩
                  injection hv' with hv'
                  subst hv'
                  cases hd : Direction.fromI32? vn.direction <;> rw [hd] at hok <;> dsimp only at hok
                  · nomatch hok
                  · rename_i d
                    rcases except_bind_eq_ok hok with ⟨dir, _, hok⟩
                    rcases except_bind_eq_ok hok with ⟨inner', _, hok⟩
                    rcases except_bind_eq_ok hok with ⟨chain', _, hok⟩
                    exact recv_v1_tail_key_valid D F pre _ hok

/-- Every `some k` key returned by `Top.recv D (spqrHkdfWith F)` outside the `Ordering::Greater` +
`msg.index == 0` special case (`src/lib.rs:406`, DEV-SPQR2) has `k.length = 32`. -/
theorem recv_some_key_length_32_unless_greater_index_zero (D : SpqrApiDeps) (F : ShaCompress)
    (stateBytes : SerializedState) (msgBytes : SerializedMessage) {r : Recv} {k : Bytes}
    (hok : recv D (spqrHkdfWith F) stateBytes msgBytes = Except.ok r)
    (hk : r.key = some k)
    (hnot : ¬ ∃ pre stPb,
      msgPreamble msgBytes = Except.ok pre ∧
      decodeState D stateBytes = Except.ok stPb ∧
      (stateVersion stPb).toU8 ≠ 0#8 ∧
      pre.version > (stateVersion stPb).toU8 ∧
      pre.index = 0#32) :
    k.length = 32 := by
  have hval := recv_key_valid_unless_greater_index_zero D F stateBytes msgBytes hok hnot
  simp only [hk, messageKeyToSalt?] at hval
  split at hval
  · assumption
  · contradiction

/-- In `Top.recv D (spqrHkdfWith F)`, every `Ok(r)` has `(recvKeyToSalt? r.key).isSome = true`
(including the `Ordering::Greater` + `msg.index == 0` path where `r.key = some []`, DEV-SPQR2). -/
theorem recv_key_valid (D : SpqrApiDeps) (F : ShaCompress)
    (stateBytes : SerializedState) (msgBytes : SerializedMessage) {r : Recv}
    (hok : recv D (spqrHkdfWith F) stateBytes msgBytes = Except.ok r) :
    (recvKeyToSalt? r.key).isSome = true := by
  have h_raw (rawKey : Bytes) (hkey : rawKey = [] ∨ rawKey.length = 32) :
      (recvKeyToSalt? (some rawKey)).isSome = true := by
    rcases hkey with rfl | hlen32
    · rfl
    · cases rawKey with
      | nil => contradiction
      | cons b bs => simp [recvKeyToSalt?, messageKeyToSalt?, hlen32]
  unfold recv at hok
  rcases except_bind_eq_ok hok with ⟨pre, _, hok⟩
  rcases except_bind_eq_ok hok with ⟨preStatePb, _, hok⟩
  cases hvn : preStatePb.versionNegotiation <;> rw [hvn] at hok <;> dsimp only at hok
  · by_cases hmin : pre.version < (stateVersion preStatePb).toU8
    · rw [ite_eq_left hmin] at hok; nomatch hok
    · rw [ite_eq_right hmin] at hok
      by_cases hmis :
          (pre.version != (stateVersion preStatePb).toU8 &&
            !((stateVersion preStatePb).toU8 == 0#8)) = true
      · rw [ite_eq_left hmis] at hok; nomatch hok
      · rw [ite_eq_right hmis] at hok
        by_cases hcv0 : ((stateVersion preStatePb).toU8 == 0#8) = true
        · rw [ite_eq_left hcv0] at hok
          injection hok with hok; subst hok; rfl
        · rw [ite_eq_right hcv0] at hok
          by_cases hgt : pre.version > (stateVersion preStatePb).toU8
          · rw [ite_eq_left hgt] at hok
            rcases except_bind_eq_ok hok with ⟨chain0, _, hok⟩
            rcases except_bind_eq_ok hok with ⟨⟨chain1, rawKey⟩, hrecvKey, hok⟩
            simp only [SpqrApiResult.ofChainResult_eq_ok] at hrecvKey
            injection hok with hok; subst hok
            rcases Chain.recvKey_key_length F chain0 0#64 pre.index hrecvKey with
              ⟨_, _, hrk⟩ | hlen32
            · exact h_raw rawKey (Or.inl hrk)
            · exact h_raw rawKey (Or.inr hlen32)
          · rw [ite_eq_right hgt] at hok
            by_cases heq : (pre.version == (stateVersion preStatePb).toU8) = true
            · rw [ite_eq_left heq] at hok
              exact recvKeyToSalt?_isSome_of_messageKeyToSalt?
                (recv_v1_tail_key_valid D F pre preStatePb hok)
            · rw [ite_eq_right heq] at hok
              by_cases hneg :
                  (!((stateVersion preStatePb).toU8 > 0#8 &&
                    ((stateVersion preStatePb).toU8 == 0#8))) = true
              · rw [ite_eq_left hneg] at hok; nomatch hok
              · rw [ite_eq_right hneg] at hok; nomatch hok
  · rename_i vn
    by_cases hmin : pre.version < vn.minVersion.truncate 8
    · rw [ite_eq_left hmin] at hok; nomatch hok
    · rw [ite_eq_right hmin] at hok
      by_cases hmis : (pre.version != (stateVersion preStatePb).toU8 && !true) = true
      · rw [ite_eq_left hmis] at hok; nomatch hok
      · rw [ite_eq_right hmis] at hok
        by_cases hcv0 : ((stateVersion preStatePb).toU8 == 0#8) = true
        · rw [ite_eq_left hcv0] at hok
          injection hok with hok; subst hok; rfl
        · rw [ite_eq_right hcv0] at hok
          by_cases hgt : pre.version > (stateVersion preStatePb).toU8
          · rw [ite_eq_left hgt] at hok
            rcases except_bind_eq_ok hok with ⟨chain0, _, hok⟩
            rcases except_bind_eq_ok hok with ⟨⟨chain1, rawKey⟩, hrecvKey, hok⟩
            simp only [SpqrApiResult.ofChainResult_eq_ok] at hrecvKey
            injection hok with hok; subst hok
            rcases Chain.recvKey_key_length F chain0 0#64 pre.index hrecvKey with
              ⟨_, _, hrk⟩ | hlen32
            · exact h_raw rawKey (Or.inl hrk)
            · exact h_raw rawKey (Or.inr hlen32)
          · rw [ite_eq_right hgt] at hok
            by_cases heq : (pre.version == (stateVersion preStatePb).toU8) = true
            · rw [ite_eq_left heq] at hok
              exact recvKeyToSalt?_isSome_of_messageKeyToSalt?
                (recv_v1_tail_key_valid D F pre preStatePb hok)
            · rw [ite_eq_right heq] at hok
              by_cases hneg : (!((stateVersion preStatePb).toU8 > 0#8 && true)) = true
              · rw [ite_eq_left hneg] at hok; nomatch hok
              · rw [ite_eq_right hneg] at hok
                rcases except_bind_eq_ok hok with ⟨vn', hvn', hok⟩
                injection hvn' with hvn'; subst hvn'
                cases hv : Version.fromU8? pre.version <;> rw [hv] at hok <;> dsimp only at hok
                · nomatch hok
                · rename_i v
                  rcases except_bind_eq_ok hok with ⟨v', hv', hok⟩
                  injection hv' with hv'; subst hv'
                  cases hd : Direction.fromI32? vn.direction <;> rw [hd] at hok <;>
                    dsimp only at hok
                  · nomatch hok
                  · rename_i d
                    rcases except_bind_eq_ok hok with ⟨dir, _, hok⟩
                    rcases except_bind_eq_ok hok with ⟨inner', _, hok⟩
                    rcases except_bind_eq_ok hok with ⟨chain', _, hok⟩
                    exact recvKeyToSalt?_isSome_of_messageKeyToSalt?
                      (recv_v1_tail_key_valid D F pre _ hok)

end CryptoVerification.LibsignalSpqrV1
