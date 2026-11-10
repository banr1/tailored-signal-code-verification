/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Computational.Proofs.CryptoGames.Ratchet.LibsignalRefinesDefs
public import Computational.Proofs.CryptoGames.Ratchet.LibsignalWireRoundTrip
public import LibsignalBinary.Specifications.CryptoGames.SM.LibsignalGame
public import Computational.Proofs.CryptoGames.SM.LibsignalGameProofDefs
import Computational.Proofs.CryptoGames.Ratchet.LibsignalSessionStatements
import LibsignalBinary.Proofs.ProtoCodecRoundTrip

/-!
# Restricted `SignalMessage` wire round trip at prost's codec

**Checked by Lean.** Proves the restricted round trip `SignalRoundTripShort protoSignalCodec` and
32-bit wire-length bound `SignalEncodeFits32 protoSignalCodec` (DEV-LS21), and instantiates
`Refine.libsignal_refines` at `protoSignalCodec`.
-/

@[expose] public section

namespace CryptoVerification.LibsignalSession

open CryptoVerification.LibsignalProtoCodec

open CryptoGames CryptoGames.LibsignalSession

theorem publicKey_deserialize_serialize (pk : PublicKey) :
    PublicKey.deserialize pk.serialize = .ok pk := by
  unfold PublicKey.serialize PublicKey.deserialize
  rcases pk with ⟨⟨bs, hbs⟩⟩
  simp [hbs]
  congr 1
  exact Subtype.ext (List.take_of_length_le (Nat.le_of_eq hbs))

theorem publicKey_serialize_length (pk : PublicKey) : pk.serialize.length = 33 := by
  unfold PublicKey.serialize
  simp [pk.bytes.toList_length]

theorem versionByte_currentVersion_shift : versionByte currentVersion >>> 4 = currentVersion := by
  decide

/-- Protobuf message encoded by `signalWireCodec` for `h` and `body`. -/
def protoOf (h : SignalHeader) (body : List (BitVec 8)) : ProtoSignalMessage :=
  { ratchetKey := some h.senderRatchetKey.serialize, counter := some h.counter,
    previousCounter := some h.previousCounter, ciphertext := some body,
    pqRatchet := if h.pqRatchet.isEmpty then none else some h.pqRatchet,
    addresses := h.addresses }

/-- Any `codec` that round-trips `protoOf h body` yields a version-4 round trip for
`signalWireCodec codec`. -/
theorem signalWire_roundTrip_of_decode (codec : SignalMessageProtoCodec) (h : SignalHeader)
    (body : List (BitVec 8)) (hver : h.messageVersion = currentVersion)
    (hdec : codec.decode (codec.encode (protoOf h body)) = some (protoOf h body)) :
    (signalWireCodec codec).parse ((signalWireCodec codec).encode h body) = some (h, body) := by
  obtain ⟨ver, rk, ctr, prev, pq, addr⟩ := h
  simp only at hver
  subst hver
  set p := protoOf ⟨currentVersion, rk, ctr, prev, pq, addr⟩ body with hp
  have henc : (signalWireCodec codec).encode ⟨currentVersion, rk, ctr, prev, pq, addr⟩
      body = versionByte currentVersion :: codec.encode p := rfl
  rw [henc]
  simp only [signalWireCodec]
  generalize hval : versionByte currentVersion :: codec.encode p ++
      List.replicate macLength 0 = value
  have hlen : ¬ value.length < macLength + 1 := by
    subst hval; simp [macLength]
  have hhead : value.headD 0 >>> 4 = currentVersion := by
    subst hval; exact versionByte_currentVersion_shift
  have hslice : codec.decode ((value.take (value.length - macLength)).drop 1) = some p := by
    subst hval
    rw [List.length_append, List.length_replicate, Nat.add_sub_cancel, List.take_left]
    exact hdec
  have h34 : ¬ currentVersion < preKyberVersion := by decide
  have h44 : ¬ currentVersion < currentVersion := by decide
  have hrk : p.ratchetKey = some rk.serialize := rfl
  have hctr : p.counter = some ctr := rfl
  have hct : p.ciphertext = some body := rfl
  have hprev : p.previousCounter = some prev := rfl
  have hpqf : p.pqRatchet.getD [] = pq := by
    simp only [hp, protoOf]; split <;> simp_all [List.isEmpty_iff]
  have haddrf : p.addresses = addr := rfl
  unfold SignalMessage.tryFrom
  simp only [hlen, hhead, h34, h44, hslice, hrk, hctr, hct, publicKey_deserialize_serialize,
    ite_false, bind, pure, Except.bind, Except.pure, throw, throwThe, MonadExceptOf.throw]
  simp only [SignalMessage.header, hprev, Option.getD_some, hpqf, haddrf]

/-- Restricted round trip of `signalWireCodec` at `protoSignalCodec` for `SignalWireShort` inputs. -/
theorem signalRoundTripShort_proto : SignalRoundTripShort protoSignalCodec := by
  intro h body hv
  obtain ⟨hver, hpq, haddr, hbody⟩ := hv
  have h63 : rustLenBound < 2 ^ 64 := by unfold rustLenBound; norm_num
  refine signalWire_roundTrip_of_decode protoSignalCodec h body hver
    (protoSignalCodec_roundTrip _ ?_)
  intro v hv
  rcases hv with hv | hv | hv | hv
  · simp only [protoOf, Option.some.injEq] at hv
    subst hv; rw [publicKey_serialize_length]; norm_num
  · simp only [protoOf, Option.some.injEq] at hv
    subst hv; omega
  · simp only [protoOf] at hv
    split at hv
    · exact absurd hv (by simp)
    · simp only [Option.some.injEq] at hv; subst hv; omega
  · have := haddr v hv; omega

private theorem encodeVarintAux_length_le : ∀ (k : ℕ) (v : BitVec 64),
    (encodeVarintAux k v).length ≤ k
  | 0, _ => by simp [encodeVarintAux]
  | k + 1, v => by
    unfold encodeVarintAux
    split_ifs
    · simp
    · simp only [List.length_cons]
      have := encodeVarintAux_length_le k (v >>> 7)
      omega

private theorem encodeVarint_length_le (v : BitVec 64) : (encodeVarint v).length ≤ 10 :=
  encodeVarintAux_length_le 10 v

private theorem encodeKey_length_le (tag : ℕ) (wt : WireType) : (encodeKey tag wt).length ≤ 10 :=
  encodeVarint_length_le _

private theorem encodeBytesField_some_length_le (tag : ℕ) (v : List (BitVec 8)) :
    (encodeBytesField tag (some v)).length ≤ 20 + v.length := by
  simp only [encodeBytesField, List.length_append]
  have h1 := encodeKey_length_le tag .lengthDelimited
  have h2 := encodeVarint_length_le (BitVec.ofNat 64 v.length)
  omega

private theorem encodeUint32Field_length_le (tag : ℕ) (opt : Option (BitVec 32)) :
    (encodeUint32Field tag opt).length ≤ 20 := by
  cases opt with
  | none => simp [encodeUint32Field]
  | some v =>
    simp only [encodeUint32Field, List.length_append]
    have h1 := encodeKey_length_le tag .varint
    have h2 := encodeVarint_length_le (v.zeroExtend 64)
    omega

/-- Encoded wire plus 8-byte MAC fits in `< 2 ^ 32` bytes at `protoSignalCodec` under bounded field
lengths. -/
theorem signalEncodeFits32_proto : SignalEncodeFits32 protoSignalCodec := by
  intro h body hpq haddr hbody
  have henc : ((signalWireCodec protoSignalCodec).encode h body).length =
      (encode (protoOf h body)).length + 1 := rfl
  rw [henc]
  simp only [encode, protoOf, List.length_append]
  have hf1 : (encodeBytesField 1 (some h.senderRatchetKey.serialize)).length ≤ 53 := by
    have := encodeBytesField_some_length_le 1 h.senderRatchetKey.serialize
    rw [publicKey_serialize_length] at this
    omega
  have hf2 := encodeUint32Field_length_le 2 (some h.counter)
  have hf3 := encodeUint32Field_length_le 3 (some h.previousCounter)
  have hf4 := encodeBytesField_some_length_le 4 body
  have hf5 : (encodeBytesField 5
      (if h.pqRatchet.isEmpty then none else some h.pqRatchet)).length ≤
      20 + h.pqRatchet.length := by
    split_ifs
    · simp [encodeBytesField]
    · exact encodeBytesField_some_length_le 5 h.pqRatchet
  have hf6 : (encodeBytesField 6 h.addresses).length < 20 + 2 ^ 29 := by
    cases had : h.addresses with
    | none => simp [encodeBytesField]
    | some a =>
      have ha := haddr a had
      have hb := encodeBytesField_some_length_le 6 a
      omega
  omega

section Ideal

instance encodableBitVec (n : ℕ) : Encodable (BitVec n) :=
  Encodable.ofEquiv (Fin (2 ^ n)) ⟨BitVec.toFin, BitVec.ofFin, fun _ => rfl, fun _ => rfl⟩

def protoEquivProd : ProtoSignalMessage ≃
    Option (List (BitVec 8)) × Option (BitVec 32) × Option (BitVec 32) ×
      Option (List (BitVec 8)) × Option (List (BitVec 8)) × Option (List (BitVec 8)) where
  toFun m := (m.ratchetKey, m.counter, m.previousCounter, m.ciphertext, m.pqRatchet, m.addresses)
  invFun x := ⟨x.1, x.2.1, x.2.2.1, x.2.2.2.1, x.2.2.2.2.1, x.2.2.2.2.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

instance encodableProto : Encodable ProtoSignalMessage :=
  Encodable.ofEquiv _ protoEquivProd

end Ideal

section LibsignalSM

open CryptoGames CryptoGames.LibsignalSM CryptoGames.Ratchet CryptoGames.Ratchet.LibsignalInst CryptoGames.CKA
  OracleComp ENNReal

/-- Session refinement `Refine.LibSim` instantiated at `protoSignalCodec`. -/
theorem libsignal_refines_proto {Pt PQ PQC : Type} [DecidableEq Pt] [Zero Pt] [SampleableType Pt]
    [Inhabited PQ] [SampleableType PQC] (P : Params PQ PQC) (hP : P.codec = protoSignalCodec)
    (ℓ : ℕ) (Dh : DHFun (BitVec 256) Pt)
    (encPt : Pt → List (BitVec 8)) (encT : Pt → PublicKey) (decT : PublicKey → Option Pt)
    (hX : X25519RealizesDh P.C Dh encPt encT) (hdec : ∀ T, decT (encT T) = some T)
    (hL : LengthsOk P ℓ)
    (hinj : Function.Injective encT) (hdum : ∀ T, encT T ≠ dummyKey) (hz : ∀ x, Dh.dh x 0 = 0)
    (hS : Corr.SpqrOffCorrect P.spqr) (idOf : Party → IdentityKey)
    (hid : idOf .A = P.idA ∧ idOf .B = P.idB) (lam : Pt) (qep q : ℕ) (hq32 : q < 2 ^ 32) (δ : ℝ≥0∞)
    (hδ : ∀ Q : Pt, 𝒟[($ᵗ BitVec 256 : ProbComp (BitVec 256))] {x | Dh.dh x Dh.base = Q} ≤ δ) :
    Refine.LibSim P ℓ Dh encPt encT decT idOf lam qep q ((qep + 2) * (q + qep + 2) * δ) :=
  Refine.libsignal_refines P ℓ Dh encPt encT decT hX hdec
    (by rw [hP]; exact signalRoundTripShort_proto) hL (by rw [hP]; exact signalEncodeFits32_proto) hinj hdum hz hS idOf hid lam qep q hq32 δ hδ

/-- SPQR switched off: empty state, empty messages, no salt. -/
def spqrOff : Spqr Unit Unit :=
  ⟨fun _ _ => (), fun _ _ => some ((), none, []), fun _ _ => .ok ((), none), fun _ _ => false,
    fun _ _ => false⟩

end LibsignalSM

end CryptoVerification.LibsignalSession
