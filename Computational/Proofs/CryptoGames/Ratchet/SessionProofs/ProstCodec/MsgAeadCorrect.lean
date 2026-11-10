/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Computational.Proofs.CryptoGames.Ratchet.LibsignalShortDefs
import Computational.Proofs.CryptoGames.Ratchet.SessionProofs.RoundTrip
import Computational.Proofs.CryptoGames.Ratchet.WireRatchet
public import LibsignalBinary.Specifications.CryptoGames.AEAD.CBCDec
public import LibsignalBinary.Specifications.CryptoGames.AEAD.WireAeadDefs
public import LibsignalBinary.Specifications.CryptoGames.AEAD.EtM
public import LibsignalBinary.Specifications.CryptoGames.AEAD.LibsignalAead
public import LibsignalBinary.Specifications.CryptoGames.AEAD.MacPrecompDefs
public import Computational.Proofs.CryptoGames.FSAEAD.FSAEADProofDefs

/-!
# Per-message AEAD correctness and wire bounds for short public parts

**Checked by Lean.**

Proves `CorrectOn`, public-part recovery (`lPubOf_enc_short_proof`), and `< 2^32`-byte encoded wire
bounds for `lAeadR` and `lWire` on short public parts under `SignalRoundTripShort` and
`SignalEncodeFits32`.
-/

@[expose] public section

open OracleComp OracleSpec

namespace CryptoGames.LibsignalSM.Proofs.ProstMsgAeadCorrect

open CryptoGames.Ratchet CryptoGames.Ratchet.LibsignalInst CryptoGames.LibsignalSession
  CryptoGames.HMAC CryptoGames.HKDF CryptoGames.CBC CryptoGames.LibsignalAead
  CryptoGames.SM.Construction CryptoGames.AEADScheme CryptoGames.WireAEAD

variable {Pt : Type}

theorem short_lHeader {ℓ : ℕ} (hℓ : ℓ + 16 < rustLenBound) (encT : Pt → PublicKey) (i : ℕ)
    (h : Header Pt) {p : LibsignalMsgPublicPart} (hp : p.shortB = true) (body : List (BitVec 8))
    (hb : body.length = 16 * nBlocks ℓ) : SignalWireShort (lHeader encT i h p) body := by
  have h29 : 2 ^ 29 < rustLenBound := by unfold rustLenBound; decide
  simp only [LibsignalMsgPublicPart.shortB, Bool.and_eq_true, decide_eq_true_eq] at hp
  obtain ⟨hpq, haddr⟩ := hp
  refine ⟨rfl, hpq.trans h29, ?_, ?_⟩
  · intro a ha
    change p.addrs = some a at ha
    rw [ha] at haddr
    have ha29 : a.length < 2 ^ 29 := by simpa using haddr
    exact ha29.trans h29
  · rw [hb]
    unfold nBlocks
    omega

theorem lAeadK_enc_length_lt (C : Crypto) (codec : SignalMessageProtoCodec)
    (hfit : SignalEncodeFits32 codec) (ℓ : ℕ) (hℓ : ℓ + 16 < 2 ^ 31 + 16)
    (encT : Pt → PublicKey) (idOf : Party → IdentityKey)
    (mk : DerivedMessageKeys) (a : (ℕ × Header Pt) × LibsignalMsgPublicPart) (m : Plain ℓ)
    (hp : a.2.shortB = true) :
    ((lAeadK C codec ℓ encT idOf).enc mk a m).1.1.length + 8 < 2 ^ 32 := by
  simp only [LibsignalMsgPublicPart.shortB, Bool.and_eq_true, decide_eq_true_eq] at hp
  obtain ⟨hpq, haddr⟩ := hp
  dsimp only [lAeadK, lWire, libsignalWireAead, wireEncode]
  refine hfit (lHeader encT a.1.1 a.1.2 a.2) _ hpq (fun ad had => ?_) ?_
  · change a.2.addrs = some ad at had
    rw [had] at haddr
    simpa using haddr
  · rw [RoundTrip.length_cbcBody]
    unfold nBlocks
    omega

theorem lWire_encode_length_lt (C : Crypto) (codec : SignalMessageProtoCodec)
    (hfit : SignalEncodeFits32 codec) (ℓ : ℕ) (hℓ : ℓ + 16 < 2 ^ 31 + 16)
    (encT : Pt → PublicKey) (a : ℕ × (Header Pt × LibsignalMsgPublicPart))
    (hp : a.2.2.shortB = true) (c : List.Vector Block (nBlocks ℓ)) :
    ((lWire C codec ℓ).encode (lHeader encT a.1 a.2.1 a.2.2) c).length + 8 < 2 ^ 32 := by
  simp only [LibsignalMsgPublicPart.shortB, Bool.and_eq_true, decide_eq_true_eq] at hp
  obtain ⟨hpq, haddr⟩ := hp
  dsimp only [lWire, libsignalWireAead, wireEncode]
  refine hfit (lHeader encT a.1 a.2.1 a.2.2) _ hpq (fun ad had => ?_) ?_
  · change a.2.2.addrs = some ad at had
    rw [had] at haddr
    simpa using haddr
  · rw [RoundTrip.length_cbcBody]
    unfold nBlocks
    omega

theorem guardedSafePost_liftM_lIdeal {ι' : Type} {tspec : OracleSpec.{0, 0} ι'}
    {RespOk' : (t : (unifSpec + tspec).Domain) → (unifSpec + tspec).Range t → Prop}
    {Q' : (unifSpec + tspec).Domain → Prop} (hQu : ∀ u, ¬ Q' (.inl u))
    (C : Crypto) (codec : SignalMessageProtoCodec)
    (hfit : SignalEncodeFits32 codec) (ℓ : ℕ) (hℓ : ℓ + 16 < 2 ^ 31 + 16)
    (encT : Pt → PublicKey) (a : ℕ × (Header Pt × LibsignalMsgPublicPart))
    (hp : a.2.2.shortB = true) :
    CryptoGames.GuardedSafe.GuardedSafePost RespOk' Q'
      (fun e : LibsignalCiphertextWithSalt32 => e.1.1.length + 8 < 2 ^ 32)
      (liftM (lIdeal C codec ℓ encT a) :
        OracleComp (unifSpec + tspec) LibsignalCiphertextWithSalt32) := by
  change CryptoGames.GuardedSafe.GuardedSafePost RespOk' Q'
    (fun e : LibsignalCiphertextWithSalt32 => e.1.1.length + 8 < 2 ^ 32)
    (liftComp (lIdeal C codec ℓ encT a) (unifSpec + tspec))
  simp only [lIdeal, idealEnc, liftComp_bind, liftComp_pure, bind_assoc, pure_bind]
  refine (CryptoGames.GuardedSafe.GuardedSafePost.liftComp_unif hQu
    ($ᵗ List.Vector Block (nBlocks ℓ))).bind fun c _ => ?_
  refine (CryptoGames.GuardedSafe.GuardedSafePost.liftComp_unif hQu ($ᵗ BitVec 64)).bind fun _ _ => ?_
  exact CryptoGames.GuardedSafe.GuardedSafePost.pure (lWire_encode_length_lt C codec hfit ℓ hℓ encT a hp c)

theorem lAeadR_correctOn_short_proof [DecidableEq Pt] (C : Crypto)
    (hD : ∀ k x, C.D k (C.E k x) = x) (codec : SignalMessageProtoCodec) (hrt : SignalRoundTripShort codec)
    (ℓ : ℕ) (hℓ : ℓ + 16 < rustLenBound) (encT : Pt → PublicKey) (idOf : Party → IdentityKey) :
    (lAeadR C codec ℓ encT idOf).CorrectOn fun a => a.2.2.shortB := by
  intro k a m hok
  have h : (lWire C codec ℓ).dec (deriveMessageKeys C.F a.2.2.salt (keyToBytes32 k)) (lIds idOf a.2.1.1)
      ((lWire C codec ℓ).enc (deriveMessageKeys C.F a.2.2.salt (keyToBytes32 k)) (lIds idOf a.2.1.1)
        (lHeader encT a.1 a.2.1 a.2.2) m) = some (lHeader encT a.1 a.2.1 a.2.2, m.toList) := by
    simp only [lWire, libsignalWireAead, libsignalReceiveWire, wireEncode, beq_self_eq_true, ↓reduceIte]
    rw [hrt (lHeader encT a.1 a.2.1 a.2.2) _
      (short_lHeader hℓ encT a.1 a.2.1 hok _ (RoundTrip.length_cbcBody _))]
    simp only [cbcPkcs7EncryptOnly, cbcScheme]
    rw [cbcDecRaw_correct hD]
    have hok' : addressCheckPasses (none : Option (List (BitVec 8))) none = true := rfl
    simp [hok']
  simp only [lAeadR, lAead, lAeadK, lWire, ne_eq, not_true_eq_false, ↓reduceIte]
  rw [h]
  simp [fitPlain_toList]

theorem lPubOf_enc_short_proof [DecidableEq Pt] (C : Crypto) (codec : SignalMessageProtoCodec)
    (hrt : SignalRoundTripShort codec) (ℓ : ℕ) (hℓ : ℓ + 16 < rustLenBound)
    (encT : Pt → PublicKey) (idOf : Party → IdentityKey) :
    ∀ k a p m, p.shortB = true →
      lPubOf codec ((lAead C codec ℓ encT idOf).enc k (a, p) m) = some p := by
  intro k a p m hp
  simp only [lPubOf, lAead, lAeadK, lWire, libsignalWireAead, wireEncode]
  rw [hrt (lHeader encT a.1 a.2 p) _
    (short_lHeader hℓ encT a.1 a.2 hp _ (RoundTrip.length_cbcBody _))]
  cases p
  rfl

end CryptoGames.LibsignalSM.Proofs.ProstMsgAeadCorrect
