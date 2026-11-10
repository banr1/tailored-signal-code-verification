/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Computational.Proofs.CryptoGames.Ratchet.LibsignalSessionStatements
public import Computational.Proofs.CryptoGames.Ratchet.LibsignalShortDefs
import Computational.Proofs.CryptoGames.Ratchet.LibsignalSessionStatementsShort
import Computational.Proofs.CryptoGames.Ratchet.SessionProofs.ProstCodec.SessionShort
import Computational.Proofs.CryptoGames.SM.Theorem1
import Computational.Proofs.SignalWireRoundTrip
public import Computational.Proofs.CryptoGames.Ratchet.SessionProofs.IndexRestrictions
public import Computational.Proofs.CryptoGames.Ratchet.SessionProofs.ProstCodec.PubToAD

/-!
# FS-AEAD instance bound and wire length lemmas at prost's codec

**Checked by Lean.** Discharges the round-trip and 32-bit length hypotheses of the short FS-AEAD
bound at `protoSignalCodec` via `signalRoundTripShort_proto` and `signalEncodeFits32_proto`, and
relates `macForgeryProb` and `ratchetKeyAdmissible` to their length-unguarded forms.
-/

@[expose] public section

open OracleComp OracleSpec ENNReal

namespace CryptoVerification.LibsignalSession

open CryptoVerification.LibsignalProtoCodec

open CryptoGames CryptoGames.LibsignalSM CryptoGames.LibsignalSM.Inst Ratchet LibsignalInst LibsignalSession
  HMAC HKDF CBC LibsignalAead SM SM.Construction CKA AEADScheme MACScheme WireAEAD FSAEAD

variable {Pt : Type}

/-- ACD19 Theorem 5 plus the salt and wire hops at `protoSignalCodec`, with one global MAC-forgery
hop per chain. -/
theorem lFS_full_bound_short_proto [DecidableEq Pt] (C : Crypto) (hD : ∀ k x, C.D k (C.E k x) = x)
    (codec : SignalMessageProtoCodec) (hc : codec = protoSignalCodec) (ℓ : ℕ)
    (hℓ : ℓ + 16 < 2 ^ 31 + 16)
    (encT : Pt → PublicKey) (hinj : Function.Injective encT) (hdum : ∀ T, encT T ≠ dummyKey)
    (idOf : Party → IdentityKey) (maxSkip : ℕ) (hms : maxSkip ≤ 25000)
    (A : FSAEAD.RatchetAdversary (BitVec 256) (BitVec 256) (Header Pt) (LibsignalMsgPublicPart × Plain ℓ)
      LibsignalCiphertextWithSalt32) (q qd : ℕ)
    (hq : FSAEAD.MakesAtMostQueries A q)
    (hqd : FSAEAD.MakesAtMostDecQueries A qd)
    (hq32 : q + 25002 < 2 ^ 32)
    (heq : FSAEAD.EqualPubChallenges A)
    (hcls : FSAEAD.AllQueriesInOneADClass (fun h : Header Pt => h.1) A)
    (hshort : FSAEAD.EncMsgsOk (fun m : LibsignalMsgPublicPart × Plain ℓ => m.1.shortB) A)
    (hinj_short : GuardedFSInjectShort A) :
    let A' := FSAEAD.pubRed
      (fun c : ℕ × LibsignalCiphertextWithSalt32 => lPubOf codec c.2) A
    let B (la : Bool) := FSAEAD.Thm5.multiSlotOtccaReduction (lIdeal C codec ℓ encT)
      (lAeadR C codec ℓ encT idOf) (lChainPRG C.F) maxSkip
      (if la then q + (maxSkip + 1) else q) la A'
    FSAEAD.advantage (lFS C codec ℓ encT idOf maxSkip) A ≤
      2 * ∑ j ∈ Finset.range (FSAEAD.Thm5.slotCount maxSkip q),
        ((lChainPRG C.F (FSAEAD.Thm5.slotToHybridHopIndex q j / 2)).prgAdvantage
            (FSAEAD.Thm5.cumulativeChainPrgReduction (lIdeal C codec ℓ encT) (lAeadR C codec ℓ encT idOf)
              (lChainPRG C.F) maxSkip (FSAEAD.Thm5.slotToHybridHopIndex q j) A') +
          (2 * (lSaltPRF32 C.F).prfAdvantage
              (lSaltRed C codec ℓ encT idOf
                (slotSaltRed C codec ℓ encT idOf
                  (if FSAEAD.Thm5.isLookaheadHop (FSAEAD.Thm5.slotToHybridHopIndex q j) then q + (maxSkip + 1) else q)
                  (FSAEAD.Thm5.slotToHybridHopIndex q j / 2)
                  (B (FSAEAD.Thm5.isLookaheadHop (FSAEAD.Thm5.slotToHybridHopIndex q j))))) +
            (lWire C codec ℓ).wireOtccaAdvantage
              (lWireRed C codec ℓ encT idOf 0
                (slotWireRed C codec ℓ encT idOf (FSAEAD.Thm5.slotToHybridHopIndex q j / 2)
                  (B (FSAEAD.Thm5.isLookaheadHop (FSAEAD.Thm5.slotToHybridHopIndex q j))))))) +
      4 * ((qd : ℝ≥0∞) * macForgeryProb C.F) :=
  lFS_full_bound_short C hD codec (hc ▸ signalRoundTripShort_proto)
    (hc ▸ signalEncodeFits32_proto) ℓ hℓ encT hinj hdum idOf
    maxSkip hms A q qd hq hqd hq32 heq hcls hshort hinj_short

/-- Restricting `macForgeryProb` to `ser.length < 2 ^ 32` bounds it by the unbounded supremum. -/
theorem macForgeryProb_le_unbounded (F : ShaCompress) :
    macForgeryProb F ≤
      ⨆ (ids : SerializedIdentityKeys) (ser : List (BitVec 8)) (tag : BitVec 64),
        𝒟[do let mk ← $ᵗ DerivedMessageKeys;
              return (hmacScheme F).tag mk.2 (ids.toList ++ ser) == tag] {true} :=
  iSup₂_le fun ids ser => iSup₂_le fun _ tag =>
    le_iSup₂_of_le ids ser
      (le_iSup (fun t : BitVec 64 =>
        𝒟[do let mk ← $ᵗ DerivedMessageKeys;
              return (hmacScheme F).tag mk.2 (ids.toList ++ ser) == t] {true}) tag)

/-- On wires shorter than `2 ^ 32` bytes, `ratchetKeyAdmissible` agrees with the unguarded on-curve
check. -/
theorem ratchetKeyAdmissible_eq_of_length_lt (codec : SignalMessageProtoCodec)
    (decT : PublicKey → Option Pt) (encT : Pt → PublicKey) (w : List (BitVec 8))
    (hw : w.length < 2 ^ 32) :
    ratchetKeyAdmissible codec decT encT w =
      (if w.length < 9 then true else
        match (signalWireCodec codec).parse (w.take (w.length - 8)) with
        | none => true
        | some (h, _) =>
          match decT h.senderRatchetKey with
          | some T => decide (encT T = h.senderRatchetKey)
          | none => false) := by
  unfold ratchetKeyAdmissible
  split_ifs with h9
  · rfl
  · rcases (signalWireCodec codec).parse (w.take (w.length - 8)) with _ | ⟨h, _⟩
    · rfl
    · dsimp only; rw [decide_eq_true hw, Bool.true_and]; rfl

variable [DecidableEq Pt] [Zero Pt] [SampleableType Pt] {PQ PQC : Type} [Inhabited PQ]
  [SampleableType PQC]

end CryptoVerification.LibsignalSession
