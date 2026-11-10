/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Computational.Proofs.CryptoGames.Ratchet.LibsignalSessionStatements
public import Computational.Proofs.CryptoGames.Ratchet.LibsignalShortDefs
public import Computational.Proofs.CryptoGames.FSAEAD.FSAEADProofDefs
public import Computational.Proofs.CryptoGames.FSAEAD.HybridWithProofDefs
import Computational.Proofs.CryptoGames.Ratchet.SessionProofs.ProstCodec.FSAEADBound
import Computational.Proofs.CryptoGames.Ratchet.SessionProofs.ProstCodec.MsgAeadCorrect
import Computational.Proofs.CryptoGames.Ratchet.SessionProofs.WireHop
import Computational.Proofs.CryptoGames.Ratchet.SessionProofs.ProstCodec.WireHop.Helpers

/-!
# Composed FS-AEAD bound for short public parts

**Checked by Lean.**

Composes ACD19 Theorem 5, the salt-PRF hop, and the wire OT-CCA hop for `lFS` under
`SignalRoundTripShort` and short encryption public parts (`LibsignalMsgPublicPart.shortB`).
-/

@[expose] public section

open OracleComp OracleSpec ENNReal

namespace CryptoGames.LibsignalSM.Inst

open Ratchet LibsignalInst LibsignalSession HMAC HKDF CBC LibsignalAead SM SM.Construction CKA
  AEADScheme MACScheme WireAEAD FSAEAD

variable {Pt : Type}

/-- Composed FS-AEAD advantage bound for `lFS` under `SignalRoundTripShort`, `SignalEncodeFits32`,
short encryption public parts, and `GuardedFSInjectShort`. -/
theorem lFS_full_bound_short [DecidableEq Pt] (C : Crypto) (hD : ∀ k x, C.D k (C.E k x) = x)
    (codec : SignalMessageProtoCodec) (hrt : SignalRoundTripShort codec)
    (hfit : SignalEncodeFits32 codec) (ℓ : ℕ) (hℓ : ℓ + 16 < 2 ^ 31 + 16)
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
  CryptoGames.LibsignalSM.Proofs.ProstFSAEADBound.lFS_full_bound_short_proof C hD codec hrt hfit
    ℓ hℓ encT hinj hdum idOf maxSkip hms A q qd hq hqd hq32 heq hcls hshort hinj_short

end CryptoGames.LibsignalSM.Inst

