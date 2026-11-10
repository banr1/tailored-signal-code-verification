/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Computational.Proofs.E2E.SignedFSStages
public import Computational.Proofs.CryptoGames.SM.ReductionsQueries
import Computational.Proofs.CryptoGames.Ratchet.SessionProofs.IndexRestrictions
import Computational.Proofs.CryptoGames.Ratchet.SessionProofs.ProstCodec.FSAEADBound
import Computational.Proofs.CryptoGames.Ratchet.SessionProofs.ProstCodec.MsgAeadCorrect
import Computational.Proofs.CryptoGames.Ratchet.SessionProofs.ProstCodec.PubToAD
import Computational.Proofs.CryptoGames.Ratchet.SessionProofs.SignedPubToAD
import Computational.Proofs.E2E.SignedThm5Gen
import ProofLib.Lemmas

/-!
# Signed FS-AEAD bound on mixtures

Proves the mixture analogue of `ProstFSAEADBound.lFS_full_bound_short_proof`, bounding the bias
of a prefix-indexed mixture of `lFS` games by `fsShortBoundMix` with single averaged reductions
against `lChainPRG`, `lSaltPRF32`, and `lWire`.
-/

@[expose] public section

open OracleComp OracleSpec MeasureTheory ENNReal

namespace CryptoVerification.E2E.Signed.FSMix

open CryptoGames CryptoGames.LibsignalSM.Proofs
open CryptoGames.Ratchet CryptoGames.Ratchet.LibsignalInst CryptoGames.LibsignalSession
open CryptoGames.FSAEAD.Thm5
open HMAC HKDF CBC LibsignalAead SM SM.Construction CKA

variable {Pt : Type} [DecidableEq Pt] {α : Type}

abbrev fsAp (codec : SignalMessageProtoCodec) {ℓ : ℕ}
    (A : FSAEAD.RatchetAdversary (BitVec 256) (BitVec 256) (Header Pt) (LibsignalMsgPublicPart × Plain ℓ)
      LibsignalCiphertextWithSalt32) :=
  FSAEAD.pubRed (fun c : ℕ × LibsignalCiphertextWithSalt32 => lPubOf codec c.2) A

abbrev fsB (C : Crypto) (codec : SignalMessageProtoCodec) (ℓ : ℕ) (encT : Pt → PublicKey)
    (idO : Party → IdentityKey) (maxSkip q : ℕ) (la : Bool)
    (A : FSAEAD.RatchetAdversary (BitVec 256) (BitVec 256) (Header Pt) (LibsignalMsgPublicPart × Plain ℓ)
      LibsignalCiphertextWithSalt32) :=
  multiSlotOtccaReduction (lIdeal C codec ℓ encT) (lAeadR C codec ℓ encT idO) (lChainPRG C.F) maxSkip
    (if la then q + (maxSkip + 1) else q) la (fsAp codec A)

noncomputable def fsPrgMix (C : Crypto) (codec : SignalMessageProtoCodec) (ℓ : ℕ) (encT : Pt → PublicKey)
    (oa : ProbComp α) (idOf : α → Party → IdentityKey) (maxSkip : ℕ)
    (A : α → FSAEAD.RatchetAdversary (BitVec 256) (BitVec 256) (Header Pt) (LibsignalMsgPublicPart × Plain ℓ)
      LibsignalCiphertextWithSalt32) (m : ℕ) : ℝ≥0∞ :=
  (lChainPRG C.F (m / 2)).prgAdvantage
    (prgAvg oa fun o => cumulativeChainPrgReduction (lIdeal C codec ℓ encT) (lAeadR C codec ℓ encT (idOf o))
      (lChainPRG C.F) maxSkip m (fsAp codec (A o)))

noncomputable def fsSWMix (C : Crypto) (codec : SignalMessageProtoCodec) (ℓ : ℕ) (encT : Pt → PublicKey)
    (oa : ProbComp α) (idOf : α → Party → IdentityKey) (maxSkip q : ℕ)
    (A : α → FSAEAD.RatchetAdversary (BitVec 256) (BitVec 256) (Header Pt) (LibsignalMsgPublicPart × Plain ℓ)
      LibsignalCiphertextWithSalt32) (m : ℕ) : ℝ≥0∞ :=
  2 * (lSaltPRF32 C.F).prfAdvantage
      (prfAvg oa fun o => lSaltRed C codec ℓ encT (idOf o)
        (slotSaltRed C codec ℓ encT (idOf o) (if isLookaheadHop m then q + (maxSkip + 1) else q) (m / 2)
          (fsB C codec ℓ encT (idOf o) maxSkip q (isLookaheadHop m) (A o)))) +
    (lWire C codec ℓ).wireOtccaAdvantage
      (wireAvg oa fun o => lWireRed C codec ℓ encT (idOf o) 0
        (slotWireRed C codec ℓ encT (idOf o) (m / 2)
          (fsB C codec ℓ encT (idOf o) maxSkip q (isLookaheadHop m) (A o))))

/-- Averaged FS-AEAD short bound over a prefix distribution `oa`. -/
noncomputable def fsShortBoundMix (C : Crypto) (codec : SignalMessageProtoCodec) (ℓ : ℕ) (encT : Pt → PublicKey)
    (oa : ProbComp α) (idOf : α → Party → IdentityKey) (maxSkip q qd : ℕ)
    (A : α → FSAEAD.RatchetAdversary (BitVec 256) (BitVec 256) (Header Pt) (LibsignalMsgPublicPart × Plain ℓ)
      LibsignalCiphertextWithSalt32) : ℝ≥0∞ :=
  2 * ∑ j ∈ Finset.range (slotCount maxSkip q),
      (fsPrgMix C codec ℓ encT oa idOf maxSkip A (slotToHybridHopIndex q j) +
        fsSWMix C codec ℓ encT oa idOf maxSkip q A (slotToHybridHopIndex q j)) +
    4 * ((qd : ℝ≥0∞) * macForgeryProb C.F)

/-- Bounds the bias of a prefix-indexed mixture of `lFS` games by `fsShortBoundMix`. -/
theorem lFS_bound_mix (C : Crypto) (hD : ∀ k x, C.D k (C.E k x) = x)
    (codec : SignalMessageProtoCodec) (hrt : SignalRoundTripShort codec)
    (hfit : SignalEncodeFits32 codec) (ℓ : ℕ) (hℓ : ℓ + 16 < 2 ^ 31 + 16)
    (encT : Pt → PublicKey) (hinj : Function.Injective encT) (hdum : ∀ T, encT T ≠ dummyKey)
    (oa : ProbComp α) (idOf : α → Party → IdentityKey) (maxSkip : ℕ) (hms : maxSkip ≤ 25000)
    (A : α → FSAEAD.RatchetAdversary (BitVec 256) (BitVec 256) (Header Pt) (LibsignalMsgPublicPart × Plain ℓ)
      LibsignalCiphertextWithSalt32) (q qd : ℕ)
    (hq : ∀ o, FSAEAD.MakesAtMostQueries (A o) q)
    (hqd : ∀ o, FSAEAD.MakesAtMostDecQueries (A o) qd)
    (hq32 : q + 25002 < 2 ^ 32)
    (heq : ∀ o, FSAEAD.EqualPubChallenges (A o))
    (hcls : ∀ o, FSAEAD.AllQueriesInOneADClass (fun h : Header Pt => h.1) (A o))
    (hshort : ∀ o, FSAEAD.EncMsgsOk (fun m : LibsignalMsgPublicPart × Plain ℓ => m.1.shortB) (A o))
    (hinj_short : ∀ o, GuardedFSInjectShort (A o)) :
    𝒟[oa >>= fun o => FSAEAD.game (lFS C codec ℓ encT (idOf o) maxSkip) (A o)].boolBias ≤
      fsShortBoundMix C codec ℓ encT oa idOf maxSkip q qd A := by
  have hℓ_rust : ℓ + 16 < rustLenBound := by unfold rustLenBound; omega
  have hred := fun o => ProstPubToAD.pubMsg_red_on (lAead C codec ℓ encT (idOf o)) (lPubOf codec)
    LibsignalMsgPublicPart.shortB (ProstMsgAeadCorrect.lPubOf_enc_short_proof C codec hrt ℓ hℓ_rust encT (idOf o))
    (lChainPRG C.F) maxSkip (fun h : Header Pt => h.1) (A o) q (hq o) (heq o) (hcls o) (hshort o)
  have hq' : ∀ o, FSAEAD.MakesAtMostQueries (fsAp codec (A o)) q := fun o => (hred o).1
  have hA' : ∀ o, FSAEAD.EncADsOk (fun ap : Header Pt × LibsignalMsgPublicPart => ap.2.shortB) (fsAp codec (A o)) :=
    fun o => (hred o).2.2.1
  have hinj_A' : ∀ o, GuardedFSInjectShort (fsAp codec (A o)) := fun o =>
    ProstFSAEADBound.pubRed_guardedFSInjectShort _ (A o) (hinj_short o)
  have hqd' : ∀ o, FSAEAD.MakesAtMostDecQueries (fsAp codec (A o)) qd := fun o =>
    IndexRestrictions.pubRed_makesAtMostDecQueries _ (A o) (hqd o)
  have hcls' : ∀ o, FSAEAD.AllQueriesInOneADClass (fun ap : Header Pt × LibsignalMsgPublicPart => ap.1.1) (fsAp codec (A o)) :=
    fun o => IndexRestrictions.pubRed_adClassConst (fun h : Header Pt => h.1) _ (A o) (hcls o)
  have hgame : ∀ o, 𝒟[FSAEAD.game (lFS C codec ℓ encT (idOf o) maxSkip) (A o)] =
      𝒟[FSAEAD.game (FSAEAD.fromAEADPRG (lAeadR C codec ℓ encT (idOf o)) (lChainPRG C.F) maxSkip)
        (fsAp codec (A o))] := fun o =>
    congrArg evalDist (SignedPubToAD.game_pubMsg_eq_on (lAead C codec ℓ encT (idOf o))
      (lPubOf codec) (lChainPRG C.F) maxSkip LibsignalMsgPublicPart.shortB
      (ProstMsgAeadCorrect.lPubOf_enc_short_proof C codec hrt ℓ hℓ_rust encT (idOf o))
      (A o) (heq o) (hshort o))
  rw [Thm5Mix.evalDist_mix_congr oa hgame]
  have hthm5 := Thm5Mix.theorem5_mix_multi (lIdeal C codec ℓ encT) (lChainPRG C.F) maxSkip oa
    (fun o => lAeadR C codec ℓ encT (idOf o)) (fun o => fsAp codec (A o))
    (fun ap : Header Pt × LibsignalMsgPublicPart => ap.2.shortB)
    (fun o => ProstMsgAeadCorrect.lAeadR_correctOn_short_proof C hD codec hrt ℓ hℓ_rust encT (idOf o))
    q hq' hA'
  have hchain : ∀ la : Bool,
      𝒟[oa >>= fun o => multiOtBranch (lIdeal C codec ℓ encT) (lAeadR C codec ℓ encT (idOf o)) true
          (if la then q + (maxSkip + 1) else q) (fsB C codec ℓ encT (idOf o) maxSkip q la (A
          o))].boolDist
        𝒟[oa >>= fun o => multiOtBranch (lIdeal C codec ℓ encT) (lAeadR C codec ℓ encT (idOf o))
          false
          (if la then q + (maxSkip + 1) else q) (fsB C codec ℓ encT (idOf o) maxSkip q la (A o))] ≤
      (∑ k ∈ Finset.range (if la then q + (maxSkip + 1) else q),
        fsSWMix C codec ℓ encT oa idOf maxSkip q A (2 * k + la.toNat)) +
        (qd : ℝ≥0∞) * macForgeryProb C.F := by
    intro la
    have hN : (if la then q + (maxSkip + 1) else q) ≤ 2 ^ 32 := by cases la <;> simp <;> omega
    refine (multiOtBranch_mix_le C codec ℓ encT oa idOf
      (fun o => fsB C codec ℓ encT (idOf o) maxSkip q la (A o)) hrt hfit hℓ hinj hdum hN
      (fun o => multiRedWith_offRange _ _ _ _ _ la (fsAp codec (A o)))
      (fun o => ProstFSAEADBound.multiRedWith_makesAtMostDecQueries _ _ _ _ _ la
        (fsAp codec (A o)) (hqd' o))
      (fun o => ProstFSAEADBound.multiRedWith_otADClassConst (fun ap : Header Pt × LibsignalMsgPublicPart => ap.1.1)
        _ _ _ _ _ la (fsAp codec (A o)) (hcls' o))
      (fun o => ProstFSAEADBound.multiRedWith_otEncADsOk (fun ap : Header Pt × LibsignalMsgPublicPart => ap.2.shortB)
        _ _ _ _ _ la (fsAp codec (A o)) (hA' o))
      (fun o => ProstFSAEADBound.multiRedWith_guardedOTDecShort C codec hfit ℓ hℓ encT (idOf o)
        maxSkip _ la (fsAp codec (A o)) (hA' o) (hinj_A' o))).trans (le_of_eq ?_)
    refine congrArg (· + (qd : ℝ≥0∞) * macForgeryProb C.F) (Finset.sum_congr rfl fun k _ => ?_)
    have hdiv : (2 * k + la.toNat) / 2 = k := by
      cases la <;> simp only [Bool.toNat_false, Bool.toNat_true] <;> omega
    have hla : isLookaheadHop (2 * k + la.toNat) = la := by
      cases la <;> simp [isLookaheadHop, Nat.add_mod]
    unfold fsSWMix
    rw [hdiv, hla]
  have hF := hchain false
  have hT := hchain true
  simp only [Bool.false_eq_true, ↓reduceIte, Bool.toNat_false, Bool.toNat_true, add_zero] at hF hT
  refine hthm5.trans ?_
  have hsplitP := sum_range_hopIdx (fsPrgMix C codec ℓ encT oa idOf maxSkip A) maxSkip q
  have hsplitSW := sum_range_hopIdx (fsSWMix C codec ℓ encT oa idOf maxSkip q A) maxSkip q
  unfold fsShortBoundMix
  rw [Finset.sum_add_distrib, hsplitSW]
  calc _ ≤ 2 * ∑ j ∈ Finset.range (slotCount maxSkip q),
          fsPrgMix C codec ℓ encT oa idOf maxSkip A (slotToHybridHopIndex q j) +
        2 * (((∑ k ∈ Finset.range q, fsSWMix C codec ℓ encT oa idOf maxSkip q A (2 * k)) +
            (qd : ℝ≥0∞) * macForgeryProb C.F) +
          ((∑ k ∈ Finset.range (q + (maxSkip + 1)),
              fsSWMix C codec ℓ encT oa idOf maxSkip q A (2 * k + 1)) +
            (qd : ℝ≥0∞) * macForgeryProb C.F)) := by
        unfold fsPrgMix
        gcongr
        · exact hF
        · exact hT
    _ = _ := by ring

end CryptoVerification.E2E.Signed.FSMix
