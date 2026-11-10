/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Symbolic.Proofs.Swarm.CREF.RecvPrekeyNew.AcceptExplainPure
public import Symbolic.Proofs.Swarm.CREF.Sanitize
public import Symbolic.Proofs.Swarm.CREF.RecvPrekeyNew.AcceptHypsPure
public import Symbolic.Proofs.Refinement.Composed.Cli.OldShape
public import Symbolic.Proofs.Swarm.CREF.Sem
import Symbolic.Proofs.Swarm.CREF.Cli.Rpk.AcceptExplainG1bPure
import Symbolic.Proofs.Swarm.CREF.Cli.Rpk.AcceptExplainG1cPure
import Symbolic.Proofs.Swarm.CREF.Cli.Rpk.CBadG2Pure
import Symbolic.Proofs.Swarm.CREF.ModelBridge
import Symbolic.Proofs.Swarm.CREF.Prelude
import Symbolic.Proofs.Swarm.CREF.RecvPrekeyNew.AcceptExplainLeafB
import Symbolic.Proofs.Swarm.CREF.RecvPrekeyNew.AcceptExplainPureA
import Symbolic.Proofs.Swarm.CREF.TR.G1.G1RepMacTR
import Symbolic.Proofs.Swarm.CREF.TR.G1.G1RepPtAtomsTR
import Symbolic.Specifications.Refinement.Concretization -- shake: keep
import Mathlib.MeasureTheory.Integral.Bochner.Basic -- shake: keep
import VCVio.Prelude.Core -- shake: keep
import Symbolic.Proofs.Swarm.CREF.TR.PQGamma -- shake: keep
import Symbolic.Proofs.Refinement.Composed.Cli.LeakRecordsCompat -- shake: keep
import Symbolic.Proofs.Swarm.CREF.Initiate.MidRngPure -- shake: keep

/-!
# Explanation Construction for Accepting Pre-Key Calls

Proves `rpk_exactRep_of_not_bobStartCollision`, `rpk_explainOK`, and `slot_rpk_hxpl`, constructing
`MatchedPrefix` and `Clean` symbolic explanations for non-colliding accepting pre-key calls.
-/

@[expose] public section

set_option autoImplicit false

cref_hide_foreign_instances

namespace Symbolic.Swarm.CREF.CliPure

cref_open
open CryptoProofLib.Refinement (ExternInterpretation)
open DY.Libsignal.TripleRatchet (TRSignalMsg parseTrSignalMsg)

theorem rpk_seedAkHyp {interpretation : ExternInterpretation}
    (hext : DY.Libsignal.Composed.Refinement.Cli.ExternContractsHoldCli interpretation) {r : ProtocolSetup} (hwf : ProtocolSetupWF r)
    {S : OpaqueSymbolSemantics} (_hSeq : S = compSemOf interpretation r) :
    RpkSeedAkHyp interpretation r S := by
  intro who g ms acc b ct_wire pt p x' msg' keys' seed' salt' st'' c'
  exact rpk_seed_ak_exactRep hwf hext.1 hext.2

/-- The inner `TRSignalMsg` parsed from any `x' ∈ preKeyRepresentations` has
`spqrHeaded msg'.mac = false`. -/
def FaithfulInnerNoSpqrMac (interpretation : ExternInterpretation) (r : ProtocolSetup) (S : OpaqueSymbolSemantics) : Prop :=
  ∀ {g : Ghost} {ms : List Move} {b : HwBytes} {p : PreKeyFields} {x' : PreKeyRep}
    {msg' : TRSignalMsg},
    parsePreKeyWire b = some p →
    x' ∈ preKeyRepresentations interpretation r S g ms b →
    parseTrSignalMsg x'.msg = some msg' →
    spqrHeaded msg'.mac = false

theorem faithfulInnerNoSpqrMac (interpretation : ExternInterpretation) (r : ProtocolSetup) (S : OpaqueSymbolSemantics) :
    FaithfulInnerNoSpqrMac interpretation r S := by
  intro g ms b p x' msg' _hp hx' hparse'
  obtain ⟨_p₀, _hp₀, msg₀, hparse₀, _, _, hspqr₀, _⟩ := hx'.2.2.2.2
  cases hparse'.symm.trans hparse₀
  exact hspqr₀

theorem rpk_notSpqrMacHyp_of_c15
    {interpretation : ExternInterpretation} {r : ProtocolSetup} {S : OpaqueSymbolSemantics}
    (hC15 : FaithfulInnerNoSpqrMac interpretation r S) :
    RpkNotSpqrMacHyp interpretation r S := by
  intro g ms b p x' msg' hp hx' hparse' _hmac_len
  exact TR.G1.notSpqrHeaded_of_spqrHeaded_eq_false (hC15 hp hx' hparse')

theorem rpk_notSpqrMacHyp (interpretation : ExternInterpretation) (r : ProtocolSetup) (S : OpaqueSymbolSemantics) :
    RpkNotSpqrMacHyp interpretation r S :=
  rpk_notSpqrMacHyp_of_c15 (faithfulInnerNoSpqrMac interpretation r S)

theorem rpk_bobTrialGuard_of_contract {interpretation : ExternInterpretation}
    {r : ProtocolSetup} {S : OpaqueSymbolSemantics} {who : List Participant}
    {ok : Nat → Bool} {opkUsed : Bool} {acc : List DY.Libsignal.HwEvents.MachineEvent}
    {sm : DY.Libsignal.HwEvents.StateAndMessage} {b : HwBytes}
    {p : PreKeyFields} {d ct_wire pt : HwBytes}
    {g' : Ghost} {ms' : List Move} {x' : PreKeyRep} {msg' : TRSignalMsg}
    (hEq : DY.Libsignal.Refinement.ExternCryptoLawsHold interpretation)
    (hne : r.alice ≠ r.bob)
    (hC : RecvAcceptContractPure interpretation r opkUsed b sm p d ct_wire pt)
    (hCOpk : COpkRelC interpretation r S who ok opkUsed acc)
    (hc' : Clean interpretation r S who ok g' ms' acc)
    (hx' : x' ∈ preKeyRepresentations interpretation r S g' ms' b)
    (hparse' : parseTrSignalMsg x'.msg = some msg') :
    MacInv.BobTrialGuard r (runTraceMoves r ms') p x' msg' = true := by
  obtain ⟨hek'_gamma, _, msg₀, hparse₀, _, _, _, _, hrk'_gamma, _, _⟩ :=
    TR.rep_ek_ct_gamma interpretation r S g' ms' b p ct_wire x' hC.parse hC.kyber_ct hx'
  cases hparse'.symm.trans hparse₀
  have hek_eq : TR.ekBytes p = (p.baseKey.take 33).drop 1 := by
    simp [TR.ekBytes, List.drop_take]
  have hek_notlow : PQXDH.x25519LowOrder x'.ek = false :=
    x25519LowOrder_false_of_gamma_notLow interpretation hEq S g'
      (by rw [hek'_gamma, hek_eq]; exact hC.baseKey_ok.2.2.1)
  have hrk_notlow : TripleRatchet.x25519LowOrder msg'.ratchetKey = false :=
    x25519LowOrder_false_of_gamma_notLow interpretation hEq S g'
      (by rw [hrk'_gamma]; exact hC.ratchetKey_ok)
  have hver : msg'.version = TripleRatchet.messageVersion :=
    version_eq_messageVersion_of_preKeyRepresentations hC.parse hC.version hx' hparse'
  have hcan :
      decide (DY.X25519.leValue (((p.baseKey.take 33).drop 1).map BitVec.toNat) <
        DY.X25519.p25519) = true :=
    decide_eq_true hC.baseKey_ok.2.1
  have hver_b : decide (msg'.version = TripleRatchet.messageVersion) = true :=
    decide_eq_true hver
  unfold MacInv.BobTrialGuard Symbolic.Swarm.Stage1Trials.bobOpk?
    Symbolic.Swarm.Stage1Trials.bobTrialGuard
  rcases hC.opk_ok with hnone | ⟨hw, hu, hsome⟩
  · rw [hnone]; dsimp only [Option.any, Option.all]
    rw [hcan, hC.baseKey_ok.2.2.1, hek_notlow, hver_b, hC.ratchetKey_ok, hrk_notlow]; rfl
  · have hopk_u : PQXDH.opkUsedB (runTraceMoves r ms') r.bob
        (DY.DiffieHellman.dhPk (setupSecret r 6)) = false := by
      simpa only [← rpk_setupPublic_8 r hne hw] using hCOpk hw hu g' ms' hc'
    rw [hsome]; dsimp only
    have hcond : (r.withOpk && r.opkId == r.opkId) = true := by simp [hw]
    simp only [hcond, ↓reduceIte, Option.any, Option.all]
    rw [hcan, hC.baseKey_ok.2.2.1, hek_notlow, hver_b, hC.ratchetKey_ok, hrk_notlow, hopk_u]; rfl

theorem rpk_exactRep_of_not_bobStartCollision {interpretation : ExternInterpretation}
    {r : ProtocolSetup} (hwf : ProtocolSetupWF r)
    (hEq : DY.Libsignal.Refinement.ExternCryptoLawsHold interpretation)
    (hpubcanon : X25519PubCanonical interpretation ∧
      DY.Libsignal.PQXDH.Refinement.X25519TorsionShiftsRejected interpretation)
    {S : OpaqueSymbolSemantics} {who : List Participant} {g' : Ghost} {ms' : List Move} {acc : List MachineEvent}
    {b ct_wire pt : HwBytes} {p : PreKeyFields} {x' : PreKeyRep} {msg' : TRSignalMsg}
    {keys' : PQXDH.HandshakeKeys} {seed' salt' st'' : DY.Bytes} {c' : TripleRatchet.RecvChain}
    (hns_hyp : RpkNotSpqrMacHyp interpretation r S)
    (hseed_hyp : RpkSeedAkHyp interpretation r S)
    (hmp' : MatchedPrefix interpretation r S who g' ms' acc)
    (hp : parsePreKeyWire b = some p)
    (hnkm : ¬ KyberMismatch interpretation r p)
    (hct_wire : p.kyberCiphertext = some (kyberKey ct_wire))
    (hct_len : ct_wire.length = 1568)
    (hopk : p.preKeyId = none ∨ (r.withOpk = true ∧ p.preKeyId = some r.opkId))
    (hx' : x' ∈ preKeyRepresentations interpretation r S g' ms' b)
    (hnbsc : ¬ BobSessionStartCollidesOrImplicitRejects interpretation r S g' ms' p x')
    (hbk' : bobKeys r p x' = some keys')
    (hguard : MacInv.BobTrialGuard r (runTraceMoves r ms') p x' msg' = true)
    (hparse' : parseTrSignalMsg x'.msg = some msg')
    (hcmk' : TripleRatchet.consumeMessageKey (bobChain r keys' msg') msg'.counter = some (seed', c'))
    (hspqr' : DY.Spqr.spqrRecv (DY.Spqr.spqrInit keys'.pqr TripleRatchet.spqrB2A)
      msg'.pqRatchet (preKeySpqrIndex p) = some (st'', salt'))
    (hss' : TR.bobSaltSeed r p x' = some (salt', seed'))
    (hek_len : (gamma interpretation S g' x'.ek).length = 32)
    (hek_can : DY.X25519.leValue ((gamma interpretation S g' x'.ek).map BitVec.toNat) < DY.X25519.p25519)
    (hek_notlow : DY.X25519.isLowOrderKey ((gamma interpretation S g' x'.ek).map BitVec.toNat) = false ∧
      DY.Libsignal.PQXDH.Refinement.X25519TorsionFree interpretation (gamma interpretation S g' x'.ek))
    (hlow' : TripleRatchet.x25519LowOrder msg'.ratchetKey = false)
    (hctr : msg'.counter.toNat ≤ TripleRatchet.maxForwardJumps)
    (hmac_len : (gamma interpretation S g' msg'.mac).length = 8)
    (hmac_bytes : gamma interpretation S g'
      (TripleRatchet.computeMac (TripleRatchet.trMsgKeys salt' seed').macKey
        (PQXDH.serializedIk (setupPublic r 0))
        (PQXDH.serializedIk (setupPublic r 2)) msg'.wire) =
      gamma interpretation S g' msg'.mac)
    (hdec_wire : interpretation DY.Libsignal.Refinement.aesCbcDecryptSymbol
      [gamma interpretation S g' msg'.ciphertext,
       gamma interpretation S g' (TripleRatchet.trMsgKeys salt' seed').cipherKey,
       (gamma interpretation S g' (TripleRatchet.trMsgKeys salt' seed').iv).take 16] = some pt)
    (hpq_ne : gamma interpretation S g' msg'.pqRatchet ≠ [])
    (hpt_mac : msg'.mac ∉ plaintextTerms (runVis r ms')) :
    ∃ (x : PreKeyRep) (msg : TRSignalMsg) (salt seed pqSalt m : DY.Bytes),
      x ∈ preKeyRepresentations interpretation r S g' ms' b ∧
      PQXDH.isCanonicalKey x.ek = true ∧
      parseTrSignalMsg x.msg = some msg ∧
      TripleRatchet.x25519LowOrder msg.ratchetKey = false ∧
      TR.bobSaltSeed r p x = some (salt, seed) ∧
      pqSalt.AttackerKnows (runTraceMoves r ms') ∧
      msg.mac = TripleRatchet.computeMac (TripleRatchet.trMsgKeys pqSalt seed).macKey
        (PQXDH.serializedIk (setupPublic r 0))
        (PQXDH.serializedIk (setupPublic r 2)) msg.wire ∧
      PQXDH.errToOption (DY.SymEnc.symDec
        (TripleRatchet.trMsgKeys pqSalt seed).cipherKey
        (TripleRatchet.trMsgKeys pqSalt seed).iv msg.ciphertext) = some m ∧
      gamma interpretation S g' m = pt := by
  have hreach' : (runTraceMoves r ms').Reachable reachability := hmp'.2.1.2.2.1.1
  have hmac_ne : gamma interpretation S g' msg'.mac ≠ [] := by intro h; rw [h] at hmac_len; cases hmac_len
  have hNotMemo := MacInv.not_memoCollision_of_noBobStartCollision hparse' hnbsc
  have hNotOwn := MacInv.not_ownSaltMacCollision_of_noBobStartCollision hparse' hnbsc
  by_cases hseed_ak : seed'.AttackerKnows (runTraceMoves r ms')
  · exact hseed_hyp hmp' hp hnkm hct_wire hct_len hopk hx' hnbsc hbk' hparse' hcmk'
      hspqr' hss' hek_len hek_can hek_notlow hlow' hctr hmac_bytes hdec_wire hpq_ne hseed_ak
  · rcases MacInv.bs_g1a_case_split interpretation r S g' ms' p x' msg' keys' st'' salt' seed' c'
        hreach' hx'.2.2.1 hbk' hguard hparse' hcmk' hspqr' hmac_ne
        (hns_hyp hp hx' hparse' hmac_len) hpt_mac hNotMemo hNotOwn hmac_bytes with
      hseed_ak' | hCaseB | hCaseC
    · exact False.elim (hseed_ak hseed_ak')
    · obtain ⟨x₁, msg₁, pqSalt_s, m_s, hx₁, hcan₁, hparse₁, hlow₁, hss₁, hpq_ak,
          hmac₁, hdec₁, hpt₁⟩ :=
        rpk_bsG1bHonestSendCase hwf hEq hpubcanon hmp' hp hx' hnbsc hbk' hparse' hcmk'
          hspqr' hss' hek_len hek_can hek_notlow hlow' hdec_wire hpq_ne hseed_ak hCaseB
      exact ⟨x₁, msg₁, salt', seed', pqSalt_s, m_s,
        hx₁, hcan₁, hparse₁, hlow₁, hss₁, hpq_ak, hmac₁, hdec₁, hpt₁⟩
    · exact False.elim (rpk_not_bsG1cOwnKeyCase hwf.1 hreach' hx'.1 hx'.2.1 hx'.2.2.1
        (TR.G1.Spine.aliceKemLen32_of_matchedPrefix hmp') hbk' hparse' hcmk' hseed_ak hCaseC)

private theorem rpk_exactRep_of_not_bobStartCollision_contract {interpretation : ExternInterpretation}
    {r : ProtocolSetup} {S : OpaqueSymbolSemantics} {who : List Participant} {ok : Nat → Bool}
    {opkUsed : Bool} {acc : List MachineEvent} {sm : DY.Libsignal.HwEvents.StateAndMessage} {b : HwBytes}
    {p : PreKeyFields} {d ct_wire pt : HwBytes}
    {g' : Ghost} {ms' : List Move} {x' : PreKeyRep}
    (hext : DY.Libsignal.Composed.Refinement.Cli.ExternContractsHoldCli interpretation) (hwf : ProtocolSetupWF r)
    (hSeq : S = compSemOf interpretation r)
    (hC : RecvAcceptContractPure interpretation r opkUsed b sm p d ct_wire pt)
    (hCOpk : COpkRelC interpretation r S who ok opkUsed acc)
    (hSeedAk : RpkSeedAkHyp interpretation r S)
    (hNotSpqrMac : RpkNotSpqrMacHyp interpretation r S)
    (hnk : ¬ KyberMismatch interpretation r p)
    (hc' : Clean interpretation r S who ok g' ms' acc)
    (hx' : x' ∈ preKeyRepresentations interpretation r S g' ms' b)
    (hnbsc : ¬ BobSessionStartCollidesOrImplicitRejects interpretation r S g' ms' p x') :
    ∃ (x : PreKeyRep) (msg : TRSignalMsg) (salt seed pqSalt m : DY.Bytes),
      x ∈ preKeyRepresentations interpretation r S g' ms' b ∧
      PQXDH.isCanonicalKey x.ek = true ∧
      parseTrSignalMsg x.msg = some msg ∧
      TripleRatchet.x25519LowOrder msg.ratchetKey = false ∧
      TR.bobSaltSeed r p x = some (salt, seed) ∧
      pqSalt.AttackerKnows (runTraceMoves r ms') ∧
      msg.mac = TripleRatchet.computeMac (TripleRatchet.trMsgKeys pqSalt seed).macKey
        (PQXDH.serializedIk (setupPublic r 0))
        (PQXDH.serializedIk (setupPublic r 2)) msg.wire ∧
      PQXDH.errToOption (DY.SymEnc.symDec
        (TripleRatchet.trMsgKeys pqSalt seed).cipherKey
        (TripleRatchet.trMsgKeys pqSalt seed).iv msg.ciphertext) = some m ∧
      gamma interpretation S g' m = pt := by
  have hmp' : MatchedPrefix interpretation r S who g' ms' acc := hc'.matched
  have hne : r.alice ≠ r.bob := hwf.1
  have hS_ck : S.chainKey = Symbolic.Swarm.SHARED.SpqrBytes.spqrChainKeyOf interpretation := by
    rw [hSeq]; rfl
  have hopk_ok : p.preKeyId = none ∨
      (r.withOpk = true ∧ opkUsed = false ∧ p.preKeyId = some r.opkId) := hC.opk_ok
  have hCompat' : GhostAndSemMatchSetup interpretation r S g' := hmp'.1
  obtain ⟨hek'_gamma, _hct'_gamma, hFaith'⟩ :=
    TR.rep_ek_ct_gamma interpretation r S g' ms' b p ct_wire x' hC.parse hC.kyber_ct hx'
  rcases hFaith' with
    ⟨msg', hparse', hwire'_gamma, hmac'_gamma, _hspqr_mac, hcipher'_gamma, hrk'_gamma, hpq'_gamma, hctr'_eq, _hver'_eq⟩
  have hctr'_le : msg'.counter.toNat ≤ TripleRatchet.maxForwardJumps := by
    rw [hctr'_eq]; exact hC.counter_le
  have hpq'_ne : gamma interpretation S g' msg'.pqRatchet ≠ [] := by
    rw [hpq'_gamma]; exact hC.pqRatchet_ne_nil
  obtain ⟨keys', c'', st'', salt', seed', hbk', hcmk', hspqr', hbss', _hmac'_T⟩ :=
    bobSaltSeed_some_of_not_implicitReject hopk_ok hparse' hctr'_le hpq'_ne
  obtain ⟨hsalt'_gamma, hseed'_gamma, _⟩ :=
    TR.bobSaltSeed_gamma interpretation hext.1 r hwf S g' hCompat' opkUsed b p hC.parse hnk
      ct_wire hC.kyber_ct hC.ct_len hopk_ok hC.counter_le hC.pqRatchet_ne_nil
      ms' x' hx' msg' salt' seed' hparse' hbss'
  have hlow' : TripleRatchet.x25519LowOrder msg'.ratchetKey = false :=
    x25519LowOrder_false_of_gamma_notLow interpretation hext.1 S g'
      (by rw [hrk'_gamma]; exact hC.ratchetKey_ok)
  have hek_eq : TR.ekBytes p = (p.baseKey.take 33).drop 1 := by
    simp [TR.ekBytes, List.drop_take]
  have hek'_len : (gamma interpretation S g' x'.ek).length = 32 := by
    rw [hek'_gamma, hek_eq]; exact hC.baseKey_ok.1
  have hek'_canon :
      DY.X25519.leValue ((gamma interpretation S g' x'.ek).map BitVec.toNat) < DY.X25519.p25519 := by
    rw [hek'_gamma, hek_eq]; exact hC.baseKey_ok.2.1
  have hek'_notlow :
      DY.X25519.isLowOrderKey ((gamma interpretation S g' x'.ek).map BitVec.toNat) = false ∧
        DY.Libsignal.PQXDH.Refinement.X25519TorsionFree interpretation
          (gamma interpretation S g' x'.ek) := by
    rw [hek'_gamma, hek_eq]; exact hC.baseKey_ok.2.2
  obtain ⟨hp0, hp2, _⟩ := TR.gamma_setupPublic_0_2_6 interpretation r S g' hCompat' hne
  have hmac_wire : TR.bobExpectedMacBytes interpretation r S p ct_wire =
      p.message.drop (p.message.length - 8) :=
    hC.mac_eq S hS_ck
  have hdec_wire := hC.dec_eq S hS_ck
  have hmac_T_gamma :
      gamma interpretation S g'
        (TripleRatchet.computeMac (TripleRatchet.trMsgKeys salt' seed').macKey
          (PQXDH.serializedIk (setupPublic r 0))
          (PQXDH.serializedIk (setupPublic r 2)) msg'.wire) =
        gamma interpretation S g' msg'.mac := by
    have hT : gamma interpretation S g'
        (TripleRatchet.computeMac (TripleRatchet.trMsgKeys salt' seed').macKey
          (PQXDH.serializedIk (setupPublic r 0))
          (PQXDH.serializedIk (setupPublic r 2)) msg'.wire) =
        TR.bobExpectedMacBytes interpretation r S p ct_wire := by
      rw [TR.gamma_computeMac, TR.gamma_trMsgKeys_macKey, hsalt'_gamma, hseed'_gamma,
        TR.gamma_serializedIk, TR.gamma_serializedIk, hp0, hp2, hwire'_gamma]; rfl
    rw [hT, hmac_wire, hmac'_gamma]
  have hdec_salt'_seed' :
      interpretation DY.Libsignal.Refinement.aesCbcDecryptSymbol
        [gamma interpretation S g' msg'.ciphertext,
         gamma interpretation S g' (TripleRatchet.trMsgKeys salt' seed').cipherKey,
         (gamma interpretation S g' (TripleRatchet.trMsgKeys salt' seed').iv).take 16] = some pt := by
    rw [hcipher'_gamma, TR.gamma_trMsgKeys_cipherKey, TR.gamma_trMsgKeys_iv,
      hsalt'_gamma, hseed'_gamma]; exact hdec_wire
  have hopk_ok₂ : p.preKeyId = none ∨ (r.withOpk = true ∧ p.preKeyId = some r.opkId) :=
    hopk_ok.imp id fun ⟨h1, _, h2⟩ => ⟨h1, h2⟩
  have hcmac_len :
      (gamma interpretation S g'
        (TripleRatchet.computeMac (TripleRatchet.trMsgKeys salt' seed').macKey
          (PQXDH.serializedIk (setupPublic r 0))
          (PQXDH.serializedIk (setupPublic r 2)) msg'.wire)).length = 8 := by
    rw [TR.gamma_computeMac]
    unfold TR.computeMacBytes
    rw [List.length_take, TR.length_hmacWith]; decide
  have hmac_len : (gamma interpretation S g' msg'.mac).length = 8 := by
    rw [← hmac_T_gamma]; exact hcmac_len
  have hpt_mac : msg'.mac ∉ plaintextTerms (runVis r ms') := by
    have h0 := TR.G1.g1_rep_ptAtoms_tr r ms' [] (fun _ h => nomatch h) hparse'
    rwa [List.append_nil] at h0
  have hguard :=
    rpk_bobTrialGuard_of_contract hext.1 hwf.1 hC hCOpk hc' hx' hparse'
  exact rpk_exactRep_of_not_bobStartCollision hwf hext.1 hext.2 hNotSpqrMac hSeedAk
    hmp' hC.parse hnk hC.kyber_ct hC.ct_len hopk_ok₂ hx' hnbsc hbk' hguard hparse' hcmk' hspqr'
    hbss' hek'_len hek'_canon hek'_notlow hlow' hctr'_le hmac_len hmac_T_gamma hdec_salt'_seed'
    hpq'_ne hpt_mac

@[simp] theorem rpk_bobStartCollision_sanitizeMoves {interpretation : ExternInterpretation}
    {r : ProtocolSetup} {S : OpaqueSymbolSemantics} {g : Ghost} {ms : List Move}
    {p : PreKeyFields} {x : PreKeyRep} :
    BobSessionStartCollidesOrImplicitRejects interpretation r S g (Sanitize.sanitizeMoves (setupTrace r) ms) p x ↔
      BobSessionStartCollidesOrImplicitRejects interpretation r S g ms p x := by
  simp only [BobSessionStartCollidesOrImplicitRejects, Sanitize.runTrace_sanitizeMoves,
    Sanitize.runVis_sanitizeMoves, Sanitize.honestSalts_sanitizeMoves]

private theorem rpk_clearStuckWrap_prekeyPath?_imp {tr : ExecTrace} {m : Move} {promote : Bool}
    (hp : (Sanitize.clearStuckWrap tr m).prekeyPath? = some promote) :
    m.prekeyPath? = some promote := by
  cases m <;> simp only [Sanitize.clearStuckWrap, Move.prekeyPath?] at hp ⊢
  case bobStart => exact hp
  case decrypt me si mi pq sp w => revert hp; cases (tr.getMessageSentAt mi).isSome <;> simp
  case decryptSkipped me si mi k pq sp w => revert hp; cases (tr.getMessageSentAt mi).isSome <;> simp
  all_goals cases hp

private theorem rpk_sanitize_clean {interpretation : ExternInterpretation} {r : ProtocolSetup}
    {S : OpaqueSymbolSemantics} {who : List Participant} {ok : Nat → Bool} {g : Ghost} {ms : List Move}
    {acc : List MachineEvent} (hc : Clean interpretation r S who ok g ms acc) :
    Clean interpretation r S who ok g (Sanitize.sanitizeMoves (setupTrace r) ms) acc := by
  let ms_s := Sanitize.sanitizeMoves (setupTrace r) ms
  have hpath_s : PathFaithful interpretation r S g ms_s acc := by
    intro i m' promote b' p hi hpath hcall hparse
    rw [Sanitize.getElem?_sanitizeMoves] at hi
    rcases hmi : ms[i]? with _ | m
    · simp [hmi] at hi
    · simp only [hmi, Option.map_some, Option.some.injEq] at hi
      subst hi
      simp only [ms_s, Sanitize.sanitizeMoves_take, Sanitize.runVis_sanitizeMoves,
        Sanitize.runTrace_sanitizeMoves] at hcall ⊢
      exact hc.matched.2.2.2.1 i m promote b' p hmi
        (rpk_clearStuckWrap_prekeyPath?_imp hpath) hcall hparse
  exact ⟨⟨⟨hc.matched.1, Sanitize.modelRun_sanitizeMoves hc.matched.2.1,
    Sanitize.roleFaithful_sanitizeMoves hc.matched.2.2.1, hpath_s,
    Sanitize.readFaithful_sanitizeMoves hc.matched.2.2.2.2.1,
    by simpa [ms_s] using hc.matched.2.2.2.2.2⟩,
    Sanitize.outcomeFaithful_sanitizeMoves hc.1.2⟩,
    mt Sanitize.readCollision_sanitizeMoves_iff.mp hc.2⟩

private theorem rpk_clean_snoc_attackerSend {interpretation : ExternInterpretation}
    {r : ProtocolSetup} {S : OpaqueSymbolSemantics} {who : List Participant} {ok : Nat → Bool}
    {g : Ghost} {ms : List Move} {acc : List MachineEvent} {t : DY.Bytes}
    (hc : Clean interpretation r S who ok g ms acc)
    (ht : t.AttackerKnows (runTraceMoves r ms)) :
    Clean interpretation r S who ok g (ms ++ [.attackerSend t]) acc :=
  DY.Libsignal.Composed.Refinement.clean_attackerSend hc
    (by rw [DY.Libsignal.Composed.Refinement.runTrace_snoc]; exact b5_attackerSend_reachable hc.matched.2.1.2.2.1.1 t ht)

private theorem rpk_callCount_lt_snoc_attackerSend {r : ProtocolSetup} {ms : List Move}
    {acc : List MachineEvent} {t : DY.Bytes}
    (hlt : ∀ i (m : Move) promote, ms[i]? = some m → m.prekeyPath? = some promote →
      callCount (runVis r (ms.take i)) < (callStarts acc).length) :
    ∀ i (m : Move) promote, (ms ++ [Move.attackerSend t])[i]? = some m →
      m.prekeyPath? = some promote →
      callCount (runVis r ((ms ++ [Move.attackerSend t]).take i)) < (callStarts acc).length := by
  intro i m promote hi hpath
  rcases Nat.lt_or_ge i ms.length with hlt_i | hge_i
  · rw [List.getElem?_append_left hlt_i] at hi
    rw [List.take_append_of_le_length hlt_i.le]
    exact hlt i m promote hi hpath
  · rcases Nat.eq_or_lt_of_le hge_i with rfl | hgt_i
    · simp only [List.getElem?_append_right (le_refl _), Nat.sub_self,
        List.getElem?_cons_zero, Option.some.injEq] at hi
      subst hi; cases hpath
    · rw [List.getElem?_eq_none (by simp; omega)] at hi; cases hi

private theorem rpk_clean_snoc_bobStart {interpretation : ExternInterpretation}
    {r : ProtocolSetup} {S : OpaqueSymbolSemantics} {who : List Participant} {ok : Nat → Bool}
    {g : Ghost} {ms : List Move} {acc : List MachineEvent}
    {b d pt : HwBytes} {kh : PQXDH.BobKeyHandles} {mh : PQXDH.PreKeyMsgHandles}
    {pqIdx : Nat} {spqrMsgIdx : UInt32}
    (hc : Clean interpretation r S who ok g ms acc)
    (hmp_out : MatchedPrefix interpretation r S who g
      (ms ++ [Move.bobStart r.bob r.alice kh 1 mh pqIdx spqrMsgIdx 3])
      (acc ++ [.recv b, .rng d, .accept pt]))
    (hok : ok (callStarts acc).length = true) :
    Clean interpretation r S who ok g
      (ms ++ [Move.bobStart r.bob r.alice kh 1 mh pqIdx spqrMsgIdx 3])
      (acc ++ [.recv b, .rng d, .accept pt]) := by
  let mBob := Move.bobStart r.bob r.alice kh 1 mh pqIdx spqrMsgIdx 3
  have hof_out : OutcomeFaithful r ok (ms ++ [mBob]) := by
    intro i m hi
    rcases Nat.lt_or_ge i ms.length with hlt | hge
    · rw [List.getElem?_append_left hlt] at hi
      simpa only [List.take_append_of_le_length hlt.le] using hc.1.2 i m hi
    · rcases Nat.eq_or_lt_of_le hge with rfl | hgt
      · simp only [List.getElem?_append_right (le_refl _), Nat.sub_self,
          List.getElem?_cons_zero, Option.some.injEq] at hi
        subst hi
        dsimp only
        have htk : (ms ++ [mBob]).take ms.length = ms := by simp
        rw [htk, DY.Libsignal.Composed.Refinement.matchedPrefix_callCount_eq hc.matched]
        exact ⟨(fun _ hrej => nomatch hrej), fun _ => hok⟩
      · rw [List.getElem?_eq_none (by simp; omega)] at hi; cases hi
  have hnd_out : ¬ ReadCollision interpretation r S g (ms ++ [mBob])
      (acc ++ [.recv b, .rng d, .accept pt]) :=
    not_readCollision_append_of_no_decrypt hc.not_readCollision
      (DY.Libsignal.Composed.Refinement.matchedPrefix_length_eq hc.matched)
      (by intro m hm _; simp only [List.mem_singleton] at hm; subst hm; rfl)
      (by intro pt' h; cases h)
  exact ⟨⟨hmp_out, hof_out⟩, hnd_out⟩

private theorem rpk_not_preKeyExcused_of_not_collisionAt
    {interpretation : ExternInterpretation} {r : ProtocolSetup} {S : OpaqueSymbolSemantics}
    {who : List Participant} {ok : Nat → Bool} {g : Ghost} {ms : List Move}
    {acc : List MachineEvent} {b d pt : HwBytes} {p : PreKeyFields}
    (hexpl : ExplainsMoves interpretation r S who ok g ms acc)
    (hp : parsePreKeyWire b = some p)
    (hnk : ¬ KnownBaseKey interpretation r S g ms p)
    (hncol : ¬ CollisionAt interpretation r S who ok (acc ++ [.recv b, .rng d, .accept pt])) :
    ¬ PreKeyExcused interpretation r S who ok g ms acc b p := by
  intro hexc
  rcases b with _ | ⟨tag, body⟩
  · cases hp
  · exact hncol ⟨acc, .recv (tag :: body), [.rng d, .accept pt], g, ms, rfl, hexpl,
      ⟨pt, rfl⟩, Or.inr ⟨p, hp, Or.inr ⟨hnk, hexc⟩⟩⟩

private theorem rpk_reselect_of_not_preKeyExcused
    {interpretation : ExternInterpretation} {r : ProtocolSetup} {S : OpaqueSymbolSemantics}
    {who : List Participant} {ok : Nat → Bool} {g : Ghost} {ms : List Move}
    {acc : List MachineEvent} {b : HwBytes} {p : PreKeyFields}
    (hrep : ∃ x, x ∈ preKeyRepresentations interpretation r S g ms b)
    (hnexc : ¬ PreKeyExcused interpretation r S who ok g ms acc b p) :
    ¬ KyberMismatch interpretation r p ∧
      ∃ g' ms' x',
        Clean interpretation r S who ok g' ms' acc ∧
        x' ∈ preKeyRepresentations interpretation r S g' ms' b ∧
        ¬ BobSessionStartCollidesOrImplicitRejects interpretation r S g' ms' p x' := by
  refine ⟨fun hkm => hnexc ⟨hrep, Or.inl hkm⟩, ?_⟩
  by_contra hall
  apply hnexc
  refine ⟨hrep, Or.inr fun g' ms' hexpl' hnrc x' hx' => ?_⟩
  by_contra hcol
  exact hall ⟨g', ms', x', ⟨hexpl', hnrc⟩, hx', hcol⟩

/-- Every non-colliding accepting pre-key call admits a `MatchedPrefix` explanation and, when
`ok (callStarts acc).length = true`, a `Clean` explanation. -/
abbrev RpkExplainOKPure (interpretation : ExternInterpretation) (r : ProtocolSetup)
    (S : OpaqueSymbolSemantics) (who : List Participant) (ok : Nat → Bool) : Prop :=
  ∀ (records : Participant → Option HwBytes) (sent accepted : List HwBytes) (opkUsed : Bool)
    (acc : List MachineEvent)
    (b : HwBytes) (sm : DY.Libsignal.HwEvents.StateAndMessage) (pf : PreKeyFields)
    (d ct_wire pt : HwBytes),
    RpkAcceptHypsPure interpretation r S who ok records sent accepted opkUsed acc b sm pf d ct_wire pt →
    ¬ CollisionAt interpretation r S who ok (acc ++ [.recv b, .rng d, .accept pt]) →
    (∃ g ms, MatchedPrefix interpretation r S who g ms (acc ++ [.recv b, .rng d, .accept pt])) ∧
    (ok (callStarts acc).length = true →
      ∃ g ms, Clean interpretation r S who ok g ms (acc ++ [.recv b, .rng d, .accept pt]))

theorem rpk_explainOK (interpretation : ExternInterpretation)
    (hext : DY.Libsignal.Composed.Refinement.Cli.ExternContractsHoldCli interpretation)
    (r : ProtocolSetup) (hwf : ProtocolSetupWF r) (S : OpaqueSymbolSemantics)
    (_hS : SemReady interpretation r S) (hSeq : S = compSemOf interpretation r)
    (hSeedAk : RpkSeedAkHyp interpretation r S)
    (hNotSpqrMac : RpkNotSpqrMacHyp interpretation r S)
    (who : List Participant) (ok : Nat → Bool) :
    RpkExplainOKPure interpretation r S who ok := by
  intro records sent accepted opkUsed acc b sm p d ct_wire pt hA hcol
  have hC := hA.contract
  have hp : parsePreKeyWire b = some p := hC.parse
  obtain ⟨g₀, ms₀, hc₀⟩ := hA.ready.1
  have hrep₀ : ∃ x, x ∈ preKeyRepresentations interpretation r S g₀ ms₀ b :=
    rpk_reps_nonempty_of_contract g₀ ms₀ hA.hon hC
  have hnk₀ : ¬ KnownBaseKey interpretation r S g₀ ms₀ p := by
    rintro ⟨ek, hek, heq⟩
    have ha2 := (hA.ready.2.1.clean g₀ ms₀ hc₀).1.2.1.2.2.2
    exact hA.fresh p hp (heq ▸ ha2 ek hek)
  have hnexc : ¬ PreKeyExcused interpretation r S who ok g₀ ms₀ acc b p :=
    rpk_not_preKeyExcused_of_not_collisionAt hc₀.1 hp hnk₀ hcol
  obtain ⟨hnkm, g', ms', x', hc', hx', hnbsc⟩ :=
    rpk_reselect_of_not_preKeyExcused hrep₀ hnexc
  set ms_s := Sanitize.sanitizeMoves (setupTrace r) ms'
  have hc_s : Clean interpretation r S who ok g' ms_s acc :=
    rpk_sanitize_clean hc'
  have hlt_s : ∀ i (m : Move) promote, ms_s[i]? = some m → m.prekeyPath? = some promote →
      callCount (runVis r (ms_s.take i)) < (callStarts acc).length :=
    fun _ _ _ hi hpath => Sanitize.callCount_take_lt_of_sanitizeMoves_prekeyPath? hc'.matched hi hpath
  have hx_s : x' ∈ preKeyRepresentations interpretation r S g' ms_s b := by
    rwa [Sanitize.preKeyRepresentations_sanitizeMoves]
  have hnbsc_s : ¬ BobSessionStartCollidesOrImplicitRejects interpretation r S g' ms_s p x' := by
    rwa [rpk_bobStartCollision_sanitizeMoves]
  obtain ⟨x, msg, salt, seed, pqSalt, m, hx, hcan, hparse, hlow, hbss, hpq_ak, hmac, hdec, hpt⟩ :=
    rpk_exactRep_of_not_bobStartCollision_contract hext hwf hSeq hC hA.ready.2.2 hSeedAk hNotSpqrMac hnkm
      hc_s hx_s hnbsc_s
  let ms₁ := ms_s ++ [Move.attackerSend x.ek]
  let ms₂ := ms₁ ++ [Move.attackerSend x.ct]
  let ms₃ := ms₂ ++ [Move.attackerSend x.msg]
  let ms₄ := ms₃ ++ [Move.attackerSend pqSalt]
  have hx₁ := preKeyRepresentations_mono_append (ms' := [Move.attackerSend x.ek]) hx
  have hx₂ := preKeyRepresentations_mono_append (ms' := [Move.attackerSend x.ct]) hx₁
  have hx₃ := preKeyRepresentations_mono_append (ms' := [Move.attackerSend x.msg]) hx₂
  have hx₄ := preKeyRepresentations_mono_append (ms' := [Move.attackerSend pqSalt]) hx₃
  have hpq₃ : pqSalt.AttackerKnows (runTraceMoves r ms₃) :=
    DY.Bytes.AttackerKnows_le _ _ _ (DY.Libsignal.Composed.Refinement.runTrace_le_append r ms₂ _)
      (DY.Bytes.AttackerKnows_le _ _ _ (DY.Libsignal.Composed.Refinement.runTrace_le_append r ms₁ _)
        (DY.Bytes.AttackerKnows_le _ _ _ (DY.Libsignal.Composed.Refinement.runTrace_le_append r ms_s _) hpq_ak))
  have hc₁ := rpk_clean_snoc_attackerSend hc_s hx.1
  have hc₂ := rpk_clean_snoc_attackerSend hc₁ hx₁.2.1
  have hc₃ := rpk_clean_snoc_attackerSend hc₂ hx₂.2.2.1
  have hc₄ := rpk_clean_snoc_attackerSend hc₃ hpq₃
  have hlt₁ := rpk_callCount_lt_snoc_attackerSend hlt_s (t := x.ek)
  have hlt₂ := rpk_callCount_lt_snoc_attackerSend hlt₁ (t := x.ct)
  have hlt₃ := rpk_callCount_lt_snoc_attackerSend hlt₂ (t := x.msg)
  have hlt₄ := rpk_callCount_lt_snoc_attackerSend hlt₃ (t := pqSalt)
  let mh : PQXDH.PreKeyMsgHandles :=
    ⟨(runTraceMoves r ms_s).length, (runTraceMoves r ms₁).length, (runTraceMoves r ms₂).length⟩
  let pqIdx : Nat := (runTraceMoves r ms₃).length
  have hek₁ : (runTraceMoves r ms₁).at? mh.ek = some (Symbolic.Swarm.CREF.TR.NetE x.ek) := by
    rw [DY.Libsignal.Composed.Refinement.runTrace_snoc, b5_attackerSend_next]
    exact TR.at?_append_self _ _
  have hek₄ : (runTraceMoves r ms₄).at? mh.ek = some (Symbolic.Swarm.CREF.TR.NetE x.ek) :=
    rpk_at?_some_of_le (DY.Libsignal.Composed.Refinement.runTrace_le_append r ms₃ _)
      (rpk_at?_some_of_le (DY.Libsignal.Composed.Refinement.runTrace_le_append r ms₂ _)
        (rpk_at?_some_of_le (DY.Libsignal.Composed.Refinement.runTrace_le_append r ms₁ _) hek₁))
  have hct₂ : (runTraceMoves r ms₂).at? mh.ct = some (Symbolic.Swarm.CREF.TR.NetE x.ct) := by
    rw [DY.Libsignal.Composed.Refinement.runTrace_snoc, b5_attackerSend_next]
    exact TR.at?_append_self _ _
  have hct₄ : (runTraceMoves r ms₄).at? mh.ct = some (Symbolic.Swarm.CREF.TR.NetE x.ct) :=
    rpk_at?_some_of_le (DY.Libsignal.Composed.Refinement.runTrace_le_append r ms₃ _)
      (rpk_at?_some_of_le (DY.Libsignal.Composed.Refinement.runTrace_le_append r ms₂ _) hct₂)
  have hmsg₃ : (runTraceMoves r ms₃).at? mh.msg = some (Symbolic.Swarm.CREF.TR.NetE x.msg) := by
    rw [DY.Libsignal.Composed.Refinement.runTrace_snoc, b5_attackerSend_next]
    exact TR.at?_append_self _ _
  have hmsg₄ : (runTraceMoves r ms₄).at? mh.msg = some (Symbolic.Swarm.CREF.TR.NetE x.msg) :=
    rpk_at?_some_of_le (DY.Libsignal.Composed.Refinement.runTrace_le_append r ms₃ _) hmsg₃
  have hpq₄ : (runTraceMoves r ms₄).at? pqIdx = some (Symbolic.Swarm.CREF.TR.NetE pqSalt) := by
    rw [DY.Libsignal.Composed.Refinement.runTrace_snoc, b5_attackerSend_next]
    exact TR.at?_append_self _ _
  have hpqSalt : (((runTraceMoves r ms₄).append (Symbolic.Swarm.CREF.TR.RndE 32)).append
      (Symbolic.Swarm.CREF.TR.NetE salt)).at? pqIdx =
      some (Symbolic.Swarm.CREF.TR.NetE pqSalt) :=
    rpk_at?_some_of_le (DY.Trace.append_le _ _) (rpk_at?_some_of_le (DY.Trace.append_le _ _) hpq₄)
  have hopk_unused : r.withOpk = true → p.preKeyId = some r.opkId →
      PQXDH.opkUsedB (runTraceMoves r ms₄) r.bob (DY.DiffieHellman.dhPk (setupSecret r 6)) = false := by
    intro hw hpk
    have hu : opkUsed = false := by
      rcases hC.opk_ok with hnone | ⟨_, hu, _⟩
      · rw [hnone] at hpk; cases hpk
      · exact hu
    have h0 := hA.ready.2.2 hw hu g' ms₄ hc₄
    rwa [← rpk_setupPublic_8 r hwf.1 hw]
  have hwho_cs : who[(callStarts acc).length]? = some r.bob := hA.who_cs
  have hno_done : ∀ q, parsePreKeyWire b = some q →
      ¬ ∃ ek ∈ bobDoneBaseKeys (runTraceMoves r ms₄),
        ecKey (gamma interpretation S g' ek) = q.baseKey.take 33 := by
    intro q hq ⟨ek, hek, heq⟩
    have ha2 := (hA.ready.2.1.clean g' ms₄ hc₄).1.2.1.2.2.2
    have hmem : q.baseKey.take 33 ∈ accepted := heq ▸ ha2 ek hek
    exact hA.fresh q hq hmem
  obtain ⟨opk, _hsel, hmp_out⟩ :=
    rpk_bobStart_of_exactRep_pqSalt_at hwf.1 hc₄.matched hlt₄ hwho_cs hno_done hp hC.version hx₄
      hcan hparse hlow hbss hpqSalt hmac hdec hpt hopk_unused hek₄ hct₄ hmsg₄
  let g_out : Ghost :=
    { g' with σ := TR.FreshSigma.updateFreshAt g'.σ (runTraceMoves r ms₄).length 32 d }
  let mBob := Move.bobStart r.bob r.alice (bobKeyHandlesOf opk) 1 mh pqIdx
    (preKeySpqrIndex p) 3
  refine ⟨⟨g_out, ms₄ ++ [mBob], hmp_out⟩, fun hok_cs => ?_⟩
  have hfr : CBadSigmaFrame g' g_out (runTraceMoves r ms₄).length :=
    cBadSigmaFrame_updateFreshAt g' (Nat.le_refl _) 32 d
  have hc₄' : Clean interpretation r S who ok g_out ms₄ acc :=
    cbadG2_cleanBy_transfer hfr hc₄
  exact ⟨g_out, ms₄ ++ [mBob], rpk_clean_snoc_bobStart hc₄' hmp_out hok_cs⟩

theorem slot_rpk_hxpl (interpretation : ExternInterpretation)
    (hext : DY.Libsignal.Composed.Refinement.Cli.ExternContractsHoldCli interpretation)
    (r : ProtocolSetup) (hwf : ProtocolSetupWF r) (S : OpaqueSymbolSemantics)
    (hS : SemReady interpretation r S) (hSeq : S = compSemOf interpretation r)
    (who : List Participant) (ok : Nat → Bool) :
    RpkExplainOKPure interpretation r S who ok :=
  rpk_explainOK interpretation hext r hwf S hS hSeq
    (rpk_seedAkHyp hext hwf hSeq)
    (rpk_notSpqrMacHyp interpretation r S) who ok

end Symbolic.Swarm.CREF.CliPure
