/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Symbolic.Proofs.Swarm.CREF.Stage1Kyber -- shake: keep
public import Symbolic.Proofs.Swarm.CREF.TR.G1.ShapeIdInv
public import Symbolic.Proofs.Swarm.CREF.TR.G1.OwnKeyBranch
public import Symbolic.Proofs.Swarm.CREF.TR.SpqrSemDef
import Symbolic.Proofs.Swarm.CREF.Cli.Rpk.RecvDecStepRatchetDHAtPureA
import Symbolic.Proofs.Swarm.CREF.Cli.Rpk.RecvDecStepRatchetDHAtPureB
import Symbolic.Proofs.Swarm.CREF.Cli.Rpk.RecvDecStepSpqrHonestPure
import Symbolic.Proofs.Swarm.CREF.Prelude
import Symbolic.Proofs.Swarm.CREF.TR.G1.HonestSendBranch
import Symbolic.Proofs.Swarm.CREF.TR.G1.RatchetDHRkSwapTR
import Symbolic.Proofs.Swarm.CREF.TR.G1.ShapeAddr
import Symbolic.Proofs.Swarm.CREF.TROpen
import Symbolic.Proofs.Swarm.CREF.Cli.Rpk.RecvDecStepCommonPure -- shake: keep
import Symbolic.Proofs.Swarm.CREF.Cli.Rpk.RecvDecStepSpqrPure -- shake: keep
import Symbolic.Proofs.Swarm.CREF.TR.PQGamma -- shake: keep
import Symbolic.Proofs.Swarm.CREF.TR.PQModelRunNil -- shake: keep
import Symbolic.Proofs.Swarm.CREF.TR.RecvDec -- shake: keep

/-!
# Authentic or Swapped-Key Seed-Known Disjunction for DH Ratchet Decrypt

Derives either a `gamma`-equivalent attacker-known sender ratchet key with attacker-known message
seed or an `AuthenticDecryptRep` witness with `TermShapeId` when a DH-ratchet decrypt succeeds
without a receive collision.
-/

@[expose] public section

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

cref_hide_foreign_instances

namespace Symbolic.Swarm.CREF.CliPure.TR.RecvDecStepAt
open Symbolic.Swarm.CREF.TR hiding at?_append_of_lt gamma_concat gamma_dhPk leValue_leBytes length_leBytes newRandoms_append_rnd p25519_lt p25519_pos runMoves_append runTrace_append runTrace_snoc runVis_append runVis_snoc uOf_leBytes uOf_lt

cref_open
cref_open_tr
open DY DY.Comparse DY.Literal DY.Libsignal
open DY.Libsignal.TripleRatchet (findRecvChain chainKeyAt kdfCk computeMac messageVersion
  createChain)
open DY.Libsignal.TripleRatchet
open DY.Libsignal.Refinement (aesCbcDecryptSymbol ExternCryptoLawsHold canonicalVariation)
open DY.Libsignal.HwEvents DY.Libsignal.Rust
open CryptoGames CryptoGames.HMAC CryptoGames.HKDF
open CryptoGames.LibsignalSession CryptoGames.LibsignalSessionApi
open CryptoVerification
open CryptoVerification.LibsignalTripleRatchet CryptoVerification.LibsignalProtoCodec
open CryptoVerification.E2E CryptoVerification.E2E.Record
open CryptoVerification.E2E.Bin hiding RecordCanonical recordDeserializeOpenSpec encodeRecord
open CryptoVerification.E2E.Pqxdh.WireEntries
open CryptoVerification.E2E.Pqxdh.WireEntries.SymP3 hiding encodeRecord
open CryptoProofLib.Refinement (ExternInterpretation)
open Proofs.libsignal.RngG
open Proofs.libsignal.RngG.R3 Proofs.libsignal.RngG.CliPure.R3 Symbolic.Swarm.CREF Symbolic.Swarm.CREF.CliPure Symbolic.Swarm.CREF.CliPure.TR
open Symbolic.Swarm.CREF.TR.RecvDec (at?_append_of_lt)

/-- Under `ExplainsMoves`, `G1cAttackerBuiltSeedExcl'`, and `¬RecvCollision`, a DH-ratchet decrypt
yields either a `gamma`-equivalent `theirPk_c` whose derived seed is attacker-known or an
`AuthenticDecryptRep` witness at some honest salt. -/
theorem recv_mac_authentic_or_rkSwap_seed_known_of_not_collision_explains'
    (interpretation : ExternInterpretation) (hEq : ExternCryptoLawsHold interpretation)
    (r₀ : ProtocolSetup) (S : SpqrSem) {who : List Participant} {ok : Nat → Bool}
    (g : Ghost) (ms : List Move) {τ₁ : List MachineEvent}
    (b ptext : HwBytes) (parsed : SignalMessage)
    (hEx : ExplainsMoves interpretation r₀ S who ok g ms τ₁)
    (hABS' : Symbolic.Swarm.CREF.TR.G1.G1cAttackerBuiltSeedExcl' interpretation r₀ S g ms)
    (hreach : (runTraceMoves r₀ ms).Reachable reachability)
    (hTryFrom : SignalMessage.tryFrom protoSignalCodec b = .ok parsed)
    (t₀ : DY.Bytes) (msg₀ : TRSignalMsg) (ht₀ : t₀ ∈ recvRepresentations interpretation r₀ S g ms b)
    (hparse₀ : parseTrSignalMsg t₀ = some msg₀) (hNotCol : ¬RecvCollision interpretation r₀ S g ms t₀)
    (st₀ : TRState) (hst₀ : st₀ ∈ availableStates r₀ (runTraceMoves r₀ ms))
    (hfind : findRecvChain st₀.recv msg₀.ratchetKey = none)
    (mkSeed : DY.Bytes) (hseed : recvSeed st₀ msg₀ = some mkSeed)
    (k_own : DY.Bytes) (hk_own : k_own ∈ ownKeys r₀ (runTraceMoves r₀ ms) st₀ msg₀)
    (hMacBytes : b.drop (b.length - 8) =
      gamma interpretation S g (computeMac (trMsgKeys k_own mkSeed).macKey st₀.peerIk st₀.myIk msg₀.wire))
    (hDecOk : interpretation aesCbcDecryptSymbol
      [parsed.ciphertext, gamma interpretation S g (trMsgKeys k_own mkSeed).cipherKey,
       (gamma interpretation S g (trMsgKeys k_own mkSeed).iv).take 16] = some ptext) :
    (∃ theirPk_c : DY.Bytes,
      let seed_c := (kdfCk (chainKeyAt (createChain st₀.rk theirPk_c st₀.dhs).2 msg₀.counter.toNat)).2
      Symbolic.Swarm.CREF.TR.G1.TermShapeId theirPk_c ∧ theirPk_c.AttackerKnows (runTraceMoves r₀ ms) ∧
      gamma interpretation S g theirPk_c = gamma interpretation S g msg₀.ratchetKey ∧
      seed_c.AttackerKnows (runTraceMoves r₀ ms) ∧
      gamma interpretation S g seed_c = gamma interpretation S g mkSeed) ∨
    (∃ salt₁ ∈ honestSalts r₀ ms, Symbolic.Swarm.CREF.TR.G1.TermShapeId msg₀.ratchetKey ∧
      Symbolic.Swarm.CREF.TR.G1.AuthenticDecryptRep interpretation r₀ S g ms b ptext msg₀ st₀ mkSeed salt₁ ∧
      gamma interpretation S g (computeMac (trMsgKeys salt₁ mkSeed).macKey st₀.peerIk st₀.myIk msg₀.wire) =
        b.drop (b.length - 8) ∧
      interpretation aesCbcDecryptSymbol
        [parsed.ciphertext, gamma interpretation S g (trMsgKeys salt₁ mkSeed).cipherKey,
         (gamma interpretation S g (trMsgKeys salt₁ mkSeed).iv).take 16] = some ptext) := by
  have hrkK := Symbolic.Swarm.CREF.TR.G1.ratchetKey_attackerKnows_of_recvRepresentations
    interpretation r₀ S g ms b ht₀ hparse₀
  have hIk := Symbolic.Swarm.CREF.TR.G1.Ik.availableIkShapeId_all r₀ ms
  have hDisj : mkSeed.AttackerKnows (runTraceMoves r₀ ms) ∨
      Symbolic.Swarm.CREF.TR.G1.AuthenticDecryptRepB3_g1 interpretation r₀ S g ms b ptext msg₀ st₀ mkSeed k_own := by
    rcases Symbolic.Swarm.CREF.TR.G1.g1a_case_split interpretation r₀ S g ms b t₀ msg₀ hreach ht₀ hparse₀
        hNotCol st₀ hst₀ mkSeed hseed k_own hk_own hMacBytes with
      hSeedKnows | hCaseB | hCaseC
    · exact Or.inl hSeedKnows
    · obtain ⟨salt₁, hsalt₁, hTripleEq, pqSalt_s, seed_s, myIk_s, peerIk_s, a_s, m_s, pqMsg_s,
        ns_s, pn_s, hmac_eq, htrunc_ak, hsh_inp⟩ := hCaseB
      let wire_s := trHonestWireMsg (DY.DiffieHellman.dhPk a_s) ns_s pn_s
        (DY.SymEnc.symEnc (trMsgKeys pqSalt_s seed_s).cipherKey (trMsgKeys pqSalt_s seed_s).iv m_s) pqMsg_s
      let inp₀ := DY.Libsignal.TripleRatchet.hmac (trMsgKeys pqSalt_s seed_s).macKey
        (DY.Concat.concat myIk_s (DY.Concat.concat peerIk_s wire_s))
      have hDecOk_salt₁ : interpretation aesCbcDecryptSymbol
          [parsed.ciphertext, gamma interpretation S g (trMsgKeys salt₁ mkSeed).cipherKey,
           (gamma interpretation S g (trMsgKeys salt₁ mkSeed).iv).take 16] = some ptext := by
        rw [hTripleEq.1, hTripleEq.2.2]; exact hDecOk
      rcases Symbolic.Swarm.CREF.TR.G1.macKdfSafe_c_trunc8_inv_strong r₀ ms inp₀ hreach htrunc_ak with
        hinp_ak | ⟨pqSalt', seed', myIk', peerIk', a', ns', pn', m', pqMsg', t_s, st_s,
          hinp_eq, hpq_ak, ht'_ak, ha_eq, hst_s, hmyIk_s, hpeerIk_s, hseed_s⟩
      · exact Symbolic.Swarm.CREF.TR.G1.g1c_own_key_branch' interpretation r₀ S g ms b ptext hABS' hreach
          t₀ msg₀ ht₀ hparse₀ hNotCol st₀ hst₀ mkSeed hseed k_own
          ⟨salt₁, inp₀, hsalt₁, hTripleEq, hmac_eq, hinp_ak, hsh_inp⟩
      · right; refine ⟨salt₁, hsalt₁, hTripleEq, ?_⟩
        have hmac_eq' : msg₀.mac = computeMac (trMsgKeys pqSalt' seed').macKey myIk' peerIk'
            (trHonestWireMsg (DY.DiffieHellman.dhPk a') ns' pn'
              (DY.SymEnc.symEnc (trMsgKeys pqSalt' seed').cipherKey (trMsgKeys pqSalt' seed').iv m') pqMsg') := by
          unfold DY.Libsignal.TripleRatchet.computeMac; rw [← hinp_eq]; exact hmac_eq
        have hsh_inp' : (gamma' interpretation S g
            (DY.Libsignal.TripleRatchet.hmac (trMsgKeys pqSalt' seed').macKey
              (DY.Concat.concat myIk' (DY.Concat.concat peerIk'
                (trHonestWireMsg (DY.DiffieHellman.dhPk a') ns' pn'
                  (DY.SymEnc.symEnc (trMsgKeys pqSalt' seed').cipherKey (trMsgKeys pqSalt' seed').iv m') pqMsg'))))).shape =
            (gamma' interpretation S g
              (DY.Libsignal.TripleRatchet.hmac (trMsgKeys salt₁ mkSeed).macKey
                (DY.Concat.concat st₀.peerIk (DY.Concat.concat st₀.myIk msg₀.wire)))).shape := by
          rw [← hinp_eq]; exact hsh_inp
        have ht'_kn' : (DY.Concat.concat (trHonestWireMsg (DY.DiffieHellman.dhPk a') ns' pn'
            (DY.SymEnc.symEnc (trMsgKeys pqSalt' seed').cipherKey (trMsgKeys pqSalt' seed').iv m') pqMsg')
            msg₀.mac).AttackerKnows (runTraceMoves r₀ ms) := by rw [hmac_eq]; exact ht'_ak
        obtain ⟨_, hseed_sh, hmyIk_sh, hpeerIk_sh, hwire_sh⟩ :=
          Symbolic.Swarm.CREF.TR.G1.shape_inp_honest_inj interpretation S g hsh_inp'
        obtain ⟨v₀, pc₀, ev₀, hwire₀_eq, _⟩ :=
          Symbolic.Swarm.CREF.TR.G1.parseTrSignalMsg_eq_some_inv hparse₀
        have hwire_sh' : (gamma' interpretation S g
            (DY.TrWire.trWireMsg messageVersion (DY.DiffieHellman.dhPk a')
              ns' pn'
              (DY.SymEnc.symEnc (trMsgKeys pqSalt' seed').cipherKey (trMsgKeys pqSalt' seed').iv m')
              pqMsg' DY.Libsignal.Refinement.canonicalVariation)).shape =
            (gamma' interpretation S g
              (DY.TrWire.trWireMsg v₀ msg₀.ratchetKey msg₀.counter pc₀ msg₀.ciphertext msg₀.pqRatchet ev₀)).shape := by
          rw [← hwire₀_eq]; exact hwire_sh
        obtain ⟨_, _, hrk_sh, _, _, _, _, _⟩ :=
          Symbolic.Swarm.CREF.TR.G1.trWire_shape_eq_imp_addr_eq interpretation interpretation S S g g
            messageVersion (DY.DiffieHellman.dhPk a')
            ns' pn'
            (DY.SymEnc.symEnc (trMsgKeys pqSalt' seed').cipherKey (trMsgKeys pqSalt' seed').iv m')
            pqMsg' DY.Libsignal.Refinement.canonicalVariation
            v₀ msg₀.ratchetKey msg₀.counter pc₀ msg₀.ciphertext msg₀.pqRatchet ev₀ hwire_sh'
        have hrk_eq : DY.DiffieHellman.dhPk a' = msg₀.ratchetKey := by
          rw [ha_eq] at hrk_sh ⊢
          exact Symbolic.Swarm.CREF.TR.G1.eq_dhPk_randTerm32_of_shape_eq interpretation S g t_s hrk_sh
        have hseed_eq : seed' = mkSeed := by
          rw [← hseed_s] at hseed_sh ⊢
          exact honestSkelUniq_of_reachable_compat interpretation r₀ S g ms hreach
            (aliceSlot_sigma_len32_of_explains interpretation r₀ S g ms hEx)
            hst_s hst₀ hseed hseed_sh
        have hmyIk_eq : myIk' = st₀.peerIk := by
          rw [← hmyIk_s] at hmyIk_sh ⊢
          exact Symbolic.Swarm.CREF.TR.G1.eq_of_shape_eq_of_shapeId (hIk st_s hst_s).1 (hIk st₀ hst₀).2 hmyIk_sh
        have hpeerIk_eq : peerIk' = st₀.myIk := by
          rw [← hpeerIk_s] at hpeerIk_sh ⊢
          exact Symbolic.Swarm.CREF.TR.G1.eq_of_shape_eq_of_shapeId (hIk st_s hst_s).2 (hIk st₀ hst₀).1 hpeerIk_sh
        exact Symbolic.Swarm.CREF.TR.G1.g1b_honest_send_branch_core interpretation hEq r₀ S g ms b ptext parsed hTryFrom
          t₀ msg₀ ht₀ hparse₀ st₀ mkSeed hseed salt₁ hDecOk_salt₁
          salt₁ pqSalt' seed' myIk' peerIk' a' m' pqMsg' ns' pn'
          rfl hmac_eq' hsh_inp' hpq_ak ht'_kn' hrk_eq hseed_eq hmyIk_eq hpeerIk_eq
    · exact Symbolic.Swarm.CREF.TR.G1.g1c_own_key_branch' interpretation r₀ S g ms b ptext hABS' hreach
        t₀ msg₀ ht₀ hparse₀ hNotCol st₀ hst₀ mkSeed hseed k_own hCaseC
  rcases hDisj with hmk_ak | ⟨salt₁, hsalt₁, ⟨hck_eq, hmk_eq, hiv_eq⟩, hAuth_salt₁⟩
  · exact Or.inl (Symbolic.Swarm.CREF.TR.G1.ratchetDH_rkSwap_seed_known_of_seed_attackerKnows
      interpretation hEq r₀ S g ms msg₀ st₀ mkSeed hreach hst₀ hfind hrkK hseed hmk_ak)
  · rcases Symbolic.Swarm.CREF.TR.G1.seed_attackerKnows_or_termShapeId_of_authenticDecryptRep
        interpretation r₀ S g ms b ptext msg₀ st₀ mkSeed salt₁ hreach hseed hAuth_salt₁ with
      hmk_ak | ⟨hrk_sid, hAuth⟩
    · exact Or.inl (Symbolic.Swarm.CREF.TR.G1.ratchetDH_rkSwap_seed_known_of_seed_attackerKnows
        interpretation hEq r₀ S g ms msg₀ st₀ mkSeed hreach hst₀ hfind hrkK hseed hmk_ak)
    · refine Or.inr ⟨salt₁, hsalt₁, hrk_sid, hAuth, ?_, by rw [hck_eq, hiv_eq]; exact hDecOk⟩
      rw [hMacBytes]
      unfold DY.Libsignal.TripleRatchet.computeMac DY.Libsignal.TripleRatchet.hmac
      rw [Symbolic.Swarm.CREF.CliPure.TR.RecvDecStep.gamma_trunc8_tr,
          Symbolic.Swarm.CREF.CliPure.TR.RecvDecStep.gamma_trunc8_tr,
          Symbolic.Swarm.CREF.TR.G1.gamma_kdfExtract_tr,
          Symbolic.Swarm.CREF.TR.G1.gamma_kdfExtract_tr, hmk_eq]

end Symbolic.Swarm.CREF.CliPure.TR.RecvDecStepAt
