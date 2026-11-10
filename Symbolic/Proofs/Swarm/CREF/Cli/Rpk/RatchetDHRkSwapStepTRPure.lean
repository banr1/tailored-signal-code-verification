/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Symbolic.Proofs.Swarm.CREF.TR.RecvDec
public import Symbolic.Proofs.Swarm.CREF.TR.G1.ShapeIdInv
import Batteries.Data.UInt
public import Symbolic.Proofs.Swarm.CREF.Cli.Rpk.SendRetCoinsCliPureB
public import Symbolic.Proofs.Swarm.CREF.TR.G1.WireShapeInj
public import Symbolic.Proofs.Swarm.CREF.TR.SrHonestVer
public import Symbolic.Proofs.Swarm.TRREF.B3DefsPure
import Symbolic.Proofs.Refinement.TripleRatchet.WireCovered
import Symbolic.Proofs.Swarm.CREF.Cli.Rpk.RatchetDHRkSwapStepTRPureA
import Symbolic.Proofs.Swarm.CREF.Cli.Rpk.RecvDecStepSpqrHonestPure
import Symbolic.Proofs.Swarm.CREF.Cli.Rpk.RecvDecStepSpqrPure
import Symbolic.Proofs.Swarm.CREF.Prelude
import Symbolic.Proofs.Swarm.CREF.TR.HonestPqNoTrWire
import Symbolic.Proofs.Swarm.CREF.TR.RecvCol -- shake: keep
import Symbolic.Proofs.Swarm.CREF.TR.Leaks -- shake: keep
import Symbolic.Proofs.Swarm.CREF.TR.PQGamma -- shake: keep
import Symbolic.Proofs.Swarm.CREF.TR.PQModelRunNil -- shake: keep
import Symbolic.Proofs.Swarm.CREF.TR.RecvRep -- shake: keep

/-!
# Forged Decrypt Representation and SPQR Step Bridge Under Ratchet-Key Swap

Constructs DY wire representations with honest SPQR provenance when swapping the sender ratchet
key to a `gamma`-equivalent key `rk_c` during a DH ratchet step, and bridges `spqrRecv` across the
swapped state.
-/

@[expose] public section

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

cref_hide_foreign_instances

namespace Symbolic.Swarm.CREF.CliPure.TR.G1
open Symbolic.Swarm.CREF.TR hiding PureBinCanonSession PureRecordRepr SpqrSem at?_append_of_lt gamma_concat getLocalState_fst leValue_leBytes length_leBytes newRandoms_append_rnd p25519_lt p25519_pos runMoves_append runTrace_append runTrace_snoc runVis_append runVis_snoc run_bind_fst run_bind_snd uOf_leBytes uOf_lt
open Symbolic.Swarm.CREF.TR.G1 hiding gamma_kdfExtract_tr gamma_symEnc_tr

cref_open
open DY DY.Comparse DY.Literal DY.DiffieHellman DY.Libsignal
open DY.Libsignal.TripleRatchet
  (SessionInfo DRState KeyComponent KeyDir RecvChain findRecvChain setRecvChain recvChainFor consumeMessageKey chainKeyAt kdfCk kdfRk maxForwardJumps u32Max computeMac messageVersion createChain x25519LowOrder litByte)
open DY.Libsignal.TripleRatchet
open DY.Libsignal.Refinement (ExternCryptoLawsHold aesCbcDecryptSymbol)
open DY.Libsignal.HwEvents DY.Libsignal.Rust
open CryptoGames CryptoGames.HMAC CryptoGames.HKDF
open CryptoGames.LibsignalSession CryptoGames.LibsignalSessionApi
open CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalProtoCodec
open CryptoVerification.E2E.Pqxdh.WireEntries
open CryptoVerification.E2E.Pqxdh.WireEntries.SymP3 hiding encodeRecord
open CryptoProofLib.Refinement (ExternInterpretation)
open Proofs.libsignal.Hooks2
open Proofs.libsignal.RngG.R3 Proofs.libsignal.RngG.CliPure.R3
open Symbolic.Swarm.CREF Symbolic.Swarm.CREF.CliPure Symbolic.Swarm.CREF.CliPure.TR
open Symbolic.Swarm.CREF.TR.RecvCol
open Symbolic.Swarm.CREF.TR.RecvRep hiding gamma_litOf
open Symbolic.Swarm.CREF.TR.RecvDec (trDhRatchetState at?_append_of_lt)
open Symbolic.Swarm.CREF.CliPure.TR.RecvDecStep (gamma_computeMac_congr_wire
  exists_forged_decrypt_rep_with_sendMsg SpqrRecvStepOut spqrRecv_step_bridge_of_not_empty_pending)
open Symbolic.Swarm.CREF.TR.Pure
open Symbolic.Swarm.TRREF.SpqrSemOf (spqrModelOf)
open Symbolic.Swarm.CREF.CliPure.TR.SendRetCoins (SpqrSem spqrSemOf gamma_symEnc_tr gamma_kdfExtract_tr gamma_trunc8_tr)

theorem forged_decrypt_rep_of_rkSwap_keysKnown_with_sendMsg_tr_prov
    (interpretation : ExternInterpretation) (hEq : ExternCryptoLawsHold interpretation)
    (r₀ : ProtocolSetup) (S : SpqrSem) (g : Ghost) (ms : List Move) (acc : List MachineEvent)
    (b ptext : HwBytes) (parsed : SignalMessage) {who : List Participant}
    (hmp : MatchedPrefix interpretation r₀ S who g ms acc)
    (hfit : SrHonestVer.SendsFit acc)
    (hHon : PqFromHonest (sentBodies acc) b)
    (hTryFrom : SignalMessage.tryFrom protoSignalCodec b = .ok parsed)
    (t₀ : DY.Bytes) (msg₀ : TRSignalMsg)
    (ht₀ : t₀ ∈ recvRepresentations interpretation r₀ S g ms b)
    (hparse₀ : parseTrSignalMsg t₀ = some msg₀)
    (st₀ : TRState) (rk_c seed_c mkSeed k_own pqSalt : DY.Bytes)
    (hrk_c_kn : rk_c.AttackerKnows (runTraceMoves r₀ ms))
    (hγ_rk_c : gamma interpretation S g rk_c = gamma interpretation S g msg₀.ratchetKey)
    (hγ_seed_c : gamma interpretation S g seed_c = gamma interpretation S g mkSeed)
    (hpqSalt_kn : pqSalt.AttackerKnows (runTraceMoves r₀ ms))
    (hpqSalt_gam : gamma interpretation S g pqSalt = gamma interpretation S g k_own)
    (hck_kn : (trMsgKeys pqSalt seed_c).cipherKey.AttackerKnows (runTraceMoves r₀ ms))
    (hmk_kn : (trMsgKeys pqSalt seed_c).macKey.AttackerKnows (runTraceMoves r₀ ms))
    (hiv_kn : (trMsgKeys pqSalt seed_c).iv.AttackerKnows (runTraceMoves r₀ ms))
    (hMacBytes : b.drop (b.length - 8) =
      gamma interpretation S g (computeMac (trMsgKeys k_own mkSeed).macKey st₀.peerIk st₀.myIk msg₀.wire))
    (hPeerK : st₀.peerIk.AttackerKnows (runTraceMoves r₀ ms))
    (hMyK : st₀.myIk.AttackerKnows (runTraceMoves r₀ ms))
    (hDecOk : interpretation aesCbcDecryptSymbol
      [parsed.ciphertext, gamma interpretation S g (trMsgKeys k_own mkSeed).cipherKey,
       (gamma interpretation S g (trMsgKeys k_own mkSeed).iv).take 16] = some ptext) :
    ∃ (t' : DY.Bytes) (msg' : TRSignalMsg) (ptTerm : DY.Bytes),
      t' ∈ recvRepresentations interpretation r₀ S g ms b ∧
      t'.AttackerKnows (runTraceMoves r₀ ms) ∧
      gamma interpretation S g t' = b ∧
      parseTrSignalMsg t' = some msg' ∧
      msg'.version = msg₀.version ∧
      msg'.ratchetKey = rk_c ∧
      msg'.counter = msg₀.counter ∧
      gamma interpretation S g msg'.pqRatchet = gamma interpretation S g msg₀.pqRatchet ∧
      DY.Spqr.spqrEmptyMsg msg'.pqRatchet = false ∧
      msg'.mac = computeMac (trMsgKeys pqSalt seed_c).macKey st₀.peerIk st₀.myIk msg'.wire ∧
      DY.SymEnc.symDec (trMsgKeys pqSalt seed_c).cipherKey (trMsgKeys pqSalt seed_c).iv msg'.ciphertext = some ptTerm ∧
      gamma interpretation S g ptTerm = ptext ∧
      ∃ (st_s : TRState) (t_c coinsLen : Nat),
        st_s ∈ availableStates r₀ (runTraceMoves r₀ ms) ∧
        msg'.pqRatchet = ({ st := st_s.spqr, coins := randTerm t_c coinsLen } : DY.Spqr.SendMsg.SubF DY.Bytes).pack := by
  obtain ⟨hck_gam, hmk_gam, hiv_gam⟩ :=
    gamma_trMsgKeys_eq_of_gamma_eq interpretation S g hpqSalt_gam hγ_seed_c
  obtain ⟨hwire₀_take, _, _, htry₀⟩ := ht₀.2.2.2 msg₀ hparse₀
  obtain ⟨_, hrk₀_gam, hpq₀_gam, hctr₀_nat, hver₀_nat⟩ := htry₀ parsed hTryFrom
  have hrk_c_gam : gamma interpretation S g rk_c = parsed.senderRatchetKey.bytes.toList := by
    rw [hγ_rk_c, hrk₀_gam]
  have hck_len : (gamma interpretation S g (trMsgKeys k_own mkSeed).cipherKey).length = 32 :=
    length_gamma_hmac_tr interpretation S g _ _
  have hiv_len32 : (gamma interpretation S g (trMsgKeys k_own mkSeed).iv).length = 32 :=
    length_gamma_hmac_tr interpretation S g _ _
  have hiv_len : ((gamma interpretation S g (trMsgKeys k_own mkSeed).iv).take 16).length = 16 := by
    rw [List.length_take, hiv_len32]; decide
  have hct_gam : gamma interpretation S g
      (DY.SymEnc.symEnc (trMsgKeys pqSalt seed_c).cipherKey (trMsgKeys pqSalt seed_c).iv (litOf ptext)) =
      parsed.ciphertext := by
    rw [gamma_symEnc_tr, gamma_litOf, hck_gam, hiv_gam,
        hEq.aes_cbc_encrypt_of_decrypt _ _ _ _ hck_len hiv_len hDecOk, Option.getD_some]
  have hmac_gam : ∀ wire' : DY.Bytes,
      gamma interpretation S g wire' = b.take (b.length - 8) →
      gamma interpretation S g (computeMac (trMsgKeys pqSalt seed_c).macKey st₀.peerIk st₀.myIk wire') =
        b.drop (b.length - 8) := by
    intro wire' hwire'_take
    rw [hMacBytes]
    rw [gamma_computeMac_congr_wire interpretation S g _ _ _ wire' msg₀.wire (hwire'_take.trans hwire₀_take.symm)]
    unfold DY.Libsignal.TripleRatchet.computeMac DY.Libsignal.TripleRatchet.hmac
    rw [gamma_trunc8_tr, gamma_trunc8_tr, gamma_kdfExtract_tr, gamma_kdfExtract_tr, hmk_gam]
  obtain ⟨st_s, coins_s, st_avail, ts, coinsLen, hpq_knows, hpq_gamma, hst_avail, rfl, rfl⟩ :=
    SrHonestVer.exists_honest_sendMsg_of_pqFromHonest_prov interpretation r₀ S g ms acc b parsed hmp hfit hHon hTryFrom
  obtain ⟨t', msg', ptTerm, ht'_rep, ht'_kn, ht'_gam, hparse', hver', hrk', hctr',
    hpq', hnot_empty, hmac', hdec', hpt_gam⟩ :=
    exists_forged_decrypt_rep_with_sendMsg interpretation r₀ S g ms b ptext parsed hTryFrom
      rk_c pqSalt seed_c st₀.peerIk st₀.myIk st_avail.spqr (randTerm (ts + 1) coinsLen)
      hrk_c_kn hrk_c_gam hck_kn hiv_kn hmk_kn hPeerK hMyK
      hpq_knows hpq_gamma hct_gam hmac_gam
  exact ⟨t', msg', ptTerm, ht'_rep, ht'_kn, ht'_gam, hparse',
    UInt8.ext (hver'.trans hver₀_nat.symm), hrk', UInt32.ext (hctr'.trans hctr₀_nat.symm),
    by rw [hpq', hpq_gamma, hpq₀_gam], hnot_empty, hmac', hdec', hpt_gam,
    st_avail, ts + 1, coinsLen, hst_avail, hpq'⟩

theorem forged_decrypt_rep_of_rkSwap_seedKnown_with_sendMsg_tr_prov
    (interpretation : ExternInterpretation) (hEq : ExternCryptoLawsHold interpretation)
    (r₀ : ProtocolSetup) (S : SpqrSem) (g : Ghost) (ms : List Move) (acc : List MachineEvent)
    (b ptext : HwBytes) (parsed : SignalMessage) {who : List Participant}
    (hmp : MatchedPrefix interpretation r₀ S who g ms acc)
    (hfit : SrHonestVer.SendsFit acc)
    (hHon : PqFromHonest (sentBodies acc) b)
    (hTryFrom : SignalMessage.tryFrom protoSignalCodec b = .ok parsed)
    (t₀ : DY.Bytes) (msg₀ : TRSignalMsg)
    (ht₀ : t₀ ∈ recvRepresentations interpretation r₀ S g ms b)
    (hparse₀ : parseTrSignalMsg t₀ = some msg₀)
    (st₀ : TRState) (rk_c seed_c mkSeed k_own : DY.Bytes)
    (hrk_c_kn : rk_c.AttackerKnows (runTraceMoves r₀ ms))
    (hγ_rk_c : gamma interpretation S g rk_c = gamma interpretation S g msg₀.ratchetKey)
    (hseed_c_kn : seed_c.AttackerKnows (runTraceMoves r₀ ms))
    (hγ_seed_c : gamma interpretation S g seed_c = gamma interpretation S g mkSeed)
    (hMacBytes : b.drop (b.length - 8) =
      gamma interpretation S g (computeMac (trMsgKeys k_own mkSeed).macKey st₀.peerIk st₀.myIk msg₀.wire))
    (hPeerK : st₀.peerIk.AttackerKnows (runTraceMoves r₀ ms))
    (hMyK : st₀.myIk.AttackerKnows (runTraceMoves r₀ ms))
    (hDecOk : interpretation aesCbcDecryptSymbol
      [parsed.ciphertext, gamma interpretation S g (trMsgKeys k_own mkSeed).cipherKey,
       (gamma interpretation S g (trMsgKeys k_own mkSeed).iv).take 16] = some ptext) :
    ∃ (t' : DY.Bytes) (msg' : TRSignalMsg) (ptTerm pqSalt : DY.Bytes),
      t' ∈ recvRepresentations interpretation r₀ S g ms b ∧
      t'.AttackerKnows (runTraceMoves r₀ ms) ∧
      pqSalt.AttackerKnows (runTraceMoves r₀ ms) ∧
      gamma interpretation S g pqSalt = gamma interpretation S g k_own ∧
      gamma interpretation S g t' = b ∧
      parseTrSignalMsg t' = some msg' ∧
      msg'.version = msg₀.version ∧
      msg'.ratchetKey = rk_c ∧
      msg'.counter = msg₀.counter ∧
      gamma interpretation S g msg'.pqRatchet = gamma interpretation S g msg₀.pqRatchet ∧
      DY.Spqr.spqrEmptyMsg msg'.pqRatchet = false ∧
      msg'.mac = computeMac (trMsgKeys pqSalt seed_c).macKey st₀.peerIk st₀.myIk msg'.wire ∧
      DY.SymEnc.symDec (trMsgKeys pqSalt seed_c).cipherKey (trMsgKeys pqSalt seed_c).iv msg'.ciphertext = some ptTerm ∧
      gamma interpretation S g ptTerm = ptext ∧
      ∃ (st_s : TRState) (t_c coinsLen : Nat),
        st_s ∈ availableStates r₀ (runTraceMoves r₀ ms) ∧
        msg'.pqRatchet = ({ st := st_s.spqr, coins := randTerm t_c coinsLen } : DY.Spqr.SendMsg.SubF DY.Bytes).pack := by
  let tr := runTraceMoves r₀ ms
  let pqSalt := litOf (gamma interpretation S g k_own)
  have hpqSalt_kn : pqSalt.AttackerKnows tr := knows_litOf _ _
  have hpqSalt_gam : gamma interpretation S g pqSalt = gamma interpretation S g k_own :=
    gamma_litOf interpretation S g _
  have hprk_kn : (DY.Libsignal.TripleRatchet.hmac pqSalt seed_c).AttackerKnows tr :=
    KdfExtract.attacker_knows_kdfExtract _ _ _ hpqSalt_kn hseed_c_kn
  have hinfo_kn : (DY.Libsignal.TripleRatchet.lit "WhisperMessageKeys").AttackerKnows tr :=
    Literal.attacker_knows_literalToBytes _ _
  have hck_kn : (trMsgKeys pqSalt seed_c).cipherKey.AttackerKnows tr :=
    KdfExtract.attacker_knows_kdfExtract _ _ _ hprk_kn
      (Concat.attacker_knows_concat _ _ _ hinfo_kn (Literal.attacker_knows_literalToBytes _ _))
  have hmk_kn : (trMsgKeys pqSalt seed_c).macKey.AttackerKnows tr :=
    KdfExtract.attacker_knows_kdfExtract _ _ _ hprk_kn
      (Concat.attacker_knows_concat _ _ _ hck_kn
        (Concat.attacker_knows_concat _ _ _ hinfo_kn (Literal.attacker_knows_literalToBytes _ _)))
  have hiv_kn : (trMsgKeys pqSalt seed_c).iv.AttackerKnows tr :=
    KdfExtract.attacker_knows_kdfExtract _ _ _ hprk_kn
      (Concat.attacker_knows_concat _ _ _ hmk_kn
        (Concat.attacker_knows_concat _ _ _ hinfo_kn (Literal.attacker_knows_literalToBytes _ _)))
  obtain ⟨t', msg', ptTerm, ht'_rep, ht'_kn, ht'_gam, hparse', hver', hrk', hctr',
    hpq_gam, hnot_empty, hmac', hdec', hpt_gam, hpq_prov⟩ :=
    forged_decrypt_rep_of_rkSwap_keysKnown_with_sendMsg_tr_prov interpretation hEq r₀ S g ms acc b ptext parsed
      hmp hfit hHon hTryFrom t₀ msg₀ ht₀ hparse₀ st₀ rk_c seed_c mkSeed k_own pqSalt
      hrk_c_kn hγ_rk_c hγ_seed_c hpqSalt_kn hpqSalt_gam hck_kn hmk_kn hiv_kn hMacBytes hPeerK hMyK hDecOk
  exact ⟨t', msg', ptTerm, pqSalt, ht'_rep, ht'_kn, hpqSalt_kn, hpqSalt_gam, ht'_gam,
    hparse', hver', hrk', hctr', hpq_gam, hnot_empty, hmac', hdec', hpt_gam, hpq_prov⟩

/-- Bridges a successful model SPQR receive step and DH ratchet decrypt under ratchet-key swap to a
DY representation at `rk_c` with honest SPQR send provenance. -/
theorem spqrRecv_step_bridge_ratchetDH_rkSwap_nw
    (interpretation : ExternInterpretation) (hEq : ExternCryptoLawsHold interpretation) (r₀ : ProtocolSetup)
    (S : SpqrSem) (hS : S = spqrSemOf interpretation r₀)
    (g' : Ghost) (p : Participant) (stateIdx : Nat) (ms₁ : List Move) (acc_evs : List MachineEvent)
    (recBytes body ptext : HwBytes) (rec : RecordRec) (st₀ : TRState) (g_rw : RecvWireGhost)
    (t₀ : DY.Bytes) (msg₀ : TRSignalMsg) (m : SignalMessage) (mkSeed k_own : DY.Bytes) (c'₀ : RecvChain)
    (newPqrState : HwBytes) (pqrKey : HKDF.Salt) {who : List Participant}
    (hmp' : MatchedPrefix interpretation r₀ S who g' ms₁ acc_evs)
    (hfit : SrHonestVer.SendsFit acc_evs)
    (hrecBytes : recBytes = recordBytes rec)
    (hrel : StateRel interpretation S g' st₀ rec)
    (hst : ((PersistentLocalState.getLocalState p stateIdx : Traceful TRState).run
      (runTraceMoves r₀ ms₁)).1 = some st₀)
    (hcanon_q : Symbolic.Swarm.CREF.TR.Pure.slots_RecordCanonical_Q Symbolic.Swarm.CREF.TR.Pure.slots_NonEmptyV1Q recBytes g_rw.sess)
    (hpq : PqFromHonest (sentBodies acc_evs) body)
    (htry : SignalMessage.tryFrom protoSignalCodec body = .ok m)
    (ht₀ : t₀ ∈ recvRepresentations interpretation r₀ S g' ms₁ body)
    (hparse₀ : parseTrSignalMsg t₀ = some msg₀)
    (hver₀ : msg₀.version = messageVersion)
    (hctr₀ : msg₀.counter = UInt32.ofBitVec m.counter)
    (hcons₀ : consumeMessageKey
      (trDhRatchetState st₀ msg₀.ratchetKey ((runTraceMoves r₀ ms₁).length + 2)).2 msg₀.counter =
      some (mkSeed, c'₀))
    (hMacBytes : body.drop (body.length - 8) =
      gamma interpretation S g' (computeMac (trMsgKeys k_own mkSeed).macKey st₀.peerIk st₀.myIk msg₀.wire))
    (hPeerK : st₀.peerIk.AttackerKnows (runTraceMoves r₀ ms₁))
    (hMyK : st₀.myIk.AttackerKnows (runTraceMoves r₀ ms₁))
    (hDecOk : interpretation aesCbcDecryptSymbol
      [m.ciphertext, gamma interpretation S g' (trMsgKeys k_own mkSeed).cipherKey,
       (gamma interpretation S g' (trMsgKeys k_own mkSeed).iv).take 16] = some ptext)
    (hrecv_spqr : (spqrModelOf interpretation).recv
      g_rw.sess.state.pqRatchetState m.pqRatchet = .ok (newPqrState, pqrKey))
    (hDisj :
      (∃ rk_c : DY.Bytes,
        let seed_c := (kdfCk (chainKeyAt (createChain st₀.rk rk_c st₀.dhs).2 msg₀.counter.toNat)).2
        TermShapeId rk_c ∧
        rk_c.AttackerKnows (runTraceMoves r₀ ms₁) ∧
        gamma interpretation S g' rk_c = gamma interpretation S g' msg₀.ratchetKey ∧
        seed_c.AttackerKnows (runTraceMoves r₀ ms₁) ∧
        gamma interpretation S g' seed_c = gamma interpretation S g' mkSeed) ∨
      (TermShapeId msg₀.ratchetKey ∧
        AuthenticDecryptRep interpretation r₀ S g' ms₁ body ptext msg₀ st₀ mkSeed k_own)) :
    ∃ (rk_c seed_c : DY.Bytes) (c'_c : RecvChain) (t' : DY.Bytes) (msg' : TRSignalMsg)
      (pqSalt ptTerm spqr' key : DY.Bytes) (spqrMsgIdx : UInt32),
      TermShapeId rk_c ∧
      gamma interpretation S g' rk_c = gamma interpretation S g' msg₀.ratchetKey ∧
      gamma interpretation S g' seed_c = gamma interpretation S g' mkSeed ∧
      consumeMessageKey (trDhRatchetState st₀ rk_c ((runTraceMoves r₀ ms₁).length + 2)).2 msg'.counter =
        some (seed_c, c'_c) ∧
      t' ∈ recvRepresentations interpretation r₀ S g' ms₁ body ∧
      pqSalt.AttackerKnows (runTraceMoves r₀ ms₁) ∧
      t'.AttackerKnows (runTraceMoves r₀ ms₁) ∧
      parseTrSignalMsg t' = some msg' ∧
      msg'.version = messageVersion ∧
      msg'.ratchetKey = rk_c ∧
      msg'.counter = UInt32.ofBitVec m.counter ∧
      Spqr.spqrRecv (trDhRatchetState st₀ rk_c ((runTraceMoves r₀ ms₁).length + 2)).1.spqr
        msg'.pqRatchet spqrMsgIdx = some (spqr', key) ∧
      gamma interpretation S g' spqr' = newPqrState ∧
      msg'.mac = computeMac (trMsgKeys pqSalt seed_c).macKey
        (trDhRatchetState st₀ rk_c ((runTraceMoves r₀ ms₁).length + 2)).1.peerIk
        (trDhRatchetState st₀ rk_c ((runTraceMoves r₀ ms₁).length + 2)).1.myIk msg'.wire ∧
      DY.SymEnc.symDec (trMsgKeys pqSalt seed_c).cipherKey (trMsgKeys pqSalt seed_c).iv
        msg'.ciphertext = some ptTerm ∧
      gamma interpretation S g' t' = body ∧
      gamma interpretation S g' ptTerm = ptext ∧
      ∃ (st_s : TRState) (t_c coinsLen : Nat),
        st_s ∈ availableStates r₀ (runTraceMoves r₀ ms₁) ∧
        msg'.pqRatchet = ({ st := st_s.spqr, coins := randTerm t_c coinsLen } : DY.Spqr.SendMsg.SubF DY.Bytes).pack := by
  have hRep :
      ∃ (rk_c seed_c : DY.Bytes) (c'_c : RecvChain) (t' : DY.Bytes) (msg' : TRSignalMsg)
        (ptTerm pqSalt : DY.Bytes),
        TermShapeId rk_c ∧
        gamma interpretation S g' rk_c = gamma interpretation S g' msg₀.ratchetKey ∧
        gamma interpretation S g' seed_c = gamma interpretation S g' mkSeed ∧
        consumeMessageKey (trDhRatchetState st₀ rk_c ((runTraceMoves r₀ ms₁).length + 2)).2 msg₀.counter =
          some (seed_c, c'_c) ∧
        t' ∈ recvRepresentations interpretation r₀ S g' ms₁ body ∧
        t'.AttackerKnows (runTraceMoves r₀ ms₁) ∧
        pqSalt.AttackerKnows (runTraceMoves r₀ ms₁) ∧
        gamma interpretation S g' pqSalt = gamma interpretation S g' k_own ∧
        gamma interpretation S g' t' = body ∧
        parseTrSignalMsg t' = some msg' ∧
        msg'.version = msg₀.version ∧
        msg'.ratchetKey = rk_c ∧
        msg'.counter = msg₀.counter ∧
        gamma interpretation S g' msg'.pqRatchet = gamma interpretation S g' msg₀.pqRatchet ∧
        DY.Spqr.spqrEmptyMsg msg'.pqRatchet = false ∧
        msg'.mac = computeMac (trMsgKeys pqSalt seed_c).macKey st₀.peerIk st₀.myIk msg'.wire ∧
        DY.SymEnc.symDec (trMsgKeys pqSalt seed_c).cipherKey (trMsgKeys pqSalt seed_c).iv msg'.ciphertext = some ptTerm ∧
        gamma interpretation S g' ptTerm = ptext ∧
        ∃ (st_s : TRState) (t_c coinsLen : Nat),
          st_s ∈ availableStates r₀ (runTraceMoves r₀ ms₁) ∧
          msg'.pqRatchet = ({ st := st_s.spqr, coins := randTerm t_c coinsLen } : DY.Spqr.SendMsg.SubF DY.Bytes).pack := by
    rcases hDisj with ⟨rk_c, hrk_c_sid, hrk_c_kn, hγ_rk_c, hseed_c_kn, hγ_seed_c⟩ | ⟨hrk₀_sid, hAuth⟩
    · let seed_c := (kdfCk (chainKeyAt (createChain st₀.rk rk_c st₀.dhs).2 msg₀.counter.toNat)).2
      let c'_c : RecvChain :=
        { ratchetKey := rk_c
          chainKey := (kdfCk (chainKeyAt (createChain st₀.rk rk_c st₀.dhs).2 msg₀.counter.toNat)).1
          index := msg₀.counter + 1
          rIdx := st₀.rIdx + 2 }
      have hcons_c :=
        (consumeMessageKey_trDhRatchetState_rkSwap_of_msg₀ st₀ msg₀
          ((runTraceMoves r₀ ms₁).length + 2) mkSeed c'₀ rk_c hcons₀).1
      obtain ⟨t', msg', ptTerm, pqSalt, ht'_rep, ht'_kn, hpqSalt_kn, hpqSalt_gam, ht'_gam,
        hparse', hver', hrk', hctr', hpq_gam, hnot_empty, hmac', hdec', hpt_gam, hpq_prov⟩ :=
        forged_decrypt_rep_of_rkSwap_seedKnown_with_sendMsg_tr_prov interpretation hEq r₀ S g' ms₁ acc_evs
          body ptext m hmp' hfit hpq htry t₀ msg₀ ht₀ hparse₀ st₀ rk_c seed_c mkSeed k_own
          hrk_c_kn hγ_rk_c hseed_c_kn hγ_seed_c hMacBytes hPeerK hMyK hDecOk
      exact ⟨rk_c, seed_c, c'_c, t', msg', ptTerm, pqSalt, hrk_c_sid, hγ_rk_c, hγ_seed_c, hcons_c,
        ht'_rep, ht'_kn, hpqSalt_kn, hpqSalt_gam, ht'_gam, hparse', hver', hrk', hctr',
        hpq_gam, hnot_empty, hmac', hdec', hpt_gam, hpq_prov⟩
    · obtain ⟨t', msg', ptTerm, pqSalt, ht'_rep, ht'_kn, hpqSalt_kn, hpqSalt_gam, ht'_gam,
        hparse', hver', hrk', hctr', hpq_gam, hmac', hdec', hpt_gam⟩ := hAuth
      rcases honest_encrypt_mac_pqRatchet_prov_or_keysKnown_tr
          hmp'.2.1.2.2.1.1 ht'_kn hparse' hmac' with
        ⟨st_s, t_c, coinsLen, hst_s, hpq_eq, hnot_empty⟩ | ⟨hck_kn, hmk_kn, hiv_kn⟩
      · exact ⟨msg₀.ratchetKey, mkSeed, c'₀, t', msg', ptTerm, pqSalt, hrk₀_sid, rfl, rfl, hcons₀,
          ht'_rep, ht'_kn, hpqSalt_kn, hpqSalt_gam, ht'_gam, hparse', hver', hrk', hctr',
          hpq_gam, hnot_empty, hmac', hdec', hpt_gam, st_s, t_c, coinsLen, hst_s, hpq_eq⟩
      · have hrk₀_kn : msg₀.ratchetKey.AttackerKnows (runTraceMoves r₀ ms₁) :=
          ratchetKey_attackerKnows_of_parseTrSignalMsg_step ht₀.1 hparse₀
        obtain ⟨t'', msg'', ptTerm'', ht''_rep, ht''_kn, ht''_gam, hparse'', hver'', hrk'', hctr'',
          hpq_gam'', hnot_empty'', hmac'', hdec'', hpt_gam'', hpq_prov''⟩ :=
          forged_decrypt_rep_of_rkSwap_keysKnown_with_sendMsg_tr_prov interpretation hEq r₀ S g' ms₁ acc_evs
            body ptext m hmp' hfit hpq htry t₀ msg₀ ht₀ hparse₀ st₀ msg₀.ratchetKey mkSeed mkSeed k_own pqSalt
            hrk₀_kn rfl rfl hpqSalt_kn hpqSalt_gam hck_kn hmk_kn hiv_kn hMacBytes hPeerK hMyK hDecOk
        exact ⟨msg₀.ratchetKey, mkSeed, c'₀, t'', msg'', ptTerm'', pqSalt, hrk₀_sid, rfl, rfl, hcons₀,
          ht''_rep, ht''_kn, hpqSalt_kn, hpqSalt_gam, ht''_gam, hparse'', hver'', hrk'', hctr'',
          hpq_gam'', hnot_empty'', hmac'', hdec'', hpt_gam'', hpq_prov''⟩
  obtain ⟨rk_c, seed_c, c'_c, t', msg', ptTerm, pqSalt, hrk_c_sid, hγ_rk_c, hγ_seed_c, hcons_c,
    ht'_rep, ht'_kn, hpqSalt_kn, _hpqSalt_gam, ht'_gam, hparse', hver', hrk', hctr',
    _hpq_gam, hnot_empty, hmac', hdec', hpt_gam, hpq_prov⟩ := hRep
  let st1_c := (trDhRatchetState st₀ rk_c ((runTraceMoves r₀ ms₁).length + 2)).1
  have hspqr_eq : st1_c.spqr = st₀.spqr := rfl
  have hSpqrOut : SpqrRecvStepOut interpretation S g' st1_c msg' newPqrState pqrKey :=
    (spqrRecv_step_bridge_of_not_empty_pending interpretation hEq r₀ S hS g' ms₁ p stateIdx
      recBytes body rec st₀ st1_c g_rw t' msg' m newPqrState pqrKey
      hst hrecBytes hrel hspqr_eq hcanon_q ht'_rep hparse' htry hnot_empty hrecv_spqr).2
  obtain ⟨spqrMsgIdx, spqr', key, hspqr_step, hspqr'_gam, _⟩ := hSpqrOut.exists_step
  have hcons_c' :
      consumeMessageKey (trDhRatchetState st₀ rk_c ((runTraceMoves r₀ ms₁).length + 2)).2 msg'.counter =
        some (seed_c, c'_c) := by
    rw [hctr']; exact hcons_c
  exact ⟨rk_c, seed_c, c'_c, t', msg', pqSalt, ptTerm, spqr', key, spqrMsgIdx,
    hrk_c_sid, hγ_rk_c, hγ_seed_c, hcons_c', ht'_rep, hpqSalt_kn, ht'_kn, hparse',
    hver'.trans hver₀, hrk', hctr'.trans hctr₀, hspqr_step, hspqr'_gam, hmac', hdec', ht'_gam, hpt_gam,
    hpq_prov⟩

end Symbolic.Swarm.CREF.CliPure.TR.G1
