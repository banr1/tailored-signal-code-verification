/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Symbolic.Proofs.Swarm.CREF.Cli.Rpk.RecvDecStepNoRatchetWAtHelpersPure
public import Symbolic.Proofs.Swarm.CREF.TR.SrHonestVer
public import Symbolic.Proofs.Swarm.CREF.TR.PureCanon
public import Symbolic.Proofs.Swarm.TRREF.B3DefsPure
public import Symbolic.Proofs.Swarm.TRREF.SpqrSemOf
import Symbolic.Proofs.Swarm.CREF.Cli.Rpk.RecvDecStepSkippedG1LeavesPure
import Symbolic.Proofs.Swarm.CREF.Cli.Rpk.RecvDecStepSpqrPure
import Symbolic.Proofs.Swarm.CREF.Prelude
import Symbolic.Proofs.Swarm.CREF.TROpen
import Symbolic.Proofs.Swarm.CREF.Cli.Rpk.RecvAtFactsPure -- shake: keep
import Symbolic.Proofs.Swarm.CREF.TR.Leaks -- shake: keep
import Symbolic.Proofs.Swarm.CREF.TR.PQModelRunNil -- shake: keep

/-!
# Existing-Chain Decrypt Witness Lemmas at a Fixed Explanation

Constructs symbolic wire, SPQR receive, MAC, and decryption witnesses at `(g, ms₁)` for the
existing-chain (`noRatchet`) branch from either attacker knowledge of `seed` or an authentic
decrypt representation `AuthenticDecryptRepB3St`.
-/

@[expose] public section

cref_hide_foreign_instances
set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

namespace Symbolic.Swarm.CREF.CliPure.TR.RecvDecStepAt
open Symbolic.Swarm.CREF.TR hiding PureBinCanonSession PureRecordRepr SpqrSem at?_append_of_lt getLocalState_fst newRandoms_append_rnd runMoves_append runTrace_append runTrace_snoc runVis_append runVis_snoc run_bind_fst run_bind_snd

cref_open
cref_open_tr

open DY DY.Comparse DY.Literal DY.Libsignal
open DY.Libsignal.TripleRatchet (computeMac messageVersion)
open DY.Libsignal.TripleRatchet
open DY.Libsignal.Refinement (aesCbcDecryptSymbol ExternCryptoLawsHold)
open DY.Libsignal.HwEvents DY.Libsignal.Rust
open CryptoGames CryptoGames.HMAC CryptoGames.HKDF
open CryptoGames.LibsignalSession CryptoGames.LibsignalSessionApi
open CryptoVerification
open CryptoVerification.LibsignalTripleRatchet CryptoVerification.LibsignalProtoCodec
open CryptoVerification.E2E CryptoVerification.E2E.Record
open CryptoVerification.E2E.Bin hiding RecordCanonical recordDeserializeOpenSpec encodeRecord
open CryptoVerification.E2E.Pqxdh.WireEntries
open CryptoVerification.E2E.Pqxdh.WireEntries.SymP3 hiding encodeRecord
open CryptoVerification.SessionModel.AdvanceAndFrame
open CryptoProofLib.Refinement (ExternInterpretation)
open Proofs.libsignal.RngG Proofs.libsignal.RngG.R3 Proofs.libsignal.RngG.CliPure.R3

open Symbolic.Swarm.CREF Symbolic.Swarm.CREF.CliPure Symbolic.Swarm.CREF.CliPure.TR
open Symbolic.Swarm.CREF.TR.Pure
open Symbolic.Swarm.TRREF.SpqrSemOf (spqrModelOf)

abbrev spqrSemOf_rdsnrwap3ad := compSemOf
open Symbolic.Swarm.CREF.CliPure.TR.RecvDecStep

theorem noRatchet_decryptWitness_of_seedKnown_at
    (interpretation : ExternInterpretation) (hCrypto : DY.Libsignal.Refinement.ExternCryptoLawsHold interpretation)
    (r₀ : ProtocolSetup) (S : SpqrSem) (hS : S = spqrSemOf_rdsnrwap3ad interpretation r₀)
    (g : Ghost) (p : Participant) (stateIdx : Nat) (ms₁ : List Move) (evs : List MachineEvent) (sent : List HwBytes)
    (recBytes body pt : HwBytes) (rec : RecordRec) (st : TRState) (g_rw : RecvWireGhost)
    (t₀ : DY.Bytes) (msg₀ : TRSignalMsg) (m : SignalMessage)
    (rk seed k_own : DY.Bytes) (newPqrState : HwBytes) (pqrKey : HKDF.Salt)
    {who : List Participant}
    (hmp : MatchedPrefix interpretation r₀ S who g ms₁ evs) (hfit : Symbolic.Swarm.CREF.TR.SrHonestVer.SendsFit evs)
    (hsent : sent = sentBodies evs)
    (hrecBytes : recBytes = recordBytes rec) (hrel : StateRel interpretation S g st rec)
    (hst : ((PersistentLocalState.getLocalState p stateIdx : Traceful TRState).run (runTraceMoves r₀ ms₁)).1 = some st)
    (hcanon_q : Symbolic.Swarm.CREF.TR.Pure.slots_RecordCanonical_Q Symbolic.Swarm.CREF.TR.Pure.slots_NonEmptyV1Q recBytes g_rw.sess)
    (hpq : PqFromHonest sent body) (htry : SignalMessage.tryFrom protoSignalCodec body = .ok m)
    (ht₀ : t₀ ∈ recvRepresentations interpretation r₀ S g ms₁ body) (hparse₀ : parseTrSignalMsg t₀ = some msg₀)
    (hver₀ : msg₀.version = messageVersion) (hrk₀ : msg₀.ratchetKey = rk)
    (hMacBytes : body.drop (body.length - 8) =
      gamma interpretation S g (computeMac (trMsgKeys k_own seed).macKey st.peerIk st.myIk msg₀.wire))
    (hPeerK : st.peerIk.AttackerKnows (runTraceMoves r₀ ms₁)) (hMyK : st.myIk.AttackerKnows (runTraceMoves r₀ ms₁))
    (hDecOk : interpretation DY.Libsignal.Refinement.aesCbcDecryptSymbol
      [m.ciphertext, gamma interpretation S g (trMsgKeys k_own seed).cipherKey,
       (gamma interpretation S g (trMsgKeys k_own seed).iv).take 16] = some pt)
    (hrecv_spqr : (Symbolic.Swarm.TRREF.SpqrSemOf.spqrModelOf interpretation).recv
      g_rw.sess.state.pqRatchetState m.pqRatchet = .ok (newPqrState, pqrKey))
    (hseed_kn : seed.AttackerKnows (runTraceMoves r₀ ms₁)) :
    ∃ (t' : DY.Bytes) (msg' : TRSignalMsg) (pqSalt ptTerm spqr' key : DY.Bytes) (spqrMsgIdx : UInt32),
      t' ∈ recvRepresentations interpretation r₀ S g ms₁ body ∧
      pqSalt.AttackerKnows (runTraceMoves r₀ ms₁) ∧ t'.AttackerKnows (runTraceMoves r₀ ms₁) ∧
      parseTrSignalMsg t' = some msg' ∧ msg'.version = messageVersion ∧
      msg'.ratchetKey = rk ∧ msg'.counter = msg₀.counter ∧
      Spqr.spqrRecv st.spqr msg'.pqRatchet spqrMsgIdx = some (spqr', key) ∧
      gamma interpretation S g spqr' = newPqrState ∧
      msg'.mac = computeMac (trMsgKeys pqSalt seed).macKey st.peerIk st.myIk msg'.wire ∧
      DY.SymEnc.symDec (trMsgKeys pqSalt seed).cipherKey (trMsgKeys pqSalt seed).iv msg'.ciphertext = some ptTerm ∧
      gamma interpretation S g t' = body ∧ gamma interpretation S g ptTerm = pt := by
  obtain ⟨t', msg', ptTerm, pqSalt, ht'_rep, ht'_kn, hpqSalt_kn, _, _, hparse', hver', hrk', hctr',
      _, hempty', hmac', hdec', hpt_gam⟩ :=
    forged_decrypt_rep_of_seedKnown_with_sendMsg_tr interpretation hCrypto r₀ S g ms₁ evs body pt m
      hmp hfit (hsent ▸ hpq) htry t₀ msg₀ ht₀ hparse₀ st seed k_own hMacBytes hPeerK hMyK hDecOk hseed_kn
  obtain ⟨_, hOut⟩ := spqrRecv_step_bridge_of_not_empty_pending interpretation hCrypto r₀ S hS g ms₁ p stateIdx
    recBytes body rec st st g_rw t' msg' m newPqrState pqrKey
    hst hrecBytes hrel rfl hcanon_q ht'_rep hparse' htry hempty' hrecv_spqr
  obtain ⟨spqrMsgIdx, spqr', key, hspqr_step, hspqr'_gam, _⟩ := hOut.exists_step
  exact ⟨t', msg', pqSalt, ptTerm, spqr', key, spqrMsgIdx,
    ht'_rep, hpqSalt_kn, ht'_kn, hparse', hver'.trans hver₀, hrk'.trans hrk₀, hctr',
    hspqr_step, hspqr'_gam, hmac', hdec', ht'_rep.2.1, hpt_gam⟩

theorem noRatchet_decryptWitness_of_authentic_at
    (interpretation : ExternInterpretation) (hCrypto : DY.Libsignal.Refinement.ExternCryptoLawsHold interpretation)
    (r₀ : ProtocolSetup) (S : SpqrSem) (hS : S = spqrSemOf_rdsnrwap3ad interpretation r₀)
    (g : Ghost) (p : Participant) (stateIdx : Nat) (ms₁ : List Move)
    (recBytes body pt : HwBytes) (rec : RecordRec) (st : TRState) (g_rw : RecvWireGhost)
    (t₀ : DY.Bytes) (msg₀ : TRSignalMsg) (m : SignalMessage)
    (rk seed salt : DY.Bytes) (newPqrState : HwBytes) (pqrKey : HKDF.Salt)
    (hrecBytes : recBytes = recordBytes rec) (hrel : StateRel interpretation S g st rec)
    (hst : ((PersistentLocalState.getLocalState p stateIdx : Traceful TRState).run (runTraceMoves r₀ ms₁)).1 = some st)
    (hcanon_q : Symbolic.Swarm.CREF.TR.Pure.slots_RecordCanonical_Q Symbolic.Swarm.CREF.TR.Pure.slots_NonEmptyV1Q recBytes g_rw.sess) (htry : SignalMessage.tryFrom protoSignalCodec body = .ok m)
    (ht₀ : t₀ ∈ recvRepresentations interpretation r₀ S g ms₁ body) (hparse₀ : parseTrSignalMsg t₀ = some msg₀)
    (hver₀ : msg₀.version = messageVersion) (hrk₀ : msg₀.ratchetKey = rk)
    (hrecv_spqr : (Symbolic.Swarm.TRREF.SpqrSemOf.spqrModelOf interpretation).recv
      g_rw.sess.state.pqRatchetState m.pqRatchet = .ok (newPqrState, pqrKey))
    (hAuth : AuthenticDecryptRepB3St interpretation r₀ S g ms₁ body pt t₀ msg₀ st salt seed)
    (_hMacBytes_salt : body.drop (body.length - 8) =
      gamma interpretation S g (computeMac (trMsgKeys salt seed).macKey st.peerIk st.myIk msg₀.wire)) :
    ∃ (t' : DY.Bytes) (msg' : TRSignalMsg) (pqSalt ptTerm spqr' key : DY.Bytes) (spqrMsgIdx : UInt32),
      t' ∈ recvRepresentations interpretation r₀ S g ms₁ body ∧
      pqSalt.AttackerKnows (runTraceMoves r₀ ms₁) ∧ t'.AttackerKnows (runTraceMoves r₀ ms₁) ∧
      parseTrSignalMsg t' = some msg' ∧ msg'.version = messageVersion ∧
      msg'.ratchetKey = rk ∧ msg'.counter = msg₀.counter ∧
      Spqr.spqrRecv st.spqr msg'.pqRatchet spqrMsgIdx = some (spqr', key) ∧
      gamma interpretation S g spqr' = newPqrState ∧
      msg'.mac = computeMac (trMsgKeys pqSalt seed).macKey st.peerIk st.myIk msg'.wire ∧
      DY.SymEnc.symDec (trMsgKeys pqSalt seed).cipherKey (trMsgKeys pqSalt seed).iv msg'.ciphertext = some ptTerm ∧
      gamma interpretation S g t' = body ∧ gamma interpretation S g ptTerm = pt := by
  obtain ⟨_, _, _, _, _, hempty, pqSalt, ptTerm, hpqSalt_kn, hmac₀, hdec₀, hpt_gam⟩ := hAuth
  obtain ⟨_, hOut⟩ := spqrRecv_step_bridge_of_not_empty_pending interpretation hCrypto r₀ S hS g ms₁ p stateIdx
    recBytes body rec st st g_rw t₀ msg₀ m newPqrState pqrKey
    hst hrecBytes hrel rfl hcanon_q ht₀ hparse₀ htry hempty hrecv_spqr
  obtain ⟨spqrMsgIdx, spqr', key, hspqr_step, hspqr'_gam, _⟩ := hOut.exists_step
  exact ⟨t₀, msg₀, pqSalt, ptTerm, spqr', key, spqrMsgIdx,
    ht₀, hpqSalt_kn, ht₀.1, hparse₀, hver₀, hrk₀, rfl,
    hspqr_step, hspqr'_gam, hmac₀, hdec₀, ht₀.2.1, hpt_gam⟩

theorem noRatchet_decryptWitness_of_g1_disj_at
    (interpretation : ExternInterpretation) (hCrypto : DY.Libsignal.Refinement.ExternCryptoLawsHold interpretation)
    (r₀ : ProtocolSetup) (S : SpqrSem) (hS : S = spqrSemOf_rdsnrwap3ad interpretation r₀)
    (g : Ghost) (p : Participant) (stateIdx : Nat) (ms₁ : List Move) (evs : List MachineEvent) (sent : List HwBytes)
    (recBytes body pt : HwBytes) (rec : RecordRec) (st : TRState) (g_rw : RecvWireGhost)
    (t₀ : DY.Bytes) (msg₀ : TRSignalMsg) (m : SignalMessage)
    (rk seed k_own : DY.Bytes) (newPqrState : HwBytes) (pqrKey : HKDF.Salt)
    {who : List Participant}
    (hmp : MatchedPrefix interpretation r₀ S who g ms₁ evs) (hfit : Symbolic.Swarm.CREF.TR.SrHonestVer.SendsFit evs)
    (hsent : sent = sentBodies evs)
    (hrecBytes : recBytes = recordBytes rec) (hrel : StateRel interpretation S g st rec)
    (hst : ((PersistentLocalState.getLocalState p stateIdx : Traceful TRState).run (runTraceMoves r₀ ms₁)).1 = some st)
    (hcanon_q : Symbolic.Swarm.CREF.TR.Pure.slots_RecordCanonical_Q Symbolic.Swarm.CREF.TR.Pure.slots_NonEmptyV1Q recBytes g_rw.sess)
    (hpq : PqFromHonest sent body) (htry : SignalMessage.tryFrom protoSignalCodec body = .ok m)
    (ht₀ : t₀ ∈ recvRepresentations interpretation r₀ S g ms₁ body) (hparse₀ : parseTrSignalMsg t₀ = some msg₀)
    (hver₀ : msg₀.version = messageVersion) (hrk₀ : msg₀.ratchetKey = rk)
    (hMacBytes : body.drop (body.length - 8) =
      gamma interpretation S g (computeMac (trMsgKeys k_own seed).macKey st.peerIk st.myIk msg₀.wire))
    (hPeerK : st.peerIk.AttackerKnows (runTraceMoves r₀ ms₁)) (hMyK : st.myIk.AttackerKnows (runTraceMoves r₀ ms₁))
    (hDecOk : interpretation DY.Libsignal.Refinement.aesCbcDecryptSymbol
      [m.ciphertext, gamma interpretation S g (trMsgKeys k_own seed).cipherKey,
       (gamma interpretation S g (trMsgKeys k_own seed).iv).take 16] = some pt)
    (hrecv_spqr : (Symbolic.Swarm.TRREF.SpqrSemOf.spqrModelOf interpretation).recv
      g_rw.sess.state.pqRatchetState m.pqRatchet = .ok (newPqrState, pqrKey))
    (hDisj : seed.AttackerKnows (runTraceMoves r₀ ms₁) ∨
      ∃ salt ∈ honestSalts r₀ ms₁,
        AuthenticDecryptRepB3St interpretation r₀ S g ms₁ body pt t₀ msg₀ st salt seed ∧
        gamma interpretation S g (computeMac (trMsgKeys k_own seed).macKey st.peerIk st.myIk msg₀.wire) =
          gamma interpretation S g (computeMac (trMsgKeys salt seed).macKey st.peerIk st.myIk msg₀.wire) ∧
        interpretation DY.Libsignal.Refinement.aesCbcDecryptSymbol
          [m.ciphertext, gamma interpretation S g (trMsgKeys salt seed).cipherKey,
           (gamma interpretation S g (trMsgKeys salt seed).iv).take 16] = some pt) :
    ∃ (t' : DY.Bytes) (msg' : TRSignalMsg) (pqSalt ptTerm spqr' key : DY.Bytes) (spqrMsgIdx : UInt32),
      t' ∈ recvRepresentations interpretation r₀ S g ms₁ body ∧
      pqSalt.AttackerKnows (runTraceMoves r₀ ms₁) ∧ t'.AttackerKnows (runTraceMoves r₀ ms₁) ∧
      parseTrSignalMsg t' = some msg' ∧ msg'.version = messageVersion ∧
      msg'.ratchetKey = rk ∧ msg'.counter = msg₀.counter ∧
      Spqr.spqrRecv st.spqr msg'.pqRatchet spqrMsgIdx = some (spqr', key) ∧
      gamma interpretation S g spqr' = newPqrState ∧
      msg'.mac = computeMac (trMsgKeys pqSalt seed).macKey st.peerIk st.myIk msg'.wire ∧
      DY.SymEnc.symDec (trMsgKeys pqSalt seed).cipherKey (trMsgKeys pqSalt seed).iv msg'.ciphertext = some ptTerm ∧
      gamma interpretation S g t' = body ∧ gamma interpretation S g ptTerm = pt :=
  hDisj.elim
    (noRatchet_decryptWitness_of_seedKnown_at interpretation hCrypto r₀ S hS g p stateIdx ms₁ evs sent
      recBytes body pt rec st g_rw t₀ msg₀ m rk seed k_own newPqrState pqrKey
      hmp hfit hsent hrecBytes hrel hst hcanon_q hpq htry ht₀ hparse₀ hver₀ hrk₀
      hMacBytes hPeerK hMyK hDecOk hrecv_spqr)
    fun ⟨salt, _, hAuth, hMacEq, _⟩ =>
      noRatchet_decryptWitness_of_authentic_at interpretation hCrypto r₀ S hS g p stateIdx ms₁
        recBytes body pt rec st g_rw t₀ msg₀ m rk seed salt newPqrState pqrKey
        hrecBytes hrel hst hcanon_q htry ht₀ hparse₀ hver₀ hrk₀ hrecv_spqr hAuth
        (hMacBytes.trans hMacEq)

end Symbolic.Swarm.CREF.CliPure.TR.RecvDecStepAt
