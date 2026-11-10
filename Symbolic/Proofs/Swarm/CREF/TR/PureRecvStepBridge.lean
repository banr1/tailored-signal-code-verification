/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Symbolic.Proofs.Swarm.CREF.Cli.PureCRel
import DY.Trace.Basic
import DY.Actions.ProtocolEvent
public import Symbolic.Proofs.Swarm.CREF.Cli.Rpk.RecvDecStepCommonPureA
public import Symbolic.Proofs.Swarm.CREF.Cli.Rpk.RecvDecStepSpqrPureA
public import Symbolic.Proofs.Swarm.CREF.TR.FreshSigmaReach
public import Symbolic.Proofs.Swarm.CREF.TR.G1.ShapeIdInv
public import Symbolic.Proofs.Swarm.CREF.TR.G1.WireShapeInj
public import Symbolic.Proofs.Swarm.CREF.TR.RecvDec
public import Symbolic.Proofs.Swarm.CREF.TR.SrHonestVer
import Symbolic.Proofs.SpecLemmas.Model.EquationalTheory.Spqr
import Symbolic.Proofs.SpecLemmas.Model.EquationalTheory.TrWireMsg
import Symbolic.Proofs.Swarm.CREF.Cli.Rpk.RatchetDHRkSwapStepTRPure
import Symbolic.Proofs.Swarm.CREF.Cli.Rpk.RatchetDHRkSwapStepTRPureA
import Symbolic.Proofs.Swarm.CREF.Cli.Rpk.RecvDecStepCommonPure
import Symbolic.Proofs.Swarm.CREF.Cli.Rpk.RecvDecStepSpqrPure
import Symbolic.Proofs.Swarm.CREF.Prelude
import Symbolic.Proofs.Swarm.CREF.TR.FreshSigmaHead
import Symbolic.Proofs.Swarm.CREF.TR.HonestPqNoTrWire
import Symbolic.Proofs.Swarm.CREF.TR.PureRecvEval
import Symbolic.Proofs.Swarm.CREF.TROpen
import Symbolic.Proofs.Swarm.CREF.TR.PQModelRunNil -- shake: keep
import Symbolic.DYBridge.DY.Trace.Basic
import Symbolic.DYBridge.DY.Actions.ProtocolEvent

/-!
# Ghost-Free Canonical and Singleton `PureTRRecordStateInv` Step Bridges

Ghost-free `slots_RecordCanonical_Q` and `PureTRRecordStateInv` variants of the SPQR and
singleton decrypt-tail step lemmas for `recv_wire` whisper verification.
-/

@[expose] public section

set_option autoImplicit false

cref_hide_foreign_instances

namespace Symbolic.Swarm.CREF.CliPure.TR.PureRecvEval
open Symbolic.Swarm.CREF.TR hiding newRandoms_append_rnd runMoves_append runTrace_append runTrace_snoc runVis_append runVis_snoc

cref_open
cref_open_tr

open DY DY.Comparse DY.Literal DY.Libsignal
open DY.Libsignal.TripleRatchet (RecvChain setRecvChain consumeMessageKey kdfCk chainKeyAt
  messageVersion createChain)
open DY.Libsignal.TripleRatchet
open DY.Libsignal.Refinement (ExternCryptoLawsHold aesCbcDecryptSymbol)
open DY.Libsignal.HwEvents
open CryptoGames CryptoGames.HMAC CryptoGames.HKDF
open CryptoGames.LibsignalSession CryptoGames.LibsignalSessionApi
open CryptoVerification.LibsignalProtoCodec
open CryptoVerification.E2E.Pqxdh.WireEntries.SymP3 (RecvWireGhost)
open CryptoProofLib.Refinement (ExternInterpretation)
open Swarm.Phase0WholeFunctionBridge (sessionToRecordRec)
open Symbolic.Swarm.CREF Symbolic.Swarm.CREF.CliPure
open Symbolic.Swarm.CREF.CliPure.TR
open Symbolic.Swarm.TRREF.SpqrSemOf (spqrModelOf)

theorem rec_eq_sessionToRecordRec_of_pureCanonical_Q
    {Q : List (BitVec 8) → Prop} {rec : RecordRec} {recBytes : HwBytes}
    {s : Session (List (BitVec 8))}
    (hrecBytes : recBytes = recordBytes rec)
    (hc : TR.Pure.slots_RecordCanonical_Q Q recBytes s) :
    normPending rec = normPending (TR.RecvDecStep.sessionToRecordRecPending s) := by
  have hb := (recordBytes_sessionToRecordRecPending_of_pureCanonical_Q hc).1
  apply TR.recordBytes_injective
  rw [← hrecBytes, hc.1]
  exact hb.symm

theorem pqRatchetState_eq_gamma_pending_pure
    (interpretation : ExternInterpretation) (S : TR.RecvDecStep.SpqrSem) (g : Ghost)
    (recBytes : HwBytes) (rec : RecordRec) (st st_in : TRState) (g_rw : RecvWireGhost)
    (hrecBytes : recBytes = recordBytes rec) (hrel : StateRel interpretation S g st rec)
    (hcanon_q : TR.Pure.slots_RecordCanonical_Q TR.Pure.slots_NonEmptyV1Q recBytes g_rw.sess)
    (hspqr_in : st_in.spqr = st.spqr) :
    normPending rec = normPending (TR.RecvDecStep.sessionToRecordRecPending g_rw.sess) ∧
    StateRel interpretation S g st (sessionToRecordRec g_rw.sess) ∧
    g_rw.sess.state.pqRatchetState = gamma interpretation S g st.spqr ∧
    g_rw.sess.state.pqRatchetState = gamma interpretation S g st_in.spqr ∧
    gamma interpretation S g st_in.spqr =
      (sessionOf interpretation (gamma interpretation S g) st_in).pqRatchetState ∧
    g_rw.sess.state.sessionVersion = 4#32 ∧
    (∃ r : RecordRec, recBytes = recordBytes r ∧ r.current.sessionVersion = 4#32) := by
  obtain ⟨hpq, hver⟩ := TR.RecvDecStep.stateRel_pqRatchetState_and_sessionVersion hrel
  have hrec_eq := rec_eq_sessionToRecordRec_of_pureCanonical_Q hrecBytes hcanon_q
  have hrel_sess : StateRel interpretation S g st (sessionToRecordRec g_rw.sess) := by
    rw [← TR.RecvDecStep.stateRel_sessionToRecordRecPending_iff,
        ← TR.RecvDecStep.stateRel_normPending_iff,
        ← hrec_eq, TR.RecvDecStep.stateRel_normPending_iff]
    exact hrel
  have hpq_norm : rec.current.pqRatchetState = g_rw.sess.state.pqRatchetState :=
    congrArg (fun r => r.current.pqRatchetState) hrec_eq
  have hver_norm : rec.current.sessionVersion = g_rw.sess.state.sessionVersion :=
    congrArg (fun r => r.current.sessionVersion) hrec_eq
  have hpq_sess : g_rw.sess.state.pqRatchetState = gamma interpretation S g st.spqr := by
    rw [← hpq_norm, hpq]
  have hver_sess : g_rw.sess.state.sessionVersion = 4#32 := by
    rw [← hver_norm, hver]
  refine ⟨hrec_eq, hrel_sess, hpq_sess, ?_, rfl, hver_sess, ⟨rec, hrecBytes, hver⟩⟩
  rw [hpq_sess, hspqr_in]

theorem spqrRecv_step_bridge_of_not_empty_pending_pure
    (interpretation : ExternInterpretation) (hceh : ExternCryptoLawsHold interpretation)
    (r₀ : ProtocolSetup) (S : TR.RecvDecStep.SpqrSem) (hS : S = compSemOf interpretation r₀)
    (g : Ghost) (ms₁ : List Move) (p : Participant) (stateIdx : Nat) (recBytes body : HwBytes)
    (rec : RecordRec) (st st_in : TRState) (g_rw : RecvWireGhost)
    (t : DY.Bytes) (msg : TRSignalMsg) (m : SignalMessage) (newPqrState : HwBytes) (pqrKey : HKDF.Salt)
    (hst : ((PersistentLocalState.getLocalState p stateIdx : Traceful TRState).run (runTraceMoves r₀ ms₁)).1 = some st)
    (hrecBytes : recBytes = recordBytes rec) (hrel : StateRel interpretation S g st rec) (hspqr_eq : st_in.spqr = st.spqr)
    (hcanon_q : TR.Pure.slots_RecordCanonical_Q TR.Pure.slots_NonEmptyV1Q recBytes g_rw.sess)
    (ht_rep : t ∈ recvRepresentations interpretation r₀ S g ms₁ body) (hparse : parseTrSignalMsg t = some msg)
    (htry : SignalMessage.tryFrom protoSignalCodec body = .ok m) (hempty : DY.Spqr.spqrEmptyMsg msg.pqRatchet = false)
    (hrecv_spqr : (spqrModelOf interpretation).recv g_rw.sess.state.pqRatchetState m.pqRatchet = .ok (newPqrState, pqrKey)) :
    g_rw.sess.state.pqRatchetState = gamma interpretation S g st_in.spqr ∧
    TR.RecvDecStep.SpqrRecvStepOut interpretation S g st_in msg newPqrState pqrKey := by
  obtain ⟨_, _, _, hpq_in, hpre_eq, _, _⟩ :=
    pqRatchetState_eq_gamma_pending_pure interpretation S g recBytes rec st st_in g_rw hrecBytes hrel hcanon_q hspqr_eq
  obtain ⟨hgam_st, hgam_key⟩ :=
    TR.RecvDecStep.spqrRecv_step_gamma_state_and_key interpretation hceh r₀ S hS g ms₁ body st_in g_rw
      t msg m newPqrState pqrKey hpq_in ht_rep hparse htry hrecv_spqr
  have hinit_in : TR.RecvDecStep.SpqrInitDirOK st_in.spqr := by
    rw [hspqr_eq]; exact TR.RecvDecStep.spqrInitDirOK_of_getLocalState hst
  obtain ⟨spqr', key, hstep⟩ :=
    TR.RecvDecStep.spqrRecv_zero_isSome_of_not_empty_of_initDir hempty hinit_in
  have hst' := DY.Spqr.spqrRecv_state st_in.spqr msg.pqRatchet 0 (spqr', key) hstep
  dsimp only at hst'
  refine ⟨hpq_in, ⟨hpre_eq, 0, spqr', key, hstep, ?_, hgam_key⟩⟩
  rw [hst']; exact hgam_st

private theorem ratchetKey_attackerKnows_of_parseTrSignalMsg_step
    {tr : ExecTrace} {t : DY.Bytes} {msg : TRSignalMsg}
    (ht : t.AttackerKnows tr) (hparse : parseTrSignalMsg t = some msg) :
    msg.ratchetKey.AttackerKnows tr := by
  have hsp := Concat.attacker_knows_split t (t.length - Trunc.trunc8Length) tr ht
  unfold parseTrSignalMsg at hparse
  rcases hsplit : Concat.split t (t.length - Trunc.trunc8Length) with _ | ⟨w, m⟩
  · rw [hsplit] at hparse; cases hparse
  · rw [hsplit] at hsp hparse; dsimp only [Bind.bind, Option.bind] at hparse
    rcases hwf : DY.TrWire.trWireMsgFields? w with _ | x
    · rw [hwf] at hparse; cases hparse
    · rw [hwf] at hparse; injection hparse with hmsg; subst hmsg
      rw [DY.TrWire.trWireMsg_of_fields? hwf] at hsp
      exact (DY.TrWire.attacker_knows_trWireMsg_args x.version x.senderRatchetKey x.counter
        x.previousCounter x.ciphertext x.pqRatchet x.encodingVariation tr hsp.1).1

theorem spqrRecv_step_bridge_ratchetDH_rkSwap_nw_pure
    (interpretation : ExternInterpretation) (hEq : ExternCryptoLawsHold interpretation) (r₀ : ProtocolSetup)
    (S : TR.RecvDecStep.SpqrSem) (hS : S = compSemOf interpretation r₀)
    (g' : Ghost) (p : Participant) (stateIdx : Nat) (ms₁ : List Move) (acc_evs : List MachineEvent)
    (recBytes body ptext : HwBytes) (rec : RecordRec) (st₀ : TRState) (g_rw : RecvWireGhost)
    (t₀ : DY.Bytes) (msg₀ : TRSignalMsg) (m : SignalMessage) (mkSeed k_own : DY.Bytes) (c'₀ : RecvChain)
    (newPqrState : HwBytes) (pqrKey : HKDF.Salt) {who : List Participant}
    (hmp' : MatchedPrefix interpretation r₀ S who g' ms₁ acc_evs)
    (hfit : TR.SrHonestVer.SendsFit acc_evs)
    (hrecBytes : recBytes = recordBytes rec)
    (hrel : StateRel interpretation S g' st₀ rec)
    (hst : ((PersistentLocalState.getLocalState p stateIdx : Traceful TRState).run
      (runTraceMoves r₀ ms₁)).1 = some st₀)
    (hcanon_q : TR.Pure.slots_RecordCanonical_Q TR.Pure.slots_NonEmptyV1Q recBytes g_rw.sess)
    (hpq : PqFromHonest (sentBodies acc_evs) body)
    (htry : SignalMessage.tryFrom protoSignalCodec body = .ok m)
    (ht₀ : t₀ ∈ recvRepresentations interpretation r₀ S g' ms₁ body)
    (hparse₀ : parseTrSignalMsg t₀ = some msg₀)
    (hver₀ : msg₀.version = messageVersion)
    (hctr₀ : msg₀.counter = UInt32.ofBitVec m.counter)
    (hcons₀ : consumeMessageKey
      (TR.RecvDec.trDhRatchetState st₀ msg₀.ratchetKey ((runTraceMoves r₀ ms₁).length + 2)).2 msg₀.counter =
      some (mkSeed, c'₀))
    (hMacBytes : body.drop (body.length - 8) =
      gamma interpretation S g' (DY.Libsignal.TripleRatchet.computeMac (trMsgKeys k_own mkSeed).macKey st₀.peerIk st₀.myIk msg₀.wire))
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
        TR.G1.TermShapeId rk_c ∧
        rk_c.AttackerKnows (runTraceMoves r₀ ms₁) ∧
        gamma interpretation S g' rk_c = gamma interpretation S g' msg₀.ratchetKey ∧
        seed_c.AttackerKnows (runTraceMoves r₀ ms₁) ∧
        gamma interpretation S g' seed_c = gamma interpretation S g' mkSeed) ∨
      (TR.G1.TermShapeId msg₀.ratchetKey ∧
        TR.G1.AuthenticDecryptRep interpretation r₀ S g' ms₁ body ptext msg₀ st₀ mkSeed k_own)) :
    ∃ (rk_c seed_c : DY.Bytes) (c'_c : RecvChain) (t' : DY.Bytes) (msg' : TRSignalMsg)
      (pqSalt ptTerm spqr' key : DY.Bytes) (spqrMsgIdx : UInt32),
      TR.G1.TermShapeId rk_c ∧
      gamma interpretation S g' rk_c = gamma interpretation S g' msg₀.ratchetKey ∧
      gamma interpretation S g' seed_c = gamma interpretation S g' mkSeed ∧
      consumeMessageKey (TR.RecvDec.trDhRatchetState st₀ rk_c ((runTraceMoves r₀ ms₁).length + 2)).2 msg'.counter =
        some (seed_c, c'_c) ∧
      t' ∈ recvRepresentations interpretation r₀ S g' ms₁ body ∧
      pqSalt.AttackerKnows (runTraceMoves r₀ ms₁) ∧
      t'.AttackerKnows (runTraceMoves r₀ ms₁) ∧
      parseTrSignalMsg t' = some msg' ∧
      msg'.version = messageVersion ∧
      msg'.ratchetKey = rk_c ∧
      msg'.counter = UInt32.ofBitVec m.counter ∧
      Spqr.spqrRecv (TR.RecvDec.trDhRatchetState st₀ rk_c ((runTraceMoves r₀ ms₁).length + 2)).1.spqr
        msg'.pqRatchet spqrMsgIdx = some (spqr', key) ∧
      gamma interpretation S g' spqr' = newPqrState ∧
      msg'.mac = DY.Libsignal.TripleRatchet.computeMac (trMsgKeys pqSalt seed_c).macKey
        (TR.RecvDec.trDhRatchetState st₀ rk_c ((runTraceMoves r₀ ms₁).length + 2)).1.peerIk
        (TR.RecvDec.trDhRatchetState st₀ rk_c ((runTraceMoves r₀ ms₁).length + 2)).1.myIk msg'.wire ∧
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
        TR.G1.TermShapeId rk_c ∧
        gamma interpretation S g' rk_c = gamma interpretation S g' msg₀.ratchetKey ∧
        gamma interpretation S g' seed_c = gamma interpretation S g' mkSeed ∧
        consumeMessageKey (TR.RecvDec.trDhRatchetState st₀ rk_c ((runTraceMoves r₀ ms₁).length + 2)).2 msg₀.counter =
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
        msg'.mac = DY.Libsignal.TripleRatchet.computeMac (trMsgKeys pqSalt seed_c).macKey st₀.peerIk st₀.myIk msg'.wire ∧
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
        (TR.G1.consumeMessageKey_trDhRatchetState_rkSwap_of_msg₀ st₀ msg₀
          ((runTraceMoves r₀ ms₁).length + 2) mkSeed c'₀ rk_c hcons₀).1
      obtain ⟨t', msg', ptTerm, pqSalt, ht'_rep, ht'_kn, hpqSalt_kn, hpqSalt_gam, ht'_gam,
        hparse', hver', hrk', hctr', hpq_gam, hnot_empty, hmac', hdec', hpt_gam, hpq_prov⟩ :=
        TR.G1.forged_decrypt_rep_of_rkSwap_seedKnown_with_sendMsg_tr_prov interpretation hEq r₀ S g' ms₁ acc_evs
          body ptext m hmp' hfit hpq htry t₀ msg₀ ht₀ hparse₀ st₀ rk_c seed_c mkSeed k_own
          hrk_c_kn hγ_rk_c hseed_c_kn hγ_seed_c hMacBytes hPeerK hMyK hDecOk
      exact ⟨rk_c, seed_c, c'_c, t', msg', ptTerm, pqSalt, hrk_c_sid, hγ_rk_c, hγ_seed_c, hcons_c,
        ht'_rep, ht'_kn, hpqSalt_kn, hpqSalt_gam, ht'_gam, hparse', hver', hrk', hctr',
        hpq_gam, hnot_empty, hmac', hdec', hpt_gam, hpq_prov⟩
    · obtain ⟨t', msg', ptTerm, pqSalt, ht'_rep, ht'_kn, hpqSalt_kn, hpqSalt_gam, ht'_gam,
        hparse', hver', hrk', hctr', hpq_gam, hmac', hdec', hpt_gam⟩ := hAuth
      rcases TR.honest_encrypt_mac_pqRatchet_prov_or_keysKnown_tr
          hmp'.2.1.2.2.1.1 ht'_kn hparse' hmac' with
        ⟨st_s, t_c, coinsLen, hst_s, hpq_eq, hnot_empty⟩ | ⟨hck_kn, hmk_kn, hiv_kn⟩
      · exact ⟨msg₀.ratchetKey, mkSeed, c'₀, t', msg', ptTerm, pqSalt, hrk₀_sid, rfl, rfl, hcons₀,
          ht'_rep, ht'_kn, hpqSalt_kn, hpqSalt_gam, ht'_gam, hparse', hver', hrk', hctr',
          hpq_gam, hnot_empty, hmac', hdec', hpt_gam, st_s, t_c, coinsLen, hst_s, hpq_eq⟩
      · have hrk₀_kn : msg₀.ratchetKey.AttackerKnows (runTraceMoves r₀ ms₁) :=
          ratchetKey_attackerKnows_of_parseTrSignalMsg_step ht₀.1 hparse₀
        obtain ⟨t'', msg'', ptTerm'', ht''_rep, ht''_kn, ht''_gam, hparse'', hver'', hrk'', hctr'',
          hpq_gam'', hnot_empty'', hmac'', hdec'', hpt_gam'', hpq_prov''⟩ :=
          TR.G1.forged_decrypt_rep_of_rkSwap_keysKnown_with_sendMsg_tr_prov interpretation hEq r₀ S g' ms₁ acc_evs
            body ptext m hmp' hfit hpq htry t₀ msg₀ ht₀ hparse₀ st₀ msg₀.ratchetKey mkSeed mkSeed k_own pqSalt
            hrk₀_kn rfl rfl hpqSalt_kn hpqSalt_gam hck_kn hmk_kn hiv_kn hMacBytes hPeerK hMyK hDecOk
        exact ⟨msg₀.ratchetKey, mkSeed, c'₀, t'', msg'', ptTerm'', pqSalt, hrk₀_sid, rfl, rfl, hcons₀,
          ht''_rep, ht''_kn, hpqSalt_kn, hpqSalt_gam, ht''_gam, hparse'', hver'', hrk'', hctr'',
          hpq_gam'', hnot_empty'', hmac'', hdec'', hpt_gam'', hpq_prov''⟩
  obtain ⟨rk_c, seed_c, c'_c, t', msg', ptTerm, pqSalt, hrk_c_sid, hγ_rk_c, hγ_seed_c, hcons_c,
    ht'_rep, ht'_kn, hpqSalt_kn, _, ht'_gam, hparse', hver', hrk', hctr',
    _, hnot_empty, hmac', hdec', hpt_gam, hpq_prov⟩ := hRep
  let st1_c := (TR.RecvDec.trDhRatchetState st₀ rk_c ((runTraceMoves r₀ ms₁).length + 2)).1
  have hSpqrOut : TR.RecvDecStep.SpqrRecvStepOut interpretation S g' st1_c msg' newPqrState pqrKey :=
    (spqrRecv_step_bridge_of_not_empty_pending_pure interpretation hEq r₀ S hS g' ms₁ p stateIdx
      recBytes body rec st₀ st1_c g_rw t' msg' m newPqrState pqrKey
      hst hrecBytes hrel rfl hcanon_q ht'_rep hparse' htry hnot_empty hrecv_spqr).2
  obtain ⟨spqrMsgIdx, spqr', key, hspqr_step, hspqr'_gam, _⟩ := hSpqrOut.exists_step
  have hcons_c' :
      consumeMessageKey (TR.RecvDec.trDhRatchetState st₀ rk_c ((runTraceMoves r₀ ms₁).length + 2)).2 msg'.counter =
        some (seed_c, c'_c) := by
    rw [hctr']; exact hcons_c
  exact ⟨rk_c, seed_c, c'_c, t', msg', pqSalt, ptTerm, spqr', key, spqrMsgIdx,
    hrk_c_sid, hγ_rk_c, hγ_seed_c, hcons_c', ht'_rep, hpqSalt_kn, ht'_kn, hparse',
    hver'.trans hver₀, hrk', hctr'.trans hctr₀, hspqr_step, hspqr'_gam, hmac', hdec', ht'_gam, hpt_gam,
    hpq_prov⟩

theorem pureTRRecordStateInv_decTail_single
    {interpretation : ExternInterpretation} {r₀ : ProtocolSetup} {S : TR.RecvDecStep.SpqrSem}
    {Z : PureTRSlots} {g : Ghost} {ms : List Move} {m : Move}
    {p : Participant} {stateIdx : Nat} {st : TRState} {rec' : RecordRec} {newBytes : HwBytes}
    {key seed pqSalt ptTerm spqr' pk : DY.Bytes} {c c' : RecvChain} {n : UInt32}
    (hp_mem : p = r₀.alice ∨ p = r₀.bob)
    (htr : runTraceMoves r₀ (ms ++ [m]) =
      TR.RecvDecStep.decTailTr ((runTraceMoves r₀ ms).append (⟨key⟩ : Network.ExecEntryT)) p stateIdx st c c'
        pk seed pqSalt ptTerm spqr' n)
    (hnew : newBytes = recordBytes rec')
    (hrel' : StateRel interpretation S g { st with recv := setRecvChain st.recv c', spqr := spqr' }
      rec')
    (hsk' : ∀ c_k ∈ rec'.current.receiverChains, ∀ k ∈ c_k.messageKeys,
      ∃ pk_k rIdx srcIdx skIdx seed_k,
        (runTraceMoves r₀ (ms ++ [m])).EventLoggedAt
          (TREvent.SkippedKeyStored (st.sessionInfo p) pk_k (UInt32.ofBitVec k.1) seed_k rIdx srcIdx)
          skIdx ∧
        !skippedKeyUsedB (runTraceMoves r₀ (ms ++ [m])) skIdx ∧
        !receiverKeyUsedB (runTraceMoves r₀ (ms ++ [m])) (st.sessionInfo p) seed_k (UInt32.ofBitVec k.1)
          rIdx ∧
        gamma interpretation S g seed_k = k.2 ∧
        c_k.senderRatchetKey = serializedKey (gamma interpretation S g pk_k) ∧
        (findRecvChain { st with recv := setRecvChain st.recv c', spqr := spqr' }.toDRState.recv pk_k).isSome = true)
    (hcanon' : newBytes.length < 2 ^ 32 - 2 ^ 20 → Z.canon p newBytes)
    (hks : TRKeyShape interpretation S g st)
    (hnd' : (rec'.current.receiverChains.map ChainRec.senderRatchetKey).Nodup ∧
      (∀ c_k ∈ rec'.current.receiverChains, (c_k.messageKeys.map Prod.fst).Nodup) ∧
      ∀ c_k ∈ rec'.current.receiverChains, ∀ k ∈ c_k.messageKeys,
        ∃ ck, c_k.chainKey = some ck ∧ k.1 < ck.1) :
    PureTRRecordStateInv interpretation r₀ S Z g (ms ++ [m])
      (fun q => if q = p then some newBytes else none) := by
  intro q b hqb
  by_cases hqp : q = p
  · subst hqp; simp only [↓reduceIte, Option.some.injEq] at hqb; subst hqb
    refine ⟨hp_mem, rec', { st with recv := setRecvChain st.recv c', spqr := spqr' },
      ((runTraceMoves r₀ ms).append (⟨key⟩ : Network.ExecEntryT)).length +
        (n.toNat - c.index.toNat) + 2, hnew, ?_, ?_, hrel', hsk', hcanon',
      TR.RecvDecStep.trKeyShape_setRecvChain_spqr hks c' spqr', hnd'⟩
    · rw [htr, TR.RecvDecStep.getLocalState_decTailTr_last]
    · rw [htr, TR.RecvDecStep.isCurrentSnapshot_decTailTr_last]
  · simp only [hqp, ↓reduceIte] at hqb; cases hqb

theorem pureTRRecordStateInv_updateFreshAt {interpretation : ExternInterpretation} {r₀ : ProtocolSetup}
    {S : OpaqueSymbolSemantics} {Z : PureTRSlots} {g : Ghost} {ms : List Move}
    {records : Participant → Option HwBytes}
    (hrun : ModelRun r₀ ms)
    (hinv : PureTRRecordStateInv interpretation r₀ S Z g ms records) {ts : Nat}
    (hts : (runTraceMoves r₀ ms).length ≤ ts) (n : Nat) (m : HwBytes) :
    PureTRRecordStateInv interpretation r₀ S Z { g with σ := FreshSigma.updateFreshAt g.σ ts n m } ms records := by
  have htr : FreshSigma.TraceEntriesLt interpretation S g ts (runTraceMoves r₀ ms) :=
    FreshSigma.traceEntriesLt_of_reachable interpretation S g ts hrun.2.2.1.1 hts
  intro p recBytes hrec
  obtain ⟨hp_mem, rec, st, stateIdx, hrecBytes, hst, hcur, hrel, hsk, hcanon, hks, hnd⟩ :=
    hinv p recBytes hrec
  have hst_lt : FreshSigma.StateStampsLt interpretation S g ts st :=
    FreshSigma.traceEntriesLt_at?_st htr (FreshSigma.at?_eq_some_of_getLocalState_some hst)
  refine ⟨hp_mem, rec, st, stateIdx, hrecBytes, hst, hcur,
    (FreshSigma.stateRel_updateFreshAt_of_stampsLt interpretation S g ts n m st rec hst_lt).mpr hrel,
    ?_, hcanon, FreshSigma.trKeyShape_updateFreshAt_of_stampsLt hst_lt hks, hnd⟩
  intro c hc k hk
  obtain ⟨pk, rIdx, srcIdx, skIdx, seed, hat, hused, hrused, hk2, hsrk, hfind⟩ := hsk c hc k hk
  have hat' : ((runTraceMoves r₀ ms).at? skIdx : Option (ProtocolEvent.ExecEntryT TREvent)) =
      some ⟨TREvent.SkippedKeyStored (st.sessionInfo p) pk ⟨k.1⟩ seed rIdx srcIdx⟩ := by
    rwa [← Symbolic.DYBridge.DY.Trace.EventLoggedAt_eq_1]
  have hev : FreshSigma.StampsLt interpretation S g ts seed ∧ FreshSigma.StampsLt interpretation S g ts pk :=
    FreshSigma.traceEntriesLt_at?_tr htr hat'
  refine ⟨pk, rIdx, srcIdx, skIdx, seed, hat, hused, hrused, ?_, ?_, hfind⟩
  · rwa [FreshSigma.gamma_updateFreshAt_of_stampsLt interpretation S g ts n m seed hev.1]
  · rwa [FreshSigma.gamma_updateFreshAt_of_stampsLt interpretation S g ts n m pk hev.2]

theorem pureRatchetDH_sigma_bridge
    (interpretation : ExternInterpretation) (r₀ : ProtocolSetup) (_hwf : ProtocolSetupWF r₀)
    (S : TR.RecvDecStep.SpqrSem) (Z : PureTRSlots) {who : List Participant} (g : Ghost) (ms₁ : List Move) (τ : List MachineEvent)
    (records : Participant → Option HwBytes) (p : Participant) (stateIdx : Nat)
    (st : TRState) (rec : RecordRec) (t : DY.Bytes) (msg : TRSignalMsg)
    (ts : Nat) (rngBytes : HwBytes) (hts : (runTraceMoves r₀ ms₁).length ≤ ts)
    (hmp : DY.Libsignal.Composed.Refinement.MatchedPrefix interpretation r₀ S who g ms₁ τ)
    (hrsi : PureTRRecordStateInv interpretation r₀ S Z g ms₁ records)
    (hst : ((PersistentLocalState.getLocalState p stateIdx : Traceful TRState).run (runTraceMoves r₀ ms₁)).1 = some st)
    (hrel : StateRel interpretation S g st rec) (hks : TRKeyShape interpretation S g st)
    (ht_kn : t.AttackerKnows (runTraceMoves r₀ ms₁)) (hparse : parseTrSignalMsg t = some msg) :
    let g' : Ghost := { g with σ := FreshSigma.updateFreshAt g.σ ts 32 rngBytes }
    g'.σ ts 32 = rngBytes ∧
    DY.Libsignal.Composed.Refinement.MatchedPrefix interpretation r₀ S who g' ms₁ τ ∧
    PureTRRecordStateInv interpretation r₀ S Z g' ms₁ records ∧
    StateRel interpretation S g' st rec ∧
    TRKeyShape interpretation S g' st ∧
    FreshSigma.StateStampsLt interpretation S g ts st ∧
    FreshSigma.TRSignalMsgStampsLt interpretation S g ts msg ∧
    gamma interpretation S g' t = gamma interpretation S g t ∧
    gamma interpretation S g' msg.wire = gamma interpretation S g msg.wire ∧
    gamma interpretation S g' msg.mac = gamma interpretation S g msg.mac ∧
    gamma interpretation S g' msg.ratchetKey = gamma interpretation S g msg.ratchetKey ∧
    gamma interpretation S g' msg.ciphertext = gamma interpretation S g msg.ciphertext ∧
    gamma interpretation S g' msg.pqRatchet = gamma interpretation S g msg.pqRatchet ∧
    gamma interpretation S g' st.spqr = gamma interpretation S g st.spqr ∧
    (∀ c ∈ st.recv,
      gamma interpretation S g' c.ratchetKey = gamma interpretation S g c.ratchetKey ∧
      gamma interpretation S g' c.chainKey = gamma interpretation S g c.chainKey) := by
  intro g'
  have htr_lt : FreshSigma.TraceEntriesLt interpretation S g ts (runTraceMoves r₀ ms₁) :=
    FreshSigma.traceEntriesLt_of_reachable interpretation S g ts hmp.2.1.2.2.1.1 hts
  have hat_st : ((runTraceMoves r₀ ms₁).at? stateIdx : Option FreshSigma.StEntry) = some ⟨⟨p, st⟩⟩ :=
    FreshSigma.at?_eq_some_of_getLocalState_some hst
  have hst_lt : FreshSigma.StateStampsLt interpretation S g ts st := FreshSigma.traceEntriesLt_at?_st htr_lt hat_st
  have ht_lt : FreshSigma.StampsLt interpretation S g ts t := FreshSigma.traceEntriesLt_knows htr_lt ht_kn
  have hmsg_lt : FreshSigma.TRSignalMsgStampsLt interpretation S g ts msg := FreshSigma.stampsLt_parseTrSignalMsg ht_lt hparse
  refine ⟨FreshSigma.updateFreshAt_self g.σ ts 32 rngBytes,
    FreshSigma.matchedPrefix_updateFreshAt hmp hts 32 rngBytes,
    pureTRRecordStateInv_updateFreshAt hmp.2.1 hrsi hts 32 rngBytes,
    (FreshSigma.stateRel_updateFreshAt_of_stampsLt interpretation S g ts 32 rngBytes st rec hst_lt).mpr hrel,
    FreshSigma.trKeyShape_updateFreshAt_of_stampsLt hst_lt hks, hst_lt, hmsg_lt,
    FreshSigma.gamma_updateFreshAt_of_stampsLt interpretation S g ts 32 rngBytes t ht_lt,
    FreshSigma.gamma_updateFreshAt_of_stampsLt interpretation S g ts 32 rngBytes msg.wire hmsg_lt.1,
    FreshSigma.gamma_updateFreshAt_of_stampsLt interpretation S g ts 32 rngBytes msg.mac hmsg_lt.2.1,
    FreshSigma.gamma_updateFreshAt_of_stampsLt interpretation S g ts 32 rngBytes msg.ratchetKey hmsg_lt.2.2.1,
    FreshSigma.gamma_updateFreshAt_of_stampsLt interpretation S g ts 32 rngBytes msg.ciphertext hmsg_lt.2.2.2.1,
    FreshSigma.gamma_updateFreshAt_of_stampsLt interpretation S g ts 32 rngBytes msg.pqRatchet hmsg_lt.2.2.2.2,
    FreshSigma.gamma_updateFreshAt_of_stampsLt interpretation S g ts 32 rngBytes st.spqr hst_lt.2.2.2.2.2.1,
    fun c hc =>
      ⟨FreshSigma.gamma_updateFreshAt_of_stampsLt interpretation S g ts 32 rngBytes c.ratchetKey (hst_lt.2.2.2.2.2.2 c hc).1,
       FreshSigma.gamma_updateFreshAt_of_stampsLt interpretation S g ts 32 rngBytes c.chainKey (hst_lt.2.2.2.2.2.2 c hc).2⟩⟩

end Symbolic.Swarm.CREF.CliPure.TR.PureRecvEval
