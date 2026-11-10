/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Symbolic.Proofs.Swarm.CREF.RecvPrekeyProm.HxplG2W.StepBranchOKPure
public import Symbolic.Proofs.Swarm.CREF.RecvPrekeyProm.HxplG2W.VersionPure
import Batteries.Data.UInt
import DY.Trace.Basic
import DY.Trace.Monad
import DY.Trace.Manipulation
import DY.Actions.Network
public import Symbolic.Proofs.Swarm.CREF.Sem
import Symbolic.Proofs.Swarm.CREF.Cli.Rpk.DecCryptoBPure
import Symbolic.Proofs.Swarm.CREF.Cli.Rpk.RecvDecStepCommonPure
import Symbolic.Proofs.Swarm.CREF.Cli.Rpk.RecvDecStepNoRatchetPure
import Symbolic.Proofs.Swarm.CREF.Cli.Rpk.RecvDecStepNoRatchetWAtPure
import Symbolic.Proofs.Swarm.CREF.Cli.Rpk.RecvDecStepSpqrPure
import Symbolic.Proofs.Swarm.CREF.Cli.Rpk.SendRetCoinsCliPure
import Symbolic.Proofs.Swarm.CREF.Cli.Rpk.SendRetCoinsCliPureB
import Symbolic.Proofs.Swarm.CREF.Cli.World.RelCliPure
import Symbolic.Proofs.Swarm.CREF.Initiate.InitRej
import Symbolic.Proofs.Swarm.CREF.ModelBridge
import Symbolic.Proofs.Swarm.CREF.Prelude
import Symbolic.Proofs.Swarm.CREF.RecvPrekeyProm.HxplG2W.BaseKeyFromRBKS
import Symbolic.Proofs.Swarm.CREF.RecvPrekeyProm.HxplRep
import Symbolic.Proofs.Swarm.CREF.TR.RecvDecStepSkippedProvTRHelpers
import Symbolic.Proofs.Swarm.CREF.TR.TrStateRkCkIk
import Symbolic.Proofs.Swarm.CREF.TROpen
import Symbolic.Proofs.Swarm.CREF.TR.RecvCol -- shake: keep
import Symbolic.Proofs.Swarm.CREF.TR.RecvDec -- shake: keep
import Symbolic.Proofs.Swarm.CREF.RecvPrekeyProm.HxplG2W.IfacePure -- shake: keep
import Symbolic.Proofs.Swarm.CREF.RecvPrekeyProm.HxplG2AdapterPure -- shake: keep
import Symbolic.DYBridge.DY.Trace.Basic
import Symbolic.DYBridge.DY.Trace.Monad
import Symbolic.DYBridge.DY.Trace.Manipulation
import Symbolic.DYBridge.DY.Actions.Network

/-!
# Existing-Chain Raw Explanation Branch on Session Promotion

Proves `prom_rawKnBranch_noRatchet`, constructing a `RawDecryptMatched` witness and
`pqSalt.AttackerKnows` for the existing-chain (`PromDecSelNoRatchet`) decrypt branch of an
accepting, non-colliding session-promotion call.
-/

@[expose] public section

cref_hide_foreign_instances
set_option autoImplicit false

namespace Symbolic.Swarm.CREF.CliPure

cref_open
cref_open_tr

open DY DY.Comparse DY.Literal DY.Libsignal
open DY.Libsignal.HwEvents DY.Libsignal.Rust
open DY.Libsignal.HwEvents (MachineEvent)
open CryptoGames CryptoGames.HMAC CryptoGames.HKDF
open CryptoGames.LibsignalSession CryptoGames.LibsignalSessionApi
open CryptoVerification
open CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalProtoCodec
open CryptoProofLib.Refinement (ExternInterpretation)
open DY.Libsignal.Composed DY.Libsignal.Composed.Refinement
open DY.Libsignal.TripleRatchet (RecvChain findRecvChain recvChainFor consumeMessageKey computeMac
  messageVersion)
open DY.Libsignal.TripleRatchet (TRState TRSignalMsg parseTrSignalMsg isCurrentSnapshot trMsgKeys)
open DY.Libsignal.TripleRatchet.Refinement (wireWhisperTag)
open DY.Libsignal.Refinement (sha256CompressFunction aesCbcDecryptSymbol)
open CryptoVerification.E2E.Pqxdh.WireEntries.SymP3 (RecvWireGhost)
open Proofs.libsignal.Hooks2 (cryptoOf')
open Proofs.libsignal.RngG Proofs.libsignal.RngG.R3 Proofs.libsignal.RngG.CliPure.R3
open Swarm.Phase0WholeFunctionBridge (sessionToRecordRec sessionToSessionRec)
open Symbolic.Swarm.CREF.TR.Pure
open Symbolic.Swarm.CREF.CliPure.TR.SendRetCoins (gamma_trMsgKeys_eq_generateKeys stateRel_sessionToRecordRec_extract_TR gamma_computeMac_tr)
open Symbolic.Swarm.CREF.TR Symbolic.Swarm.CREF.CliPure.TR
open Symbolic.Swarm.CREF.TR.RecvDec hiding StEntry TREntry TRRecvAllCollide
open Symbolic.Swarm.CREF.TR.RecvDecStep
open Symbolic.Swarm.CREF.CliPure.TR.RecvDecStep hiding StEntry TREntry
  isCurrentSnapshot_append_non_st at?_eq_none_of_le at?_append_of_lt
open Symbolic.Swarm.CREF.CliPure.TR.RecvDecStepAt
open Symbolic.Swarm.CREF.TR.G1

private theorem promNR_cbadSigmaFrame_refl (g : Ghost) (n : Nat) : CBadSigmaFrame g g n :=
  cBadSigmaFrame_refl g n

private theorem promNR_tag_ne_wireWhisperTag_of_parsePreKeyWire
    {tag : BitVec 8} {body : HwBytes} {pf : PreKeyFields}
    (hpf : parsePreKeyWire (tag :: body) = some pf) :
    tag ≠ wireWhisperTag := by
  rintro rfl
  unfold parsePreKeyWire wireWhisperTag DY.Libsignal.PQXDH.Refinement.wirePrekeyTag at hpf
  simp at hpf

private theorem promNR_tryFrom_serialized_eq {body : HwBytes} {m : SignalMessage}
    (htry : SignalMessage.tryFrom protoSignalCodec body = .ok m) : m.serialized = body := by
  simp only [SignalMessage.tryFrom, bind, Except.bind, Pure.pure, Except.pure, throw, throwThe, MonadExceptOf.throw] at htry
  split at htry; · cases htry
  split at htry; · cases htry
  split at htry; · cases htry
  split at htry <;> try cases htry
  split at htry <;> try cases htry
  split at htry <;> try cases htry
  split at htry <;> try cases htry
  split at htry <;> try cases htry
  rfl

private theorem promNR_visOf_decrypt_noRatchet_true {me : Participant} {stateIdx msgIdx pqIdx : Nat}
    {spqrMsgIdx : UInt32} {tr : ExecTrace} {st : TRState}
    {t seed key pqSalt ptTerm spqr' : DY.Bytes} {msg : TRSignalMsg} {c c' : RecvChain}
    (hst : ((PersistentLocalState.getLocalState me stateIdx : Traceful TRState).run tr).1 = some st)
    (hmsg : tr.getMessageSentAt msgIdx = some t) (hparse : parseTrSignalMsg t = some msg)
    (hver : msg.version = messageVersion) (hfind : findRecvChain st.recv msg.ratchetKey = some c)
    (hcons : consumeMessageKey c msg.counter = some (seed, c'))
    (hspqr : Spqr.spqrRecv st.spqr msg.pqRatchet spqrMsgIdx = some (spqr', key))
    (hpqSalt : ((tr.append (⟨key⟩ : Network.ExecEntryT)).at? pqIdx : Option Network.ExecEntryT) =
      some ⟨pqSalt⟩)
    (hmac_eq : msg.mac = computeMac (trMsgKeys pqSalt seed).macKey st.peerIk st.myIk msg.wire)
    (hdec : DY.SymEnc.symDec (trMsgKeys pqSalt seed).cipherKey (trMsgKeys pqSalt seed).iv
      msg.ciphertext = some ptTerm) :
    (Move.decrypt me stateIdx msgIdx pqIdx spqrMsgIdx true).vis tr =
      [(⟨.recv, [t], .preKeyInner (sessionBaseKeys tr stateIdx), none⟩ : VisEntry),
        trEntry .accept ptTerm] := by
  have hnext := decrypt_next_noRatchet_eq (wrapped := true) hst hmsg hparse hver hfind hcons
    hspqr hpqSalt hmac_eq hdec
  have hpre : receivedPlaintext tr (tr.append (⟨key⟩ : Network.ExecEntryT)) = none := by
    rw [receivedPlaintext_append_of_proj (Nat.le_refl _) _ rfl, receivedPlaintext_self]
  rw [vis_decrypt hnext, decVis_true, hmsg, newRandoms_decNoRatchet,
      receivedPlaintext_decTailTr (by simp only [Symbolic.DYBridge.DY.Trace.append_eq_1, Symbolic.DYBridge.DY.Trace.length_eq_2]; omega) hpre,
      exposures_decNoRatchet]
  rfl

private theorem promNR_rawDecryptMatched_step_decrypt_noRatchet_preKeyInner
    {interpretation : ExternInterpretation} {r₀ : ProtocolSetup} {S : OpaqueSymbolSemantics}
    {g : Ghost} {ms₁ : List Move} {τ : List MachineEvent}
    {me : Participant} {stateIdx msgIdx pqIdx : Nat}
    {spqrMsgIdx : UInt32} {st : TRState} {c c' : RecvChain}
    {t seed key pqSalt ptTerm spqr' : DY.Bytes} {msg : TRSignalMsg}
    {wire outPt : HwBytes} {pf : PreKeyFields}
    (hraw : RawDecryptMatched interpretation r₀ S g ms₁ τ)
    (hcur : isCurrentSnapshot (runTraceMoves r₀ ms₁) stateIdx = true)
    (hst : ((PersistentLocalState.getLocalState me stateIdx : Traceful TRState).run
      (runTraceMoves r₀ ms₁)).1 = some st)
    (hmsg : (runTraceMoves r₀ ms₁).getMessageSentAt msgIdx = some t)
    (hparse : parseTrSignalMsg t = some msg) (hver : msg.version = messageVersion)
    (hfind : findRecvChain st.recv msg.ratchetKey = some c)
    (hcons : consumeMessageKey c msg.counter = some (seed, c'))
    (hspqr : Spqr.spqrRecv st.spqr msg.pqRatchet spqrMsgIdx = some (spqr', key))
    (hpqSalt : (((runTraceMoves r₀ ms₁).append (⟨key⟩ : Network.ExecEntryT)).at? pqIdx :
      Option Network.ExecEntryT) = some ⟨pqSalt⟩)
    (hmac_eq : msg.mac = computeMac (trMsgKeys pqSalt seed).macKey st.peerIk st.myIk msg.wire)
    (hdec : DY.SymEnc.symDec (trMsgKeys pqSalt seed).cipherKey (trMsgKeys pqSalt seed).iv
      msg.ciphertext = some ptTerm)
    (hpf : parsePreKeyWire wire = some pf)
    (hbk : ∃ ek ∈ sessionBaseKeys (runTraceMoves r₀ ms₁) stateIdx,
      pf.baseKey.take 33 = ecKey (gamma interpretation S g ek))
    (ht_gam : gamma interpretation S g t = pf.message)
    (hpt_gam : gamma interpretation S g ptTerm = outPt) :
    RawDecryptMatched interpretation r₀ S g
      (ms₁ ++ [.decrypt me stateIdx msgIdx pqIdx spqrMsgIdx true])
      (τ ++ [.recv wire, .accept outPt]) := by
  obtain ⟨hcompat, hrun, hfor⟩ := hraw
  refine ⟨hcompat, RecvDec.modelRun_snoc_decrypt me stateIdx msgIdx pqIdx spqrMsgIdx true hrun hcur, ?_⟩
  rw [runVis_snoc, promNR_visOf_decrypt_noRatchet_true hst hmsg hparse hver hfind hcons
    hspqr hpqSalt hmac_eq hdec]
  refine RecvDec.forall₂_append hfor (List.Forall₂.cons ?_ (List.Forall₂.cons ?_ List.Forall₂.nil))
  · unfold EventMatchesEntry; dsimp only; exact ⟨rfl, t, pf, rfl, hpf, hbk, ht_gam.symm⟩
  · unfold EventMatchesEntry trEntry trLayout; dsimp only; exact ⟨rfl, by simp only [List.map, hpt_gam]; rfl⟩

private theorem promNR_rawDecryptMatched_decrypt_noRatchet_two_attackerSend_preKeyInner
    {interpretation : ExternInterpretation} {r₀ : ProtocolSetup} {S : OpaqueSymbolSemantics} {who : List Participant}
    {g' : Ghost} {ms₁ : List Move} {acc : List MachineEvent}
    {p : Participant} {stateIdx : Nat} {spqrMsgIdx : UInt32} {st : TRState} {c c' : RecvChain}
    {t seed key pqSalt ptTerm spqr' : DY.Bytes} {msg : TRSignalMsg}
    {wire outPt : HwBytes} {pf : PreKeyFields}
    (hmp : MatchedPrefix interpretation r₀ S who g' ms₁ acc)
    (hpqSalt_kn : pqSalt.AttackerKnows (runTraceMoves r₀ ms₁))
    (ht_kn : t.AttackerKnows (runTraceMoves r₀ ms₁))
    (hcur : isCurrentSnapshot (runTraceMoves r₀ ms₁) stateIdx = true)
    (hst : ((PersistentLocalState.getLocalState p stateIdx : Traceful TRState).run
      (runTraceMoves r₀ ms₁)).1 = some st)
    (hparse : parseTrSignalMsg t = some msg) (hver : msg.version = messageVersion)
    (hfind : findRecvChain st.recv msg.ratchetKey = some c)
    (hcons : consumeMessageKey c msg.counter = some (seed, c'))
    (hspqr : Spqr.spqrRecv st.spqr msg.pqRatchet spqrMsgIdx = some (spqr', key))
    (hmac_eq : msg.mac = computeMac (trMsgKeys pqSalt seed).macKey st.peerIk st.myIk msg.wire)
    (hdec : DY.SymEnc.symDec (trMsgKeys pqSalt seed).cipherKey (trMsgKeys pqSalt seed).iv
      msg.ciphertext = some ptTerm)
    (hpf : parsePreKeyWire wire = some pf)
    (hbk : ∃ ek ∈ sessionBaseKeys (runTraceMoves r₀ (ms₁ ++ [Move.attackerSend pqSalt, Move.attackerSend t])) stateIdx,
      pf.baseKey.take 33 = ecKey (gamma interpretation S g' ek))
    (ht_gam : gamma interpretation S g' t = pf.message)
    (hpt_gam : gamma interpretation S g' ptTerm = outPt) :
    RawDecryptMatched interpretation r₀ S g'
      (ms₁ ++ ([.attackerSend pqSalt, .attackerSend t] ++
        [.decrypt p stateIdx ((runTraceMoves r₀ ms₁).length + 1) (runTraceMoves r₀ ms₁).length spqrMsgIdx true]))
      (acc ++ [.recv wire, .accept outPt]) := by
  let tr₀ := runTraceMoves r₀ ms₁
  let ms_a1 := ms₁ ++ [Move.attackerSend pqSalt]
  let ms_a2 := ms_a1 ++ [Move.attackerSend t]
  have htr_a1 : runTraceMoves r₀ ms_a1 = tr₀.append (⟨pqSalt⟩ : Network.ExecEntryT) := by
    rw [runTrace_snoc]; exact Symbolic.Swarm.CREF.b5_attackerSend_next _ _
  have htr_a2 : runTraceMoves r₀ ms_a2 =
      (tr₀.append (⟨pqSalt⟩ : Network.ExecEntryT)).append (⟨t⟩ : Network.ExecEntryT) := by
    rw [runTrace_snoc, htr_a1]; exact Symbolic.Swarm.CREF.b5_attackerSend_next _ _
  have hmp1 := matchedPrefix_attackerSend hmp hpqSalt_kn
  have ht_kn1 : t.AttackerKnows (runTraceMoves r₀ ms_a1) := by
    rw [htr_a1]; exact DY.Bytes.AttackerKnows_le t tr₀ _ (Trace.append_le tr₀ _) ht_kn
  have hmp2 := matchedPrefix_attackerSend hmp1 ht_kn1
  have hraw2 : RawDecryptMatched interpretation r₀ S g' ms_a2 acc :=
    ⟨hmp2.1, hmp2.2.1, hmp2.2.2.2.2.2⟩
  have hcur2 : isCurrentSnapshot (runTraceMoves r₀ ms_a2) stateIdx = true := by
    rw [htr_a2, RecvDec.isCurrentSnapshot_append_non_st _ _ rfl,
        RecvDec.isCurrentSnapshot_append_non_st _ _ rfl]
    exact hcur
  have hst2 : ((PersistentLocalState.getLocalState p stateIdx : Traceful TRState).run
      (runTraceMoves r₀ ms_a2)).1 = some st := by
    rw [runTrace_snoc, getLocalState_attackerSend, runTrace_snoc, getLocalState_attackerSend]
    exact hst
  have hlen_a1 : (tr₀.append (⟨pqSalt⟩ : Network.ExecEntryT)).length = tr₀.length + 1 := by
    simp only [Symbolic.DYBridge.DY.Trace.append_eq_1, Symbolic.DYBridge.DY.Trace.length_eq_2]
  have hmsg2 : (runTraceMoves r₀ ms_a2).getMessageSentAt (tr₀.length + 1) = some t := by
    rw [runTrace_snoc, htr_a1, ← hlen_a1]; exact getMessageSentAt_attackerSend _ t
  have hpqSalt2 : (((runTraceMoves r₀ ms_a2).append (⟨key⟩ : Network.ExecEntryT)).at? tr₀.length :
      Option Network.ExecEntryT) = some ⟨pqSalt⟩ := by
    rw [htr_a2,
        RecvDec.at?_append_of_lt _ _ (by simp only [Symbolic.DYBridge.DY.Trace.append_eq_1, Symbolic.DYBridge.DY.Trace.length_eq_2]; omega),
        RecvDec.at?_append_of_lt _ _ (by simp only [Symbolic.DYBridge.DY.Trace.append_eq_1, Symbolic.DYBridge.DY.Trace.length_eq_2]; omega)]
    exact Trace.at?_append tr₀ (⟨pqSalt⟩ : Network.ExecEntryT)
  have hms_a2 : ms_a2 = ms₁ ++ [Move.attackerSend pqSalt, Move.attackerSend t] := by
    simp [ms_a2, ms_a1, List.append_assoc]
  have hbk2 : ∃ ek ∈ sessionBaseKeys (runTraceMoves r₀ ms_a2) stateIdx,
      pf.baseKey.take 33 = ecKey (gamma interpretation S g' ek) := by
    rw [hms_a2]; exact hbk
  have hstep := promNR_rawDecryptMatched_step_decrypt_noRatchet_preKeyInner hraw2 hcur2 hst2 hmsg2
    hparse hver hfind hcons hspqr hpqSalt2 hmac_eq hdec hpf hbk2 ht_gam hpt_gam
  have hms_eq : ms_a2 ++ [Move.decrypt p stateIdx (tr₀.length + 1) tr₀.length spqrMsgIdx true] =
      ms₁ ++ ([.attackerSend pqSalt, .attackerSend t] ++
        [.decrypt p stateIdx (tr₀.length + 1) tr₀.length spqrMsgIdx true]) := by
    simp [ms_a2, ms_a1, List.append_assoc]
  rw [← hms_eq]; exact hstep

set_option maxHeartbeats 800000 in
/-- Constructs a `RawDecryptMatched` witness and `pqSalt.AttackerKnows` on the existing-chain
(`PromDecSelNoRatchet`) decrypt branch of an accepting, non-colliding session-promotion call. -/
theorem prom_rawKnBranch_noRatchet
    (interpretation : ExternInterpretation) {r : ProtocolSetup} {S : OpaqueSymbolSemantics}
    {who : List Participant} {ok : Nat → Bool}
    (hext : DY.Libsignal.Composed.Refinement.Cli.ExternContractsHoldCli interpretation)
    (hwf : ProtocolSetupWF r)
    (hSeq : S = compSemOf interpretation r)
    (hVer : PromVersionOK interpretation r S who ok) :
    PromRawKnBranchOK interpretation r S who ok PromDecSelNoRatchet := by
  intro j e' mid acc rec tag body sm pf sess sess' coins expected pt
    hC _hcol hsel g ms t' hc hctx ht' hncol hnors
  have hmp : MatchedPrefix interpretation r S who g ms acc := hc.matched
  have hmp_nil : MatchedPrefix interpretation r S who g ms (acc ++ []) := by
    simpa only [List.append_nil] using hmp
  have hat : RecvAtFacts interpretation r S g ms := hctx.atF
  have hIW : InstallWitnessTR r (runTraceMoves r ms) :=
    installWitnessTR_of_reachable r ms hc.matched.2.1.2.2.1.1
  have hPkD_nil : NoRatchetPkDispatchAt interpretation r S g ms (acc ++ []) := by
    simpa only [List.append_nil] using hctx.pkNR
  have hsent_nil : e'.sent = sentBodies (acc ++ []) := by
    simpa only [List.append_nil] using hC.entry.sent_eq
  have hfit : SrHonestVer.SendsFit acc := hC.entry.ready.2.1.sendsFit
  have hfit_nil : SrHonestVer.SendsFit (acc ++ []) := by
    simpa only [List.append_nil] using hfit
  have hpq : PqFromHonest e'.sent pf.message := hC.entry.pqh pf hC.out.hpf
  have htry : SignalMessage.tryFrom protoSignalCodec pf.message = .ok pf.inner :=
    parsePreKeyWire_inner_tryFrom hC.out.hpf
  have hss : SingleSession rec :=
    let ⟨rr₀, _, hrec_rr₀, hprev₀, _⟩ := hC.entry.pm
    ⟨rr₀, hrec_rr₀, hprev₀⟩
  have hrr := pureCRecRelH_single (hC.entry.ready.2.1.recs hc r.bob rec hC.entry.rec_lookup).2.2 hss
  have hrsi : PureTRRecordStateInv interpretation r S (pureTrSlots r) g ms
      (fun q => if q = r.bob then some rec else none) := by
    rcases hrr with h | ⟨hab, _⟩
    · exact h
    · exact False.elim (hwf.1 hab.symm)
  obtain ⟨_hp_mem, rec₀, st₀, stateIdx₀, hrecBytes₀, hst₀, hcur₀, hrel₀, _hsk_pre₀, _hcanon₀, hks₀, hnd₀⟩ :=
    hrsi r.bob rec (by simp only [↓reduceIte])
  let g_rw : RecvWireGhost :=
    { who := 1, aPtr := 0, meBytes := [], stateBytes := rec, sess := sess,
      wirePtr := 0, wireBytes := wireWhisperTag :: pf.message, cur := 0, rest := [], tlsInit := none }
  have hcanon_q : Symbolic.Swarm.CREF.TR.Pure.slots_RecordCanonical_Q Symbolic.Swarm.CREF.TR.Pure.slots_NonEmptyV1Q rec g_rw.sess := hC.out.hcan_in
  have hnorm_eq :=
    rec_eq_sessionToRecordRec_of_canonical_Q hrecBytes₀ hcanon_q
  have hrc_rec₀ : rec₀.current.receiverChains = (sessionToRecordRec g_rw.sess).current.receiverChains :=
    congrArg (fun r => r.current.receiverChains) hnorm_eq
  have hrel₀_sess : StateRel interpretation S g st₀ (sessionToRecordRec g_rw.sess) := by
    rw [← stateRel_sessionToRecordRecPending_iff, ← stateRel_normPending_iff, ← hnorm_eq, stateRel_normPending_iff]
    exact hrel₀
  have hnd₀_sess : RecordChainsWF3 (sessionToRecordRec g_rw.sess) :=
    ⟨hrc_rec₀ ▸ hnd₀.1, hrc_rec₀ ▸ hnd₀.2.1, hrc_rec₀ ▸ hnd₀.2.2⟩
  have hnodup_rc : (sess.state.receiverChains.map ReceiverChain.senderRatchetKey).Nodup := by
    have hmap : (sessionToRecordRec g_rw.sess).current.receiverChains.map ChainRec.senderRatchetKey =
        (sess.state.receiverChains.map ReceiverChain.senderRatchetKey).map PublicKey.serialize := by
      dsimp only [g_rw, sessionToRecordRec, sessionToSessionRec]; rw [List.map_map, List.map_map]; rfl
    exact List.Nodup.of_map PublicKey.serialize (hmap ▸ hnd₀_sess.1)
  obtain ⟨remIk, ck, ck_adv, ck_next, r_adv, r2, mkGen, newPqrState, pqrKey, _st',
      hmid_nil, _hcoins_zero, hRem, hFind, hNotLt, hJump, hAdv, hNext, hSet, hMkGen,
      hrecv_spqr, hMac, hDec, _hSt', _hsess'_st, _hsm_st⟩ :=
    prom_adapter_noRatchet_out hC.out hnodup_rc hsel
  subst hmid_nil
  obtain ⟨msg₀, hparse₀⟩ := Option.isSome_iff_exists.mp ht'.2.2.1
  have hRkLensAll₀ : RecvRkLensAll interpretation S g r ms := hat.lens
  have hst₀_avail : st₀ ∈ availableStates r (runTraceMoves r ms) :=
    Symbolic.Swarm.CREF.TR.RecvHistStep2.mem_availableStates_of_at? r ms
      (Symbolic.Swarm.CREF.TR.FreshSigma.at?_eq_some_of_getLocalState_some hst₀)
  have hRkLens₀ : ∀ c ∈ st₀.recv, (gamma interpretation S g c.ratchetKey).length = 32 :=
    hRkLensAll₀ st₀ hst₀_avail
  obtain ⟨_hrk_sess, _hcks_sess, _hdhs_sess, hloc_ser, ⟨rem0, hrem0, hrem_ser⟩, _hrc_sess⟩ :=
    stateRel_sessionToRecordRec_extract_TR interpretation S g st₀ g_rw.sess hrel₀_sess
  have hst₀_rci : TrStateRkCkIk r st₀ := trStateRkCkIk_of_getLocalState hmp.2.1 hst₀
  have hCkLens : ∀ c ∈ st₀.recv, (gamma interpretation S g c.chainKey).length = 32 :=
    hst₀_rci.recv_ck_len interpretation S g hwf hmp.1
  have hNodupSym : (st₀.recv.map RecvChain.ratchetKey).Nodup :=
    nodup_ratchetKey_of_stateRel_tr hrel₀_sess hnd₀_sess.1
  have hctr₀ : msg₀.counter = UInt32.ofBitVec pf.inner.counter :=
    UInt32.ext (((ht'.2.2.2 msg₀ hparse₀).2.2.2 pf.inner htry).2.2.2.1)
  obtain ⟨_ci₀, _ch, c, _mks', seed, c', _hch0, hc0, hfind₀, _hsrk0, _htheir, _hck, _hch_ck,
      hcons₀_bv, hSeedEq, hCntEq, _hc'_rk, _hc'_rIdx, _hR2Eq, _hRel_lit, _hMks'⟩ :=
    stateRel_and_consumeMessageKey_of_existing_tr interpretation S g hrel₀_sess hNodupSym hCkLens
      (gamma_litOf interpretation S g newPqrState) hFind hNotLt hJump hAdv hNext hSet
  have hc_mem : c ∈ st₀.recv := List.mem_of_getElem? hc0
  have hcons₀ : consumeMessageKey c msg₀.counter = some (seed, c') := hctr₀ ▸ hcons₀_bv
  have hγ_c_rk : gamma interpretation S g c.ratchetKey = pf.inner.senderRatchetKey.bytes.toList := by
    rw [_htheir]; simp [vec32, hRkLens₀ c hc_mem]
  have hrk_oi : RkKnownOrInit (runTraceMoves r ms) c.ratchetKey :=
    (storedRkKnown_of_modelRun hmp.2.1 st₀ hst₀_avail).ratchetKey hc_mem
  have hrel₀'_rec₀ : StateRel interpretation S g st₀ rec₀ := by
    rw [← stateRel_normPending_iff, hnorm_eq, stateRel_normPending_iff, stateRel_sessionToRecordRecPending_iff]
    exact hrel₀_sess
  obtain ⟨_, _, hpq_sess, _, _, _hver_sess, _⟩ :=
    pqRatchetState_eq_gamma_pending interpretation S g rec rec₀ st₀ st₀ g_rw hrecBytes₀ hrel₀'_rec₀ hcanon_q rfl
  have hver_pf : pf.inner.messageVersion = 4#8 :=
    hVer j e' [] acc rec (tag :: body) sm pf sess sess' coins expected pt hC
  have hver₀_nat : msg₀.version.toNat = pf.inner.messageVersion.toNat :=
    ((ht'.2.2.2 msg₀ hparse₀).2.2.2 pf.inner htry).2.2.2.2
  have hver₀ : msg₀.version = messageVersion :=
    UInt8.ext (by rw [hver₀_nat, hver_pf]; rfl)
  have hseed_c : msg₀.ratchetKey = c.ratchetKey → recvSeed st₀ msg₀ = some seed := by
    intro hrk₀; unfold recvSeed; simp only [hver₀, ↓reduceIte, recvChainFor, hrk₀, hfind₀]
    change Option.map Prod.fst (consumeMessageKey c msg₀.counter) = some seed; rw [hcons₀]; rfl
  let k_own : DY.Bytes := ({ st := st₀.spqr, msg := msg₀.pqRatchet } : DY.Spqr.RecvKey.SubF DY.Bytes).pack
  have hk_own : k_own ∈ ownKeys r (runTraceMoves r ms) st₀ msg₀ := by
    unfold ownKeys; exact List.mem_map_of_mem (List.mem_filter.mpr ⟨hst₀_avail, beq_self_eq_true _⟩)
  have hk_own_gam :=
    (spqrRecv_step_gamma_state_and_key interpretation hext.1
      r S hSeq g ms pf.message st₀ g_rw t' msg₀ pf.inner newPqrState pqrKey hpq_sess ht' hparse₀ htry hrecv_spqr).2
  have hmkGen_eq : mkGen = ⟨gamma interpretation S g seed, pf.inner.counter⟩ := by
    rw [hMkGen]; change ck_adv.messageKeys (sha256CompressFunction interpretation) = _
    rcases h : ck_adv.messageKeys (sha256CompressFunction interpretation) with ⟨sd, ct⟩
    rw [h] at hSeedEq hCntEq; dsimp only at hSeedEq hCntEq; subst hSeedEq hCntEq; rfl
  obtain ⟨hck_mk, hmk_mk, hiv_mk, _⟩ :=
    gamma_trMsgKeys_eq_generateKeys interpretation S g k_own seed pf.inner.counter pqrKey hk_own_gam
  have hDecOk : interpretation aesCbcDecryptSymbol
      [pf.inner.ciphertext, gamma interpretation S g (trMsgKeys k_own seed).cipherKey,
       (gamma interpretation S g (trMsgKeys k_own seed).iv).take 16] = some pt := by
    rw [← hck_mk, ← hiv_mk]
    change (Proofs.libsignal.SR.interpW interpretation).dec
      (MessageKeyGenerator.generateKeys (cryptoOf' interpretation).F
        ⟨gamma interpretation S g seed, pf.inner.counter⟩ pqrKey).cipherKey
      (MessageKeyGenerator.generateKeys (cryptoOf' interpretation).F
        ⟨gamma interpretation S g seed, pf.inner.counter⟩ pqrKey).iv
      pf.inner.ciphertext = some pt
    rw [← hmkGen_eq]; exact hDec
  rw [hRem] at hrem0; injection hrem0 with hrem_eq; subst hrem_eq
  have hpeer_ser : remIk.serialize = gamma interpretation S g st₀.peerIk := hrem_ser.trans hks₀.peerIk_ser
  have hmy_ser : g_rw.sess.state.localIdentity.serialize = gamma interpretation S g st₀.myIk :=
    hloc_ser.trans hks₀.myIk_ser
  have hwire₀_take : gamma interpretation S g msg₀.wire = pf.message.take (pf.message.length - 8) :=
    (ht'.2.2.2 msg₀ hparse₀).1
  have hm_ser : pf.inner.serialized = pf.message := promNR_tryFrom_serialized_eq htry
  have hMacBytes : pf.message.drop (pf.message.length - 8) =
      gamma interpretation S g (computeMac (trMsgKeys k_own seed).macKey st₀.peerIk st₀.myIk msg₀.wire) := by
    have hmac_ver : pf.inner.verifyMac (cryptoOf' interpretation).F remIk g_rw.sess.state.localIdentity
        (mkGen.generateKeys (cryptoOf' interpretation).F pqrKey).macKey = true :=
      ((Proofs.libsignal.RngG.CliPure.DecCrypto.verifyMacWithAddresses_eq_true_iff _ _ _ _ _ _).mp hMac).1
    unfold SignalMessage.verifyMac macLength at hmac_ver; dsimp only at hmac_ver
    have hmac_eq := (beq_iff_eq.mp hmac_ver).symm; rw [hm_ser] at hmac_eq; rw [hmac_eq]
    have hkey_mk : keyToBytes32 ((mkGen.generateKeys (cryptoOf' interpretation).F pqrKey).macKey) =
        gamma interpretation S g (trMsgKeys k_own seed).macKey := by rw [hmkGen_eq]; exact hmk_mk
    exact gamma_computeMac_tr interpretation S g (trMsgKeys k_own seed).macKey st₀.peerIk st₀.myIk msg₀.wire
      remIk g_rw.sess.state.localIdentity ((mkGen.generateKeys (cryptoOf' interpretation).F pqrKey).macKey)
      hkey_mk hpeer_ser hmy_ser (pf.message.take (pf.message.length - 8)) hwire₀_take.symm
  have hik0_kn : (DY.Libsignal.PQXDH.serializedIk (setupPublic r 0)).AttackerKnows (runTraceMoves r ms) :=
    Concat.attacker_knows_concat _ _ _ (Literal.attacker_knows_literalToBytes _ _)
      (Symbolic.Swarm.CREF.CliPure.TR.knows_setupPublic r hwf.1 ms 0 (Or.inl rfl))
  have hik2_kn : (DY.Libsignal.PQXDH.serializedIk (setupPublic r 2)).AttackerKnows (runTraceMoves r ms) :=
    Concat.attacker_knows_concat _ _ _ (Literal.attacker_knows_literalToBytes _ _)
      (Symbolic.Swarm.CREF.CliPure.TR.knows_setupPublic r hwf.1 ms 2 (Or.inr rfl))
  have hPeerK : st₀.peerIk.AttackerKnows (runTraceMoves r ms) := hst₀_rci.peerIk.elim (· ▸ hik0_kn) (· ▸ hik2_kn)
  have hMyK : st₀.myIk.AttackerKnows (runTraceMoves r ms) := hst₀_rci.myIk.elim (· ▸ hik0_kn) (· ▸ hik2_kn)
  have hHist : RecvHistInvTR interpretation S g r ms := hat.hist
  obtain ⟨t₁, msg₁, ht₁_rep, hparse₁, hver₁, hrk₁, hctr₁, hMacBytes₁, hDisj⟩ :=
    hPkD_nil r.bob stateIdx₀ pf.message pt pf.inner st₀ c c' t' seed k_own msg₀ hmp.2.1 hmp.2.1.2.2.1.1
      htry ht' hparse₀ hver₀ hctr₀ hncol hnors.1 hst₀ hc_mem hcons₀ hseed_c hk_own
      hHist hIW hrk_oi hγ_c_rk hMacBytes hPeerK hMyK hDecOk
  obtain ⟨t_m, msg', pqSalt, ptTerm, spqr', key, spqrMsgIdx,
      ht_m_rep, hpqSalt_kn, ht_m_kn, hparse', hver', hrk', hctr',
      hspqr_step, _hspqr'_gam, hmac', hdec', ht_m_gam, hpt_gam⟩ :=
    noRatchet_decryptWitness_of_g1_disj_at interpretation hext.1
      r S hSeq g r.bob stateIdx₀ ms (acc ++ []) e'.sent
      rec pf.message pt rec₀ st₀ g_rw t₁ msg₁ pf.inner c.ratchetKey seed k_own newPqrState pqrKey
      hmp_nil hfit_nil hsent_nil hrecBytes₀ hrel₀'_rec₀ hst₀ hcanon_q hpq htry ht₁_rep hparse₁ hver₁ hrk₁
      hMacBytes₁ hPeerK hMyK hDecOk hrecv_spqr hDisj
  have hctr_eq : msg'.counter = msg₀.counter := hctr'.trans hctr₁
  have hfind' : findRecvChain st₀.recv msg'.ratchetKey = some c := hrk' ▸ hfind₀
  have hcons' : consumeMessageKey c msg'.counter = some (seed, c') := hctr_eq ▸ hcons₀
  have hbk := prom_baseKeyInSession_of_rbks hC.entry.pm hC.out.hpf hC.entry.rec_lookup
    (hC.entry.ready.2.1.bks hc) hc.matched.2.1 hst₀ hcur₀
    (promNR_cbadSigmaFrame_refl g (runTraceMoves r ms).length) pqSalt t_m
  have hmp₁ := promNR_rawDecryptMatched_decrypt_noRatchet_two_attackerSend_preKeyInner
    hmp hpqSalt_kn ht_m_kn hcur₀ hst₀ hparse' hver' hfind' hcons'
    hspqr_step hmac' hdec' hC.out.hpf hbk ht_m_gam hpt_gam
  have hwrap : decide (tag ≠ wireWhisperTag) = true :=
    decide_eq_true (promNR_tag_ne_wireWhisperTag_of_parsePreKeyWire hC.out.hpf)
  refine ⟨g, stateIdx₀, spqrMsgIdx, pqSalt, t_m,
    Move.decrypt r.bob stateIdx₀ ((runTraceMoves r ms).length + 1)
      (runTraceMoves r ms).length spqrMsgIdx (decide (tag ≠ wireWhisperTag)),
    promNR_cbadSigmaFrame_refl g (runTraceMoves r ms).length, ht_m_rep, hpqSalt_kn, hcur₀,
    Or.inl rfl, ?_⟩
  rw [hwrap]
  exact hmp₁

end Symbolic.Swarm.CREF.CliPure
