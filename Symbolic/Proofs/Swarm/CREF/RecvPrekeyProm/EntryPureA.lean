/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Symbolic.Proofs.Swarm.CREF.RecvPrekeyProm.HxplG2W.VersionPure
public import Symbolic.Proofs.Swarm.CREF.RecvPrekeyProm.HxplG2W.SupplyPure
import Batteries.Data.UInt
import DY.ALaCarte.Basic
import DY.Trace.Basic
import DY.Trace.Monad
import DY.Trace.Manipulation
import DY.Trace.BaseAttackerKnowledge
import DY.Actions.Network
import DY.Actions.PersistentLocalState
import DY.Actions.PersistentGlobalState
import DY.Actions.ProtocolEvent
import DY.Actions.Random
public import Symbolic.Proofs.Swarm.CREF.RecvPrekeyProm.HxplG2W.StepBranchOKPure
public import Symbolic.Proofs.Swarm.CREF.Sem
import Symbolic.Proofs.Swarm.CREF.Cli.Rpk.DecCryptoBPure
import Symbolic.Proofs.Swarm.CREF.Cli.Rpk.RecvDecStepCommonPure
import Symbolic.Proofs.Swarm.CREF.Cli.Rpk.RecvDecStepSkippedG1LeavesPure
import Symbolic.Proofs.Swarm.CREF.Cli.Rpk.RecvDecStepSpqrPure
import Symbolic.Proofs.Swarm.CREF.Cli.Rpk.SendRetCoinsCliPure
import Symbolic.Proofs.Swarm.CREF.Cli.Rpk.SendRetCoinsCliPureB
import Symbolic.Proofs.Swarm.CREF.Cli.Rpk.SlotG2ProvBPure
import Symbolic.Proofs.Swarm.CREF.Cli.Rpk.SpinePeelPure
import Symbolic.Proofs.Swarm.CREF.Cli.World.RelCliPure
import Symbolic.Proofs.Swarm.CREF.Initiate.InitRej
import Symbolic.Proofs.Swarm.CREF.ModelBridge
import Symbolic.Proofs.Swarm.CREF.Prelude
import Symbolic.Proofs.Swarm.CREF.RecvPrekeyProm.HxplG2W.BaseKeyFromRBKS
import Symbolic.Proofs.Swarm.CREF.RecvPrekeyProm.HxplG2W.SkippedProvBPure
import Symbolic.Proofs.Swarm.CREF.RecvPrekeyProm.HxplRep
import Symbolic.Proofs.Swarm.CREF.RecvWire.By2SupplyA
import Symbolic.Proofs.Swarm.CREF.TR.G1.LitKeyKnownFinal
import Symbolic.Proofs.Swarm.CREF.TR.Leaks
import Symbolic.Proofs.Swarm.CREF.TR.RecvDecStepSkippedProvTR
import Symbolic.Proofs.Swarm.CREF.TROpen
import Symbolic.Proofs.Swarm.CREF.RecvPrekeyProm.By2Pure -- shake: keep
import Symbolic.DYBridge.DY.ALaCarte.Basic
import Symbolic.DYBridge.DY.Trace.Basic
import Symbolic.DYBridge.DY.Trace.Monad
import Symbolic.DYBridge.DY.Trace.Manipulation
import Symbolic.DYBridge.DY.Trace.BaseAttackerKnowledge
import Symbolic.DYBridge.DY.Actions.Network
import Symbolic.DYBridge.DY.Actions.PersistentLocalState
import Symbolic.DYBridge.DY.Actions.PersistentGlobalState
import Symbolic.DYBridge.DY.Actions.ProtocolEvent
import Symbolic.DYBridge.DY.Actions.Random

/-!
# Context Supply and Skipped-Key Raw Explanation Branch on Session Promotion

Proves `promRawCtxSupply_proved` and `prom_rawKnBranch_skipped`, discharging `PromRawCtxSupply` and
the skipped-key raw explanation branch (`PromRawKnBranchOK ... PromDecSelSkipped`) on an accepting
promote call.
-/

@[expose] public section

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

cref_hide_foreign_instances

namespace Symbolic.Swarm.CREF.CliPure

cref_open
cref_open_tr

open CryptoProofLib.Refinement (ExternInterpretation)
open DY DY.Comparse DY.Literal DY.Libsignal
open DY.Libsignal.TripleRatchet (RecvChain consumeMessageKey chainKeyAt kdfCk kdfRk computeMac
  messageVersion createChain x25519LowOrder)
open DY.Libsignal.TripleRatchet
open DY.Libsignal.PQXDH hiding kdfRk createChain x25519LowOrder
open DY.Libsignal.Composed
open DY.Libsignal.Composed.Refinement
open DY.Libsignal.HwEvents DY.Libsignal.Rust
open CryptoGames CryptoGames.HMAC CryptoGames.HKDF
open CryptoGames.LibsignalSession CryptoGames.LibsignalSessionApi
open CryptoVerification.LibsignalTripleRatchet CryptoVerification.LibsignalProtoCodec
open CryptoVerification.E2E CryptoVerification.E2E.InMem CryptoVerification.E2E.Record
open Symbolic.Swarm.TRREF
open Symbolic.Swarm.CREF.TR.Pure
open Symbolic.Swarm.CREF.TR Symbolic.Swarm.CREF.CliPure.TR
open Symbolic.Swarm.CREF.TR.RecvDec hiding StEntry TREntry TRRecvAllCollide
open Symbolic.Swarm.CREF.TR.RecvDecStep
open Symbolic.Swarm.CREF.CliPure.TR.RecvDecStep hiding StEntry TREntry
open Symbolic.Swarm.CREF.CliPure.TR.RecvDecStepAt
open Symbolic.Swarm.CREF.TR.G1
open DY.Libsignal.TripleRatchet.Refinement (wireWhisperTag)
open DY.Libsignal.Refinement (aesCbcDecryptSymbol)
open CryptoVerification.E2E.Pqxdh.WireEntries.SymP3 (RecvWireGhost)
open Proofs.libsignal.Hooks2 (cryptoOf')
open Proofs.libsignal.SR (interpW)
open Proofs.libsignal.RngG Proofs.libsignal.RngG.R3 Proofs.libsignal.RngG.CliPure.R3
open Swarm.Phase0WholeFunctionBridge (sessionToRecordRec sessionToSessionRec)
open Symbolic.Swarm.CREF.CliPure.TR.SendRetCoins (gamma_trMsgKeys_eq_generateKeys stateRel_sessionToRecordRec_extract_TR gamma_computeMac_tr)

/-! ## Context supply (`PromRawCtxSupply`) -/

theorem promXpl_pkNR_of_cleanBy
    (interpretation : ExternInterpretation) (hext : DY.Libsignal.Composed.Refinement.Cli.ExternContractsHoldCli interpretation) {r : ProtocolSetup} (hwf : ProtocolSetupWF r) {S : OpaqueSymbolSemantics}
    {who : List Participant} {ok : Nat → Bool} :
    PromCtxAt interpretation r S who ok
      (fun g ms acc => NoRatchetPkDispatchAt interpretation r S g ms acc) := by
  intro j e' mid acc rec b sm pf sess sess' coins expected pt hC _hcol g ms hc
  exact rcv_hPkDNR_of_cleanBy hext hwf hc
    (rcv_honestSkelUniq_of_matchedPrefix hc.matched)
    (rcv_abs_of_matchedPrefix hc.matched)

theorem promXpl_pkSk_of_cleanBy
    (interpretation : ExternInterpretation) (hext : DY.Libsignal.Composed.Refinement.Cli.ExternContractsHoldCli interpretation) {r : ProtocolSetup} (hwf : ProtocolSetupWF r) {S : OpaqueSymbolSemantics}
    {who : List Participant} {ok : Nat → Bool} :
    PromCtxAt interpretation r S who ok
      (fun g ms acc => SkippedPkDispatchAtK interpretation r S g ms acc) := by
  intro j e' mid acc rec b sm pf sess sess' coins expected pt hC _hcol g ms hc
  have hch := prom_cHist_at_clean hC hc
  have hreach : (runTraceMoves r ms).Reachable Composed.reachability := hc.matched.2.1.2.2.1.1
  have hNJ : RcvSkippedNotJunkSeedProvAt interpretation r S g ms :=
    rcv_skippedNotJunkSeedProvAt_of_notLowAll hreach hch.2.1
  have hRes : RcvByteChainReselectAt interpretation r S g ms acc :=
    rcv_byteChainReselectAt_of_c16 interpretation r S g ms acc
  have hAliasB : SkippedFreshAliasExclB interpretation r S g ms acc :=
    skippedFreshAliasExclB_of_reach interpretation hreach
  exact skipped_pk_dispatch_atK' hext hwf hc hNJ hRes hch.2.2.1 hAliasB

/-- Supplies `PromRawCtxSupply` on the promote-accept branch. -/
theorem promRawCtxSupply_proved
    (interpretation : ExternInterpretation) {r : ProtocolSetup} {S : OpaqueSymbolSemantics}
    {who : List Participant} {ok : Nat → Bool}
    (hext : DY.Libsignal.Composed.Refinement.Cli.ExternContractsHoldCli interpretation)
    (hwf : ProtocolSetupWF r) :
    PromRawCtxSupply interpretation r S who ok :=
  promRawCtxSupply_of
    (fun _j _e' _mid _acc _rec _b _sm _pf _sess _sess' _coins _expected _pt _hC _hcol _g _ms hc =>
      trRecvFreshAll_of_matchedPrefix interpretation hc.matched)
    (promXpl_pkNR_of_cleanBy interpretation hext hwf)
    (promXpl_pkSk_of_cleanBy interpretation hext hwf)

/-! ## Skipped-key raw explanation branch -/

private theorem promSk_tag_ne_wireWhisperTag_of_parsePreKeyWire
    {tag : BitVec 8} {body : HwBytes} {pf : PreKeyFields}
    (hpf : parsePreKeyWire (tag :: body) = some pf) :
    tag ≠ wireWhisperTag := by
  rintro rfl
  unfold parsePreKeyWire wireWhisperTag DY.Libsignal.PQXDH.Refinement.wirePrekeyTag at hpf
  simp at hpf

private theorem promSk_tryFrom_serialized_eq {body : HwBytes} {m : SignalMessage}
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

private theorem promSk_visOf_decryptSkipped_true {me : Participant}
    {stateIdx msgIdx skIdx pqIdx rIdx srcIdx : Nat}
    {spqrMsgIdx : UInt32} {tr : ExecTrace} {st : TRState}
    {t seed key pqSalt ptTerm spqr' : DY.Bytes} {msg : TRSignalMsg}
    (hst : ((PersistentLocalState.getLocalState me stateIdx : Traceful TRState).run tr).1 = some st)
    (hmsg : tr.getMessageSentAt msgIdx = some t) (hparse : parseTrSignalMsg t = some msg)
    (hver : msg.version = messageVersion)
    (hsk : (tr.at? skIdx : Option RecvDec.TREntry) =
      some ⟨TREvent.SkippedKeyStored (st.sessionInfo me) msg.ratchetKey msg.counter seed rIdx srcIdx⟩)
    (hunused : skippedKeyUsedB tr skIdx = false)
    (hspqr : Spqr.spqrRecv st.spqr msg.pqRatchet spqrMsgIdx = some (spqr', key))
    (hpqSalt : ((tr.append (⟨key⟩ : Network.ExecEntryT)).at? pqIdx : Option Network.ExecEntryT) = some ⟨pqSalt⟩)
    (hmac_eq : msg.mac = computeMac (trMsgKeys pqSalt seed).macKey st.peerIk st.myIk msg.wire)
    (hdec : DY.SymEnc.symDec (trMsgKeys pqSalt seed).cipherKey (trMsgKeys pqSalt seed).iv msg.ciphertext = some ptTerm)
    (hfind : (findRecvChain st.toDRState.recv msg.ratchetKey).isSome = true) :
    (Move.decryptSkipped me stateIdx msgIdx skIdx pqIdx spqrMsgIdx true).vis tr =
      [(⟨.recv, [t], .preKeyInner (sessionBaseKeys tr stateIdx), none⟩ : VisEntry),
        trEntry .accept ptTerm] := by
  have hnext := decryptSkipped_next_eq (wrapped := true) hst hmsg hparse hver hsk hunused hspqr hpqSalt hmac_eq hdec hfind
  rw [vis_decryptSkipped hnext, decVis_true, hmsg, newRandoms_decSkippedTr,
      receivedPlaintext_decSkippedTr, exposures_decSkippedTr]
  rfl

private theorem promSk_rawDecryptMatched_step_decryptSkipped_true
    {interpretation : ExternInterpretation} {r₀ : ProtocolSetup} {S : OpaqueSymbolSemantics}
    {g : Ghost} {ms₁ : List Move} {τ : List MachineEvent}
    {me : Participant} {stateIdx msgIdx skIdx pqIdx rIdx srcIdx : Nat}
    {spqrMsgIdx : UInt32} {st : TRState}
    {t seed key pqSalt ptTerm spqr' : DY.Bytes} {msg : TRSignalMsg}
    {b outPt : HwBytes} {pf : PreKeyFields}
    (hraw : RawDecryptMatched interpretation r₀ S g ms₁ τ)
    (hcur : isCurrentSnapshot (runTraceMoves r₀ ms₁) stateIdx = true)
    (hst : ((PersistentLocalState.getLocalState me stateIdx : Traceful TRState).run
      (runTraceMoves r₀ ms₁)).1 = some st)
    (hmsg : (runTraceMoves r₀ ms₁).getMessageSentAt msgIdx = some t)
    (hparse : parseTrSignalMsg t = some msg) (hver : msg.version = messageVersion)
    (hsk : ((runTraceMoves r₀ ms₁).at? skIdx : Option RecvDec.TREntry) =
      some ⟨TREvent.SkippedKeyStored (st.sessionInfo me) msg.ratchetKey msg.counter seed rIdx srcIdx⟩)
    (hunused : skippedKeyUsedB (runTraceMoves r₀ ms₁) skIdx = false)
    (hspqr : Spqr.spqrRecv st.spqr msg.pqRatchet spqrMsgIdx = some (spqr', key))
    (hpqSalt : (((runTraceMoves r₀ ms₁).append (⟨key⟩ : Network.ExecEntryT)).at? pqIdx :
      Option Network.ExecEntryT) = some ⟨pqSalt⟩)
    (hmac_eq : msg.mac = computeMac (trMsgKeys pqSalt seed).macKey st.peerIk st.myIk msg.wire)
    (hdec : DY.SymEnc.symDec (trMsgKeys pqSalt seed).cipherKey (trMsgKeys pqSalt seed).iv
      msg.ciphertext = some ptTerm)
    (hpf : parsePreKeyWire b = some pf)
    (hbk : ∃ ek ∈ sessionBaseKeys (runTraceMoves r₀ ms₁) stateIdx,
      pf.baseKey.take 33 = ecKey (gamma interpretation S g ek))
    (ht_gam : gamma interpretation S g t = pf.message)
    (hpt_gam : gamma interpretation S g ptTerm = outPt)
    (hfind : (findRecvChain st.toDRState.recv msg.ratchetKey).isSome = true) :
    RawDecryptMatched interpretation r₀ S g
      (ms₁ ++ [.decryptSkipped me stateIdx msgIdx skIdx pqIdx spqrMsgIdx true])
      (τ ++ [.recv b, .accept outPt]) := by
  obtain ⟨hcompat, hrun, hfor⟩ := hraw
  refine ⟨hcompat, modelRun_snoc_decryptSkipped me stateIdx msgIdx skIdx pqIdx spqrMsgIdx true hrun hcur, ?_⟩
  rw [runVis_snoc, promSk_visOf_decryptSkipped_true hst hmsg hparse hver hsk hunused hspqr hpqSalt hmac_eq hdec hfind]
  refine TR.forall₂_append hfor (List.Forall₂.cons ?_ (List.Forall₂.cons ?_ List.Forall₂.nil))
  · unfold DY.Libsignal.Composed.Refinement.EventMatchesEntry
    dsimp only; exact ⟨rfl, t, pf, rfl, hpf, hbk, ht_gam.symm⟩
  · unfold DY.Libsignal.Composed.Refinement.EventMatchesEntry trEntry trLayout
    dsimp only; exact ⟨rfl, by simp only [List.map, hpt_gam]; rfl⟩

private theorem promSk_rawDecryptMatched_decryptSkipped_two_attackerSend_true
    {interpretation : ExternInterpretation} {r₀ : ProtocolSetup} {S : OpaqueSymbolSemantics} {who : List Participant}
    {g : Ghost} {ms₁ : List Move} {acc : List MachineEvent}
    {p : Participant} {stateIdx skIdx rIdx srcIdx : Nat} {spqrMsgIdx : UInt32} {st : TRState}
    {t seed key pqSalt ptTerm spqr' : DY.Bytes} {msg : TRSignalMsg}
    {wire outPt : HwBytes} {pf : PreKeyFields}
    (hmp : MatchedPrefix interpretation r₀ S who g ms₁ acc)
    (hpqSalt_kn : pqSalt.AttackerKnows (runTraceMoves r₀ ms₁))
    (ht_kn : t.AttackerKnows (runTraceMoves r₀ ms₁))
    (hcur : isCurrentSnapshot (runTraceMoves r₀ ms₁) stateIdx = true)
    (hst : ((PersistentLocalState.getLocalState p stateIdx : Traceful TRState).run
      (runTraceMoves r₀ ms₁)).1 = some st)
    (hparse : parseTrSignalMsg t = some msg) (hver : msg.version = messageVersion)
    (hsk : ((runTraceMoves r₀ ms₁).at? skIdx : Option RecvDec.TREntry) =
      some ⟨TREvent.SkippedKeyStored (st.sessionInfo p) msg.ratchetKey msg.counter seed rIdx srcIdx⟩)
    (hunused : skippedKeyUsedB (runTraceMoves r₀ ms₁) skIdx = false)
    (hspqr : Spqr.spqrRecv st.spqr msg.pqRatchet spqrMsgIdx = some (spqr', key))
    (hmac_eq : msg.mac = computeMac (trMsgKeys pqSalt seed).macKey st.peerIk st.myIk msg.wire)
    (hdec : DY.SymEnc.symDec (trMsgKeys pqSalt seed).cipherKey (trMsgKeys pqSalt seed).iv
      msg.ciphertext = some ptTerm)
    (hpf : parsePreKeyWire wire = some pf)
    (hbk : ∃ ek ∈ sessionBaseKeys
        (runTraceMoves r₀ (ms₁ ++ [Move.attackerSend pqSalt, Move.attackerSend t])) stateIdx,
      pf.baseKey.take 33 = ecKey (gamma interpretation S g ek))
    (ht_gam : gamma interpretation S g t = pf.message)
    (hpt_gam : gamma interpretation S g ptTerm = outPt)
    (hfind : (findRecvChain st.toDRState.recv msg.ratchetKey).isSome = true) :
    RawDecryptMatched interpretation r₀ S g
      (ms₁ ++ ([.attackerSend pqSalt, .attackerSend t] ++
        [.decryptSkipped p stateIdx ((runTraceMoves r₀ ms₁).length + 1) skIdx (runTraceMoves r₀ ms₁).length spqrMsgIdx true]))
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
    rw [htr_a1]; exact attackerKnows_append_g1 ht_kn
  have hmp2 := matchedPrefix_attackerSend hmp1 ht_kn1
  have hraw2 : RawDecryptMatched interpretation r₀ S g ms_a2 acc :=
    ⟨hmp2.1, hmp2.2.1, hmp2.2.2.2.2.2⟩
  have hcur2 : isCurrentSnapshot (runTraceMoves r₀ ms_a2) stateIdx = true := by
    rw [htr_a2, RecvDec.isCurrentSnapshot_append_non_st _ _ rfl, RecvDec.isCurrentSnapshot_append_non_st _ _ rfl]
    exact hcur
  have hst2 : ((PersistentLocalState.getLocalState p stateIdx : Traceful TRState).run
      (runTraceMoves r₀ ms_a2)).1 = some st := by
    rw [runTrace_snoc, getLocalState_attackerSend, runTrace_snoc, getLocalState_attackerSend]
    exact hst
  have hlen_a1 : (tr₀.append (⟨pqSalt⟩ : Network.ExecEntryT)).length = tr₀.length + 1 := by
    simp only [Symbolic.DYBridge.DY.Trace.append_eq_1, Symbolic.DYBridge.DY.Trace.length_eq_2]
  have hmsg2 : (runTraceMoves r₀ ms_a2).getMessageSentAt (tr₀.length + 1) = some t := by
    rw [runTrace_snoc, htr_a1, ← hlen_a1]; exact getMessageSentAt_attackerSend _ t
  have hsk2 : ((runTraceMoves r₀ ms_a2).at? skIdx : Option RecvDec.TREntry) =
      some ⟨TREvent.SkippedKeyStored (st.sessionInfo p) msg.ratchetKey msg.counter seed rIdx srcIdx⟩ := by
    rw [htr_a2, RecvDec.at?_append_non_entry _ _ rfl, RecvDec.at?_append_non_entry _ _ rfl]
    exact hsk
  have hunused2 : skippedKeyUsedB (runTraceMoves r₀ ms_a2) skIdx = false := by
    rw [htr_a2, skippedKeyUsedB_append_non_tr_a2 _ _ rfl, skippedKeyUsedB_append_non_tr_a2 _ _ rfl]
    exact hunused
  have hpqSalt2 : (((runTraceMoves r₀ ms_a2).append (⟨key⟩ : Network.ExecEntryT)).at? tr₀.length :
      Option Network.ExecEntryT) = some ⟨pqSalt⟩ := by
    rw [htr_a2,
        RecvDec.at?_append_of_lt _ _ (by simp only [Symbolic.DYBridge.DY.Trace.append_eq_1, Symbolic.DYBridge.DY.Trace.length_eq_2]; omega),
        RecvDec.at?_append_of_lt _ _ (by simp only [Symbolic.DYBridge.DY.Trace.append_eq_1, Symbolic.DYBridge.DY.Trace.length_eq_2]; omega)]
    exact Trace.at?_append tr₀ (⟨pqSalt⟩ : Network.ExecEntryT)
  have hms_a2 : ms_a2 = ms₁ ++ [Move.attackerSend pqSalt, Move.attackerSend t] := by
    simp [ms_a2, ms_a1, List.append_assoc]
  have hbk2 : ∃ ek ∈ sessionBaseKeys (runTraceMoves r₀ ms_a2) stateIdx,
      pf.baseKey.take 33 = ecKey (gamma interpretation S g ek) := by
    rw [hms_a2]; exact hbk
  have hstep := promSk_rawDecryptMatched_step_decryptSkipped_true hraw2 hcur2 hst2 hmsg2
    hparse hver hsk2 hunused2 hspqr hpqSalt2 hmac_eq hdec hpf hbk2 ht_gam hpt_gam hfind
  have hms_eq : ms_a2 ++ [Move.decryptSkipped p stateIdx (tr₀.length + 1) skIdx tr₀.length spqrMsgIdx true] =
      ms₁ ++ ([.attackerSend pqSalt, .attackerSend t] ++
        [.decryptSkipped p stateIdx (tr₀.length + 1) skIdx tr₀.length spqrMsgIdx true]) := by
    simp [ms_a2, ms_a1, List.append_assoc]
  rw [← hms_eq]; exact hstep

private theorem skipped_trace_sidecars_and_st_prov_or_bobStart_at
    (interpretation : ExternInterpretation)
    (r₀ : ProtocolSetup) (hwf : ProtocolSetupWF r₀) (S : OpaqueSymbolSemantics) {who : List Participant}
    (p : Participant) (evs acc : List MachineEvent) (g : Ghost) (ms₁ : List Move)
    (st₀ : TRState) (stateIdx₀ : Nat) (g_rw : RecvWireGhost) (m : SignalMessage) (msg₀ : TRSignalMsg)
    (pk seed : DY.Bytes) (rIdx srcIdx skIdx : Nat)
    (hmp : MatchedPrefix interpretation r₀ S who g ms₁ (acc ++ evs))
    (hat : RecvAtFacts interpretation r₀ S g ms₁) (hp_mem : p = r₀.alice ∨ p = r₀.bob)
    (hst₀ : ((PersistentLocalState.getLocalState p stateIdx₀ : Traceful TRState).run (runTraceMoves r₀ ms₁)).1 = some st₀)
    (hcur₀ : isCurrentSnapshot (runTraceMoves r₀ ms₁) stateIdx₀ = true)
    (hsk_pre₀ : ∀ c ∈ (sessionToRecordRec g_rw.sess).current.receiverChains, ∀ k ∈ c.messageKeys, ∃ pk rIdx srcIdx skIdx seed,
      (runTraceMoves r₀ ms₁).EventLoggedAt (TREvent.SkippedKeyStored (st₀.sessionInfo p) pk (UInt32.ofBitVec k.1) seed rIdx srcIdx) skIdx ∧
      (!skippedKeyUsedB (runTraceMoves r₀ ms₁) skIdx) = true ∧ (!receiverKeyUsedB (runTraceMoves r₀ ms₁) (st₀.sessionInfo p) seed (UInt32.ofBitVec k.1) rIdx) = true ∧
      gamma interpretation S g seed = k.2 ∧ c.senderRatchetKey = serializedKey (gamma interpretation S g pk))
    (hlog : (runTraceMoves r₀ ms₁).EventLoggedAt (TREvent.SkippedKeyStored (st₀.sessionInfo p) pk (UInt32.ofBitVec m.counter) seed rIdx srcIdx) skIdx)
    (hctr₀ : msg₀.counter = UInt32.ofBitVec m.counter) :
    (∀ pk_k n_k seed_k srcIdx_k skIdx_k,
      (runTraceMoves r₀ ms₁).EventLoggedAt (TREvent.SkippedKeyStored (st₀.sessionInfo p) pk_k n_k seed_k rIdx srcIdx_k) skIdx_k → pk_k = pk) ∧
    (∀ c_k ∈ (sessionToRecordRec g_rw.sess).current.receiverChains, ∀ k ∈ c_k.messageKeys, ∃ pk_k rIdx_k srcIdx_k skIdx_k seed_k,
      (runTraceMoves r₀ ms₁).EventLoggedAt (TREvent.SkippedKeyStored (st₀.sessionInfo p) pk_k (UInt32.ofBitVec k.1) seed_k rIdx_k srcIdx_k) skIdx_k ∧
      (!skippedKeyUsedB (runTraceMoves r₀ ms₁) skIdx_k) = true ∧ (!receiverKeyUsedB (runTraceMoves r₀ ms₁) (st₀.sessionInfo p) seed_k (UInt32.ofBitVec k.1) rIdx_k) = true ∧
      gamma interpretation S g seed_k = k.2 ∧ c_k.senderRatchetKey = serializedKey (gamma interpretation S g pk_k)) ∧
    TR.G1.RecvHistInvTR interpretation S g r₀ ms₁ ∧ TR.G1.InstallWitnessTR r₀ (runTraceMoves r₀ ms₁) ∧
    (TR.G1.JunkTR pk → ∀ x, pk.view? DY.X25519.Variant.SubF = some x → seed.AttackerKnows (runTraceMoves r₀ ms₁)) ∧
    ∃ (st_prov : TRState) (k_own : DY.Bytes),
      st_prov ∈ availableStates r₀ (runTraceMoves r₀ ms₁) ∧ (st_prov.peerIk = st₀.peerIk ∧ st_prov.myIk = st₀.myIk) ∧
      k_own = ({ st := st₀.spqr, msg := msg₀.pqRatchet } : DY.Spqr.RecvKey.SubF DY.Bytes).pack ∧
      k_own ∈ ownKeys r₀ (runTraceMoves r₀ ms₁) st_prov msg₀ ∧
      st_prov.peerIk.AttackerKnows (runTraceMoves r₀ ms₁) ∧ st_prov.myIk.AttackerKnows (runTraceMoves r₀ ms₁) ∧
      ((∀ msg, msg.version = messageVersion → msg.ratchetKey = pk → msg.counter = msg₀.counter → recvSeed st_prov msg = some seed) ∨
       (∃ (p_src : Participant) (c₀ : RecvChain),
         TR.G1.TRStateStoredAt p_src st_prov srcIdx (runTraceMoves r₀ ms₁) ∧
         st_prov.sessionInfo p_src = st₀.sessionInfo p ∧ st_prov.initiator = false ∧
         c₀ ∈ st_prov.recv ∧ c₀.ratchetKey = pk ∧ c₀.rIdx = rIdx ∧ msg₀.counter < c₀.index)) := by
  have hRun : ModelRun r₀ ms₁ := hmp.2.1
  have hreach : (runTraceMoves r₀ ms₁).Reachable Composed.reachability := hRun.2.2.1.1
  have hRIdxFun : ∀ pk_k n_k seed_k srcIdx_k skIdx_k,
      (runTraceMoves r₀ ms₁).EventLoggedAt (TREvent.SkippedKeyStored (st₀.sessionInfo p) pk_k n_k seed_k rIdx srcIdx_k) skIdx_k → pk_k = pk :=
    fun pk_k n_k seed_k srcIdx_k skIdx_k hlog_k =>
      (hat.fresh p stateIdx₀ st₀ hp_mem hst₀ hcur₀).2.1
        pk_k n_k seed_k srcIdx_k skIdx_k pk (UInt32.ofBitVec m.counter) seed srcIdx skIdx rIdx hlog_k hlog
  have hSeedK_var : TR.G1.JunkTR pk → ∀ x, pk.view? DY.X25519.Variant.SubF = some x → seed.AttackerKnows (runTraceMoves r₀ ms₁) :=
    fun hJunk _ _ => (TR.G1.skippedSeedKnownTR_of_litJunk hreach hlog hJunk).2
  have hIW : TR.G1.InstallWitnessTR r₀ (runTraceMoves r₀ ms₁) := installWitnessTR_of_reachable r₀ ms₁ hreach
  refine ⟨hRIdxFun, hsk_pre₀, hat.hist, hIW, hSeedK_var, ?_⟩
  rcases provEvTR_st_prov_or_bobStart r₀ hwf ms₁ p st₀ stateIdx₀ m msg₀ pk seed rIdx srcIdx skIdx hRun hst₀ hlog hctr₀ with
    ⟨st_prov, k_own, hst_prov, hIkEq, hseed_pk, hk_own_eq, hk_own, hPeerK, hMyK⟩ |
    ⟨p_src, st_src, c₀, k_own, hst_at, hst_avail, hIkEq, hsinfo_eq, hinit_f, hc₀, hc₀_rk, hc₀_rIdx, hlt, hk_own_eq, hk_own, hPeerK, hMyK⟩
  · exact ⟨st_prov, k_own, hst_prov, hIkEq, hk_own_eq, hk_own, hPeerK, hMyK, Or.inl hseed_pk⟩
  · exact ⟨st_src, k_own, hst_avail, hIkEq, hk_own_eq, hk_own, hPeerK, hMyK, Or.inr ⟨p_src, c₀, hst_at, hsinfo_eq, hinit_f, hc₀, hc₀_rk, hc₀_rIdx, hlt⟩⟩

set_option maxHeartbeats 800000 in
/-- Raw explanation step and `pqSalt.AttackerKnows` for the skipped-key (`PromDecSelSkipped`) branch
on session promotion. -/
theorem prom_rawKnBranch_skipped
    (interpretation : ExternInterpretation) {r : ProtocolSetup} {S : OpaqueSymbolSemantics}
    {who : List Participant} {ok : Nat → Bool}
    (hext : DY.Libsignal.Composed.Refinement.Cli.ExternContractsHoldCli interpretation)
    (hwf : ProtocolSetupWF r)
    (hSeq : S = compSemOf interpretation r)
    (hVer : PromVersionOK interpretation r S who ok) :
    PromRawKnBranchOK interpretation r S who ok PromDecSelSkipped := by
  intro j e' mid acc rec tag body sm pf sess sess' coins expected pt
    hC _hcol hsel g ms t' hc hctx ht' hncol hnors
  have hmp : MatchedPrefix interpretation r S who g ms acc := hc.matched
  have hmp_nil : MatchedPrefix interpretation r S who g ms (acc ++ []) := by
    simpa only [List.append_nil] using hmp
  have hat : RecvAtFacts interpretation r S g ms := hctx.atF
  have hPkD_nil : SkippedPkDispatchAtK interpretation r S g ms (acc ++ []) := by
    simpa only [List.append_nil] using hctx.pkSk
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
  obtain ⟨hp_mem, rec₀, st₀, stateIdx₀, hrecBytes₀, hst₀, hcur₀, hrel₀, hsk_pre₀, _hcanon₀, hks₀, hnd₀⟩ :=
    hrsi r.bob rec (by simp only [↓reduceIte])
  let g_rw : RecvWireGhost :=
    { who := 1, aPtr := 0, meBytes := [], stateBytes := rec, sess := sess,
      wirePtr := 0, wireBytes := wireWhisperTag :: pf.message, cur := 0, rest := [], tlsInit := none }
  have hcanon_q : Symbolic.Swarm.CREF.TR.Pure.slots_RecordCanonical_Q Symbolic.Swarm.CREF.TR.Pure.slots_NonEmptyV1Q rec g_rw.sess := hC.out.hcan_in
  obtain ⟨hnorm_eq, hrel₀_sess, hpq_sess, _, _, _hver_sess, _⟩ :=
    pqRatchetState_eq_gamma_pending interpretation S g rec rec₀ st₀ st₀ g_rw hrecBytes₀ hrel₀ hcanon_q rfl
  have hrc_rec₀ : rec₀.current.receiverChains = (sessionToRecordRec g_rw.sess).current.receiverChains :=
    congrArg (fun r => r.current.receiverChains) hnorm_eq
  have hnd₀_sess : RecordChainsWF3 (sessionToRecordRec g_rw.sess) :=
    ⟨hrc_rec₀ ▸ hnd₀.1, hrc_rec₀ ▸ hnd₀.2.1, hrc_rec₀ ▸ hnd₀.2.2⟩
  have hnodup_rc : (sess.state.receiverChains.map ReceiverChain.senderRatchetKey).Nodup := by
    have hmap : (sessionToRecordRec g_rw.sess).current.receiverChains.map ChainRec.senderRatchetKey =
        (sess.state.receiverChains.map ReceiverChain.senderRatchetKey).map PublicKey.serialize := by
      dsimp only [g_rw, sessionToRecordRec, sessionToSessionRec]; rw [List.map_map, List.map_map]; rfl
    exact List.Nodup.of_map PublicKey.serialize (hmap ▸ hnd₀_sess.1)
  have hsk_pre₀' : ∀ c ∈ (sessionToRecordRec g_rw.sess).current.receiverChains,
      ∀ k ∈ c.messageKeys, ∃ pk rIdx srcIdx skIdx seed,
        (runTraceMoves r ms).EventLoggedAt
          (TREvent.SkippedKeyStored (st₀.sessionInfo r.bob) pk (UInt32.ofBitVec k.1) seed rIdx srcIdx) skIdx ∧
        (!skippedKeyUsedB (runTraceMoves r ms) skIdx) = true ∧
        (!receiverKeyUsedB (runTraceMoves r ms) (st₀.sessionInfo r.bob) seed (UInt32.ofBitVec k.1) rIdx) = true ∧
        gamma interpretation S g seed = k.2 ∧
        c.senderRatchetKey = serializedKey (gamma interpretation S g pk) ∧
        (findRecvChain st₀.toDRState.recv pk).isSome = true := by
    intro c hc_mem
    exact hsk_pre₀ c (hrc_rec₀.symm ▸ hc_mem)
  obtain ⟨remIk, _ck, r2, mkGen, newPqrState, pqrKey, _st',
      hmid_nil, _hcoins_zero, hRem, _hFind, _hLt, hTake,
      hrecv_spqr, hMac, hDec, _hSt', _hsess'_st, _hsm_st⟩ :=
    prom_adapter_skipped_out hC.out hnodup_rc hsel
  subst hmid_nil
  obtain ⟨pk, rIdx, srcIdx, skIdx, seed, hlog, hsk_at, hunused, _hru, hseed_gam, hlink, hfind_pk⟩ :=
    extract_skippedKeyStored_of_takeSkippedKey_g1 interpretation r S g ms rfl hsk_pre₀' hTake
  obtain ⟨msg₀, hparse₀⟩ := Option.isSome_iff_exists.mp ht'.2.2.1
  have hγ_pk : gamma interpretation S g pk = pf.inner.senderRatchetKey.bytes.toList :=
    (List.cons.inj hlink).2
  have hfld₀ := (ht'.2.2.2 msg₀ hparse₀).2.2.2 pf.inner htry
  have hctr₀ : msg₀.counter = UInt32.ofBitVec pf.inner.counter :=
    UInt32.ext hfld₀.2.2.2.1
  have hver_pf : pf.inner.messageVersion = 4#8 :=
    hVer j e' [] acc rec (tag :: body) sm pf sess sess' coins expected pt hC
  have hver₀ : msg₀.version = messageVersion := by
    apply UInt8.ext; rw [hfld₀.2.2.2.2, hver_pf]; rfl
  obtain ⟨_hRIdxFun, _hsk_pre₀'', hHist, hIW, hSeedK_var,
      st_prov, k_own, hst_prov, hIkEq, hk_own_eq, hk_own, hPeerK, hMyK, hseed_or_provB⟩ :=
    skipped_trace_sidecars_and_st_prov_or_bobStart_at interpretation r hwf S
      r.bob [] acc g ms st₀ stateIdx₀ g_rw pf.inner msg₀
      pk seed rIdx srcIdx skIdx hmp_nil hat hp_mem hst₀ hcur₀
      (fun c hc k hk => let ⟨pk, rIdx, srcIdx, skIdx, seed, h1, h2, h3, h4, h5, _⟩ := hsk_pre₀' c hc k hk; ⟨pk, rIdx, srcIdx, skIdx, seed, h1, h2, h3, h4, h5⟩)
      hlog hctr₀
  obtain ⟨_, hk_own_gam⟩ :=
    spqrRecv_step_gamma_state_and_key interpretation hext.1 r S hSeq g ms pf.message st₀ g_rw
      t' msg₀ pf.inner newPqrState pqrKey hpq_sess ht' hparse₀ htry hrecv_spqr
  rw [← hk_own_eq] at hk_own_gam
  obtain ⟨_, _, _, _, _, _, _, _, hmk_ctr, _, _, _⟩ := takeSkippedKey_ok_some_inv hTake
  have hmkGen_eq : mkGen = ⟨gamma interpretation S g seed, pf.inner.counter⟩ := by
    rcases mkGen with ⟨sd, ct⟩; dsimp only at hseed_gam hmk_ctr; subst hseed_gam hmk_ctr; rfl
  obtain ⟨hck_mk, hmk_mk, hiv_mk, _⟩ :=
    gamma_trMsgKeys_eq_generateKeys interpretation S g k_own seed pf.inner.counter pqrKey hk_own_gam
  have hDecOk :
      interpretation aesCbcDecryptSymbol
        [pf.inner.ciphertext, gamma interpretation S g (trMsgKeys k_own seed).cipherKey,
         (gamma interpretation S g (trMsgKeys k_own seed).iv).take 16] = some pt := by
    rw [← hck_mk, ← hiv_mk]
    change (Proofs.libsignal.SR.interpW interpretation).dec
      (MessageKeyGenerator.generateKeys (cryptoOf' interpretation).F ⟨gamma interpretation S g seed, pf.inner.counter⟩ pqrKey).cipherKey
      (MessageKeyGenerator.generateKeys (cryptoOf' interpretation).F ⟨gamma interpretation S g seed, pf.inner.counter⟩ pqrKey).iv pf.inner.ciphertext = some pt
    rw [← hmkGen_eq]; exact hDec
  obtain ⟨_, _, _, hloc_ser, ⟨rem0, hrem0, hrem_ser⟩, _⟩ :=
    stateRel_sessionToRecordRec_extract_TR interpretation S g st₀ g_rw.sess hrel₀_sess
  rw [hRem] at hrem0; injection hrem0 with hrem_eq; subst hrem_eq
  have hpeer_ser : remIk.serialize = gamma interpretation S g st_prov.peerIk := by
    rw [hIkEq.1]; exact hrem_ser.trans hks₀.peerIk_ser
  have hmy_ser : g_rw.sess.state.localIdentity.serialize = gamma interpretation S g st_prov.myIk := by
    rw [hIkEq.2]; exact hloc_ser.trans hks₀.myIk_ser
  have hwire₀_take : gamma interpretation S g msg₀.wire = pf.message.take (pf.message.length - 8) :=
    (ht'.2.2.2 msg₀ hparse₀).1
  have hm_ser : pf.inner.serialized = pf.message := promSk_tryFrom_serialized_eq htry
  have hMacBytes :
      pf.message.drop (pf.message.length - 8) =
        gamma interpretation S g (computeMac (trMsgKeys k_own seed).macKey st_prov.peerIk st_prov.myIk msg₀.wire) := by
    have hmac_ver : pf.inner.verifyMac (cryptoOf' interpretation).F remIk g_rw.sess.state.localIdentity
        (mkGen.generateKeys (cryptoOf' interpretation).F pqrKey).macKey = true :=
      ((Proofs.libsignal.RngG.CliPure.DecCrypto.verifyMacWithAddresses_eq_true_iff _ _ _ _ _ _).mp hMac).1
    unfold SignalMessage.verifyMac macLength at hmac_ver
    dsimp only at hmac_ver
    have hmac_eq := (beq_iff_eq.mp hmac_ver).symm
    rw [hm_ser] at hmac_eq
    rw [hmac_eq]
    have hkey_mk : keyToBytes32 ((mkGen.generateKeys (cryptoOf' interpretation).F pqrKey).macKey) =
        gamma interpretation S g (trMsgKeys k_own seed).macKey := by
      rw [hmkGen_eq]; exact hmk_mk
    exact gamma_computeMac_tr interpretation S g (trMsgKeys k_own seed).macKey
      st_prov.peerIk st_prov.myIk msg₀.wire remIk g_rw.sess.state.localIdentity
      ((mkGen.generateKeys (cryptoOf' interpretation).F pqrKey).macKey)
      hkey_mk hpeer_ser hmy_ser (pf.message.take (pf.message.length - 8)) hwire₀_take.symm
  obtain ⟨t₁, msg₁, ht₁_rep, hparse₁, hver₁, hrk₁, hctr₁, hMacBytes₁, hDisj⟩ :=
    hseed_or_provB.elim
      (fun hseed_pk =>
        hPkD_nil r.bob stateIdx₀ pf.message pt pf.inner st₀ st_prov t' pk seed k_own msg₀ rIdx srcIdx skIdx
          htry ht' hparse₀ hver₀ hctr₀ hncol hnors.1 hst₀ hst_prov hIkEq hseed_pk
          hk_own hk_own_eq hlog hHist hIW hSeedK_var hγ_pk hMacBytes hPeerK hMyK hDecOk)
      (fun ⟨p_src, c₀, hst_at, hsinfo_eq, hinit_f, hc₀, hc₀_rk, hc₀_rIdx, hlt⟩ =>
        slotG2_skipped_provB_dispatch_at hext.1 r.bob p_src pf.message pt pf.inner st₀ st_prov c₀
          t' pk seed k_own msg₀ rIdx srcIdx skIdx hmp_nil hat htry ht' hparse₀ hver₀ hctr₀ hncol
          hst_at hst_prov hsinfo_eq hinit_f hc₀ hc₀_rk hc₀_rIdx hlt hk_own hlog hIW hγ_pk hMacBytes
          hPeerK hMyK hDecOk)
  have hctr₁₀ : msg₁.counter = UInt32.ofBitVec pf.inner.counter := hctr₁.trans hctr₀
  obtain ⟨t_m, msg', pqSalt, ptTerm, spqr', key, spqrMsgIdx,
      ht_m_rep, hpqSalt_kn, ht_m_kn, hparse', hver', hrk', hctr'_msg₁,
      hspqr_step, _hspqr'_gam, hmac', hdec', ht_m_gam, hpt_gam⟩ :=
    decryptWitness_of_g1_disj_at interpretation hext.1 r S hSeq g r.bob stateIdx₀ ms (acc ++ []) e'.sent
      rec pf.message pt rec₀ st₀ st₀ st_prov g_rw
      t₁ msg₁ pf.inner pk seed k_own newPqrState pqrKey
      hmp_nil hfit_nil hsent_nil hrecBytes₀ hrel₀ rfl hst₀ hcanon_q
      hpq htry
      ht₁_rep hparse₁ hver₁ hrk₁ hIkEq hk_own_gam hMacBytes₁ hPeerK hMyK hDecOk hrecv_spqr hDisj
  have hctr' : msg'.counter = UInt32.ofBitVec pf.inner.counter := hctr'_msg₁.trans hctr₁₀
  have hsk_at' : ((runTraceMoves r ms).at? skIdx : Option RecvDec.TREntry) =
      some ⟨TREvent.SkippedKeyStored (st₀.sessionInfo r.bob) msg'.ratchetKey msg'.counter seed rIdx srcIdx⟩ := by
    rw [hrk', hctr']; exact hsk_at
  have hbk := prom_baseKeyInSession_of_rbks hC.entry.pm hC.out.hpf hC.entry.rec_lookup
    (hC.entry.ready.2.1.bks hc) hc.matched.2.1 hst₀ hcur₀
    ⟨fun _ _ _ => rfl, rfl⟩ pqSalt t_m
  have hmp₁ := promSk_rawDecryptMatched_decryptSkipped_two_attackerSend_true
    hmp hpqSalt_kn ht_m_kn hcur₀ hst₀ hparse' hver' hsk_at' hunused
    hspqr_step hmac' hdec' hC.out.hpf hbk ht_m_gam hpt_gam (by rw [hrk']; exact hfind_pk)
  have hwrap : decide (tag ≠ wireWhisperTag) = true :=
    decide_eq_true (promSk_tag_ne_wireWhisperTag_of_parsePreKeyWire hC.out.hpf)
  refine ⟨g, stateIdx₀, spqrMsgIdx, pqSalt, t_m,
    Move.decryptSkipped r.bob stateIdx₀ ((runTraceMoves r ms).length + 1) skIdx
      (runTraceMoves r ms).length spqrMsgIdx (decide (tag ≠ wireWhisperTag)),
    ⟨fun _ _ _ => rfl, rfl⟩, ht_m_rep, hpqSalt_kn, hcur₀,
    Or.inr ⟨skIdx, rfl⟩, ?_⟩
  rw [hwrap]
  simpa using hmp₁

end Symbolic.Swarm.CREF.CliPure
