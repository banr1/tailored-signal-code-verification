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
import Symbolic.Proofs.Swarm.CREF.Cli.Rpk.RatchetDHRkSwapStepTRPure
import Symbolic.Proofs.Swarm.CREF.Cli.Rpk.RatchetDHRkSwapStepTRPureA
import Symbolic.Proofs.Swarm.CREF.Cli.Rpk.RecvDecStepRatchetDHAtPure
import Symbolic.Proofs.Swarm.CREF.Cli.Rpk.RecvDecStepRatchetDHaPure
import Symbolic.Proofs.Swarm.CREF.Cli.Rpk.RecvDecStepRatchetDHaPureA
import Symbolic.Proofs.Swarm.CREF.Cli.Rpk.RecvDecStepSpqrPure
import Symbolic.Proofs.Swarm.CREF.Cli.Rpk.SendRetCoinsCliPure
import Symbolic.Proofs.Swarm.CREF.Cli.World.RelCliPure
import Symbolic.Proofs.Swarm.CREF.Initiate.InitRej
import Symbolic.Proofs.Swarm.CREF.ModelBridge
import Symbolic.Proofs.Swarm.CREF.Prelude
import Symbolic.Proofs.Swarm.CREF.RecvPrekeyProm.HxplG2W.BaseKeyFromRBKS
import Symbolic.Proofs.Swarm.CREF.RecvPrekeyProm.HxplRep
import Symbolic.Proofs.Swarm.CREF.TR.TrStateRkCkIk
import Symbolic.Proofs.Swarm.CREF.TROpen
import Symbolic.Proofs.Swarm.CREF.TR.RecvCol -- shake: keep
import Symbolic.Proofs.Swarm.CREF.TR.RecvDec -- shake: keep
import Symbolic.Proofs.Swarm.CREF.RecvPrekeyProm.HxplG2W.IfacePure -- shake: keep
import Symbolic.Proofs.Swarm.CREF.RecvPrekeyProm.HxplG2AdapterPure -- shake: keep
import Symbolic.DYBridge.DY.Trace.Basic
import Symbolic.DYBridge.DY.Trace.Manipulation
import Symbolic.DYBridge.DY.Actions.Network

/-!
# `RawDecryptMatched` Witness for Promote `RatchetDH`

Proves `prom_rawKnBranch_ratchetDH`, constructing the `RawDecryptMatched` witness and
attacker-known `pqSalt` for the DH-ratchet decrypt branch (`PromDecSelRatchetDH`) of a
`.preKey` promote call.
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
open DY.Libsignal.TripleRatchet (RecvChain findRecvChain recvChainFor consumeMessageKey
  maxForwardJumps computeMac messageVersion x25519LowOrder)
open DY.Libsignal.TripleRatchet (TRState TRSignalMsg parseTrSignalMsg isCurrentSnapshot trMsgKeys)
open DY.Libsignal.TripleRatchet.Refinement (wireWhisperTag)
open DY.Libsignal.Refinement (sha256CompressFunction aesCbcDecryptSymbol)
open CryptoVerification.E2E.Pqxdh.WireEntries.SymP3 (RecvWireGhost)
open Proofs.libsignal.Hooks2 (cryptoOf')
open Proofs.libsignal.RngG Proofs.libsignal.RngG.R3 Proofs.libsignal.RngG.CliPure.R3
open Swarm.Phase0WholeFunctionBridge (sessionToRecordRec)
open Symbolic.Swarm.CREF.TR.Pure
open Symbolic.Swarm.TRREF.SpqrSemOf (saltToBytes)
open Symbolic.Swarm.CREF.CliPure.TR.SendRetCoins (gamma_trMsgKeys_eq_generateKeys stateRel_sessionToRecordRec_extract_TR gamma_computeMac_tr)
open Symbolic.Swarm.CREF.TR Symbolic.Swarm.CREF.CliPure.TR
open Symbolic.Swarm.CREF.TR.RecvDec hiding StEntry TREntry TRRecvAllCollide
open Symbolic.Swarm.CREF.TR.RecvDecStep
open Symbolic.Swarm.CREF.CliPure.TR.RecvDecStep hiding StEntry TREntry
  isCurrentSnapshot_append_non_st at?_eq_none_of_le at?_append_of_lt
open Symbolic.Swarm.CREF.CliPure.TR.RecvDecStepAt
open Symbolic.Swarm.CREF.TR.FreshSigma hiding TREntry StEntry
open Symbolic.Swarm.CREF.TR.G1 Symbolic.Swarm.CREF.CliPure.TR.G1

private theorem promDH_tag_ne_wireWhisperTag_of_parsePreKeyWire
    {tag : BitVec 8} {body : HwBytes} {pf : PreKeyFields}
    (hpf : parsePreKeyWire (tag :: body) = some pf) :
    tag ≠ wireWhisperTag := by
  rintro rfl
  unfold parsePreKeyWire wireWhisperTag DY.Libsignal.PQXDH.Refinement.wirePrekeyTag at hpf
  simp at hpf

private theorem promDH_tryFrom_serialized_eq {body : HwBytes} {m : SignalMessage}
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

private theorem promDH_gamma_randTerm32_eq
    (interpretation : ExternInterpretation) (S : OpaqueSymbolSemantics) (g : Ghost) (idx : Nat) :
    gamma interpretation S g (randTerm idx 32) = g.σ idx 32 := by
  unfold gamma gamma' randTerm
  rw [DY.Bytes.rec_eq (concretizeRandom g) (concretizeAll interpretation S g)]; rfl

private theorem promDH_visOf_decrypt_ratchet_true {me : Participant}
    {stateIdx msgIdx pqIdx : Nat} {spqrMsgIdx : UInt32} {tr : ExecTrace} {st : TRState}
    {t seed key pqSalt ptTerm spqr' : DY.Bytes} {msg : TRSignalMsg} {c' : RecvChain}
    (hst : ((PersistentLocalState.getLocalState me stateIdx : Traceful TRState).run tr).1 = some st)
    (hmsg : tr.getMessageSentAt msgIdx = some t)
    (hparse : parseTrSignalMsg t = some msg)
    (hver : msg.version = messageVersion)
    (hfind : findRecvChain st.recv msg.ratchetKey = none)
    (hlow : x25519LowOrder msg.ratchetKey = false)
    (hcons : consumeMessageKey (trDhRatchetState st msg.ratchetKey tr.length).2 msg.counter = some (seed, c'))
    (hspqr : Spqr.spqrRecv (trDhRatchetState st msg.ratchetKey tr.length).1.spqr msg.pqRatchet spqrMsgIdx = some (spqr', key))
    (hpqSalt : (((tr.append (⟨32⟩ : DY.Random.ExecEntryT)).append
      (⟨key⟩ : Network.ExecEntryT)).at? pqIdx : Option Network.ExecEntryT) = some ⟨pqSalt⟩)
    (hmac_eq : msg.mac = computeMac (trMsgKeys pqSalt seed).macKey
      (trDhRatchetState st msg.ratchetKey tr.length).1.peerIk
      (trDhRatchetState st msg.ratchetKey tr.length).1.myIk msg.wire)
    (hdec : DY.SymEnc.symDec (trMsgKeys pqSalt seed).cipherKey (trMsgKeys pqSalt seed).iv msg.ciphertext = some ptTerm) :
    (Move.decrypt me stateIdx msgIdx pqIdx spqrMsgIdx true).vis tr =
      [(⟨.recv, [t], .preKeyInner (sessionBaseKeys tr stateIdx), none⟩ : VisEntry),
       trEntry .rng (randTerm tr.length 32),
       trEntry .accept ptTerm] := by
  have hnext := decrypt_next_ratchet_eq (wrapped := true)
    hst hmsg hparse hver hfind hlow hcons hspqr hpqSalt hmac_eq hdec
  dsimp only at hnext
  rw [vis_decrypt hnext, decVis_true, hmsg, newRandoms_decRatchet,
      receivedPlaintext_decTailTr (by rw [decRatchetPreTr_length]; omega) (receivedPlaintext_decRatchetPreTr ..),
      exposures_decRatchet]
  rfl

private theorem promDH_rawDecryptMatched_step_decrypt_ratchet_preKeyInner
    {interpretation : ExternInterpretation} {r₀ : ProtocolSetup} {S : OpaqueSymbolSemantics}
    {g : Ghost} {ms₁ : List Move} {τ : List MachineEvent}
    {p : Participant} {stateIdx msgIdx pqIdx : Nat} {spqrMsgIdx : UInt32} {st : TRState}
    {t seed key pqSalt ptTerm spqr' : DY.Bytes} {msg : TRSignalMsg} {c' : RecvChain}
    {b rngBytes outPt : HwBytes} {pf : PreKeyFields}
    (hraw : RawDecryptMatched interpretation r₀ S g ms₁ τ)
    (hcur : isCurrentSnapshot (runTraceMoves r₀ ms₁) stateIdx = true)
    (hst : ((PersistentLocalState.getLocalState p stateIdx : Traceful TRState).run (runTraceMoves r₀ ms₁)).1 = some st)
    (hmsg : (runTraceMoves r₀ ms₁).getMessageSentAt msgIdx = some t)
    (hparse : parseTrSignalMsg t = some msg)
    (hver : msg.version = messageVersion)
    (hfind : findRecvChain st.recv msg.ratchetKey = none)
    (hlow : x25519LowOrder msg.ratchetKey = false)
    (hcons : consumeMessageKey (trDhRatchetState st msg.ratchetKey (runTraceMoves r₀ ms₁).length).2 msg.counter = some (seed, c'))
    (hspqr : Spqr.spqrRecv (trDhRatchetState st msg.ratchetKey (runTraceMoves r₀ ms₁).length).1.spqr msg.pqRatchet spqrMsgIdx = some (spqr', key))
    (hpqSalt : ((((runTraceMoves r₀ ms₁).append (⟨32⟩ : DY.Random.ExecEntryT)).append
      (⟨key⟩ : Network.ExecEntryT)).at? pqIdx : Option Network.ExecEntryT) = some ⟨pqSalt⟩)
    (hmac_eq : msg.mac = computeMac (trMsgKeys pqSalt seed).macKey
      (trDhRatchetState st msg.ratchetKey (runTraceMoves r₀ ms₁).length).1.peerIk
      (trDhRatchetState st msg.ratchetKey (runTraceMoves r₀ ms₁).length).1.myIk msg.wire)
    (hdec : DY.SymEnc.symDec (trMsgKeys pqSalt seed).cipherKey (trMsgKeys pqSalt seed).iv msg.ciphertext = some ptTerm)
    (hpf : parsePreKeyWire b = some pf)
    (hbk : ∃ ek ∈ sessionBaseKeys (runTraceMoves r₀ ms₁) stateIdx,
      pf.baseKey.take 33 = ecKey (gamma interpretation S g ek))
    (ht_gam : gamma interpretation S g t = pf.message)
    (hrng_gam : gamma interpretation S g (randTerm (runTraceMoves r₀ ms₁).length 32) = rngBytes)
    (hpt_gam : gamma interpretation S g ptTerm = outPt) :
    RawDecryptMatched interpretation r₀ S g
      (ms₁ ++ [Move.decrypt p stateIdx msgIdx pqIdx spqrMsgIdx true])
      (τ ++ [.recv b, .rng rngBytes, .accept outPt]) := by
  obtain ⟨hcompat, hrun, hfor⟩ := hraw
  refine ⟨hcompat, RecvDec.modelRun_snoc_decrypt p stateIdx msgIdx pqIdx spqrMsgIdx true hrun hcur, ?_⟩
  rw [runVis_snoc, promDH_visOf_decrypt_ratchet_true hst hmsg hparse hver hfind hlow hcons hspqr hpqSalt hmac_eq hdec]
  refine RecvDec.forall₂_append hfor (List.Forall₂.cons ?_ (List.Forall₂.cons ?_ (List.Forall₂.cons ?_ List.Forall₂.nil)))
  · unfold EventMatchesEntry; dsimp only; exact ⟨rfl, t, pf, rfl, hpf, hbk, ht_gam.symm⟩
  · unfold EventMatchesEntry trEntry trLayout; dsimp only; exact ⟨rfl, by simp only [List.map, hrng_gam]; rfl⟩
  · unfold EventMatchesEntry trEntry trLayout; dsimp only; exact ⟨rfl, by simp only [List.map, hpt_gam]; rfl⟩

private theorem promDH_rawDecryptMatched_decrypt_ratchet_two_attackerSend_preKeyInner
    {interpretation : ExternInterpretation} {r₀ : ProtocolSetup} {S : OpaqueSymbolSemantics} {who : List Participant}
    {g : Ghost} {ms₁ : List Move} {τ : List MachineEvent}
    {p : Participant} {stateIdx : Nat} {spqrMsgIdx : UInt32} {st : TRState}
    {t seed key pqSalt ptTerm spqr' : DY.Bytes} {msg : TRSignalMsg} {c' : RecvChain}
    {b rngBytes outPt : HwBytes} {pf : PreKeyFields}
    (hmp : MatchedPrefix interpretation r₀ S who g ms₁ τ)
    (hpq_kn : pqSalt.AttackerKnows (runTraceMoves r₀ ms₁))
    (ht_kn : t.AttackerKnows (runTraceMoves r₀ ms₁))
    (hcur : isCurrentSnapshot (runTraceMoves r₀ ms₁) stateIdx = true)
    (hst : ((PersistentLocalState.getLocalState p stateIdx : Traceful TRState).run (runTraceMoves r₀ ms₁)).1 = some st)
    (hparse : parseTrSignalMsg t = some msg)
    (hver : msg.version = messageVersion)
    (hfind : findRecvChain st.recv msg.ratchetKey = none)
    (hlow : x25519LowOrder msg.ratchetKey = false)
    (hcons : consumeMessageKey (trDhRatchetState st msg.ratchetKey ((runTraceMoves r₀ ms₁).length + 2)).2 msg.counter = some (seed, c'))
    (hspqr : Spqr.spqrRecv (trDhRatchetState st msg.ratchetKey ((runTraceMoves r₀ ms₁).length + 2)).1.spqr msg.pqRatchet spqrMsgIdx = some (spqr', key))
    (hmac_eq : msg.mac = computeMac (trMsgKeys pqSalt seed).macKey
      (trDhRatchetState st msg.ratchetKey ((runTraceMoves r₀ ms₁).length + 2)).1.peerIk
      (trDhRatchetState st msg.ratchetKey ((runTraceMoves r₀ ms₁).length + 2)).1.myIk msg.wire)
    (hdec : DY.SymEnc.symDec (trMsgKeys pqSalt seed).cipherKey (trMsgKeys pqSalt seed).iv msg.ciphertext = some ptTerm)
    (hpf : parsePreKeyWire b = some pf)
    (hbk : ∃ ek ∈ sessionBaseKeys
        (runTraceMoves r₀ (ms₁ ++ [Move.attackerSend pqSalt, Move.attackerSend t])) stateIdx,
      pf.baseKey.take 33 = ecKey (gamma interpretation S g ek))
    (ht_gam : gamma interpretation S g t = pf.message)
    (hrng_gam : gamma interpretation S g (randTerm ((runTraceMoves r₀ ms₁).length + 2) 32) = rngBytes)
    (hpt_gam : gamma interpretation S g ptTerm = outPt) :
    RawDecryptMatched interpretation r₀ S g
      (ms₁ ++ ([.attackerSend pqSalt, .attackerSend t] ++
        [.decrypt p stateIdx ((runTraceMoves r₀ ms₁).length + 1) (runTraceMoves r₀ ms₁).length spqrMsgIdx true]))
      (τ ++ [.recv b, .rng rngBytes, .accept outPt]) := by
  let tr₀ := runTraceMoves r₀ ms₁
  let ms_a1 := ms₁ ++ [Move.attackerSend pqSalt]
  let ms_a2 := ms_a1 ++ [Move.attackerSend t]
  have htr_a1 : runTraceMoves r₀ ms_a1 = tr₀.append (⟨pqSalt⟩ : Network.ExecEntryT) := by
    rw [runTrace_snoc]
    unfold Move.next Move.act
    simp only [Symbolic.DYBridge.DY.Network.sendMessage_eq_1,
      Symbolic.DYBridge.DY.appendEntry_eq_1, DY.Traceful.run_bind, DY.Traceful.run_mk,
      DY.Traceful.run_pure]
    rfl
  have htr_a2 : runTraceMoves r₀ ms_a2 =
      (tr₀.append (⟨pqSalt⟩ : Network.ExecEntryT)).append (⟨t⟩ : Network.ExecEntryT) := by
    rw [runTrace_snoc, htr_a1]
    unfold Move.next Move.act
    simp only [Symbolic.DYBridge.DY.Network.sendMessage_eq_1,
      Symbolic.DYBridge.DY.appendEntry_eq_1, DY.Traceful.run_bind, DY.Traceful.run_mk,
      DY.Traceful.run_pure]
  have hlen_a2 : (runTraceMoves r₀ ms_a2).length = tr₀.length + 2 := by
    rw [htr_a2]
    simp only [Symbolic.DYBridge.DY.Trace.append_eq_1, Symbolic.DYBridge.DY.Trace.length_eq_2]
  have hmp1 := matchedPrefix_attackerSend hmp hpq_kn
  have ht_kn1 : t.AttackerKnows (runTraceMoves r₀ ms_a1) := by
    rw [htr_a1]; exact DY.Bytes.AttackerKnows_le t tr₀ _ (Trace.append_le tr₀ _) ht_kn
  have hmp2 := matchedPrefix_attackerSend hmp1 ht_kn1
  have hraw2 : RawDecryptMatched interpretation r₀ S g ms_a2 τ :=
    ⟨hmp2.1, hmp2.2.1, hmp2.2.2.2.2.2⟩
  have hcur2 : isCurrentSnapshot (runTraceMoves r₀ ms_a2) stateIdx = true := by
    rw [htr_a2, RecvDec.isCurrentSnapshot_append_non_st _ _ rfl, RecvDec.isCurrentSnapshot_append_non_st _ _ rfl]
    exact hcur
  have hst2 : ((PersistentLocalState.getLocalState p stateIdx : Traceful TRState).run
      (runTraceMoves r₀ ms_a2)).1 = some st := by
    rw [runTrace_snoc, getLocalState_attackerSend, runTrace_snoc, getLocalState_attackerSend]
    exact hst
  have hmsg2 : (runTraceMoves r₀ ms_a2).getMessageSentAt (tr₀.length + 1) = some t := by
    have hlen1 : (tr₀.append (⟨pqSalt⟩ : Network.ExecEntryT)).length = tr₀.length + 1 := by
      simp only [Symbolic.DYBridge.DY.Trace.append_eq_1, Symbolic.DYBridge.DY.Trace.length_eq_2]
    rw [runTrace_snoc, htr_a1, ← hlen1]
    exact getMessageSentAt_attackerSend _ t
  have hpqSalt2 : ((((runTraceMoves r₀ ms_a2).append (⟨32⟩ : DY.Random.ExecEntryT)).append
      (⟨key⟩ : Network.ExecEntryT)).at? tr₀.length : Option Network.ExecEntryT) = some ⟨pqSalt⟩ := by
    rw [htr_a2,
        RecvDec.at?_append_of_lt _ _ (by simp only [Symbolic.DYBridge.DY.Trace.append_eq_1, Symbolic.DYBridge.DY.Trace.length_eq_2]; omega),
        RecvDec.at?_append_of_lt _ _ (by simp only [Symbolic.DYBridge.DY.Trace.append_eq_1, Symbolic.DYBridge.DY.Trace.length_eq_2]; omega),
        RecvDec.at?_append_of_lt _ _ (by simp only [Symbolic.DYBridge.DY.Trace.append_eq_1, Symbolic.DYBridge.DY.Trace.length_eq_2]; omega)]
    exact Trace.at?_append tr₀ (⟨pqSalt⟩ : Network.ExecEntryT)
  have hcons2 : consumeMessageKey (trDhRatchetState st msg.ratchetKey (runTraceMoves r₀ ms_a2).length).2 msg.counter = some (seed, c') := by
    rw [hlen_a2]; exact hcons
  have hspqr2 : Spqr.spqrRecv (trDhRatchetState st msg.ratchetKey (runTraceMoves r₀ ms_a2).length).1.spqr msg.pqRatchet spqrMsgIdx = some (spqr', key) := by
    rw [hlen_a2]; exact hspqr
  have hmac2 : msg.mac = computeMac (trMsgKeys pqSalt seed).macKey
      (trDhRatchetState st msg.ratchetKey (runTraceMoves r₀ ms_a2).length).1.peerIk
      (trDhRatchetState st msg.ratchetKey (runTraceMoves r₀ ms_a2).length).1.myIk msg.wire := by
    rw [hlen_a2]; exact hmac_eq
  have hrng2 : gamma interpretation S g (randTerm (runTraceMoves r₀ ms_a2).length 32) = rngBytes := by
    rw [hlen_a2]; exact hrng_gam
  have hms_a2 : ms_a2 = ms₁ ++ [Move.attackerSend pqSalt, Move.attackerSend t] := by
    simp [ms_a2, ms_a1, List.append_assoc]
  have hbk2 : ∃ ek ∈ sessionBaseKeys (runTraceMoves r₀ ms_a2) stateIdx,
      pf.baseKey.take 33 = ecKey (gamma interpretation S g ek) := by
    rw [hms_a2]; exact hbk
  have hstep := promDH_rawDecryptMatched_step_decrypt_ratchet_preKeyInner hraw2 hcur2 hst2 hmsg2
    hparse hver hfind hlow hcons2 hspqr2 hpqSalt2 hmac2 hdec hpf hbk2 ht_gam hrng2 hpt_gam
  have hms_eq : ms_a2 ++ [Move.decrypt p stateIdx (tr₀.length + 1) tr₀.length spqrMsgIdx true] =
      ms₁ ++ ([.attackerSend pqSalt, .attackerSend t] ++
        [.decrypt p stateIdx (tr₀.length + 1) tr₀.length spqrMsgIdx true]) := by
    simp [ms_a2, ms_a1, List.append_assoc]
  rw [← hms_eq]; exact hstep

set_option maxHeartbeats 800000 in
/-- Extends every clean explanation of an accepting, non-colliding `.preKey` promote call in the
`PromDecSelRatchetDH` branch to a `RawDecryptMatched` witness with attacker-known `pqSalt`. -/
theorem prom_rawKnBranch_ratchetDH
    (interpretation : ExternInterpretation) {r : ProtocolSetup} {S : OpaqueSymbolSemantics}
    {who : List Participant} {ok : Nat → Bool}
    (hext : DY.Libsignal.Composed.Refinement.Cli.ExternContractsHoldCli interpretation)
    (hwf : ProtocolSetupWF r)
    (_hik : IkShape interpretation r)
    (hSeq : S = compSemOf interpretation r)
    (hVer : PromVersionOK interpretation r S who ok) :
    PromRawKnBranchOK interpretation r S who ok PromDecSelRatchetDH := by
  intro j e' mid acc rec tag body sm pf sess sess' coins expected pt
    hC _hcol hsel g ms t' hc hctx ht' hncol _hnors
  have hmp : MatchedPrefix interpretation r S who g ms acc := hc.matched
  have hmp_nil : MatchedPrefix interpretation r S who g ms (acc ++ []) := by
    simpa only [List.append_nil] using hmp
  have hABS' : G1cAttackerBuiltSeedExcl' interpretation r S g ms := hctx.abs'
  have hsent_nil : e'.sent = sentBodies (acc ++ []) := by
    simpa only [List.append_nil] using hC.entry.sent_eq
  have hfit : SrHonestVer.SendsFit acc := hC.entry.ready.2.1.sendsFit
  have hfit_nil : SrHonestVer.SendsFit (acc ++ []) := by
    simpa only [List.append_nil] using hfit
  have hpq : PqFromHonest e'.sent pf.message := hC.entry.pqh pf hC.out.hpf
  have htry : SignalMessage.tryFrom protoSignalCodec pf.message = .ok pf.inner :=
    parsePreKeyWire_inner_tryFrom hC.out.hpf
  have hceh := hext.1
  have hss : SingleSession rec :=
    let ⟨rr₀, _, hrec_rr₀, hprev₀, _⟩ := hC.entry.pm
    ⟨rr₀, hrec_rr₀, hprev₀⟩
  have hrr := pureCRecRelH_single (hC.entry.ready.2.1.recs hc r.bob rec hC.entry.rec_lookup).2.2 hss
  have hrsi : PureTRRecordStateInv interpretation r S (pureTrSlots r) g ms
      (fun q => if q = r.bob then some rec else none) := by
    rcases hrr with h | ⟨hab, _⟩
    · exact h
    · exact False.elim (hwf.1 hab.symm)
  obtain ⟨_hp_mem, rec₀, st₀, stateIdx₀, hrecBytes₀, hst₀, hcur₀, hrel₀, _hsk_pre₀, _hcanon₀, hks₀, _hnd₀⟩ :=
    hrsi r.bob rec (by simp)
  let g_rw : RecvWireGhost :=
    { who := 1, aPtr := 0, meBytes := [], stateBytes := rec, sess := sess,
      wirePtr := 0, wireBytes := wireWhisperTag :: pf.message, cur := 0, rest := [], tlsInit := none }
  have hcanon_q : Symbolic.Swarm.CREF.TR.Pure.slots_RecordCanonical_Q Symbolic.Swarm.CREF.TR.Pure.slots_NonEmptyV1Q rec g_rw.sess := hC.out.hcan_in
  have hnorm_eq := rec_eq_sessionToRecordRec_of_canonical_Q hrecBytes₀ hcanon_q
  have hrel₀_sess : StateRel interpretation S g st₀ (sessionToRecordRec g_rw.sess) := by
    rw [← stateRel_sessionToRecordRecPending_iff, ← stateRel_normPending_iff, ← hnorm_eq, stateRel_normPending_iff]
    exact hrel₀
  obtain ⟨rngBytes, remIk, ck, ck_adv, ck_next, r1, r_adv, r2, mkGen, newPqrState, pqrKey, _st',
      hmid_rng, hrng_len, _hcoins_rng, hRem, hFind, hDh, hNotLt, hJump, hAdv, hNext, hSet, hMkGen,
      hrecv_spqr, hMac, hDec, _hSt', _hsess'_st, _hsm_st⟩ :=
    prom_adapter_ratchetDH_out hC.out hsel
  subst hmid_rng
  obtain ⟨msg₀, hparse₀⟩ := Option.isSome_iff_exists.mp ht'.2.2.1
  let g' : Ghost := { g with σ := updateFreshAt g.σ ((runTraceMoves r ms).length + 2) 32 rngBytes }
  have hRun : ModelRun r ms := hmp.2.1
  have hreach : (runTraceMoves r ms).Reachable reachability := hRun.2.2.1.1
  have hst_avail : st₀ ∈ availableStates r (runTraceMoves r ms) :=
    Symbolic.Swarm.CREF.TR.RecvHistStep2.mem_availableStates_of_at? r ms
      (Symbolic.Swarm.CREF.TR.FreshSigma.at?_eq_some_of_getLocalState_some hst₀)
  obtain ⟨hRng, hmp', _hrsi', hrel₀', hks₀', _hst_lt, _hmsg_lt, _ht_gam, _hwire_gam, _hmac_gam,
      _hrk_gam, _hct_gam, _hpq_gam, _hspqr_gam, _hrecv_gam⟩ :=
    ratchetDH_sigma_bridge interpretation r hwf S (pureTrSlots r) g ms (acc ++ [])
      (fun q => if q = r.bob then some rec else none) r.bob stateIdx₀ st₀ (sessionToRecordRec g_rw.sess) t' msg₀
      ((runTraceMoves r ms).length + 2) rngBytes (by omega)
      hmp_nil hrsi hst₀ hrel₀_sess hks₀ ht'.1 hparse₀
  have htr_lt : TraceEntriesLt interpretation S g ((runTraceMoves r ms).length + 2) (runTraceMoves r ms) :=
    traceEntriesLt_of_reachable interpretation S g ((runTraceMoves r ms).length + 2) hreach (by omega)
  obtain ⟨_hrk_sess, _hcks_sess, _hdhs_sess, hloc_ser, ⟨rem0, hrem0, hrem_ser⟩, _hrc_sess⟩ :=
    stateRel_sessionToRecordRec_extract_TR interpretation S g' st₀ g_rw.sess hrel₀'
  have hst₀_rci : TrStateRkCkIk r st₀ := trStateRkCkIk_of_getLocalState hmp'.2.1 hst₀
  have hRkLen : (gamma interpretation S g' st₀.rk).length = 32 :=
    hst₀_rci.rk_len interpretation S g' hwf hmp'.1
  have hCkLens : ∀ c ∈ st₀.recv, (gamma interpretation S g' c.chainKey).length = 32 :=
    hst₀_rci.recv_ck_len interpretation S g' hwf hmp'.1
  have hTheir' : pf.inner.senderRatchetKey.bytes.toList = gamma interpretation S g' msg₀.ratchetKey :=
    ((ht'.2.2.2 msg₀ hparse₀).2.2.2 pf.inner htry).2.1.symm.trans _hrk_gam.symm
  have hPkLen : (gamma interpretation S g' msg₀.ratchetKey).length = 32 :=
    hTheir' ▸ pf.inner.senderRatchetKey.bytes.2
  have hTheir : pf.inner.senderRatchetKey = ⟨vec32 (gamma interpretation S g' msg₀.ratchetKey)⟩ := by
    cases hmk : pf.inner.senderRatchetKey with | mk b =>
    have hb : b.toList = (vec32 (gamma interpretation S g' msg₀.ratchetKey)).toList := by
      rw [hmk] at hTheir'; exact hTheir'.trans (vec32_toList_of_length_eq_tr hPkLen).symm
    exact congrArg PublicKey.mk (Subtype.ext hb)
  have ht₀' : t' ∈ recvRepresentations interpretation r S g' ms pf.message := by
    refine ⟨ht'.1, _ht_gam.trans ht'.2.1, ht'.2.2.1, fun msg hmsg => ?_⟩
    rcases Option.some.inj (hparse₀.symm.trans hmsg) with rfl
    have h₀ := ht'.2.2.2 msg₀ hparse₀
    refine ⟨_hwire_gam.trans h₀.1, _hmac_gam.trans h₀.2.1, h₀.2.2.1, fun parsed hparsed => ?_⟩
    have hp := h₀.2.2.2 parsed hparsed
    exact ⟨_hct_gam.trans hp.1, _hrk_gam.trans hp.2.1, _hpq_gam.trans hp.2.2.1, hp.2.2.2⟩
  have hJump' : (pf.inner.counter - ck.index).toNat ≤ CryptoGames.LibsignalSession.maxForwardJumps := by
    obtain ⟨_, _, _, _, _, _, _, hr1⟩ := Proofs.libsignal.RngG.R3.dhRatchetStep_ok_inv hDh
    rw [hr1] at hJump; exact hJump
  have hctr₀ : msg₀.counter = UInt32.ofBitVec pf.inner.counter :=
    UInt32.ext (((ht₀'.2.2.2 msg₀ hparse₀).2.2.2 pf.inner htry).2.2.2.1)
  obtain ⟨hfind₀, _mks', seed, c', hcons₀_bv, hSeedEq, hCntEq,
      _hc'_rk, _hc'_rIdx, _hc_idx0, _hc_rIdx, _hR2Eq', _hRel_lit, _hRcMem, _hMks'⟩ :=
    stateRel_and_consumeMessageKey_of_dhRatchetStep_tr interpretation S g' hceh (hrel := hrel₀')
      (hRkLen := hRkLen) (hDhsLen := hks₀'.1) (hCkLens := hCkLens) (hTheir := hTheir) (hPkLen := hPkLen)
      (hRng := hRng) (hRngLen := hrng_len)
      (hspqr' := gamma_litOf interpretation S g' newPqrState)
      (hFindNone := hFind) (hStep := hDh)
      (hNotLt := hNotLt) (hJump := hJump') (hAdv := hAdv) (hNext := hNext) (hSet := hSet)
  have hcons₀ :
      consumeMessageKey (trDhRatchetState st₀ msg₀.ratchetKey ((runTraceMoves r ms).length + 2)).2 msg₀.counter =
        some (seed, c') := by
    rw [hctr₀]; exact hcons₀_bv
  have hlow₀ : x25519LowOrder msg₀.ratchetKey = false :=
    x25519LowOrder_false_of_dhRatchetStep_ok_tr interpretation S g' hceh (hTheir := hTheir') (hDh := hDh)
  have hver_pf : pf.inner.messageVersion = 4#8 :=
    hVer j e' [.rng rngBytes] acc rec (tag :: body) sm pf sess sess' coins expected pt hC
  have hver₀_nat : msg₀.version.toNat = pf.inner.messageVersion.toNat :=
    ((ht₀'.2.2.2 msg₀ hparse₀).2.2.2 pf.inner htry).2.2.2.2
  have hver₀ : msg₀.version = messageVersion :=
    UInt8.ext (by rw [hver₀_nat, hver_pf]; rfl)
  have hseed : recvSeed st₀ msg₀ = some seed := by
    unfold recvSeed
    simp only [hver₀, ↓reduceIte, recvChainFor, hfind₀, hlow₀, Bool.false_eq_true]
    change Option.map Prod.fst
      (consumeMessageKey (trDhRatchetState st₀ msg₀.ratchetKey ((runTraceMoves r ms).length + 2)).2 msg₀.counter) =
      some seed
    rw [hcons₀]; rfl
  let k_own : DY.Bytes := ({ st := st₀.spqr, msg := msg₀.pqRatchet } : DY.Spqr.RecvKey.SubF DY.Bytes).pack
  have hk_own : k_own ∈ ownKeys r (runTraceMoves r ms) st₀ msg₀ := by
    unfold ownKeys
    exact List.mem_map_of_mem (List.mem_filter.mpr ⟨hst_avail, beq_self_eq_true _⟩)
  have hpq_sess' : g_rw.sess.state.pqRatchetState = gamma interpretation S g' st₀.spqr :=
    congrArg SessionRec.pqRatchetState hrel₀'.2
  have hk_own_gam : gamma interpretation S g' k_own =
      spqrKeyBytes (saltToBytes pqrKey) :=
    (spqrRecv_step_gamma_state_and_key interpretation hceh r S hSeq g' ms pf.message st₀ g_rw t' msg₀ pf.inner
      newPqrState pqrKey hpq_sess' ht₀' hparse₀ htry hrecv_spqr).2
  have hmkGen_eq : mkGen = ⟨gamma interpretation S g' seed, pf.inner.counter⟩ := by
    rw [hMkGen]
    change ck_adv.messageKeys (sha256CompressFunction interpretation) = _
    rcases h : ck_adv.messageKeys (sha256CompressFunction interpretation) with ⟨sd, ct⟩
    rw [h] at hSeedEq hCntEq; dsimp only at hSeedEq hCntEq; subst hSeedEq hCntEq; rfl
  obtain ⟨hck_mk, hmk_mk, hiv_mk, _⟩ :=
    gamma_trMsgKeys_eq_generateKeys interpretation S g' k_own seed pf.inner.counter pqrKey hk_own_gam
  have hDecOk :
      interpretation aesCbcDecryptSymbol
        [pf.inner.ciphertext, gamma interpretation S g' (trMsgKeys k_own seed).cipherKey,
         (gamma interpretation S g' (trMsgKeys k_own seed).iv).take 16] = some pt := by
    rw [← hck_mk, ← hiv_mk]
    change (Proofs.libsignal.SR.interpW interpretation).dec
      (MessageKeyGenerator.generateKeys (cryptoOf' interpretation).F
        ⟨gamma interpretation S g' seed, pf.inner.counter⟩ pqrKey).cipherKey
      (MessageKeyGenerator.generateKeys (cryptoOf' interpretation).F
        ⟨gamma interpretation S g' seed, pf.inner.counter⟩ pqrKey).iv pf.inner.ciphertext = some pt
    rw [← hmkGen_eq]; exact hDec
  rw [hRem] at hrem0; injection hrem0 with hrem_eq; subst hrem_eq
  have hpeer_ser : remIk.serialize = gamma interpretation S g' st₀.peerIk :=
    hrem_ser.trans hks₀'.peerIk_ser
  have hmy_ser : g_rw.sess.state.localIdentity.serialize = gamma interpretation S g' st₀.myIk :=
    hloc_ser.trans hks₀'.myIk_ser
  have hwire₀_take : gamma interpretation S g' msg₀.wire = pf.message.take (pf.message.length - 8) :=
    (ht₀'.2.2.2 msg₀ hparse₀).1
  have hm_ser : pf.inner.serialized = pf.message := promDH_tryFrom_serialized_eq htry
  have hMacBytes :
      pf.message.drop (pf.message.length - 8) =
        gamma interpretation S g' (computeMac (trMsgKeys k_own seed).macKey st₀.peerIk st₀.myIk msg₀.wire) := by
    have hmac_ver : pf.inner.verifyMac (cryptoOf' interpretation).F remIk g_rw.sess.state.localIdentity
        (mkGen.generateKeys (cryptoOf' interpretation).F pqrKey).macKey = true :=
      ((Proofs.libsignal.RngG.CliPure.DecCrypto.verifyMacWithAddresses_eq_true_iff _ _ _ _ _ _).mp hMac).1
    unfold SignalMessage.verifyMac macLength at hmac_ver
    dsimp only at hmac_ver
    have hmac_eq := (beq_iff_eq.mp hmac_ver).symm
    rw [hm_ser] at hmac_eq; rw [hmac_eq]
    have hkey_mk : keyToBytes32 ((mkGen.generateKeys (cryptoOf' interpretation).F pqrKey).macKey) =
        gamma interpretation S g' (trMsgKeys k_own seed).macKey := by
      rw [hmkGen_eq]; exact hmk_mk
    exact gamma_computeMac_tr interpretation S g' (trMsgKeys k_own seed).macKey
      st₀.peerIk st₀.myIk msg₀.wire remIk g_rw.sess.state.localIdentity
      ((mkGen.generateKeys (cryptoOf' interpretation).F pqrKey).macKey)
      hkey_mk hpeer_ser hmy_ser (pf.message.take (pf.message.length - 8)) hwire₀_take.symm
  have hc_lt : ChainStampsLt interpretation S g ((runTraceMoves r ms).length + 2)
      (trDhRatchetState st₀ msg₀.ratchetKey ((runTraceMoves r ms).length + 2)).2 :=
    ⟨_hmsg_lt.2.2.1, (stampsLt_createChain _hst_lt.2.2.1 _hmsg_lt.2.2.1 _hst_lt.2.2.2.1).2⟩
  have hseed_lt : StampsLt interpretation S g ((runTraceMoves r ms).length + 2) seed :=
    (stampsLt_consumeMessageKey hc_lt hcons₀).1
  have hk_own_lt : StampsLt interpretation S g ((runTraceMoves r ms).length + 2) k_own :=
    (stampsLt_spqrRecvKey_pack interpretation S g ((runTraceMoves r ms).length + 2) ⟨st₀.spqr, msg₀.pqRatchet⟩).mpr
      ⟨_hst_lt.2.2.2.2.2.1, _hmsg_lt.2.2.2.2⟩
  have hkeys_lt := stampsLt_trMsgKeys hk_own_lt hseed_lt
  have hmac_term_lt := stampsLt_computeMac hkeys_lt.2.1 _hst_lt.2.1 _hst_lt.1 _hmsg_lt.1
  have hMacBytes₁ :
      pf.message.drop (pf.message.length - 8) =
        gamma interpretation S g (computeMac (trMsgKeys k_own seed).macKey st₀.peerIk st₀.myIk msg₀.wire) := by
    rw [← gamma_updateFreshAt_of_stampsLt interpretation S g ((runTraceMoves r ms).length + 2) 32 rngBytes _ hmac_term_lt]
    exact hMacBytes
  have hDecOk₁ :
      interpretation aesCbcDecryptSymbol
        [pf.inner.ciphertext, gamma interpretation S g (trMsgKeys k_own seed).cipherKey,
         (gamma interpretation S g (trMsgKeys k_own seed).iv).take 16] = some pt := by
    rw [← gamma_updateFreshAt_of_stampsLt interpretation S g ((runTraceMoves r ms).length + 2) 32 rngBytes _ hkeys_lt.1,
        ← gamma_updateFreshAt_of_stampsLt interpretation S g ((runTraceMoves r ms).length + 2) 32 rngBytes _ hkeys_lt.2.2]
    exact hDecOk
  have hik0_kn : (DY.Libsignal.PQXDH.serializedIk (setupPublic r 0)).AttackerKnows (runTraceMoves r ms) :=
    Concat.attacker_knows_concat _ _ _ (Literal.attacker_knows_literalToBytes _ _)
      (Symbolic.Swarm.CREF.CliPure.TR.knows_setupPublic r hwf.1 ms 0 (Or.inl rfl))
  have hik2_kn : (DY.Libsignal.PQXDH.serializedIk (setupPublic r 2)).AttackerKnows (runTraceMoves r ms) :=
    Concat.attacker_knows_concat _ _ _ (Literal.attacker_knows_literalToBytes _ _)
      (Symbolic.Swarm.CREF.CliPure.TR.knows_setupPublic r hwf.1 ms 2 (Or.inr rfl))
  have hPeerK : st₀.peerIk.AttackerKnows (runTraceMoves r ms) := hst₀_rci.peerIk.elim (· ▸ hik0_kn) (· ▸ hik2_kn)
  have hMyK : st₀.myIk.AttackerKnows (runTraceMoves r ms) := hst₀_rci.myIk.elim (· ▸ hik0_kn) (· ▸ hik2_kn)
  have hDisjRks := recv_mac_authentic_or_rkSwap_seed_known_of_not_collision_explains'
    interpretation hceh r S g ms pf.message pt pf.inner hc.1 hABS' hreach
    htry t' msg₀ ht' hparse₀ hncol st₀ hst_avail hfind₀ seed hseed k_own hk_own hMacBytes₁ hDecOk₁
  have hHon : PqFromHonest (sentBodies (acc ++ [])) pf.message := hsent_nil ▸ hpq
  have hBridge₁ := hDisjRks.elim
    (fun hRkSwap => spqrRecv_step_bridge_ratchetDH_rkSwap_nw
      interpretation hceh r S hSeq g r.bob stateIdx₀ ms (acc ++ []) rec pf.message pt
      rec₀ st₀ g_rw t' msg₀ pf.inner seed k_own c' newPqrState pqrKey
      hmp_nil hfit_nil hrecBytes₀ hrel₀ hst₀ hcanon_q hHon htry ht' hparse₀ hver₀ hctr₀ hcons₀
      hMacBytes₁ hPeerK hMyK hDecOk₁ hrecv_spqr (Or.inl hRkSwap))
    (fun ⟨salt₁, _hsalt₁, hrk_sid, hAuth, hMacBytes_salt₁, hDecOk_salt₁⟩ =>
      spqrRecv_step_bridge_ratchetDH_rkSwap_nw
        interpretation hceh r S hSeq g r.bob stateIdx₀ ms (acc ++ []) rec pf.message pt
        rec₀ st₀ g_rw t' msg₀ pf.inner seed salt₁ c' newPqrState pqrKey
        hmp_nil hfit_nil hrecBytes₀ hrel₀ hst₀ hcanon_q hHon htry ht' hparse₀ hver₀ hctr₀ hcons₀
        hMacBytes_salt₁.symm hPeerK hMyK hDecOk_salt₁ hrecv_spqr (Or.inr ⟨hrk_sid, hAuth⟩))
  obtain ⟨rk_c, seed_c, c'_c, t_m, msg', pqSalt, ptTerm, spqr', key, spqrMsgIdx,
      _hrk_c_sid, hγ_rk_c₁, _hγ_seed_c, hcons_c, ht_m_rep, hpqSalt_kn, ht_m_kn,
      hparse', hver', hrk', _hctr', hspqr_step, _hspqr'_gam₁, hmac', hdec', ht_m_gam₁, hpt_gam₁,
      _st_s, _t_c, _coinsLen, _hst_s, _hpq_eq⟩ := hBridge₁
  have ht_m_lt : StampsLt interpretation S g ((runTraceMoves r ms).length + 2) t_m :=
    traceEntriesLt_knows htr_lt ht_m_kn
  have hmsg'_lt := stampsLt_parseTrSignalMsg ht_m_lt hparse'
  have hrk_c_lt : StampsLt interpretation S g ((runTraceMoves r ms).length + 2) rk_c :=
    hrk' ▸ hmsg'_lt.2.2.1
  have hpt_lt := stampsLt_symDec hdec' hmsg'_lt.2.2.2.1
  have hγ_rk_c : gamma interpretation S g' rk_c = gamma interpretation S g' msg₀.ratchetKey := by
    rw [gamma_updateFreshAt_of_stampsLt interpretation S g ((runTraceMoves r ms).length + 2) 32 rngBytes rk_c hrk_c_lt,
        gamma_updateFreshAt_of_stampsLt interpretation S g ((runTraceMoves r ms).length + 2) 32 rngBytes msg₀.ratchetKey _hmsg_lt.2.2.1]
    exact hγ_rk_c₁
  have ht_m_gam : gamma interpretation S g' t_m = pf.message := by
    rw [gamma_updateFreshAt_of_stampsLt interpretation S g ((runTraceMoves r ms).length + 2) 32 rngBytes t_m ht_m_lt]
    exact ht_m_gam₁
  have hpt_gam : gamma interpretation S g' ptTerm = pt := by
    rw [gamma_updateFreshAt_of_stampsLt interpretation S g ((runTraceMoves r ms).length + 2) 32 rngBytes ptTerm hpt_lt]
    exact hpt_gam₁
  have hfind' : findRecvChain st₀.recv msg'.ratchetKey = none := hrk' ▸
    (findRecvChain_eq_none_of_dhRatchetStep_rkSwap (msg₀ := msg₀) interpretation S g' hrel₀' hCkLens hFind hTheir hγ_rk_c).1
  have hlow' : x25519LowOrder msg'.ratchetKey = false := hrk' ▸
    x25519LowOrder_false_of_dhRatchetStep_rkSwap (msg₀ := msg₀)
      interpretation S g' hceh (hTheir₀ := hTheir) (hPkLen₀ := hPkLen) (hγ_rk_c := hγ_rk_c) (hDh := hDh)
  have hcons' : consumeMessageKey (trDhRatchetState st₀ msg'.ratchetKey ((runTraceMoves r ms).length + 2)).2 msg'.counter = some (seed_c, c'_c) :=
    hrk' ▸ hcons_c
  have hspqr_step' : Spqr.spqrRecv (trDhRatchetState st₀ msg'.ratchetKey ((runTraceMoves r ms).length + 2)).1.spqr msg'.pqRatchet spqrMsgIdx = some (spqr', key) :=
    hrk' ▸ hspqr_step
  have hmac_eq' : msg'.mac = computeMac (trMsgKeys pqSalt seed_c).macKey
      (trDhRatchetState st₀ msg'.ratchetKey ((runTraceMoves r ms).length + 2)).1.peerIk
      (trDhRatchetState st₀ msg'.ratchetKey ((runTraceMoves r ms).length + 2)).1.myIk msg'.wire :=
    hrk' ▸ hmac'
  have hrng_gam : gamma interpretation S g' (randTerm ((runTraceMoves r ms).length + 2) 32) = rngBytes := by
    rw [promDH_gamma_randTerm32_eq]; exact hRng
  rw [List.append_nil] at hmp'
  have hfr : CBadSigmaFrame g g' (runTraceMoves r ms).length :=
    ⟨fun i hi _sz => ite_eq_right (by omega), rfl⟩
  have hbk := prom_baseKeyInSession_of_rbks hC.entry.pm hC.out.hpf hC.entry.rec_lookup
    (hC.entry.ready.2.1.bks hc) hc.matched.2.1 hst₀ hcur₀ hfr pqSalt t_m
  have hmp₁ := promDH_rawDecryptMatched_decrypt_ratchet_two_attackerSend_preKeyInner
    hmp' hpqSalt_kn ht_m_kn hcur₀ hst₀ hparse' hver' hfind' hlow' hcons'
    hspqr_step' hmac_eq' hdec' hC.out.hpf hbk ht_m_gam hrng_gam hpt_gam
  have hwrap : decide (tag ≠ wireWhisperTag) = true :=
    decide_eq_true (promDH_tag_ne_wireWhisperTag_of_parsePreKeyWire hC.out.hpf)
  refine ⟨g', stateIdx₀, spqrMsgIdx, pqSalt, t_m,
    Move.decrypt r.bob stateIdx₀ ((runTraceMoves r ms).length + 1)
      (runTraceMoves r ms).length spqrMsgIdx (decide (tag ≠ wireWhisperTag)),
    hfr, ht_m_rep, hpqSalt_kn, hcur₀, Or.inl rfl, ?_⟩
  rw [hwrap]
  exact hmp₁

end Symbolic.Swarm.CREF.CliPure
