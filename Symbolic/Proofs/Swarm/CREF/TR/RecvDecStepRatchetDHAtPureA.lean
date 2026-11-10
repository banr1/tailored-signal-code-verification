/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Symbolic.Proofs.Swarm.CREF.TR.RecvDecStepSkippedG1LeavesPure
public import Symbolic.Proofs.Swarm.CREF.TR.G1.HonestSpine
import DY.Bytes.Basic
import DY.Trace.Basic
import DY.Trace.Monad
import DY.Trace.Manipulation
import DY.ALaCarte.Basic
import DY.Actions.Network
import DY.Actions.PersistentLocalState
import DY.Actions.PersistentGlobalState
import DY.Actions.ProtocolEvent
import DY.Actions.Random
import Symbolic.Proofs.Swarm.COMPOSED.CompHsClass
import Symbolic.Proofs.Swarm.COMPOSED.CompInv
import Symbolic.Proofs.Swarm.COMPOSED.CompPubInv
import Symbolic.Proofs.Swarm.CREF.Cli.Rpk.RecvDecStepCommonPureA
import Symbolic.Proofs.Swarm.CREF.Initiate.InitRej
import Symbolic.Proofs.Swarm.CREF.ModelBridge
import Symbolic.Proofs.Swarm.CREF.Prelude
import Symbolic.Proofs.Swarm.CREF.TR.G1.CanonLocal
import Symbolic.Proofs.Swarm.CREF.TR.G1.HonestSpineRk
import Symbolic.Proofs.Swarm.CREF.TR.G1.OneSidedPeelDefs
import Symbolic.Proofs.Swarm.CREF.TROpen
import Symbolic.Proofs.Swarm.CREF.TR.Leaks -- shake: keep
import Symbolic.Proofs.Swarm.CREF.TR.PQGamma -- shake: keep
import Symbolic.Proofs.Swarm.CREF.TR.PQModelRunNil -- shake: keep
import Symbolic.DYBridge.DY.Bytes.Basic
import Symbolic.DYBridge.DY.Trace.Basic
import Symbolic.DYBridge.DY.Trace.Monad
import Symbolic.DYBridge.DY.Trace.Manipulation
import Symbolic.DYBridge.DY.ALaCarte.Basic
import Symbolic.DYBridge.DY.Actions.Network
import Symbolic.DYBridge.DY.Actions.PersistentLocalState
import Symbolic.DYBridge.DY.Actions.PersistentGlobalState
import Symbolic.DYBridge.DY.Actions.ProtocolEvent
import Symbolic.DYBridge.DY.Actions.Random

/-!
# DH-Ratchet Single-Explanation Receive Step Helpers

Proves pure helper lemmas for the DH-ratchet whisper receive branch at a fixed explanation.
-/

@[expose] public section

cref_hide_foreign_instances
set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

namespace Symbolic.Swarm.CREF.CliPureRcv.TR.RecvDecStepAtPure
open Symbolic.Swarm.CREF.TR hiding at?_append_of_lt gamma_concat gamma_dhPk getLocalState_fst leValue_leBytes length_leBytes newRandoms_append_rnd p25519_lt p25519_pos runMoves_append runTrace_append runTrace_snoc runVis_append runVis_snoc run_bind_fst run_bind_snd uOf_leBytes uOf_lt
open Symbolic.Swarm.CREF.CliPure.TR.RecvDecStep hiding SpqrSem StEntry TREntry
cref_open
cref_open_tr
open DY DY.Comparse DY.Literal DY.Libsignal
open DY.Libsignal.TripleRatchet (RecvChain findRecvChain consumeMessageKey kdfCk maxForwardJumps
  computeMac messageVersion x25519LowOrder)
open DY.Libsignal.TripleRatchet
open DY.Libsignal.TripleRatchet.Refinement (wireWhisperTag)
open DY.Libsignal.HwEvents DY.Libsignal.Rust
open CryptoGames CryptoGames.HMAC CryptoGames.HKDF
open CryptoGames.LibsignalSession CryptoGames.LibsignalSessionApi
open CryptoVerification
open CryptoVerification.LibsignalTripleRatchet CryptoVerification.LibsignalProtoCodec
open CryptoVerification.E2E CryptoVerification.E2E.InMem CryptoVerification.E2E.Record CryptoVerification.E2E.RecordX
open CryptoVerification.E2E.Bin (Role evalOpen inMemAnswers)
open CryptoVerification.E2E.Pqxdh.WireEntries.SymP3 (RecvWireGhost)
open CryptoProofLib.Refinement (ExternInterpretation)
open Proofs.libsignal.RngG
open Proofs.libsignal.Hooks2 (cryptoOf')
open Proofs.libsignal.SR (messageDecryptSignalW)
open Proofs.libsignal.RngG.R3 Proofs.libsignal.RngG.CliPure.R3 Symbolic.Swarm.CREF Symbolic.Swarm.CREF.CliPure Symbolic.Swarm.CREF.CliPureRcv Symbolic.Swarm.CREF.CliPure.TR Symbolic.Swarm.CREF.CliPureRcv.TR
open Symbolic.Swarm.CREF.TR.RecvDec (trDhRatchetState at?_append_of_lt getMessageSentAt_attackerSend
  getLocalState_attackerSend matchedPrefix_attackerSend matchedPrefix_step_decrypt_ratchet)
open Symbolic.Swarm.CREF.TR.FreshSigma hiding TREntry StEntry
open Symbolic.Swarm.TRREF.SpqrSemOf (spqrModelOf)

theorem attackerKnows_monotonic_fk2 {tr₁ tr₂ : ExecTrace} {b : DY.Bytes}
    (hle : tr₁ ≤ tr₂) (h : b.AttackerKnows tr₁) : b.AttackerKnows tr₂ :=
  DY.Bytes.AttackerKnows_le b tr₁ tr₂ hle h

theorem matchedPrefix_decrypt_ratchet_two_attackerSend_at
    {interpretation : ExternInterpretation} {r₀ : ProtocolSetup} {S : SpqrSem}
    {who : List Participant}
    {g' : Ghost} {ms₁ : List Move} {evs acc : List MachineEvent}
    {p : Participant} {stateIdx : Nat} {spqrMsgIdx : UInt32} {st : TRState} {c' : RecvChain}
    {t seed key pqSalt ptTerm spqr' : DY.Bytes} {msg : TRSignalMsg} {body rngBytes outPt : HwBytes}
    (hmp : MatchedPrefix interpretation r₀ S who g' ms₁ (acc ++ evs))
    (hpqSalt_kn : pqSalt.AttackerKnows (runTraceMoves r₀ ms₁)) (ht_kn : t.AttackerKnows (runTraceMoves r₀ ms₁))
    (hcur : isCurrentSnapshot (runTraceMoves r₀ ms₁) stateIdx = true)
    (hst : ((PersistentLocalState.getLocalState p stateIdx : Traceful TRState).run (runTraceMoves r₀ ms₁)).1 = some st)
    (hparse : parseTrSignalMsg t = some msg) (hver : msg.version = messageVersion)
    (hfind : findRecvChain st.recv msg.ratchetKey = none) (hlow : x25519LowOrder msg.ratchetKey = false)
    (hcons : consumeMessageKey (trDhRatchetState st msg.ratchetKey ((runTraceMoves r₀ ms₁).length + 2)).2 msg.counter = some (seed, c'))
    (hspqr : Spqr.spqrRecv (trDhRatchetState st msg.ratchetKey ((runTraceMoves r₀ ms₁).length + 2)).1.spqr msg.pqRatchet spqrMsgIdx = some (spqr', key))
    (hmac_eq : msg.mac = computeMac (trMsgKeys pqSalt seed).macKey
      (trDhRatchetState st msg.ratchetKey ((runTraceMoves r₀ ms₁).length + 2)).1.peerIk
      (trDhRatchetState st msg.ratchetKey ((runTraceMoves r₀ ms₁).length + 2)).1.myIk msg.wire)
    (hdec : DY.SymEnc.symDec (trMsgKeys pqSalt seed).cipherKey (trMsgKeys pqSalt seed).iv msg.ciphertext = some ptTerm)
    (ht_gam : gamma interpretation S g' t = body)
    (hrng_gam : gamma interpretation S g' (randTerm ((runTraceMoves r₀ ms₁).length + 2) 32) = rngBytes)
    (hpt_gam : gamma interpretation S g' ptTerm = outPt)
    (hwho : who[callCount (runVis r₀ ms₁)]? = some p)
    (ht_rep : t ∈ recvRepresentations interpretation r₀ S g' ms₁ body) :
    MatchedPrefix interpretation r₀ S who g'
      (ms₁ ++ [.attackerSend pqSalt, .attackerSend t,
        .decrypt p stateIdx ((runTraceMoves r₀ ms₁).length + 1) (runTraceMoves r₀ ms₁).length spqrMsgIdx false])
      (acc ++ (evs ++ [.recv (wireWhisperTag :: body)] ++ [.rng rngBytes] ++ [.accept outPt])) := by
  let tr₀ := runTraceMoves r₀ ms₁
  let ms_a1 := ms₁ ++ [Move.attackerSend pqSalt]
  let ms_a2 := ms_a1 ++ [Move.attackerSend t]
  have htr_a1 : runTraceMoves r₀ ms_a1 = tr₀.append (⟨pqSalt⟩ : Network.ExecEntryT) := by
    rw [runTrace_snoc]
    simp only [Move.next, Move.act, Symbolic.DYBridge.DY.Network.sendMessage_eq_1,
      Symbolic.DYBridge.DY.appendEntry_eq_1, Symbolic.DYBridge.DY.Traceful.mk_eq_1,
      Symbolic.DYBridge.DY.Traceful.run_eq_1]
    rfl
  have htr_a2 : runTraceMoves r₀ ms_a2 = (tr₀.append (⟨pqSalt⟩ : Network.ExecEntryT)).append (⟨t⟩ : Network.ExecEntryT) := by
    rw [runTrace_snoc, htr_a1]
    simp only [Move.next, Move.act, Symbolic.DYBridge.DY.Network.sendMessage_eq_1,
      Symbolic.DYBridge.DY.appendEntry_eq_1, Symbolic.DYBridge.DY.Traceful.mk_eq_1,
      Symbolic.DYBridge.DY.Traceful.run_eq_1]
    rfl
  have hlen_a2 : (runTraceMoves r₀ ms_a2).length = tr₀.length + 2 := by
    rw [htr_a2]
    simp only [Symbolic.DYBridge.DY.Trace.append_eq_1, Symbolic.DYBridge.DY.Trace.length_eq_2, Nat.add_assoc]
  have hmp1 := matchedPrefix_attackerSend hmp hpqSalt_kn
  have ht_kn1 : t.AttackerKnows (runTraceMoves r₀ ms_a1) := by
    rw [htr_a1]; exact attackerKnows_monotonic_fk2 (Trace.append_le tr₀ _) ht_kn
  have hmp2 := matchedPrefix_attackerSend hmp1 ht_kn1
  have hwho2 : who[callCount (runVis r₀ ms_a2)]? = some p := by
    have hv : runVis r₀ ms_a2 = runVis r₀ ms₁ := by
      change runVis r₀ ((ms₁ ++ [Move.attackerSend pqSalt]) ++ [Move.attackerSend t]) = runVis r₀ ms₁
      rw [runVis_snoc, vis_attackerSend_nil, List.append_nil, runVis_snoc, vis_attackerSend_nil, List.append_nil]
    rw [hv]; exact hwho
  have ht_rep2 : t ∈ recvRepresentations interpretation r₀ S g' ms_a2 body :=
    ⟨by rw [htr_a2]; exact attackerKnows_monotonic_fk2 (Trace.append_le _ _) (by rw [← htr_a1]; exact ht_kn1), ht_rep.2⟩
  have hcur2 : isCurrentSnapshot (runTraceMoves r₀ ms_a2) stateIdx = true := by
    rw [htr_a2, isCurrentSnapshot_append_non_st _ _ rfl, isCurrentSnapshot_append_non_st _ _ rfl]; exact hcur
  have hst2 : ((PersistentLocalState.getLocalState p stateIdx : Traceful TRState).run (runTraceMoves r₀ ms_a2)).1 = some st := by
    rw [runTrace_snoc, getLocalState_attackerSend, runTrace_snoc, getLocalState_attackerSend]; exact hst
  have hmsg2 : (runTraceMoves r₀ ms_a2).getMessageSentAt (tr₀.length + 1) = some t := by
    have hl1 : tr₀.length + 1 = (tr₀.append (⟨pqSalt⟩ : Network.ExecEntryT)).length := by
      simp only [Symbolic.DYBridge.DY.Trace.append_eq_1, Symbolic.DYBridge.DY.Trace.length_eq_2]
    rw [runTrace_snoc, htr_a1, hl1]; exact getMessageSentAt_attackerSend _ t
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
      (trDhRatchetState st msg.ratchetKey (runTraceMoves r₀ ms_a2).length).1.myIk msg.wire := by rw [hlen_a2]; exact hmac_eq
  have hrng2 : gamma interpretation S g' (randTerm (runTraceMoves r₀ ms_a2).length 32) = rngBytes := by rw [hlen_a2]; exact hrng_gam
  have hstep := matchedPrefix_step_decrypt_ratchet hmp2 hcur2 hst2 hmsg2 hparse hver hfind hlow
    hcons2 hspqr2 hpqSalt2 hmac2 hdec ht_gam hrng2 hpt_gam hwho2 ht_rep2
  have hms_eq : ms_a2 ++ [Move.decrypt p stateIdx (tr₀.length + 1) tr₀.length spqrMsgIdx false] =
      ms₁ ++ [.attackerSend pqSalt, .attackerSend t, .decrypt p stateIdx (tr₀.length + 1) tr₀.length spqrMsgIdx false] := by
    simp only [ms_a2, ms_a1, List.append_assoc, List.cons_append, List.nil_append]
  have hevs_eq : (acc ++ evs) ++ [.recv (wireWhisperTag :: body), .rng rngBytes, .accept outPt] =
      acc ++ (evs ++ [.recv (wireWhisperTag :: body)] ++ [.rng rngBytes] ++ [.accept outPt]) := by
    simp only [List.append_assoc, List.cons_append, List.nil_append]
  rw [← hms_eq, ← hevs_eq]; exact hstep

theorem evalRecvWireWithCoinsW_ratchetDH_inv_at
    (interpretation : ExternInterpretation) (body rngBytes : HwBytes) (r : StateAndMessage) (g_rw : RecvWireGhost)
    (m : SignalMessage) (newPqrState : HwBytes) (pqrKey : HKDF.Salt)
    (hwire : g_rw.wireBytes = wireWhisperTag :: body) (htry : SignalMessage.tryFrom protoSignalCodec body = .ok m)
    (hrc_none : ∀ rc ∈ g_rw.sess.state.receiverChains, rc.senderRatchetKey ≠ m.senderRatchetKey)
    (hrecv_spqr : (Symbolic.Swarm.TRREF.SpqrSemOf.spqrModelOf interpretation).recv
      g_rw.sess.state.pqRatchetState m.pqRatchet = .ok (newPqrState, pqrKey))
    (heval : PureRecvEval.pureEvalRecvWireWithCoinsW (cryptoOf' interpretation) (Proofs.libsignal.SR.interpW interpretation)
      (Symbolic.Swarm.TRREF.SpqrSemOf.spqrModelOf interpretation) g_rw
      (Symbolic.Swarm.CREF.CliPureRcv.TR.RecvDecStepPure.purePinCoins (some rngBytes)) = some (r.state, r.message)) :
    ∃ (role : Role) (remIk : IdentityKey) (ck ck_adv ck_next : ChainKey)
      (r1 r_adv r2 : RatchetState) (mkGen : MessageKeyGenerator) (st' : SessionState (List (BitVec 8))),
      Role.ofWho g_rw.who = some role ∧ g_rw.sess.state.version.toNat = m.messageVersion.toNat ∧
      g_rw.sess.state.remoteIdentity = some remIk ∧
      (Proofs.libsignal.RngG.R3.ratchetStateOf g_rw.sess.state).findReceiverChainKey m.senderRatchetKey = .ok none ∧
      Mut.exec (RatchetState.dhRatchetStep (cryptoOf' interpretation) m.senderRatchetKey (Symbolic.Swarm.CREF.CliPureRcv.TR.RecvDecStepPure.purePinCoins (some rngBytes)))
        (Proofs.libsignal.RngG.R3.ratchetStateOf g_rw.sess.state) = (.ok ck, r1) ∧
      ¬ (m.counter < ck.index) ∧ (m.counter - ck.index).toNat ≤ r1.maxForwardJumps ∧
      Mut.exec (RatchetState.advanceChain (cryptoOf' interpretation).F m.senderRatchetKey m.counter
        (m.counter - ck.index).toNat ck) r1 = (.ok ck_adv, r_adv) ∧
      ck_adv.nextChainKey (cryptoOf' interpretation).F = .ok ck_next ∧
      Mut.exec (RatchetState.setReceiverChainKey m.senderRatchetKey ck_next) r_adv = (.ok (), r2) ∧
      mkGen = ck_adv.messageKeys (cryptoOf' interpretation).F ∧
      m.verifyMacWithAddresses (cryptoOf' interpretation).F
        (PureRecvEval.pureSerializeRole role.peer role) remIk g_rw.sess.state.localIdentity
        (mkGen.generateKeys (cryptoOf' interpretation).F pqrKey).macKey = true ∧
      (Proofs.libsignal.SR.interpW interpretation).dec
        (mkGen.generateKeys (cryptoOf' interpretation).F pqrKey).cipherKey
        (mkGen.generateKeys (cryptoOf' interpretation).F pqrKey).iv m.ciphertext = some r.message ∧
      st' = { g_rw.sess.state with
        rootKey := r2.rootKey, previousCounter := r2.previousCounter, senderChain := r2.senderChain,
        receiverChains := r2.receiverChains, pqRatchetState := newPqrState, pendingPreKey := false } ∧
      r.state = CryptoVerification.E2E.Record.encodeRecord
        ⟨some { g_rw.sess with state := st', pendingPreKey := none, pendingKyberPreKey := none }⟩ := by
  unfold PureRecvEval.pureEvalRecvWireWithCoinsW at heval
  rw [hwire] at heval; simp only [wireWhisperTag] at heval; rw [htry] at heval; dsimp only at heval
  rcases hrole : Role.ofWho g_rw.who with _ | role; · simp [evalOpen, hrole] at heval
  have hopen : evalOpen g_rw.who g_rw.sess = some (role, g_rw.sess) := by simp [evalOpen, hrole]
  rw [hopen] at heval; dsimp only at heval
  rcases hres : (messageDecryptSignalW (cryptoOf' interpretation) (Proofs.libsignal.SR.interpW interpretation)
      (Symbolic.Swarm.TRREF.GrowthRecordPure.pureSpqr (Symbolic.Swarm.TRREF.SpqrSemOf.spqrModelOf interpretation)) PureRecvEval.pureSerializeRole
      (inMemAnswers g_rw.sess) m role.peer role (Symbolic.Swarm.CREF.CliPureRcv.TR.RecvDecStepPure.purePinCoins (some rngBytes))) with ⟨res, calls⟩
  rw [hres] at heval; dsimp only at heval; rcases res with e | ptB; · simp at heval
  simp only [Option.some.injEq, Prod.mk.injEq] at heval; obtain ⟨hst_enc, hpt⟩ := heval; subst hpt
  have h1 : (messageDecryptSignalW (cryptoOf' interpretation) (Proofs.libsignal.SR.interpW interpretation)
      (Symbolic.Swarm.TRREF.GrowthRecordPure.pureSpqr (Symbolic.Swarm.TRREF.SpqrSemOf.spqrModelOf interpretation)) PureRecvEval.pureSerializeRole
      (inMemAnswers g_rw.sess) m role.peer role (Symbolic.Swarm.CREF.CliPureRcv.TR.RecvDecStepPure.purePinCoins (some rngBytes))).1 = .ok r.message := by rw [hres]
  obtain ⟨st', hdec, _hrid, hstore⟩ :=
    PureRecvEval.storedSession_of_decryptOk (cryptoOf' interpretation)
      (Proofs.libsignal.SR.interpW interpretation)
      (Symbolic.Swarm.TRREF.GrowthRecordPure.pureSpqr (Symbolic.Swarm.TRREF.SpqrSemOf.spqrModelOf interpretation)) PureRecvEval.pureSerializeRole m
      role.peer role (Symbolic.Swarm.CREF.CliPureRcv.TR.RecvDecStepPure.purePinCoins (some rngBytes)) g_rw.sess r.message h1
  have hcalls2 : (messageDecryptSignalW (cryptoOf' interpretation) (Proofs.libsignal.SR.interpW interpretation)
      (Symbolic.Swarm.TRREF.GrowthRecordPure.pureSpqr (Symbolic.Swarm.TRREF.SpqrSemOf.spqrModelOf interpretation)) PureRecvEval.pureSerializeRole
      (inMemAnswers g_rw.sess) m role.peer role (Symbolic.Swarm.CREF.CliPureRcv.TR.RecvDecStepPure.purePinCoins (some rngBytes))).2 = calls := by rw [hres]
  rw [hcalls2] at hstore
  obtain ⟨remIk, r2, mkGen, newPqrState', pqrKey', hVer, hRem, hSpqr', hDec, hSt', hBr⟩ := Proofs.libsignal.RngG.R3.decryptW_ok_branch hdec
  have hspqr_eq : (Symbolic.Swarm.TRREF.GrowthRecordPure.pureSpqr (Symbolic.Swarm.TRREF.SpqrSemOf.spqrModelOf interpretation)).recv
      g_rw.sess.state.pqRatchetState m.pqRatchet =
      (Symbolic.Swarm.TRREF.SpqrSemOf.spqrModelOf interpretation).recv g_rw.sess.state.pqRatchetState m.pqRatchet := rfl
  rw [hspqr_eq, hrecv_spqr] at hSpqr'; simp only [Except.ok.injEq, Prod.mk.injEq] at hSpqr'; obtain ⟨rfl, rfl⟩ := hSpqr'
  cases hBr with
  | skipped ck' hFind _hLt _hTake _hMac =>
    obtain ⟨ci', rc', _hci', hrc', hsrk', _hck'⟩ := Proofs.libsignal.RngG.CliPure.R3.findReceiverChainKey_ok_some _ _ _ hFind
    exact absurd hsrk' (hrc_none rc' (List.mem_of_getElem? hrc'))
  | existing ck' _ck_adv _ck_next _r_adv hFind _hNotLt _hJump _hAdv _hNext _hSet _hMkGen _hMac =>
    obtain ⟨ci', rc', _hci', hrc', hsrk', _hck'⟩ := Proofs.libsignal.RngG.CliPure.R3.findReceiverChainKey_ok_some _ _ _ hFind
    exact absurd hsrk' (hrc_none rc' (List.mem_of_getElem? hrc'))
  | ratchet ck ck_adv ck_next r1 r_adv hFind hDh hNotLt hJump hAdv hNext hSet hMkGen hMac =>
    exact ⟨role, remIk, ck, ck_adv, ck_next, r1, r_adv, r2, mkGen, st',
      rfl, hVer, hRem, hFind, hDh, hNotLt, hJump, hAdv, hNext, hSet, hMkGen, hMac, hDec, hSt',
      by rw [← hst_enc, hstore]⟩

unseal DY.Bytes in
private instance (interpretation : ExternInterpretation) (S : OpaqueSymbolSemantics) (g : Ghost) :
    DY.Bytes.SubFunction (concretizeRandom g) (concretizeAll interpretation S g) :=
  @DY.Bytes.SubFunction.mk _ _ _ _ _ _ _ ⟨fun _ _ => by
    simp only [concretizeAll, allFuns, Symbolic.DYBridge.DY.Bytes.PartialFunction.combine_eq]; rfl⟩

theorem gamma_randTerm32_at (interpretation : ExternInterpretation) (S : OpaqueSymbolSemantics) (g : Ghost) (idx : Nat) :
    gamma interpretation S g (randTerm idx 32) = g.σ idx 32 := by
  unfold gamma gamma' randTerm
  show ((({ timestamp := idx, size := 32 } : DY.Random.Random DY.Bytes).pack).rec (concretizeAll interpretation S g)).bytes = _
  rw [DY.Bytes.rec_eq (concretizeRandom g) (concretizeAll interpretation S g)]; rfl

unseal DY.Bytes in
theorem shape_randTerm32_at (interpretation : ExternInterpretation) (S : OpaqueSymbolSemantics) (g : Ghost) (idx : Nat) :
    (gamma' interpretation S g (randTerm idx 32)).shape = randTerm idx 32 := by
  unfold gamma' randTerm
  show ((({ timestamp := idx, size := 32 } : DY.Random.Random DY.Bytes).pack).rec (concretizeAll interpretation S g)).shape = _
  rw [DY.Bytes.rec_eq (concretizeRandom g) (concretizeAll interpretation S g)]; rfl

theorem kemEncap_snd_eq_of_alice_bob
    (interpretation : ExternInterpretation) (S : OpaqueSymbolSemantics) (g : Ghost)
    {T : ExecTrace} (hreach : T.Reachable DY.Libsignal.Composed.reachability)
    (hσ32 : ∀ t, Symbolic.Swarm.COMPOSED.CompInv.AliceSlot T t → (g.σ (t + 1) 32).length = 32)
    {pA pB pB' pA' : Participant}
    {ikA ikB spk pqpk ek ct ikB' ikA' spk' pqpk' ek' ct' pk₁ e₁ pk₂ e₂ : DY.Bytes}
    {opk opk' : Option DY.Bytes}
    {keys keys' : DY.Libsignal.PQXDH.HandshakeKeys} {jA jB : Nat}
    (hevA : T.EventLoggedAt (DY.Libsignal.PQXDH.PQXDHEvent.AliceDone pA pB ikA ikB spk pqpk opk ek ct keys) jA)
    (hevB : T.EventLoggedAt (DY.Libsignal.PQXDH.PQXDHEvent.BobDone pB' pA' ikB' ikA' spk' pqpk' opk' ek' ct' keys') jB)
    (hct₁ : ct = (DY.PQKem.kemEncap pk₁ e₁).1)
    (hct₂ : ct' = (DY.PQKem.kemEncap pk₂ e₂).1)
    (hsh : (gamma' interpretation S g (DY.PQKem.kemEncap pk₁ e₁).2).shape =
      (gamma' interpretation S g (DY.PQKem.kemEncap pk₂ e₂).2).shape) :
    (DY.PQKem.kemEncap pk₁ e₁).2 = (DY.PQKem.kemEncap pk₂ e₂).2 := by
  have hinv := Symbolic.Swarm.COMPOSED.CompInv.spqrInv_of_reachable T hreach
  obtain ⟨t, sA, rfl, hSlot, _, _, _, hAgree, _⟩ :=
    hinv.aliceDone pA pB ikA ikB spk pqpk opk ek ct keys jA hevA
  have hct_alice : ct = (DY.PQKem.kemEncap pqpk (randTerm (t + 1) 32)).1 :=
    congrArg Prod.fst hAgree
  obtain ⟨rfl, rfl⟩ := Stage1Kyber.kemEncap_fst_inj (hct₁.symm.trans hct_alice)
  have h32 : (gamma interpretation S g (randTerm (t + 1) 32)).length = 32 := by
    rw [gamma_randTerm32_at]; exact hσ32 t hSlot
  obtain ⟨pk₂', e₂', heq₂, _, _, hsh_e₂⟩ :=
    Stage1Kyber.eq_kemSS_of_shape_eq_kemSS_len32 interpretation S g h32 hsh.symm
  obtain ⟨rfl, rfl⟩ := Stage1Kyber.kemEncap_snd_inj heq₂
  rw [shape_randTerm32_at] at hsh_e₂
  have he₂_eq : e₂ = randTerm (t + 1) 32 :=
    (Stage1Kyber.shape_eq_randTerm_iff interpretation S g e₂ (by omega)).mp hsh_e₂
  subst he₂_eq
  have hctB_ak : (DY.PQKem.kemEncap pk₂ (randTerm (t + 1) 32)).1.AttackerKnows T := by
    rw [← hct₂]
    exact (Symbolic.Swarm.CREF.TR.G1.Spine.bobDone_ct_pqpk_attackerKnows_of_reachable hreach hevB).1
  rcases Symbolic.Swarm.CREF.TR.G1.Spine.kemEncap_fst_attackerKnows_inv hreach hctB_ak with
    hcoins_ak | ⟨t', a', b', ikA'', ikB'', spk'', pqpk'', opk'', ek'', ct'', keys'', hevA', rfl, hrnd_eq⟩
  · exact False.elim (Symbolic.Swarm.COMPOSED.CompInv.not_pub_coins_of_spqrInv hinv hSlot
      (Symbolic.Swarm.COMPOSED.CompInv.pub_of_knows hinv hcoins_ak))
  · have ht_eq : t + 1 = t' + 1 := (Stage1Kyber.randTerm_inj hrnd_eq).1
    have ht_eq' : t' + 5 = t + 5 := by omega
    rw [ht_eq'] at hevA'
    have hev_eq := Symbolic.Swarm.COMPOSED.CompInv.BundleVerifyHelpers.evAt_unique hevA hevA'
    injection hev_eq with _ _ _ _ _ hpqpk_eq
    subst hpqpk_eq; rfl

private theorem kemLeaf_eq_of_alice_bob
    (interpretation : ExternInterpretation) (S : OpaqueSymbolSemantics) (g : Ghost)
    {T : ExecTrace} (hreach : T.Reachable DY.Libsignal.Composed.reachability)
    (hσ32 : ∀ t, Symbolic.Swarm.COMPOSED.CompInv.AliceSlot T t → (g.σ (t + 1) 32).length = 32)
    {pA pB pB' pA' : Participant}
    {ikA ikB spk pqpk ek ct ikB' ikA' spk' pqpk' ek' ct' ss₁ ss₂ aA bA cA : DY.Bytes}
    {opk opk' dA : Option DY.Bytes}
    {keys keys' : DY.Libsignal.PQXDH.HandshakeKeys} {jA jB : Nat}
    (hevA : T.EventLoggedAt (DY.Libsignal.PQXDH.PQXDHEvent.AliceDone pA pB ikA ikB spk pqpk opk ek ct keys) jA)
    (hevB : T.EventLoggedAt (DY.Libsignal.PQXDH.PQXDHEvent.BobDone pB' pA' ikB' ikA' spk' pqpk' opk' ek' ct' keys') jB)
    (hct₁ : (∃ pk₁ e₁, ct = (DY.PQKem.kemEncap pk₁ e₁).1 ∧ ss₁ = (DY.PQKem.kemEncap pk₁ e₁).2) ∨
      (∃ sk₁, ss₁ = DY.PQKem.kemRejKey sk₁ ct))
    (hct₂ : (∃ pk₂ e₂, ct' = (DY.PQKem.kemEncap pk₂ e₂).1 ∧ ss₂ = (DY.PQKem.kemEncap pk₂ e₂).2) ∨
      (∃ sk₂, ss₂ = DY.PQKem.kemRejKey sk₂ ct'))
    (hkeysA : keys = DY.Libsignal.PQXDH.pqxdhKdf (DY.Libsignal.PQXDH.pqxdhIkm aA bA cA dA ss₁))
    (hsh : (gamma' interpretation S g ss₁).shape = (gamma' interpretation S g ss₂).shape) :
    ss₁ = ss₂ := by
  have hinv := Symbolic.Swarm.COMPOSED.CompInv.spqrInv_of_reachable T hreach
  obtain ⟨t, sA, rfl, hSlot, _, _, _, hAgree, _⟩ :=
    hinv.aliceDone pA pB ikA ikB spk pqpk opk ek ct keys jA hevA
  have hkeys_alice : ∃ (a' b' c' : DY.Bytes) (d' : Option DY.Bytes),
      keys = DY.Libsignal.PQXDH.pqxdhKdf (DY.Libsignal.PQXDH.pqxdhIkm a' b' c' d'
        (DY.PQKem.kemEncap pqpk (randTerm (t + 1) 32)).2) := by
    change (ct, keys) = DY.Libsignal.PQXDH.aliceAgreement sA (randTerm t 32) ikB spk pqpk opk
      (randTerm (t + 1) 32) at hAgree
    rcases hk : DY.PQKem.kemEncap pqpk (randTerm (t + 1) 32) with ⟨c₀, s₀⟩
    unfold DY.Libsignal.PQXDH.aliceAgreement at hAgree
    rw [hk] at hAgree
    exact ⟨_, _, _, _, (Prod.mk.inj hAgree).2⟩
  obtain ⟨a', b', c', d', hkeys_alice⟩ := hkeys_alice
  have h32 : (gamma interpretation S g (randTerm (t + 1) 32)).length = 32 := by
    rw [gamma_randTerm32_at]; exact hσ32 t hSlot
  rcases hct₁ with ⟨pk₁, e₁, hct₁', rfl⟩ | ⟨sk₁, rfl⟩
  · rcases hct₂ with ⟨pk₂, e₂, hct₂', rfl⟩ | ⟨sk₂, rfl⟩
    · exact kemEncap_snd_eq_of_alice_bob interpretation S g hreach hσ32 hevA hevB hct₁' hct₂' hsh
    · exfalso
      have hct_alice : ct = (DY.PQKem.kemEncap pqpk (randTerm (t + 1) 32)).1 :=
        congrArg Prod.fst hAgree
      obtain ⟨rfl, rfl⟩ := Stage1Kyber.kemEncap_fst_inj (hct₁'.symm.trans hct_alice)
      obtain ⟨pk', e', heq, _⟩ :=
        Stage1Kyber.eq_kemSS_of_shape_eq_kemSS_len32 interpretation S g h32 hsh.symm
      have hnone := (Stage1Kyber.view?_kemRejKey_disjoint sk₂ ct').2.2.2.2.2.2.2.2.2.1
      rw [heq, Stage1Kyber.kemEncap_snd_eq_pack, Stage1Kyber.view_kemSS_pack] at hnone
      cases hnone
  · exfalso
    have hikm_eq : _ = _ := (Symbolic.Swarm.CREF.TR.G1.kdfExtract_injective
      (Symbolic.Swarm.CREF.TR.G1.kdfExtract_injective (congrArg DY.Libsignal.PQXDH.HandshakeKeys.rk
        (hkeysA.symm.trans hkeys_alice))).1).2
    have hsh_ikm := congrArg (fun z => (gamma' interpretation S g z).shape) hikm_eq
    unfold DY.Libsignal.PQXDH.pqxdhIkm at hsh_ikm
    obtain ⟨_, h1⟩ := Symbolic.Swarm.CREF.TR.G1.ShapeModKem.shape_concat_inj interpretation S g hsh_ikm
    obtain ⟨_, h2⟩ := Symbolic.Swarm.CREF.TR.G1.ShapeModKem.shape_concat_inj interpretation S g h1
    obtain ⟨_, h3⟩ := Symbolic.Swarm.CREF.TR.G1.ShapeModKem.shape_concat_inj interpretation S g h2
    obtain ⟨_, h4⟩ := Symbolic.Swarm.CREF.TR.G1.ShapeModKem.shape_concat_inj interpretation S g h3
    have hsh_ss : (gamma' interpretation S g (DY.PQKem.kemRejKey sk₁ ct)).shape =
        (gamma' interpretation S g (DY.PQKem.kemEncap pqpk (randTerm (t + 1) 32)).2).shape := by
      revert h4
      cases dA <;> cases d' <;> intro h4
      · exact h4
      · exact False.elim (Symbolic.Swarm.CREF.TR.G1.ShapeModKem.shape_kemLeaf_ne_concat
          interpretation S g (.inr ⟨sk₁, ct, rfl⟩) h4)
      · exact False.elim (Symbolic.Swarm.CREF.TR.G1.ShapeModKem.shape_kemLeaf_ne_concat
          interpretation S g (.inl ⟨_, _, rfl⟩) h4.symm)
      · exact (Symbolic.Swarm.CREF.TR.G1.ShapeModKem.shape_concat_inj interpretation S g h4).2
    obtain ⟨pk', e', heq, _⟩ :=
      Stage1Kyber.eq_kemSS_of_shape_eq_kemSS_len32 interpretation S g h32 hsh_ss
    have hnone := (Stage1Kyber.view?_kemRejKey_disjoint sk₁ ct).2.2.2.2.2.2.2.2.2.1
    rw [heq, Stage1Kyber.kemEncap_snd_eq_pack, Stage1Kyber.view_kemSS_pack] at hnone
    cases hnone

theorem ikm_eq_of_peel_at
    (interpretation : ExternInterpretation) (S : OpaqueSymbolSemantics) (g : Ghost)
    {T : ExecTrace} (hreach : T.Reachable DY.Libsignal.Composed.reachability)
    (hσ32 : ∀ t, Symbolic.Swarm.COMPOSED.CompInv.AliceSlot T t → (g.σ (t + 1) 32).length = 32)
    {u₀ v₀ : DY.Bytes}
    (hhole : ∀ d₁ d₂ : DY.Bytes,
      Symbolic.Swarm.CREF.TR.G1.SpineIkm.Peel u₀ v₀ d₁ d₂ →
      Symbolic.Swarm.CREF.TR.G1.SpineIkm.DhHole d₁ →
      Symbolic.Swarm.CREF.TR.G1.SpineIkm.DhHole d₂ →
      (gamma' interpretation S g d₁).shape = (gamma' interpretation S g d₂).shape → d₁ = d₂) :
    ∀ (c c' : Bool) (m₁ m₂ : DY.Bytes),
      Symbolic.Swarm.CREF.TR.G1.SpineIkm.PeelKdf u₀ v₀ m₁ m₂ →
      Symbolic.Swarm.CREF.TR.G1.Spine.LoggedIkmR T c m₁ →
      Symbolic.Swarm.CREF.TR.G1.Spine.LoggedIkmR T c' m₂ →
      (c ^^ c') = true →
      (gamma' interpretation S g m₁).shape = (gamma' interpretation S g m₂).shape → m₁ = m₂ := by
  intro c c' m₁ m₂ hP hm₁ hm₂ hp h
  have hpeel : ∀ {ss₁ a₁ b₁ c₁ : DY.Bytes} {d₁ : Option DY.Bytes}
      {ss₂ a₂ b₂ c₂ : DY.Bytes} {d₂ : Option DY.Bytes},
      Symbolic.Swarm.CREF.TR.G1.ShapeModKem.KemLeaf ss₁ →
      Symbolic.Swarm.CREF.TR.G1.ShapeModKem.KemLeaf ss₂ →
      Symbolic.Swarm.CREF.TR.G1.SpineIkm.PeelKdf u₀ v₀
        (DY.Libsignal.PQXDH.pqxdhIkm a₁ b₁ c₁ d₁ ss₁)
        (DY.Libsignal.PQXDH.pqxdhIkm a₂ b₂ c₂ d₂ ss₂) →
      Symbolic.Swarm.CREF.TR.G1.SpineIkm.DhHole a₁ →
      Symbolic.Swarm.CREF.TR.G1.SpineIkm.DhHole b₁ →
      Symbolic.Swarm.CREF.TR.G1.SpineIkm.DhHole c₁ →
      (∀ x, d₁ = some x → Symbolic.Swarm.CREF.TR.G1.SpineIkm.DhHole x) →
      Symbolic.Swarm.CREF.TR.G1.SpineIkm.DhHole a₂ →
      Symbolic.Swarm.CREF.TR.G1.SpineIkm.DhHole b₂ →
      Symbolic.Swarm.CREF.TR.G1.SpineIkm.DhHole c₂ →
      (∀ x, d₂ = some x → Symbolic.Swarm.CREF.TR.G1.SpineIkm.DhHole x) →
      ((gamma' interpretation S g ss₁).shape =
        (gamma' interpretation S g ss₂).shape → ss₁ = ss₂) →
      (gamma' interpretation S g
        (DY.Libsignal.PQXDH.pqxdhIkm a₁ b₁ c₁ d₁ ss₁)).shape =
      (gamma' interpretation S g
        (DY.Libsignal.PQXDH.pqxdhIkm a₂ b₂ c₂ d₂ ss₂)).shape →
      DY.Libsignal.PQXDH.pqxdhIkm a₁ b₁ c₁ d₁ ss₁ =
        DY.Libsignal.PQXDH.pqxdhIkm a₂ b₂ c₂ d₂ ss₂ := by
    intro ss₁ a₁ b₁ c₁ d₁ ss₂ a₂ b₂ c₂ d₂ hk₁ hk₂ hP' ha₁ hb₁ hc₁ hd₁ ha₂ hb₂ hc₂ hd₂ hleaf hsh
    unfold DY.Libsignal.PQXDH.pqxdhIkm at hsh
    obtain ⟨_, h1⟩ := Symbolic.Swarm.CREF.TR.G1.ShapeModKem.shape_concat_inj interpretation S g hsh
    obtain ⟨sha, h2⟩ := Symbolic.Swarm.CREF.TR.G1.ShapeModKem.shape_concat_inj interpretation S g h1
    obtain ⟨shb, h3⟩ := Symbolic.Swarm.CREF.TR.G1.ShapeModKem.shape_concat_inj interpretation S g h2
    obtain ⟨she, h4⟩ := Symbolic.Swarm.CREF.TR.G1.ShapeModKem.shape_concat_inj interpretation S g h3
    have ha : a₁ = a₂ := hhole _ _ (.ikmDh1 hP'.peel) ha₁ ha₂ sha
    have hb : b₁ = b₂ := hhole _ _ (.ikmDh2 hP'.peel) hb₁ hb₂ shb
    have he : c₁ = c₂ := hhole _ _ (.ikmDh3 hP'.peel) hc₁ hc₂ she
    subst ha hb he
    cases d₁ with
    | none =>
      cases d₂ with
      | none => rw [hleaf h4]
      | some v₂ =>
        exact False.elim (Symbolic.Swarm.CREF.TR.G1.ShapeModKem.shape_kemLeaf_ne_concat
          interpretation S g hk₁ h4)
    | some v₁ =>
      cases d₂ with
      | none =>
        exact False.elim (Symbolic.Swarm.CREF.TR.G1.ShapeModKem.shape_kemLeaf_ne_concat
          interpretation S g hk₂ h4.symm)
      | some v₂ =>
        obtain ⟨shd, hss⟩ := Symbolic.Swarm.CREF.TR.G1.ShapeModKem.shape_concat_inj interpretation S g h4
        have hd : v₁ = v₂ := hhole _ _ (.ikmDh4 hP'.peel) (hd₁ v₁ rfl) (hd₂ v₂ rfl) shd
        subst hd
        rw [hleaf hss]
  have hk_of : ∀ {ct s : DY.Bytes},
      ((∃ pk e, ct = (DY.PQKem.kemEncap pk e).1 ∧ s = (DY.PQKem.kemEncap pk e).2) ∨
        ∃ sk, s = DY.PQKem.kemRejKey sk ct) →
      Symbolic.Swarm.CREF.TR.G1.ShapeModKem.KemLeaf s := by
    rintro _ _ (⟨pk, e, _, rfl⟩ | ⟨sk, rfl⟩)
    · exact .inl ⟨pk, e, rfl⟩
    · exact .inr ⟨sk, _, rfl⟩
  cases c <;> cases c'
  · cases hp
  · obtain ⟨evA, ⟨jA, ⟨evA'⟩, hatA, rfl⟩, hdA⟩ := hm₁
    obtain ⟨evB, ⟨jB, ⟨evB'⟩, hatB, rfl⟩, hdB⟩ := hm₂
    cases evA' <;> try exact hdA.elim
    cases evB' <;> try exact hdB.elim
    obtain ⟨ss₁, a₁, b₁, c₁, d₁, hct₁, rfl, hkeysA, ha₁, hb₁, hc₁, hd₁⟩ := hdA
    obtain ⟨ss₂, a₂, b₂, c₂, d₂, hct₂, rfl, _, ha₂, hb₂, hc₂, hd₂⟩ := hdB
    exact hpeel (hk_of hct₁) (hk_of hct₂) hP ha₁ hb₁ hc₁ hd₁ ha₂ hb₂ hc₂ hd₂
      (kemLeaf_eq_of_alice_bob interpretation S g hreach hσ32
        (by rwa [Symbolic.DYBridge.DY.Trace.EventLoggedAt_eq_1])
        (by rwa [Symbolic.DYBridge.DY.Trace.EventLoggedAt_eq_1]) hct₁ hct₂ hkeysA) h
  · obtain ⟨evB, ⟨jB, ⟨evB'⟩, hatB, rfl⟩, hdB⟩ := hm₁
    obtain ⟨evA, ⟨jA, ⟨evA'⟩, hatA, rfl⟩, hdA⟩ := hm₂
    cases evB' <;> try exact hdB.elim
    cases evA' <;> try exact hdA.elim
    obtain ⟨ss₁, a₁, b₁, c₁, d₁, hct₁, rfl, _, ha₁, hb₁, hc₁, hd₁⟩ := hdB
    obtain ⟨ss₂, a₂, b₂, c₂, d₂, hct₂, rfl, hkeysA, ha₂, hb₂, hc₂, hd₂⟩ := hdA
    exact hpeel (hk_of hct₁) (hk_of hct₂) hP ha₁ hb₁ hc₁ hd₁ ha₂ hb₂ hc₂ hd₂
      (fun hss => (kemLeaf_eq_of_alice_bob interpretation S g hreach hσ32
        (by rwa [Symbolic.DYBridge.DY.Trace.EventLoggedAt_eq_1])
        (by rwa [Symbolic.DYBridge.DY.Trace.EventLoggedAt_eq_1]) hct₂ hct₁ hkeysA hss.symm).symm) h
  · cases hp

theorem honestSkelUniq_of_reachable_compat
    (interpretation : ExternInterpretation) (r : ProtocolSetup) (S : OpaqueSymbolSemantics) (g : Ghost) (ms : List Move)
    (hreach : (runTraceMoves r ms).Reachable reachability)
    (hσ32 : ∀ t, Symbolic.Swarm.COMPOSED.CompInv.AliceSlot (runTraceMoves r ms) t → (g.σ (t + 1) 32).length = 32)
    {st_s st₀ : TRState}
    (hst_s : st_s ∈ availableStates r (runTraceMoves r ms))
    (hst₀ : st₀ ∈ availableStates r (runTraceMoves r ms))
    {msg₀ : TRSignalMsg} {mkSeed : DY.Bytes}
    (hseed : recvSeed st₀ msg₀ = some mkSeed)
    (hshape : (gamma' interpretation S g (kdfCk st_s.cks).2).shape =
      (gamma' interpretation S g mkSeed).shape) :
    (kdfCk st_s.cks).2 = mkSeed :=
  let hhole := fun d₁ d₂ hP hd₁ (_ : Symbolic.Swarm.CREF.TR.G1.SpineIkm.DhHole d₂)
      (_ : (gamma' interpretation S g d₁).shape = (gamma' interpretation S g d₂).shape) =>
    Symbolic.Swarm.CREF.TR.G1.Spine.hdh_of_spineRk interpretation S g
      (Symbolic.Swarm.CREF.TR.G1.Spine.ikAt_spkAt_false (runTraceMoves r ms))
      (Symbolic.Swarm.CREF.TR.G1.Spine.ekAt_ikAt_false (runTraceMoves r ms))
      (Symbolic.Swarm.CREF.TR.G1.Spine.ekAt_spkAt_false (runTraceMoves r ms))
      (Symbolic.Swarm.CREF.TR.G1.Spine.ekAt_opkAt_false (runTraceMoves r ms))
      (fun _ _ h => Symbolic.Swarm.CREF.TR.G1.Spine.loggedIkmRk_roleHoles h)
      rfl
      (Symbolic.Swarm.CREF.TR.G1.Spine.spineRk_send_runTrace hst_s)
      (Symbolic.Swarm.CREF.TR.G1.Spine.spineRk_recvSeed_runTrace hst₀ hseed)
      hshape d₁ d₂ hP hd₁
  Symbolic.Swarm.CREF.TR.G1.Spine.seed_eq_of_shape_eq_peel interpretation r S g ms hst_s hst₀ hseed
    hhole (ikm_eq_of_peel_at interpretation S g hreach hσ32 hhole) hshape

section AliceCoinsLen32

open Symbolic.Swarm.CREF.XplSteps

def NoAliceDoneFrom (n : Nat) (t : ExecTrace) : Prop :=
  ∀ i ev, n ≤ i → t.getEventAt DY.Libsignal.PQXDH.PQXDHEvent i = some ev →
    DY.Libsignal.Composed.Refinement.isAliceDone ev = false

def NoAliceDone {α : Type} (x : Traceful α) : Prop :=
  ∀ tr, NoAliceDoneFrom tr.length (x.run tr).2.val

theorem noAliceDone_of_quiet {α : Type} {x : Traceful α} (hx : XQuiet x) : NoAliceDone x := by
  intro tr i ev hi hev
  have hnone := (hx tr i hi).2.1
  simp only [Symbolic.DYBridge.DY.Trace.getEventAt_eq_1] at hev
  rw [hnone] at hev; cases hev

theorem noAliceDoneFrom_trans {n : Nat} {t t' : ExecTrace} (hle : t ≤ t')
    (h1 : NoAliceDoneFrom n t) (h2 : NoAliceDoneFrom t.length t') : NoAliceDoneFrom n t' := by
  intro i ev hi hev
  by_cases hlt : i < t.length
  · refine h1 i ev hi ?_
    simp only [Symbolic.DYBridge.DY.Trace.getEventAt_eq_1] at hev ⊢
    rwa [← xat?_le_eq hle hlt]
  · exact h2 i ev (by omega) hev

theorem noAliceDone_bind {α β : Type} {x : Traceful α} {f : α → Traceful β}
    (hx : NoAliceDone x) (hf : ∀ a, NoAliceDone (f a)) : NoAliceDone (x >>= f) := by
  intro tr
  rw [xrun_bind_snd]
  split
  · exact noAliceDoneFrom_trans (xrun_le _ _) (hx tr) (hf _ _)
  · exact hx tr

theorem noAliceDone_append {E : Type} [ExecTraceTypes.Has E] (tr : ExecTrace) (e : E)
    (h : ∀ x : DY.ProtocolEvent.ExecEntryT DY.Libsignal.PQXDH.PQXDHEvent,
      ((tr.append e).at? tr.length : Option (DY.ProtocolEvent.ExecEntryT DY.Libsignal.PQXDH.PQXDHEvent)) = some x →
      DY.Libsignal.Composed.Refinement.isAliceDone x.ev = false) :
    NoAliceDoneFrom tr.length (tr.append e) := by
  intro i ev hi hev
  have hlt : tr.length < (tr.append e).length := by
    simp only [Symbolic.DYBridge.DY.Trace.append_eq_1, Symbolic.DYBridge.DY.Trace.length_eq_2]; omega
  rcases Nat.lt_or_ge tr.length i with hgt | hle
  · have hn := (xnone_of_ge (t := tr.append e) (i := i)
      (by simp only [Symbolic.DYBridge.DY.Trace.append_eq_1, Symbolic.DYBridge.DY.Trace.length_eq_2]; omega)).2.1
    simp only [Symbolic.DYBridge.DY.Trace.getEventAt_eq_1] at hev; rw [hn] at hev; cases hev
  · obtain rfl : i = tr.length := by omega
    simp only [Symbolic.DYBridge.DY.Trace.getEventAt_eq_1] at hev
    rcases hx : ((tr.append e).at? tr.length :
        Option (DY.ProtocolEvent.ExecEntryT DY.Libsignal.PQXDH.PQXDHEvent)) with _ | x
    · rw [hx] at hev; cases hev
    · rw [hx] at hev; injection hev with hev_eq; subst hev_eq; exact h x hx

theorem NoAliceDoneFrom.elim {n : Nat} {t : ExecTrace} (h : NoAliceDoneFrom n t)
    {i : Nat} {ev : DY.Libsignal.PQXDH.PQXDHEvent} (hi : n ≤ i)
    (hev : t.getEventAt DY.Libsignal.PQXDH.PQXDHEvent i = some ev) :
    DY.Libsignal.Composed.Refinement.isAliceDone ev = false :=
  h i ev hi hev

attribute [irreducible] NoAliceDoneFrom

theorem noAliceDone_logEvent_pq (ev : DY.Libsignal.PQXDH.PQXDHEvent)
    (h : DY.Libsignal.Composed.Refinement.isAliceDone ev = false) :
    NoAliceDone (DY.ProtocolEvent.logEvent ev : Traceful Unit) := by
  intro tr
  simp only [Symbolic.DYBridge.DY.ProtocolEvent.logEvent_eq_1,
    Symbolic.DYBridge.DY.appendEntry_eq_1,
    Symbolic.DYBridge.DY.Traceful.mk_eq_1,
    Symbolic.DYBridge.DY.Traceful.run_eq_1]
  refine noAliceDone_append tr (⟨ev⟩ : DY.ProtocolEvent.ExecEntryT DY.Libsignal.PQXDH.PQXDHEvent) fun x hx => ?_
  rw [DY.Trace.at?_append] at hx; injection hx with hx'; cases hx'; exact h

theorem noAliceDone_logEvent_tr (ev : TREvent) :
    NoAliceDone (DY.ProtocolEvent.logEvent ev : Traceful Unit) := by
  intro tr
  simp only [Symbolic.DYBridge.DY.ProtocolEvent.logEvent_eq_1,
    Symbolic.DYBridge.DY.appendEntry_eq_1,
    Symbolic.DYBridge.DY.Traceful.mk_eq_1,
    Symbolic.DYBridge.DY.Traceful.run_eq_1]
  refine noAliceDone_append tr (⟨ev⟩ : DY.ProtocolEvent.ExecEntryT TREvent) fun x hx => ?_
  have hlt : tr.length < (tr.append (⟨ev⟩ : DY.ProtocolEvent.ExecEntryT TREvent)).length := by
    simp only [Symbolic.DYBridge.DY.Trace.append_eq_1, Symbolic.DYBridge.DY.Trace.length_eq_2]; omega
  simp only [DY.Trace.at?, hlt, ↓reduceDIte, xtrace_append_at_length] at hx; cases hx

theorem noAliceDone_logEvent_c (ev : DY.Libsignal.Composed.ComposedEvent) :
    NoAliceDone (DY.ProtocolEvent.logEvent ev : Traceful Unit) := by
  intro tr
  simp only [Symbolic.DYBridge.DY.ProtocolEvent.logEvent_eq_1,
    Symbolic.DYBridge.DY.appendEntry_eq_1,
    Symbolic.DYBridge.DY.Traceful.mk_eq_1,
    Symbolic.DYBridge.DY.Traceful.run_eq_1]
  refine noAliceDone_append tr (⟨ev⟩ : DY.ProtocolEvent.ExecEntryT DY.Libsignal.Composed.ComposedEvent) fun x hx => ?_
  have hlt : tr.length < (tr.append (⟨ev⟩ : DY.ProtocolEvent.ExecEntryT DY.Libsignal.Composed.ComposedEvent)).length := by
    simp only [Symbolic.DYBridge.DY.Trace.append_eq_1, Symbolic.DYBridge.DY.Trace.length_eq_2]; omega
  simp only [DY.Trace.at?, hlt, ↓reduceDIte, xtrace_append_at_length] at hx; cases hx

theorem noAliceDone_storeTR (p : Participant) (st : TRState) :
    NoAliceDone (DY.PersistentLocalState.storeLocalState p st) := by
  unfold NoAliceDone; intro tr
  simp only [Symbolic.DYBridge.DY.PersistentLocalState.storeLocalState_eq_1,
    Symbolic.DYBridge.DY.PersistentGlobalState.storeGlobalState_eq_1,
    Symbolic.DYBridge.DY.appendEntry_eq_1,
    DY.Traceful.run_mk]
  refine noAliceDone_append tr (⟨⟨p, st⟩⟩ : DY.PersistentGlobalState.State.ExecEntryT
      (DY.PersistentLocalState.LocalState TRState)) fun x hx => ?_
  have hlt : tr.length < (tr.append (⟨⟨p, st⟩⟩ : DY.PersistentGlobalState.State.ExecEntryT
      (DY.PersistentLocalState.LocalState TRState))).length := by
    simp only [Symbolic.DYBridge.DY.Trace.append_eq_1, Symbolic.DYBridge.DY.Trace.length_eq_2]; omega
  simp only [DY.Trace.at?, hlt, ↓reduceDIte, xtrace_append_at_length] at hx; cases hx

theorem noAliceDone_storePQ (p : Participant) (st : DY.Libsignal.PQXDH.PQXDHState) :
    NoAliceDone (DY.PersistentLocalState.storeLocalState p st) := by
  unfold NoAliceDone; intro tr
  simp only [Symbolic.DYBridge.DY.PersistentLocalState.storeLocalState_eq_1,
    Symbolic.DYBridge.DY.PersistentGlobalState.storeGlobalState_eq_1,
    Symbolic.DYBridge.DY.appendEntry_eq_1,
    DY.Traceful.run_mk]
  refine noAliceDone_append tr (⟨⟨p, st⟩⟩ : DY.PersistentGlobalState.State.ExecEntryT
      (DY.PersistentLocalState.LocalState DY.Libsignal.PQXDH.PQXDHState)) fun x hx => ?_
  have hlt : tr.length < (tr.append (⟨⟨p, st⟩⟩ : DY.PersistentGlobalState.State.ExecEntryT
      (DY.PersistentLocalState.LocalState DY.Libsignal.PQXDH.PQXDHState))).length := by
    simp only [Symbolic.DYBridge.DY.Trace.append_eq_1, Symbolic.DYBridge.DY.Trace.length_eq_2]; omega
  simp only [DY.Trace.at?, hlt, ↓reduceDIte, xtrace_append_at_length] at hx; cases hx

end AliceCoinsLen32
end Symbolic.Swarm.CREF.CliPureRcv.TR.RecvDecStepAtPure
