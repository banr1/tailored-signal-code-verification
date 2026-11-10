/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Symbolic.Proofs.Swarm.CREF.RecvWire.AcceptNewRecBasePure
import DY.Actions.ProtocolEvent
import DY.Trace.Basic
public import Symbolic.Proofs.Swarm.CREF.TR.RecvDecStepSkippedG1LeavesPure
import Symbolic.Proofs.Swarm.CREF.Cli.Rpk.RecvDecStepCommonPure
import Symbolic.Proofs.Swarm.CREF.Cli.Rpk.RecvDecStepNoRatchetPure
import Symbolic.Proofs.Swarm.CREF.Cli.Rpk.RecvDecStepRatchetDHaPure
import Symbolic.Proofs.Swarm.CREF.Initiate.InitRej
import Symbolic.Proofs.Swarm.CREF.ModelBridge
import Symbolic.Proofs.Swarm.CREF.Prelude
import Symbolic.Proofs.Swarm.CREF.TROpen
import Symbolic.Proofs.Swarm.CREF.TR.Leaks -- shake: keep
import Symbolic.Proofs.Swarm.CREF.TR.PQGamma -- shake: keep
import Symbolic.Proofs.Swarm.CREF.TR.PQModelRunNil -- shake: keep
import Symbolic.DYBridge.DY.Actions.ProtocolEvent
import Symbolic.DYBridge.DY.Trace.Basic

/-!
# DH-Ratchet Whisper Decrypt Tie Helpers

Trace equations, pure branch inversion, and `TRNsBound` / `PureTRRecordStateInv` step helpers for
DH-ratchet `Move.decrypt` steps.
-/

@[expose] public section

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

cref_hide_foreign_instances

namespace Symbolic.Swarm.CREF.CliPureRcv.TR.RecvDecStepTiePure
open Symbolic.Swarm.CREF.TR hiding at?_append_of_lt gamma_concat gamma_dhPk getLocalState_fst leValue_leBytes length_leBytes newRandoms_append_rnd p25519_lt p25519_pos runMoves_append runTrace_append runTrace_snoc runVis_append runVis_snoc run_bind_fst run_bind_snd uOf_leBytes uOf_lt
open Symbolic.Swarm.CREF Symbolic.Swarm.CREF.CliPure Symbolic.Swarm.CREF.CliPureRcv
open Symbolic.Swarm.CREF.CliPureRcv.RecvWirePure
open Symbolic.Swarm.CREF.CliPure.TR Symbolic.Swarm.CREF.CliPureRcv.TR
open Symbolic.Swarm.CREF.CliPure.TR.RecvDecStep hiding SpqrSem StEntry TREntry
open Symbolic.Swarm.CREF.CliPureRcv.TR.RecvDecStepPure

cref_open
cref_open_tr

open DY DY.Comparse DY.Literal DY.DiffieHellman DY.Libsignal
open DY.Libsignal.TripleRatchet (SessionInfo RecvChain findRecvChain setRecvChain consumeMessageKey
  maxForwardJumps computeMac messageVersion x25519LowOrder)
open DY.Libsignal.TripleRatchet
open DY.Libsignal.TripleRatchet.Refinement (wireWhisperTag)
open DY.Libsignal.HwEvents DY.Libsignal.Rust
open CryptoGames CryptoGames.HMAC CryptoGames.HKDF
open CryptoGames.LibsignalSession CryptoGames.LibsignalSessionApi
open CryptoVerification
open CryptoVerification.LibsignalTripleRatchet CryptoVerification.LibsignalProtoCodec
open CryptoVerification.E2E CryptoVerification.E2E.InMem CryptoVerification.E2E.Record CryptoVerification.E2E.RecordX
open CryptoVerification.E2E.Bin hiding RecordCanonical recordDeserializeOpenSpec encodeRecord
open CryptoVerification.E2E.Pqxdh.WireEntries
open CryptoVerification.E2E.Pqxdh.WireEntries.SymP3 hiding encodeRecord
open CryptoProofLib.Refinement (ExternInterpretation)
open Proofs.libsignal.RngG Proofs.libsignal.Hooks2 Proofs.libsignal.RngG.R3 Proofs.libsignal.RngG.CliPure.R3
open Proofs.libsignal.SR (messageDecryptSignalW)
open Symbolic.Swarm.CREF Symbolic.Swarm.CREF.CliPure Symbolic.Swarm.CREF.CliPureRcv
open Symbolic.Swarm.CREF.CliPure.TR Symbolic.Swarm.CREF.CliPureRcv.TR
open Symbolic.Swarm.CREF.TR.RecvDec (trDhRatchetState decRatchetPreTr decrypt_next_ratchet_eq
  trNsBound_of_append_stEntry)
open Symbolic.Swarm.TRREF.SpqrSemOf (spqrModelOf)

theorem a2b_skippedKeyUsedB_decRatchetPreTr
    (tr : ExecTrace) (me : Participant) (st1 : TRState) (pk key : DY.Bytes) (skIdx : Nat) :
    skippedKeyUsedB (decRatchetPreTr tr me st1 pk key) skIdx = skippedKeyUsedB tr skIdx := by
  unfold decRatchetPreTr
  rw [skippedKeyUsedB_append_trEntry_other_a2 _ _ (fun _ _ h => by cases h),
      skippedKeyUsedB_append_trEntry_other_a2 _ _ (fun _ _ h => by cases h),
      skippedKeyUsedB_append_non_tr_a2 _ _ rfl,
      skippedKeyUsedB_append_non_tr_a2 _ _ rfl]

theorem a2b_receiverKeyUsedB_decRatchetPreTr
    (tr : ExecTrace) (me : Participant) (st1 : TRState) (pk key : DY.Bytes)
    (s' : SessionInfo) (seed' : DY.Bytes) (cnt' : UInt32) (rIdx' : Nat) :
    receiverKeyUsedB (decRatchetPreTr tr me st1 pk key) s' seed' cnt' rIdx' =
      receiverKeyUsedB tr s' seed' cnt' rIdx' := by
  unfold decRatchetPreTr
  rw [receiverKeyUsedB_append_trEntry_other_a2 _ _ (fun _ _ _ _ _ _ h => by cases h),
      receiverKeyUsedB_append_trEntry_other_a2 _ _ (fun _ _ _ _ _ _ h => by cases h),
      receiverKeyUsedB_append_non_tr_a2 _ _ rfl,
      receiverKeyUsedB_append_non_tr_a2 _ _ rfl]

theorem a2b_eventLoggedAt_decRatchetPreTr_lt
    (tr : ExecTrace) (me : Participant) (st1 : TRState) (pk key : DY.Bytes)
    {ev : TREvent} {i : Nat} (hi : i < tr.length) :
    (decRatchetPreTr tr me st1 pk key).EventLoggedAt ev i ↔ tr.EventLoggedAt ev i := by
  simp only [Symbolic.DYBridge.DY.Trace.EventLoggedAt_eq_1]
  change ((decRatchetPreTr tr me st1 pk key).at? i : Option TREntry) = some ⟨ev⟩ ↔
    (tr.at? i : Option TREntry) = some ⟨ev⟩
  unfold decRatchetPreTr
  rw [at?_append_of_lt _ _ (by simp [Symbolic.DYBridge.DY.Trace.append_eq_1, Symbolic.DYBridge.DY.Trace.length_eq_1, Symbolic.DYBridge.DY.Trace.length_eq_2]; omega),
      at?_append_of_lt _ _ (by simp [Symbolic.DYBridge.DY.Trace.append_eq_1, Symbolic.DYBridge.DY.Trace.length_eq_1, Symbolic.DYBridge.DY.Trace.length_eq_2]; omega),
      at?_append_non_entry _ _ rfl,
      at?_append_non_entry _ _ rfl]

theorem a2b_hsk'_decTailTr_of_pre_tr
    {tr_pre : ExecTrace} {me : Participant} {stateIdx : Nat}
    {st1 : TRState} {c c' : RecvChain} {pk seed pqSalt ptTerm spqr' : DY.Bytes} {n : UInt32}
    {pk_k seed_k : DY.Bytes} {n_k : UInt32} {rIdx_k srcIdx_k skIdx_k : Nat}
    (hlog_pre : tr_pre.EventLoggedAt
      (TREvent.SkippedKeyStored (st1.sessionInfo me) pk_k n_k seed_k rIdx_k srcIdx_k) skIdx_k)
    (hsu_pre : !skippedKeyUsedB tr_pre skIdx_k)
    (hru_pre : !receiverKeyUsedB tr_pre (st1.sessionInfo me) seed_k n_k rIdx_k)
    (hlt_pre : skIdx_k < tr_pre.length)
    (hne_cnt : ¬ (seed = seed_k ∧ n = n_k ∧ c.rIdx = rIdx_k)) :
    (decTailTr tr_pre me stateIdx st1 c c' pk seed pqSalt ptTerm spqr' n).EventLoggedAt
      (TREvent.SkippedKeyStored (st1.sessionInfo me) pk_k n_k seed_k rIdx_k srcIdx_k) skIdx_k ∧
    !skippedKeyUsedB (decTailTr tr_pre me stateIdx st1 c c' pk seed pqSalt ptTerm spqr' n) skIdx_k ∧
    !receiverKeyUsedB (decTailTr tr_pre me stateIdx st1 c c' pk seed pqSalt ptTerm spqr' n)
      (st1.sessionInfo me) seed_k n_k rIdx_k := by
  refine ⟨?_, ?_, ?_⟩
  · rw [eventLoggedAt_decTailTr_lt _ _ _ _ _ _ _ _ _ _ _ _ hlt_pre]; exact hlog_pre
  · rw [skippedKeyUsedB_decTailTr]; exact hsu_pre
  · rw [receiverKeyUsedB_decTailTr]
    have hfalse : decide (st1.sessionInfo me = st1.sessionInfo me ∧ seed = seed_k ∧ n = n_k ∧ c.rIdx = rIdx_k) = false := by
      simp [hne_cnt]
    rw [hfalse, Bool.or_false]; exact hru_pre

theorem a2b_evalRecvWireWithCoinsW_ratchetDH_inv
    (interpretation : ExternInterpretation) (body rngBytes : HwBytes)
    (r : StateAndMessage) (g_rw : RecvWireGhost)
    (m : SignalMessage) (newPqrState : HwBytes) (pqrKey : HKDF.Salt)
    (hwire : g_rw.wireBytes = wireWhisperTag :: body)
    (htry : SignalMessage.tryFrom protoSignalCodec body = .ok m)
    (hrc_none : ∀ rc ∈ g_rw.sess.state.receiverChains, rc.senderRatchetKey ≠ m.senderRatchetKey)
    (hrecv_spqr : (Symbolic.Swarm.TRREF.SpqrSemOf.spqrModelOf interpretation).recv
      g_rw.sess.state.pqRatchetState m.pqRatchet = .ok (newPqrState, pqrKey))
    (heval : Symbolic.Swarm.CREF.CliPure.TR.PureRecvEval.pureEvalRecvWireWithCoinsW
      (cryptoOf' interpretation) (Proofs.libsignal.SR.interpW interpretation)
      (Symbolic.Swarm.TRREF.SpqrSemOf.spqrModelOf interpretation) g_rw
      (Symbolic.Swarm.CREF.CliPureRcv.TR.RecvDecStepPure.purePinCoins (some rngBytes)) = some (r.state, r.message)) :
    ∃ (role : Role) (remIk : IdentityKey) (ck ck_adv ck_next : ChainKey)
      (r1 r_adv r2 : RatchetState) (mkGen : MessageKeyGenerator)
      (st' : SessionState (List (BitVec 8))),
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
        (Symbolic.Swarm.CREF.CliPure.TR.PureRecvEval.pureSerializeRole role.peer role) remIk g_rw.sess.state.localIdentity
        (mkGen.generateKeys (cryptoOf' interpretation).F pqrKey).macKey = true ∧
      (Proofs.libsignal.SR.interpW interpretation).dec
        (mkGen.generateKeys (cryptoOf' interpretation).F pqrKey).cipherKey
        (mkGen.generateKeys (cryptoOf' interpretation).F pqrKey).iv m.ciphertext = some r.message ∧
      st' = { g_rw.sess.state with
        rootKey := r2.rootKey, previousCounter := r2.previousCounter, senderChain := r2.senderChain,
        receiverChains := r2.receiverChains, pqRatchetState := newPqrState, pendingPreKey := false } ∧
      r.state = CryptoVerification.E2E.Record.encodeRecord
        ⟨some { g_rw.sess with state := st', pendingPreKey := none, pendingKyberPreKey := none }⟩ := by
  unfold Symbolic.Swarm.CREF.CliPure.TR.PureRecvEval.pureEvalRecvWireWithCoinsW at heval
  rw [hwire] at heval; simp only [wireWhisperTag] at heval; rw [htry] at heval; dsimp only at heval
  rcases hrole : Role.ofWho g_rw.who with _ | role
  · simp [evalOpen, hrole] at heval
  have hopen : evalOpen g_rw.who g_rw.sess =
      some (role, g_rw.sess) := by
    simp [evalOpen, hrole]
  rw [hopen] at heval; dsimp only at heval
  rcases hres : (messageDecryptSignalW (cryptoOf' interpretation) (Proofs.libsignal.SR.interpW interpretation)
      (Symbolic.Swarm.TRREF.GrowthRecordPure.pureSpqr (Symbolic.Swarm.TRREF.SpqrSemOf.spqrModelOf interpretation))
      Symbolic.Swarm.CREF.CliPure.TR.PureRecvEval.pureSerializeRole
      (inMemAnswers g_rw.sess) m role.peer role
      (Symbolic.Swarm.CREF.CliPureRcv.TR.RecvDecStepPure.purePinCoins (some rngBytes))) with ⟨res, calls⟩
  rw [hres] at heval; dsimp only at heval
  rcases res with e | ptB
  · simp at heval
  simp only [Option.some.injEq, Prod.mk.injEq] at heval; obtain ⟨hst_enc, hpt⟩ := heval; subst hpt
  have h1 : (messageDecryptSignalW (cryptoOf' interpretation) (Proofs.libsignal.SR.interpW interpretation)
      (Symbolic.Swarm.TRREF.GrowthRecordPure.pureSpqr (Symbolic.Swarm.TRREF.SpqrSemOf.spqrModelOf interpretation))
      Symbolic.Swarm.CREF.CliPure.TR.PureRecvEval.pureSerializeRole
      (inMemAnswers g_rw.sess) m role.peer role
      (Symbolic.Swarm.CREF.CliPureRcv.TR.RecvDecStepPure.purePinCoins (some rngBytes))).1 = .ok r.message := by rw [hres]
  obtain ⟨st', hdec, _hrid, hstore⟩ :=
    Symbolic.Swarm.CREF.CliPure.TR.PureRecvEval.storedSession_of_decryptOk (cryptoOf' interpretation)
      (Proofs.libsignal.SR.interpW interpretation)
      (Symbolic.Swarm.TRREF.GrowthRecordPure.pureSpqr (Symbolic.Swarm.TRREF.SpqrSemOf.spqrModelOf interpretation))
      Symbolic.Swarm.CREF.CliPure.TR.PureRecvEval.pureSerializeRole m
      role.peer role (Symbolic.Swarm.CREF.CliPureRcv.TR.RecvDecStepPure.purePinCoins (some rngBytes)) g_rw.sess r.message h1
  have hcalls2 : (messageDecryptSignalW (cryptoOf' interpretation) (Proofs.libsignal.SR.interpW interpretation)
      (Symbolic.Swarm.TRREF.GrowthRecordPure.pureSpqr (Symbolic.Swarm.TRREF.SpqrSemOf.spqrModelOf interpretation))
      Symbolic.Swarm.CREF.CliPure.TR.PureRecvEval.pureSerializeRole
      (inMemAnswers g_rw.sess) m role.peer role
      (Symbolic.Swarm.CREF.CliPureRcv.TR.RecvDecStepPure.purePinCoins (some rngBytes))).2 = calls := by rw [hres]
  rw [hcalls2] at hstore
  obtain ⟨remIk, r2, mkGen, newPqrState', pqrKey', hVer, hRem, hSpqr', hDec, hSt', hBr⟩ :=
    Proofs.libsignal.RngG.R3.decryptW_ok_branch hdec
  have hspqr_eq : (Symbolic.Swarm.TRREF.GrowthRecordPure.pureSpqr
      (Symbolic.Swarm.TRREF.SpqrSemOf.spqrModelOf interpretation)).recv
      g_rw.sess.state.pqRatchetState m.pqRatchet =
      (Symbolic.Swarm.TRREF.SpqrSemOf.spqrModelOf interpretation).recv
      g_rw.sess.state.pqRatchetState m.pqRatchet := rfl
  rw [hspqr_eq, hrecv_spqr] at hSpqr'
  simp only [Except.ok.injEq, Prod.mk.injEq] at hSpqr'; obtain ⟨rfl, rfl⟩ := hSpqr'
  cases hBr with
  | skipped ck' hFind _hLt _hTake _hMac =>
    obtain ⟨ci', rc', _hci', hrc', hsrk', _hck'⟩ :=
      Proofs.libsignal.RngG.CliPure.R3.findReceiverChainKey_ok_some _ _ _ hFind
    exact absurd hsrk' (hrc_none rc' (List.mem_of_getElem? hrc'))
  | existing ck' _ck_adv _ck_next _r_adv hFind _hNotLt _hJump _hAdv _hNext _hSet _hMkGen _hMac =>
    obtain ⟨ci', rc', _hci', hrc', hsrk', _hck'⟩ :=
      Proofs.libsignal.RngG.CliPure.R3.findReceiverChainKey_ok_some _ _ _ hFind
    exact absurd hsrk' (hrc_none rc' (List.mem_of_getElem? hrc'))
  | ratchet ck ck_adv ck_next r1 r_adv hFind hDh hNotLt hJump hAdv hNext hSet hMkGen hMac =>
    exact ⟨role, remIk, ck, ck_adv, ck_next, r1, r_adv, r2, mkGen, st',
      rfl, hVer, hRem, hFind, hDh, hNotLt, hJump, hAdv, hNext, hSet, hMkGen, hMac, hDec, hSt',
      by rw [← hst_enc, hstore]⟩

theorem a2b_runTrace_decrypt_ratchet
    {r₀ : ProtocolSetup} {ms : List Move} {p : Participant} {stateIdx msgIdx pqIdx : Nat}
    {spqrMsgIdx : UInt32} {wrapped : Bool}
    {st : TRState} {t seed key pqSalt ptTerm spqr' : DY.Bytes} {msg : TRSignalMsg} {c' : RecvChain}
    (hst : ((PersistentLocalState.getLocalState p stateIdx : Traceful TRState).run
      (runTraceMoves r₀ ms)).1 = some st)
    (hmsg : (runTraceMoves r₀ ms).getMessageSentAt msgIdx = some t)
    (hparse : parseTrSignalMsg t = some msg) (hver : msg.version = messageVersion)
    (hfind : findRecvChain st.recv msg.ratchetKey = none)
    (hlow : x25519LowOrder msg.ratchetKey = false)
    (hcons : consumeMessageKey (trDhRatchetState st msg.ratchetKey (runTraceMoves r₀ ms).length).2
      msg.counter = some (seed, c'))
    (hspqr : Spqr.spqrRecv (trDhRatchetState st msg.ratchetKey (runTraceMoves r₀ ms).length).1.spqr
      msg.pqRatchet spqrMsgIdx = some (spqr', key))
    (hpqSalt : ((((runTraceMoves r₀ ms).append (⟨32⟩ : DY.Random.ExecEntryT)).append
      (⟨key⟩ : Network.ExecEntryT)).at? pqIdx : Option Network.ExecEntryT) = some ⟨pqSalt⟩)
    (hmac_eq : msg.mac = computeMac (trMsgKeys pqSalt seed).macKey
      (trDhRatchetState st msg.ratchetKey (runTraceMoves r₀ ms).length).1.peerIk
      (trDhRatchetState st msg.ratchetKey (runTraceMoves r₀ ms).length).1.myIk msg.wire)
    (hdec : DY.SymEnc.symDec (trMsgKeys pqSalt seed).cipherKey (trMsgKeys pqSalt seed).iv
      msg.ciphertext = some ptTerm) :
    let st1 := (trDhRatchetState st msg.ratchetKey (runTraceMoves r₀ ms).length).1
    let c := (trDhRatchetState st msg.ratchetKey (runTraceMoves r₀ ms).length).2
    runTraceMoves r₀ (ms ++ [.decrypt p stateIdx msgIdx pqIdx spqrMsgIdx wrapped]) =
      decTailTr (decRatchetPreTr (runTraceMoves r₀ ms) p st1 msg.ratchetKey key) p stateIdx st1 c c'
        msg.ratchetKey seed pqSalt ptTerm spqr' msg.counter := by
  dsimp only
  rw [runTrace_snoc, ← decTailTr_eq_recvDec]
  exact decrypt_next_ratchet_eq hst hmsg hparse hver hfind hlow hcons hspqr hpqSalt hmac_eq hdec

theorem a2b_at?_stEntry_decRatchetPreTr
    (tr : ExecTrace) (me : Participant) (st1 : TRState) (pk key : DY.Bytes) (i : Nat) :
    ((decRatchetPreTr tr me st1 pk key).at? i : Option StEntry) = (tr.at? i : Option StEntry) := by
  unfold decRatchetPreTr
  rw [at?_append_non_entry _ _ rfl, at?_append_non_entry _ _ rfl,
      at?_append_non_entry _ _ rfl, at?_append_non_entry _ _ rfl]

/-- Preserves `TRNsBound` across a DH-ratchet `Move.decrypt` step (which resets `ns` to `0`). -/
theorem a2b_trNsBound_decRatchet
    {r₀ : ProtocolSetup} {ms : List Move} {sent : List HwBytes} {m : Move}
    {p : Participant} {stateIdx : Nat} {st : TRState}
    {key seed pqSalt ptTerm spqr' pk : DY.Bytes} {c' : RecvChain} {n : UInt32}
    (hns : TRNsBound r₀ ms sent)
    (htr : runTraceMoves r₀ (ms ++ [m]) =
      decTailTr
        (decRatchetPreTr (runTraceMoves r₀ ms) p
          (trDhRatchetState st pk (runTraceMoves r₀ ms).length).1 pk key)
        p stateIdx
        (trDhRatchetState st pk (runTraceMoves r₀ ms).length).1
        (trDhRatchetState st pk (runTraceMoves r₀ ms).length).2
        c' pk seed pqSalt ptTerm spqr' n) :
    TRNsBound r₀ (ms ++ [m]) sent := by
  let tr₀ := runTraceMoves r₀ ms
  let st1 := (trDhRatchetState st pk tr₀.length).1
  let c := (trDhRatchetState st pk tr₀.length).2
  let tr_pre := decRatchetPreTr tr₀ p st1 pk key
  let tr_sk := logSkippedKeysTr (st1.sessionInfo p) pk c.rIdx stateIdx c.chainKey c.index
    (n.toNat - c.index.toNat) tr_pre
  let tr_rcv := tr_sk.append (⟨TREvent.Received p st1.peer pk n ptTerm⟩ : TREntry)
  let tr_mid := tr_rcv.append (⟨TREvent.MessageKey (st1.sessionInfo p) .receiver seed pqSalt
    n c.rIdx stateIdx⟩ : TREntry)
  have htr' : runTraceMoves r₀ (ms ++ [m]) =
      tr_mid.append (⟨⟨p, { st1 with recv := setRecvChain st1.recv c', spqr := spqr' }⟩⟩ : StEntry) := by
    rw [htr]; rfl
  refine trNsBound_of_append_stEntry (tr₀ := tr_mid) (me := p)
      (st' := { st1 with recv := setRecvChain st1.recv c', spqr := spqr' })
    htr' (fun i => ?_) (Nat.zero_le sent.length) hns
  dsimp only [tr_mid, tr_rcv, tr_sk, tr_pre]
  rw [at?_append_non_entry _ _ rfl, at?_append_non_entry _ _ rfl,
      at?_stEntry_logSkippedKeysTr, a2b_at?_stEntry_decRatchetPreTr]

/-- Establishes `PureTRRecordStateInv` for the singleton table at `p` after a DH-ratchet
`Move.decrypt` step. -/
theorem a2b_trRecordStateInv_decRatchet_single
    {interpretation : ExternInterpretation} {r₀ : ProtocolSetup} {S : SpqrSem} {Z : PureTRSlots}
    {g : Ghost} {ms : List Move} {m : Move}
    {p : Participant} {stateIdx : Nat} {st : TRState} {rec' : RecordRec} {newBytes : HwBytes}
    {key seed pqSalt ptTerm spqr' pk : DY.Bytes} {c' : RecvChain} {n : UInt32}
    (hp_mem : p = r₀.alice ∨ p = r₀.bob)
    (htr : runTraceMoves r₀ (ms ++ [m]) =
      decTailTr
        (decRatchetPreTr (runTraceMoves r₀ ms) p
          (trDhRatchetState st pk (runTraceMoves r₀ ms).length).1 pk key)
        p stateIdx
        (trDhRatchetState st pk (runTraceMoves r₀ ms).length).1
        (trDhRatchetState st pk (runTraceMoves r₀ ms).length).2
        c' pk seed pqSalt ptTerm spqr' n)
    (hnew : newBytes = recordBytes rec')
    (hrel' : StateRel interpretation S g
      { (trDhRatchetState st pk (runTraceMoves r₀ ms).length).1 with
        recv := setRecvChain (trDhRatchetState st pk (runTraceMoves r₀ ms).length).1.recv c',
        spqr := spqr' }
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
        (findRecvChain
          { (trDhRatchetState st pk (runTraceMoves r₀ ms).length).1 with
            recv := setRecvChain (trDhRatchetState st pk (runTraceMoves r₀ ms).length).1.recv c',
            spqr := spqr' }.toDRState.recv pk_k).isSome = true)
    (hcanon' : newBytes.length < 2 ^ 32 - 2 ^ 20 → Z.canon p newBytes)
    (hks : TRKeyShape interpretation S g st)
    (hRngLen : (g.σ (runTraceMoves r₀ ms).length 32).length = 32)
    (hnd' : (rec'.current.receiverChains.map ChainRec.senderRatchetKey).Nodup ∧
      (∀ c_k ∈ rec'.current.receiverChains, (c_k.messageKeys.map Prod.fst).Nodup) ∧
      ∀ c_k ∈ rec'.current.receiverChains, ∀ k ∈ c_k.messageKeys,
        ∃ ck, c_k.chainKey = some ck ∧ k.1 < ck.1) :
    PureTRRecordStateInv interpretation r₀ S Z g (ms ++ [m])
      (fun q => if q = p then some newBytes else none) := by
  let st1 := (trDhRatchetState st pk (runTraceMoves r₀ ms).length).1
  let c := (trDhRatchetState st pk (runTraceMoves r₀ ms).length).2
  let tr_pre := decRatchetPreTr (runTraceMoves r₀ ms) p st1 pk key
  intro q b hqb
  by_cases hqp : q = p
  · subst hqp; simp only [↓reduceIte, Option.some.injEq] at hqb; subst hqb
    refine ⟨hp_mem, rec', { st1 with recv := setRecvChain st1.recv c', spqr := spqr' },
      tr_pre.length + (n.toNat - c.index.toNat) + 2, hnew, ?_, ?_, hrel', ?_, hcanon',
      trKeyShape_trDhRatchetState_recv_spqr interpretation S g hks hRngLen, hnd'⟩
    · rw [htr, getLocalState_decTailTr_last]
    · rw [htr, isCurrentSnapshot_decTailTr_last]
    · exact hsk'
  · simp only [hqp, ↓reduceIte] at hqb; cases hqb

end Symbolic.Swarm.CREF.CliPureRcv.TR.RecvDecStepTiePure
