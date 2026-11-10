/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

import DY.Trace.Basic
public import Symbolic.Proofs.Swarm.CREF.RecvWire.AcceptNewRecBasePure
public import Symbolic.Proofs.Swarm.CREF.TR.RecvDecStepSkippedG1LeavesPure
public import Symbolic.Proofs.Swarm.CREF.TR.RecvFresh
import Symbolic.Proofs.Swarm.CREF.Cli.Rpk.RecvDecStepCommonPure
import Symbolic.Proofs.Swarm.CREF.Cli.Rpk.RecvDecStepNoRatchetPure
import Symbolic.Proofs.Swarm.CREF.Cli.Rpk.RecvDecStepRatchetDHProvPure
import Symbolic.Proofs.Swarm.CREF.Cli.Rpk.RecvDecStepRatchetDHaPure
import Symbolic.Proofs.Swarm.CREF.ModelBridge
import Symbolic.Proofs.Swarm.CREF.Prelude
import Symbolic.Proofs.Swarm.CREF.TROpen
import Symbolic.Proofs.Swarm.CREF.TR.Leaks -- shake: keep
import Symbolic.Proofs.Swarm.CREF.TR.PQGamma -- shake: keep
import Symbolic.Proofs.Swarm.CREF.TR.PQModelRunNil -- shake: keep
import Symbolic.DYBridge.DY.Trace.Basic

/-!
# Whisper Receive Pending Pre-Key Branch Helpers

Helper lemmas for the `PureAliceInitPending` disjunct across DH-ratchet receive steps.
-/

@[expose] public section

cref_hide_foreign_instances
set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

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
  chainKeyAt kdfCk maxForwardJumps computeMac messageVersion x25519LowOrder)
open DY.Libsignal.TripleRatchet
open DY.Libsignal.TripleRatchet.Refinement (wireWhisperTag)
open DY.Libsignal.HwEvents DY.Libsignal.Rust
open CryptoGames CryptoGames.HMAC CryptoGames.HKDF
open CryptoGames.LibsignalSession CryptoGames.LibsignalSessionApi
open CryptoVerification
open CryptoVerification.LibsignalTripleRatchet CryptoVerification.LibsignalProtoCodec
open CryptoVerification.E2E CryptoVerification.E2E.InMem CryptoVerification.E2E.Record
open CryptoVerification.E2E.Bin (Role evalOpen inMemAnswers)
open CryptoVerification.E2E.Pqxdh.WireEntries.SymP3 (RecvWireGhost)
open CryptoProofLib.Refinement (ExternInterpretation)
open Proofs.libsignal.RngG
open Proofs.libsignal.Hooks2 (cryptoOf')
open Proofs.libsignal.RngG.R3 (ratchetStateOf)
open Proofs.libsignal.SR (messageDecryptSignalW)
open Swarm.Phase0WholeFunctionBridge (sessionToRecordRec sessionToSessionRec
  receiverChainToChainRec)
open CryptoVerification.SessionModel.AdvanceAndFrame (mem_set_or)
open Symbolic.Swarm.CREF Symbolic.Swarm.CREF.CliPure Symbolic.Swarm.CREF.CliPureRcv
open Symbolic.Swarm.CREF.CliPure.TR Symbolic.Swarm.CREF.CliPureRcv.TR
open Symbolic.Swarm.CREF.TR.RecvDec (trDhRatchetState decRatchetPreTr decrypt_next_ratchet_eq
  trNsBound_of_append_stEntry)
open Symbolic.Swarm.TRREF.SpqrSemOf (spqrModelOf)

open Symbolic.Swarm.CREF.CliPure.TR.RecvDecStep (receiverKeyUsedB_false_of_gt_rIdx_tr)

theorem a2b_pend_skippedKeyUsedB_decRatchetPreTr
    (tr : ExecTrace) (me : Participant) (st1 : TRState) (pk key : DY.Bytes) (skIdx : Nat) :
    skippedKeyUsedB (decRatchetPreTr tr me st1 pk key) skIdx = skippedKeyUsedB tr skIdx := by
  unfold decRatchetPreTr
  rw [skippedKeyUsedB_append_trEntry_other_a2 _ _ (fun _ _ h => by cases h),
      skippedKeyUsedB_append_trEntry_other_a2 _ _ (fun _ _ h => by cases h),
      skippedKeyUsedB_append_non_tr_a2 _ _ rfl,
      skippedKeyUsedB_append_non_tr_a2 _ _ rfl]

theorem a2b_pend_receiverKeyUsedB_decRatchetPreTr
    (tr : ExecTrace) (me : Participant) (st1 : TRState) (pk key : DY.Bytes)
    (s' : SessionInfo) (seed' : DY.Bytes) (cnt' : UInt32) (rIdx' : Nat) :
    receiverKeyUsedB (decRatchetPreTr tr me st1 pk key) s' seed' cnt' rIdx' =
      receiverKeyUsedB tr s' seed' cnt' rIdx' := by
  unfold decRatchetPreTr
  rw [receiverKeyUsedB_append_trEntry_other_a2 _ _ (fun _ _ _ _ _ _ h => by cases h),
      receiverKeyUsedB_append_trEntry_other_a2 _ _ (fun _ _ _ _ _ _ h => by cases h),
      receiverKeyUsedB_append_non_tr_a2 _ _ rfl,
      receiverKeyUsedB_append_non_tr_a2 _ _ rfl]

theorem a2b_pend_evalRecvWireWithCoinsW_ratchetDH_inv
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

theorem a2b_pend_runTrace_decrypt_ratchet
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

theorem a2b_pend_at?_stEntry_decRatchetPreTr
    (tr : ExecTrace) (me : Participant) (st1 : TRState) (pk key : DY.Bytes) (i : Nat) :
    ((decRatchetPreTr tr me st1 pk key).at? i : Option StEntry) = (tr.at? i : Option StEntry) := by
  unfold decRatchetPreTr
  rw [at?_append_non_entry _ _ rfl, at?_append_non_entry _ _ rfl,
      at?_append_non_entry _ _ rfl, at?_append_non_entry _ _ rfl]

theorem a2b_pend_trNsBound_decRatchet
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
      at?_stEntry_logSkippedKeysTr, a2b_pend_at?_stEntry_decRatchetPreTr]

theorem a2b_pend_trRecordStateInv_decRatchet_single
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

private theorem a2b_pend_findRecvChain_setRecvChain_isSome (recv : List RecvChain) (c : RecvChain) (pk : DY.Bytes) :
    (findRecvChain (setRecvChain recv c) pk).isSome = (findRecvChain recv pk).isSome := by
  unfold findRecvChain setRecvChain
  induction recv with
  | nil => rfl
  | cons d tl ih =>
    rw [List.map_cons, List.find?_cons, List.find?_cons]
    have hrk : (if (d.ratchetKey == c.ratchetKey) = true then c else d).ratchetKey = d.ratchetKey := by
      cases h : d.ratchetKey == c.ratchetKey
      · rfl
      · exact (beq_iff_eq.mp h).symm
    rw [hrk]
    cases d.ratchetKey == pk
    · exact ih
    · rfl

private theorem a2b_pend_drop_append_of_le {α : Type} :
    ∀ (xs ys : List α) (d : Nat), d ≤ xs.length → (xs ++ ys).drop d = xs.drop d ++ ys
  | xs, ys, 0, _ => rfl
  | [], _, d + 1, h => absurd h (Nat.not_le_of_gt (Nat.succ_pos d))
  | _ :: xs, ys, d + 1, h => a2b_pend_drop_append_of_le xs ys d (Nat.le_of_succ_le_succ h)

private theorem a2b_pend_findRecvChain_trDhRatchetState_self_isSome
    (st : TRState) (pk : DY.Bytes) (ts : Nat) (c' : RecvChain) (spqr' : DY.Bytes) :
    (findRecvChain
      { (trDhRatchetState st pk ts).1 with
        recv := setRecvChain (trDhRatchetState st pk ts).1.recv c',
        spqr := spqr' }.toDRState.recv pk).isSome = true := by
  dsimp only
  rw [a2b_pend_findRecvChain_setRecvChain_isSome]
  unfold trDhRatchetState
  dsimp only
  have hd : (st.recv.length + 1) - DY.Libsignal.TripleRatchet.maxReceiverChains ≤ st.recv.length := by
    change (st.recv.length + 1) - 5 ≤ st.recv.length; omega
  rw [a2b_pend_drop_append_of_le _ _ _ hd]
  exact List.find?_isSome.mpr
    ⟨_, List.mem_append_right _ (List.Mem.head []), beq_self_eq_true pk⟩

theorem a2b_pend_skippedOk_ratchet_decTail
    {interpretation : ExternInterpretation} {S : SpqrSem} {g : Ghost}
    {r₀ : ProtocolSetup} {ms : List Move} {m_move : Move} {p : Participant} {stateIdx : Nat}
    {st : TRState} {seed key pqSalt ptTerm spqr' : DY.Bytes} {msg : TRSignalMsg} {c' : RecvChain}
    {s s' : CryptoGames.LibsignalSessionApi.Session (List (BitVec 8))}
    {their : PublicKey} {ck ck_next : ChainKey} {r1 r2 : RatchetState}
    {mks' : List MessageKeyGenerator}
    (hreach : (runTraceMoves r₀ ms).Reachable reachability)
    (hF : TRRecvCountersFresh (runTraceMoves r₀ ms) p st)
    (htr : runTraceMoves r₀ (ms ++ [m_move]) =
      decTailTr
        (decRatchetPreTr (runTraceMoves r₀ ms) p
          (trDhRatchetState st msg.ratchetKey (runTraceMoves r₀ ms).length).1 msg.ratchetKey key)
        p stateIdx
        (trDhRatchetState st msg.ratchetKey (runTraceMoves r₀ ms).length).1
        (trDhRatchetState st msg.ratchetKey (runTraceMoves r₀ ms).length).2
        c' msg.ratchetKey seed pqSalt ptTerm spqr' msg.counter)
    (hnil_all : ∀ rc' ∈ s.state.receiverChains, rc'.messageKeys = [])
    (htheir : their.bytes.toList = gamma interpretation S g msg.ratchetKey)
    (hR1Rc : r1.receiverChains =
      RatchetState.evictReceiverChains (s.state.receiverChains ++ [⟨their, some ck, []⟩]))
    (hR2Rc : r2.receiverChains =
      r1.receiverChains.set (r1.receiverChains.length - 1) ⟨their, some ck_next, mks'⟩)
    (hMks' : ∀ k ∈ mks',
      ∃ j < msg.counter.toNat,
        k.counter = BitVec.ofNat 32 j ∧ UInt32.ofBitVec k.counter = UInt32.ofNat j ∧
        UInt32.ofBitVec k.counter ≠ msg.counter ∧
        k.seed = gamma interpretation S g
          (kdfCk (chainKeyAt
            (trDhRatchetState st msg.ratchetKey (runTraceMoves r₀ ms).length).2.chainKey j)).2 ∧
        k.seed.length = 32)
    (hRcs' : s'.state.receiverChains = r2.receiverChains) :
    ∀ c_k ∈ (sessionToRecordRec s').current.receiverChains, ∀ k ∈ c_k.messageKeys,
      ∃ pk rIdx srcIdx skIdx seed_k,
        (runTraceMoves r₀ (ms ++ [m_move])).EventLoggedAt
          (TREvent.SkippedKeyStored (st.sessionInfo p) pk (UInt32.ofBitVec k.1) seed_k rIdx srcIdx) skIdx ∧
        !skippedKeyUsedB (runTraceMoves r₀ (ms ++ [m_move])) skIdx ∧
        !receiverKeyUsedB (runTraceMoves r₀ (ms ++ [m_move])) (st.sessionInfo p) seed_k (UInt32.ofBitVec k.1) rIdx ∧
        gamma interpretation S g seed_k = k.2 ∧
        c_k.senderRatchetKey = serializedKey (gamma interpretation S g pk) ∧
        (findRecvChain
          { (trDhRatchetState st msg.ratchetKey (runTraceMoves r₀ ms).length).1 with
            recv := setRecvChain (trDhRatchetState st msg.ratchetKey (runTraceMoves r₀ ms).length).1.recv c',
            spqr := spqr' }.toDRState.recv pk).isSome = true := by
  intro c_k hc_k k hk
  rw [htr]
  let tr := runTraceMoves r₀ ms
  let st1 := (trDhRatchetState st msg.ratchetKey tr.length).1
  let c := (trDhRatchetState st msg.ratchetKey tr.length).2
  let tr_pre := decRatchetPreTr tr p st1 msg.ratchetKey key
  have hsinfo : st1.sessionInfo p = st.sessionInfo p := rfl
  have hrIdx_c : c.rIdx = st.rIdx + 2 := rfl
  have hgt_rIdx : st.rIdx < c.rIdx := by omega
  simp only [sessionToRecordRec, sessionToSessionRec, hRcs', hR2Rc, List.mem_map] at hc_k
  rcases hc_k with ⟨rc', hrc', rfl⟩
  simp only [receiverChainToChainRec, List.mem_map] at hk
  rcases hk with ⟨mk, hmk, rfl⟩
  rcases mem_set_or r1.receiverChains (r1.receiverChains.length - 1) ⟨their, some ck_next, mks'⟩
      rc' hrc' with rfl | hrc_r1
  · obtain ⟨j, hjLt, _, hjU32, hjNe, hjSeed, _⟩ := hMks' mk hmk
    refine ⟨msg.ratchetKey, c.rIdx, stateIdx, tr_pre.length + j,
      (kdfCk (chainKeyAt c.chainKey j)).2, ?_, ?_, ?_, hjSeed.symm, ?_,
      a2b_pend_findRecvChain_trDhRatchetState_self_isSome st msg.ratchetKey tr.length c' spqr'⟩
    · have hjLt' : j < msg.counter.toNat - c.index.toNat := by change j < msg.counter.toNat - 0; omega
      have h0 : c.index + UInt32.ofNat j = UInt32.ofBitVec mk.counter := by
        rw [hjU32]; change (0 : UInt32) + UInt32.ofNat j = UInt32.ofNat j
        exact UInt32.zero_add (UInt32.ofNat j)
      rw [← hsinfo, ← h0]
      exact hsk'_decTailTr_of_new_exact_tr tr_pre p stateIdx st1 c c' msg.ratchetKey seed pqSalt ptTerm spqr' msg.counter hjLt'
    · rw [skippedKeyUsedB_decTailTr]
      change (!skippedKeyUsedB tr_pre (tr_pre.length + j)) = true
      dsimp only [tr_pre]
      rw [a2b_pend_skippedKeyUsedB_decRatchetPreTr]
      have hge : tr.length ≤ tr_pre.length + j := by
        simp only [tr_pre, decRatchetPreTr, Symbolic.DYBridge.DY.Trace.append_eq_1,
          Symbolic.DYBridge.DY.Trace.length_eq_2]
        omega
      rw [Symbolic.Swarm.CREF.CliPure.TR.RecvDecStep.skippedKeyUsedB_of_ge_length_tr hreach hge]; rfl
    · rw [← hsinfo, receiverKeyUsedB_decTailTr, hsinfo]
      have hne_ctr : ¬ (msg.counter = UInt32.ofBitVec mk.counter) := fun h => hjNe h.symm
      simp only [hne_ctr, false_and, and_false, decide_false, Bool.or_false]
      rw [a2b_pend_receiverKeyUsedB_decRatchetPreTr,
          Symbolic.Swarm.CREF.CliPure.TR.RecvDecStep.receiverKeyUsedB_false_of_gt_rIdx_tr hF hgt_rIdx]; rfl
    · show their.serialize = _
      rw [← htheir]; rfl
  · rw [hR1Rc] at hrc_r1
    have hrc_app := List.mem_of_mem_drop hrc_r1
    rw [List.mem_append, List.mem_singleton] at hrc_app
    rcases hrc_app with hrc_old | rfl
    · rw [hnil_all rc' hrc_old] at hmk
      cases hmk
    · cases hmk

end Symbolic.Swarm.CREF.CliPureRcv.TR.RecvDecStepTiePure
