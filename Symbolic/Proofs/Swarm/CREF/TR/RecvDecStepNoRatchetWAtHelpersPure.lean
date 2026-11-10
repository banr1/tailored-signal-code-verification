/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Symbolic.Proofs.Swarm.CREF.TR.RecvDecStepSkippedG1LeavesPure
public import Symbolic.Proofs.Swarm.CREF.Cli.Rpk.R3ChainsWFPresPure
import DY.Trace.Basic
import DY.Trace.Monad
import DY.Trace.Manipulation
import DY.ALaCarte.Basic
import DY.Actions.Network
import DY.Actions.PersistentLocalState
import DY.Actions.PersistentGlobalState
import DY.Actions.ProtocolEvent
import DY.Actions.Random
import Symbolic.Proofs.SpecLemmas.Refinement.Composed.ModelTraces
import Symbolic.Proofs.Swarm.CREF.Cli.Rpk.R3StepExistingPure
import Symbolic.Proofs.Swarm.CREF.Prelude
import Symbolic.Proofs.Swarm.CREF.TROpen
import Symbolic.Proofs.Refinement.EncodeWithCovered -- shake: keep
import Symbolic.Proofs.Swarm.CREF.Cli.Rpk.RecvDecStepNoRatchetPure -- shake: keep
import Symbolic.Proofs.Swarm.CREF.TR.G1.G1RepMacTR -- shake: keep
import Symbolic.Proofs.Swarm.CREF.TR.Leaks -- shake: keep
import Symbolic.Proofs.Swarm.CREF.TR.NoTrWireU -- shake: keep
import Symbolic.Proofs.Swarm.CREF.TR.PQModelRunNil -- shake: keep
import Symbolic.Proofs.Swarm.CREF.TR.RecvCol -- shake: keep
import Symbolic.Proofs.Swarm.CREF.TR.RecvRep -- shake: keep
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
# Existing-Chain Whisper Receive Helper Lemmas

Proves pure helper lemmas for the existing-chain whisper receive branch and defines the
authentic decrypt representation `AuthenticDecryptRepB3St` at a fixed provenance state.
-/

@[expose] public section

cref_hide_foreign_instances

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

namespace Symbolic.Swarm.CREF.CliPureRcv.TRPure
open Symbolic.Swarm.CREF Symbolic.Swarm.CREF.CliPure Symbolic.Swarm.CREF.CliPureRcv
open Symbolic.Swarm.CREF.TR Symbolic.Swarm.CREF.CliPure.TR Symbolic.Swarm.CREF.CliPureRcv.TR
cref_open
cref_open_tr
open DY.Libsignal.TripleRatchet
open CryptoProofLib.Refinement (ExternInterpretation)
open DY.Libsignal.TripleRatchet (SessionInfo RecvChain findRecvChain setRecvChain recvChainFor
  consumeMessageKey computeMac messageVersion)

theorem knows_setupPublic (r₀ : ProtocolSetup) (hNe : r₀.alice ≠ r₀.bob) (ms : List Move) (i : Nat) (hi : i = 0 ∨ i = 2) :
    (setupPublic r₀ i).AttackerKnows (runTraceMoves r₀ ms) := by
  apply setupSent_known
  let f (T : ExecTrace) : List DY.Bytes :=
    (newIndices Trace.nil T).filterMap fun k => T.getMessageSentAt k
  have hnil : f Trace.nil = [] := by
    simp [f, newIndices, Symbolic.DYBridge.DY.Trace.length_eq_1]
  have happ : ∀ {E : Type} [ExecTraceTypes.Has E] (T : ExecTrace) (e : E),
      f (T.append e) = f T ++
        (match ((T.append e).at? T.length : Option Network.ExecEntryT) with
         | none => []
         | some entry => [entry.msg]) := by
    intro E _ T e
    have hidx : newIndices Trace.nil (T.append e) = newIndices Trace.nil T ++ [T.length] := by
      simp [newIndices, Symbolic.DYBridge.DY.Trace.length_eq_1,
        Symbolic.DYBridge.DY.Trace.append_eq_1, Symbolic.DYBridge.DY.Trace.length_eq_2,
        List.range'_concat]
    have hpre : List.filterMap (fun k => (T.append e).getMessageSentAt k) (newIndices Trace.nil T) =
        f T := by
      apply List.filterMap_congr
      intro k hk
      have hlt : k < T.length := by
        simp [newIndices, Symbolic.DYBridge.DY.Trace.length_eq_1, List.mem_range'] at hk
        omega
      simp only [Symbolic.DYBridge.DY.Trace.getMessageSentAt_eq_1,
        Symbolic.Swarm.CREF.TR.at?_append_of_lt T e hlt]
    have hlast := Symbolic.DYBridge.DY.Trace.getMessageSentAt_eq_1 T.length (T.append e)
    dsimp only [f]
    rw [hidx, List.filterMap_append, hpre]
    cases hproj : ((T.append e).at? T.length : Option Network.ExecEntryT) <;>
      simp [List.filterMap_cons, List.filterMap_nil, hlast, hproj, f]
  have hnet : ∀ (T : ExecTrace) (b : DY.Bytes), f (T.append (b1_NetE b)) = f T ++ [b] := by
    intro T b; rw [happ, Symbolic.Swarm.CREF.TR.at?_append_eq T (b1_NetE b) rfl]
  have hrnd : ∀ (T : ExecTrace) (n : Nat), f (T.append (b1_RndE n)) = f T := by
    intro T n; rw [happ, Symbolic.Swarm.CREF.TR.at?_append_eq_of_proj T (b1_RndE n) rfl none rfl, List.append_nil]
  have hev : ∀ (T : ExecTrace) (ev), f (T.append (b1_EvE ev)) = f T := by
    intro T ev; rw [happ, Symbolic.Swarm.CREF.TR.at?_append_eq_of_proj T (b1_EvE ev) rfl none rfl, List.append_nil]
  have hst : ∀ (T : ExecTrace) (p : DY.Participant) (s), f (T.append (b1_StE p s)) = f T := by
    intro T p s; rw [happ, Symbolic.Swarm.CREF.TR.at?_append_eq_of_proj T (b1_StE p s) rfl none rfl, List.append_nil]
  have hsent : setupSent r₀ = f (if r₀.withOpk then b1_setupTr5 r₀.alice r₀.bob else b1_setupTr4 r₀.alice r₀.bob) := by
    rw [setupSent, b1_setupTrace_eq r₀ hNe]
  rw [setupPublic, hsent]
  rcases hi with rfl | rfl <;> cases r₀.withOpk
  · simp only [↓reduceIte, Bool.false_eq_true, b1_setupTr4, b1_setupTr3, b1_setupTr2, b1_setupTr1,
      hnet, hrnd, hev, hst, hnil, List.nil_append, List.cons_append]
    exact List.mem_cons_self
  · simp only [↓reduceIte, b1_setupTr5, b1_setupTr4, b1_setupTr3, b1_setupTr2, b1_setupTr1,
      hnet, hrnd, hev, hst, hnil, List.nil_append, List.cons_append]
    exact List.mem_cons_self
  · simp only [↓reduceIte, Bool.false_eq_true, b1_setupTr4, b1_setupTr3, b1_setupTr2, b1_setupTr1,
      hnet, hrnd, hev, hst, hnil, List.nil_append, List.cons_append]
    exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self)
  · simp only [↓reduceIte, b1_setupTr5, b1_setupTr4, b1_setupTr3, b1_setupTr2, b1_setupTr1,
      hnet, hrnd, hev, hst, hnil, List.nil_append, List.cons_append]
    exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self)

end Symbolic.Swarm.CREF.CliPureRcv.TRPure

namespace Symbolic.Swarm.CREF.CliPureRcv.TR.RecvDecStepPure
open Symbolic.Swarm.CREF.TR hiding at?_append_of_lt getLocalState_fst newRandoms_append_rnd runMoves_append runTrace_append runTrace_snoc runVis_append runVis_snoc run_bind_fst run_bind_snd
open Symbolic.Swarm.CREF.CliPureRcv.TRPure
open Symbolic.Swarm.CREF.CliPure.TR.RecvDecStep hiding SpqrSem StEntry TREntry

cref_open
cref_open_tr

open DY DY.Comparse DY.Literal DY.Libsignal
open DY.Libsignal.TripleRatchet (SessionInfo DRState KeyComponent KeyDir RecvChain findRecvChain setRecvChain recvChainFor consumeMessageKey chainKeyAt kdfCk kdfRk maxForwardJumps u32Max computeMac messageVersion createChain x25519LowOrder litByte)
open DY.Libsignal.TripleRatchet
open DY.Libsignal.TripleRatchet.Refinement (wireWhisperTag)
open DY.Libsignal.Refinement (sha256CompressFunction x25519PublicKeySymbol aesCbcEncryptSymbol aesCbcDecryptSymbol ExternCryptoLawsHold encodeWith canonicalVariation WireFields FieldItem PbValue readVarint paddedVarint encodeField readVarint_paddedVarint)
open DY.Libsignal.HwEvents DY.Libsignal.Rust
open CryptoGames CryptoGames.HMAC CryptoGames.HKDF
open CryptoGames.CBC (blockToBytesLE)
open CryptoGames.LibsignalSession CryptoGames.LibsignalSessionApi
open CryptoVerification
open CryptoVerification.LibsignalTripleRatchet CryptoVerification.LibsignalProtoCodec
open CryptoVerification.E2E CryptoVerification.E2E.InMem CryptoVerification.E2E.Record CryptoVerification.E2E.RecordX
open CryptoVerification.E2E.Bin (Role evalOpen storedSession inMemAnswers)
open CryptoVerification.E2E.Pqxdh.WireEntries.SymP3 (RecvWireGhost)
open CryptoVerification.SessionModel (chainStepN skippedKeys)
open CryptoVerification.SessionModel.AdvanceAndFrame
open CryptoProofLib.Refinement (ExternInterpretation)
open Proofs.libsignal.RngG Proofs.libsignal.RngG.R3 Proofs.libsignal.RngG.CliPure.R3
open Proofs.libsignal.Hooks2 (cryptoOf')
open Proofs.libsignal.SR (AesW  messageDecryptSignalW)
open Swarm.Phase0WholeFunctionBridge (sessionToRecordRec sessionToSessionRec senderChainToChainRec receiverChainToChainRec)
open Symbolic.Swarm.CREF Symbolic.Swarm.CREF.CliPure Symbolic.Swarm.CREF.CliPureRcv
open Symbolic.Swarm.CREF.CliPure.TR Symbolic.Swarm.CREF.CliPureRcv.TR
open Symbolic.Swarm.CREF.TR.FreshSigma (at?_eq_some_of_getLocalState_some)
open Symbolic.Swarm.TRREF.SpqrSemOf (spqrModelOf saltToBytes spqrIdx1Bytes
  spqrSendOf_of_send_some spqrKeyBytes_saltToBytes)
open Symbolic.Swarm.CREF.TR.G1 (g1_rep_of_recvRepresentations)
open Symbolic.Swarm.CREF.TR.NoTrWireU (NoTrWireU )
open Symbolic.Swarm.CREF.TR.RecvCol (TRRecvAllCollide)
open Symbolic.Swarm.CREF.TR.RecvRep (decrypt_recvRepresentations_nonempty_of_tryFrom)

theorem getElem?_receiverChains_inj_of_nodup
    {rcs : List ReceiverChain} (hnodup : (rcs.map ReceiverChain.senderRatchetKey).Nodup)
    {i j : Nat} {rc₁ rc₂ : ReceiverChain} {pk : PublicKey}
    (h1 : rcs[i]? = some rc₁) (h2 : rcs[j]? = some rc₂) (hk1 : rc₁.senderRatchetKey = pk) (hk2 : rc₂.senderRatchetKey = pk) : i = j := by
  have hi : i < (rcs.map ReceiverChain.senderRatchetKey).length := by rw [List.length_map]; exact (List.getElem?_eq_some_iff.mp h1).1
  have hj : j < (rcs.map ReceiverChain.senderRatchetKey).length := by rw [List.length_map]; exact (List.getElem?_eq_some_iff.mp h2).1
  have hm1 : (rcs.map ReceiverChain.senderRatchetKey)[i]? = some pk := by rw [List.getElem?_map, h1]; exact congrArg some hk1
  have hm2 : (rcs.map ReceiverChain.senderRatchetKey)[j]? = some pk := by rw [List.getElem?_map, h2]; exact congrArg some hk2
  rw [List.getElem?_eq_getElem hi] at hm1; rw [List.getElem?_eq_getElem hj] at hm2
  exact (List.Nodup.getElem_inj_iff hnodup).mp (Option.some.inj (hm1.trans hm2.symm))

theorem evalRecvWireWithCoinsW_noRatchet_inv
    (interpretation : ExternInterpretation) (body : HwBytes) (r : StateAndMessage) (g_rw : RecvWireGhost)
    (m : SignalMessage) (ci : Nat) (rc : ReceiverChain) (ck : ChainKey) (newPqrState : HwBytes) (pqrKey : HKDF.Salt)
    (hwire : g_rw.wireBytes = wireWhisperTag :: body) (htry : SignalMessage.tryFrom protoSignalCodec body = .ok m)
    (hrc : g_rw.sess.state.receiverChains[ci]? = some rc) (hrc_key : rc.senderRatchetKey = m.senderRatchetKey)
    (hck : rc.chainKey = some ck) (hstep_idx : ck.index ≤ m.counter)
    (hnodup : (g_rw.sess.state.receiverChains.map ReceiverChain.senderRatchetKey).Nodup)
    (hrecv_spqr : (Symbolic.Swarm.TRREF.SpqrSemOf.spqrModelOf interpretation).recv g_rw.sess.state.pqRatchetState m.pqRatchet = .ok (newPqrState, pqrKey))
    (heval : PureRecvEval.pureEvalRecvWireWithCoinsW (cryptoOf' interpretation) (Proofs.libsignal.SR.interpW interpretation)
      (Symbolic.Swarm.TRREF.SpqrSemOf.spqrModelOf interpretation) g_rw (Symbolic.Swarm.CREF.CliPureRcv.TR.RecvDecStepPure.purePinCoins none) = some (r.state, r.message)) :
    ∃ (role : Role) (remIk : IdentityKey) (ck_adv ck_next : ChainKey)
      (r_adv r2 : RatchetState) (mkGen : MessageKeyGenerator) (st' : SessionState (List (BitVec 8))),
      Role.ofWho g_rw.who = some role ∧ g_rw.sess.state.version.toNat = m.messageVersion.toNat ∧
      g_rw.sess.state.remoteIdentity = some remIk ∧
      (Proofs.libsignal.RngG.R3.ratchetStateOf g_rw.sess.state).findReceiverChainKey m.senderRatchetKey = .ok (some ck) ∧
      ¬ (m.counter < ck.index) ∧ (m.counter - ck.index).toNat ≤ (Proofs.libsignal.RngG.R3.ratchetStateOf g_rw.sess.state).maxForwardJumps ∧
      Mut.exec (RatchetState.advanceChain (cryptoOf' interpretation).F m.senderRatchetKey m.counter
        (m.counter - ck.index).toNat ck) (Proofs.libsignal.RngG.R3.ratchetStateOf g_rw.sess.state) = (.ok ck_adv, r_adv) ∧
      ck_adv.nextChainKey (cryptoOf' interpretation).F = .ok ck_next ∧
      Mut.exec (RatchetState.setReceiverChainKey m.senderRatchetKey ck_next) r_adv = (.ok (), r2) ∧
      mkGen = ck_adv.messageKeys (cryptoOf' interpretation).F ∧
      m.verifyMacWithAddresses (cryptoOf' interpretation).F (PureRecvEval.pureSerializeRole role.peer role) remIk g_rw.sess.state.localIdentity
        (mkGen.generateKeys (cryptoOf' interpretation).F pqrKey).macKey = true ∧
      (Proofs.libsignal.SR.interpW interpretation).dec (mkGen.generateKeys (cryptoOf' interpretation).F pqrKey).cipherKey
        (mkGen.generateKeys (cryptoOf' interpretation).F pqrKey).iv m.ciphertext = some r.message ∧
      st' = { g_rw.sess.state with
        rootKey := r2.rootKey, previousCounter := r2.previousCounter, senderChain := r2.senderChain,
        receiverChains := r2.receiverChains, pqRatchetState := newPqrState, pendingPreKey := false } ∧
      r.state = CryptoVerification.E2E.Record.encodeRecord
        ⟨some { g_rw.sess with state := st', pendingPreKey := none, pendingKyberPreKey := none }⟩ := by
  change PureRecvEval.pureEvalRecvWireWithCoinsW (cryptoOf' interpretation) (Proofs.libsignal.SR.interpW interpretation)
      (Symbolic.Swarm.TRREF.SpqrSemOf.spqrModelOf interpretation) g_rw 0#256 = some (r.state, r.message) at heval
  unfold PureRecvEval.pureEvalRecvWireWithCoinsW at heval; rw [hwire] at heval; simp only [wireWhisperTag] at heval; rw [htry] at heval; dsimp only at heval
  rcases hrole : Role.ofWho g_rw.who with _ | role; · simp [evalOpen, hrole] at heval
  have hopen : evalOpen g_rw.who g_rw.sess = some (role, g_rw.sess) := by simp [evalOpen, hrole]
  rw [hopen] at heval; dsimp only at heval
  rcases hres : (messageDecryptSignalW (cryptoOf' interpretation) (Proofs.libsignal.SR.interpW interpretation)
      (Symbolic.Swarm.TRREF.GrowthRecordPure.pureSpqr (Symbolic.Swarm.TRREF.SpqrSemOf.spqrModelOf interpretation)) PureRecvEval.pureSerializeRole
      (inMemAnswers g_rw.sess) m role.peer role 0#256) with ⟨res, calls⟩
  rw [hres] at heval; dsimp only at heval; rcases res with e | ptB; · simp at heval
  simp only [Option.some.injEq, Prod.mk.injEq] at heval; obtain ⟨hst_enc, hpt⟩ := heval; subst hpt
  have h1 : (messageDecryptSignalW (cryptoOf' interpretation) (Proofs.libsignal.SR.interpW interpretation)
      (Symbolic.Swarm.TRREF.GrowthRecordPure.pureSpqr (Symbolic.Swarm.TRREF.SpqrSemOf.spqrModelOf interpretation)) PureRecvEval.pureSerializeRole
      (inMemAnswers g_rw.sess) m role.peer role 0#256).1 = .ok r.message := by rw [hres]
  obtain ⟨st', hdec, _hrid, hstore⟩ := PureRecvEval.storedSession_of_decryptOk (cryptoOf' interpretation) (Proofs.libsignal.SR.interpW interpretation)
    (Symbolic.Swarm.TRREF.GrowthRecordPure.pureSpqr (Symbolic.Swarm.TRREF.SpqrSemOf.spqrModelOf interpretation)) PureRecvEval.pureSerializeRole m role.peer role 0#256 g_rw.sess r.message h1
  have hcalls2 : (messageDecryptSignalW (cryptoOf' interpretation) (Proofs.libsignal.SR.interpW interpretation)
      (Symbolic.Swarm.TRREF.GrowthRecordPure.pureSpqr (Symbolic.Swarm.TRREF.SpqrSemOf.spqrModelOf interpretation)) PureRecvEval.pureSerializeRole
      (inMemAnswers g_rw.sess) m role.peer role 0#256).2 = calls := by rw [hres]
  rw [hcalls2] at hstore
  obtain ⟨remIk, r2, mkGen, newPqrState', pqrKey', hVer, hRem, hSpqr', hDec, hSt', hBr⟩ := Proofs.libsignal.RngG.R3.decryptW_ok_branch hdec
  have hspqr_eq : (Symbolic.Swarm.TRREF.GrowthRecordPure.pureSpqr (Symbolic.Swarm.TRREF.SpqrSemOf.spqrModelOf interpretation)).recv g_rw.sess.state.pqRatchetState m.pqRatchet =
      (Symbolic.Swarm.TRREF.SpqrSemOf.spqrModelOf interpretation).recv g_rw.sess.state.pqRatchetState m.pqRatchet := rfl
  rw [hspqr_eq, hrecv_spqr] at hSpqr'; simp only [Except.ok.injEq, Prod.mk.injEq] at hSpqr'; obtain ⟨rfl, rfl⟩ := hSpqr'
  cases hBr with
  | ratchet ck' _ _ _ _ hFind _ _ _ _ _ _ _ =>
    have hci_none := Proofs.libsignal.RngG.CliPure.R3.findReceiverChainKey_ok_none _ _ hFind
    unfold RatchetState.findReceiverChainIndex at hci_none; rw [List.findIdx?_eq_none_iff] at hci_none
    have hFalse := hci_none rc (List.mem_of_getElem? hrc); simp [hrc_key] at hFalse
  | skipped ck' hFind hLt _ _ =>
    obtain ⟨ci', rc', _, hrc', hsrk', hck'⟩ := Proofs.libsignal.RngG.CliPure.R3.findReceiverChainKey_ok_some _ _ _ hFind
    have hci_eq : ci' = ci := getElem?_receiverChains_inj_of_nodup hnodup hrc' hrc hsrk' hrc_key
    subst hci_eq; cases Option.some.inj (hrc'.symm.trans hrc); cases Option.some.inj (hck'.symm.trans hck)
    exact absurd hLt (BitVec.not_lt.mpr hstep_idx)
  | existing ck' ck_adv ck_next r_adv hFind hNotLt hJump hAdv hNext hSet hMkGen hMac =>
    obtain ⟨ci', rc', _, hrc', hsrk', hck'⟩ := Proofs.libsignal.RngG.CliPure.R3.findReceiverChainKey_ok_some _ _ _ hFind
    have hci_eq : ci' = ci := getElem?_receiverChains_inj_of_nodup hnodup hrc' hrc hsrk' hrc_key
    subst hci_eq; cases Option.some.inj (hrc'.symm.trans hrc); cases Option.some.inj (hck'.symm.trans hck)
    exact ⟨role, remIk, ck_adv, ck_next, r_adv, r2, mkGen, st', rfl, hVer, hRem, hFind, hNotLt, hJump, hAdv, hNext, hSet, hMkGen, hMac, hDec, hSt', by rw [← hst_enc, hstore]⟩

theorem nodup_and_lt_of_existing_tr
    {F : ShaCompress} {their : PublicKey} {counter : BitVec 32} {ck ck_adv ck_next : ChainKey} {r_adv r2 : RatchetState}
    {s s' : CryptoGames.LibsignalSessionApi.Session (List (BitVec 8))}
    (hFind : (ratchetStateOf s.state).findReceiverChainKey their = .ok (some ck)) (hNotLt : ¬ (counter < ck.index))
    (hAdv : Mut.exec (RatchetState.advanceChain F their counter (counter - ck.index).toNat ck) (ratchetStateOf s.state) = (.ok ck_adv, r_adv))
    (hNext : ck_adv.nextChainKey F = .ok ck_next) (hSet : Mut.exec (RatchetState.setReceiverChainKey their ck_next) r_adv = (.ok (), r2))
    (hs' : s'.state.receiverChains = r2.receiverChains) (hwf : RecordChainsWF3 (sessionToRecordRec s)) :
    RecordChainsWF3 (sessionToRecordRec s') := by
  apply recordChainsWF3_of_chainsWFm; rw [hs']
  exact chainsWFm_existing hFind hNotLt hAdv hNext hSet (chainsWFm_of_recordChainsWF3 hwf)

end Symbolic.Swarm.CREF.CliPureRcv.TR.RecvDecStepPure

namespace Symbolic.Swarm.CREF.CliPureRcv.TR.RecvDecStepAtPure
open Symbolic.Swarm.CREF.TR hiding at?_append_of_lt getLocalState_fst newRandoms_append_rnd runMoves_append runTrace_append runTrace_snoc runVis_append runVis_snoc run_bind_fst run_bind_snd
open Symbolic.Swarm.CREF.CliPureRcv.TRPure
open Symbolic.Swarm.CREF.CliPure.TR.RecvDecStep hiding SpqrSem StEntry TREntry
open Symbolic.Swarm.CREF.CliPureRcv.TR.RecvDecStepPure

cref_open
cref_open_tr

open DY DY.Comparse DY.Literal DY.Libsignal
open DY.Libsignal.TripleRatchet (SessionInfo DRState KeyComponent KeyDir RecvChain findRecvChain setRecvChain recvChainFor consumeMessageKey chainKeyAt kdfCk kdfRk maxForwardJumps u32Max computeMac messageVersion createChain x25519LowOrder litByte)
open DY.Libsignal.TripleRatchet
open DY.Libsignal.TripleRatchet.Refinement (wireWhisperTag)
open DY.Libsignal.Refinement (sha256CompressFunction x25519PublicKeySymbol aesCbcEncryptSymbol aesCbcDecryptSymbol ExternCryptoLawsHold encodeWith canonicalVariation WireFields FieldItem PbValue readVarint paddedVarint encodeField readVarint_paddedVarint)
open DY.Libsignal.HwEvents DY.Libsignal.Rust
open CryptoGames CryptoGames.HMAC CryptoGames.HKDF
open CryptoGames.CBC (blockToBytesLE)
open CryptoGames.LibsignalSession CryptoGames.LibsignalSessionApi
open CryptoVerification
open CryptoVerification.LibsignalTripleRatchet CryptoVerification.LibsignalProtoCodec
open CryptoVerification.E2E CryptoVerification.E2E.InMem CryptoVerification.E2E.Record CryptoVerification.E2E.RecordX
open CryptoVerification.E2E.Bin (Role evalOpen storedSession inMemAnswers)
open CryptoVerification.E2E.Pqxdh.WireEntries.SymP3 (RecvWireGhost)
open CryptoVerification.SessionModel (chainStepN skippedKeys)
open CryptoVerification.SessionModel.AdvanceAndFrame
open CryptoProofLib.Refinement (ExternInterpretation)
open Proofs.libsignal.RngG Proofs.libsignal.RngG.R3 Proofs.libsignal.RngG.CliPure.R3
open Proofs.libsignal.Hooks2 (cryptoOf')
open Proofs.libsignal.SR (AesW  messageDecryptSignalW)
open Swarm.Phase0WholeFunctionBridge (sessionToRecordRec sessionToSessionRec senderChainToChainRec receiverChainToChainRec)
open Symbolic.Swarm.CREF Symbolic.Swarm.CREF.CliPure Symbolic.Swarm.CREF.CliPureRcv
open Symbolic.Swarm.CREF.CliPure.TR Symbolic.Swarm.CREF.CliPureRcv.TR
open Symbolic.Swarm.CREF.TR.FreshSigma (at?_eq_some_of_getLocalState_some)
open Symbolic.Swarm.TRREF.SpqrSemOf (spqrModelOf saltToBytes spqrIdx1Bytes
  spqrSendOf_of_send_some spqrKeyBytes_saltToBytes)
open Symbolic.Swarm.CREF.TR.G1 (g1_rep_of_recvRepresentations)
open Symbolic.Swarm.CREF.TR.NoTrWireU (NoTrWireU )
open Symbolic.Swarm.CREF.TR.RecvCol (TRRecvAllCollide)
open Symbolic.Swarm.CREF.TR.RecvRep (decrypt_recvRepresentations_nonempty_of_tryFrom)

/-- Salt-form authentic decrypt representation at a fixed provenance state `st_prov`. -/
def AuthenticDecryptRepB3St (interpretation : ExternInterpretation) (r₀ : ProtocolSetup) (S : SpqrSem)
    (g : Ghost) (ms₁ : List Move) (_body pt : HwBytes) (_t₀ : DY.Bytes) (msg₀ : TRSignalMsg)
    (st_prov : TRState) (_salt seed : DY.Bytes) : Prop :=
  ∃ (st_s : TRState) (t_c coinsLen : Nat),
    st_s ∈ availableStates r₀ (runTraceMoves r₀ ms₁) ∧
    msg₀.pqRatchet = (DY.Spqr.spqrSend st_s.spqr (randTerm t_c coinsLen)).2.2 ∧
    DY.Spqr.spqrEmptyMsg msg₀.pqRatchet = false ∧
    ∃ (pqSalt ptTerm : DY.Bytes),
      pqSalt.AttackerKnows (runTraceMoves r₀ ms₁) ∧
      msg₀.mac = computeMac (trMsgKeys pqSalt seed).macKey st_prov.peerIk st_prov.myIk msg₀.wire ∧
      DY.SymEnc.symDec (trMsgKeys pqSalt seed).cipherKey (trMsgKeys pqSalt seed).iv msg₀.ciphertext = some ptTerm ∧
      gamma interpretation S g ptTerm = pt

end Symbolic.Swarm.CREF.CliPureRcv.TR.RecvDecStepAtPure
