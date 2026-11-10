/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Symbolic.Proofs.Swarm.CREF.RecvWire.AcceptNewRecTieBExclPure
public import Symbolic.Proofs.Swarm.CREF.Cli.Rpk.CHistStepPure
public import Symbolic.Proofs.Swarm.CREF.RecvWire.AcceptSplitPure
public import Symbolic.Proofs.Swarm.CREF.TR.G1.OwnKeyBranch
public import Symbolic.Proofs.Swarm.CREF.TR.RecvDecStepSkippedG1LeavesPure
import Symbolic.Proofs.Swarm.CREF.ModelBridge
import Symbolic.Proofs.Swarm.CREF.ModelSplit
import Symbolic.Proofs.Swarm.CREF.Prelude
import Symbolic.Proofs.Swarm.CREF.RecvWire.AcceptNewRecPendingAPure
import Symbolic.Proofs.Swarm.CREF.RecvWire.AcceptNewRecPendingPure
import Symbolic.Proofs.Swarm.CREF.RecvWire.AcceptNewRecTieAWrapPure
import Symbolic.Proofs.Swarm.CREF.RecvWire.AcceptNewRecTieBRatchetPure
import Symbolic.Proofs.Swarm.CREF.RecvWire.AcceptNewRecTieBSkipWrapPure
import Symbolic.Proofs.Swarm.CREF.TROpen
import Symbolic.Proofs.Swarm.CREF.TR.Leaks -- shake: keep
import Symbolic.Proofs.Swarm.CREF.TR.PQGamma -- shake: keep
import Symbolic.Proofs.Swarm.CREF.TR.PQModelRunNil -- shake: keep

/-!
# Whisper Decrypt Case Dispatcher

Dispatches the three implementation evaluation branches against `Move.decrypt` and
`Move.decryptSkipped` over both `PureCRecRel` input-record forms to the per-branch tie
theorems and cross-branch exclusions.
-/

@[expose] public section

cref_hide_foreign_instances
set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

namespace Symbolic.Swarm.CREF.CliPureRcv.TR.RecvDecStepTiePure
open Symbolic.Swarm.CREF.TR hiding at?_append_of_lt gamma_concat gamma_dhPk getLocalState_fst newRandoms_append_rnd runMoves_append runTrace_append runTrace_snoc runVis_append runVis_snoc run_bind_fst run_bind_snd
open Symbolic.Swarm.CREF Symbolic.Swarm.CREF.CliPure Symbolic.Swarm.CREF.CliPureRcv
open Symbolic.Swarm.CREF.CliPureRcv.RecvWirePure
open Symbolic.Swarm.CREF.CliPure.TR Symbolic.Swarm.CREF.CliPureRcv.TR
open Symbolic.Swarm.CREF.CliPure.TR.RecvDecStep hiding SpqrSem StEntry TREntry
open Symbolic.Swarm.CREF.CliPureRcv.TR.RecvDecStepPure
open Symbolic.Swarm.CREF.CliPure.TR.RecvDecStepAt

cref_open
cref_open_tr

open DY DY.Comparse DY.Literal DY.Libsignal
open DY.Libsignal.TripleRatchet
open DY.Libsignal.TripleRatchet.Refinement (wireWhisperTag)
open DY.Libsignal.Refinement (ExternCryptoLawsHold)
open DY.Libsignal.HwEvents DY.Libsignal.Rust
open CryptoGames CryptoGames.HKDF
open CryptoGames.LibsignalSession CryptoGames.LibsignalSessionApi
open CryptoVerification.LibsignalTripleRatchet CryptoVerification.LibsignalProtoCodec
open CryptoVerification.E2E CryptoVerification.E2E.InMem CryptoVerification.E2E.Record
open CryptoVerification.E2E.Bin hiding RecordCanonical recordDeserializeOpenSpec encodeRecord
open CryptoVerification.E2E.Pqxdh.WireEntries
open CryptoVerification.E2E.Pqxdh.WireEntries.SymP3 hiding encodeRecord
open CryptoProofLib.Refinement (ExternInterpretation)
open Proofs.libsignal.Hooks2
open Symbolic.Swarm.CREF Symbolic.Swarm.CREF.CliPure Symbolic.Swarm.CREF.CliPureRcv
open Symbolic.Swarm.CREF.CliPure.TR Symbolic.Swarm.CREF.CliPureRcv.TR

/-- Run invariants at `ms = ms₀ ++ pre` used by the receive case dispatch. -/
structure A2bRunFacts (interpretation : ExternInterpretation) (r₀ : ProtocolSetup) (S : OpaqueSymbolSemantics)
    (g : Ghost) (ms : List Move) (acc : List MachineEvent) : Prop where
  role : RoleSnapshots r₀ (runTraceMoves r₀ ms)
  atF : RecvDecStepAt.RecvAtFacts interpretation r₀ S g ms
  abs' : Symbolic.Swarm.CREF.TR.G1.G1cAttackerBuiltSeedExcl' interpretation r₀ S g ms
  seedEq : A2bSkStepSeedEq interpretation r₀ S g ms acc

theorem a2b_modelRun_pre {interpretation : ExternInterpretation} {r₀ : ProtocolSetup} {S : OpaqueSymbolSemantics}
    {who : List Participant} {g : Ghost} {ms₀ pre post : List Move} {m : Move} {acc blk : List MachineEvent}
    (hB : XplBlock interpretation r₀ S who g ms₀ (pre ++ m :: post) acc blk) :
    ModelRun r₀ (ms₀ ++ pre) := by
  have hreach : (runTraceMoves r₀ (ms₀ ++ pre)).Reachable reachability := by
    have h := hB.run.2.2.1.2.2 (ms₀ ++ pre).length
    rwa [← List.append_assoc, List.take_left] at h
  have h := hB.run
  rw [← List.append_assoc] at h
  exact modelRun_prefix_of_reachable h hreach

/-- Three-way evaluation branch disjunction for `pureEvalRecvWireWithCoinsW`. -/
def A2bBranches (g_rw : RecvWireGhost) (m : SignalMessage) (mid : List MachineEvent)
    (coins : BitVec 256) : Prop :=
  (∃ (ci : Nat) (rc : ReceiverChain) (ck : ChainKey),
    mid = [] ∧ coins = 0#256 ∧
    g_rw.sess.state.receiverChains[ci]? = some rc ∧
    rc.senderRatchetKey = m.senderRatchetKey ∧
    rc.chainKey = some ck ∧ m.counter < ck.index) ∨
  (∃ (ci : Nat) (rc : ReceiverChain) (ck : ChainKey),
    mid = [] ∧ coins = 0#256 ∧
    g_rw.sess.state.receiverChains[ci]? = some rc ∧
    rc.senderRatchetKey = m.senderRatchetKey ∧
    rc.chainKey = some ck ∧ ck.index ≤ m.counter) ∨
  (∃ rngBytes : HwBytes,
    mid = [.rng rngBytes] ∧ rngBytes.length = 32 ∧
    coins = Symbolic.Swarm.CREF.CliPureRcv.TR.RecvDecStepPure.purePinCoins (some rngBytes) ∧
    (∀ rc ∈ g_rw.sess.state.receiverChains, rc.senderRatchetKey ≠ m.senderRatchetKey))

theorem a2b_rcvAccBlk_acc (body : HwBytes) (mid : List MachineEvent) (r : StateAndMessage) :
    ∃ e ∈ rcvAccBlk body mid r, eventKind e = .accept :=
  ⟨.accept r.message, by simp [rcvAccBlk], rfl⟩

theorem a2b_rcvAccBlk_nil_no_rng (body : HwBytes) (r : StateAndMessage) :
    ∀ e ∈ rcvAccBlk body [] r, eventKind e ≠ .rng := by
  intro e he
  rcases he with _ | ⟨_, _ | ⟨_, he⟩⟩
  · intro h; cases h
  · intro h; cases h
  · cases he

theorem a2b_rcvAccBlk_rng (body rngBytes : HwBytes) (r : StateAndMessage) :
    ∃ e ∈ rcvAccBlk body [.rng rngBytes] r, eventKind e = .rng :=
  ⟨.rng rngBytes, by simp [rcvAccBlk], rfl⟩

/-- Preserves `PureTRRecordStateInv` and `TRNsBound` across `Move.decrypt` in an accepting block. -/
theorem a2b_tie_decrypt
    (interpretation : ExternInterpretation) (hceh : ExternCryptoLawsHold interpretation)
    (r₀ : ProtocolSetup) (hwf : ProtocolSetupWF r₀) (hik : IkShape interpretation r₀)
    (S : OpaqueSymbolSemantics) (hS : S = compSemOf interpretation r₀)
    {who : List Participant}
    (g : Ghost) (ms₀ pre post : List Move) (acc mid : List MachineEvent) (sent : List HwBytes)
    (p : Participant) (stateIdx msgIdx pqIdx : Nat) (spqrMsgIdx : UInt32) (wrapped : Bool)
    (rec body : HwBytes) (r : StateAndMessage)
    (hB : XplBlock interpretation r₀ S who g ms₀
      (pre ++ .decrypt p stateIdx msgIdx pqIdx spqrMsgIdx wrapped :: post) acc
      (rcvAccBlk body mid r))
    (hpre : MovesFrom InvisibleNoEffect (runTraceMoves r₀ ms₀) pre)
    (hpost : MovesFrom InvisibleNoEffect
      ((Move.decrypt p stateIdx msgIdx pqIdx spqrMsgIdx wrapped).next
        (runMoves pre (runTraceMoves r₀ ms₀)).1) post)
    (hnocol : ∀ t, rcvMoveTerm (runTraceMoves r₀ (ms₀ ++ pre))
        (.decrypt p stateIdx msgIdx pqIdx spqrMsgIdx wrapped) = some t →
      ¬ RecvCollision interpretation r₀ S g (ms₀ ++ pre) t)
    (hcurR : RcvCurrentRead interpretation r₀ S g (ms₀ ++ pre) body
      (.decrypt p stateIdx msgIdx pqIdx spqrMsgIdx wrapped))
    (hrel : PureCRecRel interpretation r₀ S g (ms₀ ++ pre) p rec)
    (hns : TRNsBound r₀ (ms₀ ++ pre) sent)
    (hF : A2bRunFacts interpretation r₀ S g (ms₀ ++ pre) acc)
    (g_rw : RecvWireGhost) (coins : BitVec 256) (m : SignalMessage)
    (newPqrState : HwBytes) (pqrKey : HKDF.Salt)
    (hstate_lt : r.state.length < 2 ^ 64)
    (hcanon' : r.state.length < 2 ^ 32 - 2 ^ 20 → (pureTrSlots r₀).canon p r.state)
    (hwho : g_rw.who = if p = r₀.alice then 0 else 1)
    (hwire : g_rw.wireBytes = wireWhisperTag :: body)
    (hcanon_q : TR.Pure.slots_RecordCanonical_Q TR.Pure.slots_NonEmptyV1Q rec g_rw.sess)
    (hcoins_ok : ∀ msg, SignalMessage.tryFrom protoSignalCodec body = .ok msg →
        TR.PureRecvEval.PureDecryptCoinsOk (cryptoOf' interpretation) g_rw.sess.state msg.senderRatchetKey coins)
    (heval : TR.PureRecvEval.pureEvalRecvWireWithCoinsW (cryptoOf' interpretation) (Proofs.libsignal.SR.interpW interpretation)
        (Symbolic.Swarm.TRREF.SpqrSemOf.spqrModelOf interpretation) g_rw coins =
        some (r.state, r.message))
    (htry : SignalMessage.tryFrom protoSignalCodec body = .ok m)
    (hrecv_spqr : (Symbolic.Swarm.TRREF.SpqrSemOf.spqrModelOf interpretation).recv
        g_rw.sess.state.pqRatchetState m.pqRatchet = .ok (newPqrState, pqrKey))
    (hbr : A2bBranches g_rw m mid coins) :
    PureTRRecordStateInv interpretation r₀ S (pureTrSlots r₀) g
        (ms₀ ++ pre ++ [.decrypt p stateIdx msgIdx pqIdx spqrMsgIdx wrapped])
        (fun q => if q = p then some r.state else none) ∧
      TRNsBound r₀ (ms₀ ++ pre ++ [.decrypt p stateIdx msgIdx pqIdx spqrMsgIdx wrapped]) sent := by
  have hacc := a2b_rcvAccBlk_acc body mid r
  rcases hbr with ⟨ci, rc, ck, hmid, hcoins, hrc, hrc_key, hck, hidx⟩ |
      ⟨ci, rc, ck, hmid, hcoins, hrc, hrc_key, hck, hidx⟩ |
      ⟨rngBytes, hmid, hrng_len, hcoins, hrc_none⟩
  ·
    subst hmid hcoins
    exfalso
    rcases hrel with hrr | ⟨hp, hpend⟩
    · exact a2b_not_decrypt_of_binSkip interpretation r₀ S g ms₀ pre post acc _ p stateIdx msgIdx
        pqIdx spqrMsgIdx wrapped rec body hB hpre hpost (a2b_rcvAccBlk_nil_no_rng body r) hacc hcurR
        hrr hF.role g_rw m ci rc ck hcanon_q htry hrc hrc_key hck hidx
    · exact a2b_not_decrypt_of_binSkip_pending interpretation r₀ S g ms₀ pre post acc _ p stateIdx
        msgIdx pqIdx spqrMsgIdx wrapped rec body hB hpre hpost (a2b_rcvAccBlk_nil_no_rng body r) hacc
        hcurR hp hpend hF.role g_rw m ci rc ck hcanon_q htry hrc hrc_key hck hidx
  ·
    subst hmid hcoins
    rcases hrel with hrr | ⟨hp, hpend⟩
    · exact a2b_tieA_of_block interpretation hceh r₀ hwf S hS g ms₀ pre post acc _ sent p stateIdx
        msgIdx pqIdx spqrMsgIdx wrapped rec body hB hpre hpost (a2b_rcvAccBlk_nil_no_rng body r) hacc
        hcurR hrr hns hF.role hF.atF r g_rw m ci rc ck newPqrState pqrKey hstate_lt hcanon' hwire
        hcanon_q htry hrc hrc_key hck hidx hrecv_spqr heval
    · exact a2b_tieA_pending_of_block interpretation hceh r₀ hwf S hS g ms₀ pre post acc _ sent p
        stateIdx msgIdx pqIdx spqrMsgIdx wrapped rec body hB hpre hpost
        (a2b_rcvAccBlk_nil_no_rng body r) hacc hcurR hp hpend hns hF.role hF.atF r g_rw m ci rc ck
        newPqrState pqrKey hstate_lt hcanon' hwire hcanon_q htry hrc hrc_key hck hidx hrecv_spqr heval
  ·
    subst hmid hcoins
    have hcok := hcoins_ok m htry
    rcases hrel with hrr | ⟨hp, hpend⟩
    · exact a2b_tieB_ratchet_of_block interpretation hceh r₀ hwf hik S hS g ms₀ pre post acc
        sent p stateIdx msgIdx pqIdx spqrMsgIdx wrapped rec body rngBytes r hB hpre hpost hnocol hcurR
        hrr hns hF.role hF.atF hF.abs' g_rw m newPqrState pqrKey hstate_lt hcanon' hwho hwire hcanon_q
        hrng_len htry hrc_none hcok hrecv_spqr heval
    · exact a2b_tieB_ratchet_pending_of_block interpretation hceh r₀ hwf hik S hS g ms₀ pre
        post acc sent p stateIdx msgIdx pqIdx spqrMsgIdx wrapped rec body rngBytes r hB hpre hpost
        hnocol hcurR hp hpend hns hF.role hF.atF hF.abs' g_rw m newPqrState pqrKey hstate_lt hcanon'
        hwho hwire hcanon_q hrng_len htry hrc_none hcok hrecv_spqr heval

/-- Preserves `PureTRRecordStateInv` and `TRNsBound` across `Move.decryptSkipped` in an accepting block. -/
theorem a2b_tie_decryptSkipped
    (interpretation : ExternInterpretation) (hceh : ExternCryptoLawsHold interpretation)
    (r₀ : ProtocolSetup) (S : OpaqueSymbolSemantics) (hS : S = compSemOf interpretation r₀)
    {who : List Participant}
    (g : Ghost) (ms₀ pre post : List Move) (acc mid : List MachineEvent) (sent : List HwBytes)
    (p : Participant) (stateIdx msgIdx skIdx pqIdx : Nat) (spqrMsgIdx : UInt32) (wrapped : Bool)
    (rec body : HwBytes) (r : StateAndMessage)
    (hB : XplBlock interpretation r₀ S who g ms₀
      (pre ++ .decryptSkipped p stateIdx msgIdx skIdx pqIdx spqrMsgIdx wrapped :: post) acc
      (rcvAccBlk body mid r))
    (hpre : MovesFrom InvisibleNoEffect (runTraceMoves r₀ ms₀) pre)
    (hpost : MovesFrom InvisibleNoEffect
      ((Move.decryptSkipped p stateIdx msgIdx skIdx pqIdx spqrMsgIdx wrapped).next
        (runMoves pre (runTraceMoves r₀ ms₀)).1) post)
    (hnocol : ∀ t, rcvMoveTerm (runTraceMoves r₀ (ms₀ ++ pre))
        (.decryptSkipped p stateIdx msgIdx skIdx pqIdx spqrMsgIdx wrapped) = some t →
      ¬ RecvCollision interpretation r₀ S g (ms₀ ++ pre) t)
    (hcurR : RcvCurrentRead interpretation r₀ S g (ms₀ ++ pre) body
      (.decryptSkipped p stateIdx msgIdx skIdx pqIdx spqrMsgIdx wrapped))
    (hrel : PureCRecRel interpretation r₀ S g (ms₀ ++ pre) p rec)
    (hns : TRNsBound r₀ (ms₀ ++ pre) sent)
    (hF : A2bRunFacts interpretation r₀ S g (ms₀ ++ pre) acc)
    (g_rw : RecvWireGhost) (coins : BitVec 256) (m : SignalMessage)
    (newPqrState : HwBytes) (pqrKey : HKDF.Salt)
    (hstate_lt : r.state.length < 2 ^ 64)
    (hcanon' : r.state.length < 2 ^ 32 - 2 ^ 20 → (pureTrSlots r₀).canon p r.state)
    (hwire : g_rw.wireBytes = wireWhisperTag :: body)
    (hcanon_q : TR.Pure.slots_RecordCanonical_Q TR.Pure.slots_NonEmptyV1Q rec g_rw.sess)
    (heval : TR.PureRecvEval.pureEvalRecvWireWithCoinsW (cryptoOf' interpretation) (Proofs.libsignal.SR.interpW interpretation)
        (Symbolic.Swarm.TRREF.SpqrSemOf.spqrModelOf interpretation) g_rw coins =
        some (r.state, r.message))
    (htry : SignalMessage.tryFrom protoSignalCodec body = .ok m)
    (hrecv_spqr : (Symbolic.Swarm.TRREF.SpqrSemOf.spqrModelOf interpretation).recv
        g_rw.sess.state.pqRatchetState m.pqRatchet = .ok (newPqrState, pqrKey))
    (hbr : A2bBranches g_rw m mid coins) :
    PureTRRecordStateInv interpretation r₀ S (pureTrSlots r₀) g
        (ms₀ ++ pre ++ [.decryptSkipped p stateIdx msgIdx skIdx pqIdx spqrMsgIdx wrapped])
        (fun q => if q = p then some r.state else none) ∧
      TRNsBound r₀ (ms₀ ++ pre ++ [.decryptSkipped p stateIdx msgIdx skIdx pqIdx spqrMsgIdx wrapped])
        sent := by
  have hacc := a2b_rcvAccBlk_acc body mid r
  rcases hbr with ⟨ci, rc, ck, hmid, hcoins, hrc, hrc_key, hck, hidx⟩ |
      ⟨ci, rc, ck, hmid, hcoins, hrc, hrc_key, hck, hidx⟩ |
      ⟨rngBytes, hmid, hrng_len, hcoins, hrc_none⟩
  ·
    subst hmid hcoins
    rcases hrel with hrr | ⟨hp, hpend⟩
    · exact a2b_tieB_skip_of_block interpretation hceh r₀ S hS g ms₀ pre post acc _ sent p
        stateIdx msgIdx skIdx pqIdx spqrMsgIdx wrapped rec body hB hpre hpost hacc hcurR hrr hns
        hF.role hF.atF r g_rw m ci rc ck newPqrState pqrKey hstate_lt hcanon' hwire hcanon_q htry hrc
        hrc_key hck hidx hrecv_spqr heval
    · exact a2b_tieB_skip_pending_of_block interpretation r₀ S g ms₀ pre sent p stateIdx msgIdx
        skIdx pqIdx spqrMsgIdx wrapped rec body hpend r g_rw m ci rc ck newPqrState pqrKey hwire
        hcanon_q htry hrc hrc_key hck hidx hrecv_spqr heval
  ·
    subst hmid hcoins
    exfalso
    have hsklin : SkippedSeedNeChainSeed r₀ (ms₀ ++ pre) :=
      skippedSeed_ne_chainSeed (a2b_modelRun_pre hB)
    rcases hrel with hrr | ⟨hp, hpend⟩
    · exact a2b_not_decryptSkipped_of_binStep interpretation r₀ S g ms₀ pre post acc _ p stateIdx
        msgIdx skIdx pqIdx spqrMsgIdx wrapped rec body hB hpre hpost hacc hnocol hcurR _ hrr hF.role
        hF.atF hsklin hF.seedEq r g_rw m ci rc ck hwire hcanon_q htry hrc hrc_key hck hidx heval
        newPqrState pqrKey hrecv_spqr
    · exact a2b_not_decryptSkipped_of_binStep interpretation r₀ S g ms₀ pre post acc _ p stateIdx
        msgIdx skIdx pqIdx spqrMsgIdx wrapped rec body hB hpre hpost hacc hnocol hcurR _
        (trRecordStateInv_pend_of_aliceInitPending hp hpend) hF.role hF.atF hsklin hF.seedEq
        r g_rw m ci rc ck hwire hcanon_q htry hrc hrc_key hck hidx heval newPqrState pqrKey hrecv_spqr
  ·
    subst hmid hcoins
    exact (a2b_not_decryptSkipped_of_rng interpretation r₀ S g ms₀ pre post acc _ p stateIdx msgIdx
      skIdx pqIdx spqrMsgIdx wrapped hB hpre hpost hacc (a2b_rcvAccBlk_rng body rngBytes r)).elim

theorem a2b_trRecvFreshAll_of_quietExt {r₀ : ProtocolSetup} {ms ms' : List Move}
    (hq : PureXplQuiet.QuietExt (runTraceMoves r₀ ms) (runTraceMoves r₀ ms'))
    (h : TRRecvFreshAll r₀ ms) : TRRecvFreshAll r₀ ms' := by
  intro q stateIdx st hqab hget hcur
  rw [PureXplQuiet.quiet_getLocalState hq] at hget
  rw [PureXplQuiet.quiet_isCurrentSnapshot hq] at hcur
  obtain ⟨hc, hs⟩ := h q stateIdx st hqab hget hcur
  exact ⟨trRecvCountersFresh_of_imp
      (fun _ _ _ _ _ _ hl => (PureXplQuiet.quiet_eventLoggedAt hq _ _).mp hl)
      (fun _ _ _ _ _ _ hl => (PureXplQuiet.quiet_eventLoggedAt hq _ _).mp hl) hc,
    trSkippedRIdxChainRel_of_imp
      (fun _ _ _ _ _ _ hl => (PureXplQuiet.quiet_eventLoggedAt hq _ _).mp hl) hs⟩

theorem a2b_recvAtFacts_of_quietPre {interpretation : ExternInterpretation} {r₀ : ProtocolSetup}
    {S : OpaqueSymbolSemantics} {g : Ghost} {ms₀ pre : List Move}
    (hpre : MovesFrom InvisibleNoEffect (runTraceMoves r₀ ms₀) pre)
    (hhist : TR.CHistStep.CHist interpretation r₀ S g ms₀)
    (hfresh : TRRecvFreshAll r₀ ms₀) :
    RecvDecStepAt.RecvAtFacts interpretation r₀ S g (ms₀ ++ pre) := by
  have hq := a2b_quietPre hpre
  obtain ⟨hlen, hlow, hbf, hh⟩ := PureXplQuiet.quiet_cHist hq hhist
  exact ⟨hlen, hlow, hbf, hh, a2b_trRecvFreshAll_of_quietExt hq hfresh⟩

theorem a2b_roleSnapshots_of_quietPre {r₀ : ProtocolSetup} {ms₀ pre : List Move}
    (hpre : MovesFrom InvisibleNoEffect (runTraceMoves r₀ ms₀) pre)
    (hrole : RoleSnapshots r₀ (runTraceMoves r₀ ms₀)) :
    RoleSnapshots r₀ (runTraceMoves r₀ (ms₀ ++ pre)) := by
  rw [runTrace_append]
  exact roleSnapshots_of_movesFrom_noSessionEffect
    (movesFrom_mono (fun _ _ h => h.2) _ _ hpre) hrole

theorem a2b_runFacts_of_quietPre {interpretation : ExternInterpretation} {r₀ : ProtocolSetup}
    {S : OpaqueSymbolSemantics} {g : Ghost} {ms₀ pre : List Move} {acc : List MachineEvent}
    (hpre : MovesFrom InvisibleNoEffect (runTraceMoves r₀ ms₀) pre)
    (hrole : RoleSnapshots r₀ (runTraceMoves r₀ ms₀))
    (hhist : TR.CHistStep.CHist interpretation r₀ S g ms₀)
    (hfresh : TRRecvFreshAll r₀ ms₀)
    (habs : G1.G1cAttackerBuiltSeedExcl' interpretation r₀ S g (ms₀ ++ pre))
    (hseed : A2bSkStepSeedEq interpretation r₀ S g (ms₀ ++ pre) acc) :
    A2bRunFacts interpretation r₀ S g (ms₀ ++ pre) acc :=
  ⟨a2b_roleSnapshots_of_quietPre hpre hrole, a2b_recvAtFacts_of_quietPre hpre hhist hfresh,
    habs, hseed⟩

theorem a2b_runFacts_of_cHistBy {interpretation : ExternInterpretation} {r₀ : ProtocolSetup}
    {S : OpaqueSymbolSemantics} {g : Ghost} {ms₀ pre : List Move} {acc : List MachineEvent}
    (hpre : MovesFrom InvisibleNoEffect (runTraceMoves r₀ ms₀) pre)
    (hch : CHistBy interpretation r₀ S g ms₀)
    (hfresh : TRRecvFreshAll r₀ ms₀)
    (habs : G1.G1cAttackerBuiltSeedExcl' interpretation r₀ S g (ms₀ ++ pre))
    (hseed : A2bSkStepSeedEq interpretation r₀ S g (ms₀ ++ pre) acc) :
    A2bRunFacts interpretation r₀ S g (ms₀ ++ pre) acc :=
  a2b_runFacts_of_quietPre hpre hch.2 hch.1 hfresh habs hseed

end Symbolic.Swarm.CREF.CliPureRcv.TR.RecvDecStepTiePure
