/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

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
public import Symbolic.Proofs.Swarm.CREF.Cli.PureCRel
public import Symbolic.Proofs.Swarm.CREF.Cli.Rpk.RecvDecStepCommonPureA
public import Symbolic.Proofs.Swarm.CREF.TR.RecvDec
import Symbolic.Proofs.Swarm.CREF.ModelBridge
import Symbolic.Proofs.Swarm.CREF.Prelude
import Symbolic.Proofs.Swarm.CREF.TR.RecvDecStepSkippedG1LeavesPure
import Symbolic.Proofs.Swarm.CREF.TR.Leaks -- shake: keep
import Symbolic.Proofs.Swarm.CREF.TR.PQModelRunNil -- shake: keep
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
# Cached Skipped-Key Decrypt Step Lemmas

Trace equation and `TRNsBound`, `PureTRRecordStateInv`, and skipped-key preservation lemmas for
`Move.decryptSkipped` at an arbitrary trace `runTraceMoves r₀ ms`.
-/

@[expose] public section

set_option autoImplicit false

cref_hide_foreign_instances

namespace Symbolic.Swarm.CREF.CliPureRcv.TR.RecvDecStepPure
open Symbolic.Swarm.CREF.TR hiding SpqrSem at?_append_of_lt compromisesCurrentFrom_append forall₂_append getLocalState_fst getLocalState_snd newRandoms_append_rnd ownSaltsFrom_append runMoves_append runTrace_append runTrace_snoc runVis_append runVis_snoc run_bind_fst run_bind_snd
open Symbolic.Swarm.CREF.CliPure.TR.RecvDecStep

cref_open

open DY DY.Comparse DY.Literal DY.Libsignal DY.DiffieHellman
open DY.Libsignal.TripleRatchet (computeMac messageVersion)
open DY.Libsignal.TripleRatchet
open CryptoVerification.E2E CryptoVerification.E2E.InMem CryptoVerification.E2E.Record CryptoVerification.E2E.RecordX
open CryptoProofLib.Refinement (ExternInterpretation)
open Symbolic.Swarm.CREF Symbolic.Swarm.CREF.CliPure Symbolic.Swarm.CREF.CliPureRcv
open Symbolic.Swarm.CREF.CliPure.TR Symbolic.Swarm.CREF.CliPureRcv.TR
open Symbolic.Swarm.CREF.TR.RecvDec hiding StEntry TREntry
  at?_append_of_lt at?_eq_none_of_le trace_snoc_at_length trace_append_at_length
  at?_append_non_entry isCurrentSnapshot_append_non_st logSkippedKeysTr logSkippedKeysTr_length
  at?_trEntry_logSkippedKeysTr_lt decTailTr decTailTr_length at?_trEntry_decTailTr_lt
  run_bind_fst run_bind_snd getLocalState_fst

theorem a2b_runTrace_decryptSkipped
    {r₀ : ProtocolSetup} {ms : List Move} {p : Participant} {stateIdx msgIdx skIdx pqIdx rIdx srcIdx : Nat}
    {spqrMsgIdx : UInt32} {wrapped : Bool}
    {st : TRState} {t seed key pqSalt ptTerm spqr' : DY.Bytes} {msg : TRSignalMsg}
    (hst : ((PersistentLocalState.getLocalState p stateIdx : Traceful TRState).run
      (runTraceMoves r₀ ms)).1 = some st)
    (hmsg : (runTraceMoves r₀ ms).getMessageSentAt msgIdx = some t)
    (hparse : parseTrSignalMsg t = some msg) (hver : msg.version = messageVersion)
    (hsk : ((runTraceMoves r₀ ms).at? skIdx : Option TREntry) =
      some ⟨TREvent.SkippedKeyStored (st.sessionInfo p) msg.ratchetKey msg.counter seed rIdx srcIdx⟩)
    (hunused : skippedKeyUsedB (runTraceMoves r₀ ms) skIdx = false)
    (hspqr : Spqr.spqrRecv st.spqr msg.pqRatchet spqrMsgIdx = some (spqr', key))
    (hpqSalt : (((runTraceMoves r₀ ms).append (⟨key⟩ : Network.ExecEntryT)).at? pqIdx :
      Option Network.ExecEntryT) = some ⟨pqSalt⟩)
    (hmac_eq : msg.mac = computeMac (trMsgKeys pqSalt seed).macKey st.peerIk st.myIk msg.wire)
    (hdec : DY.SymEnc.symDec (trMsgKeys pqSalt seed).cipherKey (trMsgKeys pqSalt seed).iv
      msg.ciphertext = some ptTerm)
    (hfind : (findRecvChain st.toDRState.recv msg.ratchetKey).isSome = true) :
    runTraceMoves r₀ (ms ++ [.decryptSkipped p stateIdx msgIdx skIdx pqIdx spqrMsgIdx wrapped]) =
      decSkippedTr (runTraceMoves r₀ ms) p stateIdx skIdx rIdx srcIdx st msg.ratchetKey seed key
        pqSalt ptTerm spqr' msg.counter := by
  rw [runTrace_snoc]
  exact decryptSkipped_next_eq hst hmsg hparse hver hsk hunused hspqr hpqSalt hmac_eq hdec hfind

theorem a2b_trNsBound_decSkipped
    {r₀ : ProtocolSetup} {ms : List Move} {sent : List HwBytes} {m : Move}
    {p : Participant} {stateIdx skIdx rIdx srcIdx : Nat} {st : TRState}
    {pk seed key pqSalt ptTerm spqr' : DY.Bytes} {n : UInt32}
    (hns : TRNsBound r₀ ms sent)
    (hst : ((PersistentLocalState.getLocalState p stateIdx : Traceful TRState).run
      (runTraceMoves r₀ ms)).1 = some st)
    (htr : runTraceMoves r₀ (ms ++ [m]) =
      decSkippedTr (runTraceMoves r₀ ms) p stateIdx skIdx rIdx srcIdx st pk seed key pqSalt ptTerm
        spqr' n) :
    TRNsBound r₀ (ms ++ [m]) sent := by
  let tr2 := (((runTraceMoves r₀ ms).append (⟨key⟩ : Network.ExecEntryT)).append
    (⟨TREvent.SkippedKeyUsed (st.sessionInfo p) skIdx⟩ : TREntry)).append
    (⟨TREvent.Received p st.peer pk n ptTerm⟩ : TREntry)
  let tr_mid := tr2.append (⟨TREvent.MessageKey (st.sessionInfo p) .receiver seed pqSalt n rIdx stateIdx⟩ : TREntry)
  refine trNsBound_of_append_stEntry (tr₀ := tr_mid) (me := p) (st' := { st with spqr := spqr' })
    htr (fun i => ?_) (hns p stateIdx st hst) hns
  dsimp only [tr_mid, tr2]
  rw [at?_append_non_entry _ _ rfl, at?_append_non_entry _ _ rfl, at?_append_non_entry _ _ rfl,
      at?_append_non_entry _ _ rfl]

/-- Establishes `PureTRRecordStateInv` for the singleton table at `p` after a `decSkippedTr` step. -/
theorem a2b_trRecordStateInv_decSkipped_single
    {interpretation : ExternInterpretation} {r₀ : ProtocolSetup} {S : SpqrSem} {Z : PureTRSlots}
    {g : Ghost} {ms : List Move} {m : Move}
    {p : Participant} {stateIdx skIdx rIdx srcIdx : Nat} {st : TRState} {rec' : RecordRec}
    {newBytes : HwBytes} {pk seed key pqSalt ptTerm spqr' : DY.Bytes} {n : UInt32}
    (hp_mem : p = r₀.alice ∨ p = r₀.bob)
    (htr : runTraceMoves r₀ (ms ++ [m]) =
      decSkippedTr (runTraceMoves r₀ ms) p stateIdx skIdx rIdx srcIdx st pk seed key pqSalt ptTerm
        spqr' n)
    (hnew : newBytes = recordBytes rec')
    (hrel' : StateRel interpretation S g { st with spqr := spqr' } rec')
    (hsk' : ∀ c_k ∈ rec'.current.receiverChains, ∀ k ∈ c_k.messageKeys,
      ∃ pk_k rIdx_k srcIdx_k skIdx_k seed_k,
        (runTraceMoves r₀ (ms ++ [m])).EventLoggedAt
          (TREvent.SkippedKeyStored (st.sessionInfo p) pk_k (UInt32.ofBitVec k.1) seed_k rIdx_k srcIdx_k)
          skIdx_k ∧
        !skippedKeyUsedB (runTraceMoves r₀ (ms ++ [m])) skIdx_k ∧
        !receiverKeyUsedB (runTraceMoves r₀ (ms ++ [m])) (st.sessionInfo p) seed_k (UInt32.ofBitVec k.1)
          rIdx_k ∧
        gamma interpretation S g seed_k = k.2 ∧
        c_k.senderRatchetKey = serializedKey (gamma interpretation S g pk_k) ∧
        (findRecvChain st.toDRState.recv pk_k).isSome = true)
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
    refine ⟨hp_mem, rec', { st with spqr := spqr' }, (runTraceMoves r₀ ms).length + 4, hnew, ?_, ?_,
      hrel', hsk', hcanon', (trKeyShape_with_spqr_g1 interpretation S g st spqr').mpr hks, hnd'⟩
    · rw [htr]; exact getLocalState_decSkippedTr_last_g1 _ _ _ _ _ _ _ _ _ _ _ _ _ _
    · rw [htr]; exact isCurrentSnapshot_decSkippedTr_last_g1 _ _ _ _ _ _ _ _ _ _ _ _ _ _
  · simp only [hqp, ↓reduceIte] at hqb; cases hqb

/-- Preserves skipped-key ghost invariants across `decSkippedTr` for any unconsumed
`(seed, ctr, rIdx)` triple. -/
theorem a2b_hsk'_decSkipped
    {interpretation : ExternInterpretation} {S : SpqrSem} {g : Ghost}
    {tr : ExecTrace} {p : Participant} {stateIdx skIdx rIdx srcIdx : Nat} {st : TRState}
    {pk seed key pqSalt ptTerm spqr' : DY.Bytes} {ctr : UInt32}
    {pk_k seed_k : DY.Bytes} {rIdx_k srcIdx_k skIdx_k : Nat} {k : BitVec 32 × HwBytes}
    {srk : HwBytes}
    (hsk : (tr.at? skIdx : Option TREntry) =
      some ⟨TREvent.SkippedKeyStored (st.sessionInfo p) pk ctr seed rIdx srcIdx⟩)
    (hlog : tr.EventLoggedAt
      (TREvent.SkippedKeyStored (st.sessionInfo p) pk_k (UInt32.ofBitVec k.1) seed_k rIdx_k srcIdx_k)
      skIdx_k)
    (hsu : (!skippedKeyUsedB tr skIdx_k) = true)
    (hru : (!receiverKeyUsedB tr (st.sessionInfo p) seed_k (UInt32.ofBitVec k.1) rIdx_k) = true)
    (hgam : gamma interpretation S g seed_k = k.2)
    (hpk_ser : srk = serializedKey (gamma interpretation S g pk_k))
    (hfind_k : (findRecvChain st.toDRState.recv pk_k).isSome = true)
    (hne : ¬ (seed = seed_k ∧ ctr = UInt32.ofBitVec k.1 ∧ rIdx = rIdx_k)) :
    let tr_post := decSkippedTr tr p stateIdx skIdx rIdx srcIdx st pk seed key pqSalt ptTerm
      spqr' ctr
    tr_post.EventLoggedAt (TREvent.SkippedKeyStored (st.sessionInfo p) pk_k
      (UInt32.ofBitVec k.1) seed_k rIdx_k srcIdx_k) skIdx_k ∧
    (!skippedKeyUsedB tr_post skIdx_k) = true ∧
    (!receiverKeyUsedB tr_post (st.sessionInfo p) seed_k (UInt32.ofBitVec k.1) rIdx_k) = true ∧
    gamma interpretation S g seed_k = k.2 ∧ srk = serializedKey (gamma interpretation S g pk_k) ∧
    (findRecvChain st.toDRState.recv pk_k).isSome = true := by
  intro tr_post
  have hsk_ne : skIdx ≠ skIdx_k := by
    intro hEq; subst hEq
    have hlog_at := (Symbolic.DYBridge.DY.Trace.EventLoggedAt_eq_1 _ _ _).mp hlog
    rw [hsk] at hlog_at; injection hlog_at with hEntry; injection hEntry with hEv
    injection hEv with _ _ hCtr hSeed hRIdx _; exact hne ⟨hSeed, hCtr, hRIdx⟩
  have hsu' : skippedKeyUsedB tr skIdx_k = false := by simpa using hsu
  have hru' : receiverKeyUsedB tr (st.sessionInfo p) seed_k (UInt32.ofBitVec k.1) rIdx_k = false := by
    simpa using hru
  refine ⟨?_, ?_, ?_, hgam, hpk_ser, hfind_k⟩
  · exact eventLoggedAt_decSkippedTr_of_old_g1 tr p stateIdx skIdx rIdx srcIdx st pk seed key
      pqSalt ptTerm spqr' ctr _ hlog
  · dsimp only [tr_post]
    rw [skippedKeyUsedB_decSkippedTr_g1]
    simp [hsk_ne, hsu']
  · dsimp only [tr_post]
    rw [receiverKeyUsedB_decSkippedTr_g1]
    simp [hne, hru']

end Symbolic.Swarm.CREF.CliPureRcv.TR.RecvDecStepPure
