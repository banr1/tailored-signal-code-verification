/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Symbolic.Proofs.RngG.R3ModelInv
public import Symbolic.Proofs.Swarm.CREF.TR.RecvDec
import DY.Trace.Basic
import DY.Trace.Monad
import DY.Trace.Manipulation
import DY.Actions.PersistentLocalState
import DY.Actions.ProtocolEvent
import Batteries.Data.UInt
public import Symbolic.Proofs.Swarm.CREF.Cli.Rpk.RecvDecStepCommonPureA
public import Symbolic.Proofs.Swarm.CREF.TR.SrHonestVer
import Symbolic.Proofs.Refinement.TripleRatchet.WireCovered
import Symbolic.Proofs.SpecLemmas.Model.EquationalTheory.TrWireMsg
import Symbolic.Proofs.Swarm.CREF.Cli.Rpk.RecvDecStepCommonPure
import Symbolic.Proofs.Swarm.CREF.Cli.Rpk.RecvDecStepSpqrHonestPure
import Symbolic.Proofs.Swarm.CREF.Prelude
import Symbolic.Proofs.Swarm.CREF.TR.G1.WireShapeInj
import Symbolic.Proofs.Swarm.CREF.TR.RecvRep
import Symbolic.Proofs.Swarm.CREF.Cli.PureCRel -- shake: keep
import Symbolic.Proofs.Swarm.CREF.TR.Leaks -- shake: keep
import Symbolic.Proofs.Swarm.CREF.TR.PQModelRunNil -- shake: keep
import Symbolic.Proofs.Swarm.TRREF.B3DefsPure -- shake: keep
import Symbolic.DYBridge.DY.Trace.Basic
import Symbolic.DYBridge.DY.Trace.Monad
import Symbolic.DYBridge.DY.Trace.Manipulation
import Symbolic.DYBridge.DY.Actions.PersistentLocalState
import Symbolic.DYBridge.DY.Actions.ProtocolEvent

/-!
# Cached Skipped-Key Accept Helpers

State-relation preservation, skipped-key trace extraction, and forged-decrypt
representation lemmas for the cached skipped-key accept branch.
-/

@[expose] public section

set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

cref_hide_foreign_instances

namespace Symbolic.Swarm.CREF.CliPure.TR.RecvDecStep
open Symbolic.Swarm.CREF.TR hiding PureBinCanonSession PureRecordRepr SpqrSem at?_append_of_lt compromisesCurrentFrom_append forall₂_append getLocalState_fst getLocalState_snd newRandoms_append_rnd ownSaltsFrom_append runMoves_append runTrace_append runTrace_snoc runVis_append runVis_snoc run_bind_fst run_bind_snd

cref_open

open DY DY.Comparse DY.Literal DY.Libsignal DY.DiffieHellman
open DY.Libsignal.TripleRatchet (SessionInfo computeMac)
open DY.Libsignal.Refinement (ExternCryptoLawsHold aesCbcDecryptSymbol)
open DY.Libsignal.TripleRatchet
open DY.Libsignal.HwEvents DY.Libsignal.Rust
open CryptoGames CryptoGames.LibsignalSession CryptoGames.LibsignalSessionApi
open CryptoVerification
open CryptoVerification.LibsignalTripleRatchet CryptoVerification.LibsignalProtoCodec
open CryptoVerification.E2E CryptoVerification.E2E.InMem CryptoVerification.E2E.Record
open CryptoVerification.E2E.Bin hiding RecordCanonical recordDeserializeOpenSpec encodeRecord
open CryptoVerification.E2E.Pqxdh.WireEntries
open CryptoVerification.E2E.Pqxdh.WireEntries.SymP3 hiding encodeRecord
open CryptoVerification.SessionModel.AdvanceAndFrame (mem_set_or mem_of_mem_eraseIdx)
open CryptoProofLib.Refinement (ExternInterpretation)
open Proofs.libsignal.RngG Proofs.libsignal.RngG.R3 Proofs.libsignal.RngG.CliPure.R3

open Swarm.Phase0WholeFunctionBridge (sessionToRecordRec sessionToSessionRec
  receiverChainToChainRec)
open Symbolic.Swarm.CREF Symbolic.Swarm.CREF.CliPure Symbolic.Swarm.CREF.CliPure.TR
open Symbolic.Swarm.CREF.TR.RecvRep hiding gamma_trWireMsg gamma_litOf
open Symbolic.Swarm.CREF.TR.Pure
open Symbolic.Swarm.CREF.TR.RecvDec hiding StEntry TREntry
  at?_append_of_lt at?_eq_none_of_le trace_snoc_at_length trace_append_at_length
  at?_append_non_entry isCurrentSnapshot_append_non_st logSkippedKeysTr logSkippedKeysTr_length
  at?_trEntry_logSkippedKeysTr_lt decTailTr decTailTr_length at?_trEntry_decTailTr_lt
  run_bind_fst run_bind_snd getLocalState_fst

/-! ## State relation and skipped-key extraction -/

theorem stateRel_of_takeSkippedKey_tr_g1 (interpretation : ExternInterpretation) (S : SpqrSem) (g : Ghost)
    {st : TRState} {s : CryptoGames.LibsignalSessionApi.Session (List (BitVec 8))}
    {their : PublicKey} {counter : BitVec 32}
    {mkGen : MessageKeyGenerator} {r2 : RatchetState} {spqr' : DY.Bytes} {newPqrState : HwBytes}
    (hrel : StateRel interpretation S g st (sessionToRecordRec s))
    (hTake : Mut.exec (RatchetState.takeSkippedKey their counter) (ratchetStateOf s.state) = (.ok (some mkGen), r2))
    (hspqr' : gamma interpretation S g spqr' = newPqrState) :
    r2 = { ratchetStateOf s.state with receiverChains := r2.receiverChains } ∧
    StateRel interpretation S g { st with spqr := spqr' }
      (sessionToRecordRec { s with
        state := { s.state with
          rootKey := r2.rootKey, previousCounter := r2.previousCounter, senderChain := r2.senderChain,
          receiverChains := r2.receiverChains, pqRatchetState := newPqrState, pendingPreKey := false }
        pendingPreKey := none, pendingKyberPreKey := none }) := by
  obtain ⟨ci, ch, idx, hci, hch, hsrk, hfind, hmk_at, hmk_ctr, hmk_mem, hr2, hMapErase⟩ := takeSkippedKey_ok_some_inv hTake
  refine ⟨by rw [hr2], ?_⟩
  have hRecChainEq :
      List.map ((fun c : ChainRec => { c with messageKeys := [] }) ∘ receiverChainToChainRec) r2.receiverChains =
        List.map ((fun c : ChainRec => { c with messageKeys := [] }) ∘ receiverChainToChainRec) s.state.receiverChains := by
    have h1 : List.map ((fun c : ChainRec => { c with messageKeys := [] }) ∘ receiverChainToChainRec) r2.receiverChains =
        (r2.receiverChains.map eraseRecvChain).map recChainOfErased := by rw [List.map_map]; rfl
    have h2 : List.map ((fun c : ChainRec => { c with messageKeys := [] }) ∘ receiverChainToChainRec) s.state.receiverChains =
        (s.state.receiverChains.map eraseRecvChain).map recChainOfErased := by rw [List.map_map]; rfl
    rw [h1, h2]; exact congrArg (List.map recChainOfErased) hMapErase
  have heq := (stateRel_sessionToRecordRec_iff_tr interpretation S g st s).mp hrel; rw [stateRel_sessionToRecordRec_iff_tr]
  have hrk : r2.rootKey = s.state.rootKey := by rw [hr2]; rfl
  have hpn : r2.previousCounter = s.state.previousCounter := by rw [hr2]; rfl
  have hsc : r2.senderChain = s.state.senderChain := by rw [hr2]; rfl
  simp only [eraseSkipped, eraseUnmodelled, sessionToSessionRec, List.map_map] at heq ⊢
  unfold sessionOf at heq ⊢; dsimp only at heq ⊢
  injection heq with h_ver h_loc h_rem h_rk h_pn h_sc h_rc h_ppk h_pkpk h_spqr h_alice h_uid_a h_uid_b
  rw [hrk, hpn, hsc, hRecChainEq, h_ver, h_loc, h_rem, h_rk, h_pn, h_sc, h_rc, hspqr']

theorem extract_skippedKeyStored_of_takeSkippedKey_g1
    (interpretation : ExternInterpretation) (r₀ : ProtocolSetup) (S : SpqrSem) (g : Ghost) (ms₁ : List Move)
    {p : Participant} {rec : RecordRec} {st : TRState}
    {s : CryptoGames.LibsignalSessionApi.Session (List (BitVec 8))}
    {their : PublicKey} {counter : BitVec 32} {mkGen : MessageKeyGenerator} {r2 : RatchetState}
    (hrec_eq : rec = sessionToRecordRec s)
    (hsk_inv : ∀ c ∈ rec.current.receiverChains, ∀ k ∈ c.messageKeys,
      ∃ pk rIdx srcIdx skIdx seed,
        (runTraceMoves r₀ ms₁).EventLoggedAt (TREvent.SkippedKeyStored (st.sessionInfo p) pk (UInt32.ofBitVec k.1) seed rIdx srcIdx) skIdx ∧
        (!skippedKeyUsedB (runTraceMoves r₀ ms₁) skIdx) = true ∧
        (!receiverKeyUsedB (runTraceMoves r₀ ms₁) (st.sessionInfo p) seed (UInt32.ofBitVec k.1) rIdx) = true ∧
        gamma interpretation S g seed = k.2 ∧
        c.senderRatchetKey = Symbolic.Swarm.CREF.TR.serializedKey (gamma interpretation S g pk) ∧
        (findRecvChain st.toDRState.recv pk).isSome = true)
    (hTake : Mut.exec (RatchetState.takeSkippedKey their counter) (ratchetStateOf s.state) = (.ok (some mkGen), r2)) :
    ∃ (pk : DY.Bytes) (rIdx srcIdx skIdx : Nat) (seed : DY.Bytes),
      (runTraceMoves r₀ ms₁).EventLoggedAt (TREvent.SkippedKeyStored (st.sessionInfo p) pk (UInt32.ofBitVec counter) seed rIdx srcIdx) skIdx ∧
      ((runTraceMoves r₀ ms₁).at? skIdx : Option TREntry) = some ⟨TREvent.SkippedKeyStored (st.sessionInfo p) pk (UInt32.ofBitVec counter) seed rIdx srcIdx⟩ ∧
      skippedKeyUsedB (runTraceMoves r₀ ms₁) skIdx = false ∧
      receiverKeyUsedB (runTraceMoves r₀ ms₁) (st.sessionInfo p) seed (UInt32.ofBitVec counter) rIdx = false ∧
      gamma interpretation S g seed = mkGen.seed ∧
      Symbolic.Swarm.CREF.TR.serializedKey (gamma interpretation S g pk) = their.serialize ∧
      (findRecvChain st.toDRState.recv pk).isSome = true := by
  obtain ⟨ci, ch, idx, hci, hch, hsrk, hfind, hmk_at, hmk_ctr, hmk_mem, hr2, _⟩ := takeSkippedKey_ok_some_inv hTake
  let c_k := receiverChainToChainRec ch
  have hc_k_mem : c_k ∈ rec.current.receiverChains := by rw [hrec_eq]; exact List.mem_map_of_mem (List.mem_of_getElem? hch)
  have hmk_pair_mem : (counter, mkGen.seed) ∈ c_k.messageKeys := by
    have : (mkGen.counter, mkGen.seed) ∈ c_k.messageKeys :=
      List.mem_map_of_mem (f := fun mk : MessageKeyGenerator => (mk.counter, mk.seed)) hmk_mem
    rwa [hmk_ctr] at this
  have hsrk_k : c_k.senderRatchetKey = their.serialize := congrArg PublicKey.serialize hsrk
  obtain ⟨pk, rIdx, srcIdx, skIdx, seed, hlog, hsu_b, hru_b, hseed, hpk_ser, hfind_pk⟩ :=
    hsk_inv c_k hc_k_mem (counter, mkGen.seed) hmk_pair_mem
  have hunused : skippedKeyUsedB (runTraceMoves r₀ ms₁) skIdx = false := by simpa using hsu_b
  have hru : receiverKeyUsedB (runTraceMoves r₀ ms₁) (st.sessionInfo p) seed (UInt32.ofBitVec counter) rIdx = false := by simpa using hru_b
  exact ⟨pk, rIdx, srcIdx, skIdx, seed, hlog, (Symbolic.DYBridge.DY.Trace.EventLoggedAt_eq_1 _ _ _).mp hlog, hunused, hru, hseed, hpk_ser.symm.trans hsrk_k, hfind_pk⟩

theorem attackerKnows_append_g1 {E : Type} [ExecTraceTypes.Has E] {tr : ExecTrace} {e : E} {t : DY.Bytes}
    (h : t.AttackerKnows tr) : t.AttackerKnows (tr.append e) :=
  DY.Bytes.AttackerKnows_le t tr (tr.append e) (Trace.append_le tr e) h

/-! ## Trace preservation across `decSkippedTr` -/

theorem getLocalState_decSkippedTr_last_g1 (tr : ExecTrace) (me : Participant)
    (stateIdx skIdx rIdx srcIdx : Nat) (st : TRState) (pk seed key pqSalt ptTerm spqr' : DY.Bytes) (n : UInt32) :
    ((PersistentLocalState.getLocalState me (tr.length + 4) : Traceful TRState).run
      (decSkippedTr tr me stateIdx skIdx rIdx srcIdx st pk seed key pqSalt ptTerm spqr' n)).1 =
      some { st with spqr := spqr' } := by
  unfold decSkippedTr; dsimp only
  refine (congrArg (fun k => ((PersistentLocalState.getLocalState me k : Traceful TRState).run _).1) ?_).trans
    (getLocalState_append_stEntry_at_length _ me { st with spqr := spqr' })
  simp only [Symbolic.DYBridge.DY.Trace.append_eq_1, Symbolic.DYBridge.DY.Trace.length_eq_2]

theorem isCurrentSnapshot_decSkippedTr_last_g1 (tr : ExecTrace) (me : Participant)
    (stateIdx skIdx rIdx srcIdx : Nat) (st : TRState) (pk seed key pqSalt ptTerm spqr' : DY.Bytes) (n : UInt32) :
    isCurrentSnapshot (decSkippedTr tr me stateIdx skIdx rIdx srcIdx st pk seed key pqSalt ptTerm spqr' n) (tr.length + 4) = true := by
  unfold decSkippedTr; dsimp only
  refine (congrArg (isCurrentSnapshot _) ?_).trans
    (isCurrentSnapshot_append_stEntry_at_length _ me { st with spqr := spqr' })
  simp only [Symbolic.DYBridge.DY.Trace.append_eq_1, Symbolic.DYBridge.DY.Trace.length_eq_2]

theorem eventLoggedAt_append_of_lt_g1 {E : Type} [ExecTraceTypes.Has E]
    (tr : ExecTrace) (e : E) (ev : TREvent) {i : Nat} (hlog : tr.EventLoggedAt ev i) : (tr.append e).EventLoggedAt ev i := by
  rw [Symbolic.DYBridge.DY.Trace.EventLoggedAt_eq_1] at hlog ⊢
  have hlt : i < tr.length := by have := Trace.at?_eq_some_implies_length_le (EntryT := TREntry) tr i; rwa [hlog] at this
  rw [at?_append_of_lt tr e hlt]; exact hlog

theorem eventLoggedAt_decSkippedTr_of_old_g1 (tr : ExecTrace) (me : Participant)
    (stateIdx skIdx rIdx srcIdx : Nat) (st : TRState) (pk seed key pqSalt ptTerm spqr' : DY.Bytes) (n : UInt32)
    (ev : TREvent) {i : Nat} (hlog : tr.EventLoggedAt ev i) :
    (decSkippedTr tr me stateIdx skIdx rIdx srcIdx st pk seed key pqSalt ptTerm spqr' n).EventLoggedAt ev i := by
  unfold decSkippedTr; dsimp only
  exact eventLoggedAt_append_of_lt_g1 _ _ ev (eventLoggedAt_append_of_lt_g1 _ _ ev
    (eventLoggedAt_append_of_lt_g1 _ _ ev (eventLoggedAt_append_of_lt_g1 _ _ ev (eventLoggedAt_append_of_lt_g1 _ _ ev hlog))))

theorem skippedKeyUsedB_decSkippedTr_g1 (tr : ExecTrace) (me : Participant)
    (stateIdx skIdx rIdx srcIdx : Nat) (st : TRState) (pk seed key pqSalt ptTerm spqr' : DY.Bytes) (n : UInt32) (idx : Nat) :
    skippedKeyUsedB (decSkippedTr tr me stateIdx skIdx rIdx srcIdx st pk seed key pqSalt ptTerm spqr' n) idx =
      (skippedKeyUsedB tr idx || (skIdx == idx)) := by
  unfold skippedKeyUsedB decSkippedTr; dsimp only
  rw [someEventOnTraceB_append_non_tr_a2 _ _ rfl, someEventOnTraceB_append_trEntry_a2,
      someEventOnTraceB_append_trEntry_a2, someEventOnTraceB_append_trEntry_a2, someEventOnTraceB_append_non_tr_a2 _ _ rfl]
  simp only [Bool.or_false]

theorem receiverKeyUsedB_decSkippedTr_g1 (tr : ExecTrace) (me : Participant)
    (stateIdx skIdx rIdx srcIdx : Nat) (st : TRState) (pk seed key pqSalt ptTerm spqr' : DY.Bytes) (n : UInt32)
    (s : SessionInfo) (seed' : DY.Bytes) (cnt' : UInt32) (rIdx' : Nat) :
    receiverKeyUsedB (decSkippedTr tr me stateIdx skIdx rIdx srcIdx st pk seed key pqSalt ptTerm spqr' n) s seed' cnt' rIdx' =
      (receiverKeyUsedB tr s seed' cnt' rIdx' || decide (st.sessionInfo me = s ∧ seed = seed' ∧ n = cnt' ∧ rIdx = rIdx')) := by
  unfold receiverKeyUsedB decSkippedTr; dsimp only
  rw [someEventOnTraceB_append_non_tr_a2 _ _ rfl, someEventOnTraceB_append_trEntry_a2,
      someEventOnTraceB_append_trEntry_a2, someEventOnTraceB_append_trEntry_a2, someEventOnTraceB_append_non_tr_a2 _ _ rfl]
  simp only [Bool.or_false]

theorem nodup_map_eraseIdx_g1 {α β : Type} (f : α → β) (l : List α) (idx : Nat)
    (h : (l.map f).Nodup) : ((l.eraseIdx idx).map f).Nodup := by
  rw [← List.eraseIdx_map]; exact h.eraseIdx idx

theorem nodup_and_lt_of_takeSkippedKey_tr_g1
    {s : CryptoGames.LibsignalSessionApi.Session (List (BitVec 8))}
    {their : PublicKey} {counter : BitVec 32} {mkGen : MessageKeyGenerator} {r2 : RatchetState} {newPqrState : HwBytes}
    (hTake : Mut.exec (RatchetState.takeSkippedKey their counter) (ratchetStateOf s.state) = (.ok (some mkGen), r2))
    (hnd : ((sessionToRecordRec s).current.receiverChains.map ChainRec.senderRatchetKey).Nodup ∧
      (∀ c ∈ (sessionToRecordRec s).current.receiverChains, (c.messageKeys.map Prod.fst).Nodup) ∧
      ∀ c ∈ (sessionToRecordRec s).current.receiverChains, ∀ k ∈ c.messageKeys, ∃ ck, c.chainKey = some ck ∧ k.1 < ck.1) :
    let rec' := sessionToRecordRec
      { s with
        state := { s.state with
          rootKey := r2.rootKey, previousCounter := r2.previousCounter, senderChain := r2.senderChain,
          receiverChains := r2.receiverChains, pqRatchetState := newPqrState, pendingPreKey := false }
        pendingPreKey := none, pendingKyberPreKey := none }
    (rec'.current.receiverChains.map ChainRec.senderRatchetKey).Nodup ∧
    (∀ c_k ∈ rec'.current.receiverChains, (c_k.messageKeys.map Prod.fst).Nodup) ∧
    (∀ c_k ∈ rec'.current.receiverChains, ∀ k ∈ c_k.messageKeys, ∃ ck, c_k.chainKey = some ck ∧ k.1 < ck.1) := by
  intro rec'; obtain ⟨hSrkNodup, hMksNodup, hLt⟩ := hnd
  obtain ⟨ci, ch, idx, hci, hch, hsrk, hfind, hmk_at, hmk_ctr, hmk_mem, hr2, hMapErase⟩ := takeSkippedKey_ok_some_inv hTake
  have hSrkEq : rec'.current.receiverChains.map ChainRec.senderRatchetKey =
      (sessionToRecordRec s).current.receiverChains.map ChainRec.senderRatchetKey := by
    have h1 : rec'.current.receiverChains.map ChainRec.senderRatchetKey =
        (r2.receiverChains.map eraseRecvChain).map (ChainRec.senderRatchetKey ∘ recChainOfErased) := by
      dsimp only [rec', sessionToRecordRec, sessionToSessionRec]; rw [List.map_map, List.map_map]; rfl
    have h2 : (sessionToRecordRec s).current.receiverChains.map ChainRec.senderRatchetKey =
        (s.state.receiverChains.map eraseRecvChain).map (ChainRec.senderRatchetKey ∘ recChainOfErased) := by
      dsimp only [sessionToRecordRec, sessionToSessionRec]; rw [List.map_map, List.map_map]; rfl
    rw [h1, h2]; exact congrArg (List.map (ChainRec.senderRatchetKey ∘ recChainOfErased)) hMapErase
  refine ⟨hSrkEq ▸ hSrkNodup, ?_, ?_⟩
  · intro c_k hc_k; dsimp only [rec', sessionToRecordRec, sessionToSessionRec] at hc_k
    rw [hr2] at hc_k; dsimp only [ratchetStateOf] at hc_k; rw [List.mem_map] at hc_k; obtain ⟨rc, hrc_mem, rfl⟩ := hc_k
    rcases mem_set_or s.state.receiverChains ci { ch with messageKeys := ch.messageKeys.eraseIdx idx } rc hrc_mem with rfl | hrc_old
    · have hch_old_mem : receiverChainToChainRec ch ∈ (sessionToRecordRec s).current.receiverChains :=
        List.mem_map_of_mem (List.mem_of_getElem? hch)
      have hNodup_old := hMksNodup (receiverChainToChainRec ch) hch_old_mem
      have hMapFst : ((receiverChainToChainRec ch).messageKeys.map Prod.fst) = ch.messageKeys.map MessageKeyGenerator.counter := by
        dsimp only [receiverChainToChainRec]; rw [List.map_map]; rfl
      have hMapFst' : ((receiverChainToChainRec { ch with messageKeys := ch.messageKeys.eraseIdx idx }).messageKeys.map Prod.fst) =
          (ch.messageKeys.eraseIdx idx).map MessageKeyGenerator.counter := by
        dsimp only [receiverChainToChainRec]; rw [List.map_map]; rfl
      rw [hMapFst']; rw [hMapFst] at hNodup_old; exact nodup_map_eraseIdx_g1 MessageKeyGenerator.counter ch.messageKeys idx hNodup_old
    · exact hMksNodup (receiverChainToChainRec rc) (List.mem_map_of_mem hrc_old)
  · intro c_k hc_k k hk; dsimp only [rec', sessionToRecordRec, sessionToSessionRec] at hc_k
    rw [hr2] at hc_k; dsimp only [ratchetStateOf] at hc_k; rw [List.mem_map] at hc_k; obtain ⟨rc, hrc_mem, rfl⟩ := hc_k
    rcases mem_set_or s.state.receiverChains ci { ch with messageKeys := ch.messageKeys.eraseIdx idx } rc hrc_mem with rfl | hrc_old
    · have hch_old_mem : receiverChainToChainRec ch ∈ (sessionToRecordRec s).current.receiverChains :=
        List.mem_map_of_mem (List.mem_of_getElem? hch)
      have hk_old : k ∈ (receiverChainToChainRec ch).messageKeys := by
        dsimp only [receiverChainToChainRec] at hk ⊢; rw [List.mem_map] at hk ⊢; obtain ⟨mk0, hmk0, rfl⟩ := hk
        exact ⟨mk0, mem_of_mem_eraseIdx ch.messageKeys idx mk0 hmk0, rfl⟩
      exact hLt (receiverChainToChainRec ch) hch_old_mem k hk_old
    · exact hLt (receiverChainToChainRec rc) (List.mem_map_of_mem hrc_old) k hk

theorem trKeyShape_with_spqr_g1 (interpretation : ExternInterpretation) (S : SpqrSem) (g : Ghost)
    (st : TRState) (spqr' : DY.Bytes) :
    TRKeyShape interpretation S g { st with spqr := spqr' } ↔ TRKeyShape interpretation S g st := by
  constructor <;> rintro ⟨h1, h2, h3, h4⟩ <;> exact ⟨h1, h2, h3, h4⟩

/-! ## Forged decrypt representation and own-key bounds -/

theorem forged_decrypt_rep_of_keysKnown_with_sendMsg_tr
    (interpretation : ExternInterpretation) (hEq : ExternCryptoLawsHold interpretation)
    (r₀ : ProtocolSetup) (S : SpqrSem) (g : Ghost) (ms : List Move) (acc : List MachineEvent)
    (b ptext : HwBytes) (parsed : SignalMessage)
    {who : List Participant}
    (hmp : MatchedPrefix interpretation r₀ S who g ms acc)
    (hfit : SrHonestVer.SendsFit acc)
    (hHon : PqFromHonest (sentBodies acc) b)
    (hTryFrom : SignalMessage.tryFrom protoSignalCodec b = .ok parsed)
    (t₀ : DY.Bytes) (msg₀ : TRSignalMsg)
    (ht₀ : t₀ ∈ recvRepresentations interpretation r₀ S g ms b) (hparse₀ : parseTrSignalMsg t₀ = some msg₀)
    (st₀ : TRState) (mkSeed k_own pqSalt : DY.Bytes)
    (hpqSalt_kn : pqSalt.AttackerKnows (runTraceMoves r₀ ms))
    (hpqSalt_gam : gamma interpretation S g pqSalt = gamma interpretation S g k_own)
    (hck_kn : (trMsgKeys pqSalt mkSeed).cipherKey.AttackerKnows (runTraceMoves r₀ ms))
    (hmk_kn : (trMsgKeys pqSalt mkSeed).macKey.AttackerKnows (runTraceMoves r₀ ms))
    (hiv_kn : (trMsgKeys pqSalt mkSeed).iv.AttackerKnows (runTraceMoves r₀ ms))
    (hMacBytes : b.drop (b.length - 8) =
      gamma interpretation S g (computeMac (trMsgKeys k_own mkSeed).macKey st₀.peerIk st₀.myIk msg₀.wire))
    (hPeerK : st₀.peerIk.AttackerKnows (runTraceMoves r₀ ms)) (hMyK : st₀.myIk.AttackerKnows (runTraceMoves r₀ ms))
    (hDecOk : interpretation aesCbcDecryptSymbol
      [parsed.ciphertext, gamma interpretation S g (trMsgKeys k_own mkSeed).cipherKey,
       (gamma interpretation S g (trMsgKeys k_own mkSeed).iv).take 16] = some ptext) :
    ∃ (t' : DY.Bytes) (msg' : TRSignalMsg) (ptTerm : DY.Bytes),
      t' ∈ recvRepresentations interpretation r₀ S g ms b ∧ t'.AttackerKnows (runTraceMoves r₀ ms) ∧
      gamma interpretation S g t' = b ∧ parseTrSignalMsg t' = some msg' ∧
      msg'.version = msg₀.version ∧ msg'.ratchetKey = msg₀.ratchetKey ∧ msg'.counter = msg₀.counter ∧
      gamma interpretation S g msg'.pqRatchet = gamma interpretation S g msg₀.pqRatchet ∧
      DY.Spqr.spqrEmptyMsg msg'.pqRatchet = false ∧
      msg'.mac = computeMac (trMsgKeys pqSalt mkSeed).macKey st₀.peerIk st₀.myIk msg'.wire ∧
      DY.SymEnc.symDec (trMsgKeys pqSalt mkSeed).cipherKey (trMsgKeys pqSalt mkSeed).iv msg'.ciphertext = some ptTerm ∧
      gamma interpretation S g ptTerm = ptext := by
  let tr := runTraceMoves r₀ ms
  obtain ⟨hck_gam, hmk_gam, hiv_gam⟩ :=
    Symbolic.Swarm.CREF.TR.G1.gamma_trMsgKeys_eq_of_gamma_eq interpretation S g hpqSalt_gam
      (rfl : gamma interpretation S g mkSeed = gamma interpretation S g mkSeed)
  have hwire₀_kn : msg₀.wire.AttackerKnows tr := by
    have hsp := Concat.attacker_knows_split t₀ (t₀.length - Trunc.trunc8Length) tr ht₀.1
    unfold parseTrSignalMsg at hparse₀
    rcases hsplit : Concat.split t₀ (t₀.length - Trunc.trunc8Length) with _ | ⟨w₀, m₀⟩
    · rw [hsplit] at hparse₀; cases hparse₀
    · rw [hsplit] at hsp hparse₀; dsimp only [Bind.bind, Option.bind] at hparse₀
      rcases hwf : DY.TrWire.trWireMsgFields? w₀ with _ | x₀
      · rw [hwf] at hparse₀; cases hparse₀
      · rw [hwf] at hparse₀; injection hparse₀ with hmsg; subst hmsg; exact hsp.1
  obtain ⟨v₀, pc₀, ev₀, hwire₀_eq, _⟩ := Symbolic.Swarm.CREF.TR.G1.parseTrSignalMsg_eq_some_inv hparse₀
  have hargs₀ := DY.TrWire.attacker_knows_trWireMsg_args v₀ msg₀.ratchetKey msg₀.counter pc₀
    msg₀.ciphertext msg₀.pqRatchet ev₀ tr (hwire₀_eq ▸ hwire₀_kn)
  obtain ⟨hwire₀_take, _, _, htry₀⟩ := ht₀.2.2.2 msg₀ hparse₀
  obtain ⟨_, hrk₀_gam, hpq₀_gam, hctr₀_nat, hver₀_nat⟩ := htry₀ parsed hTryFrom
  have hck_len : (gamma interpretation S g (trMsgKeys k_own mkSeed).cipherKey).length = 32 :=
    length_gamma_hmac_tr interpretation S g _ _
  have hiv_len32 : (gamma interpretation S g (trMsgKeys k_own mkSeed).iv).length = 32 :=
    length_gamma_hmac_tr interpretation S g _ _
  have hiv_len : ((gamma interpretation S g (trMsgKeys k_own mkSeed).iv).take 16).length = 16 := by
    rw [List.length_take, hiv_len32]; decide
  have hct_gam : gamma interpretation S g
      (DY.SymEnc.symEnc (trMsgKeys pqSalt mkSeed).cipherKey (trMsgKeys pqSalt mkSeed).iv (litOf ptext)) =
      parsed.ciphertext := by
    rw [Symbolic.Swarm.CREF.TR.G1.gamma_symEnc_tr, gamma_litOf, hck_gam, hiv_gam,
        hEq.aes_cbc_encrypt_of_decrypt _ _ _ _ hck_len hiv_len hDecOk, Option.getD_some]
  have hmac_gam : ∀ wire' : DY.Bytes,
      gamma interpretation S g wire' = b.take (b.length - 8) →
      gamma interpretation S g (computeMac (trMsgKeys pqSalt mkSeed).macKey st₀.peerIk st₀.myIk wire') =
        b.drop (b.length - 8) := by
    intro wire' hwire'_take; rw [hMacBytes]
    rw [gamma_computeMac_congr_wire interpretation S g _ _ _ wire' msg₀.wire (hwire'_take.trans hwire₀_take.symm)]
    unfold DY.Libsignal.TripleRatchet.computeMac DY.Libsignal.TripleRatchet.hmac
    rw [gamma_trunc8_tr, gamma_trunc8_tr, Symbolic.Swarm.CREF.TR.G1.gamma_kdfExtract_tr,
        Symbolic.Swarm.CREF.TR.G1.gamma_kdfExtract_tr, hmk_gam]
  obtain ⟨st_s, coins_s, hpq_knows, hpq_gamma⟩ :=
    exists_honest_sendMsg_of_pqFromHonest interpretation r₀ S g ms acc b parsed hmp hfit hHon hTryFrom
  obtain ⟨t', msg', ptTerm, ht'_rep, ht'_kn, ht'_gam, hparse', hver', hrk', hctr',
    hpq', hnot_empty, hmac', hdec', hpt_gam⟩ :=
    exists_forged_decrypt_rep_with_sendMsg interpretation r₀ S g ms b ptext parsed hTryFrom
      msg₀.ratchetKey pqSalt mkSeed st₀.peerIk st₀.myIk st_s coins_s
      hargs₀.1 hrk₀_gam hck_kn hiv_kn hmk_kn hPeerK hMyK hpq_knows hpq_gamma hct_gam hmac_gam
  exact ⟨t', msg', ptTerm, ht'_rep, ht'_kn, ht'_gam, hparse',
    UInt8.ext (hver'.trans hver₀_nat.symm), hrk', UInt32.ext (hctr'.trans hctr₀_nat.symm),
    by rw [hpq', hpq_gamma, hpq₀_gam], hnot_empty, hmac', hdec', hpt_gam⟩

theorem forged_decrypt_rep_of_seedKnown_with_sendMsg_tr
    (interpretation : ExternInterpretation) (hEq : ExternCryptoLawsHold interpretation)
    (r₀ : ProtocolSetup) (S : SpqrSem) (g : Ghost) (ms : List Move) (acc : List MachineEvent)
    (b ptext : HwBytes) (parsed : SignalMessage)
    {who : List Participant}
    (hmp : MatchedPrefix interpretation r₀ S who g ms acc)
    (hfit : SrHonestVer.SendsFit acc)
    (hHon : PqFromHonest (sentBodies acc) b)
    (hTryFrom : SignalMessage.tryFrom protoSignalCodec b = .ok parsed)
    (t₀ : DY.Bytes) (msg₀ : TRSignalMsg)
    (ht₀ : t₀ ∈ recvRepresentations interpretation r₀ S g ms b) (hparse₀ : parseTrSignalMsg t₀ = some msg₀)
    (st₀ : TRState) (mkSeed k_own : DY.Bytes)
    (hMacBytes : b.drop (b.length - 8) =
      gamma interpretation S g (computeMac (trMsgKeys k_own mkSeed).macKey st₀.peerIk st₀.myIk msg₀.wire))
    (hPeerK : st₀.peerIk.AttackerKnows (runTraceMoves r₀ ms)) (hMyK : st₀.myIk.AttackerKnows (runTraceMoves r₀ ms))
    (hDecOk : interpretation aesCbcDecryptSymbol
      [parsed.ciphertext, gamma interpretation S g (trMsgKeys k_own mkSeed).cipherKey,
       (gamma interpretation S g (trMsgKeys k_own mkSeed).iv).take 16] = some ptext)
    (hSeedK : mkSeed.AttackerKnows (runTraceMoves r₀ ms)) :
    ∃ (t' : DY.Bytes) (msg' : TRSignalMsg) (ptTerm pqSalt : DY.Bytes),
      t' ∈ recvRepresentations interpretation r₀ S g ms b ∧ t'.AttackerKnows (runTraceMoves r₀ ms) ∧
      pqSalt.AttackerKnows (runTraceMoves r₀ ms) ∧
      gamma interpretation S g pqSalt = gamma interpretation S g k_own ∧
      gamma interpretation S g t' = b ∧ parseTrSignalMsg t' = some msg' ∧
      msg'.version = msg₀.version ∧ msg'.ratchetKey = msg₀.ratchetKey ∧ msg'.counter = msg₀.counter ∧
      gamma interpretation S g msg'.pqRatchet = gamma interpretation S g msg₀.pqRatchet ∧
      DY.Spqr.spqrEmptyMsg msg'.pqRatchet = false ∧
      msg'.mac = computeMac (trMsgKeys pqSalt mkSeed).macKey st₀.peerIk st₀.myIk msg'.wire ∧
      DY.SymEnc.symDec (trMsgKeys pqSalt mkSeed).cipherKey (trMsgKeys pqSalt mkSeed).iv msg'.ciphertext = some ptTerm ∧
      gamma interpretation S g ptTerm = ptext := by
  let tr := runTraceMoves r₀ ms; let pqSalt := litOf (gamma interpretation S g k_own)
  have hpqSalt_kn : pqSalt.AttackerKnows tr := knows_litOf _ _
  have hpqSalt_gam : gamma interpretation S g pqSalt = gamma interpretation S g k_own := gamma_litOf interpretation S g _
  have hprk_kn : (DY.Libsignal.TripleRatchet.hmac pqSalt mkSeed).AttackerKnows tr :=
    KdfExtract.attacker_knows_kdfExtract _ _ _ hpqSalt_kn hSeedK
  have hinfo_kn : (DY.Libsignal.TripleRatchet.lit "WhisperMessageKeys").AttackerKnows tr :=
    Literal.attacker_knows_literalToBytes _ _
  have hck_kn : (trMsgKeys pqSalt mkSeed).cipherKey.AttackerKnows tr :=
    KdfExtract.attacker_knows_kdfExtract _ _ _ hprk_kn
      (Concat.attacker_knows_concat _ _ _ hinfo_kn (Literal.attacker_knows_literalToBytes _ _))
  have hmk_kn : (trMsgKeys pqSalt mkSeed).macKey.AttackerKnows tr :=
    KdfExtract.attacker_knows_kdfExtract _ _ _ hprk_kn
      (Concat.attacker_knows_concat _ _ _ hck_kn (Concat.attacker_knows_concat _ _ _ hinfo_kn (Literal.attacker_knows_literalToBytes _ _)))
  have hiv_kn : (trMsgKeys pqSalt mkSeed).iv.AttackerKnows tr :=
    KdfExtract.attacker_knows_kdfExtract _ _ _ hprk_kn
      (Concat.attacker_knows_concat _ _ _ hmk_kn (Concat.attacker_knows_concat _ _ _ hinfo_kn (Literal.attacker_knows_literalToBytes _ _)))
  obtain ⟨t', msg', ptTerm, ht'_rep, ht'_kn, ht'_gam, hparse', hver', hrk', hctr',
    hpq_gam, hnot_empty, hmac', hdec', hpt_gam⟩ :=
    forged_decrypt_rep_of_keysKnown_with_sendMsg_tr interpretation hEq r₀ S g ms acc b ptext parsed
      hmp hfit hHon hTryFrom t₀ msg₀ ht₀ hparse₀ st₀ mkSeed k_own pqSalt
      hpqSalt_kn hpqSalt_gam hck_kn hmk_kn hiv_kn hMacBytes hPeerK hMyK hDecOk
  exact ⟨t', msg', ptTerm, pqSalt, ht'_rep, ht'_kn, hpqSalt_kn, hpqSalt_gam, ht'_gam,
    hparse', hver', hrk', hctr', hpq_gam, hnot_empty, hmac', hdec', hpt_gam⟩

end Symbolic.Swarm.CREF.CliPure.TR.RecvDecStep
