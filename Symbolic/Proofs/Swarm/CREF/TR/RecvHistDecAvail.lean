/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Symbolic.Proofs.Swarm.CREF.TR.RecvDec
import DY.Trace.Basic
import DY.Trace.Monad
import DY.Trace.Manipulation
import DY.Actions.Network
import DY.Actions.PersistentLocalState
import DY.Actions.PersistentGlobalState
import DY.Actions.ProtocolEvent
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Symbolic.Proofs.Swarm.CREF.Prelude
import VCVio.Prelude.Core
import Symbolic.DYBridge.DY.Trace.Basic
import Symbolic.DYBridge.DY.Trace.Monad
import Symbolic.DYBridge.DY.Trace.Manipulation
import Symbolic.DYBridge.DY.Actions.Network
import Symbolic.DYBridge.DY.Actions.PersistentLocalState
import Symbolic.DYBridge.DY.Actions.PersistentGlobalState
import Symbolic.DYBridge.DY.Actions.ProtocolEvent

/-!
# Available States Across Whisper Decrypt Moves

Characterizes `availableStates` across `Move.decryptSkipped` and `Move.decrypt` (and their
`Move.attackerSend`-prefixed variants), showing that every post-step available state either
was already available before the step or equals the single newly stored `TRState`.
-/

@[expose] public section

set_option autoImplicit false
set_option linter.unusedSimpArgs false
cref_hide_foreign_instances
namespace Symbolic.Swarm.CREF.TR
cref_open
open DY.Libsignal.TripleRatchet (SessionInfo KeyDir findRecvChain setRecvChain recvChainFor
  consumeMessageKey computeMac messageVersion x25519LowOrder)
open DY.Libsignal.TripleRatchet (TRState TREvent TRSignalMsg parseTrSignalMsg skippedKeyUsedB
  trMsgKeys receiveSignalMsg verifyMacAndDecrypt ensureReceiverChain messageDecrypt
  messageDecryptSkipped logMessageKeyAndStore guardTrace)
open Symbolic.Swarm.CREF.TR.RecvDec

theorem mem_availableStates_iff_rhda {r₀ : ProtocolSetup} {tr : ExecTrace} {st : TRState} :
    st ∈ availableStates r₀ tr ↔
      ∃ i q, (setupTrace r₀).length ≤ i ∧ (tr.at? i : Option StEntry) = some ⟨⟨q, st⟩⟩ := by
  unfold availableStates storedStates DY.Libsignal.Composed.Refinement.newIndices
    DY.ExecTrace.getLocalStateAt; rw [List.mem_map]
  constructor
  · rintro ⟨⟨q, st'⟩, hls, rfl⟩
    obtain ⟨i, hi, hsome⟩ := List.mem_filterMap.mp hls
    rw [List.mem_range'_1] at hi
    rcases hat : (tr.at? i : Option StEntry) with _ | ⟨⟨q0, st0⟩⟩
    · rw [hat] at hsome; cases hsome
    · rw [hat] at hsome; injection hsome with h1; injection h1 with hq hst
      subst hq hst; exact ⟨i, q0, hi.1, hat⟩
  · rintro ⟨i, q, hlo, hat⟩
    have hlt : i < tr.length := by
      have := DY.Trace.at?_eq_some_implies_length_le (EntryT := StEntry) tr i
      rwa [hat] at this
    refine ⟨⟨q, st⟩, List.mem_filterMap.mpr ⟨i, ?_, ?_⟩, rfl⟩
    · rw [List.mem_range'_1]; exact ⟨hlo, by omega⟩
    · rw [hat]; rfl
theorem at?_stEntry_append_stEntry_cases_rhda
    {tr : ExecTrace} {me : Participant} {st' : TRState} {i : Nat} {q : Participant} {st : TRState}
    (hat : ((tr.append (⟨⟨me, st'⟩⟩ : StEntry)).at? i : Option StEntry) = some ⟨⟨q, st⟩⟩) :
    (tr.at? i : Option StEntry) = some ⟨⟨q, st⟩⟩ ∨ (i = tr.length ∧ q = me ∧ st = st') := by
  by_cases hlt : i < tr.length
  · rw [at?_append_of_lt _ _ hlt] at hat; exact Or.inl hat
  · by_cases heq : i = tr.length
    · subst heq; rw [Trace.at?_append] at hat
      injection hat with h1; injection h1 with h2; injection h2 with hq hst
      exact Or.inr ⟨rfl, hq.symm, hst.symm⟩
    · have hgt : (tr.append (⟨⟨me, st'⟩⟩ : StEntry)).length ≤ i := by
        simp only [Symbolic.DYBridge.DY.Trace.append_eq_1, Symbolic.DYBridge.DY.Trace.length_eq_2]; omega
      rw [at?_eq_none_of_le _ hgt] at hat; cases hat

theorem at?_stEntry_logSkippedKeysTr (s : SessionInfo) (pk : DY.Bytes)
    (rIdx sourceStateIdx : Nat) (ck : DY.Bytes) (n : UInt32) (k : Nat) (tr : ExecTrace) (i : Nat) :
    ((logSkippedKeysTr s pk rIdx sourceStateIdx ck n k tr).at? i : Option StEntry) =
      (tr.at? i : Option StEntry) := by
  induction k generalizing ck n tr with
  | zero => rfl
  | succ k ih =>
    unfold logSkippedKeysTr
    rw [ih, at?_append_non_entry _ _ rfl]

theorem receiveMessage_snd_val_rhda (idx : Nat) (tr : ExecTrace) :
    ((DY.Network.receiveMessage idx).run tr).2.val = tr := by
  simp only [Symbolic.DYBridge.DY.Network.receiveMessage_eq_1, Symbolic.DYBridge.DY.getEntry_eq_1]
  rw [run_bind_snd, Traceful.run_mk]
  rcases (tr.at? idx : Option DY.Network.ExecEntryT) with _ | ⟨t⟩ <;> (simp -failIfUnchanged only [Symbolic.DYBridge.DY.Traceful.run_eq_1]; try rfl)

theorem receiveSignalMsg_snd_val_rhda (msgIdx : Nat) (tr : ExecTrace) :
    ((DY.Libsignal.TripleRatchet.receiveSignalMsg msgIdx).run tr).2.val = tr := by
  unfold DY.Libsignal.TripleRatchet.receiveSignalMsg
  rw [run_bind_snd, receiveMessage_snd_val_rhda]
  rcases ((DY.Network.receiveMessage msgIdx).run tr).1 with _ | t
  · rfl
  · dsimp only
    rcases parseTrSignalMsg t with _ | msg'
    · (simp -failIfUnchanged only [Symbolic.DYBridge.DY.Traceful.run_eq_1]; try rfl)
    · dsimp only [_root_.guard]
      by_cases hv : msg'.version = messageVersion
      · simp only [hv, ↓reduceIte, Traceful.run_bind, Traceful.run_pure]
      · simp only [hv, ↓reduceIte]; (simp -failIfUnchanged only [Symbolic.DYBridge.DY.Traceful.run_eq_1]; try rfl)

theorem verifyMacAndDecrypt_snd_val_rhda (st : TRState) (msg : TRSignalMsg)
    (pqSalt seed : DY.Bytes) (tr : ExecTrace) :
    ((DY.Libsignal.TripleRatchet.verifyMacAndDecrypt st msg pqSalt seed).run tr).2.val = tr := by
  unfold DY.Libsignal.TripleRatchet.verifyMacAndDecrypt _root_.guard
  dsimp only
  by_cases hm : msg.mac = computeMac (trMsgKeys pqSalt seed).macKey st.peerIk st.myIk msg.wire
  · simp only [hm, ↓reduceIte, Traceful.run_bind, Traceful.run_pure]
    rcases DY.SymEnc.symDec (trMsgKeys pqSalt seed).cipherKey (trMsgKeys pqSalt seed).iv msg.ciphertext <;>
      (erw [DY.Traceful.run_mk]; rw [Traceful.run_pure])
  · simp only [hm, ↓reduceIte, Traceful.run_bind, Traceful.run_failure]

theorem at?_stEntry_logMessageKeyAndStore_rhda
    (me : Participant) (s : SessionInfo) (dir : KeyDir)
    (seed pqSalt : DY.Bytes) (n : UInt32) (rIdx pIdx : Nat) (newSt : TRState)
    (tr : ExecTrace) {i : Nat} {q : Participant} {st : TRState}
    (hat : (((logMessageKeyAndStore me s dir seed pqSalt n rIdx pIdx newSt).run tr).2.val.at? i :
      Option StEntry) = some ⟨⟨q, st⟩⟩) :
    (tr.at? i : Option StEntry) = some ⟨⟨q, st⟩⟩ ∨
      (i = tr.length + 1 ∧ q = me ∧ st = newSt) := by
  have hrun : ((logMessageKeyAndStore me s dir seed pqSalt n rIdx pIdx newSt).run tr).2.val =
      (tr.append (⟨TREvent.MessageKey s dir seed pqSalt n rIdx pIdx⟩ : TREntry)).append
        (⟨⟨me, newSt⟩⟩ : StEntry) := by
    unfold logMessageKeyAndStore
    simp only [Symbolic.DYBridge.DY.ProtocolEvent.logEvent_eq_1,
      Symbolic.DYBridge.DY.PersistentLocalState.storeLocalState_eq_1,
      Symbolic.DYBridge.DY.PersistentGlobalState.storeGlobalState_eq_1,
      Symbolic.DYBridge.DY.appendEntry_eq_1,
      Traceful.run_bind, Traceful.run_pure, Traceful.run_mk]
  rw [hrun] at hat
  rcases at?_stEntry_append_stEntry_cases_rhda hat with hat0 | ⟨hi, hq, hst⟩
  · rw [at?_append_non_entry _ _ rfl] at hat0
    exact Or.inl hat0
  · rw [Symbolic.DYBridge.DY.Trace.append_eq_1, Symbolic.DYBridge.DY.Trace.length_eq_2] at hi
    exact Or.inr ⟨hi, hq, hst⟩

theorem logEvent_run_rhda (ev : TREvent) (tr : ExecTrace) :
    ((DY.ProtocolEvent.logEvent ev).run tr).1 = some () ∧
      ((DY.ProtocolEvent.logEvent ev).run tr).2.val = tr.append (⟨ev⟩ : TREntry) := by
  simp only [Symbolic.DYBridge.DY.ProtocolEvent.logEvent_eq_1,
    Symbolic.DYBridge.DY.appendEntry_eq_1,
    Traceful.run_bind, Traceful.run_mk, Traceful.run_pure, and_self]

theorem availableStates_move_decrypt_cases
    (r₀ : ProtocolSetup) (ms : List Move) (me : Participant)
    (stateIdx msgIdx pqIdx : Nat) (spqrMsgIdx : UInt32) (wrapped : Bool := false) :
    let m := Move.decrypt me stateIdx msgIdx pqIdx spqrMsgIdx wrapped
    let tr₀ := runTraceMoves r₀ ms
    let tr₁ := runTraceMoves r₀ (ms ++ [m])
    ∀ st ∈ availableStates r₀ tr₁,
      st ∈ availableStates r₀ tr₀ ∨
        (tr₁.at? (tr₁.length - 1) : Option StEntry) = some ⟨⟨me, st⟩⟩ := by
  intro m tr₀ tr₁ st hst
  have htr₁ : tr₁ = m.next tr₀ := runTrace_snoc r₀ ms m
  rcases mem_availableStates_iff_rhda.mp hst with ⟨i, q, hlo, hat⟩
  rw [htr₁] at hat ⊢
  revert hat
  unfold m Move.next Move.act
  rw [run_bind_pure_val]
  simp (config := { zeta := false, beta := false, eta := false, proj := false, iota := false, failIfUnchanged := false }) only [DY.Libsignal.TripleRatchet.messageDecrypt_eq_inline]
  rw [run_bind_snd, getLocalState_snd]
  rcases ((PersistentLocalState.getLocalState me stateIdx : Traceful TRState).run tr₀).1 with _ | st0
  · exact fun hat => Or.inl (mem_availableStates_iff_rhda.mpr ⟨i, q, hlo, hat⟩)
  · dsimp only
    rw [run_bind_snd, receiveSignalMsg_snd_val_rhda]
    rcases ((DY.Libsignal.TripleRatchet.receiveSignalMsg msgIdx).run tr₀).1 with _ | msg
    · exact fun hat => Or.inl (mem_availableStates_iff_rhda.mpr ⟨i, q, hlo, hat⟩)
    · dsimp only
      rw [run_bind_snd]
      have hens_st : ∀ j q' s',
          (((ensureReceiverChain st0 msg.ratchetKey).run tr₀).2.val.at? j : Option StEntry) = some ⟨⟨q', s'⟩⟩ →
          (tr₀.at? j : Option StEntry) = some ⟨⟨q', s'⟩⟩ := by
        intro j q' s' h_at
        rcases hfind : findRecvChain st0.recv msg.ratchetKey with _ | c0
        · rcases hlow : x25519LowOrder msg.ratchetKey with _ | _
          · rw [(RecvDec.ensureReceiverChain_run_ratchet tr₀ hfind hlow).2,
                at?_append_non_entry _ _ rfl] at h_at
            exact h_at
          · simp (config := { zeta := false, beta := false, eta := false, proj := false, iota := false, failIfUnchanged := false }) only [DY.Libsignal.TripleRatchet.ensureReceiverChain_eq_recvChainFor] at h_at; unfold recvChainFor TRState.toDRState at h_at
            dsimp only at h_at; rw [hfind] at h_at
            simp only [hlow, ↓reduceIte, Traceful.run_failure] at h_at
            exact h_at
        · rw [(RecvDec.ensureReceiverChain_run_noRatchet tr₀ hfind).2] at h_at
          exact h_at
      rcases hens : (ensureReceiverChain st0 msg.ratchetKey).run tr₀ with ⟨_ | ⟨st1, c, ratcheted⟩, tr_ens⟩
      · intro hat
        have hat0 : (tr₀.at? i : Option StEntry) = some ⟨⟨q, st⟩⟩ := by
          apply hens_st; rw [hens]; exact hat
        exact Or.inl (mem_availableStates_iff_rhda.mpr ⟨i, q, hlo, hat0⟩)
      · have hens_imp : ∀ j q' s',
            (tr_ens.val.at? j : Option StEntry) = some ⟨⟨q', s'⟩⟩ →
            (tr₀.at? j : Option StEntry) = some ⟨⟨q', s'⟩⟩ := by
          intro j q' s' h_at; apply hens_st; rw [hens]; exact h_at
        dsimp only
        rcases consumeMessageKey c msg.counter with _ | ⟨seed, c'⟩
        · intro hat; dsimp only at hat; rw [Traceful.run_failure] at hat
          exact Or.inl (mem_availableStates_iff_rhda.mpr ⟨i, q, hlo, hens_imp i q st hat⟩)
        · dsimp only
          rcases Spqr.spqrRecv st1.spqr msg.pqRatchet spqrMsgIdx with _ | ⟨spqr', key⟩
          · intro hat; dsimp only at hat; rw [Traceful.run_failure] at hat
            exact Or.inl (mem_availableStates_iff_rhda.mpr ⟨i, q, hlo, hens_imp i q st hat⟩)
          · dsimp only
            rw [run_bind_snd]
            let tr_k := tr_ens.val.append (⟨key⟩ : Network.ExecEntryT)
            have hsm : (DY.Network.sendMessage key).run tr_ens.val =
                (some tr_ens.val.length, ⟨tr_k, Trace.append_le _ _⟩) := by
              rw [Symbolic.DYBridge.DY.Network.sendMessage_eq_1, Symbolic.DYBridge.DY.appendEntry_eq_1, Traceful.run_mk]
            rw [hsm]; dsimp only
            rw [run_bind_snd, receiveMessage_snd_val_rhda]
            rcases ((DY.Network.receiveMessage pqIdx).run tr_k).1 with _ | pqSalt
            · intro hat
              rw [at?_append_non_entry _ _ rfl] at hat
              exact Or.inl (mem_availableStates_iff_rhda.mpr ⟨i, q, hlo, hens_imp i q st hat⟩)
            · dsimp only
              rw [run_bind_snd, verifyMacAndDecrypt_snd_val_rhda]
              rcases ((DY.Libsignal.TripleRatchet.verifyMacAndDecrypt st1 msg pqSalt seed).run tr_k).1 with _ | ptTerm
              · intro hat
                rw [at?_append_non_entry _ _ rfl] at hat
                exact Or.inl (mem_availableStates_iff_rhda.mpr ⟨i, q, hlo, hens_imp i q st hat⟩)
              · dsimp only
                rcases ratcheted with _ | _
                · simp only [Bool.false_eq_true, ↓reduceIte]
                  obtain ⟨hsk1, hsk2⟩ := RecvDec.logSkippedKeys_run (st1.sessionInfo me) msg.ratchetKey c.rIdx stateIdx
                    c.chainKey c.index (msg.counter.toNat - c.index.toNat) tr_k
                  rw [run_bind_snd, hsk1, hsk2]; dsimp only
                  rw [run_bind_snd, (logEvent_run_rhda _ _).1, (logEvent_run_rhda _ _).2]; dsimp only
                  intro hat
                  rcases at?_stEntry_logMessageKeyAndStore_rhda me (st1.sessionInfo me) .receiver
                      seed pqSalt msg.counter c.rIdx stateIdx
                      { st1 with recv := setRecvChain st1.recv c', spqr := spqr' } _ hat with hat0 | ⟨hi, rfl, rfl⟩
                  · rw [at?_append_non_entry _ _ rfl, at?_stEntry_logSkippedKeysTr,
                        at?_append_non_entry _ _ rfl] at hat0
                    exact Or.inl (mem_availableStates_iff_rhda.mpr ⟨i, q, hlo, hens_imp i q st hat0⟩)
                  · right
                    have hsub : ∀ (t0 : ExecTrace) (e0 : StEntry), (t0.append e0).length - 1 = t0.length :=
                      fun t0 e0 => by
                        simp only [Symbolic.DYBridge.DY.Trace.append_eq_1, Symbolic.DYBridge.DY.Trace.length_eq_2,
                          Nat.add_sub_cancel]
                    unfold logMessageKeyAndStore
                    simp only [Symbolic.DYBridge.DY.ProtocolEvent.logEvent_eq_1,
                      Symbolic.DYBridge.DY.PersistentLocalState.storeLocalState_eq_1,
                      Symbolic.DYBridge.DY.PersistentGlobalState.storeGlobalState_eq_1,
                      Symbolic.DYBridge.DY.appendEntry_eq_1,
                      Traceful.run_bind, Traceful.run_pure, Traceful.run_mk]
                    rw [hsub]
                    exact Trace.at?_append _ _
                · simp only [↓reduceIte]
                  let tr_dh := (tr_k.append
                    (⟨TREvent.DHRatchet me st1.peer msg.ratchetKey (DY.DiffieHellman.dhPk st1.dhs)⟩ : TREntry)).append
                    (⟨TREvent.HonestDH (st1.sessionInfo me) st1.dhs (st1.rIdx - 2)⟩ : TREntry)
                  obtain ⟨hsk1, hsk2⟩ := RecvDec.logSkippedKeys_run (st1.sessionInfo me) msg.ratchetKey c.rIdx stateIdx
                    c.chainKey c.index (msg.counter.toNat - c.index.toNat) tr_dh
                  rw [run_bind_snd, (logEvent_run_rhda _ _).1, (logEvent_run_rhda _ _).2]; dsimp only
                  rw [run_bind_snd, (logEvent_run_rhda _ _).1, (logEvent_run_rhda _ _).2]; dsimp only
                  rw [run_bind_snd, hsk1, hsk2]; dsimp only
                  rw [run_bind_snd, (logEvent_run_rhda _ _).1, (logEvent_run_rhda _ _).2]; dsimp only
                  intro hat
                  rcases at?_stEntry_logMessageKeyAndStore_rhda me (st1.sessionInfo me) .receiver
                      seed pqSalt msg.counter c.rIdx stateIdx
                      { st1 with recv := setRecvChain st1.recv c', spqr := spqr' } _ hat with hat0 | ⟨hi, rfl, rfl⟩
                  · rw [at?_append_non_entry _ _ rfl, at?_stEntry_logSkippedKeysTr,
                        at?_append_non_entry _ _ rfl, at?_append_non_entry _ _ rfl,
                        at?_append_non_entry _ _ rfl] at hat0
                    exact Or.inl (mem_availableStates_iff_rhda.mpr ⟨i, q, hlo, hens_imp i q st hat0⟩)
                  · right
                    have hsub : ∀ (t0 : ExecTrace) (e0 : StEntry), (t0.append e0).length - 1 = t0.length :=
                      fun t0 e0 => by
                        simp only [Symbolic.DYBridge.DY.Trace.append_eq_1, Symbolic.DYBridge.DY.Trace.length_eq_2,
                          Nat.add_sub_cancel]
                    unfold logMessageKeyAndStore
                    simp only [Symbolic.DYBridge.DY.ProtocolEvent.logEvent_eq_1,
                      Symbolic.DYBridge.DY.PersistentLocalState.storeLocalState_eq_1,
                      Symbolic.DYBridge.DY.PersistentGlobalState.storeGlobalState_eq_1,
                      Symbolic.DYBridge.DY.appendEntry_eq_1,
                      Traceful.run_bind, Traceful.run_pure, Traceful.run_mk]
                    rw [hsub]
                    exact Trace.at?_append _ _

set_option maxHeartbeats 800000 in
theorem availableStates_move_decryptSkipped_cases
    (r₀ : ProtocolSetup) (ms : List Move) (me : Participant)
    (stateIdx msgIdx skIdx pqIdx : Nat) (spqrMsgIdx : UInt32) (wrapped : Bool := false) :
    let m := Move.decryptSkipped me stateIdx msgIdx skIdx pqIdx spqrMsgIdx wrapped
    let tr₀ := runTraceMoves r₀ ms
    let tr₁ := runTraceMoves r₀ (ms ++ [m])
    ∀ st ∈ availableStates r₀ tr₁,
      st ∈ availableStates r₀ tr₀ ∨
        (tr₁.at? (tr₁.length - 1) : Option StEntry) = some ⟨⟨me, st⟩⟩ := by
  intro m tr₀ tr₁ st hst
  have htr₁ : tr₁ = m.next tr₀ := runTrace_snoc r₀ ms m
  rcases mem_availableStates_iff_rhda.mp hst with ⟨i, q, hlo, hat⟩
  rw [htr₁] at hat ⊢; revert hat
  unfold m Move.next Move.act; rw [run_bind_pure_val]
  unfold DY.Libsignal.TripleRatchet.messageDecryptSkipped
  rw [run_bind_snd, getLocalState_snd]
  rcases ((PersistentLocalState.getLocalState me stateIdx : Traceful TRState).run tr₀).1 with _ | st0
  · exact fun hat => Or.inl (mem_availableStates_iff_rhda.mpr ⟨i, q, hlo, hat⟩)
  · dsimp only; rw [run_bind_snd, receiveSignalMsg_snd_val_rhda]
    rcases ((DY.Libsignal.TripleRatchet.receiveSignalMsg msgIdx).run tr₀).1 with _ | msg
    · exact fun hat => Or.inl (mem_availableStates_iff_rhda.mpr ⟨i, q, hlo, hat⟩)
    · dsimp only; rw [run_bind_snd]
      have hge_val : ((DY.getEntry skIdx : Traceful TREntry).run tr₀).2.val = tr₀ := by
        rw [Symbolic.DYBridge.DY.getEntry_eq_1, Traceful.run_mk]
      rw [hge_val]
      rcases ((DY.getEntry skIdx : Traceful TREntry).run tr₀).1 with _ | ⟨⟨ev⟩⟩
      · exact fun hat => Or.inl (mem_availableStates_iff_rhda.mpr ⟨i, q, hlo, hat⟩)
      · cases ev
        case SkippedKeyStored s pk n seed rIdx srcIdx =>
          dsimp only
          by_cases hg : s = st0.sessionInfo me ∧ pk = msg.ratchetKey ∧ n = msg.counter ∧
              (DY.Libsignal.TripleRatchet.findRecvChain st0.toDRState.recv pk).isSome = true
          · rcases hg with ⟨rfl, rfl, rfl, hfc⟩
            simp only [_root_.guard, hfc, and_self, ↓reduceIte]
            rw [run_bind_snd, Traceful.run_pure]; dsimp only
            rw [run_bind_snd]
            have hgt_val : ((guardTrace fun tr => !skippedKeyUsedB tr skIdx).run tr₀).2.val = tr₀ := by
              unfold guardTrace; rw [Traceful.run_mk]
            rw [hgt_val]
            rcases ((guardTrace fun tr => !skippedKeyUsedB tr skIdx).run tr₀).1 with _ | ⟨⟩
            · exact fun hat => Or.inl (mem_availableStates_iff_rhda.mpr ⟨i, q, hlo, hat⟩)
            · dsimp only
              rcases Spqr.spqrRecv st0.spqr msg.pqRatchet spqrMsgIdx with _ | ⟨spqr', key⟩
              · intro hat; dsimp only at hat; rw [Traceful.run_failure] at hat
                exact Or.inl (mem_availableStates_iff_rhda.mpr ⟨i, q, hlo, hat⟩)
              · dsimp only; rw [run_bind_snd]
                let tr_k := tr₀.append (⟨key⟩ : Network.ExecEntryT)
                have hsm : (DY.Network.sendMessage key).run tr₀ = (some tr₀.length, ⟨tr_k, Trace.append_le _ _⟩) := by
                  rw [Symbolic.DYBridge.DY.Network.sendMessage_eq_1, Symbolic.DYBridge.DY.appendEntry_eq_1, Traceful.run_mk]
                rw [hsm]; dsimp only; rw [run_bind_snd, receiveMessage_snd_val_rhda]
                rcases ((DY.Network.receiveMessage pqIdx).run tr_k).1 with _ | pqSalt
                · intro hat; rw [at?_append_non_entry _ _ rfl] at hat
                  exact Or.inl (mem_availableStates_iff_rhda.mpr ⟨i, q, hlo, hat⟩)
                · dsimp only; rw [run_bind_snd, verifyMacAndDecrypt_snd_val_rhda]
                  rcases ((DY.Libsignal.TripleRatchet.verifyMacAndDecrypt st0 msg pqSalt seed).run tr_k).1 with _ | ptTerm
                  · intro hat; rw [at?_append_non_entry _ _ rfl] at hat
                    exact Or.inl (mem_availableStates_iff_rhda.mpr ⟨i, q, hlo, hat⟩)
                  · dsimp only
                    rw [run_bind_snd, (logEvent_run_rhda _ _).1, (logEvent_run_rhda _ _).2]; dsimp only
                    rw [run_bind_snd, (logEvent_run_rhda _ _).1, (logEvent_run_rhda _ _).2]; dsimp only
                    intro hat
                    rcases at?_stEntry_logMessageKeyAndStore_rhda me (st0.sessionInfo me) .receiver
                        seed pqSalt msg.counter rIdx stateIdx
                        { st0 with spqr := spqr' } _ hat with hat0 | ⟨hi, rfl, rfl⟩
                    · rw [at?_append_non_entry _ _ rfl, at?_append_non_entry _ _ rfl,
                          at?_append_non_entry _ _ rfl] at hat0
                      exact Or.inl (mem_availableStates_iff_rhda.mpr ⟨i, q, hlo, hat0⟩)
                    · right
                      have hsub : ∀ (t0 : ExecTrace) (e0 : StEntry), (t0.append e0).length - 1 = t0.length :=
                        fun t0 e0 => by
                          simp only [Symbolic.DYBridge.DY.Trace.append_eq_1, Symbolic.DYBridge.DY.Trace.length_eq_2,
                            Nat.add_sub_cancel]
                      unfold logMessageKeyAndStore
                      simp only [Symbolic.DYBridge.DY.ProtocolEvent.logEvent_eq_1,
                        Symbolic.DYBridge.DY.PersistentLocalState.storeLocalState_eq_1,
                        Symbolic.DYBridge.DY.PersistentGlobalState.storeGlobalState_eq_1,
                        Symbolic.DYBridge.DY.appendEntry_eq_1,
                        Traceful.run_bind, Traceful.run_pure, Traceful.run_mk]
                      rw [hsub]
                      exact Trace.at?_append _ _
          · rw [run_bind_snd]
            simp only [_root_.guard, hg, ↓reduceIte, Traceful.run_failure]
            exact fun hat => Or.inl (mem_availableStates_iff_rhda.mpr ⟨i, q, hlo, hat⟩)
        all_goals
          intro hat; dsimp only at hat; rw [Traceful.run_failure] at hat
          exact Or.inl (mem_availableStates_iff_rhda.mpr ⟨i, q, hlo, hat⟩)

end Symbolic.Swarm.CREF.TR
