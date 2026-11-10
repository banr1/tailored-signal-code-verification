/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Symbolic.Proofs.Swarm.CREF.Cli.Rpk.SlotsZ6FramePure
import DY.Trace.Basic
import DY.Trace.Monad
import DY.Trace.Manipulation
import DY.Actions.ProtocolEvent
import DY.Actions.PersistentLocalState
import DY.Actions.PersistentGlobalState
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Symbolic.Proofs.Swarm.CREF.Cli.Rpk.SkippedKeyNoNewPure
import Symbolic.Proofs.Swarm.CREF.Prelude
import Symbolic.Proofs.Swarm.CREF.TR.FreshSigma
import VCVio.Prelude.Core
import Symbolic.DYBridge.DY.Trace.Basic
import Symbolic.DYBridge.DY.Trace.Monad
import Symbolic.DYBridge.DY.Trace.Manipulation
import Symbolic.DYBridge.DY.Actions.ProtocolEvent
import Symbolic.DYBridge.DY.Actions.PersistentLocalState
import Symbolic.DYBridge.DY.Actions.PersistentGlobalState

/-!
# Trace Preservation of `SkippedKeySrcLt` and Frame Wrappers

Proves `SkippedKeySrcLt (runTraceMoves r₀ ms)` across all composed protocol moves
and derives premise-free `SkippedInstallByteFresh` and `RecvRkNotLowAll` step lemmas.
-/

@[expose] public section

set_option autoImplicit false

cref_hide_foreign_instances

namespace Symbolic.Swarm.CREF.CliPure.RpkCli.Skr

cref_open
open Symbolic.Swarm.CREF.TR Symbolic.Swarm.CREF.CliPure.TR
open DY.DiffieHellman
open DY.Libsignal.TripleRatchet (SessionInfo RecvChain)
open DY.Libsignal.TripleRatchet
open CryptoProofLib.Refinement (ExternInterpretation)
open Symbolic.Swarm.CREF.TR.FreshSigma (run_bind_snd at?_eq_some_of_getLocalState_some)
open Symbolic.Swarm.CREF.TR.RecvDec
  (at?_append_of_lt at?_eq_none_of_le at?_append_non_entry
   logSkippedKeysTr logSkippedKeysTr_length
   at?_trEntry_logSkippedKeysTr_lt at?_trEntry_logSkippedKeysTr_add
   at?_trEntry_logSkippedKeysTr_exists at?_stEntry_logSkippedKeysTr
   decTailTr getLocalState_snd decrypt_next_noRatchet_eq)

private theorem noNewSkSnoc_of_act {r₀ : ProtocolSetup} {ms : List Move} {m : Move} (h : NoNewSk m.act) :
    NoNewSkSnoc r₀ ms m := by
  intro s pk n seed rIdx src i hev
  rw [runTrace_snoc] at hev
  exact h (runTraceMoves r₀ ms) s pk n seed rIdx src i hev

theorem noNewSkSnoc_aliceStart (r₀ : ProtocolSetup) (ms : List Move) (a b : Participant)
    (idStateIdx regIdxB : Nat) (h : DY.Libsignal.PQXDH.BundleHandles) (shown : Nat) :
    NoNewSkSnoc r₀ ms (.aliceStart a b idStateIdx regIdxB h shown) :=
  noNewSkSnoc_of_act (by
    unfold Move.act
    exact NoNewSk.bind (NoNewSk.aliceStart a b idStateIdx regIdxB h) fun _ => NoNewSk.pure _)

theorem noNewSkSnoc_encrypt (r₀ : ProtocolSetup) (ms : List Move) (me : Participant)
    (stH coinsLen pqIdx : Nat) (wrap : Option (Nat × Nat)) :
    NoNewSkSnoc r₀ ms (.encrypt me stH coinsLen pqIdx wrap) :=
  noNewSkSnoc_of_act (by unfold Move.act TripleRatchet.messageEncrypt; tr_nosk)

theorem noNewSkSnoc_decryptSkipped (r₀ : ProtocolSetup) (ms : List Move) (me : Participant)
    (stH msgIdx skIdx pqIdx : Nat) (spqrMsgIdx : UInt32) (wrapped : Bool) :
    NoNewSkSnoc r₀ ms (.decryptSkipped me stH msgIdx skIdx pqIdx spqrMsgIdx wrapped) :=
  noNewSkSnoc_of_act (by unfold Move.act TripleRatchet.messageDecryptSkipped; tr_nosk)

/-! ## Preservation of `SkippedKeySrcLt` across moves -/

theorem skippedKeySrcLt_logSkippedKeysTr (s₀ : SessionInfo) (pk₀ : DY.Bytes)
    (rIdx₀ src₀ : Nat) (ck : DY.Bytes) (n₀ : UInt32) (k : Nat) {tr : ExecTrace}
    (hsrc : src₀ < tr.length) (h : SkippedKeySrcLt tr) :
    SkippedKeySrcLt (logSkippedKeysTr s₀ pk₀ rIdx₀ src₀ ck n₀ k tr) := by
  intro s pk n seed rIdx src i hev
  rw [logSkippedKeysTr_length]
  rcases eventLoggedAt_logSkippedKeysTr_iff s₀ pk₀ rIdx₀ src₀ ck n₀ k tr _ i hev with h1 | ⟨_, _, heq⟩
  · have := h s pk n seed rIdx src i h1; omega
  · injection heq with _ _ _ _ _ hsrc_eq; omega

private def PreservesSkSrcFrom (n₀ : Nat) {α : Type} (x : Traceful α) : Prop :=
  ∀ tr : ExecTrace, n₀ ≤ tr.length → SkippedKeySrcLt tr → SkippedKeySrcLt (x.run tr).2.val

private theorem PreservesSkSrcFrom.of_noNewSk {n₀ : Nat} {α : Type} {x : Traceful α}
    (hx : NoNewSk x) : PreservesSkSrcFrom n₀ x := by
  intro tr _ h s pk n seed rIdx src i hev
  exact Nat.lt_of_lt_of_le (h s pk n seed rIdx src i (hx tr s pk n seed rIdx src i hev))
    (Trace.length_le tr (x.run tr).2.val (x.run tr).2.property)

private theorem PreservesSkSrcFrom.bind {n₀ : Nat} {α β : Type} {x : Traceful α} {f : α → Traceful β}
    (hx : PreservesSkSrcFrom n₀ x) (hf : ∀ a, PreservesSkSrcFrom n₀ (f a)) :
    PreservesSkSrcFrom n₀ (x >>= f) := by
  intro tr hn₀ hsk
  have hle : tr.length ≤ (x.run tr).2.val.length :=
    Trace.length_le tr (x.run tr).2.val (x.run tr).2.property
  have h1 := hx tr hn₀ hsk
  rw [Traceful.run_bind]
  rcases h : x.run tr with ⟨_ | a, trMid, _⟩
  · rw [h] at h1; exact h1
  · rw [h] at h1 hle; exact hf a trMid (Nat.le_trans hn₀ hle) h1

private theorem PreservesSkSrcFrom.prodCasesOn {n₀ : Nat} {α β γ : Type}
    (p : α × β) (f : α → β → Traceful γ)
    (hf : ∀ a b, PreservesSkSrcFrom n₀ (f a b)) :
    PreservesSkSrcFrom n₀ (Prod.casesOn p f) := by
  rcases p with ⟨a, b⟩; exact hf a b

private theorem PreservesSkSrcFrom.optionCasesOn {n₀ : Nat} {α β : Type}
    (o : Option α) (noneCase : Traceful β) (someCase : α → Traceful β)
    (hn : PreservesSkSrcFrom n₀ noneCase) (hs : ∀ a, PreservesSkSrcFrom n₀ (someCase a)) :
    PreservesSkSrcFrom n₀ (Option.casesOn o noneCase someCase) := by
  rcases o with _ | a
  · exact hn
  · exact hs a

private theorem PreservesSkSrcFrom.logSkippedKeys (s : SessionInfo) (pk : DY.Bytes)
    (rIdx src : Nat) (ck : DY.Bytes) (n : UInt32) (k : Nat) :
    PreservesSkSrcFrom (src + 1) (TripleRatchet.logSkippedKeys s pk rIdx src ck n k) := by
  intro tr hsrc hsk
  rw [(RecvDec.logSkippedKeys_run s pk rIdx src ck n k tr).2]
  exact skippedKeySrcLt_logSkippedKeysTr s pk rIdx src ck n k hsrc hsk

private theorem PreservesSkSrcFrom.bind_getLocalState {n₀ : Nat} {β : Type}
    (me : Participant) (stH : Nat) {f : TRState → Traceful β}
    (hf : ∀ st, PreservesSkSrcFrom (stH + 1) (f st)) :
    PreservesSkSrcFrom n₀ (PersistentLocalState.getLocalState me stH >>= f) := by
  intro tr _ hsk
  rw [run_bind_snd, getLocalState_snd]
  rcases hst : ((PersistentLocalState.getLocalState me stH : Traceful TRState).run tr).1 with _ | st
  · exact hsk
  · have hat := at?_eq_some_of_getLocalState_some hst
    have hlt : stH < tr.length := by
      have := Trace.at?_eq_some_implies_length_le (EntryT := StEntry) tr stH
      rw [hat] at this; exact this
    exact hf st tr hlt hsk

private theorem PreservesSkSrcFrom.bobStartTail {n₀ : Nat} (b : Participant) (st : TRState)
    (msg : TRSignalMsg) (c : RecvChain) (skipped : Nat) (m seed pqSalt : DY.Bytes)
    (st' : TRState) :
    PreservesSkSrcFrom n₀ (do
      let childIdx := (← TripleRatchet.traceLength) + skipped + 2
      TripleRatchet.logSkippedKeys (st.sessionInfo b) msg.ratchetKey c.rIdx childIdx c.chainKey c.index skipped
      DY.ProtocolEvent.logEvent (TREvent.Received b st.peer msg.ratchetKey msg.counter m)
      TripleRatchet.logMessageKeyAndStore b (st.sessionInfo b) .receiver seed pqSalt
        msg.counter c.rIdx childIdx st') := by
  intro tr _ hsk
  let childIdx := tr.length + skipped + 2
  let tr₁ := logSkippedKeysTr (st.sessionInfo b) msg.ratchetKey c.rIdx childIdx c.chainKey c.index skipped tr
  let tr₂ := tr₁.append (⟨TREvent.Received b st.peer msg.ratchetKey msg.counter m⟩ : TREntry)
  let tr₃ := (tr₂.append (⟨TREvent.MessageKey (st.sessionInfo b) .receiver seed pqSalt
    msg.counter c.rIdx childIdx⟩ : TREntry)).append (⟨⟨b, st'⟩⟩ : StEntry)
  have hrun : ((do
      let childIdx := (← TripleRatchet.traceLength) + skipped + 2
      TripleRatchet.logSkippedKeys (st.sessionInfo b) msg.ratchetKey c.rIdx childIdx c.chainKey c.index skipped
      DY.ProtocolEvent.logEvent (TREvent.Received b st.peer msg.ratchetKey msg.counter m)
      TripleRatchet.logMessageKeyAndStore b (st.sessionInfo b) .receiver seed pqSalt
        msg.counter c.rIdx childIdx st').run tr).2.val = tr₃ := by
    simp only [TripleRatchet.traceLength, TripleRatchet.logMessageKeyAndStore,
      Symbolic.DYBridge.DY.ProtocolEvent.logEvent_eq_1, Symbolic.DYBridge.DY.PersistentLocalState.storeLocalState_eq_1,
      Symbolic.DYBridge.DY.PersistentGlobalState.storeGlobalState_eq_1, Symbolic.DYBridge.DY.appendEntry_eq_1,
      Traceful.run_bind, Traceful.run_pure, Traceful.run_mk,
      RecvDec.logSkippedKeys_run]
    rfl
  rw [hrun]
  intro s pk n seed' rIdx src i hev
  have hlen₁ : tr₁.length = tr.length + skipped :=
    logSkippedKeysTr_length (st.sessionInfo b) msg.ratchetKey c.rIdx childIdx c.chainKey c.index skipped tr
  have hlen₃ : tr₃.length = tr.length + skipped + 3 := by
    dsimp only [tr₃, tr₂]
    simp only [Symbolic.DYBridge.DY.Trace.append_eq_1, Symbolic.DYBridge.DY.Trace.length_eq_2]
    omega
  rw [hlen₃]
  simp only [Symbolic.DYBridge.DY.Trace.EventLoggedAt_eq_1] at hev
  rw [at?_append_non_entry _ (⟨⟨b, st'⟩⟩ : StEntry) rfl i] at hev
  rw [← Symbolic.DYBridge.DY.Trace.EventLoggedAt_eq_1] at hev
  have hev₂ := eventLoggedAt_append_trEntry_ne tr₂ _ _ (by rintro ⟨⟩) i hev
  have hev₁ := eventLoggedAt_append_trEntry_ne tr₁ _ _ (by rintro ⟨⟩) i hev₂
  rcases eventLoggedAt_logSkippedKeysTr_iff (st.sessionInfo b) msg.ratchetKey c.rIdx childIdx
      c.chainKey c.index skipped tr _ i hev₁ with h0 | ⟨_, _, heq⟩
  · have := hsk s pk n seed' rIdx src i h0; omega
  · injection heq with _ _ _ _ _ hsrc_eq; omega

local macro "tr_sksrc" : tactic => `(tactic| repeat (first
  | with_reducible apply PreservesSkSrcFrom.bobStartTail
  | with_reducible apply PreservesSkSrcFrom.bind_getLocalState
  | with_reducible apply PreservesSkSrcFrom.logSkippedKeys
  | with_reducible apply PreservesSkSrcFrom.bind
  | with_reducible apply PreservesSkSrcFrom.prodCasesOn
  | with_reducible apply PreservesSkSrcFrom.optionCasesOn
  | (with_reducible apply PreservesSkSrcFrom.of_noNewSk;
     first
       | with_reducible apply NoNewSk.pure | with_reducible apply NoNewSk.failure
       | with_reducible apply NoNewSk.genRand
       | with_reducible apply NoNewSk.storeLocalState
       | with_reducible apply NoNewSk.storeLocalStatePQ
       | with_reducible apply NoNewSk.sendMessage
       | with_reducible apply NoNewSk.getLocalState
       | with_reducible apply NoNewSk.getLocalStatePQ
       | with_reducible apply NoNewSk.getKey
       | with_reducible apply NoNewSk.lookupIdentity
       | with_reducible apply NoNewSk.receiveMessage
       | with_reducible apply NoNewSk.getEntry
       | with_reducible apply NoNewSk.receiveSignalMsg
       | with_reducible apply NoNewSk.verifyMacAndDecrypt
       | with_reducible apply NoNewSk.dhRatchetStep
       | with_reducible apply NoNewSk.ensureReceiverChain
       | with_reducible apply NoNewSk.bobHandshake
       | with_reducible apply NoNewSk.guardP | with_reducible apply NoNewSk.monadLiftErr
       | with_reducible apply NoNewSk.guardTrace | with_reducible apply NoNewSk.requireTracePredicate
       | with_reducible apply NoNewSk.traceLength
       | with_reducible apply NoNewSk.logMessageKeyAndStore
       | with_reducible apply NoNewSk.logEventPQ
       | with_reducible apply NoNewSk.logEventC
       | with_reducible apply NoNewSk.logEvent _ (by rfl))
  | split | with_reducible intro))

private theorem PreservesSkSrcFrom.bobStart {n₀ : Nat} (b a : Participant)
    (kh : DY.Libsignal.PQXDH.BobKeyHandles) (regIdxA : Nat)
    (mh : DY.Libsignal.PQXDH.PreKeyMsgHandles) (pqIdx : Nat) (spqrMsgIdx : UInt32) :
    PreservesSkSrcFrom n₀
      (DY.Libsignal.Composed.bobStart b a kh regIdxA mh pqIdx spqrMsgIdx) := by
  simp (config := { zeta := false, beta := false, eta := false, proj := false, iota := false, failIfUnchanged := false }) only [DY.Libsignal.Composed.bobStart_eq_inline]; tr_sksrc

theorem skippedKeySrcLt_move_next (m : Move) {tr : ExecTrace} (h : SkippedKeySrcLt tr) :
    SkippedKeySrcLt (m.next tr) := by
  refine (?_ : PreservesSkSrcFrom 0 m.act) tr (Nat.zero_le _) h
  cases m with
  | setup a b withOpk =>
    exact PreservesSkSrcFrom.of_noNewSk (NoNewSk.setupAct a b withOpk)
  | aliceStart a b idStateIdx regIdxB bh shown =>
    unfold Move.act
    exact PreservesSkSrcFrom.of_noNewSk
      (NoNewSk.bind (NoNewSk.aliceStart a b idStateIdx regIdxB bh) fun _ => NoNewSk.pure _)
  | bobStart b a kh regIdxA mh pqIdx spqrMsgIdx shown =>
    unfold Move.act
    exact PreservesSkSrcFrom.bind
      (PreservesSkSrcFrom.bobStart b a kh regIdxA mh pqIdx spqrMsgIdx)
      fun _ => PreservesSkSrcFrom.of_noNewSk (NoNewSk.pure _)
  | encrypt me stateIdx coinsLen pqIdx wrap =>
    exact PreservesSkSrcFrom.of_noNewSk (by unfold Move.act TripleRatchet.messageEncrypt; tr_nosk)
  | encryptAbort me stateIdx =>
    exact PreservesSkSrcFrom.of_noNewSk (by unfold Move.act TripleRatchet.messageEncryptAbort; tr_nosk)
  | encryptFail me stateIdx coinsLen =>
    exact PreservesSkSrcFrom.of_noNewSk (by unfold Move.act TripleRatchet.messageEncrypt; tr_nosk)
  | decrypt me stateIdx msgIdx pqIdx spqrMsgIdx wrapped =>
    unfold Move.act; simp (config := { zeta := false, beta := false, eta := false, proj := false, iota := false, failIfUnchanged := false }) only [DY.Libsignal.TripleRatchet.messageDecrypt_eq_inline]; tr_sksrc
  | decryptSkipped me stateIdx msgIdx skippedKeyEventIdx pqIdx spqrMsgIdx wrapped =>
    exact PreservesSkSrcFrom.of_noNewSk
      (by unfold Move.act TripleRatchet.messageDecryptSkipped; tr_nosk)
  | reject draws =>
    exact PreservesSkSrcFrom.of_noNewSk (by unfold Move.act; tr_nosk)
  | compromiseIK p stateIdx =>
    unfold Move.act
    exact PreservesSkSrcFrom.of_noNewSk
      (NoNewSk.bind (NoNewSk.compromiseIK p stateIdx) fun _ => NoNewSk.pure _)
  | compromiseSPK p stateIdx =>
    unfold Move.act
    exact PreservesSkSrcFrom.of_noNewSk
      (NoNewSk.bind (NoNewSk.compromiseSPK p stateIdx) fun _ => NoNewSk.pure _)
  | compromisePQSPK p stateIdx =>
    unfold Move.act
    exact PreservesSkSrcFrom.of_noNewSk
      (NoNewSk.bind (NoNewSk.compromisePQSPK p stateIdx) fun _ => NoNewSk.pure _)
  | compromiseOPK p stateIdx =>
    unfold Move.act
    exact PreservesSkSrcFrom.of_noNewSk
      (NoNewSk.bind (NoNewSk.compromiseOPK p stateIdx) fun _ => NoNewSk.pure _)
  | exposeKey me stateIdx k =>
    exact PreservesSkSrcFrom.of_noNewSk (by unfold Move.act TripleRatchet.exposeKey; tr_nosk)
  | exposeSpqr me stateIdx =>
    exact PreservesSkSrcFrom.of_noNewSk (by unfold Move.act TripleRatchet.exposeSpqr; tr_nosk)
  | exposeSkipped skippedKeyEventIdx =>
    exact PreservesSkSrcFrom.of_noNewSk (by unfold Move.act TripleRatchet.exposeSkipped; tr_nosk)
  | attackerSend msg =>
    exact PreservesSkSrcFrom.of_noNewSk (by unfold Move.act; tr_nosk)
  | brkDH =>
    exact PreservesSkSrcFrom.of_noNewSk (NoNewSk.logEventPQ .BrokenDH)
  | brkKEM =>
    exact PreservesSkSrcFrom.of_noNewSk (NoNewSk.logEventPQ .BrokenKEM)

theorem skippedKeySrcLt_setupTrace (r₀ : ProtocolSetup) : SkippedKeySrcLt (setupTrace r₀) := by
  unfold setupTrace
  exact skippedKeySrcLt_move_next (.setup r₀.alice r₀.bob r₀.withOpk)
    (fun _ _ _ _ _ _ i h => by
      have hlen := Trace.at?_eq_some_implies_length_le (EntryT := TREntry) (Trace.nil : ExecTrace) i
      rw [Symbolic.DYBridge.DY.Trace.EventLoggedAt_eq_1] at h
      rw [h, Symbolic.DYBridge.DY.Trace.length_eq_1] at hlen
      omega)

theorem skippedKeySrcLt_runTrace (r₀ : ProtocolSetup) (ms : List Move) :
    SkippedKeySrcLt (runTraceMoves r₀ ms) := by
  induction ms using List.reverseRecOn with
  | nil => exact skippedKeySrcLt_setupTrace r₀
  | append_singleton ms m ih =>
    rw [runTrace_snoc]
    exact skippedKeySrcLt_move_next m ih

/-! ## Step lemmas for `SkippedInstallByteFresh` and `RecvRkNotLowAll` -/

theorem skippedInstallByteFresh_snoc_of_noNewSk'
    (interpretation : ExternInterpretation) (S : OpaqueSymbolSemantics) (g : Ghost)
    (r₀ : ProtocolSetup) (ms : List Move) (m : Move)
    (hno_new : NoNewSkSnoc r₀ ms m)
    (h1 : SkippedInstallByteFresh interpretation S g r₀ ms) :
    SkippedInstallByteFresh interpretation S g r₀ (ms ++ [m]) := by
  have hle : runTraceMoves r₀ ms ≤ runTraceMoves r₀ (ms ++ [m]) := by
    rw [runTrace_snoc]
    exact (m.act.run (runTraceMoves r₀ ms)).2.property
  exact skippedInstallByteFresh_of_le_of_noNewSk interpretation S g r₀ ms (ms ++ [m]) h1
    (skippedKeySrcLt_runTrace r₀ ms) hle hno_new

theorem skippedInstallByteFresh_encrypt'
    (interpretation : ExternInterpretation) (S : OpaqueSymbolSemantics) (g : Ghost)
    (r₀ : ProtocolSetup) (ms : List Move) (me : Participant) (stH coinsLen pqIdx : Nat)
    (wrap : Option (Nat × Nat) := none)
    (h1 : SkippedInstallByteFresh interpretation S g r₀ ms) :
    SkippedInstallByteFresh interpretation S g r₀ (ms ++ [.encrypt me stH coinsLen pqIdx wrap]) :=
  skippedInstallByteFresh_snoc_of_noNewSk' interpretation S g r₀ ms _
    (noNewSkSnoc_encrypt r₀ ms me stH coinsLen pqIdx wrap) h1

theorem skippedInstallByteFresh_decryptSkipped'
    (interpretation : ExternInterpretation) (S : OpaqueSymbolSemantics) (g : Ghost)
    (r₀ : ProtocolSetup) (ms : List Move)
    (me : Participant) (stH msgH evH pqIdx : Nat) (spqrMsgIdx : UInt32)
    (wrapped : Bool := false)
    (h1 : SkippedInstallByteFresh interpretation S g r₀ ms) :
    SkippedInstallByteFresh interpretation S g r₀
      (ms ++ [.decryptSkipped me stH msgH evH pqIdx spqrMsgIdx wrapped]) :=
  skippedInstallByteFresh_snoc_of_noNewSk' interpretation S g r₀ ms _
    (noNewSkSnoc_decryptSkipped r₀ ms me stH msgH evH pqIdx spqrMsgIdx wrapped) h1

end Symbolic.Swarm.CREF.CliPure.RpkCli.Skr
