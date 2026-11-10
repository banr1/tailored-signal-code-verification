/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Symbolic.Proofs.Swarm.CREF.Cli.RetiredModelTraces
import DY.Trace.Basic
import DY.Trace.Monad
import DY.Bytes.Basic
import DY.ALaCarte.Basic
import DY.Trace.Manipulation
import DY.Trace.BaseAttackerKnowledge
import DY.Actions.Network
import DY.Actions.PersistentLocalState
import DY.Actions.PersistentGlobalState
import DY.Actions.ProtocolEvent
import DY.Actions.Random
import Mathlib.Tactic.Push
import Symbolic.Proofs.Swarm.CREF.Prelude
import Symbolic.Proofs.Swarm.CREF.StateFaithful
import Symbolic.DYBridge.DY.Trace.Basic
import Symbolic.DYBridge.DY.Trace.Monad
import Symbolic.DYBridge.DY.Bytes.Basic
import Symbolic.DYBridge.DY.ALaCarte.Basic
import Symbolic.DYBridge.DY.Trace.Manipulation
import Symbolic.DYBridge.DY.Trace.BaseAttackerKnowledge
import Symbolic.DYBridge.DY.Actions.Network
import Symbolic.DYBridge.DY.Actions.PersistentLocalState
import Symbolic.DYBridge.DY.Actions.PersistentGlobalState
import Symbolic.DYBridge.DY.Actions.ProtocolEvent
import Symbolic.DYBridge.DY.Actions.Random

/-!
# Current-Snapshot Preservation of `StateFaithful`

Proves `stateFaithful_snoc_of_isCurrentSnapshot`: appending a move whose loaded session
snapshot (if any) satisfies `isCurrentSnapshot` preserves `StateFaithful`, because every
successful state-storing move appends a child snapshot for the same participant and
initiator flag and therefore invalidates `isCurrentSnapshot` at the parent index.
-/

@[expose] public section

set_option autoImplicit false

cref_hide_foreign_instances

namespace Symbolic.Swarm.CREF

cref_open

open DY
open TripleRatchet (TREvent TRState)

private abbrev TRStEntry :=
  PersistentGlobalState.State.ExecEntryT (PersistentLocalState.LocalState TRState)

private theorem sf_at?_eq_of_le_of_lt {E : Type} [ExecTraceTypes.Has E]
    {tr tr' : ExecTrace} (hle : tr ≤ tr') {i : Nat} (hi : i < tr.length) :
    (tr'.at? i : Option E) = (tr.at? i : Option E) := by
  have hi' : i < tr'.length := Nat.lt_of_lt_of_le hi (Trace.length_le _ _ hle)
  simp only [Trace.at?, hi, hi', ↓reduceDIte]
  rw [← Trace.at_le tr tr' i hi hle]

private theorem sf_at?_le_some {E : Type} [ExecTraceTypes.Has E]
    {tr tr' : ExecTrace} (hle : tr ≤ tr') {i : Nat} {x : E}
    (hx : (tr.at? i : Option E) = some x) :
    (tr'.at? i : Option E) = some x := by
  have hi : i < tr.length := by
    have h := Trace.at?_eq_some_implies_length_le (EntryT := E) tr i
    rw [hx] at h
    exact h
  rw [sf_at?_eq_of_le_of_lt hle hi]
  exact hx

private theorem sf_runMoves_le (ms : List Move) (tr : ExecTrace) :
    tr ≤ (runMoves ms tr).1 := by
  induction ms generalizing tr with
  | nil => exact Trace.le_refl tr
  | cons m ms ih =>
    exact Trace.le_trans _ _ _ ((m.act.run tr).2.property) (ih (m.next tr))

private theorem sf_runMoves_append_fst (ms₁ ms₂ : List Move) (tr : ExecTrace) :
    (runMoves (ms₁ ++ ms₂) tr).1 = (runMoves ms₂ (runMoves ms₁ tr).1).1 := by
  induction ms₁ generalizing tr with
  | nil => rfl
  | cons m ms₁ ih => exact ih (m.next tr)

private def StoresChildOf {α : Type} (p : Participant) (init : Bool) (x : Traceful α) : Prop :=
  ∀ tr : ExecTrace, (x.run tr).1.isSome = true →
    ∃ j : Nat, tr.length ≤ j ∧ j < (x.run tr).2.val.length ∧
      ∃ st' : TRState, st'.initiator = init ∧
        ((x.run tr).2.val.at? j : Option TRStEntry) = some ⟨⟨p, st'⟩⟩

private theorem sf_run_bind_fst {α β : Type} (x : Traceful α) (f : α → Traceful β) (tr : ExecTrace) :
    ((x >>= f).run tr).1 =
      match (x.run tr).1 with
      | some a => ((f a).run (x.run tr).2.val).1
      | none => none := by
  rw [Traceful.run_bind]
  rcases x.run tr with ⟨_ | a, tr₁⟩
  · rfl
  · rcases (f a).run tr₁.val with ⟨_, _⟩; rfl

private theorem sf_run_bind_snd {α β : Type} (x : Traceful α) (f : α → Traceful β) (tr : ExecTrace) :
    ((x >>= f).run tr).2.val =
      match (x.run tr).1 with
      | some a => ((f a).run (x.run tr).2.val).2.val
      | none => (x.run tr).2.val := by
  rw [Traceful.run_bind]
  rcases x.run tr with ⟨_ | a, tr₁⟩
  · rfl
  · rcases (f a).run tr₁.val with ⟨_, _⟩; rfl

private theorem sf_run_bind_some_decomp {α β : Type} (x : Traceful α) (f : α → Traceful β)
    (tr : ExecTrace) (hok : ((x >>= f).run tr).1.isSome = true) :
    ∃ a, (x.run tr).1 = some a ∧
      ((f a).run (x.run tr).2.val).1.isSome = true ∧
      ((x >>= f).run tr).2.val = ((f a).run (x.run tr).2.val).2.val := by
  rw [sf_run_bind_fst] at hok
  rcases hx : (x.run tr).1 with _ | a
  · rw [hx] at hok; cases hok
  · rw [hx] at hok
    exact ⟨a, rfl, hok, by rw [sf_run_bind_snd, hx]⟩

private theorem storesChildOf_bind_right {α β : Type} {p : Participant} {init : Bool}
    (x : Traceful α) {f : α → Traceful β}
    (hf : ∀ a, StoresChildOf p init (f a)) :
    StoresChildOf p init (x >>= f) := by
  intro tr hok
  obtain ⟨a, _, hfok, hval⟩ := sf_run_bind_some_decomp x f tr hok
  obtain ⟨j, hj1, hj2, st', hinit, hat⟩ := hf a (x.run tr).2.val hfok
  have hlen : tr.length ≤ (x.run tr).2.val.length :=
    Trace.length_le _ _ (x.run tr).2.property
  rw [← hval] at hj2 hat
  exact ⟨j, Nat.le_trans hlen hj1, hj2, st', hinit, hat⟩

private theorem storesChildOf_bind_left {α β : Type} {p : Participant} {init : Bool}
    {x : Traceful α} (f : α → Traceful β)
    (hx : StoresChildOf p init x) :
    StoresChildOf p init (x >>= f) := by
  intro tr hok
  obtain ⟨a, hxa, _, hval⟩ := sf_run_bind_some_decomp x f tr hok
  have hxok : (x.run tr).1.isSome = true := by rw [hxa]; rfl
  obtain ⟨j, hj1, hj2, st', hinit, hat⟩ := hx tr hxok
  have hle₂ : (x.run tr).2.val ≤ ((x >>= f).run tr).2.val := by
    rw [hval]
    exact ((f a).run (x.run tr).2.val).2.property
  exact ⟨j, hj1, Nat.lt_of_lt_of_le hj2 (Trace.length_le _ _ hle₂),
    st', hinit, sf_at?_le_some hle₂ hat⟩

private theorem storesChildOf_storeLocalState (p : Participant) {init : Bool} {st' : TRState}
    (hinit : st'.initiator = init) :
    StoresChildOf p init (PersistentLocalState.storeLocalState p st') := by
  intro tr _
  rw [Symbolic.DYBridge.DY.PersistentLocalState.storeLocalState_eq_1,
    Symbolic.DYBridge.DY.PersistentGlobalState.storeGlobalState_eq_1,
    Symbolic.DYBridge.DY.appendEntry_eq_1, DY.Traceful.run_mk]
  refine ⟨tr.length, Nat.le_refl _, ?_, st', hinit, ?_⟩
  · simp only [Symbolic.DYBridge.DY.Trace.append_eq_1, Symbolic.DYBridge.DY.Trace.length_eq_2]
    exact Nat.lt_succ_self tr.length
  · exact Trace.at?_append tr (⟨⟨p, st'⟩⟩ : TRStEntry)

private theorem storesChildOf_logMessageKeyAndStore (p : Participant) (s : TripleRatchet.SessionInfo)
    (dir : TripleRatchet.KeyDir) (seed pqSalt : DY.Bytes) (n : UInt32)
    (rIdx parIdx : Nat) {init : Bool} {st' : TRState} (hinit : st'.initiator = init) :
    StoresChildOf p init
      (TripleRatchet.logMessageKeyAndStore p s dir seed pqSalt n rIdx parIdx st') := by
  unfold TripleRatchet.logMessageKeyAndStore
  exact storesChildOf_bind_right _ fun _ => storesChildOf_storeLocalState p hinit

private theorem dhRatchetStep_initiator_eq {st₀ st₁ : TRState} {pk : DY.Bytes}
    {c₁ : TripleRatchet.RecvChain} {tr : ExecTrace}
    (h : ((TripleRatchet.dhRatchetStep st₀ pk).run tr).1 = some (st₁, c₁)) :
    st₁.initiator = st₀.initiator := by
  simp (config := { zeta := false, beta := false, eta := false, proj := false, iota := false, failIfUnchanged := false }) only [DY.Libsignal.TripleRatchet.dhRatchetStep_eq_guard] at h
  rw [sf_run_bind_fst] at h
  rcases hg : ((_root_.guard (!TripleRatchet.x25519LowOrder pk) : Traceful Unit).run tr).1 with _ | u
  · rw [hg] at h; cases h
  · rw [hg, sf_run_bind_fst] at h
    let tr₁ := ((_root_.guard (!TripleRatchet.x25519LowOrder pk) : Traceful Unit).run tr).2.val
    rcases hr : ((Random.genRand 32).run tr₁).1 with _ | dhs
    · rw [hr] at h; cases h
    · rw [hr] at h
      dsimp only at h
      rw [DY.Traceful.run_pure] at h
      injection h with hp
      injection hp with hst _
      rw [← hst]

private theorem ensureReceiverChain_initiator_eq {st₀ st : TRState} {pk : DY.Bytes}
    {c : TripleRatchet.RecvChain} {b : Bool} {tr : ExecTrace}
    (h : ((TripleRatchet.ensureReceiverChain st₀ pk).run tr).1 = some (st, c, b)) :
    st.initiator = st₀.initiator := by
  simp (config := { zeta := false, beta := false, eta := false, proj := false, iota := false, failIfUnchanged := false }) only [DY.Libsignal.TripleRatchet.ensureReceiverChain_eq_recvChainFor] at h
  rcases hrc : TripleRatchet.recvChainFor st₀.toDRState pk with _ | ⟨c₀, false | true⟩
  · rw [hrc, DY.Traceful.run_failure] at h; cases h
  · rw [hrc, DY.Traceful.run_pure] at h
    injection h with hp
    injection hp with hst _
    exact congrArg (fun s : TRState => s.initiator) hst.symm
  · rw [hrc, sf_run_bind_fst] at h
    rcases hdh : ((TripleRatchet.dhRatchetStep st₀ pk).run tr).1 with _ | ⟨st₁, c₁⟩
    · rw [hdh] at h; cases h
    · rw [hdh] at h
      dsimp only at h
      rw [DY.Traceful.run_pure] at h
      injection h with hp
      injection hp with hst _
      rw [← hst]
      exact dhRatchetStep_initiator_eq hdh

private theorem getGlobalState_some_at? {k : Nat}
    {ls : PersistentLocalState.LocalState TRState} {tr : ExecTrace}
    (h : ((PersistentGlobalState.getGlobalState k :
      Traceful (PersistentLocalState.LocalState TRState)).run tr).1 = some ls) :
    (tr.at? k : Option TRStEntry) = some ⟨ls⟩ ∧
    ((PersistentGlobalState.getGlobalState k :
      Traceful (PersistentLocalState.LocalState TRState)).run tr).2.val = tr := by
  simp only [Symbolic.DYBridge.DY.PersistentGlobalState.getGlobalState_eq_1] at h ⊢
  rw [sf_run_bind_fst] at h
  rw [sf_run_bind_snd]
  have hge1 : ((DY.getEntry k : Traceful TRStEntry).run tr).1 = tr.at? k := by
    rw [Symbolic.DYBridge.DY.getEntry_eq_1, DY.Traceful.run_mk]
  have hge2 : ((DY.getEntry k : Traceful TRStEntry).run tr).2.val = tr := by
    rw [Symbolic.DYBridge.DY.getEntry_eq_1, DY.Traceful.run_mk]
  rw [hge1] at h ⊢
  rcases hat : (tr.at? k : Option TRStEntry) with _ | ⟨⟨ls'⟩⟩
  · rw [hat] at h; cases h
  · rw [hat] at h
    dsimp only at h ⊢
    rw [DY.Traceful.run_pure] at h ⊢
    injection h with hls
    subst hls
    exact ⟨rfl, hge2⟩

private theorem getLocalState_some_at? {p : Participant} {k : Nat} {st : TRState} {tr : ExecTrace}
    (h : ((PersistentLocalState.getLocalState p k : Traceful TRState).run tr).1 = some st) :
    (tr.at? k : Option TRStEntry) = some ⟨⟨p, st⟩⟩ ∧
    ((PersistentLocalState.getLocalState p k : Traceful TRState).run tr).2.val = tr := by
  simp only [Symbolic.DYBridge.DY.PersistentLocalState.getLocalState_eq_1] at h ⊢
  rw [sf_run_bind_fst] at h
  rw [sf_run_bind_snd]
  rcases hgs : ((PersistentGlobalState.getGlobalState k :
      Traceful (PersistentLocalState.LocalState TRState)).run tr).1 with _ | ⟨p', st'⟩
  · rw [hgs] at h; cases h
  · obtain ⟨hat, hval⟩ := getGlobalState_some_at? hgs
    rw [hgs] at h
    dsimp only at h ⊢
    rw [hval, sf_run_bind_fst] at h
    rw [hval, sf_run_bind_snd]
    by_cases hp : p' = p
    · subst hp
      have hg1 : ((_root_.guard (p' = p') : Traceful Unit).run tr).1 = some () := by
        simp [_root_.guard, DY.Traceful.run_pure]
      have hg2 : ((_root_.guard (p' = p') : Traceful Unit).run tr).2.val = tr := by
        simp [_root_.guard, DY.Traceful.run_pure]
      rw [hg1] at h ⊢
      dsimp only at h ⊢
      rw [DY.Traceful.run_pure] at h ⊢
      injection h with hst
      subst hst
      exact ⟨hat, hg2⟩
    · have hg1 : ((_root_.guard (p' = p) : Traceful Unit).run tr).1 = none := by
        simp [_root_.guard, hp, DY.Traceful.run_failure]
      rw [hg1] at h
      cases h

private theorem not_isCurrentSnapshot_of_stateLoad_true_ok {mi : Move} {p : Participant}
    {k : Nat} {tr₀ tr₁ : ExecTrace}
    (hmi : mi.stateLoad? = some (p, k, true))
    (hok : (mi.act.run tr₀).1.isSome = true)
    (hle : mi.next tr₀ ≤ tr₁) :
    TripleRatchet.isCurrentSnapshot tr₁ k = false := by
  suffices h : ∃ (st₀ : TRState) (j : Nat) (st' : TRState),
      (tr₀.at? k : Option TRStEntry) = some ⟨⟨p, st₀⟩⟩ ∧
      tr₀.length ≤ j ∧ j < (mi.next tr₀).length ∧
      st'.initiator = st₀.initiator ∧
      ((mi.next tr₀).at? j : Option TRStEntry) = some ⟨⟨p, st'⟩⟩ by
    obtain ⟨st₀, j, st', hat_k₀, hj_ge, hj_lt₀, hinit, hat_j₀⟩ := h
    have hk_lt₀ : k < tr₀.length := by
      have hk := Trace.at?_eq_some_implies_length_le (EntryT := TRStEntry) tr₀ k
      rw [hat_k₀] at hk
      exact hk
    have hat_k₁ : (tr₁.at? k : Option TRStEntry) = some ⟨⟨p, st₀⟩⟩ :=
      sf_at?_le_some (Trace.le_trans _ _ _ (mi.act.run tr₀).2.property hle) hat_k₀
    have hat_j₁ : (tr₁.at? j : Option TRStEntry) = some ⟨⟨p, st'⟩⟩ :=
      sf_at?_le_some hle hat_j₀
    have hj_lt₁ : j < tr₁.length :=
      Nat.lt_of_lt_of_le hj_lt₀ (Trace.length_le _ _ hle)
    simp (config := { zeta := false, beta := false, eta := false, proj := false, iota := false, failIfUnchanged := false }) only [DY.Libsignal.TripleRatchet.isCurrentSnapshot_eq_at?]
    rw [hat_k₁]
    dsimp only
    rw [Bool.eq_false_iff]
    intro hall
    have hmem : j ∈ List.range' (k + 1) (tr₁.length - (k + 1)) :=
      List.mem_range'_1.mpr ⟨by omega, by omega⟩
    have hj_ok := List.all_eq_true.mp hall j hmem
    rw [hat_j₁] at hj_ok
    simp [hinit] at hj_ok
  cases mi with
  | encrypt me stateIdx coinsLen pqIdx wrap =>
    simp only [Move.stateLoad?, Option.some.injEq, Prod.mk.injEq] at hmi
    rcases hmi with ⟨rfl, rfl, -⟩
    obtain ⟨_, henc, _, hval⟩ :=
      sf_run_bind_some_decomp
        (TripleRatchet.messageEncrypt me stateIdx coinsLen pqIdx) (fun _ => pure ()) tr₀ hok
    have henc_ok :
        ((TripleRatchet.messageEncrypt me stateIdx coinsLen pqIdx).run tr₀).1.isSome = true := by
      rw [henc]; rfl
    unfold TripleRatchet.messageEncrypt at henc_ok
    obtain ⟨st₀, hget, hrest_ok, hrest_val⟩ := sf_run_bind_some_decomp _ _ tr₀ henc_ok
    obtain ⟨hat_k, hget_val⟩ := getLocalState_some_at? hget
    rw [hget_val] at hrest_ok hrest_val
    have hsc_apply : ∀ {α : Type} {x : Traceful α} {tr : ExecTrace},
        (x.run tr).1.isSome = true → StoresChildOf me st₀.initiator x →
        ∃ j : Nat, tr.length ≤ j ∧ j < (x.run tr).2.val.length ∧
          ∃ st' : TRState, st'.initiator = st₀.initiator ∧
            ((x.run tr).2.val.at? j : Option TRStEntry) = some ⟨⟨me, st'⟩⟩ :=
      fun hok' h => h _ hok'
    obtain ⟨j, hj1, hj2, st', hinit, hat_j⟩ := hsc_apply hrest_ok <|
      storesChildOf_bind_right _ fun _ =>
      storesChildOf_bind_right _ fun _ =>
      storesChildOf_bind_right _ fun _ =>
      storesChildOf_bind_right _ fun _ =>
      storesChildOf_bind_right _ fun _ =>
      storesChildOf_bind_right _ fun _ =>
        storesChildOf_bind_left _
          (storesChildOf_logMessageKeyAndStore me _ _ _ _ _ _ _ rfl)
    have hpure_val :
        ((Move.act (.encrypt me stateIdx coinsLen pqIdx wrap)).run tr₀).2.val =
        ((TripleRatchet.messageEncrypt me stateIdx coinsLen pqIdx).run tr₀).2.val := by
      change ((TripleRatchet.messageEncrypt me stateIdx coinsLen pqIdx >>=
        fun _ => pure ()).run tr₀).2.val = _
      rw [hval, DY.Traceful.run_pure]
    refine ⟨st₀, j, st', hat_k, hj1, ?_, hinit, ?_⟩
    · change j < ((Move.act (.encrypt me stateIdx coinsLen pqIdx wrap)).run tr₀).2.val.length
      rw [hpure_val]; unfold TripleRatchet.messageEncrypt; rw [hrest_val]; exact hj2
    · change (((Move.act (.encrypt me stateIdx coinsLen pqIdx wrap)).run tr₀).2.val.at? j :
        Option TRStEntry) = _
      rw [hpure_val]; unfold TripleRatchet.messageEncrypt; rw [hrest_val]; exact hat_j
  | decrypt me stateIdx msgIdx pqIdx spqrMsgIdx wrapped =>
    simp only [Move.stateLoad?, Option.some.injEq, Prod.mk.injEq] at hmi
    rcases hmi with ⟨rfl, rfl, -⟩
    obtain ⟨_, hdec, _, hval⟩ :=
      sf_run_bind_some_decomp
        (TripleRatchet.messageDecrypt me stateIdx msgIdx pqIdx spqrMsgIdx)
        (fun _ => pure ()) tr₀ hok
    have hdec_ok :
        ((TripleRatchet.messageDecrypt me stateIdx msgIdx pqIdx spqrMsgIdx).run tr₀).1.isSome = true := by
      rw [hdec]; rfl
    simp (config := { zeta := false, beta := false, eta := false, proj := false, iota := false, failIfUnchanged := false }) only [DY.Libsignal.TripleRatchet.messageDecrypt_eq_inline] at hdec_ok
    obtain ⟨st₀, hget, hrest_ok, hrest_val⟩ := sf_run_bind_some_decomp _ _ tr₀ hdec_ok
    obtain ⟨hat_k, hget_val⟩ := getLocalState_some_at? hget
    rw [hget_val] at hrest_ok hrest_val
    obtain ⟨msg, _, hrest2_ok, hrest2_val⟩ := sf_run_bind_some_decomp _ _ tr₀ hrest_ok
    obtain ⟨⟨st₁, c, ratcheted⟩, hens, hrest3_ok, hrest3_val⟩ :=
      sf_run_bind_some_decomp (TripleRatchet.ensureReceiverChain st₀ msg.ratchetKey) _ _ hrest2_ok
    have hinit₁ : st₁.initiator = st₀.initiator := ensureReceiverChain_initiator_eq hens
    have hsc_apply : ∀ {α : Type} {x : Traceful α} {tr : ExecTrace},
        (x.run tr).1.isSome = true → StoresChildOf me st₀.initiator x →
        ∃ j : Nat, tr.length ≤ j ∧ j < (x.run tr).2.val.length ∧
          ∃ st' : TRState, st'.initiator = st₀.initiator ∧
            ((x.run tr).2.val.at? j : Option TRStEntry) = some ⟨⟨me, st'⟩⟩ :=
      fun hok' h => h _ hok'
    obtain ⟨j, hj1, hj2, st', hinit, hat_j⟩ := hsc_apply hrest3_ok (by
      dsimp only
      rcases TripleRatchet.consumeMessageKey c msg.counter with _ | ⟨seed, c'⟩
      · intro tr hfail; rw [DY.Traceful.run_failure] at hfail; cases hfail
      · rcases DY.Spqr.spqrRecv st₁.spqr msg.pqRatchet spqrMsgIdx with _ | ⟨spqr', key⟩
        · intro tr hfail; rw [DY.Traceful.run_failure] at hfail; cases hfail
        · refine
            storesChildOf_bind_right _ fun _ =>
            storesChildOf_bind_right _ fun _ =>
            storesChildOf_bind_right _ fun _ => ?_
          split
          · exact
              storesChildOf_bind_right _ fun _ =>
              storesChildOf_bind_right _ fun _ =>
              storesChildOf_bind_right _ fun _ =>
              storesChildOf_bind_right _ fun _ =>
                storesChildOf_logMessageKeyAndStore me _ _ _ _ _ _ _ hinit₁
          · exact
              storesChildOf_bind_right _ fun _ =>
              storesChildOf_bind_right _ fun _ =>
                storesChildOf_logMessageKeyAndStore me _ _ _ _ _ _ _ hinit₁)
    let tr₂ := ((TripleRatchet.receiveSignalMsg msgIdx).run tr₀).2.val
    let tr₃ := ((TripleRatchet.ensureReceiverChain st₀ msg.ratchetKey).run tr₂).2.val
    have hle02 : tr₀.length ≤ tr₂.length :=
      Trace.length_le _ _ ((TripleRatchet.receiveSignalMsg msgIdx).run tr₀).2.property
    have hle23 : tr₂.length ≤ tr₃.length :=
      Trace.length_le _ _ ((TripleRatchet.ensureReceiverChain st₀ msg.ratchetKey).run tr₂).2.property
    have hpure_val :
        ((Move.act (.decrypt me stateIdx msgIdx pqIdx spqrMsgIdx wrapped)).run tr₀).2.val =
        ((TripleRatchet.messageDecrypt me stateIdx msgIdx pqIdx spqrMsgIdx).run tr₀).2.val := by
      change ((TripleRatchet.messageDecrypt me stateIdx msgIdx pqIdx spqrMsgIdx >>=
        fun _ => pure ()).run tr₀).2.val = _
      rw [hval, DY.Traceful.run_pure]
    refine ⟨st₀, j, st', hat_k, Nat.le_trans hle02 (Nat.le_trans hle23 hj1), ?_, hinit, ?_⟩
    · change j < ((Move.act (.decrypt me stateIdx msgIdx pqIdx spqrMsgIdx wrapped)).run tr₀).2.val.length
      rw [hpure_val]; simp (config := { zeta := false, beta := false, eta := false, proj := false, iota := false, failIfUnchanged := false }) only [DY.Libsignal.TripleRatchet.messageDecrypt_eq_inline]
      rw [hrest_val, hrest2_val, hrest3_val]; exact hj2
    · change (((Move.act (.decrypt me stateIdx msgIdx pqIdx spqrMsgIdx wrapped)).run tr₀).2.val.at? j :
        Option TRStEntry) = _
      rw [hpure_val]; simp (config := { zeta := false, beta := false, eta := false, proj := false, iota := false, failIfUnchanged := false }) only [DY.Libsignal.TripleRatchet.messageDecrypt_eq_inline]
      rw [hrest_val, hrest2_val, hrest3_val]; exact hat_j
  | decryptSkipped me stateIdx msgIdx skIdx pqIdx spqrMsgIdx wrapped =>
    simp only [Move.stateLoad?, Option.some.injEq, Prod.mk.injEq] at hmi
    rcases hmi with ⟨rfl, rfl, -⟩
    obtain ⟨_, hdec, _, hval⟩ :=
      sf_run_bind_some_decomp
        (TripleRatchet.messageDecryptSkipped me stateIdx msgIdx skIdx pqIdx spqrMsgIdx)
        (fun _ => pure ()) tr₀ hok
    have hdec_ok :
        ((TripleRatchet.messageDecryptSkipped me stateIdx msgIdx skIdx pqIdx spqrMsgIdx).run tr₀).1.isSome = true := by
      rw [hdec]; rfl
    unfold TripleRatchet.messageDecryptSkipped at hdec_ok
    obtain ⟨st₀, hget, hrest_ok, hrest_val⟩ := sf_run_bind_some_decomp _ _ tr₀ hdec_ok
    obtain ⟨hat_k, hget_val⟩ := getLocalState_some_at? hget
    rw [hget_val] at hrest_ok hrest_val
    obtain ⟨msg, _, hrest2_ok, hrest2_val⟩ := sf_run_bind_some_decomp _ _ tr₀ hrest_ok
    obtain ⟨e, _, hrest3_ok, hrest3_val⟩ := sf_run_bind_some_decomp _ _ _ hrest2_ok
    have hsc_apply : ∀ {α : Type} {x : Traceful α} {tr : ExecTrace},
        (x.run tr).1.isSome = true → StoresChildOf me st₀.initiator x →
        ∃ j : Nat, tr.length ≤ j ∧ j < (x.run tr).2.val.length ∧
          ∃ st' : TRState, st'.initiator = st₀.initiator ∧
            ((x.run tr).2.val.at? j : Option TRStEntry) = some ⟨⟨me, st'⟩⟩ :=
      fun hok' h => h _ hok'
    obtain ⟨j, hj1, hj2, st', hinit, hat_j⟩ := hsc_apply hrest3_ok (by
      rcases e.ev with _ | _ | _ | _ | _ | _ | ⟨s, pk, n, seed, rIdx, srcIdx⟩ | _ | _ | _ | _
      all_goals try (intro tr hfail; rw [DY.Traceful.run_failure] at hfail; cases hfail)
      exact
        storesChildOf_bind_right _ fun _ =>
        storesChildOf_bind_right _ fun _ =>
        (by
          rcases DY.Spqr.spqrRecv st₀.spqr msg.pqRatchet spqrMsgIdx with _ | ⟨spqr', key⟩
          · intro tr hfail; rw [DY.Traceful.run_failure] at hfail; cases hfail
          · exact
              storesChildOf_bind_right _ fun _ =>
              storesChildOf_bind_right _ fun _ =>
              storesChildOf_bind_right _ fun _ =>
              storesChildOf_bind_right _ fun _ =>
              storesChildOf_bind_right _ fun _ =>
                storesChildOf_logMessageKeyAndStore me _ _ _ _ _ _ _ rfl))
    let tr₂ := ((TripleRatchet.receiveSignalMsg msgIdx).run tr₀).2.val
    let tr₃ := ((DY.getEntry skIdx : Traceful (ProtocolEvent.ExecEntryT TREvent)).run tr₂).2.val
    have hle02 : tr₀.length ≤ tr₂.length :=
      Trace.length_le _ _ ((TripleRatchet.receiveSignalMsg msgIdx).run tr₀).2.property
    have hle23 : tr₂.length ≤ tr₃.length :=
      Trace.length_le _ _
        ((DY.getEntry skIdx : Traceful (ProtocolEvent.ExecEntryT TREvent)).run tr₂).2.property
    have hpure_val :
        ((Move.act (.decryptSkipped me stateIdx msgIdx skIdx pqIdx spqrMsgIdx wrapped)).run tr₀).2.val =
        ((TripleRatchet.messageDecryptSkipped me stateIdx msgIdx skIdx pqIdx spqrMsgIdx).run tr₀).2.val := by
      change ((TripleRatchet.messageDecryptSkipped me stateIdx msgIdx skIdx pqIdx spqrMsgIdx >>=
        fun _ => pure ()).run tr₀).2.val = _
      rw [hval, DY.Traceful.run_pure]
    refine ⟨st₀, j, st', hat_k, Nat.le_trans hle02 (Nat.le_trans hle23 hj1), ?_, hinit, ?_⟩
    · change j < ((Move.act (.decryptSkipped me stateIdx msgIdx skIdx pqIdx spqrMsgIdx wrapped)).run tr₀).2.val.length
      rw [hpure_val]; unfold TripleRatchet.messageDecryptSkipped
      rw [hrest_val, hrest2_val, hrest3_val]; exact hj2
    · change (((Move.act (.decryptSkipped me stateIdx msgIdx skIdx pqIdx spqrMsgIdx wrapped)).run tr₀).2.val.at? j :
        Option TRStEntry) = _
      rw [hpure_val]; unfold TripleRatchet.messageDecryptSkipped
      rw [hrest_val, hrest2_val, hrest3_val]; exact hat_j
  | _ => simp [Move.stateLoad?] at hmi

/-- Appending any move `m` whose loaded snapshot (if any) satisfies
`isCurrentSnapshot (runTraceMoves r ms) k = true` preserves `StateFaithful r`. -/
theorem stateFaithful_snoc_of_isCurrentSnapshot {r : ProtocolSetup} {ms : List Move} {m : Move}
    (hsf : StateFaithful r ms)
    (hcur : ∀ p k b, m.stateLoad? = some (p, k, b) →
      TripleRatchet.isCurrentSnapshot (runTraceMoves r ms) k = true) :
    StateFaithful r (ms ++ [m]) := by
  refine stateFaithful_snoc hsf fun i mi p k b hi hmi hok hm => ?_
  have hij : i < ms.length := (List.getElem?_eq_some_iff.mp hi).1
  have hsplit : ms = ms.take i ++ mi :: ms.drop (i + 1) := by
    have h1 := (List.take_append_drop i ms).symm
    obtain ⟨_, hget⟩ := List.getElem?_eq_some_iff.mp hi
    have hdrop : ms.drop i = mi :: ms.drop (i + 1) := by
      rw [← hget]
      exact List.drop_eq_getElem_cons hij
    rw [hdrop] at h1
    exact h1
  have hle : mi.next (runTraceMoves r (ms.take i)) ≤ runTraceMoves r ms := by
    unfold runTraceMoves
    conv_rhs => rw [hsplit, ← List.cons_append, sf_runMoves_append_fst]
    exact sf_runMoves_le (ms.drop (i + 1)) (mi.next (runTraceMoves r (ms.take i)))
  have hfalse := not_isCurrentSnapshot_of_stateLoad_true_ok hmi hok hle
  rw [hcur p k b hm] at hfalse
  cases hfalse

end Symbolic.Swarm.CREF
