/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Symbolic.Proofs.Swarm.CREF.Cli.RetiredTraceExplanation
import DY.Bytes.Basic
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
public import ProofLib.Lemmas
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import VCVio.Prelude.Core
import Symbolic.DYBridge.DY.Bytes.Basic
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
# Receiver Trials, MAC Forgery Bridges, and Wire-Step Faithfulness

Proves membership and decomposition lemmas for `whisperTrials` and `trialTerms`, routes
memo and cross-seed MAC collisions into `RecvCollision`, and establishes step and
monotonicity lemmas for `PeerFaithful`, `StateFaithful`, `RoleFaithful`, `PathFaithful`,
`OutcomeFaithful`, and `ReadFaithful` across wire and environment moves.
-/

@[expose] public section

set_option autoImplicit false

namespace Symbolic.Swarm.CREF.Stage1Wire

open DY DY.Comparse
open CryptoProofLib.Refinement (ExternInterpretation)
open DY.Libsignal
open DY.Libsignal.HwEvents (MachineEvent)
open DY.Libsignal.Composed
open DY.Libsignal.Composed.Refinement
open DY.Libsignal.TripleRatchet

/-! ## Receiver-Trial Decomposition -/

@[simp] theorem sinfo_me (st : DRState) (p : Participant) : (st.sessionInfo p).me = p := rfl

/-- `TrialCtx` built for a receive chain `c` of state `st` at `counter` in `whisperTrials`. -/
def chainTrialCtx (st : TRState) (own : List DY.Bytes) (c : RecvChain) (counter : UInt32) :
    TrialCtx :=
  match consumeMessageKey c counter with
  | none =>
    { peerIk := st.peerIk, myIk := st.myIk, extra := [c.chainKey],
      ownSalts := [], seed? := none }
  | some (seed, c') =>
    { peerIk := st.peerIk, myIk := st.myIk,
      extra := [c.chainKey, c'.chainKey] ++ skippedSeeds c counter,
      ownSalts := own, seed? := some seed }

/-- `TrialCtx` built for a cached `SkippedKeyStored` seed in `whisperTrials`. -/
def skippedTrialCtx (st : TRState) (own : List DY.Bytes) (s : SessionInfo) (seed : DY.Bytes) :
    TrialCtx :=
  { peerIk := st.peerIk, myIk := st.myIk, extra := [],
    ownSalts := if st.sessionInfo s.me = s then own else [],
    seed? := some seed }

/-- Every stored receive chain `c ∈ st.toDRState.recv` whose `ratchetKey` matches `msg.ratchetKey`
in bytes (`gamma interpretation S g c.ratchetKey = gamma interpretation S g msg.ratchetKey`)
contributes `chainTrialCtx` to `whisperTrials`. -/
theorem mem_whisperTrials_of_recv_chain {interpretation : ExternInterpretation} {r : ProtocolSetup}
    {S : OpaqueSymbolSemantics} {g : Ghost} {tr : ExecTrace} {msg : TRSignalMsg} {st : TRState} {c : RecvChain}
    (hver : msg.version = messageVersion)
    (hst : st ∈ availableStates r tr)
    (hc : c ∈ st.toDRState.recv)
    (hγ : gamma interpretation S g c.ratchetKey = gamma interpretation S g msg.ratchetKey) :
    chainTrialCtx st (ownKeys r tr st msg) c msg.counter ∈
      whisperTrials interpretation r S g tr msg := by
  simp only [whisperTrials, hver, ↓reduceIte, List.mem_flatMap]
  refine ⟨st, hst, List.mem_append_left _ ?_⟩
  rw [List.mem_map]
  refine ⟨c, List.mem_append_left _ ?_, rfl⟩
  rw [List.mem_filter]
  exact ⟨hc, decide_eq_true hγ⟩

/-- A fresh DH-ratchet chain (`recvChainFor st.toDRState msg.ratchetKey = some (c, true)`)
contributes `chainTrialCtx` to `whisperTrials`. -/
theorem mem_whisperTrials_of_recvChainFor_fresh {interpretation : ExternInterpretation}
    {r : ProtocolSetup} {S : OpaqueSymbolSemantics} {g : Ghost} {tr : ExecTrace} {msg : TRSignalMsg}
    {st : TRState} {c : RecvChain}
    (hver : msg.version = messageVersion)
    (hst : st ∈ availableStates r tr)
    (hrc : recvChainFor st.toDRState msg.ratchetKey = some (c, true)) :
    chainTrialCtx st (ownKeys r tr st msg) c msg.counter ∈
      whisperTrials interpretation r S g tr msg := by
  simp only [whisperTrials, hver, ↓reduceIte, List.mem_flatMap]
  refine ⟨st, hst, List.mem_append_left _ ?_⟩
  rw [List.mem_map]
  refine ⟨c, List.mem_append_right _ ?_, rfl⟩
  unfold recvChainFor at hrc
  unfold DY.Libsignal.TripleRatchet.recvHalfStep
  cases hfind : findRecvChain st.recv msg.ratchetKey with
  | some _ => simp [hfind] at hrc
  | none =>
    cases hlo : DY.Libsignal.TripleRatchet.x25519LowOrder msg.ratchetKey with
    | true => simp [hfind, hlo] at hrc
    | false =>
      simp only [hfind, hlo, Bool.false_eq_true, ↓reduceIte, Option.some.injEq,
        Prod.mk.injEq] at hrc ⊢
      rcases hrc with ⟨rfl, -⟩
      exact List.mem_singleton.mpr rfl

/-- Every `TREvent.SkippedKeyStored` on `tr` whose `pk` matches `msg.ratchetKey` in bytes and whose
counter equals `msg.counter` contributes `skippedTrialCtx` to `whisperTrials`. -/
theorem mem_whisperTrials_of_skippedKeyStored {interpretation : ExternInterpretation}
    {r : ProtocolSetup} {S : OpaqueSymbolSemantics} {g : Ghost} {tr : ExecTrace} {msg : TRSignalMsg}
    {st : TRState} {i : Nat} {s : SessionInfo} {pk seed : DY.Bytes} {n : UInt32}
    {rIdx srcIdx : Nat}
    (hver : msg.version = messageVersion)
    (hst : st ∈ availableStates r tr)
    (hfind : (findRecvChain st.toDRState.recv pk).isSome = true)
    (hi : i < tr.length)
    (hev : tr.getEventAt TREvent i = some (.SkippedKeyStored s pk n seed rIdx srcIdx))
    (hγ : gamma interpretation S g pk = gamma interpretation S g msg.ratchetKey)
    (hn : n = msg.counter) :
    skippedTrialCtx st (ownKeys r tr st msg) s seed ∈
      whisperTrials interpretation r S g tr msg := by
  simp only [whisperTrials, hver, ↓reduceIte, List.mem_flatMap]
  refine ⟨st, hst, List.mem_append_right _ ?_⟩
  rw [List.mem_filterMap]
  refine ⟨i, List.mem_range.mpr hi, ?_⟩
  simp [hev, hfind, hγ, hn, skippedTrialCtx]

/-- Every term in `ctx.extra` belongs to `trialTerms salts msg ctx`. -/
theorem mem_trialTerms_of_mem_extra (salts : List DY.Bytes) (msg : TRSignalMsg)
    {ctx : TrialCtx} {x : DY.Bytes} (hx : x ∈ ctx.extra) :
    x ∈ trialTerms salts msg ctx :=
  List.mem_append_left _ hx

/-- Per-salt `cipherKey`, `macKey`, `iv`, and `computeMac` belong to `trialTerms salts msg ctx`
whenever `ctx.seed? = some seed` and `salt ∈ salts`. -/
theorem keyTerms_sub_trialTerms {salts : List DY.Bytes} {msg : TRSignalMsg}
    {ctx : TrialCtx} {seed salt : DY.Bytes}
    (hseed : ctx.seed? = some seed) (hsalt : salt ∈ salts) :
    let mk := trMsgKeys salt seed
    mk.cipherKey ∈ trialTerms salts msg ctx ∧
    mk.macKey ∈ trialTerms salts msg ctx ∧
    mk.iv ∈ trialTerms salts msg ctx ∧
    computeMac mk.macKey ctx.peerIk ctx.myIk msg.wire ∈ trialTerms salts msg ctx := by
  dsimp only
  let mk := trMsgKeys salt seed
  have hsub : ∀ (u : DY.Bytes),
      u ∈ [mk.cipherKey, mk.macKey, mk.iv, computeMac mk.macKey ctx.peerIk ctx.myIk msg.wire] →
      u ∈ trialTerms salts msg ctx := by
    intro u hu
    unfold trialTerms
    rw [hseed]
    exact List.mem_append_right _ (List.mem_flatMap.mpr ⟨salt, hsalt, List.mem_append_left _ hu⟩)
  exact ⟨hsub mk.cipherKey (by simp), hsub mk.macKey (by simp),
    hsub mk.iv (by simp), hsub (computeMac mk.macKey ctx.peerIk ctx.myIk msg.wire) (by simp)⟩

/-- When `msg.ratchetKey` is not in `st.toDRState.recv` and is not low-order,
`(createChain st.rk msg.ratchetKey st.dhs).2` belongs to the expanded `whisperTrials` terms. -/
theorem createChain_snd_mem_whisperTrials_terms (interpretation : ExternInterpretation)
    (r : ProtocolSetup) (S : OpaqueSymbolSemantics) (g : Ghost) (tr : ExecTrace) (salts : List DY.Bytes)
    (st : TRState) (msg : TRSignalMsg)
    (hver : msg.version = messageVersion)
    (hst : st ∈ availableStates r tr)
    (hfind : findRecvChain st.toDRState.recv msg.ratchetKey = none)
    (hlow : x25519LowOrder msg.ratchetKey = false) :
    (createChain st.rk msg.ratchetKey st.dhs).2 ∈
      (whisperTrials interpretation r S g tr msg).flatMap (trialTerms salts msg) := by
  let c : RecvChain :=
    { ratchetKey := msg.ratchetKey,
      chainKey := (createChain st.rk msg.ratchetKey st.dhs).2,
      index := 0, rIdx := st.rIdx + 2 }
  have hrc : recvChainFor st.toDRState msg.ratchetKey = some (c, true) := by
    simp [recvChainFor, hfind, hlow, c]
  have hmem_ctx := mem_whisperTrials_of_recvChainFor_fresh
    (interpretation := interpretation) (S := S) (g := g) hver hst hrc
  rw [List.mem_flatMap]
  refine ⟨chainTrialCtx st (ownKeys r tr st msg) c msg.counter, hmem_ctx,
    mem_trialTerms_of_mem_extra salts msg ?_⟩
  unfold chainTrialCtx
  split <;> simp [c]

/-! ## Collision and Forgery Bridges -/

theorem memoCollisionOn_mono_newTerms {interpretation : ExternInterpretation} {r : ProtocolSetup}
    {S : OpaqueSymbolSemantics} {g : Ghost} {known : DY.Bytes → Prop} {tr : ExecTrace} {vis : List VisEntry}
    {ns₁ ns₂ newPts : List DY.Bytes} (hsub : ∀ t ∈ ns₁, t ∈ ns₂)
    (hcol : MemoCollisionOn interpretation r S g known tr vis ns₁ newPts) :
    MemoCollisionOn interpretation r S g known tr vis ns₂ newPts := by
  obtain ⟨x₁, hx₁, x₂, hx₂, hne, hinj, hpt₁, hpt₂, hbytes⟩ := hcol
  have hnew_sub : ∀ x ∈ ns₁.flatMap (fun t => (gamma' interpretation S g t).memo),
      x ∈ ns₂.flatMap (fun t => (gamma' interpretation S g t).memo) := by
    intro x hx
    obtain ⟨t, ht, hxm⟩ := List.mem_flatMap.mp hx
    exact List.mem_flatMap.mpr ⟨t, hsub t ht, hxm⟩
  refine ⟨x₁, hnew_sub x₁ hx₁, x₂, ?_, hne, hinj, hpt₁, hpt₂, hbytes⟩
  rcases List.mem_append.mp hx₂ with hpref | hnew
  · exact List.mem_append_left _ hpref
  · exact List.mem_append_right _ (hnew_sub x₂ hnew)

/-- A cross-seed syntactic `computeMac` collision injects into the right branch of
`MacTagForgeryOrCollision`. -/
theorem ownSaltMacCollision_of_cross_seed_term {interpretation : ExternInterpretation} {S : OpaqueSymbolSemantics}
    {g : Ghost} {known : DY.Bytes → Prop} {honest : List DY.Bytes} {msg : TRSignalMsg}
    {ctxs : List TrialCtx} {ctx ctx₀ : TrialCtx}
    {seed k seed₀ peerIk₀ myIk₀ salt₀ w : DY.Bytes}
    (hctx : ctx ∈ ctxs) (hseed : ctx.seed? = some seed) (hk : k ∈ ctx.ownSalts)
    (hmac : gamma interpretation S g
      (computeMac (trMsgKeys k seed).macKey ctx.peerIk ctx.myIk msg.wire) =
      gamma interpretation S g msg.mac)
    (hctx₀ : ctx₀ ∈ ctxs) (hseed₀ : ctx₀.seed? = some seed₀)
    (hne : gamma interpretation S g seed ≠ gamma interpretation S g seed₀)
    (heq_mac : msg.mac = computeMac (trMsgKeys salt₀ seed₀).macKey peerIk₀ myIk₀ w)
    (heq_wire : gamma interpretation S g w = gamma interpretation S g msg.wire) :
    MacTagForgeryOrCollision interpretation S g known honest msg ctxs :=
  .inr ⟨ctx, hctx, seed, hseed, k, hk, hmac,
    ctx₀, hctx₀, seed₀, hseed₀, hne, .inr ⟨peerIk₀, myIk₀, salt₀, w, heq_mac, heq_wire⟩⟩

/-- `MemoCollisionOn` on any subset of `t :: ctxs.flatMap (trialTerms salts msg)` yields
`RecvCollision` when `parseTrSignalMsg t = some msg`. -/
theorem recvCollision_of_memoCollisionOn_sub {interpretation : ExternInterpretation} {r : ProtocolSetup}
    {S : OpaqueSymbolSemantics} {g : Ghost} {ms : List Move} {t : DY.Bytes} {msg : TRSignalMsg}
    {ns : List DY.Bytes}
    (hparse : parseTrSignalMsg t = some msg)
    (hsub : ∀ u ∈ ns, u ∈ t :: (whisperTrials interpretation r S g (runTraceMoves r ms) msg).flatMap
      (trialTerms (honestSalts r ms) msg))
    (hcol : MemoCollisionOn interpretation r S g (fun u => u.AttackerKnows (runTraceMoves r ms))
      (runTraceMoves r ms) (runVis r ms) ns []) :
    RecvCollision interpretation r S g ms t := by
  unfold RecvCollision
  rw [hparse]
  exact .inl (memoCollisionOn_mono_newTerms hsub hcol)

/-- `MacTagForgeryOrCollision` on `whisperTrials` yields `RecvCollision` when
`parseTrSignalMsg t = some msg`. -/
theorem recvCollision_of_ownSaltMacCollision {interpretation : ExternInterpretation} {r : ProtocolSetup}
    {S : OpaqueSymbolSemantics} {g : Ghost} {ms : List Move} {t : DY.Bytes} {msg : TRSignalMsg}
    (hparse : parseTrSignalMsg t = some msg)
    (hown : MacTagForgeryOrCollision interpretation S g (fun u => u.AttackerKnows (runTraceMoves r ms))
      (honestSalts r ms) msg (whisperTrials interpretation r S g (runTraceMoves r ms) msg)) :
    RecvCollision interpretation r S g ms t := by
  unfold RecvCollision
  rw [hparse]
  exact .inr hown

/-! ## Peer and Session-State Faithfulness -/

theorem peerFaithful_append {r : ProtocolSetup} {ms₁ ms₂ : List Move} :
    PeerFaithful r (ms₁ ++ ms₂) ↔ PeerFaithful r ms₁ ∧ PeerFaithful r ms₂ := by
  simp only [PeerFaithful, List.mem_append]
  exact ⟨fun h => ⟨fun m hm => h m (.inl hm), fun m hm => h m (.inr hm)⟩,
    fun ⟨h₁, h₂⟩ m hm => hm.elim (h₁ m) (h₂ m)⟩

/-- Every move other than `aliceStart` and `bobStart` satisfies `Move.MatchesSetupPeer r`. -/
theorem peerOk_of_not_start (r : ProtocolSetup) {m : Move}
    (ha : ∀ a b idIdx regB h shown, m ≠ .aliceStart a b idIdx regB h shown)
    (hb : ∀ b a kh regA mh pqIdx spqrIdx shown,
      m ≠ .bobStart b a kh regA mh pqIdx spqrIdx shown) :
    m.MatchesSetupPeer r := by
  cases m with
  | aliceStart a b idIdx regB h shown => exact False.elim (ha a b idIdx regB h shown rfl)
  | bobStart b a kh regA mh pqIdx spqrIdx shown =>
    exact False.elim (hb b a kh regA mh pqIdx spqrIdx shown rfl)
  | _ => trivial

/-- Appending any move with `m.stateLoad? = none` (`reject`, `attackerSend`, `expose*`,
`compromise*`, `aliceStart`, `bobStart`, `setup`) preserves `StateFaithful` unconditionally. -/
theorem stateFaithful_snoc_of_stateLoad_none {r : ProtocolSetup} {ms : List Move} {m : Move}
    (hsf : StateFaithful r ms) (hnone : m.stateLoad? = none) :
    StateFaithful r (ms ++ [m]) := by
  intro i j mi mj p k b hij hi hj hmi hok hmj
  by_cases hj_lt : j < ms.length
  · have hi_lt : i < ms.length := Nat.lt_trans hij hj_lt
    rw [List.getElem?_append_left hi_lt] at hi
    rw [List.getElem?_append_left hj_lt] at hj
    have htake : (ms ++ [m]).take i = ms.take i :=
      List.take_append_of_le_length (Nat.le_of_lt hi_lt)
    rw [htake] at hok
    exact hsf i j mi mj p k b hij hi hj hmi hok hmj
  · have hj_ge : ms.length ≤ j := Nat.le_of_not_lt hj_lt
    rw [List.getElem?_append_right hj_ge] at hj
    rcases Nat.eq_or_lt_of_le hj_ge with rfl | hj_gt
    · simp only [Nat.sub_self, List.getElem?_cons_zero, Option.some.injEq] at hj
      subst hj
      rw [hnone] at hmj
      cases hmj
    · obtain ⟨d, hd⟩ : ∃ d, j - ms.length = d + 1 := ⟨j - ms.length - 1, by omega⟩
      rw [hd, List.getElem?_cons_succ, List.getElem?_nil] at hj
      cases hj

private abbrev TRStEntry :=
  PersistentGlobalState.State.ExecEntryT (PersistentLocalState.LocalState TRState)

private theorem at?_eq_of_le_of_lt {E : Type} [ExecTraceTypes.Has E]
    {tr tr' : ExecTrace} (hle : tr ≤ tr') {i : Nat} (hi : i < tr.length) :
    (tr'.at? i : Option E) = (tr.at? i : Option E) := by
  have hi' : i < tr'.length := Nat.lt_of_lt_of_le hi (Trace.length_le _ _ hle)
  simp only [Trace.at?, hi, hi', ↓reduceDIte]
  rw [← Trace.at_le tr tr' i hi hle]

private theorem at?_le_some {E : Type} [ExecTraceTypes.Has E]
    {tr tr' : ExecTrace} (hle : tr ≤ tr') {i : Nat} {x : E}
    (hx : (tr.at? i : Option E) = some x) :
    (tr'.at? i : Option E) = some x := by
  have hi : i < tr.length := by
    have h := Trace.at?_eq_some_implies_length_le (EntryT := E) tr i
    rw [hx] at h
    exact h
  rw [at?_eq_of_le_of_lt hle hi]
  exact hx

private theorem runMoves_le (ms : List Move) (tr : ExecTrace) :
    tr ≤ (runMoves ms tr).1 := by
  induction ms generalizing tr with
  | nil => exact Trace.le_refl tr
  | cons m ms ih =>
    exact Trace.le_trans _ _ _ ((m.act.run tr).2.property) (ih (m.next tr))

private theorem runMoves_append_fst (ms₁ ms₂ : List Move) (tr : ExecTrace) :
    (runMoves (ms₁ ++ ms₂) tr).1 = (runMoves ms₂ (runMoves ms₁ tr).1).1 := by
  induction ms₁ generalizing tr with
  | nil => rfl
  | cons m ms₁ ih => exact ih (m.next tr)

private def StoresChildOf {α : Type} (p : Participant) (init : Bool) (x : Traceful α) : Prop :=
  ∀ tr : ExecTrace, (x.run tr).1.isSome = true →
    ∃ j : Nat, tr.length ≤ j ∧ j < (x.run tr).2.val.length ∧
      ∃ st' : TRState, st'.initiator = init ∧
        ((x.run tr).2.val.at? j : Option TRStEntry) = some ⟨⟨p, st'⟩⟩

private theorem run_bind_fst {α β : Type} (x : Traceful α) (f : α → Traceful β) (tr : ExecTrace) :
    ((x >>= f).run tr).1 =
      match (x.run tr).1 with
      | some a => ((f a).run (x.run tr).2.val).1
      | none => none := by
  rw [Traceful.run_bind]
  rcases x.run tr with ⟨_ | a, tr₁⟩
  · rfl
  · rcases (f a).run tr₁.val with ⟨_, _⟩; rfl

private theorem run_bind_snd {α β : Type} (x : Traceful α) (f : α → Traceful β) (tr : ExecTrace) :
    ((x >>= f).run tr).2.val =
      match (x.run tr).1 with
      | some a => ((f a).run (x.run tr).2.val).2.val
      | none => (x.run tr).2.val := by
  rw [Traceful.run_bind]
  rcases x.run tr with ⟨_ | a, tr₁⟩
  · rfl
  · rcases (f a).run tr₁.val with ⟨_, _⟩; rfl

private theorem run_bind_some_decomp {α β : Type} (x : Traceful α) (f : α → Traceful β)
    (tr : ExecTrace) (hok : ((x >>= f).run tr).1.isSome = true) :
    ∃ a, (x.run tr).1 = some a ∧
      ((f a).run (x.run tr).2.val).1.isSome = true ∧
      ((x >>= f).run tr).2.val = ((f a).run (x.run tr).2.val).2.val := by
  rw [run_bind_fst] at hok
  rcases hx : (x.run tr).1 with _ | a
  · rw [hx] at hok; cases hok
  · rw [hx] at hok
    exact ⟨a, rfl, hok, by rw [run_bind_snd, hx]⟩

private theorem storesChildOf_bind_right {α β : Type} {p : Participant} {init : Bool}
    (x : Traceful α) {f : α → Traceful β}
    (hf : ∀ a, StoresChildOf p init (f a)) :
    StoresChildOf p init (x >>= f) := by
  intro tr hok
  obtain ⟨a, _, hfok, hval⟩ := run_bind_some_decomp x f tr hok
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
  obtain ⟨a, hxa, _, hval⟩ := run_bind_some_decomp x f tr hok
  have hxok : (x.run tr).1.isSome = true := by rw [hxa]; rfl
  obtain ⟨j, hj1, hj2, st', hinit, hat⟩ := hx tr hxok
  have hle₂ : (x.run tr).2.val ≤ ((x >>= f).run tr).2.val := by
    rw [hval]
    exact ((f a).run (x.run tr).2.val).2.property
  exact ⟨j, hj1, Nat.lt_of_lt_of_le hj2 (Trace.length_le _ _ hle₂),
    st', hinit, at?_le_some hle₂ hat⟩

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

private theorem storesChildOf_logMessageKeyAndStore (p : Participant) (s : SessionInfo)
    (dir : KeyDir) (seed pqSalt : DY.Bytes) (n : UInt32) (rIdx parIdx : Nat)
    {init : Bool} {st' : TRState} (hinit : st'.initiator = init) :
    StoresChildOf p init
      (logMessageKeyAndStore p s dir seed pqSalt n rIdx parIdx st') := by
  unfold logMessageKeyAndStore
  exact storesChildOf_bind_right _ fun _ =>
    storesChildOf_storeLocalState p hinit

private theorem dhRatchetStep_initiator_eq {st₀ st₁ : TRState} {pk : DY.Bytes}
    {c₁ : RecvChain} {tr : ExecTrace}
    (h : ((dhRatchetStep st₀ pk).run tr).1 = some (st₁, c₁)) :
    st₁.initiator = st₀.initiator := by
  simp (config := { zeta := false, beta := false, eta := false, proj := false, iota := false, failIfUnchanged := false }) only [DY.Libsignal.TripleRatchet.dhRatchetStep_eq_guard] at h
  rw [run_bind_fst] at h
  rcases hg : ((«guard» (!x25519LowOrder pk) : Traceful Unit).run tr).1 with _ | u
  · rw [hg] at h; cases h
  · rw [hg, run_bind_fst] at h
    let tr₁ := ((«guard» (!x25519LowOrder pk) : Traceful Unit).run tr).2.val
    rcases hr : ((Random.genRand 32).run tr₁).1 with _ | dhs
    · rw [hr] at h; cases h
    · rw [hr] at h
      dsimp only at h
      rw [DY.Traceful.run_pure] at h
      injection h with hp
      injection hp with hst _
      rw [← hst]

private theorem ensureReceiverChain_initiator_eq {st₀ st : TRState} {pk : DY.Bytes}
    {c : RecvChain} {b : Bool} {tr : ExecTrace}
    (h : ((ensureReceiverChain st₀ pk).run tr).1 = some (st, c, b)) :
    st.initiator = st₀.initiator := by
  simp (config := { zeta := false, beta := false, eta := false, proj := false, iota := false, failIfUnchanged := false }) only [DY.Libsignal.TripleRatchet.ensureReceiverChain_eq_recvChainFor] at h
  rcases hrc : recvChainFor st₀.toDRState pk with _ | ⟨c₀, false | true⟩
  · rw [hrc, DY.Traceful.run_failure] at h
    cases h
  · rw [hrc, DY.Traceful.run_pure] at h
    injection h with hp
    injection hp with hst _
    exact congrArg (fun s : TRState => s.initiator) hst.symm
  · rw [hrc, run_bind_fst] at h
    rcases hdh : ((dhRatchetStep st₀ pk).run tr).1 with _ | ⟨st₁, c₁⟩
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
  rw [run_bind_fst] at h
  rw [run_bind_snd]
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
  rw [run_bind_fst] at h
  rw [run_bind_snd]
  rcases hgs : ((PersistentGlobalState.getGlobalState k :
      Traceful (PersistentLocalState.LocalState TRState)).run tr).1 with _ | ⟨p', st'⟩
  · rw [hgs] at h; cases h
  · obtain ⟨hat, hval⟩ := getGlobalState_some_at? hgs
    rw [hgs] at h
    dsimp only at h ⊢
    rw [hval, run_bind_fst] at h
    rw [hval, run_bind_snd]
    by_cases hp : p' = p
    · subst hp
      have hg1 : ((«guard» (p' = p') : Traceful Unit).run tr).1 = some () := by
        simp [«guard», DY.Traceful.run_pure]
      have hg2 : ((«guard» (p' = p') : Traceful Unit).run tr).2.val = tr := by
        simp [«guard», DY.Traceful.run_pure]
      rw [hg1] at h ⊢
      dsimp only at h ⊢
      rw [DY.Traceful.run_pure] at h ⊢
      injection h with hst
      subst hst
      exact ⟨hat, hg2⟩
    · have hg1 : ((«guard» (p' = p) : Traceful Unit).run tr).1 = none := by
        simp [«guard», hp, DY.Traceful.run_failure]
      rw [hg1] at h
      cases h

private theorem not_isCurrentSnapshot_of_stateLoad_true_ok {mi : Move} {p : Participant}
    {k : Nat} {tr₀ tr₁ : ExecTrace}
    (hmi : mi.stateLoad? = some (p, k, true))
    (hok : (mi.act.run tr₀).1.isSome = true)
    (hle : mi.next tr₀ ≤ tr₁) :
    isCurrentSnapshot tr₁ k = false := by
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
      at?_le_some (Trace.le_trans _ _ _ (mi.act.run tr₀).2.property hle) hat_k₀
    have hat_j₁ : (tr₁.at? j : Option TRStEntry) = some ⟨⟨p, st'⟩⟩ :=
      at?_le_some hle hat_j₀
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
      run_bind_some_decomp
        (messageEncrypt me stateIdx coinsLen pqIdx) (fun _ => pure ()) tr₀ hok
    have henc_ok :
        ((messageEncrypt me stateIdx coinsLen pqIdx).run tr₀).1.isSome = true := by
      rw [henc]; rfl
    unfold messageEncrypt at henc_ok
    obtain ⟨st₀, hget, hrest_ok, hrest_val⟩ := run_bind_some_decomp _ _ tr₀ henc_ok
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
        ((messageEncrypt me stateIdx coinsLen pqIdx).run tr₀).2.val := by
      change ((messageEncrypt me stateIdx coinsLen pqIdx >>= fun _ => pure ()).run tr₀).2.val = _
      rw [hval, DY.Traceful.run_pure]
    refine ⟨st₀, j, st', hat_k, hj1, ?_, hinit, ?_⟩
    · change j < ((Move.act (.encrypt me stateIdx coinsLen pqIdx wrap)).run tr₀).2.val.length
      rw [hpure_val]
      unfold messageEncrypt; rw [hrest_val]; exact hj2
    · change (((Move.act (.encrypt me stateIdx coinsLen pqIdx wrap)).run tr₀).2.val.at? j :
        Option TRStEntry) = _
      rw [hpure_val]
      unfold messageEncrypt; rw [hrest_val]; exact hat_j
  | decrypt me stateIdx msgIdx pqIdx spqrMsgIdx wrapped =>
    simp only [Move.stateLoad?, Option.some.injEq, Prod.mk.injEq] at hmi
    rcases hmi with ⟨rfl, rfl, -⟩
    obtain ⟨_, hdec, _, hval⟩ :=
      run_bind_some_decomp
        (messageDecrypt me stateIdx msgIdx pqIdx spqrMsgIdx) (fun _ => pure ()) tr₀ hok
    have hdec_ok :
        ((messageDecrypt me stateIdx msgIdx pqIdx spqrMsgIdx).run tr₀).1.isSome = true := by
      rw [hdec]; rfl
    simp (config := { zeta := false, beta := false, eta := false, proj := false, iota := false, failIfUnchanged := false }) only [DY.Libsignal.TripleRatchet.messageDecrypt_eq_inline] at hdec_ok
    obtain ⟨st₀, hget, hrest_ok, hrest_val⟩ := run_bind_some_decomp _ _ tr₀ hdec_ok
    obtain ⟨hat_k, hget_val⟩ := getLocalState_some_at? hget
    rw [hget_val] at hrest_ok hrest_val
    obtain ⟨msg, _, hrest2_ok, hrest2_val⟩ := run_bind_some_decomp _ _ tr₀ hrest_ok
    obtain ⟨⟨st₁, c, ratcheted⟩, hens, hrest3_ok, hrest3_val⟩ :=
      run_bind_some_decomp (ensureReceiverChain st₀ msg.ratchetKey) _ _ hrest2_ok
    have hinit₁ : st₁.initiator = st₀.initiator := ensureReceiverChain_initiator_eq hens
    have hsc_apply : ∀ {α : Type} {x : Traceful α} {tr : ExecTrace},
        (x.run tr).1.isSome = true → StoresChildOf me st₀.initiator x →
        ∃ j : Nat, tr.length ≤ j ∧ j < (x.run tr).2.val.length ∧
          ∃ st' : TRState, st'.initiator = st₀.initiator ∧
            ((x.run tr).2.val.at? j : Option TRStEntry) = some ⟨⟨me, st'⟩⟩ :=
      fun hok' h => h _ hok'
    obtain ⟨j, hj1, hj2, st', hinit, hat_j⟩ := hsc_apply hrest3_ok (by
      dsimp only
      rcases consumeMessageKey c msg.counter with _ | ⟨seed, c'⟩
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
    let tr₂ := ((receiveSignalMsg msgIdx).run tr₀).2.val
    let tr₃ := ((ensureReceiverChain st₀ msg.ratchetKey).run tr₂).2.val
    have hle02 : tr₀.length ≤ tr₂.length :=
      Trace.length_le _ _ ((receiveSignalMsg msgIdx).run tr₀).2.property
    have hle23 : tr₂.length ≤ tr₃.length :=
      Trace.length_le _ _ ((ensureReceiverChain st₀ msg.ratchetKey).run tr₂).2.property
    have hpure_val :
        ((Move.act (.decrypt me stateIdx msgIdx pqIdx spqrMsgIdx wrapped)).run tr₀).2.val =
        ((messageDecrypt me stateIdx msgIdx pqIdx spqrMsgIdx).run tr₀).2.val := by
      change ((messageDecrypt me stateIdx msgIdx pqIdx spqrMsgIdx >>= fun _ => pure ()).run tr₀).2.val = _
      rw [hval, DY.Traceful.run_pure]
    refine ⟨st₀, j, st', hat_k, Nat.le_trans hle02 (Nat.le_trans hle23 hj1), ?_, hinit, ?_⟩
    · change j < ((Move.act (.decrypt me stateIdx msgIdx pqIdx spqrMsgIdx wrapped)).run tr₀).2.val.length
      rw [hpure_val]
      simp (config := { zeta := false, beta := false, eta := false, proj := false, iota := false, failIfUnchanged := false }) only [DY.Libsignal.TripleRatchet.messageDecrypt_eq_inline]; rw [hrest_val, hrest2_val, hrest3_val]; exact hj2
    · change (((Move.act (.decrypt me stateIdx msgIdx pqIdx spqrMsgIdx wrapped)).run tr₀).2.val.at? j :
        Option TRStEntry) = _
      rw [hpure_val]
      simp (config := { zeta := false, beta := false, eta := false, proj := false, iota := false, failIfUnchanged := false }) only [DY.Libsignal.TripleRatchet.messageDecrypt_eq_inline]; rw [hrest_val, hrest2_val, hrest3_val]; exact hat_j
  | decryptSkipped me stateIdx msgIdx skIdx pqIdx spqrMsgIdx wrapped =>
    simp only [Move.stateLoad?, Option.some.injEq, Prod.mk.injEq] at hmi
    rcases hmi with ⟨rfl, rfl, -⟩
    obtain ⟨_, hdec, _, hval⟩ :=
      run_bind_some_decomp
        (messageDecryptSkipped me stateIdx msgIdx skIdx pqIdx spqrMsgIdx)
        (fun _ => pure ()) tr₀ hok
    have hdec_ok :
        ((messageDecryptSkipped me stateIdx msgIdx skIdx pqIdx spqrMsgIdx).run tr₀).1.isSome = true := by
      rw [hdec]; rfl
    unfold messageDecryptSkipped at hdec_ok
    obtain ⟨st₀, hget, hrest_ok, hrest_val⟩ := run_bind_some_decomp _ _ tr₀ hdec_ok
    obtain ⟨hat_k, hget_val⟩ := getLocalState_some_at? hget
    rw [hget_val] at hrest_ok hrest_val
    obtain ⟨msg, _, hrest2_ok, hrest2_val⟩ := run_bind_some_decomp _ _ tr₀ hrest_ok
    obtain ⟨e, _, hrest3_ok, hrest3_val⟩ := run_bind_some_decomp _ _ _ hrest2_ok
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
    let tr₂ := ((receiveSignalMsg msgIdx).run tr₀).2.val
    let tr₃ := ((DY.getEntry skIdx : Traceful (ProtocolEvent.ExecEntryT TREvent)).run tr₂).2.val
    have hle02 : tr₀.length ≤ tr₂.length :=
      Trace.length_le _ _ ((receiveSignalMsg msgIdx).run tr₀).2.property
    have hle23 : tr₂.length ≤ tr₃.length :=
      Trace.length_le _ _
        ((DY.getEntry skIdx : Traceful (ProtocolEvent.ExecEntryT TREvent)).run tr₂).2.property
    have hpure_val :
        ((Move.act (.decryptSkipped me stateIdx msgIdx skIdx pqIdx spqrMsgIdx wrapped)).run tr₀).2.val =
        ((messageDecryptSkipped me stateIdx msgIdx skIdx pqIdx spqrMsgIdx).run tr₀).2.val := by
      change ((messageDecryptSkipped me stateIdx msgIdx skIdx pqIdx spqrMsgIdx >>=
        fun _ => pure ()).run tr₀).2.val = _
      rw [hval, DY.Traceful.run_pure]
    refine ⟨st₀, j, st', hat_k, Nat.le_trans hle02 (Nat.le_trans hle23 hj1), ?_, hinit, ?_⟩
    · change j < ((Move.act (.decryptSkipped me stateIdx msgIdx skIdx pqIdx spqrMsgIdx wrapped)).run tr₀).2.val.length
      rw [hpure_val]
      unfold messageDecryptSkipped; rw [hrest_val, hrest2_val, hrest3_val]; exact hj2
    · change (((Move.act (.decryptSkipped me stateIdx msgIdx skIdx pqIdx spqrMsgIdx wrapped)).run tr₀).2.val.at? j :
        Option TRStEntry) = _
      rw [hpure_val]
      unfold messageDecryptSkipped; rw [hrest_val, hrest2_val, hrest3_val]; exact hat_j
  | _ => simp [Move.stateLoad?] at hmi

/-- Appending any move `m` whose loaded snapshot (if any) satisfies
`isCurrentSnapshot (runTraceMoves r ms) k = true` preserves `StateFaithful r`. -/
theorem stateFaithful_snoc_of_isCurrentSnapshot {r : ProtocolSetup} {ms : List Move} {m : Move}
    (hsf : StateFaithful r ms)
    (hcur : ∀ p k b, m.stateLoad? = some (p, k, b) →
      isCurrentSnapshot (runTraceMoves r ms) k = true) :
    StateFaithful r (ms ++ [m]) := by
  intro i j mi mj p k b hij hi hj hmi hok hmj
  by_cases hj_lt : j < ms.length
  · have hi_lt : i < ms.length := Nat.lt_trans hij hj_lt
    rw [List.getElem?_append_left hi_lt] at hi
    rw [List.getElem?_append_left hj_lt] at hj
    have htake : (ms ++ [m]).take i = ms.take i :=
      List.take_append_of_le_length (Nat.le_of_lt hi_lt)
    rw [htake] at hok
    exact hsf i j mi mj p k b hij hi hj hmi hok hmj
  · have hj_ge : ms.length ≤ j := Nat.le_of_not_lt hj_lt
    rw [List.getElem?_append_right hj_ge] at hj
    rcases Nat.eq_or_lt_of_le hj_ge with rfl | hj_gt
    · simp only [Nat.sub_self, List.getElem?_cons_zero, Option.some.injEq] at hj
      subst hj
      rw [List.getElem?_append_left hij] at hi
      have htake : (ms ++ [m]).take i = ms.take i :=
        List.take_append_of_le_length (Nat.le_of_lt hij)
      rw [htake] at hok
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
        conv_rhs => rw [hsplit, ← List.cons_append, runMoves_append_fst]
        exact runMoves_le (ms.drop (i + 1)) (mi.next (runTraceMoves r (ms.take i)))
      have hfalse := not_isCurrentSnapshot_of_stateLoad_true_ok hmi hok hle
      rw [hcur p k b hmj] at hfalse
      cases hfalse
    · obtain ⟨d, hd⟩ : ∃ d, j - ms.length = d + 1 := ⟨j - ms.length - 1, by omega⟩
      rw [hd, List.getElem?_cons_succ, List.getElem?_nil] at hj
      cases hj

/-! ## Prefix and Move-Explanation Faithfulness -/

/-- `Forall₂ EventMatchesEntry τ vis` equates `callCount vis` and `(callStarts τ).length`. -/
theorem callCount_of_forall₂_eventMatchesEntry {interpretation : ExternInterpretation}
    {r : ProtocolSetup} {S : OpaqueSymbolSemantics} {g : Ghost} {τ : List MachineEvent} {vis : List VisEntry}
    (h : List.Forall₂ (EventMatchesEntry interpretation r S g) τ vis) :
    callCount vis = (callStarts τ).length := by
  induction h with
  | nil => rfl
  | @cons hw ev τ vis hrel _ ih =>
    have hk : ev.kind = eventKind hw := hrel.1.symm
    unfold callCount callStarts at ih ⊢
    simp only [List.filter_cons, hk]
    split <;> simp [ih]

/-- Extending `RoleFaithful r who ms` by one move `m`: environment/reject moves (`m.party? = none`)
preserve `RoleFaithful` unconditionally; party moves require `who[callCount (runVis r ms)]? = some p`. -/
theorem roleFaithful_snoc {r : ProtocolSetup} {who : List Participant} {ms : List Move} {m : Move}
    (hrf : RoleFaithful r who ms)
    (hm : ∀ p, m.party? = some p → who[callCount (runVis r ms)]? = some p) :
    RoleFaithful r who (ms ++ [m]) := by
  intro i m' p hi hp
  by_cases hlt : i < ms.length
  · rw [List.getElem?_append_left hlt] at hi
    rw [List.take_append_of_le_length (Nat.le_of_lt hlt)]
    exact hrf i m' p hi hp
  · have hi_lt : i < (ms ++ [m]).length := (List.getElem?_eq_some_iff.mp hi).1
    simp only [List.length_append, List.length_singleton] at hi_lt
    have hi_eq : i = ms.length := by omega
    subst hi_eq
    simp only [List.getElem?_append_right (Nat.le_refl _), Nat.sub_self,
      List.getElem?_cons_zero, Option.some.injEq] at hi
    subst hi
    rw [List.take_left]
    exact hm p hp

/-- Appending any move with `m.prekeyPath? = none` (every `encrypt*`, unwrapped `decrypt*`, `reject`,
`attackerSend`, `expose*`, `compromise*`, `aliceStart`) preserves `PathFaithful` on `τ₁`. -/
theorem pathFaithful_snoc_of_prekeyPath_none {interpretation : ExternInterpretation}
    {r : ProtocolSetup} {S : OpaqueSymbolSemantics} {g : Ghost} {ms : List Move} {m : Move} {τ₁ : List MachineEvent}
    (hpf : PathFaithful interpretation r S g ms τ₁)
    (hno : m.prekeyPath? = none) :
    PathFaithful interpretation r S g (ms ++ [m]) τ₁ := by
  intro i m' promote b p hi hpath hcall hparse
  by_cases hlt : i < ms.length
  · rw [List.getElem?_append_left hlt] at hi
    rw [List.take_append_of_le_length (Nat.le_of_lt hlt)] at hcall ⊢
    exact hpf i m' promote b p hi hpath hcall hparse
  · have hi_lt : i < (ms ++ [m]).length := (List.getElem?_eq_some_iff.mp hi).1
    simp only [List.length_append, List.length_singleton] at hi_lt
    have hi_eq : i = ms.length := by omega
    subst hi_eq
    simp only [List.getElem?_append_right (Nat.le_refl _), Nat.sub_self,
      List.getElem?_cons_zero, Option.some.injEq] at hi
    subst hi
    rw [hno] at hpath
    cases hpath

/-- Appending hardware events `blk` whose only call-start event is `.pt pt` (any `session_send_wire`
block) preserves `PathFaithful`. -/
theorem pathFaithful_append_pt {interpretation : ExternInterpretation} {r : ProtocolSetup} {S : OpaqueSymbolSemantics}
    {g : Ghost} {ms : List Move} {acc blk : List MachineEvent} {pt : HwBytes}
    (hcs : callStarts blk = [.pt pt])
    (hpf : PathFaithful interpretation r S g ms acc) :
    PathFaithful interpretation r S g ms (acc ++ blk) := by
  intro i m promote b pf hi hpath hcall hparse
  have hcs_app : callStarts (acc ++ blk) = callStarts acc ++ [.pt pt] := by
    simp only [callStarts, List.filter_append]
    unfold callStarts at hcs
    rw [hcs]
  rw [hcs_app] at hcall
  by_cases hk : callCount (runVis r (ms.take i)) < (callStarts acc).length
  · rw [List.getElem?_append_left hk] at hcall
    exact hpf i m promote b pf hi hpath hcall hparse
  · have hk_lt : callCount (runVis r (ms.take i)) <
        (callStarts acc ++ [MachineEvent.pt pt]).length :=
      (List.getElem?_eq_some_iff.mp hcall).1
    simp only [List.length_append, List.length_singleton] at hk_lt
    have hk_eq : callCount (runVis r (ms.take i)) = (callStarts acc).length := by omega
    rw [hk_eq, List.getElem?_append_right (Nat.le_refl _), Nat.sub_self,
      List.getElem?_cons_zero, Option.some.injEq] at hcall
    cases hcall

/-- Extending `OutcomeFaithful r ok ms` by one move `m`: moves that are neither `.reject` nor
`AliceDone`-emitting preserve `OutcomeFaithful` unconditionally. -/
theorem outcomeFaithful_snoc {r : ProtocolSetup} {ok : Nat → Bool} {ms : List Move} {m : Move}
    (hof : OutcomeFaithful r ok ms)
    (hrej : ∀ ds, m = .reject ds → ok (callCount (runVis r ms)) = false)
    (had : (eventIdx isAliceDone (runTraceMoves r ms) (m.next (runTraceMoves r ms))).isSome →
      ok (callCount (runVis r ms)) = true) :
    OutcomeFaithful r ok (ms ++ [m]) := by
  intro i m' hi
  by_cases hlt : i < ms.length
  · rw [List.getElem?_append_left hlt] at hi
    simp only [List.take_append_of_le_length (Nat.le_of_lt hlt)]
    exact hof i m' hi
  · have hi_lt : i < (ms ++ [m]).length := (List.getElem?_eq_some_iff.mp hi).1
    simp only [List.length_append, List.length_singleton] at hi_lt
    have hi_eq : i = ms.length := by omega
    subst hi_eq
    simp only [List.getElem?_append_right (Nat.le_refl _), Nat.sub_self,
      List.getElem?_cons_zero, Option.some.injEq] at hi
    subst hi
    simp only [List.take_left]
    exact ⟨hrej, had⟩

theorem recvRepresentations_mono_append {interpretation : ExternInterpretation}
    {r : ProtocolSetup} {S : OpaqueSymbolSemantics} {g : Ghost} {ms Δ : List Move} {b : HwBytes} {t : DY.Bytes}
    (ht : t ∈ recvRepresentations interpretation r S g ms b) :
    t ∈ recvRepresentations interpretation r S g (ms ++ Δ) b := by
  have hle : runTraceMoves r ms ≤ runTraceMoves r (ms ++ Δ) := by
    unfold runTraceMoves
    rw [← List.cons_append, runMoves_append_fst]
    exact runMoves_le Δ (runTraceMoves r ms)
  exact ⟨DY.Bytes.AttackerKnows_le _ _ _ hle ht.1, ht.2⟩

theorem preKeyRepresentations_mono_append {interpretation : ExternInterpretation}
    {r : ProtocolSetup} {S : OpaqueSymbolSemantics} {g : Ghost} {ms Δ : List Move} {b : HwBytes} {x : PreKeyRep}
    (hx : x ∈ preKeyRepresentations interpretation r S g ms b) :
    x ∈ preKeyRepresentations interpretation r S g (ms ++ Δ) b := by
  have hle : runTraceMoves r ms ≤ runTraceMoves r (ms ++ Δ) := by
    unfold runTraceMoves
    rw [← List.cons_append, runMoves_append_fst]
    exact runMoves_le Δ (runTraceMoves r ms)
  exact ⟨DY.Bytes.AttackerKnows_le _ _ _ hle hx.1,
    DY.Bytes.AttackerKnows_le _ _ _ hle hx.2.1,
    DY.Bytes.AttackerKnows_le _ _ _ hle hx.2.2.1,
    hx.2.2.2⟩

private theorem runMoves_append_snd (xs ys : List Move) (tr : ExecTrace) :
    (runMoves (xs ++ ys) tr).2 = (runMoves xs tr).2 ++ (runMoves ys (runMoves xs tr).1).2 := by
  induction xs generalizing tr with
  | nil => simp [runMoves]
  | cons x xs ih => simp only [List.cons_append, runMoves, ih, List.append_assoc]

private theorem runVis_append {r : ProtocolSetup} (ms Δ : List Move) :
    runVis r (ms ++ Δ) = runVis r ms ++ (runMoves Δ (runTraceMoves r ms)).2 := by
  unfold runVis runTraceMoves
  rw [← List.cons_append, runMoves_append_snd]

private theorem snd_mem_of_mem_zip {α β : Type} {xs : List α} {ys : List β} {p : α × β}
    (h : p ∈ xs.zip ys) : p.2 ∈ ys := by
  induction xs generalizing ys with
  | nil => simp at h
  | cons x xs ih =>
    rcases ys with _ | ⟨y, ys⟩
    · simp at h
    · simp only [List.zip_cons_cons, List.mem_cons] at h
      rcases h with rfl | htail
      · exact List.mem_cons_self
      · exact List.mem_cons_of_mem y (ih htail)

/-- Extending `ReadFaithful` across moves `Δ` whose visible entries contain no `.recv` entry. -/
theorem readFaithful_append_no_recv {interpretation : ExternInterpretation}
    {r : ProtocolSetup} {S : OpaqueSymbolSemantics} {g : Ghost} {ms Δ : List Move} {acc blk : List MachineEvent}
    (hlen : acc.length = (runVis r ms).length)
    (hno : ∀ v ∈ (runMoves Δ (runTraceMoves r ms)).2, v.kind ≠ .recv)
    (hrf : ReadFaithful interpretation r S g ms acc) :
    ReadFaithful interpretation r S g (ms ++ Δ) (acc ++ blk) := by
  intro ev hev hkind
  rw [runVis_append, List.zip_append hlen] at hev
  rcases List.mem_append.mp hev with hev_old | hev_new
  · have hold := hrf ev hev_old hkind
    split at hold
    · exact recvRepresentations_mono_append hold
    · intro p hp; exact recvRepresentations_mono_append (hold p hp)
    · exact preKeyRepresentations_mono_append hold
    · exact trivial
  · exact absurd hkind (hno ev.2 (snd_mem_of_mem_zip hev_new))

end Symbolic.Swarm.CREF.Stage1Wire
