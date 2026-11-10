/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Symbolic.Proofs.Swarm.CREF.Cli.RetiredTraceExplanation
import Batteries.Data.List.Lemmas
import Symbolic.Proofs.Swarm.CREF.ModelBridge
import Symbolic.Proofs.Swarm.CREF.ModelMono
import Symbolic.Proofs.Swarm.CREF.ReadFaithful

/-!
# Matched-Prefix Splitting at Call Boundaries

Splits a `MatchedPrefix` on `acc ++ blk` into `ms = ms₀ ++ δ` with `MatchedPrefix` on `(ms₀, acc)`
and `blk` matched by `δ`, whenever the cut before `blk` cannot fall strictly inside a single move's
visible entries (in particular when `blk` starts with a `.recv` or `.pt` event).
-/

@[expose] public section

set_option autoImplicit false

namespace Symbolic.Swarm.CREF

open DY
open DY.Libsignal
open DY.Libsignal.Composed
open DY.Libsignal.Composed.Refinement
open DY.Libsignal.HwEvents (MachineEvent)
open CryptoProofLib.Refinement (ExternInterpretation)

/-! ## List helpers -/

theorem b5_mem_tail_append {α : Type} {l₁ l₂ : List α} {v : α} (h : v ∈ (l₁ ++ l₂).tail) :
    v ∈ l₁.tail ∨ v ∈ l₂ := by
  cases l₁ with
  | nil => exact Or.inr (List.mem_of_mem_tail h)
  | cons x t =>
    simp only [List.cons_append, List.tail_cons, List.mem_append] at h
    exact h

theorem b5_mem_tail_take {α : Type} {l : List α} {n : Nat} {v : α} (h : v ∈ (l.take n).tail) :
    v ∈ l.tail := by
  cases l with
  | nil => simp at h
  | cons x t =>
    cases n with
    | zero => simp at h
    | succ n =>
      simp only [List.take_succ_cons, List.tail_cons] at h ⊢
      exact List.mem_of_mem_take h

theorem b5_tail_toList {α : Type} (o : Option α) : o.toList.tail = [] := by
  cases o <;> rfl

theorem b5_mem_tail_of_getElem? {α : Type} {l : List α} {k : Nat} {b : α} (hk : 0 < k)
    (h : l[k]? = some b) : b ∈ l.tail := by
  cases l with
  | nil => simp at h
  | cons x t =>
    obtain ⟨k', rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
    simp only [List.getElem?_cons_succ] at h
    exact List.mem_of_getElem? h

theorem b5_getElem?_append_length {α : Type} (l₁ l₂ : List α) :
    (l₁ ++ l₂)[l₁.length]? = l₂.head? := by
  induction l₁ with
  | nil => cases l₂ <;> rfl
  | cons x t ih =>
    simp only [List.cons_append, List.length_cons, List.getElem?_cons_succ]
    exact ih

theorem b5_forall₂_getElem? {α β : Type} {R : α → β → Prop} {xs : List α} {ys : List β}
    (h : List.Forall₂ R xs ys) :
    ∀ {i : Nat} {y : β}, ys[i]? = some y → ∃ x, xs[i]? = some x ∧ R x y := by
  induction h with
  | nil => intro i y hy; simp at hy
  | cons hxy _ ih =>
    intro i y hy
    cases i with
    | zero =>
      simp only [List.getElem?_cons_zero, Option.some.injEq] at hy
      subst hy
      exact ⟨_, rfl, hxy⟩
    | succ i =>
      simp only [List.getElem?_cons_succ] at hy ⊢
      exact ih hy

theorem b5_forall₂_length {α β : Type} {R : α → β → Prop} {xs : List α} {ys : List β}
    (h : List.Forall₂ R xs ys) : xs.length = ys.length := by
  induction h with
  | nil => rfl
  | cons _ _ ih => simp only [List.length_cons, ih]

/-! ## Entry kinds of a move -/

/-- A move's own entries (`Move.vis` without the exposures). -/
def b5_ownVis (m : Move) (tr : ExecTrace) : List VisEntry :=
  let tr' := m.next tr
  match m with
  | .aliceStart _ _ _ _ h shown => (aliceVis tr tr' h).take shown
  | .bobStart b _ kh _ mh _ _ shown => (bobVis tr tr' mh (bobOpkPk b kh tr)).take shown
  | .encrypt _ _ _ _ wrap => encVis tr tr' wrap true
  | .encryptAbort .. => encVis tr tr' none false
  | .encryptFail .. => encVis tr tr' none false
  | .decrypt _ stateIdx msgIdx _ _ wrapped => decVis tr tr' stateIdx msgIdx wrapped
  | .decryptSkipped _ stateIdx msgIdx _ _ _ wrapped => decVis tr tr' stateIdx msgIdx wrapped
  | .reject draws =>
    ⟨.recv, [], .unconstrained, none⟩ :: draws.map fun n => ⟨.rng, [], .fresh n, none⟩
  | _ => []

theorem b5_vis_eq (m : Move) (tr : ExecTrace) :
    m.vis tr = b5_ownVis m tr ++ exposures tr (m.next tr) := by
  cases m <;> rfl

theorem b5_pqExposureAt_kind {tr' : ExecTrace} {j : Nat} {v : VisEntry}
    (h : pqExposureAt tr' j = some v) : v.kind = .leak := by
  simp only [pqExposureAt] at h
  split at h <;> (try simp only [Option.some.injEq] at h) <;> (try subst h) <;>
    first | rfl | cases h

theorem b5_trExposureAt_kind {tr' : ExecTrace} {j : Nat} {v : VisEntry}
    (h : trExposureAt tr' j = some v) : v.kind = .leak := by
  simp only [trExposureAt] at h
  split at h <;> (try simp only [Option.some.injEq] at h) <;> (try subst h) <;>
    first | rfl | cases h

/-- Every exposure entry is a `leak`. -/
theorem b5_exposures_kind {tr tr' : ExecTrace} {v : VisEntry} (h : v ∈ exposures tr tr') :
    v.kind = .leak := by
  simp only [exposures, List.mem_append, List.mem_filterMap] at h
  rcases h with ⟨j, _, hj⟩ | ⟨j, _, hj⟩
  · exact b5_pqExposureAt_kind hj
  · exact b5_trExposureAt_kind hj

/-- The setup's entries are all `leak`s (it has no own entries). -/
theorem b5_setup_vis_leak (r : ProtocolSetup) (tr : ExecTrace) :
    ∀ v ∈ r.setupMove.vis tr, v.kind = .leak := by
  intro v hv
  rw [b5_vis_eq] at hv
  have h0 : b5_ownVis r.setupMove tr = [] := rfl
  rw [h0, List.nil_append] at hv
  exact b5_exposures_kind hv

theorem b5_aliceDraws_kind (d : Option Nat) :
    ∀ (l : List DY.Bytes), ∀ v ∈ aliceDraws d l, v.kind = .rng
  | [] => by simp [aliceDraws]
  | [ek] => by simp [aliceDraws, rngEntry]
  | ek :: entropy :: rest => by
    intro v hv
    have hv' : v ∈ (rngEntry ek :: kyberCoinEntries entropy) ++
        (rest.take 1).map (fun dhsA => ({ rngEntry dhsA with anchor := d } : VisEntry)) := hv
    rcases List.mem_append.1 hv' with hv | hv
    · rcases List.mem_cons.1 hv with rfl | hv
      · rfl
      · obtain ⟨_, _, rfl⟩ := List.mem_map.1 hv
        rfl
    · obtain ⟨_, _, rfl⟩ := List.mem_map.1 hv
      rfl

theorem b5_aliceVis_tail {tr tr' : ExecTrace} {h : PQXDH.BundleHandles} {v : VisEntry}
    (hv : v ∈ (aliceVis tr tr' h).tail) : v.kind ≠ .recv ∧ v.kind ≠ .pt := by
  simp only [aliceVis, List.tail_cons] at hv
  rw [b5_aliceDraws_kind _ _ v hv]
  exact ⟨by decide, by decide⟩

theorem b5_bobVis_tail {tr tr' : ExecTrace} {mh : PQXDH.PreKeyMsgHandles}
    {opk : Option DY.Bytes} {v : VisEntry} (hv : v ∈ (bobVis tr tr' mh opk).tail) :
    v.kind ≠ .recv ∧ v.kind ≠ .pt := by
  simp only [bobVis, List.cons_append, List.tail_cons, List.mem_append, List.mem_map] at hv
  rcases hv with ⟨_, _, rfl⟩ | hv
  · exact ⟨by simp [rngEntry], by simp [rngEntry]⟩
  · cases hp : receivedPlaintext tr tr' with
    | none => simp [hp] at hv
    | some m =>
      simp only [hp, Option.map_some, Option.toList_some, List.mem_singleton] at hv
      subst hv
      exact ⟨by simp, by simp⟩

theorem b5_encDraws_tail : ∀ (l : List (DY.Bytes × Nat)),
    ∀ v ∈ (encDraws l).tail, v.kind ≠ .recv ∧ v.kind ≠ .pt
  | [] => by simp [encDraws]
  | (m, c) :: rest => by
    intro v hv
    have hv' : v ∈ (rest.filter (·.2 != 0)).map fun r => rngEntry r.1 := hv
    obtain ⟨_, _, rfl⟩ := List.mem_map.1 hv'
    exact ⟨by simp [rngEntry], by simp [rngEntry]⟩

theorem b5_encSend_kind (tr tr' : ExecTrace) (wrap : Option (Nat × Nat)) :
    ∀ v ∈ encSend tr tr' wrap, v.kind ≠ .recv ∧ v.kind ≠ .pt := by
  unfold encSend
  split
  · split <;> simp
  · simp

theorem b5_encVis_tail {tr tr' : ExecTrace} {wrap : Option (Nat × Nat)} {ws : Bool}
    {v : VisEntry} (hv : v ∈ (encVis tr tr' wrap ws).tail) : v.kind ≠ .recv ∧ v.kind ≠ .pt := by
  simp only [encVis] at hv
  rcases b5_mem_tail_append hv with hv | hv
  · exact b5_encDraws_tail _ v hv
  · cases ws
    · simp at hv
    · exact b5_encSend_kind _ _ _ v (by simpa using hv)

theorem b5_decVis_tail {tr tr' : ExecTrace} {si i : Nat} {w : Bool} {v : VisEntry}
    (hv : v ∈ (decVis tr tr' si i w).tail) : v.kind ≠ .recv ∧ v.kind ≠ .pt := by
  simp only [decVis] at hv
  rcases b5_mem_tail_append hv with hv | hv
  · rcases b5_mem_tail_append hv with hv | hv
    · rw [b5_tail_toList] at hv
      simp at hv
    · simp only [List.mem_map] at hv
      obtain ⟨_, _, rfl⟩ := hv
      exact ⟨by simp [rngEntry], by simp [rngEntry]⟩
  · cases hp : receivedPlaintext tr tr' with
    | none => simp [hp] at hv
    | some m =>
      simp only [hp, Option.map_some, Option.toList_some, List.mem_singleton] at hv
      subst hv
      exact ⟨by simp, by simp⟩

theorem b5_reject_tail {draws : List Nat} {v : VisEntry}
    (hv : v ∈ ((⟨.recv, [], .unconstrained, none⟩ : VisEntry) ::
      draws.map fun n => (⟨.rng, [], .fresh n, none⟩ : VisEntry)).tail) :
    v.kind ≠ .recv ∧ v.kind ≠ .pt := by
  simp only [List.tail_cons, List.mem_map] at hv
  obtain ⟨_, _, rfl⟩ := hv
  exact ⟨by simp, by simp⟩

theorem b5_not_mem_tail_nil {v : VisEntry} (hv : v ∈ ([] : List VisEntry).tail) : False := by
  simp at hv

theorem b5_ownVis_tail (m : Move) (tr : ExecTrace) {v : VisEntry}
    (hv : v ∈ (b5_ownVis m tr).tail) : v.kind ≠ .recv ∧ v.kind ≠ .pt := by
  cases m with
  | aliceStart a b i j h shown =>
    dsimp only [b5_ownVis] at hv
    exact b5_aliceVis_tail (b5_mem_tail_take hv)
  | bobStart b a kh ra mh pq sp shown =>
    dsimp only [b5_ownVis] at hv
    exact b5_bobVis_tail (b5_mem_tail_take hv)
  | encrypt me si cl pq wrap =>
    dsimp only [b5_ownVis] at hv
    exact b5_encVis_tail hv
  | encryptAbort me si =>
    dsimp only [b5_ownVis] at hv
    exact b5_encVis_tail hv
  | encryptFail me si cl =>
    dsimp only [b5_ownVis] at hv
    exact b5_encVis_tail hv
  | decrypt me si mi pq sp w =>
    dsimp only [b5_ownVis] at hv
    exact b5_decVis_tail hv
  | decryptSkipped me si mi sk pq sp w =>
    dsimp only [b5_ownVis] at hv
    exact b5_decVis_tail hv
  | reject draws =>
    dsimp only [b5_ownVis] at hv
    exact b5_reject_tail hv
  | setup _ _ _ => exact (b5_not_mem_tail_nil hv).elim
  | compromiseIK _ _ => exact (b5_not_mem_tail_nil hv).elim
  | compromiseSPK _ _ => exact (b5_not_mem_tail_nil hv).elim
  | compromisePQSPK _ _ => exact (b5_not_mem_tail_nil hv).elim
  | compromiseOPK _ _ => exact (b5_not_mem_tail_nil hv).elim
  | exposeKey _ _ _ => exact (b5_not_mem_tail_nil hv).elim
  | exposeSpqr _ _ => exact (b5_not_mem_tail_nil hv).elim
  | exposeSkipped _ => exact (b5_not_mem_tail_nil hv).elim
  | attackerSend _ => exact (b5_not_mem_tail_nil hv).elim
  | brkDH =>
    exact (b5_not_mem_tail_nil hv).elim
  | brkKEM =>
    exact (b5_not_mem_tail_nil hv).elim

/-- `.recv` and `.pt` entries appear only as the first visible entry of a move. -/
theorem vis_tail_not_recv_pt (m : Move) (tr : ExecTrace) :
    ∀ v ∈ (m.vis tr).tail, v.kind ≠ .recv ∧ v.kind ≠ .pt := by
  intro v hv
  rw [b5_vis_eq] at hv
  rcases b5_mem_tail_append hv with hv | hv
  · exact b5_ownVis_tail m tr hv
  · rw [b5_exposures_kind hv]
    exact ⟨by decide, by decide⟩

/-! ## The generic split -/

/-- No cut admissible for `B` falls strictly inside the entry list `l`. -/
def b5_NoCutMove (B : VisEntry → VisEntry → Prop) (l : List VisEntry) : Prop :=
  ∀ (k : Nat) (a b : VisEntry), 0 < k → l[k - 1]? = some a → l[k]? = some b → ¬ B a b

/-- No cut admissible for `B` falls strictly inside one move's entries, along the run. -/
def b5_NoCutFrom (B : VisEntry → VisEntry → Prop) : List Move → ExecTrace → Prop
  | [], _ => True
  | m :: ms, tr => b5_NoCutMove B (m.vis tr) ∧ b5_NoCutFrom B ms (m.next tr)

theorem b5_noCutFrom_of_mem (B : VisEntry → VisEntry → Prop) :
    ∀ (L : List Move), (∀ m ∈ L, ∀ tr, b5_NoCutMove B (m.vis tr)) →
      ∀ tr, b5_NoCutFrom B L tr
  | [], _, _ => trivial
  | m :: L, h, tr =>
    ⟨h m (List.mem_cons_self ..) tr,
      b5_noCutFrom_of_mem B L (fun m' hm' => h m' (List.mem_cons_of_mem _ hm')) _⟩

/-- An admissible cut at position `n` of a run's visible entries occurs at a move boundary. -/
theorem b5_split_core (B : VisEntry → VisEntry → Prop) :
    ∀ (L : List Move) (tr : ExecTrace) (n : Nat), b5_NoCutFrom B L tr →
      n ≤ (runMoves L tr).2.length →
      (∀ a b, 0 < n → (runMoves L tr).2[n - 1]? = some a → (runMoves L tr).2[n]? = some b →
        B a b) →
      ∃ L₀ L₁, L = L₀ ++ L₁ ∧ (runMoves L₀ tr).2.length = n
  | [], tr, n, _, hn, _ => by
    refine ⟨[], [], rfl, ?_⟩
    have h0 : (runMoves [] tr).2.length = 0 := rfl
    omega
  | m :: L, tr, n, hnc, hn, hcut => by
    have hnc' : b5_NoCutMove B (m.vis tr) ∧ b5_NoCutFrom B L (m.next tr) := hnc
    obtain ⟨hnc1, hnc2⟩ := hnc'
    have hV : (runMoves (m :: L) tr).2 = m.vis tr ++ (runMoves L (m.next tr)).2 := rfl
    rw [hV, List.length_append] at hn
    rw [hV] at hcut
    by_cases ha : (m.vis tr).length ≤ n
    · obtain ⟨L₀, L₁, hL, hlen⟩ := b5_split_core B L (m.next tr) (n - (m.vis tr).length)
        hnc2 (by omega) (fun a b hpos ha' hb' => by
          have e1 : (m.vis tr ++ (runMoves L (m.next tr)).2)[n - 1]? =
              (runMoves L (m.next tr)).2[n - 1 - (m.vis tr).length]? :=
            List.getElem?_append_right (by omega)
          have e2 : (m.vis tr ++ (runMoves L (m.next tr)).2)[n]? =
              (runMoves L (m.next tr)).2[n - (m.vis tr).length]? :=
            List.getElem?_append_right ha
          have e3 : n - 1 - (m.vis tr).length = n - (m.vis tr).length - 1 := by omega
          refine hcut a b (by omega) ?_ ?_
          · rw [e1, e3]; exact ha'
          · rw [e2]; exact hb')
      subst hL
      refine ⟨m :: L₀, L₁, rfl, ?_⟩
      show (m.vis tr ++ (runMoves L₀ (m.next tr)).2).length = n
      rw [List.length_append, hlen]
      omega
    · by_cases h0 : n = 0
      · subst h0
        exact ⟨[], m :: L, rfl, rfl⟩
      · exfalso
        have hlt : n < (m.vis tr).length := by omega
        have ea : (m.vis tr)[n - 1]? = some (m.vis tr)[n - 1] :=
          List.getElem?_eq_getElem (by omega)
        have eb : (m.vis tr)[n]? = some (m.vis tr)[n] := List.getElem?_eq_getElem hlt
        have e1 : (m.vis tr ++ (runMoves L (m.next tr)).2)[n - 1]? = (m.vis tr)[n - 1]? :=
          List.getElem?_append_left (by omega)
        have e2 : (m.vis tr ++ (runMoves L (m.next tr)).2)[n]? = (m.vis tr)[n]? :=
          List.getElem?_append_left hlt
        exact hnc1 n _ _ (by omega) ea eb
          (hcut _ _ (by omega) (e1.trans ea) (e2.trans eb))

theorem modelRun_prefix_of_reachable {r : ProtocolSetup} {ms₀ δ : List Move}
    (h : ModelRun r (ms₀ ++ δ)) (_hr : (runTraceMoves r ms₀).Reachable reachability) :
    ModelRun r ms₀ :=
  modelRun_prefix h

/-- If no `B`-cut falls strictly inside a move and the cut before `blk` satisfies `B`, the matched
run splits at a move boundary. -/
theorem matchedPrefix_split_of_noCut
    {interpretation : ExternInterpretation}
    {r : ProtocolSetup} {S : OpaqueSymbolSemantics} {who : List Participant} {g : Ghost} {ms : List Move}
    {acc blk : List MachineEvent}
    (B : VisEntry → VisEntry → Prop)
    (h : MatchedPrefix interpretation r S who g ms (acc ++ blk))
    (hnc : b5_NoCutFrom B (r.setupMove :: ms) Trace.nil)
    (hcut : ∀ a b, 0 < acc.length → (runVis r ms)[acc.length - 1]? = some a →
      (runVis r ms)[acc.length]? = some b → B a b)
    (hnil : acc = [] → runVis r [] = [])
    (_hreach : ∀ ms₀ δ, ms = ms₀ ++ δ → (runTraceMoves r ms₀).Reachable reachability :=
      fun ms₀ δ he => by
        have hk := h.2.1.2.2.1.2.2 ms₀.length
        rwa [he, List.take_left] at hk) :
    ∃ ms₀ δ, ms = ms₀ ++ δ ∧ MatchedPrefix interpretation r S who g ms₀ acc ∧
      List.Forall₂ (EventMatchesEntry interpretation r S g) blk
        (runMoves δ (runTraceMoves r ms₀)).2 := by
  obtain ⟨hc, hrun, hrole, hpath, hread, hfor⟩ := h
  have hlen : (acc ++ blk).length = (runVis r ms).length := b5_forall₂_length hfor
  have hV : runVis r ms = (runMoves (r.setupMove :: ms) Trace.nil).2 := rfl
  obtain ⟨L₀, L₁, hL, hL₀⟩ := b5_split_core B (r.setupMove :: ms) Trace.nil acc.length hnc
    (by rw [← hV, ← hlen, List.length_append]; omega) hcut
  cases L₀ with
  | nil =>
    have hacc : acc = [] := List.eq_nil_of_length_eq_zero hL₀.symm
    subst hacc
    have h0 := hnil rfl
    have hsplit := runVis_append r [] ms
    rw [List.nil_append, h0, List.nil_append] at hsplit
    refine ⟨[], ms, rfl,
      ⟨hc, modelRun_prefix (ms₀ := []) (δ := ms) hrun,
        roleFaithful_nil r who,
        pathFaithful_nil interpretation r S g [],
        fun _ hev => by simp at hev,
        ?_⟩,
      ?_⟩
    · rw [h0]
      exact List.Forall₂.nil
    · rw [← hsplit]
      exact hfor
  | cons m L₀ =>
    simp only [List.cons_append, List.cons.injEq] at hL
    obtain ⟨rfl, rfl⟩ := hL
    have hlen₀ : (runVis r L₀).length = acc.length := hL₀
    obtain ⟨h1, h2⟩ := eventsMatch_append_split hfor
    rw [hlen₀, List.take_left] at h1
    rw [hlen₀, List.drop_left] at h2
    exact ⟨L₀, L₁, rfl,
      ⟨hc, modelRun_prefix hrun,
        roleFaithful_prefix hrole,
        pathFaithful_prefix hpath,
        readFaithful_prefix hlen₀.symm hread,
        h1⟩,
      h2⟩

/-! ## Call-boundary split forms -/

/-- A matched run on `acc ++ blk` splits at a move boundary when `blk` starts with a `.recv` or
`.pt` event (or is empty). -/
theorem matchedPrefix_split {interpretation : ExternInterpretation}
    {r : ProtocolSetup} {S : OpaqueSymbolSemantics} {who : List Participant} {g : Ghost} {ms : List Move}
    {acc blk : List MachineEvent}
    (h : MatchedPrefix interpretation r S who g ms (acc ++ blk))
    (hblk : ∀ e ∈ blk.head?, eventKind e = .recv ∨ eventKind e = .pt)
    (hreach : ∀ ms₀ δ, ms = ms₀ ++ δ → (runTraceMoves r ms₀).Reachable reachability :=
      fun ms₀ δ he => by
        have hk := h.2.1.2.2.1.2.2 ms₀.length
        rwa [he, List.take_left] at hk) :
    ∃ ms₀ δ, ms = ms₀ ++ δ ∧ MatchedPrefix interpretation r S who g ms₀ acc ∧
      List.Forall₂ (EventMatchesEntry interpretation r S g) blk
        (runMoves δ (runTraceMoves r ms₀)).2 := by
  have hfor : List.Forall₂ (EventMatchesEntry interpretation r S g) (acc ++ blk) (runVis r ms) :=
    h.2.2.2.2.2
  refine matchedPrefix_split_of_noCut (fun _ b => b.kind = .recv ∨ b.kind = .pt) h
    (b5_noCutFrom_of_mem _ _ (fun m _ tr k a b hk _ hb hB => by
      have := vis_tail_not_recv_pt m tr b (b5_mem_tail_of_getElem? hk hb)
      rcases hB with hB | hB
      · exact this.1 hB
      · exact this.2 hB) _) ?_ ?_ hreach
  · intro a b _ _ hb
    obtain ⟨e, he, hR⟩ := b5_forall₂_getElem? hfor hb
    obtain ⟨hk, -⟩ := hR
    rw [b5_getElem?_append_length] at he
    show b.kind = .recv ∨ b.kind = .pt
    rw [← hk]
    exact hblk e (Option.mem_def.2 he)
  · intro hacc
    subst hacc
    cases hv : runVis r [] with
    | nil => rfl
    | cons x rest =>
      exfalso
      have hsplit := runVis_append r [] ms
      rw [List.nil_append] at hsplit
      have hx : (runVis r ms)[0]? = some x := by
        rw [hsplit, hv, List.cons_append, List.getElem?_cons_zero]
      obtain ⟨e, he, hR⟩ := b5_forall₂_getElem? hfor hx
      obtain ⟨hk, -⟩ := hR
      have hxl : x.kind = .leak := by
        have hmem : x ∈ runVis r [] := by rw [hv]; exact List.mem_cons_self ..
        have hv' : runVis r [] = r.setupMove.vis Trace.nil ++ [] := rfl
        rw [hv', List.append_nil] at hmem
        exact b5_setup_vis_leak r _ x hmem
      have he' : blk.head? = some e := (b5_getElem?_append_length [] blk).symm.trans he
      have := hblk e (Option.mem_def.2 he')
      rw [hk, hxl] at this
      simp at this

end Symbolic.Swarm.CREF
