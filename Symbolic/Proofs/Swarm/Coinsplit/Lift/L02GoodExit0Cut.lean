/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Symbolic.Proofs.Swarm.Coinsplit.Lift.Defs
import DY.ALaCarte.Basic
import DY.Bytes.Basic
import DY.Trace.Basic
import DY.Trace.Monad
import DY.Trace.Manipulation
import DY.Actions.Network
import DY.Actions.PersistentLocalState
import DY.Actions.PersistentGlobalState
import DY.Actions.ProtocolEvent
import DY.Actions.Random
import Symbolic.Proofs.Swarm.CREF.Cli.World.XplTransferPure
import Symbolic.Proofs.Swarm.CREF.Initiate.EntryPureC
import Symbolic.Proofs.Swarm.CREF.Initiate.ModelPure
import Symbolic.Proofs.Swarm.CREF.Xpl.InvCommon
import Symbolic.DYBridge.DY.Bytes.Basic
import Symbolic.DYBridge.DY.Trace.Basic

/-!
# Single-Step `ExplainsCli` Lift from `GoodStepCut`

Proves `outcomeFaithfulCli_of_goodExit0Cut : GoodExit0CutSpec`: given a prefix explanation
`ExplainsCli interp r S who ok σ_pre τ_pre g₀ ms₀`, extending `ms₀` (or `sanitizeMoves`) by `δ`
across a `GoodStepCut` block `blk_hw` upgrades `Clean` on `τ_pre ++ blk_hw` to `ExplainsCli` on
`σ_pre ++ blk_cli`.
-/

@[expose] public section

set_option autoImplicit false

namespace Symbolic.Swarm.Coinsplit.Lift.L02

open CryptoProofLib.Refinement (ExternInterpretation)
open _root_.DY (Participant ExecTrace)
open _root_.DY.Libsignal (HwBytes)
open _root_.DY.Libsignal.HwEvents (MachineEvent)
open _root_.DY.Libsignal.Composed
open _root_.DY.Libsignal.Composed.Refinement
open _root_.DY.Libsignal.Composed.Refinement.Cli
open Symbolic.Swarm.Coinsplit.Lift

/-! ## Prefix transport -/

unseal _root_.DY.Bytes in
private instance (interp : ExternInterpretation) (S : OpaqueSymbolSemantics) (g : Ghost) :
    _root_.DY.Bytes.SubFunction (concretizeRandom g) (concretizeAll interp S g) :=
  @_root_.DY.Bytes.SubFunction.mk _ _ _ _ _ _ _ ⟨fun _ _ => by
    simp only [concretizeAll, allFuns, Symbolic.DYBridge.DY.Bytes.PartialFunction.combine_eq]; rfl⟩

private theorem gamma_randTerm_congr {interp : ExternInterpretation} {S : OpaqueSymbolSemantics}
    {g₁ g₀ : Ghost} {ts sz : Nat} (hσ : g₁.σ ts sz = g₀.σ ts sz) :
    gamma interp S g₁ (randTerm ts sz) = gamma interp S g₀ (randTerm ts sz) := by
  unfold gamma gamma' randTerm
  rw [_root_.DY.Bytes.rec_eq (concretizeRandom g₁) (concretizeAll interp S g₁),
      _root_.DY.Bytes.rec_eq (concretizeRandom g₀) (concretizeAll interp S g₀)]
  simp [concretizeRandom, node]
  split
  · rfl
  · exact hσ

private theorem exists_randTerm_lt_of_mem_newRandoms {tr tr' : ExecTrace}
    {p : _root_.DY.Bytes × Nat} (hp : p ∈ newRandoms tr tr') :
    ∃ ts sz, ts < tr'.length ∧ p.1 = randTerm ts sz := by
  obtain ⟨ts, hts_mem, hmap⟩ := List.mem_filterMap.mp hp
  obtain ⟨e, _, rfl⟩ := Option.map_eq_some_iff.mp hmap
  unfold newIndices at hts_mem
  rw [List.mem_range'_1] at hts_mem
  exact ⟨ts, e.length, by omega, rfl⟩

private theorem single_rng_mem_aliceDraws_randTerm_lt {tr tr' : ExecTrace} {done : Option Nat}
    {v : VisEntry} {t : _root_.DY.Bytes}
    (hv : v ∈ aliceDraws done ((newRandoms tr tr').map Prod.fst))
    (hl : v.layout = .single) (ht : v.terms = [t]) :
    ∃ ts sz, ts < tr'.length ∧ t = randTerm ts sz := by
  rcases hnr : (newRandoms tr tr').map Prod.fst with _ | ⟨ek, rest0⟩
  · rw [hnr] at hv; cases hv
  · rcases rest0 with _ | ⟨entropy, rest⟩
    · rw [hnr] at hv
      rcases List.mem_singleton.mp hv with rfl
      simp only [rngEntry, List.cons.injEq, and_true] at ht; subst ht
      have hmem : ek ∈ (newRandoms tr tr').map Prod.fst := by rw [hnr]; exact .head _
      obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hmem
      exact exists_randTerm_lt_of_mem_newRandoms hp
    · rw [hnr] at hv
      simp only [aliceDraws, List.cons_append, List.mem_cons, List.mem_append] at hv
      rcases hv with rfl | hkc | hdhs
      · simp only [rngEntry, List.cons.injEq, and_true] at ht; subst ht
        have hmem : ek ∈ (newRandoms tr tr').map Prod.fst := by rw [hnr]; exact .head _
        obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hmem
        exact exists_randTerm_lt_of_mem_newRandoms hp
      · unfold kyberCoinEntries at hkc
        obtain ⟨_, _, rfl⟩ := List.mem_map.mp hkc
        cases hl
      · obtain ⟨dhsA, hdhsA, rfl⟩ := List.mem_map.mp hdhs
        simp only [rngEntry, List.cons.injEq, and_true] at ht; subst ht
        have hmem : dhsA ∈ (newRandoms tr tr').map Prod.fst := by
          rw [hnr]
          exact .tail _ (.tail _ (List.mem_of_mem_take hdhsA))
        obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hmem
        exact exists_randTerm_lt_of_mem_newRandoms hp

private theorem single_rng_mem_encVis_randTerm_lt {tr tr' : ExecTrace}
    {wrap : Option (Nat × Nat)} {withSend : Bool} {v : VisEntry} {t : _root_.DY.Bytes}
    (hv : v ∈ encVis tr tr' wrap withSend)
    (hk : v.kind = .rng) (ht : v.terms = [t]) :
    ∃ ts sz, ts < tr'.length ∧ t = randTerm ts sz := by
  rcases List.mem_append.mp hv with hd | hs
  · rcases hnr : newRandoms tr tr' with _ | ⟨_, rest⟩
    · rw [hnr] at hd; cases hd
    · rw [hnr, encDraws] at hd
      rcases List.mem_cons.mp hd with rfl | hrest
      · cases hk
      · obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hrest
        simp only [rngEntry, List.cons.injEq, and_true] at ht; subst ht
        have hq_mem : q ∈ newRandoms tr tr' := by
          rw [hnr]; exact .tail _ (List.mem_of_mem_filter hq)
        exact exists_randTerm_lt_of_mem_newRandoms hq_mem
  · cases withSend with
    | false => simp at hs
    | true =>
      simp only [↓reduceIte, encSend] at hs
      cases hls : lastSent tr tr' with
      | none => simp [hls] at hs
      | some w =>
        rw [hls] at hs
        cases wrap <;> (rcases List.mem_singleton.mp hs with rfl; cases hk)

private theorem single_rng_mem_decVis_randTerm_lt {tr tr' : ExecTrace}
    {stateIdx msgIdx : Nat} {wrapped : Bool} {v : VisEntry} {t : _root_.DY.Bytes}
    (hv : v ∈ decVis tr tr' stateIdx msgIdx wrapped)
    (hk : v.kind = .rng) (ht : v.terms = [t]) :
    ∃ ts sz, ts < tr'.length ∧ t = randTerm ts sz := by
  unfold decVis at hv
  rcases List.mem_append.mp hv with h12 | h3
  · rcases List.mem_append.mp h12 with h1 | h2
    · rcases hm : tr.getMessageSentAt msgIdx with _ | b
      · simp [hm] at h1
      · simp [hm] at h1; subst h1; cases hk
    · obtain ⟨q, hq, rfl⟩ := List.mem_map.mp h2
      simp only [rngEntry, List.cons.injEq, and_true] at ht; subst ht
      exact exists_randTerm_lt_of_mem_newRandoms hq
  · rcases hp : receivedPlaintext tr tr' with _ | pt
    · simp [hp] at h3
    · simp [hp] at h3; subst h3; cases hk

private theorem single_rng_mem_vis_randTerm_lt {tr : ExecTrace} {m : Move}
    {v : VisEntry} {t : _root_.DY.Bytes}
    (hv : v ∈ m.vis tr) (hk : v.kind = .rng) (hl : v.layout = .single) (ht : v.terms = [t]) :
    ∃ ts sz, ts < (m.next tr).length ∧ t = randTerm ts sz := by
  unfold Move.vis at hv
  rcases List.mem_append.mp hv with hown | hexp
  · cases m with
    | aliceStart _ _ _ _ h _ =>
      have hv' := List.mem_of_mem_take hown
      rcases List.mem_cons.mp hv' with rfl | hd
      · cases hk
      · exact single_rng_mem_aliceDraws_randTerm_lt hd hl ht
    | bobStart _ _ _ _ _ _ _ _ =>
      have hv' := List.mem_of_mem_take hown
      unfold bobVis at hv'
      rcases List.mem_append.mp hv' with h12 | h3
      · rcases List.mem_cons.mp h12 with rfl | h2
        · cases hk
        · obtain ⟨q, hq, rfl⟩ := List.mem_map.mp h2
          simp only [rngEntry, List.cons.injEq, and_true] at ht; subst ht
          exact exists_randTerm_lt_of_mem_newRandoms hq
      · rcases hp : receivedPlaintext tr _ with _ | pt
        · rw [hp] at h3; cases h3
        · rw [hp] at h3; rcases List.mem_singleton.mp h3 with rfl; cases hk
    | encrypt _ _ _ _ _ => exact single_rng_mem_encVis_randTerm_lt hown hk ht
    | encryptAbort _ _ => exact single_rng_mem_encVis_randTerm_lt hown hk ht
    | encryptFail _ _ _ => exact single_rng_mem_encVis_randTerm_lt hown hk ht
    | decrypt _ _ _ _ _ _ => exact single_rng_mem_decVis_randTerm_lt hown hk ht
    | decryptSkipped _ _ _ _ _ _ _ => exact single_rng_mem_decVis_randTerm_lt hown hk ht
    | reject draws =>
      rcases List.mem_cons.mp hown with rfl | hd
      · cases hk
      · obtain ⟨_, _, rfl⟩ := List.mem_map.mp hd
        cases hl
    | setup _ _ _ | compromiseIK _ _ | compromiseSPK _ _ | compromisePQSPK _ _
    | compromiseOPK _ _ | exposeKey _ _ _ | exposeSpqr _ _ | exposeSkipped _
    | attackerSend _ => cases hown
    | brkDH =>
      cases hown
    | brkKEM =>
      cases hown
  · rw [Symbolic.Swarm.CREF.xpl_exposures_kind hexp] at hk
    cases hk

private theorem runTrace_next_take_le {r : ProtocolSetup} {ms : List Move} {i : Nat} {m : Move}
    (hi : ms[i]? = some m) :
    (m.next (runTraceMoves r (ms.take i))).length ≤ (runTraceMoves r ms).length := by
  have htake : ms.take (i + 1) = ms.take i ++ [m] := by
    rw [List.take_add_one, hi, Option.toList]
  have htr : runTraceMoves r (ms.take (i + 1)) = m.next (runTraceMoves r (ms.take i)) := by
    rw [htake, runTrace_snoc]
  rw [← htr]
  exact _root_.DY.Trace.length_le _ _ (runTrace_take_le r ms (i + 1))

private theorem prefix_move_reduce {r : ProtocolSetup} {ms₀ ms_pre : List Move} {i : Nat} {m' : Move}
    (hms : ms_pre = ms₀ ∨
      ms_pre = Symbolic.Swarm.CREF.Sanitize.sanitizeMoves (setupTrace r) ms₀)
    (hmi : ms_pre[i]? = some m') :
    ∃ m, ms₀[i]? = some m ∧
      runTraceMoves r (ms_pre.take i) = runTraceMoves r (ms₀.take i) ∧
      runVis r (ms_pre.take i) = runVis r (ms₀.take i) ∧
      m'.vis (runTraceMoves r (ms₀.take i)) = m.vis (runTraceMoves r (ms₀.take i)) ∧
      m'.next (runTraceMoves r (ms₀.take i)) = m.next (runTraceMoves r (ms₀.take i)) := by
  rcases hms with rfl | rfl
  · exact ⟨m', hmi, rfl, rfl, rfl, rfl⟩
  · rw [Symbolic.Swarm.CREF.Sanitize.getElem?_sanitizeMoves] at hmi
    rcases hm₀ : ms₀[i]? with _ | m
    · simp [hm₀] at hmi
    · simp only [hm₀, Option.map_some, Option.some.injEq] at hmi
      subst hmi
      have htr_eq : (runMoves (ms₀.take i) (setupTrace r)).1 = runTraceMoves r (ms₀.take i) :=
        (Symbolic.Swarm.CREF.xpl_runTrace_eq r (ms₀.take i)).symm
      refine ⟨m, rfl, ?_, ?_, ?_, ?_⟩
      · rw [Symbolic.Swarm.CREF.Sanitize.sanitizeMoves_take,
          Symbolic.Swarm.CREF.Sanitize.runTrace_sanitizeMoves]
      · rw [Symbolic.Swarm.CREF.Sanitize.sanitizeMoves_take,
          Symbolic.Swarm.CREF.Sanitize.runVis_sanitizeMoves]
      · rw [htr_eq, Symbolic.Swarm.CREF.Sanitize.clearStuckWrap_vis]
      · rw [htr_eq, Symbolic.Swarm.CREF.Sanitize.clearStuckWrap_next]

/-! ## Suffix `runMoves` decomposition and `callCount` uniqueness -/

private theorem forall2_mem_left {α β : Type} {R : α → β → Prop} {xs : List α} {ys : List β}
    (h : List.Forall₂ R xs ys) {x : α} (hx : x ∈ xs) : ∃ y ∈ ys, R x y := by
  induction h with
  | nil => cases hx
  | cons hr _ ih =>
    rcases List.mem_cons.mp hx with rfl | hxt
    · exact ⟨_, .head _, hr⟩
    · obtain ⟨y, hy, hry⟩ := ih hxt
      exact ⟨y, .tail _ hy, hry⟩

private theorem forall2_mem_right {α β : Type} {R : α → β → Prop} {xs : List α} {ys : List β}
    (h : List.Forall₂ R xs ys) {y : β} (hy : y ∈ ys) : ∃ x ∈ xs, R x y := by
  induction h with
  | nil => cases hy
  | cons hr _ ih =>
    rcases List.mem_cons.mp hy with rfl | hyt
    · exact ⟨_, .head _, hr⟩
    · obtain ⟨x, hx, hrx⟩ := ih hyt
      exact ⟨x, .tail _ hx, hrx⟩

private theorem forall2_getElem? {α β : Type} {R : α → β → Prop} {xs : List α} {ys : List β}
    (h : List.Forall₂ R xs ys) : ∀ {k : Nat} {x : α} {y : β},
      xs[k]? = some x → ys[k]? = some y → R x y := by
  induction h with
  | nil => intro k _ _ hx _; simp at hx
  | cons hr _ ih =>
    intro k x y hx hy
    cases k with
    | zero =>
      simp only [List.getElem?_cons_zero, Option.some.injEq] at hx hy
      subst hx hy; exact hr
    | succ k' =>
      exact ih hx hy

private theorem forall2_append_split {α β : Type} {R : α → β → Prop}
    {xs₁ xs₂ : List α} {ys₁ ys₂ : List β} (hlen : xs₁.length = ys₁.length)
    (h : List.Forall₂ R (xs₁ ++ xs₂) (ys₁ ++ ys₂)) :
    List.Forall₂ R xs₁ ys₁ ∧ List.Forall₂ R xs₂ ys₂ := by
  induction xs₁ generalizing ys₁ with
  | nil =>
    cases ys₁ with
    | nil => exact ⟨.nil, h⟩
    | cons _ _ => simp at hlen
  | cons _ _ ih =>
    cases ys₁ with
    | nil => simp at hlen
    | cons _ _ =>
      cases h with
      | cons hr htl =>
        obtain ⟨h1, h2⟩ := ih (Nat.succ.inj hlen) htl
        exact ⟨.cons hr h1, h2⟩

private theorem callCount_eq_callStarts_length_of_forall2
    {interp : ExternInterpretation} {r : ProtocolSetup} {S : OpaqueSymbolSemantics} {g : Ghost}
    {evs : List MachineEvent} {vs : List VisEntry}
    (h : List.Forall₂ (EventMatchesEntry interp r S g) evs vs) :
    callCount vs = (callStarts evs).length := by
  unfold callCount callStarts
  induction h with
  | nil => rfl
  | cons hr _ ih =>
    simp only [List.filter_cons, ← hr.1]
    split <;> simp [ih]

private theorem gamma_length_of_rng_single_match {interp : ExternInterpretation} {r : ProtocolSetup}
    {S : OpaqueSymbolSemantics} {g : Ghost} {coins : HwBytes} {v : VisEntry} {t : _root_.DY.Bytes}
    (hme : EventMatchesEntry interp r S g (.rng coins) v)
    (hl : v.layout = .single) (ht : v.terms = [t]) :
    (gamma interp S g t).length = coins.length := by
  have h2 := hme.2
  dsimp only [eventBytes] at h2
  rw [hl, ht] at h2
  simp only [List.map_cons, List.map_nil, List.cons.injEq, and_true] at h2
  rw [h2]

private theorem runMoves_decomp_at {δ : List Move} {tr : ExecTrace} {j : Nat} {m : Move}
    (hj : δ[j]? = some m) :
    let tr_j := (runMoves (δ.take j) tr).1
    (runMoves δ tr).2 =
      (runMoves (δ.take j) tr).2 ++ m.vis tr_j ++ (runMoves (δ.drop (j + 1)) (m.next tr_j)).2 := by
  have hlt : j < δ.length := (List.getElem?_eq_some_iff.mp hj).1
  have hdrop : δ.drop j = m :: δ.drop (j + 1) := by
    rw [← List.cons_getElem_drop_succ (h := hlt)]
    rw [List.getElem?_eq_getElem hlt, Option.some.injEq] at hj
    rw [hj]
  have hδ : δ = δ.take j ++ (m :: δ.drop (j + 1)) := by
    rw [← hdrop, List.take_append_drop]
  dsimp only
  conv_lhs => rw [hδ]
  rw [Symbolic.Swarm.CREF.TR.runMoves_append, runMoves_cons_snd, List.append_assoc]

private theorem mem_runMoves_iff {δ : List Move} {tr : ExecTrace} {v : VisEntry} :
    v ∈ (runMoves δ tr).2 ↔
      ∃ (j : Nat) (m : Move), δ[j]? = some m ∧ v ∈ m.vis (runMoves (δ.take j) tr).1 := by
  induction δ generalizing tr with
  | nil => simp [runMoves]
  | cons m₀ rest ih =>
    rw [runMoves_cons_snd, List.mem_append]
    constructor
    · rintro (hv | hv)
      · exact ⟨0, m₀, rfl, hv⟩
      · obtain ⟨j, m, hj, hvm⟩ := ih.mp hv
        exact ⟨j + 1, m, hj, hvm⟩
    · rintro ⟨j, m, hj, hvm⟩
      cases j with
      | zero =>
        simp only [List.getElem?_cons_zero, Option.some.injEq] at hj
        subst hj; exact Or.inl hvm
      | succ j' =>
        exact Or.inr (ih.mpr ⟨j', m, hj, hvm⟩)

private theorem callCount_two_lt_le {δ : List Move} (tr : ExecTrace)
    {j₁ j₂ : Nat} {m₁ m₂ : Move}
    (hlt : j₁ < j₂) (hj₁ : δ[j₁]? = some m₁) (hj₂ : δ[j₂]? = some m₂) :
    callCount (m₁.vis (runMoves (δ.take j₁) tr).1) +
      callCount (m₂.vis (runMoves (δ.take j₂) tr).1) ≤
      callCount (runMoves δ tr).2 := by
  rw [runMoves_decomp_at hj₁]
  set tr₁ := (runMoves (δ.take j₁) tr).1
  have hlt₁ : j₁ < δ.length := (List.getElem?_eq_some_iff.mp hj₁).1
  have hd_get : (δ.drop (j₁ + 1))[j₂ - (j₁ + 1)]? = some m₂ := by
    rw [List.getElem?_drop, Nat.add_sub_cancel' (by omega)]
    exact hj₂
  have htr₂ : (runMoves ((δ.drop (j₁ + 1)).take (j₂ - (j₁ + 1))) (m₁.next tr₁)).1 =
      (runMoves (δ.take j₂) tr).1 := by
    have hdrop1 : δ.drop j₁ = m₁ :: δ.drop (j₁ + 1) := by
      rw [← List.cons_getElem_drop_succ (h := hlt₁)]
      rw [List.getElem?_eq_getElem hlt₁, Option.some.injEq] at hj₁
      rw [hj₁]
    have htake₂ : δ.take j₂ = δ.take j₁ ++ (m₁ :: (δ.drop (j₁ + 1)).take (j₂ - (j₁ + 1))) := by
      conv_lhs => rw [← List.take_append_drop j₁ δ, hdrop1]
      rw [List.take_append, List.take_of_length_le (by simp; omega)]
      simp only [List.length_take, Nat.min_eq_left (Nat.le_of_lt hlt₁)]
      have hpos : j₂ - j₁ = (j₂ - (j₁ + 1)) + 1 := by omega
      rw [hpos, List.take_succ_cons]
    rw [htake₂, Symbolic.Swarm.CREF.TR.runMoves_append, runMoves_cons_fst]
  have hsub := runMoves_decomp_at hd_get (tr := m₁.next tr₁)
  dsimp only at hsub
  rw [hsub, htr₂]
  simp only [callCount_append]
  omega

private theorem callCount_pos_of_any {vs : List VisEntry}
    (h : vs.any (fun v => v.kind == .recv || v.kind == .pt) = true) :
    1 ≤ callCount vs := by
  obtain ⟨v, hv, hk⟩ := List.any_eq_true.mp h
  unfold callCount
  exact List.length_pos_of_mem (List.mem_filter.mpr ⟨hv, hk⟩)

private theorem callCount_pos_of_any_recv {vs : List VisEntry}
    (h : vs.any (fun v => v.kind == .recv) = true) :
    1 ≤ callCount vs := by
  obtain ⟨v, hv, hk⟩ := List.any_eq_true.mp h
  have hk' : (v.kind == .recv || v.kind == .pt) = true := by rw [hk]; rfl
  exact callCount_pos_of_any (List.any_eq_true.mpr ⟨v, hv, hk'⟩)

private theorem callCount_pos_of_nonLeak_mem_vis {m : Move} {tr : ExecTrace}
    (hs : m.isSetup = false) (ha : m.LogsSessionCompletion tr) {v : VisEntry}
    (hv : v ∈ m.vis tr) (hnl : v.kind ≠ .leak) :
    1 ≤ callCount (m.vis tr) := by
  rw [Symbolic.Swarm.CREF.xpl_vis_eq] at hv
  rcases List.mem_append.mp hv with hown | hexp
  · cases hhd : Symbolic.Swarm.CREF.xpl_ownVis m tr with
    | nil => rw [hhd] at hown; cases hown
    | cons w ws =>
      have hwk := Symbolic.Swarm.CREF.XplSteps.xpl_ownVis_head_kind hs ha w (by rw [hhd]; rfl)
      have hw_mem : w ∈ m.vis tr := by
        rw [Symbolic.Swarm.CREF.xpl_vis_eq, hhd]; exact .head _
      apply callCount_pos_of_any
      rw [List.any_eq_true]
      refine ⟨w, hw_mem, ?_⟩
      rcases hwk with hk | hk <;> rw [hk] <;> rfl
  · exact absurd (Symbolic.Swarm.CREF.xpl_exposures_kind hexp) hnl

private theorem callStarts_eq_nil_of_no_recv_pt {evs : List MachineEvent}
    (h : ∀ ev ∈ evs, eventKind ev ≠ .recv ∧ eventKind ev ≠ .pt) :
    callStarts evs = [] := by
  unfold callStarts
  rw [List.filter_eq_nil_iff]
  intro ev hev
  obtain ⟨h1, h2⟩ := h ev hev
  cases hk : eventKind ev <;> simp_all

private theorem callStarts_cons_pt_length {pt : HwBytes} {rest : List MachineEvent}
    (h : ∀ ev ∈ rest, eventKind ev ≠ .recv ∧ eventKind ev ≠ .pt) :
    (callStarts (.pt pt :: rest)).length = 1 := by
  change (List.filter _ (.pt pt :: rest)).length = 1
  rw [List.filter_cons_of_pos rfl]
  change (.pt pt :: callStarts rest).length = 1
  rw [callStarts_eq_nil_of_no_recv_pt h]
  rfl

private theorem callStarts_cons_recv_length {w : HwBytes} {rest : List MachineEvent}
    (h : ∀ ev ∈ rest, eventKind ev ≠ .recv ∧ eventKind ev ≠ .pt) :
    (callStarts (.recv w :: rest)).length = 1 := by
  change (List.filter _ (.recv w :: rest)).length = 1
  rw [List.filter_cons_of_pos rfl]
  change (.recv w :: callStarts rest).length = 1
  rw [callStarts_eq_nil_of_no_recv_pt h]
  rfl

private theorem suffix_callCount_eq_of_one_call
    {interp : ExternInterpretation} {r : ProtocolSetup} {S : OpaqueSymbolSemantics} {g₁ : Ghost}
    {τ_pre : List MachineEvent} {ms_pre δ : List Move} {j : Nat} {m : Move}
    (hF_pre : List.Forall₂ (EventMatchesEntry interp r S g₁) τ_pre (runVis r ms_pre))
    (hcc1 : callCount (runMoves δ (runTraceMoves r ms_pre)).2 = 1)
    (hj : δ[j]? = some m)
    (hpos : 1 ≤ callCount (m.vis (runMoves (δ.take j) (runTraceMoves r ms_pre)).1)) :
    callCount (runVis r (ms_pre ++ δ.take j)) = (callStarts τ_pre).length := by
  have hdecomp := runMoves_decomp_at hj (tr := runTraceMoves r ms_pre)
  dsimp only at hdecomp
  have hcc_eq := congrArg callCount hdecomp
  simp only [callCount_append] at hcc_eq
  have hcc_take0 : callCount (runMoves (δ.take j) (runTraceMoves r ms_pre)).2 = 0 := by omega
  rw [runVis_append, callCount_append, hcc_take0, Nat.add_zero]
  exact callCount_eq_callStarts_length_of_forall2 hF_pre

private theorem delta_move_anchored {r : ProtocolSetup} {ms_pre δ : List Move}
    (hrun : ModelRun r (ms_pre ++ δ)) {j : Nat} {m : Move} (hj : δ[j]? = some m) :
    m.isSetup = false ∧ m.LogsSessionCompletion (runMoves (δ.take j) (runTraceMoves r ms_pre)).1 := by
  obtain ⟨_, hns, ⟨_, hanc, _⟩, -⟩ := hrun
  have hlt : j < δ.length := (List.getElem?_eq_some_iff.mp hj).1
  have hm_mem : m ∈ ms_pre ++ δ :=
    List.mem_append_right _ (List.mem_of_getElem? hj)
  have hdrop : δ.drop j = m :: δ.drop (j + 1) := by
    rw [← List.cons_getElem_drop_succ (h := hlt)]
    rw [List.getElem?_eq_getElem hlt, Option.some.injEq] at hj
    rw [hj]
  have hsplit : ms_pre ++ δ = (ms_pre ++ δ.take j) ++ (m :: δ.drop (j + 1)) := by
    rw [List.append_assoc, ← hdrop, List.take_append_drop]
  rw [hsplit] at hanc
  have hanc_m := (Symbolic.Swarm.CREF.xpl_movesAnchored_append_right
    (ms_pre ++ δ.take j) (m :: δ.drop (j + 1)) (setupTrace r) hanc).1
  rw [← Symbolic.Swarm.CREF.xpl_runTrace_eq, runTrace_append] at hanc_m
  exact ⟨hns m hm_mem, hanc_m⟩

private theorem runMoves_eq_vis_of_one_call_no_leak {r : ProtocolSetup} {ms_pre δ : List Move}
    (hrun : ModelRun r (ms_pre ++ δ))
    (hcc1 : callCount (runMoves δ (runTraceMoves r ms_pre)).2 = 1)
    (hnoleak : ∀ v ∈ (runMoves δ (runTraceMoves r ms_pre)).2, v.kind ≠ .leak)
    {j : Nat} {m : Move} (hj : δ[j]? = some m)
    (hpos : 1 ≤ callCount (m.vis (runMoves (δ.take j) (runTraceMoves r ms_pre)).1)) :
    (runMoves δ (runTraceMoves r ms_pre)).2 = m.vis (runMoves (δ.take j) (runTraceMoves r ms_pre)).1 := by
  set tr_pre := runTraceMoves r ms_pre
  have hmem_only : ∀ v ∈ (runMoves δ tr_pre).2,
      ∀ j' m', δ[j']? = some m' → v ∈ m'.vis (runMoves (δ.take j') tr_pre).1 → j' = j := by
    intro v hv j' m' hj' hv'
    obtain ⟨hs', ha'⟩ := delta_move_anchored hrun hj'
    have hpos' : 1 ≤ callCount (m'.vis (runMoves (δ.take j') tr_pre).1) :=
      callCount_pos_of_nonLeak_mem_vis hs' ha' hv' (hnoleak v hv)
    rcases Nat.lt_trichotomy j' j with hlt | rfl | hgt
    · have := callCount_two_lt_le tr_pre hlt hj' hj; omega
    · rfl
    · have := callCount_two_lt_le tr_pre hgt hj hj'; omega
  have hdecomp := runMoves_decomp_at hj (tr := tr_pre)
  dsimp only at hdecomp
  have hL1 : (runMoves (δ.take j) tr_pre).2 = [] := by
    cases h1 : (runMoves (δ.take j) tr_pre).2 with
    | nil => rfl
    | cons v vs =>
      exfalso
      have hv_take : v ∈ (runMoves (δ.take j) tr_pre).2 := by rw [h1]; exact .head _
      obtain ⟨j', m', hj'_take, hv'⟩ := mem_runMoves_iff.mp hv_take
      have hj'_lt : j' < (δ.take j).length := (List.getElem?_eq_some_iff.mp hj'_take).1
      have hj'_lt_j : j' < j := Nat.lt_of_lt_of_le hj'_lt (List.length_take_le j δ)
      have hj' : δ[j']? = some m' := by rwa [List.getElem?_take_of_lt hj'_lt_j] at hj'_take
      have htake_eq : (δ.take j).take j' = δ.take j' :=
        List.take_take ▸ congrArg (fun n => δ.take n) (Nat.min_eq_left (Nat.le_of_lt hj'_lt_j))
      rw [htake_eq] at hv'
      have hv_all : v ∈ (runMoves δ tr_pre).2 := by
        rw [hdecomp, h1]; simp
      have heq := hmem_only v hv_all j' m' hj' hv'
      omega
  have hL2 : (runMoves (δ.drop (j + 1)) (m.next (runMoves (δ.take j) tr_pre).1)).2 = [] := by
    cases h2 : (runMoves (δ.drop (j + 1)) (m.next (runMoves (δ.take j) tr_pre).1)).2 with
    | nil => rfl
    | cons v vs =>
      exfalso
      have hv_drop : v ∈ (runMoves (δ.drop (j + 1)) (m.next (runMoves (δ.take j) tr_pre).1)).2 := by
        rw [h2]; exact .head _
      obtain ⟨d, m', hd_drop, hv'⟩ := mem_runMoves_iff.mp hv_drop
      have hj' : δ[j + 1 + d]? = some m' := by rwa [List.getElem?_drop] at hd_drop
      have hlt_j : j < δ.length := (List.getElem?_eq_some_iff.mp hj).1
      have hdrop_j : δ.drop j = m :: δ.drop (j + 1) := by
        rw [← List.cons_getElem_drop_succ (h := hlt_j)]
        rw [List.getElem?_eq_getElem hlt_j, Option.some.injEq] at hj
        rw [hj]
      have htake_d : δ.take (j + 1 + d) = δ.take j ++ (m :: (δ.drop (j + 1)).take d) := by
        conv_lhs => rw [← List.take_append_drop j δ, hdrop_j]
        rw [List.take_append, List.take_of_length_le (by simp; omega)]
        simp only [List.length_take, Nat.min_eq_left (Nat.le_of_lt hlt_j)]
        have hsub : j + 1 + d - j = d + 1 := by omega
        rw [hsub, List.take_succ_cons]
      have htr_d : (runMoves ((δ.drop (j + 1)).take d) (m.next (runMoves (δ.take j) tr_pre).1)).1 =
          (runMoves (δ.take (j + 1 + d)) tr_pre).1 := by
        rw [htake_d, Symbolic.Swarm.CREF.TR.runMoves_append, runMoves_cons_fst]
      rw [htr_d] at hv'
      have hv_all : v ∈ (runMoves δ tr_pre).2 := by
        rw [hdecomp, h2]; simp
      have heq := hmem_only v hv_all (j + 1 + d) m' hj' hv'
      omega
  rw [hdecomp, hL1, hL2, List.nil_append, List.append_nil]

/-! ## 34-draw `session_initiate` shape -/

private theorem init34_aliceStart_shape {interp : ExternInterpretation} {r : ProtocolSetup} {S : OpaqueSymbolSemantics}
    {ok : Nat → Bool} {g₁ : Ghost} {ms_all : List Move} {i : Nat} {m : Move} {tr : ExecTrace}
    {blob : HwBytes} {ds : List HwBytes}
    (hi : ms_all[i]? = some m)
    (htr : tr = runTraceMoves r (ms_all.take i))
    (hof : OutcomeFaithful r ok ms_all)
    (hok : ok (callCount (runVis r (ms_all.take i))) = true)
    (hds_len : ds.length = 34)
    (hF_m : List.Forall₂ (EventMatchesEntry interp r S g₁)
      (.recv blob :: ds.map MachineEvent.rng) (m.vis tr)) :
    (eventIdx isAliceDone tr (m.next tr)).isSome = true ∧
      ∃ (bh : _root_.DY.Libsignal.PQXDH.BundleHandles), m.vis tr =
        (⟨.recv, received tr ([bh.spk, bh.spkSig, bh.pqpk, bh.pqpkSig] ++ bh.opk.toList),
            .bundle, none⟩ : VisEntry) ::
          (rngEntry (randTerm tr.length 32) :: kyberCoinEntries (randTerm (tr.length + 1) 32) ++
            [{ rngEntry (randTerm (tr.length + 2) 32) with anchor := some (tr.length + 5) }]) := by
  have hlen_vis : (m.vis tr).length = 35 := by
    have := hF_m.length_eq.symm
    simpa [hds_len] using this
  obtain ⟨v₀, hv₀, hm₀⟩ := forall2_mem_left hF_m (.head _)
  have hrk := Symbolic.Swarm.CREF.xpl_recvHeadKind m tr hv₀ hm₀.1.symm
  cases m with
  | reject draws =>
    have hfalse := (hof i (.reject draws) hi).1 draws rfl
    rw [hok] at hfalse; cases hfalse
  | bobStart b a kh r' mh pq sp sh =>
    have := Symbolic.Swarm.CREF.CliPure.IniPure.vis_length_le_three_of_bob_or_dec tr
      (.bobStart b a kh r' mh pq sp sh) (Or.inl ⟨b, a, kh, r', mh, pq, sp, sh, rfl⟩)
    omega
  | decrypt me si mi pq sp w =>
    have := Symbolic.Swarm.CREF.CliPure.IniPure.vis_length_le_three_of_bob_or_dec tr
      (.decrypt me si mi pq sp w) (Or.inr (Or.inl ⟨me, si, mi, pq, sp, w, rfl⟩))
    omega
  | decryptSkipped me si mi k pq sp w =>
    have := Symbolic.Swarm.CREF.CliPure.IniPure.vis_length_le_three_of_bob_or_dec tr
      (.decryptSkipped me si mi k pq sp w) (Or.inr (Or.inr ⟨me, si, mi, k, pq, sp, w, rfl⟩))
    omega
  | aliceStart a b idIdx regIdx bh shown =>
    have _ := htr
    have hexp : exposures tr ((Move.aliceStart a b idIdx regIdx bh shown).next tr) = [] :=
      Symbolic.Swarm.CREF.exposures_nil_of_not_leakKind rfl (fun hc => nomatch hc)
    let Inv : ExecTrace → Prop := fun t =>
      t = tr ∨ t = tr.append (Symbolic.Swarm.COMPOSED.CompTrace.RndE 32) ∨
        ∃ o, t = Symbolic.Swarm.CREF.iniAliceStartTr tr a b o
    have hInv : Inv ((Move.aliceStart a b idIdx regIdx bh shown).next tr) := by
      change Inv (((aliceStart a b idIdx regIdx bh >>= fun _ => Pure.pure ()).run tr).2.val)
      simp (config := { zeta := false, beta := false, eta := false, proj := false, iota := false, failIfUnchanged := false }) only [DY.Libsignal.Composed.aliceStart_eq_inline]
      rw [Symbolic.Swarm.COMPOSED.CompTrace.run_bind_assoc_snd]
      apply Symbolic.Swarm.COMPOSED.CompTrace.bind_aliceHandshake_at a b idIdx regIdx bh tr
        (Or.inl rfl) (Or.inr (Or.inl rfl))
      intro ikA ikB _ spk _ pqpk _ opk _ _ _ _ _ _ _ _ _ _ _ _
      let o := Symbolic.Swarm.COMPOSED.CompTrace.aliceOut tr ikA ikB spk pqpk opk
      let tr2 := (tr.append (Symbolic.Swarm.COMPOSED.CompTrace.RndE 32)).append
        (Symbolic.Swarm.COMPOSED.CompTrace.RndE 32)
      have hg := Symbolic.Swarm.CREF.Runs.genRand tr2 32
      have hlen2 : tr2.length = tr.length + 2 := by
        simp only [tr2, Symbolic.DYBridge.DY.Trace.append_eq_1, Symbolic.DYBridge.DY.Trace.length_eq_2]
      rw [hlen2] at hg
      let tr5 := (((((tr.append (Symbolic.Swarm.CREF.ini_RndE 32)).append
        (Symbolic.Swarm.CREF.ini_RndE 32)).append (Symbolic.Swarm.CREF.ini_RndE 32)).append
        (Symbolic.Swarm.CREF.ini_NetE o.ek)).append (Symbolic.Swarm.CREF.ini_NetE o.ct))
      have ht := Symbolic.Swarm.CREF.Runs.ini_traceLength tr5
      have hlen5 : tr5.length = tr.length + 5 := by
        simp only [tr5, Symbolic.DYBridge.DY.Trace.append_eq_1, Symbolic.DYBridge.DY.Trace.length_eq_2]
      rw [hlen5] at ht
      refine Or.inr (Or.inr ⟨o, ?_⟩)
      refine (Symbolic.Swarm.CREF.Runs.bind (a := ?_) (f := fun _ => Pure.pure ()) ?_
        (Symbolic.Swarm.CREF.Runs.pure () _)).2
      rotate_left
      refine Symbolic.Swarm.CREF.Runs.bind hg ?_
      dsimp only
      refine Symbolic.Swarm.CREF.Runs.bind (Symbolic.Swarm.CREF.Runs.sendMessage _ _) ?_
      refine Symbolic.Swarm.CREF.Runs.bind (Symbolic.Swarm.CREF.Runs.sendMessage _ _) ?_
      refine Symbolic.Swarm.CREF.Runs.bind ht ?_
      refine Symbolic.Swarm.CREF.Runs.bind (Symbolic.Swarm.CREF.Runs.logPQEvent _ _) ?_
      refine Symbolic.Swarm.CREF.Runs.bind (Symbolic.Swarm.CREF.Runs.logTREvent _ _) ?_
      refine Symbolic.Swarm.CREF.Runs.bind (Symbolic.Swarm.CREF.Runs.logCEvent _ _) ?_
      exact Symbolic.Swarm.CREF.Runs.storeTRState _ _ _
    rcases hInv with h0 | h1 | ⟨o, ho⟩
    · dsimp only [Move.vis] at hlen_vis
      rw [hexp, List.append_nil, h0] at hlen_vis
      have hle1 : ((aliceVis tr tr bh).take shown).length ≤ (aliceVis tr tr bh).length := by
        simp only [List.length_take]; exact Nat.min_le_right _ _
      have hvis0 : (aliceVis tr tr bh).length = 1 := by
        simp [aliceVis, aliceDraws, newRandoms, newIndices]
      omega
    · dsimp only [Move.vis] at hlen_vis
      rw [hexp, List.append_nil, h1] at hlen_vis
      have hlen1 : (tr.append (Symbolic.Swarm.COMPOSED.CompTrace.RndE 32)).length =
          tr.length + 1 := by
        simp only [Symbolic.DYBridge.DY.Trace.append_eq_1, Symbolic.DYBridge.DY.Trace.length_eq_2]
      have hnr_le : (newRandoms tr
          (tr.append (Symbolic.Swarm.COMPOSED.CompTrace.RndE 32))).length ≤ 1 := by
        unfold newRandoms newIndices
        rw [hlen1, Nat.add_sub_cancel_left]
        exact Nat.le_trans (List.length_filterMap_le _ _) (by simp)
      have had_le : (aliceDraws
          (eventIdx isAliceDone tr (tr.append (Symbolic.Swarm.COMPOSED.CompTrace.RndE 32)))
          ((newRandoms tr (tr.append (Symbolic.Swarm.COMPOSED.CompTrace.RndE 32))).map
            (·.1))).length ≤ 1 := by
        rcases hL : (newRandoms tr
            (tr.append (Symbolic.Swarm.COMPOSED.CompTrace.RndE 32))).map (·.1) with
          _ | ⟨x0, _ | ⟨x1, xs⟩⟩
        · rw [hL]; simp [aliceDraws]
        · rw [hL]; simp [aliceDraws]
        · have hlenL := congrArg List.length hL
          simp only [List.length_map, List.length_cons] at hlenL
          omega
      have hle2 : ((aliceVis tr
          (tr.append (Symbolic.Swarm.COMPOSED.CompTrace.RndE 32)) bh).take shown).length ≤ 2 := by
        have htake_le : ((aliceVis tr
            (tr.append (Symbolic.Swarm.COMPOSED.CompTrace.RndE 32)) bh).take shown).length ≤
            (aliceVis tr (tr.append (Symbolic.Swarm.COMPOSED.CompTrace.RndE 32)) bh).length := by
          simp only [List.length_take]; exact Nat.min_le_right _ _
        refine Nat.le_trans htake_le ?_
        unfold aliceVis
        simp only [List.length_cons]
        omega
      omega
    · have hdone_eq :
          eventIdx isAliceDone tr ((Move.aliceStart a b idIdx regIdx bh shown).next tr) =
            some (tr.length + 5) := by
        rw [ho]; exact Symbolic.Swarm.CREF.eventIdx_isAliceDone_iniAliceStartTr tr a b o
      have hshown : 35 ≤ shown := by
        dsimp only [Move.vis] at hlen_vis
        rw [hexp, List.append_nil, List.length_take] at hlen_vis
        omega
      have hvis_len :=
        Symbolic.Swarm.CREF.CliPure.IniPure.ini_aliceVis_length_le_35 tr
          ((Move.aliceStart a b idIdx regIdx bh shown).next tr) bh
      refine ⟨by rw [hdone_eq]; rfl, bh, ?_⟩
      dsimp only [Move.vis]
      rw [hexp, List.append_nil, List.take_of_length_le (Nat.le_trans hvis_len hshown)]
      unfold aliceVis
      rw [ho, Symbolic.Swarm.CREF.newRandoms_iniAliceStartTr,
        Symbolic.Swarm.CREF.eventIdx_isAliceDone_iniAliceStartTr]
      rfl
  | _ => exact False.elim hrk

/-! ## `GoodExit0CutSpec` proof -/

/-- Lifts `Clean` on `τ_pre ++ blk_hw` to `ExplainsCli` on `σ_pre ++ blk_cli` across a single
`GoodStepCut` block. -/
theorem outcomeFaithfulCli_of_goodExit0Cut : GoodExit0CutSpec := by
  intro interp r S who ok σ_pre τ_pre blk_cli blk_hw g₀ g₁ ms₀ ms_pre δ
    hex₀ hsplit_blk hcut hms_pre hg_eq hclean
  obtain ⟨hsplit₀, hmp₀, ⟨_, hof_cli₀⟩, hrng₀⟩ := hex₀
  have hF₀ : List.Forall₂ (EventMatchesEntry interp r S g₀) τ_pre (runVis r ms₀) :=
    hmp₀.2.2.2.2.2
  obtain ⟨⟨hmp₁, hof₁⟩, hnrc₁⟩ := hclean
  have hrun₁ : ModelRun r (ms_pre ++ δ) := hmp₁.2.1
  have hF_all : List.Forall₂ (EventMatchesEntry interp r S g₁)
      (τ_pre ++ blk_hw) (runVis r (ms_pre ++ δ)) := hmp₁.2.2.2.2.2
  have hvis_pre_eq : runVis r ms_pre = runVis r ms₀ := by
    rcases hms_pre with rfl | rfl
    · rfl
    · exact Symbolic.Swarm.CREF.Sanitize.runVis_sanitizeMoves r ms₀
  have hlen_pre : τ_pre.length = (runVis r ms_pre).length := by
    rw [hvis_pre_eq]; exact hF₀.length_eq
  obtain ⟨hF_pre, hF_blk⟩ : List.Forall₂ (EventMatchesEntry interp r S g₁) τ_pre (runVis r ms_pre) ∧
      List.Forall₂ (EventMatchesEntry interp r S g₁) blk_hw (runMoves δ (runTraceMoves r ms_pre)).2 := by
    rw [runVis_append] at hF_all
    exact forall2_append_split hlen_pre hF_all
  refine ⟨⟨Symbolic.Swarm.CREF.CliPure.coinSplit_append hsplit₀ hsplit_blk, hmp₁,
    ⟨hof₁, ?_⟩, ?_⟩, hnrc₁⟩
  ·
    intro i m hi
    dsimp only
    intro hv_any hok
    by_cases hi_lt : i < ms_pre.length
    · have hmi_pre : ms_pre[i]? = some m := by
        rwa [List.getElem?_append_left hi_lt] at hi
      have htake_eq : (ms_pre ++ δ).take i = ms_pre.take i :=
        List.take_append_of_le_length (Nat.le_of_lt hi_lt)
      obtain ⟨m₀, hm₀, htr_eq, hvis_eq, hm_vis, hm_next⟩ :=
        prefix_move_reduce hms_pre hmi_pre
      rw [htake_eq, htr_eq, hm_vis] at hv_any ⊢
      rw [hm_next]
      rw [htake_eq, hvis_eq] at hok
      exact hof_cli₀ i m₀ hm₀ hv_any hok
    · have hi_ge : ms_pre.length ≤ i := Nat.le_of_not_lt hi_lt
      set j := i - ms_pre.length
      have hij : i = ms_pre.length + j := (Nat.add_sub_of_le hi_ge).symm
      have hj : δ[j]? = some m := by
        rwa [List.getElem?_append_right hi_ge] at hi
      have htake_eq : (ms_pre ++ δ).take i = ms_pre ++ δ.take j := by
        rw [hij, List.take_append, List.take_of_length_le (Nat.le_add_right _ _),
          Nat.add_sub_cancel_left]
      have htr_j : runTraceMoves r ((ms_pre ++ δ).take i) =
          (runMoves (δ.take j) (runTraceMoves r ms_pre)).1 := by
        rw [htake_eq, runTrace_append]
      rw [htr_j] at hv_any
      have hpos : 1 ≤ callCount (m.vis (runMoves (δ.take j) (runTraceMoves r ms_pre)).1) :=
        callCount_pos_of_any hv_any
      cases hcut with
      | leaks hleaks =>
        exfalso
        obtain ⟨v, hv, hk⟩ := List.any_eq_true.mp hv_any
        have hv_all : v ∈ (runMoves δ (runTraceMoves r ms_pre)).2 :=
          mem_runMoves_iff.mpr ⟨j, m, hj, hv⟩
        obtain ⟨e, he, hme⟩ := forall2_mem_right hF_blk hv_all
        obtain ⟨x, rfl⟩ := hleaks e he
        have hvk : v.kind = .leak := hme.1.symm
        rw [hvk] at hk; cases hk
      | callRecvFail hok_false =>
        exfalso
        have hcc1 : callCount (runMoves δ (runTraceMoves r ms_pre)).2 = 1 := by
          rw [callCount_eq_callStarts_length_of_forall2 hF_blk]
          exact callStarts_cons_recv_length (fun _ he => nomatch he)
        have hcc_i := suffix_callCount_eq_of_one_call hF_pre hcc1 hj hpos
        rw [htake_eq, hcc_i, hok_false] at hok; cases hok
      | callSendFail hmid hok_false =>
        exfalso
        have hcc1 : callCount (runMoves δ (runTraceMoves r ms_pre)).2 = 1 := by
          rw [callCount_eq_callStarts_length_of_forall2 hF_blk]
          exact callStarts_cons_pt_length hmid
        have hcc_i := suffix_callCount_eq_of_one_call hF_pre hcc1 hj hpos
        rw [htake_eq, hcc_i, hok_false] at hok; cases hok
      | @callSendOk pt mid out_ev hmid hout _ =>
        have hmid_out : ∀ ev ∈ mid ++ [out_ev], eventKind ev ≠ .recv ∧ eventKind ev ≠ .pt := by
          intro ev hev
          rcases List.mem_append.mp hev with hm | ho
          · exact hmid ev hm
          · rcases List.mem_singleton.mp ho with rfl
            rw [hout]; decide
        have hcc1 : callCount (runMoves δ (runTraceMoves r ms_pre)).2 = 1 := by
          rw [callCount_eq_callStarts_length_of_forall2 hF_blk]
          exact callStarts_cons_pt_length hmid_out
        have hout_mem : out_ev ∈ (.pt pt :: mid) ++ [out_ev] :=
          List.mem_append_right _ (.head _)
        obtain ⟨v_out, hv_out_all, hm_out⟩ := forall2_mem_left hF_blk hout_mem
        have hv_out_kind : v_out.kind = .send := hm_out.1.symm.trans hout
        obtain ⟨j', m', hj', hv_out_m'⟩ := mem_runMoves_iff.mp hv_out_all
        obtain ⟨hs', ha'⟩ := delta_move_anchored hrun₁ hj'
        have hpos' : 1 ≤ callCount (m'.vis (runMoves (δ.take j') (runTraceMoves r ms_pre)).1) :=
          callCount_pos_of_nonLeak_mem_vis hs' ha' hv_out_m' (by rw [hv_out_kind]; decide)
        have hjj : j' = j := by
          rcases Nat.lt_trichotomy j' j with hlt | rfl | hgt
          · have := callCount_two_lt_le (runTraceMoves r ms_pre) hlt hj' hj; omega
          · rfl
          · have := callCount_two_lt_le (runTraceMoves r ms_pre) hgt hj hj'; omega
        subst hjj
        have hm_eq : m' = m := Option.some.inj (hj'.symm.trans hj)
        subst hm_eq
        rw [htr_j]
        exact Or.inl (List.any_eq_true.mpr ⟨v_out, hv_out_m', by rw [hv_out_kind]; rfl⟩)
      | @callRecvAccept w mid out_ev hmid hout _ =>
        have hmid_out : ∀ ev ∈ mid ++ [out_ev], eventKind ev ≠ .recv ∧ eventKind ev ≠ .pt := by
          intro ev hev
          rcases List.mem_append.mp hev with hm | ho
          · rcases hmid with rfl | ⟨coins, rfl, _⟩
            · cases hm
            · rcases List.mem_singleton.mp hm with rfl; exact ⟨nofun, nofun⟩
          · rcases List.mem_singleton.mp ho with rfl
            rw [hout]; exact ⟨nofun, nofun⟩
        have hcc1 : callCount (runMoves δ (runTraceMoves r ms_pre)).2 = 1 := by
          rw [callCount_eq_callStarts_length_of_forall2 hF_blk]
          exact callStarts_cons_recv_length hmid_out
        have hnoleak : ∀ v ∈ (runMoves δ (runTraceMoves r ms_pre)).2, v.kind ≠ .leak := by
          intro v hv
          obtain ⟨e, he, hme⟩ := forall2_mem_right hF_blk hv
          rw [← hme.1]
          rcases List.mem_append.mp he with he1 | he2
          · rcases List.mem_cons.mp he1 with rfl | hm
            · nofun
            · rcases hmid with rfl | ⟨coins, rfl, _⟩
              · cases hm
              · rcases List.mem_singleton.mp hm with rfl; nofun
          · rcases List.mem_singleton.mp he2 with rfl
            rw [hout]; nofun
        have hvis_eq := runMoves_eq_vis_of_one_call_no_leak hrun₁ hcc1 hnoleak hj hpos
        have hF_m : List.Forall₂ (EventMatchesEntry interp r S g₁)
            ((.recv w :: mid) ++ [out_ev]) (m.vis (runMoves (δ.take j) (runTraceMoves r ms_pre)).1) := by
          rwa [← hvis_eq]
        have hout_mem : out_ev ∈ (.recv w :: mid) ++ [out_ev] :=
          List.mem_append_right _ (.head _)
        obtain ⟨v_out, hv_out, hm_out⟩ := forall2_mem_left hF_m hout_mem
        have hv_out_kind : v_out.kind = .accept := hm_out.1.symm.trans hout
        rw [htr_j]
        exact Or.inl (List.any_eq_true.mpr ⟨v_out, hv_out, by rw [hv_out_kind]; rfl⟩)
      | @callInit34 blob ds hds_len _ _ _ =>
        have hds_norp : ∀ ev ∈ ds.map MachineEvent.rng,
            eventKind ev ≠ .recv ∧ eventKind ev ≠ .pt := by
          intro ev hev
          obtain ⟨_, _, rfl⟩ := List.mem_map.mp hev
          exact ⟨nofun, nofun⟩
        have hcc1 : callCount (runMoves δ (runTraceMoves r ms_pre)).2 = 1 := by
          rw [callCount_eq_callStarts_length_of_forall2 hF_blk]
          exact callStarts_cons_recv_length hds_norp
        have hnoleak : ∀ v ∈ (runMoves δ (runTraceMoves r ms_pre)).2, v.kind ≠ .leak := by
          intro v hv
          obtain ⟨e, he, hme⟩ := forall2_mem_right hF_blk hv
          rw [← hme.1]
          rcases List.mem_cons.mp he with rfl | hd
          · nofun
          · obtain ⟨_, _, rfl⟩ := List.mem_map.mp hd; nofun
        have hvis_eq := runMoves_eq_vis_of_one_call_no_leak hrun₁ hcc1 hnoleak hj hpos
        have hF_m : List.Forall₂ (EventMatchesEntry interp r S g₁)
            (.recv blob :: ds.map MachineEvent.rng)
            (m.vis (runMoves (δ.take j) (runTraceMoves r ms_pre)).1) := by
          rwa [← hvis_eq]
        rw [← htr_j] at hF_m
        exact Or.inr (init34_aliceStart_shape hi rfl hof₁ hok hds_len hF_m).1
  ·
    unfold RngLengthsFaithfulCli
    intro i m hi
    dsimp only
    intro hv_recv v t hv hk hl ht
    by_cases hi_lt : i < ms_pre.length
    · have hmi_pre : ms_pre[i]? = some m := by
        rwa [List.getElem?_append_left hi_lt] at hi
      have htake_eq : (ms_pre ++ δ).take i = ms_pre.take i :=
        List.take_append_of_le_length (Nat.le_of_lt hi_lt)
      obtain ⟨m₀, hm₀, htr_eq, _, hm_vis, _⟩ := prefix_move_reduce hms_pre hmi_pre
      rw [htake_eq, htr_eq, hm_vis] at hv_recv hv
      have hlen₀ := hrng₀ i m₀ hm₀ hv_recv v t hv hk hl ht
      obtain ⟨ts, sz, hts_lt, rfl⟩ := single_rng_mem_vis_randTerm_lt hv hk hl ht
      have hts_all : ts < (runTraceMoves r ms₀).length :=
        Nat.lt_of_lt_of_le hts_lt (runTrace_next_take_le hm₀)
      rw [gamma_randTerm_congr (hg_eq ts hts_all sz)]
      exact hlen₀
    · have hi_ge : ms_pre.length ≤ i := Nat.le_of_not_lt hi_lt
      set j := i - ms_pre.length
      have hij : i = ms_pre.length + j := (Nat.add_sub_of_le hi_ge).symm
      have hj : δ[j]? = some m := by
        rwa [List.getElem?_append_right hi_ge] at hi
      have htake_eq : (ms_pre ++ δ).take i = ms_pre ++ δ.take j := by
        rw [hij, List.take_append, List.take_of_length_le (Nat.le_add_right _ _),
          Nat.add_sub_cancel_left]
      have htr_j : runTraceMoves r ((ms_pre ++ δ).take i) =
          (runMoves (δ.take j) (runTraceMoves r ms_pre)).1 := by
        rw [htake_eq, runTrace_append]
      rw [htr_j] at hv_recv hv
      have hpos : 1 ≤ callCount (m.vis (runMoves (δ.take j) (runTraceMoves r ms_pre)).1) :=
        callCount_pos_of_any_recv hv_recv
      cases hcut with
      | leaks hleaks =>
        exfalso
        have hv_all : v ∈ (runMoves δ (runTraceMoves r ms_pre)).2 :=
          mem_runMoves_iff.mpr ⟨j, m, hj, hv⟩
        obtain ⟨e, he, hme⟩ := forall2_mem_right hF_blk hv_all
        obtain ⟨x, rfl⟩ := hleaks e he
        have hvk : v.kind = .leak := hme.1.symm
        rw [hk] at hvk; cases hvk
      | callRecvFail _ =>
        exfalso
        have hv_all : v ∈ (runMoves δ (runTraceMoves r ms_pre)).2 :=
          mem_runMoves_iff.mpr ⟨j, m, hj, hv⟩
        obtain ⟨e, he, hme⟩ := forall2_mem_right hF_blk hv_all
        rcases List.mem_singleton.mp he with rfl
        have hvk : v.kind = .recv := hme.1.symm
        rw [hk] at hvk; cases hvk
      | callSendFail hmid _ =>
        exfalso
        obtain ⟨v₀, hv₀, hk₀⟩ := List.any_eq_true.mp hv_recv
        have hv₀_all : v₀ ∈ (runMoves δ (runTraceMoves r ms_pre)).2 :=
          mem_runMoves_iff.mpr ⟨j, m, hj, hv₀⟩
        obtain ⟨e, he, hme⟩ := forall2_mem_right hF_blk hv₀_all
        have hek : eventKind e = .recv := hme.1.trans (beq_iff_eq.mp hk₀)
        rcases List.mem_cons.mp he with rfl | hm
        · cases hek
        · exact (hmid e hm).1 hek
      | callSendOk hmid hout _ =>
        exfalso
        obtain ⟨v₀, hv₀, hk₀⟩ := List.any_eq_true.mp hv_recv
        have hv₀_all : v₀ ∈ (runMoves δ (runTraceMoves r ms_pre)).2 :=
          mem_runMoves_iff.mpr ⟨j, m, hj, hv₀⟩
        obtain ⟨e, he, hme⟩ := forall2_mem_right hF_blk hv₀_all
        have hek : eventKind e = .recv := hme.1.trans (beq_iff_eq.mp hk₀)
        rcases List.mem_append.mp he with he1 | he2
        · rcases List.mem_cons.mp he1 with rfl | hm
          · cases hek
          · exact (hmid e hm).1 hek
        · rcases List.mem_singleton.mp he2 with rfl
          rw [hout] at hek; cases hek
      | @callRecvAccept w mid out_ev hmid hout _ =>
        have hmid_out : ∀ ev ∈ mid ++ [out_ev], eventKind ev ≠ .recv ∧ eventKind ev ≠ .pt := by
          intro ev hev
          rcases List.mem_append.mp hev with hm | ho
          · rcases hmid with rfl | ⟨coins, rfl, _⟩
            · cases hm
            · rcases List.mem_singleton.mp hm with rfl; exact ⟨nofun, nofun⟩
          · rcases List.mem_singleton.mp ho with rfl
            rw [hout]; exact ⟨nofun, nofun⟩
        have hcc1 : callCount (runMoves δ (runTraceMoves r ms_pre)).2 = 1 := by
          rw [callCount_eq_callStarts_length_of_forall2 hF_blk]
          exact callStarts_cons_recv_length hmid_out
        have hnoleak : ∀ v' ∈ (runMoves δ (runTraceMoves r ms_pre)).2, v'.kind ≠ .leak := by
          intro v' hv'
          obtain ⟨e, he, hme⟩ := forall2_mem_right hF_blk hv'
          rw [← hme.1]
          rcases List.mem_append.mp he with he1 | he2
          · rcases List.mem_cons.mp he1 with rfl | hm
            · nofun
            · rcases hmid with rfl | ⟨coins, rfl, _⟩
              · cases hm
              · rcases List.mem_singleton.mp hm with rfl; nofun
          · rcases List.mem_singleton.mp he2 with rfl
            rw [hout]; nofun
        have hvis_eq := runMoves_eq_vis_of_one_call_no_leak hrun₁ hcc1 hnoleak hj hpos
        have hF_m : List.Forall₂ (EventMatchesEntry interp r S g₁)
            ((.recv w :: mid) ++ [out_ev]) (m.vis (runMoves (δ.take j) (runTraceMoves r ms_pre)).1) := by
          rwa [← hvis_eq]
        obtain ⟨e, he, hme⟩ := forall2_mem_right hF_m hv
        have hek : eventKind e = .rng := hme.1.trans hk
        rcases List.mem_append.mp he with he1 | he2
        · rcases List.mem_cons.mp he1 with rfl | hm
          · cases hek
          · rcases hmid with rfl | ⟨coins, rfl, hclen⟩
            · cases hm
            · rcases List.mem_singleton.mp hm with rfl
              rw [gamma_length_of_rng_single_match hme hl ht]
              exact hclen
        · rcases List.mem_singleton.mp he2 with rfl
          rw [hout] at hek; cases hek
      | @callInit34 blob ds hds_len hds0 hds33 hok_true =>
        have hds_norp : ∀ ev ∈ ds.map MachineEvent.rng,
            eventKind ev ≠ .recv ∧ eventKind ev ≠ .pt := by
          intro ev hev
          obtain ⟨_, _, rfl⟩ := List.mem_map.mp hev
          exact ⟨nofun, nofun⟩
        have hcc1 : callCount (runMoves δ (runTraceMoves r ms_pre)).2 = 1 := by
          rw [callCount_eq_callStarts_length_of_forall2 hF_blk]
          exact callStarts_cons_recv_length hds_norp
        have hnoleak : ∀ v' ∈ (runMoves δ (runTraceMoves r ms_pre)).2, v'.kind ≠ .leak := by
          intro v' hv'
          obtain ⟨e, he, hme⟩ := forall2_mem_right hF_blk hv'
          rw [← hme.1]
          rcases List.mem_cons.mp he with rfl | hd
          · nofun
          · obtain ⟨_, _, rfl⟩ := List.mem_map.mp hd; nofun
        have hvis_eq := runMoves_eq_vis_of_one_call_no_leak hrun₁ hcc1 hnoleak hj hpos
        have hF_m : List.Forall₂ (EventMatchesEntry interp r S g₁)
            (.recv blob :: ds.map MachineEvent.rng)
            (m.vis (runMoves (δ.take j) (runTraceMoves r ms_pre)).1) := by
          rwa [← hvis_eq]
        have hcc_i := suffix_callCount_eq_of_one_call hF_pre hcc1 hj hpos
        have hok_i : ok (callCount (runVis r ((ms_pre ++ δ).take i))) = true := by
          rw [htake_eq, hcc_i]; exact hok_true
        have hF_m' : List.Forall₂ (EventMatchesEntry interp r S g₁)
            (.recv blob :: ds.map MachineEvent.rng)
            (m.vis (runTraceMoves r ((ms_pre ++ δ).take i))) := by
          rwa [htr_j]
        obtain ⟨_, bh, hvis_m⟩ := init34_aliceStart_shape hi rfl hof₁ hok_i hds_len hF_m'
        rw [htr_j] at hvis_m
        set tr_j := (runMoves (δ.take j) (runTraceMoves r ms_pre)).1
        rw [hvis_m] at hv
        rcases List.mem_cons.mp hv with rfl | hv_draws
        · cases hk
        · rcases List.mem_append.mp hv_draws with hv_left | hv_right
          · rcases List.mem_cons.mp hv_left with rfl | hkc
            · simp only [rngEntry, List.cons.injEq, and_true] at ht; subst ht
              obtain ⟨d0, hd0, hd0_len⟩ := Option.map_eq_some_iff.mp hds0
              have he1 : (.recv blob :: ds.map MachineEvent.rng)[1]? = some (.rng d0) := by
                simp [hd0]
              have hv1 : (m.vis tr_j)[1]? = some (rngEntry (randTerm tr_j.length 32)) := by
                rw [hvis_m]; rfl
              have hme1 := forall2_getElem? hF_m he1 hv1
              rw [gamma_length_of_rng_single_match hme1 rfl rfl]
              exact hd0_len
            · unfold kyberCoinEntries at hkc
              obtain ⟨_, _, rfl⟩ := List.mem_map.mp hkc
              cases hl
          · rcases List.mem_singleton.mp hv_right with rfl
            simp only [rngEntry, List.cons.injEq, and_true] at ht; subst ht
            obtain ⟨d33, hd33, hd33_len⟩ := Option.map_eq_some_iff.mp hds33
            have he34 : (.recv blob :: ds.map MachineEvent.rng)[34]? = some (.rng d33) := by
              simp [hd33]
            have hv34 : (m.vis tr_j)[34]? =
                some { rngEntry (randTerm (tr_j.length + 2) 32) with
                  anchor := some (tr_j.length + 5) } := by
              rw [hvis_m]
              change ((_ :: (rngEntry (randTerm tr_j.length 32) ::
                  kyberCoinEntries (randTerm (tr_j.length + 1) 32))) ++
                [{ rngEntry (randTerm (tr_j.length + 2) 32) with
                    anchor := some (tr_j.length + 5) }])[34]? = _
              have hlen34 :
                  ((⟨.recv, received tr_j ([bh.spk, bh.spkSig, bh.pqpk, bh.pqpkSig] ++
                      bh.opk.toList), .bundle, none⟩ : VisEntry) ::
                    rngEntry (randTerm tr_j.length 32) ::
                    kyberCoinEntries (randTerm (tr_j.length + 1) 32)).length = 34 := by
                simp [kyberCoinEntries]
              rw [List.getElem?_append_right (by rw [hlen34]), hlen34]
              rfl
            have hme34 := forall2_getElem? hF_m he34 hv34
            rw [gamma_length_of_rng_single_match hme34 rfl rfl]
            exact hd33_len

end Symbolic.Swarm.Coinsplit.Lift.L02
