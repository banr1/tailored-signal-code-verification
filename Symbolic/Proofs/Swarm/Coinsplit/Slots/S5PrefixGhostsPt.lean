/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Symbolic.Proofs.Refinement.Composed.Cli.OldShape
import DY.Bytes.Basic
import DY.ALaCarte.Basic
import DY.Trace.Basic
import DY.Trace.Monad
import DY.Trace.Manipulation
import DY.Actions.Network
import DY.Actions.PersistentLocalState
import DY.Actions.PersistentGlobalState
import DY.Actions.ProtocolEvent
import DY.Actions.Random
import Symbolic.DYBridge.DY.Bytes.Basic
import Symbolic.DYBridge.DY.ALaCarte.Basic
import Symbolic.DYBridge.DY.Trace.Basic
import Symbolic.DYBridge.DY.Trace.Monad
import Symbolic.DYBridge.DY.Trace.Manipulation
import Symbolic.DYBridge.DY.Actions.Network
import Symbolic.DYBridge.DY.Actions.PersistentLocalState
import Symbolic.DYBridge.DY.Actions.PersistentGlobalState
import Symbolic.DYBridge.DY.Actions.ProtocolEvent
import Symbolic.DYBridge.DY.Actions.Random

/-!
# Coin-Cut Uniqueness for `PrefixExplainingGhostsMoves`

Proves that under `NoAdjRngS5 σ₁`, fixing a model run `ms` and random oracle `g'.σ = g.σ`
uniquely determines the explained coin cut `τ₁' = τ₁`, so `PrefixExplainingGhostsMoves` is a
subset of `PrefixGhosts`.
-/

@[expose] public section

set_option autoImplicit false

namespace Symbolic.Swarm.Coinsplit.S5

open CryptoProofLib.Refinement (ExternInterpretation)
open _root_.DY (Participant)
open _root_.DY.Libsignal (HwBytes)
open _root_.DY.Libsignal.HwEvents (MachineEvent)
open _root_.DY.Libsignal.Composed.Refinement
open _root_.DY.Libsignal.Composed.Refinement.Cli

/-- No two consecutive events in `σ` are `.rng` events. -/
def NoAdjRngS5 : List MachineEvent → Prop
  | [] => True
  | [_] => True
  | e₁ :: e₂ :: es => (eventKind e₁ ≠ .rng ∨ eventKind e₂ ≠ .rng) ∧ NoAdjRngS5 (e₂ :: es)

unseal _root_.DY.Bytes in
private instance (interpretation : ExternInterpretation) (S : OpaqueSymbolSemantics) (g : Ghost) :
    _root_.DY.Bytes.SubFunction (concretizeRandom g) (concretizeAll interpretation S g) :=
  @_root_.DY.Bytes.SubFunction.mk _ _ _ _ _ _ _ ⟨fun _ _ => by
    simp only [concretizeAll, allFuns, Symbolic.DYBridge.DY.Bytes.PartialFunction.combine_eq]; rfl⟩

private theorem gamma_randTerm_eq_of_sigma_eq {interp : ExternInterpretation} {S : OpaqueSymbolSemantics}
    {g g' : Ghost} (hσ : g'.σ = g.σ) (i n : Nat) :
    gamma interp S g' (randTerm i n) = gamma interp S g (randTerm i n) := by
  unfold gamma gamma' randTerm
  change ((({ timestamp := i, size := n } : _root_.DY.Random.Random _root_.DY.Bytes).pack).rec
    (concretizeAll interp S g')).bytes =
    ((({ timestamp := i, size := n } : _root_.DY.Random.Random _root_.DY.Bytes).pack).rec
    (concretizeAll interp S g)).bytes
  rw [_root_.DY.Bytes.rec_eq (concretizeRandom g') (concretizeAll interp S g'),
      _root_.DY.Bytes.rec_eq (concretizeRandom g) (concretizeAll interp S g)]
  simp [concretizeRandom, node, hσ]

private def RngEntryShape (v : VisEntry) : Prop :=
  v.kind = .rng →
    (∃ i n, v.layout = .single ∧ v.terms = [randTerm i n]) ∨
    (∃ j, v.layout = .kyberCoin j) ∨
    (∃ n, v.layout = .fresh n)

private theorem exists_randTerm_of_mem_newRandoms {tr tr' : _root_.DY.ExecTrace}
    {p : _root_.DY.Bytes × Nat} (hp : p ∈ newRandoms tr tr') :
    ∃ i n, p.1 = randTerm i n := by
  obtain ⟨i, _, hi⟩ := List.mem_filterMap.mp hp
  rw [Option.map_eq_some_iff] at hi
  obtain ⟨e, _, rfl⟩ := hi
  exact ⟨i, e.length, rfl⟩

private theorem rngEntryShape_of_mem_exposures {tr tr' : _root_.DY.ExecTrace}
    {v : VisEntry} (hv : v ∈ exposures tr tr') : RngEntryShape v := by
  intro hk
  rcases List.mem_append.mp hv with hpq | htr
  · obtain ⟨j, _, hj⟩ := List.mem_filterMap.mp hpq
    unfold pqExposureAt at hj
    split at hj <;> cases hj <;> cases hk
  · obtain ⟨j, _, hj⟩ := List.mem_filterMap.mp htr
    unfold trExposureAt at hj
    split at hj <;> cases hj <;> cases hk

private theorem rngEntryShape_of_mem_aliceDraws {done : Option Nat} {ts : List _root_.DY.Bytes}
    (hts : ∀ t ∈ ts, ∃ i n, t = randTerm i n) {v : VisEntry}
    (hv : v ∈ aliceDraws done ts) : RngEntryShape v := by
  intro _
  match ts with
  | [] => cases hv
  | [ek] =>
    rcases List.mem_singleton.mp hv with rfl
    obtain ⟨i, n, rfl⟩ := hts ek List.mem_cons_self
    exact Or.inl ⟨i, n, rfl, rfl⟩
  | ek :: entropy :: rest =>
    simp only [aliceDraws, List.cons_append, List.mem_cons, List.mem_append] at hv
    rcases hv with rfl | hkc | hdhs
    · obtain ⟨i, n, rfl⟩ := hts ek List.mem_cons_self
      exact Or.inl ⟨i, n, rfl, rfl⟩
    · obtain ⟨j, _, rfl⟩ := List.mem_map.mp hkc
      exact Or.inr (Or.inl ⟨j, rfl⟩)
    · obtain ⟨dhsA, hdhsA, rfl⟩ := List.mem_map.mp hdhs
      have hmem : dhsA ∈ ek :: entropy :: rest :=
        List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_of_mem_take hdhsA))
      obtain ⟨i, n, rfl⟩ := hts dhsA hmem
      exact Or.inl ⟨i, n, rfl, rfl⟩

private theorem rngEntryShape_of_mem_encVis {tr tr' : _root_.DY.ExecTrace}
    {wrap : Option (Nat × Nat)} {withSend : Bool} {v : VisEntry}
    (hv : v ∈ encVis tr tr' wrap withSend) : RngEntryShape v := by
  intro hk
  rcases List.mem_append.mp hv with hd | hs
  · cases hnr : newRandoms tr tr' with
    | nil => rw [hnr] at hd; cases hd
    | cons p rest =>
      rw [hnr, encDraws] at hd
      rcases List.mem_cons.mp hd with rfl | hrest
      · cases hk
      · obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hrest
        have hq_mem : q ∈ newRandoms tr tr' :=
          hnr ▸ List.mem_cons_of_mem _ (List.mem_of_mem_filter hq)
        obtain ⟨i, n, hq_eq⟩ := exists_randTerm_of_mem_newRandoms hq_mem
        exact Or.inl ⟨i, n, rfl, congrArg (· :: []) hq_eq⟩
  · cases withSend with
    | false => cases hs
    | true =>
      simp only [↓reduceIte, encSend] at hs
      cases hls : lastSent tr tr' with
      | none => rw [hls] at hs; cases hs
      | some w =>
        rw [hls] at hs
        cases wrap with
        | none => rcases List.mem_singleton.mp hs with rfl; cases hk
        | some ec => rcases List.mem_singleton.mp hs with rfl; cases hk

private theorem rngEntryShape_of_mem_decVis {tr tr' : _root_.DY.ExecTrace}
    {stateIdx msgIdx : Nat} {wrapped : Bool} {v : VisEntry}
    (hv : v ∈ decVis tr tr' stateIdx msgIdx wrapped) : RngEntryShape v := by
  intro hk
  unfold decVis at hv
  rcases List.mem_append.mp hv with h12 | h3
  · rcases List.mem_append.mp h12 with h1 | h2
    · cases hm : tr.getMessageSentAt msgIdx with
      | none => rw [hm] at h1; cases h1
      | some b => rw [hm] at h1; rcases List.mem_singleton.mp h1 with rfl; cases hk
    · obtain ⟨q, hq, rfl⟩ := List.mem_map.mp h2
      obtain ⟨i, n, hq_eq⟩ := exists_randTerm_of_mem_newRandoms hq
      exact Or.inl ⟨i, n, rfl, congrArg (· :: []) hq_eq⟩
  · cases hp : receivedPlaintext tr tr' with
    | none => rw [hp] at h3; cases h3
    | some m => rw [hp] at h3; rcases List.mem_singleton.mp h3 with rfl; cases hk

private theorem rngEntryShape_of_mem_moveVis {m : Move} {tr : _root_.DY.ExecTrace} {v : VisEntry}
    (hv : v ∈ m.vis tr) : RngEntryShape v := by
  unfold Move.vis at hv
  rcases List.mem_append.mp hv with hm | hexp
  · cases m with
    | aliceStart _ _ _ _ h shown =>
      have hm' := List.mem_of_mem_take hm
      unfold aliceVis at hm'
      rcases List.mem_cons.mp hm' with rfl | hdraws
      · exact fun hk => by cases hk
      · refine rngEntryShape_of_mem_aliceDraws (fun t ht => ?_) hdraws
        obtain ⟨p, hp, rfl⟩ := List.mem_map.mp ht
        exact exists_randTerm_of_mem_newRandoms hp
    | bobStart b _ kh _ mh _ _ shown =>
      intro hk
      have hm' := List.mem_of_mem_take hm
      unfold bobVis at hm'
      rcases List.mem_cons.mp hm' with rfl | hrest
      · cases hk
      · rcases List.mem_append.mp hrest with hrng | hacc
        · obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hrng
          obtain ⟨i, n, hq_eq⟩ := exists_randTerm_of_mem_newRandoms hq
          exact Or.inl ⟨i, n, rfl, congrArg (· :: []) hq_eq⟩
        · cases hp : receivedPlaintext tr _ with
          | none => rw [hp] at hacc; cases hacc
          | some m0 => rw [hp] at hacc; rcases List.mem_singleton.mp hacc with rfl; cases hk
    | encrypt _ _ _ _ wrap => exact rngEntryShape_of_mem_encVis hm
    | encryptAbort _ _ => exact rngEntryShape_of_mem_encVis hm
    | encryptFail _ _ _ => exact rngEntryShape_of_mem_encVis hm
    | decrypt _ si mi _ _ w => exact rngEntryShape_of_mem_decVis hm
    | decryptSkipped _ si mi _ _ _ w => exact rngEntryShape_of_mem_decVis hm
    | reject draws =>
      intro hk
      rcases List.mem_cons.mp hm with rfl | hrng
      · cases hk
      · obtain ⟨n, _, rfl⟩ := List.mem_map.mp hrng
        exact Or.inr (Or.inr ⟨n, rfl⟩)
    | _ => cases hm
  · exact rngEntryShape_of_mem_exposures hexp

private theorem rngEntryShape_of_mem_runMoves :
    ∀ (ms : List Move) (tr : _root_.DY.ExecTrace) {v : VisEntry},
      v ∈ (runMoves ms tr).2 → RngEntryShape v
  | [], _, _, hv => by cases hv
  | m :: ms, tr, _, hv => by
    rcases List.mem_append.mp hv with hm | hms
    · exact rngEntryShape_of_mem_moveVis hm
    · exact rngEntryShape_of_mem_runMoves ms (m.next tr) hms

private def SameKindAndRngLen (e₁ e₂ : MachineEvent) : Prop :=
  eventKind e₁ = eventKind e₂ ∧
    ∀ b₁ b₂, e₁ = .rng b₁ → e₂ = .rng b₂ → b₁.length = b₂.length

private theorem eventMatchesEntry_sameKindAndRngLen {interp : ExternInterpretation} {r : ProtocolSetup}
    {S : OpaqueSymbolSemantics} {g g' : Ghost} {e₁ e₂ : MachineEvent} {v : VisEntry}
    (hσ : g'.σ = g.σ) (hv : RngEntryShape v)
    (he₁ : EventMatchesEntry interp r S g e₁ v)
    (he₂ : EventMatchesEntry interp r S g' e₂ v) :
    SameKindAndRngLen e₁ e₂ := by
  refine ⟨he₁.1.trans he₂.1.symm, fun b₁ b₂ hb₁ hb₂ => ?_⟩
  subst hb₁; subst hb₂
  have hk : v.kind = .rng := he₁.1.symm
  have m₁ := he₁.2
  have m₂ := he₂.2
  rcases hv hk with ⟨i, n, hlay, hterms⟩ | ⟨j, hlay⟩ | ⟨n, hlay⟩
  · simp only [hlay, hterms, List.map_cons, List.map_nil, List.cons.injEq, and_true,
      eventBytes] at m₁ m₂
    rw [← m₁, ← m₂, gamma_randTerm_eq_of_sigma_eq hσ]
  · simp only [hlay, eventBytes] at m₁ m₂
    exact m₁.1.trans m₂.1.symm
  · simp only [hlay, eventBytes] at m₁ m₂
    exact m₁.trans m₂.symm

private theorem forall₂_sameKindAndRngLen_of_vis {interp : ExternInterpretation} {r : ProtocolSetup}
    {S : OpaqueSymbolSemantics} {g g' : Ghost} (hσ : g'.σ = g.σ) :
    ∀ {τ₁ τ₁' : List MachineEvent} {vs : List VisEntry},
      (∀ v ∈ vs, RngEntryShape v) →
      List.Forall₂ (EventMatchesEntry interp r S g) τ₁ vs →
      List.Forall₂ (EventMatchesEntry interp r S g') τ₁' vs →
      List.Forall₂ SameKindAndRngLen τ₁ τ₁'
  | _, _, _, _, .nil, .nil => .nil
  | _, _, _ :: _, hvs, .cons he₁ hf₁, .cons he₂ hf₂ =>
    .cons (eventMatchesEntry_sameKindAndRngLen hσ (hvs _ List.mem_cons_self) he₁ he₂)
      (forall₂_sameKindAndRngLen_of_vis hσ (fun v hv => hvs v (List.mem_cons_of_mem _ hv)) hf₁ hf₂)

/-- Pointwise `.rng` length agreement across `EventMatchesEntry` on `runVis r ms` when `g'.σ = g.σ`. -/
theorem matchedPrefix_sameKind_and_rngLen {interp : ExternInterpretation} {r : ProtocolSetup} {S : OpaqueSymbolSemantics}
    {who : List Participant} {g g' : Ghost} {ms : List Move} {τ₁ τ₁' : List MachineEvent}
    (hσ : g'.σ = g.σ)
    (hm : MatchedPrefix interp r S who g ms τ₁)
    (hm' : MatchedPrefix interp r S who g' ms τ₁') :
    List.Forall₂
      (fun e₁ e₂ => eventKind e₁ = eventKind e₂ ∧
        ∀ b₁ b₂, e₁ = .rng b₁ → e₂ = .rng b₂ → b₁.length = b₂.length)
      τ₁ τ₁' :=
  forall₂_sameKindAndRngLen_of_vis hσ
    (fun _ hv => rngEntryShape_of_mem_runMoves _ _ hv) hm.2.2.2.2.2 hm'.2.2.2.2.2

private theorem noAdjRngS5_tail {e : MachineEvent} {es : List MachineEvent}
    (h : NoAdjRngS5 (e :: es)) : NoAdjRngS5 es := by
  cases es with
  | nil => trivial
  | cons _ _ => exact h.2

private def HeadNotRng : List MachineEvent → Prop
  | [] => True
  | e :: _ => eventKind e ≠ .rng

private theorem headNotRng_of_noAdjRng_rng {coins : HwBytes} {σ τ : List MachineEvent}
    (hadj : NoAdjRngS5 (.rng coins :: σ)) (hcs : CoinSplit σ τ) : HeadNotRng τ := by
  cases hcs with
  | nil => trivial
  | keep _ _ =>
    cases hadj.1 with
    | inl h => exact absurd rfl h
    | inr h => exact h
  | split _ _ _ =>
    cases hadj.1 with
    | inl h => exact absurd rfl h
    | inr h => exact absurd rfl h

private theorem split_rng_run :
    ∀ {ps₁ ps₂ : List HwBytes} {τ₁ τ₂ : List MachineEvent},
      HeadNotRng τ₁ → HeadNotRng τ₂ →
      List.Forall₂ SameKindAndRngLen
        (ps₁.map MachineEvent.rng ++ τ₁) (ps₂.map MachineEvent.rng ++ τ₂) →
      List.Forall₂ (fun p₁ p₂ => p₁.length = p₂.length) ps₁ ps₂ ∧
        List.Forall₂ SameKindAndRngLen τ₁ τ₂
  | [], [], _, _, _, _, hrel => ⟨.nil, hrel⟩
  | [], _ :: _, τ₁, _, h₁, _, hrel => by
    cases τ₁ with
    | nil => cases hrel
    | cons _ _ =>
      cases hrel with
      | cons hhd _ => exact absurd hhd.1 h₁
  | _ :: _, [], _, τ₂, _, h₂, hrel => by
    cases τ₂ with
    | nil => cases hrel
    | cons _ _ =>
      cases hrel with
      | cons hhd _ => exact absurd hhd.1.symm h₂
  | p₁ :: _, p₂ :: _, _, _, h₁, h₂, hrel => by
    cases hrel with
    | cons hhd htl =>
      obtain ⟨hp, hτ⟩ := split_rng_run h₁ h₂ htl
      exact ⟨.cons (hhd.2 p₁ p₂ rfl rfl) hp, hτ⟩

private theorem pieces_eq_of_flatten_prefix :
    ∀ {ps₁ ps₂ : List HwBytes} {coins : HwBytes},
      ps₁.flatten <+: coins → ps₂.flatten <+: coins →
      List.Forall₂ (fun p₁ p₂ => p₁.length = p₂.length) ps₁ ps₂ →
      ps₁ = ps₂
  | _, _, _, _, _, .nil => rfl
  | _ :: _, _ :: _, _, ⟨t₁, ht₁⟩, ⟨t₂, ht₂⟩, .cons hlen htl => by
    simp only [List.flatten_cons, List.append_assoc] at ht₁ ht₂
    obtain ⟨rfl, hrest⟩ := List.append_inj (ht₁.trans ht₂.symm) hlen
    rw [pieces_eq_of_flatten_prefix ⟨t₁, rfl⟩ ⟨t₂, hrest.symm⟩ htl]

private theorem coinSplit_eq_of_sameKindAndRngLen {σ τ₁ τ₂ : List MachineEvent}
    (hadj : NoAdjRngS5 σ) (hcs₁ : CoinSplit σ τ₁) (hcs₂ : CoinSplit σ τ₂)
    (hrel : List.Forall₂ SameKindAndRngLen τ₁ τ₂) :
    τ₁ = τ₂ := by
  induction hcs₁ generalizing τ₂ with
  | nil =>
    cases hcs₂
    rfl
  | keep hx hcs₁' ih =>
    cases hcs₂ with
    | keep _ hcs₂' =>
      cases hrel with
      | cons _ hrel' =>
        rw [ih (noAdjRngS5_tail hadj) hcs₂' hrel']
    | split _ _ _ => exact absurd rfl (hx _)
  | split _ hpref₁ hcs₁' ih =>
    cases hcs₂ with
    | keep hx _ => exact absurd rfl (hx _)
    | split _ hpref₂ hcs₂' =>
      have h₁ := headNotRng_of_noAdjRng_rng hadj hcs₁'
      have h₂ := headNotRng_of_noAdjRng_rng hadj hcs₂'
      obtain ⟨hp, hrel'⟩ := split_rng_run h₁ h₂ hrel
      rw [pieces_eq_of_flatten_prefix hpref₁ hpref₂ hp,
          ih (noAdjRngS5_tail hadj) hcs₂' hrel']

/-- Under `NoAdjRngS5 σ₁`, fixing `ms` and `g'.σ = g.σ` pins the coin cut `τ₁' = τ₁`, so
`PrefixExplainingGhostsMoves` is contained in `PrefixGhosts`. -/
theorem prefixGhostsCli_subset_prefixGhosts {interp : ExternInterpretation} {r : ProtocolSetup} {S : OpaqueSymbolSemantics}
    {who : List Participant} {g : Ghost} {ms : List Move} {σ₁ τ₁ : List MachineEvent}
    (hadj : NoAdjRngS5 σ₁)
    (hcs : CoinSplit σ₁ τ₁)
    (hm : MatchedPrefix interp r S who g ms τ₁) :
    ∀ {g' : Ghost}, g' ∈ PrefixExplainingGhostsMoves interp r S who g ms σ₁ →
      g' ∈ PrefixGhosts interp r S who g ms τ₁ := by
  rintro g' ⟨hσ, τ₁', hcs', hm'⟩
  have hrel := matchedPrefix_sameKind_and_rngLen hσ hm hm'
  have hτ : τ₁ = τ₁' := coinSplit_eq_of_sameKindAndRngLen hadj hcs hcs' hrel
  exact ⟨hσ, hτ ▸ hm'⟩

/-- Transfers a `PrefixGhosts`-scoped predicate to `PrefixExplainingGhostsMoves` under `NoAdjRngS5`. -/
theorem excusesLift_pt_of_noAdjRng {interp : ExternInterpretation} {r : ProtocolSetup} {S : OpaqueSymbolSemantics}
    {who : List Participant} {g : Ghost} {ms : List Move} {σ₁ τ₁ : List MachineEvent}
    (hadj : NoAdjRngS5 σ₁)
    (hcs : CoinSplit σ₁ τ₁)
    (hm : MatchedPrefix interp r S who g ms τ₁)
    (hmemo : ∀ g' ∈ PrefixGhosts interp r S who g ms τ₁,
      MemoCollisionOn interp r S g' (fun u => u.AttackerKnows (runTraceMoves r ms)) (runTraceMoves r ms)
        (runVis r ms) (ptEntryOfNextEncrypt r ms).terms (ptEntryOfNextEncrypt r ms).terms) :
    ∀ g' ∈ PrefixExplainingGhostsMoves interp r S who g ms σ₁,
      MemoCollisionOn interp r S g' (fun u => u.AttackerKnows (runTraceMoves r ms)) (runTraceMoves r ms)
        (runVis r ms) (ptEntryOfNextEncrypt r ms).terms (ptEntryOfNextEncrypt r ms).terms :=
  fun g' hg' => hmemo g' (prefixGhostsCli_subset_prefixGhosts hadj hcs hm hg')

end Symbolic.Swarm.Coinsplit.S5
