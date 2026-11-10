/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Computational.Proofs.CryptoGames.SM.Reductions
public import LibsignalBinary.Specifications.CryptoGames.FSAEAD.Lazy
import VCVio.OracleComp.Constructions.SampleableType.Measure

/-!
# Proof of Lemma 13

**Checked by Lean.** Proves `PrivL13.lemma13_proof` (ACD19 §5.3.3, Lemma 13): `privGame` for the
Fig. 8 SM scheme is bounded in bias by the real world (`b = false`) of `redCKAPriv` in the CKA
game.
-/

@[expose] public section

open OracleComp OracleSpec ENNReal MeasureTheory CryptoGames.Lazy

namespace CryptoGames.SM.Construction.PrivL13

open Engine

/-! ### `DEq` and coin helpers -/

section Helpers

theorem DEq.bind_right_supp {α β : Type} (x : ProbComp α) {f g : α → ProbComp β}
    (h : ∀ a ∈ support x, DEq (f a) (g a)) : DEq (x >>= f) (x >>= g) := fun F => by
  simp only [bind_assoc]
  exact evalDist_bind_congr_of_support x _ _ fun a ha => h a ha F

theorem deq_of_evalDist_eq {α : Type} [MeasurableSpace α] [DiscreteMeasurableSpace α]
    {x y : ProbComp α} (h : 𝒟[x] = 𝒟[y]) : DEq x y := fun F => by
  rw [evalDist_bind_of_discrete, evalDist_bind_of_discrete, h]

theorem evalDist_uniformBool_beq (x : Bool) :
    𝒟[($ᵗ Bool : ProbComp Bool) >>= fun b => pure (b == x)] =
      𝒟[($ᵗ Bool : ProbComp Bool)] := by
  cases x
  · conv_rhs => rw [← bind_pure ($ᵗ Bool : ProbComp Bool)]
    ext s hs
    rw [evalDist_bind_of_discrete, evalDist_bind_of_discrete,
      Measure.bind_apply hs Measurable.of_discrete.aemeasurable,
      Measure.bind_apply hs Measurable.of_discrete.aemeasurable,
      lintegral_fintype, lintegral_fintype, Fintype.sum_bool, Fintype.sum_bool]
    simp [add_comm]
  · simp

theorem deq_uniformBool_beq (x : Bool) :
    DEq (($ᵗ Bool : ProbComp Bool) >>= fun b => pure (b == x)) ($ᵗ Bool : ProbComp Bool) :=
  deq_of_evalDist_eq (evalDist_uniformBool_beq x)

theorem deq_uniformBool_cond (c : Bool) (x : Bool) :
    DEq (($ᵗ Bool : ProbComp Bool) >>= fun b =>
          if c then pure (b == x) else ($ᵗ Bool : ProbComp Bool))
        ($ᵗ Bool : ProbComp Bool) := by
  cases c
  · simp only [Bool.false_eq_true, ↓reduceIte]
    exact DEq.bind_const _ _
  · simp only [↓reduceIte]
    exact deq_uniformBool_beq x

theorem boolBias_uniformBool : 𝒟[($ᵗ Bool : ProbComp Bool)].boolBias = 0 := by
  rw [Measure.boolBias_eq_two_mul_absDiff_half_of_isProbabilityMeasure]
  simp

theorem list_max?_mem {l : List ℕ} {m : ℕ} (h : l.max? = some m) : m ∈ l :=
  List.max?_mem h

theorem list_le_max?_of_mem {l : List ℕ} {a : ℕ} (ha : a ∈ l) :
    ∃ m, l.max? = some m ∧ a ≤ m := by
  induction l with
  | nil => contradiction
  | cons x xs ih =>
    simp only [List.mem_cons] at ha
    rcases xs with _ | ⟨y, ys⟩
    · simp only [List.not_mem_nil, or_false] at ha
      subst ha
      exact ⟨a, rfl, le_rfl⟩
    · rcases ha with rfl | ha
      · refine ⟨max a (ys.foldl max y), ?_, Nat.le_max_left a _⟩
        rw [List.max?_cons]
        rfl
      · obtain ⟨m, hm, ham⟩ := ih ha
        rw [List.max?_cons, hm]
        exact ⟨max x m, rfl, le_trans ham (Nat.le_max_right x m)⟩

end Helpers

/-! ### Doom lemmas -/

section TwoWayDoom

variable {Key St Msg Coins C : Type} [DecidableEq Msg] [DecidableEq C] [SampleableType Coins]

def privEnd (Δ : ℕ) (tL : Option ℕ) (t : ℕ) (b : Bool)
    (res : Bool × SM.GameState St Msg C) : ProbComp Bool :=
  if SM.lastLeakGuessAdmissible Δ tL t && SM.canon t res.2 == tL then pure (b == res.1)
  else ($ᵗ Bool : ProbComp Bool)

abbrev implP (sm : SMScheme Key St Msg Coins C) (Δ qep t : ℕ) :
    QueryImpl (unifSpec + SM.spec St Msg Coins C) (StateT (SM.GameState St Msg C) ProbComp) :=
  (QueryImpl.ofLift unifSpec ProbComp).liftTarget (StateT (SM.GameState St Msg C) ProbComp)
    + SM.oracleImpl sm Δ qep (SM.Config.priv t)

theorem implP_coin (sm : SMScheme Key St Msg Coins C) (Δ qep t n : ℕ)
    (s : SM.GameState St Msg C) :
    (implP sm Δ qep t (.inl n)).run s =
      (fun u => (u, s)) <$> ($ᵗ (Fin (n + 1)) : ProbComp (Fin (n + 1))) := rfl

theorem implP_transmit (sm : SMScheme Key St Msg Coins C) (Δ qep t : ℕ)
    (q : Party × Msg × Option Coins) :
    implP sm Δ qep t (.inr (.inl (.inl (.inl (.inl q))))) = SM.transmitImpl sm Δ qep q := rfl

theorem implP_chall (sm : SMScheme Key St Msg Coins C) (Δ qep t : ℕ)
    (q : Party × Msg × Msg × Option Coins) :
    implP sm Δ qep t (.inr (.inl (.inl (.inl (.inr q))))) =
      SM.challImpl sm Δ qep (SM.Config.priv t) q := rfl

theorem implP_deliver (sm : SMScheme Key St Msg Coins C) (Δ qep t : ℕ) (q : Party × C) :
    implP sm Δ qep t (.inr (.inl (.inl (.inr q)))) =
      SM.deliverImpl sm (SM.Config.priv t) q := rfl

theorem implP_inject (sm : SMScheme Key St Msg Coins C) (Δ qep t : ℕ) (q : Party × C) :
    implP sm Δ qep t (.inr (.inl (.inr q))) =
      SM.injectImpl sm Δ qep (SM.Config.priv t) q := rfl

theorem implP_corr (sm : SMScheme Key St Msg Coins C) (Δ qep t : ℕ) (P : Party) :
    implP sm Δ qep t (.inr (.inr P)) = SM.corrImpl P := rfl

def gsWithB (s : SM.GameState St Msg C) (b : Bool) : SM.GameState St Msg C :=
  { s with b := b }

omit [DecidableEq Msg] [DecidableEq C] [SampleableType Coins] in
theorem epMgmt_gsWithB (s : SM.GameState St Msg C) (Δ qep : ℕ) (P : Party) (bad b : Bool) :
    (gsWithB s b).epMgmt Δ qep P bad =
      Option.map (fun s₁ => gsWithB s₁ b) (s.epMgmt Δ qep P bad) := by
  unfold SM.GameState.epMgmt gsWithB SM.GameState.safeCh SM.GameState.leak
  dsimp only
  split
  · split
    · rfl
    · split <;> rfl
  · split <;> rfl

/-- Doom condition D1: a leak occurred strictly between `tL` and `t`. -/
def DoomD1 (tL : Option ℕ) (t : ℕ) (s : SM.GameState St Msg C) : Prop :=
  ∃ l ∈ s.leaks, SM.ltOpt tL l = true ∧ l < t

/-- Doom condition D2: `tL + Δ > t`, so no challenge in epoch `t` can ever be allowed. -/
def DoomD2 (Δ t : ℕ) (s : SM.GameState St Msg C) : Prop :=
  SM.healedBy s.tL Δ t = false

/-- Doom condition D3: `l` was skipped without leaking, and both parties are already `≥ l` with one
strictly above `l`. -/
def DoomD3 (l : ℕ) (s : SM.GameState St Msg C) : Prop :=
  l ∉ s.leaks ∧ l < max (s.epoch .A) (s.epoch .B) ∧ l ≤ s.epoch .A ∧ l ≤ s.epoch .B

omit [DecidableEq Msg] [DecidableEq C] [SampleableType Coins] in
theorem le_maxOpt_right (tL : Option ℕ) (x : ℕ) : x ≤ SM.maxOpt tL x := by
  cases tL with
  | none => exact le_rfl
  | some l => exact Nat.le_max_right l x

omit [DecidableEq Msg] [DecidableEq C] [SampleableType Coins] in
theorem healedBy_leak_false {s : SM.GameState St Msg C} {Δ t l : ℕ}
    (h : SM.healedBy s.tL Δ t = false) :
    SM.healedBy (s.leak l).tL Δ t = false := by
  unfold SM.GameState.leak
  cases htL : s.tL with
  | none => simp [SM.healedBy, htL] at h
  | some l₀ =>
    simp only [SM.healedBy, htL, decide_eq_false_iff_not] at h ⊢
    simp only [SM.maxOpt]
    omega

omit [DecidableEq Msg] [DecidableEq C] [SampleableType Coins] in
theorem healedBy_epMgmt_false {s s₁ : SM.GameState St Msg C} {Δ qep t : ℕ} {P : Party} {bad : Bool}
    (h : SM.healedBy s.tL Δ t = false) (hep : s.epMgmt Δ qep P bad = some s₁) :
    SM.healedBy s₁.tL Δ t = false := by
  unfold SM.GameState.epMgmt at hep
  split at hep
  · split at hep
    · contradiction
    · injection hep with hep
      rw [← hep]
      split
      · exact healedBy_leak_false h
      · exact h
  · split at hep
    · contradiction
    · injection hep with hep
      rw [← hep]
      exact h

omit [DecidableEq Msg] [DecidableEq C] [SampleableType Coins] in
theorem canon_ne_of_doomD1 {tL : Option ℕ} {t : ℕ} {s : SM.GameState St Msg C}
    (hd : DoomD1 tL t s) : (SM.canon t s == tL) = false := by
  rcases hd with ⟨l, hl_mem, hlt, hlt_t⟩
  have hmem_filt : l ∈ s.leaks.filter (· < t) := by
    rw [List.mem_filter]
    exact ⟨hl_mem, decide_eq_true hlt_t⟩
  obtain ⟨m, hmax, hlm⟩ := list_le_max?_of_mem hmem_filt
  unfold SM.canon
  rw [hmax]
  cases tL with
  | none => rfl
  | some l₀ =>
    simp only [SM.ltOpt, decide_eq_true_eq] at hlt
    rw [beq_eq_false_iff_ne]
    intro heq
    injection heq with heq
    omega

omit [DecidableEq Msg] [DecidableEq C] [SampleableType Coins] in
theorem canon_ne_of_doomD3 {l t : ℕ} {s : SM.GameState St Msg C}
    (hd : DoomD3 l s) : (SM.canon t s == some l) = false := by
  rw [beq_eq_false_iff_ne]
  intro heq
  have hmem := list_max?_mem heq
  rw [List.mem_filter] at hmem
  exact hd.1 hmem.1

omit [DecidableEq Msg] [DecidableEq C] [SampleableType Coins] in
theorem doomD1_epMgmt {tL : Option ℕ} {t Δ qep : ℕ} {P : Party} {bad : Bool}
    {s s₁ : SM.GameState St Msg C} (hd : DoomD1 tL t s)
    (hep : s.epMgmt Δ qep P bad = some s₁) : DoomD1 tL t s₁ := by
  rcases hd with ⟨l, hl, h1, h2⟩
  unfold SM.GameState.epMgmt at hep
  split at hep
  · split at hep
    · contradiction
    · injection hep with hep
      rw [← hep]
      split
      · exact ⟨l, List.mem_cons_of_mem _ hl, h1, h2⟩
      · exact ⟨l, hl, h1, h2⟩
  · split at hep
    · contradiction
    · injection hep with hep
      rw [← hep]
      exact ⟨l, hl, h1, h2⟩

omit [DecidableEq Msg] [DecidableEq C] [SampleableType Coins] in
theorem doomD3_epMgmt {l Δ qep : ℕ} {P : Party} {bad : Bool}
    {s s₁ : SM.GameState St Msg C} (hd : DoomD3 l s)
    (hep : s.epMgmt Δ qep P bad = some s₁) : DoomD3 l s₁ := by
  rcases hd with ⟨hnot, hmax, hA, hB⟩
  unfold SM.GameState.epMgmt at hep
  split at hep
  · split at hep
    · contradiction
    · injection hep with hep
      rw [← hep]
      refine ⟨?_, ?_, ?_, ?_⟩
      · split
        · simp only [SM.GameState.leak, List.mem_cons, not_or]
          refine ⟨?_, hnot⟩
          have hle := le_maxOpt_right s.tL (s.epoch P + 1)
          cases P <;> omega
        · exact hnot
      · split <;> (cases P <;> simp [SM.GameState.leak, Function.update] <;> omega)
      · split <;> (cases P <;> simp [SM.GameState.leak, Function.update] <;> omega)
      · split <;> (cases P <;> simp [SM.GameState.leak, Function.update] <;> omega)
  · split at hep
    · contradiction
    · injection hep with hep
      rw [← hep]
      exact ⟨hnot, hmax, hA, hB⟩

omit [DecidableEq Msg] [DecidableEq C] [SampleableType Coins] in
theorem doomD3_accept {l : ℕ} {P : Party} {st' : St} {pos : SM.Pos}
    {s : SM.GameState St Msg C} (hd : DoomD3 l s) : DoomD3 l (s.accept P st' pos) := by
  rcases hd with ⟨hnot, hmax, hA, hB⟩
  refine ⟨hnot, ?_, ?_, ?_⟩
  · cases P <;> simp [SM.GameState.accept, SM.GameState.delete, Function.update] <;> omega
  · cases P <;> simp [SM.GameState.accept, SM.GameState.delete, Function.update] <;> omega
  · cases P <;> simp [SM.GameState.accept, SM.GameState.delete, Function.update] <;> omega

omit [DecidableEq Msg] [DecidableEq C] [SampleableType Coins] in
theorem doomD3_afterCorr {l : ℕ} {P : Party} {s : SM.GameState St Msg C}
    (hd : DoomD3 l s) : DoomD3 l (s.afterCorr P) := by
  rcases hd with ⟨hnot, hmax, hA, hB⟩
  refine ⟨?_, hmax, hA, hB⟩
  simp only [SM.GameState.afterCorr, SM.GameState.leak, List.mem_cons, not_or]
  refine ⟨?_, hnot⟩
  have hle := le_maxOpt_right s.tL (max (s.epoch .A) (s.epoch .B))
  omega

theorem doomD1_oracleImpl (sm : SMScheme Key St Msg Coins C) (Δ qep : ℕ) (tL : Option ℕ) (t : ℕ)
    (q : (unifSpec + SM.spec St Msg Coins C).Domain) {s : SM.GameState St Msg C}
    (hd : DoomD1 tL t s) :
    ∀ z ∈ support ((implP sm Δ qep t q).run s), DoomD1 tL t z.2 := by
  rcases q with n | ((((q | q) | q) | q) | P)
  · intro z hz
    simp only [implP_coin, support_map, Set.mem_image] at hz
    rcases hz with ⟨_, _, rfl⟩
    exact hd
  · rcases q with ⟨P, m, r⟩
    intro z hz
    rw [implP_transmit] at hz
    simp only [SM.transmitImpl, StateT.run_bind, StateT.run_get, pure_bind] at hz
    split at hz
    · simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff] at hz
      rw [hz]; exact hd
    · simp only [StateT.run_bind, StateT.run_liftM, bind_assoc, pure_bind,
        mem_support_bind_iff] at hz
      rcases hz with ⟨⟨coins, bad⟩, _, hz⟩
      split at hz
      · simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff] at hz
        rw [hz]; exact hd
      · rename_i s₁ hep
        simp only [StateT.run_bind, StateT.run_set, pure_bind, StateT.run_pure,
          support_pure, Set.mem_singleton_iff] at hz
        rw [hz]
        exact doomD1_epMgmt (s₁ := s₁) hd hep
  · rcases q with ⟨P, m₀, m₁, r⟩
    intro z hz
    rw [implP_chall] at hz
    simp only [SM.challImpl, StateT.run_bind, StateT.run_get, pure_bind] at hz
    split at hz
    · simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff] at hz
      rw [hz]; exact hd
    · simp only [StateT.run_bind, StateT.run_liftM, bind_assoc, pure_bind,
        mem_support_bind_iff] at hz
      rcases hz with ⟨⟨coins, bad⟩, _, hz⟩
      split at hz
      · simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff] at hz
        rw [hz]; exact hd
      · rename_i s₁ hep
        split at hz
        · simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff] at hz
          rw [hz]; exact hd
        · simp only [StateT.run_bind, StateT.run_set, pure_bind, StateT.run_pure,
            support_pure, Set.mem_singleton_iff] at hz
          rw [hz]
          exact doomD1_epMgmt (s₁ := s₁) hd hep
  · rcases q with ⟨P, c⟩
    intro z hz
    rw [implP_deliver] at hz
    simp only [SM.deliverImpl, StateT.run_bind, StateT.run_get, pure_bind] at hz
    split at hz
    · simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff] at hz
      rw [hz]; exact hd
    · split at hz
      · simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff] at hz
        rw [hz]; exact hd
      · split at hz
        · split at hz <;>
            simp only [StateT.run_bind, StateT.run_set, pure_bind, StateT.run_pure,
              support_pure, Set.mem_singleton_iff] at hz <;>
            rw [hz] <;> exact hd
        · split at hz <;>
            simp only [StateT.run_bind, StateT.run_set, pure_bind, StateT.run_pure,
              support_pure, Set.mem_singleton_iff] at hz <;>
            rw [hz] <;> exact hd
  · rcases q with ⟨P, c⟩
    intro z hz
    rw [implP_inject] at hz
    simp only [SM.injectImpl, StateT.run_bind, StateT.run_get, pure_bind] at hz
    split at hz
    · simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff] at hz
      rw [hz]; exact hd
    · split at hz
      · simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff] at hz
        rw [hz]; exact hd
      · split at hz
        · simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff] at hz
          rw [hz]; exact hd
        · split at hz
          · simp only [StateT.run_bind, StateT.run_set, pure_bind, StateT.run_pure,
              support_pure, Set.mem_singleton_iff] at hz
            rw [hz]; exact hd
          · split at hz <;>
              simp only [StateT.run_bind, StateT.run_set, pure_bind, StateT.run_pure,
                support_pure, Set.mem_singleton_iff] at hz <;>
              rw [hz] <;> exact hd
  · intro z hz
    rw [implP_corr] at hz
    simp only [SM.corrImpl, StateT.run_bind, StateT.run_get, pure_bind] at hz
    split at hz
    · simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff] at hz
      rw [hz]; exact hd
    · simp only [StateT.run_bind, StateT.run_set, pure_bind, StateT.run_pure,
        support_pure, Set.mem_singleton_iff] at hz
      rw [hz]
      rcases hd with ⟨l, hl, h1, h2⟩
      exact ⟨l, List.mem_cons_of_mem _ hl, h1, h2⟩

theorem doomD3_oracleImpl (sm : SMScheme Key St Msg Coins C) (Δ qep l t : ℕ)
    (q : (unifSpec + SM.spec St Msg Coins C).Domain) {s : SM.GameState St Msg C}
    (hd : DoomD3 l s) :
    ∀ z ∈ support ((implP sm Δ qep t q).run s), DoomD3 l z.2 := by
  rcases q with n | ((((q | q) | q) | q) | P)
  · intro z hz
    simp only [implP_coin, support_map, Set.mem_image] at hz
    rcases hz with ⟨_, _, rfl⟩
    exact hd
  · rcases q with ⟨P, m, r⟩
    intro z hz
    rw [implP_transmit] at hz
    simp only [SM.transmitImpl, StateT.run_bind, StateT.run_get, pure_bind] at hz
    split at hz
    · simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff] at hz
      rw [hz]; exact hd
    · simp only [StateT.run_bind, StateT.run_liftM, bind_assoc, pure_bind,
        mem_support_bind_iff] at hz
      rcases hz with ⟨⟨coins, bad⟩, _, hz⟩
      split at hz
      · simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff] at hz
        rw [hz]; exact hd
      · rename_i s₁ hep
        simp only [StateT.run_bind, StateT.run_set, pure_bind, StateT.run_pure,
          support_pure, Set.mem_singleton_iff] at hz
        rw [hz]
        exact doomD3_epMgmt (s₁ := s₁) hd hep
  · rcases q with ⟨P, m₀, m₁, r⟩
    intro z hz
    rw [implP_chall] at hz
    simp only [SM.challImpl, StateT.run_bind, StateT.run_get, pure_bind] at hz
    split at hz
    · simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff] at hz
      rw [hz]; exact hd
    · simp only [StateT.run_bind, StateT.run_liftM, bind_assoc, pure_bind,
        mem_support_bind_iff] at hz
      rcases hz with ⟨⟨coins, bad⟩, _, hz⟩
      split at hz
      · simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff] at hz
        rw [hz]; exact hd
      · rename_i s₁ hep
        split at hz
        · simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff] at hz
          rw [hz]; exact hd
        · simp only [StateT.run_bind, StateT.run_set, pure_bind, StateT.run_pure,
            support_pure, Set.mem_singleton_iff] at hz
          rw [hz]
          exact doomD3_epMgmt (s₁ := s₁) hd hep
  · rcases q with ⟨P, c⟩
    intro z hz
    rw [implP_deliver] at hz
    simp only [SM.deliverImpl, StateT.run_bind, StateT.run_get, pure_bind] at hz
    split at hz
    · simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff] at hz
      rw [hz]; exact hd
    · split at hz
      · simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff] at hz
        rw [hz]; exact hd
      · split at hz
        · split at hz <;>
            simp only [StateT.run_bind, StateT.run_set, pure_bind, StateT.run_pure,
              support_pure, Set.mem_singleton_iff] at hz <;>
            rw [hz] <;> exact hd
        · rename_i r _ _ st' t' i' m' _
          split at hz <;>
            simp only [StateT.run_bind, StateT.run_set, pure_bind, StateT.run_pure,
              support_pure, Set.mem_singleton_iff] at hz <;>
            rw [hz] <;> exact doomD3_accept (st' := st') (pos := r.pos) hd
  · rcases q with ⟨P, c⟩
    intro z hz
    rw [implP_inject] at hz
    simp only [SM.injectImpl, StateT.run_bind, StateT.run_get, pure_bind] at hz
    split at hz
    · simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff] at hz
      rw [hz]; exact hd
    · split at hz
      · simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff] at hz
        rw [hz]; exact hd
      · split at hz
        · simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff] at hz
          rw [hz]; exact hd
        · split at hz
          · simp only [StateT.run_bind, StateT.run_set, pure_bind, StateT.run_pure,
              support_pure, Set.mem_singleton_iff] at hz
            rw [hz]; exact doomD3_accept hd
          · split at hz <;>
              simp only [StateT.run_bind, StateT.run_set, pure_bind, StateT.run_pure,
                support_pure, Set.mem_singleton_iff] at hz <;>
              rw [hz] <;> exact hd
  · intro z hz
    rw [implP_corr] at hz
    simp only [SM.corrImpl, StateT.run_bind, StateT.run_get, pure_bind] at hz
    split at hz
    · simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff] at hz
      rw [hz]; exact hd
    · simp only [StateT.run_bind, StateT.run_set, pure_bind, StateT.run_pure,
        support_pure, Set.mem_singleton_iff] at hz
      rw [hz]
      exact doomD3_afterCorr hd

theorem doomD2_oracleImpl (sm : SMScheme Key St Msg Coins C) (Δ qep t : ℕ)
    (q : (unifSpec + SM.spec St Msg Coins C).Domain) {s : SM.GameState St Msg C}
    (hd : DoomD2 Δ t s) :
    ∀ z ∈ support ((implP sm Δ qep t q).run s), DoomD2 Δ t z.2 := by
  rcases q with n | ((((q | q) | q) | q) | P)
  · intro z hz
    simp only [implP_coin, support_map, Set.mem_image] at hz
    rcases hz with ⟨_, _, rfl⟩
    exact hd
  · rcases q with ⟨P, m, r⟩
    intro z hz
    rw [implP_transmit] at hz
    simp only [SM.transmitImpl, StateT.run_bind, StateT.run_get, pure_bind] at hz
    split at hz
    · simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff] at hz
      rw [hz]; exact hd
    · simp only [StateT.run_bind, StateT.run_liftM, bind_assoc, pure_bind,
        mem_support_bind_iff] at hz
      rcases hz with ⟨⟨coins, bad⟩, _, hz⟩
      split at hz
      · simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff] at hz
        rw [hz]; exact hd
      · rename_i s₁ hep
        simp only [StateT.run_bind, StateT.run_set, pure_bind, StateT.run_pure,
          support_pure, Set.mem_singleton_iff] at hz
        rw [hz]
        exact healedBy_epMgmt_false (s₁ := s₁) hd hep
  · rcases q with ⟨P, m₀, m₁, r⟩
    intro z hz
    rw [implP_chall] at hz
    simp only [SM.challImpl, StateT.run_bind, StateT.run_get, pure_bind] at hz
    split at hz
    · simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff] at hz
      rw [hz]; exact hd
    · simp only [StateT.run_bind, StateT.run_liftM, bind_assoc, pure_bind,
        mem_support_bind_iff] at hz
      rcases hz with ⟨⟨coins, bad⟩, _, hz⟩
      split at hz
      · simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff] at hz
        rw [hz]; exact hd
      · rename_i s₁ hep
        split at hz
        · simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff] at hz
          rw [hz]; exact hd
        · simp only [StateT.run_bind, StateT.run_set, pure_bind, StateT.run_pure,
            support_pure, Set.mem_singleton_iff] at hz
          rw [hz]
          exact healedBy_epMgmt_false (s₁ := s₁) hd hep
  · rcases q with ⟨P, c⟩
    intro z hz
    rw [implP_deliver] at hz
    simp only [SM.deliverImpl, StateT.run_bind, StateT.run_get, pure_bind] at hz
    split at hz
    · simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff] at hz
      rw [hz]; exact hd
    · split at hz
      · simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff] at hz
        rw [hz]; exact hd
      · split at hz
        · split at hz <;>
            simp only [StateT.run_bind, StateT.run_set, pure_bind, StateT.run_pure,
              support_pure, Set.mem_singleton_iff] at hz <;>
            rw [hz] <;> exact hd
        · split at hz <;>
            simp only [StateT.run_bind, StateT.run_set, pure_bind, StateT.run_pure,
              support_pure, Set.mem_singleton_iff] at hz <;>
            rw [hz] <;> exact hd
  · rcases q with ⟨P, c⟩
    intro z hz
    rw [implP_inject] at hz
    simp only [SM.injectImpl, StateT.run_bind, StateT.run_get, pure_bind] at hz
    split at hz
    · simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff] at hz
      rw [hz]; exact hd
    · split at hz
      · simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff] at hz
        rw [hz]; exact hd
      · split at hz
        · simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff] at hz
          rw [hz]; exact hd
        · split at hz
          · simp only [StateT.run_bind, StateT.run_set, pure_bind, StateT.run_pure,
              support_pure, Set.mem_singleton_iff] at hz
            rw [hz]; exact hd
          · split at hz <;>
              simp only [StateT.run_bind, StateT.run_set, pure_bind, StateT.run_pure,
                support_pure, Set.mem_singleton_iff] at hz <;>
              rw [hz] <;> exact hd
  · intro z hz
    rw [implP_corr] at hz
    simp only [SM.corrImpl, StateT.run_bind, StateT.run_get, pure_bind] at hz
    split at hz
    · simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff] at hz
      rw [hz]; exact hd
    · simp only [StateT.run_bind, StateT.run_set, pure_bind, StateT.run_pure,
        support_pure, Set.mem_singleton_iff] at hz
      rw [hz]
      exact healedBy_leak_false hd

theorem doomD1_simulateQ (sm : SMScheme Key St Msg Coins C) (Δ qep : ℕ) (tL : Option ℕ) (t : ℕ)
    {α : Type} (oa : SM.AdversaryComp St Msg Coins C α) :
    ∀ {s : SM.GameState St Msg C}, DoomD1 tL t s →
      ∀ z ∈ support ((simulateQ (implP sm Δ qep t) oa).run s), DoomD1 tL t z.2 := by
  induction oa using OracleComp.inductionOn with
  | pure a =>
    intro s hd z hz
    simp only [simulateQ_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff] at hz
    rw [hz]; exact hd
  | query_bind q mx ih =>
    intro s hd z hz
    simp only [simulateQ_bind, simulateQ_query, OracleQuery.input_query, OracleQuery.cont_query,
      id_map, StateT.run_bind, mem_support_bind_iff] at hz
    rcases hz with ⟨⟨u, s'⟩, hu, hz⟩
    exact ih u (doomD1_oracleImpl sm Δ qep tL t q hd ⟨u, s'⟩ hu) z hz

theorem doomD3_simulateQ (sm : SMScheme Key St Msg Coins C) (Δ qep l t : ℕ)
    {α : Type} (oa : SM.AdversaryComp St Msg Coins C α) :
    ∀ {s : SM.GameState St Msg C}, DoomD3 l s →
      ∀ z ∈ support ((simulateQ (implP sm Δ qep t) oa).run s), DoomD3 l z.2 := by
  induction oa using OracleComp.inductionOn with
  | pure a =>
    intro s hd z hz
    simp only [simulateQ_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff] at hz
    rw [hz]; exact hd
  | query_bind q mx ih =>
    intro s hd z hz
    simp only [simulateQ_bind, simulateQ_query, OracleQuery.input_query, OracleQuery.cont_query,
      id_map, StateT.run_bind, mem_support_bind_iff] at hz
    rcases hz with ⟨⟨u, s'⟩, hu, hz⟩
    exact ih u (doomD3_oracleImpl sm Δ qep l t q hd ⟨u, s'⟩ hu) z hz

theorem deq_privEnd_of_doomD1 (sm : SMScheme Key St Msg Coins C) (Δ qep : ℕ) (tL : Option ℕ) (t : ℕ)
    (b : Bool) (oa : SM.Adversary St Msg Coins C) {s : SM.GameState St Msg C}
    (hd : DoomD1 tL t s) :
    DEq ((simulateQ (implP sm Δ qep t) oa).run s >>= privEnd Δ tL t b)
        ($ᵗ Bool : ProbComp Bool) := by
  refine (DEq.bind_right_supp ((simulateQ (implP sm Δ qep t) oa).run s)
    (g := fun _ => ($ᵗ Bool : ProbComp Bool)) ?_).trans (DEq.bind_const _ _)
  intro z hz
  have hd' := doomD1_simulateQ sm Δ qep tL t oa hd z hz
  simp only [privEnd, canon_ne_of_doomD1 hd', Bool.and_false]
  exact DEq.refl _

theorem deq_privEnd_of_doomD3 (sm : SMScheme Key St Msg Coins C) (Δ qep l t : ℕ)
    (b : Bool) (oa : SM.Adversary St Msg Coins C) {s : SM.GameState St Msg C}
    (hd : DoomD3 l s) :
    DEq ((simulateQ (implP sm Δ qep t) oa).run s >>= privEnd Δ (some l) t b)
        ($ᵗ Bool : ProbComp Bool) := by
  refine (DEq.bind_right_supp ((simulateQ (implP sm Δ qep t) oa).run s)
    (g := fun _ => ($ᵗ Bool : ProbComp Bool)) ?_).trans (DEq.bind_const _ _)
  intro z hz
  have hd' := doomD3_simulateQ sm Δ qep l t oa hd z hz
  simp only [privEnd, canon_ne_of_doomD3 hd', Bool.and_false]
  exact DEq.refl _

theorem implP_coin_gsWithB (sm : SMScheme Key St Msg Coins C) (Δ qep t n : ℕ)
    (s : SM.GameState St Msg C) (b : Bool) :
    (implP sm Δ qep t (.inl n)).run (gsWithB s b) =
      Prod.map id (fun s' => gsWithB s' b) <$> (implP sm Δ qep t (.inl n)).run s := by
  simp only [implP_coin, Functor.map_map]
  rfl

theorem implP_transmit_gsWithB (sm : SMScheme Key St Msg Coins C) (Δ qep t : ℕ)
    (q : Party × Msg × Option Coins) (s : SM.GameState St Msg C) (b : Bool) :
    (implP sm Δ qep t (.inr (.inl (.inl (.inl (.inl q)))))).run (gsWithB s b) =
      Prod.map id (fun s' => gsWithB s' b) <$>
        (implP sm Δ qep t (.inr (.inl (.inl (.inl (.inl q)))))).run s := by
  rcases q with ⟨P, m, r⟩
  rw [implP_transmit]
  simp only [SM.transmitImpl, StateT.run_bind, StateT.run_get, pure_bind]
  have hwin : (gsWithB s b).win = s.win := rfl
  rw [hwin]
  split
  · simp [StateT.run_pure]
  · simp only [StateT.run_bind, StateT.run_liftM, bind_assoc, pure_bind, map_bind]
    refine bind_congr fun ⟨coins, bad⟩ => ?_
    rw [epMgmt_gsWithB]
    cases s.epMgmt Δ qep P bad <;>
      simp only [Option.map, StateT.run_pure, StateT.run_bind, StateT.run_set, pure_bind, map_pure] <;>
      rfl

theorem implP_deliver_gsWithB (sm : SMScheme Key St Msg Coins C) (Δ qep t : ℕ)
    (q : Party × C) (s : SM.GameState St Msg C) (b : Bool) :
    (implP sm Δ qep t (.inr (.inl (.inl (.inr q))))).run (gsWithB s b) =
      Prod.map id (fun s' => gsWithB s' b) <$>
        (implP sm Δ qep t (.inr (.inl (.inl (.inr q))))).run s := by
  rcases q with ⟨P, c⟩
  rw [implP_deliver]
  simp only [SM.deliverImpl, StateT.run_bind, StateT.run_get, pure_bind]
  have hin : (gsWithB s b).inTransit P.other c = s.inTransit P.other c := rfl
  have hwin : (gsWithB s b).win = s.win := rfl
  have hst : (gsWithB s b).st = s.st := rfl
  have hch : (gsWithB s b).chall = s.chall := rfl
  rw [hwin, hin, hst, hch]
  split
  · simp [StateT.run_pure]
  · cases s.inTransit P.other c with
    | none => simp [StateT.run_pure]
    | some r =>
      dsimp only
      cases sm.receive (s.st P) c with
      | none =>
        simp [SM.Config.priv, StateT.run_pure]
      | some x =>
        rcases x with ⟨st', t', i', m'⟩
        simp [SM.Config.priv, StateT.run_set, gsWithB, SM.GameState.accept, SM.GameState.delete]

theorem implP_inject_gsWithB (sm : SMScheme Key St Msg Coins C) (Δ qep t : ℕ)
    (q : Party × C) (s : SM.GameState St Msg C) (b : Bool) :
    (implP sm Δ qep t (.inr (.inl (.inr q)))).run (gsWithB s b) =
      Prod.map id (fun s' => gsWithB s' b) <$>
        (implP sm Δ qep t (.inr (.inl (.inr q)))).run s := by
  rcases q with ⟨P, c⟩
  rw [implP_inject]
  simp only [SM.injectImpl, StateT.run_bind, StateT.run_get, pure_bind]
  have hcond : ((gsWithB s b).win || ((gsWithB s b).inTransit P.other c).isSome ||
      !((gsWithB s b).safeInj Δ)) =
    (s.win || (s.inTransit P.other c).isSome || !(s.safeInj Δ)) := rfl
  have hst : (gsWithB s b).st = s.st := rfl
  rw [hcond, hst]
  split
  · simp [StateT.run_pure]
  · cases sm.receive (s.st P) c with
    | none => simp [StateT.run_pure]
    | some x =>
      rcases x with ⟨st', t', i', m'⟩
      dsimp only
      split
      · simp [StateT.run_pure]
      · have htriv : (gsWithB s b).trivial Δ ⟨P.other, t', i'⟩ =
            s.trivial Δ ⟨P.other, t', i'⟩ := rfl
        rw [htriv]
        split
        · simp [StateT.run_set, gsWithB, SM.GameState.accept, SM.GameState.delete]
        · simp [SM.Config.priv, StateT.run_pure]

theorem implP_corr_gsWithB (sm : SMScheme Key St Msg Coins C) (Δ qep t : ℕ)
    (P : Party) (s : SM.GameState St Msg C) (b : Bool) :
    (implP sm Δ qep t (.inr (.inr P))).run (gsWithB s b) =
      Prod.map id (fun s' => gsWithB s' b) <$>
        (implP sm Δ qep t (.inr (.inr P))).run s := by
  rw [implP_corr]
  simp only [SM.corrImpl, StateT.run_bind, StateT.run_get, pure_bind]
  have hcond : ((gsWithB s b).win || !((gsWithB s b).corrAllowed P)) =
      (s.win || !(s.corrAllowed P)) := rfl
  have hst : (gsWithB s b).st = s.st := rfl
  rw [hcond, hst]
  split
  · simp [StateT.run_pure]
  · simp [StateT.run_set, gsWithB, SM.GameState.afterCorr, SM.GameState.leak]

theorem implP_chall_gsWithB_of_doomD2 (sm : SMScheme Key St Msg Coins C) (Δ qep t : ℕ)
    (q : Party × Msg × Msg × Option Coins) {s : SM.GameState St Msg C} (b : Bool)
    (hd : DoomD2 Δ t s) :
    (implP sm Δ qep t (.inr (.inl (.inl (.inl (.inr q)))))).run (gsWithB s b) =
      Prod.map id (fun s' => gsWithB s' b) <$>
        (implP sm Δ qep t (.inr (.inl (.inl (.inl (.inr q)))))).run s := by
  rcases q with ⟨P, m₀, m₁, r⟩
  rw [implP_chall]
  simp only [SM.challImpl, StateT.run_bind, StateT.run_get, pure_bind]
  have hwin : (gsWithB s b).win = s.win := rfl
  rw [hwin]
  split
  · simp [StateT.run_pure]
  · simp only [StateT.run_bind, StateT.run_liftM, bind_assoc, pure_bind, map_bind]
    refine bind_congr fun ⟨coins, bad⟩ => ?_
    rw [epMgmt_gsWithB]
    cases hep : s.epMgmt Δ qep P bad with
    | none => simp [StateT.run_pure]
    | some s₁ =>
      have hne : (!(s₁.safeCh Δ P) || !((SM.Config.priv (Msg := Msg) t).challAllowedIn (s₁.epoch P))) = true := by
        have hd₁ := healedBy_epMgmt_false hd hep
        simp only [SM.GameState.safeCh, SM.Config.priv, Bool.or_eq_true, Bool.not_eq_true']
        by_cases heq : s₁.epoch P = t
        · left; rw [heq]; exact hd₁
        · right; exact beq_eq_false_iff_ne.mpr heq
      have hne' : (!((gsWithB s₁ b).safeCh Δ P) ||
          !((SM.Config.priv (Msg := Msg) t).challAllowedIn ((gsWithB s₁ b).epoch P))) = true := hne
      simp only [Option.map_some, hne, hne', ↓reduceIte, StateT.run_pure, map_pure, Prod.map_apply,
        id_eq]

theorem implP_gsWithB_of_doomD2 (sm : SMScheme Key St Msg Coins C) (Δ qep t : ℕ)
    (q : (unifSpec + SM.spec St Msg Coins C).Domain) {s : SM.GameState St Msg C} (b : Bool)
    (hd : DoomD2 Δ t s) :
    (implP sm Δ qep t q).run (gsWithB s b) =
      Prod.map id (fun s' => gsWithB s' b) <$> (implP sm Δ qep t q).run s := by
  rcases q with n | ((((q | q) | q) | q) | P)
  · exact implP_coin_gsWithB sm Δ qep t n s b
  · exact implP_transmit_gsWithB sm Δ qep t q s b
  · exact implP_chall_gsWithB_of_doomD2 sm Δ qep t q b hd
  · exact implP_deliver_gsWithB sm Δ qep t q s b
  · exact implP_inject_gsWithB sm Δ qep t q s b
  · exact implP_corr_gsWithB sm Δ qep t P s b

theorem simulateQ_gsWithB_of_doomD2 (sm : SMScheme Key St Msg Coins C) (Δ qep t : ℕ)
    (b : Bool) {α : Type} (oa : SM.AdversaryComp St Msg Coins C α) :
    ∀ {s : SM.GameState St Msg C}, DoomD2 Δ t s →
      (simulateQ (implP sm Δ qep t) oa).run (gsWithB s b) =
        Prod.map id (fun s' => gsWithB s' b) <$> (simulateQ (implP sm Δ qep t) oa).run s := by
  induction oa using OracleComp.inductionOn with
  | pure a =>
    intro s _
    simp [StateT.run_pure]
  | query_bind q mx ih =>
    intro s hd
    simp only [simulateQ_bind, simulateQ_query, OracleQuery.input_query, OracleQuery.cont_query,
      id_map, StateT.run_bind, implP_gsWithB_of_doomD2 sm Δ qep t q b hd, map_bind, bind_map_left]
    exact bind_congr_of_forall_mem_support _ fun z hz =>
      ih z.1 (doomD2_oracleImpl sm Δ qep t q hd z hz)

theorem deq_privEnd_of_doomD2 (sm : SMScheme Key St Msg Coins C) (Δ qep : ℕ) (tL : Option ℕ) (t : ℕ)
    (oa : SM.Adversary St Msg Coins C) {s : SM.GameState St Msg C} (hd : DoomD2 Δ t s) :
    DEq (($ᵗ Bool : ProbComp Bool) >>= fun b =>
          (simulateQ (implP sm Δ qep t) oa).run (gsWithB s b) >>= privEnd Δ tL t b)
        ($ᵗ Bool : ProbComp Bool) := by
  have hsim : ∀ b,
      (simulateQ (implP sm Δ qep t) oa).run (gsWithB s b) >>= privEnd Δ tL t b =
        (simulateQ (implP sm Δ qep t) oa).run s >>= fun z => privEnd Δ tL t b z := by
    intro b
    rw [simulateQ_gsWithB_of_doomD2 sm Δ qep t b oa hd, bind_map_left]
    rfl
  simp_rw [hsim]
  refine (DEq.swap ($ᵗ Bool : ProbComp Bool) ((simulateQ (implP sm Δ qep t) oa).run s)
    (fun b z => privEnd Δ tL t b z)).trans ?_
  refine (DEq.bind_right ((simulateQ (implP sm Δ qep t) oa).run s)
    (g := fun _ => ($ᵗ Bool : ProbComp Bool)) fun z => ?_).trans (DEq.bind_const _ _)
  exact deq_uniformBool_cond (SM.lastLeakGuessAdmissible Δ tL t && SM.canon t z.2 == tL) z.1

end TwoWayDoom

/-! ### `redCKAPriv` simulation and invariant -/

section RedCKASim

variable {KC Γ CCoins T I : Type} {KR Sig K : Type} {SS RS M E : Type}
  [DecidableEq T] [DecidableEq M] [DecidableEq E] [DecidableEq I] [Inhabited E]
  [SampleableType KR] [SampleableType KC] [SampleableType CCoins] [SampleableType I]
  [SampleableType K]

variable (cka : CKAScheme KC Γ CCoins T I) (prng : PRFPRNG KR Sig I K)
  (fs : FSAEADScheme K SS RS (Header T) M E) (lam : I) (Δcka qep : ℕ) (tL : Option ℕ) (t : ℕ)

abbrev VPt (Γ T Sig SS RS : Type) := PartyState (Option Γ) T Sig SS RS

abbrev RSt (Γ T Sig SS RS : Type) := PartyState Γ T Sig SS RS

abbrev ESt (Γ T Sig SS RS M E I : Type) :=
  EState (VPt Γ T Sig SS RS) M (Header T × E) (CKAState T I)

abbrev JSt (Γ T Sig SS RS M E I : Type) := ESt Γ T Sig SS RS M E I × CKA.GameState Γ T

abbrev EMc (Γ CCoins T I Sig SS RS M E : Type) :=
  EM (CKA.spec Γ CCoins T I) (Option Γ) T Sig SS RS M E (CKAState T I)

abbrev CHMc (Γ CCoins T I : Type) := HM (CKA.spec Γ CCoins T I) (CKAState T I)

def moP : Mode := ⟨false, tL, t⟩

def polP : Policy := ⟨false, tL, t⟩

abbrev implC (tH : ℕ) :
    QueryImpl (unifSpec + CKA.spec Γ CCoins T I) (StateT (CKA.GameState Γ T) ProbComp) :=
  (QueryImpl.ofLift unifSpec ProbComp).liftTarget (StateT (CKA.GameState Γ T) ProbComp)
    + CKA.oracleImpl cka Δcka tH

abbrev implEc :
    QueryImpl (unifSpec + SM.spec (RSt Γ T Sig SS RS) M CCoins (Header T × E))
      (EMc Γ CCoins T I Sig SS RS M E) :=
  implE (hooksCKA cka prng fs Δcka (moP tL t)) (2 + Δcka) qep fs.maxSkip
    (SM.Config.priv t) (polP tL t)

def Y {α : Type} (y : EMc Γ CCoins T I Sig SS RS M E α) (σ : JSt Γ T Sig SS RS M E I) :
    ProbComp (α × JSt Γ T Sig SS RS M E I) :=
  (fun r => (r.1.1, (r.1.2, r.2))) <$>
    (simulateQ (implC cka Δcka (healEpoch tL)) (y.run σ.1)).run σ.2

def ckaEnd (b : Bool) (r : Bool × JSt Γ T Sig SS RS M E I) : ProbComp Bool :=
  if !r.2.1.abort && SM.lastLeakGuessAdmissible (2 + Δcka) tL t && SM.canon t r.2.1.g == tL then
    pure (b == r.1)
  else ($ᵗ Bool : ProbComp Bool)

omit [DecidableEq T] [DecidableEq M] [DecidableEq E] [DecidableEq I] [Inhabited E]
  [SampleableType KR] [SampleableType KC] [SampleableType K] in
theorem Y_pure {α : Type} (a : α) (σ : JSt Γ T Sig SS RS M E I) :
    Y cka Δcka tL (pure a) σ = pure (a, σ) := by
  simp [Y, StateT.run_pure]

omit [DecidableEq T] [DecidableEq M] [DecidableEq E] [DecidableEq I] [Inhabited E]
  [SampleableType KR] [SampleableType KC] [SampleableType K] in
theorem Y_bind {α β : Type} (y : EMc Γ CCoins T I Sig SS RS M E α)
    (f : α → EMc Γ CCoins T I Sig SS RS M E β) (σ : JSt Γ T Sig SS RS M E I) :
    Y cka Δcka tL (y >>= f) σ = Y cka Δcka tL y σ >>= fun r => Y cka Δcka tL (f r.1) r.2 := by
  simp [Y, StateT.run_bind, simulateQ_bind, map_bind, bind_map_left]

omit [DecidableEq T] [DecidableEq M] [DecidableEq E] [DecidableEq I] [Inhabited E]
  [SampleableType KR] [SampleableType KC] [SampleableType K] in
theorem Y_get (σ : JSt Γ T Sig SS RS M E I) :
    Y cka Δcka tL get σ = pure (σ.1, σ) := by
  simp [Y, StateT.run_get]

omit [DecidableEq T] [DecidableEq M] [DecidableEq E] [DecidableEq I] [Inhabited E]
  [SampleableType KR] [SampleableType KC] [SampleableType K] in
theorem Y_modify (f : ESt Γ T Sig SS RS M E I → ESt Γ T Sig SS RS M E I)
    (σ : JSt Γ T Sig SS RS M E I) :
    Y cka Δcka tL (modify f) σ = pure ((), (f σ.1, σ.2)) := by
  simp [Y, StateT.run_modify]

omit [DecidableEq T] [DecidableEq M] [DecidableEq E] [DecidableEq I] [Inhabited E]
  [SampleableType KR] [SampleableType KC] [SampleableType K] in
theorem Y_abortE (σ : JSt Γ T Sig SS RS M E I) :
    Y cka Δcka tL abortE σ = pure ((), ({ σ.1 with abort := true }, σ.2)) := by
  simp [abortE, Y_modify]

omit [DecidableEq T] [DecidableEq M] [DecidableEq E] [DecidableEq I] [Inhabited E]
  [SampleableType KR] [SampleableType KC] [SampleableType CCoins] [SampleableType I]
  [SampleableType K] in
theorem liftH_run {α : Type} (x : CHMc Γ CCoins T I α) (es : ESt Γ T Sig SS RS M E I) :
    (liftH x : EMc Γ CCoins T I Sig SS RS M E α).run es =
      (do let (a, h') ← x.run es.h; pure (a, { es with h := h' })) := rfl

omit [DecidableEq T] [DecidableEq M] [DecidableEq E] [DecidableEq I] [Inhabited E]
  [SampleableType KR] [SampleableType KC] [SampleableType CCoins] [SampleableType I]
  [SampleableType K] in
theorem liftC_run {α : Type} (x : CKA.AdversaryComp Γ CCoins T I α) (h : CKAState T I) :
    (liftC x).run h = (do let a ← x; pure (a, h)) := rfl

omit [DecidableEq T] [DecidableEq M] [DecidableEq E] [DecidableEq I] [Inhabited E]
  [SampleableType KR] [SampleableType KC] [SampleableType CCoins] [SampleableType I]
  [SampleableType K] in
theorem liftH_pure {α : Type} (a : α) :
    (liftH (pure a : CHMc Γ CCoins T I α) : EMc Γ CCoins T I Sig SS RS M E α) = pure a := by
  funext es
  change (liftH (pure a : CHMc Γ CCoins T I α) : EMc Γ CCoins T I Sig SS RS M E α).run es =
    (pure a : EMc Γ CCoins T I Sig SS RS M E α).run es
  rw [liftH_run]
  simp [StateT.run_pure]

omit [DecidableEq T] [DecidableEq M] [DecidableEq E] [DecidableEq I] [Inhabited E]
  [SampleableType KR] [SampleableType KC] [SampleableType CCoins] [SampleableType I]
  [SampleableType K] in
theorem liftH_bind {α β : Type} (x : CHMc Γ CCoins T I α) (f : α → CHMc Γ CCoins T I β) :
    (liftH (x >>= f) : EMc Γ CCoins T I Sig SS RS M E β) =
      liftH x >>= fun a => liftH (f a) := by
  funext es
  change (liftH (x >>= f) : EMc Γ CCoins T I Sig SS RS M E β).run es =
    (liftH x >>= fun a => liftH (f a) : EMc Γ CCoins T I Sig SS RS M E β).run es
  simp only [liftH_run, StateT.run_bind, bind_assoc, pure_bind]

omit [DecidableEq T] [DecidableEq M] [DecidableEq E] [DecidableEq I] [Inhabited E]
  [SampleableType KR] [SampleableType KC] [SampleableType K] in
theorem Y_liftH_pure {α : Type} (a : α) (σ : JSt Γ T Sig SS RS M E I) :
    Y cka Δcka tL (liftH (pure a)) σ = pure (a, σ) := by
  rw [liftH_pure, Y_pure]

omit [DecidableEq T] [DecidableEq M] [DecidableEq E] [DecidableEq I] [Inhabited E]
  [SampleableType KR] [SampleableType KC] [SampleableType K] in
theorem Y_liftH_bind {α β : Type} (x : CHMc Γ CCoins T I α) (f : α → CHMc Γ CCoins T I β)
    (σ : JSt Γ T Sig SS RS M E I) :
    Y cka Δcka tL (liftH (x >>= f)) σ =
      Y cka Δcka tL (liftH x) σ >>= fun r => Y cka Δcka tL (liftH (f r.1)) r.2 := by
  rw [liftH_bind, Y_bind]

omit [DecidableEq T] [DecidableEq M] [DecidableEq E] [DecidableEq I] [Inhabited E]
  [SampleableType KR] [SampleableType KC] [SampleableType K] in
theorem Y_liftH_get (σ : JSt Γ T Sig SS RS M E I) :
    Y cka Δcka tL (liftH get) σ = pure (σ.1.h, σ) := by
  simp [Y, liftH_run, StateT.run_get]

omit [DecidableEq T] [DecidableEq M] [DecidableEq E] [DecidableEq I] [Inhabited E]
  [SampleableType KR] [SampleableType KC] [SampleableType K] in
theorem Y_cacheC (ep : ℕ) (x : T × I) (σ : JSt Γ T Sig SS RS M E I) :
    Y cka Δcka tL (liftH (cacheC ep x)) σ =
      pure ((), ({ σ.1 with h := { cache := Function.update σ.1.h.cache ep (some x) } }, σ.2)) := by
  simp [Y, liftH_run, cacheC, StateT.run_modify]

omit [DecidableEq T] [DecidableEq M] [DecidableEq E] [DecidableEq I] [Inhabited E]
  [SampleableType KR] [SampleableType KC] [SampleableType K] in
theorem Y_liftC {α : Type} (x : CKA.AdversaryComp Γ CCoins T I α) (σ : JSt Γ T Sig SS RS M E I) :
    Y cka Δcka tL (liftH (liftC x)) σ =
      (fun r => (r.1, (σ.1, r.2))) <$>
        (simulateQ (implC cka Δcka (healEpoch tL)) x).run σ.2 := by
  simp [Y, liftH_run, liftC_run]

omit [DecidableEq T] [DecidableEq M] [DecidableEq E] [DecidableEq I] [Inhabited E]
  [SampleableType KR] [SampleableType KC] [SampleableType K] in
theorem Y_sampleT {α : Type} [SampleableType α] (σ : JSt Γ T Sig SS RS M E I) :
    Y cka Δcka tL (liftH (StateT.lift (sampleT α))) σ =
      (fun a => (a, σ)) <$> ($ᵗ α : ProbComp α) := by
  change Y cka Δcka tL (liftH (liftC (sampleT α))) σ = _
  rw [Y_liftC]
  simp [sampleT, implC, QueryImpl.simulateQ_add_liftM_left, simulateQ_liftTarget,
    Functor.map_map]

omit [DecidableEq T] [DecidableEq M] [DecidableEq E] [DecidableEq I] [Inhabited E]
  [SampleableType KR] [SampleableType KC] [SampleableType K] in
theorem Y_coinsE (n : ℕ) (σ : JSt Γ T Sig SS RS M E I) :
    Y cka Δcka tL (coinsE n) σ =
      (fun u => (u, σ)) <$> (QueryImpl.ofLift unifSpec ProbComp n) := by
  have hrun : (coinsE n : EMc Γ CCoins T I Sig SS RS M E (Fin (n + 1))).run σ.1 =
      (do let a ← (query (spec := unifSpec + CKA.spec Γ CCoins T I) (.inl n)); pure (a, σ.1)) := rfl
  simp only [Y, hrun, simulateQ_bind, StateT.run_bind, simulateQ_pure, StateT.run_pure]
  change (fun r => (r.1.1, r.1.2, r.2)) <$>
    (((QueryImpl.ofLift unifSpec ProbComp).liftTarget (StateT (CKA.GameState Γ T) ProbComp) n).run σ.2 >>=
      fun x => pure ((x.1, σ.1), x.2)) = _
  simp [Functor.map_map]

omit [DecidableEq T] [DecidableEq M] [DecidableEq E] [DecidableEq I] [Inhabited E]
  [SampleableType KR] [SampleableType KC] [SampleableType K] in
theorem Y_sendQuery (P : Party) (σ : JSt Γ T Sig SS RS M E I) :
    Y cka Δcka tL (liftH (liftC (CKA.sendQuery P))) σ =
      (fun r => (r.1, (σ.1, r.2))) <$> (CKA.sendImpl cka (healEpoch tL) P).run σ.2 := by
  rw [Y_liftC]
  simp [CKA.sendQuery, implC, CKA.oracleImpl]

omit [DecidableEq T] [DecidableEq M] [DecidableEq E] [DecidableEq I] [Inhabited E]
  [SampleableType KR] [SampleableType KC] [SampleableType K] in
theorem Y_sendBadQuery (P : Party) (c : CCoins) (σ : JSt Γ T Sig SS RS M E I) :
    Y cka Δcka tL (liftH (liftC (CKA.sendWithAdversaryCoinsQuery P c))) σ =
      (fun r => (r.1, (σ.1, r.2))) <$> (CKA.sendWithAdversaryCoinsImpl cka (healEpoch tL) (P, c)).run σ.2 := by
  rw [Y_liftC]
  simp [CKA.sendWithAdversaryCoinsQuery, implC, CKA.oracleImpl]

omit [DecidableEq T] [DecidableEq M] [DecidableEq E] [DecidableEq I] [Inhabited E]
  [SampleableType KR] [SampleableType KC] [SampleableType K] in
theorem Y_challQuery (P : Party) (σ : JSt Γ T Sig SS RS M E I) :
    Y cka Δcka tL (liftH (liftC (CKA.challQuery P))) σ =
      (fun r => (r.1, (σ.1, r.2))) <$> (CKA.challImpl cka (healEpoch tL) P).run σ.2 := by
  rw [Y_liftC]
  simp [CKA.challQuery, implC, CKA.oracleImpl]

omit [DecidableEq T] [DecidableEq M] [DecidableEq E] [DecidableEq I] [Inhabited E]
  [SampleableType KR] [SampleableType KC] [SampleableType K] in
theorem Y_receiveQuery (P : Party) (σ : JSt Γ T Sig SS RS M E I) :
    Y cka Δcka tL (liftH (liftC (CKA.receiveQuery P))) σ =
      (fun r => (r.1, (σ.1, r.2))) <$> (CKA.receiveImpl cka P).run σ.2 := by
  rw [Y_liftC]
  simp [CKA.receiveQuery, implC, CKA.oracleImpl]

omit [DecidableEq T] [DecidableEq M] [DecidableEq E] [DecidableEq I] [Inhabited E]
  [SampleableType KR] [SampleableType KC] [SampleableType K] in
theorem Y_corrQuery (P : Party) (σ : JSt Γ T Sig SS RS M E I) :
    Y cka Δcka tL (liftH (liftC (CKA.corrQuery P))) σ =
      (fun r => (r.1, (σ.1, r.2))) <$> (CKA.corrImpl Δcka (healEpoch tL) P).run σ.2 := by
  rw [Y_liftC]
  simp [CKA.corrQuery, implC, CKA.oracleImpl]

omit [DecidableEq I] [SampleableType KR] [SampleableType KC] [SampleableType I]
  [SampleableType K] in
theorem implEc_coin (n : ℕ) :
    implEc cka prng fs Δcka qep tL t (.inl n) = coinsE n := rfl

omit [DecidableEq I] [SampleableType KR] [SampleableType KC] [SampleableType I]
  [SampleableType K] in
theorem implEc_transmit (q : Party × M × Option CCoins) :
    implEc cka prng fs Δcka qep tL t (.inr (.inl (.inl (.inl (.inl q))))) =
      transmitE (hooksCKA cka prng fs Δcka (moP tL t)) (2 + Δcka) qep (polP tL t) q := rfl

omit [DecidableEq I] [SampleableType KR] [SampleableType KC] [SampleableType I]
  [SampleableType K] in
theorem implEc_chall (q : Party × M × M × Option CCoins) :
    implEc cka prng fs Δcka qep tL t (.inr (.inl (.inl (.inl (.inr q))))) =
      challE (hooksCKA cka prng fs Δcka (moP tL t)) (2 + Δcka) qep (SM.Config.priv t)
        (polP tL t) q := rfl

omit [DecidableEq I] [SampleableType KR] [SampleableType KC] [SampleableType I]
  [SampleableType K] in
theorem implEc_deliver (q : Party × (Header T × E)) :
    implEc cka prng fs Δcka qep tL t (.inr (.inl (.inl (.inr q)))) =
      deliverE (hooksCKA cka prng fs Δcka (moP tL t)) fs.maxSkip (SM.Config.priv t) q := rfl

omit [DecidableEq I] [SampleableType KR] [SampleableType KC] [SampleableType I]
  [SampleableType K] in
theorem implEc_inject (q : Party × (Header T × E)) :
    implEc cka prng fs Δcka qep tL t (.inr (.inl (.inr q))) =
      injectE (hooksCKA cka prng fs Δcka (moP tL t)) (2 + Δcka) qep (SM.Config.priv t) q := rfl

omit [DecidableEq I] [SampleableType KR] [SampleableType KC] [SampleableType I]
  [SampleableType K] in
theorem implEc_corr (P : Party) :
    implEc cka prng fs Δcka qep tL t (.inr (.inr P)) =
      corrE (hooksCKA cka prng fs Δcka (moP tL t)) (polP tL t) P := rfl

omit [DecidableEq I] [SampleableType KR] [SampleableType KC] [SampleableType K] in
theorem abort_preserved_step
    (q : (unifSpec + SM.spec (RSt Γ T Sig SS RS) M CCoins (Header T × E)).Domain)
    {σ : JSt Γ T Sig SS RS M E I} (hab : σ.1.abort = true) :
    ∀ r ∈ support (Y cka Δcka tL (implEc cka prng fs Δcka qep tL t q) σ),
      r.2.1.abort = true := by
  rcases q with n | ((((q | q) | q) | q) | P)
  · intro r hr
    rw [implEc_coin, Y_coinsE] at hr
    simp only [support_map, Set.mem_image] at hr
    rcases hr with ⟨_, _, rfl⟩
    exact hab
  · rcases q with ⟨P, m, r⟩
    intro z hz
    rw [implEc_transmit] at hz
    simp only [transmitE, Y_bind, Y_get, pure_bind, hab, Bool.true_or,
      ↓reduceIte, Y_pure, support_pure, Set.mem_singleton_iff] at hz
    rw [hz]; exact hab
  · rcases q with ⟨P, m₀, m₁, r⟩
    intro z hz
    rw [implEc_chall] at hz
    simp only [challE, Y_bind, Y_get, pure_bind, hab, Bool.true_or,
      ↓reduceIte, Y_pure, support_pure, Set.mem_singleton_iff] at hz
    rw [hz]; exact hab
  · rcases q with ⟨P, c⟩
    intro z hz
    rw [implEc_deliver] at hz
    simp only [deliverE, Y_bind, Y_get, pure_bind, hab, Bool.true_or,
      ↓reduceIte, Y_pure, support_pure, Set.mem_singleton_iff] at hz
    rw [hz]; exact hab
  · rcases q with ⟨P, c⟩
    intro z hz
    rw [implEc_inject] at hz
    simp only [injectE, Y_bind, Y_get, pure_bind, hab, Bool.true_or,
      ↓reduceIte, Y_pure, support_pure, Set.mem_singleton_iff] at hz
    rw [hz]; exact hab
  · intro z hz
    rw [implEc_corr] at hz
    simp only [corrE, Y_bind, Y_get, pure_bind, hab, Bool.true_or,
      ↓reduceIte, Y_pure, support_pure, Set.mem_singleton_iff] at hz
    rw [hz]; exact hab

omit [DecidableEq I] [SampleableType KR] [SampleableType KC] [SampleableType K] in
theorem abort_preserved_simulateQ {α : Type}
    (oa : SM.AdversaryComp (RSt Γ T Sig SS RS) M CCoins (Header T × E) α) :
    ∀ {σ : JSt Γ T Sig SS RS M E I}, σ.1.abort = true →
      ∀ r ∈ support (Y cka Δcka tL (simulateQ (implEc cka prng fs Δcka qep tL t) oa) σ),
        r.2.1.abort = true := by
  induction oa using OracleComp.inductionOn with
  | pure a =>
    intro σ hab r hr
    simp only [simulateQ_pure, Y_pure, support_pure, Set.mem_singleton_iff] at hr
    rw [hr]; exact hab
  | query_bind q mx ih =>
    intro σ hab r hr
    simp only [simulateQ_bind, simulateQ_query, OracleQuery.input_query, OracleQuery.cont_query,
      id_map, Y_bind, mem_support_bind_iff] at hr
    rcases hr with ⟨r₁, hr₁, hr⟩
    exact ih r₁.1 (abort_preserved_step cka prng fs Δcka qep tL t q hab r₁ hr₁) r hr

omit [DecidableEq I] [SampleableType KR] [SampleableType KC] [SampleableType K] in
theorem deq_ckaEnd_of_abort (b : Bool)
    (oa : SchemeAdversary Γ T Sig SS RS M CCoins E) {σ : JSt Γ T Sig SS RS M E I}
    (hab : σ.1.abort = true) :
    DEq (Y cka Δcka tL (simulateQ (implEc cka prng fs Δcka qep tL t) oa) σ >>=
          ckaEnd Δcka tL t b)
        ($ᵗ Bool : ProbComp Bool) := by
  refine (DEq.bind_right_supp
    (Y cka Δcka tL (simulateQ (implEc cka prng fs Δcka qep tL t) oa) σ)
    (g := fun _ => ($ᵗ Bool : ProbComp Bool)) ?_).trans (DEq.bind_const _ _)
  intro r hr
  have hab' := abort_preserved_simulateQ cka prng fs Δcka qep tL t oa hab r hr
  simp only [ckaEnd, hab', Bool.not_true, Bool.false_and]
  exact DEq.refl _

abbrev implPs := implP (scheme cka prng fs lam) (2 + Δcka) qep t

def rΓ (σ : JSt Γ T Sig SS RS M E I) (P : Party) : Γ :=
  (σ.1.g.st P).γ.getD (σ.2.st P)

def projParty (vp : VPt Γ T Sig SS RS) (γck : Γ) : RSt Γ T Sig SS RS :=
  realParty vp (vp.γ.getD γck) vp.root vp.vS vp.vR

def projGame (σ : JSt Γ T Sig SS RS M E I) :
    SM.GameState (RSt Γ T Sig SS RS) M (Header T × E) :=
  { σ.1.g with st := fun P => projParty (σ.1.g.st P) (σ.2.st P) }

omit [DecidableEq T] [DecidableEq M] [DecidableEq E] [DecidableEq I] [Inhabited E]
  [SampleableType KR] [SampleableType KC] [SampleableType CCoins] [SampleableType I]
  [SampleableType K] in
theorem ckaEnd_eq_privEnd (b : Bool) (b' : Bool) (σ : JSt Γ T Sig SS RS M E I)
    (hab : σ.1.abort = false) :
    ckaEnd Δcka tL t b (b', σ) = privEnd (2 + Δcka) tL t b (b', projGame σ) := by
  simp [ckaEnd, privEnd, projGame, SM.canon, hab]

omit [DecidableEq T] [DecidableEq M] [DecidableEq E] [DecidableEq I] [Inhabited E]
  [SampleableType KR] [SampleableType KC] [SampleableType CCoins] [SampleableType I]
  [SampleableType K] in
theorem sendsIn_succ_eq_not (P : Party) (n : ℕ) :
    P.sendsIn (n + 1) = !P.sendsIn n := by
  rw [Bool.eq_iff_iff]
  cases P <;> simp [Party.sendsIn] <;> omega

omit [DecidableEq T] [DecidableEq M] [DecidableEq E] [DecidableEq I] [Inhabited E]
  [SampleableType KR] [SampleableType KC] [SampleableType CCoins] [SampleableType I]
  [SampleableType K] in
theorem sendsIn_other_eq_not (P : Party) (n : ℕ) :
    P.other.sendsIn n = !P.sendsIn n := by
  rw [Bool.eq_iff_iff]
  cases P <;> simp [Party.other, Party.sendsIn]

omit [DecidableEq T] [DecidableEq M] [DecidableEq E] [DecidableEq I] [Inhabited E]
  [SampleableType KR] [SampleableType KC] [SampleableType CCoins] [SampleableType I]
  [SampleableType K] in
theorem sendsIn_iff_eq_senderOf (P : Party) (n : ℕ) :
    P.sendsIn n = true ↔ P = Party.senderOf n := by
  cases P <;> simp [Party.sendsIn, Party.senderOf]

omit [DecidableEq T] [DecidableEq M] [DecidableEq E] [DecidableEq I] [Inhabited E]
  [SampleableType KR] [SampleableType KC] [SampleableType CCoins] [SampleableType I]
  [SampleableType K] in
theorem epMgmt_sendsIn_epoch {St : Type} {s s₁ : SM.GameState St M (Header T × E)}
    {Δ : ℕ} {P : Party} {bad : Bool}
    (h : s.epMgmt Δ qep P bad = some s₁) :
    P.sendsIn (s₁.epoch P) = true ∧ P = Party.senderOf (s₁.epoch P) := by
  have hs : P.sendsIn (s₁.epoch P) = true := by
    unfold SM.GameState.epMgmt at h
    by_cases h1 : P.sendsIn (s.epoch P + 1) = true
    · simp only [h1, ↓reduceIte] at h
      by_cases h2 : qep < s.epoch P + 1
      · simp [h2] at h
      · simp only [h2, ↓reduceIte, Option.some.injEq] at h
        subst h
        by_cases hb : (bad && !s.safeCh Δ P) = true <;> simp [hb, SM.GameState.leak, h1]
    · simp only [h1, Bool.false_eq_true, ↓reduceIte] at h
      by_cases h2 : qep < s.epoch P
      · simp [h2] at h
      · simp only [h2, ↓reduceIte, Option.some.injEq] at h
        subst h
        have hnot := sendsIn_succ_eq_not P (s.epoch P)
        revert h1 hnot; cases P.sendsIn (s.epoch P) <;> simp
  exact ⟨hs, (sendsIn_iff_eq_senderOf P (s₁.epoch P)).mp hs⟩

def DoomFixedB (Δ : ℕ) (tL : Option ℕ) (t : ℕ)
    (gs : SM.GameState (RSt Γ T Sig SS RS) M (Header T × E)) : Prop :=
  SM.lastLeakGuessAdmissible Δ tL t = false ∨ DoomD1 tL t gs ∨ ∃ l, tL = some l ∧ DoomD3 l gs

omit [DecidableEq I] [SampleableType KR] [SampleableType KC] [SampleableType I]
  [SampleableType K] in
theorem deq_privEnd_of_doomFixedB (b : Bool)
    (oa : SchemeAdversary Γ T Sig SS RS M CCoins E)
    {gs : SM.GameState (RSt Γ T Sig SS RS) M (Header T × E)}
    (hd : DoomFixedB (2 + Δcka) tL t gs) :
    DEq ((simulateQ (implPs cka prng fs lam Δcka qep t) oa).run gs >>=
          privEnd (2 + Δcka) tL t b)
        ($ᵗ Bool : ProbComp Bool) := by
  rcases hd with hvg | h1 | ⟨l, rfl, h3⟩
  · refine (DEq.bind_right ((simulateQ (implPs cka prng fs lam Δcka qep t) oa).run gs)
      (g := fun _ => ($ᵗ Bool : ProbComp Bool)) fun z => ?_).trans (DEq.bind_const _ _)
    simp only [privEnd, hvg, Bool.false_and]
    exact DEq.refl _
  · exact deq_privEnd_of_doomD1 (scheme cka prng fs lam) (2 + Δcka) qep tL t b oa h1
  · exact deq_privEnd_of_doomD3 (scheme cka prng fs lam) (2 + Δcka) qep l t b oa h3

/-- Post-challenge invariant: `senderOf t` has reached epoch `t`, and either a challenge from
`senderOf t` is in transit or `receiverOf t` has also reached epoch `t`. -/
def PostChall (t : ℕ) (g : SM.GameState (VPt Γ T Sig SS RS) M (Header T × E)) : Prop :=
  t ≤ g.epoch (Party.senderOf t) ∧
    ((∃ pos ∈ g.chall, pos.sender = Party.senderOf t) ∨ t ≤ g.epoch (Party.receiverOf t))

/-- Simulation invariant between `redCKAPriv` and `privGame`. -/
structure Inv (cka : CKAScheme KC Γ CCoins T I) (Δcka : ℕ) (tL : Option ℕ) (t : ℕ)
    (σ : JSt Γ T Sig SS RS M E I) : Prop where
  habort : σ.1.abort = false
  hckb : σ.2.b = false
  hid : ∀ P, (σ.1.g.st P).id = P
  htcur : ∀ P, (σ.1.g.st P).tcur = σ.1.g.epoch P
  hepoch_le : ∀ P, σ.1.g.epoch P ≤ σ.1.g.epoch P.other + 1
  hepoch_sync : ∀ P, P.sendsIn (σ.1.g.epoch P) = false → σ.1.g.epoch P = σ.1.g.epoch P.other
  hcomp : ∀ pos ∈ σ.1.g.comp, SM.healedBy σ.1.g.tL (2 + Δcka) pos.epoch = false
  hchall : ∀ pos ∈ σ.1.g.chall,
    pos.sender = Party.senderOf t ∧ pos.epoch = t ∧ t ≤ σ.1.g.epoch (Party.senderOf t)
  hleaks_tL : ∀ l' ∈ σ.1.g.leaks,
    ∃ l₀, σ.1.g.tL = some l₀ ∧ l' ≤ l₀ ∧ l₀ ≤ max (σ.1.g.epoch .A) (σ.1.g.epoch .B)
  htL_leaks : ∀ l₀, σ.1.g.tL = some l₀ → l₀ ∈ σ.1.g.leaks
  htrans : ∀ r ∈ σ.1.g.trans,
    r.pos.epoch ≤ σ.1.g.epoch r.pos.sender ∧
    r.ct.1.1 = r.pos.epoch ∧
    (r.pos.epoch = σ.1.g.epoch r.pos.sender.other + 1 →
      r.ct.1.2 = (σ.1.g.st r.pos.sender).curCkaMsg)
  hγ_none : tL = none → ∀ P, (σ.1.g.st P).γ.isSome = true
  hγ_some : ∀ l, tL = some l → ∀ P,
    (σ.1.g.st P).γ.isSome = decide (healEpoch tL + Δcka ≤ σ.1.g.epoch P) ∧
    σ.2.epoch P = min (σ.1.g.epoch P) (healEpoch tL + Δcka)
  hcka_sync : ∀ P, σ.1.g.epoch P = σ.1.g.epoch P.other →
    P.sendsIn (σ.1.g.epoch P + 1) = true →
    ∀ rs, cka.AgreesFrom (rΓ σ P) (rΓ σ P.other) rs
  hcka_split : ∀ P, σ.1.g.epoch P = σ.1.g.epoch P.other + 1 →
    ∃ T_e : T,
      (σ.1.g.st P).curCkaMsg = some T_e ∧
      σ.1.h.cache (σ.1.g.epoch P) = some (T_e, (cka.receive (rΓ σ P.other) T_e).2) ∧
      ((σ.1.g.st P.other).γ = none → σ.2.lastMsg = some T_e) ∧
      ∀ rs, cka.AgreesFrom (cka.receive (rΓ σ P.other) T_e).1 (rΓ σ P) rs

omit [Inhabited E] [DecidableEq T] [DecidableEq M] [DecidableEq E] [DecidableEq I]
  [SampleableType KR] [SampleableType KC] [SampleableType CCoins] [SampleableType I]
  [SampleableType K] in
theorem postChall_accept {σ : JSt Γ T Sig SS RS M E I}
    (hI : Inv cka Δcka tL t σ) (hp : PostChall t σ.1.g)
    (P : Party) (st' : VPt Γ T Sig SS RS) (pos : SM.Pos) (hpos : pos.sender = P.other) :
    PostChall t (σ.1.g.accept P st' pos) := by
  have hep_le : ∀ Q, σ.1.g.epoch Q ≤ (σ.1.g.accept P st' pos).epoch Q := fun Q => by
    by_cases hQ : Q = P
    · subst hQ; simp [SM.GameState.accept, SM.GameState.delete]
    · simp [SM.GameState.accept, SM.GameState.delete, hQ]
  rcases hp with ⟨hS, ⟨pos₀, hmem, hsend⟩ | hR⟩
  · refine ⟨hS.trans (hep_le _), ?_⟩
    by_cases heq : pos₀ = pos
    · subst heq
      have hch := hI.hchall pos₀ hmem
      have hP : P = Party.receiverOf t := by
        have h1 : P.other = Party.senderOf t := hpos.symm.trans hch.1
        rw [← Party.other_other P, h1]
        rfl
      apply Or.inr
      subst hP
      simp [SM.GameState.accept, SM.GameState.delete, hch.2.1]
    · apply Or.inl
      refine ⟨pos₀, ?_, hsend⟩
      simp [SM.GameState.accept, SM.GameState.delete, List.mem_filter, hmem, heq]
  · exact ⟨hS.trans (hep_le _), Or.inr (hR.trans (hep_le _))⟩

abbrev initJStNone (kr : KR) (kc kc₀ : KC) (b : Bool) : JSt Γ T Sig SS RS M E I :=
  let out := prng.up (prng.init kr) lam
  let vs := mkParties (T := T) (some (cka.initA kc)) (some (cka.initB kc))
    out.1 (fs.initSender out.2) (fs.initReceiver out.2)
  ({ g := { st := fun P => match P with | .A => vs.1 | .B => vs.2, b := b }, h := {} },
   CKA.initState cka kc₀ false)

abbrev initJStSome (kr : KR) (kc : KC) (b : Bool) : JSt Γ T Sig SS RS M E I :=
  let out := prng.up (prng.init kr) lam
  let vs := mkParties (T := T) (none : Option Γ) (none : Option Γ)
    out.1 (fs.initSender out.2) (fs.initReceiver out.2)
  ({ g := { st := fun P => match P with | .A => vs.1 | .B => vs.2, b := b }, h := {} },
   CKA.initState cka kc false)

omit [DecidableEq T] [DecidableEq M] [DecidableEq E] [DecidableEq I]
  [SampleableType KR] [SampleableType KC] [SampleableType CCoins] [SampleableType I]
  [SampleableType K] in
theorem init_inv_none (hc : cka.Correct) (kr : KR) (kc kc₀ : KC) (b : Bool) :
    projGame (initJStNone cka prng fs lam kr kc kc₀ b) =
      SM.initState (scheme cka prng fs lam) (kr, kc) b ∧
      Inv cka Δcka none t (initJStNone cka prng fs lam kr kc kc₀ b) := by
  let out := prng.up (prng.init kr) lam
  let vs := mkParties (T := T) (some (cka.initA kc)) (some (cka.initB kc))
    out.1 (fs.initSender out.2) (fs.initReceiver out.2)
  let g₀ : SM.GameState (VPt Γ T Sig SS RS) M (Header T × E) :=
    { st := fun P => match P with | .A => vs.1 | .B => vs.2, b := b }
  let σ₀ : JSt Γ T Sig SS RS M E I :=
    ({ g := g₀, h := {} }, CKA.initState cka kc₀ false)
  change projGame σ₀ = SM.initState (scheme cka prng fs lam) (kr, kc) b ∧
    Inv cka Δcka none t σ₀
  refine ⟨?_, ?_⟩
  · dsimp only [projGame, σ₀, g₀, SM.initState]
    congr 1
    funext P
    cases P <;> rfl
  · refine
      { habort := rfl
        hckb := rfl
        hid := fun P => by cases P <;> rfl
        htcur := fun P => by cases P <;> rfl
        hepoch_le := fun _ => Nat.le_succ 0
        hepoch_sync := fun _ _ => rfl
        hcomp := fun _ h => nomatch h
        hchall := fun _ h => nomatch h
        hleaks_tL := fun _ h => nomatch h
        htL_leaks := fun _ h => nomatch h
        htrans := fun _ h => nomatch h
        hγ_none := fun _ P => by cases P <;> rfl
        hγ_some := fun _ h => nomatch h
        hcka_sync := fun P _ hs rs => by
          cases P with
          | A => exact hc kc rs
          | B => simp [σ₀, g₀, Party.sendsIn] at hs
        hcka_split := fun _ h => by simp [σ₀, g₀] at h }

omit [DecidableEq T] [DecidableEq M] [DecidableEq E] [DecidableEq I]
  [SampleableType KR] [SampleableType KC] [SampleableType CCoins] [SampleableType I]
  [SampleableType K] in
theorem init_inv_some (hc : cka.Correct) (l : ℕ) (kr : KR) (kc : KC) (b : Bool) :
    projGame (initJStSome cka prng fs lam kr kc b) =
      SM.initState (scheme cka prng fs lam) (kr, kc) b ∧
      Inv cka Δcka (some l) t (initJStSome cka prng fs lam kr kc b) := by
  let out := prng.up (prng.init kr) lam
  let vs := mkParties (T := T) (none : Option Γ) (none : Option Γ)
    out.1 (fs.initSender out.2) (fs.initReceiver out.2)
  let g₀ : SM.GameState (VPt Γ T Sig SS RS) M (Header T × E) :=
    { st := fun P => match P with | .A => vs.1 | .B => vs.2, b := b }
  let σ₀ : JSt Γ T Sig SS RS M E I :=
    ({ g := g₀, h := {} }, CKA.initState cka kc false)
  change projGame σ₀ = SM.initState (scheme cka prng fs lam) (kr, kc) b ∧
    Inv cka Δcka (some l) t σ₀
  refine ⟨?_, ?_⟩
  · dsimp only [projGame, σ₀, g₀, SM.initState]
    congr 1
    funext P
    cases P <;> rfl
  · refine
      { habort := rfl
        hckb := rfl
        hid := fun P => by cases P <;> rfl
        htcur := fun P => by cases P <;> rfl
        hepoch_le := fun _ => Nat.le_succ 0
        hepoch_sync := fun _ _ => rfl
        hcomp := fun _ h => nomatch h
        hchall := fun _ h => nomatch h
        hleaks_tL := fun _ h => nomatch h
        htL_leaks := fun _ h => nomatch h
        htrans := fun _ h => nomatch h
        hγ_none := fun h => nomatch h
        hγ_some := fun l' hl P => by
          cases hl
          cases P <;> simp [σ₀, g₀, vs, mkParties, CKA.initState, healEpoch]
        hcka_sync := fun P _ hs rs => by
          cases P with
          | A => exact hc kc rs
          | B => simp [σ₀, g₀, Party.sendsIn] at hs
        hcka_split := fun _ h => by simp [σ₀, g₀] at h }

omit [DecidableEq I] [SampleableType KR] [SampleableType KC] [SampleableType K] in
theorem step_coin (n : ℕ) {σ : JSt Γ T Sig SS RS M E I} (hI : Inv cka Δcka tL t σ) :
    DEq ((implPs cka prng fs lam Δcka qep t (.inl n)).run (projGame σ))
        ((fun r => (r.1, projGame r.2)) <$>
          Y cka Δcka tL (implEc cka prng fs Δcka qep tL t (.inl n)) σ) ∧
      ∀ r ∈ support (Y cka Δcka tL (implEc cka prng fs Δcka qep tL t (.inl n)) σ),
        Inv cka Δcka tL t r.2 ∧ (PostChall t σ.1.g → PostChall t r.2.1.g) := by
  rw [implP_coin, implEc_coin, Y_coinsE]
  have hrun : (QueryImpl.ofLift unifSpec ProbComp n) =
      ($ᵗ (Fin (n + 1)) : ProbComp (Fin (n + 1))) := rfl
  rw [hrun, Functor.map_map]
  refine ⟨DEq.refl _, fun r hr => ?_⟩
  simp only [map_eq_bind_pure_comp, Function.comp_apply, mem_support_bind_iff,
    support_pure, Set.mem_singleton_iff] at hr
  rcases hr with ⟨u, _, rfl⟩
  exact ⟨hI, id⟩

def updVR {γ : Type} (st : PartyState γ T Sig SS RS) (e : ℕ) (v : Option RS) :
    PartyState γ T Sig SS RS :=
  { st with vR := Function.update st.vR e v }

omit [Inhabited E] [DecidableEq T] [DecidableEq M] [DecidableEq E] [DecidableEq I]
  [SampleableType KR] [SampleableType KC] [SampleableType CCoins] [SampleableType I]
  [SampleableType K] in
theorem inv_accept_updVR {σ : JSt Γ T Sig SS RS M E I}
    (hI : Inv cka Δcka tL t σ) (P : Party) (e : ℕ) (v' : RS) (pos : SM.Pos)
    (hle : pos.epoch ≤ σ.1.g.epoch P) :
    let st' : VPt Γ T Sig SS RS := updVR (σ.1.g.st P) e (some v')
    let σ' : JSt Γ T Sig SS RS M E I := ({ σ.1 with g := σ.1.g.accept P st' pos }, σ.2)
    (projGame σ).accept P (updVR ((projGame σ).st P) e (some v')) pos = projGame σ' ∧
      Inv cka Δcka tL t σ' := by
  intro st' σ'
  have hmax : max (σ.1.g.epoch P) pos.epoch = σ.1.g.epoch P := Nat.max_eq_left hle
  refine ⟨?_, ?_⟩
  · dsimp only [SM.GameState.accept, SM.GameState.delete, projGame, σ', st']
    congr 1
    funext Q
    by_cases hQ : Q = P
    · subst hQ; simp [updVR, projParty, realParty]
    · simp [hQ]
  · have hep' : ∀ Q, σ'.1.g.epoch Q = σ.1.g.epoch Q := fun Q => by
      by_cases hQ : Q = P
      · subst hQ; simp [σ', SM.GameState.accept, SM.GameState.delete, hmax]
      · simp [σ', SM.GameState.accept, SM.GameState.delete, hQ]
    have hrΓ' : ∀ Q, rΓ σ' Q = rΓ σ Q := fun Q => by
      by_cases hQ : Q = P <;> simp [rΓ, σ', st', updVR, SM.GameState.accept,
        SM.GameState.delete, hQ]
    have hTcur' : ∀ Q, (σ'.1.g.st Q).curCkaMsg = (σ.1.g.st Q).curCkaMsg := fun Q => by
      by_cases hQ : Q = P <;> simp [σ', st', updVR, SM.GameState.accept,
        SM.GameState.delete, hQ]
    have hγ' : ∀ Q, (σ'.1.g.st Q).γ = (σ.1.g.st Q).γ := fun Q => by
      by_cases hQ : Q = P <;> simp [σ', st', updVR, SM.GameState.accept,
        SM.GameState.delete, hQ]
    exact
      { habort := hI.habort
        hckb := hI.hckb
        hid := fun Q => by
          by_cases hQ : Q = P
          · subst hQ; simp [σ', st', updVR, SM.GameState.accept, SM.GameState.delete, hI.hid Q]
          · simp [σ', SM.GameState.accept, SM.GameState.delete, hQ, hI.hid Q]
        htcur := fun Q => by
          rw [hep' Q]
          by_cases hQ : Q = P
          · subst hQ; simp [σ', st', updVR, SM.GameState.accept, SM.GameState.delete, hI.htcur Q]
          · simp [σ', SM.GameState.accept, SM.GameState.delete, hQ, hI.htcur Q]
        hepoch_le := fun Q => by rw [hep' Q, hep' Q.other]; exact hI.hepoch_le Q
        hepoch_sync := fun Q h => by
          rw [hep' Q] at h ⊢; rw [hep' Q.other]; exact hI.hepoch_sync Q h
        hcomp := fun pos' hpos' => by
          simp only [σ', SM.GameState.accept, SM.GameState.delete, List.mem_filter] at hpos'
          exact hI.hcomp pos' hpos'.1
        hchall := fun pos' hpos' => by
          simp only [σ', SM.GameState.accept, SM.GameState.delete, List.mem_filter] at hpos'
          rw [hep']; exact hI.hchall pos' hpos'.1
        hleaks_tL := fun l' hl' => by
          rw [hep' .A, hep' .B]; exact hI.hleaks_tL l' hl'
        htL_leaks := hI.htL_leaks
        htrans := fun r hr => by
          simp only [σ', SM.GameState.accept, SM.GameState.delete, List.mem_filter] at hr
          rw [hep' r.pos.sender, hep' r.pos.sender.other, hTcur' r.pos.sender]
          exact hI.htrans r hr.1
        hγ_none := fun hn Q => by rw [hγ' Q]; exact hI.hγ_none hn Q
        hγ_some := fun l hl Q => by rw [hγ' Q, hep' Q]; exact hI.hγ_some l hl Q
        hcka_sync := fun Q h1 h2 rs => by
          rw [hep' Q, hep' Q.other] at h1
          rw [hep' Q] at h2
          rw [hrΓ' Q, hrΓ' Q.other]
          exact hI.hcka_sync Q h1 h2 rs
        hcka_split := fun Q h1 => by
          rw [hep' Q, hep' Q.other] at h1
          rw [hep' Q, hTcur' Q, hγ' Q.other, hrΓ' Q, hrΓ' Q.other]
          exact hI.hcka_split Q h1 }

omit [DecidableEq T] [DecidableEq M] [DecidableEq E] [DecidableEq I]
  [SampleableType KR] [SampleableType KC] [SampleableType CCoins] [SampleableType I]
  [SampleableType K] in
theorem receive_ne_succ (P : Party) (c : Header T × E) (σ : JSt Γ T Sig SS RS M E I)
    (hne : c.1.1 ≠ (σ.1.g.st P).tcur + 1) :
    (scheme cka prng fs lam).receive ((projGame σ).st P) c =
      if (σ.1.g.st P).id.sendsIn c.1.1 || decide ((σ.1.g.st P).tcur + 1 < c.1.1) then none
      else match (σ.1.g.st P).vR c.1.1 with
        | none => none
        | some v =>
          match fs.receive v c.1 c.2 with
          | none => none
          | some (v', i, m') =>
            some (updVR ((projGame σ).st P) c.1.1 (some v'), c.1.1, i, m') := by
  dsimp only [scheme]
  unfold receive updVR
  dsimp only
  have hid : ((projGame σ).st P).id = (σ.1.g.st P).id := rfl
  have htcur : ((projGame σ).st P).tcur = (σ.1.g.st P).tcur := rfl
  have hvR : ((projGame σ).st P).vR = (σ.1.g.st P).vR := rfl
  simp only [hid, htcur, hvR, hne, ↓reduceIte]
  split_ifs with hbad
  · rfl
  · cases hv : (σ.1.g.st P).vR c.1.1 with
    | none => rfl
    | some v =>
      cases hfs : fs.receive v c.1 c.2 with
      | none => rfl
      | some res => rcases res with ⟨v', i, m'⟩; rfl

omit [DecidableEq M] [DecidableEq E] [DecidableEq I] [Inhabited E]
  [SampleableType KR] [SampleableType KC] [SampleableType K] in
theorem Y_vRecv_ne_succ (P : Party) (c : Header T × E)
    (rec : Option (SM.Record M (Header T × E))) (σ : JSt Γ T Sig SS RS M E I)
    (hne : c.1.1 ≠ (σ.1.g.st P).tcur + 1) :
    Y cka Δcka tL
      (liftH (vRecv (hooksCKA cka prng fs Δcka (moP tL t)) σ.1.g P (σ.1.g.st P) c rec)) σ =
      pure (some (
        if (σ.1.g.st P).id.sendsIn c.1.1 || decide ((σ.1.g.st P).tcur + 1 < c.1.1) then none
        else match (σ.1.g.st P).vR c.1.1 with
          | none => none
          | some v =>
            match fs.receive v c.1 c.2 with
            | none => none
            | some (v', i, m') =>
              some (updVR (σ.1.g.st P) c.1.1 (some v'), c.1.1, i, m')), σ) := by
  unfold vRecv updVR
  dsimp only
  simp only [hne, ↓reduceIte, pure_bind]
  by_cases hbad : ((σ.1.g.st P).id.sendsIn c.1.1 || decide ((σ.1.g.st P).tcur + 1 < c.1.1)) = true
  · simp [hbad, Y_liftH_pure]
  · simp only [hbad, Bool.false_eq_true, ↓reduceIte]
    rcases (σ.1.g.st P).vR c.1.1 with _ | v
    · simp [Y_liftH_pure]
    · dsimp only [hooksCKA, pure_bind]
      rcases fs.receive v c.1 c.2 with _ | ⟨v', i', m'⟩
      · simp [Y_liftH_pure]
      · simp [Y_liftH_pure]

omit [DecidableEq M] [DecidableEq E] [DecidableEq I] [Inhabited E]
  [SampleableType KR] [SampleableType KC] [SampleableType K] in
theorem Y_vRecv_eq_succ_shape (P : Party) (c : Header T × E)
    (rec : Option (SM.Record M (Header T × E))) (σ : JSt Γ T Sig SS RS M E I)
    (heq : c.1.1 = (σ.1.g.st P).tcur + 1) :
    (Y cka Δcka tL
      (liftH (vRecv (hooksCKA cka prng fs Δcka (moP tL t)) σ.1.g P (σ.1.g.st P) c rec)) σ =
        pure (some none, σ)) ∨
    ∃ st' i' m',
      Y cka Δcka tL
        (liftH (vRecv (hooksCKA cka prng fs Δcka (moP tL t)) σ.1.g P (σ.1.g.st P) c rec)) σ =
          pure (some (some (st', c.1.1, i', m')), σ) := by
  unfold vRecv
  by_cases hbad : ((σ.1.g.st P).id.sendsIn c.1.1 || decide ((σ.1.g.st P).tcur + 1 < c.1.1)) = true
  · left; simp [hbad, Y_liftH_pure]
  · simp only [hbad, Bool.false_eq_true, ↓reduceIte]
    simp only [heq, ↓reduceIte]
    cases hc2 : c.1.2 with
    | none =>
      left; simp [Y_liftH_pure]
    | some Tn =>
      simp only [hooksCKA, moP, Bool.false_and, Y_liftH_bind, Y_liftH_get, pure_bind]
      cases hcache : σ.1.h.cache ((σ.1.g.st P).tcur + 1) with
      | none =>
        left; simp [Y_liftH_pure]
      | some p =>
        rcases p with ⟨Tc, Ik⟩
        by_cases hT : Tc = Tn
        · simp only [hT, ↓reduceIte, Y_liftH_pure, pure_bind, Function.update_self]
          let s₁ : VPt Γ T Sig SS RS :=
            { σ.1.g.st P with
              tcur := (σ.1.g.st P).tcur + 1
              γ := Option.map (fun γ => (cka.receive γ Tn).1) (σ.1.g.st P).γ
              root := (prng.up (σ.1.g.st P).root Ik).1
              vR := Function.update (σ.1.g.st P).vR ((σ.1.g.st P).tcur + 1)
                (some (fs.initReceiver (prng.up (σ.1.g.st P).root Ik).2)) }
          cases hfs : fs.receive (fs.initReceiver (prng.up (σ.1.g.st P).root Ik).2) c.1 c.2 with
          | none =>
            left; simp [Y_liftH_pure]
          | some res =>
            rcases res with ⟨v', i', m'⟩
            right
            refine ⟨{ s₁ with vR := Function.update s₁.vR ((σ.1.g.st P).tcur + 1) (some v') },
              i', m', ?_⟩
            simp [s₁, Y_liftH_pure]
        · left; simp [hT, Y_liftH_pure]

omit [DecidableEq T] [DecidableEq M] [DecidableEq E] [DecidableEq I] [Inhabited E]
  [SampleableType KR] [SampleableType KC] [SampleableType CCoins] [SampleableType I]
  [SampleableType K] in
theorem trivial_succ_epoch_false {σ : JSt Γ T Sig SS RS M E I}
    (hI : Inv cka Δcka tL t σ) (P : Party) (i' : ℕ)
    (hsafe : σ.1.g.safeInj (2 + Δcka) = true) :
    σ.1.g.trivial (2 + Δcka) ⟨P.other, (σ.1.g.st P).tcur + 1, i'⟩ = false := by
  rw [hI.htcur P]
  have hheal : SM.healedBy σ.1.g.tL (2 + Δcka) (σ.1.g.epoch P + 1) = true := by
    unfold SM.GameState.safeInj at hsafe
    cases htL : σ.1.g.tL with
    | none => rfl
    | some l₀ =>
      simp only [htL, SM.healedBy, decide_eq_true_eq] at hsafe ⊢
      cases P <;> omega
  have hnot_mem : ⟨P.other, σ.1.g.epoch P + 1, i'⟩ ∉ σ.1.g.comp := by
    intro hmem
    have hf := hI.hcomp _ hmem
    simp [hheal] at hf
  simp [SM.GameState.trivial, hnot_mem, hheal]

omit [DecidableEq M] [DecidableEq E] [DecidableEq I] [Inhabited E]
  [SampleableType KR] [SampleableType KC] [SampleableType K] in
theorem Y_commitE_of_tcur_eq (P : Party) (st' : VPt Γ T Sig SS RS) (pos : SM.Pos)
    (σ : JSt Γ T Sig SS RS M E I) (htcur : st'.tcur = (σ.1.g.st P).tcur) :
    Y cka Δcka tL
      (commitE (hooksCKA cka prng fs Δcka (moP tL t)) σ.1.g P (σ.1.g.st P) st' pos) σ =
      pure (some (σ.1.g.accept P st' pos), σ) := by
  unfold commitE hooksCKA
  simp only [htcur, Nat.lt_irrefl, decide_false, Bool.false_and, Bool.false_eq_true, ↓reduceIte,
    Y_bind, Y_liftH_pure, pure_bind, Y_pure]
  dsimp only [SM.GameState.accept]
  congr 4
  funext Q
  by_cases hQ : Q = P <;> simp [hQ]

omit [DecidableEq T] [DecidableEq M] [DecidableEq E] [DecidableEq I]
  [SampleableType KR] [SampleableType KC] [SampleableType CCoins] [SampleableType I]
  [SampleableType K] in
theorem receive_eq_succ_shape (P : Party) (c : Header T × E) (σ : JSt Γ T Sig SS RS M E I)
    (heq : c.1.1 = (σ.1.g.st P).tcur + 1) :
    ((scheme cka prng fs lam).receive ((projGame σ).st P) c = none) ∨
    ∃ st' i' m',
      (scheme cka prng fs lam).receive ((projGame σ).st P) c =
        some (st', (σ.1.g.st P).tcur + 1, i', m') := by
  dsimp only [scheme]
  unfold receive
  dsimp only
  have hid : ((projGame σ).st P).id = (σ.1.g.st P).id := rfl
  have htcur : ((projGame σ).st P).tcur = (σ.1.g.st P).tcur := rfl
  simp only [hid, htcur, heq, ↓reduceIte]
  split_ifs with hb
  · left; rfl
  · cases c.1.2 with
    | none => left; rfl
    | some Tn =>
      simp only [Function.update_self]
      rcases fs.receive (fs.initReceiver (prng.up ((projGame σ).st P).root
          (cka.receive ((projGame σ).st P).γ Tn).2).2) c.1 c.2 with _ | ⟨v', i', m'⟩
      · left; rfl
      · right; exact ⟨_, i', m', rfl⟩

omit [DecidableEq I] [SampleableType KR] [SampleableType KC] [SampleableType K] in
theorem step_inject (P : Party) (c : Header T × E) {σ : JSt Γ T Sig SS RS M E I}
    (hI : Inv cka Δcka tL t σ) :
    DEq ((implPs cka prng fs lam Δcka qep t (.inr (.inl (.inr (P, c))))).run (projGame σ))
        ((fun r => (r.1, projGame r.2)) <$>
          Y cka Δcka tL (implEc cka prng fs Δcka qep tL t (.inr (.inl (.inr (P, c))))) σ) ∧
      ∀ r ∈ support (Y cka Δcka tL (implEc cka prng fs Δcka qep tL t (.inr (.inl (.inr (P, c))))) σ),
        Inv cka Δcka tL t r.2 ∧ (PostChall t σ.1.g → PostChall t r.2.1.g) := by
  unfold implPs
  rw [implP_inject, implEc_inject]
  have hab : σ.1.abort = false := hI.habort
  have hwin : (projGame σ).win = σ.1.g.win := rfl
  have hinT : (projGame σ).inTransit P.other c = σ.1.g.inTransit P.other c := rfl
  have hsafe : (projGame σ).safeInj (2 + Δcka) = σ.1.g.safeInj (2 + Δcka) := rfl
  simp only [SM.injectImpl, injectE, SM.Config.priv, Bool.false_eq_true, ↓reduceIte,
    StateT.run_bind, StateT.run_get, Y_bind, Y_get, pure_bind, hab, Bool.false_or, hwin, hinT, hsafe]
  by_cases hguard : (σ.1.g.win || (σ.1.g.inTransit P.other c).isSome || !σ.1.g.safeInj (2 + Δcka)) = true
  · simp only [hguard, ↓reduceIte, StateT.run_pure, Y_pure, map_pure]
    exact ⟨DEq.refl _, fun r hr => by
      rw [support_pure, Set.mem_singleton_iff] at hr; rw [hr]; exact ⟨hI, id⟩⟩
  · simp only [hguard, Bool.false_eq_true, ↓reduceIte]
    have hsafe_true : σ.1.g.safeInj (2 + Δcka) = true := by
      revert hguard; cases σ.1.g.win <;> cases (σ.1.g.inTransit P.other c).isSome <;>
        cases σ.1.g.safeInj (2 + Δcka) <;> decide
    by_cases heq : c.1.1 = (σ.1.g.st P).tcur + 1
    · rw [Y_bind]
      rcases receive_eq_succ_shape cka prng fs lam P c σ heq with hL | ⟨stL, iL, mL, hL⟩ <;>
        rcases Y_vRecv_eq_succ_shape cka prng fs Δcka tL t P c none σ heq with hR | ⟨stR, iR, mR, hR⟩
      · simp only [hL, hR, pure_bind, StateT.run_pure, Y_pure, map_pure]
        exact ⟨DEq.refl _, fun r hr => by
          rw [support_pure, Set.mem_singleton_iff] at hr; rw [hr]; exact ⟨hI, id⟩⟩
      · have htrivR : σ.1.g.trivial (2 + Δcka) ⟨P.other, c.1.1, iR⟩ = false := by
          rw [heq]; exact trivial_succ_epoch_false cka Δcka tL t hI P iR hsafe_true
        simp only [hL, hR, pure_bind, htrivR, Bool.false_eq_true, ↓reduceIte, ite_self,
          StateT.run_pure, Y_pure, map_pure]
        exact ⟨DEq.refl _, fun r hr => by
          rw [support_pure, Set.mem_singleton_iff] at hr; rw [hr]; exact ⟨hI, id⟩⟩
      · have htrivL : (projGame σ).trivial (2 + Δcka) ⟨P.other, (σ.1.g.st P).tcur + 1, iL⟩ = false :=
          trivial_succ_epoch_false cka Δcka tL t hI P iL hsafe_true
        simp only [hL, hR, pure_bind, htrivL, Bool.false_eq_true, ↓reduceIte, ite_self,
          StateT.run_pure, Y_pure, map_pure]
        exact ⟨DEq.refl _, fun r hr => by
          rw [support_pure, Set.mem_singleton_iff] at hr; rw [hr]; exact ⟨hI, id⟩⟩
      · have htrivL : (projGame σ).trivial (2 + Δcka) ⟨P.other, (σ.1.g.st P).tcur + 1, iL⟩ = false :=
          trivial_succ_epoch_false cka Δcka tL t hI P iL hsafe_true
        have htrivR : σ.1.g.trivial (2 + Δcka) ⟨P.other, c.1.1, iR⟩ = false := by
          rw [heq]; exact trivial_succ_epoch_false cka Δcka tL t hI P iR hsafe_true
        simp only [hL, hR, pure_bind, htrivL, htrivR, Bool.false_eq_true, ↓reduceIte, ite_self,
          StateT.run_pure, Y_pure, map_pure]
        exact ⟨DEq.refl _, fun r hr => by
          rw [support_pure, Set.mem_singleton_iff] at hr; rw [hr]; exact ⟨hI, id⟩⟩
    · rw [receive_ne_succ cka prng fs lam P c σ heq, Y_bind,
        Y_vRecv_ne_succ cka prng fs Δcka tL t P c none σ heq, pure_bind]
      by_cases hbad : ((σ.1.g.st P).id.sendsIn c.1.1 || decide ((σ.1.g.st P).tcur + 1 < c.1.1)) = true
      · simp only [hbad, ↓reduceIte, StateT.run_pure, Y_pure, map_pure]
        exact ⟨DEq.refl _, fun r hr => by
          rw [support_pure, Set.mem_singleton_iff] at hr; rw [hr]; exact ⟨hI, id⟩⟩
      · simp only [hbad, Bool.false_eq_true, ↓reduceIte]
        rcases (σ.1.g.st P).vR c.1.1 with _ | v
        · simp only [StateT.run_pure, Y_pure, map_pure]
          exact ⟨DEq.refl _, fun r hr => by
            rw [support_pure, Set.mem_singleton_iff] at hr; rw [hr]; exact ⟨hI, id⟩⟩
        · dsimp only
          rcases fs.receive v c.1 c.2 with _ | ⟨v', i', m'⟩
          · simp only [StateT.run_pure, Y_pure, map_pure]
            exact ⟨DEq.refl _, fun r hr => by
              rw [support_pure, Set.mem_singleton_iff] at hr; rw [hr]; exact ⟨hI, id⟩⟩
          · dsimp only
            by_cases hqep : qep + 1 < c.1.1
            · simp only [hqep, ↓reduceIte, StateT.run_pure, Y_pure, map_pure]
              exact ⟨DEq.refl _, fun r hr => by
                rw [support_pure, Set.mem_singleton_iff] at hr; rw [hr]; exact ⟨hI, id⟩⟩
            · simp only [hqep, ↓reduceIte]
              have htriv_eq : (projGame σ).trivial (2 + Δcka) ⟨P.other, c.1.1, i'⟩ =
                  σ.1.g.trivial (2 + Δcka) ⟨P.other, c.1.1, i'⟩ := rfl
              rw [htriv_eq]
              by_cases htriv : σ.1.g.trivial (2 + Δcka) ⟨P.other, c.1.1, i'⟩ = true
              · have hle : c.1.1 ≤ σ.1.g.epoch P := by
                  have : ¬ ((σ.1.g.st P).tcur + 1 < c.1.1) := by
                    revert hbad; cases (σ.1.g.st P).id.sendsIn c.1.1 <;> simp
                  have ht := hI.htcur P
                  omega
                let st' : VPt Γ T Sig SS RS := updVR (σ.1.g.st P) c.1.1 (some v')
                have hcommit : Y cka Δcka tL
                    (commitE (hooksCKA cka prng fs Δcka (moP tL t)) σ.1.g P (σ.1.g.st P)
                      (updVR (σ.1.g.st P) c.1.1 (some v')) ⟨P.other, c.1.1, i'⟩) σ =
                    pure (some (σ.1.g.accept P st' ⟨P.other, c.1.1, i'⟩), σ) :=
                  Y_commitE_of_tcur_eq cka prng fs Δcka tL t P st' ⟨P.other, c.1.1, i'⟩ σ rfl
                simp only [htriv, ↓reduceIte, StateT.run_bind, StateT.run_set, pure_bind,
                  StateT.run_pure, Y_bind, hcommit, Y_modify, Y_pure, map_pure]
                obtain ⟨hproj, hI'⟩ :=
                  inv_accept_updVR cka Δcka tL t hI P c.1.1 v' ⟨P.other, c.1.1, i'⟩ hle
                rw [hproj]
                refine ⟨DEq.refl _, fun r hr => ?_⟩
                rw [support_pure, Set.mem_singleton_iff] at hr
                rw [hr]
                exact ⟨hI', fun hp => postChall_accept cka Δcka tL t hI hp P st' ⟨P.other, c.1.1, i'⟩ rfl⟩
              · simp only [htriv, Bool.false_eq_true, ↓reduceIte, StateT.run_pure,
                  Y_pure, map_pure]
                exact ⟨DEq.refl _, fun r hr => by
                  rw [support_pure, Set.mem_singleton_iff] at hr; rw [hr]; exact ⟨hI, id⟩⟩

def updVRStart {γ : Type} (prng : PRFPRNG KR Sig I K)
    (fs : FSAEADScheme K SS RS (Header T) M E)
    (st : PartyState γ T Sig SS RS) (γ' : γ) (Ik : I) (v' : RS) :
    PartyState γ T Sig SS RS :=
  let e := st.tcur + 1
  let p := prng.up st.root Ik
  let vR₁ := Function.update st.vR e (some (fs.initReceiver p.2))
  { st with tcur := e, γ := γ', root := p.1, vR := Function.update vR₁ e (some v') }

omit [DecidableEq T] [DecidableEq M] [DecidableEq E] [DecidableEq I]
  [SampleableType KR] [SampleableType KC] [SampleableType CCoins] [SampleableType I]
  [SampleableType K] in
theorem receive_eq_succ_of_cache (P : Party) (c : Header T × E) (T_e : T)
    (σ : JSt Γ T Sig SS RS M E I)
    (heq : c.1.1 = (σ.1.g.st P).tcur + 1) (hc2 : c.1.2 = some T_e) :
    (scheme cka prng fs lam).receive ((projGame σ).st P) c =
      if (σ.1.g.st P).id.sendsIn c.1.1 then none
      else
        let k := cka.receive (rΓ σ P) T_e
        let p := prng.up (σ.1.g.st P).root k.2
        match fs.receive (fs.initReceiver p.2) c.1 c.2 with
        | none => none
        | some (v', i, m') =>
          some (updVRStart prng fs ((projGame σ).st P) k.1 k.2 v', c.1.1, i, m') := by
  dsimp only [scheme]
  unfold receive updVRStart
  dsimp only
  have hid : ((projGame σ).st P).id = (σ.1.g.st P).id := rfl
  have htcur : ((projGame σ).st P).tcur = (σ.1.g.st P).tcur := rfl
  have hroot : ((projGame σ).st P).root = (σ.1.g.st P).root := rfl
  have hvR : ((projGame σ).st P).vR = (σ.1.g.st P).vR := rfl
  have hγ : ((projGame σ).st P).γ = rΓ σ P := rfl
  simp only [hid, htcur, hroot, hvR, hγ, heq, Nat.lt_irrefl, decide_false, Bool.or_false,
    ↓reduceIte, hc2, Function.update_self]
  split_ifs with hs
  · rfl
  · cases fs.receive (fs.initReceiver (prng.up (σ.1.g.st P).root (cka.receive (rΓ σ P) T_e).2).2) c.1 c.2 with
    | none => rfl
    | some res => rcases res with ⟨v', i, m'⟩; rfl

omit [DecidableEq M] [DecidableEq E] [DecidableEq I] [Inhabited E]
  [SampleableType KR] [SampleableType KC] [SampleableType K] in
theorem Y_vRecv_eq_succ_of_cache (P : Party) (c : Header T × E)
    (rec : Option (SM.Record M (Header T × E))) (T_e : T)
    (σ : JSt Γ T Sig SS RS M E I)
    (heq : c.1.1 = (σ.1.g.st P).tcur + 1) (hc2 : c.1.2 = some T_e)
    (hcache : σ.1.h.cache ((σ.1.g.st P).tcur + 1) = some (T_e, (cka.receive (rΓ σ P) T_e).2)) :
    Y cka Δcka tL
      (liftH (vRecv (hooksCKA cka prng fs Δcka (moP tL t)) σ.1.g P (σ.1.g.st P) c rec)) σ =
      pure (some (
        if (σ.1.g.st P).id.sendsIn c.1.1 then none
        else
          let k := cka.receive (rΓ σ P) T_e
          let p := prng.up (σ.1.g.st P).root k.2
          match fs.receive (fs.initReceiver p.2) c.1 c.2 with
          | none => none
          | some (v', i, m') =>
            some (updVRStart prng fs (σ.1.g.st P)
              ((σ.1.g.st P).γ.map fun γ => (cka.receive γ T_e).1) k.2 v', c.1.1, i, m')), σ) := by
  unfold vRecv updVRStart
  dsimp only
  simp only [heq, Nat.lt_irrefl, decide_false, Bool.or_false]
  by_cases hs : (σ.1.g.st P).id.sendsIn ((σ.1.g.st P).tcur + 1) = true
  · simp [hs, Y_liftH_pure]
  · simp only [hs, Bool.false_eq_true, ↓reduceIte, hc2, hooksCKA, Y_liftH_bind, Y_liftH_get,
      pure_bind, hcache, Y_liftH_pure, Function.update_self]
    cases fs.receive (fs.initReceiver (prng.up (σ.1.g.st P).root (cka.receive (rΓ σ P) T_e).2).2) c.1 c.2 with
    | none => simp [Y_liftH_pure]
    | some res => rcases res with ⟨v', i, m'⟩; simp [Y_liftH_pure]

omit [DecidableEq M] [DecidableEq E] [DecidableEq I] [Inhabited E]
  [SampleableType KR] [SampleableType KC] [SampleableType K] in
theorem Y_commitE_of_tcur_succ {σ : JSt Γ T Sig SS RS M E I}
    (hI : Inv cka Δcka tL t σ) (P : Party) (T_e : T) (v' : RS) (pos : SM.Pos)
    (hsplit : σ.1.g.epoch P.other = σ.1.g.epoch P + 1)
    (hlast : (σ.1.g.st P).γ = none → σ.2.lastMsg = some T_e) :
    let k := cka.receive (rΓ σ P) T_e
    let st' := updVRStart prng fs (σ.1.g.st P)
      ((σ.1.g.st P).γ.map fun γ => (cka.receive γ T_e).1) k.2 v'
    ∃ (st'' : VPt Γ T Sig SS RS) (ck' : CKA.GameState Γ T),
      Y cka Δcka tL
        (commitE (hooksCKA cka prng fs Δcka (moP tL t)) σ.1.g P (σ.1.g.st P) st' pos) σ =
        pure (some (σ.1.g.accept P st'' pos), (σ.1, ck')) ∧
      projParty st'' (ck'.st P) = updVRStart prng fs ((projGame σ).st P) k.1 k.2 v' ∧
      st''.id = P ∧
      st''.tcur = σ.1.g.epoch P + 1 ∧
      st''.curCkaMsg = (σ.1.g.st P).curCkaMsg ∧
      (tL = none → st''.γ.isSome = true) ∧
      (∀ l, tL = some l →
        st''.γ.isSome = decide (healEpoch tL + Δcka ≤ σ.1.g.epoch P + 1) ∧
        ck'.epoch P = min (σ.1.g.epoch P + 1) (healEpoch tL + Δcka) ∧
        ck'.epoch P.other = σ.2.epoch P.other) ∧
      ck'.b = false ∧
      ck'.st P.other = σ.2.st P.other ∧
      st''.γ.getD (ck'.st P) = k.1 := by
  intro k st'
  have htcur_st' : st'.tcur = σ.1.g.epoch P + 1 := congrArg (· + 1) (hI.htcur P)
  have htcur_lt : decide ((σ.1.g.st P).tcur < σ.1.g.epoch P + 1) = true := by
    rw [hI.htcur P, decide_eq_true_eq]
    exact Nat.lt_succ_self _
  have hupd : ∀ (f : Party → VPt Γ T Sig SS RS) v₁ v₂,
      Function.update (Function.update f P v₁) P v₂ = Function.update f P v₂ :=
    fun f v₁ v₂ => by funext Q; by_cases hQ : Q = P <;> simp [hQ]
  cases hγ : (σ.1.g.st P).γ with
  | some γ₀ =>
    have hrΓ : rΓ σ P = γ₀ := by simp [rΓ, hγ]
    refine ⟨st', σ.2, ?_, ?_, ?_, ?_, rfl, ?_, ?_, hI.hckb, rfl, ?_⟩
    · unfold commitE hooksCKA
      simp only [hγ, Option.isNone_some, Bool.and_false, Bool.false_eq_true, ↓reduceIte,
        Y_bind, Y_liftH_pure, pure_bind, Y_pure, SM.GameState.accept, hupd]
    · dsimp only [projParty, realParty, st', updVRStart, projGame, k]
      simp [hγ, hrΓ]
    · exact hI.hid P
    · exact htcur_st'
    · intro _; simp [st', updVRStart, hγ]
    · intro l hl
      have hsome := (hI.hγ_some l hl P).1
      have hep_ck := (hI.hγ_some l hl P).2
      have hle_ep : healEpoch tL + Δcka ≤ σ.1.g.epoch P := by
        simpa [hγ] using hsome
      refine ⟨?_, ?_, rfl⟩
      · simp only [st', updVRStart, hγ, Option.map_some, Option.isSome_some]
        exact (decide_eq_true (by omega)).symm
      · rw [hep_ck]; omega
    · simp [st', updVRStart, hγ, k, hrΓ]
  | none =>
    have hrΓ : rΓ σ P = σ.2.st P := by simp [rΓ, hγ]
    have htL_some : ∃ l, tL = some l := by
      cases htL : tL with
      | none =>
        have h := hI.hγ_none htL P
        simp [hγ] at h
      | some l => exact ⟨l, rfl⟩
    rcases htL_some with ⟨l, hl⟩
    have hγP := (hI.hγ_some l hl P).1
    have hepP := (hI.hγ_some l hl P).2
    have hepO := (hI.hγ_some l hl P.other).2
    rw [hγ, Option.isSome_none, eq_comm, decide_eq_false_iff_not] at hγP
    have hcanR : σ.2.canReceive P = true := by
      simp only [CKA.GameState.canReceive, beq_iff_eq]
      rw [hepP, hepO, hsplit]
      omega
    have hlm : σ.2.lastMsg = some T_e := hlast hγ
    let ck' : CKA.GameState Γ T := σ.2.afterReceive P k.1
    have hck'_eq : σ.2.afterReceive P (cka.receive (σ.2.st P) T_e).1 = ck' := by
      dsimp [ck', k]; rw [hrΓ]
    have hck_stP : ck'.st P = k.1 := by simp [ck', CKA.GameState.afterReceive]
    have hck_stO : ck'.st P.other = σ.2.st P.other := by
      have hne : P.other ≠ P := by cases P <;> decide
      simp [ck', CKA.GameState.afterReceive, hne]
    have hck_epP : ck'.epoch P = min (σ.1.g.epoch P + 1) (healEpoch tL + Δcka) := by
      simp only [ck', CKA.GameState.afterReceive, Function.update_self, hepP]
      omega
    have hck_epO : ck'.epoch P.other = σ.2.epoch P.other := by
      have hne : P.other ≠ P := by cases P <;> decide
      simp [ck', CKA.GameState.afterReceive, hne]
    have hmo : (moP tL t).tH = healEpoch tL := rfl
    by_cases hfin : healEpoch tL + Δcka ≤ σ.1.g.epoch P + 1
    · let st'' : VPt Γ T Sig SS RS := { st' with γ := some k.1 }
      have hfin_ck : (ck'.allowCorr (healEpoch tL) || ck'.finished Δcka (healEpoch tL) P) = true := by
        rw [Bool.or_eq_true]
        right
        simp only [CKA.GameState.finished, decide_eq_true_eq, hck_epP]
        omega
      refine ⟨st'', ck', ?_, ?_, ?_, ?_, rfl, ?_, ?_, hI.hckb, hck_stO, ?_⟩
      · unfold commitE hooksCKA
        simp only [htcur_st', htcur_lt, hγ, Option.isNone_none, Bool.and_true, ↓reduceIte,
          Y_bind, Y_liftH_bind, Y_receiveQuery, CKA.receiveImpl, StateT.run_bind, StateT.run_get,
          pure_bind, hcanR, Bool.not_true, Bool.false_eq_true, hlm, StateT.run_set, StateT.run_pure,
          map_pure, hck'_eq, hmo, hfin, Y_corrQuery, CKA.corrImpl, hfin_ck, hck_stP,
          Y_liftH_pure, Y_pure, SM.GameState.accept, hupd]
        dsimp only [st'']
        rw [htcur_st']
      · rfl
      · exact hI.hid P
      · exact htcur_st'
      · intro hn; simp [hl] at hn
      · intro l' _
        refine ⟨?_, hck_epP, hck_epO⟩
        simp [st'', hfin]
      · simp [st'']
    · refine ⟨st', ck', ?_, ?_, ?_, ?_, rfl, ?_, ?_, hI.hckb, hck_stO, ?_⟩
      · unfold commitE hooksCKA
        simp only [htcur_st', htcur_lt, hγ, Option.isNone_none, Bool.and_true, ↓reduceIte,
          Y_bind, Y_liftH_bind, Y_receiveQuery, CKA.receiveImpl, StateT.run_bind, StateT.run_get,
          pure_bind, hcanR, Bool.not_true, Bool.false_eq_true, hlm, StateT.run_set, StateT.run_pure,
          map_pure, hck'_eq, hmo, hfin, Y_liftH_pure, Y_pure, SM.GameState.accept, hupd]
      · dsimp only [projParty, realParty, st', updVRStart, projGame]
        simp [hγ, hck_stP]
      · exact hI.hid P
      · exact htcur_st'
      · intro hn; simp [hl] at hn
      · intro l' _
        refine ⟨?_, hck_epP, hck_epO⟩
        simp [st', updVRStart, hγ, hfin]
      · simp [st', updVRStart, hγ, hck_stP]

omit [Inhabited E] [DecidableEq T] [DecidableEq M] [DecidableEq E] [DecidableEq I]
  [SampleableType KR] [SampleableType KC] [SampleableType CCoins] [SampleableType I]
  [SampleableType K] in
theorem inv_accept_succ {σ : JSt Γ T Sig SS RS M E I}
    (hI : Inv cka Δcka tL t σ) (P : Party) (T_e : T) (pos : SM.Pos)
    (st'' : VPt Γ T Sig SS RS) (ck' : CKA.GameState Γ T)
    (hsplit : σ.1.g.epoch P.other = σ.1.g.epoch P + 1)
    (hpos_ep : pos.epoch = σ.1.g.epoch P + 1)
    (hagr : ∀ rs, cka.AgreesFrom (cka.receive (rΓ σ P) T_e).1 (rΓ σ P.other) rs)
    (hid'' : st''.id = P)
    (htcur'' : st''.tcur = σ.1.g.epoch P + 1)
    (hTcur'' : st''.curCkaMsg = (σ.1.g.st P).curCkaMsg)
    (hγ_none'' : tL = none → st''.γ.isSome = true)
    (hγ_some'' : ∀ l, tL = some l →
      st''.γ.isSome = decide (healEpoch tL + Δcka ≤ σ.1.g.epoch P + 1) ∧
      ck'.epoch P = min (σ.1.g.epoch P + 1) (healEpoch tL + Δcka) ∧
      ck'.epoch P.other = σ.2.epoch P.other)
    (hckb' : ck'.b = false)
    (hck_stO : ck'.st P.other = σ.2.st P.other)
    (hrΓ'' : st''.γ.getD (ck'.st P) = (cka.receive (rΓ σ P) T_e).1) :
    Inv cka Δcka tL t ({ σ.1 with g := σ.1.g.accept P st'' pos }, ck') := by
  let σ' : JSt Γ T Sig SS RS M E I := ({ σ.1 with g := σ.1.g.accept P st'' pos }, ck')
  have hmax : max (σ.1.g.epoch P) pos.epoch = σ.1.g.epoch P + 1 := by
    rw [hpos_ep]; omega
  have hep' : ∀ Q, σ'.1.g.epoch Q = σ.1.g.epoch P + 1 := fun Q => by
    by_cases hQ : Q = P
    · subst hQ; simp [σ', SM.GameState.accept, SM.GameState.delete, hmax]
    · have hQo : Q = P.other := by cases P <;> cases Q <;> first | rfl | contradiction
      subst hQo; simp [σ', SM.GameState.accept, SM.GameState.delete, hQ, hsplit]
  have hrΓ_P : rΓ σ' P = (cka.receive (rΓ σ P) T_e).1 := by
    simp [rΓ, σ', SM.GameState.accept, SM.GameState.delete, hrΓ'']
  have hrΓ_O : rΓ σ' P.other = rΓ σ P.other := by
    have hne : P.other ≠ P := by cases P <;> decide
    simp [rΓ, σ', SM.GameState.accept, SM.GameState.delete, hne, hck_stO]
  have hTcur' : ∀ Q, (σ'.1.g.st Q).curCkaMsg = (σ.1.g.st Q).curCkaMsg := fun Q => by
    by_cases hQ : Q = P
    · subst hQ; simp [σ', SM.GameState.accept, SM.GameState.delete, hTcur'']
    · simp [σ', SM.GameState.accept, SM.GameState.delete, hQ]
  have hep_mono : ∀ Q, σ.1.g.epoch Q ≤ σ.1.g.epoch P + 1 := fun Q => by
    by_cases hQ : Q = P
    · subst hQ; exact Nat.le_succ _
    · have hQo : Q = P.other := by cases P <;> cases Q <;> first | rfl | contradiction
      subst hQo; rw [hsplit]
  refine
    { habort := hI.habort
      hckb := hckb'
      hid := fun Q => by
        by_cases hQ : Q = P
        · subst hQ; simp [SM.GameState.accept, SM.GameState.delete, hid'']
        · simp [SM.GameState.accept, SM.GameState.delete, hQ, hI.hid Q]
      htcur := fun Q => by
        rw [hep' Q]
        by_cases hQ : Q = P
        · subst hQ; simp [SM.GameState.accept, SM.GameState.delete, htcur'']
        · have hQo : Q = P.other := by cases P <;> cases Q <;> first | rfl | contradiction
          subst hQo
          simp [SM.GameState.accept, SM.GameState.delete, hQ, hI.htcur P.other, hsplit]
      hepoch_le := fun Q => by rw [hep' Q, hep' Q.other]; exact Nat.le_succ _
      hepoch_sync := fun Q _ => by rw [hep' Q, hep' Q.other]
      hcomp := fun pos' hpos' => by
        simp only [SM.GameState.accept, SM.GameState.delete, List.mem_filter] at hpos'
        exact hI.hcomp pos' hpos'.1
      hchall := fun pos' hpos' => by
        simp only [SM.GameState.accept, SM.GameState.delete, List.mem_filter] at hpos'
        have hch := hI.hchall pos' hpos'.1
        refine ⟨hch.1, hch.2.1, ?_⟩
        rw [hep' (Party.senderOf t)]
        exact hch.2.2.trans (hep_mono (Party.senderOf t))
      hleaks_tL := fun l' hl' => by
        obtain ⟨l₀, htL₀, hle₁, hle₂⟩ := hI.hleaks_tL l' hl'
        refine ⟨l₀, htL₀, hle₁, ?_⟩
        rw [hep' .A, hep' .B, Nat.max_self]
        have hA := hep_mono .A
        have hB := hep_mono .B
        omega
      htL_leaks := hI.htL_leaks
      htrans := fun r hr => by
        simp only [SM.GameState.accept, SM.GameState.delete, List.mem_filter] at hr
        have htr := hI.htrans r hr.1
        have hle_send := htr.1.trans (hep_mono r.pos.sender)
        refine ⟨?_, htr.2.1, fun h => ?_⟩
        · rw [hep' r.pos.sender]; exact hle_send
        · rw [hep' r.pos.sender.other] at h
          omega
      hγ_none := fun hn Q => by
        by_cases hQ : Q = P
        · subst hQ; simp [SM.GameState.accept, SM.GameState.delete, hγ_none'' hn]
        · simp [SM.GameState.accept, SM.GameState.delete, hQ, hI.hγ_none hn Q]
      hγ_some := fun l hl Q => by
        rw [hep' Q]
        by_cases hQ : Q = P
        · subst hQ
          obtain ⟨h1, h2, _⟩ := hγ_some'' l hl
          simp [SM.GameState.accept, SM.GameState.delete, h1, h2]
        · have hQo : Q = P.other := by cases P <;> cases Q <;> first | rfl | contradiction
          subst hQo
          obtain ⟨_, _, h3⟩ := hγ_some'' l hl
          have hO := hI.hγ_some l hl P.other
          rw [hsplit] at hO
          simp [SM.GameState.accept, SM.GameState.delete, hQ, h3, hO.1, hO.2]
      hcka_sync := fun Q _ hs rs => by
        rw [hep' Q] at hs
        by_cases hQ : Q = P
        · subst hQ
          rw [hrΓ_P, hrΓ_O]
          exact hagr rs
        · have hQo : Q = P.other := by cases P <;> cases Q <;> first | rfl | contradiction
          subst hQo
          have hsO : P.other.sendsIn (σ.1.g.epoch P.other) = true := by
            by_cases h : P.other.sendsIn (σ.1.g.epoch P.other) = true
            · exact h
            · simp only [Bool.not_eq_true] at h
              have hsync := hI.hepoch_sync P.other h
              rw [Party.other_other] at hsync
              omega
          have hnot := sendsIn_succ_eq_not P.other (σ.1.g.epoch P.other)
          rw [hsO, Bool.not_true] at hnot
          rw [hsplit] at hnot
          simp [hs] at hnot
      hcka_split := fun Q h => by
        rw [hep' Q, hep' Q.other] at h
        omega }

omit [DecidableEq I] [SampleableType KR] [SampleableType KC] [SampleableType K] in
theorem step_deliver (P : Party) (c : Header T × E) {σ : JSt Γ T Sig SS RS M E I}
    (hI : Inv cka Δcka tL t σ) :
    DEq ((implPs cka prng fs lam Δcka qep t (.inr (.inl (.inl (.inr (P, c)))))).run (projGame σ))
        ((fun r => (r.1, projGame r.2)) <$>
          Y cka Δcka tL (implEc cka prng fs Δcka qep tL t (.inr (.inl (.inl (.inr (P, c)))))) σ) ∧
      ∀ r ∈ support (Y cka Δcka tL (implEc cka prng fs Δcka qep tL t (.inr (.inl (.inl (.inr (P, c)))))) σ),
        Inv cka Δcka tL t r.2 ∧ (PostChall t σ.1.g → PostChall t r.2.1.g) := by
  unfold implPs
  rw [implP_deliver, implEc_deliver]
  have hab : σ.1.abort = false := hI.habort
  have hwin : (projGame σ).win = σ.1.g.win := rfl
  have hinT : (projGame σ).inTransit P.other c = σ.1.g.inTransit P.other c := rfl
  have hch_eq : (projGame σ).chall = σ.1.g.chall := rfl
  simp only [SM.deliverImpl, deliverE, SM.Config.priv, Bool.false_and, Bool.false_eq_true, ↓reduceIte,
    StateT.run_bind, StateT.run_get, Y_bind, Y_get, pure_bind, hab, Bool.false_or, hwin, hinT, hch_eq]
  by_cases hw : σ.1.g.win = true
  · simp only [hw, ↓reduceIte, StateT.run_pure, Y_pure, map_pure]
    exact ⟨DEq.refl _, fun r hr => by
      rw [support_pure, Set.mem_singleton_iff] at hr; rw [hr]; exact ⟨hI, id⟩⟩
  · simp only [hw, Bool.false_eq_true, ↓reduceIte]
    cases hin : σ.1.g.inTransit P.other c with
    | none =>
      simp only [StateT.run_pure, Y_pure, map_pure]
      exact ⟨DEq.refl _, fun r hr => by
        rw [support_pure, Set.mem_singleton_iff] at hr; rw [hr]; exact ⟨hI, id⟩⟩
    | some rec =>
      dsimp only
      unfold SM.GameState.inTransit at hin
      have hrec_mem : rec ∈ σ.1.g.trans := List.mem_of_find?_eq_some hin
      have hrec_pred := List.find?_some hin
      rw [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at hrec_pred
      rcases hrec_pred with ⟨hrec_sender, hrec_ct⟩
      obtain ⟨hrec_ep_le, hrec_c11, hrec_c12⟩ := hI.htrans rec hrec_mem
      rw [hrec_sender] at hrec_ep_le hrec_c12
      rw [Party.other_other] at hrec_c12
      rw [hrec_ct] at hrec_c11 hrec_c12
      by_cases heq : c.1.1 = (σ.1.g.st P).tcur + 1
      · have hrec_ep : rec.pos.epoch = σ.1.g.epoch P + 1 := by
          have ht := hI.htcur P
          omega
        have hsplit : σ.1.g.epoch P.other = σ.1.g.epoch P + 1 := by
          have hle := hI.hepoch_le P.other
          rw [Party.other_other] at hle
          omega
        have hsplit' : σ.1.g.epoch P.other = σ.1.g.epoch P.other.other + 1 := by
          rw [Party.other_other]; exact hsplit
        obtain ⟨T_e, hTcur, hcache, hlast, hagr⟩ := hI.hcka_split P.other hsplit'
        rw [Party.other_other] at hcache hlast hagr
        have hc2 : c.1.2 = some T_e := by
          rw [hrec_c12 hrec_ep, hTcur]
        have hcache' : σ.1.h.cache ((σ.1.g.st P).tcur + 1) =
            some (T_e, (cka.receive (rΓ σ P) T_e).2) := by
          rw [hI.htcur P, ← hsplit]
          exact hcache
        rw [receive_eq_succ_of_cache cka prng fs lam P c T_e σ heq hc2, Y_bind,
          Y_vRecv_eq_succ_of_cache cka prng fs Δcka tL t P c (some rec) T_e σ heq hc2 hcache',
          pure_bind]
        by_cases hs : (σ.1.g.st P).id.sendsIn c.1.1 = true
        · simp only [hs, ↓reduceIte, StateT.run_pure, Y_pure, map_pure]
          exact ⟨DEq.refl _, fun r hr => by
            rw [support_pure, Set.mem_singleton_iff] at hr; rw [hr]; exact ⟨hI, id⟩⟩
        · simp only [hs, Bool.false_eq_true, ↓reduceIte]
          cases fs.receive
              (fs.initReceiver (prng.up (σ.1.g.st P).root (cka.receive (rΓ σ P) T_e).2).2)
              c.1 c.2 with
          | none =>
            simp only [StateT.run_pure, Y_pure, map_pure]
            exact ⟨DEq.refl _, fun r hr => by
              rw [support_pure, Set.mem_singleton_iff] at hr; rw [hr]; exact ⟨hI, id⟩⟩
          | some res =>
            rcases res with ⟨v', i', m'⟩
            dsimp only
            obtain ⟨st'', ck', hcommit, hproj_st, hid'', htcur'', hTcur'', hγ_none'',
              hγ_some'', hckb', hck_stO, hrΓ''⟩ :=
              Y_commitE_of_tcur_succ cka prng fs Δcka tL t hI P T_e v' rec.pos hsplit hlast
            simp only [StateT.run_bind, StateT.run_set, pure_bind, StateT.run_pure,
              Y_bind, hcommit, Y_modify, Y_pure, map_pure]
            let σ' : JSt Γ T Sig SS RS M E I :=
              ({ σ.1 with g := σ.1.g.accept P st'' rec.pos }, ck')
            have hproj : (projGame σ).accept P
                (updVRStart prng fs ((projGame σ).st P) (cka.receive (rΓ σ P) T_e).1
                  (cka.receive (rΓ σ P) T_e).2 v') rec.pos = projGame σ' := by
              rw [← hproj_st]
              dsimp only [SM.GameState.accept, SM.GameState.delete, projGame, σ']
              congr 1
              funext Q
              by_cases hQ : Q = P
              · subst Q; simp
              · have hQo : Q = P.other := by cases P <;> cases Q <;> first | rfl | contradiction
                subst Q; simp [hQ, projParty, realParty, hck_stO]
            rw [hproj]
            refine ⟨DEq.refl _, fun r hr => ?_⟩
            rw [support_pure, Set.mem_singleton_iff] at hr
            rw [hr]
            exact ⟨inv_accept_succ cka Δcka tL t hI P T_e rec.pos st'' ck' hsplit hrec_ep hagr
              hid'' htcur'' hTcur'' hγ_none'' hγ_some'' hckb' hck_stO hrΓ'',
              fun hp => postChall_accept cka Δcka tL t hI hp P st'' rec.pos hrec_sender⟩
      · rw [receive_ne_succ cka prng fs lam P c σ heq, Y_bind,
          Y_vRecv_ne_succ cka prng fs Δcka tL t P c (some rec) σ heq, pure_bind]
        by_cases hbad : ((σ.1.g.st P).id.sendsIn c.1.1 || decide ((σ.1.g.st P).tcur + 1 < c.1.1)) = true
        · simp only [hbad, ↓reduceIte, StateT.run_pure, Y_pure, map_pure]
          exact ⟨DEq.refl _, fun r hr => by
            rw [support_pure, Set.mem_singleton_iff] at hr; rw [hr]; exact ⟨hI, id⟩⟩
        · simp only [hbad, Bool.false_eq_true, ↓reduceIte]
          rcases (σ.1.g.st P).vR c.1.1 with _ | v
          · simp only [StateT.run_pure, Y_pure, map_pure]
            exact ⟨DEq.refl _, fun r hr => by
              rw [support_pure, Set.mem_singleton_iff] at hr; rw [hr]; exact ⟨hI, id⟩⟩
          · dsimp only
            rcases fs.receive v c.1 c.2 with _ | ⟨v', i', m'⟩
            · simp only [StateT.run_pure, Y_pure, map_pure]
              exact ⟨DEq.refl _, fun r hr => by
                rw [support_pure, Set.mem_singleton_iff] at hr; rw [hr]; exact ⟨hI, id⟩⟩
            · dsimp only
              have hle : rec.pos.epoch ≤ σ.1.g.epoch P := by
                have : ¬ ((σ.1.g.st P).tcur + 1 < c.1.1) := by
                  revert hbad; cases (σ.1.g.st P).id.sendsIn c.1.1 <;> simp
                have ht := hI.htcur P
                omega
              let st' : VPt Γ T Sig SS RS := updVR (σ.1.g.st P) c.1.1 (some v')
              have hcommit : Y cka Δcka tL
                  (commitE (hooksCKA cka prng fs Δcka (moP tL t)) σ.1.g P (σ.1.g.st P)
                    (updVR (σ.1.g.st P) c.1.1 (some v')) rec.pos) σ =
                  pure (some (σ.1.g.accept P st' rec.pos), σ) :=
                Y_commitE_of_tcur_eq cka prng fs Δcka tL t P st' rec.pos σ rfl
              simp only [StateT.run_bind, StateT.run_set, pure_bind, StateT.run_pure,
                Y_bind, hcommit, Y_modify, Y_pure, map_pure]
              obtain ⟨hproj, hI'⟩ :=
                inv_accept_updVR cka Δcka tL t hI P c.1.1 v' rec.pos hle
              rw [hproj]
              refine ⟨DEq.refl _, fun r hr => ?_⟩
              rw [support_pure, Set.mem_singleton_iff] at hr
              rw [hr]
              exact ⟨hI', fun hp => postChall_accept cka Δcka tL t hI hp P st' rec.pos hrec_sender⟩

omit [Inhabited E] [DecidableEq T] [DecidableEq M] [DecidableEq E] [DecidableEq I]
  [SampleableType KR] [SampleableType KC] [SampleableType CCoins] [SampleableType I]
  [SampleableType K] in
theorem inv_afterCorr {σ : JSt Γ T Sig SS RS M E I}
    (hI : Inv cka Δcka tL t σ) (P : Party) :
    let σ' : JSt Γ T Sig SS RS M E I := ({ σ.1 with g := σ.1.g.afterCorr P }, σ.2)
    (projGame σ).afterCorr P = projGame σ' ∧ Inv cka Δcka tL t σ' := by
  intro σ'
  refine ⟨rfl, ?_⟩
  let M_ep := max (σ.1.g.epoch .A) (σ.1.g.epoch .B)
  let l_new := SM.maxOpt σ.1.g.tL M_ep
  have hl_new_eq : l_new = M_ep := by
    dsimp only [l_new, SM.maxOpt]
    cases htL : σ.1.g.tL with
    | none => rfl
    | some l₀ =>
      have hmem := hI.htL_leaks l₀ htL
      obtain ⟨l₁, htL₁, hle₁, hle₂⟩ := hI.hleaks_tL l₀ hmem
      rw [htL] at htL₁; injection htL₁ with rfl
      exact Nat.max_eq_right (hle₁.trans hle₂)
  exact
    { habort := hI.habort
      hckb := hI.hckb
      hid := hI.hid
      htcur := hI.htcur
      hepoch_le := hI.hepoch_le
      hepoch_sync := hI.hepoch_sync
      hcomp := fun pos hpos => by
        simp only [σ', SM.GameState.afterCorr, SM.GameState.leak, List.mem_append,
          List.mem_map, List.mem_filter, beq_iff_eq] at hpos ⊢
        rcases hpos with ⟨r, ⟨hr_mem, _⟩, rfl⟩ | hpos_old
        · have htr := (hI.htrans r hr_mem).1
          simp only [SM.healedBy, decide_eq_false_iff_not]
          have hle_M : r.pos.epoch ≤ M_ep := by
            dsimp only [M_ep]
            cases hS : r.pos.sender <;> simp only [hS] at htr <;> omega
          have hle_new := le_maxOpt_right σ.1.g.tL M_ep
          dsimp only [M_ep] at hle_M hle_new
          omega
        · exact healedBy_leak_false (hI.hcomp pos hpos_old)
      hchall := hI.hchall
      hleaks_tL := fun l' hl' => by
        simp only [σ', SM.GameState.afterCorr, SM.GameState.leak, List.mem_cons] at hl' ⊢
        refine ⟨l_new, rfl, ?_, by omega⟩
        rcases hl' with rfl | hl'_old
        · exact le_rfl
        · obtain ⟨l₀, _, hle₁, hle₂⟩ := hI.hleaks_tL l' hl'_old
          omega
      htL_leaks := fun l₀ hl₀ => by
        simp only [σ', SM.GameState.afterCorr, SM.GameState.leak, Option.some.injEq] at hl₀ ⊢
        subst hl₀
        exact List.mem_cons_self
      htrans := hI.htrans
      hγ_none := hI.hγ_none
      hγ_some := hI.hγ_some
      hcka_sync := hI.hcka_sync
      hcka_split := hI.hcka_split }

omit [Inhabited E] [DecidableEq T] [DecidableEq M] [DecidableEq E] [DecidableEq I]
  [SampleableType KR] [SampleableType KC] [SampleableType CCoins] [SampleableType I]
  [SampleableType K] in
theorem doom_of_corr_abort {σ : JSt Γ T Sig SS RS M E I}
    (hI : Inv cka Δcka tL t σ) (P : Party)
    (hcorr : σ.1.g.corrAllowed P = true)
    (hdoom : ((polP tL t).leakDoom σ.1.g (σ.1.g.afterCorr P) ||
              (polP tL t).corrDoom σ.1.g P) = true) :
    DoomFixedB (2 + Δcka) tL t ((projGame σ).afterCorr P) ∨
      (DoomD2 (2 + Δcka) t ((projGame σ).afterCorr P) ∧ ¬ PostChall t σ.1.g) := by
  let s₁ := σ.1.g.afterCorr P
  let sL₁ := (projGame σ).afterCorr P
  have hleaks_eq : sL₁.leaks = s₁.leaks := rfl
  have htL_eq : sL₁.tL = s₁.tL := rfl
  unfold Policy.leakDoom Policy.corrDoom polP at hdoom
  simp only [Bool.false_eq_true, ↓reduceIte, Bool.or_eq_true, Bool.and_eq_true,
    List.any_eq_true, beq_iff_eq, decide_eq_true_eq] at hdoom
  rcases hdoom with (⟨l', hl'_mem, hlt₁, hlt₂⟩ | ⟨⟨l', hl'_mem, hle_t⟩, hlt_S⟩) | ⟨rfl, hlt_R, hle_max⟩
  · left; right; left
    exact ⟨l', by rw [hleaks_eq]; exact hl'_mem, hlt₁, hlt₂⟩
  · right
    refine ⟨?_, fun hp => by have := hp.1; omega⟩
    unfold DoomD2
    rw [htL_eq]
    have hinv' := (inv_afterCorr cka Δcka tL t hI P).2
    obtain ⟨l₀, htL₀, hle₁, _⟩ := hinv'.hleaks_tL l' hl'_mem
    change SM.healedBy s₁.tL (2 + Δcka) t = false
    rw [htL₀]
    simp only [SM.healedBy, decide_eq_false_iff_not]
    omega
  · right
    refine ⟨?_, ?_⟩
    · unfold DoomD2
      simp only [projGame, SM.GameState.afterCorr, SM.GameState.leak, SM.healedBy,
        decide_eq_false_iff_not]
      have hle_m := le_maxOpt_right σ.1.g.tL (max (σ.1.g.epoch .A) (σ.1.g.epoch .B))
      omega
    · rintro ⟨_, ⟨pos, hpos_mem, hpos_S⟩ | hR⟩
      · unfold SM.GameState.corrAllowed at hcorr
        rw [Bool.and_eq_true, Bool.not_eq_true', List.any_eq_false] at hcorr
        have hf := hcorr.1 pos hpos_mem
        rw [beq_iff_eq] at hf
        have hRO : (Party.receiverOf t).other = Party.senderOf t := by
          unfold Party.receiverOf Party.senderOf
          cases t % 2 == 1 <;> rfl
        rw [hRO] at hf
        exact hf hpos_S
      · omega

omit [DecidableEq I] [SampleableType KR] [SampleableType KC] [SampleableType K] in
theorem step_corr (P : Party) {σ : JSt Γ T Sig SS RS M E I}
    (hI : Inv cka Δcka tL t σ) :
    (DEq ((implPs cka prng fs lam Δcka qep t (.inr (.inr P))).run (projGame σ))
         ((fun r => (r.1, projGame r.2)) <$>
           Y cka Δcka tL (implEc cka prng fs Δcka qep tL t (.inr (.inr P))) σ) ∧
       ∀ r ∈ support (Y cka Δcka tL (implEc cka prng fs Δcka qep tL t (.inr (.inr P))) σ),
         Inv cka Δcka tL t r.2 ∧ (PostChall t σ.1.g → PostChall t r.2.1.g)) ∨
    ((∀ r ∈ support (Y cka Δcka tL (implEc cka prng fs Δcka qep tL t (.inr (.inr P))) σ),
        r.2.1.abort = true) ∧
      ∀ z ∈ support ((implPs cka prng fs lam Δcka qep t (.inr (.inr P))).run (projGame σ)),
        DoomFixedB (2 + Δcka) tL t z.2 ∨
          (DoomD2 (2 + Δcka) t z.2 ∧ ¬ PostChall t σ.1.g)) := by
  unfold implPs
  rw [implP_corr, implEc_corr]
  have hab : σ.1.abort = false := hI.habort
  have hwin : (projGame σ).win = σ.1.g.win := rfl
  have hca : (projGame σ).corrAllowed P = σ.1.g.corrAllowed P := rfl
  simp only [SM.corrImpl, corrE, StateT.run_bind, StateT.run_get, Y_bind, Y_get, pure_bind,
    hab, Bool.false_or, hwin, hca]
  by_cases hguard : (σ.1.g.win || !σ.1.g.corrAllowed P) = true
  · left
    simp only [hguard, ↓reduceIte, StateT.run_pure, Y_pure, map_pure]
    exact ⟨DEq.refl _, fun r hr => by
      rw [support_pure, Set.mem_singleton_iff] at hr; rw [hr]; exact ⟨hI, id⟩⟩
  · simp only [hguard, Bool.false_eq_true, ↓reduceIte]
    have hcorr : σ.1.g.corrAllowed P = true := by
      revert hguard; cases σ.1.g.win <;> cases σ.1.g.corrAllowed P <;> decide
    by_cases hdoom : ((polP tL t).leakDoom σ.1.g (σ.1.g.afterCorr P) ||
                      (polP tL t).corrDoom σ.1.g P) = true
    · right
      simp only [hdoom, ↓reduceIte, Y_bind, Y_abortE, pure_bind, Y_pure,
        StateT.run_bind, StateT.run_set, StateT.run_pure]
      refine ⟨fun r hr => ?_, fun z hz => ?_⟩
      · rw [support_pure, Set.mem_singleton_iff] at hr; rw [hr]
      · rw [support_pure, Set.mem_singleton_iff] at hz; rw [hz]
        exact doom_of_corr_abort cka Δcka tL t hI P hcorr hdoom
    · simp only [hdoom, Bool.false_eq_true, ↓reduceIte]
      rw [Bool.not_eq_true] at hdoom
      cases hγ : (σ.1.g.st P).γ with
      | some γ₀ =>
        left
        have hrev : Y cka Δcka tL
            (liftH ((hooksCKA cka prng fs Δcka (moP tL t)).reveal σ.1.g P (σ.1.g.st P))) σ =
            pure (some ((projGame σ).st P), σ) := by
          unfold hooksCKA
          simp only [hγ, pure_bind, Y_liftH_pure]
          dsimp only [projGame, projParty, realParty]
          simp [hγ]
        simp only [Y_bind, hrev, pure_bind, Y_modify, Y_pure, map_pure,
          StateT.run_bind, StateT.run_set, StateT.run_pure]
        obtain ⟨hproj, hI'⟩ := inv_afterCorr cka Δcka tL t hI P
        rw [hproj]
        refine ⟨DEq.refl _, fun r hr => ?_⟩
        rw [support_pure, Set.mem_singleton_iff] at hr; rw [hr]
        exact ⟨hI', id⟩
      | none =>
        have htL_some : ∃ l, tL = some l := by
          cases htL : tL with
          | none =>
            have h := hI.hγ_none htL P
            simp [hγ] at h
          | some l => exact ⟨l, rfl⟩
        rcases htL_some with ⟨l, hl⟩
        by_cases hallow : (σ.2.allowCorr (healEpoch tL) || σ.2.finished Δcka (healEpoch tL) P) = true
        · left
          have hrev : Y cka Δcka tL
              (liftH ((hooksCKA cka prng fs Δcka (moP tL t)).reveal σ.1.g P (σ.1.g.st P))) σ =
              pure (some ((projGame σ).st P), σ) := by
            unfold hooksCKA
            simp only [hγ, Y_liftH_bind, Y_corrQuery, CKA.corrImpl, StateT.run_bind,
              StateT.run_get, pure_bind, hallow, ↓reduceIte, StateT.run_pure, map_pure,
              Y_liftH_pure]
            dsimp only [projGame, projParty, realParty]
            simp [hγ]
          simp only [Y_bind, hrev, pure_bind, Y_modify, Y_pure, map_pure,
            StateT.run_bind, StateT.run_set, StateT.run_pure]
          obtain ⟨hproj, hI'⟩ := inv_afterCorr cka Δcka tL t hI P
          rw [hproj]
          refine ⟨DEq.refl _, fun r hr => ?_⟩
          rw [support_pure, Set.mem_singleton_iff] at hr; rw [hr]
          exact ⟨hI', id⟩
        · right
          have hrev : Y cka Δcka tL
              (liftH ((hooksCKA cka prng fs Δcka (moP tL t)).reveal σ.1.g P (σ.1.g.st P))) σ =
              pure (none, σ) := by
            unfold hooksCKA
            simp only [hγ, Y_liftH_bind, Y_corrQuery, CKA.corrImpl, StateT.run_bind,
              StateT.run_get, pure_bind, hallow, Bool.false_eq_true, ↓reduceIte,
              StateT.run_pure, map_pure, Y_liftH_pure]
          simp only [Y_bind, hrev, pure_bind, Y_abortE, Y_pure,
            StateT.run_bind, StateT.run_set, StateT.run_pure]
          refine ⟨fun r hr => ?_, fun z hz => ?_⟩
          · rw [support_pure, Set.mem_singleton_iff] at hr; rw [hr]
          · rw [support_pure, Set.mem_singleton_iff] at hz; rw [hz]
            left; left
            rw [Bool.not_eq_true] at hallow
            have hγP := (hI.hγ_some l hl P).1
            have hepA := (hI.hγ_some l hl .A).2
            have hepB := (hI.hγ_some l hl .B).2
            rw [hγ, Option.isSome_none, eq_comm, decide_eq_false_iff_not] at hγP
            have hmax_gt : l < max (σ.1.g.epoch .A) (σ.1.g.epoch .B) := by
              rw [Bool.or_eq_false_iff] at hallow
              have h1 := hallow.1
              simp only [CKA.GameState.allowCorr, decide_eq_false_iff_not] at h1
              rw [hepA, hepB, hl] at h1
              simp only [healEpoch] at h1 hγP
              omega
            let s₁ := σ.1.g.afterCorr P
            let l_new := SM.maxOpt σ.1.g.tL (max (σ.1.g.epoch .A) (σ.1.g.epoch .B))
            have hl_mem : l_new ∈ s₁.leaks := List.mem_cons_self
            have hl_lt : l < l_new := by
              have := le_maxOpt_right σ.1.g.tL (max (σ.1.g.epoch .A) (σ.1.g.epoch .B))
              omega
            rw [Bool.or_eq_false_iff] at hdoom
            rcases hdoom with ⟨hLD, hCD⟩
            unfold Policy.leakDoom polP at hLD
            rw [Bool.or_eq_false_iff] at hLD
            rcases hLD with ⟨hd1, hd2⟩
            rw [List.any_eq_false] at hd1
            have ht_le_lnew : t ≤ l_new := by
              have h := hd1 l_new hl_mem
              dsimp only [SM.ltOpt] at h
              rw [hl] at h
              simp only [Bool.and_eq_true, decide_eq_true_eq, not_and, not_lt] at h
              exact h hl_lt
            have ht_le_S : t ≤ σ.1.g.epoch (Party.senderOf t) := by
              rw [Bool.and_eq_false_imp, List.any_eq_true] at hd2
              have h := hd2 ⟨l_new, hl_mem, decide_eq_true ht_le_lnew⟩
              exact decide_eq_false_iff_not.mp h |> Nat.not_lt.mp
            have ht_le_P : t ≤ σ.1.g.epoch P := by
              by_cases hPS : P = Party.senderOf t
              · rw [hPS]; exact ht_le_S
              · have hPR : P = Party.receiverOf t := by
                  cases P <;> cases hS : Party.senderOf t <;>
                    simp_all [Party.receiverOf, Party.senderOf]
                have hmax_t : t ≤ max (σ.1.g.epoch .A) (σ.1.g.epoch .B) := by
                  cases hS : Party.senderOf t <;> simp only [hS] at ht_le_S <;> omega
                unfold Policy.corrDoom polP at hCD
                simp only [Bool.false_eq_true, ↓reduceIte, Bool.and_eq_false_imp,
                  beq_iff_eq, decide_eq_true_eq, decide_eq_false_iff_not] at hCD
                by_cases hlt : σ.1.g.epoch P < t
                · exact False.elim (hCD hPR hlt hmax_t)
                · omega
            rw [hl]
            simp only [SM.lastLeakGuessAdmissible, SM.healedBy, decide_eq_false_iff_not]
            simp only [hl, healEpoch] at hγP
            omega

def samIfNecFst (r : Option CCoins) : ProbComp CCoins :=
  match r with
  | some c => pure c
  | none => $ᵗ CCoins

omit [DecidableEq T] [DecidableEq M] [DecidableEq E] [DecidableEq I] [Inhabited E]
  [SampleableType KR] [SampleableType KC] [SampleableType I] [SampleableType K] in
theorem samIfNec_eq_bind (r : Option CCoins) :
    SM.samIfNec r = (samIfNecFst r >>= fun c => pure (c, r.isSome)) := by
  cases r <;> simp [SM.samIfNec, samIfNecFst, map_eq_bind_pure_comp]

omit [DecidableEq T] [DecidableEq M] [DecidableEq E] [DecidableEq I] [Inhabited E]
  [SampleableType KR] [SampleableType KC] [SampleableType I] [SampleableType K] in
theorem samIfNecFst_bind_const {α : Type} (r : Option CCoins) (a : α) :
    DEq (samIfNecFst r >>= fun _ => pure a) (pure a) :=
  DEq.bind_const _ _

omit [Inhabited E] [DecidableEq T] [DecidableEq M] [DecidableEq E] [DecidableEq I]
  [SampleableType KR] [SampleableType KC] [SampleableType CCoins] [SampleableType I]
  [SampleableType K] in
theorem epMgmt_projGame (Δ qep : ℕ) (P : Party) (bad : Bool) (σ : JSt Γ T Sig SS RS M E I) :
    (projGame σ).epMgmt Δ qep P bad =
      (σ.1.g.epMgmt Δ qep P bad).map (fun s₁ => projGame ({ σ.1 with g := s₁ }, σ.2)) := by
  unfold SM.GameState.epMgmt SM.GameState.safeCh SM.GameState.leak projGame
  dsimp only
  split
  · split
    · rfl
    · split <;> rfl
  · split <;> rfl

omit [Inhabited E] [DecidableEq T] [DecidableEq M] [DecidableEq E] [DecidableEq I]
  [SampleableType KR] [SampleableType KC] [SampleableType CCoins] [SampleableType I]
  [SampleableType K] in
theorem epMgmt_inv_props {σ : JSt Γ T Sig SS RS M E I}
    {s₁ : SM.GameState (VPt Γ T Sig SS RS) M (Header T × E)}
    (hI : Inv cka Δcka tL t σ) (P : Party) (bad : Bool)
    (hep : σ.1.g.epMgmt (2 + Δcka) qep P bad = some s₁) :
    s₁.st = σ.1.g.st ∧
    s₁.trans = σ.1.g.trans ∧
    s₁.chall = σ.1.g.chall ∧
    s₁.comp = σ.1.g.comp ∧
    s₁.b = σ.1.g.b ∧
    s₁.win = σ.1.g.win ∧
    P.sendsIn (s₁.epoch P) = true ∧
    (∀ Q, σ.1.g.epoch Q ≤ s₁.epoch Q) ∧
    (∀ pos ∈ s₁.comp, SM.healedBy s₁.tL (2 + Δcka) pos.epoch = false) ∧
    (∀ l' ∈ s₁.leaks,
      ∃ l₀, s₁.tL = some l₀ ∧ l' ≤ l₀ ∧ l₀ ≤ max (s₁.epoch .A) (s₁.epoch .B)) ∧
    (∀ l₀, s₁.tL = some l₀ → l₀ ∈ s₁.leaks) ∧
    (P.sendsIn (σ.1.g.epoch P + 1) = false → s₁ = σ.1.g) ∧
    (P.sendsIn (σ.1.g.epoch P + 1) = true →
      σ.1.g.epoch P = σ.1.g.epoch P.other ∧
      s₁.epoch P = σ.1.g.epoch P + 1 ∧
      s₁.epoch P.other = σ.1.g.epoch P ∧
      s₁.tL = (if bad && !(σ.1.g.safeCh (2 + Δcka) P) then
                 some (SM.maxOpt σ.1.g.tL (σ.1.g.epoch P + 1))
               else σ.1.g.tL) ∧
      s₁.leaks = (if bad && !(σ.1.g.safeCh (2 + Δcka) P) then
                    SM.maxOpt σ.1.g.tL (σ.1.g.epoch P + 1) :: σ.1.g.leaks
                  else σ.1.g.leaks)) := by
  have hs_ep : P.sendsIn (s₁.epoch P) = true :=
    (epMgmt_sendsIn_epoch qep hep).1
  unfold SM.GameState.epMgmt at hep
  by_cases hs : P.sendsIn (σ.1.g.epoch P + 1) = true
  · simp only [hs, ↓reduceIte] at hep
    split at hep
    · cases hep
    · have hs0 : P.sendsIn (σ.1.g.epoch P) = false := by
        have h := sendsIn_succ_eq_not P (σ.1.g.epoch P)
        rw [hs] at h
        revert h; cases P.sendsIn (σ.1.g.epoch P) <;> decide
      have hsync : σ.1.g.epoch P = σ.1.g.epoch P.other := hI.hepoch_sync P hs0
      have hsyncAB : σ.1.g.epoch .A = σ.1.g.epoch .B := by
        cases P <;> [exact hsync; exact hsync.symm]
      have hne : P.other ≠ P := by cases P <;> decide
      have hmax_new :
          max (Function.update σ.1.g.epoch P (σ.1.g.epoch P + 1) .A)
              (Function.update σ.1.g.epoch P (σ.1.g.epoch P + 1) .B) =
            σ.1.g.epoch P + 1 := by
        cases P with
        | A =>
          change max (σ.1.g.epoch .A + 1) (σ.1.g.epoch .B) = σ.1.g.epoch .A + 1
          omega
        | B =>
          change max (σ.1.g.epoch .A) (σ.1.g.epoch .B + 1) = σ.1.g.epoch .B + 1
          omega
      by_cases hleak : (bad && !σ.1.g.safeCh (2 + Δcka) P) = true
      · simp only [hleak, ↓reduceIte] at hep ⊢
        injection hep with h_eq
        subst h_eq
        refine ⟨rfl, rfl, rfl, rfl, rfl, rfl, hs_ep, ?_, ?_, ?_, ?_,
          fun h => by simp [hs] at h,
          fun _ => ⟨hsync, by simp [SM.GameState.leak], by simp [SM.GameState.leak, hne, hsync.symm], rfl, rfl⟩⟩
        · intro Q
          by_cases hQ : Q = P
          · subst Q; simp [SM.GameState.leak]
          · simp [SM.GameState.leak, hQ]
        · intro pos hpos
          exact healedBy_leak_false (hI.hcomp pos hpos)
        · intro l' hl'
          simp only [SM.GameState.leak] at hl' ⊢
          rw [hmax_new]
          simp only [List.mem_cons] at hl'
          let l_new := SM.maxOpt σ.1.g.tL (σ.1.g.epoch P + 1)
          have hl_new_le : l_new ≤ σ.1.g.epoch P + 1 := by
            dsimp only [l_new, SM.maxOpt]
            cases htL0 : σ.1.g.tL with
            | none => exact le_rfl
            | some l₀ =>
              have hm := hI.htL_leaks l₀ htL0
              obtain ⟨l₁, htL1, hle1, hle2⟩ := hI.hleaks_tL l₀ hm
              rw [htL0] at htL1; injection htL1 with rfl
              exact Nat.max_le.mpr ⟨by cases P <;> omega, le_rfl⟩
          refine ⟨l_new, rfl, ?_, hl_new_le⟩
          rcases hl' with rfl | hl'_old
          · exact le_rfl
          · obtain ⟨l₀, htL0, hle1, _⟩ := hI.hleaks_tL l' hl'_old
            have : l₀ ≤ l_new := by
              dsimp only [l_new, SM.maxOpt]
              rw [htL0]
              exact Nat.le_max_left _ _
            omega
        · intro l₀ hl₀
          simp only [SM.GameState.leak, Option.some.injEq] at hl₀ ⊢
          subst hl₀
          exact List.mem_cons_self
      · simp only [hleak, Bool.false_eq_true, ↓reduceIte] at hep ⊢
        injection hep with h_eq
        subst h_eq
        refine ⟨rfl, rfl, rfl, rfl, rfl, rfl, hs_ep, ?_, hI.hcomp, ?_, hI.htL_leaks,
          fun h => by simp [hs] at h,
          fun _ => ⟨hsync, by simp, by simp [hne, hsync.symm], rfl, rfl⟩⟩
        · intro Q
          by_cases hQ : Q = P
          · subst Q; simp
          · simp [hQ]
        · intro l' hl'
          dsimp only
          rw [hmax_new]
          obtain ⟨l₀, htL0, hle1, hle2⟩ := hI.hleaks_tL l' hl'
          refine ⟨l₀, htL0, hle1, ?_⟩
          cases P <;> omega
  · simp only [hs, Bool.false_eq_true, ↓reduceIte] at hep
    split at hep
    · cases hep
    · injection hep with h_eq
      subst h_eq
      exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, hs_ep, fun _ => le_rfl, hI.hcomp,
        hI.hleaks_tL, hI.htL_leaks, fun _ => rfl, fun h => by simp [hs] at h⟩

omit [Inhabited E] [DecidableEq T] [DecidableEq M] [DecidableEq E] [DecidableEq I]
  [SampleableType KR] [SampleableType KC] [SampleableType CCoins] [SampleableType I]
  [SampleableType K] in
theorem doom_of_epMgmt_leakDoom {σ : JSt Γ T Sig SS RS M E I}
    {s₁ : SM.GameState (VPt Γ T Sig SS RS) M (Header T × E)}
    {s_out : SM.GameState (RSt Γ T Sig SS RS) M (Header T × E)}
    (hI : Inv cka Δcka tL t σ) (P : Party) (bad : Bool)
    (hep : σ.1.g.epMgmt (2 + Δcka) qep P bad = some s₁)
    (hdoom : (polP tL t).leakDoom σ.1.g s₁ = true)
    (hleaks_out : s_out.leaks = s₁.leaks)
    (htL_out : s_out.tL = s₁.tL) :
    (DoomFixedB (2 + Δcka) tL t s_out ∨
      (DoomD2 (2 + Δcka) t s_out ∧ ¬ PostChall t σ.1.g)) ∧
    (s₁.safeCh (2 + Δcka) P = true → s₁.epoch P = t →
      DoomFixedB (2 + Δcka) tL t s_out) := by
  have hprops := epMgmt_inv_props cka Δcka qep tL t hI P bad hep
  have hleaks_tL := hprops.2.2.2.2.2.2.2.2.2.1
  unfold Policy.leakDoom polP at hdoom
  simp only [Bool.or_eq_true, Bool.and_eq_true, List.any_eq_true, decide_eq_true_eq] at hdoom
  rcases hdoom with ⟨l', hl'_mem, hlt₁, hlt₂⟩ | ⟨⟨l', hl'_mem, hle_t⟩, hlt_S⟩
  · have hd : DoomFixedB (2 + Δcka) tL t s_out := by
      right; left
      exact ⟨l', by rw [hleaks_out]; exact hl'_mem, hlt₁, hlt₂⟩
    exact ⟨Or.inl hd, fun _ _ => hd⟩
  · obtain ⟨l₀, htL₀, hle₁, _⟩ := hleaks_tL l' hl'_mem
    have hd2 : DoomD2 (2 + Δcka) t s_out := by
      unfold DoomD2
      rw [htL_out, htL₀]
      simp only [SM.healedBy, decide_eq_false_iff_not]
      omega
    refine ⟨Or.inr ⟨hd2, fun hp => by have := hp.1; omega⟩, fun hsafe hep_t => ?_⟩
    exfalso
    unfold SM.GameState.safeCh at hsafe
    rw [hep_t, htL₀] at hsafe
    simp only [SM.healedBy, decide_eq_true_eq] at hsafe
    omega

def sendSameEpoch {γ : Type} (fs : FSAEADScheme K SS RS (Header T) M E)
    (st : PartyState γ T Sig SS RS) (m : M) :
    PartyState γ T Sig SS RS × (Header T × E) :=
  let h : Header T := (st.tcur, st.curCkaMsg)
  match st.vS with
  | some v =>
    let out := fs.send v h m
    ({ st with vS := some out.1 }, (h, out.2))
  | none => (st, (h, default))

omit [DecidableEq M] [DecidableEq E] [DecidableEq I]
  [SampleableType KR] [SampleableType KC] [SampleableType I]
  [SampleableType K] in
theorem vSend_not_sendsIn (s : SM.GameState (VPt Γ T Sig SS RS) M (Header T × E))
    (P : Party) (st : VPt Γ T Sig SS RS) (m : M) (pair : Option (M × M)) (r : Option CCoins)
    (hs : st.id.sendsIn (st.tcur + 1) = false) :
    vSend (hooksCKA cka prng fs Δcka (moP tL t)) s P st m pair r =
      pure (some (sendSameEpoch fs st m)) := by
  unfold vSend hooksCKA sendSameEpoch
  simp only [hs, Bool.false_eq_true, ↓reduceIte, pure_bind]
  cases st.vS <;> rfl

omit [DecidableEq T] [DecidableEq M] [DecidableEq E] [DecidableEq I]
  [SampleableType KR] [SampleableType KC] [SampleableType CCoins] [SampleableType I]
  [SampleableType K] in
theorem send_not_sendsIn (st : RSt Γ T Sig SS RS) (m : M) (coins : CCoins)
    (hs : st.id.sendsIn (st.tcur + 1) = false) :
    send cka prng fs st m coins = sendSameEpoch fs st m := by
  unfold send sendSameEpoch
  simp only [hs, Bool.false_eq_true, ↓reduceIte]
  cases st.vS <;> rfl

omit [DecidableEq M] [DecidableEq E] [DecidableEq I]
  [SampleableType KR] [SampleableType KC] [SampleableType I]
  [SampleableType K] in
theorem vSend_sendsIn (s : SM.GameState (VPt Γ T Sig SS RS) M (Header T × E))
    (P : Party) (st : VPt Γ T Sig SS RS) (m : M) (pair : Option (M × M)) (r : Option CCoins)
    (hs : st.id.sendsIn (st.tcur + 1) = true) :
    vSend (hooksCKA cka prng fs Δcka (moP tL t)) s P st m pair r =
      ((hooksCKA cka prng fs Δcka (moP tL t)).startSend s P (st.tcur + 1) st.γ st.root r >>=
        fun res => match res with
        | none => pure none
        | some (γ', T', σ', ss) =>
          let h : Header T := (st.tcur + 1, some T')
          let out := fs.send ss h m
          pure (some ({ st with tcur := st.tcur + 1, γ := γ', curCkaMsg := some T', root := σ',
                                vS := some out.1 }, (h, out.2)))) := by
  unfold vSend
  simp only [hs, ↓reduceIte]
  congr 1
  funext res
  cases res <;> rfl

omit [DecidableEq T] [DecidableEq M] [DecidableEq E] [DecidableEq I]
  [SampleableType KR] [SampleableType KC] [SampleableType CCoins] [SampleableType I]
  [SampleableType K] in
theorem inv_record_not_sendsIn {σ : JSt Γ T Sig SS RS M E I}
    (hI : Inv cka Δcka tL t σ) (P : Party) (m : M) (isChall : Bool)
    (hs : P.sendsIn (σ.1.g.epoch P + 1) = false)
    (hch_ep : isChall = true → σ.1.g.epoch P = t) :
    let out := sendSameEpoch fs (σ.1.g.st P) m
    let outL := sendSameEpoch fs ((projGame σ).st P) m
    let rec_m : SM.Record M (Header T × E) := ⟨⟨P, σ.1.g.epoch P, σ.1.g.idx P + 1⟩, m, out.2⟩
    let σ' : JSt Γ T Sig SS RS M E I :=
      ({ σ.1 with g := σ.1.g.record (2 + Δcka) P out.1 rec_m isChall }, σ.2)
    outL.2 = out.2 ∧
    (projGame σ).record (2 + Δcka) P outL.1
        ⟨⟨P, (projGame σ).epoch P, (projGame σ).idx P + 1⟩, m, outL.2⟩ isChall = projGame σ' ∧
    Inv cka Δcka tL t σ' ∧
    (PostChall t σ.1.g → PostChall t σ'.1.g) ∧
    (isChall = true → PostChall t σ'.1.g) := by
  intro out outL rec_m σ'
  have hout_c : outL.2 = out.2 := by
    cases h : (σ.1.g.st P).vS <;> simp [outL, out, sendSameEpoch, projGame, projParty, realParty, h]
  have hout_st : outL.1 = projParty out.1 (σ.2.st P) := by
    cases h : (σ.1.g.st P).vS <;> simp [outL, out, sendSameEpoch, projGame, projParty, realParty, h]
  have hproj : (projGame σ).record (2 + Δcka) P outL.1
      ⟨⟨P, (projGame σ).epoch P, (projGame σ).idx P + 1⟩, m, outL.2⟩ isChall = projGame σ' := by
    rw [hout_c, hout_st]
    dsimp only [SM.GameState.record, projGame, σ']
    congr 1
    funext Q
    by_cases hQ : Q = P
    · subst Q; simp
    · simp [hQ]
  have hid_out : out.1.id = (σ.1.g.st P).id := by
    dsimp only [out, sendSameEpoch]; cases (σ.1.g.st P).vS <;> rfl
  have htcur_out : out.1.tcur = (σ.1.g.st P).tcur := by
    dsimp only [out, sendSameEpoch]; cases (σ.1.g.st P).vS <;> rfl
  have hTcur_out : out.1.curCkaMsg = (σ.1.g.st P).curCkaMsg := by
    dsimp only [out, sendSameEpoch]; cases (σ.1.g.st P).vS <;> rfl
  have hγ_out : out.1.γ = (σ.1.g.st P).γ := by
    dsimp only [out, sendSameEpoch]; cases (σ.1.g.st P).vS <;> rfl
  have hrΓ_eq : ∀ Q, rΓ σ' Q = rΓ σ Q := fun Q => by
    by_cases hQ : Q = P
    · subst Q; simp [rΓ, σ', SM.GameState.record, hγ_out]
    · simp [rΓ, σ', SM.GameState.record, hQ]
  have hs0 : P.sendsIn (σ.1.g.epoch P) = true := by
    have h := sendsIn_succ_eq_not P (σ.1.g.epoch P)
    rw [hs] at h
    revert h; cases P.sendsIn (σ.1.g.epoch P) <;> decide
  refine ⟨hout_c, hproj, ?_, ?_, ?_⟩
  · refine
      { habort := hI.habort
        hckb := hI.hckb
        hid := fun Q => by
          by_cases hQ : Q = P
          · subst Q; simp [σ', SM.GameState.record, hid_out, hI.hid P]
          · simp [σ', SM.GameState.record, hQ, hI.hid Q]
        htcur := fun Q => by
          by_cases hQ : Q = P
          · subst Q; simp [σ', SM.GameState.record, htcur_out, hI.htcur P]
          · simp [σ', SM.GameState.record, hQ, hI.htcur Q]
        hepoch_le := hI.hepoch_le
        hepoch_sync := hI.hepoch_sync
        hcomp := fun pos hpos => by
          simp only [σ', SM.GameState.record] at hpos ⊢
          split at hpos
          · exact hI.hcomp pos hpos
          · rename_i hnsafe
            simp only [List.mem_cons] at hpos
            rcases hpos with rfl | hpos_old
            · simp only [SM.GameState.safeCh, Bool.not_eq_true] at hnsafe
              exact hnsafe
            · exact hI.hcomp pos hpos_old
        hchall := fun pos hpos => by
          simp only [σ', SM.GameState.record] at hpos ⊢
          split at hpos
          · rename_i hch
            simp only [List.mem_cons] at hpos
            rcases hpos with rfl | hpos_old
            · have hep_t := hch_ep hch
              have hP_send : P = Party.senderOf t := by
                rw [hep_t] at hs0
                exact (sendsIn_iff_eq_senderOf P t).mp hs0
              refine ⟨hP_send, hep_t, ?_⟩
              rw [← hP_send, hep_t]
            · exact hI.hchall pos hpos_old
          · exact hI.hchall pos hpos
        hleaks_tL := hI.hleaks_tL
        htL_leaks := hI.htL_leaks
        htrans := fun r' hr' => by
          simp only [σ', SM.GameState.record, List.mem_cons] at hr' ⊢
          rcases hr' with rfl | hr'_old
          · refine ⟨le_rfl, ?_, fun _ => ?_⟩
            · dsimp only [rec_m, out, sendSameEpoch]
              cases (σ.1.g.st P).vS <;> exact hI.htcur P
            · dsimp only [rec_m, out, sendSameEpoch]
              simp only [Function.update_self]
              cases (σ.1.g.st P).vS <;> rfl
          · obtain ⟨h1, h2, h3⟩ := hI.htrans r' hr'_old
            refine ⟨h1, h2, fun h => ?_⟩
            rw [h3 h]
            by_cases hQ : r'.pos.sender = P
            · rw [hQ]; simp [hTcur_out]
            · simp [hQ]
        hγ_none := fun hn Q => by
          by_cases hQ : Q = P
          · subst Q
            simp only [σ', SM.GameState.record, Function.update_self, hγ_out]
            exact hI.hγ_none hn P
          · simp only [σ', SM.GameState.record, Function.update_of_ne hQ]
            exact hI.hγ_none hn Q
        hγ_some := fun l hl Q => by
          by_cases hQ : Q = P
          · subst Q
            refine ⟨?_, (hI.hγ_some l hl P).2⟩
            simp only [σ', SM.GameState.record, Function.update_self, hγ_out]
            exact (hI.hγ_some l hl P).1
          · refine ⟨?_, (hI.hγ_some l hl Q).2⟩
            simp only [σ', SM.GameState.record, Function.update_of_ne hQ]
            exact (hI.hγ_some l hl Q).1
        hcka_sync := fun Q h1 h2 rs => by
          rw [hrΓ_eq Q, hrΓ_eq Q.other]
          exact hI.hcka_sync Q h1 h2 rs
        hcka_split := fun Q h1 => by
          obtain ⟨T_e, hT, hcache, hlast, hagr⟩ := hI.hcka_split Q h1
          refine ⟨T_e, ?_, ?_, ?_, fun rs => ?_⟩
          · by_cases hQ : Q = P
            · subst Q; simp [σ', SM.GameState.record, hTcur_out, hT]
            · simp [σ', SM.GameState.record, hQ, hT]
          · rw [hrΓ_eq Q.other]
            exact hcache
          · intro hγO
            apply hlast
            by_cases hQ : Q.other = P
            · rw [hQ] at hγO ⊢; simp [σ', SM.GameState.record, hγ_out] at hγO; exact hγO
            · simp [σ', SM.GameState.record, hQ] at hγO; exact hγO
          · rw [hrΓ_eq Q, hrΓ_eq Q.other]
            exact hagr rs }
  · rintro ⟨hS, ⟨pos, hmem, hsend⟩ | hR⟩
    · refine ⟨hS, Or.inl ⟨pos, ?_, hsend⟩⟩
      simp only [σ', SM.GameState.record]
      split
      · exact List.mem_cons_of_mem _ hmem
      · exact hmem
    · exact ⟨hS, Or.inr hR⟩
  · intro hch
    have hep_t := hch_ep hch
    have hP_send : P = Party.senderOf t := by
      rw [hep_t] at hs0
      exact (sendsIn_iff_eq_senderOf P t).mp hs0
    refine ⟨?_, Or.inl ⟨rec_m.pos, ?_, hP_send⟩⟩
    · simp only [σ', SM.GameState.record, ← hP_send, hep_t, le_rfl]
    · simp only [σ', SM.GameState.record, hch, ↓reduceIte, List.mem_cons_self]

def updVSend (cka : CKAScheme KC Γ CCoins T I) (prng : PRFPRNG KR Sig I K)
    (fs : FSAEADScheme K SS RS (Header T) M E)
    (st : PartyState (Option Γ) T Sig SS RS) (rΓP : Γ) (γ' : Option Γ) (m : M) (coins : CCoins) :
    PartyState (Option Γ) T Sig SS RS × (Header T × E) :=
  let c := cka.send rΓP coins
  let p := prng.up st.root c.2.2
  let h : Header T := (st.tcur + 1, some c.2.1)
  let out := fs.send (fs.initSender p.2) h m
  ({ st with tcur := st.tcur + 1, γ := γ', curCkaMsg := some c.2.1, root := p.1, vS := some out.1 },
   (h, out.2))

def afterStartSend (cka : CKAScheme KC Γ CCoins T I) (prng : PRFPRNG KR Sig I K)
    (fs : FSAEADScheme K SS RS (Header T) M E) (Δcka : ℕ)
    (σ : JSt Γ T Sig SS RS M E I)
    (s₁ : SM.GameState (VPt Γ T Sig SS RS) M (Header T × E))
    (P : Party) (m : M) (isChall : Bool)
    (coins : CCoins) (γ' : Option Γ) (ck' : CKA.GameState Γ T) :
    Option (Header T × E) × JSt Γ T Sig SS RS M E I :=
  let c := cka.send (rΓ σ P) coins
  let out := updVSend cka prng fs (σ.1.g.st P) (rΓ σ P) γ' m coins
  let h' : CKAState T I :=
    { cache := Function.update σ.1.h.cache (σ.1.g.epoch P + 1) (some (c.2.1, c.2.2)) }
  let rec_m : SM.Record M (Header T × E) := ⟨⟨P, s₁.epoch P, s₁.idx P + 1⟩, m, out.2⟩
  let g' := s₁.record (2 + Δcka) P out.1 rec_m isChall
  (some out.2, ({ σ.1 with g := g', h := h' }, ck'))

omit [DecidableEq T] [DecidableEq M] [DecidableEq E] [DecidableEq I]
  [SampleableType KR] [SampleableType KC] [SampleableType CCoins] [SampleableType I]
  [SampleableType K] in
theorem inv_afterStartSend {σ : JSt Γ T Sig SS RS M E I}
    {s₁ : SM.GameState (VPt Γ T Sig SS RS) M (Header T × E)}
    (hI : Inv cka Δcka tL t σ) (P : Party) (m : M) (bad isChall : Bool)
    (hep : σ.1.g.epMgmt (2 + Δcka) qep P bad = some s₁)
    (hs : P.sendsIn (σ.1.g.epoch P + 1) = true)
    (hch_ep : isChall = true → s₁.epoch P = t)
    (coins : CCoins) (γ' : Option Γ) (ck' : CKA.GameState Γ T)
    (hγ_none' : tL = none → γ'.isSome = true)
    (hγ_some' : ∀ l, tL = some l →
      γ'.isSome = decide (healEpoch tL + Δcka ≤ σ.1.g.epoch P + 1) ∧
      ck'.epoch P = min (σ.1.g.epoch P + 1) (healEpoch tL + Δcka) ∧
      ck'.epoch P.other = σ.2.epoch P.other)
    (hckb' : ck'.b = false)
    (hck_stO : ck'.st P.other = σ.2.st P.other)
    (hrΓ' : γ'.getD (ck'.st P) = (cka.send (rΓ σ P) coins).1)
    (hlast' : (σ.1.g.st P.other).γ = none → ck'.lastMsg = some (cka.send (rΓ σ P) coins).2.1) :
    let sL₁ := projGame ({ σ.1 with g := s₁ }, σ.2)
    let outL := send cka prng fs (sL₁.st P) m coins
    let res := afterStartSend cka prng fs Δcka σ s₁ P m isChall coins γ' ck'
    (res.1, projGame res.2) =
      (some outL.2,
        sL₁.record (2 + Δcka) P outL.1 ⟨⟨P, sL₁.epoch P, sL₁.idx P + 1⟩, m, outL.2⟩ isChall) ∧
    Inv cka Δcka tL t res.2 ∧
    (PostChall t σ.1.g → PostChall t res.2.1.g) ∧
    (isChall = true → PostChall t res.2.1.g) := by
  intro sL₁ outL res
  have hprops := epMgmt_inv_props cka Δcka qep tL t hI P bad hep
  rcases hprops with ⟨hst₁, htr₁, hch₁, hcomp₁, _, _, hs_ep₁, hep_mono,
    hcomp_s₁, hleaks_s₁, htL_s₁, _, hs_true⟩
  obtain ⟨hsync, hep₁_P, hep₁_O, _, _⟩ := hs_true hs
  have hs_stL : (sL₁.st P).id.sendsIn ((sL₁.st P).tcur + 1) = true := by
    dsimp only [sL₁, projGame, projParty, realParty]
    rw [hst₁, hI.hid P, hI.htcur P]
    exact hs
  have houtL_2 : outL.2 = (updVSend cka prng fs (σ.1.g.st P) (rΓ σ P) γ' m coins).2 := by
    dsimp only [outL, send, updVSend]
    simp only [hs_stL, ↓reduceIte]
    dsimp only [sL₁, projGame, projParty, realParty, rΓ]
    rw [hst₁]
  have houtL_1 : outL.1 =
      projParty (updVSend cka prng fs (σ.1.g.st P) (rΓ σ P) γ' m coins).1 (ck'.st P) := by
    dsimp only [outL, send, updVSend]
    simp only [hs_stL, ↓reduceIte]
    dsimp only [sL₁, projGame, projParty, realParty, rΓ]
    rw [hst₁, hrΓ']
    rfl
  have hproj_eq : (res.1, projGame res.2) =
      (some outL.2,
        sL₁.record (2 + Δcka) P outL.1 ⟨⟨P, sL₁.epoch P, sL₁.idx P + 1⟩, m, outL.2⟩ isChall) := by
    dsimp only [res, afterStartSend]
    rw [houtL_2, houtL_1]
    congr 1
    dsimp only [SM.GameState.record, projGame, sL₁]
    congr 1
    funext Q
    by_cases hQ : Q = P
    · subst Q; simp
    · have hQo : Q = P.other := by cases P <;> cases Q <;> first | rfl | contradiction
      subst Q
      simp [hQ, projParty, realParty, hck_stO]
  have hrΓ_P : rΓ res.2 P = (cka.send (rΓ σ P) coins).1 := by
    simp [rΓ, res, afterStartSend, SM.GameState.record, updVSend, hrΓ']
  have hrΓ_O : rΓ res.2 P.other = rΓ σ P.other := by
    have hne : P.other ≠ P := by cases P <;> decide
    simp [rΓ, res, afterStartSend, SM.GameState.record, hne, hst₁, hck_stO]
  refine ⟨hproj_eq, ?_, ?_, ?_⟩
  · refine
      { habort := hI.habort
        hckb := hckb'
        hid := fun Q => by
          by_cases hQ : Q = P
          · subst Q; simp [res, afterStartSend, SM.GameState.record, updVSend, hI.hid P]
          · simp [res, afterStartSend, SM.GameState.record, hQ, hst₁, hI.hid Q]
        htcur := fun Q => by
          by_cases hQ : Q = P
          · subst Q
            simp [res, afterStartSend, SM.GameState.record, updVSend, hI.htcur P, hep₁_P]
          · have hQo : Q = P.other := by cases P <;> cases Q <;> first | rfl | contradiction
            subst Q
            simp [res, afterStartSend, SM.GameState.record, hQ, hst₁, hI.htcur P.other,
              hep₁_O, hsync]
        hepoch_le := fun Q => by
          by_cases hQ : Q = P
          · subst Q
            simp only [res, afterStartSend, SM.GameState.record, hep₁_P, hep₁_O]
            exact le_rfl
          · have hQo : Q = P.other := by cases P <;> cases Q <;> first | rfl | contradiction
            subst Q
            simp only [res, afterStartSend, SM.GameState.record, Party.other_other, hep₁_P, hep₁_O]
            omega
        hepoch_sync := fun Q hns => by
          exfalso
          by_cases hQ : Q = P
          · subst Q
            simp only [res, afterStartSend, SM.GameState.record, hep₁_P] at hns
            rw [hs] at hns; cases hns
          · have hQo : Q = P.other := by cases P <;> cases Q <;> first | rfl | contradiction
            subst Q
            simp only [res, afterStartSend, SM.GameState.record, hep₁_O] at hns
            have h1 := sendsIn_other_eq_not P (σ.1.g.epoch P)
            have h2 := sendsIn_succ_eq_not P (σ.1.g.epoch P)
            rw [hs] at h2
            rw [hns] at h1
            revert h1 h2; cases P.sendsIn (σ.1.g.epoch P) <;> decide
        hcomp := fun pos hpos => by
          simp only [res, afterStartSend, SM.GameState.record] at hpos ⊢
          split at hpos
          · exact hcomp_s₁ pos hpos
          · rename_i hnsafe
            simp only [List.mem_cons] at hpos
            rcases hpos with rfl | hpos_old
            · simp only [SM.GameState.safeCh, Bool.not_eq_true] at hnsafe
              exact hnsafe
            · exact hcomp_s₁ pos hpos_old
        hchall := fun pos hpos => by
          simp only [res, afterStartSend, SM.GameState.record] at hpos ⊢
          split at hpos
          · rename_i hch
            simp only [List.mem_cons] at hpos
            rcases hpos with rfl | hpos_old
            · have hep_t := hch_ep hch
              have hP_send : P = Party.senderOf t := by
                rw [hep_t] at hs_ep₁
                exact (sendsIn_iff_eq_senderOf P t).mp hs_ep₁
              refine ⟨hP_send, hep_t, ?_⟩
              rw [← hP_send, hep_t]
            · rw [hch₁] at hpos_old
              obtain ⟨h1, h2, h3⟩ := hI.hchall pos hpos_old
              exact ⟨h1, h2, h3.trans (hep_mono _)⟩
          · rw [hch₁] at hpos
            obtain ⟨h1, h2, h3⟩ := hI.hchall pos hpos
            exact ⟨h1, h2, h3.trans (hep_mono _)⟩
        hleaks_tL := hleaks_s₁
        htL_leaks := htL_s₁
        htrans := fun r' hr' => by
          simp only [res, afterStartSend, SM.GameState.record, List.mem_cons] at hr' ⊢
          rcases hr' with rfl | hr'_old
          · refine ⟨le_rfl, ?_, fun _ => ?_⟩
            · dsimp only [updVSend]
              rw [hI.htcur P, hep₁_P]
            · simp [updVSend]
          · rw [htr₁] at hr'_old
            obtain ⟨h1, h2, _⟩ := hI.htrans r' hr'_old
            refine ⟨h1.trans (hep_mono _), h2, fun h => ?_⟩
            exfalso
            by_cases hQ : r'.pos.sender = P
            · rw [hQ, hep₁_O] at h
              rw [hQ] at h1
              omega
            · have hQo : r'.pos.sender = P.other := by
                cases P <;> cases hS : r'.pos.sender <;> simp_all [Party.other]
              rw [hQo, Party.other_other, hep₁_P] at h
              rw [hQo, ← hsync] at h1
              omega
        hγ_none := fun hn Q => by
          by_cases hQ : Q = P
          · subst Q
            simp [res, afterStartSend, SM.GameState.record, updVSend, hγ_none' hn]
          · simp [res, afterStartSend, SM.GameState.record, hQ, hst₁, hI.hγ_none hn Q]
        hγ_some := fun l hl Q => by
          by_cases hQ : Q = P
          · subst Q
            obtain ⟨h1, h2, _⟩ := hγ_some' l hl
            simp [res, afterStartSend, SM.GameState.record, updVSend, hep₁_P, h1, h2]
          · have hQo : Q = P.other := by cases P <;> cases Q <;> first | rfl | contradiction
            subst Q
            obtain ⟨_, _, h3⟩ := hγ_some' l hl
            have hO := hI.hγ_some l hl P.other
            rw [← hsync] at hO
            simp [res, afterStartSend, SM.GameState.record, hQ, hst₁, hep₁_O, h3, hO.1, hO.2]
        hcka_sync := fun Q h => by
          exfalso
          by_cases hQ : Q = P
          · subst Q
            simp only [res, afterStartSend, SM.GameState.record, hep₁_P, hep₁_O] at h
            omega
          · have hQo : Q = P.other := by cases P <;> cases Q <;> first | rfl | contradiction
            subst Q
            simp only [res, afterStartSend, SM.GameState.record, Party.other_other,
              hep₁_P, hep₁_O] at h
            omega
        hcka_split := fun Q h => by
          by_cases hQ : Q = P
          · subst Q
            let c := cka.send (rΓ σ P) coins
            refine ⟨c.2.1, ?_, ?_, ?_, ?_⟩
            · simp [res, afterStartSend, SM.GameState.record, updVSend, c]
            · rw [hrΓ_O]
              simp only [res, afterStartSend, SM.GameState.record, hep₁_P, Function.update_self]
              have hagr := hI.hcka_sync P hsync hs [coins]
              dsimp only [CKAScheme.AgreesFrom] at hagr
              rw [hagr.1]
            · intro hγO
              have hne : P.other ≠ P := by cases P <;> decide
              simp only [res, afterStartSend, SM.GameState.record, Function.update_of_ne hne,
                hst₁] at hγO
              exact hlast' hγO
            · intro rs
              rw [hrΓ_P, hrΓ_O]
              have hagr := hI.hcka_sync P hsync hs (coins :: rs)
              dsimp only [CKAScheme.AgreesFrom] at hagr
              exact hagr.2
          · exfalso
            have hQo : Q = P.other := by cases P <;> cases Q <;> first | rfl | contradiction
            subst Q
            simp only [res, afterStartSend, SM.GameState.record, Party.other_other,
              hep₁_P, hep₁_O] at h
            omega }
  · rintro ⟨hS, ⟨pos, hmem, hsend⟩ | hR⟩
    · refine ⟨hS.trans (hep_mono _), Or.inl ⟨pos, ?_, hsend⟩⟩
      simp only [res, afterStartSend, SM.GameState.record]
      rw [hch₁]
      split
      · exact List.mem_cons_of_mem _ hmem
      · exact hmem
    · exact ⟨hS.trans (hep_mono _), Or.inr (hR.trans (hep_mono _))⟩
  · intro hch
    have hep_t := hch_ep hch
    have hP_send : P = Party.senderOf t := by
      rw [hep_t] at hs_ep₁
      exact (sendsIn_iff_eq_senderOf P t).mp hs_ep₁
    refine ⟨?_, Or.inl ⟨⟨P, s₁.epoch P, s₁.idx P + 1⟩, ?_, hP_send⟩⟩
    · simp only [res, afterStartSend, SM.GameState.record, ← hP_send, hep_t, le_rfl]
    · simp only [res, afterStartSend, SM.GameState.record, hch, ↓reduceIte, List.mem_cons_self]

omit [Inhabited E] [DecidableEq T] [DecidableEq M] [DecidableEq E] [DecidableEq I]
  [SampleableType KR] [SampleableType KC] [SampleableType CCoins] [SampleableType I]
  [SampleableType K] in
theorem doom_of_sendBad_abort {σ : JSt Γ T Sig SS RS M E I}
    {s₁ : SM.GameState (VPt Γ T Sig SS RS) M (Header T × E)}
    {s_out : SM.GameState (RSt Γ T Sig SS RS) M (Header T × E)}
    (hI : Inv cka Δcka tL t σ) (P : Party) (l : ℕ)
    (hl : tL = some l)
    (hep : σ.1.g.epMgmt (2 + Δcka) qep P true = some s₁)
    (hs : P.sendsIn (σ.1.g.epoch P + 1) = true)
    (hγ : (σ.1.g.st P).γ = none)
    (hLD : (polP tL t).leakDoom σ.1.g s₁ = false)
    (hbad_cka : ¬ (σ.1.g.epoch P + 1 + 2 ≤ healEpoch tL))
    (hleaks_out : s_out.leaks = s₁.leaks)
    (hepoch_out : s_out.epoch = s₁.epoch) :
    DoomFixedB (2 + Δcka) tL t s_out := by
  have hprops := epMgmt_inv_props cka Δcka qep tL t hI P true hep
  obtain ⟨hsync, hep₁_P, hep₁_O, htL₁, hleaks₁⟩ :=
    hprops.2.2.2.2.2.2.2.2.2.2.2.2 hs
  have hsyncAB : σ.1.g.epoch .A = σ.1.g.epoch .B := by
    cases P <;> [exact hsync; exact hsync.symm]
  have hγP := (hI.hγ_some l hl P).1
  rw [hγ, Option.isSome_none, eq_comm, decide_eq_false_iff_not] at hγP
  simp only [hl, healEpoch] at hγP hbad_cka
  by_cases hsafe : σ.1.g.safeCh (2 + Δcka) P = true
  · right; right
    refine ⟨l, hl, ?_⟩
    unfold DoomD3
    rw [hleaks_out, hepoch_out]
    simp only [hsafe, Bool.not_true, Bool.and_false] at hleaks₁
    rw [hleaks₁]
    have hl_not_mem : l ∉ σ.1.g.leaks := by
      intro hmem
      obtain ⟨l₀, htL₀, hle₁, _⟩ := hI.hleaks_tL l hmem
      unfold SM.GameState.safeCh at hsafe
      rw [htL₀] at hsafe
      simp only [SM.healedBy, decide_eq_true_eq] at hsafe
      omega
    refine ⟨hl_not_mem, ?_, ?_, ?_⟩
    · cases P <;> (dsimp only [Party.other] at hep₁_O; simp only [hep₁_P, hep₁_O] at *; omega)
    · cases P <;> (dsimp only [Party.other] at hep₁_O; simp only [hep₁_P, hep₁_O] at *; omega)
    · cases P <;> (dsimp only [Party.other] at hep₁_O; simp only [hep₁_P, hep₁_O] at *; omega)
  · left
    simp only [hsafe, Bool.not_false, Bool.and_true, ↓reduceIte] at hleaks₁
    let l_new := SM.maxOpt σ.1.g.tL (σ.1.g.epoch P + 1)
    have hl_mem : l_new ∈ s₁.leaks := by rw [hleaks₁]; exact List.mem_cons_self
    have hep_le_lnew : σ.1.g.epoch P + 1 ≤ l_new := le_maxOpt_right σ.1.g.tL (σ.1.g.epoch P + 1)
    have hl_lt : l < l_new := by omega
    unfold Policy.leakDoom polP at hLD
    rw [Bool.or_eq_false_iff] at hLD
    rcases hLD with ⟨hd1, hd2⟩
    rw [List.any_eq_false] at hd1
    have ht_le_lnew : t ≤ l_new := by
      have h := hd1 l_new hl_mem
      dsimp only [SM.ltOpt] at h
      rw [hl] at h
      simp only [Bool.and_eq_true, decide_eq_true_eq, not_and, not_lt] at h
      exact h hl_lt
    have ht_le_S : t ≤ σ.1.g.epoch (Party.senderOf t) := by
      rw [Bool.and_eq_false_imp, List.any_eq_true] at hd2
      have h := hd2 ⟨l_new, hl_mem, decide_eq_true ht_le_lnew⟩
      exact decide_eq_false_iff_not.mp h |> Nat.not_lt.mp
    have ht_le_P : t ≤ σ.1.g.epoch P := by
      cases P <;> cases hS : Party.senderOf t <;>
        (simp only [hS] at ht_le_S; omega)
    rw [hl]
    simp only [SM.lastLeakGuessAdmissible, SM.healedBy, decide_eq_false_iff_not]
    omega

abbrev rhsSendStep (s₁ : SM.GameState (VPt Γ T Sig SS RS) M (Header T × E))
    (P : Party) (m : M) (pair : Option (M × M)) (r : Option CCoins) (isChall : Bool) :
    EMc Γ CCoins T I Sig SS RS M E (Option (Header T × E)) := do
  match ← liftH (vSend (hooksCKA cka prng fs Δcka (moP tL t)) s₁ P (s₁.st P) m pair r) with
  | none =>
    abortE
    return none
  | some (st', c) =>
    modify fun es =>
      { es with g := s₁.record (2 + Δcka) P st' ⟨⟨P, s₁.epoch P, s₁.idx P + 1⟩, m, c⟩ isChall }
    return some c

abbrev lhsSendStepCoins (sL₁ : SM.GameState (RSt Γ T Sig SS RS) M (Header T × E))
    (P : Party) (m : M) (coins : CCoins) (isChall : Bool) :
    Option (Header T × E) × SM.GameState (RSt Γ T Sig SS RS) M (Header T × E) :=
  let out := send cka prng fs (sL₁.st P) m coins
  (some out.2,
    sL₁.record (2 + Δcka) P out.1 ⟨⟨P, sL₁.epoch P, sL₁.idx P + 1⟩, m, out.2⟩ isChall)

omit [DecidableEq M] [DecidableEq E] [DecidableEq I]
  [SampleableType KR] [SampleableType KC] [SampleableType K] in
theorem Y_rhsSendStep_sendsIn {σ : JSt Γ T Sig SS RS M E I}
    {s₁ : SM.GameState (VPt Γ T Sig SS RS) M (Header T × E)}
    (P : Party) (m : M) (pair : Option (M × M)) (r : Option CCoins) (isChall : Bool)
    (hst₁ : s₁.st = σ.1.g.st)
    (hs_st : (σ.1.g.st P).id.sendsIn ((σ.1.g.st P).tcur + 1) = true) :
    Y cka Δcka tL (rhsSendStep cka prng fs Δcka tL t s₁ P m pair r isChall) σ =
      (Y cka Δcka tL
        (liftH ((hooksCKA cka prng fs Δcka (moP tL t)).startSend
          s₁ P ((σ.1.g.st P).tcur + 1) (σ.1.g.st P).γ (σ.1.g.st P).root r)) σ >>=
        fun z => match z.1 with
        | none => pure (none, ({ z.2.1 with abort := true }, z.2.2))
        | some (γ', T', σ', ss) =>
          let st := σ.1.g.st P
          let h : Header T := (st.tcur + 1, some T')
          let out := fs.send ss h m
          let st' : VPt Γ T Sig SS RS :=
            { st with tcur := st.tcur + 1, γ := γ', curCkaMsg := some T', root := σ', vS := some out.1 }
          let c : Header T × E := (h, out.2)
          let g' := s₁.record (2 + Δcka) P st' ⟨⟨P, s₁.epoch P, s₁.idx P + 1⟩, m, c⟩ isChall
          pure (some c, ({ z.2.1 with g := g' }, z.2.2))) := by
  unfold rhsSendStep
  rw [hst₁, vSend_sendsIn cka prng fs Δcka tL t s₁ P (σ.1.g.st P) m pair r hs_st]
  rw [Y_bind, Y_liftH_bind, bind_assoc]
  congr 1
  funext ⟨res, σ₁⟩
  cases res with
  | none =>
    rw [Y_liftH_pure, pure_bind, Y_bind, Y_abortE, pure_bind, Y_pure]
  | some val =>
    rcases val with ⟨γ', T', σ', ss⟩
    rw [Y_liftH_pure, pure_bind, Y_bind, Y_modify, pure_bind, Y_pure]

omit [DecidableEq M] [DecidableEq E] [DecidableEq I] [Inhabited E]
  [SampleableType KR] [SampleableType KC] [SampleableType K] in
theorem Y_startSend_of_some {σ : JSt Γ T Sig SS RS M E I}
    (s₁ : SM.GameState (VPt Γ T Sig SS RS) M (Header T × E))
    (P : Party) (r : Option CCoins) (γ : Γ) (hγ : (σ.1.g.st P).γ = some γ) :
    Y cka Δcka tL
      (liftH ((hooksCKA cka prng fs Δcka (moP tL t)).startSend
        s₁ P (σ.1.g.epoch P + 1) (σ.1.g.st P).γ (σ.1.g.st P).root r)) σ =
      (samIfNecFst r >>= fun coins =>
        let c := cka.send (rΓ σ P) coins
        let p := prng.up (σ.1.g.st P).root c.2.2
        let h' : CKAState T I :=
          { cache := Function.update σ.1.h.cache (σ.1.g.epoch P + 1) (some (c.2.1, c.2.2)) }
        pure (some (some c.1, c.2.1, p.1, fs.initSender p.2),
          ({ σ.1 with h := h' }, σ.2))) := by
  have hrΓ : rΓ σ P = γ := by simp [rΓ, hγ]
  rw [hγ, hrΓ]
  cases r with
  | some coins =>
    unfold hooksCKA samIfNecFst
    dsimp only
    rw [pure_bind, pure_bind, Y_liftH_bind, Y_cacheC, pure_bind, Y_liftH_pure]
  | none =>
    unfold hooksCKA samIfNecFst
    dsimp only
    rw [Y_liftH_bind, Y_sampleT, map_eq_bind_pure_comp]
    simp only [Function.comp_apply, bind_assoc, pure_bind]
    congr 1

omit [DecidableEq T] [DecidableEq M] [DecidableEq E] [DecidableEq I] [Inhabited E]
  [SampleableType KR] [SampleableType KC] [SampleableType K] in
theorem Y_startSend_tail_some {σ : JSt Γ T Sig SS RS M E I}
    (P : Party) (coins : CCoins)
    (ck' : CKA.GameState Γ T)
    (hck_stP : ck'.st P = (cka.send (rΓ σ P) coins).1)
    (hck_epP : ck'.epoch P = σ.1.g.epoch P + 1) :
    let c := cka.send (rΓ σ P) coins
    let e := σ.1.g.epoch P + 1
    let p := prng.up (σ.1.g.st P).root c.2.2
    let γ' : Option Γ := if healEpoch tL + Δcka ≤ e then some c.1 else none
    let h' : CKAState T I := { cache := Function.update σ.1.h.cache e (some (c.2.1, c.2.2)) }
    Y cka Δcka tL
      (liftH (do
        cacheC e (c.2.1, c.2.2)
        if (moP tL t).tH + Δcka ≤ e then
          match ← liftC (CKA.corrQuery P) with
          | none => return none
          | some γ => return some (some γ, c.2.1, p.1, fs.initSender p.2)
        else return some (none, c.2.1, p.1, fs.initSender p.2))) (σ.1, ck') =
      pure (some (γ', c.2.1, p.1, fs.initSender p.2), ({ σ.1 with h := h' }, ck')) := by
  intro c e p γ' h'
  rw [Y_liftH_bind, Y_cacheC, pure_bind]
  dsimp only [moP, Mode.tH, γ']
  by_cases hfin : healEpoch tL + Δcka ≤ e
  · simp only [hfin, ↓reduceIte]
    rw [Y_liftH_bind, Y_corrQuery]
    have hfinished : ck'.finished Δcka (healEpoch tL) P = true := by
      unfold CKA.GameState.finished
      rw [hck_epP]
      exact decide_eq_true hfin
    unfold CKA.corrImpl
    simp only [StateT.run_bind, StateT.run_get, pure_bind, hfinished, Bool.or_true, ↓reduceIte,
      StateT.run_pure, map_pure, pure_bind, hck_stP]
    rw [Y_liftH_pure]
  · simp only [hfin, ↓reduceIte]
    rw [Y_liftH_pure]

omit [DecidableEq M] [DecidableEq E] [DecidableEq I]
  [SampleableType KR] [SampleableType KC] [SampleableType K] in
theorem sendStep_sim {σ : JSt Γ T Sig SS RS M E I}
    {s₁ : SM.GameState (VPt Γ T Sig SS RS) M (Header T × E)}
    (hI : Inv cka Δcka tL t σ) (P : Party) (m : M) (pair : Option (M × M))
    (r : Option CCoins) (isChall : Bool)
    (hep : σ.1.g.epMgmt (2 + Δcka) qep P r.isSome = some s₁)
    (hLD : (polP tL t).leakDoom σ.1.g s₁ = false)
    (hch_ep : isChall = true → s₁.epoch P = t) :
    (DEq (samIfNecFst r >>= fun coins =>
            pure (lhsSendStepCoins cka prng fs Δcka (projGame ({ σ.1 with g := s₁ }, σ.2)) P m coins isChall))
         ((fun z => (z.1, projGame z.2)) <$>
            Y cka Δcka tL (rhsSendStep cka prng fs Δcka tL t s₁ P m pair r isChall) σ) ∧
      ∀ z ∈ support (Y cka Δcka tL (rhsSendStep cka prng fs Δcka tL t s₁ P m pair r isChall) σ),
        Inv cka Δcka tL t z.2 ∧
        (PostChall t σ.1.g → PostChall t z.2.1.g) ∧
        (isChall = true → PostChall t z.2.1.g)) ∨
    ((∀ z ∈ support (Y cka Δcka tL (rhsSendStep cka prng fs Δcka tL t s₁ P m pair r isChall) σ),
        z.2.1.abort = true) ∧
      ∀ z ∈ support (samIfNecFst r >>= fun coins =>
          pure (lhsSendStepCoins cka prng fs Δcka (projGame ({ σ.1 with g := s₁ }, σ.2)) P m coins isChall)),
        DoomFixedB (2 + Δcka) tL t z.2) := by
  let sL₁ := projGame ({ σ.1 with g := s₁ }, σ.2)
  let lhs := samIfNecFst r >>= fun coins =>
    pure (lhsSendStepCoins cka prng fs Δcka sL₁ P m coins isChall)
  let rhs := Y cka Δcka tL (rhsSendStep cka prng fs Δcka tL t s₁ P m pair r isChall) σ
  change (DEq lhs ((fun z => (z.1, projGame z.2)) <$> rhs) ∧
      ∀ z ∈ support rhs,
        Inv cka Δcka tL t z.2 ∧
        (PostChall t σ.1.g → PostChall t z.2.1.g) ∧
        (isChall = true → PostChall t z.2.1.g)) ∨
    ((∀ z ∈ support rhs, z.2.1.abort = true) ∧
      ∀ z ∈ support lhs, DoomFixedB (2 + Δcka) tL t z.2)
  have hprops := epMgmt_inv_props cka Δcka qep tL t hI P r.isSome hep
  have hst₁ : s₁.st = σ.1.g.st := hprops.1
  have hs_false := hprops.2.2.2.2.2.2.2.2.2.2.2.1
  have hs_true := hprops.2.2.2.2.2.2.2.2.2.2.2.2
  by_cases hs : P.sendsIn (σ.1.g.epoch P + 1) = true
  · obtain ⟨hsync, hep₁_P, hep₁_O, _, _⟩ := hs_true hs
    have hs_st : (σ.1.g.st P).id.sendsIn ((σ.1.g.st P).tcur + 1) = true := by
      rw [hI.hid P, hI.htcur P]; exact hs
    have hrhs_base :=
      Y_rhsSendStep_sendsIn cka prng fs Δcka tL t P m pair r isChall hst₁ hs_st
    rw [hI.htcur P] at hrhs_base
    cases hγ : (σ.1.g.st P).γ with
    | some γ =>
      left
      have hrhs : rhs = (samIfNecFst r >>= fun coins =>
          pure (afterStartSend cka prng fs Δcka σ s₁ P m isChall coins
            (some (cka.send (rΓ σ P) coins).1) σ.2)) := by
        dsimp only [rhs]
        rw [hrhs_base, Y_startSend_of_some cka prng fs Δcka tL t s₁ P r γ hγ, bind_assoc]
        congr 1
      have hall : ∀ coins : CCoins,
          let res := afterStartSend cka prng fs Δcka σ s₁ P m isChall coins
            (some (cka.send (rΓ σ P) coins).1) σ.2
          (res.1, projGame res.2) = lhsSendStepCoins cka prng fs Δcka sL₁ P m coins isChall ∧
          Inv cka Δcka tL t res.2 ∧
          (PostChall t σ.1.g → PostChall t res.2.1.g) ∧
          (isChall = true → PostChall t res.2.1.g) := fun coins => by
        apply inv_afterStartSend cka prng fs Δcka qep tL t hI P m r.isSome isChall hep hs hch_ep
          coins (some (cka.send (rΓ σ P) coins).1) σ.2
        · intro _; rfl
        · intro l hl
          have hγP := (hI.hγ_some l hl P).1
          have hepP := (hI.hγ_some l hl P).2
          rw [hγ, Option.isSome_some, eq_comm, decide_eq_true_eq] at hγP
          refine ⟨by simp; omega, ?_, rfl⟩
          rw [hepP]; omega
        · exact hI.hckb
        · rfl
        · rfl
        · intro hγO
          exfalso
          cases htL : tL with
          | none =>
            have h := hI.hγ_none htL P.other
            simp [hγO] at h
          | some l =>
            have h1 := (hI.hγ_some l htL P).1
            have h2 := (hI.hγ_some l htL P.other).1
            rw [← hsync, ← h1] at h2
            simp [hγ, hγO] at h2
      have hmap : ((fun z => (z.1, projGame z.2)) <$> rhs) = lhs := by
        rw [hrhs, map_eq_bind_pure_comp]
        dsimp only [lhs]
        simp only [Function.comp_apply, bind_assoc, pure_bind]
        congr 1; funext coins
        rw [(hall coins).1]
      refine ⟨DEq.of_eq hmap.symm, fun z hz => ?_⟩
      rw [hrhs, mem_support_bind_iff] at hz
      rcases hz with ⟨coins, _, hzx⟩
      rw [support_pure, Set.mem_singleton_iff] at hzx
      rw [hzx]
      exact ⟨(hall coins).2.1, (hall coins).2.2.1, (hall coins).2.2.2⟩
    | none =>
      have htL_some : ∃ l, tL = some l := by
        cases htL : tL with
        | none =>
          have h := hI.hγ_none htL P
          simp [hγ] at h
        | some l => exact ⟨l, rfl⟩
      rcases htL_some with ⟨l, hl⟩
      have hγP := (hI.hγ_some l hl P).1
      have hepP := (hI.hγ_some l hl P).2
      have hepO := (hI.hγ_some l hl P.other).2
      rw [hγ, Option.isSome_none, eq_comm, decide_eq_false_iff_not] at hγP
      have hck_epP : σ.2.epoch P = σ.1.g.epoch P := by rw [hepP]; omega
      have hck_epO : σ.2.epoch P.other = σ.1.g.epoch P := by rw [hepO, ← hsync]; omega
      have hcanSend : σ.2.canSend P = true := by
        unfold CKA.GameState.canSend
        rw [hck_epP, hck_epO]
        simp [hs]
      have hrΓ_P : rΓ σ P = σ.2.st P := by simp [rΓ, hγ]
      have hne_O : P.other ≠ P := by cases P <;> decide
      have hall_none : ∀ coins : CCoins,
          let c := cka.send (rΓ σ P) coins
          let γ' : Option Γ := if healEpoch tL + Δcka ≤ σ.1.g.epoch P + 1 then some c.1 else none
          let ck' := σ.2.afterSend P c.1 c.2.1
          let res := afterStartSend cka prng fs Δcka σ s₁ P m isChall coins γ' ck'
          (res.1, projGame res.2) = lhsSendStepCoins cka prng fs Δcka sL₁ P m coins isChall ∧
          Inv cka Δcka tL t res.2 ∧
          (PostChall t σ.1.g → PostChall t res.2.1.g) ∧
          (isChall = true → PostChall t res.2.1.g) := fun coins => by
        intro c γ' ck'
        apply inv_afterStartSend cka prng fs Δcka qep tL t hI P m r.isSome isChall hep hs hch_ep
          coins γ' ck'
        · intro hn; rw [hl] at hn; cases hn
        · intro l' _
          refine ⟨?_, ?_, ?_⟩
          · dsimp only [γ']; split <;> rename_i h <;> simp [h]
          · simp only [ck', CKA.GameState.afterSend, Function.update_self, hck_epP]
            omega
          · simp [ck', CKA.GameState.afterSend, hne_O]
        · exact hI.hckb
        · simp [ck', CKA.GameState.afterSend, hne_O]
        · dsimp only [γ', ck', CKA.GameState.afterSend, c]; split <;> simp
        · intro _; rfl
      cases r with
      | none =>
        left
        have hstart_none :
            Y cka Δcka tL
              (liftH ((hooksCKA cka prng fs Δcka (moP tL t)).startSend
                s₁ P (σ.1.g.epoch P + 1) (σ.1.g.st P).γ (σ.1.g.st P).root none)) σ =
              ($ᵗ CCoins >>= fun coins =>
                let c := cka.send (rΓ σ P) coins
                let e := σ.1.g.epoch P + 1
                let p := prng.up (σ.1.g.st P).root c.2.2
                let γ' : Option Γ := if healEpoch tL + Δcka ≤ e then some c.1 else none
                let h' : CKAState T I :=
                  { cache := Function.update σ.1.h.cache e (some (c.2.1, c.2.2)) }
                pure (some (γ', c.2.1, p.1, fs.initSender p.2),
                  ({ σ.1 with h := h' }, σ.2.afterSend P c.1 c.2.1))) := by
          rw [hγ]
          unfold hooksCKA
          dsimp only
          split
          · rename_i he
            rw [Y_liftH_bind, Y_challQuery]
            change σ.1.g.epoch P + 1 = healEpoch tL at he
            have hbeq : (σ.2.epoch P + 1 != healEpoch tL) = false := by
              rw [hck_epP, he]; simp
            simp only [CKA.challImpl, StateT.run_bind,
              StateT.run_get, pure_bind, hcanSend, Bool.not_true, hbeq, Bool.false_or,
              StateT.run_monadLift, monadLift_self, StateT.run_set, hI.hckb,
              Bool.false_eq_true, ↓reduceIte, StateT.run_pure, map_eq_bind_pure_comp,
              Function.comp_apply, bind_assoc, ← hrΓ_P]
            congr 1; funext coins
            have hck_stP : (σ.2.afterSend P (cka.send (rΓ σ P) coins).1
                (cka.send (rΓ σ P) coins).2.1).st P = (cka.send (rΓ σ P) coins).1 := by
              simp [CKA.GameState.afterSend]
            have hck_epP' : (σ.2.afterSend P (cka.send (rΓ σ P) coins).1
                (cka.send (rΓ σ P) coins).2.1).epoch P = σ.1.g.epoch P + 1 := by
              simp [CKA.GameState.afterSend, hck_epP]
            exact Y_startSend_tail_some cka prng fs Δcka tL t P coins _ hck_stP hck_epP'
          · rename_i he
            rw [Y_liftH_bind, Y_sendQuery]
            change σ.1.g.epoch P + 1 ≠ healEpoch tL at he
            have hbeq : (σ.2.epoch P + 1 == healEpoch tL) = false := by
              rw [hck_epP]; exact beq_eq_false_iff_ne.mpr he
            simp only [CKA.sendImpl, StateT.run_bind,
              StateT.run_get, pure_bind, hcanSend, Bool.not_true, hbeq, Bool.false_or,
              Bool.false_eq_true, ↓reduceIte, StateT.run_monadLift, monadLift_self,
              StateT.run_set, StateT.run_pure, map_eq_bind_pure_comp,
              Function.comp_apply, bind_assoc, ← hrΓ_P]
            congr 1; funext coins
            have hck_stP : (σ.2.afterSend P (cka.send (rΓ σ P) coins).1
                (cka.send (rΓ σ P) coins).2.1).st P = (cka.send (rΓ σ P) coins).1 := by
              simp [CKA.GameState.afterSend]
            have hck_epP' : (σ.2.afterSend P (cka.send (rΓ σ P) coins).1
                (cka.send (rΓ σ P) coins).2.1).epoch P = σ.1.g.epoch P + 1 := by
              simp [CKA.GameState.afterSend, hck_epP]
            exact Y_startSend_tail_some cka prng fs Δcka tL t P coins _ hck_stP hck_epP'
        have hrhs : rhs = ($ᵗ CCoins >>= fun coins =>
            let c := cka.send (rΓ σ P) coins
            let γ' : Option Γ :=
              if healEpoch tL + Δcka ≤ σ.1.g.epoch P + 1 then some c.1 else none
            let ck' := σ.2.afterSend P c.1 c.2.1
            pure (afterStartSend cka prng fs Δcka σ s₁ P m isChall coins γ' ck')) := by
          dsimp only [rhs]
          rw [hrhs_base, hstart_none, bind_assoc]
          congr 1
        have hmap : ((fun z => (z.1, projGame z.2)) <$> rhs) = lhs := by
          rw [hrhs, map_eq_bind_pure_comp]
          dsimp only [lhs, samIfNecFst]
          simp only [Function.comp_apply, bind_assoc, pure_bind]
          congr 1; funext coins
          exact congrArg pure (hall_none coins).1
        refine ⟨DEq.of_eq hmap.symm, fun z hz => ?_⟩
        rw [hrhs, mem_support_bind_iff] at hz
        rcases hz with ⟨coins, _, hzx⟩
        rw [support_pure, Set.mem_singleton_iff] at hzx
        rw [hzx]
        exact ⟨(hall_none coins).2.1, (hall_none coins).2.2.1, (hall_none coins).2.2.2⟩
      | some coins =>
        by_cases hbad_cka : σ.1.g.epoch P + 1 + 2 ≤ healEpoch tL
        · left
          have hstart_some :
              Y cka Δcka tL
                (liftH ((hooksCKA cka prng fs Δcka (moP tL t)).startSend
                  s₁ P (σ.1.g.epoch P + 1) (σ.1.g.st P).γ (σ.1.g.st P).root (some coins))) σ =
                (let c := cka.send (rΓ σ P) coins
                 let e := σ.1.g.epoch P + 1
                 let p := prng.up (σ.1.g.st P).root c.2.2
                 let γ' : Option Γ := if healEpoch tL + Δcka ≤ e then some c.1 else none
                 let h' : CKAState T I :=
                   { cache := Function.update σ.1.h.cache e (some (c.2.1, c.2.2)) }
                 pure (some (γ', c.2.1, p.1, fs.initSender p.2),
                   ({ σ.1 with h := h' }, σ.2.afterSend P c.1 c.2.1))) := by
            rw [hγ]
            unfold hooksCKA
            dsimp only
            rw [Y_liftH_bind, Y_sendBadQuery]
            unfold CKA.sendWithAdversaryCoinsImpl
            simp only [StateT.run_bind, StateT.run_get, pure_bind, hcanSend,
              hck_epP, hbad_cka, decide_true, Bool.not_true, Bool.false_or,
              Bool.false_eq_true, ↓reduceIte, StateT.run_set, StateT.run_pure,
              map_pure, ← hrΓ_P]
            have hck_stP : (σ.2.afterSend P (cka.send (rΓ σ P) coins).1
                (cka.send (rΓ σ P) coins).2.1).st P = (cka.send (rΓ σ P) coins).1 := by
              simp [CKA.GameState.afterSend]
            have hck_epP' : (σ.2.afterSend P (cka.send (rΓ σ P) coins).1
                (cka.send (rΓ σ P) coins).2.1).epoch P = σ.1.g.epoch P + 1 := by
              simp [CKA.GameState.afterSend, hck_epP]
            exact Y_startSend_tail_some cka prng fs Δcka tL t P coins _ hck_stP hck_epP'
          have hrhs : rhs =
              (let c := cka.send (rΓ σ P) coins
               let γ' : Option Γ :=
                 if healEpoch tL + Δcka ≤ σ.1.g.epoch P + 1 then some c.1 else none
               let ck' := σ.2.afterSend P c.1 c.2.1
               pure (afterStartSend cka prng fs Δcka σ s₁ P m isChall coins γ' ck')) := by
            dsimp only [rhs]
            rw [hrhs_base, hstart_some, pure_bind]
            rfl
          have hmap : ((fun z => (z.1, projGame z.2)) <$> rhs) = lhs := by
            rw [hrhs, map_pure]
            dsimp only [lhs, samIfNecFst]
            rw [pure_bind, (hall_none coins).1]
          refine ⟨DEq.of_eq hmap.symm, fun z hz => ?_⟩
          rw [hrhs, support_pure, Set.mem_singleton_iff] at hz
          rw [hz]
          exact ⟨(hall_none coins).2.1, (hall_none coins).2.2.1, (hall_none coins).2.2.2⟩
        · right
          have hstart_fail :
              Y cka Δcka tL
                (liftH ((hooksCKA cka prng fs Δcka (moP tL t)).startSend
                  s₁ P (σ.1.g.epoch P + 1) (σ.1.g.st P).γ (σ.1.g.st P).root (some coins))) σ =
                pure (none, σ) := by
            rw [hγ]
            unfold hooksCKA
            dsimp only
            rw [Y_liftH_bind, Y_sendBadQuery]
            unfold CKA.sendWithAdversaryCoinsImpl
            simp only [StateT.run_bind, StateT.run_get, pure_bind, hcanSend,
              hck_epP, hbad_cka, decide_false, Bool.not_false, Bool.or_true, ↓reduceIte,
              StateT.run_pure, map_pure, Y_liftH_pure]
          have hrhs : rhs = pure (none, ({ σ.1 with abort := true }, σ.2)) := by
            dsimp only [rhs]
            rw [hrhs_base, hstart_fail, pure_bind]
          refine ⟨fun z hz => ?_, fun z hz => ?_⟩
          · rw [hrhs, support_pure, Set.mem_singleton_iff] at hz; rw [hz]
          · dsimp only [lhs, samIfNecFst] at hz
            rw [pure_bind, support_pure, Set.mem_singleton_iff] at hz
            rw [hz]
            exact doom_of_sendBad_abort cka Δcka qep tL t hI P l hl hep hs hγ hLD hbad_cka rfl rfl
  · left
    rw [Bool.not_eq_true] at hs
    have hs₁_eq : s₁ = σ.1.g := hs_false hs
    subst s₁
    have hs_st : (σ.1.g.st P).id.sendsIn ((σ.1.g.st P).tcur + 1) = false := by
      rw [hI.hid P, hI.htcur P]; exact hs
    have hs_stL : ((projGame σ).st P).id.sendsIn (((projGame σ).st P).tcur + 1) = false := by
      dsimp only [projGame, projParty, realParty]
      rw [hI.hid P, hI.htcur P]; exact hs
    let out := sendSameEpoch fs (σ.1.g.st P) m
    let outL := sendSameEpoch fs ((projGame σ).st P) m
    let rec_m : SM.Record M (Header T × E) := ⟨⟨P, σ.1.g.epoch P, σ.1.g.idx P + 1⟩, m, out.2⟩
    let rec_mL : SM.Record M (Header T × E) :=
      ⟨⟨P, (projGame σ).epoch P, (projGame σ).idx P + 1⟩, m, outL.2⟩
    let σ' : JSt Γ T Sig SS RS M E I :=
      ({ σ.1 with g := σ.1.g.record (2 + Δcka) P out.1 rec_m isChall }, σ.2)
    have hrhs : rhs = pure (some out.2, σ') := by
      dsimp only [rhs, rhsSendStep]
      rw [vSend_not_sendsIn cka prng fs Δcka tL t σ.1.g P (σ.1.g.st P) m pair r hs_st]
      rw [Y_bind, Y_liftH_pure, pure_bind, Y_bind, Y_modify, pure_bind, Y_pure]
    have hlhs : lhs =
        (samIfNecFst r >>= fun _ =>
          pure (some outL.2, (projGame σ).record (2 + Δcka) P outL.1 rec_mL isChall)) := by
      dsimp only [lhs, lhsSendStepCoins, sL₁]
      congr 1; funext coins
      rw [send_not_sendsIn cka prng fs ((projGame σ).st P) m coins hs_stL]
    obtain ⟨hout_c, hproj, hI', hpc1, hpc2⟩ :=
      inv_record_not_sendsIn cka fs Δcka tL t hI P m isChall hs hch_ep
    change outL.2 = out.2 at hout_c
    change (projGame σ).record (2 + Δcka) P outL.1 rec_mL isChall = projGame σ' at hproj
    rw [hrhs, hlhs, map_pure, hproj, hout_c]
    refine ⟨samIfNecFst_bind_const r _, fun z hz => ?_⟩
    rw [support_pure, Set.mem_singleton_iff] at hz
    rw [hz]
    exact ⟨hI', hpc1, hpc2⟩

omit [DecidableEq I] [SampleableType KR] [SampleableType KC] [SampleableType I] [SampleableType K] in
theorem transmitImpl_eq_lhsSendStepCoins (P : Party) (m : M) (r : Option CCoins)
    (σ : JSt Γ T Sig SS RS M E I)
    {s₁ : SM.GameState (VPt Γ T Sig SS RS) M (Header T × E)}
    (hwin : σ.1.g.win = false)
    (hep : σ.1.g.epMgmt (2 + Δcka) qep P r.isSome = some s₁) :
    ((implPs cka prng fs lam Δcka qep t (.inr (.inl (.inl (.inl (.inl (P, m, r))))))).run (projGame σ)) =
      (samIfNecFst r >>= fun coins =>
        pure (lhsSendStepCoins cka prng fs Δcka (projGame ({ σ.1 with g := s₁ }, σ.2)) P m coins false)) := by
  unfold implPs
  rw [implP_transmit]
  have hwin' : (projGame σ).win = false := hwin
  simp only [SM.transmitImpl, StateT.run_bind, StateT.run_get, pure_bind, hwin',
    Bool.false_eq_true, ↓reduceIte, StateT.run_monadLift, monadLift_self,
    samIfNec_eq_bind r, bind_assoc, epMgmt_projGame (2 + Δcka) qep P r.isSome σ,
    hep, Option.map_some, StateT.run_set, StateT.run_pure]
  rfl

omit [DecidableEq I] [SampleableType KR] [SampleableType KC] [SampleableType K] in
theorem transmitE_eq_rhsSendStep (P : Party) (m : M) (r : Option CCoins)
    (σ : JSt Γ T Sig SS RS M E I)
    {s₁ : SM.GameState (VPt Γ T Sig SS RS) M (Header T × E)}
    (hab : σ.1.abort = false) (hwin : σ.1.g.win = false)
    (hep : σ.1.g.epMgmt (2 + Δcka) qep P r.isSome = some s₁)
    (hLD : (polP tL t).leakDoom σ.1.g s₁ = false) :
    Y cka Δcka tL (implEc cka prng fs Δcka qep tL t (.inr (.inl (.inl (.inl (.inl (P, m, r))))))) σ =
      Y cka Δcka tL (rhsSendStep cka prng fs Δcka tL t s₁ P m none r false) σ := by
  rw [implEc_transmit]
  unfold transmitE rhsSendStep
  simp only [Y_bind, Y_get, pure_bind, hab, hwin, Bool.false_or, Bool.false_eq_true, ↓reduceIte,
    hep, hLD]
  congr 1; funext ⟨x, σ₁⟩; rcases x with _ | ⟨st', c⟩ <;> rfl

omit [DecidableEq I] [SampleableType KR] [SampleableType KC] [SampleableType K] in
theorem step_transmit (q : Party × M × Option CCoins) {σ : JSt Γ T Sig SS RS M E I}
    (hI : Inv cka Δcka tL t σ) :
    (DEq ((implPs cka prng fs lam Δcka qep t (.inr (.inl (.inl (.inl (.inl q)))))).run (projGame σ))
         ((fun r => (r.1, projGame r.2)) <$>
           Y cka Δcka tL (implEc cka prng fs Δcka qep tL t (.inr (.inl (.inl (.inl (.inl q)))))) σ) ∧
       ∀ r ∈ support (Y cka Δcka tL (implEc cka prng fs Δcka qep tL t (.inr (.inl (.inl (.inl (.inl q)))))) σ),
         Inv cka Δcka tL t r.2 ∧ (PostChall t σ.1.g → PostChall t r.2.1.g)) ∨
    ((∀ r ∈ support (Y cka Δcka tL (implEc cka prng fs Δcka qep tL t (.inr (.inl (.inl (.inl (.inl q)))))) σ),
        r.2.1.abort = true) ∧
      ∀ z ∈ support ((implPs cka prng fs lam Δcka qep t (.inr (.inl (.inl (.inl (.inl q)))))).run (projGame σ)),
        DoomFixedB (2 + Δcka) tL t z.2 ∨
          (DoomD2 (2 + Δcka) t z.2 ∧ ¬ PostChall t σ.1.g)) := by
  rcases q with ⟨P, m, r⟩
  have hab : σ.1.abort = false := hI.habort
  have hwin : (projGame σ).win = σ.1.g.win := rfl
  by_cases hwin_b : σ.1.g.win = true
  · left
    unfold implPs
    rw [implP_transmit, implEc_transmit]
    simp only [SM.transmitImpl, transmitE, StateT.run_bind, StateT.run_get, Y_bind, Y_get,
      pure_bind, hab, Bool.false_or, hwin, hwin_b, ↓reduceIte, StateT.run_pure, Y_pure, map_pure]
    exact ⟨DEq.refl _, fun z hz => by
      rw [support_pure, Set.mem_singleton_iff] at hz; rw [hz]; exact ⟨hI, id⟩⟩
  · rw [Bool.not_eq_true] at hwin_b
    cases hep : σ.1.g.epMgmt (2 + Δcka) qep P r.isSome with
    | none =>
      left
      unfold implPs
      rw [implP_transmit, implEc_transmit]
      simp only [SM.transmitImpl, transmitE, StateT.run_bind, StateT.run_get, Y_bind, Y_get,
        pure_bind, hab, Bool.false_or, hwin, hwin_b, Bool.false_eq_true, ↓reduceIte,
        StateT.run_monadLift, monadLift_self]
      rw [samIfNec_eq_bind r]
      simp only [bind_assoc, pure_bind, epMgmt_projGame (2 + Δcka) qep P r.isSome σ,
        hep, Option.map_none, StateT.run_pure, Y_pure, map_pure]
      refine ⟨samIfNecFst_bind_const r (none, projGame σ), fun z hz => ?_⟩
      rw [support_pure, Set.mem_singleton_iff] at hz; rw [hz]; exact ⟨hI, id⟩
    | some s₁ =>
      by_cases hLD : (polP tL t).leakDoom σ.1.g s₁ = true
      · right
        unfold implPs
        rw [implP_transmit, implEc_transmit]
        simp only [SM.transmitImpl, transmitE, StateT.run_bind, StateT.run_get, Y_bind, Y_get,
          pure_bind, hab, Bool.false_or, hwin, hwin_b, Bool.false_eq_true, ↓reduceIte,
          StateT.run_monadLift, monadLift_self]
        rw [samIfNec_eq_bind r]
        simp only [bind_assoc, pure_bind, epMgmt_projGame (2 + Δcka) qep P r.isSome σ,
          hep, Option.map_some, StateT.run_bind, StateT.run_set, StateT.run_pure,
          hLD, ↓reduceIte, Y_bind, Y_abortE, Y_pure]
        refine ⟨fun z hz => ?_, fun z hz => ?_⟩
        · rw [support_pure, Set.mem_singleton_iff] at hz; rw [hz]
        · rw [mem_support_bind_iff] at hz
          rcases hz with ⟨coins, _, hzx⟩
          rw [support_pure, Set.mem_singleton_iff] at hzx
          rw [hzx]
          exact (doom_of_epMgmt_leakDoom cka Δcka qep tL t hI P r.isSome hep hLD rfl rfl).1
      · rw [Bool.not_eq_true] at hLD
        rw [transmitImpl_eq_lhsSendStepCoins cka prng fs lam Δcka qep t P m r σ hwin_b hep,
          transmitE_eq_rhsSendStep cka prng fs Δcka qep tL t P m r σ hab hwin_b hep hLD]
        rcases sendStep_sim cka prng fs Δcka qep tL t hI P m none r false hep hLD
          (by intro h; cases h) with ⟨hdeq, hsupp⟩ | ⟨hab_s, hdoom_s⟩
        · left
          exact ⟨hdeq, fun z hz => ⟨(hsupp z hz).1, (hsupp z hz).2.1⟩⟩
        · right
          exact ⟨hab_s, fun z hz => Or.inl (hdoom_s z hz)⟩

omit [DecidableEq I] [SampleableType KR] [SampleableType KC] [SampleableType I] [SampleableType K] in
theorem challImpl_eq_lhsSendStepCoins (P : Party) (m₀ m₁ : M) (r : Option CCoins)
    (σ : JSt Γ T Sig SS RS M E I)
    {s₁ : SM.GameState (VPt Γ T Sig SS RS) M (Header T × E)}
    (hwin : σ.1.g.win = false)
    (hep : σ.1.g.epMgmt (2 + Δcka) qep P r.isSome = some s₁)
    (hguard : (!s₁.safeCh (2 + Δcka) P || !(SM.Config.priv (Msg := M) t).challAllowedIn (s₁.epoch P)) = false) :
    ((implPs cka prng fs lam Δcka qep t (.inr (.inl (.inl (.inl (.inr (P, m₀, m₁, r))))))).run (projGame σ)) =
      (samIfNecFst r >>= fun coins =>
        pure (lhsSendStepCoins cka prng fs Δcka (projGame ({ σ.1 with g := s₁ }, σ.2)) P
          (((SM.Config.priv (Msg := M) t).challMsg (s₁.epoch P)).getD (if σ.1.g.b then m₁ else m₀))
          coins true)) := by
  unfold implPs
  rw [implP_chall]
  have hwin' : (projGame σ).win = false := hwin
  have hguardL : (!(projGame ({ σ.1 with g := s₁ }, σ.2)).safeCh (2 + Δcka) P ||
      !(SM.Config.priv (Msg := M) t).challAllowedIn ((projGame ({ σ.1 with g := s₁ }, σ.2)).epoch P)) = false :=
    hguard
  simp only [SM.challImpl, StateT.run_bind, StateT.run_get, pure_bind, hwin',
    Bool.false_eq_true, ↓reduceIte, StateT.run_monadLift, monadLift_self,
    samIfNec_eq_bind r, bind_assoc, epMgmt_projGame (2 + Δcka) qep P r.isSome σ,
    hep, Option.map_some, hguardL, StateT.run_set, StateT.run_pure]
  rfl

omit [DecidableEq I] [SampleableType KR] [SampleableType KC] [SampleableType K] in
theorem challE_eq_rhsSendStep (P : Party) (m₀ m₁ : M) (r : Option CCoins)
    (σ : JSt Γ T Sig SS RS M E I)
    {s₁ : SM.GameState (VPt Γ T Sig SS RS) M (Header T × E)}
    (hab : σ.1.abort = false) (hwin : σ.1.g.win = false)
    (hep : σ.1.g.epMgmt (2 + Δcka) qep P r.isSome = some s₁)
    (hguard : (!s₁.safeCh (2 + Δcka) P || !(SM.Config.priv (Msg := M) t).challAllowedIn (s₁.epoch P)) = false)
    (hLD : (polP tL t).leakDoom σ.1.g s₁ = false) :
    Y cka Δcka tL (implEc cka prng fs Δcka qep tL t (.inr (.inl (.inl (.inl (.inr (P, m₀, m₁, r))))))) σ =
      Y cka Δcka tL (rhsSendStep cka prng fs Δcka tL t s₁ P
        (((SM.Config.priv (Msg := M) t).challMsg (s₁.epoch P)).getD (if σ.1.g.b then m₁ else m₀))
        (some (m₀, m₁)) r true) σ := by
  rw [implEc_chall]
  unfold challE rhsSendStep
  simp only [Y_bind, Y_get, pure_bind, hab, hwin, Bool.false_or, Bool.false_eq_true, ↓reduceIte,
    hep, hguard, hLD]
  congr 1; funext ⟨x, σ₁⟩; rcases x with _ | ⟨st', c⟩ <;> rfl

omit [DecidableEq I] [SampleableType KR] [SampleableType KC] [SampleableType K] in
theorem step_chall_ok (P : Party) (m₀ m₁ : M) (r : Option CCoins)
    {σ : JSt Γ T Sig SS RS M E I}
    {s₁ : SM.GameState (VPt Γ T Sig SS RS) M (Header T × E)}
    (hI : Inv cka Δcka tL t σ)
    (hwin_b : σ.1.g.win = false)
    (hep : σ.1.g.epMgmt (2 + Δcka) qep P r.isSome = some s₁)
    (hguard : (!s₁.safeCh (2 + Δcka) P || !(SM.Config.priv (Msg := M) t).challAllowedIn (s₁.epoch P)) = false) :
    (DEq ((implPs cka prng fs lam Δcka qep t (.inr (.inl (.inl (.inl (.inr (P, m₀, m₁, r))))))).run (projGame σ))
         ((fun r => (r.1, projGame r.2)) <$>
           Y cka Δcka tL (implEc cka prng fs Δcka qep tL t (.inr (.inl (.inl (.inl (.inr (P, m₀, m₁, r))))))) σ) ∧
       ∀ z ∈ support (Y cka Δcka tL (implEc cka prng fs Δcka qep tL t (.inr (.inl (.inl (.inl (.inr (P, m₀, m₁, r))))))) σ),
         Inv cka Δcka tL t z.2 ∧ PostChall t z.2.1.g) ∨
    ((∀ z ∈ support (Y cka Δcka tL (implEc cka prng fs Δcka qep tL t (.inr (.inl (.inl (.inl (.inr (P, m₀, m₁, r))))))) σ),
        z.2.1.abort = true) ∧
      ∀ z ∈ support ((implPs cka prng fs lam Δcka qep t (.inr (.inl (.inl (.inl (.inr (P, m₀, m₁, r))))))).run (projGame σ)),
        DoomFixedB (2 + Δcka) tL t z.2) := by
  have hab : σ.1.abort = false := hI.habort
  have hwin : (projGame σ).win = σ.1.g.win := rfl
  have hb : (projGame σ).b = σ.1.g.b := rfl
  have hsafe : s₁.safeCh (2 + Δcka) P = true := by
    revert hguard; cases s₁.safeCh (2 + Δcka) P <;> simp
  have hep_t : s₁.epoch P = t := by
    have hok : (SM.Config.priv (Msg := M) t).challAllowedIn (s₁.epoch P) = true := by
      revert hguard
      cases s₁.safeCh (2 + Δcka) P <;> cases (SM.Config.priv (Msg := M) t).challAllowedIn (s₁.epoch P) <;> decide
    simpa [SM.Config.priv] using hok
  by_cases hLD : (polP tL t).leakDoom σ.1.g s₁ = true
  · right
    unfold implPs
    rw [implP_chall, implEc_chall]
    have hguardL : (!(projGame ({ σ.1 with g := s₁ }, σ.2)).safeCh (2 + Δcka) P ||
        !(SM.Config.priv (Msg := M) t).challAllowedIn ((projGame ({ σ.1 with g := s₁ }, σ.2)).epoch P)) = false :=
      hguard
    simp only [SM.challImpl, challE, StateT.run_bind, StateT.run_get, Y_bind, Y_get,
      pure_bind, hab, Bool.false_or, hwin, hwin_b, Bool.false_eq_true, ↓reduceIte,
      StateT.run_monadLift, monadLift_self]
    rw [samIfNec_eq_bind r]
    simp only [bind_assoc, pure_bind, epMgmt_projGame (2 + Δcka) qep P r.isSome σ,
      hep, Option.map_some, hguard, hguardL, Bool.false_eq_true, ↓reduceIte, hb,
      StateT.run_bind, StateT.run_set, StateT.run_pure,
      hLD, Y_bind, Y_abortE, Y_pure]
    refine ⟨fun z hz => ?_, fun z hz => ?_⟩
    · rw [support_pure, Set.mem_singleton_iff] at hz; rw [hz]
    · rw [mem_support_bind_iff] at hz
      rcases hz with ⟨coins, _, hzx⟩
      rw [support_pure, Set.mem_singleton_iff] at hzx
      rw [hzx]
      exact (doom_of_epMgmt_leakDoom cka Δcka qep tL t hI P r.isSome hep hLD rfl rfl).2 hsafe hep_t
  · rw [Bool.not_eq_true] at hLD
    rw [challImpl_eq_lhsSendStepCoins cka prng fs lam Δcka qep t P m₀ m₁ r σ hwin_b hep hguard,
      challE_eq_rhsSendStep cka prng fs Δcka qep tL t P m₀ m₁ r σ hab hwin_b hep hguard hLD]
    let m := ((SM.Config.priv (Msg := M) t).challMsg (s₁.epoch P)).getD (if σ.1.g.b = true then m₁ else m₀)
    rcases sendStep_sim cka prng fs Δcka qep tL t hI P m (some (m₀, m₁)) r true hep hLD
      (fun _ => hep_t) with ⟨hdeq, hsupp⟩ | ⟨hab_s, hdoom_s⟩
    · left
      exact ⟨hdeq, fun z hz => ⟨(hsupp z hz).1, (hsupp z hz).2.2 rfl⟩⟩
    · right
      exact ⟨hab_s, hdoom_s⟩

omit [DecidableEq I] [SampleableType KR] [SampleableType KC] [SampleableType K] in
theorem step_chall (q : Party × M × M × Option CCoins) {σ : JSt Γ T Sig SS RS M E I}
    (hI : Inv cka Δcka tL t σ) :
    (DEq ((implPs cka prng fs lam Δcka qep t (.inr (.inl (.inl (.inl (.inr q)))))).run (projGame σ))
         ((fun r => (r.1, projGame r.2)) <$>
           Y cka Δcka tL (implEc cka prng fs Δcka qep tL t (.inr (.inl (.inl (.inl (.inr q)))))) σ) ∧
       ∀ r ∈ support (Y cka Δcka tL (implEc cka prng fs Δcka qep tL t (.inr (.inl (.inl (.inl (.inr q)))))) σ),
         Inv cka Δcka tL t r.2 ∧ (PostChall t σ.1.g → PostChall t r.2.1.g)) ∨
    ((∀ r ∈ support (Y cka Δcka tL (implEc cka prng fs Δcka qep tL t (.inr (.inl (.inl (.inl (.inr q)))))) σ),
        r.2.1.abort = true) ∧
      ∀ z ∈ support ((implPs cka prng fs lam Δcka qep t (.inr (.inl (.inl (.inl (.inr q)))))).run (projGame σ)),
        DoomFixedB (2 + Δcka) tL t z.2) := by
  rcases q with ⟨P, m₀, m₁, r⟩
  by_cases hwin_b : σ.1.g.win = true
  · left
    unfold implPs
    rw [implP_chall, implEc_chall]
    have hab : σ.1.abort = false := hI.habort
    have hwin : (projGame σ).win = σ.1.g.win := rfl
    simp only [SM.challImpl, challE, StateT.run_bind, StateT.run_get, Y_bind, Y_get,
      pure_bind, hab, Bool.false_or, hwin, hwin_b, ↓reduceIte, StateT.run_pure, Y_pure, map_pure]
    exact ⟨DEq.refl _, fun z hz => by
      rw [support_pure, Set.mem_singleton_iff] at hz; rw [hz]; exact ⟨hI, id⟩⟩
  · rw [Bool.not_eq_true] at hwin_b
    cases hep : σ.1.g.epMgmt (2 + Δcka) qep P r.isSome with
    | none =>
      left
      unfold implPs
      rw [implP_chall, implEc_chall]
      have hab : σ.1.abort = false := hI.habort
      have hwin : (projGame σ).win = σ.1.g.win := rfl
      simp only [SM.challImpl, challE, StateT.run_bind, StateT.run_get, Y_bind, Y_get,
        pure_bind, hab, Bool.false_or, hwin, hwin_b, Bool.false_eq_true, ↓reduceIte,
        StateT.run_monadLift, monadLift_self]
      rw [samIfNec_eq_bind r]
      simp only [bind_assoc, pure_bind, epMgmt_projGame (2 + Δcka) qep P r.isSome σ,
        hep, Option.map_none, StateT.run_pure, Y_pure, map_pure]
      refine ⟨samIfNecFst_bind_const r (none, projGame σ), fun z hz => ?_⟩
      rw [support_pure, Set.mem_singleton_iff] at hz; rw [hz]; exact ⟨hI, id⟩
    | some s₁ =>
      by_cases hguard : (!s₁.safeCh (2 + Δcka) P || !(SM.Config.priv (Msg := M) t).challAllowedIn (s₁.epoch P)) = true
      · left
        unfold implPs
        rw [implP_chall, implEc_chall]
        have hab : σ.1.abort = false := hI.habort
        have hwin : (projGame σ).win = σ.1.g.win := rfl
        have hguardL : (!(projGame ({ σ.1 with g := s₁ }, σ.2)).safeCh (2 + Δcka) P ||
            !(SM.Config.priv (Msg := M) t).challAllowedIn ((projGame ({ σ.1 with g := s₁ }, σ.2)).epoch P)) = true :=
          hguard
        simp only [SM.challImpl, challE, StateT.run_bind, StateT.run_get, Y_bind, Y_get,
          pure_bind, hab, Bool.false_or, hwin, hwin_b, Bool.false_eq_true, ↓reduceIte,
          StateT.run_monadLift, monadLift_self]
        rw [samIfNec_eq_bind r]
        simp only [bind_assoc, pure_bind, epMgmt_projGame (2 + Δcka) qep P r.isSome σ,
          hep, Option.map_some, hguard, hguardL, ↓reduceIte, StateT.run_pure, Y_pure, map_pure]
        refine ⟨samIfNecFst_bind_const r (none, projGame σ), fun z hz => ?_⟩
        rw [support_pure, Set.mem_singleton_iff] at hz; rw [hz]; exact ⟨hI, id⟩
      · rw [Bool.not_eq_true] at hguard
        rcases step_chall_ok cka prng fs lam Δcka qep tL t P m₀ m₁ r hI hwin_b hep hguard with
          ⟨hdeq, hsupp⟩ | ⟨hab_s, hdoom_s⟩
        · left
          exact ⟨hdeq, fun z hz => ⟨(hsupp z hz).1, fun _ => (hsupp z hz).2⟩⟩
        · right
          exact ⟨hab_s, hdoom_s⟩

/-! ### Adversary simulation and main proof -/

omit [DecidableEq I] [SampleableType KR] [SampleableType KC] [SampleableType K] in
theorem step_postChall
    (q : (unifSpec + SM.spec (RSt Γ T Sig SS RS) M CCoins (Header T × E)).Domain)
    {σ : JSt Γ T Sig SS RS M E I}
    (hI : Inv cka Δcka tL t σ) (hpc : PostChall t σ.1.g) :
    (DEq ((implPs cka prng fs lam Δcka qep t q).run (projGame σ))
         ((fun r => (r.1, projGame r.2)) <$>
           Y cka Δcka tL (implEc cka prng fs Δcka qep tL t q) σ) ∧
       ∀ r ∈ support (Y cka Δcka tL (implEc cka prng fs Δcka qep tL t q) σ),
         Inv cka Δcka tL t r.2 ∧ PostChall t r.2.1.g) ∨
    ((∀ r ∈ support (Y cka Δcka tL (implEc cka prng fs Δcka qep tL t q) σ),
        r.2.1.abort = true) ∧
      ∀ z ∈ support ((implPs cka prng fs lam Δcka qep t q).run (projGame σ)),
        DoomFixedB (2 + Δcka) tL t z.2) := by
  rcases q with n | q
  · left
    obtain ⟨hdeq, hsupp⟩ := step_coin cka prng fs lam Δcka qep tL t n hI
    exact ⟨hdeq, fun r hr => ⟨(hsupp r hr).1, (hsupp r hr).2 hpc⟩⟩
  · rcases q with q | P
    · rcases q with q | q
      · rcases q with q | q
        · rcases q with q | q
          · rcases step_transmit cka prng fs lam Δcka qep tL t q hI with
              ⟨hdeq, hsupp⟩ | ⟨hab, hdoom⟩
            · left; exact ⟨hdeq, fun r hr => ⟨(hsupp r hr).1, (hsupp r hr).2 hpc⟩⟩
            · right
              refine ⟨hab, fun z hz => ?_⟩
              rcases hdoom z hz with hd | ⟨_, hnpc⟩
              · exact hd
              · exact False.elim (hnpc hpc)
          · rcases step_chall cka prng fs lam Δcka qep tL t q hI with
              ⟨hdeq, hsupp⟩ | ⟨hab, hdoom⟩
            · left; exact ⟨hdeq, fun r hr => ⟨(hsupp r hr).1, (hsupp r hr).2 hpc⟩⟩
            · right; exact ⟨hab, hdoom⟩
        · left
          rcases q with ⟨P, c⟩
          obtain ⟨hdeq, hsupp⟩ := step_deliver cka prng fs lam Δcka qep tL t P c hI
          exact ⟨hdeq, fun r hr => ⟨(hsupp r hr).1, (hsupp r hr).2 hpc⟩⟩
      · left
        rcases q with ⟨P, c⟩
        obtain ⟨hdeq, hsupp⟩ := step_inject cka prng fs lam Δcka qep tL t P c hI
        exact ⟨hdeq, fun r hr => ⟨(hsupp r hr).1, (hsupp r hr).2 hpc⟩⟩
    · rcases step_corr cka prng fs lam Δcka qep tL t P hI with
        ⟨hdeq, hsupp⟩ | ⟨hab, hdoom⟩
      · left; exact ⟨hdeq, fun r hr => ⟨(hsupp r hr).1, (hsupp r hr).2 hpc⟩⟩
      · right
        refine ⟨hab, fun z hz => ?_⟩
        rcases hdoom z hz with hd | ⟨_, hnpc⟩
        · exact hd
        · exact False.elim (hnpc hpc)

omit [DecidableEq I] [SampleableType KR] [SampleableType KC] [SampleableType K] in
theorem sim_postChall (b : Bool)
    (oa : SchemeAdversary Γ T Sig SS RS M CCoins E)
    {σ : JSt Γ T Sig SS RS M E I}
    (hI : Inv cka Δcka tL t σ) (hpc : PostChall t σ.1.g) :
    DEq ((simulateQ (implPs cka prng fs lam Δcka qep t) oa).run (projGame σ) >>=
          privEnd (2 + Δcka) tL t b)
        (Y cka Δcka tL (simulateQ (implEc cka prng fs Δcka qep tL t) oa) σ >>=
          ckaEnd Δcka tL t b) := by
  induction oa using OracleComp.inductionOn generalizing σ with
  | pure x =>
    simp only [simulateQ_pure, StateT.run_pure, Y_pure, pure_bind]
    exact DEq.of_eq (ckaEnd_eq_privEnd Δcka tL t b x σ hI.habort).symm
  | query_bind q k ih =>
    simp only [simulateQ_bind, simulateQ_query, OracleQuery.input_query, OracleQuery.cont_query,
      id_map, StateT.run_bind, Y_bind, bind_assoc]
    rcases step_postChall cka prng fs lam Δcka qep tL t q hI hpc with
      ⟨hdeq, hsupp⟩ | ⟨hab, hdoom⟩
    · refine (DEq.bind hdeq (fun _ => DEq.refl _)).trans ?_
      rw [bind_map_left]
      exact DEq.bind_right_supp _ (fun r hr => ih r.1 (hsupp r hr).1 (hsupp r hr).2)
    · have hlhs :
          DEq ((implPs cka prng fs lam Δcka qep t q).run (projGame σ) >>= fun z =>
                (simulateQ (implPs cka prng fs lam Δcka qep t) (k z.1)).run z.2 >>=
                  privEnd (2 + Δcka) tL t b)
              ($ᵗ Bool : ProbComp Bool) :=
        (DEq.bind_right_supp _ (g := fun _ => ($ᵗ Bool : ProbComp Bool)) fun z hz =>
          deq_privEnd_of_doomFixedB cka prng fs lam Δcka qep tL t b (k z.1) (hdoom z hz)).trans
          (DEq.bind_const _ _)
      have hrhs :
          DEq (Y cka Δcka tL (implEc cka prng fs Δcka qep tL t q) σ >>= fun r =>
                Y cka Δcka tL (simulateQ (implEc cka prng fs Δcka qep tL t) (k r.1)) r.2 >>=
                  ckaEnd Δcka tL t b)
              ($ᵗ Bool : ProbComp Bool) :=
        (DEq.bind_right_supp _ (g := fun _ => ($ᵗ Bool : ProbComp Bool)) fun r hr =>
          deq_ckaEnd_of_abort cka prng fs Δcka qep tL t b (k r.1) (hab r hr)).trans
          (DEq.bind_const _ _)
      exact hlhs.trans hrhs.symm

def σWithB (σ : JSt Γ T Sig SS RS M E I) (b : Bool) : JSt Γ T Sig SS RS M E I :=
  ({ σ.1 with g := gsWithB σ.1.g b }, σ.2)

omit [DecidableEq T] [DecidableEq M] [DecidableEq E] [DecidableEq I] [Inhabited E]
  [SampleableType KR] [SampleableType KC] [SampleableType CCoins] [SampleableType I]
  [SampleableType K] in
theorem projGame_σWithB (σ : JSt Γ T Sig SS RS M E I) (b : Bool) :
    projGame (σWithB σ b) = gsWithB (projGame σ) b := rfl

omit [DecidableEq T] [DecidableEq M] [DecidableEq E] [DecidableEq I] [Inhabited E]
  [SampleableType KR] [SampleableType KC] [SampleableType CCoins] [SampleableType I]
  [SampleableType K] in
theorem inv_σWithB {σ : JSt Γ T Sig SS RS M E I} (b : Bool)
    (hI : Inv cka Δcka tL t σ) :
    Inv cka Δcka tL t (σWithB σ b) where
  habort := hI.habort
  hckb := hI.hckb
  hid := hI.hid
  htcur := hI.htcur
  hepoch_le := hI.hepoch_le
  hepoch_sync := hI.hepoch_sync
  hcomp := hI.hcomp
  hchall := hI.hchall
  hleaks_tL := hI.hleaks_tL
  htL_leaks := hI.htL_leaks
  htrans := hI.htrans
  hγ_none := hI.hγ_none
  hγ_some := hI.hγ_some
  hcka_sync := hI.hcka_sync
  hcka_split := hI.hcka_split

omit [DecidableEq T] [DecidableEq M] [DecidableEq E] [DecidableEq I] [Inhabited E]
  [SampleableType KR] [SampleableType KC] [SampleableType K] in
theorem Y_liftH_σWithB {α : Type} (x : CHMc Γ CCoins T I α)
    (σ : JSt Γ T Sig SS RS M E I) (b : Bool) :
    Y cka Δcka tL (liftH x) (σWithB σ b) =
      Prod.map id (fun σ' => σWithB σ' b) <$> Y cka Δcka tL (liftH x) σ := by
  simp only [Y, liftH_run, σWithB, simulateQ_bind, StateT.run_bind, simulateQ_pure,
    StateT.run_pure, map_eq_bind_pure_comp, Function.comp_apply, bind_assoc, pure_bind]
  rfl

omit [DecidableEq M] [DecidableEq E] [DecidableEq I] [Inhabited E]
  [SampleableType KR] [SampleableType KC] [SampleableType K] in
theorem Y_commitE_σWithB
    (s : SM.GameState (VPt Γ T Sig SS RS) M (Header T × E))
    (P : Party) (old new : VPt Γ T Sig SS RS) (pos : SM.Pos)
    (σ : JSt Γ T Sig SS RS M E I) (b : Bool) :
    Y cka Δcka tL
      (commitE (hooksCKA cka prng fs Δcka (moP tL t)) (gsWithB s b) P old new pos)
      (σWithB σ b) =
      Prod.map (Option.map (fun s' => gsWithB s' b)) (fun σ' => σWithB σ' b) <$>
        Y cka Δcka tL
          (commitE (hooksCKA cka prng fs Δcka (moP tL t)) s P old new pos) σ := by
  have hhk : (hooksCKA cka prng fs Δcka (moP tL t)).commit ((gsWithB s b).accept P new pos) P old new =
      (hooksCKA cka prng fs Δcka (moP tL t)).commit (s.accept P new pos) P old new := rfl
  unfold commitE
  dsimp only
  rw [Y_bind, Y_bind, hhk, Y_liftH_σWithB, map_eq_bind_pure_comp, map_eq_bind_pure_comp]
  simp only [Function.comp_apply, bind_assoc, pure_bind]
  congr 1; funext ⟨r₁, σ₁⟩
  dsimp only [Prod.map_apply, id_eq]
  cases r₁ with
  | none =>
    simp only [Y_bind, Y_abortE, pure_bind, Y_pure]
    rfl
  | some new' =>
    simp only [Y_pure, pure_bind]
    rfl

omit [DecidableEq I] [SampleableType KR] [SampleableType KC] [SampleableType K] in
theorem Y_implEc_coin_σWithB (n : ℕ) (σ : JSt Γ T Sig SS RS M E I) (b : Bool) :
    Y cka Δcka tL (implEc cka prng fs Δcka qep tL t (.inl n)) (σWithB σ b) =
      Prod.map id (fun σ' => σWithB σ' b) <$>
        Y cka Δcka tL (implEc cka prng fs Δcka qep tL t (.inl n)) σ := by
  rw [implEc_coin, Y_coinsE, Y_coinsE, Functor.map_map]
  rfl

omit [DecidableEq I] [SampleableType KR] [SampleableType KC] [SampleableType K] in
theorem Y_implEc_transmit_σWithB (q : Party × M × Option CCoins)
    (σ : JSt Γ T Sig SS RS M E I) (b : Bool) :
    Y cka Δcka tL (implEc cka prng fs Δcka qep tL t (.inr (.inl (.inl (.inl (.inl q))))))
      (σWithB σ b) =
      Prod.map id (fun σ' => σWithB σ' b) <$>
        Y cka Δcka tL (implEc cka prng fs Δcka qep tL t (.inr (.inl (.inl (.inl (.inl q)))))) σ := by
  rcases q with ⟨P, m, r⟩
  rw [implEc_transmit]
  unfold transmitE
  simp only [Y_bind, Y_get, pure_bind]
  have hab : (σWithB σ b).1.abort = σ.1.abort := rfl
  have hwin : (σWithB σ b).1.g.win = σ.1.g.win := rfl
  rw [hab, hwin]
  split
  · simp [Y_pure]
  · have hep : (σWithB σ b).1.g.epMgmt (2 + Δcka) qep P r.isSome =
        (σ.1.g.epMgmt (2 + Δcka) qep P r.isSome).map (fun s' => gsWithB s' b) :=
      epMgmt_gsWithB σ.1.g (2 + Δcka) qep P r.isSome b
    rw [hep]
    cases σ.1.g.epMgmt (2 + Δcka) qep P r.isSome with
    | none => simp [Y_pure]
    | some s₁ =>
      simp only [Option.map_some]
      have hLD : (polP tL t).leakDoom (σWithB σ b).1.g (gsWithB s₁ b) =
          (polP tL t).leakDoom σ.1.g s₁ := rfl
      rw [hLD]
      split
      · simp only [Y_bind, Y_abortE, pure_bind, Y_pure, map_pure]; rfl
      · have hvS : vSend (hooksCKA cka prng fs Δcka (moP tL t)) (gsWithB s₁ b) P
            ((gsWithB s₁ b).st P) m none r =
            vSend (hooksCKA cka prng fs Δcka (moP tL t)) s₁ P (s₁.st P) m none r := rfl
        rw [Y_bind, Y_bind, hvS, Y_liftH_σWithB, map_eq_bind_pure_comp, map_eq_bind_pure_comp]
        simp only [Function.comp_apply, bind_assoc, pure_bind]
        congr 1; funext ⟨z₁, σ₁⟩
        dsimp only [Prod.map_apply, id_eq]
        cases z₁ with
        | none => simp only [Y_bind, Y_abortE, pure_bind, Y_pure]; rfl
        | some p =>
          rcases p with ⟨st', c⟩
          simp only [Y_bind, Y_modify, pure_bind, Y_pure]; rfl

omit [DecidableEq I] [SampleableType KR] [SampleableType KC] [SampleableType K] in
theorem Y_implEc_deliver_σWithB (q : Party × (Header T × E))
    (σ : JSt Γ T Sig SS RS M E I) (b : Bool) :
    Y cka Δcka tL (implEc cka prng fs Δcka qep tL t (.inr (.inl (.inl (.inr q)))))
      (σWithB σ b) =
      Prod.map id (fun σ' => σWithB σ' b) <$>
        Y cka Δcka tL (implEc cka prng fs Δcka qep tL t (.inr (.inl (.inl (.inr q))))) σ := by
  rcases q with ⟨P, c⟩
  rw [implEc_deliver]
  unfold deliverE
  simp only [Y_bind, Y_get, pure_bind]
  have hab : (σWithB σ b).1.abort = σ.1.abort := rfl
  have hwin : (σWithB σ b).1.g.win = σ.1.g.win := rfl
  rw [hab, hwin]
  split
  · simp [Y_pure]
  · have htr : (σWithB σ b).1.g.inTransit P.other c = σ.1.g.inTransit P.other c := rfl
    rw [htr]
    cases σ.1.g.inTransit P.other c with
    | none => simp [Y_pure]
    | some rec =>
      dsimp only
      have hvR : vRecv (hooksCKA cka prng fs Δcka (moP tL t)) (σWithB σ b).1.g P
          ((σWithB σ b).1.g.st P) c (some rec) =
          vRecv (hooksCKA cka prng fs Δcka (moP tL t)) σ.1.g P (σ.1.g.st P) c (some rec) := rfl
      rw [Y_bind, Y_bind, hvR, Y_liftH_σWithB, map_eq_bind_pure_comp, map_eq_bind_pure_comp]
      simp only [Function.comp_apply, bind_assoc, pure_bind]
      congr 1; funext ⟨z₁, σ₁⟩
      dsimp only [Prod.map_apply, id_eq]
      cases z₁ with
      | none => simp only [Y_bind, Y_abortE, pure_bind, Y_pure]; rfl
      | some res =>
        cases res with
        | none =>
          have hmust : (SM.Config.priv (Msg := M) t).deliverWin = false := rfl
          simp only [hmust, Bool.false_and, Bool.false_eq_true, ↓reduceIte, Y_pure, pure_bind]
          rfl
        | some quad =>
          rcases quad with ⟨st', t', i', m'⟩
          rw [Y_bind, Y_bind]
          change (Y cka Δcka tL
            (commitE (hooksCKA cka prng fs Δcka (moP tL t)) (gsWithB σ.1.g b) P (σ.1.g.st P) st' rec.pos)
            (σWithB σ₁ b) >>= _) = _
          rw [Y_commitE_σWithB, map_eq_bind_pure_comp]
          simp only [Function.comp_apply, bind_assoc, pure_bind]
          congr 1; funext ⟨w₁, σ₂⟩
          dsimp only [Prod.map_apply]
          cases w₁ with
          | none => simp only [Option.map_none, Y_pure, pure_bind]; rfl
          | some s₁ =>
            have hmust : (SM.Config.priv (Msg := M) t).deliverWin = false := rfl
            have hch : (σWithB σ b).1.g.chall = σ.1.g.chall := rfl
            simp only [Option.map_some, hmust, Bool.false_and, Bool.false_eq_true, ↓reduceIte,
              Y_bind, Y_modify, pure_bind, Y_pure, hch]
            rfl

omit [DecidableEq I] [SampleableType KR] [SampleableType KC] [SampleableType K] in
theorem Y_implEc_inject_σWithB (q : Party × (Header T × E))
    (σ : JSt Γ T Sig SS RS M E I) (b : Bool) :
    Y cka Δcka tL (implEc cka prng fs Δcka qep tL t (.inr (.inl (.inr q)))) (σWithB σ b) =
      Prod.map id (fun σ' => σWithB σ' b) <$>
        Y cka Δcka tL (implEc cka prng fs Δcka qep tL t (.inr (.inl (.inr q)))) σ := by
  rcases q with ⟨P, c⟩
  rw [implEc_inject]
  unfold injectE
  simp only [Y_bind, Y_get, pure_bind]
  have hguard : ((σWithB σ b).1.abort || (σWithB σ b).1.g.win ||
      ((σWithB σ b).1.g.inTransit P.other c).isSome || !(σWithB σ b).1.g.safeInj (2 + Δcka)) =
      (σ.1.abort || σ.1.g.win || (σ.1.g.inTransit P.other c).isSome ||
        !σ.1.g.safeInj (2 + Δcka)) := rfl
  rw [hguard]
  split
  · simp [Y_pure]
  · have hvR : vRecv (hooksCKA cka prng fs Δcka (moP tL t)) (σWithB σ b).1.g P
        ((σWithB σ b).1.g.st P) c none =
        vRecv (hooksCKA cka prng fs Δcka (moP tL t)) σ.1.g P (σ.1.g.st P) c none := rfl
    rw [Y_bind, Y_bind, hvR, Y_liftH_σWithB, map_eq_bind_pure_comp, map_eq_bind_pure_comp]
    simp only [Function.comp_apply, bind_assoc, pure_bind]
    congr 1; funext ⟨z₁, σ₁⟩
    dsimp only [Prod.map_apply, id_eq]
    cases z₁ with
    | none => simp only [Y_bind, Y_abortE, pure_bind, Y_pure]; rfl
    | some res =>
      cases res with
      | none => simp only [Y_pure, pure_bind]; rfl
      | some quad =>
        rcases quad with ⟨st', t', i', m'⟩
        dsimp only
        split
        · simp only [Y_pure, pure_bind]; rfl
        · have htriv : (σWithB σ b).1.g.trivial (2 + Δcka) ⟨P.other, t', i'⟩ =
              σ.1.g.trivial (2 + Δcka) ⟨P.other, t', i'⟩ := rfl
          rw [htriv]
          split
          · rw [Y_bind, Y_bind]
            change (Y cka Δcka tL
              (commitE (hooksCKA cka prng fs Δcka (moP tL t)) (gsWithB σ.1.g b) P (σ.1.g.st P) st' ⟨P.other, t', i'⟩)
              (σWithB σ₁ b) >>= _) = _
            rw [Y_commitE_σWithB, map_eq_bind_pure_comp]
            simp only [Function.comp_apply, bind_assoc, pure_bind]
            congr 1; funext ⟨w₁, σ₂⟩
            dsimp only [Prod.map_apply]
            cases w₁ with
            | none => simp only [Option.map_none, Y_pure, pure_bind]; rfl
            | some s₁ =>
              simp only [Option.map_some, Y_bind, Y_modify, pure_bind, Y_pure]
              rfl
          · have hinj : (SM.Config.priv (Msg := M) t).injectFull t' = false := rfl
            simp only [hinj, Bool.false_eq_true, ↓reduceIte, Y_pure, pure_bind]
            rfl

omit [DecidableEq I] [SampleableType KR] [SampleableType KC] [SampleableType K] in
theorem Y_implEc_corr_σWithB (P : Party) (σ : JSt Γ T Sig SS RS M E I) (b : Bool) :
    Y cka Δcka tL (implEc cka prng fs Δcka qep tL t (.inr (.inr P))) (σWithB σ b) =
      Prod.map id (fun σ' => σWithB σ' b) <$>
        Y cka Δcka tL (implEc cka prng fs Δcka qep tL t (.inr (.inr P))) σ := by
  rw [implEc_corr]
  unfold corrE
  simp only [Y_bind, Y_get, pure_bind]
  have hguard : ((σWithB σ b).1.abort || (σWithB σ b).1.g.win ||
      !(σWithB σ b).1.g.corrAllowed P) =
      (σ.1.abort || σ.1.g.win || !σ.1.g.corrAllowed P) := rfl
  rw [hguard]
  split
  · simp [Y_pure]
  · have hdoom : ((polP tL t).leakDoom (σWithB σ b).1.g ((σWithB σ b).1.g.afterCorr P) ||
        (polP tL t).corrDoom (σWithB σ b).1.g P) =
        ((polP tL t).leakDoom σ.1.g (σ.1.g.afterCorr P) || (polP tL t).corrDoom σ.1.g P) := rfl
    rw [hdoom]
    split
    · simp only [Y_bind, Y_abortE, pure_bind, Y_pure, map_pure]; rfl
    · have hrev : (hooksCKA cka prng fs Δcka (moP tL t)).reveal (σWithB σ b).1.g P
          ((σWithB σ b).1.g.st P) =
          (hooksCKA cka prng fs Δcka (moP tL t)).reveal σ.1.g P (σ.1.g.st P) := rfl
      rw [Y_bind, Y_bind, hrev, Y_liftH_σWithB, map_eq_bind_pure_comp, map_eq_bind_pure_comp]
      simp only [Function.comp_apply, bind_assoc, pure_bind]
      congr 1; funext ⟨z₁, σ₁⟩
      dsimp only [Prod.map_apply, id_eq]
      cases z₁ with
      | none => simp only [Y_bind, Y_abortE, pure_bind, Y_pure]; rfl
      | some st => simp only [Y_bind, Y_modify, pure_bind, Y_pure]; rfl

omit [DecidableEq I] [SampleableType KR] [SampleableType KC] [SampleableType K] in
theorem sim_preChall_step_equiv
    (q : (unifSpec + SM.spec (RSt Γ T Sig SS RS) M CCoins (Header T × E)).Domain)
    (k : (unifSpec + SM.spec (RSt Γ T Sig SS RS) M CCoins (Header T × E)).Range q →
      SchemeAdversary Γ T Sig SS RS M CCoins E)
    {σ : JSt Γ T Sig SS RS M E I}
    (hlhs_eq : ∀ b, (implPs cka prng fs lam Δcka qep t q).run (gsWithB (projGame σ) b) =
      Prod.map id (fun s' => gsWithB s' b) <$>
        (implPs cka prng fs lam Δcka qep t q).run (projGame σ))
    (hrhs_eq : ∀ b, Y cka Δcka tL (implEc cka prng fs Δcka qep tL t q) (σWithB σ b) =
      Prod.map id (fun σ' => σWithB σ' b) <$>
        Y cka Δcka tL (implEc cka prng fs Δcka qep tL t q) σ)
    (hstep :
      (DEq ((implPs cka prng fs lam Δcka qep t q).run (projGame σ))
           ((fun r => (r.1, projGame r.2)) <$>
             Y cka Δcka tL (implEc cka prng fs Δcka qep tL t q) σ) ∧
         ∀ r ∈ support (Y cka Δcka tL (implEc cka prng fs Δcka qep tL t q) σ),
           Inv cka Δcka tL t r.2) ∨
      ((∀ r ∈ support (Y cka Δcka tL (implEc cka prng fs Δcka qep tL t q) σ),
          r.2.1.abort = true) ∧
        ∀ z ∈ support ((implPs cka prng fs lam Δcka qep t q).run (projGame σ)),
          DoomFixedB (2 + Δcka) tL t z.2 ∨
            (DoomD2 (2 + Δcka) t z.2 ∧ ¬ PostChall t σ.1.g)))
    (ih : ∀ a {σ' : JSt Γ T Sig SS RS M E I}, Inv cka Δcka tL t σ' →
      DEq (($ᵗ Bool : ProbComp Bool) >>= fun b =>
            (simulateQ (implPs cka prng fs lam Δcka qep t) (k a)).run (projGame (σWithB σ' b)) >>=
              privEnd (2 + Δcka) tL t b)
          (($ᵗ Bool : ProbComp Bool) >>= fun b =>
            Y cka Δcka tL (simulateQ (implEc cka prng fs Δcka qep tL t) (k a)) (σWithB σ' b) >>=
              ckaEnd Δcka tL t b)) :
    DEq (($ᵗ Bool : ProbComp Bool) >>= fun b =>
          (implPs cka prng fs lam Δcka qep t q).run (projGame (σWithB σ b)) >>= fun z =>
            (simulateQ (implPs cka prng fs lam Δcka qep t) (k z.1)).run z.2 >>=
              privEnd (2 + Δcka) tL t b)
        (($ᵗ Bool : ProbComp Bool) >>= fun b =>
          Y cka Δcka tL (implEc cka prng fs Δcka qep tL t q) (σWithB σ b) >>= fun r =>
            Y cka Δcka tL (simulateQ (implEc cka prng fs Δcka qep tL t) (k r.1)) r.2 >>=
              ckaEnd Δcka tL t b) := by
  have hL_rw : ∀ b,
      ((implPs cka prng fs lam Δcka qep t q).run (projGame (σWithB σ b)) >>= fun z =>
        (simulateQ (implPs cka prng fs lam Δcka qep t) (k z.1)).run z.2 >>=
          privEnd (2 + Δcka) tL t b) =
      ((implPs cka prng fs lam Δcka qep t q).run (projGame σ) >>= fun z =>
        (simulateQ (implPs cka prng fs lam Δcka qep t) (k z.1)).run (gsWithB z.2 b) >>=
          privEnd (2 + Δcka) tL t b) := fun b => by
    rw [projGame_σWithB, hlhs_eq b, bind_map_left]
    rfl
  have hR_rw : ∀ b,
      (Y cka Δcka tL (implEc cka prng fs Δcka qep tL t q) (σWithB σ b) >>= fun r =>
        Y cka Δcka tL (simulateQ (implEc cka prng fs Δcka qep tL t) (k r.1)) r.2 >>=
          ckaEnd Δcka tL t b) =
      (Y cka Δcka tL (implEc cka prng fs Δcka qep tL t q) σ >>= fun r =>
        Y cka Δcka tL (simulateQ (implEc cka prng fs Δcka qep tL t) (k r.1)) (σWithB r.2 b) >>=
          ckaEnd Δcka tL t b) := fun b => by
    rw [hrhs_eq b, bind_map_left]
    rfl
  simp_rw [hL_rw, hR_rw]
  refine (DEq.swap ($ᵗ Bool : ProbComp Bool)
    ((implPs cka prng fs lam Δcka qep t q).run (projGame σ)) _).trans ?_
  refine DEq.trans ?_ (DEq.swap ($ᵗ Bool : ProbComp Bool)
    (Y cka Δcka tL (implEc cka prng fs Δcka qep tL t q) σ) _).symm
  rcases hstep with ⟨hdeq, hsupp⟩ | ⟨hab, hdoom⟩
  · refine (DEq.bind hdeq (fun _ => DEq.refl _)).trans ?_
    rw [bind_map_left]
    exact DEq.bind_right_supp _ (fun r hr => ih r.1 (hsupp r hr))
  · have hlhs :
        DEq ((implPs cka prng fs lam Δcka qep t q).run (projGame σ) >>= fun z =>
              ($ᵗ Bool : ProbComp Bool) >>= fun b =>
                (simulateQ (implPs cka prng fs lam Δcka qep t) (k z.1)).run (gsWithB z.2 b) >>=
                  privEnd (2 + Δcka) tL t b)
            ($ᵗ Bool : ProbComp Bool) := by
      refine (DEq.bind_right_supp _ (g := fun _ => ($ᵗ Bool : ProbComp Bool)) fun z hz => ?_).trans
        (DEq.bind_const _ _)
      rcases hdoom z hz with hdf | ⟨hd2, _⟩
      · exact (DEq.bind_right ($ᵗ Bool) (g := fun _ => ($ᵗ Bool : ProbComp Bool)) fun b =>
          deq_privEnd_of_doomFixedB cka prng fs lam Δcka qep tL t b (k z.1)
            (gs := gsWithB z.2 b) hdf).trans
          (DEq.bind_const _ _)
      · exact deq_privEnd_of_doomD2 (scheme cka prng fs lam) (2 + Δcka) qep tL t (k z.1) hd2
    have hrhs :
        DEq (Y cka Δcka tL (implEc cka prng fs Δcka qep tL t q) σ >>= fun r =>
              ($ᵗ Bool : ProbComp Bool) >>= fun b =>
                Y cka Δcka tL (simulateQ (implEc cka prng fs Δcka qep tL t) (k r.1))
                  (σWithB r.2 b) >>= ckaEnd Δcka tL t b)
            ($ᵗ Bool : ProbComp Bool) := by
      refine (DEq.bind_right_supp _ (g := fun _ => ($ᵗ Bool : ProbComp Bool)) fun r hr => ?_).trans
        (DEq.bind_const _ _)
      exact (DEq.bind_right ($ᵗ Bool) (g := fun _ => ($ᵗ Bool : ProbComp Bool)) fun b =>
        deq_ckaEnd_of_abort cka prng fs Δcka qep tL t b (k r.1)
          (σ := σWithB r.2 b) (hab r hr)).trans
        (DEq.bind_const _ _)
    exact hlhs.trans hrhs.symm

omit [DecidableEq I] [SampleableType KR] [SampleableType KC] [SampleableType K] in
theorem sim_preChall
    (oa : SchemeAdversary Γ T Sig SS RS M CCoins E)
    {σ : JSt Γ T Sig SS RS M E I}
    (hI : Inv cka Δcka tL t σ) :
    DEq (($ᵗ Bool : ProbComp Bool) >>= fun b =>
          (simulateQ (implPs cka prng fs lam Δcka qep t) oa).run (projGame (σWithB σ b)) >>=
            privEnd (2 + Δcka) tL t b)
        (($ᵗ Bool : ProbComp Bool) >>= fun b =>
          Y cka Δcka tL (simulateQ (implEc cka prng fs Δcka qep tL t) oa) (σWithB σ b) >>=
            ckaEnd Δcka tL t b) := by
  induction oa using OracleComp.inductionOn generalizing σ with
  | pure x =>
    refine DEq.bind_right ($ᵗ Bool) fun b => ?_
    simp only [simulateQ_pure, StateT.run_pure, Y_pure, pure_bind]
    exact DEq.of_eq (ckaEnd_eq_privEnd Δcka tL t b x (σWithB σ b) hI.habort).symm
  | query_bind q k ih =>
    simp only [simulateQ_bind, simulateQ_query, OracleQuery.input_query, OracleQuery.cont_query,
      id_map, StateT.run_bind, Y_bind, bind_assoc]
    rcases q with n | q
    · obtain ⟨hdeq, hsupp⟩ := step_coin cka prng fs lam Δcka qep tL t n hI
      exact sim_preChall_step_equiv cka prng fs lam Δcka qep tL t (.inl n) k
        (implP_coin_gsWithB (scheme cka prng fs lam) (2 + Δcka) qep t n (projGame σ))
        (Y_implEc_coin_σWithB cka prng fs Δcka qep tL t n σ)
        (Or.inl ⟨hdeq, fun r hr => (hsupp r hr).1⟩)
        (fun a _ hI' => ih a hI')
    · rcases q with q | P
      · rcases q with q | q
        · rcases q with q | q
          · rcases q with q | q
            · exact sim_preChall_step_equiv cka prng fs lam Δcka qep tL t
                (.inr (.inl (.inl (.inl (.inl q))))) k
                (implP_transmit_gsWithB (scheme cka prng fs lam) (2 + Δcka) qep t q (projGame σ))
                (Y_implEc_transmit_σWithB cka prng fs Δcka qep tL t q σ)
                (by
                  rcases step_transmit cka prng fs lam Δcka qep tL t q hI with
                    ⟨hdeq, hsupp⟩ | ⟨hab, hdoom⟩
                  · exact Or.inl ⟨hdeq, fun r hr => (hsupp r hr).1⟩
                  · exact Or.inr ⟨hab, hdoom⟩)
                (fun a _ hI' => ih a hI')
            · rcases q with ⟨P, m₀, m₁, r⟩
              by_cases hwin_b : σ.1.g.win = true
              · have hL_win : ∀ b,
                    ((implPs cka prng fs lam Δcka qep t
                      (.inr (.inl (.inl (.inl (.inr (P, m₀, m₁, r))))))).run
                      (projGame (σWithB σ b)) >>= fun z =>
                      (simulateQ (implPs cka prng fs lam Δcka qep t) (k z.1)).run z.2 >>=
                        privEnd (2 + Δcka) tL t b) =
                    (simulateQ (implPs cka prng fs lam Δcka qep t) (k none)).run
                      (projGame (σWithB σ b)) >>= privEnd (2 + Δcka) tL t b := fun b => by
                  unfold implPs
                  rw [implP_chall]
                  have hwin' : (projGame (σWithB σ b)).win = true := hwin_b
                  simp only [SM.challImpl, StateT.run_bind, StateT.run_get, pure_bind, hwin',
                    ↓reduceIte, StateT.run_pure]
                have hR_win : ∀ b,
                    (Y cka Δcka tL (implEc cka prng fs Δcka qep tL t
                      (.inr (.inl (.inl (.inl (.inr (P, m₀, m₁, r))))))) (σWithB σ b) >>= fun z =>
                      Y cka Δcka tL (simulateQ (implEc cka prng fs Δcka qep tL t) (k z.1)) z.2 >>=
                        ckaEnd Δcka tL t b) =
                    Y cka Δcka tL (simulateQ (implEc cka prng fs Δcka qep tL t) (k none))
                      (σWithB σ b) >>= ckaEnd Δcka tL t b := fun b => by
                  rw [implEc_chall]
                  have hab' : (σWithB σ b).1.abort = false := hI.habort
                  have hwin' : (σWithB σ b).1.g.win = true := hwin_b
                  simp only [challE, Y_bind, Y_get, pure_bind, hab', hwin', Bool.or_true,
                    ↓reduceIte, Y_pure]
                simp_rw [hL_win, hR_win]
                exact ih none hI
              · rw [Bool.not_eq_true] at hwin_b
                cases hep : σ.1.g.epMgmt (2 + Δcka) qep P r.isSome with
                | none =>
                  have hL_none : ∀ b,
                      DEq ((implPs cka prng fs lam Δcka qep t
                            (.inr (.inl (.inl (.inl (.inr (P, m₀, m₁, r))))))).run
                            (projGame (σWithB σ b)) >>= fun z =>
                            (simulateQ (implPs cka prng fs lam Δcka qep t) (k z.1)).run z.2 >>=
                              privEnd (2 + Δcka) tL t b)
                          ((simulateQ (implPs cka prng fs lam Δcka qep t) (k none)).run
                            (projGame (σWithB σ b)) >>= privEnd (2 + Δcka) tL t b) := fun b => by
                    unfold implPs
                    rw [implP_chall]
                    have hwin' : (projGame (σWithB σ b)).win = false := hwin_b
                    have hep' : (σWithB σ b).1.g.epMgmt (2 + Δcka) qep P r.isSome = none := by
                      dsimp only [σWithB]; rw [epMgmt_gsWithB σ.1.g (2 + Δcka) qep P r.isSome b, hep]; rfl
                    simp only [SM.challImpl, StateT.run_bind, StateT.run_get, pure_bind, hwin',
                      Bool.false_eq_true, ↓reduceIte, StateT.run_monadLift, monadLift_self]
                    rw [samIfNec_eq_bind r]
                    simp only [bind_assoc, pure_bind, epMgmt_projGame (2 + Δcka) qep P r.isSome (σWithB σ b),
                      hep', Option.map_none, StateT.run_pure]
                    exact DEq.bind_const _ _
                  have hR_none : ∀ b,
                      (Y cka Δcka tL (implEc cka prng fs Δcka qep tL t
                        (.inr (.inl (.inl (.inl (.inr (P, m₀, m₁, r))))))) (σWithB σ b) >>= fun z =>
                        Y cka Δcka tL (simulateQ (implEc cka prng fs Δcka qep tL t) (k z.1)) z.2 >>=
                          ckaEnd Δcka tL t b) =
                      Y cka Δcka tL (simulateQ (implEc cka prng fs Δcka qep tL t) (k none))
                        (σWithB σ b) >>= ckaEnd Δcka tL t b := fun b => by
                    rw [implEc_chall]
                    have hab' : (σWithB σ b).1.abort = false := hI.habort
                    have hwin' : (σWithB σ b).1.g.win = false := hwin_b
                    have hep' : (σWithB σ b).1.g.epMgmt (2 + Δcka) qep P r.isSome = none := by
                      dsimp only [σWithB]; rw [epMgmt_gsWithB σ.1.g (2 + Δcka) qep P r.isSome b, hep]; rfl
                    simp only [challE, Y_bind, Y_get, pure_bind, hab', hwin', Bool.false_or,
                      Bool.false_eq_true, ↓reduceIte, hep', Y_pure]
                  simp_rw [hR_none]
                  exact (DEq.bind_right ($ᵗ Bool) hL_none).trans (ih none hI)
                | some s₁ =>
                  by_cases hguard : (!s₁.safeCh (2 + Δcka) P ||
                      !(SM.Config.priv (Msg := M) t).challAllowedIn (s₁.epoch P)) = true
                  · have hL_guard : ∀ b,
                        DEq ((implPs cka prng fs lam Δcka qep t
                              (.inr (.inl (.inl (.inl (.inr (P, m₀, m₁, r))))))).run
                              (projGame (σWithB σ b)) >>= fun z =>
                              (simulateQ (implPs cka prng fs lam Δcka qep t) (k z.1)).run z.2 >>=
                                privEnd (2 + Δcka) tL t b)
                            ((simulateQ (implPs cka prng fs lam Δcka qep t) (k none)).run
                              (projGame (σWithB σ b)) >>= privEnd (2 + Δcka) tL t b) := fun b => by
                      unfold implPs
                      rw [implP_chall]
                      have hwin' : (projGame (σWithB σ b)).win = false := hwin_b
                      have hep' : (σWithB σ b).1.g.epMgmt (2 + Δcka) qep P r.isSome =
                          some (gsWithB s₁ b) := by
                        dsimp only [σWithB]; rw [epMgmt_gsWithB σ.1.g (2 + Δcka) qep P r.isSome b, hep]; rfl
                      have hguardL : (!(projGame ({ (σWithB σ b).1 with g := gsWithB s₁ b }, (σWithB σ b).2)).safeCh (2 + Δcka) P ||
                          !(SM.Config.priv (Msg := M) t).challAllowedIn
                            ((projGame ({ (σWithB σ b).1 with g := gsWithB s₁ b }, (σWithB σ b).2)).epoch P)) = true :=
                        hguard
                      simp only [SM.challImpl, StateT.run_bind, StateT.run_get, pure_bind, hwin',
                        Bool.false_eq_true, ↓reduceIte, StateT.run_monadLift, monadLift_self]
                      rw [samIfNec_eq_bind r]
                      simp only [bind_assoc, pure_bind, epMgmt_projGame (2 + Δcka) qep P r.isSome (σWithB σ b),
                        hep', Option.map_some, hguardL, ↓reduceIte, StateT.run_pure]
                      exact DEq.bind_const _ _
                    have hR_guard : ∀ b,
                        (Y cka Δcka tL (implEc cka prng fs Δcka qep tL t
                          (.inr (.inl (.inl (.inl (.inr (P, m₀, m₁, r))))))) (σWithB σ b) >>= fun z =>
                          Y cka Δcka tL (simulateQ (implEc cka prng fs Δcka qep tL t) (k z.1)) z.2 >>=
                            ckaEnd Δcka tL t b) =
                        Y cka Δcka tL (simulateQ (implEc cka prng fs Δcka qep tL t) (k none))
                          (σWithB σ b) >>= ckaEnd Δcka tL t b := fun b => by
                      rw [implEc_chall]
                      have hab' : (σWithB σ b).1.abort = false := hI.habort
                      have hwin' : (σWithB σ b).1.g.win = false := hwin_b
                      have hep' : (σWithB σ b).1.g.epMgmt (2 + Δcka) qep P r.isSome =
                          some (gsWithB s₁ b) := by
                        dsimp only [σWithB]; rw [epMgmt_gsWithB σ.1.g (2 + Δcka) qep P r.isSome b, hep]; rfl
                      have hguardR : (!(gsWithB s₁ b).safeCh (2 + Δcka) P ||
                          !(SM.Config.priv (Msg := M) t).challAllowedIn ((gsWithB s₁ b).epoch P)) = true :=
                        hguard
                      simp only [challE, Y_bind, Y_get, pure_bind, hab', hwin', Bool.false_or,
                        Bool.false_eq_true, ↓reduceIte, hep', hguardR, Y_pure]
                    simp_rw [hR_guard]
                    exact (DEq.bind_right ($ᵗ Bool) hL_guard).trans (ih none hI)
                  · rw [Bool.not_eq_true] at hguard
                    refine DEq.bind_right ($ᵗ Bool) fun b => ?_
                    have hep_b : (σWithB σ b).1.g.epMgmt (2 + Δcka) qep P r.isSome =
                        some (gsWithB s₁ b) := by
                      dsimp only [σWithB]; rw [epMgmt_gsWithB σ.1.g (2 + Δcka) qep P r.isSome b, hep]; rfl
                    rcases step_chall_ok cka prng fs lam Δcka qep tL t P m₀ m₁ r
                      (inv_σWithB cka Δcka tL t b hI) hwin_b hep_b hguard with
                      ⟨hdeq, hsupp⟩ | ⟨hab_s, hdoom_s⟩
                    · refine (DEq.bind hdeq (fun _ => DEq.refl _)).trans ?_
                      rw [bind_map_left]
                      exact DEq.bind_right_supp _ (fun z hz =>
                        sim_postChall cka prng fs lam Δcka qep tL t b (k z.1)
                          (hsupp z hz).1 (hsupp z hz).2)
                    · have hlhs :
                          DEq ((implPs cka prng fs lam Δcka qep t
                                (.inr (.inl (.inl (.inl (.inr (P, m₀, m₁, r))))))).run
                                (projGame (σWithB σ b)) >>= fun z =>
                                (simulateQ (implPs cka prng fs lam Δcka qep t) (k z.1)).run z.2 >>=
                                  privEnd (2 + Δcka) tL t b)
                              ($ᵗ Bool : ProbComp Bool) :=
                        (DEq.bind_right_supp _ (g := fun _ => ($ᵗ Bool : ProbComp Bool)) fun z hz =>
                          deq_privEnd_of_doomFixedB cka prng fs lam Δcka qep tL t b (k z.1)
                            (hdoom_s z hz)).trans (DEq.bind_const _ _)
                      have hrhs :
                          DEq (Y cka Δcka tL (implEc cka prng fs Δcka qep tL t
                                (.inr (.inl (.inl (.inl (.inr (P, m₀, m₁, r))))))) (σWithB σ b) >>= fun z =>
                                Y cka Δcka tL (simulateQ (implEc cka prng fs Δcka qep tL t) (k z.1)) z.2 >>=
                                  ckaEnd Δcka tL t b)
                              ($ᵗ Bool : ProbComp Bool) :=
                        (DEq.bind_right_supp _ (g := fun _ => ($ᵗ Bool : ProbComp Bool)) fun z hz =>
                          deq_ckaEnd_of_abort cka prng fs Δcka qep tL t b (k z.1)
                            (hab_s z hz)).trans (DEq.bind_const _ _)
                      exact hlhs.trans hrhs.symm
          · rcases q with ⟨P, c⟩
            obtain ⟨hdeq, hsupp⟩ := step_deliver cka prng fs lam Δcka qep tL t P c hI
            exact sim_preChall_step_equiv cka prng fs lam Δcka qep tL t
              (.inr (.inl (.inl (.inr (P, c))))) k
              (implP_deliver_gsWithB (scheme cka prng fs lam) (2 + Δcka) qep t (P, c) (projGame σ))
              (Y_implEc_deliver_σWithB cka prng fs Δcka qep tL t (P, c) σ)
              (Or.inl ⟨hdeq, fun r hr => (hsupp r hr).1⟩)
              (fun a _ hI' => ih a hI')
        · rcases q with ⟨P, c⟩
          obtain ⟨hdeq, hsupp⟩ := step_inject cka prng fs lam Δcka qep tL t P c hI
          exact sim_preChall_step_equiv cka prng fs lam Δcka qep tL t
            (.inr (.inl (.inr (P, c)))) k
            (implP_inject_gsWithB (scheme cka prng fs lam) (2 + Δcka) qep t (P, c) (projGame σ))
            (Y_implEc_inject_σWithB cka prng fs Δcka qep tL t (P, c) σ)
            (Or.inl ⟨hdeq, fun r hr => (hsupp r hr).1⟩)
            (fun a _ hI' => ih a hI')
      · exact sim_preChall_step_equiv cka prng fs lam Δcka qep tL t
          (.inr (.inr P)) k
          (implP_corr_gsWithB (scheme cka prng fs lam) (2 + Δcka) qep t P (projGame σ))
          (Y_implEc_corr_σWithB cka prng fs Δcka qep tL t P σ)
          (by
            rcases step_corr cka prng fs lam Δcka qep tL t P hI with
              ⟨hdeq, hsupp⟩ | ⟨hab, hdoom⟩
            · exact Or.inl ⟨hdeq, fun r hr => (hsupp r hr).1⟩
            · exact Or.inr ⟨hab, hdoom⟩)
          (fun a _ hI' => ih a hI')

omit [DecidableEq T] [DecidableEq M] [DecidableEq E] [DecidableEq I] [Inhabited E]
  [SampleableType CCoins] [SampleableType I] [SampleableType K] in
theorem uniformSample_prod_kr_kc :
    ($ᵗ (KR × KC) : ProbComp (KR × KC)) =
      (($ᵗ KR : ProbComp KR) >>= fun kr => ($ᵗ KC : ProbComp KC) >>= fun kc => pure (kr, kc)) := by
  change (Prod.mk <$> ($ᵗ KR) <*> ($ᵗ KC)) = _
  simp [seq_eq_bind_map, map_eq_bind_pure_comp]

omit [DecidableEq I] [SampleableType I] [SampleableType K] in
theorem privGame_eq (A : SchemeAdversary Γ T Sig SS RS M CCoins E) :
    SM.privGame (scheme cka prng fs lam) (2 + Δcka) qep tL t A =
      (($ᵗ Bool : ProbComp Bool) >>= fun b =>
        ($ᵗ KR : ProbComp KR) >>= fun kr =>
        ($ᵗ KC : ProbComp KC) >>= fun kc =>
          (simulateQ (implPs cka prng fs lam Δcka qep t) A).run
            (SM.initState (scheme cka prng fs lam) (kr, kc) b) >>=
            privEnd (2 + Δcka) tL t b) := by
  unfold SM.privGame SM.run privEnd implPs implP
  rw [uniformSample_prod_kr_kc]
  simp only [bind_assoc, pure_bind]

omit [DecidableEq T] [DecidableEq M] [DecidableEq E] [DecidableEq I] [Inhabited E]
  [SampleableType KR] [SampleableType KC] [SampleableType K] in
theorem simulateQ_implC_sampleT {α : Type} [SampleableType α]
    (cs : CKA.GameState Γ T) :
    (simulateQ (implC cka Δcka (healEpoch tL)) (sampleT α)).run cs =
      (·, cs) <$> ($ᵗ α : ProbComp α) := by
  simp [sampleT, implC, QueryImpl.simulateQ_add_liftM_left, simulateQ_liftTarget]

omit [DecidableEq T] [DecidableEq M] [DecidableEq E] [DecidableEq I] [Inhabited E]
  [SampleableType KR] [SampleableType KC] [SampleableType K] in
theorem simulateQ_implC_privOut (b b' : Bool)
    (es : ESt Γ T Sig SS RS M E I) (cs : CKA.GameState Γ T) :
    Prod.fst <$> (simulateQ (implC cka Δcka (healEpoch tL))
        (privOut (2 + Δcka) (polP tL t) b b' es)).run cs =
      ckaEnd Δcka tL t b (b', (es, cs)) := by
  unfold privOut ckaEnd polP
  dsimp only
  split <;> simp [implC, QueryImpl.simulateQ_add_liftM_left, simulateQ_liftTarget]

omit [DecidableEq T] [DecidableEq M] [DecidableEq E] [DecidableEq I] [Inhabited E]
  [SampleableType KR] [SampleableType KC] [SampleableType CCoins] [SampleableType I]
  [SampleableType K] in
theorem stateT_run_lift {α : Type} (x : CKA.AdversaryComp Γ CCoins T I α) (h : CKAState T I) :
    (StateT.lift x : CHMc Γ CCoins T I α).run h = (x >>= fun a => pure (a, h)) := rfl

omit [DecidableEq T] [DecidableEq M] [DecidableEq E] [DecidableEq I] [Inhabited E]
  [SampleableType K] in
theorem simulateQ_initCKA_none (h : CKAState T I) (cs : CKA.GameState Γ T) :
    (simulateQ (implC cka Δcka (healEpoch none))
      ((initCKA cka prng fs lam (moP none t)).run h)).run cs =
      (($ᵗ KR : ProbComp KR) >>= fun kr =>
        ($ᵗ KC : ProbComp KC) >>= fun kc =>
          let out := prng.up (prng.init kr) lam
          pure ((some (mkParties (some (cka.initA kc)) (some (cka.initB kc)) out.1
                  (fs.initSender out.2) (fs.initReceiver out.2)), h), cs)) := by
  unfold initCKA moP
  dsimp only
  simp only [stateT_run_lift, StateT.run_bind, StateT.run_pure, simulateQ_bind,
    simulateQ_implC_sampleT, bind_map_left, bind_assoc, simulateQ_pure,
    pure_bind]

omit [DecidableEq T] [DecidableEq M] [DecidableEq E] [DecidableEq I] [Inhabited E]
  [SampleableType K] in
theorem simulateQ_initCKA_some (l : ℕ) (h : CKAState T I) (cs : CKA.GameState Γ T) :
    (simulateQ (implC cka Δcka (healEpoch (some l)))
      ((initCKA cka prng fs lam (moP (some l) t)).run h)).run cs =
      (($ᵗ KR : ProbComp KR) >>= fun kr =>
        let out := prng.up (prng.init kr) lam
        pure ((some (mkParties none none out.1
                (fs.initSender out.2) (fs.initReceiver out.2)), h), cs)) := by
  unfold initCKA moP
  dsimp only
  simp only [stateT_run_lift, StateT.run_bind, StateT.run_pure, simulateQ_bind,
    simulateQ_implC_sampleT, bind_map_left, bind_assoc, simulateQ_pure,
    pure_bind]

omit [DecidableEq I] [SampleableType K] in
theorem branch_redCKAPriv_eq (A : SchemeAdversary Γ T Sig SS RS M CCoins E) :
    CKA.branch cka Δcka (healEpoch tL) false
        (redCKAPriv cka prng fs lam Δcka qep tL t A) =
      (($ᵗ KC : ProbComp KC) >>= fun kc =>
        ($ᵗ Bool : ProbComp Bool) >>= fun b =>
        (simulateQ (implC cka Δcka (healEpoch tL))
          ((initCKA cka prng fs lam (moP tL t)).run {})).run
          (CKA.initState cka kc false) >>= fun x =>
        match x.1.1 with
        | none => ($ᵗ Bool : ProbComp Bool)
        | some (vA, vB) =>
          let g : SM.GameState (VPt Γ T Sig SS RS) M (Header T × E) :=
            { st := fun P => match P with | .A => vA | .B => vB, b }
          Y cka Δcka tL (simulateQ (implEc cka prng fs Δcka qep tL t) A)
            ({ g, h := x.1.2 }, x.2) >>= ckaEnd Δcka tL t b) := by
  refine bind_congr fun kc => ?_
  unfold redCKAPriv runCKA
  change Prod.fst <$> (simulateQ (implC cka Δcka (healEpoch tL)) _).run
    (CKA.initState cka kc false) = _
  simp only [engRun, simulateQ_bind, StateT.run_bind, bind_assoc,
    simulateQ_implC_sampleT, bind_map_left, map_bind]
  refine bind_congr fun b => bind_congr fun ⟨⟨vs, h⟩, os₁⟩ => ?_
  cases vs with
  | none =>
    simp [simulateQ_implC_sampleT]
  | some vAvB =>
    rcases vAvB with ⟨vA, vB⟩
    simp only [Y, simulateQ_bind, StateT.run_bind, bind_assoc, simulateQ_pure,
      StateT.run_pure, pure_bind, bind_map_left]
    change (do
      let x ← (simulateQ (implC cka Δcka (healEpoch tL))
        ((simulateQ (implEc cka prng fs Δcka qep tL t) A).run
          { g := { st := fun P => match P with | .A => vA | .B => vB, b := b }, h := h })).run os₁
      Prod.fst <$> (simulateQ (implC cka Δcka (healEpoch tL))
        (privOut (2 + Δcka) (polP tL t) b x.1.1 x.1.2)).run x.2) = _
    simp only [simulateQ_implC_privOut]

omit [DecidableEq I] [SampleableType K] in
theorem privGame_dEq_redCKAPriv (hc : cka.Correct)
    (A : SchemeAdversary Γ T Sig SS RS M CCoins E) :
    DEq (SM.privGame (scheme cka prng fs lam) (2 + Δcka) qep tL t A)
        (CKA.branch cka Δcka (healEpoch tL) false
          (redCKAPriv cka prng fs lam Δcka qep tL t A)) := by
  rw [privGame_eq, branch_redCKAPriv_eq]
  have hLHS :
      DEq (($ᵗ Bool : ProbComp Bool) >>= fun b =>
            ($ᵗ KR : ProbComp KR) >>= fun kr =>
            ($ᵗ KC : ProbComp KC) >>= fun kc =>
              (simulateQ (implPs cka prng fs lam Δcka qep t) A).run
                (SM.initState (scheme cka prng fs lam) (kr, kc) b) >>=
                privEnd (2 + Δcka) tL t b)
          (($ᵗ KR : ProbComp KR) >>= fun kr =>
             ($ᵗ KC : ProbComp KC) >>= fun kc =>
             ($ᵗ Bool : ProbComp Bool) >>= fun b =>
               (simulateQ (implPs cka prng fs lam Δcka qep t) A).run
                 (SM.initState (scheme cka prng fs lam) (kr, kc) b) >>=
                 privEnd (2 + Δcka) tL t b) := by
    refine (DEq.swap ($ᵗ Bool) ($ᵗ KR) _).trans (DEq.bind_right ($ᵗ KR) fun kr => ?_)
    exact DEq.swap ($ᵗ Bool) ($ᵗ KC) _
  refine hLHS.trans ?_
  cases tL with
  | none =>
    have hRHS_none :
        ∀ kc_game : KC,
          DEq (($ᵗ KR : ProbComp KR) >>= fun kr =>
                ($ᵗ KC : ProbComp KC) >>= fun kc =>
                ($ᵗ Bool : ProbComp Bool) >>= fun b =>
                  (simulateQ (implPs cka prng fs lam Δcka qep t) A).run
                    (SM.initState (scheme cka prng fs lam) (kr, kc) b) >>=
                    privEnd (2 + Δcka) none t b)
              (($ᵗ Bool : ProbComp Bool) >>= fun b =>
                (simulateQ (implC cka Δcka (healEpoch none))
                  ((initCKA cka prng fs lam (moP none t)).run {})).run
                  (CKA.initState cka kc_game false) >>= fun x =>
                match x.1.1 with
                | none => ($ᵗ Bool : ProbComp Bool)
                | some (vA, vB) =>
                  let g : SM.GameState (VPt Γ T Sig SS RS) M (Header T × E) :=
                    { st := fun P => match P with | .A => vA | .B => vB, b }
                  Y cka Δcka none (simulateQ (implEc cka prng fs Δcka qep none t) A)
                    ({ g, h := x.1.2 }, x.2) >>= ckaEnd Δcka none t b) := by
      intro kc_game
      simp only [simulateQ_initCKA_none, bind_assoc, pure_bind]
      refine DEq.trans ?_ (DEq.swap ($ᵗ Bool) ($ᵗ KR) _).symm
      refine DEq.bind_right ($ᵗ KR) fun kr => ?_
      refine DEq.trans ?_ (DEq.swap ($ᵗ Bool) ($ᵗ KC) _).symm
      refine DEq.bind_right ($ᵗ KC) fun kc => ?_
      have hinit := init_inv_none cka prng fs lam Δcka t hc kr kc kc_game false
      have hproj : ∀ b, SM.initState (scheme cka prng fs lam) (kr, kc) b =
          projGame (σWithB (initJStNone cka prng fs lam kr kc kc_game false) b) := fun b =>
        (init_inv_none cka prng fs lam Δcka t hc kr kc kc_game b).1.symm
      simp_rw [hproj]
      exact sim_preChall cka prng fs lam Δcka qep none t A hinit.2
    exact (DEq.bind_const ($ᵗ KC) _).symm.trans (DEq.bind_right ($ᵗ KC) hRHS_none)
  | some l =>
    simp only [simulateQ_initCKA_some, bind_assoc, pure_bind]
    refine DEq.trans ?_ (DEq.swap ($ᵗ KC) ($ᵗ Bool) _).symm
    refine DEq.trans ?_ (DEq.bind_right ($ᵗ Bool) fun b => (DEq.swap ($ᵗ KC) ($ᵗ KR) _).symm)
    refine DEq.trans ?_ (DEq.swap ($ᵗ Bool) ($ᵗ KR) _).symm
    refine DEq.bind_right ($ᵗ KR) fun kr => ?_
    refine DEq.trans ?_ (DEq.swap ($ᵗ Bool) ($ᵗ KC) _).symm
    refine DEq.bind_right ($ᵗ KC) fun kc => ?_
    have hinit := init_inv_some cka prng fs lam Δcka t hc l kr kc false
    have hproj : ∀ b, SM.initState (scheme cka prng fs lam) (kr, kc) b =
         projGame (σWithB (initJStSome cka prng fs lam kr kc false) b) := fun b =>
       (init_inv_some cka prng fs lam Δcka t hc l kr kc b).1.symm
    simp_rw [hproj]
    exact sim_preChall cka prng fs lam Δcka qep (some l) t A hinit.2

end RedCKASim

variable {KC Γ CCoins T I : Type} {KR Sig K : Type} {SS RS M E : Type}
  [DecidableEq T] [DecidableEq M] [DecidableEq E] [DecidableEq I] [Inhabited E]
  [SampleableType KR] [SampleableType KC] [SampleableType CCoins] [SampleableType I]
  [SampleableType K]

variable (cka : CKAScheme KC Γ CCoins T I) (prng : PRFPRNG KR Sig I K)
  (fs : FSAEADScheme K SS RS (Header T) M E) (lam : I) (Δcka qep : ℕ)

omit [DecidableEq I] [SampleableType K] in
/-- Lemma 13: `privGame` bias is bounded by the CKA real-world bias of `redCKAPriv`. -/
theorem lemma13_proof (hc : cka.Correct) (tL : Option ℕ) (t : ℕ)
    (A : SchemeAdversary Γ T Sig SS RS M CCoins E) :
    𝒟[privGame (scheme cka prng fs lam) (2 + Δcka) qep tL t A].boolBias ≤
      𝒟[CKA.branch cka Δcka (healEpoch tL) false
        (redCKAPriv cka prng fs lam Δcka qep tL t A)].boolBias := by
  rw [(privGame_dEq_redCKAPriv cka prng fs lam Δcka qep tL t hc A).evalDist_eq]

end CryptoGames.SM.Construction.PrivL13
