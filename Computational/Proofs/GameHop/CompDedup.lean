/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Specifications.CryptoGames.SM.LibsignalGame
public import Computational.Proofs.CryptoGames.SM.GameProofDefs
public import Computational.Proofs.GameHop.StateSim
public import Mathlib.Data.List.Dedup

/-!
# Deduplicated Compromised-Position Table Equivalence and Length Bounds

Shows that deduplicating `SM.GameState.comp` on insertion (`afterCorrDedup`) preserves oracle
behavior via canonical state projection (`canonComp`) and bounds `comp.length` within a query
budget.
-/

set_option autoImplicit false

@[expose] public section

namespace Computational.Proofs.GameHop.CompDedup

open OracleSpec OracleComp
open CryptoGames (Party)
open CryptoGames.SM (Pos Record ConfigR GameState)
open Computational.Proofs.GameHop.StateSim (isQueryBoundP_false map_run_simulateQ_eq_of_inv_dis)

section DedupPrepend

/-- Right-to-left prepend of `xs` onto `acc`, skipping entries already in the accumulator. -/
def dedupPrepend {α : Type} [BEq α] (xs acc : List α) : List α :=
  xs.foldr (fun x a => if a.contains x then a else x :: a) acc

theorem dedupPrepend_cons {α : Type} [BEq α] (x : α) (xs acc : List α) :
    dedupPrepend (x :: xs) acc =
      if (dedupPrepend xs acc).contains x then dedupPrepend xs acc
      else x :: dedupPrepend xs acc := rfl

/-- Multiplicity dominance `∀ y, l.count y ≤ U.count y`. -/
def CountLe {α : Type} [BEq α] (l U : List α) : Prop :=
  ∀ y : α, l.count y ≤ U.count y

section DecidableEq

variable {α : Type} [DecidableEq α]

theorem mem_dedupPrepend_iff (xs acc : List α) (y : α) :
    y ∈ dedupPrepend xs acc ↔ y ∈ xs ∨ y ∈ acc := by
  induction xs with
  | nil => simp [dedupPrepend]
  | cons x xs ih =>
    rw [dedupPrepend_cons]
    split_ifs with hc
    · have hx : x ∈ dedupPrepend xs acc := List.contains_iff_mem.mp hc
      constructor
      · intro hy
        rcases ih.mp hy with hxs | hacc
        · exact Or.inl (List.mem_cons_of_mem x hxs)
        · exact Or.inr hacc
      · rintro (h | hacc)
        · rcases List.mem_cons.mp h with rfl | hxs
          · exact hx
          · exact ih.mpr (Or.inl hxs)
        · exact ih.mpr (Or.inr hacc)
    · simp only [List.mem_cons, ih]
      tauto

theorem countLe_nil (U : List α) : CountLe ([] : List α) U :=
  fun _ => Nat.zero_le _

theorem countLe_cons_cons (x : α) {l U : List α} (h : CountLe l U) :
    CountLe (x :: l) (x :: U) := by
  intro y
  by_cases hyx : y = x
  · subst hyx
    have := h y
    simp only [List.count_cons_self]
    omega
  · simpa [List.count_cons_of_ne (Ne.symm hyx)] using h y

theorem countLe_cons_right (x : α) {l U : List α} (h : CountLe l U) :
    CountLe l (x :: U) := by
  intro y
  by_cases hyx : y = x
  · subst hyx
    have := h y
    simp only [List.count_cons_self]
    omega
  · simpa [List.count_cons_of_ne (Ne.symm hyx)] using h y

theorem count_filter_le (p : α → Bool) (y : α) (l : List α) :
    (l.filter p).count y ≤ l.count y := by
  induction l with
  | nil => simp
  | cons x xs ih =>
    rw [List.filter_cons]
    split_ifs
    · by_cases hyx : y = x
      · subst hyx; simp only [List.count_cons_self]; omega
      · simpa [List.count_cons_of_ne (Ne.symm hyx)] using ih
    · by_cases hyx : y = x
      · subst hyx; simp only [List.count_cons_self]; omega
      · simpa [List.count_cons_of_ne (Ne.symm hyx)] using ih

theorem countLe_filter_left (p : α → Bool) {l U : List α} (h : CountLe l U) :
    CountLe (l.filter p) U :=
  fun y => le_trans (count_filter_le p y l) (h y)

theorem countLe_length_le {l U : List α} (h : CountLe l U) : l.length ≤ U.length := by
  induction l generalizing U with
  | nil => exact Nat.zero_le _
  | cons x xs ih =>
    have hxpos : 0 < U.count x := by
      have hx := h x
      rw [List.count_cons_self] at hx
      omega
    have hxmem : x ∈ U := List.count_pos_iff.mp hxpos
    have hlenpos : 0 < U.length := List.length_pos_of_mem hxmem
    have hEraseLen : (U.erase x).length = U.length - 1 := List.length_erase_of_mem hxmem
    have hxs : CountLe xs (U.erase x) := by
      intro y
      by_cases hyx : y = x
      · subst hyx
        have hx := h y
        rw [List.count_cons_self] at hx
        rw [List.count_erase]
        simp only [beq_self_eq_true, ↓reduceIte]
        omega
      · rw [List.count_erase_of_ne hyx]
        have hy := h y
        rwa [List.count_cons_of_ne (Ne.symm hyx)] at hy
    have ih' := ih hxs
    simp only [List.length_cons]
    omega

theorem countLe_dedupPrepend {xs acc U : List α}
    (hacc : CountLe acc U) (hxs : ∀ x ∈ xs, x ∈ U) :
    CountLe (dedupPrepend xs acc) U := by
  induction xs with
  | nil => exact hacc
  | cons x xs ih =>
    have ih' := ih fun z hz => hxs z (List.mem_cons_of_mem x hz)
    intro y
    rw [dedupPrepend_cons]
    split_ifs with hc
    · exact ih' y
    · have hnx : x ∉ dedupPrepend xs acc := fun hm => hc (List.contains_iff_mem.mpr hm)
      by_cases hyx : y = x
      · subst hyx
        rw [List.count_cons_self, List.count_eq_zero.mpr hnx, zero_add]
        exact List.count_pos_iff.mpr (hxs y List.mem_cons_self)
      · rw [List.count_cons_of_ne (Ne.symm hyx)]
        exact ih' y

/-- Shows the bounded encoded `foldr` equals `(dedupPrepend ((rs.filter keep).map posOf) acc).map encP`
when lengths stay within `K`. -/
theorem foldr_dedup_map_eq {ρ τ π : Type}
    (K : ℕ) (rs : List ρ) (acc U : List α)
    (keep : ρ → Bool) (posOf : ρ → α)
    (encR : ρ → τ) (encP : α → π)
    (keepE : τ → Bool) (posE : τ → π) (eqP : π → π → Bool)
    (hKeep : ∀ r, keepE (encR r) = keep r)
    (hPos : ∀ r, posE (encR r) = encP (posOf r))
    (hEq : ∀ p₁ p₂, eqP (encP p₁) (encP p₂) = (p₁ == p₂))
    (hrsK : rs.length ≤ K) (hUK : U.length ≤ K)
    (haccU : CountLe acc U)
    (hrsU : ∀ r ∈ rs, keep r = true → posOf r ∈ U) :
    ((rs.map encR).take K).foldr
      (fun rE aE =>
        if keepE rE && !((aE.take K).any (fun pE => eqP pE (posE rE)))
        then posE rE :: aE
        else aE)
      (acc.map encP)
    = (dedupPrepend ((rs.filter keep).map posOf) acc).map encP := by
  have htake : (rs.map encR).take K = rs.map encR :=
    List.take_of_length_le (by simpa using hrsK)
  rw [htake]
  clear hrsK htake
  induction rs with
  | nil => simp [dedupPrepend]
  | cons r rs ih =>
    have hrsU' : ∀ r' ∈ rs, keep r' = true → posOf r' ∈ U :=
      fun r' hr' hk => hrsU r' (List.mem_cons_of_mem r hr') hk
    simp only [List.map_cons, List.foldr_cons]
    rw [ih hrsU']
    set tail := dedupPrepend ((rs.filter keep).map posOf) acc
    have htailU : CountLe tail U := by
      refine countLe_dedupPrepend haccU ?_
      intro x hx
      rcases List.mem_map.mp hx with ⟨r', hr', rfl⟩
      rcases List.mem_filter.mp hr' with ⟨hr'mem, hr'k⟩
      exact hrsU' r' hr'mem hr'k
    have htailLen : (tail.map encP).length ≤ K := by
      rw [List.length_map]
      exact le_trans (countLe_length_le htailU) hUK
    rw [List.take_of_length_le htailLen, hKeep, hPos, List.any_map]
    have hany :
        (tail.any ((fun pE => eqP pE (encP (posOf r))) ∘ encP)) = tail.contains (posOf r) := by
      rw [Bool.eq_iff_iff]
      simp [Function.comp_def, hEq]
    rw [hany]
    cases hk : keep r
    · rw [List.filter_cons_of_neg (by simp [hk])]
      simp [tail]
    · rw [List.filter_cons_of_pos hk, List.map_cons, dedupPrepend_cons]
      simp only [Bool.true_and]
      cases hc : tail.contains (posOf r) <;> simp [tail]

/-! ### `List.dedup` identities -/

theorem dedup_dedup (xs : List α) : xs.dedup.dedup = xs.dedup :=
  xs.nodup_dedup.dedup

theorem dedup_cons_eq_ite_contains (x : α) (xs : List α) :
    (x :: xs).dedup = if xs.dedup.contains x then xs.dedup else x :: xs.dedup := by
  by_cases hx : x ∈ xs
  · simp [List.dedup_cons_of_mem hx, hx]
  · simp [List.dedup_cons_of_notMem hx, hx]

theorem dedup_cons_dedup (x : α) (xs : List α) :
    (x :: xs.dedup).dedup = (x :: xs).dedup := by
  by_cases hx : x ∈ xs
  · rw [List.dedup_cons_of_mem (List.mem_dedup.mpr hx), List.dedup_cons_of_mem hx, dedup_dedup]
  · rw [List.dedup_cons_of_notMem (by simpa [List.mem_dedup] using hx),
        List.dedup_cons_of_notMem hx, dedup_dedup]

theorem dedup_append_eq_dedupPrepend (xs ys : List α) :
    (xs ++ ys).dedup = dedupPrepend xs ys.dedup := by
  induction xs with
  | nil => simp [dedupPrepend]
  | cons x xs ih =>
    rw [List.cons_append, dedup_cons_eq_ite_contains, ih, dedupPrepend_cons]

theorem dedup_dedupPrepend_eq_dedup_append (xs ys : List α) :
    (dedupPrepend xs ys).dedup = (xs ++ ys).dedup := by
  induction xs with
  | nil => simp [dedupPrepend]
  | cons x xs ih =>
    rw [dedupPrepend_cons, List.cons_append]
    split_ifs with hc
    · have hx : x ∈ xs ++ ys := by
        have hm : x ∈ dedupPrepend xs ys := List.contains_iff_mem.mp hc
        rcases (mem_dedupPrepend_iff xs ys x).mp hm with hxs | hys
        · exact List.mem_append_left ys hxs
        · exact List.mem_append_right xs hys
      rw [List.dedup_cons_of_mem hx, ih]
    · have hnx : x ∉ dedupPrepend xs ys := fun hm => hc (List.contains_iff_mem.mpr hm)
      have hnx' : x ∉ xs ++ ys := by
        intro hm
        apply hnx
        rw [mem_dedupPrepend_iff]
        exact List.mem_append.mp hm
      rw [List.dedup_cons_of_notMem hnx, List.dedup_cons_of_notMem hnx', ih]

theorem dedup_filter_eq (p : α → Bool) (xs : List α) :
    (xs.filter p).dedup = xs.dedup.filter p := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    cases hpx : p x
    · rw [List.filter_cons_of_neg (by simp [hpx]), ih]
      by_cases hx : x ∈ xs
      · rw [List.dedup_cons_of_mem hx]
      · rw [List.dedup_cons_of_notMem hx, List.filter_cons_of_neg (by simp [hpx])]
    · rw [List.filter_cons_of_pos hpx]
      by_cases hx : x ∈ xs
      · have hxf : x ∈ xs.filter p := List.mem_filter.mpr ⟨hx, hpx⟩
        rw [List.dedup_cons_of_mem hxf, List.dedup_cons_of_mem hx, ih]
      · have hnxf : x ∉ xs.filter p := fun h => hx (List.mem_filter.mp h).1
        rw [List.dedup_cons_of_notMem hnxf, List.dedup_cons_of_notMem hx,
            List.filter_cons_of_pos hpx, ih]

theorem countLe_dedup_of_subset {xs U : List α} (h : ∀ x ∈ xs, x ∈ U) :
    CountLe xs.dedup U := by
  intro y
  by_cases hy : y ∈ xs.dedup
  · have h1 : xs.dedup.count y ≤ 1 := List.nodup_iff_count_le_one.mp xs.nodup_dedup y
    have h2 : 0 < U.count y := List.count_pos_iff.mpr (h y (List.mem_dedup.mp hy))
    omega
  · simp [List.count_eq_zero.mpr hy]

theorem length_dedup_le_of_subset {xs U : List α} (h : ∀ x ∈ xs, x ∈ U) :
    xs.dedup.length ≤ U.length :=
  countLe_length_le (countLe_dedup_of_subset h)

end DecidableEq

end DedupPrepend

section GameStateDedup

/-- `SM.GameState.afterCorr` with `comp` deduplicated on insertion via `dedupPrepend`. -/
def afterCorrDedup {St Msg C : Type} (s : GameState St Msg C) (P : Party) :
    GameState St Msg C :=
  let s₁ : GameState St Msg C :=
    { s with
      comp := dedupPrepend
        ((s.trans.filter (fun r : Record Msg C => r.pos.sender == P.other)).map
          (fun r : Record Msg C => r.pos))
        s.comp }
  { s₁.leak (max (s.epoch .A) (s.epoch .B)) with corrs := (P, s.epoch P) :: s.corrs }

/-- Canonical `GameState` projection deduplicating `comp`. -/
def canonComp {St Msg C : Type} (s : GameState St Msg C) : GameState St Msg C :=
  { s with comp := s.comp.dedup }

theorem canonComp_idem {St Msg C : Type} (s : GameState St Msg C) :
    canonComp (canonComp s) = canonComp s := by
  simp [canonComp]

theorem canonComp_comp_contains {St Msg C : Type} (s : GameState St Msg C) (pos : Pos) :
    (canonComp s).comp.contains pos = s.comp.contains pos := by
  rw [Bool.eq_iff_iff]
  simp [canonComp]

theorem canonComp_safeCh {St Msg C : Type} (s : GameState St Msg C) (Δ : ℕ) (P : Party) :
    (canonComp s).safeCh Δ P = s.safeCh Δ P := rfl

theorem canonComp_safeInj {St Msg C : Type} (s : GameState St Msg C) (Δ : ℕ) :
    (canonComp s).safeInj Δ = s.safeInj Δ := rfl

theorem canonComp_inWindow {St Msg C : Type} (s : GameState St Msg C) (P : Party) :
    CryptoGames.SM.inWindow (canonComp s) P = CryptoGames.SM.inWindow s P := rfl

theorem canonComp_inTransit {St Msg C : Type} [DecidableEq C]
    (s : GameState St Msg C) (Q : Party) (c : C) :
    (canonComp s).inTransit Q c = s.inTransit Q c := rfl

theorem canonComp_trivial {St Msg C : Type}
    (s : GameState St Msg C) (Δ : ℕ) (pos : Pos) :
    (canonComp s).trivial Δ pos = s.trivial Δ pos := by
  rw [Bool.eq_iff_iff]
  simp [GameState.trivial, canonComp]

theorem canonComp_corrAllowed {St Msg C : Type}
    (s : GameState St Msg C) (P : Party) :
    (canonComp s).corrAllowed P = s.corrAllowed P := by
  rw [Bool.eq_iff_iff]
  simp [GameState.corrAllowed, canonComp]

theorem canonComp_epMgmt {St Msg C : Type}
    (s : GameState St Msg C) (Δ qep : ℕ) (P : Party) (bad : Bool) :
    Option.map canonComp (s.epMgmt Δ qep P bad) = (canonComp s).epMgmt Δ qep P bad := by
  cases s
  unfold GameState.epMgmt canonComp GameState.safeCh GameState.leak
  dsimp only []
  split_ifs <;> rfl

theorem canonComp_record {St Msg C : Type}
    (s : GameState St Msg C) (Δ : ℕ) (P : Party) (st' : St) (r : Record Msg C) (isChall : Bool) :
    canonComp (s.record Δ P st' r isChall) =
      canonComp ((canonComp s).record Δ P st' r isChall) := by
  have hs : (canonComp s).safeCh Δ P = s.safeCh Δ P := rfl
  unfold GameState.record
  rw [hs]
  unfold canonComp
  dsimp only []
  congr 1
  split_ifs
  · exact (dedup_dedup s.comp).symm
  · exact (dedup_cons_dedup r.pos s.comp).symm

theorem canonComp_delete {St Msg C : Type} (s : GameState St Msg C) (pos : Pos) :
    canonComp (s.delete pos) = (canonComp s).delete pos := by
  simp [GameState.delete, canonComp, dedup_filter_eq]

theorem canonComp_setWin {St Msg C : Type} (s : GameState St Msg C) (w : Bool) :
    canonComp { s with win := w } = { canonComp s with win := w } :=
  rfl

theorem canonComp_accept {St Msg C : Type}
    (s : GameState St Msg C) (P : Party) (st' : St) (pos : Pos) :
    canonComp (s.accept P st' pos) = (canonComp s).accept P st' pos := by
  unfold GameState.accept
  rw [← canonComp_delete]
  rfl

theorem canonComp_afterCorr {St Msg C : Type} (s : GameState St Msg C) (P : Party) :
    canonComp (s.afterCorr P) = canonComp ((canonComp s).afterCorr P) := by
  unfold GameState.afterCorr GameState.leak canonComp
  dsimp only []
  congr 1
  rw [dedup_append_eq_dedupPrepend, dedup_append_eq_dedupPrepend, dedup_dedup]

theorem canonComp_afterCorrDedup {St Msg C : Type} (s : GameState St Msg C) (P : Party) :
    canonComp (afterCorrDedup s P) = canonComp ((canonComp s).afterCorr P) := by
  unfold afterCorrDedup GameState.afterCorr GameState.leak canonComp
  dsimp only []
  congr 1
  rw [dedup_dedupPrepend_eq_dedup_append, dedup_append_eq_dedupPrepend,
      dedup_append_eq_dedupPrepend, dedup_dedup]

/-! ### Idempotent-projection `simulateQ` bisimulation -/

/-- State-projection equivalence for two `QueryImpl`s sharing an idempotent projection `proj`
under invariant `inv`. -/
theorem map_run_simulateQ_eq_of_idem_proj_inv {ι κ : Type} {G : OracleSpec.{0, 0} κ}
    {T : OracleSpec.{0, 0} ι} {α σ : Type}
    (impl₁ impl₂ : QueryImpl G (StateT σ (OracleComp T)))
    (inv : σ → Prop) (proj : σ → σ)
    (hinv₁ : ∀ t s, inv s → ∀ z ∈ support ((impl₁ t).run s), inv z.2)
    (hinv₂ : ∀ t s, inv s → ∀ z ∈ support ((impl₂ t).run s), inv z.2)
    (hstep₁ : ∀ t s, inv s →
      Prod.map id proj <$> (impl₁ t).run s = Prod.map id proj <$> (impl₂ t).run (proj s))
    (hstep₂ : ∀ t s, inv s →
      Prod.map id proj <$> (impl₂ t).run s = Prod.map id proj <$> (impl₂ t).run (proj s))
    (oa : OracleComp G α) {s₁ s₂ : σ}
    (hs₁ : inv s₁) (hs₂ : inv s₂) (hproj : proj s₁ = proj s₂) :
    Prod.map id proj <$> (simulateQ impl₁ oa).run s₁ =
      Prod.map id proj <$> (simulateQ impl₂ oa).run s₂ := by
  let impl₀ : QueryImpl G (StateT σ (OracleComp T)) :=
    fun t => StateT.mk fun s => Prod.map id proj <$> (impl₂ t).run s
  have h₁ := map_run_simulateQ_eq_of_inv_dis impl₁ impl₀ inv proj (fun _ => False)
    (fun t s _ hs z hz => hinv₁ t s hs z hz)
    (fun t s _ hs => hstep₁ t s hs)
    oa (isQueryBoundP_false oa 0) s₁ hs₁
  have h₂ := map_run_simulateQ_eq_of_inv_dis impl₂ impl₀ inv proj (fun _ => False)
    (fun t s _ hs z hz => hinv₂ t s hs z hz)
    (fun t s _ hs => hstep₂ t s hs)
    oa (isQueryBoundP_false oa 0) s₂ hs₂
  rw [h₁, hproj, ← h₂]

theorem map_run_simulateQ_eq_of_idem_proj {ι κ : Type} {G : OracleSpec.{0, 0} κ}
    {T : OracleSpec.{0, 0} ι} {α σ : Type}
    (impl₁ impl₂ : QueryImpl G (StateT σ (OracleComp T)))
    (proj : σ → σ)
    (hstep₁ : ∀ t s,
      Prod.map id proj <$> (impl₁ t).run s = Prod.map id proj <$> (impl₂ t).run (proj s))
    (hstep₂ : ∀ t s,
      Prod.map id proj <$> (impl₂ t).run s = Prod.map id proj <$> (impl₂ t).run (proj s))
    (oa : OracleComp G α) {s₁ s₂ : σ} (hproj : proj s₁ = proj s₂) :
    Prod.map id proj <$> (simulateQ impl₁ oa).run s₁ =
      Prod.map id proj <$> (simulateQ impl₂ oa).run s₂ :=
  map_run_simulateQ_eq_of_idem_proj_inv impl₁ impl₂ (fun _ => True) proj
    (fun _ _ _ _ _ => trivial) (fun _ _ _ _ _ => trivial)
    (fun t s _ => hstep₁ t s) (fun t s _ => hstep₂ t s)
    oa trivial trivial hproj

theorem run'_simulateQ_eq_of_idem_proj {ι κ : Type} {G : OracleSpec.{0, 0} κ}
    {T : OracleSpec.{0, 0} ι} {α σ : Type}
    (impl₁ impl₂ : QueryImpl G (StateT σ (OracleComp T)))
    (proj : σ → σ)
    (hstep₁ : ∀ t s,
      Prod.map id proj <$> (impl₁ t).run s = Prod.map id proj <$> (impl₂ t).run (proj s))
    (hstep₂ : ∀ t s,
      Prod.map id proj <$> (impl₂ t).run s = Prod.map id proj <$> (impl₂ t).run (proj s))
    (oa : OracleComp G α) {s₁ s₂ : σ} (hproj : proj s₁ = proj s₂) :
    (simulateQ impl₁ oa).run' s₁ = (simulateQ impl₂ oa).run' s₂ := by
  have hmap := congrArg (fun p => Prod.fst <$> p)
    (map_run_simulateQ_eq_of_idem_proj impl₁ impl₂ proj hstep₁ hstep₂ oa hproj)
  simpa [StateT.run'_eq, Functor.map_map, Function.comp_def] using hmap

/-- `SM.corrR` using `afterCorrDedup` instead of `GameState.afterCorr`. -/
def corrRDedup {St Msg C : Type} (cfg : ConfigR St Msg C) :
    QueryImpl (Party →ₒ Option St) (StateT (GameState St Msg C) ProbComp) := fun P => do
  let s ← get
  if s.win || !(s.corrAllowed P) || (cfg.r1 && CryptoGames.SM.inWindow s P) || !(cfg.corrOK s P) then
    return none
  set (afterCorrDedup s P)
  return some (s.st P)

/-! ### Position freshness invariant -/

/-- Invariant that every recorded or compromised position is lexicographically bounded by its
sender's current `(epoch, idx)`. -/
def PosFreshInv {St Msg C : Type} (s : GameState St Msg C) : Prop :=
  (∀ r ∈ s.trans,
    r.pos.epoch < s.epoch r.pos.sender ∨
      (r.pos.epoch = s.epoch r.pos.sender ∧ r.pos.idx ≤ s.idx r.pos.sender)) ∧
  (∀ p ∈ s.comp,
    p.epoch < s.epoch p.sender ∨
      (p.epoch = s.epoch p.sender ∧ p.idx ≤ s.idx p.sender))

theorem PosFreshInv.init {St Msg C : Type} (st₀ : Party → St) (b : Bool) :
    PosFreshInv ({ st := st₀, b := b } : GameState St Msg C) :=
  And.intro (fun _ h => nomatch h) (fun _ h => nomatch h)

theorem PosFreshInv.notMem_comp_next {St Msg C : Type}
    {s : GameState St Msg C} (h : PosFreshInv s) (P : Party) :
    (⟨P, s.epoch P, s.idx P + 1⟩ : Pos) ∉ s.comp := by
  intro hMem
  have hBound := h.2 _ hMem
  dsimp only at hBound
  omega

theorem PosFreshInv.setWin {St Msg C : Type}
    {s : GameState St Msg C} (h : PosFreshInv s) (w : Bool) :
    PosFreshInv { s with win := w } :=
  h

theorem PosFreshInv.epMgmt {St Msg C : Type}
    {s s₁ : GameState St Msg C} (h : PosFreshInv s) {Δ qep : ℕ} {P : Party} {bad : Bool}
    (hEp : s.epMgmt Δ qep P bad = some s₁) :
    PosFreshInv s₁ := by
  unfold GameState.epMgmt GameState.leak at hEp
  split_ifs at hEp with hSends hCap1 hBad hCap2
  · cases hEp
    constructor
    · intro r hr
      have hr0 := h.1 r hr
      by_cases hP : r.pos.sender = P
      · subst hP; simp only [Function.update_self]; omega
      · simp only [Function.update_of_ne hP]; exact hr0
    · intro p hp
      have hp0 := h.2 p hp
      by_cases hP : p.sender = P
      · subst hP; simp only [Function.update_self]; omega
      · simp only [Function.update_of_ne hP]; exact hp0
  · cases hEp
    constructor
    · intro r hr
      have hr0 := h.1 r hr
      by_cases hP : r.pos.sender = P
      · subst hP; simp only [Function.update_self]; omega
      · simp only [Function.update_of_ne hP]; exact hr0
    · intro p hp
      have hp0 := h.2 p hp
      by_cases hP : p.sender = P
      · subst hP; simp only [Function.update_self]; omega
      · simp only [Function.update_of_ne hP]; exact hp0
  · cases hEp
    exact h

theorem PosFreshInv.record {St Msg C : Type}
    {s : GameState St Msg C} (h : PosFreshInv s)
    (Δ : ℕ) (P : Party) (st' : St) (r : Record Msg C) (isChall : Bool)
    (hPos : r.pos = ⟨P, s.epoch P, s.idx P + 1⟩) :
    PosFreshInv (s.record Δ P st' r isChall) := by
  unfold PosFreshInv GameState.record
  dsimp only
  constructor
  · intro r' hr'
    simp only [List.mem_cons] at hr'
    rcases hr' with rfl | hr'
    · simp [hPos]
    · have hr0 := h.1 r' hr'
      by_cases hP : r'.pos.sender = P
      · simp only [hPos, hP, Function.update_self] at hr0 ⊢
        omega
      · rw [Function.update_of_ne hP]; exact hr0
  · intro p hp
    split_ifs at hp with hSafe
    · have hp0 := h.2 p hp
      by_cases hP : p.sender = P
      · simp only [hPos, hP, Function.update_self] at hp0 ⊢
        omega
      · rw [Function.update_of_ne hP]; exact hp0
    · simp only [List.mem_cons] at hp
      rcases hp with rfl | hp
      · simp [hPos]
      · have hp0 := h.2 p hp
        by_cases hP : p.sender = P
        · simp only [hPos, hP, Function.update_self] at hp0 ⊢
          omega
        · rw [Function.update_of_ne hP]; exact hp0

theorem PosFreshInv.delete {St Msg C : Type}
    {s : GameState St Msg C} (h : PosFreshInv s) (pos : Pos) :
    PosFreshInv (s.delete pos) := by
  unfold GameState.delete
  exact ⟨fun r hr => h.1 r (List.mem_of_mem_filter hr),
    fun p hp => h.2 p (List.mem_of_mem_filter hp)⟩

theorem PosFreshInv.accept {St Msg C : Type}
    {s : GameState St Msg C} (h : PosFreshInv s) (P : Party) (st' : St) (pos : Pos) :
    PosFreshInv (s.accept P st' pos) := by
  have hd := h.delete pos
  unfold GameState.accept
  constructor
  · intro r hr
    have hr0 := hd.1 r hr
    dsimp only [GameState.delete] at hr0 ⊢
    by_cases hP : r.pos.sender = P
    · rw [hP, Function.update_self]
      rw [hP] at hr0; omega
    · rw [Function.update_of_ne hP]; exact hr0
  · intro p hp
    have hp0 := hd.2 p hp
    dsimp only [GameState.delete] at hp0 ⊢
    by_cases hP : p.sender = P
    · rw [hP, Function.update_self]
      rw [hP] at hp0; omega
    · rw [Function.update_of_ne hP]; exact hp0

theorem PosFreshInv.afterCorr {St Msg C : Type}
    {s : GameState St Msg C} (h : PosFreshInv s) (P : Party) :
    PosFreshInv (s.afterCorr P) := by
  unfold GameState.afterCorr GameState.leak
  constructor
  · exact h.1
  · intro p hp
    dsimp only at hp ⊢
    simp only [List.mem_append, List.mem_map, List.mem_filter] at hp
    rcases hp with ⟨r, ⟨hr, _⟩, rfl⟩ | hp
    · exact h.1 r hr
    · exact h.2 p hp

end GameStateDedup

end Computational.Proofs.GameHop.CompDedup
