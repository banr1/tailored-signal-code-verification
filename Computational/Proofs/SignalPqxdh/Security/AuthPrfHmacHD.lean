/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Computational.Proofs.SignalPqxdh.Security.AuthPrfHmacD
public import Computational.Proofs.SignalPqxdh.Security.CollisionsB
import Computational.Proofs.SignalPqxdh.Security.SigHopA
import VCVio.EvalDist.Monad.Basic
import VCVio.OracleComp.Constructions.SampleableType.Measure

/-!
# PQXDH authentication: last hybrid of the `PrfHmac` argument

Proves `gProb_last_le`, bounding the all-random hybrid (`defer = (· ≤ N - 1)`, `unifTag`) by
`q_dec / 2^64` via a potential over deferred 64-bit tag guesses, and `aeadMuIntCtxt_zero` when no
forgery queries are made.
-/

@[expose] public section

set_option autoImplicit false

open OracleSpec OracleComp MeasureTheory ENNReal BigOperators

namespace SignalPqxdh.Security

open SignalPqxdh
open RoKem

/-! ## Truncated uniform tag guessing bound -/

noncomputable def hdEps : ℝ≥0∞ := ((2 : ℝ≥0∞) ^ 64)⁻¹

theorem hd_mod_eq_of_bytes (x y : ℕ) (h : ∀ i < 8, (x >>> (8 * i)) % 256 = (y >>> (8 * i)) % 256) :
    x % 2 ^ 64 = y % 2 ^ 64 := by
  apply Nat.eq_of_testBit_eq
  intro j
  rw [Nat.testBit_mod_two_pow, Nat.testBit_mod_two_pow]
  by_cases hj : j < 64
  · have h1 := congrArg (fun z => Nat.testBit z (j % 8)) (h (j / 8) (by omega))
    simp only [show (256 : ℕ) = 2 ^ 8 from rfl, Nat.testBit_mod_two_pow, Nat.testBit_shiftRight]
      at h1
    have e : 8 * (j / 8) + j % 8 = j := by omega
    have h8 : j % 8 < 8 := Nat.mod_lt _ (by omega)
    simp only [e, h8, decide_true, Bool.true_and] at h1
    simp [hj, h1]
  · simp [hj]

theorem hd_lo8_eq (w1 w2 : BitVec 256)
    (h : (word256ToBytes w1).take 8 = (word256ToBytes w2).take 8) :
    w1.toNat % 2 ^ 64 = w2.toNat % 2 ^ 64 := by
  apply hd_mod_eq_of_bytes
  intro i hi
  have h1 := congrArg (fun L => L[i]?) h
  have hi32 : i < 32 := by omega
  simp only [List.getElem?_take, hi, ite_true, word256ToBytes, List.getElem?_ofFn, hi32,
    dite_true, Option.some.injEq] at h1
  have h2 := congrArg UInt8.toNat h1
  simpa [UInt8.toNat_ofNat] using h2

theorem hd_card_take8_le (tg : Bytes) :
    (Finset.univ.filter (fun w : BitVec 256 => (word256ToBytes w).take 8 = tg)).card ≤ 2 ^ 192 := by
  classical
  calc _ ≤ (Finset.univ : Finset (Fin (2 ^ 192))).card := by
        refine Finset.card_le_card_of_injOn
          (fun w : BitVec 256 => (⟨w.toNat / 2 ^ 64,
            Nat.div_lt_of_lt_mul (by rw [← pow_add]; exact w.isLt)⟩ : Fin (2 ^ 192)))
          (fun _ _ => Finset.mem_coe.2 (Finset.mem_univ _)) ?_
        intro a ha b hb hab
        simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_ofPred_eq] at ha hb
        have hm := hd_lo8_eq a b (ha.trans hb.symm)
        have hd : a.toNat / 2 ^ 64 = b.toNat / 2 ^ 64 := congrArg Fin.val hab
        apply BitVec.eq_of_toNat_eq
        rw [← Nat.div_add_mod a.toNat (2 ^ 64), ← Nat.div_add_mod b.toNat (2 ^ 64), hd, hm]
    _ = 2 ^ 192 := by simp

theorem hd_tag_bound (tg : Bytes) :
    probExpect sampleBytes32 (fun t => if t.take 8 = tg then 1 else 0) ≤ hdEps := by
  have hrw : probExpect sampleBytes32 (fun t => if t.take 8 = tg then 1 else 0) =
      𝒟[sampleBytes32 >>= fun t => pure (decide (t.take 8 = tg))] {true} := by
    rw [evalDist_bind_true_eq_probExpect]
    congr 1; funext t
    by_cases h : t.take 8 = tg <;> simp [h]
  rw [hrw]
  unfold sampleBytes32
  have hmap : ((word256ToBytes <$> ($ᵗ BitVec 256)) >>= fun t => pure (decide (t.take 8 = tg))) =
      (fun x : BitVec 256 => decide ((word256ToBytes x).take 8 = tg)) <$> ($ᵗ BitVec 256) := by
    simp [map_eq_bind_pure_comp]
  rw [hmap, evalDist_map ($ᵗ BitVec 256) Measurable.of_discrete,
    Measure.map_apply Measurable.of_discrete (MeasurableSet.singleton true),
    SampleableType.evalDist_bitVec]
  have hpre : ((fun x : BitVec 256 => decide ((word256ToBytes x).take 8 = tg)) ⁻¹' {true}) =
      {x : BitVec 256 | (word256ToBytes x).take 8 = tg} := by
    ext x; simp
  rw [hpre, ProbabilityTheory.uniformOn_univ_apply_setOf, Fintype.card_bitVec]
  apply ENNReal.div_le_of_le_mul
  have hc := hd_card_take8_le tg
  calc ((Finset.univ.filter (fun w : BitVec 256 => (word256ToBytes w).take 8 = tg)).card : ℝ≥0∞)
      ≤ ((2 ^ 192 : ℕ) : ℝ≥0∞) := by exact_mod_cast hc
    _ = hdEps * ((2 ^ 256 : ℕ) : ℝ≥0∞) := by
      unfold hdEps
      rw [Nat.cast_pow, Nat.cast_pow, Nat.cast_ofNat,
        show (2 : ℝ≥0∞) ^ 256 = 2 ^ 64 * 2 ^ 192 by rw [← pow_add],
        ENNReal.inv_mul_cancel_left (by simp) (by simp)]

/-! ## Expectation helpers and deferred checks -/

def hdInd (b : Bool) : ℝ≥0∞ := if b then 1 else 0

theorem hdInd_or_le (a b : Bool) : hdInd (a || b) ≤ hdInd a + hdInd b := by
  cases a <;> cases b <;> simp [hdInd]

theorem hd_probExpect_le_const {α : Type} (mx : ProbComp α) (f : α → ℝ≥0∞) (c : ℝ≥0∞)
    (h : ∀ x, f x ≤ c) : probExpect mx f ≤ c :=
  probExpect_const_le_of_support mx f c (fun x _ => h x)

theorem hd_probExpect_mono {α : Type} (mx : ProbComp α) (f g : α → ℝ≥0∞)
    (h : ∀ x, f x ≤ g x) : probExpect mx f ≤ probExpect mx g :=
  probExpect_mono_of_support mx f g (fun x _ => h x)

theorem hd_probExpect_add {α : Type} (mx : ProbComp α) (f g : α → ℝ≥0∞) :
    probExpect mx (fun x => f x + g x) = probExpect mx f + probExpect mx g := by
  let _ : MeasurableSpace α := ⊤
  have _ : DiscreteMeasurableSpace α := ⟨fun _ => trivial⟩
  unfold probExpect
  exact lintegral_add_left Measurable.of_discrete _

theorem hd_probExpect_const_add {α : Type} (mx : ProbComp α) (c : ℝ≥0∞) (g : α → ℝ≥0∞) :
    probExpect mx (fun x => c + g x) = c + probExpect mx g := by
  rw [hd_probExpect_add mx (fun _ => c) g, probExpect_const]

def hdCnt (pending : List (ℕ × Bytes × Bytes)) (r : ℕ) (x : Bytes) : ℕ :=
  pending.countP (fun e => e.1 == r && e.2.1 == x)

theorem hd_pendingHit_bound (r : ℕ) (x : Bytes) : ∀ pending : List (ℕ × Bytes × Bytes),
    probExpect sampleBytes32 (fun t => hdInd (prfHmacPendingHit pending r x t)) ≤
      (hdCnt pending r x : ℝ≥0∞) * hdEps
  | [] => by simp [prfHmacPendingHit, hdInd, hdCnt]
  | e :: pending => by
    have ih := hd_pendingHit_bound r x pending
    have hhead : probExpect sampleBytes32
        (fun t => if (e.1 == r && e.2.1 == x) = true then
          (if t.take 8 = e.2.2 then 1 else 0) else 0) ≤
        (if (e.1 == r && e.2.1 == x) = true then 1 else 0) * hdEps := by
      by_cases hc : (e.1 == r && e.2.1 == x) = true
      · simp only [hc, ite_true, one_mul]; exact hd_tag_bound e.2.2
      · simp only [hc, Bool.false_eq_true, ite_false, zero_mul]
        exact le_of_eq (probExpect_const _ 0)
    calc _ ≤ probExpect sampleBytes32 (fun t =>
          (if (e.1 == r && e.2.1 == x) = true then (if t.take 8 = e.2.2 then 1 else 0) else 0) +
            hdInd (prfHmacPendingHit pending r x t)) := by
          apply hd_probExpect_mono; intro t
          simp only [prfHmacPendingHit, List.any_cons]
          generalize List.any pending (fun e => e.1 == r && e.2.1 == x && e.2.2 == t.take 8) = c
          have hb : (e.2.2 == t.take 8) = decide (t.take 8 = e.2.2) := by
            by_cases h : t.take 8 = e.2.2
            · rw [h]; simp
            · have h' : ¬ e.2.2 = t.take 8 := fun h'' => h h''.symm
              simp [h, h']
          rw [hb]
          generalize (e.1 == r && e.2.1 == x) = a
          by_cases h2 : t.take 8 = e.2.2 <;> cases a <;> cases c <;> simp [hdInd, h2]
      _ = _ := hd_probExpect_add _ _ _
      _ ≤ (if (e.1 == r && e.2.1 == x) = true then 1 else 0) * hdEps +
            (hdCnt pending r x : ℝ≥0∞) * hdEps := add_le_add hhead ih
      _ = _ := by
          simp only [hdCnt, List.countP_cons]
          push_cast
          split_ifs <;> simp [add_mul, add_comm]

theorem hd_sum_ind_le_one (e : ℕ × Bytes × Bytes) : ∀ pts : List (ℕ × Bytes), pts.Nodup →
    (pts.map (fun p => if (e.1 == p.1 && e.2.1 == p.2) = true then 1 else 0)).sum ≤ 1
  | [], _ => by simp
  | p :: pts, hnd => by
    rw [List.nodup_cons] at hnd
    have ih := hd_sum_ind_le_one e pts hnd.2
    simp only [List.map_cons, List.sum_cons]
    by_cases hp : (e.1 == p.1 && e.2.1 == p.2) = true
    · have hz : (pts.map (fun p => if (e.1 == p.1 && e.2.1 == p.2) = true then 1 else 0)).sum
          = 0 := by
        apply List.sum_eq_zero
        intro y hy
        obtain ⟨p', hp', rfl⟩ := List.mem_map.1 hy
        have hne : ¬ (e.1 == p'.1 && e.2.1 == p'.2) = true := by
          intro h'
          apply hnd.1
          simp only [Bool.and_eq_true, beq_iff_eq] at hp h'
          have : p = p' := Prod.ext (hp.1.symm.trans h'.1) (hp.2.symm.trans h'.2)
          exact this ▸ hp'
        simp only [hne, Bool.false_eq_true, ite_false]
      rw [ite_eq_left hp, hz]
    · rw [ite_eq_right hp]; omega

theorem hd_cnt_sum_le (pts : List (ℕ × Bytes)) (hnd : pts.Nodup) :
    ∀ pending : List (ℕ × Bytes × Bytes),
      (pts.map (fun p => hdCnt pending p.1 p.2)).sum ≤ pending.length
  | [] => by simp [hdCnt]
  | e :: pending => by
    have ih := hd_cnt_sum_le pts hnd pending
    have h1 := hd_sum_ind_le_one e pts hnd
    simp only [hdCnt, List.countP_cons, List.sum_map_add, List.length_cons] at ih h1 ⊢
    omega

noncomputable def hdFin (pending : List (ℕ × Bytes × Bytes)) : List (ℕ × Bytes) → ProbComp Bool
  | [] => pure false
  | (r, x) :: pts => do
    let t ← sampleBytes32
    let rest ← hdFin pending pts
    pure (prfHmacPendingHit pending r x t || rest)

theorem hd_fin_bound (pending : List (ℕ × Bytes × Bytes)) : ∀ pts : List (ℕ × Bytes),
    probExpect (hdFin pending pts) hdInd ≤
      ((pts.map (fun p => hdCnt pending p.1 p.2)).sum : ℝ≥0∞) * hdEps
  | [] => by simp [hdFin, hdInd]
  | (r, x) :: pts => by
    simp only [hdFin, probExpect_bind, probExpect_pure]
    calc _ ≤ probExpect sampleBytes32 (fun t =>
          hdInd (prfHmacPendingHit pending r x t) + probExpect (hdFin pending pts) hdInd) := by
          apply hd_probExpect_mono; intro t
          calc _ ≤ probExpect (hdFin pending pts)
                (fun rest => hdInd (prfHmacPendingHit pending r x t) + hdInd rest) :=
                hd_probExpect_mono _ _ _ (fun rest => hdInd_or_le _ _)
            _ = _ := hd_probExpect_const_add _ _ _
      _ = _ := hd_probExpect_add _ _ _
      _ ≤ (hdCnt pending r x : ℝ≥0∞) * hdEps +
            ((pts.map (fun p => hdCnt pending p.1 p.2)).sum : ℝ≥0∞) * hdEps := by
          rw [probExpect_const]
          exact add_le_add (hd_pendingHit_bound r x pending) (hd_fin_bound pending pts)
      _ = _ := by simp only [List.map_cons, List.sum_cons]; push_cast; ring

/-! ## Potential argument -/

/-- Invariant: the key count plus the remaining budgets is at most `N`, and all ranks are `< N`. -/
def hdInv (N E D : ℕ) (st : PrfHmacMuState) : Prop :=
  st.keys.length + E + D ≤ N ∧ ∀ e ∈ st.keys, e.2.1 < N

/-- Potential: `[bad] + (|pending| + D) · 2^-64`. -/
noncomputable def hdPhi (st : PrfHmacMuState) (D : ℕ) : ℝ≥0∞ :=
  hdInd st.bad + ((st.pending.length + D : ℕ) : ℝ≥0∞) * hdEps

theorem hdPhi_mono (st : PrfHmacMuState) {D D' : ℕ} (h : D ≤ D') : hdPhi st D ≤ hdPhi st D' := by
  unfold hdPhi
  gcongr

theorem hdPhi_cons (st st' : PrfHmacMuState) (D : ℕ) (hD : 0 < D) (hb : st'.bad = st.bad)
    (hl : st'.pending.length = st.pending.length + 1) : hdPhi st' (D - 1) = hdPhi st D := by
  unfold hdPhi
  rw [hb, hl]
  congr 3
  omega

theorem hd_filter_cnt (r : ℕ) (x : Bytes) : ∀ l : List (ℕ × Bytes × Bytes),
    (l.filter (fun e => !(e.1 == r && e.2.1 == x))).length + hdCnt l r x = l.length
  | [] => rfl
  | e :: l => by
    have ih := hd_filter_cnt r x l
    unfold hdCnt at ih ⊢
    rw [List.filter_cons, List.countP_cons]
    cases h : (e.1 == r && e.2.1 == x)
    · simp only [Bool.not_false, ite_true, Bool.false_eq_true, ite_false, List.length_cons]
      omega
    · simp only [Bool.not_true, ite_true, Bool.false_eq_true, ite_false, List.length_cons]
      omega

theorem hd_chal_bound (st : PrfHmacMuState) (D r : ℕ) (x0 : Bytes) (F : Bytes → PrfHmacMuState)
    (hF : ∀ t, (F t).pending = st.pending.filter (fun e => !(e.1 == r && e.2.1 == x0)) ∧
      (F t).bad = (st.bad || prfHmacPendingHit st.pending r x0 t)) :
    probExpect sampleBytes32 (fun t => hdPhi (F t) D) ≤ hdPhi st D := by
  set L : ℝ≥0∞ :=
    (((st.pending.filter (fun e => !(e.1 == r && e.2.1 == x0))).length + D : ℕ) : ℝ≥0∞) * hdEps
  calc probExpect sampleBytes32 (fun t => hdPhi (F t) D)
      ≤ probExpect sampleBytes32 (fun t =>
          hdInd st.bad + (hdInd (prfHmacPendingHit st.pending r x0 t) + L)) := by
        apply hd_probExpect_mono; intro t
        unfold hdPhi; rw [(hF t).1, (hF t).2, ← add_assoc]
        exact add_le_add (hdInd_or_le _ _) le_rfl
    _ = hdInd st.bad +
          (probExpect sampleBytes32 (fun t => hdInd (prfHmacPendingHit st.pending r x0 t)) + L) := by
        rw [hd_probExpect_const_add, hd_probExpect_add, probExpect_const]
    _ ≤ hdInd st.bad + ((hdCnt st.pending r x0 : ℝ≥0∞) * hdEps + L) := by
        gcongr; exact hd_pendingHit_bound r x0 st.pending
    _ = hdPhi st D := by
        unfold hdPhi
        rw [← add_mul]
        congr 2
        have := hd_filter_cnt r x0 st.pending
        norm_cast
        omega

section Sim

variable (P : Primitives) {σ : Type} (ev : QueryImpl prfHmacSpec (StateT σ ProbComp))

theorem hd_run_unif {α : Type} (mx : ProbComp α) (c : σ) :
    (simulateQ (gFull P ev) (prfHmacUnif mx)).run c = (fun a => (a, c)) <$> mx := by
  unfold prfHmacUnif gFull
  rw [simulateQ_embedPrim_run, simulateQ_embedUnif]

theorem hd_run_finish (pending : List (ℕ × Bytes × Bytes)) : ∀ (pts : List (ℕ × Bytes)) (c : σ),
    (simulateQ (gFull P ev) (gFinish unifTag pending pts)).run c =
      (fun b => (b, c)) <$> hdFin pending pts
  | [], c => by simp [gFinish, hdFin]
  | (r, x) :: pts, c => by
    simp only [gFinish, hdFin, unifTag, simulateQ_bind, simulateQ_pure, StateT.run_bind,
      hd_run_unif, hd_run_finish pending pts, map_eq_bind_pure_comp, bind_assoc, pure_bind,
      Function.comp, StateT.run_pure]

theorem hd_key_le (i : ℕ) (st : PrfHmacMuState) (c : σ)
    (G : ((ℕ × MessageKeys) × PrfHmacMuState) × σ → ℝ≥0∞) (b : ℝ≥0∞)
    (h1 : ∀ e, st.keys.lookup i = some e → G ((e, st), c) ≤ b)
    (h2 : st.keys.lookup i = none → ∀ mk,
      G (((st.keys.length, mk), { st with keys := (i, (st.keys.length, mk)) :: st.keys }), c) ≤ b) :
    probExpect ((simulateQ (gFull P ev) (prfHmacMuKey i st)).run c) G ≤ b := by
  unfold prfHmacMuKey
  split
  · rename_i e he
    simp only [simulateQ_pure, StateT.run_pure, probExpect_pure]
    exact h1 e he
  · rename_i hn
    simp only [simulateQ_bind, StateT.run_bind, hd_run_unif, simulateQ_pure, StateT.run_pure,
      map_eq_bind_pure_comp, bind_assoc, pure_bind, Function.comp, probExpect_bind,
      probExpect_pure]
    exact hd_probExpect_le_const _ _ _ (fun mk => h2 hn mk)

theorem hd_step_enc (defer : ℕ → Prop) [DecidablePred defer] (N : ℕ) (hdef : ∀ r, r < N → defer r)
    (i : ℕ) (ad pt : Bytes) (st : PrfHmacMuState) (c : σ) (E D : ℕ) (hE : 0 < E)
    (hinv : hdInv N E D st)
    (G : (Option Bytes × PrfHmacMuState) × σ → ℝ≥0∞)
    (hG : ∀ z, hdInv N (E - 1) D z.1.2 → G z ≤ hdPhi z.1.2 D) :
    probExpect ((simulateQ (gFull P ev) (gStep defer unifTag (.encOnce i ad pt) st)).run c) G ≤
      hdPhi st D := by
  simp only [gStep]
  split
  · simp only [simulateQ_pure, StateT.run_pure, probExpect_pure]
    refine hG ((none, st), c) ⟨?_, hinv.2⟩
    have := hinv.1; dsimp only; omega
  · rename_i hnone
    simp only [simulateQ_bind, StateT.run_bind, probExpect_bind]
    apply hd_key_le
    · intro e he
      obtain ⟨r, mk⟩ := e
      have hr : r < N := hinv.2 _ (prf_lookup_mem _ _ _ he)
      simp only [hdef r hr, ite_true, unifTag, simulateQ_bind, simulateQ_pure, StateT.run_bind,
        StateT.run_pure, hd_run_unif, map_eq_bind_pure_comp, bind_assoc, pure_bind,
        Function.comp, probExpect_bind, probExpect_pure]
      apply hd_probExpect_le_const; intro ct
      refine le_trans (hd_probExpect_mono _ _ _ (fun t => hG _ ⟨?_, hinv.2⟩))
        (hd_chal_bound st D r _ _ (fun t => ⟨rfl, rfl⟩))
      have := hinv.1; dsimp only; omega
    · intro hn mk
      have hr : st.keys.length < N := by have := hinv.1; omega
      simp only [hdef _ hr, ite_true, unifTag, simulateQ_bind, simulateQ_pure, StateT.run_bind,
        StateT.run_pure, hd_run_unif, map_eq_bind_pure_comp, bind_assoc, pure_bind,
        Function.comp, probExpect_bind, probExpect_pure]
      apply hd_probExpect_le_const; intro ct
      refine le_trans (hd_probExpect_mono _ _ _ (fun t => hG _ ⟨?_, ?_⟩))
        (hd_chal_bound { st with keys := (i, (st.keys.length, mk)) :: st.keys } D
          st.keys.length _ _ (fun t => ⟨rfl, rfl⟩))
      · have := hinv.1; dsimp only; simp only [List.length_cons]; omega
      · intro e he
        rcases List.mem_cons.1 he with rfl | he
        · exact hr
        · exact hinv.2 e he

theorem hd_step_forge (defer : ℕ → Prop) [DecidablePred defer] (N : ℕ)
    (hdef : ∀ r, r < N → defer r)
    (i : ℕ) (ad ct : Bytes) (st : PrfHmacMuState) (c : σ) (E D : ℕ) (hD : 0 < D)
    (hinv : hdInv N E D st)
    (G : (Bool × PrfHmacMuState) × σ → ℝ≥0∞)
    (hG : ∀ z, hdInv N E (D - 1) z.1.2 → G z ≤ hdPhi z.1.2 (D - 1)) :
    probExpect ((simulateQ (gFull P ev) (gStep defer unifTag (.tryForge i ad ct) st)).run c) G ≤
      hdPhi st D := by
  simp only [gStep]
  split
  · simp only [simulateQ_pure, StateT.run_pure, probExpect_pure]
    refine le_trans (hG ((false, st), c) ⟨?_, hinv.2⟩) (hdPhi_mono _ (by omega))
    have := hinv.1; dsimp only; omega
  · simp only [simulateQ_bind, StateT.run_bind, probExpect_bind]
    apply hd_key_le
    · intro e he
      obtain ⟨r, mk⟩ := e
      have hr : r < N := hinv.2 _ (prf_lookup_mem _ _ _ he)
      dsimp only
      split
      · rw [ite_eq_left (hdef r hr)]
        simp only [simulateQ_pure, StateT.run_pure, probExpect_pure]
        refine le_trans (hG _ ⟨?_, hinv.2⟩) (le_of_eq (hdPhi_cons _ _ D hD rfl rfl))
        have := hinv.1; dsimp only; omega
      · simp only [simulateQ_pure, StateT.run_pure, probExpect_pure]
        refine le_trans (hG ((false, st), c) ⟨?_, hinv.2⟩) (hdPhi_mono _ (by omega))
        have := hinv.1; dsimp only; omega
    · intro hn mk
      have hr : st.keys.length < N := by have := hinv.1; omega
      have hinv' : ∀ (st' : PrfHmacMuState), st'.keys = (i, (st.keys.length, mk)) :: st.keys →
          hdInv N E (D - 1) st' := by
        intro st' hk
        refine ⟨?_, ?_⟩
        · rw [hk, List.length_cons]; have := hinv.1; omega
        · intro e he
          rw [hk] at he
          rcases List.mem_cons.1 he with rfl | he
          · exact hr
          · exact hinv.2 e he
      dsimp only
      split
      · rw [ite_eq_left (hdef _ hr)]
        simp only [simulateQ_pure, StateT.run_pure, probExpect_pure]
        exact le_trans (hG _ (hinv' _ rfl)) (le_of_eq (hdPhi_cons _ _ D hD rfl rfl))
      · simp only [simulateQ_pure, StateT.run_pure, probExpect_pure]
        exact le_trans (hG _ (hinv' _ rfl)) (hdPhi_mono _ (by omega))

theorem hd_main (defer : ℕ → Prop) [DecidablePred defer] (N : ℕ) (hdef : ∀ r, r < N → defer r)
    {α : Type} (mx : OracleComp AeadMuIntSimSpec α) (E D : ℕ)
    (hE : IsQueryBoundP mx isMuEncQuery E) (hD : IsQueryBoundP mx isMuForgeQuery D)
    (st : PrfHmacMuState) (c : σ) (hinv : hdInv N E D st) :
    probExpect ((simulateQ (gOuter P ev defer unifTag) mx).run (st, c))
      (fun z => hdPhi z.2.1 0) ≤ hdPhi st D := by
  induction mx using OracleComp.inductionOn generalizing E D st c with
  | pure a =>
    simp only [simulateQ_pure, StateT.run_pure, probExpect_pure]
    exact hdPhi_mono _ (Nat.zero_le _)
  | query_bind q mx ih =>
    rw [isQueryBoundP_query_bind_iff] at hE hD
    rcases q with pq | mq
    · have hE' : ¬ isMuEncQuery (Sum.inl pq) := fun h => by cases h
      have hD' : ¬ isMuForgeQuery (Sum.inl pq) := fun h => by cases h
      simp only [hE', hD', ↓reduceIte] at hE hD
      simp only [simulateQ_bind, simulateQ_query, OracleQuery.input_query, OracleQuery.cont_query,
        id_map, StateT.run_bind, gOuter, StateT.run_mk, bind_assoc, pure_bind, probExpect_bind]
      exact hd_probExpect_le_const _ _ _ (fun u => ih u E D (hE.2 u) (hD.2 u) st c hinv)
    · rcases mq with ⟨i, ad, pt⟩ | ⟨i, ad, ct⟩
      · have hEq : isMuEncQuery (Sum.inr (.encOnce i ad pt)) := trivial
        have hDq : ¬ isMuForgeQuery (Sum.inr (.encOnce i ad pt)) := fun h => by cases h
        simp only [hEq, hDq, ↓reduceIte] at hE hD
        have hEpos : 0 < E := by rcases hE.1 with h | h; exact absurd hEq h; exact h
        simp only [simulateQ_bind, simulateQ_query, OracleQuery.input_query,
          OracleQuery.cont_query, id_map, StateT.run_bind, gOuter, StateT.run_mk, bind_assoc,
          pure_bind, probExpect_bind]
        exact hd_step_enc P ev defer N hdef i ad pt st c E D hEpos hinv _
          (fun z hz => ih z.1.1 (E - 1) D (hE.2 _) (hD.2 _) z.1.2 z.2 hz)
      · have hEq : ¬ isMuEncQuery (Sum.inr (.tryForge i ad ct)) := fun h => by cases h
        have hDq : isMuForgeQuery (Sum.inr (.tryForge i ad ct)) := trivial
        simp only [hEq, hDq, ↓reduceIte] at hE hD
        have hDpos : 0 < D := by rcases hD.1 with h | h; exact absurd hDq h; exact h
        simp only [simulateQ_bind, simulateQ_query, OracleQuery.input_query,
          OracleQuery.cont_query, id_map, StateT.run_bind, gOuter, StateT.run_mk, bind_assoc,
          pure_bind, probExpect_bind]
        exact hd_step_forge P ev defer N hdef i ad ct st c E D hDpos hinv _
          (fun z hz => ih z.1.1 E (D - 1) (hE.2 _) (hD.2 _) z.1.2 z.2 hz)

end Sim

/-! ## Last hybrid bound -/

theorem hd_after_bound (P : Primitives) (B : AeadMuIntCtxtAdv) (hB : B.Bounded)
    (defer : ℕ → Prop) [DecidablePred defer] (hdef : ∀ r, r < B.q_enc + B.q_dec → defer r)
    (k : Bytes) (c : List (Bytes × Bytes)) :
    probExpect ((simulateQ (prfFullImpl P false k) (gAfter defer unifTag B)).run c)
      (fun z => hdInd z.1) ≤ (B.q_dec : ℝ≥0∞) * hdEps := by
  have hfull : prfFullImpl P false k = gFull P (prfEvalImpl P false k) := rfl
  rw [hfull]
  unfold gAfter
  simp only [simulateQ_bind, StateT.run_bind, simulateQ_gRun, map_eq_bind_pure_comp, bind_assoc,
    pure_bind, Function.comp, probExpect_bind]
  have hmain := hd_main P (prfEvalImpl P false k) defer (B.q_enc + B.q_dec) hdef B.run
    B.q_enc B.q_dec hB.1 hB.2.1 {} c ⟨by simp, by simp⟩
  have h0 : hdPhi ({} : PrfHmacMuState) B.q_dec = (B.q_dec : ℝ≥0∞) * hdEps := by
    simp [hdPhi, hdInd]
  rw [← h0]
  refine le_trans (hd_probExpect_mono _ _ _ (fun z => ?_)) hmain
  obtain ⟨u, st, c'⟩ := z
  dsimp only
  simp only [hd_run_finish, map_eq_bind_pure_comp, Function.comp,
    probExpect_bind, probExpect_pure, StateT.run_pure, simulateQ_pure]
  calc _ ≤ probExpect (hdFin st.pending (pendPts st.pending))
        (fun h => hdInd st.bad + hdInd h) := hd_probExpect_mono _ _ _ (fun h => hdInd_or_le _ _)
    _ = hdInd st.bad + probExpect (hdFin st.pending (pendPts st.pending)) hdInd :=
        hd_probExpect_const_add _ _ _
    _ ≤ hdInd st.bad + (st.pending.length : ℝ≥0∞) * hdEps := by
        gcongr
        refine le_trans (hd_fin_bound _ _) ?_
        gcongr
        exact_mod_cast hd_cnt_sum_le _ (List.nodup_dedup _) _
    _ = hdPhi st 0 := by simp [hdPhi]

theorem gProb_last_le (P : Primitives) (B : AeadMuIntCtxtAdv) (hB : B.Bounded)
    (hN : 0 < B.q_enc + B.q_dec) :
    gProb P false (fun r => r ≤ B.q_enc + B.q_dec - 1) unifTag B ≤ (B.q_dec : ℝ) / (2 : ℝ) ^ 64 := by
  have hdef : ∀ r, r < B.q_enc + B.q_dec → r ≤ B.q_enc + B.q_dec - 1 := fun r hr => by omega
  unfold gProb
  have hrw : (do
      let k ← sampleBytes32
      let (z, _) ← (simulateQ (prfFullImpl P false k)
        (gAfter (fun r => r ≤ B.q_enc + B.q_dec - 1) unifTag B)).run []
      return z : ProbComp Bool) =
      ((do
        let k ← sampleBytes32
        (simulateQ (prfFullImpl P false k)
          (gAfter (fun r => r ≤ B.q_enc + B.q_dec - 1) unifTag B)).run []) >>=
        fun z => pure z.1) := by
    simp only [bind_assoc]
  rw [hrw, evalDist_bind_true_eq_probExpect, probExpect_bind]
  have hle : (probExpect sampleBytes32 fun k =>
      probExpect ((simulateQ (prfFullImpl P false k)
        (gAfter (fun r => r ≤ B.q_enc + B.q_dec - 1) unifTag B)).run [])
        (fun z => 𝒟[(pure z.1 : ProbComp Bool)] {true})) ≤ (B.q_dec : ℝ≥0∞) * hdEps := by
    apply hd_probExpect_le_const; intro k
    refine le_trans (le_of_eq ?_) (hd_after_bound P B hB _ hdef k [])
    congr 1; funext z
    cases z.1 <;> simp [hdInd]
  have hfin : (B.q_dec : ℝ≥0∞) * hdEps ≠ ⊤ := by
    unfold hdEps; exact ENNReal.mul_ne_top (by simp) (by simp)
  refine le_trans (ENNReal.toReal_mono hfin hle) (le_of_eq ?_)
  unfold hdEps
  rw [ENNReal.toReal_mul, ENNReal.toReal_inv, ENNReal.toReal_pow, ENNReal.toReal_natCast]
  simp [div_eq_mul_inv]

/-! ## Zero forgery budget -/

theorem hd_win_false
    (impl : QueryImpl (PrimBaseSpec + aeadMuIntSpec) (StateT AeadMuIntState ProbComp))
    (hstep : ∀ q, ¬ isMuForgeQuery q → ∀ s : AeadMuIntState, s.2.2 = false →
      ∀ z ∈ support ((impl q).run s), z.2.2.2 = false)
    {α : Type} (mx : OracleComp (PrimBaseSpec + aeadMuIntSpec) α)
    (hD : IsQueryBoundP mx isMuForgeQuery 0) (s : AeadMuIntState) (hs : s.2.2 = false) :
    ∀ z ∈ support ((simulateQ impl mx).run s), z.2.2.2 = false := by
  induction mx using OracleComp.inductionOn generalizing s with
  | pure a =>
    intro z hz
    simp only [simulateQ_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff] at hz
    subst hz; exact hs
  | query_bind q mx ih =>
    rw [isQueryBoundP_query_bind_iff] at hD
    have hq : ¬ isMuForgeQuery q := by
      rcases hD.1 with h | h
      · exact h
      · exact absurd h (Nat.lt_irrefl 0)
    have hD2 : ∀ u, IsQueryBoundP (mx u) isMuForgeQuery 0 := by
      intro u; have := hD.2 u; simpa [hq] using this
    intro z hz
    simp only [simulateQ_bind, simulateQ_query, OracleQuery.input_query, OracleQuery.cont_query,
      id_map, StateT.run_bind, support_bind, Set.mem_iUnion] at hz
    obtain ⟨p, hp, hz⟩ := hz
    exact ih p.1 (hD2 p.1) p.2 (hstep q hq s hs p hp) z hz

theorem hd_key_w (i : ℕ) (s : AeadMuIntState) (z : MessageKeys × AeadMuIntState)
    (hz : z ∈ support ((aeadMuIntKey i).run s)) : z.2.2.2 = s.2.2 := by
  obtain ⟨keys, chal, w⟩ := s
  unfold aeadMuIntKey at hz
  simp only [StateT.run_bind, StateT.run_get, pure_bind] at hz
  cases h : keys.lookup i with
  | some mk =>
    simp only [h, StateT.run_pure, support_pure, Set.mem_singleton_iff] at hz
    subst hz; rfl
  | none =>
    simp [h, StateT.run_bind, StateT.run_set] at hz
    obtain ⟨a, _, rfl⟩ := hz
    rfl

theorem aeadMuIntCtxt_zero (P : Primitives) (B : AeadMuIntCtxtAdv) (hB : B.Bounded)
    (h0 : B.q_enc + B.q_dec = 0) : AeadMuIntCtxt P B ≤ 0 := by
  have hD : IsQueryBoundP B.run isMuForgeQuery 0 := by
    have := hB.2.1; rwa [show B.q_dec = 0 by omega] at this
  unfold AeadMuIntCtxt aeadMuIntCtxtExp
  simp only
  rw [show ∀ (mx : ProbComp (Unit × AeadMuIntState)),
      (mx >>= fun a => match a with | (_, (_, _, w)) => pure w) = mx >>= fun a => pure a.2.2.2
      from fun mx => by congr 1, evalDist_bind_true_eq_probExpect]
  rw [probExpect_eq_zero_of_support]
  · simp
  intro z hz
  rw [hd_win_false _ ?_ B.run hD _ rfl z hz]
  · simp
  intro q hq s hs z hz
  rcases q with pq | mq
  · simp [QueryImpl.liftTarget] at hz
    obtain ⟨a, _, rfl⟩ := hz
    exact hs
  · rcases mq with ⟨i, ad, pt⟩ | ⟨i, ad, ct⟩
    · obtain ⟨keys, chal, w⟩ := s
      simp only at hs; subst hs
      cases hg : goodFirstMsgAD ad
      · simp [hg, StateT.run_pure] at hz
        subst hz; rfl
      simp only [QueryImpl.add_apply_inr, hg, Bool.not_true, Bool.false_eq_true, ↓reduceIte,
        StateT.run_bind, StateT.run_get, pure_bind] at hz
      cases hc : chal.lookup i with
      | some _ =>
        simp only [hc, StateT.run_pure, support_pure, Set.mem_singleton_iff] at hz
        subst hz; rfl
      | none =>
        simp only [hc, StateT.run_bind, support_bind, Set.mem_iUnion] at hz
        obtain ⟨p, hp, hz⟩ := hz
        have hpw := hd_key_w i _ p hp
        obtain ⟨mk, keys', chal', w'⟩ := p
        simp only at hpw; subst hpw
        simp [StateT.run_get, StateT.run_set] at hz
        subst hz; rfl
    · exact absurd trivial hq

end SignalPqxdh.Security
