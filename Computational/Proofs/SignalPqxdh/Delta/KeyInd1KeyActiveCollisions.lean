/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Computational.Specifications.Pqxdh.Bound
public import Computational.Proofs.GameHop.StateSim -- proof-setup: allow-public-import
public import Computational.Proofs.GameHop.Fel -- proof-setup: allow-public-import
public import Computational.Proofs.SignalPqxdh.Security.Collisions -- proof-setup: allow-public-import
public import Computational.Proofs.SignalPqxdh.Security.SigHop1Key -- proof-setup: allow-public-import
public import Computational.Proofs.SignalPqxdh.Security.RoKemHop1Key -- proof-setup: allow-public-import
public import Computational.Proofs.SignalPqxdh.Delta.KeyInd1KeyActiveLengths -- proof-setup: allow-public-import

/-!
# Creation-Order Active-Count Birthday Collision Hops

Proves the active-count birthday collision bounds for one-key `KeyInd` (`G0 -> G0_1`, `G1 -> G2`,
and `G2 -> G2_1` / `G2_5`) parameterized by `b.q_on`, bounding ML-KEM-1024 public-key collisions
via `activeSpkCount` and X25519 / initiator `dh2` collisions via `activeDhCount` and
`activeSendCount`.
-/

set_option autoImplicit false

open BigOperators OracleSpec OracleComp
open SignalPqxdh (Setup Primitives Bytes QueryBudget BoundedAdv KeyIndAdversary KeyIndQuery
  KeyIndResponse KeyIndState SpkBundleEntry KeyIndInitiatorEntry SessionId PreKeyBundleInput
  keyIndSpec pqxdhKeyIndImpl pqxdhKeyIndImpl1KeyRo pqxdhKeyIndImpl1KeyReal runKeyIndInitiate
  sampleScalar32 sampleCoins32 sampleKemKeyGen koskBundleOk resolveSigPk encodeEC encodeKEM
  CryptoWellFormedPrimitivesδ activeSpkCount activeSendCount activeDhCount)
open SignalPqxdh.Security (HasKeyIndState hasDuplicateBytes allHonestEcPksKeyInd
  allHonestKemPksKeyInd allInitDh2sKeyInd hasEcPkCollisionKeyInd hasKemPkCollisionKeyInd
  Pfixed_pk_ec Pfixed_pk_kem pfixed_pk_ec_nonneg pfixed_pk_kem_nonneg runKeyInd1KeySim
  ecCollProbKeyInd1Key kemCollProbKeyInd1Key keyInd1KeyAdvG0 keyInd1KeyAdvG0_1 keyInd1KeyAdvG1
  keyInd1KeyAdvG2 keyInd1KeyAdvG2_1 keyInd1KeyAdvG1_eq_G2 keyInd1Key_hop_G0_G0_1_le_prob
  keyInd1Key_hop_G2_G2_1_le_prob probExpect probExpect_pure probExpect_bind probExpect_const
  probExpect_mono_of_support probExpect_const_le_of_support probExpect_swap
  evalDist_bind_true_eq_probExpect toReal_bind_bool_mono_of_support toReal_any_range_le_sum
  ValidKeyIndDh2 validKeyIndDh2_empty pqxdhKeyIndImpl1KeyRo_dh2_step ValidTaggedPks
  hasTaggedPairCollAt hasDuplicateBytes_map_snd_imp_any_double_range ecPairPotential
  evalDist_hasTaggedPairCollAt_le_potential ecPairPotential_nil_le find?_fst_none_of_not_mem
  find?_insert_fresh probExpect_ecPairPotential_insert_fresh_le
  simulateQ_valid_and_ecPairPotential_le probExpect_sampleKemKeyGen_coll_le hasUpperTaggedPairCollAt
  hasDuplicateBytes_map_snd_imp_any_upper_double_range dh2UpperPairPotential
  evalDist_hasUpperTaggedPairCollAt_le_potential dh2UpperPairPotential_nil_le
  probExpect_dh2UpperPairPotential_cons_fresh_le exists_skB_of_koskBundleOk sum_lt_range_const)
open Proofs.SignalPqxdh.Security (pqxdhKeyIndImpl1KeyRo_initPrin_preserves_spkBundles
  map_proj_simulateQ keyInd1KeyAdvG2_5)
open Computational.Proofs.SignalPqxdh.Delta.KeyInd1KeyActiveLengths
  (runKeyInd1KeySim_mem_support_activeBounded mem_support_runKeyIndInitiate
   mem_support_pqxdhKeyIndImpl pqxdhKeyIndImpl_preserves_spkBundles_nonGen)

namespace Computational.Proofs.SignalPqxdh.Delta.KeyInd1KeyActiveCollisions

public section
/-! ## Active ML-KEM-1024 birthday collision hop -/

/-- Tags each entry of a newest-first list `L` with its creation ordinal `tail.length`. -/
@[expose] def tagByCreation {α : Type} (f : α → Bytes) : List α → List (Nat × Bytes)
  | [] => []
  | x :: xs => (xs.length, f x) :: tagByCreation f xs

@[simp] theorem tagByCreation_nil {α : Type} (f : α → Bytes) : tagByCreation f [] = [] := by
  rfl

@[simp] theorem tagByCreation_cons {α : Type} (f : α → Bytes) (x : α) (xs : List α) :
    tagByCreation f (x :: xs) = (xs.length, f x) :: tagByCreation f xs := by
  rfl

theorem map_snd_tagByCreation {α : Type} (f : α → Bytes) :
    ∀ (L : List α), (tagByCreation f L).map Prod.snd = L.map f := by
  intro L; induction L with
  | nil => rfl
  | cons _ xs ih => simp [ih]

theorem tagByCreation_eq_id_map {α : Type} (f : α → Bytes) :
    ∀ (L : List α), tagByCreation f L = tagByCreation id (L.map f) := by
  intro L; induction L with
  | nil => rfl
  | cons _ xs ih => simp [ih]

private theorem fst_lt_length_of_mem_tagByCreation {α : Type} (f : α → Bytes) :
    ∀ (L : List α) (p : Nat × Bytes), p ∈ tagByCreation f L → p.1 < L.length := by
  intro L; induction L with
  | nil => intro _ hp; exact False.elim (List.not_mem_nil hp)
  | cons _ xs ih =>
    intro _ hp
    rcases List.mem_cons.mp hp with rfl | htl
    · exact Nat.lt_succ_self xs.length
    · exact Nat.lt_succ_of_lt (ih _ htl)

theorem not_mem_fst_tagByCreation_length {α : Type} (f : α → Bytes) (L : List α) :
    L.length ∉ (tagByCreation f L).map Prod.fst := by
  intro hmem; rcases List.mem_map.mp hmem with ⟨p, hp, heq⟩
  exact Nat.lt_irrefl L.length (heq ▸ fst_lt_length_of_mem_tagByCreation f L p hp)

theorem validTaggedPks_tagByCreation {α : Type} (f : α → Bytes) :
    ∀ (L : List α) {N : Nat}, L.length ≤ N → ValidTaggedPks N (tagByCreation f L) := by
  intro L; induction L with
  | nil => intro _ _; exact ⟨fun _ h => False.elim (List.not_mem_nil h), List.nodup_nil⟩
  | cons _ xs ihL =>
    intro _ hN
    have ih := ihL (Nat.le_of_succ_le hN)
    refine ⟨fun p hp => ?_, List.nodup_cons.mpr ⟨not_mem_fst_tagByCreation_length f xs, ih.2⟩⟩
    rcases List.mem_cons.mp hp with rfl | htl
    · exact Nat.lt_of_lt_of_le (Nat.lt_succ_self xs.length) hN
    · exact ih.1 p htl

theorem tagByCreation_map_congr {α : Type} (f : α → Bytes) (g : α → α)
    (hg : ∀ x, f (g x) = f x) : ∀ (L : List α), tagByCreation f (L.map g) = tagByCreation f L := by
  intro L; induction L with
  | nil => rfl
  | cons x xs ih => simp [hg x, ih]

private theorem simulateQ_potential_le {ι St α : Type} {QSpec : OracleSpec ι}
    (ValidSt : St → Prop) (pot : St → ENNReal) (impl : QueryImpl QSpec (StateT St ProbComp))
    (hValid : ∀ q st, ValidSt st → ∀ x ∈ support ((impl q).run st), ValidSt x.2)
    (hStep : ∀ q st, ValidSt st → probExpect ((impl q).run st) (fun x => pot x.2) ≤ pot st)
    (oa : OracleComp (unifSpec + QSpec) α) (st : St) (hV : ValidSt st) :
    probExpect ((simulateQ ((QueryImpl.ofLift unifSpec ProbComp).liftTarget
      (StateT St ProbComp) + impl) oa).run st) (fun x => pot x.2) ≤ pot st := by
  let fullImpl := (QueryImpl.ofLift unifSpec ProbComp).liftTarget (StateT St ProbComp) + impl
  induction oa using OracleComp.inductionOn generalizing st with
  | pure _ => simp [StateT.run_pure, probExpect_pure]
  | query_bind q oa ih =>
    cases q with
    | inl uq =>
      have hrun : (simulateQ fullImpl (liftM (OracleSpec.query (Sum.inl uq)) >>= oa)).run st =
          (do let u ← liftM (unifSpec.query uq); (simulateQ fullImpl (oa u)).run st) := by
        simp [fullImpl, simulateQ_bind, QueryImpl.liftTarget, StateT.run_bind, StateT.run_monadLift]
      rw [hrun, probExpect_bind]
      exact probExpect_const_le_of_support _ _ _ (fun u _ => ih u st hV)
    | inr gq =>
      have hrun : (simulateQ fullImpl (liftM (OracleSpec.query (Sum.inr gq)) >>= oa)).run st =
          (do let y ← (impl gq).run st; (simulateQ fullImpl (oa y.1)).run y.2) := by
        simp [fullImpl, simulateQ_bind, StateT.run_bind]
      rw [hrun, probExpect_bind]
      exact (probExpect_mono_of_support _ _ _
        (fun y hy => ih y.1 y.2 (hValid gq st hV y hy))).trans (hStep gq st hV)

private theorem doubleRangeColl_toReal_le {Ω : Type} (upper : Bool) (runSim : ProbComp Ω)
    (bytesOf : Ω → List Bytes) (taggedOf : Ω → List (Nat × Bytes))
    (pairColl : List (Nat × Bytes) → Nat → Nat → Bool)
    (N exp2 : Nat) (pFixed : ℝ) (hp_nn : 0 ≤ pFixed) (hp_eq : pFixed = 1 / (2 : ℝ) ^ exp2)
    (hDom : ∀ x ∈ support runSim, hasDuplicateBytes (bytesOf x) = true →
      (List.range N).any (fun i => (List.range N).any (fun j => pairColl (taggedOf x) i j)) = true)
    (hEnn : ∀ i j, (if upper = true then i < j else j < i) →
      𝒟[runSim >>= fun x => pure (pairColl (taggedOf x) i j)] {true} ≤ ENNReal.ofReal pFixed)
    (hZero : ∀ i j, ¬ (if upper = true then i < j else j < i) →
      ∀ x ∈ support runSim, pairColl (taggedOf x) i j = false) :
    (𝒟[runSim >>= fun x => pure (hasDuplicateBytes (bytesOf x))] {true}).toReal ≤
      ((N * (N - 1) : ℕ) : ℝ) / (2 : ℝ) ^ (exp2 + 1) := by
  have hPair_le : ∀ i j : Nat,
      (𝒟[runSim >>= fun x => pure (pairColl (taggedOf x) i j)] {true}).toReal ≤
      if (if upper = true then i < j else j < i) then pFixed else 0 := by
    intro i j
    by_cases hlt : (if upper = true then i < j else j < i)
    · simp only [hlt, ↓reduceIte]
      have hreal := (ENNReal.toReal_le_toReal
        (MeasureTheory.measure_ne_top _ _) ENNReal.ofReal_ne_top).mpr (hEnn i j hlt)
      rwa [ENNReal.toReal_ofReal hp_nn] at hreal
    · have h0 : 𝒟[runSim >>= fun x => pure (pairColl (taggedOf x) i j)] {true} ≤ 0 := by
        rw [evalDist_bind_true_eq_probExpect]
        exact probExpect_const_le_of_support _ _ 0 (fun x hx => by simp [hZero i j hlt x hx])
      simp only [le_antisymm h0 zero_le, hlt, ↓reduceIte, ENNReal.toReal_zero, le_rfl]
  calc (𝒟[runSim >>= fun x => pure (hasDuplicateBytes (bytesOf x))] {true}).toReal
      ≤ (𝒟[runSim >>= fun x =>
          pure ((List.range N).any (fun i => (List.range N).any (fun j =>
            pairColl (taggedOf x) i j)))] {true}).toReal :=
        toReal_bind_bool_mono_of_support runSim _ _ hDom
    _ ≤ ∑ i ∈ Finset.range N, ∑ j ∈ Finset.range N,
          (𝒟[runSim >>= fun x => pure (pairColl (taggedOf x) i j)] {true}).toReal :=
        (toReal_any_range_le_sum runSim N
          (fun i x => (List.range N).any (fun j => pairColl (taggedOf x) i j))).trans
          (Finset.sum_le_sum fun i _ => toReal_any_range_le_sum runSim N
            (fun j x => pairColl (taggedOf x) i j))
    _ ≤ ∑ i ∈ Finset.range N, ∑ j ∈ Finset.range N,
          if (if upper = true then i < j else j < i) then pFixed else 0 :=
        Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => hPair_le i j
    _ = ((N * (N - 1) : ℕ) : ℝ) / (2 : ℝ) ^ (exp2 + 1) := by
        cases upper
        · simp only [Bool.false_eq_true, ↓reduceIte]
          rw [sum_lt_range_const, hp_eq, pow_succ]; ring
        · simp only [↓reduceIte]
          rw [Finset.sum_comm, sum_lt_range_const, hp_eq, pow_succ]; ring

private noncomputable def kemActivePairPotential (tagged : List (Nat × Bytes)) (b1 b2 : Nat) :
    ENNReal :=
  if b1 < b2 then
    match tagged.find? (fun p => p.1 == b1), tagged.find? (fun p => p.1 == b2) with
    | some (_, pk1), some (_, pk2) => 𝒟[(pure (pk1 == pk2) : ProbComp Bool)] {true}
    | _, _ => ENNReal.ofReal Pfixed_pk_kem
  else 0

private theorem evalDist_hasUpperTaggedPairCollAt_le_kemPotential
    (tagged : List (Nat × Bytes)) (b1 b2 : Nat) :
    𝒟[(pure (hasUpperTaggedPairCollAt tagged b1 b2) : ProbComp Bool)] {true} ≤
      kemActivePairPotential tagged b1 b2 := by
  unfold hasUpperTaggedPairCollAt kemActivePairPotential
  by_cases hlt : b1 < b2
  · simp only [hlt, decide_true, Bool.true_and, ↓reduceIte]
    cases tagged.find? (fun p => p.1 == b1) with
    | none => simp
    | some p1 =>
      rcases p1 with ⟨_, _⟩
      cases tagged.find? (fun p => p.1 == b2) with
      | none => simp
      | some p2 => rcases p2 with ⟨_, _⟩; exact le_rfl
  · simp [hlt]

private theorem kemActivePairPotential_nil_le (b1 b2 : Nat) :
    kemActivePairPotential [] b1 b2 ≤ ENNReal.ofReal Pfixed_pk_kem := by
  unfold kemActivePairPotential; split_ifs <;> simp

private theorem probExpect_kemActivePairPotential_cons_fresh_le (P : Primitives)
    (hP : CryptoWellFormedPrimitivesδ P) (tagged : List (Nat × Bytes)) (sNew b1 b2 : Nat)
    (hFresh : sNew ∉ tagged.map Prod.fst) :
    probExpect (sampleKemKeyGen P)
      (fun pair => kemActivePairPotential ((sNew, pair.1) :: tagged) b1 b2) ≤
      kemActivePairPotential tagged b1 b2 := by
  have hFresh' : sNew ∉ ([] ++ tagged).map Prod.fst := by simpa using hFresh
  unfold kemActivePairPotential
  by_cases hlt : b1 < b2
  · simp only [hlt, ↓reduceIte]
    have h_ins : ∀ (pk : Bytes) (s : Nat),
        (((sNew, pk) :: tagged).find? (fun p => p.1 == s)) =
        if sNew == s then some (sNew, pk) else tagged.find? (fun p => p.1 == s) :=
      fun pk s => find?_insert_fresh [] tagged sNew pk s hFresh'
    simp_rw [h_ins]
    by_cases hs1 : (sNew == b1) = true
    · have heq1 : sNew = b1 := beq_iff_eq.mp hs1
      have hs2 : (sNew == b2) = false := by rw [beq_eq_false_iff_ne]; omega
      have hnone1 := find?_fst_none_of_not_mem tagged b1 (heq1 ▸ hFresh)
      simp only [hs1, hs2, hnone1, ↓reduceIte, Bool.false_eq_true]
      cases tagged.find? (fun p => p.1 == b2) with
      | none => simp [probExpect_const]
      | some p2 => rcases p2 with ⟨_, pk2⟩; exact probExpect_sampleKemKeyGen_coll_le P hP pk2
    · simp only [Bool.not_eq_true] at hs1
      by_cases hs2 : (sNew == b2) = true
      · have heq2 : sNew = b2 := beq_iff_eq.mp hs2
        have hnone2 := find?_fst_none_of_not_mem tagged b2 (heq2 ▸ hFresh)
        simp only [hs1, hs2, hnone2, ↓reduceIte, Bool.false_eq_true]
        cases tagged.find? (fun p => p.1 == b1) with
        | none => simp [probExpect_const]
        | some p1 =>
          rcases p1 with ⟨_, pk1⟩
          have h_comm : ∀ pair : Bytes × Bytes, ((pk1 == pair.1) : Bool) = (pair.1 == pk1) :=
            fun _ => Bool.beq_comm
          simp_rw [h_comm]; exact probExpect_sampleKemKeyGen_coll_le P hP pk1
      · simp only [Bool.not_eq_true] at hs2
        simp only [hs1, hs2, Bool.false_eq_true, ↓reduceIte, probExpect_const, le_rfl]
  · simp [hlt, probExpect_const]

private def kemTaggedActive {S : Setup} (st : KeyIndState S) : List (Nat × Bytes) :=
  tagByCreation (fun (_, b) => b.pqspkPk) st.spkBundles

private theorem pqxdhKeyIndImpl1KeyRo_activeKem_step (S : Setup) (P : Primitives)
    (hP : CryptoWellFormedPrimitivesδ P) (b1 b2 : Nat)
    (q : KeyIndQuery S) (st : KeyIndState S) :
    probExpect ((pqxdhKeyIndImpl1KeyRo S P q).run st)
      (fun x => kemActivePairPotential (kemTaggedActive x.2) b1 b2) ≤
      kemActivePairPotential (kemTaggedActive st) b1 b2 := by
  cases q with
  | initPrin u =>
    exact probExpect_const_le_of_support _ _ _ (fun x hx => by
      simp [kemTaggedActive, pqxdhKeyIndImpl1KeyRo_initPrin_preserves_spkBundles S P u st x hx])
  | genSPK u j =>
    change probExpect ((pqxdhKeyIndImpl true S P (.genSPK u j)).run st) _ ≤ _
    unfold pqxdhKeyIndImpl; dsimp only
    simp only [StateT.run_bind, StateT.run_get, pure_bind]
    cases st.spkBundles.any (fun (k, _) => k == (u.val, j.val)) with
    | true => simp [StateT.run_pure, probExpect_pure]
    | false =>
      simp only [Bool.false_eq_true, ↓reduceIte]
      cases st.principals.find? (fun (idx, _) => idx == u.val) with
      | none => simp [StateT.run_pure, probExpect_pure]
      | some uPair =>
        rcases uPair with ⟨_, _⟩; dsimp only
        simp only [StateT.run_bind, StateT.run_monadLift, monadLift_self, StateT.run_set,
          StateT.run_pure, bind_assoc, pure_bind, probExpect_bind, probExpect_pure]
        apply probExpect_const_le_of_support; intro _ _
        apply probExpect_const_le_of_support; intro _ _
        refine (probExpect_mono_of_support (sampleKemKeyGen P) _
          (fun pair => kemActivePairPotential
            ((st.spkBundles.length, pair.1) :: kemTaggedActive st) b1 b2) ?_).trans
          (probExpect_kemActivePairPotential_cons_fresh_le P hP (kemTaggedActive st)
            st.spkBundles.length b1 b2 (not_mem_fst_tagByCreation_length _ _))
        intro pair _
        exact probExpect_const_le_of_support _ _ _ (fun _ _ => by simp [kemTaggedActive])
  | revealSpkSk u j =>
    refine probExpect_const_le_of_support _ _ _ (fun x hx => ?_)
    rcases mem_support_pqxdhKeyIndImpl true S P (.revealSpkSk u j) st x hx with h | h
    · simp [h]
    · simp only [kemTaggedActive, h]
      rw [tagByCreation_map_congr (fun p : (Nat × Nat) × SpkBundleEntry => p.2.pqspkPk) _
        (fun _ => by split_ifs <;> rfl)]
  | _ =>
    exact probExpect_const_le_of_support _ _ _ (fun x hx => by
      simp [kemTaggedActive, pqxdhKeyIndImpl_preserves_spkBundles_nonGen true P _ st
        (fun _ _ h => by cases h) (fun _ _ h => by cases h) x hx])

/-- Active-count ML-KEM-1024 public-key collision bound in one-key `KeyInd`. -/
theorem kemCollProbKeyInd1Key_active_le (S : Setup) (P : Primitives)
    (hP : CryptoWellFormedPrimitivesδ P) (b : QueryBudget)
    (A : BoundedAdv (KeyIndAdversary S) b) :
    kemCollProbKeyInd1Key S P A.1 ≤
      let n_spk := activeSpkCount S b.q_on
      ((n_spk * (n_spk - 1) : ℕ) : ℝ) / (2 : ℝ) ^ 256 := by
  dsimp only
  unfold kemCollProbKeyInd1Key hasKemPkCollisionKeyInd
  refine doubleRangeColl_toReal_le true (runKeyInd1KeySim S P A.1)
    (fun x => allHonestKemPksKeyInd x.2.2) (fun x => kemTaggedActive x.2.2)
    hasUpperTaggedPairCollAt (activeSpkCount S b.q_on) 255 Pfixed_pk_kem pfixed_pk_kem_nonneg
    (by unfold Pfixed_pk_kem; ring) (fun x hx hdup => ?_) (fun b1 b2 _ => ?_) (fun b1 b2 hlt _ _ => ?_)
  · have hAct := runKeyInd1KeySim_mem_support_activeBounded S P b A x.1 x.2.1 x.2.2 hx
    have hV := validTaggedPks_tagByCreation
      (fun p : (Nat × Nat) × SpkBundleEntry => p.2.pqspkPk) x.2.2.spkBundles hAct.spkBundles_le
    have hdup' : hasDuplicateBytes ((kemTaggedActive x.2.2).map Prod.snd) = true := by
      simpa [kemTaggedActive, map_snd_tagByCreation, allHonestKemPksKeyInd,
        HasKeyIndState.toKeyIndState] using hdup
    exact hasDuplicateBytes_map_snd_imp_any_upper_double_range _ _ hV hdup'
  · rw [evalDist_bind_true_eq_probExpect]
    simp only [runKeyInd1KeySim, probExpect_bind, probExpect_pure]
    apply probExpect_const_le_of_support; intro secb _
    refine (probExpect_mono_of_support _ _ _
      (fun x _ => evalDist_hasUpperTaggedPairCollAt_le_kemPotential _ b1 b2)).trans ?_
    exact (simulateQ_potential_le (fun _ => True)
      (fun st => kemActivePairPotential (kemTaggedActive st) b1 b2)
      (pqxdhKeyIndImpl1KeyRo S P) (fun _ _ _ _ _ => trivial)
      (fun q st _ => pqxdhKeyIndImpl1KeyRo_activeKem_step S P hP b1 b2 q st)
      A.1.run (KeyIndState.empty S secb) trivial).trans (kemActivePairPotential_nil_le b1 b2)
  · simp only [↓reduceIte] at hlt; simp [hasUpperTaggedPairCollAt, hlt]

/-- Active-count `G2 -> G2_1` ML-KEM-1024 birthday collision hop. -/
theorem keyInd1Key_hop_G2_G2_1_active_le (S : Setup) (P : Primitives)
    (hP : CryptoWellFormedPrimitivesδ P) (b : QueryBudget)
    (A : BoundedAdv (KeyIndAdversary S) b) :
    |keyInd1KeyAdvG2 S P A.1 - keyInd1KeyAdvG2_1 S P A.1| ≤
      let n_spk := activeSpkCount S b.q_on
      ((n_spk * (n_spk - 1) : ℕ) : ℝ) / (2 : ℝ) ^ 256 :=
  (keyInd1Key_hop_G2_G2_1_le_prob S P A.1).trans (kemCollProbKeyInd1Key_active_le S P hP b A)

theorem keyInd1Key_hop_G2_G2_5_active_le (S : Setup) (P : Primitives)
    (hP : CryptoWellFormedPrimitivesδ P) (b : QueryBudget)
    (A : BoundedAdv (KeyIndAdversary S) b) :
    |keyInd1KeyAdvG2 S P A.1 - keyInd1KeyAdvG2_5 S P A.1| ≤
      let n_spk := activeSpkCount S b.q_on
      ((n_spk * (n_spk - 1) : ℕ) : ℝ) / (2 : ℝ) ^ 256 :=
  keyInd1Key_hop_G2_G2_1_active_le S P hP b A

/-! ## Active X25519 and initiator `dh2` birthday collision hops -/

private theorem mem_support_pqxdhKeyIndImpl1KeyRo_initPrin (S : Setup) (P : Primitives)
    (u : Fin S.N_id) (st : KeyIndState S) (x : KeyIndResponse × KeyIndState S)
    (hx : x ∈ support ((pqxdhKeyIndImpl1KeyRo S P (.initPrin u)).run st)) :
    x.2 = st ∨ (st.principals.any (fun (idx, _) => idx == u.val) = false ∧
      ∃ sk, x.2 = { st with principals := (u.val,
        { secIKA0 := sk, ikAPk := P.x25519Base sk, secIKAsign := sk,
          ikSignPk := P.x25519Base sk, corrupted := false }) :: st.principals }) := by
  unfold pqxdhKeyIndImpl1KeyRo pqxdhKeyIndImpl1KeyReal at hx; dsimp only at hx
  simp only [StateT.run_bind, StateT.run_get, pure_bind] at hx
  cases hF : st.principals.any (fun (idx, _) => idx == u.val) with
  | true =>
    rw [hF] at hx; simp only [↓reduceIte, StateT.run_pure, support_pure,
      Set.mem_singleton_iff] at hx; subst hx; exact Or.inl rfl
  | false =>
    rw [hF] at hx; simp only [Bool.false_eq_true, ↓reduceIte, StateT.run_bind, StateT.run_monadLift,
      monadLift_self, StateT.run_set, StateT.run_pure, bind_assoc, pure_bind,
      MonadAttach.mem_support_bind, support_pure, Set.mem_singleton_iff] at hx
    rcases hx with ⟨sk, _, rfl⟩; exact Or.inr ⟨rfl, sk, rfl⟩

private theorem probExpect_runKeyIndInitiate_le {S : Setup} (P : Primitives)
    (sid : SessionId S) (u : Fin S.N_id) (bundle : PreKeyBundleInput) (st : KeyIndState S)
    (pot : KeyIndState S → ENNReal) (stepPot : Bytes → ENNReal)
    (hMatch : ∀ (ekASk : Bytes) (eNew : KeyIndInitiatorEntry S) (rc : _),
      eNew.ekASk = ekASk → eNew.peerIkPk = bundle.ikB → eNew.hdr.ekAPk = P.x25519Base ekASk →
      pot { st with sessions := eNew :: st.sessions, roCache := rc } ≤ stepPot ekASk)
    (hSample :
      (!koskBundleOk P st.principals st.spkBundles st.opkEntries st.advKeys bundle) = false →
      probExpect sampleScalar32 stepPot ≤ pot st) :
    probExpect ((runKeyIndInitiate true S P sid u bundle).run st) (fun x => pot x.2) ≤ pot st := by
  unfold runKeyIndInitiate; dsimp only
  simp only [StateT.run_bind, StateT.run_get, pure_bind]
  cases st.sessions.any (fun e => e.sid == sid) with
  | true => simp [StateT.run_pure, probExpect_pure]
  | false =>
    simp only [Bool.false_eq_true, ↓reduceIte]
    cases st.principals.find? (fun (idx, _) => idx == u.val) with
    | none => simp [StateT.run_pure, probExpect_pure]
    | some p =>
      rcases p with ⟨_, _⟩; dsimp only
      cases hKosk : !koskBundleOk P st.principals st.spkBundles st.opkEntries st.advKeys bundle with
      | true => simp [StateT.run_pure, probExpect_pure]
      | false =>
        simp only [Bool.false_eq_true, ↓reduceIte, StateT.run_bind, StateT.run_monadLift,
          monadLift_self, bind_assoc, pure_bind]
        cases !(P.sigVerify (resolveSigPk P st.principals bundle.ikB) (encodeEC bundle.spkB)
            bundle.spkSig &&
            P.sigVerify (resolveSigPk P st.principals bundle.ikB) (encodeKEM bundle.pqspkB)
            bundle.pqspkSig) with
        | true =>
          simp only [↓reduceIte, StateT.run_pure, probExpect_bind, probExpect_pure]
          apply probExpect_const_le_of_support; intro _ _
          exact probExpect_const_le_of_support _ _ _ (fun _ _ => le_rfl)
        | false =>
          simp only [Bool.false_eq_true, ↓reduceIte, probExpect_bind]
          rw [probExpect_swap sampleScalar32 sampleCoins32]
          apply probExpect_const_le_of_support; intro kemCoins _
          cases P.kemEncaps bundle.pqspkB kemCoins with
          | none =>
            simp only [StateT.run_pure, probExpect_pure]
            exact probExpect_const_le_of_support _ _ _ (fun _ _ => le_rfl)
          | some val =>
            rcases val with ⟨_, _⟩; dsimp only
            refine (probExpect_mono_of_support sampleScalar32 _ stepPot ?_).trans (hSample hKosk)
            intro ekASk _
            apply probExpect_const_le_of_support; intro x hx
            simp only [StateT.run_bind, StateT.run_monadLift, monadLift_self,
              bind_assoc, pure_bind, MonadAttach.mem_support_bind] at hx
            rcases hx with ⟨⟨_, _⟩, _, hx⟩
            split at hx <;>
              simp only [StateT.run_bind, StateT.run_monadLift, monadLift_self, StateT.run_set,
                bind_assoc, pure_bind, MonadAttach.mem_support_bind] at hx
            swap; rcases hx with ⟨_, _, hx⟩; all_goals
            cases hHon : SignalPqxdh.findHonestPrincipal P st.principals bundle.ikB <;> (
              rw [hHon] at hx
              simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff] at hx
              subst hx; dsimp only; apply hMatch <;> rfl)

private def dh2TaggedActive {S : Setup} (P : Primitives) (st : KeyIndState S) :
    List (Nat × Bytes) :=
  tagByCreation (fun s : KeyIndInitiatorEntry S => P.x25519 s.ekASk s.peerIkPk) st.sessions

private theorem runKeyIndInitiate_activeDh2_step (S : Setup) (P : Primitives)
    (hP : CryptoWellFormedPrimitivesδ P) (sid : SessionId S) (u : Fin S.N_id)
    (bundle : PreKeyBundleInput) (st : KeyIndState S) (s1 s2 : Nat)
    (hV : ValidKeyIndDh2 S P st) :
    probExpect ((runKeyIndInitiate true S P sid u bundle).run st)
      (fun x => dh2UpperPairPotential (dh2TaggedActive P x.2) s1 s2) ≤
      dh2UpperPairPotential (dh2TaggedActive P st) s1 s2 := by
  exact probExpect_runKeyIndInitiate_le P sid u bundle st
    (fun st' => dh2UpperPairPotential (dh2TaggedActive P st') s1 s2)
    (fun ekASk => dh2UpperPairPotential
      ((st.sessions.length, P.x25519 ekASk bundle.ikB) :: dh2TaggedActive P st) s1 s2)
    (fun _ _ _ h1 h2 _ => by simp [dh2TaggedActive, h1, h2])
    (fun hKosk => by
      rcases exists_skB_of_koskBundleOk P st.principals st.spkBundles st.opkEntries
        st.advKeys bundle hV.2.1 hV.2.2 hKosk with ⟨skB, hSkB, hPowB⟩
      exact probExpect_dh2UpperPairPotential_cons_fresh_le P hP (dh2TaggedActive P st)
        st.sessions.length bundle.ikB skB hSkB hPowB s1 s2 (not_mem_fst_tagByCreation_length _ _))

private theorem pqxdhKeyIndImpl1KeyRo_activeDh2_step (S : Setup) (P : Primitives)
    (hP : CryptoWellFormedPrimitivesδ P) (s1 s2 : Nat)
    (q : KeyIndQuery S) (st : KeyIndState S) (hV : ValidKeyIndDh2 S P st) :
    probExpect ((pqxdhKeyIndImpl1KeyRo S P q).run st)
      (fun x => dh2UpperPairPotential (dh2TaggedActive P x.2) s1 s2) ≤
      dh2UpperPairPotential (dh2TaggedActive P st) s1 s2 := by
  have hNonInit : ∀ {q' : KeyIndQuery S} (x : (keyIndSpec S).Range q' × KeyIndState S),
      x ∈ support ((pqxdhKeyIndImpl true S P q').run st) →
      (∀ u i b, q' ≠ .initiateOPK u i b) → (∀ u i b, q' ≠ .initiateNoOPK u i b) →
      dh2TaggedActive P x.2 = dh2TaggedActive P st := by
    intro q' x hx h1 h2
    have hsh := mem_support_pqxdhKeyIndImpl true S P q' st x hx
    cases q' with
    | initiateOPK u i b => exact False.elim (h1 u i b rfl)
    | initiateNoOPK u i b => exact False.elim (h2 u i b rfl)
    | testSession _ | revealSessionKey _ =>
      let fn := fun s : KeyIndInitiatorEntry S => P.x25519 s.ekASk s.peerIkPk
      have hm : x.2.sessions.map fn = st.sessions.map fn := by
        simpa [fn, List.map_map, Function.comp_def] using
          congrArg (List.map (fun t => P.x25519 t.2.1 t.2.2.1)) hsh.2.2.2
      rw [dh2TaggedActive, dh2TaggedActive, tagByCreation_eq_id_map fn,
        tagByCreation_eq_id_map fn, hm]
    | initPrin _ =>
      rcases hsh with h | ⟨_, _, _, h⟩ <;> simp [dh2TaggedActive, h]
    | genSPK _ _ =>
      rcases hsh with h | ⟨_, _, _, _, _, _, h⟩ <;> simp [dh2TaggedActive, h]
    | genOPK _ _ _ =>
      rcases hsh with h | ⟨_, _, h⟩ <;> simp [dh2TaggedActive, h]
    | corruptIK _ | revealSpkSk _ =>
      rcases hsh with h | h <;> simp [dh2TaggedActive, h]
    | acceptOPK _ _ _ _ => simp [dh2TaggedActive, hsh.2.2.1]
    | acceptNoOPK _ _ _ _ | roQuery _ | registerKey _ | revealDhSecrets =>
      simp [dh2TaggedActive, hsh.2.2.2]
  cases q with
  | initPrin u =>
    exact probExpect_const_le_of_support _ _ _ (fun x hx => by
      rcases mem_support_pqxdhKeyIndImpl1KeyRo_initPrin S P u st x hx with h | ⟨_, _, h⟩ <;>
        simp [dh2TaggedActive, h])
  | initiateOPK u i bundle =>
    change probExpect ((pqxdhKeyIndImpl true S P (.initiateOPK u i bundle)).run st) _ ≤ _
    unfold pqxdhKeyIndImpl; dsimp only; simp only [StateT.run_bind, StateT.run_get, pure_bind]
    cases bundle.opkB?.isNone with
    | true => simp [StateT.run_pure, probExpect_pure]
    | false =>
      simp only [Bool.false_eq_true, ↓reduceIte]
      exact runKeyIndInitiate_activeDh2_step S P hP (.sendOPK u i) u bundle st s1 s2 hV
  | initiateNoOPK u i bundle =>
    change probExpect ((pqxdhKeyIndImpl true S P (.initiateNoOPK u i bundle)).run st) _ ≤ _
    unfold pqxdhKeyIndImpl; dsimp only; simp only [StateT.run_bind, StateT.run_get, pure_bind]
    cases bundle.opkB?.isSome with
    | true => simp [StateT.run_pure, probExpect_pure]
    | false =>
      simp only [Bool.false_eq_true, ↓reduceIte]
      exact runKeyIndInitiate_activeDh2_step S P hP (.sendNoOPK u i) u bundle st s1 s2 hV
  | _ =>
    exact probExpect_const_le_of_support _ _ _ (fun x hx => by
      rw [hNonInit x hx (fun _ _ _ h => by cases h) (fun _ _ _ h => by cases h)])

private theorem dh2CollProbKeyInd1Key_active_le (S : Setup) (P : Primitives)
    (hP : CryptoWellFormedPrimitivesδ P) (b : QueryBudget)
    (A : BoundedAdv (KeyIndAdversary S) b) :
    (𝒟[runKeyInd1KeySim S P A.1 >>= fun (_, _, finalSt) =>
      pure (hasDuplicateBytes (allInitDh2sKeyInd P finalSt))] {true}).toReal ≤
      let n_send := activeSendCount S b.q_on
      ((n_send * (n_send - 1) : ℕ) : ℝ) / (2 : ℝ) ^ 251 := by
  dsimp only
  refine doubleRangeColl_toReal_le true (runKeyInd1KeySim S P A.1)
    (fun x => allInitDh2sKeyInd P x.2.2) (fun x => dh2TaggedActive P x.2.2)
    hasUpperTaggedPairCollAt (activeSendCount S b.q_on) 250 Pfixed_pk_ec pfixed_pk_ec_nonneg
    (by unfold Pfixed_pk_ec; ring) (fun x hx hdup => ?_) (fun s1 s2 _ => ?_) (fun s1 s2 hlt _ _ => ?_)
  · have hAct := runKeyInd1KeySim_mem_support_activeBounded S P b A x.1 x.2.1 x.2.2 hx
    have hV := validTaggedPks_tagByCreation
      (fun s : KeyIndInitiatorEntry S => P.x25519 s.ekASk s.peerIkPk)
      x.2.2.sessions hAct.sessions_le
    have hdup' : hasDuplicateBytes ((dh2TaggedActive P x.2.2).map Prod.snd) = true := by
      simpa [dh2TaggedActive, map_snd_tagByCreation, allInitDh2sKeyInd,
        HasKeyIndState.toKeyIndState] using hdup
    exact hasDuplicateBytes_map_snd_imp_any_upper_double_range _ _ hV hdup'
  · rw [evalDist_bind_true_eq_probExpect]
    simp only [runKeyInd1KeySim, probExpect_bind, probExpect_pure]
    apply probExpect_const_le_of_support; intro secb _
    refine (probExpect_mono_of_support _ _ _
      (fun x _ => evalDist_hasUpperTaggedPairCollAt_le_potential _ s1 s2)).trans ?_
    exact (simulateQ_potential_le (ValidKeyIndDh2 S P)
      (fun st => dh2UpperPairPotential (dh2TaggedActive P st) s1 s2)
      (pqxdhKeyIndImpl1KeyRo S P)
      (fun q st hV => (pqxdhKeyIndImpl1KeyRo_dh2_step S P hP q st 0 0 hV).1)
      (fun q st hV => pqxdhKeyIndImpl1KeyRo_activeDh2_step S P hP s1 s2 q st hV)
      A.1.run (KeyIndState.empty S secb) (validKeyIndDh2_empty S P secb)).trans
      (dh2UpperPairPotential_nil_le s1 s2)
  · simp only [↓reduceIte] at hlt; simp [hasUpperTaggedPairCollAt, hlt]

private theorem hasDuplicateBytes_eq_false_iff_nodup :
    ∀ (L : List Bytes), hasDuplicateBytes L = false ↔ L.Nodup := by
  intro L; induction L with
  | nil => simp [hasDuplicateBytes]
  | cons _ xs ih => simp [hasDuplicateBytes, List.nodup_cons, ih]

private theorem hasDuplicateBytes_of_perm {L1 L2 : List Bytes} (h : List.Perm L1 L2) :
    hasDuplicateBytes L1 = hasDuplicateBytes L2 := by
  cases h2 : hasDuplicateBytes L2 with
  | false =>
    exact (hasDuplicateBytes_eq_false_iff_nodup L1).mpr
      (h.nodup_iff.mpr ((hasDuplicateBytes_eq_false_iff_nodup L2).mp h2))
  | true =>
    by_contra hne
    have h1 : hasDuplicateBytes L1 = false := Bool.eq_false_iff.mpr hne
    have h2' := (hasDuplicateBytes_eq_false_iff_nodup L2).mpr
      (h.symm.nodup_iff.mpr ((hasDuplicateBytes_eq_false_iff_nodup L1).mp h1))
    rw [h2'] at h2; cases h2

private theorem perm_cons_append_middle {α : Type} (a : α) (L1 L2 : List α) :
    List.Perm (a :: (L1 ++ L2)) (L1 ++ a :: L2) := by
  first | exact List.perm_middle | exact List.perm_middle.symm

private def stepEcLog {S : Setup} (P : Primitives) (q : KeyIndQuery S)
    (st st' : KeyIndState S) (ecLog : List Bytes) : List Bytes :=
  match q with
  | .initPrin _ =>
    if st.principals.length < st'.principals.length then
      match st'.principals with | (_, e) :: _ => P.pow8 e.ikAPk :: ecLog | [] => ecLog
    else ecLog
  | .genSPK _ _ =>
    if st.spkBundles.length < st'.spkBundles.length then
      match st'.spkBundles with | (_, b) :: _ => P.pow8 b.spkPk :: ecLog | [] => ecLog
    else ecLog
  | .genOPK _ _ _ =>
    if st.opkEntries.length < st'.opkEntries.length then
      match st'.opkEntries with | (_, o) :: _ => P.pow8 o.opkPk :: ecLog | [] => ecLog
    else ecLog
  | .initiateOPK _ _ _ | .initiateNoOPK _ _ _ =>
    if st.sessions.length < st'.sessions.length then
      match st'.sessions with | s :: _ => P.pow8 s.hdr.ekAPk :: ecLog | [] => ecLog
    else ecLog
  | _ => ecLog

private def pqxdhKeyIndImpl1KeyRoEcLog (S : Setup) (P : Primitives) :
    QueryImpl (keyIndSpec S) (StateT (KeyIndState S × List Bytes) ProbComp) :=
  fun q => StateT.mk fun (st, ecLog) => do
    let (resp, st') ← (pqxdhKeyIndImpl1KeyRo S P q).run st
    return (resp, (st', stepEcLog P q st st' ecLog))

private theorem map_fst_fullKeyInd1KeyEcLogImpl (S : Setup) (P : Primitives)
    (t : Sum Nat (KeyIndQuery S)) (p : KeyIndState S × List Bytes) :
    (Prod.map id Prod.fst <$>
      (((QueryImpl.ofLift unifSpec ProbComp).liftTarget
        (StateT (KeyIndState S × List Bytes) ProbComp) +
        pqxdhKeyIndImpl1KeyRoEcLog S P) t).run p) =
    (((QueryImpl.ofLift unifSpec ProbComp).liftTarget
      (StateT (KeyIndState S) ProbComp) + pqxdhKeyIndImpl1KeyRo S P) t).run p.1 := by
  rcases p with ⟨st, ecLog⟩
  cases t <;> simp [pqxdhKeyIndImpl1KeyRoEcLog, QueryImpl.liftTarget, StateT.run_mk,
    StateT.run_monadLift, map_eq_bind_pure_comp, bind_assoc]

private theorem pqxdhKeyIndImpl1KeyRoEcLog_perm (S : Setup) (P : Primitives)
    (q : KeyIndQuery S) (st : KeyIndState S) (ecLog : List Bytes)
    (hPerm : List.Perm ecLog (allHonestEcPksKeyInd P st)) :
    ∀ x ∈ support ((pqxdhKeyIndImpl1KeyRoEcLog S P q).run (st, ecLog)),
      List.Perm x.2.2 (allHonestEcPksKeyInd P x.2.1) := by
  intro x hx
  simp only [pqxdhKeyIndImpl1KeyRoEcLog, StateT.run_mk, MonadAttach.mem_support_bind,
    support_pure, Set.mem_singleton_iff] at hx
  rcases hx with ⟨⟨resp, st'⟩, hst', rfl⟩; dsimp only
  have hInitSess : ∀ {r : KeyIndResponse} {st'' : KeyIndState S}
      (sid : SessionId S) (u : Fin S.N_id) (bundle : PreKeyBundleInput),
      (r, st'') ∈ support ((runKeyIndInitiate true S P sid u bundle).run st) →
      List.Perm
        (if st.sessions.length < st''.sessions.length then
          match st''.sessions with | s :: _ => P.pow8 s.hdr.ekAPk :: ecLog | [] => ecLog
         else ecLog)
        (allHonestEcPksKeyInd P st'') := by
    intro r st'' sid u bundle hrun
    rcases mem_support_runKeyIndInitiate true S P sid u bundle st (r, st'') hrun with
      hEq | ⟨_, eNew, rc, _, _, _, hEq⟩
    · dsimp only at hEq; subst hEq; simpa using hPerm
    · dsimp only at hEq; subst hEq
      simp only [List.length_cons, Nat.lt_succ_self, ↓reduceIte,
        allHonestEcPksKeyInd, HasKeyIndState.toKeyIndState, List.map_cons]
      exact (hPerm.cons (P.pow8 eNew.hdr.ekAPk)).trans
        (perm_cons_append_middle (P.pow8 eNew.hdr.ekAPk)
          (st.principals.map (fun (_, e) => P.pow8 e.ikAPk) ++
           st.spkBundles.map (fun (_, b) => P.pow8 b.spkPk) ++
           st.opkEntries.map (fun (_, o) => P.pow8 o.opkPk))
          (st.sessions.map (fun s => P.pow8 s.hdr.ekAPk)))
  cases q with
  | initPrin u =>
    rcases mem_support_pqxdhKeyIndImpl1KeyRo_initPrin S P u st (resp, st') hst' with
      hEq | ⟨_, sk, hEq⟩
    · dsimp only at hEq; subst hEq; simpa [stepEcLog] using hPerm
    · dsimp only at hEq; subst hEq
      simpa [stepEcLog, allHonestEcPksKeyInd, HasKeyIndState.toKeyIndState] using
        hPerm.cons (P.pow8 (P.x25519Base sk))
  | genSPK u j =>
    rcases mem_support_pqxdhKeyIndImpl true S P (.genSPK u j) st (resp, st') hst' with
      hEq | ⟨_, spkSk, pqspkPk, pqspkSk, spkSig, pqspkSig, hEq⟩
    · dsimp only at hEq; subst hEq; simpa [stepEcLog] using hPerm
    · dsimp only at hEq; subst hEq
      simp only [stepEcLog, List.length_cons, Nat.lt_succ_self, ↓reduceIte,
        allHonestEcPksKeyInd, HasKeyIndState.toKeyIndState, List.map_cons]
      have hm := perm_cons_append_middle (P.pow8 (P.x25519Base spkSk))
        (st.principals.map (fun (_, e) => P.pow8 e.ikAPk))
        (st.spkBundles.map (fun (_, b) => P.pow8 b.spkPk) ++
         st.opkEntries.map (fun (_, o) => P.pow8 o.opkPk) ++
         st.sessions.map (fun s => P.pow8 s.hdr.ekAPk))
      have hEq : allHonestEcPksKeyInd P st =
          st.principals.map (fun (_, e) => P.pow8 e.ikAPk) ++
          (st.spkBundles.map (fun (_, b) => P.pow8 b.spkPk) ++
           st.opkEntries.map (fun (_, o) => P.pow8 o.opkPk) ++
           st.sessions.map (fun s => P.pow8 s.hdr.ekAPk)) := by
        simp [allHonestEcPksKeyInd, HasKeyIndState.toKeyIndState, List.append_assoc]
      rw [hEq] at hPerm
      simpa [List.append_assoc] using (hPerm.cons (P.pow8 (P.x25519Base spkSk))).trans hm
  | genOPK u j o =>
    rcases mem_support_pqxdhKeyIndImpl true S P (.genOPK u j o) st (resp, st') hst' with
      hEq | ⟨_, opkSk, hEq⟩
    · dsimp only at hEq; subst hEq; simpa [stepEcLog] using hPerm
    · dsimp only at hEq; subst hEq
      simp only [stepEcLog, List.length_cons, Nat.lt_succ_self, ↓reduceIte,
        allHonestEcPksKeyInd, HasKeyIndState.toKeyIndState, List.map_cons]
      have hm := perm_cons_append_middle (P.pow8 (P.x25519Base opkSk))
        (st.principals.map (fun (_, e) => P.pow8 e.ikAPk) ++
         st.spkBundles.map (fun (_, b) => P.pow8 b.spkPk))
        (st.opkEntries.map (fun (_, o) => P.pow8 o.opkPk) ++
         st.sessions.map (fun s => P.pow8 s.hdr.ekAPk))
      have hEq : allHonestEcPksKeyInd P st =
          (st.principals.map (fun (_, e) => P.pow8 e.ikAPk) ++
           st.spkBundles.map (fun (_, b) => P.pow8 b.spkPk)) ++
          (st.opkEntries.map (fun (_, o) => P.pow8 o.opkPk) ++
           st.sessions.map (fun s => P.pow8 s.hdr.ekAPk)) := by
        simp [allHonestEcPksKeyInd, HasKeyIndState.toKeyIndState, List.append_assoc]
      rw [hEq] at hPerm
      simpa [List.append_assoc] using (hPerm.cons (P.pow8 (P.x25519Base opkSk))).trans hm
  | initiateOPK u i bundle =>
    rcases mem_support_pqxdhKeyIndImpl true S P (.initiateOPK u i bundle) st (resp, st') hst' with
      hEq | ⟨_, hrun⟩
    · dsimp only at hEq; subst hEq; simpa [stepEcLog] using hPerm
    · exact hInitSess (.sendOPK u i) u bundle hrun
  | initiateNoOPK u i bundle =>
    rcases mem_support_pqxdhKeyIndImpl true S P (.initiateNoOPK u i bundle) st (resp, st') hst' with
      hEq | ⟨_, hrun⟩
    · dsimp only at hEq; subst hEq; simpa [stepEcLog] using hPerm
    · exact hInitSess (.sendNoOPK u i) u bundle hrun
  | corruptIK u =>
    rcases mem_support_pqxdhKeyIndImpl true S P (.corruptIK u) st (resp, st') hst' with hEq | hEq
    · dsimp only at hEq; subst hEq; simpa [stepEcLog] using hPerm
    · dsimp only at hEq; subst hEq
      have hm : (st.principals.map (fun (idx, e) =>
          if idx == u.val then (idx, { e with corrupted := true }) else (idx, e))).map
          (fun (_, e) => P.pow8 e.ikAPk) = st.principals.map (fun (_, e) => P.pow8 e.ikAPk) := by
        rw [List.map_map]; refine List.map_congr_left fun p _ => ?_
        rcases p with ⟨_, _⟩; dsimp only [Function.comp_def]; split_ifs <;> rfl
      dsimp only [stepEcLog, allHonestEcPksKeyInd, HasKeyIndState.toKeyIndState]
      rw [hm]; exact hPerm
  | revealSpkSk u j =>
    rcases mem_support_pqxdhKeyIndImpl true S P (.revealSpkSk u j) st (resp, st') hst' with hEq | hEq
    · dsimp only at hEq; subst hEq; simpa [stepEcLog] using hPerm
    · dsimp only at hEq; subst hEq
      have hm : (st.spkBundles.map (fun (idx, b) =>
          if idx == (u.val, j.val) then (idx, { b with revealed := true }) else (idx, b))).map
          (fun (_, b) => P.pow8 b.spkPk) = st.spkBundles.map (fun (_, b) => P.pow8 b.spkPk) := by
        rw [List.map_map]; refine List.map_congr_left fun p _ => ?_
        rcases p with ⟨_, _⟩; dsimp only [Function.comp_def]; split_ifs <;> rfl
      dsimp only [stepEcLog, allHonestEcPksKeyInd, HasKeyIndState.toKeyIndState]
      rw [hm]; exact hPerm
  | acceptOPK u j bundle hdr =>
    rcases mem_support_pqxdhKeyIndImpl true S P (.acceptOPK u j bundle hdr) st (resp, st') hst' with
      ⟨h1, h2, h3, h4⟩
    dsimp only at h1 h2 h3 h4
    have hm : st'.opkEntries.map (fun (_, o) => P.pow8 o.opkPk) =
        st.opkEntries.map (fun (_, o) => P.pow8 o.opkPk) := by
      simpa [List.map_map, Function.comp_def] using congrArg (List.map (fun p => P.pow8 p.2)) h4
    simpa [stepEcLog, allHonestEcPksKeyInd, HasKeyIndState.toKeyIndState, h1, h2, h3, hm] using hPerm
  | testSession sid =>
    rcases mem_support_pqxdhKeyIndImpl true S P (.testSession sid) st (resp, st') hst' with
      ⟨h1, h2, h3, h4⟩
    dsimp only at h1 h2 h3 h4
    have hm : st'.sessions.map (fun s => P.pow8 s.hdr.ekAPk) =
        st.sessions.map (fun s => P.pow8 s.hdr.ekAPk) := by
      simpa [List.map_map, Function.comp_def] using
        congrArg (List.map (fun t => P.pow8 t.2.2.2.2.ekAPk)) h4
    simpa [stepEcLog, allHonestEcPksKeyInd, HasKeyIndState.toKeyIndState, h1, h2, h3, hm] using hPerm
  | revealSessionKey sid =>
    rcases mem_support_pqxdhKeyIndImpl true S P (.revealSessionKey sid) st (resp, st') hst' with
      ⟨h1, h2, h3, h4⟩
    dsimp only at h1 h2 h3 h4
    have hm : st'.sessions.map (fun s => P.pow8 s.hdr.ekAPk) =
        st.sessions.map (fun s => P.pow8 s.hdr.ekAPk) := by
      simpa [List.map_map, Function.comp_def] using
        congrArg (List.map (fun t => P.pow8 t.2.2.2.2.ekAPk)) h4
    simpa [stepEcLog, allHonestEcPksKeyInd, HasKeyIndState.toKeyIndState, h1, h2, h3, hm] using hPerm
  | acceptNoOPK u j bundle hdr =>
    rcases mem_support_pqxdhKeyIndImpl true S P (.acceptNoOPK u j bundle hdr) st (resp, st') hst' with
      ⟨h1, h2, h3, h4⟩
    dsimp only at h1 h2 h3 h4
    simpa [stepEcLog, allHonestEcPksKeyInd, HasKeyIndState.toKeyIndState, h1, h2, h3, h4] using hPerm
  | roQuery inp =>
    rcases mem_support_pqxdhKeyIndImpl true S P (.roQuery inp) st (resp, st') hst' with
      ⟨h1, h2, h3, h4⟩
    dsimp only at h1 h2 h3 h4
    simpa [stepEcLog, allHonestEcPksKeyInd, HasKeyIndState.toKeyIndState, h1, h2, h3, h4] using hPerm
  | registerKey inp =>
    rcases mem_support_pqxdhKeyIndImpl true S P (.registerKey inp) st (resp, st') hst' with
      ⟨h1, h2, h3, h4⟩
    dsimp only at h1 h2 h3 h4
    simpa [stepEcLog, allHonestEcPksKeyInd, HasKeyIndState.toKeyIndState, h1, h2, h3, h4] using hPerm
  | revealDhSecrets =>
    rcases mem_support_pqxdhKeyIndImpl true S P .revealDhSecrets st (resp, st') hst' with
      ⟨h1, h2, h3, h4⟩
    dsimp only at h1 h2 h3 h4
    simpa [stepEcLog, allHonestEcPksKeyInd, HasKeyIndState.toKeyIndState, h1, h2, h3, h4] using hPerm

private theorem pqxdhKeyIndImpl1KeyRoEcLog_step (S : Setup) (P : Primitives)
    (hP : CryptoWellFormedPrimitivesδ P) (s1 s2 : Nat)
    (q : KeyIndQuery S) (p : KeyIndState S × List Bytes) :
    probExpect ((pqxdhKeyIndImpl1KeyRoEcLog S P q).run p)
      (fun x => ecPairPotential P (tagByCreation id x.2.2) s1 s2) ≤
      ecPairPotential P (tagByCreation id p.2) s1 s2 := by
  rcases p with ⟨st, ecLog⟩
  have hFresh' : ecLog.length ∉ ([] ++ tagByCreation id ecLog).map Prod.fst := by
    simpa using not_mem_fst_tagByCreation_length id ecLog
  have hInitStep : ∀ (sid : SessionId S) (u : Fin S.N_id) (bundle : PreKeyBundleInput),
      probExpect (do
        let (resp, st') ← (runKeyIndInitiate true S P sid u bundle).run st
        return (resp, (st',
          if st.sessions.length < st'.sessions.length then
            match st'.sessions with | s :: _ => P.pow8 s.hdr.ekAPk :: ecLog | [] => ecLog
          else ecLog)))
        (fun x => ecPairPotential P (tagByCreation id x.2.2) s1 s2) ≤
        ecPairPotential P (tagByCreation id ecLog) s1 s2 := by
    intro sid u bundle
    simp only [probExpect_bind, probExpect_pure]
    simpa using probExpect_runKeyIndInitiate_le P sid u bundle st
      (fun st' => ecPairPotential P (tagByCreation id
        (if st.sessions.length < st'.sessions.length then
          match st'.sessions with | s :: _ => P.pow8 s.hdr.ekAPk :: ecLog | [] => ecLog
        else ecLog)) s1 s2)
      (fun ekASk => ecPairPotential P
        ((ecLog.length, P.pow8 (P.x25519Base ekASk)) :: tagByCreation id ecLog) s1 s2)
      (fun _ _ _ _ _ h3 => by simp [h3])
      (fun _ => by
        simpa using probExpect_ecPairPotential_insert_fresh_le P hP []
          (tagByCreation id ecLog) ecLog.length s1 s2 hFresh')
  simp only [pqxdhKeyIndImpl1KeyRoEcLog, StateT.run_mk]
  cases q with
  | initPrin u =>
    unfold pqxdhKeyIndImpl1KeyRo pqxdhKeyIndImpl1KeyReal; dsimp only [stepEcLog]
    simp only [StateT.run_bind, StateT.run_get, pure_bind]
    cases st.principals.any (fun (idx, _) => idx == u.val) with
    | true => simp [StateT.run_pure, probExpect_pure]
    | false =>
      simp only [Bool.false_eq_true, ↓reduceIte, StateT.run_bind, StateT.run_monadLift,
        monadLift_self, StateT.run_set, StateT.run_pure, bind_assoc, pure_bind,
        probExpect_bind, probExpect_pure, List.length_cons, Nat.lt_succ_self]
      exact probExpect_ecPairPotential_insert_fresh_le P hP []
        (tagByCreation id ecLog) ecLog.length s1 s2 hFresh'
  | genSPK u j =>
    unfold pqxdhKeyIndImpl1KeyRo pqxdhKeyIndImpl; dsimp only [stepEcLog]
    simp only [StateT.run_bind, StateT.run_get, pure_bind]
    cases st.spkBundles.any (fun (k, _) => k == (u.val, j.val)) with
    | true => simp [StateT.run_pure, probExpect_pure]
    | false =>
      simp only [Bool.false_eq_true, ↓reduceIte]
      cases st.principals.find? (fun (idx, _) => idx == u.val) with
      | none => simp [StateT.run_pure, probExpect_pure]
      | some p =>
        rcases p with ⟨_, _⟩; dsimp only
        simp only [StateT.run_bind, StateT.run_monadLift, monadLift_self, StateT.run_set,
          StateT.run_pure, bind_assoc, pure_bind, probExpect_bind, probExpect_pure,
          List.length_cons, Nat.lt_succ_self]
        refine (probExpect_mono_of_support sampleScalar32 _
          (fun spkSk => ecPairPotential P
            ((ecLog.length, P.pow8 (P.x25519Base spkSk)) :: tagByCreation id ecLog) s1 s2) ?_).trans
          (probExpect_ecPairPotential_insert_fresh_le P hP []
            (tagByCreation id ecLog) ecLog.length s1 s2 hFresh')
        intro spkSk _
        apply probExpect_const_le_of_support; intro _ _
        apply probExpect_const_le_of_support; intro _ _
        exact probExpect_const_le_of_support _ _ _ (fun _ _ => le_rfl)
  | genOPK u j o =>
    unfold pqxdhKeyIndImpl1KeyRo pqxdhKeyIndImpl; dsimp only [stepEcLog]
    simp only [StateT.run_bind, StateT.run_get, pure_bind]
    cases st.opkEntries.any (fun (k, _) => k == (u.val, j.val, o.val)) with
    | true => simp [StateT.run_pure, probExpect_pure]
    | false =>
      simp only [Bool.false_eq_true, ↓reduceIte, StateT.run_bind, StateT.run_monadLift,
        monadLift_self, StateT.run_set, StateT.run_pure, bind_assoc, pure_bind,
        probExpect_bind, probExpect_pure, List.length_cons, Nat.lt_succ_self]
      exact probExpect_ecPairPotential_insert_fresh_le P hP []
        (tagByCreation id ecLog) ecLog.length s1 s2 hFresh'
  | initiateOPK u i bundle =>
    unfold pqxdhKeyIndImpl1KeyRo pqxdhKeyIndImpl; dsimp only [stepEcLog]
    simp only [StateT.run_bind, StateT.run_get, pure_bind]
    cases bundle.opkB?.isNone with
    | true => simp [StateT.run_pure, probExpect_pure]
    | false => simp only [Bool.false_eq_true, ↓reduceIte]; exact hInitStep (.sendOPK u i) u bundle
  | initiateNoOPK u i bundle =>
    unfold pqxdhKeyIndImpl1KeyRo pqxdhKeyIndImpl; dsimp only [stepEcLog]
    simp only [StateT.run_bind, StateT.run_get, pure_bind]
    cases bundle.opkB?.isSome with
    | true => simp [StateT.run_pure, probExpect_pure]
    | false => simp only [Bool.false_eq_true, ↓reduceIte]; exact hInitStep (.sendNoOPK u i) u bundle
  | _ =>
    dsimp only [stepEcLog]; simp only [probExpect_bind, probExpect_pure]
    exact probExpect_const_le_of_support _ _ _ (fun _ _ => le_rfl)

private theorem honestEcCollProbKeyInd1Key_active_le (S : Setup) (P : Primitives)
    (hP : CryptoWellFormedPrimitivesδ P) (b : QueryBudget)
    (A : BoundedAdv (KeyIndAdversary S) b) :
    (𝒟[runKeyInd1KeySim S P A.1 >>= fun (_, _, finalSt) =>
      pure (hasDuplicateBytes (allHonestEcPksKeyInd P finalSt))] {true}).toReal ≤
      let n_dh := activeDhCount S b.q_on
      ((n_dh * (n_dh - 1) : ℕ) : ℝ) / (2 : ℝ) ^ 251 := by
  dsimp only
  let fullEcImpl := (QueryImpl.ofLift unifSpec ProbComp).liftTarget
    (StateT (KeyIndState S × List Bytes) ProbComp) + pqxdhKeyIndImpl1KeyRoEcLog S P
  let fullImpl := (QueryImpl.ofLift unifSpec ProbComp).liftTarget
    (StateT (KeyIndState S) ProbComp) + pqxdhKeyIndImpl1KeyRo S P
  let runSimEc : ProbComp (Bool × Bool × (KeyIndState S × List Bytes)) := do
    let secb ← $ᵗ Bool
    let (b', finalPair) ← (simulateQ fullEcImpl A.1.run).run (KeyIndState.empty S secb, [])
    return (secb, b', finalPair)
  have hProj : ∀ secb,
      Prod.map id Prod.fst <$> (simulateQ fullEcImpl A.1.run).run (KeyIndState.empty S secb, []) =
      (simulateQ fullImpl A.1.run).run (KeyIndState.empty S secb) :=
    fun secb => map_proj_simulateQ Prod.fst fullEcImpl fullImpl
      (map_fst_fullKeyInd1KeyEcLogImpl S P) A.1.run (KeyIndState.empty S secb, [])
  have hRunEq : (runKeyInd1KeySim S P A.1 >>= fun (_, _, finalSt) =>
        pure (hasDuplicateBytes (allHonestEcPksKeyInd P finalSt))) =
      (runSimEc >>= fun x => pure (hasDuplicateBytes (allHonestEcPksKeyInd P x.2.2.1))) := by
    simp only [runKeyInd1KeySim, runSimEc, bind_assoc, pure_bind]
    congr 1; funext secb; rw [← hProj secb, map_eq_bind_pure_comp]; simp
  have hSim := fun s1 s2 secb =>
    simulateQ_valid_and_ecPairPotential_le P
      (fun p : KeyIndState S × List Bytes => List.Perm p.2 (allHonestEcPksKeyInd P p.1))
      (fun p => tagByCreation id p.2) (pqxdhKeyIndImpl1KeyRoEcLog S P)
      (fun q p hV => pqxdhKeyIndImpl1KeyRoEcLog_perm S P q p.1 p.2 hV) s1 s2
      (fun q p _ => pqxdhKeyIndImpl1KeyRoEcLog_step S P hP s1 s2 q p)
      A.1.run (KeyIndState.empty S secb, []) List.Perm.nil
  rw [hRunEq]
  refine doubleRangeColl_toReal_le false runSimEc
    (fun x => allHonestEcPksKeyInd P x.2.2.1) (fun x => tagByCreation id x.2.2.2)
    hasTaggedPairCollAt (activeDhCount S b.q_on) 250 Pfixed_pk_ec pfixed_pk_ec_nonneg
    (by unfold Pfixed_pk_ec; ring) (fun x hx hdup => ?_) (fun s1 s2 _ => ?_) (fun s1 s2 hlt _ _ => ?_)
  · simp only [runSimEc, MonadAttach.mem_support_bind, support_pure,
      Set.mem_singleton_iff] at hx
    rcases hx with ⟨secb, hsecb, ⟨b', finalSt, ecLog⟩, hmem, rfl⟩
    have hPerm := (hSim 0 0 secb).1 (b', finalSt, ecLog) hmem
    have hmem_base : (secb, b', finalSt) ∈ support (runKeyInd1KeySim S P A.1) := by
      simp only [runKeyInd1KeySim, MonadAttach.mem_support_bind, support_pure, Set.mem_singleton_iff]
      refine ⟨secb, hsecb, (b', finalSt), ?_, rfl⟩
      rw [← hProj secb, support_map]; exact ⟨(b', finalSt, ecLog), hmem, rfl⟩
    have hAct := runKeyInd1KeySim_mem_support_activeBounded S P b A secb b' finalSt hmem_base
    have hV := validTaggedPks_tagByCreation id ecLog (hPerm.length_eq.trans_le hAct.ecPks_le)
    have hdup' : hasDuplicateBytes ((tagByCreation id ecLog).map Prod.snd) = true := by
      simpa [map_snd_tagByCreation] using (hasDuplicateBytes_of_perm hPerm).trans hdup
    exact hasDuplicateBytes_map_snd_imp_any_double_range _ _ hV hdup'
  · rw [evalDist_bind_true_eq_probExpect]
    simp only [runSimEc, probExpect_bind, probExpect_pure]
    apply probExpect_const_le_of_support; intro secb _
    exact (probExpect_mono_of_support _ _ _
      (fun x _ => evalDist_hasTaggedPairCollAt_le_potential P _ s1 s2)).trans
      ((hSim s1 s2 secb).2.trans (ecPairPotential_nil_le P s1 s2))
  · simp only [Bool.false_eq_true, ↓reduceIte] at hlt; simp [hasTaggedPairCollAt, hlt]

/-- Active-count X25519 EC and initiator `dh2` collision bound in one-key `KeyInd`. -/
theorem ecCollProbKeyInd1Key_active_le (S : Setup) (P : Primitives)
    (hP : CryptoWellFormedPrimitivesδ P) (b : QueryBudget)
    (A : BoundedAdv (KeyIndAdversary S) b) :
    ecCollProbKeyInd1Key S P A.1 ≤
      let n_dh := activeDhCount S b.q_on
      let n_send := activeSendCount S b.q_on
      ((n_dh * (n_dh - 1) + n_send * (n_send - 1) : ℕ) : ℝ) / (2 : ℝ) ^ 251 := by
  dsimp only
  let runSim := runKeyInd1KeySim S P A.1
  have hOr : ecCollProbKeyInd1Key S P A.1 ≤
      (𝒟[runSim >>= fun (_, _, finalSt) =>
        pure (hasDuplicateBytes (allHonestEcPksKeyInd P finalSt))] {true}).toReal +
      (𝒟[runSim >>= fun (_, _, finalSt) =>
        pure (hasDuplicateBytes (allInitDh2sKeyInd P finalSt))] {true}).toReal := by
    unfold ecCollProbKeyInd1Key hasEcPkCollisionKeyInd
    simpa [List.range_succ, Finset.sum_range_succ, add_comm] using
      toReal_any_range_le_sum runSim 2 (fun k x =>
        if k == 0 then hasDuplicateBytes (allHonestEcPksKeyInd P x.2.2)
        else hasDuplicateBytes (allInitDh2sKeyInd P x.2.2))
  have h1 := honestEcCollProbKeyInd1Key_active_le S P hP b A
  have h2 := dh2CollProbKeyInd1Key_active_le S P hP b A
  dsimp only at h1 h2
  calc ecCollProbKeyInd1Key S P A.1
      ≤ _ := hOr
    _ ≤ ((activeDhCount S b.q_on * (activeDhCount S b.q_on - 1) : ℕ) : ℝ) / (2 : ℝ) ^ 251 +
        ((activeSendCount S b.q_on * (activeSendCount S b.q_on - 1) : ℕ) : ℝ) / (2 : ℝ) ^ 251 :=
        add_le_add h1 h2
    _ = ((activeDhCount S b.q_on * (activeDhCount S b.q_on - 1) +
          activeSendCount S b.q_on * (activeSendCount S b.q_on - 1) : ℕ) : ℝ) / (2 : ℝ) ^ 251 := by
        push_cast; ring

/-- Active-count `G0 -> G0_1` X25519 EC and `dh2` birthday collision hop. -/
theorem keyInd1Key_hop_G0_G0_1_active_le (S : Setup) (P : Primitives)
    (hP : CryptoWellFormedPrimitivesδ P) (b : QueryBudget)
    (A : BoundedAdv (KeyIndAdversary S) b) :
    |keyInd1KeyAdvG0 S P A.1 - keyInd1KeyAdvG0_1 S P A.1| ≤
      let n_dh := activeDhCount S b.q_on
      let n_send := activeSendCount S b.q_on
      ((n_dh * (n_dh - 1) + n_send * (n_send - 1) : ℕ) : ℝ) / (2 : ℝ) ^ 251 :=
  (keyInd1Key_hop_G0_G0_1_le_prob S P A.1).trans (ecCollProbKeyInd1Key_active_le S P hP b A)

/-- Active-count `G1 -> G2` birthday collision hop. -/
theorem keyInd1Key_hop_G1_G2_active_le (S : Setup) (P : Primitives)
    (hP : CryptoWellFormedPrimitivesδ P) (b : QueryBudget)
    (A : BoundedAdv (KeyIndAdversary S) b) :
    |keyInd1KeyAdvG1 S P A.1 - keyInd1KeyAdvG2 S P A.1| ≤
      let n_dh := activeDhCount S b.q_on
      let n_send := activeSendCount S b.q_on
      ((n_dh * (n_dh - 1) + n_send * (n_send - 1) : ℕ) : ℝ) / (2 : ℝ) ^ 251 := by
  have _ := hP; rw [keyInd1KeyAdvG1_eq_G2, sub_self, abs_zero]; positivity

end

end Computational.Proofs.SignalPqxdh.Delta.KeyInd1KeyActiveCollisions
