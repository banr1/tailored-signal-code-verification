/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Computational.Proofs.SignalPqxdh.Security.CollisionsB
import VCVio.EvalDist.Monad.Basic

@[expose] public section

/-!
# Supermartingale Public-Key Collision Bounds

Bounds honest KEM and X25519 public-key collision probabilities in PQXDH games via pairwise slot
supermartingale potentials preserved across every oracle step.
-/

set_option autoImplicit false

open OracleComp OracleSpec ENNReal MeasureTheory BigOperators

namespace SignalPqxdh.Security

open SignalPqxdh

private theorem mul_sub_one_even : ∀ n : Nat, ∃ m : Nat, n * (n - 1) = m * 2
  | 0 => ⟨0, rfl⟩
  | 1 => ⟨0, rfl⟩
  | n + 2 => by
    obtain ⟨m, hm⟩ := mul_sub_one_even (n + 1)
    rw [Nat.add_sub_cancel] at hm
    refine ⟨m + n + 1, ?_⟩
    calc (n + 2) * (n + 1) = (n + 1) * n + (n + 1) * 2 := by ring
      _ = m * 2 + (n + 1) * 2 := by rw [hm]
      _ = (m + n + 1) * 2 := by ring

theorem sum_lt_range_const (N : Nat) (c : ℝ) :
    (∑ i ∈ Finset.range N, ∑ j ∈ Finset.range N, if j < i then c else 0) =
      ((N * (N - 1) : ℕ) : ℝ) * c / 2 := by
  have hinner : ∀ i ∈ Finset.range N,
      (∑ j ∈ Finset.range N, if j < i then c else 0) = (i : ℝ) * c := by
    intro i hi
    have hi_lt : i < N := Finset.mem_range.mp hi
    rw [← Finset.sum_filter]
    have hfilt : (Finset.range N).filter (· < i) = Finset.range i := by
      ext j
      simp only [Finset.mem_filter, Finset.mem_range]
      omega
    rw [hfilt, Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  rw [Finset.sum_congr rfl hinner, ← Finset.sum_mul]
  have hsum : (∑ i ∈ Finset.range N, (i : ℝ)) = ((N * (N - 1) / 2 : ℕ) : ℝ) := by
    rw [← Nat.cast_sum, Finset.sum_range_id]
  rw [hsum]
  obtain ⟨m, hm⟩ := mul_sub_one_even N
  have hdiv : N * (N - 1) / 2 = m := by omega
  rw [hdiv, hm]
  push_cast
  ring

theorem sum_upper_offset_range_const (K M : Nat) (c : ℝ) :
    (∑ s1 ∈ Finset.range (K + M), ∑ s2 ∈ Finset.range (K + M),
      if K ≤ s1 ∧ s1 < s2 then c else 0) =
      ((M * (M - 1) : ℕ) : ℝ) * c / 2 := by
  rw [Finset.sum_range_add]
  have h1 : (∑ s1 ∈ Finset.range K, ∑ s2 ∈ Finset.range (K + M),
      if K ≤ s1 ∧ s1 < s2 then c else 0) = 0 := by
    refine Finset.sum_eq_zero (fun s1 hs1 => Finset.sum_eq_zero (fun s2 _ => ?_))
    have hfalse : ¬ (K ≤ s1 ∧ s1 < s2) := by
      have := Finset.mem_range.mp hs1
      omega
    simp [hfalse]
  rw [h1, zero_add]
  have h2 : ∀ i ∈ Finset.range M,
      (∑ s2 ∈ Finset.range (K + M), if K ≤ K + i ∧ K + i < s2 then c else 0) =
        ∑ j ∈ Finset.range M, if i < j then c else 0 := by
    intro i _
    rw [Finset.sum_range_add]
    have h2a : (∑ s2 ∈ Finset.range K, if K ≤ K + i ∧ K + i < s2 then c else 0) = 0 := by
      refine Finset.sum_eq_zero (fun s2 hs2 => ?_)
      have hfalse : ¬ (K ≤ K + i ∧ K + i < s2) := by
        have := Finset.mem_range.mp hs2
        omega
      simp only [hfalse, ↓reduceIte]
    rw [h2a, zero_add]
    refine Finset.sum_congr rfl (fun j _ => ?_)
    have hiff : (K ≤ K + i ∧ K + i < K + j) ↔ i < j := by omega
    exact if_congr hiff rfl rfl
  rw [Finset.sum_congr rfl h2, Finset.sum_comm]
  exact sum_lt_range_const M c

theorem sum_keyIndEcGrid_const (S : Setup) (c : ℝ) :
    (∑ s1 ∈ Finset.range S.N_dh, ∑ s2 ∈ Finset.range S.N_dh,
      if s2 < s1 then c
      else if S.N_id + S.N_spk_tot + S.N_opk_tot ≤ s1 ∧ s1 < s2 then c
      else 0) =
      ((S.N_dh * (S.N_dh - 1) + S.N_send_tot * (S.N_send_tot - 1) : ℕ) : ℝ) * c / 2 := by
  have hsplit : ∀ s1 s2 : Nat,
      (if s2 < s1 then c
       else if S.N_id + S.N_spk_tot + S.N_opk_tot ≤ s1 ∧ s1 < s2 then c
       else 0) =
      (if s2 < s1 then c else 0) +
      (if S.N_id + S.N_spk_tot + S.N_opk_tot ≤ s1 ∧ s1 < s2 then c else 0) := by
    intro s1 s2
    by_cases h1 : s2 < s1
    · have h2 : ¬ (S.N_id + S.N_spk_tot + S.N_opk_tot ≤ s1 ∧ s1 < s2) := by omega
      simp [h1, h2]
    · simp [h1]
  simp_rw [hsplit, Finset.sum_add_distrib]
  rw [sum_lt_range_const S.N_dh c]
  have hNdh : S.N_dh = (S.N_id + S.N_spk_tot + S.N_opk_tot) + S.N_send_tot := rfl
  rw [hNdh, sum_upper_offset_range_const (S.N_id + S.N_spk_tot + S.N_opk_tot) S.N_send_tot c]
  push_cast
  ring

theorem kemCollProb_simulateQ_le {ι : Type} {QSpec : OracleSpec ι}
    {St α : Type} (S : Setup) (getBundles : St → List ((Nat × Nat) × SpkBundleEntry))
    (initSt : Bool → St) (hInit : ∀ secb, getBundles (initSt secb) = [])
    (impl : QueryImpl QSpec (StateT St ProbComp))
    (hValid : ∀ (q : ι) (st : St), ValidSpkBundlesKem S (getBundles st) →
      ∀ x ∈ support ((impl q).run st), ValidSpkBundlesKem S (getBundles x.2))
    (hStep : ∀ (b1 b2 : Nat) (q : ι) (st : St), ValidSpkBundlesKem S (getBundles st) →
      probExpect ((impl q).run st) (fun x => kemPairPotential S (getBundles x.2) b1 b2) ≤
        kemPairPotential S (getBundles st) b1 b2)
    (oa : OracleComp (unifSpec + QSpec) α) :
    let fullImpl := (QueryImpl.ofLift unifSpec ProbComp).liftTarget (StateT St ProbComp) + impl
    let runSim : ProbComp (Bool × α × St) := do
      let secb ← $ᵗ Bool
      let (b', finalSt) ← (simulateQ fullImpl oa).run (initSt secb)
      return (secb, b', finalSt)
    (𝒟[runSim >>= fun (_, _, finalSt) =>
      pure (hasDuplicateBytes (allHonestKemPks (getBundles finalSt)))] {true}).toReal ≤
      ((S.N_spk_tot * (S.N_spk_tot - 1) : ℕ) : ℝ) / (2 : ℝ) ^ 256 := by
  intro fullImpl runSim
  have hV_init : ∀ secb, ValidSpkBundlesKem S (getBundles (initSt secb)) := by
    intro secb; rw [hInit secb]; exact validSpkBundlesKem_nil S
  have hSim := fun b1 b2 secb =>
    simulateQ_kemPairPotential_le S getBundles impl hValid b1 b2 (hStep b1 b2) oa (initSt secb)
        (hV_init secb)
  have hV_runSim : ∀ x ∈ support runSim, ValidSpkBundlesKem S (getBundles x.2.2) := by
    intro x hx
    simp only [runSim, MonadAttach.mem_support_bind,
      support_pure, Set.mem_singleton_iff] at hx
    rcases hx with ⟨secb, _, ⟨b', finalSt⟩, hmem, rfl⟩
    exact (hSim 0 0 secb).1 (b', finalSt) hmem
  have hPair_le : ∀ b1 b2 : Nat,
      (𝒟[runSim >>= fun (_, _, finalSt) =>
        pure (hasKemBundlePairCollAt S (getBundles finalSt) b1 b2)] {true}).toReal ≤
      if b2 < b1 then Pfixed_pk_kem else 0 := by
    intro b1 b2
    by_cases hlt : b2 < b1
    · simp only [hlt, ↓reduceIte]
      have h_enn :
          𝒟[runSim >>= fun (_, _, finalSt) =>
            pure (hasKemBundlePairCollAt S (getBundles finalSt) b1 b2)] {true} ≤
          ENNReal.ofReal Pfixed_pk_kem := by
        rw [evalDist_bind_true_eq_probExpect]
        simp only [runSim, probExpect_bind, probExpect_pure]
        apply probExpect_const_le_of_support; intro secb _
        calc probExpect ((simulateQ fullImpl oa).run (initSt secb))
              (fun x => 𝒟[(pure (hasKemBundlePairCollAt S (getBundles x.2) b1 b2) : ProbComp Bool)]
                  {true})
            ≤ probExpect ((simulateQ fullImpl oa).run (initSt secb))
                (fun x => kemPairPotential S (getBundles x.2) b1 b2) :=
              probExpect_mono_of_support _ _ _ (fun x _ =>
                evalDist_hasKemBundlePairCollAt_le_potential S (getBundles x.2) b1 b2)
          _ ≤ kemPairPotential S (getBundles (initSt secb)) b1 b2 := (hSim b1 b2 secb).2
          _ = kemPairPotential S [] b1 b2 := by rw [hInit secb]
          _ ≤ ENNReal.ofReal Pfixed_pk_kem := kemPairPotential_nil_le S b1 b2
      have hpos : (0 : ℝ) ≤ Pfixed_pk_kem := pfixed_pk_kem_nonneg
      have hreal := (ENNReal.toReal_le_toReal (measure_ne_top _ _) ENNReal.ofReal_ne_top).mpr h_enn
      rwa [ENNReal.toReal_ofReal hpos] at hreal
    · have h0 : 𝒟[runSim >>= fun (_, _, finalSt) =>
          pure (hasKemBundlePairCollAt S (getBundles finalSt) b1 b2)] {true} ≤ 0 := by
        rw [evalDist_bind_true_eq_probExpect]
        refine probExpect_const_le_of_support _ _ 0 (fun _ _ => ?_)
        simp [hasKemBundlePairCollAt, hlt]
      simp only [le_antisymm h0 zero_le, hlt, ↓reduceIte, ENNReal.toReal_zero, le_rfl]
  calc (𝒟[runSim >>= fun (_, _, finalSt) =>
        pure (hasDuplicateBytes (allHonestKemPks (getBundles finalSt)))] {true}).toReal
      ≤ (𝒟[runSim >>= fun (_, _, finalSt) =>
          pure ((List.range S.N_spk_tot).any (fun b1 =>
            (List.range S.N_spk_tot).any (fun b2 =>
              hasKemBundlePairCollAt S (getBundles finalSt) b1 b2)))] {true}).toReal :=
        toReal_bind_bool_mono_of_support runSim _ _ (fun x hx hdup =>
          hasDuplicateBytes_allHonestKemPks_imp_any_double_range S (getBundles x.2.2) (hV_runSim x
              hx) hdup)
    _ ≤ ∑ b1 ∈ Finset.range S.N_spk_tot,
          (𝒟[runSim >>= fun (_, _, finalSt) =>
            pure ((List.range S.N_spk_tot).any (fun b2 =>
              hasKemBundlePairCollAt S (getBundles finalSt) b1 b2))] {true}).toReal :=
        toReal_any_range_le_sum runSim S.N_spk_tot
          (fun b1 x => (List.range S.N_spk_tot).any (fun b2 =>
              hasKemBundlePairCollAt S (getBundles x.2.2) b1 b2))
    _ ≤ ∑ b1 ∈ Finset.range S.N_spk_tot,
          ∑ b2 ∈ Finset.range S.N_spk_tot,
            (𝒟[runSim >>= fun (_, _, finalSt) =>
              pure (hasKemBundlePairCollAt S (getBundles finalSt) b1 b2)] {true}).toReal :=
        Finset.sum_le_sum (fun b1 _ =>
          toReal_any_range_le_sum runSim S.N_spk_tot
            (fun b2 x => hasKemBundlePairCollAt S (getBundles x.2.2) b1 b2))
    _ ≤ ∑ b1 ∈ Finset.range S.N_spk_tot,
          ∑ b2 ∈ Finset.range S.N_spk_tot, if b2 < b1 then Pfixed_pk_kem else 0 :=
        Finset.sum_le_sum (fun b1 _ => Finset.sum_le_sum (fun b2 _ => hPair_le b1 b2))
    _ = ((S.N_spk_tot * (S.N_spk_tot - 1) : ℕ) : ℝ) / (2 : ℝ) ^ 256 := by
        rw [sum_lt_range_const]
        unfold Pfixed_pk_kem
        have h256 : (2 : ℝ) ^ 256 = (2 : ℝ) ^ 255 * 2 := pow_succ 2 255
        rw [h256]
        ring

theorem kemCollProbKeyInd_le_bound (useRo : Bool) (S : Setup) (P : Primitives)
    (hCWF : CryptoWellFormedPrimitivesδ P) (A : KeyIndAdversary S) :
    kemCollProbKeyInd useRo S P A ≤ ((S.N_spk_tot * (S.N_spk_tot - 1) : ℕ) : ℝ) / (2 : ℝ) ^ 256 := by
  unfold kemCollProbKeyInd runKeyIndSim hasKemPkCollisionKeyInd
  exact kemCollProb_simulateQ_le S KeyIndState.spkBundles (KeyIndState.empty S)
    (fun _ => rfl) (pqxdhKeyIndImpl useRo S P)
    (fun q st hV => (pqxdhKeyIndImpl_valid_and_potential_le useRo S P hCWF 0 0 q st hV).1)
    (fun b1 b2 q st hV => (pqxdhKeyIndImpl_valid_and_potential_le useRo S P hCWF b1 b2 q st hV).2)
    A.run

/-! ## EC collision supermartingale -/

def ecPrinSlotIdx (u : Nat) : Nat := u

def ecSpkSlotIdx (S : Setup) (p : Nat × Nat) : Nat :=
  S.N_id + spkSlotFlatIdx S p

def ecOpkSlotIdx (S : Setup) (p : Nat × Nat × Nat) : Nat :=
  S.N_id + S.N_spk_tot + opkSlotFlatIdx S p

def IsSendSessionId (S : Setup) : SessionId S → Prop
  | .sendOPK _ _     => True
  | .sendNoOPK _ _   => True
  | .recvOPK _ _ _   => False
  | .recvNoOPK _ _ _ => False

def sessSlotFlatIdx (S : Setup) : SessionId S → Nat
  | .sendOPK u i     => u.val * S.N_send_opk + i.val
  | .sendNoOPK u i   => S.N_id * S.N_send_opk + (u.val * S.N_send_no_opk + i.val)
  | .recvOPK _ _ _   => 0
  | .recvNoOPK _ _ _ => 0

def ecSessSlotIdx (S : Setup) (sid : SessionId S) : Nat :=
  S.N_id + S.N_spk_tot + S.N_opk_tot + sessSlotFlatIdx S sid

theorem ecSpkSlotIdx_inj (S : Setup) {k1 k2 : Nat × Nat}
    (h1 : k1.2 < S.N_recv) (h2 : k2.2 < S.N_recv)
    (heq : ecSpkSlotIdx S k1 = ecSpkSlotIdx S k2) : k1 = k2 :=
  spkSlotFlatIdx_inj S h1 h2 (Nat.add_left_cancel heq)

theorem opkSlotFlatIdx_lt (S : Setup) {u j o : Nat}
    (hu : u < S.N_id) (hj : j < S.N_recv) (ho : o < S.N_opk) :
    opkSlotFlatIdx S (u, j, o) < S.N_opk_tot := by
  unfold opkSlotFlatIdx Setup.N_opk_tot
  have h_uj : u * S.N_recv + j < S.N_id * S.N_recv := spkSlotFlatIdx_lt S hu hj
  have h_uj1 : u * S.N_recv + j + 1 ≤ S.N_id * S.N_recv := Nat.succ_le_of_lt h_uj
  calc (u * S.N_recv + j) * S.N_opk + o
      < (u * S.N_recv + j) * S.N_opk + S.N_opk := Nat.add_lt_add_left ho _
    _ = (u * S.N_recv + j + 1) * S.N_opk := by ring
    _ ≤ (S.N_id * S.N_recv) * S.N_opk := Nat.mul_le_mul_right S.N_opk h_uj1
    _ = S.N_id * S.N_recv * S.N_opk := rfl

theorem opkSlotFlatIdx_inj (S : Setup) {k1 k2 : Nat × Nat × Nat}
    (hj1 : k1.2.1 < S.N_recv) (ho1 : k1.2.2 < S.N_opk)
    (hj2 : k2.2.1 < S.N_recv) (ho2 : k2.2.2 < S.N_opk)
    (heq : opkSlotFlatIdx S k1 = opkSlotFlatIdx S k2) : k1 = k2 := by
  rcases k1 with ⟨u1, j1, o1⟩
  rcases k2 with ⟨u2, j2, o2⟩
  dsimp [opkSlotFlatIdx] at hj1 ho1 hj2 ho2 heq
  have hdiv1 : ((u1 * S.N_recv + j1) * S.N_opk + o1) / S.N_opk = u1 * S.N_recv + j1 := by
    rw [Nat.mul_comm, Nat.mul_add_div (Nat.pos_of_ne_zero (by omega)), Nat.div_eq_of_lt ho1,
        Nat.add_zero]
  have hdiv2 : ((u2 * S.N_recv + j2) * S.N_opk + o2) / S.N_opk = u2 * S.N_recv + j2 := by
    rw [Nat.mul_comm, Nat.mul_add_div (Nat.pos_of_ne_zero (by omega)), Nat.div_eq_of_lt ho2,
        Nat.add_zero]
  have huj : spkSlotFlatIdx S (u1, j1) = spkSlotFlatIdx S (u2, j2) := by
    dsimp [spkSlotFlatIdx]; rw [← hdiv1, ← hdiv2, heq]
  have hpair := spkSlotFlatIdx_inj S hj1 hj2 huj
  injection hpair with hu hj
  subst hu; subst hj
  have ho : o1 = o2 := Nat.add_left_cancel heq
  subst ho
  rfl

theorem ecOpkSlotIdx_inj (S : Setup) {k1 k2 : Nat × Nat × Nat}
    (hj1 : k1.2.1 < S.N_recv) (ho1 : k1.2.2 < S.N_opk)
    (hj2 : k2.2.1 < S.N_recv) (ho2 : k2.2.2 < S.N_opk)
    (heq : ecOpkSlotIdx S k1 = ecOpkSlotIdx S k2) : k1 = k2 :=
  opkSlotFlatIdx_inj S hj1 ho1 hj2 ho2 (Nat.add_left_cancel heq)

theorem sessSlotFlatIdx_lt (S : Setup) (sid : SessionId S) (h : IsSendSessionId S sid) :
    sessSlotFlatIdx S sid < S.N_send_tot := by
  cases sid with
  | sendOPK u i =>
    have hu1 : u.val + 1 ≤ S.N_id := Nat.succ_le_of_lt u.isLt
    have hlt : u.val * S.N_send_opk + i.val < S.N_id * S.N_send_opk := by
      calc u.val * S.N_send_opk + i.val
          < u.val * S.N_send_opk + S.N_send_opk := Nat.add_lt_add_left i.isLt _
        _ = (u.val + 1) * S.N_send_opk := by ring
        _ ≤ S.N_id * S.N_send_opk := Nat.mul_le_mul_right S.N_send_opk hu1
    dsimp only [sessSlotFlatIdx, Setup.N_send_tot, Setup.N_send_opk_tot]; omega
  | sendNoOPK u i =>
    have hu1 : u.val + 1 ≤ S.N_id := Nat.succ_le_of_lt u.isLt
    have hlt : u.val * S.N_send_no_opk + i.val < S.N_id * S.N_send_no_opk := by
      calc u.val * S.N_send_no_opk + i.val
          < u.val * S.N_send_no_opk + S.N_send_no_opk := Nat.add_lt_add_left i.isLt _
        _ = (u.val + 1) * S.N_send_no_opk := by ring
        _ ≤ S.N_id * S.N_send_no_opk := Nat.mul_le_mul_right S.N_send_no_opk hu1
    dsimp only [sessSlotFlatIdx, Setup.N_send_tot, Setup.N_send_opk_tot, Setup.N_send_no_opk_tot];
        omega
  | recvOPK _ _ _ => exact False.elim h
  | recvNoOPK _ _ _ => exact False.elim h

theorem sessSlotFlatIdx_inj (S : Setup) {s1 s2 : SessionId S}
    (h1 : IsSendSessionId S s1) (h2 : IsSendSessionId S s2)
    (heq : sessSlotFlatIdx S s1 = sessSlotFlatIdx S s2) : s1 = s2 := by
  cases s1 with
  | sendOPK u1 i1 =>
    cases s2 with
    | sendOPK u2 i2 =>
      dsimp [sessSlotFlatIdx] at heq
      have hdiv1 : (u1.val * S.N_send_opk + i1.val) / S.N_send_opk = u1.val := by
        rw [Nat.mul_comm, Nat.mul_add_div (Nat.pos_of_ne_zero (by omega)),
            Nat.div_eq_of_lt i1.isLt, Nat.add_zero]
      have hdiv2 : (u2.val * S.N_send_opk + i2.val) / S.N_send_opk = u2.val := by
        rw [Nat.mul_comm, Nat.mul_add_div (Nat.pos_of_ne_zero (by omega)),
            Nat.div_eq_of_lt i2.isLt, Nat.add_zero]
      have hu : u1 = u2 := Fin.ext (by rw [← hdiv1, ← hdiv2, heq])
      subst hu
      have hi : i1 = i2 := Fin.ext (Nat.add_left_cancel heq)
      subst hi
      rfl
    | sendNoOPK u2 i2 =>
      dsimp [sessSlotFlatIdx] at heq
      have hu1 : u1.val + 1 ≤ S.N_id := Nat.succ_le_of_lt u1.isLt
      have hlt : u1.val * S.N_send_opk + i1.val < S.N_id * S.N_send_opk := by
        calc u1.val * S.N_send_opk + i1.val
            < u1.val * S.N_send_opk + S.N_send_opk := Nat.add_lt_add_left i1.isLt _
          _ = (u1.val + 1) * S.N_send_opk := by ring
          _ ≤ S.N_id * S.N_send_opk := Nat.mul_le_mul_right S.N_send_opk hu1
      omega
    | recvOPK _ _ _ => exact False.elim h2
    | recvNoOPK _ _ _ => exact False.elim h2
  | sendNoOPK u1 i1 =>
    cases s2 with
    | sendOPK u2 i2 =>
      dsimp [sessSlotFlatIdx] at heq
      have hu2 : u2.val + 1 ≤ S.N_id := Nat.succ_le_of_lt u2.isLt
      have hlt : u2.val * S.N_send_opk + i2.val < S.N_id * S.N_send_opk := by
        calc u2.val * S.N_send_opk + i2.val
            < u2.val * S.N_send_opk + S.N_send_opk := Nat.add_lt_add_left i2.isLt _
          _ = (u2.val + 1) * S.N_send_opk := by ring
          _ ≤ S.N_id * S.N_send_opk := Nat.mul_le_mul_right S.N_send_opk hu2
      omega
    | sendNoOPK u2 i2 =>
      dsimp [sessSlotFlatIdx] at heq
      have heq' : u1.val * S.N_send_no_opk + i1.val = u2.val * S.N_send_no_opk + i2.val :=
        Nat.add_left_cancel heq
      have hdiv1 : (u1.val * S.N_send_no_opk + i1.val) / S.N_send_no_opk = u1.val := by
        rw [Nat.mul_comm, Nat.mul_add_div (Nat.pos_of_ne_zero (by omega)),
            Nat.div_eq_of_lt i1.isLt, Nat.add_zero]
      have hdiv2 : (u2.val * S.N_send_no_opk + i2.val) / S.N_send_no_opk = u2.val := by
        rw [Nat.mul_comm, Nat.mul_add_div (Nat.pos_of_ne_zero (by omega)),
            Nat.div_eq_of_lt i2.isLt, Nat.add_zero]
      have hu : u1 = u2 := Fin.ext (by rw [← hdiv1, ← hdiv2, heq'])
      subst hu
      have hi : i1 = i2 := Fin.ext (Nat.add_left_cancel heq')
      subst hi
      rfl
    | recvOPK _ _ _ => exact False.elim h2
    | recvNoOPK _ _ _ => exact False.elim h2
  | recvOPK _ _ _ => exact False.elim h1
  | recvNoOPK _ _ _ => exact False.elim h1

theorem ecSessSlotIdx_inj (S : Setup) {s1 s2 : SessionId S}
    (h1 : IsSendSessionId S s1) (h2 : IsSendSessionId S s2)
    (heq : ecSessSlotIdx S s1 = ecSessSlotIdx S s2) : s1 = s2 :=
  sessSlotFlatIdx_inj S h1 h2 (Nat.add_left_cancel heq)

def hasTaggedPairCollAt (tagged : List (Nat × Bytes)) (s1 s2 : Nat) : Bool :=
  decide (s2 < s1) &&
  match tagged.find? (fun p => p.1 == s1), tagged.find? (fun p => p.1 == s2) with
  | some (_, pk1), some (_, pk2) => pk1 == pk2
  | _, _                         => false

theorem find?_fst_eq_some :
    ∀ (tagged : List (Nat × Bytes)),
      (tagged.map Prod.fst).Nodup →
      ∀ p ∈ tagged, tagged.find? (fun x => x.1 == p.1) = some p
  | [], _, _, hmem => False.elim (List.not_mem_nil hmem)
  | x :: xs, hnodup, p, hmem => by
    rw [List.map_cons, List.nodup_cons] at hnodup
    rcases List.mem_cons.mp hmem with rfl | hxs
    · simp [List.find?]
    · have hne : (x.1 == p.1) = false := by
        rw [beq_eq_false_iff_ne]
        intro heq
        apply hnodup.1
        rw [heq, List.mem_map]
        exact ⟨p, hxs, rfl⟩
      simp [List.find?, hne, find?_fst_eq_some xs hnodup.2 p hxs]

theorem exists_mem_of_contains_map_snd (pk : Bytes) :
    ∀ (xs : List (Nat × Bytes)),
      (xs.map Prod.snd).contains pk = true →
      ∃ p ∈ xs, p.2 = pk
  | [], h => by simp at h
  | y :: ys, h => by
    simp only [List.map_cons, List.contains_cons, Bool.or_eq_true] at h
    rcases h with hhead | htail
    · exact ⟨y, List.mem_cons_self, (beq_iff_eq.mp hhead).symm⟩
    · obtain ⟨p, hp, hpk⟩ := exists_mem_of_contains_map_snd pk ys htail
      exact ⟨p, List.mem_cons_of_mem y hp, hpk⟩

theorem exists_distinct_of_hasDuplicateBytes_map_snd :
    ∀ (xs : List (Nat × Bytes)),
      (xs.map Prod.fst).Nodup →
      hasDuplicateBytes (xs.map Prod.snd) = true →
      ∃ p1 ∈ xs, ∃ p2 ∈ xs, p1.1 ≠ p2.1 ∧ p1.2 = p2.2
  | [], _, h => by simp [hasDuplicateBytes] at h
  | x :: xs, hnodup, h => by
    rw [List.map_cons, List.nodup_cons] at hnodup
    simp only [List.map_cons, hasDuplicateBytes, Bool.or_eq_true] at h
    rcases h with hmem | hdup
    · obtain ⟨p2, hp2, hpk⟩ := exists_mem_of_contains_map_snd x.2 xs hmem
      refine ⟨x, List.mem_cons_self, p2, List.mem_cons_of_mem x hp2, ?_, hpk.symm⟩
      intro heq
      apply hnodup.1
      rw [heq, List.mem_map]
      exact ⟨p2, hp2, rfl⟩
    · obtain ⟨p1, hp1, p2, hp2, hne, hpk⟩ :=
        exists_distinct_of_hasDuplicateBytes_map_snd xs hnodup.2 hdup
      exact ⟨p1, List.mem_cons_of_mem x hp1, p2, List.mem_cons_of_mem x hp2, hne, hpk⟩

def ValidTaggedPks (N : Nat) (tagged : List (Nat × Bytes)) : Prop :=
  (∀ p ∈ tagged, p.1 < N) ∧ (tagged.map Prod.fst).Nodup

theorem hasDuplicateBytes_map_snd_imp_any_double_range (N : Nat)
    (tagged : List (Nat × Bytes))
    (hV : ValidTaggedPks N tagged)
    (hdup : hasDuplicateBytes (tagged.map Prod.snd) = true) :
    ((List.range N).any (fun s1 =>
      (List.range N).any (fun s2 =>
        hasTaggedPairCollAt tagged s1 s2))) = true := by
  obtain ⟨p1, hp1, p2, hp2, hne, hpk⟩ :=
    exists_distinct_of_hasDuplicateBytes_map_snd tagged hV.2 hdup
  have hs1 : p1.1 < N := hV.1 p1 hp1
  have hs2 : p2.1 < N := hV.1 p2 hp2
  have hf1 := find?_fst_eq_some tagged hV.2 p1 hp1
  have hf2 := find?_fst_eq_some tagged hV.2 p2 hp2
  simp only [List.any_eq_true, List.mem_range]
  rcases Nat.lt_or_gt_of_ne hne with hlt | hgt
  · refine ⟨p2.1, hs2, p1.1, hs1, ?_⟩
    unfold hasTaggedPairCollAt
    simp [hlt, hf1, hf2, hpk]
  · refine ⟨p1.1, hs1, p2.1, hs2, ?_⟩
    unfold hasTaggedPairCollAt
    simp [hgt, hf1, hf2, hpk]

/-- Lower-triangle (`s2 < s1`) supermartingale potential for X25519 public-key collisions, charging
    `Pfixed_pk_ec` while either slot is unfilled. -/
noncomputable def ecPairPotential (P : Primitives) (tagged : List (Nat × Bytes)) (s1 s2 : Nat) :
  ℝ≥0∞ :=
  if s2 < s1 then
    match tagged.find? (fun p => p.1 == s1), tagged.find? (fun p => p.1 == s2) with
    | some (_, pk1), some (_, pk2) =>
        𝒟[(pure (P.pow8 pk1 == P.pow8 pk2) : ProbComp Bool)] {true}
    | _, _ => ENNReal.ofReal Pfixed_pk_ec
  else
    0

theorem evalDist_hasTaggedPairCollAt_le_potential (P : Primitives)
    (tagged : List (Nat × Bytes)) (s1 s2 : Nat) :
    𝒟[(pure (hasTaggedPairCollAt tagged s1 s2) : ProbComp Bool)] {true} ≤
      ecPairPotential P tagged s1 s2 := by
  unfold hasTaggedPairCollAt ecPairPotential
  by_cases hlt : s2 < s1
  · simp only [hlt, decide_true, Bool.true_and, ↓reduceIte]
    cases tagged.find? (fun p => p.1 == s1) with
    | none => simp
    | some p1 =>
      rcases p1 with ⟨_, pk1⟩
      cases tagged.find? (fun p => p.1 == s2) with
      | none => simp
      | some p2 =>
        rcases p2 with ⟨_, pk2⟩
        dsimp only
        by_cases heq : (pk1 == pk2) = true
        · have hpow : (P.pow8 pk1 == P.pow8 pk2) = true := by
            rw [beq_iff_eq] at heq ⊢
            exact congrArg P.pow8 heq
          simp [heq, hpow]
        · simp [heq]
  · simp [hlt]

theorem ecPairPotential_nil_le (P : Primitives) (s1 s2 : Nat) :
    ecPairPotential P [] s1 s2 ≤ ENNReal.ofReal Pfixed_pk_ec := by
  unfold ecPairPotential
  split_ifs <;> simp

theorem find?_fst_none_of_not_mem (tagged : List (Nat × Bytes)) (s : Nat)
    (h : s ∉ tagged.map Prod.fst) :
    tagged.find? (fun p => p.1 == s) = none := by
  rw [List.find?_eq_none]
  intro p hp hbeq
  apply h
  rw [← beq_iff_eq.mp hbeq, List.mem_map]
  exact ⟨p, hp, rfl⟩

theorem find?_insert_fresh :
    ∀ (L1 L2 : List (Nat × Bytes)) (sNew : Nat) (pkNew : Bytes) (s : Nat),
      sNew ∉ (L1 ++ L2).map Prod.fst →
      (L1 ++ (sNew, pkNew) :: L2).find? (fun p => p.1 == s) =
        if sNew == s then some (sNew, pkNew) else (L1 ++ L2).find? (fun p => p.1 == s)
  | [], L2, sNew, pkNew, s, _ => by
    cases h : (sNew == s) <;> simp [h]
  | (s0, pk0) :: tl, L2, sNew, pkNew, s, hFresh => by
    simp only [List.cons_append, List.map_cons, List.mem_cons, not_or] at hFresh
    rcases hFresh with ⟨hne0, hFresh_tl⟩
    simp only [List.cons_append, List.find?]
    by_cases hs0 : (s0 == s) = true
    · have hsNew : (sNew == s) = false := by
        rw [beq_eq_false_iff_ne]
        intro heq
        exact hne0 (heq.trans (beq_iff_eq.mp hs0).symm)
      simp [hs0, hsNew]
    · simp [hs0, find?_insert_fresh tl L2 sNew pkNew s hFresh_tl]

theorem probExpect_sampleScalar32_ec_coll_le (P : Primitives) (hP : CryptoWellFormedPrimitivesδ P)
    (targetPk : Bytes) :
    probExpect sampleScalar32
      (fun sk => 𝒟[(pure (P.pow8 (P.x25519Base sk) == P.pow8 targetPk) : ProbComp Bool)] {true}) ≤
      ENNReal.ofReal Pfixed_pk_ec := by
  rw [← evalDist_bind_true_eq_probExpect, ← ENNReal.ofReal_toReal (measure_ne_top _ {true})]
  exact ENNReal.ofReal_le_ofReal (hP.ec_coll_bound_real targetPk)

theorem probExpect_ecPairPotential_insert_fresh_le (P : Primitives)
    (hP : CryptoWellFormedPrimitivesδ P)
    (L1 L2 : List (Nat × Bytes)) (sNew : Nat) (s1 s2 : Nat)
    (hFresh : sNew ∉ (L1 ++ L2).map Prod.fst) :
    probExpect sampleScalar32
      (fun sk => ecPairPotential P (L1 ++ (sNew, P.pow8 (P.x25519Base sk)) :: L2) s1 s2) ≤
      ecPairPotential P (L1 ++ L2) s1 s2 := by
  have hnone := find?_fst_none_of_not_mem (L1 ++ L2) sNew hFresh
  unfold ecPairPotential
  by_cases hlt : s2 < s1
  · simp only [hlt, ↓reduceIte]
    simp_rw [find?_insert_fresh L1 L2 sNew _ s1 hFresh,
             find?_insert_fresh L1 L2 sNew _ s2 hFresh]
    by_cases hs1 : (sNew == s1) = true
    · have heq1 : sNew = s1 := beq_iff_eq.mp hs1
      have hs2 : (sNew == s2) = false := by rw [beq_eq_false_iff_ne]; omega
      have hnone1 : (L1 ++ L2).find? (fun p => p.1 == s1) = none := by rwa [← heq1]
      simp only [hs1, hs2, hnone1, ↓reduceIte, Bool.false_eq_true]
      cases (L1 ++ L2).find? (fun p => p.1 == s2) with
      | none => simp [probExpect_const]
      | some p2 =>
        rcases p2 with ⟨_, pk2⟩
        simp only [hP.pow8_idemp]
        exact probExpect_sampleScalar32_ec_coll_le P hP pk2
    · simp only [Bool.not_eq_true] at hs1
      by_cases hs2 : (sNew == s2) = true
      · have heq2 : sNew = s2 := beq_iff_eq.mp hs2
        have hnone2 : (L1 ++ L2).find? (fun p => p.1 == s2) = none := by rwa [← heq2]
        simp only [hs1, hs2, hnone2, ↓reduceIte, Bool.false_eq_true]
        cases (L1 ++ L2).find? (fun p => p.1 == s1) with
        | none => simp [probExpect_const]
        | some p1 =>
          rcases p1 with ⟨_, pk1⟩
          have h_comm : ∀ sk : Bytes,
              ((P.pow8 pk1 == P.pow8 (P.pow8 (P.x25519Base sk))) : Bool) =
              (P.pow8 (P.x25519Base sk) == P.pow8 pk1) := by
            intro sk
            rw [hP.pow8_idemp, Bool.beq_comm]
          simp_rw [h_comm]
          exact probExpect_sampleScalar32_ec_coll_le P hP pk1
      · simp only [Bool.not_eq_true] at hs2
        simp only [hs1, hs2, Bool.false_eq_true, ↓reduceIte, probExpect_const, le_rfl]
  · simp [hlt, probExpect_const]

theorem simulateQ_valid_and_ecPairPotential_le
    {ι : Type} {QSpec : OracleSpec ι} {St α : Type}
    (P : Primitives) (ValidSt : St → Prop) (getTagged : St → List (Nat × Bytes))
    (impl : QueryImpl QSpec (StateT St ProbComp))
    (hValid : ∀ (q : ι) (st : St), ValidSt st →
      ∀ x ∈ support ((impl q).run st), ValidSt x.2)
    (s1 s2 : Nat)
    (hStep : ∀ (q : ι) (st : St), ValidSt st →
      probExpect ((impl q).run st) (fun x => ecPairPotential P (getTagged x.2) s1 s2) ≤
        ecPairPotential P (getTagged st) s1 s2)
    (oa : OracleComp (unifSpec + QSpec) α) (st : St)
    (hV : ValidSt st) :
    (∀ x ∈ support ((simulateQ ((QueryImpl.ofLift unifSpec ProbComp).liftTarget (StateT St
      ProbComp) + impl) oa).run st),
      ValidSt x.2) ∧
    probExpect ((simulateQ ((QueryImpl.ofLift unifSpec ProbComp).liftTarget (StateT St ProbComp) +
      impl) oa).run st)
      (fun x => ecPairPotential P (getTagged x.2) s1 s2) ≤
      ecPairPotential P (getTagged st) s1 s2 := by
  let fullImpl := (QueryImpl.ofLift unifSpec ProbComp).liftTarget (StateT St ProbComp) + impl
  induction oa using OracleComp.inductionOn generalizing st with
  | pure a =>
    refine ⟨?_, ?_⟩
    · intro x hx
      simp [StateT.run_pure] at hx
      rcases hx with ⟨_, rfl⟩
      exact hV
    · simp [StateT.run_pure, probExpect_pure]
  | query_bind q oa ih =>
    cases q with
    | inl uq =>
      have hrun :
          (simulateQ fullImpl (liftM (OracleSpec.query (Sum.inl uq)) >>= oa)).run st =
          (do let u ← liftM (unifSpec.query uq); (simulateQ fullImpl (oa u)).run st) := by
        simp [fullImpl, simulateQ_bind, QueryImpl.liftTarget, StateT.run_bind, StateT.run_monadLift]
      rw [hrun]
      refine ⟨?_, ?_⟩
      · intro x hx
        rw [MonadAttach.mem_support_bind] at hx
        rcases hx with ⟨u, _, hx⟩
        exact (ih u st hV).1 x hx
      · rw [probExpect_bind]
        exact probExpect_const_le_of_support _ _ _ (fun u _ => (ih u st hV).2)
    | inr gq =>
      have hrun :
          (simulateQ fullImpl (liftM (OracleSpec.query (Sum.inr gq)) >>= oa)).run st =
          ((impl gq).run st >>= fun y => (simulateQ fullImpl (oa y.1)).run y.2) := by
        simp [fullImpl, simulateQ_bind, StateT.run_bind]
      rw [hrun]
      refine ⟨?_, ?_⟩
      · intro x hx
        rw [MonadAttach.mem_support_bind] at hx
        rcases hx with ⟨y, hy, hx⟩
        exact (ih y.1 y.2 (hValid gq st hV y hy)).1 x hx
      · rw [probExpect_bind]
        calc probExpect ((impl gq).run st)
              (fun y => probExpect ((simulateQ fullImpl (oa y.1)).run y.2)
                (fun x => ecPairPotential P (getTagged x.2) s1 s2))
            ≤ probExpect ((impl gq).run st)
                (fun y => ecPairPotential P (getTagged y.2) s1 s2) :=
              probExpect_mono_of_support ((impl gq).run st) _ _
                (fun y hy => (ih y.1 y.2 (hValid gq st hV y hy)).2)
          _ ≤ ecPairPotential P (getTagged st) s1 s2 := hStep gq st hV

theorem ecCollProb_le_of_step
    {ι : Type} {QSpec : OracleSpec ι} {St α : Type}
    (N : Nat) (P : Primitives) (ValidSt : St → Prop) (getTagged : St → List (Nat × Bytes))
    (hasColl : St → Bool)
    (impl : QueryImpl QSpec (StateT St ProbComp))
    (initSt : Bool → St)
    (hInitV : ∀ secb, ValidSt (initSt secb))
    (hInitE : ∀ secb, getTagged (initSt secb) = [])
    (hValidTagged : ∀ st, ValidSt st → ValidTaggedPks N (getTagged st))
    (hCollEq : ∀ st, ValidSt st → hasColl st = hasDuplicateBytes ((getTagged st).map Prod.snd))
    (hValid : ∀ (q : ι) (st : St), ValidSt st →
      ∀ x ∈ support ((impl q).run st), ValidSt x.2)
    (hStep : ∀ (q : ι) (st : St) (s1 s2 : Nat), ValidSt st →
      probExpect ((impl q).run st) (fun x => ecPairPotential P (getTagged x.2) s1 s2) ≤
        ecPairPotential P (getTagged st) s1 s2)
    (oa : OracleComp (unifSpec + QSpec) α) :
    let fullImpl := (QueryImpl.ofLift unifSpec ProbComp).liftTarget (StateT St ProbComp) + impl
    let runSim : ProbComp (Bool × α × St) := do
      let secb ← $ᵗ Bool
      let (b', finalSt) ← (simulateQ fullImpl oa).run (initSt secb)
      return (secb, b', finalSt)
    (𝒟[runSim >>= fun (_, _, finalSt) =>
      pure (hasColl finalSt)] {true}).toReal ≤
      ((N * (N - 1) : ℕ) : ℝ) / (2 : ℝ) ^ 251 := by
  intro fullImpl runSim
  have hSim := fun s1 s2 secb =>
    simulateQ_valid_and_ecPairPotential_le P ValidSt getTagged impl hValid s1 s2
      (fun q st hV => hStep q st s1 s2 hV) oa (initSt secb) (hInitV secb)
  have hV_runSim : ∀ x ∈ support runSim, ValidSt x.2.2 := by
    intro x hx
    simp only [runSim, MonadAttach.mem_support_bind,
      support_pure, Set.mem_singleton_iff] at hx
    rcases hx with ⟨secb, _, ⟨b', finalSt⟩, hmem, rfl⟩
    exact (hSim 0 0 secb).1 (b', finalSt) hmem
  have hPair_le : ∀ s1 s2 : Nat,
      (𝒟[runSim >>= fun (_, _, finalSt) =>
        pure (hasTaggedPairCollAt (getTagged finalSt) s1 s2)] {true}).toReal ≤
      if s2 < s1 then Pfixed_pk_ec else 0 := by
    intro s1 s2
    by_cases hlt : s2 < s1
    · simp only [hlt, ↓reduceIte]
      have h_enn :
          𝒟[runSim >>= fun (_, _, finalSt) =>
            pure (hasTaggedPairCollAt (getTagged finalSt) s1 s2)] {true} ≤
          ENNReal.ofReal Pfixed_pk_ec := by
        rw [evalDist_bind_true_eq_probExpect]
        simp only [runSim, probExpect_bind, probExpect_pure]
        apply probExpect_const_le_of_support; intro secb _
        calc probExpect ((simulateQ fullImpl oa).run (initSt secb))
              (fun x => 𝒟[(pure (hasTaggedPairCollAt (getTagged x.2) s1 s2) : ProbComp Bool)] {true})
            ≤ probExpect ((simulateQ fullImpl oa).run (initSt secb))
                (fun x => ecPairPotential P (getTagged x.2) s1 s2) :=
              probExpect_mono_of_support _ _ _ (fun x _ =>
                evalDist_hasTaggedPairCollAt_le_potential P (getTagged x.2) s1 s2)
          _ ≤ ecPairPotential P (getTagged (initSt secb)) s1 s2 := (hSim s1 s2 secb).2
          _ = ecPairPotential P [] s1 s2 := by rw [hInitE secb]
          _ ≤ ENNReal.ofReal Pfixed_pk_ec := ecPairPotential_nil_le P s1 s2
      have hreal := (ENNReal.toReal_le_toReal (measure_ne_top _ _) ENNReal.ofReal_ne_top).mpr h_enn
      rwa [ENNReal.toReal_ofReal pfixed_pk_ec_nonneg] at hreal
    · have h0 : 𝒟[runSim >>= fun (_, _, finalSt) =>
          pure (hasTaggedPairCollAt (getTagged finalSt) s1 s2)] {true} ≤ 0 := by
        rw [evalDist_bind_true_eq_probExpect]
        refine probExpect_const_le_of_support _ _ 0 (fun _ _ => ?_)
        simp [hasTaggedPairCollAt, hlt]
      simp only [le_antisymm h0 zero_le, hlt, ↓reduceIte, ENNReal.toReal_zero, le_rfl]
  calc (𝒟[runSim >>= fun (_, _, finalSt) =>
        pure (hasColl finalSt)] {true}).toReal
      ≤ (𝒟[runSim >>= fun (_, _, finalSt) =>
          pure ((List.range N).any (fun s1 =>
            (List.range N).any (fun s2 =>
              hasTaggedPairCollAt (getTagged finalSt) s1 s2)))] {true}).toReal :=
        toReal_bind_bool_mono_of_support runSim _ _ (fun x hx hdup => by
          rw [hCollEq x.2.2 (hV_runSim x hx)] at hdup
          exact hasDuplicateBytes_map_snd_imp_any_double_range N (getTagged x.2.2)
            (hValidTagged x.2.2 (hV_runSim x hx)) hdup)
    _ ≤ ∑ s1 ∈ Finset.range N,
          (𝒟[runSim >>= fun (_, _, finalSt) =>
            pure ((List.range N).any (fun s2 =>
              hasTaggedPairCollAt (getTagged finalSt) s1 s2))] {true}).toReal :=
        toReal_any_range_le_sum runSim N
          (fun s1 x => (List.range N).any (fun s2 => hasTaggedPairCollAt (getTagged x.2.2) s1 s2))
    _ ≤ ∑ s1 ∈ Finset.range N,
          ∑ s2 ∈ Finset.range N,
            (𝒟[runSim >>= fun (_, _, finalSt) =>
              pure (hasTaggedPairCollAt (getTagged finalSt) s1 s2)] {true}).toReal :=
        Finset.sum_le_sum (fun s1 _ =>
          toReal_any_range_le_sum runSim N
            (fun s2 x => hasTaggedPairCollAt (getTagged x.2.2) s1 s2))
    _ ≤ ∑ s1 ∈ Finset.range N,
          ∑ s2 ∈ Finset.range N, if s2 < s1 then Pfixed_pk_ec else 0 :=
        Finset.sum_le_sum (fun s1 _ => Finset.sum_le_sum (fun s2 _ => hPair_le s1 s2))
    _ = ((N * (N - 1) : ℕ) : ℝ) / (2 : ℝ) ^ 251 := by
        rw [sum_lt_range_const]
        unfold Pfixed_pk_ec
        ring

/-! ## Slot-list invariants -/

def ValidPrincipals (S : Setup) (principals : List (Nat × PrincipalEntry)) : Prop :=
  (∀ e ∈ principals, e.1 < S.N_id) ∧
  (principals.map Prod.fst).Nodup

def ValidSpkBundles (S : Setup) (spkBundles : List ((Nat × Nat) × SpkBundleEntry)) : Prop :=
  (∀ e ∈ spkBundles, e.1.1 < S.N_id ∧ e.1.2 < S.N_recv) ∧
  (spkBundles.map (fun e => ecSpkSlotIdx S e.1)).Nodup

def ValidOpkEntries (S : Setup) (opkEntries : List ((Nat × Nat × Nat) × OpkEntry)) : Prop :=
  (∀ e ∈ opkEntries, e.1.1 < S.N_id ∧ e.1.2.1 < S.N_recv ∧ e.1.2.2 < S.N_opk) ∧
  (opkEntries.map (fun e => ecOpkSlotIdx S e.1)).Nodup

def ValidSessionIds (S : Setup) (sids : List (SessionId S)) : Prop :=
  (∀ s ∈ sids, IsSendSessionId S s) ∧
  (sids.map (ecSessSlotIdx S)).Nodup

def ValidEcLists (S : Setup)
    (principals : List (Nat × PrincipalEntry))
    (spkBundles : List ((Nat × Nat) × SpkBundleEntry))
    (opkEntries : List ((Nat × Nat × Nat) × OpkEntry))
    (sids : List (SessionId S)) : Prop :=
  ValidPrincipals S principals ∧
  ValidSpkBundles S spkBundles ∧
  ValidOpkEntries S opkEntries ∧
  ValidSessionIds S sids

theorem validEcLists_nil (S : Setup) : ValidEcLists S [] [] [] [] :=
  ⟨⟨fun _ h => False.elim (List.not_mem_nil h), List.nodup_nil⟩,
   ⟨fun _ h => False.elim (List.not_mem_nil h), List.nodup_nil⟩,
   ⟨fun _ h => False.elim (List.not_mem_nil h), List.nodup_nil⟩,
   ⟨fun _ h => False.elim (List.not_mem_nil h), List.nodup_nil⟩⟩

def ecTaggedFromLists (S : Setup) (P : Primitives)
    (principals : List (Nat × PrincipalEntry))
    (spkBundles : List ((Nat × Nat) × SpkBundleEntry))
    (opkEntries : List ((Nat × Nat × Nat) × OpkEntry))
    (sessPks : List (SessionId S × Bytes)) : List (Nat × Bytes) :=
  (principals.map (fun (u, e) => (ecPrinSlotIdx u, P.pow8 e.ikAPk))) ++
  (spkBundles.map (fun (k, b) => (ecSpkSlotIdx S k, P.pow8 b.spkPk))) ++
  (opkEntries.map (fun (k, o) => (ecOpkSlotIdx S k, P.pow8 o.opkPk))) ++
  (sessPks.map (fun (sid, pk) => (ecSessSlotIdx S sid, P.pow8 pk)))

theorem nodup_append_of_lt_le {L1 L2 : List Nat} {M : Nat}
    (h1 : L1.Nodup) (h2 : L2.Nodup)
    (hlt : ∀ x ∈ L1, x < M) (hle : ∀ y ∈ L2, M ≤ y) :
    (L1 ++ L2).Nodup :=
  h1.append h2 (fun x hx1 hx2 => by
    have h_x := hlt x hx1
    have h_y := hle x hx2
    omega)

theorem map_fst_ecTaggedFromLists (S : Setup) (P : Primitives)
    (principals : List (Nat × PrincipalEntry))
    (spkBundles : List ((Nat × Nat) × SpkBundleEntry))
    (opkEntries : List ((Nat × Nat × Nat) × OpkEntry))
    (sessPks : List (SessionId S × Bytes)) :
    (ecTaggedFromLists S P principals spkBundles opkEntries sessPks).map Prod.fst =
      (principals.map Prod.fst) ++
      (spkBundles.map (fun e => ecSpkSlotIdx S e.1)) ++
      (opkEntries.map (fun e => ecOpkSlotIdx S e.1)) ++
      ((sessPks.map Prod.fst).map (ecSessSlotIdx S)) := by
  unfold ecTaggedFromLists ecPrinSlotIdx
  simp [List.map_append, List.map_map, Function.comp_def]

theorem validTaggedPks_ecTaggedFromLists (S : Setup) (P : Primitives)
    (principals : List (Nat × PrincipalEntry))
    (spkBundles : List ((Nat × Nat) × SpkBundleEntry))
    (opkEntries : List ((Nat × Nat × Nat) × OpkEntry))
    (sessPks : List (SessionId S × Bytes))
    (hV : ValidEcLists S principals spkBundles opkEntries (sessPks.map Prod.fst)) :
    ValidTaggedPks S.N_dh (ecTaggedFromLists S P principals spkBundles opkEntries sessPks) := by
  rcases hV with ⟨hP_v, hS_v, hO_v, hSess_v⟩
  have h1_lt : ∀ x ∈ principals.map Prod.fst, x < S.N_id := by
    intro x hx; rw [List.mem_map] at hx; rcases hx with ⟨e, he, rfl⟩; exact hP_v.1 e he
  have h2_ge : ∀ x ∈ spkBundles.map (fun e => ecSpkSlotIdx S e.1), S.N_id ≤ x := by
    intro x hx; rw [List.mem_map] at hx; rcases hx with ⟨e, _, rfl⟩; unfold ecSpkSlotIdx; omega
  have h2_lt : ∀ x ∈ spkBundles.map (fun e => ecSpkSlotIdx S e.1), x < S.N_id + S.N_spk_tot := by
    intro x hx; rw [List.mem_map] at hx; rcases hx with ⟨⟨⟨u, j⟩, b⟩, he, rfl⟩
    unfold ecSpkSlotIdx
    have := spkSlotFlatIdx_lt S (hS_v.1 _ he).1 (hS_v.1 _ he).2
    dsimp only at *; omega
  have h3_ge : ∀ x ∈ opkEntries.map (fun e => ecOpkSlotIdx S e.1), S.N_id + S.N_spk_tot ≤ x := by
    intro x hx; rw [List.mem_map] at hx; rcases hx with ⟨e, _, rfl⟩; unfold ecOpkSlotIdx; omega
  have h3_lt : ∀ x ∈ opkEntries.map (fun e => ecOpkSlotIdx S e.1),
      x < S.N_id + S.N_spk_tot + S.N_opk_tot := by
    intro x hx; rw [List.mem_map] at hx; rcases hx with ⟨⟨⟨u, j, o⟩, b⟩, he, rfl⟩
    unfold ecOpkSlotIdx
    have := opkSlotFlatIdx_lt S (hO_v.1 _ he).1 (hO_v.1 _ he).2.1 (hO_v.1 _ he).2.2
    dsimp only at *; omega
  have h4_ge : ∀ x ∈ (sessPks.map Prod.fst).map (ecSessSlotIdx S),
      S.N_id + S.N_spk_tot + S.N_opk_tot ≤ x := by
    intro x hx; rw [List.mem_map] at hx; rcases hx with ⟨sid, _, rfl⟩; unfold ecSessSlotIdx; omega
  have h4_lt : ∀ x ∈ (sessPks.map Prod.fst).map (ecSessSlotIdx S), x < S.N_dh := by
    intro x hx; rw [List.mem_map] at hx; rcases hx with ⟨sid, hsid, rfl⟩
    unfold ecSessSlotIdx Setup.N_dh
    have := sessSlotFlatIdx_lt S sid (hSess_v.1 sid hsid)
    omega
  have h12_nodup : ((principals.map Prod.fst) ++ (spkBundles.map (fun e =>
      ecSpkSlotIdx S e.1))).Nodup :=
    nodup_append_of_lt_le hP_v.2 hS_v.2 h1_lt h2_ge
  have h12_lt : ∀ x ∈ (principals.map Prod.fst) ++ (spkBundles.map (fun e => ecSpkSlotIdx S e.1)),
      x < S.N_id + S.N_spk_tot := by
    intro x hx; rcases List.mem_append.mp hx with hx1 | hx2
    · have := h1_lt x hx1; omega
    · exact h2_lt x hx2
  have h123_nodup :
      (((principals.map Prod.fst) ++ (spkBundles.map (fun e => ecSpkSlotIdx S e.1))) ++
       (opkEntries.map (fun e => ecOpkSlotIdx S e.1))).Nodup :=
    nodup_append_of_lt_le h12_nodup hO_v.2 h12_lt h3_ge
  have h123_lt :
      ∀ x ∈ ((principals.map Prod.fst) ++ (spkBundles.map (fun e => ecSpkSlotIdx S e.1))) ++
        (opkEntries.map (fun e => ecOpkSlotIdx S e.1)),
        x < S.N_id + S.N_spk_tot + S.N_opk_tot := by
    intro x hx; rcases List.mem_append.mp hx with hx12 | hx3
    · have := h12_lt x hx12; omega
    · exact h3_lt x hx3
  have h1234_nodup := nodup_append_of_lt_le h123_nodup hSess_v.2 h123_lt h4_ge
  refine ⟨?_, ?_⟩
  · intro p hp
    have hmem : p.1 ∈ (ecTaggedFromLists S P principals spkBundles opkEntries sessPks).map
      Prod.fst :=
      List.mem_map_of_mem hp
    rw [map_fst_ecTaggedFromLists] at hmem
    rcases List.mem_append.mp hmem with h123 | h4
    · have := h123_lt p.1 h123; unfold Setup.N_dh; omega
    · exact h4_lt p.1 h4
  · rw [map_fst_ecTaggedFromLists]
    exact h1234_nodup

theorem validPrincipals_cons (S : Setup) (u : Fin S.N_id) (entry : PrincipalEntry)
    (principals : List (Nat × PrincipalEntry))
    (hV : ValidPrincipals S principals)
    (hFresh : principals.any (fun (idx, _) => idx == u.val) = false) :
    ValidPrincipals S ((u.val, entry) :: principals) ∧
    u.val ∉ principals.map Prod.fst := by
  have hnot_in : u.val ∉ principals.map Prod.fst := by
    intro hmem
    rw [List.mem_map] at hmem
    rcases hmem with ⟨⟨idx, e⟩, he_mem, hidx_eq⟩
    have hany : principals.any (fun (idx', _) => idx' == u.val) = true := by
      rw [List.any_eq_true]
      exact ⟨(idx, e), he_mem, beq_iff_eq.mpr hidx_eq⟩
    rw [hFresh] at hany; cases hany
  refine ⟨⟨?_, ?_⟩, hnot_in⟩
  · intro e he
    rcases List.mem_cons.mp he with rfl | hmem
    · exact u.isLt
    · exact hV.1 e hmem
  · rw [List.map_cons, List.nodup_cons]
    exact ⟨hnot_in, hV.2⟩

theorem validSpkBundles_cons (S : Setup) (u : Fin S.N_id) (j : Fin S.N_recv)
    (bEntry : SpkBundleEntry) (spkBundles : List ((Nat × Nat) × SpkBundleEntry))
    (hV : ValidSpkBundles S spkBundles)
    (hFresh : spkBundles.any (fun (k, _) => k == (u.val, j.val)) = false) :
    ValidSpkBundles S (((u.val, j.val), bEntry) :: spkBundles) ∧
    ecSpkSlotIdx S (u.val, j.val) ∉ spkBundles.map (fun e => ecSpkSlotIdx S e.1) := by
  have hnot_in : ecSpkSlotIdx S (u.val, j.val) ∉ spkBundles.map (fun e => ecSpkSlotIdx S e.1) := by
    intro hmem
    rw [List.mem_map] at hmem
    rcases hmem with ⟨⟨k, b⟩, hk_mem, hk_eq⟩
    have hk_bounds := hV.1 (k, b) hk_mem
    have hkeq : k = (u.val, j.val) := ecSpkSlotIdx_inj S hk_bounds.2 j.isLt hk_eq
    have hany : spkBundles.any (fun (k', _) => k' == (u.val, j.val)) = true := by
      rw [List.any_eq_true]
      exact ⟨(k, b), hk_mem, by simp [hkeq]⟩
    rw [hFresh] at hany; cases hany
  refine ⟨⟨?_, ?_⟩, hnot_in⟩
  · intro e he
    rcases List.mem_cons.mp he with rfl | hmem
    · exact ⟨u.isLt, j.isLt⟩
    · exact hV.1 e hmem
  · rw [List.map_cons, List.nodup_cons]
    exact ⟨hnot_in, hV.2⟩

theorem validOpkEntries_cons (S : Setup) (u : Fin S.N_id) (j : Fin S.N_recv) (o : Fin S.N_opk)
    (oEntry : OpkEntry) (opkEntries : List ((Nat × Nat × Nat) × OpkEntry))
    (hV : ValidOpkEntries S opkEntries)
    (hFresh : opkEntries.any (fun (k, _) => k == (u.val, j.val, o.val)) = false) :
    ValidOpkEntries S (((u.val, j.val, o.val), oEntry) :: opkEntries) ∧
    ecOpkSlotIdx S (u.val, j.val, o.val) ∉ opkEntries.map (fun e => ecOpkSlotIdx S e.1) := by
  have hnot_in : ecOpkSlotIdx S (u.val, j.val, o.val) ∉ opkEntries.map (fun e =>
      ecOpkSlotIdx S e.1) := by
    intro hmem
    rw [List.mem_map] at hmem
    rcases hmem with ⟨⟨k, b⟩, hk_mem, hk_eq⟩
    have hk_bounds := hV.1 (k, b) hk_mem
    have hkeq : k = (u.val, j.val, o.val) :=
      ecOpkSlotIdx_inj S hk_bounds.2.1 hk_bounds.2.2 j.isLt o.isLt hk_eq
    have hany : opkEntries.any (fun (k', _) => k' == (u.val, j.val, o.val)) = true := by
      rw [List.any_eq_true]
      exact ⟨(k, b), hk_mem, by simp [hkeq]⟩
    rw [hFresh] at hany; cases hany
  refine ⟨⟨?_, ?_⟩, hnot_in⟩
  · intro e he
    rcases List.mem_cons.mp he with rfl | hmem
    · exact ⟨u.isLt, j.isLt, o.isLt⟩
    · exact hV.1 e hmem
  · rw [List.map_cons, List.nodup_cons]
    exact ⟨hnot_in, hV.2⟩

theorem validSessionIds_cons (S : Setup) (sid : SessionId S) (sids : List (SessionId S))
    (hSend : IsSendSessionId S sid)
    (hV : ValidSessionIds S sids)
    (hFresh : sids.any (fun s => s == sid) = false) :
    ValidSessionIds S (sid :: sids) ∧
    ecSessSlotIdx S sid ∉ sids.map (ecSessSlotIdx S) := by
  have hnot_in : ecSessSlotIdx S sid ∉ sids.map (ecSessSlotIdx S) := by
    intro hmem
    rw [List.mem_map] at hmem
    rcases hmem with ⟨s', hs'_mem, hs'_eq⟩
    have hseq : s' = sid := ecSessSlotIdx_inj S (hV.1 s' hs'_mem) hSend hs'_eq
    have hany : sids.any (fun s => s == sid) = true := by
      rw [List.any_eq_true]
      exact ⟨s', hs'_mem, by simp [hseq]⟩
    rw [hFresh] at hany; cases hany
  refine ⟨⟨?_, ?_⟩, hnot_in⟩
  · intro s hs
    rcases List.mem_cons.mp hs with rfl | hmem
    · exact hSend
    · exact hV.1 s hmem
  · rw [List.map_cons, List.nodup_cons]
    exact ⟨hnot_in, hV.2⟩

theorem not_mem_ecTaggedFromLists_of_fresh_prin (S : Setup) (P : Primitives)
    (u : Fin S.N_id)
    (principals : List (Nat × PrincipalEntry))
    (spkBundles : List ((Nat × Nat) × SpkBundleEntry))
    (opkEntries : List ((Nat × Nat × Nat) × OpkEntry))
    (sessPks : List (SessionId S × Bytes))
    (hNotIn : u.val ∉ principals.map Prod.fst) :
    ecPrinSlotIdx u.val ∉
      (ecTaggedFromLists S P principals spkBundles opkEntries sessPks).map Prod.fst := by
  rw [map_fst_ecTaggedFromLists]
  simp only [List.mem_append, not_or, ecPrinSlotIdx]
  refine ⟨⟨⟨hNotIn, ?_⟩, ?_⟩, ?_⟩
  · intro h; rw [List.mem_map] at h; rcases h with ⟨e, _, heq⟩
    unfold ecSpkSlotIdx at heq; have := u.isLt; omega
  · intro h; rw [List.mem_map] at h; rcases h with ⟨e, _, heq⟩
    unfold ecOpkSlotIdx at heq; have := u.isLt; omega
  · intro h; rw [List.mem_map] at h; rcases h with ⟨sid, _, heq⟩
    unfold ecSessSlotIdx at heq; have := u.isLt; omega

theorem not_mem_ecTaggedFromLists_of_fresh_spk (S : Setup) (P : Primitives)
    (u : Fin S.N_id) (j : Fin S.N_recv)
    (principals : List (Nat × PrincipalEntry))
    (spkBundles : List ((Nat × Nat) × SpkBundleEntry))
    (opkEntries : List ((Nat × Nat × Nat) × OpkEntry))
    (sessPks : List (SessionId S × Bytes))
    (hV : ValidPrincipals S principals)
    (hNotIn : ecSpkSlotIdx S (u.val, j.val) ∉ spkBundles.map (fun e => ecSpkSlotIdx S e.1)) :
    ecSpkSlotIdx S (u.val, j.val) ∉
      (ecTaggedFromLists S P principals spkBundles opkEntries sessPks).map Prod.fst := by
  rw [map_fst_ecTaggedFromLists]
  simp only [List.mem_append, not_or]
  have hlt_spk := spkSlotFlatIdx_lt S u.isLt j.isLt
  refine ⟨⟨⟨?_, hNotIn⟩, ?_⟩, ?_⟩
  · intro h; rw [List.mem_map] at h; rcases h with ⟨e, he, heq⟩
    have := hV.1 e he; unfold ecSpkSlotIdx at heq; omega
  · intro h; rw [List.mem_map] at h; rcases h with ⟨e, _, heq⟩
    unfold ecOpkSlotIdx ecSpkSlotIdx at heq; omega
  · intro h; rw [List.mem_map] at h; rcases h with ⟨sid, _, heq⟩
    unfold ecSessSlotIdx ecSpkSlotIdx at heq; omega

theorem not_mem_ecTaggedFromLists_of_fresh_opk (S : Setup) (P : Primitives)
    (u : Fin S.N_id) (j : Fin S.N_recv) (o : Fin S.N_opk)
    (principals : List (Nat × PrincipalEntry))
    (spkBundles : List ((Nat × Nat) × SpkBundleEntry))
    (opkEntries : List ((Nat × Nat × Nat) × OpkEntry))
    (sessPks : List (SessionId S × Bytes))
    (hVP : ValidPrincipals S principals)
    (hVS : ValidSpkBundles S spkBundles)
    (hNotIn : ecOpkSlotIdx S (u.val, j.val, o.val) ∉ opkEntries.map (fun e => ecOpkSlotIdx S e.1)) :
    ecOpkSlotIdx S (u.val, j.val, o.val) ∉
      (ecTaggedFromLists S P principals spkBundles opkEntries sessPks).map Prod.fst := by
  rw [map_fst_ecTaggedFromLists]
  simp only [List.mem_append, not_or]
  have hlt_opk := opkSlotFlatIdx_lt S u.isLt j.isLt o.isLt
  refine ⟨⟨⟨?_, ?_⟩, hNotIn⟩, ?_⟩
  · intro h; rw [List.mem_map] at h; rcases h with ⟨e, he, heq⟩
    have := hVP.1 e he; unfold ecOpkSlotIdx at heq; omega
  · intro h; rw [List.mem_map] at h; rcases h with ⟨⟨⟨u', j'⟩, b⟩, he, heq⟩
    have h_b := hVS.1 _ he
    have := spkSlotFlatIdx_lt S h_b.1 h_b.2
    dsimp only at *
    unfold ecOpkSlotIdx ecSpkSlotIdx at heq; omega
  · intro h; rw [List.mem_map] at h; rcases h with ⟨sid, _, heq⟩
    unfold ecSessSlotIdx ecOpkSlotIdx at heq; omega

theorem not_mem_ecTaggedFromLists_of_fresh_sess (S : Setup) (P : Primitives)
    (sid : SessionId S)
    (principals : List (Nat × PrincipalEntry))
    (spkBundles : List ((Nat × Nat) × SpkBundleEntry))
    (opkEntries : List ((Nat × Nat × Nat) × OpkEntry))
    (sessPks : List (SessionId S × Bytes))
    (hVP : ValidPrincipals S principals)
    (hVS : ValidSpkBundles S spkBundles)
    (hVO : ValidOpkEntries S opkEntries)
    (hNotIn : ecSessSlotIdx S sid ∉ (sessPks.map Prod.fst).map (ecSessSlotIdx S)) :
    ecSessSlotIdx S sid ∉
      (ecTaggedFromLists S P principals spkBundles opkEntries sessPks).map Prod.fst := by
  rw [map_fst_ecTaggedFromLists]
  simp only [List.mem_append, not_or]
  refine ⟨⟨⟨?_, ?_⟩, ?_⟩, hNotIn⟩
  · intro h; rw [List.mem_map] at h; rcases h with ⟨e, he, heq⟩
    have := hVP.1 e he; unfold ecSessSlotIdx at heq; omega
  · intro h; rw [List.mem_map] at h; rcases h with ⟨⟨⟨u', j'⟩, b⟩, he, heq⟩
    have h_b := hVS.1 _ he
    have := spkSlotFlatIdx_lt S h_b.1 h_b.2
    dsimp only at *
    unfold ecSessSlotIdx ecSpkSlotIdx at heq; omega
  · intro h; rw [List.mem_map] at h; rcases h with ⟨⟨⟨u', j', o'⟩, b⟩, he, heq⟩
    have h_b := hVO.1 _ he
    have := opkSlotFlatIdx_lt S h_b.1 h_b.2.1 h_b.2.2
    dsimp only at *
    unfold ecSessSlotIdx ecOpkSlotIdx at heq; omega

theorem probExpect_ecTaggedFromLists_cons_prin_le (S : Setup) (P : Primitives)
    (hP : CryptoWellFormedPrimitivesδ P) (u : Fin S.N_id)
    (principals : List (Nat × PrincipalEntry))
    (spkBundles : List ((Nat × Nat) × SpkBundleEntry))
    (opkEntries : List ((Nat × Nat × Nat) × OpkEntry))
    (sessPks : List (SessionId S × Bytes))
    (hNotIn : u.val ∉ principals.map Prod.fst)
    (mkEntry : Bytes → PrincipalEntry)
    (hik : ∀ sk, (mkEntry sk).ikAPk = P.x25519Base sk)
    (s1 s2 : Nat) :
    probExpect sampleScalar32 (fun sk =>
      ecPairPotential P
        (ecTaggedFromLists S P ((u.val, mkEntry sk) :: principals) spkBundles opkEntries sessPks)
        s1 s2) ≤
      ecPairPotential P (ecTaggedFromLists S P principals spkBundles opkEntries sessPks) s1 s2 := by
  have hFresh :=
      not_mem_ecTaggedFromLists_of_fresh_prin S P u principals spkBundles opkEntries sessPks hNotIn
  have heq : ∀ sk,
      ecTaggedFromLists S P ((u.val, mkEntry sk) :: principals) spkBundles opkEntries sessPks =
      [] ++ (ecPrinSlotIdx u.val, P.pow8 (P.x25519Base sk)) ::
        ecTaggedFromLists S P principals spkBundles opkEntries sessPks := by
    intro sk; simp [ecTaggedFromLists, hik sk]
  simp_rw [heq]
  exact probExpect_ecPairPotential_insert_fresh_le P hP []
    (ecTaggedFromLists S P principals spkBundles opkEntries sessPks) (ecPrinSlotIdx u.val) s1 s2
        hFresh

theorem probExpect_ecTaggedFromLists_cons_spk_le (S : Setup) (P : Primitives)
    (hP : CryptoWellFormedPrimitivesδ P) (u : Fin S.N_id) (j : Fin S.N_recv)
    (principals : List (Nat × PrincipalEntry))
    (spkBundles : List ((Nat × Nat) × SpkBundleEntry))
    (opkEntries : List ((Nat × Nat × Nat) × OpkEntry))
    (sessPks : List (SessionId S × Bytes))
    (hVP : ValidPrincipals S principals)
    (hNotIn : ecSpkSlotIdx S (u.val, j.val) ∉ spkBundles.map (fun e => ecSpkSlotIdx S e.1))
    (mkEntry : Bytes → SpkBundleEntry)
    (hspk : ∀ sk, (mkEntry sk).spkPk = P.x25519Base sk)
    (s1 s2 : Nat) :
    probExpect sampleScalar32 (fun sk =>
      ecPairPotential P
        (ecTaggedFromLists S P principals (((u.val, j.val),
            mkEntry sk) :: spkBundles) opkEntries sessPks)
        s1 s2) ≤
      ecPairPotential P (ecTaggedFromLists S P principals spkBundles opkEntries sessPks) s1 s2 := by
  let L1 := principals.map (fun (u, e) => (ecPrinSlotIdx u, P.pow8 e.ikAPk))
  let L2 := (spkBundles.map (fun (k, b) => (ecSpkSlotIdx S k, P.pow8 b.spkPk))) ++
    (opkEntries.map (fun (k, o) => (ecOpkSlotIdx S k, P.pow8 o.opkPk))) ++
    (sessPks.map (fun (sid, pk) => (ecSessSlotIdx S sid, P.pow8 pk)))
  have hL : L1 ++ L2 = ecTaggedFromLists S P principals spkBundles opkEntries sessPks := by
    simp [L1, L2, ecTaggedFromLists, List.append_assoc]
  have hFresh : ecSpkSlotIdx S (u.val, j.val) ∉ (L1 ++ L2).map Prod.fst := by
    rw [hL]
    exact not_mem_ecTaggedFromLists_of_fresh_spk S P u j principals spkBundles opkEntries sessPks
        hVP hNotIn
  have heq : ∀ sk,
      ecTaggedFromLists S P principals (((u.val, j.val),
          mkEntry sk) :: spkBundles) opkEntries sessPks =
      L1 ++ (ecSpkSlotIdx S (u.val, j.val), P.pow8 (P.x25519Base sk)) :: L2 := by
    intro sk; simp [L1, L2, ecTaggedFromLists, hspk sk, List.append_assoc]
  simp_rw [heq, ← hL]
  exact probExpect_ecPairPotential_insert_fresh_le P hP L1 L2 (ecSpkSlotIdx S (u.val,
      j.val)) s1 s2 hFresh

theorem probExpect_ecTaggedFromLists_cons_opk_le (S : Setup) (P : Primitives)
    (hP : CryptoWellFormedPrimitivesδ P) (u : Fin S.N_id) (j : Fin S.N_recv) (o : Fin S.N_opk)
    (principals : List (Nat × PrincipalEntry))
    (spkBundles : List ((Nat × Nat) × SpkBundleEntry))
    (opkEntries : List ((Nat × Nat × Nat) × OpkEntry))
    (sessPks : List (SessionId S × Bytes))
    (hVP : ValidPrincipals S principals)
    (hVS : ValidSpkBundles S spkBundles)
    (hNotIn : ecOpkSlotIdx S (u.val, j.val, o.val) ∉ opkEntries.map (fun e => ecOpkSlotIdx S e.1))
    (mkEntry : Bytes → OpkEntry)
    (hopk : ∀ sk, (mkEntry sk).opkPk = P.x25519Base sk)
    (s1 s2 : Nat) :
    probExpect sampleScalar32 (fun sk =>
      ecPairPotential P
        (ecTaggedFromLists S P principals spkBundles (((u.val, j.val, o.val),
            mkEntry sk) :: opkEntries) sessPks)
        s1 s2) ≤
      ecPairPotential P (ecTaggedFromLists S P principals spkBundles opkEntries sessPks) s1 s2 := by
  let L1 := (principals.map (fun (u, e) => (ecPrinSlotIdx u, P.pow8 e.ikAPk))) ++
    (spkBundles.map (fun (k, b) => (ecSpkSlotIdx S k, P.pow8 b.spkPk)))
  let L2 := (opkEntries.map (fun (k, o) => (ecOpkSlotIdx S k, P.pow8 o.opkPk))) ++
    (sessPks.map (fun (sid, pk) => (ecSessSlotIdx S sid, P.pow8 pk)))
  have hL : L1 ++ L2 = ecTaggedFromLists S P principals spkBundles opkEntries sessPks := by
    simp [L1, L2, ecTaggedFromLists, List.append_assoc]
  have hFresh : ecOpkSlotIdx S (u.val, j.val, o.val) ∉ (L1 ++ L2).map Prod.fst := by
    rw [hL]
    exact not_mem_ecTaggedFromLists_of_fresh_opk S P u j o principals spkBundles opkEntries
        sessPks hVP hVS hNotIn
  have heq : ∀ sk,
      ecTaggedFromLists S P principals spkBundles (((u.val, j.val, o.val),
          mkEntry sk) :: opkEntries) sessPks =
      L1 ++ (ecOpkSlotIdx S (u.val, j.val, o.val), P.pow8 (P.x25519Base sk)) :: L2 := by
    intro sk; simp [L1, L2, ecTaggedFromLists, hopk sk, List.append_assoc]
  simp_rw [heq, ← hL]
  exact probExpect_ecPairPotential_insert_fresh_le P hP L1 L2 (ecOpkSlotIdx S (u.val, j.val,
      o.val)) s1 s2 hFresh

theorem probExpect_ecTaggedFromLists_cons_sess_le (S : Setup) (P : Primitives)
    (hP : CryptoWellFormedPrimitivesδ P) (sid : SessionId S)
    (principals : List (Nat × PrincipalEntry))
    (spkBundles : List ((Nat × Nat) × SpkBundleEntry))
    (opkEntries : List ((Nat × Nat × Nat) × OpkEntry))
    (sessPks : List (SessionId S × Bytes))
    (hVP : ValidPrincipals S principals)
    (hVS : ValidSpkBundles S spkBundles)
    (hVO : ValidOpkEntries S opkEntries)
    (hNotIn : ecSessSlotIdx S sid ∉ (sessPks.map Prod.fst).map (ecSessSlotIdx S))
    (s1 s2 : Nat) :
    probExpect sampleScalar32 (fun sk =>
      ecPairPotential P
        (ecTaggedFromLists S P principals spkBundles opkEntries ((sid, P.x25519Base sk) :: sessPks))
        s1 s2) ≤
      ecPairPotential P (ecTaggedFromLists S P principals spkBundles opkEntries sessPks) s1 s2 := by
  let L1 := (principals.map (fun (u, e) => (ecPrinSlotIdx u, P.pow8 e.ikAPk))) ++
    (spkBundles.map (fun (k, b) => (ecSpkSlotIdx S k, P.pow8 b.spkPk))) ++
    (opkEntries.map (fun (k, o) => (ecOpkSlotIdx S k, P.pow8 o.opkPk)))
  let L2 := sessPks.map (fun (sid, pk) => (ecSessSlotIdx S sid, P.pow8 pk))
  have hL : L1 ++ L2 = ecTaggedFromLists S P principals spkBundles opkEntries sessPks := rfl
  have hFresh : ecSessSlotIdx S sid ∉ (L1 ++ L2).map Prod.fst :=
    not_mem_ecTaggedFromLists_of_fresh_sess S P sid principals spkBundles opkEntries sessPks hVP
        hVS hVO hNotIn
  exact probExpect_ecPairPotential_insert_fresh_le P hP L1 L2 (ecSessSlotIdx S sid) s1 s2 hFresh

theorem validPrincipals_map_corrupted (S : Setup) (P : Primitives) (uIdx : Nat)
    (principals : List (Nat × PrincipalEntry))
    (hV : ValidPrincipals S principals) :
    ValidPrincipals S (principals.map (fun (idx, e) =>
      if idx == uIdx then (idx, { e with corrupted := true }) else (idx, e))) ∧
    (principals.map (fun (idx, e) =>
      if idx == uIdx then (idx, { e with corrupted := true }) else (idx, e))).map
        (fun (u, e) => (ecPrinSlotIdx u, P.pow8 e.ikAPk)) =
      principals.map (fun (u, e) => (ecPrinSlotIdx u, P.pow8 e.ikAPk)) := by
  have h_fst :
      (principals.map (fun (idx, e) =>
        if idx == uIdx then (idx, { e with corrupted := true }) else (idx, e))).map Prod.fst =
      principals.map Prod.fst := by
    rw [List.map_map]
    refine List.map_congr_left (fun ⟨idx, e⟩ _ => ?_)
    dsimp; split_ifs <;> rfl
  have h_pk :
      (principals.map (fun (idx, e) =>
        if idx == uIdx then (idx, { e with corrupted := true }) else (idx, e))).map
          (fun (u, e) => (ecPrinSlotIdx u, P.pow8 e.ikAPk)) =
      principals.map (fun (u, e) => (ecPrinSlotIdx u, P.pow8 e.ikAPk)) := by
    rw [List.map_map]
    refine List.map_congr_left (fun ⟨idx, e⟩ _ => ?_)
    dsimp; split_ifs <;> rfl
  refine ⟨⟨?_, ?_⟩, h_pk⟩
  · intro x hx
    have hx_fst : x.1 ∈ principals.map Prod.fst := by
      rw [← h_fst]; exact List.mem_map_of_mem hx
    rw [List.mem_map] at hx_fst
    rcases hx_fst with ⟨e, he, heq⟩
    rw [← heq]; exact hV.1 e he
  · rw [h_fst]; exact hV.2

theorem validOpkEntries_map_consumed (S : Setup) (P : Primitives) (key : Nat × Nat × Nat)
    (opkEntries : List ((Nat × Nat × Nat) × OpkEntry))
    (hV : ValidOpkEntries S opkEntries) :
    ValidOpkEntries S (opkEntries.map (fun (idx, e) =>
      if idx == key then (idx, { e with consumed := true }) else (idx, e))) ∧
    (opkEntries.map (fun (idx, e) =>
      if idx == key then (idx, { e with consumed := true }) else (idx, e))).map
        (fun (k, o) => (ecOpkSlotIdx S k, P.pow8 o.opkPk)) =
      opkEntries.map (fun (k, o) => (ecOpkSlotIdx S k, P.pow8 o.opkPk)) := by
  have h_fst :
      (opkEntries.map (fun (idx, e) =>
        if idx == key then (idx, { e with consumed := true }) else (idx, e))).map Prod.fst =
      opkEntries.map Prod.fst := by
    rw [List.map_map]
    refine List.map_congr_left (fun ⟨idx, e⟩ _ => ?_)
    dsimp; split_ifs <;> rfl
  have h_slot :
      (opkEntries.map (fun (idx, e) =>
        if idx == key then (idx, { e with consumed := true }) else (idx, e))).map
          (fun e => ecOpkSlotIdx S e.1) =
      opkEntries.map (fun e => ecOpkSlotIdx S e.1) := by
    rw [List.map_map]
    refine List.map_congr_left (fun ⟨idx, e⟩ _ => ?_)
    dsimp; split_ifs <;> rfl
  have h_pk :
      (opkEntries.map (fun (idx, e) =>
        if idx == key then (idx, { e with consumed := true }) else (idx, e))).map
          (fun (k, o) => (ecOpkSlotIdx S k, P.pow8 o.opkPk)) =
      opkEntries.map (fun (k, o) => (ecOpkSlotIdx S k, P.pow8 o.opkPk)) := by
    rw [List.map_map]
    refine List.map_congr_left (fun ⟨idx, e⟩ _ => ?_)
    dsimp; split_ifs <;> rfl
  refine ⟨⟨?_, ?_⟩, h_pk⟩
  · intro x hx
    have hx_fst : x.1 ∈ opkEntries.map Prod.fst := by
      rw [← h_fst]; exact List.mem_map_of_mem hx
    rw [List.mem_map] at hx_fst
    rcases hx_fst with ⟨e, he, heq⟩
    rw [← heq]; exact hV.1 e he
  · rw [h_slot]; exact hV.2

theorem validSpkBundles_map_revealed (S : Setup) (P : Primitives) (key : Nat × Nat)
    (spkBundles : List ((Nat × Nat) × SpkBundleEntry))
    (hV : ValidSpkBundles S spkBundles) :
    ValidSpkBundles S (spkBundles.map (fun (idx, e) =>
      if idx == key then (idx, { e with revealed := true }) else (idx, e))) ∧
    (spkBundles.map (fun (idx, e) =>
      if idx == key then (idx, { e with revealed := true }) else (idx, e))).map
        (fun (k, b) => (ecSpkSlotIdx S k, P.pow8 b.spkPk)) =
      spkBundles.map (fun (k, b) => (ecSpkSlotIdx S k, P.pow8 b.spkPk)) := by
  have h_fst :
      (spkBundles.map (fun (idx, e) =>
        if idx == key then (idx, { e with revealed := true }) else (idx, e))).map Prod.fst =
      spkBundles.map Prod.fst := by
    rw [List.map_map]
    refine List.map_congr_left (fun ⟨idx, e⟩ _ => ?_)
    dsimp; split_ifs <;> rfl
  have h_slot :
      (spkBundles.map (fun (idx, e) =>
        if idx == key then (idx, { e with revealed := true }) else (idx, e))).map
          (fun e => ecSpkSlotIdx S e.1) =
      spkBundles.map (fun e => ecSpkSlotIdx S e.1) := by
    rw [List.map_map]
    refine List.map_congr_left (fun ⟨idx, e⟩ _ => ?_)
    dsimp; split_ifs <;> rfl
  have h_pk :
      (spkBundles.map (fun (idx, e) =>
        if idx == key then (idx, { e with revealed := true }) else (idx, e))).map
          (fun (k, b) => (ecSpkSlotIdx S k, P.pow8 b.spkPk)) =
      spkBundles.map (fun (k, b) => (ecSpkSlotIdx S k, P.pow8 b.spkPk)) := by
    rw [List.map_map]
    refine List.map_congr_left (fun ⟨idx, e⟩ _ => ?_)
    dsimp; split_ifs <;> rfl
  refine ⟨⟨?_, ?_⟩, h_pk⟩
  · intro x hx
    have hx_fst : x.1 ∈ spkBundles.map Prod.fst := by
      rw [← h_fst]; exact List.mem_map_of_mem hx
    rw [List.mem_map] at hx_fst
    rcases hx_fst with ⟨e, he, heq⟩
    rw [← heq]; exact hV.1 e he
  · rw [h_slot]; exact hV.2

/-! ## `KeyInd` EC collision step -/

def sessPksKeyInd (S : Setup) (st : KeyIndState S) : List (SessionId S × Bytes) :=
  st.sessions.map (fun s => (s.sid, s.hdr.ekAPk))

def ecTaggedKeyInd (S : Setup) (P : Primitives) (st : KeyIndState S) : List (Nat × Bytes) :=
  ecTaggedFromLists S P st.principals st.spkBundles st.opkEntries (sessPksKeyInd S st)

def ValidKeyIndEc (S : Setup) (st : KeyIndState S) : Prop :=
  ValidEcLists S st.principals st.spkBundles st.opkEntries ((sessPksKeyInd S st).map Prod.fst)

theorem map_snd_ecTaggedKeyInd (S : Setup) (P : Primitives) (st : KeyIndState S) :
    (ecTaggedKeyInd S P st).map Prod.snd = allHonestEcPksKeyInd P st := by
  unfold ecTaggedKeyInd ecTaggedFromLists sessPksKeyInd allHonestEcPksKeyInd
  simp [HasKeyIndState.toKeyIndState, List.map_append, List.map_map, Function.comp_def]

theorem runKeyIndInitiate_ec_step (useRo : Bool) (S : Setup) (P : Primitives)
    (hP : CryptoWellFormedPrimitivesδ P)
    (sid : SessionId S) (hSend : IsSendSessionId S sid) (u : Fin S.N_id) (bundle :
        PreKeyBundleInput)
    (st : KeyIndState S) (s1 s2 : Nat)
    (hV : ValidKeyIndEc S st) :
    (∀ x ∈ support ((runKeyIndInitiate useRo S P sid u bundle).run st), ValidKeyIndEc S x.2) ∧
    probExpect ((runKeyIndInitiate useRo S P sid u bundle).run st)
      (fun x => ecPairPotential P (ecTaggedKeyInd S P x.2) s1 s2) ≤
      ecPairPotential P (ecTaggedKeyInd S P st) s1 s2 := by
  rcases hV with ⟨hVP, hVS, hVO, hVSess⟩
  unfold runKeyIndInitiate; dsimp only
  simp only [StateT.run_bind, StateT.run_get, pure_bind]
  cases hFresh : st.sessions.any (fun e => e.sid == sid)
  · simp only [Bool.false_eq_true, ↓reduceIte]
    have hFresh' : ((sessPksKeyInd S st).map Prod.fst).any (fun s => s == sid) = false := by
      simpa [sessPksKeyInd, List.any_map, Function.comp_def] using hFresh
    have hCons :=
        validSessionIds_cons S sid ((sessPksKeyInd S st).map Prod.fst) hSend hVSess hFresh'
    cases st.principals.find? (fun (idx, _) => idx == u.val) with
    | none =>
      simp [StateT.run_pure, probExpect_pure, ValidKeyIndEc, ValidEcLists, hVP, hVS, hVO, hVSess]
    | some p =>
      rcases p with ⟨_, uEntry⟩
      dsimp only
      cases !koskBundleOk P st.principals st.spkBundles st.opkEntries st.advKeys bundle
      · simp only [Bool.false_eq_true, ↓reduceIte, StateT.run_bind, StateT.run_monadLift,
        monadLift_self, bind_assoc, pure_bind]
        cases hSig : !(P.sigVerify (resolveSigPk P st.principals bundle.ikB) (encodeEC
            bundle.spkB) bundle.spkSig &&
            P.sigVerify (resolveSigPk P st.principals bundle.ikB) (encodeKEM bundle.pqspkB)
                bundle.pqspkSig)
        · simp only [Bool.false_eq_true, ↓reduceIte]
          refine ⟨?_, ?_⟩
          · intro x hx
            simp only [MonadAttach.mem_support_bind] at hx
            rcases hx with ⟨ekASk, _, kemCoins, _, hx⟩
            cases hEnc : P.kemEncaps bundle.pqspkB kemCoins with
            | none =>
              rw [hEnc] at hx
              simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff] at hx
              subst hx; exact ⟨hVP, hVS, hVO, hVSess⟩
            | some val =>
              rcases val with ⟨ss, kemCt⟩
              rw [hEnc] at hx
              dsimp only at hx
              simp only [StateT.run_bind, StateT.run_monadLift, monadLift_self,
                bind_assoc, pure_bind, MonadAttach.mem_support_bind] at hx
              rcases hx with ⟨⟨drKeyReal, roCache'⟩, _, hx⟩
              split at hx <;>
                simp only [StateT.run_bind, StateT.run_monadLift, monadLift_self, StateT.run_set,
                  bind_assoc, pure_bind, MonadAttach.mem_support_bind] at hx
              swap; rcases hx with ⟨drKeyRand, _, hx⟩; all_goals
              have hx_st : x.2.principals = st.principals ∧ x.2.spkBundles = st.spkBundles ∧
                  x.2.opkEntries = st.opkEntries ∧
                  (sessPksKeyInd S x.2).map Prod.fst =
                      sid :: (sessPksKeyInd S st).map Prod.fst := by
                cases hHon : findHonestPrincipal P st.principals bundle.ikB <;> (
                  rw [hHon] at hx
                  simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff] at hx
                  subst hx
                  simp [sessPksKeyInd])
              rcases hx_st with ⟨hp1, hp2, hp3, hp4⟩
              exact ⟨hp1 ▸ hVP, hp2 ▸ hVS, hp3 ▸ hVO, hp4 ▸ hCons.1⟩
          · simp only [probExpect_bind]
            rw [probExpect_swap sampleScalar32 sampleCoins32]
            apply probExpect_const_le_of_support; intro kemCoins _
            cases P.kemEncaps bundle.pqspkB kemCoins with
            | none =>
              simp only [StateT.run_pure, probExpect_pure]
              exact probExpect_const_le_of_support _ _ _ (fun _ _ => le_rfl)
            | some val =>
              rcases val with ⟨ss, kemCt⟩
              dsimp only
              refine le_trans (probExpect_mono_of_support sampleScalar32 _
                (fun ekASk => ecPairPotential P
                  (ecTaggedFromLists S P st.principals st.spkBundles st.opkEntries
                    ((sid, P.x25519Base ekASk) :: sessPksKeyInd S st)) s1 s2) ?_) ?_
              · intro ekASk _
                apply probExpect_const_le_of_support; intro x hx
                simp only [StateT.run_bind, StateT.run_monadLift, monadLift_self,
                  bind_assoc, pure_bind, MonadAttach.mem_support_bind] at hx
                rcases hx with ⟨⟨drKeyReal, roCache'⟩, _, hx⟩
                split at hx <;>
                  simp only [StateT.run_bind, StateT.run_monadLift, monadLift_self, StateT.run_set,
                    bind_assoc, pure_bind, MonadAttach.mem_support_bind] at hx
                swap; rcases hx with ⟨drKeyRand, _, hx⟩; all_goals
                cases hHon : findHonestPrincipal P st.principals bundle.ikB <;> (
                  rw [hHon] at hx
                  simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff] at hx
                  subst hx
                  simp [ecTaggedKeyInd, sessPksKeyInd])
              · exact probExpect_ecTaggedFromLists_cons_sess_le S P hP sid
                  st.principals st.spkBundles st.opkEntries (sessPksKeyInd S st)
                  hVP hVS hVO hCons.2 s1 s2
        · simp only [↓reduceIte, StateT.run_pure, probExpect_bind, probExpect_pure]
          refine ⟨?_, ?_⟩
          · intro x hx
            simp only [MonadAttach.mem_support_bind, support_pure, Set.mem_singleton_iff] at hx
            rcases hx with ⟨_, _, _, _, rfl⟩
            exact ⟨hVP, hVS, hVO, hVSess⟩
          · apply probExpect_const_le_of_support; intro _ _
            exact probExpect_const_le_of_support _ _ _ (fun _ _ => le_rfl)
      · simp [StateT.run_pure, probExpect_pure, ValidKeyIndEc, ValidEcLists, hVP, hVS, hVO, hVSess]
  · simp [StateT.run_pure, probExpect_pure, ValidKeyIndEc, ValidEcLists, hVP, hVS, hVO, hVSess]

theorem pqxdhKeyIndImpl_ec_step (useRo : Bool) (S : Setup) (P : Primitives)
    (hP : CryptoWellFormedPrimitivesδ P)
    (q : KeyIndQuery S) (st : KeyIndState S) (s1 s2 : Nat)
    (hV : ValidKeyIndEc S st) :
    (∀ x ∈ support ((pqxdhKeyIndImpl useRo S P q).run st), ValidKeyIndEc S x.2) ∧
    probExpect ((pqxdhKeyIndImpl useRo S P q).run st)
      (fun x => ecPairPotential P (ecTaggedKeyInd S P x.2) s1 s2) ≤
      ecPairPotential P (ecTaggedKeyInd S P st) s1 s2 := by
  let proj := fun s : KeyIndState S => (s.principals, s.spkBundles, s.opkEntries, s.sessions)
  have h_from_proj : ∀ s : KeyIndState S, proj s = proj st →
      ValidKeyIndEc S s ∧ ecTaggedKeyInd S P s = ecTaggedKeyInd S P st := by
    intro s hs
    have hp : s.principals = st.principals := congrArg Prod.fst hs
    have hsb : s.spkBundles = st.spkBundles := congrArg (Prod.fst ∘ Prod.snd) hs
    have hop : s.opkEntries = st.opkEntries := congrArg (Prod.fst ∘ Prod.snd ∘ Prod.snd) hs
    have hss : s.sessions = st.sessions := congrArg (Prod.snd ∘ Prod.snd ∘ Prod.snd) hs
    refine ⟨?_, ?_⟩
    · unfold ValidKeyIndEc ValidEcLists sessPksKeyInd at hV ⊢; rw [hp, hsb, hop, hss]; exact hV
    · unfold ecTaggedKeyInd sessPksKeyInd; rw [hp, hsb, hop, hss]
  rcases hV with ⟨hVP, hVS, hVO, hVSess⟩
  cases q with
  | initPrin u =>
    unfold pqxdhKeyIndImpl; dsimp only
    simp only [StateT.run_bind, StateT.run_get, pure_bind]
    cases hFresh : st.principals.any (fun (idx, _) => idx == u.val)
    · simp only [Bool.false_eq_true, ↓reduceIte, StateT.run_bind, StateT.run_monadLift,
        monadLift_self, StateT.run_set, StateT.run_pure, bind_assoc, pure_bind]
      refine ⟨?_, ?_⟩
      · intro x hx
        simp only [MonadAttach.mem_support_bind, support_pure, Set.mem_singleton_iff] at hx
        rcases hx with ⟨secIKA0, _, secIKAsign, _, rfl⟩
        exact ⟨(validPrincipals_cons S u _ st.principals hVP hFresh).1, hVS, hVO, hVSess⟩
      · simp only [probExpect_bind, probExpect_pure]
        rw [probExpect_swap sampleScalar32 sampleScalar32]
        apply probExpect_const_le_of_support
        intro secIKAsign _
        have hNotIn := (validPrincipals_cons S u
          { secIKA0 := [], ikAPk := [], secIKAsign := [], ikSignPk := [], corrupted := false }
          st.principals hVP hFresh).2
        exact probExpect_ecTaggedFromLists_cons_prin_le S P hP u
          st.principals st.spkBundles st.opkEntries (sessPksKeyInd S st) hNotIn
          (fun sk => {
            secIKA0 := sk, ikAPk := P.x25519Base sk,
            secIKAsign := secIKAsign, ikSignPk := P.sigPkGen secIKAsign, corrupted := false })
          (fun _ => rfl) s1 s2
    · simp [StateT.run_pure, probExpect_pure, ValidKeyIndEc, ValidEcLists, hVP, hVS, hVO, hVSess]
  | corruptIK u =>
    unfold pqxdhKeyIndImpl; dsimp only
    simp only [StateT.run_bind, StateT.run_get, pure_bind]
    cases st.principals.find? (fun (idx, _) => idx == u.val) with
    | none =>
      simp [StateT.run_pure, probExpect_pure, ValidKeyIndEc, ValidEcLists, hVP, hVS, hVO, hVSess]
    | some p =>
      rcases p with ⟨_, entry⟩
      dsimp only
      simp only [StateT.run_bind, StateT.run_set, StateT.run_pure, pure_bind, probExpect_pure]
      have h_corr := validPrincipals_map_corrupted S P u.val st.principals hVP
      refine ⟨?_, ?_⟩
      · intro x hx
        simp only [support_pure, Set.mem_singleton_iff] at hx; subst hx
        exact ⟨h_corr.1, hVS, hVO, hVSess⟩
      · unfold ecTaggedKeyInd ecTaggedFromLists
        dsimp only [sessPksKeyInd]
        rw [h_corr.2]
  | genSPK u j =>
    unfold pqxdhKeyIndImpl; dsimp only
    simp only [StateT.run_bind, StateT.run_get, pure_bind]
    cases hFresh : st.spkBundles.any (fun (k, _) => k == (u.val, j.val))
    · simp only [Bool.false_eq_true, ↓reduceIte]
      cases st.principals.find? (fun (idx, _) => idx == u.val) with
      | none =>
        simp [StateT.run_pure, probExpect_pure, ValidKeyIndEc, ValidEcLists, hVP, hVS, hVO, hVSess]
      | some p =>
        rcases p with ⟨_, uEntry⟩
        dsimp only
        simp only [StateT.run_bind, StateT.run_monadLift, monadLift_self, StateT.run_set,
          StateT.run_pure, bind_assoc, pure_bind]
        refine ⟨?_, ?_⟩
        · intro x hx
          simp only [MonadAttach.mem_support_bind, support_pure, Set.mem_singleton_iff] at hx
          rcases hx with ⟨spkSk, _, rSpk, _, ⟨pqspkPk, pqspkSk⟩, _, rPq, _, rfl⟩
          exact ⟨hVP, (validSpkBundles_cons S u j _ st.spkBundles hVS hFresh).1, hVO, hVSess⟩
        · simp only [probExpect_bind, probExpect_pure]
          rw [probExpect_swap sampleScalar32 sampleRandom64]
          apply probExpect_const_le_of_support; intro rSpk _
          rw [probExpect_swap sampleScalar32 (sampleKemKeyGen P)]
          apply probExpect_const_le_of_support; rintro ⟨pqspkPk, pqspkSk⟩ _
          rw [probExpect_swap sampleScalar32 sampleRandom64]
          apply probExpect_const_le_of_support; intro rPq _
          have hNotIn := (validSpkBundles_cons S u j
            { spkSk := [], spkPk := [], spkSig := [], pqspkSk := [], pqspkPk := [], pqspkSig := [] }
            st.spkBundles hVS hFresh).2
          exact probExpect_ecTaggedFromLists_cons_spk_le S P hP u j
            st.principals st.spkBundles st.opkEntries (sessPksKeyInd S st) hVP hNotIn
            (fun spkSk => {
              spkSk := spkSk, spkPk := P.x25519Base spkSk,
              spkSig := P.sigSign uEntry.secIKAsign (encodeEC (P.x25519Base spkSk)) rSpk,
              pqspkSk := pqspkSk, pqspkPk := pqspkPk,
              pqspkSig := P.sigSign uEntry.secIKAsign (encodeKEM pqspkPk) rPq })
            (fun _ => rfl) s1 s2
    · simp [StateT.run_pure, probExpect_pure, ValidKeyIndEc, ValidEcLists, hVP, hVS, hVO, hVSess]
  | genOPK u j o =>
    unfold pqxdhKeyIndImpl; dsimp only
    simp only [StateT.run_bind, StateT.run_get, pure_bind]
    cases hFresh : st.opkEntries.any (fun (k, _) => k == (u.val, j.val, o.val))
    · simp only [Bool.false_eq_true, ↓reduceIte, StateT.run_bind, StateT.run_monadLift,
        monadLift_self, StateT.run_set, StateT.run_pure, bind_assoc, pure_bind]
      refine ⟨?_, ?_⟩
      · intro x hx
        simp only [MonadAttach.mem_support_bind, support_pure, Set.mem_singleton_iff] at hx
        rcases hx with ⟨opkSk, _, rfl⟩
        exact ⟨hVP, hVS, (validOpkEntries_cons S u j o _ st.opkEntries hVO hFresh).1, hVSess⟩
      · simp only [probExpect_bind, probExpect_pure]
        have hNotIn := (validOpkEntries_cons S u j o
          { opkSk := [], opkPk := [], consumed := false }
          st.opkEntries hVO hFresh).2
        exact probExpect_ecTaggedFromLists_cons_opk_le S P hP u j o
          st.principals st.spkBundles st.opkEntries (sessPksKeyInd S st) hVP hVS hNotIn
          (fun opkSk => { opkSk := opkSk, opkPk := P.x25519Base opkSk, consumed := false })
          (fun _ => rfl) s1 s2
    · simp [StateT.run_pure, probExpect_pure, ValidKeyIndEc, ValidEcLists, hVP, hVS, hVO, hVSess]
  | initiateOPK u i bundle =>
    unfold pqxdhKeyIndImpl; dsimp only
    simp only [StateT.run_bind, StateT.run_get, pure_bind]
    cases bundle.opkB?.isNone
    · simp only [Bool.false_eq_true, ↓reduceIte]
      exact runKeyIndInitiate_ec_step useRo S P hP (.sendOPK u i) trivial u bundle st s1 s2 ⟨hVP,
          hVS, hVO, hVSess⟩
    · simp [StateT.run_pure, probExpect_pure, ValidKeyIndEc, ValidEcLists, hVP, hVS, hVO, hVSess]
  | initiateNoOPK u i bundle =>
    unfold pqxdhKeyIndImpl; dsimp only
    simp only [StateT.run_bind, StateT.run_get, pure_bind]
    cases bundle.opkB?.isSome
    · simp only [Bool.false_eq_true, ↓reduceIte]
      exact runKeyIndInitiate_ec_step useRo S P hP (.sendNoOPK u i) trivial u bundle st s1 s2
          ⟨hVP, hVS, hVO, hVSess⟩
    · simp [StateT.run_pure, probExpect_pure, ValidKeyIndEc, ValidEcLists, hVP, hVS, hVO, hVSess]
  | acceptOPK k j o hdr =>
    let projOpk := fun s : KeyIndState S =>
      (s.principals, s.spkBundles,
       s.opkEntries.map (fun (idx, o) => (ecOpkSlotIdx S idx, P.pow8 o.opkPk)),
       s.opkEntries.map Prod.fst,
       s.sessions)
    have h_step : ∀ (s : KeyIndState S) u t rc,
        projOpk { s with
          opkEntries := s.opkEntries.map (fun (idx, e) =>
            if idx == (k.val, j.val, o.val) then (idx, { e with consumed := true }) else (idx, e))
          usedRecvOPK := u, seenKyberBaseKeys := t, roCache := rc } = projOpk s := by
      intro s u t rc
      refine Prod.ext rfl (Prod.ext rfl (Prod.ext ?_ (Prod.ext ?_ rfl))) <;> (
        dsimp only [projOpk]
        rw [List.map_map]
        refine List.map_congr_left (fun ⟨idx, e⟩ _ => ?_)
        simp only [Function.comp_def]; split_ifs <;> rfl)
    have hp : PreservesAt projOpk st (pqxdhKeyIndImpl useRo S P (.acceptOPK k j o hdr)) := by
      unfold pqxdhKeyIndImpl; dsimp only
      repeat (first
        | with_reducible apply PreservesAt.pure
        | with_reducible apply PreservesAt.get_bind
        | (with_reducible apply PreservesAt.liftM_bind; intro _)
        | ((with_reducible apply PreservesAt.recordKeyIndResp_pure); intro _; rfl)
        | ((with_reducible apply PreservesAt.set_bind); exact h_step _ _ _ _)
        | split)
    suffices h_supp : ∀ x ∈ support ((pqxdhKeyIndImpl useRo S P (.acceptOPK k j o hdr)).run st),
        ValidKeyIndEc S x.2 ∧ ecTaggedKeyInd S P x.2 = ecTaggedKeyInd S P st by
      refine ⟨fun x hx => (h_supp x hx).1, ?_⟩
      exact probExpect_const_le_of_support _ _ _ (fun x hx => by rw [(h_supp x hx).2])
    intro x hx
    have h_eq := hp x hx
    have hp1 : x.2.principals = st.principals := congrArg Prod.fst h_eq
    have hp2 : x.2.spkBundles = st.spkBundles := congrArg (Prod.fst ∘ Prod.snd) h_eq
    have hp3 : x.2.opkEntries.map (fun (idx, o) => (ecOpkSlotIdx S idx, P.pow8 o.opkPk)) =
        st.opkEntries.map (fun (idx, o) => (ecOpkSlotIdx S idx, P.pow8 o.opkPk)) :=
      congrArg (Prod.fst ∘ Prod.snd ∘ Prod.snd) h_eq
    have hp4 : x.2.opkEntries.map Prod.fst = st.opkEntries.map Prod.fst :=
      congrArg (Prod.fst ∘ Prod.snd ∘ Prod.snd ∘ Prod.snd) h_eq
    have hp5 : sessPksKeyInd S x.2 = sessPksKeyInd S st := by
      have hsess : x.2.sessions = st.sessions :=
        congrArg (Prod.snd ∘ Prod.snd ∘ Prod.snd ∘ Prod.snd) h_eq
      unfold sessPksKeyInd; rw [hsess]
    refine ⟨⟨hp1 ▸ hVP, hp2 ▸ hVS, ⟨?_, ?_⟩, hp5 ▸ hVSess⟩, ?_⟩
    · intro e he
      have he_fst : e.1 ∈ st.opkEntries.map Prod.fst := by
        rw [← hp4]; exact List.mem_map_of_mem he
      rw [List.mem_map] at he_fst
      rcases he_fst with ⟨e', he', heq⟩
      rw [← heq]; exact hVO.1 e' he'
    · have h_slot : x.2.opkEntries.map (fun e => ecOpkSlotIdx S e.1) =
          st.opkEntries.map (fun e => ecOpkSlotIdx S e.1) := by
        simpa [List.map_map, Function.comp_def] using congrArg (List.map (ecOpkSlotIdx S)) hp4
      rw [h_slot]; exact hVO.2
    · unfold ecTaggedKeyInd ecTaggedFromLists
      rw [hp1, hp2, hp3, hp5]
  | acceptNoOPK k j l hdr =>
    have hp : PreservesAt proj st (pqxdhKeyIndImpl useRo S P (.acceptNoOPK k j l hdr)) := by
      unfold pqxdhKeyIndImpl; dsimp only
      repeat (first
        | with_reducible apply PreservesAt.pure
        | with_reducible apply PreservesAt.get_bind
        | (with_reducible apply PreservesAt.liftM_bind; intro _)
        | ((with_reducible apply PreservesAt.recordKeyIndResp_pure); intro _; rfl)
        | ((with_reducible apply PreservesAt.set_bind); rfl)
        | split)
    refine ⟨fun x hx => (h_from_proj x.2 (hp x hx)).1, ?_⟩
    exact probExpect_const_le_of_support _ _ _ (fun x hx => by rw [(h_from_proj x.2 (hp x hx)).2])
  | testSession sid =>
    let projTest := fun s : KeyIndState S =>
      (s.principals, s.spkBundles, s.opkEntries, sessPksKeyInd S s)
    have h_step : ∀ (s : KeyIndState S),
        projTest { s with sessions := s.sessions.map (fun e =>
          if e.sid == sid then { e with tested := true } else e) } = projTest s := by
      intro s
      refine Prod.ext rfl (Prod.ext rfl (Prod.ext rfl ?_))
      dsimp only [projTest, sessPksKeyInd]
      rw [List.map_map]
      refine List.map_congr_left (fun e _ => ?_)
      simp only [Function.comp_def]; split_ifs <;> rfl
    have hp : PreservesAt projTest st (pqxdhKeyIndImpl useRo S P (.testSession sid)) := by
      unfold pqxdhKeyIndImpl; dsimp only
      repeat (first
        | with_reducible apply PreservesAt.pure
        | with_reducible apply PreservesAt.get_bind
        | ((with_reducible apply PreservesAt.set_bind); rfl)
        | ((with_reducible apply PreservesAt.set_bind); exact h_step _)
        | (split; try dsimp only))
    suffices h_supp : ∀ x ∈ support ((pqxdhKeyIndImpl useRo S P (.testSession sid)).run st),
        ValidKeyIndEc S x.2 ∧ ecTaggedKeyInd S P x.2 = ecTaggedKeyInd S P st by
      refine ⟨fun x hx => (h_supp x hx).1, ?_⟩
      exact probExpect_const_le_of_support _ _ _ (fun x hx => by rw [(h_supp x hx).2])
    intro x hx
    have h_eq := hp x hx
    have hp1 : x.2.principals = st.principals := congrArg Prod.fst h_eq
    have hp2 : x.2.spkBundles = st.spkBundles := congrArg (Prod.fst ∘ Prod.snd) h_eq
    have hp3 : x.2.opkEntries = st.opkEntries := congrArg (Prod.fst ∘ Prod.snd ∘ Prod.snd) h_eq
    have hp4 : sessPksKeyInd S x.2 = sessPksKeyInd S st :=
        congrArg (Prod.snd ∘ Prod.snd ∘ Prod.snd) h_eq
    refine ⟨⟨hp1 ▸ hVP, hp2 ▸ hVS, hp3 ▸ hVO, hp4 ▸ hVSess⟩, ?_⟩
    unfold ecTaggedKeyInd; rw [hp1, hp2, hp3, hp4]
  | revealSessionKey sid =>
    let projTest := fun s : KeyIndState S =>
      (s.principals, s.spkBundles, s.opkEntries, sessPksKeyInd S s)
    have h_step : ∀ (s : KeyIndState S),
        projTest { s with sessions := s.sessions.map (fun e =>
          if e.sid == sid then { e with revealed := true } else e) } = projTest s := by
      intro s
      refine Prod.ext rfl (Prod.ext rfl (Prod.ext rfl ?_))
      dsimp only [projTest, sessPksKeyInd]
      rw [List.map_map]
      refine List.map_congr_left (fun e _ => ?_)
      simp only [Function.comp_def]; split_ifs <;> rfl
    have hp : PreservesAt projTest st (pqxdhKeyIndImpl useRo S P (.revealSessionKey sid)) := by
      unfold pqxdhKeyIndImpl; dsimp only
      repeat (first
        | with_reducible apply PreservesAt.pure
        | with_reducible apply PreservesAt.get_bind
        | ((with_reducible apply PreservesAt.set_bind); rfl)
        | ((with_reducible apply PreservesAt.set_bind); exact h_step _)
        | (split; try dsimp only))
    suffices h_supp : ∀ x ∈ support ((pqxdhKeyIndImpl useRo S P (.revealSessionKey sid)).run st),
        ValidKeyIndEc S x.2 ∧ ecTaggedKeyInd S P x.2 = ecTaggedKeyInd S P st by
      refine ⟨fun x hx => (h_supp x hx).1, ?_⟩
      exact probExpect_const_le_of_support _ _ _ (fun x hx => by rw [(h_supp x hx).2])
    intro x hx
    have h_eq := hp x hx
    have hp1 : x.2.principals = st.principals := congrArg Prod.fst h_eq
    have hp2 : x.2.spkBundles = st.spkBundles := congrArg (Prod.fst ∘ Prod.snd) h_eq
    have hp3 : x.2.opkEntries = st.opkEntries := congrArg (Prod.fst ∘ Prod.snd ∘ Prod.snd) h_eq
    have hp4 : sessPksKeyInd S x.2 = sessPksKeyInd S st :=
        congrArg (Prod.snd ∘ Prod.snd ∘ Prod.snd) h_eq
    refine ⟨⟨hp1 ▸ hVP, hp2 ▸ hVS, hp3 ▸ hVO, hp4 ▸ hVSess⟩, ?_⟩
    unfold ecTaggedKeyInd; rw [hp1, hp2, hp3, hp4]
  | roQuery secrets =>
    have hp : PreservesAt proj st (pqxdhKeyIndImpl useRo S P (.roQuery secrets)) := by
      unfold pqxdhKeyIndImpl; dsimp only
      repeat (first
        | with_reducible apply PreservesAt.pure
        | with_reducible apply PreservesAt.get_bind
        | (with_reducible apply PreservesAt.liftM_bind; intro _)
        | (with_reducible apply PreservesAt.set_bind; rfl)
        | split)
    refine ⟨fun x hx => (h_from_proj x.2 (hp x hx)).1, ?_⟩
    exact probExpect_const_le_of_support _ _ _ (fun x hx => by rw [(h_from_proj x.2 (hp x hx)).2])
  | revealDhSecrets =>
    have hp : PreservesAt proj st (pqxdhKeyIndImpl useRo S P .revealDhSecrets) := by
      unfold pqxdhKeyIndImpl; dsimp only
      repeat (first
        | with_reducible apply PreservesAt.pure
        | with_reducible apply PreservesAt.get_bind
        | split)
    refine ⟨fun x hx => (h_from_proj x.2 (hp x hx)).1, ?_⟩
    exact probExpect_const_le_of_support _ _ _ (fun x hx => by rw [(h_from_proj x.2 (hp x hx)).2])
  | registerKey sk =>
    have hp : PreservesAt proj st (pqxdhKeyIndImpl useRo S P (.registerKey sk)) := by
      unfold pqxdhKeyIndImpl; dsimp only
      repeat (first
        | with_reducible apply PreservesAt.pure
        | with_reducible apply PreservesAt.get_bind
        | (with_reducible apply PreservesAt.set_bind; rfl)
        | (split; try dsimp only))
    refine ⟨fun x hx => (h_from_proj x.2 (hp x hx)).1, ?_⟩
    exact probExpect_const_le_of_support _ _ _ (fun x hx => by rw [(h_from_proj x.2 (hp x hx)).2])
  | revealSpkSk u j =>
    unfold pqxdhKeyIndImpl; dsimp only
    simp only [StateT.run_bind, StateT.run_get, pure_bind]
    cases st.spkBundles.find? (fun (idx, _) => idx == (u.val, j.val)) with
    | none =>
      simp [StateT.run_pure, probExpect_pure, ValidKeyIndEc, ValidEcLists, hVP, hVS, hVO, hVSess]
    | some bp =>
      rcases bp with ⟨_, bEntry⟩
      dsimp only
      simp only [StateT.run_bind, StateT.run_set, StateT.run_pure, pure_bind, probExpect_pure]
      have h_rev := validSpkBundles_map_revealed S P (u.val, j.val) st.spkBundles hVS
      refine ⟨?_, ?_⟩
      · intro x hx
        simp only [support_pure, Set.mem_singleton_iff] at hx; subst hx
        exact ⟨hVP, h_rev.1, hVO, hVSess⟩
      · unfold ecTaggedKeyInd ecTaggedFromLists
        dsimp only [sessPksKeyInd]
        rw [h_rev.2]

def hasUpperTaggedPairCollAt (tagged : List (Nat × Bytes)) (s1 s2 : Nat) : Bool :=
  decide (s1 < s2) &&
  match tagged.find? (fun p => p.1 == s1), tagged.find? (fun p => p.1 == s2) with
  | some (_, v1), some (_, v2) => v1 == v2
  | _, _                       => false

theorem hasDuplicateBytes_map_snd_imp_any_upper_double_range (N : Nat)
    (tagged : List (Nat × Bytes))
    (hV : ValidTaggedPks N tagged)
    (hdup : hasDuplicateBytes (tagged.map Prod.snd) = true) :
    ((List.range N).any (fun s1 =>
      (List.range N).any (fun s2 =>
        hasUpperTaggedPairCollAt tagged s1 s2))) = true := by
  obtain ⟨p1, hp1, p2, hp2, hne, hpk⟩ :=
    exists_distinct_of_hasDuplicateBytes_map_snd tagged hV.2 hdup
  have hs1 : p1.1 < N := hV.1 p1 hp1
  have hs2 : p2.1 < N := hV.1 p2 hp2
  have hf1 := find?_fst_eq_some tagged hV.2 p1 hp1
  have hf2 := find?_fst_eq_some tagged hV.2 p2 hp2
  simp only [List.any_eq_true, List.mem_range]
  rcases Nat.lt_or_gt_of_ne hne with hlt | hgt
  · refine ⟨p1.1, hs1, p2.1, hs2, ?_⟩
    unfold hasUpperTaggedPairCollAt
    simp [hlt, hf1, hf2, hpk]
  · refine ⟨p2.1, hs2, p1.1, hs1, ?_⟩
    unfold hasUpperTaggedPairCollAt
    simp [hgt, hf1, hf2, hpk]

/-- Upper-triangle (`s1 < s2`) supermartingale potential for initiator `dh2` collisions. -/
noncomputable def dh2UpperPairPotential (tagged : List (Nat × Bytes)) (s1 s2 : Nat) : ℝ≥0∞ :=
  if s1 < s2 then
    match tagged.find? (fun p => p.1 == s1), tagged.find? (fun p => p.1 == s2) with
    | some (_, dh1), some (_, dh2) =>
        𝒟[(pure (dh1 == dh2) : ProbComp Bool)] {true}
    | _, _ => ENNReal.ofReal Pfixed_pk_ec
  else
    0

theorem evalDist_hasUpperTaggedPairCollAt_le_potential
    (tagged : List (Nat × Bytes)) (s1 s2 : Nat) :
    𝒟[(pure (hasUpperTaggedPairCollAt tagged s1 s2) : ProbComp Bool)] {true} ≤
      dh2UpperPairPotential tagged s1 s2 := by
  unfold hasUpperTaggedPairCollAt dh2UpperPairPotential
  by_cases hlt : s1 < s2
  · simp only [hlt, decide_true, Bool.true_and, ↓reduceIte]
    cases tagged.find? (fun p => p.1 == s1) with
    | none => simp
    | some p1 =>
      rcases p1 with ⟨_, dh1⟩
      cases tagged.find? (fun p => p.1 == s2) with
      | none => simp
      | some p2 =>
        rcases p2 with ⟨_, dh2⟩
        exact le_rfl
  · simp [hlt]

theorem dh2UpperPairPotential_nil_le (s1 s2 : Nat) :
    dh2UpperPairPotential [] s1 s2 ≤ ENNReal.ofReal Pfixed_pk_ec := by
  unfold dh2UpperPairPotential
  split_ifs <;> simp

theorem length_of_mem_support_sampleScalar32_coll {x : Bytes} (hx : x ∈ support sampleScalar32) :
    x.length = 32 := by
  unfold sampleScalar32 sampleBytes32 at hx
  simp only [support_map, Set.mem_image] at hx
  rcases hx with ⟨w, _, rfl⟩
  simp [word256ToBytes]

theorem probExpect_sampleScalar32_dh2_coll_le (P : Primitives) (hP : CryptoWellFormedPrimitivesδ P)
    (ikB skB dhOther : Bytes) (hSkB : skB.length = 32)
    (hPowB : P.pow8 (P.x25519Base skB) = P.pow8 ikB) :
    probExpect sampleScalar32
      (fun ekASk => 𝒟[(pure (P.x25519 ekASk ikB == dhOther) : ProbComp Bool)] {true}) ≤
      ENNReal.ofReal Pfixed_pk_ec := by
  by_cases hEx : ∃ ek0 ∈ support sampleScalar32, P.x25519 ek0 ikB = dhOther
  · rcases hEx with ⟨ek0, _, hDh0⟩
    refine le_trans (probExpect_mono_of_support sampleScalar32 _
      (fun ekASk =>
          𝒟[(pure (P.pow8 (P.x25519Base ekASk) == P.pow8 (P.x25519Base ek0)) :
              ProbComp Bool)] {true}) ?_)
      (probExpect_sampleScalar32_ec_coll_le P hP (P.x25519Base ek0))
    intro ekASk _
    by_cases hEq : (P.x25519 ekASk ikB == dhOther) = true
    · have hDh : P.x25519 ekASk ikB = P.x25519 ek0 ikB :=
        (beq_iff_eq.mp hEq).trans hDh0.symm
      have hIkBLen : ikB.length = 32 := hP.pow8_base_len ikB skB hPowB.symm
      have hCongr1 :=
        hP.x25519_pow8_congr ekASk (P.x25519Base skB) ikB (hP.x25519Base_len skB) hIkBLen hPowB
      have hCongr0 :=
        hP.x25519_pow8_congr ek0 (P.x25519Base skB) ikB (hP.x25519Base_len skB) hIkBLen hPowB
      have hComm1 := hP.x25519_comm skB ekASk
      have hComm0 := hP.x25519_comm skB ek0
      have hSkEq : P.x25519 skB (P.x25519Base ekASk) = P.x25519 skB (P.x25519Base ek0) := by
        rw [hComm1, hCongr1, hDh, ← hCongr0, ← hComm0]
      have hInj := hP.x25519_inj_pow8 skB (P.x25519Base ekASk) (P.x25519Base ek0)
        hSkB (hP.x25519Base_len ekASk) (hP.x25519Base_len ek0) hSkEq
      have hBeq : (P.pow8 (P.x25519Base ekASk) == P.pow8 (P.x25519Base ek0)) = true :=
        beq_iff_eq.mpr hInj
      simp [hEq, hBeq]
    · simp only [Bool.not_eq_true] at hEq
      simp [hEq]
  · refine le_trans (probExpect_const_le_of_support sampleScalar32 _ 0 ?_) zero_le
    intro ekASk hek
    have hNe : (P.x25519 ekASk ikB == dhOther) = false := by
      rw [beq_eq_false_iff_ne]
      intro hEq
      exact hEx ⟨ekASk, hek, hEq⟩
    simp [hNe]

theorem probExpect_dh2UpperPairPotential_cons_fresh_le (P : Primitives)
    (hP : CryptoWellFormedPrimitivesδ P)
    (dh2Tagged : List (Nat × Bytes)) (sNew : Nat) (ikB skB : Bytes)
    (hSkB : skB.length = 32)
    (hPowB : P.pow8 (P.x25519Base skB) = P.pow8 ikB)
    (s1 s2 : Nat)
    (hFresh : sNew ∉ dh2Tagged.map Prod.fst) :
    probExpect sampleScalar32
      (fun ekASk => dh2UpperPairPotential ((sNew, P.x25519 ekASk ikB) :: dh2Tagged) s1 s2) ≤
      dh2UpperPairPotential dh2Tagged s1 s2 := by
  have hFresh' : sNew ∉ ([] ++ dh2Tagged).map Prod.fst := by simpa using hFresh
  unfold dh2UpperPairPotential
  by_cases hlt : s1 < s2
  · simp only [hlt, ↓reduceIte]
    have h_ins : ∀ ekASk (s : Nat),
        (((sNew, P.x25519 ekASk ikB) :: dh2Tagged).find? (fun p => p.1 == s)) =
        if sNew == s then some (sNew, P.x25519 ekASk ikB) else dh2Tagged.find? (fun p =>
            p.1 == s) :=
      fun ekASk s => find?_insert_fresh [] dh2Tagged sNew (P.x25519 ekASk ikB) s hFresh'
    simp_rw [h_ins]
    by_cases hs1 : (sNew == s1) = true
    · have heq1 : sNew = s1 := beq_iff_eq.mp hs1
      have hs2 : (sNew == s2) = false := by rw [beq_eq_false_iff_ne]; omega
      have hnone1 : dh2Tagged.find? (fun p => p.1 == s1) = none :=
        find?_fst_none_of_not_mem dh2Tagged s1 (heq1 ▸ hFresh)
      simp only [hs1, hs2, hnone1, ↓reduceIte, Bool.false_eq_true]
      cases dh2Tagged.find? (fun p => p.1 == s2) with
      | none => simp [probExpect_const]
      | some p2 =>
        rcases p2 with ⟨_, dhOther⟩
        exact probExpect_sampleScalar32_dh2_coll_le P hP ikB skB dhOther hSkB hPowB
    · simp only [Bool.not_eq_true] at hs1
      by_cases hs2 : (sNew == s2) = true
      · have heq2 : sNew = s2 := beq_iff_eq.mp hs2
        have hnone2 : dh2Tagged.find? (fun p => p.1 == s2) = none :=
          find?_fst_none_of_not_mem dh2Tagged s2 (heq2 ▸ hFresh)
        simp only [hs1, hs2, hnone2, ↓reduceIte, Bool.false_eq_true]
        cases dh2Tagged.find? (fun p => p.1 == s1) with
        | none => simp [probExpect_const]
        | some p1 =>
          rcases p1 with ⟨_, dhOther⟩
          have h_comm : ∀ ekASk : Bytes,
              ((dhOther == P.x25519 ekASk ikB) : Bool) =
              (P.x25519 ekASk ikB == dhOther) := fun _ => Bool.beq_comm
          simp_rw [h_comm]
          exact probExpect_sampleScalar32_dh2_coll_le P hP ikB skB dhOther hSkB hPowB
      · simp only [Bool.not_eq_true] at hs2
        simp only [hs1, hs2, Bool.false_eq_true, ↓reduceIte, probExpect_const, le_rfl]
  · simp [hlt, probExpect_const]

def sessDh2sKeyInd (S : Setup) (P : Primitives) (st : KeyIndState S) : List (SessionId S × Bytes) :=
  st.sessions.map (fun s => (s.sid, P.x25519 s.ekASk s.peerIkPk))

def dh2TaggedKeyInd (S : Setup) (P : Primitives) (st : KeyIndState S) : List (Nat × Bytes) :=
  (sessDh2sKeyInd S P st).map (fun (sid, dh2) => (ecSessSlotIdx S sid, dh2))

theorem map_snd_dh2TaggedKeyInd (S : Setup) (P : Primitives) (st : KeyIndState S) :
    (dh2TaggedKeyInd S P st).map Prod.snd = allInitDh2sKeyInd P st := by
  unfold dh2TaggedKeyInd sessDh2sKeyInd allInitDh2sKeyInd
  simp [HasKeyIndState.toKeyIndState, List.map_map, Function.comp_def]

theorem map_fst_dh2TaggedKeyInd (S : Setup) (P : Primitives) (st : KeyIndState S) :
    (dh2TaggedKeyInd S P st).map Prod.fst =
      ((sessPksKeyInd S st).map Prod.fst).map (ecSessSlotIdx S) := by
  unfold dh2TaggedKeyInd sessDh2sKeyInd sessPksKeyInd
  simp [List.map_map, Function.comp_def]

theorem validTaggedPks_dh2TaggedKeyInd (S : Setup) (P : Primitives) (st : KeyIndState S)
    (hVSess : ValidSessionIds S ((sessPksKeyInd S st).map Prod.fst)) :
    ValidTaggedPks S.N_dh (dh2TaggedKeyInd S P st) := by
  refine ⟨?_, ?_⟩
  · intro p hp
    have hp_fst : p.1 ∈ (dh2TaggedKeyInd S P st).map Prod.fst := List.mem_map_of_mem hp
    rw [map_fst_dh2TaggedKeyInd, List.mem_map] at hp_fst
    rcases hp_fst with ⟨sid, hsid_mem, hsid_eq⟩
    rw [← hsid_eq]
    have hlt := sessSlotFlatIdx_lt S sid (hVSess.1 sid hsid_mem)
    unfold ecSessSlotIdx Setup.N_dh
    omega
  · rw [map_fst_dh2TaggedKeyInd]
    exact hVSess.2

theorem ge_offset_of_hasUpperTaggedPairCollAt_dh2TaggedKeyInd (S : Setup) (P : Primitives)
    (st : KeyIndState S) {s1 s2 : Nat}
    (hColl : hasUpperTaggedPairCollAt (dh2TaggedKeyInd S P st) s1 s2 = true) :
    S.N_id + S.N_spk_tot + S.N_opk_tot ≤ s1 := by
  unfold hasUpperTaggedPairCollAt at hColl
  cases hfind : (dh2TaggedKeyInd S P st).find? (fun p => p.1 == s1) with
  | none => simp [hfind] at hColl
  | some p1 =>
    have hp1_mem : p1 ∈ dh2TaggedKeyInd S P st := List.mem_of_find?_eq_some hfind
    have hp1_eq : p1.1 = s1 :=
      beq_iff_eq.mp (List.find?_some (p := fun (p : Nat × Bytes) => p.1 == s1) hfind)
    unfold dh2TaggedKeyInd sessDh2sKeyInd at hp1_mem
    rw [List.mem_map] at hp1_mem
    rcases hp1_mem with ⟨⟨sid, _⟩, _, rfl⟩
    dsimp only at hp1_eq
    unfold ecSessSlotIdx at hp1_eq
    omega

end SignalPqxdh.Security
