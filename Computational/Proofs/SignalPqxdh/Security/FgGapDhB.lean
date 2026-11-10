/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Computational.Proofs.SignalPqxdh.Security.FgGapDhA
public import Computational.Proofs.SignalPqxdh.Security.CollisionsB
import VCVio.EvalDist.Monad.Basic
import VCVio.OracleComp.Constructions.SampleableType.Measure

@[expose] public section

/-!
# Soundness of the Fiedler–Günther `GapDH` Reduction Helpers

Algebraic soundness of `ddhEqPure` and of CDH extraction, index-guessing identities for the
`GapDH` advantage, `simulateQ` characterization of the simulator step, and relational coupling up
to a bad event.
-/

open SignalPqxdh
open OracleSpec OracleComp
open MeasureTheory
open scoped ENNReal

open SignalPqxdh.Security

namespace Proofs.SignalPqxdh.Security.FgGapDh

open _root_.SignalPqxdh.Security.FgGapDh

abbrev onCurveKeyLocal (P : Primitives) (pk : Bytes) : Prop :=
  onCurveKey P pk

theorem isCanonical_length_eq_32 (P : Primitives) (hWF : WellFormedPrimitivesδ P)
    {pk : Bytes} (hCan : P.isCanonical pk = true) : pk.length = 32 := by
  rw [hWF.isCanonical_eq_isCanonicalRef] at hCan
  unfold isCanonicalRef at hCan
  by_contra hNe
  have hFalse : (pk.length == 32) = false := beq_eq_false_iff_ne.mpr hNe
  simp [hFalse] at hCan

theorem onCurveKeyLocal_length_eq_32 (P : Primitives) (hP : CryptoWellFormedPrimitivesδ P)
    {pk : Bytes} (hpk : onCurveKeyLocal P pk) : pk.length = 32 := by
  rcases hpk with hCan | ⟨e, _he, hpow⟩
  · exact isCanonical_length_eq_32 P hP.toWellFormedPrimitivesδ hCan
  · exact hP.pow8_base_len pk e hpow

theorem isCanonical_x25519_of_onCurveKeyLocal (P : Primitives) (hWF : WellFormedPrimitivesδ P)
    (a pk : Bytes) (ha : a.length = 32) (hpkLen : pk.length = 32) (hpk : onCurveKeyLocal P pk) :
    P.isCanonical (P.x25519 a pk) = true := by
  rcases hpk with hCan | ⟨e, _he, hpow⟩
  · exact hWF.canon_x25519 a pk ha hCan
  · rw [hWF.x25519_pow8_congr a pk (P.x25519Base e) hpkLen (hWF.x25519Base_len e) hpow]
    exact hWF.canon_x25519 a (P.x25519Base e) ha (hWF.canon_base e)

theorem ddh_consistent_left_of_onCurveKeyLocal (P : Primitives) (hWF : WellFormedPrimitivesδ P)
    (a pk z : Bytes) (_ha : a.length = 32) (hpk : onCurveKeyLocal P pk) :
    P.isValidDhTriple (P.x25519Base a) pk z = true ↔ P.pow8 z = P.pow8 (P.x25519 a pk) :=
  hWF.ddh_consistent_left a pk z hpk

/-- Comparing `.pair (P.x25519Base a) pk` against `.secret z (P.isCanonical z)` under `ddhEqPure`
    returns `true` iff `z = P.x25519 a pk`. -/
theorem ddhEqPure_pair_left_secret_iff (P : Primitives) (hWF : WellFormedPrimitivesδ P)
    (a pk w1 w2 z : Bytes) (ha : a.length = 32) (hpkLen : pk.length = 32)
    (hpk : onCurveKeyLocal P pk) :
    ddhEqPure P.isValidDhTriple (.pair (P.x25519Base a) pk w1 w2) (.secret z (P.isCanonical z)) =
      true ↔
      z = P.x25519 a pk := by
  simp only [ddhEqPure]
  have h : (if P.isCanonical z then P.isValidDhTriple (P.x25519Base a) pk z else false) =
      (P.isCanonical z && P.isValidDhTriple (P.x25519Base a) pk z) := by
    cases P.isCanonical z <;> rfl
  rw [h, Bool.and_eq_true, ddh_consistent_left_of_onCurveKeyLocal P hWF a pk z ha hpk]
  have hCanX := isCanonical_x25519_of_onCurveKeyLocal P hWF a pk ha hpkLen hpk
  constructor
  · rintro ⟨hcz, hpow⟩
    exact hWF.canon_pow8_inj z (P.x25519 a pk) hcz hCanX hpow
  · rintro rfl
    exact ⟨hCanX, rfl⟩

theorem ddhEqPure_pair_right_secret_iff (P : Primitives) (hWF : WellFormedPrimitivesδ P)
    (pk b w1 w2 z : Bytes) (hb : b.length = 32) (hpkLen : pk.length = 32)
    (hpk : onCurveKeyLocal P pk) :
    ddhEqPure P.isValidDhTriple (.pair pk (P.x25519Base b) w1 w2) (.secret z (P.isCanonical z)) =
      true ↔
      z = P.x25519 b pk := by
  simp only [ddhEqPure, hWF.ddh_symm pk (P.x25519Base b) z]
  exact ddhEqPure_pair_left_secret_iff P hWF b pk w1 w2 z hb hpkLen hpk

theorem ddhEqPure_secret_pair_left_iff (P : Primitives) (hWF : WellFormedPrimitivesδ P)
    (a pk w1 w2 z : Bytes) (ha : a.length = 32) (hpkLen : pk.length = 32)
    (hpk : onCurveKeyLocal P pk) :
    ddhEqPure P.isValidDhTriple (.secret z (P.isCanonical z)) (.pair (P.x25519Base a) pk w1 w2) =
      true ↔
      z = P.x25519 a pk :=
  ddhEqPure_pair_left_secret_iff P hWF a pk w1 w2 z ha hpkLen hpk

theorem ddhEqPure_secret_pair_right_iff (P : Primitives) (hWF : WellFormedPrimitivesδ P)
    (pk b w1 w2 z : Bytes) (hb : b.length = 32) (hpkLen : pk.length = 32)
    (hpk : onCurveKeyLocal P pk) :
    ddhEqPure P.isValidDhTriple (.secret z (P.isCanonical z)) (.pair pk (P.x25519Base b) w1 w2) =
      true ↔
      z = P.x25519 b pk :=
  ddhEqPure_pair_right_secret_iff P hWF pk b w1 w2 z hb hpkLen hpk

/-- If `advRoLog.take maxLen` logs a `.roQuery` input whose target DH value equals
    `P.x25519 u (P.x25519Base v)`, `pureExtractCdhFromAdvRoLog` outputs a winning `GapDH`
    solution. -/
theorem pureExtractCdhFromAdvRoLog_wins_of_mem
    (P : Primitives) (hWF : WellFormedPrimitivesδ P)
    (useDh1 : Bool) (maxLen : ℕ) (u v : Bytes) (advRoLog : List Bytes)
    (h_mem : ∃ sec ∈ advRoLog.take maxLen,
      (if useDh1 then extractDh1 sec else extractDh3 sec) = P.x25519 u (P.x25519Base v)) :
    (P.pow8 (pureExtractCdhFromAdvRoLog P.isValidDhTriple useDh1 maxLen
      (P.x25519Base u) (P.x25519Base v) advRoLog) ==
      P.pow8 (P.x25519 u (P.x25519Base v))) = true := by
  dsimp only [pureExtractCdhFromAdvRoLog]
  set cands := (advRoLog.take maxLen).map (fun sec =>
    if useDh1 then extractDh1 sec else extractDh3 sec)
  rcases h_mem with ⟨sec, hsec_mem, hsec_eq⟩
  have hcands_mem : P.x25519 u (P.x25519Base v) ∈ cands := by
    rw [← hsec_eq]
    exact List.mem_map_of_mem hsec_mem
  have hddh_target : P.isValidDhTriple (P.x25519Base u) (P.x25519Base v)
      (P.x25519 u (P.x25519Base v)) = true :=
    (hWF.ddh_consistent u v (P.x25519 u (P.x25519Base v))).mpr rfl
  have hfind_some : (cands.find? (fun z =>
    P.isValidDhTriple (P.x25519Base u) (P.x25519Base v) z)).isSome = true :=
    List.find?_isSome.mpr ⟨P.x25519 u (P.x25519Base v), hcands_mem, hddh_target⟩
  rcases Option.isSome_iff_exists.mp hfind_some with ⟨Z, hZ⟩
  have hZ_ddh : P.isValidDhTriple (P.x25519Base u) (P.x25519Base v) Z = true :=
    List.find?_some hZ
  have hZ_pow : P.pow8 Z = P.pow8 (P.x25519 u (P.x25519Base v)) :=
    (hWF.ddh_consistent u v Z).mp hZ_ddh
  rw [hZ]
  simp [hZ_pow]

/-! ## Index-guessing decomposition -/

theorem ddh_eq_pow8_of_find?_some (P : Primitives) (hWF : WellFormedPrimitivesδ P)
    (u v z : Bytes) (L : List Bytes)
    (h : L.find? (fun z => P.isValidDhTriple (P.x25519Base u) (P.x25519Base v) z) = some z) :
    (P.pow8 z == P.pow8 (P.x25519 u (P.x25519Base v))) = true := by
  have hddh : P.isValidDhTriple (P.x25519Base u) (P.x25519Base v) z = true :=
    List.find?_some h
  have hpow : P.pow8 z = P.pow8 (P.x25519 u (P.x25519Base v)) :=
    (hWF.ddh_consistent u v z).mp hddh
  simp [hpow]

theorem find?_ddh_isSome_of_mem (P : Primitives) (hWF : WellFormedPrimitivesδ P)
    (u v : Bytes) (L : List Bytes)
    (h_mem : P.x25519 u (P.x25519Base v) ∈ L) :
    (L.find? (fun z => P.isValidDhTriple (P.x25519Base u) (P.x25519Base v) z)).isSome = true :=
  List.find?_isSome.mpr ⟨P.x25519 u (P.x25519Base v), h_mem,
    (hWF.ddh_consistent u v (P.x25519 u (P.x25519Base v))).mpr rfl⟩

theorem pureExtractCdhFromSimState_dh1_wins_of_mem (S : Setup) (P : Primitives)
    (hWF : WellFormedPrimitivesδ P) (maxLen : ℕ) (u v : Bytes) (st : FgKeyIndSimState S)
    (h_mem :
      P.x25519 u (P.x25519Base v) ∈ (st.advRoLog.take maxLen).map extractDh1 ∨
      P.x25519 u (P.x25519Base v) ∈
        (st.base.sessions.take S.N_dh).map (initDh1Cand S P st.base.spkBundles st.advKeyPows) ∨
      P.x25519 u (P.x25519Base v) ∈
        (st.base.respSessions.take S.N_sess_tot).map (respDh1Cand S P st.base.spkBundles)) :
    (P.pow8 (pureExtractCdhFromSimState S P P.isValidDhTriple true maxLen
      (P.x25519Base u) (P.x25519Base v) st) ==
      P.pow8 (P.x25519 u (P.x25519Base v))) = true := by
  unfold pureExtractCdhFromSimState
  simp only [↓reduceIte]
  cases h1 : ((st.advRoLog.take maxLen).map extractDh1).find?
      (fun z => P.isValidDhTriple (P.x25519Base u) (P.x25519Base v) z) with
  | some z1 => exact ddh_eq_pow8_of_find?_some P hWF u v z1 _ h1
  | none =>
    cases h2 : ((st.base.sessions.take S.N_dh).map
        (initDh1Cand S P st.base.spkBundles st.advKeyPows)).find?
        (fun z => P.isValidDhTriple (P.x25519Base u) (P.x25519Base v) z) with
    | some z2 => exact ddh_eq_pow8_of_find?_some P hWF u v z2 _ h2
    | none =>
      cases h3 : ((st.base.respSessions.take S.N_sess_tot).map
          (respDh1Cand S P st.base.spkBundles)).find?
          (fun z => P.isValidDhTriple (P.x25519Base u) (P.x25519Base v) z) with
      | some z3 => exact ddh_eq_pow8_of_find?_some P hWF u v z3 _ h3
      | none =>
        exfalso
        rcases h_mem with hm1 | hm2 | hm3
        · have hs := find?_ddh_isSome_of_mem P hWF u v _ hm1
          rw [h1] at hs; cases hs
        · have hs := find?_ddh_isSome_of_mem P hWF u v _ hm2
          rw [h2] at hs; cases hs
        · have hs := find?_ddh_isSome_of_mem P hWF u v _ hm3
          rw [h3] at hs; cases hs

theorem gapDhExp_fgKeyIndGapDhAdvAt_eq (P : Primitives)
    (ddh : Bytes → Bytes → Bytes → Bool) (pow8 : Bytes → Bytes)
    (useDh1 : Bool) (targetIdx targetSpkIdx : ℕ)
    (S : Setup) (b : QueryBudget) (A : BoundedAdv (KeyIndAdversary S) b) :
    gapDhExp P ddh pow8 (fgKeyIndGapDhAdvAt useDh1 targetIdx targetSpkIdx S b A) =
    (do
      let u ← sampleScalar32
      let v ← sampleScalar32
      let U := P.x25519Base u
      let V := P.x25519Base v
      let secb ← $ᵗ Bool
      let initSt := FgKeyIndSimState.empty S secb
      let impl := (QueryImpl.ofLift unifSpec ProbComp).liftTarget
          (StateT (FgKeyIndSimState S) ProbComp) +
        fgKeyIndSimImpl P ddh useDh1 targetIdx targetSpkIdx S b.q_total U V
      let (_, finalSt) ← (simulateQ impl A.1.run).run initSt
      return (pow8 (pureExtractCdhFromSimState S P ddh useDh1 b.q_total U V finalSt) ==
        pow8 (P.x25519 u V))) := by
  unfold gapDhExp fgKeyIndGapDhAdvAt
  dsimp only [gapDhFullImpl, gapDhDdhImpl]
  congr 1; ext u
  congr 1; ext v
  change (simulateQ (gapDhFullImpl P ddh)
      (fgKeyIndGapDhRunAt useDh1 targetIdx targetSpkIdx S b A (P.x25519Base u) (P.x25519Base v)) >>=
    fun Z => pure (pow8 Z == pow8 (P.x25519 u (P.x25519Base v)))) = _
  rw [simulateQ_gapDhFullImpl_fgKeyIndGapDhRunAt]
  simp only [bind_assoc, pure_bind]

theorem evalDist_uniformFin_bind_true_fg (N : ℕ) [NeZero N] (f : ℕ → ProbComp Bool) :
    𝒟[($ᵗ (Fin N) : ProbComp (Fin N)) >>= fun k => f k.val] {true} =
      ∑ k ∈ Finset.range N, 𝒟[f k] {true} * (N : ℝ≥0∞)⁻¹ := by
  let : MeasurableSpace (Fin N) := ⊤
  rw [evalDist_bind_of_discrete,
    MeasureTheory.Measure.bind_apply (MeasurableSet.singleton true)
      (Measurable.of_discrete).aemeasurable,
    MeasureTheory.lintegral_fintype]
  simp_rw [SampleableType.evalDist_uniformSample_singleton, Fintype.card_fin]
  exact (Fin.sum_univ_eq_sum_range (fun k => 𝒟[f k] {true} * (N : ℝ≥0∞)⁻¹) N)

theorem mul_toReal_uniformFin_bind_eq_sum_fg (N : ℕ) [NeZero N] (f : ℕ → ProbComp Bool) :
    (N : ℝ) * (𝒟[($ᵗ (Fin N) : ProbComp (Fin N)) >>= fun k => f k.val] {true}).toReal =
      ∑ k ∈ Finset.range N, (𝒟[f k] {true}).toReal := by
  rw [evalDist_uniformFin_bind_true_fg]
  have hfin : ∀ k ∈ Finset.range N, 𝒟[f k] {true} * (N : ℝ≥0∞)⁻¹ ≠ ⊤ := by
    intro k _
    exact ENNReal.mul_ne_top (MeasureTheory.measure_ne_top _ {true})
      (ENNReal.inv_ne_top.mpr (Nat.cast_ne_zero.mpr (NeZero.ne N)))
  rw [ENNReal.toReal_sum hfin]
  have hterm : ∀ k ∈ Finset.range N,
      (𝒟[f k] {true} * (N : ℝ≥0∞)⁻¹).toReal = (𝒟[f k] {true}).toReal * (N : ℝ)⁻¹ := by
    intro k _
    rw [ENNReal.toReal_mul, ENNReal.toReal_inv, ENNReal.toReal_natCast]
  rw [Finset.sum_congr rfl hterm, ← Finset.sum_mul, ← mul_assoc,
    mul_comm (N : ℝ), mul_assoc, mul_inv_cancel₀ (Nat.cast_ne_zero.mpr (NeZero.ne N)), mul_one]

theorem mul_toReal_sampleIndexRange_bind_eq_sum_fg (N : ℕ) (f : ℕ → ProbComp Bool) :
    (N : ℝ) * (𝒟[sampleIndexRange N >>= f] {true}).toReal =
      ∑ k ∈ Finset.range N, (𝒟[f k] {true}).toReal := by
  unfold sampleIndexRange
  split_ifs with h
  · let : NeZero N := ⟨Nat.ne_of_gt h⟩
    simp only [bind_assoc, pure_bind]
    exact mul_toReal_uniformFin_bind_eq_sum_fg N f
  · have h0 : N = 0 := Nat.eq_zero_of_not_pos h
    subst h0
    simp

theorem mul_toReal_sampleIndexRange2_bind_eq_double_sum_fg (M N : ℕ) (f : ℕ → ℕ → ProbComp Bool) :
    (M : ℝ) * (N : ℝ) *
      (𝒟[sampleIndexRange2 M N >>= fun p => f p.1 p.2] {true}).toReal =
      ∑ i ∈ Finset.range M, ∑ j ∈ Finset.range N, (𝒟[f i j] {true}).toReal := by
  unfold sampleIndexRange2
  simp only [bind_assoc, pure_bind]
  have hOuter := mul_toReal_sampleIndexRange_bind_eq_sum_fg M
    (fun i => sampleIndexRange N >>= fun j => f i j)
  calc (M : ℝ) * (N : ℝ) *
        (𝒟[sampleIndexRange M >>= fun i => sampleIndexRange N >>= fun j => f i j] {true}).toReal
      = (N : ℝ) * ((M : ℝ) *
          (𝒟[sampleIndexRange M >>= fun i => sampleIndexRange N >>= fun j =>
            f i j] {true}).toReal) := by
        ring
    _ = (N : ℝ) * ∑ i ∈ Finset.range M,
          (𝒟[sampleIndexRange N >>= fun j => f i j] {true}).toReal := by
        rw [hOuter]
    _ = ∑ i ∈ Finset.range M,
          (N : ℝ) * (𝒟[sampleIndexRange N >>= fun j => f i j] {true}).toReal :=
        Finset.mul_sum _ _ _
    _ = ∑ i ∈ Finset.range M, ∑ j ∈ Finset.range N, (𝒟[f i j] {true}).toReal :=
        Finset.sum_congr rfl (fun i _ => mul_toReal_sampleIndexRange_bind_eq_sum_fg N (fun j =>
          f i j))

/-! ## Pure `simulateQ` semantics -/

theorem simulateQ_primBaseImpl_findMPrim {α : Type} (P : Primitives)
    (p : α → OracleComp PrimBaseSpec Bool) (pPure : α → Bool)
    (hp : ∀ x, simulateQ (primBaseImpl P) (p x) = pure (pPure x))
    (xs : List α) :
    simulateQ (primBaseImpl P) (findMPrim p xs) = pure (xs.find? pPure) := by
  induction xs with
  | nil => simp [findMPrim]
  | cons x xs ih =>
    simp only [findMPrim, simulateQ_bind, hp x, pure_bind, List.find?_cons]
    cases pPure x <;> simp [ih]

theorem simulateQ_primBaseImpl_anyMPrim {α : Type} (P : Primitives)
    (p : α → OracleComp PrimBaseSpec Bool) (pPure : α → Bool)
    (hp : ∀ x, simulateQ (primBaseImpl P) (p x) = pure (pPure x))
    (xs : List α) :
    simulateQ (primBaseImpl P) (anyMPrim p xs) = pure (xs.any pPure) := by
  induction xs with
  | nil => simp [anyMPrim]
  | cons x xs ih =>
    simp only [anyMPrim, simulateQ_bind, hp x, pure_bind, List.any_cons]
    cases pPure x <;> simp [ih]

@[simp]
theorem simulateQ_gapDhFullImpl_embedPrim {α : Type} (P : Primitives)
    (ddh : Bytes → Bytes → Bytes → Bool) (oa : OracleComp PrimBaseSpec α) :
    simulateQ (gapDhFullImpl P ddh) (embedPrim (spec := gapDhOracleSpec) oa) =
      simulateQ (primBaseImpl P) oa := by
  unfold gapDhFullImpl
  exact simulateQ_embedPrim (primBaseImpl P) (gapDhDdhImpl ddh) oa

@[simp]
theorem simulateQ_primBaseImpl_findHonestPrincipalPrim (S : Setup) (P : Primitives)
    (principals : List (Nat × PrincipalEntry)) (ikB : Bytes) :
    simulateQ (primBaseImpl P) (findHonestPrincipalPrim S principals ikB) =
      pure (findHonestPrincipal P (principals.take S.N_dh) ikB) := by
  unfold findHonestPrincipalPrim findHonestPrincipal
  apply simulateQ_primBaseImpl_findMPrim
  rintro ⟨_, entry⟩
  simp [primQ, primBaseImpl, primImpl]

@[simp]
theorem simulateQ_primBaseImpl_resolveSigPkPrim (S : Setup) (P : Primitives)
    (principals : List (Nat × PrincipalEntry)) (ikB : Bytes) :
    simulateQ (primBaseImpl P) (resolveSigPkPrim S principals ikB) =
      pure (resolveSigPk P (principals.take S.N_dh) ikB) := by
  unfold resolveSigPkPrim resolveSigPk
  rw [simulateQ_bind, simulateQ_primBaseImpl_findHonestPrincipalPrim, pure_bind]
  cases findHonestPrincipal P (principals.take S.N_dh) ikB <;> simp

@[simp]
theorem simulateQ_primBaseImpl_isHonestUncorruptedPeerPrim (S : Setup) (P : Primitives)
    (principals : List (Nat × PrincipalEntry)) (ikB : Bytes) :
    simulateQ (primBaseImpl P) (isHonestUncorruptedPeerPrim S principals ikB) =
      pure (isHonestUncorruptedPeer P (principals.take S.N_dh) ikB) := by
  unfold isHonestUncorruptedPeerPrim isHonestUncorruptedPeer
  rw [simulateQ_bind, simulateQ_primBaseImpl_findHonestPrincipalPrim, pure_bind]
  cases findHonestPrincipal P (principals.take S.N_dh) ikB <;> simp

def checkBundleProvenanceTake (S : Setup) (P : Primitives)
    (principals : List (Nat × PrincipalEntry))
    (spkBundles : List ((Nat × Nat) × SpkBundleEntry))
    (opkEntries : List ((Nat × Nat × Nat) × OpkEntry))
    (bundle : PreKeyBundleInput) : Bool × Bool × Bool :=
  match findHonestPrincipal P (principals.take S.N_dh) bundle.ikB with
  | none => (false, false, false)
  | some (k, _) =>
    let spkHon := (spkBundles.take S.N_dh).any (fun ((u, _), b) =>
      u == k && P.pow8 b.spkPk == P.pow8 bundle.spkB)
    let pqspkHon := spkBundles.any (fun ((u, _), b) =>
      u == k && b.pqspkPk == bundle.pqspkB)
    let opkHon := match bundle.opkB? with
      | none => false
      | some (_, opkPk) =>
        (opkEntries.take S.N_dh).any (fun ((u, _, _), e) =>
          u == k && P.pow8 e.opkPk == P.pow8 opkPk)
    (spkHon, opkHon, pqspkHon)

theorem checkBundleProvenanceTake_eq_of_le (S : Setup) (P : Primitives)
    (principals : List (Nat × PrincipalEntry))
    (spkBundles : List ((Nat × Nat) × SpkBundleEntry))
    (opkEntries : List ((Nat × Nat × Nat) × OpkEntry))
    (bundle : PreKeyBundleInput)
    (hPrin : principals.length ≤ S.N_dh)
    (hSpk : spkBundles.length ≤ S.N_dh)
    (hOpk : opkEntries.length ≤ S.N_dh) :
    checkBundleProvenanceTake S P principals spkBundles opkEntries bundle =
      checkBundleProvenance P principals spkBundles opkEntries bundle := by
  unfold checkBundleProvenanceTake checkBundleProvenance
  simp only [List.take_of_length_le hPrin, List.take_of_length_le hSpk, List.take_of_length_le hOpk]
  rfl

@[simp]
theorem simulateQ_primBaseImpl_checkBundleProvenancePrim (S : Setup) (P : Primitives)
    (principals : List (Nat × PrincipalEntry))
    (spkBundles : List ((Nat × Nat) × SpkBundleEntry))
    (opkEntries : List ((Nat × Nat × Nat) × OpkEntry))
    (bundle : PreKeyBundleInput) :
    simulateQ (primBaseImpl P)
      (checkBundleProvenancePrim S principals spkBundles opkEntries bundle) =
      pure (checkBundleProvenanceTake S P principals spkBundles opkEntries bundle) := by
  unfold checkBundleProvenancePrim checkBundleProvenanceTake
  rw [simulateQ_bind, simulateQ_primBaseImpl_findHonestPrincipalPrim, pure_bind]
  cases findHonestPrincipal P (principals.take S.N_dh) bundle.ikB with
  | none => simp
  | some kp =>
    rcases kp with ⟨k, _⟩
    dsimp only
    have h1 : simulateQ (primBaseImpl P)
        (anyMPrim (fun ((u, _), b) => do
          let p1 ← primQ (.pow8 b.spkPk)
          let p2 ← primQ (.pow8 bundle.spkB)
          return (u == k && p1 == p2)) (spkBundles.take S.N_dh)) =
        pure ((spkBundles.take S.N_dh).any (fun ((u, _), b) =>
          u == k && P.pow8 b.spkPk == P.pow8 bundle.spkB)) := by
      apply simulateQ_primBaseImpl_anyMPrim
      rintro ⟨⟨u, _⟩, b⟩
      simp [primQ, primBaseImpl, primImpl]
    rw [simulateQ_bind, h1, pure_bind]
    cases bundle.opkB? with
    | none => simp
    | some opkPair =>
      rcases opkPair with ⟨_, opkPk⟩
      dsimp only
      have h2 : simulateQ (primBaseImpl P)
          (anyMPrim (fun ((u, _, _), e) => do
            let p1 ← primQ (.pow8 e.opkPk)
            let p2 ← primQ (.pow8 opkPk)
            return (u == k && p1 == p2)) (opkEntries.take S.N_dh)) =
          pure ((opkEntries.take S.N_dh).any (fun ((u, _, _), e) =>
            u == k && P.pow8 e.opkPk == P.pow8 opkPk)) := by
        apply simulateQ_primBaseImpl_anyMPrim
        rintro ⟨⟨u, _, _⟩, e⟩
        simp [primQ, primBaseImpl, primImpl]
      rw [simulateQ_bind, h2, pure_bind]
      rfl

def koskSenderOkTake (S : Setup) (P : Primitives)
    (principals : List (Nat × PrincipalEntry))
    (advKeyPows : List (Bytes × Bytes))
    (ikAPk : Bytes) : Bool :=
  (findHonestPrincipal P (principals.take S.N_dh) ikAPk).isSome ||
    isAdvRegisteredPows advKeyPows (P.pow8 ikAPk)

@[simp]
theorem simulateQ_primBaseImpl_primQ_pow8 (P : Primitives) (pk : Bytes) :
    simulateQ (primBaseImpl P) (primQ (.pow8 pk)) = pure (P.pow8 pk) := by
  simp [primQ, primBaseImpl, primImpl]

@[simp]
theorem simulateQ_primBaseImpl_koskSenderOkPrim (S : Setup) (P : Primitives)
    (principals : List (Nat × PrincipalEntry))
    (advKeyPows : List (Bytes × Bytes))
    (ikAPk : Bytes) :
    simulateQ (primBaseImpl P) (koskSenderOkPrim S principals advKeyPows ikAPk) =
      pure (koskSenderOkTake S P principals advKeyPows ikAPk) := by
  unfold koskSenderOkPrim koskSenderOkTake
  rw [simulateQ_bind, simulateQ_primBaseImpl_findHonestPrincipalPrim, pure_bind]
  simp [primQ, primBaseImpl, primImpl]

@[simp]
theorem simulateQ_primBaseImpl_isGameSpkPrim (S : Setup) (P : Primitives)
    (spkBundles : List ((Nat × Nat) × SpkBundleEntry))
    (spkPk : Bytes) :
    simulateQ (primBaseImpl P) (isGameSpkPrim S spkBundles spkPk) =
      pure ((spkBundles.take S.N_dh).any (fun (_, b) => P.pow8 b.spkPk == P.pow8 spkPk)) := by
  unfold isGameSpkPrim
  apply simulateQ_primBaseImpl_anyMPrim
  rintro ⟨_, b⟩
  simp [primQ, primBaseImpl, primImpl]

@[simp]
theorem simulateQ_primBaseImpl_isGameOpkPrim (S : Setup) (P : Primitives)
    (opkEntries : List ((Nat × Nat × Nat) × OpkEntry))
    (opkPk : Bytes) :
    simulateQ (primBaseImpl P) (isGameOpkPrim S opkEntries opkPk) =
      pure ((opkEntries.take S.N_dh).any (fun (_, e) => P.pow8 e.opkPk == P.pow8 opkPk)) := by
  unfold isGameOpkPrim
  apply simulateQ_primBaseImpl_anyMPrim
  rintro ⟨_, e⟩
  simp [primQ, primBaseImpl, primImpl]

def koskBundleOkTake (S : Setup) (P : Primitives)
    (principals : List (Nat × PrincipalEntry))
    (spkBundles : List ((Nat × Nat) × SpkBundleEntry))
    (opkEntries : List ((Nat × Nat × Nat) × OpkEntry))
    (advKeyPows : List (Bytes × Bytes))
    (bundle : PreKeyBundleInput) : Bool :=
  let ikOk := (findHonestPrincipal P (principals.take S.N_dh) bundle.ikB).isSome ||
    isAdvRegisteredPows advKeyPows (P.pow8 bundle.ikB)
  let spkOk := (spkBundles.take S.N_dh).any (fun (_, b) => P.pow8 b.spkPk == P.pow8 bundle.spkB) ||
    isAdvRegisteredPows advKeyPows (P.pow8 bundle.spkB)
  let opkOk := match bundle.opkB? with
    | none => true
    | some (_, opkPk) =>
      (opkEntries.take S.N_dh).any (fun (_, e) => P.pow8 e.opkPk == P.pow8 opkPk) ||
        isAdvRegisteredPows advKeyPows (P.pow8 opkPk)
  ikOk && spkOk && opkOk

@[simp]
theorem simulateQ_primBaseImpl_koskBundleOkPrim (S : Setup) (P : Primitives)
    (principals : List (Nat × PrincipalEntry))
    (spkBundles : List ((Nat × Nat) × SpkBundleEntry))
    (opkEntries : List ((Nat × Nat × Nat) × OpkEntry))
    (advKeyPows : List (Bytes × Bytes))
    (bundle : PreKeyBundleInput) :
    simulateQ (primBaseImpl P)
      (koskBundleOkPrim S principals spkBundles opkEntries advKeyPows bundle) =
      pure (koskBundleOkTake S P principals spkBundles opkEntries advKeyPows bundle) := by
  unfold koskBundleOkPrim koskBundleOkTake
  rw [simulateQ_bind, simulateQ_primBaseImpl_findHonestPrincipalPrim, pure_bind]
  rw [simulateQ_bind, simulateQ_primBaseImpl_primQ_pow8, pure_bind]
  dsimp only
  rw [simulateQ_bind, simulateQ_primBaseImpl_isGameSpkPrim, pure_bind]
  rw [simulateQ_bind, simulateQ_primBaseImpl_primQ_pow8, pure_bind]
  dsimp only
  cases bundle.opkB? with
  | none => simp
  | some p =>
    rcases p with ⟨_, opkPk⟩
    dsimp only
    rw [simulateQ_bind, simulateQ_primBaseImpl_isGameOpkPrim, pure_bind]
    rw [simulateQ_bind, simulateQ_primBaseImpl_primQ_pow8, pure_bind]
    simp

@[simp]
theorem simulateQ_primBaseImpl_lookupSpkSkPrim (S : Setup) (P : Primitives)
    (spkBundles : List ((Nat × Nat) × SpkBundleEntry))
    (advKeyPows : List (Bytes × Bytes))
    (spkPk : Bytes) :
    simulateQ (primBaseImpl P) (lookupSpkSkPrim S spkBundles advKeyPows spkPk) =
      pure (lookupSpkSkTake S P spkBundles advKeyPows spkPk) := by
  unfold lookupSpkSkPrim lookupSpkSkTake
  rw [simulateQ_bind, simulateQ_primBaseImpl_primQ_pow8, pure_bind]
  have hFind : simulateQ (primBaseImpl P)
      (findMPrim (fun (_, b) => do
        let p1 ← primQ (.pow8 b.spkPk)
        return (p1 == P.pow8 spkPk)) (spkBundles.take S.N_dh)) =
      pure ((spkBundles.take S.N_dh).find? (fun (_, b) => P.pow8 b.spkPk == P.pow8 spkPk)) := by
    apply simulateQ_primBaseImpl_findMPrim
    rintro ⟨_, b⟩
    simp [primQ, primBaseImpl, primImpl]
  rw [simulateQ_bind, hFind, pure_bind]
  dsimp only
  cases (spkBundles.take S.N_dh).find? (fun (_, b) => P.pow8 b.spkPk == P.pow8 spkPk) with
  | some p =>
    rcases p with ⟨_, b⟩
    simp
  | none =>
    dsimp only
    cases advKeyPows.find? (fun (_, wPk) => wPk == P.pow8 spkPk) with
    | some p =>
      rcases p with ⟨sk, _⟩
      simp
    | none => simp

@[simp]
theorem simulateQ_primBaseImpl_keyIndPartnerPrim {S : Setup} (P : Primitives)
    (s : KeyIndInitiatorEntry S) (r : KeyIndRespEntry S) :
    simulateQ (primBaseImpl P) (keyIndPartnerPrim s r) =
      pure (keyIndPartner P s r) := by
  unfold keyIndPartnerPrim keyIndPartner
  simp [primQ, primBaseImpl, primImpl]
  congr 1
  have hOpt :
      (s.peerOpkPk?.map (fun _ => P.pow8 (s.peerOpkPk?.getD [])) ==
        r.opkPk?.map (fun _ => P.pow8 (r.opkPk?.getD []))) =
      (s.peerOpkPk?.map P.pow8 == r.opkPk?.map P.pow8) := by
    cases s.peerOpkPk? <;> cases r.opkPk? <;> rfl
  rw [hOpt]

def choosePartnerDrKeyRandPure {S : Setup} (P : Primitives)
    (sessions : List (KeyIndInitiatorEntry S)) (r : KeyIndRespEntry S) : ProbComp DRKey :=
  match (sessions.take S.N_dh).find? (fun s => keyIndPartner P s r) with
  | some s => pure s.drKeyRand
  | none   => sampleDRKey96

@[simp]
theorem simulateQ_gapDhFullImpl_choosePartnerDrKeyRandGdh {S : Setup} (P : Primitives)
    (ddh : Bytes → Bytes → Bytes → Bool)
    (sessions : List (KeyIndInitiatorEntry S)) (r : KeyIndRespEntry S) :
    simulateQ (gapDhFullImpl P ddh) (choosePartnerDrKeyRandGdh sessions r) =
      choosePartnerDrKeyRandPure P sessions r := by
  unfold choosePartnerDrKeyRandGdh choosePartnerDrKeyRandPure
  rw [simulateQ_bind, simulateQ_gapDhFullImpl_embedPrim,
      simulateQ_primBaseImpl_findMPrim P _ _
        (fun s => simulateQ_primBaseImpl_keyIndPartnerPrim P s r) (sessions.take S.N_dh),
      pure_bind]
  cases (sessions.take S.N_dh).find? (fun s => keyIndPartner P s r) <;> simp

def chooseInitPartnerDrKeyRandPure {S : Setup} (P : Primitives)
    (respSessions : List (KeyIndRespEntry S)) (s : KeyIndInitiatorEntry S) : ProbComp DRKey :=
  match (respSessions.take S.N_sess_tot).find? (fun r => keyIndPartner P s r) with
  | some r => pure r.drKeyRand
  | none   => sampleDRKey96

@[simp]
theorem simulateQ_gapDhFullImpl_chooseInitPartnerDrKeyRandGdh {S : Setup} (P : Primitives)
    (ddh : Bytes → Bytes → Bytes → Bool)
    (respSessions : List (KeyIndRespEntry S)) (s : KeyIndInitiatorEntry S) :
    simulateQ (gapDhFullImpl P ddh) (chooseInitPartnerDrKeyRandGdh respSessions s) =
      chooseInitPartnerDrKeyRandPure P respSessions s := by
  unfold chooseInitPartnerDrKeyRandGdh chooseInitPartnerDrKeyRandPure
  rw [simulateQ_bind, simulateQ_gapDhFullImpl_embedPrim,
      simulateQ_primBaseImpl_findMPrim P _ _
        (fun r => simulateQ_primBaseImpl_keyIndPartnerPrim P s r) (respSessions.take S.N_sess_tot),
      pure_bind]
  cases (respSessions.take S.N_sess_tot).find? (fun r => keyIndPartner P s r) <;> simp

def mkSecretPosPure (P : Primitives) (z : Bytes) : FgPoS :=
  FgPoS.secret z (P.isCanonical z)

def mkPairPosPure (P : Primitives) (pk1 pk2 : Bytes) : FgPoS :=
  FgPoS.pair pk1 pk2 (P.pow8 pk1) (P.pow8 pk2)

def computeTwoSideOrPairPosPure (P : Primitives) (sk1 sk2 pk1 pk2 : Bytes) : FgPoS :=
  if !sk1.isEmpty then
    mkSecretPosPure P (P.x25519 sk1 pk2)
  else if !sk2.isEmpty then
    mkSecretPosPure P (P.x25519 sk2 pk1)
  else
    mkPairPosPure P pk1 pk2

def computeOptPosPure (P : Primitives) (sk1 pk1 : Bytes) :
    Option (Bytes × Bytes) → Option FgPoS
  | none => none
  | some (sk2, pk2) => some (computeTwoSideOrPairPosPure P sk1 sk2 pk1 pk2)

@[simp]
theorem simulateQ_gapDhFullImpl_primGdhQ_x25519Base (P : Primitives)
    (ddh : Bytes → Bytes → Bytes → Bool) (sk : Bytes) :
    simulateQ (α := Bytes) (gapDhFullImpl P ddh) (primGdhQ (.x25519Base sk)) =
      pure (P.x25519Base sk) := by
  rw [simulateQ_gapDhFullImpl_primGdhQ]; rfl

@[simp]
theorem simulateQ_gapDhFullImpl_primGdhQ_isCanonical (P : Primitives)
    (ddh : Bytes → Bytes → Bytes → Bool) (pk : Bytes) :
    simulateQ (α := Bool) (gapDhFullImpl P ddh) (primGdhQ (.isCanonical pk)) =
      pure (P.isCanonical pk) := by
  rw [simulateQ_gapDhFullImpl_primGdhQ]; rfl

@[simp]
theorem simulateQ_gapDhFullImpl_primGdhQ_sigPkGen (P : Primitives)
    (ddh : Bytes → Bytes → Bytes → Bool) (sk : Bytes) :
    simulateQ (α := Bytes) (gapDhFullImpl P ddh) (primGdhQ (.sigPkGen sk)) =
      pure (P.sigPkGen sk) := by
  rw [simulateQ_gapDhFullImpl_primGdhQ]; rfl

@[simp]
theorem simulateQ_gapDhFullImpl_primGdhQ_sigSign (P : Primitives)
    (ddh : Bytes → Bytes → Bytes → Bool) (sk msg r : Bytes) :
    simulateQ (α := Bytes) (gapDhFullImpl P ddh) (primGdhQ (.sigSign sk msg r)) =
      pure (P.sigSign sk msg r) := by
  rw [simulateQ_gapDhFullImpl_primGdhQ]; rfl

@[simp]
theorem simulateQ_gapDhFullImpl_primGdhQ_sigVerify (P : Primitives)
    (ddh : Bytes → Bytes → Bytes → Bool) (pk msg sig : Bytes) :
    simulateQ (α := Bool) (gapDhFullImpl P ddh) (primGdhQ (.sigVerify pk msg sig)) =
      pure (P.sigVerify pk msg sig) := by
  rw [simulateQ_gapDhFullImpl_primGdhQ]; rfl

@[simp]
theorem simulateQ_gapDhFullImpl_primGdhQ_kemKeyGen (P : Primitives)
    (ddh : Bytes → Bytes → Bytes → Bool) (seed : Bytes) :
    simulateQ (α := Bytes × Bytes) (gapDhFullImpl P ddh) (primGdhQ (.kemKeyGen seed)) =
      pure (P.kemKeyGen seed) := by
  rw [simulateQ_gapDhFullImpl_primGdhQ]; rfl

@[simp]
theorem simulateQ_gapDhFullImpl_primGdhQ_kemEncaps (P : Primitives)
    (ddh : Bytes → Bytes → Bytes → Bool) (pk coins : Bytes) :
    simulateQ (α := Option (Bytes × Bytes)) (gapDhFullImpl P ddh) (primGdhQ (.kemEncaps pk coins)) =
      pure (P.kemEncaps pk coins) := by
  rw [simulateQ_gapDhFullImpl_primGdhQ]; rfl

@[simp]
theorem simulateQ_gapDhFullImpl_primGdhQ_kemDecaps (P : Primitives)
    (ddh : Bytes → Bytes → Bytes → Bool) (sk ct : Bytes) :
    simulateQ (α := Option Bytes) (gapDhFullImpl P ddh) (primGdhQ (.kemDecaps sk ct)) =
      pure (P.kemDecaps sk ct) := by
  rw [simulateQ_gapDhFullImpl_primGdhQ]; rfl

@[simp]
theorem simulateQ_gapDhFullImpl_mkSecretPos (P : Primitives)
    (ddh : Bytes → Bytes → Bytes → Bool) (z : Bytes) :
    simulateQ (gapDhFullImpl P ddh) (mkSecretPos z) = pure (mkSecretPosPure P z) := by
  unfold mkSecretPos mkSecretPosPure
  simp

@[simp]
theorem simulateQ_gapDhFullImpl_mkPairPos (P : Primitives)
    (ddh : Bytes → Bytes → Bytes → Bool) (pk1 pk2 : Bytes) :
    simulateQ (gapDhFullImpl P ddh) (mkPairPos pk1 pk2) = pure (mkPairPosPure P pk1 pk2) := by
  unfold mkPairPos mkPairPosPure
  simp

@[simp]
theorem simulateQ_gapDhFullImpl_computeTwoSideOrPairPos (P : Primitives)
    (ddh : Bytes → Bytes → Bytes → Bool) (sk1 sk2 pk1 pk2 : Bytes) :
    simulateQ (gapDhFullImpl P ddh) (computeTwoSideOrPairPos sk1 sk2 pk1 pk2) =
      pure (computeTwoSideOrPairPosPure P sk1 sk2 pk1 pk2) := by
  unfold computeTwoSideOrPairPos computeTwoSideOrPairPosPure
  split_ifs <;> simp

@[simp]
theorem simulateQ_gapDhFullImpl_computeOptPos (P : Primitives)
    (ddh : Bytes → Bytes → Bytes → Bool) (sk1 pk1 : Bytes) (opt : Option (Bytes × Bytes)) :
    simulateQ (gapDhFullImpl P ddh) (computeOptPos sk1 pk1 opt) =
      pure (computeOptPosPure P sk1 pk1 opt) := by
  cases opt <;> simp [computeOptPos, computeOptPosPure]

noncomputable def fgRoQueryPure {S : Setup} (P : Primitives)
    (ddh : Bytes → Bytes → Bytes → Bool) (maxLen : ℕ) (secrets : Bytes)
    (st : FgKeyIndSimState S) : ProbComp (KeyIndResponse × FgKeyIndSimState S) := do
  let advRoLog' := secrets :: st.advRoLog
  match parseRoSecrets secrets with
  | some (dh1, dh2, dh3, dh4?, ss) =>
    let pos1 := mkSecretPosPure P dh1
    let pos2 := mkSecretPosPure P dh2
    let pos3 := mkSecretPosPure P dh3
    let pos4? := dh4?.map (mkSecretPosPure P)
    let (dk, fgL') ← fgPatchPure ddh maxLen pos1 pos2 pos3 pos4? ss st.fgL
    return (.drKeyResp dk, { st with fgL := fgL', advRoLog := advRoLog' })
  | none =>
    match st.rawRoCache.find? (fun (s, _) => s == secrets) with
    | some (_, dk) =>
      return (.drKeyResp dk, { st with advRoLog := advRoLog' })
    | none =>
      let dk ← sampleDRKey96
      return (.drKeyResp dk,
        { st with rawRoCache := (secrets, dk) :: st.rawRoCache, advRoLog := advRoLog' })

@[simp]
theorem simulateQ_gapDhFullImpl_fgRoQueryGdh {S : Setup} (P : Primitives)
    (ddh : Bytes → Bytes → Bytes → Bool) (maxLen : ℕ) (secrets : Bytes)
    (st : FgKeyIndSimState S) :
    simulateQ (gapDhFullImpl P ddh) (fgRoQueryGdh maxLen secrets st) =
      fgRoQueryPure P ddh maxLen secrets st := by
  unfold fgRoQueryGdh fgRoQueryPure
  cases parseRoSecrets secrets with
  | none =>
    cases st.rawRoCache.find? (fun (s, _) => s == secrets) <;> simp
  | some tup =>
    rcases tup with ⟨dh1, dh2, dh3, dh4?, ss⟩
    cases dh4? <;> simp

noncomputable def fgRunInitiatePure (P : Primitives) (ddh : Bytes → Bytes → Bytes → Bool)
    (useDh1 : Bool) (targetIdx : ℕ) (S : Setup) (maxLen : ℕ) (U : Bytes)
    (sid : SessionId S) (u : Fin S.N_id) (bundle : PreKeyBundleInput)
    (st : FgKeyIndSimState S) : ProbComp (KeyIndResponse × FgKeyIndSimState S) := do
  if st.base.sessions.any (fun e => e.sid == sid) then
    return (.noneResp, st)
  let some (_, uEntry) := st.base.principals.find? (fun (idx, _) => idx == u.val)
    | return (.noneResp, st)
  if !koskBundleOkTake S P st.base.principals st.base.spkBundles st.base.opkEntries st.advKeyPows
    bundle then
    return (.noneResp, st)
  let isTargetEph : Bool := !useDh1 && (initSessionSlotIdx sid == targetIdx)
  let ekASkRaw ← sampleScalar32
  let kemCoins ← sampleCoins32
  let sigPkB := resolveSigPk P (st.base.principals.take S.N_dh) bundle.ikB
  if !(P.sigVerify sigPkB (encodeEC bundle.spkB) bundle.spkSig &&
       P.sigVerify sigPkB (encodeKEM bundle.pqspkB) bundle.pqspkSig) then
    return (.noneResp, st)
  let some (ss, kemCt) := P.kemEncaps bundle.pqspkB kemCoins
    | return (.noneResp, st)
  let ekAPkRaw := P.x25519Base ekASkRaw
  let ekASk := if isTargetEph then [] else ekASkRaw
  let ekAPk := if isTargetEph then U else ekAPkRaw
  let spkSk := lookupSpkSkTake S P st.base.spkBundles st.advKeyPows bundle.spkB
  let pos1 := computeTwoSideOrPairPosPure P uEntry.secIKA0 spkSk uEntry.ikAPk bundle.spkB
  let pos2 := computeTwoSideOrPairPosPure P ekASk [] ekAPk bundle.ikB
  let pos3 := computeTwoSideOrPairPosPure P ekASk [] ekAPk bundle.spkB
  let pos4? := computeOptPosPure P ekASk ekAPk (bundle.opkB?.map (fun (_, opkPk) => ([], opkPk)))
  let (drKeyReal, fgL') ← fgPatchPure ddh maxLen pos1 pos2 pos3 pos4? ss st.fgL
  let hdr : HandshakeHdr := {
    ikAPk   := uEntry.ikAPk
    ekAPk   := ekAPk
    spkId   := bundle.spkId
    opkId?  := bundle.opkB?.map Prod.fst
    pqspkId := bundle.pqspkId
    kemCt   := kemCt
  }
  let honestPeer := isHonestUncorruptedPeer P (st.base.principals.take S.N_dh) bundle.ikB
  let (spkHon, opkHon, pqspkHon) :=
    checkBundleProvenanceTake S P st.base.principals st.base.spkBundles st.base.opkEntries bundle
  let sessEntry : KeyIndInitiatorEntry S := {
    sid         := sid
    honestPeer  := honestPeer
    peerIkPk    := bundle.ikB
    peerSpkPk   := bundle.spkB
    peerOpkPk?  := bundle.opkB?.map Prod.snd
    peerPqspkPk := bundle.pqspkB
    spkHonest   := spkHon
    opkHonest   := opkHon
    pqspkHonest := pqspkHon
    ekASk       := ekASk
    fresh       := honestPeer.isSome
    drKeyReal   := drKeyReal
    drKeyRand   := drKeyReal
    hdr         := hdr
    tested      := false
  }
  let drKeyRand ← chooseInitPartnerDrKeyRandPure P st.base.respSessions sessEntry
  let base' : KeyIndState S := { st.base with sessions := { sessEntry with drKeyRand :=
    drKeyRand } :: st.base.sessions }
  let st' : FgKeyIndSimState S := { st with base := base', fgL := fgL' }
  match findHonestPrincipal P (st.base.principals.take S.N_dh) bundle.ikB with
  | some _ => return (.hdrResp hdr, st')
  | none   => return (.initUnfreshResp drKeyReal hdr, st')

@[simp]
theorem simulateQ_gapDhFullImpl_fgRunInitiateGdh (P : Primitives)
    (ddh : Bytes → Bytes → Bytes → Bool) (useDh1 : Bool) (targetIdx : ℕ)
    (S : Setup) (maxLen : ℕ) (U : Bytes) (sid : SessionId S)
    (u : Fin S.N_id) (bundle : PreKeyBundleInput) (st : FgKeyIndSimState S) :
    simulateQ (gapDhFullImpl P ddh) (fgRunInitiateGdh useDh1 targetIdx S maxLen U sid u bundle st) =
      fgRunInitiatePure P ddh useDh1 targetIdx S maxLen U sid u bundle st := by
  unfold fgRunInitiateGdh fgRunInitiatePure
  by_cases hSid : (st.base.sessions.any (fun e => e.sid == sid)) = true
  · simp [hSid]
  · simp only [hSid, Bool.false_eq_true, ↓reduceIte]
    cases st.base.principals.find? (fun (idx, _) => idx == u.val) with
    | none => simp
    | some p =>
      rcases p with ⟨_, uEntry⟩
      dsimp only
      simp only [simulateQ_bind, simulateQ_gapDhFullImpl_embedPrim,
        simulateQ_primBaseImpl_koskBundleOkPrim, pure_bind]
      by_cases hKosk : (!koskBundleOkTake S P st.base.principals st.base.spkBundles
        st.base.opkEntries st.advKeyPows bundle) = true
      · simp [hKosk]
      · simp only [hKosk, Bool.false_eq_true, ↓reduceIte,
          simulateQ_bind, simulateQ_gapDhFullImpl_unifGdh,
          simulateQ_gapDhFullImpl_embedPrim, simulateQ_primBaseImpl_resolveSigPkPrim,
          simulateQ_gapDhFullImpl_primGdhQ_sigVerify, pure_bind]
        congr 1; ext ekASkRaw
        congr 1; ext kemCoins
        by_cases hv :
            (!(P.sigVerify (resolveSigPk P (st.base.principals.take S.N_dh) bundle.ikB)
                (encodeEC bundle.spkB) bundle.spkSig &&
               P.sigVerify (resolveSigPk P (st.base.principals.take S.N_dh) bundle.ikB)
                (encodeKEM bundle.pqspkB) bundle.pqspkSig)) = true
        · simp [hv]
        · simp only [hv, Bool.false_eq_true, ↓reduceIte,
            simulateQ_bind, simulateQ_gapDhFullImpl_primGdhQ_kemEncaps, pure_bind]
          cases P.kemEncaps bundle.pqspkB kemCoins with
          | none => simp
          | some sc =>
            rcases sc with ⟨ss, kemCt⟩
            simp only [simulateQ_bind, simulateQ_gapDhFullImpl_primGdhQ_x25519Base,
              simulateQ_gapDhFullImpl_embedPrim,
              simulateQ_primBaseImpl_lookupSpkSkPrim,
              simulateQ_gapDhFullImpl_computeTwoSideOrPairPos,
              simulateQ_gapDhFullImpl_computeOptPos,
              simulateQ_gapDhFullImpl_fgPatch,
              simulateQ_gapDhFullImpl_chooseInitPartnerDrKeyRandGdh,
              simulateQ_primBaseImpl_isHonestUncorruptedPeerPrim,
              simulateQ_primBaseImpl_checkBundleProvenancePrim,
              simulateQ_primBaseImpl_findHonestPrincipalPrim,
              pure_bind]
            congr 1; ext ⟨drKeyReal, fgL'⟩
            congr 1; ext drKeyRand
            cases findHonestPrincipal P (st.base.principals.take S.N_dh) bundle.ikB <;> simp

noncomputable def fgRunAcceptOPKPure (P : Primitives) (ddh : Bytes → Bytes → Bytes → Bool)
    (S : Setup) (maxLen : ℕ) (k : Fin S.N_id) (j : Fin S.N_recv) (o : Fin S.N_opk)
    (hdr : HandshakeHdr) (st : FgKeyIndSimState S) :
    ProbComp (KeyIndResponse × FgKeyIndSimState S) := do
  if !(hdr.spkId == UInt32.ofNat j.val &&
       hdr.pqspkId == UInt32.ofNat j.val &&
       hdr.opkId? == some (UInt32.ofNat o.val) &&
       hdr.ikAPk.length == 32 &&
       hdr.ekAPk.length == 32) then
    return (.noneResp, st)
  if st.base.usedRecvOPK.contains (k.val, j.val, o.val) then
    return (.noneResp, st)
  if !koskSenderOkTake S P st.base.principals st.advKeyPows hdr.ikAPk then
    return (.noneResp, st)
  let some (_, kEntry) := st.base.principals.find? (fun (idx, _) => idx == k.val)
    | return (.noneResp, st)
  let some (_, bEntry) := st.base.spkBundles.find? (fun (idx, _) => idx == (k.val, j.val))
    | return (.noneResp, st)
  let some (_, oEntry) := st.base.opkEntries.find? (fun (idx, _) => idx == (k.val, j.val, o.val))
    | return (.noneResp, st)
  if oEntry.consumed then
    return (.noneResp, st)
  let (replayOk, usedTriples') :=
    checkAndMarkKyberBaseKeySeen st.base.seenKyberBaseKeys k.val hdr.pqspkId hdr.spkId hdr.ekAPk
  let canon := P.isCanonical hdr.ekAPk
  let dh1Zero := P.x25519 (List.replicate 32 0) hdr.ikAPk
  let dh2Zero := P.x25519 (List.replicate 32 0) hdr.ekAPk
  let dh4Check := P.x25519 oEntry.opkSk hdr.ekAPk
  let ss? := P.kemDecaps bEntry.pqspkSk hdr.kemCt
  if !(replayOk && canon &&
       dh1Zero != List.replicate 32 0 &&
       dh2Zero != List.replicate 32 0 &&
       dh4Check != List.replicate 32 0) then
    return (.noneResp, st)
  let some ss := ss?
    | return (.noneResp, st)
  let pos1 := computeTwoSideOrPairPosPure P [] bEntry.spkSk hdr.ikAPk bEntry.spkPk
  let pos2 := computeTwoSideOrPairPosPure P [] kEntry.secIKA0 hdr.ekAPk kEntry.ikAPk
  let pos3 := computeTwoSideOrPairPosPure P [] bEntry.spkSk hdr.ekAPk bEntry.spkPk
  let pos4 := mkSecretPosPure P dh4Check
  let (drKey, fgL') ← fgPatchPure ddh maxLen pos1 pos2 pos3 (some pos4) ss st.fgL
  let opkEntries' := st.base.opkEntries.map (fun (idx, e) =>
    if idx == (k.val, j.val, o.val) then (idx, { e with consumed := true }) else (idx, e))
  let senderHonestOpt := findHonestPrincipal P (st.base.principals.take S.N_dh) hdr.ikAPk
  let rInit : KeyIndRespEntry S := {
    sid          := .recvOPK k j o
    respIkPk     := kEntry.ikAPk
    spkPk        := bEntry.spkPk
    opkPk?       := some oEntry.opkPk
    pqspkPk      := bEntry.pqspkPk
    hdr          := hdr
    senderHonest := senderHonestOpt.isSome
    drKeyReal    := drKey
    drKeyRand    := drKey
  }
  let drKeyRand ← choosePartnerDrKeyRandPure P st.base.sessions rInit
  let base' : KeyIndState S := { st.base with
    opkEntries       := opkEntries'
    usedRecvOPK      := (k.val, j.val, o.val) :: st.base.usedRecvOPK
    seenKyberBaseKeys := usedTriples'
    respSessions     := { rInit with drKeyRand := drKeyRand } :: st.base.respSessions
  }
  let st' : FgKeyIndSimState S := { st with base := base', fgL := fgL' }
  match senderHonestOpt with
  | some _ => return (.acceptFreshResp, st')
  | none   => return (.drKeyResp drKey, st')

@[simp]
theorem simulateQ_gapDhFullImpl_fgRunAcceptOPKGdh (P : Primitives)
    (ddh : Bytes → Bytes → Bytes → Bool) (S : Setup) (maxLen : ℕ)
    (k : Fin S.N_id) (j : Fin S.N_recv) (o : Fin S.N_opk)
    (hdr : HandshakeHdr) (st : FgKeyIndSimState S) :
    simulateQ (gapDhFullImpl P ddh) (fgRunAcceptOPKGdh S maxLen k j o hdr st) =
      fgRunAcceptOPKPure P ddh S maxLen k j o hdr st := by
  unfold fgRunAcceptOPKGdh fgRunAcceptOPKPure
  by_cases hHdr : (!(hdr.spkId == UInt32.ofNat j.val &&
       hdr.pqspkId == UInt32.ofNat j.val &&
       hdr.opkId? == some (UInt32.ofNat o.val) &&
       hdr.ikAPk.length == 32 &&
       hdr.ekAPk.length == 32)) = true
  · simp only [hHdr, ↓reduceIte, simulateQ_pure]
  · simp only [hHdr, Bool.false_eq_true, ↓reduceIte]
    by_cases hUsed : (st.base.usedRecvOPK.contains (k.val, j.val, o.val)) = true
    · simp only [hUsed, ↓reduceIte, simulateQ_pure]
    · simp only [hUsed, Bool.false_eq_true, ↓reduceIte,
        simulateQ_bind, simulateQ_gapDhFullImpl_embedPrim,
        simulateQ_primBaseImpl_koskSenderOkPrim, pure_bind]
      by_cases hSender : (!koskSenderOkTake S P st.base.principals st.advKeyPows hdr.ikAPk) = true
      · simp only [hSender, ↓reduceIte, simulateQ_pure]
      · simp only [hSender, Bool.false_eq_true, ↓reduceIte]
        cases st.base.principals.find? (fun (idx, _) => idx == k.val) with
      | none => simp
      | some pk =>
        rcases pk with ⟨_, kEntry⟩
        dsimp only
        cases st.base.spkBundles.find? (fun (idx, _) => idx == (k.val, j.val)) with
        | none => simp
        | some pb =>
          rcases pb with ⟨_, bEntry⟩
          dsimp only
          cases st.base.opkEntries.find? (fun (idx, _) => idx == (k.val, j.val, o.val)) with
          | none => simp
          | some po =>
            rcases po with ⟨_, oEntry⟩
            dsimp only
            by_cases hCons : oEntry.consumed = true
            · simp only [hCons, ↓reduceIte, simulateQ_pure]
            · simp only [hCons, Bool.false_eq_true, ↓reduceIte]
              rcases checkAndMarkKyberBaseKeySeen st.base.seenKyberBaseKeys k.val hdr.pqspkId hdr.spkId
                hdr.ekAPk with ⟨replayOk, usedTriples'⟩
              dsimp only
              simp only [simulateQ_bind,
                simulateQ_gapDhFullImpl_primGdhQ_isCanonical,
                simulateQ_gapDhFullImpl_primGdhQ_x25519,
                simulateQ_gapDhFullImpl_primGdhQ_kemDecaps,
                pure_bind]
              by_cases hChk : (!(replayOk && P.isCanonical hdr.ekAPk &&
                   P.x25519 (List.replicate 32 0) hdr.ikAPk != List.replicate 32 0 &&
                   P.x25519 (List.replicate 32 0) hdr.ekAPk != List.replicate 32 0 &&
                   P.x25519 oEntry.opkSk hdr.ekAPk != List.replicate 32 0)) = true
              · simp only [hChk, ↓reduceIte, simulateQ_pure]
              · simp only [hChk, Bool.false_eq_true, ↓reduceIte]
                cases P.kemDecaps bEntry.pqspkSk hdr.kemCt with
                | none => simp
                | some ss =>
                  simp only [simulateQ_bind,
                    simulateQ_gapDhFullImpl_computeTwoSideOrPairPos,
                    simulateQ_gapDhFullImpl_mkSecretPos,
                    simulateQ_gapDhFullImpl_fgPatch,
                    simulateQ_gapDhFullImpl_embedPrim,
                    simulateQ_primBaseImpl_findHonestPrincipalPrim,
                    simulateQ_gapDhFullImpl_choosePartnerDrKeyRandGdh,
                    pure_bind]
                  congr 1; ext ⟨drKey, fgL'⟩
                  congr 1; ext drKeyRand
                  cases findHonestPrincipal P (st.base.principals.take S.N_dh) hdr.ikAPk <;> simp

noncomputable def fgRunAcceptNoOPKPure (P : Primitives) (ddh : Bytes → Bytes → Bytes → Bool)
    (S : Setup) (maxLen : ℕ) (k : Fin S.N_id) (j : Fin S.N_recv) (l : Fin S.N_no_opk)
    (hdr : HandshakeHdr) (st : FgKeyIndSimState S) :
    ProbComp (KeyIndResponse × FgKeyIndSimState S) := do
  if !(hdr.spkId == UInt32.ofNat j.val &&
       hdr.pqspkId == UInt32.ofNat j.val &&
       hdr.opkId? == none &&
       hdr.ikAPk.length == 32 &&
       hdr.ekAPk.length == 32) then
    return (.noneResp, st)
  if st.base.usedRecvNoOPK.contains (k.val, j.val, l.val) then
    return (.noneResp, st)
  if !koskSenderOkTake S P st.base.principals st.advKeyPows hdr.ikAPk then
    return (.noneResp, st)
  let some (_, kEntry) := st.base.principals.find? (fun (idx, _) => idx == k.val)
    | return (.noneResp, st)
  let some (_, bEntry) := st.base.spkBundles.find? (fun (idx, _) => idx == (k.val, j.val))
    | return (.noneResp, st)
  let (replayOk, usedTriples') :=
    checkAndMarkKyberBaseKeySeen st.base.seenKyberBaseKeys k.val hdr.pqspkId hdr.spkId hdr.ekAPk
  let canon := P.isCanonical hdr.ekAPk
  let dh1Zero := P.x25519 (List.replicate 32 0) hdr.ikAPk
  let dh2Zero := P.x25519 (List.replicate 32 0) hdr.ekAPk
  let ss? := P.kemDecaps bEntry.pqspkSk hdr.kemCt
  if !(replayOk && canon &&
       dh1Zero != List.replicate 32 0 &&
       dh2Zero != List.replicate 32 0) then
    return (.noneResp, st)
  let some ss := ss?
    | return (.noneResp, st)
  let pos1 := computeTwoSideOrPairPosPure P [] bEntry.spkSk hdr.ikAPk bEntry.spkPk
  let pos2 := computeTwoSideOrPairPosPure P [] kEntry.secIKA0 hdr.ekAPk kEntry.ikAPk
  let pos3 := computeTwoSideOrPairPosPure P [] bEntry.spkSk hdr.ekAPk bEntry.spkPk
  let (drKey, fgL') ← fgPatchPure ddh maxLen pos1 pos2 pos3 none ss st.fgL
  let senderHonestOpt := findHonestPrincipal P (st.base.principals.take S.N_dh) hdr.ikAPk
  let rInit : KeyIndRespEntry S := {
    sid          := .recvNoOPK k j l
    respIkPk     := kEntry.ikAPk
    spkPk        := bEntry.spkPk
    opkPk?       := none
    pqspkPk      := bEntry.pqspkPk
    hdr          := hdr
    senderHonest := senderHonestOpt.isSome
    drKeyReal    := drKey
    drKeyRand    := drKey
  }
  let drKeyRand ← choosePartnerDrKeyRandPure P st.base.sessions rInit
  let base' : KeyIndState S := { st.base with
    usedRecvNoOPK    := (k.val, j.val, l.val) :: st.base.usedRecvNoOPK
    seenKyberBaseKeys := usedTriples'
    respSessions     := { rInit with drKeyRand := drKeyRand } :: st.base.respSessions
  }
  let st' : FgKeyIndSimState S := { st with base := base', fgL := fgL' }
  match senderHonestOpt with
  | some _ => return (.acceptFreshResp, st')
  | none   => return (.drKeyResp drKey, st')

@[simp]
theorem simulateQ_gapDhFullImpl_fgRunAcceptNoOPKGdh (P : Primitives)
    (ddh : Bytes → Bytes → Bytes → Bool) (S : Setup) (maxLen : ℕ)
    (k : Fin S.N_id) (j : Fin S.N_recv) (l : Fin S.N_no_opk)
    (hdr : HandshakeHdr) (st : FgKeyIndSimState S) :
    simulateQ (gapDhFullImpl P ddh) (fgRunAcceptNoOPKGdh S maxLen k j l hdr st) =
      fgRunAcceptNoOPKPure P ddh S maxLen k j l hdr st := by
  unfold fgRunAcceptNoOPKGdh fgRunAcceptNoOPKPure
  by_cases hHdr : (!(hdr.spkId == UInt32.ofNat j.val &&
       hdr.pqspkId == UInt32.ofNat j.val &&
       hdr.opkId? == none &&
       hdr.ikAPk.length == 32 &&
       hdr.ekAPk.length == 32)) = true
  · simp only [hHdr, ↓reduceIte, simulateQ_pure]
  · simp only [hHdr, Bool.false_eq_true, ↓reduceIte]
    by_cases hUsed : (st.base.usedRecvNoOPK.contains (k.val, j.val, l.val)) = true
    · simp only [hUsed, ↓reduceIte, simulateQ_pure]
    · simp only [hUsed, Bool.false_eq_true, ↓reduceIte,
        simulateQ_bind, simulateQ_gapDhFullImpl_embedPrim,
        simulateQ_primBaseImpl_koskSenderOkPrim, pure_bind]
      by_cases hSender : (!koskSenderOkTake S P st.base.principals st.advKeyPows hdr.ikAPk) = true
      · simp only [hSender, ↓reduceIte, simulateQ_pure]
      · simp only [hSender, Bool.false_eq_true, ↓reduceIte]
        cases st.base.principals.find? (fun (idx, _) => idx == k.val) with
      | none => simp
      | some pk =>
        rcases pk with ⟨_, kEntry⟩
        dsimp only
        cases st.base.spkBundles.find? (fun (idx, _) => idx == (k.val, j.val)) with
        | none => simp
        | some pb =>
          rcases pb with ⟨_, bEntry⟩
          dsimp only
          rcases checkAndMarkKyberBaseKeySeen st.base.seenKyberBaseKeys k.val hdr.pqspkId hdr.spkId
            hdr.ekAPk with ⟨replayOk, usedTriples'⟩
          dsimp only
          simp only [simulateQ_bind,
            simulateQ_gapDhFullImpl_primGdhQ_isCanonical,
            simulateQ_gapDhFullImpl_primGdhQ_x25519,
            simulateQ_gapDhFullImpl_primGdhQ_kemDecaps,
            pure_bind]
          by_cases hChk : (!(replayOk && P.isCanonical hdr.ekAPk &&
               P.x25519 (List.replicate 32 0) hdr.ikAPk != List.replicate 32 0 &&
               P.x25519 (List.replicate 32 0) hdr.ekAPk != List.replicate 32 0)) = true
          · simp only [hChk, ↓reduceIte, simulateQ_pure]
          · simp only [hChk, Bool.false_eq_true, ↓reduceIte]
            cases P.kemDecaps bEntry.pqspkSk hdr.kemCt with
            | none => simp
            | some ss =>
              simp only [simulateQ_bind,
                simulateQ_gapDhFullImpl_computeTwoSideOrPairPos,
                simulateQ_gapDhFullImpl_fgPatch,
                simulateQ_gapDhFullImpl_embedPrim,
                simulateQ_primBaseImpl_findHonestPrincipalPrim,
                simulateQ_gapDhFullImpl_choosePartnerDrKeyRandGdh,
                pure_bind]
              congr 1; ext ⟨drKey, fgL'⟩
              congr 1; ext drKeyRand
              cases findHonestPrincipal P (st.base.principals.take S.N_dh) hdr.ikAPk <;> simp

/-- Pure `ProbComp` version of `fgKeyIndStep`. -/
noncomputable def fgKeyIndStepPure (P : Primitives) (ddh : Bytes → Bytes → Bytes → Bool)
    (useDh1 : Bool) (targetIdx targetSpkIdx : ℕ) (S : Setup) (maxLen : ℕ)
    (U V : Bytes) (q : KeyIndQuery S) (st : FgKeyIndSimState S) :
    ProbComp (KeyIndResponse × FgKeyIndSimState S) := do
  match q with
  | .initPrin u =>
    if st.base.principals.any (fun (idx, _) => idx == u.val) then
      return (.noneResp, st)
    let isTargetPrin : Bool := useDh1 && (u.val == targetIdx)
    let secIKA0Raw ← sampleScalar32
    let ikAPkRaw := P.x25519Base secIKA0Raw
    let secIKAsign ← sampleScalar32
    let ikSignPk := P.sigPkGen secIKAsign
    let entry : PrincipalEntry := {
      secIKA0    := if isTargetPrin then [] else secIKA0Raw
      ikAPk      := if isTargetPrin then U else ikAPkRaw
      secIKAsign := secIKAsign
      ikSignPk   := ikSignPk
      corrupted  := false
    }
    let base' := { st.base with principals := (u.val, entry) :: st.base.principals }
    return (.initPrinResp entry.ikAPk entry.ikSignPk, { st with base := base' })
  | .corruptIK u =>
    match st.base.principals.find? (fun (idx, _) => idx == u.val) with
    | none => return (.noneResp, st)
    | some (_, entry) =>
      let principals' := st.base.principals.map (fun (idx, e) =>
        if idx == u.val then (idx, { e with corrupted := true }) else (idx, e))
      let base' := { st.base with principals := principals' }
      return (.corrResp entry.secIKA0 entry.secIKAsign, { st with base := base' })
  | .genSPK u j =>
    if st.base.spkBundles.any (fun (k, _) => k == (u.val, j.val)) then
      return (.noneResp, st)
    let some (_, uEntry) := st.base.principals.find? (fun (idx, _) => idx == u.val)
      | return (.noneResp, st)
    let isTargetSpk : Bool := spkBundleFlatIdx S u j == targetSpkIdx
    let spkSkRaw ← sampleScalar32
    let spkPkRaw := P.x25519Base spkSkRaw
    let spkSk := if isTargetSpk then [] else spkSkRaw
    let spkPk := if isTargetSpk then V else spkPkRaw
    let rSpk ← sampleRandom64
    let spkSig := P.sigSign uEntry.secIKAsign (encodeEC spkPk) rSpk
    let seedKem ← sampleRandom64
    let (pqspkPk, pqspkSk) := P.kemKeyGen seedKem
    let rPq ← sampleRandom64
    let pqspkSig := P.sigSign uEntry.secIKAsign (encodeKEM pqspkPk) rPq
    let bEntry : SpkBundleEntry := {
      spkSk    := spkSk
      spkPk    := spkPk
      spkSig   := spkSig
      pqspkSk  := pqspkSk
      pqspkPk  := pqspkPk
      pqspkSig := pqspkSig
    }
    let base' := { st.base with spkBundles := ((u.val, j.val), bEntry) :: st.base.spkBundles }
    let bundleOut : PreKeyBundleInput := {
      ikB      := uEntry.ikAPk
      spkId    := UInt32.ofNat j.val
      spkB     := spkPk
      spkSig   := spkSig
      opkB?    := none
      pqspkId  := UInt32.ofNat j.val
      pqspkB   := pqspkPk
      pqspkSig := pqspkSig
    }
    return (.bundleResp bundleOut, { st with base := base' })
  | .genOPK u j o =>
    if st.base.opkEntries.any (fun (k, _) => k == (u.val, j.val, o.val)) then
      return (.noneResp, st)
    let opkSk ← sampleScalar32
    let opkPk := P.x25519Base opkSk
    let oEntry : OpkEntry := { opkSk := opkSk, opkPk := opkPk, consumed := false }
    let base' := { st.base with opkEntries := ((u.val, j.val, o.val),
      oEntry) :: st.base.opkEntries }
    return (.pkResp opkPk, { st with base := base' })
  | .initiateOPK u i bundle =>
    if bundle.opkB?.isNone then
      return (.noneResp, st)
    fgRunInitiatePure P ddh useDh1 targetIdx S maxLen U (.sendOPK u i) u bundle st
  | .initiateNoOPK u i bundle =>
    if bundle.opkB?.isSome then
      return (.noneResp, st)
    fgRunInitiatePure P ddh useDh1 targetIdx S maxLen U (.sendNoOPK u i) u bundle st
  | .acceptOPK k j o hdr =>
    fgRunAcceptOPKPure P ddh S maxLen k j o hdr st
  | .acceptNoOPK k j l hdr =>
    fgRunAcceptNoOPKPure P ddh S maxLen k j l hdr st
  | .testSession sid =>
    if !isKeyIndSessionTestable st.base sid then
      return (.noneResp, st)
    match st.base.sessions.find? (fun e => e.sid == sid) with
    | some e =>
      let sessions' := st.base.sessions.map (fun s =>
        if s.sid == sid then { s with tested := true } else s)
      let base' := { st.base with sessions := sessions' }
      return (.drKeyResp (if st.base.secb then e.drKeyReal else e.drKeyRand), { st with base :=
        base' })
    | none =>
      match st.base.respSessions.find? (fun r => r.sid == sid) with
      | none => return (.noneResp, st)
      | some r =>
        let resp' := st.base.respSessions.map (fun x =>
          if x.sid == sid then { x with tested := true } else x)
        let base' := { st.base with respSessions := resp' }
        return (.drKeyResp (if st.base.secb then r.drKeyReal else r.drKeyRand), { st with base :=
          base' })
  | .revealSessionKey sid =>
    match st.base.sessions.find? (fun e => e.sid == sid) with
    | some e =>
      if e.tested then return (.noneResp, st)
      let sessions' := st.base.sessions.map (fun s =>
        if s.sid == sid then { s with revealed := true } else s)
      let base' := { st.base with sessions := sessions' }
      return (.drKeyResp e.drKeyReal, { st with base := base' })
    | none =>
      match st.base.respSessions.find? (fun r => r.sid == sid) with
      | none => return (.noneResp, st)
      | some r =>
        if r.tested then return (.noneResp, st)
        let resp' := st.base.respSessions.map (fun x =>
          if x.sid == sid then { x with revealed := true } else x)
        let base' := { st.base with respSessions := resp' }
        return (.drKeyResp r.drKeyReal, { st with base := base' })
  | .roQuery secrets =>
    fgRoQueryPure P ddh maxLen secrets st
  | .revealDhSecrets =>
    return (.noneResp, st)
  | .revealSpkSk u j =>
    match st.base.spkBundles.find? (fun (idx, _) => idx == (u.val, j.val)) with
    | none => return (.noneResp, st)
    | some (_, bEntry) =>
      let spkBundles' := st.base.spkBundles.map (fun (idx, b) =>
        if idx == (u.val, j.val) then (idx, { b with revealed := true }) else (idx, b))
      let base' := { st.base with spkBundles := spkBundles' }
      return (.spkSkResp bEntry.spkSk, { st with base := base' })
  | .registerKey sk =>
    if sk.length != 32 then
      return (.noneResp, st)
    let pk := P.x25519Base sk
    let wPk := P.pow8 pk
    let base' := { st.base with advKeys := (sk, pk) :: st.base.advKeys }
    return (.pkResp pk, { st with base := base', advKeyPows := (sk, wPk) :: st.advKeyPows })

@[simp]
theorem simulateQ_gapDhFullImpl_fgKeyIndStep (P : Primitives)
    (ddh : Bytes → Bytes → Bytes → Bool) (useDh1 : Bool) (targetIdx targetSpkIdx : ℕ)
    (S : Setup) (maxLen : ℕ) (U V : Bytes) (q : KeyIndQuery S) (st : FgKeyIndSimState S) :
    simulateQ (gapDhFullImpl P ddh)
      (fgKeyIndStep useDh1 targetIdx targetSpkIdx S maxLen U V q st) =
      fgKeyIndStepPure P ddh useDh1 targetIdx targetSpkIdx S maxLen U V q st := by
  cases q with
  | initPrin u =>
    simp only [fgKeyIndStep, fgKeyIndStepPure]
    split_ifs <;> simp
  | corruptIK u =>
    simp only [fgKeyIndStep, fgKeyIndStepPure]
    cases st.base.principals.find? (fun (idx, _) => idx == u.val) <;> simp
  | genSPK u j =>
    simp only [fgKeyIndStep, fgKeyIndStepPure]
    by_cases hAny : (st.base.spkBundles.any (fun (k, _) => k == (u.val, j.val))) = true
    · simp [hAny]
    · simp only [hAny, Bool.false_eq_true, ↓reduceIte]
      cases st.base.principals.find? (fun (idx, _) => idx == u.val) with
      | none => simp
      | some p =>
        rcases p with ⟨_, uEntry⟩
        dsimp only
        simp only [simulateQ_bind, simulateQ_gapDhFullImpl_unifGdh,
          simulateQ_gapDhFullImpl_primGdhQ_x25519Base,
          simulateQ_gapDhFullImpl_primGdhQ_sigSign,
          simulateQ_gapDhFullImpl_primGdhQ_kemKeyGen,
          pure_bind, simulateQ_pure]
  | genOPK u j o =>
    simp only [fgKeyIndStep, fgKeyIndStepPure]
    split_ifs <;> simp
  | initiateOPK u i bundle =>
    simp only [fgKeyIndStep, fgKeyIndStepPure]
    split_ifs <;> simp
  | initiateNoOPK u i bundle =>
    simp only [fgKeyIndStep, fgKeyIndStepPure]
    split_ifs <;> simp
  | acceptOPK k j o hdr =>
    simp [fgKeyIndStep, fgKeyIndStepPure]
  | acceptNoOPK k j l hdr =>
    simp [fgKeyIndStep, fgKeyIndStepPure]
  | testSession sid =>
    simp only [fgKeyIndStep, fgKeyIndStepPure]
    by_cases hFresh : (!isKeyIndSessionTestable st.base sid) = true
    · simp [hFresh]
    · simp only [hFresh, Bool.false_eq_true, ↓reduceIte]
      cases st.base.sessions.find? (fun e => e.sid == sid) with
      | some e => simp
      | none =>
        dsimp only
        cases st.base.respSessions.find? (fun r => r.sid == sid) <;> simp
  | revealSessionKey sid =>
    simp only [fgKeyIndStep, fgKeyIndStepPure]
    cases st.base.sessions.find? (fun e => e.sid == sid) with
    | some e =>
      dsimp only
      by_cases hTest : e.tested = true <;> simp [hTest]
    | none =>
      dsimp only
      cases st.base.respSessions.find? (fun r => r.sid == sid) with
      | none => simp
      | some r =>
        dsimp only
        by_cases hTest : r.tested = true <;> simp [hTest]
  | roQuery secrets =>
    simp [fgKeyIndStep, fgKeyIndStepPure]
  | revealDhSecrets =>
    simp [fgKeyIndStep, fgKeyIndStepPure]
  | revealSpkSk u j =>
    simp only [fgKeyIndStep, fgKeyIndStepPure]
    cases st.base.spkBundles.find? (fun (idx, _) => idx == (u.val, j.val)) <;> simp
  | registerKey sk =>
    simp only [fgKeyIndStep, fgKeyIndStepPure]
    split_ifs <;> simp

/-! ## Up-to-bad coupling -/

theorem simulateQ_run_query_inl {ι : Type} {QSpec : OracleSpec.{0, 0} ι} {St α : Type}
    (impl : QueryImpl QSpec (StateT St ProbComp)) (uq : unifSpec.Domain)
    (oa : (unifSpec + QSpec).Range (Sum.inl uq) → OracleComp (unifSpec + QSpec) α) (st : St) :
    (simulateQ ((QueryImpl.ofLift unifSpec ProbComp).liftTarget (StateT St ProbComp) + impl)
      (liftM (OracleSpec.query (Sum.inl uq)) >>= oa)).run st =
    (liftM (unifSpec.query uq) >>= fun u =>
      (simulateQ ((QueryImpl.ofLift unifSpec ProbComp).liftTarget (StateT St ProbComp) + impl)
        (oa u)).run st) := by
  simp [simulateQ_bind, QueryImpl.liftTarget, StateT.run_bind, StateT.run_monadLift]

theorem simulateQ_run_query_inr {ι : Type} {QSpec : OracleSpec.{0, 0} ι} {St α : Type}
    (impl : QueryImpl QSpec (StateT St ProbComp)) (gq : ι)
    (oa : (unifSpec + QSpec).Range (Sum.inr gq) → OracleComp (unifSpec + QSpec) α) (st : St) :
    (simulateQ ((QueryImpl.ofLift unifSpec ProbComp).liftTarget (StateT St ProbComp) + impl)
      (liftM (OracleSpec.query (Sum.inr gq)) >>= oa)).run st =
    ((impl gq).run st >>= fun y =>
      (simulateQ ((QueryImpl.ofLift unifSpec ProbComp).liftTarget (StateT St ProbComp) + impl)
        (oa y.1)).run y.2) := by
  simp [simulateQ_bind, StateT.run_bind]

theorem le_probExpect_const_of_support {α : Type} (mx : ProbComp α) (f : α → ℝ≥0∞) (c : ℝ≥0∞)
    (h : ∀ x ∈ support mx, c ≤ f x) :
    c ≤ probExpect mx f := by
  calc c = probExpect mx (fun _ => c) := (probExpect_const mx c).symm
    _ ≤ probExpect mx f := probExpect_mono_of_support mx (fun _ => c) f h

theorem probExpect_eq_zero_of_support {α : Type} (mx : ProbComp α) (f : α → ℝ≥0∞)
    (h : ∀ x ∈ support mx, f x = 0) :
    probExpect mx f = 0 :=
  le_antisymm (probExpect_const_le_of_support mx f 0 (fun x hx => le_of_eq (h x hx))) bot_le

def spkBundleFlatIdxVal (S : Setup) (k : Nat × Nat) : Nat :=
  k.1 * S.N_recv + k.2

theorem toReal_any_double_range_le_sum2 {α : Type} (mx : ProbComp α) (n1 n2 : Nat)
    (badAt : Nat → Nat → α → Bool) :
    (𝒟[mx >>= fun a => pure ((List.range n1).any (fun i =>
      (List.range n2).any (fun j => badAt i j a)))] {true}).toReal ≤
      ∑ i ∈ Finset.range n1, ∑ j ∈ Finset.range n2,
        (𝒟[mx >>= fun a => pure (badAt i j a)] {true}).toReal := by
  calc (𝒟[mx >>= fun a => pure ((List.range n1).any (fun i =>
        (List.range n2).any (fun j => badAt i j a)))] {true}).toReal
      ≤ ∑ i ∈ Finset.range n1,
          (𝒟[mx >>= fun a => pure ((List.range n2).any (fun j => badAt i j a))] {true}).toReal :=
        toReal_any_range_le_sum mx n1 (fun i a => (List.range n2).any (fun j => badAt i j a))
    _ ≤ ∑ i ∈ Finset.range n1, ∑ j ∈ Finset.range n2,
          (𝒟[mx >>= fun a => pure (badAt i j a)] {true}).toReal :=
        Finset.sum_le_sum (fun i _ => toReal_any_range_le_sum mx n2 (badAt i))

theorem simulateQ_bad_mono
    {ι : Type} {QSpec : OracleSpec.{0, 0} ι} {St α : Type}
    (impl : QueryImpl QSpec (StateT St ProbComp))
    (bad : St → Bool)
    (hBadMono : ∀ (q : ι) (s : St), bad s = true →
      ∀ y ∈ support ((impl q).run s), bad y.2 = true)
    (oa : OracleComp (unifSpec + QSpec) α) (s : St)
    (hBad : bad s = true) :
    let fullImpl := (QueryImpl.ofLift unifSpec ProbComp).liftTarget (StateT St ProbComp) + impl
    ∀ x ∈ support ((simulateQ fullImpl oa).run s), bad x.2 = true := by
  intro fullImpl
  induction oa using OracleComp.inductionOn generalizing s with
  | pure a =>
    intro x hx
    simp only [simulateQ_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff] at hx
    subst hx; exact hBad
  | query_bind q oa ih =>
    cases q with
    | inl uq =>
      intro x hx
      dsimp only [fullImpl] at hx
      rw [simulateQ_run_query_inl, MonadAttach.mem_support_bind] at hx
      rcases hx with ⟨u, _, hx'⟩
      exact ih u s hBad x hx'
    | inr gq =>
      intro x hx
      dsimp only [fullImpl] at hx
      rw [simulateQ_run_query_inr, MonadAttach.mem_support_bind] at hx
      rcases hx with ⟨y, hy, hx'⟩
      exact ih y.1 y.2 (hBadMono gq s hBad y hy) x hx'

theorem probExpect_eq_const_of_support {α : Type} (mx : ProbComp α) (f : α → ℝ≥0∞) (c : ℝ≥0∞)
    (h : ∀ x ∈ support mx, f x = c) :
    probExpect mx f = c :=
  le_antisymm
    (probExpect_const_le_of_support mx f c (fun x hx => le_of_eq (h x hx)))
    (le_probExpect_const_of_support mx f c (fun x hx => le_of_eq (h x hx).symm))

def RelProbUpToBad {α : Type} (R : α → α → Prop) (bad : α → Bool)
    (m5 m6 : ProbComp α) : Prop :=
  (∀ (w5 w6 : α → ℝ≥0∞),
    (∀ y5, w5 y5 ≤ 1) →
    (∀ y6, bad y6 = true → w6 y6 = 1) →
    (∀ y5 y6, R y5 y6 → w5 y5 ≤ w6 y6) →
    probExpect m5 w5 ≤ probExpect m6 w6) ∧
  (∀ (w6 w5 : α → ℝ≥0∞),
    (∀ y6, bad y6 = true → w6 y6 = 0) →
    (∀ y5 y6, R y5 y6 → w6 y6 ≤ w5 y5) →
    probExpect m6 w6 ≤ probExpect m5 w5)

theorem RelProbUpToBad.of_pure {α : Type} {R : α → α → Prop} {bad : α → Bool}
    {x5 x6 : α} (h : R x5 x6) :
    RelProbUpToBad R bad (pure x5) (pure x6) := by
  refine ⟨fun w5 w6 _ _ hle => ?_, fun w6 w5 _ hle => ?_⟩
  · simp only [probExpect_pure]; exact hle x5 x6 h
  · simp only [probExpect_pure]; exact hle x5 x6 h

theorem RelProbUpToBad.bad6 {α : Type} {R : α → α → Prop} {bad : α → Bool}
    (m5 m6 : ProbComp α) (hbad : ∀ y6 ∈ support m6, bad y6 = true) :
    RelProbUpToBad R bad m5 m6 := by
  refine ⟨fun w5 w6 hw5 hw6 _ => ?_, fun w6 w5 hw6 _ => ?_⟩
  · calc probExpect m5 w5
        ≤ 1 := probExpect_const_le_of_support m5 w5 1 (fun y5 _ => hw5 y5)
      _ = probExpect m6 w6 :=
          (probExpect_eq_const_of_support m6 w6 1 (fun y6 hy6 => hw6 y6 (hbad y6 hy6))).symm
  · calc probExpect m6 w6
        = 0 := probExpect_eq_zero_of_support m6 w6 (fun y6 hy6 => hw6 y6 (hbad y6 hy6))
      _ ≤ probExpect m5 w5 := zero_le

theorem RelProbUpToBad.bind_same {β α : Type} {R : α → α → Prop} {bad : α → Bool}
    (mx : ProbComp β) {f5 f6 : β → ProbComp α}
    (h : ∀ b, RelProbUpToBad R bad (f5 b) (f6 b)) :
    RelProbUpToBad R bad (mx >>= f5) (mx >>= f6) := by
  refine ⟨fun w5 w6 hw5 hw6 hle => ?_, fun w6 w5 hw6 hle => ?_⟩
  · rw [probExpect_bind, probExpect_bind]
    exact probExpect_mono_of_support mx _ _ (fun b _ => (h b).1 w5 w6 hw5 hw6 hle)
  · rw [probExpect_bind, probExpect_bind]
    exact probExpect_mono_of_support mx _ _ (fun b _ => (h b).2 w6 w5 hw6 hle)

theorem RelProbUpToBad.bind_rel {β α : Type}
    {R1 : β → β → Prop} {bad1 : β → Bool}
    {R2 : α → α → Prop} {bad2 : α → Bool}
    {m5 m6 : ProbComp β} {f5 f6 : β → ProbComp α}
    (hm : RelProbUpToBad R1 bad1 m5 m6)
    (hbad : ∀ b6, bad1 b6 = true → ∀ y6 ∈ support (f6 b6), bad2 y6 = true)
    (hf : ∀ b5 b6, R1 b5 b6 → RelProbUpToBad R2 bad2 (f5 b5) (f6 b6)) :
    RelProbUpToBad R2 bad2 (m5 >>= f5) (m6 >>= f6) := by
  refine ⟨fun w5 w6 hw5 hw6 hle => ?_, fun w6 w5 hw6 hle => ?_⟩
  · rw [probExpect_bind, probExpect_bind]
    refine hm.1 _ _ ?_ ?_ ?_
    · intro b5
      exact probExpect_const_le_of_support _ _ 1 (fun y5 _ => hw5 y5)
    · intro b6 hb6
      exact probExpect_eq_const_of_support _ _ 1 (fun y6 hy6 => hw6 y6 (hbad b6 hb6 y6 hy6))
    · intro b5 b6 hR1
      exact (hf b5 b6 hR1).1 w5 w6 hw5 hw6 hle
  · rw [probExpect_bind, probExpect_bind]
    refine hm.2 _ _ ?_ ?_
    · intro b6 hb6
      exact probExpect_eq_zero_of_support _ _ (fun y6 hy6 => hw6 y6 (hbad b6 hb6 y6 hy6))
    · intro b5 b6 hR1
      exact (hf b5 b6 hR1).2 w6 w5 hw6 hle

end Proofs.SignalPqxdh.Security.FgGapDh
