/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Computational.Proofs.SignalPqxdh.Security.FgGapDhB
import VCVio.EvalDist.Monad.Basic
import VCVio.OracleComp.EvalDist.Measure

@[expose] public section

/-!
# Fiedler–Günther `KeyInd` Bad Events and Pre-Sampling

Coupling-up-to-bad lemmas for `simulateQ`, the cutoff `KeyInd` game `runKeyIndFgSim` with its
Case A and Case C bad events, and the pre-sampled implementation `pqxdhKeyIndFgPreImpl`.
-/

open SignalPqxdh
open OracleSpec OracleComp
open MeasureTheory
open scoped ENNReal

open SignalPqxdh.Security

namespace Proofs.SignalPqxdh.Security.FgGapDh

open _root_.SignalPqxdh.Security.FgGapDh

theorem simulateQ_relProbUpToBad
    {ι : Type} {QSpec : OracleSpec.{0, 0} ι} {St α : Type}
    (impl5 impl6 : QueryImpl QSpec (StateT St ProbComp))
    (Agree : St → St → Prop)
    (bad : St → Bool)
    (hBadMono : ∀ (q : ι) (s6 : St), bad s6 = true →
      ∀ y ∈ support ((impl6 q).run s6), bad y.2 = true)
    (hStep : ∀ (q : ι) (s5 s6 : St), Agree s5 s6 →
      RelProbUpToBad (fun y5 y6 => y5.1 = y6.1 ∧ Agree y5.2 y6.2) (fun y6 => bad y6.2)
        ((impl5 q).run s5) ((impl6 q).run s6))
    (oa : OracleComp (unifSpec + QSpec) α) (s5 s6 : St)
    (hAgree : Agree s5 s6) :
    let full5 := (QueryImpl.ofLift unifSpec ProbComp).liftTarget (StateT St ProbComp) + impl5
    let full6 := (QueryImpl.ofLift unifSpec ProbComp).liftTarget (StateT St ProbComp) + impl6
    RelProbUpToBad (fun x5 x6 => x5.1 = x6.1 ∧ Agree x5.2 x6.2) (fun x6 => bad x6.2)
      ((simulateQ full5 oa).run s5) ((simulateQ full6 oa).run s6) := by
  intro full5 full6
  induction oa using OracleComp.inductionOn generalizing s5 s6 with
  | pure a =>
    exact RelProbUpToBad.of_pure ⟨rfl, hAgree⟩
  | query_bind q oa ih =>
    cases q with
    | inl uq =>
      dsimp only [full5, full6]
      rw [simulateQ_run_query_inl, simulateQ_run_query_inl]
      exact RelProbUpToBad.bind_same _ (fun u => ih u s5 s6 hAgree)
    | inr gq =>
      dsimp only [full5, full6]
      rw [simulateQ_run_query_inr, simulateQ_run_query_inr]
      exact RelProbUpToBad.bind_rel (hStep gq s5 s6 hAgree)
        (fun y6 hb x6 hx6 => simulateQ_bad_mono impl6 bad hBadMono (oa y6.1) y6.2 hb x6 hx6)
        (fun y5 y6 ⟨hr, hAg⟩ => hr ▸ ih y6.1 y5.2 y6.2 hAg)

theorem probExpect_add_le {α : Type} (mx : ProbComp α) (f g h : α → ℝ≥0∞)
    (hle : ∀ x, f x ≤ g x + h x) :
    probExpect mx f ≤ probExpect mx g + probExpect mx h := by
  let _ : MeasurableSpace α := ⊤
  have _ : DiscreteMeasurableSpace α := ⟨fun _ => trivial⟩
  unfold probExpect
  calc ∫⁻ a, f a ∂𝒟[mx]
      ≤ ∫⁻ a, (g a + h a) ∂𝒟[mx] := MeasureTheory.lintegral_mono hle
    _ = (∫⁻ a, g a ∂𝒟[mx]) + (∫⁻ a, h a ∂𝒟[mx]) :=
        MeasureTheory.lintegral_add_left Measurable.of_discrete _

theorem RelProbUpToBad.evalDist_bind_le {α : Type} {R : α → α → Prop} {bad : α → Bool}
    {m5 m6 : ProbComp α} (hRel : RelProbUpToBad R bad m5 m6)
    (hNotBad : ∀ x5 x6, R x5 x6 → bad x6 = false)
    (fin5 fin6 : α → ProbComp Bool)
    (hfin : ∀ x5 x6, R x5 x6 → 𝒟[fin5 x5] {true} = 𝒟[fin6 x6] {true}) :
    𝒟[m5 >>= fin5] {true} ≤
      𝒟[m6 >>= fin6] {true} + 𝒟[m6 >>= fun x => pure (bad x)] {true} ∧
    𝒟[m6 >>= fin6] {true} ≤
      𝒟[m5 >>= fin5] {true} + 𝒟[m6 >>= fun x => pure (bad x)] {true} := by
  have h5 : 𝒟[m5 >>= fin5] {true} = probExpect m5 (fun x => 𝒟[fin5 x] {true}) := by
    let _ : MeasurableSpace α := ⊤
    have _ : DiscreteMeasurableSpace α := ⟨fun _ => trivial⟩
    unfold probExpect
    rw [evalDist_bind_of_discrete,
        MeasureTheory.Measure.bind_apply MeasurableSet.of_discrete
          Measurable.of_discrete.aemeasurable]
  have h6 : 𝒟[m6 >>= fin6] {true} = probExpect m6 (fun x => 𝒟[fin6 x] {true}) := by
    let _ : MeasurableSpace α := ⊤
    have _ : DiscreteMeasurableSpace α := ⟨fun _ => trivial⟩
    unfold probExpect
    rw [evalDist_bind_of_discrete,
        MeasureTheory.Measure.bind_apply MeasurableSet.of_discrete
          Measurable.of_discrete.aemeasurable]
  have hbad : 𝒟[m6 >>= fun x => pure (bad x)] {true} =
      probExpect m6 (fun x => 𝒟[(pure (bad x) : ProbComp Bool)] {true}) :=
    evalDist_bind_true_eq_probExpect m6 bad
  rw [h5, h6, hbad]
  refine ⟨?_, ?_⟩
  · calc probExpect m5 (fun x => 𝒟[fin5 x] {true})
        ≤ probExpect m6 (fun x => if bad x then 1 else 𝒟[fin6 x] {true}) := by
          refine hRel.1 _ _ (fun x => MeasureTheory.prob_le_one) (fun x hx =>
            by simp [hx]) (fun x5 x6 hR => ?_)
          simp [hNotBad x5 x6 hR, hfin x5 x6 hR]
      _ ≤ probExpect m6 (fun x => 𝒟[fin6 x] {true}) +
          probExpect m6 (fun x => 𝒟[(pure (bad x) : ProbComp Bool)] {true}) := by
          apply probExpect_add_le
          intro x
          cases bad x <;> simp
  · calc probExpect m6 (fun x => 𝒟[fin6 x] {true})
        ≤ probExpect m6 (fun x => if bad x then 0 else 𝒟[fin6 x] {true}) +
          probExpect m6 (fun x => 𝒟[(pure (bad x) : ProbComp Bool)] {true}) := by
          apply probExpect_add_le
          intro x
          cases bad x <;> simp
      _ ≤ probExpect m5 (fun x => 𝒟[fin5 x] {true}) +
          probExpect m6 (fun x => 𝒟[(pure (bad x) : ProbComp Bool)] {true}) := by
          refine add_le_add ?_ le_rfl
          refine hRel.2 _ _ (fun x hx => by simp [hx]) (fun x5 x6 hR => ?_)
          simp [hNotBad x5 x6 hR, hfin x5 x6 hR]

theorem evalDist_simulateQ_eq_uniformBool_of_bad_preserved
    {ι α St : Type} {QSpec : OracleSpec.{0, 0} ι}
    (bad : St → Bool)
    (impl : QueryImpl QSpec (StateT St ProbComp))
    (hPres : ∀ q st, bad st = true → ∀ x ∈ support ((impl q).run st), bad x.2 = true)
    (fin : α × St → ProbComp Bool)
    (hFin : ∀ a st, bad st = true → 𝒟[fin (a, st)] = 𝒟[$ᵗ Bool])
    (oa : OracleComp (unifSpec + QSpec) α) (st : St) (hbad : bad st = true) :
    let full := (QueryImpl.ofLift unifSpec ProbComp).liftTarget (StateT St ProbComp) + impl
    𝒟[(simulateQ full oa).run st >>= fin] = 𝒟[$ᵗ Bool] := by
  intro full
  induction oa using OracleComp.inductionOn generalizing st with
  | pure a =>
    simp only [simulateQ_pure, StateT.run_pure, pure_bind]
    exact hFin a st hbad
  | query_bind q mx ih =>
    rcases q with uq | gq
    · dsimp only [full]
      rw [simulateQ_run_query_inl, bind_assoc]
      calc 𝒟[(liftM (OracleSpec.query (spec := unifSpec) uq) : ProbComp _) >>= fun u =>
            (simulateQ full (mx u)).run st >>= fin]
          = 𝒟[(liftM (OracleSpec.query (spec := unifSpec) uq) : ProbComp _) >>= fun _ =>
            $ᵗ Bool] := by
            refine OracleComp.evalDist_bind_congr_of_support _ _ _ fun u _ => ?_
            exact ih u st hbad
        _ = 𝒟[$ᵗ Bool] := OracleComp.evalDist_bind_const _ _
    · dsimp only [full]
      rw [simulateQ_run_query_inr, bind_assoc]
      calc 𝒟[(impl gq).run st >>= fun x => (simulateQ full (mx x.1)).run x.2 >>= fin]
          = 𝒟[(impl gq).run st >>= fun _ => $ᵗ Bool] := by
            refine OracleComp.evalDist_bind_congr_of_support _ _ _ fun x hx => ?_
            exact ih x.1 x.2 (hPres gq st hbad x hx)
        _ = 𝒟[$ᵗ Bool] := OracleComp.evalDist_bind_const _ _

theorem evalDist_simulateQ_eq_of_step_or_bad
    {ι α St : Type} {QSpec : OracleSpec.{0, 0} ι}
    (bad : St → Bool)
    (impl1 impl2 : QueryImpl QSpec (StateT St ProbComp))
    (hPres1 : ∀ q st, bad st = true → ∀ x ∈ support ((impl1 q).run st), bad x.2 = true)
    (hPres2 : ∀ q st, bad st = true → ∀ x ∈ support ((impl2 q).run st), bad x.2 = true)
    (hStep : ∀ q st, bad st = false →
      ∀ (k1 k2 : QSpec.Range q × St → ProbComp Bool),
        (∀ x, bad x.2 = false → 𝒟[k1 x] = 𝒟[k2 x]) →
        (∀ x, bad x.2 = true → 𝒟[k1 x] = 𝒟[$ᵗ Bool] ∧ 𝒟[k2 x] = 𝒟[$ᵗ Bool]) →
        𝒟[(impl1 q).run st >>= k1] = 𝒟[(impl2 q).run st >>= k2])
    (fin : α × St → ProbComp Bool)
    (hFin : ∀ a st, bad st = true → 𝒟[fin (a, st)] = 𝒟[$ᵗ Bool])
    (oa : OracleComp (unifSpec + QSpec) α) (st : St) :
    let full1 := (QueryImpl.ofLift unifSpec ProbComp).liftTarget (StateT St ProbComp) + impl1
    let full2 := (QueryImpl.ofLift unifSpec ProbComp).liftTarget (StateT St ProbComp) + impl2
    𝒟[(simulateQ full1 oa).run st >>= fin] = 𝒟[(simulateQ full2 oa).run st >>= fin] := by
  intro full1 full2
  induction oa using OracleComp.inductionOn generalizing st with
  | pure a =>
    simp [simulateQ_pure, StateT.run_pure]
  | query_bind q mx ih =>
    by_cases hbad : bad st = true
    · rw [evalDist_simulateQ_eq_uniformBool_of_bad_preserved bad impl1 hPres1 fin hFin _ st hbad,
          evalDist_simulateQ_eq_uniformBool_of_bad_preserved bad impl2 hPres2 fin hFin _ st hbad]
    · have hbadF : bad st = false := Bool.eq_false_iff.mpr hbad
      rcases q with uq | gq
      · dsimp only [full1, full2]
        rw [simulateQ_run_query_inl, simulateQ_run_query_inl, bind_assoc, bind_assoc]
        refine OracleComp.evalDist_bind_congr_of_support _ _ _ fun u _ => ?_
        exact ih u st
      · dsimp only [full1, full2]
        rw [simulateQ_run_query_inr, simulateQ_run_query_inr, bind_assoc, bind_assoc]
        refine hStep gq st hbadF
          (fun x => (simulateQ full1 (mx x.1)).run x.2 >>= fin)
          (fun x => (simulateQ full2 (mx x.1)).run x.2 >>= fin)
          (fun x _ => ih x.1 x.2)
          (fun x hx => ⟨evalDist_simulateQ_eq_uniformBool_of_bad_preserved bad impl1 hPres1 fin hFin
                       (mx x.1) x.2 hx,
                       evalDist_simulateQ_eq_uniformBool_of_bad_preserved bad impl2 hPres2 fin hFin
                         (mx x.1) x.2 hx⟩)

/-- Extended `KeyInd` state recording adversary `.roQuery` inputs in `advRoLog`. -/
structure KeyIndFgCutoffState (S : Setup) where
  base     : KeyIndState S
  advRoLog : List Bytes := []

def KeyIndFgCutoffState.empty (S : Setup) (secb : Bool) : KeyIndFgCutoffState S :=
  { base := KeyIndState.empty S secb, advRoLog := [] }

/-- `KeyInd` oracle implementation evolving `base` identically to `pqxdhKeyIndImpl true S P`
    while recording adversary `.roQuery` inputs in `advRoLog`. -/
def pqxdhKeyIndFgImpl (S : Setup) (P : Primitives) :
    QueryImpl (keyIndSpec S) (StateT (KeyIndFgCutoffState S) ProbComp)
  | .roQuery secrets => StateT.mk (fun hst => do
    let (resp, base') ← (pqxdhKeyIndImpl true S P (.roQuery secrets)).run hst.base
    return (resp, { base := base', advRoLog := secrets :: hst.advRoLog }))
  | q => StateT.mk (fun hst => do
    let (resp, base') ← (pqxdhKeyIndImpl true S P q).run hst.base
    return (resp, { hst with base := base' }))

noncomputable def runKeyIndFgSim (S : Setup) (P : Primitives) (A : KeyIndAdversary S) :
    ProbComp (Bool × Bool × KeyIndFgCutoffState S) := do
  let secb ← $ᵗ Bool
  let initSt := KeyIndFgCutoffState.empty S secb
  let impl := (QueryImpl.ofLift unifSpec ProbComp).liftTarget
      (StateT (KeyIndFgCutoffState S) ProbComp) + pqxdhKeyIndFgImpl S P
  let (b', finalHst) ← (simulateQ impl A.run).run initSt
  return (secb, b', finalHst)

def eraseSpkBundleEntryFg (S : Setup) (bIdx : ℕ) (k : Nat × Nat) (b : SpkBundleEntry) :
    SpkBundleEntry :=
  if spkBundleFlatIdxVal S k == bIdx then { b with spkSk := [] } else b

def eraseSpkBundlesFg (S : Setup) (bIdx : ℕ)
    (spkBundles : List ((Nat × Nat) × SpkBundleEntry)) :
    List ((Nat × Nat) × SpkBundleEntry) :=
  spkBundles.map (fun (k, b) => (k, eraseSpkBundleEntryFg S bIdx k b))

/-- Case A (`DH1 = CDH(ik_U*, spk_V*)`) bad event at `(uIdx, bIdx)`: principal `uIdx` is
    uncorrupted, SPK bundle `bIdx` is unrevealed, and `P.x25519 uEntry.secIKA0 bEntry.spkPk`
    appears in `advRoLog.take maxLen` or a non-target session candidate. -/
def badKeyIndFgDh1At {S : Setup} (P : Primitives) (maxLen uIdx bIdx : ℕ)
    (st : KeyIndState S) (advRoLog : List Bytes) : Bool :=
  match st.principals.find? (fun (u, _) => u == uIdx),
        st.spkBundles.find? (fun (k, _) => spkBundleFlatIdxVal S k == bIdx) with
  | some (_, uEntry), some (_, bEntry) =>
    let zTarget := P.x25519 uEntry.secIKA0 bEntry.spkPk
    let spkErased := eraseSpkBundlesFg S bIdx st.spkBundles
    let advKeyPows := st.advKeys.map (fun (sk, pk) => (sk, P.pow8 pk))
    !uEntry.corrupted && !bEntry.revealed &&
    ((advRoLog.take maxLen).any (fun sec => extractDh1 sec == zTarget) ||
     (st.sessions.take S.N_dh).any (fun s =>
       initDh1Cand S P spkErased advKeyPows s == zTarget) ||
     (st.respSessions.take S.N_sess_tot).any (fun r =>
       respDh1Cand S P spkErased r == zTarget))
  | _, _ => false

/-- Case C (`DH3 = CDH(ek_U*, spk_V*)`) bad event at `(sIdx, bIdx)`: initiator session `sIdx` is
    fresh against SPK bundle `bIdx` and `P.x25519 s.ekASk bEntry.spkPk` is queried in
    `advRoLog.take maxLen`. -/
def badKeyIndFgDh3At {S : Setup} (P : Primitives) (maxLen sIdx bIdx : ℕ)
    (st : KeyIndState S) (advRoLog : List Bytes) : Bool :=
  match st.sessions.find? (fun s => initSessionSlotIdx s.sid == sIdx),
        st.spkBundles.find? (fun (k, _) => spkBundleFlatIdxVal S k == bIdx) with
  | some s, some (_, bEntry) =>
    s.fresh && s.spkHonest && !bEntry.revealed &&
    (P.pow8 s.peerSpkPk == P.pow8 bEntry.spkPk) &&
    (advRoLog.take maxLen).any (fun sec =>
      extractDh3 sec == P.x25519 s.ekASk bEntry.spkPk)
  | _, _ => false

/-- Disjunction of `badKeyIndFgDh1At` and `badKeyIndFgDh3At` over all slot indices. -/
def badKeyIndFgAny {S : Setup} (P : Primitives) (maxLen : ℕ)
    (st : KeyIndState S) (advRoLog : List Bytes) : Bool :=
  ((List.range S.N_id).any (fun uIdx =>
    (List.range S.N_spk_tot).any (fun bIdx =>
      badKeyIndFgDh1At P maxLen uIdx bIdx st advRoLog))) ||
  ((List.range S.N_send_tot).any (fun sIdx =>
    (List.range S.N_spk_tot).any (fun bIdx =>
      badKeyIndFgDh3At P maxLen sIdx bIdx st advRoLog)))

theorem prob_or_le_add_fg {α : Type} (mx : ProbComp α) (P1 P2 : α → Bool) :
    (𝒟[mx >>= fun x => pure (P1 x || P2 x)] {true}).toReal ≤
      (𝒟[mx >>= fun x => pure (P1 x)] {true}).toReal +
      (𝒟[mx >>= fun x => pure (P2 x)] {true}).toReal := by
  have hle : 𝒟[mx >>= fun x => pure (P1 x || P2 x)] {true} ≤
      𝒟[mx >>= fun x => pure (P1 x)] {true} + 𝒟[mx >>= fun x => pure (P2 x)] {true} := by
    rw [evalDist_bind_true_eq_probExpect, evalDist_bind_true_eq_probExpect,
        evalDist_bind_true_eq_probExpect]
    apply probExpect_add_le
    intro x
    cases P1 x <;> cases P2 x <;> simp
  have h1 : 𝒟[mx >>= fun x => pure (P1 x)] {true} ≠ ⊤ := MeasureTheory.measure_ne_top _ _
  have h2 : 𝒟[mx >>= fun x => pure (P2 x)] {true} ≠ ⊤ := MeasureTheory.measure_ne_top _ _
  rw [← ENNReal.toReal_add h1 h2]
  exact ENNReal.toReal_mono (ENNReal.add_ne_top.mpr ⟨h1, h2⟩) hle

theorem prob_badKeyIndFgAny_le_sum {S : Setup} (P : Primitives) (maxLen : ℕ)
    {α : Type} (mx : ProbComp α) (projSt : α → KeyIndState S) (projLog : α → List Bytes) :
    (𝒟[mx >>= fun x => pure (badKeyIndFgAny P maxLen (projSt x) (projLog x))] {true}).toReal ≤
      (∑ uIdx ∈ Finset.range S.N_id, ∑ bIdx ∈ Finset.range S.N_spk_tot,
        (𝒟[mx >>= fun x =>
          pure (badKeyIndFgDh1At P maxLen uIdx bIdx (projSt x) (projLog x))] {true}).toReal) +
      (∑ sIdx ∈ Finset.range S.N_send_tot, ∑ bIdx ∈ Finset.range S.N_spk_tot,
        (𝒟[mx >>= fun x =>
          pure (badKeyIndFgDh3At P maxLen sIdx bIdx (projSt x) (projLog x))] {true}).toReal) := by
  unfold badKeyIndFgAny
  have hOr := prob_or_le_add_fg mx
    (fun x => (List.range S.N_id).any (fun uIdx =>
      (List.range S.N_spk_tot).any (fun bIdx =>
        badKeyIndFgDh1At P maxLen uIdx bIdx (projSt x) (projLog x))))
    (fun x => (List.range S.N_send_tot).any (fun sIdx =>
      (List.range S.N_spk_tot).any (fun bIdx =>
        badKeyIndFgDh3At P maxLen sIdx bIdx (projSt x) (projLog x))))
  have hDh1 := toReal_any_double_range_le_sum2 mx S.N_id S.N_spk_tot
    (fun uIdx bIdx x => badKeyIndFgDh1At P maxLen uIdx bIdx (projSt x) (projLog x))
  have hDh3 := toReal_any_double_range_le_sum2 mx S.N_send_tot S.N_spk_tot
    (fun sIdx bIdx x => badKeyIndFgDh3At P maxLen sIdx bIdx (projSt x) (projLog x))
  linarith


/-! ## Algebraic `x25519` and `ddhEqPure` lemmas -/

theorem x25519_eq_iff_pow8_eq (P : Primitives) (hP : CryptoWellFormedPrimitivesδ P)
    (a pk1 pk2 : Bytes) (ha : a.length = 32) (hpk1 : pk1.length = 32) (hpk2 : pk2.length = 32) :
    P.x25519 a pk1 = P.x25519 a pk2 ↔ P.pow8 pk1 = P.pow8 pk2 :=
  ⟨hP.x25519_inj_pow8 a pk1 pk2 ha hpk1 hpk2, hP.x25519_pow8_congr a pk1 pk2 hpk1 hpk2⟩

theorem ddhEqPure_pair_pair_same_right_iff (P : Primitives) (hP : CryptoWellFormedPrimitivesδ P)
    (v pk1 pk2 pk3 pk4 : Bytes) (hv : v.length = 32)
    (hpk1 : pk1.length = 32) (hpk3 : pk3.length = 32)
    (h2 : P.pow8 pk2 = P.pow8 (P.x25519Base v))
    (h4 : P.pow8 pk4 = P.pow8 (P.x25519Base v)) :
    ddhEqPure P.isValidDhTriple (mkPairPosPure P pk1 pk2) (mkPairPosPure P pk3 pk4) =
      (P.x25519 v pk1 == P.x25519 v pk3) := by
  unfold ddhEqPure mkPairPosPure
  rw [h2, h4]
  apply Bool.eq_iff_iff.mpr
  rw [Bool.or_eq_true, Bool.and_eq_true, Bool.and_eq_true, beq_iff_eq, beq_iff_eq,
      beq_iff_eq, beq_iff_eq, beq_iff_eq, x25519_eq_iff_pow8_eq P hP v pk1 pk3 hv hpk1 hpk3]
  constructor
  · rintro (⟨h13, _⟩ | ⟨h1v, hv3⟩)
    · exact h13
    · exact h1v.trans hv3
  · intro h13
    exact Or.inl ⟨h13, rfl⟩

theorem ddhEqPure_pair_pair_same_left_iff (P : Primitives) (hP : CryptoWellFormedPrimitivesδ P)
    (u pk1 pk2 pk3 pk4 : Bytes) (hu : u.length = 32)
    (hpk2 : pk2.length = 32) (hpk4 : pk4.length = 32)
    (h1 : P.pow8 pk1 = P.pow8 (P.x25519Base u))
    (h3 : P.pow8 pk3 = P.pow8 (P.x25519Base u)) :
    ddhEqPure P.isValidDhTriple (mkPairPosPure P pk1 pk2) (mkPairPosPure P pk3 pk4) =
      (P.x25519 u pk2 == P.x25519 u pk4) := by
  unfold ddhEqPure mkPairPosPure
  rw [h1, h3]
  apply Bool.eq_iff_iff.mpr
  rw [Bool.or_eq_true, Bool.and_eq_true, Bool.and_eq_true, beq_iff_eq, beq_iff_eq,
      beq_iff_eq, beq_iff_eq, beq_iff_eq, x25519_eq_iff_pow8_eq P hP u pk2 pk4 hu hpk2 hpk4]
  constructor
  · rintro (⟨_, h24⟩ | ⟨hu4, h2u⟩)
    · exact h24
    · exact h2u.trans hu4
  · intro h24
    exact Or.inl ⟨rfl, h24⟩

/-! ## Single-slot pre-sampling -/

theorem evalDist_simulateQ_preSample_slot_eq_of_hasFired
    {ι α κ St : Type} {QSpec : OracleSpec.{0, 0} ι}
    (hasFired : St → Prop)
    (implLazy : QueryImpl QSpec (StateT St ProbComp))
    (implPre : κ → QueryImpl QSpec (StateT St ProbComp))
    (hAfter : ∀ (q : ι) (st : St), hasFired st →
      (∀ k, (implPre k q).run st = (implLazy q).run st) ∧
      (∀ x ∈ support ((implLazy q).run st), hasFired x.2))
    (oa : OracleComp (unifSpec + QSpec) α) (st : St)
    (hFired : hasFired st) (k : κ)
    (obs : α × St → ProbComp Bool) :
    let fullPre := (QueryImpl.ofLift unifSpec ProbComp).liftTarget (StateT St ProbComp) + implPre k
    let fullLazy := (QueryImpl.ofLift unifSpec ProbComp).liftTarget (StateT St ProbComp) + implLazy
    𝒟[(simulateQ fullPre oa).run st >>= obs] = 𝒟[(simulateQ fullLazy oa).run st >>= obs] := by
  intro fullPre fullLazy
  induction oa using OracleComp.inductionOn generalizing st with
  | pure a => rfl
  | query_bind q oa ih =>
    cases q with
    | inl uq =>
      dsimp only [fullPre, fullLazy]
      rw [simulateQ_run_query_inl, simulateQ_run_query_inl, bind_assoc, bind_assoc]
      refine OracleComp.evalDist_bind_congr_of_support _ _ _ (fun u _ => ?_)
      exact ih u st hFired
    | inr gq =>
      dsimp only [fullPre, fullLazy]
      rw [simulateQ_run_query_inr, simulateQ_run_query_inr, bind_assoc, bind_assoc]
      rw [(hAfter gq st hFired).1 k]
      refine OracleComp.evalDist_bind_congr_of_support ((implLazy gq).run st) _ _ (fun x hx => ?_)
      exact ih x.1 x.2 ((hAfter gq st hFired).2 x hx)

theorem evalDist_simulateQ_preSample_slot_eq
    {ι α κ St : Type} {QSpec : OracleSpec.{0, 0} ι}
    (samp : ProbComp κ)
    (hasFired : St → Prop)
    (implLazy : QueryImpl QSpec (StateT St ProbComp))
    (implPre : κ → QueryImpl QSpec (StateT St ProbComp))
    (hAfter : ∀ (q : ι) (st : St), hasFired st →
      (∀ k, (implPre k q).run st = (implLazy q).run st) ∧
      (∀ x ∈ support ((implLazy q).run st), hasFired x.2))
    (hBefore : ∀ (q : ι) (st : St), ¬ hasFired st →
      (∀ k, (implPre k q).run st = (implLazy q).run st) ∨
      ((∀ obs : QSpec.Range q × St → ProbComp Bool,
        𝒟[samp >>= fun k => (implPre k q).run st >>= obs] =
        𝒟[(implLazy q).run st >>= obs]) ∧
       (∀ k, ∀ x ∈ support ((implPre k q).run st), hasFired x.2)))
    (oa : OracleComp (unifSpec + QSpec) α) (st : St)
    (obs : α × St → ProbComp Bool) :
    let fullPre (k : κ) := (QueryImpl.ofLift unifSpec ProbComp).liftTarget (StateT St ProbComp) +
      implPre k
    let fullLazy := (QueryImpl.ofLift unifSpec ProbComp).liftTarget (StateT St ProbComp) + implLazy
    𝒟[samp >>= fun k => (simulateQ (fullPre k) oa).run st >>= obs] =
    𝒟[(simulateQ fullLazy oa).run st >>= obs] := by
  intro fullPre fullLazy
  induction oa using OracleComp.inductionOn generalizing st with
  | pure a =>
    simp only [simulateQ_pure, StateT.run_pure, OracleComp.evalDist_bind_const]
  | query_bind q oa ih =>
    by_cases hFired : hasFired st
    · calc 𝒟[samp >>= fun k =>
            (simulateQ (fullPre k) (liftM (OracleSpec.query q) >>= oa)).run st >>= obs]
          = 𝒟[samp >>= fun _ =>
              (simulateQ fullLazy (liftM (OracleSpec.query q) >>= oa)).run st >>= obs] := by
            refine OracleComp.evalDist_bind_congr_of_support _ _ _ (fun k _ => ?_)
            exact evalDist_simulateQ_preSample_slot_eq_of_hasFired hasFired implLazy implPre hAfter
              _ st hFired k obs
        _ = 𝒟[(simulateQ fullLazy (liftM (OracleSpec.query q) >>= oa)).run st >>= obs] :=
            OracleComp.evalDist_bind_const _ _
    · cases q with
      | inl uq =>
        dsimp only [fullPre, fullLazy]
        simp_rw [simulateQ_run_query_inl, bind_assoc]
        rw [OracleComp.evalDist_bind_bind_swap]
        refine OracleComp.evalDist_bind_congr_of_support _ _ _ (fun u _ => ?_)
        exact ih u st
      | inr gq =>
        dsimp only [fullPre, fullLazy]
        simp_rw [simulateQ_run_query_inr, bind_assoc]
        rcases hBefore gq st hFired with hLeft | ⟨hDist, hSupp⟩
        · calc 𝒟[samp >>= fun k =>
                (implPre k gq).run st >>= fun x =>
                (simulateQ (fullPre k) (oa x.1)).run x.2 >>= obs]
              = 𝒟[samp >>= fun k =>
                  (implLazy gq).run st >>= fun x =>
                  (simulateQ (fullPre k) (oa x.1)).run x.2 >>= obs] := by
                refine OracleComp.evalDist_bind_congr_of_support _ _ _ (fun k _ => ?_)
                rw [hLeft k]
            _ = 𝒟[(implLazy gq).run st >>= fun x =>
                  (simulateQ fullLazy (oa x.1)).run x.2 >>= obs] := by
                rw [OracleComp.evalDist_bind_bind_swap]
                refine OracleComp.evalDist_bind_congr_of_support ((implLazy gq).run st) _ _ (fun x _
                  => ?_)
                exact ih x.1 x.2
        · calc 𝒟[samp >>= fun k =>
                (implPre k gq).run st >>= fun x =>
                (simulateQ (fullPre k) (oa x.1)).run x.2 >>= obs]
              = 𝒟[samp >>= fun k =>
                  (implPre k gq).run st >>= fun x =>
                  (simulateQ fullLazy (oa x.1)).run x.2 >>= obs] := by
                refine OracleComp.evalDist_bind_congr_of_support _ _ _ (fun k _ => ?_)
                refine OracleComp.evalDist_bind_congr_of_support _ _ _ (fun x hx => ?_)
                exact evalDist_simulateQ_preSample_slot_eq_of_hasFired hasFired implLazy implPre
                  hAfter
                  (oa x.1) x.2 (hSupp k x hx) k obs
            _ = 𝒟[(implLazy gq).run st >>= fun x =>
                  (simulateQ fullLazy (oa x.1)).run x.2 >>= obs] :=
                hDist (fun x => (simulateQ fullLazy (oa x.1)).run x.2 >>= obs)

theorem evalDist_simulateQ_preSample_slot_eq_c0
    {ι α κ α0 St : Type} {QSpec : OracleSpec.{0, 0} ι}
    (samp : ProbComp κ)
    (c0 : ProbComp α0)
    (hasFired : St → Prop)
    (implLazy : QueryImpl QSpec (StateT St ProbComp))
    (implPre : κ → QueryImpl QSpec (StateT St ProbComp))
    (hAfter : ∀ (q : ι) (st : St), hasFired st →
      (∀ k, (implPre k q).run st = (implLazy q).run st) ∧
      (∀ x ∈ support ((implLazy q).run st), hasFired x.2))
    (hBefore : ∀ (q : ι) (st : St), ¬ hasFired st →
      (∀ k, (implPre k q).run st = (implLazy q).run st) ∨
      ∃ (fPre : κ → α0 → ProbComp (QSpec.Range q × St)),
        (∀ k, (implPre k q).run st = (c0 >>= fPre k)) ∧
        (∀ obs : QSpec.Range q × St → ProbComp Bool,
          𝒟[(implLazy q).run st >>= obs] =
          𝒟[c0 >>= fun a0 => samp >>= fun k => fPre k a0 >>= obs]) ∧
        (∀ a0, (∃ x0, ∀ k, fPre k a0 = pure x0) ∨
               (∀ k, ∀ x ∈ support (fPre k a0), hasFired x.2)))
    (oa : OracleComp (unifSpec + QSpec) α) (st : St)
    (obs : α × St → ProbComp Bool) :
    let fullPre (k : κ) := (QueryImpl.ofLift unifSpec ProbComp).liftTarget (StateT St ProbComp) +
      implPre k
    let fullLazy := (QueryImpl.ofLift unifSpec ProbComp).liftTarget (StateT St ProbComp) + implLazy
    𝒟[samp >>= fun k => (simulateQ (fullPre k) oa).run st >>= obs] =
    𝒟[(simulateQ fullLazy oa).run st >>= obs] := by
  intro fullPre fullLazy
  induction oa using OracleComp.inductionOn generalizing st with
  | pure a =>
    simp only [simulateQ_pure, StateT.run_pure, OracleComp.evalDist_bind_const]
  | query_bind q oa ih =>
    by_cases hFired : hasFired st
    · calc 𝒟[samp >>= fun k =>
            (simulateQ (fullPre k) (liftM (OracleSpec.query q) >>= oa)).run st >>= obs]
          = 𝒟[samp >>= fun _ =>
              (simulateQ fullLazy (liftM (OracleSpec.query q) >>= oa)).run st >>= obs] := by
            refine OracleComp.evalDist_bind_congr_of_support _ _ _ (fun k _ => ?_)
            exact evalDist_simulateQ_preSample_slot_eq_of_hasFired hasFired implLazy implPre hAfter
              _ st hFired k obs
        _ = 𝒟[(simulateQ fullLazy (liftM (OracleSpec.query q) >>= oa)).run st >>= obs] :=
            OracleComp.evalDist_bind_const _ _
    · cases q with
      | inl uq =>
        dsimp only [fullPre, fullLazy]
        simp_rw [simulateQ_run_query_inl, bind_assoc]
        rw [OracleComp.evalDist_bind_bind_swap]
        refine OracleComp.evalDist_bind_congr_of_support _ _ _ (fun u _ => ?_)
        exact ih u st
      | inr gq =>
        dsimp only [fullPre, fullLazy]
        simp_rw [simulateQ_run_query_inr, bind_assoc]
        rcases hBefore gq st hFired with hLeft | ⟨fPre, hPreEq, hLazyDist, hCases⟩
        · calc 𝒟[samp >>= fun k =>
                (implPre k gq).run st >>= fun x =>
                (simulateQ (fullPre k) (oa x.1)).run x.2 >>= obs]
              = 𝒟[samp >>= fun k =>
                  (implLazy gq).run st >>= fun x =>
                  (simulateQ (fullPre k) (oa x.1)).run x.2 >>= obs] := by
                refine OracleComp.evalDist_bind_congr_of_support _ _ _ (fun k _ => ?_)
                rw [hLeft k]
            _ = 𝒟[(implLazy gq).run st >>= fun x =>
                  (simulateQ fullLazy (oa x.1)).run x.2 >>= obs] := by
                rw [OracleComp.evalDist_bind_bind_swap]
                refine OracleComp.evalDist_bind_congr_of_support ((implLazy gq).run st) _ _ (fun x _
                  => ?_)
                exact ih x.1 x.2
        · calc 𝒟[samp >>= fun k =>
                (implPre k gq).run st >>= fun x =>
                (simulateQ (fullPre k) (oa x.1)).run x.2 >>= obs]
              = 𝒟[samp >>= fun k =>
                  c0 >>= fun a0 =>
                  fPre k a0 >>= fun x =>
                  (simulateQ (fullPre k) (oa x.1)).run x.2 >>= obs] := by
                refine OracleComp.evalDist_bind_congr_of_support _ _ _ (fun k _ => ?_)
                rw [hPreEq k, bind_assoc]
            _ = 𝒟[c0 >>= fun a0 =>
                  samp >>= fun k =>
                  fPre k a0 >>= fun x =>
                  (simulateQ (fullPre k) (oa x.1)).run x.2 >>= obs] :=
                OracleComp.evalDist_bind_bind_swap samp c0 _
            _ = 𝒟[c0 >>= fun a0 =>
                  samp >>= fun k =>
                  fPre k a0 >>= fun x =>
                  (simulateQ fullLazy (oa x.1)).run x.2 >>= obs] := by
                refine OracleComp.evalDist_bind_congr_of_support c0 _ _ (fun a0 _ => ?_)
                rcases hCases a0 with ⟨x0, hx0⟩ | hFireA0
                · calc 𝒟[samp >>= fun k =>
                          fPre k a0 >>= fun x =>
                          (simulateQ (fullPre k) (oa x.1)).run x.2 >>= obs]
                      = 𝒟[samp >>= fun k =>
                          (simulateQ (fullPre k) (oa x0.1)).run x0.2 >>= obs] := by
                        refine OracleComp.evalDist_bind_congr_of_support _ _ _ (fun k _ => ?_)
                        rw [hx0 k, pure_bind]
                    _ = 𝒟[(simulateQ fullLazy (oa x0.1)).run x0.2 >>= obs] :=
                        ih x0.1 x0.2
                    _ = 𝒟[samp >>= fun _ =>
                          (simulateQ fullLazy (oa x0.1)).run x0.2 >>= obs] :=
                        (OracleComp.evalDist_bind_const _ _).symm
                    _ = 𝒟[samp >>= fun k =>
                          fPre k a0 >>= fun x =>
                          (simulateQ fullLazy (oa x.1)).run x.2 >>= obs] := by
                        refine OracleComp.evalDist_bind_congr_of_support _ _ _ (fun k _ => ?_)
                        rw [hx0 k, pure_bind]
                · refine OracleComp.evalDist_bind_congr_of_support _ _ _ (fun k _ => ?_)
                  refine OracleComp.evalDist_bind_congr_of_support _ _ _ (fun x hx => ?_)
                  exact evalDist_simulateQ_preSample_slot_eq_of_hasFired hasFired implLazy implPre
                    hAfter
                    (oa x.1) x.2 (hFireA0 k x hx) k obs
            _ = 𝒟[(implLazy gq).run st >>= fun x =>
                  (simulateQ fullLazy (oa x.1)).run x.2 >>= obs] :=
                (hLazyDist (fun x => (simulateQ fullLazy (oa x.1)).run x.2 >>= obs)).symm

/-! ## Pre-sampled `pqxdhKeyIndFgPreImpl` -/

theorem initSessionSlotIdx_sendOPK_lt {S : Setup} (u : Fin S.N_id) (i : Fin S.N_send_opk) :
    initSessionSlotIdx (.sendOPK u i) < S.N_send_opk_tot := by
  simp only [initSessionSlotIdx, Setup.N_send_opk_tot]
  have hu : u.val + 1 ≤ S.N_id := u.isLt
  have hi : i.val < S.N_send_opk := i.isLt
  calc u.val * S.N_send_opk + i.val
      < u.val * S.N_send_opk + S.N_send_opk := Nat.add_lt_add_left hi _
    _ = (u.val + 1) * S.N_send_opk := by ring
    _ ≤ S.N_id * S.N_send_opk := Nat.mul_le_mul_right S.N_send_opk hu

theorem initSessionSlotIdx_sendNoOPK_lt {S : Setup} (u : Fin S.N_id) (i : Fin S.N_send_no_opk) :
    initSessionSlotIdx (.sendNoOPK u i) < S.N_send_tot := by
  simp only [initSessionSlotIdx, Setup.N_send_tot, Setup.N_send_no_opk_tot]
  have hu : u.val + 1 ≤ S.N_id := u.isLt
  have hi : i.val < S.N_send_no_opk := i.isLt
  have hlt : u.val * S.N_send_no_opk + i.val < S.N_id * S.N_send_no_opk := by
    calc u.val * S.N_send_no_opk + i.val
        < u.val * S.N_send_no_opk + S.N_send_no_opk := Nat.add_lt_add_left hi _
      _ = (u.val + 1) * S.N_send_no_opk := by ring
      _ ≤ S.N_id * S.N_send_no_opk := Nat.mul_le_mul_right S.N_send_no_opk hu
  omega

theorem initSessionSlotIdx_inj_of_lt {S : Setup} {sid1 sid2 : SessionId S}
    (h : initSessionSlotIdx sid1 = initSessionSlotIdx sid2)
    (hlt : initSessionSlotIdx sid2 < S.N_send_tot) : sid1 = sid2 := by
  cases sid1 with
  | sendOPK u1 i1 =>
    cases sid2 with
    | sendOPK u2 i2 =>
      simp only [initSessionSlotIdx] at h
      have hi1 : i1.val < S.N_send_opk := i1.isLt
      have hi2 : i2.val < S.N_send_opk := i2.isLt
      have hu : u1.val = u2.val := by
        have h1 : (u1.val * S.N_send_opk + i1.val) / S.N_send_opk = u1.val := by
          rw [Nat.mul_comm, Nat.mul_add_div (Nat.zero_lt_of_lt hi1), Nat.div_eq_of_lt hi1,
            Nat.add_zero]
        have h2 : (u2.val * S.N_send_opk + i2.val) / S.N_send_opk = u2.val := by
          rw [Nat.mul_comm, Nat.mul_add_div (Nat.zero_lt_of_lt hi2), Nat.div_eq_of_lt hi2,
            Nat.add_zero]
        rw [← h1, ← h2, h]
      have hi : i1.val = i2.val := by rw [hu] at h; omega
      rw [Fin.ext hu, Fin.ext hi]
    | sendNoOPK u2 i2 =>
      have h1 := initSessionSlotIdx_sendOPK_lt u1 i1
      simp only [initSessionSlotIdx] at h h1
      omega
    | recvOPK _ _ _ => simp only [initSessionSlotIdx] at hlt; omega
    | recvNoOPK _ _ _ => simp only [initSessionSlotIdx] at hlt; omega
  | sendNoOPK u1 i1 =>
    cases sid2 with
    | sendOPK u2 i2 =>
      have h2 := initSessionSlotIdx_sendOPK_lt u2 i2
      simp only [initSessionSlotIdx] at h h2
      omega
    | sendNoOPK u2 i2 =>
      simp only [initSessionSlotIdx] at h
      have h' : u1.val * S.N_send_no_opk + i1.val = u2.val * S.N_send_no_opk + i2.val := by omega
      have hi1 : i1.val < S.N_send_no_opk := i1.isLt
      have hi2 : i2.val < S.N_send_no_opk := i2.isLt
      have hu : u1.val = u2.val := by
        have h1 : (u1.val * S.N_send_no_opk + i1.val) / S.N_send_no_opk = u1.val := by
          rw [Nat.mul_comm, Nat.mul_add_div (Nat.zero_lt_of_lt hi1), Nat.div_eq_of_lt hi1,
            Nat.add_zero]
        have h2 : (u2.val * S.N_send_no_opk + i2.val) / S.N_send_no_opk = u2.val := by
          rw [Nat.mul_comm, Nat.mul_add_div (Nat.zero_lt_of_lt hi2), Nat.div_eq_of_lt hi2,
            Nat.add_zero]
        rw [← h1, ← h2, h']
      have hi : i1.val = i2.val := by rw [hu] at h'; omega
      rw [Fin.ext hu, Fin.ext hi]
    | recvOPK _ _ _ => simp only [initSessionSlotIdx] at hlt; omega
    | recvNoOPK _ _ _ => simp only [initSessionSlotIdx] at hlt; omega
  | recvOPK _ _ _ => simp only [initSessionSlotIdx] at h hlt; omega
  | recvNoOPK _ _ _ => simp only [initSessionSlotIdx] at h hlt; omega

theorem spkBundleFlatIdx_inj (S : Setup) (u1 u2 : Fin S.N_id) (j1 j2 : Fin S.N_recv)
    (heq : spkBundleFlatIdx S u1 j1 = spkBundleFlatIdx S u2 j2) :
    u1 = u2 ∧ j1 = j2 := by
  unfold spkBundleFlatIdx at heq
  have hj1 : j1.val < S.N_recv := j1.isLt
  have hj2 : j2.val < S.N_recv := j2.isLt
  have hpos : 0 < S.N_recv := by omega
  have hu : u1.val = u2.val := by
    have h1 : (u1.val * S.N_recv + j1.val) / S.N_recv = u1.val := by
      rw [Nat.mul_comm, Nat.mul_add_div hpos, Nat.div_eq_of_lt hj1, Nat.add_zero]
    have h2 : (u2.val * S.N_recv + j2.val) / S.N_recv = u2.val := by
      rw [Nat.mul_comm, Nat.mul_add_div hpos, Nat.div_eq_of_lt hj2, Nat.add_zero]
    calc u1.val
        = (u1.val * S.N_recv + j1.val) / S.N_recv := h1.symm
      _ = (u2.val * S.N_recv + j2.val) / S.N_recv := by rw [heq]
      _ = u2.val := h2
  have hj : j1.val = j2.val := by
    rw [hu] at heq
    exact Nat.add_left_cancel heq
  exact ⟨Fin.ext hu, Fin.ext hj⟩

def hasFiredSpk (S : Setup) (bIdx : ℕ) (hst : KeyIndFgCutoffState S) : Prop :=
  ∃ (u₀ : Fin S.N_id) (j₀ : Fin S.N_recv),
    spkBundleFlatIdx S u₀ j₀ = bIdx ∧
    hst.base.spkBundles.any (fun (k, _) => k == (u₀.val, j₀.val)) = true

theorem spkBundles_any_of_hasFiredSpk (S : Setup) (bIdx : ℕ) (hst : KeyIndFgCutoffState S)
    (hFired : hasFiredSpk S bIdx hst) (u : Fin S.N_id) (j : Fin S.N_recv)
    (hb : (spkBundleFlatIdx S u j == bIdx) = true) :
    hst.base.spkBundles.any (fun (k, _) => k == (u.val, j.val)) = true := by
  rcases hFired with ⟨u₀, j₀, hidx₀, hany₀⟩
  have heq : spkBundleFlatIdx S u j = spkBundleFlatIdx S u₀ j₀ :=
    (beq_iff_eq.mp hb).trans hidx₀.symm
  rcases spkBundleFlatIdx_inj S u u₀ j j₀ heq with ⟨rfl, rfl⟩
  exact hany₀

def hasFiredPrin (S : Setup) (uIdx : ℕ) (hst : KeyIndFgCutoffState S) : Prop :=
  hst.base.principals.any (fun (idx, _) => idx == uIdx) = true

def hasFiredSess (S : Setup) (sIdx : ℕ) (hst : KeyIndFgCutoffState S) : Prop :=
  hst.base.sessions.any (fun e => initSessionSlotIdx e.sid == sIdx) = true

theorem sessions_any_of_hasFiredSess {S : Setup} (sIdx : ℕ) (hst : KeyIndFgCutoffState S)
    (hFired : hasFiredSess S sIdx hst) (sid : SessionId S)
    (hs : (initSessionSlotIdx sid == sIdx) = true)
    (hlt : initSessionSlotIdx sid < S.N_send_tot) :
    hst.base.sessions.any (fun e => e.sid == sid) = true := by
  unfold hasFiredSess at hFired
  rw [List.any_eq_true] at hFired ⊢
  rcases hFired with ⟨e, he, hidx⟩
  have heq : e.sid = sid :=
    initSessionSlotIdx_inj_of_lt ((beq_iff_eq.mp hidx).trans (beq_iff_eq.mp hs).symm) hlt
  exact ⟨e, he, beq_iff_eq.mpr heq⟩

@[simp]
theorem StateT_run_mk {σ : Type} {m : Type → Type} {α : Type} (f : σ → m (α × σ)) (s : σ) :
    (StateT.mk f).run s = f s := rfl

def liftFgBase {S : Setup} (m : StateT (KeyIndState S) ProbComp KeyIndResponse) :
    StateT (KeyIndFgCutoffState S) ProbComp KeyIndResponse :=
  StateT.mk (fun hst => do
    let (resp, base') ← m.run hst.base
    return (resp, { hst with base := base' }))

noncomputable def fgPreInitPrin (useDh1 : Bool) (targetIdx : ℕ) (optUsk : Option Bytes)
    (S : Setup) (P : Primitives) (u : Fin S.N_id) :
    StateT (KeyIndState S) ProbComp KeyIndResponse := do
  let st ← get
  if st.principals.any (fun (idx, _) => idx == u.val) then
    return .noneResp
  let secIKA0 ← liftM (match optUsk with
    | some uSk => if useDh1 && (u.val == targetIdx) then pure uSk else sampleScalar32
    | none => sampleScalar32)
  let ikAPk := P.x25519Base secIKA0
  let secIKAsign ← liftM sampleScalar32
  let ikSignPk := P.sigPkGen secIKAsign
  let entry : PrincipalEntry := {
    secIKA0    := secIKA0
    ikAPk      := ikAPk
    secIKAsign := secIKAsign
    ikSignPk   := ikSignPk
    corrupted  := false
  }
  set { st with principals := (u.val, entry) :: st.principals }
  return .initPrinResp ikAPk ikSignPk

noncomputable def fgPreGenSPK (targetSpkIdx : ℕ) (optVsk : Option Bytes)
    (S : Setup) (P : Primitives) (u : Fin S.N_id) (j : Fin S.N_recv) :
    StateT (KeyIndState S) ProbComp KeyIndResponse := do
  let st ← get
  if st.spkBundles.any (fun (k, _) => k == (u.val, j.val)) then
    return .noneResp
  let some (_, uEntry) := st.principals.find? (fun (idx, _) => idx == u.val)
    | return .noneResp
  let spkSk ← liftM (match optVsk with
    | some vSk => if spkBundleFlatIdx S u j == targetSpkIdx then pure vSk else sampleScalar32
    | none => sampleScalar32)
  let spkPk := P.x25519Base spkSk
  let rSpk ← liftM sampleRandom64
  let spkSig := P.sigSign uEntry.secIKAsign (encodeEC spkPk) rSpk
  let (pqspkPk, pqspkSk) ← liftM (sampleKemKeyGen P)
  let rPq ← liftM sampleRandom64
  let pqspkSig := P.sigSign uEntry.secIKAsign (encodeKEM pqspkPk) rPq
  let bEntry : SpkBundleEntry := {
    spkSk    := spkSk
    spkPk    := spkPk
    spkSig   := spkSig
    pqspkSk  := pqspkSk
    pqspkPk  := pqspkPk
    pqspkSig := pqspkSig
  }
  set { st with spkBundles := ((u.val, j.val), bEntry) :: st.spkBundles }
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
  return .bundleResp bundleOut

def chooseInitPartnerDrKeyRand {S : Setup} (P : Primitives)
    (respSessions : List (KeyIndRespEntry S)) (s : KeyIndInitiatorEntry S) : ProbComp DRKey :=
  match keyIndPartnerRandKey? P respSessions s with
  | some k => pure k
  | none   => sampleDRKey96

theorem liftM_chooseInitPartnerDrKeyRand_bind {S : Setup} (P : Primitives)
    (respSessions : List (KeyIndRespEntry S)) (s : KeyIndInitiatorEntry S)
    {α : Type} (k : DRKey → StateT (KeyIndState S) ProbComp α) :
    (liftM (chooseInitPartnerDrKeyRand P respSessions s) >>= k) =
      (match keyIndPartnerRandKey? P respSessions s with
       | some rk => pure rk >>= k
       | none    => liftM sampleDRKey96 >>= k) := by
  unfold chooseInitPartnerDrKeyRand
  cases keyIndPartnerRandKey? P respSessions s <;> rfl

noncomputable def fgPreInitiate (useDh1 : Bool) (targetIdx : ℕ) (optUsk : Option Bytes)
    (S : Setup) (P : Primitives) (sid : SessionId S) (u : Fin S.N_id) (bundle : PreKeyBundleInput) :
    StateT (KeyIndState S) ProbComp KeyIndResponse := do
  let st ← get
  if st.sessions.any (fun e => e.sid == sid) then
    return .noneResp
  let some (_, uEntry) := st.principals.find? (fun (idx, _) => idx == u.val)
    | return .noneResp
  if !koskBundleOk P st.principals st.spkBundles st.opkEntries st.advKeys bundle then
    return .noneResp
  let ekASk ← liftM (match optUsk with
    | some uSk =>
      if !useDh1 && (initSessionSlotIdx sid == targetIdx) then pure uSk else sampleScalar32
    | none => sampleScalar32)
  let kemCoins ← liftM sampleCoins32
  let sigPkB := resolveSigPk P st.principals bundle.ikB
  if !(P.sigVerify sigPkB (encodeEC bundle.spkB) bundle.spkSig &&
       P.sigVerify sigPkB (encodeKEM bundle.pqspkB) bundle.pqspkSig) then
    return .noneResp
  let some (ss, kemCt) := P.kemEncaps bundle.pqspkB kemCoins
    | return .noneResp
  let ekAPk := P.x25519Base ekASk
  let dh1 := P.x25519 uEntry.secIKA0 bundle.spkB
  let dh2 := P.x25519 ekASk bundle.ikB
  let dh3 := P.x25519 ekASk bundle.spkB
  let dh4? := bundle.opkB?.map (fun (_, opkPk) => P.x25519 ekASk opkPk)
  let secrets := buildSecrets dh1 dh2 dh3 dh4? ss
  let (drKeyReal, roCache') ← liftM (evalHkdfOrRo true P st.roCache secrets)
  let hdr : HandshakeHdr := {
    ikAPk   := uEntry.ikAPk
    ekAPk   := ekAPk
    spkId   := bundle.spkId
    opkId?  := bundle.opkB?.map Prod.fst
    pqspkId := bundle.pqspkId
    kemCt   := kemCt
  }
  let honestPeer := isHonestUncorruptedPeer P st.principals bundle.ikB
  let (spkHon, opkHon, pqspkHon) :=
    checkBundleProvenance P st.principals st.spkBundles st.opkEntries bundle
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
  let drKeyRand ← liftM (chooseInitPartnerDrKeyRand P st.respSessions sessEntry)
  set { st with sessions := { sessEntry with drKeyRand := drKeyRand } :: st.sessions, roCache :=
    roCache' }
  match findHonestPrincipal P st.principals bundle.ikB with
  | some _ => return .hdrResp hdr
  | none   => return .initUnfreshResp drKeyReal hdr

noncomputable def pqxdhKeyIndFgPreImpl (useDh1 : Bool) (targetIdx targetSpkIdx : ℕ)
    (optUsk optVsk : Option Bytes) (S : Setup) (P : Primitives) :
    QueryImpl (keyIndSpec S) (StateT (KeyIndFgCutoffState S) ProbComp)
  | .initPrin u => liftFgBase (fgPreInitPrin useDh1 targetIdx optUsk S P u)
  | .genSPK u j => liftFgBase (fgPreGenSPK targetSpkIdx optVsk S P u j)
  | .initiateOPK u i bundle =>
    liftFgBase (do
      let _ ← get
      if bundle.opkB?.isNone then return .noneResp
      fgPreInitiate useDh1 targetIdx optUsk S P (.sendOPK u i) u bundle)
  | .initiateNoOPK u i bundle =>
    liftFgBase (do
      let _ ← get
      if bundle.opkB?.isSome then return .noneResp
      fgPreInitiate useDh1 targetIdx optUsk S P (.sendNoOPK u i) u bundle)
  | q => pqxdhKeyIndFgImpl S P q

theorem pqxdhKeyIndFgPreImpl_none_none_eq {S : Setup} (useDh1 : Bool) (targetIdx targetSpkIdx : ℕ)
    (P : Primitives) :
    pqxdhKeyIndFgPreImpl useDh1 targetIdx targetSpkIdx none none S P = pqxdhKeyIndFgImpl S P := by
  funext q
  cases q with
  | initiateOPK u i bundle =>
    unfold pqxdhKeyIndFgPreImpl pqxdhKeyIndFgImpl pqxdhKeyIndImpl liftFgBase fgPreInitiate
      runKeyIndInitiate
    simp only [liftM_chooseInitPartnerDrKeyRand_bind]
    rfl
  | initiateNoOPK u i bundle =>
    unfold pqxdhKeyIndFgPreImpl pqxdhKeyIndFgImpl pqxdhKeyIndImpl liftFgBase fgPreInitiate
      runKeyIndInitiate
    simp only [liftM_chooseInitPartnerDrKeyRand_bind]
    rfl
  | _ => rfl

theorem mem_support_liftFgBase {S : Setup} (m : StateT (KeyIndState S) ProbComp KeyIndResponse)
    (hst : KeyIndFgCutoffState S) (x : KeyIndResponse × KeyIndFgCutoffState S)
    (hx : x ∈ support ((liftFgBase m).run hst)) :
    (x.1, x.2.base) ∈ support (m.run hst.base) ∧ x.2.advRoLog = hst.advRoLog := by
  unfold liftFgBase at hx
  simp only [StateT_run_mk, MonadAttach.mem_support_bind, support_pure, Set.mem_singleton_iff] at hx
  rcases hx with ⟨⟨r, b'⟩, hb, hEq⟩
  have h1 := (Prod.mk.inj hEq).1
  have h2 := (Prod.mk.inj hEq).2
  rw [h1, h2]
  exact ⟨hb, rfl⟩

theorem mem_support_recordKeyIndResp {S : Setup} (P : Primitives) (r : KeyIndRespEntry S)
    (st : KeyIndState S) (x : Unit × KeyIndState S)
    (hx : x ∈ support ((recordKeyIndResp S P r).run st)) :
    x.2.principals = st.principals ∧ x.2.spkBundles = st.spkBundles ∧
      x.2.opkEntries = st.opkEntries ∧ x.2.sessions = st.sessions := by
  unfold recordKeyIndResp at hx
  simp only [StateT.run_bind, StateT.run_get, pure_bind] at hx
  revert hx
  cases st.sessions.find? (fun s => keyIndPartner P s r) with
  | some s =>
    simp only [StateT.run_set, support_pure, Set.mem_singleton_iff]
    intro hEq; have hB := (Prod.mk.inj hEq).2; rw [hB]; exact ⟨rfl, rfl, rfl, rfl⟩
  | none =>
    simp only [StateT.run_bind, StateT.run_monadLift, monadLift_self,
      StateT.run_set, MonadAttach.mem_support_bind, support_pure, Set.mem_singleton_iff]
    rintro ⟨_, _, hEq⟩; have hB := (Prod.mk.inj hEq).2; rw [hB]; exact ⟨rfl, rfl, rfl, rfl⟩

theorem mem_support_fgPreInitiate_elim {S : Setup} (useDh1 : Bool) (sIdx : ℕ)
    (optUsk : Option Bytes) (P : Primitives) (sid : SessionId S) (u : Fin S.N_id)
    (bundle : PreKeyBundleInput) (st : KeyIndState S)
    (x : KeyIndResponse × KeyIndState S)
    (hx : x ∈ support ((fgPreInitiate useDh1 sIdx optUsk S P sid u bundle).run st))
    {Φ : Prop}
    (hUnch : x.2 = st → Φ)
    (hCons : ∀ (s : KeyIndInitiatorEntry S) (roCache' : List (Bytes × DRKey)),
      st.sessions.any (fun e => e.sid == s.sid) = false →
      x.2 = { st with roCache := roCache', sessions := s :: st.sessions } → Φ) :
    Φ := by
  unfold fgPreInitiate at hx
  simp only [StateT.run_bind, StateT.run_get, pure_bind] at hx
  revert hx
  cases hAny : st.sessions.any (fun e => e.sid == sid)
  · simp only [Bool.false_eq_true, ↓reduceIte]
    cases st.principals.find? (fun (idx, _) => idx == u.val) with
    | none =>
      simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff]
      intro hEq; exact hUnch (Prod.mk.inj hEq).2
    | some p =>
      rcases p with ⟨_, _⟩; dsimp only
      cases koskBundleOk P st.principals st.spkBundles st.opkEntries st.advKeys bundle
      · simp only [Bool.not_false, ↓reduceIte, StateT.run_pure, support_pure,
          Set.mem_singleton_iff]
        intro hEq; exact hUnch (Prod.mk.inj hEq).2
      · simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte,
          StateT.run_bind, StateT.run_monadLift, monadLift_self, bind_assoc, pure_bind,
          MonadAttach.mem_support_bind]
        rintro ⟨ekASk, _, kemCoins, _, hb⟩; revert hb
        split_ifs
        · simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff]
          intro hEq; exact hUnch (Prod.mk.inj hEq).2
        · cases P.kemEncaps bundle.pqspkB kemCoins with
          | none =>
            simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff]
            intro hEq; exact hUnch (Prod.mk.inj hEq).2
          | some sc =>
            rcases sc with ⟨_, _⟩; dsimp only
            simp only [StateT.run_bind, StateT.run_monadLift, monadLift_self, StateT.run_set,
              bind_assoc, pure_bind, MonadAttach.mem_support_bind]
            rintro ⟨⟨_, roCache'⟩, _, _, _, hb⟩; revert hb
            cases findHonestPrincipal P st.principals bundle.ikB <;>
            · simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff]
              intro hEq; exact hCons _ roCache' hAny (Prod.mk.inj hEq).2
  · simp only [↓reduceIte, StateT.run_pure, support_pure, Set.mem_singleton_iff]
    intro hEq; exact hUnch (Prod.mk.inj hEq).2

theorem mem_support_pqxdhKeyIndFgPreImpl_elim {S : Setup} (useDh1 : Bool)
    (targetIdx targetSpkIdx : ℕ) (optUsk optVsk : Option Bytes) (P : Primitives)
    (q : KeyIndQuery S) (hst : KeyIndFgCutoffState S)
    (x : KeyIndResponse × KeyIndFgCutoffState S)
    (hx : x ∈ support
      ((pqxdhKeyIndFgPreImpl useDh1 targetIdx targetSpkIdx optUsk optVsk S P q).run hst))
    {Φ : Prop}
    (hUnch : x.2.base.principals = hst.base.principals →
      x.2.base.spkBundles = hst.base.spkBundles →
      x.2.base.opkEntries = hst.base.opkEntries →
      x.2.base.sessions = hst.base.sessions → Φ)
    (hInitPrin : ∀ (u : Fin S.N_id) (e : PrincipalEntry),
      q = .initPrin u →
      hst.base.principals.any (fun (idx, _) => idx == u.val) = false →
      x.2.base = { hst.base with principals := (u.val, e) :: hst.base.principals } → Φ)
    (hCorruptIK : ∀ (u : Fin S.N_id) (u1 : Nat) (entry1 : PrincipalEntry),
      q = .corruptIK u →
      hst.base.principals.find? (fun (idx, _) => idx == u.val) = some (u1, entry1) →
      x.2.base = { hst.base with
        principals := hst.base.principals.map (fun (idx, e) =>
          if idx == u.val then (idx, { e with corrupted := true }) else (idx, e)) } → Φ)
    (hGenSPK : ∀ (u : Fin S.N_id) (j : Fin S.N_recv) (bEntry : SpkBundleEntry),
      q = .genSPK u j →
      hst.base.spkBundles.any (fun (k, _) => k == (u.val, j.val)) = false →
      bEntry.revealed = false →
      (∀ vSk, optVsk = some vSk → (spkBundleFlatIdx S u j == targetSpkIdx) = true →
        bEntry.spkSk = vSk ∧ bEntry.spkPk = P.x25519Base vSk) →
      x.2.base = { hst.base with spkBundles := ((u.val, j.val), bEntry) :: hst.base.spkBundles } →
      Φ)
    (hGenOPK : ∀ (u : Fin S.N_id) (j : Fin S.N_recv) (o : Fin S.N_opk) (oEntry : OpkEntry),
      q = .genOPK u j o →
      hst.base.opkEntries.any (fun (k, _) => k == (u.val, j.val, o.val)) = false →
      oEntry.consumed = false →
      x.2.base = { hst.base with opkEntries := ((u.val, j.val, o.val), oEntry) :: hst.base.opkEntries } →
      Φ)
    (hInitiate : ∀ (s : KeyIndInitiatorEntry S) (roCache' : List (Bytes × DRKey)),
      hst.base.sessions.any (fun e => e.sid == s.sid) = false →
      x.2.base = { hst.base with roCache := roCache', sessions := s :: hst.base.sessions } → Φ)
    (hAcceptOPK : ∀ (k : Fin S.N_id) (j : Fin S.N_recv) (o : Fin S.N_opk),
      x.2.base.principals = hst.base.principals →
      x.2.base.spkBundles = hst.base.spkBundles →
      x.2.base.sessions = hst.base.sessions →
      x.2.base.opkEntries = hst.base.opkEntries.map (fun (idx, e) =>
        if idx == (k.val, j.val, o.val) then (idx, { e with consumed := true }) else (idx, e)) →
      Φ)
    (hSessMap : ∀ (f : KeyIndInitiatorEntry S → KeyIndInitiatorEntry S),
      (∀ s, (f s).sid = s.sid) →
      (∀ s, (f s).peerIkPk = s.peerIkPk) →
      (∀ s, (f s).peerSpkPk = s.peerSpkPk) →
      (∀ s, (f s).peerOpkPk? = s.peerOpkPk?) →
      x.2.base.principals = hst.base.principals →
      x.2.base.spkBundles = hst.base.spkBundles →
      x.2.base.opkEntries = hst.base.opkEntries →
      x.2.base.sessions = hst.base.sessions.map f → Φ)
    (hRevealSpk : ∀ (u : Fin S.N_id) (j : Fin S.N_recv),
      x.2.base = { hst.base with
        spkBundles := hst.base.spkBundles.map (fun (idx, b) =>
          if idx == (u.val, j.val) then (idx, { b with revealed := true }) else (idx, b)) } →
      Φ) :
    Φ := by
  have unchanged : x.2.base = hst.base → Φ := fun hB =>
    hUnch (by rw [hB]) (by rw [hB]) (by rw [hB]) (by rw [hB])
  cases q with
  | initPrin u =>
    unfold pqxdhKeyIndFgPreImpl fgPreInitPrin at hx
    rcases mem_support_liftFgBase _ hst x hx with ⟨hb, _⟩; clear hx
    simp only [StateT.run_bind, StateT.run_get, pure_bind] at hb
    revert hb
    cases hAny : hst.base.principals.any (fun (idx, _) => idx == u.val)
    · simp only [Bool.false_eq_true, ↓reduceIte, StateT.run_bind, StateT.run_monadLift,
        monadLift_self, StateT.run_set, StateT.run_pure, bind_assoc, pure_bind,
        MonadAttach.mem_support_bind, support_pure, Set.mem_singleton_iff]
      rintro ⟨_, _, _, _, hEq⟩
      exact hInitPrin u _ rfl hAny (Prod.mk.inj hEq).2
    · simp only [↓reduceIte, StateT.run_pure, support_pure, Set.mem_singleton_iff]
      intro hEq; exact unchanged (Prod.mk.inj hEq).2
  | genSPK u j =>
    unfold pqxdhKeyIndFgPreImpl fgPreGenSPK at hx
    rcases mem_support_liftFgBase _ hst x hx with ⟨hb, _⟩; clear hx
    simp only [StateT.run_bind, StateT.run_get, pure_bind] at hb
    revert hb
    cases hAny : hst.base.spkBundles.any (fun (k, _) => k == (u.val, j.val))
    · simp only [Bool.false_eq_true, ↓reduceIte]
      cases hst.base.principals.find? (fun (idx, _) => idx == u.val) with
      | none =>
        simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff]
        intro hEq; exact unchanged (Prod.mk.inj hEq).2
      | some p =>
        rcases p with ⟨_, uEntry⟩
        simp only [StateT.run_bind, StateT.run_monadLift, monadLift_self, StateT.run_set,
          StateT.run_pure, bind_assoc, pure_bind, MonadAttach.mem_support_bind,
          support_pure, Set.mem_singleton_iff]
        rintro ⟨spkSk, hSk, rSpk, _, pqPair, _, rPq, _, hEq⟩
        refine hGenSPK u j _ rfl hAny rfl (fun vSk hOpt hSlot => ?_) (Prod.mk.inj hEq).2
        subst hOpt
        simp only [hSlot, ↓reduceIte, support_pure, Set.mem_singleton_iff] at hSk
        subst hSk; exact ⟨rfl, rfl⟩
    · simp only [↓reduceIte, StateT.run_pure, support_pure, Set.mem_singleton_iff]
      intro hEq; exact unchanged (Prod.mk.inj hEq).2
  | initiateOPK u i bundle =>
    unfold pqxdhKeyIndFgPreImpl at hx
    rcases mem_support_liftFgBase _ hst x hx with ⟨hb, _⟩; clear hx
    simp only [StateT.run_bind, StateT.run_get, pure_bind] at hb
    revert hb
    cases bundle.opkB?.isNone
    · simp only [Bool.false_eq_true, ↓reduceIte]
      intro hb
      exact mem_support_fgPreInitiate_elim useDh1 targetIdx optUsk P (.sendOPK u i) u bundle
        hst.base (x.1, x.2.base) hb unchanged hInitiate
    · simp only [↓reduceIte, StateT.run_pure, support_pure, Set.mem_singleton_iff]
      intro hEq; exact unchanged (Prod.mk.inj hEq).2
  | initiateNoOPK u i bundle =>
    unfold pqxdhKeyIndFgPreImpl at hx
    rcases mem_support_liftFgBase _ hst x hx with ⟨hb, _⟩; clear hx
    simp only [StateT.run_bind, StateT.run_get, pure_bind] at hb
    revert hb
    cases bundle.opkB?.isSome
    · simp only [Bool.false_eq_true, ↓reduceIte]
      intro hb
      exact mem_support_fgPreInitiate_elim useDh1 targetIdx optUsk P (.sendNoOPK u i) u bundle
        hst.base (x.1, x.2.base) hb unchanged hInitiate
    · simp only [↓reduceIte, StateT.run_pure, support_pure, Set.mem_singleton_iff]
      intro hEq; exact unchanged (Prod.mk.inj hEq).2
  | corruptIK u =>
    unfold pqxdhKeyIndFgPreImpl pqxdhKeyIndFgImpl pqxdhKeyIndImpl at hx
    rcases mem_support_liftFgBase _ hst x hx with ⟨hb, _⟩; clear hx
    simp only [StateT.run_bind, StateT.run_get, pure_bind] at hb
    revert hb
    cases hFU : hst.base.principals.find? (fun (idx, _) => idx == u.val) with
    | none =>
      simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff]
      intro hEq; exact unchanged (Prod.mk.inj hEq).2
    | some p =>
      rcases p with ⟨u1, entry1⟩
      simp only [StateT.run_bind, StateT.run_set, StateT.run_pure, pure_bind,
        support_pure, Set.mem_singleton_iff]
      intro hEq; exact hCorruptIK u u1 entry1 rfl hFU (Prod.mk.inj hEq).2
  | genOPK u j o =>
    unfold pqxdhKeyIndFgPreImpl pqxdhKeyIndFgImpl pqxdhKeyIndImpl at hx
    rcases mem_support_liftFgBase _ hst x hx with ⟨hb, _⟩; clear hx
    simp only [StateT.run_bind, StateT.run_get, pure_bind] at hb
    revert hb
    cases hAny : hst.base.opkEntries.any (fun (k, _) => k == (u.val, j.val, o.val))
    · simp only [Bool.false_eq_true, ↓reduceIte, StateT.run_bind, StateT.run_monadLift,
        monadLift_self, StateT.run_set, StateT.run_pure, bind_assoc, pure_bind,
        MonadAttach.mem_support_bind, support_pure, Set.mem_singleton_iff]
      rintro ⟨_, _, hEq⟩
      exact hGenOPK u j o _ rfl hAny rfl (Prod.mk.inj hEq).2
    · simp only [↓reduceIte, StateT.run_pure, support_pure, Set.mem_singleton_iff]
      intro hEq; exact unchanged (Prod.mk.inj hEq).2
  | acceptOPK k j o hdr =>
    unfold pqxdhKeyIndFgPreImpl pqxdhKeyIndFgImpl pqxdhKeyIndImpl at hx
    rcases mem_support_liftFgBase _ hst x hx with ⟨hb, _⟩; clear hx
    simp only [StateT.run_bind, StateT.run_get, pure_bind] at hb
    revert hb
    split_ifs with h1 h2 h2b
    · simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff]
      intro hEq; exact unchanged (Prod.mk.inj hEq).2
    · simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff]
      intro hEq; exact unchanged (Prod.mk.inj hEq).2
    · simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff]
      intro hEq; exact unchanged (Prod.mk.inj hEq).2
    · cases hst.base.principals.find? (fun (idx, _) => idx == k.val) with
      | none =>
        simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff]
        intro hEq; exact unchanged (Prod.mk.inj hEq).2
      | some kp =>
        rcases kp with ⟨_, _⟩; dsimp only
        cases hst.base.spkBundles.find? (fun (idx, _) => idx == (k.val, j.val)) with
        | none =>
          simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff]
          intro hEq; exact unchanged (Prod.mk.inj hEq).2
        | some bp =>
          rcases bp with ⟨_, bEntry⟩; dsimp only
          cases hst.base.opkEntries.find? (fun (idx, _) => idx == (k.val, j.val, o.val)) with
          | none =>
            simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff]
            intro hEq; exact unchanged (Prod.mk.inj hEq).2
          | some op =>
            rcases op with ⟨_, _⟩; dsimp only
            split_ifs with h3
            · simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff]
              intro hEq; exact unchanged (Prod.mk.inj hEq).2
            · cases Model.acceptKeys P _ with
              | none =>
                simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff]
                intro hEq; exact unchanged (Prod.mk.inj hEq).2
              | some _ =>
                dsimp only
                cases P.kemDecaps bEntry.pqspkSk hdr.kemCt with
                | none =>
                  simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff]
                  intro hEq; exact unchanged (Prod.mk.inj hEq).2
                | some _ =>
                  dsimp only
                  simp only [StateT.run_bind, StateT.run_monadLift, monadLift_self, StateT.run_set,
                    bind_assoc, pure_bind, MonadAttach.mem_support_bind]
                  rintro ⟨⟨_, _⟩, _, y, hy, hb⟩
                  rcases mem_support_recordKeyIndResp P _ _ y hy with ⟨hP, hS, hO, hSe⟩
                  revert hb
                  cases findHonestPrincipal P hst.base.principals hdr.ikAPk <;>
                  · simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff]
                    intro hEq; have hB := (Prod.mk.inj hEq).2
                    exact hAcceptOPK k j o (by rw [hB, hP]) (by rw [hB, hS]) (by rw [hB, hSe])
                      (by rw [hB, hO])
  | acceptNoOPK k j l hdr =>
    unfold pqxdhKeyIndFgPreImpl pqxdhKeyIndFgImpl pqxdhKeyIndImpl at hx
    rcases mem_support_liftFgBase _ hst x hx with ⟨hb, _⟩; clear hx
    simp only [StateT.run_bind, StateT.run_get, pure_bind] at hb
    revert hb
    split_ifs with h1 h2 h2b
    · simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff]
      intro hEq; exact unchanged (Prod.mk.inj hEq).2
    · simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff]
      intro hEq; exact unchanged (Prod.mk.inj hEq).2
    · simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff]
      intro hEq; exact unchanged (Prod.mk.inj hEq).2
    · cases hst.base.principals.find? (fun (idx, _) => idx == k.val) with
      | none =>
        simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff]
        intro hEq; exact unchanged (Prod.mk.inj hEq).2
      | some kp =>
        rcases kp with ⟨_, _⟩; dsimp only
        cases hst.base.spkBundles.find? (fun (idx, _) => idx == (k.val, j.val)) with
        | none =>
          simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff]
          intro hEq; exact unchanged (Prod.mk.inj hEq).2
        | some bp =>
          rcases bp with ⟨_, bEntry⟩; dsimp only
          cases Model.acceptKeys P _ with
          | none =>
            simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff]
            intro hEq; exact unchanged (Prod.mk.inj hEq).2
          | some _ =>
            dsimp only
            cases P.kemDecaps bEntry.pqspkSk hdr.kemCt with
            | none =>
              simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff]
              intro hEq; exact unchanged (Prod.mk.inj hEq).2
            | some _ =>
              dsimp only
              simp only [StateT.run_bind, StateT.run_monadLift, monadLift_self, StateT.run_set,
                bind_assoc, pure_bind, MonadAttach.mem_support_bind]
              rintro ⟨⟨_, _⟩, _, y, hy, hb⟩
              rcases mem_support_recordKeyIndResp P _ _ y hy with ⟨hP, hS, hO, hSe⟩
              revert hb
              cases findHonestPrincipal P hst.base.principals hdr.ikAPk <;>
              · simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff]
                intro hEq; have hB := (Prod.mk.inj hEq).2
                exact hUnch (by rw [hB, hP]) (by rw [hB, hS]) (by rw [hB, hO]) (by rw [hB, hSe])
  | testSession sid =>
    unfold pqxdhKeyIndFgPreImpl pqxdhKeyIndFgImpl pqxdhKeyIndImpl at hx
    rcases mem_support_liftFgBase _ hst x hx with ⟨hb, _⟩; clear hx
    simp only [StateT.run_bind, StateT.run_get, pure_bind] at hb
    revert hb
    by_cases h1 : (!isKeyIndSessionTestable hst.base sid) = true
    · simp only [h1, ↓reduceIte, StateT.run_pure, support_pure, Set.mem_singleton_iff]
      intro hEq; exact unchanged (Prod.mk.inj hEq).2
    · simp only [h1, Bool.false_eq_true, ↓reduceIte]
      cases hst.base.sessions.find? (fun e => e.sid == sid) with
      | some _ =>
        simp only [StateT.run_bind, StateT.run_set, StateT.run_pure, pure_bind,
          support_pure, Set.mem_singleton_iff]
        intro hEq; have hB := (Prod.mk.inj hEq).2
        exact hSessMap (fun s => if s.sid == sid then { s with tested := true } else s)
          (fun s => by split_ifs <;> rfl) (fun s => by split_ifs <;> rfl)
          (fun s => by split_ifs <;> rfl) (fun s => by split_ifs <;> rfl)
          (by rw [hB]) (by rw [hB]) (by rw [hB]) (by rw [hB])
      | none =>
        cases hst.base.respSessions.find? (fun r => r.sid == sid) with
        | none =>
          simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff]
          intro hEq; exact unchanged (Prod.mk.inj hEq).2
        | some _ =>
          simp only [StateT.run_bind, StateT.run_set, StateT.run_pure, pure_bind,
            support_pure, Set.mem_singleton_iff]
          intro hEq; have hB := (Prod.mk.inj hEq).2
          exact hUnch (by rw [hB]) (by rw [hB]) (by rw [hB]) (by rw [hB])
  | revealSessionKey sid =>
    unfold pqxdhKeyIndFgPreImpl pqxdhKeyIndFgImpl pqxdhKeyIndImpl at hx
    rcases mem_support_liftFgBase _ hst x hx with ⟨hb, _⟩; clear hx
    simp only [StateT.run_bind, StateT.run_get, pure_bind] at hb
    revert hb
    cases hst.base.sessions.find? (fun e => e.sid == sid) with
    | some e =>
      by_cases ht : e.tested = true
      · simp only [ht, ↓reduceIte, StateT.run_pure, support_pure, Set.mem_singleton_iff]
        intro hEq; exact unchanged (Prod.mk.inj hEq).2
      · simp only [ht, Bool.false_eq_true, ↓reduceIte, StateT.run_bind, StateT.run_set,
          StateT.run_pure, pure_bind, support_pure, Set.mem_singleton_iff]
        intro hEq; have hB := (Prod.mk.inj hEq).2
        exact hSessMap (fun s => if s.sid == sid then { s with revealed := true } else s)
          (fun s => by split_ifs <;> rfl) (fun s => by split_ifs <;> rfl)
          (fun s => by split_ifs <;> rfl) (fun s => by split_ifs <;> rfl)
          (by rw [hB]) (by rw [hB]) (by rw [hB]) (by rw [hB])
    | none =>
      cases hst.base.respSessions.find? (fun r => r.sid == sid) with
      | none =>
        simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff]
        intro hEq; exact unchanged (Prod.mk.inj hEq).2
      | some r =>
        by_cases ht : r.tested = true
        · simp only [ht, ↓reduceIte, StateT.run_pure, support_pure, Set.mem_singleton_iff]
          intro hEq; exact unchanged (Prod.mk.inj hEq).2
        · simp only [ht, Bool.false_eq_true, ↓reduceIte, StateT.run_bind, StateT.run_set,
            StateT.run_pure, pure_bind, support_pure, Set.mem_singleton_iff]
          intro hEq; have hB := (Prod.mk.inj hEq).2
          exact hUnch (by rw [hB]) (by rw [hB]) (by rw [hB]) (by rw [hB])
  | roQuery secrets =>
    unfold pqxdhKeyIndFgPreImpl pqxdhKeyIndFgImpl pqxdhKeyIndImpl at hx
    simp only [StateT_run_mk, StateT.run_bind, StateT.run_get, StateT.run_monadLift, monadLift_self,
      StateT.run_set, StateT.run_pure, Bool.not_true, Bool.false_eq_true, ↓reduceIte,
      bind_assoc, pure_bind, MonadAttach.mem_support_bind, support_pure,
        Set.mem_singleton_iff] at hx
    rcases hx with ⟨⟨_, _⟩, _, hEq⟩
    have hB := (Prod.mk.inj hEq).2
    exact hUnch (by rw [hB]) (by rw [hB]) (by rw [hB]) (by rw [hB])
  | revealDhSecrets =>
    unfold pqxdhKeyIndFgPreImpl pqxdhKeyIndFgImpl pqxdhKeyIndImpl at hx
    rcases mem_support_liftFgBase _ hst x hx with ⟨hb, _⟩; clear hx
    simp only [StateT.run_bind, StateT.run_get, pure_bind, ↓reduceIte,
      StateT.run_pure, support_pure, Set.mem_singleton_iff] at hb
    exact unchanged (Prod.mk.inj hb).2
  | registerKey sk =>
    unfold pqxdhKeyIndFgPreImpl pqxdhKeyIndFgImpl pqxdhKeyIndImpl registerAdvKey at hx
    rcases mem_support_liftFgBase _ hst x hx with ⟨hb, _⟩; clear hx
    simp only [StateT.run_bind, StateT.run_get, pure_bind] at hb
    revert hb
    split_ifs
    · simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff]
      intro hEq; exact unchanged (Prod.mk.inj hEq).2
    · simp only [StateT.run_bind, StateT.run_set, StateT.run_pure, pure_bind,
        support_pure, Set.mem_singleton_iff]
      intro hEq; have hB := (Prod.mk.inj hEq).2
      exact hUnch (by rw [hB]) (by rw [hB]) (by rw [hB]) (by rw [hB])
  | revealSpkSk u j =>
    unfold pqxdhKeyIndFgPreImpl pqxdhKeyIndFgImpl pqxdhKeyIndImpl at hx
    rcases mem_support_liftFgBase _ hst x hx with ⟨hb, _⟩; clear hx
    simp only [StateT.run_bind, StateT.run_get, pure_bind] at hb
    revert hb
    cases hst.base.spkBundles.find? (fun (idx, _) => idx == (u.val, j.val)) with
    | none =>
      simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff]
      intro hEq; exact unchanged (Prod.mk.inj hEq).2
    | some _ =>
      simp only [StateT.run_bind, StateT.run_set, StateT.run_pure, pure_bind,
        support_pure, Set.mem_singleton_iff]
      intro hEq; exact hRevealSpk u j (Prod.mk.inj hEq).2

theorem pqxdhKeyIndFgPreImpl_preserves_hasFired {S : Setup} (useDh1 : Bool)
    (targetIdx targetSpkIdx : ℕ) (optUsk optVsk : Option Bytes) (P : Primitives)
    (q : KeyIndQuery S) (hst : KeyIndFgCutoffState S)
    (x : KeyIndResponse × KeyIndFgCutoffState S)
    (hx : x ∈ support ((pqxdhKeyIndFgPreImpl useDh1 targetIdx targetSpkIdx optUsk optVsk S P q).run
      hst)) :
    (∀ bIdx, hasFiredSpk S bIdx hst → hasFiredSpk S bIdx x.2) ∧
    (∀ uIdx, hasFiredPrin S uIdx hst → hasFiredPrin S uIdx x.2) ∧
    (∀ sIdx, hasFiredSess S sIdx hst → hasFiredSess S sIdx x.2) := by
  refine mem_support_pqxdhKeyIndFgPreImpl_elim useDh1 targetIdx targetSpkIdx optUsk optVsk P q hst x
    hx ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · intro hP hS _ hSe
    exact ⟨fun bIdx ⟨u₀, j₀, h1, h2⟩ => ⟨u₀, j₀, h1, by rw [hS]; exact h2⟩,
      fun uIdx h => by unfold hasFiredPrin at h ⊢; rw [hP]; exact h,
      fun sIdx h => by unfold hasFiredSess at h ⊢; rw [hSe]; exact h⟩
  · intro u e _ _ hB
    exact ⟨fun bIdx ⟨u₀, j₀, h1, h2⟩ => ⟨u₀, j₀, h1, by rw [hB]; exact h2⟩,
      fun uIdx h => by unfold hasFiredPrin at h ⊢; rw [hB]; simp [List.any_cons, h],
      fun sIdx h => by unfold hasFiredSess at h ⊢; rw [hB]; exact h⟩
  · intro u _ _ _ _ hB
    refine ⟨fun bIdx ⟨u₀, j₀, h1, h2⟩ => ⟨u₀, j₀, h1, by rw [hB]; exact h2⟩,
      fun uIdx h => ?_,
      fun sIdx h => by unfold hasFiredSess at h ⊢; rw [hB]; exact h⟩
    unfold hasFiredPrin at h ⊢; rw [hB]; dsimp only
    rw [List.any_map]; rw [List.any_eq_true] at h ⊢
    rcases h with ⟨⟨idx, e⟩, hy, hidx⟩
    exact ⟨(idx, e), hy, by dsimp only [Function.comp_apply] at hidx ⊢; split_ifs <;> exact hidx⟩
  · intro u j bEntry _ _ _ _ hB
    exact ⟨fun bIdx ⟨u₀, j₀, h1, h2⟩ => ⟨u₀, j₀, h1, by rw [hB]; simp [List.any_cons, h2]⟩,
      fun uIdx h => by unfold hasFiredPrin at h ⊢; rw [hB]; exact h,
      fun sIdx h => by unfold hasFiredSess at h ⊢; rw [hB]; exact h⟩
  · intro u j o oEntry _ _ _ hB
    exact ⟨fun bIdx ⟨u₀, j₀, h1, h2⟩ => ⟨u₀, j₀, h1, by rw [hB]; exact h2⟩,
      fun uIdx h => by unfold hasFiredPrin at h ⊢; rw [hB]; exact h,
      fun sIdx h => by unfold hasFiredSess at h ⊢; rw [hB]; exact h⟩
  · intro s _ _ hB
    exact ⟨fun bIdx ⟨u₀, j₀, h1, h2⟩ => ⟨u₀, j₀, h1, by rw [hB]; exact h2⟩,
      fun uIdx h => by unfold hasFiredPrin at h ⊢; rw [hB]; exact h,
      fun sIdx h => by unfold hasFiredSess at h ⊢; rw [hB]; simp [List.any_cons, h]⟩
  · intro k j o hP hS hSe _
    exact ⟨fun bIdx ⟨u₀, j₀, h1, h2⟩ => ⟨u₀, j₀, h1, by rw [hS]; exact h2⟩,
      fun uIdx h => by unfold hasFiredPrin at h ⊢; rw [hP]; exact h,
      fun sIdx h => by unfold hasFiredSess at h ⊢; rw [hSe]; exact h⟩
  · intro f hfSid _ _ _ hP hS _ hSe
    refine ⟨fun bIdx ⟨u₀, j₀, h1, h2⟩ => ⟨u₀, j₀, h1, by rw [hS]; exact h2⟩,
      fun uIdx h => by unfold hasFiredPrin at h ⊢; rw [hP]; exact h,
      fun sIdx h => ?_⟩
    unfold hasFiredSess at h ⊢; rw [hSe, List.any_map]
    rw [List.any_eq_true] at h ⊢
    rcases h with ⟨s, hs, hidx⟩
    exact ⟨s, hs, by dsimp only [Function.comp_apply]; rw [hfSid s]; exact hidx⟩
  · intro u j hB
    refine ⟨fun bIdx ⟨u₀, j₀, h1, h2⟩ => ⟨u₀, j₀, h1, ?_⟩,
      fun uIdx h => by unfold hasFiredPrin at h ⊢; rw [hB]; exact h,
      fun sIdx h => by unfold hasFiredSess at h ⊢; rw [hB]; exact h⟩
    rw [hB]; dsimp only; rw [List.any_map]
    rw [List.any_eq_true] at h2 ⊢
    rcases h2 with ⟨⟨idx, b⟩, hMem, hEq⟩
    exact ⟨(idx, b), hMem, by dsimp only [Function.comp_apply] at hEq ⊢; split_ifs <;> exact hEq⟩

theorem evalDist_preSample_V_pqxdhKeyIndFgPreImpl {S : Setup} {α : Type}
    (useDh1 : Bool) (targetIdx targetSpkIdx : ℕ) (optUsk : Option Bytes) (P : Primitives)
    (oa : OracleComp (unifSpec + keyIndSpec S) α) (hst : KeyIndFgCutoffState S)
    (obs : α × KeyIndFgCutoffState S → ProbComp Bool) :
    let fullPre (vSk : Bytes) := (QueryImpl.ofLift unifSpec ProbComp).liftTarget
        (StateT (KeyIndFgCutoffState S) ProbComp) +
      pqxdhKeyIndFgPreImpl useDh1 targetIdx targetSpkIdx optUsk (some vSk) S P
    let fullLazy := (QueryImpl.ofLift unifSpec ProbComp).liftTarget
        (StateT (KeyIndFgCutoffState S) ProbComp) +
      pqxdhKeyIndFgPreImpl useDh1 targetIdx targetSpkIdx optUsk none S P
    𝒟[sampleScalar32 >>= fun vSk => (simulateQ (fullPre vSk) oa).run hst >>= obs] =
    𝒟[(simulateQ fullLazy oa).run hst >>= obs] := by
  refine evalDist_simulateQ_preSample_slot_eq
    sampleScalar32
    (hasFiredSpk S targetSpkIdx)
    (pqxdhKeyIndFgPreImpl useDh1 targetIdx targetSpkIdx optUsk none S P)
    (fun vSk => pqxdhKeyIndFgPreImpl useDh1 targetIdx targetSpkIdx optUsk (some vSk) S P)
    (fun q s hFired => ⟨?_, fun x hx =>
      (pqxdhKeyIndFgPreImpl_preserves_hasFired useDh1 targetIdx targetSpkIdx optUsk none P q s x
        hx).1
        targetSpkIdx hFired⟩)
    (fun q s _ => ?_)
    oa hst obs
  · intro vSk
    cases q with
    | genSPK u j =>
      unfold pqxdhKeyIndFgPreImpl fgPreGenSPK liftFgBase
      simp only [StateT_run_mk, StateT.run_bind, StateT.run_get, pure_bind]
      by_cases hSlot : (spkBundleFlatIdx S u j == targetSpkIdx) = true
      · have hany := spkBundles_any_of_hasFiredSpk S targetSpkIdx s hFired u j hSlot
        simp [hany]
      · cases s.base.spkBundles.any (fun (k, _) => k == (u.val, j.val))
        · simp only [Bool.false_eq_true, ↓reduceIte]
          cases s.base.principals.find? (fun (idx, _) => idx == u.val) with
          | none => rfl
          | some p => rcases p with ⟨_, uEntry⟩; simp [hSlot]
        · rfl
    | _ => rfl
  · cases q with
    | genSPK u j =>
      by_cases hSlot : (spkBundleFlatIdx S u j == targetSpkIdx) = true
      · unfold pqxdhKeyIndFgPreImpl fgPreGenSPK liftFgBase
        simp only [StateT_run_mk, StateT.run_bind, StateT.run_get, pure_bind]
        cases s.base.spkBundles.any (fun (k, _) => k == (u.val, j.val))
        · simp only [Bool.false_eq_true, ↓reduceIte]
          cases s.base.principals.find? (fun (idx, _) => idx == u.val) with
          | none => exact Or.inl (fun _ => rfl)
          | some p =>
            rcases p with ⟨_, uEntry⟩
            dsimp only
            refine Or.inr ⟨fun obs' => ?_, fun vSk x hx => ?_⟩
            · simp only [hSlot, ↓reduceIte, StateT.run_bind, StateT.run_pure, StateT.run_monadLift,
                monadLift_self, StateT.run_set, pure_bind, bind_assoc]
            · simp only [hSlot, ↓reduceIte, StateT.run_bind, StateT.run_pure, StateT.run_monadLift,
                monadLift_self, StateT.run_set, pure_bind, bind_assoc, MonadAttach.mem_support_bind,
                support_pure, Set.mem_singleton_iff] at hx
              rcases hx with ⟨rSpk, _, pqPair, _, rPq, _, hEq⟩
              have hB := (Prod.mk.inj hEq).2
              exact ⟨u, j, beq_iff_eq.mp hSlot, by rw [hB]; simp⟩
        · exact Or.inl (fun _ => rfl)
      · refine Or.inl (fun vSk => ?_)
        unfold pqxdhKeyIndFgPreImpl fgPreGenSPK liftFgBase
        simp only [StateT_run_mk, StateT.run_bind, StateT.run_get, pure_bind]
        cases s.base.spkBundles.any (fun (k, _) => k == (u.val, j.val))
        · simp only [Bool.false_eq_true, ↓reduceIte]
          cases s.base.principals.find? (fun (idx, _) => idx == u.val) with
          | none => rfl
          | some p => rcases p with ⟨_, uEntry⟩; simp [hSlot]
        · rfl
    | _ => exact Or.inl (fun _ => rfl)

theorem evalDist_preSample_U_dh1_pqxdhKeyIndFgPreImpl {S : Setup} {α : Type}
    (targetIdx targetSpkIdx : ℕ) (optVsk : Option Bytes) (P : Primitives)
    (oa : OracleComp (unifSpec + keyIndSpec S) α) (hst : KeyIndFgCutoffState S)
    (obs : α × KeyIndFgCutoffState S → ProbComp Bool) :
    let fullPre (uSk : Bytes) := (QueryImpl.ofLift unifSpec ProbComp).liftTarget
        (StateT (KeyIndFgCutoffState S) ProbComp) +
      pqxdhKeyIndFgPreImpl true targetIdx targetSpkIdx (some uSk) optVsk S P
    let fullLazy := (QueryImpl.ofLift unifSpec ProbComp).liftTarget
        (StateT (KeyIndFgCutoffState S) ProbComp) +
      pqxdhKeyIndFgPreImpl true targetIdx targetSpkIdx none optVsk S P
    𝒟[sampleScalar32 >>= fun uSk => (simulateQ (fullPre uSk) oa).run hst >>= obs] =
    𝒟[(simulateQ fullLazy oa).run hst >>= obs] := by
  refine evalDist_simulateQ_preSample_slot_eq
    sampleScalar32
    (hasFiredPrin S targetIdx)
    (pqxdhKeyIndFgPreImpl true targetIdx targetSpkIdx none optVsk S P)
    (fun uSk => pqxdhKeyIndFgPreImpl true targetIdx targetSpkIdx (some uSk) optVsk S P)
    (fun q s hFired => ⟨?_, fun x hx =>
      (pqxdhKeyIndFgPreImpl_preserves_hasFired true targetIdx targetSpkIdx none optVsk P q s x
        hx).2.1
        targetIdx hFired⟩)
    (fun q s _ => ?_)
    oa hst obs
  · intro uSk
    cases q with
    | initPrin u =>
      unfold pqxdhKeyIndFgPreImpl fgPreInitPrin liftFgBase
      simp only [StateT_run_mk, StateT.run_bind, StateT.run_get, pure_bind, Bool.true_and]
      by_cases hSlot : (u.val == targetIdx) = true
      · have hany : s.base.principals.any (fun (idx, _) => idx == u.val) = true := by
          unfold hasFiredPrin at hFired
          rw [beq_iff_eq.mp hSlot]; exact hFired
        simp [hany]
      · cases s.base.principals.any (fun (idx, _) => idx == u.val) <;> simp [hSlot]
    | _ => rfl
  · cases q with
    | initPrin u =>
      by_cases hSlot : (u.val == targetIdx) = true
      · unfold pqxdhKeyIndFgPreImpl fgPreInitPrin liftFgBase
        simp only [StateT_run_mk, StateT.run_bind, StateT.run_get, pure_bind, Bool.true_and]
        cases s.base.principals.any (fun (idx, _) => idx == u.val)
        · simp only [Bool.false_eq_true, ↓reduceIte]
          refine Or.inr ⟨fun obs' => ?_, fun uSk x hx => ?_⟩
          · simp only [hSlot, ↓reduceIte, StateT.run_bind, StateT.run_pure, StateT.run_monadLift,
              monadLift_self, StateT.run_set, pure_bind, bind_assoc]
          · simp only [hSlot, ↓reduceIte, StateT.run_bind, StateT.run_pure, StateT.run_monadLift,
              monadLift_self, StateT.run_set, pure_bind, bind_assoc, MonadAttach.mem_support_bind,
              support_pure, Set.mem_singleton_iff] at hx
            rcases hx with ⟨secIKAsign, _, hEq⟩
            have hB := (Prod.mk.inj hEq).2
            unfold hasFiredPrin; rw [hB]; simp [hSlot]
        · exact Or.inl (fun _ => rfl)
      · refine Or.inl (fun uSk => ?_)
        unfold pqxdhKeyIndFgPreImpl fgPreInitPrin liftFgBase
        simp only [StateT_run_mk, StateT.run_bind, StateT.run_get, pure_bind, Bool.true_and]
        cases s.base.principals.any (fun (idx, _) => idx == u.val) <;> simp [hSlot]
    | _ => exact Or.inl (fun _ => rfl)

noncomputable def fgPreInitiateAfterCoins {S : Setup} (P : Primitives)
    (sid : SessionId S) (uEntry : PrincipalEntry) (bundle : PreKeyBundleInput)
    (hst : KeyIndFgCutoffState S) (ekASk kemCoins : Bytes) :
    ProbComp (KeyIndResponse × KeyIndFgCutoffState S) := do
  let st := hst.base
  let sigPkB := resolveSigPk P st.principals bundle.ikB
  if !(P.sigVerify sigPkB (encodeEC bundle.spkB) bundle.spkSig &&
       P.sigVerify sigPkB (encodeKEM bundle.pqspkB) bundle.pqspkSig) then
    return (.noneResp, hst)
  let some (ss, kemCt) := P.kemEncaps bundle.pqspkB kemCoins
    | return (.noneResp, hst)
  let ekAPk := P.x25519Base ekASk
  let dh1 := P.x25519 uEntry.secIKA0 bundle.spkB
  let dh2 := P.x25519 ekASk bundle.ikB
  let dh3 := P.x25519 ekASk bundle.spkB
  let dh4? := bundle.opkB?.map (fun (_, opkPk) => P.x25519 ekASk opkPk)
  let secrets := buildSecrets dh1 dh2 dh3 dh4? ss
  let (drKeyReal, roCache') ← evalHkdfOrRo true P st.roCache secrets
  let hdr : HandshakeHdr := {
    ikAPk   := uEntry.ikAPk
    ekAPk   := ekAPk
    spkId   := bundle.spkId
    opkId?  := bundle.opkB?.map Prod.fst
    pqspkId := bundle.pqspkId
    kemCt   := kemCt
  }
  let honestPeer := isHonestUncorruptedPeer P st.principals bundle.ikB
  let (spkHon, opkHon, pqspkHon) :=
    checkBundleProvenance P st.principals st.spkBundles st.opkEntries bundle
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
  let drKeyRand ← chooseInitPartnerDrKeyRand P st.respSessions sessEntry
  let base' : KeyIndState S :=
    { st with sessions := { sessEntry with drKeyRand := drKeyRand } :: st.sessions,
              roCache := roCache' }
  let resp : KeyIndResponse :=
    match findHonestPrincipal P st.principals bundle.ikB with
    | some _ => .hdrResp hdr
    | none   => .initUnfreshResp drKeyReal hdr
  return (resp, { hst with base := base' })

theorem fgPreInitiate_run_eq_afterCoins {S : Setup} (targetIdx : ℕ) (optUsk : Option Bytes)
    (P : Primitives) (sid : SessionId S) (u : Fin S.N_id) (bundle : PreKeyBundleInput)
    (hst : KeyIndFgCutoffState S)
    (hSid : hst.base.sessions.any (fun e => e.sid == sid) = false)
    (uEntry : PrincipalEntry)
    (hPrin : hst.base.principals.find? (fun (idx, _) => idx == u.val) = some (u.val, uEntry) ∨
             ∃ idx0, hst.base.principals.find? (fun (idx, _) => idx == u.val) = some (idx0, uEntry))
    (hKosk : koskBundleOk P hst.base.principals hst.base.spkBundles hst.base.opkEntries
      hst.base.advKeys bundle = true) :
    (liftFgBase (fgPreInitiate false targetIdx optUsk S P sid u bundle)).run hst =
      ((match optUsk with
        | some uSk => if initSessionSlotIdx sid == targetIdx then pure uSk else sampleScalar32
        | none => sampleScalar32) >>= fun ekASk =>
        sampleCoins32 >>= fun kemCoins =>
        fgPreInitiateAfterCoins P sid uEntry bundle hst ekASk kemCoins) := by
  unfold liftFgBase fgPreInitiate fgPreInitiateAfterCoins
  simp only [StateT_run_mk, StateT.run_bind, StateT.run_get, pure_bind, hSid,
    Bool.false_eq_true, ↓reduceIte, Bool.not_false, Bool.true_and]
  rcases hPrin with hP | ⟨idx0, hP⟩ <;>
  · rw [hP]; dsimp only
    simp only [hKosk, Bool.not_true, Bool.false_eq_true, ↓reduceIte,
      StateT.run_bind, StateT.run_monadLift, monadLift_self, bind_assoc, pure_bind]
    congr 1; funext ekASk
    congr 1; funext kemCoins
    by_cases hSig : (!(P.sigVerify (resolveSigPk P hst.base.principals bundle.ikB)
          (encodeEC bundle.spkB) bundle.spkSig &&
        P.sigVerify (resolveSigPk P hst.base.principals bundle.ikB)
          (encodeKEM bundle.pqspkB) bundle.pqspkSig)) = true
    · simp [hSig, StateT.run_pure]
    · simp only [hSig, Bool.false_eq_true, ↓reduceIte]
      cases P.kemEncaps bundle.pqspkB kemCoins with
      | none => simp [StateT.run_pure]
      | some sc =>
        rcases sc with ⟨ss, kemCt⟩
        dsimp only
        simp only [StateT.run_bind, StateT.run_monadLift, monadLift_self, StateT.run_set,
          bind_assoc, pure_bind]
        congr 1; funext ⟨drKeyReal, roCache'⟩
        congr 1; funext drKeyRand
        cases findHonestPrincipal P hst.base.principals bundle.ikB <;> simp [StateT.run_pure]

theorem fgPreInitiate_before_c0 {S : Setup} (targetIdx : ℕ) (P : Primitives)
    (sid : SessionId S) (u : Fin S.N_id) (bundle : PreKeyBundleInput)
    (hst : KeyIndFgCutoffState S) :
    (∀ uSk, (liftFgBase (fgPreInitiate false targetIdx (some uSk) S P sid u bundle)).run hst =
      (liftFgBase (fgPreInitiate false targetIdx none S P sid u bundle)).run hst) ∨
    ∃ (fPre : Bytes → Bytes → ProbComp (KeyIndResponse × KeyIndFgCutoffState S)),
      (∀ uSk, (liftFgBase (fgPreInitiate false targetIdx (some uSk) S P sid u bundle)).run hst =
        (sampleCoins32 >>= fPre uSk)) ∧
      (∀ obs : KeyIndResponse × KeyIndFgCutoffState S → ProbComp Bool,
        𝒟[(liftFgBase (fgPreInitiate false targetIdx none S P sid u bundle)).run hst >>= obs] =
        𝒟[sampleCoins32 >>= fun kemCoins => sampleScalar32 >>= fun uSk => fPre uSk kemCoins >>=
          obs]) ∧
      (∀ kemCoins,
        (∃ x0, ∀ uSk, fPre uSk kemCoins = pure x0) ∨
        (∀ uSk, ∀ x ∈ support (fPre uSk kemCoins), hasFiredSess S targetIdx x.2)) := by
  by_cases hSlot : (initSessionSlotIdx sid == targetIdx) = true
  · cases hSid : hst.base.sessions.any (fun e => e.sid == sid)
    · cases hP : hst.base.principals.find? (fun (idx, _) => idx == u.val) with
      | none =>
        refine Or.inl (fun uSk => ?_)
        unfold liftFgBase fgPreInitiate
        simp only [StateT_run_mk, StateT.run_bind, StateT.run_get, pure_bind, hSid, hP,
          Bool.false_eq_true, ↓reduceIte]
      | some p =>
        rcases p with ⟨idx0, uEntry⟩
        by_cases hKosk : koskBundleOk P hst.base.principals hst.base.spkBundles hst.base.opkEntries
          hst.base.advKeys bundle = true
        · refine Or.inr ⟨fgPreInitiateAfterCoins P sid uEntry bundle hst,
            fun uSk => ?_, fun obs => ?_, fun kemCoins => ?_⟩
          · rw [fgPreInitiate_run_eq_afterCoins targetIdx (some uSk) P sid u bundle hst hSid uEntry
            (Or.inr ⟨idx0, hP⟩) hKosk]
            simp [hSlot]
          · rw [fgPreInitiate_run_eq_afterCoins targetIdx none P sid u bundle hst hSid uEntry
            (Or.inr ⟨idx0, hP⟩) hKosk]
            simp only [bind_assoc]
            exact OracleComp.evalDist_bind_bind_swap sampleScalar32 sampleCoins32 _
          · unfold fgPreInitiateAfterCoins
            dsimp only
            by_cases hSig : (!(P.sigVerify (resolveSigPk P hst.base.principals bundle.ikB)
                  (encodeEC bundle.spkB) bundle.spkSig &&
                P.sigVerify (resolveSigPk P hst.base.principals bundle.ikB)
                  (encodeKEM bundle.pqspkB) bundle.pqspkSig)) = true
            · refine Or.inl ⟨(.noneResp, hst), fun uSk => ?_⟩
              simp [hSig]
            · simp only [hSig, Bool.false_eq_true, ↓reduceIte]
              cases P.kemEncaps bundle.pqspkB kemCoins with
              | none => exact Or.inl ⟨(.noneResp, hst), fun _ => rfl⟩
              | some sc =>
                rcases sc with ⟨ss, kemCt⟩
                dsimp only
                refine Or.inr (fun uSk x hx => ?_)
                simp only [MonadAttach.mem_support_bind, support_pure, Set.mem_singleton_iff] at hx
                rcases hx with ⟨⟨drKeyReal, roCache'⟩, _, drKeyRand, _, hEq⟩
                have hB := (Prod.mk.inj hEq).2
                unfold hasFiredSess; rw [hB]; simp [hSlot]
        · have hKoskF : koskBundleOk P hst.base.principals hst.base.spkBundles hst.base.opkEntries
            hst.base.advKeys bundle = false :=
            Bool.eq_false_iff.mpr hKosk
          refine Or.inl (fun uSk => ?_)
          unfold liftFgBase fgPreInitiate
          simp only [StateT_run_mk, StateT.run_bind, StateT.run_get, pure_bind, hSid, hP, hKoskF,
            Bool.not_false, Bool.false_eq_true, ↓reduceIte]
    · refine Or.inl (fun uSk => ?_)
      unfold liftFgBase fgPreInitiate
      simp only [StateT_run_mk, StateT.run_bind, StateT.run_get, pure_bind, hSid, ↓reduceIte]
  · refine Or.inl (fun uSk => ?_)
    have hSlotF : (!false && (initSessionSlotIdx sid == targetIdx)) = false := by simp [hSlot]
    unfold fgPreInitiate
    simp only [hSlotF, Bool.false_eq_true, ↓reduceIte]


end Proofs.SignalPqxdh.Security.FgGapDh
