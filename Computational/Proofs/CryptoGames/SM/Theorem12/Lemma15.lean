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
# Proof of Lemma 15

**Checked by Lean.** Proves `PrivL15.lemma15_proof` (ACD19 §5.3.3, Lemma 15): in the ideal
PRF-PRNG world (`b = true`), the privacy bias of `redPRNGPriv` is at most
`FSAEAD.advantage fs redFSPriv + 2 * FSAEAD.advantage fs redFSPrivCoin` (`DEV-SM25`).
-/

@[expose] public section

open OracleComp OracleSpec ENNReal MeasureTheory CryptoGames.Lazy

namespace CryptoGames.SM.Construction.PrivL15

open CryptoGames.SM.Construction Engine

/-! ### `CloseBy` and post-`win` helpers -/

section Helpers

theorem DEq.of_evalDist_eq {α : Type} [MeasurableSpace α] [DiscreteMeasurableSpace α]
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

theorem evalDist_uniformBool_beq_left (b : Bool) :
    𝒟[($ᵗ Bool : ProbComp Bool) >>= fun x => pure (b == x)] =
      𝒟[($ᵗ Bool : ProbComp Bool)] := by
  have heq : (fun x : Bool => (pure (b == x) : ProbComp Bool)) =
      (fun x : Bool => (pure (x == b) : ProbComp Bool)) := by
    funext x; simp [Bool.beq_comm]
  rw [heq]
  exact evalDist_uniformBool_beq b

theorem boolBias_uniformBool : 𝒟[($ᵗ Bool : ProbComp Bool)].boolBias = 0 := by
  rw [Measure.boolBias_eq_two_mul_absDiff_half_of_isProbabilityMeasure]
  simp

def CloseBy (cR cM cL : ProbComp Bool) : Prop :=
  ∀ s : Set Bool,
    𝒟[cR] s ≤ 𝒟[cM] s + 𝒟[cL] {true} ∧
    𝒟[cM] s ≤ 𝒟[cR] s + 𝒟[cL] {true}

theorem closeBy_of_eq {cR cM cL : ProbComp Bool} (h : cR = cM) :
    CloseBy cR cM cL := by
  intro s
  rw [h]
  exact ⟨le_self_add, le_self_add⟩

theorem closeBy_of_evalDist_eq_one {cR cM cL : ProbComp Bool}
    (h : 𝒟[cL] {true} = 1) :
    CloseBy cR cM cL := by
  intro s
  rw [h]
  exact ⟨(prob_le_one).trans le_add_self, (prob_le_one).trans le_add_self⟩

theorem closeBy_bind {α : Type}
    (oa : ProbComp α) {fR fM fL : α → ProbComp Bool}
    (h : ∀ a, CloseBy (fR a) (fM a) (fL a)) :
    CloseBy (oa >>= fR) (oa >>= fM) (oa >>= fL) := by
  induction oa using OracleComp.inductionOn with
  | pure a =>
    simp only [pure_bind]
    exact h a
  | query_bind t k ih =>
    intro s
    have h1 : ∀ g : unifSpec.Range t → ProbComp Bool, ∀ ev : Set Bool,
        𝒟[(liftM (OracleSpec.query t) : ProbComp _) >>= g] ev =
          ∫⁻ u, 𝒟[g u] ev ∂𝒟[(liftM (OracleSpec.query t) : ProbComp _)] := by
      intro g ev
      rw [evalDist_bind_of_discrete, Measure.bind_apply MeasurableSet.of_discrete
        Measurable.of_discrete.aemeasurable]
    simp only [bind_assoc]
    rw [h1 (fun u => k u >>= fR) s, h1 (fun u => k u >>= fM) s, h1 (fun u => k u >>= fL) {true}]
    rw [← lintegral_add_left Measurable.of_discrete,
        ← lintegral_add_left Measurable.of_discrete]
    exact ⟨lintegral_mono fun u => (ih u s).1, lintegral_mono fun u => (ih u s).2⟩

theorem boolDist_le_of_closeBy {cR cM cL : ProbComp Bool} (h : CloseBy cR cM cL) :
    𝒟[cR].boolDist 𝒟[cM] ≤ 𝒟[cL] {true} := by
  rw [Measure.boolDist]
  exact ENNReal.absDiff_le_iff.mpr (h {true})

end Helpers

/-! ### `redFSPrivCoin` advantage -/

section FSAEADWin

variable {K SS RS AD M E : Type} [DecidableEq AD] [DecidableEq M] [DecidableEq E]
  (fs : FSAEADScheme K SS RS AD M E)

abbrev fsFullImpl :
    QueryImpl (unifSpec + FSAEAD.spec SS RS AD M E)
      (StateT (FSAEAD.State SS RS AD M E) ProbComp) :=
  (QueryImpl.ofLift unifSpec ProbComp).liftTarget
      (StateT (FSAEAD.State SS RS AD M E) ProbComp) + FSAEAD.oracleImpl fs

private theorem mem_support_liftM_run {α σ : Type} (c : ProbComp α) (s : σ) (z : α × σ)
    (hz : z ∈ support ((liftM c : StateT σ ProbComp α).run s)) :
    z.1 ∈ support c ∧ z.2 = s := by
  rw [StateT.run_monadLift, MonadAttach.mem_support_bind] at hz
  rcases hz with ⟨a, ha, hz⟩
  rw [support_pure, Set.mem_singleton_iff] at hz
  subst hz
  exact ⟨ha, rfl⟩

theorem win_of_mem_support_fsFullImpl
    (q : (unifSpec + FSAEAD.spec SS RS AD M E).Domain)
    {st : FSAEAD.State SS RS AD M E} (hwin : st.win = true)
    {z : (unifSpec + FSAEAD.spec SS RS AD M E).Range q × FSAEAD.State SS RS AD M E}
    (hz : z ∈ support ((fsFullImpl fs q).run st)) :
    z.2.win = true := by
  rcases q with n | (((((q | q) | _) | _) | q) | q)
  · rcases mem_support_liftM_run _ st z hz with ⟨_, rfl⟩
    exact hwin
  · change z ∈ support ((FSAEAD.transmitImpl fs q).run st) at hz
    simp only [FSAEAD.transmitImpl, FSAEAD.transmit, StateT.run_modifyGet, support_pure,
      Set.mem_singleton_iff] at hz
    split at hz <;> (subst hz; exact hwin)
  · change z ∈ support ((FSAEAD.challengeImpl fs q).run st) at hz
    simp only [FSAEAD.challengeImpl, FSAEAD.challenge, StateT.run_modifyGet, support_pure,
      Set.mem_singleton_iff] at hz
    split at hz <;> (subst hz; exact hwin)
  · change z ∈ support ((FSAEAD.corruptSenderImpl ()).run st) at hz
    simp only [FSAEAD.corruptSenderImpl, FSAEAD.corruptSender, StateT.run_modifyGet, support_pure,
      Set.mem_singleton_iff] at hz
    split at hz <;> (subst hz; exact hwin)
  · change z ∈ support ((FSAEAD.corruptReceiverImpl ()).run st) at hz
    simp only [FSAEAD.corruptReceiverImpl, FSAEAD.corruptReceiver, StateT.run_modifyGet,
      support_pure, Set.mem_singleton_iff] at hz
    split at hz <;> (subst hz; exact hwin)
  · change z ∈ support ((FSAEAD.deliverImpl fs q).run st) at hz
    simp only [FSAEAD.deliverImpl, FSAEAD.deliver, StateT.run_modifyGet, support_pure,
      Set.mem_singleton_iff] at hz
    split at hz
    · subst hz; exact hwin
    · split at hz
      · subst hz; exact hwin
      · split at hz
        · subst hz; simp [hwin]
        · subst hz; simp [FSAEAD.State.removeFromTransit, hwin]
  · change z ∈ support ((FSAEAD.injectImpl fs q).run st) at hz
    simp only [FSAEAD.injectImpl, FSAEAD.inject, StateT.run_modifyGet, support_pure,
      Set.mem_singleton_iff] at hz
    split at hz
    · subst hz; exact hwin
    · split at hz
      · subst hz; exact hwin
      · subst hz; simp [FSAEAD.State.removeFromTransit, hwin]

theorem win_of_mem_support_simulateQ_fsFullImpl {α : Type}
    (oa : FSAEAD.AdversaryComp SS RS AD M E α) :
    ∀ {st : FSAEAD.State SS RS AD M E} {z : α × FSAEAD.State SS RS AD M E},
      st.win = true →
      z ∈ support ((simulateQ (fsFullImpl fs) oa).run st) →
      z.2.win = true := by
  induction oa using OracleComp.inductionOn with
  | pure a =>
    intro st z hwin hz
    simp only [simulateQ_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff] at hz
    subst hz; exact hwin
  | query_bind q k ih =>
    intro st z hwin hz
    simp only [simulateQ_bind, simulateQ_query, OracleQuery.input_query, OracleQuery.cont_query,
      id_map, StateT.run_bind, mem_support_bind_iff] at hz
    rcases hz with ⟨⟨u, st₁⟩, h₁, h₂⟩
    exact ih u (win_of_mem_support_fsFullImpl fs q hwin h₁) h₂

theorem evalDist_simulateQ_fsFullImpl_eq_one_of_win {α : Type}
    (oa : FSAEAD.AdversaryComp SS RS AD M E α)
    (f : α × FSAEAD.State SS RS AD M E → ProbComp Bool)
    (hf : ∀ z : α × FSAEAD.State SS RS AD M E,
      z.2.win = true → 𝒟[f z] = 𝒟[(pure true : ProbComp Bool)])
    {st : FSAEAD.State SS RS AD M E} (hwin : st.win = true) :
    𝒟[(simulateQ (fsFullImpl fs) oa).run st >>= f] {true} = 1 := by
  have heq : 𝒟[(simulateQ (fsFullImpl fs) oa).run st >>= f] = 𝒟[(pure true : ProbComp Bool)] := by
    rw [evalDist_bind_congr_of_support _ _ (fun _ => pure true)]
    · exact OracleComp.evalDist_bind_const _ _
    · intro z hz
      exact hf z (win_of_mem_support_simulateQ_fsFullImpl fs oa hwin hz)
  rw [heq]
  simp

theorem measure_bool_true_add_false (μ : Measure Bool) [IsProbabilityMeasure μ] :
    μ {true} + μ {false} = 1 := by
  have huniv : μ Set.univ = 1 := measure_univ
  have heq : (Set.univ : Set Bool) = {true} ∪ {false} := by
    ext x; cases x <;> simp
  rw [heq, measure_union (by simp) MeasurableSet.of_discrete] at huniv
  exact huniv

theorem boolBias_coin_or_win (X : ProbComp Bool) :
    𝒟[X >>= fun w => if w then pure true else ($ᵗ Bool : ProbComp Bool)].boolBias =
      𝒟[X] {true} := by
  have hcoin : 𝒟[($ᵗ Bool : ProbComp Bool)] {true} = 2⁻¹ := by simp
  have htrue :
      𝒟[X >>= fun w => if w then pure true else ($ᵗ Bool : ProbComp Bool)] {true} =
        2⁻¹ + 2⁻¹ * (𝒟[X] {true}) := by
    rw [evalDist_bind_of_discrete,
      Measure.bind_apply MeasurableSet.of_discrete Measurable.of_discrete.aemeasurable,
      lintegral_fintype, Fintype.sum_bool]
    simp only [↓reduceIte, Bool.false_eq_true, evalDist_pure,
      Measure.dirac_apply' _ MeasurableSet.of_discrete,
      Set.indicator_of_mem (Set.mem_singleton true), Pi.one_apply, one_mul, hcoin]
    have hsum := measure_bool_true_add_false 𝒟[X]
    have h1 : (1 : ℝ≥0∞) = 2⁻¹ + 2⁻¹ := by
      simpa only [one_div] using (ENNReal.add_halves 1).symm
    calc 𝒟[X] {true} + 2⁻¹ * 𝒟[X] {false}
        = (2⁻¹ + 2⁻¹) * 𝒟[X] {true} + 2⁻¹ * 𝒟[X] {false} := by rw [← h1, one_mul]
      _ = 2⁻¹ * (𝒟[X] {true} + 𝒟[X] {false}) + 2⁻¹ * 𝒟[X] {true} := by ring
      _ = 2⁻¹ + 2⁻¹ * 𝒟[X] {true} := by rw [hsum, mul_one]
  rw [Measure.boolBias_eq_two_mul_absDiff_half_of_isProbabilityMeasure, one_div, htrue]
  have hsub : ENNReal.absDiff (2⁻¹ + 2⁻¹ * 𝒟[X] {true}) 2⁻¹ = 2⁻¹ * 𝒟[X] {true} := by
    apply le_antisymm
    · exact ENNReal.absDiff_le_iff.mpr ⟨le_rfl, le_self_add.trans le_self_add⟩
    · exact (ENNReal.add_le_add_iff_left (by norm_num)).mp (ENNReal.absDiff_le_iff.mp le_rfl).1
  rw [hsub, ← mul_assoc, ENNReal.mul_inv_cancel (by norm_num) (by norm_num), one_mul]

theorem evalDist_sampleT_bool_run (st : FSAEAD.State SS RS AD M E) :
    ((simulateQ (fsFullImpl fs) (sampleT Bool)).run st : ProbComp _) =
      (·, st) <$> ($ᵗ Bool : ProbComp Bool) := by
  simp [sampleT, fsFullImpl, QueryImpl.simulateQ_add_liftM_left, simulateQ_liftTarget]

theorem evalDist_coin_or_win (b : Bool) (st : FSAEAD.State SS RS AD M E) :
    𝒟[((simulateQ (fsFullImpl fs) (sampleT Bool)).run st : ProbComp _) >>=
        fun z => pure (b == z.1 || z.2.win)] =
      𝒟[if st.win then (pure true : ProbComp Bool) else ($ᵗ Bool : ProbComp Bool)] := by
  rw [evalDist_sampleT_bool_run, bind_map_left]
  cases hwin : st.win
  · simp only [hwin, Bool.or_false, Bool.false_eq_true, ↓reduceIte]
    exact evalDist_uniformBool_beq_left b
  · simp only [hwin, Bool.or_true, ↓reduceIte]
    exact OracleComp.evalDist_bind_const _ _

theorem advantage_bind_sampleT_bool [SampleableType K] {α : Type}
    (C : FSAEAD.AdversaryComp SS RS AD M E α) :
    FSAEAD.advantage fs
        (show FSAEAD.AdversaryComp SS RS AD M E Bool from C >>= fun _ => sampleT Bool) =
      𝒟[do
        let b ← $ᵗ Bool
        let k ← $ᵗ K
        let (_, st) ← (simulateQ (fsFullImpl fs) C).run (FSAEAD.initState fs k b)
        pure st.win] {true} := by
  unfold FSAEAD.advantage
  rw [← boolBias_coin_or_win]
  congr 1
  refine DEq.evalDist_eq ?_
  unfold FSAEAD.game
  simp only [bind_assoc, pure_bind]
  refine DEq.bind_right _ fun b => DEq.bind_right _ fun k => ?_
  simp only [simulateQ_bind, StateT.run_bind, bind_assoc]
  refine DEq.bind_right _ fun z => DEq.of_evalDist_eq ?_
  exact evalDist_coin_or_win fs b z.2

end FSAEADWin

/-! ### Engine execution helpers -/

section GenericEngine

variable {ι : Type} {tspec : OracleSpec.{0, 0} ι} {OS : Type}
  {Γ T Sig SS RS M E CCoins : Type} {Γv Sv SSv RSv HS : Type}

def outerFull (oimpl : QueryImpl tspec (StateT OS ProbComp)) :
    QueryImpl (unifSpec + tspec) (StateT OS ProbComp) :=
  (QueryImpl.ofLift unifSpec ProbComp).liftTarget (StateT OS ProbComp) + oimpl

def runHM (oimpl : QueryImpl tspec (StateT OS ProbComp)) {α : Type}
    (x : HM tspec HS α) (h : HS) (os : OS) : ProbComp ((α × HS) × OS) :=
  (simulateQ (outerFull oimpl) (x.run h)).run os

def runEM (oimpl : QueryImpl tspec (StateT OS ProbComp)) {α : Type}
    (x : EM tspec Γv T Sv SSv RSv M E HS α)
    (s : EState (VP Γv T Sv SSv RSv) M (Header T × E) HS × OS) :
    ProbComp (α × (EState (VP Γv T Sv SSv RSv) M (Header T × E) HS × OS)) :=
  (fun r => (r.1.1, (r.1.2, r.2))) <$>
    (simulateQ (outerFull oimpl) (x.run s.1)).run s.2

def privOutP [DecidableEq M] {VPt C HS : Type} (Δ : ℕ) (π : Policy) (b b' : Bool)
    (es : EState VPt M C HS) : ProbComp Bool :=
  if !es.abort && lastLeakGuessAdmissible Δ π.tL π.tStar && canon π.tStar es.g == π.tL then pure (b == b')
  else ($ᵗ Bool : ProbComp Bool)

def fsPrivOut [DecidableEq M] {VPt C HS : Type} (Δ : ℕ) (π : Policy) (b b' : Bool)
    (es : EState VPt M C HS) (win : Bool) : ProbComp Bool :=
  if win then pure true else privOutP Δ π b b' es

def evalEng [DecidableEq M] [DecidableEq T] [DecidableEq E] [Inhabited E]
    (oimpl : QueryImpl tspec (StateT OS ProbComp))
    (hk : Hooks tspec HS Γ T Sig SS RS M E CCoins Γv Sv SSv RSv)
    (Δ qep maxSkip : ℕ) (cfg : Config M) (π : Policy) (b : Bool)
    (oa : OracleComp (unifSpec + spec (PartyState Γ T Sig SS RS) M CCoins (Header T × E)) Bool)
    (s : EState (VP Γv T Sv SSv RSv) M (Header T × E) HS × OS) : ProbComp Bool :=
  runEM oimpl (simulateQ (implE hk Δ qep maxSkip cfg π) oa) s >>=
    fun r => privOutP Δ π b r.1 r.2.1

def evalEngM [DecidableEq M] [DecidableEq T] [DecidableEq E] [Inhabited E] {K : Type}
    (fs : FSAEADScheme K SS RS (Header T) M E)
    (hk : Hooks (FSAEAD.spec SS RS (Header T) M E) HS Γ T Sig SS RS M E CCoins Γv Sv SSv RSv)
    (Δ qep maxSkip : ℕ) (cfg : Config M) (π : Policy) (b : Bool)
    (oa : OracleComp (unifSpec + spec (PartyState Γ T Sig SS RS) M CCoins (Header T × E)) Bool)
    (s : EState (VP Γv T Sv SSv RSv) M (Header T × E) HS × FSAEAD.State SS RS (Header T) M E) :
    ProbComp Bool :=
  runEM (FSAEAD.oracleImpl fs) (simulateQ (implE hk Δ qep maxSkip cfg π) oa) s >>=
    fun r => fsPrivOut Δ π b r.1 r.2.1 r.2.2.win

def evalEngL [DecidableEq M] [DecidableEq T] [DecidableEq E] [Inhabited E] {K : Type}
    (fs : FSAEADScheme K SS RS (Header T) M E)
    (hk : Hooks (FSAEAD.spec SS RS (Header T) M E) HS Γ T Sig SS RS M E CCoins Γv Sv SSv RSv)
    (Δ qep maxSkip : ℕ) (cfg : Config M) (π : Policy)
    (oa : OracleComp (unifSpec + spec (PartyState Γ T Sig SS RS) M CCoins (Header T × E)) Bool)
    (s : EState (VP Γv T Sv SSv RSv) M (Header T × E) HS × FSAEAD.State SS RS (Header T) M E) :
    ProbComp Bool :=
  runEM (FSAEAD.oracleImpl fs) (simulateQ (implE hk Δ qep maxSkip cfg π) oa) s >>=
    fun r => pure r.2.2.win

theorem runEM_pure (oimpl : QueryImpl tspec (StateT OS ProbComp)) {α : Type} (a : α)
    (s : EState (VP Γv T Sv SSv RSv) M (Header T × E) HS × OS) :
    runEM oimpl (pure a : EM tspec Γv T Sv SSv RSv M E HS α) s = pure (a, s) := by
  simp [runEM]

theorem runEM_bind (oimpl : QueryImpl tspec (StateT OS ProbComp)) {α β : Type}
    (x : EM tspec Γv T Sv SSv RSv M E HS α)
    (f : α → EM tspec Γv T Sv SSv RSv M E HS β)
    (s : EState (VP Γv T Sv SSv RSv) M (Header T × E) HS × OS) :
    runEM oimpl (x >>= f) s = runEM oimpl x s >>= fun r => runEM oimpl (f r.1) r.2 := by
  simp [runEM, StateT.run_bind, simulateQ_bind, map_bind, bind_map_left]

theorem runEM_get (oimpl : QueryImpl tspec (StateT OS ProbComp))
    (s : EState (VP Γv T Sv SSv RSv) M (Header T × E) HS × OS) :
    runEM oimpl (get : EM tspec Γv T Sv SSv RSv M E HS _) s = pure (s.1, s) := by
  simp [runEM]

theorem runEM_modify (oimpl : QueryImpl tspec (StateT OS ProbComp))
    (f : EState (VP Γv T Sv SSv RSv) M (Header T × E) HS →
      EState (VP Γv T Sv SSv RSv) M (Header T × E) HS)
    (s : EState (VP Γv T Sv SSv RSv) M (Header T × E) HS × OS) :
    runEM oimpl (modify f : EM tspec Γv T Sv SSv RSv M E HS Unit) s =
      pure ((), (f s.1, s.2)) := by
  simp [runEM]

theorem runEM_abortE (oimpl : QueryImpl tspec (StateT OS ProbComp))
    (s : EState (VP Γv T Sv SSv RSv) M (Header T × E) HS × OS) :
    runEM oimpl (abortE : EM tspec Γv T Sv SSv RSv M E HS Unit) s =
      pure ((), ({ s.1 with abort := true }, s.2)) := by
  simp [abortE, runEM_modify]

theorem runEM_abort_pure (oimpl : QueryImpl tspec (StateT OS ProbComp)) {α : Type} (a : α)
    (s : EState (VP Γv T Sv SSv RSv) M (Header T × E) HS × OS) :
    runEM oimpl (do abortE; pure a) s = pure (a, ({ s.1 with abort := true }, s.2)) := by
  rw [runEM_bind, runEM_abortE, pure_bind, runEM_pure]

theorem simulateQ_outerFull_sampleT (oimpl : QueryImpl tspec (StateT OS ProbComp))
    (α : Type) [SampleableType α] (os : OS) :
    (simulateQ (outerFull oimpl) (sampleT (tspec := tspec) α)).run os =
      (·, os) <$> ($ᵗ α : ProbComp α) := by
  simp [sampleT, outerFull, QueryImpl.simulateQ_add_liftM_left, simulateQ_liftTarget]

theorem simulateQ_outerFull_privOut [DecidableEq M] {VPt C HS : Type}
    (oimpl : QueryImpl tspec (StateT OS ProbComp)) (Δ : ℕ) (π : Policy) (b b' : Bool)
    (es : EState VPt M C HS) (os : OS) :
    Prod.fst <$> (simulateQ (outerFull oimpl) (privOut Δ π b b' es)).run os =
      privOutP Δ π b b' es := by
  unfold privOut privOutP
  split <;> simp [outerFull, QueryImpl.simulateQ_add_liftM_left, simulateQ_liftTarget]

def evalAfterInitL [DecidableEq M] [DecidableEq T] [DecidableEq E] [Inhabited E]
    (oimpl : QueryImpl tspec (StateT OS ProbComp))
    (hk : Hooks tspec HS Γ T Sig SS RS M E CCoins Γv Sv SSv RSv)
    (Δ qep maxSkip : ℕ) (cfg : Config M) (π : Policy) (b : Bool)
    (oa : OracleComp (unifSpec + spec (PartyState Γ T Sig SS RS) M CCoins (Header T × E)) Bool)
    (r : (Option (VP Γv T Sv SSv RSv × VP Γv T Sv SSv RSv) × HS) × OS) : ProbComp Bool :=
  match r.1.1 with
  | none => ($ᵗ Bool : ProbComp Bool)
  | some (vA, vB) =>
    evalEng oimpl hk Δ qep maxSkip cfg π b oa
      ({ g := { st := fun P => match P with | .A => vA | .B => vB, b },
         h := r.1.2 }, r.2)

def evalAfterInitM [DecidableEq M] [DecidableEq T] [DecidableEq E] [Inhabited E] {K : Type}
    (fs : FSAEADScheme K SS RS (Header T) M E)
    (hk : Hooks (FSAEAD.spec SS RS (Header T) M E) HS Γ T Sig SS RS M E CCoins Γv Sv SSv RSv)
    (Δ qep maxSkip : ℕ) (cfg : Config M) (π : Policy) (b b₀ : Bool)
    (oa : OracleComp (unifSpec + spec (PartyState Γ T Sig SS RS) M CCoins (Header T × E)) Bool)
    (r : (Option (VP Γv T Sv SSv RSv × VP Γv T Sv SSv RSv) × HS) ×
      FSAEAD.State SS RS (Header T) M E) : ProbComp Bool :=
  match r.1.1 with
  | none => if r.2.win then pure true else ($ᵗ Bool : ProbComp Bool)
  | some (vA, vB) =>
    evalEngM fs hk Δ qep maxSkip cfg π b oa
      ({ g := { st := fun P => match P with | .A => vA | .B => vB, b := b₀ },
         h := r.1.2 }, r.2)

def evalAfterInitCoin [DecidableEq M] [DecidableEq T] [DecidableEq E] [Inhabited E] {K : Type}
    (fs : FSAEADScheme K SS RS (Header T) M E)
    (hk : Hooks (FSAEAD.spec SS RS (Header T) M E) HS Γ T Sig SS RS M E CCoins Γv Sv SSv RSv)
    (Δ qep maxSkip : ℕ) (cfg : Config M) (π : Policy) (b₀ : Bool)
    (oa : OracleComp (unifSpec + spec (PartyState Γ T Sig SS RS) M CCoins (Header T × E)) Bool)
    (r : (Option (VP Γv T Sv SSv RSv × VP Γv T Sv SSv RSv) × HS) ×
      FSAEAD.State SS RS (Header T) M E) : ProbComp Bool :=
  match r.1.1 with
  | none => pure r.2.win
  | some (vA, vB) =>
    evalEngL fs hk Δ qep maxSkip cfg π oa
      ({ g := { st := fun P => match P with | .A => vA | .B => vB, b := b₀ },
         h := r.1.2 }, r.2)

theorem evalDist_fsPrivOut_step [DecidableEq T] [DecidableEq M] [DecidableEq E] {K VPt C HS : Type}
    (fs : FSAEADScheme K SS RS (Header T) M E)
    (Δ : ℕ) (π : Policy) (b b' : Bool) (es : EState VPt M C HS)
    (st : FSAEAD.State SS RS (Header T) M E) :
    𝒟[((simulateQ (fsFullImpl fs)
          (if privValid Δ π es then pure b' else sampleT Bool)).run st : ProbComp _) >>=
        fun z => pure (b == z.1 || z.2.win)] =
      𝒟[fsPrivOut Δ π b b' es st.win] := by
  by_cases hval : privValid Δ π es = true
  · have hval' : (!es.abort && lastLeakGuessAdmissible Δ π.tL π.tStar && canon π.tStar es.g == π.tL) = true := hval
    simp only [hval, ↓reduceIte, simulateQ_pure, StateT.run_pure, pure_bind, fsPrivOut, privOutP, hval']
    cases st.win <;> simp
  · have hval' : ¬(!es.abort && lastLeakGuessAdmissible Δ π.tL π.tStar && canon π.tStar es.g == π.tL) = true := hval
    simp only [hval, fsPrivOut, privOutP, hval']
    exact evalDist_coin_or_win fs b st

theorem evalEng_pure [DecidableEq M] [DecidableEq T] [DecidableEq E] [Inhabited E]
    (oimpl : QueryImpl tspec (StateT OS ProbComp))
    (hk : Hooks tspec HS Γ T Sig SS RS M E CCoins Γv Sv SSv RSv)
    (Δ qep maxSkip : ℕ) (cfg : Config M) (π : Policy) (b b' : Bool)
    (s : EState (VP Γv T Sv SSv RSv) M (Header T × E) HS × OS) :
    evalEng oimpl hk Δ qep maxSkip cfg π b (pure b') s = privOutP Δ π b b' s.1 := by
  simp [evalEng, runEM_pure]

theorem evalEngM_pure [DecidableEq M] [DecidableEq T] [DecidableEq E] [Inhabited E] {K : Type}
    (fs : FSAEADScheme K SS RS (Header T) M E)
    (hk : Hooks (FSAEAD.spec SS RS (Header T) M E) HS Γ T Sig SS RS M E CCoins Γv Sv SSv RSv)
    (Δ qep maxSkip : ℕ) (cfg : Config M) (π : Policy) (b b' : Bool)
    (s : EState (VP Γv T Sv SSv RSv) M (Header T × E) HS × FSAEAD.State SS RS (Header T) M E) :
    evalEngM fs hk Δ qep maxSkip cfg π b (pure b') s = fsPrivOut Δ π b b' s.1 s.2.win := by
  simp [evalEngM, runEM_pure]

theorem evalEng_query_bind [DecidableEq M] [DecidableEq T] [DecidableEq E] [Inhabited E]
    (oimpl : QueryImpl tspec (StateT OS ProbComp))
    (hk : Hooks tspec HS Γ T Sig SS RS M E CCoins Γv Sv SSv RSv)
    (Δ qep maxSkip : ℕ) (cfg : Config M) (π : Policy) (b : Bool)
    (q : (unifSpec + spec (PartyState Γ T Sig SS RS) M CCoins (Header T × E)).Domain)
    (k : (unifSpec + spec (PartyState Γ T Sig SS RS) M CCoins (Header T × E)).Range q →
      OracleComp (unifSpec + spec (PartyState Γ T Sig SS RS) M CCoins (Header T × E)) Bool)
    (s : EState (VP Γv T Sv SSv RSv) M (Header T × E) HS × OS) :
    evalEng oimpl hk Δ qep maxSkip cfg π b (query q >>= k) s =
      runEM oimpl (implE hk Δ qep maxSkip cfg π q) s >>=
        fun r => evalEng oimpl hk Δ qep maxSkip cfg π b (k r.1) r.2 := by
  simp [evalEng, simulateQ_bind, simulateQ_query, runEM_bind]

theorem evalEngM_query_bind [DecidableEq M] [DecidableEq T] [DecidableEq E] [Inhabited E]
    {K : Type} (fs : FSAEADScheme K SS RS (Header T) M E)
    (hk : Hooks (FSAEAD.spec SS RS (Header T) M E) HS Γ T Sig SS RS M E CCoins Γv Sv SSv RSv)
    (Δ qep maxSkip : ℕ) (cfg : Config M) (π : Policy) (b : Bool)
    (q : (unifSpec + spec (PartyState Γ T Sig SS RS) M CCoins (Header T × E)).Domain)
    (k : (unifSpec + spec (PartyState Γ T Sig SS RS) M CCoins (Header T × E)).Range q →
      OracleComp (unifSpec + spec (PartyState Γ T Sig SS RS) M CCoins (Header T × E)) Bool)
    (s : EState (VP Γv T Sv SSv RSv) M (Header T × E) HS × FSAEAD.State SS RS (Header T) M E) :
    evalEngM fs hk Δ qep maxSkip cfg π b (query q >>= k) s =
      runEM (FSAEAD.oracleImpl fs) (implE hk Δ qep maxSkip cfg π q) s >>=
        fun r => evalEngM fs hk Δ qep maxSkip cfg π b (k r.1) r.2 := by
  simp [evalEngM, simulateQ_bind, simulateQ_query, runEM_bind]

theorem evalEngL_query_bind [DecidableEq M] [DecidableEq T] [DecidableEq E] [Inhabited E]
    {K : Type} (fs : FSAEADScheme K SS RS (Header T) M E)
    (hk : Hooks (FSAEAD.spec SS RS (Header T) M E) HS Γ T Sig SS RS M E CCoins Γv Sv SSv RSv)
    (Δ qep maxSkip : ℕ) (cfg : Config M) (π : Policy)
    (q : (unifSpec + spec (PartyState Γ T Sig SS RS) M CCoins (Header T × E)).Domain)
    (k : (unifSpec + spec (PartyState Γ T Sig SS RS) M CCoins (Header T × E)).Range q →
      OracleComp (unifSpec + spec (PartyState Γ T Sig SS RS) M CCoins (Header T × E)) Bool)
    (s : EState (VP Γv T Sv SSv RSv) M (Header T × E) HS × FSAEAD.State SS RS (Header T) M E) :
    evalEngL fs hk Δ qep maxSkip cfg π (query q >>= k) s =
      runEM (FSAEAD.oracleImpl fs) (implE hk Δ qep maxSkip cfg π q) s >>=
        fun r => evalEngL fs hk Δ qep maxSkip cfg π (k r.1) r.2 := by
  simp [evalEngL, simulateQ_bind, simulateQ_query, runEM_bind]

theorem evalEngL_eq_one_of_win [DecidableEq M] [DecidableEq T] [DecidableEq E] [Inhabited E]
    {K : Type} (fs : FSAEADScheme K SS RS (Header T) M E)
    (hk : Hooks (FSAEAD.spec SS RS (Header T) M E) HS Γ T Sig SS RS M E CCoins Γv Sv SSv RSv)
    (Δ qep maxSkip : ℕ) (cfg : Config M) (π : Policy)
    (oa : OracleComp (unifSpec + spec (PartyState Γ T Sig SS RS) M CCoins (Header T × E)) Bool)
    (s : EState (VP Γv T Sv SSv RSv) M (Header T × E) HS × FSAEAD.State SS RS (Header T) M E)
    (hwin : s.2.win = true) :
    𝒟[evalEngL fs hk Δ qep maxSkip cfg π oa s] {true} = 1 := by
  unfold evalEngL runEM
  rw [bind_map_left]
  exact evalDist_simulateQ_fsFullImpl_eq_one_of_win fs _ _
    (fun z hz => by simp [hz]) hwin

theorem evalEng_invalid [DecidableEq M] [DecidableEq T] [DecidableEq E] [Inhabited E]
    (oimpl : QueryImpl tspec (StateT OS ProbComp))
    (hk : Hooks tspec HS Γ T Sig SS RS M E CCoins Γv Sv SSv RSv)
    (Δ qep maxSkip : ℕ) (cfg : Config M) (π : Policy) (b : Bool)
    (hinv : lastLeakGuessAdmissible Δ π.tL π.tStar = false)
    (oa : OracleComp (unifSpec + spec (PartyState Γ T Sig SS RS) M CCoins (Header T × E)) Bool)
    (s : EState (VP Γv T Sv SSv RSv) M (Header T × E) HS × OS) :
    𝒟[evalEng oimpl hk Δ qep maxSkip cfg π b oa s] = 𝒟[($ᵗ Bool : ProbComp Bool)] := by
  unfold evalEng
  have hpriv : ∀ r : Bool × (EState (VP Γv T Sv SSv RSv) M (Header T × E) HS × OS),
      privOutP Δ π b r.1 r.2.1 = ($ᵗ Bool : ProbComp Bool) := by
    intro r
    simp [privOutP, hinv]
  simp only [hpriv]
  exact OracleComp.evalDist_bind_const _ _

end GenericEngine

/-! ### Eager `PRFPRNG` key slot -/

section EagerPRNG

variable {KR Sig I K : Type}

/-- A 3-state slot for pre-sampling the first uniform output of `chall-prng` or `chall-prf`. -/
inductive KeySlot (K : Type) where
  | unknown : KeySlot K
  | ready : K → KeySlot K
  | done : KeySlot K

def fillKey [SampleableType K] (_ : PRFPRNG.GameState Sig I K) :
    KeySlot K → ProbComp (KeySlot K)
  | .unknown => KeySlot.ready <$> ($ᵗ K)
  | sl => pure sl

def consumeKey [SampleableType K] : KeySlot K → ProbComp (K × KeySlot K)
  | .unknown => (·, .done) <$> ($ᵗ K)
  | .ready k => pure (k, .done)
  | .done => (·, .done) <$> ($ᵗ K)

abbrev EagerState (Sig I K : Type) := PRFPRNG.GameState Sig I K × KeySlot K
abbrev EagerM (Sig I K : Type) := StateT (EagerState Sig I K) ProbComp

def liftPG {α : Type} (x : StateT (PRFPRNG.GameState Sig I K) ProbComp α) : EagerM Sig I K α :=
  StateT.mk fun s => (fun r => (r.1, (r.2, s.2))) <$> x.run s.1

def drawKey [SampleableType K] : EagerM Sig I K K :=
  StateT.mk fun s => (fun r => (r.1, (s.1, r.2))) <$> consumeKey s.2

theorem fillKey_idem [SampleableType K] : Idem (fillKey (Sig := Sig) (I := I) (K := K)) := by
  intro _ sl
  cases sl <;>
    simp only [fillKey, map_eq_bind_pure_comp, bind_assoc, Function.comp_apply, pure_bind] <;>
    exact DEq.refl _

theorem fillKey_idem_bind [SampleableType K] {β : Type}
    (g : PRFPRNG.GameState Sig I K) (sl : KeySlot K)
    (k : KeySlot K → ProbComp β) :
    DEq (fillKey g sl >>= fun x => fillKey g x >>= k) (fillKey g sl >>= k) := by
  have := DEq.bind_left (fillKey_idem g sl) k
  simpa only [bind_assoc] using this

theorem comm_liftPG [SampleableType K] {α : Type}
    (x : StateT (PRFPRNG.GameState Sig I K) ProbComp α) :
    Comm (fillKey (Sig := Sig) (I := I) (K := K)) (liftPG x) := by
  rintro ⟨g, sl⟩
  have hfg : ∀ g' : PRFPRNG.GameState Sig I K, fillKey g' = fillKey g := fun _ => rfl
  simp only [fillSt, fillOut, liftPG, StateT.run_mk, map_eq_bind_pure_comp, bind_assoc,
    Function.comp_apply, pure_bind, hfg]
  refine (DEq.swap _ _ _).trans ?_
  exact DEq.bind_right _ fun r => fillKey_idem_bind g sl _

theorem comm_drawKey [SampleableType K] :
    Comm (fillKey (Sig := Sig) (I := I) (K := K)) drawKey := by
  rintro ⟨g, sl⟩
  cases sl <;>
    simp only [fillSt, fillOut, fillKey, drawKey, consumeKey, StateT.run_mk,
      map_eq_bind_pure_comp, bind_assoc, Function.comp_apply, pure_bind] <;>
    exact DEq.refl _

def NonReady : KeySlot K → Prop
  | .ready _ => False
  | _ => True

theorem consumeKey_of_nonReady [SampleableType K] {sl : KeySlot K} (h : NonReady sl) :
    consumeKey sl = (·, .done) <$> ($ᵗ K) := by
  cases sl
  · rfl
  · cases h
  · rfl

def StepNR {α : Type} (m₁ : EagerM Sig I K α)
    (m₂ : StateT (PRFPRNG.GameState Sig I K) ProbComp α) : Prop :=
  ∀ g sl, NonReady sl →
    Prod.map id Prod.fst <$> m₁.run (g, sl) = m₂.run g ∧
    ∀ z ∈ support (m₁.run (g, sl)), NonReady z.2.2

theorem stepNR_pure {α : Type} (a : α) :
    StepNR (Sig := Sig) (I := I) (K := K) (Pure.pure a) (Pure.pure a) := by
  intro g sl hsl
  simp [hsl]

theorem stepNR_bind {α β : Type} {x₁ : EagerM Sig I K α}
    {x₂ : StateT (PRFPRNG.GameState Sig I K) ProbComp α}
    {f₁ : α → EagerM Sig I K β} {f₂ : α → StateT (PRFPRNG.GameState Sig I K) ProbComp β}
    (hx : StepNR x₁ x₂) (hf : ∀ a, StepNR (f₁ a) (f₂ a)) :
    StepNR (x₁ >>= f₁) (x₂ >>= f₂) := by
  intro g sl hsl
  obtain ⟨h1, h2⟩ := hx g sl hsl
  refine ⟨?_, ?_⟩
  · simp only [StateT.run_bind, map_bind]
    rw [← h1, bind_map_left]
    exact bind_congr_of_forall_mem_support _ fun z hz => (hf z.1 z.2.1 z.2.2 (h2 z hz)).1
  · intro z hz
    simp only [StateT.run_bind, mem_support_bind_iff] at hz
    rcases hz with ⟨w, hw, hz⟩
    exact (hf w.1 w.2.1 w.2.2 (h2 w hw)).2 z hz

theorem stepNR_liftPG {α : Type} (x : StateT (PRFPRNG.GameState Sig I K) ProbComp α) :
    StepNR (liftPG x) x := by
  intro g sl hsl
  refine ⟨by simp [liftPG], ?_⟩
  intro z hz
  simp only [liftPG, StateT.run_mk, support_map, Set.mem_image] at hz
  rcases hz with ⟨_, _, rfl⟩
  exact hsl

theorem stepNR_drawKey [SampleableType K] :
    StepNR (Sig := Sig) (I := I) (K := K) drawKey
      (liftM ($ᵗ K : ProbComp K)) := by
  intro g sl hsl
  have hc := consumeKey_of_nonReady hsl
  refine ⟨by simp [drawKey, hc, StateT.run_monadLift, map_eq_bind_pure_comp], ?_⟩
  intro z hz
  simp only [drawKey, hc, StateT.run_mk, support_map, Set.mem_image] at hz
  rcases hz with ⟨_, ⟨_, _, rfl⟩, rfl⟩
  trivial

variable [DecidableEq I] [SampleableType I] [SampleableType K]
  (prng : PRFPRNG KR Sig I K)

def eagerProcess : QueryImpl (Option I →ₒ Option K) (EagerM Sig I K) := fun inp =>
  liftPG (PRFPRNG.processImpl prng inp)

def eagerChallPrng : QueryImpl (Option I →ₒ Option K) (EagerM Sig I K) := fun inp => do
  let s ← liftPG get
  let (inp', fresh) ← liftPG (PRFPRNG.samIfNec inp : ProbComp (I × Bool))
  if (s.corr && !fresh) || s.prf then return none
  let (σ', R) := prng.up s.σ inp'
  liftPG (set { s with σ := σ', corr := false, prng := true })
  if s.b then
    let R' ← drawKey
    return some R'
  else
    return some R

def eagerChallPrf : QueryImpl (I →ₒ Option (Sig × K)) (EagerM Sig I K) := fun inp => do
  let s ← liftPG get
  if s.corr || s.prng then return none
  let (σ', R) := prng.up s.σ inp
  liftPG (set { s with prf := true })
  if s.b then
    match s.table.lookup inp with
    | some R' => return some (σ', R')
    | none =>
      let R' ← drawKey
      liftPG (modify fun s => { s with table := (inp, R') :: s.table })
      return some (σ', R')
  else
    return some (σ', R)

def eagerCorr : QueryImpl (Unit →ₒ Option Sig) (EagerM Sig I K) := fun u =>
  liftPG (PRFPRNG.corrImpl u)

def eagerOracleImpl : QueryImpl (PRFPRNG.spec Sig I K) (EagerM Sig I K) :=
  eagerProcess prng + eagerChallPrng prng + eagerChallPrf prng
    + (eagerCorr : QueryImpl _ (EagerM Sig I K))

theorem comm_eagerOracleImpl (q : (unifSpec + PRFPRNG.spec Sig I K).Domain) :
    Comm (fillKey (Sig := Sig) (I := I) (K := K)) (outerFull (eagerOracleImpl prng) q) := by
  rcases q with n | (((inp | inp) | inp) | _)
  · change Comm fillKey (liftPG (query (spec := unifSpec) n))
    exact comm_liftPG _
  · exact comm_liftPG _
  · change Comm fillKey (eagerChallPrng prng inp)
    unfold eagerChallPrng
    refine Comm.bind (comm_liftPG _) fun s => ?_
    refine Comm.bind (comm_liftPG _) fun ⟨inp', fresh⟩ => ?_
    by_cases h1 : ((s.corr && !fresh) || s.prf) = true
    · simp only [h1, ↓reduceIte]
      exact Comm.pure fillKey_idem _
    · simp only [h1, Bool.false_eq_true, ↓reduceIte]
      refine Comm.bind (comm_liftPG _) fun _ => ?_
      by_cases hb : s.b = true
      · simp only [hb, ↓reduceIte]
        exact Comm.bind comm_drawKey fun _ => Comm.pure fillKey_idem _
      · simp only [hb, Bool.false_eq_true, ↓reduceIte]
        exact Comm.pure fillKey_idem _
  · change Comm fillKey (eagerChallPrf prng inp)
    unfold eagerChallPrf
    refine Comm.bind (comm_liftPG _) fun s => ?_
    by_cases h1 : (s.corr || s.prng) = true
    · simp only [h1, ↓reduceIte]
      exact Comm.pure fillKey_idem _
    · simp only [h1, Bool.false_eq_true, ↓reduceIte]
      refine Comm.bind (comm_liftPG _) fun _ => ?_
      by_cases hb : s.b = true
      · simp only [hb, ↓reduceIte]
        cases s.table.lookup inp
        · exact Comm.bind comm_drawKey fun _ =>
            Comm.bind (comm_liftPG _) fun _ => Comm.pure fillKey_idem _
        · exact Comm.pure fillKey_idem _
      · simp only [hb, Bool.false_eq_true, ↓reduceIte]
        exact Comm.pure fillKey_idem _
  · exact comm_liftPG _

theorem eagerOracleImpl_step (q : (unifSpec + PRFPRNG.spec Sig I K).Domain) :
    StepNR (outerFull (eagerOracleImpl prng) q) (outerFull (PRFPRNG.oracleImpl prng) q) := by
  rcases q with n | (((inp | inp) | inp) | _)
  · exact stepNR_liftPG (query (spec := unifSpec) n)
  · exact stepNR_liftPG (PRFPRNG.processImpl prng inp)
  · change StepNR (eagerChallPrng prng inp) (PRFPRNG.challPrngImpl prng inp)
    unfold eagerChallPrng PRFPRNG.challPrngImpl
    refine stepNR_bind (stepNR_liftPG _) fun s => ?_
    refine stepNR_bind (stepNR_liftPG _) fun ⟨inp', fresh⟩ => ?_
    by_cases h1 : ((s.corr && !fresh) || s.prf) = true
    · simp only [h1, ↓reduceIte]
      exact stepNR_pure _
    · simp only [h1, Bool.false_eq_true, ↓reduceIte]
      refine stepNR_bind (stepNR_liftPG _) fun _ => ?_
      by_cases hb : s.b = true
      · simp only [hb, ↓reduceIte]
        exact stepNR_bind stepNR_drawKey fun _ => stepNR_pure _
      · simp only [hb, Bool.false_eq_true, ↓reduceIte]
        exact stepNR_pure _
  · change StepNR (eagerChallPrf prng inp) (PRFPRNG.challPrfImpl prng inp)
    unfold eagerChallPrf PRFPRNG.challPrfImpl
    refine stepNR_bind (stepNR_liftPG _) fun s => ?_
    by_cases h1 : (s.corr || s.prng) = true
    · simp only [h1, ↓reduceIte]
      exact stepNR_pure _
    · simp only [h1, Bool.false_eq_true, ↓reduceIte]
      refine stepNR_bind (stepNR_liftPG _) fun _ => ?_
      by_cases hb : s.b = true
      · simp only [hb, ↓reduceIte]
        cases s.table.lookup inp
        · exact stepNR_bind stepNR_drawKey fun _ =>
            stepNR_bind (stepNR_liftPG _) fun _ => stepNR_pure _
        · exact stepNR_pure _
      · simp only [hb, Bool.false_eq_true, ↓reduceIte]
        exact stepNR_pure _
  · exact stepNR_liftPG (PRFPRNG.corrImpl ())

theorem simulateQ_eagerOracleImpl_nonReady {α : Type}
    (oa : PRFPRNG.AdversaryComp Sig I K α) :
    ∀ (s : EagerState Sig I K), NonReady s.2 →
      Prod.map id Prod.fst <$> (simulateQ (outerFull (eagerOracleImpl prng)) oa).run s =
        (simulateQ (outerFull (PRFPRNG.oracleImpl prng)) oa).run s.1 := by
  induction oa using OracleComp.inductionOn with
  | pure a =>
    intro s _
    simp
  | query_bind q k ih =>
    intro s hs
    obtain ⟨h1, h2⟩ := eagerOracleImpl_step prng q s.1 s.2 hs
    simp only [simulateQ_bind, simulateQ_query, OracleQuery.input_query, OracleQuery.cont_query,
      id_map, StateT.run_bind, map_bind]
    rw [← h1, bind_map_left]
    exact bind_congr_of_forall_mem_support _ fun z hz => ih z.1 z.2 (h2 z hz)

theorem branch_true_eq_eager [SampleableType KR] (B : PRFPRNG.Adversary Sig I K) :
    𝒟[PRFPRNG.branch prng true B] =
      𝒟[do
        let kr ← $ᵗ KR
        let k_fs ← $ᵗ K
        (simulateQ (outerFull (eagerOracleImpl prng)) B).run'
          ({ σ := prng.init kr, b := true }, .ready k_fs)] := by
  refine DEq.evalDist_eq ?_
  unfold PRFPRNG.branch
  refine DEq.bind_right _ fun kr => ?_
  set g₀ : PRFPRNG.GameState Sig I K := { σ := prng.init kr, b := true }
  have hnr : Prod.fst <$> (simulateQ (outerFull (eagerOracleImpl prng)) B).run (g₀, .unknown) =
      (simulateQ (outerFull (PRFPRNG.oracleImpl prng)) B).run' g₀ := by
    change Prod.fst <$> (simulateQ (outerFull (eagerOracleImpl prng)) B).run (g₀, .unknown) =
      Prod.fst <$> (simulateQ (outerFull (PRFPRNG.oracleImpl prng)) B).run g₀
    rw [← simulateQ_eagerOracleImpl_nonReady prng B (g₀, .unknown) trivial]
    simp
  change DEq ((simulateQ (outerFull (PRFPRNG.oracleImpl prng)) B).run' g₀) _
  rw [← hnr]
  have hcomm := Comm.simulateQ fillKey_idem (comm_eagerOracleImpl prng) B (g₀, .unknown)
  have hmap := (map_fillOut (fill := fillKey) (fun a _ => a)
    ((simulateQ (outerFull (eagerOracleImpl prng)) B).run (g₀, .unknown))).symm.trans
    ((DEq.map hcomm.symm Prod.fst).trans
      (map_fillOut (fill := fillKey) (fun a _ => a)
        (fillSt fillKey (g₀, .unknown) >>= (simulateQ (outerFull (eagerOracleImpl prng)) B).run)))
  refine hmap.trans ?_
  simp only [fillSt, fillKey, StateT.run', map_eq_bind_pure_comp, bind_assoc, Function.comp_apply,
    pure_bind]
  exact DEq.refl _

end EagerPRNG

/-! ### Simulation invariant `Inv15` -/

section Invariant

variable {KC Γ CCoins T I : Type} {KR Sig K : Type} {SS RS M E : Type}
  [DecidableEq T] [DecidableEq M] [DecidableEq E] [DecidableEq I] [Inhabited E]
  [SampleableType CCoins] [SampleableType I] [SampleableType K]

theorem Party.sendsIn_eq_senderOf (P : Party) (e : ℕ) :
    P.sendsIn e = true ↔ P = Party.senderOf e := by
  cases P <;> simp [Party.sendsIn, Party.senderOf]

theorem Party.sendsIn_false_iff_receiverOf (P : Party) (e : ℕ) :
    P.sendsIn e = false ↔ P = Party.receiverOf e := by
  unfold Party.sendsIn Party.receiverOf Party.senderOf
  cases P <;> split_ifs <;> simp_all [Party.other]

theorem Party.sendsIn_succ (P : Party) (e : ℕ) :
    P.sendsIn (e + 1) = !P.sendsIn e := by
  cases P <;> simp only [Party.sendsIn]
  · cases h1 : decide ((e + 1) % 2 = 1) <;> cases h2 : decide (e % 2 = 1) <;>
      simp_all <;> omega
  · cases h1 : decide ((e + 1) % 2 = 0) <;> cases h2 : decide (e % 2 = 0) <;>
      simp_all <;> omega

theorem Party.senderOf_ne_receiverOf (e : ℕ) :
    Party.senderOf e ≠ Party.receiverOf e := by
  simp [Party.receiverOf]
  exact (Party.other_ne _).symm

theorem Party.other_receiverOf (e : ℕ) :
    (Party.receiverOf e).other = Party.senderOf e :=
  Party.other_other (Party.senderOf e)

theorem Party.le_max_apply (f : Party → ℕ) (P : Party) :
    f P ≤ max (f .A) (f .B) := by
  cases P
  · exact le_max_left _ _
  · exact le_max_right _ _

theorem Party.eq_senderOf_or_receiverOf (P : Party) (e : ℕ) :
    P = Party.senderOf e ∨ P = Party.receiverOf e := by
  cases h : P.sendsIn e
  · exact Or.inr ((Party.sendsIn_false_iff_receiverOf P e).mp h)
  · exact Or.inl ((Party.sendsIn_eq_senderOf P e).mp h)

theorem find?_filter_of_imp {α : Type} (p q : α → Bool) (l : List α)
    (h : ∀ a ∈ l, q a = true → p a = true) :
    (l.filter p).find? q = l.find? q := by
  induction l with
  | nil => rfl
  | cons a l ih =>
    have ih' := ih fun x hx => h x (List.mem_cons_of_mem a hx)
    by_cases hq : q a = true
    · have hp := h a List.mem_cons_self hq
      simp [List.filter, hp, List.find?, hq]
    · simp only [Bool.not_eq_true] at hq
      cases hp : p a <;> simp [List.filter, hp, List.find?, hq, ih']

theorem healedBy_maxOpt_false_of_false {tL : Option ℕ} {Δ l t : ℕ}
    (h : healedBy tL Δ t = false) :
    healedBy (some (maxOpt tL l)) Δ t = false := by
  cases tL with
  | none => cases h
  | some l₀ =>
    dsimp only [healedBy, maxOpt] at h ⊢
    rw [decide_eq_false_iff_not] at h ⊢
    omega

theorem healedBy_maxOpt_false_of_le {tL : Option ℕ} {Δ l t : ℕ}
    (hl : t ≤ l) (hΔ : 0 < Δ) :
    healedBy (some (maxOpt tL l)) Δ t = false := by
  cases tL <;>
    (dsimp only [healedBy, maxOpt]; rw [decide_eq_false_iff_not]; omega)

theorem canon_eq_of_leaks_eq {St₁ St₂ Msg C₁ C₂ : Type} (t : ℕ)
    (g₁ : GameState St₁ Msg C₁) (g₂ : GameState St₂ Msg C₂)
    (h : g₁.leaks = g₂.leaks) :
    canon t g₁ = canon t g₂ := by
  simp only [canon, h]

def curSS (h : FSState T Sig K I SS RS E) (st : FSAEAD.State SS RS (Header T) M E) : SS :=
  match h.ext with
  | some (ss, _) => ss
  | none => st.senderState

def curRS (h : FSState T Sig K I SS RS E) (st : FSAEAD.State SS RS (Header T) M E) : RS :=
  match h.ext with
  | some (_, rs) => rs
  | none => st.receiverState

abbrev StateL (Γ T Sig SS RS M E K I : Type) :=
  EState (VP Γ T (Option Sig) SS RS) M (Header T × E) (PRNGState T Sig K) × EagerState Sig I K

abbrev StateR (Γ T Sig K I SS RS M E : Type) :=
  EState (VP Γ T Sig (Option SS) (Option RS)) M (Header T × E) (FSState T Sig K I SS RS E) ×
    FSAEAD.State SS RS (Header T) M E

def AbortInv (b : Bool) (sL : StateL Γ T Sig SS RS M E K I)
    (sR : StateR Γ T Sig K I SS RS M E) : Prop :=
  sL.1.abort = true ∧ sR.1.abort = true ∧ sR.2.win = false ∧ sR.2.b = b

/-- Active simulation invariant relating `hooksPRNG` + `eagerOracleImpl` and
`hooksFS` + `FSAEAD`. -/
structure ActiveInv (fs : FSAEADScheme K SS RS (Header T) M E) (Δcka qep : ℕ)
    (tL : Option ℕ) (t : ℕ) (b : Bool)
    (sL : StateL Γ T Sig SS RS M E K I)
    (sR : StateR Γ T Sig K I SS RS M E) : Prop where
  abortL : sL.1.abort = false
  abortR : sR.1.abort = false
  winL : sL.1.g.win = false
  winR : sR.1.g.win = false
  winFS : sR.2.win = false
  bL : sL.1.g.b = b
  bR : sR.1.g.b = false
  bFS : sR.2.b = b
  epoch_eq : sL.1.g.epoch = sR.1.g.epoch
  idx_eq : sL.1.g.idx = sR.1.g.idx
  tL_eq : sL.1.g.tL = sR.1.g.tL
  chall_eq : sL.1.g.chall = sR.1.g.chall
  comp_eq : sL.1.g.comp = sR.1.g.comp
  maxAcc_eq : sL.1.g.maxAcc = sR.1.g.maxAcc
  leaks_eq : sL.1.g.leaks = sR.1.g.leaks
  corrs_eq : sL.1.g.corrs = sR.1.g.corrs
  trans_eq :
    sL.1.g.trans.map (fun r => (r.pos, r.ct)) = sR.1.g.trans.map (fun r => (r.pos, r.ct))
  idL : ∀ P, (sL.1.g.st P).id = P
  idR : ∀ P, (sR.1.g.st P).id = P
  tcurL : ∀ P, (sL.1.g.st P).tcur = sR.1.g.epoch P
  tcurR : ∀ P, (sR.1.g.st P).tcur = sR.1.g.epoch P
  γ_eq : ∀ P, (sL.1.g.st P).γ = (sR.1.g.st P).γ
  Tcur_eq : ∀ P, (sL.1.g.st P).curCkaMsg = (sR.1.g.st P).curCkaMsg
  root_eq : ∀ P, (sL.1.g.st P).root =
    if sR.1.g.epoch P < t ∧ ¬(tL.isSome && decide (sR.1.g.epoch P < healEpoch tL)) then none
    else some (sR.1.g.st P).root
  vS_eq : ∀ P, (sL.1.g.st P).vS = ((sR.1.g.st P).vS).map (·.getD (curSS sR.1.h sR.2))
  vR_eq : ∀ P t', (sL.1.g.st P).vR t' = ((sR.1.g.st P).vR t').map (·.getD (curRS sR.1.h sR.2))
  sender_epoch :
    sR.1.g.epoch (Party.senderOf (max (sR.1.g.epoch .A) (sR.1.g.epoch .B))) =
      max (sR.1.g.epoch .A) (sR.1.g.epoch .B)
  receiver_epoch :
    let epM := max (sR.1.g.epoch .A) (sR.1.g.epoch .B)
    sR.1.g.epoch (Party.receiverOf epM) = epM ∨
      (1 ≤ epM ∧ sR.1.g.epoch (Party.receiverOf epM) + 1 = epM)
  maxEp_le_qep : max (sR.1.g.epoch .A) (sR.1.g.epoch .B) ≤ qep
  tL_le_maxEp : ∀ l₀, sR.1.g.tL = some l₀ → l₀ ≤ max (sR.1.g.epoch .A) (sR.1.g.epoch .B)
  vS_none : ∀ P, (sR.1.g.st P).vS = some none →
    P = Party.senderOf t ∧ t ≤ sR.1.g.epoch P
  vS_sending : ∀ P, P.sendsIn (sR.1.g.epoch P) = true →
    (sR.1.g.epoch P = t → (sR.1.g.st P).vS = some none) ∧
    (sR.1.g.epoch P ≠ t → ∃ ss, (sR.1.g.st P).vS = some (some ss))
  vR_sender : (sR.1.g.st (Party.senderOf t)).vR t = none
  vR_receiver : (sR.1.g.st (Party.receiverOf t)).vR t =
    if t ≤ sR.1.g.epoch (Party.receiverOf t) then some none else none
  vR_other : ∀ P t' x, t' ≠ t → (sR.1.g.st P).vR t' = some x →
    x.isSome = true ∧ P = Party.receiverOf t' ∧ t' ≤ sR.1.g.epoch P
  cache_none : ∀ t', (t' = 0 ∨ max (sR.1.g.epoch .A) (sR.1.g.epoch .B) < t') →
    sL.1.h.cache t' = none ∧ sR.1.h.cache t' = none
  cache_other : ∀ t', t' ≠ t →
    sL.1.h.cache t' = (sR.1.h.cache t').map (fun x =>
      (x.1, if t' < t ∧ ¬(tL.isSome && decide (t' < healEpoch tL)) then none else some x.2.1,
        x.2.2.1))
  cache_other_ext : ∀ t' Tc σc kc ext, t' ≠ t →
    sR.1.h.cache t' = some (Tc, σc, kc, ext) → ext = false
  cache_t_none : sR.1.h.cache t = none → sL.1.h.cache t = none
  cache_t : ∀ Tc σc kc ext,
    sR.1.h.cache t = some (Tc, σc, kc, ext) →
      ext = true ∧ ∃ k₀, sL.1.h.cache t = some (Tc, some σc, k₀) ∧
        (sR.1.g.epoch (Party.receiverOf t) < t →
          sR.2.receiverState = fs.initReceiver k₀ ∧ sR.1.h.ext = none)
  trans_wf : ∀ r ∈ sR.1.g.trans,
    r.pos.epoch = r.ct.1.1 ∧ r.pos.sender = Party.senderOf r.pos.epoch ∧
      r.pos.epoch ≤ max (sR.1.g.epoch .A) (sR.1.g.epoch .B)
  chall_wf : ∀ pos ∈ sR.1.g.chall,
    pos.sender = Party.senderOf pos.epoch ∧
      pos.epoch ≤ max (sR.1.g.epoch .A) (sR.1.g.epoch .B)
  comp_t : ∀ pos ∈ sR.1.g.comp,
    pos.epoch = t → healedBy sR.1.g.tL (2 + Δcka) t = false
  before_t :
    let epM := max (sR.1.g.epoch .A) (sR.1.g.epoch .B)
    epM < t →
      sL.2.1.b = true ∧
      sL.2.1.corr = (tL.isSome && decide (epM < healEpoch tL)) ∧
      sL.2.1.prng = false ∧ sL.2.1.prf = false ∧ sL.2.1.table = [] ∧
      (∀ P, sR.1.g.epoch P = epM → (sR.1.g.st P).root = sL.2.1.σ) ∧
      (∀ Tc σc kc ext, sR.1.h.cache epM = some (Tc, σc, kc, ext) → σc = sL.2.1.σ) ∧
      sR.1.h.table = [] ∧ sR.1.h.sessions = [] ∧ sR.1.h.fsTrans = [] ∧
      sR.1.h.fsCount = 0 ∧ sR.1.h.fsSCorr = false ∧ sR.1.h.ext = none ∧
      ∃ k_fs, sL.2.2 = .ready k_fs ∧ sR.2 = FSAEAD.initState fs k_fs b
  ext_some :
    sR.1.h.ext.isSome = true →
      healedBy sR.1.g.tL (2 + Δcka) t = false ∧
      ∀ r ∈ sR.1.g.trans, r.pos.epoch = t → r.pos ∈ sR.1.g.comp
  ext_none :
    sR.1.h.ext = none →
      sR.2.ended = false ∧
      sR.1.h.fsCount = sR.2.lastSentIdx ∧
      sR.1.h.fsSCorr = sR.2.senderCorruptedAt.isSome ∧
      (sR.1.g.epoch (Party.senderOf t) = t → sR.1.g.idx (Party.senderOf t) = sR.2.lastSentIdx) ∧
      sR.1.h.fsTrans = sR.2.inTransit.map (fun r => (r.idx, r.ad, r.ct)) ∧
      (sR.1.g.trans.filter (fun r => r.pos.epoch == t)).map (fun r => (r.pos.idx, r.ct.1, r.ct.2)) =
        sR.2.inTransit.map (fun r => (r.idx, r.ad, r.ct)) ∧
      (sR.1.g.chall.filter (fun pos => pos.epoch == t)).map Pos.idx = sR.2.challengesInTransit ∧
      (∀ r ∈ sR.2.inTransit, r.idx ≤ sR.2.lastSentIdx) ∧
      (∀ r ∈ sR.1.g.trans, r.pos.epoch = t →
        (r.pos ∈ sR.1.g.comp ↔ sR.2.isCompromised r.pos.idx = true)) ∧
      ((sR.2.senderCorruptedAt.isSome = true → healedBy sR.1.g.tL (2 + Δcka) t = false) ∧
        (∀ j, sR.2.senderCorruptedAt = some j → j ≤ sR.2.lastSentIdx))

/-- Full invariant: either both simulations have aborted, or `ActiveInv` holds. -/
def Inv15 (fs : FSAEADScheme K SS RS (Header T) M E) (Δcka qep : ℕ)
    (tL : Option ℕ) (t : ℕ) (b : Bool)
    (sL : StateL Γ T Sig SS RS M E K I)
    (sR : StateR Γ T Sig K I SS RS M E) : Prop :=
  AbortInv b sL sR ∨ ActiveInv fs Δcka qep tL t b sL sR

abbrev AdvSpec (Γ T Sig SS RS M CCoins E : Type) :=
  unifSpec + spec (PartyState Γ T Sig SS RS) M CCoins (Header T × E)

def CloseByEng (cka : CKAScheme KC Γ CCoins T I) (prng : PRFPRNG KR Sig I K)
    (fs : FSAEADScheme K SS RS (Header T) M E) (Δcka qep : ℕ) (tL : Option ℕ) (t : ℕ) (b : Bool)
    (oa : OracleComp (AdvSpec Γ T Sig SS RS M CCoins E) Bool)
    (sL : StateL Γ T Sig SS RS M E K I) (sR : StateR Γ T Sig K I SS RS M E) : Prop :=
  CloseBy
    (evalEng (eagerOracleImpl prng) (hooksPRNG cka prng fs ⟨false, tL, t⟩)
      (2 + Δcka) qep fs.maxSkip (Config.priv t) ⟨false, tL, t⟩ b oa sL)
    (evalEngM fs (hooksFS cka prng fs Δcka ⟨false, tL, t⟩ 0)
      (2 + Δcka) qep fs.maxSkip (Config.priv t) ⟨false, tL, t⟩ b oa sR)
    (evalEngL fs (hooksFS cka prng fs Δcka ⟨false, tL, t⟩ 0)
      (2 + Δcka) qep fs.maxSkip (Config.priv t) ⟨false, tL, t⟩ oa sR)

theorem closeBy_evalEng_pure (cka : CKAScheme KC Γ CCoins T I) (prng : PRFPRNG KR Sig I K)
    (fs : FSAEADScheme K SS RS (Header T) M E) (Δcka qep : ℕ) (tL : Option ℕ) (t : ℕ) (b : Bool)
    (a : Bool) (sL : StateL Γ T Sig SS RS M E K I) (sR : StateR Γ T Sig K I SS RS M E)
    (hInv : Inv15 fs Δcka qep tL t b sL sR) :
    CloseByEng cka prng fs Δcka qep tL t b (pure a) sL sR := by
  unfold CloseByEng
  rw [evalEng_pure, evalEngM_pure]
  refine closeBy_of_eq ?_
  rcases hInv with ⟨habL, habR, hwinFS, _⟩ | h
  · simp [fsPrivOut, privOutP, habL, habR, hwinFS]
  · simp [fsPrivOut, privOutP, h.abortL, h.abortR, h.winFS, canon_eq_of_leaks_eq _ _ _ h.leaks_eq]

theorem closeBy_of_det_step (cka : CKAScheme KC Γ CCoins T I) (prng : PRFPRNG KR Sig I K)
    (fs : FSAEADScheme K SS RS (Header T) M E) (Δcka qep : ℕ) (tL : Option ℕ) (t : ℕ) (b : Bool)
    (q : (AdvSpec Γ T Sig SS RS M CCoins E).Domain)
    (k : (AdvSpec Γ T Sig SS RS M CCoins E).Range q →
      OracleComp (AdvSpec Γ T Sig SS RS M CCoins E) Bool)
    (sL sL' : StateL Γ T Sig SS RS M E K I) (sR sR' : StateR Γ T Sig K I SS RS M E)
    (ansL ansR : (AdvSpec Γ T Sig SS RS M CCoins E).Range q)
    (hL : runEM (eagerOracleImpl prng)
      (implE (hooksPRNG cka prng fs ⟨false, tL, t⟩) (2 + Δcka) qep fs.maxSkip
        (Config.priv t) ⟨false, tL, t⟩ q) sL = pure (ansL, sL'))
    (hR : runEM (FSAEAD.oracleImpl fs)
      (implE (hooksFS cka prng fs Δcka ⟨false, tL, t⟩ 0) (2 + Δcka) qep fs.maxSkip
        (Config.priv t) ⟨false, tL, t⟩ q) sR = pure (ansR, sR'))
    (ih : ∀ u sL₁ sR₁, Inv15 fs Δcka qep tL t b sL₁ sR₁ →
      CloseByEng cka prng fs Δcka qep tL t b (k u) sL₁ sR₁)
    (hpost : sR'.2.win = true ∨ (ansL = ansR ∧ Inv15 fs Δcka qep tL t b sL' sR')) :
    CloseByEng cka prng fs Δcka qep tL t b (query q >>= k) sL sR := by
  unfold CloseByEng
  rw [evalEng_query_bind, evalEngM_query_bind, evalEngL_query_bind, hL, hR,
    pure_bind, pure_bind, pure_bind]
  rcases hpost with hwin | ⟨rfl, hInv'⟩
  · exact closeBy_of_evalDist_eq_one (evalEngL_eq_one_of_win fs _ _ _ _ _ _ (k ansR) sR' hwin)
  · exact ih ansL sL' sR' hInv'

theorem closeBy_coinsE (cka : CKAScheme KC Γ CCoins T I) (prng : PRFPRNG KR Sig I K)
    (fs : FSAEADScheme K SS RS (Header T) M E) (Δcka qep : ℕ) (tL : Option ℕ) (t : ℕ) (b : Bool)
    (n : unifSpec.Domain)
    (k : (AdvSpec Γ T Sig SS RS M CCoins E).Range (Sum.inl n) →
      OracleComp (AdvSpec Γ T Sig SS RS M CCoins E) Bool)
    (sL : StateL Γ T Sig SS RS M E K I) (sR : StateR Γ T Sig K I SS RS M E)
    (hInv : Inv15 fs Δcka qep tL t b sL sR)
    (ih : ∀ u sL₁ sR₁, Inv15 fs Δcka qep tL t b sL₁ sR₁ →
      CloseByEng cka prng fs Δcka qep tL t b (k u) sL₁ sR₁) :
    CloseByEng cka prng fs Δcka qep tL t b (query (Sum.inl n) >>= k) sL sR := by
  unfold CloseByEng
  rw [evalEng_query_bind, evalEngM_query_bind, evalEngL_query_bind]
  have hL : runEM (eagerOracleImpl prng)
      (implE (hooksPRNG cka prng fs ⟨false, tL, t⟩) (2 + Δcka) qep fs.maxSkip
        (Config.priv t) ⟨false, tL, t⟩ (.inl n)) sL =
      (fun u => (u, sL)) <$> (query (spec := unifSpec) n : ProbComp _) := by
    simp [runEM, implE, coinsE, outerFull, StateT.run_lift, map_eq_bind_pure_comp]
  have hR : runEM (FSAEAD.oracleImpl fs)
      (implE (hooksFS cka prng fs Δcka ⟨false, tL, t⟩ 0) (2 + Δcka) qep fs.maxSkip
        (Config.priv t) ⟨false, tL, t⟩ (.inl n)) sR =
      (fun u => (u, sR)) <$> (query (spec := unifSpec) n : ProbComp _) := by
    simp [runEM, implE, coinsE, outerFull, StateT.run_lift, map_eq_bind_pure_comp]
  rw [hL, hR, bind_map_left, bind_map_left, bind_map_left]
  exact closeBy_bind _ fun u => ih u sL sR hInv

theorem closeBy_sm_of_abortInv (cka : CKAScheme KC Γ CCoins T I) (prng : PRFPRNG KR Sig I K)
    (fs : FSAEADScheme K SS RS (Header T) M E) (Δcka qep : ℕ) (tL : Option ℕ) (t : ℕ) (b : Bool)
    (q : (spec (PartyState Γ T Sig SS RS) M CCoins (Header T × E)).Domain)
    (k : (AdvSpec Γ T Sig SS RS M CCoins E).Range (Sum.inr q) →
      OracleComp (AdvSpec Γ T Sig SS RS M CCoins E) Bool)
    (sL : StateL Γ T Sig SS RS M E K I) (sR : StateR Γ T Sig K I SS RS M E)
    (hab : AbortInv b sL sR)
    (ih : ∀ u sL₁ sR₁, Inv15 fs Δcka qep tL t b sL₁ sR₁ →
      CloseByEng cka prng fs Δcka qep tL t b (k u) sL₁ sR₁) :
    CloseByEng cka prng fs Δcka qep tL t b (query (Sum.inr q) >>= k) sL sR := by
  have ⟨habL, habR, _, _⟩ := hab
  rcases q with ((((q | q) | q) | q) | q) <;>
    refine closeBy_of_det_step cka prng fs Δcka qep tL t b (Sum.inr _) k sL sL sR sR none none
      ?_ ?_ ih (Or.inr ⟨rfl, Or.inl hab⟩) <;>
    simp [runEM, implE, transmitE, challE, deliverE, injectE, corrE, habL, habR]

theorem trans_find?_map_eq {M₁ M₂ C : Type} [DecidableEq C]
    {l₁ : List (Record M₁ C)} {l₂ : List (Record M₂ C)}
    (h : l₁.map (fun r => (r.pos, r.ct)) = l₂.map (fun r => (r.pos, r.ct)))
    (Q : Party) (c : C) :
    (l₁.find? (fun r => r.pos.sender == Q && decide (r.ct = c))).map (fun r => (r.pos, r.ct)) =
      (l₂.find? (fun r => r.pos.sender == Q && decide (r.ct = c))).map (fun r => (r.pos, r.ct)) := by
  have h1 := List.find?_map (p := fun x : Pos × C => x.1.sender == Q && decide (x.2 = c))
    (f := fun r : Record M₁ C => (r.pos, r.ct)) (l := l₁)
  have h2 := List.find?_map (p := fun x : Pos × C => x.1.sender == Q && decide (x.2 = c))
    (f := fun r : Record M₂ C => (r.pos, r.ct)) (l := l₂)
  simp only [Function.comp_def] at h1 h2
  rw [← h1, ← h2, h]

theorem trans_any_eq {M₁ M₂ C : Type}
    {l₁ : List (Record M₁ C)} {l₂ : List (Record M₂ C)}
    (h : l₁.map (fun r => (r.pos, r.ct)) = l₂.map (fun r => (r.pos, r.ct)))
    (p : Pos × C → Bool) :
    l₁.any (fun r => p (r.pos, r.ct)) = l₂.any (fun r => p (r.pos, r.ct)) := by
  have h1 := List.any_map (f := fun r : Record M₁ C => (r.pos, r.ct)) (p := p) (l := l₁)
  have h2 := List.any_map (f := fun r : Record M₂ C => (r.pos, r.ct)) (p := p) (l := l₂)
  simp only [Function.comp_def] at h1 h2
  rw [← h1, ← h2, h]

theorem trans_filter_pos_eq {M₁ M₂ C : Type}
    {l₁ : List (Record M₁ C)} {l₂ : List (Record M₂ C)}
    (h : l₁.map (fun r => (r.pos, r.ct)) = l₂.map (fun r => (r.pos, r.ct)))
    (p : Pos → Bool) :
    (l₁.filter (fun r => p r.pos)).map (fun r => r.pos) =
      (l₂.filter (fun r => p r.pos)).map (fun r => r.pos) := by
  have h1 : (l₁.filter (fun r => p r.pos)).map (fun r => r.pos) =
      ((l₁.map (fun r => (r.pos, r.ct))).filter (fun x => p x.1)).map Prod.fst := by
    rw [List.filter_map, List.map_map]
    rfl
  have h2 : (l₂.filter (fun r => p r.pos)).map (fun r => r.pos) =
      ((l₂.map (fun r => (r.pos, r.ct))).filter (fun x => p x.1)).map Prod.fst := by
    rw [List.filter_map, List.map_map]
    rfl
  rw [h1, h2, h]

theorem trans_delete_map_eq {M₁ M₂ C : Type}
    {l₁ : List (Record M₁ C)} {l₂ : List (Record M₂ C)}
    (h : l₁.map (fun r => (r.pos, r.ct)) = l₂.map (fun r => (r.pos, r.ct)))
    (pos : Pos) :
    (l₁.filter (fun r => r.pos != pos)).map (fun r => (r.pos, r.ct)) =
      (l₂.filter (fun r => r.pos != pos)).map (fun r => (r.pos, r.ct)) := by
  have h1 : (l₁.filter (fun r => r.pos != pos)).map (fun r => (r.pos, r.ct)) =
      (l₁.map (fun r => (r.pos, r.ct))).filter (fun x => x.1 != pos) := by
    rw [List.filter_map]
    rfl
  have h2 : (l₂.filter (fun r => r.pos != pos)).map (fun r => (r.pos, r.ct)) =
      (l₂.map (fun r => (r.pos, r.ct))).filter (fun x => x.1 != pos) := by
    rw [List.filter_map]
    rfl
  rw [h1, h2, h]

omit [DecidableEq T] [DecidableEq M] [DecidableEq E] [DecidableEq I] [Inhabited E]
  [SampleableType I] [SampleableType K] in
theorem ActiveInv.safeCh_eq {fs : FSAEADScheme K SS RS (Header T) M E} {Δcka qep : ℕ}
    {tL : Option ℕ} {t : ℕ} {b : Bool}
    {sL : StateL Γ T Sig SS RS M E K I} {sR : StateR Γ T Sig K I SS RS M E}
    (h : ActiveInv fs Δcka qep tL t b sL sR) (Δ : ℕ) (P : Party) :
    sL.1.g.safeCh Δ P = sR.1.g.safeCh Δ P := by
  simp only [GameState.safeCh, h.tL_eq, h.epoch_eq]

omit [DecidableEq T] [DecidableEq M] [DecidableEq E] [DecidableEq I] [Inhabited E]
  [SampleableType I] [SampleableType K] in
theorem ActiveInv.safeInj_eq {fs : FSAEADScheme K SS RS (Header T) M E} {Δcka qep : ℕ}
    {tL : Option ℕ} {t : ℕ} {b : Bool}
    {sL : StateL Γ T Sig SS RS M E K I} {sR : StateR Γ T Sig K I SS RS M E}
    (h : ActiveInv fs Δcka qep tL t b sL sR) (Δ : ℕ) :
    sL.1.g.safeInj Δ = sR.1.g.safeInj Δ := by
  simp only [GameState.safeInj, h.tL_eq, h.epoch_eq]

omit [DecidableEq T] [DecidableEq M] [DecidableEq E] [DecidableEq I] [Inhabited E]
  [SampleableType I] [SampleableType K] in
theorem ActiveInv.trivial_eq {fs : FSAEADScheme K SS RS (Header T) M E} {Δcka qep : ℕ}
    {tL : Option ℕ} {t : ℕ} {b : Bool}
    {sL : StateL Γ T Sig SS RS M E K I} {sR : StateR Γ T Sig K I SS RS M E}
    (h : ActiveInv fs Δcka qep tL t b sL sR) (Δ : ℕ) (pos : Pos) :
    sL.1.g.trivial Δ pos = sR.1.g.trivial Δ pos := by
  simp only [GameState.trivial, h.comp_eq, h.tL_eq]
  rw [trans_any_eq h.trans_eq (fun x => x.1 == pos)]

omit [DecidableEq T] [DecidableEq M] [DecidableEq E] [DecidableEq I] [Inhabited E]
  [SampleableType I] [SampleableType K] in
theorem ActiveInv.corrAllowed_eq {fs : FSAEADScheme K SS RS (Header T) M E} {Δcka qep : ℕ}
    {tL : Option ℕ} {t : ℕ} {b : Bool}
    {sL : StateL Γ T Sig SS RS M E K I} {sR : StateR Γ T Sig K I SS RS M E}
    (h : ActiveInv fs Δcka qep tL t b sL sR) (P : Party) :
    sL.1.g.corrAllowed P = sR.1.g.corrAllowed P := by
  simp only [GameState.corrAllowed, h.chall_eq, h.comp_eq]
  rw [trans_any_eq h.trans_eq (fun x => x.1.sender == P.other && !(sR.1.g.comp.contains x.1))]

omit [DecidableEq M] [DecidableEq I] [Inhabited E] [SampleableType I] [SampleableType K] in
theorem ActiveInv.inTransit_map_eq {fs : FSAEADScheme K SS RS (Header T) M E} {Δcka qep : ℕ}
    {tL : Option ℕ} {t : ℕ} {b : Bool}
    {sL : StateL Γ T Sig SS RS M E K I} {sR : StateR Γ T Sig K I SS RS M E}
    (h : ActiveInv fs Δcka qep tL t b sL sR) (Q : Party) (c : Header T × E) :
    (sL.1.g.inTransit Q c).map (fun r => (r.pos, r.ct)) =
      (sR.1.g.inTransit Q c).map (fun r => (r.pos, r.ct)) :=
  trans_find?_map_eq h.trans_eq Q c

omit [DecidableEq M] [DecidableEq I] [Inhabited E] [SampleableType I] [SampleableType K] in
theorem ActiveInv.inTransit_isSome_eq {fs : FSAEADScheme K SS RS (Header T) M E} {Δcka qep : ℕ}
    {tL : Option ℕ} {t : ℕ} {b : Bool}
    {sL : StateL Γ T Sig SS RS M E K I} {sR : StateR Γ T Sig K I SS RS M E}
    (h : ActiveInv fs Δcka qep tL t b sL sR) (Q : Party) (c : Header T × E) :
    (sL.1.g.inTransit Q c).isSome = (sR.1.g.inTransit Q c).isSome := by
  have h1 := Option.isSome_map (f := fun r : Record M (Header T × E) => (r.pos, r.ct))
    (x := sL.1.g.inTransit Q c)
  have h2 := Option.isSome_map (f := fun r : Record M (Header T × E) => (r.pos, r.ct))
    (x := sR.1.g.inTransit Q c)
  rw [← h1, ← h2, h.inTransit_map_eq Q c]

omit [DecidableEq T] [DecidableEq M] [DecidableEq E] [DecidableEq I] [Inhabited E]
  [SampleableType I] [SampleableType K] in
theorem ActiveInv.afterCorr_eq {fs : FSAEADScheme K SS RS (Header T) M E} {Δcka qep : ℕ}
    {tL : Option ℕ} {t : ℕ} {b : Bool}
    {sL : StateL Γ T Sig SS RS M E K I} {sR : StateR Γ T Sig K I SS RS M E}
    (h : ActiveInv fs Δcka qep tL t b sL sR) (P : Party) :
    (sL.1.g.afterCorr P).tL = (sR.1.g.afterCorr P).tL ∧
    (sL.1.g.afterCorr P).leaks = (sR.1.g.afterCorr P).leaks ∧
    (sL.1.g.afterCorr P).corrs = (sR.1.g.afterCorr P).corrs ∧
    (sL.1.g.afterCorr P).comp = (sR.1.g.afterCorr P).comp ∧
    (Mode.policy ⟨false, tL, t⟩).leakDoom sL.1.g (sL.1.g.afterCorr P) =
      (Mode.policy ⟨false, tL, t⟩).leakDoom sR.1.g (sR.1.g.afterCorr P) ∧
    (Mode.policy ⟨false, tL, t⟩).corrDoom sL.1.g P =
      (Mode.policy ⟨false, tL, t⟩).corrDoom sR.1.g P := by
  have hcomp : (sL.1.g.afterCorr P).comp = (sR.1.g.afterCorr P).comp := by
    simp only [GameState.afterCorr, GameState.leak, h.comp_eq]
    rw [trans_filter_pos_eq h.trans_eq (fun pos => pos.sender == P.other)]
  refine ⟨?_, ?_, ?_, hcomp, ?_, ?_⟩
  · simp only [GameState.afterCorr, GameState.leak, h.tL_eq, h.epoch_eq]
  · simp only [GameState.afterCorr, GameState.leak, h.tL_eq, h.epoch_eq, h.leaks_eq]
  · simp only [GameState.afterCorr, GameState.leak, h.epoch_eq, h.corrs_eq]
  · simp only [Policy.leakDoom, Mode.policy, GameState.afterCorr, GameState.leak,
      h.tL_eq, h.epoch_eq, h.leaks_eq]
    rfl
  · simp only [Policy.corrDoom, Mode.policy, h.epoch_eq]
    rfl

omit [DecidableEq T] [DecidableEq M] [DecidableEq E] [DecidableEq I] [Inhabited E]
  [SampleableType I] [SampleableType K] in
theorem ActiveInv.root_some_of_not_corr_doom
    {fs : FSAEADScheme K SS RS (Header T) M E} {Δcka qep : ℕ}
    {tL : Option ℕ} {t : ℕ} {b : Bool}
    {sL : StateL Γ T Sig SS RS M E K I} {sR : StateR Γ T Sig K I SS RS M E}
    (h : ActiveInv fs Δcka qep tL t b sL sR) (P : Party)
    (hdoom : ((Mode.policy ⟨false, tL, t⟩).leakDoom sR.1.g (sR.1.g.afterCorr P) ||
      (Mode.policy ⟨false, tL, t⟩).corrDoom sR.1.g P) = false) :
    (sL.1.g.st P).root = some (sR.1.g.st P).root := by
  rw [h.root_eq P, ite_eq_right_iff]
  rintro ⟨hep, hnh⟩
  exfalso
  have hmaxOpt : maxOpt sR.1.g.tL (max (sR.1.g.epoch .A) (sR.1.g.epoch .B)) =
      max (sR.1.g.epoch .A) (sR.1.g.epoch .B) := by
    cases htL : sR.1.g.tL with
    | none => rfl
    | some l₀ =>
      have := h.tL_le_maxEp l₀ htL
      simp only [maxOpt]
      omega
  have hle : sR.1.g.epoch P ≤ max (sR.1.g.epoch .A) (sR.1.g.epoch .B) :=
    Party.le_max_apply sR.1.g.epoch P
  have hlt : ltOpt tL (max (sR.1.g.epoch .A) (sR.1.g.epoch .B)) = true := by
    cases tL with
    | none => rfl
    | some l =>
      have hnh' : ¬(sR.1.g.epoch P < l + 2) := fun hlt =>
        hnh (by simp [healEpoch, hlt])
      simp only [ltOpt, decide_eq_true_eq]
      omega
  rcases lt_or_ge (max (sR.1.g.epoch .A) (sR.1.g.epoch .B)) t with hepM | hepM
  · have hld_true : (Mode.policy ⟨false, tL, t⟩).leakDoom sR.1.g (sR.1.g.afterCorr P) = true := by
      simp [Policy.leakDoom, Mode.policy, GameState.afterCorr, GameState.leak, hmaxOpt,
        hlt, hepM, -max_lt_iff]
    simp [hld_true] at hdoom
  · have hP : P = Party.receiverOf t := by
      rcases Party.eq_senderOf_or_receiverOf P (max (sR.1.g.epoch .A) (sR.1.g.epoch .B)) with
        hPs | hPr
      · have hs := h.sender_epoch
        rw [← hPs] at hs
        omega
      · rcases h.receiver_epoch with hre | ⟨_, hre⟩
        · rw [← hPr] at hre
          omega
        · rw [← hPr] at hre
          have heq : max (sR.1.g.epoch .A) (sR.1.g.epoch .B) = t := by omega
          rw [heq] at hPr
          exact hPr
    have hep' : sR.1.g.epoch (Party.receiverOf t) < t := hP ▸ hep
    have hcd_true : (Mode.policy ⟨false, tL, t⟩).corrDoom sR.1.g P = true := by
      simp [Policy.corrDoom, Mode.policy, hP, hep', hepM, -le_max_iff]
    simp [hcd_true] at hdoom

omit [DecidableEq T] [DecidableEq M] [DecidableEq E] [DecidableEq I] [Inhabited E]
  [SampleableType I] [SampleableType K] in
theorem ActiveInv.corruptReceiver_ok
    {fs : FSAEADScheme K SS RS (Header T) M E} {Δcka qep : ℕ}
    {tL : Option ℕ} {t : ℕ} {b : Bool}
    {sL : StateL Γ T Sig SS RS M E K I} {sR : StateR Γ T Sig K I SS RS M E}
    (h : ActiveInv fs Δcka qep tL t b sL sR)
    (hca : sR.1.g.corrAllowed (Party.receiverOf t) = true)
    (hext : sR.1.h.ext = none) :
    FSAEAD.corruptReceiver sR.2 =
      (some (sR.2.senderState, sR.2.receiverState), { sR.2 with ended := true }) := by
  have hextN := h.ext_none hext
  have hended : sR.2.ended = false := hextN.1
  have hchallEq : (sR.1.g.chall.filter (fun pos => pos.epoch == t)).map Pos.idx =
      sR.2.challengesInTransit := hextN.2.2.2.2.2.2.1
  have htransEq : (sR.1.g.trans.filter (fun r => r.pos.epoch == t)).map
      (fun r => (r.pos.idx, r.ct.1, r.ct.2)) =
      sR.2.inTransit.map (fun r => (r.idx, r.ad, r.ct)) := hextN.2.2.2.2.2.1
  have hcompIff := hextN.2.2.2.2.2.2.2.2.1
  simp only [GameState.corrAllowed, Party.other_receiverOf, Bool.and_eq_true,
    Bool.not_eq_true', List.any_eq_false] at hca
  rcases hca with ⟨hch, htr⟩
  have hchEmpty : sR.2.challengesInTransit = [] := by
    rw [← hchallEq, List.map_eq_nil_iff, List.filter_eq_nil_iff]
    intro pos hpos
    simp only [beq_iff_eq]
    intro hpe
    have hps := (h.chall_wf pos hpos).1
    rw [hpe] at hps
    exact hch pos hpos (by simp [hps])
  have htrComp : sR.2.inTransit.any (fun r => !sR.2.isCompromised r.idx) = false := by
    rw [List.any_eq_false]
    intro r' hr'
    have hmem : (r'.idx, r'.ad, r'.ct) ∈
        sR.2.inTransit.map (fun r => (r.idx, r.ad, r.ct)) :=
      List.mem_map_of_mem hr'
    rw [← htransEq, List.mem_map] at hmem
    rcases hmem with ⟨r, hr, hreq⟩
    rw [List.mem_filter, beq_iff_eq] at hr
    rcases hr with ⟨hr, hrt⟩
    have hidx : r.pos.idx = r'.idx := by injection hreq
    have hps : r.pos.sender = Party.senderOf t := by
      rw [(h.trans_wf r hr).2.1, hrt]
    have hcomp : r.pos ∈ sR.1.g.comp := by
      have h1 := htr r hr
      simp [hps] at h1
      exact h1
    have hisComp : sR.2.isCompromised r'.idx = true := by
      rw [← hidx]
      exact (hcompIff r hr hrt).mp hcomp
    simp [hisComp]
  simp [FSAEAD.corruptReceiver, hended, hchEmpty, htrComp]

theorem afterCorr_mem_comp_iff {St Msg C : Type} {s : GameState St Msg C} {P : Party}
    (hca : s.corrAllowed P = true) (pos : Pos) :
    pos ∈ (s.afterCorr P).comp ↔ pos ∈ s.comp := by
  simp only [GameState.corrAllowed, Bool.and_eq_true, Bool.not_eq_true', List.any_eq_false] at hca
  rcases hca with ⟨_, htr⟩
  simp only [GameState.afterCorr, GameState.leak, List.mem_append, List.mem_map, List.mem_filter,
    beq_iff_eq]
  constructor
  · rintro (⟨r, ⟨hr, hps⟩, rfl⟩ | hmem)
    · have h1 := htr r hr
      simp [hps] at h1
      exact h1
    · exact hmem
  · intro hmem
    exact Or.inr hmem

def realSt (sR : StateR Γ T Sig K I SS RS M E) (P : Party) : PartyState Γ T Sig SS RS :=
  realParty (sR.1.g.st P) (sR.1.g.st P).γ (sR.1.g.st P).root
    (((sR.1.g.st P).vS).map (·.getD (curSS sR.1.h sR.2)))
    (fun t' => ((sR.1.g.st P).vR t').map (·.getD (curRS sR.1.h sR.2)))

omit [DecidableEq M] [DecidableEq E] [DecidableEq I] [Inhabited E]
  [SampleableType I] [SampleableType K] in
theorem ActiveInv.reveal_prng (cka : CKAScheme KC Γ CCoins T I) (prng : PRFPRNG KR Sig I K)
    (fs : FSAEADScheme K SS RS (Header T) M E) {Δcka qep : ℕ}
    {tL : Option ℕ} {t : ℕ} {b : Bool}
    {sL : StateL Γ T Sig SS RS M E K I} {sR : StateR Γ T Sig K I SS RS M E}
    (h : ActiveInv fs Δcka qep tL t b sL sR) (P : Party)
    (hdoom : ((Mode.policy ⟨false, tL, t⟩).leakDoom sR.1.g (sR.1.g.afterCorr P) ||
      (Mode.policy ⟨false, tL, t⟩).corrDoom sR.1.g P) = false) :
    ((hooksPRNG cka prng fs ⟨false, tL, t⟩).reveal sL.1.g P (sL.1.g.st P)).run sL.1.h =
      pure (some (realSt sR P), sL.1.h) := by
  have hroot := h.root_some_of_not_corr_doom P hdoom
  have hst : realParty (sL.1.g.st P) (sL.1.g.st P).γ (sR.1.g.st P).root
      (sL.1.g.st P).vS (sL.1.g.st P).vR = realSt sR P := by
    simp only [realSt, realParty, h.idL P, h.idR P, h.γ_eq P, h.Tcur_eq P,
      h.tcurL P, h.tcurR P, h.vS_eq P]
    congr 1
    funext t'
    exact h.vR_eq P t'
  simp [hooksPRNG, hroot, hst, StateT.run_pure]

omit [DecidableEq T] [DecidableEq M] [DecidableEq E] [DecidableEq I] [Inhabited E]
  [SampleableType I] [SampleableType K] in
theorem ActiveInv.afterCorr_preserves
    {fs : FSAEADScheme K SS RS (Header T) M E} {Δcka qep : ℕ}
    {tL : Option ℕ} {t : ℕ} {b : Bool}
    {sL : StateL Γ T Sig SS RS M E K I} {sR : StateR Γ T Sig K I SS RS M E}
    (h : ActiveInv fs Δcka qep tL t b sL sR) (P : Party)
    (hR' : FSState T Sig K I SS RS E) (osR' : FSAEAD.State SS RS (Header T) M E)
    (hwinFS' : osR'.win = false) (hbFS' : osR'.b = b)
    (hcurSS : curSS hR' osR' = curSS sR.1.h sR.2)
    (hcurRS : curRS hR' osR' = curRS sR.1.h sR.2)
    (hcache : hR'.cache = sR.1.h.cache)
    (hbefore : max (sR.1.g.epoch .A) (sR.1.g.epoch .B) < t → hR' = sR.1.h ∧ osR' = sR.2)
    (hrecv : sR.1.g.epoch (Party.receiverOf t) < t →
      osR'.receiverState = sR.2.receiverState ∧ hR'.ext = sR.1.h.ext)
    (hext_some : hR'.ext.isSome = true →
      healedBy (sR.1.g.afterCorr P).tL (2 + Δcka) t = false ∧
      ∀ r ∈ sR.1.g.trans, r.pos.epoch = t → r.pos ∈ (sR.1.g.afterCorr P).comp)
    (hext_none : hR'.ext = none →
      osR'.ended = false ∧
      hR'.fsCount = osR'.lastSentIdx ∧
      hR'.fsSCorr = osR'.senderCorruptedAt.isSome ∧
      (sR.1.g.epoch (Party.senderOf t) = t → sR.1.g.idx (Party.senderOf t) = osR'.lastSentIdx) ∧
      hR'.fsTrans = osR'.inTransit.map (fun r => (r.idx, r.ad, r.ct)) ∧
      (sR.1.g.trans.filter (fun r => r.pos.epoch == t)).map (fun r => (r.pos.idx, r.ct.1, r.ct.2)) =
        osR'.inTransit.map (fun r => (r.idx, r.ad, r.ct)) ∧
      (sR.1.g.chall.filter (fun pos => pos.epoch == t)).map Pos.idx = osR'.challengesInTransit ∧
      (∀ r ∈ osR'.inTransit, r.idx ≤ osR'.lastSentIdx) ∧
      (∀ r ∈ sR.1.g.trans, r.pos.epoch = t →
        (r.pos ∈ (sR.1.g.afterCorr P).comp ↔ osR'.isCompromised r.pos.idx = true)) ∧
      ((osR'.senderCorruptedAt.isSome = true →
          healedBy (sR.1.g.afterCorr P).tL (2 + Δcka) t = false) ∧
        (∀ j, osR'.senderCorruptedAt = some j → j ≤ osR'.lastSentIdx))) :
    ActiveInv fs Δcka qep tL t b
      ({ sL.1 with g := sL.1.g.afterCorr P }, sL.2)
      ({ sR.1 with g := sR.1.g.afterCorr P, h := hR' }, osR') := by
  have hac := h.afterCorr_eq P
  refine
    { abortL := h.abortL
      abortR := h.abortR
      winL := h.winL
      winR := h.winR
      winFS := hwinFS'
      bL := h.bL
      bR := h.bR
      bFS := hbFS'
      epoch_eq := h.epoch_eq
      idx_eq := h.idx_eq
      tL_eq := hac.1
      chall_eq := h.chall_eq
      comp_eq := hac.2.2.2.1
      maxAcc_eq := h.maxAcc_eq
      leaks_eq := hac.2.1
      corrs_eq := hac.2.2.1
      trans_eq := h.trans_eq
      idL := h.idL
      idR := h.idR
      tcurL := h.tcurL
      tcurR := h.tcurR
      γ_eq := h.γ_eq
      Tcur_eq := h.Tcur_eq
      root_eq := h.root_eq
      vS_eq := fun Q => by simp only [GameState.afterCorr, GameState.leak, hcurSS, h.vS_eq Q]
      vR_eq := fun Q t' => by simp only [GameState.afterCorr, GameState.leak, hcurRS, h.vR_eq Q t']
      sender_epoch := h.sender_epoch
      receiver_epoch := h.receiver_epoch
      maxEp_le_qep := h.maxEp_le_qep
      tL_le_maxEp := by
        intro l₀ hl₀
        simp only [GameState.afterCorr, GameState.leak, Option.some.injEq] at hl₀ ⊢
        subst hl₀
        cases htL : sR.1.g.tL with
        | none => exact le_rfl
        | some l₁ =>
          have := h.tL_le_maxEp l₁ htL
          simp only [maxOpt]
          omega
      vS_none := h.vS_none
      vS_sending := h.vS_sending
      vR_sender := h.vR_sender
      vR_receiver := h.vR_receiver
      vR_other := h.vR_other
      cache_none := fun t' ht' => by
        rw [hcache]
        exact h.cache_none t' ht'
      cache_other := fun t' ht' => by
        rw [hcache]
        exact h.cache_other t' ht'
      cache_other_ext := fun t' Tc σc kc ext ht' hc => by
        rw [hcache] at hc
        exact h.cache_other_ext t' Tc σc kc ext ht' hc
      cache_t_none := fun hc => by
        rw [hcache] at hc
        exact h.cache_t_none hc
      cache_t := fun Tc σc kc ext hc => by
        rw [hcache] at hc
        rcases h.cache_t Tc σc kc ext hc with ⟨hext, k₀, hcL, hrec⟩
        refine ⟨hext, k₀, hcL, fun hlt => ?_⟩
        rcases hrecv hlt with ⟨hrs, hext'⟩
        rw [hrs, hext']
        exact hrec hlt
      trans_wf := h.trans_wf
      chall_wf := h.chall_wf
      comp_t := fun pos hpos hpe => by
        simp only [GameState.afterCorr, GameState.leak, List.mem_append, List.mem_map,
          List.mem_filter] at hpos ⊢
        rcases hpos with ⟨r, ⟨hr, _⟩, rfl⟩ | hpos
        · have hle : t ≤ max (sR.1.g.epoch .A) (sR.1.g.epoch .B) :=
            hpe ▸ (h.trans_wf r hr).2.2
          exact healedBy_maxOpt_false_of_le hle (by omega)
        · exact healedBy_maxOpt_false_of_false (h.comp_t pos hpos hpe)
      before_t := fun hepM => by
        rcases hbefore hepM with ⟨rfl, rfl⟩
        exact h.before_t hepM
      ext_some := hext_some
      ext_none := hext_none }

omit [DecidableEq T] [DecidableEq M] [DecidableEq E] [DecidableEq I] [Inhabited E]
  [SampleableType I] [SampleableType K] in
theorem ActiveInv.afterCorr_unchanged
    {fs : FSAEADScheme K SS RS (Header T) M E} {Δcka qep : ℕ}
    {tL : Option ℕ} {t : ℕ} {b : Bool}
    {sL : StateL Γ T Sig SS RS M E K I} {sR : StateR Γ T Sig K I SS RS M E}
    (h : ActiveInv fs Δcka qep tL t b sL sR) (P : Party)
    (hca : sR.1.g.corrAllowed P = true) :
    ActiveInv fs Δcka qep tL t b
      ({ sL.1 with g := sL.1.g.afterCorr P }, sL.2)
      ({ sR.1 with g := sR.1.g.afterCorr P }, sR.2) := by
  refine h.afterCorr_preserves P sR.1.h sR.2 h.winFS h.bFS rfl rfl rfl
    (fun _ => ⟨rfl, rfl⟩) (fun _ => ⟨rfl, rfl⟩) ?_ ?_
  · intro hext
    rcases h.ext_some hext with ⟨hheal, hcomp⟩
    refine ⟨healedBy_maxOpt_false_of_false hheal, fun r hr hrt => ?_⟩
    rw [afterCorr_mem_comp_iff hca]
    exact hcomp r hr hrt
  · intro hext
    have hextN := h.ext_none hext
    refine ⟨hextN.1, hextN.2.1, hextN.2.2.1, hextN.2.2.2.1, hextN.2.2.2.2.1,
      hextN.2.2.2.2.2.1, hextN.2.2.2.2.2.2.1, hextN.2.2.2.2.2.2.2.1, ?_,
      ⟨fun hsc => healedBy_maxOpt_false_of_false (hextN.2.2.2.2.2.2.2.2.2.1 hsc),
        hextN.2.2.2.2.2.2.2.2.2.2⟩⟩
    intro r hr hrt
    rw [afterCorr_mem_comp_iff hca]
    exact hextN.2.2.2.2.2.2.2.2.1 r hr hrt

omit [DecidableEq T] [DecidableEq M] [DecidableEq E] [DecidableEq I] [Inhabited E]
  [SampleableType I] [SampleableType K] in
theorem ActiveInv.vR_map_of_ne_some_none
    {fs : FSAEADScheme K SS RS (Header T) M E} {Δcka qep : ℕ}
    {tL : Option ℕ} {t : ℕ} {b : Bool}
    {sL : StateL Γ T Sig SS RS M E K I} {sR : StateR Γ T Sig K I SS RS M E}
    (h : ActiveInv fs Δcka qep tL t b sL sR) (P : Party)
    (hnt : (sR.1.g.st P).vR t ≠ some none) (rs₀ : RS) (t' : ℕ) :
    (match (sR.1.g.st P).vR t' with
     | some (some rs) => some rs
     | some none => none
     | none => none) = ((sR.1.g.st P).vR t').map (·.getD rs₀) := by
  rcases eq_or_ne t' t with ht' | ht'
  · subst ht'
    cases hv : (sR.1.g.st P).vR t' with
    | none => rfl
    | some x =>
      cases x with
      | none => exact absurd hv hnt
      | some rs => rfl
  · cases hv : (sR.1.g.st P).vR t' with
    | none => rfl
    | some x =>
      cases x with
      | none =>
        have h1 := (h.vR_other P t' none ht' hv).1
        simp at h1
      | some rs => rfl

omit [DecidableEq T] [DecidableEq M] [DecidableEq E] [DecidableEq I] [Inhabited E]
  [SampleableType I] [SampleableType K] in
theorem ActiveInv.vR_map_some (opt : Option (Option RS)) (rs₀ : RS) :
    (match opt with
     | some (some rs) => some rs
     | some none => some rs₀
     | none => none) = opt.map (·.getD rs₀) := by
  rcases opt with _ | _ | rs <;> rfl

omit [DecidableEq T] [DecidableEq M] [DecidableEq E] [DecidableEq I] [Inhabited E]
  [SampleableType CCoins] [SampleableType I] [SampleableType K] in
theorem ActiveInv.afterCorr_corruptReceiver
    {fs : FSAEADScheme K SS RS (Header T) M E} {Δcka qep : ℕ}
    {tL : Option ℕ} {t : ℕ} {b : Bool}
    {sL : StateL Γ T Sig SS RS M E K I} {sR : StateR Γ T Sig K I SS RS M E}
    (h : ActiveInv fs Δcka qep tL t b sL sR) (P : Party)
    (hca : sR.1.g.corrAllowed P = true)
    (hext : sR.1.h.ext = none)
    (hvR : (sR.1.g.st P).vR t = some none) :
    FSAEAD.corruptReceiver sR.2 =
      (some (sR.2.senderState, sR.2.receiverState), { sR.2 with ended := true }) ∧
    ActiveInv fs Δcka qep tL t b
      ({ sL.1 with g := sL.1.g.afterCorr P }, sL.2)
      ({ sR.1 with g := sR.1.g.afterCorr P,
                   h := { sR.1.h with ext := some (sR.2.senderState, sR.2.receiverState) } },
       { sR.2 with ended := true }) := by
  have hPr : P = Party.receiverOf t ∧ t ≤ sR.1.g.epoch (Party.receiverOf t) := by
    rcases Party.eq_senderOf_or_receiverOf P t with hPs | hPr
    · have h1 := h.vR_sender
      rw [← hPs, hvR] at h1
      cases h1
    · refine ⟨hPr, ?_⟩
      have h1 := h.vR_receiver
      rw [← hPr, hvR] at h1
      rw [← hPr]
      split_ifs at h1 with hle
      exact hle
  refine ⟨h.corruptReceiver_ok (hPr.1 ▸ hca) hext, ?_⟩
  have hleM : t ≤ max (sR.1.g.epoch .A) (sR.1.g.epoch .B) :=
    le_trans hPr.2 (Party.le_max_apply sR.1.g.epoch (Party.receiverOf t))
  refine h.afterCorr_preserves P _ _ h.winFS h.bFS
    (by simp [curSS, hext]) (by simp [curRS, hext]) rfl
    (fun hlt => by omega) (fun hlt => by omega) ?_ (by simp)
  intro _
  refine ⟨healedBy_maxOpt_false_of_le hleM (by omega), fun r hr hrt => ?_⟩
  rw [afterCorr_mem_comp_iff hca]
  simp only [GameState.corrAllowed, Bool.and_eq_true, Bool.not_eq_true',
    List.any_eq_false] at hca
  have h1 := hca.2 r hr
  have hps : r.pos.sender = P.other := by
    rw [(h.trans_wf r hr).2.1, hrt, hPr.1, Party.other_receiverOf]
  simp [hps] at h1
  exact h1

omit [DecidableEq T] [DecidableEq M] [DecidableEq E] [DecidableEq I] [Inhabited E]
  [SampleableType CCoins] [SampleableType I] [SampleableType K] in
theorem ActiveInv.afterCorr_corruptSender
    {fs : FSAEADScheme K SS RS (Header T) M E} {Δcka qep : ℕ}
    {tL : Option ℕ} {t : ℕ} {b : Bool}
    {sL : StateL Γ T Sig SS RS M E K I} {sR : StateR Γ T Sig K I SS RS M E}
    (h : ActiveInv fs Δcka qep tL t b sL sR) (P : Party)
    (hca : sR.1.g.corrAllowed P = true)
    (hext : sR.1.h.ext = none)
    (hvS : (sR.1.g.st P).vS = some none) :
    (sR.1.g.st P).vR t = none ∧
    sR.2.ended = false ∧
    ActiveInv fs Δcka qep tL t b
      ({ sL.1 with g := sL.1.g.afterCorr P }, sL.2)
      ({ sR.1 with g := sR.1.g.afterCorr P,
                   h := { sR.1.h with fsSCorr := true } },
       { sR.2 with senderCorruptedAt := some (sR.2.senderCorruptedAt.getD sR.2.lastSentIdx) }) := by
  rcases h.vS_none P hvS with ⟨hPs, htep⟩
  subst hPs
  have hvR : (sR.1.g.st (Party.senderOf t)).vR t = none := h.vR_sender
  have hextN := h.ext_none hext
  have hended : sR.2.ended = false := hextN.1
  refine ⟨hvR, hended, ?_⟩
  have hleM : t ≤ max (sR.1.g.epoch .A) (sR.1.g.epoch .B) :=
    le_trans htep (Party.le_max_apply sR.1.g.epoch (Party.senderOf t))
  refine h.afterCorr_preserves (Party.senderOf t) _ _ h.winFS h.bFS
    (by simp [curSS, hext]) (by simp [curRS, hext]) rfl
    (fun hlt => by omega) (fun _ => ⟨rfl, rfl⟩) (by simp [hext]) ?_
  intro _
  refine ⟨hended, hextN.2.1, rfl, hextN.2.2.2.1, hextN.2.2.2.2.1,
    hextN.2.2.2.2.2.1, hextN.2.2.2.2.2.2.1, hextN.2.2.2.2.2.2.2.1, ?_, ?_⟩
  · intro r hr hrt
    rw [afterCorr_mem_comp_iff hca, hextN.2.2.2.2.2.2.2.2.1 r hr hrt]
    have hmem : (r.pos.idx, r.ct.1, r.ct.2) ∈
        (sR.1.g.trans.filter (fun r => r.pos.epoch == t)).map
          (fun r => (r.pos.idx, r.ct.1, r.ct.2)) := by
      refine List.mem_map_of_mem ?_
      simp [hr, hrt]
    rw [hextN.2.2.2.2.2.1, List.mem_map] at hmem
    rcases hmem with ⟨r', hr', hreq⟩
    have hidx : r'.idx = r.pos.idx := by injection hreq
    have hle : r.pos.idx ≤ sR.2.lastSentIdx := hidx ▸ hextN.2.2.2.2.2.2.2.1 r' hr'
    cases hsc : sR.2.senderCorruptedAt with
    | none =>
      simp [FSAEAD.State.isCompromised, hsc, not_lt.mpr hle]
    | some j =>
      simp [FSAEAD.State.isCompromised, hsc]
  · refine ⟨fun _ => healedBy_maxOpt_false_of_le hleM (by omega), fun j hj => ?_⟩
    simp only [Option.some.injEq] at hj ⊢
    cases hsc : sR.2.senderCorruptedAt with
    | none =>
      simp only [hsc, Option.getD_none] at hj
      exact le_of_eq hj.symm
    | some j₀ =>
      simp only [hsc, Option.getD_some] at hj
      subst hj
      exact hextN.2.2.2.2.2.2.2.2.2.2 j₀ hsc

omit [Inhabited E] in
theorem ActiveInv.reveal_fs (cka : CKAScheme KC Γ CCoins T I) (prng : PRFPRNG KR Sig I K)
    {fs : FSAEADScheme K SS RS (Header T) M E} {Δcka qep : ℕ}
    {tL : Option ℕ} {t : ℕ} {b : Bool}
    {sL : StateL Γ T Sig SS RS M E K I} {sR : StateR Γ T Sig K I SS RS M E}
    (h : ActiveInv fs Δcka qep tL t b sL sR) (P : Party)
    (hca : sR.1.g.corrAllowed P = true) :
    ∃ hR' osR',
      runHM (FSAEAD.oracleImpl fs)
        ((hooksFS cka prng fs Δcka ⟨false, tL, t⟩ 0).reveal sR.1.g P (sR.1.g.st P))
        sR.1.h sR.2 = pure ((some (realSt sR P), hR'), osR') ∧
      ActiveInv fs Δcka qep tL t b
        ({ sL.1 with g := sL.1.g.afterCorr P }, sL.2)
        ({ sR.1 with g := sR.1.g.afterCorr P, h := hR' }, osR') := by
  cases hext : sR.1.h.ext with
  | some p =>
    rcases p with ⟨ss₀, rs₀⟩
    have hcurSS : curSS sR.1.h sR.2 = ss₀ := by simp [curSS, hext]
    have hcurRS : curRS sR.1.h sR.2 = rs₀ := by simp [curRS, hext]
    refine ⟨sR.1.h, sR.2, ?_, h.afterCorr_unchanged P hca⟩
    rcases hvS : (sR.1.g.st P).vS with _ | _ | ss <;>
    · rcases hvR : (sR.1.g.st P).vR t with _ | _ | rs
      · simp [runHM, hooksFS, hext, hvS, hvR, realSt, hcurSS, hcurRS]
        congr 1; funext t'; exact h.vR_map_of_ne_some_none P (by simp [hvR]) rs₀ t'
      · simp [runHM, hooksFS, hext, hvS, hvR, realSt, hcurSS, hcurRS]
        congr 1; funext t'; exact ActiveInv.vR_map_some ((sR.1.g.st P).vR t') rs₀
      · simp [runHM, hooksFS, hext, hvS, hvR, realSt, hcurSS, hcurRS]
        congr 1; funext t'; exact h.vR_map_of_ne_some_none P (by simp [hvR]) rs₀ t'
  | none =>
    have hcurSS : curSS sR.1.h sR.2 = sR.2.senderState := by simp [curSS, hext]
    have hcurRS : curRS sR.1.h sR.2 = sR.2.receiverState := by simp [curRS, hext]
    rcases hvS : (sR.1.g.st P).vS with _ | _ | ss
    · rcases hvR : (sR.1.g.st P).vR t with _ | _ | rs
      · refine ⟨sR.1.h, sR.2, ?_, h.afterCorr_unchanged P hca⟩
        simp [runHM, hooksFS, hvS, hvR, realSt, hcurSS, hcurRS]
        congr 1; funext t'
        exact h.vR_map_of_ne_some_none P (by simp [hvR]) sR.2.receiverState t'
      · rcases h.afterCorr_corruptReceiver P hca hext hvR with ⟨hcr, hInv'⟩
        refine ⟨_, _, ?_, hInv'⟩
        simp [runHM, hooksFS, liftF, FSAEAD.corruptReceiverQuery, FSAEAD.oracleImpl,
          FSAEAD.corruptReceiverImpl, hext, hvS, hvR, hcr, realSt, hcurSS, hcurRS, outerFull]
        congr 1; funext t'
        exact ActiveInv.vR_map_some ((sR.1.g.st P).vR t') sR.2.receiverState
      · refine ⟨sR.1.h, sR.2, ?_, h.afterCorr_unchanged P hca⟩
        simp [runHM, hooksFS, hvS, hvR, realSt, hcurSS, hcurRS]
        congr 1; funext t'
        exact h.vR_map_of_ne_some_none P (by simp [hvR]) sR.2.receiverState t'
    · rcases h.afterCorr_corruptSender P hca hext hvS with ⟨hvR, hended, hInv'⟩
      refine ⟨_, _, ?_, hInv'⟩
      simp [runHM, hooksFS, liftF, FSAEAD.corruptSenderQuery, FSAEAD.oracleImpl,
        FSAEAD.corruptSenderImpl, FSAEAD.corruptSender, hext, hvS, hvR, hended,
        realSt, hcurSS, hcurRS, outerFull]
      congr 1; funext t'
      exact h.vR_map_of_ne_some_none P (by simp [hvR]) sR.2.receiverState t'
    · rcases hvR : (sR.1.g.st P).vR t with _ | _ | rs
      · refine ⟨sR.1.h, sR.2, ?_, h.afterCorr_unchanged P hca⟩
        simp [runHM, hooksFS, hvS, hvR, realSt, hcurSS, hcurRS]
        congr 1; funext t'
        exact h.vR_map_of_ne_some_none P (by simp [hvR]) sR.2.receiverState t'
      · rcases h.afterCorr_corruptReceiver P hca hext hvR with ⟨hcr, hInv'⟩
        refine ⟨_, _, ?_, hInv'⟩
        simp [runHM, hooksFS, liftF, FSAEAD.corruptReceiverQuery, FSAEAD.oracleImpl,
          FSAEAD.corruptReceiverImpl, hext, hvS, hvR, hcr, realSt, hcurSS, hcurRS, outerFull]
        congr 1; funext t'
        exact ActiveInv.vR_map_some ((sR.1.g.st P).vR t') sR.2.receiverState
      · refine ⟨sR.1.h, sR.2, ?_, h.afterCorr_unchanged P hca⟩
        simp [runHM, hooksFS, hvS, hvR, realSt, hcurSS, hcurRS]
        congr 1; funext t'
        exact h.vR_map_of_ne_some_none P (by simp [hvR]) sR.2.receiverState t'

theorem StateT_run_liftH {ι : Type} {tspec : OracleSpec.{0, 0} ι}
    {Γv T Sv SSv RSv M E HS α : Type}
    (x : HM tspec HS α) (es : EState (VP Γv T Sv SSv RSv) M (Header T × E) HS) :
    StateT.run (liftH x : EM tspec Γv T Sv SSv RSv M E HS α) es = (do
      let (a, h') ← StateT.run x es.h
      pure (a, { es with h := h' })) := rfl

theorem closeBy_corrE (cka : CKAScheme KC Γ CCoins T I) (prng : PRFPRNG KR Sig I K)
    (fs : FSAEADScheme K SS RS (Header T) M E) (Δcka qep : ℕ) (tL : Option ℕ) (t : ℕ) (b : Bool)
    (P : Party)
    (k : (AdvSpec Γ T Sig SS RS M CCoins E).Range (Sum.inr (Sum.inr P)) →
      OracleComp (AdvSpec Γ T Sig SS RS M CCoins E) Bool)
    (sL : StateL Γ T Sig SS RS M E K I) (sR : StateR Γ T Sig K I SS RS M E)
    (h : ActiveInv fs Δcka qep tL t b sL sR)
    (ih : ∀ u sL₁ sR₁, Inv15 fs Δcka qep tL t b sL₁ sR₁ →
      CloseByEng cka prng fs Δcka qep tL t b (k u) sL₁ sR₁) :
    CloseByEng cka prng fs Δcka qep tL t b (query (Sum.inr (Sum.inr P)) >>= k) sL sR := by
  have hca_eq := h.corrAllowed_eq P
  cases hca : sR.1.g.corrAllowed P
  · refine closeBy_of_det_step cka prng fs Δcka qep tL t b (Sum.inr (Sum.inr P)) k
      sL sL sR sR none none ?_ ?_ ih (Or.inr ⟨rfl, Or.inr h⟩) <;>
    simp [runEM, implE, corrE, h.abortL, h.winL, h.abortR, h.winR, hca_eq, hca]
  · have hac := h.afterCorr_eq P
    have hld_eq : (Policy.mk false tL t).leakDoom sL.1.g (sL.1.g.afterCorr P) =
        (Policy.mk false tL t).leakDoom sR.1.g (sR.1.g.afterCorr P) := hac.2.2.2.2.1
    have hcd_eq : (Policy.mk false tL t).corrDoom sL.1.g P =
        (Policy.mk false tL t).corrDoom sR.1.g P := hac.2.2.2.2.2
    cases hdoom :
      ((Policy.mk false tL t).leakDoom sR.1.g (sR.1.g.afterCorr P) ||
        (Policy.mk false tL t).corrDoom sR.1.g P)
    · have hrevL := h.reveal_prng cka prng fs P hdoom
      rcases h.reveal_fs cka prng P hca with ⟨hR', osR', hrevR, hInv'⟩
      simp only [runHM] at hrevR
      refine closeBy_of_det_step cka prng fs Δcka qep tL t b (Sum.inr (Sum.inr P)) k
        sL ({ sL.1 with g := sL.1.g.afterCorr P }, sL.2)
        sR ({ sR.1 with g := sR.1.g.afterCorr P, h := hR' }, osR')
        (some (realSt sR P)) (some (realSt sR P)) ?_ ?_ ih (Or.inr ⟨rfl, Or.inr hInv'⟩)
      · simp [runEM, implE, corrE, StateT_run_liftH, h.abortL, h.winL, hca_eq, hca,
          hld_eq, hcd_eq, hdoom, hrevL, -Bool.or_eq_true]
      · simp [runEM, implE, corrE, StateT_run_liftH, h.abortR, h.winR, hca,
          hdoom, hrevR, -Bool.or_eq_true]
    · refine closeBy_of_det_step cka prng fs Δcka qep tL t b (Sum.inr (Sum.inr P)) k
        sL ({ sL.1 with abort := true }, sL.2)
        sR ({ sR.1 with abort := true }, sR.2)
        none none ?_ ?_ ih (Or.inr ⟨rfl, Or.inl ⟨rfl, rfl, h.winFS, h.bFS⟩⟩)
      · simp [runEM, implE, corrE, abortE, h.abortL, h.winL,
          hca_eq, hca, hld_eq, hcd_eq, hdoom, -Bool.or_eq_true]
      · simp [runEM, implE, corrE, abortE, h.abortR, h.winR,
          hca, hdoom, -Bool.or_eq_true]

/-! ### Receive step (`deliverE` and `injectE`) -/

omit [DecidableEq T] [DecidableEq M] [DecidableEq E] [DecidableEq I] [Inhabited E]
  [SampleableType CCoins] [SampleableType I] [SampleableType K] in
theorem ActiveInv.cache_eq_none
    {fs : FSAEADScheme K SS RS (Header T) M E} {Δcka qep : ℕ}
    {tL : Option ℕ} {t : ℕ} {b : Bool}
    {sL : StateL Γ T Sig SS RS M E K I} {sR : StateR Γ T Sig K I SS RS M E}
    (h : ActiveInv fs Δcka qep tL t b sL sR) (t' : ℕ)
    (hc : sR.1.h.cache t' = none) :
    sL.1.h.cache t' = none := by
  rcases eq_or_ne t' t with rfl | hne
  · exact h.cache_t_none hc
  · rw [h.cache_other t' hne, hc]
    rfl

omit [DecidableEq T] [DecidableEq M] [DecidableEq E] [DecidableEq I] [Inhabited E]
  [SampleableType CCoins] [SampleableType I] [SampleableType K] in
theorem ActiveInv.cache_some_le_maxEp
    {fs : FSAEADScheme K SS RS (Header T) M E} {Δcka qep : ℕ}
    {tL : Option ℕ} {t : ℕ} {b : Bool}
    {sL : StateL Γ T Sig SS RS M E K I} {sR : StateR Γ T Sig K I SS RS M E}
    (h : ActiveInv fs Δcka qep tL t b sL sR) (t' : ℕ)
    (hc : sR.1.h.cache t' ≠ none) :
    0 < t' ∧ t' ≤ max (sR.1.g.epoch .A) (sR.1.g.epoch .B) := by
  refine ⟨?_, ?_⟩
  · by_contra h0
    have ht0 : t' = 0 := by omega
    exact hc (h.cache_none t' (Or.inl ht0)).2
  · by_contra hgt
    have hlt : max (sR.1.g.epoch .A) (sR.1.g.epoch .B) < t' := by omega
    exact hc (h.cache_none t' (Or.inr hlt)).2

omit [DecidableEq T] [DecidableEq M] [DecidableEq E] [DecidableEq I] [Inhabited E]
  [SampleableType CCoins] [SampleableType I] [SampleableType K] in
theorem ActiveInv.cache_lookup
    {fs : FSAEADScheme K SS RS (Header T) M E} {Δcka qep : ℕ}
    {tL : Option ℕ} {t : ℕ} {b : Bool}
    {sL : StateL Γ T Sig SS RS M E K I} {sR : StateR Γ T Sig K I SS RS M E}
    (h : ActiveInv fs Δcka qep tL t b sL sR) {P : Party} {t' : ℕ}
    {Tc : T} {σc : Sig} {kc : K} {ext : Bool}
    (hPr : P = Party.receiverOf t')
    (ht_succ : t' = sR.1.g.epoch P + 1)
    (hc : sR.1.h.cache t' = some (Tc, σc, kc, ext)) :
    ∃ σL k₀,
      sL.1.h.cache t' = some (Tc, σL, k₀) ∧
      σL = (if t' < t ∧ ¬(tL.isSome && decide (t' < healEpoch tL)) then none else some σc) ∧
      (if ext then none else some (fs.initReceiver kc)).getD (curRS sR.1.h sR.2) =
        fs.initReceiver k₀ ∧
      ext = decide (t' = t) := by
  rcases eq_or_ne t' t with rfl | hne
  · rcases h.cache_t Tc σc kc ext hc with ⟨rfl, k₀, hcL, hrec⟩
    have hlt : sR.1.g.epoch (Party.receiverOf t') < t' := by rw [← hPr]; omega
    rcases hrec hlt with ⟨hrs, hext⟩
    refine ⟨some σc, k₀, hcL, by simp, ?_, by simp⟩
    simp [curRS, hext, hrs]
  · have hext := h.cache_other_ext t' Tc σc kc ext hne hc
    subst hext
    have hcL := h.cache_other t' hne
    rw [hc] at hcL
    exact ⟨_, kc, hcL, rfl, rfl, by simp [hne]⟩

structure SteppedVP (fs : FSAEADScheme K SS RS (Header T) M E)
    (tL : Option ℕ) (t : ℕ)
    (sL : StateL Γ T Sig SS RS M E K I) (sR : StateR Γ T Sig K I SS RS M E)
    (P : Party) (t' : ℕ)
    (s₁L : VP Γ T (Option Sig) SS RS) (s₁R : VP Γ T Sig (Option SS) (Option RS)) : Prop where
  P_eq : P = Party.receiverOf t'
  t'_le_succ : t' ≤ sR.1.g.epoch P + 1
  t'_le_maxEp : t' ≤ max (sR.1.g.epoch .A) (sR.1.g.epoch .B)
  idL : s₁L.id = P
  idR : s₁R.id = P
  tcurL : s₁L.tcur = max (sR.1.g.epoch P) t'
  tcurR : s₁R.tcur = max (sR.1.g.epoch P) t'
  γ_eq : s₁L.γ = s₁R.γ
  Tcur_eq : s₁L.curCkaMsg = s₁R.curCkaMsg
  root_eq : s₁L.root =
    if max (sR.1.g.epoch P) t' < t ∧ ¬(tL.isSome && decide (max (sR.1.g.epoch P) t' < healEpoch tL))
    then none else some s₁R.root
  vS_R : s₁R.vS = (sR.1.g.st P).vS
  vS_L : s₁L.vS = s₁R.vS.map (·.getD (curSS sR.1.h sR.2))
  vR_eq : ∀ t'', s₁L.vR t'' = (s₁R.vR t'').map (·.getD (curRS sR.1.h sR.2))
  vR_t_sender : P = Party.senderOf t → s₁R.vR t = none
  vR_t_receiver : P = Party.receiverOf t →
    s₁R.vR t = if t ≤ max (sR.1.g.epoch P) t' then some none else none
  vR_other : ∀ t'' x, t'' ≠ t → s₁R.vR t'' = some x →
    x.isSome = true ∧ P = Party.receiverOf t'' ∧ t'' ≤ max (sR.1.g.epoch P) t'
  root_before_t :
    max (sR.1.g.epoch .A) (sR.1.g.epoch .B) < t →
    max (sR.1.g.epoch P) t' = max (sR.1.g.epoch .A) (sR.1.g.epoch .B) →
      s₁R.root = sL.2.1.σ

omit [DecidableEq T] [DecidableEq M] [DecidableEq E] [DecidableEq I] [Inhabited E]
  [SampleableType CCoins] [SampleableType I] [SampleableType K] in
theorem ActiveInv.steppedVP_stay
    {fs : FSAEADScheme K SS RS (Header T) M E} {Δcka qep : ℕ}
    {tL : Option ℕ} {t : ℕ} {b : Bool}
    {sL : StateL Γ T Sig SS RS M E K I} {sR : StateR Γ T Sig K I SS RS M E}
    (h : ActiveInv fs Δcka qep tL t b sL sR) {P : Party} {t' : ℕ}
    (hPr : P = Party.receiverOf t') (hle : t' ≤ sR.1.g.epoch P) :
    SteppedVP fs tL t sL sR P t' (sL.1.g.st P) (sR.1.g.st P) := by
  have hmax : max (sR.1.g.epoch P) t' = sR.1.g.epoch P := Nat.max_eq_left hle
  refine
    { P_eq := hPr
      t'_le_succ := by omega
      t'_le_maxEp := le_trans hle (Party.le_max_apply sR.1.g.epoch P)
      idL := h.idL P
      idR := h.idR P
      tcurL := by rw [hmax, h.tcurL P]
      tcurR := by rw [hmax, h.tcurR P]
      γ_eq := h.γ_eq P
      Tcur_eq := h.Tcur_eq P
      root_eq := by rw [hmax, h.root_eq P]
      vS_R := rfl
      vS_L := h.vS_eq P
      vR_eq := h.vR_eq P
      vR_t_sender := fun hPs => hPs ▸ h.vR_sender
      vR_t_receiver := fun hPrt => by rw [hmax, hPrt, h.vR_receiver]
      vR_other := fun t'' x hne hv => by
        rw [hmax]
        exact h.vR_other P t'' x hne hv
      root_before_t := fun hepM heq => by
        rw [hmax] at heq
        exact (h.before_t hepM).2.2.2.2.2.1 P heq }

omit [DecidableEq T] [DecidableEq M] [DecidableEq E] [DecidableEq I] [Inhabited E]
  [SampleableType CCoins] [SampleableType I] [SampleableType K] in
theorem ActiveInv.steppedVP_advance (cka : CKAScheme KC Γ CCoins T I)
    {fs : FSAEADScheme K SS RS (Header T) M E} {Δcka qep : ℕ}
    {tL : Option ℕ} {t : ℕ} {b : Bool}
    {sL : StateL Γ T Sig SS RS M E K I} {sR : StateR Γ T Sig K I SS RS M E}
    (h : ActiveInv fs Δcka qep tL t b sL sR) {P : Party} {t' : ℕ}
    {Tc : T} {σc : Sig} {kc : K} {ext : Bool} {σL : Option Sig} {k₀ : K}
    (hPr : P = Party.receiverOf t')
    (ht_succ : t' = sR.1.g.epoch P + 1)
    (hc : sR.1.h.cache t' = some (Tc, σc, kc, ext))
    (hσL : σL = (if t' < t ∧ ¬(tL.isSome && decide (t' < healEpoch tL)) then none else some σc))
    (hrs₀ : (if ext then none else some (fs.initReceiver kc)).getD (curRS sR.1.h sR.2) =
      fs.initReceiver k₀)
    (hext_eq : ext = decide (t' = t)) :
    SteppedVP fs tL t sL sR P t'
      { sL.1.g.st P with
          tcur := t',
          γ := (cka.receive (sL.1.g.st P).γ Tc).1,
          root := σL,
          vR := Function.update (sL.1.g.st P).vR t' (some (fs.initReceiver k₀)) }
      { sR.1.g.st P with
          tcur := t',
          γ := (cka.receive (sR.1.g.st P).γ Tc).1,
          root := σc,
          vR := Function.update (sR.1.g.st P).vR t'
            (some (if ext then none else some (fs.initReceiver kc))) } := by
  have hmax : max (sR.1.g.epoch P) t' = t' := Nat.max_eq_right (by omega)
  have hle_maxEp : t' ≤ max (sR.1.g.epoch .A) (sR.1.g.epoch .B) :=
    (h.cache_some_le_maxEp t' (by simp [hc])).2
  refine
    { P_eq := hPr
      t'_le_succ := by omega
      t'_le_maxEp := hle_maxEp
      idL := h.idL P
      idR := h.idR P
      tcurL := by simp [hmax]
      tcurR := by simp [hmax]
      γ_eq := by simp [h.γ_eq P]
      Tcur_eq := h.Tcur_eq P
      root_eq := by simp [hmax, hσL]
      vS_R := rfl
      vS_L := h.vS_eq P
      vR_eq := fun t'' => by
        rcases eq_or_ne t'' t' with rfl | hne
        · simp [hrs₀]
        · simp [Function.update_of_ne hne, h.vR_eq P t'']
      vR_t_sender := fun hPs => by
        have hne : t ≠ t' := by
          intro heq
          subst heq
          exact Party.senderOf_ne_receiverOf t (hPs.symm.trans hPr)
        simp [Function.update_of_ne hne, hPs, h.vR_sender]
      vR_t_receiver := fun hPrt => by
        simp only [hmax]
        subst hPrt
        rcases eq_or_ne t t' with rfl | hne
        · simp [hext_eq]
        · simp only [Function.update_of_ne hne, h.vR_receiver]
          split_ifs with h1 h2 <;> first | rfl | omega
      vR_other := fun t'' x hne_t hv => by
        rw [hmax]
        rcases eq_or_ne t'' t' with rfl | hne_t'
        · simp only [Function.update_self, Option.some.injEq] at hv
          subst hv
          simp [hext_eq, hne_t, hPr]
        · simp only [Function.update_of_ne hne_t'] at hv
          rcases h.vR_other P t'' x hne_t hv with ⟨hx, hPr'', hle''⟩
          exact ⟨hx, hPr'', by omega⟩
      root_before_t := fun hepM heq => by
        rw [hmax] at heq
        subst heq
        exact (h.before_t hepM).2.2.2.2.2.2.1 Tc σc kc ext hc }

omit [DecidableEq M] [Inhabited E] in
theorem ActiveInv.prepRecv (cka : CKAScheme KC Γ CCoins T I) (prng : PRFPRNG KR Sig I K)
    {fs : FSAEADScheme K SS RS (Header T) M E} {Δcka qep : ℕ}
    {tL : Option ℕ} {t : ℕ} {b : Bool}
    {sL : StateL Γ T Sig SS RS M E K I} {sR : StateR Γ T Sig K I SS RS M E}
    (h : ActiveInv fs Δcka qep tL t b sL sR) (P : Party) (c : Header T × E)
    (recL recR : Option (Record M (Header T × E))) :
    ((vRecv (hooksPRNG cka prng fs ⟨false, tL, t⟩) sL.1.g P (sL.1.g.st P) c recL).run sL.1.h =
        pure (some none, sL.1.h) ∧
     (vRecv (hooksFS cka prng fs Δcka ⟨false, tL, t⟩ 0) sR.1.g P (sR.1.g.st P) c recR).run sR.1.h =
        pure (some none, sR.1.h)) ∨
    ∃ s₁L s₁R rsv,
      SteppedVP fs tL t sL sR P c.1.1 s₁L s₁R ∧
      s₁R.vR c.1.1 = some rsv ∧
      s₁L.vR c.1.1 = some (rsv.getD (curRS sR.1.h sR.2)) ∧
      (vRecv (hooksPRNG cka prng fs ⟨false, tL, t⟩) sL.1.g P (sL.1.g.st P) c recL).run sL.1.h =
        pure (match fs.receive (rsv.getD (curRS sR.1.h sR.2)) c.1 c.2 with
          | none => some none
          | some (v', i, m) =>
            some (some ({ s₁L with vR := Function.update s₁L.vR c.1.1 (some v') }, c.1.1, i, m)),
          sL.1.h) ∧
      (vRecv (hooksFS cka prng fs Δcka ⟨false, tL, t⟩ 0) sR.1.g P (sR.1.g.st P) c recR).run sR.1.h =
        (((hooksFS cka prng fs Δcka ⟨false, tL, t⟩ 0).fsRecv
            sR.1.g P c.1.1 rsv c.1 c.2 recR).run sR.1.h >>= fun p =>
          pure (match p.1 with
            | none => none
            | some none => some none
            | some (some (v', i, m)) =>
              some (some ({ s₁R with vR := Function.update s₁R.vR c.1.1 (some v') },
                c.1.1, i, m)), p.2)) := by
  cases hcond : (P.sendsIn c.1.1 || decide (sR.1.g.epoch P + 1 < c.1.1))
  · simp only [Bool.or_eq_false_iff, decide_eq_false_iff_not, not_lt] at hcond
    have hPr : P = Party.receiverOf c.1.1 :=
      (Party.sendsIn_false_iff_receiverOf P c.1.1).mp hcond.1
    rcases eq_or_ne c.1.1 (sR.1.g.epoch P + 1) with ht_succ | ht_ne
    · cases hc2 : c.1.2 with
      | none =>
        left
        refine ⟨?_, ?_⟩
        · simp [vRecv, h.idL P, h.tcurL P, hcond.1, ← ht_succ, hc2]
        · simp [vRecv, h.idR P, h.tcurR P, hcond.1, ← ht_succ, hc2]
      | some Tn =>
        cases hcache : sR.1.h.cache c.1.1 with
        | none =>
          have hcacheL := h.cache_eq_none c.1.1 hcache
          left
          refine ⟨?_, ?_⟩
          · simp [vRecv, hooksPRNG, h.idL P, h.tcurL P, hcond.1, ← ht_succ, hc2, hcacheL]
          · simp [vRecv, hooksFS, h.idR P, h.tcurR P, hcond.1, ← ht_succ, hc2, hcache]
        | some val =>
          rcases val with ⟨Tc, σc, kc, ext⟩
          rcases h.cache_lookup hPr ht_succ hcache with ⟨σL, k₀, hcacheL, hσL, hrs₀, hext_eq⟩
          rcases eq_or_ne Tc Tn with rfl | hne_T
          · right
            refine ⟨_, _, if ext then none else some (fs.initReceiver kc),
              h.steppedVP_advance cka hPr ht_succ hcache hσL hrs₀ hext_eq,
              by simp, by simp [hrs₀], ?_, ?_⟩
            · cases hrecv : fs.receive (fs.initReceiver k₀) c.1 c.2 <;>
              simp [vRecv, hooksPRNG, h.idL P, h.tcurL P, hcond.1, ← ht_succ, hc2, hcacheL,
                hrs₀, hrecv]
            · have hstartR : ((hooksFS cka prng fs Δcka ⟨false, tL, t⟩ 0).startRecv sR.1.g P
                  c.1.1 (sR.1.g.st P).γ (sR.1.g.st P).root Tc).run sR.1.h =
                  pure (some (some ((cka.receive (sR.1.g.st P).γ Tc).1, σc,
                    if ext then none else some (fs.initReceiver kc))), sR.1.h) := by
                simp [hooksFS, hcache]
              simp only [vRecv, h.idR P, h.tcurR P, hcond.1, ← ht_succ, hc2,
                Nat.lt_irrefl, decide_false, Bool.or_false, Bool.false_eq_true, ↓reduceIte,
                StateT.run_bind, hstartR, pure_bind, Function.update_self]
              congr 1; funext ⟨res, h'⟩
              rcases res with _ | _ | ⟨v', i, m⟩ <;> simp
          · left
            refine ⟨?_, ?_⟩
            · simp [vRecv, hooksPRNG, h.idL P, h.tcurL P, hcond.1, ← ht_succ, hc2, hcacheL, hne_T]
            · simp [vRecv, hooksFS, h.idR P, h.tcurR P, hcond.1, ← ht_succ, hc2, hcache, hne_T]
    · have hle : c.1.1 ≤ sR.1.g.epoch P := by omega
      cases hvR : (sR.1.g.st P).vR c.1.1 with
      | none =>
        have hvRL : (sL.1.g.st P).vR c.1.1 = none := by rw [h.vR_eq P c.1.1, hvR]; rfl
        left
        refine ⟨?_, ?_⟩
        · simp [vRecv, h.idL P, h.tcurL P, hcond.1, not_lt.mpr hcond.2, ht_ne, hvRL]
        · simp [vRecv, h.idR P, h.tcurR P, hcond.1, not_lt.mpr hcond.2, ht_ne, hvR]
      | some rsv =>
        have hvRL : (sL.1.g.st P).vR c.1.1 = some (rsv.getD (curRS sR.1.h sR.2)) := by
          rw [h.vR_eq P c.1.1, hvR]; rfl
        right
        refine ⟨sL.1.g.st P, sR.1.g.st P, rsv, h.steppedVP_stay hPr hle, hvR, hvRL, ?_, ?_⟩
        · cases hrecv : fs.receive (rsv.getD (curRS sR.1.h sR.2)) c.1 c.2 <;>
          simp [vRecv, hooksPRNG, h.idL P, h.tcurL P, hcond.1, not_lt.mpr hcond.2, ht_ne,
            hvRL, hrecv]
        · simp only [vRecv, h.idR P, h.tcurR P, hcond.1, not_lt.mpr hcond.2,
            decide_false, Bool.or_false, Bool.false_eq_true, ht_ne, ↓reduceIte,
            StateT.run_bind, pure_bind, hvR]
          congr 1; funext ⟨res, h'⟩
          rcases res with _ | _ | ⟨v', i, m⟩ <;> simp
  · left
    refine ⟨?_, ?_⟩
    · simp [vRecv, h.idL P, h.tcurL P, hcond, -Bool.or_eq_true]
    · simp [vRecv, h.idR P, h.tcurR P, hcond, -Bool.or_eq_true]

theorem accept_update_st_self {St Msg C : Type}
    (s : GameState St Msg C) (P : Party) (st' : St) (pos : Pos) :
    { s.accept P st' pos with st := Function.update (s.accept P st' pos).st P st' } =
      s.accept P st' pos := by
  simp [GameState.accept]

omit [DecidableEq T] [DecidableEq M] [DecidableEq E] [DecidableEq I] [Inhabited E]
  [SampleableType CCoins] [SampleableType I] [SampleableType K] in
theorem SteppedVP.epoch_accept
    {fs : FSAEADScheme K SS RS (Header T) M E} {Δcka qep : ℕ}
    {tL : Option ℕ} {t : ℕ} {b : Bool}
    {sL : StateL Γ T Sig SS RS M E K I} {sR : StateR Γ T Sig K I SS RS M E}
    {P : Party} {t' : ℕ}
    {s₁L : VP Γ T (Option Sig) SS RS} {s₁R : VP Γ T Sig (Option SS) (Option RS)}
    (h : ActiveInv fs Δcka qep tL t b sL sR)
    (hs : SteppedVP fs tL t sL sR P t' s₁L s₁R) :
    let ep' := Function.update sR.1.g.epoch P (max (sR.1.g.epoch P) t')
    let epM := max (sR.1.g.epoch .A) (sR.1.g.epoch .B)
    max (ep' .A) (ep' .B) = epM ∧
    ep' (Party.senderOf epM) = epM ∧
    (ep' (Party.receiverOf epM) = epM ∨ (1 ≤ epM ∧ ep' (Party.receiverOf epM) + 1 = epM)) ∧
    ∀ Q, Q.sendsIn (ep' Q) = true → ep' Q = sR.1.g.epoch Q := by
  intro ep' epM
  have hbound : ∀ Q, sR.1.g.epoch Q ≤ ep' Q ∧ ep' Q ≤ epM := by
    intro Q
    rcases eq_or_ne Q P with rfl | hne
    · simp only [ep', Function.update_self]
      have h1 := Party.le_max_apply sR.1.g.epoch Q
      have h2 := hs.t'_le_maxEp
      omega
    · simp only [ep', Function.update_of_ne hne]
      exact ⟨le_rfl, Party.le_max_apply sR.1.g.epoch Q⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · have hA := hbound .A
    have hB := hbound .B
    dsimp only [epM] at *
    omega
  · have hS := hbound (Party.senderOf epM)
    have hSe := h.sender_epoch
    dsimp only [epM] at *
    omega
  · have hR := hbound (Party.receiverOf epM)
    have hRe := h.receiver_epoch
    dsimp only [epM] at *
    omega
  · intro Q hsend
    rcases eq_or_ne Q P with rfl | hne
    · simp only [ep', Function.update_self] at hsend ⊢
      rcases le_or_gt t' (sR.1.g.epoch Q) with hle | hgt
      · exact Nat.max_eq_left hle
      · have := hs.t'_le_succ
        have ht_eq : t' = sR.1.g.epoch Q + 1 := by omega
        have hmax : max (sR.1.g.epoch Q) t' = t' := Nat.max_eq_right (by omega)
        rw [hmax, hs.P_eq, (Party.sendsIn_false_iff_receiverOf _ _).mpr rfl] at hsend
        cases hsend
    · simp [ep', Function.update_of_ne hne]

omit [DecidableEq T] [DecidableEq M] [DecidableEq E] [DecidableEq I] [Inhabited E]
  [SampleableType CCoins] [SampleableType I] [SampleableType K] in
theorem SteppedVP.accept_core
    {fs : FSAEADScheme K SS RS (Header T) M E} {Δcka qep : ℕ}
    {tL : Option ℕ} {t : ℕ} {b : Bool}
    {sL : StateL Γ T Sig SS RS M E K I} {sR : StateR Γ T Sig K I SS RS M E}
    {P : Party} {t' : ℕ}
    {s₁L : VP Γ T (Option Sig) SS RS} {s₁R : VP Γ T Sig (Option SS) (Option RS)}
    (h : ActiveInv fs Δcka qep tL t b sL sR)
    (hs : SteppedVP fs tL t sL sR P t' s₁L s₁R)
    (rs' : RS) (vR_R' : Option RS) (idx₀ : ℕ)
    (hR' : FSState T Sig K I SS RS E) (osR' : FSAEAD.State SS RS (Header T) M E)
    (hwinFS' : osR'.win = false) (hbFS' : osR'.b = b)
    (hvR_getD : vR_R'.getD (curRS hR' osR') = rs')
    (hcurSS : curSS hR' osR' = curSS sR.1.h sR.2)
    (hcurRS_ne : t' ≠ t → curRS hR' osR' = curRS sR.1.h sR.2)
    (hvR_t : t' = t → vR_R' = none)
    (hvR_ne : t' ≠ t → vR_R' = some rs')
    (hcache : hR'.cache = sR.1.h.cache)
    (ht_unchanged : t' ≠ t → hR' = sR.1.h ∧ osR' = sR.2)
    (hext_some : hR'.ext.isSome = true →
      healedBy sR.1.g.tL (2 + Δcka) t = false ∧
      ∀ r ∈ (sR.1.g.delete ⟨P.other, t', idx₀⟩).trans,
        r.pos.epoch = t → r.pos ∈ (sR.1.g.delete ⟨P.other, t', idx₀⟩).comp)
    (hext_none : hR'.ext = none →
      osR'.ended = false ∧
      hR'.fsCount = osR'.lastSentIdx ∧
      hR'.fsSCorr = osR'.senderCorruptedAt.isSome ∧
      ((Function.update sR.1.g.epoch P (max (sR.1.g.epoch P) t')) (Party.senderOf t) = t →
        sR.1.g.idx (Party.senderOf t) = osR'.lastSentIdx) ∧
      hR'.fsTrans = osR'.inTransit.map (fun r => (r.idx, r.ad, r.ct)) ∧
      (((sR.1.g.delete ⟨P.other, t', idx₀⟩).trans.filter (fun r => r.pos.epoch == t)).map
        (fun r => (r.pos.idx, r.ct.1, r.ct.2)) =
        osR'.inTransit.map (fun r => (r.idx, r.ad, r.ct))) ∧
      (((sR.1.g.delete ⟨P.other, t', idx₀⟩).chall.filter (fun pos => pos.epoch == t)).map Pos.idx =
        osR'.challengesInTransit) ∧
      (∀ r ∈ osR'.inTransit, r.idx ≤ osR'.lastSentIdx) ∧
      (∀ r ∈ (sR.1.g.delete ⟨P.other, t', idx₀⟩).trans, r.pos.epoch = t →
        (r.pos ∈ (sR.1.g.delete ⟨P.other, t', idx₀⟩).comp ↔ osR'.isCompromised r.pos.idx = true)) ∧
      ((osR'.senderCorruptedAt.isSome = true → healedBy sR.1.g.tL (2 + Δcka) t = false) ∧
        (∀ j, osR'.senderCorruptedAt = some j → j ≤ osR'.lastSentIdx))) :
    let pos : Pos := ⟨P.other, t', idx₀⟩
    let stL' := { s₁L with vR := Function.update s₁L.vR t' (some rs') }
    let stR' := { s₁R with vR := Function.update s₁R.vR t' (some vR_R') }
    ActiveInv fs Δcka qep tL t b
      ({ sL.1 with g := sL.1.g.accept P stL' pos }, sL.2)
      ({ sR.1 with g := sR.1.g.accept P stR' pos, h := hR' }, osR') := by
  intro pos stL' stR'
  have hpos_ep : pos.epoch = t' := rfl
  rcases hs.epoch_accept h with ⟨hmax_eq, hsend_ep, hrecv_ep, hsend_stay⟩
  have hdel_eq := trans_delete_map_eq h.trans_eq pos
  refine
    { abortL := h.abortL
      abortR := h.abortR
      winL := h.winL
      winR := h.winR
      winFS := hwinFS'
      bL := h.bL
      bR := h.bR
      bFS := hbFS'
      epoch_eq := by simp [GameState.accept, GameState.delete, h.epoch_eq]
      idx_eq := h.idx_eq
      tL_eq := h.tL_eq
      chall_eq := by simp [GameState.accept, GameState.delete, h.chall_eq]
      comp_eq := by simp [GameState.accept, GameState.delete, h.comp_eq]
      maxAcc_eq := by simp [GameState.accept, GameState.delete, h.maxAcc_eq]
      leaks_eq := h.leaks_eq
      corrs_eq := h.corrs_eq
      trans_eq := hdel_eq
      idL := fun Q => by
        rcases eq_or_ne Q P with rfl | hne
        · simp [GameState.accept, GameState.delete, stL', hs.idL]
        · simp [GameState.accept, GameState.delete, Function.update_of_ne hne, h.idL]
      idR := fun Q => by
        rcases eq_or_ne Q P with rfl | hne
        · simp [GameState.accept, GameState.delete, stR', hs.idR]
        · simp [GameState.accept, GameState.delete, Function.update_of_ne hne, h.idR]
      tcurL := fun Q => by
        rcases eq_or_ne Q P with rfl | hne
        · simp [GameState.accept, GameState.delete, hpos_ep, stL', hs.tcurL]
        · simp [GameState.accept, GameState.delete, Function.update_of_ne hne, h.tcurL]
      tcurR := fun Q => by
        rcases eq_or_ne Q P with rfl | hne
        · simp [GameState.accept, GameState.delete, hpos_ep, stR', hs.tcurR]
        · simp [GameState.accept, GameState.delete, Function.update_of_ne hne, h.tcurR]
      γ_eq := fun Q => by
        rcases eq_or_ne Q P with rfl | hne
        · simp [GameState.accept, GameState.delete, stL', stR', hs.γ_eq]
        · simp [GameState.accept, GameState.delete, Function.update_of_ne hne, h.γ_eq]
      Tcur_eq := fun Q => by
        rcases eq_or_ne Q P with rfl | hne
        · simp [GameState.accept, GameState.delete, stL', stR', hs.Tcur_eq]
        · simp [GameState.accept, GameState.delete, Function.update_of_ne hne, h.Tcur_eq]
      root_eq := fun Q => by
        rcases eq_or_ne Q P with rfl | hne
        · simp [GameState.accept, GameState.delete, hpos_ep, stL', stR', hs.root_eq]
        · simp [GameState.accept, GameState.delete, Function.update_of_ne hne, h.root_eq Q]
      vS_eq := fun Q => by
        rcases eq_or_ne Q P with rfl | hne
        · simp [GameState.accept, GameState.delete, stL', stR', hcurSS, hs.vS_L]
        · simp [GameState.accept, GameState.delete, Function.update_of_ne hne, hcurSS, h.vS_eq Q]
      vR_eq := fun Q t'' => by
        rcases eq_or_ne Q P with rfl | hne_Q
        · simp only [GameState.accept, GameState.delete, Function.update_self, stL', stR']
          rcases eq_or_ne t'' t' with rfl | hne_t'
          · simp [hvR_getD]
          · simp only [Function.update_of_ne hne_t', hs.vR_eq t'']
            rcases eq_or_ne t' t with rfl | hne_t
            · cases hv : s₁R.vR t'' with
              | none => rfl
              | some x =>
                cases x with
                | none =>
                  have h1 := (hs.vR_other t'' none hne_t' hv).1
                  simp at h1
                | some rs => rfl
            · rw [hcurRS_ne hne_t]
        · simp only [GameState.accept, GameState.delete, Function.update_of_ne hne_Q, h.vR_eq Q t'']
          rcases eq_or_ne t' t with rfl | hne_t
          · have hQs : Q = Party.senderOf t' := by
              rcases Party.eq_senderOf_or_receiverOf Q t' with hQs | hQr
              · exact hQs
              · exact absurd (hQr.trans hs.P_eq.symm) hne_Q
            rcases eq_or_ne t'' t' with rfl | hne_t''
            · rw [hQs, h.vR_sender]; rfl
            · cases hv : (sR.1.g.st Q).vR t'' with
              | none => rfl
              | some x =>
                cases x with
                | none =>
                  have h1 := (h.vR_other Q t'' none hne_t'' hv).1
                  simp at h1
                | some rs => rfl
          · rw [hcurRS_ne hne_t]
      sender_epoch := by
        simp only [GameState.accept, GameState.delete, hpos_ep, hmax_eq]
        exact hsend_ep
      receiver_epoch := by
        simp only [GameState.accept, GameState.delete, hpos_ep, hmax_eq]
        exact hrecv_ep
      maxEp_le_qep := by
        simp only [GameState.accept, GameState.delete, hpos_ep, hmax_eq]
        exact h.maxEp_le_qep
      tL_le_maxEp := fun l₀ hl₀ => by
        simp only [GameState.accept, GameState.delete, hpos_ep, hmax_eq] at hl₀ ⊢
        exact h.tL_le_maxEp l₀ hl₀
      vS_none := fun Q hvS => by
        simp only [GameState.accept, GameState.delete, hpos_ep] at hvS ⊢
        rcases eq_or_ne Q P with rfl | hne_Q
        · simp only [Function.update_self, stR', hs.vS_R] at hvS ⊢
          rcases h.vS_none Q hvS with ⟨hQs, hle⟩
          exact ⟨hQs, by omega⟩
        · simp only [Function.update_of_ne hne_Q] at hvS ⊢
          exact h.vS_none Q hvS
      vS_sending := fun Q hsend => by
        simp only [GameState.accept, GameState.delete, hpos_ep] at hsend ⊢
        have hstay := hsend_stay Q hsend
        rw [hstay] at hsend ⊢
        rcases eq_or_ne Q P with rfl | hne_Q
        · simp only [Function.update_self, stR', hs.vS_R]
          exact h.vS_sending Q hsend
        · simp only [Function.update_of_ne hne_Q]
          exact h.vS_sending Q hsend
      vR_sender := by
        simp only [GameState.accept, GameState.delete]
        rcases eq_or_ne (Party.senderOf t) P with heq | hne
        · rw [heq, Function.update_self]
          have hne_t : t ≠ t' := by
            intro ht
            subst ht
            exact Party.senderOf_ne_receiverOf t (heq.trans hs.P_eq)
          simp [stR', Function.update_of_ne hne_t, hs.vR_t_sender heq.symm]
        · rw [Function.update_of_ne hne]
          exact h.vR_sender
      vR_receiver := by
        simp only [GameState.accept, GameState.delete, hpos_ep]
        rcases eq_or_ne (Party.receiverOf t) P with heq | hne
        · simp only [heq, Function.update_self]
          rcases eq_or_ne t t' with rfl | hne_t
          · simp [stR', hvR_t rfl]
          · simp [stR', Function.update_of_ne hne_t, hs.vR_t_receiver heq.symm]
        · simp only [Function.update_of_ne hne]
          exact h.vR_receiver
      vR_other := fun Q t'' x hne_t hv => by
        simp only [GameState.accept, GameState.delete, hpos_ep] at hv ⊢
        rcases eq_or_ne Q P with rfl | hne_Q
        · simp only [Function.update_self, stR'] at hv ⊢
          rcases eq_or_ne t'' t' with rfl | hne_t'
          · simp only [Function.update_self, Option.some.injEq] at hv
            subst hv
            simp [hvR_ne hne_t, hs.P_eq]
          · simp only [Function.update_of_ne hne_t'] at hv
            exact hs.vR_other t'' x hne_t hv
        · simp only [Function.update_of_ne hne_Q] at hv ⊢
          exact h.vR_other Q t'' x hne_t hv
      cache_none := fun t'' ht'' => by
        simp only [GameState.accept, GameState.delete, hpos_ep, hmax_eq] at ht''
        rw [hcache]
        exact h.cache_none t'' ht''
      cache_other := fun t'' ht'' => by
        rw [hcache]
        exact h.cache_other t'' ht''
      cache_other_ext := fun t'' Tc σc kc ext ht'' hc => by
        rw [hcache] at hc
        exact h.cache_other_ext t'' Tc σc kc ext ht'' hc
      cache_t_none := fun hc => by
        rw [hcache] at hc
        exact h.cache_t_none hc
      cache_t := fun Tc σc kc ext hc => by
        rw [hcache] at hc
        rcases h.cache_t Tc σc kc ext hc with ⟨hext, k₀, hcL, hrec⟩
        refine ⟨hext, k₀, hcL, fun hlt => ?_⟩
        simp only [GameState.accept, GameState.delete, hpos_ep] at hlt
        rcases eq_or_ne t' t with rfl | hne_t
        · rw [← hs.P_eq, Function.update_self] at hlt
          omega
        · rcases ht_unchanged hne_t with ⟨rfl, rfl⟩
          apply hrec
          rcases eq_or_ne (Party.receiverOf t) P with heq | hne_P
          · rw [heq, Function.update_self] at hlt
            rw [heq]
            omega
          · rw [Function.update_of_ne hne_P] at hlt
            exact hlt
      trans_wf := fun r hr => by
        simp only [GameState.accept, GameState.delete, hpos_ep, hmax_eq, List.mem_filter] at hr ⊢
        exact h.trans_wf r hr.1
      chall_wf := fun p hp => by
        simp only [GameState.accept, GameState.delete, hpos_ep, hmax_eq, List.mem_filter] at hp ⊢
        exact h.chall_wf p hp.1
      comp_t := fun p hp hpe => by
        simp only [GameState.accept, GameState.delete, List.mem_filter] at hp ⊢
        exact h.comp_t p hp.1 hpe
      before_t := by
        simp only [GameState.accept, GameState.delete, hpos_ep, hmax_eq]
        intro hepM
        have hne_t : t' ≠ t := by
          have := hs.t'_le_maxEp
          omega
        rcases ht_unchanged hne_t with ⟨rfl, rfl⟩
        have hb := h.before_t hepM
        refine ⟨hb.1, hb.2.1, hb.2.2.1, hb.2.2.2.1, hb.2.2.2.2.1, ?_, ?_, hb.2.2.2.2.2.2.2⟩
        · intro Q hQ
          rcases eq_or_ne Q P with rfl | hne_Q
          · simp only [Function.update_self, stR'] at hQ ⊢
            exact hs.root_before_t hepM hQ
          · simp only [Function.update_of_ne hne_Q] at hQ ⊢
            exact hb.2.2.2.2.2.1 Q hQ
        · exact hb.2.2.2.2.2.2.1
      ext_some := hext_some
      ext_none := hext_none }

theorem filter_filter_eq_of_mem {α : Type} (l : List α) (p q₁ q₂ : α → Bool)
    (h : ∀ x ∈ l, p x = true → q₁ x = q₂ x) :
    (l.filter q₁).filter p = (l.filter p).filter q₂ := by
  rw [List.filter_filter]
  symm
  rw [List.filter_filter]
  refine List.filter_congr fun x hx => ?_
  cases hp : p x
  · simp
  · simp [h x hx hp]

theorem filter_filter_true_of_mem {α : Type} (l : List α) (p q : α → Bool)
    (h : ∀ x ∈ l, p x = true → q x = true) :
    (l.filter q).filter p = l.filter p := by
  rw [List.filter_filter]
  refine List.filter_congr fun x hx => ?_
  cases hp : p x
  · simp
  · simp [h x hx hp]

omit [DecidableEq T] [DecidableEq M] [DecidableEq E] [DecidableEq I] [Inhabited E]
  [SampleableType CCoins] [SampleableType I] [SampleableType K] in
theorem SteppedVP.accept_other
    {fs : FSAEADScheme K SS RS (Header T) M E} {Δcka qep : ℕ}
    {tL : Option ℕ} {t : ℕ} {b : Bool}
    {sL : StateL Γ T Sig SS RS M E K I} {sR : StateR Γ T Sig K I SS RS M E}
    {P : Party} {t' : ℕ}
    {s₁L : VP Γ T (Option Sig) SS RS} {s₁R : VP Γ T Sig (Option SS) (Option RS)}
    (h : ActiveInv fs Δcka qep tL t b sL sR)
    (hs : SteppedVP fs tL t sL sR P t' s₁L s₁R)
    (hne : t' ≠ t) (rs' : RS) (idx₀ : ℕ) :
    let pos : Pos := ⟨P.other, t', idx₀⟩
    let stL' := { s₁L with vR := Function.update s₁L.vR t' (some rs') }
    let stR' := { s₁R with vR := Function.update s₁R.vR t' (some (some rs')) }
    ActiveInv fs Δcka qep tL t b
      ({ sL.1 with g := sL.1.g.accept P stL' pos }, sL.2)
      ({ sR.1 with g := sR.1.g.accept P stR' pos, h := sR.1.h }, sR.2) := by
  have hpos_ne : ∀ p : Pos, p.epoch = t → (p != ⟨P.other, t', idx₀⟩) = true := by
    intro p hp
    simp only [bne_iff_ne, ne_eq]
    intro heq
    apply hne
    rw [← hp, heq]
  refine hs.accept_core h rs' (some rs') idx₀ sR.1.h sR.2 h.winFS h.bFS
    rfl rfl (fun _ => rfl) (fun ht => absurd ht hne) (fun _ => rfl) rfl
    (fun _ => ⟨rfl, rfl⟩) ?_ ?_
  · intro hext
    rcases h.ext_some hext with ⟨hheal, hcomp⟩
    refine ⟨hheal, fun r hr hrt => ?_⟩
    simp only [GameState.delete, List.mem_filter] at hr ⊢
    exact ⟨hcomp r hr.1 hrt, hpos_ne r.pos hrt⟩
  · intro hext
    have hextN := h.ext_none hext
    have htr : (sR.1.g.delete ⟨P.other, t', idx₀⟩).trans.filter (fun r => r.pos.epoch == t) =
        sR.1.g.trans.filter (fun r => r.pos.epoch == t) := by
      refine filter_filter_true_of_mem _ _ _ fun r _ hr => ?_
      simp only [beq_iff_eq] at hr
      exact hpos_ne r.pos hr
    have hch : (sR.1.g.delete ⟨P.other, t', idx₀⟩).chall.filter (fun p => p.epoch == t) =
        sR.1.g.chall.filter (fun p => p.epoch == t) := by
      refine filter_filter_true_of_mem _ _ _ fun p _ hp => ?_
      simp only [beq_iff_eq] at hp
      exact hpos_ne p hp
    refine ⟨hextN.1, hextN.2.1, hextN.2.2.1, ?_, hextN.2.2.2.2.1,
      by rw [htr, hextN.2.2.2.2.2.1], by rw [hch, hextN.2.2.2.2.2.2.1],
      hextN.2.2.2.2.2.2.2.1, ?_, hextN.2.2.2.2.2.2.2.2.2⟩
    · intro hep
      apply hextN.2.2.2.1
      rcases eq_or_ne (Party.senderOf t) P with heq | hne_P
      · rw [heq, Function.update_self] at hep
        rw [heq]
        omega
      · rw [Function.update_of_ne hne_P] at hep
        exact hep
    · intro r hr hrt
      simp only [GameState.delete, List.mem_filter] at hr ⊢
      rw [and_iff_left (hpos_ne r.pos hrt)]
      exact hextN.2.2.2.2.2.2.2.2.1 r hr.1 hrt

omit [DecidableEq T] [DecidableEq M] [DecidableEq E] [DecidableEq I] [Inhabited E]
  [SampleableType CCoins] [SampleableType I] [SampleableType K] in
theorem SteppedVP.accept_t_ext_some
    {fs : FSAEADScheme K SS RS (Header T) M E} {Δcka qep : ℕ}
    {tL : Option ℕ} {t : ℕ} {b : Bool}
    {sL : StateL Γ T Sig SS RS M E K I} {sR : StateR Γ T Sig K I SS RS M E}
    {P : Party}
    {s₁L : VP Γ T (Option Sig) SS RS} {s₁R : VP Γ T Sig (Option SS) (Option RS)}
    (h : ActiveInv fs Δcka qep tL t b sL sR)
    (hs : SteppedVP fs tL t sL sR P t s₁L s₁R)
    (ss_val : SS) (rs_val rs' : RS) (idx₀ : ℕ)
    (hext : sR.1.h.ext = some (ss_val, rs_val)) :
    let pos : Pos := ⟨P.other, t, idx₀⟩
    let stL' := { s₁L with vR := Function.update s₁L.vR t (some rs') }
    let stR' := { s₁R with vR := Function.update s₁R.vR t (some none) }
    ActiveInv fs Δcka qep tL t b
      ({ sL.1 with g := sL.1.g.accept P stL' pos }, sL.2)
      ({ sR.1 with g := sR.1.g.accept P stR' pos,
                   h := { sR.1.h with ext := some (ss_val, rs') } }, sR.2) := by
  refine hs.accept_core h rs' none idx₀ { sR.1.h with ext := some (ss_val, rs') } sR.2
    h.winFS h.bFS (by simp [curRS]) (by simp [curSS, hext])
    (fun hne => absurd rfl hne) (fun _ => rfl) (fun hne => absurd rfl hne)
    rfl (fun hne => absurd rfl hne) ?_ (by simp)
  intro _
  rcases h.ext_some (by simp [hext]) with ⟨hheal, hcomp⟩
  refine ⟨hheal, fun r hr hrt => ?_⟩
  simp only [GameState.delete, List.mem_filter] at hr ⊢
  exact ⟨hcomp r hr.1 hrt, hr.2⟩

omit [DecidableEq T] [DecidableEq M] [DecidableEq E] [DecidableEq I] [Inhabited E]
  [SampleableType CCoins] [SampleableType I] [SampleableType K] in
theorem SteppedVP.accept_t_ext_none
    {fs : FSAEADScheme K SS RS (Header T) M E} {Δcka qep : ℕ}
    {tL : Option ℕ} {t : ℕ} {b : Bool}
    {sL : StateL Γ T Sig SS RS M E K I} {sR : StateR Γ T Sig K I SS RS M E}
    {P : Party}
    {s₁L : VP Γ T (Option Sig) SS RS} {s₁R : VP Γ T Sig (Option SS) (Option RS)}
    (h : ActiveInv fs Δcka qep tL t b sL sR)
    (hs : SteppedVP fs tL t sL sR P t s₁L s₁R)
    (rs' : RS) (i' idx₀ : ℕ) (win' : Bool)
    (hwin' : win' = false)
    (hext : sR.1.h.ext = none) :
    let pos : Pos := ⟨P.other, t, idx₀⟩
    let stL' := { s₁L with vR := Function.update s₁L.vR t (some rs') }
    let stR' := { s₁R with vR := Function.update s₁R.vR t (some none) }
    let hR' := { sR.1.h with fsTrans := sR.1.h.fsTrans.filter (·.1 != idx₀) }
    let osR' := ({ sR.2 with receiverState := rs',
                             receiverIdx := max sR.2.receiverIdx i',
                             win := win' }).removeFromTransit idx₀
    ActiveInv fs Δcka qep tL t b
      ({ sL.1 with g := sL.1.g.accept P stL' pos }, sL.2)
      ({ sR.1 with g := sR.1.g.accept P stR' pos, h := hR' }, osR') := by
  intro pos stL' stR' hR' osR'
  have hPo : P.other = Party.senderOf t := by rw [hs.P_eq, Party.other_receiverOf]
  have hpos_eq : ∀ p : Pos, p.sender = Party.senderOf p.epoch → p.epoch = t →
      (p != pos) = (p.idx != idx₀) := by
    rintro ⟨s, e, i⟩ hps hpe
    dsimp only [pos] at hps hpe ⊢
    subst hpe hps
    rw [Bool.eq_iff_iff, bne_iff_ne, bne_iff_ne, ne_eq, ne_eq, hPo]
    exact ⟨fun h heq => h (congrArg _ heq), fun h heq => h (congrArg Pos.idx heq)⟩
  refine hs.accept_core h rs' none idx₀ hR' osR'
    (by simp [osR', FSAEAD.State.removeFromTransit, hwin'])
    (by simp [osR', FSAEAD.State.removeFromTransit, h.bFS])
    (by simp [curRS, hR', osR', FSAEAD.State.removeFromTransit, hext])
    (by simp [curSS, hR', osR', FSAEAD.State.removeFromTransit, hext])
    (fun hne => absurd rfl hne) (fun _ => rfl) (fun hne => absurd rfl hne)
    rfl (fun hne => absurd rfl hne) (by simp [hR', hext]) ?_
  intro _
  have hextN := h.ext_none hext
  have hne_SP : Party.senderOf t ≠ P := by
    rw [hs.P_eq]
    exact Party.senderOf_ne_receiverOf t
  have htr : (sR.1.g.delete ⟨P.other, t, idx₀⟩).trans.filter (fun r => r.pos.epoch == t) =
      (sR.1.g.trans.filter (fun r => r.pos.epoch == t)).filter
        ((fun x : ℕ × Header T × E => x.1 != idx₀) ∘ (fun r => (r.pos.idx, r.ct.1, r.ct.2))) := by
    refine filter_filter_eq_of_mem _ _ _ _ fun r hr hrt => ?_
    simp only [beq_iff_eq] at hrt
    exact hpos_eq r.pos (h.trans_wf r hr).2.1 hrt
  have hch : (sR.1.g.delete ⟨P.other, t, idx₀⟩).chall.filter (fun p => p.epoch == t) =
      (sR.1.g.chall.filter (fun p => p.epoch == t)).filter
        ((fun x : ℕ => x != idx₀) ∘ Pos.idx) := by
    refine filter_filter_eq_of_mem _ _ _ _ fun p hp hpt => ?_
    simp only [beq_iff_eq] at hpt
    exact hpos_eq p (h.chall_wf p hp).1 hpt
  refine ⟨hextN.1, hextN.2.1, hextN.2.2.1, ?_, ?_, ?_, ?_, ?_, ?_, hextN.2.2.2.2.2.2.2.2.2⟩
  · rw [Function.update_of_ne hne_SP]
    exact hextN.2.2.2.1
  · simp only [hR', osR', FSAEAD.State.removeFromTransit, hextN.2.2.2.2.1, List.filter_map]
    rfl
  · rw [htr, ← List.filter_map, hextN.2.2.2.2.2.1]
    simp only [osR', FSAEAD.State.removeFromTransit, List.filter_map]
    rfl
  · rw [hch, ← List.filter_map, hextN.2.2.2.2.2.2.1]
    rfl
  · intro r hr
    simp only [osR', FSAEAD.State.removeFromTransit, List.mem_filter] at hr
    exact hextN.2.2.2.2.2.2.2.1 r hr.1
  · intro r hr hrt
    simp only [GameState.delete, List.mem_filter] at hr ⊢
    rw [and_iff_left hr.2]
    exact hextN.2.2.2.2.2.2.2.2.1 r hr.1 hrt

omit [DecidableEq T] [DecidableEq M] [DecidableEq E] [DecidableEq I] [Inhabited E]
  [SampleableType CCoins] [SampleableType I] [SampleableType K] in
theorem ActiveInv.trivial_of_ext_some
    {fs : FSAEADScheme K SS RS (Header T) M E} {Δcka qep : ℕ}
    {tL : Option ℕ} {t : ℕ} {b : Bool}
    {sL : StateL Γ T Sig SS RS M E K I} {sR : StateR Γ T Sig K I SS RS M E}
    (h : ActiveInv fs Δcka qep tL t b sL sR) (Q : Party) (i' : ℕ)
    (hext : sR.1.h.ext.isSome = true) :
    sR.1.g.trivial (2 + Δcka) ⟨Q, t, i'⟩ = true := by
  rcases h.ext_some hext with ⟨hheal, hcomp⟩
  simp only [GameState.trivial, hheal, Bool.not_false, Bool.and_true]
  cases hany : sR.1.g.trans.any (fun r => r.pos == ⟨Q, t, i'⟩)
  · simp
  · simp only [List.any_eq_true, beq_iff_eq] at hany
    rcases hany with ⟨r, hr, hpos⟩
    have hmem := hcomp r hr (by rw [hpos])
    rw [hpos] at hmem
    simp [hmem]

omit [DecidableEq T] [DecidableEq M] [DecidableEq E] [DecidableEq I] [Inhabited E]
  [SampleableType CCoins] [SampleableType I] [SampleableType K] in
theorem ActiveInv.trivial_of_isCompromised
    {fs : FSAEADScheme K SS RS (Header T) M E} {Δcka qep : ℕ}
    {tL : Option ℕ} {t : ℕ} {b : Bool}
    {sL : StateL Γ T Sig SS RS M E K I} {sR : StateR Γ T Sig K I SS RS M E}
    (h : ActiveInv fs Δcka qep tL t b sL sR) (Q : Party) (i' : ℕ)
    (hext : sR.1.h.ext = none)
    (hcomp_i : sR.2.isCompromised i' = true) :
    sR.1.g.trivial (2 + Δcka) ⟨Q, t, i'⟩ = true := by
  have hextN := h.ext_none hext
  have hsc : sR.2.senderCorruptedAt.isSome = true := by
    cases h1 : sR.2.senderCorruptedAt with
    | none => simp [FSAEAD.State.isCompromised, h1] at hcomp_i
    | some j => rfl
  have hheal := hextN.2.2.2.2.2.2.2.2.2.1 hsc
  simp only [GameState.trivial, hheal, Bool.not_false, Bool.and_true]
  cases hany : sR.1.g.trans.any (fun r => r.pos == ⟨Q, t, i'⟩)
  · simp
  · simp only [List.any_eq_true, beq_iff_eq] at hany
    rcases hany with ⟨r, hr, hpos⟩
    have hmem : r.pos ∈ sR.1.g.comp := by
      rw [hextN.2.2.2.2.2.2.2.2.1 r hr (by rw [hpos]), hpos]
      exact hcomp_i
    rw [hpos] at hmem
    simp [hmem]

omit [DecidableEq M] [DecidableEq I] [Inhabited E]
  [SampleableType CCoins] [SampleableType I] [SampleableType K] in
theorem ActiveInv.inTransit_deliver_t
    {fs : FSAEADScheme K SS RS (Header T) M E} {Δcka qep : ℕ}
    {tL : Option ℕ} {t : ℕ} {b : Bool}
    {sL : StateL Γ T Sig SS RS M E K I} {sR : StateR Γ T Sig K I SS RS M E}
    (h : ActiveInv fs Δcka qep tL t b sL sR) {P : Party} {c : Header T × E}
    {rR : Record M (Header T × E)}
    (hPr : P = Party.receiverOf t)
    (hct_t : c.1.1 = t)
    (hext : sR.1.h.ext = none)
    (hitr : sR.1.g.inTransit P.other c = some rR) :
    rR.pos = ⟨P.other, t, rR.pos.idx⟩ ∧
    sR.1.h.fsTrans.find? (fun x => x.2 == (c.1, c.2)) = some (rR.pos.idx, c.1, c.2) ∧
    ∃ r_fs,
      sR.2.inTransit.find?
        (fun r => @BEq.beq (Header T) instBEqOfDecidableEq r.ad c.1 && r.ct == c.2) = some r_fs ∧
      r_fs.idx = rR.pos.idx ∧
      (rR.pos.idx ∈ sR.2.challengesInTransit ↔ rR.pos ∈ sR.1.g.chall) := by
  have hextN := h.ext_none hext
  have hPo : P.other = Party.senderOf t := by rw [hPr, Party.other_receiverOf]
  have hr_mem : rR ∈ sR.1.g.trans := List.mem_of_find?_eq_some hitr
  have hr_pred := List.find?_some hitr
  simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at hr_pred
  have hr_wf := h.trans_wf rR hr_mem
  have hr_ep : rR.pos.epoch = t := by rw [hr_wf.1, hr_pred.2, hct_t]
  have hr_pos : rR.pos = ⟨P.other, t, rR.pos.idx⟩ := by
    rcases rR with ⟨⟨s, e, i⟩, msg, ct⟩
    exact congrArg₂ (Pos.mk · · i) hr_pred.1 hr_ep
  have hfind_filt :
      (sR.1.g.trans.filter (fun r => r.pos.epoch == t)).find?
        (fun r => r.pos.sender == P.other && decide (r.ct = c)) = some rR := by
    rw [find?_filter_of_imp]
    · exact hitr
    · intro r hr hq
      simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at hq ⊢
      rw [(h.trans_wf r hr).1, hq.2, hct_t]
  have hfind_congr :
      (sR.1.g.trans.filter (fun r => r.pos.epoch == t)).find?
        (fun r => (fun x : ℕ × Header T × E => x.2 == (c.1, c.2)) (r.pos.idx, r.ct.1, r.ct.2)) =
      (sR.1.g.trans.filter (fun r => r.pos.epoch == t)).find?
        (fun r => r.pos.sender == P.other && decide (r.ct = c)) := by
    refine List.find?_congr fun r hr => ?_
    simp only [List.mem_filter, beq_iff_eq] at hr
    have hrs : r.pos.sender = P.other := by rw [(h.trans_wf r hr.1).2.1, hr.2, hPo]
    rw [Bool.eq_iff_iff]
    simp [hrs, Prod.ext_iff]
  have hfs_find : sR.1.h.fsTrans.find? (fun x => x.2 == (c.1, c.2)) =
      some (rR.pos.idx, c.1, c.2) := by
    rw [hextN.2.2.2.2.1, ← hextN.2.2.2.2.2.1, List.find?_map]
    change Option.map (fun r => (r.pos.idx, r.ct.1, r.ct.2))
      ((sR.1.g.trans.filter (fun r => r.pos.epoch == t)).find?
        (fun r => (fun x : ℕ × Header T × E => x.2 == (c.1, c.2)) (r.pos.idx, r.ct.1, r.ct.2))) = _
    rw [hfind_congr, hfind_filt, ← hr_pred.2]
    rfl
  have hin_map :
      Option.map (fun r : FSAEAD.Record (Header T) M E => (r.idx, r.ad, r.ct))
        (sR.2.inTransit.find?
          (fun r => @BEq.beq (Header T) instBEqOfDecidableEq r.ad c.1 && r.ct == c.2)) =
      some (rR.pos.idx, c.1, c.2) := by
    have h1 : (fun r : FSAEAD.Record (Header T) M E =>
          @BEq.beq (Header T) instBEqOfDecidableEq r.ad c.1 && r.ct == c.2) =
        ((fun x : ℕ × Header T × E => x.2 == (c.1, c.2)) ∘ (fun r => (r.idx, r.ad, r.ct))) := by
      funext r
      rw [Bool.eq_iff_iff]
      simp [Prod.ext_iff]
    rw [h1, ← List.find?_map, ← hextN.2.2.2.2.1, hfs_find]
  rcases Option.map_eq_some_iff.mp hin_map with ⟨r_fs, hr_fs, hr_fs_eq⟩
  have hidx_eq : r_fs.idx = rR.pos.idx := by injection hr_fs_eq
  refine ⟨hr_pos, hfs_find, r_fs, hr_fs, hidx_eq, ?_⟩
  rw [← hextN.2.2.2.2.2.2.1]
  simp only [List.mem_map, List.mem_filter, beq_iff_eq]
  constructor
  · rintro ⟨⟨s, e, i⟩, ⟨hp, hpt⟩, hp_idx⟩
    have hps : s = P.other := by
      have h1 := (h.chall_wf ⟨s, e, i⟩ hp).1
      dsimp only at h1 hpt hp_idx
      rw [h1, hpt, hPo]
    dsimp only at hpt hp_idx
    subst hps hpt hp_idx
    exact hr_pos ▸ hp
  · intro hp
    exact ⟨rR.pos, ⟨hp, hr_ep⟩, rfl⟩

omit [DecidableEq M] [DecidableEq I] [Inhabited E]
  [SampleableType CCoins] [SampleableType I] [SampleableType K] in
theorem ActiveInv.inTransit_inject_t
    {fs : FSAEADScheme K SS RS (Header T) M E} {Δcka qep : ℕ}
    {tL : Option ℕ} {t : ℕ} {b : Bool}
    {sL : StateL Γ T Sig SS RS M E K I} {sR : StateR Γ T Sig K I SS RS M E}
    (h : ActiveInv fs Δcka qep tL t b sL sR) {P : Party} {c : Header T × E}
    (hPr : P = Party.receiverOf t)
    (hext : sR.1.h.ext = none)
    (hitr : (sR.1.g.inTransit P.other c).isSome = false) :
    sR.1.h.fsTrans.find? (fun x => x.2 == (c.1, c.2)) = none ∧
    (¬∃ r ∈ sR.2.inTransit, r.ad = c.1 ∧ r.ct = c.2) := by
  have hextN := h.ext_none hext
  have hPo : P.other = Party.senderOf t := by rw [hPr, Party.other_receiverOf]
  simp only [Option.isSome_eq_false_iff, Option.isNone_iff_eq_none, GameState.inTransit,
    List.find?_eq_none, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq, not_and] at hitr
  have hnone : ∀ x ∈ sR.1.h.fsTrans, (x.2 == (c.1, c.2)) = false := by
    intro x hx
    rw [hextN.2.2.2.2.1, ← hextN.2.2.2.2.2.1, List.mem_map] at hx
    rcases hx with ⟨r, hr, rfl⟩
    simp only [List.mem_filter, beq_iff_eq] at hr
    have hrs : r.pos.sender = P.other := by rw [(h.trans_wf r hr.1).2.1, hr.2, hPo]
    have hne : r.ct ≠ c := hitr r hr.1 hrs
    simp only [beq_eq_false_iff_ne, ne_eq]
    intro heq
    exact hne (Prod.ext (by injection heq) (by injection heq))
  refine ⟨List.find?_eq_none.mpr (fun x hx => by simp [hnone x hx]), ?_⟩
  rintro ⟨r, hr, had, hct⟩
  have hmem : (r.idx, r.ad, r.ct) ∈ sR.1.h.fsTrans := by
    rw [hextN.2.2.2.2.1]
    exact List.mem_map_of_mem hr
  have h1 := hnone (r.idx, r.ad, r.ct) hmem
  simp [had, hct] at h1

theorem EState_mk_false_eq {VPt M C HS : Type} {es : EState VPt M C HS}
    (h : es.abort = false) :
    ({ g := es.g, h := es.h, abort := false } : EState VPt M C HS) = es := by
  cases es; dsimp only at h; subst h; rfl

omit [DecidableEq M] [Inhabited E] in
theorem hooksFS_fsRecv_some (cka : CKAScheme KC Γ CCoins T I) (prng : PRFPRNG KR Sig I K)
    (fs : FSAEADScheme K SS RS (Header T) M E) (Δcka : ℕ) (mo : Mode) (j : ℕ)
    (g : Ctx Γ T Sig (Option SS) (Option RS) M E) (P : Party) (t' : ℕ)
    (rs : RS) (hdr : Header T) (e : E) (rec : Option (Record M (Header T × E)))
    (s : FSState T Sig K I SS RS E) :
    ((hooksFS cka prng fs Δcka mo j).fsRecv g P t' (some rs) hdr e rec).run s =
      pure (some ((fs.receive rs hdr e).map fun o => (some o.1, o.2)), s) := rfl

omit [DecidableEq M] [Inhabited E] in
theorem hooksFS_fsRecv_ext_some (cka : CKAScheme KC Γ CCoins T I) (prng : PRFPRNG KR Sig I K)
    (fs : FSAEADScheme K SS RS (Header T) M E) (Δcka : ℕ) (mo : Mode) (j : ℕ)
    (g : Ctx Γ T Sig (Option SS) (Option RS) M E) (P : Party) (t' : ℕ)
    (hdr : Header T) (e : E) (rec : Option (Record M (Header T × E)))
    (s : FSState T Sig K I SS RS E) (ss_val : SS) (rs_val : RS)
    (hext : s.ext = some (ss_val, rs_val)) :
    ((hooksFS cka prng fs Δcka mo j).fsRecv g P t' none hdr e rec).run s =
      pure (match fs.receive rs_val hdr e with
        | none => (some none, s)
        | some (rs', i, m) =>
          (some (some (none, i, m)), { s with ext := some (ss_val, rs') })) := by
  simp only [hooksFS, StateT.run_bind, StateT.run_get, pure_bind, hext]
  cases fs.receive rs_val hdr e <;> rfl

omit [DecidableEq M] [Inhabited E] in
theorem hooksFS_fsRecv_deliver (cka : CKAScheme KC Γ CCoins T I) (prng : PRFPRNG KR Sig I K)
    (fs : FSAEADScheme K SS RS (Header T) M E) (Δcka : ℕ) (mo : Mode) (j : ℕ)
    (g : Ctx Γ T Sig (Option SS) (Option RS) M E) (P : Party) (t' : ℕ)
    (hdr : Header T) (e : E) (rec : Option (Record M (Header T × E)))
    (s : FSState T Sig K I SS RS E) (idx : ℕ) (ad' : Header T) (ct' : E)
    (hext : s.ext = none)
    (hfind : s.fsTrans.find? (fun x => x.2 == (hdr, e)) = some (idx, ad', ct')) :
    ((hooksFS cka prng fs Δcka mo j).fsRecv g P t' none hdr e rec).run s =
      (do
        let (res, s₀) ← (liftF (FSAEAD.deliverQuery hdr e)).run s
        match res with
        | none => return (none, s₀)
        | some .rejected => return (some none, s₀)
        | some (.accepted i mo') =>
          let s' := { s₀ with fsTrans := s₀.fsTrans.filter (·.1 != idx) }
          match mo', rec with
          | some m, _ => return (some (some (none, i, m)), s')
          | none, some r => return (some (some (none, i, r.msg)), s')
          | none, none => return (none, s')) := by
  simp only [hooksFS, StateT.run_bind, StateT.run_get, pure_bind, hext, hfind,
    Option.isSome_some, ↓reduceIte, Option.map_some, Option.getD_some]
  refine bind_congr fun ⟨res, s₀⟩ => ?_
  rcases res with _ | _ | ⟨i, _ | m⟩ <;> cases rec <;> rfl

omit [DecidableEq M] [Inhabited E] in
theorem hooksFS_fsRecv_inject (cka : CKAScheme KC Γ CCoins T I) (prng : PRFPRNG KR Sig I K)
    (fs : FSAEADScheme K SS RS (Header T) M E) (Δcka : ℕ) (mo : Mode) (j : ℕ)
    (g : Ctx Γ T Sig (Option SS) (Option RS) M E) (P : Party) (t' : ℕ)
    (hdr : Header T) (e : E) (rec : Option (Record M (Header T × E)))
    (s : FSState T Sig K I SS RS E)
    (hext : s.ext = none)
    (hfind : s.fsTrans.find? (fun x => x.2 == (hdr, e)) = none) :
    ((hooksFS cka prng fs Δcka mo j).fsRecv g P t' none hdr e rec).run s =
      (do
        let (res, s₀) ← (liftF (FSAEAD.injectQuery hdr e)).run s
        match res with
        | none => return (none, s₀)
        | some .rejected => return (some none, s₀)
        | some (.accepted i mo') =>
          let s' := { s₀ with fsTrans := s₀.fsTrans.filter (·.1 != i) }
          match mo', rec with
          | some m, _ => return (some (some (none, i, m)), s')
          | none, some r => return (some (some (none, i, r.msg)), s')
          | none, none => return (none, s')) := by
  simp only [hooksFS, StateT.run_bind, StateT.run_get, pure_bind, hext, hfind,
    Option.isSome_none, Bool.false_eq_true, ↓reduceIte, Option.map_none, Option.getD_none]
  refine bind_congr fun ⟨res, s₀⟩ => ?_
  rcases res with _ | _ | ⟨i, _ | m⟩ <;> cases rec <;> rfl

omit [DecidableEq M] [DecidableEq E] [DecidableEq I] [Inhabited E]
  [SampleableType I] [SampleableType K] in
theorem StateT_run_commitE_prng (cka : CKAScheme KC Γ CCoins T I) (prng : PRFPRNG KR Sig I K)
    (fs : FSAEADScheme K SS RS (Header T) M E) (mo : Mode)
    (s : Ctx Γ T (Option Sig) SS RS M E) (P : Party)
    (old new : VP Γ T (Option Sig) SS RS) (pos : Pos)
    (es : EState (VP Γ T (Option Sig) SS RS) M (Header T × E) (PRNGState T Sig K)) :
    (commitE (hooksPRNG cka prng fs mo) s P old new pos).run es =
      pure (some (s.accept P new pos), es) := by
  simp [commitE, hooksPRNG, StateT_run_liftH, accept_update_st_self]

omit [DecidableEq M] [Inhabited E] in
theorem StateT_run_commitE_fs (cka : CKAScheme KC Γ CCoins T I) (prng : PRFPRNG KR Sig I K)
    (fs : FSAEADScheme K SS RS (Header T) M E) (Δcka : ℕ) (mo : Mode) (j : ℕ)
    (s : Ctx Γ T Sig (Option SS) (Option RS) M E) (P : Party)
    (old new : VP Γ T Sig (Option SS) (Option RS)) (pos : Pos)
    (es : EState (VP Γ T Sig (Option SS) (Option RS)) M (Header T × E) (FSState T Sig K I SS RS E)) :
    (commitE (hooksFS cka prng fs Δcka mo j) s P old new pos).run es =
      pure (some (s.accept P new pos), es) := by
  simp [commitE, hooksFS, StateT_run_liftH, accept_update_st_self]

theorem closeBy_deliverE (cka : CKAScheme KC Γ CCoins T I) (prng : PRFPRNG KR Sig I K)
    (fs : FSAEADScheme K SS RS (Header T) M E) (Δcka qep : ℕ) (tL : Option ℕ) (t : ℕ) (b : Bool)
    (P : Party) (c : Header T × E)
    (k : (AdvSpec Γ T Sig SS RS M CCoins E).Range
        (Sum.inr (Sum.inl (Sum.inl (Sum.inr (P, c))))) →
      OracleComp (AdvSpec Γ T Sig SS RS M CCoins E) Bool)
    (sL : StateL Γ T Sig SS RS M E K I) (sR : StateR Γ T Sig K I SS RS M E)
    (h : ActiveInv fs Δcka qep tL t b sL sR)
    (ih : ∀ u sL₁ sR₁, Inv15 fs Δcka qep tL t b sL₁ sR₁ →
      CloseByEng cka prng fs Δcka qep tL t b (k u) sL₁ sR₁) :
    CloseByEng cka prng fs Δcka qep tL t b
      (query (Sum.inr (Sum.inl (Sum.inl (Sum.inr (P, c))))) >>= k) sL sR := by
  have hesL := EState_mk_false_eq h.abortL
  have hesR := EState_mk_false_eq h.abortR
  have hmap := h.inTransit_map_eq P.other c
  cases hitr : sR.1.g.inTransit P.other c with
  | none =>
    rw [hitr, Option.map_none, Option.map_eq_none_iff] at hmap
    refine closeBy_of_det_step cka prng fs Δcka qep tL t b
      (Sum.inr (Sum.inl (Sum.inl (Sum.inr (P, c))))) k
      sL sL sR sR none none ?_ ?_ ih (Or.inr ⟨rfl, Or.inr h⟩)
    · simp [runEM, implE, deliverE, h.abortL, h.winL, hmap]
    · simp [runEM, implE, deliverE, h.abortR, h.winR, hitr]
  | some rR =>
    rw [hitr, Option.map_some, Option.map_eq_some_iff] at hmap
    rcases hmap with ⟨rL, hitrL, hr_eq⟩
    have hrpos_eq : rL.pos = rR.pos := by injection hr_eq
    have hr_mem : rR ∈ sR.1.g.trans := List.mem_of_find?_eq_some hitr
    have hr_pred := List.find?_some hitr
    simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at hr_pred
    have hr_wf := h.trans_wf rR hr_mem
    have hr_ep : rR.pos.epoch = c.1.1 := by rw [hr_wf.1, hr_pred.2]
    have hr_pos : rR.pos = ⟨P.other, c.1.1, rR.pos.idx⟩ := by
      rcases rR with ⟨⟨s, e, i⟩, msg, ct⟩
      exact congrArg₂ (Pos.mk · · i) hr_pred.1 hr_ep
    rcases h.prepRecv cka prng P c (some rL) (some rR) with
      ⟨hvL, hvR⟩ | ⟨s₁L, s₁R, rsv, hs, hvR_R, hvR_L, hvL, hvR⟩
    · refine closeBy_of_det_step cka prng fs Δcka qep tL t b
        (Sum.inr (Sum.inl (Sum.inl (Sum.inr (P, c))))) k
        sL sL sR sR (some .rejected) (some .rejected) ?_ ?_ ih (Or.inr ⟨rfl, Or.inr h⟩)
      · simp [runEM, implE, deliverE, Config.priv, StateT_run_liftH, hesL,
          h.abortL, h.winL, hitrL, hvL]
      · simp [runEM, implE, deliverE, Config.priv, StateT_run_liftH, hesR,
          h.abortR, h.winR, hitr, hvR]
    · rcases eq_or_ne t c.1.1 with rfl | hne_t
      · have hvR_t := hs.vR_t_receiver hs.P_eq
        simp only [Nat.le_max_right, ↓reduceIte, hvR_R] at hvR_t
        injection hvR_t with hrsv
        subst hrsv
        cases hext : sR.1.h.ext with
        | some val =>
          rcases val with ⟨ss_val, rs_val⟩
          have hcurRS : (none : Option RS).getD (curRS sR.1.h sR.2) = rs_val := by
            simp [curRS, hext]
          cases hrecv : fs.receive rs_val c.1 c.2 with
          | none =>
            refine closeBy_of_det_step cka prng fs Δcka qep tL c.1.1 b
              (Sum.inr (Sum.inl (Sum.inl (Sum.inr (P, c))))) k
              sL sL sR sR (some .rejected) (some .rejected) ?_ ?_ ih (Or.inr ⟨rfl, Or.inr h⟩)
            · simp [runEM, implE, deliverE, Config.priv, StateT_run_liftH, hesL,
                h.abortL, h.winL, hitrL, hvL, hcurRS, hrecv]
            · simp [runEM, implE, deliverE, Config.priv, StateT_run_liftH, hesR,
                h.abortR, h.winR, hitr, hvR,
                hooksFS_fsRecv_ext_some _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hext, hrecv]
          | some val =>
            rcases val with ⟨rs', i', m'⟩
            have hInv' := hs.accept_t_ext_some h ss_val rs_val rs' rR.pos.idx hext
            dsimp only at hInv'
            rw [← hr_pos] at hInv'
            let stL' := { s₁L with vR := Function.update s₁L.vR c.1.1 (some rs') }
            let stR' := { s₁R with vR := Function.update s₁R.vR c.1.1 (some none) }
            let hR' := { sR.1.h with ext := some (ss_val, rs') }
            refine closeBy_of_det_step cka prng fs Δcka qep tL c.1.1 b
              (Sum.inr (Sum.inl (Sum.inl (Sum.inr (P, c))))) k
              sL ({ sL.1 with g := sL.1.g.accept P stL' rR.pos }, sL.2)
              sR ({ sR.1 with g := sR.1.g.accept P stR' rR.pos, h := hR' }, sR.2)
              (some (.accepted c.1.1 i' (if sR.1.g.chall.contains rR.pos then none else some m')))
              (some (.accepted c.1.1 i' (if sR.1.g.chall.contains rR.pos then none else some m')))
              ?_ ?_ ih (Or.inr ⟨rfl, Or.inr hInv'⟩)
            · simp [runEM, implE, deliverE, Config.priv, StateT_run_liftH, stL',
                StateT_run_commitE_prng, h.abortL, h.winL, hitrL, hvL, hcurRS, hrecv,
                h.chall_eq, hrpos_eq]
            · simp [runEM, implE, deliverE, Config.priv, StateT_run_liftH, stR', hR',
                StateT_run_commitE_fs, h.abortR, h.winR, hitr, hvR,
                hooksFS_fsRecv_ext_some _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hext, hrecv]
        | none =>
          have hcurRS : (none : Option RS).getD (curRS sR.1.h sR.2) = sR.2.receiverState := by
            simp [curRS, hext]
          have hended : sR.2.ended = false := (h.ext_none hext).1
          rcases h.inTransit_deliver_t hs.P_eq rfl hext hitr with
            ⟨_, hfs_find, r_fs, hr_fs, hidx_eq, hchall_eq⟩
          cases hrecv : fs.receive sR.2.receiverState c.1 c.2 with
          | none =>
            let win' := sR.2.win ||
              (!sR.2.isCompromised r_fs.idx && decide (r_fs.idx ≤ sR.2.receiverIdx + fs.maxSkip + 1))
            refine closeBy_of_det_step cka prng fs Δcka qep tL c.1.1 b
              (Sum.inr (Sum.inl (Sum.inl (Sum.inr (P, c))))) k
              sL sL sR (sR.1, { sR.2 with win := win' })
              (some .rejected) (some .rejected) ?_ ?_ ih ?_
            · simp [runEM, implE, deliverE, Config.priv, StateT_run_liftH, hesL,
                h.abortL, h.winL, hitrL, hvL, hcurRS, hrecv]
            · simp [runEM, implE, deliverE, Config.priv, StateT_run_liftH, hesR,
                h.abortR, h.winR, hitr, hvR,
                hooksFS_fsRecv_deliver _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hext hfs_find,
                liftF, FSAEAD.deliverQuery, FSAEAD.oracleImpl, FSAEAD.deliverImpl,
                FSAEAD.deliver, outerFull, hended, hr_fs, hrecv, win']
            · cases hwin' : win'
              · right
                have hos : { sR.2 with win := false } = sR.2 := by
                  have hw := h.winFS
                  revert hw
                  cases sR.2
                  rintro rfl
                  rfl
                rw [hos]
                exact ⟨rfl, Or.inr h⟩
              · exact Or.inl rfl
          | some val =>
            rcases val with ⟨rs', i', m'⟩
            let win' := sR.2.win ||
              ((!sR.2.isCompromised r_fs.idx &&
                decide (r_fs.idx ≤ sR.2.receiverIdx + fs.maxSkip + 1)) &&
                (i' != r_fs.idx || m' != r_fs.msg))
            let stL' := { s₁L with vR := Function.update s₁L.vR c.1.1 (some rs') }
            let stR' := { s₁R with vR := Function.update s₁R.vR c.1.1 (some none) }
            let hR' := { sR.1.h with fsTrans := sR.1.h.fsTrans.filter (·.1 != rR.pos.idx) }
            let osR' := ({ sR.2 with receiverState := rs',
                                     receiverIdx := max sR.2.receiverIdx i',
                                     win := win' }).removeFromTransit rR.pos.idx
            refine closeBy_of_det_step cka prng fs Δcka qep tL c.1.1 b
              (Sum.inr (Sum.inl (Sum.inl (Sum.inr (P, c))))) k
              sL ({ sL.1 with g := sL.1.g.accept P stL' rR.pos }, sL.2)
              sR ({ sR.1 with g := sR.1.g.accept P stR' rR.pos, h := hR' }, osR')
              (some (.accepted c.1.1 i' (if sR.1.g.chall.contains rR.pos then none else some m')))
              (some (.accepted c.1.1 i' (if sR.1.g.chall.contains rR.pos then none else some m')))
              ?_ ?_ ih ?_
            · simp [runEM, implE, deliverE, Config.priv, StateT_run_liftH, stL',
                StateT_run_commitE_prng, h.abortL, h.winL, hitrL, hvL, hcurRS, hrecv,
                h.chall_eq, hrpos_eq]
            · by_cases hch : rR.pos ∈ sR.1.g.chall <;>
              simp [runEM, implE, deliverE, Config.priv, StateT_run_liftH, stR', hR', osR',
                StateT_run_commitE_fs, h.abortR, h.winR, hitr, hvR,
                hooksFS_fsRecv_deliver _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hext hfs_find,
                liftF, FSAEAD.deliverQuery, FSAEAD.oracleImpl, FSAEAD.deliverImpl,
                FSAEAD.deliver, outerFull, hended, hr_fs, hrecv, hidx_eq, hchall_eq, hch, win']
            · cases hwin' : win'
              · right
                have hInv' := hs.accept_t_ext_none h rs' i' rR.pos.idx win' hwin' hext
                dsimp only at hInv'
                rw [← hr_pos] at hInv'
                exact ⟨rfl, Or.inr hInv'⟩
              · left
                simp [osR', FSAEAD.State.removeFromTransit, hwin']
      · rcases Option.isSome_iff_exists.mp (hs.vR_other c.1.1 rsv hne_t.symm hvR_R).1 with ⟨rs, rfl⟩
        cases hrecv : fs.receive rs c.1 c.2 with
        | none =>
          refine closeBy_of_det_step cka prng fs Δcka qep tL t b
            (Sum.inr (Sum.inl (Sum.inl (Sum.inr (P, c))))) k
            sL sL sR sR (some .rejected) (some .rejected) ?_ ?_ ih (Or.inr ⟨rfl, Or.inr h⟩)
          · simp [runEM, implE, deliverE, Config.priv, StateT_run_liftH, hesL,
              h.abortL, h.winL, hitrL, hvL, hrecv]
          · simp [runEM, implE, deliverE, Config.priv, StateT_run_liftH, hesR,
              h.abortR, h.winR, hitr, hvR, hooksFS_fsRecv_some, hrecv]
        | some val =>
          rcases val with ⟨rs', i', m'⟩
          have hInv' := hs.accept_other h hne_t.symm rs' rR.pos.idx
          dsimp only at hInv'
          rw [← hr_pos] at hInv'
          let stL' := { s₁L with vR := Function.update s₁L.vR c.1.1 (some rs') }
          let stR' := { s₁R with vR := Function.update s₁R.vR c.1.1 (some (some rs')) }
          refine closeBy_of_det_step cka prng fs Δcka qep tL t b
            (Sum.inr (Sum.inl (Sum.inl (Sum.inr (P, c))))) k
            sL ({ sL.1 with g := sL.1.g.accept P stL' rR.pos }, sL.2)
            sR ({ sR.1 with g := sR.1.g.accept P stR' rR.pos, h := sR.1.h }, sR.2)
            (some (.accepted c.1.1 i' (if sR.1.g.chall.contains rR.pos then none else some m')))
            (some (.accepted c.1.1 i' (if sR.1.g.chall.contains rR.pos then none else some m')))
            ?_ ?_ ih (Or.inr ⟨rfl, Or.inr hInv'⟩)
          · simp [runEM, implE, deliverE, Config.priv, StateT_run_liftH, stL',
              StateT_run_commitE_prng, h.abortL, h.winL, hitrL, hvL, hrecv,
              h.chall_eq, hrpos_eq]
          · simp [runEM, implE, deliverE, Config.priv, StateT_run_liftH, stR',
              StateT_run_commitE_fs, h.abortR, h.winR, hitr, hvR, hooksFS_fsRecv_some, hrecv]

theorem closeBy_injectE (cka : CKAScheme KC Γ CCoins T I) (prng : PRFPRNG KR Sig I K)
    (fs : FSAEADScheme K SS RS (Header T) M E) (Δcka qep : ℕ) (tL : Option ℕ) (t : ℕ) (b : Bool)
    (P : Party) (c : Header T × E)
    (k : (AdvSpec Γ T Sig SS RS M CCoins E).Range
        (Sum.inr (Sum.inl (Sum.inr (P, c)))) →
      OracleComp (AdvSpec Γ T Sig SS RS M CCoins E) Bool)
    (sL : StateL Γ T Sig SS RS M E K I) (sR : StateR Γ T Sig K I SS RS M E)
    (h : ActiveInv fs Δcka qep tL t b sL sR)
    (ih : ∀ u sL₁ sR₁, Inv15 fs Δcka qep tL t b sL₁ sR₁ →
      CloseByEng cka prng fs Δcka qep tL t b (k u) sL₁ sR₁) :
    CloseByEng cka prng fs Δcka qep tL t b
      (query (Sum.inr (Sum.inl (Sum.inr (P, c)))) >>= k) sL sR := by
  have hesL := EState_mk_false_eq h.abortL
  have hesR := EState_mk_false_eq h.abortR
  have hitr_eq := h.inTransit_isSome_eq P.other c
  have hsafe_eq := h.safeInj_eq (2 + Δcka)
  cases hguard : ((sR.1.g.inTransit P.other c).isSome || !sR.1.g.safeInj (2 + Δcka))
  · simp only [Bool.or_eq_false_iff, Bool.not_eq_false'] at hguard
    rcases hguard with ⟨hitr, hsafe⟩
    rcases h.prepRecv cka prng P c none none with
      ⟨hvL, hvR⟩ | ⟨s₁L, s₁R, rsv, hs, hvR_R, hvR_L, hvL, hvR⟩
    · refine closeBy_of_det_step cka prng fs Δcka qep tL t b
        (Sum.inr (Sum.inl (Sum.inr (P, c)))) k
        sL sL sR sR (some .rejected) (some .rejected) ?_ ?_ ih (Or.inr ⟨rfl, Or.inr h⟩)
      · simp [runEM, implE, injectE, StateT_run_liftH, hesL,
          h.abortL, h.winL, hitr_eq, hitr, hsafe_eq, hsafe, hvL]
      · simp [runEM, implE, injectE, StateT_run_liftH, hesR,
          h.abortR, h.winR, hitr, hsafe, hvR]
    · have hnot_gt : ¬(qep + 1 < c.1.1) := by
        have := hs.t'_le_maxEp
        have := h.maxEp_le_qep
        omega
      rcases eq_or_ne t c.1.1 with rfl | hne_t
      · have hvR_t := hs.vR_t_receiver hs.P_eq
        simp only [Nat.le_max_right, ↓reduceIte, hvR_R] at hvR_t
        injection hvR_t with hrsv
        subst hrsv
        cases hext : sR.1.h.ext with
        | some val =>
          rcases val with ⟨ss_val, rs_val⟩
          have hcurRS : (none : Option RS).getD (curRS sR.1.h sR.2) = rs_val := by
            simp [curRS, hext]
          cases hrecv : fs.receive rs_val c.1 c.2 with
          | none =>
            refine closeBy_of_det_step cka prng fs Δcka qep tL c.1.1 b
              (Sum.inr (Sum.inl (Sum.inr (P, c)))) k
              sL sL sR sR (some .rejected) (some .rejected) ?_ ?_ ih (Or.inr ⟨rfl, Or.inr h⟩)
            · simp [runEM, implE, injectE, StateT_run_liftH, hesL,
                h.abortL, h.winL, hitr_eq, hitr, hsafe_eq, hsafe, hvL, hcurRS, hrecv]
            · simp [runEM, implE, injectE, StateT_run_liftH, hesR,
                h.abortR, h.winR, hitr, hsafe, hvR,
                hooksFS_fsRecv_ext_some _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hext, hrecv]
          | some val =>
            rcases val with ⟨rs', i', m'⟩
            have htriv : sR.1.g.trivial (2 + Δcka) ⟨P.other, c.1.1, i'⟩ = true :=
              h.trivial_of_ext_some P.other i' (by simp [hext])
            have htriv_eq := h.trivial_eq (2 + Δcka) ⟨P.other, c.1.1, i'⟩
            have hInv' := hs.accept_t_ext_some h ss_val rs_val rs' i' hext
            let stL' := { s₁L with vR := Function.update s₁L.vR c.1.1 (some rs') }
            let stR' := { s₁R with vR := Function.update s₁R.vR c.1.1 (some none) }
            let hR' := { sR.1.h with ext := some (ss_val, rs') }
            refine closeBy_of_det_step cka prng fs Δcka qep tL c.1.1 b
              (Sum.inr (Sum.inl (Sum.inr (P, c)))) k
              sL ({ sL.1 with g := sL.1.g.accept P stL' ⟨P.other, c.1.1, i'⟩ }, sL.2)
              sR ({ sR.1 with g := sR.1.g.accept P stR' ⟨P.other, c.1.1, i'⟩, h := hR' }, sR.2)
              (some (.accepted c.1.1 i' (some m')))
              (some (.accepted c.1.1 i' (some m')))
              ?_ ?_ ih (Or.inr ⟨rfl, Or.inr hInv'⟩)
            · simp [runEM, implE, injectE, StateT_run_liftH, stL',
                StateT_run_commitE_prng,
                h.abortL, h.winL, hitr_eq, hitr, hsafe_eq, hsafe, hvL, hcurRS, hrecv,
                hnot_gt, htriv_eq, htriv]
            · simp [runEM, implE, injectE, StateT_run_liftH, stR', hR',
                StateT_run_commitE_fs,
                h.abortR, h.winR, hitr, hsafe, hvR,
                hooksFS_fsRecv_ext_some _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hext, hrecv,
                hnot_gt, htriv]
        | none =>
          have hcurRS : (none : Option RS).getD (curRS sR.1.h sR.2) = sR.2.receiverState := by
            simp [curRS, hext]
          have hended : sR.2.ended = false := (h.ext_none hext).1
          rcases h.inTransit_inject_t hs.P_eq hext hitr with ⟨hfs_find, hin_any⟩
          cases hrecv : fs.receive sR.2.receiverState c.1 c.2 with
          | none =>
            refine closeBy_of_det_step cka prng fs Δcka qep tL c.1.1 b
              (Sum.inr (Sum.inl (Sum.inr (P, c)))) k
              sL sL sR sR (some .rejected) (some .rejected) ?_ ?_ ih (Or.inr ⟨rfl, Or.inr h⟩)
            · simp [runEM, implE, injectE, StateT_run_liftH, hesL,
                h.abortL, h.winL, hitr_eq, hitr, hsafe_eq, hsafe, hvL, hcurRS, hrecv]
            · simp [runEM, implE, injectE, StateT_run_liftH, hesR,
                h.abortR, h.winR, hitr, hsafe, hvR,
                hooksFS_fsRecv_inject _ _ _ _ _ _ _ _ _ _ _ _ _ hext hfs_find,
                liftF, FSAEAD.injectQuery, FSAEAD.oracleImpl, FSAEAD.injectImpl,
                FSAEAD.inject, outerFull, hended, hin_any, hrecv]
          | some val =>
            rcases val with ⟨rs', i', m'⟩
            have htriv_eq := h.trivial_eq (2 + Δcka) ⟨P.other, c.1.1, i'⟩
            let stL' := { s₁L with vR := Function.update s₁L.vR c.1.1 (some rs') }
            let stR' := { s₁R with vR := Function.update s₁R.vR c.1.1 (some none) }
            let hR' := { sR.1.h with fsTrans := sR.1.h.fsTrans.filter (·.1 != i') }
            let osR_win := ({ sR.2 with receiverState := rs',
                                        receiverIdx := max sR.2.receiverIdx i',
                                        win := true }).removeFromTransit i'
            let osR_nowin := ({ sR.2 with receiverState := rs',
                                          receiverIdx := max sR.2.receiverIdx i',
                                          win := false }).removeFromTransit i'
            cases hcomp_i : sR.2.isCompromised i'
            · cases htriv : sR.1.g.trivial (2 + Δcka) ⟨P.other, c.1.1, i'⟩
              · refine closeBy_of_det_step cka prng fs Δcka qep tL c.1.1 b
                  (Sum.inr (Sum.inl (Sum.inr (P, c)))) k
                  sL sL
                  sR ({ sR.1 with h := hR' }, osR_win)
                  (some .rejected) (some .rejected)
                  ?_ ?_ ih (Or.inl (by simp [osR_win, FSAEAD.State.removeFromTransit]))
                · simp [runEM, implE, injectE, Config.priv, StateT_run_liftH, hesL,
                    h.abortL, h.winL, hitr_eq, hitr, hsafe_eq, hsafe, hvL, hcurRS, hrecv,
                    hnot_gt, htriv_eq, htriv]
                · simp [runEM, implE, injectE, Config.priv, StateT_run_liftH, hR', osR_win,
                    h.abortR, h.winR, hitr, hsafe, hvR,
                    hooksFS_fsRecv_inject _ _ _ _ _ _ _ _ _ _ _ _ _ hext hfs_find,
                    liftF, FSAEAD.injectQuery, FSAEAD.oracleImpl, FSAEAD.injectImpl,
                    FSAEAD.inject, outerFull, hended, hin_any, hrecv, hcomp_i,
                    hnot_gt, htriv]
              · refine closeBy_of_det_step cka prng fs Δcka qep tL c.1.1 b
                  (Sum.inr (Sum.inl (Sum.inr (P, c)))) k
                  sL ({ sL.1 with g := sL.1.g.accept P stL' ⟨P.other, c.1.1, i'⟩ }, sL.2)
                  sR ({ sR.1 with g := sR.1.g.accept P stR' ⟨P.other, c.1.1, i'⟩, h := hR' }, osR_win)
                  (some (.accepted c.1.1 i' (some m')))
                  (some (.accepted c.1.1 i' (some m')))
                  ?_ ?_ ih (Or.inl (by simp [osR_win, FSAEAD.State.removeFromTransit]))
                · simp [runEM, implE, injectE, StateT_run_liftH, stL',
                    StateT_run_commitE_prng,
                    h.abortL, h.winL, hitr_eq, hitr, hsafe_eq, hsafe, hvL, hcurRS, hrecv,
                    hnot_gt, htriv_eq, htriv]
                · simp [runEM, implE, injectE, StateT_run_liftH, stR', hR', osR_win,
                    StateT_run_commitE_fs,
                    h.abortR, h.winR, hitr, hsafe, hvR,
                    hooksFS_fsRecv_inject _ _ _ _ _ _ _ _ _ _ _ _ _ hext hfs_find,
                    liftF, FSAEAD.injectQuery, FSAEAD.oracleImpl, FSAEAD.injectImpl,
                    FSAEAD.inject, outerFull, hended, hin_any, hrecv, hcomp_i,
                    hnot_gt, htriv]
            · have htriv : sR.1.g.trivial (2 + Δcka) ⟨P.other, c.1.1, i'⟩ = true :=
                h.trivial_of_isCompromised P.other i' hext hcomp_i
              have hInv' := hs.accept_t_ext_none h rs' i' i' false rfl hext
              refine closeBy_of_det_step cka prng fs Δcka qep tL c.1.1 b
                (Sum.inr (Sum.inl (Sum.inr (P, c)))) k
                sL ({ sL.1 with g := sL.1.g.accept P stL' ⟨P.other, c.1.1, i'⟩ }, sL.2)
                sR ({ sR.1 with g := sR.1.g.accept P stR' ⟨P.other, c.1.1, i'⟩, h := hR' }, osR_nowin)
                (some (.accepted c.1.1 i' (some m')))
                (some (.accepted c.1.1 i' (some m')))
                ?_ ?_ ih (Or.inr ⟨rfl, Or.inr hInv'⟩)
              · simp [runEM, implE, injectE, StateT_run_liftH, stL',
                  StateT_run_commitE_prng,
                  h.abortL, h.winL, hitr_eq, hitr, hsafe_eq, hsafe, hvL, hcurRS, hrecv,
                  hnot_gt, htriv_eq, htriv]
              · simp [runEM, implE, injectE, StateT_run_liftH, stR', hR', osR_nowin,
                  StateT_run_commitE_fs,
                  h.abortR, h.winR, hitr, hsafe, hvR,
                  hooksFS_fsRecv_inject _ _ _ _ _ _ _ _ _ _ _ _ _ hext hfs_find,
                  liftF, FSAEAD.injectQuery, FSAEAD.oracleImpl, FSAEAD.injectImpl,
                  FSAEAD.inject, outerFull, hended, hin_any, hrecv, hcomp_i, h.winFS,
                  hnot_gt, htriv]
      · rcases Option.isSome_iff_exists.mp (hs.vR_other c.1.1 rsv hne_t.symm hvR_R).1 with ⟨rs, rfl⟩
        cases hrecv : fs.receive rs c.1 c.2 with
        | none =>
          refine closeBy_of_det_step cka prng fs Δcka qep tL t b
            (Sum.inr (Sum.inl (Sum.inr (P, c)))) k
            sL sL sR sR (some .rejected) (some .rejected) ?_ ?_ ih (Or.inr ⟨rfl, Or.inr h⟩)
          · simp [runEM, implE, injectE, StateT_run_liftH, hesL,
              h.abortL, h.winL, hitr_eq, hitr, hsafe_eq, hsafe, hvL, hrecv]
          · simp [runEM, implE, injectE, StateT_run_liftH, hesR,
              h.abortR, h.winR, hitr, hsafe, hvR, hooksFS_fsRecv_some, hrecv]
        | some val =>
          rcases val with ⟨rs', i', m'⟩
          have htriv_eq := h.trivial_eq (2 + Δcka) ⟨P.other, c.1.1, i'⟩
          cases htriv : sR.1.g.trivial (2 + Δcka) ⟨P.other, c.1.1, i'⟩
          · refine closeBy_of_det_step cka prng fs Δcka qep tL t b
              (Sum.inr (Sum.inl (Sum.inr (P, c)))) k
              sL sL sR sR (some .rejected) (some .rejected) ?_ ?_ ih (Or.inr ⟨rfl, Or.inr h⟩)
            · simp [runEM, implE, injectE, Config.priv, StateT_run_liftH, hesL,
                h.abortL, h.winL, hitr_eq, hitr, hsafe_eq, hsafe, hvL, hrecv,
                hnot_gt, htriv_eq, htriv]
            · simp [runEM, implE, injectE, Config.priv, StateT_run_liftH, hesR,
                h.abortR, h.winR, hitr, hsafe, hvR, hooksFS_fsRecv_some, hrecv,
                hnot_gt, htriv]
          · have hInv' := hs.accept_other h hne_t.symm rs' i'
            let stL' := { s₁L with vR := Function.update s₁L.vR c.1.1 (some rs') }
            let stR' := { s₁R with vR := Function.update s₁R.vR c.1.1 (some (some rs')) }
            refine closeBy_of_det_step cka prng fs Δcka qep tL t b
              (Sum.inr (Sum.inl (Sum.inr (P, c)))) k
              sL ({ sL.1 with g := sL.1.g.accept P stL' ⟨P.other, c.1.1, i'⟩ }, sL.2)
              sR ({ sR.1 with g := sR.1.g.accept P stR' ⟨P.other, c.1.1, i'⟩, h := sR.1.h }, sR.2)
              (some (.accepted c.1.1 i' (some m')))
              (some (.accepted c.1.1 i' (some m')))
              ?_ ?_ ih (Or.inr ⟨rfl, Or.inr hInv'⟩)
            · simp [runEM, implE, injectE, StateT_run_liftH, stL',
                StateT_run_commitE_prng,
                h.abortL, h.winL, hitr_eq, hitr, hsafe_eq, hsafe, hvL, hrecv,
                hnot_gt, htriv_eq, htriv]
            · simp [runEM, implE, injectE, StateT_run_liftH, stR',
                StateT_run_commitE_fs,
                h.abortR, h.winR, hitr, hsafe, hvR, hooksFS_fsRecv_some, hrecv,
                hnot_gt, htriv]
  · refine closeBy_of_det_step cka prng fs Δcka qep tL t b
      (Sum.inr (Sum.inl (Sum.inr (P, c)))) k
      sL sL sR sR none none ?_ ?_ ih (Or.inr ⟨rfl, Or.inr h⟩)
    · simp [runEM, implE, injectE, h.abortL, h.winL, hitr_eq, hsafe_eq, hguard, -Bool.or_eq_true]
    · simp [runEM, implE, injectE, h.abortR, h.winR, hguard, -Bool.or_eq_true]

/-! ### Send step (`transmitE` and `challE`) -/

theorem record_update_st_self {St Msg C : Type} (s : GameState St Msg C) (Δ : ℕ)
    (P : Party) (st₁ st' : St) (r : Record Msg C) (isChall : Bool) :
    ({ s with st := Function.update s.st P st₁ } : GameState St Msg C).record Δ P st' r isChall =
      s.record Δ P st' r isChall := by
  cases s
  dsimp only [GameState.record, GameState.safeCh]
  rw [Function.update_idem]
  rfl

omit [DecidableEq T] [DecidableEq M] [DecidableEq E] [DecidableEq I] [Inhabited E]
  [SampleableType CCoins] [SampleableType I] [SampleableType K] in
theorem ActiveInv.record_core
    {fs : FSAEADScheme K SS RS (Header T) M E} {Δcka qep : ℕ}
    {tL : Option ℕ} {t : ℕ} {b : Bool}
    {sL : StateL Γ T Sig SS RS M E K I} {sR : StateR Γ T Sig K I SS RS M E}
    (h : ActiveInv fs Δcka qep tL t b sL sR)
    {P : Party} (hPs : P.sendsIn (sR.1.g.epoch P) = true)
    (mL mR : M) (isChall : Bool)
    (ss' : SS) (ssv' : Option SS) (e : E)
    (hR' : FSState T Sig K I SS RS E) (osR' : FSAEAD.State SS RS (Header T) M E)
    (hwinFS' : osR'.win = false) (hbFS' : osR'.b = b)
    (hvS_getD : ssv'.getD (curSS hR' osR') = ss')
    (hcurSS_ne : sR.1.g.epoch P ≠ t → curSS hR' osR' = curSS sR.1.h sR.2)
    (hcurRS : curRS hR' osR' = curRS sR.1.h sR.2)
    (hvS_t : sR.1.g.epoch P = t → ssv' = none)
    (hvS_ne : sR.1.g.epoch P ≠ t → ssv' = some ss')
    (hcache : hR'.cache = sR.1.h.cache)
    (ht_unchanged : sR.1.g.epoch P ≠ t → hR' = sR.1.h ∧ osR' = sR.2)
    (hrs : osR'.receiverState = sR.2.receiverState ∧ (hR'.ext = none ↔ sR.1.h.ext = none))
    (hext_some : hR'.ext.isSome = true →
      healedBy sR.1.g.tL (2 + Δcka) t = false ∧
      ∀ r ∈ (sR.1.g.record (2 + Δcka) P { sR.1.g.st P with vS := some ssv' }
        ⟨⟨P, sR.1.g.epoch P, sR.1.g.idx P + 1⟩, mR, ((sR.1.g.epoch P, (sR.1.g.st P).curCkaMsg), e)⟩
        isChall).trans,
        r.pos.epoch = t →
        r.pos ∈ (sR.1.g.record (2 + Δcka) P { sR.1.g.st P with vS := some ssv' }
          ⟨⟨P, sR.1.g.epoch P, sR.1.g.idx P + 1⟩, mR, ((sR.1.g.epoch P, (sR.1.g.st P).curCkaMsg), e)⟩
          isChall).comp)
    (hext_none : hR'.ext = none →
      let gR' := sR.1.g.record (2 + Δcka) P { sR.1.g.st P with vS := some ssv' }
        ⟨⟨P, sR.1.g.epoch P, sR.1.g.idx P + 1⟩, mR, ((sR.1.g.epoch P, (sR.1.g.st P).curCkaMsg), e)⟩
        isChall
      osR'.ended = false ∧
      hR'.fsCount = osR'.lastSentIdx ∧
      hR'.fsSCorr = osR'.senderCorruptedAt.isSome ∧
      (gR'.epoch (Party.senderOf t) = t → gR'.idx (Party.senderOf t) = osR'.lastSentIdx) ∧
      hR'.fsTrans = osR'.inTransit.map (fun r => (r.idx, r.ad, r.ct)) ∧
      ((gR'.trans.filter (fun r => r.pos.epoch == t)).map
        (fun r => (r.pos.idx, r.ct.1, r.ct.2)) =
        osR'.inTransit.map (fun r => (r.idx, r.ad, r.ct))) ∧
      ((gR'.chall.filter (fun pos => pos.epoch == t)).map Pos.idx =
        osR'.challengesInTransit) ∧
      (∀ r ∈ osR'.inTransit, r.idx ≤ osR'.lastSentIdx) ∧
      (∀ r ∈ gR'.trans, r.pos.epoch = t →
        (r.pos ∈ gR'.comp ↔ osR'.isCompromised r.pos.idx = true)) ∧
      ((osR'.senderCorruptedAt.isSome = true → healedBy gR'.tL (2 + Δcka) t = false) ∧
        (∀ j, osR'.senderCorruptedAt = some j → j ≤ osR'.lastSentIdx))) :
    let t' := sR.1.g.epoch P
    let hdr : Header T := (t', (sR.1.g.st P).curCkaMsg)
    let pos : Pos := ⟨P, t', sR.1.g.idx P + 1⟩
    let stL' := { sL.1.g.st P with vS := some ss' }
    let stR' := { sR.1.g.st P with vS := some ssv' }
    ActiveInv fs Δcka qep tL t b
      ({ sL.1 with g := sL.1.g.record (2 + Δcka) P stL' ⟨pos, mL, (hdr, e)⟩ isChall }, sL.2)
      ({ sR.1 with g := sR.1.g.record (2 + Δcka) P stR' ⟨pos, mR, (hdr, e)⟩ isChall,
                   h := hR' }, osR') := by
  intro t' hdr pos stL' stR'
  have hPs_eq : P = Party.senderOf (sR.1.g.epoch P) := (Party.sendsIn_eq_senderOf P _).mp hPs
  have hle_max : sR.1.g.epoch P ≤ max (sR.1.g.epoch .A) (sR.1.g.epoch .B) :=
    Party.le_max_apply sR.1.g.epoch P
  refine
    { abortL := h.abortL
      abortR := h.abortR
      winL := h.winL
      winR := h.winR
      winFS := hwinFS'
      bL := h.bL
      bR := h.bR
      bFS := hbFS'
      epoch_eq := h.epoch_eq
      idx_eq := by simp [GameState.record, h.idx_eq]
      tL_eq := h.tL_eq
      chall_eq := by simp [GameState.record, h.chall_eq]
      comp_eq := by simp [GameState.record, h.safeCh_eq (2 + Δcka) P, h.comp_eq]
      maxAcc_eq := h.maxAcc_eq
      leaks_eq := h.leaks_eq
      corrs_eq := h.corrs_eq
      trans_eq := by simp [GameState.record, h.trans_eq]
      idL := fun Q => by
        rcases eq_or_ne Q P with rfl | hne
        · simp [GameState.record, stL', h.idL]
        · simp [GameState.record, Function.update_of_ne hne, h.idL]
      idR := fun Q => by
        rcases eq_or_ne Q P with rfl | hne
        · simp [GameState.record, stR', h.idR]
        · simp [GameState.record, Function.update_of_ne hne, h.idR]
      tcurL := fun Q => by
        rcases eq_or_ne Q P with rfl | hne
        · simp [GameState.record, stL', h.tcurL]
        · simp [GameState.record, Function.update_of_ne hne, h.tcurL]
      tcurR := fun Q => by
        rcases eq_or_ne Q P with rfl | hne
        · simp [GameState.record, stR', h.tcurR]
        · simp [GameState.record, Function.update_of_ne hne, h.tcurR]
      γ_eq := fun Q => by
        rcases eq_or_ne Q P with rfl | hne
        · simp [GameState.record, stL', stR', h.γ_eq]
        · simp [GameState.record, Function.update_of_ne hne, h.γ_eq]
      Tcur_eq := fun Q => by
        rcases eq_or_ne Q P with rfl | hne
        · simp [GameState.record, stL', stR', h.Tcur_eq]
        · simp [GameState.record, Function.update_of_ne hne, h.Tcur_eq]
      root_eq := fun Q => by
        rcases eq_or_ne Q P with rfl | hne
        · simp [GameState.record, stL', stR', h.root_eq]
        · simp [GameState.record, Function.update_of_ne hne, h.root_eq]
      vS_eq := fun Q => by
        rcases eq_or_ne Q P with rfl | hne_Q
        · simp [GameState.record, stL', stR', hvS_getD]
        · simp only [GameState.record, Function.update_of_ne hne_Q, h.vS_eq Q]
          rcases eq_or_ne (sR.1.g.epoch P) t with ht | hne_t
          · rcases hv : (sR.1.g.st Q).vS with _ | _ | ss
            · rfl
            · have h1 := (h.vS_none Q hv).1
              rw [← ht, ← hPs_eq] at h1
              exact absurd h1 hne_Q
            · rfl
          · rw [hcurSS_ne hne_t]
      vR_eq := fun Q t'' => by
        rcases eq_or_ne Q P with rfl | hne_Q
        · simp [GameState.record, stL', stR', hcurRS, h.vR_eq]
        · simp [GameState.record, Function.update_of_ne hne_Q, hcurRS, h.vR_eq]
      sender_epoch := h.sender_epoch
      receiver_epoch := h.receiver_epoch
      maxEp_le_qep := h.maxEp_le_qep
      tL_le_maxEp := h.tL_le_maxEp
      vS_none := fun Q hvS => by
        simp only [GameState.record] at hvS ⊢
        rcases eq_or_ne Q P with rfl | hne_Q
        · simp only [Function.update_self, stR', Option.some.injEq] at hvS
          have ht : sR.1.g.epoch Q = t := by
            by_contra hne_t
            rw [hvS_ne hne_t] at hvS
            cases hvS
          exact ⟨ht ▸ hPs_eq, le_of_eq ht.symm⟩
        · simp only [Function.update_of_ne hne_Q] at hvS
          exact h.vS_none Q hvS
      vS_sending := fun Q hQs => by
        simp only [GameState.record] at hQs ⊢
        rcases eq_or_ne Q P with rfl | hne_Q
        · simp only [Function.update_self, stR']
          exact ⟨fun ht => by rw [hvS_t ht], fun hne_t => ⟨ss', by rw [hvS_ne hne_t]⟩⟩
        · simp only [Function.update_of_ne hne_Q]
          exact h.vS_sending Q hQs
      vR_sender := by
        simp only [GameState.record]
        rcases eq_or_ne (Party.senderOf t) P with heq | hne
        · rw [heq, Function.update_self]; dsimp only [stR']; rw [← heq]; exact h.vR_sender
        · rw [Function.update_of_ne hne]; exact h.vR_sender
      vR_receiver := by
        simp only [GameState.record]
        rcases eq_or_ne (Party.receiverOf t) P with heq | hne
        · rw [heq, Function.update_self]; dsimp only [stR']; rw [← heq]; exact h.vR_receiver
        · rw [Function.update_of_ne hne]; exact h.vR_receiver

      vR_other := fun Q t'' x hne_t hv => by
        simp only [GameState.record] at hv ⊢
        rcases eq_or_ne Q P with rfl | hne_Q
        · rw [Function.update_self] at hv
          exact h.vR_other Q t'' x hne_t hv
        · rw [Function.update_of_ne hne_Q] at hv
          exact h.vR_other Q t'' x hne_t hv
      cache_none := fun t'' ht'' => by
        rw [hcache]; exact h.cache_none t'' ht''
      cache_other := fun t'' ht'' => by
        rw [hcache]; exact h.cache_other t'' ht''
      cache_other_ext := fun t'' Tc σc kc ext ht'' hc => by
        rw [hcache] at hc; exact h.cache_other_ext t'' Tc σc kc ext ht'' hc
      cache_t_none := fun hc => by
        rw [hcache] at hc; exact h.cache_t_none hc
      cache_t := fun Tc σc kc ext hc => by
        rw [hcache] at hc
        rcases h.cache_t Tc σc kc ext hc with ⟨hext, k₀, hcL, hrec⟩
        refine ⟨hext, k₀, hcL, fun hlt => ?_⟩
        rw [hrs.1, hrs.2]
        exact hrec hlt
      trans_wf := fun r hr => by
        simp only [GameState.record, List.mem_cons] at hr ⊢
        rcases hr with rfl | hr
        · exact ⟨rfl, hPs_eq, hle_max⟩
        · exact h.trans_wf r hr
      chall_wf := fun p hp => by
        simp only [GameState.record] at hp ⊢
        split_ifs at hp with hch
        · simp only [List.mem_cons] at hp
          rcases hp with rfl | hp
          · exact ⟨hPs_eq, hle_max⟩
          · exact h.chall_wf p hp
        · exact h.chall_wf p hp
      comp_t := fun p hp hpe => by
        simp only [GameState.record] at hp ⊢
        split_ifs at hp with hsafe
        · exact h.comp_t p hp hpe
        · simp only [List.mem_cons] at hp
          rcases hp with rfl | hp
          · dsimp only [pos, t'] at hpe
            simp only [GameState.safeCh, hpe, Bool.not_eq_true] at hsafe
            exact hsafe
          · exact h.comp_t p hp hpe
      before_t := by
        simp only [GameState.record]
        intro hepM
        have hne_t : sR.1.g.epoch P ≠ t := by omega
        rcases ht_unchanged hne_t with ⟨rfl, rfl⟩
        have hb := h.before_t hepM
        refine ⟨hb.1, hb.2.1, hb.2.2.1, hb.2.2.2.1, hb.2.2.2.2.1, ?_, ?_, hb.2.2.2.2.2.2.2⟩
        · intro Q hQ
          rcases eq_or_ne Q P with rfl | hne_Q
          · simp only [Function.update_self, stR']
            exact hb.2.2.2.2.2.1 Q hQ
          · simp only [Function.update_of_ne hne_Q]
            exact hb.2.2.2.2.2.1 Q hQ
        · exact hb.2.2.2.2.2.2.1
      ext_some := hext_some
      ext_none := hext_none }

omit [DecidableEq T] [DecidableEq M] [DecidableEq E] [DecidableEq I] [Inhabited E]
  [SampleableType CCoins] [SampleableType I] [SampleableType K] in
theorem ActiveInv.record_other
    {fs : FSAEADScheme K SS RS (Header T) M E} {Δcka qep : ℕ}
    {tL : Option ℕ} {t : ℕ} {b : Bool}
    {sL : StateL Γ T Sig SS RS M E K I} {sR : StateR Γ T Sig K I SS RS M E}
    (h : ActiveInv fs Δcka qep tL t b sL sR)
    {P : Party} (hPs : P.sendsIn (sR.1.g.epoch P) = true)
    (hne : sR.1.g.epoch P ≠ t)
    (mL mR : M) (ss' : SS) (e : E) :
    let t' := sR.1.g.epoch P
    let hdr : Header T := (t', (sR.1.g.st P).curCkaMsg)
    let pos : Pos := ⟨P, t', sR.1.g.idx P + 1⟩
    let stL' := { sL.1.g.st P with vS := some ss' }
    let stR' := { sR.1.g.st P with vS := some (some ss') }
    ActiveInv fs Δcka qep tL t b
      ({ sL.1 with g := sL.1.g.record (2 + Δcka) P stL' ⟨pos, mL, (hdr, e)⟩ false }, sL.2)
      ({ sR.1 with g := sR.1.g.record (2 + Δcka) P stR' ⟨pos, mR, (hdr, e)⟩ false,
                   h := sR.1.h }, sR.2) := by
  refine h.record_core hPs mL mR false ss' (some ss') e sR.1.h sR.2
    h.winFS h.bFS rfl (fun _ => rfl) rfl (fun ht => absurd ht hne) (fun _ => rfl)
    rfl (fun _ => ⟨rfl, rfl⟩) ⟨rfl, Iff.rfl⟩ ?_ ?_
  · intro hext
    rcases h.ext_some hext with ⟨hheal, hcomp⟩
    refine ⟨hheal, fun r hr hrt => ?_⟩
    simp only [GameState.record, List.mem_cons] at hr ⊢
    rcases hr with rfl | hr
    · exact absurd hrt hne
    · have hc := hcomp r hr hrt
      split_ifs
      · exact hc
      · exact List.mem_cons_of_mem _ hc
  · intro hext
    have hextN := h.ext_none hext
    refine ⟨hextN.1, hextN.2.1, hextN.2.2.1, ?_, hextN.2.2.2.2.1, ?_, hextN.2.2.2.2.2.2.1,
      hextN.2.2.2.2.2.2.2.1, ?_, hextN.2.2.2.2.2.2.2.2.2⟩
    · intro hep
      simp only [GameState.record] at hep ⊢
      have hne_SP : Party.senderOf t ≠ P := fun heq => hne (heq ▸ hep)
      rw [Function.update_of_ne hne_SP]
      exact hextN.2.2.2.1 hep
    · have hflt : ¬((sR.1.g.epoch P == t) = true) := by simp [hne]
      simp only [GameState.record, List.filter_cons, hflt]
      exact hextN.2.2.2.2.2.1

    · intro r hr hrt
      simp only [GameState.record, List.mem_cons] at hr ⊢
      rcases hr with rfl | hr
      · exact absurd hrt hne
      · have hiff := hextN.2.2.2.2.2.2.2.2.1 r hr hrt
        split_ifs
        · exact hiff
        · simp only [List.mem_cons]
          have hne_pos : r.pos ≠ ⟨P, sR.1.g.epoch P, sR.1.g.idx P + 1⟩ := by
            intro heq
            have : r.pos.epoch = sR.1.g.epoch P := by rw [heq]
            exact hne (this.symm.trans hrt)
          simp [hne_pos, hiff]

omit [DecidableEq T] [DecidableEq M] [DecidableEq E] [DecidableEq I] [Inhabited E]
  [SampleableType CCoins] [SampleableType I] [SampleableType K] in
theorem ActiveInv.record_t_ext_some
    {fs : FSAEADScheme K SS RS (Header T) M E} {Δcka qep : ℕ}
    {tL : Option ℕ} {t : ℕ} {b : Bool}
    {sL : StateL Γ T Sig SS RS M E K I} {sR : StateR Γ T Sig K I SS RS M E}
    (h : ActiveInv fs Δcka qep tL t b sL sR)
    {P : Party} (hPs : P.sendsIn (sR.1.g.epoch P) = true)
    (ht : sR.1.g.epoch P = t)
    {ss_val : SS} {rs_val : RS} (hext : sR.1.h.ext = some (ss_val, rs_val))
    (m : M) (ss' : SS) (e : E) :
    let t' := sR.1.g.epoch P
    let hdr : Header T := (t', (sR.1.g.st P).curCkaMsg)
    let pos : Pos := ⟨P, t', sR.1.g.idx P + 1⟩
    let stL' := { sL.1.g.st P with vS := some ss' }
    let stR' := { sR.1.g.st P with vS := some none }
    let hR' := { sR.1.h with ext := some (ss', rs_val) }
    ActiveInv fs Δcka qep tL t b
      ({ sL.1 with g := sL.1.g.record (2 + Δcka) P stL' ⟨pos, m, (hdr, e)⟩ false }, sL.2)
      ({ sR.1 with g := sR.1.g.record (2 + Δcka) P stR' ⟨pos, m, (hdr, e)⟩ false,
                   h := hR' }, sR.2) := by
  refine h.record_core hPs m m false ss' none e
    { sR.1.h with ext := some (ss', rs_val) } sR.2
    h.winFS h.bFS rfl (fun hne => absurd ht hne)
    (by simp [curRS, hext]) (fun _ => rfl) (fun hne => absurd ht hne)
    rfl (fun hne => absurd ht hne) (by simp [hext]) ?_ (by intro hnone; simp at hnone)
  intro _
  rcases h.ext_some (by simp [hext]) with ⟨hheal, hcomp⟩
  have hsafe : sR.1.g.safeCh (2 + Δcka) P = false := by
    simp [GameState.safeCh, ht, hheal]
  refine ⟨hheal, fun r hr hrt => ?_⟩
  simp only [GameState.record, hsafe, Bool.false_eq_true, ↓reduceIte, List.mem_cons] at hr ⊢
  rcases hr with rfl | hr
  · exact Or.inl rfl
  · exact Or.inr (hcomp r hr hrt)

omit [DecidableEq T] [DecidableEq M] [DecidableEq E] [DecidableEq I] [Inhabited E]
  [SampleableType CCoins] [SampleableType I] [SampleableType K] in
theorem ActiveInv.record_t_ext_none
    {fs : FSAEADScheme K SS RS (Header T) M E} {Δcka qep : ℕ}
    {tL : Option ℕ} {t : ℕ} {b : Bool}
    {sL : StateL Γ T Sig SS RS M E K I} {sR : StateR Γ T Sig K I SS RS M E}
    (h : ActiveInv fs Δcka qep tL t b sL sR)
    {P : Party} (hPs : P.sendsIn (sR.1.g.epoch P) = true)
    (ht : sR.1.g.epoch P = t)
    (hext : sR.1.h.ext = none)
    (mL mR : M) (isChall : Bool)
    (ss' : SS) (e : E) :
    let t' := sR.1.g.epoch P
    let hdr : Header T := (t', (sR.1.g.st P).curCkaMsg)
    let pos : Pos := ⟨P, t', sR.1.g.idx P + 1⟩
    let stL' := { sL.1.g.st P with vS := some ss' }
    let stR' := { sR.1.g.st P with vS := some none }
    let corrAt' : Option ℕ :=
      if sR.1.g.safeCh (2 + Δcka) P then sR.2.senderCorruptedAt
      else some (sR.2.senderCorruptedAt.getD sR.2.lastSentIdx)
    let i := sR.2.lastSentIdx + 1
    let hR' : FSState T Sig K I SS RS E :=
      { sR.1.h with
          fsSCorr := corrAt'.isSome
          fsCount := i
          fsTrans := (i, hdr, e) :: sR.1.h.fsTrans }
    let osR' : FSAEAD.State SS RS (Header T) M E :=
      { sR.2 with
          senderState := ss'
          lastSentIdx := i
          senderCorruptedAt := corrAt'
          inTransit := ⟨i, hdr, mL, e⟩ :: sR.2.inTransit
          challengesInTransit :=
            if isChall then i :: sR.2.challengesInTransit else sR.2.challengesInTransit }
    ActiveInv fs Δcka qep tL t b
      ({ sL.1 with g := sL.1.g.record (2 + Δcka) P stL' ⟨pos, mL, (hdr, e)⟩ isChall }, sL.2)
      ({ sR.1 with g := sR.1.g.record (2 + Δcka) P stR' ⟨pos, mR, (hdr, e)⟩ isChall,
                   h := hR' }, osR') := by
  intro t' hdr pos stL' stR' corrAt' i hR' osR'
  have hPs_eq : P = Party.senderOf t := ht ▸ (Party.sendsIn_eq_senderOf P _).mp hPs
  have hextN := h.ext_none hext
  have hidxP : sR.1.g.idx P = sR.2.lastSentIdx := by
    rw [hPs_eq]
    exact hextN.2.2.2.1 (hPs_eq ▸ ht)
  refine h.record_core hPs mL mR isChall ss' none e hR' osR'
    h.winFS h.bFS (by simp [curSS, hR', osR', hext]) (fun hne => absurd ht hne)
    (by simp [curRS, hR', osR', hext]) (fun _ => rfl) (fun hne => absurd ht hne)
    rfl (fun hne => absurd ht hne) (by simp [hR', osR', hext])
    (by intro hs; simp [hR', hext] at hs) ?_
  intro _
  refine ⟨hextN.1, rfl, rfl, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro _
    simp only [GameState.record, ← hPs_eq, Function.update_self, hidxP, osR', i]
  · simp only [hR', osR', List.map_cons, hextN.2.2.2.2.1]
  · simp only [GameState.record, List.filter_cons, ht, beq_self_eq_true, ↓reduceIte,
      List.map_cons, hidxP, osR', hdr, t', i, hextN.2.2.2.2.2.1]
  · cases isChall
    · simp only [GameState.record, Bool.false_eq_true, ↓reduceIte, osR', hextN.2.2.2.2.2.2.1]
    · simp only [GameState.record, ↓reduceIte, List.filter_cons, ht, beq_self_eq_true,
        List.map_cons, hidxP, osR', i, hextN.2.2.2.2.2.2.1]
  · intro r hr
    simp only [osR', List.mem_cons] at hr ⊢
    rcases hr with rfl | hr
    · exact le_rfl
    · have := hextN.2.2.2.2.2.2.2.1 r hr
      dsimp only [i]
      omega
  · intro r hr hrt
    have hmem_idx : ∀ r₀ ∈ sR.1.g.trans, r₀.pos.epoch = t → r₀.pos.idx ≤ sR.2.lastSentIdx := by
      intro r₀ hr₀ hrt₀
      have hflt : (r₀.pos.idx, r₀.ct.1, r₀.ct.2) ∈
          (sR.1.g.trans.filter (fun r => r.pos.epoch == t)).map
            (fun r => (r.pos.idx, r.ct.1, r.ct.2)) := by
        rw [List.mem_map]
        exact ⟨r₀, List.mem_filter.mpr ⟨hr₀, by simp [hrt₀]⟩, rfl⟩
      rw [hextN.2.2.2.2.2.1, List.mem_map] at hflt
      rcases hflt with ⟨r', hr', hreq⟩
      have hidx_eq : r'.idx = r₀.pos.idx := by injection hreq
      rw [← hidx_eq]
      exact hextN.2.2.2.2.2.2.2.1 r' hr'
    cases hsafe : sR.1.g.safeCh (2 + Δcka) P
    · simp only [GameState.record, hsafe, Bool.false_eq_true, ↓reduceIte, List.mem_cons] at hr ⊢
      rcases hr with rfl | hr
      · simp only [true_or, true_iff, FSAEAD.State.isCompromised, osR', corrAt', hsafe,
          Bool.false_eq_true, ↓reduceIte, hidxP]
        cases hsc : sR.2.senderCorruptedAt with
        | none => simp
        | some j =>
          have hj := hextN.2.2.2.2.2.2.2.2.2.2 j hsc
          simp only [Option.getD_some, decide_eq_true_eq]
          omega
      · have hle_idx := hmem_idx r hr hrt
        have hne_pos : r.pos ≠ ⟨P, sR.1.g.epoch P, sR.1.g.idx P + 1⟩ := by
          intro heq
          have : r.pos.idx = sR.1.g.idx P + 1 := by rw [heq]
          omega
        simp only [hne_pos, false_or]
        rw [hextN.2.2.2.2.2.2.2.2.1 r hr hrt]
        simp only [FSAEAD.State.isCompromised, osR', corrAt', hsafe, Bool.false_eq_true, ↓reduceIte]
        cases hsc : sR.2.senderCorruptedAt with
        | none =>
          simp [not_lt.mpr hle_idx]
        | some j => rfl
    · have hheal : healedBy sR.1.g.tL (2 + Δcka) t = true := by
        simpa [GameState.safeCh, ht] using hsafe
      have hsc_none : sR.2.senderCorruptedAt = none := by
        cases hsc : sR.2.senderCorruptedAt with
        | none => rfl
        | some j =>
          have := hextN.2.2.2.2.2.2.2.2.2.1 (by simp [hsc])
          rw [this] at hheal
          cases hheal
      simp only [GameState.record, hsafe, ↓reduceIte, FSAEAD.State.isCompromised, osR', corrAt',
        hsc_none, Bool.false_eq_true, iff_false]
      intro hcomp
      have := h.comp_t r.pos hcomp hrt
      rw [this] at hheal
      cases hheal
  · refine ⟨?_, ?_⟩
    · intro hsc
      simp only [GameState.record, osR', corrAt'] at hsc ⊢
      split_ifs at hsc with hsafe
      · exact hextN.2.2.2.2.2.2.2.2.2.1 hsc
      · simp only [GameState.safeCh, ht, Bool.not_eq_true] at hsafe
        exact hsafe
    · intro j hj
      simp only [osR', corrAt', i] at hj ⊢
      split_ifs at hj with hsafe
      · have := hextN.2.2.2.2.2.2.2.2.2.2 j hj
        omega
      · simp only [Option.some.injEq] at hj
        subst hj
        cases hsc : sR.2.senderCorruptedAt with
        | none => simp
        | some j₀ =>
          have := hextN.2.2.2.2.2.2.2.2.2.2 j₀ hsc
          simp only [Option.getD_some]
          omega

def vSendRecord {ι : Type} {tspec : OracleSpec.{0, 0} ι} {HS Γv Sv SSv RSv : Type}
    (hk : Hooks tspec HS Γ T Sig SS RS M E CCoins Γv Sv SSv RSv)
    (Δ : ℕ) (s₁ : Ctx Γv T Sv SSv RSv M E) (P : Party) (m : M) (pair : Option (M × M))
    (r : Option CCoins) (bad : Bool) :
    EM tspec Γv T Sv SSv RSv M E HS (Option (Header T × E)) := do
  match ← liftH (vSend hk s₁ P (s₁.st P) m pair r) with
  | none => abortE; return none
  | some (st', c) =>
    modify fun es =>
      { es with g := s₁.record Δ P st' ⟨⟨P, s₁.epoch P, s₁.idx P + 1⟩, m, c⟩ bad }
    return some c

theorem ActiveInv.vSend_stay_transmit
    (cka : CKAScheme KC Γ CCoins T I) (prng : PRFPRNG KR Sig I K)
    {fs : FSAEADScheme K SS RS (Header T) M E} {Δcka qep : ℕ}
    {tL : Option ℕ} {t : ℕ} {b : Bool}
    {sL : StateL Γ T Sig SS RS M E K I} {sR : StateR Γ T Sig K I SS RS M E}
    (h : ActiveInv fs Δcka qep tL t b sL sR)
    {P : Party} (hPs : P.sendsIn (sR.1.g.epoch P) = true)
    (m : M) (r : Option CCoins)
    (gL₀ : Ctx Γ T (Option Sig) SS RS M E)
    (gR₀ : Ctx Γ T Sig (Option SS) (Option RS) M E) :
    ∃ (c : Header T × E) (sL' : StateL Γ T Sig SS RS M E K I)
      (sR' : StateR Γ T Sig K I SS RS M E),
      runEM (eagerOracleImpl prng)
        (vSendRecord (hooksPRNG cka prng fs ⟨false, tL, t⟩)
          (2 + Δcka) sL.1.g P m none r false)
        ({ sL.1 with g := gL₀ }, sL.2) = pure (some c, sL') ∧
      runEM (FSAEAD.oracleImpl fs)
        (vSendRecord (hooksFS cka prng fs Δcka ⟨false, tL, t⟩ 0)
          (2 + Δcka) sR.1.g P m none r false)
        ({ sR.1 with g := gR₀ }, sR.2) = pure (some c, sR') ∧
      ActiveInv fs Δcka qep tL t b sL' sR' := by
  have hPs_next : P.sendsIn (sR.1.g.epoch P + 1) = false := by
    rw [Party.sendsIn_succ, hPs]; rfl
  have hepP : sL.1.g.epoch P = sR.1.g.epoch P := congrFun h.epoch_eq P
  have hidxP : sL.1.g.idx P = sR.1.g.idx P := congrFun h.idx_eq P
  rcases eq_or_ne (sR.1.g.epoch P) t with ht | hne
  · have hvR := (h.vS_sending P hPs).1 ht
    have hvL : (sL.1.g.st P).vS = some (curSS sR.1.h sR.2) := by
      rw [h.vS_eq P, hvR]; rfl
    cases hext : sR.1.h.ext with
    | some val =>
      rcases val with ⟨ss_val, rs_val⟩
      let hdr : Header T := (sR.1.g.epoch P, (sR.1.g.st P).curCkaMsg)
      let ss' := (fs.send ss_val hdr m).1
      let e := (fs.send ss_val hdr m).2
      refine ⟨(hdr, e), _, _, ?_, ?_, h.record_t_ext_some hPs ht hext m ss' e⟩
      · simp [vSendRecord, runEM, StateT_run_liftH, vSend, hooksPRNG, h.idL P, h.tcurL P, h.Tcur_eq P,
          hepP, hidxP, hPs_next, hvL, curSS, hext, hdr, ss', e]
      · simp [vSendRecord, runEM, StateT_run_liftH, vSend, hooksFS, h.idR P, h.tcurR P,
          hPs_next, hvR, hext, hdr, ss', e]
    | none =>
      have hextN := h.ext_none hext
      let hdr : Header T := (sR.1.g.epoch P, (sR.1.g.st P).curCkaMsg)
      let ss' := (fs.send sR.2.senderState hdr m).1
      let e := (fs.send sR.2.senderState hdr m).2
      refine ⟨(hdr, e), _, _, ?_, ?_, h.record_t_ext_none hPs ht hext m m false ss' e⟩
      · simp [vSendRecord, runEM, StateT_run_liftH, vSend, hooksPRNG, h.idL P, h.tcurL P, h.Tcur_eq P,
          hepP, hidxP, hPs_next, hvL, curSS, hext, hdr, ss', e]
      · cases hsafe : sR.1.g.safeCh (2 + Δcka) P
        · cases hsc : sR.2.senderCorruptedAt with
          | none =>
            have hfsSCorr : sR.1.h.fsSCorr = false := by simp [hextN.2.2.1, hsc]
            simp [vSendRecord, runEM, StateT_run_liftH, vSend, hooksFS, outerFull,
              liftF, FSAEAD.corruptSenderQuery, FSAEAD.transmitQuery,
              FSAEAD.oracleImpl, FSAEAD.corruptSenderImpl, FSAEAD.transmitImpl,
              FSAEAD.corruptSender, FSAEAD.transmit, h.idR P, h.tcurR P, hPs_next,
              hvR, hext, hsafe, hfsSCorr, hextN.1, hextN.2.1, hsc, hdr, ss', e]
          | some j =>
            have hfsSCorr : sR.1.h.fsSCorr = true := by simp [hextN.2.2.1, hsc]
            simp [vSendRecord, runEM, StateT_run_liftH, vSend, hooksFS, outerFull,
              liftF, FSAEAD.transmitQuery, FSAEAD.oracleImpl, FSAEAD.transmitImpl,
              FSAEAD.transmit, h.idR P, h.tcurR P, hPs_next,
              hvR, hext, hsafe, hfsSCorr, hextN.1, hextN.2.1, hsc, hdr, ss', e]
        · have hfsSCorr : sR.1.h.fsSCorr = sR.2.senderCorruptedAt.isSome := hextN.2.2.1
          simp [vSendRecord, runEM, StateT_run_liftH, vSend, hooksFS, outerFull,
            liftF, FSAEAD.transmitQuery, FSAEAD.oracleImpl, FSAEAD.transmitImpl,
            FSAEAD.transmit, h.idR P, h.tcurR P, hPs_next,
            hvR, hext, hsafe, hfsSCorr, hextN.1, hextN.2.1, hdr, ss', e]
  · rcases (h.vS_sending P hPs).2 hne with ⟨ss, hvR⟩
    have hvL : (sL.1.g.st P).vS = some ss := by
      rw [h.vS_eq P, hvR]; rfl
    let hdr : Header T := (sR.1.g.epoch P, (sR.1.g.st P).curCkaMsg)
    let ss' := (fs.send ss hdr m).1
    let e := (fs.send ss hdr m).2
    refine ⟨(hdr, e), _, _, ?_, ?_, h.record_other hPs hne m m ss' e⟩
    · simp [vSendRecord, runEM, StateT_run_liftH, vSend, hooksPRNG, h.idL P, h.tcurL P, h.Tcur_eq P,
        hepP, hidxP, hPs_next, hvL, hdr, ss', e]
    · simp [vSendRecord, runEM, StateT_run_liftH, vSend, hooksFS, h.idR P, h.tcurR P,
        hPs_next, hvR, hdr, ss', e]

theorem ActiveInv.vSend_stay_chall
    (cka : CKAScheme KC Γ CCoins T I) (prng : PRFPRNG KR Sig I K)
    {fs : FSAEADScheme K SS RS (Header T) M E} {Δcka qep : ℕ}
    {tL : Option ℕ} {t : ℕ} {b : Bool}
    {sL : StateL Γ T Sig SS RS M E K I} {sR : StateR Γ T Sig K I SS RS M E}
    (h : ActiveInv fs Δcka qep tL t b sL sR)
    {P : Party} (hPs : P.sendsIn (sR.1.g.epoch P) = true)
    (ht : sR.1.g.epoch P = t)
    (hsafe : sR.1.g.safeCh (2 + Δcka) P = true)
    (m₀ m₁ : M) (r : Option CCoins)
    (gL₀ : Ctx Γ T (Option Sig) SS RS M E)
    (gR₀ : Ctx Γ T Sig (Option SS) (Option RS) M E) :
    let mL := if b then m₁ else m₀
    ∃ (c : Header T × E) (sL' : StateL Γ T Sig SS RS M E K I)
      (sR' : StateR Γ T Sig K I SS RS M E),
      runEM (eagerOracleImpl prng)
        (vSendRecord (hooksPRNG cka prng fs ⟨false, tL, t⟩)
          (2 + Δcka) sL.1.g P mL (some (m₀, m₁)) r true)
        ({ sL.1 with g := gL₀ }, sL.2) = pure (some c, sL') ∧
      runEM (FSAEAD.oracleImpl fs)
        (vSendRecord (hooksFS cka prng fs Δcka ⟨false, tL, t⟩ 0)
          (2 + Δcka) sR.1.g P m₀ (some (m₀, m₁)) r true)
        ({ sR.1 with g := gR₀ }, sR.2) = pure (some c, sR') ∧
      ActiveInv fs Δcka qep tL t b sL' sR' := by
  intro mL
  have hPs_next : P.sendsIn (sR.1.g.epoch P + 1) = false := by
    rw [Party.sendsIn_succ, hPs]; rfl
  have hepP : sL.1.g.epoch P = sR.1.g.epoch P := congrFun h.epoch_eq P
  have hidxP : sL.1.g.idx P = sR.1.g.idx P := congrFun h.idx_eq P
  have hheal : healedBy sR.1.g.tL (2 + Δcka) t = true := by
    simpa [GameState.safeCh, ht] using hsafe
  have hext : sR.1.h.ext = none := by
    cases hx : sR.1.h.ext with
    | none => rfl
    | some val =>
      have := (h.ext_some (by simp [hx])).1
      rw [this] at hheal
      cases hheal
  have hextN := h.ext_none hext
  have hsc_none : sR.2.senderCorruptedAt = none := by
    cases hsc : sR.2.senderCorruptedAt with
    | none => rfl
    | some j =>
      have := hextN.2.2.2.2.2.2.2.2.2.1 (by simp [hsc])
      rw [this] at hheal
      cases hheal
  have hfsSCorr : sR.1.h.fsSCorr = false := by simp [hextN.2.2.1, hsc_none]
  have hvR := (h.vS_sending P hPs).1 ht
  have hvL : (sL.1.g.st P).vS = some sR.2.senderState := by
    rw [h.vS_eq P, hvR]; simp [curSS, hext]
  let hdr : Header T := (sR.1.g.epoch P, (sR.1.g.st P).curCkaMsg)
  let ss' := (fs.send sR.2.senderState hdr mL).1
  let e := (fs.send sR.2.senderState hdr mL).2
  refine ⟨(hdr, e), _, _, ?_, ?_, h.record_t_ext_none hPs ht hext mL m₀ true ss' e⟩
  · simp [vSendRecord, runEM, StateT_run_liftH, vSend, hooksPRNG, h.idL P, h.tcurL P, h.Tcur_eq P,
      hepP, hidxP, hPs_next, hvL, hdr, ss', e]
  · simp [vSendRecord, runEM, StateT_run_liftH, vSend, hooksFS, outerFull,
      liftF, FSAEAD.challengeQuery, FSAEAD.oracleImpl, FSAEAD.challengeImpl,
      FSAEAD.challenge, h.idR P, h.tcurR P, hPs_next,
      hvR, hext, hsafe, hfsSCorr, hextN.1, hextN.2.1, hsc_none, h.bFS, hdr, ss', e, mL]

theorem corr_false_of_validGuess {Δcka : ℕ} {tL : Option ℕ} {ep t : ℕ}
    (hvalid : lastLeakGuessAdmissible (2 + Δcka) tL t = true)
    (ht : ep + 1 = t)
    (hnot_heal : (tL.isSome && decide (t = healEpoch tL)) = false) :
    (tL.isSome && decide (ep < healEpoch tL)) = false := by
  cases tL with
  | none => rfl
  | some l =>
    rw [Option.isSome, Bool.true_and, decide_eq_false_iff_not] at hnot_heal ⊢
    rw [lastLeakGuessAdmissible, healedBy, decide_eq_true_eq] at hvalid
    dsimp only [healEpoch] at hnot_heal ⊢
    omega

theorem decide_mode_tH_eq (auth : Bool) (tL : Option ℕ) (tStar x : ℕ) :
    decide (x = (Mode.mk auth tL tStar).tH) = decide (x = healEpoch tL) := rfl

theorem decide_mode_tH_lt (auth : Bool) (tL : Option ℕ) (tStar x : ℕ) :
    decide (x < (Mode.mk auth tL tStar).tH) = decide (x < healEpoch tL) := rfl

omit [DecidableEq T] [DecidableEq M] [DecidableEq E] [DecidableEq I] [Inhabited E]
  [SampleableType CCoins] [SampleableType I] [SampleableType K] in
theorem ActiveInv.epoch_of_sendsIn_succ
    {fs : FSAEADScheme K SS RS (Header T) M E} {Δcka qep : ℕ}
    {tL : Option ℕ} {t : ℕ} {b : Bool}
    {sL : StateL Γ T Sig SS RS M E K I} {sR : StateR Γ T Sig K I SS RS M E}
    (h : ActiveInv fs Δcka qep tL t b sL sR)
    {P : Party} (hPs_next : P.sendsIn (sR.1.g.epoch P + 1) = true) :
    let ep := sR.1.g.epoch P
    P.sendsIn ep = false ∧
    P = Party.receiverOf ep ∧
    P = Party.senderOf (ep + 1) ∧
    max (sR.1.g.epoch .A) (sR.1.g.epoch .B) = ep ∧
    (∀ Q, sR.1.g.epoch Q = ep) := by
  intro ep
  have hPs_stay : P.sendsIn ep = false := by
    have := Party.sendsIn_succ P ep
    rw [hPs_next] at this
    simpa using this.symm
  have hPr : P = Party.receiverOf ep := (Party.sendsIn_false_iff_receiverOf P ep).mp hPs_stay
  have hPs1 : P = Party.senderOf (ep + 1) := (Party.sendsIn_eq_senderOf P (ep + 1)).mp hPs_next
  let epM := max (sR.1.g.epoch .A) (sR.1.g.epoch .B)
  have hepM : epM = ep := by
    rcases Party.eq_senderOf_or_receiverOf P epM with hPsM | hPrM
    · have h1 : ep = epM := by
        change sR.1.g.epoch P = epM
        rw [hPsM]
        exact h.sender_epoch
      rw [← h1] at hPsM
      exact absurd (hPr.symm.trans hPsM).symm (Party.senderOf_ne_receiverOf ep)
    · rcases h.receiver_epoch with hre | ⟨_, hre⟩
      · change epM = sR.1.g.epoch P
        rw [hPrM]
        exact hre.symm
      · have h1 : ep + 1 = epM := by
          change sR.1.g.epoch P + 1 = epM
          rw [hPrM]
          exact hre
        rw [← h1] at hPrM
        exact absurd (hPs1.symm.trans hPrM) (Party.senderOf_ne_receiverOf (ep + 1))
  refine ⟨hPs_stay, hPr, hPs1, hepM, fun Q => ?_⟩
  rcases Party.eq_senderOf_or_receiverOf Q epM with rfl | rfl
  · exact h.sender_epoch.trans hepM
  · rw [hepM, ← hPr]

omit [DecidableEq T] [DecidableEq M] [DecidableEq E] [DecidableEq I] [Inhabited E]
  [SampleableType CCoins] [SampleableType I] [SampleableType K] in
theorem ActiveInv.advance_core
    {fs : FSAEADScheme K SS RS (Header T) M E} {Δcka qep : ℕ}
    {tL : Option ℕ} {t : ℕ} {b : Bool}
    {sL : StateL Γ T Sig SS RS M E K I} {sR : StateR Γ T Sig K I SS RS M E}
    (h : ActiveInv fs Δcka qep tL t b sL sR)
    {P : Party} (hPs_next : P.sendsIn (sR.1.g.epoch P + 1) = true)
    (hqep : ¬(qep < sR.1.g.epoch P + 1))
    (bad : Bool) (γ' : Γ) (T' : T)
    (σL' : Option Sig) (kL : K) (pgL' : EagerState Sig I K)
    (σR' : Sig) (kR : K) (ext : Bool)
    (hR_mid : FSState T Sig K I SS RS E)
    (hext_iff : ext = true ↔ sR.1.g.epoch P + 1 = t)
    (hk_ne : sR.1.g.epoch P + 1 ≠ t → kL = kR)
    (hrootP : σL' =
      if sR.1.g.epoch P + 1 < t ∧ ¬(tL.isSome && decide (sR.1.g.epoch P + 1 < healEpoch tL))
      then none else some σR')
    (hR_mid_fields :
      hR_mid.ext = sR.1.h.ext ∧
      hR_mid.fsCount = sR.1.h.fsCount ∧
      hR_mid.fsSCorr = sR.1.h.fsSCorr ∧
      hR_mid.fsTrans = sR.1.h.fsTrans)
    (hcache_t : sR.1.g.epoch P + 1 = t →
      sR.2.senderState = fs.initSender kL ∧
      sR.2.receiverState = fs.initReceiver kL ∧ sR.1.h.ext = none ∧ sR.2.lastSentIdx = 0)
    (hbefore : sR.1.g.epoch P + 1 < t →
      pgL'.1.b = true ∧
      pgL'.1.corr = (tL.isSome && decide (sR.1.g.epoch P + 1 < healEpoch tL)) ∧
      pgL'.1.prng = false ∧ pgL'.1.prf = false ∧ pgL'.1.table = [] ∧
      σR' = pgL'.1.σ ∧
      hR_mid.table = [] ∧ hR_mid.sessions = [] ∧ hR_mid.fsTrans = [] ∧
      hR_mid.fsCount = 0 ∧ hR_mid.fsSCorr = false ∧ hR_mid.ext = none ∧
      ∃ k_fs, pgL'.2 = .ready k_fs ∧ sR.2 = FSAEAD.initState fs k_fs b) :
    let t' := sR.1.g.epoch P + 1
    let s₁L := if bad && !sL.1.g.safeCh (2 + Δcka) P then sL.1.g.leak t' else sL.1.g
    let s₁R := if bad && !sR.1.g.safeCh (2 + Δcka) P then sR.1.g.leak t' else sR.1.g
    let stL₁ : VP Γ T (Option Sig) SS RS :=
      { sL.1.g.st P with
          root := σL'
          vS := some (fs.initSender kL)
          γ := γ'
          curCkaMsg := some T'
          tcur := t' }
    let stR₁ : VP Γ T Sig (Option SS) (Option RS) :=
      { sR.1.g.st P with
          root := σR'
          vS := some (if ext then none else some (fs.initSender kR))
          γ := γ'
          curCkaMsg := some T'
          tcur := t' }
    let gMidL : Ctx Γ T (Option Sig) SS RS M E :=
      { s₁L with
          st := Function.update sL.1.g.st P stL₁
          epoch := Function.update sL.1.g.epoch P t'
          idx := Function.update sL.1.g.idx P 0 }
    let gMidR : Ctx Γ T Sig (Option SS) (Option RS) M E :=
      { s₁R with
          st := Function.update sR.1.g.st P stR₁
          epoch := Function.update sR.1.g.epoch P t'
          idx := Function.update sR.1.g.idx P 0 }
    let hL' : PRNGState T Sig K :=
      { cache := Function.update sL.1.h.cache t' (some (T', σL', kL)) }
    let hR' : FSState T Sig K I SS RS E :=
      { hR_mid with cache := Function.update sR.1.h.cache t' (some (T', σR', kR, ext)) }
    ActiveInv fs Δcka qep tL t b
      ({ sL.1 with g := gMidL, h := hL' }, pgL')
      ({ sR.1 with g := gMidR, h := hR' }, sR.2) := by
  intro t' s₁L s₁R stL₁ stR₁ gMidL gMidR hL' hR'
  rcases h.epoch_of_sendsIn_succ hPs_next with ⟨hPs_stay, hPr, hPs1, hepM, hall_ep⟩
  have hsafe_eq := h.safeCh_eq (2 + Δcka) P
  have hs₁L :
      s₁L.win = sL.1.g.win ∧ s₁L.b = sL.1.g.b ∧ s₁L.chall = sL.1.g.chall ∧
      s₁L.comp = sL.1.g.comp ∧ s₁L.maxAcc = sL.1.g.maxAcc ∧
      s₁L.corrs = sL.1.g.corrs ∧ s₁L.trans = sL.1.g.trans := by
    dsimp only [s₁L]; split_ifs <;> simp [GameState.leak]
  have hs₁R :
      s₁R.win = sR.1.g.win ∧ s₁R.b = sR.1.g.b ∧ s₁R.chall = sR.1.g.chall ∧
      s₁R.comp = sR.1.g.comp ∧ s₁R.maxAcc = sR.1.g.maxAcc ∧
      s₁R.corrs = sR.1.g.corrs ∧ s₁R.trans = sR.1.g.trans := by
    dsimp only [s₁R]; split_ifs <;> simp [GameState.leak]
  have hs₁_tL : s₁L.tL = s₁R.tL := by
    dsimp only [s₁L, s₁R]; rw [hsafe_eq]; split_ifs <;> simp [GameState.leak, h.tL_eq]
  have hs₁_leaks : s₁L.leaks = s₁R.leaks := by
    dsimp only [s₁L, s₁R]; rw [hsafe_eq]; split_ifs <;> simp [GameState.leak, h.tL_eq, h.leaks_eq]
  have hep' : ∀ Q, gMidR.epoch Q = if Q = P then t' else sR.1.g.epoch P := by
    intro Q
    rcases eq_or_ne Q P with rfl | hne
    · simp [gMidR]
    · simp [gMidR, hall_ep Q, hne]
  have hmax_ep' : max (gMidR.epoch .A) (gMidR.epoch .B) = t' := by
    cases P
    · simp [hep' .A, hep' .B, t']
    · simp [hep' .A, hep' .B, t']
  have hcurSS : curSS hR' sR.2 = curSS sR.1.h sR.2 := by
    simp [curSS, hR', hR_mid_fields.1]
  have hcurRS : curRS hR' sR.2 = curRS sR.1.h sR.2 := by
    simp [curRS, hR', hR_mid_fields.1]
  refine
    { abortL := h.abortL
      abortR := h.abortR
      winL := by simp [gMidL, hs₁L, h.winL]
      winR := by simp [gMidR, hs₁R, h.winR]
      winFS := h.winFS
      bL := by simp [gMidL, hs₁L, h.bL]
      bR := by simp [gMidR, hs₁R, h.bR]
      bFS := h.bFS
      epoch_eq := by simp [gMidL, gMidR, h.epoch_eq]
      idx_eq := by simp [gMidL, gMidR, h.idx_eq]
      tL_eq := by simp [gMidL, gMidR, hs₁_tL]
      chall_eq := by simp [gMidL, gMidR, hs₁L, hs₁R, h.chall_eq]
      comp_eq := by simp [gMidL, gMidR, hs₁L, hs₁R, h.comp_eq]
      maxAcc_eq := by simp [gMidL, gMidR, hs₁L, hs₁R, h.maxAcc_eq]
      leaks_eq := by simp [gMidL, gMidR, hs₁_leaks]
      corrs_eq := by simp [gMidL, gMidR, hs₁L, hs₁R, h.corrs_eq]
      trans_eq := by simp [gMidL, gMidR, hs₁L, hs₁R, h.trans_eq]
      idL := fun Q => by
        rcases eq_or_ne Q P with rfl | hne
        · simp [gMidL, stL₁, h.idL]
        · simp [gMidL, Function.update_of_ne hne, h.idL]
      idR := fun Q => by
        rcases eq_or_ne Q P with rfl | hne
        · simp [gMidR, stR₁, h.idR]
        · simp [gMidR, Function.update_of_ne hne, h.idR]
      tcurL := fun Q => by
        rcases eq_or_ne Q P with rfl | hne
        · simp [gMidL, gMidR, stL₁]
        · simp [gMidL, gMidR, Function.update_of_ne hne, h.tcurL]
      tcurR := fun Q => by
        rcases eq_or_ne Q P with rfl | hne
        · simp [gMidR, stR₁]
        · simp [gMidR, Function.update_of_ne hne, h.tcurR]
      γ_eq := fun Q => by
        rcases eq_or_ne Q P with rfl | hne
        · simp [gMidL, gMidR, stL₁, stR₁]
        · simp [gMidL, gMidR, Function.update_of_ne hne, h.γ_eq]
      Tcur_eq := fun Q => by
        rcases eq_or_ne Q P with rfl | hne
        · simp [gMidL, gMidR, stL₁, stR₁]
        · simp [gMidL, gMidR, Function.update_of_ne hne, h.Tcur_eq]
      root_eq := fun Q => by
        rcases eq_or_ne Q P with rfl | hne
        · simp [gMidL, gMidR, stL₁, stR₁, hrootP, t']
        · simp [gMidL, gMidR, Function.update_of_ne hne, h.root_eq]
      vS_eq := fun Q => by
        rcases eq_or_ne Q P with rfl | hne
        · simp only [gMidL, gMidR, Function.update_self, stL₁, stR₁, hcurSS]
          by_cases hext : ext = true
          · have ht : t' = t := hext_iff.mp hext
            rcases hcache_t ht with ⟨hss, _, hext_none, _⟩
            simp [hext, curSS, hext_none, hss]
          · simp only [Bool.not_eq_true] at hext
            have hne_t : t' ≠ t := fun ht => by rw [hext_iff.mpr ht] at hext; cases hext
            simp [hext, hk_ne hne_t]
        · simp [gMidL, gMidR, Function.update_of_ne hne, hcurSS, h.vS_eq]
      vR_eq := fun Q t'' => by
        rcases eq_or_ne Q P with rfl | hne
        · simp [gMidL, gMidR, stL₁, stR₁, hcurRS, h.vR_eq]
        · simp [gMidL, gMidR, Function.update_of_ne hne, hcurRS, h.vR_eq]
      sender_epoch := by
        rw [hmax_ep', ← hPs1]
        simp [gMidR]
      receiver_epoch := by
        dsimp only
        rw [hmax_ep']
        right
        have hne_rec : Party.receiverOf t' ≠ P := by
          intro heq
          exact Party.senderOf_ne_receiverOf t' (hPs1.symm.trans heq.symm)
        refine ⟨by omega, ?_⟩
        simp [hep' (Party.receiverOf t'), hne_rec, t']
      maxEp_le_qep := by
        rw [hmax_ep']
        omega
      tL_le_maxEp := fun l₀ hl₀ => by
        rw [hmax_ep']
        simp only [gMidR, s₁R] at hl₀
        split_ifs at hl₀
        · simp only [GameState.leak, Option.some.injEq] at hl₀
          subst hl₀
          cases htL : sR.1.g.tL with
          | none => exact le_rfl
          | some l₁ =>
            have := h.tL_le_maxEp l₁ htL
            simp only [maxOpt]
            omega
        · have := h.tL_le_maxEp l₀ hl₀
          omega
      vS_none := fun Q hvS => by
        rcases eq_or_ne Q P with rfl | hne
        · simp only [gMidR, Function.update_self, stR₁, Option.some.injEq] at hvS ⊢
          have hext : ext = true := by
            cases h_ext : ext
            · simp [h_ext] at hvS
            · rfl
          have ht : t' = t := hext_iff.mp hext
          exact ⟨ht ▸ hPs1, le_of_eq ht.symm⟩
        · simp only [gMidR, Function.update_of_ne hne] at hvS ⊢
          exact h.vS_none Q hvS
      vS_sending := fun Q hQs => by
        rcases eq_or_ne Q P with rfl | hne
        · simp only [gMidR, Function.update_self, stR₁]
          refine ⟨fun ht => ?_, fun hne_t => ?_⟩
          · simp [hext_iff.mpr ht]
          · have hext : ext = false := by
              cases h_ext : ext
              · rfl
              · exact absurd (hext_iff.mp h_ext) hne_t
            exact ⟨fs.initSender kR, by simp [hext]⟩
        · simp only [gMidR, Function.update_of_ne hne] at hQs ⊢
          exact h.vS_sending Q hQs
      vR_sender := by
        rcases eq_or_ne (Party.senderOf t) P with heq | hne
        · rw [heq]
          simp [gMidR, stR₁, ← heq, h.vR_sender]
        · simp [gMidR, Function.update_of_ne hne, h.vR_sender]
      vR_receiver := by
        rcases eq_or_ne (Party.receiverOf t) P with heq | hne
        · have hne_t : t ≠ t' := by
            intro ht
            subst ht
            exact Party.senderOf_ne_receiverOf t' (hPs1.symm.trans heq.symm)
          have hiff : (t ≤ t') ↔ (t ≤ sR.1.g.epoch P) := by omega
          simp only [gMidR, heq, Function.update_self, stR₁]
          have hrec := h.vR_receiver
          rw [heq] at hrec
          rw [hrec]
          by_cases hle : t ≤ sR.1.g.epoch P
          · have hle' : t ≤ t' := hiff.mpr hle
            simp [hle, hle']
          · have hle' : ¬(t ≤ t') := fun h1 => hle (hiff.mp h1)
            simp [hle, hle']
        · simp [gMidR, Function.update_of_ne hne, h.vR_receiver]
      vR_other := fun Q t'' x hne_t hv => by
        rcases eq_or_ne Q P with rfl | hne
        · simp only [gMidR, Function.update_self, stR₁] at hv ⊢
          rcases h.vR_other Q t'' x hne_t hv with ⟨hx, hQr, hle⟩
          exact ⟨hx, hQr, by omega⟩
        · simp only [gMidR, Function.update_of_ne hne] at hv ⊢
          exact h.vR_other Q t'' x hne_t hv
      cache_none := fun t'' ht'' => by
        rw [hmax_ep'] at ht''
        have hne_t' : t'' ≠ t' := by omega
        simp [hL', hR', Function.update_of_ne hne_t', h.cache_none t'' (by omega)]
      cache_other := fun t'' ht'' => by
        rcases eq_or_ne t'' t' with rfl | hne_t'
        · have hext : ext = false := by
            cases h_ext : ext
            · rfl
            · exact absurd (hext_iff.mp h_ext) ht''
          simp [hL', hR', hk_ne ht'', hrootP, t']
        · simp [hL', hR', Function.update_of_ne hne_t', h.cache_other t'' ht'']
      cache_other_ext := fun t'' Tc σc kc ext' ht'' hc => by
        rcases eq_or_ne t'' t' with rfl | hne_t'
        · simp only [hR', Function.update_self, Option.some.injEq, Prod.mk.injEq] at hc
          rcases hc with ⟨_, _, _, rfl⟩
          cases h_ext : ext
          · rfl
          · exact absurd (hext_iff.mp h_ext) ht''
        · simp only [hR', Function.update_of_ne hne_t'] at hc
          exact h.cache_other_ext t'' Tc σc kc ext' ht'' hc
      cache_t_none := fun hc => by
        rcases eq_or_ne t t' with rfl | hne_t'
        · simp [hR'] at hc
        · simp only [hL', hR', Function.update_of_ne hne_t'] at hc ⊢
          exact h.cache_t_none hc
      cache_t := fun Tc σc kc ext' hc => by
        rcases eq_or_ne t t' with rfl | hne_t'
        · simp only [hR', Function.update_self, Option.some.injEq, Prod.mk.injEq] at hc
          rcases hc with ⟨rfl, rfl, rfl, rfl⟩
          have hext : ext = true := hext_iff.mpr rfl
          have hσL : σL' = some σR' := by
            rw [hrootP]
            simp [t']
          rcases hcache_t rfl with ⟨_, hrs, hext_none, _⟩
          refine ⟨hext, kL, ?_, fun _ => ⟨hrs, by simp [hR', hR_mid_fields.1, hext_none]⟩⟩
          simp [hL', hσL]
        · simp only [hL', hR', Function.update_of_ne hne_t'] at hc ⊢
          rcases h.cache_t Tc σc kc ext' hc with ⟨hext, k₀, hcL, hrec⟩
          refine ⟨hext, k₀, hcL, fun hlt => ?_⟩
          have hlt' : sR.1.g.epoch (Party.receiverOf t) < t := by
            rcases eq_or_ne (Party.receiverOf t) P with heq | hne_P
            · simp only [gMidR, heq, Function.update_self] at hlt
              rw [heq]
              omega
            · simp only [gMidR, Function.update_of_ne hne_P] at hlt
              exact hlt
          rw [hR_mid_fields.1]
          exact hrec hlt'
      trans_wf := fun r hr => by
        rw [hmax_ep']
        have hr' : r ∈ sR.1.g.trans := by simpa [gMidR, hs₁R] using hr
        rcases h.trans_wf r hr' with ⟨h1, h2, h3⟩
        exact ⟨h1, h2, by omega⟩
      chall_wf := fun p hp => by
        rw [hmax_ep']
        have hp' : p ∈ sR.1.g.chall := by simpa [gMidR, hs₁R] using hp
        rcases h.chall_wf p hp' with ⟨h1, h2⟩
        exact ⟨h1, by omega⟩
      comp_t := fun pos hpos hpe => by
        have hpos' : pos ∈ sR.1.g.comp := by simpa [gMidR, hs₁R] using hpos
        have hc := h.comp_t pos hpos' hpe
        simp only [gMidR, s₁R, GameState.leak]
        split_ifs
        · exact healedBy_maxOpt_false_of_false hc
        · exact hc
      before_t := by
        dsimp only
        rw [hmax_ep']
        intro ht'
        rcases hbefore ht' with ⟨hb1, hb2, hb3, hb4, hb5, hσ, ht1, ht2, ht3, ht4, ht5, ht6, hfs⟩
        refine ⟨hb1, hb2, hb3, hb4, hb5, ?_, ?_, ht1, ht2, ht3, ht4, ht5, ht6, hfs⟩
        · intro Q hQ
          rw [hep' Q] at hQ
          rcases eq_or_ne Q P with rfl | hne
          · simp [gMidR, stR₁, hσ]
          · simp only [hne, ↓reduceIte] at hQ
            omega
        · intro Tc σc kc ext' hc
          simp only [hR', Function.update_self, Option.some.injEq, Prod.mk.injEq] at hc
          rcases hc with ⟨_, rfl, _, _⟩
          exact hσ
      ext_some := fun hs => by
        simp only [hR', hR_mid_fields.1] at hs
        rcases h.ext_some hs with ⟨hheal, hcomp⟩
        refine ⟨?_, ?_⟩
        · simp only [gMidR, s₁R, GameState.leak]
          split_ifs
          · exact healedBy_maxOpt_false_of_false hheal
          · exact hheal
        · simpa [gMidR, hs₁R] using hcomp
      ext_none := fun hn => by
        simp only [hR', hR_mid_fields] at hn ⊢
        have hextN := h.ext_none hn
        refine ⟨hextN.1, hextN.2.1, hextN.2.2.1, ?_, hextN.2.2.2.2.1,
          by simpa [gMidR, hs₁R] using hextN.2.2.2.2.2.1,
          by simpa [gMidR, hs₁R] using hextN.2.2.2.2.2.2.1,
          hextN.2.2.2.2.2.2.2.1,
          by simpa [gMidR, hs₁R] using hextN.2.2.2.2.2.2.2.2.1,
          ⟨?_, hextN.2.2.2.2.2.2.2.2.2.2⟩⟩
        · intro hep_t
          rcases eq_or_ne t' t with ht | hne_t
          · rcases hcache_t ht with ⟨_, _, _, hlast⟩
            have hSP : Party.senderOf t = P := ht ▸ hPs1.symm
            simp [gMidR, hSP, hlast]
          · have hne_SP : Party.senderOf t ≠ P := by
              intro heq
              simp [gMidR, heq] at hep_t
              exact hne_t hep_t
            simp only [gMidR, Function.update_of_ne hne_SP] at hep_t ⊢
            exact hextN.2.2.2.1 hep_t
        · intro hsc
          have hheal := hextN.2.2.2.2.2.2.2.2.2.1 hsc
          simp only [gMidR, s₁R, GameState.leak]
          split_ifs
          · exact healedBy_maxOpt_false_of_false hheal
          · exact hheal }

omit [DecidableEq T] [DecidableEq M] [DecidableEq E] [DecidableEq I] [Inhabited E]
  [SampleableType CCoins] [SampleableType I] [SampleableType K] in
theorem closeBy_bind_right_const {α : Type} [SampleableType α]
    {cR : ProbComp Bool} {cM cL : α → ProbComp Bool}
    (h : ∀ a, CloseBy cR (cM a) (cL a)) :
    CloseBy cR (($ᵗ α : ProbComp α) >>= cM) (($ᵗ α : ProbComp α) >>= cL) := by
  have h' : CloseBy (($ᵗ α : ProbComp α) >>= fun _ => cR)
      (($ᵗ α : ProbComp α) >>= cM) (($ᵗ α : ProbComp α) >>= cL) :=
    closeBy_bind ($ᵗ α) h
  unfold CloseBy at h' ⊢
  simpa only [OracleComp.evalDist_bind_const] using h'

omit [DecidableEq T] [DecidableEq M] [DecidableEq E] [DecidableEq I]
  [SampleableType CCoins] [SampleableType I] [SampleableType K] in
theorem vSend_advance_eq {ι : Type} {tspec : OracleSpec ι} {HS Γv Sv SSv RSv : Type}
    (hk : Hooks tspec HS Γ T Sig SS RS M E CCoins Γv Sv SSv RSv)
    (s₁ : Ctx Γv T Sv SSv RSv M E) (P : Party) (m : M) (pair : Option (M × M))
    (r : Option CCoins)
    (hid : (s₁.st P).id = P)
    (hPs_next : P.sendsIn ((s₁.st P).tcur + 1) = true)
    (hfsSend : ∀ st₁ : VP Γv T Sv SSv RSv,
      hk.fsSend { s₁ with st := Function.update s₁.st P st₁ } P = hk.fsSend s₁ P) :
    vSend hk s₁ P (s₁.st P) m pair r =
      (do
        match ← hk.startSend s₁ P ((s₁.st P).tcur + 1) (s₁.st P).γ (s₁.st P).root r with
        | none => return none
        | some (γ', T', σ', ss) =>
          let st₁ : VP Γv T Sv SSv RSv :=
            { s₁.st P with root := σ', vS := some ss, γ := γ', curCkaMsg := some T', tcur := (s₁.st P).tcur + 1 }
          let gMid := { s₁ with st := Function.update s₁.st P st₁ }
          vSend hk gMid P (gMid.st P) m pair r) := by
  have hPs_next2 : P.sendsIn ((s₁.st P).tcur + 1 + 1) = false := by
    rw [Party.sendsIn_succ, hPs_next]; rfl
  simp only [vSend, hid, hPs_next, ↓reduceIte]
  refine bind_congr fun res => ?_
  rcases res with _ | ⟨γ', T', σ', ss⟩
  · simp
  · simp [hPs_next2, hfsSend]

omit [DecidableEq T] [DecidableEq M] [DecidableEq E] [DecidableEq I] [Inhabited E]
  [SampleableType CCoins] [SampleableType I] [SampleableType K] in
theorem runEM_liftH_bind {ι : Type} {tspec : OracleSpec.{0, 0} ι} {OS HS Γv Sv SSv RSv α β γ : Type}
    (oimpl : QueryImpl tspec (StateT OS ProbComp))
    (x : HM tspec HS α) (f : α → HM tspec HS β)
    (k : β → EM tspec Γv T Sv SSv RSv M E HS γ)
    (s : EState (VP Γv T Sv SSv RSv) M (Header T × E) HS × OS) :
    runEM oimpl (liftH (x >>= f) >>= k) s =
      runHM oimpl x s.1.h s.2 >>= fun r =>
        runEM oimpl (liftH (f r.1.1) >>= k) ({ s.1 with h := r.1.2 }, r.2) := by
  simp [runEM, runHM, StateT_run_liftH, StateT.run_bind, simulateQ_bind]

omit [DecidableEq T] [DecidableEq M] [DecidableEq E] [DecidableEq I]
  [SampleableType CCoins] [SampleableType I] [SampleableType K] in
theorem runEM_vSend_advance {ι : Type} {tspec : OracleSpec.{0, 0} ι} {OS HS Γv Sv SSv RSv : Type}
    (oimpl : QueryImpl tspec (StateT OS ProbComp))
    (hk : Hooks tspec HS Γ T Sig SS RS M E CCoins Γv Sv SSv RSv)
    (Δ : ℕ) (s₁ : Ctx Γv T Sv SSv RSv M E) (P : Party) (m : M) (pair : Option (M × M))
    (r : Option CCoins) (bad : Bool)
    (s : EState (VP Γv T Sv SSv RSv) M (Header T × E) HS × OS)
    (hid : (s₁.st P).id = P)
    (hPs_next : P.sendsIn ((s₁.st P).tcur + 1) = true)
    (hfsSend : ∀ st₁ : VP Γv T Sv SSv RSv,
      hk.fsSend { s₁ with st := Function.update s₁.st P st₁ } P = hk.fsSend s₁ P) :
    runEM oimpl (vSendRecord hk Δ s₁ P m pair r bad) s =
      (runHM oimpl (hk.startSend s₁ P ((s₁.st P).tcur + 1) (s₁.st P).γ (s₁.st P).root r) s.1.h s.2 >>=
        fun res =>
          match res.1.1 with
          | none => pure (none, ({ s.1 with h := res.1.2, abort := true }, res.2))
          | some (γ', T', σ', ss) =>
            let st₁ : VP Γv T Sv SSv RSv :=
              { s₁.st P with root := σ', vS := some ss, γ := γ', curCkaMsg := some T', tcur := (s₁.st P).tcur + 1 }
            let gMid := { s₁ with st := Function.update s₁.st P st₁ }
            runEM oimpl (vSendRecord hk Δ gMid P m pair r bad)
              ({ s.1 with h := res.1.2 }, res.2)) := by
  unfold vSendRecord
  rw [vSend_advance_eq hk s₁ P m pair r hid hPs_next hfsSend, runEM_liftH_bind]
  refine bind_congr fun res => ?_
  rcases res.1.1 with _ | ⟨γ', T', σ', ss⟩
  · simp [runEM, StateT_run_liftH, abortE]
  · simp only [record_update_st_self]

def optSample (α : Type) [SampleableType α] : Option α → ProbComp α
  | some a => pure a
  | none => $ᵗ α

omit [DecidableEq M] [DecidableEq E] [Inhabited E] in
theorem runHM_startSend_prng_eq (cka : CKAScheme KC Γ CCoins T I) (prng : PRFPRNG KR Sig I K)
    (fs : FSAEADScheme K SS RS (Header T) M E) (mo : Mode)
    (s₁ : Ctx Γ T (Option Sig) SS RS M E) (P : Party) (t' : ℕ) (γ : Γ) (σ : Option Sig)
    (r : Option CCoins) (hL : PRNGState T Sig K) (pgL : EagerState Sig I K) :
    runHM (eagerOracleImpl prng) ((hooksPRNG cka prng fs mo).startSend s₁ P t' γ σ r) hL pgL =
      optSample CCoins r >>= fun coins =>
        runHM (eagerOracleImpl prng)
          ((hooksPRNG cka prng fs mo).startSend s₁ P t' γ σ (some coins)) hL pgL := by
  cases r with
  | some coins => simp [optSample]
  | none =>
    simp [optSample, hooksPRNG, runHM, StateT.run_bind, simulateQ_bind,
      simulateQ_outerFull_sampleT, bind_map_left]

omit [Inhabited E] in
theorem runHM_startSend_fs_eq (cka : CKAScheme KC Γ CCoins T I) (prng : PRFPRNG KR Sig I K)
    (fs : FSAEADScheme K SS RS (Header T) M E) (Δcka : ℕ) (mo : Mode) (j : ℕ)
    (s₁ : Ctx Γ T Sig (Option SS) (Option RS) M E) (P : Party) (t' : ℕ) (γ : Γ) (σ : Sig)
    (r : Option CCoins) (hR : FSState T Sig K I SS RS E)
    (osR : FSAEAD.State SS RS (Header T) M E) :
    runHM (FSAEAD.oracleImpl fs) ((hooksFS cka prng fs Δcka mo j).startSend s₁ P t' γ σ r) hR osR =
      optSample CCoins r >>= fun coins =>
        runHM (FSAEAD.oracleImpl fs)
          ((hooksFS cka prng fs Δcka mo j).startSend s₁ P t' γ σ (some coins)) hR osR := by
  cases r with
  | some coins => simp [optSample]
  | none =>
    simp [optSample, hooksFS, runHM, StateT.run_bind, simulateQ_bind,
      simulateQ_outerFull_sampleT, bind_map_left]

omit [Inhabited E] in
theorem ActiveInv.closeBy_startSend
    (cka : CKAScheme KC Γ CCoins T I) (prng : PRFPRNG KR Sig I K)
    {fs : FSAEADScheme K SS RS (Header T) M E} {Δcka qep : ℕ}
    {tL : Option ℕ} {t : ℕ} {b : Bool}
    {sL : StateL Γ T Sig SS RS M E K I} {sR : StateR Γ T Sig K I SS RS M E}
    (h : ActiveInv fs Δcka qep tL t b sL sR)
    (hvalid : lastLeakGuessAdmissible (2 + Δcka) tL t = true)
    {P : Party} (hPs_next : P.sendsIn (sR.1.g.epoch P + 1) = true)
    (hqep : ¬(qep < sR.1.g.epoch P + 1))
    (bad : Bool) (r : Option CCoins)
    (s₁_epL : Ctx Γ T (Option Sig) SS RS M E)
    (s₁_epR : Ctx Γ T Sig (Option SS) (Option RS) M E)
    (fR : (Option (Γ × T × Option Sig × SS) × PRNGState T Sig K) × EagerState Sig I K → ProbComp Bool)
    (fM fL : (Option (Γ × T × Sig × Option SS) × FSState T Sig K I SS RS E) ×
      FSAEAD.State SS RS (Header T) M E → ProbComp Bool)
    (hcont : ∀ (γ' : Γ) (T' : T) (σL' : Option Sig) (kL : K) (pgL' : EagerState Sig I K)
        (σR' : Sig) (kR : K) (ext : Bool) (hL' : PRNGState T Sig K)
        (hR' : FSState T Sig K I SS RS E),
      let t' := sR.1.g.epoch P + 1
      let s₁L := if bad && !sL.1.g.safeCh (2 + Δcka) P then sL.1.g.leak t' else sL.1.g
      let s₁R := if bad && !sR.1.g.safeCh (2 + Δcka) P then sR.1.g.leak t' else sR.1.g
      let stL₁ : VP Γ T (Option Sig) SS RS :=
        { sL.1.g.st P with root := σL', vS := some (fs.initSender kL), γ := γ', curCkaMsg := some T', tcur := t' }
      let stR₁ : VP Γ T Sig (Option SS) (Option RS) :=
        { sR.1.g.st P with
            root := σR', vS := some (if ext then none else some (fs.initSender kR)),
            γ := γ', curCkaMsg := some T', tcur := t' }
      let gMidL : Ctx Γ T (Option Sig) SS RS M E :=
        { s₁L with
            st := Function.update sL.1.g.st P stL₁
            epoch := Function.update sL.1.g.epoch P t'
            idx := Function.update sL.1.g.idx P 0 }
      let gMidR : Ctx Γ T Sig (Option SS) (Option RS) M E :=
        { s₁R with
            st := Function.update sR.1.g.st P stR₁
            epoch := Function.update sR.1.g.epoch P t'
            idx := Function.update sR.1.g.idx P 0 }
      ActiveInv fs Δcka qep tL t b
        ({ sL.1 with g := gMidL, h := hL' }, pgL')
        ({ sR.1 with g := gMidR, h := hR' }, sR.2) →
      CloseBy
        (fR ((some (γ', T', σL', fs.initSender kL), hL'), pgL'))
        (fM ((some (γ', T', σR', if ext then none else some (fs.initSender kR)), hR'), sR.2))
        (fL ((some (γ', T', σR', if ext then none else some (fs.initSender kR)), hR'), sR.2))) :
    CloseBy
      (runHM (eagerOracleImpl prng)
        ((hooksPRNG cka prng fs ⟨false, tL, t⟩).startSend s₁_epL P
          (sR.1.g.epoch P + 1) (sR.1.g.st P).γ (sL.1.g.st P).root r) sL.1.h sL.2 >>= fR)
      (runHM (FSAEAD.oracleImpl fs)
        ((hooksFS cka prng fs Δcka ⟨false, tL, t⟩ 0).startSend s₁_epR P
          (sR.1.g.epoch P + 1) (sR.1.g.st P).γ (sR.1.g.st P).root r) sR.1.h sR.2 >>= fM)
      (runHM (FSAEAD.oracleImpl fs)
        ((hooksFS cka prng fs Δcka ⟨false, tL, t⟩ 0).startSend s₁_epR P
          (sR.1.g.epoch P + 1) (sR.1.g.st P).γ (sR.1.g.st P).root r) sR.1.h sR.2 >>= fL) := by
  rw [runHM_startSend_prng_eq, runHM_startSend_fs_eq, bind_assoc, bind_assoc, bind_assoc]
  refine closeBy_bind (optSample CCoins r) fun coins => ?_
  rcases h.epoch_of_sendsIn_succ hPs_next with ⟨hPs_stay, hPr, hPs1, hepM, hall_ep⟩
  set c := cka.send (sR.1.g.st P).γ coins
  rcases lt_trichotomy t (sR.1.g.epoch P + 1) with hgt | rfl | hlt
  · have hnot_lt : ¬(sR.1.g.epoch P < t) := by omega
    have hrootL : (sL.1.g.st P).root = some (sR.1.g.st P).root := by
      rw [h.root_eq P]; simp [hnot_lt]
    set p := prng.up (sR.1.g.st P).root c.2.2
    have hL_eval :
        runHM (eagerOracleImpl prng)
          ((hooksPRNG cka prng fs ⟨false, tL, t⟩).startSend s₁_epL P (sR.1.g.epoch P + 1)
            (sR.1.g.st P).γ (sL.1.g.st P).root (some coins)) sL.1.h sL.2 =
        pure ((some (c.1, c.2.1, some p.1, fs.initSender p.2),
          { cache := Function.update sL.1.h.cache (sR.1.g.epoch P + 1) (some (c.2.1, some p.1, p.2)) }), sL.2) := by
      simp [runHM, hooksPRNG, rootPRNG, hgt, hrootL, c, p]
    have hR_eval :
        runHM (FSAEAD.oracleImpl fs)
          ((hooksFS cka prng fs Δcka ⟨false, tL, t⟩ 0).startSend s₁_epR P (sR.1.g.epoch P + 1)
            (sR.1.g.st P).γ (sR.1.g.st P).root (some coins)) sR.1.h sR.2 =
        pure ((some (c.1, c.2.1, p.1, if false then none else some (fs.initSender p.2)),
          { sR.1.h with cache := Function.update sR.1.h.cache (sR.1.g.epoch P + 1) (some (c.2.1, p.1, p.2, false)) }), sR.2) := by
      simp [runHM, hooksFS, rootFS, extOf, hgt, c, p]
    rw [hL_eval, hR_eval, pure_bind, pure_bind, pure_bind]
    exact hcont c.1 c.2.1 (some p.1) p.2 sL.2 p.1 p.2 false _ _
      (h.advance_core hPs_next hqep bad c.1 c.2.1 (some p.1) p.2 sL.2 p.1 p.2 false sR.1.h
        (by simp; omega) (fun _ => rfl) (by simp; omega) ⟨rfl, rfl, rfl, rfl⟩
        (fun ht => absurd ht (by omega)) (fun ht => absurd ht (by omega)))
  · have hbef := h.before_t (by rw [hepM]; omega)
    rcases hbef with ⟨hbL, hcorrL, hprngL, hprfL, htableL, hroot_σ, _,
      htableR, hsessR, hfsTransR, hfsCountR, hfsSCorrR, hextR, k_fs, hslot, hosR⟩
    rw [hepM] at hcorrL
    have hrootP_σ : (sR.1.g.st P).root = sL.2.1.σ := hroot_σ P ((hall_ep P).trans hepM.symm)
    cases hheal : tL.isSome && decide (sR.1.g.epoch P + 1 = healEpoch tL)
    · have hcorr0 : sL.2.1.corr = false :=
        hcorrL.trans (corr_false_of_validGuess hvalid rfl hheal)
      set p := prng.up sL.2.1.σ c.2.2
      have hL_eval :
          runHM (eagerOracleImpl prng)
            ((hooksPRNG cka prng fs ⟨false, tL, sR.1.g.epoch P + 1⟩).startSend s₁_epL P (sR.1.g.epoch P + 1)
              (sR.1.g.st P).γ (sL.1.g.st P).root (some coins)) sL.1.h sL.2 =
          pure ((some (c.1, c.2.1, some p.1, fs.initSender k_fs),
            { cache := Function.update sL.1.h.cache (sR.1.g.epoch P + 1) (some (c.2.1, some p.1, k_fs)) }),
            ({ sL.2.1 with prf := true, table := [(c.2.2, k_fs)] }, .done)) := by
        rcases sL with ⟨esL, pg, sl⟩
        dsimp only at hbL hcorr0 hprngL hprfL htableL hslot ⊢
        subst hslot
        simp only [hooksPRNG, rootPRNG, decide_mode_tH_eq, lt_self_iff_false, ↓reduceIte,
          hheal, Bool.false_eq_true]
        simp [runHM, liftP,
          PRFPRNG.challPrfQuery, outerFull, eagerOracleImpl, eagerChallPrf,
          liftPG, drawKey, consumeKey, hcorr0, hprngL, hbL, htableL, c, p]
      have hR_eval :
          runHM (FSAEAD.oracleImpl fs)
            ((hooksFS cka prng fs Δcka ⟨false, tL, sR.1.g.epoch P + 1⟩ 0).startSend s₁_epR P (sR.1.g.epoch P + 1)
              (sR.1.g.st P).γ (sR.1.g.st P).root (some coins)) sR.1.h sR.2 =
          (($ᵗ K : ProbComp K) >>= fun k =>
            pure ((some (c.1, c.2.1, p.1, if true then none else some (fs.initSender k)),
              { ({ sR.1.h with table := [(c.2.2, k)], sessions := [c.2.2] } : FSState T Sig K I SS RS E) with
                  cache := Function.update sR.1.h.cache (sR.1.g.epoch P + 1) (some (c.2.1, p.1, k, true)) }), sR.2)) := by
        simp only [hooksFS, rootFS, extOf, isExt, decide_mode_tH_eq, lt_self_iff_false, ↓reduceIte,
          hheal, Bool.false_eq_true]
        simp [runHM, lookupF,
          htableR, hsessR, hrootP_σ, StateT.run_bind,
          simulateQ_outerFull_sampleT, bind_map_left, c, p]
      rw [hL_eval, hR_eval, pure_bind, bind_assoc, bind_assoc]
      refine closeBy_bind_right_const fun k => ?_
      simp only [pure_bind]
      exact hcont c.1 c.2.1 (some p.1) k_fs ({ sL.2.1 with prf := true, table := [(c.2.2, k_fs)] }, .done)
        p.1 k true _ _
        (h.advance_core hPs_next hqep bad c.1 c.2.1 (some p.1) k_fs
          ({ sL.2.1 with prf := true, table := [(c.2.2, k_fs)] }, .done) p.1 k true
          { sR.1.h with table := [(c.2.2, k)], sessions := [c.2.2] }
          (by simp) (fun hne => absurd rfl hne) (by simp) ⟨rfl, rfl, rfl, rfl⟩
          (fun _ => by simp [hosR, FSAEAD.initState, hextR])
          (fun ht => absurd ht (by omega)))
    · have hL_eval :
          runHM (eagerOracleImpl prng)
            ((hooksPRNG cka prng fs ⟨false, tL, sR.1.g.epoch P + 1⟩).startSend s₁_epL P (sR.1.g.epoch P + 1)
              (sR.1.g.st P).γ (sL.1.g.st P).root (some coins)) sL.1.h sL.2 =
          (($ᵗ I : ProbComp I) >>= fun Ir =>
            let p := prng.up sL.2.1.σ Ir
            pure ((some (c.1, c.2.1, some p.1, fs.initSender k_fs),
              { cache := Function.update sL.1.h.cache (sR.1.g.epoch P + 1) (some (c.2.1, some p.1, k_fs)) }),
              ({ sL.2.1 with σ := p.1, corr := true, prng := true }, .done))) := by
        rcases sL with ⟨esL, pg, sl⟩
        dsimp only at hbL hprfL hslot ⊢
        subst hslot
        simp only [hooksPRNG, rootPRNG, decide_mode_tH_eq, lt_self_iff_false, ↓reduceIte, hheal]
        simp [runHM, liftP,
          PRFPRNG.challPrngQuery, PRFPRNG.corrQuery, PRFPRNG.samIfNec, PRFPRNG.corrImpl,
          outerFull, eagerOracleImpl, eagerChallPrng, eagerCorr,
          liftPG, drawKey, consumeKey, hbL, hprfL, StateT.run_bind, simulateQ_bind,
          bind_map_left, c]
      have hR_eval :
          runHM (FSAEAD.oracleImpl fs)
            ((hooksFS cka prng fs Δcka ⟨false, tL, sR.1.g.epoch P + 1⟩ 0).startSend s₁_epR P (sR.1.g.epoch P + 1)
              (sR.1.g.st P).γ (sR.1.g.st P).root (some coins)) sR.1.h sR.2 =
          (($ᵗ I : ProbComp I) >>= fun Ir => ($ᵗ K : ProbComp K) >>= fun k =>
            let p := prng.up sL.2.1.σ Ir
            pure ((some (c.1, c.2.1, p.1, if true then none else some (fs.initSender k)),
              { ({ sR.1.h with sessions := [Ir] } : FSState T Sig K I SS RS E) with
                  cache := Function.update sR.1.h.cache (sR.1.g.epoch P + 1) (some (c.2.1, p.1, k, true)) }), sR.2)) := by
        simp only [hooksFS, rootFS, extOf, isExt, decide_mode_tH_eq, lt_self_iff_false, ↓reduceIte,
          hheal]
        simp [runHM,
          hsessR, hrootP_σ, StateT.run_bind, simulateQ_bind,
          simulateQ_outerFull_sampleT, bind_map_left, c]
      rw [hL_eval, hR_eval, bind_assoc, bind_assoc, bind_assoc]
      refine closeBy_bind ($ᵗ I) fun Ir => ?_
      set p := prng.up sL.2.1.σ Ir
      simp only [pure_bind, bind_assoc]
      refine closeBy_bind_right_const fun k => ?_
      exact hcont c.1 c.2.1 (some p.1) k_fs ({ sL.2.1 with σ := p.1, corr := true, prng := true }, .done)
        p.1 k true _ _
        (h.advance_core hPs_next hqep bad c.1 c.2.1 (some p.1) k_fs
          ({ sL.2.1 with σ := p.1, corr := true, prng := true }, .done) p.1 k true
          { sR.1.h with sessions := [Ir] }
          (by simp) (fun hne => absurd rfl hne) (by simp) ⟨rfl, rfl, rfl, rfl⟩
          (fun _ => by simp [hosR, FSAEAD.initState, hextR])
          (fun ht => absurd ht (by omega)))
  · have hbef := h.before_t (by rw [hepM]; omega)
    rcases hbef with ⟨hbL, hcorrL, hprngL, hprfL, htableL, hroot_σ, _,
      htableR, hsessR, hfsTransR, hfsCountR, hfsSCorrR, hextR, k_fs, hslot, hosR⟩
    rw [hepM] at hcorrL
    have hrootP_σ : (sR.1.g.st P).root = sL.2.1.σ := hroot_σ P ((hall_ep P).trans hepM.symm)
    have hnot_gt : ¬(t < sR.1.g.epoch P + 1) := by omega
    have hne_t : sR.1.g.epoch P + 1 ≠ t := by omega
    cases hheal : tL.isSome && decide (sR.1.g.epoch P + 1 = healEpoch tL)
    · have hcorr_eq : (tL.isSome && decide (sR.1.g.epoch P + 1 < healEpoch tL)) =
          (tL.isSome && decide (sR.1.g.epoch P < healEpoch tL)) := by
        cases tL with
        | none => rfl
        | some l =>
          rw [Option.isSome, Bool.true_and, decide_eq_false_iff_not] at hheal
          rw [Option.isSome, Bool.true_and, Bool.true_and, decide_eq_decide]
          dsimp only [healEpoch] at hheal ⊢
          omega
      cases hcorr : tL.isSome && decide (sR.1.g.epoch P + 1 < healEpoch tL)
      · have hcorr0 : sL.2.1.corr = false := hcorrL.trans (hcorr_eq.symm.trans hcorr)
        set p := prng.up sL.2.1.σ c.2.2
        have hL_eval :
            runHM (eagerOracleImpl prng)
              ((hooksPRNG cka prng fs ⟨false, tL, t⟩).startSend s₁_epL P (sR.1.g.epoch P + 1)
                (sR.1.g.st P).γ (sL.1.g.st P).root (some coins)) sL.1.h sL.2 =
            pure ((some (c.1, c.2.1, none, fs.initSender p.2),
              { cache := Function.update sL.1.h.cache (sR.1.g.epoch P + 1) (some (c.2.1, none, p.2)) }),
              ({ sL.2.1 with σ := p.1, corr := false }, sL.2.2)) := by
          rcases sL with ⟨esL, pg, sl⟩
          dsimp only at hcorr0 hprfL ⊢
          simp only [hooksPRNG, rootPRNG, decide_mode_tH_eq, decide_mode_tH_lt, hnot_gt, hne_t,
            hheal, hcorr, Bool.false_eq_true, ↓reduceIte]
          simp [runHM,
            liftP, PRFPRNG.processQuery, PRFPRNG.processImpl, PRFPRNG.samIfNec,
            outerFull, eagerOracleImpl, eagerProcess, liftPG, hcorr0, hprfL, c, p]
        have hR_eval :
            runHM (FSAEAD.oracleImpl fs)
              ((hooksFS cka prng fs Δcka ⟨false, tL, t⟩ 0).startSend s₁_epR P (sR.1.g.epoch P + 1)
                (sR.1.g.st P).γ (sR.1.g.st P).root (some coins)) sR.1.h sR.2 =
            pure ((some (c.1, c.2.1, p.1, if false then none else some (fs.initSender p.2)),
              { sR.1.h with cache := Function.update sR.1.h.cache (sR.1.g.epoch P + 1) (some (c.2.1, p.1, p.2, false)) }), sR.2) := by
          simp only [hooksFS, rootFS, extOf, decide_mode_tH_eq, hnot_gt, hne_t, hheal,
            Bool.false_eq_true, ↓reduceIte]
          simp [runHM, hrootP_σ, c, p]
        rw [hL_eval, hR_eval, pure_bind, pure_bind, pure_bind]
        exact hcont c.1 c.2.1 none p.2 ({ sL.2.1 with σ := p.1, corr := false }, sL.2.2)
          p.1 p.2 false _ _
          (h.advance_core hPs_next hqep bad c.1 c.2.1 none p.2
            ({ sL.2.1 with σ := p.1, corr := false }, sL.2.2) p.1 p.2 false sR.1.h
            (by simp [hne_t]) (fun _ => rfl)
            (by simp only [hlt, hcorr, Bool.false_eq_true, not_false_eq_true, and_self, ↓reduceIte])
            ⟨rfl, rfl, rfl, rfl⟩
            (fun ht => absurd ht hne_t)
            (fun _ => ⟨hbL, hcorr.symm, hprngL, hprfL, htableL, rfl,
              htableR, hsessR, hfsTransR, hfsCountR, hfsSCorrR, hextR, k_fs, hslot, hosR⟩))
      · set p := prng.up sL.2.1.σ c.2.2
        have hL_eval :
            runHM (eagerOracleImpl prng)
              ((hooksPRNG cka prng fs ⟨false, tL, t⟩).startSend s₁_epL P (sR.1.g.epoch P + 1)
                (sR.1.g.st P).γ (sL.1.g.st P).root (some coins)) sL.1.h sL.2 =
            pure ((some (c.1, c.2.1, some p.1, fs.initSender p.2),
              { cache := Function.update sL.1.h.cache (sR.1.g.epoch P + 1) (some (c.2.1, some p.1, p.2)) }),
              ({ sL.2.1 with σ := p.1, corr := true }, sL.2.2)) := by
          rcases sL with ⟨esL, pg, sl⟩
          dsimp only at hprfL ⊢
          simp only [hooksPRNG, rootPRNG, processCorr, decide_mode_tH_eq, decide_mode_tH_lt, hnot_gt,
            hne_t, hheal, hcorr, Bool.false_eq_true, ↓reduceIte]
          simp [runHM, liftP, PRFPRNG.processQuery, PRFPRNG.corrQuery,
            PRFPRNG.processImpl, PRFPRNG.corrImpl, PRFPRNG.samIfNec,
            outerFull, eagerOracleImpl, eagerProcess, eagerCorr, liftPG, hprfL, c, p]
        have hR_eval :
            runHM (FSAEAD.oracleImpl fs)
              ((hooksFS cka prng fs Δcka ⟨false, tL, t⟩ 0).startSend s₁_epR P (sR.1.g.epoch P + 1)
                (sR.1.g.st P).γ (sR.1.g.st P).root (some coins)) sR.1.h sR.2 =
            pure ((some (c.1, c.2.1, p.1, if false then none else some (fs.initSender p.2)),
              { sR.1.h with cache := Function.update sR.1.h.cache (sR.1.g.epoch P + 1) (some (c.2.1, p.1, p.2, false)) }), sR.2) := by
          simp only [hooksFS, rootFS, extOf, decide_mode_tH_eq, hnot_gt, hne_t, hheal,
            Bool.false_eq_true, ↓reduceIte]
          simp [runHM, hrootP_σ, c, p]
        rw [hL_eval, hR_eval, pure_bind, pure_bind, pure_bind]
        exact hcont c.1 c.2.1 (some p.1) p.2 ({ sL.2.1 with σ := p.1, corr := true }, sL.2.2)
          p.1 p.2 false _ _
          (h.advance_core hPs_next hqep bad c.1 c.2.1 (some p.1) p.2
            ({ sL.2.1 with σ := p.1, corr := true }, sL.2.2) p.1 p.2 false sR.1.h
            (by simp [hne_t]) (fun _ => rfl)
            (by simp only [hlt, hcorr, not_true_eq_false, and_false, ↓reduceIte])
            ⟨rfl, rfl, rfl, rfl⟩
            (fun ht => absurd ht hne_t)
            (fun _ => ⟨hbL, hcorr.symm, hprngL, hprfL, htableL, rfl,
              htableR, hsessR, hfsTransR, hfsCountR, hfsSCorrR, hextR, k_fs, hslot, hosR⟩))
    · have hcorr_next : (tL.isSome && decide (sR.1.g.epoch P + 1 < healEpoch tL)) = false := by
        cases tL with
        | none => rfl
        | some l =>
          rw [Option.isSome, Bool.true_and, decide_eq_true_eq] at hheal
          rw [Option.isSome, Bool.true_and, decide_eq_false_iff_not]
          dsimp only [healEpoch] at hheal ⊢
          omega
      have hL_eval :
          runHM (eagerOracleImpl prng)
            ((hooksPRNG cka prng fs ⟨false, tL, t⟩).startSend s₁_epL P (sR.1.g.epoch P + 1)
              (sR.1.g.st P).γ (sL.1.g.st P).root (some coins)) sL.1.h sL.2 =
          (($ᵗ I : ProbComp I) >>= fun Ir =>
            let p := prng.up sL.2.1.σ Ir
            pure ((some (c.1, c.2.1, none, fs.initSender p.2),
              { cache := Function.update sL.1.h.cache (sR.1.g.epoch P + 1) (some (c.2.1, none, p.2)) }),
              ({ sL.2.1 with σ := p.1, corr := false }, sL.2.2))) := by
        rcases sL with ⟨esL, pg, sl⟩
        dsimp only at hprfL ⊢
        simp only [hooksPRNG, rootPRNG, decide_mode_tH_eq, hnot_gt, hne_t, hheal, ↓reduceIte]
        simp [runHM,
          liftP, PRFPRNG.processQuery, PRFPRNG.processImpl, PRFPRNG.samIfNec,
          outerFull, eagerOracleImpl, eagerProcess, liftPG, hprfL,
          StateT.run_bind, simulateQ_bind, bind_map_left, c]
      have hR_eval :
          runHM (FSAEAD.oracleImpl fs)
            ((hooksFS cka prng fs Δcka ⟨false, tL, t⟩ 0).startSend s₁_epR P (sR.1.g.epoch P + 1)
              (sR.1.g.st P).γ (sR.1.g.st P).root (some coins)) sR.1.h sR.2 =
          (($ᵗ I : ProbComp I) >>= fun Ir =>
            let p := prng.up sL.2.1.σ Ir
            pure ((some (c.1, c.2.1, p.1, if false then none else some (fs.initSender p.2)),
              { sR.1.h with cache := Function.update sR.1.h.cache (sR.1.g.epoch P + 1) (some (c.2.1, p.1, p.2, false)) }), sR.2)) := by
        simp only [hooksFS, rootFS, extOf, decide_mode_tH_eq, hnot_gt, hne_t, hheal,
          Bool.false_eq_true, ↓reduceIte]
        simp [runHM,
          hrootP_σ, StateT.run_bind, simulateQ_outerFull_sampleT, bind_map_left, c]
      rw [hL_eval, hR_eval, bind_assoc, bind_assoc, bind_assoc]
      refine closeBy_bind ($ᵗ I) fun Ir => ?_
      set p := prng.up sL.2.1.σ Ir
      simp only [pure_bind]
      exact hcont c.1 c.2.1 none p.2 ({ sL.2.1 with σ := p.1, corr := false }, sL.2.2)
        p.1 p.2 false _ _
        (h.advance_core hPs_next hqep bad c.1 c.2.1 none p.2
          ({ sL.2.1 with σ := p.1, corr := false }, sL.2.2) p.1 p.2 false sR.1.h
          (by simp [hne_t]) (fun _ => rfl)
          (by simp only [hlt, hcorr_next, Bool.false_eq_true, not_false_eq_true, and_self, ↓reduceIte])
          ⟨rfl, rfl, rfl, rfl⟩
          (fun ht => absurd ht hne_t)
          (fun _ => ⟨hbL, hcorr_next.symm, hprngL, hprfL, htableL, rfl,
            htableR, hsessR, hfsTransR, hfsCountR, hfsSCorrR, hextR, k_fs, hslot, hosR⟩))

omit [DecidableEq T] [DecidableEq M] [DecidableEq E] [DecidableEq I] [Inhabited E]
  [SampleableType CCoins] [SampleableType I] [SampleableType K] in
theorem ActiveInv.epMgmt_advance
    {fs : FSAEADScheme K SS RS (Header T) M E} {Δcka qep : ℕ}
    {tL : Option ℕ} {t : ℕ} {b : Bool}
    {sL : StateL Γ T Sig SS RS M E K I} {sR : StateR Γ T Sig K I SS RS M E}
    (h : ActiveInv fs Δcka qep tL t b sL sR)
    {P : Party} (hPs_next : P.sendsIn (sR.1.g.epoch P + 1) = true)
    (hqep : ¬(qep < sR.1.g.epoch P + 1)) (bad : Bool) :
    let t' := sR.1.g.epoch P + 1
    let s₁L := if bad && !sL.1.g.safeCh (2 + Δcka) P then sL.1.g.leak t' else sL.1.g
    let s₁R := if bad && !sR.1.g.safeCh (2 + Δcka) P then sR.1.g.leak t' else sR.1.g
    let s₁_epL :=
      { s₁L with
          epoch := Function.update sL.1.g.epoch P t'
          idx := Function.update sL.1.g.idx P 0 }
    let s₁_epR :=
      { s₁R with
          epoch := Function.update sR.1.g.epoch P t'
          idx := Function.update sR.1.g.idx P 0 }
    sL.1.g.epMgmt (2 + Δcka) qep P bad = some s₁_epL ∧
    sR.1.g.epMgmt (2 + Δcka) qep P bad = some s₁_epR ∧
    (Policy.mk false tL t).leakDoom sL.1.g s₁_epL =
      (Policy.mk false tL t).leakDoom sR.1.g s₁_epR ∧
    s₁_epL.safeCh (2 + Δcka) P = s₁_epR.safeCh (2 + Δcka) P ∧
    s₁_epL.epoch P = t' ∧
    s₁_epR.epoch P = t' := by
  intro t' s₁L s₁R s₁_epL s₁_epR
  have hepP : sL.1.g.epoch P = sR.1.g.epoch P := congrFun h.epoch_eq P
  have hsafe := h.safeCh_eq (2 + Δcka) P
  have hs₁_tL : s₁L.tL = s₁R.tL := by
    dsimp only [s₁L, s₁R]; rw [hsafe]; split_ifs <;> simp [GameState.leak, h.tL_eq]
  have hs₁_leaks : s₁L.leaks = s₁R.leaks := by
    dsimp only [s₁L, s₁R]; rw [hsafe]; split_ifs <;> simp [GameState.leak, h.tL_eq, h.leaks_eq]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · dsimp only [GameState.epMgmt, s₁_epL, s₁L, t']
    simp only [hepP, hPs_next, ↓reduceIte, hqep, Option.some.injEq]
    split_ifs <;> simp [GameState.leak, hepP]
  · dsimp only [GameState.epMgmt, s₁_epR, s₁R, t']
    simp only [hPs_next, ↓reduceIte, hqep, Option.some.injEq]
    split_ifs <;> rfl
  · dsimp only [s₁_epL, s₁_epR]
    simp only [Policy.leakDoom, hs₁_leaks, h.epoch_eq]
  · dsimp only [s₁_epL, s₁_epR]
    simp only [GameState.safeCh, hs₁_tL, h.epoch_eq]
  · simp [s₁_epL]
  · simp [s₁_epR]

omit [DecidableEq T] [DecidableEq M] [DecidableEq E] [DecidableEq I] [Inhabited E]
  [SampleableType CCoins] [SampleableType I] [SampleableType K] in
theorem ActiveInv.epMgmt_stay
    {fs : FSAEADScheme K SS RS (Header T) M E} {Δcka qep : ℕ}
    {tL : Option ℕ} {t : ℕ} {b : Bool}
    {sL : StateL Γ T Sig SS RS M E K I} {sR : StateR Γ T Sig K I SS RS M E}
    (h : ActiveInv fs Δcka qep tL t b sL sR)
    {P : Party} (hPs_next : P.sendsIn (sR.1.g.epoch P + 1) = false) (bad : Bool) :
    P.sendsIn (sR.1.g.epoch P) = true ∧
    sL.1.g.epMgmt (2 + Δcka) qep P bad = some sL.1.g ∧
    sR.1.g.epMgmt (2 + Δcka) qep P bad = some sR.1.g ∧
    (Policy.mk false tL t).leakDoom sL.1.g sL.1.g =
      (Policy.mk false tL t).leakDoom sR.1.g sR.1.g := by
  have hPs : P.sendsIn (sR.1.g.epoch P) = true := by
    rw [Party.sendsIn_succ] at hPs_next
    simpa using hPs_next
  have hepP : sL.1.g.epoch P = sR.1.g.epoch P := congrFun h.epoch_eq P
  have hle_max := Party.le_max_apply sR.1.g.epoch P
  have hmax_le := h.maxEp_le_qep
  have hqep : ¬(qep < sR.1.g.epoch P) := by omega
  refine ⟨hPs, ?_, ?_, ?_⟩
  · simp [GameState.epMgmt, hepP, hPs_next, hqep]
  · simp [GameState.epMgmt, hPs_next, hqep]
  · simp only [Policy.leakDoom, h.leaks_eq, h.epoch_eq]

omit [DecidableEq I] [SampleableType CCoins] [SampleableType I] [SampleableType K] in
theorem runEM_implE_transmitE {ι : Type} {tspec : OracleSpec.{0, 0} ι} {OS HS Γv Sv SSv RSv : Type}
    (oimpl : QueryImpl tspec (StateT OS ProbComp))
    (hk : Hooks tspec HS Γ T Sig SS RS M E CCoins Γv Sv SSv RSv)
    (Δ qep maxSkip : ℕ) (cfg : Config M) (π : Policy)
    (P : Party) (m : M) (r : Option CCoins)
    (s : EState (VP Γv T Sv SSv RSv) M (Header T × E) HS × OS)
    (habort : s.1.abort = false) (hwin : s.1.g.win = false) :
    runEM oimpl
      (implE hk Δ qep maxSkip cfg π (Sum.inr (Sum.inl (Sum.inl (Sum.inl (Sum.inl (P, m, r))))))) s =
    match s.1.g.epMgmt Δ qep P r.isSome with
    | none => pure (none, s)
    | some s₁ =>
      if π.leakDoom s.1.g s₁ then
        pure (none, ({ s.1 with abort := true }, s.2))
      else
        runEM oimpl (vSendRecord hk Δ s₁ P m none r false) s := by
  change runEM oimpl (transmitE hk Δ qep π (P, m, r)) s = _
  dsimp only [transmitE]
  rw [runEM_bind, runEM_get, pure_bind]
  simp only [habort, hwin, Bool.false_or, Bool.false_eq_true, ↓reduceIte]
  cases s.1.g.epMgmt Δ qep P r.isSome with
  | none => exact runEM_pure oimpl none s
  | some s₁ =>
    dsimp only
    split_ifs with hdoom
    · exact runEM_abort_pure oimpl none s
    · rfl

omit [DecidableEq I] [SampleableType CCoins] [SampleableType I] [SampleableType K] in
theorem runEM_implE_challE {ι : Type} {tspec : OracleSpec.{0, 0} ι} {OS HS Γv Sv SSv RSv : Type}
    (oimpl : QueryImpl tspec (StateT OS ProbComp))
    (hk : Hooks tspec HS Γ T Sig SS RS M E CCoins Γv Sv SSv RSv)
    (Δ qep maxSkip t : ℕ) (π : Policy)
    (P : Party) (m₀ m₁ : M) (r : Option CCoins)
    (s : EState (VP Γv T Sv SSv RSv) M (Header T × E) HS × OS)
    (habort : s.1.abort = false) (hwin : s.1.g.win = false) :
    runEM oimpl
      (implE hk Δ qep maxSkip (Config.priv t) π
        (Sum.inr (Sum.inl (Sum.inl (Sum.inl (Sum.inr (P, m₀, m₁, r))))))) s =
    match s.1.g.epMgmt Δ qep P r.isSome with
    | none => pure (none, s)
    | some s₁ =>
      if !(s₁.safeCh Δ P) || !((Config.priv (Msg := M) t).challAllowedIn (s₁.epoch P)) then
        pure (none, s)
      else if π.leakDoom s.1.g s₁ then
        pure (none, ({ s.1 with abort := true }, s.2))
      else
        let m := if s.1.g.b then m₁ else m₀
        runEM oimpl (vSendRecord hk Δ s₁ P m (some (m₀, m₁)) r true) s := by
  change runEM oimpl (challE hk Δ qep (Config.priv t) π (P, m₀, m₁, r)) s = _
  dsimp only [challE]
  rw [runEM_bind, runEM_get, pure_bind]
  simp only [habort, hwin, Bool.false_or, Bool.false_eq_true, ↓reduceIte]
  cases s.1.g.epMgmt Δ qep P r.isSome with
  | none => exact runEM_pure oimpl none s
  | some s₁ =>
    dsimp only
    split_ifs with hcond hdoom hb
    · exact runEM_pure oimpl none s
    · exact runEM_abort_pure oimpl none s
    · rfl
    · simp only [Config.priv, Option.getD_none]; rfl

theorem closeBy_transmitE (cka : CKAScheme KC Γ CCoins T I) (prng : PRFPRNG KR Sig I K)
    (fs : FSAEADScheme K SS RS (Header T) M E) (Δcka qep : ℕ) (tL : Option ℕ) (t : ℕ) (b : Bool)
    (hvalid : lastLeakGuessAdmissible (2 + Δcka) tL t = true)
    (q : ((Party × M × Option CCoins) →ₒ Option (Header T × E)).Domain)
    (k : (AdvSpec Γ T Sig SS RS M CCoins E).Range (Sum.inr (Sum.inl (Sum.inl (Sum.inl (Sum.inl q))))) →
      OracleComp (AdvSpec Γ T Sig SS RS M CCoins E) Bool)
    (sL : StateL Γ T Sig SS RS M E K I) (sR : StateR Γ T Sig K I SS RS M E)
    (h : ActiveInv fs Δcka qep tL t b sL sR)
    (ih : ∀ u sL₁ sR₁, Inv15 fs Δcka qep tL t b sL₁ sR₁ →
      CloseByEng cka prng fs Δcka qep tL t b (k u) sL₁ sR₁) :
    CloseByEng cka prng fs Δcka qep tL t b
      (query (Sum.inr (Sum.inl (Sum.inl (Sum.inl (Sum.inl q))))) >>= k) sL sR := by
  rcases q with ⟨P, m, r⟩
  have hepP : sL.1.g.epoch P = sR.1.g.epoch P := congrFun h.epoch_eq P
  cases hPs_next : P.sendsIn (sR.1.g.epoch P + 1)
  · rcases h.epMgmt_stay hPs_next r.isSome with ⟨hPs, hepL, hepR, hdoom_eq⟩
    cases hdoom : (Policy.mk false tL t).leakDoom sR.1.g sR.1.g
    · rcases h.vSend_stay_transmit cka prng hPs m r sL.1.g sR.1.g with
        ⟨c, sL', sR', hvL, hvR, hInv'⟩
      rw [show ({ sL.1 with g := sL.1.g }, sL.2) = sL from rfl] at hvL
      rw [show ({ sR.1 with g := sR.1.g }, sR.2) = sR from rfl] at hvR
      refine closeBy_of_det_step cka prng fs Δcka qep tL t b _ k sL sL' sR sR' (some c) (some c)
        ?_ ?_ ih (Or.inr ⟨rfl, Or.inr hInv'⟩)
      · rw [runEM_implE_transmitE _ _ _ _ _ _ _ P m r sL h.abortL h.winL]
        simp only [hepL, hdoom_eq, hdoom, Bool.false_eq_true, ↓reduceIte]
        exact hvL
      · rw [runEM_implE_transmitE _ _ _ _ _ _ _ P m r sR h.abortR h.winR]
        simp only [hepR, hdoom, Bool.false_eq_true, ↓reduceIte]
        exact hvR
    · refine closeBy_of_det_step cka prng fs Δcka qep tL t b _ k
        sL ({ sL.1 with abort := true }, sL.2) sR ({ sR.1 with abort := true }, sR.2)
        none none ?_ ?_ ih (Or.inr ⟨rfl, Or.inl ⟨rfl, rfl, h.winFS, h.bFS⟩⟩)
      · rw [runEM_implE_transmitE _ _ _ _ _ _ _ P m r sL h.abortL h.winL]
        simp only [hepL, hdoom_eq, hdoom, ↓reduceIte]
      · rw [runEM_implE_transmitE _ _ _ _ _ _ _ P m r sR h.abortR h.winR]
        simp only [hepR, hdoom, ↓reduceIte]
  · by_cases hqep : qep < sR.1.g.epoch P + 1
    · have hepL : sL.1.g.epMgmt (2 + Δcka) qep P r.isSome = none := by
        simp only [GameState.epMgmt, hepP, hPs_next, ↓reduceIte, hqep]
      have hepR : sR.1.g.epMgmt (2 + Δcka) qep P r.isSome = none := by
        simp only [GameState.epMgmt, hPs_next, ↓reduceIte, hqep]
      refine closeBy_of_det_step cka prng fs Δcka qep tL t b _ k sL sL sR sR none none
        ?_ ?_ ih (Or.inr ⟨rfl, Or.inr h⟩)
      · rw [runEM_implE_transmitE _ _ _ _ _ _ _ P m r sL h.abortL h.winL]
        simp only [hepL]
      · rw [runEM_implE_transmitE _ _ _ _ _ _ _ P m r sR h.abortR h.winR]
        simp only [hepR]
    · rcases h.epMgmt_advance hPs_next hqep r.isSome with
        ⟨hepL, hepR, hdoom_eq, _, _, _⟩
      set t' := sR.1.g.epoch P + 1
      set s₁L := if r.isSome && !sL.1.g.safeCh (2 + Δcka) P then sL.1.g.leak t' else sL.1.g
      set s₁R := if r.isSome && !sR.1.g.safeCh (2 + Δcka) P then sR.1.g.leak t' else sR.1.g
      set s₁_epL :=
        { s₁L with
            epoch := Function.update sL.1.g.epoch P t'
            idx := Function.update sL.1.g.idx P 0 }
      set s₁_epR :=
        { s₁R with
            epoch := Function.update sR.1.g.epoch P t'
            idx := Function.update sR.1.g.idx P 0 }
      cases hdoom : (Policy.mk false tL t).leakDoom sR.1.g s₁_epR
      · unfold CloseByEng
        rw [evalEng_query_bind, evalEngM_query_bind, evalEngL_query_bind]
        have hs₁L_st : s₁_epL.st = sL.1.g.st := by
          dsimp only [s₁_epL, s₁L]; split_ifs <;> rfl
        have hs₁R_st : s₁_epR.st = sR.1.g.st := by
          dsimp only [s₁_epR, s₁R]; split_ifs <;> rfl
        have hstepL :=
          (runEM_implE_transmitE (eagerOracleImpl prng) (hooksPRNG cka prng fs ⟨false, tL, t⟩)
            (2 + Δcka) qep fs.maxSkip (Config.priv t) ⟨false, tL, t⟩ P m r sL h.abortL h.winL).trans
          (by
            simp only [hepL, hdoom_eq, hdoom, Bool.false_eq_true, ↓reduceIte]
            exact runEM_vSend_advance (eagerOracleImpl prng) (hooksPRNG cka prng fs ⟨false, tL, t⟩)
              (2 + Δcka) s₁_epL P m none r false sL
              (by rw [hs₁L_st]; exact h.idL P)
              (by rw [hs₁L_st, h.tcurL P]; exact hPs_next)
              (fun _ => rfl))
        have hstepR :=
          (runEM_implE_transmitE (FSAEAD.oracleImpl fs) (hooksFS cka prng fs Δcka ⟨false, tL, t⟩ 0)
            (2 + Δcka) qep fs.maxSkip (Config.priv t) ⟨false, tL, t⟩ P m r sR h.abortR h.winR).trans
          (by
            simp only [hepR, hdoom, Bool.false_eq_true, ↓reduceIte]
            exact runEM_vSend_advance (FSAEAD.oracleImpl fs) (hooksFS cka prng fs Δcka ⟨false, tL, t⟩ 0)
              (2 + Δcka) s₁_epR P m none r false sR
              (by rw [hs₁R_st]; exact h.idR P)
              (by rw [hs₁R_st, h.tcurR P]; exact hPs_next)
              (fun _ => rfl))
        rw [hstepL, hstepR, bind_assoc, bind_assoc, bind_assoc]
        simp only [hs₁L_st, hs₁R_st, h.tcurL P, h.tcurR P, h.γ_eq P]
        refine h.closeBy_startSend cka prng hvalid hPs_next hqep r.isSome r s₁_epL s₁_epR _ _ _ ?_
        intro γ' T' σL' kL pgL' σR' kR ext hL' hR'
          t'_mid s₁L_mid s₁R_mid stL₁_mid stR₁_mid gMidL gMidR h_mid
        dsimp only
        have hPs_mid : P.sendsIn (({ sR.1 with g := gMidR, h := hR' }, sR.2).1.g.epoch P) = true := by
          simpa [gMidR, t'_mid] using hPs_next
        rcases h_mid.vSend_stay_transmit cka prng hPs_mid m r sL.1.g sR.1.g with
          ⟨c, sL', sR', hvL, hvR, hInv'⟩
        dsimp only [gMidL, gMidR, stL₁_mid, stR₁_mid, s₁L_mid, s₁R_mid, t'_mid,
          s₁_epL, s₁_epR, s₁L, s₁R, t'] at hvL hvR ⊢
        rw [hvL, hvR, pure_bind, pure_bind, pure_bind]
        exact ih (some c) sL' sR' (Or.inr hInv')
      · refine closeBy_of_det_step cka prng fs Δcka qep tL t b _ k
          sL ({ sL.1 with abort := true }, sL.2) sR ({ sR.1 with abort := true }, sR.2)
          none none ?_ ?_ ih (Or.inr ⟨rfl, Or.inl ⟨rfl, rfl, h.winFS, h.bFS⟩⟩)
        · rw [runEM_implE_transmitE _ _ _ _ _ _ _ P m r sL h.abortL h.winL]
          simp only [hepL, hdoom_eq, hdoom, ↓reduceIte]
        · rw [runEM_implE_transmitE _ _ _ _ _ _ _ P m r sR h.abortR h.winR]
          simp only [hepR, hdoom, ↓reduceIte]

theorem closeBy_challE (cka : CKAScheme KC Γ CCoins T I) (prng : PRFPRNG KR Sig I K)
    (fs : FSAEADScheme K SS RS (Header T) M E) (Δcka qep : ℕ) (tL : Option ℕ) (t : ℕ) (b : Bool)
    (hvalid : lastLeakGuessAdmissible (2 + Δcka) tL t = true)
    (q : ((Party × M × M × Option CCoins) →ₒ Option (Header T × E)).Domain)
    (k : (AdvSpec Γ T Sig SS RS M CCoins E).Range (Sum.inr (Sum.inl (Sum.inl (Sum.inl (Sum.inr q))))) →
      OracleComp (AdvSpec Γ T Sig SS RS M CCoins E) Bool)
    (sL : StateL Γ T Sig SS RS M E K I) (sR : StateR Γ T Sig K I SS RS M E)
    (h : ActiveInv fs Δcka qep tL t b sL sR)
    (ih : ∀ u sL₁ sR₁, Inv15 fs Δcka qep tL t b sL₁ sR₁ →
      CloseByEng cka prng fs Δcka qep tL t b (k u) sL₁ sR₁) :
    CloseByEng cka prng fs Δcka qep tL t b
      (query (Sum.inr (Sum.inl (Sum.inl (Sum.inl (Sum.inr q))))) >>= k) sL sR := by
  rcases q with ⟨P, m₀, m₁, r⟩
  have hepP : sL.1.g.epoch P = sR.1.g.epoch P := congrFun h.epoch_eq P
  have hsafe_eq := h.safeCh_eq (2 + Δcka) P
  cases hPs_next : P.sendsIn (sR.1.g.epoch P + 1)
  · rcases h.epMgmt_stay hPs_next r.isSome with ⟨hPs, hepL, hepR, hdoom_eq⟩
    by_cases hcond : (!(sR.1.g.safeCh (2 + Δcka) P) || !((Config.priv (Msg := M) t).challAllowedIn (sR.1.g.epoch P))) = true
    · refine closeBy_of_det_step cka prng fs Δcka qep tL t b _ k sL sL sR sR none none
        ?_ ?_ ih (Or.inr ⟨rfl, Or.inr h⟩)
      · rw [runEM_implE_challE _ _ _ _ _ _ _ P m₀ m₁ r sL h.abortL h.winL]
        simp only [hepL, hsafe_eq, hepP, hcond, ↓reduceIte]
      · rw [runEM_implE_challE _ _ _ _ _ _ _ P m₀ m₁ r sR h.abortR h.winR]
        simp only [hepR, hcond, ↓reduceIte]
    · simp only [Bool.not_eq_true, Bool.or_eq_false_iff, Bool.not_eq_false'] at hcond
      have hsafe : sR.1.g.safeCh (2 + Δcka) P = true := hcond.1
      have ht : sR.1.g.epoch P = t := by simpa [Config.priv] using hcond.2
      have hchallL : (Config.priv (Msg := M) t).challAllowedIn (sL.1.g.epoch P) = true := by
        simp [Config.priv, hepP, ht]
      have hchallR : (Config.priv (Msg := M) t).challAllowedIn (sR.1.g.epoch P) = true := by
        simp [Config.priv, ht]
      cases hdoom : (Policy.mk false tL t).leakDoom sR.1.g sR.1.g
      · rcases h.vSend_stay_chall cka prng hPs ht hsafe m₀ m₁ r sL.1.g sR.1.g with
          ⟨c, sL', sR', hvL, hvR, hInv'⟩
        rw [show ({ sL.1 with g := sL.1.g }, sL.2) = sL from rfl] at hvL
        rw [show ({ sR.1 with g := sR.1.g }, sR.2) = sR from rfl] at hvR
        refine closeBy_of_det_step cka prng fs Δcka qep tL t b _ k sL sL' sR sR' (some c) (some c)
          ?_ ?_ ih (Or.inr ⟨rfl, Or.inr hInv'⟩)
        · rw [runEM_implE_challE _ _ _ _ _ _ _ P m₀ m₁ r sL h.abortL h.winL]
          simp only [h.bL, hepL, hsafe_eq, hsafe, hchallL, Bool.not_true, Bool.false_or,
            Bool.false_eq_true, ↓reduceIte, hdoom_eq, hdoom]
          exact hvL
        · rw [runEM_implE_challE _ _ _ _ _ _ _ P m₀ m₁ r sR h.abortR h.winR]
          simp only [h.bR, hepR, hsafe, hchallR, Bool.not_true, Bool.false_or,
            Bool.false_eq_true, ↓reduceIte, hdoom]
          exact hvR
      · refine closeBy_of_det_step cka prng fs Δcka qep tL t b _ k
          sL ({ sL.1 with abort := true }, sL.2) sR ({ sR.1 with abort := true }, sR.2)
          none none ?_ ?_ ih (Or.inr ⟨rfl, Or.inl ⟨rfl, rfl, h.winFS, h.bFS⟩⟩)
        · rw [runEM_implE_challE _ _ _ _ _ _ _ P m₀ m₁ r sL h.abortL h.winL]
          simp only [hepL, hsafe_eq, hsafe, hchallL, Bool.not_true, Bool.false_or,
            Bool.false_eq_true, ↓reduceIte, hdoom_eq, hdoom]
        · rw [runEM_implE_challE _ _ _ _ _ _ _ P m₀ m₁ r sR h.abortR h.winR]
          simp only [hepR, hsafe, hchallR, Bool.not_true, Bool.false_or,
            Bool.false_eq_true, ↓reduceIte, hdoom]
  · by_cases hqep : qep < sR.1.g.epoch P + 1
    · have hepL : sL.1.g.epMgmt (2 + Δcka) qep P r.isSome = none := by
        simp only [GameState.epMgmt, hepP, hPs_next, ↓reduceIte, hqep]
      have hepR : sR.1.g.epMgmt (2 + Δcka) qep P r.isSome = none := by
        simp only [GameState.epMgmt, hPs_next, ↓reduceIte, hqep]
      refine closeBy_of_det_step cka prng fs Δcka qep tL t b _ k sL sL sR sR none none
        ?_ ?_ ih (Or.inr ⟨rfl, Or.inr h⟩)
      · rw [runEM_implE_challE _ _ _ _ _ _ _ P m₀ m₁ r sL h.abortL h.winL]
        simp only [hepL]
      · rw [runEM_implE_challE _ _ _ _ _ _ _ P m₀ m₁ r sR h.abortR h.winR]
        simp only [hepR]
    · rcases h.epMgmt_advance hPs_next hqep r.isSome with
        ⟨hepL, hepR, hdoom_eq, hsafe_s₁, hep_s₁L, hep_s₁R⟩
      set t' := sR.1.g.epoch P + 1
      set s₁L := if r.isSome && !sL.1.g.safeCh (2 + Δcka) P then sL.1.g.leak t' else sL.1.g
      set s₁R := if r.isSome && !sR.1.g.safeCh (2 + Δcka) P then sR.1.g.leak t' else sR.1.g
      set s₁_epL :=
        { s₁L with
            epoch := Function.update sL.1.g.epoch P t'
            idx := Function.update sL.1.g.idx P 0 }
      set s₁_epR :=
        { s₁R with
            epoch := Function.update sR.1.g.epoch P t'
            idx := Function.update sR.1.g.idx P 0 }
      by_cases hcond : (!(s₁_epR.safeCh (2 + Δcka) P) || !((Config.priv (Msg := M) t).challAllowedIn (s₁_epR.epoch P))) = true
      · refine closeBy_of_det_step cka prng fs Δcka qep tL t b _ k sL sL sR sR none none
          ?_ ?_ ih (Or.inr ⟨rfl, Or.inr h⟩)
        · rw [runEM_implE_challE _ _ _ _ _ _ _ P m₀ m₁ r sL h.abortL h.winL]
          simp only [hepL, hsafe_s₁, hep_s₁L, ← hep_s₁R, hcond, ↓reduceIte]
        · rw [runEM_implE_challE _ _ _ _ _ _ _ P m₀ m₁ r sR h.abortR h.winR]
          simp only [hepR, hcond, ↓reduceIte]
      · simp only [Bool.not_eq_true, Bool.or_eq_false_iff, Bool.not_eq_false'] at hcond
        have hsafe₁ : s₁_epR.safeCh (2 + Δcka) P = true := hcond.1
        have ht₁ : s₁_epR.epoch P = t := by simpa [Config.priv] using hcond.2
        have ht' : t' = t := hep_s₁R ▸ ht₁
        have hchallL : (Config.priv (Msg := M) t).challAllowedIn (s₁_epL.epoch P) = true := by
          simp [Config.priv, hep_s₁L, ht']
        have hchallR : (Config.priv (Msg := M) t).challAllowedIn (s₁_epR.epoch P) = true := by
          simp [Config.priv, ht₁]
        cases hdoom : (Policy.mk false tL t).leakDoom sR.1.g s₁_epR
        · unfold CloseByEng
          rw [evalEng_query_bind, evalEngM_query_bind, evalEngL_query_bind]
          have hs₁L_st : s₁_epL.st = sL.1.g.st := by
            dsimp only [s₁_epL, s₁L]; split_ifs <;> rfl
          have hs₁R_st : s₁_epR.st = sR.1.g.st := by
            dsimp only [s₁_epR, s₁R]; split_ifs <;> rfl
          let mL := if b then m₁ else m₀
          have hstepL :=
            (runEM_implE_challE (eagerOracleImpl prng) (hooksPRNG cka prng fs ⟨false, tL, t⟩)
              (2 + Δcka) qep fs.maxSkip t ⟨false, tL, t⟩ P m₀ m₁ r sL h.abortL h.winL).trans
            (by
              simp only [h.bL, hepL, hsafe_s₁, hsafe₁, hchallL,
                Bool.not_true, Bool.false_or, Bool.false_eq_true, ↓reduceIte, hdoom_eq, hdoom]
              exact runEM_vSend_advance (eagerOracleImpl prng) (hooksPRNG cka prng fs ⟨false, tL, t⟩)
                (2 + Δcka) s₁_epL P mL (some (m₀, m₁)) r true sL
                (by rw [hs₁L_st]; exact h.idL P)
                (by rw [hs₁L_st, h.tcurL P]; exact hPs_next)
                (fun _ => rfl))
          have hstepR :=
            (runEM_implE_challE (FSAEAD.oracleImpl fs) (hooksFS cka prng fs Δcka ⟨false, tL, t⟩ 0)
              (2 + Δcka) qep fs.maxSkip t ⟨false, tL, t⟩ P m₀ m₁ r sR h.abortR h.winR).trans
            (by
              simp only [h.bR, hepR, hsafe₁, hchallR,
                Bool.not_true, Bool.false_or, Bool.false_eq_true, ↓reduceIte, hdoom]
              exact runEM_vSend_advance (FSAEAD.oracleImpl fs) (hooksFS cka prng fs Δcka ⟨false, tL, t⟩ 0)
                (2 + Δcka) s₁_epR P m₀ (some (m₀, m₁)) r true sR
                (by rw [hs₁R_st]; exact h.idR P)
                (by rw [hs₁R_st, h.tcurR P]; exact hPs_next)
                (fun _ => rfl))
          rw [hstepL, hstepR, bind_assoc, bind_assoc, bind_assoc]
          simp only [hs₁L_st, hs₁R_st, h.tcurL P, h.tcurR P, h.γ_eq P]
          refine h.closeBy_startSend cka prng hvalid hPs_next hqep r.isSome r s₁_epL s₁_epR _ _ _ ?_
          intro γ' T' σL' kL pgL' σR' kR ext hL' hR'
            t'_mid s₁L_mid s₁R_mid stL₁_mid stR₁_mid gMidL gMidR h_mid
          dsimp only
          have hPs_mid : P.sendsIn (({ sR.1 with g := gMidR, h := hR' }, sR.2).1.g.epoch P) = true := by
            simpa [gMidR, t'_mid] using hPs_next
          have ht_mid : ({ sR.1 with g := gMidR, h := hR' }, sR.2).1.g.epoch P = t := by
            simpa [gMidR, t'_mid] using ht'
          have hsafe_mid : ({ sR.1 with g := gMidR, h := hR' }, sR.2).1.g.safeCh (2 + Δcka) P = true := by
            simpa [gMidR, s₁R_mid, t'_mid, s₁_epR, s₁R, t', GameState.safeCh] using hsafe₁
          rcases h_mid.vSend_stay_chall cka prng hPs_mid ht_mid hsafe_mid m₀ m₁ r sL.1.g sR.1.g with
            ⟨c, sL', sR', hvL, hvR, hInv'⟩
          dsimp only [gMidL, gMidR, stL₁_mid, stR₁_mid, s₁L_mid, s₁R_mid, t'_mid,
            s₁_epL, s₁_epR, s₁L, s₁R, t', mL] at hvL hvR ⊢
          rw [hvL, hvR, pure_bind, pure_bind, pure_bind]
          exact ih (some c) sL' sR' (Or.inr hInv')
        · refine closeBy_of_det_step cka prng fs Δcka qep tL t b _ k
            sL ({ sL.1 with abort := true }, sL.2) sR ({ sR.1 with abort := true }, sR.2)
            none none ?_ ?_ ih (Or.inr ⟨rfl, Or.inl ⟨rfl, rfl, h.winFS, h.bFS⟩⟩)
          · rw [runEM_implE_challE _ _ _ _ _ _ _ P m₀ m₁ r sL h.abortL h.winL]
            simp only [hepL, hsafe_s₁, hsafe₁, hchallL,
              Bool.not_true, Bool.false_or, Bool.false_eq_true, ↓reduceIte, hdoom_eq, hdoom]
          · rw [runEM_implE_challE _ _ _ _ _ _ _ P m₀ m₁ r sR h.abortR h.winR]
            simp only [hepR, hsafe₁, hchallR,
              Bool.not_true, Bool.false_or, Bool.false_eq_true, ↓reduceIte, hdoom]

/-! ### Adversary coupling and main proof -/

theorem closeBy_evalEng (cka : CKAScheme KC Γ CCoins T I) (prng : PRFPRNG KR Sig I K)
    (fs : FSAEADScheme K SS RS (Header T) M E) (Δcka qep : ℕ) (tL : Option ℕ) (t : ℕ) (b : Bool)
    (hvalid : lastLeakGuessAdmissible (2 + Δcka) tL t = true)
    (oa : OracleComp (AdvSpec Γ T Sig SS RS M CCoins E) Bool)
    (sL : StateL Γ T Sig SS RS M E K I) (sR : StateR Γ T Sig K I SS RS M E)
    (hInv : Inv15 fs Δcka qep tL t b sL sR) :
    CloseByEng cka prng fs Δcka qep tL t b oa sL sR := by
  induction oa using OracleComp.inductionOn generalizing sL sR with
  | pure b' =>
    exact closeBy_evalEng_pure cka prng fs Δcka qep tL t b b' sL sR hInv
  | query_bind i t_oa ih =>
    rcases i with n | q_sm
    · exact closeBy_coinsE cka prng fs Δcka qep tL t b n t_oa sL sR hInv ih
    · rcases hInv with hAbort | hAct
      · exact closeBy_sm_of_abortInv cka prng fs Δcka qep tL t b q_sm t_oa sL sR hAbort ih
      · rcases q_sm with (((q_tr | q_ch) | ⟨P, c⟩) | ⟨P, c⟩) | q_corr
        · exact closeBy_transmitE cka prng fs Δcka qep tL t b hvalid q_tr t_oa sL sR hAct ih
        · exact closeBy_challE cka prng fs Δcka qep tL t b hvalid q_ch t_oa sL sR hAct ih
        · exact closeBy_deliverE cka prng fs Δcka qep tL t b P c t_oa sL sR hAct ih
        · exact closeBy_injectE cka prng fs Δcka qep tL t b P c t_oa sL sR hAct ih
        · exact closeBy_corrE cka prng fs Δcka qep tL t b q_corr t_oa sL sR hAct ih

theorem healEpoch_zero_false (tL : Option ℕ) :
    (tL.isSome && decide (0 = healEpoch tL)) = false := by
  cases tL <;> rfl

omit [DecidableEq T] [DecidableEq M] [DecidableEq E] [DecidableEq I] [Inhabited E]
  [SampleableType CCoins] [SampleableType I] [SampleableType K] in
theorem ActiveInv.init_mkParties
    {fs : FSAEADScheme K SS RS (Header T) M E} {Δcka qep : ℕ}
    {tL : Option ℕ} {t : ℕ} {b : Bool}
    (γA γB : Γ) (σL : Option Sig) (kL : K)
    (σR : Sig) (kR : K) (ext : Bool)
    (pgL : EagerState Sig I K)
    (hR : FSState T Sig K I SS RS E)
    (k_fs : K)
    (hext_iff : ext = true ↔ t = 0)
    (hk_ne : t ≠ 0 → kL = kR)
    (hroot : σL = if 0 < t ∧ ¬(tL.isSome && decide (0 < healEpoch tL)) then none else some σR)
    (hhR_cache : hR.cache = fun _ => none)
    (hhR_fields : hR.ext = none ∧ hR.fsCount = 0 ∧ hR.fsSCorr = false ∧ hR.fsTrans = [])
    (ht0 : t = 0 → kL = k_fs)
    (hbefore : 0 < t →
      pgL.1.b = true ∧
      pgL.1.corr = (tL.isSome && decide (0 < healEpoch tL)) ∧
      pgL.1.prng = false ∧
      pgL.1.prf = false ∧
      pgL.1.table = [] ∧
      σR = pgL.1.σ ∧
      hR.table = [] ∧
      hR.sessions = [] ∧
      pgL.2 = .ready k_fs) :
    let pL := mkParties (T := T) γA γB σL (fs.initSender kL) (fs.initReceiver kL)
    let gL : Ctx Γ T (Option Sig) SS RS M E :=
      { st := fun P => match P with | .A => pL.1 | .B => pL.2
        b := b }
    let pR := mkParties (T := T) γA γB σR (if ext then none else some (fs.initSender kR))
                (if ext then none else some (fs.initReceiver kR))
    let gR : Ctx Γ T Sig (Option SS) (Option RS) M E :=
      { st := fun P => match P with | .A => pR.1 | .B => pR.2
        b := false }
    let osR : FSAEAD.State SS RS (Header T) M E := FSAEAD.initState fs k_fs b
    ActiveInv fs Δcka qep tL t b
      ({ g := gL, h := {} }, pgL)
      ({ g := gR, h := hR }, osR) := by
  intro pL gL pR gR osR
  have hext_false : ∀ hne : t ≠ 0, ext = false := by
    intro hne
    cases he : ext
    · rfl
    · exact absurd (hext_iff.mp he) hne
  refine
    { abortL := rfl
      abortR := rfl
      winL := rfl
      winR := rfl
      winFS := rfl
      bL := rfl
      bR := rfl
      bFS := rfl
      epoch_eq := rfl
      idx_eq := rfl
      tL_eq := rfl
      chall_eq := rfl
      comp_eq := rfl
      maxAcc_eq := rfl
      leaks_eq := rfl
      corrs_eq := rfl
      trans_eq := rfl
      idL := fun P => by cases P <;> rfl
      idR := fun P => by cases P <;> rfl
      tcurL := fun P => by cases P <;> rfl
      tcurR := fun P => by cases P <;> rfl
      γ_eq := fun P => by cases P <;> rfl
      Tcur_eq := fun P => by cases P <;> rfl
      root_eq := fun P => by cases P <;> exact hroot
      vS_eq := fun P => by
        cases P with
        | A => rfl
        | B =>
          dsimp only [gL, gR, pL, pR, mkParties, curSS, osR, FSAEAD.initState]
          rw [hhR_fields.1]
          rcases eq_or_ne t 0 with rfl | hne
          · simp [hext_iff.mpr rfl, ht0 rfl]
          · simp [hext_false hne, hk_ne hne]
      vR_eq := fun P t' => by
        cases P with
        | A =>
          dsimp only [gL, gR, pL, pR, mkParties, curRS, osR, FSAEAD.initState]
          rw [hhR_fields.1]
          rcases eq_or_ne t' 0 with rfl | ht'
          · rcases eq_or_ne t 0 with rfl | hne
            · simp [hext_iff.mpr rfl, ht0 rfl]
            · simp [hext_false hne, hk_ne hne]
          · simp [ht']
        | B => rfl
      sender_epoch := rfl
      receiver_epoch := Or.inl rfl
      maxEp_le_qep := Nat.zero_le qep
      tL_le_maxEp := fun _ h => by nomatch h
      vS_none := fun P hvS => by
        cases P with
        | A => nomatch hvS
        | B =>
          dsimp only [gR, pR, mkParties] at hvS ⊢
          rcases eq_or_ne t 0 with rfl | hne
          · exact ⟨rfl, le_rfl⟩
          · rw [hext_false hne] at hvS
            nomatch hvS
      vS_sending := fun P hPs => by
        cases P with
        | A => nomatch hPs
        | B =>
          dsimp only [gR, pR, mkParties]
          refine ⟨fun ht => by simp [hext_iff.mpr ht.symm], fun hne => ?_⟩
          exact ⟨fs.initSender kR, by simp [hext_false hne.symm]⟩
      vR_sender := by
        rcases eq_or_ne t 0 with rfl | hne
        · rfl
        · cases Party.senderOf t <;> simp [gR, pR, mkParties, hne]
      vR_receiver := by
        rcases eq_or_ne t 0 with rfl | hne
        · change (gR.st .A).vR 0 = some none
          dsimp only [gR, pR, mkParties]
          simp [hext_iff.mpr rfl]
        · have hnot_le : ¬(t ≤ gR.epoch (Party.receiverOf t)) := by
            change ¬(t ≤ 0); omega
          cases Party.receiverOf t <;> simp [gR, pR, mkParties, hnot_le, hne]
      vR_other := fun P t' x hne hv => by
        cases P with
        | A =>
          dsimp only [gR, pR, mkParties] at hv
          rcases eq_or_ne t' 0 with rfl | ht'
          · simp only [↓reduceIte, hext_false hne.symm, Bool.false_eq_true, Option.some.injEq] at hv
            subst hv
            exact ⟨rfl, rfl, le_rfl⟩
          · simp only [ht', ↓reduceIte] at hv
            nomatch hv
        | B => nomatch hv
      cache_none := fun t' _ => ⟨rfl, congrFun hhR_cache t'⟩
      cache_other := fun _ _ => by simp [hhR_cache]
      cache_other_ext := fun _ _ _ _ _ _ hc => by rw [hhR_cache] at hc; nomatch hc
      cache_t_none := fun _ => rfl
      cache_t := fun _ _ _ _ hc => by rw [hhR_cache] at hc; nomatch hc
      trans_wf := fun _ h => by nomatch h
      chall_wf := fun _ h => by nomatch h
      comp_t := fun _ h => by nomatch h
      before_t := fun hlt => by
        rcases hbefore hlt with
          ⟨hb, hcorr, hprng, hprf, htabL, hσ, htabR, hsessR, hsl⟩
        refine ⟨hb, hcorr, hprng, hprf, htabL, fun P _ => ?_, fun _ _ _ _ hc => ?_,
          htabR, hsessR, hhR_fields.2.2.2, hhR_fields.2.1, hhR_fields.2.2.1,
          hhR_fields.1, k_fs, hsl, rfl⟩
        · cases P <;> exact hσ
        · rw [hhR_cache] at hc; nomatch hc
      ext_some := fun hs => by rw [hhR_fields.1] at hs; nomatch hs
      ext_none := fun _ =>
        ⟨rfl, hhR_fields.2.1, hhR_fields.2.2.1, fun _ => rfl, hhR_fields.2.2.2,
          rfl, rfl, fun _ h => (by cases h), fun _ h => (by cases h),
          ⟨fun h => (by cases h), fun _ h => (by cases h)⟩⟩ }

def initPRNGBody (cka : CKAScheme KC Γ CCoins T I) (prng : PRFPRNG KR Sig I K)
    (fs : FSAEADScheme K SS RS (Header T) M E) (lam : I) (mo : Mode) (kc : KC) :
    HM (PRFPRNG.spec Sig I K) (PRNGState T Sig K)
      (Option (PartyState Γ T (Option Sig) SS RS × PartyState Γ T (Option Sig) SS RS)) := do
  match ← rootPRNG prng mo 0 lam none with
  | none => return none
  | some (σ, k) =>
    return some (mkParties (T := T) (cka.initA kc) (cka.initB kc) σ
      (fs.initSender k) (fs.initReceiver k))

def initFSBody (cka : CKAScheme KC Γ CCoins T I) (prng : PRFPRNG KR Sig I K)
    (fs : FSAEADScheme K SS RS (Header T) M E) (lam : I) (mo : Mode) (j : ℕ)
    (kr : KR) (kc : KC) :
    HM (FSAEAD.spec SS RS (Header T) M E) (FSState T Sig K I SS RS E)
      (Option (PartyState Γ T Sig (Option SS) (Option RS) ×
        PartyState Γ T Sig (Option SS) (Option RS))) := do
  let (σ, k, sid) ← rootFS prng mo 0 lam (prng.init kr)
  let ext ← extOf j sid
  return some (mkParties (T := T) (cka.initA kc) (cka.initB kc) σ
    (if ext then none else some (fs.initSender k))
    (if ext then none else some (fs.initReceiver k)))

omit [DecidableEq T] [DecidableEq M] [DecidableEq E] [Inhabited E] [SampleableType CCoins] in
theorem runHM_initPRNG_eq [SampleableType KC]
    (cka : CKAScheme KC Γ CCoins T I) (prng : PRFPRNG KR Sig I K)
    (fs : FSAEADScheme K SS RS (Header T) M E) (lam : I) (mo : Mode)
    (hL : PRNGState T Sig K) (pgL : EagerState Sig I K) :
    runHM (eagerOracleImpl prng) (initPRNG cka prng fs lam mo) hL pgL =
      ($ᵗ KC : ProbComp KC) >>= fun kc =>
        runHM (eagerOracleImpl prng) (initPRNGBody cka prng fs lam mo kc) hL pgL := by
  simp [initPRNG, initPRNGBody, runHM, StateT.run_bind, simulateQ_bind,
    simulateQ_outerFull_sampleT, bind_map_left]
  refine bind_congr fun kc => bind_congr fun p => ?_
  rcases p with ⟨⟨_ | ⟨σ, k⟩, _⟩, _⟩ <;> rfl

omit [Inhabited E] [SampleableType CCoins] in
theorem runHM_initFS_eq [SampleableType KR] [SampleableType KC]
    (cka : CKAScheme KC Γ CCoins T I) (prng : PRFPRNG KR Sig I K)
    (fs : FSAEADScheme K SS RS (Header T) M E) (lam : I) (mo : Mode) (j : ℕ)
    (hR : FSState T Sig K I SS RS E) (osR : FSAEAD.State SS RS (Header T) M E) :
    runHM (FSAEAD.oracleImpl fs) (initFS cka prng fs lam mo j) hR osR =
      ($ᵗ KR : ProbComp KR) >>= fun kr =>
        ($ᵗ KC : ProbComp KC) >>= fun kc =>
          runHM (FSAEAD.oracleImpl fs) (initFSBody cka prng fs lam mo j kr kc) hR osR := by
  simp [initFS, initFSBody, runHM, StateT.run_bind, simulateQ_bind,
    simulateQ_outerFull_sampleT, bind_map_left]

theorem simulateQ_redPRNGPriv [SampleableType KC]
    (cka : CKAScheme KC Γ CCoins T I) (prng : PRFPRNG KR Sig I K)
    (fs : FSAEADScheme K SS RS (Header T) M E) (lam : I) (Δcka qep : ℕ)
    (tL : Option ℕ) (t : ℕ) (A : SchemeAdversary Γ T Sig SS RS M CCoins E)
    (os₀ : EagerState Sig I K) :
    (simulateQ (outerFull (eagerOracleImpl prng))
      (redPRNGPriv cka prng fs lam Δcka qep tL t A)).run' os₀ =
    (do
      let b ← ($ᵗ Bool : ProbComp Bool)
      let r ← runHM (eagerOracleImpl prng) (initPRNG cka prng fs lam ⟨false, tL, t⟩)
        ({} : PRNGState T Sig K) os₀
      evalAfterInitL (eagerOracleImpl prng) (hooksPRNG cka prng fs ⟨false, tL, t⟩)
        (2 + Δcka) qep fs.maxSkip (Config.priv t) ⟨false, tL, t⟩ b A r) := by
  change Prod.fst <$> (simulateQ (outerFull (eagerOracleImpl prng)) _).run os₀ = _
  unfold redPRNGPriv runPRNG Mode.cfg Mode.policy
  simp only [engRun, simulateQ_bind, StateT.run_bind, bind_assoc,
    simulateQ_outerFull_sampleT, bind_map_left, map_bind, runHM, Bool.false_eq_true, ↓reduceIte]
  refine bind_congr fun b => bind_congr fun ⟨⟨vs, h⟩, os₁⟩ => ?_
  cases vs with
  | none =>
    simp [evalAfterInitL, simulateQ_outerFull_sampleT]
  | some vAvB =>
    rcases vAvB with ⟨vA, vB⟩
    simp only [evalAfterInitL, evalEng, runEM, simulateQ_bind, StateT.run_bind, bind_assoc,
      simulateQ_pure, StateT.run_pure, pure_bind, bind_map_left, simulateQ_outerFull_privOut]
    rfl

theorem evalDist_game_redFSPriv [SampleableType KR] [SampleableType KC]
    (cka : CKAScheme KC Γ CCoins T I) (prng : PRFPRNG KR Sig I K)
    (fs : FSAEADScheme K SS RS (Header T) M E) (lam : I) (Δcka qep : ℕ)
    (tL : Option ℕ) (t : ℕ) (A : SchemeAdversary Γ T Sig SS RS M CCoins E) :
    𝒟[FSAEAD.game fs (redFSPriv cka prng fs lam Δcka qep tL t A)] =
    𝒟[do
      let b ← ($ᵗ Bool : ProbComp Bool)
      let k ← ($ᵗ K : ProbComp K)
      let r ← runHM (FSAEAD.oracleImpl fs) (initFS cka prng fs lam ⟨false, tL, t⟩ 0)
        ({} : FSState T Sig K I SS RS E) (FSAEAD.initState fs k b)
      evalAfterInitM fs (hooksFS cka prng fs Δcka ⟨false, tL, t⟩ 0)
        (2 + Δcka) qep fs.maxSkip (Config.priv t) ⟨false, tL, t⟩ b false A r] := by
  refine DEq.evalDist_eq ?_
  unfold FSAEAD.game redFSPriv runFS Mode.cfg Mode.policy
  refine DEq.bind_right _ fun b => DEq.bind_right _ fun k => ?_
  simp only [engRun, simulateQ_bind, StateT.run_bind, bind_assoc, runHM, outerFull,
    Bool.false_eq_true, ↓reduceIte]
  refine DEq.bind_right _ fun ⟨⟨vs, h⟩, st₁⟩ => ?_
  cases vs with
  | none =>
    simp only [evalAfterInitM, simulateQ_pure, StateT.run_pure, pure_bind]
    exact DEq.of_evalDist_eq (evalDist_coin_or_win fs b st₁)
  | some vAvB =>
    rcases vAvB with ⟨vA, vB⟩
    simp only [evalAfterInitM, evalEngM, runEM, outerFull, simulateQ_bind, StateT.run_bind,
      bind_assoc, simulateQ_pure, StateT.run_pure, pure_bind, bind_map_left]
    refine DEq.bind_right _ fun ⟨⟨b', es⟩, st₂⟩ => ?_
    exact DEq.of_evalDist_eq (evalDist_fsPrivOut_step fs (2 + Δcka) ⟨false, tL, t⟩ b b' es st₂)

theorem advantage_redFSPrivCoin [SampleableType KR] [SampleableType KC]
    (cka : CKAScheme KC Γ CCoins T I) (prng : PRFPRNG KR Sig I K)
    (fs : FSAEADScheme K SS RS (Header T) M E) (lam : I) (Δcka qep : ℕ)
    (tL : Option ℕ) (t : ℕ) (A : SchemeAdversary Γ T Sig SS RS M CCoins E) :
    FSAEAD.advantage fs (redFSPrivCoin cka prng fs lam Δcka qep tL t A) =
    𝒟[do
      let b ← ($ᵗ Bool : ProbComp Bool)
      let k ← ($ᵗ K : ProbComp K)
      let r ← runHM (FSAEAD.oracleImpl fs) (initFS cka prng fs lam ⟨false, tL, t⟩ 0)
        ({} : FSState T Sig K I SS RS E) (FSAEAD.initState fs k b)
      evalAfterInitCoin fs (hooksFS cka prng fs Δcka ⟨false, tL, t⟩ 0)
        (2 + Δcka) qep fs.maxSkip (Config.priv t) ⟨false, tL, t⟩ false A r] {true} := by
  unfold redFSPrivCoin runFS Mode.cfg Mode.policy
  rw [advantage_bind_sampleT_bool]
  congr 1
  refine DEq.evalDist_eq ?_
  refine DEq.bind_right _ fun b => DEq.bind_right _ fun k => ?_
  simp only [engRun, simulateQ_bind, StateT.run_bind, bind_assoc, runHM, outerFull,
    Bool.false_eq_true, ↓reduceIte]
  refine DEq.bind_right _ fun ⟨⟨vs, h⟩, st₁⟩ => ?_
  cases vs with
  | none =>
    simp only [evalAfterInitCoin, simulateQ_pure, StateT.run_pure, pure_bind]
    exact DEq.refl _
  | some vAvB =>
    rcases vAvB with ⟨vA, vB⟩
    simp only [evalAfterInitCoin, evalEngL, runEM, outerFull, simulateQ_bind, StateT.run_bind,
      bind_assoc, simulateQ_pure, StateT.run_pure, pure_bind, bind_map_left]
    exact DEq.refl _

theorem closeBy_init_after_keys (cka : CKAScheme KC Γ CCoins T I) (prng : PRFPRNG KR Sig I K)
    (fs : FSAEADScheme K SS RS (Header T) M E) (lam : I) (Δcka qep : ℕ) (tL : Option ℕ) (t : ℕ)
    (A : SchemeAdversary Γ T Sig SS RS M CCoins E)
    (hvalid : lastLeakGuessAdmissible (2 + Δcka) tL t = true)
    (b : Bool) (k_fs : K) (kr : KR) (kc : KC) :
    let σ₀ := prng.init kr
    let sL₀ : EagerState Sig I K := ({ σ := σ₀, b := true }, .ready k_fs)
    let sR₀ : FSAEAD.State SS RS (Header T) M E := FSAEAD.initState fs k_fs b
    CloseBy
      (runHM (eagerOracleImpl prng) (initPRNGBody cka prng fs lam ⟨false, tL, t⟩ kc)
        ({} : PRNGState T Sig K) sL₀ >>=
        evalAfterInitL (eagerOracleImpl prng) (hooksPRNG cka prng fs ⟨false, tL, t⟩)
          (2 + Δcka) qep fs.maxSkip (Config.priv t) ⟨false, tL, t⟩ b A)
      (runHM (FSAEAD.oracleImpl fs) (initFSBody cka prng fs lam ⟨false, tL, t⟩ 0 kr kc)
        ({} : FSState T Sig K I SS RS E) sR₀ >>=
        evalAfterInitM fs (hooksFS cka prng fs Δcka ⟨false, tL, t⟩ 0)
          (2 + Δcka) qep fs.maxSkip (Config.priv t) ⟨false, tL, t⟩ b false A)
      (runHM (FSAEAD.oracleImpl fs) (initFSBody cka prng fs lam ⟨false, tL, t⟩ 0 kr kc)
        ({} : FSState T Sig K I SS RS E) sR₀ >>=
        evalAfterInitCoin fs (hooksFS cka prng fs Δcka ⟨false, tL, t⟩ 0)
          (2 + Δcka) qep fs.maxSkip (Config.priv t) ⟨false, tL, t⟩ false A) := by
  intro σ₀ sL₀ sR₀
  have hheal0 : (tL.isSome && decide (0 = healEpoch tL)) = false := healEpoch_zero_false tL
  rcases Nat.eq_zero_or_pos t with rfl | ht
  · set p := prng.up σ₀ lam
    have hL_eval :
        runHM (eagerOracleImpl prng) (initPRNGBody cka prng fs lam ⟨false, tL, 0⟩ kc)
          ({} : PRNGState T Sig K) sL₀ =
        pure ((some (mkParties (T := T) (cka.initA kc) (cka.initB kc) (some p.1)
                (fs.initSender k_fs) (fs.initReceiver k_fs)), ({} : PRNGState T Sig K)),
          ({ ({ σ := σ₀, b := true } : PRFPRNG.GameState Sig I K) with
              prf := true, table := [(lam, k_fs)] }, .done)) := by
      simp only [initPRNGBody, rootPRNG, decide_mode_tH_eq, lt_self_iff_false, ↓reduceIte,
        hheal0, Bool.false_eq_true]
      simp [runHM, liftP, PRFPRNG.challPrfQuery, outerFull, eagerOracleImpl, eagerChallPrf,
        liftPG, drawKey, consumeKey, sL₀, p]
    have hR_eval :
        runHM (FSAEAD.oracleImpl fs) (initFSBody cka prng fs lam ⟨false, tL, 0⟩ 0 kr kc)
          ({} : FSState T Sig K I SS RS E) sR₀ =
        (($ᵗ K : ProbComp K) >>= fun k =>
          pure ((some (mkParties (T := T) (cka.initA kc) (cka.initB kc) p.1
                  (if true then none else some (fs.initSender k))
                  (if true then none else some (fs.initReceiver k))),
            { ({} : FSState T Sig K I SS RS E) with table := [(lam, k)], sessions := [lam] }), sR₀)) := by
      simp only [initFSBody, rootFS, extOf, isExt, decide_mode_tH_eq, lt_self_iff_false, ↓reduceIte,
        hheal0, Bool.false_eq_true]
      simp [runHM, lookupF, StateT.run_bind, simulateQ_outerFull_sampleT, bind_map_left, σ₀, p]
    rw [hL_eval, hR_eval, pure_bind, bind_assoc, bind_assoc]
    refine closeBy_bind_right_const fun k => ?_
    simp only [pure_bind, evalAfterInitL, evalAfterInitM, evalAfterInitCoin]
    exact closeBy_evalEng cka prng fs Δcka qep tL 0 b hvalid A _ _
      (Or.inr (ActiveInv.init_mkParties (cka.initA kc) (cka.initB kc) (some p.1) k_fs
        p.1 k true
        ({ ({ σ := σ₀, b := true } : PRFPRNG.GameState Sig I K) with
            prf := true, table := [(lam, k_fs)] }, .done)
        { ({} : FSState T Sig K I SS RS E) with table := [(lam, k)], sessions := [lam] }
        k_fs
        (by simp) (fun hne => absurd rfl hne) (by simp)
        rfl ⟨rfl, rfl, rfl, rfl⟩ (fun _ => rfl)
        (fun hlt => absurd hlt (Nat.lt_irrefl 0))))
  · have hnot_gt : ¬(t < 0) := by omega
    have hne_t : 0 ≠ t := by omega
    set p := prng.up σ₀ lam
    cases hcorr : tL.isSome && decide (0 < healEpoch tL)
    · have hL_eval :
          runHM (eagerOracleImpl prng) (initPRNGBody cka prng fs lam ⟨false, tL, t⟩ kc)
            ({} : PRNGState T Sig K) sL₀ =
          pure ((some (mkParties (T := T) (cka.initA kc) (cka.initB kc) none
                  (fs.initSender p.2) (fs.initReceiver p.2)), ({} : PRNGState T Sig K)),
            ({ ({ σ := σ₀, b := true } : PRFPRNG.GameState Sig I K) with
                σ := p.1, corr := false }, .ready k_fs)) := by
        simp only [initPRNGBody, rootPRNG, decide_mode_tH_eq, decide_mode_tH_lt, hnot_gt, hne_t,
          hheal0, hcorr, Bool.false_eq_true, ↓reduceIte]
        simp [runHM, liftP, PRFPRNG.processQuery, PRFPRNG.processImpl, PRFPRNG.samIfNec,
          outerFull, eagerOracleImpl, eagerProcess, liftPG, sL₀, p]
      have hR_eval :
          runHM (FSAEAD.oracleImpl fs) (initFSBody cka prng fs lam ⟨false, tL, t⟩ 0 kr kc)
            ({} : FSState T Sig K I SS RS E) sR₀ =
          pure ((some (mkParties (T := T) (cka.initA kc) (cka.initB kc) p.1
                  (if false then none else some (fs.initSender p.2))
                  (if false then none else some (fs.initReceiver p.2))), ({} : FSState T Sig K I SS RS E)), sR₀) := by
        simp only [initFSBody, rootFS, extOf, decide_mode_tH_eq, hnot_gt, hne_t,
          hheal0, Bool.false_eq_true, ↓reduceIte]
        simp [runHM, σ₀, p]
      rw [hL_eval, hR_eval, pure_bind, pure_bind, pure_bind]
      dsimp only [evalAfterInitL, evalAfterInitM, evalAfterInitCoin]
      exact closeBy_evalEng cka prng fs Δcka qep tL t b hvalid A _ _
        (Or.inr (ActiveInv.init_mkParties (cka.initA kc) (cka.initB kc) none p.2
          p.1 p.2 false
          ({ ({ σ := σ₀, b := true } : PRFPRNG.GameState Sig I K) with
              σ := p.1, corr := false }, .ready k_fs)
          {} k_fs
          (by simp [hne_t.symm]) (fun _ => rfl)
          (by simp only [ht, hcorr, Bool.false_eq_true, not_false_eq_true, and_self, ↓reduceIte])
          rfl ⟨rfl, rfl, rfl, rfl⟩
          (fun ht0 => absurd ht0 hne_t.symm)
          (fun _ => ⟨rfl, hcorr.symm, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩)))
    · have hL_eval :
          runHM (eagerOracleImpl prng) (initPRNGBody cka prng fs lam ⟨false, tL, t⟩ kc)
            ({} : PRNGState T Sig K) sL₀ =
          pure ((some (mkParties (T := T) (cka.initA kc) (cka.initB kc) (some p.1)
                  (fs.initSender p.2) (fs.initReceiver p.2)), ({} : PRNGState T Sig K)),
            ({ ({ σ := σ₀, b := true } : PRFPRNG.GameState Sig I K) with
                σ := p.1, corr := true }, .ready k_fs)) := by
        simp only [initPRNGBody, rootPRNG, processCorr, decide_mode_tH_eq, decide_mode_tH_lt,
          hnot_gt, hne_t, hheal0, hcorr, Bool.false_eq_true, ↓reduceIte]
        simp [runHM, liftP, PRFPRNG.processQuery, PRFPRNG.corrQuery,
          PRFPRNG.processImpl, PRFPRNG.corrImpl, PRFPRNG.samIfNec,
          outerFull, eagerOracleImpl, eagerProcess, eagerCorr, liftPG, sL₀, p]
      have hR_eval :
          runHM (FSAEAD.oracleImpl fs) (initFSBody cka prng fs lam ⟨false, tL, t⟩ 0 kr kc)
            ({} : FSState T Sig K I SS RS E) sR₀ =
          pure ((some (mkParties (T := T) (cka.initA kc) (cka.initB kc) p.1
                  (if false then none else some (fs.initSender p.2))
                  (if false then none else some (fs.initReceiver p.2))), ({} : FSState T Sig K I SS RS E)), sR₀) := by
        simp only [initFSBody, rootFS, extOf, decide_mode_tH_eq, hnot_gt, hne_t,
          hheal0, Bool.false_eq_true, ↓reduceIte]
        simp [runHM, σ₀, p]
      rw [hL_eval, hR_eval, pure_bind, pure_bind, pure_bind]
      dsimp only [evalAfterInitL, evalAfterInitM, evalAfterInitCoin]
      exact closeBy_evalEng cka prng fs Δcka qep tL t b hvalid A _ _
        (Or.inr (ActiveInv.init_mkParties (cka.initA kc) (cka.initB kc) (some p.1) p.2
          p.1 p.2 false
          ({ ({ σ := σ₀, b := true } : PRFPRNG.GameState Sig I K) with
              σ := p.1, corr := true }, .ready k_fs)
          {} k_fs
          (by simp [hne_t.symm]) (fun _ => rfl)
          (by simp only [ht, hcorr, not_true_eq_false, and_false, ↓reduceIte])
          rfl ⟨rfl, rfl, rfl, rfl⟩
          (fun ht0 => absurd ht0 hne_t.symm)
          (fun _ => ⟨rfl, hcorr.symm, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩)))

omit [DecidableEq T] [DecidableEq M] [DecidableEq E] [DecidableEq I] [Inhabited E]
  [SampleableType CCoins] [SampleableType I] in
theorem evalDist_swap_three [SampleableType KR]
    (f : KR → K → Bool → ProbComp Bool) :
    𝒟[do
      let kr ← $ᵗ KR
      let k_fs ← $ᵗ K
      let b ← $ᵗ Bool
      f kr k_fs b] =
    𝒟[do
      let b ← $ᵗ Bool
      let k_fs ← $ᵗ K
      let kr ← $ᵗ KR
      f kr k_fs b] := by
  refine DEq.evalDist_eq ?_
  refine (DEq.bind_right ($ᵗ KR) fun kr =>
    DEq.swap ($ᵗ K) ($ᵗ Bool) (fun k_fs b => f kr k_fs b)).trans ?_
  refine (DEq.swap ($ᵗ KR) ($ᵗ Bool) (fun kr b => do let k_fs ← $ᵗ K; f kr k_fs b)).trans ?_
  exact DEq.bind_right ($ᵗ Bool) fun b =>
    DEq.swap ($ᵗ KR) ($ᵗ K) (fun kr k_fs => f kr k_fs b)

variable [SampleableType KR] [SampleableType KC]
  (cka : CKAScheme KC Γ CCoins T I) (prng : PRFPRNG KR Sig I K)
  (fs : FSAEADScheme K SS RS (Header T) M E) (lam : I) (Δcka qep : ℕ) in
/-- Lemma 15: ideal PRF-PRNG privacy bias bounded by `redFSPriv` plus twice `redFSPrivCoin`. -/
theorem lemma15_proof (tL : Option ℕ) (t : ℕ) (A : SchemeAdversary Γ T Sig SS RS M CCoins E) :
    𝒟[PRFPRNG.branch prng true (redPRNGPriv cka prng fs lam Δcka qep tL t A)].boolBias ≤
      FSAEAD.advantage fs (redFSPriv cka prng fs lam Δcka qep tL t A)
        + 2 * FSAEAD.advantage fs (redFSPrivCoin cka prng fs lam Δcka qep tL t A) := by
  cases hvalid : lastLeakGuessAdmissible (2 + Δcka) tL t
  · have hdeq :
        DEq
          (do
            let kr ← $ᵗ KR
            let k_fs ← $ᵗ K
            (simulateQ (outerFull (eagerOracleImpl prng))
              (redPRNGPriv cka prng fs lam Δcka qep tL t A)).run'
              ({ σ := prng.init kr, b := true }, .ready k_fs))
          ($ᵗ Bool : ProbComp Bool) := by
      refine (DEq.bind_right ($ᵗ KR) fun kr => ?_).trans (DEq.bind_const ($ᵗ KR) _)
      refine (DEq.bind_right ($ᵗ K) fun k_fs => ?_).trans (DEq.bind_const ($ᵗ K) _)
      rw [simulateQ_redPRNGPriv]
      refine (DEq.bind_right ($ᵗ Bool) fun b => ?_).trans (DEq.bind_const ($ᵗ Bool) _)
      refine (DEq.bind_right _ fun ⟨⟨vs, h⟩, os₁⟩ => ?_).trans (DEq.bind_const _ _)
      cases vs with
      | none => exact DEq.refl _
      | some vAvB =>
        rcases vAvB with ⟨vA, vB⟩
        exact DEq.of_evalDist_eq
          (evalEng_invalid (eagerOracleImpl prng) (hooksPRNG cka prng fs ⟨false, tL, t⟩)
            (2 + Δcka) qep fs.maxSkip (Config.priv t) ⟨false, tL, t⟩ b hvalid A _)
    rw [branch_true_eq_eager, hdeq.evalDist_eq, boolBias_uniformBool]
    exact zero_le
  · refine (boolBias_le_add_two_mul_boolDist
      𝒟[PRFPRNG.branch prng true (redPRNGPriv cka prng fs lam Δcka qep tL t A)]
      𝒟[FSAEAD.game fs (redFSPriv cka prng fs lam Δcka qep tL t A)]).trans ?_
    have hdist :
        𝒟[PRFPRNG.branch prng true (redPRNGPriv cka prng fs lam Δcka qep tL t A)].boolDist
          𝒟[FSAEAD.game fs (redFSPriv cka prng fs lam Δcka qep tL t A)] ≤
        FSAEAD.advantage fs (redFSPrivCoin cka prng fs lam Δcka qep tL t A) := by
      rw [branch_true_eq_eager]
      simp only [simulateQ_redPRNGPriv]
      rw [evalDist_swap_three, evalDist_game_redFSPriv, advantage_redFSPrivCoin]
      refine boolDist_le_of_closeBy ?_
      refine closeBy_bind ($ᵗ Bool) fun b => ?_
      refine closeBy_bind ($ᵗ K) fun k_fs => ?_
      simp only [runHM_initPRNG_eq, runHM_initFS_eq, bind_assoc]
      refine closeBy_bind ($ᵗ KR) fun kr => ?_
      refine closeBy_bind ($ᵗ KC) fun kc => ?_
      exact closeBy_init_after_keys cka prng fs lam Δcka qep tL t A hvalid b k_fs kr kc
    rw [two_mul, two_mul]
    exact add_le_add le_rfl (add_le_add hdist hdist)

end Invariant

end CryptoGames.SM.Construction.PrivL15
