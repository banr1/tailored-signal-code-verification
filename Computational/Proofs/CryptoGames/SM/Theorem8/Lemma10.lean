/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Computational.Proofs.CryptoGames.SM.Theorem8.Lemma10Aux
import VCVio.OracleComp.EvalDist.Measure

/-!
# Proof of Lemma 10 (Theorem 8, Hop H1 → H2)

**Checked by Lean.** Proves ACD19 §5.3.2 Lemma 10 (`lemma10_proof`), bounding the ideal CKA branch
of `redCKAAuth` by the real PRF-PRNG branch of `redPRNGAuth`.
-/

@[expose] public section

open OracleComp OracleSpec ENNReal

namespace CryptoGames.SM.Construction.AuthL10

open Engine

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

variable {KC Γ CCoins T I : Type} {KR Sig K : Type} {SS RS M E : Type}
  [DecidableEq T] [DecidableEq M] [DecidableEq E] [DecidableEq I] [Inhabited E]
  [SampleableType KR] [SampleableType KC] [SampleableType CCoins] [SampleableType I]
  [SampleableType K]

variable (cka : CKAScheme KC Γ CCoins T I) (prng : PRFPRNG KR Sig I K)
  (fs : FSAEADScheme K SS RS (Header T) M E) (lam : I) (Δcka qep : ℕ)

theorem runL_le_runR (mo : Mode) (hauth : mo.auth = true)
    (hvalid : SM.lastLeakGuessAdmissible (2 + Δcka) mo.tL mo.tStar = true)
    (oa : SMComp Γ T Sig SS RS M CCoins E Bool)
    {esC : EStateC Γ T Sig SS RS M E I} {sc : CKA.GameState Γ T}
    {esP : EStateP Γ T Sig SS RS M E K} {sp : PRFPRNG.GameState Sig I K}
    (hS : Sync prng Δcka mo esC sc esP sp) :
    𝒟[runL cka prng fs Δcka qep mo oa esC sc] {true} ≤
      𝒟[runR cka prng fs Δcka qep mo oa esP sp] {true} := by
  induction oa using OracleComp.inductionOn generalizing esC sc esP sp with
  | pure b' =>
    rw [runL_pure, runR_pure, hS.authOut_eq]
  | query_bind q k ih =>
    rw [runL_query_bind, runR_query_bind]
    rcases q with n | ((((⟨P, m_msg, r⟩ | q_ch) | ⟨P, c⟩) | q_inj) | P)
    · exact step_coinsE_le cka prng fs Δcka qep mo n
        (fun u => runL cka prng fs Δcka qep mo (k u))
        (fun u => runR cka prng fs Δcka qep mo (k u)) hS @ih
    · exact step_transmitE_le cka prng fs Δcka qep mo hvalid P m_msg r
        (fun u => runL cka prng fs Δcka qep mo (k u))
        (fun u => runR cka prng fs Δcka qep mo (k u))
        (fun rhs hab => runL_abort_apply_true_le cka prng fs Δcka qep mo (k none) hab rhs) hS @ih
    · exact step_challE_le cka prng fs Δcka qep mo hauth q_ch
        (fun u => runL cka prng fs Δcka qep mo (k u))
        (fun u => runR cka prng fs Δcka qep mo (k u)) hS @ih
    · exact step_deliverE_le cka prng fs Δcka qep mo hauth P c
        (fun u => runL cka prng fs Δcka qep mo (k u))
        (fun u => runR cka prng fs Δcka qep mo (k u)) hS @ih
    · exact step_injectE_le cka prng fs Δcka qep mo hauth q_inj
        (fun u => runL cka prng fs Δcka qep mo (k u))
        (fun u => runR cka prng fs Δcka qep mo (k u))
        (fun rhs hab => runL_abort_apply_true_le cka prng fs Δcka qep mo (k none) hab rhs) hS @ih
    · exact step_corrE_le cka prng fs Δcka qep mo hauth P
        (fun u => runL cka prng fs Δcka qep mo (k u))
        (fun u => runR cka prng fs Δcka qep mo (k u))
        (fun rhs hab => runL_abort_apply_true_le cka prng fs Δcka qep mo (k none) hab rhs) hS @ih

theorem validGuess_some_pos {Δ l t : ℕ}
    (h : SM.lastLeakGuessAdmissible (2 + Δ) (some l) t = true) : 0 < t := by
  simp only [SM.lastLeakGuessAdmissible, SM.healedBy, decide_eq_true_eq] at h
  omega

@[simp]
theorem simulateQ_sampleT_run {ι : Type} {tspec : OracleSpec.{0, 0} ι} {S α : Type}
    [SampleableType α] (impl : QueryImpl tspec (StateT S ProbComp)) (st : S) :
    (simulateQ ((QueryImpl.ofLift unifSpec ProbComp).liftTarget (StateT S ProbComp) + impl)
      (sampleT α)).run st =
    (($ᵗ α : ProbComp α) >>= fun a => pure (a, st)) := by
  unfold sampleT
  rw [simulateQ_liftM_unif]
  rfl

@[simp]
theorem simulateQ_sampleT_run_id {ι : Type} {tspec : OracleSpec.{0, 0} ι} {S α : Type}
    [SampleableType α] (impl : QueryImpl tspec (StateT S ProbComp)) (st : S) :
    (simulateQ ((QueryImpl.id' unifSpec).liftTarget (StateT S ProbComp) + impl)
      (sampleT α)).run st =
    (($ᵗ α : ProbComp α) >>= fun a => pure (a, st)) :=
  simulateQ_sampleT_run impl st

def initES_C (tL : Option ℕ) (kr : KR) (kc : KC) : EStateC Γ T Sig SS RS M E I :=
  let out := prng.up (prng.init kr) lam
  let γA := match tL with | none => some (cka.initA kc) | some _ => none
  let γB := match tL with | none => some (cka.initB kc) | some _ => none
  let vp := mkParties (T := T) γA γB out.1 (fs.initSender out.2) (fs.initReceiver out.2)
  { g := { st := fun P => match P with | .A => vp.1 | .B => vp.2, b := false }, h := {} }

def initES_P (σv : Option Sig) (kr : KR) (kc : KC) : EStateP Γ T Sig SS RS M E K :=
  let out := prng.up (prng.init kr) lam
  let vp := mkParties (T := T) (cka.initA kc) (cka.initB kc) σv
    (fs.initSender out.2) (fs.initReceiver out.2)
  { g := { st := fun P => match P with | .A => vp.1 | .B => vp.2, b := false }, h := {} }

def initSP (tL : Option ℕ) (kr : KR) : PRFPRNG.GameState Sig I K :=
  { σ := (prng.up (prng.init kr) lam).1, corr := tL.isSome, b := false }

def initSP_zero (kr : KR) : PRFPRNG.GameState Sig I K :=
  { σ := prng.init kr, prf := true, b := false }

theorem sync_init_none_zero (kr : KR) (kc kc_ext : KC) :
    Sync prng Δcka ⟨true, none, 0⟩
      (initES_C cka prng fs lam none kr kc)
      (CKA.initState cka kc_ext true)
      (initES_P cka prng fs lam (some (prng.up (prng.init kr) lam).1) kr kc)
      (initSP_zero prng kr) := by
  refine
    { abort_C := rfl
      abort_P := rfl
      b_C := rfl
      b_P := rfl
      g_eq := rfl
      id_C := fun P => by cases P <;> rfl
      id_P := fun P => by cases P <;> rfl
      tcur_C := fun P => by cases P <;> rfl
      tcur_P := fun P => by cases P <;> rfl
      vS_eq := fun P => by cases P <;> rfl
      vR_eq := fun P => by cases P <;> rfl
      Tcur_eq := fun P => by cases P <;> rfl
      γ_C := fun P => by cases P <;> rfl
      root_P := fun P => by
        have hkr : knownRoot ⟨true, none, 0⟩ 0 = true := by
          simp [knownRoot]
        cases P <;> simp [initES_P, initES_C, mkParties, hkr]
      cka_st := fun P h => by
        simp [localCKA, initES_C] at h
      trans_inv := fun r hr => by simp [initES_C] at hr
      comp_inv := fun pos hpos => by simp [initES_C] at hpos
      epoch_S := rfl
      cache_gt := fun _ _ => ⟨rfl, rfl⟩
      ping_pong := Or.inl ⟨rfl, rfl⟩
      prng_before_tH := fun _ h => by simp at h
      prng_after_tH := fun h => by
        change 0 < 0 at h
        omega
      prng_at_tStar := fun _ h => by
        change 0 + 1 = 0 at h
        omega }

theorem sync_init_none_pos (t : ℕ) (ht : 0 < t)
    (kr : KR) (kc kc_ext : KC) :
    Sync prng Δcka ⟨true, none, t⟩
      (initES_C cka prng fs lam none kr kc)
      (CKA.initState cka kc_ext true)
      (initES_P cka prng fs lam none kr kc)
      (initSP prng lam none kr) := by
  refine
    { abort_C := rfl
      abort_P := rfl
      b_C := rfl
      b_P := rfl
      g_eq := rfl
      id_C := fun P => by cases P <;> rfl
      id_P := fun P => by cases P <;> rfl
      tcur_C := fun P => by cases P <;> rfl
      tcur_P := fun P => by cases P <;> rfl
      vS_eq := fun P => by cases P <;> rfl
      vR_eq := fun P => by cases P <;> rfl
      Tcur_eq := fun P => by cases P <;> rfl
      γ_C := fun P => by cases P <;> rfl
      root_P := fun P => by
        have hkr : knownRoot ⟨true, none, t⟩ 0 = false := by
          simp [knownRoot]; omega
        cases P <;> simp [initES_P, initES_C, mkParties, hkr]
      cka_st := fun P h => by
        simp [localCKA, initES_C] at h
      trans_inv := fun r hr => by simp [initES_C] at hr
      comp_inv := fun pos hpos => by simp [initES_C] at hpos
      epoch_S := rfl
      cache_gt := fun _ _ => ⟨rfl, rfl⟩
      ping_pong := Or.inl ⟨rfl, rfl⟩
      prng_before_tH := fun _ h => by simp at h
      prng_after_tH := fun _ _ => ⟨rfl, rfl, rfl, fun _ => rfl⟩
      prng_at_tStar := fun h => by
        change 0 = t at h
        omega }

theorem sync_init_some (l t : ℕ) (hvg : SM.lastLeakGuessAdmissible (2 + Δcka) (some l) t = true)
    (kr : KR) (kc : KC) :
    Sync prng Δcka ⟨true, some l, t⟩
      (initES_C cka prng fs lam (some l) kr kc)
      (CKA.initState cka kc true)
      (initES_P cka prng fs lam (some (prng.up (prng.init kr) lam).1) kr kc)
      (initSP prng lam (some l) kr) := by
  have ht : 0 < t := validGuess_some_pos hvg
  have hloc0 : localCKA ⟨true, some l, t⟩ Δcka 0 = false := by
    simp [localCKA, Mode.tH, healEpoch]
  refine
    { abort_C := rfl
      abort_P := rfl
      b_C := rfl
      b_P := rfl
      g_eq := rfl
      id_C := fun P => by cases P <;> rfl
      id_P := fun P => by cases P <;> rfl
      tcur_C := fun P => by cases P <;> rfl
      tcur_P := fun P => by cases P <;> rfl
      vS_eq := fun P => by cases P <;> rfl
      vR_eq := fun P => by cases P <;> rfl
      Tcur_eq := fun P => by cases P <;> rfl
      γ_C := fun P => by cases P <;> simp [initES_C, mkParties, hloc0]
      root_P := fun P => by
        have hkr : knownRoot ⟨true, some l, t⟩ 0 = true := by
          simp [knownRoot, Mode.tH, healEpoch]
        cases P <;> simp [initES_P, initES_C, mkParties, hkr]
      cka_st := fun P _ => by cases P <;> exact ⟨rfl, rfl⟩
      trans_inv := fun r hr => by simp [initES_C] at hr
      comp_inv := fun pos hpos => by simp [initES_C] at hpos
      epoch_S := rfl
      cache_gt := fun _ _ => ⟨rfl, rfl⟩
      ping_pong := Or.inl ⟨rfl, rfl⟩
      prng_before_tH := fun _ _ => ⟨rfl, rfl, rfl, rfl⟩
      prng_after_tH := fun _ h => by
        simp [initES_C, Mode.tH, healEpoch] at h
      prng_at_tStar := fun h => by
        change 0 = t at h
        omega }

theorem initPRNG_run_none_zero (kr : KR) :
    (simulateQ
      ((QueryImpl.ofLift unifSpec ProbComp).liftTarget
        (StateT (PRFPRNG.GameState Sig I K) ProbComp) + PRFPRNG.oracleImpl prng)
      ((initPRNG cka prng fs lam ⟨true, none, 0⟩).run {})).run { σ := prng.init kr, b := false } =
    (($ᵗ KC : ProbComp KC) >>= fun kc =>
      let out := prng.up (prng.init kr) lam
      pure ((some (mkParties (cka.initA kc) (cka.initB kc) (some out.1)
        (fs.initSender out.2) (fs.initReceiver out.2)), {}),
        initSP_zero prng kr)) := by
  simp [initPRNG, rootPRNG, liftP, PRFPRNG.challPrfQuery, PRFPRNG.oracleImpl,
    PRFPRNG.challPrfImpl, initSP_zero, StateT.run_bind,
    StateT.run_pure, StateT.run_get, StateT.run_set, simulateQ_bind, simulateQ_query,
    simulateQ_pure, map_eq_bind_pure_comp, bind_assoc]

theorem initPRNG_run_none_pos (t : ℕ) (ht : 0 < t) (kr : KR) :
    (simulateQ
      ((QueryImpl.ofLift unifSpec ProbComp).liftTarget
        (StateT (PRFPRNG.GameState Sig I K) ProbComp) + PRFPRNG.oracleImpl prng)
      ((initPRNG cka prng fs lam ⟨true, none, t⟩).run {})).run { σ := prng.init kr, b := false } =
    (($ᵗ KC : ProbComp KC) >>= fun kc =>
      let out := prng.up (prng.init kr) lam
      pure ((some (mkParties (cka.initA kc) (cka.initB kc) none
        (fs.initSender out.2) (fs.initReceiver out.2)), {}),
        initSP prng lam none kr)) := by
  have h0_lt : ¬ (t < 0) := by omega
  have h0_eq : ¬ (0 = t) := by omega
  simp [initPRNG, rootPRNG, liftP, PRFPRNG.processQuery, PRFPRNG.oracleImpl,
    PRFPRNG.processImpl, PRFPRNG.samIfNec, initSP, h0_lt, h0_eq, StateT.run_bind,
    StateT.run_pure, StateT.run_get, StateT.run_set, simulateQ_bind, simulateQ_query,
    simulateQ_pure, map_eq_bind_pure_comp, bind_assoc]

theorem initPRNG_run_some (l t : ℕ) (hvg : SM.lastLeakGuessAdmissible (2 + Δcka) (some l) t = true) (kr : KR) :
    (simulateQ
      ((QueryImpl.ofLift unifSpec ProbComp).liftTarget
        (StateT (PRFPRNG.GameState Sig I K) ProbComp) + PRFPRNG.oracleImpl prng)
      ((initPRNG cka prng fs lam ⟨true, some l, t⟩).run {})).run { σ := prng.init kr, b := false } =
    (($ᵗ KC : ProbComp KC) >>= fun kc =>
      let out := prng.up (prng.init kr) lam
      pure ((some (mkParties (cka.initA kc) (cka.initB kc) (some out.1)
        (fs.initSender out.2) (fs.initReceiver out.2)), {}),
        initSP prng lam (some l) kr)) := by
  have ht : 0 < t := validGuess_some_pos hvg
  have h0_lt : ¬ (t < 0) := by omega
  have h0_eq : ¬ (0 = t) := by omega
  simp [initPRNG, rootPRNG, processCorr, liftP, PRFPRNG.processQuery, PRFPRNG.corrQuery,
    PRFPRNG.oracleImpl, PRFPRNG.processImpl, PRFPRNG.corrImpl, PRFPRNG.samIfNec,
    Mode.tH, healEpoch, initSP, h0_lt, h0_eq, StateT.run_bind, StateT.run_pure,
    StateT.run_get, StateT.run_set, simulateQ_bind, simulateQ_query, simulateQ_pure,
    map_eq_bind_pure_comp, bind_assoc]

theorem authOut_of_validGuess_false {VPt M C HS : Type} [DecidableEq M] (Δ : ℕ) (π : Policy)
    (h : SM.lastLeakGuessAdmissible Δ π.tL π.tStar = false) (es : EState VPt M C HS) :
    authOut Δ π es = false := by
  simp [authOut, SM.authLosingConditionsAvoided, h]

theorem lemma10_proof (hc : cka.Correct) (tL : Option ℕ) (t : ℕ)
    (A : SchemeAdversary Γ T Sig SS RS M CCoins E) :
    𝒟[CKA.branch cka Δcka (healEpoch tL) true
        (redCKAAuth cka prng fs lam Δcka qep tL t A)] {true} ≤
      𝒟[PRFPRNG.branch prng false (redPRNGAuth cka prng fs lam Δcka qep tL t A)] {true} := by
  by_cases hvg : SM.lastLeakGuessAdmissible (2 + Δcka) tL t = true
  · cases htL : tL with
    | none =>
      subst htL
      have hL : CKA.branch cka Δcka (healEpoch none) true
          (redCKAAuth cka prng fs lam Δcka qep none t A) =
          ($ᵗ KC >>= fun kc_ext => $ᵗ KR >>= fun kr => $ᵗ KC >>= fun kc =>
            runL cka prng fs Δcka qep ⟨true, none, t⟩ A
              (initES_C cka prng fs lam none kr kc)
              (CKA.initState cka kc_ext true)) := by
        unfold CKA.branch redCKAAuth runCKA engRun initCKA runL initES_C
        simp only [cImpl, Mode.tH, Mode.policy, StateT.run'_eq, StateT.run_lift,
          StateT.run_bind, StateT.run_pure, simulateQ_bind, simulateQ_pure,
          simulateQ_sampleT_run, map_eq_bind_pure_comp, bind_assoc, pure_bind,
          Function.comp_apply]
        rfl
      rcases Nat.eq_zero_or_pos t with rfl | ht
      · have hR : PRFPRNG.branch prng false
            (redPRNGAuth cka prng fs lam Δcka qep none 0 A) =
            ($ᵗ KR >>= fun kr => $ᵗ KC >>= fun kc =>
              runR cka prng fs Δcka qep ⟨true, none, 0⟩ A
                (initES_P cka prng fs lam (some (prng.up (prng.init kr) lam).1) kr kc)
                (initSP_zero prng kr)) := by
          unfold PRFPRNG.branch redPRNGAuth runPRNG engRun runR initES_P
          simp only [pImpl, Mode.policy, StateT.run'_eq, StateT.run_bind, simulateQ_bind,
            initPRNG_run_none_zero cka prng fs lam, map_eq_bind_pure_comp,
            bind_assoc, pure_bind, simulateQ_pure, StateT.run_pure, Function.comp_apply]
          rfl
        rw [hL, hR]
        have hconst :
            𝒟[$ᵗ KC >>= fun _ : KC => $ᵗ KR >>= fun kr => $ᵗ KC >>= fun kc =>
              runR cka prng fs Δcka qep ⟨true, none, 0⟩ A
                (initES_P cka prng fs lam (some (prng.up (prng.init kr) lam).1) kr kc)
                (initSP_zero prng kr)] {true} =
            𝒟[$ᵗ KR >>= fun kr => $ᵗ KC >>= fun kc =>
              runR cka prng fs Δcka qep ⟨true, none, 0⟩ A
                (initES_P cka prng fs lam (some (prng.up (prng.init kr) lam).1) kr kc)
                (initSP_zero prng kr)] {true} := by
          rw [OracleComp.evalDist_bind_const]
        rw [← hconst]
        refine OracleComp.evalDist_bind_apply_mono_of_support _ _ _ (MeasurableSet.singleton true)
          fun kc_ext _ => ?_
        refine OracleComp.evalDist_bind_apply_mono_of_support _ _ _ (MeasurableSet.singleton true)
          fun kr _ => ?_
        refine OracleComp.evalDist_bind_apply_mono_of_support _ _ _ (MeasurableSet.singleton true)
          fun kc _ => ?_
        exact runL_le_runR cka prng fs Δcka qep ⟨true, none, 0⟩ rfl hvg A
          (sync_init_none_zero cka prng fs lam Δcka kr kc kc_ext)
      · have hR : PRFPRNG.branch prng false
            (redPRNGAuth cka prng fs lam Δcka qep none t A) =
            ($ᵗ KR >>= fun kr => $ᵗ KC >>= fun kc =>
              runR cka prng fs Δcka qep ⟨true, none, t⟩ A
                (initES_P cka prng fs lam none kr kc)
                (initSP prng lam none kr)) := by
          unfold PRFPRNG.branch redPRNGAuth runPRNG engRun runR initES_P
          simp only [pImpl, Mode.policy, StateT.run'_eq, StateT.run_bind, simulateQ_bind,
            initPRNG_run_none_pos cka prng fs lam t ht, map_eq_bind_pure_comp,
            bind_assoc, pure_bind, simulateQ_pure, StateT.run_pure, Function.comp_apply]
          rfl
        rw [hL, hR]
        have hconst :
            𝒟[$ᵗ KC >>= fun _ : KC => $ᵗ KR >>= fun kr => $ᵗ KC >>= fun kc =>
              runR cka prng fs Δcka qep ⟨true, none, t⟩ A
                (initES_P cka prng fs lam none kr kc)
                (initSP prng lam none kr)] {true} =
            𝒟[$ᵗ KR >>= fun kr => $ᵗ KC >>= fun kc =>
              runR cka prng fs Δcka qep ⟨true, none, t⟩ A
                (initES_P cka prng fs lam none kr kc)
                (initSP prng lam none kr)] {true} := by
          rw [OracleComp.evalDist_bind_const]
        rw [← hconst]
        refine OracleComp.evalDist_bind_apply_mono_of_support _ _ _ (MeasurableSet.singleton true)
          fun kc_ext _ => ?_
        refine OracleComp.evalDist_bind_apply_mono_of_support _ _ _ (MeasurableSet.singleton true)
          fun kr _ => ?_
        refine OracleComp.evalDist_bind_apply_mono_of_support _ _ _ (MeasurableSet.singleton true)
          fun kc _ => ?_
        exact runL_le_runR cka prng fs Δcka qep ⟨true, none, t⟩ rfl hvg A
          (sync_init_none_pos cka prng fs lam Δcka t ht kr kc kc_ext)
    | some l =>
      subst htL
      have hL : CKA.branch cka Δcka (healEpoch (some l)) true
          (redCKAAuth cka prng fs lam Δcka qep (some l) t A) =
          ($ᵗ KC >>= fun kc => $ᵗ KR >>= fun kr =>
            runL cka prng fs Δcka qep ⟨true, some l, t⟩ A
              (initES_C cka prng fs lam (some l) kr kc)
              (CKA.initState cka kc true)) := by
        unfold CKA.branch redCKAAuth runCKA engRun initCKA runL initES_C
        simp only [cImpl, Mode.tH, Mode.policy, StateT.run'_eq, StateT.run_lift,
          StateT.run_bind, StateT.run_pure, simulateQ_bind, simulateQ_pure,
          simulateQ_sampleT_run, map_eq_bind_pure_comp, bind_assoc, pure_bind,
          Function.comp_apply]
        rfl
      have hR : PRFPRNG.branch prng false
          (redPRNGAuth cka prng fs lam Δcka qep (some l) t A) =
          ($ᵗ KR >>= fun kr => $ᵗ KC >>= fun kc =>
            runR cka prng fs Δcka qep ⟨true, some l, t⟩ A
              (initES_P cka prng fs lam (some (prng.up (prng.init kr) lam).1) kr kc)
              (initSP prng lam (some l) kr)) := by
        unfold PRFPRNG.branch redPRNGAuth runPRNG engRun runR initES_P
        simp only [pImpl, Mode.policy, StateT.run'_eq, StateT.run_bind, simulateQ_bind,
          initPRNG_run_some cka prng fs lam Δcka l t hvg, map_eq_bind_pure_comp,
          bind_assoc, pure_bind, simulateQ_pure, StateT.run_pure, Function.comp_apply]
        rfl
      rw [hL, hR, OracleComp.evalDist_bind_bind_swap ($ᵗ KR) ($ᵗ KC)]
      refine OracleComp.evalDist_bind_apply_mono_of_support _ _ _ (MeasurableSet.singleton true)
        fun kc _ => ?_
      refine OracleComp.evalDist_bind_apply_mono_of_support _ _ _ (MeasurableSet.singleton true)
        fun kr _ => ?_
      exact runL_le_runR cka prng fs Δcka qep ⟨true, some l, t⟩ rfl hvg A
        (sync_init_some cka prng fs lam Δcka l t hvg kr kc)
  · have hvg_f : SM.lastLeakGuessAdmissible (2 + Δcka) tL t = false := Bool.eq_false_iff.mpr hvg
    have hred : redCKAAuth cka prng fs lam Δcka qep tL t A =
        (runCKA cka prng fs lam Δcka qep ⟨true, tL, t⟩ false A >>= fun _ => pure false) := by
      dsimp only [redCKAAuth]
      congr 1
      funext r
      cases r with
      | none => rfl
      | some p => exact congrArg pure (authOut_of_validGuess_false (2 + Δcka) ⟨true, tL, t⟩ hvg_f p.2)
    have hbranch : 𝒟[CKA.branch cka Δcka (healEpoch tL) true
        (redCKAAuth cka prng fs lam Δcka qep tL t A)] = 𝒟[(pure false : ProbComp Bool)] := by
      unfold CKA.branch
      rw [hred]
      simp only [StateT.run'_eq, simulateQ_bind, simulateQ_pure, StateT.run_bind, StateT.run_pure,
        map_eq_bind_pure_comp, bind_assoc, pure_bind, Function.comp_apply]
      refine evalDist_bind_false_of_support ($ᵗ KC) _ fun k _ => ?_
      exact OracleComp.evalDist_bind_const _ _
    rw [hbranch]
    simp

end CryptoGames.SM.Construction.AuthL10
