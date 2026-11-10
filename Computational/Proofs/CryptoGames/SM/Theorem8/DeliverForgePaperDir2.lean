/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Computational.Proofs.CryptoGames.SM.Theorem8.DeliverForgePaperShiftedCKA2
import Computational.Proofs.CryptoGames.SM.Theorem8.DeliverForgePaperShiftedCKA
import Computational.Proofs.CryptoGames.SM.Theorem8.DeliverForgePaperShiftedFS3
import Computational.Proofs.CryptoGames.SM.Theorem8.DeliverForgePaperShiftedPRNG3
import Computational.Proofs.CryptoGames.SM.Theorem8.Lemma9
import ProofLib.SepLogic.WP.StateNorm

/-!
# Paper-Engine Healing-Epoch Boundary and Shifted Reductions

Reductions and Lemma 9 for the boundary cell of the paper `DeliverForge` engine at `Δ = 2`,
the Theorem 8 bounds for the shifted paper games, and `NoBadCoinsDF` for `challSimDF'Paper`.
-/

@[expose] public section

set_option autoImplicit false

open scoped BigOperators ENNReal
open MeasureTheory ProbabilityTheory OracleComp OracleSpec

namespace CryptoGames.SM.Construction.DeliverForge

open CryptoGames.SM
open CryptoGames.SM.Engine
open CryptoGames.SM.Construction
open CryptoGames.LibsignalSM.Proofs.Refinement

variable {ι : Type} {tspec : OracleSpec.{0, 0} ι}
  {HS KC Γ CCoins T I KR Sig K SS RS M E Γv Sv SSv RSv : Type}

section AuthL9ShiftedDir2PaperEnd

open CryptoGames.SM.Construction.AuthL9
open CryptoGames.SM.Construction.DeliverForge.AuthL9DF
open CryptoGames.SM.Construction.AuthL9DFDir2

variable [DecidableEq T] [DecidableEq M] [DecidableEq E] [DecidableEq I] [Inhabited E]
  [SampleableType KR] [SampleableType KC] [SampleableType CCoins] [SampleableType I]
  [SampleableType K]

local notation "ASpecDF" =>
  unifSpec + specDF (PartyState Γ T Sig SS RS) M CCoins (Header T × E)

theorem step_inject_DFShiftedDir2Paper {α : Type} (cka : CKAScheme KC Γ CCoins T I)
    (prng : PRFPRNG KR Sig I K) (fs : FSAEADScheme K SS RS (Header T) M E)
    (lam : I) (qep l : ℕ) (P : Party) (c : Header T × E)
    (k : (ASpecDF).Range (Sum.inr (Sum.inl (Sum.inl (Sum.inr (P, c))))) →
      AdversaryCompDF (PartyState Γ T Sig SS RS) M CCoins (Header T × E) α)
    {s : GameState (PartyState Γ T Sig SS RS) M (Header T × E)}
    {es : EState (PartyState (Option Γ) T Sig SS RS) M (Header T × E) (CKAStateShifted Γ T I)}
    {sc : CKA.GameState Γ T}
    (hs : Sync9ShiftedDir2 cka l s es sc)
    (ih : ∀ u {s' es' sc'}, Sync9ShiftedDir2 cka l s' es' sc' →
      𝒟[runLDFShiftedDir2Paper cka prng fs lam qep l (k u) s'] {true} ≤
        𝒟[runRDFShiftedDir2Paper cka prng fs qep l (k u) es' sc'] {true}) :
    𝒟[runLDFShiftedDir2Paper cka prng fs lam qep l
        (query (spec := ASpecDF) (Sum.inr (Sum.inl (Sum.inl (Sum.inr (P, c))))) >>= k) s]
        {true} ≤
      𝒟[runRDFShiftedDir2Paper cka prng fs qep l
        (query (spec := ASpecDF) (Sum.inr (Sum.inl (Sum.inl (Sum.inr (P, c))))) >>= k) es sc]
        {true} := by
  rw [runLDFShiftedDir2Paper_query_bind, runRDFShiftedDir2Paper_query_bind]
  dsimp only [QueryImpl.add_apply, fullImplBaseDFShiftedDir2Paper, oracleImplBaseDFShiftedDir2Paper,
    oracleImplShiftedDir2Paper, implEDFShiftedDir2Paper, injectImplB1, injectEB1, Config.auth]
  have habort : es.abort = false := hs.base.base.no_abort
  have hwin : s.win = es.g.win := by rw [hs.base.base.s_eq]; rfl
  have hin_eq : s.inTransit P.other c = es.g.inTransit P.other c := by rw [hs.base.base.s_eq]; rfl
  have hsafe_eq : s.safeInj 2 = es.g.safeInj 2 := by rw [hs.base.base.s_eq]; rfl
  have htriv_eq : ∀ pos, trivB1 (l + 1) s pos = trivB1 (l + 1) es.g pos :=
    fun pos => by rw [hs.base.base.s_eq]; rfl
  simp only [habort, Bool.false_or, hwin, hin_eq, hsafe_eq,
    StateT.run_bind, StateT.run_get, pure_bind]
  by_cases hcond :
      (es.g.win || (es.g.inTransit P.other c).isSome || !es.g.safeInj 2) = true
  · simp [hcond, ih none hs]
  · simp only [hcond, Bool.false_eq_true, ↓reduceIte]
    have hsafe : es.g.safeInj 2 = true := by
      cases h : es.g.safeInj 2
      · simp [h] at hcond
      · rfl
    by_cases hguard : (P.sendsIn c.1.1 || decide (es.g.epoch P + 1 < c.1.1)) = true
    · obtain ⟨hrcvL, hrcvR⟩ :=
        AuthL9.vRecv_guard_true cka prng fs 1 (some (l - 1)) 0 (rec := none) hs.base.base hguard
      dsimp only at hrcvL hrcvR
      dsimp only [scheme]
      rw [hrcvL, StateT.run_bind, vRecv_hooksCKAShifted_run, hrcvR]
      simp [ih (some .rejected) hs]
    · have hnsend : P.sendsIn c.1.1 = false := by
        cases h : P.sendsIn c.1.1
        · rfl
        · simp [h] at hguard
      have hle_P1 : c.1.1 ≤ es.g.epoch P + 1 := by
        simp [hnsend] at hguard
        omega
      by_cases hstep : c.1.1 = es.g.epoch P + 1
      · have htriv_f : ∀ i', trivB1 (l + 1) es.g ⟨P.other, c.1.1, i'⟩ = false := by
          intro i'
          rw [trivB1_eq_trivial_of_new_epoch (l + 1) es.g P ⟨P.other, c.1.1, i'⟩ hstep]
          exact trivial_false_of_safeInj_dir2 hs.base (P := P) hsafe (by dsimp; omega)
        cases hc2 : c.1.2 with
        | none =>
          obtain ⟨hrcvL, hrcvR⟩ :=
            AuthL9.vRecv_new_none cka prng fs 1 (some (l - 1)) 0 (rec := none) hs.base.base hnsend hstep hc2
          dsimp only at hrcvL hrcvR
          dsimp only [scheme]
          rw [hrcvL, StateT.run_bind, vRecv_hooksCKAShifted_run, hrcvR]
          simp [ih (some .rejected) hs]
        | some Tn =>
          by_cases hhon_ex : ∃ I_t, es.h.base.cache c.1.1 = some (Tn, I_t)
          · rcases hhon_ex with ⟨I_t, hcache'⟩
            have hle_max : c.1.1 ≤ max (es.g.epoch .A) (es.g.epoch .B) := by
              by_contra hgt
              have hnone := hs.base.base.cache_gt c.1.1 (by dsimp; omega)
              dsimp only at hnone
              rw [hnone] at hcache'
              nomatch hcache'
            have heq_other : es.g.epoch P + 1 = es.g.epoch P.other := by
              have hle2 := hs.base.base.epoch_le P.other
              dsimp only at hle2
              rw [Party.other_other] at hle2
              cases P <;> simp [Party.other] at hle_max hstep hle2 ⊢ <;> omega
            obtain ⟨T_t, I_t', hcache_step, _, _, hI, _⟩ := hs.base.base.cka_step P heq_other
            dsimp only at hcache_step hI
            rw [← heq_other, ← hstep, hcache'] at hcache_step
            injection hcache_step with hpair
            injection hpair with hT_eq hI_eq
            subst hT_eq hI_eq
            obtain ⟨hrcvL, hrcvR⟩ :=
              AuthL9.vRecv_new_honest cka prng fs 1 (some (l - 1)) 0 (rec := none)
                hs.base.base hnsend hstep hc2 hcache' hI
            dsimp only at hrcvL hrcvR
            dsimp only [scheme]
            rw [hrcvL, StateT.run_bind, vRecv_hooksCKAShifted_run, hrcvR]
            simp only [pure_bind]
            cases hfs : fs.receive (fs.initReceiver (prng.up (es.g.st P).root I_t).2) c.1 c.2 with
            | none =>
              simp [ih (some .rejected) hs]
            | some val =>
              rcases val with ⟨v', i', m'⟩
              simp only [htriv_eq, htriv_f, Bool.false_eq_true, ↓reduceIte]
              by_cases hqep : qep + 1 < c.1.1
              · simp [hqep, ih (some .rejected) hs]
              · simp only [hqep, ↓reduceIte]
                by_cases hfull : (c.1.1 == l + 1) = true
                · simp only [hfull, ↓reduceIte, StateT.run_bind, StateT.run_set,
                    StateT.run_modify, pure_bind, StateT.run_pure, simulateQ_pure]
                  exact ih (some .rejected) (sync9ShiftedDir2_win hs true)
                · simp [hfull, ih (some .rejected) hs]
          · have hhon : ∀ Tc Ik, es.h.base.cache c.1.1 = some (Tc, Ik) → Tc ≠ Tn := by
              intro Tc Ik hc heq
              subst heq
              exact hhon_ex ⟨Ik, hc⟩
            have hrcvR :=
              AuthL9.vRecv_new_dishonest_ne cka prng fs 1 (some (l - 1)) 0 (rec := none)
                hs.base.base hnsend hstep hc2 hhon (by omega)
            dsimp only at hrcvR
            rw [StateT.run_bind, vRecv_hooksCKAShifted_run, hrcvR]
            simp only [pure_bind, StateT.run_pure, simulateQ_pure]
            dsimp only [scheme]
            cases hrcvL : receive cka prng fs (s.st P) c with
            | none =>
              simp [ih (some .rejected) hs]
            | some res =>
              rcases res with ⟨st', t', i', m'⟩
              have ht' : t' = c.1.1 := AuthL9.receive_t_eq cka prng fs hrcvL
              subst ht'
              simp only [htriv_eq, htriv_f, Bool.false_eq_true, ↓reduceIte]
              by_cases hqep : qep + 1 < c.1.1
              · simp [hqep, ih (some .rejected) hs]
              · simp only [hqep, ↓reduceIte]
                by_cases hfull : (c.1.1 == l + 1) = true
                · have heq_l1 : es.g.epoch P + 1 = l + 1 := by
                    have h := beq_iff_eq.mp hfull; omega
                  have hdoom := doomed_win_of_safeInj_two_epoch_eq hs P heq_l1 hsafe
                  simp only [hfull, ↓reduceIte, StateT.run_bind, StateT.run_set,
                    StateT.run_pure, pure_bind]
                  rw [evalDist_runLDFShiftedDir2Paper_true_eq_zero_of_doomed cka prng fs lam qep l
                    (k (some .rejected)) { s with win := true } hdoom]
                  simp
                · simp [hfull, ih (some .rejected) hs]
      · have hle_P : c.1.1 ≤ es.g.epoch P := by omega
        obtain ⟨hrcvL, hrcvR⟩ :=
          AuthL9.vRecv_same_epoch cka prng fs 1 (some (l - 1)) 0 (rec := none) hs.base.base hnsend hle_P
        dsimp only at hrcvL hrcvR
        dsimp only [scheme]
        rw [hrcvL, StateT.run_bind, vRecv_hooksCKAShifted_run, hrcvR]
        simp only [pure_bind]
        cases hv : (es.g.st P).vR c.1.1 with
        | none =>
          simp [ih (some .rejected) hs]
        | some v =>
          simp only []
          cases hfs : fs.receive v c.1 c.2 with
          | none =>
            simp [ih (some .rejected) hs]
          | some val =>
            rcases val with ⟨v', i', m'⟩
            simp only []
            by_cases hqep : qep + 1 < c.1.1
            · simp [hqep, ih (some .rejected) hs]
            · simp only [hqep, ↓reduceIte, htriv_eq]
              by_cases htriv : trivB1 (l + 1) es.g ⟨P.other, c.1.1, i'⟩ = true
              · have hcom := commitE_same_shifted cka prng fs l 0
                  (P := P)
                  (new := { es.g.st P with vR := Function.update (es.g.st P).vR c.1.1 (some v') })
                  (pos := ⟨P.other, c.1.1, i'⟩) (es := es) (sc := sc) rfl
                have hsync := sync9ShiftedDir2_accept_same hs
                  (Function.update (es.g.st P).vR c.1.1 (some v'))
                  (pos := ⟨P.other, c.1.1, i'⟩) hle_P
                simp only [htriv, ↓reduceIte, StateT.run_bind, StateT.run_set, pure_bind,
                  StateT.run_pure, simulateQ_bind, hcom, StateT.run_modify,
                  simulateQ_pure]
                exact ih _ hsync
              · simp only [htriv, Bool.false_eq_true, ↓reduceIte]
                by_cases hfull : (c.1.1 == l + 1) = true
                · simp only [hfull, ↓reduceIte, StateT.run_bind, StateT.run_set,
                    StateT.run_modify, pure_bind, StateT.run_pure, simulateQ_pure]
                  exact ih (some .rejected) (sync9ShiftedDir2_win hs true)
                · simp [hfull, ih (some .rejected) hs]

omit [DecidableEq I] [SampleableType KR] [SampleableType KC] [SampleableType I]
  [SampleableType K] in
theorem evalDist_runLDFShiftedDir2Paper_eq_pure_false_of_doomed {α : Type}
    (cka : CKAScheme KC Γ CCoins T I) (prng : PRFPRNG KR Sig I K)
    (fs : FSAEADScheme K SS RS (Header T) M E) (lam : I) (qep l : ℕ)
    (oa : AdversaryCompDF (PartyState Γ T Sig SS RS) M CCoins (Header T × E) α)
    (s : GameState (PartyState Γ T Sig SS RS) M (Header T × E))
    (hd : DoomedAuthShiftedDir2Paper l s) :
    evalDist (runLDFShiftedDir2Paper cka prng fs lam qep l oa s) =
      evalDist (pure false : ProbComp Bool) := by
  apply AuthL9.evalDist_bind_eq_pure_false
  rintro ⟨a, s'⟩ hmem
  have hd' := doomedAuthShiftedDir2Paper_simulateQ_DF (scheme cka prng fs lam) l qep oa hd hmem
  dsimp only
  rw [doomedAuthShiftedDir2Paper_not_win l s' hd']

theorem step_transmit_DFShiftedDir2Paper {α : Type} (cka : CKAScheme KC Γ CCoins T I)
    (prng : PRFPRNG KR Sig I K) (fs : FSAEADScheme K SS RS (Header T) M E)
    (lam : I) (qep l : ℕ) (P : Party) (m : M)
    (k : (ASpecDF).Range (Sum.inr (Sum.inl (Sum.inl (Sum.inl (Sum.inl (Sum.inl (P, m, none))))))) →
      AdversaryCompDF (PartyState Γ T Sig SS RS) M CCoins (Header T × E) α)
    {s : GameState (PartyState Γ T Sig SS RS) M (Header T × E)}
    {es : EState (PartyState (Option Γ) T Sig SS RS) M (Header T × E) (CKAStateShifted Γ T I)}
    {sc : CKA.GameState Γ T}
    (hs : Sync9ShiftedDir2 cka l s es sc)
    (ih : ∀ u {s' es' sc'}, Sync9ShiftedDir2 cka l s' es' sc' →
      𝒟[runLDFShiftedDir2Paper cka prng fs lam qep l (k u) s'] {true} ≤
        𝒟[runRDFShiftedDir2Paper cka prng fs qep l (k u) es' sc'] {true}) :
    𝒟[runLDFShiftedDir2Paper cka prng fs lam qep l
        (query (spec := ASpecDF)
          (Sum.inr (Sum.inl (Sum.inl (Sum.inl (Sum.inl (Sum.inl (P, m, none))))))) >>= k) s]
        {true} ≤
      𝒟[runRDFShiftedDir2Paper cka prng fs qep l
        (query (spec := ASpecDF)
          (Sum.inr (Sum.inl (Sum.inl (Sum.inl (Sum.inl (Sum.inl (P, m, none))))))) >>= k)
          es sc] {true} := by
  rw [runLDFShiftedDir2Paper_query_bind, runRDFShiftedDir2Paper_query_bind]
  dsimp only [QueryImpl.add_apply, fullImplBaseDFShiftedDir2Paper, oracleImplBaseDFShiftedDir2Paper,
    oracleImplShiftedDir2Paper, implEDFShiftedDir2Paper]
  have habort : es.abort = false := hs.base.base.no_abort
  by_cases hw : es.g.win = true
  · have hwin : s.win = true := by rw [hs.base.base.s_eq]; exact hw
    dsimp only [transmitImpl, transmitE]
    simp [habort, hw, hwin, ih none hs]
  · have hw_f : es.g.win = false := Bool.eq_false_iff.mpr hw
    rw [AuthL9DFDir2.transmitImpl_run_eq_dir2 cka prng fs lam qep hs.base hw_f]
    dsimp only [transmitE]
    simp only [habort, hw_f, Bool.or_self, Bool.false_eq_true, ↓reduceIte,
      StateT.run_bind, StateT.run_get, pure_bind, bind_assoc, Option.isSome_none]
    cases hep : es.g.epMgmt 2 qep P false with
    | none =>
      simp only [pure_bind, StateT.run_pure, simulateQ_pure, OracleComp.evalDist_bind_const]
      exact ih none hs
    | some s₁ =>
      have hs₁_st : s₁.st = es.g.st := by
        unfold GameState.epMgmt at hep
        split_ifs at hep <;> (injection hep with hep; subst hep; simp [GameState.leak])
      simp only []
      by_cases hld : (Policy.mk true (some (l - 1)) (l + 1)).leakDoom es.g s₁ = true
      · simp only [hld, ↓reduceIte, abortE, StateT.run_bind, StateT.run_modify, pure_bind,
          StateT.run_pure, simulateQ_pure]
        have hL : 𝒟[$ᵗ CCoins >>= fun coins =>
            runLDFShiftedDir2Paper cka prng fs lam qep l
              (k (some (send cka prng fs (s.st P) m coins).2))
              ((AuthL9.realGS sc s₁).record 2 P (send cka prng fs (s.st P) m coins).1
                ⟨⟨P, s₁.epoch P, s₁.idx P + 1⟩, m,
                  (send cka prng fs (s.st P) m coins).2⟩ false)] =
            𝒟[(pure false : ProbComp Bool)] := by
          refine AuthL9.evalDist_bind_eq_pure_false _ _ fun coins _ => ?_
          have hdoom := doomed_of_leakDoom_epMgmt_shifted_dir2 hs hw_f hep hld
            (send cka prng fs (s.st P) m coins).1 m
            (send cka prng fs (s.st P) m coins).2 false
          exact evalDist_runLDFShiftedDir2Paper_eq_pure_false_of_doomed cka prng fs lam qep l
            (k (some (send cka prng fs (s.st P) m coins).2)) _ hdoom
        rw [hL]
        simp
      · simp only [hld, Bool.false_eq_true, ↓reduceIte, hs₁_st]
        rw [vSend_hooksCKAShifted_zero_eq cka prng fs l ((l - 1) + 3)]
        by_cases hsend : P.sendsIn (es.g.epoch P + 1) = true
        · have hq : ¬qep < es.g.epoch P + 1 := by
            intro hq; simp [GameState.epMgmt, hsend, hq] at hep
          have hs₁_ep : s₁.epoch P = es.g.epoch P + 1 := by
            unfold GameState.epMgmt at hep
            simp only [hsend, hq, ↓reduceIte] at hep
            split_ifs at hep <;>
              (injection hep with hep; subst hep; simp [GameState.leak])
          have hs₁_idx : s₁.idx P = 0 := by
            unfold GameState.epMgmt at hep
            simp only [hsend, hq, ↓reduceIte] at hep
            split_ifs at hep <;>
              (injection hep with hep; subst hep; simp [GameState.leak])
          have hsend_eq := fun coins =>
            AuthL9.send_new_eq cka prng fs 1 (some (l - 1)) ((l - 1) + 3) (m := m) (coins := coins)
              hs.base.base hsend
          dsimp only at hsend_eq
          by_cases hloc : AuthL9.isLocal (some (l - 1)) 1 (es.g.epoch P) = true
          · have hvR := vSend_new_local_shifted cka prng fs
              (m := m) (r := none) (s₁ := s₁) hs.toSync9Shifted hsend hloc
            dsimp only at hvR
            rw [StateT.run_bind, simulateQ_bind, StateT.run_bind, hvR]
            simp only [bind_assoc, pure_bind, hs₁_ep, hs₁_idx]
            refine OracleComp.evalDist_bind_apply_mono_of_support _ _ _
              (MeasurableSet.singleton true) fun coins _ => ?_
            rw [hsend_eq coins]
            exact ih _ (sync9ShiftedDir2_send_new prng fs hs hsend hep coins m false)
          · have hloc_f : AuthL9.isLocal (some (l - 1)) 1 (es.g.epoch P) = false :=
              Bool.eq_false_iff.mpr hloc
            have hvR := vSend_new_nonlocal_none_shifted cka prng fs
              (m := m) (s₁ := s₁) hs.toSync9Shifted hsend hloc_f
            dsimp only at hvR
            rw [StateT.run_bind, simulateQ_bind, StateT.run_bind, hvR]
            simp only [bind_assoc, pure_bind, hs₁_ep, hs₁_idx]
            refine OracleComp.evalDist_bind_apply_mono_of_support _ _ _
              (MeasurableSet.singleton true) fun coins _ => ?_
            rw [hsend_eq coins]
            exact ih _ (sync9ShiftedDir2_send_new prng fs hs hsend hep coins m false)
        · have hnsend : P.sendsIn (es.g.epoch P + 1) = false :=
            Bool.eq_false_iff.mpr hsend
          have hs₁_eq : s₁ = es.g := by
            unfold GameState.epMgmt at hep
            simp only [hnsend, Bool.false_eq_true, ↓reduceIte] at hep
            split_ifs at hep
            injection hep with hep
            exact hep.symm
          subst hs₁_eq
          obtain ⟨hsendL, hsendR⟩ :=
            vSend_same_epoch_shifted cka prng fs (m := m) (r := none) hs.toSync9Shifted hnsend
          dsimp only at hsendL hsendR
          have hreal_eq : AuthL9.realGS sc es.g = s := hs.base.base.s_eq.symm
          rw [StateT.run_bind, hsendR]
          simp only [hsendL, hreal_eq, pure_bind, OracleComp.evalDist_bind_const]
          exact ih _ (sync9ShiftedDir2_send_same hs hnsend _ m _ false)

theorem step_deliverForge_DFShiftedDir2Paper {α : Type} (cka : CKAScheme KC Γ CCoins T I)
    (prng : PRFPRNG KR Sig I K) (fs : FSAEADScheme K SS RS (Header T) M E)
    (lam : I) (qep l : ℕ) (P : Party) (c c' : Header T × E)
    (k : (ASpecDF).Range (Sum.inr (Sum.inr (P, c, c'))) →
      AdversaryCompDF (PartyState Γ T Sig SS RS) M CCoins (Header T × E) α)
    {s : GameState (PartyState Γ T Sig SS RS) M (Header T × E)}
    {es : EState (PartyState (Option Γ) T Sig SS RS) M (Header T × E) (CKAStateShifted Γ T I)}
    {sc : CKA.GameState Γ T}
    (hs : Sync9ShiftedDir2 cka l s es sc)
    (ih : ∀ u {s' es' sc'}, Sync9ShiftedDir2 cka l s' es' sc' →
      𝒟[runLDFShiftedDir2Paper cka prng fs lam qep l (k u) s'] {true} ≤
        𝒟[runRDFShiftedDir2Paper cka prng fs qep l (k u) es' sc'] {true}) :
    𝒟[runLDFShiftedDir2Paper cka prng fs lam qep l
        (query (spec := ASpecDF) (Sum.inr (Sum.inr (P, c, c'))) >>= k) s] {true} ≤
      𝒟[runRDFShiftedDir2Paper cka prng fs qep l
        (query (spec := ASpecDF) (Sum.inr (Sum.inr (P, c, c'))) >>= k) es sc] {true} := by
  rw [runLDFShiftedDir2Paper_query_bind, runRDFShiftedDir2Paper_query_bind]
  dsimp only [QueryImpl.add_apply, fullImplBaseDFShiftedDir2Paper, oracleImplBaseDFShiftedDir2Paper,
    implEDFShiftedDir2Paper, deliverForgeBaseImplB1, deliverForgeEB1, sameHdrScheme, Config.auth]
  have habort : es.abort = false := hs.base.base.no_abort
  have hwin : s.win = es.g.win := by rw [hs.base.base.s_eq]; rfl
  have hin_eq : s.inTransit P.other c = es.g.inTransit P.other c := by rw [hs.base.base.s_eq]; rfl
  have hin'_eq : s.inTransit P.other c' = es.g.inTransit P.other c' := by
    rw [hs.base.base.s_eq]; rfl
  have hcomp_eq : ∀ pos, s.comp.contains pos = es.g.comp.contains pos :=
    fun pos => by rw [hs.base.base.s_eq]; rfl
  have htriv_eq : ∀ pos, trivB1 (l + 1) s pos = trivB1 (l + 1) es.g pos :=
    fun pos => by rw [hs.base.base.s_eq]; rfl
  have hbne : (!(c.1 == c'.1)) = (c.1 != c'.1) := rfl
  simp only [habort, Bool.false_or, hwin, hin_eq, hin'_eq, hcomp_eq, hbne,
    StateT.run_bind, StateT.run_get, pure_bind]
  by_cases hw : es.g.win = true
  · simp [hw, ih none hs]
  · simp only [hw, Bool.false_eq_true, ↓reduceIte]
    cases hin : es.g.inTransit P.other c with
    | none => simp [ih none hs]
    | some r =>
      simp only []
      by_cases hguard :
          ((es.g.inTransit P.other c').isSome || es.g.comp.contains r.pos ||
            (c.1 != c'.1)) = true
      · simp only [hguard, ↓reduceIte, StateT.run_pure, simulateQ_pure, pure_bind]
        exact ih none hs
      · simp only [hguard, Bool.false_eq_true, ↓reduceIte]
        have hhdr : c'.1 = c.1 := by
          rcases Bool.or_eq_false_iff.mp (Bool.eq_false_iff.mpr hguard) with ⟨_, h2⟩
          exact (bne_eq_false_iff_eq.mp h2).symm
        obtain ⟨hmem, hsnd, hct⟩ := AuthL9.mem_trans_of_inTransit hin
        obtain ⟨ht_ep, hsnd_sends, hle_snd, hTcur⟩ := hs.base.base.trans_inv r hmem
        dsimp only at ht_ep hsnd_sends hle_snd hTcur
        have hpos_c : r.pos.epoch = c'.1.1 := by rw [hhdr, ← hct, ht_ep]
        have hnsend : P.sendsIn c'.1.1 = false := by
          have h1 : P.other.sendsIn c'.1.1 = true := by
            rw [← hpos_c, ← hsnd]; exact hsnd_sends
          rw [AuthL9.sendsIn_other, Bool.not_eq_true'] at h1
          exact h1
        have hle_other : c'.1.1 ≤ es.g.epoch P.other := by
          rw [← hpos_c, ← hsnd]; exact hle_snd
        have hle_P1 : c'.1.1 ≤ es.g.epoch P + 1 := by
          have hle2 := hs.base.base.epoch_le P.other
          dsimp only at hle2
          rw [Party.other_other] at hle2
          omega
        by_cases hstep : c'.1.1 = es.g.epoch P + 1
        · have heq_other : es.g.epoch P + 1 = es.g.epoch P.other :=
            hs.base.base.epoch_eq_of_deliver_step hmem hsnd (by rw [hct, ← hhdr]; exact hstep)
          obtain ⟨T_t, I_t, hcache, hT_other, hl_msg, hI, hagr⟩ :=
            hs.base.base.cka_step P heq_other
          dsimp only at hcache hT_other hl_msg hI hagr
          have hcT : c'.1.2 = some T_t := by
            rw [hhdr, ← hct, hTcur (by rw [hsnd]; omega), hsnd, hT_other]
          have hcache' : es.h.base.cache c'.1.1 = some (T_t, I_t) := by rwa [hstep, heq_other]
          obtain ⟨hrcvL, hrcvR⟩ :=
            AuthL9.vRecv_new_honest cka prng fs 1 (some (l - 1)) 0 (rec := none)
              hs.base.base hnsend hstep hcT hcache' hI
          dsimp only at hrcvL hrcvR
          dsimp only [scheme]
          rw [hrcvL, StateT.run_bind, vRecv_hooksCKAShifted_run, hrcvR]
          simp only [pure_bind]
          cases hfs : fs.receive (fs.initReceiver (prng.up (es.g.st P).root I_t).2) c'.1 c'.2 with
          | none =>
            simp [ih (some .rejected) hs]
          | some val =>
            rcases val with ⟨v', i', m'⟩
            have hne_ep : (c'.1.1 != r.pos.epoch) = false := by
              rw [bne_eq_false_iff_eq, hpos_c]
            simp only [hne_ep, Bool.or_false]
            by_cases hqep : decide (qep + 1 < c'.1.1) = true
            · simp [hqep, ih (some .rejected) hs]
            · simp only [hqep, Bool.false_eq_true, ↓reduceIte, htriv_eq]
              by_cases htriv : trivB1 (l + 1) es.g ⟨P.other, c'.1.1, i'⟩ = true
              · have hcom := commitE_new_shifted cka prng fs
                  (pos := ⟨P.other, c'.1.1, i'⟩)
                  (prng.up (es.g.st P).root I_t).1
                  (Function.update (es.g.st P).vR c'.1.1 (some v'))
                  hs.toSync9Shifted hstep heq_other T_t (hl_msg (l - 1) rfl)
                have hsync := sync9ShiftedDir2_accept_new hs
                  (pos := ⟨P.other, c'.1.1, i'⟩)
                  (prng.up (es.g.st P).root I_t).1
                  (Function.update (es.g.st P).vR c'.1.1 (some v'))
                  hstep heq_other hnsend T_t hagr
                dsimp only at hcom hsync
                rw [commitE_hooksCKAShifted_zero_eq cka prng fs l ((l - 1) + 3)]
                simp only [htriv, ↓reduceIte, StateT.run_bind, StateT.run_set, pure_bind,
                  StateT.run_pure, simulateQ_bind, hcom, StateT.run_modify,
                  simulateQ_pure]
                exact ih _ hsync
              · simp only [htriv, Bool.false_eq_true, ↓reduceIte]
                by_cases hfull : (c'.1.1 == l + 1) = true
                · simp only [hfull, ↓reduceIte, StateT.run_bind, StateT.run_set,
                    StateT.run_modify, pure_bind, StateT.run_pure, simulateQ_pure]
                  exact ih (some .rejected) (sync9ShiftedDir2_win hs true)
                · simp [hfull, ih (some .rejected) hs]
        · have hle_P : c'.1.1 ≤ es.g.epoch P := by omega
          obtain ⟨hrcvL, hrcvR⟩ :=
            AuthL9.vRecv_same_epoch cka prng fs 1 (some (l - 1)) 0 (rec := none) hs.base.base hnsend hle_P
          dsimp only at hrcvL hrcvR
          dsimp only [scheme]
          rw [hrcvL, StateT.run_bind, vRecv_hooksCKAShifted_run, hrcvR]
          simp only [pure_bind]
          cases hv : (es.g.st P).vR c'.1.1 with
          | none =>
            simp [ih (some .rejected) hs]
          | some v =>
            simp only []
            cases hfs : fs.receive v c'.1 c'.2 with
            | none =>
              simp [ih (some .rejected) hs]
            | some val =>
              rcases val with ⟨v', i', m'⟩
              have hne_ep : (c'.1.1 != r.pos.epoch) = false := by
                rw [bne_eq_false_iff_eq, hpos_c]
              simp only [hne_ep, Bool.or_false]
              by_cases hqep : decide (qep + 1 < c'.1.1) = true
              · simp [hqep, ih (some .rejected) hs]
              · simp only [hqep, Bool.false_eq_true, ↓reduceIte, htriv_eq]
                by_cases htriv : trivB1 (l + 1) es.g ⟨P.other, c'.1.1, i'⟩ = true
                · have hcom := commitE_same_shifted cka prng fs l 0
                    (P := P)
                    (new :=
                      { es.g.st P with vR := Function.update (es.g.st P).vR c'.1.1 (some v') })
                    (pos := ⟨P.other, c'.1.1, i'⟩) (es := es) (sc := sc) rfl
                  have hsync := sync9ShiftedDir2_accept_same hs
                    (Function.update (es.g.st P).vR c'.1.1 (some v'))
                    (pos := ⟨P.other, c'.1.1, i'⟩) hle_P
                  simp only [htriv, ↓reduceIte, StateT.run_bind, StateT.run_set, pure_bind,
                    StateT.run_pure, simulateQ_bind, hcom, StateT.run_modify,
                    simulateQ_pure]
                  exact ih _ hsync
                · simp only [htriv, Bool.false_eq_true, ↓reduceIte]
                  by_cases hfull : (c'.1.1 == l + 1) = true
                  · simp only [hfull, ↓reduceIte, StateT.run_bind, StateT.run_set,
                      StateT.run_modify, pure_bind, StateT.run_pure, simulateQ_pure]
                    exact ih (some .rejected) (sync9ShiftedDir2_win hs true)
                  · simp [hfull, ih (some .rejected) hs]

theorem runLDFShiftedDir2Paper_le_runRDFShiftedDir2Paper_of_sync {α : Type}
    (cka : CKAScheme KC Γ CCoins T I)
    (prng : PRFPRNG KR Sig I K) (fs : FSAEADScheme K SS RS (Header T) M E)
    (lam : I) (qep l : ℕ)
    {oa : AdversaryCompDF (PartyState Γ T Sig SS RS) M CCoins (Header T × E) α}
    (hnbc : AuthL9DFDir2.NoBadCoinsDF oa)
    {s : GameState (PartyState Γ T Sig SS RS) M (Header T × E)}
    {es : EState (PartyState (Option Γ) T Sig SS RS) M (Header T × E) (CKAStateShifted Γ T I)}
    {sc : CKA.GameState Γ T}
    (hs : Sync9ShiftedDir2 cka l s es sc) :
    𝒟[runLDFShiftedDir2Paper cka prng fs lam qep l oa s] {true} ≤
      𝒟[runRDFShiftedDir2Paper cka prng fs qep l oa es sc] {true} := by
  induction hnbc generalizing s es sc with
  | pure a =>
    rw [runLDFShiftedDir2Paper_pure, runRDFShiftedDir2Paper_pure]
    have habort : es.abort = false := hs.base.base.no_abort
    have hwin : s.win = es.g.win := by rw [hs.base.base.s_eq]; rfl
    have hok : authLosingConditionsAvoided 2 (some (l - 1)) (l + 1) s = authLosingConditionsAvoided 2 (some (l - 1)) (l + 1) es.g := by
      rw [hs.base.base.s_eq]; rfl
    dsimp only [authOut, authOKDir2]
    rw [habort, hwin, hok]
    cases es.g.win <;> cases authLosingConditionsAvoided 2 (some (l - 1)) (l + 1) es.g <;>
      cases s.corrs.contains (Party.senderOf (l + 1), l + 1) <;> simp
  | query_bind t k hno_bad _ ih =>
    rcases t with n | (((((⟨P, m, r⟩ | ⟨P, m₀, m₁, r⟩) | ⟨P, c⟩) | ⟨P, c⟩) | P) | ⟨P, c, c'⟩)
    · exact step_coins_DFShiftedDir2Paper cka prng fs lam qep l n k hs @ih
    · have hr : r = none := hno_bad P m r rfl
      subst hr
      exact step_transmit_DFShiftedDir2Paper cka prng fs lam qep l P m k hs @ih
    · exact step_chall_DFShiftedDir2Paper cka prng fs lam qep l P m₀ m₁ r k hs @ih
    · exact step_deliver_DFShiftedDir2Paper cka prng fs lam qep l P c k hs @ih
    · exact step_inject_DFShiftedDir2Paper cka prng fs lam qep l P c k hs @ih
    · exact step_corr_DFShiftedDir2Paper cka prng fs lam qep l P k hs @ih
    · exact step_deliverForge_DFShiftedDir2Paper cka prng fs lam qep l P c c' k hs @ih

omit [DecidableEq I] [SampleableType I] [SampleableType K] in
theorem forgeGameGuessedShiftedDir2Paper_eq_runLDFShiftedDir2Paper (cka : CKAScheme KC Γ CCoins T I)
    (prng : PRFPRNG KR Sig I K) (fs : FSAEADScheme K SS RS (Header T) M E)
    (lam : I) (qep l : ℕ)
    (A : SchemeAdversaryDF Γ T Sig SS RS M CCoins E) :
    forgeGameGuessedShiftedDir2Paper (scheme cka prng fs lam) qep sameHdrScheme l (l + 1) A =
      ($ᵗ KR >>= fun kr => $ᵗ KC >>= fun kc =>
        runLDFShiftedDir2Paper cka prng fs lam qep l A
          (initState (scheme cka prng fs lam) (kr, kc) false)) := by
  unfold forgeGameGuessedShiftedDir2Paper runBaseDFShiftedDir2Paper runLDFShiftedDir2Paper
  simp only [uniformSample, SampleableType.selectElem, seq_eq_bind_map, map_eq_bind_pure_comp,
    Function.comp_apply, pure_bind, bind_assoc]

/-- Shifted-paper Lemma 9 at `Δ = 2`: `forgeGuessedAdvantageShiftedDir2Paper` at `(l, l + 1)`
(`1 ≤ l`) is bounded by the real-world CKA branch (`b = false`) of `redCKAAuthDFShiftedDir2Paper`
at `t_CKA = l + 1` and `Δcka = 1`. -/
theorem lemma9_df_shifted_dir2_paper (cka : CKAScheme KC Γ CCoins T I) (prng : PRFPRNG KR Sig I K)
    (fs : FSAEADScheme K SS RS (Header T) M E) (lam : I) (qep l : ℕ)
    (hc : cka.Correct) (hl : 1 ≤ l)
    (A : SchemeAdversaryDF Γ T Sig SS RS M CCoins E)
    (hnbc : AuthL9DFDir2.NoBadCoinsDF A) :
    forgeGuessedAdvantageShiftedDir2Paper (scheme cka prng fs lam) qep sameHdrScheme l (l + 1) A ≤
      𝒟[CKA.branch cka 1 (l + 1) false
        (redCKAAuthDFShiftedDir2Paper cka prng fs lam qep l (l + 1) A)] {true} := by
  unfold forgeGuessedAdvantageShiftedDir2Paper
  rw [forgeGameGuessedShiftedDir2Paper_eq_runLDFShiftedDir2Paper]
  unfold CKA.branch redCKAAuthDFShiftedDir2Paper authSimDFShiftedDir2Paper
    engRunDFShiftedDir2Paper initCKAShifted
  simp only [hl, ↓reduceIte, liftCShifted, setγPreShifted, StateT.run'_eq,
    StateT.run_bind, StateT.run_lift, StateT.run_modify, StateT.run_pure, pure_bind, bind_assoc,
    simulateQ_bind, simulateQ_pure, AuthL9.simulateQ_sampleT_run, map_bind]
  rw [OracleComp.evalDist_bind_bind_swap ($ᵗ KR) ($ᵗ KC)]
  refine OracleComp.evalDist_bind_apply_mono_of_support _ _ _ (MeasurableSet.singleton true)
    fun kc _ => ?_
  refine OracleComp.evalDist_bind_apply_mono_of_support _ _ _ (MeasurableSet.singleton true)
    fun kr _ => ?_
  have hall : (CKA.initState cka kc false).allowCorr (l + 1) = true :=
    allowCorr_initState_of_one_le cka kc false hl
  have hstA : (CKA.initState cka kc false).st .A = cka.initA kc := rfl
  have hstB : (CKA.initState cka kc false).st .B = cka.initB kc := rfl
  have hγPre_init :
      Function.update
        (Function.update (fun _ : Party => (none : Option Γ)) .A (some (cka.initA kc)))
        .B (some (cka.initB kc)) =
      (fun P => match P with | .A => some (cka.initA kc) | .B => some (cka.initB kc)) := by
    funext P; cases P <;> rfl
  simp only [CKA.corrQuery, AuthL9.simulateQ_query_eq, QueryImpl.add_apply, CKA.oracleImpl,
    CKA.corrImpl, hall, Bool.true_or, ↓reduceIte, StateT.run_bind, StateT.run_get,
    StateT.run_pure, pure_bind, hstA, hstB, hγPre_init]
  refine (runLDFShiftedDir2Paper_le_runRDFShiftedDir2Paper_of_sync cka prng fs lam qep l hnbc
    (sync9ShiftedDir2_init cka prng fs lam hc hl kr kc)).trans ?_
  simp only [runRDFShiftedDir2Paper, bind_pure_comp, map_pure]
  exact le_rfl

end AuthL9ShiftedDir2PaperEnd

/-- Theorem-8 instance for the `Δ = 2` shifted paper game at `l = t - 1`. -/
theorem forgeGuessedAdvantageShiftedDir2Paper_le_reds
    [DecidableEq T] [DecidableEq M] [DecidableEq E] [DecidableEq I] [Inhabited E]
    [SampleableType KR] [SampleableType KC] [SampleableType CCoins] [SampleableType I]
    [SampleableType K]
    (cka : CKAScheme KC Γ CCoins T I) (prng : PRFPRNG KR Sig I K)
    (fs : FSAEADScheme K SS RS (Header T) M E) (lam : I) (qep t q : ℕ)
    (hc : cka.Correct) (ht2 : 2 ≤ t)
    (A : DeliverForge.SchemeAdversaryDF Γ T Sig SS RS M CCoins E)
    (hnbc : AuthL9DFDir2.NoBadCoinsDF A) (hq : DeliverForge.MakesAtMostQueriesDF A q) :
    forgeGuessedAdvantageShiftedDir2Paper (scheme cka prng fs lam) qep
        DeliverForge.sameHdrScheme (t - 1) t A ≤
      CKA.advantage cka 1 (healEpoch (some (t - 2)))
        (redCKAAuthDFShiftedDir2Paper cka prng fs lam qep (t - 1) t A) +
      PRFPRNG.advantage prng
        (redPRNGAuthDFShiftedDir2Paper cka prng fs lam qep (t - 1) t A) +
      ∑ j ∈ Finset.range q,
        FSAEAD.advantage fs
          (redFSAuthDFShiftedDir2Paper cka prng fs lam qep j (t - 1) t A) := by
  rw [CKA.advantage_eq_boolDist, PRFPRNG.advantage_eq_boolDist]
  set cT := 𝒟[CKA.branch cka 1 (healEpoch (some (t - 2))) true
    (redCKAAuthDFShiftedDir2Paper cka prng fs lam qep (t - 1) t A)]
  set cF := 𝒟[CKA.branch cka 1 (healEpoch (some (t - 2))) false
    (redCKAAuthDFShiftedDir2Paper cka prng fs lam qep (t - 1) t A)]
  set pT := 𝒟[PRFPRNG.branch prng true
    (redPRNGAuthDFShiftedDir2Paper cka prng fs lam qep (t - 1) t A)]
  set pF := 𝒟[PRFPRNG.branch prng false
    (redPRNGAuthDFShiftedDir2Paper cka prng fs lam qep (t - 1) t A)]
  have hl1 : 1 ≤ t - 1 := by omega
  have ht_eq : (t - 1) + 1 = t := by omega
  have hheal : healEpoch (some (t - 2)) = (t - 1) + 1 := by
    simp only [healEpoch]; omega
  have hsub : (t - 1) - 1 = t - 2 := by omega
  have h9 : forgeGuessedAdvantageShiftedDir2Paper (scheme cka prng fs lam) qep
      DeliverForge.sameHdrScheme (t - 1) t A ≤ cF {true} := by
    dsimp only [cF]
    rw [hheal, ← ht_eq]
    exact lemma9_df_shifted_dir2_paper cka prng fs lam qep (t - 1) hc hl1 A hnbc
  have h10 : cT {true} ≤ pF {true} := by
    dsimp only [cT, pF]
    rw [hheal]
    exact lemma10_df_shifted_dir2_paper cka prng fs lam qep (t - 1) t hl1 A
  have h11 : pT {true} ≤ ∑ j ∈ Finset.range q,
      FSAEAD.advantage fs (redFSAuthDFShiftedDir2Paper cka prng fs lam qep j (t - 1) t A) :=
    lemma11_df_shifted_dir2_paper cka prng fs lam qep (t - 1) t q A hq
  have hc' : cF {true} ≤ cT {true} + cT.boolDist cF := by
    rw [Measure.boolDist_comm]; exact Measure.apply_true_le_add_boolDist _ _
  have hp' : pF {true} ≤ pT {true} + pT.boolDist pF := by
    rw [Measure.boolDist_comm]; exact Measure.apply_true_le_add_boolDist _ _
  calc forgeGuessedAdvantageShiftedDir2Paper (scheme cka prng fs lam) qep
          DeliverForge.sameHdrScheme (t - 1) t A
      ≤ cF {true} := h9
    _ ≤ cT {true} + cT.boolDist cF := hc'
    _ ≤ (pT {true} + pT.boolDist pF) + cT.boolDist cF := add_le_add (h10.trans hp') le_rfl
    _ ≤ ((∑ j ∈ Finset.range q, FSAEAD.advantage fs
          (redFSAuthDFShiftedDir2Paper cka prng fs lam qep j (t - 1) t A)) + pT.boolDist pF) +
          cT.boolDist cF :=
        add_le_add (add_le_add h11 le_rfl) le_rfl
    _ = _ := by ring

/-- Theorem-8 instance for the `Δ = 2 + 1` shifted paper game at `l = t - 2`. -/
theorem forgeGuessedAdvantageShiftedPaper_le_reds
    [DecidableEq T] [DecidableEq M] [DecidableEq E] [DecidableEq I] [Inhabited E]
    [SampleableType KR] [SampleableType KC] [SampleableType CCoins] [SampleableType I]
    [SampleableType K]
    (cka : CKAScheme KC Γ CCoins T I) (prng : PRFPRNG KR Sig I K)
    (fs : FSAEADScheme K SS RS (Header T) M E) (lam : I) (qep t q : ℕ)
    (hc : cka.Correct) (ht3 : 3 ≤ t)
    (A : DeliverForge.SchemeAdversaryDF Γ T Sig SS RS M CCoins E)
    (hnbc : AuthL9DFDir2.NoBadCoinsDF A)
    (hq : DeliverForge.MakesAtMostQueriesDF A q) :
    forgeGuessedAdvantageShiftedPaper (scheme cka prng fs lam) (2 + 1) qep
        DeliverForge.sameHdrScheme (t - 2) t A ≤
      CKA.advantage cka 1 (healEpoch (some (t - 3)))
        (redCKAAuthDFShiftedPaper cka prng fs lam 1 qep (t - 2) t A) +
      PRFPRNG.advantage prng
        (redPRNGAuthDFShiftedPaper cka prng fs lam 1 qep (t - 2) t A) +
      ∑ j ∈ Finset.range q,
        FSAEAD.advantage fs
          (redFSAuthDFShiftedPaper cka prng fs lam 1 qep j (t - 2) t A) := by
  rw [CKA.advantage_eq_boolDist, PRFPRNG.advantage_eq_boolDist]
  set cT := 𝒟[CKA.branch cka 1 (healEpoch (some (t - 3))) true
    (redCKAAuthDFShiftedPaper cka prng fs lam 1 qep (t - 2) t A)]
  set cF := 𝒟[CKA.branch cka 1 (healEpoch (some (t - 3))) false
    (redCKAAuthDFShiftedPaper cka prng fs lam 1 qep (t - 2) t A)]
  set pT := 𝒟[PRFPRNG.branch prng true
    (redPRNGAuthDFShiftedPaper cka prng fs lam 1 qep (t - 2) t A)]
  set pF := 𝒟[PRFPRNG.branch prng false
    (redPRNGAuthDFShiftedPaper cka prng fs lam 1 qep (t - 2) t A)]
  have hl1 : 1 ≤ t - 2 := by omega
  have hheal : healEpoch (some (t - 3)) = (t - 2) + 1 := by
    simp only [healEpoch]; omega
  have h9 : forgeGuessedAdvantageShiftedPaper (scheme cka prng fs lam) (2 + 1) qep
      DeliverForge.sameHdrScheme (t - 2) t A ≤ cF {true} := by
    dsimp only [cF]
    rw [hheal]
    exact lemma9_df_shifted_paper cka prng fs lam qep (t - 2) t hc hl1 A hnbc
  have h10 : cT {true} ≤ pF {true} := by
    dsimp only [cT, pF]
    rw [hheal]
    exact lemma10_df_shifted_paper cka prng fs lam 1 qep (t - 2) t hl1 A
  have h11 : pT {true} ≤ ∑ j ∈ Finset.range q,
      FSAEAD.advantage fs (redFSAuthDFShiftedPaper cka prng fs lam 1 qep j (t - 2) t A) :=
    lemma11_df_shifted_paper cka prng fs lam 1 qep (t - 2) t q A hq
  have hc' : cF {true} ≤ cT {true} + cT.boolDist cF := by
    rw [Measure.boolDist_comm]; exact Measure.apply_true_le_add_boolDist _ _
  have hp' : pF {true} ≤ pT {true} + pT.boolDist pF := by
    rw [Measure.boolDist_comm]; exact Measure.apply_true_le_add_boolDist _ _
  calc forgeGuessedAdvantageShiftedPaper (scheme cka prng fs lam) (2 + 1) qep
          DeliverForge.sameHdrScheme (t - 2) t A
      ≤ cF {true} := h9
    _ ≤ cT {true} + cT.boolDist cF := hc'
    _ ≤ (pT {true} + pT.boolDist pF) + cT.boolDist cF := add_le_add (h10.trans hp') le_rfl
    _ ≤ ((∑ j ∈ Finset.range q, FSAEAD.advantage fs
          (redFSAuthDFShiftedPaper cka prng fs lam 1 qep j (t - 2) t A)) + pT.boolDist pF) +
          cT.boolDist cF :=
        add_le_add (add_le_add h11 le_rfl) le_rfl
    _ = _ := by ring

section NoBadCoinsSimDFPrimePaper

open CryptoGames.SM CryptoGames.SM.Engine CryptoGames.SM.Thm1 CryptoGames.SM.Thm1L17

variable {St Msg Coins C : Type}

local notation "CompDF" => AdversaryCompDF St Msg Coins C
local notation "RedMDF" => StateT (Mirror Msg C) (AdversaryCompDF St Msg Coins C)

private lemma noBadCoinsDF_stateT_pure_paper {α : Type} (a : α) (s : Mirror Msg C) :
    AuthL9DFDir2.NoBadCoinsDF ((pure a : RedMDF α).run s) :=
  AuthL9DFDir2.NoBadCoinsDF.pure (a, s)

private lemma noBadCoinsDF_stateT_get_paper (s : Mirror Msg C) :
    AuthL9DFDir2.NoBadCoinsDF ((get : RedMDF (Mirror Msg C)).run s) :=
  AuthL9DFDir2.NoBadCoinsDF.pure (s, s)

private lemma noBadCoinsDF_stateT_set_paper (s' s : Mirror Msg C) :
    AuthL9DFDir2.NoBadCoinsDF ((set s' : RedMDF PUnit).run s) := by
  rw [StateT.run_set]
  exact AuthL9DFDir2.NoBadCoinsDF.pure (PUnit.unit, s')

private lemma noBadCoinsDF_stateT_bind_paper {α β : Type} (m : RedMDF α) (k : α → RedMDF β)
    (s : Mirror Msg C) (hm : AuthL9DFDir2.NoBadCoinsDF (m.run s))
    (hk : ∀ a s', AuthL9DFDir2.NoBadCoinsDF ((k a).run s')) :
    AuthL9DFDir2.NoBadCoinsDF ((m >>= k).run s) :=
  hm.bind fun p => hk p.1 p.2

private lemma noBadCoinsDF_stateT_run'_paper {α : Type} (m : RedMDF α) (s : Mirror Msg C)
    (hm : AuthL9DFDir2.NoBadCoinsDF (m.run s)) :
    AuthL9DFDir2.NoBadCoinsDF (m.run' s) := by
  rw [StateT.run'_eq, map_eq_bind_pure_comp]
  exact hm.bind fun p => AuthL9DFDir2.NoBadCoinsDF.pure p.1

private lemma noBadCoinsDF_stateT_lift_query_paper
    (q : (unifSpec + specDF St Msg Coins C).Domain)
    (hq : ∀ P m r, q = Sum.inr (Sum.inl (Sum.inl (Sum.inl (Sum.inl (Sum.inl (P, m, r)))))) →
      r = none)
    (s : Mirror Msg C) :
    AuthL9DFDir2.NoBadCoinsDF
      ((StateT.lift (query (spec := unifSpec + specDF St Msg Coins C) q : CompDF _) :
        RedMDF _).run s) :=
  AuthL9DFDir2.NoBadCoinsDF.query_bind q (fun a => pure (a, s)) hq
    (fun a => AuthL9DFDir2.NoBadCoinsDF.pure (a, s))

private lemma noBadCoinsDF_liftM_probComp_paper {α : Type} (oa : ProbComp α) :
    AuthL9DFDir2.NoBadCoinsDF (liftM oa : AdversaryCompDF St Msg Coins C α) := by
  induction oa using OracleComp.inductionOn with
  | pure a => exact AuthL9DFDir2.NoBadCoinsDF.pure a
  | query_bind t r ih =>
    change AuthL9DFDir2.NoBadCoinsDF
      (query (spec := unifSpec + specDF St Msg Coins C) (Sum.inl t) >>= fun u => liftM (r u))
    exact AuthL9DFDir2.NoBadCoinsDF.query_bind (Sum.inl t) _ (fun _ _ _ hq => nomatch hq) ih

private lemma noBadCoinsDF_simOraclesDF'Paper [DecidableEq C] (Δ qep : ℕ)
    (o : (specDF St Msg Coins C).Domain) (s : Mirror Msg C) :
    AuthL9DFDir2.NoBadCoinsDF
      ((simOraclesDF'Paper (St := St) (Coins := Coins) Δ qep o).run s) := by
  rcases o with (((((⟨P, msg, r⟩ | ⟨P, m₀, m₁, r⟩) | ⟨P, c⟩) | ⟨P, c⟩) | P) | ⟨P, c, c'⟩)
  · change AuthL9DFDir2.NoBadCoinsDF ((simTransmitDF'Paper (St := St) Δ qep (P, msg, r)).run s)
    unfold simTransmitDF'Paper transmitQueryDF
    refine noBadCoinsDF_stateT_bind_paper _ _ s (noBadCoinsDF_stateT_get_paper s) fun s₀ s₂ => ?_
    refine noBadCoinsDF_stateT_bind_paper _ _ s₂
      (noBadCoinsDF_stateT_lift_query_paper _ (fun _ _ _ hq => by cases hq; rfl) s₂)
      fun res s₃ => ?_
    cases res with
    | none => exact noBadCoinsDF_stateT_pure_paper none s₃
    | some c =>
      cases s₀.epMgmt Δ qep P false with
      | none => exact noBadCoinsDF_stateT_pure_paper (some c) s₃
      | some s₁ =>
        exact noBadCoinsDF_stateT_bind_paper _ _ s₃ (noBadCoinsDF_stateT_set_paper _ s₃)
          fun _ s₄ => noBadCoinsDF_stateT_pure_paper (some c) s₄
  · change AuthL9DFDir2.NoBadCoinsDF ((simChallDF'Paper (St := St) Δ qep (P, m₀, m₁, r)).run s)
    unfold simChallDF'Paper transmitQueryDF
    refine noBadCoinsDF_stateT_bind_paper _ _ s (noBadCoinsDF_stateT_get_paper s) fun s₀ s₂ => ?_
    cases s₀.epMgmt Δ qep P false with
    | none => exact noBadCoinsDF_stateT_pure_paper none s₂
    | some s₁ =>
      dsimp only
      split
      · exact noBadCoinsDF_stateT_pure_paper none s₂
      · refine noBadCoinsDF_stateT_bind_paper _ _ s₂
          (noBadCoinsDF_stateT_lift_query_paper _ (fun _ _ _ hq => by cases hq; rfl) s₂)
          fun res s₃ => ?_
        cases res with
        | none => exact noBadCoinsDF_stateT_pure_paper none s₃
        | some c =>
          exact noBadCoinsDF_stateT_bind_paper _ _ s₃ (noBadCoinsDF_stateT_set_paper _ s₃)
            fun _ s₄ => noBadCoinsDF_stateT_pure_paper (some c) s₄
  · change AuthL9DFDir2.NoBadCoinsDF ((simDeliverDF (St := St) (Coins := Coins) (P, c)).run s)
    unfold simDeliverDF deliverQueryDF
    refine noBadCoinsDF_stateT_bind_paper _ _ s (noBadCoinsDF_stateT_get_paper s) fun s₀ s₂ => ?_
    refine noBadCoinsDF_stateT_bind_paper _ _ s₂
      (noBadCoinsDF_stateT_lift_query_paper _ (fun _ _ _ hq => by cases hq) s₂) fun res s₃ => ?_
    cases res with
    | none => exact noBadCoinsDF_stateT_pure_paper none s₃
    | some rr =>
      cases rr with
      | rejected => exact noBadCoinsDF_stateT_pure_paper (some RecvResult.rejected) s₃
      | accepted t' i' m =>
        cases s₀.inTransit P.other c with
        | none => exact noBadCoinsDF_stateT_pure_paper (some (RecvResult.accepted t' i' m)) s₃
        | some r =>
          exact noBadCoinsDF_stateT_bind_paper _ _ s₃ (noBadCoinsDF_stateT_set_paper _ s₃)
            fun _ s₄ => noBadCoinsDF_stateT_pure_paper _ s₄
  · change AuthL9DFDir2.NoBadCoinsDF ((simInjectDF (St := St) (Coins := Coins) (P, c)).run s)
    unfold simInjectDF injectQueryDF
    refine noBadCoinsDF_stateT_bind_paper _ _ s (noBadCoinsDF_stateT_get_paper s) fun _ s₂ => ?_
    refine noBadCoinsDF_stateT_bind_paper _ _ s₂
      (noBadCoinsDF_stateT_lift_query_paper _ (fun _ _ _ hq => by cases hq) s₂) fun res s₃ => ?_
    cases res with
    | none => exact noBadCoinsDF_stateT_pure_paper none s₃
    | some rr =>
      cases rr with
      | rejected => exact noBadCoinsDF_stateT_pure_paper (some RecvResult.rejected) s₃
      | accepted t' i' m =>
        exact noBadCoinsDF_stateT_bind_paper _ _ s₃ (noBadCoinsDF_stateT_set_paper _ s₃)
          fun _ s₄ => noBadCoinsDF_stateT_pure_paper (some (RecvResult.accepted t' i' m)) s₄
  · change AuthL9DFDir2.NoBadCoinsDF
      ((simCorrDFPaper (St := St) (Msg := Msg) (Coins := Coins) (C := C) P).run s)
    unfold simCorrDFPaper corrQueryDF
    refine noBadCoinsDF_stateT_bind_paper _ _ s (noBadCoinsDF_stateT_get_paper s) fun _ s₂ => ?_
    dsimp only
    split
    · exact noBadCoinsDF_stateT_pure_paper none s₂
    · refine noBadCoinsDF_stateT_bind_paper _ _ s₂
        (noBadCoinsDF_stateT_lift_query_paper _ (fun _ _ _ hq => by cases hq) s₂) fun res s₃ => ?_
      split
      · exact noBadCoinsDF_stateT_bind_paper _ _ s₃ (noBadCoinsDF_stateT_set_paper _ s₃)
          fun _ s₄ => noBadCoinsDF_stateT_pure_paper res s₄
      · exact noBadCoinsDF_stateT_pure_paper res s₃
  · change AuthL9DFDir2.NoBadCoinsDF
      ((simDeliverForgeDF (St := St) (Coins := Coins) (P, c, c')).run s)
    unfold simDeliverForgeDF deliverForgeQuery
    refine noBadCoinsDF_stateT_bind_paper _ _ s (noBadCoinsDF_stateT_get_paper s) fun _ s₂ => ?_
    refine noBadCoinsDF_stateT_bind_paper _ _ s₂
      (noBadCoinsDF_stateT_lift_query_paper _ (fun _ _ _ hq => by cases hq) s₂) fun res s₃ => ?_
    cases res with
    | none => exact noBadCoinsDF_stateT_pure_paper none s₃
    | some rr =>
      cases rr with
      | rejected => exact noBadCoinsDF_stateT_pure_paper (some RecvResult.rejected) s₃
      | accepted t' i' m =>
        exact noBadCoinsDF_stateT_bind_paper _ _ s₃ (noBadCoinsDF_stateT_set_paper _ s₃)
          fun _ s₄ => noBadCoinsDF_stateT_pure_paper (some (RecvResult.accepted t' i' m)) s₄

theorem noBadCoinsDF_simulateQ_simImplDF'Paper_run [DecidableEq C] (Δ qep : ℕ) {α : Type}
    (oa : AdversaryCompDF St Msg Coins C α) (m : Mirror Msg C) :
    AuthL9DFDir2.NoBadCoinsDF ((simulateQ (simImplDF'Paper Δ qep) oa).run m) := by
  induction oa using OracleComp.inductionOn generalizing m with
  | pure a =>
    rw [simulateQ_pure]
    exact noBadCoinsDF_stateT_pure_paper a m
  | query_bind t k ih =>
    rw [simulateQ_query_bind]
    refine noBadCoinsDF_stateT_bind_paper _ _ m ?_ fun x m' => ih x m'
    rcases t with n | o
    · exact noBadCoinsDF_stateT_lift_query_paper (.inl n) (fun _ _ _ hq => nomatch hq) m
    · exact noBadCoinsDF_simOraclesDF'Paper Δ qep o m

/-- `challSimDF'Paper Δ qep A` always satisfies `AuthL9DFDir2.NoBadCoinsDF`. -/
theorem noBadCoinsDF_challSimDF'Paper [DecidableEq C] (Δ qep : ℕ)
    (A : AdversaryDF St Msg Coins C) :
    AuthL9DFDir2.NoBadCoinsDF (challSimDF'Paper Δ qep A) :=
  (noBadCoinsDF_liftM_probComp_paper ($ᵗ Bool)).bind fun b =>
    noBadCoinsDF_stateT_run'_paper _ _
      (noBadCoinsDF_simulateQ_simImplDF'Paper_run Δ qep A { st := fun _ => (), b })

end NoBadCoinsSimDFPrimePaper

end CryptoGames.SM.Construction.DeliverForge
