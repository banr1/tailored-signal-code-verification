/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Computational.Proofs.LibsignalCli.MainHaltedKeyInd
public import Computational.Proofs.E2E.BinaryHarnessCostedRedsV1
import VCVio.EvalDist.Monad.Basic

/-!
# Query Bounds for `bhKindRedWithTracked` and `bhKindRedWithHalted`

**Checked by Lean.** Target-level `SignalPqxdh.QueryBounded` bounds (`keyIndReductionBudget S qStart b`)
for `bhKindRedWithTracked` and `bhKindRedWithHalted` on any bounded target-game distinguisher `B_A`.
-/

@[expose] public section

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option maxRecDepth 200000

open scoped ENNReal BigOperators
open OracleComp OracleSpec

namespace Computational.Proofs.LibsignalCli.MainHaltedKindBounds

open CryptoGames.CBC (Plain)
open CryptoGames.LibsignalSession (Crypto GhostState PublicKey)
open CryptoGames.SM (GameState)
open CryptoVerification.LibsignalSpqrV1 (MlKem)
open CryptoVerification.E2E (BHModelInst BhShallowRed Bytes SampledSessionKey bhClassifyTarget
  bhClassifyTargetOnly bhE2EGuard bhFwdU bhLiftP bhTargetGameSpec bhTargetQenc bhTargetRdec
  keyIndReductionBudget)
open Computational.Proofs.LibsignalCli.MainHaltedKeyInd (BHE2EDrvStateTracked
  bhKindHandleWithTracked bhKindRedWithHalted bhKindRedWithTracked)

section KindQueryBoundTracked

variable {τ : Type} (initTrack : SampledSessionKey → τ)
variable {S : SignalPqxdh.Setup} {ℓ : ℕ}
variable (smImpl : BHModelInst S ℓ →
  QueryImpl (CryptoGames.SM.spec (GhostState Bytes) (Plain ℓ) (BitVec 512) Bytes)
    (StateT (GameState (GhostState Bytes) (Plain ℓ) Bytes) (StateT τ ProbComp)))
variable (P : SignalPqxdh.Primitives)
variable (ki : QueryImpl (SignalPqxdh.keyIndSpec S) (StateT (SignalPqxdh.KeyIndState S) ProbComp))
variable (C : Crypto) (K : MlKem)

private theorem isQueryBoundP_bhFwdU_ki
    {P_ki : (unifSpec + SignalPqxdh.keyIndSpec S).Domain → Prop} [DecidablePred P_ki]
    (hInl : ∀ n, ¬ P_ki (.inl n)) (n : ℕ) :
    (bhFwdU (G := SignalPqxdh.keyIndSpec S) n).IsQueryBoundP P_ki 0 :=
  (isQueryBoundP_query_iff (spec := unifSpec + SignalPqxdh.keyIndSpec S)
    P_ki (Sum.inl n) 0).2 (fun h => False.elim (hInl n h))

private theorem isQueryBoundP_bhLiftP_ki {α : Type}
    {P_ki : (unifSpec + SignalPqxdh.keyIndSpec S).Domain → Prop} [DecidablePred P_ki]
    (hInl : ∀ n, ¬ P_ki (.inl n)) (p : ProbComp α) :
    (bhLiftP (G := SignalPqxdh.keyIndSpec S) p).IsQueryBoundP P_ki 0 := by
  unfold bhLiftP
  induction p using OracleComp.inductionOn with
  | pure a => simp [simulateQ_pure]
  | query_bind n mx ih =>
    rw [simulateQ_query_bind]
    exact (isQueryBoundP_bind (isQueryBoundP_bhFwdU_ki hInl n)
      (fun u _ => ih u)).mono (by omega)

private theorem isQueryBoundP_ki_query_zero
    {P_ki : (unifSpec + SignalPqxdh.keyIndSpec S).Domain → Prop} [DecidablePred P_ki]
    {kq : SignalPqxdh.KeyIndQuery S} (hnot : ¬ P_ki (.inr kq)) :
    (liftM ((unifSpec + SignalPqxdh.keyIndSpec S).query (.inr kq)) :
      OracleComp (unifSpec + SignalPqxdh.keyIndSpec S) _).IsQueryBoundP P_ki 0 :=
  (isQueryBoundP_query_iff (spec := unifSpec + SignalPqxdh.keyIndSpec S)
    P_ki (Sum.inr kq) 0).2 (fun h => False.elim (hnot h))

private theorem isQueryBoundP_ki_query_one
    {P_ki : (unifSpec + SignalPqxdh.keyIndSpec S).Domain → Prop} [DecidablePred P_ki]
    (kq : SignalPqxdh.KeyIndQuery S) :
    (liftM ((unifSpec + SignalPqxdh.keyIndSpec S).query (.inr kq)) :
      OracleComp (unifSpec + SignalPqxdh.keyIndSpec S) _).IsQueryBoundP P_ki 1 :=
  (isQueryBoundP_query_iff (spec := unifSpec + SignalPqxdh.keyIndSpec S)
    P_ki (Sum.inr kq) 1).2 (fun _ => Nat.zero_lt_one)

private theorem isQueryBoundP_bhKindHandleWithTracked_subpred
    {P_ki : (unifSpec + SignalPqxdh.keyIndSpec S).Domain → Prop} [DecidablePred P_ki]
    (hInl : ∀ n, ¬ P_ki (.inl n))
    (hTest : ∀ sid, ¬ P_ki (.inr (.testSession sid)))
    (hRev : ∀ u j, ¬ P_ki (.inr (.revealSpkSk u j)))
    (pKi : SignalPqxdh.KeyIndQuery S → Bool)
    (hSub : ∀ kq, P_ki (.inr kq) → pKi kq = true)
    (s : BHE2EDrvStateTracked τ S ℓ) (t : (bhTargetGameSpec S ℓ (BitVec 512)).Domain) :
    (bhKindHandleWithTracked initTrack smImpl P ki C K s (bhTargetQenc t)).IsQueryBoundP
      P_ki (if bhClassifyTargetOnly pKi (fun _ => false) (fun _ => false) t then 1 else 0) := by
  rcases t with (kq | cq) | ⟨i, sq⟩
  · simp only [bhClassifyTargetOnly, bhTargetQenc, bhKindHandleWithTracked]
    by_cases hp : pKi kq = true
    · simp only [hp, ↓reduceIte]
      split_ifs
      · simpa only [Nat.add_zero] using
          isQueryBoundP_bind (isQueryBoundP_ki_query_one kq)
            (fun _ _ => isQueryBoundP_pure P_ki _ 0)
      · exact isQueryBoundP_pure P_ki _ 1
    · simp only [hp, Bool.false_eq_true, ↓reduceIte]
      have hnot : ¬ P_ki (.inr kq) := fun h => by simp [hSub kq h] at hp
      split_ifs
      · simpa only [Nat.add_zero] using
          isQueryBoundP_bind (isQueryBoundP_ki_query_zero hnot)
            (fun _ _ => isQueryBoundP_pure P_ki _ 0)
      · exact isQueryBoundP_pure P_ki _ 0
  · rcases cq with ⟨sid⟩
    simp only [bhClassifyTargetOnly, Bool.false_eq_true, ↓reduceIte, bhTargetQenc,
      bhKindHandleWithTracked]
    cases (bhE2EGuard s.1 sid).map (fun x => x.2.2) with
    | none => exact isQueryBoundP_pure P_ki _ 0
    | some uj =>
      rcases uj with ⟨u, j⟩
      dsimp only
      exact (isQueryBoundP_bind (isQueryBoundP_ki_query_zero (hTest sid)) (fun _ _ =>
        isQueryBoundP_bind (isQueryBoundP_ki_query_zero (hRev u j)) (fun _ _ =>
          isQueryBoundP_bind (isQueryBoundP_bhLiftP_ki hInl _) (fun _ _ =>
            isQueryBoundP_pure P_ki _ 0)))).mono (by omega)
  · simp only [bhClassifyTargetOnly, Bool.false_eq_true, ↓reduceIte, bhTargetQenc,
      bhKindHandleWithTracked]
    simpa only [Nat.add_zero] using
      isQueryBoundP_bind (isQueryBoundP_bhLiftP_ki hInl _)
        (fun _ _ => isQueryBoundP_pure P_ki _ 0)

private theorem isQueryBoundP_bhKindRedWithTracked_init
    {P_ki : (unifSpec + SignalPqxdh.keyIndSpec S).Domain → Prop} [DecidablePred P_ki]
    (hInl : ∀ n, ¬ P_ki (.inl n)) :
    ((bhKindRedWithTracked initTrack smImpl P ki C K).init ()).IsQueryBoundP P_ki 0 := by
  dsimp only [bhKindRedWithTracked]
  simpa only [Nat.add_zero] using
    isQueryBoundP_bind (isQueryBoundP_bhLiftP_ki hInl _)
      (fun _ _ => isQueryBoundP_pure P_ki _ 0)

private theorem simulateQ_run_StateT_of_step_le
    {ι κ : Type} {G : OracleSpec κ} {T : OracleSpec ι} {σ α : Type}
    {P_src : κ → Prop} [DecidablePred P_src] {P_tgt : ι → Prop} [DecidablePred P_tgt]
    {so : QueryImpl G (StateT σ (OracleComp T))}
    (hstep : ∀ q s, ((so q).run s).IsQueryBoundP P_tgt (if P_src q then 1 else 0))
    {oa : OracleComp G α} {n : ℕ} (hB : oa.IsQueryBoundP P_src n) (s : σ) :
    ((simulateQ so oa).run s).IsQueryBoundP P_tgt n := by
  induction oa using OracleComp.inductionOn generalizing n s with
  | pure _ => simp [simulateQ_pure]
  | query_bind q mx ih =>
    rw [isQueryBoundP_query_bind_iff] at hB
    rw [simulateQ_query_bind, StateT.run_bind]
    by_cases hp : P_src q
    · have hpos : 0 < n := hB.1.resolve_left (not_not.mpr hp)
      have hq : ((so q).run s).IsQueryBoundP P_tgt 1 := by simpa [hp] using hstep q s
      exact (isQueryBoundP_bind hq fun y _ =>
        ih y.1 (by simpa [hp] using hB.2 y.1) y.2).mono (by omega)
    · have hq : ((so q).run s).IsQueryBoundP P_tgt 0 := by simpa [hp] using hstep q s
      exact (isQueryBoundP_bind hq fun y _ =>
        ih y.1 (by simpa [hp] using hB.2 y.1) y.2).mono (by omega)

private theorem isQueryBoundP_bhKindRedWithTracked_eval_subpred
    {P_ki : (unifSpec + SignalPqxdh.keyIndSpec S).Domain → Prop} [DecidablePred P_ki]
    (hInl : ∀ n, ¬ P_ki (.inl n))
    (hTest : ∀ sid, ¬ P_ki (.inr (.testSession sid)))
    (hRev : ∀ u j, ¬ P_ki (.inr (.revealSpkSk u j)))
    (pKi : SignalPqxdh.KeyIndQuery S → Bool)
    (hSub : ∀ kq, P_ki (.inr kq) → pKi kq = true)
    (B_A : OracleComp (unifSpec + bhTargetGameSpec S ℓ (BitVec 512)) Bool) (n : ℕ)
    (hB : B_A.IsQueryBoundP
      (fun q => bhClassifyTarget pKi (fun _ => false) (fun _ => false) q = true) n) :
    ((bhKindRedWithTracked initTrack smImpl P ki C K).eval (fun _ => B_A) ()).IsQueryBoundP P_ki n := by
  have hstep : ∀ (q : (unifSpec + bhTargetGameSpec S ℓ (BitVec 512)).Domain)
      (s : BHE2EDrvStateTracked τ S ℓ),
      (((bhKindRedWithTracked initTrack smImpl P ki C K).impl q).run s).IsQueryBoundP
        P_ki (if bhClassifyTarget pKi (fun _ => false) (fun _ => false) q = true then 1 else 0) := by
    intro q s
    cases q with
    | inl m =>
      show (bhFwdU (G := SignalPqxdh.keyIndSpec S) m >>= fun a => pure (a, s)).IsQueryBoundP P_ki 0
      exact isQueryBoundP_bind (n := 0) (m := 0)
        (isQueryBoundP_bhFwdU_ki hInl m)
        (fun a _ => isQueryBoundP_pure P_ki (a, s) 0)
    | inr t =>
      show (bhKindHandleWithTracked initTrack smImpl P ki C K s (bhTargetQenc t) >>=
          fun p => pure (bhTargetRdec t p.1, p.2)).IsQueryBoundP
        P_ki (if bhClassifyTargetOnly pKi (fun _ => false) (fun _ => false) t = true then 1 else 0)
      simpa only [Nat.add_zero] using isQueryBoundP_bind
        (isQueryBoundP_bhKindHandleWithTracked_subpred initTrack smImpl P ki C K
          hInl hTest hRev pKi hSub s t)
        (fun p _ => isQueryBoundP_pure P_ki (bhTargetRdec t p.1, p.2) 0)
  have hsim := simulateQ_run_StateT_of_step_le hstep hB
  have hinit := isQueryBoundP_bhKindRedWithTracked_init initTrack smImpl P ki C K hInl
  have hfin : ∀ s' b,
      ((bhKindRedWithTracked initTrack smImpl P ki C K).finish s' b).IsQueryBoundP P_ki 0 := by
    intro s' b; dsimp only [bhKindRedWithTracked]; exact isQueryBoundP_pure P_ki _ 0
  unfold BhShallowRed.eval
  exact (isQueryBoundP_bind hinit (fun ⟨_, s⟩ _ =>
    isQueryBoundP_bind (hsim s) (fun ⟨b, s'⟩ _ => hfin s' b))).mono (by omega)

private theorem isQueryBoundP_bhKindHandleWithTracked_ki_p
    {P_ki : (unifSpec + SignalPqxdh.keyIndSpec S).Domain → Prop} [DecidablePred P_ki]
    (pKi : SignalPqxdh.KeyIndQuery S → Bool)
    (hSub : ∀ kq, P_ki (.inr kq) → pKi kq = true)
    (s : BHE2EDrvStateTracked τ S ℓ) (kq : SignalPqxdh.KeyIndQuery S) :
    (bhKindHandleWithTracked initTrack smImpl P ki C K s (bhTargetQenc (.inl (.inl kq)))).IsQueryBoundP
      P_ki (if pKi kq then 1 else 0) := by
  dsimp only [bhTargetQenc, bhKindHandleWithTracked]
  by_cases hp : pKi kq = true
  · simp only [hp, ↓reduceIte]
    split_ifs
    · simpa only [Nat.add_zero] using
        isQueryBoundP_bind (isQueryBoundP_ki_query_one (P_ki := P_ki) kq)
          (fun _ _ => isQueryBoundP_pure P_ki _ 0)
    · exact isQueryBoundP_pure P_ki _ 1
  · simp only [hp, Bool.false_eq_true, ↓reduceIte]
    have hnot : ¬ P_ki (.inr kq) := fun h => hp (hSub kq h)
    split_ifs
    · simpa only [Nat.add_zero] using
        isQueryBoundP_bind (isQueryBoundP_ki_query_zero hnot)
          (fun _ _ => isQueryBoundP_pure P_ki _ 0)
    · exact isQueryBoundP_pure P_ki _ 0

private theorem isQueryBoundP_bhKindHandleWithTracked_ctl_two
    {P_ki : (unifSpec + SignalPqxdh.keyIndSpec S).Domain → Prop} [DecidablePred P_ki]
    (hInl : ∀ n : ℕ, ¬ P_ki (.inl n))
    (s : BHE2EDrvStateTracked τ S ℓ) (sid : SignalPqxdh.SessionId S) :
    (bhKindHandleWithTracked initTrack smImpl P ki C K s
      (bhTargetQenc (.inl (.inr (.startDR sid))))).IsQueryBoundP
      P_ki 2 := by
  dsimp only [bhTargetQenc, bhKindHandleWithTracked]
  cases (bhE2EGuard s.1 sid).map (fun x => x.2.2) with
  | none => exact isQueryBoundP_pure P_ki _ 2
  | some uj =>
    rcases uj with ⟨u, j⟩
    dsimp only
    exact (isQueryBoundP_bind (isQueryBoundP_ki_query_one (P_ki := P_ki) (.testSession sid)) (fun _ _ =>
      isQueryBoundP_bind (isQueryBoundP_ki_query_one (P_ki := P_ki) (.revealSpkSk u j)) (fun _ _ =>
        isQueryBoundP_bind (isQueryBoundP_bhLiftP_ki hInl _) (fun _ _ =>
          isQueryBoundP_pure P_ki _ 0)))).mono (by omega)

private theorem isQueryBoundP_bhKindHandleWithTracked_sm_zero
    {P_ki : (unifSpec + SignalPqxdh.keyIndSpec S).Domain → Prop} [DecidablePred P_ki]
    (hInl : ∀ n : ℕ, ¬ P_ki (.inl n))
    (s : BHE2EDrvStateTracked τ S ℓ) (i : ℕ)
    (sq : (CryptoGames.SM.spec (GhostState Bytes) (Plain ℓ) (BitVec 512) Bytes).Domain) :
    (bhKindHandleWithTracked initTrack smImpl P ki C K s (bhTargetQenc (.inr ⟨i, sq⟩))).IsQueryBoundP
      P_ki 0 := by
  dsimp only [bhTargetQenc, bhKindHandleWithTracked]
  simpa only [Nat.add_zero] using
    isQueryBoundP_bind (isQueryBoundP_bhLiftP_ki hInl _)
      (fun _ _ => isQueryBoundP_pure P_ki _ 0)

private theorem isQueryBoundP_simulateQ_bhKindRedWithTracked_two
    {P_ki : (unifSpec + SignalPqxdh.keyIndSpec S).Domain → Prop} [DecidablePred P_ki]
    (hInl : ∀ n : ℕ, ¬ P_ki (.inl n))
    (pKi : SignalPqxdh.KeyIndQuery S → Bool)
    (hSub : ∀ kq, P_ki (.inr kq) → pKi kq = true)
    {α : Type} (oa : OracleComp (unifSpec + bhTargetGameSpec S ℓ (BitVec 512)) α)
    (s : BHE2EDrvStateTracked τ S ℓ) (n₁ n₂ : ℕ)
    (h₁ : oa.IsQueryBoundP
      (fun q => bhClassifyTarget pKi (fun _ => false) (fun _ => false) q = true) n₁)
    (h₂ : oa.IsQueryBoundP
      (fun q => bhClassifyTarget (fun _ => false) (fun _ => true) (fun _ => false) q = true) n₂) :
    ((simulateQ (bhKindRedWithTracked initTrack smImpl P ki C K).impl oa).run s).IsQueryBoundP
      P_ki (n₁ + 2 * n₂) := by
  induction oa using OracleComp.inductionOn generalizing s n₁ n₂ with
  | pure a => simp [simulateQ_pure, StateT.run_pure]
  | query_bind q mx ih =>
    rw [isQueryBoundP_query_bind_iff] at h₁ h₂
    rw [simulateQ_query_bind, StateT.run_bind]
    rcases q with m | ((kq | cq) | ⟨i, sq⟩)
    · have hstep :
          (((bhKindRedWithTracked initTrack smImpl P ki C K).impl (.inl m)).run s).IsQueryBoundP
            P_ki 0 :=
        isQueryBoundP_bind (n := 0) (m := 0) (isQueryBoundP_bhFwdU_ki hInl m)
          (fun a _ => isQueryBoundP_pure P_ki (a, s) 0)
      have hcont : ∀ y ∈ support
          (((bhKindRedWithTracked initTrack smImpl P ki C K).impl (.inl m)).run s),
          ((simulateQ (bhKindRedWithTracked initTrack smImpl P ki C K).impl (mx y.1)).run y.2).IsQueryBoundP
            P_ki (n₁ + 2 * n₂) :=
        fun y _ => ih y.1 y.2 n₁ n₂
          ((h₁.2 y.1).mono (by simp [bhClassifyTarget]))
          ((h₂.2 y.1).mono (by simp [bhClassifyTarget]))
      exact (isQueryBoundP_bind hstep hcont).mono (by omega)
    · by_cases hp : pKi kq = true
      · have hn₁ : 0 < n₁ := h₁.1.resolve_left (by simp [bhClassifyTarget, bhClassifyTargetOnly, hp])
        have hstep :
            (((bhKindRedWithTracked initTrack smImpl P ki C K).impl
              (.inr (.inl (.inl kq)))).run s).IsQueryBoundP P_ki 1 := by
          show (bhKindHandleWithTracked initTrack smImpl P ki C K s
              (bhTargetQenc (.inl (.inl kq))) >>=
              fun p => pure (bhTargetRdec (.inl (.inl kq)) p.1, p.2)).IsQueryBoundP P_ki 1
          have hk :
              (bhKindHandleWithTracked initTrack smImpl P ki C K s
                (bhTargetQenc (.inl (.inl kq)))).IsQueryBoundP P_ki 1 := by
            simpa [hp] using
              isQueryBoundP_bhKindHandleWithTracked_ki_p initTrack smImpl P ki C K pKi hSub s kq
          simpa only [Nat.add_zero] using
            isQueryBoundP_bind hk
              (fun p _ => isQueryBoundP_pure P_ki (bhTargetRdec (.inl (.inl kq)) p.1, p.2) 0)
        have hcont : ∀ y ∈ support
            (((bhKindRedWithTracked initTrack smImpl P ki C K).impl (.inr (.inl (.inl kq)))).run s),
            ((simulateQ (bhKindRedWithTracked initTrack smImpl P ki C K).impl (mx y.1)).run y.2).IsQueryBoundP
              P_ki ((n₁ - 1) + 2 * n₂) :=
          fun y _ => ih y.1 y.2 (n₁ - 1) n₂
            ((h₁.2 y.1).mono (by simp [bhClassifyTarget, bhClassifyTargetOnly, hp]))
            ((h₂.2 y.1).mono (by simp [bhClassifyTarget, bhClassifyTargetOnly]))
        exact (isQueryBoundP_bind hstep hcont).mono (by omega)
      · have hstep :
            (((bhKindRedWithTracked initTrack smImpl P ki C K).impl
              (.inr (.inl (.inl kq)))).run s).IsQueryBoundP P_ki 0 := by
          show (bhKindHandleWithTracked initTrack smImpl P ki C K s
              (bhTargetQenc (.inl (.inl kq))) >>=
              fun p => pure (bhTargetRdec (.inl (.inl kq)) p.1, p.2)).IsQueryBoundP P_ki 0
          have hk :
              (bhKindHandleWithTracked initTrack smImpl P ki C K s
                (bhTargetQenc (.inl (.inl kq)))).IsQueryBoundP P_ki 0 := by
            simpa [hp] using
              isQueryBoundP_bhKindHandleWithTracked_ki_p initTrack smImpl P ki C K pKi hSub s kq
          simpa only [Nat.add_zero] using
            isQueryBoundP_bind hk
              (fun p _ => isQueryBoundP_pure P_ki (bhTargetRdec (.inl (.inl kq)) p.1, p.2) 0)
        have hcont : ∀ y ∈ support
            (((bhKindRedWithTracked initTrack smImpl P ki C K).impl (.inr (.inl (.inl kq)))).run s),
            ((simulateQ (bhKindRedWithTracked initTrack smImpl P ki C K).impl (mx y.1)).run y.2).IsQueryBoundP
              P_ki (n₁ + 2 * n₂) :=
          fun y _ => ih y.1 y.2 n₁ n₂
            ((h₁.2 y.1).mono (by simp [bhClassifyTarget, bhClassifyTargetOnly, hp]))
            ((h₂.2 y.1).mono (by simp [bhClassifyTarget, bhClassifyTargetOnly]))
        exact (isQueryBoundP_bind hstep hcont).mono (by omega)
    · rcases cq with ⟨sid⟩
      have hn₂ : 0 < n₂ := h₂.1.resolve_left (by simp [bhClassifyTarget, bhClassifyTargetOnly])
      have hstep :
          (((bhKindRedWithTracked initTrack smImpl P ki C K).impl
            (.inr (.inl (.inr (.startDR sid))))).run s).IsQueryBoundP P_ki 2 := by
        show (bhKindHandleWithTracked initTrack smImpl P ki C K s
            (bhTargetQenc (.inl (.inr (.startDR sid)))) >>=
            fun p => pure (bhTargetRdec (.inl (.inr (.startDR sid))) p.1, p.2)).IsQueryBoundP
          P_ki 2
        simpa only [Nat.add_zero] using
          isQueryBoundP_bind (isQueryBoundP_bhKindHandleWithTracked_ctl_two
              initTrack smImpl P ki C K hInl s sid)
            (fun p _ => isQueryBoundP_pure P_ki
              (bhTargetRdec (.inl (.inr (.startDR sid))) p.1, p.2) 0)
      have hcont : ∀ y ∈ support
          (((bhKindRedWithTracked initTrack smImpl P ki C K).impl
            (.inr (.inl (.inr (.startDR sid))))).run s),
          ((simulateQ (bhKindRedWithTracked initTrack smImpl P ki C K).impl (mx y.1)).run y.2).IsQueryBoundP
            P_ki (n₁ + 2 * (n₂ - 1)) :=
        fun y _ => ih y.1 y.2 n₁ (n₂ - 1)
          ((h₁.2 y.1).mono (by simp [bhClassifyTarget, bhClassifyTargetOnly]))
          ((h₂.2 y.1).mono (by simp [bhClassifyTarget, bhClassifyTargetOnly]))
      exact (isQueryBoundP_bind hstep hcont).mono (by omega)
    · have hstep :
          (((bhKindRedWithTracked initTrack smImpl P ki C K).impl
            (.inr (.inr ⟨i, sq⟩))).run s).IsQueryBoundP P_ki 0 := by
        show (bhKindHandleWithTracked initTrack smImpl P ki C K s
            (bhTargetQenc (.inr ⟨i, sq⟩)) >>=
            fun p => pure (bhTargetRdec (.inr ⟨i, sq⟩) p.1, p.2)).IsQueryBoundP P_ki 0
        simpa only [Nat.add_zero] using
          isQueryBoundP_bind (isQueryBoundP_bhKindHandleWithTracked_sm_zero
              initTrack smImpl P ki C K hInl s i sq)
            (fun p _ => isQueryBoundP_pure P_ki (bhTargetRdec (.inr ⟨i, sq⟩) p.1, p.2) 0)
      have hcont : ∀ y ∈ support
          (((bhKindRedWithTracked initTrack smImpl P ki C K).impl (.inr (.inr ⟨i, sq⟩))).run s),
          ((simulateQ (bhKindRedWithTracked initTrack smImpl P ki C K).impl (mx y.1)).run y.2).IsQueryBoundP
            P_ki (n₁ + 2 * n₂) :=
        fun y _ => ih y.1 y.2 n₁ n₂
          ((h₁.2 y.1).mono (by simp [bhClassifyTarget, bhClassifyTargetOnly]))
          ((h₂.2 y.1).mono (by simp [bhClassifyTarget, bhClassifyTargetOnly]))
      exact (isQueryBoundP_bind hstep hcont).mono (by omega)

/-- Target-level `KeyInd` query bound for `bhKindRedWithTracked` on an arbitrary `B_A`. -/
theorem bhKindRedWithTracked_queryBounded_of_B
    (B_A : OracleComp (unifSpec + bhTargetGameSpec S ℓ (BitVec 512)) Bool)
    (b : SignalPqxdh.QueryBudget) (qStart : ℕ)
    (hRo : B_A.IsQueryBoundP
      (fun q => bhClassifyTarget (fun kq => kq matches .roQuery _) (fun _ => false) (fun _ => false) q = true)
      b.q_ro)
    (hSend : B_A.IsQueryBoundP
      (fun q => bhClassifyTarget
        (fun kq => kq matches .initiateOPK .. || kq matches .initiateNoOPK ..)
        (fun _ => false) (fun _ => false) q = true)
      S.N_send_tot)
    (hRecv : B_A.IsQueryBoundP
      (fun q => bhClassifyTarget
        (fun kq => kq matches .acceptOPK .. || kq matches .acceptNoOPK ..)
        (fun _ => false) (fun _ => false) q = true)
      S.N_recv_tot)
    (hTot : B_A.IsQueryBoundP
      (fun q => bhClassifyTarget (fun _ => true) (fun _ => false) (fun _ => false) q = true)
      b.q_total)
    (hOn : B_A.IsQueryBoundP
      (fun q => bhClassifyTarget
        (fun kq => !(kq matches .roQuery _)) (fun _ => false) (fun _ => false) q = true)
      b.q_on)
    (hCtlSend : B_A.IsQueryBoundP
      (fun q => bhClassifyTarget (fun _ => false) (fun _ => true) (fun _ => false) q = true)
      S.N_send_tot)
    (hCtlStart : B_A.IsQueryBoundP
      (fun q => bhClassifyTarget (fun _ => false) (fun _ => true) (fun _ => false) q = true)
      qStart) :
    let advK : SignalPqxdh.KeyIndAdversary S :=
      ⟨(bhKindRedWithTracked initTrack smImpl P ki C K).eval (fun _ => B_A) ()⟩
    SignalPqxdh.QueryBounded advK (keyIndReductionBudget S qStart b) := by
  intro advK
  have hCtlMin : B_A.IsQueryBoundP
      (fun q => bhClassifyTarget (fun _ => false) (fun _ => true) (fun _ => false) q = true)
      (min qStart S.N_send_tot) := by
    rcases le_total qStart S.N_send_tot with h | h
    · simpa [Nat.min_eq_left h] using hCtlStart
    · simpa [Nat.min_eq_right h] using hCtlSend
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · exact isQueryBoundP_bhKindRedWithTracked_eval_subpred initTrack smImpl P ki C K
      (by intro n; simp [SignalPqxdh.isKeyIndRoQuery])
      (by intro sid; simp [SignalPqxdh.isKeyIndRoQuery])
      (by intro u j; simp [SignalPqxdh.isKeyIndRoQuery])
      (fun kq => kq matches .roQuery _)
      (by intro kq h; cases kq <;> first | rfl | exact False.elim h)
      B_A b.q_ro hRo
  · exact isQueryBoundP_bhKindRedWithTracked_eval_subpred initTrack smImpl P ki C K
      (by intro n; simp [SignalPqxdh.isKeyIndSendQuery])
      (by intro sid; simp [SignalPqxdh.isKeyIndSendQuery])
      (by intro u j; simp [SignalPqxdh.isKeyIndSendQuery])
      (fun kq => kq matches .initiateOPK .. || kq matches .initiateNoOPK ..)
      (by intro kq h; cases kq <;> first | rfl | exact False.elim h)
      B_A S.N_send_tot hSend
  · exact isQueryBoundP_bhKindRedWithTracked_eval_subpred initTrack smImpl P ki C K
      (by intro n; simp [SignalPqxdh.isKeyIndRecvQuery])
      (by intro sid; simp [SignalPqxdh.isKeyIndRecvQuery])
      (by intro u j; simp [SignalPqxdh.isKeyIndRecvQuery])
      (fun kq => kq matches .acceptOPK .. || kq matches .acceptNoOPK ..)
      (by intro kq h; cases kq <;> first | rfl | exact False.elim h)
      B_A S.N_recv_tot hRecv
  · let P_game : (unifSpec + SignalPqxdh.keyIndSpec S).Domain → Prop :=
      fun q => SignalPqxdh.isGameQuery q = true
    have hInl : ∀ n : ℕ, ¬ P_game (.inl n) := by intro n; simp [P_game, SignalPqxdh.isGameQuery]
    have hinit := isQueryBoundP_bhKindRedWithTracked_init initTrack smImpl P ki C K hInl
    have hfin : ∀ s' b_out,
        ((bhKindRedWithTracked initTrack smImpl P ki C K).finish s' b_out).IsQueryBoundP P_game 0 := by
      intro s' b_out; dsimp only [bhKindRedWithTracked]; exact isQueryBoundP_pure P_game _ 0
    show ((bhKindRedWithTracked initTrack smImpl P ki C K).eval (fun _ => B_A) ()).IsQueryBoundP
      P_game (b.q_total + 2 * min qStart S.N_send_tot)
    unfold BhShallowRed.eval
    exact (isQueryBoundP_bind hinit (fun ⟨_, s⟩ _ =>
      isQueryBoundP_bind
        (isQueryBoundP_simulateQ_bhKindRedWithTracked_two initTrack smImpl P ki C K hInl
          (fun _ => true) (by intro _ _; rfl) B_A s b.q_total (min qStart S.N_send_tot) hTot hCtlMin)
        (fun ⟨b_out, s'⟩ _ => hfin s' b_out))).mono (by omega)
  · let P_on : (unifSpec + SignalPqxdh.keyIndSpec S).Domain → Prop :=
      SignalPqxdh.isKeyIndOnlineQuery
    have hInl : ∀ n : ℕ, ¬ P_on (.inl n) := by intro n; simp [P_on, SignalPqxdh.isKeyIndOnlineQuery]
    have hinit := isQueryBoundP_bhKindRedWithTracked_init initTrack smImpl P ki C K hInl
    have hfin : ∀ s' b_out,
        ((bhKindRedWithTracked initTrack smImpl P ki C K).finish s' b_out).IsQueryBoundP P_on 0 := by
      intro s' b_out; dsimp only [bhKindRedWithTracked]; exact isQueryBoundP_pure P_on _ 0
    show ((bhKindRedWithTracked initTrack smImpl P ki C K).eval (fun _ => B_A) ()).IsQueryBoundP
      P_on (b.q_on + 2 * min qStart S.N_send_tot)
    unfold BhShallowRed.eval
    exact (isQueryBoundP_bind hinit (fun ⟨_, s⟩ _ =>
      isQueryBoundP_bind
        (isQueryBoundP_simulateQ_bhKindRedWithTracked_two initTrack smImpl P ki C K hInl
          (fun kq => !(kq matches .roQuery _))
          (by intro kq h; cases kq <;> first | rfl | exact False.elim h)
          B_A s b.q_on (min qStart S.N_send_tot) hOn hCtlMin)
        (fun ⟨b_out, s'⟩ _ => hfin s' b_out))).mono (by omega)

end KindQueryBoundTracked

/-- Target-level `KeyInd` query bound for `bhKindRedWithHalted` on an arbitrary `B_A`. -/
theorem bhKindRedWithHalted_queryBounded_of_B {S : SignalPqxdh.Setup} {ℓ : ℕ} {Pt : Type}
    (badLog : List (BitVec 512) → Bool)
    (P : SignalPqxdh.Primitives)
    (ki : QueryImpl (SignalPqxdh.keyIndSpec S) (StateT (SignalPqxdh.KeyIndState S) ProbComp))
    (C : Crypto) (K : MlKem) (qep : ℕ)
    (decT : PublicKey → Option Pt) (encT : Pt → PublicKey)
    (B_A : OracleComp (unifSpec + bhTargetGameSpec S ℓ (BitVec 512)) Bool)
    (b : SignalPqxdh.QueryBudget) (qStart : ℕ)
    (hRo : B_A.IsQueryBoundP
      (fun q => bhClassifyTarget (fun kq => kq matches .roQuery _) (fun _ => false) (fun _ => false) q = true)
      b.q_ro)
    (hSend : B_A.IsQueryBoundP
      (fun q => bhClassifyTarget
        (fun kq => kq matches .initiateOPK .. || kq matches .initiateNoOPK ..)
        (fun _ => false) (fun _ => false) q = true)
      S.N_send_tot)
    (hRecv : B_A.IsQueryBoundP
      (fun q => bhClassifyTarget
        (fun kq => kq matches .acceptOPK .. || kq matches .acceptNoOPK ..)
        (fun _ => false) (fun _ => false) q = true)
      S.N_recv_tot)
    (hTot : B_A.IsQueryBoundP
      (fun q => bhClassifyTarget (fun _ => true) (fun _ => false) (fun _ => false) q = true)
      b.q_total)
    (hOn : B_A.IsQueryBoundP
      (fun q => bhClassifyTarget
        (fun kq => !(kq matches .roQuery _)) (fun _ => false) (fun _ => false) q = true)
      b.q_on)
    (hCtlSend : B_A.IsQueryBoundP
      (fun q => bhClassifyTarget (fun _ => false) (fun _ => true) (fun _ => false) q = true)
      S.N_send_tot)
    (hCtlStart : B_A.IsQueryBoundP
      (fun q => bhClassifyTarget (fun _ => false) (fun _ => true) (fun _ => false) q = true)
      qStart) :
    let advK : SignalPqxdh.KeyIndAdversary S :=
      ⟨(bhKindRedWithHalted badLog P ki C K qep decT encT).eval (fun _ => B_A) ()⟩
    SignalPqxdh.QueryBounded advK (keyIndReductionBudget S qStart b) :=
  bhKindRedWithTracked_queryBounded_of_B (fun _ => []) _ P ki C K B_A b qStart
    hRo hSend hRecv hTot hOn hCtlSend hCtlStart

end Computational.Proofs.LibsignalCli.MainHaltedKindBounds
