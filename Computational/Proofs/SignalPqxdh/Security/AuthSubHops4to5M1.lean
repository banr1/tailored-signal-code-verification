/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Computational.Proofs.SignalPqxdh.Security.ReductionsAuthAead
public import Computational.Proofs.SignalPqxdh.Security.SigHopA
import Computational.Proofs.SignalPqxdh.Security.AuthSubHops4to5
import Computational.Proofs.SignalPqxdh.Security.AuthSubHops4to5C2

/-!
# Multi-Key `INT-CTXT` Reduction Query Bounds

Proves encryption, forgery, and primitive-oracle query bounds (`MuBounded`) for
`aeadMuIntReductionAuth`.
-/

@[expose] public section

set_option autoImplicit false

open OracleSpec OracleComp MeasureTheory ENNReal BigOperators

namespace SignalPqxdh.Security

open SignalPqxdh
open _root_.Proofs.SignalPqxdh.Security
open _root_.Proofs.SignalPqxdh.Security.FgGapDh

/-- Encryption, forgery and primitive query bounds of an `AeadMuIntSimSpec` computation. -/
def MuBounded {α : Type} (mx : OracleComp AeadMuIntSimSpec α) (E D P : Nat) : Prop :=
  IsQueryBoundP mx isMuEncQuery E ∧
  IsQueryBoundP mx isMuForgeQuery D ∧
  IsQueryBoundP mx (fun q => isPrimQuery q = true) P

theorem muBounded_pure {α : Type} (a : α) (E D P : Nat) :
    MuBounded (pure a : OracleComp AeadMuIntSimSpec α) E D P :=
  ⟨(isQueryBoundP_pure _ a 0).mono (Nat.zero_le E),
   (isQueryBoundP_pure _ a 0).mono (Nat.zero_le D),
   (isQueryBoundP_pure _ a 0).mono (Nat.zero_le P)⟩

theorem muBounded_pure' {α : Type} {a : α} {E D P : Nat} :
    MuBounded (pure a : OracleComp AeadMuIntSimSpec α) E D P :=
  muBounded_pure a E D P

theorem muBounded_mono {α : Type} {mx : OracleComp AeadMuIntSimSpec α}
    {E1 E2 D1 D2 P1 P2 : Nat} (h : MuBounded mx E1 D1 P1) (hE : E1 ≤ E2) (hD : D1 ≤ D2)
    (hP : P1 ≤ P2) : MuBounded mx E2 D2 P2 :=
  ⟨h.1.mono hE, h.2.1.mono hD, h.2.2.mono hP⟩

theorem muBounded_bind {α β : Type}
    {mx : OracleComp AeadMuIntSimSpec α} {f : α → OracleComp AeadMuIntSimSpec β}
    {E1 E2 D1 D2 P1 P2 : Nat}
    (h1 : MuBounded mx E1 D1 P1) (h2 : ∀ a, MuBounded (f a) E2 D2 P2) :
    MuBounded (mx >>= f) (E1 + E2) (D1 + D2) (P1 + P2) :=
  ⟨isQueryBoundP_bind h1.1 (fun a _ => (h2 a).1),
   isQueryBoundP_bind h1.2.1 (fun a _ => (h2 a).2.1),
   isQueryBoundP_bind h1.2.2 (fun a _ => (h2 a).2.2)⟩

theorem muBounded_bind_le {α β : Type}
    {mx : OracleComp AeadMuIntSimSpec α} {f : α → OracleComp AeadMuIntSimSpec β}
    {E1 D1 P1 E D P : Nat} (E2 D2 P2 : Nat)
    (h1 : MuBounded mx E1 D1 P1) (h2 : ∀ a, MuBounded (f a) E2 D2 P2)
    (hE : E1 + E2 ≤ E := by omega) (hD : D1 + D2 ≤ D := by omega)
    (hP : P1 + P2 ≤ P := by omega) :
    MuBounded (mx >>= f) E D P :=
  muBounded_mono (muBounded_bind h1 h2) hE hD hP

theorem muBounded_ite {α : Type} {c : Prop} [Decidable c]
    {t e : OracleComp AeadMuIntSimSpec α} {E D P : Nat}
    (ht : MuBounded t E D P) (he : MuBounded e E D P) :
    MuBounded (if c then t else e) E D P := by
  by_cases h : c <;> simp [h, ht, he]

theorem isQueryBoundP_embedPrimMu_notPrim {α : Type}
    (pred : ((ℕ ⊕ PrimQuery) ⊕ AeadMuIntQuery) → Prop) [DecidablePred pred]
    (hpred : ∀ q, ¬ pred (Sum.inl q))
    (oa : OracleComp PrimBaseSpec α) (n : Nat) :
    IsQueryBoundP (embedPrimMu oa) pred n := by
  unfold embedPrimMu
  induction oa using OracleComp.inductionOn generalizing n with
  | pure x => exact (isQueryBoundP_pure _ x 0).mono (Nat.zero_le n)
  | query_bind q mx ih =>
    rw [embedPrim_query_bind, isQueryBoundP_query_bind_iff]
    exact ⟨Or.inl (hpred q), fun u => by simpa [hpred q] using ih u n⟩

theorem muBounded_embedPrimMu {α : Type}
    (oa : OracleComp PrimBaseSpec α) (E D P : Nat) (hP : PrimBounded oa P) :
    MuBounded (embedPrimMu oa) E D P :=
  ⟨isQueryBoundP_embedPrimMu_notPrim isMuEncQuery (fun _ h => by cases h) oa E,
   isQueryBoundP_embedPrimMu_notPrim isMuForgeQuery (fun _ h => by cases h) oa D,
   isQueryBoundP_embedPrim_isPrimQuery (spec := aeadMuIntSpec) oa P hP⟩

theorem muBounded_unifMu {α : Type} (oa : ProbComp α) (E D P : Nat) :
    MuBounded (unifMu oa) E D P :=
  muBounded_embedPrimMu (embedUnif oa) E D P (primBounded_embedUnif oa P)

theorem muBounded_primMuQ (op : PrimQuery) :
    MuBounded (primMuQ op) 0 0 1 :=
  muBounded_embedPrimMu (primQ op) 0 0 1 (primBounded_primQ op)

theorem muBounded_encOnceMuQ (i : Nat) (ad pt : Bytes) :
    MuBounded (encOnceMuQ i ad pt) 1 0 0 := by
  unfold encOnceMuQ MuBounded
  refine ⟨?_, ?_, ?_⟩
  · exact (isQueryBoundP_query_iff (spec := AeadMuIntSimSpec)
      isMuEncQuery (Sum.inr (.encOnce i ad pt)) 1).2 (fun _ => Nat.zero_lt_one)
  · exact (isQueryBoundP_query_iff (spec := AeadMuIntSimSpec)
      isMuForgeQuery (Sum.inr (.encOnce i ad pt)) 0).2 (fun h => by cases h)
  · exact (isQueryBoundP_query_iff (spec := AeadMuIntSimSpec)
      (fun q => isPrimQuery q = true) (Sum.inr (.encOnce i ad pt)) 0).2 (fun h => by cases h)

theorem muBounded_tryForgeMuQ (i : Nat) (ad ct : Bytes) :
    MuBounded (tryForgeMuQ i ad ct) 0 1 0 := by
  unfold tryForgeMuQ MuBounded
  refine ⟨?_, ?_, ?_⟩
  · exact (isQueryBoundP_query_iff (spec := AeadMuIntSimSpec)
      isMuEncQuery (Sum.inr (.tryForge i ad ct)) 0).2 (fun h => by cases h)
  · exact (isQueryBoundP_query_iff (spec := AeadMuIntSimSpec)
      isMuForgeQuery (Sum.inr (.tryForge i ad ct)) 1).2 (fun _ => Nat.zero_lt_one)
  · exact (isQueryBoundP_query_iff (spec := AeadMuIntSimSpec)
      (fun q => isPrimQuery q = true) (Sum.inr (.tryForge i ad ct)) 0).2 (fun h => by cases h)

theorem runWithMuStep_pure {ιI : Type}
    {GSpec : OracleSpec.{0, 0} ιI} {St α : Type}
    (step : (q : ιI) → St → OracleComp AeadMuIntSimSpec (GSpec.Range q × St))
    (a : α) (st : St) :
    runWithMuStep step (pure a) st = pure (a, st) := rfl

@[simp]
theorem runWithMuStep_query_inl {ιI : Type}
    {GSpec : OracleSpec.{0, 0} ιI} {St α : Type}
    (step : (q : ιI) → St → OracleComp AeadMuIntSimSpec (GSpec.Range q × St))
    (n : Nat) (mx : (unifSpec + GSpec).Range (Sum.inl n) → OracleComp (unifSpec + GSpec) α)
    (st : St) :
    runWithMuStep step (liftM (OracleSpec.query (Sum.inl n)) >>= mx) st =
      (liftM (OracleSpec.query (spec := AeadMuIntSimSpec) (Sum.inl (Sum.inl n))) >>=
        fun u => runWithMuStep step (mx u) st) := rfl

@[simp]
theorem runWithMuStep_query_inr {ιI : Type}
    {GSpec : OracleSpec.{0, 0} ιI} {St α : Type}
    (step : (q : ιI) → St → OracleComp AeadMuIntSimSpec (GSpec.Range q × St))
    (gq : ιI) (mx : (unifSpec + GSpec).Range (Sum.inr gq) → OracleComp (unifSpec + GSpec) α)
    (st : St) :
    runWithMuStep step (liftM (OracleSpec.query (Sum.inr gq)) >>= mx) st =
      (step gq st >>= fun p => runWithMuStep step (mx p.1) p.2) := rfl

theorem isQueryBoundP_runWithMuStep_counted {ιI : Type}
    {GSpec : OracleSpec.{0, 0} ιI} {St α : Type}
    (target : ((ℕ ⊕ PrimQuery) ⊕ AeadMuIntQuery) → Prop) [DecidablePred target]
    (h_target_unif : ∀ n, ¬ target (Sum.inl (Sum.inl n)))
    (pred : ℕ ⊕ ιI → Prop) [DecidablePred pred]
    (h_inl : ∀ n, ¬ pred (Sum.inl n))
    (step : (q : ιI) → St → OracleComp AeadMuIntSimSpec (GSpec.Range q × St))
    (h_step : ∀ gq st,
      IsQueryBoundP (step gq st) target (if pred (Sum.inr gq) then 1 else 0))
    (mx : OracleComp (unifSpec + GSpec) α) (R : Nat)
    (h_mx : IsQueryBoundP mx pred R)
    (st : St) :
    IsQueryBoundP (runWithMuStep step mx st) target R := by
  induction mx using OracleComp.inductionOn generalizing R st with
  | pure x =>
    simp [runWithMuStep_pure, isQueryBoundP_pure]
  | query_bind q mx ih =>
    rw [isQueryBoundP_query_bind_iff] at h_mx
    cases q with
    | inl n =>
      rcases h_mx with ⟨_, h_cont⟩
      have hnl : ¬ pred (Sum.inl n) := h_inl n
      simp only [hnl, ↓reduceIte] at h_cont
      rw [runWithMuStep_query_inl, isQueryBoundP_query_bind_iff]
      exact ⟨Or.inl (h_target_unif n), fun u => by
        simpa [h_target_unif n] using ih u R (h_cont u) st⟩
    | inr gq =>
      rcases h_mx with ⟨h_first, h_cont⟩
      rw [runWithMuStep_query_inr]
      by_cases hp : pred (Sum.inr gq)
      · rcases h_first with h_abs | hRpos
        · exfalso; exact h_abs hp
        · obtain ⟨R', rfl⟩ : ∃ R', R = R' + 1 := ⟨R - 1, by omega⟩
          simp only [hp, ↓reduceIte, Nat.add_sub_cancel] at h_cont
          have h1 : IsQueryBoundP (step gq st) target 1 := by
            simpa [hp] using h_step gq st
          exact (isQueryBoundP_bind h1 (fun p _ => ih p.1 R' (h_cont p.1) p.2)).mono (by omega)
      · simp only [hp, ↓reduceIte] at h_cont
        have h0 : IsQueryBoundP (step gq st) target 0 := by
          simpa [hp] using h_step gq st
        exact (isQueryBoundP_bind h0 (fun p _ => ih p.1 R (h_cont p.1) p.2)).mono (by omega)

theorem isQueryBoundP_runWithMuStep_prim {ιI : Type}
    {GSpec : OracleSpec.{0, 0} ιI} {St α : Type}
    (step : (q : ιI) → St → OracleComp AeadMuIntSimSpec (GSpec.Range q × St))
    (P : Nat)
    (h_step : ∀ gq st, IsQueryBoundP (step gq st) (fun q => isPrimQuery q = true) P)
    (mx : OracleComp (unifSpec + GSpec) α) (Q : Nat)
    (h_mx : IsQueryBoundP mx (fun q : ℕ ⊕ ιI => isGameQuery q = true) Q)
    (st : St) :
    IsQueryBoundP (runWithMuStep step mx st) (fun q => isPrimQuery q = true) (Q * P) := by
  induction mx using OracleComp.inductionOn generalizing Q st with
  | pure x =>
    simp [runWithMuStep_pure, isQueryBoundP_pure]
  | query_bind q mx ih =>
    rw [isQueryBoundP_query_bind_iff] at h_mx
    cases q with
    | inl n =>
      rcases h_mx with ⟨_, h_cont⟩
      rw [runWithMuStep_query_inl, isQueryBoundP_query_bind_iff]
      exact ⟨Or.inl (fun h => by cases h), fun u => ih u Q (h_cont u) st⟩
    | inr gq =>
      rcases h_mx with ⟨h_abs | hQpos, h_cont⟩
      · exfalso; exact h_abs rfl
      · obtain ⟨Q', rfl⟩ : ∃ Q', Q = Q' + 1 := ⟨Q - 1, by omega⟩
        simp only [isGameQuery, Nat.add_sub_cancel] at h_cont
        rw [runWithMuStep_query_inr]
        exact (isQueryBoundP_bind (h_step gq st) (fun p _ => ih p.1 Q' (h_cont p.1) p.2)).mono
          (by rw [Nat.succ_mul]; omega)

theorem muBounded_runAuthSendMuPrim (S : Setup)
    (sid : SessionId S) (u : Fin S.N_id) (bundle : PreKeyBundleInput) (m0 m1 : Bytes)
    (hst : AuthHybridStateFixed S) :
    MuBounded (runAuthSendMuPrim S sid u bundle m0 m1 hst) 1 0 (perQueryAuthPrimBudget S) := by
  unfold runAuthSendMuPrim perQueryAuthPrimBudget
  refine muBounded_bind_le 1 0 2
    (muBounded_embedPrimMu _ 0 0 (S.N_dh * 14 + 16)
        (primBounded_prepAuthIntSendPrim S sid u bundle m0 m1 hst))
    (fun p? => ?_)
  cases p? with
  | none => exact muBounded_pure'
  | some p =>
    dsimp only
    refine muBounded_bind_le (E1 := 1) (D1 := 0) (P1 := 2) 0 0 0 ?_ (fun _ => muBounded_pure')
    refine muBounded_ite ?_ ?_
    · exact muBounded_bind_le 0 0 0 (muBounded_encOnceMuQ _ _ _) (fun _ => muBounded_pure')
    · refine muBounded_bind_le (E1 := 0) (D1 := 0) (P1 := 1) 0 0 1 (muBounded_primMuQ _)
        (fun _ => ?_)
      exact muBounded_bind_le 0 0 0 (muBounded_primMuQ _) (fun _ => muBounded_pure')

theorem muBounded_finishAuthRecvScheduleMuPrim {S : Setup}
    (kEntry : PrincipalEntry) (msg : PreKeyMsg)
    (recvCount : Nat) (mkSaltCache : AuthMkSaltCache S) (sp : AuthIntRecvSchedPrep S) :
    MuBounded (finishAuthRecvScheduleMuPrim kEntry msg recvCount mkSaltCache sp) 0 1 2 := by
  unfold finishAuthRecvScheduleMuPrim
  have hF : ∀ i ad ct (r : Option (DRKey × Bytes × Bytes × Bytes × List (Bytes × DRKey) ×
        List ((Bytes × Bytes) × (Bytes × Bytes))) × AuthMkSaltCache S),
      MuBounded (do let _ ← tryForgeMuQ i ad ct; return r) 0 1 2 := fun i ad ct r =>
    muBounded_bind_le 0 0 0 (muBounded_tryForgeMuQ i ad ct) (fun _ => muBounded_pure')
  dsimp only
  refine muBounded_ite ?_ ?_
  · cases sp.matchedSess? with
    | none => exact hF _ _ _ _
    | some s =>
      dsimp only
      refine muBounded_ite (muBounded_ite muBounded_pure' (hF _ _ _ _)) ?_
      refine muBounded_ite ?_ (hF _ _ _ _)
      cases mkSaltCache.find? (fun (k, _) => mkSaltKeyMatch k s.sid sp.spqrSalt?) with
      | some entry => rcases entry with ⟨_, r0, _⟩; exact hF _ _ _ _
      | none => exact hF _ _ _ _
  · refine muBounded_bind_le 0 0 1 (muBounded_primMuQ _) (fun _ => ?_)
    refine muBounded_bind_le 0 0 0 (muBounded_primMuQ _) (fun pt? => ?_)
    cases pt? <;> exact muBounded_pure'

theorem muBounded_evalAuthRecvScheduleMuPrim (S : Setup)
    (hstDec : AuthHybridState S) (recvCount : Nat) (mkSaltCache : AuthMkSaltCache S)
    (kEntry : PrincipalEntry) (bEntry : SpkBundleEntry) (opkPk? : Option Bytes)
    (secrets : Bytes) (msg : PreKeyMsg) :
    MuBounded
      (evalAuthRecvScheduleMuPrim S hstDec recvCount mkSaltCache kEntry bEntry opkPk? secrets msg)
      0 1 (S.N_dh * 2 + S.N_sess_tot * 10 + 8) := by
  unfold evalAuthRecvScheduleMuPrim
  refine muBounded_bind_le 0 1 2
    (muBounded_embedPrimMu _ 0 0 (S.N_dh * 2 + S.N_sess_tot * 10 + 6)
      (primBounded_prepAuthIntRecvSchedPrim S hstDec kEntry bEntry opkPk? secrets msg))
    (fun sp? => ?_)
  cases sp? with
  | none => exact muBounded_pure'
  | some sp => exact muBounded_finishAuthRecvScheduleMuPrim kEntry msg recvCount mkSaltCache sp

theorem muBounded_stepAuthMuPrim (S : Setup) (q : AuthQuery S) (hst : AuthHybridStateFixed S) :
    MuBounded (stepAuthMuPrim S q hst)
      (if isAuthSendQuery (.inr q) then 1 else 0)
      (if isAuthRecvQuery (.inr q) then 1 else 0)
      (perQueryAuthPrimBudget S) := by
  unfold stepAuthMuPrim
  cases q with
  | sendOPK u i bundle m0 m1 =>
    simp only [isAuthSendQuery, isAuthRecvQuery, ↓reduceIte]
    split <;>
      [exact muBounded_pure'; exact muBounded_runAuthSendMuPrim S (.sendOPK u i) u bundle m0 m1 hst]
  | sendNoOPK u i bundle m0 m1 =>
    simp only [isAuthSendQuery, isAuthRecvQuery, ↓reduceIte]
    split <;>
      [exact muBounded_pure';
       exact muBounded_runAuthSendMuPrim S (.sendNoOPK u i) u bundle m0 m1 hst]
  | recvOPK k j o msg =>
    simp only [isAuthSendQuery, isAuthRecvQuery, ↓reduceIte]
    unfold perQueryAuthPrimBudget
    refine muBounded_bind_le 0 1 (S.N_dh * 2 + S.N_sess_tot * 10 + 8)
      (muBounded_embedPrimMu _ 0 0 (S.N_dh * 4 + 8)
        (primBounded_prepareAuthRecvOPKPrim S k j o msg hst.toAuthHybridState))
      (fun prep? => ?_)
    cases prep? with
    | none => exact muBounded_pure'
    | some prep =>
      exact muBounded_bind_le 0 0 0
        (muBounded_evalAuthRecvScheduleMuPrim S prep.hstDec
          hst.recvCount hst.mkSaltCache prep.kEntry prep.bEntry prep.opkPk? prep.secrets msg)
        (fun _ => muBounded_pure')
  | recvNoOPK k j l msg =>
    simp only [isAuthSendQuery, isAuthRecvQuery, ↓reduceIte]
    unfold perQueryAuthPrimBudget
    refine muBounded_bind_le 0 1 (S.N_dh * 2 + S.N_sess_tot * 10 + 8)
      (muBounded_embedPrimMu _ 0 0 (S.N_dh * 4 + 8)
        (primBounded_prepareAuthRecvNoOPKPrim S k j l msg hst.toAuthHybridState))
      (fun prep? => ?_)
    cases prep? with
    | none => exact muBounded_pure'
    | some prep =>
      exact muBounded_bind_le 0 0 0
        (muBounded_evalAuthRecvScheduleMuPrim S prep.hstDec
          hst.recvCount hst.mkSaltCache prep.kEntry prep.bEntry prep.opkPk? prep.secrets msg)
        (fun _ => muBounded_pure')
  | initPrin u | corruptIK u | genSPK u j | genOPK u j o | registerKey sk | roQuery secrets
  | roRootQuery rk dh | revealDhSecrets =>
    simp only [isAuthSendQuery, isAuthRecvQuery, ↓reduceIte]
    unfold perQueryAuthPrimBudget
    exact muBounded_embedPrimMu _ 0 0 (S.N_dh * 14 + S.N_sess_tot * 10 + 18)
      ((primBounded_stepAuthOtherPrim true S _ hst).mono (by omega))

theorem muBounded_aeadMuIntReductionAuthRun (S : Setup) (b : QueryBudget)
    (A : BoundedAdv (AuthAdversary S) b) :
    MuBounded (aeadMuIntReductionAuthRun S A.1)
      S.N_send_tot S.N_recv_tot (b.q_total * perQueryAuthPrimBudget S + S.N_dh * 5) := by
  unfold aeadMuIntReductionAuthRun
  refine muBounded_bind_le S.N_send_tot S.N_recv_tot
    (b.q_total * perQueryAuthPrimBudget S + S.N_dh * 5)
    (muBounded_unifMu ($ᵗ Bool) 0 0 0) (fun secb => ?_)
  have hStep : MuBounded
      (runWithMuStep (stepAuthMuPrim S) A.1.run (AuthHybridStateFixed.empty S secb))
      S.N_send_tot S.N_recv_tot (b.q_total * perQueryAuthPrimBudget S) :=
    ⟨isQueryBoundP_runWithMuStep_counted isMuEncQuery (fun _ h => by cases h)
      isAuthSendQuery (fun _ h => by cases h) (stepAuthMuPrim S)
      (fun gq st => (muBounded_stepAuthMuPrim S gq st).1)
      A.1.run S.N_send_tot (QueryBounded.auth_send A.2) (AuthHybridStateFixed.empty S secb),
     isQueryBoundP_runWithMuStep_counted isMuForgeQuery (fun _ h => by cases h)
      isAuthRecvQuery (fun _ h => by cases h) (stepAuthMuPrim S)
      (fun gq st => (muBounded_stepAuthMuPrim S gq st).2.1)
      A.1.run S.N_recv_tot (QueryBounded.auth_recv A.2) (AuthHybridStateFixed.empty S secb),
     isQueryBoundP_runWithMuStep_prim
      (stepAuthMuPrim S) (perQueryAuthPrimBudget S)
      (fun gq st => (muBounded_stepAuthMuPrim S gq st).2.2)
      A.1.run b.q_total (QueryBounded.auth_total A.2) (AuthHybridStateFixed.empty S secb)⟩
  exact muBounded_bind_le 0 0 (S.N_dh * 5) hStep (fun _ => muBounded_pure')

theorem aeadMuIntReductionAuth_bounded (S : Setup) (b : QueryBudget)
    (A : BoundedAdv (AuthAdversary S) b) :
    (aeadMuIntReductionAuth S b A).Bounded :=
  muBounded_aeadMuIntReductionAuthRun S b A

theorem aeadMuIntReductionAuth_queries (S : Setup) (b : QueryBudget)
    (A : BoundedAdv (AuthAdversary S) b) :
    (aeadMuIntReductionAuth S b A).q_dec ≤ S.N_recv_tot := le_rfl

theorem aeadMuIntReductionAuth_enc_queries (S : Setup) (b : QueryBudget)
    (A : BoundedAdv (AuthAdversary S) b) :
    (aeadMuIntReductionAuth S b A).q_enc ≤ S.N_send_tot := le_rfl

theorem aeadMuIntReductionAuth_prim_queries (S : Setup) (b : QueryBudget)
    (A : BoundedAdv (AuthAdversary S) b) :
    (aeadMuIntReductionAuth S b A).q_prim ≤ primQueryBudget S b := by
  unfold aeadMuIntReductionAuth perQueryAuthPrimBudget primQueryBudget
  dsimp only
  nlinarith

end SignalPqxdh.Security
