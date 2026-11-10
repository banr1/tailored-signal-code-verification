/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Computational.Proofs.SignalPqxdh.Security.ReductionDsl.Auth1KeyPrfBase
public import Computational.Proofs.SignalPqxdh.Security.ReductionDsl.AuthPrfMkEval
public import Computational.Proofs.SignalPqxdh.Security.ReductionDsl.AuthPrfCost
public import Computational.Proofs.SignalPqxdh.Security.ReductionDsl.AuthPrfMkShallow
import Computational.Proofs.SignalPqxdh.Security.AuthSubHops1to3H2
import Computational.Proofs.SignalPqxdh.Security.ReductionDsl.AuthPrfMkDecomp
import Computational.Proofs.SignalPqxdh.Security.ReductionDsl.AuthPrfMkLeaves
import VCVio.EvalDist.Monad.Basic

/-!
# One-Key `PrfMsgKeys` `ReductionDsl` Program

Defines `prfMsgKeysRedProg1Key` by replacing the `.initPrin` pre-step branch of `prfMsgKeysRedProg`
with `initPrin1KeyFixedB`. Proves evaluation equivalence with `prfMsgKeysReductionAuthFixed1Key` and
bounds static cost and query counts by those of `prfMsgKeysRedProg`.
-/

@[expose] public section

set_option autoImplicit false
set_option maxHeartbeats 16000000
set_option maxRecDepth 100000
namespace SignalPqxdh.Security.ReductionDsl.AuthPrf

open _root_.ReductionDsl hiding B PTag U32 bundleOfV bundleT bundleV dhSecretsT drKeyOfV drKeyT drKeyV hdrOfV hdrT hdrV keyIndCodec keyIndQT keyIndQenc keyIndRT keyIndRdec keyIndRenc pqPrimIface pqSigAndDdhIface sampleIndex sidT sidV
open SignalPqxdh
open SignalPqxdh.LegacyCosted
open SignalPqxdh.Security
open SignalPqxdh.Security.AuthSubHops1to3
open RoKem
open FgGapDh
open OracleSpec OracleComp

section PrfMk1KeyBranches

variable (S : Setup) (K : Nat) {Γ₁ Γ₂ Δ : List PT}

/-- `prfMkStepPreC` with the `.initPrin` branch replaced by `initPrin1KeyFixedB`. -/
def prfMkStepPre1KeyC (core : Var Γ₁ prfMkCoreTy) (q : Var Γ₂ authQueryTy)
    [Ext Γ₁ Δ] [Ext Γ₂ Δ] : Comp pqxdhOps pqPrimIface Δ prfMkStepPreTy :=
  letV (mkcFhst (v core)) fun fhst =>
  caseSumV (v q) (fun u => wrapMkBase core (initPrin1KeyFixedB K fhst u)) fun q =>
  caseSumV (v q) (fun u => wrapMkBase core (corruptFixedB K fhst u)) fun q =>
  caseSumV (v q) (fun x => wrapMkBase core (genSpkFixedB K fhst x)) fun q =>
  caseSumV (v q) (fun x => wrapMkBase core (genOpkFixedB K fhst x)) fun q =>
  caseSumV (v q) (fun x => authMkSendPreB S K true core x) fun q =>
  caseSumV (v q) (fun x => authMkSendPreB S K false core x) fun q =>
  caseSumV (v q) (fun x => authMkRecvPreB S K true core x) fun q =>
  caseSumV (v q) (fun x => authMkRecvPreB S K false core x) fun q =>
  caseSumV (v q) (fun sec => wrapMkBase core (roFixedB K fhst sec)) fun q =>
  caseSumV (v q) (fun x => wrapMkBase core (roRootFixedB K fhst x)) fun q =>
  caseSumV (v q) (fun _ => .ret (.inl (.pair aNone (v core)))) fun sk =>
  wrapMkBase core (registerFixedB fhst sk)

end PrfMk1KeyBranches

/-- One-key per-query handler: `prfMsgKeysHandleDsl` over `prfMkStepPre1KeyC`. -/
def prfMsgKeysHandle1KeyDsl (S : Setup) (K : Nat) :
    Comp pqxdhOps pqPrfMkIface [prfMkStTy, authQueryTy] (.prod authRespTy prfMkStTy) :=
  letV (.var .zero : Expr pqxdhOps [prfMkStTy, authQueryTy] prfMkStTy) fun s =>
  letV (.fst (v s)) fun bud =>
  letV (.snd (v s)) fun core =>
  bindV (liftPrimComp
    (prfMkStepPre1KeyC S K core (.succ .zero : Var [prfMkStTy, authQueryTy] authQueryTy))) fun pre =>
  caseSumV (v pre)
    (fun d => .ret (.pair (.fst (v d)) (.pair (v bud) (.snd (v d)))))
    fun req =>
      .ite (natEq (v bud) (.nat 0))
        (.ret (.pair aNone (.pair (.nat 0) (v core))))
        (letV (.fst (v req)) fun salt? =>
         letV (.snd (v req)) fun cont =>
         bindV (queryDeriveMk (v salt?)) fun mk =>
         bindV (liftPrimComp (prfMkStepPostC S K cont mk)) fun post =>
         .ret (.pair (.fst (v post))
           (.pair (.sub (v bud) (.nat 1)) (.snd (v post)))))

/-- ReductionDsl program for `prfMsgKeysReductionAuthFixed1Key S b`. -/
def prfMsgKeysRedProg1Key (S : Setup) (K : Nat) :
    CostedReduction pqxdhOps pqPrfMkIface (authSpec S) (authCodec S)
      .unit .unit .bool .bool where
  σ      := prfMkStTy
  init   := prfMsgKeysInitDslK S K
  handle := prfMsgKeysHandle1KeyDsl S K
  finish := prfMsgKeysFinishDsl S K

/-- One-key pre-step of a `PrfMsgKeys` game step (`mkPre` with the one-key `.initPrin`). -/
def mkPre1Key (S : Setup) (idx : Nat) (q : AuthQuery S) (hst : AuthHybridStateFixed S)
    (sentChal : Bool) : OracleComp PrimBaseSpec (MkPre S) :=
  match q with
  | .initPrin u => .inl <$> AuthSubHops1to3.stepAuthOtherPrim1Key S (.initPrin u) hst
  | q => mkPre S idx q hst sentChal

def prfMkStep1KeyC (S : Setup) (idx : Nat) (q : AuthQuery S) (hst : AuthHybridStateFixed S)
    (sentChal : Bool) :
    OracleComp PrfMkSimSpec ((AuthResponse × AuthHybridStateFixed S) × Nat × Bool) :=
  prfMkRunPre (mkPre1Key S idx q hst sentChal) sentChal

theorem mkPre1Key_eq_of_ne {S : Setup} (idx : Nat) (q : AuthQuery S)
    (hq : AuthQuery.NotInitPrin q) (hst : AuthHybridStateFixed S) (sc : Bool) :
    mkPre1Key S idx q hst sc = mkPre S idx q hst sc := by
  cases q <;> first | rfl | exact absurd rfl (hq _)

theorem authMkStepReduction1Key_eq_of_ne {S : Setup} (idx : Nat) (q : AuthQuery S)
    (hq : AuthQuery.NotInitPrin q) (hst : AuthHybridStateFixed S) (sc : Bool) :
    authMkStepReduction1Key S idx q hst sc = authMkStepReduction S idx q hst sc := by
  cases q <;> first | rfl | exact absurd rfl (hq _)

theorem authMkStepReduction1Key_eq {S : Setup} (idx : Nat) (q : AuthQuery S)
    (hst : AuthHybridStateFixed S) (sc : Bool) :
    authMkStepReduction1Key S idx q hst sc =
      (fun x => (x.1, x.2.2)) <$> prfMkStep1KeyC S idx q hst sc := by
  by_cases hI : AuthQuery.NotInitPrin q
  · rw [authMkStepReduction1Key_eq_of_ne idx q hI, authMkStepReduction_eq]
    unfold prfMkStep1KeyC prfMkStepC
    rw [mkPre1Key_eq_of_ne idx q hI]
  · obtain ⟨u, rfl⟩ : ∃ u, q = .initPrin u := by
      by_contra hne; push Not at hne; exact hI hne
    unfold prfMkStep1KeyC mkPre1Key
    rw [prfMkRunPre_map_inl]
    simp [authMkStepReduction1Key]

theorem mkPre1Key_leaves {S : Setup} {n : Nat} (idx : Nat) (q : AuthQuery S)
    (hst : AuthHybridStateFixed S) (sc : Bool) (hB : AuthListsBounded n hst) :
    AllLeaves (fun (p : MkPre S) => match p with
        | .inl (_, hst') => AuthListsBounded (n + 1) hst'
        | .inr (_, c) => c.Bounded n ∧ (c.isSend = true → sc = false) ∧
            (c.isSend = false → isAuthRecvQuery (.inr q : Nat ⊕ AuthQuery S)))
      (mkPre1Key S idx q hst sc) := by
  by_cases hI : AuthQuery.NotInitPrin q
  · rw [mkPre1Key_eq_of_ne idx q hI]
    exact mkPre_leaves idx q hst sc hB
  · obtain ⟨u, rfl⟩ : ∃ u, q = .initPrin u := by
      by_contra hne; push Not at hne; exact hI hne
    unfold mkPre1Key
    dsimp only
    rw [map_eq_bind_pure_comp]
    exact AllLeaves.bind (stepAuthOtherPrim1Key_bounded (.initPrin u) hst hB)
      (fun ⟨_, _⟩ hp => AllLeaves.pure hp)

theorem prfMkStep1KeyC_leaves {S : Setup} {n : Nat} (idx : Nat) (q : AuthQuery S)
    (hst : AuthHybridStateFixed S) (sc : Bool) (hB : AuthListsBounded n hst) :
    AllLeaves (fun (x : (AuthResponse × AuthHybridStateFixed S) × Nat × Bool) =>
        AuthListsBounded (n + 1) x.1.2 ∧
        ((x.2.1 = 0 ∧ x.2.2 = sc) ∨
         (x.2.1 = 1 ∧ ((sc = false ∧ x.2.2 = true) ∨
           (isAuthRecvQuery (.inr q : Nat ⊕ AuthQuery S) ∧ x.2.2 = sc)))))
      (prfMkStep1KeyC S idx q hst sc) := by
  unfold prfMkStep1KeyC prfMkRunPre
  refine AllLeaves.bind (AllLeaves.embedPrim (mkPre1Key_leaves idx q hst sc hB)) fun p hp => ?_
  rcases p with ⟨r, hst'⟩ | ⟨salt?, c⟩
  · exact AllLeaves.pure ⟨hp, Or.inl ⟨rfl, rfl⟩⟩
  · obtain ⟨hcB, hsend, hrecv⟩ := hp
    refine AllLeaves.bind_const _ fun mk => ?_
    refine AllLeaves.bind (AllLeaves.embedPrim (MkCont.post_leaves c mk hcB)) fun res hres => ?_
    refine AllLeaves.pure ⟨hres, Or.inr ⟨rfl, ?_⟩⟩
    cases hc : c.isSend
    · exact Or.inr ⟨hrecv hc, by simp⟩
    · exact Or.inl ⟨hsend hc, by simp⟩

section Dispatch1Key

variable (S : Setup) (K : Nat) {Γ₁ Γ₂ Δ : List PT}

theorem prfMkStepPre1KeyC_eval (core : Var Γ₁ prfMkCoreTy) (q : Var Γ₂ authQueryTy)
    [h₁ : Ext Γ₁ Δ] [h₂ : Ext Γ₂ Δ] (env : Env Δ)
    (secb : Bool) (idx : Nat) (sc : Bool) (hst : AuthHybridStateFixed S) (qv : AuthQuery S)
    (hcore : Env.get env (h₁.wk core) = mkCoreToVal secb idx sc hst)
    (hq : Env.get env (h₂.wk q) = authQueryToVal qv)
    (hB : AuthListsBounded K hst) :
    (prfMkStepPre1KeyC S K core q).eval env =
      mkPreToVal secb idx sc <$> mkPre1Key S idx qv hst sc := by
  by_cases hI : AuthQuery.NotInitPrin qv
  · obtain ⟨y, hy⟩ : ∃ y, authQueryToVal qv = Sum.inr y := by
      cases qv with
      | initPrin u => exact absurd rfl (hI u)
      | _ => exact ⟨_, rfl⟩
    rw [mkPre1Key_eq_of_ne idx qv hI,
      ← prfMkStepPreC_eval S K core q env secb idx sc hst qv hcore hq hB]
    have hq' := hq.trans hy
    simp only [prfMkStepPre1KeyC, prfMkStepPreC, letV, eval_letC, caseSumV, v, Comp.eval,
      Expr.eval, Ext.step_wk, Ext.refl_wk, Env.get_succ, Env.get_zero, hq']
  · obtain ⟨u, rfl⟩ : ∃ u, qv = .initPrin u := by
      by_contra hne; push Not at hne; exact hI hne
    simp only [authQueryToVal, authQenc] at hq
    simp only [prfMkStepPre1KeyC, letV, eval_letC, caseSumV, v, Comp.eval, Expr.eval,
      Ext.step_wk, Ext.refl_wk, Env.get_succ, hq]
    refine wrapMkBase_eval S core _ secb idx sc hst ?_ _ _
      (initPrin1KeyFixedB_eval S K _ _ _ hst u ?_ ?_ hB) <;>
      first | rfl | simp [hcore, mkCoreToVal]

end Dispatch1Key

theorem prfMsgKeysHandle1KeyDsl_eval (S : Setup) (K : Nat) (secb : Bool) (idx : Nat) (sc : Bool)
    (hst : AuthHybridStateFixed S) (bud : Nat) (qv : AuthQuery S)
    (hB : AuthListsBounded K hst)
    (hsc : sc = false → 0 < bud)
    (hrecv : isAuthRecvQuery (.inr qv : Nat ⊕ AuthQuery S) → 0 < bud) :
    (prfMsgKeysHandle1KeyDsl S K).eval
        (.cons (mkStToVal bud secb idx sc hst)
          (.cons (authQueryToVal qv) .nil)) =
      toDslMk ((fun x => (authRespToVal x.1.1,
        mkStToVal (bud - x.2.1) secb idx x.2.2 x.1.2)) <$> prfMkStep1KeyC S idx qv hst sc) := by
  have hpre := prfMkStepPre1KeyC_eval S K
    (env := (.cons (mkCoreToVal secb idx sc hst) (.cons bud
      (.cons (mkStToVal bud secb idx sc hst)
        (.cons (mkStToVal bud secb idx sc hst)
          (.cons (authQueryToVal qv) .nil)))) :
      Env [prfMkCoreTy, .nat, prfMkStTy, prfMkStTy, authQueryTy]))
    (core := (.zero : Var [prfMkCoreTy, .nat, prfMkStTy, prfMkStTy, authQueryTy] prfMkCoreTy))
    (q := (.succ .zero : Var [prfMkStTy, authQueryTy] authQueryTy))
    (secb := secb) (idx := idx) (sc := sc) (hst := hst) (qv := qv) (hcore := rfl) (hq := rfl)
    (hB := hB)
  simp only [prfMsgKeysHandle1KeyDsl, letV, eval_letC, bindV, caseSumV, v, Comp.eval, Expr.eval,
    Ext.step_wk, Ext.refl_wk, Env.get_succ, Env.get_zero, mkStToVal_fst, mkStToVal_snd,
    eval_liftPrimComp]
  rw [hpre]
  unfold prfMkStep1KeyC prfMkRunPre
  simp only [toDslMk_bind, toDslMk_pure, toDslMk_embedPrimMk, map_eq_bind_pure_comp,
    embedPrim_bind, embedPrim_pure, bind_assoc, Function.comp_apply, pure_bind]
  refine allLeaves_bind_congr (AllLeaves.embedPrim (mkPre1Key_leaves idx qv hst sc hB))
    fun p hp => ?_
  rcases p with ⟨r, hst'⟩ | ⟨salt?, c⟩
  · simp [mkStToVal, mkPreToVal, mkCoreToVal]
  · obtain ⟨hcB, hsend, hrecvc⟩ := hp
    have hbud : bud ≠ 0 := by
      cases hc : c.isSend
      · exact Nat.pos_iff_ne_zero.mp (hrecv (hrecvc hc))
      · exact Nat.pos_iff_ne_zero.mp (hsc (hsend hc))
    have hb : (bud == 0) = false := by simpa using hbud
    simp only [mkPreToVal, Expr.eval, natEq_eval, Env.get_zero, Env.get_succ,
      queryDeriveMk_eval', hb, Bool.false_eq_true, ↓reduceIte, toDslMk_bind, toDslMk_pure,
      toDslMk_embedPrimMk, map_eq_bind_pure_comp, bind_assoc, Function.comp_apply, pure_bind]
    refine bind_congr fun mk => ?_
    rw [prfMkStepPostC_eval S K
      (Γ₁ := [prfMkChalContTy, .opt (B 32), .prod (.opt (B 32)) prfMkChalContTy, prfMkStepPreTy,
        prfMkCoreTy, .nat, prfMkStTy, prfMkStTy, authQueryTy])
      (Γ₂ := [msgKeysTy, prfMkChalContTy, .opt (B 32), .prod (.opt (B 32)) prfMkChalContTy,
        prfMkStepPreTy, prfMkCoreTy, .nat, prfMkStTy, prfMkStTy, authQueryTy])
      (Δ := [msgKeysTy, prfMkChalContTy, .opt (B 32), .prod (.opt (B 32)) prfMkChalContTy,
        prfMkStepPreTy, prfMkCoreTy, .nat, prfMkStTy, prfMkStTy, authQueryTy])
      .zero .zero _ secb idx sc c mk _ _ hcB]
    rotate_left
    · rfl
    · rfl
    simp only [map_eq_bind_pure_comp, embedPrim_bind, embedPrim_pure, bind_assoc,
      Function.comp_apply, pure_bind, mkStToVal]

/-- Relates `simulateQ` of `prfMsgKeysHandle1KeyDsl` to `authMkStepReduction1Key` under bounded
    state lists and challenger budget. -/
theorem prfMk1Key_runBridge (S : Setup) (K : Nat) (secb : Bool) (idx : Nat) {α β : Type}
    (f : α × prfMkStTy.denote → OracleComp (PrimBaseSpec + msgKeyPrfOracle.spec) β)
    (g : (α × AuthHybridStateFixed S) × Bool → OracleComp PrfMkSimSpec β)
    (hfg : ∀ a hst sc bud, AuthListsBounded K hst →
      f (a, mkStToVal bud secb idx sc hst) = toDslMk (g ((a, hst), sc)))
    (mx : OracleComp (unifSpec + authSpec S) α) :
    ∀ (n r m bud : Nat) (hst : AuthHybridStateFixed S) (sc : Bool),
      IsQueryBoundP mx (fun q => SignalPqxdh.isGameQuery q = true) n →
      IsQueryBoundP mx isAuthRecvQuery r →
      AuthListsBounded m hst → m + n ≤ K →
      r + (if sc = true then 0 else 1) ≤ bud →
      ((simulateQ (handlerImpl (C := authCodec S) (prfMsgKeysHandle1KeyDsl S K)) mx).run
        (mkStToVal bud secb idx sc hst) >>= f) =
        toDslMk (runWithPrfMkStep (authMkStepReduction1Key S idx) mx hst sc >>= g) := by
  induction mx using OracleComp.inductionOn with
  | pure a =>
    intro n r m bud hst sc _ _ hB hmK _
    simp only [simulateQ_pure, runWithPrfMkStep, OracleComp.construct_pure, pure_bind]
    exact hfg a hst sc bud (hB.mono (by omega))
  | query_bind q k ih =>
    intro n r m bud hst sc hG hR hB hmK hbud
    rw [isQueryBoundP_query_bind_iff] at hG hR
    rcases q with uq | gq
    · obtain ⟨_, hG⟩ := hG
      obtain ⟨_, hR⟩ := hR
      have hnr : ¬ isAuthRecvQuery (.inl uq : Nat ⊕ AuthQuery S) := id
      simp only [SignalPqxdh.isGameQuery, Bool.false_eq_true, ↓reduceIte, hnr] at hG hR
      change (((do let a ← pqPrfMkIface.fwdU uq; pure (a, mkStToVal bud secb idx sc hst)) >>=
          fun x =>
            (simulateQ (handlerImpl (C := authCodec S) (prfMsgKeysHandle1KeyDsl S K)) (k x.1)).run
              x.2) >>= f) =
        toDslMk ((embedUnifMk (liftM (OracleSpec.query (spec := unifSpec) uq)) >>= fun u =>
            runWithPrfMkStep (authMkStepReduction1Key S idx) (k u) hst sc) >>= g)
      simp only [toDslMk_bind, pqPrfMkIface_fwdU_eq, bind_assoc, pure_bind]
      refine bind_congr fun u => ?_
      exact ih u n r m bud hst sc (hG u) (hR u) hB hmK hbud
    · obtain ⟨hG0, hG⟩ := hG
      obtain ⟨hR0, hR⟩ := hR
      simp only [SignalPqxdh.isGameQuery, ↓reduceIte] at hG hG0
      have hn : 0 < n := by
        rcases hG0 with h | h
        · exact absurd trivial h
        · exact h
      obtain ⟨n', rfl⟩ : ∃ n', n = n' + 1 := ⟨n - 1, by omega⟩
      simp only [Nat.add_sub_cancel] at hG
      change (((do
          let p ← (prfMsgKeysHandle1KeyDsl S K).eval
            (.cons (mkStToVal bud secb idx sc hst) (.cons (authQueryToVal gq) .nil))
          return (valToAuthResp p.1, p.2)) >>= fun x =>
            (simulateQ (handlerImpl (C := authCodec S) (prfMsgKeysHandle1KeyDsl S K)) (k x.1)).run
              x.2) >>= f) =
        toDslMk ((authMkStepReduction1Key S idx gq hst sc >>= fun p =>
            runWithPrfMkStep (authMkStepReduction1Key S idx) (k p.1.1) p.1.2 p.2) >>= g)
      have hRpos : isAuthRecvQuery (.inr gq : Nat ⊕ AuthQuery S) → 0 < r := fun h => by
        rcases hR0 with h' | h'
        · exact absurd h h'
        · exact h'
      have hB' : AuthListsBounded K hst := hB.mono (by omega)
      rw [prfMsgKeysHandle1KeyDsl_eval S K secb idx sc hst bud gq hB'
        (fun h => by subst h; simp at hbud; omega)
        (fun h => by have := hRpos h; omega),
        authMkStepReduction1Key_eq]
      simp only [toDslMk_bind, toDslMk_pure, map_eq_bind_pure_comp, bind_assoc,
        Function.comp_apply, pure_bind]
      refine allLeaves_bind_congr (AllLeaves.toDslMk (prfMkStep1KeyC_leaves idx gq hst sc hB))
        fun x hx => ?_
      obtain ⟨hxB, hleaf⟩ := hx
      rw [valToAuthResp_authRespToVal]
      refine ih x.1.1 n' (if isAuthRecvQuery (.inr gq : Nat ⊕ AuthQuery S) then r - 1 else r)
        (m + 1) (bud - x.2.1) x.1.2 x.2.2 (hG x.1.1) (hR x.1.1) hxB (by omega) ?_
      exact prfMk_budget_step r _ bud x.2.1 sc x.2.2
        (isAuthRecvQuery (.inr gq : Nat ⊕ AuthQuery S)) rfl hRpos hbud hleaf

private theorem isQueryBoundP_authRecv_of_game {S : Setup} {α : Type}
    (mx : OracleComp (unifSpec + authSpec S) α) :
    ∀ n, IsQueryBoundP mx (fun q => SignalPqxdh.isGameQuery q = true) n →
      IsQueryBoundP mx isAuthRecvQuery n := by
  induction mx using OracleComp.inductionOn with
  | pure _ => intro n _; exact isQueryBoundP_pure _ _ _
  | query_bind q k ih =>
    intro n hG
    rw [isQueryBoundP_query_bind_iff] at hG ⊢
    refine ⟨?_, fun u => ?_⟩
    · rcases hG.1 with h0 | hpos
      · left; intro hr; apply h0; cases q <;> simp_all [isAuthRecvQuery, SignalPqxdh.isGameQuery]
      · right; exact hpos
    · have hGu := hG.2 u
      by_cases hr : isAuthRecvQuery q
      · have hg : SignalPqxdh.isGameQuery q = true := by
          cases q <;> simp_all [isAuthRecvQuery, SignalPqxdh.isGameQuery]
        simp only [hr, ↓reduceIte]
        simp only [hg, ↓reduceIte] at hGu
        exact ih u (n - 1) hGu
      · simp only [hr, ↓reduceIte]
        by_cases hg : SignalPqxdh.isGameQuery q = true
        · simp only [hg, ↓reduceIte] at hGu
          exact (ih u (n - 1) hGu).mono (Nat.sub_le n 1)
        · simp only [hg] at hGu
          exact ih u n hGu

private theorem isQueryBoundP_authRecv_min {S : Setup} {α : Type}
    (mx : OracleComp (unifSpec + authSpec S) α) {rem R : Nat}
    (hG : IsQueryBoundP mx (fun q => SignalPqxdh.isGameQuery q = true) rem)
    (hR : IsQueryBoundP mx isAuthRecvQuery R) :
    IsQueryBoundP mx isAuthRecvQuery (min rem R) := by
  by_cases h : rem ≤ R
  · rw [Nat.min_eq_left h]
    exact isQueryBoundP_authRecv_of_game mx rem hG
  · rw [Nat.min_eq_right (by omega)]
    exact hR

private theorem prfMsgKeysInitDslK_eval (S : Setup) (K : Nat) (u : Ty.denote .unit) :
    (prfMsgKeysInitDslK S K).eval (.cons u .nil) =
      toDslMk (embedUnifMk (RoKem.sampleIndexRange (min K S.N_sess_tot)) >>= fun idx =>
        embedUnifMk ($ᵗ Bool) >>= fun secb =>
          pure ((), mkStToVal (min K S.N_recv_tot + 1) secb idx false
            (AuthHybridStateFixed.empty S secb))) := by
  simp only [prfMsgKeysInitDslK, bindV, v, Comp.eval, Expr.eval, Ext.step_wk, Ext.refl_wk,
    Env.get_succ, Env.get_zero, sampleChal_index_eval, sampleChal_bool_eval,
    toDslMk_bind, toDslMk_pure]
  refine bind_congr fun idx => bind_congr fun secb => ?_
  rfl

/-- Evaluation equivalence for `prfMsgKeysRedProg1Key` on any adversary with bounded game and
    receive queries. -/
theorem prfMsgKeysRedProg1Key_eval_eq_of_bound (S : Setup) (K : Nat)
    (A : AuthAdversary S) (rem : Nat)
    (hG : IsQueryBoundP A.run (fun q => SignalPqxdh.isGameQuery q = true) rem)
    (hR : IsQueryBoundP A.run isAuthRecvQuery S.N_recv_tot)
    (hK : rem ≤ K) :
    (prfMsgKeysRedProg1Key S K).eval (fun _ => A.run) () =
      (do
        let idx ← embedUnifMk (RoKem.sampleIndexRange (min K S.N_sess_tot))
        authMkReductionRun1Key S idx A) := by
  change ((do
      let q ← (prfMsgKeysInitDslK S K).eval (.cons () .nil)
      let r ← (simulateQ (handlerImpl (C := authCodec S) (prfMsgKeysHandle1KeyDsl S K)) A.run).run q.2
      (prfMsgKeysFinishDsl S K).eval (.cons r.2 (.cons r.1 .nil))) :
      OracleComp (PrimBaseSpec + msgKeyPrfOracle.spec) Bool) =
    toDslMk (do
      let idx ← embedUnifMk (RoKem.sampleIndexRange (min K S.N_sess_tot))
      let secb ← embedUnifMk ($ᵗ Bool)
      let p ← runWithPrfMkStep (authMkStepReduction1Key S idx) A.run
        (AuthHybridStateFixed.empty S secb) false
      embedPrimMk (finalizeAuthFixedPrim S secb p.1.1 p.1.2.toAuthHybridState))
  rw [prfMsgKeysInitDslK_eval]
  simp only [toDslMk_bind, toDslMk_pure, bind_assoc, pure_bind]
  refine bind_congr fun idx => bind_congr fun secb => ?_
  exact prfMk1Key_runBridge S K secb idx
    (fun q => (prfMsgKeysFinishDsl S K).eval (.cons q.2 (.cons q.1 .nil)))
    (fun x => embedPrimMk (finalizeAuthFixedPrim S secb x.1.1 x.1.2.toAuthHybridState))
    (fun a hst sc bud hB => prfMsgKeysFinishDsl_eval S K secb idx sc hst bud a hB)
    A.run rem (min rem S.N_recv_tot) 0 (min K S.N_recv_tot + 1)
    (AuthHybridStateFixed.empty S secb) false
    hG (isQueryBoundP_authRecv_min A.run hG hR) (authListsBounded_empty S secb) (by omega)
    (by simp only [Bool.false_eq_true, ↓reduceIte]; omega)

/-- End-to-end evaluation equivalence between `prfMsgKeysRedProg1Key` and
    `prfMsgKeysReductionAuthFixed1Key`. -/
theorem prfMsgKeysRedProg1Key_eval_eq (S : Setup) (b : QueryBudget)
    (A : BoundedAdv (AuthAdversary S) b) :
    (prfMsgKeysRedProg1Key S b.q_total).eval (fun _ => A.1.run) () =
      (prfMsgKeysReductionAuthFixed1Key S b A).run := by
  exact prfMsgKeysRedProg1Key_eval_eq_of_bound S b.q_total A.1 b.q_total
    (SignalPqxdh.QueryBounded.auth_total A.2) (SignalPqxdh.QueryBounded.auth_recv A.2) le_rfl

/-- The `ReductionDsl` reduction as a `PrfMsgKeysAdv` (same budgets as
    `prfMsgKeysReductionAuthFixed1Key`). -/
def prfMsgKeys1KeyDslAdv (S : Setup) (b : QueryBudget)
    (A : BoundedAdv (AuthAdversary S) b) : PrfMsgKeysAdv where
  run := (prfMsgKeysRedProg1Key S b.q_total).eval (fun _ => A.1.run) ()
  q_prf := (prfMsgKeysReductionAuthFixed1Key S b A).q_prf
  q_prim := (prfMsgKeysReductionAuthFixed1Key S b A).q_prim

theorem prfMsgKeys1KeyDslAdv_eq (S : Setup) (b : QueryBudget) (A : BoundedAdv (AuthAdversary S) b) :
    prfMsgKeys1KeyDslAdv S b A = prfMsgKeysReductionAuthFixed1Key S b A := by
  have h := prfMsgKeysRedProg1Key_eval_eq S b A
  simp only [prfMsgKeys1KeyDslAdv, h]

theorem prfMsgKeysRedProg1Key_prfMsgKeys_eq (P : Primitives) (S : Setup) (b : QueryBudget)
    (A : BoundedAdv (AuthAdversary S) b) :
    PrfMsgKeys P (prfMsgKeys1KeyDslAdv S b A) = PrfMsgKeys P (prfMsgKeysReductionAuthFixed1Key S b A) := by
  rw [prfMsgKeys1KeyDslAdv_eq]

section PrfMk1KeyCost

variable (S : Setup) (K : Nat) {Γ₁ Γ₂ Δ : List PT}

theorem prfMkStepPre1KeyC_cost_le (core : Var Γ₁ prfMkCoreTy) (q : Var Γ₂ authQueryTy)
    [Ext Γ₁ Δ] [Ext Γ₂ Δ] :
    (prfMkStepPre1KeyC (Δ := Δ) S K core q).cost ≤ (prfMkStepPreC (Δ := Δ) S K core q).cost := by
  simp only [prfMkStepPre1KeyC, prfMkStepPreC, letV, Comp.letC, caseSumV, wrapMkBase, bindV,
    Comp.cost]
  gcongr
  exact initPrin1KeyFixedB_cost_le K _ _

theorem prfMkStepPre1KeyC_queries_le (core : Var Γ₁ prfMkCoreTy) (q : Var Γ₂ authQueryTy)
    [Ext Γ₁ Δ] [Ext Γ₂ Δ] (w : pqPrimIface.Tag → ℕ) (ws : pqPrimIface.smp.Samp → ℕ) :
    (prfMkStepPre1KeyC (Δ := Δ) S K core q).queries w ws ≤
      (prfMkStepPreC (Δ := Δ) S K core q).queries w ws := by
  simp only [prfMkStepPre1KeyC, prfMkStepPreC, letV, Comp.letC, caseSumV, wrapMkBase, bindV,
    Comp.queries]
  gcongr
  exact initPrin1KeyFixedB_queries_le K _ _ w ws

end PrfMk1KeyCost

theorem cost_liftPrimComp_mono {Γ : List PT} {t : PT}
    (c c' : Comp pqxdhOps pqPrimIface Γ t) (h : c.cost ≤ c'.cost) :
    (liftPrimComp (C := msgKeyPrfOracle) c).cost ≤ (liftPrimComp (C := msgKeyPrfOracle) c').cost := by
  simpa [cost_liftPrimComp] using h

theorem queries_liftPrimComp_gen {C : ChallengerOracle} {Γ : List PT} {t : PT}
    (w : (pqChalIface C).Tag → ℕ) (ws : pqPrimIface.smp.Samp → ℕ)
    (c : Comp pqxdhOps pqPrimIface Γ t) :
    (liftPrimComp (C := C) c).queries w ws = c.queries (fun g => w (.inl g)) ws := by
  induction c with
  | ret _ => rfl
  | bind _ _ ih1 ih2 => simp [liftPrimComp, Comp.queries, ih1, ih2]
  | ite _ _ _ ih1 ih2 => simp [liftPrimComp, Comp.queries, ih1, ih2]
  | caseOpt _ _ _ ih1 ih2 => simp [liftPrimComp, Comp.queries, ih1, ih2]
  | caseSum _ _ _ ih1 ih2 => simp [liftPrimComp, Comp.queries, ih1, ih2]
  | sample _ _ => rfl
  | query _ _ => rfl
  | iter _ _ _ ih => simp [liftPrimComp, Comp.queries, ih]
  | findM _ _ _ ih => simp [liftPrimComp, Comp.queries, ih]
  | anyM _ _ _ ih => simp [liftPrimComp, Comp.queries, ih]
  | mapM _ _ _ ih => simp [liftPrimComp, Comp.queries, ih]
  | consumeFirstM _ _ _ _ ih => simp [liftPrimComp, Comp.queries, ih]
  | foldM _ _ _ _ ih => simp [liftPrimComp, Comp.queries, ih]

theorem prfMsgKeysHandle1KeyDsl_cost_le (S : Setup) (K : Nat) :
    (prfMsgKeysHandle1KeyDsl S K).cost ≤ (prfMsgKeysHandleDsl S K).cost := by
  simp only [prfMsgKeysHandle1KeyDsl, prfMsgKeysHandleDsl, letV, Comp.letC, bindV, caseSumV,
    Comp.cost]
  gcongr
  exact cost_liftPrimComp_mono _ _ (prfMkStepPre1KeyC_cost_le S K _ _)

theorem prfMsgKeysHandle1KeyDsl_queries_le (S : Setup) (K : Nat)
    (w : pqPrfMkIface.Tag → ℕ) (ws : pqPrfMkIface.smp.Samp → ℕ) :
    (prfMsgKeysHandle1KeyDsl S K).queries w ws ≤ (prfMsgKeysHandleDsl S K).queries w ws := by
  simp only [prfMsgKeysHandle1KeyDsl, prfMsgKeysHandleDsl, letV, Comp.letC, bindV, caseSumV,
    Comp.queries]
  gcongr
  erw [queries_liftPrimComp_gen (C := msgKeyPrfOracle), queries_liftPrimComp_gen (C := msgKeyPrfOracle)]
  exact prfMkStepPre1KeyC_queries_le S K _ _ _ ws

theorem prfMsgKeysRedProg1Key_totalCost_le (S : Setup) (K q : Nat) :
    (prfMsgKeysRedProg1Key S K).totalCost q ≤ (prfMsgKeysRedProg S K).totalCost q := by
  have h := prfMsgKeysHandle1KeyDsl_cost_le S K
  simp only [CostedReduction.totalCost, prfMsgKeysRedProg1Key, prfMsgKeysRedProg]
  gcongr
  exact h

theorem prfMsgKeysRedProg1Key_totalQueries_le (S : Setup) (K : Nat)
    (w : pqPrfMkIface.Tag → ℕ) (ws : pqPrfMkIface.smp.Samp → ℕ) (q : Nat) :
    (prfMsgKeysRedProg1Key S K).totalQueries w ws q ≤ (prfMsgKeysRedProg S K).totalQueries w ws q := by
  have h := prfMsgKeysHandle1KeyDsl_queries_le S K w ws
  simp only [CostedReduction.totalQueries, prfMsgKeysRedProg1Key, prfMsgKeysRedProg]
  gcongr
  exact h

end SignalPqxdh.Security.ReductionDsl.AuthPrf
