/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Computational.Proofs.SignalPqxdh.Security.ReductionDsl.Auth1KeyAeadCpa
public import Computational.Proofs.SignalPqxdh.Security.ReductionDsl.AuthPrfHmacEval
public import Computational.Proofs.SignalPqxdh.Security.ReductionDsl.AuthPrfHmacProofs
public import Computational.Proofs.SignalPqxdh.Security.ReductionDsl.AuthPrfHmacLeaves
public import Computational.Proofs.SignalPqxdh.Security.ReductionDsl.AuthPrfHmacShallow
public import Computational.Proofs.SignalPqxdh.Security.ReductionDsl.AuthPrfHmacMu
public import Computational.Proofs.SignalPqxdh.Security.ReductionDsl.Auth1KeyPrfMk
public import Computational.Proofs.SignalPqxdh.Security.AuthSubHops4to5M1
public import Computational.Proofs.SignalPqxdh.Security.AuthSubHops4to5
public import Computational.Proofs.SignalPqxdh.Security.AuthPrfHmacA
public import VCVio.EvalDist.Monad.Basic

/-!
# One-Key `PrfHmac` `ReductionDsl` Program

Defines `prfHmacRedProg1Key` by replacing the `.initPrin` branch of `prfHmacRedProg` with
`initPrin1KeyFixedB`, and proves evaluation equivalence with the shallow simulator
`prfHmacReductionAuth1Key`. Also transfers `.Bounded` compliance and bounds static step cost and
primitive-query counts via `prfHmacRedProg`.
-/

@[expose] public section

set_option autoImplicit false
set_option maxHeartbeats 16000000
set_option maxRecDepth 100000

namespace SignalPqxdh.Security.ReductionDsl.AuthPrfHmac

open _root_.ReductionDsl hiding B PTag U32 bundleOfV bundleT bundleV dhSecretsT drKeyOfV drKeyT drKeyV hdrOfV hdrT hdrV keyIndCodec keyIndQT keyIndQenc keyIndRT keyIndRdec keyIndRenc pqPrimIface pqSigAndDdhIface sampleIndex sidT sidV
open SignalPqxdh SignalPqxdh.LegacyCosted SignalPqxdh.Security
open SignalPqxdh.Security.ReductionDsl SignalPqxdh.Security.ReductionDsl.AuthPrf
open SignalPqxdh.Security.ReductionDsl.AuthAead
open FgGapDh
open OracleSpec OracleComp

section Hm1KeyBranches

variable (S : Setup) (K : Nat) {Γ₁ Γ₂ Γ₃ Γ₄ Δ : List PT}

/-- `hmDispatchC` with the `.initPrin` branch replaced by `initPrin1KeyFixedB`. -/
def hmDispatch1KeyC (jt : Var Γ₁ .nat) (fhst : Var Γ₂ authHybridStateFixedTy) (mst : Var Γ₃ muStTy)
    (q : Var Γ₄ authQueryTy) [Ext Γ₁ Δ] [Ext Γ₂ Δ] [Ext Γ₃ Δ] [Ext Γ₄ Δ] :
    Comp pqxdhOps pqPrimIface Δ hmPreTy :=
  caseSumV (v q) (fun u => hmOther mst (initPrin1KeyFixedB K fhst u)) fun q =>
  caseSumV (v q) (fun u => hmOther mst (corruptFixedB K fhst u)) fun q =>
  caseSumV (v q) (fun x => hmOther mst (genSpkFixedB K fhst x)) fun q =>
  caseSumV (v q) (fun x => hmOther mst (genOpkFixedB K fhst x)) fun q =>
  caseSumV (v q) (fun x => hmSendC S K true jt fhst mst x) fun q =>
  caseSumV (v q) (fun x => hmSendC S K false jt fhst mst x) fun q =>
  caseSumV (v q) (fun x => hmRecvC S K true jt fhst mst x) fun q =>
  caseSumV (v q) (fun x => hmRecvC S K false jt fhst mst x) fun q =>
  caseSumV (v q) (fun sec => hmOther mst (roFixedB K fhst sec)) fun q =>
  caseSumV (v q) (fun x => hmOther mst (roRootFixedB K fhst x)) fun q =>
  caseSumV (v q) (fun _ => .ret (.inl (.pair (.pair aNone (v fhst)) (v mst)))) fun sk =>
  hmOther mst (registerFixedB fhst sk)

end Hm1KeyBranches

section Prog1Key

variable (S : Setup) (K : Nat)

def hmPre1KeyC : Comp pqxdhOps pqPrimIface [hmStTy, authQueryTy] hmPreTy :=
  letV (.var .zero : Expr pqxdhOps [hmStTy, authQueryTy] hmStTy) fun s =>
  letV (.fst (v s)) fun jt =>
  letV (.fst (.snd (v s))) fun fhst =>
  letV (.snd (.snd (v s))) fun mst =>
  hmDispatch1KeyC S K jt fhst mst
    (.succ (.succ (.succ (.succ (.succ .zero)))) :
      Var [muStTy, authHybridStateFixedTy, .nat, hmStTy, hmStTy, authQueryTy] authQueryTy)

def hmHandle1KeyC : Comp pqxdhOps pqPrfHmacIface [hmStTy, authQueryTy] (.prod authRespTy hmStTy) :=
  bindV (liftPrimComp (hmPre1KeyC S K)) fun pre =>
  letV (.fst (.var (.succ .zero)) : Expr pqxdhOps [hmPreTy, hmStTy, authQueryTy] .nat) fun jt =>
  caseSumV (v pre)
    (fun r => .ret (.pair (.fst (.fst (v r)))
      (.pair (v jt) (.pair (.snd (.fst (v r))) (.snd (v r))))))
    fun c =>
      bindV (queryHmacEval (hmContX0E (v c))) fun t =>
      bindV (liftPrimComp (hmPostC K (.pair (v c) (v t)))) fun r =>
      .ret (.pair (.fst (.fst (v r)))
        (.pair (v jt) (.pair (.snd (.fst (v r))) (.snd (v r)))))

/-- `ReductionDsl` reduction program for `prfHmacReductionAuth1Key S b` (list bound `K`). -/
def prfHmacRedProg1Key :
    CostedReduction pqxdhOps pqPrfHmacIface (authSpec S) (authCodec S) .unit .unit .bool .bool where
  σ      := hmStTy
  init   := hmInitC S
  handle := hmHandle1KeyC S K
  finish := hmFinishC K

end Prog1Key

def hmPre1Key (S : Setup) (jt : ℕ) (q : AuthQuery S) (hst : AuthHybridStateFixed S)
    (mst : PrfHmacMuState) : OracleComp PrimBaseSpec (HmRes S ⊕ HmSendCont S) :=
  match q with
  | .initPrin u => (fun r => .inl (r, mst)) <$> stepAuthOtherPrim1Key true S (.initPrin u) hst
  | q => hmPre S jt q hst mst

theorem hmPre1Key_eq_of_ne (S : Setup) (jt : ℕ) (q : AuthQuery S) (hq : AuthQuery.NotInitPrin q)
    (hst : AuthHybridStateFixed S) (mst : PrfHmacMuState) :
    hmPre1Key S jt q hst mst = hmPre S jt q hst mst := by
  cases q <;> first | exact absurd rfl (hq _) | rfl

theorem stepAuthMuPrim1Key_eq_of_ne (S : Setup) (q : AuthQuery S) (hq : AuthQuery.NotInitPrin q)
    (hst : AuthHybridStateFixed S) :
    stepAuthMuPrim1Key S q hst = stepAuthMuPrim S q hst := by
  cases q <;> first | exact absurd rfl (hq _) | rfl

theorem prfMuRun_stepAuthMuPrim1Key (S : Setup) (jt : ℕ) (q : AuthQuery S)
    (hst : AuthHybridStateFixed S) (mst : PrfHmacMuState) :
    prfMuRun jt (stepAuthMuPrim1Key S q hst) mst =
      embedPrim (spec := prfHmacSpec) (hmPre1Key S jt q hst mst) >>= hmResume := by
  by_cases hq : AuthQuery.NotInitPrin q
  · rw [stepAuthMuPrim1Key_eq_of_ne S q hq hst, hmPre1Key_eq_of_ne S jt q hq hst mst]
    exact prfMuRun_stepAuthMuPrim S jt q hst mst
  · obtain ⟨u, rfl⟩ : ∃ u, q = .initPrin u := by
      by_contra hne; push Not at hne; exact hq hne
    simp only [stepAuthMuPrim1Key, hmPre1Key]
    rw [prfMuRun_embedPrimMu, embedPrim_map, bind_map_left]
    simp only [hmResume, bind_pure_comp]

theorem hmPre1Key_leaves (S : Setup) (n jt : Nat) (q : AuthQuery S) (hst : AuthHybridStateFixed S)
    (ms : PrfHmacMuState) (hI : HmInv n hst ms) :
    AllLeaves (HmPreLeaf n) (hmPre1Key S jt q hst ms) := by
  by_cases hq : AuthQuery.NotInitPrin q
  · rw [hmPre1Key_eq_of_ne S jt q hq hst ms]
    exact hmPre_leaves S n jt q hst ms hI
  · obtain ⟨u, rfl⟩ : ∃ u, q = .initPrin u := by
      by_contra hne; push Not at hne; exact hq hne
    have hC : CpaInv n hst := ⟨hI.bnd, hI.won⟩
    have hL := stepAuthCpaNonSendPrim1Key_leaves S n (.initPrin u) hst hC
    simp only [hmPre1Key]
    exact AllLeaves.map' _ hL
      (fun x hx => (⟨hx.bnd, hx.won, hI.mu.mono (Nat.le_succ n)⟩ : HmInv (n + 1) _ _))

section Dispatch

variable (S : Setup) (K : Nat)

theorem hmPre1KeyC_eval_inr (sv : hmStTy.denote) (y : _) (qv : authQueryTy.denote)
    (hq : qv = Sum.inr y) :
    (hmPre1KeyC S K).eval (.cons sv (.cons qv .nil)) =
      (hmPreC S K).eval (.cons sv (.cons qv .nil)) := by
  subst hq
  simp only [hmPre1KeyC, hmPreC, hmDispatch1KeyC, hmDispatchC, letV, eval_letC, caseSumV, v,
    Comp.eval, Expr.eval, Ext.step_wk, Ext.refl_wk, Env.get_succ, Env.get_zero]

set_option maxHeartbeats 4000000 in
theorem hmPre1KeyC_eval (jt : Nat) (q : AuthQuery S) (hst : AuthHybridStateFixed S)
    (ms : PrfHmacMuState) (hB : AuthListsBounded K hst)
    (hw : hst.toAuthHybridState.base.hasWonAuth = false) (hM : MuBounded K ms) :
    (hmPre1KeyC S K).eval (.cons (hmStToVal jt hst ms) (.cons (authQueryToVal q) .nil)) =
      hmPreToVal <$> hmPre1Key S jt q hst ms := by
  by_cases hq : AuthQuery.NotInitPrin q
  · obtain ⟨y, hy⟩ : ∃ y, authQueryToVal q = Sum.inr y := by
      cases q with
      | initPrin u => exact absurd rfl (hq u)
      | _ => exact ⟨_, rfl⟩
    rw [hmPre1KeyC_eval_inr S K _ y _ hy, hmPreC_eval S K jt q hst ms hB hw hM,
      hmPre1Key_eq_of_ne S jt q hq hst ms]
  · obtain ⟨u, rfl⟩ : ∃ u, q = .initPrin u := by
      by_contra hne; push Not at hne; exact hq hne
    simp only [hmPre1KeyC, hmDispatch1KeyC, letV_eval, caseSumV, v, Comp.eval, Expr.eval,
      Ext.step_wk, Ext.refl_wk, Env.get_succ, Env.get_zero, authQueryToVal, authQenc, hmStToVal]
    refine (hmOther_eval_v2 S _ _ ms rfl _ _
      (initPrin1KeyFixedB_eval S K _ _ _ hst u rfl rfl hB)).trans ?_
    simp only [hmPre1Key]
    rw [stepAuthOtherPrim1Key_cpa_initPrin u hst hw]

end Dispatch

section Handle

variable (S : Setup) (K : Nat)

set_option maxHeartbeats 4000000 in
theorem hmHandle1KeyC_eval (n jt : Nat) (q : AuthQuery S) (hst : AuthHybridStateFixed S)
    (ms : PrfHmacMuState) (hI : HmInv n hst ms) (hn : n ≤ K) :
    (hmHandle1KeyC S K).eval (.cons (hmStToVal jt hst ms) (.cons (authQueryToVal q) .nil)) =
      hmOutToVal jt <$>
        (embedPrim (spec := prfHmacSpec) (hmPre1Key S jt q hst ms) >>= hmResume) := by
  have hI' := hI.mono hn
  simp only [hmHandle1KeyC, bindV_eval, letV_eval, caseSumV, v, liftPrimComp_prfHmac_eval,
    Comp.eval, Expr.eval, Ext.step_wk, Ext.refl_wk, Env.get_succ, Env.get_zero]
  rw [hmPre1KeyC_eval S K jt q hst ms hI'.bnd hI'.won hI'.mu, embedPrim_map]
  erw [bind_map_left]
  rw [map_eq_bind_pure_comp, bind_assoc]
  refine hm_bind_congr_leaves (AllLeaves.embedPrim (hmPre1Key_leaves S n jt q hst ms hI))
    fun p hp => ?_
  rcases p with r | c
  · rfl
  · simp only [hmPreToVal, hmResume, queryHmacEval_eval]
    have hcB : c.Bounded n := hp
    rw [hmContX0E_eval _ _ c rfl]
    simp only [prfHmacEvalQ, map_eq_bind_pure_comp, bind_assoc, Function.comp_apply, pure_bind]
    refine bind_congr fun t => ?_
    rw [hmPostC_eval S K _ _ c t rfl (Nat.le_trans hcB.pending_le hn)]
    simp only [embedPrim_pure]
    erw [pure_bind]
    rfl

end Handle

section Run

variable (S : Setup) (K : Nat)

theorem hmStep1Key_leaves (n jt : Nat) (q : AuthQuery S) (hst : AuthHybridStateFixed S)
    (ms : PrfHmacMuState) (hI : HmInv n hst ms) :
    AllLeaves (fun r : HmRes S => HmInv (n + 1) r.1.2 r.2)
      (embedPrim (spec := prfHmacSpec) (hmPre1Key S jt q hst ms) >>= hmResume) := by
  refine AllLeaves.bind (AllLeaves.embedPrim (hmPre1Key_leaves S n jt q hst ms hI)) fun p hp => ?_
  rcases p with r | c
  · exact AllLeaves.pure hp
  · have hcB : c.Bounded n := hp
    simp only [hmResume, map_eq_bind_pure_comp]
    exact AllLeaves.bind_const _ fun t => AllLeaves.pure (hcB.post_inv t)

/-- The DSL step function of `CostedReduction.eval` for `prfHmacRedProg1Key`. -/
def hmDslStep1Key :
    (q : AuthQuery S) → hmStTy.denote →
      OracleComp PrfHmacSimSpec ((authSpec S).Range q × hmStTy.denote) :=
  fun q st => do
    let p ← (hmHandle1KeyC S K).eval (.cons st (.cons (authQueryToVal q) .nil))
    return (valToAuthResp p.1, p.2)

theorem simulateQ_prfHmacRedProg1Key_impl_eq {α : Type}
    (mx : OracleComp (unifSpec + authSpec S) α) (st : (prfHmacRedProg1Key S K).σ.denote) :
    (simulateQ (prfHmacRedProg1Key S K).impl mx).run st =
      runWithPrfHmacStep (hmDslStep1Key S K) mx st := by
  induction mx using OracleComp.inductionOn generalizing st with
  | pure a => rfl
  | query_bind q k ih =>
    rw [simulateQ_query_bind, StateT.run_bind]
    rcases q with uq | gq
    · change ((do let u ← pqPrfHmacIface.fwdU uq; return (u, st)) >>=
          fun x => (simulateQ (prfHmacRedProg1Key S K).impl (k x.1)).run x.2) =
        (liftM (OracleSpec.query (spec := PrfHmacSimSpec) (Sum.inl (Sum.inl uq))) >>=
          fun u => runWithPrfHmacStep (hmDslStep1Key S K) (k u) st)
      rw [bind_assoc]
      congr 1; funext u
      rw [pure_bind, ih u st]
    · change (hmDslStep1Key S K gq st >>=
          fun x => (simulateQ (prfHmacRedProg1Key S K).impl (k x.1)).run x.2) =
        (hmDslStep1Key S K gq st >>=
          fun x => runWithPrfHmacStep (hmDslStep1Key S K) (k x.1) x.2)
      congr 1; funext x
      exact ih x.1 x.2

theorem hm_runBridge1Key (jt : Nat) {α β : Type}
    (f : α × hmStTy.denote → OracleComp PrfHmacSimSpec β)
    (g : α × (AuthHybridStateFixed S × PrfHmacMuState) → OracleComp PrfHmacSimSpec β)
    (hfg : ∀ a hst ms, HmInv K hst ms → f (a, hmStToVal jt hst ms) = g (a, (hst, ms)))
    (mx : OracleComp (unifSpec + authSpec S) α) :
    ∀ (n m : Nat) (hst : AuthHybridStateFixed S) (ms : PrfHmacMuState),
      IsQueryBoundP mx (fun q => isGameQuery q = true) n →
      HmInv m hst ms → m + n ≤ K →
      (runWithPrfHmacStep (hmDslStep1Key S K) mx (hmStToVal jt hst ms) >>= f) =
        (runWithPrfHmacStep (fuseStep jt (stepAuthMuPrim1Key S)) mx (hst, ms) >>= g) := by
  induction mx using OracleComp.inductionOn with
  | pure a =>
    intro n m hst ms _ hI hmK
    change (pure (a, hmStToVal jt hst ms) >>= f) = (pure (a, (hst, ms)) >>= g)
    simp only [pure_bind]
    exact hfg a hst ms (hI.mono (by omega))
  | query_bind q k ih =>
    intro n m hst ms hG hI hmK
    rw [isQueryBoundP_query_bind_iff] at hG
    rcases q with uq | gq
    · obtain ⟨_, hG⟩ := hG
      simp only [SignalPqxdh.isGameQuery, Bool.false_eq_true, ↓reduceIte] at hG
      rw [runWithPrfHmacStep_query_inl, runWithPrfHmacStep_query_inl, bind_assoc, bind_assoc]
      refine bind_congr fun u => ?_
      exact ih u n m hst ms (hG u) hI hmK
    · obtain ⟨hG0, hG⟩ := hG
      simp only [SignalPqxdh.isGameQuery, ↓reduceIte] at hG hG0
      have hn : 0 < n := by
        rcases hG0 with h | h
        · exact absurd trivial h
        · exact h
      obtain ⟨n', rfl⟩ : ∃ n', n = n' + 1 := ⟨n - 1, by omega⟩
      simp only [Nat.add_sub_cancel] at hG
      rw [runWithPrfHmacStep_query_inr, runWithPrfHmacStep_query_inr, bind_assoc, bind_assoc]
      simp only [hmDslStep1Key, fuseStep]
      rw [hmHandle1KeyC_eval S K m jt gq hst ms hI (by omega), prfMuRun_stepAuthMuPrim1Key]
      have hL := hmStep1Key_leaves S m jt gq hst ms hI
      generalize (embedPrim (spec := prfHmacSpec) (hmPre1Key S jt gq hst ms) >>= hmResume) = X
        at hL ⊢
      simp only [map_eq_bind_pure_comp, bind_assoc, Function.comp_apply, pure_bind]
      refine hm_bind_congr_leaves hL fun x hx => ?_
      simp only [hmOutToVal, valToAuthResp_authRespToVal]
      exact ih x.1.1 n' (m + 1) x.1.2 x.2 (hG x.1.1) hx (by omega)

/-- Shallow `prfHmacReductionAuth1Key` computation parameterized by an adversary computation. -/
def prfHmacReductionAuthRun1Key (runA : OracleComp (unifSpec + authSpec S) Bool) :
    OracleComp PrfHmacSimSpec Bool := do
  let j ← prfHmacUnif (RoKem.sampleIndexRange (S.N_send_tot + S.N_recv_tot))
  let (_, st) ← prfMuRun j (aeadMuIntReductionAuthRun1Key S ⟨runA⟩) {}
  let hit ← prfHmacFinish j st.pending (st.pending.map (fun e => (e.1, e.2.1))).dedup
  return (st.bad || hit)

theorem prfHmacRedProg1Key_eval_eq_of_isQueryBoundP
    (A : Unit → OracleComp (unifSpec + authSpec S) Bool)
    (hG : IsQueryBoundP (A ()) (fun q => isGameQuery q = true) K) :
    (prfHmacRedProg1Key S K).eval A () = prfHmacReductionAuthRun1Key S (A ()) := by
  unfold CostedReduction.eval prfHmacReductionAuthRun1Key aeadMuIntReductionAuthRun1Key
  change (do
      let as ← (hmInitC S).eval (.cons () .nil)
      let bs ← (simulateQ (prfHmacRedProg1Key S K).impl (A as.1)).run as.2
      (hmFinishC K).eval (.cons bs.2 (.cons bs.1 .nil)) :
      OracleComp PrfHmacSimSpec Bool) = _
  rw [hmInitC_eval]
  simp only [bind_assoc, pure_bind]
  refine bind_congr fun jt => ?_
  rw [prfMuRun_bind, unifMu, prfMuRun_embedPrimMu]
  simp only [map_eq_bind_pure_comp, bind_assoc, Function.comp_apply, pure_bind]
  refine bind_congr fun secb => ?_
  erw [simulateQ_prfHmacRedProg1Key_impl_eq]
  rw [prfMuRun_bind, prfMuRun_runWithMuStep]
  simp only [map_eq_bind_pure_comp, bind_assoc, Function.comp_apply, pure_bind, prfMuRun_pure]
  exact hm_runBridge1Key S K jt
    (fun x => (hmFinishC K).eval (.cons x.2 (.cons x.1 .nil)))
    (fun x => prfHmacFinish jt x.2.2.pending (x.2.2.pending.map (fun e => (e.1, e.2.1))).dedup >>=
      fun hit => pure (x.2.2.bad || hit))
    (fun a hst ms hI => hmFinishC_eval K jt hst ms a hI.mu.pending_le)
    (A ()) K 0 _ _ hG (hmInv_empty S secb) (by omega)

/-- End-to-end evaluation equivalence between `prfHmacRedProg1Key` and `prfHmacReductionAuth1Key`. -/
theorem prfHmacRedProg1Key_eval_eq (b : QueryBudget) (A : BoundedAdv (AuthAdversary S) b) :
    (prfHmacRedProg1Key S b.q_total).eval (fun _ => A.1.run) () =
      (prfHmacReductionAuth1Key S b A).run := by
  rw [prfHmacRedProg1Key_eval_eq_of_isQueryBoundP S b.q_total (fun _ => A.1.run)
    (SignalPqxdh.QueryBounded.auth_total A.2)]
  simp only [prfHmacReductionAuthRun1Key, prfHmacReductionAuth1Key, prfHmacOfMu, prfHmacOfMuRun,
    prfHmacOfMuRunAt_eq, aeadMuIntReductionAuth1Key]
  rfl

end Run

theorem primBounded_stepAuthOtherPrim1Key_initPrin (useRo : Bool) (S : Setup) (u : Fin S.N_id)
    (hst : AuthHybridStateFixed S) :
    PrimBounded (stepAuthOtherPrim1Key useRo S (.initPrin u) hst) 4 := by
  unfold stepAuthOtherPrim1Key
  dsimp only
  split
  · exact primBounded_pure'
  · refine primBounded_bind_le 4 (primBounded_embedUnif sampleScalar32 0) (fun _ => ?_) (by omega)
    exact primBounded_bind_le 0 (primBounded_primQ _) (fun _ => primBounded_pure') (by omega)

theorem muBounded_stepAuthMuPrim1Key (S : Setup) (q : AuthQuery S) (hst : AuthHybridStateFixed S) :
    SignalPqxdh.Security.MuBounded (stepAuthMuPrim1Key S q hst)
      (if isAuthSendQuery (.inr q) then 1 else 0)
      (if isAuthRecvQuery (.inr q) then 1 else 0)
      (perQueryAuthPrimBudget S) := by
  by_cases hq : AuthQuery.NotInitPrin q
  · rw [stepAuthMuPrim1Key_eq_of_ne S q hq hst]
    exact muBounded_stepAuthMuPrim S q hst
  · obtain ⟨u, rfl⟩ : ∃ u, q = .initPrin u := by
      by_contra hne; push Not at hne; exact hq hne
    simp only [stepAuthMuPrim1Key, isAuthSendQuery, isAuthRecvQuery, ↓reduceIte]
    unfold perQueryAuthPrimBudget
    exact muBounded_embedPrimMu _ 0 0 _
      ((primBounded_stepAuthOtherPrim1Key_initPrin true S u hst).mono (by omega))

theorem muBounded_aeadMuIntReductionAuthRun1Key (S : Setup) (b : QueryBudget)
    (A : BoundedAdv (AuthAdversary S) b) :
    SignalPqxdh.Security.MuBounded (aeadMuIntReductionAuthRun1Key S A.1)
      S.N_send_tot S.N_recv_tot (b.q_total * perQueryAuthPrimBudget S + S.N_dh * 5) := by
  unfold aeadMuIntReductionAuthRun1Key
  refine muBounded_bind_le S.N_send_tot S.N_recv_tot
    (b.q_total * perQueryAuthPrimBudget S + S.N_dh * 5)
    (muBounded_unifMu ($ᵗ Bool) 0 0 0) (fun secb => ?_)
  have hStep : SignalPqxdh.Security.MuBounded
      (runWithMuStep (stepAuthMuPrim1Key S) A.1.run (AuthHybridStateFixed.empty S secb))
      S.N_send_tot S.N_recv_tot (b.q_total * perQueryAuthPrimBudget S) :=
    ⟨isQueryBoundP_runWithMuStep_counted isMuEncQuery (fun _ h => by cases h)
      isAuthSendQuery (fun _ h => by cases h) (stepAuthMuPrim1Key S)
      (fun gq st => (muBounded_stepAuthMuPrim1Key S gq st).1)
      A.1.run S.N_send_tot (QueryBounded.auth_send A.2) (AuthHybridStateFixed.empty S secb),
     isQueryBoundP_runWithMuStep_counted isMuForgeQuery (fun _ h => by cases h)
      isAuthRecvQuery (fun _ h => by cases h) (stepAuthMuPrim1Key S)
      (fun gq st => (muBounded_stepAuthMuPrim1Key S gq st).2.1)
      A.1.run S.N_recv_tot (QueryBounded.auth_recv A.2) (AuthHybridStateFixed.empty S secb),
     isQueryBoundP_runWithMuStep_prim
      (stepAuthMuPrim1Key S) (perQueryAuthPrimBudget S)
      (fun gq st => (muBounded_stepAuthMuPrim1Key S gq st).2.2)
      A.1.run b.q_total (QueryBounded.auth_total A.2) (AuthHybridStateFixed.empty S secb)⟩
  exact muBounded_bind_le 0 0 (S.N_dh * 5) hStep (fun _ => muBounded_pure')

/-- The one-key multi-key INT-CTXT simulator respects its declared query bounds. -/
theorem aeadMuIntReductionAuth1Key_bounded (S : Setup) (b : QueryBudget)
    (A : BoundedAdv (AuthAdversary S) b) :
    (aeadMuIntReductionAuth1Key S b A).Bounded :=
  muBounded_aeadMuIntReductionAuthRun1Key S b A

/-- The one-key shallow `PrfHmac` simulator respects its declared query bounds. -/
theorem prfHmacReductionAuth1Key_bounded (S : Setup) (b : QueryBudget)
    (A : BoundedAdv (AuthAdversary S) b) :
    (prfHmacReductionAuth1Key S b A).Bounded :=
  prfHmacOfMu_bounded _ (aeadMuIntReductionAuth1Key_bounded S b A)

section Adv

variable (S : Setup)

/-- The one-key `ReductionDsl` reduction as a `PrfHmacAdv`. -/
def prfHmac1KeyDslAdv (b : QueryBudget) (A : BoundedAdv (AuthAdversary S) b) :
    PrfHmacAdv where
  run := (prfHmacRedProg1Key S b.q_total).eval (fun _ => A.1.run) ()
  q_prf := (prfHmacReductionAuth1Key S b A).q_prf
  q_prim := primQueryBudget S b

theorem prfHmac1KeyDslAdv_run (b : QueryBudget) (A : BoundedAdv (AuthAdversary S) b) :
    (prfHmac1KeyDslAdv S b A).run = (prfHmacReductionAuth1Key S b A).run :=
  prfHmacRedProg1Key_eval_eq S b A

theorem prfHmacRedProg1Key_evalDist_eq (P : Primitives) (b : QueryBudget)
    (A : BoundedAdv (AuthAdversary S) b) :
    𝒟[prfHmacExp P (prfHmac1KeyDslAdv S b A)] =
      𝒟[prfHmacExp P (prfHmacReductionAuth1Key S b A)] := by
  have h : prfHmac1KeyDslAdv S b A =
      { prfHmacReductionAuth1Key S b A with q_prim := primQueryBudget S b } := by
    unfold prfHmac1KeyDslAdv
    rw [prfHmacRedProg1Key_eval_eq]
  rw [h]
  rfl

theorem prfHmac1KeyDslAdv_prfHmac_eq (P : Primitives) (b : QueryBudget)
    (A : BoundedAdv (AuthAdversary S) b) :
    PrfHmac P (prfHmac1KeyDslAdv S b A) = PrfHmac P (prfHmacReductionAuth1Key S b A) := by
  simp only [PrfHmac, prfHmacRedProg1Key_evalDist_eq]

/-- The one-key `ReductionDsl` `PrfHmac` adversary respects its declared budgets. -/
theorem prfHmac1KeyDslAdv_bounded (b : QueryBudget) (A : BoundedAdv (AuthAdversary S) b) :
    (prfHmac1KeyDslAdv S b A).Bounded := by
  obtain ⟨h1, h2⟩ := prfHmacReductionAuth1Key_bounded S b A
  have hq : (prfHmacReductionAuth1Key S b A).q_prim ≤ primQueryBudget S b := by
    unfold prfHmacReductionAuth1Key prfHmacOfMu aeadMuIntReductionAuth1Key perQueryAuthPrimBudget
      primQueryBudget Setup.N_sess_tot
    dsimp only
    nlinarith
  refine ⟨?_, ?_⟩
  · rw [prfHmac1KeyDslAdv_run]; exact h1
  · rw [prfHmac1KeyDslAdv_run]; exact h2.mono hq

end Adv

section Hm1KeyCost

variable (S : Setup) (K : Nat)

theorem hmPre1KeyC_cost_le : (hmPre1KeyC S K).cost ≤ (hmPreC S K).cost := by
  simp only [hmPre1KeyC, hmPreC, hmDispatch1KeyC, hmDispatchC, hmOther, letV, Comp.letC, caseSumV,
    bindV, Comp.cost]
  gcongr
  exact initPrin1KeyFixedB_cost_le K _ _

theorem hmPre1KeyC_queries_le (w : pqPrimIface.Tag → ℕ) (ws : pqPrimIface.smp.Samp → ℕ) :
    (hmPre1KeyC S K).queries w ws ≤ (hmPreC S K).queries w ws := by
  simp only [hmPre1KeyC, hmPreC, hmDispatch1KeyC, hmDispatchC, hmOther, letV, Comp.letC, caseSumV,
    bindV, Comp.queries]
  gcongr
  exact initPrin1KeyFixedB_queries_le K _ _ w ws

theorem hmHandle1KeyC_cost_le : (hmHandle1KeyC S K).cost ≤ (hmHandleC S K).cost := by
  have h := hmPre1KeyC_cost_le S K
  simp only [hmHandle1KeyC, hmHandleC, letV, Comp.letC, bindV, caseSumV, cost_liftPrimComp,
    Comp.cost]
  gcongr

theorem hmHandle1KeyC_queries_le :
    (hmHandle1KeyC S K).queries chalPrimW chalWS ≤ (hmHandleC S K).queries chalPrimW chalWS := by
  have h := hmPre1KeyC_queries_le S K primW primWS
  simp only [hmHandle1KeyC, hmHandleC, letV, Comp.letC, bindV, caseSumV, queries_liftPrimComp_prim,
    Comp.queries]
  gcongr

theorem prfHmacRedProg1Key_totalCost_le (q : Nat) :
    (prfHmacRedProg1Key S K).totalCost q ≤ (prfHmacRedProg S K).totalCost q := by
  have h := hmHandle1KeyC_cost_le S K
  simp only [CostedReduction.totalCost, prfHmacRedProg1Key, prfHmacRedProg]
  gcongr
  exact h

theorem prfHmacRedProg1Key_totalQueries_prim_le (q : Nat) :
    (prfHmacRedProg1Key S K).totalQueries chalPrimW chalWS q ≤
      (prfHmacRedProg S K).totalQueries chalPrimW chalWS q := by
  have h := hmHandle1KeyC_queries_le S K
  simp only [CostedReduction.totalQueries, prfHmacRedProg1Key, prfHmacRedProg]
  gcongr
  exact h

end Hm1KeyCost

private theorem authAeadStepCostBudget_le_legacy (S : Setup) (b : QueryBudget) :
    AuthAead.stepCostBudget S b ≤
      _root_.SignalPqxdh.LegacyCosted.stepCostBudget S b := by
  unfold AuthAead.stepCostBudget _root_.SignalPqxdh.LegacyCosted.stepCostBudget
  nlinarith [Nat.zero_le (b.q_total * S.N_dh), Nat.zero_le (b.q_total * S.N_sess_tot),
    Nat.zero_le (S.N_dh * S.N_sess_tot)]

/-- Step-cost budget for the one-key `PrfHmac` program. -/
theorem prfHmacRedProg1Key_totalCost_budget (S : Setup) (b : QueryBudget) :
    (prfHmacRedProg1Key S b.q_total).totalCost b.q_total ≤
      SignalPqxdh.LegacyCosted.stepCostBudget S b :=
  ((prfHmacRedProg1Key_totalCost_le S b.q_total b.q_total).trans
    (prfHmacRedProg_totalCost_le S b)).trans (authAeadStepCostBudget_le_legacy S b)

/-- Primitive-query budget for the one-key `PrfHmac` program. -/
theorem prfHmacRedProg1Key_totalQueries_budget (S : Setup) (b : QueryBudget) :
    (prfHmacRedProg1Key S b.q_total).totalQueries chalPrimW chalWS b.q_total ≤
      primQueryBudget S b :=
  (prfHmacRedProg1Key_totalQueries_prim_le S b.q_total b.q_total).trans
    (prfHmacRedProg_totalQueries_prim_le S b)

end SignalPqxdh.Security.ReductionDsl.AuthPrfHmac
