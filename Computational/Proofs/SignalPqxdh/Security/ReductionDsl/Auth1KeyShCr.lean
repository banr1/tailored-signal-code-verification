/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Computational.Specifications.Pqxdh.Security.CostedBudgets
public import Computational.Proofs.SignalPqxdh.Security.ReductionDsl.AuthHandshakeShCrLoop
public import Computational.Proofs.SignalPqxdh.Security.ReductionDsl.AuthHandshakeShCrProofs
public import Computational.Proofs.SignalPqxdh.Security.ReductionDsl.AuthCoreSim
public import Computational.Proofs.SignalPqxdh.Security.ReductionDsl.Auth1KeyPrfBase
public import Computational.Proofs.SignalPqxdh.Security.Auth1KeyShallowSims
import Computational.Proofs.SignalPqxdh.Security.ReductionDsl.AuthHandshakeShCrStep
import Computational.Proofs.SignalPqxdh.Security.ReductionDsl.AuthCoreSimSend
import Computational.Proofs.SignalPqxdh.Security.ReductionDsl.AuthCoreSimRecv
import VCVio.EvalDist.Monad.Basic

/-!
# One-Key `Auth` `KemShCr` `ReductionDsl` Program

**Checked by Lean.** Defines `shcrReductionAuthProg1Key` (`shcrReductionAuthProg` with `.initPrin`
replaced by `initPrin1KeyB`), bounds its step cost and primitive queries via the two-key program,
and proves branch evaluation equivalence for `pqxdhAuthShCrPrimImpl1Key true S`.
-/

@[expose] public section

set_option autoImplicit false

namespace SignalPqxdh.Security.ReductionDsl.AuthHs

open _root_.ReductionDsl hiding B PTag U32 bundleOfV bundleT bundleV dhSecretsT drKeyOfV drKeyT drKeyV hdrOfV hdrT hdrV keyIndCodec keyIndQT keyIndQenc keyIndRT keyIndRdec keyIndRenc pqPrimIface pqSigAndDdhIface sampleIndex sidT sidV
open SignalPqxdh SignalPqxdh.LegacyCosted SignalPqxdh.Security SignalPqxdh.Security.ReductionDsl
open OracleSpec OracleComp RoKem

set_option allowUnsafeReducibility true in
attribute [implicit_reducible] authCodec shcrReductionAuthProg

/-! ## Shallow bridge -/

theorem pqxdhAuthSimImplPrim1Key_eq_of_ne {S : Setup} (q : AuthQuery S)
    (hq : AuthPrf.AuthQuery.NotInitPrin q) :
    pqxdhAuthSimImplPrim1Key S q = pqxdhAuthSimImplPrim S q := by
  cases q <;> first | exact absurd rfl (hq _) | rfl

theorem pqxdhAuthShCrPrimImpl1Key_eq_of_ne {S : Setup} (q : AuthQuery S)
    (hq : AuthPrf.AuthQuery.NotInitPrin q) :
    pqxdhAuthShCrPrimImpl1Key true S q = pqxdhAuthShCrPrimImpl true S q := by
  cases q <;> first | exact absurd rfl (hq _) | rfl

theorem pqxdhAuthShCrPrimImpl1Key_initPrin {S : Setup} (u : Fin S.N_id) :
    pqxdhAuthShCrPrimImpl1Key true S (.initPrin u) =
      liftShCrBasePrim (S := S) (pqxdhAuthSimImplPrim1Key S (.initPrin u)) := rfl

/-! ## Program -/

section Branches1Key

variable (S : Setup) (K : Nat) {Γ₁ Γ₂ Δ : List (Ty pqSig)}

def initPrin1KeyB (st : Var Γ₁ authStateTy) (u : Var Γ₂ .nat) [Ext Γ₁ Δ] [Ext Γ₂ Δ] :
    Comp pqxdhOps pqPrimIface Δ RS :=
  .iteC (eAny K (stPrin (v st)) fun e => natEq (.fst (v e)) (v u)) (.ret (rs aNone (v st))) <|
  bindV .sampleBytes32 fun s0 => bindV (.queryPrim .x25519Base (v s0)) fun ik =>
  .ret (rs (aInitPrin (v ik) (v ik)) (stUpd (v st) (prin := .listCons
    (.pair (v u) (peMk (v s0) (v ik) (v s0) (v ik) (.litBool false))) (stPrin (v st)))))

def shcrPost1KeyC (s : Var Γ₁ shcrStTy) (q : Var Γ₂ authQueryTy)
    [Ext Γ₁ Δ] [Ext Γ₂ Δ] : Comp pqxdhOps pqPrimIface Δ SCS :=
  caseSumV (v q) (fun u => onBase s fun g => initPrin1KeyB K g u) fun q =>
  caseSumV (v q) (fun u => onBase s fun g => corruptB K g u) fun q =>
  caseSumV (v q) (fun x => shcrGenSpkB S K s x) fun q =>
  caseSumV (v q) (fun x => onBase s fun g => genOpkB K g x) fun q =>
  caseSumV (v q) (fun x => shcrSendC S K true s x) fun q =>
  caseSumV (v q) (fun x => shcrSendC S K false s x) fun q =>
  caseSumV (v q) (fun x => shcrAcceptB S K true s x) fun q =>
  caseSumV (v q) (fun x => shcrAcceptB S K false s x) fun q =>
  caseSumV (v q) (fun sec => onBase s fun g => roB K g sec) fun q =>
  caseSumV (v q) (fun x => onBase s fun g => roRootB K g x) fun q =>
  caseSumV (v q) (fun _ => .ret (.pair aNone (v s))) fun sk =>
  onBase s fun g => registerB g sk

def shcrPre1KeyC (s : Var Γ₁ shcrStTy) (q : Var Γ₂ authQueryTy)
    [Ext Γ₁ Δ] [Ext Γ₂ Δ] :
    Comp pqxdhOps pqPrimIface Δ (.sum SCS (.prod (B 1568) (.prod pauseTy shcrStTy))) :=
  bindV (pauseCheckC S K s q) fun p =>
  caseOptV (v p) (bindV (shcrPost1KeyC S K s q) fun r => .ret (.inl (v r))) fun d =>
  .ret (.inr (.pair (buPqspkB (pdBu (v d))) (.pair (v d) (v s))))

end Branches1Key

/-- `ReductionDsl` version of `shcrReductionAuthCore1Key S b` (`Q = b.q_total`, list bound `K`). -/
def shcrReductionAuthProg1Key (S : Setup) (Q K : Nat) :
    TwoStageCostedReduction pqxdhOps pqPrimIface (authSpec S) (authCodec S)
      (.prod (B 1568) (B 3168)) .unit .bool (B 1568) (.prod (B 32) (B 1568)) (B 1568) where
  σ := shcrStTy
  π := pauseTy
  init := (shcrReductionAuthProg S Q K).init
  handlePre := shcrPre1KeyC S K (Γ₁ := [shcrStTy, authQueryTy]) (Γ₂ := [authQueryTy])
    (Δ := [shcrStTy, authQueryTy]) .vz .vz
  chDone := (shcrReductionAuthProg S Q K).chDone
  resume := (shcrReductionAuthProg S Q K).resume
  handlePost := shcrPost1KeyC S K (Γ₁ := [shcrStTy, authQueryTy]) (Γ₂ := [authQueryTy])
    (Δ := [shcrStTy, authQueryTy]) .vz .vz
  finish := (shcrReductionAuthProg S Q K).finish

abbrev shcrAuth1KeyDslProg (S : Setup) (b : QueryBudget) :=
  shcrReductionAuthProg1Key S b.q_total b.q_total

set_option allowUnsafeReducibility true in
attribute [implicit_reducible] shcrReductionAuthProg1Key

/-! ## Syntactic cost and query bounds -/

theorem initPrin1KeyB_cost_le (K : Nat) {Γ₁ Γ₂ Δ : List (Ty pqSig)}
    (st : Var Γ₁ authStateTy) (u : Var Γ₂ .nat) [Ext Γ₁ Δ] [Ext Γ₂ Δ] :
    (initPrin1KeyB (Δ := Δ) K st u).cost ≤ (initPrinB (Δ := Δ) K st u).cost := by
  simp only [initPrin1KeyB, initPrinB, bindV, rs, aNone, aInitPrin, stUpd, stMk, peMk,
    stSecb, stHasWon, stPrin, stSpks, stOpks, stSess, stUsedS, stUsedO, stUsedN, stKyb, stSOE,
    stSNE, stROE, stRNE, stRo, stRoot, stAdv, v, Comp.cost, Expr.cost]
  omega

theorem initPrin1KeyB_queries_le (K : Nat) {Γ₁ Γ₂ Δ : List (Ty pqSig)}
    (st : Var Γ₁ authStateTy) (u : Var Γ₂ .nat) [Ext Γ₁ Δ] [Ext Γ₂ Δ]
    (w : pqPrimIface.Tag → ℕ) (ws : pqPrimIface.smp.Samp → ℕ) :
    (initPrin1KeyB (Δ := Δ) K st u).queries w ws ≤ (initPrinB (Δ := Δ) K st u).queries w ws := by
  simp only [initPrin1KeyB, initPrinB, bindV, Comp.queries]
  omega

@[reducible] def authQueryRestTy : Ty pqSig :=
  .sum .nat (.sum (.prod .nat .nat) (.sum (.prod .nat (.prod .nat .nat))
  (.sum (.prod .nat (.prod .nat (.prod bundleT (.prod (B 32) (B 32)))))
  (.sum (.prod .nat (.prod .nat (.prod bundleT (.prod (B 32) (B 32)))))
  (.sum (.prod .nat (.prod .nat (.prod .nat preKeyMsgT)))
  (.sum (.prod .nat (.prod .nat (.prod .nat preKeyMsgT)))
  (.sum (B 192) (.sum (.prod (B 32) (B 32)) (.sum .unit (B 32))))))))))

def shcrPostTailC (S : Setup) (K : Nat) {Γ₁ Δ : List (Ty pqSig)}
    (s : Var Γ₁ shcrStTy) [Ext Γ₁ Δ]
    (q : Var (authQueryRestTy :: Δ) authQueryRestTy) :
    Comp pqxdhOps pqPrimIface (authQueryRestTy :: Δ) SCS :=
  caseSumV (v q) (fun u => onBase s fun g => corruptB K g u) fun q =>
  caseSumV (v q) (fun x => shcrGenSpkB S K s x) fun q =>
  caseSumV (v q) (fun x => onBase s fun g => genOpkB K g x) fun q =>
  caseSumV (v q) (fun x => shcrSendC S K true s x) fun q =>
  caseSumV (v q) (fun x => shcrSendC S K false s x) fun q =>
  caseSumV (v q) (fun x => shcrAcceptB S K true s x) fun q =>
  caseSumV (v q) (fun x => shcrAcceptB S K false s x) fun q =>
  caseSumV (v q) (fun sec => onBase s fun g => roB K g sec) fun q =>
  caseSumV (v q) (fun x => onBase s fun g => roRootB K g x) fun q =>
  caseSumV (v q) (fun _ => .ret (.pair aNone (v s))) fun sk =>
  onBase s fun g => registerB g sk

theorem shcrPostC_eq_tail (S : Setup) (K : Nat) {Γ₁ Γ₂ Δ : List (Ty pqSig)}
    (s : Var Γ₁ shcrStTy) (q : Var Γ₂ authQueryTy) [Ext Γ₁ Δ] [Ext Γ₂ Δ] :
    shcrPostC (Δ := Δ) S K s q =
      caseSumV (v q) (fun u => onBase s fun g => initPrinB K g u) (shcrPostTailC S K s) :=
  rfl

theorem shcrPost1KeyC_eq_tail (S : Setup) (K : Nat) {Γ₁ Γ₂ Δ : List (Ty pqSig)}
    (s : Var Γ₁ shcrStTy) (q : Var Γ₂ authQueryTy) [Ext Γ₁ Δ] [Ext Γ₂ Δ] :
    shcrPost1KeyC (Δ := Δ) S K s q =
      caseSumV (v q) (fun u => onBase s fun g => initPrin1KeyB K g u) (shcrPostTailC S K s) :=
  rfl

theorem onBase_cost_le {Γ₁ Δ : List (Ty pqSig)} (s : Var Γ₁ shcrStTy) [Ext Γ₁ Δ]
    (br₁ br₂ : (g : Var (authStateTy :: Δ) authStateTy) →
      Comp pqxdhOps pqPrimIface (authStateTy :: Δ) RS)
    (h : (br₁ .vz).cost ≤ (br₂ .vz).cost) :
    (onBase (Δ := Δ) s br₁).cost ≤ (onBase (Δ := Δ) s br₂).cost := by
  dsimp only [onBase, bindV, letV, Comp.cost_letC, Comp.cost]
  omega

theorem onBase_queries_le {Γ₁ Δ : List (Ty pqSig)} (s : Var Γ₁ shcrStTy) [Ext Γ₁ Δ]
    (w : pqPrimIface.Tag → ℕ) (ws : pqPrimIface.smp.Samp → ℕ)
    (br₁ br₂ : (g : Var (authStateTy :: Δ) authStateTy) →
      Comp pqxdhOps pqPrimIface (authStateTy :: Δ) RS)
    (h : (br₁ .vz).queries w ws ≤ (br₂ .vz).queries w ws) :
    (onBase (Δ := Δ) s br₁).queries w ws ≤ (onBase (Δ := Δ) s br₂).queries w ws := by
  simp only [onBase, bindV, letV, Comp.queries_letC, Comp.queries]
  omega

theorem caseSumV_cost_le_left {τ₁ τ₂ τ : Ty pqSig} {Γ : List (Ty pqSig)}
    (e : Expr pqxdhOps Γ (.sum τ₁ τ₂))
    (l₁ l₂ : Var (τ₁ :: Γ) τ₁ → Comp pqxdhOps pqPrimIface (τ₁ :: Γ) τ)
    (r : Var (τ₂ :: Γ) τ₂ → Comp pqxdhOps pqPrimIface (τ₂ :: Γ) τ)
    (hl : (l₁ .vz).cost ≤ (l₂ .vz).cost) :
    (caseSumV e l₁ r).cost ≤ (caseSumV e l₂ r).cost := by
  dsimp only [caseSumV, Comp.cost]
  omega

theorem caseSumV_queries_le_left {τ₁ τ₂ τ : Ty pqSig} {Γ : List (Ty pqSig)}
    (w : pqPrimIface.Tag → ℕ) (ws : pqPrimIface.smp.Samp → ℕ)
    (e : Expr pqxdhOps Γ (.sum τ₁ τ₂))
    (l₁ l₂ : Var (τ₁ :: Γ) τ₁ → Comp pqxdhOps pqPrimIface (τ₁ :: Γ) τ)
    (r : Var (τ₂ :: Γ) τ₂ → Comp pqxdhOps pqPrimIface (τ₂ :: Γ) τ)
    (hl : (l₁ .vz).queries w ws ≤ (l₂ .vz).queries w ws) :
    (caseSumV e l₁ r).queries w ws ≤ (caseSumV e l₂ r).queries w ws := by
  dsimp only [caseSumV, Comp.queries]
  omega

theorem shcrPost1KeyC_cost_le (S : Setup) (K : Nat) {Γ₁ Γ₂ Δ : List (Ty pqSig)}
    (s : Var Γ₁ shcrStTy) (q : Var Γ₂ authQueryTy) [Ext Γ₁ Δ] [Ext Γ₂ Δ] :
    (shcrPost1KeyC (Δ := Δ) S K s q).cost ≤ (shcrPostC (Δ := Δ) S K s q).cost := by
  rw [shcrPost1KeyC_eq_tail, shcrPostC_eq_tail]
  refine caseSumV_cost_le_left _ _ _ (shcrPostTailC S K s) ?_
  exact onBase_cost_le s _ _ (initPrin1KeyB_cost_le K (Γ₁ := authStateTy :: .nat :: Δ)
    (Γ₂ := .nat :: Δ) (Δ := authStateTy :: .nat :: Δ) .vz .vz)

theorem shcrPost1KeyC_queries_le (S : Setup) (K : Nat) {Γ₁ Γ₂ Δ : List (Ty pqSig)}
    (s : Var Γ₁ shcrStTy) (q : Var Γ₂ authQueryTy) [Ext Γ₁ Δ] [Ext Γ₂ Δ]
    (w : pqPrimIface.Tag → ℕ) (ws : pqPrimIface.smp.Samp → ℕ) :
    (shcrPost1KeyC (Δ := Δ) S K s q).queries w ws ≤ (shcrPostC (Δ := Δ) S K s q).queries w ws := by
  rw [shcrPost1KeyC_eq_tail, shcrPostC_eq_tail]
  refine caseSumV_queries_le_left w ws _ _ _ (shcrPostTailC S K s) ?_
  exact onBase_queries_le s w ws _ _ (initPrin1KeyB_queries_le K (Γ₁ := authStateTy :: .nat :: Δ)
    (Γ₂ := .nat :: Δ) (Δ := authStateTy :: .nat :: Δ) .vz .vz w ws)

theorem shcrPre1KeyC_cost_le (S : Setup) (K : Nat) {Γ₁ Γ₂ Δ : List (Ty pqSig)}
    (s : Var Γ₁ shcrStTy) (q : Var Γ₂ authQueryTy) [Ext Γ₁ Δ] [Ext Γ₂ Δ] :
    (shcrPre1KeyC (Δ := Δ) S K s q).cost ≤ (shcrPreC (Δ := Δ) S K s q).cost := by
  have h := shcrPost1KeyC_cost_le S K (Γ₁ := Γ₁) (Γ₂ := Γ₂) (Δ := (.opt pauseTy) :: Δ) s q
  simp only [shcrPre1KeyC, shcrPreC, bindV, caseOptV, Comp.cost]
  omega

theorem shcrPre1KeyC_queries_le (S : Setup) (K : Nat) {Γ₁ Γ₂ Δ : List (Ty pqSig)}
    (s : Var Γ₁ shcrStTy) (q : Var Γ₂ authQueryTy) [Ext Γ₁ Δ] [Ext Γ₂ Δ]
    (w : pqPrimIface.Tag → ℕ) (ws : pqPrimIface.smp.Samp → ℕ) :
    (shcrPre1KeyC (Δ := Δ) S K s q).queries w ws ≤ (shcrPreC (Δ := Δ) S K s q).queries w ws := by
  have h := shcrPost1KeyC_queries_le S K (Γ₁ := Γ₁) (Γ₂ := Γ₂) (Δ := (.opt pauseTy) :: Δ) s q w ws
  simp only [shcrPre1KeyC, shcrPreC, bindV, caseOptV, Comp.queries]
  omega

theorem shcrReductionAuthProg1Key_totalCost_le_twoKey (S : Setup) (Q K fuel : Nat) :
    (shcrReductionAuthProg1Key S Q K).totalCost fuel ≤ (shcrReductionAuthProg S Q K).totalCost fuel := by
  have hPre : (shcrReductionAuthProg1Key S Q K).handlePre.cost ≤
      (shcrReductionAuthProg S Q K).handlePre.cost :=
    shcrPre1KeyC_cost_le S K (Γ₁ := [shcrStTy, authQueryTy]) (Γ₂ := [authQueryTy])
      (Δ := [shcrStTy, authQueryTy]) .vz .vz
  have hPost : (shcrReductionAuthProg1Key S Q K).handlePost.cost ≤
      (shcrReductionAuthProg S Q K).handlePost.cost :=
    shcrPost1KeyC_cost_le S K (Γ₁ := [shcrStTy, authQueryTy]) (Γ₂ := [authQueryTy])
      (Δ := [shcrStTy, authQueryTy]) .vz .vz
  have hMax :
      max pqPrimIface.uCost (max (shcrReductionAuthProg1Key S Q K).handlePre.cost
        (shcrReductionAuthProg1Key S Q K).handlePost.cost + (authCodec S).codecCost) ≤
      max pqPrimIface.uCost (max (shcrReductionAuthProg S Q K).handlePre.cost
        (shcrReductionAuthProg S Q K).handlePost.cost + (authCodec S).codecCost) :=
    max_le (le_max_left _ _)
      (le_trans (Nat.add_le_add_right (max_le (le_trans hPre (le_max_left _ _))
        (le_trans hPost (le_max_right _ _))) _) (le_max_right _ _))
  have hMul := Nat.mul_le_mul_left fuel hMax
  unfold TwoStageCostedReduction.totalCost
  change (shcrReductionAuthProg S Q K).init.cost + _ +
      max (shcrReductionAuthProg S Q K).chDone.cost (shcrReductionAuthProg S Q K).resume.cost +
      (shcrReductionAuthProg S Q K).finish.cost ≤ _
  omega

theorem shcrReductionAuthProg1Key_totalQueries_le_twoKey (S : Setup) (Q K fuel : Nat)
    (w : pqPrimIface.Tag → ℕ) (ws : pqPrimIface.smp.Samp → ℕ) :
    (shcrReductionAuthProg1Key S Q K).totalQueries w ws fuel ≤
      (shcrReductionAuthProg S Q K).totalQueries w ws fuel := by
  have hPre : (shcrReductionAuthProg1Key S Q K).handlePre.queries w ws ≤
      (shcrReductionAuthProg S Q K).handlePre.queries w ws :=
    shcrPre1KeyC_queries_le S K (Γ₁ := [shcrStTy, authQueryTy]) (Γ₂ := [authQueryTy])
      (Δ := [shcrStTy, authQueryTy]) .vz .vz w ws
  have hPost : (shcrReductionAuthProg1Key S Q K).handlePost.queries w ws ≤
      (shcrReductionAuthProg S Q K).handlePost.queries w ws :=
    shcrPost1KeyC_queries_le S K (Γ₁ := [shcrStTy, authQueryTy]) (Γ₂ := [authQueryTy])
      (Δ := [shcrStTy, authQueryTy]) .vz .vz w ws
  have hMax :
      max ((shcrReductionAuthProg1Key S Q K).handlePre.queries w ws)
        ((shcrReductionAuthProg1Key S Q K).handlePost.queries w ws) ≤
      max ((shcrReductionAuthProg S Q K).handlePre.queries w ws)
        ((shcrReductionAuthProg S Q K).handlePost.queries w ws) :=
    max_le (le_trans hPre (le_max_left _ _)) (le_trans hPost (le_max_right _ _))
  have hMul := Nat.mul_le_mul_left fuel hMax
  unfold TwoStageCostedReduction.totalQueries
  change (shcrReductionAuthProg S Q K).init.queries w ws + _ +
      max ((shcrReductionAuthProg S Q K).chDone.queries w ws)
        ((shcrReductionAuthProg S Q K).resume.queries w ws) +
      (shcrReductionAuthProg S Q K).finish.queries w ws ≤ _
  omega

theorem shcrAuth1KeyDslProg_totalCost_le (S : Setup) (b : QueryBudget) :
    (shcrAuth1KeyDslProg S b).totalCost b.q_total ≤
      SignalPqxdh.Security.stepCostBudget S b :=
  (shcrReductionAuthProg1Key_totalCost_le_twoKey S b.q_total b.q_total b.q_total).trans
    (shcrReductionAuthProg_totalCost_le_sec S b)

theorem shcrAuth1KeyDslProg_totalQueries_le (S : Setup) (b : QueryBudget) :
    (shcrAuth1KeyDslProg S b).totalQueries primW primWS b.q_total ≤ primQueryBudget S b :=
  (shcrReductionAuthProg1Key_totalQueries_le_twoKey S b.q_total b.q_total b.q_total
    primW primWS).trans (shcrReductionAuthProg_totalQueries_le S b)

/-! ## Branch evaluation and invariants -/

theorem initPrin1KeyB_eval (S : Setup) (K : Nat) {Γ₁ Γ₂ Δ : List (Ty pqSig)} [h₁ : Ext Γ₁ Δ]
    [h₂ : Ext Γ₂ Δ] (env : Env Δ) (s : AuthState S) (st : Var Γ₁ authStateTy)
    (u : Var Γ₂ .nat) (uf : Fin S.N_id)
    (hst : Env.get env (h₁.wk st) = authStateToVal s) (hu : Env.get env (h₂.wk u) = uf.val)
    (hK : AuthBaseListsBounded K s) :
    (initPrin1KeyB K st u).eval env =
      Prod.map authRespToVal authStateToVal <$> (pqxdhAuthSimImplPrim1Key S (.initPrin uf)).run s := by
  unfold initPrin1KeyB
  dsl_unfold
  simp only [hst, hu]
  rw [List.take_of_length_le (by simpa using hK.principals_le)]
  simp only [pqxdhAuthSimImplPrim1Key, authStateToVal, List.any_map, StateT.run_bind,
    StateT.run_get, Function.comp_def, pure_bind, Prod.map_fst, id_eq]
  split
  · simp [*]
  · simp [*, sampleScalar32, map_bind, principalEntryToVal]

set_option maxHeartbeats 1000000 in
theorem pqxdhAuthSimImplPrim1Key_hol (S : Setup) (n : Nat) (q : (authSpec S).Domain)
    (s : AuthState S) (hK : AuthBaseListsBounded n s) :
    HoldsOnLeaves (fun x => AuthBaseListsBounded (n + 1) x.2)
      ((pqxdhAuthSimImplPrim1Key S q).run s) := by
  by_cases hq : AuthPrf.AuthQuery.NotInitPrin q
  · rw [pqxdhAuthSimImplPrim1Key_eq_of_ne q hq]
    exact pqxdhAuthSimImplPrim_hol S n q s hK
  · simp only [AuthPrf.AuthQuery.NotInitPrin, not_forall, not_not] at hq
    obtain ⟨u, rfl⟩ := hq
    have hK' := hK
    obtain ⟨a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11⟩ := hK'
    simp only [pqxdhAuthSimImplPrim1Key]
    hol_full

theorem pqxdhAuthShCrPrimImpl1Key_inv (S : Setup) (pk sk : Bytes) (n : Nat) (q : AuthQuery S)
    (h : AuthShCrState S) (hI : ShInv pk sk n h) :
    HoldsOnLeaves (fun x : AuthResponse × AuthShCrState S => ShInv pk sk (n + 1) x.2)
      ((pqxdhAuthShCrPrimImpl1Key true S q).run h) := by
  by_cases hq : AuthPrf.AuthQuery.NotInitPrin q
  · rw [pqxdhAuthShCrPrimImpl1Key_eq_of_ne q hq]
    exact pqxdhAuthShCrPrimImpl_inv S pk sk n q h hI
  · simp only [AuthPrf.AuthQuery.NotInitPrin, not_forall, not_not] at hq
    obtain ⟨u, rfl⟩ := hq
    rw [pqxdhAuthShCrPrimImpl1Key_initPrin]
    simp only [liftShCrBasePrim, StateT.run]
    exact HoldsOnLeaves.bind (pqxdhAuthSimImplPrim1Key_hol S n (.initPrin u) h.base hI.bnd)
      fun p hp => HoldsOnLeaves.pure ⟨hp, hI.tpk, hI.tsk⟩

theorem caseSumV_eval_congr_left {τ₁ τ₂ τ : Ty pqSig} {Γ : List (Ty pqSig)}
    (e : Expr pqxdhOps Γ (.sum τ₁ τ₂))
    (l₁ l₂ : Var (τ₁ :: Γ) τ₁ → Comp pqxdhOps pqPrimIface (τ₁ :: Γ) τ)
    (r : Var (τ₂ :: Γ) τ₂ → Comp pqxdhOps pqPrimIface (τ₂ :: Γ) τ) (env : Env Γ)
    (hne : ∀ a, e.eval env ≠ .inl a) :
    (caseSumV e l₁ r).eval env = (caseSumV e l₂ r).eval env := by
  simp only [caseSumV, Comp.eval_caseSumC_elim]
  cases h : e.eval env with
  | inl a => exact absurd h (hne a)
  | inr b => rfl

/-- The DSL post-pause handler `shcrPost1KeyC` evaluates to `pqxdhAuthShCrPrimImpl1Key true S`. -/
theorem shcrPost1KeyC_eval (S : Setup) (K n : Nat) {Γ₁ Γ₂ Δ : List (Ty pqSig)} [h₁ : Ext Γ₁ Δ]
    [h₂ : Ext Γ₂ Δ] (sV : Var Γ₁ shcrStTy) (qV : Var Γ₂ authQueryTy) (env : Env Δ)
    (q : AuthQuery S) (h : AuthShCrState S) (sIdx : Nat) (chosen : Bytes)
    (hs : env.get (h₁.wk sV) = shcrStToVal sIdx chosen h)
    (hq : env.get (h₂.wk qV) = authQueryToVal q)
    (hB : AuthBaseListsBounded n h.base) (hn : n + 1 ≤ K) :
    (shcrPost1KeyC S K sV qV).eval env =
      encSCS sIdx chosen <$> (pqxdhAuthShCrPrimImpl1Key true S q).run h := by
  by_cases hq' : AuthPrf.AuthQuery.NotInitPrin q
  · rw [pqxdhAuthShCrPrimImpl1Key_eq_of_ne q hq',
      ← shcrPostC_eval S K n sV qV env q h sIdx chosen hs hq hB hn,
      shcrPost1KeyC_eq_tail, shcrPostC_eq_tail]
    refine caseSumV_eval_congr_left _ _ _ _ env ?_
    intro a
    simp only [v, Expr.eval, hq, authQueryToVal]
    cases q <;> first
      | exact absurd rfl (hq' _)
      | (simp only [authQenc]; exact Sum.inr_ne_inl)
  · simp only [AuthPrf.AuthQuery.NotInitPrin, not_forall, not_not] at hq'
    obtain ⟨u, rfl⟩ := hq'
    have hK : AuthBaseListsBounded K h.base := hB.mono (by omega)
    unfold shcrPost1KeyC
    simp only [caseSumV, v, Comp.eval_caseSumC_elim, Expr.eval, hq, authQueryToVal]
    rw [pqxdhAuthShCrPrimImpl1Key_initPrin]
    exact onBase_eval S _ _ h sIdx chosen (by simpa using hs) _ _
      (initPrin1KeyB_eval S K _ h.base .vz _ u rfl (by simp) hK)

end SignalPqxdh.Security.ReductionDsl.AuthHs
