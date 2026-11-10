/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Computational.Proofs.SignalPqxdh.Security.ReductionDsl.KeyIndSigKem
public import Computational.Proofs.SignalPqxdh.Security.ReductionDsl.Potential

/-!
# Semantic Challenger-Query Bound for the Costed `KeyInd` Signature Reduction

Proves via a potential argument on the remaining signing budget that `sigKeyIndProg` makes at most
`2 * S.N_spk_tot` signing-oracle queries for any adversary.
-/

@[expose] public section

set_option autoImplicit false

open SignalPqxdh SignalPqxdh.Security
open _root_.ReductionDsl hiding B PTag U32 bundleOfV bundleT bundleV dhSecretsT drKeyOfV drKeyT drKeyV hdrOfV hdrT hdrV keyIndCodec keyIndQT keyIndQenc keyIndRT keyIndRdec keyIndRenc pqPrimIface pqSigAndDdhIface sampleIndex sidT sidV
open SignalPqxdh.LegacyCosted
open OracleSpec OracleComp

namespace SignalPqxdh.Security.ReductionDsl.KeyInd

attribute [local simp] Expr.eval Env.get

@[reducible] def isSigChalQ : (PrimBaseSpec + eufCmaSignOracle.spec).Domain → Prop :=
  fun q => q.isRight = true

instance : DecidablePred isSigChalQ :=
  fun q => inferInstanceAs (Decidable (q.isRight = true))

def wSigChal : pqxdhEufCmaIface.Tag → ℕ
  | .inl _ => 0
  | .inr _ => 1

@[simp] def wsZero : pqxdhEufCmaIface.smp.Samp → ℕ := fun _ => 0

theorem hwSigChal : ∀ g x, isSigChalQ (pqxdhEufCmaIface.enc g x) → 1 ≤ wSigChal g
  | .inl _, _, h => by cases h
  | .inr _, _, _ => le_rfl

theorem hUSigChal (n : ℕ) : (pqxdhEufCmaIface.fwdU n).IsQueryBoundP isSigChalQ 0 := by
  change IsQueryBoundP
    (liftM (OracleSpec.query (spec := PrimBaseSpec + eufCmaSignOracle.spec) (.inl (.inl n))))
    isSigChalQ 0
  rw [isQueryBoundP_query_iff]
  intro h; cases h

@[simp] theorem liftBase_queries_wSigChal {Γ : List PT} {τ : PT}
    (c : Comp pqxdhOps pqPrimIface Γ τ) :
    (liftBase (C := eufCmaSignOracle) c).queries wSigChal wsZero = 0 := by
  induction c <;> simp [liftBase, Comp.queries, wSigChal, wsZero, *]

theorem potC_sig_ret {Γ : List PT} {τ : PT} {Pot : τ.denote → ℕ}
    (e : Expr pqxdhOps Γ τ) (env : Env Γ) {n : ℕ} (h : Pot (e.eval env) ≤ n) :
    PotOK isSigChalQ Pot ((Comp.ret e : Comp pqxdhOps pqxdhEufCmaIface Γ τ).eval env) n :=
  potC_ret e env h

theorem potC_sig_ite {Γ : List PT} {τ : PT} {Pot : τ.denote → ℕ}
    (c : Expr pqxdhOps Γ .bool) (t e : Comp pqxdhOps pqxdhEufCmaIface Γ τ) (env : Env Γ) {n : ℕ}
    (ht : c.eval env = true → PotOK isSigChalQ Pot (t.eval env) n)
    (he : c.eval env = false → PotOK isSigChalQ Pot (e.eval env) n) :
    PotOK isSigChalQ Pot ((Comp.ite c t e).eval env) n :=
  potC_ite c t e env ht he

theorem potC_sig_caseOpt {Γ : List PT} {τ₁ τ : PT} {Pot : τ.denote → ℕ}
    (o : Expr pqxdhOps Γ (.opt τ₁)) (kn : Comp pqxdhOps pqxdhEufCmaIface Γ τ)
    (ks : Comp pqxdhOps pqxdhEufCmaIface (τ₁ :: Γ) τ) (env : Env Γ) {n : ℕ}
    (hn : o.eval env = none → PotOK isSigChalQ Pot (kn.eval env) n)
    (hs : ∀ a, o.eval env = some a → PotOK isSigChalQ Pot (ks.eval (.cons a env)) n) :
    PotOK isSigChalQ Pot ((Comp.caseOpt o kn ks).eval env) n := by
  simp only [Comp.eval]
  split
  · next h => exact hn h
  · next a h => exact hs a h

theorem potC_sig_caseSum {Γ : List PT} {τ₁ τ₂ τ : PT} {Pot : τ.denote → ℕ}
    (s : Expr pqxdhOps Γ (.sum τ₁ τ₂))
    (kl : Comp pqxdhOps pqxdhEufCmaIface (τ₁ :: Γ) τ) (kr : Comp pqxdhOps pqxdhEufCmaIface (τ₂ :: Γ) τ)
    (env : Env Γ) {n : ℕ}
    (hl : ∀ a, s.eval env = .inl a → PotOK isSigChalQ Pot (kl.eval (.cons a env)) n)
    (hr : ∀ b, s.eval env = .inr b → PotOK isSigChalQ Pot (kr.eval (.cons b env)) n) :
    PotOK isSigChalQ Pot ((Comp.caseSum s kl kr).eval env) n :=
  potC_caseSum s kl kr env hl hr

theorem potC_bind0 {Γ : List PT} {τ₁ τ₂ : PT} {Pot : τ₂.denote → ℕ}
    (m : Comp pqxdhOps pqxdhEufCmaIface Γ τ₁) (k : Comp pqxdhOps pqxdhEufCmaIface (τ₁ :: Γ) τ₂)
    (env : Env Γ) {n : ℕ}
    (hm : m.queries wSigChal wsZero = 0)
    (hk : ∀ x, PotOK isSigChalQ Pot (k.eval (.cons x env)) n) :
    PotOK isSigChalQ Pot ((Comp.bind m k).eval env) n :=
  potC_bind wSigChal wsZero hwSigChal hUSigChal m k env hk (by omega)

theorem potC_bind1 (m : ℕ+) {Γ : List PT} {τ₂ : PT} {Pot : τ₂.denote → ℕ}
    (arg : Expr pqxdhOps Γ (B m)) (k : Comp pqxdhOps pqxdhEufCmaIface (B 64 :: Γ) τ₂)
    (env : Env Γ) {r n : ℕ}
    (hk : ∀ x, PotOK isSigChalQ Pot (k.eval (.cons x env)) r) (hmn : 1 + r ≤ n) :
    PotOK isSigChalQ Pot ((Comp.bind (qChalSign m arg) k).eval env) n :=
  potC_bind wSigChal wsZero hwSigChal hUSigChal _ k env hk
    (by simpa [qChalSign, Comp.queries, wSigChal] using hmn)

/-- Potential of a signature-reduction state: twice its remaining signing budget. -/
def sigPot (st : sigStTy.denote) : ℕ := 2 * st.2.2.2.2

@[simp] theorem Ext.step_wk {Γ Δ : List PT} {σ τ : PT} [h : Ext Γ Δ] (x : Var Γ τ) :
    (Ext.step (σ := σ)).wk x = .succ (h.wk x) := rfl

@[simp] theorem Ext.refl_wk {Γ : List PT} {τ : PT} (x : Var Γ τ) :
    (Ext.refl).wk x = x := rfl

theorem onGame_potOK {Γ₁ Δ : List PT} [Ext Γ₁ Δ] (s : Var Γ₁ sigStTy)
    (br : (g : Var (keyIndStateTy :: Δ) keyIndStateTy) →
      Comp pqxdhOps pqPrimIface (keyIndStateTy :: Δ) RS)
    (env : Env Δ) {n : ℕ} (hn : sigPot ((v s : Expr pqxdhOps Δ sigStTy).eval env) ≤ n) :
    PotOK isSigChalQ (fun r : SRS.denote => sigPot r.2) ((onGame s br).eval env) n := by
  unfold onGame bindV
  refine @potC_bind0 _ _ _ _ _ _ _ _ (by simp) (fun x => ?_)
  refine @potC_sig_ret _ _ _ _ _ _ ?_
  simpa [sigPot, v] using hn

macro "pot_step" hn:ident : tactic => `(tactic| first
  | (with_reducible refine @potC_sig_ret _ _ _ _ _ _ ?_); simpa [sigPot, v] using $hn
  | (with_reducible refine @onGame_potOK _ _ _ _ _ _ _ ?_); simpa [sigPot, v] using $hn
  | with_reducible refine @potC_sig_ite _ _ _ _ _ _ _ _ (fun h => ?_) (fun h => ?_)
  | with_reducible refine @potC_sig_caseOpt _ _ _ _ _ _ _ _ _ (fun h => ?_) (fun _ h => ?_)
  | with_reducible refine @potC_sig_caseSum _ _ _ _ _ _ _ _ _ _ (fun _ h => ?_) (fun _ h => ?_)
  | (with_reducible refine @potC_bind0 _ _ _ _ _ _ _ _ ?_ (fun _ => ?_));
      (focus (simp [extractC, bindV, letV, Comp.queries]; done)))

theorem potAux_two (b n : ℕ) (hb : b ≠ 0) (hn : 2 * b ≤ n) : 2 ≤ n := by omega
theorem potAux_one (n : ℕ) (h : 2 ≤ n) : 1 + (n - 1) ≤ n := by omega
theorem potAux_one' (n : ℕ) (h : 2 ≤ n) : 1 + (n - 2) ≤ n - 1 := by omega
theorem potAux_sub (b n : ℕ) (hn : 2 * b ≤ n) : 2 * (b - 1) ≤ n - 2 := by omega

section SigPot

variable (useRo : Bool) (S : Setup) (K : ℕ) {Γ₁ Γ₂ Δ : List PT} [Ext Γ₁ Δ] [Ext Γ₂ Δ]

theorem sigInitPrinB_potOK (s : Var Γ₁ sigStTy) (u : Var Γ₂ .nat) (env : Env Δ) {n : ℕ}
    (hn : sigPot ((v s : Expr pqxdhOps Δ sigStTy).eval env) ≤ n) :
    PotOK isSigChalQ (fun r : SRS.denote => sigPot r.2) ((sigInitPrinB K s u).eval env) n := by
  unfold sigInitPrinB
  (try unfold bindV); (try beta_reduce)
  repeat' pot_step hn

theorem sigCorruptB_potOK (s : Var Γ₁ sigStTy) (u : Var Γ₂ .nat) (env : Env Δ) {n : ℕ}
    (hn : sigPot ((v s : Expr pqxdhOps Δ sigStTy).eval env) ≤ n) :
    PotOK isSigChalQ (fun r : SRS.denote => sigPot r.2) ((sigCorruptB K s u).eval env) n := by
  unfold sigCorruptB
  (try unfold caseOptV); (try beta_reduce)
  repeat' pot_step hn

theorem sigInitiateB_potOK (opk : Bool) (s : Var Γ₁ sigStTy) (x : Var Γ₂ initQTy) (env : Env Δ)
    {n : ℕ} (hn : sigPot ((v s : Expr pqxdhOps Δ sigStTy).eval env) ≤ n) :
    PotOK isSigChalQ (fun r : SRS.denote => sigPot r.2)
      ((sigInitiateB useRo S K opk s x).eval env) n := by
  unfold sigInitiateB letV bindV
  refine @potC_bind0 _ _ _ _ _ _ _ _ (by simp [Comp.queries]) (fun _ => ?_)
  refine @potC_bind0 _ _ _ _ _ _ _ _ (by simp [extractC, bindV, Comp.queries]) (fun _ => ?_)
  refine @potC_bind0 _ _ _ _ _ _ _ _ (by simp) (fun _ => ?_)
  refine @potC_sig_ret _ _ _ _ _ _ ?_
  simpa [sigPot, v] using hn

theorem sigGenSpkB_potOK (s : Var Γ₁ sigStTy) (x : Var Γ₂ (.prod .nat .nat)) (env : Env Δ)
    {n : ℕ} (hn : sigPot ((v s : Expr pqxdhOps Δ sigStTy).eval env) ≤ n) :
    PotOK isSigChalQ (fun r : SRS.denote => sigPot r.2) ((sigGenSpkB K s x).eval env) n := by
  unfold sigGenSpkB
  (try unfold bindV); (try unfold caseOptV); (try beta_reduce)
  repeat' pot_step hn
  rename_i hb
  have hb' : (env.get (Ext.wk s)).2.2.2.2 ≠ 0 := by simpa [natEq, v, sgBudget] using hb
  have hsp : sigPot ((v s : Expr pqxdhOps Δ sigStTy).eval env) = 2 * (env.get (Ext.wk s)).2.2.2.2 := by
    simp [sigPot, v]
  rw [hsp] at hn
  have h2 : 2 ≤ n := potAux_two _ _ hb' hn
  refine @potC_bind1 33 _ _ _ _ _ _ (n - 1) _ (fun _ => ?_) (potAux_one n h2)
  refine @potC_bind0 _ _ _ _ _ _ _ _ (by simp) (fun _ => ?_)
  refine @potC_bind0 _ _ _ _ _ _ _ _ (by simp) (fun _ => ?_)
  refine @potC_bind1 1569 _ _ _ _ _ _ (n - 2) _ (fun _ => ?_) (potAux_one' n h2)
  refine @potC_sig_ret _ _ _ _ _ _ ?_
  simp only [sigPot, v, Expr.eval, Env.get, Ext.step_wk]
  exact potAux_sub _ _ hn

set_option maxHeartbeats 4000000 in
theorem sigHandleC_potOK (s : Var Γ₁ sigStTy) (q : Var Γ₂ keyIndQueryTy) (env : Env Δ)
    {n : ℕ} (hn : sigPot ((v s : Expr pqxdhOps Δ sigStTy).eval env) ≤ n) :
    PotOK isSigChalQ (fun r : SRS.denote => sigPot r.2)
      ((sigHandleC useRo S K s q).eval env) n := by
  unfold sigHandleC
  (try unfold caseSumV); (try beta_reduce)
  repeat' first
    | (with_reducible refine @sigInitPrinB_potOK K _ _ _ _ _ s _ _ _ ?_); simpa [sigPot, v] using hn
    | (with_reducible refine @sigCorruptB_potOK K _ _ _ _ _ s _ _ _ ?_); simpa [sigPot, v] using hn
    | (with_reducible refine @sigGenSpkB_potOK K _ _ _ _ _ s _ _ _ ?_); simpa [sigPot, v] using hn
    | (with_reducible refine @sigInitiateB_potOK useRo S K _ _ _ _ _ _ s _ _ _ ?_);
        simpa [sigPot, v] using hn
    | pot_step hn

end SigPot

theorem sigInitC_potOK (S : Setup) (pk : Bytes) :
    PotOK isSigChalQ (fun p : Unit × sigStTy.denote => sigPot p.2)
      ((bindV (liftBase (sIndex S.N_id)) fun k =>
        bindV (liftBase sBool) fun secb =>
        Comp.ret (.pair .unit (.pair (emptyStE (v secb)) (.pair (v k)
          (.pair (.var (.succ (.succ .zero))) (.pair .none (.nat S.N_spk_tot)))))) :
        Comp pqxdhOps pqxdhEufCmaIface [B 32] (.prod .unit sigStTy)).eval (.cons pk .nil))
      (2 * S.N_spk_tot) := by
  unfold bindV
  refine potC_bind0 (τ₂ := .prod .unit sigStTy) _ _ _ rfl (fun _ => ?_)
  refine potC_bind0 (τ₂ := .prod .unit sigStTy) _ _ _ rfl (fun _ => ?_)
  exact potC_sig_ret (τ := .prod .unit sigStTy) _ _ (by simp [sigPot])

theorem sigKeyIndProg_init_potOK_min (useRo : Bool) (S : Setup) (K : ℕ) (pk : Bytes) :
    PotOK isSigChalQ (fun p : Unit × sigStTy.denote => sigPot p.2)
      ((sigKeyIndProg useRo S K).init.eval (.cons pk .nil)) (2 * min K S.N_spk_tot) := by
  dsimp only [sigKeyIndProg]
  unfold bindV
  refine potC_bind0 (τ₂ := .prod .unit sigStTy) _ _ _ rfl (fun _ => ?_)
  refine potC_bind0 (τ₂ := .prod .unit sigStTy) _ _ _ rfl (fun _ => ?_)
  exact potC_sig_ret (τ := .prod .unit sigStTy) _ _ (by simp [sigPot])

theorem sigKeyIndProg_init_potOK (useRo : Bool) (S : Setup) (K : ℕ) (pk : Bytes) :
    PotOK isSigChalQ (fun p : Unit × sigStTy.denote => sigPot p.2)
      ((sigKeyIndProg useRo S K).init.eval (.cons pk .nil)) (2 * S.N_spk_tot) := by
  dsimp only [sigKeyIndProg]
  unfold bindV
  refine potC_bind0 (τ₂ := .prod .unit sigStTy) _ _ _ rfl (fun _ => ?_)
  refine potC_bind0 (τ₂ := .prod .unit sigStTy) _ _ _ rfl (fun _ => ?_)
  exact potC_sig_ret (τ := .prod .unit sigStTy) _ _ (by simp [sigPot])

theorem sigKeyIndProg_chalBounded_min (useRo : Bool) (S : Setup) (K : ℕ)
    (A : Unit → OracleComp (unifSpec + keyIndSpec S) Bool) (pk : Bytes) :
    ((sigKeyIndProg useRo S K).eval A pk).IsQueryBoundP isSigChalQ (2 * min K S.N_spk_tot) := by
  unfold CostedReduction.eval CostedReduction.impl
  refine PotOK.toQueryBound (B := fun _ => 0) ?_ (fun _ => rfl)
  refine PotOK.bindPot (sigKeyIndProg_init_potOK_min useRo S K pk) (fun as => ?_)
  refine PotOK.bindPot (B₁ := fun x : Bool × sigStTy.denote => sigPot x.2)
    (potOK_simulateQ_handlerImpl sigPot hUSigChal (sigKeyIndProg useRo S K).handle ?_ (A as.1) as.2)
    (fun bs => ?_)
  · intro q s
    exact sigHandleC_potOK useRo S K
      (Γ₁ := [sigStTy, keyIndQueryTy]) (Γ₂ := [keyIndQueryTy]) (Δ := [sigStTy, keyIndQueryTy])
      .zero .zero (.cons s (.cons q .nil)) (by simp [sigPot, v])
  · exact @potC_sig_ret _ _ _ _ _ _ (Nat.zero_le _)

/-- `sigKeyIndProg` makes at most `2 * S.N_spk_tot` challenger signing queries for any adversary. -/
theorem sigKeyIndProg_chalBounded (useRo : Bool) (S : Setup) (K : ℕ)
    (A : Unit → OracleComp (unifSpec + keyIndSpec S) Bool) (pk : Bytes) :
    ((sigKeyIndProg useRo S K).eval A pk).IsQueryBoundP isSigChalQ (2 * S.N_spk_tot) :=
  (sigKeyIndProg_chalBounded_min useRo S K A pk).mono
    (Nat.mul_le_mul_left 2 (Nat.min_le_right K S.N_spk_tot))

end SignalPqxdh.Security.ReductionDsl.KeyInd
