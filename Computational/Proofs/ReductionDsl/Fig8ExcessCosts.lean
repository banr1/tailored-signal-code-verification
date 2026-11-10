/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Computational.Proofs.ReductionDsl.Fig8SourceCosts
import Computational.Proofs.GameHop.ReductionDsl.CostUB

/-!
# Excess cost bounds and atomic step budget for Figure 8 reductions

Bounds `compExcessOf` via branch-free `compExcessUB` under the concrete macro weight schedules
`smOpC` and `ckaOpC`, and fits `fig8AtomicStepBound` inside `ratchetCostBudget q qep`.
-/

@[expose] public section

set_option autoImplicit false

open OracleComp OracleSpec CryptoGames CryptoGames.LibsignalSM Ratchet LibsignalInst
  LibsignalSession HMAC HKDF CBC LibsignalAead SM SM.Construction SM.Engine
  CKA AEADScheme MACScheme WireAEAD FSAEAD ReductionDsl
open CryptoVerification.LibsignalSession (ratchetCostBudget)
open Computational.Proofs.GameHop.ReductionDsl.CostUB
open Computational.Proofs.ReductionDsl.PureAuxMacroLift
open Computational.Proofs.ReductionDsl.Fig8SourceCosts

namespace Computational.Proofs.ReductionDsl.Fig8ExcessCosts

/-! ## Sum-replaced excess combinators -/

section ExcessUB

def exprExcessUB {S : Sig} {O : Ops S} (opEx : O.Op → ℕ) :
    {Γ : List (Ty S)} → {t : Ty S} → Expr O Γ t → ℕ
  | _, _, .var _ | _, _, .unit | _, _, .bool _ | _, _, .nat _ | _, _, .none | _, _, .nil => 0
  | _, _, .add a b | _, _, .sub a b | _, _, .lt a b | _, _, .eqN a b | _, _, .and a b
  | _, _, .pair a b | _, _, .cons a b | _, _, .take a b | _, _, .appendL _ a b
  | _, _, .letE a b | _, _, .tget a b => exprExcessUB opEx a + exprExcessUB opEx b
  | _, _, .mulK _ a | _, _, .divK _ a | _, _, .modK _ a | _, _, .not a | _, _, .fst a
  | _, _, .snd a | _, _, .inl a | _, _, .inr a | _, _, .some a | _, _, .len a
  | _, _, .tconst a => exprExcessUB opEx a
  | _, _, .ite c a b | _, _, .caseOpt c a b | _, _, .caseSum c a b =>
    exprExcessUB opEx c + exprExcessUB opEx a + exprExcessUB opEx b
  | _, _, .op o a => exprExcessUB opEx a + opEx o
  | _, _, .findB K l p | _, _, .anyB K l p | _, _, .mapB K l p =>
    exprExcessUB opEx l + K * exprExcessUB opEx p
  | _, _, .foldrB K l z f =>
    exprExcessUB opEx l + exprExcessUB opEx z + K * exprExcessUB opEx f
  | _, _, .tset m i a => exprExcessUB opEx m + exprExcessUB opEx i + exprExcessUB opEx a

def compExcessUB {S : Sig} {O : Ops S} {ι : Type} {T : OracleSpec ι} {I : Iface S T}
    (opEx : O.Op → ℕ) (sEx : I.smp.Samp → ℕ) (qEx : I.Tag → ℕ) :
    {Γ : List (Ty S)} → {t : Ty S} → Comp O I Γ t → ℕ
  | _, _, .ret e => exprExcessUB opEx e
  | _, _, .bind c k => compExcessUB opEx sEx qEx c + compExcessUB opEx sEx qEx k
  | _, _, .ite b c d | _, _, .caseOpt b c d | _, _, .caseSum b c d =>
    exprExcessUB opEx b + compExcessUB opEx sEx qEx c + compExcessUB opEx sEx qEx d
  | _, _, .sample s e => exprExcessUB opEx e + sEx s
  | _, _, .query g e => exprExcessUB opEx e + qEx g
  | _, _, .iter n e body => exprExcessUB opEx e + n * compExcessUB opEx sEx qEx body
  | _, _, .findM K l p | _, _, .anyM K l p | _, _, .mapM K l p =>
    exprExcessUB opEx l + K * compExcessUB opEx sEx qEx p
  | _, _, .consumeFirstM K l p fmk =>
    exprExcessUB opEx l + K * (compExcessUB opEx sEx qEx p + exprExcessUB opEx fmk)
  | _, _, .foldM K l z f =>
    exprExcessUB opEx l + exprExcessUB opEx z + K * compExcessUB opEx sEx qEx f

theorem exprExcessOf_le_UB {S : Sig} {O : Ops S} (opEx : O.Op → ℕ)
    {Γ : List (Ty S)} {t : Ty S} (e : Expr O Γ t) :
    exprExcessOf opEx e ≤ exprExcessUB opEx e := by
  induction e with
  | var _ | unit | bool _ | nat _ | none | nil => rfl
  | add _ _ ih1 ih2 | sub _ _ ih1 ih2 | lt _ _ ih1 ih2 | eqN _ _ ih1 ih2 | and _ _ ih1 ih2
  | pair _ _ ih1 ih2 | cons _ _ ih1 ih2 | take _ _ ih1 ih2 | appendL _ _ _ ih1 ih2
  | letE _ _ ih1 ih2 | tget _ _ ih1 ih2 =>
    simp only [exprExcessOf, exprExcessUB]; omega
  | mulK _ _ ih | divK _ _ ih | modK _ _ ih | not _ ih | fst _ ih | snd _ ih
  | inl _ ih | inr _ ih | some _ ih | len _ ih | tconst _ ih | op _ _ ih =>
    simp only [exprExcessOf, exprExcessUB]; omega
  | ite _ _ _ ihc iha ihb | caseOpt _ _ _ ihc iha ihb | caseSum _ _ _ ihc iha ihb =>
    simp only [exprExcessOf, exprExcessUB]; omega
  | findB K _ _ ihl ihp | anyB K _ _ ihl ihp | mapB K _ _ ihl ihp =>
    have hm := Nat.mul_le_mul_left K ihp
    simp only [exprExcessOf, exprExcessUB]; omega
  | foldrB K _ _ _ ihl ihz ihf =>
    have hm := Nat.mul_le_mul_left K ihf
    simp only [exprExcessOf, exprExcessUB]; omega
  | tset _ _ _ ih1 ih2 ih3 =>
    simp only [exprExcessOf, exprExcessUB]; omega

theorem compExcessOf_le_UB {S : Sig} {O : Ops S} {ι : Type} {T : OracleSpec ι} {I : Iface S T}
    (opEx : O.Op → ℕ) (sEx : I.smp.Samp → ℕ) (qEx : I.Tag → ℕ)
    {Γ : List (Ty S)} {t : Ty S} (c : Comp O I Γ t) :
    compExcessOf opEx sEx qEx c ≤ compExcessUB opEx sEx qEx c := by
  induction c with
  | ret e => exact exprExcessOf_le_UB opEx e
  | bind _ _ ihc ihk => simp only [compExcessOf, compExcessUB]; omega
  | ite b _ _ ihc ihd | caseOpt b _ _ ihc ihd | caseSum b _ _ ihc ihd =>
    have hb := exprExcessOf_le_UB opEx b
    simp only [compExcessOf, compExcessUB]; omega
  | sample s e =>
    have he := exprExcessOf_le_UB opEx e
    simp only [compExcessOf, compExcessUB]; omega
  | query g e =>
    have he := exprExcessOf_le_UB opEx e
    simp only [compExcessOf, compExcessUB]; omega
  | iter n e _ ihb =>
    have he := exprExcessOf_le_UB opEx e
    have hm := Nat.mul_le_mul_left n ihb
    simp only [compExcessOf, compExcessUB]; omega
  | findM K l _ ihp | anyM K l _ ihp | mapM K l _ ihp =>
    have hl := exprExcessOf_le_UB opEx l
    have hm := Nat.mul_le_mul_left K ihp
    simp only [compExcessOf, compExcessUB]; omega
  | consumeFirstM K l _ fmk ihp =>
    have hl := exprExcessOf_le_UB opEx l
    have hmk := exprExcessOf_le_UB opEx fmk
    have hm := Nat.mul_le_mul_left K (Nat.add_le_add ihp hmk)
    simp only [compExcessOf, compExcessUB]; omega
  | foldM K l z _ ihf =>
    have hl := exprExcessOf_le_UB opEx l
    have hz := exprExcessOf_le_UB opEx z
    have hm := Nat.mul_le_mul_left K ihf
    simp only [compExcessOf, compExcessUB]; omega

theorem compCostW_le_cost_add_excessUB {S : Sig} {O : Ops S}
    {ι : Type} {T : OracleSpec ι} {I : Iface S T}
    (opC : O.Op → ℕ) (sC : I.smp.Samp → ℕ) (qC : I.Tag → ℕ)
    {Γ : List (Ty S)} {t : Ty S} (c : Comp O I Γ t) :
    compCostW opC sC qC c ≤ c.cost + compExcessUB opC sC qC c :=
  (compCostW_le_cost_add_excess opC opC sC sC qC qC
    (fun _ => Nat.le_add_left _ _)
    (fun _ => Nat.le_add_left _ _)
    (fun _ => Nat.le_add_left _ _) c).trans
    (Nat.add_le_add_left (compExcessOf_le_UB opC sC qC c) c.cost)

end ExcessUB

section ExcessSimps

variable {S : Sig} {O : Ops S} {ι : Type} {T : OracleSpec ι} {I : Iface S T}
  (opEx : O.Op → ℕ) (sEx : I.smp.Samp → ℕ) (qEx : I.Tag → ℕ)

@[simp] theorem exprExcessUB_var {Γ t} (v : Var Γ t) : exprExcessUB opEx (Expr.var (O := O) v) = 0 := rfl
@[simp] theorem exprExcessUB_v0 {Γ t} : exprExcessUB opEx (Expr.v0 (O := O) (Γ := Γ) (t := t)) = 0 := rfl
@[simp] theorem exprExcessUB_v1 {Γ t a} : exprExcessUB opEx (Expr.v1 (O := O) (Γ := Γ) (t := t) (a := a)) = 0 := rfl
@[simp] theorem exprExcessUB_v2 {Γ t a b} : exprExcessUB opEx (Expr.v2 (O := O) (Γ := Γ) (t := t) (a := a) (b := b)) = 0 := rfl
@[simp] theorem exprExcessUB_v3 {Γ t a b c} : exprExcessUB opEx (Expr.v3 (O := O) (Γ := Γ) (t := t) (a := a) (b := b) (c := c)) = 0 := rfl
@[simp] theorem exprExcessUB_v4 {Γ t a b c d} : exprExcessUB opEx (Expr.v4 (O := O) (Γ := Γ) (t := t) (a := a) (b := b) (c := c) (d := d)) = 0 := rfl
@[simp] theorem exprExcessUB_v5 {Γ t a b c d e} : exprExcessUB opEx (Expr.v5 (O := O) (Γ := Γ) (t := t) (a := a) (b := b) (c := c) (d := d) (e := e)) = 0 := rfl
@[simp] theorem exprExcessUB_v6 {Γ t a b c d e f} : exprExcessUB opEx (Expr.v6 (O := O) (Γ := Γ) (t := t) (a := a) (b := b) (c := c) (d := d) (e := e) (f := f)) = 0 := rfl
@[simp] theorem exprExcessUB_v7 {Γ t a b c d e f g} : exprExcessUB opEx (Expr.v7 (O := O) (Γ := Γ) (t := t) (a := a) (b := b) (c := c) (d := d) (e := e) (f := f) (g := g)) = 0 := rfl
@[simp] theorem exprExcessUB_unit {Γ} : exprExcessUB opEx (Expr.unit (O := O) (Γ := Γ)) = 0 := rfl
@[simp] theorem exprExcessUB_bool {Γ} (b : Bool) : exprExcessUB opEx (Expr.bool (O := O) (Γ := Γ) b) = 0 := rfl
@[simp] theorem exprExcessUB_nat {Γ} (n : ℕ) : exprExcessUB opEx (Expr.nat (O := O) (Γ := Γ) n) = 0 := rfl
@[simp] theorem exprExcessUB_none {Γ t} : exprExcessUB opEx (Expr.none (O := O) (Γ := Γ) (t := t)) = 0 := rfl
@[simp] theorem exprExcessUB_nil {Γ t} : exprExcessUB opEx (Expr.nil (O := O) (Γ := Γ) (t := t)) = 0 := rfl
@[simp] theorem exprExcessUB_add {Γ} (a b : Expr O Γ .nat) : exprExcessUB opEx (.add a b) = exprExcessUB opEx a + exprExcessUB opEx b := rfl
@[simp] theorem exprExcessUB_sub {Γ} (a b : Expr O Γ .nat) : exprExcessUB opEx (.sub a b) = exprExcessUB opEx a + exprExcessUB opEx b := rfl
@[simp] theorem exprExcessUB_mulK {Γ} (k : ℕ) (a : Expr O Γ .nat) : exprExcessUB opEx (.mulK k a) = exprExcessUB opEx a := rfl
@[simp] theorem exprExcessUB_divK {Γ} (k : ℕ) (a : Expr O Γ .nat) : exprExcessUB opEx (.divK k a) = exprExcessUB opEx a := rfl
@[simp] theorem exprExcessUB_modK {Γ} (k : ℕ) (a : Expr O Γ .nat) : exprExcessUB opEx (.modK k a) = exprExcessUB opEx a := rfl
@[simp] theorem exprExcessUB_lt {Γ} (a b : Expr O Γ .nat) : exprExcessUB opEx (.lt a b) = exprExcessUB opEx a + exprExcessUB opEx b := rfl
@[simp] theorem exprExcessUB_eqN {Γ} (a b : Expr O Γ .nat) : exprExcessUB opEx (.eqN a b) = exprExcessUB opEx a + exprExcessUB opEx b := rfl
@[simp] theorem exprExcessUB_not {Γ} (a : Expr O Γ .bool) : exprExcessUB opEx (.not a) = exprExcessUB opEx a := rfl
@[simp] theorem exprExcessUB_and {Γ} (a b : Expr O Γ .bool) : exprExcessUB opEx (.and a b) = exprExcessUB opEx a + exprExcessUB opEx b := rfl
@[simp] theorem exprExcessUB_ite {Γ t} (c : Expr O Γ .bool) (a b : Expr O Γ t) :
    exprExcessUB opEx (.ite c a b) = exprExcessUB opEx c + exprExcessUB opEx a + exprExcessUB opEx b := rfl
@[simp] theorem exprExcessUB_pair {Γ t u} (a : Expr O Γ t) (b : Expr O Γ u) :
    exprExcessUB opEx (.pair a b) = exprExcessUB opEx a + exprExcessUB opEx b := rfl
@[simp] theorem exprExcessUB_fst {Γ t u} (a : Expr O Γ (.prod t u)) : exprExcessUB opEx (.fst a) = exprExcessUB opEx a := rfl
@[simp] theorem exprExcessUB_snd {Γ t u} (a : Expr O Γ (.prod t u)) : exprExcessUB opEx (.snd a) = exprExcessUB opEx a := rfl
@[simp] theorem exprExcessUB_inl {Γ t u} (a : Expr O Γ t) : exprExcessUB opEx (Expr.inl (u := u) a) = exprExcessUB opEx a := rfl
@[simp] theorem exprExcessUB_inr {Γ t u} (a : Expr O Γ u) : exprExcessUB opEx (Expr.inr (t := t) a) = exprExcessUB opEx a := rfl
@[simp] theorem exprExcessUB_some {Γ t} (a : Expr O Γ t) : exprExcessUB opEx (.some a) = exprExcessUB opEx a := rfl
@[simp] theorem exprExcessUB_caseOpt {Γ t u} (e : Expr O Γ (.opt t)) (n : Expr O Γ u) (s : Expr O (t :: Γ) u) :
    exprExcessUB opEx (.caseOpt e n s) = exprExcessUB opEx e + exprExcessUB opEx n + exprExcessUB opEx s := rfl
@[simp] theorem exprExcessUB_caseSum {Γ t u v} (e : Expr O Γ (.sum t u)) (l : Expr O (t :: Γ) v) (r : Expr O (u :: Γ) v) :
    exprExcessUB opEx (.caseSum e l r) = exprExcessUB opEx e + exprExcessUB opEx l + exprExcessUB opEx r := rfl
@[simp] theorem exprExcessUB_letE {Γ t u} (e : Expr O Γ t) (b : Expr O (t :: Γ) u) :
    exprExcessUB opEx (.letE e b) = exprExcessUB opEx e + exprExcessUB opEx b := rfl
@[simp] theorem exprExcessUB_op {Γ} (o : O.Op) (a : Expr O Γ (O.dom o)) :
    exprExcessUB opEx (.op o a) = exprExcessUB opEx a + opEx o := rfl
@[simp] theorem exprExcessUB_cons {Γ t} (x : Expr O Γ t) (l : Expr O Γ (.list t)) :
    exprExcessUB opEx (.cons x l) = exprExcessUB opEx x + exprExcessUB opEx l := rfl
@[simp] theorem exprExcessUB_len {Γ t} (l : Expr O Γ (.list t)) : exprExcessUB opEx (.len l) = exprExcessUB opEx l := rfl
@[simp] theorem exprExcessUB_take {Γ t} (n : Expr O Γ .nat) (l : Expr O Γ (.list t)) :
    exprExcessUB opEx (.take n l) = exprExcessUB opEx n + exprExcessUB opEx l := rfl
@[simp] theorem exprExcessUB_appendL {Γ t} (K : ℕ) (a b : Expr O Γ (.list t)) :
    exprExcessUB opEx (.appendL K a b) = exprExcessUB opEx a + exprExcessUB opEx b := rfl
@[simp] theorem exprExcessUB_findB {Γ t} (K : ℕ) (l : Expr O Γ (.list t)) (p : Expr O (t :: Γ) .bool) :
    exprExcessUB opEx (.findB K l p) = exprExcessUB opEx l + K * exprExcessUB opEx p := rfl
@[simp] theorem exprExcessUB_anyB {Γ t} (K : ℕ) (l : Expr O Γ (.list t)) (p : Expr O (t :: Γ) .bool) :
    exprExcessUB opEx (.anyB K l p) = exprExcessUB opEx l + K * exprExcessUB opEx p := rfl
@[simp] theorem exprExcessUB_mapB {Γ t u} (K : ℕ) (l : Expr O Γ (.list t)) (f : Expr O (t :: Γ) u) :
    exprExcessUB opEx (.mapB K l f) = exprExcessUB opEx l + K * exprExcessUB opEx f := rfl
@[simp] theorem exprExcessUB_foldrB {Γ t u} (K : ℕ) (l : Expr O Γ (.list t)) (z : Expr O Γ u) (f : Expr O (t :: u :: Γ) u) :
    exprExcessUB opEx (.foldrB K l z f) = exprExcessUB opEx l + exprExcessUB opEx z + K * exprExcessUB opEx f := rfl
@[simp] theorem exprExcessUB_tconst {Γ t} (a : Expr O Γ t) : exprExcessUB opEx (.tconst a) = exprExcessUB opEx a := rfl
@[simp] theorem exprExcessUB_tget {Γ t} (m : Expr O Γ (.tbl t)) (i : Expr O Γ .nat) :
    exprExcessUB opEx (.tget m i) = exprExcessUB opEx m + exprExcessUB opEx i := rfl
@[simp] theorem exprExcessUB_tset {Γ t} (m : Expr O Γ (.tbl t)) (i : Expr O Γ .nat) (a : Expr O Γ t) :
    exprExcessUB opEx (.tset m i a) = exprExcessUB opEx m + exprExcessUB opEx i + exprExcessUB opEx a := rfl

@[simp] theorem compExcessUB_ret {Γ t} (e : Expr O Γ t) :
    compExcessUB opEx sEx qEx (Comp.ret (I := I) e) = exprExcessUB opEx e := rfl
@[simp] theorem compExcessUB_bind {Γ t u} (c : Comp O I Γ t) (k : Comp O I (t :: Γ) u) :
    compExcessUB opEx sEx qEx (.bind c k) = compExcessUB opEx sEx qEx c + compExcessUB opEx sEx qEx k := rfl
@[simp] theorem compExcessUB_ite {Γ t} (b : Expr O Γ .bool) (c d : Comp O I Γ t) :
    compExcessUB opEx sEx qEx (.ite b c d) =
      exprExcessUB opEx b + compExcessUB opEx sEx qEx c + compExcessUB opEx sEx qEx d := rfl
@[simp] theorem compExcessUB_caseOpt {Γ t u} (b : Expr O Γ (.opt t)) (c : Comp O I Γ u) (d : Comp O I (t :: Γ) u) :
    compExcessUB opEx sEx qEx (.caseOpt b c d) =
      exprExcessUB opEx b + compExcessUB opEx sEx qEx c + compExcessUB opEx sEx qEx d := rfl
@[simp] theorem compExcessUB_caseSum {Γ t u v} (b : Expr O Γ (.sum t u)) (c : Comp O I (t :: Γ) v) (d : Comp O I (u :: Γ) v) :
    compExcessUB opEx sEx qEx (.caseSum b c d) =
      exprExcessUB opEx b + compExcessUB opEx sEx qEx c + compExcessUB opEx sEx qEx d := rfl
@[simp] theorem compExcessUB_sample {Γ} (s : I.smp.Samp) (e : Expr O Γ (I.smp.sDom s)) :
    compExcessUB opEx sEx qEx (.sample s e) = exprExcessUB opEx e + sEx s := rfl
@[simp] theorem compExcessUB_query {Γ} (g : I.Tag) (e : Expr O Γ (I.dom g)) :
    compExcessUB opEx sEx qEx (.query g e) = exprExcessUB opEx e + qEx g := rfl

end ExcessSimps

/-! ## Macro weight schedules and excess bounds -/

set_option linter.unusedSimpArgs false
set_option maxRecDepth 200000

def smOpC : SM.SMOp → ℕ
  | .eqMsg => 32000
  | .eqCt => 200
  | .blank => 32000
  | _ => 10

def smSampC {α : Type} : α → ℕ := fun _ => 200
def smQueryC {α : Type} : α → ℕ := fun _ => 100000

section Thm1ExcessHelpers

variable {Key St St₂ Msg Coins RCoins C : Type}
  {init : Party → Key → Option St}
  {send : St → Msg → Coins → Option (St × C)}
  {receive : St → C → RCoins → Option (St × ℕ × ℕ × Msg)}
  {eqMsg : Msg → Msg → Bool}
  {eqCt : C → C → Bool}
  {blank : Msg → Msg}
  {injOK : C → Bool}
  {stOK : Party → St → Bool}
  {φ : St → Option St₂}
  {stSort : SM.SMSort}
  {sampKey : ProbComp (Option Key)}
  {sampCoins : ProbComp (Option Coins)}
  {sampRCoins : ProbComp (Option RCoins)}

lemma thm1_simInitC_excessUB_le :
    compExcessUB smOpC smSampC smQueryC
      (SM.simInitC (init := init) (send := send) (receive := receive)
        (eqMsg := eqMsg) (eqCt := eqCt) (blank := blank) (injOK := injOK) (stOK := stOK) (φ := φ)
        (stSort := stSort) (sampKey := sampKey) (sampCoins := sampCoins)
        (sampRCoins := sampRCoins)) ≤ 500 := by
  simp [SM.simInitC, SM.mMk, smSampC]

lemma thm1_simInitC_cost_le :
    (SM.simInitC (init := init) (send := send) (receive := receive)
      (eqMsg := eqMsg) (eqCt := eqCt) (blank := blank) (injOK := injOK) (stOK := stOK) (φ := φ)
      (stSort := stSort) (sampKey := sampKey) (sampCoins := sampCoins)
      (sampRCoins := sampRCoins)).cost ≤ 200 := by
  have hb0 : ReductionDsl.bits 0 = 1 := rfl
  refine (compCost_le_costUB _).trans ?_
  simp only [SM.simInitC, SM.mMk, SM.smIface, SM.smSamplers,
    ReductionDsl.Expr.v0, hb0, dsl_cost, compCostUB, exprCostUB, Nat.reduceAdd]
  omega

lemma thm1_simHandleC_excessUB_le (K qep : ℕ) (realEpoch : Option ℕ) :
    compExcessUB smOpC smSampC smQueryC
      (SM.simHandleC (init := init) (send := send) (receive := receive)
        (eqMsg := eqMsg) (eqCt := eqCt) (blank := blank) (injOK := injOK) (stOK := stOK) (φ := φ)
        (stSort := stSort) (sampKey := sampKey) (sampCoins := sampCoins) (sampRCoins := sampRCoins)
        K 3 qep realEpoch) ≤ 200 * K + 800000 := by
  cases realEpoch <;>
  · simp only [SM.simHandleC, SM.simTransmitC, SM.simChallC, SM.simSendC,
      SM.simDeliverC, SM.simInjectC, SM.simCorrC,
      SM.mEpMgmtE, SM.mSafeChE, SM.mLeakE, SM.mRecordE, SM.mInTransitE,
      SM.mDeleteE, SM.mAcceptE, SM.mChallContainsE, SM.mAfterCorrE,
      SM.mMk, SM.mSt, SM.mB, SM.mWin, SM.mEpoch, SM.mIdx, SM.mTL, SM.mTrans, SM.mChall,
      SM.mComp, SM.mMaxAcc, SM.mLeaks, SM.mCorrs, SM.recPos, SM.recCt,
      SM.isSomeE, SM.otherE, SM.pGet, SM.pSet, SM.sendsInE, SM.healedByE,
      SM.leN, SM.maxN, SM.maxOptE, SM.maxAccSet, SM.maxAccGet,
      SM.posEq, SM.posSender, SM.posEpoch, SM.posIdx, SM.boolEq,
      smOpC, smSampC, smQueryC,
      exprExcessUB_v0, exprExcessUB_v1, exprExcessUB_v2, exprExcessUB_v3, exprExcessUB_v4,
      exprExcessUB_v5, exprExcessUB_v6, exprExcessUB_v7,
      exprExcessUB_var, exprExcessUB_unit, exprExcessUB_bool, exprExcessUB_nat,
      exprExcessUB_none, exprExcessUB_nil, exprExcessUB_add, exprExcessUB_sub,
      exprExcessUB_mulK, exprExcessUB_divK, exprExcessUB_modK, exprExcessUB_lt,
      exprExcessUB_eqN, exprExcessUB_not, exprExcessUB_and, exprExcessUB_ite,
      exprExcessUB_pair, exprExcessUB_fst, exprExcessUB_snd, exprExcessUB_inl,
      exprExcessUB_inr, exprExcessUB_some, exprExcessUB_caseOpt, exprExcessUB_caseSum,
      exprExcessUB_letE, exprExcessUB_op, exprExcessUB_cons, exprExcessUB_len,
      exprExcessUB_take, exprExcessUB_appendL, exprExcessUB_findB, exprExcessUB_anyB,
      exprExcessUB_mapB, exprExcessUB_foldrB, exprExcessUB_tconst, exprExcessUB_tget,
      exprExcessUB_tset, compExcessUB_ret, compExcessUB_bind, compExcessUB_ite,
      compExcessUB_caseOpt, compExcessUB_caseSum, compExcessUB_sample, compExcessUB_query,
      Nat.reduceAdd, Nat.zero_add, Nat.add_zero, Nat.mul_zero]
    omega

end Thm1ExcessHelpers

def ckaOpC (B0 : ℕ) : CKA.CKAOp → ℕ
  | .ckaInitA => 20
  | .ckaInitB => 10
  | .ckaSend => 60
  | .ckaReceive => 35
  | .prngInit => 5
  | .prngUp => 30
  | .fsInitSender => 10
  | .fsInitReceiver => 10
  | .fsSend => 380000
  | .fsReceive B' => 20 * B0 + 3 * ReductionDsl.bits B' + 2710000
  | .eqT => 10
  | .eqI => 10
  | .eqM => 32000
  | .eqE => 140
  | .lamI => 10
  | .defaultE => 60

def ckaSampC {α : Type} : α → ℕ := fun _ => 200
def ckaQueryC {α : Type} : α → ℕ := fun _ => 200
def prngQueryC {α : Type} : α → ℕ := fun _ => 200
def fsQueryC {α : Type} : α → ℕ := fun _ => 100000

section EngineExcessHelpers

variable {KC Γ CCoins T I KR RSt K SS RS M E : Type}
  {ckaInitA : KC → Γ}
  {ckaInitB : KC → Γ}
  {ckaSend : Γ → CCoins → Γ × T × I}
  {ckaReceive : Γ → T → Γ × I}
  {prngInit : KR → RSt}
  {prngUp : RSt → I → RSt × K}
  {fsInitSender : K → SS}
  {fsInitReceiver : K → RS}
  {fsSend : SS → Header T → M → SS × E}
  {fsReceive : RS → Header T → E → Option (RS × ℕ × M)}
  {eqT : T → T → Bool}
  {eqI : I → I → Bool}
  {eqM : M → M → Bool}
  {eqE : E → E → Bool}
  {lam : I}
  {defaultE : E}

local notation "S_cka" => CKA.ckaSig KC Γ CCoins T I KR RSt K SS RS M E
local notation "OO_cka" =>
  CKA.ckaOps ckaInitA ckaInitB ckaSend ckaReceive prngInit prngUp
    fsInitSender fsInitReceiver fsSend fsReceive eqT eqI eqM eqE lam defaultE

lemma optNatLit_excessUB {S' : Sig} {O' : Ops S'} (opEx : O'.Op → ℕ) {Γ'} (o : Option ℕ) :
    exprExcessUB opEx (SM.Engine.optNatLit (O' := O') (Γ' := Γ') o) = 0 := by
  cases o <;> rfl

lemma modeCfgEC_challOKE_excessUB {O' : Ops S_cka} (opEx : O'.Op → ℕ)
    (mo : SM.Construction.Mode) {Γ'} (e : Expr O' Γ' .nat) :
    exprExcessUB opEx ((SM.Engine.modeCfgEC O' mo).challOKE e) ≤ exprExcessUB opEx e := by
  cases h : mo.auth <;> simp [SM.Engine.modeCfgEC, h]

lemma modeCfgEC_injectFullE_excessUB {O' : Ops S_cka} (opEx : O'.Op → ℕ)
    (mo : SM.Construction.Mode) {Γ'} (e : Expr O' Γ' .nat) :
    exprExcessUB opEx ((SM.Engine.modeCfgEC O' mo).injectFullE e) ≤ exprExcessUB opEx e := by
  cases h : mo.auth <;> simp [SM.Engine.modeCfgEC, h]

lemma modeCfgEC_challMsgE_excessUB {O' : Ops S_cka} (opEx : O'.Op → ℕ)
    (mo : SM.Construction.Mode) {Γ'} (ep : Expr O' Γ' .nat) (b : Expr O' Γ' .bool)
    (m0 m1 : Expr O' Γ' (.base .msg)) :
    exprExcessUB opEx ((SM.Engine.modeCfgEC O' mo).challMsgE ep b m0 m1) =
      exprExcessUB opEx b + exprExcessUB opEx m1 + exprExcessUB opEx m0 := rfl

lemma corrDoomE_excessUB {O' : Ops S_cka} (opEx : O'.Op → ℕ) {vpT : Ty S_cka}
    (π : SM.Engine.Policy) {Γ'} (g : Expr O' Γ' (SM.Engine.cGsTy vpT)) (p : Expr O' Γ' .bool) :
    exprExcessUB opEx (SM.Engine.corrDoomE π g p) ≤
      exprExcessUB opEx g + exprExcessUB opEx p := by
  cases h : π.auth <;>
  · simp [SM.Engine.corrDoomE, h, SM.boolEq, SM.ltOptE, SM.leN, SM.maxN, SM.pGet,
      SM.Engine.cGsEpoch, optNatLit_excessUB]

@[simp] lemma rangeListC_excessUB {S' : Sig} {O' : Ops S'} {ι : Type} {spec : OracleSpec ι}
    {I' : Iface S' spec} (opEx : O'.Op → ℕ) (sEx : I'.smp.Samp → ℕ) (qEx : I'.Tag → ℕ)
    (L : ℕ) {Γ' : List (Ty S')} :
    compExcessUB opEx sEx qEx (SM.Construction.rangeListC (O' := O') (I' := I') L (Γ' := Γ')) = 0 := by
  simp [SM.Construction.rangeListC, compExcessUB, exprExcessUB]

lemma unliftVRE_excessUB (opEx : (OO_cka).Op → ℕ) (L : ℕ) {Γ'}
    (vRE : Expr OO_cka Γ' (.tbl (.opt (.opt (.base .rs)))))
    (rsExtE : Expr OO_cka Γ' (.opt (.base .rs)))
    (rngE : Expr OO_cka Γ' (.list .nat)) :
    exprExcessUB opEx (SM.Construction.unliftVRE (ckaInitA := ckaInitA) (ckaInitB := ckaInitB)
      (ckaSend := ckaSend) (ckaReceive := ckaReceive) (prngInit := prngInit) (prngUp := prngUp)
      (fsInitSender := fsInitSender) (fsInitReceiver := fsInitReceiver) (fsSend := fsSend)
      (fsReceive := fsReceive) (eqT := eqT) (eqI := eqI) (eqM := eqM) (eqE := eqE)
      (lam := lam) (defaultE := defaultE) L vRE rsExtE rngE) ≤
      exprExcessUB opEx vRE + exprExcessUB opEx rsExtE + exprExcessUB opEx rngE := by
  simp [SM.Construction.unliftVRE, SM.Construction.unliftEntryE]

structure HooksExcessBounded {ι : Type} {TSpec : OracleSpec.{0, 0} ι}
    {I' : Iface S_cka (unifSpec + TSpec)}
    (B0 : ℕ) (sC : I'.smp.Samp → ℕ) (qC : I'.Tag → ℕ)
    {γvT svT ssvT rsvT hsT : Ty S_cka}
    (hk : SM.Engine.HooksC OO_cka I' γvT svT ssvT rsvT hsT) (Ho Hs Hr : ℕ) : Prop where
  startSend_le : ∀ {Γ'} (h : Expr OO_cka Γ' hsT)
      (ctx : Expr OO_cka Γ'
        (SM.Engine.cGsTy (@SM.Engine.vpTblTy KC Γ CCoins T I KR RSt K SS RS M E γvT svT ssvT rsvT)))
      (p : Expr OO_cka Γ' .bool) (t : Expr OO_cka Γ' .nat)
      (γv : Expr OO_cka Γ' γvT) (σ : Expr OO_cka Γ' svT)
      (r : Expr OO_cka Γ' (.opt (.base .ccoins))),
      compExcessUB (ckaOpC B0) sC qC (hk.startSend h ctx p t γv σ r) ≤
        4 * (exprExcessUB (ckaOpC B0) h + exprExcessUB (ckaOpC B0) ctx + exprExcessUB (ckaOpC B0) p +
          exprExcessUB (ckaOpC B0) t + exprExcessUB (ckaOpC B0) γv + exprExcessUB (ckaOpC B0) σ +
          exprExcessUB (ckaOpC B0) r) + Ho
  startRecv_le : ∀ {Γ'} (h : Expr OO_cka Γ' hsT)
      (ctx : Expr OO_cka Γ'
        (SM.Engine.cGsTy (@SM.Engine.vpTblTy KC Γ CCoins T I KR RSt K SS RS M E γvT svT ssvT rsvT)))
      (p : Expr OO_cka Γ' .bool) (t : Expr OO_cka Γ' .nat)
      (γv : Expr OO_cka Γ' γvT) (σ : Expr OO_cka Γ' svT) (tn : Expr OO_cka Γ' (.base .t)),
      compExcessUB (ckaOpC B0) sC qC (hk.startRecv h ctx p t γv σ tn) ≤
        4 * (exprExcessUB (ckaOpC B0) h + exprExcessUB (ckaOpC B0) ctx + exprExcessUB (ckaOpC B0) p +
          exprExcessUB (ckaOpC B0) t + exprExcessUB (ckaOpC B0) γv + exprExcessUB (ckaOpC B0) σ +
          exprExcessUB (ckaOpC B0) tn) + Ho
  fsSend_le : ∀ {Γ'} (h : Expr OO_cka Γ' hsT)
      (ctx : Expr OO_cka Γ'
        (SM.Engine.cGsTy (@SM.Engine.vpTblTy KC Γ CCoins T I KR RSt K SS RS M E γvT svT ssvT rsvT)))
      (p : Expr OO_cka Γ' .bool) (t : Expr OO_cka Γ' .nat) (ss : Expr OO_cka Γ' ssvT)
      (hdr : Expr OO_cka Γ' (CKA.ckaHdrTy KC Γ CCoins T I KR RSt K SS RS M E))
      (m : Expr OO_cka Γ' (.base .msg))
      (pair : Expr OO_cka Γ' (.opt (.prod (.base .msg) (.base .msg)))),
      compExcessUB (ckaOpC B0) sC qC (hk.fsSend h ctx p t ss hdr m pair) ≤
        4 * (exprExcessUB (ckaOpC B0) h + exprExcessUB (ckaOpC B0) ctx + exprExcessUB (ckaOpC B0) p +
          exprExcessUB (ckaOpC B0) t + exprExcessUB (ckaOpC B0) ss + exprExcessUB (ckaOpC B0) hdr +
          exprExcessUB (ckaOpC B0) m + exprExcessUB (ckaOpC B0) pair) + Hs
  fsRecv_le : ∀ {Γ'} (h : Expr OO_cka Γ' hsT)
      (ctx : Expr OO_cka Γ'
        (SM.Engine.cGsTy (@SM.Engine.vpTblTy KC Γ CCoins T I KR RSt K SS RS M E γvT svT ssvT rsvT)))
      (p : Expr OO_cka Γ' .bool) (t : Expr OO_cka Γ' .nat) (rs : Expr OO_cka Γ' rsvT)
      (hdr : Expr OO_cka Γ' (CKA.ckaHdrTy KC Γ CCoins T I KR RSt K SS RS M E))
      (e : Expr OO_cka Γ' (.base .ct)) (rec_ : Expr OO_cka Γ' (.opt SM.Engine.cRecTy)),
      compExcessUB (ckaOpC B0) sC qC (hk.fsRecv h ctx p t rs hdr e rec_) ≤
        4 * (exprExcessUB (ckaOpC B0) h + exprExcessUB (ckaOpC B0) ctx + exprExcessUB (ckaOpC B0) p +
          exprExcessUB (ckaOpC B0) t + exprExcessUB (ckaOpC B0) rs + exprExcessUB (ckaOpC B0) hdr +
          exprExcessUB (ckaOpC B0) e + exprExcessUB (ckaOpC B0) rec_) + Hr
  commit_le : ∀ {Γ'} (h : Expr OO_cka Γ' hsT)
      (ctx : Expr OO_cka Γ'
        (SM.Engine.cGsTy (@SM.Engine.vpTblTy KC Γ CCoins T I KR RSt K SS RS M E γvT svT ssvT rsvT)))
      (p : Expr OO_cka Γ' .bool)
      (old new : Expr OO_cka Γ'
        (@SM.Engine.vpTblTy KC Γ CCoins T I KR RSt K SS RS M E γvT svT ssvT rsvT)),
      compExcessUB (ckaOpC B0) sC qC (hk.commit h ctx p old new) ≤
        4 * (exprExcessUB (ckaOpC B0) h + exprExcessUB (ckaOpC B0) ctx + exprExcessUB (ckaOpC B0) p +
          exprExcessUB (ckaOpC B0) old + exprExcessUB (ckaOpC B0) new) + Ho
  reveal_le : ∀ {Γ'} (h : Expr OO_cka Γ' hsT)
      (ctx : Expr OO_cka Γ'
        (SM.Engine.cGsTy (@SM.Engine.vpTblTy KC Γ CCoins T I KR RSt K SS RS M E γvT svT ssvT rsvT)))
      (p : Expr OO_cka Γ' .bool)
      (vp : Expr OO_cka Γ'
        (@SM.Engine.vpTblTy KC Γ CCoins T I KR RSt K SS RS M E γvT svT ssvT rsvT)),
      compExcessUB (ckaOpC B0) sC qC (hk.reveal h ctx p vp) ≤
        4 * (exprExcessUB (ckaOpC B0) h + exprExcessUB (ckaOpC B0) ctx + exprExcessUB (ckaOpC B0) p +
          exprExcessUB (ckaOpC B0) vp) + Ho

lemma HooksExcessBounded.mono {ι : Type} {TSpec : OracleSpec.{0, 0} ι}
    {I' : Iface S_cka (unifSpec + TSpec)}
    {B0 : ℕ} {sC : I'.smp.Samp → ℕ} {qC : I'.Tag → ℕ}
    {γvT svT ssvT rsvT hsT : Ty S_cka}
    {hk : SM.Engine.HooksC OO_cka I' γvT svT ssvT rsvT hsT} {Ho Ho' Hs Hs' Hr Hr' : ℕ}
    (ho : Ho ≤ Ho') (hs : Hs ≤ Hs') (hr : Hr ≤ Hr')
    (hhk : HooksExcessBounded B0 sC qC hk Ho Hs Hr) : HooksExcessBounded B0 sC qC hk Ho' Hs' Hr' where
  startSend_le hE ctx p t γv σ r := (hhk.startSend_le hE ctx p t γv σ r).trans (by omega)
  startRecv_le hE ctx p t γv σ tn := (hhk.startRecv_le hE ctx p t γv σ tn).trans (by omega)
  fsSend_le hE ctx p t ss hdr m pair := (hhk.fsSend_le hE ctx p t ss hdr m pair).trans (by omega)
  fsRecv_le hE ctx p t rs hdr e rec_ := (hhk.fsRecv_le hE ctx p t rs hdr e rec_).trans (by omega)
  commit_le hE ctx p old new := (hhk.commit_le hE ctx p old new).trans (by omega)
  reveal_le hE ctx p vp := (hhk.reveal_le hE ctx p vp).trans (by omega)

lemma cInTransitE_excessUB {vpT : Ty S_cka} (B0 L : ℕ) {Γ'}
    (s : Expr OO_cka Γ' (SM.Engine.cGsTy vpT))
    (qParty : Expr OO_cka Γ' .bool)
    (c : Expr OO_cka Γ' (CKA.ckaHdrCtTy KC Γ CCoins T I KR RSt K SS RS M E)) :
    exprExcessUB (ckaOpC B0) (SM.Engine.cInTransitE L s qParty c) ≤
      exprExcessUB (ckaOpC B0) s + exprExcessUB (ckaOpC B0) qParty +
        exprExcessUB (ckaOpC B0) c + 150 * L := by
  simp only [SM.Engine.cInTransitE, SM.Engine.cGsTrans, SM.Engine.cRecPos, SM.Engine.cRecCt,
    SM.Engine.hdrCtEqE, SM.Engine.optTEqE, SM.posSender, SM.boolEq, ckaOpC,
    exprExcessUB_v0, exprExcessUB_v1, exprExcessUB_v2, exprExcessUB_v3, exprExcessUB_v4,
    exprExcessUB_var, exprExcessUB_bool, exprExcessUB_eqN,
    exprExcessUB_not, exprExcessUB_and, exprExcessUB_ite, exprExcessUB_pair, exprExcessUB_fst,
    exprExcessUB_snd, exprExcessUB_caseOpt, exprExcessUB_letE, exprExcessUB_op,
    exprExcessUB_findB, Nat.reduceAdd, Nat.zero_add, Nat.add_zero]
  omega

lemma pureEngineExprs_excessUB {O' : Ops S_cka} (opEx : O'.Op → ℕ) {vpT hsT : Ty S_cka}
    (L _qep _maxSkip : ℕ) (π : SM.Engine.Policy) {Γ'}
    (es : Expr O' Γ' (SM.Engine.esTy vpT hsT)) :
    exprExcessUB opEx (SM.Engine.authOutE L 3 π es) = exprExcessUB opEx es ∧
    exprExcessUB opEx (SM.Engine.privValidE L 3 π es) = exprExcessUB opEx es := by
  constructor <;>
  · simp [SM.Engine.authOutE, SM.Engine.privValidE, SM.Engine.cAuthOKE, SM.Engine.cCanonE,
      SM.validGuessE, SM.healedByE, SM.optNatEqE, SM.ltOptE, SM.leN, SM.maxN, SM.boolEq,
      SM.receiverOfE, SM.Engine.esAbort, SM.Engine.esG, SM.Engine.cGsWin,
      SM.Engine.cGsLeaks, SM.Engine.cGsCorrs, optNatLit_excessUB]

lemma privOutC_excessUB_le {O' : Ops S_cka} {ι : Type} {TSpec : OracleSpec ι}
    {I' : Iface S_cka TSpec} {vpT hsT : Ty S_cka}
    (opEx : O'.Op → ℕ) (sEx : I'.smp.Samp → ℕ) (qEx : I'.Tag → ℕ)
    (L : ℕ) (π : SM.Engine.Policy)
    (drawBit : ∀ {Γ''}, Comp O' I' Γ'' .bool)
    {Γ'} (b b' : Expr O' Γ' .bool) (es : Expr O' Γ' (SM.Engine.esTy vpT hsT)) :
    compExcessUB opEx sEx qEx (SM.Engine.privOutC L 3 π drawBit b b' es) ≤
      exprExcessUB opEx es + exprExcessUB opEx b + 2 * exprExcessUB opEx b' +
        compExcessUB opEx sEx qEx (drawBit (Γ'' := Γ')) := by
  have hpv := (pureEngineExprs_excessUB opEx L 0 0 π es).2
  simp only [SM.Engine.privOutC, SM.boolEq, compExcessUB_ite, compExcessUB_ret,
    exprExcessUB_ite, exprExcessUB_not, hpv]
  omega

lemma vSendC_excessUB_le {ι : Type} {TSpec : OracleSpec.{0, 0} ι}
    {I' : Iface S_cka (unifSpec + TSpec)} {B0 : ℕ} {sC : I'.smp.Samp → ℕ} {qC : I'.Tag → ℕ}
    {γvT svT ssvT rsvT hsT : Ty S_cka}
    (hk : SM.Engine.HooksC OO_cka I' γvT svT ssvT rsvT hsT) (Ho Hs Hr : ℕ)
    (hhk : HooksExcessBounded B0 sC qC hk Ho Hs Hr)
    {Γ'} (h : Expr OO_cka Γ' hsT)
    (ctx : Expr OO_cka Γ'
      (SM.Engine.cGsTy (@SM.Engine.vpTblTy KC Γ CCoins T I KR RSt K SS RS M E γvT svT ssvT rsvT)))
    (p : Expr OO_cka Γ' .bool)
    (s : Expr OO_cka Γ' (@SM.Engine.vpTblTy KC Γ CCoins T I KR RSt K SS RS M E γvT svT ssvT rsvT))
    (m : Expr OO_cka Γ' (.base .msg))
    (pair : Expr OO_cka Γ' (.opt (.prod (.base .msg) (.base .msg))))
    (r : Expr OO_cka Γ' (.opt (.base .ccoins))) :
    compExcessUB (ckaOpC B0) sC qC (SM.Engine.vSendC hk h ctx p s m pair r) ≤
      6 * (exprExcessUB (ckaOpC B0) h + exprExcessUB (ckaOpC B0) ctx + exprExcessUB (ckaOpC B0) p +
        exprExcessUB (ckaOpC B0) s + exprExcessUB (ckaOpC B0) m + exprExcessUB (ckaOpC B0) pair +
        exprExcessUB (ckaOpC B0) r) + Ho + Hs + 60 := by
  let vpT := @SM.Engine.vpTblTy KC Γ CCoins T I KR RSt K SS RS M E γvT svT ssvT rsvT
  let Γ0 : List (Ty S_cka) :=
    .prod hsT (.prod (SM.Engine.cGsTy vpT) (.prod .bool (.prod vpT (.opt (.base .ccoins))))) ::
      .prod hsT (.prod (SM.Engine.cGsTy vpT) (.prod .bool (.prod vpT (.prod (.base .msg)
        (.prod (.opt (.prod (.base .msg) (.base .msg))) (.opt (.base .ccoins))))))) :: Γ'
  let Γ1 : List (Ty S_cka) :=
    ssvT :: vpT :: .prod (.opt vpT) hsT ::
      .prod hsT (.prod (SM.Engine.cGsTy vpT) (.prod .bool (.prod vpT (.prod (.base .msg)
        (.prod (.opt (.prod (.base .msg) (.base .msg))) (.opt (.base .ccoins))))))) :: Γ'
  have hss := hhk.startSend_le (Γ' := Γ0)
    (.fst .v0) (.fst (.snd .v0)) (.fst (.snd (.snd .v0)))
    (.add (SM.Engine.vpTcurNat (.fst (.snd (.snd (.snd .v0))))) (.nat 1))
    (SM.Engine.vpΓ (.fst (.snd (.snd (.snd .v0)))))
    (SM.Engine.vpRoot (.fst (.snd (.snd (.snd .v0)))))
    (.snd (.snd (.snd (.snd .v0))))
  have hfs := hhk.fsSend_le (Γ' := Γ1)
    (.snd .v2) (.fst (.snd .v3)) (.fst (.snd (.snd .v3)))
    (SM.Engine.vpTcurNat .v1) .v0
    (.pair (SM.Engine.vpTcurNat .v1) (SM.Engine.vpTcur .v1))
    (.fst (.snd (.snd (.snd (.snd .v3)))))
    (.fst (.snd (.snd (.snd (.snd (.snd .v3))))))
  simp only [SM.Engine.vpTcurNat, SM.Engine.vpTcur, SM.Engine.vpΓ, SM.Engine.vpRoot,
    exprExcessUB_v0, exprExcessUB_v1, exprExcessUB_v2, exprExcessUB_v3, exprExcessUB_var,
    exprExcessUB_nat, exprExcessUB_add, exprExcessUB_pair, exprExcessUB_fst, exprExcessUB_snd,
    Nat.add_zero, Nat.mul_zero, Nat.zero_add] at hss hfs
  simp only [SM.Engine.vSendC, SM.Engine.vSendStep1C, SM.sendsInE,
    SM.Engine.vpMk, SM.Engine.vpId, SM.Engine.vpVS, SM.Engine.vpVR, SM.Engine.vpTcur,
    SM.Engine.vpTcurNat, SM.Engine.vpSetVS, SM.Engine.vpΓ, SM.Engine.vpRoot, ckaOpC,
    exprExcessUB_v0, exprExcessUB_v1, exprExcessUB_v2, exprExcessUB_v3, exprExcessUB_v4,
    exprExcessUB_var, exprExcessUB_unit, exprExcessUB_bool, exprExcessUB_nat, exprExcessUB_add,
    exprExcessUB_eqN, exprExcessUB_modK, exprExcessUB_lt, exprExcessUB_and,
    exprExcessUB_not, exprExcessUB_ite, exprExcessUB_pair, exprExcessUB_fst, exprExcessUB_snd,
    exprExcessUB_none, exprExcessUB_some, exprExcessUB_caseOpt, exprExcessUB_letE, exprExcessUB_op,
    compExcessUB_ret, compExcessUB_bind, compExcessUB_ite, compExcessUB_caseOpt,
    Nat.add_zero, Nat.zero_add]
  omega

lemma vRecvC_excessUB_le {ι : Type} {TSpec : OracleSpec.{0, 0} ι}
    {I' : Iface S_cka (unifSpec + TSpec)} {B0 : ℕ} {sC : I'.smp.Samp → ℕ} {qC : I'.Tag → ℕ}
    {γvT svT ssvT rsvT hsT : Ty S_cka}
    (hk : SM.Engine.HooksC OO_cka I' γvT svT ssvT rsvT hsT) (Ho Hs Hr : ℕ)
    (hhk : HooksExcessBounded B0 sC qC hk Ho Hs Hr)
    {Γ'} (h : Expr OO_cka Γ' hsT)
    (ctx : Expr OO_cka Γ'
      (SM.Engine.cGsTy (@SM.Engine.vpTblTy KC Γ CCoins T I KR RSt K SS RS M E γvT svT ssvT rsvT)))
    (p : Expr OO_cka Γ' .bool)
    (s : Expr OO_cka Γ' (@SM.Engine.vpTblTy KC Γ CCoins T I KR RSt K SS RS M E γvT svT ssvT rsvT))
    (c : Expr OO_cka Γ' (CKA.ckaHdrCtTy KC Γ CCoins T I KR RSt K SS RS M E))
    (rec_ : Expr OO_cka Γ' (.opt SM.Engine.cRecTy)) :
    compExcessUB (ckaOpC B0) sC qC (SM.Engine.vRecvC hk h ctx p s c rec_) ≤
      6 * (exprExcessUB (ckaOpC B0) h + exprExcessUB (ckaOpC B0) ctx + exprExcessUB (ckaOpC B0) p +
        exprExcessUB (ckaOpC B0) s + exprExcessUB (ckaOpC B0) c + exprExcessUB (ckaOpC B0) rec_) +
        Ho + Hr := by
  let vpT := @SM.Engine.vpTblTy KC Γ CCoins T I KR RSt K SS RS M E γvT svT ssvT rsvT
  let hdrCtT := CKA.ckaHdrCtTy KC Γ CCoins T I KR RSt K SS RS M E
  let Γ0 : List (Ty S_cka) :=
    .base .t :: .prod hsT (.prod (SM.Engine.cGsTy vpT) (.prod .bool (.prod vpT hdrCtT))) ::
      .prod hsT (.prod (SM.Engine.cGsTy vpT) (.prod .bool (.prod vpT
        (.prod hdrCtT (.opt SM.Engine.cRecTy))))) :: Γ'
  let Γ1 : List (Ty S_cka) :=
    rsvT :: vpT :: .opt vpT :: .prod (.opt (.opt vpT)) hsT ::
      .prod hsT (.prod (SM.Engine.cGsTy vpT) (.prod .bool (.prod vpT
        (.prod hdrCtT (.opt SM.Engine.cRecTy))))) :: Γ'
  have hsr := hhk.startRecv_le (Γ' := Γ0)
    (.fst .v1) (.fst (.snd .v1)) (.fst (.snd (.snd .v1)))
    (.fst (.fst (.snd (.snd (.snd (.snd .v1))))))
    (SM.Engine.vpΓ (.fst (.snd (.snd (.snd .v1)))))
    (SM.Engine.vpRoot (.fst (.snd (.snd (.snd .v1))))) .v0
  have hfr := hhk.fsRecv_le (Γ' := Γ1)
    (.snd .v3) (.fst (.snd .v4)) (.fst (.snd (.snd .v4)))
    (.fst (.fst (.fst (.snd (.snd (.snd (.snd .v4))))))) .v0
    (.fst (.fst (.snd (.snd (.snd (.snd .v4))))))
    (.snd (.fst (.snd (.snd (.snd (.snd .v4))))))
    (.snd (.snd (.snd (.snd (.snd .v4)))))
  simp only [SM.Engine.vpΓ, SM.Engine.vpRoot,
    exprExcessUB_v0, exprExcessUB_v1, exprExcessUB_v3, exprExcessUB_v4, exprExcessUB_var,
    exprExcessUB_fst, exprExcessUB_snd, Nat.add_zero, Nat.mul_zero, Nat.zero_add] at hsr hfr
  simp only [SM.Engine.vRecvC, SM.Engine.vRecvStep1C, SM.orE, SM.sendsInE,
    SM.Engine.vpMk, SM.Engine.vpId, SM.Engine.vpVS, SM.Engine.vpVR, SM.Engine.vpTcur,
    SM.Engine.vpTcurNat, SM.Engine.vpSetVR, SM.Engine.vpΓ, SM.Engine.vpRoot,
    exprExcessUB_v0, exprExcessUB_v1, exprExcessUB_v2, exprExcessUB_v3, exprExcessUB_v4,
    exprExcessUB_v5, exprExcessUB_v6, exprExcessUB_v7, exprExcessUB_var,
    exprExcessUB_bool, exprExcessUB_nat, exprExcessUB_add, exprExcessUB_lt,
    exprExcessUB_eqN, exprExcessUB_modK, exprExcessUB_not, exprExcessUB_and, exprExcessUB_ite,
    exprExcessUB_pair, exprExcessUB_fst, exprExcessUB_snd, exprExcessUB_none, exprExcessUB_some,
    exprExcessUB_caseOpt, exprExcessUB_letE, exprExcessUB_tget, exprExcessUB_tset,
    compExcessUB_ret, compExcessUB_bind, compExcessUB_ite, compExcessUB_caseOpt,
    Nat.add_zero, Nat.zero_add]
  omega

lemma commitEC_excessUB_le {ι : Type} {TSpec : OracleSpec.{0, 0} ι}
    {I' : Iface S_cka (unifSpec + TSpec)} {B0 : ℕ} {sC : I'.smp.Samp → ℕ} {qC : I'.Tag → ℕ}
    {γvT svT ssvT rsvT hsT : Ty S_cka}
    (hk : SM.Engine.HooksC OO_cka I' γvT svT ssvT rsvT hsT) (Ho Hs Hr L : ℕ)
    (hhk : HooksExcessBounded B0 sC qC hk Ho Hs Hr)
    {Γ'} (es : Expr OO_cka Γ'
      (SM.Engine.esTy (@SM.Engine.vpTblTy KC Γ CCoins T I KR RSt K SS RS M E γvT svT ssvT rsvT) hsT))
    (s : Expr OO_cka Γ'
      (SM.Engine.cGsTy (@SM.Engine.vpTblTy KC Γ CCoins T I KR RSt K SS RS M E γvT svT ssvT rsvT)))
    (p : Expr OO_cka Γ' .bool)
    (old new : Expr OO_cka Γ'
      (@SM.Engine.vpTblTy KC Γ CCoins T I KR RSt K SS RS M E γvT svT ssvT rsvT))
    (pos : Expr OO_cka Γ' SM.posTy) :
    compExcessUB (ckaOpC B0) sC qC (SM.Engine.commitEC hk L es s p old new pos) ≤
      6 * (exprExcessUB (ckaOpC B0) es + exprExcessUB (ckaOpC B0) s + exprExcessUB (ckaOpC B0) p +
        exprExcessUB (ckaOpC B0) old + exprExcessUB (ckaOpC B0) new +
        exprExcessUB (ckaOpC B0) pos) + Ho := by
  let vpT := @SM.Engine.vpTblTy KC Γ CCoins T I KR RSt K SS RS M E γvT svT ssvT rsvT
  let Γ0 : List (Ty S_cka) :=
    .prod (SM.Engine.esTy vpT hsT) (.prod (SM.Engine.cGsTy vpT)
      (.prod .bool (.prod vpT vpT))) :: Γ'
  have hcm := hhk.commit_le (Γ' := Γ0)
    (SM.Engine.esH (.fst .v0)) (.fst (.snd .v0)) (.fst (.snd (.snd .v0)))
    (.fst (.snd (.snd (.snd .v0)))) (.snd (.snd (.snd (.snd .v0))))
  simp only [SM.Engine.esH, exprExcessUB_v0, exprExcessUB_var, exprExcessUB_fst, exprExcessUB_snd,
    Nat.add_zero, Nat.mul_zero, Nat.zero_add] at hcm
  simp only [SM.Engine.commitEC, SM.Engine.cAcceptE, SM.Engine.cDeleteE, SM.Engine.cGsSetStP,
    SM.Engine.cCompDeleteE, SM.Engine.cCompSetE,
    SM.Engine.cGsMk, SM.Engine.esMk, SM.Engine.esG, SM.Engine.esH, SM.Engine.esAbort,
    SM.Engine.cRecPos, SM.Engine.cGsSt, SM.Engine.cGsB, SM.Engine.cGsWin, SM.Engine.cGsEpoch,
    SM.Engine.cGsIdx, SM.Engine.cGsTL, SM.Engine.cGsTrans, SM.Engine.cGsChall, SM.Engine.cGsComp,
    SM.Engine.cGsMaxAcc, SM.Engine.cGsLeaks, SM.Engine.cGsCorrs,
    SM.pSet, SM.pGet, SM.maxAccSet, SM.maxAccGet, SM.maxN, SM.leN,
    SM.posEq, SM.boolEq, SM.posSender, SM.posEpoch, SM.posIdx,
    exprExcessUB_v0, exprExcessUB_v1, exprExcessUB_v2, exprExcessUB_v3, exprExcessUB_var,
    exprExcessUB_bool, exprExcessUB_nat, exprExcessUB_add, exprExcessUB_lt, exprExcessUB_eqN,
    exprExcessUB_not, exprExcessUB_and, exprExcessUB_ite, exprExcessUB_pair, exprExcessUB_fst,
    exprExcessUB_snd, exprExcessUB_none, exprExcessUB_some, exprExcessUB_caseOpt,
    exprExcessUB_nil, exprExcessUB_cons, exprExcessUB_letE, exprExcessUB_foldrB,
    exprExcessUB_tget, exprExcessUB_tset,
    compExcessUB_ret, compExcessUB_bind, compExcessUB_ite, compExcessUB_caseOpt,
    Nat.add_zero, Nat.zero_add, Nat.mul_zero]
  omega

lemma implEC_excessUB_le {ι : Type} {TSpec : OracleSpec.{0, 0} ι}
    {I' : Iface S_cka (unifSpec + TSpec)} {B0 : ℕ} {sC : I'.smp.Samp → ℕ} {qC : I'.Tag → ℕ}
    {γvT svT ssvT rsvT hsT : Ty S_cka}
    (hk : SM.Engine.HooksC OO_cka I' γvT svT ssvT rsvT hsT) (Ho Hs Hr L qep maxSkip : ℕ)
    (mo : SM.Construction.Mode) (hhk : HooksExcessBounded B0 sC qC hk Ho Hs Hr)
    {Γ'} (es : Expr OO_cka Γ'
      (SM.Engine.esTy (@SM.Engine.vpTblTy KC Γ CCoins T I KR RSt K SS RS M E γvT svT ssvT rsvT) hsT))
    (q : Expr OO_cka Γ' (CKA.ckaSMQ KC Γ CCoins T I KR RSt K SS RS M E)) :
    compExcessUB (ckaOpC B0) sC qC
      (SM.Engine.implEC hk L 3 qep maxSkip (SM.Engine.modeCfgEC OO_cka mo) mo.policy es q) ≤
      60 * (exprExcessUB (ckaOpC B0) es + exprExcessUB (ckaOpC B0) q) +
        7 * Ho + 2 * Hs + 2 * Hr + 300 * L + 40000 := by
  let vpT := @SM.Engine.vpTblTy KC Γ CCoins T I KR RSt K SS RS M E γvT svT ssvT rsvT
  let esT := SM.Engine.esTy vpT hsT
  let smqT := CKA.ckaSMQ KC Γ CCoins T I KR RSt K SS RS M E
  let hdrCtT := CKA.ckaHdrCtTy KC Γ CCoins T I KR RSt K SS RS M E
  let trQ : Ty S_cka := .prod .bool (.prod (.base .msg) (.opt (.base .ccoins)))
  let chQ : Ty S_cka := .prod .bool (.prod (.base .msg) (.prod (.base .msg) (.opt (.base .ccoins))))
  let dlQ : Ty S_cka := .prod .bool hdrCtT
  let decT : Ty S_cka := .prod vpT (.prod .nat (.prod .nat (.base .msg)))
  let Γ_base : List (Ty S_cka) := .prod esT smqT :: Γ'
  let Γ_cr : List (Ty S_cka) := .bool :: Γ_base
  let Γ_s1 : List (Ty S_cka) := .sum (.sum (.sum trQ chQ) dlQ) dlQ :: Γ_base
  let Γ_ij : List (Ty S_cka) := dlQ :: Γ_s1
  let Γ_s2 : List (Ty S_cka) := .sum (.sum trQ chQ) dlQ :: Γ_s1
  let Γ_dl : List (Ty S_cka) := dlQ :: Γ_s2
  let Γ_s3 : List (Ty S_cka) := .sum trQ chQ :: Γ_s2
  let Γ_tr : List (Ty S_cka) := trQ :: Γ_s3
  let Γ_ch : List (Ty S_cka) := chQ :: Γ_s3
  have hvs_tr := vSendC_excessUB_le hk Ho Hs Hr hhk
    (Γ' := SM.Engine.cGsTy vpT :: .prod esT trQ :: Γ_tr)
    (SM.Engine.esH (.fst .v1)) .v0 (.fst (.snd .v1))
    (SM.pGet (SM.Engine.cGsSt .v0) (.fst (.snd .v1)))
    (.fst (.snd (.snd .v1))) .none (.snd (.snd (.snd .v1)))
  have hvs_ch := vSendC_excessUB_le hk Ho Hs Hr hhk
    (Γ' := SM.Engine.cGsTy vpT :: .prod esT chQ :: Γ_ch)
    (SM.Engine.esH (.fst .v1)) .v0 (.fst (.snd .v1))
    (SM.pGet (SM.Engine.cGsSt .v0) (.fst (.snd .v1)))
    ((SM.Engine.modeCfgEC OO_cka mo).challMsgE
      (SM.pGet (SM.Engine.cGsEpoch .v0) (.fst (.snd .v1)))
      (SM.Engine.cGsB (SM.Engine.esG (.fst .v1)))
      (.fst (.snd (.snd .v1))) (.fst (.snd (.snd (.snd .v1)))))
    (.some (.pair (.fst (.snd (.snd .v1))) (.fst (.snd (.snd (.snd .v1))))))
    (.snd (.snd (.snd (.snd .v1))))
  have hok_ch := modeCfgEC_challOKE_excessUB (O' := OO_cka) (ckaOpC B0) mo
    (Γ' := SM.Engine.cGsTy vpT :: .prod esT chQ :: Γ_ch)
    (SM.pGet (SM.Engine.cGsEpoch .v0) (.fst (.snd .v1)))
  let Γ_dl0 : List (Ty S_cka) := .prod esT dlQ :: Γ_dl
  have hit_dl := cInTransitE_excessUB (ckaInitA := ckaInitA) (ckaInitB := ckaInitB)
    (ckaSend := ckaSend) (ckaReceive := ckaReceive) (prngInit := prngInit) (prngUp := prngUp)
    (fsInitSender := fsInitSender) (fsInitReceiver := fsInitReceiver) (fsSend := fsSend)
    (fsReceive := fsReceive) (eqT := eqT) (eqI := eqI) (eqM := eqM) (eqE := eqE)
    (lam := lam) (defaultE := defaultE) (vpT := vpT) B0 L (Γ' := Γ_dl0)
    (SM.Engine.esG (.fst .v0)) (SM.otherE (.fst (.snd .v0))) (.snd (.snd .v0))
  have hvr_dl := vRecvC_excessUB_le hk Ho Hs Hr hhk (Γ' := SM.Engine.cRecTy :: Γ_dl0)
    (SM.Engine.esH (.fst .v1)) (SM.Engine.esG (.fst .v1)) (.fst (.snd .v1))
    (SM.pGet (SM.Engine.cGsSt (SM.Engine.esG (.fst .v1))) (.fst (.snd .v1)))
    (.snd (.snd .v1)) (.some .v0)
  have hcm_dl := commitEC_excessUB_le hk Ho Hs Hr L hhk
    (Γ' := decT :: .opt decT :: .prod (.opt (.opt decT)) hsT :: SM.Engine.cRecTy :: Γ_dl0)
    (SM.Engine.esSetH (.fst .v4) (.snd .v2)) (SM.Engine.esG (.fst .v4)) (.fst (.snd .v4))
    (SM.pGet (SM.Engine.cGsSt (SM.Engine.esG (.fst .v4))) (.fst (.snd .v4)))
    (.fst .v0) (SM.Engine.cRecPos .v3)
  let Γ_ij0 : List (Ty S_cka) := .prod esT dlQ :: Γ_ij
  have hit_ij := cInTransitE_excessUB (ckaInitA := ckaInitA) (ckaInitB := ckaInitB)
    (ckaSend := ckaSend) (ckaReceive := ckaReceive) (prngInit := prngInit) (prngUp := prngUp)
    (fsInitSender := fsInitSender) (fsInitReceiver := fsInitReceiver) (fsSend := fsSend)
    (fsReceive := fsReceive) (eqT := eqT) (eqI := eqI) (eqM := eqM) (eqE := eqE)
    (lam := lam) (defaultE := defaultE) (vpT := vpT) B0 L (Γ' := Γ_ij0)
    (SM.Engine.esG (.fst .v0)) (SM.otherE (.fst (.snd .v0))) (.snd (.snd .v0))
  have hvr_ij := vRecvC_excessUB_le hk Ho Hs Hr hhk (Γ' := Γ_ij0)
    (SM.Engine.esH (.fst .v0)) (SM.Engine.esG (.fst .v0)) (.fst (.snd .v0))
    (SM.pGet (SM.Engine.cGsSt (SM.Engine.esG (.fst .v0))) (.fst (.snd .v0)))
    (.snd (.snd .v0)) .none
  have hcm_ij := commitEC_excessUB_le hk Ho Hs Hr L hhk
    (Γ' := decT :: .opt decT :: .prod (.opt (.opt decT)) hsT :: Γ_ij0)
    (SM.Engine.esSetH (.fst .v3) (.snd .v2)) (SM.Engine.esG (.fst .v3)) (.fst (.snd .v3))
    (SM.pGet (SM.Engine.cGsSt (SM.Engine.esG (.fst .v3))) (.fst (.snd .v3)))
    (.fst .v0) (.pair (SM.otherE (.fst (.snd .v3))) (.pair (.fst (.snd .v0)) (.fst (.snd (.snd .v0)))))
  have hij_ij := modeCfgEC_injectFullE_excessUB (O' := OO_cka) (ckaOpC B0) mo
    (Γ' := decT :: .opt decT :: .prod (.opt (.opt decT)) hsT :: Γ_ij0) (.fst (.snd .v0))
  let Γ_cr0 : List (Ty S_cka) := .prod esT .bool :: Γ_cr
  have hcd_cr := corrDoomE_excessUB (O' := OO_cka) (ckaOpC B0) mo.policy (Γ' := Γ_cr0)
    (SM.Engine.esG (.fst .v0)) (.snd .v0)
  have hrv_cr := hhk.reveal_le (Γ' := Γ_cr0)
    (SM.Engine.esH (.fst .v0)) (SM.Engine.esG (.fst .v0)) (.snd .v0)
    (SM.pGet (SM.Engine.cGsSt (SM.Engine.esG (.fst .v0))) (.snd .v0))
  simp only [modeCfgEC_challMsgE_excessUB, SM.Engine.esG, SM.Engine.esH, SM.Engine.esSetH,
    SM.Engine.esMk, SM.Engine.esAbort,
    SM.Engine.cGsSt, SM.Engine.cGsEpoch, SM.Engine.cGsB, SM.Engine.cRecPos, SM.pGet, SM.otherE,
    exprExcessUB_v0, exprExcessUB_v1, exprExcessUB_v2, exprExcessUB_v3, exprExcessUB_v4,
    exprExcessUB_var, exprExcessUB_not, exprExcessUB_ite, exprExcessUB_pair, exprExcessUB_fst,
    exprExcessUB_snd, exprExcessUB_none, exprExcessUB_some, exprExcessUB_letE,
    Nat.add_zero, Nat.zero_add, Nat.mul_zero]
    at hvs_tr hvs_ch hok_ch hit_dl hvr_dl hcm_dl hit_ij hvr_ij hcm_ij hij_ij hcd_cr hrv_cr
  simp only [SM.Engine.implEC, SM.Engine.transmitEC, SM.Engine.challEC, SM.Engine.deliverEC,
    SM.Engine.injectEC, SM.Engine.corrEC,
    SM.Engine.cEpMgmtE, SM.Engine.cSafeChE, SM.Engine.cSafeInjE, SM.Engine.cLeakE,
    SM.Engine.cCompContainsE, SM.Engine.cCompInsertE, SM.Engine.cCompSetE,
    SM.Engine.cRecordE, SM.Engine.cChallContainsE,
    SM.Engine.cMustBeCorrectE, SM.Engine.cTrivialE, SM.Engine.cCorrAllowedE,
    SM.Engine.cAfterCorrE, SM.Engine.leakDoomE,
    SM.Engine.esMk, SM.Engine.esG, SM.Engine.esH, SM.Engine.esAbort,
    SM.Engine.esSetG, SM.Engine.esSetH, SM.Engine.esSetAbort,
    SM.Engine.cGsMk, SM.Engine.cGsSetWin, SM.Engine.cGsSt, SM.Engine.cGsB, SM.Engine.cGsWin,
    SM.Engine.cGsEpoch, SM.Engine.cGsIdx, SM.Engine.cGsTL, SM.Engine.cGsTrans,
    SM.Engine.cGsChall, SM.Engine.cGsComp, SM.Engine.cGsMaxAcc, SM.Engine.cGsLeaks,
    SM.Engine.cGsCorrs, SM.Engine.cRecPos, SM.Engine.cRecMsg, modeCfgEC_challMsgE_excessUB,
    optNatLit_excessUB, SM.sendsInE, SM.healedByE, SM.pGet, SM.pSet, SM.orE, SM.isSomeE,
    SM.otherE, SM.leN, SM.minN, SM.maxN, SM.maxOptE, SM.maxAccGet, SM.ltOptE,
    SM.posEq, SM.boolEq, SM.posSender, SM.posEpoch, SM.posIdx, ckaOpC,
    exprExcessUB_v0, exprExcessUB_v1, exprExcessUB_v2, exprExcessUB_v3, exprExcessUB_v4,
    exprExcessUB_v5, exprExcessUB_v6, exprExcessUB_v7, exprExcessUB_var,
    exprExcessUB_unit, exprExcessUB_bool, exprExcessUB_nat,
    exprExcessUB_none, exprExcessUB_nil, exprExcessUB_add, exprExcessUB_sub, exprExcessUB_mulK,
    exprExcessUB_divK, exprExcessUB_modK, exprExcessUB_lt, exprExcessUB_eqN, exprExcessUB_not,
    exprExcessUB_and, exprExcessUB_ite, exprExcessUB_pair, exprExcessUB_fst, exprExcessUB_snd,
    exprExcessUB_inl, exprExcessUB_inr, exprExcessUB_some, exprExcessUB_caseOpt,
    exprExcessUB_caseSum, exprExcessUB_letE, exprExcessUB_op, exprExcessUB_cons,
    exprExcessUB_len, exprExcessUB_take, exprExcessUB_appendL, exprExcessUB_findB,
    exprExcessUB_anyB, exprExcessUB_mapB, exprExcessUB_foldrB, exprExcessUB_tconst,
    exprExcessUB_tget, exprExcessUB_tset,
    compExcessUB_ret, compExcessUB_bind, compExcessUB_ite, compExcessUB_caseOpt,
    compExcessUB_caseSum, Nat.reduceAdd, Nat.add_zero, Nat.zero_add, Nat.mul_zero]
  omega

section HooksCKAAndPRNGExcess

variable {sampKR : ProbComp KR} {sampKC : ProbComp KC} {sampCCoins : ProbComp CCoins}
  {sampI : ProbComp I} {sampK : ProbComp K}

lemma hooksCKAC_excessBounded (B0 B : ℕ) (mo : SM.Construction.Mode) :
    HooksExcessBounded B0 ckaSampC ckaQueryC
      (SM.Construction.hooksCKAC (ckaInitA := ckaInitA) (ckaInitB := ckaInitB)
        (ckaSend := ckaSend) (ckaReceive := ckaReceive) (prngInit := prngInit)
        (prngUp := prngUp) (fsInitSender := fsInitSender) (fsInitReceiver := fsInitReceiver)
        (fsSend := fsSend) (fsReceive := fsReceive) (eqT := eqT) (eqI := eqI)
        (eqM := eqM) (eqE := eqE) (lam := lam) (defaultE := defaultE)
        (sampKR := sampKR) (sampKC := sampKC) (sampCCoins := sampCCoins)
        (sampI := sampI) (sampK := sampK) B 1 mo)
      2000 380000 (20 * B0 + 3 * ReductionDsl.bits B + 2710000) where
  startSend_le h ctx p t γv σ r := by
    simp only [SM.Construction.hooksCKAC, SM.Construction.ckaStartSendC, SM.leN,
      ckaOpC, ckaSampC, ckaQueryC,
      exprExcessUB_v0, exprExcessUB_v1, exprExcessUB_v2, exprExcessUB_v3, exprExcessUB_v4,
      exprExcessUB_v5, exprExcessUB_v6, exprExcessUB_v7, exprExcessUB_var,
      exprExcessUB_unit, exprExcessUB_bool, exprExcessUB_nat, exprExcessUB_lt, exprExcessUB_eqN,
      exprExcessUB_not, exprExcessUB_and, exprExcessUB_ite, exprExcessUB_pair, exprExcessUB_fst,
      exprExcessUB_snd, exprExcessUB_none, exprExcessUB_some, exprExcessUB_caseOpt,
      exprExcessUB_letE, exprExcessUB_op, exprExcessUB_tget, exprExcessUB_tset,
      compExcessUB_ret, compExcessUB_bind, compExcessUB_ite, compExcessUB_caseOpt,
      compExcessUB_sample, compExcessUB_query, Nat.reduceAdd, Nat.add_zero, Nat.zero_add]
    omega
  startRecv_le h ctx p t γv σ tn := by
    simp only [SM.Construction.hooksCKAC, SM.Construction.ckaStartRecvC,
      SM.Construction.ckaStartRecvAnsE, ckaOpC,
      exprExcessUB_v0, exprExcessUB_v1, exprExcessUB_v2, exprExcessUB_v3, exprExcessUB_var,
      exprExcessUB_bool, exprExcessUB_nat, exprExcessUB_eqN, exprExcessUB_and, exprExcessUB_ite,
      exprExcessUB_pair, exprExcessUB_fst, exprExcessUB_snd, exprExcessUB_none, exprExcessUB_some,
      exprExcessUB_caseOpt, exprExcessUB_letE, exprExcessUB_op, exprExcessUB_tget,
      compExcessUB_ret, Nat.reduceAdd, Nat.add_zero, Nat.zero_add]
    omega
  fsSend_le h ctx p t ss hdr m pair := by
    simp only [SM.Construction.hooksCKAC, SM.Construction.ckaFsSendC, ckaOpC,
      exprExcessUB_pair, exprExcessUB_some, exprExcessUB_op, compExcessUB_ret]
    omega
  fsRecv_le h ctx p t rs hdr e rec_ := by
    simp only [SM.Construction.hooksCKAC, SM.Construction.ckaFsRecvC, ckaOpC,
      exprExcessUB_pair, exprExcessUB_some, exprExcessUB_op, compExcessUB_ret]
    omega
  commit_le h ctx p old new := by
    simp only [SM.Construction.hooksCKAC, SM.Construction.ckaCommitC, SM.isSomeE, SM.leN,
      SM.Engine.vpSetΓ, SM.Engine.vpMk, SM.Engine.vpId, SM.Engine.vpRoot, SM.Engine.vpVS,
      SM.Engine.vpVR, SM.Engine.vpΓ, SM.Engine.vpTcur, SM.Engine.vpTcurNat, ckaQueryC,
      exprExcessUB_v0, exprExcessUB_v1, exprExcessUB_v2, exprExcessUB_v3, exprExcessUB_v4,
      exprExcessUB_var, exprExcessUB_bool, exprExcessUB_nat, exprExcessUB_lt, exprExcessUB_eqN,
      exprExcessUB_not, exprExcessUB_and, exprExcessUB_ite, exprExcessUB_pair, exprExcessUB_fst,
      exprExcessUB_snd, exprExcessUB_none, exprExcessUB_some,
      exprExcessUB_caseOpt, exprExcessUB_letE, compExcessUB_ret, compExcessUB_bind,
      compExcessUB_ite, compExcessUB_caseOpt, compExcessUB_query,
      Nat.reduceAdd, Nat.add_zero, Nat.zero_add]
    omega
  reveal_le h ctx p vp := by
    simp only [SM.Construction.hooksCKAC, SM.Construction.ckaRevealC, SM.Engine.realPartyE,
      SM.Engine.vpMk, SM.Engine.vpId, SM.Engine.vpRoot, SM.Engine.vpVS, SM.Engine.vpVR,
      SM.Engine.vpΓ, SM.Engine.vpTcur, SM.Engine.vpTcurNat, ckaQueryC,
      exprExcessUB_v0, exprExcessUB_v1, exprExcessUB_v2, exprExcessUB_v3, exprExcessUB_var,
      exprExcessUB_pair, exprExcessUB_fst, exprExcessUB_snd, exprExcessUB_none, exprExcessUB_some,
      exprExcessUB_caseOpt, exprExcessUB_letE,
      compExcessUB_ret, compExcessUB_bind, compExcessUB_caseOpt, compExcessUB_query,
      Nat.reduceAdd, Nat.add_zero, Nat.zero_add]
    omega

lemma hooksPRNGC_excessBounded (B0 B : ℕ) (mo : SM.Construction.Mode) :
    HooksExcessBounded B0 ckaSampC prngQueryC
      (SM.Construction.hooksPRNGC (ckaInitA := ckaInitA) (ckaInitB := ckaInitB)
        (ckaSend := ckaSend) (ckaReceive := ckaReceive) (prngInit := prngInit)
        (prngUp := prngUp) (fsInitSender := fsInitSender) (fsInitReceiver := fsInitReceiver)
        (fsSend := fsSend) (fsReceive := fsReceive) (eqT := eqT) (eqI := eqI)
        (eqM := eqM) (eqE := eqE) (lam := lam) (defaultE := defaultE)
        (sampKR := sampKR) (sampKC := sampKC) (sampCCoins := sampCCoins)
        (sampI := sampI) (sampK := sampK) B mo)
      2000 380000 (20 * B0 + 3 * ReductionDsl.bits B + 2710000) where
  startSend_le h ctx p t γv σ r := by
    simp only [SM.Construction.hooksPRNGC, SM.Construction.prngStartSendC,
      SM.Construction.rootPRNGC, SM.Construction.prngProcessCorrC,
      ckaOpC, ckaSampC, prngQueryC,
      exprExcessUB_v0, exprExcessUB_v1, exprExcessUB_v2, exprExcessUB_v3, exprExcessUB_v4,
      exprExcessUB_var, exprExcessUB_unit, exprExcessUB_bool, exprExcessUB_nat, exprExcessUB_lt,
      exprExcessUB_eqN, exprExcessUB_not, exprExcessUB_and, exprExcessUB_ite, exprExcessUB_pair,
      exprExcessUB_fst, exprExcessUB_snd, exprExcessUB_none, exprExcessUB_some,
      exprExcessUB_caseOpt, exprExcessUB_letE, exprExcessUB_op, exprExcessUB_tget,
      exprExcessUB_tset, compExcessUB_ret, compExcessUB_bind, compExcessUB_ite,
      compExcessUB_caseOpt, compExcessUB_sample, compExcessUB_query,
      Nat.reduceAdd, Nat.add_zero, Nat.zero_add]
    omega
  startRecv_le h ctx p t γv σ tn := by
    simp only [SM.Construction.hooksPRNGC, SM.Construction.prngStartRecvC, ckaOpC, prngQueryC,
      exprExcessUB_v0, exprExcessUB_v1, exprExcessUB_v2, exprExcessUB_v3, exprExcessUB_var,
      exprExcessUB_bool, exprExcessUB_nat, exprExcessUB_eqN, exprExcessUB_and, exprExcessUB_ite,
      exprExcessUB_pair, exprExcessUB_fst, exprExcessUB_snd, exprExcessUB_none, exprExcessUB_some,
      exprExcessUB_caseOpt, exprExcessUB_letE, exprExcessUB_op, exprExcessUB_tget,
      compExcessUB_ret, compExcessUB_bind, compExcessUB_ite, compExcessUB_caseOpt,
      compExcessUB_query, Nat.reduceAdd, Nat.add_zero, Nat.zero_add]
    omega
  fsSend_le h ctx p t ss hdr m pair := by
    simp only [SM.Construction.hooksPRNGC, SM.Construction.prngFsSendC, ckaOpC,
      exprExcessUB_pair, exprExcessUB_some, exprExcessUB_op, compExcessUB_ret]
    omega
  fsRecv_le h ctx p t rs hdr e rec_ := by
    simp only [SM.Construction.hooksPRNGC, SM.Construction.prngFsRecvC, ckaOpC,
      exprExcessUB_pair, exprExcessUB_some, exprExcessUB_op, compExcessUB_ret]
    omega
  commit_le h ctx p old new := by
    simp only [SM.Construction.hooksPRNGC, SM.Construction.prngCommitC,
      exprExcessUB_pair, exprExcessUB_some, compExcessUB_ret]
    omega
  reveal_le h ctx p vp := by
    simp only [SM.Construction.hooksPRNGC, SM.Construction.prngRevealC, SM.Engine.realPartyE,
      SM.Engine.vpMk, SM.Engine.vpId, SM.Engine.vpRoot, SM.Engine.vpVS, SM.Engine.vpVR,
      SM.Engine.vpΓ, SM.Engine.vpTcur, SM.Engine.vpTcurNat,
      exprExcessUB_v0, exprExcessUB_v1, exprExcessUB_v2, exprExcessUB_var, exprExcessUB_pair,
      exprExcessUB_fst, exprExcessUB_snd, exprExcessUB_none, exprExcessUB_some,
      exprExcessUB_caseOpt, exprExcessUB_letE,
      compExcessUB_ret, compExcessUB_bind, compExcessUB_caseOpt,
      Nat.add_zero, Nat.zero_add]
    omega

lemma initCKAEStateC_excessUB_le (B0 : ℕ) (mo : SM.Construction.Mode) {Γ'}
    (bE : Expr OO_cka Γ' .bool) :
    compExcessUB (ckaOpC B0) ckaSampC ckaQueryC
      (SM.Construction.initCKAEStateC (ckaInitA := ckaInitA) (ckaInitB := ckaInitB)
        (ckaSend := ckaSend) (ckaReceive := ckaReceive) (prngInit := prngInit)
        (prngUp := prngUp) (fsInitSender := fsInitSender) (fsInitReceiver := fsInitReceiver)
        (fsSend := fsSend) (fsReceive := fsReceive) (eqT := eqT) (eqI := eqI)
        (eqM := eqM) (eqE := eqE) (lam := lam) (defaultE := defaultE)
        (sampKR := sampKR) (sampKC := sampKC) (sampCCoins := sampCCoins)
        (sampI := sampI) (sampK := sampK) mo bE) ≤ exprExcessUB (ckaOpC B0) bE + 1500 := by
  simp only [SM.Construction.initCKAEStateC, SM.Engine.mkPartiesE, SM.Engine.cGsInitE,
    SM.Engine.cGsMk, SM.Engine.esMk, SM.Engine.vpMk, ckaOpC, ckaSampC,
    exprExcessUB_v0, exprExcessUB_v1, exprExcessUB_v2, exprExcessUB_v3, exprExcessUB_var,
    exprExcessUB_unit, exprExcessUB_bool, exprExcessUB_nat, exprExcessUB_none, exprExcessUB_nil,
    exprExcessUB_pair, exprExcessUB_fst, exprExcessUB_snd, exprExcessUB_some, exprExcessUB_letE,
    exprExcessUB_op, exprExcessUB_tconst, exprExcessUB_tget, exprExcessUB_tset,
    compExcessUB_ret, compExcessUB_bind, compExcessUB_ite, compExcessUB_sample,
    Nat.reduceAdd, Nat.add_zero, Nat.zero_add]
  omega

lemma initPRNGEStateC_excessUB_le (B0 : ℕ) (mo : SM.Construction.Mode) {Γ'}
    (bE : Expr OO_cka Γ' .bool) :
    compExcessUB (ckaOpC B0) ckaSampC prngQueryC
      (SM.Construction.initPRNGEStateC (ckaInitA := ckaInitA) (ckaInitB := ckaInitB)
        (ckaSend := ckaSend) (ckaReceive := ckaReceive) (prngInit := prngInit)
        (prngUp := prngUp) (fsInitSender := fsInitSender) (fsInitReceiver := fsInitReceiver)
        (fsSend := fsSend) (fsReceive := fsReceive) (eqT := eqT) (eqI := eqI)
        (eqM := eqM) (eqE := eqE) (lam := lam) (defaultE := defaultE)
        (sampKR := sampKR) (sampKC := sampKC) (sampCCoins := sampCCoins)
        (sampI := sampI) (sampK := sampK) mo bE) ≤ exprExcessUB (ckaOpC B0) bE + 3000 := by
  simp only [SM.Construction.initPRNGEStateC, SM.Construction.rootPRNGC,
    SM.Construction.prngProcessCorrC, SM.Construction.abortedPartiesE,
    SM.Engine.mkPartiesE, SM.Engine.cGsInitE, SM.Engine.cGsMk, SM.Engine.esMk, SM.Engine.vpMk,
    ckaOpC, ckaSampC, prngQueryC,
    exprExcessUB_v0, exprExcessUB_v1, exprExcessUB_v2, exprExcessUB_v3, exprExcessUB_v4,
    exprExcessUB_var,
    exprExcessUB_unit, exprExcessUB_bool, exprExcessUB_nat, exprExcessUB_lt, exprExcessUB_eqN,
    exprExcessUB_not, exprExcessUB_and, exprExcessUB_ite, exprExcessUB_none, exprExcessUB_nil,
    exprExcessUB_pair, exprExcessUB_fst, exprExcessUB_snd, exprExcessUB_some,
    exprExcessUB_caseOpt, exprExcessUB_letE, exprExcessUB_op, exprExcessUB_tconst,
    exprExcessUB_tget, exprExcessUB_tset,
    compExcessUB_ret, compExcessUB_bind, compExcessUB_ite, compExcessUB_caseOpt,
    compExcessUB_sample, compExcessUB_query, Nat.reduceAdd, Nat.add_zero, Nat.zero_add]
  omega

end HooksCKAAndPRNGExcess

section HooksFSCExcess

variable {sampKR : ProbComp KR} {sampKC : ProbComp KC} {sampCCoins : ProbComp CCoins}
  {sampI : ProbComp I} {sampK : ProbComp K}

local notation "hsTy_fs" => SM.Construction.fsHsTy KC Γ CCoins T I KR RSt K SS RS M E
local notation "vpTy_fs" => SM.Construction.fsVpTy KC Γ CCoins T I KR RSt K SS RS M E

private lemma lookupFC_excessUB_le (B0 L : ℕ) {Γ'}
    (hE : Expr OO_cka Γ' hsTy_fs) (ikE : Expr OO_cka Γ' (.base .i)) :
    compExcessUB (ckaOpC B0) ckaSampC fsQueryC
      (SM.Construction.lookupFC (sampKR := sampKR) (sampKC := sampKC)
        (sampCCoins := sampCCoins) (sampI := sampI) (sampK := sampK) L hE ikE) ≤
      exprExcessUB (ckaOpC B0) hE + exprExcessUB (ckaOpC B0) ikE + 10 * L + 250 := by
  simp only [SM.Construction.lookupFC, SM.Construction.tableLookupE,
    SM.Construction.fsHsSetTable, SM.Construction.fsHsMk,
    SM.Construction.fsHsCache, SM.Construction.fsHsTable, SM.Construction.fsHsSessions,
    SM.Construction.fsHsTrans, SM.Construction.fsHsCount, SM.Construction.fsHsSCorr,
    SM.Construction.fsHsExt, ckaOpC, ckaSampC, fsQueryC,
    exprExcessUB_v0, exprExcessUB_v1, exprExcessUB_v2, exprExcessUB_v3, exprExcessUB_v4,
    exprExcessUB_v5, exprExcessUB_v6, exprExcessUB_v7, exprExcessUB_var,
    exprExcessUB_unit, exprExcessUB_bool, exprExcessUB_nat, exprExcessUB_none, exprExcessUB_nil,
    exprExcessUB_add, exprExcessUB_sub, exprExcessUB_mulK, exprExcessUB_divK, exprExcessUB_modK,
    exprExcessUB_lt, exprExcessUB_eqN, exprExcessUB_not, exprExcessUB_and, exprExcessUB_ite,
    exprExcessUB_pair, exprExcessUB_fst, exprExcessUB_snd, exprExcessUB_inl, exprExcessUB_inr,
    exprExcessUB_some, exprExcessUB_caseOpt, exprExcessUB_caseSum, exprExcessUB_letE,
    exprExcessUB_op, exprExcessUB_cons, exprExcessUB_len, exprExcessUB_take, exprExcessUB_appendL,
    exprExcessUB_findB, exprExcessUB_anyB, exprExcessUB_mapB, exprExcessUB_foldrB,
    exprExcessUB_tconst, exprExcessUB_tget, exprExcessUB_tset,
    compExcessUB_ret, compExcessUB_bind, compExcessUB_ite, compExcessUB_caseOpt,
    compExcessUB_caseSum, compExcessUB_sample, compExcessUB_query,
    Nat.reduceAdd, Nat.add_zero, Nat.zero_add, Nat.mul_zero]
  omega

private lemma isExtE_excessUB_le (B0 L j : ℕ) {Γ'}
    (hE : Expr OO_cka Γ' hsTy_fs) (ikE : Expr OO_cka Γ' (.base .i)) :
    exprExcessUB (ckaOpC B0) (SM.Construction.isExtE L j hE ikE) ≤
      exprExcessUB (ckaOpC B0) hE + exprExcessUB (ckaOpC B0) ikE + 20 * L := by
  simp only [SM.Construction.isExtE, SM.Construction.sessionsMemE, SM.Construction.sessionsIdxOfE,
    SM.Construction.sessionsLenE, SM.Construction.sessionsAppendOneE,
    SM.Construction.fsHsSetSessions, SM.Construction.fsHsMk,
    SM.Construction.fsHsCache, SM.Construction.fsHsTable, SM.Construction.fsHsSessions,
    SM.Construction.fsHsTrans, SM.Construction.fsHsCount, SM.Construction.fsHsSCorr,
    SM.Construction.fsHsExt, SM.orE, ckaOpC,
    exprExcessUB_v0, exprExcessUB_v1, exprExcessUB_v2, exprExcessUB_v3, exprExcessUB_v4,
    exprExcessUB_v5, exprExcessUB_v6, exprExcessUB_v7, exprExcessUB_var,
    exprExcessUB_unit, exprExcessUB_bool, exprExcessUB_nat, exprExcessUB_none, exprExcessUB_nil,
    exprExcessUB_add, exprExcessUB_sub, exprExcessUB_mulK, exprExcessUB_divK, exprExcessUB_modK,
    exprExcessUB_lt, exprExcessUB_eqN, exprExcessUB_not, exprExcessUB_and, exprExcessUB_ite,
    exprExcessUB_pair, exprExcessUB_fst, exprExcessUB_snd, exprExcessUB_inl, exprExcessUB_inr,
    exprExcessUB_some, exprExcessUB_caseOpt, exprExcessUB_caseSum, exprExcessUB_letE,
    exprExcessUB_op, exprExcessUB_cons, exprExcessUB_len, exprExcessUB_take, exprExcessUB_appendL,
    exprExcessUB_findB, exprExcessUB_anyB, exprExcessUB_mapB, exprExcessUB_foldrB,
    exprExcessUB_tconst, exprExcessUB_tget, exprExcessUB_tset,
    Nat.reduceAdd, Nat.add_zero, Nat.zero_add, Nat.mul_zero]
  omega

private lemma extOfE_excessUB_le (B0 L j : ℕ) {Γ'}
    (hE : Expr OO_cka Γ' hsTy_fs) (sidE : Expr OO_cka Γ' (.opt (.base .i))) :
    exprExcessUB (ckaOpC B0) (SM.Construction.extOfE L j hE sidE) ≤
      exprExcessUB (ckaOpC B0) hE + exprExcessUB (ckaOpC B0) sidE + 20 * L := by
  have hie := isExtE_excessUB_le (ckaInitA := ckaInitA) (ckaInitB := ckaInitB)
    (ckaSend := ckaSend) (ckaReceive := ckaReceive) (prngInit := prngInit) (prngUp := prngUp)
    (fsInitSender := fsInitSender) (fsInitReceiver := fsInitReceiver) (fsSend := fsSend)
    (fsReceive := fsReceive) (eqT := eqT) (eqI := eqI) (eqM := eqM) (eqE := eqE)
    (lam := lam) (defaultE := defaultE) B0 L j
    (Γ' := .base .i :: .prod hsTy_fs (.opt (.base .i)) :: Γ') (.fst .v1) .v0
  simp only [exprExcessUB_v0, exprExcessUB_v1, exprExcessUB_var, exprExcessUB_fst, Nat.add_zero] at hie
  simp only [SM.Construction.extOfE, exprExcessUB_v0, exprExcessUB_var, exprExcessUB_bool,
    exprExcessUB_pair, exprExcessUB_fst, exprExcessUB_snd, exprExcessUB_caseOpt, exprExcessUB_letE,
    Nat.add_zero, Nat.zero_add]
  omega

private lemma rootFSC_excessUB_le (B0 L : ℕ) (mo : SM.Construction.Mode) {Γ'}
    (hE : Expr OO_cka Γ' hsTy_fs) (tE : Expr OO_cka Γ' .nat)
    (ikE : Expr OO_cka Γ' (.base .i)) (σE : Expr OO_cka Γ' (.base .sig)) :
    compExcessUB (ckaOpC B0) ckaSampC fsQueryC
      (SM.Construction.rootFSC (sampKR := sampKR) (sampKC := sampKC)
        (sampCCoins := sampCCoins) (sampI := sampI) (sampK := sampK) L mo hE tE ikE σE) ≤
      exprExcessUB (ckaOpC B0) hE + exprExcessUB (ckaOpC B0) tE + exprExcessUB (ckaOpC B0) ikE +
        exprExcessUB (ckaOpC B0) σE + 10 * L + 1200 := by
  have hlk := lookupFC_excessUB_le (ckaInitA := ckaInitA) (ckaInitB := ckaInitB)
    (ckaSend := ckaSend) (ckaReceive := ckaReceive) (prngInit := prngInit) (prngUp := prngUp)
    (fsInitSender := fsInitSender) (fsInitReceiver := fsInitReceiver) (fsSend := fsSend)
    (fsReceive := fsReceive) (eqT := eqT) (eqI := eqI) (eqM := eqM) (eqE := eqE)
    (lam := lam) (defaultE := defaultE)
    (sampKR := sampKR) (sampKC := sampKC) (sampCCoins := sampCCoins)
    (sampI := sampI) (sampK := sampK) B0 L
    (Γ' := .prod hsTy_fs (.prod .nat (.prod (.base .i) (.base .sig))) :: Γ')
    (.fst .v0) (.fst (.snd (.snd .v0)))
  simp only [exprExcessUB_v0, exprExcessUB_var, exprExcessUB_fst, exprExcessUB_snd, Nat.add_zero] at hlk
  simp only [SM.Construction.rootFSC, ckaOpC, ckaSampC, fsQueryC,
    exprExcessUB_v0, exprExcessUB_v1, exprExcessUB_v2, exprExcessUB_v3, exprExcessUB_v4,
    exprExcessUB_v5, exprExcessUB_v6, exprExcessUB_v7, exprExcessUB_var,
    exprExcessUB_unit, exprExcessUB_bool, exprExcessUB_nat, exprExcessUB_none, exprExcessUB_nil,
    exprExcessUB_add, exprExcessUB_sub, exprExcessUB_mulK, exprExcessUB_divK, exprExcessUB_modK,
    exprExcessUB_lt, exprExcessUB_eqN, exprExcessUB_not, exprExcessUB_and, exprExcessUB_ite,
    exprExcessUB_pair, exprExcessUB_fst, exprExcessUB_snd, exprExcessUB_inl, exprExcessUB_inr,
    exprExcessUB_some, exprExcessUB_caseOpt, exprExcessUB_caseSum, exprExcessUB_letE,
    exprExcessUB_op, exprExcessUB_cons, exprExcessUB_len, exprExcessUB_take, exprExcessUB_appendL,
    exprExcessUB_findB, exprExcessUB_anyB, exprExcessUB_mapB, exprExcessUB_foldrB,
    exprExcessUB_tconst, exprExcessUB_tget, exprExcessUB_tset,
    compExcessUB_ret, compExcessUB_bind, compExcessUB_ite, compExcessUB_caseOpt,
    compExcessUB_caseSum, compExcessUB_sample, compExcessUB_query,
    Nat.reduceAdd, Nat.add_zero, Nat.zero_add]
  omega

private lemma fsTransFindE_excessUB_le (B0 L : ℕ) {Γ'}
    (trE : Expr OO_cka Γ'
      (.list (SM.Construction.fsTransEntryTy KC Γ CCoins T I KR RSt K SS RS M E)))
    (hcE : Expr OO_cka Γ' (CKA.ckaHdrCtTy KC Γ CCoins T I KR RSt K SS RS M E)) :
    exprExcessUB (ckaOpC B0) (SM.Construction.fsTransFindE L trE hcE) ≤
      exprExcessUB (ckaOpC B0) trE + exprExcessUB (ckaOpC B0) hcE + 150 * L := by
  simp only [SM.Construction.fsTransFindE, SM.Engine.hdrCtEqE, SM.Engine.optTEqE, ckaOpC,
    exprExcessUB_v0, exprExcessUB_v1, exprExcessUB_v2, exprExcessUB_v3, exprExcessUB_v4,
    exprExcessUB_v5, exprExcessUB_v6, exprExcessUB_v7, exprExcessUB_var,
    exprExcessUB_unit, exprExcessUB_bool, exprExcessUB_nat, exprExcessUB_none, exprExcessUB_nil,
    exprExcessUB_add, exprExcessUB_sub, exprExcessUB_mulK, exprExcessUB_divK, exprExcessUB_modK,
    exprExcessUB_lt, exprExcessUB_eqN, exprExcessUB_not, exprExcessUB_and, exprExcessUB_ite,
    exprExcessUB_pair, exprExcessUB_fst, exprExcessUB_snd, exprExcessUB_inl, exprExcessUB_inr,
    exprExcessUB_some, exprExcessUB_caseOpt, exprExcessUB_caseSum, exprExcessUB_letE,
    exprExcessUB_op, exprExcessUB_cons, exprExcessUB_len, exprExcessUB_take, exprExcessUB_appendL,
    exprExcessUB_findB, exprExcessUB_anyB, exprExcessUB_mapB, exprExcessUB_foldrB,
    exprExcessUB_tconst, exprExcessUB_tget, exprExcessUB_tset,
    Nat.reduceAdd, Nat.add_zero, Nat.zero_add]
  omega

lemma hooksFSC_excessBounded (B0 L B : ℕ) (mo : SM.Construction.Mode) (j : ℕ) :
    HooksExcessBounded B0 ckaSampC fsQueryC
      (SM.Construction.hooksFSC (ckaInitA := ckaInitA) (ckaInitB := ckaInitB)
        (ckaSend := ckaSend) (ckaReceive := ckaReceive) (prngInit := prngInit)
        (prngUp := prngUp) (fsInitSender := fsInitSender) (fsInitReceiver := fsInitReceiver)
        (fsSend := fsSend) (fsReceive := fsReceive) (eqT := eqT) (eqI := eqI)
        (eqM := eqM) (eqE := eqE) (lam := lam) (defaultE := defaultE)
        (sampKR := sampKR) (sampKC := sampKC) (sampCCoins := sampCCoins)
        (sampI := sampI) (sampK := sampK) L B 1 mo j)
      (300 * L + 250000) 2000000 (500 * L + 40 * B0 + 6 * ReductionDsl.bits B + 5700000) where
  startSend_le {Γ'} hE ctxE pE tE γE σE rE := by
    let Γ0 : List (Ty S_cka) :=
      .base .ccoins :: .prod hsTy_fs (.prod .nat (.prod (.base .γ)
        (.prod (.base .sig) (.opt (.base .ccoins))))) :: Γ'
    let Γ1 : List (Ty S_cka) :=
      .prod (.prod (.base .sig) (.prod (.base .k) (.opt (.base .i)))) hsTy_fs :: Γ0
    have hrt := rootFSC_excessUB_le (ckaInitA := ckaInitA) (ckaInitB := ckaInitB)
      (ckaSend := ckaSend) (ckaReceive := ckaReceive) (prngInit := prngInit) (prngUp := prngUp)
      (fsInitSender := fsInitSender) (fsInitReceiver := fsInitReceiver) (fsSend := fsSend)
      (fsReceive := fsReceive) (eqT := eqT) (eqI := eqI) (eqM := eqM) (eqE := eqE)
      (lam := lam) (defaultE := defaultE)
      (sampKR := sampKR) (sampKC := sampKC) (sampCCoins := sampCCoins)
      (sampI := sampI) (sampK := sampK) B0 L mo (Γ' := Γ0)
      (.fst .v1) (.fst (.snd .v1))
      (.snd (.snd (Expr.op (O := OO_cka) CKA.CKAOp.ckaSend (.pair (.fst (.snd (.snd .v1))) .v0))))
      (.fst (.snd (.snd (.snd .v1))))
    have hext := extOfE_excessUB_le (ckaInitA := ckaInitA) (ckaInitB := ckaInitB)
      (ckaSend := ckaSend) (ckaReceive := ckaReceive) (prngInit := prngInit) (prngUp := prngUp)
      (fsInitSender := fsInitSender) (fsInitReceiver := fsInitReceiver) (fsSend := fsSend)
      (fsReceive := fsReceive) (eqT := eqT) (eqI := eqI) (eqM := eqM) (eqE := eqE)
      (lam := lam) (defaultE := defaultE) B0 L j (Γ' := Γ1) (.snd .v0) (.snd (.snd (.fst .v0)))
    simp only [ckaOpC, exprExcessUB_v0, exprExcessUB_v1, exprExcessUB_var, exprExcessUB_pair,
      exprExcessUB_fst, exprExcessUB_snd, exprExcessUB_op, Nat.add_zero, Nat.zero_add] at hrt hext
    simp only [SM.Construction.hooksFSC, SM.Construction.fsStartSendC,
      SM.Construction.fsHsSetCache, SM.Construction.fsHsMk,
      SM.Construction.fsHsCache, SM.Construction.fsHsTable, SM.Construction.fsHsSessions,
      SM.Construction.fsHsTrans, SM.Construction.fsHsCount, SM.Construction.fsHsSCorr,
      SM.Construction.fsHsExt, ckaOpC, ckaSampC, fsQueryC,
      exprExcessUB_v0, exprExcessUB_v1, exprExcessUB_v2, exprExcessUB_v3, exprExcessUB_v4,
      exprExcessUB_v5, exprExcessUB_v6, exprExcessUB_v7, exprExcessUB_var,
      exprExcessUB_unit, exprExcessUB_bool, exprExcessUB_nat, exprExcessUB_none, exprExcessUB_nil,
      exprExcessUB_add, exprExcessUB_sub, exprExcessUB_mulK, exprExcessUB_divK, exprExcessUB_modK,
      exprExcessUB_lt, exprExcessUB_eqN, exprExcessUB_not, exprExcessUB_and, exprExcessUB_ite,
      exprExcessUB_pair, exprExcessUB_fst, exprExcessUB_snd, exprExcessUB_inl, exprExcessUB_inr,
      exprExcessUB_some, exprExcessUB_caseOpt, exprExcessUB_caseSum, exprExcessUB_letE,
      exprExcessUB_op, exprExcessUB_cons, exprExcessUB_len, exprExcessUB_take, exprExcessUB_appendL,
      exprExcessUB_findB, exprExcessUB_anyB, exprExcessUB_mapB, exprExcessUB_foldrB,
      exprExcessUB_tconst, exprExcessUB_tget, exprExcessUB_tset,
      compExcessUB_ret, compExcessUB_bind, compExcessUB_ite, compExcessUB_caseOpt,
      compExcessUB_caseSum, compExcessUB_sample, compExcessUB_query,
      Nat.reduceAdd, Nat.add_zero, Nat.zero_add]
    omega
  startRecv_le {Γ'} hE ctxE pE tE γE σE tnE := by
    let Γ0 : List (Ty S_cka) :=
      .prod hsTy_fs (.prod .nat (.prod (.base .γ) (.prod (.base .sig) (.base .t)))) :: Γ'
    let Γ1 : List (Ty S_cka) := .prod (.base .k) hsTy_fs :: Γ0
    have hlk := lookupFC_excessUB_le (ckaInitA := ckaInitA) (ckaInitB := ckaInitB)
      (ckaSend := ckaSend) (ckaReceive := ckaReceive) (prngInit := prngInit) (prngUp := prngUp)
      (fsInitSender := fsInitSender) (fsInitReceiver := fsInitReceiver) (fsSend := fsSend)
      (fsReceive := fsReceive) (eqT := eqT) (eqI := eqI) (eqM := eqM) (eqE := eqE)
      (lam := lam) (defaultE := defaultE)
      (sampKR := sampKR) (sampKC := sampKC) (sampCCoins := sampCCoins)
      (sampI := sampI) (sampK := sampK) B0 L (Γ' := Γ0)
      (.fst .v0) (.snd (Expr.op (O := OO_cka) CKA.CKAOp.ckaReceive
        (.pair (.fst (.snd (.snd .v0))) (.snd (.snd (.snd (.snd .v0)))))))
    have hie := isExtE_excessUB_le (ckaInitA := ckaInitA) (ckaInitB := ckaInitB)
      (ckaSend := ckaSend) (ckaReceive := ckaReceive) (prngInit := prngInit) (prngUp := prngUp)
      (fsInitSender := fsInitSender) (fsInitReceiver := fsInitReceiver) (fsSend := fsSend)
      (fsReceive := fsReceive) (eqT := eqT) (eqI := eqI) (eqM := eqM) (eqE := eqE)
      (lam := lam) (defaultE := defaultE) B0 L j (Γ' := Γ1) (.snd .v0)
      (.snd (Expr.op (O := OO_cka) CKA.CKAOp.ckaReceive
        (.pair (.fst (.snd (.snd .v1))) (.snd (.snd (.snd (.snd .v1)))))))
    simp only [ckaOpC, exprExcessUB_v0, exprExcessUB_v1, exprExcessUB_var, exprExcessUB_pair,
      exprExcessUB_fst, exprExcessUB_snd, exprExcessUB_op, Nat.add_zero, Nat.zero_add] at hlk hie
    simp only [SM.Construction.hooksFSC, SM.Construction.fsStartRecvC, SM.Construction.fsHsCache,
      ckaOpC, ckaSampC, fsQueryC,
      exprExcessUB_v0, exprExcessUB_v1, exprExcessUB_v2, exprExcessUB_v3, exprExcessUB_v4,
      exprExcessUB_v5, exprExcessUB_v6, exprExcessUB_v7, exprExcessUB_var,
      exprExcessUB_unit, exprExcessUB_bool, exprExcessUB_nat, exprExcessUB_none, exprExcessUB_nil,
      exprExcessUB_add, exprExcessUB_sub, exprExcessUB_mulK, exprExcessUB_divK, exprExcessUB_modK,
      exprExcessUB_lt, exprExcessUB_eqN, exprExcessUB_not, exprExcessUB_and, exprExcessUB_ite,
      exprExcessUB_pair, exprExcessUB_fst, exprExcessUB_snd, exprExcessUB_inl, exprExcessUB_inr,
      exprExcessUB_some, exprExcessUB_caseOpt, exprExcessUB_caseSum, exprExcessUB_letE,
      exprExcessUB_op, exprExcessUB_cons, exprExcessUB_len, exprExcessUB_take, exprExcessUB_appendL,
      exprExcessUB_findB, exprExcessUB_anyB, exprExcessUB_mapB, exprExcessUB_foldrB,
      exprExcessUB_tconst, exprExcessUB_tget, exprExcessUB_tset,
      compExcessUB_ret, compExcessUB_bind, compExcessUB_ite, compExcessUB_caseOpt,
      compExcessUB_caseSum, compExcessUB_sample, compExcessUB_query,
      Nat.reduceAdd, Nat.add_zero, Nat.zero_add]
    omega
  fsSend_le hE ctxE pE tE ssvE hdrE mE pairE := by
    simp only [SM.Construction.hooksFSC, SM.Construction.fsFsSendC, SM.Engine.cSafeChE,
      SM.Construction.fsHsSetSCorr, SM.Construction.fsHsSetCountTrans, SM.Construction.fsHsSetExt,
      SM.Construction.fsHsMk, SM.Construction.fsHsCache, SM.Construction.fsHsTable,
      SM.Construction.fsHsSessions, SM.Construction.fsHsTrans, SM.Construction.fsHsCount,
      SM.Construction.fsHsSCorr, SM.Construction.fsHsExt, SM.healedByE, SM.leN, SM.pGet,
      SM.Engine.cGsTL, SM.Engine.cGsEpoch, ckaOpC, ckaSampC, fsQueryC,
      exprExcessUB_v0, exprExcessUB_v1, exprExcessUB_v2, exprExcessUB_v3, exprExcessUB_v4,
      exprExcessUB_v5, exprExcessUB_v6, exprExcessUB_v7, exprExcessUB_var,
      exprExcessUB_unit, exprExcessUB_bool, exprExcessUB_nat, exprExcessUB_none, exprExcessUB_nil,
      exprExcessUB_add, exprExcessUB_sub, exprExcessUB_mulK, exprExcessUB_divK, exprExcessUB_modK,
      exprExcessUB_lt, exprExcessUB_eqN, exprExcessUB_not, exprExcessUB_and, exprExcessUB_ite,
      exprExcessUB_pair, exprExcessUB_fst, exprExcessUB_snd, exprExcessUB_inl, exprExcessUB_inr,
      exprExcessUB_some, exprExcessUB_caseOpt, exprExcessUB_caseSum, exprExcessUB_letE,
      exprExcessUB_op, exprExcessUB_cons, exprExcessUB_len, exprExcessUB_take, exprExcessUB_appendL,
      exprExcessUB_findB, exprExcessUB_anyB, exprExcessUB_mapB, exprExcessUB_foldrB,
      exprExcessUB_tconst, exprExcessUB_tget, exprExcessUB_tset,
      compExcessUB_ret, compExcessUB_bind, compExcessUB_ite, compExcessUB_caseOpt,
      compExcessUB_caseSum, compExcessUB_sample, compExcessUB_query,
      Nat.reduceAdd, Nat.add_zero, Nat.zero_add]
    omega
  fsRecv_le {Γ'} hE ctxE pE tE rsvE hdrE eE recE := by
    let hdrT := CKA.ckaHdrTy KC Γ CCoins T I KR RSt K SS RS M E
    let Γ0 : List (Ty S_cka) :=
      .prod hsTy_fs (.prod (.opt (.base .rs)) (.prod hdrT
        (.prod (.base .ct) (.opt SM.Engine.cRecTy)))) :: Γ'
    let rrT : Ty S_cka := .sum .unit (.prod .nat (.opt (.base .msg)))
    let Γ1 : List (Ty S_cka) := .prod .nat (.opt (.base .msg)) :: rrT :: .opt rrT :: Γ0
    have htf0 := fsTransFindE_excessUB_le (ckaInitA := ckaInitA) (ckaInitB := ckaInitB)
      (ckaSend := ckaSend) (ckaReceive := ckaReceive) (prngInit := prngInit) (prngUp := prngUp)
      (fsInitSender := fsInitSender) (fsInitReceiver := fsInitReceiver) (fsSend := fsSend)
      (fsReceive := fsReceive) (eqT := eqT) (eqI := eqI) (eqM := eqM) (eqE := eqE)
      (lam := lam) (defaultE := defaultE) B0 L (Γ' := Γ0)
      (SM.Construction.fsHsTrans (.fst .v0))
      (.pair (.fst (.snd (.snd .v0))) (.fst (.snd (.snd (.snd .v0)))))
    have htf3 := fsTransFindE_excessUB_le (ckaInitA := ckaInitA) (ckaInitB := ckaInitB)
      (ckaSend := ckaSend) (ckaReceive := ckaReceive) (prngInit := prngInit) (prngUp := prngUp)
      (fsInitSender := fsInitSender) (fsInitReceiver := fsInitReceiver) (fsSend := fsSend)
      (fsReceive := fsReceive) (eqT := eqT) (eqI := eqI) (eqM := eqM) (eqE := eqE)
      (lam := lam) (defaultE := defaultE) B0 L (Γ' := Γ1)
      (SM.Construction.fsHsTrans (.fst .v3))
      (.pair (.fst (.snd (.snd .v3))) (.fst (.snd (.snd (.snd .v3)))))
    simp only [SM.Construction.fsHsTrans, exprExcessUB_v0, exprExcessUB_v3, exprExcessUB_var,
      exprExcessUB_pair, exprExcessUB_fst, exprExcessUB_snd, Nat.add_zero] at htf0 htf3
    simp only [SM.Construction.hooksFSC, SM.Construction.fsFsRecvC, SM.Construction.fsTransFilterE,
      SM.Construction.fsHsSetTrans, SM.Construction.fsHsSetExt, SM.Construction.fsHsMk,
      SM.Construction.fsHsCache, SM.Construction.fsHsTable, SM.Construction.fsHsSessions,
      SM.Construction.fsHsTrans, SM.Construction.fsHsCount, SM.Construction.fsHsSCorr,
      SM.Construction.fsHsExt, SM.Engine.cRecMsg, ckaOpC, ckaSampC, fsQueryC,
      exprExcessUB_v0, exprExcessUB_v1, exprExcessUB_v2, exprExcessUB_v3, exprExcessUB_v4,
      exprExcessUB_v5, exprExcessUB_v6, exprExcessUB_v7, exprExcessUB_var,
      exprExcessUB_unit, exprExcessUB_bool, exprExcessUB_nat, exprExcessUB_none, exprExcessUB_nil,
      exprExcessUB_add, exprExcessUB_sub, exprExcessUB_mulK, exprExcessUB_divK, exprExcessUB_modK,
      exprExcessUB_lt, exprExcessUB_eqN, exprExcessUB_not, exprExcessUB_and, exprExcessUB_ite,
      exprExcessUB_pair, exprExcessUB_fst, exprExcessUB_snd, exprExcessUB_inl, exprExcessUB_inr,
      exprExcessUB_some, exprExcessUB_caseOpt, exprExcessUB_caseSum, exprExcessUB_letE,
      exprExcessUB_op, exprExcessUB_cons, exprExcessUB_len, exprExcessUB_take, exprExcessUB_appendL,
      exprExcessUB_findB, exprExcessUB_anyB, exprExcessUB_mapB, exprExcessUB_foldrB,
      exprExcessUB_tconst, exprExcessUB_tget, exprExcessUB_tset,
      compExcessUB_ret, compExcessUB_bind, compExcessUB_ite, compExcessUB_caseOpt,
      compExcessUB_caseSum, compExcessUB_sample, compExcessUB_query,
      Nat.reduceAdd, Nat.add_zero, Nat.zero_add, Nat.mul_zero]
    omega
  commit_le hE ctxE pE old new := by
    simp only [SM.Construction.hooksFSC, SM.Construction.fsCommitC,
      exprExcessUB_pair, exprExcessUB_some, compExcessUB_ret]
    omega
  reveal_le {Γ'} hE ctxE pE vpE := by
    let Γ0 : List (Ty S_cka) := .prod hsTy_fs vpTy_fs :: Γ'
    let Γ2 : List (Ty S_cka) := .opt (.base .ss) :: .prod (.opt (.opt (.base .ss))) hsTy_fs :: Γ0
    let Γ4 : List (Ty S_cka) := .opt (.base .rs) :: .prod (.opt (.opt (.base .rs))) hsTy_fs :: Γ2
    let Γ5 : List (Ty S_cka) := .list .nat :: Γ4
    have huv := unliftVRE_excessUB (ckaInitA := ckaInitA) (ckaInitB := ckaInitB)
      (ckaSend := ckaSend) (ckaReceive := ckaReceive) (prngInit := prngInit) (prngUp := prngUp)
      (fsInitSender := fsInitSender) (fsInitReceiver := fsInitReceiver) (fsSend := fsSend)
      (fsReceive := fsReceive) (eqT := eqT) (eqI := eqI) (eqM := eqM) (eqE := eqE)
      (lam := lam) (defaultE := defaultE) (ckaOpC B0) L (Γ' := Γ5)
      (SM.Engine.vpVR (.snd .v5)) .v1 .v0
    simp only [SM.Engine.vpVR, exprExcessUB_v0, exprExcessUB_v1, exprExcessUB_v5,
      exprExcessUB_var, exprExcessUB_fst, exprExcessUB_snd, Nat.add_zero] at huv
    simp only [SM.Construction.hooksFSC, SM.Construction.fsRevealC,
      SM.Construction.fsHsSetSCorr, SM.Construction.fsHsSetExt, SM.Construction.fsHsMk,
      SM.Construction.fsHsCache, SM.Construction.fsHsTable, SM.Construction.fsHsSessions,
      SM.Construction.fsHsTrans, SM.Construction.fsHsCount, SM.Construction.fsHsSCorr,
      SM.Construction.fsHsExt, SM.Engine.realPartyE, SM.Engine.vpMk, SM.Engine.vpId,
      SM.Engine.vpRoot, SM.Engine.vpVS, SM.Engine.vpVR, SM.Engine.vpΓ, SM.Engine.vpTcur,
      SM.Engine.vpTcurNat, ckaOpC, ckaSampC, fsQueryC, rangeListC_excessUB,
      exprExcessUB_v0, exprExcessUB_v1, exprExcessUB_v2, exprExcessUB_v3, exprExcessUB_v4,
      exprExcessUB_v5, exprExcessUB_v6, exprExcessUB_v7, exprExcessUB_var,
      exprExcessUB_unit, exprExcessUB_bool, exprExcessUB_nat, exprExcessUB_none, exprExcessUB_nil,
      exprExcessUB_add, exprExcessUB_sub, exprExcessUB_mulK, exprExcessUB_divK, exprExcessUB_modK,
      exprExcessUB_lt, exprExcessUB_eqN, exprExcessUB_not, exprExcessUB_and, exprExcessUB_ite,
      exprExcessUB_pair, exprExcessUB_fst, exprExcessUB_snd, exprExcessUB_inl, exprExcessUB_inr,
      exprExcessUB_some, exprExcessUB_caseOpt, exprExcessUB_caseSum, exprExcessUB_letE,
      exprExcessUB_op, exprExcessUB_cons, exprExcessUB_len, exprExcessUB_take, exprExcessUB_appendL,
      exprExcessUB_findB, exprExcessUB_anyB, exprExcessUB_mapB, exprExcessUB_foldrB,
      exprExcessUB_tconst, exprExcessUB_tget, exprExcessUB_tset,
      compExcessUB_ret, compExcessUB_bind, compExcessUB_ite, compExcessUB_caseOpt,
      compExcessUB_caseSum, compExcessUB_sample, compExcessUB_query,
      Nat.reduceAdd, Nat.add_zero, Nat.zero_add]
    omega

lemma initFSEStateC_excessUB_le (B0 L : ℕ) (mo : SM.Construction.Mode) (j : ℕ) {Γ'}
    (bE : Expr OO_cka Γ' .bool) :
    compExcessUB (ckaOpC B0) ckaSampC fsQueryC
      (SM.Construction.initFSEStateC (ckaInitA := ckaInitA) (ckaInitB := ckaInitB)
        (ckaSend := ckaSend) (ckaReceive := ckaReceive) (prngInit := prngInit)
        (prngUp := prngUp) (fsInitSender := fsInitSender) (fsInitReceiver := fsInitReceiver)
        (fsSend := fsSend) (fsReceive := fsReceive) (eqT := eqT) (eqI := eqI)
        (eqM := eqM) (eqE := eqE) (lam := lam) (defaultE := defaultE)
        (sampKR := sampKR) (sampKC := sampKC) (sampCCoins := sampCCoins)
        (sampI := sampI) (sampK := sampK) L mo j bE) ≤
      exprExcessUB (ckaOpC B0) bE + 200 * L + 5000 := by
  let Γ0 : List (Ty S_cka) := .base .kc :: .base .kr :: .bool :: Γ'
  let Γ1 : List (Ty S_cka) :=
    .prod (.prod (.base .sig) (.prod (.base .k) (.opt (.base .i)))) hsTy_fs :: Γ0
  have hrt := rootFSC_excessUB_le (ckaInitA := ckaInitA) (ckaInitB := ckaInitB)
    (ckaSend := ckaSend) (ckaReceive := ckaReceive) (prngInit := prngInit) (prngUp := prngUp)
    (fsInitSender := fsInitSender) (fsInitReceiver := fsInitReceiver) (fsSend := fsSend)
    (fsReceive := fsReceive) (eqT := eqT) (eqI := eqI) (eqM := eqM) (eqE := eqE)
    (lam := lam) (defaultE := defaultE)
    (sampKR := sampKR) (sampKC := sampKC) (sampCCoins := sampCCoins)
    (sampI := sampI) (sampK := sampK) B0 L mo (Γ' := Γ0)
    SM.Construction.fsHsEmptyE (.nat 0)
    (Expr.op (O := OO_cka) CKA.CKAOp.lamI .unit)
    (Expr.op (O := OO_cka) CKA.CKAOp.prngInit .v1)
  have hext := extOfE_excessUB_le (ckaInitA := ckaInitA) (ckaInitB := ckaInitB)
    (ckaSend := ckaSend) (ckaReceive := ckaReceive) (prngInit := prngInit) (prngUp := prngUp)
    (fsInitSender := fsInitSender) (fsInitReceiver := fsInitReceiver) (fsSend := fsSend)
    (fsReceive := fsReceive) (eqT := eqT) (eqI := eqI) (eqM := eqM) (eqE := eqE)
    (lam := lam) (defaultE := defaultE) B0 L j (Γ' := Γ1) (.snd .v0) (.snd (.snd (.fst .v0)))
  simp only [SM.Construction.fsHsEmptyE, SM.Construction.fsHsMk, ckaOpC,
    exprExcessUB_v0, exprExcessUB_v1, exprExcessUB_var, exprExcessUB_unit, exprExcessUB_bool,
    exprExcessUB_nat, exprExcessUB_none, exprExcessUB_nil, exprExcessUB_pair, exprExcessUB_fst,
    exprExcessUB_snd, exprExcessUB_op, exprExcessUB_tconst, Nat.add_zero, Nat.zero_add] at hrt hext
  simp only [SM.Construction.initFSEStateC, SM.Engine.mkPartiesE, SM.Engine.cGsInitE,
    SM.Engine.cGsMk, SM.Engine.esMk, SM.Engine.vpMk,
    SM.Construction.fsHsEmptyE, SM.Construction.fsHsMk, ckaOpC, ckaSampC, fsQueryC,
    exprExcessUB_v0, exprExcessUB_v1, exprExcessUB_v2, exprExcessUB_v3, exprExcessUB_v4,
    exprExcessUB_v5, exprExcessUB_v6, exprExcessUB_v7, exprExcessUB_var,
    exprExcessUB_unit, exprExcessUB_bool, exprExcessUB_nat, exprExcessUB_none, exprExcessUB_nil,
    exprExcessUB_add, exprExcessUB_sub, exprExcessUB_mulK, exprExcessUB_divK, exprExcessUB_modK,
    exprExcessUB_lt, exprExcessUB_eqN, exprExcessUB_not, exprExcessUB_and, exprExcessUB_ite,
    exprExcessUB_pair, exprExcessUB_fst, exprExcessUB_snd, exprExcessUB_inl, exprExcessUB_inr,
    exprExcessUB_some, exprExcessUB_caseOpt, exprExcessUB_caseSum, exprExcessUB_letE,
    exprExcessUB_op, exprExcessUB_cons, exprExcessUB_len, exprExcessUB_take, exprExcessUB_appendL,
    exprExcessUB_findB, exprExcessUB_anyB, exprExcessUB_mapB, exprExcessUB_foldrB,
    exprExcessUB_tconst, exprExcessUB_tget, exprExcessUB_tset,
    compExcessUB_ret, compExcessUB_bind, compExcessUB_ite, compExcessUB_caseOpt,
    compExcessUB_caseSum, compExcessUB_sample, compExcessUB_query,
    Nat.reduceAdd, Nat.add_zero, Nat.zero_add]
  omega

end HooksFSCExcess

end EngineExcessHelpers

end Computational.Proofs.ReductionDsl.Fig8ExcessCosts
