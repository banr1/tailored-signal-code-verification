/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Computational.Proofs.Game.PromotedCostedReds.SimFig8State
public import Computational.Proofs.Game.PromotedCostedReds.AtomicSessionBridge
import Computational.Proofs.E2E.Dsl.SpqrSimSend
import Computational.Proofs.E2E.Dsl.SpqrSimRecv

/-!
# `SPQR`, `Fig8Atomic`, and Budget `DescBits` Bounds for `simFig8`

Proves syntactic description-bit bounds for `bits` helpers, variable renamings, lifted SPQR V1
step simulators (`spqrSendAtomicC`, `spqrRecvAtomicC`), and `Fig8Atomic` primitives.
-/

@[expose] public section

set_option autoImplicit false

open OracleSpec OracleComp
open ReductionDsl (Sig Ty Var Env Ops Iface Expr Comp bits bits_mono lt_two_pow_bits
  atomicSig atomicFig8Ops atomicSessionOps
  AtomicPureOp AtomicSymOp AtomicGroupOp
  B U32 BV128 BV256 BV512 PK IdKey PlainT PtT
  fig8HdrT lpubT lctT wireSaltCtT signalParsedT fsSendStT fsRecvStT fig8CtT)
open CryptoGames.CKA (DHFun)
open CryptoGames.Ratchet.LibsignalInst (dummyKey)
open CryptoGames.LibsignalSession (Crypto IdentityKey PublicKey maxForwardJumps)
open CryptoVerification.LibsignalSession (ratchetCostBudget)
open CryptoVerification.LibsignalSpqrV1 (MlKem)
open CryptoVerification.E2E (Bytes toU8 vecU8)
open Computational.Proofs.Game.PromotedCostedReds.AtomicSessionBridge (zeroPqxdhPrims
  sessPureOp sessSymOp sessCurveOp sessSpqrKemOp
  liftSort liftTy liftVar liftPureOpExpr liftCurveOpExpr liftCryptoOpExpr liftOpExpr
  liftExpr emptyE2EIface liftCompEmpty liftRen renExpr renComp wk1Ren wk1Comp
  spqrSendAtomicC spqrRecvAtomicC)
open Computational.Proofs.Game.PromotedCostedReds.KemFailRedLoopAndCost
  (atomicSortDescBits atomicTyDescBits varIdx atomicPureOpDescBits atomicSymOpDescBits
   atomicSessionOpDescBits atomicExprDescBits atomicCompDescBits)
open Computational.Proofs.Game.PromotedCostedReds.SimFig8State
  (bits_zero bits_eq_of_bounds bits_le_of_lt_pow atomicFig8OpDescBits)
open Computational.Proofs.ReductionDsl.Fig8Atomic
  (opPure opSym opGrp opPtEncPk pkLitExpr optBytesEqExpr optPtEqExpr lPubOfExpr chainGenExpr
   appAux unitsPowExpr aeadEncExpr aeadDecExpr lctEqBody fsInitSendExpr fsInitRecvExpr
   fsSendExpr fsRecvExpr ckaInitAExpr ckaInitBExpr ckaSendExpr ckaRecvExpr
   prngInitExpr prngUpExpr lamIExpr defaultEExpr eqPtExpr smEqCtExpr)

namespace Computational.Proofs.Game.PromotedCostedReds.SimFig8SpqrDesc

/-! ## `bits` bounds and variable-renaming `descBits` -/

section BitsAndRenameDesc
set_option linter.unusedSimpArgs false

theorem small_bits_bounds :
    bits 0 = 1 ∧ bits 1 = 1 ∧ bits 2 = 2 ∧ bits 3 = 2 ∧ bits 4 = 3 ∧ bits 5 = 3 ∧
    bits 6 = 3 ∧ bits 8 = 4 ∧ bits 10 = 4 ∧ bits 16 = 5 ∧ bits 32 = 6 ∧
    bits ((32 : ℕ+) : ℕ) = 6 ∧ bits 64 = 7 ∧ bits 96 = 7 ∧ bits 128 = 8 ∧
    bits 2000 = 11 ∧ bits 25000 = 15 ∧ bits (2 ^ 32) = 33 := by
  have hb0 : bits 0 = 1 := bits_zero
  have hb1 : bits 1 = 1 := bits_eq_of_bounds (by omega) (by omega) (by omega) (by omega)
  have hb2 : bits 2 = 2 := bits_eq_of_bounds (by omega) (by omega) (by omega) (by omega)
  have hb3 : bits 3 = 2 := bits_eq_of_bounds (by omega) (by omega) (by omega) (by omega)
  have hb4 : bits 4 = 3 := bits_eq_of_bounds (by omega) (by omega) (by omega) (by omega)
  have hb5 : bits 5 = 3 := bits_eq_of_bounds (by omega) (by omega) (by omega) (by omega)
  have hb6 : bits 6 = 3 := bits_eq_of_bounds (by omega) (by omega) (by omega) (by omega)
  have hb8 : bits 8 = 4 := bits_eq_of_bounds (by omega) (by omega) (by omega) (by omega)
  have hb10 : bits 10 = 4 := bits_eq_of_bounds (by omega) (by omega) (by omega) (by omega)
  have hb16 : bits 16 = 5 := bits_eq_of_bounds (by omega) (by omega) (by omega) (by omega)
  have hb32 : bits 32 = 6 := bits_eq_of_bounds (by omega) (by omega) (by omega) (by omega)
  have hb64 : bits 64 = 7 := bits_eq_of_bounds (by omega) (by omega) (by omega) (by omega)
  have hb96 : bits 96 = 7 := bits_eq_of_bounds (by omega) (by omega) (by omega) (by omega)
  have hb128 : bits 128 = 8 := bits_eq_of_bounds (by omega) (by omega) (by omega) (by omega)
  have hb2k : bits 2000 = 11 := bits_eq_of_bounds (by omega) (by omega) (by omega) (by omega)
  have hb25k : bits 25000 = 15 := bits_eq_of_bounds (by omega) (by omega) (by omega) (by omega)
  have hb232 : bits (2 ^ 32) = 33 :=
    bits_eq_of_bounds (by omega) (by omega) (by omega) (by omega)
  exact ⟨hb0, hb1, hb2, hb3, hb4, hb5, hb6, hb8, hb10, hb16, hb32, hb32,
    hb64, hb96, hb128, hb2k, hb25k, hb232⟩

theorem bits_mul_le_add {k a b : ℕ} (_ha : 1 ≤ a) (ha2 : a ≤ 2 ^ k) :
    bits (a * b) ≤ k + bits b := by
  by_cases hb0 : b = 0
  · subst hb0
    rw [Nat.mul_zero, bits_zero]; omega
  · have hlt_b : b < 2 ^ bits b := lt_two_pow_bits b
    have hlt : a * b < 2 ^ (k + bits b) := by
      calc a * b ≤ 2 ^ k * b := Nat.mul_le_mul_right b ha2
        _ < 2 ^ k * 2 ^ bits b := Nat.mul_lt_mul_of_pos_left hlt_b (Nat.two_pow_pos k)
        _ = 2 ^ (k + bits b) := (Nat.pow_add 2 k (bits b)).symm
    exact bits_le_of_lt_pow (by unfold bits; omega) hlt

private theorem L_le_ratchetCostBudget (L qep : ℕ) :
    L + 1 ≤ ratchetCostBudget L (qep + 1) + (qep + 1) := by
  unfold ratchetCostBudget
  have hsq : L + 1 ≤ (L + 1) ^ 2 := Nat.le_self_pow (by omega) (L + 1)
  have hm : maxForwardJumps = 25000 := rfl
  have h2 : L + 1 ≤ (2 ^ 12 * (L + 1) ^ 2) * (maxForwardJumps + bits (qep + 1)) := by
    calc L + 1 ≤ (2 ^ 12 * (L + 1) ^ 2) * 1 := by omega
      _ ≤ (2 ^ 12 * (L + 1) ^ 2) * (maxForwardJumps + bits (qep + 1)) :=
          Nat.mul_le_mul_left _ (by omega)
  omega

theorem bits_clampB_le_budget (L qep : ℕ) :
    bits (2 ^ 32 + L + 2) ≤ 34 + bits (ratchetCostBudget L (qep + 1) + (qep + 1)) := by
  have hbud := L_le_ratchetCostBudget L qep
  have hle : 2 ^ 32 + L + 2 ≤ 2 ^ 33 * (ratchetCostBudget L (qep + 1) + (qep + 1)) := by omega
  calc bits (2 ^ 32 + L + 2)
      ≤ bits (2 ^ 33 * (ratchetCostBudget L (qep + 1) + (qep + 1))) := bits_mono hle
    _ ≤ 33 + bits (ratchetCostBudget L (qep + 1) + (qep + 1)) :=
        bits_mul_le_add (by omega) (le_refl (2 ^ 33))
    _ ≤ 34 + bits (ratchetCostBudget L (qep + 1) + (qep + 1)) := by omega

theorem bits_skipB_le_budget (L qep : ℕ) :
    bits (25000 * L) ≤ 15 + bits (ratchetCostBudget L (qep + 1) + (qep + 1)) := by
  have hbud := L_le_ratchetCostBudget L qep
  have hle : 25000 * L ≤ 25000 * (ratchetCostBudget L (qep + 1) + (qep + 1)) :=
    Nat.mul_le_mul_left 25000 (by omega)
  calc bits (25000 * L)
      ≤ bits (25000 * (ratchetCostBudget L (qep + 1) + (qep + 1))) := bits_mono hle
    _ ≤ 15 + bits (ratchetCostBudget L (qep + 1) + (qep + 1)) :=
        bits_mul_le_add (by omega) (show 25000 ≤ 2 ^ 15 by omega)

theorem bits_L_le_budget (L qep : ℕ) :
    bits L ≤ bits (ratchetCostBudget L (qep + 1) + (qep + 1)) := by
  have hbud := L_le_ratchetCostBudget L qep
  exact bits_mono (by omega)

theorem bits_qep1_le_budget (L qep : ℕ) :
    bits (qep + 1) ≤ bits (ratchetCostBudget L (qep + 1) + (qep + 1)) := by
  apply bits_mono; omega

theorem bits_add_le (n : ℕ) : ∀ (k : ℕ), bits (n + k) ≤ bits n + k
  | 0 => le_rfl
  | k + 1 => by
    have hn : n < 2 ^ bits n := lt_two_pow_bits n
    have hb : 1 ≤ bits n := by unfold bits; omega
    have hpow : ∀ m, n + m < 2 ^ (bits n + m) := by
      intro m; induction m with
      | zero => simpa using hn
      | succ m ih =>
        have h1 : 1 ≤ 2 ^ (bits n + m) := Nat.one_le_two_pow
        have hp : 2 ^ (bits n + (m + 1)) = 2 * 2 ^ (bits n + m) := by
          rw [← Nat.add_assoc, Nat.pow_succ]; ring
        omega
    exact bits_le_of_lt_pow (by omega) (hpow (k + 1))

private theorem mul_succ_ge (k x : ℕ) : x ≤ (k + 1) * x :=
  Nat.le_mul_of_pos_left x (Nat.succ_pos k)

private theorem add3_le_mul_succ (k x y z w : ℕ) (hyw : y ≤ (k + 1) * w) :
    x + y + z ≤ (k + 1) * (x + w + z) := by
  have hx := mul_succ_ge k x
  have hz := mul_succ_ge k z
  simp only [Nat.mul_add]
  omega

private def liftRenB {S0 : Sig} {Γ₁ Γ₂ : List (Ty S0)} {a : Ty S0}
    (ren : ∀ ⦃u⦄, Var Γ₁ u → Var Γ₂ u) : ∀ ⦃u⦄, Var (a :: Γ₁) u → Var (a :: Γ₂) u
  | _, .zero => .zero
  | _, .succ w => .succ (ren w)

private theorem liftRenB_varIdx_le {ℓ : ℕ} {Pt : Type} {Γ₁ Γ₂ : List (Ty (atomicSig ℓ Pt))}
    {a : Ty (atomicSig ℓ Pt)} {k : ℕ} {ren : ∀ ⦃u⦄, Var Γ₁ u → Var Γ₂ u}
    (hren : ∀ u (v : Var Γ₁ u), varIdx (ren v) ≤ varIdx v + k) :
    ∀ u (v : Var (a :: Γ₁) u), varIdx (liftRenB ren v) ≤ varIdx v + k
  | _, .zero => Nat.zero_le _
  | _, .succ w => by
    have := hren _ w
    change varIdx (ren w) + 1 ≤ varIdx w + 1 + k
    omega

theorem rename_descBits_le_mul {ℓ : ℕ} {Pt : Type} {O : Ops (atomicSig ℓ Pt)}
    (opB : O.Op → ℕ) (k : ℕ) {Γ₁ Γ₂ : List (Ty (atomicSig ℓ Pt))} {t : Ty (atomicSig ℓ Pt)}
    (ren : ∀ ⦃u⦄, Var Γ₁ u → Var Γ₂ u) (e : Expr O Γ₁ t)
    (hren : ∀ u (v : Var Γ₁ u), varIdx (ren v) ≤ varIdx v + k) :
    atomicExprDescBits opB (Expr.renameM ren e) ≤ (k + 1) * atomicExprDescBits opB e := by
  induction e generalizing Γ₂ with
  | var v =>
    have hv : bits (varIdx (ren v)) ≤ bits (varIdx v) + k :=
      le_trans (bits_mono (hren _ v)) (bits_add_le (varIdx v) k)
    have hk6 : 2 * k ≤ k * (2 * bits (varIdx v) + 6) :=
      le_trans (by omega) (Nat.mul_le_mul_left k (by omega : 2 ≤ 2 * bits (varIdx v) + 6))
    have hmul : (k + 1) * (2 * bits (varIdx v) + 6) =
        (2 * bits (varIdx v) + 6) + k * (2 * bits (varIdx v) + 6) := by ring
    dsimp only [Expr.renameM, atomicExprDescBits]
    omega
  | unit => exact mul_succ_ge k 6
  | bool _ => exact mul_succ_ge k 7
  | nat n => exact mul_succ_ge k (2 * bits n + 6)
  | none => exact mul_succ_ge k (_ + 6)
  | nil => exact mul_succ_ge k (_ + 6)
  | add _ _ ha hb | sub _ _ ha hb | lt _ _ ha hb | eqN _ _ ha hb | and _ _ ha hb
  | pair _ _ ha hb | cons _ _ ha hb | take _ _ ha hb | tget _ _ ha hb =>
    have iha := ha ren hren; have ihb := hb ren hren; have h6 := mul_succ_ge k 6
    dsimp only [Expr.renameM, atomicExprDescBits]; simp only [Nat.mul_add]; omega
  | mulK m _ ha | divK m _ ha | modK m _ ha =>
    have iha := ha ren hren; have hm := mul_succ_ge k (2 * bits m); have h6 := mul_succ_ge k 6
    dsimp only [Expr.renameM, atomicExprDescBits]; simp only [Nat.mul_add]; omega
  | not _ ha | fst _ ha | snd _ ha | some _ ha | len _ ha | tconst _ ha =>
    have iha := ha ren hren; have h6 := mul_succ_ge k 6
    dsimp only [Expr.renameM, atomicExprDescBits]; simp only [Nat.mul_add]; omega
  | inl _ ha | inr _ ha =>
    dsimp only [Expr.renameM, atomicExprDescBits]
    exact add3_le_mul_succ k _ _ 6 _ (ha ren hren)
  | op o _ ha =>
    have iha := ha ren hren; have ho := mul_succ_ge k (opB o); have h6 := mul_succ_ge k 6
    dsimp only [Expr.renameM, atomicExprDescBits]; simp only [Nat.mul_add]; omega
  | ite _ _ _ hc ha hb | tset _ _ _ hc ha hb =>
    have ihc := hc ren hren; have iha := ha ren hren; have ihb := hb ren hren
    have h6 := mul_succ_ge k 6
    dsimp only [Expr.renameM, atomicExprDescBits]; simp only [Nat.mul_add]; omega
  | appendL m _ _ ha hb =>
    have iha := ha ren hren; have ihb := hb ren hren
    have hm := mul_succ_ge k (2 * bits m); have h6 := mul_succ_ge k 6
    dsimp only [Expr.renameM, atomicExprDescBits]; simp only [Nat.mul_add]; omega
  | letE _ _ ha hb =>
    have iha := ha ren hren
    have ihb : atomicExprDescBits opB (Expr.renameM (liftRenB ren) _) ≤ _ :=
      hb (liftRenB ren) (liftRenB_varIdx_le hren)
    have h6 := mul_succ_ge k 6
    change _ + atomicExprDescBits opB (Expr.renameM (liftRenB ren) _) + 6 ≤ _
    dsimp only [atomicExprDescBits]; simp only [Nat.mul_add]; omega
  | findB m _ _ ha hb | anyB m _ _ ha hb | mapB m _ _ ha hb =>
    have iha := ha ren hren
    have ihb : atomicExprDescBits opB (Expr.renameM (liftRenB ren) _) ≤ _ :=
      hb (liftRenB ren) (liftRenB_varIdx_le hren)
    have hm := mul_succ_ge k (2 * bits m); have h6 := mul_succ_ge k 6
    change 2 * bits m + _ + atomicExprDescBits opB (Expr.renameM (liftRenB ren) _) + 6 ≤ _
    dsimp only [atomicExprDescBits]; simp only [Nat.mul_add]; omega
  | caseOpt _ _ _ hc ha hb =>
    have ihc := hc ren hren; have iha := ha ren hren
    have ihb : atomicExprDescBits opB (Expr.renameM (liftRenB ren) _) ≤ _ :=
      hb (liftRenB ren) (liftRenB_varIdx_le hren)
    have h6 := mul_succ_ge k 6
    change _ + _ + atomicExprDescBits opB (Expr.renameM (liftRenB ren) _) + 6 ≤ _
    dsimp only [atomicExprDescBits]; simp only [Nat.mul_add]; omega
  | caseSum _ _ _ hc ha hb =>
    have ihc := hc ren hren
    have iha : atomicExprDescBits opB (Expr.renameM (liftRenB ren) _) ≤ _ :=
      ha (liftRenB ren) (liftRenB_varIdx_le hren)
    have ihb : atomicExprDescBits opB (Expr.renameM (liftRenB ren) _) ≤ _ :=
      hb (liftRenB ren) (liftRenB_varIdx_le hren)
    have h6 := mul_succ_ge k 6
    change _ + atomicExprDescBits opB (Expr.renameM (liftRenB ren) _) +
      atomicExprDescBits opB (Expr.renameM (liftRenB ren) _) + 6 ≤ _
    dsimp only [atomicExprDescBits]; simp only [Nat.mul_add]; omega
  | @foldrB Γ0 t0 u0 m el ez ef hl hz hf =>
    have ihl := hl ren hren; have ihz := hz ren hren
    have hren1 : ∀ u (v : Var (u0 :: Γ0) u), varIdx (liftRenB ren v) ≤ varIdx v + k :=
      liftRenB_varIdx_le hren
    have hren2 : ∀ u (v : Var (t0 :: u0 :: Γ0) u),
        varIdx (liftRenB (liftRenB ren) v) ≤ varIdx v + k :=
      liftRenB_varIdx_le hren1
    have ihf := hf (liftRenB (liftRenB ren)) hren2
    have hfeq : Expr.renameM (_root_.ReductionDsl.liftRen (_root_.ReductionDsl.liftRen ren)) ef =
        Expr.renameM (liftRenB (liftRenB ren)) ef := by
      rfl
    have hm := mul_succ_ge k (2 * bits m); have h6 := mul_succ_ge k 6
    dsimp only [Expr.renameM, atomicExprDescBits]
    rw [hfeq]; simp only [Nat.mul_add]; omega

private theorem liftRen_varIdx {ℓ : ℕ} {Pt : Type}
    {Γ₁ Γ₂ : List (Ty (atomicSig ℓ Pt))} {u : Ty (atomicSig ℓ Pt)}
    {f : ∀ {t}, Var Γ₁ t → Var Γ₂ t}
    (hf : ∀ {t} (v : Var Γ₁ t), varIdx (f v) = varIdx v) :
    ∀ {t} (v : Var (u :: Γ₁) t), varIdx (liftRen f v) = varIdx v
  | _, .zero => rfl
  | _, .succ v => by change varIdx (f v) + 1 = varIdx v + 1; rw [hf v]

theorem renExpr_descBits_eq {ℓ : ℕ} {Pt : Type} {O' : Ops (atomicSig ℓ Pt)} (opB : O'.Op → ℕ)
    {Γ₁ Γ₂ : List (Ty (atomicSig ℓ Pt))} {t : Ty (atomicSig ℓ Pt)}
    (f : ∀ {u}, Var Γ₁ u → Var Γ₂ u) (e : Expr O' Γ₁ t)
    (hf : ∀ {u} (v : Var Γ₁ u), varIdx (f v) = varIdx v) :
    atomicExprDescBits opB (renExpr f e) = atomicExprDescBits opB e := by
  induction e generalizing Γ₂ with
  | var v => dsimp only [renExpr, atomicExprDescBits]; rw [hf v]
  | unit | bool _ | nat _ | none | nil => rfl
  | add _ _ ha hb | sub _ _ ha hb | lt _ _ ha hb | eqN _ _ ha hb | and _ _ ha hb
  | pair _ _ ha hb | cons _ _ ha hb | take _ _ ha hb | appendL _ _ _ ha hb | tget _ _ ha hb =>
    simp only [renExpr, atomicExprDescBits, ha f hf, hb f hf]
  | mulK _ _ ha | divK _ _ ha | modK _ _ ha | not _ ha | fst _ ha | snd _ ha
  | inl _ ha | inr _ ha | some _ ha | op _ _ ha | len _ ha | tconst _ ha =>
    simp only [renExpr, atomicExprDescBits, ha f hf]
  | ite _ _ _ hc ha hb | tset _ _ _ hc ha hb =>
    simp only [renExpr, atomicExprDescBits, hc f hf, ha f hf, hb f hf]
  | caseOpt _ _ _ he hn hs =>
    simp only [renExpr, atomicExprDescBits, he f hf, hn f hf, hs (liftRen f) (liftRen_varIdx hf)]
  | caseSum _ _ _ he hl hr =>
    simp only [renExpr, atomicExprDescBits, he f hf,
      hl (liftRen f) (liftRen_varIdx hf), hr (liftRen f) (liftRen_varIdx hf)]
  | letE _ _ he hb | findB _ _ _ he hb | anyB _ _ _ he hb | mapB _ _ _ he hb =>
    simp only [renExpr, atomicExprDescBits, he f hf, hb (liftRen f) (liftRen_varIdx hf)]
  | foldrB _ _ _ _ hl hz hg =>
    simp only [renExpr, atomicExprDescBits, hl f hf, hz f hf,
      hg (liftRen (liftRen f)) (liftRen_varIdx (liftRen_varIdx hf))]

theorem renComp_descBits_eq {ℓ : ℕ} {Pt : Type} {O' : Ops (atomicSig ℓ Pt)}
    {ι : Type} {T : OracleSpec ι} {I' : Iface (atomicSig ℓ Pt) T}
    (opB : O'.Op → ℕ) (sB : I'.smp.Samp → ℕ) (qB : I'.Tag → ℕ)
    {Γ₁ Γ₂ : List (Ty (atomicSig ℓ Pt))} {t : Ty (atomicSig ℓ Pt)}
    (f : ∀ {u}, Var Γ₁ u → Var Γ₂ u) (c : Comp O' I' Γ₁ t)
    (hf : ∀ {u} (v : Var Γ₁ u), varIdx (f v) = varIdx v) :
    atomicCompDescBits opB sB qB (renComp f c) = atomicCompDescBits opB sB qB c := by
  induction c generalizing Γ₂ with
  | ret e | sample _ e | query _ e =>
    simp only [renComp, atomicCompDescBits, renExpr_descBits_eq opB f e hf]
  | bind _ _ hc hk =>
    simp only [renComp, atomicCompDescBits, hc f hf, hk (liftRen f) (liftRen_varIdx hf)]
  | ite b _ _ hc hd =>
    simp only [renComp, atomicCompDescBits, renExpr_descBits_eq opB f b hf, hc f hf, hd f hf]
  | caseOpt e _ _ hn hs =>
    simp only [renComp, atomicCompDescBits, renExpr_descBits_eq opB f e hf,
      hn f hf, hs (liftRen f) (liftRen_varIdx hf)]
  | caseSum e _ _ hl hr =>
    simp only [renComp, atomicCompDescBits, renExpr_descBits_eq opB f e hf,
      hl (liftRen f) (liftRen_varIdx hf), hr (liftRen f) (liftRen_varIdx hf)]
  | iter _ e _ hb | findM _ e _ hb | anyM _ e _ hb | mapM _ e _ hb =>
    simp only [renComp, atomicCompDescBits, renExpr_descBits_eq opB f e hf,
      hb (liftRen f) (liftRen_varIdx hf)]
  | consumeFirstM _ l _ mk hp =>
    simp only [renComp, atomicCompDescBits, renExpr_descBits_eq opB f l hf,
      hp (liftRen f) (liftRen_varIdx hf),
      renExpr_descBits_eq opB (liftRen f) mk (liftRen_varIdx hf)]
  | foldM _ l z _ hg =>
    simp only [renComp, atomicCompDescBits, renExpr_descBits_eq opB f l hf,
      renExpr_descBits_eq opB f z hf,
      hg (liftRen (liftRen f)) (liftRen_varIdx (liftRen_varIdx hf))]

@[simp] theorem wk1Comp_descBits_eq {ℓ : ℕ} {Pt : Type} {O' : Ops (atomicSig ℓ Pt)}
    {ι : Type} {T : OracleSpec ι} {I' : Iface (atomicSig ℓ Pt) T}
    (opB : O'.Op → ℕ) (sB : I'.smp.Samp → ℕ) (qB : I'.Tag → ℕ)
    {a b : Ty (atomicSig ℓ Pt)} {Γ : List (Ty (atomicSig ℓ Pt))} (c : Comp O' I' [a] b) :
    atomicCompDescBits opB sB qB (wk1Comp (Γ := Γ) c) = atomicCompDescBits opB sB qB c :=
  renComp_descBits_eq opB sB qB wk1Ren c fun {_} v => by
    cases v with
    | zero => rfl
    | succ w => nomatch w

end BitsAndRenameDesc

/-! ## Compositional `SPQR` `descBits` bridge -/

section SpqrDescBridge

open CryptoVerification.E2E.Costed (E2ESort E2EPureOp E2ECurveCheckOp E2ECryptoOp e2eSig e2eOps
  U8 U32 U64 spqrVnT spqrParamsT spqrPrevEntryT spqrDirT spqrEpochLinkT spqrChainT spqrStatePartsT)
open Computational.Proofs.E2E.Dsl.TablesHonest (e2ePureOp e2eCurveOp e2eCryptoOp)
open Computational.Proofs.E2E.Dsl.PqxdhSimTypes (Ext v letV bindV bindV2 caseOptV caseSumV
  findMV anyMV mapMV orE isSomeE isNoneE optMapE)

def e2eSortDescBits : E2ESort → ℕ
  | .pbytes w | .bytes w => 2 * bits w + 4
  | .fin n => 2 * bits n + 4
  | .pu32 | .u8 | .u32 | .u64 | .bv128 | .bv256 | .bv512
  | .pk | .idKey | .plain | .ghostSt | .binSt => 4

@[simp] def e2eTyDescBits {ℓ : ℕ} : Ty (e2eSig ℓ) → ℕ
  | .base b => e2eSortDescBits b + 4
  | .unit | .bool | .nat => 4
  | .opt t | .list t | .tbl t => e2eTyDescBits t + 4
  | .prod t u | .sum t u => e2eTyDescBits t + e2eTyDescBits u + 4

private theorem atomicSortDescBits_liftSort (b : E2ESort) :
    atomicSortDescBits (liftSort b) = e2eSortDescBits b := by
  cases b <;> rfl

private theorem atomicTyDescBits_liftTy {ℓ : ℕ} {Pt : Type} :
    ∀ (t : Ty (e2eSig ℓ)), atomicTyDescBits (liftTy (Pt := Pt) t) = e2eTyDescBits t
  | .base b => by dsimp only [liftTy]; simp [atomicTyDescBits, atomicSortDescBits_liftSort]
  | .unit | .bool | .nat => rfl
  | .opt t | .list t | .tbl t => by
    dsimp only [liftTy]; simp [atomicTyDescBits, atomicTyDescBits_liftTy t]
  | .prod t u | .sum t u => by
    dsimp only [liftTy]
    simp [atomicTyDescBits, atomicTyDescBits_liftTy t, atomicTyDescBits_liftTy u]

private theorem varIdx_liftVar {ℓ : ℕ} {Pt : Type} :
    ∀ {Γ : List (Ty (e2eSig ℓ))} {t : Ty (e2eSig ℓ)} (x : Var Γ t),
      varIdx (liftVar (Pt := Pt) x) = varIdx x
  | _ :: _, _, .zero => rfl
  | _ :: _, _, .succ x => congrArg (· + 1) (varIdx_liftVar x)

private theorem varIdx_lt_len {S0 : Sig} :
    ∀ {Γ : List (Ty S0)} {t : Ty S0} (x : Var Γ t), varIdx x < Γ.length
  | _ :: _, _, .zero => Nat.zero_lt_succ _
  | _ :: _, _, .succ x => Nat.succ_lt_succ (varIdx_lt_len x)

@[simp] def e2ePureOpDescBits : E2EPureOp → ℕ
  | .pbytesLit w v => 8 * v.length + 2 * bits v.length + 2 * bits w + 8
  | .bytesLit w v => 8 * v.length + 2 * bits v.length + 2 * bits w + 8
  | .pbytesCat m n | .pbytesEq m n | .bytesCat m n | .bytesEq m n | .bytesLtOp m n =>
    2 * bits m + 2 * bits n + 8
  | .pbytesCons _ w | .bytesCons _ w => 2 * bits w + 16
  | .pbytesWiden w d | .bytesWiden w d => 2 * bits w + 2 * bits d + 8
  | .pbytesTakeK w k | .bytesTakeK w k => 2 * bits w + 2 * bits k + 8
  | .pbytesTake w | .pbytesDrop w | .pbytesLen w | .pbytesToBytes w
  | .bytesTake w | .bytesDrop w | .bytesLen w | .bytesToPbytes w => 2 * bits w + 8
  | .pu32Lit _ | .u32Lit _ => 40
  | .u8Lit _ => 16
  | .u64Lit _ => 72
  | .bv256Lit _ => 264
  | .bv512Lit _ => 520
  | .finVal n | .finEq n => 2 * bits n + 8
  | .pu32OfNat | .pu32ToNat | .pu32Eq | .pu32ToU32 | .u32ToPu32
  | .u8OfNat | .u8ToNat | .u8Eq | .u8Lt
  | .u32OfNat | .u32ToNat | .u32Eq | .u32Lt | .u32Add | .u32Sub | .u32BeBytes
  | .u64OfNat | .u64ToNat | .u64Eq | .u64Lt | .u64Add | .u64Sub | .u64Trunc8
  | .bv128Eq | .bv256Eq | .bv256ToPbytes32 | .pbytesToBv256 | .bv256ToBytes32 | .bytesToBv256
  | .bv512ToBytes64
  | .idKeyOfPbytes | .idKeySerialize | .idKeyEq
  | .pkOfPbytes | .pkDeserialize | .pkSerialize | .pkEq
  | .plainDefault | .plainToBytes | .bytesToPlain | .plainEq
  | .checkShortCiphertext | .parsePreKeyWire | .partneredInnerBytes | .wireInnerBytes
  | .splitWhisperWire | .isValidSignalWire | .signalMsgParse | .wrapWhisperWire | .wrapPreKeyWire
  | .spqrParsePreamble | .spqrAssembleMsg | .spqrStateSplit | .spqrStateJoin
  | .ghostStateSplit | .ghostStateJoin | .encodeSessionRecord => 8

@[simp] def e2eOpDescUB {ℓ : ℕ} {Pt : Type} {P : SignalPqxdh.Primitives} {C : Crypto} {K : MlKem}
    {decT : PublicKey → Option Pt} {encT : Pt → PublicKey} :
    (e2eOps ℓ P C K decT encT).Op → ℕ
  | .inl o => e2ePureOpDescBits o + 4
  | .inr (.inl _) => 12
  | .inr (.inr _) => 200

@[simp] def edepth {S0 : Sig} {O : Ops S0} : {Γ : List (Ty S0)} → {t : Ty S0} → Expr O Γ t → ℕ
  | _, _, .var _ | _, _, .unit | _, _, .bool _ | _, _, .nat _ | _, _, .none | _, _, .nil => 0
  | _, _, .mulK _ a | _, _, .divK _ a | _, _, .modK _ a | _, _, .not a
  | _, _, .fst a | _, _, .snd a | _, _, .inl a | _, _, .inr a | _, _, .some a
  | _, _, .op _ a | _, _, .len a | _, _, .tconst a => edepth a
  | _, _, .add a b | _, _, .sub a b | _, _, .lt a b | _, _, .eqN a b | _, _, .and a b
  | _, _, .pair a b | _, _, .cons a b | _, _, .take a b | _, _, .appendL _ a b
  | _, _, .tget a b => max (edepth a) (edepth b)
  | _, _, .ite c a b | _, _, .tset c a b => max (edepth c) (max (edepth a) (edepth b))
  | _, _, .caseOpt e n s => max (edepth e) (max (edepth n) (edepth s + 1))
  | _, _, .caseSum e l r => max (edepth e) (max (edepth l + 1) (edepth r + 1))
  | _, _, .letE e b | _, _, .findB _ e b | _, _, .anyB _ e b | _, _, .mapB _ e b =>
    max (edepth e) (edepth b + 1)
  | _, _, .foldrB _ l z f => max (edepth l) (max (edepth z) (edepth f + 2))

@[simp] def cdepth {S0 : Sig} {O : Ops S0} {ι : Type} {T : OracleSpec ι} {I : Iface S0 T} :
    {Γ : List (Ty S0)} → {t : Ty S0} → Comp O I Γ t → ℕ
  | _, _, .ret e | _, _, .sample _ e | _, _, .query _ e => edepth e
  | _, _, .bind c k => max (cdepth c) (cdepth k + 1)
  | _, _, .ite b c d => max (edepth b) (max (cdepth c) (cdepth d))
  | _, _, .caseOpt e n s => max (edepth e) (max (cdepth n) (cdepth s + 1))
  | _, _, .caseSum e l r => max (edepth e) (max (cdepth l + 1) (cdepth r + 1))
  | _, _, .iter _ e b | _, _, .findM _ e b | _, _, .anyM _ e b | _, _, .mapM _ e b =>
    max (edepth e) (cdepth b + 1)
  | _, _, .consumeFirstM _ l p mk => max (edepth l) (max (cdepth p + 1) (edepth mk + 1))
  | _, _, .foldM _ l z f => max (edepth l) (max (edepth z) (cdepth f + 2))

@[simp] def e2eEDescUB {ℓ : ℕ} {Pt : Type} {P : SignalPqxdh.Primitives} {C : Crypto} {K : MlKem}
    {decT : PublicKey → Option Pt} {encT : Pt → PublicKey} :
    {Γ : List (Ty (e2eSig ℓ))} → {t : Ty (e2eSig ℓ)} →
    Expr (e2eOps ℓ P C K decT encT) Γ t → ℕ
  | _, _, .var _ => 22
  | _, _, .unit => 6
  | _, _, .bool _ => 7
  | _, _, .nat n => 2 * bits n + 6
  | _, _, .add a b | _, _, .sub a b | _, _, .lt a b | _, _, .eqN a b | _, _, .and a b
  | _, _, .pair a b | _, _, .cons a b | _, _, .take a b | _, _, .tget a b =>
    e2eEDescUB (Pt := Pt) a + e2eEDescUB (Pt := Pt) b + 6
  | _, _, .mulK k a | _, _, .divK k a | _, _, .modK k a => 2 * bits k + e2eEDescUB (Pt := Pt) a + 6
  | _, _, .not a | _, _, .fst a | _, _, .snd a | _, _, .some a
  | _, _, .len a | _, _, .tconst a => e2eEDescUB (Pt := Pt) a + 6
  | _, _, .ite c a b | _, _, .tset c a b =>
    e2eEDescUB (Pt := Pt) c + e2eEDescUB (Pt := Pt) a + e2eEDescUB (Pt := Pt) b + 6
  | _, .sum _ u, .inl a => e2eTyDescBits u + e2eEDescUB (Pt := Pt) a + 6
  | _, .sum t _, .inr a => e2eTyDescBits t + e2eEDescUB (Pt := Pt) a + 6
  | _, .opt t, .none => e2eTyDescBits t + 6
  | _, .list t, .nil => e2eTyDescBits t + 6
  | _, _, .caseOpt e n s =>
    e2eEDescUB (Pt := Pt) e + e2eEDescUB (Pt := Pt) n + e2eEDescUB (Pt := Pt) s + 6
  | _, _, .caseSum e l r =>
    e2eEDescUB (Pt := Pt) e + e2eEDescUB (Pt := Pt) l + e2eEDescUB (Pt := Pt) r + 6
  | _, _, .letE e b => e2eEDescUB (Pt := Pt) e + e2eEDescUB (Pt := Pt) b + 6
  | _, _, .op o a => e2eOpDescUB (Pt := Pt) o + e2eEDescUB (Pt := Pt) a + 6
  | _, _, .appendL k a b | _, _, .findB k a b | _, _, .anyB k a b | _, _, .mapB k a b =>
    2 * bits k + e2eEDescUB (Pt := Pt) a + e2eEDescUB (Pt := Pt) b + 6
  | _, _, .foldrB k l z f =>
    2 * bits k + e2eEDescUB (Pt := Pt) l + e2eEDescUB (Pt := Pt) z + e2eEDescUB (Pt := Pt) f + 6

@[simp] def e2eCDescUB {ℓ : ℕ} {Pt : Type} {P : SignalPqxdh.Primitives} {C : Crypto} {K : MlKem}
    {decT : PublicKey → Option Pt} {encT : Pt → PublicKey}
    {ι : Type} {T : OracleSpec ι} {I : Iface (e2eSig ℓ) T} :
    {Γ : List (Ty (e2eSig ℓ))} → {t : Ty (e2eSig ℓ)} →
    Comp (e2eOps ℓ P C K decT encT) I Γ t → ℕ
  | _, _, .ret e => e2eEDescUB (Pt := Pt) e + 6
  | _, _, .sample _ e | _, _, .query _ e => e2eEDescUB (Pt := Pt) e + 64
  | _, _, .bind c k => e2eCDescUB (Pt := Pt) c + e2eCDescUB (Pt := Pt) k + 6
  | _, _, .ite b c d =>
    e2eEDescUB (Pt := Pt) b + e2eCDescUB (Pt := Pt) c + e2eCDescUB (Pt := Pt) d + 6
  | _, _, .caseOpt e n s =>
    e2eEDescUB (Pt := Pt) e + e2eCDescUB (Pt := Pt) n + e2eCDescUB (Pt := Pt) s + 6
  | _, _, .caseSum e l r =>
    e2eEDescUB (Pt := Pt) e + e2eCDescUB (Pt := Pt) l + e2eCDescUB (Pt := Pt) r + 6
  | _, _, .iter n e b | _, _, .findM n e b | _, _, .anyM n e b | _, _, .mapM n e b =>
    2 * bits n + e2eEDescUB (Pt := Pt) e + e2eCDescUB (Pt := Pt) b + 6
  | _, _, .consumeFirstM k l p mk =>
    2 * bits k + e2eEDescUB (Pt := Pt) l + e2eCDescUB (Pt := Pt) p + e2eEDescUB (Pt := Pt) mk + 6
  | _, _, .foldM k l z f =>
    2 * bits k + e2eEDescUB (Pt := Pt) l + e2eEDescUB (Pt := Pt) z + e2eCDescUB (Pt := Pt) f + 6

private theorem liftPureOpExpr_descBits_eq {ℓ : ℕ} {Pt : Type} [DecidableEq Pt] [Zero Pt]
    {C : Crypto} {K : MlKem} {Dh : DHFun (BitVec 256) Pt} {encPt : Pt → Bytes}
    {encT : Pt → PublicKey} {decT : PublicKey → Option Pt} {lam : Pt}
    {Γ : List (Ty (atomicSig ℓ Pt))} (o : E2EPureOp)
    (a : Expr (atomicSessionOps ℓ Pt C K Dh encPt encT decT lam) Γ (liftTy (Pt := Pt) (o.dom ℓ))) :
    atomicExprDescBits atomicSessionOpDescBits
      (liftPureOpExpr (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT)
        (decT := decT) (lam := lam) o a) =
      (e2ePureOpDescBits o + 4) + atomicExprDescBits atomicSessionOpDescBits a + 6 := by
  cases o <;> rfl

private theorem op_desc_le {ℓ : ℕ} {Pt : Type} {O : Ops (atomicSig ℓ Pt)} {opB : O.Op → ℕ}
    {Γ : List (Ty (atomicSig ℓ Pt))} {T : Ty (atomicSig ℓ Pt)}
    {op : O.Op} {a : Expr O Γ T} {a' : Expr O Γ (O.dom op)} {u : ℕ}
    (ha : atomicExprDescBits opB a' = atomicExprDescBits opB a)
    (hop : opB op ≤ u) :
    atomicExprDescBits opB (.op op a') ≤ u + atomicExprDescBits opB a + 6 := by
  dsimp only [atomicExprDescBits]; rw [ha]; omega

private theorem letE_desc_le {ℓ : ℕ} {Pt : Type} {O : Ops (atomicSig ℓ Pt)} (opB : O.Op → ℕ)
    {Γ : List (Ty (atomicSig ℓ Pt))} {T U : Ty (atomicSig ℓ Pt)}
    (a : Expr O Γ T) (b : Expr O (T :: Γ) U) (u : ℕ)
    (hb : atomicExprDescBits opB b ≤ u) :
    atomicExprDescBits opB (.letE a b) ≤ u + atomicExprDescBits opB a + 6 := by
  dsimp only [atomicExprDescBits]; omega

private theorem liftCurveOpExpr_descBits_le {ℓ : ℕ} {Pt : Type} [DecidableEq Pt] [Zero Pt]
    {C : Crypto} {K : MlKem} {Dh : DHFun (BitVec 256) Pt} {encPt : Pt → Bytes}
    {encT : Pt → PublicKey} {decT : PublicKey → Option Pt} {lam : Pt}
    {Γ : List (Ty (atomicSig ℓ Pt))} (cc : E2ECurveCheckOp)
    (a : Expr (atomicSessionOps ℓ Pt C K Dh encPt encT decT lam) Γ
      (liftTy (Pt := Pt) ((CryptoVerification.E2E.Costed.e2eCurveCheckOps ℓ decT encT).dom cc))) :
    atomicExprDescBits atomicSessionOpDescBits
      (liftCurveOpExpr (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT)
        (decT := decT) (lam := lam) cc a) ≤
      12 + atomicExprDescBits atomicSessionOpDescBits a + 6 := by
  cases cc <;> (
    dsimp only [liftCurveOpExpr, sessCurveOp]
    refine op_desc_le rfl ?_
    dsimp only [atomicSessionOpDescBits]; omega)

set_option linter.unusedSimpArgs false in
private theorem liftCryptoOpExpr_descBits_le {ℓ : ℕ} {Pt : Type} [DecidableEq Pt] [Zero Pt]
    {C : Crypto} {K : MlKem} {Dh : DHFun (BitVec 256) Pt} {encPt : Pt → Bytes}
    {encT : Pt → PublicKey} {decT : PublicKey → Option Pt} {lam : Pt}
    {Γ : List (Ty (atomicSig ℓ Pt))} (c : E2ECryptoOp)
    (a : Expr (atomicSessionOps ℓ Pt C K Dh encPt encT decT lam) Γ (liftTy (Pt := Pt) (c.dom ℓ))) :
    atomicExprDescBits atomicSessionOpDescBits
      (liftCryptoOpExpr (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT)
        (decT := decT) (lam := lam) c a) ≤
      200 + atomicExprDescBits atomicSessionOpDescBits a + 6 := by
  have hb0 : bits 0 = 1 := bits_zero
  have hb32 : bits 32 = 6 := bits_eq_of_bounds (by omega) (by omega) (by omega) (by omega)
  have hbp32 : bits ((32 : ℕ+) : ℕ) = 6 := hb32
  have hb64 : bits 64 = 7 := bits_eq_of_bounds (by omega) (by omega) (by omega) (by omega)
  have hbp64 : bits ((64 : ℕ+) : ℕ) = 7 := hb64
  have hb1568 : bits 1568 = 11 := bits_eq_of_bounds (by omega) (by omega) (by omega) (by omega)
  have hbp1568 : bits ((1568 : ℕ+) : ℕ) = 11 := hb1568
  have hb3168 : bits 3168 = 12 := bits_eq_of_bounds (by omega) (by omega) (by omega) (by omega)
  have hbp3168 : bits ((3168 : ℕ+) : ℕ) = 12 := hb3168
  cases c with
  | x25519 | x25519Base | pow8 | isCanonical | sigSign | sigVerify
  | kemKeyGen | kemEncaps | kemDecaps | hkdfDerive96 =>
    dsimp only [liftCryptoOpExpr]
    refine letE_desc_le _ a _ 200 ?_
    dsimp only [sessPureOp, E2ECryptoOp.cod,
      Computational.Proofs.SpecLemmas.Reductions.E2E.CompositionCostedTables.E2ECryptoOp.cod,
      CryptoVerification.E2E.Costed.E2ECryptoOp.cod,
      Computational.Proofs.SpecLemmas.Reductions.E2E.CompositionCostedTables.PB,
      Computational.Proofs.SpecLemmas.Reductions.E2E.CompositionCostedTables.BV256,
      CryptoVerification.E2E.Costed.PB, CryptoVerification.E2E.Costed.BV256,
      ReductionDsl.PB, ReductionDsl.BV256, PNat.val_ofNat, List.length_nil,
      liftTy, liftSort, atomicExprDescBits, atomicTyDescBits, atomicSortDescBits,
      atomicSessionOpDescBits, atomicPureOpDescBits]
    try simp only [hb0, hb32, hbp32, hb64, hbp64, hb1568, hbp1568, hb3168, hbp3168]
    omega
  | _ =>
    dsimp only [liftCryptoOpExpr, sessSymOp, sessSpqrKemOp]
    refine op_desc_le rfl ?_
    dsimp only [atomicSessionOpDescBits, atomicSymOpDescBits]
    omega

private theorem liftOpExpr_descBits_le {ℓ : ℕ} {Pt : Type} [DecidableEq Pt] [Zero Pt]
    {C : Crypto} {K : MlKem} {Dh : DHFun (BitVec 256) Pt} {encPt : Pt → Bytes}
    {encT : Pt → PublicKey} {decT : PublicKey → Option Pt} {lam : Pt}
    {Γ : List (Ty (atomicSig ℓ Pt))}
    (o : (e2eOps ℓ zeroPqxdhPrims C K decT encT).Op)
    (a : Expr (atomicSessionOps ℓ Pt C K Dh encPt encT decT lam) Γ
      (liftTy (Pt := Pt) ((e2eOps ℓ zeroPqxdhPrims C K decT encT).dom o))) :
    atomicExprDescBits atomicSessionOpDescBits
      (liftOpExpr (Pt := Pt) (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT)
        (decT := decT) (lam := lam) o a) ≤
      e2eOpDescUB (Pt := Pt) o + atomicExprDescBits atomicSessionOpDescBits a + 6 := by
  rcases o with o | (cc | c)
  · exact Nat.le_of_eq (liftPureOpExpr_descBits_eq (Pt := Pt) (C := C) (K := K) (Dh := Dh)
      (encPt := encPt) (encT := encT) (decT := decT) (lam := lam) o a)
  · exact liftCurveOpExpr_descBits_le (Pt := Pt) (C := C) (K := K) (Dh := Dh)
      (encPt := encPt) (encT := encT) (decT := decT) (lam := lam) cc a
  · exact liftCryptoOpExpr_descBits_le (Pt := Pt) (C := C) (K := K) (Dh := Dh)
      (encPt := encPt) (encT := encT) (decT := decT) (lam := lam) c a

theorem liftExpr_descBits_le {ℓ : ℕ} {Pt : Type} [DecidableEq Pt] [Zero Pt]
    {C : Crypto} {K : MlKem} {Dh : DHFun (BitVec 256) Pt} {encPt : Pt → Bytes}
    {encT : Pt → PublicKey} {decT : PublicKey → Option Pt} {lam : Pt}
    {Γ : List (Ty (e2eSig ℓ))} {t : Ty (e2eSig ℓ)}
    (e : Expr (e2eOps ℓ zeroPqxdhPrims C K decT encT) Γ t)
    (h : Γ.length + edepth e ≤ 256) :
    atomicExprDescBits atomicSessionOpDescBits
      (liftExpr (Pt := Pt) (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT)
        (decT := decT) (lam := lam) e) ≤ e2eEDescUB (Pt := Pt) e := by
  induction e with
  | var x =>
    have hlt : varIdx x < 2 ^ 8 := lt_of_lt_of_le (varIdx_lt_len x) (by simp [edepth] at h; omega)
    have hb : bits (varIdx x) ≤ 8 := bits_le_of_lt_pow (by omega) hlt
    simp only [liftExpr, atomicExprDescBits, varIdx_liftVar, e2eEDescUB]; omega
  | unit | bool _ | nat _ => simp [liftExpr, atomicExprDescBits, e2eEDescUB]
  | none | nil => simp [liftExpr, atomicExprDescBits, atomicTyDescBits_liftTy, e2eEDescUB]
  | inl a ih | inr a ih =>
    simp only [edepth] at h; have := ih h
    simp only [liftExpr, atomicExprDescBits, atomicTyDescBits_liftTy, e2eEDescUB]; omega
  | mulK _ a ih | divK _ a ih | modK _ a ih | not a ih | fst a ih | snd a ih
  | some a ih | len a ih | tconst a ih =>
    simp only [edepth] at h; have := ih h
    simp only [liftExpr, atomicExprDescBits, e2eEDescUB]; omega
  | op o a ih =>
    simp only [edepth] at h; have iha := ih h
    have hop := liftOpExpr_descBits_le (Pt := Pt) (C := C) (K := K) (Dh := Dh) (encPt := encPt)
      (encT := encT) (decT := decT) (lam := lam) o
      (liftExpr (Pt := Pt) (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT)
        (decT := decT) (lam := lam) a)
    dsimp only [liftExpr, e2eEDescUB]; omega
  | add a b ha hb | sub a b ha hb | lt a b ha hb | eqN a b ha hb | and a b ha hb
  | pair a b ha hb | cons a b ha hb | take a b ha hb | appendL _ a b ha hb | tget a b ha hb =>
    simp only [edepth] at h; have := ha (by omega); have := hb (by omega)
    simp only [liftExpr, atomicExprDescBits, e2eEDescUB]; omega
  | ite c a b hc ha hb | tset c a b hc ha hb =>
    simp only [edepth] at h
    have := hc (by omega); have := ha (by omega); have := hb (by omega)
    simp only [liftExpr, atomicExprDescBits, e2eEDescUB]; omega
  | caseOpt e n s he hn hs =>
    simp only [edepth] at h
    have := he (by omega); have := hn (by omega); have := hs (by simp; omega)
    simp only [liftExpr, atomicExprDescBits, e2eEDescUB]; omega
  | caseSum e l r he hl hr =>
    simp only [edepth] at h
    have := he (by omega); have := hl (by simp; omega); have := hr (by simp; omega)
    simp only [liftExpr, atomicExprDescBits, e2eEDescUB]; omega
  | letE e b he hb | findB _ e b he hb | anyB _ e b he hb | mapB _ e b he hb =>
    simp only [edepth] at h; have := he (by omega); have := hb (by simp; omega)
    simp only [liftExpr, atomicExprDescBits, e2eEDescUB]; omega
  | foldrB _ l z f hl hz hf =>
    simp only [edepth] at h
    have := hl (by omega); have := hz (by omega); have := hf (by simp; omega)
    simp only [liftExpr, atomicExprDescBits, e2eEDescUB]; omega

theorem liftCompEmpty_descBits_le {ℓ : ℕ} {Pt : Type} [DecidableEq Pt] [Zero Pt]
    {C : Crypto} {K : MlKem} {Dh : DHFun (BitVec 256) Pt} {encPt : Pt → Bytes}
    {encT : Pt → PublicKey} {decT : PublicKey → Option Pt} {lam : Pt}
    {ι : Type} {T : OracleSpec ι} {I' : Iface (atomicSig ℓ Pt) T}
    (sB : I'.smp.Samp → ℕ) (qB : I'.Tag → ℕ)
    {Γ : List (Ty (e2eSig ℓ))} {t : Ty (e2eSig ℓ)}
    (c : Comp (e2eOps ℓ zeroPqxdhPrims C K decT encT) (emptyE2EIface I') Γ t)
    (h : Γ.length + cdepth c ≤ 256) :
    atomicCompDescBits atomicSessionOpDescBits sB qB
      (liftCompEmpty (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT)
        (decT := decT) (lam := lam) (I' := I') c) ≤ e2eCDescUB (Pt := Pt) c := by
  induction c with
  | sample s _ => exact s.elim
  | query g _ => exact g.elim
  | ret e =>
    simp only [cdepth] at h
    have := liftExpr_descBits_le (Pt := Pt) (C := C) (K := K) (Dh := Dh) (encPt := encPt)
      (encT := encT) (decT := decT) (lam := lam) e h
    simp only [liftCompEmpty, atomicCompDescBits, e2eCDescUB]; omega
  | bind _ _ hc hk =>
    simp only [cdepth] at h; have := hc (by omega); have := hk (by simp; omega)
    simp only [liftCompEmpty, atomicCompDescBits, e2eCDescUB]; omega
  | ite b _ _ hc hd =>
    simp only [cdepth] at h
    have := liftExpr_descBits_le (Pt := Pt) (C := C) (K := K) (Dh := Dh) (encPt := encPt)
      (encT := encT) (decT := decT) (lam := lam) b (by omega)
    have := hc (by omega); have := hd (by omega)
    simp only [liftCompEmpty, atomicCompDescBits, e2eCDescUB]; omega
  | caseOpt e _ _ hn hs =>
    simp only [cdepth] at h
    have := liftExpr_descBits_le (Pt := Pt) (C := C) (K := K) (Dh := Dh) (encPt := encPt)
      (encT := encT) (decT := decT) (lam := lam) e (by omega)
    have := hn (by omega); have := hs (by simp; omega)
    simp only [liftCompEmpty, atomicCompDescBits, e2eCDescUB]; omega
  | caseSum e _ _ hl hr =>
    simp only [cdepth] at h
    have := liftExpr_descBits_le (Pt := Pt) (C := C) (K := K) (Dh := Dh) (encPt := encPt)
      (encT := encT) (decT := decT) (lam := lam) e (by omega)
    have := hl (by simp; omega); have := hr (by simp; omega)
    simp only [liftCompEmpty, atomicCompDescBits, e2eCDescUB]; omega
  | iter _ e _ hb | findM _ e _ hb | anyM _ e _ hb | mapM _ e _ hb =>
    simp only [cdepth] at h
    have := liftExpr_descBits_le (Pt := Pt) (C := C) (K := K) (Dh := Dh) (encPt := encPt)
      (encT := encT) (decT := decT) (lam := lam) e (by omega)
    have := hb (by simp; omega)
    simp only [liftCompEmpty, atomicCompDescBits, e2eCDescUB]; omega
  | consumeFirstM _ l _ mk hp =>
    simp only [cdepth] at h
    have := liftExpr_descBits_le (Pt := Pt) (C := C) (K := K) (Dh := Dh) (encPt := encPt)
      (encT := encT) (decT := decT) (lam := lam) l (by omega)
    have := hp (by simp; omega)
    have := liftExpr_descBits_le (Pt := Pt) (C := C) (K := K) (Dh := Dh) (encPt := encPt)
      (encT := encT) (decT := decT) (lam := lam) mk (by simp; omega)
    simp only [liftCompEmpty, atomicCompDescBits, e2eCDescUB]; omega
  | foldM _ l z _ hf =>
    simp only [cdepth] at h
    have := liftExpr_descBits_le (Pt := Pt) (C := C) (K := K) (Dh := Dh) (encPt := encPt)
      (encT := encT) (decT := decT) (lam := lam) l (by omega)
    have := liftExpr_descBits_le (Pt := Pt) (C := C) (K := K) (Dh := Dh) (encPt := encPt)
      (encT := encT) (decT := decT) (lam := lam) z (by omega)
    have := hf (by simp; omega)
    simp only [liftCompEmpty, atomicCompDescBits, e2eCDescUB]; omega

private theorem bits_c0 : bits 0 = 1 := bits_zero
private theorem bits_c1 : bits 1 = 1 := bits_eq_of_bounds (by omega) (by omega) (by omega) (by omega)
private theorem bits_c2 : bits 2 = 2 := bits_eq_of_bounds (by omega) (by omega) (by omega) (by omega)
private theorem bits_c3 : bits 3 = 2 := bits_eq_of_bounds (by omega) (by omega) (by omega) (by omega)
private theorem bits_c4 : bits 4 = 3 := bits_eq_of_bounds (by omega) (by omega) (by omega) (by omega)
private theorem bits_c5 : bits 5 = 3 := bits_eq_of_bounds (by omega) (by omega) (by omega) (by omega)
private theorem bits_c8 : bits 8 = 4 := bits_eq_of_bounds (by omega) (by omega) (by omega) (by omega)
private theorem bits_c10 : bits 10 = 4 := bits_eq_of_bounds (by omega) (by omega) (by omega) (by omega)
private theorem bits_c11 : bits 11 = 4 := bits_eq_of_bounds (by omega) (by omega) (by omega) (by omega)
private theorem bits_c12 : bits 12 = 4 := bits_eq_of_bounds (by omega) (by omega) (by omega) (by omega)
private theorem bits_c16 : bits 16 = 5 := bits_eq_of_bounds (by omega) (by omega) (by omega) (by omega)
private theorem bits_c32 : bits 32 = 6 := bits_eq_of_bounds (by omega) (by omega) (by omega) (by omega)
private theorem bits_c35 : bits 35 = 6 := bits_eq_of_bounds (by omega) (by omega) (by omega) (by omega)
private theorem bits_c36 : bits 36 = 6 := bits_eq_of_bounds (by omega) (by omega) (by omega) (by omega)
private theorem bits_c64 : bits 64 = 7 := bits_eq_of_bounds (by omega) (by omega) (by omega) (by omega)
private theorem bits_c1568 : bits 1568 = 11 := bits_eq_of_bounds (by omega) (by omega) (by omega) (by omega)
private theorem bits_c2000 : bits 2000 = 11 := bits_eq_of_bounds (by omega) (by omega) (by omega) (by omega)
private theorem bits_c2201 : bits 2201 = 12 := bits_eq_of_bounds (by omega) (by omega) (by omega) (by omega)
private theorem bits_c3168 : bits 3168 = 12 := bits_eq_of_bounds (by omega) (by omega) (by omega) (by omega)
private theorem bits_c4201 : bits 4201 = 13 := bits_eq_of_bounds (by omega) (by omega) (by omega) (by omega)
private theorem bits_c25000 : bits 25000 = 15 := bits_eq_of_bounds (by omega) (by omega) (by omega) (by omega)
private theorem bits_p32 : bits ((32 : ℕ+) : ℕ) = 6 := bits_c32
private theorem bits_p35 : bits ((35 : ℕ+) : ℕ) = 6 := bits_c35

attribute [local simp] e2eSortDescBits bits_c0 bits_c1 bits_c2 bits_c3 bits_c4 bits_c5 bits_c8
  bits_c10 bits_c11 bits_c12 bits_c16 bits_c32 bits_c35 bits_c36 bits_c64 bits_c1568 bits_c2000
  bits_c2201 bits_c3168 bits_c4201 bits_c25000 bits_p32 bits_p35

@[local simp] private theorem edepth_v0 {S0 : Sig} {O : Ops S0} {Γ : List (Ty S0)} {t : Ty S0} :
    edepth (Expr.v0 (O := O) (Γ := Γ) (t := t)) = 0 := rfl
@[local simp] private theorem edepth_v1 {S0 : Sig} {O : Ops S0} {Γ : List (Ty S0)} {t a : Ty S0} :
    edepth (Expr.v1 (O := O) (Γ := Γ) (t := t) (a := a)) = 0 := rfl
@[local simp] private theorem edepth_v2 {S0 : Sig} {O : Ops S0} {Γ : List (Ty S0)} {t a b : Ty S0} :
    edepth (Expr.v2 (O := O) (Γ := Γ) (t := t) (a := a) (b := b)) = 0 := rfl
@[local simp] private theorem edepth_v3 {S0 : Sig} {O : Ops S0} {Γ : List (Ty S0)} {t a b c : Ty S0} :
    edepth (Expr.v3 (O := O) (Γ := Γ) (t := t) (a := a) (b := b) (c := c)) = 0 := rfl
@[local simp] private theorem edepth_v4 {S0 : Sig} {O : Ops S0} {Γ : List (Ty S0)} {t a b c d : Ty S0} :
    edepth (Expr.v4 (O := O) (Γ := Γ) (t := t) (a := a) (b := b) (c := c) (d := d)) = 0 := rfl
@[local simp] private theorem edepth_v5 {S0 : Sig} {O : Ops S0} {Γ : List (Ty S0)} {t a b c d e : Ty S0} :
    edepth (Expr.v5 (O := O) (Γ := Γ) (t := t) (a := a) (b := b) (c := c) (d := d) (e := e)) = 0 := rfl
@[local simp] private theorem edepth_v6 {S0 : Sig} {O : Ops S0} {Γ : List (Ty S0)} {t a b c d e f : Ty S0} :
    edepth (Expr.v6 (O := O) (Γ := Γ) (t := t) (a := a) (b := b) (c := c) (d := d) (e := e) (f := f)) = 0 := rfl

@[local simp] private theorem edesc_v0 {ℓ : ℕ} {Pt : Type} {P : SignalPqxdh.Primitives}
    {C : Crypto} {K : MlKem} {decT : PublicKey → Option Pt} {encT : Pt → PublicKey}
    {Γ : List (Ty (e2eSig ℓ))} {t : Ty (e2eSig ℓ)} :
    e2eEDescUB (Pt := Pt) (Expr.v0 (O := e2eOps ℓ P C K decT encT) (Γ := Γ) (t := t)) = 22 := rfl
@[local simp] private theorem edesc_v1 {ℓ : ℕ} {Pt : Type} {P : SignalPqxdh.Primitives}
    {C : Crypto} {K : MlKem} {decT : PublicKey → Option Pt} {encT : Pt → PublicKey}
    {Γ : List (Ty (e2eSig ℓ))} {t a : Ty (e2eSig ℓ)} :
    e2eEDescUB (Pt := Pt) (Expr.v1 (O := e2eOps ℓ P C K decT encT) (Γ := Γ) (t := t) (a := a)) = 22 := rfl
@[local simp] private theorem edesc_v2 {ℓ : ℕ} {Pt : Type} {P : SignalPqxdh.Primitives}
    {C : Crypto} {K : MlKem} {decT : PublicKey → Option Pt} {encT : Pt → PublicKey}
    {Γ : List (Ty (e2eSig ℓ))} {t a b : Ty (e2eSig ℓ)} :
    e2eEDescUB (Pt := Pt) (Expr.v2 (O := e2eOps ℓ P C K decT encT) (Γ := Γ) (t := t) (a := a) (b := b)) = 22 := rfl
@[local simp] private theorem edesc_v3 {ℓ : ℕ} {Pt : Type} {P : SignalPqxdh.Primitives}
    {C : Crypto} {K : MlKem} {decT : PublicKey → Option Pt} {encT : Pt → PublicKey}
    {Γ : List (Ty (e2eSig ℓ))} {t a b c : Ty (e2eSig ℓ)} :
    e2eEDescUB (Pt := Pt) (Expr.v3 (O := e2eOps ℓ P C K decT encT) (Γ := Γ) (t := t) (a := a) (b := b) (c := c)) = 22 := rfl
@[local simp] private theorem edesc_v4 {ℓ : ℕ} {Pt : Type} {P : SignalPqxdh.Primitives}
    {C : Crypto} {K : MlKem} {decT : PublicKey → Option Pt} {encT : Pt → PublicKey}
    {Γ : List (Ty (e2eSig ℓ))} {t a b c d : Ty (e2eSig ℓ)} :
    e2eEDescUB (Pt := Pt) (Expr.v4 (O := e2eOps ℓ P C K decT encT) (Γ := Γ) (t := t) (a := a) (b := b) (c := c) (d := d)) = 22 := rfl
@[local simp] private theorem edesc_v5 {ℓ : ℕ} {Pt : Type} {P : SignalPqxdh.Primitives}
    {C : Crypto} {K : MlKem} {decT : PublicKey → Option Pt} {encT : Pt → PublicKey}
    {Γ : List (Ty (e2eSig ℓ))} {t a b c d e : Ty (e2eSig ℓ)} :
    e2eEDescUB (Pt := Pt) (Expr.v5 (O := e2eOps ℓ P C K decT encT) (Γ := Γ) (t := t) (a := a) (b := b) (c := c) (d := d) (e := e)) = 22 := rfl
@[local simp] private theorem edesc_v6 {ℓ : ℕ} {Pt : Type} {P : SignalPqxdh.Primitives}
    {C : Crypto} {K : MlKem} {decT : PublicKey → Option Pt} {encT : Pt → PublicKey}
    {Γ : List (Ty (e2eSig ℓ))} {t a b c d e f : Ty (e2eSig ℓ)} :
    e2eEDescUB (Pt := Pt) (Expr.v6 (O := e2eOps ℓ P C K decT encT) (Γ := Γ) (t := t) (a := a) (b := b) (c := c) (d := d) (e := e) (f := f)) = 22 := rfl

@[local simp] private theorem edepth_e2ePureOp {ℓ : ℕ} {Pt : Type} {P : SignalPqxdh.Primitives}
    {C : Crypto} {K : MlKem} {decT : PublicKey → Option Pt} {encT : Pt → PublicKey}
    {Γ : List (Ty (e2eSig ℓ))} (o : E2EPureOp)
    (a : Expr (e2eOps ℓ P C K decT encT) Γ (o.dom ℓ)) :
    edepth (e2ePureOp o a) = edepth a := rfl
@[local simp] private theorem edesc_e2ePureOp {ℓ : ℕ} {Pt : Type} {P : SignalPqxdh.Primitives}
    {C : Crypto} {K : MlKem} {decT : PublicKey → Option Pt} {encT : Pt → PublicKey}
    {Γ : List (Ty (e2eSig ℓ))} (o : E2EPureOp)
    (a : Expr (e2eOps ℓ P C K decT encT) Γ (o.dom ℓ)) :
    e2eEDescUB (Pt := Pt) (e2ePureOp o a) = (e2ePureOpDescBits o + 4) + e2eEDescUB (Pt := Pt) a + 6 := rfl
@[local simp] private theorem edepth_e2eCryptoOp {ℓ : ℕ} {Pt : Type} {P : SignalPqxdh.Primitives}
    {C : Crypto} {K : MlKem} {decT : PublicKey → Option Pt} {encT : Pt → PublicKey}
    {Γ : List (Ty (e2eSig ℓ))} (o : E2ECryptoOp)
    (a : Expr (e2eOps ℓ P C K decT encT) Γ (o.dom ℓ)) :
    edepth (e2eCryptoOp o a) = edepth a := rfl
@[local simp] private theorem edesc_e2eCryptoOp {ℓ : ℕ} {Pt : Type} {P : SignalPqxdh.Primitives}
    {C : Crypto} {K : MlKem} {decT : PublicKey → Option Pt} {encT : Pt → PublicKey}
    {Γ : List (Ty (e2eSig ℓ))} (o : E2ECryptoOp)
    (a : Expr (e2eOps ℓ P C K decT encT) Γ (o.dom ℓ)) :
    e2eEDescUB (Pt := Pt) (e2eCryptoOp o a) = 200 + e2eEDescUB (Pt := Pt) a + 6 := rfl

private def edepthHide {S0 : Sig} {O : Ops S0} {Γ : List (Ty S0)} {t : Ty S0}
    (e : Expr O Γ t) (ub : ℕ) : ℕ := min (edepth e) ub
private def cdepthHide {S0 : Sig} {O : Ops S0} {ι : Type} {T : OracleSpec ι} {I : Iface S0 T}
    {Γ : List (Ty S0)} {t : Ty S0} (c : Comp O I Γ t) (ub : ℕ) : ℕ := min (cdepth c) ub
private def e2eEDescHide {ℓ : ℕ} {Pt : Type} {P : SignalPqxdh.Primitives} {C : Crypto} {K : MlKem}
    {decT : PublicKey → Option Pt} {encT : Pt → PublicKey}
    {Γ : List (Ty (e2eSig ℓ))} {t : Ty (e2eSig ℓ)}
    (e : Expr (e2eOps ℓ P C K decT encT) Γ t) (ub : ℕ) : ℕ := min (e2eEDescUB (Pt := Pt) e) ub
private def e2eCDescHide {ℓ : ℕ} {Pt : Type} {P : SignalPqxdh.Primitives} {C : Crypto} {K : MlKem}
    {decT : PublicKey → Option Pt} {encT : Pt → PublicKey}
    {ι : Type} {T : OracleSpec ι} {I : Iface (e2eSig ℓ) T}
    {Γ : List (Ty (e2eSig ℓ))} {t : Ty (e2eSig ℓ)}
    (c : Comp (e2eOps ℓ P C K decT encT) I Γ t) (ub : ℕ) : ℕ := min (e2eCDescUB (Pt := Pt) c) ub

private theorem edepth_eq_hide {S0 : Sig} {O : Ops S0} {Γ : List (Ty S0)} {t : Ty S0}
    {e : Expr O Γ t} {ub : ℕ} (h : edepth e ≤ ub) : edepth e = edepthHide e ub :=
  (Nat.min_eq_left h).symm
private theorem cdepth_eq_hide {S0 : Sig} {O : Ops S0} {ι : Type} {T : OracleSpec ι}
    {I : Iface S0 T} {Γ : List (Ty S0)} {t : Ty S0} {c : Comp O I Γ t} {ub : ℕ}
    (h : cdepth c ≤ ub) : cdepth c = cdepthHide c ub :=
  (Nat.min_eq_left h).symm
private theorem edesc_eq_hide {ℓ : ℕ} {Pt : Type} {P : SignalPqxdh.Primitives} {C : Crypto}
    {K : MlKem} {decT : PublicKey → Option Pt} {encT : Pt → PublicKey}
    {Γ : List (Ty (e2eSig ℓ))} {t : Ty (e2eSig ℓ)}
    {e : Expr (e2eOps ℓ P C K decT encT) Γ t} {ub : ℕ} (h : e2eEDescUB (Pt := Pt) e ≤ ub) :
    e2eEDescUB (Pt := Pt) e = e2eEDescHide (Pt := Pt) e ub :=
  (Nat.min_eq_left h).symm
private theorem cdesc_eq_hide {ℓ : ℕ} {Pt : Type} {P : SignalPqxdh.Primitives} {C : Crypto}
    {K : MlKem} {decT : PublicKey → Option Pt} {encT : Pt → PublicKey}
    {ι : Type} {T : OracleSpec ι} {I : Iface (e2eSig ℓ) T}
    {Γ : List (Ty (e2eSig ℓ))} {t : Ty (e2eSig ℓ)}
    {c : Comp (e2eOps ℓ P C K decT encT) I Γ t} {ub : ℕ} (h : e2eCDescUB (Pt := Pt) c ≤ ub) :
    e2eCDescUB (Pt := Pt) c = e2eCDescHide (Pt := Pt) c ub :=
  (Nat.min_eq_left h).symm
private theorem cdepthHide_def {S0 : Sig} {O : Ops S0} {ι : Type} {T : OracleSpec ι}
    {I : Iface S0 T} {Γ : List (Ty S0)} {t : Ty S0} (c : Comp O I Γ t) (ub : ℕ) :
    cdepthHide c ub = min (cdepth c) ub := rfl
private theorem e2eCDescHide_def {ℓ : ℕ} {Pt : Type} {P : SignalPqxdh.Primitives} {C : Crypto}
    {K : MlKem} {decT : PublicKey → Option Pt} {encT : Pt → PublicKey}
    {ι : Type} {T : OracleSpec ι} {I : Iface (e2eSig ℓ) T}
    {Γ : List (Ty (e2eSig ℓ))} {t : Ty (e2eSig ℓ)}
    (c : Comp (e2eOps ℓ P C K decT encT) I Γ t) (ub : ℕ) :
    e2eCDescHide (Pt := Pt) c ub = min (e2eCDescUB (Pt := Pt) c) ub := rfl

open Computational.Proofs.E2E.Dsl.SpqrSimSend (spqrRunSendChainComp spqrSendComp)
open Computational.Proofs.E2E.Dsl.SpqrSimRecv (spqrPreambleT spqrRecvGreaterComp
  spqrRecvPrepStateComp spqrRunRecvChainComp spqrRecvV1BodyComp spqrRecvComp)

section SpqrSimBounds
set_option linter.unusedSimpArgs false
set_option maxRecDepth 8192
attribute [local irreducible] edepthHide cdepthHide e2eEDescHide e2eCDescHide

open Computational.Proofs.E2E.Dsl.SpqrSimChain (spqrNegotiateInitC spqrBraidSendC spqrBraidRecvC
  spqrChainFromVnC spqrChainAddEpochC spqrChainNextKeyC listDropExpr listGetExpr listSetExpr
  spqrEpochIdxExpr spqrResolveChainComp spqrAddEpochOptComp clearLinkSendNextExpr
  linksClearSendPrefixExpr spqrChainSendKeyComp)
open Computational.Proofs.E2E.Dsl.SpqrSimHist (spqrListRevExpr spqrPrevGetFuelExpr spqrPrevGetExpr
  spqrPrevGcFuelExpr spqrPrevGcExpr spqrCatchAccT spqrKeyAdvanceStep spqrKeyAdvanceFuelComp
  spqrKeyAdvanceComp spqrDirKeyFwdComp spqrDirKeyComp spqrChainRecvKeyComp)

variable {ℓ : ℕ} {Pt : Type} {P : SignalPqxdh.Primitives} {C : Crypto} {K : MlKem}
  {decT : PublicKey → Option Pt} {encT : Pt → PublicKey}
  {ι : Type} {T : OracleSpec ι} (I : Iface (e2eSig ℓ) T)

@[local simp] private theorem cdepth_spqrNegotiateInitC {Γ} (a) :
    cdepth (spqrNegotiateInitC (P := P) (C := C) (K := K) (decT := decT) (encT := encT)
      I (Γ := Γ) a) = edepth a := rfl
@[local simp] private theorem cdesc_spqrNegotiateInitC {Γ} (a) :
    e2eCDescUB (Pt := Pt) (spqrNegotiateInitC (P := P) (C := C) (K := K) (decT := decT)
      (encT := encT) I (Γ := Γ) a) = e2eEDescUB (Pt := Pt) a + 212 := by
  simp [spqrNegotiateInitC]; omega
@[local simp] private theorem cdepth_spqrBraidSendC {Γ} (a) :
    cdepth (spqrBraidSendC (P := P) (C := C) (K := K) (decT := decT) (encT := encT)
      I (Γ := Γ) a) = edepth a := rfl
@[local simp] private theorem cdesc_spqrBraidSendC {Γ} (a) :
    e2eCDescUB (Pt := Pt) (spqrBraidSendC (P := P) (C := C) (K := K) (decT := decT)
      (encT := encT) I (Γ := Γ) a) = e2eEDescUB (Pt := Pt) a + 212 := by
  simp [spqrBraidSendC]; omega
@[local simp] private theorem cdepth_spqrBraidRecvC {Γ} (a) :
    cdepth (spqrBraidRecvC (P := P) (C := C) (K := K) (decT := decT) (encT := encT)
      I (Γ := Γ) a) = edepth a := rfl
@[local simp] private theorem cdesc_spqrBraidRecvC {Γ} (a) :
    e2eCDescUB (Pt := Pt) (spqrBraidRecvC (P := P) (C := C) (K := K) (decT := decT)
      (encT := encT) I (Γ := Γ) a) = e2eEDescUB (Pt := Pt) a + 212 := by
  simp [spqrBraidRecvC]; omega
@[local simp] private theorem cdepth_spqrChainFromVnC {Γ} (a) :
    cdepth (spqrChainFromVnC (P := P) (C := C) (K := K) (decT := decT) (encT := encT)
      I (Γ := Γ) a) = edepth a := rfl
@[local simp] private theorem cdesc_spqrChainFromVnC {Γ} (a) :
    e2eCDescUB (Pt := Pt) (spqrChainFromVnC (P := P) (C := C) (K := K) (decT := decT)
      (encT := encT) I (Γ := Γ) a) = e2eEDescUB (Pt := Pt) a + 212 := by
  simp [spqrChainFromVnC]; omega
@[local simp] private theorem cdepth_spqrChainAddEpochC {Γ} (a) :
    cdepth (spqrChainAddEpochC (P := P) (C := C) (K := K) (decT := decT) (encT := encT)
      I (Γ := Γ) a) = edepth a := rfl
@[local simp] private theorem cdesc_spqrChainAddEpochC {Γ} (a) :
    e2eCDescUB (Pt := Pt) (spqrChainAddEpochC (P := P) (C := C) (K := K) (decT := decT)
      (encT := encT) I (Γ := Γ) a) = e2eEDescUB (Pt := Pt) a + 212 := by
  simp [spqrChainAddEpochC]; omega
@[local simp] private theorem cdepth_spqrChainNextKeyC {Γ} (a) :
    cdepth (spqrChainNextKeyC (P := P) (C := C) (K := K) (decT := decT) (encT := encT)
      I (Γ := Γ) a) = edepth a := rfl
@[local simp] private theorem cdesc_spqrChainNextKeyC {Γ} (a) :
    e2eCDescUB (Pt := Pt) (spqrChainNextKeyC (P := P) (C := C) (K := K) (decT := decT)
      (encT := encT) I (Γ := Γ) a) = e2eEDescUB (Pt := Pt) a + 212 := by
  simp [spqrChainNextKeyC]; omega

private theorem clearLinkSendNextExpr_ub {Γ}
    (lk : Expr (e2eOps ℓ P C K decT encT) Γ spqrEpochLinkT) :
    edepth (clearLinkSendNextExpr lk) ≤ edepth lk + 3 ∧
    e2eEDescUB (Pt := Pt) (clearLinkSendNextExpr lk) ≤ e2eEDescUB (Pt := Pt) lk + 500 := by
  refine ⟨by simp [clearLinkSendNextExpr], ?_⟩
  simp [clearLinkSendNextExpr, spqrDirT, spqrPrevEntryT, CryptoVerification.E2E.Costed.B,
    CryptoVerification.E2E.Costed.U32, CryptoVerification.E2E.Costed.BV256]

@[local simp] private theorem edepth_clearLink_eq {Γ}
    (lk : Expr (e2eOps ℓ P C K decT encT) Γ spqrEpochLinkT) :
    edepth (clearLinkSendNextExpr lk) = edepthHide (clearLinkSendNextExpr lk) (edepth lk + 3) :=
  edepth_eq_hide (clearLinkSendNextExpr_ub (Pt := Pt) lk).1
@[local simp] private theorem edesc_clearLink_eq {Γ}
    (lk : Expr (e2eOps ℓ P C K decT encT) Γ spqrEpochLinkT) :
    e2eEDescUB (Pt := Pt) (clearLinkSendNextExpr lk) =
      e2eEDescHide (Pt := Pt) (clearLinkSendNextExpr lk) (e2eEDescUB (Pt := Pt) lk + 500) :=
  edesc_eq_hide (clearLinkSendNextExpr_ub (Pt := Pt) lk).2

private theorem spqrChainSendKeyComp_ub {Γ}
    (ch : Expr (e2eOps ℓ P C K decT encT) Γ spqrChainT)
    (epoch : Expr (e2eOps ℓ P C K decT encT) Γ U64) :
    cdepth (spqrChainSendKeyComp I ch epoch) ≤ edepth ch + edepth epoch + 16 ∧
    e2eCDescUB (Pt := Pt) (spqrChainSendKeyComp I ch epoch) ≤
      e2eEDescUB (Pt := Pt) ch + e2eEDescUB (Pt := Pt) epoch + 10000 := by
  refine ⟨?_, ?_⟩
  · simp [spqrChainSendKeyComp, spqrEpochIdxExpr, linksClearSendPrefixExpr,
      listDropExpr, listGetExpr, listSetExpr]
    unfold edepthHide; omega
  · simp [spqrChainSendKeyComp, spqrEpochIdxExpr, linksClearSendPrefixExpr,
      listDropExpr, listGetExpr, listSetExpr, spqrChainT, spqrEpochLinkT, spqrDirT,
      spqrPrevEntryT, spqrParamsT, CryptoVerification.E2E.Costed.B,
      CryptoVerification.E2E.Costed.U32, CryptoVerification.E2E.Costed.U64,
      CryptoVerification.E2E.Costed.BV256]
    unfold e2eEDescHide; omega

@[local simp] private theorem cdepth_spqrChainSendKeyComp_eq {Γ}
    (ch : Expr (e2eOps ℓ P C K decT encT) Γ spqrChainT)
    (epoch : Expr (e2eOps ℓ P C K decT encT) Γ U64) :
    cdepth (spqrChainSendKeyComp I ch epoch) =
      cdepthHide (spqrChainSendKeyComp I ch epoch) (edepth ch + edepth epoch + 16) :=
  cdepth_eq_hide (spqrChainSendKeyComp_ub (Pt := Pt) I ch epoch).1
@[local simp] private theorem cdesc_spqrChainSendKeyComp_eq {Γ}
    (ch : Expr (e2eOps ℓ P C K decT encT) Γ spqrChainT)
    (epoch : Expr (e2eOps ℓ P C K decT encT) Γ U64) :
    e2eCDescUB (Pt := Pt) (spqrChainSendKeyComp I ch epoch) =
      e2eCDescHide (Pt := Pt) (spqrChainSendKeyComp I ch epoch)
        (e2eEDescUB (Pt := Pt) ch + e2eEDescUB (Pt := Pt) epoch + 10000) :=
  cdesc_eq_hide (spqrChainSendKeyComp_ub (Pt := Pt) I ch epoch).2

private theorem spqrListRevExpr_ub {Γ} {t : Ty (e2eSig ℓ)} (cap : ℕ)
    (dflt : Expr (e2eOps ℓ P C K decT encT) Γ t)
    (l : Expr (e2eOps ℓ P C K decT encT) Γ (.list t)) :
    edepth (spqrListRevExpr cap dflt l) ≤ edepth dflt + edepth l + 8 ∧
    e2eEDescUB (Pt := Pt) (spqrListRevExpr cap dflt l) ≤
      e2eEDescUB (Pt := Pt) dflt + e2eEDescUB (Pt := Pt) l +
        e2eTyDescBits t + 6 * bits cap + 900 := by
  refine ⟨by simp [spqrListRevExpr]; omega, by simp [spqrListRevExpr]; omega⟩

@[local simp] private theorem edepth_spqrListRevExpr_eq {Γ} {t : Ty (e2eSig ℓ)} (cap : ℕ)
    (dflt : Expr (e2eOps ℓ P C K decT encT) Γ t)
    (l : Expr (e2eOps ℓ P C K decT encT) Γ (.list t)) :
    edepth (spqrListRevExpr cap dflt l) =
      edepthHide (spqrListRevExpr cap dflt l) (edepth dflt + edepth l + 8) :=
  edepth_eq_hide (spqrListRevExpr_ub (Pt := Pt) cap dflt l).1
@[local simp] private theorem edesc_spqrListRevExpr_eq {Γ} {t : Ty (e2eSig ℓ)} (cap : ℕ)
    (dflt : Expr (e2eOps ℓ P C K decT encT) Γ t)
    (l : Expr (e2eOps ℓ P C K decT encT) Γ (.list t)) :
    e2eEDescUB (Pt := Pt) (spqrListRevExpr cap dflt l) =
      e2eEDescHide (Pt := Pt) (spqrListRevExpr cap dflt l)
        (e2eEDescUB (Pt := Pt) dflt + e2eEDescUB (Pt := Pt) l +
          e2eTyDescBits t + 6 * bits cap + 900) :=
  edesc_eq_hide (spqrListRevExpr_ub (Pt := Pt) cap dflt l).2

private theorem spqrPrevGetExpr_ub {Γ}
    (entries : Expr (e2eOps ℓ P C K decT encT) Γ (.list spqrPrevEntryT))
    (tail : Expr (e2eOps ℓ P C K decT encT) Γ (CryptoVerification.E2E.Costed.B 35))
    (atIdx curCtr maxOoo : Expr (e2eOps ℓ P C K decT encT) Γ U32) :
    edepth (spqrPrevGetExpr entries tail atIdx curCtr maxOoo) ≤
      edepth entries + edepth tail + edepth atIdx + edepth curCtr + edepth maxOoo + 12 ∧
    e2eEDescUB (Pt := Pt) (spqrPrevGetExpr entries tail atIdx curCtr maxOoo) ≤
      e2eEDescUB (Pt := Pt) entries + e2eEDescUB (Pt := Pt) tail + e2eEDescUB (Pt := Pt) atIdx +
        e2eEDescUB (Pt := Pt) curCtr + e2eEDescUB (Pt := Pt) maxOoo + 4500 := by
  refine ⟨?_, ?_⟩
  · simp [spqrPrevGetExpr, spqrPrevGetFuelExpr, listGetExpr, listSetExpr]; omega
  · simp [spqrPrevGetExpr, spqrPrevGetFuelExpr, listGetExpr, listSetExpr, spqrPrevEntryT,
      CryptoVerification.E2E.Costed.U32, CryptoVerification.E2E.Costed.BV256]; omega

@[local simp] private theorem edepth_spqrPrevGetExpr_eq {Γ}
    (entries : Expr (e2eOps ℓ P C K decT encT) Γ (.list spqrPrevEntryT))
    (tail : Expr (e2eOps ℓ P C K decT encT) Γ (CryptoVerification.E2E.Costed.B 35))
    (atIdx curCtr maxOoo : Expr (e2eOps ℓ P C K decT encT) Γ U32) :
    edepth (spqrPrevGetExpr entries tail atIdx curCtr maxOoo) =
      edepthHide (spqrPrevGetExpr entries tail atIdx curCtr maxOoo)
        (edepth entries + edepth tail + edepth atIdx + edepth curCtr + edepth maxOoo + 12) :=
  edepth_eq_hide (spqrPrevGetExpr_ub (Pt := Pt) entries tail atIdx curCtr maxOoo).1
@[local simp] private theorem edesc_spqrPrevGetExpr_eq {Γ}
    (entries : Expr (e2eOps ℓ P C K decT encT) Γ (.list spqrPrevEntryT))
    (tail : Expr (e2eOps ℓ P C K decT encT) Γ (CryptoVerification.E2E.Costed.B 35))
    (atIdx curCtr maxOoo : Expr (e2eOps ℓ P C K decT encT) Γ U32) :
    e2eEDescUB (Pt := Pt) (spqrPrevGetExpr entries tail atIdx curCtr maxOoo) =
      e2eEDescHide (Pt := Pt) (spqrPrevGetExpr entries tail atIdx curCtr maxOoo)
        (e2eEDescUB (Pt := Pt) entries + e2eEDescUB (Pt := Pt) tail + e2eEDescUB (Pt := Pt) atIdx +
          e2eEDescUB (Pt := Pt) curCtr + e2eEDescUB (Pt := Pt) maxOoo + 4500) :=
  edesc_eq_hide (spqrPrevGetExpr_ub (Pt := Pt) entries tail atIdx curCtr maxOoo).2

private theorem spqrPrevGcExpr_ub {Γ}
    (entries : Expr (e2eOps ℓ P C K decT encT) Γ (.list spqrPrevEntryT))
    (curKey maxOoo : Expr (e2eOps ℓ P C K decT encT) Γ U32)
    (trimSize : Expr (e2eOps ℓ P C K decT encT) Γ .nat) :
    edepth (spqrPrevGcExpr entries curKey maxOoo trimSize) ≤
      edepth entries + edepth curKey + edepth maxOoo + edepth trimSize + 14 ∧
    e2eEDescUB (Pt := Pt) (spqrPrevGcExpr entries curKey maxOoo trimSize) ≤
      e2eEDescUB (Pt := Pt) entries + e2eEDescUB (Pt := Pt) curKey +
        e2eEDescUB (Pt := Pt) maxOoo + e2eEDescUB (Pt := Pt) trimSize + 5000 := by
  refine ⟨by simp [spqrPrevGcExpr, spqrPrevGcFuelExpr]; omega, ?_⟩
  simp [spqrPrevGcExpr, spqrPrevGcFuelExpr, spqrPrevEntryT,
    CryptoVerification.E2E.Costed.U32, CryptoVerification.E2E.Costed.BV256]; omega

@[local simp] private theorem edepth_spqrPrevGcExpr_eq {Γ}
    (entries : Expr (e2eOps ℓ P C K decT encT) Γ (.list spqrPrevEntryT))
    (curKey maxOoo : Expr (e2eOps ℓ P C K decT encT) Γ U32)
    (trimSize : Expr (e2eOps ℓ P C K decT encT) Γ .nat) :
    edepth (spqrPrevGcExpr entries curKey maxOoo trimSize) =
      edepthHide (spqrPrevGcExpr entries curKey maxOoo trimSize)
        (edepth entries + edepth curKey + edepth maxOoo + edepth trimSize + 14) :=
  edepth_eq_hide (spqrPrevGcExpr_ub (Pt := Pt) entries curKey maxOoo trimSize).1
@[local simp] private theorem edesc_spqrPrevGcExpr_eq {Γ}
    (entries : Expr (e2eOps ℓ P C K decT encT) Γ (.list spqrPrevEntryT))
    (curKey maxOoo : Expr (e2eOps ℓ P C K decT encT) Γ U32)
    (trimSize : Expr (e2eOps ℓ P C K decT encT) Γ .nat) :
    e2eEDescUB (Pt := Pt) (spqrPrevGcExpr entries curKey maxOoo trimSize) =
      e2eEDescHide (Pt := Pt) (spqrPrevGcExpr entries curKey maxOoo trimSize)
        (e2eEDescUB (Pt := Pt) entries + e2eEDescUB (Pt := Pt) curKey +
          e2eEDescUB (Pt := Pt) maxOoo + e2eEDescUB (Pt := Pt) trimSize + 5000) :=
  edesc_eq_hide (spqrPrevGcExpr_ub (Pt := Pt) entries curKey maxOoo trimSize).2

private theorem spqrKeyAdvanceComp_ub {Γ}
    (ctr0 : Expr (e2eOps ℓ P C K decT encT) Γ U32)
    (next0 : Expr (e2eOps ℓ P C K decT encT) Γ (CryptoVerification.E2E.Costed.B 32))
    (entries0 : Expr (e2eOps ℓ P C K decT encT) Γ (.list spqrPrevEntryT))
    (atIdx maxOoo : Expr (e2eOps ℓ P C K decT encT) Γ U32) :
    cdepth (spqrKeyAdvanceComp I ctr0 next0 entries0 atIdx maxOoo) ≤
      edepth ctr0 + edepth next0 + edepth entries0 + edepth atIdx + edepth maxOoo + 14 ∧
    e2eCDescUB (Pt := Pt) (spqrKeyAdvanceComp I ctr0 next0 entries0 atIdx maxOoo) ≤
      e2eEDescUB (Pt := Pt) ctr0 + e2eEDescUB (Pt := Pt) next0 + e2eEDescUB (Pt := Pt) entries0 +
        e2eEDescUB (Pt := Pt) atIdx + e2eEDescUB (Pt := Pt) maxOoo + 6000 := by
  refine ⟨?_, ?_⟩
  · simp [spqrKeyAdvanceComp, spqrKeyAdvanceFuelComp, spqrKeyAdvanceStep]
    unfold edepthHide; omega
  · simp [spqrKeyAdvanceComp, spqrKeyAdvanceFuelComp, spqrKeyAdvanceStep,
      spqrCatchAccT, spqrPrevEntryT, CryptoVerification.E2E.Costed.B,
      CryptoVerification.E2E.Costed.U32, CryptoVerification.E2E.Costed.BV256]
    unfold e2eEDescHide; omega

@[local simp] private theorem cdepth_spqrKeyAdvanceComp_eq {Γ}
    (ctr0 : Expr (e2eOps ℓ P C K decT encT) Γ U32)
    (next0 : Expr (e2eOps ℓ P C K decT encT) Γ (CryptoVerification.E2E.Costed.B 32))
    (entries0 : Expr (e2eOps ℓ P C K decT encT) Γ (.list spqrPrevEntryT))
    (atIdx maxOoo : Expr (e2eOps ℓ P C K decT encT) Γ U32) :
    cdepth (spqrKeyAdvanceComp I ctr0 next0 entries0 atIdx maxOoo) =
      cdepthHide (spqrKeyAdvanceComp I ctr0 next0 entries0 atIdx maxOoo)
        (edepth ctr0 + edepth next0 + edepth entries0 + edepth atIdx + edepth maxOoo + 14) :=
  cdepth_eq_hide (spqrKeyAdvanceComp_ub (Pt := Pt) I ctr0 next0 entries0 atIdx maxOoo).1
@[local simp] private theorem cdesc_spqrKeyAdvanceComp_eq {Γ}
    (ctr0 : Expr (e2eOps ℓ P C K decT encT) Γ U32)
    (next0 : Expr (e2eOps ℓ P C K decT encT) Γ (CryptoVerification.E2E.Costed.B 32))
    (entries0 : Expr (e2eOps ℓ P C K decT encT) Γ (.list spqrPrevEntryT))
    (atIdx maxOoo : Expr (e2eOps ℓ P C K decT encT) Γ U32) :
    e2eCDescUB (Pt := Pt) (spqrKeyAdvanceComp I ctr0 next0 entries0 atIdx maxOoo) =
      e2eCDescHide (Pt := Pt) (spqrKeyAdvanceComp I ctr0 next0 entries0 atIdx maxOoo)
        (e2eEDescUB (Pt := Pt) ctr0 + e2eEDescUB (Pt := Pt) next0 + e2eEDescUB (Pt := Pt) entries0 +
          e2eEDescUB (Pt := Pt) atIdx + e2eEDescUB (Pt := Pt) maxOoo + 6000) :=
  cdesc_eq_hide (spqrKeyAdvanceComp_ub (Pt := Pt) I ctr0 next0 entries0 atIdx maxOoo).2

private theorem spqrDirKeyComp_ub {Γ}
    (recvDir : Expr (e2eOps ℓ P C K decT encT) Γ spqrDirT)
    (atIdx maxJump maxOoo : Expr (e2eOps ℓ P C K decT encT) Γ U32)
    (trimSize : Expr (e2eOps ℓ P C K decT encT) Γ .nat) :
    cdepth (spqrDirKeyComp I recvDir atIdx maxJump maxOoo trimSize) ≤
      edepth recvDir + edepth atIdx + edepth maxJump + edepth maxOoo + edepth trimSize + 22 ∧
    e2eCDescUB (Pt := Pt) (spqrDirKeyComp I recvDir atIdx maxJump maxOoo trimSize) ≤
      e2eEDescUB (Pt := Pt) recvDir + e2eEDescUB (Pt := Pt) atIdx + e2eEDescUB (Pt := Pt) maxJump +
        e2eEDescUB (Pt := Pt) maxOoo + e2eEDescUB (Pt := Pt) trimSize + 20000 := by
  refine ⟨?_, ?_⟩
  · simp [spqrDirKeyComp, spqrDirKeyFwdComp]
    unfold edepthHide cdepthHide; omega
  · simp [spqrDirKeyComp, spqrDirKeyFwdComp, spqrCatchAccT, spqrDirT, spqrPrevEntryT,
      CryptoVerification.E2E.Costed.B, CryptoVerification.E2E.Costed.U32,
      CryptoVerification.E2E.Costed.BV256]
    unfold e2eEDescHide e2eCDescHide; omega

@[local simp] private theorem cdepth_spqrDirKeyComp_eq {Γ}
    (recvDir : Expr (e2eOps ℓ P C K decT encT) Γ spqrDirT)
    (atIdx maxJump maxOoo : Expr (e2eOps ℓ P C K decT encT) Γ U32)
    (trimSize : Expr (e2eOps ℓ P C K decT encT) Γ .nat) :
    cdepth (spqrDirKeyComp I recvDir atIdx maxJump maxOoo trimSize) =
      cdepthHide (spqrDirKeyComp I recvDir atIdx maxJump maxOoo trimSize)
        (edepth recvDir + edepth atIdx + edepth maxJump + edepth maxOoo + edepth trimSize + 22) :=
  cdepth_eq_hide (spqrDirKeyComp_ub (Pt := Pt) I recvDir atIdx maxJump maxOoo trimSize).1
@[local simp] private theorem cdesc_spqrDirKeyComp_eq {Γ}
    (recvDir : Expr (e2eOps ℓ P C K decT encT) Γ spqrDirT)
    (atIdx maxJump maxOoo : Expr (e2eOps ℓ P C K decT encT) Γ U32)
    (trimSize : Expr (e2eOps ℓ P C K decT encT) Γ .nat) :
    e2eCDescUB (Pt := Pt) (spqrDirKeyComp I recvDir atIdx maxJump maxOoo trimSize) =
      e2eCDescHide (Pt := Pt) (spqrDirKeyComp I recvDir atIdx maxJump maxOoo trimSize)
        (e2eEDescUB (Pt := Pt) recvDir + e2eEDescUB (Pt := Pt) atIdx + e2eEDescUB (Pt := Pt) maxJump +
          e2eEDescUB (Pt := Pt) maxOoo + e2eEDescUB (Pt := Pt) trimSize + 20000) :=
  cdesc_eq_hide (spqrDirKeyComp_ub (Pt := Pt) I recvDir atIdx maxJump maxOoo trimSize).2

private theorem spqrChainRecvKeyComp_ub {Γ}
    (ch : Expr (e2eOps ℓ P C K decT encT) Γ spqrChainT)
    (epoch : Expr (e2eOps ℓ P C K decT encT) Γ U64)
    (index : Expr (e2eOps ℓ P C K decT encT) Γ U32) :
    cdepth (spqrChainRecvKeyComp I ch epoch index) ≤
      edepth ch + edepth epoch + edepth index + 32 ∧
    e2eCDescUB (Pt := Pt) (spqrChainRecvKeyComp I ch epoch index) ≤
      e2eEDescUB (Pt := Pt) ch + e2eEDescUB (Pt := Pt) epoch + e2eEDescUB (Pt := Pt) index + 28000 := by
  refine ⟨?_, ?_⟩
  · simp [spqrChainRecvKeyComp, spqrEpochIdxExpr, listGetExpr, listSetExpr]
    simp only [cdepthHide_def]; omega
  · simp [spqrChainRecvKeyComp, spqrEpochIdxExpr, listGetExpr, listSetExpr,
      spqrChainT, spqrEpochLinkT, spqrDirT, spqrPrevEntryT, spqrParamsT,
      CryptoVerification.E2E.Costed.B, CryptoVerification.E2E.Costed.U32,
      CryptoVerification.E2E.Costed.U64, CryptoVerification.E2E.Costed.BV256]
    simp only [e2eCDescHide_def]; omega

@[local simp] private theorem cdepth_spqrChainRecvKeyComp_eq {Γ}
    (ch : Expr (e2eOps ℓ P C K decT encT) Γ spqrChainT)
    (epoch : Expr (e2eOps ℓ P C K decT encT) Γ U64)
    (index : Expr (e2eOps ℓ P C K decT encT) Γ U32) :
    cdepth (spqrChainRecvKeyComp I ch epoch index) =
      cdepthHide (spqrChainRecvKeyComp I ch epoch index)
        (edepth ch + edepth epoch + edepth index + 32) :=
  cdepth_eq_hide (spqrChainRecvKeyComp_ub (Pt := Pt) I ch epoch index).1
@[local simp] private theorem cdesc_spqrChainRecvKeyComp_eq {Γ}
    (ch : Expr (e2eOps ℓ P C K decT encT) Γ spqrChainT)
    (epoch : Expr (e2eOps ℓ P C K decT encT) Γ U64)
    (index : Expr (e2eOps ℓ P C K decT encT) Γ U32) :
    e2eCDescUB (Pt := Pt) (spqrChainRecvKeyComp I ch epoch index) =
      e2eCDescHide (Pt := Pt) (spqrChainRecvKeyComp I ch epoch index)
        (e2eEDescUB (Pt := Pt) ch + e2eEDescUB (Pt := Pt) epoch + e2eEDescUB (Pt := Pt) index + 28000) :=
  cdesc_eq_hide (spqrChainRecvKeyComp_ub (Pt := Pt) I ch epoch index).2

private theorem spqrSendComp_ub {Γ}
    (e : Expr (e2eOps ℓ P C K decT encT) Γ
      (.prod (CryptoVerification.E2E.Costed.B 32) CryptoVerification.E2E.Costed.BV512)) :
    cdepth (spqrSendComp I e) ≤ edepth e + 28 ∧
    e2eCDescUB (Pt := Pt) (spqrSendComp I e) ≤ e2eEDescUB (Pt := Pt) e + 18000 := by
  refine ⟨?_, ?_⟩
  · simp [spqrSendComp, spqrRunSendChainComp, spqrResolveChainComp, spqrAddEpochOptComp]
    simp only [cdepthHide_def]; omega
  · simp [spqrSendComp, spqrRunSendChainComp, spqrResolveChainComp, spqrAddEpochOptComp,
      spqrChainT, spqrEpochLinkT, spqrDirT, spqrPrevEntryT, spqrParamsT,
      CryptoVerification.E2E.Costed.B, CryptoVerification.E2E.Costed.U32,
      CryptoVerification.E2E.Costed.U64, CryptoVerification.E2E.Costed.BV256]
    simp only [e2eCDescHide_def]; omega

private theorem spqrRecvComp_ub {Γ}
    (e : Expr (e2eOps ℓ P C K decT encT) Γ
      (.prod (CryptoVerification.E2E.Costed.B 32) (CryptoVerification.E2E.Costed.B 32))) :
    cdepth (spqrRecvComp I e) ≤ edepth e + 55 ∧
    e2eCDescUB (Pt := Pt) (spqrRecvComp I e) ≤ e2eEDescUB (Pt := Pt) e + 75000 := by
  refine ⟨?_, ?_⟩
  · simp [spqrRecvComp, spqrRecvGreaterComp, spqrRecvPrepStateComp, spqrRecvV1BodyComp,
      spqrRunRecvChainComp, spqrResolveChainComp, spqrAddEpochOptComp]
    simp only [cdepthHide_def]; omega
  · simp [spqrRecvComp, spqrRecvGreaterComp, spqrRecvPrepStateComp, spqrRecvV1BodyComp,
      spqrRunRecvChainComp, spqrResolveChainComp, spqrAddEpochOptComp,
      spqrStatePartsT, spqrVnT, spqrChainT, spqrEpochLinkT, spqrDirT, spqrPrevEntryT,
      spqrParamsT, spqrPreambleT, CryptoVerification.E2E.Costed.B,
      CryptoVerification.E2E.Costed.U8, CryptoVerification.E2E.Costed.U32,
      CryptoVerification.E2E.Costed.U64, CryptoVerification.E2E.Costed.BV256]
    simp only [e2eCDescHide_def]; omega

end SpqrSimBounds

theorem spqrSendAtomicC_descBits_le {ℓ : ℕ} {Pt : Type} [DecidableEq Pt] [Zero Pt]
    {C : Crypto} {K : MlKem} {Dh : DHFun (BitVec 256) Pt} {encPt : Pt → Bytes}
    {encT : Pt → PublicKey} {decT : PublicKey → Option Pt} {lam : Pt}
    {ι : Type} {T : OracleSpec ι} (I' : Iface (atomicSig ℓ Pt) T)
    (sB : I'.smp.Samp → ℕ) (qB : I'.Tag → ℕ)
    {Γ : List (Ty (atomicSig ℓ Pt))}
    (inpE : Expr (atomicSessionOps ℓ Pt C K Dh encPt encT decT lam) Γ (.prod (B 32) BV512)) :
    atomicCompDescBits atomicSessionOpDescBits sB qB
      (spqrSendAtomicC (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT)
        (decT := decT) (lam := lam) I' inpE) ≤
      atomicExprDescBits atomicSessionOpDescBits inpE + 25000 := by
  let v0E : Expr (e2eOps ℓ zeroPqxdhPrims C K decT encT)
      [.prod (CryptoVerification.E2E.Costed.B 32) CryptoVerification.E2E.Costed.BV512]
      (.prod (CryptoVerification.E2E.Costed.B 32) CryptoVerification.E2E.Costed.BV512) := .v0
  have hub := spqrSendComp_ub (Pt := Pt) (P := zeroPqxdhPrims) (C := C) (K := K)
    (decT := decT) (encT := encT) (emptyE2EIface I') v0E
  have hd0 : edepth v0E = 0 := rfl
  have he0 : e2eEDescUB (Pt := Pt) v0E = 22 := rfl
  have hlift := liftCompEmpty_descBits_le (Pt := Pt) (C := C) (K := K) (Dh := Dh)
    (encPt := encPt) (encT := encT) (decT := decT) (lam := lam) sB qB
    (spqrSendComp (P := zeroPqxdhPrims) (C := C) (K := K) (decT := decT) (encT := encT)
      (emptyE2EIface I') v0E)
    (by dsimp only [List.length_cons, List.length_nil]; omega)
  dsimp only [v0E] at hub hlift hd0 he0
  dsimp only [spqrSendAtomicC, atomicCompDescBits]
  rw [wk1Comp_descBits_eq]
  omega

theorem spqrRecvAtomicC_descBits_le {ℓ : ℕ} {Pt : Type} [DecidableEq Pt] [Zero Pt]
    {C : Crypto} {K : MlKem} {Dh : DHFun (BitVec 256) Pt} {encPt : Pt → Bytes}
    {encT : Pt → PublicKey} {decT : PublicKey → Option Pt} {lam : Pt}
    {ι : Type} {T : OracleSpec ι} (I' : Iface (atomicSig ℓ Pt) T)
    (sB : I'.smp.Samp → ℕ) (qB : I'.Tag → ℕ)
    {Γ : List (Ty (atomicSig ℓ Pt))}
    (inpE : Expr (atomicSessionOps ℓ Pt C K Dh encPt encT decT lam) Γ (.prod (B 32) (B 32))) :
    atomicCompDescBits atomicSessionOpDescBits sB qB
      (spqrRecvAtomicC (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT)
        (decT := decT) (lam := lam) I' inpE) ≤
      atomicExprDescBits atomicSessionOpDescBits inpE + 90000 := by
  let v0E : Expr (e2eOps ℓ zeroPqxdhPrims C K decT encT)
      [.prod (CryptoVerification.E2E.Costed.B 32) (CryptoVerification.E2E.Costed.B 32)]
      (.prod (CryptoVerification.E2E.Costed.B 32) (CryptoVerification.E2E.Costed.B 32)) := .v0
  have hub := spqrRecvComp_ub (Pt := Pt) (P := zeroPqxdhPrims) (C := C) (K := K)
    (decT := decT) (encT := encT) (emptyE2EIface I') v0E
  have hd0 : edepth v0E = 0 := rfl
  have he0 : e2eEDescUB (Pt := Pt) v0E = 22 := rfl
  have hlift := liftCompEmpty_descBits_le (Pt := Pt) (C := C) (K := K) (Dh := Dh)
    (encPt := encPt) (encT := encT) (decT := decT) (lam := lam) sB qB
    (spqrRecvComp (P := zeroPqxdhPrims) (C := C) (K := K) (decT := decT) (encT := encT)
      (emptyE2EIface I') v0E)
    (by dsimp only [List.length_cons, List.length_nil]; omega)
  dsimp only [v0E] at hub hlift hd0 he0
  dsimp only [spqrRecvAtomicC, atomicCompDescBits]
  rw [wk1Comp_descBits_eq]
  omega

end SpqrDescBridge

/-! ## `DescBits` bounds for `Fig8Atomic` primitives -/

section Fig8DescBits
set_option linter.unusedSimpArgs false

variable {ℓ : ℕ} {Pt : Type} [DecidableEq Pt] [Zero Pt]
  {C : Crypto} {Dh : DHFun (BitVec 256) Pt}
  {encPt : Pt → Bytes} {encT : Pt → PublicKey} {lam : Pt}

local notation "ASig" => atomicSig ℓ Pt
local notation "FOps" => atomicFig8Ops ℓ Pt C Dh encPt encT lam
local notation "FDesc" => atomicFig8OpDescBits (ℓ := ℓ) (Pt := Pt) (C := C) (Dh := Dh)
  (encPt := encPt) (encT := encT) (lam := lam)

@[local simp] private theorem fb_c0 : bits 0 = 1 := bits_zero
@[local simp] private theorem fb_c1 : bits 1 = 1 :=
  bits_eq_of_bounds (by omega) (by omega) (by omega) (by omega)
@[local simp] private theorem fb_c2 : bits 2 = 2 :=
  bits_eq_of_bounds (by omega) (by omega) (by omega) (by omega)
@[local simp] private theorem fb_c3 : bits 3 = 2 :=
  bits_eq_of_bounds (by omega) (by omega) (by omega) (by omega)
@[local simp] private theorem fb_c4 : bits 4 = 3 :=
  bits_eq_of_bounds (by omega) (by omega) (by omega) (by omega)
@[local simp] private theorem fb_c8 : bits 8 = 4 :=
  bits_eq_of_bounds (by omega) (by omega) (by omega) (by omega)
@[local simp] private theorem fb_c32 : bits 32 = 6 :=
  bits_eq_of_bounds (by omega) (by omega) (by omega) (by omega)
@[local simp] private theorem fb_p1 : bits ((1 : ℕ+) : ℕ) = 1 := fb_c1
@[local simp] private theorem fb_p8 : bits ((8 : ℕ+) : ℕ) = 4 := fb_c8
@[local simp] private theorem fb_p32 : bits ((32 : ℕ+) : ℕ) = 6 := fb_c32
@[local simp] private theorem fb_c25000 : bits 25000 = 15 :=
  bits_eq_of_bounds (by omega) (by omega) (by omega) (by omega)
@[local simp] private theorem fb_mfj : bits maxForwardJumps = 15 := fb_c25000

@[local simp] private theorem fdesc_opPure {Γ : List (Ty ASig)} (o : AtomicPureOp)
    (a : Expr FOps Γ (o.dom ℓ Pt)) :
    atomicExprDescBits FDesc (opPure ℓ Pt C Dh encPt encT lam o a) =
      (atomicPureOpDescBits o + 4) + atomicExprDescBits FDesc a + 6 := rfl

@[local simp] private theorem fdesc_opPtEncPk {Γ : List (Ty ASig)} (a : Expr FOps Γ PtT) :
    atomicExprDescBits FDesc (opPtEncPk ℓ Pt C Dh encPt encT lam a) =
      13 + atomicExprDescBits FDesc a + 6 := rfl

@[local simp] private theorem fdesc_opSym {Γ : List (Ty ASig)} (o : AtomicSymOp)
    (a : Expr FOps Γ (o.dom ℓ Pt)) :
    atomicExprDescBits FDesc (opSym ℓ Pt C Dh encPt encT lam o a) =
      (atomicSymOpDescBits o + 5) + atomicExprDescBits FDesc a + 6 := rfl

@[local simp] private theorem fdesc_opGrp {Γ : List (Ty ASig)} (o : AtomicGroupOp)
    (a : Expr FOps Γ (o.dom ℓ Pt)) :
    atomicExprDescBits FDesc (opGrp ℓ Pt C Dh encPt encT lam o a) =
      11 + atomicExprDescBits FDesc a + 6 := rfl

@[local simp] private theorem pdesc_u8Lit (x : BitVec 8) :
    atomicPureOpDescBits (.u8Lit x) = 16 := rfl
@[local simp] private theorem pdesc_u32Lit (x : BitVec 32) :
    atomicPureOpDescBits (.u32Lit x) = 40 := rfl
@[local simp] private theorem pdesc_u64Lit (x : BitVec 64) :
    atomicPureOpDescBits (.u64Lit x) = 72 := rfl
@[local simp] private theorem pdesc_bv256Lit (x : BitVec 256) :
    atomicPureOpDescBits (.bv256Lit x) = 264 := rfl
@[local simp] private theorem pdesc_bytesLit (w : ℕ+) (v : Bytes) :
    atomicPureOpDescBits (.bytesLit w v) =
      8 * v.length + 2 * bits v.length + 2 * bits (w : ℕ) + 8 := rfl
@[local simp] private theorem pdesc_pbytesLit (w : ℕ+) (v : SignalPqxdh.Bytes) :
    atomicPureOpDescBits (.pbytesLit w v) =
      8 * v.length + 2 * bits v.length + 2 * bits (w : ℕ) + 8 := rfl

theorem pkLitExpr_descBits_le {Γ : List (Ty ASig)} (pk : PublicKey) :
    atomicExprDescBits FDesc
      (pkLitExpr ℓ Pt C Dh encPt encT lam (Γ := Γ) pk) ≤ 350 := by
  have hlen : (vecU8 pk.bytes).length = 32 := by simp [vecU8, toU8]
  dsimp only [pkLitExpr]
  simp only [atomicExprDescBits, atomicPureOpDescBits, fdesc_opPure, pdesc_pbytesLit,
    hlen, fb_c32, fb_p32]
  omega

theorem optBytesEqExpr_descBits_le {Γ : List (Ty ASig)} (x y : Expr FOps Γ (.opt (B 32))) :
    atomicExprDescBits FDesc
      (optBytesEqExpr ℓ Pt C Dh encPt encT lam x y) ≤
      atomicExprDescBits FDesc x + 3 * atomicExprDescBits FDesc y + 120 := by
  dsimp only [optBytesEqExpr]
  have hy := rename_descBits_le_mul FDesc 1
    (Γ₂ := B 32 :: Γ) (fun ⦃_⦄ v => Var.succ v) y (fun _ _ => le_rfl)
  simp only [atomicExprDescBits, atomicPureOpDescBits, fdesc_opPure, varIdx, Nat.reduceAdd,
    fb_c0, fb_c1, fb_c32, fb_p32]
  omega

theorem optPtEqExpr_descBits_le {Γ : List (Ty ASig)} (x y : Expr FOps Γ (.opt PtT)) :
    atomicExprDescBits FDesc
      (optPtEqExpr ℓ Pt C Dh encPt encT lam x y) ≤
      atomicExprDescBits FDesc x + 3 * atomicExprDescBits FDesc y + 100 := by
  dsimp only [optPtEqExpr]
  have hy := rename_descBits_le_mul FDesc 1
    (Γ₂ := PtT :: Γ) (fun ⦃_⦄ v => Var.succ v) y (fun _ _ => le_rfl)
  simp only [atomicExprDescBits, fdesc_opGrp, varIdx, Nat.reduceAdd, fb_c0, fb_c1]
  omega

theorem lPubOfExpr_descBits_le {Γ : List (Ty ASig)} (cV : Expr FOps Γ wireSaltCtT) :
    atomicExprDescBits FDesc
      (lPubOfExpr ℓ Pt C Dh encPt encT lam cV) ≤
      atomicExprDescBits FDesc cV + 400 := by
  simp only [lPubOfExpr, lpubT, B, U32, BV256,
    atomicExprDescBits, atomicTyDescBits, atomicSortDescBits, atomicPureOpDescBits,
    fdesc_opPure, pdesc_bytesLit,
    varIdx, Nat.reduceAdd, List.length_replicate, List.length_nil,
    fb_c0, fb_c1, fb_c8, fb_c32, fb_p8, fb_p32]
  omega

theorem chainGenExpr_descBits_le {Γ : List (Ty ASig)} (ck : Expr FOps Γ BV256) :
    atomicExprDescBits FDesc
      (chainGenExpr ℓ Pt C Dh encPt encT lam ck) ≤
      atomicExprDescBits FDesc ck + 200 := by
  simp only [chainGenExpr, atomicExprDescBits, atomicSymOpDescBits, atomicPureOpDescBits,
    fdesc_opPure, fdesc_opSym, pdesc_bytesLit,
    varIdx, Nat.reduceAdd, List.length_cons, List.length_nil, fb_c0, fb_c1, fb_c32, fb_p1, fb_p32]
  omega

theorem appAux_descBits_le {Γ : List (Ty ASig)} {a b : Ty ASig}
    (f : Expr FOps [a, .prod IdKey IdKey] b) (arg : Expr FOps Γ a)
    (vAux : Var Γ (.prod IdKey IdKey)) :
    atomicExprDescBits FDesc
      (appAux ℓ Pt C Dh encPt encT lam f arg vAux) ≤
      atomicExprDescBits FDesc arg +
        (varIdx vAux + 1) * atomicExprDescBits FDesc f + 6 := by
  dsimp only [appAux, atomicExprDescBits]
  refine Nat.add_le_add_right (Nat.add_le_add_left
    (rename_descBits_le_mul FDesc (varIdx vAux) _ f fun _ v => ?_) _) 6
  cases v with
  | zero => exact Nat.zero_le _
  | succ w =>
    cases w with
    | zero => change varIdx vAux + 1 ≤ 0 + 1 + varIdx vAux; omega
    | succ z => nomatch z

theorem unitsPowExpr_descBits_le :
    ∀ (k : ℕ) {Γ : List (Ty ASig)},
      atomicExprDescBits FDesc
        (unitsPowExpr ℓ Pt C Dh encPt encT lam (Γ := Γ) k) ≤ k * k + 40 * k + 30
  | 0, _ => by
    simp only [unitsPowExpr, atomicExprDescBits, atomicTyDescBits]; omega
  | k + 1, Γ => by
    have ih := unitsPowExpr_descBits_le k (Γ := Γ)
    have hpow : bits (2 ^ (k + 1)) ≤ k + 2 :=
      bits_le_of_lt_pow (by omega) (Nat.pow_lt_pow_right (by omega) (by omega))
    have hsq : (k + 1) * (k + 1) = k * k + 2 * k + 1 := by ring
    simp only [unitsPowExpr, atomicExprDescBits, varIdx, fb_c0]; omega

theorem aeadEncExpr_descBits_le :
    atomicExprDescBits FDesc (aeadEncExpr ℓ Pt C Dh encPt encT lam) ≤ 2100 := by
  have hpk := pkLitExpr_descBits_le (ℓ := ℓ) (Pt := Pt) (C := C) (Dh := Dh) (encPt := encPt)
    (encT := encT) (lam := lam)
    (Γ := [.prod BV256 (.prod BV256 (.prod BV128 U32)),
           .prod BV256 (.prod (.prod (.prod .nat fig8HdrT) lpubT) PlainT),
           .prod IdKey IdKey]) dummyKey
  simp only [aeadEncExpr, atomicExprDescBits, atomicSymOpDescBits, atomicPureOpDescBits,
    fdesc_opPure, fdesc_opPtEncPk, fdesc_opSym, pdesc_u8Lit, pdesc_u32Lit,
    varIdx, Nat.reduceAdd, fb_c0, fb_c1, fb_c2, fb_c8, fb_c32, fb_p8, fb_p32]
  omega

theorem aeadDecExpr_descBits_le :
    atomicExprDescBits FDesc (aeadDecExpr ℓ Pt C Dh encPt encT lam) ≤ 3000 := by
  have hpk := pkLitExpr_descBits_le (ℓ := ℓ) (Pt := Pt) (C := C) (Dh := Dh) (encPt := encPt)
    (encT := encT) (lam := lam)
    (Γ := [.prod BV256 (.prod BV256 (.prod BV128 U32)),
           signalParsedT,
           .prod BV256 (.prod (.prod (.prod .nat fig8HdrT) lpubT) wireSaltCtT),
           .prod IdKey IdKey]) dummyKey
  have hopt := optBytesEqExpr_descBits_le (ℓ := ℓ) (Pt := Pt) (C := C) (Dh := Dh)
    (encPt := encPt) (encT := encT) (lam := lam)
    (Γ := [.prod BV256 (.prod BV256 (.prod BV128 U32)),
           signalParsedT,
           .prod BV256 (.prod (.prod (.prod .nat fig8HdrT) lpubT) wireSaltCtT),
           .prod IdKey IdKey])
    (.snd (.snd (.snd (.var (.succ .zero)))))
    (.snd (.snd (.snd (.snd (.fst (.snd (.var (.succ (.succ .zero)))))))))
  simp only [atomicExprDescBits, varIdx, Nat.reduceAdd, fb_c1, fb_c2] at hopt
  simp only [aeadDecExpr, PlainT, atomicExprDescBits, atomicTyDescBits, atomicSortDescBits,
    atomicSymOpDescBits, atomicPureOpDescBits,
    fdesc_opPure, fdesc_opPtEncPk, fdesc_opSym, pdesc_u8Lit, pdesc_u32Lit, pdesc_bytesLit,
    varIdx, Nat.reduceAdd, List.length_replicate,
    List.length_nil, fb_c0, fb_c1, fb_c2, fb_c3, fb_c8, fb_c32, fb_p8, fb_p32]
  omega

theorem lctEqBody_descBits_le {Γ : List (Ty ASig)} (c1 c2 : Expr FOps Γ lctT) :
    atomicExprDescBits FDesc (lctEqBody ℓ Pt C Dh encPt encT lam c1 c2) ≤
      4 * atomicExprDescBits FDesc c1 + 4 * atomicExprDescBits FDesc c2 + 250 := by
  simp only [lctEqBody, atomicExprDescBits, atomicPureOpDescBits, fdesc_opPure, fb_c32, fb_p32]
  omega

theorem fsInitSendExpr_descBits_le :
    atomicExprDescBits FDesc (fsInitSendExpr ℓ Pt C Dh encPt encT lam) ≤ 40 := by
  simp only [fsInitSendExpr, atomicExprDescBits, varIdx, fb_c0]; omega

theorem fsInitRecvExpr_descBits_le :
    atomicExprDescBits FDesc (fsInitRecvExpr ℓ Pt C Dh encPt encT lam) ≤ 60 := by
  simp only [fsInitRecvExpr, BV256, atomicExprDescBits, atomicTyDescBits, atomicSortDescBits,
    varIdx, fb_c0]
  omega

theorem fsSendExpr_descBits_le :
    atomicExprDescBits FDesc (fsSendExpr ℓ Pt C Dh encPt encT lam) ≤ 7500 := by
  have hcg := chainGenExpr_descBits_le (ℓ := ℓ) (Pt := Pt) (C := C) (Dh := Dh) (encPt := encPt)
    (encT := encT) (lam := lam)
    (Γ := [.prod fsSendStT (.prod fig8HdrT (.prod lpubT PlainT)), .prod IdKey IdKey])
    (.fst (.fst (.var .zero)))
  have hae := aeadEncExpr_descBits_le (ℓ := ℓ) (Pt := Pt) (C := C) (Dh := Dh) (encPt := encPt)
    (encT := encT) (lam := lam)
  let vArg1 : Expr FOps [.prod BV256 BV256, .prod fsSendStT (.prod fig8HdrT (.prod lpubT PlainT)),
    .prod IdKey IdKey] _ := Expr.var (.succ .zero)
  let i1 := Expr.add (.snd (.fst vArg1)) (.nat 1)
  let encArg := Expr.pair (.snd (.var .zero))
    (.pair (.pair (.pair i1 (.fst (.snd vArg1))) (.fst (.snd (.snd vArg1))))
      (.snd (.snd (.snd vArg1))))
  have happ := appAux_descBits_le (ℓ := ℓ) (Pt := Pt) (C := C) (Dh := Dh) (encPt := encPt)
    (encT := encT) (lam := lam) (aeadEncExpr ℓ Pt C Dh encPt encT lam) encArg (.succ (.succ .zero))
  simp only [encArg, i1, vArg1, atomicExprDescBits, varIdx, Nat.reduceAdd, fb_c0, fb_c1] at hcg happ
  dsimp only [fsSendExpr]
  simp only [atomicExprDescBits, varIdx, Nat.reduceAdd, fb_c0, fb_c1]
  omega

theorem fsRecvExpr_descBits_le (B0 Bmax : ℕ) :
    atomicExprDescBits FDesc (fsRecvExpr ℓ Pt C Dh encPt encT lam B0 Bmax) ≤
      6 * bits B0 + 4 * bits Bmax + 16000 := by
  let inT : Ty ASig := .prod fsRecvStT (.prod fig8HdrT lctT)
  let Γ₀ : List (Ty ASig) := [inT, .prod IdKey IdKey]
  let Γ₁ : List (Ty ASig) := [lpubT, inT, .prod IdKey IdKey]
  have hlpub := lPubOfExpr_descBits_le (ℓ := ℓ) (Pt := Pt) (C := C) (Dh := Dh) (encPt := encPt)
    (encT := encT) (lam := lam) (Γ := Γ₀) (.snd (.snd (.snd (.var .zero))))
  have hpow := unitsPowExpr_descBits_le (ℓ := ℓ) (Pt := Pt) (C := C) (Dh := Dh) (encPt := encPt)
    (encT := encT) (lam := lam) 15 (Γ := Γ₁)
  have hcg1 := chainGenExpr_descBits_le (ℓ := ℓ) (Pt := Pt) (C := C) (Dh := Dh) (encPt := encPt)
    (encT := encT) (lam := lam) (Γ := .unit :: fsRecvStT :: Γ₁) (.fst (.var (.succ .zero)))
  have hcg2 := chainGenExpr_descBits_le (ℓ := ℓ) (Pt := Pt) (C := C) (Dh := Dh) (encPt := encPt)
    (encT := encT) (lam := lam) (Γ := fsRecvStT :: Γ₁) (.fst (.var .zero))
  have hadec := aeadDecExpr_descBits_le (ℓ := ℓ) (Pt := Pt) (C := C) (Dh := Dh) (encPt := encPt)
    (encT := encT) (lam := lam)
  let vIn2 : Expr FOps (.prod BV256 fsRecvStT :: Γ₁) inT := .var (.succ (.succ .zero))
  let decArg := Expr.pair (.fst (.var .zero))
    (.pair (.pair (.pair (.fst (.snd (.snd vIn2))) (.fst (.snd vIn2))) (.var (.succ .zero)))
      (.snd (.snd (.snd vIn2))))
  have happ := appAux_descBits_le (ℓ := ℓ) (Pt := Pt) (C := C) (Dh := Dh) (encPt := encPt)
    (encT := encT) (lam := lam) (aeadDecExpr ℓ Pt C Dh encPt encT lam) decArg
    (.succ (.succ (.succ .zero)))
  simp only [decArg, vIn2, atomicExprDescBits, varIdx, Nat.reduceAdd,
    fb_c0, fb_c1, fb_c2] at hlpub hcg1 hcg2 happ
  dsimp only [fsRecvExpr]
  simp only [fsRecvStT, lpubT, PlainT, B, U32, BV256,
    atomicExprDescBits, atomicTyDescBits, atomicSortDescBits, varIdx, Nat.reduceAdd,
    fb_c0, fb_c1, fb_c2, fb_c3, fb_c4, fb_c32, fb_p32, fb_mfj]
  omega

theorem ckaInitAExpr_descBits_le :
    atomicExprDescBits FDesc (ckaInitAExpr ℓ Pt C Dh encPt encT lam) ≤ 80 := by
  simp only [ckaInitAExpr, BV256, atomicExprDescBits, atomicTyDescBits, atomicSortDescBits,
    fdesc_opGrp, varIdx, fb_c0]
  omega

theorem ckaInitBExpr_descBits_le :
    atomicExprDescBits FDesc (ckaInitBExpr ℓ Pt C Dh encPt encT lam) ≤ 40 := by
  simp only [ckaInitBExpr, PtT, atomicExprDescBits, atomicTyDescBits, atomicSortDescBits,
    fdesc_opGrp, varIdx, fb_c0]
  omega

theorem ckaSendExpr_descBits_le :
    atomicExprDescBits FDesc (ckaSendExpr ℓ Pt C Dh encPt encT lam) ≤ 300 := by
  simp only [ckaSendExpr, PtT, BV256, atomicExprDescBits, atomicTyDescBits, atomicSortDescBits,
    fdesc_opGrp, varIdx, Nat.reduceAdd, fb_c0, fb_c1]
  omega

theorem ckaRecvExpr_descBits_le :
    atomicExprDescBits FDesc (ckaRecvExpr ℓ Pt C Dh encPt encT lam) ≤ 200 := by
  simp only [ckaRecvExpr, PtT, BV256, atomicExprDescBits, atomicTyDescBits, atomicSortDescBits,
    fdesc_opGrp, varIdx, Nat.reduceAdd, fb_c0, fb_c1]
  omega

theorem prngInitExpr_descBits_le :
    atomicExprDescBits FDesc (prngInitExpr ℓ Pt C Dh encPt encT lam) ≤ 20 := by
  simp only [prngInitExpr, atomicExprDescBits, varIdx, fb_c0]; omega

theorem prngUpExpr_descBits_le :
    atomicExprDescBits FDesc (prngUpExpr ℓ Pt C Dh encPt encT lam) ≤ 80 := by
  simp only [prngUpExpr, atomicExprDescBits, fdesc_opGrp, varIdx, fb_c0]; omega

theorem lamIExpr_descBits_le :
    atomicExprDescBits FDesc (lamIExpr ℓ Pt C Dh encPt encT lam) ≤ 40 := by
  simp only [lamIExpr, atomicExprDescBits, fdesc_opGrp]; omega

theorem defaultEExpr_descBits_le :
    atomicExprDescBits FDesc (defaultEExpr ℓ Pt C Dh encPt encT lam) ≤ 450 := by
  simp only [defaultEExpr, atomicExprDescBits, fdesc_opPure, pdesc_bytesLit, pdesc_u64Lit,
    pdesc_bv256Lit, List.length_nil, fb_c0, fb_c32, fb_p32]
  omega

theorem eqPtExpr_descBits_le :
    atomicExprDescBits FDesc (eqPtExpr ℓ Pt C Dh encPt encT lam) ≤ 40 := by
  simp only [eqPtExpr, atomicExprDescBits, fdesc_opGrp, varIdx, fb_c0]; omega

theorem smEqCtExpr_descBits_le :
    atomicExprDescBits FDesc (smEqCtExpr ℓ Pt C Dh encPt encT lam) ≤ 800 := by
  have h1 := optPtEqExpr_descBits_le (ℓ := ℓ) (Pt := Pt) (C := C) (Dh := Dh) (encPt := encPt)
    (encT := encT) (lam := lam) (Γ := [.prod fig8CtT fig8CtT, .prod IdKey IdKey])
    (.snd (.fst (.fst (.var .zero)))) (.snd (.fst (.snd (.var .zero))))
  have h2 := lctEqBody_descBits_le (ℓ := ℓ) (Pt := Pt) (C := C) (Dh := Dh) (encPt := encPt)
    (encT := encT) (lam := lam) (Γ := [.prod fig8CtT fig8CtT, .prod IdKey IdKey])
    (.snd (.fst (.var .zero))) (.snd (.snd (.var .zero)))
  simp only [atomicExprDescBits, varIdx, fb_c0] at h1 h2
  dsimp only [smEqCtExpr]
  simp only [atomicExprDescBits, varIdx, fb_c0]
  omega

end Fig8DescBits

end Computational.Proofs.Game.PromotedCostedReds.SimFig8SpqrDesc
