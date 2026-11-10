/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Computational.Proofs.SignalPqxdh.Security.ReductionDsl.KeyInd1KeyGapDh
public import Computational.Proofs.SignalPqxdh.Security.ReductionDsl.KeyIndGapDhProofs
public import Computational.Proofs.ReductionDsl.GRedBoundedOfBounds
import Computational.Proofs.ReductionDsl.Size

/-!
# Cost, Block-Size, and Query Bounds for `fgKeyInd1KeyGapDhProg`

**Checked by Lean.** Proves syntactic step-cost, program-size, output block-size, and query-count
bounds for `fgKeyInd1KeyGapDhProg` and `fgKeyInd1KeyGapDh2Prog`, together with `IsQueryBoundP`
soundness bridges.
-/

@[expose] public section

set_option autoImplicit false

open SignalPqxdh SignalPqxdh.Security SignalPqxdh.Security.FgGapDh SignalPqxdh.Security.FgGapDh1Key
open _root_.ReductionDsl hiding B PTag U32 bundleOfV bundleT bundleV dhSecretsT drKeyOfV drKeyT drKeyV hdrOfV hdrT hdrV keyIndCodec keyIndQT keyIndQenc keyIndRT keyIndRdec keyIndRenc pqPrimIface pqSigAndDdhIface sampleIndex sidT sidV
open SignalPqxdh.LegacyCosted
open OracleSpec OracleComp

namespace SignalPqxdh.Security.ReductionDsl.KeyInd1KeyGapDh
open SignalPqxdh.Security.ReductionDsl.KeyInd
open SignalPqxdh.Security.ReductionDsl.KeyIndGapDh

section
set_option allowUnsafeReducibility true
attribute [implicit_reducible] sigAndDdhOracle gapDhDdhOracle
end

def wSig1Key : pqSigAndDdhIface.Tag → ℕ := SignalPqxdh.LegacyCosted.chalIfaceSigQueryWeight
def wDdh1Key : pqSigAndDdhIface.Tag → ℕ := SignalPqxdh.LegacyCosted.chalIfaceDdhQueryWeight
def wPrim1Key : pqSigAndDdhIface.Tag → ℕ := SignalPqxdh.LegacyCosted.chalIfacePrimQueryWeight
def wsZero1Key : pqSigAndDdhIface.smp.Samp → ℕ := SignalPqxdh.LegacyCosted.samplerZeroQueryWeight

/-! ## Cost and Query Preservation -/

@[simp] theorem renameExpr_cost :
    ∀ {Γ : List PT} {t : PT} (e : Expr pqxdhOps Γ t) {Δ : List PT} (ρ : Ren Γ Δ),
      (renameExpr ρ e).cost = e.cost := by
  intro Γ t e; induction e <;> intro Δ ρ <;> simp [renameExpr, Expr.cost, *]

@[simp] theorem renameComp_cost {ι : Type} {T : OracleSpec ι} {I : Iface pqSig T} :
    ∀ {Γ : List PT} {t : PT} (c : Comp pqxdhOps I Γ t) {Δ : List PT} (ρ : Ren Γ Δ),
      (renameComp ρ c).cost = c.cost := by
  intro Γ t c; induction c <;> intro Δ ρ <;> simp [renameComp, Comp.cost, *]

@[simp] theorem renameComp_queries {ι : Type} {T : OracleSpec ι} {I : Iface pqSig T}
    (w : I.Tag → ℕ) (ws : I.smp.Samp → ℕ) :
    ∀ {Γ : List PT} {t : PT} (c : Comp pqxdhOps I Γ t) {Δ : List PT} (ρ : Ren Γ Δ),
      (renameComp ρ c).queries w ws = c.queries w ws := by
  intro Γ t c; induction c <;> intro Δ ρ <;> simp [renameComp, Comp.queries, *]

@[simp] theorem liftGdhComp_cost :
    ∀ {Γ : List PT} {t : PT} (c : Comp pqxdhOps pqGapDhIface Γ t), (liftGdhComp c).cost = c.cost := by
  intro Γ t c; induction c with
  | query q _ => rcases q with _ | ⟨⟩ <;> rfl
  | sample _ _ => rfl
  | _ => simp_all [liftGdhComp, Comp.cost]

@[simp] theorem liftGdhComp_costUB :
    ∀ {Γ : List PT} {t : PT} (c : Comp pqxdhOps pqGapDhIface Γ t), (liftGdhComp c).costUB = c.costUB := by
  intro Γ t c; induction c with
  | query q _ => rcases q with _ | ⟨⟩ <;> rfl
  | sample _ _ => rfl
  | _ => simp_all [liftGdhComp, Comp.costUB]

@[simp] theorem renameExpr_size :
    ∀ {Γ : List PT} {t : PT} (e : Expr pqxdhOps Γ t) {Δ : List PT} (ρ : Ren Γ Δ), (renameExpr ρ e).size = e.size := by
  intro Γ t e; induction e <;> intro Δ ρ <;> simp [renameExpr, Expr.size, *]

@[simp] theorem renameComp_size {ι : Type} {T : OracleSpec ι} {I : Iface pqSig T} :
    ∀ {Γ : List PT} {t : PT} (c : Comp pqxdhOps I Γ t) {Δ : List PT} (ρ : Ren Γ Δ), (renameComp ρ c).size = c.size := by
  intro Γ t c; induction c <;> intro Δ ρ <;> simp [renameComp, Comp.size, *]

@[simp] theorem liftGdhComp_size :
    ∀ {Γ : List PT} {t : PT} (c : Comp pqxdhOps pqGapDhIface Γ t), (liftGdhComp c).size = c.size := by
  intro Γ t c; induction c with
  | query q _ => rcases q with _ | ⟨⟩ <;> rfl
  | sample _ _ => rfl
  | _ => simp_all [liftGdhComp, Comp.size]

@[simp] theorem liftGdhComp_queries_sig :
    ∀ {Γ : List PT} {t : PT} (c : Comp pqxdhOps pqGapDhIface Γ t), (liftGdhComp c).queries wSig1Key wsZero1Key = 0 := by
  intro Γ t c; induction c with
  | query q _ => rcases q with _ | ⟨⟩ <;> rfl
  | sample _ _ => rfl
  | _ => simp_all [liftGdhComp, Comp.queries]

@[simp] theorem liftGdhComp_queries_ddh :
    ∀ {Γ : List PT} {t : PT} (c : Comp pqxdhOps pqGapDhIface Γ t),
      (liftGdhComp c).queries wDdh1Key wsZero1Key = c.queries wDdhGdh wsZero := by
  intro Γ t c; induction c with
  | query q _ => rcases q with _ | ⟨⟩ <;> rfl
  | sample _ _ => rfl
  | _ => simp_all [liftGdhComp, Comp.queries]

@[simp] theorem liftGdhComp_queries_prim :
    ∀ {Γ : List PT} {t : PT} (c : Comp pqxdhOps pqGapDhIface Γ t),
      (liftGdhComp c).queries wPrim1Key wsZero1Key = c.queries wPrimGdh wsZero := by
  intro Γ t c; induction c with
  | query q _ => rcases q with _ | ⟨⟩ <;> rfl
  | sample _ _ => rfl
  | _ => simp_all [liftGdhComp, Comp.queries]

@[simp] theorem sigChalQ_dsl_costUB (m : ℕ+) {Γ : List PT} (msg : Expr pqxdhOps Γ (B m)) :
    (sigChalQ_dsl m msg).costUB = msg.costUB + (1 + m.val + 0 + 64) := rfl
@[simp] theorem sigChalQ_dsl_queries_sig (m : ℕ+) {Γ : List PT} (msg : Expr pqxdhOps Γ (B m)) :
    (sigChalQ_dsl m msg).queries wSig1Key wsZero1Key = 1 := rfl
@[simp] theorem sigChalQ_dsl_queries_ddh (m : ℕ+) {Γ : List PT} (msg : Expr pqxdhOps Γ (B m)) :
    (sigChalQ_dsl m msg).queries wDdh1Key wsZero1Key = 0 := rfl
@[simp] theorem sigChalQ_dsl_queries_prim (m : ℕ+) {Γ : List PT} (msg : Expr pqxdhOps Γ (B m)) :
    (sigChalQ_dsl m msg).queries wPrim1Key wsZero1Key = 0 := rfl
@[simp] theorem qX25519Base_queries {Γ : List PT} (e : Expr pqxdhOps Γ (B 32)) :
    (qX25519Base e).queries wPrimBase wsZeroBase = 1 := rfl
@[simp] theorem qKemKeyGen_queries {Γ : List PT} (e : Expr pqxdhOps Γ (B 64)) :
    (qKemKeyGen e).queries wPrimBase wsZeroBase = 1 := rfl

/-! ## Syntactic Query Counts -/

@[simp] theorem callGdhHandle_queries_sig (S : Setup) (K : Nat) {Δ : List PT}
    (st1 : Var Δ gdh1KeyStateTy) (q : Var Δ keyIndQueryTy) :
    (callGdhHandle S K st1 q).queries wSig1Key wsZero1Key = 0 := by simp [callGdhHandle, Comp.queries]
@[simp] theorem callGdhHandle_queries_ddh (S : Setup) (K : Nat) {Δ : List PT}
    (st1 : Var Δ gdh1KeyStateTy) (q : Var Δ keyIndQueryTy) :
    (callGdhHandle S K st1 q).queries wDdh1Key wsZero1Key = 4 * K := by
  simp [callGdhHandle, Comp.queries, gdhHandle_chalQueries]
@[simp] theorem callGdhHandle_queries_prim (S : Setup) (K : Nat) {Δ : List PT}
    (st1 : Var Δ gdh1KeyStateTy) (q : Var Δ keyIndQueryTy) :
    (callGdhHandle S K st1 q).queries wPrim1Key wsZero1Key = (gdhHandle S K).queries wPrimGdh wsZero := by
  simp [callGdhHandle, Comp.queries]

@[simp] theorem initPrin1KeyB_queries_sig (K : Nat) {Γ₁ Γ₂ Δ : List PT} [Ext Γ₁ Δ] [Ext Γ₂ Δ]
    (st1 : Var Γ₁ gdh1KeyStateTy) (u : Var Γ₂ .nat) :
    (initPrin1KeyB K (Δ := Δ) st1 u).queries wSig1Key wsZero1Key = 0 := by simp [initPrin1KeyB, Comp.queries]
@[simp] theorem initPrin1KeyB_queries_ddh (K : Nat) {Γ₁ Γ₂ Δ : List PT} [Ext Γ₁ Δ] [Ext Γ₂ Δ]
    (st1 : Var Γ₁ gdh1KeyStateTy) (u : Var Γ₂ .nat) :
    (initPrin1KeyB K (Δ := Δ) st1 u).queries wDdh1Key wsZero1Key = 0 := by simp [initPrin1KeyB, Comp.queries]
theorem initPrin1KeyB_queries_prim_le (K : Nat) {Γ₁ Γ₂ Δ : List PT} [Ext Γ₁ Δ] [Ext Γ₂ Δ]
    (st1 : Var Γ₁ gdh1KeyStateTy) (u : Var Γ₂ .nat) :
    (initPrin1KeyB K (Δ := Δ) st1 u).queries wPrim1Key wsZero1Key ≤ 1 := by simp [initPrin1KeyB, Comp.queries]

@[simp] theorem genSpk1KeyB_queries_sig (S : Setup) (K : Nat) {Δ : List PT}
    (st1 : Var Δ gdh1KeyStateTy) (q : Var Δ keyIndQueryTy) (x : Var Δ (.prod .nat .nat)) :
    (genSpk1KeyB S K st1 q x).queries wSig1Key wsZero1Key = 2 := by simp [genSpk1KeyB, Comp.queries]
@[simp] theorem genSpk1KeyB_queries_ddh (S : Setup) (K : Nat) {Δ : List PT}
    (st1 : Var Δ gdh1KeyStateTy) (q : Var Δ keyIndQueryTy) (x : Var Δ (.prod .nat .nat)) :
    (genSpk1KeyB S K st1 q x).queries wDdh1Key wsZero1Key = 4 * K := by simp [genSpk1KeyB, Comp.queries]

theorem genSpk1KeyB_queries_prim_le (S : Setup) (K : Nat) {Δ : List PT}
    (st1 : Var Δ gdh1KeyStateTy) (q : Var Δ keyIndQueryTy) (x : Var Δ (.prod .nat .nat)) :
    (genSpk1KeyB S K st1 q x).queries wPrim1Key wsZero1Key ≤ 153 + 72 * S.N_dh + 16 * S.N_sess_tot := by
  have hGdh := gdhHandle_primQueries_le S K
  simp only [genSpk1KeyB, Comp.queries, letV_queries, bindV_queries, caseOptV_queries,
    liftGdhComp_queries_prim, gPrim_queries_wPrimGdh, sigChalQ_dsl_queries_prim,
    callGdhHandle_queries_prim, sBytes32_queries, sRandom64_queries, qX25519Base_queries, qKemKeyGen_queries]
  omega

theorem gdh1KeyHandle_queries_sig (S : Setup) (K : Nat) :
    (gdh1KeyHandle S K).queries wSig1Key wsZero1Key = 2 := by simp [gdh1KeyHandle]
theorem gdh1KeyHandle_queries_ddh (S : Setup) (K : Nat) :
    (gdh1KeyHandle S K).queries wDdh1Key wsZero1Key = 4 * K := by simp [gdh1KeyHandle]

theorem gdh1KeyHandle_queries_prim_le (S : Setup) (K : Nat) :
    (gdh1KeyHandle S K).queries wPrim1Key wsZero1Key ≤ 153 + 72 * S.N_dh + 16 * S.N_sess_tot := by
  have hGdh := gdhHandle_primQueries_le S K
  simp only [gdh1KeyHandle, caseSumV_queries, callGdhHandle_queries_prim]
  refine Nat.max_le.mpr ⟨(initPrin1KeyB_queries_prim_le _ _ _).trans (by omega), ?_⟩
  exact Nat.max_le.mpr ⟨hGdh, Nat.max_le.mpr ⟨genSpk1KeyB_queries_prim_le _ _ _ _ _, hGdh⟩⟩

theorem gdh1KeyFinish_queries_sig (S : Setup) (K : Nat) :
    (gdh1KeyFinish S K).queries wSig1Key wsZero1Key = 0 := by simp [gdh1KeyFinish]
theorem gdh1KeyFinish_queries_ddh (S : Setup) (K : Nat) :
    (gdh1KeyFinish S K).queries wDdh1Key wsZero1Key = K + min K S.N_dh + min K S.N_sess_tot := by
  simp [gdh1KeyFinish, gdhFinish_chalQueries]
theorem gdh1KeyFinish_queries_prim_le (S : Setup) (K : Nat) :
    (gdh1KeyFinish S K).queries wPrim1Key wsZero1Key ≤ 3 * S.N_dh + S.N_sess_tot := by
  simp only [gdh1KeyFinish, letV_queries, renameComp_queries, liftGdhComp_queries_prim]
  exact gdhFinish_primQueries_le S K

theorem fgKeyInd1KeyGapDhProg_init_queries_sig (S : Setup) (K : Nat) :
    (fgKeyInd1KeyGapDhProg S K).init.queries wSig1Key wsZero1Key = 0 := by
  simp [fgKeyInd1KeyGapDhProg, initAdv4_1Key, Comp.queries]
theorem fgKeyInd1KeyGapDhProg_init_queries_ddh (S : Setup) (K : Nat) :
    (fgKeyInd1KeyGapDhProg S K).init.queries wDdh1Key wsZero1Key = 0 := by
  simp [fgKeyInd1KeyGapDhProg, initAdv4_1Key, initAdv4_1KeyBase, Comp.queries]
theorem fgKeyInd1KeyGapDhProg_init_queries_prim (S : Setup) (K : Nat) :
    (fgKeyInd1KeyGapDhProg S K).init.queries wPrim1Key wsZero1Key = 0 := by
  simp [fgKeyInd1KeyGapDhProg, initAdv4_1Key, initAdv4_1KeyBase, Comp.queries]

theorem fgKeyInd1KeyGapDhProg_totalSigQueries_eq (S : Setup) (K q : Nat) :
    (fgKeyInd1KeyGapDhProg S K).totalQueries SignalPqxdh.LegacyCosted.chalIfaceSigQueryWeight SignalPqxdh.LegacyCosted.samplerZeroQueryWeight q =
      2 * q := by
  change (fgKeyInd1KeyGapDhProg S K).totalQueries wSig1Key wsZero1Key q = 2 * q
  simp only [CostedReduction.totalQueries, fgKeyInd1KeyGapDhProg_init_queries_sig]
  change 0 + q * (gdh1KeyHandle S K).queries wSig1Key wsZero1Key +
    (gdh1KeyFinish S K).queries wSig1Key wsZero1Key = _
  rw [gdh1KeyHandle_queries_sig, gdh1KeyFinish_queries_sig]
  ring

/-- Syntactic signing-query bound for `fgKeyInd1KeyGapDhProg`. -/
theorem fgKeyInd1KeyGapDhProg_totalSigQueries_le (S : Setup) (b : QueryBudget) :
    (fgKeyInd1KeyGapDhProg S b.q_total).totalQueries
      SignalPqxdh.LegacyCosted.chalIfaceSigQueryWeight SignalPqxdh.LegacyCosted.samplerZeroQueryWeight b.q_total ≤ 2 * b.q_total := by
  rw [fgKeyInd1KeyGapDhProg_totalSigQueries_eq]

theorem fgKeyInd1KeyGapDhProg_totalDdhQueries_eq (S : Setup) (K q : Nat) :
    (fgKeyInd1KeyGapDhProg S K).totalQueries SignalPqxdh.LegacyCosted.chalIfaceDdhQueryWeight SignalPqxdh.LegacyCosted.samplerZeroQueryWeight q =
      4 * q * K + K + min K S.N_dh + min K S.N_sess_tot := by
  change (fgKeyInd1KeyGapDhProg S K).totalQueries wDdh1Key wsZero1Key q = _
  simp only [CostedReduction.totalQueries, fgKeyInd1KeyGapDhProg_init_queries_ddh]
  change 0 + q * (gdh1KeyHandle S K).queries wDdh1Key wsZero1Key +
    (gdh1KeyFinish S K).queries wDdh1Key wsZero1Key = _
  rw [gdh1KeyHandle_queries_ddh, gdh1KeyFinish_queries_ddh]
  ring

/-- Syntactic DDH-query bound for `fgKeyInd1KeyGapDhProg`. -/
theorem fgKeyInd1KeyGapDhProg_totalDdhQueries_le (S : Setup) (b : QueryBudget) :
    (fgKeyInd1KeyGapDhProg S b.q_total).totalQueries
      SignalPqxdh.LegacyCosted.chalIfaceDdhQueryWeight SignalPqxdh.LegacyCosted.samplerZeroQueryWeight b.q_total ≤
      4 * b.q_total ^ 2 + b.q_total + S.N_dh + S.N_sess_tot := by
  rw [fgKeyInd1KeyGapDhProg_totalDdhQueries_eq, ← fgKeyIndGapDhProg_totalChalQueries_eq]
  exact fgKeyIndGapDhProg_totalChalQueries_le S b

theorem fgKeyInd1KeyGapDhProg_totalPrimQueries_poly_le (S : Setup) (K q : Nat) :
    (fgKeyInd1KeyGapDhProg S K).totalQueries SignalPqxdh.LegacyCosted.chalIfacePrimQueryWeight SignalPqxdh.LegacyCosted.samplerZeroQueryWeight q ≤
      q * (153 + 72 * S.N_dh + 16 * S.N_sess_tot) + 3 * S.N_dh + S.N_sess_tot := by
  change (fgKeyInd1KeyGapDhProg S K).totalQueries wPrim1Key wsZero1Key q ≤ _
  simp only [CostedReduction.totalQueries, fgKeyInd1KeyGapDhProg_init_queries_prim]
  have hH := Nat.mul_le_mul_left q (gdh1KeyHandle_queries_prim_le S K)
  have hF := gdh1KeyFinish_queries_prim_le S K
  change 0 + q * (gdh1KeyHandle S K).queries wPrim1Key wsZero1Key +
    (gdh1KeyFinish S K).queries wPrim1Key wsZero1Key ≤ _
  omega

/-- Syntactic primitive-query bound for `fgKeyInd1KeyGapDhProg` against `primQueryBudget`. -/
theorem fgKeyInd1KeyGapDhProg_totalPrimQueries_le (S : Setup) (b : QueryBudget) :
    (fgKeyInd1KeyGapDhProg S b.q_total).totalQueries
      SignalPqxdh.LegacyCosted.chalIfacePrimQueryWeight SignalPqxdh.LegacyCosted.samplerZeroQueryWeight b.q_total ≤ primQueryBudget S b := by
  have hp := fgKeyInd1KeyGapDhProg_totalPrimQueries_poly_le S b.q_total b.q_total
  unfold primQueryBudget
  nlinarith

/-! ## Step-Cost Bounds -/

theorem callGdhHandle_cost (S : Setup) (K : Nat) {Δ : List PT}
    (st1 : Var Δ gdh1KeyStateTy) (q : Var Δ keyIndQueryTy) :
    (callGdhHandle S K st1 q).cost = (gdhHandle S K).cost + 14 := by
  simp only [callGdhHandle, letV, bindV, v, Comp.cost, Expr.cost,
    renameComp_cost, liftGdhComp_cost]
  omega

theorem initPrin1KeyB_costUB (K : Nat) {Γ₁ Γ₂ Δ : List PT} [Ext Γ₁ Δ] [Ext Γ₂ Δ]
    (st1 : Var Γ₁ gdh1KeyStateTy) (u : Var Γ₂ .nat) :
    (initPrin1KeyB K (Δ := Δ) st1 u).costUB ≤ 7 * K + 400 := by
  simp only [initPrin1KeyB, stPrin, stUpd, stSecb, stSpks, stOpks, stSess, stResps,
    stUsedO, stUsedN, stKyb, stRo, stAdv, stMk, peMk, smUpd, smMk,
    smBase_costUB, smFgL_costUB, smRaw_costUB, smLog_costUB, smPows_costUB,
    paUp_costUB, paPrinFlag_costUB, paPrinIdx_costUB, rNone, rInitPrin, natEq,
    letV_costUB, bindV_costUB, eAny_costUB, liftGdhComp_costUB, gPrim_costUB,
    sBytes32_costUB, qX25519Base_costUB, litB_costUB, v_costUB,
    Comp.costUB, Expr.costUB, List.length_nil, PNat.val_ofNat]
  omega

theorem initPrin1KeyB_cost_le (K : Nat) {Γ₁ Γ₂ Δ : List PT} [Ext Γ₁ Δ] [Ext Γ₂ Δ]
    (st1 : Var Γ₁ gdh1KeyStateTy) (u : Var Γ₂ .nat) :
    (initPrin1KeyB K (Δ := Δ) st1 u).cost ≤ 7 * K + 400 :=
  le_trans (initPrin1KeyB K (Δ := Δ) st1 u).cost_le_costUB (initPrin1KeyB_costUB K st1 u)

private def genSpk1KeyTargetArm (S : Setup) (K : Nat) {Δ : List PT}
    (st1 : Var Δ gdh1KeyStateTy) (x : Var Δ (.prod .nat .nat)) :
    Comp pqxdhOps pqSigAndDdhIface Δ (.prod keyIndRespTy gdh1KeyStateTy) :=
  let pa := Expr.fst (.fst (v st1))
  letV pa fun paV =>
  letV (.snd (.fst (v st1))) fun sm =>
  letV (smBase (v sm)) fun bSt =>
  letV (.snd (v st1)) fun sigB =>
  .ite (eAny K (stSpks (v bSt)) fun p => nat2Eq (.fst (v p)) (v x))
    (.ret (.pair rNone (v st1)))
    (caseOptV (eFind K (stPrin (v bSt)) fun p => natEq (.fst (v p)) (.fst (v x)))
      (.ret (.pair rNone (v st1)))
      fun ue =>
        .ite (natEq (v sigB) (.nat 0))
          (.ret (.pair rNone (v st1)))
          (letV (natEq (spkFlatIdxE S (.fst (v x)) (.snd (v x))) (paSpkIdx (v paV))) fun isT =>
           bindV (liftGdhComp (gPrim sBytes32)) fun spkSkRaw =>
           bindV (liftGdhComp (gPrim (qX25519Base (v spkSkRaw)))) fun spkPkRaw =>
           letV (.ite (v isT) (litB 32 []) (v spkSkRaw)) fun spkSk =>
           letV (.ite (v isT) (KeyInd.paV (v paV)) (v spkPkRaw)) fun spkPk =>
           bindV (sigChalQ_dsl 33 (encEC (v spkPk))) fun spkSig =>
           bindV (liftGdhComp (gPrim sRandom64)) fun seed =>
           bindV (liftGdhComp (gPrim (qKemKeyGen (v seed)))) fun kp =>
           bindV (sigChalQ_dsl 1569 (encKEM (.fst (v kp)))) fun pqSig =>
           let jId := u32OfNat (.snd (v x))
           let bE := sbMk (v spkSk) (v spkPk) (v spkSig)
             (.snd (v kp)) (.fst (v kp)) (v pqSig) (.bool false)
           let buOut := buMk (peIkAPk (.snd (v ue))) jId (v spkPk) (v spkSig)
             .none jId (.fst (v kp)) (v pqSig)
           let bSt' := stUpd (v bSt) (spks := .cons (.pair (v x) bE) (stSpks (v bSt)))
           let sm' := smUpd (v sm) (base := bSt')
           .ret (.pair (rBundle buOut) (.pair (.pair (v paV) sm') (.sub (v sigB) (.nat 1))))))

private theorem genSpk1KeyTargetArm_cost_le_min (S : Setup) (K : Nat) {Δ : List PT}
    (st1 : Var Δ gdh1KeyStateTy) (x : Var Δ (.prod .nat .nat)) :
    (genSpk1KeyTargetArm S K st1 x).cost ≤ 20 * K + 2 * bits S.N_dh + 9000 := by
  refine le_trans (genSpk1KeyTargetArm S K st1 x).cost_le_costUB ?_
  simp only [genSpk1KeyTargetArm, stPrin, stSpks, stUpd, stSecb, stOpks, stSess, stResps,
    stUsedO, stUsedN, stKyb, stRo, stAdv, stMk, peIkAPk, sbMk, buMk, smUpd, smMk,
    smBase_costUB, smFgL_costUB, smRaw_costUB, smLog_costUB, smPows_costUB, paV_costUB, paSpkIdx_costUB,
    spkFlatIdxE, mulRight, rNone, rBundle, natEq, nat2Eq, encEC_costUB, encKEM_costUB,
    letV_costUB, bindV_costUB, caseOptV_costUB, eAny_costUB, eFind_costUB,
    liftGdhComp_costUB, gPrim_costUB, sigChalQ_dsl_costUB, sBytes32_costUB, sRandom64_costUB,
    qX25519Base_costUB, qKemKeyGen_costUB, litB_costUB, u32OfNat_costUB, v_costUB,
    Comp.costUB, Expr.costUB, List.length_nil, PNat.val_ofNat, bits_0, bits_1]
  have hd : S.N_dh = S.N_id + S.N_spk_tot + S.N_opk_tot + S.N_send_tot := rfl
  have b1 : bits (S.N_recv.min S.N_spk_tot) ≤ bits S.N_dh :=
    bits_mono (le_trans (Nat.min_le_right _ _) (by omega))
  omega

private theorem genSpk1KeyTargetArm_cost_le (S : Setup) (K : Nat) {Δ : List PT}
    (st1 : Var Δ gdh1KeyStateTy) (x : Var Δ (.prod .nat .nat)) :
    (genSpk1KeyTargetArm S K st1 x).cost ≤ 20 * K + S.N_dh + 9000 := by
  refine le_trans (genSpk1KeyTargetArm S K st1 x).cost_le_costUB ?_
  simp only [genSpk1KeyTargetArm, stPrin, stSpks, stUpd, stSecb, stOpks, stSess, stResps,
    stUsedO, stUsedN, stKyb, stRo, stAdv, stMk, peIkAPk, sbMk, buMk, smUpd, smMk,
    smBase_costUB, smFgL_costUB, smRaw_costUB, smLog_costUB, smPows_costUB, paV_costUB, paSpkIdx_costUB,
    spkFlatIdxE, mulRight, rNone, rBundle, natEq, nat2Eq, encEC_costUB, encKEM_costUB,
    letV_costUB, bindV_costUB, caseOptV_costUB, eAny_costUB, eFind_costUB,
    liftGdhComp_costUB, gPrim_costUB, sigChalQ_dsl_costUB, sBytes32_costUB, sRandom64_costUB,
    qX25519Base_costUB, qKemKeyGen_costUB, litB_costUB, u32OfNat_costUB, v_costUB,
    Comp.costUB, Expr.costUB, List.length_nil, PNat.val_ofNat, bits_0, bits_1]
  have b1 := bits_le_succ (S.N_recv.min S.N_spk_tot)
  have m1 : S.N_recv.min S.N_spk_tot ≤ S.N_spk_tot := Nat.min_le_right _ _
  have hd : S.N_dh = S.N_id + S.N_spk_tot + S.N_opk_tot + S.N_send_tot := rfl
  omega

theorem genSpk1KeyB_cost_le (S : Setup) (K : Nat) {Δ : List PT}
    (st1 : Var Δ gdh1KeyStateTy) (q : Var Δ keyIndQueryTy) (x : Var Δ (.prod .nat .nat)) :
    (genSpk1KeyB S K st1 q x).cost ≤
      28015 * K + 27171 * S.N_dh + 14742 * S.N_sess_tot + 60900 := by
  have hEq : genSpk1KeyB S K st1 q x =
      .ite (.and (paPrinFlag (.fst (.fst (v st1))))
        (natEq (.fst (v x)) (paPrinIdx (.fst (.fst (v st1))))))
        (genSpk1KeyTargetArm S K st1 x)
        (callGdhHandle S K st1 q) := rfl
  rw [hEq]
  have hT := genSpk1KeyTargetArm_cost_le S K st1 x
  have hE : (callGdhHandle S K st1 q).cost ≤
      28015 * K + 27171 * S.N_dh + 14742 * S.N_sess_tot + 60875 := by
    rw [callGdhHandle_cost]
    have := gdhHandle_cost_le S K
    omega
  simp only [Comp.cost, paPrinFlag, paPrinIdx, natEq, v, Expr.cost]
  omega

private theorem caseSumV_cost_add_le {Γ : List PT} {τ₁ τ₂ τ : PT}
    (x : Var Γ (.sum τ₁ τ₂))
    (kl : Var (τ₁ :: Γ) τ₁ → Comp pqxdhOps pqSigAndDdhIface (τ₁ :: Γ) τ)
    (kr : Var (τ₂ :: Γ) τ₂ → Comp pqxdhOps pqSigAndDdhIface (τ₂ :: Γ) τ)
    {d c : ℕ} (hl : (kl .zero).cost + (d + 2) ≤ c) (hr : (kr .zero).cost + (d + 2) ≤ c) :
    (caseSumV (v x) kl kr).cost + d ≤ c := by
  simp only [caseSumV, v, Comp.cost, Expr.cost]
  omega

private theorem add_cost_le {a b d c : ℕ} (h : a ≤ b) (hbc : b + 14 + d ≤ c) :
    a + 14 + d ≤ c := by
  omega

theorem gdh1KeyHandle_cost_le (S : Setup) (K : Nat) :
    (gdh1KeyHandle S K).cost ≤
      28015 * K + 27171 * S.N_dh + 14742 * S.N_sess_tot + 60906 := by
  unfold gdh1KeyHandle
  refine Nat.le_of_add_right_le (k := 0) ?_
  refine caseSumV_cost_add_le _ _ _ ?_ ?_
  · exact (Nat.add_le_add_right (initPrin1KeyB_cost_le _ _ _) 2).trans (by omega)
  · refine caseSumV_cost_add_le _ _ _ ?_ ?_
    · rw [callGdhHandle_cost]
      exact add_cost_le (gdhHandle_cost_le S K) (by omega)
    · refine caseSumV_cost_add_le _ _ _ ?_ ?_
      · exact (Nat.add_le_add_right (genSpk1KeyB_cost_le _ _ _ _ _) 6).trans (by omega)
      · rw [callGdhHandle_cost]
        exact add_cost_le (gdhHandle_cost_le S K) (by omega)

theorem gdh1KeyFinish_cost_le (S : Setup) (K : Nat) :
    (gdh1KeyFinish S K).cost ≤
      69 * S.N_dh ^ 2 + 69 * K * S.N_dh + 66 * S.N_dh * S.N_sess_tot +
        423 * S.N_dh + 263 * S.N_sess_tot + 2132 * K + 413 := by
  have hF := gdhFinish_cost_le S K
  simp only [gdh1KeyFinish, letV, v, Comp.cost, Expr.cost, renameComp_cost, liftGdhComp_cost]
  omega

theorem initAdv4_1KeyBase_costUB (S : Setup) {Γ : List PT} (U V : Expr pqxdhOps Γ (B 32)) :
    (initAdv4_1KeyBase S U V).costUB =
      U.costUB + V.costUB + bits (fgTotalIndexCount S) +
        4 * bits (S.N_id * S.N_spk_tot) + 8 * bits S.N_spk_tot +
        5 * bits S.N_opk_tot +
        3 * bits (S.N_id * S.N_spk_tot + S.N_send_tot * S.N_spk_tot) +
        3 * bits (S.N_id * S.N_spk_tot + S.N_send_tot * S.N_spk_tot + S.N_send_tot * S.N_id) +
        3 * bits S.N_id + 154 := by
  simp only [initAdv4_1KeyBase, initParams1KeyFlat, initParamsDh, initParams1KeyIk, initParamsOpk,
    paMk, emptySimE, smMk, emptyStE, stMk,
    letV_costUB, bindV_costUB, gPrim_costUB, sIndex_costUB, sBool_costUB, v_costUB,
    Comp.costUB, Expr.costUB, bits_0, bits_1, bits_2, bits_3]
  ring

theorem fgKeyInd1KeyGapDhProg_init_costUB (S : Setup) (K : Nat) :
    (fgKeyInd1KeyGapDhProg S K).init.costUB =
      bits (fgTotalIndexCount S) +
        4 * bits (S.N_id * S.N_spk_tot) + 8 * bits S.N_spk_tot +
        bits (min S.N_spk_tot S.N_recv) +
        5 * bits S.N_opk_tot +
        3 * bits (S.N_id * S.N_spk_tot + S.N_send_tot * S.N_spk_tot) +
        3 * bits (S.N_id * S.N_spk_tot + S.N_send_tot * S.N_spk_tot + S.N_send_tot * S.N_id) +
        3 * bits S.N_id + 167 := by
  simp only [fgKeyInd1KeyGapDhProg, initAdv4_1Key, bindV_costUB, liftGdhComp_costUB,
    initAdv4_1KeyBase_costUB, v_costUB, Comp.costUB, Expr.costUB]
  ring

theorem fgKeyInd1KeyGapDhProg_init_cost_le (S : Setup) (K : Nat) :
    (fgKeyInd1KeyGapDhProg S K).init.cost ≤ 26 * S.N_dh ^ 2 + 17 * S.N_dh + 195 := by
  have h := (fgKeyInd1KeyGapDhProg S K).init.cost_le_costUB
  rw [fgKeyInd1KeyGapDhProg_init_costUB] at h
  have b1 := bits_le_succ (fgTotalIndexCount S)
  have b2 := bits_le_succ (S.N_id * S.N_spk_tot)
  have b3 : 8 * bits S.N_spk_tot + bits (min S.N_spk_tot S.N_recv) ≤ 9 * (S.N_spk_tot + 1) := by
    have := bits_le_succ S.N_spk_tot
    have := bits_le_succ (min S.N_spk_tot S.N_recv)
    have := Nat.min_le_left S.N_spk_tot S.N_recv
    omega
  have b4 := bits_le_succ S.N_opk_tot
  have b5 := bits_le_succ (S.N_id * S.N_spk_tot + S.N_send_tot * S.N_spk_tot)
  have b6 := bits_le_succ
    (S.N_id * S.N_spk_tot + S.N_send_tot * S.N_spk_tot + S.N_send_tot * S.N_id)
  have b7 := bits_le_succ S.N_id
  have hfg : fgTotalIndexCount S =
      S.N_id * S.N_spk_tot + S.N_send_tot * S.N_spk_tot +
      S.N_send_tot * S.N_id + S.N_send_opk_tot * S.N_opk_tot := rfl
  have hs : S.N_send_tot = S.N_send_opk_tot + S.N_send_no_opk_tot := rfl
  have hd : S.N_dh = S.N_id + S.N_spk_tot + S.N_opk_tot + S.N_send_tot := rfl
  nlinarith [Nat.zero_le (S.N_send_no_opk_tot * S.N_opk_tot)]

theorem fgKeyInd1KeyGapDhProg_totalCost_poly_le (S : Setup) (K q : Nat) :
    (fgKeyInd1KeyGapDhProg S K).totalCost q ≤
      q * (28015 * K + 27171 * S.N_dh + 14742 * S.N_sess_tot + 60938) +
        95 * S.N_dh ^ 2 + 69 * K * S.N_dh + 66 * S.N_dh * S.N_sess_tot +
        440 * S.N_dh + 263 * S.N_sess_tot + 2132 * K + 608 := by
  have hI := fgKeyInd1KeyGapDhProg_init_cost_le S K
  have hH := gdh1KeyHandle_cost_le S K
  have hF := gdh1KeyFinish_cost_le S K
  have hH32 : max 1 ((gdh1KeyHandle S K).cost + 32) ≤
      28015 * K + 27171 * S.N_dh + 14742 * S.N_sess_tot + 60938 :=
    max_le (by clear hI hH hF; omega) ((Nat.add_le_add_right hH 32).trans (by clear hI hH hF; omega))
  change (fgKeyInd1KeyGapDhProg S K).init.cost + q * max 1 ((gdh1KeyHandle S K).cost + 32) +
    (gdh1KeyFinish S K).cost ≤ _
  exact (Nat.add_le_add (Nat.add_le_add hI (Nat.mul_le_mul_left q hH32)) hF).trans
    (by clear hI hH hF hH32; linarith)

private theorem genSpk1KeyB_cost_le_min (S : Setup) (K : Nat) {Δ : List PT}
    (st1 : Var Δ gdh1KeyStateTy) (q : Var Δ keyIndQueryTy) (x : Var Δ (.prod .nat .nat)) :
    (genSpk1KeyB S K st1 q x).cost ≤
      28015 * K + 27165 * min K S.N_dh + 14742 * min K S.N_sess_tot + 11 * bits S.N_dh + 60890 := by
  have hEq : genSpk1KeyB S K st1 q x =
      .ite (.and (paPrinFlag (.fst (.fst (v st1))))
        (natEq (.fst (v x)) (paPrinIdx (.fst (.fst (v st1))))))
        (genSpk1KeyTargetArm S K st1 x)
        (callGdhHandle S K st1 q) := rfl
  rw [hEq]
  have hT := genSpk1KeyTargetArm_cost_le_min S K st1 x
  have hE : (callGdhHandle S K st1 q).cost ≤
      28015 * K + 27165 * min K S.N_dh + 14742 * min K S.N_sess_tot + 11 * bits S.N_dh + 60864 := by
    rw [callGdhHandle_cost]
    have := gdhHandle_cost_le_min S K
    omega
  simp only [Comp.cost, paPrinFlag, paPrinIdx, natEq, v, Expr.cost]
  omega

private theorem gdh1KeyHandle_cost_le_min (S : Setup) (K : Nat) :
    (gdh1KeyHandle S K).cost ≤
      28015 * K + 27165 * min K S.N_dh + 14742 * min K S.N_sess_tot + 11 * bits S.N_dh + 60896 := by
  unfold gdh1KeyHandle
  refine Nat.le_of_add_right_le (k := 0) ?_
  refine caseSumV_cost_add_le _ _ _ ?_ ?_
  · exact (Nat.add_le_add_right (initPrin1KeyB_cost_le _ _ _) 2).trans (by omega)
  · refine caseSumV_cost_add_le _ _ _ ?_ ?_
    · rw [callGdhHandle_cost]
      exact add_cost_le (gdhHandle_cost_le_min S K) (by omega)
    · refine caseSumV_cost_add_le _ _ _ ?_ ?_
      · exact (Nat.add_le_add_right (genSpk1KeyB_cost_le_min _ _ _ _ _) 6).trans (by omega)
      · rw [callGdhHandle_cost]
        exact add_cost_le (gdhHandle_cost_le_min S K) (by omega)

private theorem gdh1KeyFinish_cost_le_min (S : Setup) (K : Nat) :
    (gdh1KeyFinish S K).cost ≤
      69 * (min K S.N_dh) ^ 2 + 69 * K * min K S.N_dh +
        66 * min K S.N_dh * min K S.N_sess_tot +
        423 * min K S.N_dh + 263 * min K S.N_sess_tot + 2132 * K + 413 := by
  have hF := gdhFinish_cost_le_min S K
  simp only [gdh1KeyFinish, letV, v, Comp.cost, Expr.cost, renameComp_cost, liftGdhComp_cost]
  omega

private theorem fgKeyInd1KeyGapDhProg_init_cost_le_log (S : Setup) (K : Nat) :
    (fgKeyInd1KeyGapDhProg S K).init.cost ≤ 39 * bits S.N_dh + 210 := by
  have h := (fgKeyInd1KeyGapDhProg S K).init.cost_le_costUB
  rw [fgKeyInd1KeyGapDhProg_init_costUB] at h
  have hfg : fgTotalIndexCount S =
      S.N_id * S.N_spk_tot + S.N_send_tot * S.N_spk_tot +
      S.N_send_tot * S.N_id + S.N_send_opk_tot * S.N_opk_tot := rfl
  have hs : S.N_send_tot = S.N_send_opk_tot + S.N_send_no_opk_tot := rfl
  have hd : S.N_dh = S.N_id + S.N_spk_tot + S.N_opk_tot + S.N_send_tot := rfl
  have hsq : ∀ x, x ≤ S.N_dh * S.N_dh → bits x ≤ 2 * bits S.N_dh + 1 := by
    intro x hx
    exact le_trans (bits_mono hx) (by have hm := bits_mul S.N_dh S.N_dh; omega)
  have b1 : bits (fgTotalIndexCount S) ≤ 2 * bits S.N_dh + 1 :=
    hsq _ (by nlinarith [Nat.zero_le (S.N_send_no_opk_tot * S.N_opk_tot)])
  have b2 : bits (S.N_id * S.N_spk_tot) ≤ 2 * bits S.N_dh + 1 := hsq _ (by nlinarith)
  have b3 : bits S.N_spk_tot ≤ bits S.N_dh := bits_mono (by omega)
  have b3m : bits (min S.N_spk_tot S.N_recv) ≤ bits S.N_dh :=
    bits_mono (le_trans (Nat.min_le_left _ _) (by omega))
  have b4 : bits S.N_opk_tot ≤ bits S.N_dh := bits_mono (by omega)
  have b5 : bits (S.N_id * S.N_spk_tot + S.N_send_tot * S.N_spk_tot) ≤ 2 * bits S.N_dh + 1 :=
    hsq _ (by nlinarith)
  have b6 : bits (S.N_id * S.N_spk_tot + S.N_send_tot * S.N_spk_tot + S.N_send_tot * S.N_id) ≤
      2 * bits S.N_dh + 1 := hsq _ (by nlinarith)
  have b7 : bits S.N_id ≤ bits S.N_dh := bits_mono (by omega)
  omega

theorem fgKeyInd1KeyGapDhProg_totalCost_le (S : Setup) (b : QueryBudget) :
    (fgKeyInd1KeyGapDhProg S b.q_total).totalCost b.q_total ≤ stepCostBudget S b := by
  have hI := fgKeyInd1KeyGapDhProg_init_cost_le_log S b.q_total
  have hH := gdh1KeyHandle_cost_le_min S b.q_total
  have hF := gdh1KeyFinish_cost_le_min S b.q_total
  have hmax : max 1 ((gdh1KeyHandle S b.q_total).cost + 32) ≤
      28015 * b.q_total + 27165 * min b.q_total S.N_dh +
        14742 * min b.q_total S.N_sess_tot + 11 * bits S.N_dh + 60928 :=
    max_le (by clear hI hH hF; omega) ((Nat.add_le_add_right hH 32).trans (by clear hI hH hF; omega))
  have htot : (fgKeyInd1KeyGapDhProg S b.q_total).totalCost b.q_total ≤
      b.q_total * (28015 * b.q_total + 27165 * min b.q_total S.N_dh +
        14742 * min b.q_total S.N_sess_tot + 11 * bits S.N_dh + 60928) +
        69 * (min b.q_total S.N_dh) ^ 2 + 69 * b.q_total * min b.q_total S.N_dh +
        66 * min b.q_total S.N_dh * min b.q_total S.N_sess_tot +
        423 * min b.q_total S.N_dh + 263 * min b.q_total S.N_sess_tot +
        39 * bits S.N_dh + 2132 * b.q_total + 623 := by
    change (fgKeyInd1KeyGapDhProg S b.q_total).init.cost +
      b.q_total * max 1 ((gdh1KeyHandle S b.q_total).cost + 32) +
      (gdh1KeyFinish S b.q_total).cost ≤ _
    exact (Nat.add_le_add (Nat.add_le_add hI (Nat.mul_le_mul_left b.q_total hmax)) hF).trans
      (by clear hI hH hF hmax; linarith)
  refine htot.trans ?_
  have hbits : bits S.N_dh = Nat.log 2 S.N_dh + 1 := rfl
  rw [hbits]
  dsimp only [stepCostBudget, _root_.SignalPqxdh.Security.stepCostBudget]
  set q := b.q_total
  set md := min b.q_total S.N_dh
  set ms := min b.q_total S.N_sess_tot
  set ld := Nat.log 2 S.N_dh
  set ls := Nat.log 2 S.N_sess_tot
  have hdiff :
      2 ^ 16 * (q + 1) * (q + 1) + 2 ^ 15 * (q + 1) * (md + ms) +
        2 ^ 10 * (q + 1) * (ld + ls) + 2 ^ 11 * md ^ 2 + 2 ^ 8 * md * ms =
      (q * (28015 * q + 27165 * md + 14742 * ms + 11 * (ld + 1) + 60928) +
        69 * md ^ 2 + 69 * q * md + 66 * md * ms + 423 * md + 263 * ms +
        39 * (ld + 1) + 2132 * q + 623) +
      (37521 * q ^ 2 + 68001 * q + 64874 + 5534 * q * md + 32345 * md +
        18026 * q * ms + 32505 * ms + 1013 * q * ld + 985 * ld +
        1024 * q * ls + 1024 * ls + 1979 * md ^ 2 + 190 * md * ms) := by ring
  omega

/-! ## Output Block-Size Bound -/

theorem securityStepCostBudget_le_legacy (S : Setup) (b : QueryBudget) :
    _root_.SignalPqxdh.Security.stepCostBudget S b ≤
      _root_.SignalPqxdh.LegacyCosted.stepCostBudget S b := by
  have hpow : ∀ k : ℕ, k < 2 ^ k := fun k => by
    induction k with
    | zero => decide
    | succ k ih => rw [Nat.pow_succ]; omega
  have hlog : ∀ n : ℕ, Nat.log 2 n ≤ n := fun n => by
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · simp
    · exact Nat.le_of_lt (Nat.log_lt_of_lt_pow (by omega) (hpow n))
  have md : min b.q_total S.N_dh ≤ S.N_dh := Nat.min_le_right _ _
  have ms : min b.q_total S.N_sess_tot ≤ S.N_sess_tot := Nat.min_le_right _ _
  have ld : Nat.log 2 S.N_dh ≤ S.N_dh := hlog S.N_dh
  have ls : Nat.log 2 S.N_sess_tot ≤ S.N_sess_tot := hlog S.N_sess_tot
  unfold _root_.SignalPqxdh.Security.stepCostBudget _root_.SignalPqxdh.LegacyCosted.stepCostBudget
  dsimp only
  nlinarith [Nat.zero_le (b.q_total + 1), Nat.mul_le_mul md md, Nat.mul_le_mul md ms,
    Nat.mul_le_mul_left (b.q_total + 1) (Nat.add_le_add ld ls),
    Nat.mul_le_mul_left (b.q_total + 1) (Nat.add_le_add md ms)]

/-- Output block-size bound for `fgKeyInd1KeyGapDhProg`. -/
theorem fgKeyInd1KeyGapDhProg_blockBounded (S : Setup) (b : QueryBudget) (ℓ : Nat) :
    SignalPqxdh.LegacyCosted.GRedBlockBounded S b ℓ (fgKeyInd1KeyGapDhProg S b.q_total) :=
  gredBlockBounded_of_totalCost_le pqSamplers_sizeHonest
    one_le_pqChalIface_qCost one_le_pqSamplers_sCost S b ℓ
    (fgKeyInd1KeyGapDhProg S b.q_total)
    ((fgKeyInd1KeyGapDhProg_totalCost_le S b).trans (securityStepCostBudget_le_legacy S b))

/-! ## Query-Bound Soundness Bridges -/

/-- Semantic DDH query bound for `(fgKeyInd1KeyGapDhProg S K).eval`. -/
theorem fgKeyInd1KeyGapDhProg_ddhBounded (S : Setup) (K q : Nat)
    (A : Unit → OracleComp (unifSpec + keyIndSpec S) Bool)
    (hA : ∀ a, (A a).IsQueryBoundP (ReductionDsl.isGameQuery (G := keyIndSpec S)) q)
    (U V : Bytes) :
    ((fgKeyInd1KeyGapDhProg S K).eval A (U, V)).IsQueryBoundP
      (fun q => isDdhChalQuery q = true) (4 * q * K + K + min K S.N_dh + min K S.N_sess_tot) := by
  rw [← fgKeyInd1KeyGapDhProg_totalDdhQueries_eq S K q]
  refine CostedReduction.queryBound_eval (fgKeyInd1KeyGapDhProg S K)
    (fun q => isDdhChalQuery q = true)
    SignalPqxdh.LegacyCosted.chalIfaceDdhQueryWeight SignalPqxdh.LegacyCosted.samplerZeroQueryWeight ?_ ?_ A q hA (U, V)
  · intro g x hx
    cases g with
    | inl t => simp [pqSigAndDdhIface, pqChalIface, isDdhChalQuery] at hx
    | inr t =>
      cases t with
      | inl m => simp [pqSigAndDdhIface, pqChalIface, sigAndDdhOracle, isDdhChalQuery] at hx
      | inr u => rcases u with ⟨⟩; simp [SignalPqxdh.LegacyCosted.chalIfaceDdhQueryWeight]
  · intro n
    change IsQueryBoundP
      (liftM (OracleSpec.query (spec := PrimBaseSpec + sigAndDdhOracle.spec) (Sum.inl (Sum.inl n))))
      (fun q => isDdhChalQuery q = true) 0
    rw [isQueryBoundP_query_iff]
    simp [isDdhChalQuery]

/-- Semantic signing query bound for `(fgKeyInd1KeyGapDhProg S K).eval`. -/
theorem fgKeyInd1KeyGapDhProg_sigBounded_syntactic (S : Setup) (K q : Nat)
    (A : Unit → OracleComp (unifSpec + keyIndSpec S) Bool)
    (hA : ∀ a, (A a).IsQueryBoundP (ReductionDsl.isGameQuery (G := keyIndSpec S)) q)
    (U V : Bytes) :
    ((fgKeyInd1KeyGapDhProg S K).eval A (U, V)).IsQueryBoundP
      (fun q => isSigChalQuery q = true) (2 * q) := by
  rw [← fgKeyInd1KeyGapDhProg_totalSigQueries_eq S K q]
  refine CostedReduction.queryBound_eval (fgKeyInd1KeyGapDhProg S K)
    (fun q => isSigChalQuery q = true)
    SignalPqxdh.LegacyCosted.chalIfaceSigQueryWeight SignalPqxdh.LegacyCosted.samplerZeroQueryWeight ?_ ?_ A q hA (U, V)
  · intro g x hx
    cases g with
    | inl t => simp [pqSigAndDdhIface, pqChalIface, isSigChalQuery] at hx
    | inr t =>
      cases t with
      | inl m => simp [SignalPqxdh.LegacyCosted.chalIfaceSigQueryWeight]
      | inr u =>
        rcases u with ⟨⟩
        simp [pqSigAndDdhIface, pqChalIface, sigAndDdhOracle, isSigChalQuery] at hx
  · intro n
    change IsQueryBoundP
      (liftM (OracleSpec.query (spec := PrimBaseSpec + sigAndDdhOracle.spec) (Sum.inl (Sum.inl n))))
      (fun q => isSigChalQuery q = true) 0
    rw [isQueryBoundP_query_iff]
    simp [isSigChalQuery]

/-- Semantic primitive query bound for `(fgKeyInd1KeyGapDhProg S K).eval`. -/
theorem fgKeyInd1KeyGapDhProg_primBounded (S : Setup) (K q : Nat)
    (A : Unit → OracleComp (unifSpec + keyIndSpec S) Bool)
    (hA : ∀ a, (A a).IsQueryBoundP (ReductionDsl.isGameQuery (G := keyIndSpec S)) q)
    (U V : Bytes) :
    ((fgKeyInd1KeyGapDhProg S K).eval A (U, V)).IsQueryBoundP
      (fun q => isPrimQuery q = true)
      ((fgKeyInd1KeyGapDhProg S K).totalQueries SignalPqxdh.LegacyCosted.chalIfacePrimQueryWeight SignalPqxdh.LegacyCosted.samplerZeroQueryWeight q) := by
  refine CostedReduction.queryBound_eval (fgKeyInd1KeyGapDhProg S K)
    (fun q => isPrimQuery q = true)
    SignalPqxdh.LegacyCosted.chalIfacePrimQueryWeight SignalPqxdh.LegacyCosted.samplerZeroQueryWeight ?_ ?_ A q hA (U, V)
  · intro g x hx
    cases g with
    | inl t => simp [SignalPqxdh.LegacyCosted.chalIfacePrimQueryWeight]
    | inr t => simp [pqSigAndDdhIface, pqChalIface, isPrimQuery] at hx
  · intro n
    change IsQueryBoundP
      (liftM (OracleSpec.query (spec := PrimBaseSpec + sigAndDdhOracle.spec) (Sum.inl (Sum.inl n))))
      (fun q => isPrimQuery q = true) 0
    rw [isQueryBoundP_query_iff]
    simp [isPrimQuery]

/-! ## Program-Size and Run-Local Block-Size Bounds -/

@[simp] theorem liftBase_size {C : ChallengerOracle} {Γ : List PT} {t : PT}
    (c : Comp pqxdhOps pqPrimIface Γ t) :
    (liftBase (C := C) c).size = c.size := by
  induction c <;> simp_all [liftBase, Comp.size, pqChalIface, pqPrimIface]

@[simp] theorem gPrim_size {Γ : List PT} {t : PT} (c : Comp pqxdhOps pqPrimIface Γ t) :
    (gPrim c).size = c.size := liftBase_size c

@[simp] theorem sigChalQ_dsl_size (m : ℕ+) {Γ : List PT} (msg : Expr pqxdhOps Γ (B m)) :
    (sigChalQ_dsl m msg).size = msg.size + 1 := rfl

section AtomicSizeSimp

variable {ι : Type} {T : OracleSpec ι} {I : Iface pqSig T}
  {Γ Δ : List PT} {τ τ₁ τ₂ : PT}

@[simp] theorem v_size [Ext Γ Δ] (x : Var Γ τ) : (v (Δ := Δ) x).size = 1 := rfl
@[simp] theorem bindV_size (m : Comp pqxdhOps I Γ τ₁) (k : Var (τ₁ :: Γ) τ₁ → Comp pqxdhOps I (τ₁ :: Γ) τ₂) : (bindV m k).size = m.size + (k .zero).size + 1 := rfl
@[simp] theorem letV_size (e : Expr pqxdhOps Γ τ₁) (k : Var (τ₁ :: Γ) τ₁ → Comp pqxdhOps I (τ₁ :: Γ) τ₂) : (letV (I := I) e k).size = e.size + 1 + (k .zero).size + 1 := rfl
@[simp] theorem caseOptV_size (o : Expr pqxdhOps Γ (.opt τ₁)) (kn : Comp pqxdhOps I Γ τ₂) (ks : Var (τ₁ :: Γ) τ₁ → Comp pqxdhOps I (τ₁ :: Γ) τ₂) : (caseOptV o kn ks).size = o.size + kn.size + (ks .zero).size + 1 := rfl
@[simp] theorem caseSumV_size (s : Expr pqxdhOps Γ (.sum τ₁ τ₂)) (kl : Var (τ₁ :: Γ) τ₁ → Comp pqxdhOps I (τ₁ :: Γ) τ) (kr : Var (τ₂ :: Γ) τ₂ → Comp pqxdhOps I (τ₂ :: Γ) τ) : (caseSumV s kl kr).size = s.size + (kl .zero).size + (kr .zero).size + 1 := rfl
@[simp] theorem findMV_size (K : Nat) (xs : Expr pqxdhOps Γ (.list τ)) (p : Var (τ :: Γ) τ → Comp pqxdhOps I (τ :: Γ) .bool) : (findMV K xs p).size = xs.size + (p .zero).size + bits K + 1 := rfl
@[simp] theorem anyMV_size (K : Nat) (xs : Expr pqxdhOps Γ (.list τ)) (p : Var (τ :: Γ) τ → Comp pqxdhOps I (τ :: Γ) .bool) : (anyMV K xs p).size = xs.size + (p .zero).size + bits K + 1 := rfl
@[simp] theorem mapMV_size (K : Nat) (xs : Expr pqxdhOps Γ (.list τ₁)) (f : Var (τ₁ :: Γ) τ₁ → Comp pqxdhOps I (τ₁ :: Γ) τ₂) : (mapMV K xs f).size = xs.size + (f .zero).size + bits K + 1 := rfl
@[simp] theorem foldMV_size (K : Nat) (xs : Expr pqxdhOps Γ (.list τ₁)) (init : Expr pqxdhOps Γ τ₂) (f : Var (τ₁ :: τ₂ :: Γ) τ₁ → Var (τ₁ :: τ₂ :: Γ) τ₂ → Comp pqxdhOps I (τ₁ :: τ₂ :: Γ) τ₂) : (foldMV K xs init f).size = xs.size + init.size + (f .zero (.succ .zero)).size + bits K + 1 := rfl
@[simp] theorem eLet_size (e : Expr pqxdhOps Γ τ₁) (k : Var (τ₁ :: Γ) τ₁ → Expr pqxdhOps (τ₁ :: Γ) τ₂) : (eLet e k).size = e.size + (k .zero).size + 1 := rfl
@[simp] theorem eCaseOpt_size (o : Expr pqxdhOps Γ (.opt τ₁)) (kn : Expr pqxdhOps Γ τ₂) (ks : Var (τ₁ :: Γ) τ₁ → Expr pqxdhOps (τ₁ :: Γ) τ₂) : (eCaseOpt o kn ks).size = o.size + kn.size + (ks .zero).size + 1 := rfl
@[simp] theorem eCaseSum_size (s : Expr pqxdhOps Γ (.sum τ₁ τ₂)) (kl : Var (τ₁ :: Γ) τ₁ → Expr pqxdhOps (τ₁ :: Γ) τ) (kr : Var (τ₂ :: Γ) τ₂ → Expr pqxdhOps (τ₂ :: Γ) τ) : (eCaseSum s kl kr).size = s.size + (kl .zero).size + (kr .zero).size + 1 := rfl
@[simp] theorem eFind_size (K : Nat) (xs : Expr pqxdhOps Γ (.list τ)) (p : Var (τ :: Γ) τ → Expr pqxdhOps (τ :: Γ) .bool) : (eFind K xs p).size = xs.size + (p .zero).size + bits K + 1 := rfl
@[simp] theorem eAny_size (K : Nat) (xs : Expr pqxdhOps Γ (.list τ)) (p : Var (τ :: Γ) τ → Expr pqxdhOps (τ :: Γ) .bool) : (eAny K xs p).size = xs.size + (p .zero).size + bits K + 1 := rfl
@[simp] theorem eMap_size (K : Nat) (xs : Expr pqxdhOps Γ (.list τ₁)) (f : Var (τ₁ :: Γ) τ₁ → Expr pqxdhOps (τ₁ :: Γ) τ₂) : (eMap K xs f).size = xs.size + (f .zero).size + bits K + 1 := rfl
@[simp] theorem litB_size (w : ℕ+) (bs : Bytes) : (litB w bs (Γ := Γ)).size = 2 := rfl
@[simp] theorem catB_size {m n : ℕ+} (a : Expr pqxdhOps Γ (B m)) (b : Expr pqxdhOps Γ (B n)) : (catB a b).size = a.size + b.size + 2 := rfl
@[simp] theorem consB_size {w : ℕ+} (b : UInt8) (e : Expr pqxdhOps Γ (B w)) : (consB b e).size = e.size + 1 := rfl
@[simp] theorem widenB_size (w d : ℕ+) (e : Expr pqxdhOps Γ (B w)) : (widenB w d e).size = e.size + 1 := rfl
@[simp] theorem takeKB_size (w k : ℕ+) (e : Expr pqxdhOps Γ (B w)) : (takeKB w k e).size = e.size + 1 := rfl
@[simp] theorem dropB_size {w : ℕ+} (n : Expr pqxdhOps Γ .nat) (e : Expr pqxdhOps Γ (B w)) : (dropB n e).size = n.size + e.size + 2 := rfl
@[simp] theorem lenB_size {w : ℕ+} (e : Expr pqxdhOps Γ (B w)) : (lenB e).size = e.size + 1 := rfl
@[simp] theorem eqB_size {m n : ℕ+} (a : Expr pqxdhOps Γ (B m)) (b : Expr pqxdhOps Γ (B n)) : (eqB a b).size = a.size + b.size + 2 := rfl
@[simp] theorem u32OfNat_size (e : Expr pqxdhOps Γ .nat) : (u32OfNat e).size = e.size + 1 := rfl
@[simp] theorem eqU32_size (a b : Expr pqxdhOps Γ U32) : (eqU32 a b).size = a.size + b.size + 2 := rfl
@[simp] theorem sBool_size : (sBool (Γ := Γ)).size = 2 := rfl
@[simp] theorem sBytes32_size : (sBytes32 (Γ := Γ)).size = 2 := rfl
@[simp] theorem sRandom64_size : (sRandom64 (Γ := Γ)).size = 2 := rfl
@[simp] theorem sDrKey96_size : (sDrKey96 (Γ := Γ)).size = 2 := rfl
@[simp] theorem sIndex_size (N : ℕ) : (sIndex N (Γ := Γ)).size = 2 := rfl
@[simp] theorem qX25519_size (e : Expr pqxdhOps Γ (.prod (B 32) (B 32))) : (qX25519 e).size = e.size + 1 := rfl
@[simp] theorem qX25519Base_size (e : Expr pqxdhOps Γ (B 32)) : (qX25519Base e).size = e.size + 1 := rfl
@[simp] theorem qIsCanonical_size (e : Expr pqxdhOps Γ (B 32)) : (qIsCanonical e).size = e.size + 1 := rfl
@[simp] theorem qPow8_size (e : Expr pqxdhOps Γ (B 32)) : (qPow8 e).size = e.size + 1 := rfl
@[simp] theorem qSigPkGen_size (e : Expr pqxdhOps Γ (B 32)) : (qSigPkGen e).size = e.size + 1 := rfl
@[simp] theorem qSigSign_size (m : ℕ+) (e : Expr pqxdhOps Γ (.prod (B 32) (.prod (B m) (B 64)))) : (qSigSign m e).size = e.size + 1 := rfl
@[simp] theorem qSigVerify_size (m : ℕ+) (e : Expr pqxdhOps Γ (.prod (B 32) (.prod (B m) (B 64)))) : (qSigVerify m e).size = e.size + 1 := rfl
@[simp] theorem qKemKeyGen_size (e : Expr pqxdhOps Γ (B 64)) : (qKemKeyGen e).size = e.size + 1 := rfl
@[simp] theorem qKemEncaps_size (e : Expr pqxdhOps Γ (.prod (B 1568) (B 32))) : (qKemEncaps e).size = e.size + 1 := rfl
@[simp] theorem qKemDecaps_size (e : Expr pqxdhOps Γ (.prod (B 3168) (B 1568))) : (qKemDecaps e).size = e.size + 1 := rfl
@[simp] theorem ddhQ_size (x y z : Expr pqxdhOps Γ (B 32)) : (ddhQ x y z).size = x.size + (y.size + z.size + 1) + 2 := rfl
@[simp] theorem encEC_size (e : Expr pqxdhOps Γ (B 32)) : (encEC e).size = e.size + 1 := rfl
@[simp] theorem encKEM_size (e : Expr pqxdhOps Γ (B 1568)) : (encKEM e).size = e.size + 1 := rfl

end AtomicSizeSimp

theorem bits_le_of_le_four_mul_sq {x N : ℕ} (h : x ≤ 4 * (N * N)) : bits x ≤ 2 * bits N + 3 := by
  have h1 := bits_mono h; have h2 := bits_mul 4 (N * N); have h3 := bits_mul N N
  have h4 : bits 4 = 3 := by decide
  omega

@[simp] private theorem partnerC_size {Γ₁ Γ₂ Δ : List PT} [Ext Γ₁ Δ] [Ext Γ₂ Δ]
    (s : Var Γ₁ keyIndSessionEntryTy) (r : Var Γ₂ keyIndRespEntryTy) :
    (partnerC (Δ := Δ) s r).size = 211 := by
  simp only [partnerC, bindV_size, qPow8_size, getDBytes, optBytesEq, eLet2, eLet_size, eCaseOpt_size,
    eqB_size, litB_size, v_size, Comp.size, Expr.size]

@[simp] private theorem chooseRespRandC_size (S : Setup) (K : Nat) {Γ Δ : List PT} [Ext Γ Δ]
    (st : Var Γ keyIndStateTy) (r : Var Δ keyIndRespEntryTy) :
    (chooseRespRandC S K (Δ := Δ) st r).size = bits (min K S.N_dh) + 238 := by
  simp only [chooseRespRandC, bindV_size, gPrim_size, findMV_size, partnerC_size,
    caseOptV_size, sDrKey96_size, v_size, Comp.size, Expr.size]; omega

@[simp] private theorem chooseInitRandC_size (S : Setup) (K : Nat) {Γ Δ : List PT} [Ext Γ Δ]
    (st : Var Γ keyIndStateTy) (s : Var Δ keyIndSessionEntryTy) :
    (chooseInitRandC S K (Δ := Δ) st s).size = bits (min K S.N_sess_tot) + 235 := by
  simp only [chooseInitRandC, bindV_size, gPrim_size, findMV_size, partnerC_size,
    caseOptV_size, sDrKey96_size, v_size, Comp.size, Expr.size]; omega

@[simp] private theorem fgPatchC_size (K : Nat) {Γ₁ Γ₂ Γ₃ Γ₄ Γ₅ Δ : List PT}
    [Ext Γ₁ Δ] [Ext Γ₂ Δ] [Ext Γ₃ Δ] [Ext Γ₄ Δ] [Ext Γ₅ Δ]
    (pos1 : Var Γ₁ fgPosTy) (pos2 : Var Γ₂ fgPosTy) (pos3 : Var Γ₃ fgPosTy)
    (pos4? : Var Γ₄ (.opt fgPosTy)) (ss : Var Γ₅ (B 32))
    (fgL : Expr pqxdhOps Δ (.list fgPatchEntryTy)) :
    (fgPatchC K pos1 pos2 pos3 pos4? ss fgL).size = fgL.size + bits K + 474 := by
  simp only [fgPatchC, entryMatchesC, ddhEqOptC, ddhEqC, fePos1, fePos2, fePos3, fePos4,
    feSs, feDk, feMk, orE, letV_size, bindV_size, findMV_size, caseOptV_size, caseSumV_size,
    gPrim_size, sDrKey96_size, ddhQ_size, eqB_size, v_size, Comp.size, Expr.size]; omega

@[simp] private theorem finishAcceptGdhC_size (S : Setup) (K : Nat) {Γ₂ Γ₃ Γ₄ Γ₅ Γ₆ Γ₇ Δ : List PT}
    [Ext Γ₂ Δ] [Ext Γ₃ Δ] [Ext Γ₄ Δ] [Ext Γ₅ Δ] [Ext Γ₆ Δ] [Ext Γ₇ Δ]
    (sm : Var Γ₂ simTy) (bSt : Var Γ₃ keyIndStateTy) (hasOpk : Bool) (x : Var Γ₄ accQTy)
    (ke : Var Γ₅ (.prod .nat principalEntryTy))
    (be : Var Γ₆ (.prod (.prod .nat .nat) spkBundleEntryTy))
    (opkPkOpt : Expr pqxdhOps Δ (.opt (B 32)))
    (opks' : Expr pqxdhOps Δ (.list (.prod (.prod .nat (.prod .nat .nat)) opkEntryTy)))
    (usedO' : Expr pqxdhOps Δ (.list (.prod .nat (.prod .nat .nat))))
    (usedN' : Expr pqxdhOps Δ (.list (.prod .nat (.prod .nat .nat))))
    (kyb' : Expr pqxdhOps Δ (.list (.prod .nat (.prod U32 (.prod U32 (B 32))))))
    (patchR : Var Γ₇ (.prod drKeyTy (.list fgPatchEntryTy))) :
    (finishAcceptGdhC S K sm bSt hasOpk x ke be opkPkOpt opks' usedO' usedN' kyb' patchR).size =
      opkPkOpt.size + opks'.size + usedN'.size + usedO'.size + kyb'.size + 2 * bits (min K S.N_dh) + 530 := by
  cases hasOpk <;> {
    simp only [finishAcceptGdhC, findHonestC, chooseRespRandC_size, isSomeE, qHdr, qKJO, qK, qJ, qO,
      smRaw, smLog, smPows, smMk, smUpd, rDrKey, rAccFresh, eqB_size,
      letV_size, bindV_size, findMV_size, eCaseOpt_size, gPrim_size, qPow8_size,
      v_size, Comp.size, Expr.size, ↓reduceIte, Bool.false_eq_true]; omega }

set_option maxRecDepth 100000 in
set_option maxHeartbeats 800000 in
theorem gdhHandle_size_le (S : Setup) (K : Nat) :
    (gdhHandle S K).size ≤ 55 * bits K + 42 * bits S.N_dh + 3 * bits S.N_sess_tot + 15000 := by
  simp (config := { maxSteps := 500000 }) only [gdhHandle, initPrinGdhB, corruptB, genSpkGdhB,
    genOpkGdhB, initiateGdhB, finishAcceptGdhC_size, acceptOpkGdhB, acceptNoOpkGdhB,
    testB, roParsedC, roRawFallbackC, revealB, registerGdhB, revealSpkB,
    wrapBase, wrapSim, paU, paV, paUp, paPrinFlag, paPrinIdx, paDhFlag, paEphIdx, paSpkIdx,
    paOpkMode, paOpkIdx, smBase, smFgL, smRaw, smLog, smPows, smMk, smUpd,
    qKJO, qK, qJ, qO, qHdr, rs, slice32,
    rNone, rInitPrin, rPk, rCorr, rBundle, rHdr, rInitUnfresh, rDrKey, rSpkSk,
    spkFlatIdxE, opkFlatIdxE, initSlotIdxE, initSidE,
    natEq, nat2Eq, nat3Eq, sidEq, kyberEq, kyberCheckE, freshE,
    optU32Eq, isSomeE, optFst, optSnd, nonZero32, encEC_size, encKEM_size,
    orE, mulRight, eLet2, isAdvPowsE,
    mkSecretPosC, mkPairPosC, computePosC, computeOptPosInitC, fgPatchC_size,
    findHonestC, isGameSpkC, isGameOpkC, koskSenderOkPowsC, koskBundleOkPowsC,
    lookupSpkSkC, resolveSigPkC, honestPeerC, checkProvC, chooseInitRandC_size,
    letV_size, bindV_size, caseOptV_size, caseSumV_size, findMV_size, anyMV_size,
    eLet_size, eCaseOpt_size, eCaseSum_size, eFind_size, eAny_size, eMap_size,
    gPrim_size, litB_size, takeKB_size, dropB_size, lenB_size, eqB_size, u32OfNat_size, eqU32_size,
    sBytes32_size, sRandom64_size, sDrKey96_size,
    qX25519_size, qX25519Base_size, qIsCanonical_size, qPow8_size,
    qSigPkGen_size, qSigSign_size, qSigVerify_size,
    qKemKeyGen_size, qKemEncaps_size, qKemDecaps_size, v_size, Comp.size, Expr.size,
    bits_0, bits_32, bits_64, bits_96, bits_128, bits_160, bits_192,
    ↓reduceIte, Bool.false_eq_true]
  have hd : S.N_dh = S.N_id + S.N_spk_tot + S.N_opk_tot + S.N_send_tot := rfl
  have hs : S.N_send_tot = S.N_send_opk_tot + S.N_send_no_opk_tot := rfl
  have b1 : bits (S.N_recv.min S.N_spk_tot) ≤ bits S.N_dh := bits_mono (le_trans (Nat.min_le_right _ _) (by omega))
  have b2 : bits (S.N_opk.min S.N_opk_tot) ≤ bits S.N_dh := bits_mono (le_trans (Nat.min_le_right _ _) (by omega))
  have b3 : bits (S.N_send_opk.min S.N_send_opk_tot) ≤ bits S.N_dh := bits_mono (le_trans (Nat.min_le_right _ _) (by omega))
  have b4 : bits S.N_send_opk_tot ≤ bits S.N_dh := bits_mono (by omega)
  have b5 : bits (S.N_send_no_opk.min S.N_send_no_opk_tot) ≤ bits S.N_dh := bits_mono (le_trans (Nat.min_le_right _ _) (by omega))
  have b6 : bits S.N_send_tot ≤ bits S.N_dh := bits_mono (by omega)
  have bMinDh : bits (min K S.N_dh) ≤ bits S.N_dh := bits_mono (Nat.min_le_right _ _)
  have bMinSess : bits (min K S.N_sess_tot) ≤ bits S.N_sess_tot := bits_mono (Nat.min_le_right _ _)
  omega

theorem gdhFinish_size_le (S : Setup) (K : Nat) :
    (gdhFinish S K).size ≤ 10 * bits K + 5 * bits S.N_dh + 2 * bits S.N_sess_tot + 600 := by
  simp only [gdhFinish, extractMode0C, logFindC, spkPowsC, findMapStepC, initDh1CandC, respDh1CandC,
    lookupFromPowsE, respBundleKeyE, slice32, smBase, smLog, smPows, paU, paV, paMode, natEq, nat2Eq,
    letV_size, bindV_size, caseOptV_size, findMV_size, mapMV_size, foldMV_size, eCaseOpt_size,
    eCaseSum_size, eFind_size, eMap_size, gPrim_size, qPow8_size, qX25519_size, ddhQ_size,
    litB_size, takeKB_size, dropB_size, eqB_size, v_size, Comp.size, Expr.size,
    bits_0, bits_1, bits_2, bits_32, bits_64, bits_96, bits_128]
  have bMinDh : bits (min K S.N_dh) ≤ bits S.N_dh := bits_mono (Nat.min_le_right _ _)
  have bMinSess : bits (min K S.N_sess_tot) ≤ bits S.N_sess_tot := bits_mono (Nat.min_le_right _ _)
  omega

theorem fgKeyIndGapDhProg_size_le (S : Setup) (K : Nat) :
    (fgKeyIndGapDhProg S K).size ≤ 65 * bits K + 85 * bits S.N_dh + 5 * bits S.N_sess_tot + 16000 := by
  have hH := gdhHandle_size_le S K; have hF := gdhFinish_size_le S K
  have hI : (fgKeyIndGapDhProg S K).init.size ≤ 38 * bits S.N_dh + 300 := by
    simp only [fgKeyIndGapDhProg, initAdv4, initParamsFlat, initParamsDh, initParamsIk,
      initParamsOpk, paMk, emptySimE, smMk, emptyStE, letV_size, bindV_size, gPrim_size,
      sIndex_size, sBool_size, v_size, Comp.size, Expr.size, bits_0, bits_1, bits_2, bits_3]
    have hd : S.N_dh = S.N_id + S.N_spk_tot + S.N_opk_tot + S.N_send_tot := rfl
    have hs : S.N_send_tot = S.N_send_opk_tot + S.N_send_no_opk_tot := rfl
    have c1 := bits_le_of_le_four_mul_sq (N := S.N_dh) (x := S.N_id * S.N_spk_tot) (by nlinarith)
    have c2 : bits S.N_spk_tot ≤ bits S.N_dh := bits_mono (by omega)
    have c3 : bits S.N_opk_tot ≤ bits S.N_dh := bits_mono (by omega)
    have c4 := bits_le_of_le_four_mul_sq (N := S.N_dh) (x := S.N_id * S.N_spk_tot + S.N_send_tot * S.N_spk_tot) (by nlinarith)
    have c5 := bits_le_of_le_four_mul_sq (N := S.N_dh) (x := S.N_id * S.N_spk_tot + S.N_send_tot * S.N_spk_tot + S.N_send_tot * S.N_id) (by nlinarith)
    have c6 : bits S.N_id ≤ bits S.N_dh := bits_mono (by omega)
    omega
  change (fgKeyIndGapDhProg S K).init.size + (gdhHandle S K).size + (gdhFinish S K).size ≤ _; omega

theorem callGdhHandle_size (S : Setup) (K : Nat) {Δ : List PT}
    (st1 : Var Δ gdh1KeyStateTy) (q : Var Δ keyIndQueryTy) :
    (callGdhHandle S K st1 q).size = (gdhHandle S K).size + 14 := by
  simp only [callGdhHandle, letV, bindV, v, Comp.size, Expr.size, renameComp_size, liftGdhComp_size]; omega

private theorem caseSumV_size_le {Γ : List PT} {τ₁ τ₂ τ : PT} (x : Var Γ (.sum τ₁ τ₂))
    (kl : Var (τ₁ :: Γ) τ₁ → Comp pqxdhOps pqSigAndDdhIface (τ₁ :: Γ) τ)
    (kr : Var (τ₂ :: Γ) τ₂ → Comp pqxdhOps pqSigAndDdhIface (τ₂ :: Γ) τ)
    {cl cr c : ℕ} (hl : (kl .zero).size ≤ cl) (hr : (kr .zero).size ≤ cr) (hc : cl + cr + 2 ≤ c) :
    (caseSumV (v x) kl kr).size ≤ c := by simp only [caseSumV_size, v_size]; omega

theorem fgKeyInd1KeyGapDhProg_size_le (S : Setup) (K : Nat) :
    (fgKeyInd1KeyGapDhProg S K).size ≤
      180 * bits K + 175 * bits S.N_dh + 11 * bits S.N_sess_tot + 47000 := by
  have hd : S.N_dh = S.N_id + S.N_spk_tot + S.N_opk_tot + S.N_send_tot := rfl
  have hs : S.N_send_tot = S.N_send_opk_tot + S.N_send_no_opk_tot := rfl
  have hGH := gdhHandle_size_le S K; have hGF := gdhFinish_size_le S K
  have hInitPrin : ∀ {Δ : List PT} (st1 : Var Δ gdh1KeyStateTy) (u : Var Δ .nat),
      (initPrin1KeyB K (Δ := Δ) st1 u).size ≤ bits K + 200 := fun st1 u => by
    simp only [initPrin1KeyB, paUp, paPrinFlag, paPrinIdx, smBase, smFgL, smRaw, smLog, smPows,
      smMk, smUpd, rNone, rInitPrin, natEq, letV_size, bindV_size, eAny_size, liftGdhComp_size,
      gPrim_size, sBytes32_size, qX25519Base_size, litB_size, v_size, Comp.size, Expr.size]; omega
  have hTargetArm : ∀ {Δ : List PT} (st1 : Var Δ gdh1KeyStateTy) (x : Var Δ (.prod .nat .nat)),
      (genSpk1KeyTargetArm S K st1 x).size ≤ 2 * bits K + 2 * bits S.N_dh + 400 := fun st1 x => by
    simp only [genSpk1KeyTargetArm, smBase, smFgL, smRaw, smLog, smPows, smMk, smUpd,
      paV, paSpkIdx, spkFlatIdxE, mulRight, rNone, rBundle, natEq, nat2Eq, encEC_size, encKEM_size,
      letV_size, bindV_size, caseOptV_size, eAny_size, eFind_size, liftGdhComp_size, gPrim_size,
      sigChalQ_dsl_size, sBytes32_size, sRandom64_size, qX25519Base_size, qKemKeyGen_size,
      litB_size, u32OfNat_size, v_size, Comp.size, Expr.size, bits_0, bits_1]
    have bm : bits (S.N_recv.min S.N_spk_tot) ≤ bits S.N_dh :=
      bits_mono (le_trans (Nat.min_le_right _ _) (by omega))
    omega
  have hGenSpk : ∀ {Δ : List PT} (st1 : Var Δ gdh1KeyStateTy) (q : Var Δ keyIndQueryTy)
      (x : Var Δ (.prod .nat .nat)), (genSpk1KeyB S K st1 q x).size ≤
        57 * bits K + 44 * bits S.N_dh + 3 * bits S.N_sess_tot + 15500 := fun st1 q x => by
    have hEq : genSpk1KeyB S K st1 q x = .ite (.and (paPrinFlag (.fst (.fst (v st1))))
        (natEq (.fst (v x)) (paPrinIdx (.fst (.fst (v st1))))))
        (genSpk1KeyTargetArm S K st1 x) (callGdhHandle S K st1 q) := rfl
    rw [hEq]; have hT := hTargetArm st1 x; have hC := callGdhHandle_size S K st1 q
    simp only [Comp.size, paPrinFlag, paPrinIdx, natEq, v, Expr.size]; omega
  have hH : (gdh1KeyHandle S K).size ≤
      168 * bits K + 128 * bits S.N_dh + 9 * bits S.N_sess_tot + 46000 := by
    unfold gdh1KeyHandle
    refine caseSumV_size_le _ _ _ (hInitPrin _ _) ?_ (cl := bits K + 200)
      (cr := 167 * bits K + 128 * bits S.N_dh + 9 * bits S.N_sess_tot + 45700) (by omega)
    refine caseSumV_size_le _ _ _ ?_ ?_ (cl := 55 * bits K + 42 * bits S.N_dh + 3 * bits S.N_sess_tot + 15014)
      (cr := 112 * bits K + 86 * bits S.N_dh + 6 * bits S.N_sess_tot + 30600) (by omega)
    · rw [callGdhHandle_size]; omega
    · refine caseSumV_size_le _ _ _ (hGenSpk _ _ _) ?_
        (cl := 57 * bits K + 44 * bits S.N_dh + 3 * bits S.N_sess_tot + 15500)
        (cr := 55 * bits K + 42 * bits S.N_dh + 3 * bits S.N_sess_tot + 15014) (by omega)
      rw [callGdhHandle_size]; omega
  have hF : (gdh1KeyFinish S K).size ≤ 10 * bits K + 5 * bits S.N_dh + 2 * bits S.N_sess_tot + 620 := by
    simp only [gdh1KeyFinish, letV, v, Comp.size, Expr.size, renameComp_size, liftGdhComp_size]; omega
  have hI : (fgKeyInd1KeyGapDhProg S K).init.size ≤ 38 * bits S.N_dh + 300 := by
    simp only [fgKeyInd1KeyGapDhProg, initAdv4_1Key, initAdv4_1KeyBase, initParams1KeyFlat,
      initParamsDh, initParams1KeyIk, initParamsOpk, paMk, emptySimE, smMk, emptyStE,
      letV_size, bindV_size, liftGdhComp_size, gPrim_size, sIndex_size, sBool_size, v_size,
      Comp.size, Expr.size, bits_0, bits_1, bits_2, bits_3]
    have c1 := bits_le_of_le_four_mul_sq (N := S.N_dh) (x := S.N_id * S.N_spk_tot) (by nlinarith)
    have c2 : bits S.N_spk_tot ≤ bits S.N_dh := bits_mono (by omega)
    have c2m : bits (min S.N_spk_tot S.N_recv) ≤ bits S.N_dh := bits_mono (le_trans (Nat.min_le_left _ _) (by omega))
    have c3 : bits S.N_opk_tot ≤ bits S.N_dh := bits_mono (by omega)
    have c4 := bits_le_of_le_four_mul_sq (N := S.N_dh) (x := S.N_id * S.N_spk_tot + S.N_send_tot * S.N_spk_tot) (by nlinarith)
    have c5 := bits_le_of_le_four_mul_sq (N := S.N_dh) (x := S.N_id * S.N_spk_tot + S.N_send_tot * S.N_spk_tot + S.N_send_tot * S.N_id) (by nlinarith)
    have c6 : bits S.N_id ≤ bits S.N_dh := bits_mono (by omega)
    omega
  change (fgKeyInd1KeyGapDhProg S K).init.size + (gdh1KeyHandle S K).size + (gdh1KeyFinish S K).size ≤ _; omega

/-- Run-local output block-size bound for `fgKeyInd1KeyGapDhProg` under `AllGameQueriesFit`. -/
theorem fgKeyInd1KeyGapDhProg_blockBounded_when (S : Setup) (b : QueryBudget) (ℓ : Nat)
    (A : Unit → OracleComp (unifSpec + keyIndSpec S) Bool)
    (hA : ∀ u, (A u).IsQueryBoundP (fun q => SignalPqxdh.isGameQuery q = true) b.q_total)
    (hfit : ∀ u, AllGameQueriesFit ℓ (keyIndCodec S) (A u))
    (x : (Ty.prod (B 32) (B 32)).denote)
    (hx : ValFits ℓ (Ty.prod (B 32) (B 32)) x)
    (y : Bytes)
    (hy : y ∈ supportWhen (pqSigAndDdhIface.AnswerFits ℓ)
      ((fgKeyInd1KeyGapDhProg S b.q_total).eval A x)) :
    ValFits (SignalPqxdh.LegacyCosted.outputSizeBudget S b ℓ) (B 32) y := by
  rw [valFits_iff_fits]
  have hx' : (Ty.prod (B 32) (B 32)).Fits ℓ x := (valFits_iff_fits ℓ _ _).1 hx
  have hA' : ∀ u, (A u).IsQueryBoundP
      (ReductionDsl.isGameQuery (G := keyIndSpec S)) b.q_total := by
    intro u
    convert hA u using 1
    funext q; cases q <;> simp [ReductionDsl.isGameQuery, SignalPqxdh.isGameQuery]
  have hEval := (fgKeyInd1KeyGapDhProg S b.q_total).fits_eval_when
    pqO_sizeHonest pqSamplers_sizeHonest ℓ ℓ 0 (fun _ => trivial)
    A b.q_total ℓ hA' hfit x hx' y hy
  have hCost := le_trans (fgKeyInd1KeyGapDhProg_totalCost_le S b) (securityStepCostBudget_le_legacy S b)
  have hNq := le_trans
    (gred_nq_le_totalCost one_le_pqChalIface_qCost one_le_pqSamplers_sCost
      (fgKeyInd1KeyGapDhProg S b.q_total) b.q_total)
    hCost
  refine Ty.fits_mono ?_ (B 32) y hEval
  unfold SignalPqxdh.LegacyCosted.outputSizeBudget
  have hMul := Nat.mul_le_mul_right ℓ hNq
  nlinarith

/-! ## Tuple-Keyed Reduction Bounds -/

theorem bits_q_total_le_stepCostBudget (S : Setup) (b : QueryBudget) :
    bits b.q_total ≤ bits (_root_.SignalPqxdh.Security.stepCostBudget S b) := by
  refine bits_mono ?_
  unfold _root_.SignalPqxdh.Security.stepCostBudget
  dsimp only
  have h1 : b.q_total ≤ 2 ^ 16 * (b.q_total + 1) := by omega
  have h2 : 2 ^ 16 * (b.q_total + 1) ≤ 2 ^ 16 * (b.q_total + 1) * (b.q_total + 1) :=
    Nat.le_mul_of_pos_right _ (Nat.succ_pos _)
  omega

private theorem bernoulliRatioGdhC_size_le {Δ : List PT} (A B : Nat) :
    (bernoulliRatioGdhC (Δ := Δ) A B).size ≤ 30 := by
  unfold bernoulliRatioGdhC
  split_ifs <;> simp only [bindV_size, gPrim_size, sIndex_size, v_size, Comp.size, Expr.size, bits_1] <;> omega

private theorem chooseArm2C_size_le {Γ₁ Δ : List PT} {α : PT} [Ext Γ₁ Δ] (w1 w2 : Nat)
    (c1 c2 : ∀ {Δ' : List PT} [Ext Γ₁ Δ'], Comp pqxdhOps pqGapDhIface Δ' α)
    {s1 s2 : Nat} (h1 : ∀ {Δ' : List PT} [Ext Γ₁ Δ'], (c1 (Δ' := Δ')).size ≤ s1)
    (h2 : ∀ {Δ' : List PT} [Ext Γ₁ Δ'], (c2 (Δ' := Δ')).size ≤ s2) :
    (chooseArm2C (Γ₁ := Γ₁) (Δ := Δ) w1 w2 c1 c2).size ≤ s1 + s2 + 35 := by
  unfold chooseArm2C
  split_ifs
  · exact (h2 (Δ' := Δ)).trans (by omega)
  · exact (h1 (Δ' := Δ)).trans (by omega)
  · simp only [bindV_size, v_size, Comp.size]
    have hc1 := h1 (Δ' := .bool :: Δ); have hc2 := h2 (Δ' := .bool :: Δ)
    have hb := bernoulliRatioGdhC_size_le (Δ := Δ) w1 w2
    omega

private theorem sampleTargets2C_size_le (S : Setup) :
    (∀ {Δ : List PT}, (samplePrin2C S (Δ := Δ)).size ≤ 15) ∧
    (∀ {Δ : List PT}, (sampleSpkPair2C S (Δ := Δ)).size ≤ 25) ∧
    (∀ {Δ : List PT}, (sampleOpkTriple2C S (Δ := Δ)).size ≤ 35) ∧
    (∀ {Δ : List PT}, (sampleSendOpkTarget2C S (Δ := Δ)).size ≤ 25) ∧
    (∀ {Δ : List PT}, (sampleSendNoOpkTarget2C S (Δ := Δ)).size ≤ 25) ∧
    (∀ {Δ : List PT}, (sampleSendTarget2C S (Δ := Δ)).size ≤ 90) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro Δ; unfold samplePrin2C; split_ifs <;> simp only [bindV_size, gPrim_size, sIndex_size, v_size, Comp.size, Expr.size] <;> omega
  · intro Δ; unfold sampleSpkPair2C; split_ifs <;> simp only [bindV_size, gPrim_size, sIndex_size, v_size, Comp.size, Expr.size] <;> omega
  · intro Δ; unfold sampleOpkTriple2C; split_ifs <;> simp only [bindV_size, gPrim_size, sIndex_size, v_size, Comp.size, Expr.size] <;> omega
  · intro Δ; unfold sampleSendOpkTarget2C; split_ifs <;> simp only [bindV_size, gPrim_size, sIndex_size, v_size, Comp.size, Expr.size] <;> omega
  · intro Δ; unfold sampleSendNoOpkTarget2C; split_ifs <;> simp only [bindV_size, gPrim_size, sIndex_size, v_size, Comp.size, Expr.size] <;> omega
  · intro Δ; unfold sampleSendTarget2C; split_ifs
    · simp only [Comp.size, Expr.size]; omega
    · refine (chooseArm2C_size_le _ _ _ _ (s1 := 25) (s2 := 25) (fun {_} [_] => ?_) (fun {_} [_] => ?_)).trans (by omega)
      · unfold sampleSendOpkTarget2C; split_ifs <;> simp only [bindV_size, gPrim_size, sIndex_size, v_size, Comp.size, Expr.size] <;> omega
      · unfold sampleSendNoOpkTarget2C; split_ifs <;> simp only [bindV_size, gPrim_size, sIndex_size, v_size, Comp.size, Expr.size] <;> omega

set_option maxRecDepth 100000 in
set_option maxHeartbeats 800000 in
theorem gdhHandle2_size_le (S : Setup) (K : Nat) :
    (gdhHandle2 S K).size ≤ 85 * bits K + 15000 := by
  simp (config := { maxSteps := 500000 }) only [gdhHandle2, initPrinGdh2B, corruptB, genSpkGdh2B,
    genOpkGdh2B, initiateGdh2B, finishAcceptGdhC_size, acceptOpkGdh2B, acceptNoOpkGdhB,
    testB, roParsedC, roRawFallbackC, revealB, registerGdhB, revealSpkB,
    wrapBase2, wrapSim2, KeyInd.pa2U, KeyInd.pa2V, KeyInd.pa2Up, KeyInd.pa2PrinTarget,
    KeyInd.pa2DhFlag, KeyInd.pa2EphTarget, KeyInd.pa2SpkTarget, KeyInd.pa2OpkMode,
    KeyInd.pa2OpkTarget, ephSidMatchesE, smBase, smFgL, smRaw, smLog, smPows, smMk, smUpd,
    qKJO, qK, qJ, qO, qHdr, rs, slice32,
    rNone, rInitPrin, rPk, rCorr, rBundle, rHdr, rInitUnfresh, rDrKey, rSpkSk,
    initSidE, natEq, nat2Eq, nat3Eq, sidEq, kyberEq, kyberCheckE, freshE,
    optU32Eq, isSomeE, optFst, optSnd, nonZero32, encEC_size, encKEM_size,
    orE, eLet2, isAdvPowsE,
    mkSecretPosC, mkPairPosC, computePosC, computeOptPosInitC, fgPatchC_size,
    findHonestC, isGameSpkC, isGameOpkC, koskSenderOkPowsC, koskBundleOkPowsC,
    lookupSpkSkC, resolveSigPkC, honestPeerC, checkProvC, chooseInitRandC_size,
    letV_size, bindV_size, caseOptV_size, caseSumV_size, findMV_size, anyMV_size,
    eLet_size, eCaseOpt_size, eCaseSum_size, eFind_size, eAny_size, eMap_size,
    gPrim_size, litB_size, takeKB_size, dropB_size, lenB_size, eqB_size, u32OfNat_size, eqU32_size,
    sBytes32_size, sRandom64_size, sDrKey96_size,
    qX25519_size, qX25519Base_size, qIsCanonical_size, qPow8_size,
    qSigPkGen_size, qSigSign_size, qSigVerify_size,
    qKemKeyGen_size, qKemEncaps_size, qKemDecaps_size, v_size, Comp.size, Expr.size,
    bits_0, bits_32, bits_64, bits_96, bits_128, bits_160, bits_192,
    ↓reduceIte, Bool.false_eq_true]
  have bMinDh : bits (min K S.N_dh) ≤ bits K := bits_mono (Nat.min_le_left _ _)
  have bMinDh' : bits (K.min S.N_dh) ≤ bits K := bits_mono (Nat.min_le_left _ _)
  have bMinSess : bits (min K S.N_sess_tot) ≤ bits K := bits_mono (Nat.min_le_left _ _)
  have bMinSess' : bits (K.min S.N_sess_tot) ≤ bits K := bits_mono (Nat.min_le_left _ _)
  omega

theorem gdhFinish2_size_le (S : Setup) (K : Nat) :
    (gdhFinish2 S K).size ≤ 17 * bits K + 600 := by
  simp only [gdhFinish2, extractMode0_2C, logFind2C, spkPowsC, findMapStep2C, initDh1CandC, respDh1CandC,
    lookupFromPowsE, respBundleKeyE, slice32, smBase, smLog, smPows,
    KeyInd.pa2U, KeyInd.pa2V, KeyInd.pa2Mode, natEq, nat2Eq,
    letV_size, bindV_size, caseOptV_size, findMV_size, mapMV_size, foldMV_size, eCaseOpt_size,
    eCaseSum_size, eFind_size, eMap_size, gPrim_size, qPow8_size, qX25519_size, ddhQ_size,
    litB_size, takeKB_size, dropB_size, eqB_size, v_size, Comp.size, Expr.size,
    bits_0, bits_1, bits_2, bits_32, bits_64, bits_96, bits_128]
  have bMinDh : bits (min K S.N_dh) ≤ bits K := bits_mono (Nat.min_le_left _ _)
  have bMinDh' : bits (K.min S.N_dh) ≤ bits K := bits_mono (Nat.min_le_left _ _)
  have bMinSess : bits (min K S.N_sess_tot) ≤ bits K := bits_mono (Nat.min_le_left _ _)
  have bMinSess' : bits (K.min S.N_sess_tot) ≤ bits K := bits_mono (Nat.min_le_left _ _)
  omega

theorem initParams2C_size_le (S : Setup) {Γ₁ Δ : List PT} [Ext Γ₁ Δ]
    (uv : Var Γ₁ (.prod (B 32) (B 32))) :
    (initParams2C S (Δ := Δ) uv).size ≤ 800 := by
  obtain ⟨hP, hSpk, hOpk, hSO, _, hSend⟩ := sampleTargets2C_size_le S
  unfold initParams2C; split_ifs
  · simp only [KeyInd.pa2Mk, v_size, Comp.size, Expr.size, bits_0, bits_3]; omega
  · refine (chooseArm2C_size_le _ _ _ _ (s1 := 270) (s2 := 270) ?_ ?_).trans (by omega)
    · intro Δ₁ _; refine (chooseArm2C_size_le _ _ _ _ (s1 := 80) (s2 := 150) ?_ ?_).trans (by omega)
      · intro Δ₂ _; simp only [bindV_size, KeyInd.pa2Mk, v_size, Comp.size, Expr.size, bits_0]
        have a := hP (Δ := Δ₂); have b := hSpk (Δ := .opt .nat :: Δ₂); omega
      · intro Δ₂ _; simp only [bindV_size, KeyInd.pa2Mk, v_size, Comp.size, Expr.size, bits_1]
        have a := hSend (Δ := Δ₂); have b := hSpk (Δ := .opt ephTargetTy :: Δ₂); omega
    · intro Δ₁ _; refine (chooseArm2C_size_le _ _ _ _ (s1 := 140) (s2 := 95) ?_ ?_).trans (by omega)
      · intro Δ₂ _; simp only [bindV_size, KeyInd.pa2Mk, v_size, Comp.size, Expr.size, bits_2]
        have a := hSend (Δ := Δ₂); have b := hP (Δ := .opt ephTargetTy :: Δ₂); omega
      · intro Δ₂ _; simp only [bindV_size, KeyInd.pa2Mk, v_size, Comp.size, Expr.size, bits_3]
        have a := hSO (Δ := Δ₂); have b := hOpk (Δ := .opt ephTargetTy :: Δ₂); omega

theorem fgKeyIndGapDh2Prog_size_le (S : Setup) (K : Nat) :
    (fgKeyIndGapDh2Prog S K).size ≤ 102 * bits K + 16600 := by
  have hGH := gdhHandle2_size_le S K; have hGF := gdhFinish2_size_le S K
  have hI : (fgKeyIndGapDh2Prog S K).init.size ≤ 950 := by
    dsimp only [fgKeyIndGapDh2Prog]
    simp only [initAdv4_2, emptySimE, smMk, emptyStE, letV_size, bindV_size, gPrim_size, sBool_size,
      v_size, Comp.size, Expr.size]
    have hP := initParams2C_size_le S
      (Γ₁ := .prod (B 32) (B 32) :: [.prod (B 32) (B 32)])
      (Δ := .prod (B 32) (B 32) :: [.prod (B 32) (B 32)]) .zero
    omega
  change (fgKeyIndGapDh2Prog S K).init.size + (gdhHandle2 S K).size + (gdhFinish2 S K).size ≤ _; omega

theorem fgKeyIndGapDh2Prog_size_le_stepCostBudget (S : Setup) (b : QueryBudget) :
    (fgKeyIndGapDh2Prog S b.q_total).size ≤
      16600 + 102 * bits (_root_.SignalPqxdh.Security.stepCostBudget S b) := by
  have h := fgKeyIndGapDh2Prog_size_le S b.q_total; have hq := bits_q_total_le_stepCostBudget S b; omega

theorem callGdhHandle2_size (S : Setup) (K : Nat) {Δ : List PT}
    (st1 : Var Δ gdh1KeyState2Ty) (q : Var Δ keyIndQueryTy) :
    (callGdhHandle2 S K st1 q).size = (gdhHandle2 S K).size + 14 := by
  simp only [callGdhHandle2, letV, bindV, v, Comp.size, Expr.size, renameComp_size, liftGdhComp_size]; omega

theorem initParams1Key2C_size_le (S : Setup) {Γ₁ Δ : List PT} [Ext Γ₁ Δ]
    (uv : Var Γ₁ (.prod (B 32) (B 32))) :
    (initParams1Key2C S (Δ := Δ) uv).size ≤ 800 := by
  obtain ⟨hP, hSpk, hOpk, hSO, _, hSend⟩ := sampleTargets2C_size_le S
  unfold initParams1Key2C; split_ifs
  · simp only [KeyInd.pa2Mk, v_size, Comp.size, Expr.size, bits_0, bits_3]; omega
  · refine (chooseArm2C_size_le _ _ _ _ (s1 := 270) (s2 := 270) ?_ ?_).trans (by omega)
    · intro Δ₁ _; refine (chooseArm2C_size_le _ _ _ _ (s1 := 80) (s2 := 150) ?_ ?_).trans (by omega)
      · intro Δ₂ _; simp only [bindV_size, KeyInd.pa2Mk, v_size, Comp.size, Expr.size, bits_0]
        have a := hP (Δ := Δ₂); have b := hSpk (Δ := .opt .nat :: Δ₂); omega
      · intro Δ₂ _; simp only [bindV_size, KeyInd.pa2Mk, v_size, Comp.size, Expr.size, bits_1]
        have a := hSend (Δ := Δ₂); have b := hSpk (Δ := .opt ephTargetTy :: Δ₂); omega
    · intro Δ₁ _; refine (chooseArm2C_size_le _ _ _ _ (s1 := 140) (s2 := 95) ?_ ?_).trans (by omega)
      · intro Δ₂ _; simp only [bindV_size, KeyInd.pa2Mk, v_size, Comp.size, Expr.size, bits_2]
        have a := hSend (Δ := Δ₂); have b := hP (Δ := .opt ephTargetTy :: Δ₂); omega
      · intro Δ₂ _; simp only [bindV_size, KeyInd.pa2Mk, v_size, Comp.size, Expr.size, bits_3]
        have a := hSO (Δ := Δ₂); have b := hOpk (Δ := .opt ephTargetTy :: Δ₂); omega

theorem fgKeyInd1KeyGapDh2Prog_size_le (S : Setup) (K : Nat) :
    (fgKeyInd1KeyGapDh2Prog S K).size ≤ 280 * bits K + 48000 := by
  have hGH := gdhHandle2_size_le S K; have hGF := gdhFinish2_size_le S K
  have hInitPrin : ∀ {Δ : List PT} (st1 : Var Δ gdh1KeyState2Ty) (u : Var Δ .nat),
      (initPrin1Key2B K (Δ := Δ) st1 u).size ≤ bits K + 200 := fun st1 u => by
    simp only [initPrin1Key2B, KeyInd.pa2Up, KeyInd.pa2PrinTarget, smBase, smFgL, smRaw, smLog, smPows,
      smMk, smUpd, rNone, rInitPrin, natEq, letV_size, bindV_size, eCaseOpt_size, eAny_size,
      liftGdhComp_size, gPrim_size, sBytes32_size, qX25519Base_size, litB_size, v_size, Comp.size, Expr.size]; omega
  have hGenSpk : ∀ {Δ : List PT} (st1 : Var Δ gdh1KeyState2Ty) (q : Var Δ keyIndQueryTy)
      (x : Var Δ (.prod .nat .nat)),
      (genSpk1Key2B S K st1 q x).size ≤ 88 * bits K + 15500 := fun st1 q x => by
    have hC := callGdhHandle2_size S K st1 q
    simp only [genSpk1Key2B, hC, KeyInd.pa2PrinTarget, KeyInd.pa2SpkTarget, KeyInd.pa2V,
      smBase, smFgL, smRaw, smLog, smPows, smMk, smUpd, rNone, rBundle, natEq, nat2Eq, encEC_size, encKEM_size,
      letV_size, bindV_size, caseOptV_size, eCaseOpt_size, eAny_size, eFind_size,
      liftGdhComp_size, gPrim_size, sigChalQ_dsl_size, sBytes32_size, sRandom64_size,
      qX25519Base_size, qKemKeyGen_size, litB_size, u32OfNat_size, v_size, Comp.size, Expr.size, bits_0, bits_1]; omega
  have hH : (gdh1KeyHandle2 S K).size ≤ 260 * bits K + 46000 := by
    unfold gdh1KeyHandle2
    refine caseSumV_size_le _ _ _ (hInitPrin _ _) ?_ (cl := bits K + 200) (cr := 259 * bits K + 45700) (by omega)
    refine caseSumV_size_le _ _ _ ?_ ?_ (cl := 85 * bits K + 15014) (cr := 173 * bits K + 30600) (by omega)
    · rw [callGdhHandle2_size]; omega
    · refine caseSumV_size_le _ _ _ (hGenSpk _ _ _) ?_ (cl := 88 * bits K + 15500) (cr := 85 * bits K + 15014) (by omega)
      rw [callGdhHandle2_size]; omega
  have hF : (gdh1KeyFinish2 S K).size ≤ 17 * bits K + 620 := by
    simp only [gdh1KeyFinish2, letV, v, Comp.size, Expr.size, renameComp_size, liftGdhComp_size]; omega
  have hI : (fgKeyInd1KeyGapDh2Prog S K).init.size ≤ bits K + 1000 := by
    have bClamp : bits (min K (min S.N_spk_tot S.N_recv)) ≤ bits K := bits_mono (Nat.min_le_left _ _)
    have bClamp' : bits (K.min (S.N_spk_tot.min S.N_recv)) ≤ bits K := bits_mono (Nat.min_le_left _ _)
    dsimp only [fgKeyInd1KeyGapDh2Prog]
    simp only [initAdv4_1Key2, initAdv4_1Key2Base, emptySimE, smMk, emptyStE,
      letV_size, bindV_size, liftGdhComp_size, gPrim_size, sBool_size, v_size, Comp.size, Expr.size]
    have hP := initParams1Key2C_size_le S
      (Γ₁ := .prod (B 32) (B 32) :: [.prod (B 32) (B 32)])
      (Δ := .prod (B 32) (B 32) :: [.prod (B 32) (B 32)]) .zero
    omega
  change (fgKeyInd1KeyGapDh2Prog S K).init.size + (gdh1KeyHandle2 S K).size + (gdh1KeyFinish2 S K).size ≤ _; omega

theorem fgKeyInd1KeyGapDh2Prog_size_le_stepCostBudget (S : Setup) (b : QueryBudget) :
    (fgKeyInd1KeyGapDh2Prog S b.q_total).size ≤
      48000 + 280 * bits (_root_.SignalPqxdh.Security.stepCostBudget S b) := by
  have h := fgKeyInd1KeyGapDh2Prog_size_le S b.q_total; have hq := bits_q_total_le_stepCostBudget S b; omega

end SignalPqxdh.Security.ReductionDsl.KeyInd1KeyGapDh
