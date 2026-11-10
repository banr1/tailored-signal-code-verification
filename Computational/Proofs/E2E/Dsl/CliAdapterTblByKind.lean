/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Computational.Specifications.Game.StatementBinaryHarnessCore
public import Computational.Specifications.Session.ACD19.Ratchet.LibsignalBound
public import Computational.Proofs.E2E.Dsl.CliAdapterCosted -- proof-setup: allow-public-import
import Computational.Proofs.ReductionDsl.KindedCost

/-!
# Per-Kind Costed `Ty.tbl` Binary-Harness Adapter

Refines `cliToModelAdapterProgTbl` with a pre-query `.roQuery` fast path (`isRoQueryExpr`) on the
`.ki` arm so offline random-oracle queries bypass `stepBaseMirrorTblExpr`. The resulting adapter
`cliToModelAdapterProgTblRo` preserves `CostedReduction.eval` unconditionally while satisfying both
`bhAdapterCostBudget` and `bhAdapterCostBudgetByKind`.
-/

public section

set_option autoImplicit false

namespace Computational.Proofs.E2E.Dsl.CliAdapterTblByKind

open _root_.ReductionDsl (Ty Env Expr Comp Ops CostedReduction handlerImpl bits reductionSizeBudget)
open CryptoGames.LibsignalSession (PublicKey)
open CryptoVerification.SignalSession (stdinCapBytes)
open CryptoVerification.E2E (BHDRCtlQuery bhGameSpec bhQueryKind bhKindCounts
  bhAdapterCostBudget bhAdapterCostBudgetByKind)
open CryptoVerification.E2E.Costed (e2eSig PB B sidT keyIndQT keyIndQenc keyIndRT
  E2EPureOp e2ePureOps e2eAdapterOps E2EAdapterTag e2eAdapterIface e2eAdapterCodec)
open Computational.Proofs.E2E.Dsl.TablesHonest (adapterPureOp cost_adapterPureOp
  adapterNoneSmRespExpr adapterCrArm adapterCrArm_cost)
open Computational.Proofs.E2E.Dsl.CliAdapterCosted (bhCtlUnStart e2eBhAdapterIface
  e2eBhAdapterCodec CliToModelAdapterProgHonest drvMirrorTblTy cliAdapterTblStateTy
  cliQuery isEmptyBytesExpr capOkBytesExpr initRegIdExpr natListLitE byte1ToNatE
  pack8BytesE pack32PbytesE pack56BytesE pack392BytesE pack1568Key4E
  tset2E tset3E tset6E stepBaseMirrorTblExpr guardPromoteTblExpr
  cliBobUpdateStateTblExpr cliAliceUpdateStateTblExpr
  cliAdapterKiOrCtlArmTbl cliAdapterTrArmTbl cliAdapterChArmTbl
  cliAdapterDlArmTbl cliAdapterIjArmTbl cliAdapterHandleTbl cliToModelAdapterProgTbl
  size_cliToModelAdapterProgTbl_le_reductionSizeBudget)

/-- Pure `ReductionDsl` classifier returning `true` iff `e : keyIndQT S` encodes `.roQuery`. -/
def isRoQueryExpr {S : SignalPqxdh.Setup} {ℓ : ℕ} {O : Ops (e2eSig ℓ)}
    {Γ : List (Ty (e2eSig ℓ))} (e : Expr O Γ (keyIndQT S)) : Expr O Γ .bool :=
  .caseSum e (.bool false)
    (.caseSum .v0 (.bool false)
      (.caseSum .v0 (.bool false)
        (.caseSum .v0 (.bool false)
          (.caseSum .v0 (.bool false)
            (.caseSum .v0 (.bool false)
              (.caseSum .v0 (.bool false)
                (.caseSum .v0 (.bool false)
                  (.caseSum .v0 (.bool false)
                    (.caseSum .v0 (.bool true) (.bool false))))))))))

def cliAdapterKiOrCtlArmTblRo (S : SignalPqxdh.Setup) (ℓ : ℕ) {Pt : Type}
    (decT : PublicKey → Option Pt) (encT : Pt → PublicKey) :
    Comp (e2eAdapterOps ℓ decT encT) (e2eBhAdapterIface S ℓ)
      [.sum (keyIndQT S) (sidT S), cliAdapterTblStateTy S ℓ, (e2eBhAdapterCodec S ℓ).Q]
      (.prod (e2eBhAdapterCodec S ℓ).R (cliAdapterTblStateTy S ℓ)) :=
  .caseSum .v0
    (.ite (isRoQueryExpr .v0)
      (.bind (cliQuery E2EAdapterTag.ki .v0)
        (.ret (.pair (.inl (.inl .v0)) .v3)))
      (.bind (cliQuery E2EAdapterTag.ki .v0)
        (.ret (.pair (.inl (.inl .v0))
          (.pair (.fst .v3)
            (.pair (.fst (.snd .v3))
              (stepBaseMirrorTblExpr (.snd (.snd .v3)) .v1 .v0)))))))
    (.bind (cliQuery E2EAdapterTag.ctl .v0)
      (.caseOpt .v0
        (.ret (.pair (.inl (.inr .none)) .v3))
        (.caseOpt (guardPromoteTblExpr (.snd (.snd .v4)) .v2)
          (.ret (.pair (.inl (.inr (.some .v0))) .v4))
          (.ret (.pair (.inl (.inr (.some .v1)))
            (.pair (.tset (.fst .v5) .v1 (.some .v0)) (.snd .v5)))))))

def cliAdapterHandleTblRo {Pt : Type} (decT : PublicKey → Option Pt) (encT : Pt → PublicKey)
    (S : SignalPqxdh.Setup) (ℓ : ℕ) :
    Comp (e2eAdapterOps ℓ decT encT) (e2eBhAdapterIface S ℓ)
      [cliAdapterTblStateTy S ℓ, (e2eBhAdapterCodec S ℓ).Q]
      (.prod (e2eBhAdapterCodec S ℓ).R (cliAdapterTblStateTy S ℓ)) :=
  .caseSum (.var (.succ .zero))
    (cliAdapterKiOrCtlArmTblRo S ℓ decT encT)
    (.caseSum (.snd .v0)
      (cliAdapterTrArmTbl S ℓ decT encT)
      (.caseSum .v0
        (cliAdapterChArmTbl S ℓ decT encT)
        (.caseSum .v0
          (cliAdapterDlArmTbl S ℓ decT encT)
          (.caseSum .v0
            (cliAdapterIjArmTbl S ℓ decT encT)
            (adapterCrArm S ℓ BHDRCtlQuery.startDR (bhCtlUnStart (S := S)) decT encT
              (drvMirrorTblTy S ℓ))))))

/-- `Ty.tbl`-backed `CostedReduction` adapter with a `.roQuery` fast path. -/
def cliToModelAdapterProgTblRo {S : SignalPqxdh.Setup} {ℓ : ℕ} {Pt : Type}
    (decT : PublicKey → Option Pt) (encT : Pt → PublicKey) :
    CliToModelAdapterProgHonest S ℓ decT encT where
  σ := cliAdapterTblStateTy S ℓ
  init := (cliToModelAdapterProgTbl (S := S) (ℓ := ℓ) decT encT).init
  handle := cliAdapterHandleTblRo decT encT S ℓ
  finish := (cliToModelAdapterProgTbl (S := S) (ℓ := ℓ) decT encT).finish

theorem cliAdapterKiOrCtlArmTblRo_eval_eq {S : SignalPqxdh.Setup} {ℓ : ℕ} {Pt : Type}
    (decT : PublicKey → Option Pt) (encT : Pt → PublicKey)
    (ρ : Env [.sum (keyIndQT S) (sidT S), cliAdapterTblStateTy S ℓ, (e2eBhAdapterCodec S ℓ).Q]) :
    (cliAdapterKiOrCtlArmTblRo S ℓ decT encT).eval ρ =
      (cliAdapterKiOrCtlArmTbl S ℓ decT encT).eval ρ := by
  dsimp only [cliAdapterKiOrCtlArmTblRo, cliAdapterKiOrCtlArmTbl, Comp.eval]
  cases hkc : (Expr.v0 : Expr (e2eAdapterOps ℓ decT encT) _ _).eval ρ with
  | inr _ => rfl
  | inl v =>
    dsimp only [Comp.eval]
    cases hRo :
        (isRoQueryExpr (.v0 : Expr (e2eAdapterOps ℓ decT encT) _ (keyIndQT S))).eval
          (.cons v ρ) with
    | false => rfl
    | true =>
      rcases v with _ | _ | _ | _ | _ | _ | _ | _ | _ | sec | rest
      · simp [isRoQueryExpr, Expr.eval, Expr.v0, Env.get] at hRo
      · simp [isRoQueryExpr, Expr.eval, Expr.v0, Env.get] at hRo
      · simp [isRoQueryExpr, Expr.eval, Expr.v0, Env.get] at hRo
      · simp [isRoQueryExpr, Expr.eval, Expr.v0, Env.get] at hRo
      · simp [isRoQueryExpr, Expr.eval, Expr.v0, Env.get] at hRo
      · simp [isRoQueryExpr, Expr.eval, Expr.v0, Env.get] at hRo
      · simp [isRoQueryExpr, Expr.eval, Expr.v0, Env.get] at hRo
      · simp [isRoQueryExpr, Expr.eval, Expr.v0, Env.get] at hRo
      · simp [isRoQueryExpr, Expr.eval, Expr.v0, Env.get] at hRo
      · rfl
      · simp [isRoQueryExpr, Expr.eval, Expr.v0, Env.get] at hRo

theorem cliAdapterHandleTblRo_eval_eq {S : SignalPqxdh.Setup} {ℓ : ℕ} {Pt : Type}
    (decT : PublicKey → Option Pt) (encT : Pt → PublicKey)
    (ρ : Env [cliAdapterTblStateTy S ℓ, (e2eBhAdapterCodec S ℓ).Q]) :
    (cliAdapterHandleTblRo decT encT S ℓ).eval ρ =
      (cliAdapterHandleTbl decT encT S ℓ).eval ρ := by
  dsimp only [cliAdapterHandleTblRo, cliAdapterHandleTbl, Comp.eval]
  cases (Expr.var (.succ .zero) : Expr (e2eAdapterOps ℓ decT encT) _ _).eval ρ with
  | inl x => exact cliAdapterKiOrCtlArmTblRo_eval_eq decT encT (.cons x ρ)
  | inr _ => rfl

private theorem cliToModelAdapterProgTblRo_impl_eq {S : SignalPqxdh.Setup} {ℓ : ℕ} {Pt : Type}
    (decT : PublicKey → Option Pt) (encT : Pt → PublicKey) :
    (cliToModelAdapterProgTblRo (S := S) (ℓ := ℓ) decT encT).impl =
      (cliToModelAdapterProgTbl (S := S) (ℓ := ℓ) decT encT).impl := by
  funext q
  cases q with
  | inl _ => rfl
  | inr t =>
    ext s
    simp only [CostedReduction.impl, handlerImpl, cliToModelAdapterProgTblRo,
      cliToModelAdapterProgTbl, cliAdapterHandleTblRo_eval_eq]

/-- Unconditional monadic evaluation equality between `cliToModelAdapterProgTblRo` and
`cliToModelAdapterProgTbl`. -/
theorem cliToModelAdapterProgTblRo_eval_eq {S : SignalPqxdh.Setup} {ℓ : ℕ} {Pt : Type}
    (decT : PublicKey → Option Pt) (encT : Pt → PublicKey) :
    (cliToModelAdapterProgTblRo (S := S) (ℓ := ℓ) decT encT).eval =
      (cliToModelAdapterProgTbl (S := S) (ℓ := ℓ) decT encT).eval := by
  funext A x
  unfold CostedReduction.eval
  rw [cliToModelAdapterProgTblRo_impl_eq]
  rfl

private theorem size_cliToModelAdapterProgTblRo_le {S : SignalPqxdh.Setup} {ℓ : ℕ} {Pt : Type}
    (decT : PublicKey → Option Pt) (encT : Pt → PublicKey) :
    (cliToModelAdapterProgTblRo (S := S) (ℓ := ℓ) decT encT).size ≤
      (cliToModelAdapterProgTbl (S := S) (ℓ := ℓ) decT encT).size + 100 := by
  dsimp only [CostedReduction.size, cliToModelAdapterProgTblRo, cliToModelAdapterProgTbl,
    cliAdapterHandleTblRo, cliAdapterHandleTbl, cliAdapterKiOrCtlArmTblRo,
    cliAdapterKiOrCtlArmTbl, isRoQueryExpr, cliQuery, Comp.size, Expr.size,
    Expr.v0, Expr.v3]
  omega

theorem size_cliToModelAdapterProgTblRo_le_bhAdapterCostBudget
    {S : SignalPqxdh.Setup} {ℓ : ℕ} {Pt : Type}
    (decT : PublicKey → Option Pt) (encT : Pt → PublicKey)
    (b : SignalPqxdh.QueryBudget) (qStart qDR : ℕ) :
    (cliToModelAdapterProgTblRo (S := S) (ℓ := ℓ) decT encT).size ≤
      reductionSizeBudget + 2 ^ 12 * bits (bhAdapterCostBudget S b qStart qDR ℓ) := by
  have hOrig := size_cliToModelAdapterProgTbl_le_reductionSizeBudget (S := S) (ℓ := ℓ) decT encT
  have hDelta := size_cliToModelAdapterProgTblRo_le (S := S) (ℓ := ℓ) decT encT
  have hBits : 1 ≤ bits (bhAdapterCostBudget S b qStart qDR ℓ) := by
    unfold bits; omega
  omega

theorem totalQueries_cliToModelAdapterProgTblRo_eq
    {S : SignalPqxdh.Setup} {ℓ : ℕ} {Pt : Type}
    (decT : PublicKey → Option Pt) (encT : Pt → PublicKey) (q : ℕ) :
    (cliToModelAdapterProgTblRo (S := S) (ℓ := ℓ) decT encT).totalQueries
      (fun _ => 1) (fun _ => 0) q = q := by
  simp [CostedReduction.totalQueries, cliToModelAdapterProgTblRo, cliToModelAdapterProgTbl,
    cliAdapterHandleTblRo, cliAdapterKiOrCtlArmTblRo, cliAdapterTrArmTbl, cliAdapterChArmTbl,
    cliAdapterDlArmTbl, cliAdapterIjArmTbl, adapterCrArm, cliQuery, Comp.queries]

theorem totalQueries_cliToModelAdapterProgTblRo_le
    {S : SignalPqxdh.Setup} {ℓ : ℕ} {Pt : Type}
    (decT : PublicKey → Option Pt) (encT : Pt → PublicKey) (q : ℕ) :
    (cliToModelAdapterProgTblRo (S := S) (ℓ := ℓ) decT encT).totalQueries
      (fun _ => 1) (fun _ => 0) q ≤ q :=
  (totalQueries_cliToModelAdapterProgTblRo_eq (S := S) (ℓ := ℓ) decT encT q).le

private def natListLitCost : List ℕ → ℕ
  | [] => 1
  | k :: ks => bits k + natListLitCost ks + 1

private theorem natListLitE_cost {ℓ : ℕ} {O : Ops (e2eSig ℓ)} {Γ : List (Ty (e2eSig ℓ))} :
    ∀ (ns : List ℕ), (natListLitE (O := O) (Γ := Γ) ns).cost = natListLitCost ns
  | [] => rfl
  | _ :: ks => by simp only [natListLitE, Expr.cost, natListLitE_cost ks, natListLitCost]

private theorem bits_pow_mul {a b k : ℕ} (ha : a = 2 ^ b) : bits (a ^ k) = b * k + 1 := by
  subst ha
  rw [← Nat.pow_mul, bits, Nat.log_pow (by decide : 1 < 2)]

private theorem bits_256_pow_8 : bits (256 ^ 8) = 65 :=
  (bits_pow_mul (b := 8) (k := 8) (by decide)).trans (by omega)

private theorem bits_256_pow_56 : bits (256 ^ 56) = 449 :=
  (bits_pow_mul (b := 8) (k := 56) (by decide)).trans (by omega)

private theorem byte1ToNatE_cost_eq {ℓ : ℕ} {Pt : Type}
    {decT : PublicKey → Option Pt} {encT : Pt → PublicKey} :
    ∃ c, c ≤ 62 ∧ ∀ {Γ : List (Ty (e2eSig ℓ))}
      (e : Expr (e2eAdapterOps ℓ decT encT) Γ (B 1)),
      (byte1ToNatE e).cost = e.cost + c := by
  have hB0 : bits 0 = 1 := by decide
  refine Exists.intro ?c (And.intro ?hB (fun {Γ} e => ?hE))
  case hE =>
    dsimp only [byte1ToNatE, adapterPureOp, e2eAdapterOps, ReductionDsl.Ops.sum, Sum.elim,
      e2ePureOps, Expr.cost, E2EPureOp.cost, List.length_cons, List.length_nil, Expr.v0]
    simp only [PNat.val_ofNat, hB0, Nat.add_assoc]
    rfl
  case hB => omega

private theorem pack8BytesE_cost_eq {ℓ : ℕ} {Pt : Type}
    {decT : PublicKey → Option Pt} {encT : Pt → PublicKey} :
    ∃ c, c ≤ 824 ∧ ∀ {Γ : List (Ty (e2eSig ℓ))}
      (e : Expr (e2eAdapterOps ℓ decT encT) Γ (B 8)),
      (pack8BytesE e).cost = e.cost + c := by
  obtain ⟨cb, hcb, hb⟩ := byte1ToNatE_cost_eq (ℓ := ℓ) (decT := decT) (encT := encT)
  have hL8 : natListLitCost (List.range 8) = 27 := by decide
  have hB0 : bits 0 = 1 := by decide
  have hB256 : bits 256 = 9 := by decide
  refine Exists.intro ?c (And.intro ?hB (fun {Γ} e => ?hE))
  case hE =>
    unfold pack8BytesE
    dsimp only [Expr.cost, Expr.v0, Expr.v1, Expr.v2]
    rw [natListLitE_cost, hb]
    dsimp only [adapterPureOp, e2eAdapterOps, ReductionDsl.Ops.sum, Sum.elim, e2ePureOps,
      Expr.cost, E2EPureOp.cost, Expr.v0, Expr.v2]
    simp only [PNat.val_ofNat, hL8, hB0, hB256, Nat.add_assoc]
    rfl
  case hB => omega

private theorem pack32PbytesE_cost_eq {ℓ : ℕ} {Pt : Type}
    {decT : PublicKey → Option Pt} {encT : Pt → PublicKey} :
    ∃ c, c ≤ 3960 ∧ ∀ {Γ : List (Ty (e2eSig ℓ))}
      (e : Expr (e2eAdapterOps ℓ decT encT) Γ (PB 32)),
      (pack32PbytesE e).cost = e.cost + c := by
  obtain ⟨c8, hc8, h8⟩ := pack8BytesE_cost_eq (ℓ := ℓ) (decT := decT) (encT := encT)
  have hL4 : natListLitCost (List.range 4) = 11 := by decide
  have hB0 : bits 0 = 1 := by decide
  have hB8 : bits 8 = 4 := by decide
  have hB256_8 := bits_256_pow_8
  refine Exists.intro ?c (And.intro ?hB (fun {Γ} e => ?hE))
  case hE =>
    unfold pack32PbytesE
    dsimp only [Expr.cost, Expr.v0, Expr.v1, Expr.v2]
    rw [natListLitE_cost, h8]
    dsimp only [adapterPureOp, e2eAdapterOps, ReductionDsl.Ops.sum, Sum.elim, e2ePureOps,
      Expr.cost, E2EPureOp.cost, Expr.v0, Expr.v2]
    simp only [PNat.val_ofNat, hL4, hB0, hB8, hB256_8, Nat.add_assoc]
    rfl
  case hB => omega

private theorem pack56BytesE_cost_eq {ℓ : ℕ} {Pt : Type}
    {decT : PublicKey → Option Pt} {encT : Pt → PublicKey} :
    ∃ c, c ≤ 7200 ∧ ∀ {Γ : List (Ty (e2eSig ℓ))}
      (e : Expr (e2eAdapterOps ℓ decT encT) Γ (B 56)),
      (pack56BytesE e).cost = e.cost + c := by
  obtain ⟨c8, hc8, h8⟩ := pack8BytesE_cost_eq (ℓ := ℓ) (decT := decT) (encT := encT)
  have hL7 : natListLitCost (List.range 7) = 23 := by decide
  have hB0 : bits 0 = 1 := by decide
  have hB8 : bits 8 = 4 := by decide
  have hB256_8 := bits_256_pow_8
  refine Exists.intro ?c (And.intro ?hB (fun {Γ} e => ?hE))
  case hE =>
    unfold pack56BytesE
    dsimp only [Expr.cost, Expr.v0, Expr.v1, Expr.v2]
    rw [natListLitE_cost, h8]
    dsimp only [adapterPureOp, e2eAdapterOps, ReductionDsl.Ops.sum, Sum.elim, e2ePureOps,
      Expr.cost, E2EPureOp.cost, Expr.v0, Expr.v2]
    simp only [PNat.val_ofNat, hL7, hB0, hB8, hB256_8, Nat.add_assoc]
    rfl
  case hB => omega

private theorem pack392BytesE_cost_eq {ℓ : ℕ} {Pt : Type}
    {decT : PublicKey → Option Pt} {encT : Pt → PublicKey} :
    ∃ c, c ≤ 59600 ∧ ∀ {Γ : List (Ty (e2eSig ℓ))}
      (e : Expr (e2eAdapterOps ℓ decT encT) Γ (B 392)),
      (pack392BytesE e).cost = e.cost + c := by
  obtain ⟨c56, hc56, h56⟩ := pack56BytesE_cost_eq (ℓ := ℓ) (decT := decT) (encT := encT)
  have hL7 : natListLitCost (List.range 7) = 23 := by decide
  have hB0 : bits 0 = 1 := by decide
  have hB56 : bits 56 = 6 := by decide
  have hB256_56 := bits_256_pow_56
  refine Exists.intro ?c (And.intro ?hB (fun {Γ} e => ?hE))
  case hE =>
    unfold pack392BytesE
    dsimp only [Expr.cost, Expr.v0, Expr.v1, Expr.v2]
    rw [natListLitE_cost, h56]
    dsimp only [adapterPureOp, e2eAdapterOps, ReductionDsl.Ops.sum, Sum.elim, e2ePureOps,
      Expr.cost, E2EPureOp.cost, Expr.v0, Expr.v2]
    simp only [PNat.val_ofNat, hL7, hB0, hB56, hB256_56, Nat.add_assoc]
    rfl
  case hB => omega

private theorem pack1568Key4E_cost_eq {ℓ : ℕ} {Pt : Type}
    {decT : PublicKey → Option Pt} {encT : Pt → PublicKey} :
    ∃ c, c ≤ 254200 ∧ ∀ {Γ : List (Ty (e2eSig ℓ))}
      (e : Expr (e2eAdapterOps ℓ decT encT) Γ (PB 1568)),
      (pack1568Key4E e).cost = e.cost + c := by
  obtain ⟨c392, hc392, h392⟩ := pack392BytesE_cost_eq (ℓ := ℓ) (decT := decT) (encT := encT)
  have hB0 : bits 0 = 1 := by decide
  have hB392 : bits 392 = 9 := by decide
  have hB784 : bits 784 = 10 := by decide
  have hB1176 : bits 1176 = 11 := by decide
  refine Exists.intro ?c (And.intro ?hB (fun {Γ} e => ?hE))
  case hE =>
    unfold pack1568Key4E
    dsimp only [Expr.cost]
    rw [h392, h392, h392, h392]
    simp only [adapterPureOp, e2eAdapterOps, ReductionDsl.Ops.sum, Sum.elim, e2ePureOps,
      Expr.cost, E2EPureOp.cost, Expr.v0, PNat.val_ofNat, hB0, hB392, hB784, hB1176, Nat.add_assoc]
    rfl
  case hB => linarith

private theorem stepBaseMirrorTblExpr_cost_le {S : SignalPqxdh.Setup} {ℓ : ℕ} {Pt : Type}
    {decT : PublicKey → Option Pt} {encT : Pt → PublicKey}
    {Γ : List (Ty (e2eSig ℓ))}
    (drv : Expr (e2eAdapterOps ℓ decT encT) Γ (drvMirrorTblTy S ℓ))
    (kq : Expr (e2eAdapterOps ℓ decT encT) Γ (keyIndQT S))
    (kr : Expr (e2eAdapterOps ℓ decT encT) Γ keyIndRT) :
    (stepBaseMirrorTblExpr drv kq kr).cost ≤ drv.cost + kq.cost + kr.cost + 260000 := by
  obtain ⟨c1568, hc1568, h1568⟩ := pack1568Key4E_cost_eq (ℓ := ℓ) (decT := decT) (encT := encT)
  obtain ⟨c32, hc32, h32⟩ := pack32PbytesE_cost_eq (ℓ := ℓ) (decT := decT) (encT := encT)
  dsimp only [stepBaseMirrorTblExpr, tset6E, tset3E, tset2E, Expr.cost,
    Expr.v0, Expr.v1, Expr.v2, Expr.v3, Expr.v4, Expr.v5, Expr.v6]
  rw [h1568, h32]
  dsimp only [adapterPureOp, e2eAdapterOps, ReductionDsl.Ops.sum, Sum.elim, e2ePureOps,
    Expr.cost, E2EPureOp.cost, Expr.v0, Expr.v1]
  omega

private theorem guardPromoteTblExpr_cost_le {S : SignalPqxdh.Setup} {ℓ : ℕ} {Pt : Type}
    {decT : PublicKey → Option Pt} {encT : Pt → PublicKey}
    {Γ : List (Ty (e2eSig ℓ))}
    (drv : Expr (e2eAdapterOps ℓ decT encT) Γ (drvMirrorTblTy S ℓ))
    (sid : Expr (e2eAdapterOps ℓ decT encT) Γ (sidT S)) :
    (guardPromoteTblExpr drv sid).cost ≤ drv.cost + sid.cost + 261000 := by
  obtain ⟨c1568, hc1568, h1568⟩ := pack1568Key4E_cost_eq (ℓ := ℓ) (decT := decT) (encT := encT)
  obtain ⟨c32, hc32, h32⟩ := pack32PbytesE_cost_eq (ℓ := ℓ) (decT := decT) (encT := encT)
  have hB32 : bits 32 = 6 := by decide
  have hB1568 : bits 1568 = 11 := by decide
  dsimp only [guardPromoteTblExpr, initRegIdExpr, Expr.cost,
    Expr.v0, Expr.v1, Expr.v2, Expr.v3, Expr.v4]
  rw [h1568, h32]
  dsimp only [adapterPureOp, e2eAdapterOps, ReductionDsl.Ops.sum, Sum.elim, e2ePureOps,
    Expr.cost, E2EPureOp.cost, Expr.v0, Expr.v1, Expr.v2, Expr.v3, Expr.v4]
  simp only [PNat.val_ofNat, hB32, hB1568]
  omega

private theorem cliAdapterKiOrCtlArmTblRo_cost_le {S : SignalPqxdh.Setup} {ℓ : ℕ} {Pt : Type}
    (decT : PublicKey → Option Pt) (encT : Pt → PublicKey) :
    (cliAdapterKiOrCtlArmTblRo S ℓ decT encT).cost ≤ 261800 := by
  have hMir := stepBaseMirrorTblExpr_cost_le (S := S) (ℓ := ℓ) (decT := decT) (encT := encT)
    (Γ := [keyIndRT, keyIndQT S, .sum (keyIndQT S) (sidT S),
           cliAdapterTblStateTy S ℓ, (e2eBhAdapterCodec S ℓ).Q])
    (.snd (.snd .v3)) .v1 .v0
  have hGrd := guardPromoteTblExpr_cost_le (S := S) (ℓ := ℓ) (decT := decT) (encT := encT)
    (Γ := [.nat, .opt .nat, sidT S, .sum (keyIndQT S) (sidT S),
           cliAdapterTblStateTy S ℓ, (e2eBhAdapterCodec S ℓ).Q])
    (.snd (.snd .v4)) .v2
  dsimp only [cliAdapterKiOrCtlArmTblRo, isRoQueryExpr, cliQuery, e2eBhAdapterIface,
    e2eAdapterIface, Comp.cost, Expr.cost,
    Expr.v0, Expr.v1, Expr.v2, Expr.v3, Expr.v4, Expr.v5] at hMir hGrd ⊢
  omega

private theorem cliAdapterTrArmTbl_cost_le {S : SignalPqxdh.Setup} {ℓ : ℕ} {Pt : Type}
    (decT : PublicKey → Option Pt) (encT : Pt → PublicKey) :
    (cliAdapterTrArmTbl S ℓ decT encT).cost ≤ 512 + 4 * (ℓ / 32) := by
  dsimp only [cliAdapterTrArmTbl, cliQuery, e2eBhAdapterIface, e2eAdapterIface,
    adapterNoneSmRespExpr, Comp.cost, Expr.cost, cost_adapterPureOp, E2EPureOp.cost,
    Expr.v0, Expr.v1, Expr.v2, Expr.v3, Expr.v4, Expr.v5]
  omega

private theorem cliAdapterChArmTbl_cost_le {S : SignalPqxdh.Setup} {ℓ : ℕ} {Pt : Type}
    (decT : PublicKey → Option Pt) (encT : Pt → PublicKey) :
    (cliAdapterChArmTbl S ℓ decT encT).cost ≤ 512 + 5 * (ℓ / 32) := by
  dsimp only [cliAdapterChArmTbl, cliQuery, e2eBhAdapterIface, e2eAdapterIface,
    adapterNoneSmRespExpr, Comp.cost, Expr.cost, cost_adapterPureOp, E2EPureOp.cost,
    Expr.v0, Expr.v1, Expr.v2, Expr.v3, Expr.v4, Expr.v5, Expr.v6]
  omega

private theorem cliAdapterDlArmTbl_cost_le {S : SignalPqxdh.Setup} {ℓ : ℕ} {Pt : Type}
    (decT : PublicKey → Option Pt) (encT : Pt → PublicKey) :
    (cliAdapterDlArmTbl S ℓ decT encT).cost ≤ 1024 + 4 * (ℓ / 32) := by
  have hB32 : bits (32 : ℕ+) = 6 := by decide
  have hB0 : bits 0 = 1 := by decide
  dsimp only [cliAdapterDlArmTbl, cliBobUpdateStateTblExpr, cliAliceUpdateStateTblExpr,
    isEmptyBytesExpr, cliQuery, e2eBhAdapterIface, e2eAdapterIface, adapterNoneSmRespExpr,
    Comp.cost, Expr.cost, cost_adapterPureOp, E2EPureOp.cost, Expr.v0, Expr.v1, Expr.v2,
    Expr.v3, Expr.v4, Expr.v5, Expr.v6]
  rw [hB32, hB0]
  omega

private theorem cliAdapterIjArmTbl_cost_le {S : SignalPqxdh.Setup} {ℓ : ℕ} {Pt : Type}
    (decT : PublicKey → Option Pt) (encT : Pt → PublicKey) :
    (cliAdapterIjArmTbl S ℓ decT encT).cost ≤ 1024 + 4 * (ℓ / 32) := by
  have hB32 : bits (32 : ℕ+) = 6 := by decide
  have hB0 : bits 0 = 1 := by decide
  have hBCap : bits stdinCapBytes = 21 := by decide
  dsimp only [cliAdapterIjArmTbl, cliAliceUpdateStateTblExpr, isEmptyBytesExpr, capOkBytesExpr,
    cliQuery, e2eBhAdapterIface, e2eAdapterIface, adapterNoneSmRespExpr, Comp.cost, Expr.cost,
    cost_adapterPureOp, E2EPureOp.cost, Expr.v0, Expr.v1, Expr.v2, Expr.v3,
    Expr.v4, Expr.v5, Expr.v6]
  rw [hB32, hB0, hBCap]
  omega

private theorem cliAdapterHandleTblRo_cost_le {S : SignalPqxdh.Setup} {ℓ : ℕ} {Pt : Type}
    (decT : PublicKey → Option Pt) (encT : Pt → PublicKey) :
    (cliAdapterHandleTblRo decT encT S ℓ).cost ≤ 262000 + 8 * (ℓ / 32) := by
  have h1 := cliAdapterKiOrCtlArmTblRo_cost_le (S := S) (ℓ := ℓ) decT encT
  have h2 := cliAdapterTrArmTbl_cost_le (S := S) (ℓ := ℓ) decT encT
  have h3 := cliAdapterChArmTbl_cost_le (S := S) (ℓ := ℓ) decT encT
  have h4 := cliAdapterDlArmTbl_cost_le (S := S) (ℓ := ℓ) decT encT
  have h5 := cliAdapterIjArmTbl_cost_le (S := S) (ℓ := ℓ) decT encT
  have h6 := adapterCrArm_cost S ℓ BHDRCtlQuery.startDR (bhCtlUnStart (S := S)) decT encT
    (drvMirrorTblTy S ℓ)
  dsimp only [cliAdapterHandleTblRo, Comp.cost, Expr.cost, Expr.v0]
  have m5 : max (cliAdapterIjArmTbl S ℓ decT encT).cost
      (adapterCrArm S ℓ BHDRCtlQuery.startDR (bhCtlUnStart (S := S)) decT encT
        (drvMirrorTblTy S ℓ)).cost ≤ 226000 + 8 * (ℓ / 32) :=
    Nat.max_le.mpr ⟨by omega, by omega⟩
  have m4 : max (cliAdapterDlArmTbl S ℓ decT encT).cost
      (1 + max (cliAdapterIjArmTbl S ℓ decT encT).cost
        (adapterCrArm S ℓ BHDRCtlQuery.startDR (bhCtlUnStart (S := S)) decT encT
          (drvMirrorTblTy S ℓ)).cost + 1) ≤ 226002 + 8 * (ℓ / 32) :=
    Nat.max_le.mpr ⟨by omega, by omega⟩
  have m3 : max (cliAdapterChArmTbl S ℓ decT encT).cost
      (1 + max (cliAdapterDlArmTbl S ℓ decT encT).cost
        (1 + max (cliAdapterIjArmTbl S ℓ decT encT).cost
          (adapterCrArm S ℓ BHDRCtlQuery.startDR (bhCtlUnStart (S := S)) decT encT
            (drvMirrorTblTy S ℓ)).cost + 1) + 1) ≤ 226004 + 8 * (ℓ / 32) :=
    Nat.max_le.mpr ⟨by omega, by omega⟩
  have m2 : max (cliAdapterTrArmTbl S ℓ decT encT).cost
      (1 + max (cliAdapterChArmTbl S ℓ decT encT).cost
        (1 + max (cliAdapterDlArmTbl S ℓ decT encT).cost
          (1 + max (cliAdapterIjArmTbl S ℓ decT encT).cost
            (adapterCrArm S ℓ BHDRCtlQuery.startDR (bhCtlUnStart (S := S)) decT encT
              (drvMirrorTblTy S ℓ)).cost + 1) + 1) + 1) ≤ 226006 + 8 * (ℓ / 32) :=
    Nat.max_le.mpr ⟨by omega, by omega⟩
  have m1 : max (cliAdapterKiOrCtlArmTblRo S ℓ decT encT).cost
      ((1 + 1) + max (cliAdapterTrArmTbl S ℓ decT encT).cost
        (1 + max (cliAdapterChArmTbl S ℓ decT encT).cost
          (1 + max (cliAdapterDlArmTbl S ℓ decT encT).cost
            (1 + max (cliAdapterIjArmTbl S ℓ decT encT).cost
              (adapterCrArm S ℓ BHDRCtlQuery.startDR (bhCtlUnStart (S := S)) decT encT
                (drvMirrorTblTy S ℓ)).cost + 1) + 1) + 1) + 1) ≤ 261990 + 8 * (ℓ / 32) :=
    Nat.max_le.mpr ⟨by omega, by omega⟩
  omega

theorem totalCost_cliToModelAdapterProgTblRo_le_bhAdapterCostBudget
    {S : SignalPqxdh.Setup} {ℓ : ℕ} {Pt : Type}
    (decT : PublicKey → Option Pt) (encT : Pt → PublicKey)
    (b : SignalPqxdh.QueryBudget) (qStart qDR : ℕ) :
    (cliToModelAdapterProgTblRo (S := S) (ℓ := ℓ) decT encT).totalCost (b.q_total + qStart + qDR) ≤
      bhAdapterCostBudget S b qStart qDR ℓ := by
  let R := cliToModelAdapterProgTblRo (S := S) (ℓ := ℓ) decT encT
  let qTot := b.q_total + qStart + qDR
  let P := 2 ^ 6 * (4 * ℓ + 2 ^ 12)
  have hInitFin : R.init.cost + R.finish.cost ≤ P := by
    dsimp only [R, P, cliToModelAdapterProgTblRo, cliToModelAdapterProgTbl, Comp.cost, Expr.cost]
    omega
  have hHandle : R.handle.cost ≤ 262000 + 8 * (ℓ / 32) :=
    cliAdapterHandleTblRo_cost_le decT encT
  have hCodec : (e2eBhAdapterCodec S ℓ).codecCost ≤ 64 := by
    dsimp [e2eBhAdapterCodec, e2eAdapterCodec]
    omega
  have hStep : max (e2eBhAdapterIface S ℓ).uCost
      (R.handle.cost + (e2eBhAdapterCodec S ℓ).codecCost) ≤ P := by
    dsimp only [e2eBhAdapterIface, e2eAdapterIface, P]
    omega
  calc R.totalCost qTot
      = (R.init.cost + R.finish.cost) +
          qTot * max (e2eBhAdapterIface S ℓ).uCost
            (R.handle.cost + (e2eBhAdapterCodec S ℓ).codecCost) := by
        dsimp only [CostedReduction.totalCost]; omega
    _ ≤ 1 * P + qTot * P :=
        Nat.add_le_add (by simpa only [Nat.one_mul] using hInitFin) (Nat.mul_le_mul_left qTot hStep)
    _ = (qTot + 1) * P := by rw [← Nat.add_mul, Nat.add_comm]
    _ = 2 ^ 6 * (qTot + 1) * (4 * ℓ + 2 ^ 12) := by
        dsimp only [P]
        rw [← Nat.mul_assoc, Nat.mul_comm (qTot + 1) (2 ^ 6), Nat.mul_assoc]
    _ ≤ bhAdapterCostBudget S b qStart qDR ℓ := by
        unfold bhAdapterCostBudget
        dsimp only [qTot]
        exact Nat.mul_le_mul_left _ (by omega)

private theorem list_ofFn_fin2_sum_local (f : Fin 2 → ℕ) :
    (List.ofFn f).sum = f 0 + f 1 := by
  simp [List.ofFn_succ]

private theorem handle_costAt_roQuery_le {S : SignalPqxdh.Setup} {ℓ : ℕ} {Pt : Type}
    (decT : PublicKey → Option Pt) (encT : Pt → PublicKey)
    (s : (cliAdapterTblStateTy S ℓ).denote) (sec : SignalPqxdh.Bytes) :
    (cliAdapterHandleTblRo decT encT S ℓ).costAt
      (.cons s (.cons ((e2eBhAdapterCodec S ℓ).qenc (.inl (.inl (.roQuery sec)))) .nil)) ≤ 200 := by
  simp only [cliAdapterHandleTblRo, cliAdapterKiOrCtlArmTblRo, isRoQueryExpr, cliQuery,
    e2eBhAdapterIface, e2eAdapterIface, e2eBhAdapterCodec, e2eAdapterCodec, keyIndQenc,
    Comp.costAt, Comp.pureEval?, Comp.cost, Expr.costAt, Expr.cost, Expr.eval,
    Expr.v0, Expr.v3, Env.get, ↓reduceIte, Nat.reduceAdd]
  omega

/-- Per-kind `CostBoundedByKind` bound against `bhAdapterCostBudgetByKind` for
`cliToModelAdapterProgTblRo`. -/
theorem costBoundedByKind_cliToModelAdapterProgTblRo_bhAdapterCostBudgetByKind
    {S : SignalPqxdh.Setup} {ℓ : ℕ} {Pt : Type}
    (decT : PublicKey → Option Pt) (encT : Pt → PublicKey)
    (b : SignalPqxdh.QueryBudget) (qStart qDR : ℕ) :
    (cliToModelAdapterProgTblRo (S := S) (ℓ := ℓ) decT encT).CostBoundedByKind
      bhQueryKind (bhKindCounts b qStart qDR) (bhAdapterCostBudgetByKind S b qStart qDR ℓ) := by
  let R := cliToModelAdapterProgTblRo (S := S) (ℓ := ℓ) decT encT
  let hCost : Fin 2 → ℕ
    | 0 => R.handle.cost
    | 1 => 200
  refine ⟨hCost, ?_, ?_⟩
  · intro s t
    rcases t with (kq | cq) | ⟨idx, sq⟩
    · cases kq with
      | roQuery sec =>
        change R.handle.costAt _ ≤ hCost 1
        exact handle_costAt_roQuery_le decT encT s sec
      | _ =>
        change R.handle.costAt _ ≤ R.handle.cost
        exact _root_.ReductionDsl.Comp.costAt_le_cost R.handle _
    · change R.handle.costAt _ ≤ R.handle.cost
      exact _root_.ReductionDsl.Comp.costAt_le_cost R.handle _
    · change R.handle.costAt _ ≤ R.handle.cost
      exact _root_.ReductionDsl.Comp.costAt_le_cost R.handle _
  · let qKind := bhKindCounts b qStart qDR
    let P := 2 ^ 6 * (4 * ℓ + 2 ^ 12)
    have hInitFin : R.init.cost + R.finish.cost ≤ P := by
      dsimp only [R, P, cliToModelAdapterProgTblRo, cliToModelAdapterProgTbl, Comp.cost, Expr.cost]
      omega
    have hHandle : R.handle.cost ≤ 262000 + 8 * (ℓ / 32) :=
      cliAdapterHandleTblRo_cost_le decT encT
    have hStep0 : max (e2eBhAdapterIface S ℓ).uCost
        (hCost 0 + (e2eBhAdapterCodec S ℓ).codecCost) ≤ P := by
      dsimp only [hCost, P]
      omega
    have hStep1 : max (e2eBhAdapterIface S ℓ).uCost
        (hCost 1 + (e2eBhAdapterCodec S ℓ).codecCost) ≤ 2 ^ 12 := by
      dsimp only [hCost]
      omega
    have hSum : R.totalCostByKind hCost qKind =
        (R.init.cost + R.finish.cost) +
          qKind 0 * max (e2eBhAdapterIface S ℓ).uCost
            (hCost 0 + (e2eBhAdapterCodec S ℓ).codecCost) +
          qKind 1 * max (e2eBhAdapterIface S ℓ).uCost
            (hCost 1 + (e2eBhAdapterCodec S ℓ).codecCost) := by
      unfold CostedReduction.totalCostByKind
      rw [list_ofFn_fin2_sum_local]
      omega
    rw [hSum]
    have hOn : (R.init.cost + R.finish.cost) +
        qKind 0 * max (e2eBhAdapterIface S ℓ).uCost
          (hCost 0 + (e2eBhAdapterCodec S ℓ).codecCost) ≤
        2 ^ 6 * (min b.q_on b.q_total + qStart + qDR + 1) * (4 * ℓ + 2 ^ 12) := by
      calc (R.init.cost + R.finish.cost) +
            qKind 0 * max (e2eBhAdapterIface S ℓ).uCost
              (hCost 0 + (e2eBhAdapterCodec S ℓ).codecCost)
          ≤ 1 * P + qKind 0 * P :=
            Nat.add_le_add (by simpa only [Nat.one_mul] using hInitFin)
              (Nat.mul_le_mul_left _ hStep0)
        _ = (qKind 0 + 1) * P := by rw [← Nat.add_mul, Nat.add_comm]
        _ = 2 ^ 6 * (min b.q_on b.q_total + qStart + qDR + 1) * (4 * ℓ + 2 ^ 12) := by
            dsimp only [qKind, bhKindCounts, P]
            rw [← Nat.mul_assoc, Nat.mul_comm _ (2 ^ 6), Nat.mul_assoc]
    have hRo : qKind 1 * max (e2eBhAdapterIface S ℓ).uCost
          (hCost 1 + (e2eBhAdapterCodec S ℓ).codecCost) ≤
        2 ^ 12 * min b.q_ro b.q_total := by
      calc qKind 1 * max (e2eBhAdapterIface S ℓ).uCost
            (hCost 1 + (e2eBhAdapterCodec S ℓ).codecCost)
          ≤ (min b.q_ro b.q_total) * 2 ^ 12 := Nat.mul_le_mul_left _ hStep1
        _ = 2 ^ 12 * min b.q_ro b.q_total := Nat.mul_comm _ _
    unfold bhAdapterCostBudgetByKind
    refine Nat.add_le_add ?_ hRo
    exact le_trans hOn (Nat.mul_le_mul_left _ (by omega))

end Computational.Proofs.E2E.Dsl.CliAdapterTblByKind
