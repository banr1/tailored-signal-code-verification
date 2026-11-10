/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Computational.Proofs.ReductionDsl.FsAtomicBundles -- proof-setup: allow-public-import
import Computational.Proofs.ReductionDsl.AtomicTablesHonest
import Computational.Proofs.ReductionDsl.GRedBoundedOfBounds
import Computational.Proofs.ReductionDsl.SizeBudgetBridge
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring


/-! # Shared cost and size helpers for `FsAtomicBounds` -/

public section

set_option autoImplicit false

open ReductionDsl (Sig Ty Var Env Expr Comp Samplers Ops Iface GameCodec CostedReduction
  TwoStageCostedReduction UniformSamplerTag OpsSizeHonest SampSizeHonest bits reductionSizeBudget
  unifSamplers unifSamplers0 atomicSig AtomicBaseUnif atomicBaseSamplers atomicFsOps
  atomicFsOps_sizeHonest atomicBaseSamplers_sizeHonest B U8 U32 U64 BV128 BV256 PK IdKey PlainT PtT
  wireSignalHdrT lpubT wireSaltCtT lctT fig8HdrT fig8PubAdT slotAdT fsSendStT fsRecvStT
  fsRrT derivedMsgKeysT OTCCATag FSAEADTag coinOnlyBaseIface saltPrfTargetIface
  wireOtccaTargetIface slotOtccaTargetIface fsaeadPubTargetIface fsaeadPubCodec fsaeadRatchetCodec)

namespace Computational.Proofs.ReductionDsl.FsAtomicBounds

open OracleSpec OracleComp
open CryptoGames (Party AEADScheme MACScheme WireAEAD)
open CryptoGames.CBC (Plain nBlocks)
open CryptoGames.Ratchet.LibsignalInst (Salt32 LibsignalCiphertextWithSalt32 LibsignalMsgPublicPart
  lPubOf lChainPRG lAeadR lIdeal)
open CryptoGames.SM.Construction (Header)
open CryptoGames.LibsignalSession (Crypto PublicKey IdentityKey SignalHeader
  SignalMessageProtoCodec maxForwardJumps)
open CryptoGames.FSAEAD (RatchetSenderState RatchetReceiverState)
open CryptoVerification.LibsignalProtoCodec (protoSignalCodec)
open CryptoVerification.LibsignalSession (LCt fsSlotCount ratchetCostBudget
  ratchetFsAdapterBudget fsRatchetCostBudget GRedBounded GTwoStageBounded
  FsCostedReds fsCostedBounds gredBounded_of_bounds)
open Computational.Proofs.ReductionDsl.MacroLift (mapTy gTwoStageBounded_of_bounds
  dummyTwoStageRed dummyTwoStageRed_totalCost dummyTwoStageRed_size dummyTwoStageRed_totalQueries
  guardTwoStageRed)
open Computational.Proofs.ReductionDsl.FsAtomicMacros (PureMacroBundle exprCostBound compCostBound
  castHandle compilePureRed compilePureRed_totalCost_le compilePureRed_size_le
  compilePureRed_size_le_nodes compilePureRed_totalQueries_le
  compilePureTwoStageRed compilePureTwoStageRed_totalCost_le_UB compilePureTwoStageRed_size_le
  compilePureTwoStageRed_size_le_nodes compilePureTwoStageRed_totalQueries_le)
open Computational.Proofs.ReductionDsl.FsAtomicOps (clampedProtoSignalCodec
  opPure opPtEncPk opSym pkLitExpr idKeyLitExpr optBytesEqExpr optPtEqExpr eqLpubExpr
  lPubOfExpr lPubOfExpr_cost chainGenExpr chainGenExpr_cost lIdsExpr lIdsExpr_cost
  lHeaderExpr lHeaderExpr_cost eqWireSignalHdrExpr eqWireSignalHdrExpr_cost
  fitPlainExpr fitPlainExpr_cost eqPlainExpr eqPlainExpr_cost eqSaltExpr eqSaltExpr_cost
  saltOfSlotAdExpr saltOfSlotAdExpr_cost eqFig8PubAdExpr eqFig8PubAdExpr_cost
  eqSlotAdExpr eqSlotAdExpr_cost eqWireSaltCtExpr eqWireSaltCtExpr_cost exprWkTop1
  aeadKEncExpr aeadKEncExpr_cost aeadKDecExpr aeadKDecExpr_cost aeadREncExpr aeadREncExpr_cost
  aeadRDecExpr aeadRDecExpr_cost signalEncodeSerOnlyExpr
  sampleU64Comp sampleMsgKeyComp sampleMsgKeyComp_cost
  sampleIdealComp sampleIdealComp_cost)
open Computational.Proofs.ReductionDsl.FsAtomicBundles

scoped macro "unfold_vars" : tactic =>
  `(tactic| try dsimp only [Expr.v0, Expr.v1, Expr.v2, Expr.v3, Expr.v4, Expr.v5, Expr.v6, Expr.v7])


section CostBoundUB

/-- Branch-summing upper bound on `exprCostBound opC`. -/
@[simp, expose] def exprCostBoundUB {S : Sig} {O : Ops S} (opC : O.Op → ℕ) :
    {Γ : List (Ty S)} → {t : Ty S} → Expr O Γ t → ℕ
  | _, _, .var _ | _, _, .unit | _, _, .bool _ | _, _, .none | _, _, .nil => 1
  | _, _, .nat n => bits n
  | _, _, .add a b | _, _, .sub a b | _, _, .lt a b | _, _, .eqN a b
  | _, _, .and a b | _, _, .pair a b | _, _, .cons a b | _, _, .take a b
  | _, _, .letE a b => exprCostBoundUB opC a + exprCostBoundUB opC b + 1
  | _, _, .mulK k a | _, _, .divK k a | _, _, .modK k a => exprCostBoundUB opC a + bits k
  | _, _, .not a | _, _, .fst a | _, _, .snd a | _, _, .inl a | _, _, .inr a
  | _, _, .some a | _, _, .len a | _, _, .tconst a => exprCostBoundUB opC a + 1
  | _, _, .ite c a b | _, _, .caseOpt c a b | _, _, .caseSum c a b =>
    exprCostBoundUB opC c + exprCostBoundUB opC a + exprCostBoundUB opC b + 1
  | _, _, .op o a => exprCostBoundUB opC a + opC o
  | _, _, .appendL K a b => exprCostBoundUB opC a + exprCostBoundUB opC b + K + 1
  | _, _, .findB K l p | _, _, .anyB K l p | _, _, .mapB K l p =>
    exprCostBoundUB opC l + K * (exprCostBoundUB opC p + 1) + 1
  | _, _, .foldrB K l z f =>
    exprCostBoundUB opC l + exprCostBoundUB opC z + K * (exprCostBoundUB opC f + 1) + 1
  | _, _, .tget m i => exprCostBoundUB opC m + exprCostBoundUB opC i + 64
  | _, _, .tset m i a =>
    exprCostBoundUB opC m + exprCostBoundUB opC i + exprCostBoundUB opC a + 128

@[simp] lemma exprCostBound_var {S : Sig} {O : Ops S} (opC : O.Op → ℕ) {Γ : List (Ty S)} {t : Ty S}
    (v : Var Γ t) :
    exprCostBound opC (.var v) = 1 := rfl

@[simp] lemma exprCostBoundUB_var {S : Sig} {O : Ops S} (opC : O.Op → ℕ) {Γ : List (Ty S)} {t : Ty S}
    (v : Var Γ t) :
    exprCostBoundUB opC (.var v) = 1 := rfl

@[simp, expose] def compCostBoundUB {S : Sig} {O : Ops S} {ι : Type} {T : OracleSpec ι} {I : Iface S T}
    (opC : O.Op → ℕ) (sC : I.smp.Samp → ℕ) (qC : I.Tag → ℕ) :
    {Γ : List (Ty S)} → {t : Ty S} → Comp O I Γ t → ℕ
  | _, _, .ret e => exprCostBoundUB opC e + 1
  | _, _, .bind c k => compCostBoundUB opC sC qC c + compCostBoundUB opC sC qC k + 1
  | _, _, .ite b c d | _, _, .caseOpt b c d | _, _, .caseSum b c d =>
    exprCostBoundUB opC b + compCostBoundUB opC sC qC c + compCostBoundUB opC sC qC d + 1
  | _, _, .sample s e => exprCostBoundUB opC e + sC s
  | _, _, .query g e => exprCostBoundUB opC e + qC g
  | _, _, .iter n e body => exprCostBoundUB opC e + n * (compCostBoundUB opC sC qC body + 1) + 1
  | _, _, .findM K l p | _, _, .anyM K l p | _, _, .mapM K l p =>
    exprCostBoundUB opC l + K * (compCostBoundUB opC sC qC p + 1) + 1
  | _, _, .consumeFirstM K l p mk =>
    exprCostBoundUB opC l + K * (compCostBoundUB opC sC qC p + exprCostBoundUB opC mk + 1) + 1
  | _, _, .foldM K l z f =>
    exprCostBoundUB opC l + exprCostBoundUB opC z + K * (compCostBoundUB opC sC qC f + 1) + 1

theorem exprCostBound_le_UB {S : Sig} {O : Ops S} (opC : O.Op → ℕ)
    {Γ : List (Ty S)} {t : Ty S} (e : Expr O Γ t) :
    exprCostBound opC e ≤ exprCostBoundUB opC e := by
  induction e with
  | var _ | unit | bool _ | nat _ | none | nil => rfl
  | add _ _ iha ihb | sub _ _ iha ihb | lt _ _ iha ihb | eqN _ _ iha ihb
  | and _ _ iha ihb | pair _ _ iha ihb | cons _ _ iha ihb | take _ _ iha ihb
  | letE _ _ iha ihb | appendL _ _ _ iha ihb | tget _ _ iha ihb =>
    simp only [exprCostBound, exprCostBoundUB]; omega
  | mulK _ _ iha | divK _ _ iha | modK _ _ iha | not _ iha | fst _ iha | snd _ iha
  | inl _ iha | inr _ iha | some _ iha | len _ iha | tconst _ iha | op _ _ iha =>
    simp only [exprCostBound, exprCostBoundUB]; omega
  | ite _ a b ihc iha ihb | caseOpt _ a b ihc iha ihb | caseSum _ a b ihc iha ihb =>
    have hm : max (exprCostBound opC a) (exprCostBound opC b) ≤
        exprCostBoundUB opC a + exprCostBoundUB opC b := by omega
    simp only [exprCostBound, exprCostBoundUB]; omega
  | findB K _ _ ihl ihp | anyB K _ _ ihl ihp | mapB K _ _ ihl ihp =>
    have hm := Nat.mul_le_mul_left K (Nat.add_le_add_right ihp 1)
    simp only [exprCostBound, exprCostBoundUB]; omega
  | foldrB K _ _ _ ihl ihz ihf =>
    have hm := Nat.mul_le_mul_left K (Nat.add_le_add_right ihf 1)
    simp only [exprCostBound, exprCostBoundUB]; omega
  | tset _ _ _ ihm ihi iha =>
    simp only [exprCostBound, exprCostBoundUB]; omega

theorem compCostBound_le_UB {S : Sig} {O : Ops S} {ι : Type} {T : OracleSpec ι} {I : Iface S T}
    (opC : O.Op → ℕ) (sC : I.smp.Samp → ℕ) (qC : I.Tag → ℕ)
    {Γ : List (Ty S)} {t : Ty S} (c : Comp O I Γ t) :
    compCostBound opC sC qC c ≤ compCostBoundUB opC sC qC c := by
  induction c with
  | ret e =>
    have he := exprCostBound_le_UB opC e
    simp only [compCostBound, compCostBoundUB]; omega
  | bind _ _ ihc ihk =>
    simp only [compCostBound, compCostBoundUB]; omega
  | ite b c d ihc ihd | caseOpt b c d ihc ihd | caseSum b c d ihc ihd =>
    have hb := exprCostBound_le_UB opC b
    have hm : max (compCostBound opC sC qC c) (compCostBound opC sC qC d) ≤
        compCostBoundUB opC sC qC c + compCostBoundUB opC sC qC d := by omega
    simp only [compCostBound, compCostBoundUB]; omega
  | sample _ e | query _ e =>
    have he := exprCostBound_le_UB opC e
    simp only [compCostBound, compCostBoundUB]; omega
  | iter n e _ ihb =>
    have he := exprCostBound_le_UB opC e
    have hm := Nat.mul_le_mul_left n (Nat.add_le_add_right ihb 1)
    simp only [compCostBound, compCostBoundUB]; omega
  | findM K l _ ihp | anyM K l _ ihp | mapM K l _ ihp =>
    have hl := exprCostBound_le_UB opC l
    have hm := Nat.mul_le_mul_left K (Nat.add_le_add_right ihp 1)
    simp only [compCostBound, compCostBoundUB]; omega
  | consumeFirstM K l _ mk ihp =>
    have hl := exprCostBound_le_UB opC l
    have hmk := exprCostBound_le_UB opC mk
    have hm := Nat.mul_le_mul_left K (Nat.add_le_add_right (Nat.add_le_add ihp hmk) 1)
    simp only [compCostBound, compCostBoundUB]; omega
  | foldM K l z _ ihf =>
    have hl := exprCostBound_le_UB opC l
    have hz := exprCostBound_le_UB opC z
    have hm := Nat.mul_le_mul_left K (Nat.add_le_add_right ihf 1)
    simp only [compCostBound, compCostBoundUB]; omega

theorem caseSum_compCostBound_le {S : Sig} {O : Ops S} {ι : Type} {T : OracleSpec ι} {I : Iface S T}
    (opC : O.Op → ℕ) (sC : I.smp.Samp → ℕ) (qC : I.Tag → ℕ)
    {Γ : List (Ty S)} {t u v : Ty S}
    (e : Expr O Γ (.sum t u)) (l : Comp O I (t :: Γ) v) (r : Comp O I (u :: Γ) v) {b : ℕ}
    (he : exprCostBoundUB opC e ≤ 2) (hl : compCostBound opC sC qC l ≤ b)
    (hr : compCostBound opC sC qC r ≤ b) :
    compCostBound opC sC qC (.caseSum e l r) ≤ b + 3 := by
  have he' := (exprCostBound_le_UB opC e).trans he
  have hm := max_le hl hr
  simp only [compCostBound]; omega

theorem compilePureRed_totalCost_le_UB {S₁ S₂ : Sig} {O₁ : Ops S₁} {O₂ : Ops S₂}
    {ι κ : Type} {T : OracleSpec.{0, 0} ι} {G : OracleSpec.{0, 0} κ}
    {I₁ : Iface S₁ T} {I₂ : Iface S₂ T}
    {C₁ : GameCodec S₁ G} (C₂ : GameCodec S₂ G)
    (M : PureMacroBundle O₁ O₂ I₁ I₂) {rIn₁ : Ty S₁}
    (R : CostedReduction O₁ I₁ G C₁ rIn₁ .unit .bool .bool)
    (hQ : mapTy M.baseTy C₁.Q = C₂.Q) (hR : mapTy M.baseTy C₁.R = C₂.R)
    (opC : O₁.Op → ℕ) (sC : I₁.smp.Samp → ℕ) (qC : I₁.Tag → ℕ)
    (hOp : ∀ o, (M.opMacro o).cost + 1 ≤ opC o)
    (hSamp : ∀ s, (M.sampMacro s).cost + 2 ≤ sC s)
    (hQuery : ∀ g, (M.queryMacro g).cost + 2 ≤ qC g)
    {cInit cHandle cFin : ℕ}
    (hi : compCostBound opC sC qC R.init ≤ cInit)
    (hh : compCostBound opC sC qC R.handle ≤ cHandle)
    (hf : compCostBound opC sC qC R.finish ≤ cFin) (q : ℕ) :
    (compilePureRed C₂ M R hQ hR).totalCost q ≤
      cInit + q * max I₂.uCost (cHandle + C₂.codecCost) + cFin := by
  have h1 := compilePureRed_totalCost_le C₂ M R hQ hR opC sC qC hOp hSamp hQuery q
  have hmax : max I₂.uCost (compCostBound opC sC qC R.handle + C₂.codecCost) ≤
      max I₂.uCost (cHandle + C₂.codecCost) :=
    max_le_max le_rfl (Nat.add_le_add_right hh _)
  have hmul := Nat.mul_le_mul_left q hmax
  omega

lemma add_one_le_two_pow (n : ℕ) : n + 1 ≤ 2 ^ n := by
  induction n with
  | zero => exact le_rfl
  | succ n ih =>
    have hp : 2 ^ (n + 1) = 2 * 2 ^ n := by ring
    rw [hp]; omega

lemma bits_le_qR_add_15 {x qR : ℕ} (hx : x ≤ qR + 25002) : bits x ≤ qR + 15 := by
  refine ReductionDsl.bits_le_of_lt ?_ (by omega)
  have h1 : qR + 1 ≤ 2 ^ qR := add_one_le_two_pow qR
  have h2 : (2 : ℕ) ^ (qR + 15) = 32768 * 2 ^ qR := by rw [Nat.pow_add]; norm_num; ring
  omega

lemma bits_le_bits_add_16 {x qR : ℕ} (hx : x ≤ qR + 25002) : bits x ≤ bits qR + 16 := by
  refine ReductionDsl.bits_le_of_lt ?_ (by omega)
  have h1 : qR < 2 ^ bits qR := by
    simpa only [bits] using Nat.lt_pow_succ_log_self (by norm_num : 1 < 2) qR
  have h2 : 1 ≤ 2 ^ bits qR := Nat.one_le_two_pow
  have h3 : (2 : ℕ) ^ (bits qR + 16) = 65536 * 2 ^ bits qR := by rw [Nat.pow_add]; norm_num; ring
  omega

lemma bits_25000_le : bits 25000 ≤ 16 :=
  ReductionDsl.bits_le_of_lt (by norm_num) (by omega)

lemma bits_25001_le : bits 25001 ≤ 16 :=
  ReductionDsl.bits_le_of_lt (by norm_num) (by omega)

lemma reductionSizeBudget_eq : reductionSizeBudget = 16777216 := rfl

lemma fs_poly_le_ratchetCostBudget (qR qep : ℕ) :
    100000000 + 200000000 * qR + 100000000 * qR ^ 2 ≤ ratchetCostBudget qR qep := by
  have hmfj : maxForwardJumps = 25000 := rfl
  have hbits : 1 ≤ bits qep := ReductionDsl.one_le_bits qep
  have hfac : 25001 ≤ maxForwardJumps + bits qep := by omega
  have hbase : 2 ^ 12 * (qR + 1) ^ 2 * 25001 ≤ ratchetCostBudget qR qep := by
    unfold ratchetCostBudget
    exact Nat.mul_le_mul_left _ hfac
  nlinarith

lemma qR_le_ratchetCostBudget (qR qep : ℕ) : qR ≤ ratchetCostBudget qR qep := by
  have := fs_poly_le_ratchetCostBudget qR qep
  omega

lemma size_le_budget_of_qR {sz C₀ C₁ qR qep : ℕ}
    (h₀ : C₀ ≤ 16777216) (h₁ : C₁ ≤ 4096)
    (hR : sz ≤ C₀ + C₁ * bits qR) :
    sz ≤ reductionSizeBudget + 2 ^ 12 * bits (ratchetCostBudget qR qep) := by
  have hbit : C₁ * bits qR ≤ 2 ^ 12 * bits (ratchetCostBudget qR qep) :=
    Nat.le_trans
      (Nat.mul_le_mul_left C₁
        (Computational.Proofs.ReductionDsl.SizeBudgetBridge.bits_mono
          (qR_le_ratchetCostBudget qR qep)))
      (Nat.mul_le_mul_right _ (by omega))
  simp only [reductionSizeBudget_eq]
  omega

lemma fs_poly_le_ratchetFsAdapterBudget (qR qep : ℕ) :
    16000000 + 16000000 * qR + 1000 * qR ^ 2 ≤ ratchetFsAdapterBudget qR qep := by
  unfold ratchetFsAdapterBudget
  nlinarith

lemma qR_le_ratchetFsAdapterBudget (qR qep : ℕ) :
    qR ≤ ratchetFsAdapterBudget qR qep := by
  have := fs_poly_le_ratchetFsAdapterBudget qR qep
  omega

lemma size_le_adapter_budget_of_qR {sz C₀ C₁ qR qep : ℕ}
    (h₀ : C₀ ≤ 16777216) (h₁ : C₁ ≤ 4096)
    (hR : sz ≤ C₀ + C₁ * bits qR) :
    sz ≤ reductionSizeBudget + 2 ^ 12 * bits (ratchetFsAdapterBudget qR qep) := by
  have hbit : C₁ * bits qR ≤ 2 ^ 12 * bits (ratchetFsAdapterBudget qR qep) :=
    Nat.le_trans
      (Nat.mul_le_mul_left C₁
        (Computational.Proofs.ReductionDsl.SizeBudgetBridge.bits_mono
          (qR_le_ratchetFsAdapterBudget qR qep)))
      (Nat.mul_le_mul_right _ (by omega))
  simp only [reductionSizeBudget_eq]
  omega

lemma fs_poly_le_fsRatchetCostBudget (qR qep : ℕ) :
    100000000 + 130000000 * qR + 10000 * qR ^ 2 ≤ fsRatchetCostBudget qR qep := by
  have hmfj : maxForwardJumps = 25000 := rfl
  have hbits : 1 ≤ bits qep := ReductionDsl.one_le_bits qep
  unfold fsRatchetCostBudget
  refine le_min ?_ ?_
  · have hfac : 25001 ≤ maxForwardJumps + bits qep := by omega
    have hbase : 2 ^ 12 * (qR + 1) ^ 2 * 25001 ≤ ratchetCostBudget qR qep := by
      unfold ratchetCostBudget
      exact Nat.mul_le_mul_left _ hfac
    nlinarith
  · have hfac2 : 25001 ≤ maxForwardJumps + bits qep := by omega
    have hbase2 : 2 ^ 14 * (qR + 1) ^ 2 + 2 ^ 15 * (qR + 1) * 25001 ≤
        2 ^ 14 * (qR + 1) ^ 2 + 2 ^ 15 * (qR + 1) * (maxForwardJumps + bits qep) :=
      Nat.add_le_add_left (Nat.mul_le_mul_left _ hfac2) _
    nlinarith

lemma qR_le_fsRatchetCostBudget (qR qep : ℕ) :
    qR ≤ fsRatchetCostBudget qR qep := by
  have := fs_poly_le_fsRatchetCostBudget qR qep
  omega

lemma size_le_fs_budget_of_qR {sz C₀ C₁ qR qep : ℕ}
    (h₀ : C₀ ≤ 16777216) (h₁ : C₁ ≤ 4096)
    (hR : sz ≤ C₀ + C₁ * bits qR) :
    sz ≤ reductionSizeBudget + 2 ^ 12 * bits (fsRatchetCostBudget qR qep) := by
  have hbit : C₁ * bits qR ≤ 2 ^ 12 * bits (fsRatchetCostBudget qR qep) :=
    Nat.le_trans
      (Nat.mul_le_mul_left C₁
        (Computational.Proofs.ReductionDsl.SizeBudgetBridge.bits_mono
          (qR_le_fsRatchetCostBudget qR qep)))
      (Nat.mul_le_mul_right _ (by omega))
  simp only [reductionSizeBudget_eq]
  omega

end CostBoundUB

section MacroBounds

variable {Pt : Type} [DecidableEq Pt]
  (C : Crypto) (ℓ : ℕ) (encT : Pt → PublicKey) (idOf : Party → IdentityKey)

@[expose] def pubOpC : Unit → ℕ := fun _ => 31320
def pubQC : CryptoGames.FSAEAD.Costed.FsaeadTag → ℕ := fun _ => 94000

@[expose] def hybOpCU : (Unit ⊕ CryptoGames.OTCCA.Costed.OtccaOp) → ℕ
  | .inl () => 45
  | .inr .enc => 377000
  | .inr .dec => 439000
  | .inr .saltOf => 5
  | .inr .eqAD => 260
  | .inr .eqM => 31260
  | .inr .eqC => 140
  | .inr .eqSalt => 5

@[expose] def prgSC : ((Empty ⊕ Unit) ⊕ UniformSamplerTag Bool) → ℕ
  | .inl (.inl e) => nomatch e
  | .inl (.inr ()) => 2190000
  | .inr (.index N) => bits N + 4
  | .inr .bool | .inr (.base _) => 10

@[expose] def multiSC : (Unit ⊕ UniformSamplerTag Bool) → ℕ
  | .inl () => 2190000
  | .inr (.index N) => bits N + 4
  | .inr .bool | .inr (.base _) => 10

@[expose] def multiQC : CryptoGames.OTCCA.Costed.OtccaTag → ℕ := fun _ => 63000

@[expose] def swOpCU :
    (CryptoGames.OTCCA.Costed.OtccaOp ⊕
      (CryptoGames.OTCCA.Costed.OtccaOp ⊕ CryptoGames.AEAD.Costed.WireOp)) → ℕ
  | .inl .enc | .inr (.inl .enc) => 377000
  | .inl .dec | .inr (.inl .dec) => 439000
  | .inl .saltOf | .inr (.inl .saltOf) => 10
  | .inl .eqAD | .inr (.inl .eqAD) => 280
  | .inl .eqM | .inr (.inl .eqM) | .inr (.inr .fitPlainOp) => 31260
  | .inl .eqC | .inr (.inl .eqC) => 140
  | .inl .eqSalt | .inr (.inl .eqSalt) => 10
  | .inr (.inr .idsOf) => 160
  | .inr (.inr .hdrOf) => 150
  | .inr (.inr .eqHdr) => 240

@[expose] def slotSwSC : (Unit ⊕ UniformSamplerTag Bool) → ℕ
  | .inl () => 2190000
  | .inr (.index N) => bits N + 4
  | .inr (.base false) => 30
  | .inr .bool | .inr (.base true) => 10

@[expose] def slotSwQC : CryptoGames.OTCCA.Costed.OtccaTag → ℕ := fun _ => 63000

@[expose] def lSaltSC : ((Empty ⊕ Unit) ⊕ UniformSamplerTag Empty) → ℕ
  | .inl (.inl e) => nomatch e
  | .inl (.inr ()) => 2190000
  | .inr (.base e) => nomatch e
  | .inr (.index N) => bits N + 4
  | .inr .bool => 10

@[expose] def lSaltQC : Unit → ℕ := fun _ => 10

@[expose] def lWireSC : (Empty ⊕ UniformSamplerTag Empty) → ℕ
  | .inl e => nomatch e
  | .inr (.base e) => nomatch e
  | .inr (.index N) => bits N + 4
  | .inr .bool => 10

@[expose] def lWireQC : CryptoGames.AEAD.Costed.WireTag → ℕ := fun _ => 63000

lemma hybOpMacro_cost_le (hℓ : ℓ < 10 ^ 6) (o) :
    (hybOpMacro (Pt := Pt) C ℓ encT idOf o).cost + 1 ≤ hybOpCU o := by
  have hdiv : ℓ / 32 ≤ 31250 := by omega
  rcases o with ⟨⟩ | (_ | _ | _ | _ | _ | _ | _)
  · have := chainGenExpr_cost ℓ Pt C encT (Γ := [.prod .nat BV256]) (.snd (.var .zero))
    dsimp only [hybOpMacro, Ops.sum, Sum.elim, CryptoGames.PRG.Costed.prgOps, mapTy, hybBaseTy]
    simp only [hybOpCU, Expr.cost] at this ⊢; omega
  · have := aeadREncExpr_cost ℓ Pt C encT idOf
    dsimp only [hybOpMacro, Ops.sum, Sum.elim, CryptoGames.OTCCA.Costed.otccaOps, mapTy, hybBaseTy]
    simp only [hybOpCU] at this ⊢; omega
  · have := aeadRDecExpr_cost ℓ Pt C encT idOf
    dsimp only [hybOpMacro, Ops.sum, Sum.elim, CryptoGames.OTCCA.Costed.otccaOps, mapTy, hybBaseTy]
    simp only [hybOpCU] at this ⊢; omega
  · dsimp only [hybOpMacro, Ops.sum, Sum.elim, CryptoGames.OTCCA.Costed.otccaOps, mapTy, hybBaseTy]
    simp [hybOpCU, Expr.cost]
  · have := eqFig8PubAdExpr_cost ℓ Pt C encT (Γ := [.prod fig8PubAdT fig8PubAdT])
      (.fst (.var .zero)) (.snd (.var .zero))
    dsimp only [hybOpMacro, Ops.sum, Sum.elim, CryptoGames.OTCCA.Costed.otccaOps, mapTy, hybBaseTy]
    simp only [hybOpCU, Expr.cost] at this ⊢; omega
  · have := eqPlainExpr_cost ℓ Pt C encT (Γ := [.prod PlainT PlainT])
      (.fst (.var .zero)) (.snd (.var .zero))
    dsimp only [hybOpMacro, Ops.sum, Sum.elim, CryptoGames.OTCCA.Costed.otccaOps, mapTy, hybBaseTy]
    simp only [hybOpCU, Expr.cost] at this ⊢; omega
  · have := eqWireSaltCtExpr_cost ℓ Pt C encT (Γ := [.prod wireSaltCtT wireSaltCtT])
      (.fst (.var .zero)) (.snd (.var .zero))
    dsimp only [hybOpMacro, Ops.sum, Sum.elim, CryptoGames.OTCCA.Costed.otccaOps, mapTy, hybBaseTy]
    simp only [hybOpCU, Expr.cost] at this ⊢; omega
  · dsimp only [hybOpMacro, Ops.sum, Sum.elim, CryptoGames.OTCCA.Costed.otccaOps, mapTy, hybBaseTy]
    simp [hybOpCU, Expr.cost]

end MacroBounds

section MacroBounds2

variable {Pt : Type} [DecidableEq Pt]
  (C : Crypto) (ℓ : ℕ) (encT : Pt → PublicKey) (idOf : Party → IdentityKey)

omit [DecidableEq Pt] in
lemma pubOpMacro_cost_le (hℓ : ℓ < 10 ^ 6) (o) :
    ((pubMacroBundle (Pt := Pt) C ℓ encT).opMacro o).cost + 1 ≤ pubOpC o := by
  have hdiv : ℓ / 32 ≤ 31250 := by omega
  cases o
  have h := lPubOfExpr_cost ℓ Pt C encT (Γ := [lctT]) (.snd (.var .zero))
  dsimp only [pubMacroBundle, CryptoGames.FSAEAD.Costed.fsOps, mapTy, pubBaseTy]
  simp only [pubOpC, Expr.cost] at h ⊢; omega

omit [DecidableEq Pt] in
lemma pubQueryMacro_cost_le (hℓ : ℓ < 10 ^ 6) (g) :
    ((pubMacroBundle (Pt := Pt) C ℓ encT).queryMacro g).cost + 2 ≤ pubQC g := by
  have hdiv : ℓ / 32 ≤ 31250 := by omega
  cases g <;>
    (dsimp only [pubMacroBundle, CryptoGames.FSAEAD.Costed.fsaeadIface, mapTy, pubBaseTy]
     simp only [pubQC, Comp.cost, Expr.cost]; omega)

lemma swOpMacro_cost_le (hℓ : ℓ < 10 ^ 6) (o) :
    (swOpMacro (Pt := Pt) C ℓ encT idOf o).cost + 1 ≤ swOpCU o := by
  have hdiv : ℓ / 32 ≤ 31250 := by omega
  rcases o with (_ | _ | _ | _ | _ | _ | _) | ((_ | _ | _ | _ | _ | _ | _) | (_ | _ | _ | _))
  · have := aeadKEncExpr_cost ℓ Pt C encT idOf
    dsimp only [swOpMacro, CryptoGames.AEAD.Costed.saltWireOps, Ops.sum, Sum.elim,
      CryptoGames.OTCCA.Costed.otccaOps, CryptoGames.AEAD.Costed.slotAdTy,
      CryptoGames.AEAD.Costed.lctTy, mapTy, swBaseTy]
    simp only [swOpCU] at this ⊢; omega
  · have := aeadKDecExpr_cost ℓ Pt C encT idOf
    dsimp only [swOpMacro, CryptoGames.AEAD.Costed.saltWireOps, Ops.sum, Sum.elim,
      CryptoGames.OTCCA.Costed.otccaOps, CryptoGames.AEAD.Costed.slotAdTy,
      CryptoGames.AEAD.Costed.lctTy, mapTy, swBaseTy]
    simp only [swOpCU] at this ⊢; omega
  · have := saltOfSlotAdExpr_cost ℓ Pt C encT (Γ := [slotAdT]) (.var .zero)
    dsimp only [swOpMacro, CryptoGames.AEAD.Costed.saltWireOps, Ops.sum, Sum.elim,
      CryptoGames.OTCCA.Costed.otccaOps, CryptoGames.AEAD.Costed.slotAdTy, mapTy, swBaseTy]
    simp only [swOpCU, Expr.cost] at this ⊢; omega
  · have := eqSlotAdExpr_cost ℓ Pt C encT (Γ := [.prod slotAdT slotAdT])
      (.fst (.var .zero)) (.snd (.var .zero))
    dsimp only [swOpMacro, CryptoGames.AEAD.Costed.saltWireOps, Ops.sum, Sum.elim,
      CryptoGames.OTCCA.Costed.otccaOps, CryptoGames.AEAD.Costed.slotAdTy, mapTy, swBaseTy]
    simp only [swOpCU, Expr.cost] at this ⊢; omega
  · have := eqPlainExpr_cost ℓ Pt C encT (Γ := [.prod PlainT PlainT])
      (.fst (.var .zero)) (.snd (.var .zero))
    dsimp only [swOpMacro, CryptoGames.AEAD.Costed.saltWireOps, Ops.sum, Sum.elim,
      CryptoGames.OTCCA.Costed.otccaOps, mapTy, swBaseTy]
    simp only [swOpCU, Expr.cost] at this ⊢; omega
  · have := eqWireSaltCtExpr_cost ℓ Pt C encT (Γ := [.prod wireSaltCtT wireSaltCtT])
      (.fst (.var .zero)) (.snd (.var .zero))
    dsimp only [swOpMacro, CryptoGames.AEAD.Costed.saltWireOps, Ops.sum, Sum.elim,
      CryptoGames.OTCCA.Costed.otccaOps, CryptoGames.AEAD.Costed.lctTy, mapTy, swBaseTy]
    simp only [swOpCU, Expr.cost] at this ⊢; omega
  · have := eqSaltExpr_cost ℓ Pt C encT (Γ := [.prod BV256 BV256])
      (.fst (.var .zero)) (.snd (.var .zero))
    dsimp only [swOpMacro, CryptoGames.AEAD.Costed.saltWireOps, Ops.sum, Sum.elim,
      CryptoGames.OTCCA.Costed.otccaOps, mapTy, swBaseTy]
    simp only [swOpCU, Expr.cost] at this ⊢; omega
  · have := aeadREncExpr_cost ℓ Pt C encT idOf
    dsimp only [swOpMacro, CryptoGames.AEAD.Costed.saltWireOps, Ops.sum, Sum.elim,
      CryptoGames.OTCCA.Costed.otccaOps, CryptoGames.AEAD.Costed.slotAdTy,
      CryptoGames.AEAD.Costed.lctTy, mapTy, swBaseTy]
    simp only [swOpCU] at this ⊢; omega
  · have := aeadRDecExpr_cost ℓ Pt C encT idOf
    dsimp only [swOpMacro, CryptoGames.AEAD.Costed.saltWireOps, Ops.sum, Sum.elim,
      CryptoGames.OTCCA.Costed.otccaOps, CryptoGames.AEAD.Costed.slotAdTy,
      CryptoGames.AEAD.Costed.lctTy, mapTy, swBaseTy]
    simp only [swOpCU] at this ⊢; omega
  · have := saltOfSlotAdExpr_cost ℓ Pt C encT (Γ := [slotAdT]) (.var .zero)
    dsimp only [swOpMacro, CryptoGames.AEAD.Costed.saltWireOps, Ops.sum, Sum.elim,
      CryptoGames.OTCCA.Costed.otccaOps, CryptoGames.AEAD.Costed.slotAdTy, mapTy, swBaseTy]
    simp only [swOpCU, Expr.cost] at this ⊢; omega
  · have := eqSlotAdExpr_cost ℓ Pt C encT (Γ := [.prod slotAdT slotAdT])
      (.fst (.var .zero)) (.snd (.var .zero))
    dsimp only [swOpMacro, CryptoGames.AEAD.Costed.saltWireOps, Ops.sum, Sum.elim,
      CryptoGames.OTCCA.Costed.otccaOps, CryptoGames.AEAD.Costed.slotAdTy, mapTy, swBaseTy]
    simp only [swOpCU, Expr.cost] at this ⊢; omega
  · have := eqPlainExpr_cost ℓ Pt C encT (Γ := [.prod PlainT PlainT])
      (.fst (.var .zero)) (.snd (.var .zero))
    dsimp only [swOpMacro, CryptoGames.AEAD.Costed.saltWireOps, Ops.sum, Sum.elim,
      CryptoGames.OTCCA.Costed.otccaOps, mapTy, swBaseTy]
    simp only [swOpCU, Expr.cost] at this ⊢; omega
  · have := eqWireSaltCtExpr_cost ℓ Pt C encT (Γ := [.prod wireSaltCtT wireSaltCtT])
      (.fst (.var .zero)) (.snd (.var .zero))
    dsimp only [swOpMacro, CryptoGames.AEAD.Costed.saltWireOps, Ops.sum, Sum.elim,
      CryptoGames.OTCCA.Costed.otccaOps, CryptoGames.AEAD.Costed.lctTy, mapTy, swBaseTy]
    simp only [swOpCU, Expr.cost] at this ⊢; omega
  · have := eqSaltExpr_cost ℓ Pt C encT (Γ := [.prod BV256 BV256])
      (.fst (.var .zero)) (.snd (.var .zero))
    dsimp only [swOpMacro, CryptoGames.AEAD.Costed.saltWireOps, Ops.sum, Sum.elim,
      CryptoGames.OTCCA.Costed.otccaOps, mapTy, swBaseTy]
    simp only [swOpCU, Expr.cost] at this ⊢; omega
  · have := lIdsExpr_cost ℓ Pt C encT idOf (Γ := [slotAdT]) (.fst (.fst (.snd (.var .zero))))
    dsimp only [swOpMacro, CryptoGames.AEAD.Costed.saltWireOps, Ops.sum, Sum.elim,
      CryptoGames.AEAD.Costed.wireOps, CryptoGames.AEAD.Costed.slotAdTy, mapTy, swBaseTy]
    simp only [swOpCU, Expr.cost] at this ⊢; omega
  · have := lHeaderExpr_cost ℓ Pt C encT (Γ := [slotAdT]) (.var .zero)
    dsimp only [swOpMacro, CryptoGames.AEAD.Costed.saltWireOps, Ops.sum, Sum.elim,
      CryptoGames.AEAD.Costed.wireOps, CryptoGames.AEAD.Costed.slotAdTy, mapTy, swBaseTy]
    simp only [swOpCU, Expr.cost] at this ⊢; omega
  · have := eqWireSignalHdrExpr_cost ℓ Pt C encT (Γ := [.prod wireSignalHdrT wireSignalHdrT])
      (.fst (.var .zero)) (.snd (.var .zero))
    dsimp only [swOpMacro, CryptoGames.AEAD.Costed.saltWireOps, Ops.sum, Sum.elim,
      CryptoGames.AEAD.Costed.wireOps, mapTy, swBaseTy]
    simp only [swOpCU, Expr.cost] at this ⊢; omega
  · have := fitPlainExpr_cost ℓ Pt C encT (Γ := [B 32]) (.var .zero)
    dsimp only [swOpMacro, CryptoGames.AEAD.Costed.saltWireOps, Ops.sum, Sum.elim,
      CryptoGames.AEAD.Costed.wireOps, mapTy, swBaseTy]
    simp only [swOpCU, Expr.cost] at this ⊢; omega

lemma prgSampMacro_cost_le (hℓ : ℓ < 10 ^ 6) (s) :
    ((prgZeroMacroBundle (Pt := Pt) C ℓ encT idOf).sampMacro s).cost + 2 ≤ prgSC s := by
  have hdiv : ℓ / 32 ≤ 31250 := by omega
  rcases s with (e | ⟨⟩) | (_ | N | (_ | _))
  · exact nomatch e
  · have h := sampleIdealComp_cost ℓ Pt C encT (I := coinOnlyBaseIface ℓ Pt)
      (fun b => Comp.sample (I := coinOnlyBaseIface ℓ Pt) (UniformSamplerTag.base b) .unit)
      (fun b => by cases b <;> simp [Comp.cost, Expr.cost, AtomicBaseUnif.cost])
    dsimp only [prgZeroMacroBundle, Iface.withSamp, Samplers.sum, Sum.elim,
      CryptoGames.OTCCA.Costed.idealSamplers, mapTy, hybBaseTy, prgSC]
    omega
  all_goals
    dsimp only [prgZeroMacroBundle, coinOnlyBaseIface, atomicBaseSamplers, unifSamplers]
    simp only [prgSC, Comp.cost, Expr.cost, AtomicBaseUnif.cost]; omega

lemma multiSampMacro_cost_le (hℓ : ℓ < 10 ^ 6) (s) :
    ((multiMacroBundle (Pt := Pt) C ℓ encT idOf).sampMacro s).cost + 2 ≤ multiSC s := by
  have hdiv : ℓ / 32 ≤ 31250 := by omega
  cases s with
  | inl u =>
    cases u
    have h := sampleIdealComp_cost ℓ Pt C encT (I := slotOtccaTargetIface ℓ Pt)
      (fun b => Comp.sample (I := slotOtccaTargetIface ℓ Pt) (UniformSamplerTag.base b) .unit)
      (fun b => by cases b <;> simp [Comp.cost, Expr.cost, AtomicBaseUnif.cost])
    dsimp only [multiMacroBundle, Iface.withSamp, Samplers.sum, Sum.elim,
      CryptoGames.OTCCA.Costed.otccaIface, CryptoGames.OTCCA.Costed.idealSamplers,
      mapTy, hybBaseTy, multiSC]
    omega
  | inr t =>
    rcases t with _ | N | (_ | _) <;>
      (dsimp only [multiMacroBundle, slotOtccaTargetIface, atomicBaseSamplers, unifSamplers]
       simp only [multiSC, Comp.cost, Expr.cost, AtomicBaseUnif.cost]; omega)

lemma multiQueryMacro_cost_le (hℓ : ℓ < 10 ^ 6) (g) :
    ((multiMacroBundle (Pt := Pt) C ℓ encT idOf).queryMacro g).cost + 2 ≤ multiQC g := by
  have hdiv : ℓ / 32 ≤ 31250 := by omega
  cases g <;>
    (dsimp only [multiMacroBundle, Iface.withSamp, CryptoGames.OTCCA.Costed.otccaIface,
      mapTy, hybBaseTy]
     simp only [multiQC, Comp.cost, Expr.cost]; omega)

lemma slotSwSampMacro_cost_le (hℓ : ℓ < 10 ^ 6) (s) :
    ((slotSwMacroBundle (Pt := Pt) C ℓ encT idOf).sampMacro s).cost + 2 ≤ slotSwSC s := by
  have hdiv : ℓ / 32 ≤ 31250 := by omega
  cases s with
  | inl u =>
    cases u
    have h := sampleIdealComp_cost ℓ Pt C encT (I := slotOtccaTargetIface ℓ Pt)
      (fun b => Comp.sample (I := slotOtccaTargetIface ℓ Pt) (UniformSamplerTag.base b) .unit)
      (fun b => by cases b <;> simp [Comp.cost, Expr.cost, AtomicBaseUnif.cost])
    dsimp only [slotSwMacroBundle, CryptoGames.AEAD.Costed.slotOtccaIface, Iface.withSamp,
      Samplers.sum, Sum.elim, CryptoGames.OTCCA.Costed.otccaIface,
      CryptoGames.OTCCA.Costed.idealSamplers, CryptoGames.AEAD.Costed.slotAdTy,
      CryptoGames.AEAD.Costed.lctTy, mapTy, swBaseTy, slotSwSC]
    omega
  | inr t =>
    rcases t with _ | N | (_ | _)
    · dsimp only [slotSwMacroBundle, slotOtccaTargetIface, atomicBaseSamplers, unifSamplers]
      simp [slotSwSC, Comp.cost, Expr.cost]
    · dsimp only [slotSwMacroBundle, slotOtccaTargetIface, atomicBaseSamplers, unifSamplers]
      simp only [slotSwSC, Comp.cost, Expr.cost]; omega
    · dsimp only [slotSwMacroBundle, slotSwSC]
      exact Nat.le_trans (Nat.add_le_add_right
        (sampleMsgKeyComp_cost ℓ Pt C encT (I := slotOtccaTargetIface ℓ Pt)
          (fun b => Comp.sample (I := slotOtccaTargetIface ℓ Pt) (UniformSamplerTag.base b) .unit)
          (fun b => by cases b <;> simp [Comp.cost, Expr.cost, AtomicBaseUnif.cost])) 2) (by omega)
    · dsimp only [slotSwMacroBundle, slotOtccaTargetIface, atomicBaseSamplers, unifSamplers]
      simp [slotSwSC, Comp.cost, Expr.cost, AtomicBaseUnif.cost]

lemma slotSwQueryMacro_cost_le (hℓ : ℓ < 10 ^ 6) (g) :
    ((slotSwMacroBundle (Pt := Pt) C ℓ encT idOf).queryMacro g).cost + 2 ≤ slotSwQC g := by
  have hdiv : ℓ / 32 ≤ 31250 := by omega
  cases g <;>
    (dsimp only [slotSwMacroBundle, CryptoGames.AEAD.Costed.slotOtccaIface, Iface.withSamp,
      CryptoGames.OTCCA.Costed.otccaIface, CryptoGames.AEAD.Costed.slotAdTy,
      CryptoGames.AEAD.Costed.lctTy, mapTy, swBaseTy]
     simp only [slotSwQC, Comp.cost, Expr.cost]; omega)

lemma lSaltSampMacro_cost_le (hℓ : ℓ < 10 ^ 6) (s) :
    ((lSaltMacroBundle (Pt := Pt) C ℓ encT idOf).sampMacro s).cost + 2 ≤ lSaltSC s := by
  have hdiv : ℓ / 32 ≤ 31250 := by omega
  rcases s with (e | ⟨⟩) | (_ | N | e)
  · exact nomatch e
  · have h := sampleIdealComp_cost ℓ Pt C encT (I := saltPrfTargetIface ℓ Pt)
      (fun b => Comp.sample (I := saltPrfTargetIface ℓ Pt) (UniformSamplerTag.base b) .unit)
      (fun b => by cases b <;> simp [Comp.cost, Expr.cost, AtomicBaseUnif.cost])
    dsimp only [lSaltMacroBundle, CryptoGames.AEAD.Costed.saltRedIface, Iface.withSamp,
      Samplers.sum, Sum.elim, CryptoGames.OTCCA.Costed.idealSamplers,
      CryptoGames.AEAD.Costed.slotAdTy, CryptoGames.AEAD.Costed.lctTy, mapTy, swBaseTy, lSaltSC]
    omega
  · dsimp only [lSaltMacroBundle, saltPrfTargetIface, atomicBaseSamplers, unifSamplers]
    simp [lSaltSC, Comp.cost, Expr.cost]
  · dsimp only [lSaltMacroBundle, saltPrfTargetIface, atomicBaseSamplers, unifSamplers]
    simp only [lSaltSC, Comp.cost, Expr.cost]; omega
  · exact nomatch e

lemma lSaltQueryMacro_cost_le (g) :
    ((lSaltMacroBundle (Pt := Pt) C ℓ encT idOf).queryMacro g).cost + 2 ≤ lSaltQC g := by
  cases g
  dsimp only [lSaltMacroBundle, CryptoGames.AEAD.Costed.saltRedIface, Iface.withSamp,
    CryptoGames.PRF.Costed.prfIface, mapTy, swBaseTy]
  simp [lSaltQC, Comp.cost, Expr.cost]

lemma lWireSampMacro_cost_le (s) :
    ((lWireMacroBundle (Pt := Pt) C ℓ encT idOf).sampMacro s).cost + 2 ≤ lWireSC s := by
  rcases s with e | (_ | N | e)
  · exact nomatch e
  · dsimp only [lWireMacroBundle, wireOtccaTargetIface, atomicBaseSamplers, unifSamplers]
    simp [lWireSC, Comp.cost, Expr.cost]
  · dsimp only [lWireMacroBundle, wireOtccaTargetIface, atomicBaseSamplers, unifSamplers]
    simp only [lWireSC, Comp.cost, Expr.cost]; omega
  · exact nomatch e

lemma lWireQueryMacro_cost_le (hℓ : ℓ < 10 ^ 6) (g) :
    ((lWireMacroBundle (Pt := Pt) C ℓ encT idOf).queryMacro g).cost + 2 ≤ lWireQC g := by
  have hdiv : ℓ / 32 ≤ 31250 := by omega
  cases g <;>
    (dsimp only [lWireMacroBundle, CryptoGames.AEAD.Costed.wireRedIface, Iface.withSamp,
      CryptoGames.AEAD.Costed.wireIface, mapTy, swBaseTy]
     simp only [lWireQC, Comp.cost, Expr.cost]; omega)

section MacroSizeHelpers

omit [DecidableEq Pt]

lemma opPure_size {Γ : List (Ty (atomicSig ℓ Pt))} (o : ReductionDsl.AtomicPureOp)
    (e : Expr (atomicFsOps ℓ Pt C encT) Γ (o.dom ℓ Pt)) :
    (opPure ℓ Pt C encT o e).size = e.size + o.opSize + 1 := rfl

lemma opPtEncPk_size {Γ : List (Ty (atomicSig ℓ Pt))}
    (e : Expr (atomicFsOps ℓ Pt C encT) Γ PtT) :
    (opPtEncPk ℓ Pt C encT e).size = e.size + 1 := rfl

lemma opSym_size {Γ : List (Ty (atomicSig ℓ Pt))} (o : ReductionDsl.AtomicSymOp)
    (e : Expr (atomicFsOps ℓ Pt C encT) Γ (o.dom ℓ Pt)) :
    (opSym ℓ Pt C encT o e).size = e.size + 1 := rfl

lemma pkLitExpr_size {Γ : List (Ty (atomicSig ℓ Pt))} (pk : PublicKey) :
    (pkLitExpr ℓ Pt C encT (Γ := Γ) pk).size = 35 := by
  simp [pkLitExpr, opPure_size, ReductionDsl.AtomicPureOp.opSize, Expr.size,
    CryptoVerification.E2E.vecU8, CryptoVerification.E2E.toU8]

lemma idKeyLitExpr_size {Γ : List (Ty (atomicSig ℓ Pt))} (ik : IdentityKey) :
    (idKeyLitExpr ℓ Pt C encT (Γ := Γ) ik).size = 35 := by
  simp [idKeyLitExpr, opPure_size, ReductionDsl.AtomicPureOp.opSize, Expr.size,
    CryptoVerification.E2E.vecU8, CryptoVerification.E2E.toU8]

lemma optBytesEqExpr_size {Γ : List (Ty (atomicSig ℓ Pt))}
    (x y : Expr (atomicFsOps ℓ Pt C encT) Γ (.opt (B 32))) :
    (optBytesEqExpr ℓ Pt C encT x y).size ≤ x.size + 2 * y.size + 12 := by
  simp only [optBytesEqExpr, opPure_size, ReductionDsl.AtomicPureOp.opSize,
    Expr.size, Expr.renameM_size]; omega

lemma optPtEqExpr_size {Γ : List (Ty (atomicSig ℓ Pt))}
    (x y : Expr (atomicFsOps ℓ Pt C encT) Γ (.opt PtT)) :
    (optPtEqExpr ℓ Pt C encT x y).size ≤ x.size + 2 * y.size + 14 := by
  simp only [optPtEqExpr, opPure_size, ReductionDsl.AtomicPureOp.opSize, opPtEncPk_size,
    Expr.size, Expr.renameM_size]; omega

lemma eqLpubExpr_size {Γ : List (Ty (atomicSig ℓ Pt))}
    (x y : Expr (atomicFsOps ℓ Pt C encT) Γ lpubT) :
    (eqLpubExpr ℓ Pt C encT x y).size ≤ x.size + y.size + 70 := by
  have hopt := optBytesEqExpr_size C ℓ encT (Γ := .prod lpubT lpubT :: Γ)
    (.snd (.snd (.snd (.fst (.var .zero))))) (.snd (.snd (.snd (.snd (.var .zero)))))
  simp only [Expr.size] at hopt
  simp only [eqLpubExpr, opPure_size, ReductionDsl.AtomicPureOp.opSize, Expr.size]; omega

lemma eqFig8PubAdExpr_size {Γ : List (Ty (atomicSig ℓ Pt))}
    (x y : Expr (atomicFsOps ℓ Pt C encT) Γ fig8PubAdT) :
    (eqFig8PubAdExpr ℓ Pt C encT x y).size ≤ x.size + y.size + 120 := by
  have hpt := optPtEqExpr_size C ℓ encT (Γ := .prod fig8PubAdT fig8PubAdT :: Γ)
    (.snd (.fst (.fst (.var .zero)))) (.snd (.fst (.snd (.var .zero))))
  have hpub := eqLpubExpr_size C ℓ encT (Γ := .prod fig8PubAdT fig8PubAdT :: Γ)
    (.snd (.fst (.var .zero))) (.snd (.snd (.var .zero)))
  simp only [Expr.size] at hpt hpub
  simp only [eqFig8PubAdExpr, Expr.size]; omega

lemma eqSlotAdExpr_size {Γ : List (Ty (atomicSig ℓ Pt))}
    (x y : Expr (atomicFsOps ℓ Pt C encT) Γ slotAdT) :
    (eqSlotAdExpr ℓ Pt C encT x y).size ≤ x.size + y.size + 140 := by
  have had := eqFig8PubAdExpr_size C ℓ encT (Γ := .prod slotAdT slotAdT :: Γ)
    (.snd (.fst (.var .zero))) (.snd (.snd (.var .zero)))
  simp only [Expr.size] at had
  simp only [eqSlotAdExpr, Expr.size]; omega

lemma eqWireSaltCtExpr_size {Γ : List (Ty (atomicSig ℓ Pt))}
    (x y : Expr (atomicFsOps ℓ Pt C encT) Γ wireSaltCtT) :
    (eqWireSaltCtExpr ℓ Pt C encT x y).size ≤ x.size + y.size + 40 := by
  simp only [eqWireSaltCtExpr, opPure_size, ReductionDsl.AtomicPureOp.opSize, Expr.size]; omega

lemma lPubOfExpr_size {Γ : List (Ty (atomicSig ℓ Pt))}
    (cV : Expr (atomicFsOps ℓ Pt C encT) Γ wireSaltCtT) :
    (lPubOfExpr ℓ Pt C encT cV).size ≤ cV.size + 40 := by
  simp only [lPubOfExpr, opPure_size, ReductionDsl.AtomicPureOp.opSize,
    List.length_replicate, Expr.size]; omega

lemma chainGenExpr_size {Γ : List (Ty (atomicSig ℓ Pt))}
    (ck : Expr (atomicFsOps ℓ Pt C encT) Γ BV256) :
    (chainGenExpr ℓ Pt C encT ck).size ≤ ck.size + 15 := by
  simp only [chainGenExpr, opSym_size, opPure_size, ReductionDsl.AtomicPureOp.opSize,
    List.length_singleton, Expr.size]; omega

lemma lIdsExpr_size {Γ : List (Ty (atomicSig ℓ Pt))}
    (tE : Expr (atomicFsOps ℓ Pt C encT) Γ .nat) :
    (lIdsExpr ℓ Pt C encT idOf tE).size ≤ tE.size + 150 := by
  have hb1 : bits 1 = 1 := rfl
  have hb2 : bits 2 = 2 := rfl
  simp only [lIdsExpr, opPure_size, ReductionDsl.AtomicPureOp.opSize,
    List.Vector.toList_length, Expr.size, hb1, hb2]; omega

lemma lHeaderExpr_size {Γ : List (Ty (atomicSig ℓ Pt))}
    (aE : Expr (atomicFsOps ℓ Pt C encT) Γ slotAdT) :
    (lHeaderExpr ℓ Pt C encT aE).size ≤ aE.size + 80 := by
  have hb1 : bits 1 = 1 := rfl
  simp only [lHeaderExpr, pkLitExpr_size, opPure_size, ReductionDsl.AtomicPureOp.opSize,
    opPtEncPk_size, Expr.size, hb1]; omega

lemma eqWireSignalHdrExpr_size {Γ : List (Ty (atomicSig ℓ Pt))}
    (x y : Expr (atomicFsOps ℓ Pt C encT) Γ wireSignalHdrT) :
    (eqWireSignalHdrExpr ℓ Pt C encT x y).size ≤ x.size + y.size + 100 := by
  have hopt := optBytesEqExpr_size C ℓ encT (Γ := .prod wireSignalHdrT wireSignalHdrT :: Γ)
    (.snd (.snd (.fst (.var .zero)))) (.snd (.snd (.snd (.var .zero))))
  simp only [Expr.size] at hopt
  simp only [eqWireSignalHdrExpr, opPure_size, ReductionDsl.AtomicPureOp.opSize, Expr.size]; omega

lemma fitPlainExpr_size {Γ : List (Ty (atomicSig ℓ Pt))}
    (m : Expr (atomicFsOps ℓ Pt C encT) Γ (B 32)) :
    (fitPlainExpr ℓ Pt C encT m).size = m.size + 1 := rfl

lemma eqPlainExpr_size {Γ : List (Ty (atomicSig ℓ Pt))}
    (x y : Expr (atomicFsOps ℓ Pt C encT) Γ PlainT) :
    (eqPlainExpr ℓ Pt C encT x y).size = x.size + y.size + 2 := rfl

lemma eqSaltExpr_size {Γ : List (Ty (atomicSig ℓ Pt))}
    (x y : Expr (atomicFsOps ℓ Pt C encT) Γ BV256) :
    (eqSaltExpr ℓ Pt C encT x y).size = x.size + y.size + 2 := rfl

lemma saltOfSlotAdExpr_size {Γ : List (Ty (atomicSig ℓ Pt))}
    (a : Expr (atomicFsOps ℓ Pt C encT) Γ slotAdT) :
    (saltOfSlotAdExpr ℓ Pt C encT a).size = a.size + 5 := by
  simp only [saltOfSlotAdExpr, Expr.size]

lemma exprWkTop1_size {Γ : List (Ty (atomicSig ℓ Pt))} {a b : Ty (atomicSig ℓ Pt)}
    (e : Expr (atomicFsOps ℓ Pt C encT) [a] b) :
    (exprWkTop1 ℓ Pt C encT (Γ := Γ) e).size = e.size := by
  simp [exprWkTop1]

set_option maxRecDepth 2000 in
lemma aeadKEncExpr_size :
    (aeadKEncExpr ℓ Pt C encT idOf).size ≤ 480 := by
  have hsalt := saltOfSlotAdExpr_size C ℓ encT
    (Γ := [B 32, .prod derivedMsgKeysT (.prod slotAdT PlainT)])
    (Expr.fst (Expr.snd (.var (.succ .zero))))
  have hb1 : bits 1 = 1 := rfl
  have hb2 : bits 2 = 2 := rfl
  have hb8 : bits 8 ≤ 4 := ReductionDsl.bits_le_of_lt (by norm_num) (by omega)
  have hb96 : bits 96 ≤ 8 := ReductionDsl.bits_le_of_lt (by norm_num) (by omega)
  have hb128 : bits 128 ≤ 9 := ReductionDsl.bits_le_of_lt (by norm_num) (by omega)
  simp only [Expr.size] at hsalt
  simp only [aeadKEncExpr, pkLitExpr_size, idKeyLitExpr_size, opSym_size, opPure_size,
    ReductionDsl.AtomicPureOp.opSize, opPtEncPk_size, Expr.size, hsalt, hb1, hb2, Nat.reduceAdd]
  clear hsalt; omega

lemma aeadKDecExpr_size :
    (aeadKDecExpr ℓ Pt C encT idOf).size ≤ 570 := by
  let argT : Ty (atomicSig ℓ Pt) := .prod derivedMsgKeysT (.prod slotAdT wireSaltCtT)
  let Γ₁ : List (Ty (atomicSig ℓ Pt)) := ReductionDsl.signalParsedT :: [argT]
  have hhdr := lHeaderExpr_size C ℓ encT (Γ := Γ₁)
    (Expr.fst (Expr.snd (.var (.succ .zero))))
  have heq := eqWireSignalHdrExpr_size C ℓ encT (Γ := Γ₁)
    (.pair (Expr.fst (.var .zero)) (Expr.snd (Expr.snd (.var .zero))))
    (lHeaderExpr ℓ Pt C encT (Expr.fst (Expr.snd (.var (.succ .zero)))))
  have hb1 : bits 1 = 1 := rfl
  have hb2 : bits 2 = 2 := rfl
  simp only [Expr.size] at hhdr heq
  simp only [aeadKDecExpr, idKeyLitExpr_size, opSym_size, opPure_size,
    ReductionDsl.AtomicPureOp.opSize, List.length_replicate, Expr.size, hb1, hb2, Nat.reduceAdd]
  omega

lemma aeadREncExpr_size :
    (aeadREncExpr ℓ Pt C encT idOf).size ≤ 540 := by
  have hk := aeadKEncExpr_size C ℓ encT idOf
  have hsalt := saltOfSlotAdExpr_size C ℓ encT (Γ := [.prod BV256 (.prod slotAdT PlainT)])
    (Expr.fst (Expr.snd (.var .zero)))
  simp only [Expr.size] at hsalt
  simp only [aeadREncExpr, opSym_size, opPure_size, ReductionDsl.AtomicPureOp.opSize,
    Expr.size, exprWkTop1_size, hsalt]
  omega

lemma aeadRDecExpr_size :
    (aeadRDecExpr ℓ Pt C encT idOf).size ≤ 630 := by
  have hk := aeadKDecExpr_size C ℓ encT idOf
  have hsalt := saltOfSlotAdExpr_size C ℓ encT (Γ := [.prod BV256 (.prod slotAdT wireSaltCtT)])
    (Expr.fst (Expr.snd (.var .zero)))
  simp only [Expr.size] at hsalt
  simp only [aeadRDecExpr, opSym_size, opPure_size, ReductionDsl.AtomicPureOp.opSize,
    Expr.size, exprWkTop1_size, hsalt]
  omega

lemma signalEncodeSerOnlyExpr_size :
    (signalEncodeSerOnlyExpr ℓ Pt C encT).size ≤ 170 := by
  have hb8 : bits 8 ≤ 4 := ReductionDsl.bits_le_of_lt (by norm_num) (by omega)
  have hb96 : bits 96 ≤ 8 := ReductionDsl.bits_le_of_lt (by norm_num) (by omega)
  have hb128 : bits 128 ≤ 9 := ReductionDsl.bits_le_of_lt (by norm_num) (by omega)
  simp only [signalEncodeSerOnlyExpr, idKeyLitExpr_size, opSym_size, opPure_size,
    ReductionDsl.AtomicPureOp.opSize, Expr.size, Nat.reduceAdd]
  omega

lemma sampleU64Comp_size {ι : Type} {T : OracleSpec.{0, 0} ι}
    {I : Iface (atomicSig ℓ Pt) T}
    (sampU : ∀ {Γ : List (Ty (atomicSig ℓ Pt))} (b : AtomicBaseUnif),
      Comp (atomicFsOps ℓ Pt C encT) I Γ (.base b.sort))
    (hs : ∀ {Γ : List (Ty (atomicSig ℓ Pt))} (b : AtomicBaseUnif), (sampU (Γ := Γ) b).size ≤ 2)
    {Γ : List (Ty (atomicSig ℓ Pt))} :
    (sampleU64Comp ℓ Pt C encT sampU (Γ := Γ)).size ≤ 10 := by
  have hb := hs (Γ := Γ) .bv128
  simp only [sampleU64Comp, Comp.size, opPure_size, ReductionDsl.AtomicPureOp.opSize, Expr.size]; omega

lemma sampleMsgKeyComp_size {ι : Type} {T : OracleSpec.{0, 0} ι}
    {I : Iface (atomicSig ℓ Pt) T}
    (sampU : ∀ {Γ : List (Ty (atomicSig ℓ Pt))} (b : AtomicBaseUnif),
      Comp (atomicFsOps ℓ Pt C encT) I Γ (.base b.sort))
    (hs : ∀ {Γ : List (Ty (atomicSig ℓ Pt))} (b : AtomicBaseUnif), (sampU (Γ := Γ) b).size ≤ 2)
    {Γ : List (Ty (atomicSig ℓ Pt))} :
    (sampleMsgKeyComp ℓ Pt C encT sampU (Γ := Γ)).size ≤ 16 := by
  have hb1 := hs (Γ := Γ) .bv256
  have hb2 := hs (Γ := BV256 :: Γ) .bv128
  have hb3 := hs (Γ := BV128 :: BV256 :: Γ) .bv256
  dsimp only [sampleMsgKeyComp, BV256, BV128, AtomicBaseUnif.sort, Comp.size, Expr.size] at hb1 hb2 hb3 ⊢
  omega

lemma sampleIdealComp_size {ι : Type} {T : OracleSpec.{0, 0} ι}
    {I : Iface (atomicSig ℓ Pt) T}
    (hℓ : ℓ < 10 ^ 6)
    (sampU : ∀ {Γ : List (Ty (atomicSig ℓ Pt))} (b : AtomicBaseUnif),
      Comp (atomicFsOps ℓ Pt C encT) I Γ (.base b.sort))
    (hs : ∀ {Γ : List (Ty (atomicSig ℓ Pt))} (b : AtomicBaseUnif), (sampU (Γ := Γ) b).size ≤ 2) :
    (sampleIdealComp ℓ Pt C encT sampU).size ≤ 350 := by
  have hb := hs (Γ := [B 32, slotAdT]) .bv128
  have hu := sampleU64Comp_size C ℓ encT sampU hs (Γ := [B 32, slotAdT])
  have hhdr := lHeaderExpr_size C ℓ encT (Γ := [U64, B 32, slotAdT]) (.var (.succ (.succ .zero)))
  have hser := signalEncodeSerOnlyExpr_size C ℓ encT
  have hsalt := saltOfSlotAdExpr_size C ℓ encT (Γ := [U64, B 32, slotAdT])
    (.var (.succ (.succ .zero)))
  have hnb : bits (nBlocks ℓ) ≤ 16 := by
    refine ReductionDsl.bits_le_of_lt ?_ (by omega)
    unfold nBlocks; omega
  simp only [Expr.size] at hhdr hsalt
  simp only [sampleIdealComp, Comp.size, opPure_size, ReductionDsl.AtomicPureOp.opSize,
    List.length_nil, Expr.size, exprWkTop1_size]
  omega

end MacroSizeHelpers

omit [DecidableEq Pt] in
lemma pubOpMacro_size_le (o) :
    ((pubMacroBundle (Pt := Pt) C ℓ encT).opMacro o).size + 1 ≤ 250 := by
  cases o
  have h := lPubOfExpr_size C ℓ encT (Γ := [lctT]) (.snd (.var .zero))
  dsimp only [pubMacroBundle, CryptoGames.FSAEAD.Costed.fsOps, mapTy, pubBaseTy]
  simp only [Expr.size] at h ⊢; omega

omit [DecidableEq Pt] in
lemma pubQueryMacro_size_le (g) :
    ((pubMacroBundle (Pt := Pt) C ℓ encT).queryMacro g).size + 2 ≤ 250 := by
  cases g <;>
    (dsimp only [pubMacroBundle, CryptoGames.FSAEAD.Costed.fsaeadIface, mapTy, pubBaseTy]
     simp only [Comp.size, Expr.size]; omega)

lemma hybOpMacro_size_le (o) :
    (hybOpMacro (Pt := Pt) C ℓ encT idOf o).size + 1 ≤ 650 := by
  rcases o with ⟨⟩ | (_ | _ | _ | _ | _ | _ | _)
  · have := chainGenExpr_size C ℓ encT (Γ := [.prod .nat BV256]) (.snd (.var .zero))
    dsimp only [hybOpMacro, Ops.sum, Sum.elim, CryptoGames.PRG.Costed.prgOps, mapTy, hybBaseTy]
    simp only [Expr.size] at this ⊢; omega
  · have := aeadREncExpr_size C ℓ encT idOf
    dsimp only [hybOpMacro, Ops.sum, Sum.elim, CryptoGames.OTCCA.Costed.otccaOps, mapTy, hybBaseTy]
    omega
  · have := aeadRDecExpr_size C ℓ encT idOf
    dsimp only [hybOpMacro, Ops.sum, Sum.elim, CryptoGames.OTCCA.Costed.otccaOps, mapTy, hybBaseTy]
    omega
  · dsimp only [hybOpMacro, Ops.sum, Sum.elim, CryptoGames.OTCCA.Costed.otccaOps, mapTy, hybBaseTy]
    simp only [Expr.size]; omega
  · have := eqFig8PubAdExpr_size C ℓ encT (Γ := [.prod fig8PubAdT fig8PubAdT])
      (.fst (.var .zero)) (.snd (.var .zero))
    dsimp only [hybOpMacro, Ops.sum, Sum.elim, CryptoGames.OTCCA.Costed.otccaOps, mapTy, hybBaseTy]
    simp only [Expr.size] at this ⊢; omega
  · have := eqPlainExpr_size C ℓ encT (Γ := [.prod PlainT PlainT])
      (.fst (.var .zero)) (.snd (.var .zero))
    dsimp only [hybOpMacro, Ops.sum, Sum.elim, CryptoGames.OTCCA.Costed.otccaOps, mapTy, hybBaseTy]
    simp only [Expr.size] at this ⊢; omega
  · have := eqWireSaltCtExpr_size C ℓ encT (Γ := [.prod wireSaltCtT wireSaltCtT])
      (.fst (.var .zero)) (.snd (.var .zero))
    dsimp only [hybOpMacro, Ops.sum, Sum.elim, CryptoGames.OTCCA.Costed.otccaOps, mapTy, hybBaseTy]
    simp only [Expr.size] at this ⊢; omega
  · dsimp only [hybOpMacro, Ops.sum, Sum.elim, CryptoGames.OTCCA.Costed.otccaOps, mapTy, hybBaseTy]
    simp only [Expr.size]; omega

lemma swOpMacro_size_le (o) :
    (swOpMacro (Pt := Pt) C ℓ encT idOf o).size + 1 ≤ 650 := by
  rcases o with (_ | _ | _ | _ | _ | _ | _) | ((_ | _ | _ | _ | _ | _ | _) | (_ | _ | _ | _))
  · have := aeadKEncExpr_size C ℓ encT idOf
    dsimp only [swOpMacro, CryptoGames.AEAD.Costed.saltWireOps, Ops.sum, Sum.elim,
      CryptoGames.OTCCA.Costed.otccaOps, CryptoGames.AEAD.Costed.slotAdTy,
      CryptoGames.AEAD.Costed.lctTy, mapTy, swBaseTy]; omega
  · have := aeadKDecExpr_size C ℓ encT idOf
    dsimp only [swOpMacro, CryptoGames.AEAD.Costed.saltWireOps, Ops.sum, Sum.elim,
      CryptoGames.OTCCA.Costed.otccaOps, CryptoGames.AEAD.Costed.slotAdTy,
      CryptoGames.AEAD.Costed.lctTy, mapTy, swBaseTy]; omega
  · have := saltOfSlotAdExpr_size C ℓ encT (Γ := [slotAdT]) (.var .zero)
    dsimp only [swOpMacro, CryptoGames.AEAD.Costed.saltWireOps, Ops.sum, Sum.elim,
      CryptoGames.OTCCA.Costed.otccaOps, CryptoGames.AEAD.Costed.slotAdTy, mapTy, swBaseTy]
    simp only [Expr.size] at this ⊢; omega
  · have := eqSlotAdExpr_size C ℓ encT (Γ := [.prod slotAdT slotAdT])
      (.fst (.var .zero)) (.snd (.var .zero))
    dsimp only [swOpMacro, CryptoGames.AEAD.Costed.saltWireOps, Ops.sum, Sum.elim,
      CryptoGames.OTCCA.Costed.otccaOps, CryptoGames.AEAD.Costed.slotAdTy, mapTy, swBaseTy]
    simp only [Expr.size] at this ⊢; omega
  · have := eqPlainExpr_size C ℓ encT (Γ := [.prod PlainT PlainT])
      (.fst (.var .zero)) (.snd (.var .zero))
    dsimp only [swOpMacro, CryptoGames.AEAD.Costed.saltWireOps, Ops.sum, Sum.elim,
      CryptoGames.OTCCA.Costed.otccaOps, mapTy, swBaseTy]
    simp only [Expr.size] at this ⊢; omega
  · have := eqWireSaltCtExpr_size C ℓ encT (Γ := [.prod wireSaltCtT wireSaltCtT])
      (.fst (.var .zero)) (.snd (.var .zero))
    dsimp only [swOpMacro, CryptoGames.AEAD.Costed.saltWireOps, Ops.sum, Sum.elim,
      CryptoGames.OTCCA.Costed.otccaOps, CryptoGames.AEAD.Costed.lctTy, mapTy, swBaseTy]
    simp only [Expr.size] at this ⊢; omega
  · have := eqSaltExpr_size C ℓ encT (Γ := [.prod BV256 BV256])
      (.fst (.var .zero)) (.snd (.var .zero))
    dsimp only [swOpMacro, CryptoGames.AEAD.Costed.saltWireOps, Ops.sum, Sum.elim,
      CryptoGames.OTCCA.Costed.otccaOps, mapTy, swBaseTy]
    simp only [Expr.size] at this ⊢; omega
  · have := aeadREncExpr_size C ℓ encT idOf
    dsimp only [swOpMacro, CryptoGames.AEAD.Costed.saltWireOps, Ops.sum, Sum.elim,
      CryptoGames.OTCCA.Costed.otccaOps, CryptoGames.AEAD.Costed.slotAdTy,
      CryptoGames.AEAD.Costed.lctTy, mapTy, swBaseTy]; omega
  · have := aeadRDecExpr_size C ℓ encT idOf
    dsimp only [swOpMacro, CryptoGames.AEAD.Costed.saltWireOps, Ops.sum, Sum.elim,
      CryptoGames.OTCCA.Costed.otccaOps, CryptoGames.AEAD.Costed.slotAdTy,
      CryptoGames.AEAD.Costed.lctTy, mapTy, swBaseTy]; omega
  · have := saltOfSlotAdExpr_size C ℓ encT (Γ := [slotAdT]) (.var .zero)
    dsimp only [swOpMacro, CryptoGames.AEAD.Costed.saltWireOps, Ops.sum, Sum.elim,
      CryptoGames.OTCCA.Costed.otccaOps, CryptoGames.AEAD.Costed.slotAdTy, mapTy, swBaseTy]
    simp only [Expr.size] at this ⊢; omega
  · have := eqSlotAdExpr_size C ℓ encT (Γ := [.prod slotAdT slotAdT])
      (.fst (.var .zero)) (.snd (.var .zero))
    dsimp only [swOpMacro, CryptoGames.AEAD.Costed.saltWireOps, Ops.sum, Sum.elim,
      CryptoGames.OTCCA.Costed.otccaOps, CryptoGames.AEAD.Costed.slotAdTy, mapTy, swBaseTy]
    simp only [Expr.size] at this ⊢; omega
  · have := eqPlainExpr_size C ℓ encT (Γ := [.prod PlainT PlainT])
      (.fst (.var .zero)) (.snd (.var .zero))
    dsimp only [swOpMacro, CryptoGames.AEAD.Costed.saltWireOps, Ops.sum, Sum.elim,
      CryptoGames.OTCCA.Costed.otccaOps, mapTy, swBaseTy]
    simp only [Expr.size] at this ⊢; omega
  · have := eqWireSaltCtExpr_size C ℓ encT (Γ := [.prod wireSaltCtT wireSaltCtT])
      (.fst (.var .zero)) (.snd (.var .zero))
    dsimp only [swOpMacro, CryptoGames.AEAD.Costed.saltWireOps, Ops.sum, Sum.elim,
      CryptoGames.OTCCA.Costed.otccaOps, CryptoGames.AEAD.Costed.lctTy, mapTy, swBaseTy]
    simp only [Expr.size] at this ⊢; omega
  · have := eqSaltExpr_size C ℓ encT (Γ := [.prod BV256 BV256])
      (.fst (.var .zero)) (.snd (.var .zero))
    dsimp only [swOpMacro, CryptoGames.AEAD.Costed.saltWireOps, Ops.sum, Sum.elim,
      CryptoGames.OTCCA.Costed.otccaOps, mapTy, swBaseTy]
    simp only [Expr.size] at this ⊢; omega
  · have := lIdsExpr_size C ℓ encT idOf (Γ := [slotAdT]) (.fst (.fst (.snd (.var .zero))))
    dsimp only [swOpMacro, CryptoGames.AEAD.Costed.saltWireOps, Ops.sum, Sum.elim,
      CryptoGames.AEAD.Costed.wireOps, CryptoGames.AEAD.Costed.slotAdTy, mapTy, swBaseTy]
    simp only [Expr.size] at this ⊢; omega
  · have := lHeaderExpr_size C ℓ encT (Γ := [slotAdT]) (.var .zero)
    dsimp only [swOpMacro, CryptoGames.AEAD.Costed.saltWireOps, Ops.sum, Sum.elim,
      CryptoGames.AEAD.Costed.wireOps, CryptoGames.AEAD.Costed.slotAdTy, mapTy, swBaseTy]
    simp only [Expr.size] at this ⊢; omega
  · have := eqWireSignalHdrExpr_size C ℓ encT (Γ := [.prod wireSignalHdrT wireSignalHdrT])
      (.fst (.var .zero)) (.snd (.var .zero))
    dsimp only [swOpMacro, CryptoGames.AEAD.Costed.saltWireOps, Ops.sum, Sum.elim,
      CryptoGames.AEAD.Costed.wireOps, mapTy, swBaseTy]
    simp only [Expr.size] at this ⊢; omega
  · have := fitPlainExpr_size C ℓ encT (Γ := [B 32]) (.var .zero)
    dsimp only [swOpMacro, CryptoGames.AEAD.Costed.saltWireOps, Ops.sum, Sum.elim,
      CryptoGames.AEAD.Costed.wireOps, mapTy, swBaseTy]
    simp only [Expr.size] at this ⊢; omega

lemma prgSampMacro_size_le (hℓ : ℓ < 10 ^ 6) (s) :
    ((prgZeroMacroBundle (Pt := Pt) C ℓ encT idOf).sampMacro s).size + 2 ≤ 650 := by
  rcases s with (e | ⟨⟩) | (_ | N | (_ | _))
  · exact nomatch e
  · have h := sampleIdealComp_size C ℓ encT hℓ (I := coinOnlyBaseIface ℓ Pt)
      (fun b => Comp.sample (I := coinOnlyBaseIface ℓ Pt) (UniformSamplerTag.base b) .unit)
      (fun b => by simp [Comp.size, Expr.size])
    dsimp only [prgZeroMacroBundle, Iface.withSamp, Samplers.sum, Sum.elim,
      CryptoGames.OTCCA.Costed.idealSamplers, mapTy, hybBaseTy]; omega
  all_goals
    dsimp only [prgZeroMacroBundle, coinOnlyBaseIface, atomicBaseSamplers, unifSamplers]
    simp only [Comp.size, Expr.size]; omega

lemma multiSampMacro_size_le (hℓ : ℓ < 10 ^ 6) (s) :
    ((multiMacroBundle (Pt := Pt) C ℓ encT idOf).sampMacro s).size + 2 ≤ 650 := by
  cases s with
  | inl u =>
    cases u
    have h := sampleIdealComp_size C ℓ encT hℓ (I := slotOtccaTargetIface ℓ Pt)
      (fun b => Comp.sample (I := slotOtccaTargetIface ℓ Pt) (UniformSamplerTag.base b) .unit)
      (fun b => by simp [Comp.size, Expr.size])
    dsimp only [multiMacroBundle, Iface.withSamp, Samplers.sum, Sum.elim,
      CryptoGames.OTCCA.Costed.otccaIface, CryptoGames.OTCCA.Costed.idealSamplers,
      mapTy, hybBaseTy]; omega
  | inr t =>
    rcases t with _ | N | (_ | _) <;>
      (dsimp only [multiMacroBundle, slotOtccaTargetIface, atomicBaseSamplers, unifSamplers]
       simp only [Comp.size, Expr.size]; omega)

lemma multiQueryMacro_size_le (g) :
    ((multiMacroBundle (Pt := Pt) C ℓ encT idOf).queryMacro g).size + 2 ≤ 650 := by
  cases g <;>
    (dsimp only [multiMacroBundle, Iface.withSamp, CryptoGames.OTCCA.Costed.otccaIface,
      mapTy, hybBaseTy]
     simp only [Comp.size, Expr.size]; omega)

lemma slotSwSampMacro_size_le (hℓ : ℓ < 10 ^ 6) (s) :
    ((slotSwMacroBundle (Pt := Pt) C ℓ encT idOf).sampMacro s).size + 2 ≤ 650 := by
  cases s with
  | inl u =>
    cases u
    have h := sampleIdealComp_size C ℓ encT hℓ (I := slotOtccaTargetIface ℓ Pt)
      (fun b => Comp.sample (I := slotOtccaTargetIface ℓ Pt) (UniformSamplerTag.base b) .unit)
      (fun b => by simp [Comp.size, Expr.size])
    dsimp only [slotSwMacroBundle, CryptoGames.AEAD.Costed.slotOtccaIface, Iface.withSamp,
      Samplers.sum, Sum.elim, CryptoGames.OTCCA.Costed.otccaIface,
      CryptoGames.OTCCA.Costed.idealSamplers, CryptoGames.AEAD.Costed.slotAdTy,
      CryptoGames.AEAD.Costed.lctTy, mapTy, swBaseTy]; omega
  | inr t =>
    rcases t with _ | N | (_ | _)
    · dsimp only [slotSwMacroBundle, slotOtccaTargetIface, atomicBaseSamplers, unifSamplers]
      simp only [Comp.size, Expr.size]; omega
    · dsimp only [slotSwMacroBundle, slotOtccaTargetIface, atomicBaseSamplers, unifSamplers]
      simp only [Comp.size, Expr.size]; omega
    · dsimp only [slotSwMacroBundle]
      exact Nat.le_trans (Nat.add_le_add_right
        (sampleMsgKeyComp_size C ℓ encT (I := slotOtccaTargetIface ℓ Pt)
          (fun b => Comp.sample (I := slotOtccaTargetIface ℓ Pt) (UniformSamplerTag.base b) .unit)
          (fun b => by simp [Comp.size, Expr.size])
          (Γ := [.unit])) 2) (by omega)
    · dsimp only [slotSwMacroBundle, slotOtccaTargetIface, atomicBaseSamplers, unifSamplers]
      simp only [Comp.size, Expr.size]; omega

lemma slotSwQueryMacro_size_le (g) :
    ((slotSwMacroBundle (Pt := Pt) C ℓ encT idOf).queryMacro g).size + 2 ≤ 650 := by
  cases g <;>
    (dsimp only [slotSwMacroBundle, CryptoGames.AEAD.Costed.slotOtccaIface, Iface.withSamp,
      CryptoGames.OTCCA.Costed.otccaIface, CryptoGames.AEAD.Costed.slotAdTy,
      CryptoGames.AEAD.Costed.lctTy, mapTy, swBaseTy]
     simp only [Comp.size, Expr.size]; omega)

lemma lSaltSampMacro_size_le (hℓ : ℓ < 10 ^ 6) (s) :
    ((lSaltMacroBundle (Pt := Pt) C ℓ encT idOf).sampMacro s).size + 2 ≤ 650 := by
  rcases s with (e | ⟨⟩) | (_ | N | e)
  · exact nomatch e
  · have h := sampleIdealComp_size C ℓ encT hℓ (I := saltPrfTargetIface ℓ Pt)
      (fun b => Comp.sample (I := saltPrfTargetIface ℓ Pt) (UniformSamplerTag.base b) .unit)
      (fun b => by simp [Comp.size, Expr.size])
    dsimp only [lSaltMacroBundle, CryptoGames.AEAD.Costed.saltRedIface, Iface.withSamp,
      Samplers.sum, Sum.elim, CryptoGames.OTCCA.Costed.idealSamplers,
      CryptoGames.AEAD.Costed.slotAdTy, CryptoGames.AEAD.Costed.lctTy, mapTy, swBaseTy]; omega
  · dsimp only [lSaltMacroBundle, saltPrfTargetIface, atomicBaseSamplers, unifSamplers]
    simp only [Comp.size, Expr.size]; omega
  · dsimp only [lSaltMacroBundle, saltPrfTargetIface, atomicBaseSamplers, unifSamplers]
    simp only [Comp.size, Expr.size]; omega
  · exact nomatch e

lemma lSaltQueryMacro_size_le (g) :
    ((lSaltMacroBundle (Pt := Pt) C ℓ encT idOf).queryMacro g).size + 2 ≤ 650 := by
  cases g
  dsimp only [lSaltMacroBundle, CryptoGames.AEAD.Costed.saltRedIface, Iface.withSamp,
    CryptoGames.PRF.Costed.prfIface, mapTy, swBaseTy]
  simp only [Comp.size, Expr.size]; omega

lemma lWireSampMacro_size_le (s) :
    ((lWireMacroBundle (Pt := Pt) C ℓ encT idOf).sampMacro s).size + 2 ≤ 650 := by
  rcases s with e | (_ | N | e)
  · exact nomatch e
  · dsimp only [lWireMacroBundle, wireOtccaTargetIface, atomicBaseSamplers, unifSamplers]
    simp only [Comp.size, Expr.size]; omega
  · dsimp only [lWireMacroBundle, wireOtccaTargetIface, atomicBaseSamplers, unifSamplers]
    simp only [Comp.size, Expr.size]; omega
  · exact nomatch e

lemma lWireQueryMacro_size_le (g) :
    ((lWireMacroBundle (Pt := Pt) C ℓ encT idOf).queryMacro g).size + 2 ≤ 650 := by
  cases g <;>
    (dsimp only [lWireMacroBundle, CryptoGames.AEAD.Costed.wireRedIface, Iface.withSamp,
      CryptoGames.AEAD.Costed.wireIface, mapTy, swBaseTy]
     simp only [Comp.size, Expr.size]; omega)

end MacroBounds2


section SwProgBounds

open CryptoGames.Ratchet.LibsignalInst.Costed

variable {Pt : Type} [DecidableEq Pt]
  (C : Crypto) (codec : SignalMessageProtoCodec) (ℓ : ℕ)
  (encT : Pt → PublicKey) (idOf : Party → IdentityKey)

lemma slotSaltEncC_cost_le {Γ} (b : Bool) (qR : ℕ) :
    compCostBound swOpCU slotSwSC slotSwQC
      (slotSaltEncC (Pt := Pt) C clampedProtoSignalCodec ℓ encT idOf 1 1 b qR (Γ := Γ)) ≤
      3000000 + 50 * qR := by
  refine (compCostBound_le_UB _ _ _ _).trans ?_
  dsimp only [slotSaltEncC, slotKeyOfC, sampleSlotMsgKeyC, sampleSlotIdealC, isSomeE, saltOfE,
    encKE, eqSaltE, CryptoGames.AEAD.Costed.saltWireOps, Ops.sum,
    CryptoGames.OTCCA.Costed.otccaOps]
  unfold_vars
  dsimp only [compCostBoundUB, exprCostBoundUB, swOpCU, slotSwSC]
  omega

lemma slotSaltDecC_cost_le {Γ} (nf b : Bool) (qR : ℕ) :
    compCostBound swOpCU slotSwSC slotSwQC
      (slotSaltDecC (Pt := Pt) C clampedProtoSignalCodec ℓ encT idOf 1 1 nf b qR (Γ := Γ)) ≤
      1000000 + 50 * qR := by
  refine (compCostBound_le_UB _ _ _ _).trans ?_
  dsimp only [slotSaltDecC, isSlotChalSaltE, slotKeyOfC, sampleSlotMsgKeyC, orE, eqSaltE, saltOfE,
    eqChalSomeE, eqADE, eqCE, decKE,
    CryptoGames.AEAD.Costed.saltWireOps, Ops.sum, CryptoGames.OTCCA.Costed.otccaOps]
  unfold_vars
  dsimp only [compCostBoundUB, exprCostBoundUB, swOpCU, slotSwSC]
  cases nf
  · have hite : ∀ {α : Type} (x y : α), (if false = true then x else y) = y := fun _ _ => rfl
    rw [hite]
    dsimp only [exprCostBoundUB, swOpCU]
    omega
  · have hite : ∀ {α : Type} (x y : α), (if true = true then x else y) = x := fun _ _ => rfl
    rw [hite]
    dsimp only [exprCostBoundUB, swOpCU]
    omega

lemma slotRedHandleC_cost_le
    {slTy srTy : Ty (CryptoGames.AEAD.Costed.saltWireSig Pt ℓ)} (k qR : ℕ)
    (hb1 : bits k ≤ qR + 15) (hb2 : bits (k + 1) ≤ qR + 15)
    (encL : ∀ {Γ}, Comp _ _ (slTy :: .prod (CryptoGames.AEAD.Costed.slotAdTy Pt ℓ) (.base .plain) :: Γ)
      (.prod (.opt (CryptoGames.AEAD.Costed.lctTy Pt ℓ)) slTy))
    (decL : ∀ {Γ}, Comp _ _ (slTy :: .prod (CryptoGames.AEAD.Costed.slotAdTy Pt ℓ) (CryptoGames.AEAD.Costed.lctTy Pt ℓ) :: Γ)
      (.prod (.opt (.base .plain)) slTy))
    (encR : ∀ {Γ}, Comp _ _ (srTy :: .prod (CryptoGames.AEAD.Costed.slotAdTy Pt ℓ) (.base .plain) :: Γ)
      (.prod (.opt (CryptoGames.AEAD.Costed.lctTy Pt ℓ)) srTy))
    (decR : ∀ {Γ}, Comp _ _ (srTy :: .prod (CryptoGames.AEAD.Costed.slotAdTy Pt ℓ) (CryptoGames.AEAD.Costed.lctTy Pt ℓ) :: Γ)
      (.prod (.opt (.base .plain)) srTy))
    (hEL : ∀ {Γ}, compCostBound swOpCU slotSwSC slotSwQC (encL (Γ := Γ)) ≤ 3000000 + 50 * qR)
    (hDL : ∀ {Γ}, compCostBound swOpCU slotSwSC slotSwQC (decL (Γ := Γ)) ≤ 1000000 + 50 * qR)
    (hER : ∀ {Γ}, compCostBound swOpCU slotSwSC slotSwQC (encR (Γ := Γ)) ≤ 3000000 + 50 * qR)
    (hDR : ∀ {Γ}, compCostBound swOpCU slotSwSC slotSwQC (decR (Γ := Γ)) ≤ 1000000 + 50 * qR) :
    compCostBound swOpCU slotSwSC slotSwQC
      (slotRedHandleC C clampedProtoSignalCodec ℓ encT idOf 1 1 k encL decL encR decR) ≤
      5000000 + 200 * qR := by
  have hc1 : bits 1 = 1 := rfl
  let Δ0 : List (Ty (CryptoGames.AEAD.Costed.saltWireSig Pt ℓ)) :=
    [.prod (.tbl slTy) (.tbl srTy), (CryptoGames.AEAD.Costed.slotOtccaCodec Pt ℓ).Q]
  have hel := hEL (Γ := Δ0)
  have hdl := hDL (Γ := Δ0)
  have her := hER (Γ := Δ0)
  have hdr := hDR (Γ := Δ0)
  dsimp only [Δ0, slotRedHandleC, slotRedEncC, slotRedDecC, querySlotEncC, querySlotDecC, leE,
    CryptoGames.AEAD.Costed.saltWireOps, Ops.sum, CryptoGames.OTCCA.Costed.otccaOps,
    CryptoGames.AEAD.Costed.slotOtccaIface, Iface.withSamp] at hel hdl her hdr ⊢
  unfold_vars
  dsimp only [compCostBound, exprCostBound, slotSwQC] at hel hdl her hdr ⊢
  simp only [hc1]
  omega

lemma slotSaltEncC_size_le {Γ} (b : Bool) (qR : ℕ) :
    (slotSaltEncC (Pt := Pt) C clampedProtoSignalCodec ℓ encT idOf 1 1 b qR (Γ := Γ)).size ≤
      130 + bits qR := by
  dsimp only [slotSaltEncC, slotKeyOfC, sampleSlotMsgKeyC, sampleSlotIdealC, isSomeE, saltOfE,
    encKE, eqSaltE, CryptoGames.AEAD.Costed.saltWireOps, Ops.sum,
    CryptoGames.OTCCA.Costed.otccaOps]
  unfold_vars; dsimp only [Comp.size, Expr.size, Sum.elim]; omega

lemma slotSaltEncC_nodes_le {Γ} (b : Bool) (qR : ℕ) :
    (slotSaltEncC (Pt := Pt) C clampedProtoSignalCodec ℓ encT idOf 1 1 b qR (Γ := Γ)).nodes ≤ 130 := by
  dsimp only [slotSaltEncC, slotKeyOfC, sampleSlotMsgKeyC, sampleSlotIdealC, isSomeE, saltOfE,
    encKE, eqSaltE, CryptoGames.AEAD.Costed.saltWireOps, Ops.sum,
    CryptoGames.OTCCA.Costed.otccaOps]
  unfold_vars; dsimp only [Comp.nodes, Expr.nodes]; omega

lemma slotSaltDecC_size_le {Γ} (nf b : Bool) (qR : ℕ) :
    (slotSaltDecC (Pt := Pt) C clampedProtoSignalCodec ℓ encT idOf 1 1 nf b qR (Γ := Γ)).size ≤
      160 + bits qR := by
  dsimp only [slotSaltDecC, isSlotChalSaltE, slotKeyOfC, sampleSlotMsgKeyC, orE, eqSaltE, saltOfE,
    eqChalSomeE, eqADE, eqCE, decKE,
    CryptoGames.AEAD.Costed.saltWireOps, Ops.sum, CryptoGames.OTCCA.Costed.otccaOps]
  unfold_vars; dsimp only [Comp.size, Expr.size, Sum.elim]
  cases nf
  · have hite : ∀ {α : Type} (x y : α), (if false = true then x else y) = y := fun _ _ => rfl
    rw [hite]; dsimp only [Expr.size, Sum.elim]; omega
  · have hite : ∀ {α : Type} (x y : α), (if true = true then x else y) = x := fun _ _ => rfl
    rw [hite]; dsimp only [Expr.size, Sum.elim]; omega

lemma slotSaltDecC_nodes_le {Γ} (nf b : Bool) (qR : ℕ) :
    (slotSaltDecC (Pt := Pt) C clampedProtoSignalCodec ℓ encT idOf 1 1 nf b qR (Γ := Γ)).nodes ≤ 160 := by
  dsimp only [slotSaltDecC, isSlotChalSaltE, slotKeyOfC, sampleSlotMsgKeyC, orE, eqSaltE, saltOfE,
    eqChalSomeE, eqADE, eqCE, decKE,
    CryptoGames.AEAD.Costed.saltWireOps, Ops.sum, CryptoGames.OTCCA.Costed.otccaOps]
  unfold_vars; dsimp only [Comp.nodes, Expr.nodes]
  cases nf
  · have hite : ∀ {α : Type} (x y : α), (if false = true then x else y) = y := fun _ _ => rfl
    rw [hite]; dsimp only [Expr.nodes]; omega
  · have hite : ∀ {α : Type} (x y : α), (if true = true then x else y) = x := fun _ _ => rfl
    rw [hite]; dsimp only [Expr.nodes]; omega

lemma slotRedHandleC_size_le
    {slTy srTy : Ty (CryptoGames.AEAD.Costed.saltWireSig Pt ℓ)} (k qR : ℕ)
    (hb1 : bits k ≤ bits qR + 16) (hb2 : bits (k + 1) ≤ bits qR + 16)
    (encL : ∀ {Γ}, Comp _ _ (slTy :: .prod (CryptoGames.AEAD.Costed.slotAdTy Pt ℓ) (.base .plain) :: Γ)
      (.prod (.opt (CryptoGames.AEAD.Costed.lctTy Pt ℓ)) slTy))
    (decL : ∀ {Γ}, Comp _ _ (slTy :: .prod (CryptoGames.AEAD.Costed.slotAdTy Pt ℓ) (CryptoGames.AEAD.Costed.lctTy Pt ℓ) :: Γ)
      (.prod (.opt (.base .plain)) slTy))
    (encR : ∀ {Γ}, Comp _ _ (srTy :: .prod (CryptoGames.AEAD.Costed.slotAdTy Pt ℓ) (.base .plain) :: Γ)
      (.prod (.opt (CryptoGames.AEAD.Costed.lctTy Pt ℓ)) srTy))
    (decR : ∀ {Γ}, Comp _ _ (srTy :: .prod (CryptoGames.AEAD.Costed.slotAdTy Pt ℓ) (CryptoGames.AEAD.Costed.lctTy Pt ℓ) :: Γ)
      (.prod (.opt (.base .plain)) srTy))
    (hEL : ∀ {Γ}, (encL (Γ := Γ)).size ≤ 160 + bits qR)
    (hDL : ∀ {Γ}, (decL (Γ := Γ)).size ≤ 160 + bits qR)
    (hER : ∀ {Γ}, (encR (Γ := Γ)).size ≤ 160 + bits qR)
    (hDR : ∀ {Γ}, (decR (Γ := Γ)).size ≤ 160 + bits qR) :
    (slotRedHandleC C clampedProtoSignalCodec ℓ encT idOf 1 1 k encL decL encR decR).size ≤
      900 + 8 * bits qR := by
  have hc1 : bits 1 = 1 := rfl
  let Δ0 : List (Ty (CryptoGames.AEAD.Costed.saltWireSig Pt ℓ)) :=
    [.prod (.tbl slTy) (.tbl srTy), (CryptoGames.AEAD.Costed.slotOtccaCodec Pt ℓ).Q]
  have hel := hEL (Γ := Δ0); have hdl := hDL (Γ := Δ0)
  have her := hER (Γ := Δ0); have hdr := hDR (Γ := Δ0)
  dsimp only [Δ0, slotRedHandleC, slotRedEncC, slotRedDecC, querySlotEncC, querySlotDecC, leE] at hel hdl her hdr ⊢
  unfold_vars; dsimp only [Comp.size, Expr.size] at hel hdl her hdr ⊢
  simp only [hc1]; omega

lemma slotRedHandleC_nodes_le
    {slTy srTy : Ty (CryptoGames.AEAD.Costed.saltWireSig Pt ℓ)} (k : ℕ)
    (encL : ∀ {Γ}, Comp _ _ (slTy :: .prod (CryptoGames.AEAD.Costed.slotAdTy Pt ℓ) (.base .plain) :: Γ)
      (.prod (.opt (CryptoGames.AEAD.Costed.lctTy Pt ℓ)) slTy))
    (decL : ∀ {Γ}, Comp _ _ (slTy :: .prod (CryptoGames.AEAD.Costed.slotAdTy Pt ℓ) (CryptoGames.AEAD.Costed.lctTy Pt ℓ) :: Γ)
      (.prod (.opt (.base .plain)) slTy))
    (encR : ∀ {Γ}, Comp _ _ (srTy :: .prod (CryptoGames.AEAD.Costed.slotAdTy Pt ℓ) (.base .plain) :: Γ)
      (.prod (.opt (CryptoGames.AEAD.Costed.lctTy Pt ℓ)) srTy))
    (decR : ∀ {Γ}, Comp _ _ (srTy :: .prod (CryptoGames.AEAD.Costed.slotAdTy Pt ℓ) (CryptoGames.AEAD.Costed.lctTy Pt ℓ) :: Γ)
      (.prod (.opt (.base .plain)) srTy))
    (hEL : ∀ {Γ}, (encL (Γ := Γ)).nodes ≤ 160)
    (hDL : ∀ {Γ}, (decL (Γ := Γ)).nodes ≤ 160)
    (hER : ∀ {Γ}, (encR (Γ := Γ)).nodes ≤ 160)
    (hDR : ∀ {Γ}, (decR (Γ := Γ)).nodes ≤ 160) :
    (slotRedHandleC C clampedProtoSignalCodec ℓ encT idOf 1 1 k encL decL encR decR).nodes ≤ 900 := by
  let Δ0 : List (Ty (CryptoGames.AEAD.Costed.saltWireSig Pt ℓ)) :=
    [.prod (.tbl slTy) (.tbl srTy), (CryptoGames.AEAD.Costed.slotOtccaCodec Pt ℓ).Q]
  have hel := hEL (Γ := Δ0); have hdl := hDL (Γ := Δ0)
  have her := hER (Γ := Δ0); have hdr := hDR (Γ := Δ0)
  dsimp only [Δ0, slotRedHandleC, slotRedEncC, slotRedDecC, querySlotEncC, querySlotDecC, leE] at hel hdl her hdr ⊢
  unfold_vars; dsimp only [Comp.nodes, Expr.nodes] at hel hdl her hdr ⊢
  omega

end SwProgBounds

end Computational.Proofs.ReductionDsl.FsAtomicBounds
