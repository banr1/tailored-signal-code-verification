/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Computational.Proofs.ReductionDsl.FsAtomicBoundsBase -- proof-setup: allow-public-import
import Computational.Proofs.ReductionDsl.AtomicTablesHonest
import Computational.Proofs.ReductionDsl.GRedBoundedOfBounds
import Computational.Proofs.ReductionDsl.SizeBudgetBridge
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-! # Salt, wire, and fallback bounds for `FsAtomicBounds` -/

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

local macro "unfold_vars" : tactic =>
  `(tactic| try dsimp only [Expr.v0, Expr.v1, Expr.v2, Expr.v3, Expr.v4, Expr.v5, Expr.v6, Expr.v7])

section SwProgBounds

open CryptoGames.Ratchet.LibsignalInst.Costed

variable {Pt : Type} [DecidableEq Pt]
  (C : Crypto) (codec : SignalMessageProtoCodec) (ℓ : ℕ)
  (encT : Pt → PublicKey) (idOf : Party → IdentityKey)

theorem fsSlotSaltRedAtomic_bounds (hℓ : ℓ < 10 ^ 6) (qR qep j : ℕ)
    (hj : j ≤ 2 * (qR + maxForwardJumps + 1)) :
    GRedBounded (fsSlotSaltRedAtomic (Pt := Pt) C ℓ encT idOf qR j)
      (fun _ => 1) (fun _ => 0) qR qR (ratchetFsAdapterBudget qR qep) := by
  have hbud : 16000000 + 16000000 * qR + 1000 * qR ^ 2 ≤ ratchetFsAdapterBudget qR qep := by
    unfold ratchetFsAdapterBudget; nlinarith
  have hqR_le : qR ≤ ratchetFsAdapterBudget qR qep := by
    unfold ratchetFsAdapterBudget; omega
  have hdiv : ℓ / 32 ≤ 31250 := by omega
  have hmfj : maxForwardJumps = 25000 := rfl
  have hN : (if CryptoGames.FSAEAD.Thm5.isLookaheadHop j then qR + (maxForwardJumps + 1) else qR) ≤
      qR + 25002 := by split_ifs <;> omega
  have hj1 : j / 2 ≤ qR + 25002 := by omega
  have hj2 : j / 2 + 1 ≤ qR + 25002 := by omega
  have hb1 := bits_le_qR_add_15 hj1
  have hb2 := bits_le_qR_add_15 hj2
  have hc1 : bits 1 = 1 := rfl
  refine CryptoVerification.E2E.Costed.gRedBounded_of_bounds _ _ _ _ _ _ ?_ ?_ ?_
    (atomicFsOps_sizeHonest ℓ Pt C encT) (atomicBaseSamplers_sizeHonest ℓ Pt)
  · dsimp only [fsSlotSaltRedAtomic]
    have hl1 : ∀ {Γ}, compCostBound swOpCU slotSwSC slotSwQC
        (otImplEncC (Pt := Pt) C clampedProtoSignalCodec ℓ encT idOf 1 1 (Γ := Γ)) ≤
        3000000 + 50 * qR := by
      intro Γ; refine (compCostBound_le_UB _ _ _ _).trans ?_
      dsimp only [otImplEncC, sampleSlotIdealC, isSomeE, encRE,
        CryptoGames.AEAD.Costed.saltWireOps, Ops.sum, CryptoGames.OTCCA.Costed.otccaOps,
        CryptoGames.AEAD.Costed.slotOtccaIface, Iface.withSamp]
      unfold_vars
      dsimp only [compCostBoundUB, exprCostBoundUB, swOpCU, slotSwSC]; omega
    have hl2 : ∀ {Γ}, compCostBound swOpCU slotSwSC slotSwQC
        (otImplDecC (Pt := Pt) C clampedProtoSignalCodec ℓ encT idOf 1 1 (Γ := Γ)) ≤
        1000000 + 50 * qR := by
      intro Γ; refine (compCostBound_le_UB _ _ _ _).trans ?_
      dsimp only [otImplDecC, orE, eqChalSomeE, eqADE, eqCE, decRE,
        CryptoGames.AEAD.Costed.saltWireOps, Ops.sum, CryptoGames.OTCCA.Costed.otccaOps]
      unfold_vars
      dsimp only [compCostBoundUB, exprCostBoundUB, swOpCU]; omega
    have hh := slotRedHandleC_cost_le (Pt := Pt) C ℓ encT idOf (j / 2) qR hb1 hb2
      (otImplEncC C clampedProtoSignalCodec ℓ encT idOf 1 1)
      (otImplDecC C clampedProtoSignalCodec ℓ encT idOf 1 1)
      (slotSaltEncC C clampedProtoSignalCodec ℓ encT idOf 1 1 false qR)
      (slotSaltDecC C clampedProtoSignalCodec ℓ encT idOf 1 1 false false qR)
      hl1 hl2
      (fun {Γ} => slotSaltEncC_cost_le (Pt := Pt) (Γ := Γ) C ℓ encT idOf false qR)
      (fun {Γ} => slotSaltDecC_cost_le (Pt := Pt) (Γ := Γ) C ℓ encT idOf false false qR)
    refine (compilePureRed_totalCost_le_UB (ReductionDsl.slotOtccaCodec ℓ Pt)
      (slotSwMacroBundle (Pt := Pt) C ℓ encT idOf) _ rfl rfl swOpCU slotSwSC slotSwQC
      (swOpMacro_cost_le C ℓ encT idOf hℓ) (slotSwSampMacro_cost_le C ℓ encT idOf hℓ)
      (slotSwQueryMacro_cost_le C ℓ encT idOf hℓ)
      (cInit := 8000000 + 400 * qR) (cHandle := 5000000 + 200 * qR) (cFin := 20) ?_ hh ?_ qR).trans ?_
    · dsimp only [slotSaltRedProg, slotSaltInitC, sampleSlotSeedC, emptySaltSlotStE,
        CryptoGames.AEAD.Costed.saltWireOps, Ops.sum, CryptoGames.OTCCA.Costed.otccaOps,
        CryptoGames.AEAD.Costed.slotOtccaIface, Iface.withSamp]
      unfold_vars
      dsimp only [compCostBound, exprCostBound, slotSwSC]
      simp only [hc1]; omega
    · dsimp only [slotSaltRedProg]
      unfold_vars; dsimp only [compCostBound, exprCostBound]; omega
    · have hcc : (ReductionDsl.slotOtccaCodec ℓ Pt).codecCost ≤ 200000 := by
        dsimp [ReductionDsl.slotOtccaCodec]; omega
      have hmax : max (slotOtccaTargetIface ℓ Pt).uCost
          (5000000 + 200 * qR + (ReductionDsl.slotOtccaCodec ℓ Pt).codecCost) ≤
          6000000 + 200 * qR := by dsimp [slotOtccaTargetIface]; omega
      have hmul := Nat.mul_le_mul_left qR hmax
      nlinarith
  · refine Computational.Proofs.ReductionDsl.SizeBudgetBridge.size_le_budget_of_log_cost_mono
      (C₀ := 1000000) (C₁ := 20) (by norm_num) (by norm_num) hqR_le ?_
    dsimp only [fsSlotSaltRedAtomic]
    refine (compilePureRed_size_le_nodes (ReductionDsl.slotOtccaCodec ℓ Pt)
      (slotSwMacroBundle (Pt := Pt) C ℓ encT idOf) _ rfl rfl 650
      (fun o => Nat.le_of_succ_le (swOpMacro_size_le C ℓ encT idOf o))
      (fun s => Nat.le_of_succ_le (slotSwSampMacro_size_le C ℓ encT idOf hℓ s))
      (fun g => Nat.le_of_succ_le (slotSwQueryMacro_size_le C ℓ encT idOf g))).trans ?_
    have hbN := bits_le_bits_add_16 hN
    have hhS := slotRedHandleC_size_le (Pt := Pt) C ℓ encT idOf (j / 2) qR
      (bits_le_bits_add_16 hj1) (bits_le_bits_add_16 hj2)
      (otImplEncC C clampedProtoSignalCodec ℓ encT idOf 1 1)
      (otImplDecC C clampedProtoSignalCodec ℓ encT idOf 1 1)
      (slotSaltEncC C clampedProtoSignalCodec ℓ encT idOf 1 1 false qR)
      (slotSaltDecC C clampedProtoSignalCodec ℓ encT idOf 1 1 false false qR)
      (fun {Γ} => by
        dsimp only [otImplEncC, sampleSlotIdealC, isSomeE, encRE,
          CryptoGames.AEAD.Costed.saltWireOps, Ops.sum, CryptoGames.OTCCA.Costed.otccaOps]
        unfold_vars; dsimp only [Comp.size, Expr.size, Sum.elim]; omega)
      (fun {Γ} => by
        dsimp only [otImplDecC, orE, eqChalSomeE, eqADE, eqCE, decRE,
          CryptoGames.AEAD.Costed.saltWireOps, Ops.sum, CryptoGames.OTCCA.Costed.otccaOps]
        unfold_vars; dsimp only [Comp.size, Expr.size, Sum.elim]; omega)
      (fun {Γ} => (slotSaltEncC_size_le (Pt := Pt) (Γ := Γ) C ℓ encT idOf false qR).trans (by omega))
      (fun {Γ} => slotSaltDecC_size_le (Pt := Pt) (Γ := Γ) C ℓ encT idOf false false qR)
    have hhN := slotRedHandleC_nodes_le (Pt := Pt) C ℓ encT idOf (j / 2)
      (otImplEncC C clampedProtoSignalCodec ℓ encT idOf 1 1)
      (otImplDecC C clampedProtoSignalCodec ℓ encT idOf 1 1)
      (slotSaltEncC C clampedProtoSignalCodec ℓ encT idOf 1 1 false qR)
      (slotSaltDecC C clampedProtoSignalCodec ℓ encT idOf 1 1 false false qR)
      (fun {Γ} => by dsimp only [otImplEncC, sampleSlotIdealC, isSomeE, encRE]; unfold_vars; dsimp only [Comp.nodes, Expr.nodes]; omega)
      (fun {Γ} => by dsimp only [otImplDecC, orE, eqChalSomeE, eqADE, eqCE, decRE]; unfold_vars; dsimp only [Comp.nodes, Expr.nodes]; omega)
      (fun {Γ} => (slotSaltEncC_nodes_le (Pt := Pt) (Γ := Γ) C ℓ encT idOf false qR).trans (by omega))
      (fun {Γ} => slotSaltDecC_nodes_le (Pt := Pt) (Γ := Γ) C ℓ encT idOf false false qR)
    dsimp only [CostedReduction.size, CostedReduction.nodes, slotSaltRedProg, slotSaltInitC,
      sampleSlotSeedC, emptySaltSlotStE]
    generalize hhs : (slotRedHandleC (Pt := Pt) C clampedProtoSignalCodec ℓ encT idOf 1 1 (j / 2)
      _ _ _ _).size = hs
    generalize hhn : (slotRedHandleC (Pt := Pt) C clampedProtoSignalCodec ℓ encT idOf 1 1 (j / 2)
      _ _ _ _).nodes = hn
    have hhs' : hs ≤ 900 + 8 * bits qR := by rw [← hhs]; exact hhS
    have hhn' : hn ≤ 900 := by rw [← hhn]; exact hhN
    unfold_vars; dsimp only [Comp.size, Expr.size, Comp.nodes, Expr.nodes]
    simp only [hc1]; omega
  · dsimp only [fsSlotSaltRedAtomic]
    refine (compilePureRed_totalQueries_le (ReductionDsl.slotOtccaCodec ℓ Pt)
      (slotSwMacroBundle (Pt := Pt) C ℓ encT idOf) _ rfl rfl (fun _ => 1) (fun _ => 0)
      (fun _ => 1) (fun _ => 0)
      (fun s => by
        cases s with
        | inl u =>
          cases u
          simp [slotSwMacroBundle, sampleIdealComp, sampleU64Comp, Comp.queries]
        | inr t =>
          rcases t with _ | N | (_ | _) <;>
            simp [slotSwMacroBundle, sampleMsgKeyComp, Comp.queries])
      (fun g => by cases g <;> simp [slotSwMacroBundle, Comp.queries]) qR).trans ?_
    simp [CostedReduction.totalQueries, slotSaltRedProg, slotSaltInitC, slotRedHandleC,
      slotRedEncC, slotRedDecC, otImplEncC, otImplDecC, slotSaltEncC, slotSaltDecC,
      slotKeyOfC, sampleSlotSeedC, sampleSlotIdealC, sampleSlotMsgKeyC,
      querySlotEncC, querySlotDecC, Comp.queries]

theorem fsLSaltRedAtomic_bounds (hℓ : ℓ < 10 ^ 6) (qR qep : ℕ) :
    GRedBounded (fsLSaltRedAtomic (Pt := Pt) C ℓ encT idOf)
      (fun _ => 1) (fun _ => 0) qR qR (ratchetFsAdapterBudget qR qep) := by
  have hbud : 16000000 + 16000000 * qR + 1000 * qR ^ 2 ≤ ratchetFsAdapterBudget qR qep := by
    unfold ratchetFsAdapterBudget; nlinarith
  have hdiv : ℓ / 32 ≤ 31250 := by omega
  refine CryptoVerification.E2E.Costed.gRedBounded_of_bounds_const _ _ _ _ _ _ ?_ ?_ ?_
    (atomicFsOps_sizeHonest ℓ Pt C encT) (atomicBaseSamplers_sizeHonest ℓ Pt)
  · dsimp only [fsLSaltRedAtomic]
    refine (compilePureRed_totalCost_le_UB (ReductionDsl.slotOtccaCodec ℓ Pt)
      (lSaltMacroBundle (Pt := Pt) C ℓ encT idOf) _ rfl rfl swOpCU lSaltSC lSaltQC
      (swOpMacro_cost_le C ℓ encT idOf hℓ) (lSaltSampMacro_cost_le C ℓ encT idOf hℓ)
      (lSaltQueryMacro_cost_le C ℓ encT idOf)
      (cInit := 100) (cHandle := 3500000) (cFin := 50) ?_ ?_ ?_ qR).trans ?_
    · dsimp only [lSaltRedProg, lSaltInitC, sampleSaltBoolC,
        CryptoGames.AEAD.Costed.saltWireOps, Ops.sum, CryptoGames.OTCCA.Costed.otccaOps,
        CryptoGames.AEAD.Costed.saltRedIface, Iface.withSamp]
      unfold_vars; dsimp only [compCostBound, exprCostBound, lSaltSC]; omega
    · refine (compCostBound_le_UB _ _ _ _).trans ?_
      dsimp only [lSaltRedProg, lSaltEncC, lSaltDecC, sampleSaltIdealC, querySaltPrfC,
        isSomeE, saltOfE, encKE, decKE, orE, eqChalSomeE, eqADE, eqCE, eqSaltE,
        CryptoGames.AEAD.Costed.saltWireOps, Ops.sum, CryptoGames.OTCCA.Costed.otccaOps,
        CryptoGames.AEAD.Costed.saltRedIface, Iface.withSamp]
      unfold_vars
      dsimp only [compCostBoundUB, exprCostBoundUB, swOpCU, lSaltSC, lSaltQC]; omega
    · refine (compCostBound_le_UB _ _ _ _).trans ?_
      dsimp only [lSaltRedProg, lSaltFinishC, eqBoolE,
        CryptoGames.AEAD.Costed.saltWireOps, Ops.sum, CryptoGames.OTCCA.Costed.otccaOps]
      unfold_vars; dsimp only [compCostBoundUB, exprCostBoundUB]; omega
    · have hcc : (ReductionDsl.slotOtccaCodec ℓ Pt).codecCost ≤ 200000 := by
        dsimp [ReductionDsl.slotOtccaCodec]; omega
      have hmax : max (saltPrfTargetIface ℓ Pt).uCost
          (3500000 + (ReductionDsl.slotOtccaCodec ℓ Pt).codecCost) ≤ 4000000 := by
        dsimp [saltPrfTargetIface]; omega
      have hmul := Nat.mul_le_mul_left qR hmax
      nlinarith
  · dsimp only [fsLSaltRedAtomic]
    refine (compilePureRed_size_le (ReductionDsl.slotOtccaCodec ℓ Pt)
      (lSaltMacroBundle (Pt := Pt) C ℓ encT idOf) _ rfl rfl 650 (by omega)
      (swOpMacro_size_le C ℓ encT idOf) (lSaltSampMacro_size_le C ℓ encT idOf hℓ)
      (lSaltQueryMacro_size_le C ℓ encT idOf)).trans ?_
    dsimp only [CostedReduction.size, lSaltRedProg, lSaltInitC, lSaltEncC, lSaltDecC, lSaltFinishC,
      sampleSaltBoolC, sampleSaltIdealC, querySaltPrfC, isSomeE, saltOfE, encKE, decKE, orE,
      eqChalSomeE, eqADE, eqCE, eqSaltE, eqBoolE,
      CryptoGames.AEAD.Costed.saltWireOps, Ops.sum, CryptoGames.OTCCA.Costed.otccaOps]
    unfold_vars; dsimp only [Comp.size, Expr.size, Sum.elim]; simp only [reductionSizeBudget_eq]; omega
  · dsimp only [fsLSaltRedAtomic]
    refine (compilePureRed_totalQueries_le (ReductionDsl.slotOtccaCodec ℓ Pt)
      (lSaltMacroBundle (Pt := Pt) C ℓ encT idOf) _ rfl rfl (fun _ => 1) (fun _ => 0)
      (fun _ => 1) (fun _ => 0)
      (fun s => by
        rcases s with (e | ⟨⟩) | (_ | N | e)
        · exact nomatch e
        · simp [lSaltMacroBundle, sampleIdealComp, sampleU64Comp, Comp.queries]
        · simp [lSaltMacroBundle, Comp.queries]
        · simp [lSaltMacroBundle, Comp.queries]
        · exact nomatch e)
      (fun g => by cases g; simp [lSaltMacroBundle, Comp.queries]) qR).trans ?_
    simp [CostedReduction.totalQueries, lSaltRedProg, lSaltInitC, lSaltEncC, lSaltDecC,
      lSaltFinishC, sampleSaltBoolC, sampleSaltIdealC, querySaltPrfC, Comp.queries]

end SwProgBounds

section WireAndInstBounds

open CryptoGames.Ratchet.LibsignalInst.Costed

variable {Pt : Type} [DecidableEq Pt]
  (C : Crypto) (codec : SignalMessageProtoCodec) (ℓ : ℕ)
  (encT : Pt → PublicKey) (idOf : Party → IdentityKey)

theorem fsSlotWireRedAtomic_bounds (hℓ : ℓ < 10 ^ 6) (qR qep j : ℕ)
    (hj : j ≤ 2 * (qR + maxForwardJumps + 1)) :
    GRedBounded (fsSlotWireRedAtomic (Pt := Pt) C ℓ encT idOf qR j)
      (fun _ => 1) (fun _ => 0) qR qR (ratchetFsAdapterBudget qR qep) := by
  have hbud : 16000000 + 16000000 * qR + 1000 * qR ^ 2 ≤ ratchetFsAdapterBudget qR qep := by
    unfold ratchetFsAdapterBudget; nlinarith
  have hqR_le : qR ≤ ratchetFsAdapterBudget qR qep := by
    unfold ratchetFsAdapterBudget; omega
  have hdiv : ℓ / 32 ≤ 31250 := by omega
  have hmfj : maxForwardJumps = 25000 := rfl
  have hj1 : j / 2 ≤ qR + 25002 := by omega
  have hj2 : j / 2 + 1 ≤ qR + 25002 := by omega
  have hb1 := bits_le_qR_add_15 hj1
  have hb2 := bits_le_qR_add_15 hj2
  refine CryptoVerification.E2E.Costed.gRedBounded_of_bounds _ _ _ _ _ _ ?_ ?_ ?_
    (atomicFsOps_sizeHonest ℓ Pt C encT) (atomicBaseSamplers_sizeHonest ℓ Pt)
  · dsimp only [fsSlotWireRedAtomic]
    have hh := slotRedHandleC_cost_le (Pt := Pt) C ℓ encT idOf (j / 2) qR hb1 hb2
      (slotSaltEncC C clampedProtoSignalCodec ℓ encT idOf 1 1 false qR)
      (slotSaltDecC C clampedProtoSignalCodec ℓ encT idOf 1 1 true false qR)
      (slotSaltEncC C clampedProtoSignalCodec ℓ encT idOf 1 1 true qR)
      (slotSaltDecC C clampedProtoSignalCodec ℓ encT idOf 1 1 false true qR)
      (fun {Γ} => slotSaltEncC_cost_le (Pt := Pt) (Γ := Γ) C ℓ encT idOf false qR)
      (fun {Γ} => slotSaltDecC_cost_le (Pt := Pt) (Γ := Γ) C ℓ encT idOf true false qR)
      (fun {Γ} => slotSaltEncC_cost_le (Pt := Pt) (Γ := Γ) C ℓ encT idOf true qR)
      (fun {Γ} => slotSaltDecC_cost_le (Pt := Pt) (Γ := Γ) C ℓ encT idOf false true qR)
    refine (compilePureRed_totalCost_le_UB (ReductionDsl.slotOtccaCodec ℓ Pt)
      (slotSwMacroBundle (Pt := Pt) C ℓ encT idOf) _ rfl rfl swOpCU slotSwSC slotSwQC
      (swOpMacro_cost_le C ℓ encT idOf hℓ) (slotSwSampMacro_cost_le C ℓ encT idOf hℓ)
      (slotSwQueryMacro_cost_le C ℓ encT idOf hℓ)
      (cInit := 50) (cHandle := 5000000 + 200 * qR) (cFin := 20) ?_ hh ?_ qR).trans ?_
    · dsimp only [slotWireRedProg, emptySaltSlotStE,
        CryptoGames.AEAD.Costed.saltWireOps, Ops.sum, CryptoGames.OTCCA.Costed.otccaOps]
      dsimp only [compCostBound, exprCostBound]; omega
    · dsimp only [slotWireRedProg,
        CryptoGames.AEAD.Costed.saltWireOps, Ops.sum, CryptoGames.OTCCA.Costed.otccaOps]
      unfold_vars; dsimp only [compCostBound, exprCostBound]; omega
    · have hcc : (ReductionDsl.slotOtccaCodec ℓ Pt).codecCost ≤ 200000 := by
        dsimp [ReductionDsl.slotOtccaCodec]; omega
      have hmax : max (slotOtccaTargetIface ℓ Pt).uCost
          (5000000 + 200 * qR + (ReductionDsl.slotOtccaCodec ℓ Pt).codecCost) ≤
          6000000 + 200 * qR := by dsimp [slotOtccaTargetIface]; omega
      have hmul := Nat.mul_le_mul_left qR hmax
      nlinarith
  · refine Computational.Proofs.ReductionDsl.SizeBudgetBridge.size_le_budget_of_log_cost_mono
      (C₀ := 1000000) (C₁ := 20) (by norm_num) (by norm_num) hqR_le ?_
    dsimp only [fsSlotWireRedAtomic]
    refine (compilePureRed_size_le_nodes (ReductionDsl.slotOtccaCodec ℓ Pt)
      (slotSwMacroBundle (Pt := Pt) C ℓ encT idOf) _ rfl rfl 650
      (fun o => Nat.le_of_succ_le (swOpMacro_size_le C ℓ encT idOf o))
      (fun s => Nat.le_of_succ_le (slotSwSampMacro_size_le C ℓ encT idOf hℓ s))
      (fun g => Nat.le_of_succ_le (slotSwQueryMacro_size_le C ℓ encT idOf g))).trans ?_
    have hhS := slotRedHandleC_size_le (Pt := Pt) C ℓ encT idOf (j / 2) qR
      (bits_le_bits_add_16 hj1) (bits_le_bits_add_16 hj2)
      (slotSaltEncC C clampedProtoSignalCodec ℓ encT idOf 1 1 false qR)
      (slotSaltDecC C clampedProtoSignalCodec ℓ encT idOf 1 1 true false qR)
      (slotSaltEncC C clampedProtoSignalCodec ℓ encT idOf 1 1 true qR)
      (slotSaltDecC C clampedProtoSignalCodec ℓ encT idOf 1 1 false true qR)
      (fun {Γ} => (slotSaltEncC_size_le (Pt := Pt) (Γ := Γ) C ℓ encT idOf false qR).trans (by omega))
      (fun {Γ} => slotSaltDecC_size_le (Pt := Pt) (Γ := Γ) C ℓ encT idOf true false qR)
      (fun {Γ} => (slotSaltEncC_size_le (Pt := Pt) (Γ := Γ) C ℓ encT idOf true qR).trans (by omega))
      (fun {Γ} => slotSaltDecC_size_le (Pt := Pt) (Γ := Γ) C ℓ encT idOf false true qR)
    have hhN := slotRedHandleC_nodes_le (Pt := Pt) C ℓ encT idOf (j / 2)
      (slotSaltEncC C clampedProtoSignalCodec ℓ encT idOf 1 1 false qR)
      (slotSaltDecC C clampedProtoSignalCodec ℓ encT idOf 1 1 true false qR)
      (slotSaltEncC C clampedProtoSignalCodec ℓ encT idOf 1 1 true qR)
      (slotSaltDecC C clampedProtoSignalCodec ℓ encT idOf 1 1 false true qR)
      (fun {Γ} => (slotSaltEncC_nodes_le (Pt := Pt) (Γ := Γ) C ℓ encT idOf false qR).trans (by omega))
      (fun {Γ} => slotSaltDecC_nodes_le (Pt := Pt) (Γ := Γ) C ℓ encT idOf true false qR)
      (fun {Γ} => (slotSaltEncC_nodes_le (Pt := Pt) (Γ := Γ) C ℓ encT idOf true qR).trans (by omega))
      (fun {Γ} => slotSaltDecC_nodes_le (Pt := Pt) (Γ := Γ) C ℓ encT idOf false true qR)
    dsimp only [CostedReduction.size, CostedReduction.nodes, slotWireRedProg, emptySaltSlotStE]
    generalize hhs : (slotRedHandleC (Pt := Pt) C clampedProtoSignalCodec ℓ encT idOf 1 1 (j / 2)
      _ _ _ _).size = hs
    generalize hhn : (slotRedHandleC (Pt := Pt) C clampedProtoSignalCodec ℓ encT idOf 1 1 (j / 2)
      _ _ _ _).nodes = hn
    have hhs' : hs ≤ 900 + 8 * bits qR := by rw [← hhs]; exact hhS
    have hhn' : hn ≤ 900 := by rw [← hhn]; exact hhN
    unfold_vars; dsimp only [Comp.size, Expr.size, Comp.nodes, Expr.nodes]; omega
  · dsimp only [fsSlotWireRedAtomic]
    refine (compilePureRed_totalQueries_le (ReductionDsl.slotOtccaCodec ℓ Pt)
      (slotSwMacroBundle (Pt := Pt) C ℓ encT idOf) _ rfl rfl (fun _ => 1) (fun _ => 0)
      (fun _ => 1) (fun _ => 0)
      (fun s => by
        cases s with
        | inl u =>
          cases u
          simp [slotSwMacroBundle, sampleIdealComp, sampleU64Comp, Comp.queries]
        | inr t =>
          rcases t with _ | N | (_ | _) <;>
            simp [slotSwMacroBundle, sampleMsgKeyComp, Comp.queries])
      (fun g => by cases g <;> simp [slotSwMacroBundle, Comp.queries]) qR).trans ?_
    simp [CostedReduction.totalQueries, slotWireRedProg, slotRedHandleC, slotRedEncC, slotRedDecC,
      slotSaltEncC, slotSaltDecC, slotKeyOfC, sampleSlotIdealC, sampleSlotMsgKeyC,
      querySlotEncC, querySlotDecC, Comp.queries]

theorem fsLWireRedAtomic_bounds (hℓ : ℓ < 10 ^ 6) (qR qep : ℕ) :
    GRedBounded (fsLWireRedAtomic (Pt := Pt) C ℓ encT idOf qR)
      (fun _ => 1) (fun _ => 0) qR qR (ratchetFsAdapterBudget qR qep) := by
  have hdiv : ℓ / 32 ≤ 31250 := by omega
  have hb0 : bits 0 = 1 := rfl
  refine CryptoVerification.E2E.Costed.gRedBounded_of_bounds _ _ _ _ _ _ ?_ ?_ ?_
    (atomicFsOps_sizeHonest ℓ Pt C encT) (atomicBaseSamplers_sizeHonest ℓ Pt)
  · dsimp only [fsLWireRedAtomic]
    refine (compilePureRed_totalCost_le_UB (ReductionDsl.slotOtccaCodec ℓ Pt)
      (lWireMacroBundle (Pt := Pt) C ℓ encT idOf) _ rfl rfl swOpCU lWireSC lWireQC
      (swOpMacro_cost_le C ℓ encT idOf hℓ) (lWireSampMacro_cost_le C ℓ encT idOf)
      (lWireQueryMacro_cost_le C ℓ encT idOf hℓ)
      (cInit := 50) (cHandle := 500000 + 100 * qR) (cFin := 100) ?_ ?_ ?_ qR).trans ?_
    · dsimp only [lWireRedProg,
        CryptoGames.AEAD.Costed.saltWireOps, Ops.sum, CryptoGames.OTCCA.Costed.otccaOps]
      dsimp only [compCostBound, exprCostBound]; omega
    · refine (compCostBound_le_UB _ _ _ _).trans ?_
      dsimp only [lWireRedProg, lWireEncC, lWireDecC, wireSlotE,
        queryWireEncC, queryWireDecC, saltOfE, eqSaltE, idsOfE, hdrOfE, eqHdrE, fitPlainE, orE,
        CryptoGames.AEAD.Costed.saltWireOps, Ops.sum, CryptoGames.OTCCA.Costed.otccaOps,
        CryptoGames.AEAD.Costed.wireOps, CryptoGames.AEAD.Costed.wireRedIface, Iface.withSamp]
      unfold_vars
      dsimp only [compCostBoundUB, exprCostBoundUB, swOpCU, lWireQC]
      simp only [hb0]; omega
    · refine (compCostBound_le_UB _ _ _ _).trans ?_
      dsimp only [lWireRedProg, lWireFinishC, sampleWireBoolC, orE,
        CryptoGames.AEAD.Costed.saltWireOps, Ops.sum, CryptoGames.OTCCA.Costed.otccaOps,
        CryptoGames.AEAD.Costed.wireRedIface, Iface.withSamp]
      unfold_vars
      dsimp only [compCostBoundUB, exprCostBoundUB, lWireSC]
      simp only [hb0]; omega
    · have hcc : (ReductionDsl.slotOtccaCodec ℓ Pt).codecCost ≤ 200000 := by
        dsimp [ReductionDsl.slotOtccaCodec]; omega
      have hmax : max (wireOtccaTargetIface ℓ Pt).uCost
          (500000 + 100 * qR + (ReductionDsl.slotOtccaCodec ℓ Pt).codecCost) ≤
          1000000 + 100 * qR := by dsimp [wireOtccaTargetIface]; omega
      have hmul := Nat.mul_le_mul_left qR hmax
      have hbud : 16000000 + 16000000 * qR + 1000 * qR ^ 2 ≤ ratchetFsAdapterBudget qR qep := by
        unfold ratchetFsAdapterBudget; nlinarith
      nlinarith
  · have hqR_le : qR ≤ ratchetFsAdapterBudget qR qep := by
      have hbud : 16000000 + 16000000 * qR + 1000 * qR ^ 2 ≤ ratchetFsAdapterBudget qR qep := by
        unfold ratchetFsAdapterBudget; nlinarith
      omega
    refine Computational.Proofs.ReductionDsl.SizeBudgetBridge.size_le_budget_of_log_cost_mono
      (C₀ := 1000000) (C₁ := 1500) (by norm_num) (by norm_num) hqR_le ?_
    dsimp only [fsLWireRedAtomic]
    refine (compilePureRed_size_le (ReductionDsl.slotOtccaCodec ℓ Pt)
      (lWireMacroBundle (Pt := Pt) C ℓ encT idOf) _ rfl rfl 650 (by omega)
      (swOpMacro_size_le C ℓ encT idOf) (lWireSampMacro_size_le C ℓ encT idOf)
      (lWireQueryMacro_size_le C ℓ encT idOf)).trans ?_
    dsimp only [CostedReduction.size, lWireRedProg, lWireEncC, lWireDecC, lWireFinishC,
      wireSlotE, sampleWireBoolC, queryWireEncC, queryWireDecC, saltOfE, eqSaltE, idsOfE,
      hdrOfE, eqHdrE, fitPlainE, orE,
      CryptoGames.AEAD.Costed.saltWireOps, Ops.sum,
      CryptoGames.OTCCA.Costed.otccaOps, CryptoGames.AEAD.Costed.wireOps]
    unfold_vars; dsimp only [Comp.size, Expr.size, Sum.elim]; simp only [hb0]; omega
  · dsimp only [fsLWireRedAtomic]
    refine (compilePureRed_totalQueries_le (ReductionDsl.slotOtccaCodec ℓ Pt)
      (lWireMacroBundle (Pt := Pt) C ℓ encT idOf) _ rfl rfl (fun _ => 1) (fun _ => 0)
      (fun _ => 1) (fun _ => 0)
      (fun s => by
        rcases s with e | (_ | N | e)
        · exact nomatch e
        · simp [lWireMacroBundle, Comp.queries]
        · simp [lWireMacroBundle, Comp.queries]
        · exact nomatch e)
      (fun g => by cases g <;> simp [lWireMacroBundle, Comp.queries]) qR).trans ?_
    simp [CostedReduction.totalQueries, lWireRedProg, lWireEncC, lWireDecC, lWireFinishC,
      sampleWireBoolC, queryWireEncC, queryWireDecC, Comp.queries]

omit [DecidableEq Pt] in
theorem fsCostedRedsBoundedWitness_bounds (qR qep : ℕ) :
    fsCostedBounds qR qep (fsCostedRedsBoundedWitness (Pt := Pt) C codec ℓ encT idOf) := by
  have hbud : 16000000 + 16000000 * qR + 1000 * qR ^ 2 ≤ ratchetFsAdapterBudget qR qep := by
    unfold ratchetFsAdapterBudget; nlinarith
  have hbud_hyb : 100000000 + 130000000 * qR ≤ fsRatchetCostBudget qR qep := by
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
  have hmax21 : max 1 21 = 21 := rfl
  have hmax22 : max 1 22 = 22 := rfl
  have hOps := atomicFsOps_sizeHonest ℓ Pt C encT
  have hSamp := atomicBaseSamplers_sizeHonest ℓ Pt
  refine ⟨?_, fun _ _ => ?_, fun _ => ?_, fun _ _ => ?_, ?_, fun _ _ => ?_, ?_⟩
  · refine CryptoVerification.E2E.Costed.gRedBounded_of_bounds_const _ _ _ _ _ _ ?_ ?_ ?_ hOps hSamp
    · simp only [CostedReduction.totalCost, fsCostedRedsBoundedWitness, Comp.cost, Expr.cost,
        fsaeadPubTargetIface, fsaeadPubCodec, Nat.reduceAdd, hmax21]; omega
    · simp only [CostedReduction.size, fsCostedRedsBoundedWitness, Comp.size, Expr.size,
        reductionSizeBudget_eq]; omega
    · simp only [CostedReduction.totalQueries, fsCostedRedsBoundedWitness, Comp.queries]; omega
  · refine Computational.Proofs.ReductionDsl.MacroLift.gTwoStageBounded_of_bounds
        _ _ _ _ _ _ ?_ ?_ ?_ hOps hSamp
    · dsimp only [fsCostedRedsBoundedWitness]
      rw [Computational.Proofs.ReductionDsl.MacroLift.dummyTwoStageRed_totalCost]
      dsimp only [coinOnlyBaseIface, fsaeadRatchetCodec]
      simp only [Expr.cost, Nat.reduceAdd, hmax22]; omega
    · refine Nat.le_trans ?_ (Nat.le_add_right reductionSizeBudget _)
      dsimp only [fsCostedRedsBoundedWitness]
      rw [Computational.Proofs.ReductionDsl.MacroLift.dummyTwoStageRed_size]
      simp only [Expr.size, reductionSizeBudget_eq]; omega
    · dsimp only [fsCostedRedsBoundedWitness]
      rw [Computational.Proofs.ReductionDsl.MacroLift.dummyTwoStageRed_totalQueries]
  · refine Computational.Proofs.ReductionDsl.MacroLift.gTwoStageBounded_of_bounds
        _ _ _ _ _ _ ?_ ?_ ?_ hOps hSamp
    · dsimp only [fsCostedRedsBoundedWitness]
      rw [Computational.Proofs.ReductionDsl.MacroLift.dummyTwoStageRed_totalCost]
      dsimp only [slotOtccaTargetIface, fsaeadRatchetCodec]
      simp only [Expr.cost, Nat.reduceAdd, hmax22]; omega
    · refine Nat.le_trans ?_ (Nat.le_add_right reductionSizeBudget _)
      dsimp only [fsCostedRedsBoundedWitness]
      rw [Computational.Proofs.ReductionDsl.MacroLift.dummyTwoStageRed_size]
      simp only [Expr.size, reductionSizeBudget_eq]; omega
    · dsimp only [fsCostedRedsBoundedWitness]
      rw [Computational.Proofs.ReductionDsl.MacroLift.dummyTwoStageRed_totalQueries]
      exact Nat.zero_le _
  · refine CryptoVerification.E2E.Costed.gRedBounded_of_bounds_const _ _ _ _ _ _ ?_ ?_ ?_ hOps hSamp
    · simp only [CostedReduction.totalCost, fsCostedRedsBoundedWitness, Comp.cost, Expr.cost,
        slotOtccaTargetIface, ReductionDsl.slotOtccaCodec, Nat.reduceAdd, hmax21]; omega
    · simp only [CostedReduction.size, fsCostedRedsBoundedWitness, Comp.size, Expr.size,
        reductionSizeBudget_eq]; omega
    · simp only [CostedReduction.totalQueries, fsCostedRedsBoundedWitness, Comp.queries]; omega
  · refine CryptoVerification.E2E.Costed.gRedBounded_of_bounds_const _ _ _ _ _ _ ?_ ?_ ?_ hOps hSamp
    · simp only [CostedReduction.totalCost, fsCostedRedsBoundedWitness, Comp.cost, Expr.cost,
        saltPrfTargetIface, ReductionDsl.slotOtccaCodec, Nat.reduceAdd, hmax21]; omega
    · simp only [CostedReduction.size, fsCostedRedsBoundedWitness, Comp.size, Expr.size,
        reductionSizeBudget_eq]; omega
    · simp only [CostedReduction.totalQueries, fsCostedRedsBoundedWitness, Comp.queries]; omega
  · refine CryptoVerification.E2E.Costed.gRedBounded_of_bounds_const _ _ _ _ _ _ ?_ ?_ ?_ hOps hSamp
    · simp only [CostedReduction.totalCost, fsCostedRedsBoundedWitness, Comp.cost, Expr.cost,
        slotOtccaTargetIface, ReductionDsl.slotOtccaCodec, Nat.reduceAdd, hmax21]; omega
    · simp only [CostedReduction.size, fsCostedRedsBoundedWitness, Comp.size, Expr.size,
        reductionSizeBudget_eq]; omega
    · simp only [CostedReduction.totalQueries, fsCostedRedsBoundedWitness, Comp.queries]; omega
  · refine CryptoVerification.E2E.Costed.gRedBounded_of_bounds_const _ _ _ _ _ _ ?_ ?_ ?_ hOps hSamp
    · simp only [CostedReduction.totalCost, fsCostedRedsBoundedWitness, Comp.cost, Expr.cost,
        wireOtccaTargetIface, ReductionDsl.slotOtccaCodec, Nat.reduceAdd, hmax21]; omega
    · simp only [CostedReduction.size, fsCostedRedsBoundedWitness, Comp.size, Expr.size,
        reductionSizeBudget_eq]; omega
    · simp only [CostedReduction.totalQueries, fsCostedRedsBoundedWitness, Comp.queries]; omega

end WireAndInstBounds

end Computational.Proofs.ReductionDsl.FsAtomicBounds
