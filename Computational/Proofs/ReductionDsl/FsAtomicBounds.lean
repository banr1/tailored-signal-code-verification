/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Computational.Proofs.ReductionDsl.FsAtomicBoundsBase -- proof-setup: allow-public-import
public import Computational.Proofs.ReductionDsl.FsAtomicBoundsStage -- proof-setup: allow-public-import
public import Computational.Proofs.ReductionDsl.FsAtomicBoundsSaltWire -- proof-setup: allow-public-import

/-!
# Cost, query, and `fsCostedBounds` certificates

Re-exports `FsAtomicBoundsBase`, `FsAtomicBoundsStage`, and `FsAtomicBoundsSaltWire`, and
assembles `fsCostedRedsInst_bounds`.
-/

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

section WireAndInstBounds

open CryptoGames.Ratchet.LibsignalInst.Costed

variable {Pt : Type} [DecidableEq Pt]
  (C : Crypto) (codec : SignalMessageProtoCodec) (ℓ : ℕ)
  (encT : Pt → PublicKey) (idOf : Party → IdentityKey)


theorem fsCostedRedsInst_bounds (qR qep : ℕ) :
    fsCostedBounds qR qep (fsCostedRedsInst (Pt := Pt) C codec ℓ encT idOf qR) := by
  have hfb := fsCostedRedsBoundedWitness_bounds (Pt := Pt) C codec ℓ encT idOf qR qep
  rcases hfb with ⟨hb1, hb2, hb3, hb4, hb5, hb6, hb7⟩
  refine ⟨?_, fun j hj => ?_, fun la => ?_, fun j hj => ?_, ?_, fun j hj => ?_, ?_⟩
  · dsimp only [fsCostedRedsInst]
    by_cases hℓ : ℓ < 10 ^ 6
    · simp only [hℓ, ↓reduceIte]; exact fsPubRedAtomic_bounds C ℓ encT hℓ qR qep
    · simp only [hℓ, ↓reduceIte]; exact hb1
  · dsimp only [fsCostedRedsInst, guardTwoStageRed]
    by_cases hc : ℓ < 10 ^ 6 ∧ CryptoGames.FSAEAD.Thm5.slotToHybridHopIndex qR j ≤ 2 * (qR + maxForwardJumps + 1)
    · simp only [hc, and_self, ↓reduceIte]; exact fsPrgRedZeroAtomic_bounds C ℓ encT idOf hc.1 qR qep _ hc.2
    · simp only [hc, ↓reduceIte]; exact hb2 j hj
  · dsimp only [fsCostedRedsInst, guardTwoStageRed]
    by_cases hℓ : ℓ < 10 ^ 6
    · simp only [hℓ, ↓reduceIte]; exact fsMultiRedAtomic_bounds C ℓ encT idOf hℓ qR qep la
    · simp only [hℓ, ↓reduceIte]; exact hb3 la
  · dsimp only [fsCostedRedsInst]
    by_cases hc : ℓ < 10 ^ 6 ∧ CryptoGames.FSAEAD.Thm5.slotToHybridHopIndex qR j ≤ 2 * (qR + maxForwardJumps + 1)
    · simp only [hc, and_self, ↓reduceIte]; exact fsSlotSaltRedAtomic_bounds C ℓ encT idOf hc.1 qR qep _ hc.2
    · simp only [hc, ↓reduceIte]; exact hb4 j hj
  · dsimp only [fsCostedRedsInst]
    by_cases hℓ : ℓ < 10 ^ 6
    · simp only [hℓ, ↓reduceIte]; exact fsLSaltRedAtomic_bounds C ℓ encT idOf hℓ qR qep
    · simp only [hℓ, ↓reduceIte]; exact hb5
  · dsimp only [fsCostedRedsInst]
    by_cases hc : ℓ < 10 ^ 6 ∧ CryptoGames.FSAEAD.Thm5.slotToHybridHopIndex qR j ≤ 2 * (qR + maxForwardJumps + 1)
    · simp only [hc, and_self, ↓reduceIte]; exact fsSlotWireRedAtomic_bounds C ℓ encT idOf hc.1 qR qep _ hc.2
    · simp only [hc, ↓reduceIte]; exact hb6 j hj
  · dsimp only [fsCostedRedsInst]
    by_cases hℓ : ℓ < 10 ^ 6
    · simp only [hℓ, ↓reduceIte]; exact fsLWireRedAtomic_bounds C ℓ encT idOf hℓ qR qep
    · simp only [hℓ, ↓reduceIte]; exact hb7

end WireAndInstBounds

end Computational.Proofs.ReductionDsl.FsAtomicBounds
