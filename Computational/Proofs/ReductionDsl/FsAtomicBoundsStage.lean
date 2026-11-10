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

/-! # Two-stage reduction bounds for `FsAtomicBounds` -/

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

section HybProgBounds

open CryptoGames.FSAEAD.Thm5.Costed

variable {Pt : Type} [DecidableEq Pt]
  (C : Crypto) (ℓ : ℕ) (encT : Pt → PublicKey) (idOf : Party → IdentityKey)

abbrev lAE := lAeadR C clampedProtoSignalCodec ℓ encT idOf
abbrev lG := lChainPRG C.F
abbrev HSig' (Pt : Type) (ℓ : ℕ) :=
  CryptoGames.FSAEAD.Costed.fsSig (BitVec 256) (BitVec 256)
    (Header Pt × LibsignalMsgPublicPart) Unit (Plain ℓ) LCt
abbrev HSamp' (Pt : Type) (ℓ : ℕ) :=
  unifSamplers (S := HSig' Pt ℓ) CryptoGames.FSAEAD.Costed.fsStateSampleSort (fun _ => 1)
abbrev HybOps' :=
  Ops.sum
    (CryptoGames.PRG.Costed.prgOps (S := HSig' Pt ℓ)
      (Ty.prod Ty.nat (CryptoGames.FSAEAD.Costed.bt .ss))
      (Ty.prod (CryptoGames.FSAEAD.Costed.bt .ss) (CryptoGames.FSAEAD.Costed.bt .rs))
      (fun pw => PRGScheme.gen (lG C (Prod.fst pw)) (Prod.snd pw)) 1)
    (CryptoGames.OTCCA.Costed.otccaOps (S := HSig' Pt ℓ)
      (CryptoGames.FSAEAD.Costed.bt .rs)
      (Ty.prod Ty.nat (CryptoGames.FSAEAD.Costed.bt .ad))
      (CryptoGames.FSAEAD.Costed.bt .ad)
      (CryptoGames.FSAEAD.Costed.bt .msg)
      (CryptoGames.FSAEAD.Costed.bt .ct)
      (lAE C ℓ encT idOf) 1 Ty.unit (fun _ => ()))
abbrev PrgRedZeroIface' :=
  Iface.withSamp
    (Iface.withSamp (CryptoGames.PRG.Costed.prgIface (HSig' Pt ℓ))
      (CryptoGames.OTCCA.Costed.idealSamplers (S := HSig' Pt ℓ)
        (Ty.prod Ty.nat (CryptoGames.FSAEAD.Costed.bt .ad))
        (CryptoGames.FSAEAD.Costed.bt .ct)
        (lIdeal C clampedProtoSignalCodec ℓ encT) 1))
    (HSamp' Pt ℓ)
abbrev MultiRedIface' :=
  Iface.withSamp
    (CryptoGames.OTCCA.Costed.otccaIface (S := HSig' Pt ℓ)
      (Ty.prod Ty.nat (CryptoGames.FSAEAD.Costed.bt .ad))
      (CryptoGames.FSAEAD.Costed.bt .msg)
      (CryptoGames.FSAEAD.Costed.bt .ct)
      (lIdeal C clampedProtoSignalCodec ℓ encT) 1)
    (HSamp' Pt ℓ)

lemma genUpToC_ub_le {ι : Type} {T : OracleSpec ι}
    {I₀ : Iface (HSig' Pt ℓ) T} {Γ}
    {sC : (I₀.withSamp (HSamp' Pt ℓ)).smp.Samp → ℕ}
    {qC : (I₀.withSamp (HSamp' Pt ℓ)).Tag → ℕ}
    (_hsMK : sC (Sum.inr (UniformSamplerTag.base false)) ≤ 260)
    (_hsCK : sC (Sum.inr (UniformSamplerTag.base true)) ≤ 260)
    {jPos qR : ℕ} (hj : jPos ≤ qR + 25002)
    (i : Expr _ Γ .nat) (s : Expr _ Γ stTy) :
    compCostBoundUB hybOpCU sC qC
      (genUpToC (I₀ := I₀) (lAE C ℓ encT idOf) (lG C) 1 1 maxForwardJumps jPos i s) ≤
      exprCostBoundUB hybOpCU i + exprCostBoundUB hybOpCU s + 45500000 + 5 * qR := by
  have hbJ := bits_le_qR_add_15 hj
  have hb1 : bits 1 = 1 := rfl
  have hstep : ∀ {Δ}, compCostBoundUB hybOpCU sC qC
      (genStepKcBody (I₀ := I₀) (Γ := Δ) (lAE C ℓ encT idOf) (lG C) 1 1) ≤ 1800 := by
    intro Δ
    dsimp only [genStepKcBody, appendKcE, prgGenE, Ops.sum,
      CryptoGames.PRG.Costed.prgOps, CryptoGames.OTCCA.Costed.otccaOps, Iface.withSamp]
    unfold_vars
    dsimp only [compCostBoundUB, exprCostBoundUB, hybOpCU]
    simp only [hb1]
    omega
  have hmfj : maxForwardJumps = 25000 := rfl
  dsimp only [genUpToC, genUpToBody, withKcE, hsNKeys, hsKeysT, callC]
  generalize hbs : genStepKcBody (I₀ := I₀) (lAE C ℓ encT idOf) (lG C) 1 1 (Γ := _) = bs
  have hstep' : compCostBoundUB hybOpCU sC qC bs ≤ 1800 := by rw [← hbs]; exact hstep
  unfold_vars
  dsimp only [compCostBoundUB, exprCostBoundUB]
  simp only [hmfj]
  omega

lemma chainFromC_ub_le {ι : Type} {T : OracleSpec ι}
    {I₀ : Iface (HSig' Pt ℓ) T} {Γ}
    {sC : (I₀.withSamp (HSamp' Pt ℓ)).smp.Samp → ℕ}
    {qC : (I₀.withSamp (HSamp' Pt ℓ)).Tag → ℕ}
    (fuel : ℕ) (c : Expr _ Γ .nat) (w : Expr _ Γ _) (m : Expr _ Γ .nat) :
    compCostBoundUB hybOpCU sC qC
      (chainFromC (I := I₀.withSamp (HSamp' Pt ℓ))
        (lAE C ℓ encT idOf) (lG C) 1 1 fuel c w m) ≤
      exprCostBoundUB hybOpCU c + exprCostBoundUB hybOpCU w + exprCostBoundUB hybOpCU m +
        20 + 100 * fuel := by
  have hb0 : bits 0 = 1 := rfl
  have hb1 : bits 1 = 1 := rfl
  dsimp only [chainFromC, chainFromBody, callC, prgGenE]
  unfold_vars
  dsimp only [compCostBoundUB, exprCostBoundUB, hybOpCU]
  simp only [hb0, hb1, Nat.reduceAdd]
  omega

lemma senderKeyBody_ub_le {ι : Type} {T : OracleSpec ι}
    {I₀ : Iface (HSig' Pt ℓ) T} {Γ}
    {sC : (I₀.withSamp (HSamp' Pt ℓ)).smp.Samp → ℕ}
    {qC : (I₀.withSamp (HSamp' Pt ℓ)).Tag → ℕ}
    (hsCK : sC (Sum.inr (UniformSamplerTag.base true)) ≤ 260) (qR : ℕ) :
    compCostBoundUB hybOpCU sC qC
      (senderKeyBody (I₀ := I₀) (lAE C ℓ encT idOf) (lG C) 1 1 qR (Γ := Γ)) ≤
      2000 + 150 * qR := by
  have hb0 : bits 0 = 1 := rfl
  have hb1 : bits 1 = 1 := rfl
  dsimp only [senderKeyBody, revealBody, chainFromC, chainFromBody, hsCorrAt, hsCorrKey,
    hsLastSent, prgGenE, callC, Ops.sum,
    CryptoGames.PRG.Costed.prgOps, CryptoGames.OTCCA.Costed.otccaOps, Iface.withSamp]
  unfold_vars
  dsimp only [compCostBoundUB, exprCostBoundUB, hybOpCU]
  simp only [hb0, hb1, Nat.reduceAdd]
  omega

lemma hybHandlePreC_cost_le {ι : Type} {T : OracleSpec ι}
    {I₀ : Iface (HSig' Pt ℓ) T}
    {sC : (I₀.withSamp (HSamp' Pt ℓ)).smp.Samp → ℕ}
    {qC : (I₀.withSamp (HSamp' Pt ℓ)).Tag → ℕ}
    (hsMK : sC (Sum.inr (UniformSamplerTag.base false)) ≤ 260)
    (hsCK : sC (Sum.inr (UniformSamplerTag.base true)) ≤ 260)
    {jPos mSlot qR : ℕ} (hj : jPos ≤ qR + 25002) (hm : mSlot ≤ qR + 25002) (la : Bool)
    (sampleIdeal : ∀ {Δ}, Expr _ Δ _ → Comp _ (I₀.withSamp (HSamp' Pt ℓ)) Δ _)
    (specialEnc : Option (∀ {Δ}, Expr _ Δ _ → Comp _ (I₀.withSamp (HSamp' Pt ℓ)) Δ _))
    (specialDec : Option (∀ {Δ}, Expr _ Δ _ → Comp _ (I₀.withSamp (HSamp' Pt ℓ)) Δ _))
    (hId : ∀ {Δ} (ia : Expr _ Δ _),
      compCostBoundUB hybOpCU sC qC (sampleIdeal ia) ≤ exprCostBoundUB hybOpCU ia + 2500000)
    (hEnc : match specialEnc with
      | none => True
      | some f => ∀ {Δ} (x : Expr _ Δ _),
          compCostBoundUB hybOpCU sC qC (f x) ≤ exprCostBoundUB hybOpCU x + 2600000)
    (hDec : match specialDec with
      | none => True
      | some f => ∀ {Δ} (x : Expr _ Δ _),
          compCostBoundUB hybOpCU sC qC (f x) ≤ exprCostBoundUB hybOpCU x + 70000) :
    compCostBound hybOpCU sC qC
      (hybHandlePreC (I₀ := I₀) (lAE C ℓ encT idOf) (lG C) 1 1 maxForwardJumps qR jPos mSlot la
        sampleIdeal specialEnc specialDec) ≤
      60000000 + 2000 * qR := by
  have hmfj : maxForwardJumps = 25000 := rfl
  have hb0 : bits 0 = 1 := rfl
  have hb1 : bits 1 = 1 := rfl
  have hb2 : bits 2 = 2 := rfl
  have hbM := bits_le_qR_add_15 hm
  have hbS : bits 25000 ≤ qR + 15 := bits_le_qR_add_15 (by omega)
  have hdecB : ∀ {Δ}, compCostBoundUB hybOpCU sC qC
      (decIdxBody (I := I₀.withSamp (HSamp' Pt ℓ))
        (lAE C ℓ encT idOf) (lG C) 1 1 mSlot specialDec (Γ := Δ)) ≤ 1000000 + 10 * qR := by
    intro Δ
    dsimp only [decIdxBody, hsKeysT, isCompromisedE, isCompromisedBody, hsCorrAt, aeadDecE, callE]
    cases specialDec with
    | none =>
      unfold_vars
      dsimp only [compCostBoundUB, exprCostBoundUB, hybOpCU]
      simp only [hb0, hb1]; omega
    | some sD =>
      have hs := hDec (Δ := .prod (.prod (.opt (CryptoGames.FSAEAD.Costed.bt .msg))
        (.prod .nat (.prod (CryptoGames.FSAEAD.Costed.bt .ad)
          (CryptoGames.FSAEAD.Costed.bt .ct)))) hsTy :: Δ)
        (.pair (.pair (.fst (.snd (.fst .v0))) (.fst (.snd (.snd (.fst .v0)))))
          (.snd (.snd (.snd (.fst .v0)))))
      dsimp only [Expr.v0, exprCostBoundUB] at hs
      unfold_vars
      dsimp only [compCostBoundUB, exprCostBoundUB, hybOpCU]
      simp only [hb0, hb1]
      generalize hsdx : compCostBoundUB hybOpCU sC qC (sD _) = sdx at hs ⊢
      omega
  have hencB : ∀ {Δ}, compCostBoundUB hybOpCU sC qC
      (encIdxBody (I := I₀.withSamp (HSamp' Pt ℓ))
        (lAE C ℓ encT idOf) (lG C) 1 1 mSlot sampleIdeal specialEnc (Γ := Δ)) ≤
      8500000 + 10 * qR := by
    intro Δ
    let Δ0 : List (Ty (HSig' Pt ℓ)) :=
      .prod (.prod .nat (.prod (CryptoGames.FSAEAD.Costed.bt .ad)
        (CryptoGames.FSAEAD.Costed.bt .msg))) hsTy :: Δ
    have hi1 := hId (Δ := Δ0) (.pair (.fst (.fst .v0)) (.fst (.snd (.fst .v0))))
    dsimp only [Δ0, encIdxBody, hsKeysT, isCompromisedE, isCompromisedBody, hsCorrAt,
      aeadEncE, callE, Expr.v0, exprCostBoundUB] at hi1 ⊢
    cases specialEnc with
    | none =>
      unfold_vars
      dsimp only [compCostBoundUB, exprCostBoundUB, hybOpCU]
      generalize hidx : compCostBoundUB hybOpCU sC qC (sampleIdeal _) = idx at hi1 ⊢
      simp only [hb0, hb1]; omega
    | some sE =>
      have hs := hEnc (Δ := Δ0) (.pair (.pair (.fst (.fst .v0)) (.fst (.snd (.fst .v0))))
        (.snd (.snd (.fst .v0))))
      dsimp only [Δ0, Expr.v0, exprCostBoundUB] at hs
      unfold_vars
      dsimp only [compCostBoundUB, exprCostBoundUB, hybOpCU]
      generalize hidx : compCostBoundUB hybOpCU sC qC (sampleIdeal _) = idx at hi1 ⊢
      generalize hsex : compCostBoundUB hybOpCU sC qC (sE _) = sex at hs ⊢
      simp only [hb0, hb1]; omega
  have hrcv : ∀ {Δ}, compCostBoundUB hybOpCU sC qC
      (receiveBody (I₀ := I₀) (lAE C ℓ encT idOf) (lG C) 1 1 maxForwardJumps jPos mSlot la
        specialDec (Γ := Δ)) ≤ 52000000 + 100 * qR := by
    intro Δ
    dsimp only [receiveBody, skippedContainsE, skippedRemoveE, skippedRemoveBody, withSkippedE,
      isCompromisedE, isCompromisedBody, prependNewSkippedBody,
      orE, hsLastSent, hsCorrAt, hsRecvIdx, hsSkipped, callE, callC]
    generalize hgc :
      genUpToC (I₀ := I₀) (lAE C ℓ encT idOf) (lG C) 1 1 maxForwardJumps jPos _ _ = gc
    have hg' : compCostBoundUB hybOpCU sC qC gc ≤ 45500050 + 5 * qR := by
      rw [← hgc]
      refine (genUpToC_ub_le (I₀ := I₀) (sC := sC) (qC := qC) C ℓ encT idOf hsMK hsCK hj _ _).trans ?_
      unfold_vars; dsimp only [Expr.v0, exprCostBoundUB]; omega
    unfold_vars
    dsimp only [Expr.v0, compCostBoundUB, exprCostBoundUB]
    generalize hd1x : compCostBoundUB hybOpCU sC qC
      (decIdxBody (I := I₀.withSamp (HSamp' Pt ℓ)) (lAE C ℓ encT idOf) (lG C) 1 1 mSlot specialDec
        (Γ := stTy :: _)) = d1x
    have hd1 : d1x ≤ 1000000 + 10 * qR := by rw [← hd1x]; exact hdecB
    generalize hd2x : compCostBoundUB hybOpCU sC qC
      (decIdxBody (I := I₀.withSamp (HSamp' Pt ℓ)) (lAE C ℓ encT idOf) (lG C) 1 1 mSlot specialDec
        (Γ := _)) = d2x
    have hd2 : d2x ≤ 1000000 + 10 * qR := by rw [← hd2x]; exact hdecB
    simp only [hmfj, hb1, Nat.reduceAdd]
    omega
  have hsk : ∀ {Δ}, compCostBoundUB hybOpCU sC qC
      (senderKeyBody (I₀ := I₀) (lAE C ℓ encT idOf) (lG C) 1 1 qR (Γ := Δ)) ≤
      2000 + 150 * qR :=
    fun {Δ} => senderKeyBody_ub_le (I₀ := I₀) C ℓ encT idOf hsCK qR (Γ := Δ)
  have htr : ∀ {Δ}, compCostBoundUB hybOpCU sC qC
      (transmitBody (I₀ := I₀) (lAE C ℓ encT idOf) (lG C) 1 1 maxForwardJumps jPos mSlot
        sampleIdeal specialEnc (Γ := Δ)) ≤ 54500000 + 100 * qR := by
    intro Δ
    dsimp only [transmitBody, mkHS, hsB, hsLastSent, hsCorrAt, hsRecvIdx, hsEnded, hsWin, hsLf,
      hsInTransit, hsChalls, hsNKeys, hsKeysT, hsCorrKey, hsSkipped, callC]
    generalize hgc :
      genUpToC (I₀ := I₀) (lAE C ℓ encT idOf) (lG C) 1 1 maxForwardJumps jPos _ _ = gc
    have hg' : compCostBoundUB hybOpCU sC qC gc ≤ 45500050 + 5 * qR := by
      rw [← hgc]
      refine (genUpToC_ub_le (I₀ := I₀) (sC := sC) (qC := qC) C ℓ encT idOf hsMK hsCK hj _ _).trans ?_
      unfold_vars; dsimp only [Expr.v0, hsLastSent, exprCostBoundUB]; simp only [hb1]; omega
    unfold_vars
    dsimp only [Expr.v0, hsLastSent, compCostBoundUB, exprCostBoundUB]
    generalize hex : compCostBoundUB hybOpCU sC qC (encIdxBody _ _ _ _ _ _ _) = ex
    have he' : ex ≤ 8500000 + 10 * qR := by rw [← hex]; exact hencB
    simp only [hb1]; omega
  have hch : ∀ {Δ}, compCostBoundUB hybOpCU sC qC
      (challengeBody (I₀ := I₀) (lAE C ℓ encT idOf) (lG C) 1 1 maxForwardJumps jPos mSlot
        sampleIdeal specialEnc (Γ := Δ)) ≤ 54500000 + 100 * qR := by
    intro Δ
    dsimp only [challengeBody, isSomeE, orE, mkHS, hsB, hsLastSent, hsCorrAt, hsRecvIdx, hsEnded,
      hsWin, hsLf, hsInTransit, hsChalls, hsNKeys, hsKeysT, hsCorrKey, hsSkipped, callC]
    generalize hgc :
      genUpToC (I₀ := I₀) (lAE C ℓ encT idOf) (lG C) 1 1 maxForwardJumps jPos _ _ = gc
    have hg' : compCostBoundUB hybOpCU sC qC gc ≤ 45500050 + 5 * qR := by
      rw [← hgc]
      refine (genUpToC_ub_le (I₀ := I₀) (sC := sC) (qC := qC) C ℓ encT idOf hsMK hsCK hj _ _).trans ?_
      unfold_vars; dsimp only [Expr.v0, hsLastSent, exprCostBoundUB]; simp only [hb1]; omega
    unfold_vars
    dsimp only [Expr.v0, hsLastSent, compCostBoundUB, exprCostBoundUB, hybOpCU]
    generalize hex : compCostBoundUB hybOpCU sC qC (encIdxBody _ _ _ _ _ _ _) = ex
    have he' : ex ≤ 8500000 + 10 * qR := by rw [← hex]; exact hencB
    simp only [hb1]; omega
  have hcs : ∀ {Δ}, compCostBoundUB hybOpCU sC qC
      (corruptSenderBody (I₀ := I₀) (lAE C ℓ encT idOf) (lG C) 1 1 qR la (Γ := Δ)) ≤
      5000 + 200 * qR := by
    intro Δ
    dsimp only [corruptSenderBody, mkHS, hsB, hsLastSent, hsCorrAt, hsRecvIdx, hsEnded, hsWin,
      hsLf, hsInTransit, hsChalls, hsNKeys, hsKeysT, hsCorrKey, hsSkipped, callC]
    unfold_vars
    dsimp only [compCostBoundUB, exprCostBoundUB]
    generalize hsx : compCostBoundUB hybOpCU sC qC (senderKeyBody _ _ _ _ _) = sx
    have hs1 : sx ≤ 2000 + 150 * qR := by rw [← hsx]; exact hsk
    omega
  have hdl : ∀ {Δ}, compCostBoundUB hybOpCU sC qC
      (deliverBody (I₀ := I₀) (lAE C ℓ encT idOf) (lG C) 1 1 maxForwardJumps qR jPos mSlot la
        specialDec (Γ := Δ)) ≤ 56000000 + 1000 * qR := by
    intro Δ
    dsimp only [deliverBody, findInTransitE, findInTransitBody, recMatchesE, challsContainsE,
      challsContainsBody, removeFromTransitE, removeFromTransitBody, isCompromisedE,
      isCompromisedBody, eqAdE, eqME, eqCE, orE, maxNatE, mkHS, hsB, hsLastSent, hsCorrAt,
      hsRecvIdx, hsEnded, hsWin, hsLf, hsInTransit, hsChalls, hsNKeys, hsKeysT, hsCorrKey,
      hsSkipped, recIdx, recAd, recMsg, recCt, callE, callC]
    unfold_vars
    dsimp only [compCostBoundUB, exprCostBoundUB, hybOpCU]
    generalize hrx : compCostBoundUB hybOpCU sC qC (receiveBody _ _ _ _ _ _ _ _ _) = rx
    have hr1 : rx ≤ 52000000 + 100 * qR := by rw [← hrx]; exact hrcv
    simp only [hmfj, hb1, hb2, Nat.reduceAdd]; omega
  have hij : ∀ {Δ}, compCostBoundUB hybOpCU sC qC
      (injectBody (I₀ := I₀) (lAE C ℓ encT idOf) (lG C) 1 1 maxForwardJumps qR jPos mSlot la
        specialDec (Γ := Δ)) ≤ 56000000 + 1000 * qR := by
    intro Δ
    dsimp only [injectBody, anyInTransitE, anyInTransitBody, recMatchesE, removeFromTransitE,
      removeFromTransitBody, isCompromisedE, isCompromisedBody, eqAdE, eqCE, orE, maxNatE,
      mkHS, hsB, hsLastSent, hsCorrAt, hsRecvIdx, hsEnded, hsWin, hsLf, hsInTransit, hsChalls,
      hsNKeys, hsKeysT, hsCorrKey, hsSkipped, recIdx, recAd, recCt, callE, callC]
    unfold_vars
    dsimp only [compCostBoundUB, exprCostBoundUB, hybOpCU]
    generalize hrx : compCostBoundUB hybOpCU sC qC (receiveBody _ _ _ _ _ _ _ _ _) = rx
    have hr1 : rx ≤ 52000000 + 100 * qR := by rw [← hrx]; exact hrcv
    simp only [hb1, Nat.reduceAdd]; omega
  dsimp only [hybHandlePreC]
  refine (caseSum_compCostBound_le _ _ _ _ _ _ (b := 59000020 + 2000 * qR)
    (by unfold_vars; dsimp only [exprCostBoundUB]; omega) ?_ ?_).trans (by omega)
  · refine (compCostBound_le_UB _ _ _ _).trans ?_
    dsimp only [callC]
    unfold_vars; dsimp only [compCostBoundUB, exprCostBoundUB]
    generalize hx : compCostBoundUB hybOpCU sC qC (transmitBody _ _ _ _ _ _ _ _ _) = x
    have hx' : x ≤ 54500000 + 100 * qR := by rw [← hx]; exact htr
    omega
  · refine (caseSum_compCostBound_le _ _ _ _ _ _ (b := 59000015 + 2000 * qR)
      (by unfold_vars; dsimp only [exprCostBoundUB]; omega) ?_ ?_).trans (by omega)
    · refine (compCostBound_le_UB _ _ _ _).trans ?_
      dsimp only [callC]
      unfold_vars; dsimp only [compCostBoundUB, exprCostBoundUB]
      generalize hx : compCostBoundUB hybOpCU sC qC (challengeBody _ _ _ _ _ _ _ _ _) = x
      have hx' : x ≤ 54500000 + 100 * qR := by rw [← hx]; exact hch
      omega
    · refine (caseSum_compCostBound_le _ _ _ _ _ _ (b := 59000010 + 2000 * qR)
        (by unfold_vars; dsimp only [exprCostBoundUB]; omega) ?_ ?_).trans (by omega)
      · refine (compCostBound_le_UB _ _ _ _).trans ?_
        dsimp only [callC]
        unfold_vars; dsimp only [compCostBoundUB, exprCostBoundUB]
        generalize hx : compCostBoundUB hybOpCU sC qC (corruptSenderBody _ _ _ _ _ _) = x
        have hx' : x ≤ 5000 + 200 * qR := by rw [← hx]; exact hcs
        omega
      · refine (caseSum_compCostBound_le _ _ _ _ _ _ (b := 59000005 + 2000 * qR)
          (by unfold_vars; dsimp only [exprCostBoundUB]; omega) ?_ ?_).trans (by omega)
        · refine (compCostBound_le_UB _ _ _ _).trans ?_
          dsimp only [orE, anyUncompInTransitE, anyUncompInTransitBody, isCompromisedE,
            isCompromisedBody, hsEnded, hsChalls, hsInTransit, hsCorrAt, recIdx, callE]
          unfold_vars
          dsimp only [compCostBoundUB, exprCostBoundUB]
          simp only [hb0]; omega
        · refine (caseSum_compCostBound_le _ _ _ _ _ _ (b := 59000000 + 2000 * qR)
            (by unfold_vars; dsimp only [exprCostBoundUB]; omega) ?_ ?_).trans (by omega)
          · refine (compCostBound_le_UB _ _ _ _).trans ?_
            dsimp only [callC]
            unfold_vars; dsimp only [compCostBoundUB, exprCostBoundUB]
            generalize hx : compCostBoundUB hybOpCU sC qC (deliverBody _ _ _ _ _ _ _ _ _ _) = x
            have hx' : x ≤ 56000000 + 1000 * qR := by rw [← hx]; exact hdl
            omega
          · refine (compCostBound_le_UB _ _ _ _).trans ?_
            dsimp only [callC]
            unfold_vars; dsimp only [compCostBoundUB, exprCostBoundUB]
            generalize hx : compCostBoundUB hybOpCU sC qC (injectBody _ _ _ _ _ _ _ _ _ _) = x
            have hx' : x ≤ 56000000 + 1000 * qR := by rw [← hx]; exact hij
            omega

lemma hybResumeC_cost_le {ι : Type} {T : OracleSpec ι}
    {I₀ : Iface (HSig' Pt ℓ) T}
    {sC : (I₀.withSamp (HSamp' Pt ℓ)).smp.Samp → ℕ}
    {qC : (I₀.withSamp (HSamp' Pt ℓ)).Tag → ℕ}
    (hsCK : sC (Sum.inr (UniformSamplerTag.base true)) ≤ 260)
    (qR : ℕ) (la : Bool) :
    compCostBound hybOpCU sC qC
      (hybResumeC (I₀ := I₀) (lAE C ℓ encT idOf) (lG C) 1 1 maxForwardJumps qR la) ≤
      20000 + 12000000 * qR := by
  have hmfj : maxForwardJumps = 25000 := rfl
  have hb0 : bits 0 = 1 := rfl
  have hb1 : bits 1 = 1 := rfl
  have hsk : ∀ {Δ}, compCostBoundUB hybOpCU sC qC
      (senderKeyBody (I₀ := I₀) (lAE C ℓ encT idOf) (lG C) 1 1 qR (Γ := Δ)) ≤
      2000 + 150 * qR :=
    fun {Δ} => senderKeyBody_ub_le (I₀ := I₀) C ℓ encT idOf hsCK qR (Γ := Δ)
  refine (compCostBound_le_UB _ _ _ _).trans ?_
  dsimp only [hybResumeC, corruptReceiverResumeBody, corruptReceiverDBody,
    mkHS, hsB, hsLastSent, hsCorrAt, hsRecvIdx, hsEnded, hsWin, hsLf,
    hsInTransit, hsChalls, hsNKeys, hsKeysT, hsCorrKey, hsSkipped, callC]
  generalize hcc :
    chainFromC (I := I₀.withSamp (HSamp' Pt ℓ))
      (lAE C ℓ encT idOf) (lG C) 1 1 ((maxForwardJumps + 1) * qR) _ _ _ = cc
  have hc1' : compCostBoundUB hybOpCU sC qC cc ≤ 50 + 2500100 * qR := by
    rw [← hcc]
    refine (chainFromC_ub_le (I₀ := I₀) (sC := sC) (qC := qC) C ℓ encT idOf
      ((maxForwardJumps + 1) * qR) _ _ _).trans ?_
    unfold_vars; dsimp only [hsRecvIdx, exprCostBoundUB]; simp only [hmfj]; omega
  unfold_vars
  dsimp only [hsRecvIdx, compCostBoundUB, exprCostBoundUB]
  generalize hsx : compCostBoundUB hybOpCU sC qC (senderKeyBody _ _ _ _ _) = sx
  have hs1 : sx ≤ 2000 + 150 * qR := by rw [← hsx]; exact hsk
  simp only [hmfj, hb0, hb1, Nat.reduceAdd]
  omega

private lemma genUpToC_size_le {ι : Type} {T : OracleSpec ι}
    {I₀ : Iface (HSig' Pt ℓ) T} {Γ}
    {jPos qR : ℕ} (hj : jPos ≤ qR + 25002)
    (i : Expr _ Γ .nat) (s : Expr _ Γ stTy) :
    (genUpToC (I₀ := I₀) (lAE C ℓ encT idOf) (lG C) 1 1 maxForwardJumps jPos i s).size ≤
      i.size + s.size + 800 + 2 * bits qR := by
  have hbJ := bits_le_bits_add_16 hj
  have hb1 : bits 1 = 1 := rfl
  have hb25000 := bits_25000_le
  have hb25001 := bits_25001_le
  have hstep : ∀ {Δ},
      (genStepKcBody (I₀ := I₀) (Γ := Δ) (lAE C ℓ encT idOf) (lG C) 1 1).size ≤ 300 := by
    intro Δ
    dsimp only [genStepKcBody, appendKcE, prgGenE]
    unfold_vars
    dsimp only [Comp.size, Expr.size, Ops.sum, Sum.elim, CryptoGames.PRG.Costed.prgOps]
    simp only [hb1]
    omega
  have hmfj : maxForwardJumps = 25000 := rfl
  dsimp only [genUpToC, genUpToBody, withKcE, hsNKeys, hsKeysT, callC]
  generalize hbs : genStepKcBody (I₀ := I₀) (lAE C ℓ encT idOf) (lG C) 1 1 (Γ := _) = bs
  have hstep' : bs.size ≤ 300 := by rw [← hbs]; exact hstep
  unfold_vars
  dsimp only [Comp.size, Expr.size]
  simp only [hmfj, Nat.reduceAdd]
  omega

private lemma chainFromC_size_le {ι : Type} {T : OracleSpec ι}
    {I₀ : Iface (HSig' Pt ℓ) T} {Γ}
    (fuel : ℕ) (c : Expr _ Γ .nat) (w : Expr _ Γ _) (m : Expr _ Γ .nat) :
    (chainFromC (I := I₀.withSamp (HSamp' Pt ℓ))
      (lAE C ℓ encT idOf) (lG C) 1 1 fuel c w m).size ≤
      c.size + w.size + m.size + 120 + bits fuel := by
  have hb0 : bits 0 = 1 := rfl
  have hb1 : bits 1 = 1 := rfl
  dsimp only [chainFromC, chainFromBody, callC, prgGenE]
  unfold_vars
  dsimp only [Comp.size, Expr.size, Ops.sum, Sum.elim, CryptoGames.PRG.Costed.prgOps]
  simp only [hb0, hb1, Nat.reduceAdd]
  omega

private lemma senderKeyBody_size_le {ι : Type} {T : OracleSpec ι}
    {I₀ : Iface (HSig' Pt ℓ) T} {Γ} (qR : ℕ) :
    (senderKeyBody (I₀ := I₀) (lAE C ℓ encT idOf) (lG C) 1 1 qR (Γ := Γ)).size ≤
      250 + 2 * bits qR := by
  have hb0 : bits 0 = 1 := rfl
  have hb1 : bits 1 = 1 := rfl
  dsimp only [senderKeyBody, revealBody, chainFromC, chainFromBody, hsCorrAt, hsCorrKey,
    hsLastSent, prgGenE, callC]
  unfold_vars
  dsimp only [Comp.size, Expr.size, Ops.sum, Sum.elim, CryptoGames.PRG.Costed.prgOps]
  simp only [hb0, hb1, Nat.reduceAdd]
  omega

private lemma genUpToC_nodes_le {ι : Type} {T : OracleSpec ι}
    {I₀ : Iface (HSig' Pt ℓ) T} {Γ} (jPos : ℕ)
    (i : Expr _ Γ .nat) (s : Expr _ Γ stTy) :
    (genUpToC (I₀ := I₀) (lAE C ℓ encT idOf) (lG C) 1 1 maxForwardJumps jPos i s).nodes ≤
      i.nodes + s.nodes + 800 := by
  have hstep : ∀ {Δ},
      (genStepKcBody (I₀ := I₀) (Γ := Δ) (lAE C ℓ encT idOf) (lG C) 1 1).nodes ≤ 300 := by
    intro Δ
    dsimp only [genStepKcBody, appendKcE, prgGenE]
    unfold_vars
    dsimp only [Comp.nodes, Expr.nodes]
    omega
  dsimp only [genUpToC, genUpToBody, withKcE, hsNKeys, hsKeysT, callC]
  generalize hbs : genStepKcBody (I₀ := I₀) (lAE C ℓ encT idOf) (lG C) 1 1 (Γ := _) = bs
  have hstep' : bs.nodes ≤ 300 := by rw [← hbs]; exact hstep
  unfold_vars
  dsimp only [Comp.nodes, Expr.nodes]
  omega

private lemma chainFromC_nodes_le {ι : Type} {T : OracleSpec ι}
    {I₀ : Iface (HSig' Pt ℓ) T} {Γ}
    (fuel : ℕ) (c : Expr _ Γ .nat) (w : Expr _ Γ _) (m : Expr _ Γ .nat) :
    (chainFromC (I := I₀.withSamp (HSamp' Pt ℓ))
      (lAE C ℓ encT idOf) (lG C) 1 1 fuel c w m).nodes ≤
      c.nodes + w.nodes + m.nodes + 120 := by
  dsimp only [chainFromC, chainFromBody, callC, prgGenE]
  unfold_vars
  dsimp only [Comp.nodes, Expr.nodes]
  omega

private lemma senderKeyBody_nodes_le {ι : Type} {T : OracleSpec ι}
    {I₀ : Iface (HSig' Pt ℓ) T} {Γ} (qR : ℕ) :
    (senderKeyBody (I₀ := I₀) (lAE C ℓ encT idOf) (lG C) 1 1 qR (Γ := Γ)).nodes ≤
      250 := by
  dsimp only [senderKeyBody, revealBody, chainFromC, chainFromBody, hsCorrAt, hsCorrKey,
    hsLastSent, prgGenE, callC]
  unfold_vars
  dsimp only [Comp.nodes, Expr.nodes]
  omega

private lemma receiveBody_size_le {ι : Type} {T : OracleSpec ι}
    {I₀ : Iface (HSig' Pt ℓ) T} {Γ}
    {jPos mSlot qR : ℕ} (hj : jPos ≤ qR + 25002) (hm : mSlot ≤ qR + 25002) (la : Bool)
    (specialDec : Option (∀ {Δ}, Expr _ Δ _ → Comp _ (I₀.withSamp (HSamp' Pt ℓ)) Δ _))
    (hDec : match specialDec with
      | none => True
      | some f => ∀ {Δ} (x : Expr _ Δ _), (f x).size ≤ x.size + 20) :
    (receiveBody (I₀ := I₀) (lAE C ℓ encT idOf) (lG C) 1 1 maxForwardJumps jPos mSlot la
      specialDec (Γ := Γ)).size ≤ 2500 + 10 * bits qR := by
  have hmfj : maxForwardJumps = 25000 := rfl
  have hb0 : bits 0 = 1 := rfl
  have hb1 : bits 1 = 1 := rfl
  have hbM := bits_le_bits_add_16 hm
  have hbS := bits_25000_le
  have hdecB : ∀ {Δ},
      (decIdxBody (I := I₀.withSamp (HSamp' Pt ℓ))
        (lAE C ℓ encT idOf) (lG C) 1 1 mSlot specialDec (Γ := Δ)).size ≤ 300 + 2 * bits qR := by
    intro Δ
    dsimp only [decIdxBody, hsKeysT, isCompromisedE, isCompromisedBody, hsCorrAt, aeadDecE, callE]
    cases specialDec with
    | none =>
      unfold_vars
      dsimp only [Comp.size, Expr.size, Ops.sum, Sum.elim, CryptoGames.OTCCA.Costed.otccaOps]
      simp only [hb0, hb1]; omega
    | some sD =>
      have hs := hDec (Δ := .prod (.prod (.opt (CryptoGames.FSAEAD.Costed.bt .msg))
        (.prod .nat (.prod (CryptoGames.FSAEAD.Costed.bt .ad)
          (CryptoGames.FSAEAD.Costed.bt .ct)))) hsTy :: Δ)
        (.pair (.pair (.fst (.snd (.fst .v0))) (.fst (.snd (.snd (.fst .v0)))))
          (.snd (.snd (.snd (.fst .v0)))))
      dsimp only [Expr.v0, Expr.size] at hs
      unfold_vars
      dsimp only [Comp.size, Expr.size]
      simp only [hb0, hb1]
      generalize hsdx : (sD _).size = sdx at hs ⊢
      dsimp only [Ops.sum, Sum.elim, CryptoGames.OTCCA.Costed.otccaOps]; omega
  dsimp only [receiveBody, skippedContainsE, skippedRemoveE, skippedRemoveBody, withSkippedE,
    isCompromisedE, isCompromisedBody, prependNewSkippedBody,
    orE, hsLastSent, hsCorrAt, hsRecvIdx, hsSkipped, callE, callC]
  generalize hgc :
    genUpToC (I₀ := I₀) (lAE C ℓ encT idOf) (lG C) 1 1 maxForwardJumps jPos _ _ = gc
  have hg' : gc.size ≤ 820 + 2 * bits qR := by
    rw [← hgc]
    refine (genUpToC_size_le (I₀ := I₀) C ℓ encT idOf hj _ _).trans ?_
    unfold_vars; dsimp only [Expr.v0, Expr.size]; omega
  unfold_vars; dsimp only [Expr.v0, Comp.size, Expr.size]
  generalize hd1x :
    (decIdxBody (I := I₀.withSamp (HSamp' Pt ℓ)) (lAE C ℓ encT idOf) (lG C) 1 1 mSlot specialDec
      (Γ := stTy :: _)).size = d1x
  have hd1 : d1x ≤ 300 + 2 * bits qR := by rw [← hd1x]; exact hdecB
  generalize hd2x :
    (decIdxBody (I := I₀.withSamp (HSamp' Pt ℓ)) (lAE C ℓ encT idOf) (lG C) 1 1 mSlot specialDec
      (Γ := _)).size = d2x
  have hd2 : d2x ≤ 300 + 2 * bits qR := by rw [← hd2x]; exact hdecB
  simp only [hmfj, hb1, Nat.reduceAdd]; omega

private lemma hybHandlePreC_size_le {ι : Type} {T : OracleSpec ι}
    {I₀ : Iface (HSig' Pt ℓ) T}
    {jPos mSlot qR : ℕ} (hj : jPos ≤ qR + 25002) (hm : mSlot ≤ qR + 25002) (la : Bool)
    (sampleIdeal : ∀ {Δ}, Expr _ Δ _ → Comp _ (I₀.withSamp (HSamp' Pt ℓ)) Δ _)
    (specialEnc : Option (∀ {Δ}, Expr _ Δ _ → Comp _ (I₀.withSamp (HSamp' Pt ℓ)) Δ _))
    (specialDec : Option (∀ {Δ}, Expr _ Δ _ → Comp _ (I₀.withSamp (HSamp' Pt ℓ)) Δ _))
    (hId : ∀ {Δ} (ia : Expr _ Δ _), (sampleIdeal ia).size ≤ ia.size + 20)
    (hEnc : match specialEnc with
      | none => True
      | some f => ∀ {Δ} (x : Expr _ Δ _), (f x).size ≤ x.size + 40)
    (hDec : match specialDec with
      | none => True
      | some f => ∀ {Δ} (x : Expr _ Δ _), (f x).size ≤ x.size + 20) :
    (hybHandlePreC (I₀ := I₀) (lAE C ℓ encT idOf) (lG C) 1 1 maxForwardJumps qR jPos mSlot la
      sampleIdeal specialEnc specialDec).size ≤
      14000 + 60 * bits qR := by
  have hmfj : maxForwardJumps = 25000 := rfl
  have hb0 : bits 0 = 1 := rfl
  have hb1 : bits 1 = 1 := rfl
  have hb2 : bits 2 = 2 := rfl
  have hbM := bits_le_bits_add_16 hm
  have hbS := bits_25000_le
  have hencB : ∀ {Δ},
      (encIdxBody (I := I₀.withSamp (HSamp' Pt ℓ))
        (lAE C ℓ encT idOf) (lG C) 1 1 mSlot sampleIdeal specialEnc (Γ := Δ)).size ≤
      300 + 2 * bits qR := by
    intro Δ
    let Δ0 : List (Ty (HSig' Pt ℓ)) :=
      .prod (.prod .nat (.prod (CryptoGames.FSAEAD.Costed.bt .ad)
        (CryptoGames.FSAEAD.Costed.bt .msg))) hsTy :: Δ
    have hi1 := hId (Δ := Δ0) (.pair (.fst (.fst .v0)) (.fst (.snd (.fst .v0))))
    dsimp only [Δ0, encIdxBody, hsKeysT, isCompromisedE, isCompromisedBody, hsCorrAt,
      aeadEncE, callE, Expr.v0, Expr.size] at hi1 ⊢
    cases specialEnc with
    | none =>
      unfold_vars
      dsimp only [Comp.size, Expr.size]
      generalize hidx : (sampleIdeal _).size = idx at hi1 ⊢
      dsimp only [Ops.sum, Sum.elim, CryptoGames.OTCCA.Costed.otccaOps]
      simp only [hb0, hb1]; omega
    | some sE =>
      have hs := hEnc (Δ := Δ0) (.pair (.pair (.fst (.fst .v0)) (.fst (.snd (.fst .v0))))
        (.snd (.snd (.fst .v0))))
      dsimp only [Δ0, Expr.v0, Expr.size] at hs
      unfold_vars
      dsimp only [Comp.size, Expr.size]
      generalize hidx : (sampleIdeal _).size = idx at hi1 ⊢
      generalize hsex : (sE _).size = sex at hs ⊢
      dsimp only [Ops.sum, Sum.elim, CryptoGames.OTCCA.Costed.otccaOps]
      simp only [hb0, hb1]; omega
  have hrcv : ∀ {Δ}, _ ≤ 2500 + 10 * bits qR :=
    fun {Δ} => receiveBody_size_le (I₀ := I₀) C ℓ encT idOf hj hm la specialDec hDec (Γ := Δ)
  have hsk : ∀ {Δ}, _ ≤ 250 + 2 * bits qR :=
    fun {Δ} => senderKeyBody_size_le (I₀ := I₀) C ℓ encT idOf qR (Γ := Δ)
  have htr : ∀ {Δ},
      (transmitBody (I₀ := I₀) (lAE C ℓ encT idOf) (lG C) 1 1 maxForwardJumps jPos mSlot
        sampleIdeal specialEnc (Γ := Δ)).size ≤ 1600 + 5 * bits qR := by
    intro Δ; dsimp only [transmitBody, mkHS, hsB, hsLastSent, hsCorrAt, hsRecvIdx, hsEnded, hsWin,
      hsLf, hsInTransit, hsChalls, hsNKeys, hsKeysT, hsCorrKey, hsSkipped, callC]
    generalize hgc : genUpToC (I₀ := I₀) (lAE C ℓ encT idOf) (lG C) 1 1 maxForwardJumps jPos _ _ = gc
    have hg' : gc.size ≤ 820 + 2 * bits qR := by
      rw [← hgc]; refine (genUpToC_size_le (I₀ := I₀) C ℓ encT idOf hj _ _).trans ?_
      unfold_vars; dsimp only [Expr.v0, hsLastSent, Expr.size]; simp only [hb1]; omega
    unfold_vars; dsimp only [Expr.v0, hsLastSent, Comp.size, Expr.size]
    generalize hex :
      (encIdxBody (I := I₀.withSamp (HSamp' Pt ℓ)) (lAE C ℓ encT idOf) (lG C) 1 1 mSlot sampleIdeal
        specialEnc (Γ := _)).size = ex
    have he' : ex ≤ 300 + 2 * bits qR := by rw [← hex]; exact hencB
    simp only [hb1]; omega
  have hch : ∀ {Δ},
      (challengeBody (I₀ := I₀) (lAE C ℓ encT idOf) (lG C) 1 1 maxForwardJumps jPos mSlot
        sampleIdeal specialEnc (Γ := Δ)).size ≤ 1600 + 5 * bits qR := by
    intro Δ; dsimp only [challengeBody, isSomeE, orE, mkHS, hsB, hsLastSent, hsCorrAt, hsRecvIdx,
      hsEnded, hsWin, hsLf, hsInTransit, hsChalls, hsNKeys, hsKeysT, hsCorrKey, hsSkipped, callC]
    generalize hgc : genUpToC (I₀ := I₀) (lAE C ℓ encT idOf) (lG C) 1 1 maxForwardJumps jPos _ _ = gc
    have hg' : gc.size ≤ 820 + 2 * bits qR := by
      rw [← hgc]; refine (genUpToC_size_le (I₀ := I₀) C ℓ encT idOf hj _ _).trans ?_
      unfold_vars; dsimp only [Expr.v0, hsLastSent, Expr.size]; simp only [hb1]; omega
    unfold_vars
    dsimp only [Expr.v0, hsLastSent, Comp.size, Expr.size]
    generalize hex :
      (encIdxBody (I := I₀.withSamp (HSamp' Pt ℓ)) (lAE C ℓ encT idOf) (lG C) 1 1 mSlot sampleIdeal
        specialEnc (Γ := _)).size = ex
    have he' : ex ≤ 300 + 2 * bits qR := by rw [← hex]; exact hencB
    simp only [hb1]; omega
  have hcs : ∀ {Δ},
      (corruptSenderBody (I₀ := I₀) (lAE C ℓ encT idOf) (lG C) 1 1 qR la (Γ := Δ)).size ≤
      700 + 3 * bits qR := by
    intro Δ; dsimp only [corruptSenderBody, mkHS, hsB, hsLastSent, hsCorrAt, hsRecvIdx, hsEnded,
      hsWin, hsLf, hsInTransit, hsChalls, hsNKeys, hsKeysT, hsCorrKey, hsSkipped, callC]
    unfold_vars; dsimp only [Comp.size, Expr.size]
    generalize hsx :
      (senderKeyBody (I₀ := I₀) (lAE C ℓ encT idOf) (lG C) 1 1 qR (Γ := _)).size = sx
    have hs1 : sx ≤ 250 + 2 * bits qR := by rw [← hsx]; exact hsk
    omega
  have hdl : ∀ {Δ},
      (deliverBody (I₀ := I₀) (lAE C ℓ encT idOf) (lG C) 1 1 maxForwardJumps qR jPos mSlot la
        specialDec (Γ := Δ)).size ≤ 3800 + 16 * bits qR := by
    intro Δ; dsimp only [deliverBody, findInTransitE, findInTransitBody, recMatchesE, challsContainsE,
      challsContainsBody, removeFromTransitE, removeFromTransitBody, isCompromisedE,
      isCompromisedBody, eqAdE, eqME, eqCE, orE, maxNatE, mkHS, hsB, hsLastSent, hsCorrAt,
      hsRecvIdx, hsEnded, hsWin, hsLf, hsInTransit, hsChalls, hsNKeys, hsKeysT, hsCorrKey,
      hsSkipped, recIdx, recAd, recMsg, recCt, callE, callC]
    unfold_vars
    dsimp only [Comp.size, Expr.size]
    generalize hrx :
      (receiveBody (I₀ := I₀) (lAE C ℓ encT idOf) (lG C) _ _ _ _ _ _ _).size = rx
    have hr1 : rx ≤ 2500 + 10 * bits qR := by rw [← hrx]; exact hrcv
    dsimp only [Ops.sum, Sum.elim, CryptoGames.OTCCA.Costed.otccaOps]
    simp only [hmfj, hb1, hb2, Nat.reduceAdd]; omega
  have hij : ∀ {Δ},
      (injectBody (I₀ := I₀) (lAE C ℓ encT idOf) (lG C) 1 1 maxForwardJumps qR jPos mSlot la
        specialDec (Γ := Δ)).size ≤ 3800 + 16 * bits qR := by
    intro Δ; dsimp only [injectBody, anyInTransitE, anyInTransitBody, recMatchesE, removeFromTransitE,
      removeFromTransitBody, isCompromisedE, isCompromisedBody, eqAdE, eqCE, orE, maxNatE,
      mkHS, hsB, hsLastSent, hsCorrAt, hsRecvIdx, hsEnded, hsWin, hsLf, hsInTransit, hsChalls,
      hsNKeys, hsKeysT, hsCorrKey, hsSkipped, recIdx, recAd, recCt, callE, callC]
    unfold_vars
    dsimp only [Comp.size, Expr.size]
    generalize hrx :
      (receiveBody (I₀ := I₀) (lAE C ℓ encT idOf) (lG C) _ _ _ _ _ _ _).size = rx
    have hr1 : rx ≤ 2500 + 10 * bits qR := by rw [← hrx]; exact hrcv
    dsimp only [Ops.sum, Sum.elim, CryptoGames.OTCCA.Costed.otccaOps]
    simp only [hb1, Nat.reduceAdd]; omega
  dsimp only [hybHandlePreC, orE, anyUncompInTransitE, anyUncompInTransitBody, isCompromisedE,
    isCompromisedBody, hsEnded, hsChalls, hsInTransit, hsCorrAt, recIdx, callE, callC]
  unfold_vars; dsimp only [Comp.size, Expr.size]
  generalize hx1 : (transmitBody (I₀ := I₀) (lAE C ℓ encT idOf) (lG C) _ _ _ _ _ _ _).size = x1
  generalize hx2 : (challengeBody (I₀ := I₀) (lAE C ℓ encT idOf) (lG C) _ _ _ _ _ _ _).size = x2
  generalize hx3 : (corruptSenderBody (I₀ := I₀) (lAE C ℓ encT idOf) (lG C) _ _ _ _).size = x3
  generalize hx5 : (deliverBody (I₀ := I₀) (lAE C ℓ encT idOf) (lG C) _ _ _ _ _ _ _ _).size = x5
  generalize hx6 : (injectBody (I₀ := I₀) (lAE C ℓ encT idOf) (lG C) _ _ _ _ _ _ _ _).size = x6
  have h1 : x1 ≤ 1600 + 5 * bits qR := by rw [← hx1]; exact htr
  have h2 : x2 ≤ 1600 + 5 * bits qR := by rw [← hx2]; exact hch
  have h3 : x3 ≤ 700 + 3 * bits qR := by rw [← hx3]; exact hcs
  have h5 : x5 ≤ 3800 + 16 * bits qR := by rw [← hx5]; exact hdl
  have h6 : x6 ≤ 3800 + 16 * bits qR := by rw [← hx6]; exact hij
  simp only [hb0]; omega

private lemma hybResumeC_size_le {ι : Type} {T : OracleSpec ι}
    {I₀ : Iface (HSig' Pt ℓ) T}
    (qR : ℕ) (la : Bool) :
    (hybResumeC (I₀ := I₀) (lAE C ℓ encT idOf) (lG C) 1 1 maxForwardJumps qR la).size ≤
      1500 + 10 * bits qR := by
  have hmfj : maxForwardJumps = 25000 := rfl
  have hb0 : bits 0 = 1 := rfl
  have hb1 : bits 1 = 1 := rfl
  have hbMul : bits (25001 * qR) ≤ bits qR + 16 := by
    have := Computational.Proofs.ReductionDsl.SizeBudgetBridge.bits_mul_le 25001 qR
    have := bits_25001_le; omega
  have hsk : ∀ {Δ}, _ ≤ 250 + 2 * bits qR :=
    fun {Δ} => senderKeyBody_size_le (I₀ := I₀) C ℓ encT idOf qR (Γ := Δ)
  dsimp only [hybResumeC, corruptReceiverResumeBody, corruptReceiverDBody,
    mkHS, hsB, hsLastSent, hsCorrAt, hsRecvIdx, hsEnded, hsWin, hsLf,
    hsInTransit, hsChalls, hsNKeys, hsKeysT, hsCorrKey, hsSkipped, callC]
  generalize hcc : chainFromC (I := I₀.withSamp (HSamp' Pt ℓ))
    (lAE C ℓ encT idOf) (lG C) 1 1 ((maxForwardJumps + 1) * qR) _ _ _ = cc
  have hc1' : cc.size ≤ 170 + 2 * bits qR := by
    rw [← hcc]
    refine (chainFromC_size_le (I₀ := I₀) C ℓ encT idOf
      ((maxForwardJumps + 1) * qR) _ _ _).trans ?_
    unfold_vars; dsimp only [hsRecvIdx, Expr.size]; simp only [hmfj, Nat.reduceAdd]; omega
  unfold_vars; dsimp only [hsRecvIdx, Comp.size, Expr.size]
  generalize hsx :
    (senderKeyBody (I₀ := I₀) (lAE C ℓ encT idOf) (lG C) 1 1 qR (Γ := _)).size = sx
  have hs1 : sx ≤ 250 + 2 * bits qR := by rw [← hsx]; exact hsk
  simp only [hmfj, hb0, hb1, Nat.reduceAdd]; omega

private lemma receiveBody_nodes_le {ι : Type} {T : OracleSpec ι}
    {I₀ : Iface (HSig' Pt ℓ) T} {Γ}
    (jPos mSlot : ℕ) (la : Bool)
    (specialDec : Option (∀ {Δ}, Expr _ Δ _ → Comp _ (I₀.withSamp (HSamp' Pt ℓ)) Δ _))
    (hDec : match specialDec with
      | none => True
      | some f => ∀ {Δ} (x : Expr _ Δ _), (f x).nodes ≤ x.nodes + 20) :
    (receiveBody (I₀ := I₀) (lAE C ℓ encT idOf) (lG C) 1 1 maxForwardJumps jPos mSlot la
      specialDec (Γ := Γ)).nodes ≤ 2500 := by
  have hdecB : ∀ {Δ},
      (decIdxBody (I := I₀.withSamp (HSamp' Pt ℓ))
        (lAE C ℓ encT idOf) (lG C) 1 1 mSlot specialDec (Γ := Δ)).nodes ≤ 300 := by
    intro Δ
    dsimp only [decIdxBody, hsKeysT, isCompromisedE, isCompromisedBody, hsCorrAt, aeadDecE, callE]
    cases specialDec with
    | none => unfold_vars; dsimp only [Comp.nodes, Expr.nodes]; omega
    | some sD =>
      have hs := hDec (Δ := .prod (.prod (.opt (CryptoGames.FSAEAD.Costed.bt .msg))
        (.prod .nat (.prod (CryptoGames.FSAEAD.Costed.bt .ad)
          (CryptoGames.FSAEAD.Costed.bt .ct)))) hsTy :: Δ)
        (.pair (.pair (.fst (.snd (.fst .v0))) (.fst (.snd (.snd (.fst .v0)))))
          (.snd (.snd (.snd (.fst .v0)))))
      dsimp only [Expr.v0, Expr.nodes] at hs
      unfold_vars; dsimp only [Comp.nodes, Expr.nodes]
      generalize hsdx : (sD _).nodes = sdx at hs ⊢; omega
  dsimp only [receiveBody, skippedContainsE, skippedRemoveE, skippedRemoveBody, withSkippedE,
    isCompromisedE, isCompromisedBody, prependNewSkippedBody,
    orE, hsLastSent, hsCorrAt, hsRecvIdx, hsSkipped, callE, callC]
  generalize hgc :
    genUpToC (I₀ := I₀) (lAE C ℓ encT idOf) (lG C) 1 1 maxForwardJumps jPos _ _ = gc
  have hg' : gc.nodes ≤ 820 := by
    rw [← hgc]
    refine (genUpToC_nodes_le (I₀ := I₀) C ℓ encT idOf jPos _ _).trans ?_
    unfold_vars; dsimp only [Expr.v0, Expr.nodes]; omega
  unfold_vars; dsimp only [Expr.v0, Comp.nodes, Expr.nodes]
  generalize hd1x :
    (decIdxBody (I := I₀.withSamp (HSamp' Pt ℓ)) (lAE C ℓ encT idOf) (lG C) 1 1 mSlot specialDec
      (Γ := stTy :: _)).nodes = d1x
  have hd1 : d1x ≤ 300 := by rw [← hd1x]; exact hdecB
  generalize hd2x :
    (decIdxBody (I := I₀.withSamp (HSamp' Pt ℓ)) (lAE C ℓ encT idOf) (lG C) 1 1 mSlot specialDec
      (Γ := _)).nodes = d2x
  have hd2 : d2x ≤ 300 := by rw [← hd2x]; exact hdecB
  omega

private lemma hybHandlePreC_nodes_le {ι : Type} {T : OracleSpec ι}
    {I₀ : Iface (HSig' Pt ℓ) T}
    (jPos mSlot qR : ℕ) (la : Bool)
    (sampleIdeal : ∀ {Δ}, Expr _ Δ _ → Comp _ (I₀.withSamp (HSamp' Pt ℓ)) Δ _)
    (specialEnc : Option (∀ {Δ}, Expr _ Δ _ → Comp _ (I₀.withSamp (HSamp' Pt ℓ)) Δ _))
    (specialDec : Option (∀ {Δ}, Expr _ Δ _ → Comp _ (I₀.withSamp (HSamp' Pt ℓ)) Δ _))
    (hId : ∀ {Δ} (ia : Expr _ Δ _), (sampleIdeal ia).nodes ≤ ia.nodes + 20)
    (hEnc : match specialEnc with
      | none => True
      | some f => ∀ {Δ} (x : Expr _ Δ _), (f x).nodes ≤ x.nodes + 40)
    (hDec : match specialDec with
      | none => True
      | some f => ∀ {Δ} (x : Expr _ Δ _), (f x).nodes ≤ x.nodes + 20) :
    (hybHandlePreC (I₀ := I₀) (lAE C ℓ encT idOf) (lG C) 1 1 maxForwardJumps qR jPos mSlot la
      sampleIdeal specialEnc specialDec).nodes ≤ 14000 := by
  have hencB : ∀ {Δ},
      (encIdxBody (I := I₀.withSamp (HSamp' Pt ℓ))
        (lAE C ℓ encT idOf) (lG C) 1 1 mSlot sampleIdeal specialEnc (Γ := Δ)).nodes ≤ 300 := by
    intro Δ
    let Δ0 : List (Ty (HSig' Pt ℓ)) :=
      .prod (.prod .nat (.prod (CryptoGames.FSAEAD.Costed.bt .ad)
        (CryptoGames.FSAEAD.Costed.bt .msg))) hsTy :: Δ
    have hi1 := hId (Δ := Δ0) (.pair (.fst (.fst .v0)) (.fst (.snd (.fst .v0))))
    dsimp only [Δ0, encIdxBody, hsKeysT, isCompromisedE, isCompromisedBody, hsCorrAt,
      aeadEncE, callE, Expr.v0, Expr.nodes] at hi1 ⊢
    cases specialEnc with
    | none =>
      unfold_vars; dsimp only [Comp.nodes, Expr.nodes]
      generalize hidx : (sampleIdeal _).nodes = idx at hi1 ⊢; omega
    | some sE =>
      have hs := hEnc (Δ := Δ0) (.pair (.pair (.fst (.fst .v0)) (.fst (.snd (.fst .v0))))
        (.snd (.snd (.fst .v0))))
      dsimp only [Δ0, Expr.v0, Expr.nodes] at hs
      unfold_vars; dsimp only [Comp.nodes, Expr.nodes]
      generalize hidx : (sampleIdeal _).nodes = idx at hi1 ⊢
      generalize hsex : (sE _).nodes = sex at hs ⊢; omega
  have hrcv : ∀ {Δ}, _ ≤ 2500 :=
    fun {Δ} => receiveBody_nodes_le (I₀ := I₀) C ℓ encT idOf jPos mSlot la specialDec hDec (Γ := Δ)
  have hsk : ∀ {Δ}, _ ≤ 250 :=
    fun {Δ} => senderKeyBody_nodes_le (I₀ := I₀) C ℓ encT idOf qR (Γ := Δ)
  have htr : ∀ {Δ},
      (transmitBody (I₀ := I₀) (lAE C ℓ encT idOf) (lG C) 1 1 maxForwardJumps jPos mSlot
        sampleIdeal specialEnc (Γ := Δ)).nodes ≤ 1600 := by
    intro Δ; dsimp only [transmitBody, mkHS, hsB, hsLastSent, hsCorrAt, hsRecvIdx, hsEnded, hsWin,
      hsLf, hsInTransit, hsChalls, hsNKeys, hsKeysT, hsCorrKey, hsSkipped, callC]
    generalize hgc : genUpToC (I₀ := I₀) (lAE C ℓ encT idOf) (lG C) 1 1 maxForwardJumps jPos _ _ = gc
    have hg' : gc.nodes ≤ 820 := by
      rw [← hgc]; refine (genUpToC_nodes_le (I₀ := I₀) C ℓ encT idOf jPos _ _).trans ?_
      unfold_vars; dsimp only [Expr.v0, hsLastSent, Expr.nodes]; omega
    unfold_vars; dsimp only [Expr.v0, hsLastSent, Comp.nodes, Expr.nodes]
    generalize hex :
      (encIdxBody (I := I₀.withSamp (HSamp' Pt ℓ)) (lAE C ℓ encT idOf) (lG C) 1 1 mSlot sampleIdeal
        specialEnc (Γ := _)).nodes = ex
    have he' : ex ≤ 300 := by rw [← hex]; exact hencB
    omega
  have hch : ∀ {Δ},
      (challengeBody (I₀ := I₀) (lAE C ℓ encT idOf) (lG C) 1 1 maxForwardJumps jPos mSlot
        sampleIdeal specialEnc (Γ := Δ)).nodes ≤ 1600 := by
    intro Δ; dsimp only [challengeBody, isSomeE, orE, mkHS, hsB, hsLastSent, hsCorrAt, hsRecvIdx,
      hsEnded, hsWin, hsLf, hsInTransit, hsChalls, hsNKeys, hsKeysT, hsCorrKey, hsSkipped, callC]
    generalize hgc : genUpToC (I₀ := I₀) (lAE C ℓ encT idOf) (lG C) 1 1 maxForwardJumps jPos _ _ = gc
    have hg' : gc.nodes ≤ 820 := by
      rw [← hgc]; refine (genUpToC_nodes_le (I₀ := I₀) C ℓ encT idOf jPos _ _).trans ?_
      unfold_vars; dsimp only [Expr.v0, hsLastSent, Expr.nodes]; omega
    unfold_vars; dsimp only [Expr.v0, hsLastSent, Comp.nodes, Expr.nodes]
    generalize hex :
      (encIdxBody (I := I₀.withSamp (HSamp' Pt ℓ)) (lAE C ℓ encT idOf) (lG C) 1 1 mSlot sampleIdeal
        specialEnc (Γ := _)).nodes = ex
    have he' : ex ≤ 300 := by rw [← hex]; exact hencB
    omega
  have hcs : ∀ {Δ},
      (corruptSenderBody (I₀ := I₀) (lAE C ℓ encT idOf) (lG C) 1 1 qR la (Γ := Δ)).nodes ≤
      700 := by
    intro Δ; dsimp only [corruptSenderBody, mkHS, hsB, hsLastSent, hsCorrAt, hsRecvIdx, hsEnded,
      hsWin, hsLf, hsInTransit, hsChalls, hsNKeys, hsKeysT, hsCorrKey, hsSkipped, callC]
    unfold_vars; dsimp only [Comp.nodes, Expr.nodes]
    generalize hsx :
      (senderKeyBody (I₀ := I₀) (lAE C ℓ encT idOf) (lG C) 1 1 qR (Γ := _)).nodes = sx
    have hs1 : sx ≤ 250 := by rw [← hsx]; exact hsk
    omega
  have hdl : ∀ {Δ},
      (deliverBody (I₀ := I₀) (lAE C ℓ encT idOf) (lG C) 1 1 maxForwardJumps qR jPos mSlot la
        specialDec (Γ := Δ)).nodes ≤ 3800 := by
    intro Δ; dsimp only [deliverBody, findInTransitE, findInTransitBody, recMatchesE, challsContainsE,
      challsContainsBody, removeFromTransitE, removeFromTransitBody, isCompromisedE,
      isCompromisedBody, eqAdE, eqME, eqCE, orE, maxNatE, mkHS, hsB, hsLastSent, hsCorrAt,
      hsRecvIdx, hsEnded, hsWin, hsLf, hsInTransit, hsChalls, hsNKeys, hsKeysT, hsCorrKey,
      hsSkipped, recIdx, recAd, recMsg, recCt, callE, callC]
    unfold_vars; dsimp only [Comp.nodes, Expr.nodes]
    generalize hrx :
      (receiveBody (I₀ := I₀) (lAE C ℓ encT idOf) (lG C) _ _ _ _ _ _ _).nodes = rx
    have hr1 : rx ≤ 2500 := by rw [← hrx]; exact hrcv
    omega
  have hij : ∀ {Δ},
      (injectBody (I₀ := I₀) (lAE C ℓ encT idOf) (lG C) 1 1 maxForwardJumps qR jPos mSlot la
        specialDec (Γ := Δ)).nodes ≤ 3800 := by
    intro Δ; dsimp only [injectBody, anyInTransitE, anyInTransitBody, recMatchesE, removeFromTransitE,
      removeFromTransitBody, isCompromisedE, isCompromisedBody, eqAdE, eqCE, orE, maxNatE,
      mkHS, hsB, hsLastSent, hsCorrAt, hsRecvIdx, hsEnded, hsWin, hsLf, hsInTransit, hsChalls,
      hsNKeys, hsKeysT, hsCorrKey, hsSkipped, recIdx, recAd, recCt, callE, callC]
    unfold_vars; dsimp only [Comp.nodes, Expr.nodes]
    generalize hrx :
      (receiveBody (I₀ := I₀) (lAE C ℓ encT idOf) (lG C) _ _ _ _ _ _ _).nodes = rx
    have hr1 : rx ≤ 2500 := by rw [← hrx]; exact hrcv
    omega
  dsimp only [hybHandlePreC, orE, anyUncompInTransitE, anyUncompInTransitBody, isCompromisedE,
    isCompromisedBody, hsEnded, hsChalls, hsInTransit, hsCorrAt, recIdx, callE, callC]
  unfold_vars; dsimp only [Comp.nodes, Expr.nodes]
  generalize hx1 : (transmitBody (I₀ := I₀) (lAE C ℓ encT idOf) (lG C) _ _ _ _ _ _ _).nodes = x1
  generalize hx2 : (challengeBody (I₀ := I₀) (lAE C ℓ encT idOf) (lG C) _ _ _ _ _ _ _).nodes = x2
  generalize hx3 : (corruptSenderBody (I₀ := I₀) (lAE C ℓ encT idOf) (lG C) _ _ _ _).nodes = x3
  generalize hx5 : (deliverBody (I₀ := I₀) (lAE C ℓ encT idOf) (lG C) _ _ _ _ _ _ _ _).nodes = x5
  generalize hx6 : (injectBody (I₀ := I₀) (lAE C ℓ encT idOf) (lG C) _ _ _ _ _ _ _ _).nodes = x6
  have h1 : x1 ≤ 1600 := by rw [← hx1]; exact htr
  have h2 : x2 ≤ 1600 := by rw [← hx2]; exact hch
  have h3 : x3 ≤ 700 := by rw [← hx3]; exact hcs
  have h5 : x5 ≤ 3800 := by rw [← hx5]; exact hdl
  have h6 : x6 ≤ 3800 := by rw [← hx6]; exact hij
  omega

private lemma hybResumeC_nodes_le {ι : Type} {T : OracleSpec ι}
    {I₀ : Iface (HSig' Pt ℓ) T}
    (qR : ℕ) (la : Bool) :
    (hybResumeC (I₀ := I₀) (lAE C ℓ encT idOf) (lG C) 1 1 maxForwardJumps qR la).nodes ≤ 1500 := by
  have hsk : ∀ {Δ}, _ ≤ 250 :=
    fun {Δ} => senderKeyBody_nodes_le (I₀ := I₀) C ℓ encT idOf qR (Γ := Δ)
  dsimp only [hybResumeC, corruptReceiverResumeBody, corruptReceiverDBody,
    mkHS, hsB, hsLastSent, hsCorrAt, hsRecvIdx, hsEnded, hsWin, hsLf,
    hsInTransit, hsChalls, hsNKeys, hsKeysT, hsCorrKey, hsSkipped, callC]
  generalize hcc : chainFromC (I := I₀.withSamp (HSamp' Pt ℓ))
    (lAE C ℓ encT idOf) (lG C) 1 1 ((maxForwardJumps + 1) * qR) _ _ _ = cc
  have hc1' : cc.nodes ≤ 150 := by
    rw [← hcc]
    refine (chainFromC_nodes_le (I₀ := I₀) C ℓ encT idOf
      ((maxForwardJumps + 1) * qR) _ _ _).trans ?_
    unfold_vars; dsimp only [hsRecvIdx, Expr.nodes]; omega
  unfold_vars; dsimp only [hsRecvIdx, Comp.nodes, Expr.nodes]
  generalize hsx :
    (senderKeyBody (I₀ := I₀) (lAE C ℓ encT idOf) (lG C) 1 1 qR (Γ := _)).nodes = sx
  have hs1 : sx ≤ 250 := by rw [← hsx]; exact hsk
  omega

private lemma genUpToC_queries {ι : Type} {T : OracleSpec ι}
    {I₀ : Iface (HSig' Pt ℓ) T} {Γ} (w : (I₀.withSamp (HSamp' Pt ℓ)).Tag → ℕ) (jPos : ℕ)
    (i : Expr _ Γ .nat) (s : Expr _ Γ stTy) :
    (genUpToC (I₀ := I₀) (lAE C ℓ encT idOf) (lG C) 1 1 maxForwardJumps jPos i s).queries
      w (fun _ => 0) = 0 := by
  have hstep : ∀ {Δ},
      (genStepKcBody (I₀ := I₀) (Γ := Δ) (lAE C ℓ encT idOf) (lG C) 1 1).queries
        w (fun _ => 0) = 0 := by
    intro Δ; dsimp only [genStepKcBody, Comp.queries]; omega
  dsimp only [genUpToC, genUpToBody, callC, Comp.queries]
  generalize hbs : (genStepKcBody (I₀ := I₀) (lAE C ℓ encT idOf) (lG C) 1 1 (Γ := _)).queries
    w (fun _ => 0) = bs
  have hstep' : bs = 0 := by rw [← hbs]; exact hstep
  rw [hstep']; rfl

private lemma chainFromC_queries {ι : Type} {T : OracleSpec ι}
    {I₀ : Iface (HSig' Pt ℓ) T} {Γ} (w : (I₀.withSamp (HSamp' Pt ℓ)).Tag → ℕ)
    (fuel : ℕ) (c : Expr _ Γ .nat) (wk : Expr _ Γ _) (m : Expr _ Γ .nat) :
    (chainFromC (I := I₀.withSamp (HSamp' Pt ℓ))
      (lAE C ℓ encT idOf) (lG C) 1 1 fuel c wk m).queries w (fun _ => 0) = 0 := by
  dsimp only [chainFromC, chainFromBody, callC, Comp.queries]
  rfl

private lemma senderKeyBody_queries {ι : Type} {T : OracleSpec ι}
    {I₀ : Iface (HSig' Pt ℓ) T} {Γ} (w : (I₀.withSamp (HSamp' Pt ℓ)).Tag → ℕ) (qR : ℕ) :
    (senderKeyBody (I₀ := I₀) (lAE C ℓ encT idOf) (lG C) 1 1 qR (Γ := Γ)).queries
      w (fun _ => 0) = 0 := by
  dsimp only [senderKeyBody, revealBody, chainFromC, chainFromBody, callC, Comp.queries]
  rfl

private lemma receiveBody_queries_le {ι : Type} {T : OracleSpec ι}
    {I₀ : Iface (HSig' Pt ℓ) T} {Γ} (w : (I₀.withSamp (HSamp' Pt ℓ)).Tag → ℕ)
    (jPos mSlot : ℕ) (la : Bool)
    (specialDec : Option (∀ {Δ}, Expr _ Δ _ → Comp _ (I₀.withSamp (HSamp' Pt ℓ)) Δ _))
    (hDec : match specialDec with
      | none => True
      | some f => ∀ {Δ} (x : Expr _ Δ _), (f x).queries w (fun _ => 0) ≤ 1) :
    (receiveBody (I₀ := I₀) (lAE C ℓ encT idOf) (lG C) 1 1 maxForwardJumps jPos mSlot la
      specialDec (Γ := Γ)).queries w (fun _ => 0) ≤ 1 := by
  have hdecB : ∀ {Δ},
      (decIdxBody (I := I₀.withSamp (HSamp' Pt ℓ))
        (lAE C ℓ encT idOf) (lG C) 1 1 mSlot specialDec (Γ := Δ)).queries w (fun _ => 0) ≤ 1 := by
    intro Δ; dsimp only [decIdxBody]
    cases specialDec with
    | none => dsimp only [Comp.queries]; omega
    | some sD =>
      have hs := hDec (Δ := .prod (.prod (.opt (CryptoGames.FSAEAD.Costed.bt .msg))
        (.prod .nat (.prod (CryptoGames.FSAEAD.Costed.bt .ad)
          (CryptoGames.FSAEAD.Costed.bt .ct)))) hsTy :: Δ)
        (.pair (.pair (.fst (.snd (.fst .v0))) (.fst (.snd (.snd (.fst .v0)))))
          (.snd (.snd (.snd (.fst .v0)))))
      dsimp only [Comp.queries]
      generalize hsdx : (sD _).queries w (fun _ => 0) = sdx at hs ⊢; omega
  dsimp only [receiveBody, prependNewSkippedBody, callC, Comp.queries]
  generalize hgc : (genUpToC (I₀ := I₀) (lAE C ℓ encT idOf) (lG C) 1 1 maxForwardJumps jPos _ _).queries
    w (fun _ => 0) = gc
  have hg' : gc = 0 := by rw [← hgc]; exact genUpToC_queries C ℓ encT idOf w jPos _ _
  generalize hd1x :
    (decIdxBody (I := I₀.withSamp (HSamp' Pt ℓ)) (lAE C ℓ encT idOf) (lG C) 1 1 mSlot specialDec
      (Γ := stTy :: _)).queries w (fun _ => 0) = d1x
  have hd1 : d1x ≤ 1 := by rw [← hd1x]; exact hdecB
  generalize hd2x :
    (decIdxBody (I := I₀.withSamp (HSamp' Pt ℓ)) (lAE C ℓ encT idOf) (lG C) 1 1 mSlot specialDec
      (Γ := _)).queries w (fun _ => 0) = d2x
  have hd2 : d2x ≤ 1 := by rw [← hd2x]; exact hdecB
  simp only [Nat.mul_zero]; omega

private lemma hybHandlePreC_queries_le {ι : Type} {T : OracleSpec ι}
    {I₀ : Iface (HSig' Pt ℓ) T} (w : (I₀.withSamp (HSamp' Pt ℓ)).Tag → ℕ)
    (jPos mSlot qR : ℕ) (la : Bool)
    (sampleIdeal : ∀ {Δ}, Expr _ Δ _ → Comp _ (I₀.withSamp (HSamp' Pt ℓ)) Δ _)
    (specialEnc : Option (∀ {Δ}, Expr _ Δ _ → Comp _ (I₀.withSamp (HSamp' Pt ℓ)) Δ _))
    (specialDec : Option (∀ {Δ}, Expr _ Δ _ → Comp _ (I₀.withSamp (HSamp' Pt ℓ)) Δ _))
    (hId : ∀ {Δ} (ia : Expr _ Δ _), (sampleIdeal ia).queries w (fun _ => 0) = 0)
    (hEnc : match specialEnc with
      | none => True
      | some f => ∀ {Δ} (x : Expr _ Δ _), (f x).queries w (fun _ => 0) ≤ 1)
    (hDec : match specialDec with
      | none => True
      | some f => ∀ {Δ} (x : Expr _ Δ _), (f x).queries w (fun _ => 0) ≤ 1) :
    (hybHandlePreC (I₀ := I₀) (lAE C ℓ encT idOf) (lG C) 1 1 maxForwardJumps qR jPos mSlot la
      sampleIdeal specialEnc specialDec).queries w (fun _ => 0) ≤ 1 := by
  have hencB : ∀ {Δ},
      (encIdxBody (I := I₀.withSamp (HSamp' Pt ℓ))
        (lAE C ℓ encT idOf) (lG C) 1 1 mSlot sampleIdeal specialEnc (Γ := Δ)).queries
        w (fun _ => 0) ≤ 1 := by
    intro Δ
    let Δ0 : List (Ty (HSig' Pt ℓ)) :=
      .prod (.prod .nat (.prod (CryptoGames.FSAEAD.Costed.bt .ad)
        (CryptoGames.FSAEAD.Costed.bt .msg))) hsTy :: Δ
    have hi1 := hId (Δ := Δ0) (.pair (.fst (.fst .v0)) (.fst (.snd (.fst .v0))))
    dsimp only [Δ0, encIdxBody] at hi1 ⊢
    cases specialEnc with
    | none =>
      dsimp only [Comp.queries]
      generalize hidx : (sampleIdeal _).queries w (fun _ => 0) = idx at hi1 ⊢; omega
    | some sE =>
      have hs := hEnc (Δ := Δ0) (.pair (.pair (.fst (.fst .v0)) (.fst (.snd (.fst .v0))))
        (.snd (.snd (.fst .v0))))
      dsimp only [Δ0, Comp.queries] at hs ⊢
      generalize hidx : (sampleIdeal _).queries w (fun _ => 0) = idx at hi1 ⊢
      generalize hsex : (sE _).queries w (fun _ => 0) = sex at hs ⊢; omega
  have hrcv : ∀ {Δ}, _ ≤ 1 :=
    fun {Δ} => receiveBody_queries_le (I₀ := I₀) C ℓ encT idOf w jPos mSlot la specialDec hDec (Γ := Δ)
  have hsk : ∀ {Δ}, _ = 0 :=
    fun {Δ} => senderKeyBody_queries (I₀ := I₀) C ℓ encT idOf w qR (Γ := Δ)
  have htr : ∀ {Δ},
      (transmitBody (I₀ := I₀) (lAE C ℓ encT idOf) (lG C) 1 1 maxForwardJumps jPos mSlot
        sampleIdeal specialEnc (Γ := Δ)).queries w (fun _ => 0) ≤ 1 := by
    intro Δ; dsimp only [transmitBody, callC, Comp.queries]
    generalize hgc : (genUpToC (I₀ := I₀) (lAE C ℓ encT idOf) (lG C) 1 1 maxForwardJumps jPos _ _).queries
      w (fun _ => 0) = gc
    have hg' : gc = 0 := by rw [← hgc]; exact genUpToC_queries C ℓ encT idOf w jPos _ _
    generalize hex :
      (encIdxBody (I := I₀.withSamp (HSamp' Pt ℓ)) (lAE C ℓ encT idOf) (lG C) 1 1 mSlot sampleIdeal
        specialEnc (Γ := _)).queries w (fun _ => 0) = ex
    have he' : ex ≤ 1 := by rw [← hex]; exact hencB
    omega
  have hch : ∀ {Δ},
      (challengeBody (I₀ := I₀) (lAE C ℓ encT idOf) (lG C) 1 1 maxForwardJumps jPos mSlot
        sampleIdeal specialEnc (Γ := Δ)).queries w (fun _ => 0) ≤ 1 := by
    intro Δ; dsimp only [challengeBody, callC, Comp.queries]
    generalize hgc : (genUpToC (I₀ := I₀) (lAE C ℓ encT idOf) (lG C) 1 1 maxForwardJumps jPos _ _).queries
      w (fun _ => 0) = gc
    have hg' : gc = 0 := by rw [← hgc]; exact genUpToC_queries C ℓ encT idOf w jPos _ _
    generalize hex :
      (encIdxBody (I := I₀.withSamp (HSamp' Pt ℓ)) (lAE C ℓ encT idOf) (lG C) 1 1 mSlot sampleIdeal
        specialEnc (Γ := _)).queries w (fun _ => 0) = ex
    have he' : ex ≤ 1 := by rw [← hex]; exact hencB
    omega
  have hcs : ∀ {Δ},
      (corruptSenderBody (I₀ := I₀) (lAE C ℓ encT idOf) (lG C) 1 1 qR la (Γ := Δ)).queries
        w (fun _ => 0) = 0 := by
    intro Δ; dsimp only [corruptSenderBody, callC, Comp.queries]
    generalize hsx :
      (senderKeyBody (I₀ := I₀) (lAE C ℓ encT idOf) (lG C) 1 1 qR (Γ := _)).queries
        w (fun _ => 0) = sx
    have hs1 : sx = 0 := by rw [← hsx]; exact hsk
    omega
  have hdl : ∀ {Δ},
      (deliverBody (I₀ := I₀) (lAE C ℓ encT idOf) (lG C) 1 1 maxForwardJumps qR jPos mSlot la
        specialDec (Γ := Δ)).queries w (fun _ => 0) ≤ 1 := by
    intro Δ; dsimp only [deliverBody, callC, Comp.queries]
    generalize hrx :
      (receiveBody (I₀ := I₀) (lAE C ℓ encT idOf) (lG C) _ _ _ _ _ _ _).queries
        w (fun _ => 0) = rx
    have hr1 : rx ≤ 1 := by rw [← hrx]; exact hrcv
    omega
  have hij : ∀ {Δ},
      (injectBody (I₀ := I₀) (lAE C ℓ encT idOf) (lG C) 1 1 maxForwardJumps qR jPos mSlot la
        specialDec (Γ := Δ)).queries w (fun _ => 0) ≤ 1 := by
    intro Δ; dsimp only [injectBody, callC, Comp.queries]
    generalize hrx :
      (receiveBody (I₀ := I₀) (lAE C ℓ encT idOf) (lG C) _ _ _ _ _ _ _).queries
        w (fun _ => 0) = rx
    have hr1 : rx ≤ 1 := by rw [← hrx]; exact hrcv
    omega
  dsimp only [hybHandlePreC, callC, Comp.queries]
  generalize hx1 : (transmitBody (I₀ := I₀) (lAE C ℓ encT idOf) (lG C) _ _ _ _ _ _ _).queries w (fun _ => 0) = x1
  generalize hx2 : (challengeBody (I₀ := I₀) (lAE C ℓ encT idOf) (lG C) _ _ _ _ _ _ _).queries w (fun _ => 0) = x2
  generalize hx3 : (corruptSenderBody (I₀ := I₀) (lAE C ℓ encT idOf) (lG C) _ _ _ _).queries w (fun _ => 0) = x3
  generalize hx5 : (deliverBody (I₀ := I₀) (lAE C ℓ encT idOf) (lG C) _ _ _ _ _ _ _ _).queries w (fun _ => 0) = x5
  generalize hx6 : (injectBody (I₀ := I₀) (lAE C ℓ encT idOf) (lG C) _ _ _ _ _ _ _ _).queries w (fun _ => 0) = x6
  have h1 : x1 ≤ 1 := by rw [← hx1]; exact htr
  have h2 : x2 ≤ 1 := by rw [← hx2]; exact hch
  have h3 : x3 = 0 := by rw [← hx3]; exact hcs
  have h5 : x5 ≤ 1 := by rw [← hx5]; exact hdl
  have h6 : x6 ≤ 1 := by rw [← hx6]; exact hij
  omega

private lemma hybResumeC_queries {ι : Type} {T : OracleSpec ι}
    {I₀ : Iface (HSig' Pt ℓ) T} (w : (I₀.withSamp (HSamp' Pt ℓ)).Tag → ℕ)
    (qR : ℕ) (la : Bool) :
    (hybResumeC (I₀ := I₀) (lAE C ℓ encT idOf) (lG C) 1 1 maxForwardJumps qR la).queries
      w (fun _ => 0) = 0 := by
  have hsk : ∀ {Δ}, _ = 0 :=
    fun {Δ} => senderKeyBody_queries (I₀ := I₀) C ℓ encT idOf w qR (Γ := Δ)
  dsimp only [hybResumeC, corruptReceiverResumeBody, corruptReceiverDBody, callC, Comp.queries]
  generalize hcc : (chainFromC (I := I₀.withSamp (HSamp' Pt ℓ))
    (lAE C ℓ encT idOf) (lG C) 1 1 ((maxForwardJumps + 1) * qR) _ _ _).queries w (fun _ => 0) = cc
  have hc1' : cc = 0 := by rw [← hcc]; exact chainFromC_queries C ℓ encT idOf w _ _ _ _
  generalize hsx :
    (senderKeyBody (I₀ := I₀) (lAE C ℓ encT idOf) (lG C) 1 1 qR (Γ := _)).queries w (fun _ => 0) = sx
  have hs1 : sx = 0 := by rw [← hsx]; exact hsk
  simp only [Nat.mul_zero]; omega

end HybProgBounds

section AllProgBounds

variable {Pt : Type} [DecidableEq Pt]
  (C : Crypto) (codec : SignalMessageProtoCodec) (ℓ : ℕ)
  (encT : Pt → PublicKey) (idOf : Party → IdentityKey)

omit [DecidableEq Pt] in
theorem fsPubRedAtomic_bounds (hℓ : ℓ < 10 ^ 6) (qR qep : ℕ) :
    GRedBounded (fsPubRedAtomic (Pt := Pt) C ℓ encT) (fun _ => 1) (fun _ => 0) qR qR
      (ratchetFsAdapterBudget qR qep) := by
  have hdiv : ℓ / 32 ≤ 31250 := by omega
  refine CryptoVerification.E2E.Costed.gRedBounded_of_bounds_const _ _ _ _ _ _ ?_ ?_ ?_
    (atomicFsOps_sizeHonest ℓ Pt C encT) (atomicBaseSamplers_sizeHonest ℓ Pt)
  · dsimp only [fsPubRedAtomic]
    refine (compilePureRed_totalCost_le_UB (fsaeadPubCodec ℓ Pt)
      (pubMacroBundle (Pt := Pt) C ℓ encT) _ rfl rfl pubOpC (fun s => nomatch s) (fun _ => 94000)
      (pubOpMacro_cost_le C ℓ encT hℓ) (fun s => nomatch s)
      (fun g => by
        cases g <;>
          (dsimp only [pubMacroBundle, CryptoGames.FSAEAD.Costed.fsaeadIface, mapTy, pubBaseTy]
           simp only [Comp.cost, Expr.cost]; omega))
      (cInit := 10) (cHandle := 1000000) (cFin := 10) ?_ ?_ ?_ qR).trans ?_
    · dsimp only [CryptoGames.FSAEAD.Costed.pubRedProg]
      dsimp only [compCostBound, exprCostBound]; omega
    · refine (compCostBound_le_UB _ _ _ _).trans ?_
      dsimp only [CryptoGames.FSAEAD.Costed.pubRedProg, CryptoGames.FSAEAD.Costed.pubHandle,
        CryptoGames.FSAEAD.Costed.withPubE]
      unfold_vars; dsimp only [compCostBoundUB, exprCostBoundUB, pubOpC]; omega
    · dsimp only [CryptoGames.FSAEAD.Costed.pubRedProg]
      unfold_vars; dsimp only [compCostBound, exprCostBound]; omega
    · have hcc : (fsaeadPubCodec ℓ Pt).codecCost ≤ 200000 := by
        dsimp [fsaeadPubCodec]; omega
      have hmax : max (fsaeadPubTargetIface ℓ Pt).uCost
          (1000000 + (fsaeadPubCodec ℓ Pt).codecCost) ≤ 1500000 := by
        dsimp [fsaeadPubTargetIface]; omega
      have hmul := Nat.mul_le_mul_left qR hmax
      have hbud := fs_poly_le_ratchetFsAdapterBudget qR qep
      nlinarith
  · dsimp only [fsPubRedAtomic]
    refine (compilePureRed_size_le (fsaeadPubCodec ℓ Pt)
      (pubMacroBundle (Pt := Pt) C ℓ encT) _ rfl rfl 250 (by omega)
      (pubOpMacro_size_le C ℓ encT) (fun s => nomatch s)
      (pubQueryMacro_size_le C ℓ encT)).trans ?_
    dsimp only [CostedReduction.size, CryptoGames.FSAEAD.Costed.pubRedProg,
      CryptoGames.FSAEAD.Costed.pubHandle, CryptoGames.FSAEAD.Costed.withPubE]
    unfold_vars
    dsimp only [Comp.size, Expr.size, CryptoGames.FSAEAD.Costed.fsOps, reductionSizeBudget_eq]
    omega
  · dsimp only [fsPubRedAtomic]
    refine (compilePureRed_totalQueries_le (fsaeadPubCodec ℓ Pt)
      (pubMacroBundle (Pt := Pt) C ℓ encT) _ rfl rfl (fun _ => 1) (fun s => nomatch s)
      (fun _ => 1) (fun _ => 0) (fun s => nomatch s)
      (fun g => by cases g <;> simp [pubMacroBundle, Comp.queries]) qR).trans ?_
    simp [CostedReduction.totalQueries, CryptoGames.FSAEAD.Costed.pubRedProg,
      CryptoGames.FSAEAD.Costed.pubHandle, Comp.queries]

private lemma fsPrgRedAtomic_bounds_of_finish (hℓ : ℓ < 10 ^ 6) (qR qep j : ℕ)
    (hj : j ≤ 2 * (qR + maxForwardJumps + 1))
    (fin : Comp (HybOps' C ℓ encT idOf) (PrgRedZeroIface' C ℓ encT)
      [CryptoGames.FSAEAD.Thm5.Costed.stTy, .bool, .unit] .bool)
    (hfCost : compCostBound hybOpCU prgSC Empty.elim fin ≤ 100)
    (hfSize : fin.size ≤ 100) (hfNodes : fin.nodes ≤ 50) :
    GTwoStageBounded
      (compilePureTwoStageRed (fsaeadRatchetCodec ℓ Pt)
        (prgZeroMacroBundle (Pt := Pt) C ℓ encT idOf)
        { CryptoGames.FSAEAD.Thm5.Costed.prgRedZeroProg
            (lAeadR C clampedProtoSignalCodec ℓ encT idOf) (lChainPRG C.F) 1 1
            (lIdeal C clampedProtoSignalCodec ℓ encT) 1 qR maxForwardJumps j with
          finish := fin }
        rfl rfl)
      Empty.elim (fun _ => 0) qR 0 (fsRatchetCostBudget qR qep) := by
  have hdiv : ℓ / 32 ≤ 31250 := by omega
  have hmfj : maxForwardJumps = 25000 := rfl
  have hj2 : j / 2 ≤ qR + 25002 := by omega
  have hbJ := bits_le_qR_add_15 hj2
  have hbitsJ := bits_le_bits_add_16 hj2
  have hb0 : bits 0 = 1 := rfl
  let I₀' := Iface.withSamp (CryptoGames.PRG.Costed.prgIface (HSig' Pt ℓ))
    (CryptoGames.OTCCA.Costed.idealSamplers (.prod .nat (.base .ad)) (.base .ct)
      (lIdeal C clampedProtoSignalCodec ℓ encT) 1)
  refine gTwoStageBounded_of_bounds _ _ _ _ _ _ ?_ ?_ ?_ (atomicFsOps_sizeHonest ℓ Pt C encT)
    (atomicBaseSamplers_sizeHonest ℓ Pt)
  · have hh := hybHandlePreC_cost_le (Pt := Pt) C ℓ encT idOf
      (I₀ := I₀') (sC := prgSC) (qC := Empty.elim)
      (by dsimp [prgSC]; omega) (by dsimp [prgSC]; omega) (mSlot := 0) hj2 (Nat.zero_le _)
      (CryptoGames.FSAEAD.Thm5.isLookaheadHop j)
      (fun {Δ} ia =>
        Comp.sample (O := HybOps' C ℓ encT idOf)
          (I := PrgRedZeroIface' C ℓ encT)
          (Sum.inl (Sum.inr ()) : (Empty ⊕ Unit) ⊕ UniformSamplerTag Bool) ia)
      none none
      (fun {Δ} ia => by
        change exprCostBoundUB hybOpCU ia + 2190000 ≤ exprCostBoundUB hybOpCU ia + 2500000
        omega)
      trivial trivial
    have hr := hybResumeC_cost_le (Pt := Pt) C ℓ encT idOf
      (I₀ := I₀') (sC := prgSC) (qC := Empty.elim)
      (by dsimp [prgSC]; omega) qR (CryptoGames.FSAEAD.Thm5.isLookaheadHop j)
    refine (compilePureTwoStageRed_totalCost_le_UB (fsaeadRatchetCodec ℓ Pt)
      (prgZeroMacroBundle (Pt := Pt) C ℓ encT idOf) _ rfl rfl hybOpCU prgSC Empty.elim
      (hybOpMacro_cost_le C ℓ encT idOf hℓ) (prgSampMacro_cost_le C ℓ encT idOf hℓ)
      (fun e => nomatch e)
      (cInit := 500 + qR) (cHandlePre := 60000000 + 2000 * qR) (cHandlePost := 20)
      (cChDone := 10) (cResume := 20000 + 12000000 * qR) (cFin := 100)
      ?_ ?_ ?_ ?_ ?_ ?_ qR).trans ?_
    · dsimp only [CryptoGames.FSAEAD.Thm5.Costed.prgRedZeroProg,
        CryptoGames.FSAEAD.Thm5.Costed.initHSE, CryptoGames.FSAEAD.Thm5.Costed.mkHS]
      unfold_vars
      dsimp only [compCostBound, exprCostBound, prgSC]
      simp only [hb0]; omega
    · exact hh
    · dsimp only [CryptoGames.FSAEAD.Thm5.Costed.prgRedZeroProg,
        CryptoGames.FSAEAD.Thm5.Costed.hybHandlePostC]
      unfold_vars; dsimp only [compCostBound, exprCostBound]; omega
    · dsimp only [CryptoGames.FSAEAD.Thm5.Costed.prgRedZeroProg,
        CryptoGames.FSAEAD.Thm5.Costed.hybChDoneC]
      dsimp only [compCostBound, exprCostBound]; omega
    · exact hr
    · exact hfCost
    · have hcc : (fsaeadRatchetCodec ℓ Pt).codecCost ≤ 200000 := by
        dsimp [fsaeadRatchetCodec]; omega
      have hmPre : max (60000000 + 2000 * qR) 20 = 60000000 + 2000 * qR := by omega
      have hmCh : max 10 (20000 + 12000000 * qR) = 20000 + 12000000 * qR := by omega
      rw [hmPre, hmCh]
      have hmax : max (coinOnlyBaseIface ℓ Pt).uCost
          (60000000 + 2000 * qR + (fsaeadRatchetCodec ℓ Pt).codecCost) ≤
          61000000 + 2000 * qR := by dsimp [coinOnlyBaseIface]; omega
      have hmul := Nat.mul_le_mul_left qR hmax
      have hbud := fs_poly_le_fsRatchetCostBudget qR qep
      nlinarith
  · refine (compilePureTwoStageRed_size_le_nodes (fsaeadRatchetCodec ℓ Pt)
      (prgZeroMacroBundle (Pt := Pt) C ℓ encT idOf) _ rfl rfl 650
      (fun o => by dsimp only [prgZeroMacroBundle]; have := hybOpMacro_size_le C ℓ encT idOf o; omega)
      (fun s => by have := prgSampMacro_size_le C ℓ encT idOf hℓ s; omega)
      (fun e => nomatch e)).trans ?_
    refine size_le_fs_budget_of_qR (C₀ := 15000000) (C₁ := 3000) (by omega) (by omega) ?_
    let p0 := CryptoGames.FSAEAD.Thm5.Costed.prgRedZeroProg
      (lAeadR C clampedProtoSignalCodec ℓ encT idOf) (lChainPRG C.F) 1 1
      (lIdeal C clampedProtoSignalCodec ℓ encT) 1 qR maxForwardJumps j
    have hhs : p0.handlePre.size ≤ 14000 + 60 * bits qR :=
      hybHandlePreC_size_le (Pt := Pt) C ℓ encT idOf (I₀ := I₀')
        (mSlot := 0) hj2 (Nat.zero_le _) (CryptoGames.FSAEAD.Thm5.isLookaheadHop j)
        (fun {Δ} ia =>
          Comp.sample (O := HybOps' C ℓ encT idOf)
            (I := PrgRedZeroIface' C ℓ encT)
            (Sum.inl (Sum.inr ()) : (Empty ⊕ Unit) ⊕ UniformSamplerTag Bool) ia)
        none none
        (fun {Δ} ia => by change ia.size + 1 ≤ ia.size + 20; omega) trivial trivial
    have hrs : p0.resume.size ≤ 1500 + 10 * bits qR :=
      hybResumeC_size_le (Pt := Pt) C ℓ encT idOf (I₀ := I₀')
        qR (CryptoGames.FSAEAD.Thm5.isLookaheadHop j)
    have hhn : p0.handlePre.nodes ≤ 14000 :=
      hybHandlePreC_nodes_le (Pt := Pt) C ℓ encT idOf (I₀ := I₀')
        (j / 2) 0 qR (CryptoGames.FSAEAD.Thm5.isLookaheadHop j)
        (fun {Δ} ia =>
          Comp.sample (O := HybOps' C ℓ encT idOf)
            (I := PrgRedZeroIface' C ℓ encT)
            (Sum.inl (Sum.inr ()) : (Empty ⊕ Unit) ⊕ UniformSamplerTag Bool) ia)
        none none
        (fun {Δ} ia => by change ia.nodes + 1 ≤ ia.nodes + 20; omega) trivial trivial
    have hrn : p0.resume.nodes ≤ 1500 :=
      hybResumeC_nodes_le (Pt := Pt) C ℓ encT idOf (I₀ := I₀')
        qR (CryptoGames.FSAEAD.Thm5.isLookaheadHop j)
    have his : p0.init.size ≤ 200 + bits (j / 2) := by
      dsimp only [p0, CryptoGames.FSAEAD.Thm5.Costed.prgRedZeroProg,
        CryptoGames.FSAEAD.Thm5.Costed.initHSE, CryptoGames.FSAEAD.Thm5.Costed.mkHS]
      unfold_vars; dsimp only [Comp.size, Expr.size]; simp only [hb0]; omega
    have hin : p0.init.nodes ≤ 50 := by
      dsimp only [p0, CryptoGames.FSAEAD.Thm5.Costed.prgRedZeroProg,
        CryptoGames.FSAEAD.Thm5.Costed.initHSE, CryptoGames.FSAEAD.Thm5.Costed.mkHS]
      unfold_vars; dsimp only [Comp.nodes, Expr.nodes]; omega
    have hchs : p0.chDone.size ≤ 20 := by
      dsimp only [p0, CryptoGames.FSAEAD.Thm5.Costed.prgRedZeroProg,
        CryptoGames.FSAEAD.Thm5.Costed.hybChDoneC, Comp.size, Expr.size]; omega
    have hchn : p0.chDone.nodes ≤ 20 := by
      dsimp only [p0, CryptoGames.FSAEAD.Thm5.Costed.prgRedZeroProg,
        CryptoGames.FSAEAD.Thm5.Costed.hybChDoneC, Comp.nodes, Expr.nodes]; omega
    have hhps : p0.handlePost.size ≤ 20 := by
      dsimp only [p0, CryptoGames.FSAEAD.Thm5.Costed.prgRedZeroProg,
        CryptoGames.FSAEAD.Thm5.Costed.hybHandlePostC]
      unfold_vars; dsimp only [Comp.size, Expr.size]; omega
    have hhpn : p0.handlePost.nodes ≤ 20 := by
      dsimp only [p0, CryptoGames.FSAEAD.Thm5.Costed.prgRedZeroProg,
        CryptoGames.FSAEAD.Thm5.Costed.hybHandlePostC]
      unfold_vars; dsimp only [Comp.nodes, Expr.nodes]; omega
    have hfSize' : ({ p0 with finish := fin }).finish.size ≤ 100 := hfSize
    have hfNodes' : ({ p0 with finish := fin }).finish.nodes ≤ 50 := hfNodes
    change ({ p0 with finish := fin }).size + 650 * ({ p0 with finish := fin }).nodes ≤
      15000000 + 3000 * bits qR
    dsimp only [TwoStageCostedReduction.size, TwoStageCostedReduction.nodes] at hfSize' hfNodes' ⊢
    omega
  · dsimp only [TwoStageCostedReduction.totalQueries]
    have hz : ∀ {Γ t} (c : Comp (atomicFsOps ℓ Pt C encT) (coinOnlyBaseIface ℓ Pt) Γ t),
        c.queries Empty.elim (fun _ => 0) = 0 := by
      intro Γ t c
      induction c with
      | query g _ => exact nomatch g
      | _ => simp_all [Comp.queries]
    rw [hz, hz, hz, hz, hz, hz]
    simp

theorem fsPrgRedZeroAtomic_bounds (hℓ : ℓ < 10 ^ 6) (qR qep j : ℕ)
    (hj : j ≤ 2 * (qR + maxForwardJumps + 1)) :
    GTwoStageBounded (fsPrgRedZeroAtomic (Pt := Pt) C ℓ encT idOf qR j)
      Empty.elim (fun _ => 0) qR 0 (fsRatchetCostBudget qR qep) := by
  refine fsPrgRedAtomic_bounds_of_finish C ℓ encT idOf hℓ qR qep j hj _ ?_ ?_ ?_
  · refine (compCostBound_le_UB _ _ _ _).trans ?_
    dsimp only [CryptoGames.FSAEAD.Thm5.Costed.hybFinishC, CryptoGames.FSAEAD.Thm5.Costed.orE,
      CryptoGames.FSAEAD.Thm5.Costed.beqBoolE,
      CryptoGames.FSAEAD.Thm5.Costed.hsLf, CryptoGames.FSAEAD.Thm5.Costed.hsB,
      CryptoGames.FSAEAD.Thm5.Costed.hsWin]
    unfold_vars; dsimp only [compCostBoundUB, exprCostBoundUB]; omega
  · dsimp only [CryptoGames.FSAEAD.Thm5.Costed.hybFinishC, CryptoGames.FSAEAD.Thm5.Costed.orE,
      CryptoGames.FSAEAD.Thm5.Costed.beqBoolE,
      CryptoGames.FSAEAD.Thm5.Costed.hsLf, CryptoGames.FSAEAD.Thm5.Costed.hsB,
      CryptoGames.FSAEAD.Thm5.Costed.hsWin]
    unfold_vars; dsimp only [Comp.size, Expr.size]; omega
  · dsimp only [CryptoGames.FSAEAD.Thm5.Costed.hybFinishC, CryptoGames.FSAEAD.Thm5.Costed.orE,
      CryptoGames.FSAEAD.Thm5.Costed.beqBoolE,
      CryptoGames.FSAEAD.Thm5.Costed.hsLf, CryptoGames.FSAEAD.Thm5.Costed.hsB,
      CryptoGames.FSAEAD.Thm5.Costed.hsWin]
    unfold_vars; dsimp only [Comp.nodes, Expr.nodes]; omega

private lemma fsMultiRedAtomic_bounds_of_finish (hℓ : ℓ < 10 ^ 6) (qR qep : ℕ) (la : Bool)
    (fin : Comp (HybOps' C ℓ encT idOf) (MultiRedIface' C ℓ encT)
      [CryptoGames.FSAEAD.Thm5.Costed.stTy, .bool, .unit] .bool)
    (hfCost : compCostBound hybOpCU multiSC multiQC fin ≤ 100)
    (hfSize : fin.size ≤ 100) (hfNodes : fin.nodes ≤ 50)
    (hfQ : fin.queries (fun _ => 1) (fun _ => 0) = 0) :
    GTwoStageBounded
      (compilePureTwoStageRed (fsaeadRatchetCodec ℓ Pt)
        (multiMacroBundle (Pt := Pt) C ℓ encT idOf)
        { CryptoGames.FSAEAD.Thm5.Costed.multiRedProg
            (lAeadR C clampedProtoSignalCodec ℓ encT idOf) (lChainPRG C.F) 1 1
            (lIdeal C clampedProtoSignalCodec ℓ encT) 1 qR maxForwardJumps
            (if la then qR + (maxForwardJumps + 1) else qR) la with
          finish := fin }
        rfl rfl)
      (fun _ => 1) (fun _ => 0) qR qR (fsRatchetCostBudget qR qep) := by
  have hdiv : ℓ / 32 ≤ 31250 := by omega
  have hmfj : maxForwardJumps = 25000 := rfl
  have hN : (if la then qR + (maxForwardJumps + 1) else qR) ≤ qR + 25002 := by
    split_ifs <;> omega
  have hb0 : bits 0 = 1 := rfl
  let I₀' := CryptoGames.OTCCA.Costed.otccaIface (S := HSig' Pt ℓ)
    (.prod .nat (.base .ad)) (.base .msg) (.base .ct)
    (lIdeal C clampedProtoSignalCodec ℓ encT) 1
  refine gTwoStageBounded_of_bounds _ _ _ _ _ _ ?_ ?_ ?_ (atomicFsOps_sizeHonest ℓ Pt C encT)
    (atomicBaseSamplers_sizeHonest ℓ Pt)
  · have hh := hybHandlePreC_cost_le (Pt := Pt) C ℓ encT idOf
      (I₀ := I₀') (sC := multiSC) (qC := multiQC)
      (by dsimp [multiSC]; omega) (by dsimp [multiSC]; omega) hN hN la
      (fun {Δ} ia =>
        Comp.sample (O := HybOps' C ℓ encT idOf)
          (I := MultiRedIface' C ℓ encT)
          (Sum.inl () : Unit ⊕ UniformSamplerTag Bool) ia)
      (some (CryptoGames.FSAEAD.Thm5.Costed.otSpecialEncC
        (lAeadR C clampedProtoSignalCodec ℓ encT idOf) (lChainPRG C.F) 1 1
        (lIdeal C clampedProtoSignalCodec ℓ encT) 1))
      (some (CryptoGames.FSAEAD.Thm5.Costed.otSpecialDecC
        (lAeadR C clampedProtoSignalCodec ℓ encT idOf) (lChainPRG C.F) 1 1
        (lIdeal C clampedProtoSignalCodec ℓ encT) 1))
      (fun {Δ} ia => by
        change exprCostBoundUB hybOpCU ia + 2190000 ≤ exprCostBoundUB hybOpCU ia + 2500000
        omega)
      (fun {Δ} x => by
        dsimp only [I₀', CryptoGames.FSAEAD.Thm5.Costed.otSpecialEncC,
          CryptoGames.FSAEAD.Thm5.Costed.callC, HybOps', MultiRedIface',
          Ops.sum, CryptoGames.PRG.Costed.prgOps, CryptoGames.OTCCA.Costed.otccaOps,
          CryptoGames.OTCCA.Costed.otccaIface, Iface.withSamp]
        unfold_vars
        dsimp only [compCostBoundUB, exprCostBoundUB, multiSC, multiQC]; omega)
      (fun {Δ} x => by
        change exprCostBoundUB hybOpCU x + 63000 ≤ exprCostBoundUB hybOpCU x + 70000
        omega)
    have hr := hybResumeC_cost_le (Pt := Pt) C ℓ encT idOf
      (I₀ := I₀') (sC := multiSC) (qC := multiQC)
      (by dsimp [multiSC]; omega) qR la
    refine (compilePureTwoStageRed_totalCost_le_UB (fsaeadRatchetCodec ℓ Pt)
      (multiMacroBundle (Pt := Pt) C ℓ encT idOf) _ rfl rfl hybOpCU multiSC multiQC
      (hybOpMacro_cost_le C ℓ encT idOf hℓ) (multiSampMacro_cost_le C ℓ encT idOf hℓ)
      (multiQueryMacro_cost_le C ℓ encT idOf hℓ)
      (cInit := 500) (cHandlePre := 60000000 + 2000 * qR) (cHandlePost := 20)
      (cChDone := 10) (cResume := 20000 + 12000000 * qR) (cFin := 100)
      ?_ ?_ ?_ ?_ ?_ ?_ qR).trans ?_
    · dsimp only [CryptoGames.FSAEAD.Thm5.Costed.multiRedProg,
        CryptoGames.FSAEAD.Thm5.Costed.initHSE, CryptoGames.FSAEAD.Thm5.Costed.mkHS]
      unfold_vars
      dsimp only [compCostBound, exprCostBound, multiSC]
      simp only [hb0]; omega
    · exact hh
    · dsimp only [CryptoGames.FSAEAD.Thm5.Costed.multiRedProg,
        CryptoGames.FSAEAD.Thm5.Costed.hybHandlePostC]
      unfold_vars; dsimp only [compCostBound, exprCostBound]; omega
    · dsimp only [CryptoGames.FSAEAD.Thm5.Costed.multiRedProg,
        CryptoGames.FSAEAD.Thm5.Costed.hybChDoneC]
      dsimp only [compCostBound, exprCostBound]; omega
    · exact hr
    · exact hfCost
    · have hcc : (fsaeadRatchetCodec ℓ Pt).codecCost ≤ 200000 := by
        dsimp [fsaeadRatchetCodec]; omega
      have hmPre : max (60000000 + 2000 * qR) 20 = 60000000 + 2000 * qR := by omega
      have hmCh : max 10 (20000 + 12000000 * qR) = 20000 + 12000000 * qR := by omega
      rw [hmPre, hmCh]
      have hmax : max (slotOtccaTargetIface ℓ Pt).uCost
          (60000000 + 2000 * qR + (fsaeadRatchetCodec ℓ Pt).codecCost) ≤
          61000000 + 2000 * qR := by dsimp [slotOtccaTargetIface]; omega
      have hmul := Nat.mul_le_mul_left qR hmax
      have hbud := fs_poly_le_fsRatchetCostBudget qR qep
      nlinarith
  · refine (compilePureTwoStageRed_size_le_nodes (fsaeadRatchetCodec ℓ Pt)
      (multiMacroBundle (Pt := Pt) C ℓ encT idOf) _ rfl rfl 650
      (fun o => by dsimp only [multiMacroBundle]; have := hybOpMacro_size_le C ℓ encT idOf o; omega)
      (fun s => by have := multiSampMacro_size_le C ℓ encT idOf hℓ s; omega)
      (fun g => by have := multiQueryMacro_size_le C ℓ encT idOf g; omega)).trans ?_
    refine size_le_fs_budget_of_qR (C₀ := 15000000) (C₁ := 3000) (by omega) (by omega) ?_
    let m0 := CryptoGames.FSAEAD.Thm5.Costed.multiRedProg
      (lAeadR C clampedProtoSignalCodec ℓ encT idOf) (lChainPRG C.F) 1 1
      (lIdeal C clampedProtoSignalCodec ℓ encT) 1 qR maxForwardJumps
      (if la then qR + (maxForwardJumps + 1) else qR) la
    have hhs : m0.handlePre.size ≤ 14000 + 60 * bits qR :=
      hybHandlePreC_size_le (Pt := Pt) C ℓ encT idOf (I₀ := I₀')
        hN hN la
        (fun {Δ} ia =>
          Comp.sample (O := HybOps' C ℓ encT idOf)
            (I := MultiRedIface' C ℓ encT)
            (Sum.inl () : Unit ⊕ UniformSamplerTag Bool) ia)
        (some (CryptoGames.FSAEAD.Thm5.Costed.otSpecialEncC
          (lAeadR C clampedProtoSignalCodec ℓ encT idOf) (lChainPRG C.F) 1 1
          (lIdeal C clampedProtoSignalCodec ℓ encT) 1))
        (some (CryptoGames.FSAEAD.Thm5.Costed.otSpecialDecC
          (lAeadR C clampedProtoSignalCodec ℓ encT idOf) (lChainPRG C.F) 1 1
          (lIdeal C clampedProtoSignalCodec ℓ encT) 1))
        (fun {Δ} ia => by change ia.size + 1 ≤ ia.size + 20; omega)
        (fun {Δ} x => by
          dsimp only [I₀', CryptoGames.FSAEAD.Thm5.Costed.otSpecialEncC,
            CryptoGames.FSAEAD.Thm5.Costed.callC, HybOps', MultiRedIface',
            Ops.sum, CryptoGames.PRG.Costed.prgOps, CryptoGames.OTCCA.Costed.otccaOps,
            CryptoGames.OTCCA.Costed.otccaIface, Iface.withSamp]
          unfold_vars; dsimp only [Comp.size, Expr.size]; omega)
        (fun {Δ} x => by
          change x.size + 1 ≤ x.size + 20
          omega)
    have hrs : m0.resume.size ≤ 1500 + 10 * bits qR :=
      hybResumeC_size_le (Pt := Pt) C ℓ encT idOf (I₀ := I₀') qR la
    have hhn : m0.handlePre.nodes ≤ 14000 :=
      hybHandlePreC_nodes_le (Pt := Pt) C ℓ encT idOf (I₀ := I₀')
        (if la then qR + (maxForwardJumps + 1) else qR)
        (if la then qR + (maxForwardJumps + 1) else qR) qR la
        (fun {Δ} ia =>
          Comp.sample (O := HybOps' C ℓ encT idOf)
            (I := MultiRedIface' C ℓ encT)
            (Sum.inl () : Unit ⊕ UniformSamplerTag Bool) ia)
        (some (CryptoGames.FSAEAD.Thm5.Costed.otSpecialEncC
          (lAeadR C clampedProtoSignalCodec ℓ encT idOf) (lChainPRG C.F) 1 1
          (lIdeal C clampedProtoSignalCodec ℓ encT) 1))
        (some (CryptoGames.FSAEAD.Thm5.Costed.otSpecialDecC
          (lAeadR C clampedProtoSignalCodec ℓ encT idOf) (lChainPRG C.F) 1 1
          (lIdeal C clampedProtoSignalCodec ℓ encT) 1))
        (fun {Δ} ia => by change ia.nodes + 1 ≤ ia.nodes + 20; omega)
        (fun {Δ} x => by
          dsimp only [I₀', CryptoGames.FSAEAD.Thm5.Costed.otSpecialEncC,
            CryptoGames.FSAEAD.Thm5.Costed.callC]
          unfold_vars; dsimp only [Comp.nodes, Expr.nodes]; omega)
        (fun {Δ} x => by
          change x.nodes + 1 ≤ x.nodes + 20
          omega)
    have hrn : m0.resume.nodes ≤ 1500 :=
      hybResumeC_nodes_le (Pt := Pt) C ℓ encT idOf (I₀ := I₀') qR la
    have his : m0.init.size ≤ 200 := by
      dsimp only [m0, CryptoGames.FSAEAD.Thm5.Costed.multiRedProg,
        CryptoGames.FSAEAD.Thm5.Costed.initHSE, CryptoGames.FSAEAD.Thm5.Costed.mkHS]
      unfold_vars; dsimp only [Comp.size, Expr.size]; simp only [hb0]; omega
    have hin : m0.init.nodes ≤ 50 := by
      dsimp only [m0, CryptoGames.FSAEAD.Thm5.Costed.multiRedProg,
        CryptoGames.FSAEAD.Thm5.Costed.initHSE, CryptoGames.FSAEAD.Thm5.Costed.mkHS]
      unfold_vars; dsimp only [Comp.nodes, Expr.nodes]; omega
    have hchs : m0.chDone.size ≤ 20 := by
      dsimp only [m0, CryptoGames.FSAEAD.Thm5.Costed.multiRedProg,
        CryptoGames.FSAEAD.Thm5.Costed.hybChDoneC, Comp.size, Expr.size]; omega
    have hchn : m0.chDone.nodes ≤ 20 := by
      dsimp only [m0, CryptoGames.FSAEAD.Thm5.Costed.multiRedProg,
        CryptoGames.FSAEAD.Thm5.Costed.hybChDoneC, Comp.nodes, Expr.nodes]; omega
    have hhps : m0.handlePost.size ≤ 20 := by
      dsimp only [m0, CryptoGames.FSAEAD.Thm5.Costed.multiRedProg,
        CryptoGames.FSAEAD.Thm5.Costed.hybHandlePostC]
      unfold_vars; dsimp only [Comp.size, Expr.size]; omega
    have hhpn : m0.handlePost.nodes ≤ 20 := by
      dsimp only [m0, CryptoGames.FSAEAD.Thm5.Costed.multiRedProg,
        CryptoGames.FSAEAD.Thm5.Costed.hybHandlePostC]
      unfold_vars; dsimp only [Comp.nodes, Expr.nodes]; omega
    have hfSize' : ({ m0 with finish := fin }).finish.size ≤ 100 := hfSize
    have hfNodes' : ({ m0 with finish := fin }).finish.nodes ≤ 50 := hfNodes
    change ({ m0 with finish := fin }).size + 650 * ({ m0 with finish := fin }).nodes ≤
      15000000 + 3000 * bits qR
    dsimp only [TwoStageCostedReduction.size, TwoStageCostedReduction.nodes] at hfSize' hfNodes' ⊢
    omega
  · refine (compilePureTwoStageRed_totalQueries_le (fsaeadRatchetCodec ℓ Pt)
      (multiMacroBundle (Pt := Pt) C ℓ encT idOf) _ rfl rfl (fun _ => 1) (fun _ => 0)
      (fun _ => 1) (fun _ => 0)
      (fun s => by
        cases s with
        | inl u =>
          cases u
          simp [multiMacroBundle, sampleIdealComp, sampleU64Comp, Comp.queries]
        | inr t =>
          rcases t with _ | N | (_ | _) <;> simp [multiMacroBundle, Comp.queries])
      (fun g => by cases g <;> simp [multiMacroBundle, Comp.queries]) qR).trans ?_
    let m0 := CryptoGames.FSAEAD.Thm5.Costed.multiRedProg
      (lAeadR C clampedProtoSignalCodec ℓ encT idOf) (lChainPRG C.F) 1 1
      (lIdeal C clampedProtoSignalCodec ℓ encT) 1 qR maxForwardJumps
      (if la then qR + (maxForwardJumps + 1) else qR) la
    have hhq : m0.handlePre.queries (fun _ => 1) (fun _ => 0) ≤ 1 :=
      hybHandlePreC_queries_le (Pt := Pt) C ℓ encT idOf (I₀ := I₀') (fun _ => 1)
        (if la then qR + (maxForwardJumps + 1) else qR)
        (if la then qR + (maxForwardJumps + 1) else qR) qR la
        (fun {Δ} ia =>
          Comp.sample (O := HybOps' C ℓ encT idOf)
            (I := MultiRedIface' C ℓ encT)
            (Sum.inl () : Unit ⊕ UniformSamplerTag Bool) ia)
        (some (CryptoGames.FSAEAD.Thm5.Costed.otSpecialEncC
          (lAeadR C clampedProtoSignalCodec ℓ encT idOf) (lChainPRG C.F) 1 1
          (lIdeal C clampedProtoSignalCodec ℓ encT) 1))
        (some (CryptoGames.FSAEAD.Thm5.Costed.otSpecialDecC
          (lAeadR C clampedProtoSignalCodec ℓ encT idOf) (lChainPRG C.F) 1 1
          (lIdeal C clampedProtoSignalCodec ℓ encT) 1))
        (fun {Δ} _ => rfl)
        (fun {Δ} x => by
          dsimp only [I₀', CryptoGames.FSAEAD.Thm5.Costed.otSpecialEncC,
            CryptoGames.FSAEAD.Thm5.Costed.callC, Comp.queries]; omega)
        (fun {Δ} x => by
          dsimp only [I₀', CryptoGames.FSAEAD.Thm5.Costed.otSpecialDecC, Comp.queries]; omega)
    have hrq : m0.resume.queries (fun _ => 1) (fun _ => 0) = 0 :=
      hybResumeC_queries (Pt := Pt) C ℓ encT idOf (I₀ := I₀') (fun _ => 1) qR la
    have hiq : m0.init.queries (fun _ => 1) (fun _ => 0) = 0 := rfl
    have hcdq : m0.chDone.queries (fun _ => 1) (fun _ => 0) = 0 := rfl
    have hhpq : m0.handlePost.queries (fun _ => 1) (fun _ => 0) = 0 := rfl
    have hfQ' : ({ m0 with finish := fin }).finish.queries (fun _ => 1) (fun _ => 0) = 0 := hfQ
    change ({ m0 with finish := fin }).totalQueries (fun _ => 1) (fun _ => 0) qR ≤ qR
    dsimp only [TwoStageCostedReduction.totalQueries] at hfQ' ⊢
    rw [hiq, hcdq, hrq, hhpq, hfQ']
    have hmul := Nat.mul_le_mul_left qR (max_le hhq (Nat.zero_le _))
    omega

theorem fsMultiRedAtomic_bounds (hℓ : ℓ < 10 ^ 6) (qR qep : ℕ) (la : Bool) :
    GTwoStageBounded (fsMultiRedAtomic (Pt := Pt) C ℓ encT idOf qR la)
      (fun _ => 1) (fun _ => 0) qR qR (fsRatchetCostBudget qR qep) := by
  refine fsMultiRedAtomic_bounds_of_finish C ℓ encT idOf hℓ qR qep la _ ?_ ?_ ?_ ?_
  · refine (compCostBound_le_UB _ _ _ _).trans ?_
    dsimp only [CryptoGames.FSAEAD.Thm5.Costed.hybFinishC, CryptoGames.FSAEAD.Thm5.Costed.orE,
      CryptoGames.FSAEAD.Thm5.Costed.beqBoolE,
      CryptoGames.FSAEAD.Thm5.Costed.hsLf, CryptoGames.FSAEAD.Thm5.Costed.hsB,
      CryptoGames.FSAEAD.Thm5.Costed.hsWin]
    unfold_vars; dsimp only [compCostBoundUB, exprCostBoundUB]; omega
  · dsimp only [CryptoGames.FSAEAD.Thm5.Costed.hybFinishC, CryptoGames.FSAEAD.Thm5.Costed.orE,
      CryptoGames.FSAEAD.Thm5.Costed.beqBoolE,
      CryptoGames.FSAEAD.Thm5.Costed.hsLf, CryptoGames.FSAEAD.Thm5.Costed.hsB,
      CryptoGames.FSAEAD.Thm5.Costed.hsWin]
    unfold_vars; dsimp only [Comp.size, Expr.size]; omega
  · dsimp only [CryptoGames.FSAEAD.Thm5.Costed.hybFinishC, CryptoGames.FSAEAD.Thm5.Costed.orE,
      CryptoGames.FSAEAD.Thm5.Costed.beqBoolE,
      CryptoGames.FSAEAD.Thm5.Costed.hsLf, CryptoGames.FSAEAD.Thm5.Costed.hsB,
      CryptoGames.FSAEAD.Thm5.Costed.hsWin]
    unfold_vars; dsimp only [Comp.nodes, Expr.nodes]; omega
  · rfl

theorem fsPrgRedAuthAtomic_bounds (hℓ : ℓ < 10 ^ 6) (qR qep j : ℕ)
    (hj : j ≤ 2 * (qR + maxForwardJumps + 1)) :
    GTwoStageBounded (fsPrgRedAuthAtomic (Pt := Pt) C ℓ encT idOf qR j)
      Empty.elim (fun _ => 0) qR 0 (fsRatchetCostBudget qR qep) := by
  refine fsPrgRedAtomic_bounds_of_finish C ℓ encT idOf hℓ qR qep j hj _ ?_ ?_ ?_
  · dsimp only [CryptoGames.FSAEAD.Thm5.Costed.hybFinishAuthC, compCostBound, exprCostBound]; omega
  · dsimp only [CryptoGames.FSAEAD.Thm5.Costed.hybFinishAuthC, Comp.size, Expr.size]; omega
  · dsimp only [CryptoGames.FSAEAD.Thm5.Costed.hybFinishAuthC, Comp.nodes, Expr.nodes]; omega

theorem fsMultiRedAuthAtomic_bounds (hℓ : ℓ < 10 ^ 6) (qR qep : ℕ) (la : Bool) :
    GTwoStageBounded (fsMultiRedAuthAtomic (Pt := Pt) C ℓ encT idOf qR la)
      (fun _ => 1) (fun _ => 0) qR qR (fsRatchetCostBudget qR qep) := by
  refine fsMultiRedAtomic_bounds_of_finish C ℓ encT idOf hℓ qR qep la _ ?_ ?_ ?_ ?_
  · dsimp only [CryptoGames.FSAEAD.Thm5.Costed.hybFinishAuthC, compCostBound, exprCostBound]; omega
  · dsimp only [CryptoGames.FSAEAD.Thm5.Costed.hybFinishAuthC, Comp.size, Expr.size]; omega
  · dsimp only [CryptoGames.FSAEAD.Thm5.Costed.hybFinishAuthC, Comp.nodes, Expr.nodes]; omega
  · rfl

end AllProgBounds

end Computational.Proofs.ReductionDsl.FsAtomicBounds
