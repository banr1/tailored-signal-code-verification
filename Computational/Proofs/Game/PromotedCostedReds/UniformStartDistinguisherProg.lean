/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Computational.Proofs.Game.PromotedCostedReds.SessionProgCommon
public import Computational.Proofs.E2E.Dsl.DrSessionSim
import Computational.Proofs.ReductionDsl.SizeBudgetBridge
import Computational.Proofs.E2E.ComposedPrefixHelpers

/-!
# Promoted `CostedReduction` Witness for `uniformStartDistinguisher`

Constructs the `CostedReduction` witness `uniformStartRed` for `uniformStartDistinguisher` and
proves its `GRedBounded` cost bounds and `.eval` equivalence.
-/

@[expose] public section

set_option autoImplicit false

namespace Computational.Proofs.Game.PromotedCostedReds.UniformStartDistinguisherProg

open OracleSpec OracleComp
open _root_.ReductionDsl (Ty Var Env Ops Iface Expr Comp CostedReduction bits bits_mono handlerImpl
  bind_congr_of_mem_support' atomicSig atomicSessionOps coinOnlyIface e2eSessionCodec BV256
  reductionSizeBudget)
open Computational.Proofs.ReductionDsl.SizeBudgetBridge (size_le_budget_of_log_cost)
open CryptoGames (Party)
open CryptoGames.CBC (Plain)
open CryptoGames.Ratchet (RootKey)
open CryptoGames.Ratchet.LibsignalInst (libsignalSessionSchemeFromEpoch0Keys ratchetKeyAdmissible
  configR1OnCurve)
open CryptoGames.SM (GameState initState corrR oracleImplR runR MakesAtMostQueries
  noAliceCorrWhileAliceBelowEpoch10 inWindow partyEnc orE boolEq pGet orE_eval boolEq_eval
  pGet_eval some_eval)
open CryptoGames.LibsignalSession (Crypto IdentityKey PublicKey GhostState)
open CryptoVerification.LibsignalProtoCodec (protoSignalCodec)
open CryptoVerification.LibsignalSpqrV1 (MlKem spqrV1SessionUniformCoins)
open CryptoVerification.LibsignalSession (ratchetCostBudget GRedBounded)
open CryptoVerification.E2E (Bytes paramsIdsWithSpqr paramsV1 sessionSchemeFixedSpk
  uniformStartDistinguisher oracleImplR_preserves_b)
open CryptoVerification.E2E.Costed (e2eSig e2eOps GhostStT PlainT B BV512 smQT smQenc smRT
  partyToBool)
open CryptoVerification.E2E.Costed (gRedBounded_of_bounds)
open Computational.Proofs.E2E.Dsl.SmReachInv (SmListBounded SmReachBounded smReachBounded_oracleImplR)
open Computational.Proofs.E2E.Dsl.DrSessionSimBookkeeping (partyToBool_eq_partyEnc smRenc smRCorrE
  eval_smRCorrE cost_smRCorrE e2eGsTy e2eGsEnc e2eGsSt e2eGsB e2eGsWin e2eGsEpoch
  e2eCorrAllowedE eval_e2eCorrAllowedE cost_e2eCorrAllowedE_le
  e2eInWindowE eval_e2eInWindowE cost_e2eInWindowE_le
  e2eAfterCorrAllowedE eval_e2eAfterCorrAllowedE cost_e2eAfterCorrAllowedE_le)
open Computational.Proofs.E2E.Dsl.SpqrSim (spqrDslHooks)
open Computational.Proofs.E2E.Dsl.DrSessionSim (drTrArmC drChArmC drDlArmC drIjArmC
  drTrArmC_queries_zero drChArmC_queries_zero drDlArmC_queries_zero drIjArmC_queries_zero
  drTrArmC_cost drChArmC_cost drDlArmC_cost drIjArmC_cost
  drTrArmC_eval drChArmC_eval drDlArmC_eval drIjArmC_eval)
open Computational.Proofs.Game.PromotedCostedReds.AtomicOpsHonest (atomicSessionOps_sizeHonest
  atomicSamplers_sizeHonest)
open Computational.Proofs.Game.PromotedCostedReds.AtomicSessionBridge (zeroPqxdhPrims
  liftTy liftVal liftExpr liftExpr_cost liftExpr_eval coinE2EIface coinE2ESamplers
  liftCompCoins liftCompCoins_queries_zero liftCompCoins_cost liftCompCoins_eval)
open Computational.Proofs.Game.PromotedCostedReds.SessionProgCommon (eval_eq_simulateQ_of_enc
  isQueryBoundP_of_makesAtMostQueries liftP_unif_eq_self liftVal_smQenc
  liftExpr_size_le liftCompCoins_size_le
  initEpoch0GsC initEpoch0GsC_queries_zero initEpoch0GsC_cost initEpoch0GsC_size_le initEpoch0GsC_eval
  epoch0InitImpl smReachBounded_epoch0InitImpl oracleImplR_epoch0Keys_eq_fixedSpk
  bits_succ_le session_cost_le_ratchetCostBudget
  dummyBoolSessionRed dummyBoolSessionRed_totalQueries dummyBoolSessionRed_totalCost_le
  dummyBoolSessionRed_size_le)

private theorem liftP_pure {S0 : ReductionDsl.Sig} {ι : Type} {T : OracleSpec ι}
    (I : Iface S0 T) {α : Type} (a : α) :
    I.liftP (pure a) = pure a := by
  simp [Iface.liftP]

/-! ## Component size bounds -/

section SpqrSimSizeBounds

set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option maxRecDepth 8192

open Computational.Proofs.E2E.Dsl.TablesHonest (e2ePureOp e2eCurveOp e2eCryptoOp
  size_e2ePureOp size_e2eCurveOp size_e2eCryptoOp)
open Computational.Proofs.E2E.Dsl.SpqrSimChain (spqrNegotiateInitC spqrBraidSendC spqrBraidRecvC
  spqrChainFromVnC spqrChainAddEpochC spqrChainNextKeyC listDropExpr listGetExpr listSetExpr
  spqrEpochIdxExpr spqrResolveChainComp spqrAddEpochOptComp clearLinkSendNextExpr
  linksClearSendPrefixExpr spqrChainSendKeyComp)
open Computational.Proofs.E2E.Dsl.SpqrSimHist (spqrListRevExpr spqrPrevGetFuelExpr spqrPrevGetExpr
  spqrPrevGcFuelExpr spqrPrevGcExpr spqrKeyAdvanceStep spqrKeyAdvanceFuelComp
  spqrKeyAdvanceComp spqrDirKeyFwdComp spqrDirKeyComp spqrChainRecvKeyComp)
open Computational.Proofs.E2E.Dsl.SpqrSimSend (spqrRunSendChainComp spqrSendComp)
open Computational.Proofs.E2E.Dsl.SpqrSimRecv (spqrRecvGreaterComp spqrRecvPrepStateComp
  spqrRunRecvChainComp spqrRecvV1BodyComp spqrRecvComp)

private theorem bits_c0 : bits 0 = 1 := by decide
private theorem bits_c1 : bits 1 = 1 := by decide
private theorem bits_c2 : bits 2 = 2 := by decide
private theorem bits_c3 : bits 3 = 2 := by decide
private theorem bits_c4 : bits 4 = 3 := by decide
private theorem bits_c5 : bits 5 = 3 := by decide
private theorem bits_c8 : bits 8 = 4 := by decide
private theorem bits_c10 : bits 10 = 4 := by decide
private theorem bits_c11 : bits 11 = 4 := by decide
private theorem bits_c12 : bits 12 = 4 := by decide
private theorem bits_c16 : bits 16 = 5 := by decide
private theorem bits_c32 : bits 32 = 6 := by decide
private theorem bits_c35 : bits 35 = 6 := by decide
private theorem bits_c36 : bits 36 = 6 := by decide
private theorem bits_c64 : bits 64 = 7 := by decide
private theorem bits_c256 : bits 256 = 9 := by decide
private theorem bits_c1568 : bits 1568 = 11 := by decide
private theorem bits_c2000 : bits 2000 = 11 := by decide
private theorem bits_c2201 : bits 2201 = 12 := by decide
private theorem bits_c3168 : bits 3168 = 12 := by decide
private theorem bits_c4201 : bits 4201 = 13 := by decide
private theorem bits_c25000 : bits 25000 = 15 := by decide
private theorem bits_p32 : bits ((32 : ℕ+) : ℕ) = 6 := bits_c32
private theorem bits_p35 : bits ((35 : ℕ+) : ℕ) = 6 := bits_c35

attribute [local simp] Expr.size Comp.size CryptoVerification.E2E.Costed.E2EPureOp.opSize
  bits_c0 bits_c1 bits_c2 bits_c3 bits_c4 bits_c5 bits_c8 bits_c10 bits_c11 bits_c12
  bits_c16 bits_c32 bits_c35 bits_c36 bits_c64 bits_c256 bits_c1568 bits_c2000
  bits_c2201 bits_c3168 bits_c4201 bits_c25000 bits_p32 bits_p35

@[local simp] private theorem size_v0 {S0 : ReductionDsl.Sig} {O : Ops S0}
    {Γ : List (Ty S0)} {t : Ty S0} :
    (Expr.v0 (O := O) (Γ := Γ) (t := t)).size = 1 := rfl
@[local simp] private theorem size_v1 {S0 : ReductionDsl.Sig} {O : Ops S0}
    {Γ : List (Ty S0)} {t a : Ty S0} :
    (Expr.v1 (O := O) (Γ := Γ) (t := t) (a := a)).size = 1 := rfl
@[local simp] private theorem size_v2 {S0 : ReductionDsl.Sig} {O : Ops S0}
    {Γ : List (Ty S0)} {t a b : Ty S0} :
    (Expr.v2 (O := O) (Γ := Γ) (t := t) (a := a) (b := b)).size = 1 := rfl
@[local simp] private theorem size_v3 {S0 : ReductionDsl.Sig} {O : Ops S0}
    {Γ : List (Ty S0)} {t a b c : Ty S0} :
    (Expr.v3 (O := O) (Γ := Γ) (t := t) (a := a) (b := b) (c := c)).size = 1 := rfl
@[local simp] private theorem size_v4 {S0 : ReductionDsl.Sig} {O : Ops S0}
    {Γ : List (Ty S0)} {t a b c d : Ty S0} :
    (Expr.v4 (O := O) (Γ := Γ) (t := t) (a := a) (b := b) (c := c) (d := d)).size = 1 := rfl
@[local simp] private theorem size_v5 {S0 : ReductionDsl.Sig} {O : Ops S0}
    {Γ : List (Ty S0)} {t a b c d e : Ty S0} :
    (Expr.v5 (O := O) (Γ := Γ) (t := t) (a := a) (b := b) (c := c) (d := d) (e := e)).size = 1 :=
  rfl
@[local simp] private theorem size_v6 {S0 : ReductionDsl.Sig} {O : Ops S0}
    {Γ : List (Ty S0)} {t a b c d e f : Ty S0} :
    (Expr.v6 (O := O) (Γ := Γ) (t := t) (a := a) (b := b) (c := c) (d := d)
      (e := e) (f := f)).size = 1 := rfl

private def esizeHide {S0 : ReductionDsl.Sig} {O : Ops S0} {Γ : List (Ty S0)} {t : Ty S0}
    (e : Expr O Γ t) (ub : ℕ) : ℕ := min e.size ub
private def csizeHide {S0 : ReductionDsl.Sig} {O : Ops S0} {ι : Type} {T : OracleSpec ι}
    {I : Iface S0 T} {Γ : List (Ty S0)} {t : Ty S0} (c : Comp O I Γ t) (ub : ℕ) : ℕ :=
  min c.size ub
private theorem esize_eq_hide {S0 : ReductionDsl.Sig} {O : Ops S0} {Γ : List (Ty S0)} {t : Ty S0}
    {e : Expr O Γ t} {ub : ℕ} (h : e.size ≤ ub) : e.size = esizeHide e ub :=
  (Nat.min_eq_left h).symm
private theorem csize_eq_hide {S0 : ReductionDsl.Sig} {O : Ops S0} {ι : Type} {T : OracleSpec ι}
    {I : Iface S0 T} {Γ : List (Ty S0)} {t : Ty S0} {c : Comp O I Γ t} {ub : ℕ}
    (h : c.size ≤ ub) : c.size = csizeHide c ub :=
  (Nat.min_eq_left h).symm
private theorem esizeHide_def {S0 : ReductionDsl.Sig} {O : Ops S0} {Γ : List (Ty S0)} {t : Ty S0}
    (e : Expr O Γ t) (ub : ℕ) : esizeHide e ub = min e.size ub := rfl
private theorem csizeHide_def {S0 : ReductionDsl.Sig} {O : Ops S0} {ι : Type} {T : OracleSpec ι}
    {I : Iface S0 T} {Γ : List (Ty S0)} {t : Ty S0} (c : Comp O I Γ t) (ub : ℕ) :
    csizeHide c ub = min c.size ub := rfl

attribute [local irreducible] esizeHide csizeHide

section SpqrInner

variable {ℓ : ℕ} {Pt : Type} {P : SignalPqxdh.Primitives} {C : Crypto} {K : MlKem}
  {decT : PublicKey → Option Pt} {encT : Pt → PublicKey}
  {ι : Type} {T : OracleSpec ι} (I : Iface (e2eSig ℓ) T)

@[local simp] private theorem size_spqrNegotiateInitC {Γ} (a) :
    (spqrNegotiateInitC (P := P) (C := C) (K := K) (decT := decT) (encT := encT)
      I (Γ := Γ) a).size = a.size + 2 := by
  simp [spqrNegotiateInitC]
@[local simp] private theorem size_spqrBraidSendC {Γ} (a) :
    (spqrBraidSendC (P := P) (C := C) (K := K) (decT := decT) (encT := encT)
      I (Γ := Γ) a).size = a.size + 2 := by
  simp [spqrBraidSendC]
@[local simp] private theorem size_spqrBraidRecvC {Γ} (a) :
    (spqrBraidRecvC (P := P) (C := C) (K := K) (decT := decT) (encT := encT)
      I (Γ := Γ) a).size = a.size + 2 := by
  simp [spqrBraidRecvC]
@[local simp] private theorem size_spqrChainFromVnC {Γ} (a) :
    (spqrChainFromVnC (P := P) (C := C) (K := K) (decT := decT) (encT := encT)
      I (Γ := Γ) a).size = a.size + 2 := by
  simp [spqrChainFromVnC]
@[local simp] private theorem size_spqrChainAddEpochC {Γ} (a) :
    (spqrChainAddEpochC (P := P) (C := C) (K := K) (decT := decT) (encT := encT)
      I (Γ := Γ) a).size = a.size + 2 := by
  simp [spqrChainAddEpochC]
@[local simp] private theorem size_spqrChainNextKeyC {Γ} (a) :
    (spqrChainNextKeyC (P := P) (C := C) (K := K) (decT := decT) (encT := encT)
      I (Γ := Γ) a).size = a.size + 2 := by
  simp [spqrChainNextKeyC]

private theorem clearLinkSendNextExpr_size_le {Γ}
    (lk : Expr (e2eOps ℓ P C K decT encT) Γ _) :
    (clearLinkSendNextExpr lk).size ≤ lk.size + 250 := by
  simp [clearLinkSendNextExpr]

@[local simp] private theorem size_clearLink_eq {Γ}
    (lk : Expr (e2eOps ℓ P C K decT encT) Γ _) :
    (clearLinkSendNextExpr lk).size = esizeHide (clearLinkSendNextExpr lk) (lk.size + 250) :=
  esize_eq_hide (clearLinkSendNextExpr_size_le lk)

private theorem spqrChainSendKeyComp_size_le {Γ}
    (ch : Expr (e2eOps ℓ P C K decT encT) Γ _)
    (epoch : Expr (e2eOps ℓ P C K decT encT) Γ _) :
    (spqrChainSendKeyComp I ch epoch).size ≤ ch.size + epoch.size + 5000 := by
  simp [spqrChainSendKeyComp, spqrEpochIdxExpr, linksClearSendPrefixExpr,
    listDropExpr, listGetExpr, listSetExpr]
  simp only [esizeHide_def]; omega

@[local simp] private theorem size_spqrChainSendKeyComp_eq {Γ}
    (ch : Expr (e2eOps ℓ P C K decT encT) Γ _)
    (epoch : Expr (e2eOps ℓ P C K decT encT) Γ _) :
    (spqrChainSendKeyComp I ch epoch).size =
      csizeHide (spqrChainSendKeyComp I ch epoch) (ch.size + epoch.size + 5000) :=
  csize_eq_hide (spqrChainSendKeyComp_size_le I ch epoch)

private theorem spqrListRevExpr_size_le {Γ} {t : Ty (e2eSig ℓ)} (cap : ℕ)
    (dflt : Expr (e2eOps ℓ P C K decT encT) Γ t)
    (l : Expr (e2eOps ℓ P C K decT encT) Γ (.list t)) :
    (spqrListRevExpr cap dflt l).size ≤ dflt.size + l.size + 3 * bits cap + 450 := by
  simp [spqrListRevExpr]; omega

@[local simp] private theorem size_spqrListRevExpr_eq {Γ} {t : Ty (e2eSig ℓ)} (cap : ℕ)
    (dflt : Expr (e2eOps ℓ P C K decT encT) Γ t)
    (l : Expr (e2eOps ℓ P C K decT encT) Γ (.list t)) :
    (spqrListRevExpr cap dflt l).size =
      esizeHide (spqrListRevExpr cap dflt l) (dflt.size + l.size + 3 * bits cap + 450) :=
  esize_eq_hide (spqrListRevExpr_size_le cap dflt l)

private theorem spqrPrevGetExpr_size_le {Γ}
    (entries : Expr (e2eOps ℓ P C K decT encT) Γ _)
    (tail : Expr (e2eOps ℓ P C K decT encT) Γ _)
    (atIdx curCtr maxOoo : Expr (e2eOps ℓ P C K decT encT) Γ _) :
    (spqrPrevGetExpr entries tail atIdx curCtr maxOoo).size ≤
      entries.size + tail.size + atIdx.size + curCtr.size + maxOoo.size + 2250 := by
  simp [spqrPrevGetExpr, spqrPrevGetFuelExpr, listGetExpr, listSetExpr]
  omega

@[local simp] private theorem size_spqrPrevGetExpr_eq {Γ}
    (entries : Expr (e2eOps ℓ P C K decT encT) Γ _)
    (tail : Expr (e2eOps ℓ P C K decT encT) Γ _)
    (atIdx curCtr maxOoo : Expr (e2eOps ℓ P C K decT encT) Γ _) :
    (spqrPrevGetExpr entries tail atIdx curCtr maxOoo).size =
      esizeHide (spqrPrevGetExpr entries tail atIdx curCtr maxOoo)
        (entries.size + tail.size + atIdx.size + curCtr.size + maxOoo.size + 2250) :=
  esize_eq_hide (spqrPrevGetExpr_size_le entries tail atIdx curCtr maxOoo)

private theorem spqrPrevGcExpr_size_le {Γ}
    (entries : Expr (e2eOps ℓ P C K decT encT) Γ _)
    (curKey maxOoo : Expr (e2eOps ℓ P C K decT encT) Γ _)
    (trimSize : Expr (e2eOps ℓ P C K decT encT) Γ .nat) :
    (spqrPrevGcExpr entries curKey maxOoo trimSize).size ≤
      entries.size + curKey.size + maxOoo.size + trimSize.size + 2500 := by
  simp [spqrPrevGcExpr, spqrPrevGcFuelExpr]
  omega

@[local simp] private theorem size_spqrPrevGcExpr_eq {Γ}
    (entries : Expr (e2eOps ℓ P C K decT encT) Γ _)
    (curKey maxOoo : Expr (e2eOps ℓ P C K decT encT) Γ _)
    (trimSize : Expr (e2eOps ℓ P C K decT encT) Γ .nat) :
    (spqrPrevGcExpr entries curKey maxOoo trimSize).size =
      esizeHide (spqrPrevGcExpr entries curKey maxOoo trimSize)
        (entries.size + curKey.size + maxOoo.size + trimSize.size + 2500) :=
  esize_eq_hide (spqrPrevGcExpr_size_le entries curKey maxOoo trimSize)

private theorem spqrKeyAdvanceComp_size_le {Γ}
    (ctr0 : Expr (e2eOps ℓ P C K decT encT) Γ _)
    (next0 : Expr (e2eOps ℓ P C K decT encT) Γ _)
    (entries0 : Expr (e2eOps ℓ P C K decT encT) Γ _)
    (atIdx maxOoo : Expr (e2eOps ℓ P C K decT encT) Γ _) :
    (spqrKeyAdvanceComp I ctr0 next0 entries0 atIdx maxOoo).size ≤
      ctr0.size + next0.size + entries0.size + atIdx.size + maxOoo.size + 3000 := by
  simp [spqrKeyAdvanceComp, spqrKeyAdvanceFuelComp, spqrKeyAdvanceStep]
  simp only [esizeHide_def, csizeHide_def]; omega

@[local simp] private theorem size_spqrKeyAdvanceComp_eq {Γ}
    (ctr0 : Expr (e2eOps ℓ P C K decT encT) Γ _)
    (next0 : Expr (e2eOps ℓ P C K decT encT) Γ _)
    (entries0 : Expr (e2eOps ℓ P C K decT encT) Γ _)
    (atIdx maxOoo : Expr (e2eOps ℓ P C K decT encT) Γ _) :
    (spqrKeyAdvanceComp I ctr0 next0 entries0 atIdx maxOoo).size =
      csizeHide (spqrKeyAdvanceComp I ctr0 next0 entries0 atIdx maxOoo)
        (ctr0.size + next0.size + entries0.size + atIdx.size + maxOoo.size + 3000) :=
  csize_eq_hide (spqrKeyAdvanceComp_size_le I ctr0 next0 entries0 atIdx maxOoo)

private theorem spqrDirKeyComp_size_le {Γ}
    (recvDir : Expr (e2eOps ℓ P C K decT encT) Γ _)
    (atIdx maxJump maxOoo : Expr (e2eOps ℓ P C K decT encT) Γ _)
    (trimSize : Expr (e2eOps ℓ P C K decT encT) Γ .nat) :
    (spqrDirKeyComp I recvDir atIdx maxJump maxOoo trimSize).size ≤
      recvDir.size + atIdx.size + maxJump.size + maxOoo.size + trimSize.size + 10000 := by
  simp [spqrDirKeyComp, spqrDirKeyFwdComp]
  simp only [esizeHide_def, csizeHide_def]; omega

@[local simp] private theorem size_spqrDirKeyComp_eq {Γ}
    (recvDir : Expr (e2eOps ℓ P C K decT encT) Γ _)
    (atIdx maxJump maxOoo : Expr (e2eOps ℓ P C K decT encT) Γ _)
    (trimSize : Expr (e2eOps ℓ P C K decT encT) Γ .nat) :
    (spqrDirKeyComp I recvDir atIdx maxJump maxOoo trimSize).size =
      csizeHide (spqrDirKeyComp I recvDir atIdx maxJump maxOoo trimSize)
        (recvDir.size + atIdx.size + maxJump.size + maxOoo.size + trimSize.size + 10000) :=
  csize_eq_hide (spqrDirKeyComp_size_le I recvDir atIdx maxJump maxOoo trimSize)

private theorem spqrChainRecvKeyComp_size_le {Γ}
    (ch : Expr (e2eOps ℓ P C K decT encT) Γ _)
    (epoch : Expr (e2eOps ℓ P C K decT encT) Γ _)
    (index : Expr (e2eOps ℓ P C K decT encT) Γ _) :
    (spqrChainRecvKeyComp I ch epoch index).size ≤
      ch.size + epoch.size + index.size + 14000 := by
  simp [spqrChainRecvKeyComp, spqrEpochIdxExpr, listGetExpr, listSetExpr]
  simp only [esizeHide_def, csizeHide_def]; omega

@[local simp] private theorem size_spqrChainRecvKeyComp_eq {Γ}
    (ch : Expr (e2eOps ℓ P C K decT encT) Γ _)
    (epoch : Expr (e2eOps ℓ P C K decT encT) Γ _)
    (index : Expr (e2eOps ℓ P C K decT encT) Γ _) :
    (spqrChainRecvKeyComp I ch epoch index).size =
      csizeHide (spqrChainRecvKeyComp I ch epoch index)
        (ch.size + epoch.size + index.size + 14000) :=
  csize_eq_hide (spqrChainRecvKeyComp_size_le I ch epoch index)

theorem spqrSendComp_size_le {Γ}
    (e : Expr (e2eOps ℓ P C K decT encT) Γ (.prod (B 32) BV512)) :
    (spqrSendComp I e).size ≤ e.size + 9000 := by
  simp [spqrSendComp, spqrRunSendChainComp, spqrResolveChainComp, spqrAddEpochOptComp]
  simp only [esizeHide_def, csizeHide_def]; omega

theorem spqrRecvComp_size_le {Γ}
    (e : Expr (e2eOps ℓ P C K decT encT) Γ (.prod (B 32) (B 32))) :
    (spqrRecvComp I e).size ≤ e.size + 38000 := by
  simp [spqrRecvComp, spqrRecvGreaterComp, spqrRecvPrepStateComp, spqrRecvV1BodyComp,
    spqrRunRecvChainComp, spqrResolveChainComp, spqrAddEpochOptComp]
  simp only [esizeHide_def, csizeHide_def]; omega

end SpqrInner

@[local simp] private theorem size_spqrSendComp_eq {ℓ : ℕ} {Pt : Type}
    {P : SignalPqxdh.Primitives} {C : Crypto} {K : MlKem}
    {decT : PublicKey → Option Pt} {encT : Pt → PublicKey}
    {ι : Type} {T : OracleSpec ι} (I : Iface (e2eSig ℓ) T) {Γ}
    (e : Expr (e2eOps ℓ P C K decT encT) Γ (.prod (B 32) BV512)) :
    (spqrSendComp I e).size = csizeHide (spqrSendComp I e) (e.size + 9000) :=
  csize_eq_hide (spqrSendComp_size_le I e)

@[local simp] private theorem size_spqrRecvComp_eq {ℓ : ℕ} {Pt : Type}
    {P : SignalPqxdh.Primitives} {C : Crypto} {K : MlKem}
    {decT : PublicKey → Option Pt} {encT : Pt → PublicKey}
    {ι : Type} {T : OracleSpec ι} (I : Iface (e2eSig ℓ) T) {Γ}
    (e : Expr (e2eOps ℓ P C K decT encT) Γ (.prod (B 32) (B 32))) :
    (spqrRecvComp I e).size = csizeHide (spqrRecvComp I e) (e.size + 38000) :=
  csize_eq_hide (spqrRecvComp_size_le I e)

section DrSendRecvSize

open CryptoGames.SM (sendsInE)
open CryptoVerification.LibsignalTripleRatchetRepr (uuidTryParse)
open CryptoVerification.E2E (serializedPartyAddresses)
open CryptoVerification.E2E.Costed (U32 PK IdKey drSenderChainT drRecvChainT ghostPartsT)
open Computational.Proofs.E2E.Dsl.SmReachInvParty (serializedPartyAddresses_length_le_128)
open Computational.Proofs.E2E.Dsl.DrSessionSimHooks (gpIsB gpVer gpLocId gpRemId gpRk gpPrevCtr
  gpPend gpEp gpCEps gpSc gpRcs gpPqSt gpMk optBytes32LitE sendAddrsE expectedAddrsE
  sessionVersionEffE drop1BE pushEvict5E getDZero5E findChainWithIdx5E replaceFirstChain5E
  takeSkippedFromListE advanceSingleChainC)
open Computational.Proofs.E2E.Dsl.DrSessionSimSend (drSendPreE drSendPostE drSendC)
open Computational.Proofs.E2E.Dsl.DrSessionSimRecv (drRecvOutT drRatchetMidT drChainActiveT
  drRecvPreE drRecvDhStepE drRecvChainSetupE drRecvTakeSkippedE drRecvAfterAdvE drRecvConsumeC
  drRecvFinishE drReceiveC)

variable {ℓ : ℕ} {Pt : Type} {P : SignalPqxdh.Primitives} {C : Crypto} {K : MlKem}
  {decT : PublicKey → Option Pt} {encT : Pt → PublicKey}

private theorem optBytes32LitE_size_le {Γ : List (Ty (e2eSig ℓ))} (opt : Option Bytes)
    (h : ∀ bs ∈ opt, bs.length ≤ 128) :
    (optBytes32LitE (ℓ := ℓ) (P := P) (C := C) (K := K) (decT := decT) (encT := encT)
      (Γ := Γ) opt).size ≤ 135 := by
  cases opt with
  | none => simp [optBytes32LitE]
  | some bs =>
    have hbs := h bs rfl
    simp [optBytes32LitE]; omega

private theorem sendAddrsE_size_le {Γ} (isB : Expr (e2eOps ℓ P C K decT encT) Γ .bool) :
    (sendAddrsE isB).size ≤ isB.size + 275 := by
  have hAB := optBytes32LitE_size_le (ℓ := ℓ) (P := P) (C := C) (K := K)
    (decT := decT) (encT := encT) (Γ := Γ)
    (serializedPartyAddresses uuidTryParse .A .B)
    (serializedPartyAddresses_length_le_128 uuidTryParse .A .B)
  have hBA := optBytes32LitE_size_le (ℓ := ℓ) (P := P) (C := C) (K := K)
    (decT := decT) (encT := encT) (Γ := Γ)
    (serializedPartyAddresses uuidTryParse .B .A)
    (serializedPartyAddresses_length_le_128 uuidTryParse .B .A)
  dsimp only [sendAddrsE, Expr.size]
  omega

@[local simp] private theorem size_sendAddrsE_eq {Γ}
    (isB : Expr (e2eOps ℓ P C K decT encT) Γ .bool) :
    (sendAddrsE isB).size = esizeHide (sendAddrsE isB) (isB.size + 275) :=
  esize_eq_hide (sendAddrsE_size_le isB)

private theorem expectedAddrsE_size_le {Γ} (isB : Expr (e2eOps ℓ P C K decT encT) Γ .bool) :
    (expectedAddrsE isB).size ≤ isB.size + 275 := by
  have hAB := optBytes32LitE_size_le (ℓ := ℓ) (P := P) (C := C) (K := K)
    (decT := decT) (encT := encT) (Γ := Γ)
    (serializedPartyAddresses uuidTryParse .A .B)
    (serializedPartyAddresses_length_le_128 uuidTryParse .A .B)
  have hBA := optBytes32LitE_size_le (ℓ := ℓ) (P := P) (C := C) (K := K)
    (decT := decT) (encT := encT) (Γ := Γ)
    (serializedPartyAddresses uuidTryParse .B .A)
    (serializedPartyAddresses_length_le_128 uuidTryParse .B .A)
  dsimp only [expectedAddrsE, Expr.size]
  omega

@[local simp] private theorem size_expectedAddrsE_eq {Γ}
    (isB : Expr (e2eOps ℓ P C K decT encT) Γ .bool) :
    (expectedAddrsE isB).size = esizeHide (expectedAddrsE isB) (isB.size + 275) :=
  esize_eq_hide (expectedAddrsE_size_le isB)

private theorem sessionVersionEffE_size_le {Γ} (ver : Expr (e2eOps ℓ P C K decT encT) Γ U32) :
    (sessionVersionEffE ver).size ≤ ver.size + 25 := by
  simp [sessionVersionEffE]

@[local simp] private theorem size_sessionVersionEffE_eq {Γ}
    (ver : Expr (e2eOps ℓ P C K decT encT) Γ U32) :
    (sessionVersionEffE ver).size = esizeHide (sessionVersionEffE ver) (ver.size + 25) :=
  esize_eq_hide (sessionVersionEffE_size_le ver)

private theorem pushEvict5E_size_le {O' : Ops (e2eSig ℓ)} {Γ t}
    (xs : Expr O' Γ (.list t)) (x : Expr O' Γ t) :
    (pushEvict5E xs x).size ≤ xs.size + x.size + 60 := by
  simp [pushEvict5E, drop1BE]

@[local simp] private theorem size_pushEvict5E_eq {O' : Ops (e2eSig ℓ)} {Γ t}
    (xs : Expr O' Γ (.list t)) (x : Expr O' Γ t) :
    (pushEvict5E xs x).size = esizeHide (pushEvict5E xs x) (xs.size + x.size + 60) :=
  esize_eq_hide (pushEvict5E_size_le xs x)

private theorem getDZero5E_size_le {O' : Ops (e2eSig ℓ)} {Γ}
    (cEps : Expr O' Γ (.list .nat)) (idx : Expr O' Γ .nat) :
    (getDZero5E cEps idx).size ≤ cEps.size + idx.size + 60 := by
  simp [getDZero5E]

@[local simp] private theorem size_getDZero5E_eq {O' : Ops (e2eSig ℓ)} {Γ}
    (cEps : Expr O' Γ (.list .nat)) (idx : Expr O' Γ .nat) :
    (getDZero5E cEps idx).size = esizeHide (getDZero5E cEps idx) (cEps.size + idx.size + 60) :=
  esize_eq_hide (getDZero5E_size_le cEps idx)

private theorem findChainWithIdx5E_size_le {Γ}
    (rcs : Expr (e2eOps ℓ P C K decT encT) Γ _)
    (their : Expr (e2eOps ℓ P C K decT encT) Γ _) :
    (findChainWithIdx5E rcs their).size ≤ rcs.size + their.size + 60 := by
  simp [findChainWithIdx5E]

@[local simp] private theorem size_findChainWithIdx5E_eq {Γ}
    (rcs : Expr (e2eOps ℓ P C K decT encT) Γ _)
    (their : Expr (e2eOps ℓ P C K decT encT) Γ _) :
    (findChainWithIdx5E rcs their).size =
      esizeHide (findChainWithIdx5E rcs their) (rcs.size + their.size + 60) :=
  esize_eq_hide (findChainWithIdx5E_size_le rcs their)

private theorem replaceFirstChain5E_size_le {Γ}
    (rcs : Expr (e2eOps ℓ P C K decT encT) Γ _)
    (their : Expr (e2eOps ℓ P C K decT encT) Γ _)
    (newRc : Expr (e2eOps ℓ P C K decT encT) Γ _) :
    (replaceFirstChain5E rcs their newRc).size ≤ rcs.size + their.size + newRc.size + 80 := by
  simp [replaceFirstChain5E]; omega

@[local simp] private theorem size_replaceFirstChain5E_eq {Γ}
    (rcs : Expr (e2eOps ℓ P C K decT encT) Γ _)
    (their : Expr (e2eOps ℓ P C K decT encT) Γ _)
    (newRc : Expr (e2eOps ℓ P C K decT encT) Γ _) :
    (replaceFirstChain5E rcs their newRc).size =
      esizeHide (replaceFirstChain5E rcs their newRc) (rcs.size + their.size + newRc.size + 80) :=
  esize_eq_hide (replaceFirstChain5E_size_le rcs their newRc)

private theorem takeSkippedFromListE_size_le {Γ}
    (mks : Expr (e2eOps ℓ P C K decT encT) Γ _)
    (targetCtr : Expr (e2eOps ℓ P C K decT encT) Γ _) :
    (takeSkippedFromListE mks targetCtr).size ≤ mks.size + targetCtr.size + 100 := by
  simp [takeSkippedFromListE]

@[local simp] private theorem size_takeSkippedFromListE_eq {Γ}
    (mks : Expr (e2eOps ℓ P C K decT encT) Γ _)
    (targetCtr : Expr (e2eOps ℓ P C K decT encT) Γ _) :
    (takeSkippedFromListE mks targetCtr).size =
      esizeHide (takeSkippedFromListE mks targetCtr) (mks.size + targetCtr.size + 100) :=
  esize_eq_hide (takeSkippedFromListE_size_le mks targetCtr)

private theorem advanceSingleChainC_size_le {ι : Type} {T : OracleSpec ι}
    (I : Iface (e2eSig ℓ) T) {Γ}
    (ckInit : Expr (e2eOps ℓ P C K decT encT) Γ _)
    (mksInit : Expr (e2eOps ℓ P C K decT encT) Γ _)
    (targetCtr : Expr (e2eOps ℓ P C K decT encT) Γ _) :
    (advanceSingleChainC I ckInit mksInit targetCtr).size ≤
      ckInit.size + mksInit.size + targetCtr.size + 120 := by
  simp [advanceSingleChainC]; omega

@[local simp] private theorem size_advanceSingleChainC_eq {ι : Type} {T : OracleSpec ι}
    (I : Iface (e2eSig ℓ) T) {Γ}
    (ckInit : Expr (e2eOps ℓ P C K decT encT) Γ _)
    (mksInit : Expr (e2eOps ℓ P C K decT encT) Γ _)
    (targetCtr : Expr (e2eOps ℓ P C K decT encT) Γ _) :
    (advanceSingleChainC I ckInit mksInit targetCtr).size =
      csizeHide (advanceSingleChainC I ckInit mksInit targetCtr)
        (ckInit.size + mksInit.size + targetCtr.size + 120) :=
  csize_eq_hide (advanceSingleChainC_size_le I ckInit mksInit targetCtr)

private theorem drSendPreE_size_le {Γ}
    (gE : Expr (e2eOps ℓ P C K decT encT) Γ GhostStT) :
    (drSendPreE gE).size ≤ gE.size + 80 := by
  simp [drSendPreE, gpSc, gpVer, gpRemId]
  simp only [esizeHide_def]; omega

@[local simp] private theorem size_drSendPreE_eq {Γ}
    (gE : Expr (e2eOps ℓ P C K decT encT) Γ GhostStT) :
    (drSendPreE gE).size = esizeHide (drSendPreE gE) (gE.size + 80) :=
  esize_eq_hide (drSendPreE_size_le gE)

private theorem drSendPostE_size_le {Γ}
    (gE : Expr (e2eOps ℓ P C K decT encT) Γ _)
    (mE : Expr (e2eOps ℓ P C K decT encT) Γ _)
    (partsE : Expr (e2eOps ℓ P C K decT encT) Γ _)
    (scE : Expr (e2eOps ℓ P C K decT encT) Γ _)
    (remIdE : Expr (e2eOps ℓ P C K decT encT) Γ _)
    (pqOutE : Expr (e2eOps ℓ P C K decT encT) Γ _) :
    (drSendPostE gE mE partsE scE remIdE pqOutE).size ≤
      gE.size + mE.size + partsE.size + scE.size + remIdE.size + pqOutE.size + 600 := by
  simp [drSendPostE, sendsInE, gpIsB, gpVer, gpLocId, gpRemId, gpRk, gpPrevCtr, gpPend,
    gpEp, gpCEps, gpRcs, gpMk]
  simp only [esizeHide_def]; omega

@[local simp] private theorem size_drSendPostE_eq {Γ}
    (gE : Expr (e2eOps ℓ P C K decT encT) Γ _)
    (mE : Expr (e2eOps ℓ P C K decT encT) Γ _)
    (partsE : Expr (e2eOps ℓ P C K decT encT) Γ _)
    (scE : Expr (e2eOps ℓ P C K decT encT) Γ _)
    (remIdE : Expr (e2eOps ℓ P C K decT encT) Γ _)
    (pqOutE : Expr (e2eOps ℓ P C K decT encT) Γ _) :
    (drSendPostE gE mE partsE scE remIdE pqOutE).size =
      esizeHide (drSendPostE gE mE partsE scE remIdE pqOutE)
        (gE.size + mE.size + partsE.size + scE.size + remIdE.size + pqOutE.size + 600) :=
  esize_eq_hide (drSendPostE_size_le gE mE partsE scE remIdE pqOutE)

theorem size_drSendC_le {ι : Type} {T : OracleSpec ι} (I : Iface (e2eSig ℓ) T) {Γ}
    (e : Expr (e2eOps ℓ P C K decT encT) Γ (.prod GhostStT (.prod PlainT BV512))) :
    (drSendC (spqrDslHooks ℓ (Pt := Pt) P C K decT encT) I e).size ≤ e.size + 10000 := by
  simp [drSendC, spqrDslHooks, gpPqSt]
  simp only [esizeHide_def, csizeHide_def]; omega

@[local simp] private theorem size_drSendC_eq {ι : Type} {T : OracleSpec ι}
    (I : Iface (e2eSig ℓ) T) {Γ}
    (e : Expr (e2eOps ℓ P C K decT encT) Γ (.prod GhostStT (.prod PlainT BV512))) :
    (drSendC (spqrDslHooks ℓ (Pt := Pt) P C K decT encT) I e).size =
      csizeHide (drSendC (spqrDslHooks ℓ (Pt := Pt) P C K decT encT) I e) (e.size + 10000) :=
  csize_eq_hide (size_drSendC_le I e)

private theorem drRecvPreE_size_le {Γ}
    (gE : Expr (e2eOps ℓ P C K decT encT) Γ GhostStT)
    (cE : Expr (e2eOps ℓ P C K decT encT) Γ (B 32)) :
    (drRecvPreE gE cE).size ≤ gE.size + cE.size + 120 := by
  simp [drRecvPreE, gpVer, gpRemId]
  simp only [esizeHide_def]; omega

@[local simp] private theorem size_drRecvPreE_eq {Γ}
    (gE : Expr (e2eOps ℓ P C K decT encT) Γ GhostStT)
    (cE : Expr (e2eOps ℓ P C K decT encT) Γ (B 32)) :
    (drRecvPreE gE cE).size = esizeHide (drRecvPreE gE cE) (gE.size + cE.size + 120) :=
  esize_eq_hide (drRecvPreE_size_le gE cE)

private theorem drRecvDhStepE_size_le {Γ}
    (partsE : Expr (e2eOps ℓ P C K decT encT) Γ _)
    (theirE : Expr (e2eOps ℓ P C K decT encT) Γ _)
    (rcCoinsE : Expr (e2eOps ℓ P C K decT encT) Γ _) :
    (drRecvDhStepE partsE theirE rcCoinsE).size ≤
      partsE.size + theirE.size + rcCoinsE.size + 450 := by
  simp [drRecvDhStepE, gpSc, gpRk, gpRcs, gpEp, gpCEps]
  simp only [esizeHide_def]; omega

@[local simp] private theorem size_drRecvDhStepE_eq {Γ}
    (partsE : Expr (e2eOps ℓ P C K decT encT) Γ _)
    (theirE : Expr (e2eOps ℓ P C K decT encT) Γ _)
    (rcCoinsE : Expr (e2eOps ℓ P C K decT encT) Γ _) :
    (drRecvDhStepE partsE theirE rcCoinsE).size =
      esizeHide (drRecvDhStepE partsE theirE rcCoinsE)
        (partsE.size + theirE.size + rcCoinsE.size + 450) :=
  esize_eq_hide (drRecvDhStepE_size_le partsE theirE rcCoinsE)

private theorem drRecvChainSetupE_size_le {Γ}
    (partsE : Expr (e2eOps ℓ P C K decT encT) Γ _)
    (theirE : Expr (e2eOps ℓ P C K decT encT) Γ _)
    (rcCoinsE : Expr (e2eOps ℓ P C K decT encT) Γ _) :
    (drRecvChainSetupE partsE theirE rcCoinsE).size ≤
      partsE.size + theirE.size + rcCoinsE.size + 800 := by
  simp [drRecvChainSetupE, gpRk, gpPrevCtr, gpSc, gpRcs, gpEp, gpCEps]
  simp only [esizeHide_def]; omega

@[local simp] private theorem size_drRecvChainSetupE_eq {Γ}
    (partsE : Expr (e2eOps ℓ P C K decT encT) Γ _)
    (theirE : Expr (e2eOps ℓ P C K decT encT) Γ _)
    (rcCoinsE : Expr (e2eOps ℓ P C K decT encT) Γ _) :
    (drRecvChainSetupE partsE theirE rcCoinsE).size =
      esizeHide (drRecvChainSetupE partsE theirE rcCoinsE)
        (partsE.size + theirE.size + rcCoinsE.size + 800) :=
  esize_eq_hide (drRecvChainSetupE_size_le partsE theirE rcCoinsE)

private theorem drRecvTakeSkippedE_size_le {Γ}
    (theirE : Expr (e2eOps ℓ P C K decT encT) Γ _)
    (msgCtrE : Expr (e2eOps ℓ P C K decT encT) Γ _)
    (rcs1E : Expr (e2eOps ℓ P C K decT encT) Γ _)
    (activeE : Expr (e2eOps ℓ P C K decT encT) Γ _) :
    (drRecvTakeSkippedE theirE msgCtrE rcs1E activeE).size ≤
      theirE.size + msgCtrE.size + rcs1E.size + activeE.size + 300 := by
  simp [drRecvTakeSkippedE]
  simp only [esizeHide_def]; omega

@[local simp] private theorem size_drRecvTakeSkippedE_eq {Γ}
    (theirE : Expr (e2eOps ℓ P C K decT encT) Γ _)
    (msgCtrE : Expr (e2eOps ℓ P C K decT encT) Γ _)
    (rcs1E : Expr (e2eOps ℓ P C K decT encT) Γ _)
    (activeE : Expr (e2eOps ℓ P C K decT encT) Γ _) :
    (drRecvTakeSkippedE theirE msgCtrE rcs1E activeE).size =
      esizeHide (drRecvTakeSkippedE theirE msgCtrE rcs1E activeE)
        (theirE.size + msgCtrE.size + rcs1E.size + activeE.size + 300) :=
  esize_eq_hide (drRecvTakeSkippedE_size_le theirE msgCtrE rcs1E activeE)

private theorem drRecvAfterAdvE_size_le {Γ}
    (theirE : Expr (e2eOps ℓ P C K decT encT) Γ _)
    (rcs1E : Expr (e2eOps ℓ P C K decT encT) Γ _)
    (advPairE : Expr (e2eOps ℓ P C K decT encT) Γ _) :
    (drRecvAfterAdvE theirE rcs1E advPairE).size ≤
      theirE.size + rcs1E.size + advPairE.size + 200 := by
  simp [drRecvAfterAdvE]
  simp only [esizeHide_def]; omega

@[local simp] private theorem size_drRecvAfterAdvE_eq {Γ}
    (theirE : Expr (e2eOps ℓ P C K decT encT) Γ _)
    (rcs1E : Expr (e2eOps ℓ P C K decT encT) Γ _)
    (advPairE : Expr (e2eOps ℓ P C K decT encT) Γ _) :
    (drRecvAfterAdvE theirE rcs1E advPairE).size =
      esizeHide (drRecvAfterAdvE theirE rcs1E advPairE)
        (theirE.size + rcs1E.size + advPairE.size + 200) :=
  esize_eq_hide (drRecvAfterAdvE_size_le theirE rcs1E advPairE)

private theorem drRecvConsumeC_size_le {ι : Type} {T : OracleSpec ι}
    (I : Iface (e2eSig ℓ) T) {Γ}
    (theirE : Expr (e2eOps ℓ P C K decT encT) Γ _)
    (msgCtrE : Expr (e2eOps ℓ P C K decT encT) Γ _)
    (rcs1E : Expr (e2eOps ℓ P C K decT encT) Γ _)
    (activeE : Expr (e2eOps ℓ P C K decT encT) Γ _) :
    (drRecvConsumeC I theirE msgCtrE rcs1E activeE).size ≤
      theirE.size + msgCtrE.size + rcs1E.size + activeE.size + 800 := by
  simp [drRecvConsumeC]
  simp only [esizeHide_def, csizeHide_def]; omega

@[local simp] private theorem size_drRecvConsumeC_eq {ι : Type} {T : OracleSpec ι}
    (I : Iface (e2eSig ℓ) T) {Γ}
    (theirE : Expr (e2eOps ℓ P C K decT encT) Γ _)
    (msgCtrE : Expr (e2eOps ℓ P C K decT encT) Γ _)
    (rcs1E : Expr (e2eOps ℓ P C K decT encT) Γ _)
    (activeE : Expr (e2eOps ℓ P C K decT encT) Γ _) :
    (drRecvConsumeC I theirE msgCtrE rcs1E activeE).size =
      csizeHide (drRecvConsumeC I theirE msgCtrE rcs1E activeE)
        (theirE.size + msgCtrE.size + rcs1E.size + activeE.size + 800) :=
  csize_eq_hide (drRecvConsumeC_size_le I theirE msgCtrE rcs1E activeE)

private theorem drRecvFinishE_size_le {Γ}
    (cE : Expr (e2eOps ℓ P C K decT encT) Γ _)
    (partsE : Expr (e2eOps ℓ P C K decT encT) Γ _)
    (remIdE : Expr (e2eOps ℓ P C K decT encT) Γ _)
    (msgCtrE : Expr (e2eOps ℓ P C K decT encT) Γ _)
    (msgCtE : Expr (e2eOps ℓ P C K decT encT) Γ _)
    (midE : Expr (e2eOps ℓ P C K decT encT) Γ _)
    (consOutE : Expr (e2eOps ℓ P C K decT encT) Γ _)
    (pqOutE : Expr (e2eOps ℓ P C K decT encT) Γ _) :
    (drRecvFinishE cE partsE remIdE msgCtrE msgCtE midE consOutE pqOutE).size ≤
      cE.size + partsE.size + remIdE.size + msgCtrE.size + msgCtE.size +
        midE.size + consOutE.size + pqOutE.size + 500 := by
  simp [drRecvFinishE, gpIsB, gpVer, gpLocId, gpRemId, gpMk]
  simp only [esizeHide_def]; omega

@[local simp] private theorem size_drRecvFinishE_eq {Γ}
    (cE : Expr (e2eOps ℓ P C K decT encT) Γ _)
    (partsE : Expr (e2eOps ℓ P C K decT encT) Γ _)
    (remIdE : Expr (e2eOps ℓ P C K decT encT) Γ _)
    (msgCtrE : Expr (e2eOps ℓ P C K decT encT) Γ _)
    (msgCtE : Expr (e2eOps ℓ P C K decT encT) Γ _)
    (midE : Expr (e2eOps ℓ P C K decT encT) Γ _)
    (consOutE : Expr (e2eOps ℓ P C K decT encT) Γ _)
    (pqOutE : Expr (e2eOps ℓ P C K decT encT) Γ _) :
    (drRecvFinishE cE partsE remIdE msgCtrE msgCtE midE consOutE pqOutE).size =
      esizeHide (drRecvFinishE cE partsE remIdE msgCtrE msgCtE midE consOutE pqOutE)
        (cE.size + partsE.size + remIdE.size + msgCtrE.size + msgCtE.size +
          midE.size + consOutE.size + pqOutE.size + 500) :=
  esize_eq_hide (drRecvFinishE_size_le cE partsE remIdE msgCtrE msgCtE midE consOutE pqOutE)

theorem size_drReceiveC_le {ι : Type} {T : OracleSpec ι} (I : Iface (e2eSig ℓ) T) {Γ}
    (e : Expr (e2eOps ℓ P C K decT encT) Γ
      (.prod GhostStT (.prod (B 32) CryptoVerification.E2E.Costed.BV256))) :
    (drReceiveC (spqrDslHooks ℓ (Pt := Pt) P C K decT encT) I e).size ≤ e.size + 41000 := by
  simp [drReceiveC, spqrDslHooks, gpPqSt]
  simp only [esizeHide_def, csizeHide_def]; omega

@[local simp] private theorem size_drReceiveC_eq {ι : Type} {T : OracleSpec ι}
    (I : Iface (e2eSig ℓ) T) {Γ}
    (e : Expr (e2eOps ℓ P C K decT encT) Γ
      (.prod GhostStT (.prod (B 32) CryptoVerification.E2E.Costed.BV256))) :
    (drReceiveC (spqrDslHooks ℓ (Pt := Pt) P C K decT encT) I e).size =
      csizeHide (drReceiveC (spqrDslHooks ℓ (Pt := Pt) P C K decT encT) I e) (e.size + 41000) :=
  csize_eq_hide (size_drReceiveC_le I e)

open CryptoGames.SM (posTy posSender posEpoch posIdx posEq leN maxN minN isSomeE otherE pSet
  maxAccGet maxAccSet healedByE maxOptE)
open CryptoVerification.E2E.Costed (recvResultT)
open Computational.Proofs.E2E.Dsl.DrSessionSimBookkeeping (bytesEqE ratchetKeyAdmissibleE
  recvResultRejE recvResultAccE smRWireE smRRecvE e2eRecTy e2eRecPos e2eRecMsg e2eRecCt e2eRecComp
  e2eRecMk e2eGsIdx e2eGsTL e2eGsTrans e2eGsChall e2eGsComp e2eGsMaxAcc e2eGsLeaks e2eGsCorrs
  e2eGsMk e2eInitGsE e2eGsSetWin e2eSafeChE e2eSafeInjE e2eLeakE e2eEpMgmtE e2eCompContainsE
  e2eChallContainsE e2eRecordE e2eDeleteE e2eAcceptE e2eTrivialE e2eSendOKE e2eCorrOKE
  e2eInTransitE)
open Computational.Proofs.E2E.Dsl.DrSessionSim (mkE2ECoinSamplers e2eSamIfNec512C)

@[local simp] private theorem size_bytesEqE {Γ}
    (a b : Expr (e2eOps ℓ P C K decT encT) Γ (B 32)) :
    (bytesEqE a b).size = a.size + b.size + 2 := by
  simp [bytesEqE]

@[local simp] private theorem size_ratchetKeyAdmissibleE {Γ}
    (c : Expr (e2eOps ℓ P C K decT encT) Γ (B 32)) :
    (ratchetKeyAdmissibleE c).size = c.size + 1 := by
  simp [ratchetKeyAdmissibleE]

@[simp] theorem size_recvResultRejE {O' : Ops (e2eSig ℓ)} {Γ} :
    (recvResultRejE (ℓ := ℓ) (O' := O') (Γ := Γ)).size = 2 := rfl

@[simp] theorem size_recvResultAccE {O' : Ops (e2eSig ℓ)} {Γ}
    (t i : Expr O' Γ .nat) (m? : Expr O' Γ (.opt PlainT)) :
    (recvResultAccE t i m?).size = t.size + i.size + m?.size + 3 := by
  simp [recvResultAccE]; omega

@[simp] theorem size_smRWireE {O' : Ops (e2eSig ℓ)} {stT : Ty (e2eSig ℓ)} {Γ}
    (w? : Expr O' Γ (.opt (B 32))) :
    (smRWireE (stT := stT) w?).size = w?.size + 4 := by
  simp [smRWireE]

@[simp] theorem size_smRRecvE {O' : Ops (e2eSig ℓ)} {stT : Ty (e2eSig ℓ)} {Γ}
    (rr? : Expr O' Γ (.opt recvResultT)) :
    (smRRecvE (stT := stT) rr?).size = rr?.size + 4 := by
  simp [smRRecvE]; omega

@[simp] theorem size_smRCorrE {O' : Ops (e2eSig ℓ)} {stT : Ty (e2eSig ℓ)} {Γ}
    (st? : Expr O' Γ (.opt stT)) :
    (smRCorrE st?).size = st?.size + 4 := by
  simp [smRCorrE]; omega

theorem size_e2eInitGsE_le {O' : Ops (e2eSig ℓ)} {Γ}
    (stA stB : Expr O' Γ GhostStT) (b : Expr O' Γ .bool) :
    (e2eInitGsE stA stB b).size ≤ stA.size + stB.size + b.size + 40 := by
  simp [e2eInitGsE, e2eGsMk]; omega

theorem size_e2eGsSetWin_le {O' : Ops (e2eSig ℓ)} {Γ}
    (s : Expr O' Γ (e2eGsTy ℓ)) (w : Expr O' Γ .bool) :
    (e2eGsSetWin s w).size ≤ s.size + w.size + 150 := by
  simp [e2eGsSetWin, e2eGsMk, e2eGsSt, e2eGsB, e2eGsEpoch, e2eGsIdx, e2eGsTL, e2eGsTrans,
    e2eGsChall, e2eGsComp, e2eGsMaxAcc, e2eGsLeaks, e2eGsCorrs]

@[local simp] private theorem size_e2eGsSetWin_eq {O' : Ops (e2eSig ℓ)} {Γ}
    (s : Expr O' Γ (e2eGsTy ℓ)) (w : Expr O' Γ .bool) :
    (e2eGsSetWin s w).size = esizeHide (e2eGsSetWin s w) (s.size + w.size + 150) :=
  esize_eq_hide (size_e2eGsSetWin_le s w)

theorem size_e2eSafeChE_le {O' : Ops (e2eSig ℓ)} {Γ} (Δ : ℕ)
    (s : Expr O' Γ (e2eGsTy ℓ)) (p : Expr O' Γ .bool) :
    (e2eSafeChE Δ s p).size ≤ s.size + p.size + bits Δ + 60 := by
  simp [e2eSafeChE, healedByE, leN, e2eGsTL, e2eGsEpoch, pGet]; omega

@[local simp] private theorem size_e2eSafeChE_eq {O' : Ops (e2eSig ℓ)} {Γ} (Δ : ℕ)
    (s : Expr O' Γ (e2eGsTy ℓ)) (p : Expr O' Γ .bool) :
    (e2eSafeChE Δ s p).size = esizeHide (e2eSafeChE Δ s p) (s.size + p.size + bits Δ + 60) :=
  esize_eq_hide (size_e2eSafeChE_le Δ s p)

theorem size_e2eSafeInjE_le {O' : Ops (e2eSig ℓ)} {Γ} (Δ : ℕ)
    (s : Expr O' Γ (e2eGsTy ℓ)) :
    (e2eSafeInjE Δ s).size ≤ s.size + bits Δ + 60 := by
  simp [e2eSafeInjE, healedByE, leN, minN, e2eGsTL, e2eGsEpoch]; omega

@[local simp] private theorem size_e2eSafeInjE_eq {O' : Ops (e2eSig ℓ)} {Γ} (Δ : ℕ)
    (s : Expr O' Γ (e2eGsTy ℓ)) :
    (e2eSafeInjE Δ s).size = esizeHide (e2eSafeInjE Δ s) (s.size + bits Δ + 60) :=
  esize_eq_hide (size_e2eSafeInjE_le Δ s)

theorem size_e2eLeakE_le {O' : Ops (e2eSig ℓ)} {Γ}
    (s : Expr O' Γ (e2eGsTy ℓ)) (l : Expr O' Γ .nat) :
    (e2eLeakE s l).size ≤ s.size + l.size + 200 := by
  simp [e2eLeakE, maxOptE, maxN, leN, e2eGsMk, e2eGsSt, e2eGsB, e2eGsWin, e2eGsEpoch,
    e2eGsIdx, e2eGsTL, e2eGsTrans, e2eGsChall, e2eGsComp, e2eGsMaxAcc, e2eGsLeaks, e2eGsCorrs]

@[local simp] private theorem size_e2eLeakE_eq {O' : Ops (e2eSig ℓ)} {Γ}
    (s : Expr O' Γ (e2eGsTy ℓ)) (l : Expr O' Γ .nat) :
    (e2eLeakE s l).size = esizeHide (e2eLeakE s l) (s.size + l.size + 200) :=
  esize_eq_hide (size_e2eLeakE_le s l)

theorem size_e2eEpMgmtE_le {O' : Ops (e2eSig ℓ)} {Γ} (Δ qep : ℕ)
    (s : Expr O' Γ (e2eGsTy ℓ)) (p bad : Expr O' Γ .bool) :
    (e2eEpMgmtE Δ qep s p bad).size ≤
      s.size + p.size + bad.size + bits Δ + 2 * bits qep + 600 := by
  simp [e2eEpMgmtE, sendsInE, pGet, pSet, e2eGsMk, e2eGsSt, e2eGsB, e2eGsWin, e2eGsEpoch,
    e2eGsIdx, e2eGsTL, e2eGsTrans, e2eGsChall, e2eGsComp, e2eGsMaxAcc, e2eGsLeaks, e2eGsCorrs]
  simp only [esizeHide_def]; omega

@[local simp] private theorem size_e2eEpMgmtE_eq {O' : Ops (e2eSig ℓ)} {Γ} (Δ qep : ℕ)
    (s : Expr O' Γ (e2eGsTy ℓ)) (p bad : Expr O' Γ .bool) :
    (e2eEpMgmtE Δ qep s p bad).size =
      esizeHide (e2eEpMgmtE Δ qep s p bad)
        (s.size + p.size + bad.size + bits Δ + 2 * bits qep + 600) :=
  esize_eq_hide (size_e2eEpMgmtE_le Δ qep s p bad)

theorem size_e2eCompContainsE_le {O' : Ops (e2eSig ℓ)} {Γ} (q : ℕ)
    (s : Expr O' Γ (e2eGsTy ℓ)) (pos : Expr O' Γ posTy) :
    (e2eCompContainsE q s pos).size ≤ s.size + pos.size + bits q + 50 := by
  simp [e2eCompContainsE, e2eGsComp, posEq, posSender, posEpoch, posIdx, boolEq]; omega

@[local simp] private theorem size_e2eCompContainsE_eq {O' : Ops (e2eSig ℓ)} {Γ} (q : ℕ)
    (s : Expr O' Γ (e2eGsTy ℓ)) (pos : Expr O' Γ posTy) :
    (e2eCompContainsE q s pos).size =
      esizeHide (e2eCompContainsE q s pos) (s.size + pos.size + bits q + 50) :=
  esize_eq_hide (size_e2eCompContainsE_le q s pos)

theorem size_e2eChallContainsE_le {O' : Ops (e2eSig ℓ)} {Γ} (q : ℕ)
    (s : Expr O' Γ (e2eGsTy ℓ)) (pos : Expr O' Γ posTy) :
    (e2eChallContainsE q s pos).size ≤ s.size + pos.size + bits q + 50 := by
  simp [e2eChallContainsE, e2eGsChall, posEq, posSender, posEpoch, posIdx, boolEq]; omega

@[local simp] private theorem size_e2eChallContainsE_eq {O' : Ops (e2eSig ℓ)} {Γ} (q : ℕ)
    (s : Expr O' Γ (e2eGsTy ℓ)) (pos : Expr O' Γ posTy) :
    (e2eChallContainsE q s pos).size =
      esizeHide (e2eChallContainsE q s pos) (s.size + pos.size + bits q + 50) :=
  esize_eq_hide (size_e2eChallContainsE_le q s pos)

theorem size_e2eRecordE_le {O' : Ops (e2eSig ℓ)} {Γ} (q Δ : ℕ)
    (s : Expr O' Γ (e2eGsTy ℓ)) (p : Expr O' Γ .bool) (st' : Expr O' Γ GhostStT)
    (pos : Expr O' Γ posTy) (msg : Expr O' Γ PlainT) (ct : Expr O' Γ (B 32))
    (isChall : Expr O' Γ .bool) :
    (e2eRecordE q Δ s p st' pos msg ct isChall).size ≤
      s.size + p.size + st'.size + pos.size + msg.size + ct.size + isChall.size +
        2 * bits q + bits Δ + 500 := by
  simp [e2eRecordE, e2eGsMk, e2eRecMk, e2eRecPos, e2eRecMsg, e2eRecCt, e2eRecComp,
    e2eGsSt, e2eGsB, e2eGsWin, e2eGsEpoch, e2eGsIdx, e2eGsTL, e2eGsTrans, e2eGsChall, e2eGsComp,
    e2eGsMaxAcc, e2eGsLeaks, e2eGsCorrs, pSet, pGet, posEq, posSender, posEpoch, posIdx,
    boolEq, orE]
  simp only [esizeHide_def]; omega

@[local simp] private theorem size_e2eRecordE_eq {O' : Ops (e2eSig ℓ)} {Γ} (q Δ : ℕ)
    (s : Expr O' Γ (e2eGsTy ℓ)) (p : Expr O' Γ .bool) (st' : Expr O' Γ GhostStT)
    (pos : Expr O' Γ posTy) (msg : Expr O' Γ PlainT) (ct : Expr O' Γ (B 32))
    (isChall : Expr O' Γ .bool) :
    (e2eRecordE q Δ s p st' pos msg ct isChall).size =
      esizeHide (e2eRecordE q Δ s p st' pos msg ct isChall)
        (s.size + p.size + st'.size + pos.size + msg.size + ct.size + isChall.size +
          2 * bits q + bits Δ + 500) :=
  esize_eq_hide (size_e2eRecordE_le q Δ s p st' pos msg ct isChall)

theorem size_e2eDeleteE_le {O' : Ops (e2eSig ℓ)} {Γ} (q : ℕ)
    (s : Expr O' Γ (e2eGsTy ℓ)) (pos : Expr O' Γ posTy) :
    (e2eDeleteE q s pos).size ≤ s.size + pos.size + 3 * bits q + 250 := by
  simp [e2eDeleteE, e2eGsMk, e2eRecPos, e2eGsSt, e2eGsB, e2eGsWin, e2eGsEpoch, e2eGsIdx,
    e2eGsTL, e2eGsTrans, e2eGsChall, e2eGsComp, e2eGsMaxAcc, e2eGsLeaks, e2eGsCorrs, posEq,
    posSender, posEpoch, posIdx, boolEq]
  omega

@[local simp] private theorem size_e2eDeleteE_eq {O' : Ops (e2eSig ℓ)} {Γ} (q : ℕ)
    (s : Expr O' Γ (e2eGsTy ℓ)) (pos : Expr O' Γ posTy) :
    (e2eDeleteE q s pos).size =
      esizeHide (e2eDeleteE q s pos) (s.size + pos.size + 3 * bits q + 250) :=
  esize_eq_hide (size_e2eDeleteE_le q s pos)

theorem size_e2eAcceptE_le {O' : Ops (e2eSig ℓ)} {Γ} (q : ℕ)
    (s : Expr O' Γ (e2eGsTy ℓ)) (p : Expr O' Γ .bool) (st' : Expr O' Γ GhostStT)
    (pos : Expr O' Γ posTy) :
    (e2eAcceptE q s p st' pos).size ≤
      s.size + p.size + st'.size + 2 * pos.size + 3 * bits q + 900 := by
  simp [e2eAcceptE, e2eGsMk, e2eGsSt, e2eGsB, e2eGsWin, e2eGsEpoch, e2eGsIdx, e2eGsTL,
    e2eGsTrans, e2eGsChall, e2eGsComp, e2eGsMaxAcc, e2eGsLeaks, e2eGsCorrs, pSet, pGet,
    maxAccSet, maxAccGet, maxN, leN, posEpoch, posIdx]
  simp only [esizeHide_def]; omega

@[local simp] private theorem size_e2eAcceptE_eq {O' : Ops (e2eSig ℓ)} {Γ} (q : ℕ)
    (s : Expr O' Γ (e2eGsTy ℓ)) (p : Expr O' Γ .bool) (st' : Expr O' Γ GhostStT)
    (pos : Expr O' Γ posTy) :
    (e2eAcceptE q s p st' pos).size =
      esizeHide (e2eAcceptE q s p st' pos)
        (s.size + p.size + st'.size + 2 * pos.size + 3 * bits q + 900) :=
  esize_eq_hide (size_e2eAcceptE_le q s p st' pos)

theorem size_e2eTrivialE_le {O' : Ops (e2eSig ℓ)} {Γ} (q Δ : ℕ)
    (s : Expr O' Γ (e2eGsTy ℓ)) (pos : Expr O' Γ posTy) :
    (e2eTrivialE q Δ s pos).size ≤ s.size + pos.size + 2 * bits q + bits Δ + 150 := by
  simp [e2eTrivialE, e2eGsTrans, e2eGsTL, e2eRecPos, healedByE, leN, posEq, posSender,
    posEpoch, posIdx, boolEq, orE]
  simp only [esizeHide_def]; omega

@[local simp] private theorem size_e2eTrivialE_eq {O' : Ops (e2eSig ℓ)} {Γ} (q Δ : ℕ)
    (s : Expr O' Γ (e2eGsTy ℓ)) (pos : Expr O' Γ posTy) :
    (e2eTrivialE q Δ s pos).size =
      esizeHide (e2eTrivialE q Δ s pos) (s.size + pos.size + 2 * bits q + bits Δ + 150) :=
  esize_eq_hide (size_e2eTrivialE_le q Δ s pos)

theorem size_e2eCorrAllowedE_le {O' : Ops (e2eSig ℓ)} {Γ} (q : ℕ)
    (s : Expr O' Γ (e2eGsTy ℓ)) (p : Expr O' Γ .bool) :
    (e2eCorrAllowedE q s p).size ≤ s.size + p.size + 2 * bits q + 80 := by
  simp [e2eCorrAllowedE, e2eGsChall, e2eGsTrans, e2eRecPos, e2eRecComp, posSender,
    otherE, boolEq]
  omega

@[local simp] private theorem size_e2eCorrAllowedE_eq {O' : Ops (e2eSig ℓ)} {Γ} (q : ℕ)
    (s : Expr O' Γ (e2eGsTy ℓ)) (p : Expr O' Γ .bool) :
    (e2eCorrAllowedE q s p).size =
      esizeHide (e2eCorrAllowedE q s p) (s.size + p.size + 2 * bits q + 80) :=
  esize_eq_hide (size_e2eCorrAllowedE_le q s p)

theorem size_e2eAfterCorrAllowedE_le {O' : Ops (e2eSig ℓ)} {Γ}
    (s : Expr O' Γ (e2eGsTy ℓ)) (p : Expr O' Γ .bool) :
    (e2eAfterCorrAllowedE s p).size ≤ s.size + p.size + 400 := by
  simp [e2eAfterCorrAllowedE, maxN, leN, pGet, e2eGsMk, e2eGsSt, e2eGsB, e2eGsWin,
    e2eGsEpoch, e2eGsIdx, e2eGsTL, e2eGsTrans, e2eGsChall, e2eGsComp, e2eGsMaxAcc, e2eGsLeaks,
    e2eGsCorrs]
  simp only [esizeHide_def]; omega

@[local simp] private theorem size_e2eAfterCorrAllowedE_eq {O' : Ops (e2eSig ℓ)} {Γ}
    (s : Expr O' Γ (e2eGsTy ℓ)) (p : Expr O' Γ .bool) :
    (e2eAfterCorrAllowedE s p).size =
      esizeHide (e2eAfterCorrAllowedE s p) (s.size + p.size + 400) :=
  esize_eq_hide (size_e2eAfterCorrAllowedE_le s p)

theorem size_e2eInWindowE_le {O' : Ops (e2eSig ℓ)} {Γ}
    (s : Expr O' Γ (e2eGsTy ℓ)) (p : Expr O' Γ .bool) :
    (e2eInWindowE s p).size ≤ s.size + p.size + 50 := by
  simp [e2eInWindowE, sendsInE, pGet, e2eGsEpoch]

@[local simp] private theorem size_e2eInWindowE_eq {O' : Ops (e2eSig ℓ)} {Γ}
    (s : Expr O' Γ (e2eGsTy ℓ)) (p : Expr O' Γ .bool) :
    (e2eInWindowE s p).size = esizeHide (e2eInWindowE s p) (s.size + p.size + 50) :=
  esize_eq_hide (size_e2eInWindowE_le s p)

theorem size_e2eSendOKE_le {O' : Ops (e2eSig ℓ)} {Γ}
    (s : Expr O' Γ (e2eGsTy ℓ)) (p : Expr O' Γ .bool) :
    (e2eSendOKE s p).size ≤ s.size + p.size + 30 := by
  simp [e2eSendOKE, e2eGsEpoch]

@[local simp] private theorem size_e2eSendOKE_eq {O' : Ops (e2eSig ℓ)} {Γ}
    (s : Expr O' Γ (e2eGsTy ℓ)) (p : Expr O' Γ .bool) :
    (e2eSendOKE s p).size = esizeHide (e2eSendOKE s p) (s.size + p.size + 30) :=
  esize_eq_hide (size_e2eSendOKE_le s p)

theorem size_e2eCorrOKE_le {O' : Ops (e2eSig ℓ)} {Γ}
    (s : Expr O' Γ (e2eGsTy ℓ)) (p : Expr O' Γ .bool) :
    (e2eCorrOKE s p).size ≤ s.size + p.size + 80 := by
  simp [e2eCorrOKE, e2eGsEpoch]

theorem size_e2eInTransitE_le {Γ} (q : ℕ)
    (s : Expr (e2eOps ℓ P C K decT encT) Γ (e2eGsTy ℓ))
    (qParty : Expr (e2eOps ℓ P C K decT encT) Γ .bool)
    (c : Expr (e2eOps ℓ P C K decT encT) Γ (B 32)) :
    (e2eInTransitE q s qParty c).size ≤ s.size + qParty.size + c.size + bits q + 50 := by
  simp [e2eInTransitE, e2eGsTrans, e2eRecPos, e2eRecCt, posSender, boolEq]; omega

@[local simp] private theorem size_e2eInTransitE_eq {Γ} (q : ℕ)
    (s : Expr (e2eOps ℓ P C K decT encT) Γ (e2eGsTy ℓ))
    (qParty : Expr (e2eOps ℓ P C K decT encT) Γ .bool)
    (c : Expr (e2eOps ℓ P C K decT encT) Γ (B 32)) :
    (e2eInTransitE q s qParty c).size =
      esizeHide (e2eInTransitE q s qParty c) (s.size + qParty.size + c.size + bits q + 50) :=
  esize_eq_hide (size_e2eInTransitE_le q s qParty c)

@[local simp] private theorem size_coinDraw256 {ι : Type} {T : OracleSpec ι}
    (I' : Iface (atomicSig ℓ Pt) T) {Γ : List (Ty (e2eSig ℓ))} :
    ((coinE2ESamplers (ℓ := ℓ) (Pt := Pt) (C := C) (K := K) (decT := decT) (encT := encT)
      I').draw256 (Γ := Γ)).size = 2 := by
  simp [coinE2ESamplers, mkE2ECoinSamplers]

@[local simp] private theorem size_coinDraw512 {ι : Type} {T : OracleSpec ι}
    (I' : Iface (atomicSig ℓ Pt) T) {Γ : List (Ty (e2eSig ℓ))} :
    ((coinE2ESamplers (ℓ := ℓ) (Pt := Pt) (C := C) (K := K) (decT := decT) (encT := encT)
      I').draw512 (Γ := Γ)).size = 2 := by
  simp [coinE2ESamplers, mkE2ECoinSamplers]

theorem size_e2eSamIfNec512C_le {ι : Type} {T : OracleSpec ι}
    (I' : Iface (atomicSig ℓ Pt) T) {Γ}
    (optR : Expr (e2eOps ℓ zeroPqxdhPrims C K decT encT) Γ (.opt BV512)) :
    (e2eSamIfNec512C
      (coinE2ESamplers (ℓ := ℓ) (Pt := Pt) (C := C) (K := K) (decT := decT) (encT := encT) I')
      optR).size ≤ optR.size + 15 := by
  simp [e2eSamIfNec512C]

@[local simp] private theorem size_e2eSamIfNec512C_eq {ι : Type} {T : OracleSpec ι}
    (I' : Iface (atomicSig ℓ Pt) T) {Γ}
    (optR : Expr (e2eOps ℓ zeroPqxdhPrims C K decT encT) Γ (.opt BV512)) :
    (e2eSamIfNec512C
      (coinE2ESamplers (ℓ := ℓ) (Pt := Pt) (C := C) (K := K) (decT := decT) (encT := encT) I')
      optR).size =
      csizeHide (e2eSamIfNec512C
        (coinE2ESamplers (ℓ := ℓ) (Pt := Pt) (C := C) (K := K) (decT := decT) (encT := encT) I')
        optR) (optR.size + 15) :=
  csize_eq_hide (size_e2eSamIfNec512C_le I' optR)

theorem size_drTrArmC_le {ι : Type} {T : OracleSpec ι}
    (I' : Iface (atomicSig ℓ Pt) T) (q Δ qep : ℕ) {Γ}
    (gsE : Expr (e2eOps ℓ zeroPqxdhPrims C K decT encT) Γ (e2eGsTy ℓ))
    (trArg : Expr (e2eOps ℓ zeroPqxdhPrims C K decT encT) Γ
      (.prod .bool (.prod PlainT (.opt BV512)))) :
    (drTrArmC (spqrDslHooks ℓ (Pt := Pt) zeroPqxdhPrims C K decT encT)
      (coinE2ESamplers (ℓ := ℓ) (Pt := Pt) (C := C) (K := K) (decT := decT) (encT := encT) I')
      q Δ qep gsE trArg).size ≤
      gsE.size + trArg.size + 11500 + 2 * bits q + 2 * bits Δ + 2 * bits qep := by
  simp [drTrArmC, orE, pGet, e2eGsSt, e2eGsWin, e2eGsEpoch, e2eGsIdx]
  simp only [esizeHide_def, csizeHide_def]; omega

theorem size_drChArmC_le {ι : Type} {T : OracleSpec ι}
    (I' : Iface (atomicSig ℓ Pt) T) (q Δ qep : ℕ) {Γ}
    (gsE : Expr (e2eOps ℓ zeroPqxdhPrims C K decT encT) Γ (e2eGsTy ℓ))
    (chArg : Expr (e2eOps ℓ zeroPqxdhPrims C K decT encT) Γ
      (.prod .bool (.prod PlainT (.prod PlainT (.opt BV512))))) :
    (drChArmC (spqrDslHooks ℓ (Pt := Pt) zeroPqxdhPrims C K decT encT)
      (coinE2ESamplers (ℓ := ℓ) (Pt := Pt) (C := C) (K := K) (decT := decT) (encT := encT) I')
      q Δ qep gsE chArg).size ≤
      gsE.size + chArg.size + 11800 + 2 * bits q + 3 * bits Δ + 2 * bits qep := by
  simp [drChArmC, orE, pGet, e2eGsSt, e2eGsB, e2eGsWin, e2eGsEpoch, e2eGsIdx]
  simp only [esizeHide_def, csizeHide_def]; omega

theorem size_drDlArmC_le {ι : Type} {T : OracleSpec ι}
    (I' : Iface (atomicSig ℓ Pt) T) (q : ℕ) {Γ}
    (gsE : Expr (e2eOps ℓ zeroPqxdhPrims C K decT encT) Γ (e2eGsTy ℓ))
    (dlArg : Expr (e2eOps ℓ zeroPqxdhPrims C K decT encT) Γ (.prod .bool (B 32))) :
    (drDlArmC (spqrDslHooks ℓ (Pt := Pt) zeroPqxdhPrims C K decT encT)
      (coinE2ESamplers (ℓ := ℓ) (Pt := Pt) (C := C) (K := K) (decT := decT) (encT := encT) I')
      q gsE dlArg).size ≤
      gsE.size + dlArg.size + 42500 + 5 * bits q := by
  simp [drDlArmC, otherE, pGet, e2eGsSt, e2eGsWin, e2eRecPos]
  simp only [esizeHide_def, csizeHide_def]; omega

theorem size_drIjArmC_le {ι : Type} {T : OracleSpec ι}
    (I' : Iface (atomicSig ℓ Pt) T) (q Δ qep : ℕ) {Γ}
    (gsE : Expr (e2eOps ℓ zeroPqxdhPrims C K decT encT) Γ (e2eGsTy ℓ))
    (ijArg : Expr (e2eOps ℓ zeroPqxdhPrims C K decT encT) Γ (.prod .bool (B 32))) :
    (drIjArmC (spqrDslHooks ℓ (Pt := Pt) zeroPqxdhPrims C K decT encT)
      (coinE2ESamplers (ℓ := ℓ) (Pt := Pt) (C := C) (K := K) (decT := decT) (encT := encT) I')
      q Δ qep gsE ijArg).size ≤
      gsE.size + ijArg.size + 42800 + 6 * bits q + 2 * bits Δ + bits (qep + 1) := by
  simp [drIjArmC, orE, isSomeE, otherE, pGet, e2eGsSt, e2eGsWin]
  simp only [esizeHide_def, csizeHide_def]; omega

end DrSendRecvSize

end SpqrSimSizeBounds

/-! ## Step handler over `EOps` -/

section StepE2E

set_option linter.unusedSectionVars false

variable {ℓ : ℕ} {Pt : Type} [DecidableEq Pt] [Zero Pt] [SampleableType Pt]
  {C : Crypto} {K : MlKem}
  {decT : PublicKey → Option Pt} {encT : Pt → PublicKey}

local notation "ESig" => e2eSig ℓ
local notation "EOps" => e2eOps ℓ zeroPqxdhPrims C K decT encT

def noAliceBelow10E {Γ : List (Ty ESig)}
    (gsE : Expr EOps Γ (e2eGsTy ℓ)) (pE : Expr EOps Γ .bool) : Expr EOps Γ .bool :=
  .not (.and (.not pE) (.lt (.fst (e2eGsEpoch gsE)) (.nat 10)))

theorem eval_noAliceBelow10E {Γ : List (Ty ESig)}
    (gsE : Expr EOps Γ (e2eGsTy ℓ)) (pE : Expr EOps Γ .bool) (ρ : Env Γ)
    (st : GameState (GhostState Bytes) (Plain ℓ) Bytes) (party : Party)
    (hgs : gsE.eval ρ = e2eGsEnc st) (hp : pE.eval ρ = partyEnc party) :
    (noAliceBelow10E (C := C) (K := K) (decT := decT) (encT := encT) gsE pE).eval ρ =
      noAliceCorrWhileAliceBelowEpoch10 st party := by
  cases party <;>
    simp [noAliceBelow10E, noAliceCorrWhileAliceBelowEpoch10, e2eGsEpoch, e2eGsEnc, partyEnc,
      hgs, hp, Expr.eval]

theorem cost_noAliceBelow10E_le {Γ : List (Ty ESig)}
    (gsE : Expr EOps Γ (e2eGsTy ℓ)) (pE : Expr EOps Γ .bool) :
    (noAliceBelow10E (C := C) (K := K) (decT := decT) (encT := encT) gsE pE).cost ≤
      gsE.cost + pE.cost + 15 := by
  have hb10 : bits 10 = 4 := by decide
  simp only [noAliceBelow10E, e2eGsEpoch, Expr.cost, hb10]
  omega

theorem size_noAliceBelow10E_le {Γ : List (Ty ESig)}
    (gsE : Expr EOps Γ (e2eGsTy ℓ)) (pE : Expr EOps Γ .bool) :
    (noAliceBelow10E (C := C) (K := K) (decT := decT) (encT := encT) gsE pE).size ≤
      gsE.size + pE.size + 15 := by
  have hb10 : bits 10 = 4 := by decide
  simp only [noAliceBelow10E, e2eGsEpoch, Expr.size, hb10]
  omega

def r1CrArmC {ι : Type} {T : OracleSpec ι} {I : Iface ESig T}
    (q : ℕ) {Γ : List (Ty ESig)}
    (gsE : Expr EOps Γ (e2eGsTy ℓ)) (crArg : Expr EOps Γ .bool) :
    Comp EOps I Γ (.prod (smRT GhostStT) (e2eGsTy ℓ)) :=
  .bind (.ret (.pair gsE crArg))
    (let gs0 : Expr EOps _ (e2eGsTy ℓ) := .fst .v0
     let p0 : Expr EOps _ .bool := .snd .v0
     let refuseCond : Expr EOps _ .bool :=
       orE (e2eGsWin gs0)
         (orE (.not (e2eCorrAllowedE q gs0 p0))
           (orE (e2eInWindowE gs0 p0) (.not (noAliceBelow10E gs0 p0))))
     .ite refuseCond
       (.ret (.pair (smRCorrE .none) gs0))
       (.ret (.pair (smRCorrE (.some (pGet (e2eGsSt gs0) p0)))
         (e2eAfterCorrAllowedE gs0 p0))))

theorem r1CrArmC_queries {ι : Type} {T : OracleSpec ι} {I : Iface ESig T}
    (q : ℕ) {Γ : List (Ty ESig)}
    (gsE : Expr EOps Γ (e2eGsTy ℓ)) (crArg : Expr EOps Γ .bool)
    (w : I.Tag → ℕ) (ws : I.smp.Samp → ℕ) :
    (r1CrArmC (C := C) (K := K) (decT := decT) (encT := encT) (I := I) q gsE crArg).queries
      w ws = 0 := by
  simp [r1CrArmC, Comp.queries]

theorem r1CrArmC_cost {ι : Type} {T : OracleSpec ι} {I : Iface ESig T}
    (q : ℕ) {Γ : List (Ty ESig)}
    (gsE : Expr EOps Γ (e2eGsTy ℓ)) (crArg : Expr EOps Γ .bool) :
    (r1CrArmC (C := C) (K := K) (decT := decT) (encT := encT) (I := I) q gsE crArg).cost ≤
      gsE.cost + crArg.cost + 75 * q + 550 := by
  let t0 : Ty ESig := .prod (e2eGsTy ℓ) .bool
  have hallow := cost_e2eCorrAllowedE_le (ℓ := ℓ) (O' := EOps) q
    (.fst .v0 : Expr EOps (t0 :: Γ) (e2eGsTy ℓ)) (.snd .v0)
  have hwin := cost_e2eInWindowE_le (ℓ := ℓ) (O' := EOps)
    (.fst .v0 : Expr EOps (t0 :: Γ) (e2eGsTy ℓ)) (.snd .v0)
  have hcorrOK := cost_noAliceBelow10E_le (C := C) (K := K) (decT := decT) (encT := encT)
    (.fst .v0 : Expr EOps (t0 :: Γ) (e2eGsTy ℓ)) (.snd .v0)
  have hafter := cost_e2eAfterCorrAllowedE_le (ℓ := ℓ) (O' := EOps)
    (.fst .v0 : Expr EOps (t0 :: Γ) (e2eGsTy ℓ)) (.snd .v0)
  simp only [r1CrArmC, orE, pGet, e2eGsSt, e2eGsWin, cost_smRCorrE, Comp.cost, Expr.cost,
    Expr.v0] at hallow hwin hcorrOK hafter ⊢
  omega

theorem r1CrArmC_size_le {ι : Type} {T : OracleSpec ι} {I : Iface ESig T}
    (q : ℕ) {Γ : List (Ty ESig)}
    (gsE : Expr EOps Γ (e2eGsTy ℓ)) (crArg : Expr EOps Γ .bool) :
    (r1CrArmC (C := C) (K := K) (decT := decT) (encT := encT) (I := I) q gsE crArg).size ≤
      gsE.size + crArg.size + 650 + 2 * bits q := by
  let t0 : Ty ESig := .prod (e2eGsTy ℓ) .bool
  have hallow := size_e2eCorrAllowedE_le (ℓ := ℓ) (O' := EOps) q
    (.fst .v0 : Expr EOps (t0 :: Γ) (e2eGsTy ℓ)) (.snd .v0)
  have hwin := size_e2eInWindowE_le (ℓ := ℓ) (O' := EOps)
    (.fst .v0 : Expr EOps (t0 :: Γ) (e2eGsTy ℓ)) (.snd .v0)
  have hcorrOK := size_noAliceBelow10E_le (C := C) (K := K) (decT := decT) (encT := encT)
    (.fst .v0 : Expr EOps (t0 :: Γ) (e2eGsTy ℓ)) (.snd .v0)
  have hafter := size_e2eAfterCorrAllowedE_le (ℓ := ℓ) (O' := EOps)
    (.fst .v0 : Expr EOps (t0 :: Γ) (e2eGsTy ℓ)) (.snd .v0)
  simp only [r1CrArmC, orE, pGet, e2eGsSt, e2eGsWin, size_smRCorrE, Comp.size, Expr.size,
    Expr.v0] at hallow hwin hcorrOK hafter ⊢
  omega

theorem r1CrArmC_eval {ι : Type} {T : OracleSpec ι} {I : Iface ESig T}
    (q : ℕ) {Γ : List (Ty ESig)}
    (gsE : Expr EOps Γ (e2eGsTy ℓ)) (crArg : Expr EOps Γ .bool) (ρ : Env Γ)
    (st : GameState (GhostState Bytes) (Plain ℓ) Bytes) (party : Party)
    (h : SmListBounded q st)
    (hgs : gsE.eval ρ = e2eGsEnc st) (harg : crArg.eval ρ = partyEnc party) :
    (r1CrArmC (C := C) (K := K) (decT := decT) (encT := encT) (I := I) q gsE crArg).eval ρ =
      Prod.map (fun st? => (none, (none, st?))) e2eGsEnc <$>
        I.liftP ((corrR (configR1OnCurve (ratchetKeyAdmissible protoSignalCodec decT encT))
          party).run st) := by
  set cfg : CryptoGames.SM.ConfigR (GhostState Bytes) (Plain ℓ) Bytes :=
    configR1OnCurve (ratchetKeyAdmissible protoSignalCodec decT encT)
  have hr1 : cfg.r1 = true := rfl
  unfold r1CrArmC corrR
  simp only [Comp.eval, Expr.eval, hgs, harg, pure_bind]
  let t0 : Ty ESig := .prod (e2eGsTy ℓ) .bool
  set ρ₁ := Env.cons (t := t0) (e2eGsEnc st, partyEnc party) ρ
  have hAllow := eval_e2eCorrAllowedE q (.fst (Expr.v0 (O := EOps))) (.snd .v0)
    ρ₁ st party h rfl rfl
  have hInWin := eval_e2eInWindowE (.fst (Expr.v0 (O := EOps))) (.snd .v0)
    ρ₁ st party rfl rfl
  have hCorrOK :
      (noAliceBelow10E (C := C) (K := K) (decT := decT) (encT := encT)
        (.fst .v0) (.snd .v0)).eval ρ₁ = cfg.corrOK st party :=
    eval_noAliceBelow10E (.fst .v0) (.snd .v0) ρ₁ st party rfl rfl
  have hRefuse :
      (orE (e2eGsWin (.fst (Expr.v0 (O := EOps))))
        (orE (.not (e2eCorrAllowedE q (.fst .v0) (.snd .v0)))
          (orE (e2eInWindowE (.fst .v0) (.snd .v0))
            (.not (noAliceBelow10E (.fst .v0) (.snd .v0)))))).eval ρ₁ =
      (st.win || !st.corrAllowed party || (cfg.r1 && inWindow st party) ||
        !cfg.corrOK st party) := by
    simp only [orE_eval, Expr.eval, hAllow, hInWin, hCorrOK, hr1, Bool.true_and]
    simp [ρ₁, e2eGsWin, e2eGsEnc, Expr.eval, Expr.v0, Bool.or_assoc]
  rw [hRefuse]
  by_cases href :
      st.win || !st.corrAllowed party || (cfg.r1 && inWindow st party) || !cfg.corrOK st party
  · simp only [href, ↓reduceIte, StateT.run_bind, StateT.run_get, StateT.run_pure,
      pure_bind, liftP_pure, map_pure, Prod.map]
    rfl
  · simp only [href, Bool.false_eq_true, ↓reduceIte, StateT.run_bind, StateT.run_get,
      StateT.run_set, StateT.run_pure, pure_bind, liftP_pure, map_pure, Prod.map]
    have hallowTrue : st.corrAllowed party = true := by
      cases hc : st.corrAllowed party
      · simp [hc] at href
      · rfl
    have hAfter := eval_e2eAfterCorrAllowedE (.fst (Expr.v0 (O := EOps))) (.snd .v0)
      ρ₁ st party hallowTrue rfl rfl
    have hpGet := pGet_eval (e2eGsSt (.fst (Expr.v0 (O := EOps)))) (.snd .v0)
      ρ₁ st.st party rfl rfl
    simp only [eval_smRCorrE, some_eval, hpGet, hAfter]

def r1OracleStepE2EC (q Δ qep : ℕ) {Γ : List (Ty ESig)}
    (gsE : Expr EOps Γ (e2eGsTy ℓ)) (qryE : Expr EOps Γ smQT) :
    Comp EOps (coinE2EIface (coinOnlyIface ℓ Pt)) Γ (.prod (smRT GhostStT) (e2eGsTy ℓ)) :=
  let hooks := spqrDslHooks ℓ zeroPqxdhPrims C K decT encT
  let coins := coinE2ESamplers (C := C) (K := K) (decT := decT) (encT := encT) (coinOnlyIface ℓ Pt)
  .bind (.ret (.pair gsE qryE))
    (.caseSum (.snd .v0)
      (drTrArmC hooks coins q Δ qep (.fst .v1) .v0)
      (.caseSum .v0
        (drChArmC hooks coins q Δ qep (.fst .v2) .v0)
        (.caseSum .v0
          (drDlArmC hooks coins q (.fst .v3) .v0)
          (.caseSum .v0
            (drIjArmC hooks coins q Δ qep (.fst .v4) .v0)
            (r1CrArmC q (.fst .v4) .v0)))))

theorem r1OracleStepE2EC_queries_zero (q Δ qep : ℕ) {Γ : List (Ty ESig)}
    (gsE : Expr EOps Γ (e2eGsTy ℓ)) (qryE : Expr EOps Γ smQT) (w : Empty → ℕ) :
    (r1OracleStepE2EC (Pt := Pt) (C := C) (K := K) (decT := decT) (encT := encT)
      q Δ qep gsE qryE).queries w (fun _ => 0) = 0 := by
  simp [r1OracleStepE2EC, Comp.queries, drTrArmC_queries_zero, drChArmC_queries_zero,
    drDlArmC_queries_zero, drIjArmC_queries_zero, r1CrArmC_queries]

theorem r1OracleStepE2EC_cost (q Δ qep : ℕ) {Γ : List (Ty ESig)}
    (gsE : Expr EOps Γ (e2eGsTy ℓ)) (qryE : Expr EOps Γ smQT) :
    (r1OracleStepE2EC (Pt := Pt) (C := C) (K := K) (decT := decT) (encT := encT)
      q Δ qep gsE qryE).cost ≤
      gsE.cost + qryE.cost + 5106000 + 10 * (ℓ / 32 + 1) + 420 * q +
        3 * bits Δ + bits qep + bits (qep + 1) := by
  let hooks := spqrDslHooks ℓ zeroPqxdhPrims C K decT encT
  let coins := coinE2ESamplers (C := C) (K := K) (decT := decT) (encT := encT) (coinOnlyIface ℓ Pt)
  let tTop : Ty ESig := .prod (e2eGsTy ℓ) smQT
  let r1T : Ty ESig :=
    .sum (.prod .bool (.prod PlainT (.prod PlainT (.opt BV512))))
      (.sum (.prod .bool (B 32)) (.sum (.prod .bool (B 32)) .bool))
  let r2T : Ty ESig := .sum (.prod .bool (B 32)) (.sum (.prod .bool (B 32)) .bool)
  let r3T : Ty ESig := .sum (.prod .bool (B 32)) .bool
  have htr := drTrArmC_cost hooks coins q Δ qep
    (.fst .v1 : Expr EOps (.prod .bool (.prod PlainT (.opt BV512)) :: tTop :: Γ) (e2eGsTy ℓ)) .v0
  have hch := drChArmC_cost hooks coins q Δ qep
    (.fst .v2 : Expr EOps
      (.prod .bool (.prod PlainT (.prod PlainT (.opt BV512))) :: r1T :: tTop :: Γ)
      (e2eGsTy ℓ)) .v0
  have hdl := drDlArmC_cost hooks coins q
    (.fst .v3 : Expr EOps (.prod .bool (B 32) :: r2T :: r1T :: tTop :: Γ) (e2eGsTy ℓ)) .v0
  have hij := drIjArmC_cost hooks coins q Δ qep
    (.fst .v4 : Expr EOps (.prod .bool (B 32) :: r3T :: r2T :: r1T :: tTop :: Γ) (e2eGsTy ℓ)) .v0
  have hcr := r1CrArmC_cost (C := C) (K := K) (decT := decT) (encT := encT)
    (I := coinE2EIface (coinOnlyIface ℓ Pt)) q
    (.fst .v4 : Expr EOps (.bool :: r3T :: r2T :: r1T :: tTop :: Γ) (e2eGsTy ℓ)) .v0
  dsimp only [hooks, coins] at htr hch hdl hij
  simp only [r1OracleStepE2EC, Comp.cost, Expr.cost, Expr.v0, Expr.v1, Expr.v2, Expr.v3,
    Expr.v4] at htr hch hdl hij hcr ⊢
  omega

theorem r1OracleStepE2EC_size_le (q Δ qep : ℕ) {Γ : List (Ty ESig)}
    (gsE : Expr EOps Γ (e2eGsTy ℓ)) (qryE : Expr EOps Γ smQT) :
    (r1OracleStepE2EC (Pt := Pt) (C := C) (K := K) (decT := decT) (encT := encT)
      q Δ qep gsE qryE).size ≤
      gsE.size + qryE.size + 110000 + 17 * bits q + 7 * bits Δ + 4 * bits qep + bits (qep + 1) := by
  let tTop : Ty ESig := .prod (e2eGsTy ℓ) smQT
  let r1T : Ty ESig :=
    .sum (.prod .bool (.prod PlainT (.prod PlainT (.opt BV512))))
      (.sum (.prod .bool (B 32)) (.sum (.prod .bool (B 32)) .bool))
  let r2T : Ty ESig := .sum (.prod .bool (B 32)) (.sum (.prod .bool (B 32)) .bool)
  let r3T : Ty ESig := .sum (.prod .bool (B 32)) .bool
  have htr := size_drTrArmC_le (coinOnlyIface ℓ Pt) q Δ qep
    (.fst .v1 : Expr EOps (.prod .bool (.prod PlainT (.opt BV512)) :: tTop :: Γ) (e2eGsTy ℓ)) .v0
  have hch := size_drChArmC_le (coinOnlyIface ℓ Pt) q Δ qep
    (.fst .v2 : Expr EOps
      (.prod .bool (.prod PlainT (.prod PlainT (.opt BV512))) :: r1T :: tTop :: Γ)
      (e2eGsTy ℓ)) .v0
  have hdl := size_drDlArmC_le (coinOnlyIface ℓ Pt) q
    (.fst .v3 : Expr EOps (.prod .bool (B 32) :: r2T :: r1T :: tTop :: Γ) (e2eGsTy ℓ)) .v0
  have hij := size_drIjArmC_le (coinOnlyIface ℓ Pt) q Δ qep
    (.fst .v4 : Expr EOps (.prod .bool (B 32) :: r3T :: r2T :: r1T :: tTop :: Γ) (e2eGsTy ℓ)) .v0
  have hcr := r1CrArmC_size_le (C := C) (K := K) (decT := decT) (encT := encT)
    (I := coinE2EIface (coinOnlyIface ℓ Pt)) q
    (.fst .v4 : Expr EOps (.bool :: r3T :: r2T :: r1T :: tTop :: Γ) (e2eGsTy ℓ)) .v0
  simp only [r1OracleStepE2EC, Comp.size, Expr.size, Expr.v0, Expr.v1, Expr.v2, Expr.v3,
    Expr.v4] at htr hch hdl hij hcr ⊢
  omega

theorem r1OracleStepE2EC_eval (q Δ qep : ℕ) {Γ : List (Ty ESig)}
    (gsE : Expr EOps Γ (e2eGsTy ℓ)) (qryE : Expr EOps Γ smQT) (ρ : Env Γ)
    (idA idB : IdentityKey) (spkCoins : BitVec 256)
    (st : GameState (GhostState Bytes) (Plain ℓ) Bytes)
    (sq : (CryptoGames.SM.spec (GhostState Bytes) (Plain ℓ) (BitVec 512) Bytes).Domain)
    (h : SmReachBounded C K q st)
    (hgs : gsE.eval ρ = e2eGsEnc st) (hqry : qryE.eval ρ = smQenc sq) :
    (r1OracleStepE2EC (Pt := Pt) (C := C) (K := K) (decT := decT) (encT := encT)
      q Δ qep gsE qryE).eval ρ =
      Prod.map (smRenc (stT := GhostStT) id sq) e2eGsEnc <$>
        (coinE2EIface (coinOnlyIface ℓ Pt)).liftP ((oracleImplR
          (sessionSchemeFixedSpk
            (paramsIdsWithSpqr C (spqrV1SessionUniformCoins C.F K) idA idB) ℓ spkCoins)
          Δ qep (configR1OnCurve (ratchetKeyAdmissible protoSignalCodec decT encT)) sq).run st) := by
  let hooks := spqrDslHooks ℓ zeroPqxdhPrims C K decT encT
  let coins := coinE2ESamplers (C := C) (K := K) (decT := decT) (encT := encT) (coinOnlyIface ℓ Pt)
  unfold r1OracleStepE2EC
  simp only [Comp.eval, Expr.eval, hgs, hqry, pure_bind]
  rcases sq with (((⟨party, m, optR⟩ | ⟨party, m0, m1, optR⟩) | ⟨party, c⟩) | ⟨party, c⟩) | party
  · dsimp only [smQenc, partyToBool_eq_partyEnc]
    exact drTrArmC_eval hooks coins q Δ qep _ _ _ idA idB spkCoins st party m optR h rfl rfl
  · dsimp only [smQenc, partyToBool_eq_partyEnc]
    exact drChArmC_eval hooks coins q Δ qep _ _ _ idA idB spkCoins st party m0 m1 optR h rfl rfl
  · dsimp only [smQenc, partyToBool_eq_partyEnc]
    exact drDlArmC_eval hooks coins q _ _ _ idA idB spkCoins st party c h rfl rfl
  · dsimp only [smQenc, partyToBool_eq_partyEnc]
    exact drIjArmC_eval hooks coins q Δ qep _ _ _ idA idB spkCoins st party c h rfl rfl
  · dsimp only [smQenc, partyToBool_eq_partyEnc, Expr.v0, Expr.eval, Env.get]
    refine Eq.trans (r1CrArmC_eval (C := C) (K := K) (decT := decT) (encT := encT)
      (I := coinE2EIface (coinOnlyIface ℓ Pt)) q _ _ _ st party h.lists ?_ ?_) ?_
    · rfl
    · rfl
    · dsimp only [oracleImplR]
      congr 1
      funext ⟨st?, s'⟩
      cases st? <;> rfl

end StepE2E

/-! ## `CostedReduction` witness -/

section Reduction

variable (C : Crypto) (K : MlKem) {Pt : Type} [DecidableEq Pt] [Zero Pt] [SampleableType Pt]
  (Dh : CryptoGames.CKA.DHFun (BitVec 256) Pt) (encPt : Pt → Bytes)
  (encT : Pt → PublicKey) (decT : PublicKey → Option Pt)
  (idA idB : IdentityKey) (lam : Pt) (ℓ q qep : ℕ)

def uniformStartRedReal :
    CostedReduction (atomicSessionOps ℓ Pt C K Dh encPt encT decT lam)
      (coinOnlyIface ℓ Pt)
      (CryptoGames.SM.spec (GhostState Bytes) (Plain ℓ) (BitVec 512) Bytes)
      (e2eSessionCodec ℓ Pt) (.prod BV256 BV256) .unit .bool .bool where
  σ := liftTy (Pt := Pt) (e2eGsTy ℓ)
  init := initEpoch0GsC (ℓ := ℓ) (Pt := Pt) (C := C) (K := K) (Dh := Dh)
    (encPt := encPt) (encT := encT) (decT := decT) (lam := lam) idA idB
  handle := liftCompCoins (Pt := Pt) (C := C) (K := K) (Dh := Dh) (encPt := encPt)
    (encT := encT) (decT := decT) (lam := lam) (I' := coinOnlyIface ℓ Pt) rfl
    (r1OracleStepE2EC (ℓ := ℓ) (Pt := Pt) (C := C) (K := K) (decT := decT) (encT := encT)
      q (2 + 1) qep (Γ := [e2eGsTy ℓ, smQT]) .v0 .v1)
  finish := .ret (liftExpr (Pt := Pt) (C := C) (K := K) (Dh := Dh) (encPt := encPt)
    (encT := encT) (decT := decT) (lam := lam)
    (orE (O' := e2eOps ℓ zeroPqxdhPrims C K decT encT) (Γ := [e2eGsTy ℓ, .bool])
      (boolEq (e2eGsB .v0) .v1) (e2eGsWin .v0)))

/-- Promoted `CostedReduction` for `uniformStartDistinguisher`, guarded by `if ℓ < 10 ^ 6`. -/
def uniformStartRed :
    CostedReduction (atomicSessionOps ℓ Pt C K Dh encPt encT decT lam)
      (coinOnlyIface ℓ Pt)
      (CryptoGames.SM.spec (GhostState Bytes) (Plain ℓ) (BitVec 512) Bytes)
      (e2eSessionCodec ℓ Pt) (.prod BV256 BV256) .unit .bool .bool :=
  if ℓ < 10 ^ 6 then
    uniformStartRedReal C K Dh encPt encT decT idA idB lam ℓ q qep
  else
    dummyBoolSessionRed (coinOnlyIface ℓ Pt) (.prod BV256 BV256)

/-! ## Cost, size, and `GRedBounded` bounds -/

private theorem q_add_eleven_le_ratchetCostBudget (q' qep' : ℕ) :
    q' + 11 ≤ ratchetCostBudget q' qep' := by
  have h := session_cost_le_ratchetCostBudget q' qep' 100 (400 * q') 0 0 0
    (by omega) (by omega) (by omega) (by omega) (by omega)
  omega

theorem uniformStartRed_totalQueries_zero :
    (uniformStartRed C K Dh encPt encT decT idA idB lam ℓ q qep).totalQueries
      Empty.elim (fun _ => 0) q = 0 := by
  unfold uniformStartRed
  split_ifs with hℓ
  · simp [uniformStartRedReal, CostedReduction.totalQueries, initEpoch0GsC_queries_zero,
      liftCompCoins_queries_zero, Comp.queries]
  · exact dummyBoolSessionRed_totalQueries _ _ _ _ _

theorem uniformStartRed_totalCost_le {qep' : ℕ} (hqep : qep ≤ qep') :
    (uniformStartRed C K Dh encPt encT decT idA idB lam ℓ q qep).totalCost q ≤
      ratchetCostBudget q qep' := by
  unfold uniformStartRed
  split_ifs with hℓ
  · let stepE2E := r1OracleStepE2EC (ℓ := ℓ) (Pt := Pt) (C := C) (K := K) (decT := decT) (encT := encT)
      q (2 + 1) qep (Γ := [e2eGsTy ℓ, smQT]) .v0 .v1
    let finE2E := orE (O' := e2eOps ℓ zeroPqxdhPrims C K decT encT)
      (Γ := [e2eGsTy ℓ, .bool]) (boolEq (e2eGsB .v0) .v1) (e2eGsWin .v0)
    have hinit := initEpoch0GsC_cost (ℓ := ℓ) (Pt := Pt) (C := C) (K := K) (Dh := Dh)
      (encPt := encPt) (encT := encT) (decT := decT) (lam := lam) idA idB
    have hstep1 := liftCompCoins_cost (Pt := Pt) (C := C) (K := K) (Dh := Dh) (encPt := encPt)
      (encT := encT) (decT := decT) (lam := lam) (I' := coinOnlyIface ℓ Pt) rfl stepE2E
    have hstep2 : stepE2E.cost ≤ 5106010 + 10 * (ℓ / 32 + 1) + 420 * q +
        3 * bits (2 + 1) + bits qep + bits (qep + 1) := by
      have h := r1OracleStepE2EC_cost (ℓ := ℓ) (Pt := Pt) (C := C) (K := K)
        (decT := decT) (encT := encT) q (2 + 1) qep (Γ := [e2eGsTy ℓ, smQT]) .v0 .v1
      simp only [Expr.v0, Expr.v1, Expr.cost] at h
      dsimp only [stepE2E, Expr.v0, Expr.v1]
      omega
    have hfin : (liftExpr (ℓ := ℓ) (Pt := Pt) (C := C) (K := K) (Dh := Dh) (encPt := encPt)
        (encT := encT) (decT := decT) (lam := lam) finE2E).cost ≤ 500 := by
      have h := liftExpr_cost (ℓ := ℓ) (Pt := Pt) (C := C) (K := K) (Dh := Dh) (encPt := encPt)
        (encT := encT) (decT := decT) (lam := lam) finE2E
      simp only [finE2E, orE, boolEq, e2eGsB, e2eGsWin, Expr.v0, Expr.v1, Expr.cost] at h ⊢
      omega
    have hb3 : bits (2 + 1) = 2 := by decide
    have hbQep1 : bits qep ≤ bits qep' := bits_mono hqep
    have hbQep2 : bits (qep + 1) ≤ bits qep' + 1 :=
      (bits_succ_le qep).trans (Nat.add_le_add_right (bits_mono hqep) 1)
    have hdiv : ℓ / 32 + 1 ≤ 31251 := by omega
    have hhandle :
        max 1 ((uniformStartRedReal C K Dh encPt encT decT idA idB lam ℓ q qep).handle.cost + 16) ≤
          173600000 + 13440 * q + 64 * bits qep' := by
      change max 1 ((liftCompCoins rfl stepE2E).cost + 16) ≤
        173600000 + 13440 * q + 64 * bits qep'
      omega
    have hmul :
        q * max 1
          ((uniformStartRedReal C K Dh encPt encT decT idA idB lam ℓ q qep).handle.cost + 16) ≤
          q * (173600000 + 13440 * q + 64 * bits qep') :=
      Nat.mul_le_mul_left q hhandle
    have hinit_le :
        (uniformStartRedReal C K Dh encPt encT decT idA idB lam ℓ q qep).init.cost ≤ 3020000 := by
      change (initEpoch0GsC idA idB).cost ≤ 3020000
      omega
    have hfin_le :
        (uniformStartRedReal C K Dh encPt encT decT idA idB lam ℓ q qep).finish.cost ≤ 1000 := by
      change (Comp.ret (liftExpr finE2E)).cost ≤ 1000
      simp only [Comp.cost]
      omega
    have htot :
        (uniformStartRedReal C K Dh encPt encT decT idA idB lam ℓ q qep).totalCost q ≤
          3020000 + q * (173600000 + 13440 * q + 64 * bits qep') + 1000 := by
      dsimp only [CostedReduction.totalCost, coinOnlyIface, e2eSessionCodec]
      omega
    exact htot.trans (session_cost_le_ratchetCostBudget q qep' 3020000 1000 173600000 13440 64
      (by omega) (by omega) (by omega) (by omega) (by omega))
  · exact dummyBoolSessionRed_totalCost_le _ rfl _ q qep'

theorem uniformStartRed_size_le_of_clamp {qep' : ℕ}
    (hqep_B : qep + 1 ≤ ratchetCostBudget q qep') :
    (uniformStartRed C K Dh encPt encT decT idA idB lam ℓ q qep).size ≤
      reductionSizeBudget + 2 ^ 12 * bits (ratchetCostBudget q qep') := by
  unfold uniformStartRed
  split_ifs with hℓ
  · let stepE2E := r1OracleStepE2EC (ℓ := ℓ) (Pt := Pt) (C := C) (K := K) (decT := decT) (encT := encT)
      q (2 + 1) qep (Γ := [e2eGsTy ℓ, smQT]) .v0 .v1
    let finE2E := orE (O' := e2eOps ℓ zeroPqxdhPrims C K decT encT)
      (Γ := [e2eGsTy ℓ, .bool]) (boolEq (e2eGsB .v0) .v1) (e2eGsWin .v0)
    have hinit := initEpoch0GsC_size_le (ℓ := ℓ) (Pt := Pt) (C := C) (K := K) (Dh := Dh)
      (encPt := encPt) (encT := encT) (decT := decT) (lam := lam) idA idB
    have hstep1 := liftCompCoins_size_le (Pt := Pt) (C := C) (K := K) (Dh := Dh) (encPt := encPt)
      (encT := encT) (decT := decT) (lam := lam) (I' := coinOnlyIface ℓ Pt) rfl stepE2E
    have hstep2 : stepE2E.size ≤ 110002 + 17 * bits q + 7 * bits (2 + 1) +
        4 * bits qep + bits (qep + 1) := by
      have h := r1OracleStepE2EC_size_le (ℓ := ℓ) (Pt := Pt) (C := C) (K := K)
        (decT := decT) (encT := encT) q (2 + 1) qep (Γ := [e2eGsTy ℓ, smQT]) .v0 .v1
      simp only [Expr.v0, Expr.v1, Expr.size] at h
      dsimp only [stepE2E, Expr.v0, Expr.v1]
      omega
    have hfin : (liftExpr (ℓ := ℓ) (Pt := Pt) (C := C) (K := K) (Dh := Dh) (encPt := encPt)
        (encT := encT) (decT := decT) (lam := lam) finE2E).size ≤ 500 := by
      have h := liftExpr_size_le (ℓ := ℓ) (Pt := Pt) (C := C) (K := K) (Dh := Dh) (encPt := encPt)
        (encT := encT) (decT := decT) (lam := lam) finE2E
      simp only [finE2E, orE, boolEq, e2eGsB, e2eGsWin, Expr.v0, Expr.v1, Expr.size] at h ⊢
      omega
    have hb3 : bits (2 + 1) = 2 := by decide
    have hqB : q + 11 ≤ ratchetCostBudget q qep' := q_add_eleven_le_ratchetCostBudget q qep'
    have hbq : bits q ≤ bits (ratchetCostBudget q qep') := bits_mono (by omega)
    have hbqep : bits qep ≤ bits (ratchetCostBudget q qep') := bits_mono (by omega)
    have hbqep1 : bits (qep + 1) ≤ bits (ratchetCostBudget q qep') := bits_mono hqep_B
    have hsz :
        (uniformStartRedReal C K Dh encPt encT decT idA idB lam ℓ q qep).size ≤
          1000000 + 198 * bits (ratchetCostBudget q qep') := by
      dsimp only [uniformStartRedReal, CostedReduction.size, Comp.size]
      change (initEpoch0GsC idA idB).size + (liftCompCoins rfl stepE2E).size +
        ((liftExpr finE2E).size + 1) ≤ 1000000 + 198 * bits (ratchetCostBudget q qep')
      omega
    exact size_le_budget_of_log_cost (by decide) (by decide) hsz
  · exact (dummyBoolSessionRed_size_le (coinOnlyIface ℓ Pt) (.prod BV256 BV256)).trans
      (Nat.le_add_right _ _)

theorem uniformStartRed_size_le {qep' : ℕ} (hqep_q : qep ≤ q + 10) :
    (uniformStartRed C K Dh encPt encT decT idA idB lam ℓ q qep).size ≤
      reductionSizeBudget + 2 ^ 12 * bits (ratchetCostBudget q qep') := by
  have hqB := q_add_eleven_le_ratchetCostBudget q qep'
  exact uniformStartRed_size_le_of_clamp C K Dh encPt encT decT idA idB lam ℓ q qep (by omega)

theorem uniformStartRed_gRedBounded_of_clamp {qep' : ℕ}
    (hqep : qep ≤ qep') (hqep_B : qep + 1 ≤ ratchetCostBudget q qep') :
    GRedBounded (uniformStartRed C K Dh encPt encT decT idA idB lam ℓ q qep)
      Empty.elim (fun _ => 0) q 0 (ratchetCostBudget q qep') :=
  gRedBounded_of_bounds _ Empty.elim (fun _ => 0) q 0 (ratchetCostBudget q qep')
    (uniformStartRed_totalCost_le C K Dh encPt encT decT idA idB lam ℓ q qep hqep)
    (uniformStartRed_size_le_of_clamp C K Dh encPt encT decT idA idB lam ℓ q qep hqep_B)
    (Nat.le_of_eq (uniformStartRed_totalQueries_zero C K Dh encPt encT decT idA idB lam ℓ q qep))
    (atomicSessionOps_sizeHonest ℓ Pt C K Dh encPt encT decT lam)
    (atomicSamplers_sizeHonest ℓ Pt)

theorem uniformStartRed_gRedBounded_of_le {qep' : ℕ}
    (hqep_q : qep ≤ q + 10) (hqep : qep ≤ qep') :
    GRedBounded (uniformStartRed C K Dh encPt encT decT idA idB lam ℓ q qep)
      Empty.elim (fun _ => 0) q 0 (ratchetCostBudget q qep') :=
  gRedBounded_of_bounds _ Empty.elim (fun _ => 0) q 0 (ratchetCostBudget q qep')
    (uniformStartRed_totalCost_le C K Dh encPt encT decT idA idB lam ℓ q qep hqep)
    (uniformStartRed_size_le C K Dh encPt encT decT idA idB lam ℓ q qep hqep_q)
    (Nat.le_of_eq (uniformStartRed_totalQueries_zero C K Dh encPt encT decT idA idB lam ℓ q qep))
    (atomicSessionOps_sizeHonest ℓ Pt C K Dh encPt encT decT lam)
    (atomicSamplers_sizeHonest ℓ Pt)

theorem uniformStartRed_gRedBounded (hqep : qep ≤ q + 10) :
    GRedBounded (uniformStartRed C K Dh encPt encT decT idA idB lam ℓ q qep)
      Empty.elim (fun _ => 0) q 0 (ratchetCostBudget q qep) :=
  uniformStartRed_gRedBounded_of_le C K Dh encPt encT decT idA idB lam ℓ q qep hqep (Nat.le_refl qep)

theorem uniformStartRed_gRedBounded_succ (hqep : qep ≤ q + 10) :
    GRedBounded (uniformStartRed C K Dh encPt encT decT idA idB lam ℓ q qep)
      Empty.elim (fun _ => 0) q 0 (ratchetCostBudget q (qep + 1)) :=
  uniformStartRed_gRedBounded_of_le C K Dh encPt encT decT idA idB lam ℓ q qep hqep (Nat.le_succ qep)

/-! ## `.eval` equivalence -/

theorem uniformStartRed_eval
    (A : CryptoGames.SM.Adversary (GhostState Bytes) (Plain ℓ) (BitVec 512) Bytes)
    (rc : RootKey × BitVec 256)
    (hA : MakesAtMostQueries A q) (hℓ : ℓ < 10 ^ 6) :
    (uniformStartRed C K Dh encPt encT decT idA idB lam ℓ q qep).eval (fun _ => A) rc =
      uniformStartDistinguisher (paramsV1 C K idA idB) ℓ
        (configR1OnCurve (ratchetKeyAdmissible protoSignalCodec decT encT)) qep A rc := by
  unfold uniformStartRed
  simp only [hℓ, ↓reduceIte]
  set cfg := configR1OnCurve (ratchetKeyAdmissible protoSignalCodec decT encT)
  set sm := libsignalSessionSchemeFromEpoch0Keys (paramsV1 C K idA idB) ℓ rc.1 rc.2
  let so : QueryImpl (unifSpec + CryptoGames.SM.spec (GhostState Bytes) (Plain ℓ) (BitVec 512) Bytes)
      (StateT (GameState (GhostState Bytes) (Plain ℓ) Bytes) ProbComp) :=
    (QueryImpl.ofLift unifSpec ProbComp).liftTarget
      (StateT (GameState (GhostState Bytes) (Plain ℓ) Bytes) ProbComp) +
      oracleImplR sm 3 qep cfg
  let enc : GameState (GhostState Bytes) (Plain ℓ) Bytes →
      (liftTy (Pt := Pt) (e2eGsTy ℓ)).denote :=
    fun st => liftVal (Pt := Pt) (e2eGsEnc st)
  let Inv : ℕ → GameState (GhostState Bytes) (Plain ℓ) Bytes → Prop :=
    fun m st => m ≤ q ∧ SmReachBounded C K (q - m) st
  have hsim := eval_eq_simulateQ_of_enc
    (uniformStartRedReal C K Dh encPt encT decT idA idB lam ℓ q qep)
    enc Inv
    (epoch0InitImpl C K idA idB ℓ)
    so
    (fun s₁ b' => pure (s₁.b == b' || s₁.win))
    q rc
    (initEpoch0GsC_eval idA idB rc)
    (fun r hr => by
      refine ⟨Nat.le_refl q, ?_⟩
      rw [Nat.sub_self]
      exact smReachBounded_epoch0InitImpl C K idA idB ℓ rc hr)
    (fun n s => rfl)
    (fun m sq s hs => by
      have hreachQ : SmReachBounded C K q s := hs.2.mono (by omega)
      have horacle := oracleImplR_epoch0Keys_eq_fixedSpk C K idA idB ℓ 3 qep rc 0 cfg
      refine ⟨?_, ?_⟩
      · change (do
            let p ← (liftCompCoins (Pt := Pt) (C := C) (K := K) (Dh := Dh) (encPt := encPt)
              (encT := encT) (decT := decT) (lam := lam) (I' := coinOnlyIface ℓ Pt) rfl
              (r1OracleStepE2EC (ℓ := ℓ) (Pt := Pt) (C := C) (K := K) (decT := decT) (encT := encT)
                q (2 + 1) qep (Γ := [e2eGsTy ℓ, smQT]) .v0 .v1)).eval
              (.cons (enc s) (.cons ((e2eSessionCodec ℓ Pt).qenc sq) .nil))
            pure ((e2eSessionCodec ℓ Pt).rdec sq p.1, p.2)) =
          Prod.map id enc <$> (oracleImplR sm 3 qep cfg sq).run s
        have hev := liftCompCoins_eval (Pt := Pt) (C := C) (K := K) (Dh := Dh) (encPt := encPt)
          (encT := encT) (decT := decT) (lam := lam) (I' := coinOnlyIface ℓ Pt) rfl
          (r1OracleStepE2EC (ℓ := ℓ) (Pt := Pt) (C := C) (K := K) (decT := decT) (encT := encT)
            q (2 + 1) qep (Γ := [e2eGsTy ℓ, smQT]) .v0 .v1)
          (.cons (e2eGsEnc s) (.cons (smQenc (St := GhostState Bytes) sq) .nil))
        change (liftCompCoins rfl
            (r1OracleStepE2EC q (2 + 1) qep (Γ := [e2eGsTy ℓ, smQT]) .v0 .v1)).eval
            (.cons (enc s) (.cons (liftVal (Pt := Pt) (smQenc (St := GhostState Bytes) sq)) .nil)) =
          liftVal (Pt := Pt) <$>
            (r1OracleStepE2EC q (2 + 1) qep (Γ := [e2eGsTy ℓ, smQT]) .v0 .v1).eval
              (.cons (e2eGsEnc s) (.cons (smQenc (St := GhostState Bytes) sq) .nil)) at hev
        rw [liftVal_smQenc] at hev
        have hstepE2E := r1OracleStepE2EC_eval (ℓ := ℓ) (Pt := Pt) (C := C) (K := K)
          (decT := decT) (encT := encT) q (2 + 1) qep
          (.v0 : Expr (e2eOps ℓ zeroPqxdhPrims C K decT encT) [e2eGsTy ℓ, smQT] (e2eGsTy ℓ)) .v1
          (.cons (e2eGsEnc s) (.cons (smQenc (St := GhostState Bytes) sq) .nil))
          idA idB 0 s sq hreachQ rfl rfl
        rw [hev, hstepE2E, liftP_unif_eq_self _ (fun _ => rfl), ← horacle]
        simp only [map_eq_bind_pure_comp, Function.comp_def, bind_assoc, pure_bind]
        refine bind_congr fun ⟨ans, s'⟩ => congrArg pure ?_
        change ((e2eSessionCodec ℓ Pt).rdec sq
            (liftVal (Pt := Pt) (smRenc (stT := GhostStT) id sq ans)), enc s') = (ans, enc s')
        rcases sq with (((_ | _) | _) | _) | _ <;> rcases ans with _ | v <;> (try rfl) <;>
          rcases v with _ | ⟨_, _, _ | _⟩ <;> rfl
      · intro r hr
        dsimp only [so, Sum.elim_inr] at hr
        rw [horacle] at hr
        have hr' := smReachBounded_oracleImplR C K idA idB ℓ 3 qep (q - (m + 1)) 0 cfg sq hs.2 hr
        refine ⟨by omega, ?_⟩
        have heq : q - (m + 1) + 1 = q - m := by omega
        exact heq ▸ hr')
    (fun s₁ b' _ => by
      dsimp only [uniformStartRedReal, Comp.eval]
      have hev := liftExpr_eval (Pt := Pt) (C := C) (K := K) (Dh := Dh) (encPt := encPt)
        (encT := encT) (decT := decT) (lam := lam)
        (orE (O' := e2eOps ℓ zeroPqxdhPrims C K decT encT) (Γ := [e2eGsTy ℓ, .bool])
          (boolEq (e2eGsB .v0) .v1) (e2eGsWin .v0))
        (.cons (e2eGsEnc s₁) (.cons b' .nil))
      change (liftExpr (orE (O' := e2eOps ℓ zeroPqxdhPrims C K decT encT)
          (Γ := [e2eGsTy ℓ, .bool]) (boolEq (e2eGsB .v0) .v1) (e2eGsWin .v0))).eval
          (.cons (enc s₁) (.cons b' .nil)) = _ at hev
      rw [hev]
      simp [orE_eval, boolEq_eval, e2eGsB, e2eGsWin, e2eGsEnc, Expr.eval, Expr.v0, Expr.v1,
        liftVal])
    (fun {m n} s hmn hn => ⟨by omega, hn.2.mono (by omega)⟩)
    (fun _ => A)
    (fun _ => isQueryBoundP_of_makesAtMostQueries hA)
  rw [hsim]
  unfold uniformStartDistinguisher runR epoch0InitImpl
  simp only [bind_assoc, pure_bind]
  refine bind_congr fun b => ?_
  refine bind_congr fun k => ?_
  refine bind_congr_of_mem_support' ((simulateQ so A).run (initState sm.sendPart k b)) ?_
  intro ⟨b', s₁⟩ hr
  have hb_pres : ∀ {α : Type} {oa : OracleComp (unifSpec +
        CryptoGames.SM.spec (GhostState Bytes) (Plain ℓ) (BitVec 512) Bytes) α}
      (s : GameState (GhostState Bytes) (Plain ℓ) Bytes)
      (r : α × GameState (GhostState Bytes) (Plain ℓ) Bytes),
      r ∈ support ((simulateQ so oa).run s) → r.2.b = s.b := by
    intro α oa
    induction oa using OracleComp.inductionOn with
    | pure a =>
      intro s r hr0
      simp only [simulateQ_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff] at hr0
      subst hr0; rfl
    | query_bind qy mx ih =>
      intro s r hr0
      rw [run_simulateQ_query_bind, mem_support_bind_iff] at hr0
      obtain ⟨⟨u, s'⟩, hst, hr0⟩ := hr0
      have hs' : s'.b = s.b := by
        cases qy with
        | inl n =>
          change (u, s') ∈ support ((StateT.lift (query (spec := unifSpec) n)).run s) at hst
          simp only [StateT.run_lift, mem_support_bind_iff, support_pure, Set.mem_singleton_iff]
            at hst
          obtain ⟨_, -, h0⟩ := hst
          exact congrArg GameState.b (Prod.mk.inj h0).2
        | inr sq =>
          change (u, s') ∈ support ((oracleImplR sm 3 qep cfg sq).run s) at hst
          exact oracleImplR_preserves_b sm 3 qep cfg sq s hst
      exact (ih u s' r hr0).trans hs'
  have hbEq : s₁.b = b := hb_pres (initState sm.sendPart k b) (b', s₁) hr
  rw [hbEq]

end Reduction

end Computational.Proofs.Game.PromotedCostedReds.UniformStartDistinguisherProg
