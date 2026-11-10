/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Computational.Proofs.E2E.Dsl.DrSessionSim -- proof-setup: allow-public-import
public import Computational.Proofs.E2E.Dsl.SpqrSim -- proof-setup: allow-public-import
import Computational.Proofs.E2E.Dsl.SpqrSimChain
import Computational.Proofs.E2E.Dsl.SpqrSimHist

/-!
# Compositional Size Bounds for `SpqrSim` and `DrSessionSim`

Proves closed-form `ReductionDsl.Expr.size` and `ReductionDsl.Comp.size` upper bounds for the SPQR
V1 send/receive sub-programs, `DrSessionSim` state operations, Double Ratchet + SPQR V1 step
simulators, and the five `SM.oracleImplR` arm handlers.
-/

public section

set_option autoImplicit false

namespace Computational.Proofs.Game.PromotedCostedReds.DrSessionSimSize

open OracleSpec OracleComp
open ReductionDsl (Sig Ty Ops Iface Expr Comp bits)
open CryptoGames.SM (posTy posSender posEpoch posIdx posEq orE boolEq leN maxN minN
  isSomeE otherE sendsInE pGet pSet maxAccGet maxAccSet healedByE maxOptE)
open CryptoGames.LibsignalSession (Crypto PublicKey)
open CryptoVerification.LibsignalSpqrV1 (MlKem)
open CryptoVerification.LibsignalTripleRatchetRepr (uuidTryParse)
open CryptoVerification.E2E (Bytes serializedPartyAddresses)
open CryptoVerification.E2E.Costed (e2eSig e2eOps E2EPureOp GhostStT PlainT B U32 BV256 BV512 PK IdKey
  drSenderChainT drRecvChainT ghostPartsT recvResultT smQT smRT)
open Computational.Proofs.E2E.Dsl.SmReachInvParty (serializedPartyAddresses_length_le_128)
open Computational.Proofs.E2E.Dsl.TablesHonest (size_e2ePureOp size_e2eCryptoOp size_e2eCurveOp)
open Computational.Proofs.E2E.Dsl.DrSessionSimBookkeeping (bytesEqE recvResultRejE recvResultAccE
  smRWireE smRRecvE smRCorrE ratchetKeyAdmissibleE
  e2eRecTy e2eRecPos e2eRecMsg e2eRecCt e2eRecComp e2eRecMk
  e2eGsTy e2eGsSt e2eGsB e2eGsWin e2eGsEpoch e2eGsIdx e2eGsTL e2eGsTrans
  e2eGsChall e2eGsComp e2eGsMaxAcc e2eGsLeaks e2eGsCorrs e2eGsMk
  e2eInitGsE e2eGsSetWin e2eSafeChE e2eSafeInjE e2eLeakE e2eEpMgmtE
  e2eCompContainsE e2eChallContainsE e2eRecordE e2eDeleteE e2eAcceptE e2eTrivialE
  e2eCorrAllowedE e2eAfterCorrAllowedE e2eInWindowE e2eSendOKE e2eCorrOKE e2eInTransitE)
open Computational.Proofs.E2E.Dsl.SpqrSim (spqrDslHooks)
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
open Computational.Proofs.E2E.Dsl.DrSessionSimHooks (gpIsB gpVer gpLocId gpRemId gpRk gpPrevCtr
  gpPend gpEp gpCEps gpSc gpRcs gpPqSt gpMk optBytes32LitE sendAddrsE expectedAddrsE
  sessionVersionEffE drop1BE pushEvict5E getDZero5E findChainWithIdx5E replaceFirstChain5E
  takeSkippedFromListE advanceSingleChainC)
open Computational.Proofs.E2E.Dsl.DrSessionSimSend (drSendPreE drSendPostE drSendC)
open Computational.Proofs.E2E.Dsl.DrSessionSimRecv (drRecvMsgT drRatchetMidT drChainActiveT
  drRecvConsumeOutT drRecvPreE drRecvDhStepE drRecvChainSetupE
  drRecvTakeSkippedE drRecvAfterAdvE drRecvConsumeC drRecvFinishE drReceiveC)
open Computational.Proofs.E2E.Dsl.DrSessionSim (E2ECoinSamplers e2eSamIfNec512C drTrArmC drChArmC
  drDlArmC drIjArmC drCrArmC drOracleStepC)

private def esizeHide {S0 : Sig} {O : Ops S0} {Γ : List (Ty S0)} {t : Ty S0}
    (e : Expr O Γ t) (ub : ℕ) : ℕ := min e.size ub

private def csizeHide {S0 : Sig} {O : Ops S0} {ι : Type} {T : OracleSpec ι}
    {I : Iface S0 T} {Γ : List (Ty S0)} {t : Ty S0} (c : Comp O I Γ t) (ub : ℕ) : ℕ :=
  min c.size ub

private theorem esize_eq_hide {S0 : Sig} {O : Ops S0} {Γ : List (Ty S0)} {t : Ty S0}
    {e : Expr O Γ t} {ub : ℕ} (h : e.size ≤ ub) : e.size = esizeHide e ub :=
  (Nat.min_eq_left h).symm

private theorem csize_eq_hide {S0 : Sig} {O : Ops S0} {ι : Type} {T : OracleSpec ι}
    {I : Iface S0 T} {Γ : List (Ty S0)} {t : Ty S0} {c : Comp O I Γ t} {ub : ℕ}
    (h : c.size ≤ ub) : c.size = csizeHide c ub :=
  (Nat.min_eq_left h).symm

private theorem esizeHide_def {S0 : Sig} {O : Ops S0} {Γ : List (Ty S0)} {t : Ty S0}
    (e : Expr O Γ t) (ub : ℕ) : esizeHide e ub = min e.size ub := rfl

private theorem csizeHide_def {S0 : Sig} {O : Ops S0} {ι : Type} {T : OracleSpec ι}
    {I : Iface S0 T} {Γ : List (Ty S0)} {t : Ty S0} (c : Comp O I Γ t) (ub : ℕ) :
    csizeHide c ub = min c.size ub := rfl

section SizeBounds
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option maxRecDepth 8192
attribute [local irreducible] esizeHide csizeHide
attribute [local simp] Expr.size Comp.size E2EPureOp.opSize
  Expr.v0 Expr.v1 Expr.v2 Expr.v3 Expr.v4 Expr.v5 Expr.v6

@[local simp] private theorem bits_c0 : bits 0 = 1 := by decide
@[local simp] private theorem bits_c1 : bits 1 = 1 := by decide
@[local simp] private theorem bits_c2 : bits 2 = 2 := by decide
@[local simp] private theorem bits_c3 : bits 3 = 2 := by decide
@[local simp] private theorem bits_c4 : bits 4 = 3 := by decide
@[local simp] private theorem bits_c5 : bits 5 = 3 := by decide
@[local simp] private theorem bits_c8 : bits 8 = 4 := by decide
@[local simp] private theorem bits_c10 : bits 10 = 4 := by decide
@[local simp] private theorem bits_c11 : bits 11 = 4 := by decide
@[local simp] private theorem bits_c12 : bits 12 = 4 := by decide
@[local simp] private theorem bits_c16 : bits 16 = 5 := by decide
@[local simp] private theorem bits_c32 : bits 32 = 6 := by decide
@[local simp] private theorem bits_c35 : bits 35 = 6 := by decide
@[local simp] private theorem bits_c36 : bits 36 = 6 := by decide
@[local simp] private theorem bits_c64 : bits 64 = 7 := by decide
@[local simp] private theorem bits_c256 : bits 256 = 9 := by decide
@[local simp] private theorem bits_c1568 : bits 1568 = 11 := by decide
@[local simp] private theorem bits_c2000 : bits 2000 = 11 := by decide
@[local simp] private theorem bits_c2201 : bits 2201 = 12 := by decide
@[local simp] private theorem bits_c3168 : bits 3168 = 12 := by decide
@[local simp] private theorem bits_c4201 : bits 4201 = 13 := by decide
@[local simp] private theorem bits_c25000 : bits 25000 = 15 := by decide

/-! ## `SpqrSim` size bounds -/

section SpqrSimSize
variable {ℓ : ℕ} {Pt : Type} {P : SignalPqxdh.Primitives} {C : Crypto} {K : MlKem}
  {decT : PublicKey → Option Pt} {encT : Pt → PublicKey}
  {ι : Type} {T : OracleSpec ι} (I : Iface (e2eSig ℓ) T)

@[local simp] private theorem csize_spqrNegotiateInitC {Γ} (a) :
    (spqrNegotiateInitC (P := P) (C := C) (K := K) (decT := decT) (encT := encT)
      I (Γ := Γ) a).size =
      csizeHide (spqrNegotiateInitC (P := P) (C := C) (K := K) (decT := decT) (encT := encT)
        I (Γ := Γ) a) (a.size + 50) :=
  csize_eq_hide (by simp [spqrNegotiateInitC])

@[local simp] private theorem csize_spqrBraidSendC {Γ} (a) :
    (spqrBraidSendC (P := P) (C := C) (K := K) (decT := decT) (encT := encT)
      I (Γ := Γ) a).size =
      csizeHide (spqrBraidSendC (P := P) (C := C) (K := K) (decT := decT) (encT := encT)
        I (Γ := Γ) a) (a.size + 50) :=
  csize_eq_hide (by simp [spqrBraidSendC])

@[local simp] private theorem csize_spqrBraidRecvC {Γ} (a) :
    (spqrBraidRecvC (P := P) (C := C) (K := K) (decT := decT) (encT := encT)
      I (Γ := Γ) a).size =
      csizeHide (spqrBraidRecvC (P := P) (C := C) (K := K) (decT := decT) (encT := encT)
        I (Γ := Γ) a) (a.size + 50) :=
  csize_eq_hide (by simp [spqrBraidRecvC])

@[local simp] private theorem csize_spqrChainFromVnC {Γ} (a) :
    (spqrChainFromVnC (P := P) (C := C) (K := K) (decT := decT) (encT := encT)
      I (Γ := Γ) a).size =
      csizeHide (spqrChainFromVnC (P := P) (C := C) (K := K) (decT := decT) (encT := encT)
        I (Γ := Γ) a) (a.size + 50) :=
  csize_eq_hide (by simp [spqrChainFromVnC])

@[local simp] private theorem csize_spqrChainAddEpochC {Γ} (a) :
    (spqrChainAddEpochC (P := P) (C := C) (K := K) (decT := decT) (encT := encT)
      I (Γ := Γ) a).size =
      csizeHide (spqrChainAddEpochC (P := P) (C := C) (K := K) (decT := decT) (encT := encT)
        I (Γ := Γ) a) (a.size + 50) :=
  csize_eq_hide (by simp [spqrChainAddEpochC])

@[local simp] private theorem csize_spqrChainNextKeyC {Γ} (a) :
    (spqrChainNextKeyC (P := P) (C := C) (K := K) (decT := decT) (encT := encT)
      I (Γ := Γ) a).size =
      csizeHide (spqrChainNextKeyC (P := P) (C := C) (K := K) (decT := decT) (encT := encT)
        I (Γ := Γ) a) (a.size + 50) :=
  csize_eq_hide (by simp [spqrChainNextKeyC])

@[local simp] private theorem esize_clearLinkSendNextExpr {Γ} (lk) :
    (clearLinkSendNextExpr (ℓ := ℓ) (P := P) (C := C) (K := K) (decT := decT) (encT := encT)
      (Γ := Γ) lk).size =
      esizeHide (clearLinkSendNextExpr (ℓ := ℓ) (P := P) (C := C) (K := K) (decT := decT)
        (encT := encT) (Γ := Γ) lk) (lk.size + 500) :=
  esize_eq_hide (by simp [clearLinkSendNextExpr])

@[local simp] private theorem csize_spqrChainSendKeyComp {Γ} (ch epoch) :
    (spqrChainSendKeyComp (P := P) (C := C) (K := K) (decT := decT) (encT := encT)
      I (Γ := Γ) ch epoch).size =
      csizeHide (spqrChainSendKeyComp (P := P) (C := C) (K := K) (decT := decT) (encT := encT)
        I (Γ := Γ) ch epoch) (ch.size + epoch.size + 10000) :=
  csize_eq_hide (by
    simp [spqrChainSendKeyComp, spqrEpochIdxExpr, linksClearSendPrefixExpr,
      listDropExpr, listGetExpr, listSetExpr]
    simp only [esizeHide_def, csizeHide_def]; omega)

@[local simp] private theorem esize_spqrListRevExpr {Γ} {t : Ty (e2eSig ℓ)} (cap : ℕ)
    (dflt : Expr (e2eOps ℓ P C K decT encT) Γ t)
    (l : Expr (e2eOps ℓ P C K decT encT) Γ (.list t)) :
    (spqrListRevExpr cap dflt l).size =
      esizeHide (spqrListRevExpr cap dflt l) (dflt.size + l.size + 6 * bits cap + 900) :=
  esize_eq_hide (by simp [spqrListRevExpr]; omega)

@[local simp] private theorem esize_spqrPrevGetExpr {Γ} (entries tail atIdx curCtr maxOoo) :
    (spqrPrevGetExpr (ℓ := ℓ) (P := P) (C := C) (K := K) (decT := decT) (encT := encT)
      (Γ := Γ) entries tail atIdx curCtr maxOoo).size =
      esizeHide (spqrPrevGetExpr (ℓ := ℓ) (P := P) (C := C) (K := K) (decT := decT) (encT := encT)
        (Γ := Γ) entries tail atIdx curCtr maxOoo)
        (entries.size + tail.size + atIdx.size + curCtr.size + maxOoo.size + 4500) :=
  esize_eq_hide (by simp [spqrPrevGetExpr, spqrPrevGetFuelExpr, listGetExpr, listSetExpr]; omega)

@[local simp] private theorem esize_spqrPrevGcExpr {Γ} (entries curKey maxOoo trimSize) :
    (spqrPrevGcExpr (ℓ := ℓ) (P := P) (C := C) (K := K) (decT := decT) (encT := encT)
      (Γ := Γ) entries curKey maxOoo trimSize).size =
      esizeHide (spqrPrevGcExpr (ℓ := ℓ) (P := P) (C := C) (K := K) (decT := decT) (encT := encT)
        (Γ := Γ) entries curKey maxOoo trimSize)
        (entries.size + curKey.size + maxOoo.size + trimSize.size + 5000) :=
  esize_eq_hide (by simp [spqrPrevGcExpr, spqrPrevGcFuelExpr]; omega)

@[local simp] private theorem csize_spqrKeyAdvanceComp {Γ} (ctr0 next0 entries0 atIdx maxOoo) :
    (spqrKeyAdvanceComp (P := P) (C := C) (K := K) (decT := decT) (encT := encT)
      I (Γ := Γ) ctr0 next0 entries0 atIdx maxOoo).size =
      csizeHide (spqrKeyAdvanceComp (P := P) (C := C) (K := K) (decT := decT) (encT := encT)
        I (Γ := Γ) ctr0 next0 entries0 atIdx maxOoo)
        (ctr0.size + next0.size + entries0.size + atIdx.size + maxOoo.size + 6000) :=
  csize_eq_hide (by
    simp [spqrKeyAdvanceComp, spqrKeyAdvanceFuelComp, spqrKeyAdvanceStep]
    simp only [esizeHide_def, csizeHide_def]; omega)

@[local simp] private theorem csize_spqrDirKeyComp {Γ} (recvDir atIdx maxJump maxOoo trimSize) :
    (spqrDirKeyComp (P := P) (C := C) (K := K) (decT := decT) (encT := encT)
      I (Γ := Γ) recvDir atIdx maxJump maxOoo trimSize).size =
      csizeHide (spqrDirKeyComp (P := P) (C := C) (K := K) (decT := decT) (encT := encT)
        I (Γ := Γ) recvDir atIdx maxJump maxOoo trimSize)
        (recvDir.size + atIdx.size + maxJump.size + maxOoo.size + trimSize.size + 20000) :=
  csize_eq_hide (by
    simp [spqrDirKeyComp, spqrDirKeyFwdComp]
    simp only [esizeHide_def, csizeHide_def]; omega)

@[local simp] private theorem csize_spqrChainRecvKeyComp {Γ} (ch epoch index) :
    (spqrChainRecvKeyComp (P := P) (C := C) (K := K) (decT := decT) (encT := encT)
      I (Γ := Γ) ch epoch index).size =
      csizeHide (spqrChainRecvKeyComp (P := P) (C := C) (K := K) (decT := decT) (encT := encT)
        I (Γ := Γ) ch epoch index) (ch.size + epoch.size + index.size + 28000) :=
  csize_eq_hide (by
    simp [spqrChainRecvKeyComp, spqrEpochIdxExpr, listGetExpr, listSetExpr]
    simp only [esizeHide_def, csizeHide_def]; omega)

@[local simp] private theorem csize_spqrResolveChainComp {Γ} (vn? ch?) :
    (spqrResolveChainComp (P := P) (C := C) (K := K) (decT := decT) (encT := encT)
      I (Γ := Γ) vn? ch?).size =
      csizeHide (spqrResolveChainComp (P := P) (C := C) (K := K) (decT := decT) (encT := encT)
        I (Γ := Γ) vn? ch?) (vn?.size + ch?.size + 100) :=
  csize_eq_hide (by simp [spqrResolveChainComp]; simp only [csizeHide_def]; omega)

@[local simp] private theorem csize_spqrAddEpochOptComp {Γ} (ch epSec?) :
    (spqrAddEpochOptComp (P := P) (C := C) (K := K) (decT := decT) (encT := encT)
      I (Γ := Γ) ch epSec?).size =
      csizeHide (spqrAddEpochOptComp (P := P) (C := C) (K := K) (decT := decT) (encT := encT)
        I (Γ := Γ) ch epSec?) (ch.size + epSec?.size + 100) :=
  csize_eq_hide (by simp [spqrAddEpochOptComp]; simp only [csizeHide_def]; omega)

@[local simp] private theorem csize_spqrRunSendChainComp {Γ} (vn? ch? epSec? epoch) :
    (spqrRunSendChainComp (P := P) (C := C) (K := K) (decT := decT) (encT := encT)
      I (Γ := Γ) vn? ch? epSec? epoch).size =
      csizeHide (spqrRunSendChainComp (P := P) (C := C) (K := K) (decT := decT) (encT := encT)
        I (Γ := Γ) vn? ch? epSec? epoch)
        (vn?.size + ch?.size + epSec?.size + epoch.size + 10500) :=
  csize_eq_hide (by simp [spqrRunSendChainComp]; simp only [csizeHide_def]; omega)

theorem spqrSendComp_size_le {Γ}
    (e : Expr (e2eOps ℓ P C K decT encT) Γ (.prod (B 32) BV512)) :
    (spqrSendComp I e).size ≤ e.size + 18000 := by
  simp [spqrSendComp]
  simp only [csizeHide_def]; omega

@[local simp] private theorem csize_spqrRecvGreaterComp {Γ} (parts msgIdx) :
    (spqrRecvGreaterComp (P := P) (C := C) (K := K) (decT := decT) (encT := encT)
      I (Γ := Γ) parts msgIdx).size =
      csizeHide (spqrRecvGreaterComp (P := P) (C := C) (K := K) (decT := decT) (encT := encT)
        I (Γ := Γ) parts msgIdx) (parts.size + msgIdx.size + 28500) :=
  csize_eq_hide (by simp [spqrRecvGreaterComp]; simp only [csizeHide_def]; omega)

@[local simp] private theorem csize_spqrRecvPrepStateComp {Γ} (parts msgVer curVer stillNeg) :
    (spqrRecvPrepStateComp (P := P) (C := C) (K := K) (decT := decT) (encT := encT)
      I (Γ := Γ) parts msgVer curVer stillNeg).size =
      csizeHide (spqrRecvPrepStateComp (P := P) (C := C) (K := K) (decT := decT) (encT := encT)
        I (Γ := Γ) parts msgVer curVer stillNeg)
        (parts.size + msgVer.size + curVer.size + stillNeg.size + 300) :=
  csize_eq_hide (by simp [spqrRecvPrepStateComp]; simp only [csizeHide_def]; omega)

@[local simp] private theorem csize_spqrRunRecvChainComp {Γ} (vn? ch? epSec? msgEpoch msgIdx) :
    (spqrRunRecvChainComp (P := P) (C := C) (K := K) (decT := decT) (encT := encT)
      I (Γ := Γ) vn? ch? epSec? msgEpoch msgIdx).size =
      csizeHide (spqrRunRecvChainComp (P := P) (C := C) (K := K) (decT := decT) (encT := encT)
        I (Γ := Γ) vn? ch? epSec? msgEpoch msgIdx)
        (vn?.size + ch?.size + epSec?.size + msgEpoch.size + msgIdx.size + 28500) :=
  csize_eq_hide (by simp [spqrRunRecvChainComp]; simp only [csizeHide_def]; omega)

@[local simp] private theorem csize_spqrRecvV1BodyComp {Γ} (stateParts msgEp msgIdx msgRem) :
    (spqrRecvV1BodyComp (P := P) (C := C) (K := K) (decT := decT) (encT := encT)
      I (Γ := Γ) stateParts msgEp msgIdx msgRem).size =
      csizeHide (spqrRecvV1BodyComp (P := P) (C := C) (K := K) (decT := decT) (encT := encT)
        I (Γ := Γ) stateParts msgEp msgIdx msgRem)
        (stateParts.size + msgEp.size + msgIdx.size + msgRem.size + 29000) :=
  csize_eq_hide (by simp [spqrRecvV1BodyComp]; simp only [csizeHide_def]; omega)

theorem spqrRecvComp_size_le {Γ}
    (e : Expr (e2eOps ℓ P C K decT encT) Γ (.prod (B 32) (B 32))) :
    (spqrRecvComp I e).size ≤ e.size + 75000 := by
  simp [spqrRecvComp, isSomeE]
  simp only [csizeHide_def]; omega

end SpqrSimSize

/-! ## `DrSessionSim` size bounds -/

section DrSimSize
variable {ℓ : ℕ} {Pt : Type} {P : SignalPqxdh.Primitives} {C : Crypto} {K : MlKem}
  {decT : PublicKey → Option Pt} {encT : Pt → PublicKey}

theorem size_optBytes32LitE_le {Γ : List (Ty (e2eSig ℓ))} (opt : Option Bytes)
    (h : ∀ bs ∈ opt, bs.length ≤ 128) :
    (optBytes32LitE (ℓ := ℓ) (P := P) (C := C) (K := K) (decT := decT) (encT := encT)
      (Γ := Γ) opt).size ≤ 132 := by
  cases opt with
  | none => simp [optBytes32LitE]
  | some bs =>
    have hbs := h bs rfl
    simp [optBytes32LitE]
    omega

private theorem esize_optBytes32LitE {Γ : List (Ty (e2eSig ℓ))}
    (opt : Option Bytes) (h : ∀ bs ∈ opt, bs.length ≤ 128) :
    (optBytes32LitE (ℓ := ℓ) (P := P) (C := C) (K := K) (decT := decT) (encT := encT)
      (Γ := Γ) opt).size =
      esizeHide (optBytes32LitE (ℓ := ℓ) (P := P) (C := C) (K := K) (decT := decT)
        (encT := encT) (Γ := Γ) opt) 132 :=
  esize_eq_hide (size_optBytes32LitE_le opt h)

@[local simp] private theorem esize_sendAddrsE {Γ : List (Ty (e2eSig ℓ))}
    (isB : Expr (e2eOps ℓ P C K decT encT) Γ .bool) :
    (sendAddrsE isB).size = esizeHide (sendAddrsE isB) (isB.size + 270) :=
  esize_eq_hide (by
    dsimp only [sendAddrsE, Expr.size]
    have hAB := size_optBytes32LitE_le (ℓ := ℓ) (P := P) (C := C) (K := K)
      (decT := decT) (encT := encT) (Γ := Γ)
      (serializedPartyAddresses uuidTryParse .A .B)
      (serializedPartyAddresses_length_le_128 uuidTryParse .A .B)
    have hBA := size_optBytes32LitE_le (ℓ := ℓ) (P := P) (C := C) (K := K)
      (decT := decT) (encT := encT) (Γ := Γ)
      (serializedPartyAddresses uuidTryParse .B .A)
      (serializedPartyAddresses_length_le_128 uuidTryParse .B .A)
    omega)

theorem size_sendAddrsE_le {Γ : List (Ty (e2eSig ℓ))}
    (isB : Expr (e2eOps ℓ P C K decT encT) Γ .bool) :
    (sendAddrsE isB).size ≤ isB.size + 270 := by
  simp [esize_sendAddrsE]; simp only [esizeHide_def]; omega

@[local simp] private theorem esize_expectedAddrsE {Γ : List (Ty (e2eSig ℓ))}
    (isB : Expr (e2eOps ℓ P C K decT encT) Γ .bool) :
    (expectedAddrsE isB).size = esizeHide (expectedAddrsE isB) (isB.size + 270) :=
  esize_eq_hide (by
    dsimp only [expectedAddrsE, Expr.size]
    have hAB := size_optBytes32LitE_le (ℓ := ℓ) (P := P) (C := C) (K := K)
      (decT := decT) (encT := encT) (Γ := Γ)
      (serializedPartyAddresses uuidTryParse .A .B)
      (serializedPartyAddresses_length_le_128 uuidTryParse .A .B)
    have hBA := size_optBytes32LitE_le (ℓ := ℓ) (P := P) (C := C) (K := K)
      (decT := decT) (encT := encT) (Γ := Γ)
      (serializedPartyAddresses uuidTryParse .B .A)
      (serializedPartyAddresses_length_le_128 uuidTryParse .B .A)
    omega)

theorem size_expectedAddrsE_le {Γ : List (Ty (e2eSig ℓ))}
    (isB : Expr (e2eOps ℓ P C K decT encT) Γ .bool) :
    (expectedAddrsE isB).size ≤ isB.size + 270 := by
  simp [esize_expectedAddrsE]; simp only [esizeHide_def]; omega

@[local simp] private theorem esize_pushEvict5E {O' : Ops (e2eSig ℓ)} {Γ t}
    (xs : Expr O' Γ (.list t)) (x : Expr O' Γ t) :
    (pushEvict5E xs x).size = esizeHide (pushEvict5E xs x) (xs.size + x.size + 60) :=
  esize_eq_hide (by simp [pushEvict5E, drop1BE])

theorem size_pushEvict5E_le {O' : Ops (e2eSig ℓ)} {Γ t}
    (xs : Expr O' Γ (.list t)) (x : Expr O' Γ t) :
    (pushEvict5E xs x).size ≤ xs.size + x.size + 60 := by
  simp [esize_pushEvict5E]; simp only [esizeHide_def]; omega

@[local simp] private theorem esize_getDZero5E {O' : Ops (e2eSig ℓ)} {Γ}
    (cEps : Expr O' Γ (.list .nat)) (idx : Expr O' Γ .nat) :
    (getDZero5E cEps idx).size = esizeHide (getDZero5E cEps idx) (cEps.size + idx.size + 50) :=
  esize_eq_hide (by simp [getDZero5E])

theorem size_getDZero5E_le {O' : Ops (e2eSig ℓ)} {Γ}
    (cEps : Expr O' Γ (.list .nat)) (idx : Expr O' Γ .nat) :
    (getDZero5E cEps idx).size ≤ cEps.size + idx.size + 50 := by
  simp [esize_getDZero5E]; simp only [esizeHide_def]; omega

@[local simp] private theorem esize_findChainWithIdx5E {Γ}
    (rcs : Expr (e2eOps ℓ P C K decT encT) Γ (.list drRecvChainT))
    (their : Expr (e2eOps ℓ P C K decT encT) Γ PK) :
    (findChainWithIdx5E rcs their).size =
      esizeHide (findChainWithIdx5E rcs their) (rcs.size + their.size + 60) :=
  esize_eq_hide (by simp [findChainWithIdx5E])

theorem size_findChainWithIdx5E_le {Γ}
    (rcs : Expr (e2eOps ℓ P C K decT encT) Γ (.list drRecvChainT))
    (their : Expr (e2eOps ℓ P C K decT encT) Γ PK) :
    (findChainWithIdx5E rcs their).size ≤ rcs.size + their.size + 60 := by
  simp [esize_findChainWithIdx5E]; simp only [esizeHide_def]; omega

@[local simp] private theorem esize_replaceFirstChain5E {Γ}
    (rcs : Expr (e2eOps ℓ P C K decT encT) Γ (.list drRecvChainT))
    (their : Expr (e2eOps ℓ P C K decT encT) Γ PK)
    (newRc : Expr (e2eOps ℓ P C K decT encT) Γ drRecvChainT) :
    (replaceFirstChain5E rcs their newRc).size =
      esizeHide (replaceFirstChain5E rcs their newRc) (rcs.size + their.size + newRc.size + 80) :=
  esize_eq_hide (by simp [replaceFirstChain5E]; omega)

theorem size_replaceFirstChain5E_le {Γ}
    (rcs : Expr (e2eOps ℓ P C K decT encT) Γ (.list drRecvChainT))
    (their : Expr (e2eOps ℓ P C K decT encT) Γ PK)
    (newRc : Expr (e2eOps ℓ P C K decT encT) Γ drRecvChainT) :
    (replaceFirstChain5E rcs their newRc).size ≤ rcs.size + their.size + newRc.size + 80 := by
  simp [esize_replaceFirstChain5E]; simp only [esizeHide_def]; omega

@[local simp] private theorem esize_takeSkippedFromListE {Γ}
    (mks : Expr (e2eOps ℓ P C K decT encT) Γ (.list (.prod BV256 U32)))
    (targetCtr : Expr (e2eOps ℓ P C K decT encT) Γ U32) :
    (takeSkippedFromListE mks targetCtr).size =
      esizeHide (takeSkippedFromListE mks targetCtr) (mks.size + targetCtr.size + 100) :=
  esize_eq_hide (by simp [takeSkippedFromListE])

theorem size_takeSkippedFromListE_le {Γ}
    (mks : Expr (e2eOps ℓ P C K decT encT) Γ (.list (.prod BV256 U32)))
    (targetCtr : Expr (e2eOps ℓ P C K decT encT) Γ U32) :
    (takeSkippedFromListE mks targetCtr).size ≤ mks.size + targetCtr.size + 100 := by
  simp [esize_takeSkippedFromListE]; simp only [esizeHide_def]; omega

@[local simp] private theorem csize_advanceSingleChainC {ι : Type} {T : OracleSpec ι}
    (I : Iface (e2eSig ℓ) T) {Γ}
    (ckInit : Expr (e2eOps ℓ P C K decT encT) Γ (.prod BV256 U32))
    (mksInit : Expr (e2eOps ℓ P C K decT encT) Γ (.list (.prod BV256 U32)))
    (targetCtr : Expr (e2eOps ℓ P C K decT encT) Γ U32) :
    (advanceSingleChainC I ckInit mksInit targetCtr).size =
      csizeHide (advanceSingleChainC I ckInit mksInit targetCtr)
        (ckInit.size + mksInit.size + targetCtr.size + 120) :=
  csize_eq_hide (by simp [advanceSingleChainC]; omega)

theorem advanceSingleChainC_size_le {ι : Type} {T : OracleSpec ι}
    (I : Iface (e2eSig ℓ) T) {Γ}
    (ckInit : Expr (e2eOps ℓ P C K decT encT) Γ (.prod BV256 U32))
    (mksInit : Expr (e2eOps ℓ P C K decT encT) Γ (.list (.prod BV256 U32)))
    (targetCtr : Expr (e2eOps ℓ P C K decT encT) Γ U32) :
    (advanceSingleChainC I ckInit mksInit targetCtr).size ≤
      ckInit.size + mksInit.size + targetCtr.size + 120 := by
  simp [csize_advanceSingleChainC]; simp only [csizeHide_def]; omega

@[local simp] private theorem esize_drSendPreE {Γ}
    (gE : Expr (e2eOps ℓ P C K decT encT) Γ GhostStT) :
    (drSendPreE gE).size = esizeHide (drSendPreE gE) (gE.size + 80) :=
  esize_eq_hide (by simp [drSendPreE, gpSc, gpVer, gpRemId, sessionVersionEffE])

@[local simp] private theorem esize_drSendPostE {Γ}
    (gE : Expr (e2eOps ℓ P C K decT encT) Γ GhostStT)
    (mE : Expr (e2eOps ℓ P C K decT encT) Γ PlainT)
    (partsE : Expr (e2eOps ℓ P C K decT encT) Γ ghostPartsT)
    (scE : Expr (e2eOps ℓ P C K decT encT) Γ drSenderChainT)
    (remIdE : Expr (e2eOps ℓ P C K decT encT) Γ IdKey)
    (pqOutE : Expr (e2eOps ℓ P C K decT encT) Γ (.prod (B 32) (.prod (.opt BV256) (B 32)))) :
    (drSendPostE gE mE partsE scE remIdE pqOutE).size =
      esizeHide (drSendPostE gE mE partsE scE remIdE pqOutE)
        (gE.size + mE.size + partsE.size + scE.size + remIdE.size + pqOutE.size + 600) :=
  esize_eq_hide (by
    simp [drSendPostE, sendsInE, gpIsB, gpVer, gpLocId, gpRemId, gpRk, gpPrevCtr, gpPend,
      gpEp, gpCEps, gpRcs, gpMk, sessionVersionEffE]
    simp only [esizeHide_def]; omega)

theorem drSendC_spqr_size_le {ι : Type} {T : OracleSpec ι} (I : Iface (e2eSig ℓ) T) {Γ}
    (e : Expr (e2eOps ℓ P C K decT encT) Γ (.prod GhostStT (.prod PlainT BV512))) :
    (drSendC (spqrDslHooks ℓ P C K decT encT) I e).size ≤ e.size + 19000 := by
  have hspqr := spqrSendComp_size_le (ℓ := ℓ) (P := P) (C := C) (K := K) (decT := decT)
    (encT := encT) I
    (.pair (gpPqSt (.fst .v0)) (.snd (.snd .v1)) :
      Expr (e2eOps ℓ P C K decT encT)
        (.prod ghostPartsT (.prod drSenderChainT IdKey) ::
          .prod GhostStT (.prod PlainT BV512) :: Γ) (.prod (B 32) BV512))
  simp [drSendC, spqrDslHooks, gpPqSt] at hspqr ⊢
  simp only [esizeHide_def]; omega

@[local simp] private theorem esize_drRecvPreE {Γ}
    (gE : Expr (e2eOps ℓ P C K decT encT) Γ GhostStT)
    (cE : Expr (e2eOps ℓ P C K decT encT) Γ (B 32)) :
    (drRecvPreE gE cE).size = esizeHide (drRecvPreE gE cE) (gE.size + cE.size + 100) :=
  esize_eq_hide (by simp [drRecvPreE, gpVer, gpRemId, sessionVersionEffE])

@[local simp] private theorem esize_drRecvDhStepE {Γ}
    (partsE : Expr (e2eOps ℓ P C K decT encT) Γ ghostPartsT)
    (theirE : Expr (e2eOps ℓ P C K decT encT) Γ PK)
    (rcCoinsE : Expr (e2eOps ℓ P C K decT encT) Γ BV256) :
    (drRecvDhStepE partsE theirE rcCoinsE).size =
      esizeHide (drRecvDhStepE partsE theirE rcCoinsE)
        (partsE.size + theirE.size + rcCoinsE.size + 350) :=
  esize_eq_hide (by
    simp [drRecvDhStepE, gpSc, gpRk, gpRcs, gpEp, gpCEps]
    simp only [esizeHide_def]; omega)

@[local simp] private theorem esize_drRecvChainSetupE {Γ}
    (partsE : Expr (e2eOps ℓ P C K decT encT) Γ ghostPartsT)
    (theirE : Expr (e2eOps ℓ P C K decT encT) Γ PK)
    (rcCoinsE : Expr (e2eOps ℓ P C K decT encT) Γ BV256) :
    (drRecvChainSetupE partsE theirE rcCoinsE).size =
      esizeHide (drRecvChainSetupE partsE theirE rcCoinsE)
        (partsE.size + theirE.size + rcCoinsE.size + 600) :=
  esize_eq_hide (by
    simp [drRecvChainSetupE, gpRk, gpPrevCtr, gpSc, gpRcs, gpEp, gpCEps]
    simp only [esizeHide_def]; omega)

@[local simp] private theorem esize_drRecvTakeSkippedE {Γ} (theirE msgCtrE rcs1E activeE) :
    (drRecvTakeSkippedE (ℓ := ℓ) (P := P) (C := C) (K := K) (decT := decT) (encT := encT)
      (Γ := Γ) theirE msgCtrE rcs1E activeE).size =
      esizeHide (drRecvTakeSkippedE (ℓ := ℓ) (P := P) (C := C) (K := K) (decT := decT)
        (encT := encT) (Γ := Γ) theirE msgCtrE rcs1E activeE)
        (theirE.size + msgCtrE.size + rcs1E.size + activeE.size + 250) :=
  esize_eq_hide (by simp [drRecvTakeSkippedE]; simp only [esizeHide_def]; omega)

@[local simp] private theorem esize_drRecvAfterAdvE {Γ} (theirE rcs1E advPairE) :
    (drRecvAfterAdvE (ℓ := ℓ) (P := P) (C := C) (K := K) (decT := decT) (encT := encT)
      (Γ := Γ) theirE rcs1E advPairE).size =
      esizeHide (drRecvAfterAdvE (ℓ := ℓ) (P := P) (C := C) (K := K) (decT := decT) (encT := encT)
        (Γ := Γ) theirE rcs1E advPairE)
        (theirE.size + rcs1E.size + advPairE.size + 150) :=
  esize_eq_hide (by simp [drRecvAfterAdvE]; simp only [esizeHide_def]; omega)

@[local simp] private theorem csize_drRecvConsumeC {ι : Type} {T : OracleSpec ι}
    (I : Iface (e2eSig ℓ) T) {Γ} (theirE msgCtrE rcs1E activeE) :
    (drRecvConsumeC (ℓ := ℓ) (P := P) (C := C) (K := K) (decT := decT) (encT := encT)
      I (Γ := Γ) theirE msgCtrE rcs1E activeE).size =
      csizeHide (drRecvConsumeC (ℓ := ℓ) (P := P) (C := C) (K := K) (decT := decT) (encT := encT)
        I (Γ := Γ) theirE msgCtrE rcs1E activeE)
        (theirE.size + msgCtrE.size + rcs1E.size + activeE.size + 650) :=
  csize_eq_hide (by
    simp [drRecvConsumeC]
    simp only [esizeHide_def, csizeHide_def]; omega)

@[local simp] private theorem esize_drRecvFinishE {Γ}
    (cE partsE remIdE msgCtrE msgCtE midE consOutE pqOutE) :
    (drRecvFinishE (ℓ := ℓ) (P := P) (C := C) (K := K) (decT := decT) (encT := encT)
      (Γ := Γ) cE partsE remIdE msgCtrE msgCtE midE consOutE pqOutE).size =
      esizeHide (drRecvFinishE (ℓ := ℓ) (P := P) (C := C) (K := K) (decT := decT) (encT := encT)
        (Γ := Γ) cE partsE remIdE msgCtrE msgCtE midE consOutE pqOutE)
        (cE.size + partsE.size + remIdE.size + msgCtrE.size + msgCtE.size +
          midE.size + consOutE.size + pqOutE.size + 550) :=
  esize_eq_hide (by
    simp [drRecvFinishE, gpIsB, gpVer, gpLocId, gpRemId, gpMk]
    simp only [esizeHide_def]; omega)

theorem drReceiveC_spqr_size_le {ι : Type} {T : OracleSpec ι}
    (I : Iface (e2eSig ℓ) T) {Γ}
    (e : Expr (e2eOps ℓ P C K decT encT) Γ (.prod GhostStT (.prod (B 32) BV256))) :
    (drReceiveC (spqrDslHooks ℓ P C K decT encT) I e).size ≤ e.size + 77000 := by
  let tIn : Ty (e2eSig ℓ) := .prod GhostStT (.prod (B 32) BV256)
  let tPreVal : Ty (e2eSig ℓ) := .prod ghostPartsT (.prod IdKey (drRecvMsgT ℓ))
  let tSetVal : Ty (e2eSig ℓ) := .prod (drRatchetMidT ℓ) (drChainActiveT ℓ)
  let tConsVal : Ty (e2eSig ℓ) := .prod (.prod BV256 U32) (.list drRecvChainT)
  have hspqr := spqrRecvComp_size_le (ℓ := ℓ) (P := P) (C := C) (K := K) (decT := decT)
    (encT := encT) I
    (.pair (gpPqSt (.fst .v3)) (.snd (.snd (.snd (.snd (.snd .v3))))) :
      Expr (e2eOps ℓ P C K decT encT)
        (tConsVal :: drRecvConsumeOutT ℓ :: tSetVal :: tPreVal :: tIn :: Γ)
        (.prod (B 32) (B 32)))
  simp [drReceiveC, spqrDslHooks, gpPqSt] at hspqr ⊢
  simp only [esizeHide_def, csizeHide_def]; omega

@[simp] theorem size_ratchetKeyAdmissibleE {Γ : List (Ty (e2eSig ℓ))}
    (c : Expr (e2eOps ℓ P C K decT encT) Γ (B 32)) :
    (ratchetKeyAdmissibleE c).size = c.size + 1 := rfl

@[simp] theorem size_recvResultRejE {O' : Ops (e2eSig ℓ)} {Γ : List (Ty (e2eSig ℓ))} :
    (recvResultRejE (ℓ := ℓ) (O' := O') (Γ := Γ)).size = 2 := rfl

theorem size_recvResultAccE_le {O' : Ops (e2eSig ℓ)} {Γ : List (Ty (e2eSig ℓ))}
    (t i : Expr O' Γ .nat) (m? : Expr O' Γ (.opt PlainT)) :
    (recvResultAccE t i m?).size ≤ t.size + i.size + m?.size + 4 := by
  simp [recvResultAccE]; omega

theorem size_smRWireE_le {O' : Ops (e2eSig ℓ)} {stT : Ty (e2eSig ℓ)} {Γ : List (Ty (e2eSig ℓ))}
    (w? : Expr O' Γ (.opt (B 32))) :
    (smRWireE (stT := stT) w?).size ≤ w?.size + 6 := by
  simp [smRWireE]

theorem size_smRRecvE_le {O' : Ops (e2eSig ℓ)} {stT : Ty (e2eSig ℓ)} {Γ : List (Ty (e2eSig ℓ))}
    (rr? : Expr O' Γ (.opt recvResultT)) :
    (smRRecvE (stT := stT) rr?).size ≤ rr?.size + 6 := by
  simp [smRRecvE]; omega

theorem size_smRCorrE_le {O' : Ops (e2eSig ℓ)} {stT : Ty (e2eSig ℓ)} {Γ : List (Ty (e2eSig ℓ))}
    (st? : Expr O' Γ (.opt stT)) :
    (smRCorrE st?).size ≤ st?.size + 6 := by
  simp [smRCorrE]; omega

@[local simp] private theorem esize_e2eInitGsE {O' : Ops (e2eSig ℓ)} {Γ}
    (stA stB : Expr O' Γ GhostStT) (b : Expr O' Γ .bool) :
    (e2eInitGsE stA stB b).size =
      esizeHide (e2eInitGsE stA stB b) (stA.size + stB.size + b.size + 50) :=
  esize_eq_hide (by simp [e2eInitGsE, e2eGsMk]; omega)

theorem size_e2eInitGsE_le {O' : Ops (e2eSig ℓ)} {Γ}
    (stA stB : Expr O' Γ GhostStT) (b : Expr O' Γ .bool) :
    (e2eInitGsE stA stB b).size ≤ stA.size + stB.size + b.size + 50 := by
  simp [esize_e2eInitGsE]; simp only [esizeHide_def]; omega

@[local simp] private theorem esize_e2eGsSetWin {O' : Ops (e2eSig ℓ)} {Γ}
    (s : Expr O' Γ (e2eGsTy ℓ)) (w : Expr O' Γ .bool) :
    (e2eGsSetWin s w).size = esizeHide (e2eGsSetWin s w) (s.size + w.size + 160) :=
  esize_eq_hide (by
    simp [e2eGsSetWin, e2eGsMk, e2eGsSt, e2eGsB, e2eGsEpoch, e2eGsIdx, e2eGsTL, e2eGsTrans,
      e2eGsChall, e2eGsComp, e2eGsMaxAcc, e2eGsLeaks, e2eGsCorrs])

theorem size_e2eGsSetWin_le {O' : Ops (e2eSig ℓ)} {Γ}
    (s : Expr O' Γ (e2eGsTy ℓ)) (w : Expr O' Γ .bool) :
    (e2eGsSetWin s w).size ≤ s.size + w.size + 160 := by
  simp [esize_e2eGsSetWin]; simp only [esizeHide_def]; omega

@[local simp] private theorem esize_e2eSafeChE {O' : Ops (e2eSig ℓ)} {Γ} (Δ : ℕ)
    (s : Expr O' Γ (e2eGsTy ℓ)) (p : Expr O' Γ .bool) :
    (e2eSafeChE Δ s p).size = esizeHide (e2eSafeChE Δ s p) (s.size + p.size + bits Δ + 50) :=
  esize_eq_hide (by simp [e2eSafeChE, healedByE, leN, e2eGsTL, e2eGsEpoch, pGet]; omega)

theorem size_e2eSafeChE_le {O' : Ops (e2eSig ℓ)} {Γ} (Δ : ℕ)
    (s : Expr O' Γ (e2eGsTy ℓ)) (p : Expr O' Γ .bool) :
    (e2eSafeChE Δ s p).size ≤ s.size + p.size + bits Δ + 50 := by
  simp [esize_e2eSafeChE]; simp only [esizeHide_def]; omega

@[local simp] private theorem esize_e2eSafeInjE {O' : Ops (e2eSig ℓ)} {Γ} (Δ : ℕ)
    (s : Expr O' Γ (e2eGsTy ℓ)) :
    (e2eSafeInjE Δ s).size = esizeHide (e2eSafeInjE Δ s) (s.size + bits Δ + 60) :=
  esize_eq_hide (by simp [e2eSafeInjE, healedByE, leN, minN, e2eGsTL, e2eGsEpoch]; omega)

theorem size_e2eSafeInjE_le {O' : Ops (e2eSig ℓ)} {Γ} (Δ : ℕ)
    (s : Expr O' Γ (e2eGsTy ℓ)) :
    (e2eSafeInjE Δ s).size ≤ s.size + bits Δ + 60 := by
  simp [esize_e2eSafeInjE]; simp only [esizeHide_def]; omega

@[local simp] private theorem esize_e2eLeakE {O' : Ops (e2eSig ℓ)} {Γ}
    (s : Expr O' Γ (e2eGsTy ℓ)) (l : Expr O' Γ .nat) :
    (e2eLeakE s l).size = esizeHide (e2eLeakE s l) (s.size + l.size + 180) :=
  esize_eq_hide (by
    simp [e2eLeakE, maxOptE, maxN, leN, e2eGsMk, e2eGsSt, e2eGsB, e2eGsWin, e2eGsEpoch,
      e2eGsIdx, e2eGsTL, e2eGsTrans, e2eGsChall, e2eGsComp, e2eGsMaxAcc, e2eGsLeaks,
      e2eGsCorrs])

theorem size_e2eLeakE_le {O' : Ops (e2eSig ℓ)} {Γ}
    (s : Expr O' Γ (e2eGsTy ℓ)) (l : Expr O' Γ .nat) :
    (e2eLeakE s l).size ≤ s.size + l.size + 250 := by
  simp [esize_e2eLeakE]; simp only [esizeHide_def]; omega

@[local simp] private theorem esize_e2eEpMgmtE {O' : Ops (e2eSig ℓ)} {Γ} (Δ qep : ℕ)
    (s : Expr O' Γ (e2eGsTy ℓ)) (p bad : Expr O' Γ .bool) :
    (e2eEpMgmtE Δ qep s p bad).size =
      esizeHide (e2eEpMgmtE Δ qep s p bad)
        (s.size + p.size + bad.size + bits Δ + 2 * bits qep + 600) :=
  esize_eq_hide (by
    simp [e2eEpMgmtE, sendsInE, pGet, pSet, e2eGsMk, e2eGsSt, e2eGsB, e2eGsWin,
      e2eGsEpoch, e2eGsIdx, e2eGsTL, e2eGsTrans, e2eGsChall, e2eGsComp, e2eGsMaxAcc,
      e2eGsLeaks, e2eGsCorrs]
    simp only [esizeHide_def]; omega)

theorem size_e2eEpMgmtE_le {O' : Ops (e2eSig ℓ)} {Γ} (Δ qep : ℕ)
    (s : Expr O' Γ (e2eGsTy ℓ)) (p bad : Expr O' Γ .bool) :
    (e2eEpMgmtE Δ qep s p bad).size ≤
      s.size + p.size + bad.size + bits Δ + 2 * bits qep + 600 := by
  simp [esize_e2eEpMgmtE]; simp only [esizeHide_def]; omega

@[local simp] private theorem esize_e2eCompContainsE {O' : Ops (e2eSig ℓ)} {Γ} (q : ℕ)
    (s : Expr O' Γ (e2eGsTy ℓ)) (pos : Expr O' Γ posTy) :
    (e2eCompContainsE q s pos).size =
      esizeHide (e2eCompContainsE q s pos) (s.size + pos.size + bits q + 50) :=
  esize_eq_hide (by simp [e2eCompContainsE, e2eGsComp, posEq, posSender, posEpoch, posIdx, boolEq]; omega)

theorem size_e2eCompContainsE_le {O' : Ops (e2eSig ℓ)} {Γ} (q : ℕ)
    (s : Expr O' Γ (e2eGsTy ℓ)) (pos : Expr O' Γ posTy) :
    (e2eCompContainsE q s pos).size ≤ s.size + pos.size + bits q + 50 := by
  simp [esize_e2eCompContainsE]; simp only [esizeHide_def]; omega

@[local simp] private theorem esize_e2eChallContainsE {O' : Ops (e2eSig ℓ)} {Γ} (q : ℕ)
    (s : Expr O' Γ (e2eGsTy ℓ)) (pos : Expr O' Γ posTy) :
    (e2eChallContainsE q s pos).size =
      esizeHide (e2eChallContainsE q s pos) (s.size + pos.size + bits q + 50) :=
  esize_eq_hide (by simp [e2eChallContainsE, e2eGsChall, posEq, posSender, posEpoch, posIdx, boolEq]; omega)

theorem size_e2eChallContainsE_le {O' : Ops (e2eSig ℓ)} {Γ} (q : ℕ)
    (s : Expr O' Γ (e2eGsTy ℓ)) (pos : Expr O' Γ posTy) :
    (e2eChallContainsE q s pos).size ≤ s.size + pos.size + bits q + 50 := by
  simp [esize_e2eChallContainsE]; simp only [esizeHide_def]; omega

@[local simp] private theorem esize_e2eRecordE {O' : Ops (e2eSig ℓ)} {Γ} (q Δ : ℕ)
    (s : Expr O' Γ (e2eGsTy ℓ)) (p : Expr O' Γ .bool) (st' : Expr O' Γ GhostStT)
    (pos : Expr O' Γ posTy) (msg : Expr O' Γ PlainT) (ct : Expr O' Γ (B 32))
    (isChall : Expr O' Γ .bool) :
    (e2eRecordE q Δ s p st' pos msg ct isChall).size =
      esizeHide (e2eRecordE q Δ s p st' pos msg ct isChall)
        (s.size + p.size + st'.size + pos.size + msg.size + ct.size + isChall.size +
          2 * bits q + bits Δ + 600) :=
  esize_eq_hide (by
    simp [e2eRecordE, e2eGsMk, e2eRecMk, e2eRecPos, e2eRecMsg, e2eRecCt, e2eRecComp,
      e2eGsSt, e2eGsB, e2eGsWin, e2eGsEpoch, e2eGsIdx, e2eGsTL, e2eGsTrans, e2eGsChall,
      e2eGsComp, e2eGsMaxAcc, e2eGsLeaks, e2eGsCorrs, pSet, posEq, posSender, posEpoch,
      posIdx, boolEq, orE]
    simp only [esizeHide_def]; omega)

theorem size_e2eRecordE_le {O' : Ops (e2eSig ℓ)} {Γ} (q Δ : ℕ)
    (s : Expr O' Γ (e2eGsTy ℓ)) (p : Expr O' Γ .bool) (st' : Expr O' Γ GhostStT)
    (pos : Expr O' Γ posTy) (msg : Expr O' Γ PlainT) (ct : Expr O' Γ (B 32))
    (isChall : Expr O' Γ .bool) :
    (e2eRecordE q Δ s p st' pos msg ct isChall).size ≤
      s.size + p.size + st'.size + pos.size + msg.size + ct.size + isChall.size +
        2 * bits q + bits Δ + 600 := by
  simp [esize_e2eRecordE]; simp only [esizeHide_def]; omega

@[local simp] private theorem esize_e2eDeleteE {O' : Ops (e2eSig ℓ)} {Γ} (q : ℕ)
    (s : Expr O' Γ (e2eGsTy ℓ)) (pos : Expr O' Γ posTy) :
    (e2eDeleteE q s pos).size =
      esizeHide (e2eDeleteE q s pos) (s.size + pos.size + 3 * bits q + 250) :=
  esize_eq_hide (by
    simp [e2eDeleteE, e2eGsMk, e2eRecPos, e2eGsSt, e2eGsB, e2eGsWin, e2eGsEpoch, e2eGsIdx,
      e2eGsTL, e2eGsTrans, e2eGsChall, e2eGsComp, e2eGsMaxAcc, e2eGsLeaks, e2eGsCorrs,
      posEq, posSender, posEpoch, posIdx, boolEq]; omega)

theorem size_e2eDeleteE_le {O' : Ops (e2eSig ℓ)} {Γ} (q : ℕ)
    (s : Expr O' Γ (e2eGsTy ℓ)) (pos : Expr O' Γ posTy) :
    (e2eDeleteE q s pos).size ≤ s.size + pos.size + 3 * bits q + 400 := by
  simp [esize_e2eDeleteE]; simp only [esizeHide_def]; omega

@[local simp] private theorem esize_e2eAcceptE {O' : Ops (e2eSig ℓ)} {Γ} (q : ℕ)
    (s : Expr O' Γ (e2eGsTy ℓ)) (p : Expr O' Γ .bool) (st' : Expr O' Γ GhostStT)
    (pos : Expr O' Γ posTy) :
    (e2eAcceptE q s p st' pos).size =
      esizeHide (e2eAcceptE q s p st' pos)
        (s.size + p.size + st'.size + 2 * pos.size + 3 * bits q + 700) :=
  esize_eq_hide (by
    simp [e2eAcceptE, e2eGsMk, e2eGsSt, e2eGsB, e2eGsWin, e2eGsEpoch, e2eGsIdx, e2eGsTL,
      e2eGsTrans, e2eGsChall, e2eGsComp, e2eGsMaxAcc, e2eGsLeaks, e2eGsCorrs, pSet, pGet,
      maxAccSet, maxAccGet, maxN, leN, posEpoch, posIdx]
    simp only [esizeHide_def]; omega)

theorem size_e2eAcceptE_le {O' : Ops (e2eSig ℓ)} {Γ} (q : ℕ)
    (s : Expr O' Γ (e2eGsTy ℓ)) (p : Expr O' Γ .bool) (st' : Expr O' Γ GhostStT)
    (pos : Expr O' Γ posTy) :
    (e2eAcceptE q s p st' pos).size ≤
      s.size + p.size + st'.size + 2 * pos.size + 3 * bits q + 700 := by
  simp [esize_e2eAcceptE]; simp only [esizeHide_def]; omega

@[local simp] private theorem esize_e2eTrivialE {O' : Ops (e2eSig ℓ)} {Γ} (q Δ : ℕ)
    (s : Expr O' Γ (e2eGsTy ℓ)) (pos : Expr O' Γ posTy) :
    (e2eTrivialE q Δ s pos).size =
      esizeHide (e2eTrivialE q Δ s pos) (s.size + pos.size + 2 * bits q + bits Δ + 200) :=
  esize_eq_hide (by
    simp [e2eTrivialE, e2eGsTrans, e2eGsTL, e2eRecPos, healedByE, leN, posEq, posSender,
      posEpoch, posIdx, boolEq, orE]
    simp only [esizeHide_def]; omega)

theorem size_e2eTrivialE_le {O' : Ops (e2eSig ℓ)} {Γ} (q Δ : ℕ)
    (s : Expr O' Γ (e2eGsTy ℓ)) (pos : Expr O' Γ posTy) :
    (e2eTrivialE q Δ s pos).size ≤ s.size + pos.size + 2 * bits q + bits Δ + 200 := by
  simp [esize_e2eTrivialE]; simp only [esizeHide_def]; omega

@[local simp] private theorem esize_e2eCorrAllowedE {O' : Ops (e2eSig ℓ)} {Γ} (q : ℕ)
    (s : Expr O' Γ (e2eGsTy ℓ)) (p : Expr O' Γ .bool) :
    (e2eCorrAllowedE q s p).size =
      esizeHide (e2eCorrAllowedE q s p) (s.size + p.size + 2 * bits q + 150) :=
  esize_eq_hide (by
    simp [e2eCorrAllowedE, e2eGsChall, e2eGsTrans, e2eRecPos, e2eRecComp, posSender,
      otherE, boolEq]; omega)

theorem size_e2eCorrAllowedE_le {O' : Ops (e2eSig ℓ)} {Γ} (q : ℕ)
    (s : Expr O' Γ (e2eGsTy ℓ)) (p : Expr O' Γ .bool) :
    (e2eCorrAllowedE q s p).size ≤ s.size + p.size + 2 * bits q + 150 := by
  simp [esize_e2eCorrAllowedE]; simp only [esizeHide_def]; omega

@[local simp] private theorem esize_e2eAfterCorrAllowedE {O' : Ops (e2eSig ℓ)} {Γ}
    (s : Expr O' Γ (e2eGsTy ℓ)) (p : Expr O' Γ .bool) :
    (e2eAfterCorrAllowedE s p).size =
      esizeHide (e2eAfterCorrAllowedE s p) (s.size + p.size + 450) :=
  esize_eq_hide (by
    simp [e2eAfterCorrAllowedE, maxN, leN, pGet, e2eGsMk, e2eGsSt, e2eGsB, e2eGsWin,
      e2eGsEpoch, e2eGsIdx, e2eGsTL, e2eGsTrans, e2eGsChall, e2eGsComp, e2eGsMaxAcc,
      e2eGsLeaks, e2eGsCorrs]
    simp only [esizeHide_def]; omega)

theorem size_e2eAfterCorrAllowedE_le {O' : Ops (e2eSig ℓ)} {Γ}
    (s : Expr O' Γ (e2eGsTy ℓ)) (p : Expr O' Γ .bool) :
    (e2eAfterCorrAllowedE s p).size ≤ s.size + p.size + 450 := by
  simp [esize_e2eAfterCorrAllowedE]; simp only [esizeHide_def]; omega

@[local simp] private theorem esize_e2eInWindowE {O' : Ops (e2eSig ℓ)} {Γ}
    (s : Expr O' Γ (e2eGsTy ℓ)) (p : Expr O' Γ .bool) :
    (e2eInWindowE s p).size = esizeHide (e2eInWindowE s p) (s.size + p.size + 50) :=
  esize_eq_hide (by simp [e2eInWindowE, sendsInE, pGet, e2eGsEpoch])

theorem size_e2eInWindowE_le {O' : Ops (e2eSig ℓ)} {Γ}
    (s : Expr O' Γ (e2eGsTy ℓ)) (p : Expr O' Γ .bool) :
    (e2eInWindowE s p).size ≤ s.size + p.size + 50 := by
  simp [esize_e2eInWindowE]; simp only [esizeHide_def]; omega

@[local simp] private theorem esize_e2eSendOKE {O' : Ops (e2eSig ℓ)} {Γ}
    (s : Expr O' Γ (e2eGsTy ℓ)) (p : Expr O' Γ .bool) :
    (e2eSendOKE s p).size = esizeHide (e2eSendOKE s p) (s.size + p.size + 30) :=
  esize_eq_hide (by simp [e2eSendOKE, e2eGsEpoch])

theorem size_e2eSendOKE_le {O' : Ops (e2eSig ℓ)} {Γ}
    (s : Expr O' Γ (e2eGsTy ℓ)) (p : Expr O' Γ .bool) :
    (e2eSendOKE s p).size ≤ s.size + p.size + 30 := by
  simp [esize_e2eSendOKE]; simp only [esizeHide_def]; omega

@[local simp] private theorem esize_e2eCorrOKE {O' : Ops (e2eSig ℓ)} {Γ}
    (s : Expr O' Γ (e2eGsTy ℓ)) (p : Expr O' Γ .bool) :
    (e2eCorrOKE s p).size = esizeHide (e2eCorrOKE s p) (s.size + p.size + 80) :=
  esize_eq_hide (by simp [e2eCorrOKE, e2eGsEpoch])

theorem size_e2eCorrOKE_le {O' : Ops (e2eSig ℓ)} {Γ}
    (s : Expr O' Γ (e2eGsTy ℓ)) (p : Expr O' Γ .bool) :
    (e2eCorrOKE s p).size ≤ s.size + p.size + 80 := by
  simp [esize_e2eCorrOKE]; simp only [esizeHide_def]; omega

@[local simp] private theorem esize_e2eInTransitE {Γ} (q : ℕ)
    (s : Expr (e2eOps ℓ P C K decT encT) Γ (e2eGsTy ℓ))
    (qParty : Expr (e2eOps ℓ P C K decT encT) Γ .bool)
    (c : Expr (e2eOps ℓ P C K decT encT) Γ (B 32)) :
    (e2eInTransitE q s qParty c).size =
      esizeHide (e2eInTransitE q s qParty c) (s.size + qParty.size + c.size + bits q + 100) :=
  esize_eq_hide (by
    simp [e2eInTransitE, e2eGsTrans, e2eRecPos, e2eRecCt, posSender, boolEq, bytesEqE]; omega)

theorem size_e2eInTransitE_le {Γ} (q : ℕ)
    (s : Expr (e2eOps ℓ P C K decT encT) Γ (e2eGsTy ℓ))
    (qParty : Expr (e2eOps ℓ P C K decT encT) Γ .bool)
    (c : Expr (e2eOps ℓ P C K decT encT) Γ (B 32)) :
    (e2eInTransitE q s qParty c).size ≤ s.size + qParty.size + c.size + bits q + 100 := by
  simp [esize_e2eInTransitE]; simp only [esizeHide_def]; omega

theorem drTrArmC_spqr_size_le {ι : Type} {T : OracleSpec ι} {I : Iface (e2eSig ℓ) T}
    (coins : E2ECoinSamplers ℓ P C K decT encT I)
    (h512 : ∀ {Γ}, (coins.draw512 (Γ := Γ)).size ≤ 4)
    (q Δ qep : ℕ) {Γ}
    (gsE : Expr (e2eOps ℓ P C K decT encT) Γ (e2eGsTy ℓ))
    (trArg : Expr (e2eOps ℓ P C K decT encT) Γ (.prod .bool (.prod PlainT (.opt BV512)))) :
    (drTrArmC (spqrDslHooks ℓ P C K decT encT) coins q Δ qep gsE trArg).size ≤
      gsE.size + trArg.size + 2 * bits q + 2 * bits Δ + 2 * bits qep + 20500 := by
  let t0 : Ty (e2eSig ℓ) := .prod (e2eGsTy ℓ) (.prod .bool (.prod PlainT (.opt BV512)))
  let t1 : Ty (e2eSig ℓ) := .prod BV512 .bool
  have hd := h512 (Γ := t0 :: Γ)
  have hsend := drSendC_spqr_size_le (ℓ := ℓ) (P := P) (C := C) (K := K) (decT := decT)
    (encT := encT) I
    (.pair (pGet (e2eGsSt .v0) (.fst (.snd .v2))) (.pair (.fst (.snd (.snd .v2))) (.fst .v1)) :
      Expr (e2eOps ℓ P C K decT encT) (e2eGsTy ℓ :: t1 :: t0 :: Γ)
        (.prod GhostStT (.prod PlainT BV512)))
  simp [drTrArmC, e2eSamIfNec512C, orE, e2eGsWin, smRWireE, pGet, e2eGsSt, e2eGsEpoch,
    e2eGsIdx] at hsend ⊢
  simp only [esizeHide_def]; omega

theorem drChArmC_spqr_size_le {ι : Type} {T : OracleSpec ι} {I : Iface (e2eSig ℓ) T}
    (coins : E2ECoinSamplers ℓ P C K decT encT I)
    (h512 : ∀ {Γ}, (coins.draw512 (Γ := Γ)).size ≤ 4)
    (q Δ qep : ℕ) {Γ}
    (gsE : Expr (e2eOps ℓ P C K decT encT) Γ (e2eGsTy ℓ))
    (chArg : Expr (e2eOps ℓ P C K decT encT) Γ
      (.prod .bool (.prod PlainT (.prod PlainT (.opt BV512))))) :
    (drChArmC (spqrDslHooks ℓ P C K decT encT) coins q Δ qep gsE chArg).size ≤
      gsE.size + chArg.size + 2 * bits q + 3 * bits Δ + 2 * bits qep + 21000 := by
  let t0 : Ty (e2eSig ℓ) :=
    .prod (e2eGsTy ℓ) (.prod .bool (.prod PlainT (.prod PlainT (.opt BV512))))
  let t1 : Ty (e2eSig ℓ) := .prod BV512 .bool
  have hd := h512 (Γ := t0 :: Γ)
  have hsend := drSendC_spqr_size_le (ℓ := ℓ) (P := P) (C := C) (K := K) (decT := decT)
    (encT := encT) I
    (.pair (pGet (e2eGsSt .v0) (.fst (.snd .v2)))
      (.pair (.ite (e2eGsB (.fst .v2)) (.fst (.snd (.snd (.snd .v2)))) (.fst (.snd (.snd .v2))))
        (.fst .v1)) :
      Expr (e2eOps ℓ P C K decT encT) (e2eGsTy ℓ :: t1 :: t0 :: Γ)
        (.prod GhostStT (.prod PlainT BV512)))
  simp [drChArmC, e2eSamIfNec512C, orE, e2eGsWin, e2eGsB, smRWireE, pGet, e2eGsSt, e2eGsEpoch,
    e2eGsIdx] at hsend ⊢
  simp only [esizeHide_def]; omega

theorem drDlArmC_spqr_size_le {ι : Type} {T : OracleSpec ι} {I : Iface (e2eSig ℓ) T}
    (coins : E2ECoinSamplers ℓ P C K decT encT I)
    (h256 : ∀ {Γ}, (coins.draw256 (Γ := Γ)).size ≤ 4)
    (q : ℕ) {Γ}
    (gsE : Expr (e2eOps ℓ P C K decT encT) Γ (e2eGsTy ℓ))
    (dlArg : Expr (e2eOps ℓ P C K decT encT) Γ (.prod .bool (B 32))) :
    (drDlArmC (spqrDslHooks ℓ P C K decT encT) coins q gsE dlArg).size ≤
      gsE.size + dlArg.size + 5 * bits q + 78500 := by
  have hd := h256 (Γ := e2eRecTy ℓ :: .prod (e2eGsTy ℓ) (.prod .bool (B 32)) :: Γ)
  have hrecv := drReceiveC_spqr_size_le (ℓ := ℓ) (P := P) (C := C) (K := K) (decT := decT)
    (encT := encT) I
    (.pair (pGet (e2eGsSt (.fst .v2)) (.fst (.snd .v2))) (.pair (.snd (.snd .v2)) .v0) :
      Expr (e2eOps ℓ P C K decT encT)
        (BV256 :: e2eRecTy ℓ :: .prod (e2eGsTy ℓ) (.prod .bool (B 32)) :: Γ)
        (.prod GhostStT (.prod (B 32) BV256)))
  simp [drDlArmC, e2eGsWin, otherE, smRRecvE, recvResultRejE, recvResultAccE, e2eRecPos,
    pGet, e2eGsSt] at hrecv ⊢
  simp only [esizeHide_def]; omega

theorem drIjArmC_spqr_size_le {ι : Type} {T : OracleSpec ι} {I : Iface (e2eSig ℓ) T}
    (coins : E2ECoinSamplers ℓ P C K decT encT I)
    (h256 : ∀ {Γ}, (coins.draw256 (Γ := Γ)).size ≤ 4)
    (q Δ qep : ℕ) {Γ}
    (gsE : Expr (e2eOps ℓ P C K decT encT) Γ (e2eGsTy ℓ))
    (ijArg : Expr (e2eOps ℓ P C K decT encT) Γ (.prod .bool (B 32))) :
    (drIjArmC (spqrDslHooks ℓ P C K decT encT) coins q Δ qep gsE ijArg).size ≤
      gsE.size + ijArg.size + 6 * bits q + 2 * bits Δ + bits (qep + 1) + 79000 := by
  have hd := h256 (Γ := .prod (e2eGsTy ℓ) (.prod .bool (B 32)) :: Γ)
  have hrecv := drReceiveC_spqr_size_le (ℓ := ℓ) (P := P) (C := C) (K := K) (decT := decT)
    (encT := encT) I
    (.pair (pGet (e2eGsSt (.fst .v1)) (.fst (.snd .v1))) (.pair (.snd (.snd .v1)) .v0) :
      Expr (e2eOps ℓ P C K decT encT)
        (BV256 :: .prod (e2eGsTy ℓ) (.prod .bool (B 32)) :: Γ)
        (.prod GhostStT (.prod (B 32) BV256)))
  simp [drIjArmC, orE, isSomeE, otherE, e2eGsWin, smRRecvE, recvResultRejE, recvResultAccE,
    pGet, e2eGsSt] at hrecv ⊢
  simp only [esizeHide_def]; omega

theorem drCrArmC_size_le {ι : Type} {T : OracleSpec ι} {I : Iface (e2eSig ℓ) T}
    (q : ℕ) {Γ}
    (gsE : Expr (e2eOps ℓ P C K decT encT) Γ (e2eGsTy ℓ))
    (crArg : Expr (e2eOps ℓ P C K decT encT) Γ .bool) :
    (drCrArmC (I := I) q gsE crArg).size ≤ gsE.size + crArg.size + 2 * bits q + 900 := by
  simp [drCrArmC, orE, e2eGsWin, smRCorrE, pGet, e2eGsSt]
  simp only [esizeHide_def]; omega

theorem drOracleStepC_spqr_size_le {ι : Type} {T : OracleSpec ι} {I : Iface (e2eSig ℓ) T}
    (coins : E2ECoinSamplers ℓ P C K decT encT I)
    (h256 : ∀ {Γ}, (coins.draw256 (Γ := Γ)).size ≤ 4)
    (h512 : ∀ {Γ}, (coins.draw512 (Γ := Γ)).size ≤ 4)
    (q Δ qep : ℕ) {Γ}
    (gsE : Expr (e2eOps ℓ P C K decT encT) Γ (e2eGsTy ℓ))
    (qryE : Expr (e2eOps ℓ P C K decT encT) Γ smQT) :
    (drOracleStepC (spqrDslHooks ℓ P C K decT encT) coins q Δ qep gsE qryE).size ≤
      gsE.size + qryE.size + 17 * bits q + 7 * bits Δ + 4 * bits qep +
        bits (qep + 1) + 200000 := by
  let tTop : Ty (e2eSig ℓ) := .prod (e2eGsTy ℓ) smQT
  let r1T : Ty (e2eSig ℓ) :=
    .sum (.prod .bool (.prod PlainT (.prod PlainT (.opt BV512))))
      (.sum (.prod .bool (B 32)) (.sum (.prod .bool (B 32)) .bool))
  let r2T : Ty (e2eSig ℓ) := .sum (.prod .bool (B 32)) (.sum (.prod .bool (B 32)) .bool)
  let r3T : Ty (e2eSig ℓ) := .sum (.prod .bool (B 32)) .bool
  have htr := drTrArmC_spqr_size_le (ℓ := ℓ) (P := P) (C := C) (K := K) (decT := decT)
    (encT := encT) coins h512 q Δ qep
    (.fst .v1 : Expr (e2eOps ℓ P C K decT encT)
      (.prod .bool (.prod PlainT (.opt BV512)) :: tTop :: Γ) (e2eGsTy ℓ)) .v0
  have hch := drChArmC_spqr_size_le (ℓ := ℓ) (P := P) (C := C) (K := K) (decT := decT)
    (encT := encT) coins h512 q Δ qep
    (.fst .v2 : Expr (e2eOps ℓ P C K decT encT)
      (.prod .bool (.prod PlainT (.prod PlainT (.opt BV512))) :: r1T :: tTop :: Γ) (e2eGsTy ℓ)) .v0
  have hdl := drDlArmC_spqr_size_le (ℓ := ℓ) (P := P) (C := C) (K := K) (decT := decT)
    (encT := encT) coins h256 q
    (.fst .v3 : Expr (e2eOps ℓ P C K decT encT)
      (.prod .bool (B 32) :: r2T :: r1T :: tTop :: Γ) (e2eGsTy ℓ)) .v0
  have hij := drIjArmC_spqr_size_le (ℓ := ℓ) (P := P) (C := C) (K := K) (decT := decT)
    (encT := encT) coins h256 q Δ qep
    (.fst .v4 : Expr (e2eOps ℓ P C K decT encT)
      (.prod .bool (B 32) :: r3T :: r2T :: r1T :: tTop :: Γ) (e2eGsTy ℓ)) .v0
  have hcr := drCrArmC_size_le (ℓ := ℓ) (P := P) (C := C) (K := K) (decT := decT)
    (encT := encT) (I := I) q
    (.fst .v4 : Expr (e2eOps ℓ P C K decT encT)
      (.bool :: r3T :: r2T :: r1T :: tTop :: Γ) (e2eGsTy ℓ)) .v0
  simp only [drOracleStepC, Comp.size, Expr.size, Expr.v0, Expr.v1, Expr.v2, Expr.v3,
    Expr.v4] at htr hch hdl hij hcr ⊢
  omega

end DrSimSize
end SizeBounds

end Computational.Proofs.Game.PromotedCostedReds.DrSessionSimSize
