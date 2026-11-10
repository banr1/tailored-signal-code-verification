/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Computational.Proofs.E2E.Dsl.LocalSessionStep -- proof-setup: allow-public-import
public import Computational.Proofs.E2E.Dsl.SpqrSim -- proof-setup: allow-public-import
public import Computational.Proofs.E2E.Dsl.DrSessionSim -- proof-setup: allow-public-import
import Computational.Proofs.ReductionDsl.SizeBudgetBridge

/-!
# Compositional Syntax-Size Bound for `stepLocalSmC`

Proves a closed-form `Comp.size` bound (`stepLocalSmSize`) for `LocalSessionStep.stepLocalSmC`
instantiated with `drSessionSimIface` and `spqrDslHooks`, linear in `bits` of
`(qStart, nCorr, nPrins, qBound, qep)`.
-/

public section

set_option autoImplicit false

namespace Computational.Proofs.E2E.Dsl.M3SessionSize

open _root_.ReductionDsl (Ty Ops Var Expr Comp Iface bits)
open Computational.Proofs.ReductionDsl.SizeBudgetBridge (bits_succ_le)
open CryptoGames.LibsignalSession (Crypto PublicKey)
open CryptoGames.SM (posSender posEpoch posIdx posEq boolEq leN maxN minN otherE sendsInE
  pGet pSet maxAccGet maxAccSet healedByE maxOptE)
open CryptoVerification.LibsignalSpqrV1 (MlKem)
open SignalPqxdh (Setup Primitives)
open CryptoVerification.E2E.Costed (E2EPureOp E2ECryptoOp e2eSig e2eOps B PB PU32 U8 U32
  BV128 BV256 BV512 PK IdKey PlainT GhostStT drSenderChainT drRecvChainT ghostPartsT
  smQT smRT)
open Computational.Proofs.E2E.Dsl.TablesHonest (e2ePureOp e2eCryptoOp size_e2eCurveOp)
open Computational.Proofs.E2E.Dsl.PqxdhSimTypes (Ext v stepAIface
  eLet eCaseOpt eCaseSum eAny letV bindV caseOptV orE isSomeE isNoneE optEqByE
  hdrIkA hdrEkA hdrSpkId hdrOpkId hdrPqId hdrKemCt)
open Computational.Proofs.E2E.Dsl.SpqrSimChain (spqrNegotiateInitC spqrBraidSendC spqrBraidRecvC
  spqrChainFromVnC spqrChainAddEpochC spqrChainNextKeyC
  listDropExpr listGetExpr listSetExpr spqrEpochIdxExpr
  spqrResolveChainComp spqrAddEpochOptComp clearLinkSendNextExpr linksClearSendPrefixExpr
  spqrChainSendKeyComp)
open Computational.Proofs.E2E.Dsl.SpqrSimSend (spqrRunSendChainComp spqrSendComp)
open Computational.Proofs.E2E.Dsl.SpqrSimHist (spqrListRevExpr
  spqrPrevGetFuelExpr spqrPrevGetExpr spqrPrevGcFuelExpr spqrPrevGcExpr
  spqrKeyAdvanceStep spqrKeyAdvanceFuelComp spqrKeyAdvanceComp
  spqrDirKeyFwdComp spqrDirKeyComp spqrChainRecvKeyComp)
open Computational.Proofs.E2E.Dsl.SpqrSimRecv (spqrRecvGreaterComp spqrRecvPrepStateComp
  spqrRunRecvChainComp spqrRecvV1BodyComp spqrRecvComp)
open Computational.Proofs.E2E.Dsl.SpqrSim (spqrDslHooks)
open Computational.Proofs.E2E.Dsl.DrSessionSimHooks (
  gpIsB gpVer gpLocId gpRemId gpRk gpPrevCtr gpPend gpEp gpCEps gpSc gpRcs gpPqSt gpMk
  optBytes32LitE sendAddrsE expectedAddrsE sessionVersionEffE
  drop1BE pushEvict5E getDZero5E findChainWithIdx5E replaceFirstChain5E
  takeSkippedFromListE advanceSingleChainC)
open Computational.Proofs.E2E.Dsl.SmReachInvParty (serializedPartyAddresses_length_le_128)
open Computational.Proofs.E2E.Dsl.DrSessionSimBookkeeping (bytesEqE ratchetKeyAdmissibleE
  recvResultRejE recvResultAccE smRWireE smRRecvE smRCorrE
  e2eRecTy e2eGsTy e2eRecPos e2eRecMsg e2eRecCt e2eRecComp e2eRecMk
  e2eGsSt e2eGsB e2eGsWin e2eGsEpoch e2eGsIdx e2eGsTL e2eGsTrans e2eGsChall e2eGsComp
  e2eGsMaxAcc e2eGsLeaks e2eGsCorrs e2eGsMk
  e2eGsSetWin e2eSafeChE e2eSafeInjE e2eLeakE e2eEpMgmtE
  e2eCompContainsE e2eChallContainsE e2eRecordE e2eDeleteE e2eAcceptE
  e2eTrivialE e2eCorrAllowedE e2eAfterCorrAllowedE e2eInWindowE
  e2eSendOKE e2eCorrOKE e2eInTransitE)
open Computational.Proofs.E2E.Dsl.DrSessionSimSend (drSendPreE drSendPostE drSendC)
open Computational.Proofs.E2E.Dsl.DrSessionSimRecv (drRecvPreE drRecvDhStepE drRecvChainSetupE
  drRecvTakeSkippedE drRecvAfterAdvE drRecvConsumeC drRecvFinishE drReceiveC)
open Computational.Proofs.E2E.Dsl.DrSessionSim (e2eStepACoinSamplers e2eSamIfNec512C
  drTrArmC drChArmC drDlArmC drIjArmC drCrArmC drOracleStepC drSessionSimIface)
open Computational.Proofs.E2E.Dsl.M3Interfaces (e2eInstMetaTy e2eModelInstTy e2eDrvStateTy
  respNotRevealedE)
open Computational.Proofs.E2E.Dsl.LocalSessionStepAux (emptySmRespE instSlotTy defaultE2eGsE
  e2eInstHdrMetaTy listGetOptE listSetE
  initPrinOptE initRegIdE hdrEqE isBobRecvSmQueryE isBobAcceptSmRespE
  setInstMetaAcceptE filterLocalSmQueryE)
open Computational.Proofs.E2E.Dsl.LocalSessionStep (corrTblOfListE instIkACorrTblE
  instIkACorrListE drvInstCleanDrvStateE modelInstToHmE modelInstToSlotE slotHmToModelInstE
  stepInstSlotC stepSingleInstC stepLocalSmC)

/-- Closed-form compositional `Comp.size` budget for one concrete `stepLocalSmC` query. -/
@[expose] def stepLocalSmSize (qStart nCorr nPrins qBound qep : ℕ) : ℕ :=
  6 * bits qStart + 2 * bits nCorr + bits nPrins + 17 * bits qBound + 5 * bits qep + 31000

section SizeLemmas

set_option linter.unusedSimpArgs false

variable {ℓ : ℕ} {S : Setup} {Pt : Type} {P : Primitives} {C : Crypto} {K : MlKem}
  {decT : PublicKey → Option Pt} {encT : Pt → PublicKey}
  {O : Ops (e2eSig ℓ)} {ι : Type} {T : OracleSpec ι}
  {I : Iface (e2eSig ℓ) T} {I₀ : Iface (e2eSig ℓ) T} {Γ : List (Ty (e2eSig ℓ))}

local notation "Sig" => e2eSig ℓ
local notation "OO" => e2eOps ℓ P C K decT encT

/-! ## Primitive, Binder, and Numeric `bits` Identities -/

@[local simp] private theorem hb0 : bits 0 = 1 := rfl
@[local simp] private theorem hb1 : bits 1 = 1 := rfl
@[local simp] private theorem hb2 : bits 2 = 2 := rfl
@[local simp] private theorem hb3 : bits 3 = 2 := rfl
@[local simp] private theorem hb4 : bits 4 = 3 := rfl
@[local simp] private theorem hb5 : bits 5 = 3 := rfl
@[local simp] private theorem hb10 : bits 10 = 4 := rfl
@[local simp] private theorem hb11 : bits 11 = 4 := by decide
@[local simp] private theorem hb32 : bits 32 = 6 := by decide
@[local simp] private theorem hb256 : bits 256 = 9 := by decide
@[local simp] private theorem hb2000 : bits 2000 = 11 := by decide
@[local simp] private theorem hb2201 : bits 2201 = 12 := by decide
@[local simp] private theorem hb4201 : bits 4201 = 13 := by decide
@[local simp] private theorem hb25000 : bits 25000 = 15 := by decide

@[local simp] private theorem size_v {Δ : List (Ty Sig)} [Ext Γ Δ] {τ : Ty Sig}
    (x : Var Γ τ) : (v (O := O) (Δ := Δ) x).size = 1 := by
  simp [v, Expr.size]

@[local simp] private theorem size_eLet {τ υ : Ty Sig}
    (e : Expr O Γ τ) (k : Var (τ :: Γ) τ → Expr O (τ :: Γ) υ) :
    (eLet e k).size = e.size + (k .zero).size + 1 := rfl

@[local simp] private theorem size_eCaseOpt {τ υ : Ty Sig}
    (e : Expr O Γ (.opt τ)) (n : Expr O Γ υ) (s : Var (τ :: Γ) τ → Expr O (τ :: Γ) υ) :
    (eCaseOpt e n s).size = e.size + n.size + (s .zero).size + 1 := by
  simp only [eCaseOpt, Expr.size]

@[local simp] private theorem size_eCaseSum {α β υ : Ty Sig}
    (e : Expr O Γ (.sum α β))
    (l : Var (α :: Γ) α → Expr O (α :: Γ) υ) (r : Var (β :: Γ) β → Expr O (β :: Γ) υ) :
    (eCaseSum e l r).size = e.size + (l .zero).size + (r .zero).size + 1 := by
  simp only [eCaseSum, Expr.size]

@[local simp] private theorem size_eAny {τ : Ty Sig} (n : ℕ)
    (l : Expr O Γ (.list τ)) (p : Var (τ :: Γ) τ → Expr O (τ :: Γ) .bool) :
    (eAny n l p).size = l.size + (p .zero).size + bits n + 1 := by
  simp only [eAny, Expr.size]

@[local simp] private theorem size_bindV {τ υ : Ty Sig}
    (c : Comp O I Γ τ) (k : Var (τ :: Γ) τ → Comp O I (τ :: Γ) υ) :
    (bindV c k).size = c.size + (k .zero).size + 1 := rfl

@[local simp] private theorem size_letV {τ υ : Ty Sig}
    (e : Expr O Γ τ) (k : Var (τ :: Γ) τ → Comp O I (τ :: Γ) υ) :
    (letV (I := I) e k).size = e.size + (k .zero).size + 2 := by
  simp only [letV, Comp.size]; omega

@[local simp] private theorem size_caseOptV {τ υ : Ty Sig}
    (e : Expr O Γ (.opt τ)) (n : Comp O I Γ υ) (s : Var (τ :: Γ) τ → Comp O I (τ :: Γ) υ) :
    (caseOptV e n s).size = e.size + n.size + (s .zero).size + 1 := by
  simp only [caseOptV, Comp.size]

@[local simp] private theorem size_pureOp_loc (o : E2EPureOp)
    (e : Expr OO Γ (o.dom ℓ)) :
    (e2ePureOp (P := P) (C := C) (K := K) (decT := decT) (encT := encT) o e).size =
      e.size + o.opSize + 1 := rfl

@[local simp] private theorem size_cryptoOp_loc (o : E2ECryptoOp)
    (e : Expr OO Γ (o.dom ℓ)) :
    (e2eCryptoOp (P := P) (C := C) (K := K) (decT := decT) (encT := encT) o e).size =
      e.size + 1 := rfl

@[local simp] private theorem size_var {τ : Ty Sig} (x : Var Γ τ) :
    (Expr.var (O := O) x).size = 1 := rfl

private theorem size_orE (a b : Expr O Γ .bool) : (orE a b).size = a.size + b.size + 4 := by
  simp only [orE, Expr.size]; omega

private theorem size_isSomeE {t : Ty Sig} (e : Expr O Γ (.opt t)) : (isSomeE e).size = e.size + 3 :=
  by simp only [isSomeE, Expr.size]

private theorem size_sm_orE (a b : Expr O Γ .bool) :
    (CryptoGames.SM.orE a b).size = a.size + b.size + 2 := by
  simp only [CryptoGames.SM.orE, Expr.size]; omega

private theorem size_sm_isSomeE {t : Ty Sig} (e : Expr O Γ (.opt t)) :
    (CryptoGames.SM.isSomeE e).size = e.size + 3 := by
  simp only [CryptoGames.SM.isSomeE, Expr.size]

private theorem le_size_letE {a b : Ty Sig} {A B : ℕ}
    {e : Expr O Γ a} {k : Expr O (a :: Γ) b}
    (h : A + e.size + 1 + k.size ≤ B) : A + (Expr.letE e k).size ≤ B := by
  simp only [Expr.size]; omega

private theorem le_size_letE_of {a b : Ty Sig} {A B E0 : ℕ}
    {e : Expr O Γ a} {k : Expr O (a :: Γ) b}
    (he : e.size ≤ E0) (h : A + E0 + 1 + k.size ≤ B) : A + (Expr.letE e k).size ≤ B := by
  simp only [Expr.size]; omega

private theorem le_size_caseOptE {a b : Ty Sig} {A B : ℕ}
    {e : Expr O Γ (.opt a)} {n : Expr O Γ b} {s : Expr O (a :: Γ) b}
    (h : A + e.size + n.size + 1 + s.size ≤ B) : A + (Expr.caseOpt e n s).size ≤ B := by
  simp only [Expr.size]; omega

private theorem le_size_caseOptE_of {a b : Ty Sig} {A B E0 : ℕ}
    {e : Expr O Γ (.opt a)} {n : Expr O Γ b} {s : Expr O (a :: Γ) b}
    (he : e.size ≤ E0) (h : A + E0 + n.size + 1 + s.size ≤ B) :
    A + (Expr.caseOpt e n s).size ≤ B := by
  simp only [Expr.size]; omega

private theorem le_size_caseOptE_none_of {a b : Ty Sig} {A B N0 : ℕ}
    {e : Expr O Γ (.opt a)} {n : Expr O Γ b} {s : Expr O (a :: Γ) b}
    (hn : n.size ≤ N0) (h : A + e.size + N0 + 1 + s.size ≤ B) :
    A + (Expr.caseOpt e n s).size ≤ B := by
  simp only [Expr.size]; omega

private theorem le_size_ret_of {a : Ty Sig} {A B E0 : ℕ} {e : Expr O Γ a}
    (he : e.size ≤ E0) (h : A + E0 + 1 ≤ B) : A + (Comp.ret (I := I) e).size ≤ B := by
  simp only [Comp.size]; omega

private theorem le_size_bind {a b : Ty Sig} {A B : ℕ}
    {c : Comp O I Γ a} {k : Comp O I (a :: Γ) b}
    (h : A + c.size + 1 + k.size ≤ B) : A + (Comp.bind c k).size ≤ B := by
  simp only [Comp.size]; omega

private theorem le_size_bind_of {a b : Ty Sig} {A B C0 : ℕ}
    {c : Comp O I Γ a} {k : Comp O I (a :: Γ) b}
    (hc : c.size ≤ C0) (h : A + C0 + 1 + k.size ≤ B) : A + (Comp.bind c k).size ≤ B := by
  simp only [Comp.size]; omega

private theorem le_size_caseOptC {a b : Ty Sig} {A B : ℕ}
    {e : Expr O Γ (.opt a)} {n : Comp O I Γ b} {s : Comp O I (a :: Γ) b}
    (h : A + e.size + n.size + 1 + s.size ≤ B) : A + (Comp.caseOpt e n s).size ≤ B := by
  simp only [Comp.size]; omega

private theorem le_size_caseOptC_of {a b : Ty Sig} {A B E0 : ℕ}
    {e : Expr O Γ (.opt a)} {n : Comp O I Γ b} {s : Comp O I (a :: Γ) b}
    (he : e.size ≤ E0) (h : A + E0 + n.size + 1 + s.size ≤ B) :
    A + (Comp.caseOpt e n s).size ≤ B := by
  simp only [Comp.size]; omega

private theorem le_size_iteC {a : Ty Sig} {A B : ℕ}
    {c : Expr O Γ .bool} {t f : Comp O I Γ a}
    (h : A + c.size + t.size + 1 + f.size ≤ B) : A + (Comp.ite c t f).size ≤ B := by
  simp only [Comp.size]; omega

private theorem le_size_iteC_of {a : Ty Sig} {A B C0 : ℕ}
    {c : Expr O Γ .bool} {t f : Comp O I Γ a}
    (hc : c.size ≤ C0) (h : A + C0 + t.size + 1 + f.size ≤ B) :
    A + (Comp.ite c t f).size ≤ B := by
  simp only [Comp.size]; omega

private theorem le_size_iteC_then {a : Ty Sig} {A B : ℕ} (T0 : ℕ)
    {c : Expr O Γ .bool} {t f : Comp O I Γ a}
    (ht : 0 + t.size ≤ T0) (hf : A + c.size + T0 + 1 + f.size ≤ B) :
    A + (Comp.ite c t f).size ≤ B := by
  simp only [Comp.size]; omega

private theorem le_size_iteC_both {a : Ty Sig} {A B C0 T0 F0 : ℕ}
    {c : Expr O Γ .bool} {t f : Comp O I Γ a}
    (hc : c.size ≤ C0) (ht : t.size ≤ T0) (hf : f.size ≤ F0)
    (h : A + C0 + T0 + 1 + F0 ≤ B) : A + (Comp.ite c t f).size ≤ B := by
  simp only [Comp.size]; omega

private theorem le_size_caseSumC_of {a b c : Ty Sig} {A B L0 : ℕ}
    {e : Expr O Γ (.sum a b)} {l : Comp O I (a :: Γ) c} {r : Comp O I (b :: Γ) c}
    (hl : l.size ≤ L0) (hr : A + e.size + L0 + 1 + r.size ≤ B) :
    A + (Comp.caseSum e l r).size ≤ B := by
  simp only [Comp.size]; omega

private theorem le_size_letV {a b : Ty Sig} {A B : ℕ}
    {e : Expr O Γ a} {k : Var (a :: Γ) a → Comp O I (a :: Γ) b}
    (h : A + e.size + 2 + (k .zero).size ≤ B) : A + (letV (I := I) e k).size ≤ B := by
  simp only [size_letV]; omega

private theorem le_size_letV_of {a b : Ty Sig} {A B E0 : ℕ}
    {e : Expr O Γ a} {k : Var (a :: Γ) a → Comp O I (a :: Γ) b}
    (he : e.size ≤ E0) (h : A + E0 + 2 + (k .zero).size ≤ B) :
    A + (letV (I := I) e k).size ≤ B := by
  simp only [size_letV]; omega

private theorem le_size_bindV_of {a b : Ty Sig} {A B C0 : ℕ}
    {c : Comp O I Γ a} {k : Var (a :: Γ) a → Comp O I (a :: Γ) b}
    (hc : c.size ≤ C0) (h : A + C0 + 1 + (k .zero).size ≤ B) :
    A + (bindV c k).size ≤ B := by
  simp only [size_bindV]; omega

private theorem le_size_caseOptV_of {a b : Ty Sig} {A B E0 : ℕ}
    {e : Expr O Γ (.opt a)} {n : Comp O I Γ b} {s : Var (a :: Γ) a → Comp O I (a :: Γ) b}
    (he : e.size ≤ E0) (h : A + E0 + n.size + 1 + (s .zero).size ≤ B) :
    A + (caseOptV e n s).size ≤ B := by
  simp only [size_caseOptV]; omega

/-! ## SPQR Chain, Send, History, and Receive `.size` Bounds -/

private theorem size_spqrBraidSendC (e : Expr OO Γ _) :
    (spqrBraidSendC (P := P) (C := C) (K := K) (decT := decT) (encT := encT) I e).size =
      e.size + 2 := rfl

private theorem size_spqrBraidRecvC (e : Expr OO Γ _) :
    (spqrBraidRecvC (P := P) (C := C) (K := K) (decT := decT) (encT := encT) I e).size =
      e.size + 2 := rfl

private theorem size_spqrNegotiateInitC (e : Expr OO Γ _) :
    (spqrNegotiateInitC (P := P) (C := C) (K := K) (decT := decT) (encT := encT) I e).size =
      e.size + 2 := rfl

private theorem size_spqrChainFromVnC (e : Expr OO Γ _) :
    (spqrChainFromVnC (P := P) (C := C) (K := K) (decT := decT) (encT := encT) I e).size =
      e.size + 2 := rfl

private theorem size_spqrChainAddEpochC (e : Expr OO Γ _) :
    (spqrChainAddEpochC (P := P) (C := C) (K := K) (decT := decT) (encT := encT) I e).size =
      e.size + 2 := rfl

private theorem size_spqrChainNextKeyC (e : Expr OO Γ _) :
    (spqrChainNextKeyC (P := P) (C := C) (K := K) (decT := decT) (encT := encT) I e).size =
      e.size + 2 := rfl

private theorem size_listDropExpr {α : Ty Sig} (fuel : ℕ)
    (n : Expr O Γ .nat) (l : Expr O Γ (.list α)) :
    (listDropExpr fuel n l).size ≤ n.size + l.size + 2 * bits fuel + 35 := by
  simp only [listDropExpr, Expr.size, Expr.v0, Expr.v1, Expr.v2, Expr.v3, size_var, hb1]; omega

private theorem size_listGetExpr {α : Ty Sig} (fuel : ℕ)
    (idx : Expr O Γ .nat) (l : Expr O Γ (.list α)) :
    (listGetExpr fuel idx l).size ≤ idx.size + l.size + 2 * bits fuel + 35 := by
  simp only [listGetExpr, Expr.size, Expr.v0, Expr.v1, Expr.v2, Expr.v3, size_var, hb1]; omega

private theorem size_listSetExpr {α : Ty Sig} (fuel : ℕ)
    (idx : Expr O Γ .nat) (val : Expr O Γ α) (l : Expr O Γ (.list α)) :
    (listSetExpr fuel idx val l).size ≤ idx.size + val.size + l.size + 2 * bits fuel + 45 := by
  simp only [listSetExpr, Expr.size, Expr.v0, Expr.v1, Expr.v2, Expr.v3, size_var, hb1]; omega

private theorem size_spqrEpochIdxExpr
    (curEp : Expr OO Γ _) (linksLen : Expr OO Γ _) (epoch : Expr OO Γ _) :
    (spqrEpochIdxExpr (P := P) (C := C) (K := K) (decT := decT) (encT := encT)
      curEp linksLen epoch).size ≤ curEp.size + linksLen.size + epoch.size + 60 := by
  simp only [spqrEpochIdxExpr, Expr.size, Expr.v0, Expr.v1, size_var,
    size_pureOp_loc, E2EPureOp.opSize, hb1]; omega

private theorem size_spqrResolveChainComp (vn? : Expr OO Γ _) (ch? : Expr OO Γ _) :
    (spqrResolveChainComp (P := P) (C := C) (K := K) (decT := decT) (encT := encT)
      I vn? ch?).size ≤ vn?.size + ch?.size + 25 := by
  simp only [spqrResolveChainComp, Comp.size, Expr.size, Expr.v0, size_var, size_spqrChainFromVnC]
  omega

private theorem size_spqrAddEpochOptComp (ch : Expr OO Γ _) (epSec? : Expr OO Γ _) :
    (spqrAddEpochOptComp (P := P) (C := C) (K := K) (decT := decT) (encT := encT)
      I ch epSec?).size ≤ ch.size + epSec?.size + 45 := by
  simp only [spqrAddEpochOptComp, Comp.size, Expr.size, Expr.v0, Expr.v1, size_var,
    size_spqrChainAddEpochC, size_pureOp_loc, E2EPureOp.opSize]
  omega

private theorem size_linksClearSendPrefixExpr (n : Expr OO Γ .nat) (links : Expr OO Γ _) :
    (linksClearSendPrefixExpr (P := P) (C := C) (K := K) (decT := decT) (encT := encT)
      n links).size ≤ n.size + links.size + 95 := by
  simp only [linksClearSendPrefixExpr, clearLinkSendNextExpr, Expr.size,
    Expr.v0, Expr.v1, Expr.v2, Expr.v3, size_var,
    size_pureOp_loc, E2EPureOp.opSize, List.length_nil, hb1, hb4]
  omega

private theorem size_spqrChainSendKeyComp (ch : Expr OO Γ _) (epoch : Expr OO Γ _) :
    (spqrChainSendKeyComp (P := P) (C := C) (K := K) (decT := decT) (encT := encT)
      I ch epoch).size ≤ ch.size + epoch.size + 550 := by
  rw [← Nat.zero_add (Comp.size _)]; unfold spqrChainSendKeyComp
  apply le_size_bind; apply le_size_iteC; apply le_size_caseOptC_of (size_spqrEpochIdxExpr _ _ _)
  apply le_size_bind; apply le_size_caseOptC_of (size_listGetExpr 4 _ _)
  apply le_size_caseOptC; apply le_size_bind_of (by rw [size_spqrChainNextKeyC])
  apply le_size_caseOptC
  simp only [linksClearSendPrefixExpr, clearLinkSendNextExpr, listDropExpr, listSetExpr,
    Comp.size, Expr.size, Expr.v0, Expr.v1, Expr.v2, Expr.v3, Expr.v4, Expr.v6,
    size_var, size_pureOp_loc, E2EPureOp.opSize, List.length_nil, hb0, hb1, hb4]
  omega

private theorem size_spqrRunSendChainComp
    (vn? : Expr OO Γ _) (ch? : Expr OO Γ _) (epSec? : Expr OO Γ _) (msgEpoch : Expr OO Γ _) :
    (spqrRunSendChainComp (P := P) (C := C) (K := K) (decT := decT) (encT := encT)
      I vn? ch? epSec? msgEpoch).size ≤
      vn?.size + ch?.size + epSec?.size + msgEpoch.size + 725 := by
  rw [← Nat.zero_add (Comp.size _)]; unfold spqrRunSendChainComp
  apply le_size_bind; apply le_size_bind_of (size_spqrResolveChainComp _ _)
  apply le_size_caseOptC; apply le_size_bind_of (size_spqrAddEpochOptComp _ _)
  apply le_size_caseOptC; apply le_size_iteC
  refine Nat.le_trans (Nat.add_le_add_left (size_spqrChainSendKeyComp _ _) _) ?_
  simp only [Comp.size, Expr.size, Expr.v0, Expr.v1, Expr.v2, Expr.v3, Expr.v4,
    size_var, size_pureOp_loc, E2EPureOp.opSize]; omega

theorem size_spqrSendComp (e : Expr OO Γ _) :
    (spqrSendComp (P := P) (C := C) (K := K) (decT := decT) (encT := encT) I e).size ≤
      e.size + 925 := by
  rw [← Nat.zero_add (Comp.size _)]; unfold spqrSendComp
  apply le_size_bind; apply le_size_caseOptC; apply le_size_caseOptC
  apply le_size_bind_of (by rw [size_spqrBraidSendC])
  apply le_size_caseOptC; apply le_size_bind_of (size_spqrRunSendChainComp _ _ _ _)
  apply le_size_caseOptC
  simp only [Comp.size, Expr.size, Expr.v0, Expr.v1, Expr.v2, Expr.v3, Expr.v5,
    size_var, size_pureOp_loc, E2EPureOp.opSize, List.length_nil, size_cryptoOp_loc]; omega

private theorem size_spqrListRevExpr {α : Ty Sig} (fuel : ℕ)
    (dflt : Expr O Γ α) (l : Expr O Γ (.list α)) :
    (spqrListRevExpr fuel dflt l).size ≤ 2 * dflt.size + 2 * l.size + 3 * bits fuel + 100 := by
  simp only [spqrListRevExpr, Expr.size, Expr.v0, Expr.v1, Expr.v2, Expr.v3, Expr.v4,
    size_var, hb0, hb1]
  omega

private theorem size_spqrPrevGetExpr
    (entries : Expr OO Γ _) (tail : Expr OO Γ _) (atIdx curCtr maxOoo : Expr OO Γ _) :
    (spqrPrevGetExpr (P := P) (C := C) (K := K) (decT := decT) (encT := encT)
      entries tail atIdx curCtr maxOoo).size ≤
      entries.size + tail.size + atIdx.size + curCtr.size + maxOoo.size + 520 := by
  simp only [spqrPrevGetExpr, spqrPrevGetFuelExpr, listGetExpr, listSetExpr,
    Expr.size, Expr.v0, Expr.v1, Expr.v2, Expr.v3, Expr.v4,
    size_var, size_pureOp_loc, E2EPureOp.opSize, List.length_nil, hb0, hb1, hb2201]
  omega

private theorem size_spqrPrevGcExpr
    (entries : Expr OO Γ _) (curKey maxOoo trimSize : Expr OO Γ _) :
    (spqrPrevGcExpr (P := P) (C := C) (K := K) (decT := decT) (encT := encT)
      entries curKey maxOoo trimSize).size ≤
      entries.size + curKey.size + maxOoo.size + trimSize.size + 520 := by
  simp only [spqrPrevGcExpr, spqrPrevGcFuelExpr, listDropExpr,
    Expr.size, Expr.v0, Expr.v1, Expr.v2, Expr.v3, Expr.v4,
    size_var, size_pureOp_loc, E2EPureOp.opSize, List.length_nil, hb0, hb1, hb4201]
  omega

private theorem size_spqrKeyAdvanceComp
    (ctr0 : Expr OO Γ _) (next0 : Expr OO Γ _) (entries0 : Expr OO Γ _)
    (atIdx maxOoo : Expr OO Γ _) :
    (spqrKeyAdvanceComp (P := P) (C := C) (K := K) (decT := decT) (encT := encT)
      I ctr0 next0 entries0 atIdx maxOoo).size ≤
      ctr0.size + next0.size + entries0.size + atIdx.size + maxOoo.size + 760 := by
  simp only [spqrKeyAdvanceComp, spqrKeyAdvanceFuelComp, spqrKeyAdvanceStep, spqrListRevExpr,
    Comp.size, Expr.size, Expr.v0, Expr.v1, Expr.v2, Expr.v3, Expr.v4, size_var,
    size_spqrChainNextKeyC, size_pureOp_loc, E2EPureOp.opSize, List.length_nil,
    hb0, hb1, hb32, hb2000, hb4201, hb25000]
  omega

private theorem size_spqrDirKeyFwdComp
    (ctr0 : Expr OO Γ _) (next0 : Expr OO Γ _) (entriesInit : Expr OO Γ _)
    (atIdx maxOoo trimSize : Expr OO Γ _) :
    (spqrDirKeyFwdComp (P := P) (C := C) (K := K) (decT := decT) (encT := encT)
      I ctr0 next0 entriesInit atIdx maxOoo trimSize).size ≤
      ctr0.size + next0.size + entriesInit.size + atIdx.size + maxOoo.size + trimSize.size +
        1490 := by
  rw [← Nat.zero_add (Comp.size _)]; unfold spqrDirKeyFwdComp
  apply le_size_bind; apply le_size_bind_of (size_spqrKeyAdvanceComp _ _ _ _ _)
  apply le_size_caseOptC; apply le_size_caseOptC_of (size_spqrPrevGcExpr _ _ _ _)
  apply le_size_bind_of (by rw [size_spqrChainNextKeyC]); apply le_size_caseOptC
  simp only [Comp.size, Expr.size, Expr.v0, Expr.v1, Expr.v2, Expr.v3, size_var,
    size_pureOp_loc, E2EPureOp.opSize, List.length_nil]
  omega

private theorem size_spqrDirKeyComp
    (recvDir : Expr OO Γ _) (atIdx maxJump maxOoo trimSize : Expr OO Γ _) :
    (spqrDirKeyComp (P := P) (C := C) (K := K) (decT := decT) (encT := encT)
      I recvDir atIdx maxJump maxOoo trimSize).size ≤
      recvDir.size + atIdx.size + maxJump.size + maxOoo.size + trimSize.size + 2340 := by
  rw [← Nat.zero_add (Comp.size _)]; unfold spqrDirKeyComp
  apply le_size_bind; apply le_size_iteC_then 610
  · apply le_size_caseOptC_of (size_spqrPrevGetExpr _ _ _ _ _)
    simp only [Comp.size, Expr.size, Expr.v0, Expr.v1, size_var,
      size_pureOp_loc, E2EPureOp.opSize, List.length_nil]; omega
  · apply le_size_iteC; apply le_size_iteC; apply le_size_iteC
    refine Nat.le_trans (Nat.add_le_add_left (size_spqrDirKeyFwdComp _ _ _ _ _ _) _) ?_
    simp only [Comp.size, Expr.size, Expr.v0, Expr.v1, Expr.v2, Expr.v3, size_var,
      size_pureOp_loc, E2EPureOp.opSize, hb0, hb1]; omega

private theorem size_spqrChainRecvKeyComp
    (ch : Expr OO Γ _) (epoch : Expr OO Γ _) (index : Expr OO Γ _) :
    (spqrChainRecvKeyComp (P := P) (C := C) (K := K) (decT := decT) (encT := encT)
      I ch epoch index).size ≤ ch.size + epoch.size + index.size + 2960 := by
  rw [← Nat.zero_add (Comp.size _)]; unfold spqrChainRecvKeyComp
  apply le_size_bind; apply le_size_iteC; apply le_size_caseOptC_of (size_spqrEpochIdxExpr _ _ _)
  apply le_size_caseOptC_of (size_listGetExpr 4 _ _); apply le_size_caseOptC; apply le_size_caseOptC
  apply le_size_bind; apply le_size_bind_of (size_spqrDirKeyComp _ _ _ _ _)
  apply le_size_caseOptC
  simp only [listSetExpr, Comp.size, Expr.size, Expr.v0, Expr.v1, Expr.v2, Expr.v3,
    Expr.v4, Expr.v5, Expr.v6, size_var, size_pureOp_loc, E2EPureOp.opSize,
    hb0, hb1, hb4, hb10, hb11]; omega

private theorem size_spqrRecvGreaterComp (parts : Expr OO Γ _) (msgIdx : Expr OO Γ _) :
    (spqrRecvGreaterComp (P := P) (C := C) (K := K) (decT := decT) (encT := encT)
      I parts msgIdx).size ≤ parts.size + msgIdx.size + 3180 := by
  rw [← Nat.zero_add (Comp.size _)]; unfold spqrRecvGreaterComp
  apply le_size_bind; apply le_size_bind_of (size_spqrResolveChainComp _ _)
  apply le_size_caseOptC; apply le_size_bind_of (size_spqrChainRecvKeyComp _ _ _)
  apply le_size_caseOptC
  simp only [Comp.size, Expr.size, Expr.v0, Expr.v1, Expr.v2, Expr.v3, Expr.v4, size_var,
    size_pureOp_loc, E2EPureOp.opSize, hb0]; omega

private theorem size_spqrRecvPrepStateComp
    (parts : Expr OO Γ _) (msgVer curVer : Expr OO Γ _) (stillNeg : Expr OO Γ _) :
    (spqrRecvPrepStateComp (P := P) (C := C) (K := K) (decT := decT) (encT := encT)
      I parts msgVer curVer stillNeg).size ≤
      parts.size + msgVer.size + curVer.size + stillNeg.size + 230 := by
  simp only [spqrRecvPrepStateComp, spqrResolveChainComp, Comp.size, Expr.size,
    Expr.v0, Expr.v1, Expr.v2, Expr.v3, size_var, size_spqrNegotiateInitC,
    size_spqrChainFromVnC, size_pureOp_loc, E2EPureOp.opSize, hb0, hb1]; omega

private theorem size_spqrRunRecvChainComp
    (vn? : Expr OO Γ _) (ch? : Expr OO Γ _) (epSec? : Expr OO Γ _)
    (msgEpoch : Expr OO Γ _) (msgIdx : Expr OO Γ _) :
    (spqrRunRecvChainComp (P := P) (C := C) (K := K) (decT := decT) (encT := encT)
      I vn? ch? epSec? msgEpoch msgIdx).size ≤
      vn?.size + ch?.size + epSec?.size + msgEpoch.size + msgIdx.size + 3180 := by
  rw [← Nat.zero_add (Comp.size _)]; unfold spqrRunRecvChainComp
  apply le_size_bind; apply le_size_iteC; apply le_size_bind_of (size_spqrResolveChainComp _ _)
  apply le_size_caseOptC; apply le_size_bind_of (size_spqrAddEpochOptComp _ _)
  apply le_size_caseOptC
  refine Nat.le_trans (Nat.add_le_add_left (size_spqrChainRecvKeyComp _ _ _) _) ?_
  simp only [Comp.size, Expr.size, Expr.v0, Expr.v1, Expr.v2, Expr.v3, Expr.v4,
    size_var, size_pureOp_loc, E2EPureOp.opSize]; omega

private theorem size_spqrRecvV1BodyComp
    (stateParts : Expr OO Γ _) (msgEp : Expr OO Γ _) (msgIdx : Expr OO Γ _) (msgRem : Expr OO Γ _) :
    (spqrRecvV1BodyComp (P := P) (C := C) (K := K) (decT := decT) (encT := encT)
      I stateParts msgEp msgIdx msgRem).size ≤
      stateParts.size + msgEp.size + msgIdx.size + msgRem.size + 3400 := by
  rw [← Nat.zero_add (Comp.size _)]; unfold spqrRecvV1BodyComp
  apply le_size_bind; apply le_size_caseOptC
  apply le_size_bind_of (by rw [size_spqrBraidRecvC]); apply le_size_caseOptC
  apply le_size_bind_of (size_spqrRunRecvChainComp _ _ _ _ _); apply le_size_caseOptC
  simp only [Comp.size, Expr.size, Expr.v0, Expr.v1, Expr.v2, Expr.v3, size_var,
    size_pureOp_loc, E2EPureOp.opSize, List.length_nil]
  omega

theorem size_spqrRecvComp (e : Expr OO Γ _) :
    (spqrRecvComp (P := P) (C := C) (K := K) (decT := decT) (encT := encT) I e).size ≤
      e.size + 7000 := by
  rw [← Nat.zero_add (Comp.size _)]; unfold spqrRecvComp
  apply le_size_bind; apply le_size_caseOptC; apply le_size_caseOptC; apply le_size_bind
  apply le_size_iteC; apply le_size_iteC; apply le_size_iteC; apply le_size_iteC_then 3200
  · refine Nat.le_trans (Nat.add_le_add_left (size_spqrRecvGreaterComp _ _) _) ?_
    simp only [Comp.size, Expr.size, Expr.v0, Expr.v1, Expr.v2, size_var]; omega
  · apply le_size_bind_of (size_spqrRecvPrepStateComp _ _ _ _); apply le_size_caseOptC
    refine Nat.le_trans (Nat.add_le_add_left (size_spqrRecvV1BodyComp _ _ _ _) _) ?_
    simp only [Comp.size, Expr.size, Expr.v0, Expr.v1, Expr.v2, Expr.v3, Expr.v4, size_var,
      size_pureOp_loc, E2EPureOp.opSize, List.length_nil, size_cryptoOp_loc, size_isSomeE,
      hb0, hb1]; omega

/-! ## Double Ratchet Hooks, Bookkeeping, Send, Receive, and Oracle Step `.size` Bounds -/

private def optLitSz (opt : Option CryptoVerification.E2E.Bytes) : ℕ :=
  match opt with | none => 1 | some bs => bs.length + 3

private theorem optLitSz_le_of_len (opt : Option CryptoVerification.E2E.Bytes)
    (h : ∀ bs, opt = some bs → bs.length ≤ 128) : optLitSz opt ≤ 131 := by
  cases opt with
  | none => simp [optLitSz]
  | some bs =>
    have hbs := h bs rfl
    simp only [optLitSz]
    omega

private theorem size_optBytes32LitE_eq {Γ' : List (Ty Sig)}
    (opt : Option CryptoVerification.E2E.Bytes) :
    (optBytes32LitE (ℓ := ℓ) (P := P) (C := C) (K := K) (decT := decT) (encT := encT)
      (Γ := Γ') opt).size = optLitSz opt := by
  cases opt <;>
    simp only [optBytes32LitE, optLitSz, size_pureOp_loc, E2EPureOp.opSize, Expr.size]; omega

private theorem size_sendAddrsE (isB : Expr OO Γ .bool) :
    (sendAddrsE (ℓ := ℓ) (P := P) (C := C) (K := K) (decT := decT) (encT := encT) isB).size ≤
      isB.size + 270 := by
  have h1 := optLitSz_le_of_len _
    (serializedPartyAddresses_length_le_128 CryptoVerification.LibsignalTripleRatchetRepr.uuidTryParse .B .A)
  have h2 := optLitSz_le_of_len _
    (serializedPartyAddresses_length_le_128 CryptoVerification.LibsignalTripleRatchetRepr.uuidTryParse .A .B)
  simp only [sendAddrsE, size_optBytes32LitE_eq, Expr.size]; omega

private theorem size_expectedAddrsE (isB : Expr OO Γ .bool) :
    (expectedAddrsE (ℓ := ℓ) (P := P) (C := C) (K := K) (decT := decT) (encT := encT) isB).size ≤
      isB.size + 270 := by
  have h1 := optLitSz_le_of_len _
    (serializedPartyAddresses_length_le_128 CryptoVerification.LibsignalTripleRatchetRepr.uuidTryParse .A .B)
  have h2 := optLitSz_le_of_len _
    (serializedPartyAddresses_length_le_128 CryptoVerification.LibsignalTripleRatchetRepr.uuidTryParse .B .A)
  simp only [expectedAddrsE, size_optBytes32LitE_eq, Expr.size]; omega

private theorem size_sessionVersionEffE (ver : Expr OO Γ U32) :
    (sessionVersionEffE (ℓ := ℓ) (P := P) (C := C) (K := K)
      (decT := decT) (encT := encT) ver).size ≤ ver.size + 25 := by
  simp only [sessionVersionEffE, Expr.size, Expr.v0, size_pureOp_loc, E2EPureOp.opSize, hb0, hb3]
  omega

private theorem size_pushEvict5E {α : Ty Sig} (xs : Expr OO Γ (.list α)) (x : Expr OO Γ α) :
    (pushEvict5E xs x).size ≤ xs.size + x.size + 45 := by
  simp only [pushEvict5E, drop1BE, Expr.size, Expr.v0, Expr.v1, Expr.v2, size_var, hb5]; omega

private theorem size_getDZero5E (cEps : Expr OO Γ (.list .nat)) (idx : Expr OO Γ .nat) :
    (getDZero5E cEps idx).size ≤ cEps.size + idx.size + 45 := by
  simp only [getDZero5E, Expr.size, Expr.v0, Expr.v1, Expr.v2, size_var, hb0, hb1, hb5]; omega

private theorem size_findChainWithIdx5E (rcs : Expr OO Γ (.list drRecvChainT))
    (their : Expr OO Γ PK) :
    (findChainWithIdx5E (ℓ := ℓ) (P := P) (C := C) (K := K)
      (decT := decT) (encT := encT) rcs their).size ≤ rcs.size + their.size + 45 := by
  simp only [findChainWithIdx5E, Expr.size, Expr.v0, Expr.v1, Expr.v2, size_var,
    size_pureOp_loc, E2EPureOp.opSize, hb0, hb1, hb5]; omega

private theorem size_replaceFirstChain5E (rcs : Expr OO Γ (.list drRecvChainT))
    (their : Expr OO Γ PK) (newRc : Expr OO Γ drRecvChainT) :
    (replaceFirstChain5E (ℓ := ℓ) (P := P) (C := C) (K := K)
      (decT := decT) (encT := encT) rcs their newRc).size ≤
      rcs.size + their.size + newRc.size + 55 := by
  simp only [replaceFirstChain5E, Expr.size, Expr.v0, Expr.v1, Expr.v2, size_var,
    size_pureOp_loc, E2EPureOp.opSize, hb5]; omega

private theorem size_takeSkippedFromListE
    (mks : Expr OO Γ (.list (.prod BV256 U32))) (targetCtr : Expr OO Γ U32) :
    (takeSkippedFromListE (ℓ := ℓ) (P := P) (C := C) (K := K)
      (decT := decT) (encT := encT) mks targetCtr).size ≤
      mks.size + targetCtr.size + 90 := by
  simp only [takeSkippedFromListE, Expr.size, Expr.v0, Expr.v1, Expr.v2, size_var,
    size_pureOp_loc, E2EPureOp.opSize, hb2000]; omega

private theorem size_advanceSingleChainC (I : Iface Sig T)
    (ckInit : Expr OO Γ (.prod BV256 U32))
    (mksInit : Expr OO Γ (.list (.prod BV256 U32)))
    (targetCtr : Expr OO Γ U32) :
    (advanceSingleChainC (ℓ := ℓ) (P := P) (C := C) (K := K)
      (decT := decT) (encT := encT) I ckInit mksInit targetCtr).size ≤
      ckInit.size + mksInit.size + targetCtr.size + 130 := by
  simp only [advanceSingleChainC, drop1BE, Comp.size, Expr.size,
    Expr.v0, Expr.v1, Expr.v2, Expr.v3, size_var,
    size_pureOp_loc, E2EPureOp.opSize, size_cryptoOp_loc, hb2000, hb25000]; omega

private theorem size_e2eGsSetWin (s : Expr O Γ (e2eGsTy ℓ)) (w : Expr O Γ .bool) :
    (e2eGsSetWin s w).size ≤ s.size + w.size + 140 := by
  simp only [e2eGsSetWin, e2eGsMk, e2eGsSt, e2eGsB, e2eGsWin, e2eGsEpoch, e2eGsIdx,
    e2eGsTL, e2eGsTrans, e2eGsChall, e2eGsComp, e2eGsMaxAcc, e2eGsLeaks, e2eGsCorrs,
    Expr.size, Expr.v0, size_var]; omega

private theorem size_e2eSafeChE (Δ : ℕ) (s : Expr O Γ (e2eGsTy ℓ)) (p : Expr O Γ .bool) :
    (e2eSafeChE Δ s p).size ≤ s.size + p.size + bits Δ + 60 := by
  unfold e2eSafeChE
  simp only [e2eGsEpoch, e2eGsTL, pGet, otherE, healedByE, leN, maxN, minN, maxOptE,
    CryptoGames.SM.orE, CryptoGames.SM.isSomeE, Expr.size, Expr.v0, Expr.v1, size_var, hb0, hb1]
  omega

private theorem size_e2eSafeInjE (Δ : ℕ) (s : Expr O Γ (e2eGsTy ℓ)) :
    (e2eSafeInjE Δ s).size ≤ s.size + bits Δ + 60 := by
  unfold e2eSafeInjE
  simp only [e2eGsEpoch, e2eGsTL, pGet, otherE, healedByE, leN, maxN, minN, maxOptE,
    CryptoGames.SM.orE, CryptoGames.SM.isSomeE, Expr.size, Expr.v0, Expr.v1, size_var, hb0, hb1]
  omega

private theorem size_e2eLeakE (s : Expr O Γ (e2eGsTy ℓ)) (l : Expr O Γ .nat) :
    (e2eLeakE s l).size ≤ s.size + l.size + 180 := by
  unfold e2eLeakE
  simp only [e2eGsMk, e2eGsSt, e2eGsB, e2eGsWin, e2eGsEpoch, e2eGsIdx,
    e2eGsTL, e2eGsTrans, e2eGsChall, e2eGsComp, e2eGsMaxAcc, e2eGsLeaks, e2eGsCorrs,
    maxOptE, maxN, leN, Expr.size, Expr.v0, Expr.v1, size_var]; omega

private theorem size_e2eEpMgmtE (Δ qep : ℕ) (s : Expr O Γ (e2eGsTy ℓ))
    (p bad : Expr O Γ .bool) :
    (e2eEpMgmtE Δ qep s p bad).size ≤
      s.size + p.size + bad.size + bits Δ + 2 * bits qep + 550 := by
  rw [← Nat.zero_add (Expr.size _)]; unfold e2eEpMgmtE
  apply le_size_letE
  simp only [e2eSafeChE, e2eLeakE, e2eGsMk, e2eGsSt, e2eGsB, e2eGsWin, e2eGsEpoch, e2eGsIdx,
    e2eGsTL, e2eGsTrans, e2eGsChall, e2eGsComp, e2eGsMaxAcc, e2eGsLeaks, e2eGsCorrs,
    pGet, pSet, sendsInE, otherE, healedByE, leN, maxN, minN, maxOptE,
    size_sm_orE, size_sm_isSomeE,
    Expr.size, Expr.v0, Expr.v1, size_var, hb0, hb1, hb2]
  omega

private theorem size_e2eCompContainsE (q : ℕ) (s : Expr O Γ (e2eGsTy ℓ))
    (pos : Expr O Γ _) :
    (e2eCompContainsE q s pos).size ≤ s.size + pos.size + bits q + 60 := by
  unfold e2eCompContainsE
  simp only [e2eGsComp, posEq, posSender, posEpoch, posIdx, boolEq,
    Expr.size, Expr.v0, Expr.v1, size_var]; omega

private theorem size_e2eChallContainsE (q : ℕ) (s : Expr O Γ (e2eGsTy ℓ))
    (pos : Expr O Γ _) :
    (e2eChallContainsE q s pos).size ≤ s.size + pos.size + bits q + 60 := by
  unfold e2eChallContainsE
  simp only [e2eGsChall, posEq, posSender, posEpoch, posIdx, boolEq,
    Expr.size, Expr.v0, Expr.v1, size_var]; omega

private theorem size_e2eRecordE (q Δ : ℕ) (s : Expr O Γ (e2eGsTy ℓ)) (p : Expr O Γ .bool)
    (st' : Expr O Γ GhostStT) (pos : Expr O Γ _) (msg : Expr O Γ PlainT)
    (ct : Expr O Γ _) (isChall : Expr O Γ .bool) :
    (e2eRecordE q Δ s p st' pos msg ct isChall).size ≤
      s.size + p.size + st'.size + pos.size + msg.size + ct.size + isChall.size +
        bits Δ + 2 * bits q + 500 := by
  rw [← Nat.zero_add (Expr.size _)]; unfold e2eRecordE
  apply le_size_letE
  apply le_size_letE_of (by
    simp only [Expr.size]
    exact Nat.add_le_add_right
      (Nat.add_le_add (size_e2eSafeChE Δ _ _) (size_e2eCompContainsE q _ _)) 1)
  simp only [e2eGsMk, e2eRecMk, e2eRecPos, e2eRecMsg, e2eRecCt, e2eRecComp,
    e2eGsSt, e2eGsB, e2eGsWin, e2eGsEpoch, e2eGsIdx,
    e2eGsTL, e2eGsTrans, e2eGsChall, e2eGsComp, e2eGsMaxAcc, e2eGsLeaks, e2eGsCorrs,
    pGet, pSet, posSender, posEpoch, posIdx, posEq, boolEq, size_sm_orE,
    Expr.size, Expr.v0, Expr.v1, Expr.v2, size_var]
  omega

private theorem size_e2eDeleteE (q : ℕ) (s : Expr O Γ (e2eGsTy ℓ)) (pos : Expr O Γ _) :
    (e2eDeleteE q s pos).size ≤ s.size + pos.size + 3 * bits q + 300 := by
  unfold e2eDeleteE
  simp only [e2eGsMk, e2eRecPos, e2eGsSt, e2eGsB, e2eGsWin, e2eGsEpoch, e2eGsIdx,
    e2eGsTL, e2eGsTrans, e2eGsChall, e2eGsComp, e2eGsMaxAcc, e2eGsLeaks, e2eGsCorrs,
    posEq, posSender, posEpoch, posIdx, boolEq, Expr.size, Expr.v0, Expr.v1, Expr.v2, size_var]
  omega

private theorem size_e2eAcceptE (q : ℕ) (s : Expr O Γ (e2eGsTy ℓ)) (p : Expr O Γ .bool)
    (st' : Expr O Γ GhostStT) (pos : Expr O Γ _) :
    (e2eAcceptE q s p st' pos).size ≤
      s.size + p.size + st'.size + 2 * pos.size + 3 * bits q + 800 := by
  have hdel := size_e2eDeleteE (ℓ := ℓ) (O := O) q s pos
  unfold e2eAcceptE
  simp only [e2eGsMk, e2eGsSt, e2eGsB, e2eGsWin, e2eGsEpoch, e2eGsIdx,
    e2eGsTL, e2eGsTrans, e2eGsChall, e2eGsComp, e2eGsMaxAcc, e2eGsLeaks, e2eGsCorrs,
    pGet, pSet, maxAccGet, maxAccSet, maxN, leN, posEpoch, posIdx,
    Expr.size, Expr.v0, Expr.v1, size_var] at hdel ⊢
  omega

private theorem size_e2eTrivialE (q Δ : ℕ) (s : Expr O Γ (e2eGsTy ℓ)) (pos : Expr O Γ _) :
    (e2eTrivialE q Δ s pos).size ≤ s.size + pos.size + bits Δ + 2 * bits q + 220 := by
  rw [← Nat.zero_add (Expr.size _)]; unfold e2eTrivialE
  apply le_size_letE
  simp only [e2eCompContainsE, e2eGsComp, e2eGsTrans, e2eGsTL, e2eRecPos, healedByE,
    posEq, posSender, posEpoch, posIdx, boolEq, leN, size_sm_orE,
    Expr.size, Expr.v0, Expr.v1, size_var, hb1]
  omega

private theorem size_e2eCorrAllowedE (q : ℕ) (s : Expr O Γ (e2eGsTy ℓ)) (p : Expr O Γ .bool) :
    (e2eCorrAllowedE q s p).size ≤ s.size + p.size + 2 * bits q + 140 := by
  unfold e2eCorrAllowedE
  simp only [e2eGsChall, e2eGsTrans, e2eRecPos, e2eRecComp, posSender, otherE, boolEq,
    size_sm_orE, Expr.size, Expr.v0, Expr.v1, size_var]; omega

private theorem size_e2eAfterCorrAllowedE (s : Expr O Γ (e2eGsTy ℓ)) (p : Expr O Γ .bool) :
    (e2eAfterCorrAllowedE s p).size ≤ s.size + p.size + 420 := by
  rw [← Nat.zero_add (Expr.size _)]; unfold e2eAfterCorrAllowedE
  apply le_size_letE
  apply le_size_letE_of (size_e2eLeakE _ _)
  simp only [e2eGsMk, e2eGsSt, e2eGsB, e2eGsWin, e2eGsEpoch, e2eGsIdx,
    e2eGsTL, e2eGsTrans, e2eGsChall, e2eGsComp, e2eGsMaxAcc, e2eGsLeaks, e2eGsCorrs,
    pGet, maxN, leN, Expr.size, Expr.v0, Expr.v1, size_var]
  omega

private theorem size_e2eInWindowE (s : Expr O Γ (e2eGsTy ℓ)) (p : Expr O Γ .bool) :
    (e2eInWindowE s p).size ≤ s.size + p.size + 120 := by
  unfold e2eInWindowE
  simp only [e2eGsEpoch, pGet, otherE, sendsInE, leN, CryptoGames.SM.orE, size_orE,
    Expr.size, Expr.v0, size_var, hb0, hb1, hb2]; omega

private theorem size_e2eSendOKE (s : Expr O Γ (e2eGsTy ℓ)) (p : Expr O Γ .bool) :
    (e2eSendOKE s p).size ≤ s.size + p.size + 60 := by
  simp only [e2eSendOKE, e2eGsEpoch, pGet, otherE, leN, CryptoGames.SM.orE, size_orE,
    Expr.size, Expr.v0, size_var, hb0]; omega

private theorem size_e2eCorrOKE (s : Expr O Γ (e2eGsTy ℓ)) (p : Expr O Γ .bool) :
    (e2eCorrOKE s p).size ≤ s.size + p.size + 100 := by
  simp only [e2eCorrOKE, e2eGsEpoch, pGet, otherE, leN, CryptoGames.SM.orE, size_orE,
    Expr.size, Expr.v0, size_var, hb0, hb10]; omega

private theorem size_e2eInTransitE (q : ℕ) (s : Expr OO Γ (e2eGsTy ℓ))
    (qParty : Expr OO Γ .bool) (c : Expr OO Γ _) :
    (e2eInTransitE (P := P) (C := C) (K := K) (decT := decT) (encT := encT)
      q s qParty c).size ≤ s.size + qParty.size + c.size + bits q + 80 := by
  unfold e2eInTransitE
  simp only [e2eGsTrans, e2eRecPos, e2eRecCt, bytesEqE, posSender, boolEq,
    size_pureOp_loc, E2EPureOp.opSize, Expr.size, Expr.v0, Expr.v1, size_var]; omega

private theorem size_drSendPreE (gE : Expr OO Γ GhostStT) :
    (drSendPreE (ℓ := ℓ) (P := P) (C := C) (K := K) (decT := decT) (encT := encT) gE).size ≤
      gE.size + 75 := by
  simp only [drSendPreE, sessionVersionEffE, gpSc, gpVer, gpRemId, Expr.size,
    Expr.v0, Expr.v1, Expr.v2, size_var, size_pureOp_loc, E2EPureOp.opSize, hb0, hb3, hb256]
  omega

private theorem size_drSendPostE
    (gE : Expr OO Γ GhostStT) (mE : Expr OO Γ PlainT) (partsE : Expr OO Γ ghostPartsT)
    (scE : Expr OO Γ drSenderChainT) (remIdE : Expr OO Γ IdKey) (pqOutE : Expr OO Γ _) :
    (drSendPostE (P := P) (C := C) (K := K) (decT := decT) (encT := encT)
      gE mE partsE scE remIdE pqOutE).size ≤
      gE.size + mE.size + partsE.size + scE.size + remIdE.size + pqOutE.size + 620 := by
  have h1 := optLitSz_le_of_len _
    (serializedPartyAddresses_length_le_128 CryptoVerification.LibsignalTripleRatchetRepr.uuidTryParse .B .A)
  have h2 := optLitSz_le_of_len _
    (serializedPartyAddresses_length_le_128 CryptoVerification.LibsignalTripleRatchetRepr.uuidTryParse .A .B)
  rw [← Nat.zero_add (Expr.size _)]; unfold drSendPostE
  apply le_size_letE; apply le_size_caseOptE; apply le_size_letE
  simp only [sendAddrsE, size_optBytes32LitE_eq, sessionVersionEffE, sendsInE,
    gpIsB, gpVer, gpLocId, gpRemId, gpRk, gpPrevCtr, gpPend, gpEp, gpCEps, gpRcs, gpMk,
    Expr.size, Expr.v0, Expr.v1, Expr.v2, size_var,
    size_pureOp_loc, E2EPureOp.opSize, List.length_nil, size_cryptoOp_loc, hb0, hb1, hb2, hb3]
  omega

private theorem size_drSendC (e : Expr OO Γ (.prod GhostStT (.prod PlainT BV512))) :
    (drSendC (spqrDslHooks ℓ P C K decT encT) I e).size ≤ e.size + 1760 := by
  rw [← Nat.zero_add (Comp.size _)]; unfold drSendC; dsimp only [spqrDslHooks]
  apply le_size_bind; apply le_size_caseOptC_of (size_drSendPreE _)
  apply le_size_bind_of (size_spqrSendComp _); apply le_size_caseOptC
  apply le_size_ret_of (size_drSendPostE _ _ _ _ _ _)
  simp only [gpPqSt, Comp.size, Expr.size, Expr.v0, Expr.v1, Expr.v2, Expr.v3,
    size_var, size_pureOp_loc, E2EPureOp.opSize, List.length_nil]; omega

private theorem size_drRecvPreE (gE : Expr OO Γ GhostStT) (cE : Expr OO Γ (B 32)) :
    (drRecvPreE (ℓ := ℓ) (P := P) (C := C) (K := K) (decT := decT) (encT := encT) gE cE).size ≤
      gE.size + cE.size + 115 := by
  simp only [drRecvPreE, sessionVersionEffE, gpVer, gpRemId, Expr.size,
    Expr.v0, Expr.v1, Expr.v2, Expr.v3, size_var, size_pureOp_loc, E2EPureOp.opSize,
    hb0, hb3, hb256]
  omega

private theorem size_drRecvDhStepE
    (partsE : Expr OO Γ ghostPartsT) (theirE : Expr OO Γ PK) (rcCoinsE : Expr OO Γ BV256) :
    (drRecvDhStepE (ℓ := ℓ) (P := P) (C := C) (K := K)
      (decT := decT) (encT := encT) partsE theirE rcCoinsE).size ≤
      partsE.size + theirE.size + rcCoinsE.size + 380 := by
  simp only [drRecvDhStepE, pushEvict5E, drop1BE, gpIsB, gpRk, gpPrevCtr, gpEp, gpCEps, gpSc, gpRcs,
    Expr.size, Expr.v0, Expr.v1, Expr.v2, Expr.v3, size_var,
    size_pureOp_loc, E2EPureOp.opSize, size_cryptoOp_loc, hb0, hb1, hb2, hb5]
  omega

private theorem size_drRecvChainSetupE
    (partsE : Expr OO Γ ghostPartsT) (theirE : Expr OO Γ PK) (rcCoinsE : Expr OO Γ BV256) :
    (drRecvChainSetupE (ℓ := ℓ) (P := P) (C := C) (K := K)
      (decT := decT) (encT := encT) partsE theirE rcCoinsE).size ≤
      partsE.size + theirE.size + rcCoinsE.size + 660 := by
  rw [← Nat.zero_add (Expr.size _)]; unfold drRecvChainSetupE
  apply le_size_letE; apply le_size_letE_of (size_findChainWithIdx5E _ _)
  apply le_size_caseOptE_none_of (size_drRecvDhStepE _ _ _); apply le_size_caseOptE
  simp only [getDZero5E, gpRk, gpPrevCtr, gpEp, gpCEps, gpSc, gpRcs,
    Expr.size, Expr.v0, Expr.v1, Expr.v2, Expr.v3, size_var, hb0, hb1, hb5]; omega

private theorem size_drRecvTakeSkippedE
    (theirE : Expr OO Γ PK) (msgCtrE : Expr OO Γ U32)
    (rcs1E : Expr OO Γ (.list drRecvChainT)) (activeE : Expr OO Γ _) :
    (drRecvTakeSkippedE (ℓ := ℓ) (P := P) (C := C) (K := K)
      (decT := decT) (encT := encT) theirE msgCtrE rcs1E activeE).size ≤
      theirE.size + msgCtrE.size + rcs1E.size + activeE.size + 180 := by
  rw [← Nat.zero_add (Expr.size _)]; unfold drRecvTakeSkippedE
  apply le_size_letE; apply le_size_letE_of (size_takeSkippedFromListE _ _); apply le_size_caseOptE
  simp only [replaceFirstChain5E, Expr.size, Expr.v0, Expr.v1, Expr.v2,
    size_var, size_pureOp_loc, E2EPureOp.opSize, hb5]; omega

private theorem size_drRecvAfterAdvE
    (theirE : Expr OO Γ PK) (rcs1E : Expr OO Γ (.list drRecvChainT))
    (advE : Expr OO Γ _) :
    (drRecvAfterAdvE (ℓ := ℓ) (P := P) (C := C) (K := K)
      (decT := decT) (encT := encT) theirE rcs1E advE).size ≤
      theirE.size + rcs1E.size + advE.size + 130 := by
  rw [← Nat.zero_add (Expr.size _)]; unfold drRecvAfterAdvE
  apply le_size_letE; apply le_size_caseOptE
  simp only [replaceFirstChain5E, Expr.size, Expr.v0, Expr.v1, Expr.v2,
    size_var, size_pureOp_loc, E2EPureOp.opSize, size_cryptoOp_loc, hb5]; omega

private theorem size_drRecvConsumeC
    (theirE : Expr OO Γ PK) (msgCtrE : Expr OO Γ U32)
    (rcs1E : Expr OO Γ (.list drRecvChainT)) (activeE : Expr OO Γ _) :
    (drRecvConsumeC (ℓ := ℓ) (P := P) (C := C) (K := K)
      (decT := decT) (encT := encT) I theirE msgCtrE rcs1E activeE).size ≤
      theirE.size + msgCtrE.size + rcs1E.size + activeE.size + 620 := by
  rw [← Nat.zero_add (Comp.size _)]; unfold drRecvConsumeC
  apply le_size_bind; apply le_size_iteC_then 210
  · apply le_size_ret_of (size_drRecvTakeSkippedE _ _ _ _)
    simp only [Expr.size, Expr.v0, size_var]; omega
  · apply le_size_iteC; apply le_size_bind_of (size_advanceSingleChainC I _ _ _)
    apply le_size_caseOptC; apply le_size_ret_of (size_drRecvAfterAdvE _ _ _)
    simp only [Comp.size, Expr.size, Expr.v0, Expr.v2, size_var,
      size_pureOp_loc, E2EPureOp.opSize, hb25000]; omega

private theorem size_drRecvFinishE
    (cE : Expr OO Γ _) (partsE : Expr OO Γ ghostPartsT) (remIdE : Expr OO Γ IdKey)
    (msgCtrE : Expr OO Γ U32) (msgCtE : Expr OO Γ _) (midE : Expr OO Γ _)
    (consOutE : Expr OO Γ _) (pqOutE : Expr OO Γ _) :
    (drRecvFinishE (P := P) (C := C) (K := K) (decT := decT) (encT := encT)
      cE partsE remIdE msgCtrE msgCtE midE consOutE pqOutE).size ≤
      cE.size + partsE.size + remIdE.size + msgCtrE.size + msgCtE.size +
        midE.size + consOutE.size + pqOutE.size + 560 := by
  have h1 := optLitSz_le_of_len _
    (serializedPartyAddresses_length_le_128 CryptoVerification.LibsignalTripleRatchetRepr.uuidTryParse .A .B)
  have h2 := optLitSz_le_of_len _
    (serializedPartyAddresses_length_le_128 CryptoVerification.LibsignalTripleRatchetRepr.uuidTryParse .B .A)
  rw [← Nat.zero_add (Expr.size _)]; unfold drRecvFinishE
  apply le_size_letE; apply le_size_letE
  simp only [expectedAddrsE, size_optBytes32LitE_eq, gpIsB, gpVer, gpLocId, gpRemId, gpMk,
    Expr.size, Expr.v0, Expr.v1, Expr.v2, size_var,
    size_pureOp_loc, E2EPureOp.opSize, size_cryptoOp_loc, hb1]
  omega

private theorem size_drReceiveC (e : Expr OO Γ _) :
    (drReceiveC (spqrDslHooks ℓ P C K decT encT) I e).size ≤ e.size + 9200 := by
  rw [← Nat.zero_add (Comp.size _)]; unfold drReceiveC; dsimp only [spqrDslHooks]
  apply le_size_bind; apply le_size_caseOptC_of (size_drRecvPreE _ _)
  apply le_size_caseOptC_of (size_drRecvChainSetupE _ _ _)
  apply le_size_bind_of (size_drRecvConsumeC _ _ _ _); apply le_size_caseOptC
  apply le_size_bind_of (size_spqrRecvComp _); apply le_size_caseOptC
  apply le_size_ret_of (size_drRecvFinishE _ _ _ _ _ _ _ _)
  simp only [gpPqSt, Comp.size, Expr.size, Expr.v0, Expr.v1, Expr.v2, Expr.v3, size_var]; omega

private theorem size_stepA_draw256 :
    ((e2eStepACoinSamplers ℓ P C K decT encT I₀).draw256 (Γ := Γ)).size ≤ 10 := by
  simp only [e2eStepACoinSamplers, DrSessionSim.E2ECoinSamplers.ofSmpEq,
    DrSessionSim.mkE2ECoinSamplers, Comp.size, Expr.size]
  omega

private theorem size_stepA_draw512 :
    ((e2eStepACoinSamplers ℓ P C K decT encT I₀).draw512 (Γ := Γ)).size ≤ 15 := by
  simp only [e2eStepACoinSamplers, DrSessionSim.E2ECoinSamplers.ofSmpEq,
    DrSessionSim.mkE2ECoinSamplers, Comp.size, Expr.size]
  omega

private theorem size_stepA_samIfNec512 (optR : Expr OO Γ (.opt BV512)) :
    (e2eSamIfNec512C (e2eStepACoinSamplers ℓ P C K decT encT I₀) optR).size ≤
      optR.size + 25 := by
  have hd := size_stepA_draw512 (ℓ := ℓ) (P := P) (C := C) (K := K)
    (decT := decT) (encT := encT) (I₀ := I₀) (Γ := Γ)
  simp only [e2eSamIfNec512C, Comp.size, Expr.size, Expr.v0] at hd ⊢
  omega

private theorem size_drTrArmC (q Δ qep : ℕ)
    (gsE : Expr OO Γ (e2eGsTy ℓ)) (trArg : Expr OO Γ _) :
    (drTrArmC (spqrDslHooks ℓ P C K decT encT)
      (e2eStepACoinSamplers ℓ P C K decT encT I₀) q Δ qep gsE trArg).size ≤
      gsE.size + trArg.size + 2 * bits q + 2 * bits Δ + 2 * bits qep + 3220 := by
  rw [← Nat.zero_add (Comp.size _)]; unfold drTrArmC
  apply le_size_bind
  apply le_size_iteC_of (by
    simp only [size_sm_orE, Expr.size]
    exact Nat.add_le_add_right
      (Nat.add_le_add_right (Nat.add_le_add_right (size_e2eSendOKE _ _) 1) _) 2)
  apply le_size_bind_of (size_stepA_samIfNec512 _)
  apply le_size_caseOptC_of (size_e2eEpMgmtE Δ qep _ _ _)
  apply le_size_bind_of (size_drSendC _); dsimp only
  apply le_size_ret_of (by
    simp only [Expr.size]
    exact Nat.add_le_add_right (Nat.add_le_add_left (size_e2eRecordE q Δ _ _ _ _ _ _ _) _) 1)
  simp only [smRWireE, e2eGsWin, e2eGsSt, e2eGsEpoch, e2eGsIdx, pGet,
    Comp.size, Expr.size, Expr.v0, Expr.v1, Expr.v2, Expr.v3, size_var, hb1]; omega

private theorem size_drChArmC (q Δ qep : ℕ)
    (gsE : Expr OO Γ (e2eGsTy ℓ)) (chArg : Expr OO Γ _) :
    (drChArmC (spqrDslHooks ℓ P C K decT encT)
      (e2eStepACoinSamplers ℓ P C K decT encT I₀) q Δ qep gsE chArg).size ≤
      gsE.size + chArg.size + 2 * bits q + 3 * bits Δ + 2 * bits qep + 3370 := by
  rw [← Nat.zero_add (Comp.size _)]; unfold drChArmC
  apply le_size_bind
  apply le_size_iteC_of (by
    simp only [size_sm_orE, Expr.size]
    exact Nat.add_le_add_right
      (Nat.add_le_add_right (Nat.add_le_add_right (size_e2eSendOKE _ _) 1) _) 2)
  apply le_size_bind_of (size_stepA_samIfNec512 _)
  apply le_size_caseOptC_of (size_e2eEpMgmtE Δ qep _ _ _)
  apply le_size_iteC_of (by
    simp only [Expr.size]
    exact Nat.add_le_add_right (size_e2eSafeChE Δ _ _) 1)
  dsimp only; apply le_size_bind_of (size_drSendC _)
  apply le_size_ret_of (by
    simp only [Expr.size]
    exact Nat.add_le_add_right (Nat.add_le_add_left (size_e2eRecordE q Δ _ _ _ _ _ _ _) _) 1)
  simp only [smRWireE, e2eGsWin, e2eGsB, e2eGsSt, e2eGsEpoch, e2eGsIdx, pGet,
    Comp.size, Expr.size, Expr.v0, Expr.v1, Expr.v2, Expr.v3, size_var, hb1]; omega

private theorem size_drDlArmC (q : ℕ)
    (gsE : Expr OO Γ (e2eGsTy ℓ)) (dlArg : Expr OO Γ _) :
    (drDlArmC (spqrDslHooks ℓ P C K decT encT)
      (e2eStepACoinSamplers ℓ P C K decT encT I₀) q gsE dlArg).size ≤
      gsE.size + dlArg.size + 5 * bits q + 10400 := by
  rw [← Nat.zero_add (Comp.size _)]; unfold drDlArmC
  apply le_size_bind; apply le_size_iteC
  apply le_size_caseOptC_of (size_e2eInTransitE q _ _ _)
  apply le_size_bind_of size_stepA_draw256
  apply le_size_bind_of (size_drReceiveC _); apply le_size_caseOptC; dsimp only
  refine Nat.le_trans (Nat.add_le_add_left
    (by
      simp only [Comp.size, Expr.size]
      exact Nat.add_le_add_right (Nat.add_le_add_right
        (Nat.add_le_add_left (size_e2eAcceptE q _ _ _ _) _) 1) 1) _) ?_
  simp only [e2eChallContainsE, e2eGsChall, posEq, posSender, posEpoch, posIdx, boolEq,
    smRRecvE, recvResultAccE, recvResultRejE, e2eGsWin, e2eGsSt, e2eRecPos, pGet, otherE,
    Comp.size, Expr.size, Expr.v0, Expr.v1, Expr.v2, Expr.v3, Expr.v4, size_var]; omega

private theorem size_drIjArmC (q Δ qep : ℕ)
    (gsE : Expr OO Γ (e2eGsTy ℓ)) (ijArg : Expr OO Γ _) :
    (drIjArmC (spqrDslHooks ℓ P C K decT encT)
      (e2eStepACoinSamplers ℓ P C K decT encT I₀) q Δ qep gsE ijArg).size ≤
      gsE.size + ijArg.size + 6 * bits q + 2 * bits Δ + bits qep + 10750 := by
  have hbs := bits_succ_le qep
  rw [← Nat.zero_add (Comp.size _)]; unfold drIjArmC; dsimp only
  apply le_size_bind
  apply le_size_iteC_of (by
    simp only [size_sm_orE, size_sm_isSomeE, ratchetKeyAdmissibleE,
      size_e2eCurveOp, size_pureOp_loc, E2EPureOp.opSize, size_cryptoOp_loc, Expr.size]
    exact Nat.add_le_add_right (Nat.add_le_add_left (Nat.add_le_add_right (Nat.add_le_add
      (Nat.add_le_add_right (size_e2eInTransitE q _ _ _) 3)
      (Nat.add_le_add_right (Nat.add_le_add_right (Nat.add_le_add_right (size_e2eSafeInjE Δ _) 1) _) 2)) 2) _) 2)
  apply le_size_bind_of size_stepA_draw256
  apply le_size_bind_of (size_drReceiveC _); apply le_size_caseOptC; apply le_size_iteC
  apply le_size_iteC_both (size_e2eTrivialE q Δ _ _)
    (by
      simp only [Comp.size, Expr.size]
      exact Nat.add_le_add_right (Nat.add_le_add_right
        (Nat.add_le_add_left (size_e2eAcceptE q _ _ _ _) _) 1) 1)
    (by
      simp only [Comp.size, Expr.size]
      exact Nat.add_le_add_right (Nat.add_le_add_right
        (Nat.add_le_add_left (size_e2eGsSetWin _ _) _) 1) 1)
  simp only [smRRecvE, recvResultRejE, recvResultAccE, e2eGsWin, e2eGsSt, pGet, otherE,
    Comp.size, Expr.size, Expr.v0, Expr.v1, Expr.v2, Expr.v3, size_var]; omega

private theorem size_drCrArmC (q : ℕ)
    (gsE : Expr OO Γ (e2eGsTy ℓ)) (crArg : Expr OO Γ .bool) :
    (drCrArmC (ℓ := ℓ) (P := P) (C := C) (K := K) (decT := decT) (encT := encT)
      (I := stepAIface ℓ I₀) q gsE crArg).size ≤
      gsE.size + crArg.size + 2 * bits q + 860 := by
  rw [← Nat.zero_add (Comp.size _)]; unfold drCrArmC; dsimp only
  apply le_size_bind
  apply le_size_iteC_of (by
    simp only [size_sm_orE, Expr.size]
    exact Nat.add_le_add_right (Nat.add_le_add_left (Nat.add_le_add_right (Nat.add_le_add
      (Nat.add_le_add_right (size_e2eCorrAllowedE q _ _) 1)
      (Nat.add_le_add_right (Nat.add_le_add (size_e2eInWindowE _ _)
        (Nat.add_le_add_right (size_e2eCorrOKE _ _) 1)) 2)) 2) _) 2)
  apply le_size_ret_of (by
    simp only [Expr.size]
    exact Nat.add_le_add_right (Nat.add_le_add_left (size_e2eAfterCorrAllowedE _ _) _) 1)
  simp only [smRCorrE, e2eGsWin, e2eGsSt, pGet, Comp.size, Expr.size, Expr.v0, size_var]; omega

theorem size_drOracleStepC_concrete (q qep : ℕ)
    (gsE : Expr OO Γ (e2eGsTy ℓ)) (qryE : Expr OO Γ smQT) :
    ((drSessionSimIface (spqrDslHooks ℓ P C K decT encT)).oracleStepC
      I₀ q qep gsE qryE).size ≤
      gsE.size + qryE.size + 17 * bits q + 5 * bits qep + 28850 := by
  rw [← Nat.zero_add (Comp.size _)]; dsimp only [drSessionSimIface]; unfold drOracleStepC
  apply le_size_bind
  apply le_size_caseSumC_of (size_drTrArmC q 3 qep _ _)
  apply le_size_caseSumC_of (size_drChArmC q 3 qep _ _)
  apply le_size_caseSumC_of (size_drDlArmC q _ _)
  apply le_size_caseSumC_of (size_drIjArmC q 3 qep _ _)
  refine Nat.le_trans (Nat.add_le_add_left (size_drCrArmC q _ _) _) ?_
  simp only [Comp.size, Expr.size, Expr.v0, Expr.v1, Expr.v2, Expr.v3, Expr.v4, size_var, hb3]
  omega

/-! ## Local Session-Step Auxiliary and Driver `.size` Bounds -/

private theorem size_emptySmRespE : (emptySmRespE (O := O) (Γ := Γ)).size = 5 := rfl

private theorem size_defaultE2eGsE :
    (defaultE2eGsE (ℓ := ℓ) (P := P) (C := C) (K := K)
      (decT := decT) (encT := encT) (Γ := Γ)).size ≤ 260 := by
  simp only [defaultE2eGsE, size_pureOp_loc, E2EPureOp.opSize, List.length_nil, Expr.size, hb0]
  omega

private theorem size_auxListGetOptE {t : Ty Sig} (k : ℕ)
    (lE : Expr O Γ (.list t)) (iE : Expr O Γ .nat) :
    (listGetOptE k lE iE).size ≤ lE.size + iE.size + bits k + 50 := by
  simp only [listGetOptE, Expr.size, Expr.v0, Expr.v1, Expr.v2, Expr.v3, size_var, hb0, hb1]; omega

private theorem size_auxListSetE {t : Ty Sig} (k : ℕ)
    (lE : Expr O Γ (.list t)) (iE : Expr O Γ .nat) (valE : Expr O Γ t) :
    (listSetE k lE iE valE).size ≤ lE.size + iE.size + valE.size + bits k + 55 := by
  simp only [listSetE, Expr.size, Expr.v0, Expr.v1, Expr.v2, Expr.v3, size_var, hb0, hb1]; omega

private theorem size_initPrinOptE (sidE : Expr OO Γ _) :
    (initPrinOptE (S := S) (P := P) (C := C) (K := K) (decT := decT) (encT := encT) sidE).size ≤
      sidE.size + 15 := by
  simp only [initPrinOptE, size_eCaseSum, size_v, Expr.size]; omega

private theorem size_initRegIdE (sidE : Expr OO Γ _) :
    (initRegIdE (S := S) (P := P) (C := C) (K := K) (decT := decT) (encT := encT) sidE).size ≤
      sidE.size + 40 := by
  simp only [initRegIdE, initPrinOptE, size_eLet, size_eCaseSum, size_eCaseOpt, size_v,
    size_pureOp_loc, E2EPureOp.opSize, Expr.size, hb0]; omega

private theorem size_hdrEqE (h1 h2 : Expr OO Γ _) :
    (hdrEqE (P := P) (C := C) (K := K) (decT := decT) (encT := encT) h1 h2).size ≤
      h1.size + h2.size + 140 := by
  unfold hdrEqE
  simp only [optEqByE, isNoneE, hdrIkA, hdrEkA, hdrSpkId, hdrOpkId, hdrPqId, hdrKemCt,
    size_eLet, size_eCaseOpt, size_v, size_pureOp_loc, E2EPureOp.opSize, Expr.size]; omega

private theorem size_isBobRecvSmQueryE (qE : Expr OO Γ smQT) :
    (isBobRecvSmQueryE (P := P) (C := C) (K := K) (decT := decT) (encT := encT) qE).size ≤
      qE.size + 30 := by
  simp only [isBobRecvSmQueryE, size_eCaseSum, size_v, Expr.size]; omega

private theorem size_isBobAcceptSmRespE (qE : Expr OO Γ smQT) (respE : Expr OO Γ (smRT GhostStT)) :
    (isBobAcceptSmRespE (P := P) (C := C) (K := K) (decT := decT) (encT := encT) qE respE).size ≤
      qE.size + respE.size + 50 := by
  simp only [isBobAcceptSmRespE, isBobRecvSmQueryE, size_eLet, size_eCaseSum, size_eCaseOpt,
    size_v, Expr.size]; omega

private theorem size_setInstMetaAcceptE (imE : Expr OO Γ _) (ikACorrE : Expr OO Γ .bool) :
    (setInstMetaAcceptE (S := S) (P := P) (C := C) (K := K)
      (decT := decT) (encT := encT) imE ikACorrE).size ≤ imE.size + ikACorrE.size + 15 := by
  simp only [setInstMetaAcceptE, Expr.size]; omega

private theorem size_filterLocalSmQueryE
    (bobAccE : Expr OO Γ .bool) (sidE : Expr OO Γ _) (hdrE : Expr OO Γ _) (qE : Expr OO Γ smQT) :
    (filterLocalSmQueryE (S := S) (P := P) (C := C) (K := K)
      (decT := decT) (encT := encT) bobAccE sidE hdrE qE).size ≤
      bobAccE.size + sidE.size + hdrE.size + qE.size + 460 := by
  unfold filterLocalSmQueryE
  simp only [initRegIdE, initPrinOptE, hdrEqE, optEqByE, isNoneE,
    hdrIkA, hdrEkA, hdrSpkId, hdrOpkId, hdrPqId, hdrKemCt,
    size_eLet, size_eCaseSum, size_eCaseOpt, size_v, size_pureOp_loc, E2EPureOp.opSize,
    Expr.size, hb0]; omega

private theorem size_corrTblOfListE (nCorr : ℕ) (corrPrinsE : Expr OO Γ _) :
    (corrTblOfListE (S := S) (P := P) (C := C) (K := K)
      (decT := decT) (encT := encT) nCorr corrPrinsE).size ≤ corrPrinsE.size + bits nCorr + 20 := by
  simp only [corrTblOfListE, Expr.size, Expr.v0, Expr.v1, size_var,
    size_pureOp_loc, E2EPureOp.opSize]; omega

private theorem size_instIkACorrTblE (nPrins : ℕ)
    (sidE : Expr OO Γ _) (ikAPkE : Expr OO Γ _) (corrTblE : Expr OO Γ (.tbl .bool))
    (prinsE : Expr OO Γ _) :
    (instIkACorrTblE (S := S) (P := P) (C := C) (K := K)
      (decT := decT) (encT := encT) nPrins sidE ikAPkE corrTblE prinsE).size ≤
      sidE.size + ikAPkE.size + corrTblE.size + prinsE.size + bits nPrins + 70 := by
  unfold instIkACorrTblE
  simp only [initPrinOptE, size_eLet, size_eCaseOpt, size_eCaseSum, size_eAny, size_v,
    size_pureOp_loc, E2EPureOp.opSize, size_orE, Expr.size]; omega

private theorem size_instIkACorrListE (nCorr nPrins : ℕ)
    (sidE : Expr OO Γ _) (ikAPkE : Expr OO Γ _) (corrPrinsE : Expr OO Γ _)
    (prinsE : Expr OO Γ _) :
    (instIkACorrListE (S := S) (P := P) (C := C) (K := K)
      (decT := decT) (encT := encT) nCorr nPrins sidE ikAPkE corrPrinsE prinsE).size ≤
      sidE.size + ikAPkE.size + corrPrinsE.size + prinsE.size + bits nCorr + bits nPrins + 95 := by
  have hct := size_corrTblOfListE (S := S) (P := P) (C := C) (K := K)
    (decT := decT) (encT := encT) nCorr corrPrinsE
  have hit := size_instIkACorrTblE (S := S) (P := P) (C := C) (K := K)
    (decT := decT) (encT := encT) nPrins sidE ikAPkE (corrTblOfListE nCorr corrPrinsE) prinsE
  unfold instIkACorrListE; omega

private theorem size_drvInstCleanDrvStateE (qStart nCorr : ℕ)
    (revE : Expr OO Γ _) (instsE : Expr OO Γ _) (instMetaE : Expr OO Γ _) (ixE : Expr OO Γ .nat) :
    (drvInstCleanDrvStateE (S := S) (P := P) (C := C) (K := K)
      (decT := decT) (encT := encT) qStart nCorr revE instsE instMetaE ixE).size ≤
      revE.size + instsE.size + instMetaE.size + ixE.size + 2 * bits qStart + bits nCorr + 200 := by
  unfold drvInstCleanDrvStateE respNotRevealedE
  simp only [listGetOptE, initPrinOptE, size_isSomeE, size_eLet, size_eCaseOpt, size_eCaseSum,
    size_eAny, size_v, size_pureOp_loc, E2EPureOp.opSize,
    Expr.size, Expr.v0, Expr.v1, Expr.v2, Expr.v3, size_var, hb0, hb1]; omega

private theorem size_modelInstToHmE (dE : Expr OO Γ _) (imE : Expr OO Γ _) :
    (modelInstToHmE (S := S) (P := P) (C := C) (K := K) (decT := decT) (encT := encT) dE imE).size ≤
      dE.size + imE.size + 25 := by
  simp only [modelInstToHmE, Expr.size, Expr.v0, size_var]; omega

private theorem size_modelInstToSlotE (dE : Expr OO Γ _) :
    (modelInstToSlotE (S := S) (P := P) (C := C) (K := K) (decT := decT) (encT := encT) dE).size ≤
      dE.size + 290 := by
  simp only [modelInstToSlotE, defaultE2eGsE, size_pureOp_loc, E2EPureOp.opSize, List.length_nil,
    Expr.size, Expr.v0, size_var, hb0]
  omega

private theorem size_slotHmToModelInstE (hmE : Expr OO Γ _) (slE : Expr OO Γ _) :
    (slotHmToModelInstE (S := S) (P := P) (C := C) (K := K)
      (decT := decT) (encT := encT) hmE slE).size ≤ hmE.size + slE.size + 45 := by
  simp only [slotHmToModelInstE, Expr.size, Expr.v0, size_var]; omega

private theorem size_stepInstSlotC_concrete (qBound qep : ℕ)
    (slotE : Expr OO Γ (instSlotTy ℓ)) (qE : Expr OO Γ smQT) :
    (stepInstSlotC (drSessionSimIface (spqrDslHooks ℓ P C K decT encT))
      I₀ qBound qep slotE qE).size ≤
      slotE.size + qE.size + 17 * bits qBound + 5 * bits qep + 28950 := by
  rw [← Nat.zero_add (Comp.size _)]; unfold stepInstSlotC
  apply le_size_letV; apply le_size_letV; apply le_size_letV; apply le_size_iteC
  apply le_size_bindV_of (size_drOracleStepC_concrete qBound qep _ _)
  simp only [size_v, size_emptySmRespE, Comp.size, Expr.size]; omega

private theorem size_stepSingleInstC_concrete (qBound qep : ℕ)
    (hmE : Expr OO Γ (e2eInstHdrMetaTy S ℓ)) (slotE : Expr OO Γ (instSlotTy ℓ))
    (ikACorrE : Expr OO Γ .bool) (qE : Expr OO Γ smQT) :
    (stepSingleInstC (drSessionSimIface (spqrDslHooks ℓ P C K decT encT))
      I₀ qBound qep hmE slotE ikACorrE qE).size ≤
      hmE.size + slotE.size + ikACorrE.size + qE.size + 17 * bits qBound + 5 * bits qep + 29860 := by
  rw [← Nat.zero_add (Comp.size _)]; unfold stepSingleInstC
  apply le_size_letV; apply le_size_letV; apply le_size_letV; apply le_size_letV
  apply le_size_letV; apply le_size_letV; apply le_size_letV; apply le_size_letV
  apply le_size_letV; apply le_size_letV_of (size_isBobRecvSmQueryE _)
  apply le_size_iteC_then 45
  · apply le_size_letV_of (size_setInstMetaAcceptE _ _)
    simp only [size_v, size_emptySmRespE, Comp.size, Expr.size]; omega
  · apply le_size_iteC
    apply le_size_caseOptV_of (size_filterLocalSmQueryE _ _ _ _)
    apply le_size_bindV_of (size_stepInstSlotC_concrete qBound qep _ _)
    apply le_size_letV_of (size_isBobAcceptSmRespE _ _)
    apply le_size_letV_of (size_setInstMetaAcceptE _ _); apply le_size_letV
    simp only [size_v, size_emptySmRespE, Comp.size, Expr.size]; omega

/-- Closed-form syntax-size bound for `stepLocalSmC` over `drSessionSimIface (spqrDslHooks ...)`. -/
theorem size_stepLocalSmC (qStart nCorr nPrins qBound qep : ℕ)
    (σE : Expr OO Γ (e2eDrvStateTy S ℓ)) (idxE : Expr OO Γ .nat) (qE : Expr OO Γ smQT) :
    (stepLocalSmC (drSessionSimIface (spqrDslHooks ℓ P C K decT encT))
      I₀ qStart nCorr nPrins qBound qep σE idxE qE).size ≤
      σE.size + idxE.size + qE.size + stepLocalSmSize qStart nCorr nPrins qBound qep := by
  rw [← Nat.zero_add (Comp.size _)]; unfold stepLocalSmC stepLocalSmSize
  apply le_size_letV; apply le_size_letV; apply le_size_letV; apply le_size_letV
  apply le_size_letV; apply le_size_letV; apply le_size_letV; apply le_size_letV
  apply le_size_letV; apply le_size_letV
  apply le_size_letV_of (size_drvInstCleanDrvStateE qStart nCorr _ _ _ _)
  apply le_size_iteC
  apply le_size_caseOptV_of (size_auxListGetOptE qStart _ _)
  apply le_size_caseOptV_of (size_auxListGetOptE qStart _ _)
  apply le_size_letV_of (size_modelInstToHmE _ _)
  apply le_size_letV_of (size_modelInstToSlotE _)
  apply le_size_letV_of (size_instIkACorrListE nCorr nPrins _ _ _ _)
  apply le_size_bindV_of (size_stepSingleInstC_concrete qBound qep _ _ _ _)
  apply le_size_letV_of (size_slotHmToModelInstE _ _); apply le_size_letV
  apply le_size_letV_of (size_auxListSetE qStart _ _ _)
  apply le_size_letV_of (size_auxListSetE qStart _ _ _)
  simp only [size_v, size_emptySmRespE, Comp.size, Expr.size]; omega

end SizeLemmas

end Computational.Proofs.E2E.Dsl.M3SessionSize
