/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Computational.Proofs.E2E.Dsl.DrSessionSim -- proof-setup: allow-public-import
public import Computational.Proofs.E2E.Dsl.DrSessionSimBookkeeping -- proof-setup: allow-public-import
public import Computational.Proofs.E2E.Dsl.DrSessionSimSend -- proof-setup: allow-public-import
public import Computational.Proofs.E2E.Dsl.HaltedDrSessionLifter -- proof-setup: allow-public-import
public import Computational.Proofs.E2E.Dsl.LocalSessionStep -- proof-setup: allow-public-import
public import Computational.Proofs.E2E.Dsl.SmReachInv -- proof-setup: allow-public-import
public import Computational.Proofs.E2E.Dsl.SpqrSim -- proof-setup: allow-public-import
public import Computational.Proofs.Game.PromotedCostedReds.AtomicSessionBridge -- proof-setup: allow-public-import
import Computational.Proofs.E2E.Dsl.DrSessionSimHooks
import Computational.Proofs.E2E.Dsl.SmReachInvParty
import Computational.Proofs.E2E.Dsl.SpqrSimChain
import Computational.Proofs.E2E.Dsl.SpqrSimSend
import Computational.Proofs.E2E.Dsl.TablesHonest

/-!
# Pre-Tracker `e2eOps` Send and Challenge Stages

Bounds the AST size of `drSendC` in oracle context and packages the single-argument pre-tracker
`e2eOps` stages `drTrSendStageC` and `drChSendStageC` with query, cost, size, evaluation, and
`SmReachBounded` preservation lemmas.
-/

public section

set_option autoImplicit false

namespace Computational.Proofs.E2E.Dsl.HaltedDrSessionSimStepsAux

open OracleSpec OracleComp
open _root_.ReductionDsl (Sig Ty Var Env Ops Iface Expr Comp bits)
open CryptoGames (Party SMSchemeR)
open CryptoGames.CBC (Plain)
open CryptoGames.SM (ConfigR GameState samIfNec transmitR transmitImpl challR challImpl
  oracleImplR partyEnc posTy posEnc posSender posEpoch posIdx posEq boolEq
  leN maxN sendsInE pGet pSet pGet_eval healedByE maxOptE)
open CryptoGames.LibsignalSession (Crypto PublicKey IdentityKey GhostState)
open CryptoVerification.LibsignalSpqrV1 (MlKem spqrV1SessionUniformCoins)
open CryptoVerification.E2E (Bytes SampledSessionKey
  paramsIdsWithSpqr sessionSchemeFixedSpk configRefuseEarlyBobCorr)
open CryptoVerification.E2E.Costed (e2eSig e2eOps)
open Computational.Proofs.E2E.Dsl.PqxdhSimTypes (stepAIface)
open Computational.Proofs.E2E.Dsl.HaltedDrSessionLifter (emptyTargetE2EIface)
open Computational.Proofs.E2E.Dsl.SmReachInvParty (PartyReachInv)
open Computational.Proofs.E2E.Dsl.SmReachInv (dedupComp SmReachBounded smReachBounded_oracleImplR)
open Computational.Proofs.E2E.Dsl.SpqrSim (spqrDslHooks)
open Computational.Proofs.E2E.Dsl.DrSessionSimBookkeeping
  (e2eGsTy e2eGsEnc e2eGsMk e2eGsSt e2eGsB e2eGsWin e2eGsEpoch e2eGsIdx e2eGsTL e2eGsTrans
   e2eGsChall e2eGsComp e2eGsMaxAcc e2eGsLeaks e2eGsCorrs e2eRecMk e2eRecPos e2eRecMsg
   e2eRecCt e2eRecComp e2eSendOKE eval_e2eSendOKE cost_e2eSendOKE_le
   e2eLeakE e2eEpMgmtE eval_e2eEpMgmtE cost_e2eEpMgmtE_le e2eSafeChE eval_e2eSafeChE
   cost_e2eSafeChE_le e2eCompContainsE e2eRecordE eval_e2eRecordE cost_e2eRecordE_le)
open Computational.Proofs.E2E.Dsl.DrSessionSimSend (drSendC drSendC_queries drSendC_cost drSendC_eval)
open Computational.Proofs.E2E.Dsl.DrSessionSim
  (e2eStepACoinSamplers e2eSamIfNec512C e2eSamIfNec512C_queries_zero e2eSamIfNec512C_cost
   e2eSamIfNec512C_eval)
open Computational.Proofs.Game.PromotedCostedReds.AtomicSessionBridge
  (renExpr renComp renComp_queries renComp_cost renComp_eval pullEnv
   wk1Comp wk1Comp_queries wk1Comp_cost wk1Comp_eval)

theorem liftP_pure {S₀ : Sig} {ι : Type} {T : OracleSpec ι} (I : Iface S₀ T)
    {α : Type} (a : α) : I.liftP (pure a) = pure a := by
  simp [Iface.liftP]

theorem liftP_bind {S₀ : Sig} {ι : Type} {T : OracleSpec ι} (I : Iface S₀ T)
    {α β : Type} (p : ProbComp α) (k : α → ProbComp β) :
    I.liftP (p >>= k) = (I.liftP p >>= fun a => I.liftP (k a)) := by
  simp [Iface.liftP]

theorem liftP_map {S₀ : Sig} {ι : Type} {T : OracleSpec ι} (I : Iface S₀ T)
    {α β : Type} (f : α → β) (p : ProbComp α) :
    I.liftP (f <$> p) = f <$> I.liftP p := by
  rw [map_eq_bind_pure_comp, map_eq_bind_pure_comp, liftP_bind]
  exact bind_congr fun a => liftP_pure I (f a)

private theorem epMgmt_preserve_fields {ℓ Δ qep : ℕ}
    {st s1 : GameState (GhostState Bytes) (Plain ℓ) Bytes} {party : Party} {bad : Bool}
    (hep : st.epMgmt Δ qep party bad = some s1) :
    s1.st = st.st ∧ s1.trans = st.trans ∧ s1.comp = st.comp := by
  unfold GameState.epMgmt at hep
  split_ifs at hep <;> simp only [Option.some.injEq] at hep <;> subst hep <;> exact ⟨rfl, rfl, rfl⟩

@[simp] private theorem renExpr_size_loc {S₀ : Sig} {O : Ops S₀} {Γ : List (Ty S₀)} {t : Ty S₀}
    (e : Expr O Γ t) :
    ∀ {Δ : List (Ty S₀)} (f : ∀ {τ}, Var Γ τ → Var Δ τ),
      (renExpr f e).size = e.size := by
  induction e <;> intro Δ f <;> simp only [renExpr, Expr.size, *]

@[simp] private theorem renComp_size_loc {S₀ : Sig} {O : Ops S₀} {ι : Type} {T : OracleSpec ι}
    {I₀ : Iface S₀ T} {Γ : List (Ty S₀)} {t : Ty S₀} (c : Comp O I₀ Γ t) :
    ∀ {Δ : List (Ty S₀)} (f : ∀ {τ}, Var Γ τ → Var Δ τ),
      (renComp f c).size = c.size := by
  induction c <;> intro Δ f <;> simp only [renComp, Comp.size, renExpr_size_loc, *]

@[simp] private theorem wk1Comp_size_loc {S₀ : Sig} {O : Ops S₀} {ι : Type} {T : OracleSpec ι}
    {I₀ : Iface S₀ T} {a b : Ty S₀} {Γ : List (Ty S₀)} (c : Comp O I₀ [a] b) :
    (wk1Comp (Γ := Γ) c).size = c.size :=
  renComp_size_loc c _

/-! ## Pre-tracker `e2eOps` send stages -/

abbrev e2eTTop (ℓ : ℕ) : Ty (e2eSig ℓ) :=
  .prod (e2eGsTy ℓ) CryptoVerification.E2E.Costed.smQT

abbrev e2eTrArgT (ℓ : ℕ) : Ty (e2eSig ℓ) :=
  .prod .bool (.prod CryptoVerification.E2E.Costed.PlainT (.opt CryptoVerification.E2E.Costed.BV512))

abbrev e2eChArgT (ℓ : ℕ) : Ty (e2eSig ℓ) :=
  .prod .bool (.prod CryptoVerification.E2E.Costed.PlainT
    (.prod CryptoVerification.E2E.Costed.PlainT (.opt CryptoVerification.E2E.Costed.BV512)))

abbrev e2eTrInTy (ℓ : ℕ) : Ty (e2eSig ℓ) :=
  .prod (e2eGsTy ℓ) (e2eTrArgT ℓ)

abbrev e2eChInTy (ℓ : ℕ) : Ty (e2eSig ℓ) :=
  .prod (e2eGsTy ℓ) (e2eChArgT ℓ)

abbrev e2eCoinsBadT (ℓ : ℕ) : Ty (e2eSig ℓ) :=
  .prod CryptoVerification.E2E.Costed.BV512 .bool

abbrev e2eSendCallInTy (ℓ : ℕ) : Ty (e2eSig ℓ) :=
  .prod (e2eGsTy ℓ)
    (.prod .bool (.prod CryptoVerification.E2E.Costed.PlainT CryptoVerification.E2E.Costed.BV512))

abbrev e2eSendStageOutTy (ℓ : ℕ) : Ty (e2eSig ℓ) :=
  .opt (.prod CryptoVerification.E2E.Costed.BV512
    (.prod (CryptoVerification.E2E.Costed.B 32) (e2eGsTy ℓ)))

abbrev e2eOracleSendCtx (ℓ : ℕ) : List (Ty (e2eSig ℓ)) :=
  [e2eGsTy ℓ, e2eCoinsBadT ℓ, e2eTrInTy ℓ, e2eTrArgT ℓ, e2eTTop ℓ, e2eTTop ℓ]

@[expose] def drSendInOracleCtx {ℓ : ℕ} {Pt : Type} (P : SignalPqxdh.Primitives)
    (C : Crypto) (K : MlKem) (decT : PublicKey → Option Pt) (encT : Pt → PublicKey) :
    Comp (e2eOps ℓ P C K decT encT) (stepAIface ℓ (emptyTargetE2EIface ℓ))
      (e2eOracleSendCtx ℓ)
      (.prod CryptoVerification.E2E.Costed.GhostStT (CryptoVerification.E2E.Costed.B 32)) :=
  drSendC (spqrDslHooks ℓ P C K decT encT) (stepAIface ℓ (emptyTargetE2EIface ℓ))
    (.pair (pGet (e2eGsSt .v0) (.fst (.snd .v2)))
      (.pair (.fst (.snd (.snd .v2))) (.fst .v1)))

section DirectSendSize

open CryptoVerification.E2E.Costed (E2EPureOp E2ECryptoOp drSenderChainT ghostPartsT IdKey)
open Computational.Proofs.E2E.Dsl.TablesHonest (e2ePureOp e2eCryptoOp)
open Computational.Proofs.E2E.Dsl.SpqrSimChain
  (spqrBraidSendC spqrChainFromVnC spqrChainAddEpochC spqrChainNextKeyC
   listDropExpr listGetExpr listSetExpr spqrEpochIdxExpr
   spqrResolveChainComp spqrAddEpochOptComp clearLinkSendNextExpr linksClearSendPrefixExpr
   spqrChainSendKeyComp)
open Computational.Proofs.E2E.Dsl.SpqrSimSend (spqrRunSendChainComp spqrSendComp)
open Computational.Proofs.E2E.Dsl.DrSessionSimHooks
  (gpIsB gpVer gpLocId gpRemId gpRk gpPrevCtr gpPend gpEp gpCEps gpSc gpRcs gpPqSt gpMk
   optBytes32LitE sendAddrsE sessionVersionEffE)
open Computational.Proofs.E2E.Dsl.DrSessionSimSend (drSendPreE drSendPostE)
open Computational.Proofs.E2E.Dsl.SmReachInvParty (serializedPartyAddresses_length_le_128)

private theorem hb0_s : bits 0 = 1 := rfl
private theorem hb1_s : bits 1 = 1 := rfl
private theorem hb2_s : bits 2 = 2 := rfl
private theorem hb3_s : bits 3 = 2 := rfl
private theorem hb4_s : bits 4 = 3 := rfl
private theorem hb256_s : bits 256 = 9 := rfl

private theorem size_var_s {ℓ : ℕ} {O : Ops (e2eSig ℓ)} {Γ : List (Ty (e2eSig ℓ))}
    {τ : Ty (e2eSig ℓ)} (x : Var Γ τ) : (Expr.var (O := O) x).size = 1 := rfl

private theorem size_pureOp_s {ℓ : ℕ} {Pt : Type} {P : SignalPqxdh.Primitives}
    {C : Crypto} {K : MlKem} {decT : PublicKey → Option Pt} {encT : Pt → PublicKey}
    {Γ : List (Ty (e2eSig ℓ))} (o : E2EPureOp)
    (e : Expr (e2eOps ℓ P C K decT encT) Γ (o.dom ℓ)) :
    (e2ePureOp (P := P) (C := C) (K := K) (decT := decT) (encT := encT) o e).size =
      e.size + o.opSize + 1 := rfl

private theorem size_cryptoOp_s {ℓ : ℕ} {Pt : Type} {P : SignalPqxdh.Primitives}
    {C : Crypto} {K : MlKem} {decT : PublicKey → Option Pt} {encT : Pt → PublicKey}
    {Γ : List (Ty (e2eSig ℓ))} (o : E2ECryptoOp)
    (e : Expr (e2eOps ℓ P C K decT encT) Γ (o.dom ℓ)) :
    (e2eCryptoOp (P := P) (C := C) (K := K) (decT := decT) (encT := encT) o e).size =
      e.size + 1 := rfl

private theorem le_sz_letE {S₀ : Sig} {O : Ops S₀} {Γ : List (Ty S₀)} {a b : Ty S₀} {A B : ℕ}
    {e : Expr O Γ a} {k : Expr O (a :: Γ) b}
    (h : A + e.size + 1 + k.size ≤ B) : A + (Expr.letE e k).size ≤ B := by
  simp only [Expr.size]; omega

private theorem le_sz_caseOptE {S₀ : Sig} {O : Ops S₀} {Γ : List (Ty S₀)} {a b : Ty S₀} {A B : ℕ}
    {e : Expr O Γ (.opt a)} {n : Expr O Γ b} {s : Expr O (a :: Γ) b}
    (h : A + e.size + n.size + 1 + s.size ≤ B) : A + (Expr.caseOpt e n s).size ≤ B := by
  simp only [Expr.size]; omega

private theorem le_sz_ret_of {S₀ : Sig} {O : Ops S₀} {ι : Type} {T : OracleSpec ι}
    {I₀ : Iface S₀ T} {Γ : List (Ty S₀)} {a : Ty S₀} {A B E0 : ℕ} {e : Expr O Γ a}
    (he : e.size ≤ E0) (h : A + E0 + 1 ≤ B) : A + (Comp.ret (I := I₀) e).size ≤ B := by
  simp only [Comp.size]; omega

private theorem le_sz_bind {S₀ : Sig} {O : Ops S₀} {ι : Type} {T : OracleSpec ι}
    {I₀ : Iface S₀ T} {Γ : List (Ty S₀)} {a b : Ty S₀} {A B : ℕ}
    {c : Comp O I₀ Γ a} {k : Comp O I₀ (a :: Γ) b}
    (h : A + c.size + 1 + k.size ≤ B) : A + (Comp.bind c k).size ≤ B := by
  simp only [Comp.size]; omega

private theorem le_sz_bind_of {S₀ : Sig} {O : Ops S₀} {ι : Type} {T : OracleSpec ι}
    {I₀ : Iface S₀ T} {Γ : List (Ty S₀)} {a b : Ty S₀} {A B C0 : ℕ}
    {c : Comp O I₀ Γ a} {k : Comp O I₀ (a :: Γ) b}
    (hc : c.size ≤ C0) (h : A + C0 + 1 + k.size ≤ B) : A + (Comp.bind c k).size ≤ B := by
  simp only [Comp.size]; omega

private theorem le_sz_caseOptC {S₀ : Sig} {O : Ops S₀} {ι : Type} {T : OracleSpec ι}
    {I₀ : Iface S₀ T} {Γ : List (Ty S₀)} {a b : Ty S₀} {A B : ℕ}
    {e : Expr O Γ (.opt a)} {n : Comp O I₀ Γ b} {s : Comp O I₀ (a :: Γ) b}
    (h : A + e.size + n.size + 1 + s.size ≤ B) : A + (Comp.caseOpt e n s).size ≤ B := by
  simp only [Comp.size]; omega

private theorem le_sz_caseOptC_of {S₀ : Sig} {O : Ops S₀} {ι : Type} {T : OracleSpec ι}
    {I₀ : Iface S₀ T} {Γ : List (Ty S₀)} {a b : Ty S₀} {A B E0 : ℕ}
    {e : Expr O Γ (.opt a)} {n : Comp O I₀ Γ b} {s : Comp O I₀ (a :: Γ) b}
    (he : e.size ≤ E0) (h : A + E0 + n.size + 1 + s.size ≤ B) :
    A + (Comp.caseOpt e n s).size ≤ B := by
  simp only [Comp.size]; omega

private theorem le_sz_iteC {S₀ : Sig} {O : Ops S₀} {ι : Type} {T : OracleSpec ι}
    {I₀ : Iface S₀ T} {Γ : List (Ty S₀)} {a : Ty S₀} {A B : ℕ}
    {c : Expr O Γ .bool} {t f : Comp O I₀ Γ a}
    (h : A + c.size + t.size + 1 + f.size ≤ B) : A + (Comp.ite c t f).size ≤ B := by
  simp only [Comp.size]; omega

private theorem size_spqrBraidSendC_s {ℓ : ℕ} {Pt : Type} {P : SignalPqxdh.Primitives}
    {C : Crypto} {K : MlKem} {decT : PublicKey → Option Pt} {encT : Pt → PublicKey}
    {ι : Type} {T : OracleSpec ι} {I₀ : Iface (e2eSig ℓ) T} {Γ : List (Ty (e2eSig ℓ))}
    (e : Expr (e2eOps ℓ P C K decT encT) Γ _) :
    (spqrBraidSendC (P := P) (C := C) (K := K) (decT := decT) (encT := encT) I₀ e).size =
      e.size + 2 := rfl

private theorem size_spqrChainFromVnC_s {ℓ : ℕ} {Pt : Type} {P : SignalPqxdh.Primitives}
    {C : Crypto} {K : MlKem} {decT : PublicKey → Option Pt} {encT : Pt → PublicKey}
    {ι : Type} {T : OracleSpec ι} {I₀ : Iface (e2eSig ℓ) T} {Γ : List (Ty (e2eSig ℓ))}
    (e : Expr (e2eOps ℓ P C K decT encT) Γ _) :
    (spqrChainFromVnC (P := P) (C := C) (K := K) (decT := decT) (encT := encT) I₀ e).size =
      e.size + 2 := rfl

private theorem size_spqrChainAddEpochC_s {ℓ : ℕ} {Pt : Type} {P : SignalPqxdh.Primitives}
    {C : Crypto} {K : MlKem} {decT : PublicKey → Option Pt} {encT : Pt → PublicKey}
    {ι : Type} {T : OracleSpec ι} {I₀ : Iface (e2eSig ℓ) T} {Γ : List (Ty (e2eSig ℓ))}
    (e : Expr (e2eOps ℓ P C K decT encT) Γ _) :
    (spqrChainAddEpochC (P := P) (C := C) (K := K) (decT := decT) (encT := encT) I₀ e).size =
      e.size + 2 := rfl

private theorem size_spqrChainNextKeyC_s {ℓ : ℕ} {Pt : Type} {P : SignalPqxdh.Primitives}
    {C : Crypto} {K : MlKem} {decT : PublicKey → Option Pt} {encT : Pt → PublicKey}
    {ι : Type} {T : OracleSpec ι} {I₀ : Iface (e2eSig ℓ) T} {Γ : List (Ty (e2eSig ℓ))}
    (e : Expr (e2eOps ℓ P C K decT encT) Γ _) :
    (spqrChainNextKeyC (P := P) (C := C) (K := K) (decT := decT) (encT := encT) I₀ e).size =
      e.size + 2 := rfl

private theorem size_listGetExpr_s {ℓ : ℕ} {O : Ops (e2eSig ℓ)} {Γ : List (Ty (e2eSig ℓ))}
    {α : Ty (e2eSig ℓ)} (fuel : ℕ) (idx : Expr O Γ .nat) (l : Expr O Γ (.list α)) :
    (listGetExpr fuel idx l).size ≤ idx.size + l.size + 2 * bits fuel + 35 := by
  simp only [listGetExpr, Expr.size, Expr.v0, Expr.v1, Expr.v2, Expr.v3, hb1_s]; omega

private theorem size_spqrEpochIdxExpr_s {ℓ : ℕ} {Pt : Type} {P : SignalPqxdh.Primitives}
    {C : Crypto} {K : MlKem} {decT : PublicKey → Option Pt} {encT : Pt → PublicKey}
    {Γ : List (Ty (e2eSig ℓ))}
    (curEp : Expr (e2eOps ℓ P C K decT encT) Γ _)
    (linksLen : Expr (e2eOps ℓ P C K decT encT) Γ _)
    (epoch : Expr (e2eOps ℓ P C K decT encT) Γ _) :
    (spqrEpochIdxExpr (P := P) (C := C) (K := K) (decT := decT) (encT := encT)
      curEp linksLen epoch).size ≤ curEp.size + linksLen.size + epoch.size + 60 := by
  simp only [spqrEpochIdxExpr, Expr.size, Expr.v0, Expr.v1, size_pureOp_s, E2EPureOp.opSize, hb1_s]
  omega

private theorem size_spqrResolveChainComp_s {ℓ : ℕ} {Pt : Type} {P : SignalPqxdh.Primitives}
    {C : Crypto} {K : MlKem} {decT : PublicKey → Option Pt} {encT : Pt → PublicKey}
    {ι : Type} {T : OracleSpec ι} {I₀ : Iface (e2eSig ℓ) T} {Γ : List (Ty (e2eSig ℓ))}
    (vn? : Expr (e2eOps ℓ P C K decT encT) Γ _)
    (ch? : Expr (e2eOps ℓ P C K decT encT) Γ _) :
    (spqrResolveChainComp (P := P) (C := C) (K := K) (decT := decT) (encT := encT)
      I₀ vn? ch?).size ≤ vn?.size + ch?.size + 25 := by
  simp only [spqrResolveChainComp, Comp.size, Expr.size, Expr.v0, size_spqrChainFromVnC_s]
  omega

private theorem size_spqrAddEpochOptComp_s {ℓ : ℕ} {Pt : Type} {P : SignalPqxdh.Primitives}
    {C : Crypto} {K : MlKem} {decT : PublicKey → Option Pt} {encT : Pt → PublicKey}
    {ι : Type} {T : OracleSpec ι} {I₀ : Iface (e2eSig ℓ) T} {Γ : List (Ty (e2eSig ℓ))}
    (ch : Expr (e2eOps ℓ P C K decT encT) Γ _)
    (epSec? : Expr (e2eOps ℓ P C K decT encT) Γ _) :
    (spqrAddEpochOptComp (P := P) (C := C) (K := K) (decT := decT) (encT := encT)
      I₀ ch epSec?).size ≤ ch.size + epSec?.size + 45 := by
  simp only [spqrAddEpochOptComp, Comp.size, Expr.size, Expr.v0, Expr.v1,
    size_spqrChainAddEpochC_s]
  omega

private theorem size_spqrChainSendKeyComp_s {ℓ : ℕ} {Pt : Type} {P : SignalPqxdh.Primitives}
    {C : Crypto} {K : MlKem} {decT : PublicKey → Option Pt} {encT : Pt → PublicKey}
    {ι : Type} {T : OracleSpec ι} {I₀ : Iface (e2eSig ℓ) T} {Γ : List (Ty (e2eSig ℓ))}
    (ch : Expr (e2eOps ℓ P C K decT encT) Γ _)
    (epoch : Expr (e2eOps ℓ P C K decT encT) Γ _) :
    (spqrChainSendKeyComp (P := P) (C := C) (K := K) (decT := decT) (encT := encT)
      I₀ ch epoch).size ≤ ch.size + epoch.size + 550 := by
  rw [← Nat.zero_add (Comp.size _)]; unfold spqrChainSendKeyComp
  apply le_sz_bind; apply le_sz_iteC; apply le_sz_caseOptC_of (size_spqrEpochIdxExpr_s _ _ _)
  apply le_sz_bind; apply le_sz_caseOptC_of (size_listGetExpr_s 4 _ _)
  apply le_sz_caseOptC; apply le_sz_bind_of (by rw [size_spqrChainNextKeyC_s])
  apply le_sz_caseOptC
  simp only [linksClearSendPrefixExpr, clearLinkSendNextExpr, listDropExpr, listSetExpr,
    Comp.size, Expr.size, Expr.v0, Expr.v1, Expr.v2, Expr.v3, Expr.v4, Expr.v6,
    size_var_s, size_pureOp_s, E2EPureOp.opSize, List.length_nil, hb1_s, hb4_s]
  omega

private theorem size_spqrRunSendChainComp_s {ℓ : ℕ} {Pt : Type} {P : SignalPqxdh.Primitives}
    {C : Crypto} {K : MlKem} {decT : PublicKey → Option Pt} {encT : Pt → PublicKey}
    {ι : Type} {T : OracleSpec ι} {I₀ : Iface (e2eSig ℓ) T} {Γ : List (Ty (e2eSig ℓ))}
    (vn? : Expr (e2eOps ℓ P C K decT encT) Γ _)
    (ch? : Expr (e2eOps ℓ P C K decT encT) Γ _)
    (epSec? : Expr (e2eOps ℓ P C K decT encT) Γ _)
    (msgEpoch : Expr (e2eOps ℓ P C K decT encT) Γ _) :
    (spqrRunSendChainComp (P := P) (C := C) (K := K) (decT := decT) (encT := encT)
      I₀ vn? ch? epSec? msgEpoch).size ≤
      vn?.size + ch?.size + epSec?.size + msgEpoch.size + 700 := by
  rw [← Nat.zero_add (Comp.size _)]; unfold spqrRunSendChainComp
  apply le_sz_bind; apply le_sz_bind_of (size_spqrResolveChainComp_s _ _)
  apply le_sz_caseOptC; apply le_sz_bind_of (size_spqrAddEpochOptComp_s _ _)
  apply le_sz_caseOptC; apply le_sz_iteC
  refine Nat.le_trans (Nat.add_le_add_left (size_spqrChainSendKeyComp_s _ _) _) ?_
  simp only [Comp.size, Expr.size, Expr.v0, Expr.v2, Expr.v4,
    size_var_s, size_pureOp_s, E2EPureOp.opSize]; omega

private theorem size_spqrSendComp_s {ℓ : ℕ} {Pt : Type} {P : SignalPqxdh.Primitives}
    {C : Crypto} {K : MlKem} {decT : PublicKey → Option Pt} {encT : Pt → PublicKey}
    {ι : Type} {T : OracleSpec ι} {I₀ : Iface (e2eSig ℓ) T} {Γ : List (Ty (e2eSig ℓ))}
    (e : Expr (e2eOps ℓ P C K decT encT) Γ _) :
    (spqrSendComp (P := P) (C := C) (K := K) (decT := decT) (encT := encT) I₀ e).size ≤
      e.size + 900 := by
  rw [← Nat.zero_add (Comp.size _)]; unfold spqrSendComp
  apply le_sz_bind; apply le_sz_caseOptC; apply le_sz_caseOptC
  apply le_sz_bind_of (by rw [size_spqrBraidSendC_s])
  apply le_sz_caseOptC; apply le_sz_bind_of (size_spqrRunSendChainComp_s _ _ _ _)
  apply le_sz_caseOptC
  simp only [Comp.size, Expr.size, Expr.v0, Expr.v2, Expr.v3, Expr.v5,
    size_var_s, size_pureOp_s, E2EPureOp.opSize, List.length_nil]; omega

private def optLitSz_s (opt : Option CryptoVerification.E2E.Bytes) : ℕ :=
  match opt with | none => 1 | some bs => bs.length + 3

private theorem optLitSz_le_s (opt : Option CryptoVerification.E2E.Bytes)
    (h : ∀ bs ∈ opt, bs.length ≤ 128) : optLitSz_s opt ≤ 131 := by
  cases opt with
  | none => simp [optLitSz_s]
  | some bs =>
    have hbs : bs.length ≤ 128 := h bs rfl
    simp only [optLitSz_s]
    omega

private theorem size_optBytes32LitE_eq_s {ℓ : ℕ} {Pt : Type} {P : SignalPqxdh.Primitives}
    {C : Crypto} {K : MlKem} {decT : PublicKey → Option Pt} {encT : Pt → PublicKey}
    {Γ' : List (Ty (e2eSig ℓ))} (opt : Option CryptoVerification.E2E.Bytes) :
    (optBytes32LitE (ℓ := ℓ) (P := P) (C := C) (K := K) (decT := decT) (encT := encT)
      (Γ := Γ') opt).size = optLitSz_s opt := by
  cases opt with
  | none => rfl
  | some bs =>
    simp only [optBytes32LitE, optLitSz_s, size_pureOp_s, E2EPureOp.opSize, Expr.size]
    omega

private theorem size_drSendPreE_s {ℓ : ℕ} {Pt : Type} {P : SignalPqxdh.Primitives}
    {C : Crypto} {K : MlKem} {decT : PublicKey → Option Pt} {encT : Pt → PublicKey}
    {Γ : List (Ty (e2eSig ℓ))}
    (gE : Expr (e2eOps ℓ P C K decT encT) Γ CryptoVerification.E2E.Costed.GhostStT) :
    (drSendPreE (ℓ := ℓ) (P := P) (C := C) (K := K) (decT := decT) (encT := encT) gE).size ≤
      gE.size + 120 := by
  simp only [drSendPreE, sessionVersionEffE, gpSc, gpVer, gpRemId, Expr.size,
    Expr.v0, Expr.v1, Expr.v2, size_pureOp_s, E2EPureOp.opSize, hb256_s]
  omega

private theorem size_drSendPostE_s {ℓ : ℕ} {Pt : Type} {P : SignalPqxdh.Primitives}
    {C : Crypto} {K : MlKem} {decT : PublicKey → Option Pt} {encT : Pt → PublicKey}
    {Γ : List (Ty (e2eSig ℓ))}
    (gE : Expr (e2eOps ℓ P C K decT encT) Γ CryptoVerification.E2E.Costed.GhostStT)
    (mE : Expr (e2eOps ℓ P C K decT encT) Γ CryptoVerification.E2E.Costed.PlainT)
    (partsE : Expr (e2eOps ℓ P C K decT encT) Γ ghostPartsT)
    (scE : Expr (e2eOps ℓ P C K decT encT) Γ drSenderChainT)
    (remIdE : Expr (e2eOps ℓ P C K decT encT) Γ IdKey)
    (pqOutE : Expr (e2eOps ℓ P C K decT encT) Γ _) :
    (drSendPostE (P := P) (C := C) (K := K) (decT := decT) (encT := encT)
      gE mE partsE scE remIdE pqOutE).size ≤
      gE.size + mE.size + partsE.size + scE.size + remIdE.size + pqOutE.size + 610 := by
  have h1 := optLitSz_le_s (CryptoVerification.E2E.serializedPartyAddresses
    CryptoVerification.LibsignalTripleRatchetRepr.uuidTryParse .B .A)
    (serializedPartyAddresses_length_le_128 _ .B .A)
  have h2 := optLitSz_le_s (CryptoVerification.E2E.serializedPartyAddresses
    CryptoVerification.LibsignalTripleRatchetRepr.uuidTryParse .A .B)
    (serializedPartyAddresses_length_le_128 _ .A .B)
  rw [← Nat.zero_add (Expr.size _)]; unfold drSendPostE
  apply le_sz_letE; apply le_sz_caseOptE; apply le_sz_letE
  simp only [sendAddrsE, size_optBytes32LitE_eq_s, sessionVersionEffE, sendsInE,
    gpIsB, gpVer, gpLocId, gpRemId, gpRk, gpPrevCtr, gpPend, gpEp, gpCEps, gpRcs, gpMk,
    Expr.size, Expr.v0, Expr.v1, Expr.v2, size_var_s,
    size_pureOp_s, E2EPureOp.opSize, List.length_nil, size_cryptoOp_s, hb0_s, hb1_s, hb2_s]
  omega

private theorem size_drSendC_s {ℓ : ℕ} {Pt : Type} {P : SignalPqxdh.Primitives}
    {C : Crypto} {K : MlKem} {decT : PublicKey → Option Pt} {encT : Pt → PublicKey}
    {ι : Type} {T : OracleSpec ι} {I₀ : Iface (e2eSig ℓ) T} {Γ : List (Ty (e2eSig ℓ))}
    (e : Expr (e2eOps ℓ P C K decT encT) Γ
      (.prod CryptoVerification.E2E.Costed.GhostStT
        (.prod CryptoVerification.E2E.Costed.PlainT CryptoVerification.E2E.Costed.BV512))) :
    (drSendC (spqrDslHooks ℓ P C K decT encT) I₀ e).size ≤ e.size + 1850 := by
  rw [← Nat.zero_add (Comp.size _)]; unfold drSendC; dsimp only [spqrDslHooks]
  apply le_sz_bind; apply le_sz_caseOptC_of (size_drSendPreE_s _)
  apply le_sz_bind_of (size_spqrSendComp_s _); apply le_sz_caseOptC
  apply le_sz_ret_of (size_drSendPostE_s _ _ _ _ _ _)
  simp only [gpPqSt, Comp.size, Expr.size, Expr.v0, Expr.v1, Expr.v2, Expr.v3,
    size_var_s, size_pureOp_s, E2EPureOp.opSize, List.length_nil]; omega

end DirectSendSize

private theorem size_drSendInOracleCtx {ℓ : ℕ} {Pt : Type} (P : SignalPqxdh.Primitives)
    (C : Crypto) (K : MlKem) (decT : PublicKey → Option Pt) (encT : Pt → PublicKey) :
    (drSendInOracleCtx (Pt := Pt) P C K decT encT (ℓ := ℓ)).size ≤ 26726 := by
  have hs := size_drSendC_s (P := P) (C := C) (K := K) (decT := decT) (encT := encT)
    (I₀ := stepAIface ℓ (emptyTargetE2EIface ℓ)) (Γ := e2eOracleSendCtx ℓ)
    (.pair (pGet (e2eGsSt .v0) (.fst (.snd .v2)))
      (.pair (.fst (.snd (.snd .v2))) (.fst .v1)))
  simp only [drSendInOracleCtx, pGet, e2eGsSt, Expr.size, Expr.v0, Expr.v1, Expr.v2, size_var_s] at hs ⊢
  omega

@[expose] def wkSend6Ren {S₀ : Sig} {a b c d e f : Ty S₀} {Δ : List (Ty S₀)} :
    ∀ {τ}, Var [a, b, c, d, e, f] τ → Var (a :: b :: c :: d :: e :: f :: Δ) τ
  | _, .zero => .zero
  | _, .succ .zero => .succ .zero
  | _, .succ (.succ .zero) => .succ (.succ .zero)
  | _, .succ (.succ (.succ .zero)) => .succ (.succ (.succ .zero))
  | _, .succ (.succ (.succ (.succ .zero))) => .succ (.succ (.succ (.succ .zero)))
  | _, .succ (.succ (.succ (.succ (.succ .zero)))) => .succ (.succ (.succ (.succ (.succ .zero))))

private theorem pullEnv_wkSend6Ren {S₀ : Sig} {a b c d e f : Ty S₀} {Δ : List (Ty S₀)}
    (va : a.denote) (vb : b.denote) (vc : c.denote) (vd : d.denote) (ve : e.denote) (vf : f.denote)
    (ρ : Env Δ) :
    pullEnv (wkSend6Ren (Δ := Δ)) (.cons va (.cons vb (.cons vc (.cons vd (.cons ve (.cons vf ρ)))))) =
      .cons va (.cons vb (.cons vc (.cons vd (.cons ve (.cons vf .nil))))) :=
  rfl

@[expose] def drSendStageCallC {ℓ : ℕ} {Pt : Type} (P : SignalPqxdh.Primitives)
    (C : Crypto) (K : MlKem) (decT : PublicKey → Option Pt) (encT : Pt → PublicKey) :
    Comp (e2eOps ℓ P C K decT encT) (stepAIface ℓ (emptyTargetE2EIface ℓ))
      [e2eSendCallInTy ℓ]
      (.prod CryptoVerification.E2E.Costed.GhostStT (CryptoVerification.E2E.Costed.B 32)) :=
  .bind (.ret (.pair (.fst .v0) (.inr (.inr (.inr (.inr (.bool false)))))))
    (.bind (.ret .v0)
      (.bind (.ret (.pair (.fst (.snd .v2)) (.pair (.fst (.snd (.snd .v2))) .none)))
        (.bind (.ret (.pair (.fst .v3) .v0))
          (.bind (.ret (.pair (.snd (.snd (.snd .v4))) (.bool false)))
            (.bind (.ret (.fst .v5))
              (renComp wkSend6Ren (drSendInOracleCtx P C K decT encT)))))))

private theorem drSendStageCallC_queries_zero {ℓ : ℕ} {Pt : Type} (P : SignalPqxdh.Primitives)
    (C : Crypto) (K : MlKem) (decT : PublicKey → Option Pt) (encT : Pt → PublicKey)
    (w : (stepAIface ℓ (emptyTargetE2EIface ℓ)).Tag → ℕ) :
    (drSendStageCallC P C K decT encT).queries w (fun _ => 0) = 0 := by
  simp [drSendStageCallC, drSendInOracleCtx, Comp.queries, renComp_queries, drSendC_queries]

private theorem drSendStageCallC_cost_le {ℓ : ℕ} {Pt : Type} (P : SignalPqxdh.Primitives)
    (C : Crypto) (K : MlKem) (decT : PublicKey → Option Pt) (encT : Pt → PublicKey) :
    (drSendStageCallC P C K decT encT (ℓ := ℓ)).cost ≤ 67900 + 10 * (ℓ / 32 + 1) := by
  have hc := drSendC_cost (spqrDslHooks ℓ P C K decT encT) (stepAIface ℓ (emptyTargetE2EIface ℓ))
    (.pair (pGet (e2eGsSt .v0) (.fst (.snd .v2)))
      (.pair (.fst (.snd (.snd .v2))) (.fst .v1)) :
      Expr (e2eOps ℓ P C K decT encT) (e2eOracleSendCtx ℓ) _)
  simp only [drSendStageCallC, drSendInOracleCtx, pGet, e2eGsSt, renComp_cost, Comp.cost, Expr.cost,
    Expr.v0, Expr.v1, Expr.v2, Expr.v3, Expr.v4, Expr.v5] at hc ⊢
  omega

private theorem drSendStageCallC_size_le {ℓ : ℕ} {Pt : Type} (P : SignalPqxdh.Primitives)
    (C : Crypto) (K : MlKem) (decT : PublicKey → Option Pt) (encT : Pt → PublicKey) :
    (drSendStageCallC P C K decT encT (ℓ := ℓ)).size ≤ 26770 := by
  have hs := size_drSendInOracleCtx P C K decT encT (ℓ := ℓ)
  simp only [drSendStageCallC, renComp_size_loc, Comp.size, Expr.size,
    Expr.v0, Expr.v2, Expr.v3, Expr.v4, Expr.v5]
  omega

private theorem drSendStageCallC_eval {ℓ : ℕ} {Pt : Type} (P : SignalPqxdh.Primitives)
    (C : Crypto) (K : MlKem) (decT : PublicKey → Option Pt) (encT : Pt → PublicKey)
    (idA idB : IdentityKey) (spkCoins : BitVec 256)
    (s1 : GameState (GhostState Bytes) (Plain ℓ) Bytes)
    (party : Party) (m : Plain ℓ) (rCoins : BitVec 512)
    (hgParty : PartyReachInv C K (s1.st party)) :
    (drSendStageCallC P C K decT encT).eval
        (.cons (e2eGsEnc s1, (partyEnc party, (m, rCoins))) .nil) =
      pure ((sessionSchemeFixedSpk
        (paramsIdsWithSpqr C (spqrV1SessionUniformCoins C.F K) idA idB) ℓ spkCoins).send
        (s1.st party) m rCoins) := by
  simp only [drSendStageCallC, Comp.eval, Expr.eval, Expr.v0, Expr.v2, Expr.v3, Expr.v4, Expr.v5,
    Env.get, pure_bind, renComp_eval, pullEnv_wkSend6Ren]
  set ρSend : Env (e2eOracleSendCtx ℓ) :=
    .cons (e2eGsEnc s1)
      (.cons (rCoins, false)
        (.cons (e2eGsEnc s1, (partyEnc party, (m, none)))
          (.cons (partyEnc party, (m, none))
            (.cons (e2eGsEnc s1, Sum.inr (Sum.inr (Sum.inr (Sum.inr false))))
              (.cons (e2eGsEnc s1, Sum.inr (Sum.inr (Sum.inr (Sum.inr false)))) .nil)))))
  have hIn :
      (Expr.pair (pGet (e2eGsSt (Expr.v0 (O := e2eOps ℓ P C K decT encT))) (.fst (.snd .v2)))
        (.pair (.fst (.snd (.snd .v2))) (.fst .v1))).eval ρSend =
      (s1.st party, (m, rCoins)) := by
    have hp := pGet_eval (e2eGsSt (Expr.v0 (O := e2eOps ℓ P C K decT encT)))
      (.fst (.snd .v2)) ρSend s1.st party rfl rfl
    simp only [Expr.eval, hp]
    rfl
  have hgIn : PartyReachInv C K
      ((Expr.pair (pGet (e2eGsSt (Expr.v0 (O := e2eOps ℓ P C K decT encT))) (.fst (.snd .v2)))
        (.pair (.fst (.snd (.snd .v2))) (.fst .v1))).eval ρSend).1 := by
    rw [hIn]; exact hgParty
  unfold drSendInOracleCtx
  rw [drSendC_eval (spqrDslHooks ℓ P C K decT encT) (stepAIface ℓ (emptyTargetE2EIface ℓ)) _
    ρSend idA idB spkCoins hgIn, hIn]

/-- Pre-tracker `e2eOps` stage for `transmit`. -/
@[expose] def drTrSendStageC {ℓ : ℕ} {Pt : Type} (P : SignalPqxdh.Primitives)
    (C : Crypto) (K : MlKem) (decT : PublicKey → Option Pt) (encT : Pt → PublicKey)
    (q Δ qep : ℕ) :
    Comp (e2eOps ℓ P C K decT encT) (stepAIface ℓ (emptyTargetE2EIface ℓ))
      [e2eTrInTy ℓ] (e2eSendStageOutTy ℓ) :=
  .ite (CryptoGames.SM.orE (.not (e2eSendOKE (.fst .v0) (.fst (.snd .v0)))) (e2eGsWin (.fst .v0)))
    (.ret .none)
    (.bind (e2eSamIfNec512C
        (e2eStepACoinSamplers ℓ P C K decT encT (emptyTargetE2EIface ℓ))
        (.snd (.snd (.snd .v0))))
      (.caseOpt (e2eEpMgmtE Δ qep (.fst .v1) (.fst (.snd .v1)) (.snd .v0))
        (.ret .none)
        (.bind (.ret (.pair .v0
            (.pair (.fst (.snd .v2)) (.pair (.fst (.snd (.snd .v2))) (.fst .v1)))))
          (.bind (wk1Comp (drSendStageCallC P C K decT encT))
            (let st' : Expr (e2eOps ℓ P C K decT encT) _ _ := .fst .v0
             let ct' : Expr (e2eOps ℓ P C K decT encT) _ _ := .snd .v0
             let s1 : Expr (e2eOps ℓ P C K decT encT) _ (e2eGsTy ℓ) := .v2
             let rCoins : Expr (e2eOps ℓ P C K decT encT) _ _ := .fst .v3
             let p4 : Expr (e2eOps ℓ P C K decT encT) _ .bool := .fst (.snd .v4)
             let m4 : Expr (e2eOps ℓ P C K decT encT) _ _ := .fst (.snd (.snd .v4))
             let posE : Expr (e2eOps ℓ P C K decT encT) _ posTy :=
               .pair p4 (.pair (pGet (e2eGsEpoch s1) p4) (.add (pGet (e2eGsIdx s1) p4) (.nat 1)))
             .ret (.some (.pair rCoins
               (.pair ct' (e2eRecordE q Δ s1 p4 st' posE m4 ct' (.bool false))))))))))

/-- Pre-tracker `e2eOps` stage for `chall`. -/
@[expose] def drChSendStageC {ℓ : ℕ} {Pt : Type} (P : SignalPqxdh.Primitives)
    (C : Crypto) (K : MlKem) (decT : PublicKey → Option Pt) (encT : Pt → PublicKey)
    (q Δ qep : ℕ) :
    Comp (e2eOps ℓ P C K decT encT) (stepAIface ℓ (emptyTargetE2EIface ℓ))
      [e2eChInTy ℓ] (e2eSendStageOutTy ℓ) :=
  .ite (CryptoGames.SM.orE (.not (e2eSendOKE (.fst .v0) (.fst (.snd .v0)))) (e2eGsWin (.fst .v0)))
    (.ret .none)
    (.bind (e2eSamIfNec512C
        (e2eStepACoinSamplers ℓ P C K decT encT (emptyTargetE2EIface ℓ))
        (.snd (.snd (.snd (.snd .v0)))))
      (.caseOpt (e2eEpMgmtE Δ qep (.fst .v1) (.fst (.snd .v1)) (.snd .v0))
        (.ret .none)
        (.ite (.not (e2eSafeChE Δ .v0 (.fst (.snd .v2))))
          (.ret .none)
          (let mCh2 : Expr (e2eOps ℓ P C K decT encT) _ _ :=
             .ite (e2eGsB (.fst .v2))
               (.fst (.snd (.snd (.snd .v2))))
               (.fst (.snd (.snd .v2)))
           .bind (.ret (.pair .v0 (.pair (.fst (.snd .v2)) (.pair mCh2 (.fst .v1)))))
             (.bind (wk1Comp (drSendStageCallC P C K decT encT))
               (let st' : Expr (e2eOps ℓ P C K decT encT) _ _ := .fst .v0
                let ct' : Expr (e2eOps ℓ P C K decT encT) _ _ := .snd .v0
                let s1 : Expr (e2eOps ℓ P C K decT encT) _ (e2eGsTy ℓ) := .v2
                let rCoins : Expr (e2eOps ℓ P C K decT encT) _ _ := .fst .v3
                let gs4 : Expr (e2eOps ℓ P C K decT encT) _ (e2eGsTy ℓ) := .fst .v4
                let p4 : Expr (e2eOps ℓ P C K decT encT) _ .bool := .fst (.snd .v4)
                let mCh4 : Expr (e2eOps ℓ P C K decT encT) _ _ :=
                  .ite (e2eGsB gs4)
                    (.fst (.snd (.snd (.snd .v4))))
                    (.fst (.snd (.snd .v4)))
                let posE : Expr (e2eOps ℓ P C K decT encT) _ posTy :=
                  .pair p4 (.pair (pGet (e2eGsEpoch s1) p4) (.add (pGet (e2eGsIdx s1) p4) (.nat 1)))
                .ret (.some (.pair rCoins
                  (.pair ct' (e2eRecordE q Δ s1 p4 st' posE mCh4 ct' (.bool true)))))))))))

@[simp] theorem drTrSendStageC_queries_zero {ℓ : ℕ} {Pt : Type} (P : SignalPqxdh.Primitives)
    (C : Crypto) (K : MlKem) (decT : PublicKey → Option Pt) (encT : Pt → PublicKey)
    (q Δ qep : ℕ) (w : (stepAIface ℓ (emptyTargetE2EIface ℓ)).Tag → ℕ) :
    (drTrSendStageC P C K decT encT q Δ qep).queries w (fun _ => 0) = 0 := by
  simp [drTrSendStageC, Comp.queries, e2eSamIfNec512C_queries_zero,
    wk1Comp_queries, drSendStageCallC_queries_zero]

@[simp] theorem drChSendStageC_queries_zero {ℓ : ℕ} {Pt : Type} (P : SignalPqxdh.Primitives)
    (C : Crypto) (K : MlKem) (decT : PublicKey → Option Pt) (encT : Pt → PublicKey)
    (q Δ qep : ℕ) (w : (stepAIface ℓ (emptyTargetE2EIface ℓ)).Tag → ℕ) :
    (drChSendStageC P C K decT encT q Δ qep).queries w (fun _ => 0) = 0 := by
  simp [drChSendStageC, Comp.queries, e2eSamIfNec512C_queries_zero,
    wk1Comp_queries, drSendStageCallC_queries_zero]

theorem drTrSendStageC_cost_le {ℓ : ℕ} {Pt : Type} (P : SignalPqxdh.Primitives)
    (C : Crypto) (K : MlKem) (decT : PublicKey → Option Pt) (encT : Pt → PublicKey)
    (q Δ qep : ℕ) :
    (drTrSendStageC P C K decT encT q Δ qep (ℓ := ℓ)).cost ≤
      70500 + 10 * (ℓ / 32 + 1) + 135 * q + 2 * bits Δ + bits qep := by
  let OO := e2eOps ℓ P C K decT encT
  let tOut : Ty (e2eSig ℓ) := .prod CryptoVerification.E2E.Costed.GhostStT
    (CryptoVerification.E2E.Costed.B 32)
  have hsendOK := cost_e2eSendOKE_le (ℓ := ℓ) (O' := OO)
    (.fst .v0 : Expr OO [e2eTrInTy ℓ] (e2eGsTy ℓ)) (.fst (.snd .v0))
  have hsam := e2eSamIfNec512C_cost
    (e2eStepACoinSamplers ℓ P C K decT encT (emptyTargetE2EIface ℓ))
    (.snd (.snd (.snd .v0)) : Expr OO [e2eTrInTy ℓ] _)
  have hep := cost_e2eEpMgmtE_le (ℓ := ℓ) (O' := OO) Δ qep
    (.fst .v1 : Expr OO [e2eCoinsBadT ℓ, e2eTrInTy ℓ] (e2eGsTy ℓ)) (.fst (.snd .v1)) (.snd .v0)
  have hsend := drSendStageCallC_cost_le P C K decT encT (ℓ := ℓ) (Pt := Pt)
  have hrec := cost_e2eRecordE_le (ℓ := ℓ) (O' := OO) q Δ
    (.v2 : Expr OO [tOut, e2eSendCallInTy ℓ, e2eGsTy ℓ, e2eCoinsBadT ℓ, e2eTrInTy ℓ] (e2eGsTy ℓ))
    (.fst (.snd .v4)) (.fst .v0)
    (.pair (.fst (.snd .v4))
      (.pair (pGet (e2eGsEpoch .v2) (.fst (.snd .v4)))
        (.add (pGet (e2eGsIdx .v2) (.fst (.snd .v4))) (.nat 1))))
    (.fst (.snd (.snd .v4))) (.snd .v0) (.bool false)
  have hb1 : bits 1 = 1 := rfl
  simp only [drTrSendStageC, CryptoGames.SM.orE, pGet, e2eGsWin, e2eGsEpoch, e2eGsIdx,
    wk1Comp_cost, Comp.cost, Expr.cost, Expr.v0, Expr.v1, Expr.v2, Expr.v3, Expr.v4, hb1]
    at hsendOK hsam hep hrec ⊢
  omega

theorem drChSendStageC_cost_le {ℓ : ℕ} {Pt : Type} (P : SignalPqxdh.Primitives)
    (C : Crypto) (K : MlKem) (decT : PublicKey → Option Pt) (encT : Pt → PublicKey)
    (q Δ qep : ℕ) :
    (drChSendStageC P C K decT encT q Δ qep (ℓ := ℓ)).cost ≤
      70700 + 10 * (ℓ / 32 + 1) + 135 * q + 3 * bits Δ + bits qep := by
  let OO := e2eOps ℓ P C K decT encT
  let tOut : Ty (e2eSig ℓ) := .prod CryptoVerification.E2E.Costed.GhostStT
    (CryptoVerification.E2E.Costed.B 32)
  have hsendOK := cost_e2eSendOKE_le (ℓ := ℓ) (O' := OO)
    (.fst .v0 : Expr OO [e2eChInTy ℓ] (e2eGsTy ℓ)) (.fst (.snd .v0))
  have hsam := e2eSamIfNec512C_cost
    (e2eStepACoinSamplers ℓ P C K decT encT (emptyTargetE2EIface ℓ))
    (.snd (.snd (.snd (.snd .v0))) : Expr OO [e2eChInTy ℓ] _)
  have hep := cost_e2eEpMgmtE_le (ℓ := ℓ) (O' := OO) Δ qep
    (.fst .v1 : Expr OO [e2eCoinsBadT ℓ, e2eChInTy ℓ] (e2eGsTy ℓ)) (.fst (.snd .v1)) (.snd .v0)
  have hsafe := cost_e2eSafeChE_le (ℓ := ℓ) (O' := OO) Δ
    (.v0 : Expr OO [e2eGsTy ℓ, e2eCoinsBadT ℓ, e2eChInTy ℓ] (e2eGsTy ℓ)) (.fst (.snd .v2))
  have hsend := drSendStageCallC_cost_le P C K decT encT (ℓ := ℓ) (Pt := Pt)
  have hrec := cost_e2eRecordE_le (ℓ := ℓ) (O' := OO) q Δ
    (.v2 : Expr OO [tOut, e2eSendCallInTy ℓ, e2eGsTy ℓ, e2eCoinsBadT ℓ, e2eChInTy ℓ] (e2eGsTy ℓ))
    (.fst (.snd .v4)) (.fst .v0)
    (.pair (.fst (.snd .v4))
      (.pair (pGet (e2eGsEpoch .v2) (.fst (.snd .v4)))
        (.add (pGet (e2eGsIdx .v2) (.fst (.snd .v4))) (.nat 1))))
    (.ite (e2eGsB (.fst .v4))
      (.fst (.snd (.snd (.snd .v4)))) (.fst (.snd (.snd .v4))))
    (.snd .v0) (.bool true)
  have hb1 : bits 1 = 1 := rfl
  simp only [drChSendStageC, CryptoGames.SM.orE, pGet, e2eGsB, e2eGsWin, e2eGsEpoch, e2eGsIdx,
    wk1Comp_cost, Comp.cost, Expr.cost, Expr.v0, Expr.v1, Expr.v2, Expr.v3, Expr.v4, hb1]
    at hsendOK hsam hep hsafe hrec ⊢
  omega

/-! ## Bookkeeping size helpers -/

theorem size_var_loc {S₀ : Sig} {O : Ops S₀} {Γ : List (Ty S₀)} {τ : Ty S₀}
    (x : Var Γ τ) : (Expr.var (O := O) x).size = 1 := rfl

private theorem size_sm_orE_loc {S₀ : Sig} {O : Ops S₀} {Γ : List (Ty S₀)}
    (a b : Expr O Γ .bool) : (CryptoGames.SM.orE a b).size = a.size + b.size + 2 := by
  simp only [CryptoGames.SM.orE, Expr.size]; omega

private theorem size_e2eSendOKE_loc {ℓ : ℕ} {O : Ops (e2eSig ℓ)} {Γ : List (Ty (e2eSig ℓ))}
    (s : Expr O Γ (e2eGsTy ℓ)) (p : Expr O Γ .bool) :
    (e2eSendOKE s p).size ≤ s.size + p.size + 30 := by
  have hb0 : bits 0 = 1 := rfl
  simp only [e2eSendOKE, e2eGsEpoch, Expr.size, Expr.v0, hb0]
  omega

private theorem size_e2eSafeChE_loc {ℓ : ℕ} {O : Ops (e2eSig ℓ)} {Γ : List (Ty (e2eSig ℓ))}
    (Δ : ℕ) (s : Expr O Γ (e2eGsTy ℓ)) (p : Expr O Γ .bool) :
    (e2eSafeChE Δ s p).size ≤ s.size + p.size + bits Δ + 60 := by
  have hb0 : bits 0 = 1 := rfl
  have hb1 : bits 1 = 1 := rfl
  unfold e2eSafeChE
  simp only [e2eGsEpoch, e2eGsTL, pGet, healedByE, leN,
    Expr.size, Expr.v0, Expr.v1]
  omega

private theorem size_e2eEpMgmtE_loc {ℓ : ℕ} {O : Ops (e2eSig ℓ)} {Γ : List (Ty (e2eSig ℓ))}
    (Δ qep : ℕ) (s : Expr O Γ (e2eGsTy ℓ)) (p bad : Expr O Γ .bool) :
    (e2eEpMgmtE Δ qep s p bad).size ≤
      s.size + p.size + bad.size + bits Δ + 2 * bits qep + 550 := by
  have hb0 : bits 0 = 1 := rfl
  have hb1 : bits 1 = 1 := rfl
  have hb2 : bits 2 = 2 := rfl
  unfold e2eEpMgmtE
  simp only [e2eSafeChE, e2eLeakE, e2eGsMk, e2eGsSt, e2eGsB, e2eGsWin, e2eGsEpoch, e2eGsIdx,
    e2eGsTL, e2eGsTrans, e2eGsChall, e2eGsComp, e2eGsMaxAcc, e2eGsLeaks, e2eGsCorrs,
    pGet, pSet, sendsInE, healedByE, leN, maxN, maxOptE,
    Expr.size, Expr.v0, Expr.v1, size_var_loc, hb0, hb1, hb2]
  omega

private theorem size_e2eCompContainsE_loc {ℓ : ℕ} {O : Ops (e2eSig ℓ)} {Γ : List (Ty (e2eSig ℓ))}
    (q : ℕ) (s : Expr O Γ (e2eGsTy ℓ)) (pos : Expr O Γ posTy) :
    (e2eCompContainsE q s pos).size ≤ s.size + pos.size + bits q + 60 := by
  unfold e2eCompContainsE
  simp only [e2eGsComp, posEq, posSender, posEpoch, posIdx, boolEq,
    Expr.size, Expr.v0, Expr.v1]
  omega

private theorem le_size_letE_loc {S₀ : Sig} {O : Ops S₀} {Γ : List (Ty S₀)} {a b : Ty S₀} {A B : ℕ}
    {e : Expr O Γ a} {k : Expr O (a :: Γ) b}
    (h : A + e.size + 1 + k.size ≤ B) : A + (Expr.letE e k).size ≤ B := by
  simp only [Expr.size]; omega

private theorem le_size_letE_of_loc {S₀ : Sig} {O : Ops S₀} {Γ : List (Ty S₀)} {a b : Ty S₀} {A B E0 : ℕ}
    {e : Expr O Γ a} {k : Expr O (a :: Γ) b}
    (he : e.size ≤ E0) (h : A + E0 + 1 + k.size ≤ B) : A + (Expr.letE e k).size ≤ B := by
  simp only [Expr.size]; omega

private theorem size_e2eRecordE_loc {ℓ : ℕ} {O : Ops (e2eSig ℓ)} {Γ : List (Ty (e2eSig ℓ))}
    (q Δ : ℕ) (s : Expr O Γ (e2eGsTy ℓ)) (p : Expr O Γ .bool)
    (st' : Expr O Γ CryptoVerification.E2E.Costed.GhostStT) (pos : Expr O Γ posTy)
    (msg : Expr O Γ CryptoVerification.E2E.Costed.PlainT)
    (ct : Expr O Γ (CryptoVerification.E2E.Costed.B 32)) (isChall : Expr O Γ .bool) :
    (e2eRecordE q Δ s p st' pos msg ct isChall).size ≤
      s.size + p.size + st'.size + pos.size + msg.size + ct.size + isChall.size +
        bits Δ + 2 * bits q + 500 := by
  rw [← Nat.zero_add (Expr.size _)]; unfold e2eRecordE
  apply le_size_letE_loc
  apply le_size_letE_of_loc (by
    simp only [Expr.size]
    exact Nat.add_le_add_right
      (Nat.add_le_add (size_e2eSafeChE_loc Δ _ _) (size_e2eCompContainsE_loc q _ _)) 1)
  simp only [e2eGsMk, e2eRecMk, e2eRecPos, e2eRecMsg, e2eRecCt, e2eRecComp,
    e2eGsSt, e2eGsB, e2eGsWin, e2eGsEpoch, e2eGsIdx,
    e2eGsTL, e2eGsTrans, e2eGsChall, e2eGsComp, e2eGsMaxAcc, e2eGsLeaks, e2eGsCorrs,
    pSet, posSender, posEpoch, posIdx, posEq, boolEq, size_sm_orE_loc,
    Expr.size, Expr.v0, Expr.v1, Expr.v2, size_var_loc]
  omega

private theorem size_samIfNec512_loc {ℓ : ℕ} {Pt : Type} (P : SignalPqxdh.Primitives)
    (C : Crypto) (K : MlKem) (decT : PublicKey → Option Pt) (encT : Pt → PublicKey)
    {Γ : List (Ty (e2eSig ℓ))}
    (optR : Expr (e2eOps ℓ P C K decT encT) Γ (.opt CryptoVerification.E2E.Costed.BV512)) :
    (e2eSamIfNec512C
      (e2eStepACoinSamplers ℓ P C K decT encT (emptyTargetE2EIface ℓ)) optR).size ≤
      optR.size + 25 := by
  simp only [e2eSamIfNec512C, e2eStepACoinSamplers, DrSessionSim.E2ECoinSamplers.ofSmpEq,
    DrSessionSim.mkE2ECoinSamplers, Comp.size, Expr.size, Expr.v0]
  omega

theorem drTrSendStageC_size_le {ℓ : ℕ} {Pt : Type} (P : SignalPqxdh.Primitives)
    (C : Crypto) (K : MlKem) (decT : PublicKey → Option Pt) (encT : Pt → PublicKey)
    (q Δ qep : ℕ) :
    (drTrSendStageC P C K decT encT q Δ qep (ℓ := ℓ)).size ≤
      28100 + 2 * bits q + 2 * bits Δ + 2 * bits qep := by
  let OO := e2eOps ℓ P C K decT encT
  let tOut : Ty (e2eSig ℓ) := .prod CryptoVerification.E2E.Costed.GhostStT
    (CryptoVerification.E2E.Costed.B 32)
  have hsendOK := size_e2eSendOKE_loc (O := OO)
    (.fst .v0 : Expr OO [e2eTrInTy ℓ] (e2eGsTy ℓ)) (.fst (.snd .v0))
  have hsam := size_samIfNec512_loc P C K decT encT (Pt := Pt)
    (.snd (.snd (.snd .v0)) : Expr OO [e2eTrInTy ℓ] _)
  have hep := size_e2eEpMgmtE_loc (O := OO) Δ qep
    (.fst .v1 : Expr OO [e2eCoinsBadT ℓ, e2eTrInTy ℓ] (e2eGsTy ℓ)) (.fst (.snd .v1)) (.snd .v0)
  have hsend := drSendStageCallC_size_le P C K decT encT (ℓ := ℓ) (Pt := Pt)
  have hrec := size_e2eRecordE_loc (O := OO) q Δ
    (.v2 : Expr OO [tOut, e2eSendCallInTy ℓ, e2eGsTy ℓ, e2eCoinsBadT ℓ, e2eTrInTy ℓ] (e2eGsTy ℓ))
    (.fst (.snd .v4)) (.fst .v0)
    (.pair (.fst (.snd .v4))
      (.pair (pGet (e2eGsEpoch .v2) (.fst (.snd .v4)))
        (.add (pGet (e2eGsIdx .v2) (.fst (.snd .v4))) (.nat 1))))
    (.fst (.snd (.snd .v4))) (.snd .v0) (.bool false)
  have hb1 : bits 1 = 1 := rfl
  simp only [drTrSendStageC, size_sm_orE_loc, pGet, e2eGsWin, e2eGsEpoch, e2eGsIdx,
    wk1Comp_size_loc, Comp.size, Expr.size, Expr.v0, Expr.v1, Expr.v2, Expr.v3, Expr.v4,
    size_var_loc, hb1] at hsendOK hsam hep hrec ⊢
  omega

theorem drChSendStageC_size_le {ℓ : ℕ} {Pt : Type} (P : SignalPqxdh.Primitives)
    (C : Crypto) (K : MlKem) (decT : PublicKey → Option Pt) (encT : Pt → PublicKey)
    (q Δ qep : ℕ) :
    (drChSendStageC P C K decT encT q Δ qep (ℓ := ℓ)).size ≤
      28200 + 2 * bits q + 3 * bits Δ + 2 * bits qep := by
  let OO := e2eOps ℓ P C K decT encT
  let tOut : Ty (e2eSig ℓ) := .prod CryptoVerification.E2E.Costed.GhostStT
    (CryptoVerification.E2E.Costed.B 32)
  have hsendOK := size_e2eSendOKE_loc (O := OO)
    (.fst .v0 : Expr OO [e2eChInTy ℓ] (e2eGsTy ℓ)) (.fst (.snd .v0))
  have hsam := size_samIfNec512_loc P C K decT encT (Pt := Pt)
    (.snd (.snd (.snd (.snd .v0))) : Expr OO [e2eChInTy ℓ] _)
  have hep := size_e2eEpMgmtE_loc (O := OO) Δ qep
    (.fst .v1 : Expr OO [e2eCoinsBadT ℓ, e2eChInTy ℓ] (e2eGsTy ℓ)) (.fst (.snd .v1)) (.snd .v0)
  have hsafe := size_e2eSafeChE_loc (O := OO) Δ
    (.v0 : Expr OO [e2eGsTy ℓ, e2eCoinsBadT ℓ, e2eChInTy ℓ] (e2eGsTy ℓ)) (.fst (.snd .v2))
  have hsend := drSendStageCallC_size_le P C K decT encT (ℓ := ℓ) (Pt := Pt)
  have hrec := size_e2eRecordE_loc (O := OO) q Δ
    (.v2 : Expr OO [tOut, e2eSendCallInTy ℓ, e2eGsTy ℓ, e2eCoinsBadT ℓ, e2eChInTy ℓ] (e2eGsTy ℓ))
    (.fst (.snd .v4)) (.fst .v0)
    (.pair (.fst (.snd .v4))
      (.pair (pGet (e2eGsEpoch .v2) (.fst (.snd .v4)))
        (.add (pGet (e2eGsIdx .v2) (.fst (.snd .v4))) (.nat 1))))
    (.ite (e2eGsB (.fst .v4))
      (.fst (.snd (.snd (.snd .v4)))) (.fst (.snd (.snd .v4))))
    (.snd .v0) (.bool true)
  have hb1 : bits 1 = 1 := rfl
  simp only [drChSendStageC, size_sm_orE_loc, pGet, e2eGsB, e2eGsWin, e2eGsEpoch, e2eGsIdx,
    wk1Comp_size_loc, Comp.size, Expr.size, Expr.v0, Expr.v1, Expr.v2, Expr.v3, Expr.v4,
    size_var_loc, hb1] at hsendOK hsam hep hsafe hrec ⊢
  omega

/-! ## Stage evaluation and `SmReachBounded` preservation -/

@[expose] def trStageProb {ℓ : ℕ} {RCoins : Type}
    (sm : SMSchemeR SampledSessionKey (GhostState Bytes) (Plain ℓ) (BitVec 512) RCoins Bytes)
    (Δ qep : ℕ) (cfg : ConfigR (GhostState Bytes) (Plain ℓ) Bytes)
    (gs : GameState (GhostState Bytes) (Plain ℓ) Bytes)
    (Q : Party) (m : Plain ℓ) (optR : Option (BitVec 512)) :
    ProbComp (Option (BitVec 512 × (Bytes × GameState (GhostState Bytes) (Plain ℓ) Bytes))) :=
  if !(cfg.sendOK gs Q) || gs.win then pure none
  else do
    let (coins, bad) ← samIfNec optR
    match gs.epMgmt Δ qep Q bad with
    | none => pure none
    | some s₁ =>
      let out := sm.send (s₁.st Q) m coins
      pure (some (coins, (out.2,
        s₁.record Δ Q out.1 ⟨⟨Q, s₁.epoch Q, s₁.idx Q + 1⟩, m, out.2⟩ false)))

@[expose] def chStageProb {ℓ : ℕ} {RCoins : Type}
    (sm : SMSchemeR SampledSessionKey (GhostState Bytes) (Plain ℓ) (BitVec 512) RCoins Bytes)
    (Δ qep : ℕ) (cfg : ConfigR (GhostState Bytes) (Plain ℓ) Bytes)
    (gs : GameState (GhostState Bytes) (Plain ℓ) Bytes)
    (Q : Party) (m0 m1 : Plain ℓ) (optR : Option (BitVec 512)) :
    ProbComp (Option (BitVec 512 × (Bytes × GameState (GhostState Bytes) (Plain ℓ) Bytes))) :=
  if !(cfg.sendOK gs Q) || gs.win then pure none
  else do
    let (coins, bad) ← samIfNec optR
    match gs.epMgmt Δ qep Q bad with
    | none => pure none
    | some s₁ =>
      if !(s₁.safeCh Δ Q) then pure none
      else
        let mCh := if gs.b then m1 else m0
        let out := sm.send (s₁.st Q) mCh coins
        pure (some (coins, (out.2,
          s₁.record Δ Q out.1 ⟨⟨Q, s₁.epoch Q, s₁.idx Q + 1⟩, mCh, out.2⟩ true)))

theorem drTrSendStageC_eval {ℓ : ℕ} {Pt : Type} (P : SignalPqxdh.Primitives)
    (C : Crypto) (K : MlKem) (decT : PublicKey → Option Pt) (encT : Pt → PublicKey)
    (q Δ qep : ℕ) (idA idB : IdentityKey) (spkCoins : BitVec 256)
    (gs : GameState (GhostState Bytes) (Plain ℓ) Bytes)
    (Q : Party) (m : Plain ℓ) (optR : Option (BitVec 512))
    (h : SmReachBounded C K q gs) :
    (drTrSendStageC P C K decT encT q Δ qep).eval
        (.cons (e2eGsEnc gs, (partyEnc Q, (m, optR))) .nil) =
      (stepAIface ℓ (emptyTargetE2EIface ℓ)).liftP
        ((Option.map fun (coins, (ct, gsRec)) => (coins, (ct, e2eGsEnc gsRec))) <$>
          trStageProb
            (sessionSchemeFixedSpk
              (paramsIdsWithSpqr C (spqrV1SessionUniformCoins C.F K) idA idB) ℓ spkCoins)
            Δ qep (configRefuseEarlyBobCorr decT encT) gs Q m optR) := by
  let OO := e2eOps ℓ P C K decT encT
  set sm := sessionSchemeFixedSpk
    (paramsIdsWithSpqr C (spqrV1SessionUniformCoins C.F K) idA idB) ℓ spkCoins
  set cfg : ConfigR (GhostState Bytes) (Plain ℓ) Bytes := configRefuseEarlyBobCorr decT encT
  set ρ₁ : Env [e2eTrInTy ℓ] := .cons (e2eGsEnc gs, (partyEnc Q, (m, optR))) .nil
  unfold drTrSendStageC trStageProb
  have hSendOK : (e2eSendOKE (.fst (Expr.v0 (O := OO))) (.fst (.snd .v0))).eval ρ₁ =
      cfg.sendOK gs Q :=
    eval_e2eSendOKE decT encT (.fst .v0) (.fst (.snd .v0)) ρ₁ gs Q rfl rfl
  have hWin : (e2eGsWin (.fst (Expr.v0 (O := OO)))).eval ρ₁ = gs.win := rfl
  simp only [Comp.eval, CryptoGames.SM.orE, Expr.eval, hSendOK, hWin]
  by_cases hok : cfg.sendOK gs Q
  · by_cases hwin : gs.win
    · simp [hok, hwin]
    · have hOptR : (Expr.snd (.snd (.snd (Expr.v0 (O := OO))))).eval ρ₁ = optR := rfl
      simp only [hok, hwin, Bool.not_true, Bool.or_self, Bool.false_eq_true, ↓reduceIte,
        e2eSamIfNec512C_eval, hOptR, map_bind, liftP_bind]
      refine bind_congr fun ⟨rCoins, bad⟩ => ?_
      set ρ₂ : Env [e2eCoinsBadT ℓ, e2eTrInTy ℓ] := .cons (rCoins, bad) ρ₁
      have hep : (e2eEpMgmtE Δ qep (.fst (Expr.v1 (O := OO))) (.fst (.snd .v1)) (.snd .v0)).eval ρ₂ =
          (gs.epMgmt Δ qep Q bad).map e2eGsEnc :=
        eval_e2eEpMgmtE Δ qep (.fst .v1) (.fst (.snd .v1)) (.snd .v0) ρ₂ gs Q rfl rfl
      rw [hep]
      cases hepEq : gs.epMgmt Δ qep Q bad with
      | none =>
        simp [Option.map]
      | some s1 =>
        simp only [Option.map_some]
        obtain ⟨hst1, htr1, hcp1⟩ := epMgmt_preserve_fields hepEq
        set ρ₃ : Env [e2eGsTy ℓ, e2eCoinsBadT ℓ, e2eTrInTy ℓ] := .cons (e2eGsEnc s1) ρ₂
        have hgParty : PartyReachInv C K (s1.st Q) := hst1 ▸ h.reach.party Q
        simp only [pure_bind, wk1Comp_eval]
        have hCallArg :
            ((Expr.v0 (O := OO)).eval ρ₃,
              ((Expr.v2 (O := OO)).eval ρ₃).2.1,
              ((Expr.v2 (O := OO)).eval ρ₃).2.2.1,
              ((Expr.v1 (O := OO)).eval ρ₃).1) =
            (e2eGsEnc s1, (partyEnc Q, (m, rCoins))) := rfl
        rw [hCallArg, drSendStageCallC_eval P C K decT encT idA idB spkCoins s1 Q m rCoins hgParty]
        simp only [pure_bind, map_pure, liftP_pure, Option.map]
        let tOut : Ty (e2eSig ℓ) := .prod CryptoVerification.E2E.Costed.GhostStT
          (CryptoVerification.E2E.Costed.B 32)
        set out := sm.send (s1.st Q) m rCoins
        set ρ₄ : Env [tOut, e2eSendCallInTy ℓ, e2eGsTy ℓ, e2eCoinsBadT ℓ, e2eTrInTy ℓ] :=
          .cons out (.cons (e2eGsEnc s1, (partyEnc Q, (m, rCoins))) ρ₃)
        have hpos4 :
            (Expr.pair (.fst (.snd (Expr.v4 (O := OO))))
              (.pair (pGet (e2eGsEpoch .v2) (.fst (.snd .v4)))
                (.add (pGet (e2eGsIdx .v2) (.fst (.snd .v4))) (.nat 1)))).eval ρ₄ =
            posEnc ⟨Q, s1.epoch Q, s1.idx Q + 1⟩ := by
          have hep4 : (pGet (e2eGsEpoch (Expr.v2 (O := OO))) (.fst (.snd .v4))).eval ρ₄ =
              s1.epoch Q := pGet_eval (t := .nat) _ _ ρ₄ s1.epoch Q rfl rfl
          have hidx4 : (pGet (e2eGsIdx (Expr.v2 (O := OO))) (.fst (.snd .v4))).eval ρ₄ =
              s1.idx Q := pGet_eval (t := .nat) _ _ ρ₄ s1.idx Q rfl rfl
          simp only [Expr.eval, hep4, hidx4]
          rfl
        have htr1_le : s1.trans.length ≤ q := htr1 ▸ h.lists.trans_le
        have hcp1_le : (dedupComp s1.comp).length ≤ q := hcp1 ▸ h.lists.dedupComp_le
        have hrec4 := eval_e2eRecordE q Δ (.v2 : Expr OO _ (e2eGsTy ℓ)) (.fst (.snd .v4))
          (.fst .v0)
          (.pair (.fst (.snd .v4))
            (.pair (pGet (e2eGsEpoch .v2) (.fst (.snd .v4)))
              (.add (pGet (e2eGsIdx .v2) (.fst (.snd .v4))) (.nat 1))))
          (.fst (.snd (.snd .v4))) (.snd .v0) (.bool false)
          ρ₄ s1 Q ⟨Q, s1.epoch Q, s1.idx Q + 1⟩
          htr1_le hcp1_le rfl rfl hpos4
        simp only [Expr.eval, hrec4]
        rfl
  · simp [hok]

theorem drChSendStageC_eval {ℓ : ℕ} {Pt : Type} (P : SignalPqxdh.Primitives)
    (C : Crypto) (K : MlKem) (decT : PublicKey → Option Pt) (encT : Pt → PublicKey)
    (q Δ qep : ℕ) (idA idB : IdentityKey) (spkCoins : BitVec 256)
    (gs : GameState (GhostState Bytes) (Plain ℓ) Bytes)
    (Q : Party) (m0 m1 : Plain ℓ) (optR : Option (BitVec 512))
    (h : SmReachBounded C K q gs) :
    (drChSendStageC P C K decT encT q Δ qep).eval
        (.cons (e2eGsEnc gs, (partyEnc Q, (m0, (m1, optR)))) .nil) =
      (stepAIface ℓ (emptyTargetE2EIface ℓ)).liftP
        ((Option.map fun (coins, (ct, gsRec)) => (coins, (ct, e2eGsEnc gsRec))) <$>
          chStageProb
            (sessionSchemeFixedSpk
              (paramsIdsWithSpqr C (spqrV1SessionUniformCoins C.F K) idA idB) ℓ spkCoins)
            Δ qep (configRefuseEarlyBobCorr decT encT) gs Q m0 m1 optR) := by
  let OO := e2eOps ℓ P C K decT encT
  set sm := sessionSchemeFixedSpk
    (paramsIdsWithSpqr C (spqrV1SessionUniformCoins C.F K) idA idB) ℓ spkCoins
  set cfg : ConfigR (GhostState Bytes) (Plain ℓ) Bytes := configRefuseEarlyBobCorr decT encT
  set ρ₁ : Env [e2eChInTy ℓ] := .cons (e2eGsEnc gs, (partyEnc Q, (m0, (m1, optR)))) .nil
  unfold drChSendStageC chStageProb
  have hSendOK : (e2eSendOKE (.fst (Expr.v0 (O := OO))) (.fst (.snd .v0))).eval ρ₁ =
      cfg.sendOK gs Q :=
    eval_e2eSendOKE decT encT (.fst .v0) (.fst (.snd .v0)) ρ₁ gs Q rfl rfl
  have hWin : (e2eGsWin (.fst (Expr.v0 (O := OO)))).eval ρ₁ = gs.win := rfl
  simp only [Comp.eval, CryptoGames.SM.orE, Expr.eval, hSendOK, hWin]
  by_cases hok : cfg.sendOK gs Q
  · by_cases hwin : gs.win
    · simp [hok, hwin]
    · have hOptR : (Expr.snd (.snd (.snd (.snd (Expr.v0 (O := OO)))))).eval ρ₁ = optR := rfl
      simp only [hok, hwin, Bool.not_true, Bool.or_self, Bool.false_eq_true, ↓reduceIte,
        e2eSamIfNec512C_eval, hOptR, map_bind, liftP_bind]
      refine bind_congr fun ⟨rCoins, bad⟩ => ?_
      set ρ₂ : Env [e2eCoinsBadT ℓ, e2eChInTy ℓ] := .cons (rCoins, bad) ρ₁
      have hep : (e2eEpMgmtE Δ qep (.fst (Expr.v1 (O := OO))) (.fst (.snd .v1)) (.snd .v0)).eval ρ₂ =
          (gs.epMgmt Δ qep Q bad).map e2eGsEnc :=
        eval_e2eEpMgmtE Δ qep (.fst .v1) (.fst (.snd .v1)) (.snd .v0) ρ₂ gs Q rfl rfl
      rw [hep]
      cases hepEq : gs.epMgmt Δ qep Q bad with
      | none =>
        simp [Option.map]
      | some s1 =>
        simp only [Option.map_some]
        obtain ⟨hst1, htr1, hcp1⟩ := epMgmt_preserve_fields hepEq
        set ρ₃ : Env [e2eGsTy ℓ, e2eCoinsBadT ℓ, e2eChInTy ℓ] := .cons (e2eGsEnc s1) ρ₂
        have hSafe : (e2eSafeChE Δ (Expr.v0 (O := OO)) (.fst (.snd .v2))).eval ρ₃ =
            s1.safeCh Δ Q :=
          eval_e2eSafeChE Δ .v0 (.fst (.snd .v2)) ρ₃ s1 Q rfl rfl
        simp only [hSafe]
        by_cases hsafe : s1.safeCh Δ Q
        · simp only [hsafe, Bool.not_true, Bool.false_eq_true, ↓reduceIte]
          set mCh := if gs.b then m1 else m0
          have hmCh3 :
              (Expr.ite (e2eGsB (.fst (Expr.v2 (O := OO))))
                (.fst (.snd (.snd (.snd .v2))))
                (.fst (.snd (.snd .v2)))).eval ρ₃ = mCh := by
            simp [ρ₃, ρ₂, ρ₁, mCh, e2eGsB, e2eGsEnc, Expr.eval, Expr.v2]
          have hgParty : PartyReachInv C K (s1.st Q) := hst1 ▸ h.reach.party Q
          simp only [pure_bind, wk1Comp_eval]
          have hCallArg :
              ((Expr.v0 (O := OO)).eval ρ₃,
                ((Expr.v2 (O := OO)).eval ρ₃).2.1,
                (if (e2eGsB (.fst (Expr.v2 (O := OO)))).eval ρ₃ = true
                 then ((Expr.v2 (O := OO)).eval ρ₃).2.2.2.1
                 else ((Expr.v2 (O := OO)).eval ρ₃).2.2.1),
                ((Expr.v1 (O := OO)).eval ρ₃).1) =
              (e2eGsEnc s1, (partyEnc Q, (mCh, rCoins))) := by
            simp [ρ₃, ρ₂, ρ₁, mCh, e2eGsB, e2eGsEnc, Expr.eval, Expr.v0, Expr.v1, Expr.v2]
          rw [hCallArg, drSendStageCallC_eval P C K decT encT idA idB spkCoins s1 Q mCh rCoins hgParty]
          simp only [pure_bind, map_pure, liftP_pure, Option.map]
          let tOut : Ty (e2eSig ℓ) := .prod CryptoVerification.E2E.Costed.GhostStT
            (CryptoVerification.E2E.Costed.B 32)
          set out := sm.send (s1.st Q) mCh rCoins
          set ρ₄ : Env [tOut, e2eSendCallInTy ℓ, e2eGsTy ℓ, e2eCoinsBadT ℓ, e2eChInTy ℓ] :=
            .cons out (.cons (e2eGsEnc s1, (partyEnc Q, (mCh, rCoins))) ρ₃)
          have hmCh4 :
              (Expr.ite (e2eGsB (.fst (Expr.v4 (O := OO))))
                (.fst (.snd (.snd (.snd .v4))))
                (.fst (.snd (.snd .v4)))).eval ρ₄ = mCh := by
            simp [ρ₄, ρ₃, ρ₂, ρ₁, mCh, e2eGsB, e2eGsEnc, Expr.eval, Expr.v4]
          have hpos4 :
              (Expr.pair (.fst (.snd (Expr.v4 (O := OO))))
                (.pair (pGet (e2eGsEpoch .v2) (.fst (.snd .v4)))
                  (.add (pGet (e2eGsIdx .v2) (.fst (.snd .v4))) (.nat 1)))).eval ρ₄ =
              posEnc ⟨Q, s1.epoch Q, s1.idx Q + 1⟩ := by
            have hep4 : (pGet (e2eGsEpoch (Expr.v2 (O := OO))) (.fst (.snd .v4))).eval ρ₄ =
                s1.epoch Q := pGet_eval (t := .nat) _ _ ρ₄ s1.epoch Q rfl rfl
            have hidx4 : (pGet (e2eGsIdx (Expr.v2 (O := OO))) (.fst (.snd .v4))).eval ρ₄ =
                s1.idx Q := pGet_eval (t := .nat) _ _ ρ₄ s1.idx Q rfl rfl
            simp only [Expr.eval, hep4, hidx4]
            rfl
          have htr1_le : s1.trans.length ≤ q := htr1 ▸ h.lists.trans_le
          have hcp1_le : (dedupComp s1.comp).length ≤ q := hcp1 ▸ h.lists.dedupComp_le
          have hrec4 := eval_e2eRecordE q Δ (.v2 : Expr OO _ (e2eGsTy ℓ)) (.fst (.snd .v4))
            (.fst .v0)
            (.pair (.fst (.snd .v4))
              (.pair (pGet (e2eGsEpoch .v2) (.fst (.snd .v4)))
                (.add (pGet (e2eGsIdx .v2) (.fst (.snd .v4))) (.nat 1))))
            (.ite (e2eGsB (.fst .v4))
              (.fst (.snd (.snd (.snd .v4))))
              (.fst (.snd (.snd .v4))))
            (.snd .v0) (.bool true)
            ρ₄ s1 Q ⟨Q, s1.epoch Q, s1.idx Q + 1⟩
            htr1_le hcp1_le rfl rfl hpos4
          simp only [Expr.eval, hrec4]
          rfl
        · simp [hsafe]
  · simp [hok]

theorem smReachBounded_of_trStageProb {ℓ : ℕ} {Pt : Type}
    (C : Crypto) (K : MlKem) (idA idB : IdentityKey) (spkCoins : BitVec 256)
    (decT : PublicKey → Option Pt) (encT : Pt → PublicKey)
    (q Δ qep : ℕ) (gs : GameState (GhostState Bytes) (Plain ℓ) Bytes)
    (Q : Party) (m : Plain ℓ) (optR : Option (BitVec 512))
    (hReach : SmReachBounded C K q gs)
    {coins : BitVec 512} {ct : Bytes} {gsRec : GameState (GhostState Bytes) (Plain ℓ) Bytes}
    (hmem : some (coins, (ct, gsRec)) ∈ support (trStageProb
      (sessionSchemeFixedSpk
        (paramsIdsWithSpqr C (spqrV1SessionUniformCoins C.F K) idA idB) ℓ spkCoins)
      Δ qep (configRefuseEarlyBobCorr decT encT) gs Q m optR)) :
    SmReachBounded C K (q + 1) gsRec := by
  set sm := sessionSchemeFixedSpk
    (paramsIdsWithSpqr C (spqrV1SessionUniformCoins C.F K) idA idB) ℓ spkCoins
  set cfg : ConfigR (GhostState Bytes) (Plain ℓ) Bytes := configRefuseEarlyBobCorr decT encT
  suffices hsup :
      (some ct, gsRec) ∈
        support ((oracleImplR sm Δ qep cfg (.inl (.inl (.inl (.inl (Q, m, optR)))))).run gs) by
    exact smReachBounded_oracleImplR C K idA idB ℓ Δ qep q spkCoins cfg
      (.inl (.inl (.inl (.inl (Q, m, optR))))) hReach hsup
  unfold trStageProb at hmem
  by_cases hguard : !(cfg.sendOK gs Q) || gs.win
  · simp [hguard] at hmem
  · simp only [hguard, Bool.false_eq_true, ↓reduceIte, support_bind, Set.mem_iUnion,
      exists_prop] at hmem
    rcases hmem with ⟨⟨rC, bad⟩, hSam, hEp⟩
    cases hepEq : gs.epMgmt Δ qep Q bad with
    | none => simp [hepEq] at hEp
    | some s₁ =>
      simp only [hepEq, support_pure, Set.mem_singleton_iff, Option.some.injEq, Prod.mk.injEq] at hEp
      rcases hEp with ⟨rfl, rfl, rfl⟩
      have hok : cfg.sendOK gs Q = true := by
        cases h1 : cfg.sendOK gs Q <;> simp_all
      have hwin : gs.win = false := by
        cases h2 : gs.win <;> simp_all
      change (some (sm.send (s₁.st Q) m coins).2, _) ∈
        support ((transmitR sm Δ qep cfg (Q, m, optR)).run gs)
      unfold transmitR transmitImpl
      simp only [StateT.run_bind, StateT.run_get, StateT.run_monadLift, monadLift_self,
        pure_bind, hok, hwin, Bool.not_true, Bool.false_eq_true, ↓reduceIte,
        support_bind, Set.mem_iUnion, exists_prop]
      exact ⟨((coins, bad), gs),
        by simp; exact hSam,
        by simp [hepEq]; exact ⟨rfl, rfl⟩⟩

theorem smReachBounded_of_chStageProb {ℓ : ℕ} {Pt : Type}
    (C : Crypto) (K : MlKem) (idA idB : IdentityKey) (spkCoins : BitVec 256)
    (decT : PublicKey → Option Pt) (encT : Pt → PublicKey)
    (q Δ qep : ℕ) (gs : GameState (GhostState Bytes) (Plain ℓ) Bytes)
    (Q : Party) (m0 m1 : Plain ℓ) (optR : Option (BitVec 512))
    (hReach : SmReachBounded C K q gs)
    {coins : BitVec 512} {ct : Bytes} {gsRec : GameState (GhostState Bytes) (Plain ℓ) Bytes}
    (hmem : some (coins, (ct, gsRec)) ∈ support (chStageProb
      (sessionSchemeFixedSpk
        (paramsIdsWithSpqr C (spqrV1SessionUniformCoins C.F K) idA idB) ℓ spkCoins)
      Δ qep (configRefuseEarlyBobCorr decT encT) gs Q m0 m1 optR)) :
    SmReachBounded C K (q + 1) gsRec := by
  set sm := sessionSchemeFixedSpk
    (paramsIdsWithSpqr C (spqrV1SessionUniformCoins C.F K) idA idB) ℓ spkCoins
  set cfg : ConfigR (GhostState Bytes) (Plain ℓ) Bytes := configRefuseEarlyBobCorr decT encT
  have hchallAllowed : ∀ t, cfg.base.challAllowedIn t = true := fun _ => rfl
  have hchallMsg : ∀ t, cfg.base.challMsg t = none := fun _ => rfl
  suffices hsup :
      (some ct, gsRec) ∈
        support ((oracleImplR sm Δ qep cfg (.inl (.inl (.inl (.inr (Q, m0, m1, optR)))))).run gs) by
    exact smReachBounded_oracleImplR C K idA idB ℓ Δ qep q spkCoins cfg
      (.inl (.inl (.inl (.inr (Q, m0, m1, optR))))) hReach hsup
  unfold chStageProb at hmem
  by_cases hguard : !(cfg.sendOK gs Q) || gs.win
  · simp [hguard] at hmem
  · simp only [hguard, Bool.false_eq_true, ↓reduceIte, support_bind, Set.mem_iUnion,
      exists_prop] at hmem
    rcases hmem with ⟨⟨rC, bad⟩, hSam, hEp⟩
    cases hepEq : gs.epMgmt Δ qep Q bad with
    | none => simp [hepEq] at hEp
    | some s₁ =>
      simp only [hepEq] at hEp
      by_cases hsafe : s₁.safeCh Δ Q
      · simp only [hsafe, Bool.not_true, Bool.false_eq_true, ↓reduceIte, support_pure,
          Set.mem_singleton_iff, Option.some.injEq, Prod.mk.injEq] at hEp
        rcases hEp with ⟨rfl, rfl, rfl⟩
        have hok : cfg.sendOK gs Q = true := by
          cases h1 : cfg.sendOK gs Q <;> simp_all
        have hwin : gs.win = false := by
          cases h2 : gs.win <;> simp_all
        change (some _, _) ∈ support ((challR sm Δ qep cfg (Q, m0, m1, optR)).run gs)
        unfold challR challImpl
        simp only [StateT.run_bind, StateT.run_get, StateT.run_monadLift, monadLift_self,
          pure_bind, hok, hwin, Bool.not_true, Bool.false_eq_true, ↓reduceIte,
          support_bind, Set.mem_iUnion, exists_prop]
        exact ⟨((coins, bad), gs),
          by simp; exact hSam,
          by simp [hepEq, hsafe, hchallAllowed, hchallMsg]; exact ⟨rfl, rfl⟩⟩
      · simp [hsafe] at hEp

end Computational.Proofs.E2E.Dsl.HaltedDrSessionSimStepsAux
