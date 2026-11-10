/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Computational.Proofs.ReductionDsl.Fig8Atomic
public import Computational.Proofs.ReductionDsl.PureAuxMacroLift
public import Computational.Proofs.ReductionDsl.MacroLift
public import Computational.Proofs.ReductionDsl.SM.Theorem1
public import Computational.Proofs.ReductionDsl.SM.RedCKA
public import Computational.Proofs.ReductionDsl.SM.RedPRNG
public import Computational.Proofs.ReductionDsl.SM.RedFS
public import Computational.Proofs.ReductionDsl.SM.DeliverForge
public import Computational.Proofs.SessionCostedFig8.QuerySubsumes
public import Computational.Proofs.SpecLemmas.Session.ACD19.Ratchet.LibsignalBound
public import Computational.Specifications.Session.StatementComposed

/-!
# Atomic `PureAuxBundle` and Adapter Infrastructure for Figure 8 Reductions

Constructs `PureAuxAdapters`, `PureAuxBundle`, and `fig8RedsInst` lowering shallow Figure 8 (`SM`)
and `DeliverForge` `CostedReduction` programs to `ReductionDsl.atomicFig8Ops`.
-/

@[expose] public section

set_option autoImplicit false
set_option linter.dupNamespace false

open OracleSpec OracleComp
open _root_.ReductionDsl (Sig Ty Ops Iface Env Expr Comp CostedReduction bits
  UniformSamplerTag AtomicUnifBase SMTag SMTagDF CKATag PRNGTag FSAEADTag
  atomicSig atomicFig8Ops BV256 IdKey PlainT PtT
  ckaStT ckaStV ckaStOfV fsSendStT fsSendStV fsSendStOfV fsRecvStT fsRecvStV fsRecvStOfV
  lpubT lpubV lpubOfV lctT lctV lctOfV fig8StT fig8StV fig8StOfV fig8CtT fig8CtV fig8CtOfV
  smRrT smRrEnc smRrDec fsRrEnc
  fig8SmIface fig8SmIfaceDF fig8SmCodec fig8SmCodecDF
  ckaTargetIface prngTargetIface fsaeadHeaderIface)
open Computational.Proofs.ReductionDsl.MacroLift (mapTy toVal callMacroAux callMacroAux_size
  guardRed)
open Computational.Proofs.ReductionDsl.PureAuxMacroLift (CoinSimEquiv PureAuxAdapters
  PureAuxBundle coinSimEquiv_liftP callPureMacroAux compilePureAuxExpr compilePureAuxComp
  callAdaptR compilePureAuxRed bits_mono)
open Computational.Proofs.ReductionDsl.Fig8Atomic (dhSchemeFb fsAtomicB
  idKeyLitExpr idKeyLitExpr_cost idKeyLitExpr_size
  partyToBool_eq_partyEnc boolToParty_eq_partyDec
  ckaStOfV_ckaStV fsSendStOfV_fsSendStV fsRecvStOfV_fsRecvStV
  lpubOfV_lpubV lctOfV_lctV fig8StOfV_fig8StV fig8CtOfV_fig8CtV
  eqPtExpr eqPtExpr_eval eqPtExpr_size eqMExpr eqMExpr_eval eqMExpr_size
  eqEExpr eqEExpr_eval eqEExpr_size
  defaultEExpr defaultEExpr_eval defaultEExpr_size lamIExpr lamIExpr_eval lamIExpr_size
  smEqCtExpr smEqCtExpr_eval smEqCtExpr_size smBlankExpr smBlankExpr_eval smBlankExpr_size
  ckaInitAExpr ckaInitAExpr_eval ckaInitAExpr_size
  ckaInitBExpr ckaInitBExpr_eval ckaInitBExpr_size
  ckaSendExpr ckaSendExpr_eval ckaSendExpr_size ckaRecvExpr ckaRecvExpr_eval ckaRecvExpr_size
  prngInitExpr prngInitExpr_eval prngInitExpr_size prngUpExpr prngUpExpr_eval prngUpExpr_size
  fsInitSendExpr fsInitSendExpr_size fsInitRecvExpr fsInitRecvExpr_eval fsInitRecvExpr_size
  fsSendExpr fsSendExpr_eval fsSendExpr_size fsRecvExpr fsRecvExpr_eval fsRecvExpr_size)
open Computational.Proofs.SessionCostedFig8.QuerySubsumes (QuerySubsumes)
open CryptoGames (Party)
open CryptoGames.CBC (Plain)
open CryptoGames.CKA (DHFun CKASort ckaSig CKAOp ckaOps ckaSchemeOps CKASamp ckaSamplers ckaIface
  ckaSMCodec ckaSMCodecDF ckaPsTy ckaPsDec)
open CryptoGames.PRFPRNG (prngSig prngIface fsaeadHeaderAdIface FSHdrTag fsHdrRrEnc)
open CryptoGames.FSAEAD (RatchetSenderState RatchetReceiverState)
open CryptoGames.Ratchet (rootPRNG)
open CryptoGames.Ratchet.LibsignalInst (LibsignalMsgPublicPart LibsignalCiphertextWithSalt32 lPubOf)
open CryptoGames.Ratchet.LibsignalSim (Fig8St Fig8C)
open CryptoGames.LibsignalSession (Crypto IdentityKey PublicKey SignalMessageProtoCodec
  maxForwardJumps)
open CryptoGames.LibsignalSM (lBlank)
open CryptoGames.SM (SMSort smSig SMOp smOps SMSamp smIface smIfaceDF smCodec smCodecDF
  partyEnc partyDec)
open CryptoVerification.LibsignalSession (Fig8CostedReds)

namespace Computational.Proofs.SessionCostedFig8.Bundles

section SortAndAdapters

variable (ℓ : ℕ) (Pt : Type) [DecidableEq Pt] [Zero Pt]
  (C : Crypto) (Dh : DHFun (BitVec 256) Pt) (encPt : Pt → List (BitVec 8))
  (encT : Pt → PublicKey) (idOf : Party → IdentityKey) (lam : Pt)

local notation "S₂" => atomicSig ℓ Pt
local notation "O₂" => atomicFig8Ops ℓ Pt C Dh encPt encT lam

@[reducible] def fig8MsgT : Ty S₂ := .prod lpubT PlainT

@[reducible] def fSortSM : SMSort → Ty S₂
  | .key => .unit
  | .st => fig8StT
  | .st2 => .unit
  | .msg => fig8MsgT ℓ Pt
  | .coins => BV256
  | .rcoins => .unit
  | .ct => fig8CtT

def toDenSM :
    (b : SMSort) →
      (smSig Unit (Fig8St Pt) Unit (LibsignalMsgPublicPart × Plain ℓ)
        (BitVec 256) Unit (Fig8C Pt)).den b →
      (fSortSM ℓ Pt b).denote
  | .key, () => ()
  | .st, s => fig8StV s
  | .st2, () => ()
  | .msg, (pub, m) => (lpubV pub, m)
  | .coins, r => r
  | .rcoins, () => ()
  | .ct, c => fig8CtV c

@[reducible] def fSortCKA : CKASort → Ty S₂
  | .kc | .ccoins | .kr | .sig | .k => BV256
  | .γ => ckaStT
  | .t | .i => PtT
  | .ss => fsSendStT
  | .rs => fsRecvStT
  | .msg => fig8MsgT ℓ Pt
  | .ct => lctT

def toDenCKA :
    (b : CKASort) →
      (ckaSig (BitVec 256) (CryptoGames.CKA.DDH.State (BitVec 256) Pt) (BitVec 256) Pt Pt
        (BitVec 256) (BitVec 256) (BitVec 256)
        (RatchetSenderState (BitVec 256)) (RatchetReceiverState (BitVec 256) (BitVec 256))
        (LibsignalMsgPublicPart × Plain ℓ) (ℕ × LibsignalCiphertextWithSalt32)).den b →
      (fSortCKA ℓ Pt b).denote
  | .kc, x | .ccoins, x | .kr, x | .sig, x | .k, x => x
  | .γ, γ => ckaStV γ
  | .t, x | .i, x => x
  | .ss, ss => fsSendStV ss
  | .rs, rs => fsRecvStV rs
  | .msg, (pub, m) => (lpubV pub, m)
  | .ct, c => lctV c

@[reducible] def fig8SrcQT : Ty S₂ :=
  .sum
    (.sum
      (.sum
        (.sum
          (.prod .bool (.prod (fig8MsgT ℓ Pt) (.opt BV256)))
          (.prod .bool (.prod (fig8MsgT ℓ Pt) (.prod (fig8MsgT ℓ Pt) (.opt BV256)))))
        (.prod .bool fig8CtT))
      (.prod .bool fig8CtT))
    .bool

@[reducible] def fig8SrcRT : Ty S₂ :=
  .sum
    (.sum
      (.sum
        (.sum (.opt fig8CtT) (.opt fig8CtT))
        (.opt (smRrT (fig8MsgT ℓ Pt))))
      (.opt (smRrT (fig8MsgT ℓ Pt))))
    (.opt fig8StT)

@[reducible] def fig8SrcQDFT : Ty S₂ :=
  .sum (fig8SrcQT ℓ Pt) (.prod .bool (.prod fig8CtT fig8CtT))

@[reducible] def fig8SrcRDFT : Ty S₂ :=
  .sum (fig8SrcRT ℓ Pt) (.opt (smRrT (fig8MsgT ℓ Pt)))

def fig8SplitIn : Expr O₂ [.unit] (.prod .unit (.prod IdKey IdKey)) :=
  .pair .unit
    (.pair (idKeyLitExpr ℓ Pt C Dh encPt encT lam (idOf .A))
           (idKeyLitExpr ℓ Pt C Dh encPt encT lam (idOf .B)))

theorem fig8SplitIn_eval :
    (fig8SplitIn ℓ Pt C Dh encPt encT idOf lam).eval (.cons () .nil) = ((), (idOf .A, idOf .B)) := by
  simp [fig8SplitIn, Expr.eval]

theorem fig8SplitIn_cost : (fig8SplitIn ℓ Pt C Dh encPt encT idOf lam).cost ≤ 200 := by
  have hA := idKeyLitExpr_cost ℓ Pt C Dh encPt encT lam (Γ := [.unit]) (idOf .A)
  have hB := idKeyLitExpr_cost ℓ Pt C Dh encPt encT lam (Γ := [.unit]) (idOf .B)
  simp only [fig8SplitIn, Expr.cost]
  omega

theorem fig8SplitIn_size : (fig8SplitIn ℓ Pt C Dh encPt encT idOf lam).size ≤ 75 := by
  simp only [fig8SplitIn, idKeyLitExpr_size, Expr.size]
  omega

def fig8AdaptQ : Expr O₂ [(fig8SmCodec ℓ Pt).Q] (fig8SrcQT ℓ Pt) :=
  .caseSum (.var .zero)
    (.inl (.inl (.inl (.inl (.var .zero)))))
    (.caseSum (.var .zero)
      (.inl (.inl (.inl (.inr (.var .zero)))))
      (.caseSum (.var .zero)
        (.inl (.inl (.inr (.var .zero))))
        (.caseSum (.var .zero)
          (.inl (.inr (.var .zero)))
          (.inr (.var .zero)))))

theorem fig8AdaptQ_cost : (fig8AdaptQ ℓ Pt C Dh encPt encT lam).cost ≤ 35 := by
  simp only [fig8AdaptQ, Expr.cost]; omega

theorem fig8AdaptQ_size : (fig8AdaptQ ℓ Pt C Dh encPt encT lam).size ≤ 45 := by
  simp only [fig8AdaptQ, Expr.size]; omega

def fig8AdaptR : Expr O₂ [fig8SrcRT ℓ Pt, (fig8SmCodec ℓ Pt).Q] (fig8SmCodec ℓ Pt).R :=
  let r0 {Γ} : Expr O₂ (fig8SrcRT ℓ Pt :: Γ) (fig8SrcRT ℓ Pt) := .var .zero
  let onTr {Γ} : Expr O₂ (fig8SrcRT ℓ Pt :: Γ) (fig8SmCodec ℓ Pt).R :=
    .caseSum r0
      (.caseSum (.var .zero)
        (.caseSum (.var .zero)
          (.caseSum (.var .zero) (.inl (.var .zero)) (.inl .none))
          (.inl .none))
        (.inl .none))
      (.inl .none)
  let onCh {Γ} : Expr O₂ (fig8SrcRT ℓ Pt :: Γ) (fig8SmCodec ℓ Pt).R :=
    .caseSum r0
      (.caseSum (.var .zero)
        (.caseSum (.var .zero)
          (.caseSum (.var .zero) (.inl .none) (.inl (.var .zero)))
          (.inl .none))
        (.inl .none))
      (.inl .none)
  let onDl {Γ} : Expr O₂ (fig8SrcRT ℓ Pt :: Γ) (fig8SmCodec ℓ Pt).R :=
    .caseSum r0
      (.caseSum (.var .zero)
        (.caseSum (.var .zero) (.inr (.inl .none)) (.inr (.inl (.var .zero))))
        (.inr (.inl .none)))
      (.inr (.inl .none))
  let onIj {Γ} : Expr O₂ (fig8SrcRT ℓ Pt :: Γ) (fig8SmCodec ℓ Pt).R :=
    .caseSum r0
      (.caseSum (.var .zero) (.inr (.inl .none)) (.inr (.inl (.var .zero))))
      (.inr (.inl .none))
  let onCr {Γ} : Expr O₂ (fig8SrcRT ℓ Pt :: Γ) (fig8SmCodec ℓ Pt).R :=
    .caseSum r0 (.inr (.inr .none)) (.inr (.inr (.var .zero)))
  .caseSum (.var (.succ .zero))
    (.letE (.var (.succ .zero)) onTr)
    (.caseSum (.var .zero)
      (.letE (.var (.succ (.succ .zero))) onCh)
      (.caseSum (.var .zero)
        (.letE (.var (.succ (.succ (.succ .zero)))) onDl)
        (.caseSum (.var .zero)
          (.letE (.var (.succ (.succ (.succ (.succ .zero))))) onIj)
          (.letE (.var (.succ (.succ (.succ (.succ .zero))))) onCr))))

theorem fig8AdaptR_cost : (fig8AdaptR ℓ Pt C Dh encPt encT lam).cost ≤ 120 := by
  simp only [fig8AdaptR, Expr.cost]; omega

theorem fig8AdaptR_size : (fig8AdaptR ℓ Pt C Dh encPt encT lam).size ≤ 150 := by
  simp only [fig8AdaptR, Expr.size]; omega

def fig8AdaptQDF : Expr O₂ [(fig8SmCodecDF ℓ Pt).Q] (fig8SrcQDFT ℓ Pt) :=
  .caseSum (.var .zero)
    (.inl (.inl (.inl (.inl (.inl (.var .zero))))))
    (.caseSum (.var .zero)
      (.inl (.inl (.inl (.inl (.inr (.var .zero))))))
      (.caseSum (.var .zero)
        (.inl (.inl (.inl (.inr (.var .zero)))))
        (.caseSum (.var .zero)
          (.inl (.inl (.inr (.var .zero))))
          (.caseSum (.var .zero)
            (.inl (.inr (.var .zero)))
            (.inr (.var .zero))))))

theorem fig8AdaptQDF_cost : (fig8AdaptQDF ℓ Pt C Dh encPt encT lam).cost ≤ 45 := by
  simp only [fig8AdaptQDF, Expr.cost]; omega

theorem fig8AdaptQDF_size : (fig8AdaptQDF ℓ Pt C Dh encPt encT lam).size ≤ 60 := by
  simp only [fig8AdaptQDF, Expr.size]; omega

def fig8AdaptRDF : Expr O₂ [fig8SrcRDFT ℓ Pt, (fig8SmCodecDF ℓ Pt).Q] (fig8SmCodecDF ℓ Pt).R :=
  let rTop {Γ} : Expr O₂ (fig8SrcRDFT ℓ Pt :: Γ) (fig8SrcRDFT ℓ Pt) := .var .zero
  let onTr {Γ} : Expr O₂ (fig8SrcRDFT ℓ Pt :: Γ) (fig8SmCodecDF ℓ Pt).R :=
    .caseSum rTop
      (.caseSum (.var .zero)
        (.caseSum (.var .zero)
          (.caseSum (.var .zero)
            (.caseSum (.var .zero) (.inl (.var .zero)) (.inl .none))
            (.inl .none))
          (.inl .none))
        (.inl .none))
      (.inl .none)
  let onCh {Γ} : Expr O₂ (fig8SrcRDFT ℓ Pt :: Γ) (fig8SmCodecDF ℓ Pt).R :=
    .caseSum rTop
      (.caseSum (.var .zero)
        (.caseSum (.var .zero)
          (.caseSum (.var .zero)
            (.caseSum (.var .zero) (.inl .none) (.inl (.var .zero)))
            (.inl .none))
          (.inl .none))
        (.inl .none))
      (.inl .none)
  let onDl {Γ} : Expr O₂ (fig8SrcRDFT ℓ Pt :: Γ) (fig8SmCodecDF ℓ Pt).R :=
    .caseSum rTop
      (.caseSum (.var .zero)
        (.caseSum (.var .zero)
          (.caseSum (.var .zero) (.inr (.inl .none)) (.inr (.inl (.var .zero))))
          (.inr (.inl .none)))
        (.inr (.inl .none)))
      (.inr (.inl .none))
  let onIj {Γ} : Expr O₂ (fig8SrcRDFT ℓ Pt :: Γ) (fig8SmCodecDF ℓ Pt).R :=
    .caseSum rTop
      (.caseSum (.var .zero)
        (.caseSum (.var .zero) (.inr (.inl .none)) (.inr (.inl (.var .zero))))
        (.inr (.inl .none)))
      (.inr (.inl .none))
  let onCr {Γ} : Expr O₂ (fig8SrcRDFT ℓ Pt :: Γ) (fig8SmCodecDF ℓ Pt).R :=
    .caseSum rTop (.caseSum (.var .zero) (.inr (.inr .none)) (.inr (.inr (.var .zero))))
      (.inr (.inr .none))
  let onDf {Γ} : Expr O₂ (fig8SrcRDFT ℓ Pt :: Γ) (fig8SmCodecDF ℓ Pt).R :=
    .caseSum rTop (.inr (.inl .none)) (.inr (.inl (.var .zero)))
  .caseSum (.var (.succ .zero))
    (.letE (.var (.succ .zero)) onTr)
    (.caseSum (.var .zero)
      (.letE (.var (.succ (.succ .zero))) onCh)
      (.caseSum (.var .zero)
        (.letE (.var (.succ (.succ (.succ .zero)))) onDl)
        (.caseSum (.var .zero)
          (.letE (.var (.succ (.succ (.succ (.succ .zero))))) onIj)
          (.caseSum (.var .zero)
            (.letE (.var (.succ (.succ (.succ (.succ (.succ .zero)))))) onCr)
            (.letE (.var (.succ (.succ (.succ (.succ (.succ .zero)))))) onDf)))))

theorem fig8AdaptRDF_cost : (fig8AdaptRDF ℓ Pt C Dh encPt encT lam).cost ≤ 155 := by
  simp only [fig8AdaptRDF, Expr.cost]; omega

theorem fig8AdaptRDF_size : (fig8AdaptRDF ℓ Pt C Dh encPt encT lam).size ≤ 200 := by
  simp only [fig8AdaptRDF, Expr.size]; omega

omit [DecidableEq Pt] [Zero Pt] in
private theorem fig8StOfV_toVal_ckaPsTy
    (ps : (ckaPsTy (BitVec 256) (CryptoGames.CKA.DDH.State (BitVec 256) Pt) (BitVec 256) Pt Pt
      (BitVec 256) (BitVec 256) (BitVec 256)
      (RatchetSenderState (BitVec 256)) (RatchetReceiverState (BitVec 256) (BitVec 256))
      (LibsignalMsgPublicPart × Plain ℓ) (ℕ × LibsignalCiphertextWithSalt32)).denote) :
    fig8StOfV (toVal (fSortCKA ℓ Pt) (toDenCKA ℓ Pt)
      (ckaPsTy (BitVec 256) (CryptoGames.CKA.DDH.State (BitVec 256) Pt) (BitVec 256) Pt Pt
        (BitVec 256) (BitVec 256) (BitVec 256)
        (RatchetSenderState (BitVec 256)) (RatchetReceiverState (BitVec 256) (BitVec 256))
        (LibsignalMsgPublicPart × Plain ℓ) (ℕ × LibsignalCiphertextWithSalt32)) ps) =
      ckaPsDec ps := by
  rcases ps with ⟨p, rk, vs?, vrTbl, γ, cur?, tc⟩
  dsimp only [toVal, fSortCKA, toDenCKA, fig8StOfV, ckaPsDec]
  rw [boolToParty_eq_partyDec, ckaStOfV_ckaStV]
  have hvs : Option.map (fsSendStOfV (ℓ := ℓ) (Pt := Pt))
      (Option.map (fun x => fsSendStV (ℓ := ℓ) (Pt := Pt) x) vs?) = vs? := by
    cases vs? <;> simp [fsSendStOfV_fsSendStV]
  have hvr : (fun t => Option.map (fsRecvStOfV (ℓ := ℓ) (Pt := Pt))
      (Option.map (fun x => fsRecvStV (ℓ := ℓ) (Pt := Pt) x) (vrTbl t))) = vrTbl := by
    funext t; cases vrTbl t <;> simp [fsRecvStOfV_fsRecvStV]
  have hcur : Option.map (fun x => x) cur? = cur? := by
    cases cur? <;> rfl
  rw [hvs, hvr, hcur]

@[reducible] def smToFig8Adapters :
    PureAuxAdapters (fSortSM ℓ Pt) O₂
      (smCodec Unit (Fig8St Pt) Unit (LibsignalMsgPublicPart × Plain ℓ) (BitVec 256) Unit (Fig8C Pt))
      (fig8SmCodec ℓ Pt) (.prod IdKey IdKey)
      .unit .unit .bool .bool .unit .unit .bool .bool where
  splitIn := fig8SplitIn ℓ Pt C Dh encPt encT idOf lam
  adaptAIn := .unit
  adaptQ := fig8AdaptQ ℓ Pt C Dh encPt encT lam
  adaptR := fig8AdaptR ℓ Pt C Dh encPt encT lam
  adaptAOut := .var .zero
  adaptOut := .var .zero

@[reducible] def smDFToFig8Adapters :
    PureAuxAdapters (fSortSM ℓ Pt) O₂
      (smCodecDF Unit (Fig8St Pt) Unit (LibsignalMsgPublicPart × Plain ℓ) (BitVec 256) Unit (Fig8C Pt))
      (fig8SmCodecDF ℓ Pt) (.prod IdKey IdKey)
      .unit .unit .bool .bool .unit .unit .bool .bool where
  splitIn := fig8SplitIn ℓ Pt C Dh encPt encT idOf lam
  adaptAIn := .unit
  adaptQ := fig8AdaptQDF ℓ Pt C Dh encPt encT lam
  adaptR := fig8AdaptRDF ℓ Pt C Dh encPt encT lam
  adaptAOut := .var .zero
  adaptOut := .var .zero

@[reducible] def ckaToFig8Adapters :
    PureAuxAdapters (fSortCKA ℓ Pt) O₂
      (ckaSMCodec (BitVec 256) (CryptoGames.CKA.DDH.State (BitVec 256) Pt) (BitVec 256) Pt Pt
        (BitVec 256) (BitVec 256) (BitVec 256)
        (RatchetSenderState (BitVec 256)) (RatchetReceiverState (BitVec 256) (BitVec 256))
        (LibsignalMsgPublicPart × Plain ℓ) (ℕ × LibsignalCiphertextWithSalt32))
      (fig8SmCodec ℓ Pt) (.prod IdKey IdKey)
      .unit .unit .bool .bool .unit .unit .bool .bool where
  splitIn := fig8SplitIn ℓ Pt C Dh encPt encT idOf lam
  adaptAIn := .unit
  adaptQ := fig8AdaptQ ℓ Pt C Dh encPt encT lam
  adaptR := fig8AdaptR ℓ Pt C Dh encPt encT lam
  adaptAOut := .var .zero
  adaptOut := .var .zero

@[reducible] def ckaDFToFig8Adapters :
    PureAuxAdapters (fSortCKA ℓ Pt) O₂
      (ckaSMCodecDF (BitVec 256) (CryptoGames.CKA.DDH.State (BitVec 256) Pt) (BitVec 256) Pt Pt
        (BitVec 256) (BitVec 256) (BitVec 256)
        (RatchetSenderState (BitVec 256)) (RatchetReceiverState (BitVec 256) (BitVec 256))
        (LibsignalMsgPublicPart × Plain ℓ) (ℕ × LibsignalCiphertextWithSalt32))
      (fig8SmCodecDF ℓ Pt) (.prod IdKey IdKey)
      .unit .unit .bool .bool .unit .unit .bool .bool where
  splitIn := fig8SplitIn ℓ Pt C Dh encPt encT idOf lam
  adaptAIn := .unit
  adaptQ := fig8AdaptQDF ℓ Pt C Dh encPt encT lam
  adaptR := fig8AdaptRDF ℓ Pt C Dh encPt encT lam
  adaptAOut := .var .zero
  adaptOut := .var .zero

private def decodeSrcR
    (t : (CryptoGames.SM.spec (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ)
      (BitVec 256) (Fig8C Pt)).Domain)
    (r₂ : (fig8SrcRT ℓ Pt).denote) :
    (CryptoGames.SM.spec (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ)
      (BitVec 256) (Fig8C Pt)).Range t :=
  match t with
  | .inl (.inl (.inl (.inl _))) =>
    match r₂ with
    | .inl (.inl (.inl (.inl r))) => r.map (fig8CtOfV (ℓ := ℓ) (Pt := Pt))
    | _ => none
  | .inl (.inl (.inl (.inr _))) =>
    match r₂ with
    | .inl (.inl (.inl (.inr r))) => r.map (fig8CtOfV (ℓ := ℓ) (Pt := Pt))
    | _ => none
  | .inl (.inl (.inr _)) =>
    match r₂ with
    | .inl (.inl (.inr r)) =>
      r.map (ReductionDsl.smRrDec (ℓ := ℓ) (Pt := Pt) (msgT := fig8MsgT ℓ Pt)
        fun x => (lpubOfV (ℓ := ℓ) (Pt := Pt) x.1, x.2))
    | _ => none
  | .inl (.inr _) =>
    match r₂ with
    | .inl (.inr r) =>
      r.map (ReductionDsl.smRrDec (ℓ := ℓ) (Pt := Pt) (msgT := fig8MsgT ℓ Pt)
        fun x => (lpubOfV (ℓ := ℓ) (Pt := Pt) x.1, x.2))
    | _ => none
  | .inr _ =>
    match r₂ with
    | .inr r => r.map (fig8StOfV (ℓ := ℓ) (Pt := Pt))
    | _ => none

private theorem fig8SmCodec_rdec_adaptR
    (t : (CryptoGames.SM.spec (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ)
      (BitVec 256) (Fig8C Pt)).Domain)
    (r₂ : (fig8SrcRT ℓ Pt).denote) :
    (fig8SmCodec ℓ Pt).rdec t
      ((fig8AdaptR ℓ Pt C Dh encPt encT lam).eval
        (.cons r₂ (.cons ((fig8SmCodec ℓ Pt).qenc t) .nil))) =
      decodeSrcR ℓ Pt t r₂ := by
  rcases t with (((⟨p, ⟨pub, m⟩, r⟩ | ⟨p, ⟨pub0, m0⟩, ⟨pub1, m1⟩, r⟩) | ⟨p, c⟩) | ⟨p, c⟩) | p
  · rcases r₂ with (((r | _) | _) | _) | _ <;> rfl
  · rcases r₂ with (((_ | r) | _) | _) | _ <;> rfl
  · rcases r₂ with ((_ | r) | _) | _ <;> rfl
  · rcases r₂ with (_ | r) | _ <;> rfl
  · rcases r₂ with _ | r <;> rfl

private def decodeSrcRDF
    (t : (CryptoGames.SM.specDF (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ)
      (BitVec 256) (Fig8C Pt)).Domain)
    (r₂ : (fig8SrcRDFT ℓ Pt).denote) :
    (CryptoGames.SM.specDF (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ)
      (BitVec 256) (Fig8C Pt)).Range t :=
  match t with
  | .inl t' =>
    match r₂ with
    | .inl r₂' => decodeSrcR ℓ Pt t' r₂'
    | .inr _ =>
      match t' with
      | .inl (.inl (.inl (.inl _))) => none
      | .inl (.inl (.inl (.inr _))) => none
      | .inl (.inl (.inr _)) => none
      | .inl (.inr _) => none
      | .inr _ => none
  | .inr _ =>
    match r₂ with
    | .inr r =>
      r.map (ReductionDsl.smRrDec (ℓ := ℓ) (Pt := Pt) (msgT := fig8MsgT ℓ Pt)
        fun x => (lpubOfV (ℓ := ℓ) (Pt := Pt) x.1, x.2))
    | .inl _ => none

private theorem fig8SmCodecDF_rdec_adaptRDF
    (t : (CryptoGames.SM.specDF (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ)
      (BitVec 256) (Fig8C Pt)).Domain)
    (r₂ : (fig8SrcRDFT ℓ Pt).denote) :
    (fig8SmCodecDF ℓ Pt).rdec t
      ((fig8AdaptRDF ℓ Pt C Dh encPt encT lam).eval
        (.cons r₂ (.cons ((fig8SmCodecDF ℓ Pt).qenc t) .nil))) =
      decodeSrcRDF ℓ Pt t r₂ := by
  rcases t with
    ((((⟨p, ⟨pub, m⟩, r⟩ | ⟨p, ⟨pub0, m0⟩, ⟨pub1, m1⟩, r⟩) | ⟨p, c⟩) | ⟨p, c⟩) | p) | ⟨p, c1, c2⟩
  · rcases r₂ with ((((r | _) | _) | _) | _) | _ <;> rfl
  · rcases r₂ with ((((_ | r) | _) | _) | _) | _ <;> rfl
  · rcases r₂ with (((_ | r) | _) | _) | _ <;> rfl
  · rcases r₂ with ((_ | r) | _) | _ <;> rfl
  · rcases r₂ with (_ | r) | _ <;> rfl
  · rcases r₂ with _ | r <;> rfl

theorem fig8AdaptQ_eval_sm
    (t : (CryptoGames.SM.spec (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ)
      (BitVec 256) (Fig8C Pt)).Domain) :
    (fig8AdaptQ ℓ Pt C Dh encPt encT lam).eval (.cons ((fig8SmCodec ℓ Pt).qenc t) .nil) =
      toVal (fSortSM ℓ Pt) (toDenSM ℓ Pt)
        (smCodec Unit (Fig8St Pt) Unit (LibsignalMsgPublicPart × Plain ℓ)
          (BitVec 256) Unit (Fig8C Pt)).Q
        ((smCodec Unit (Fig8St Pt) Unit (LibsignalMsgPublicPart × Plain ℓ)
          (BitVec 256) Unit (Fig8C Pt)).qenc t) := by
  rcases t with (((⟨p, ⟨pub, m⟩, r⟩ | ⟨p, ⟨pub0, m0⟩, ⟨pub1, m1⟩, r⟩) | ⟨p, c⟩) | ⟨p, c⟩) | p
  · dsimp only [fig8AdaptQ, fig8SmCodec, smCodec, toVal, toDenSM, Expr.eval, Env.get]
    rw [partyToBool_eq_partyEnc]; cases r <;> rfl
  · dsimp only [fig8AdaptQ, fig8SmCodec, smCodec, toVal, toDenSM, Expr.eval, Env.get]
    rw [partyToBool_eq_partyEnc]; cases r <;> rfl
  · dsimp only [fig8AdaptQ, fig8SmCodec, smCodec, toVal, toDenSM, Expr.eval, Env.get]
    rw [partyToBool_eq_partyEnc]; rfl
  · dsimp only [fig8AdaptQ, fig8SmCodec, smCodec, toVal, toDenSM, Expr.eval, Env.get]
    rw [partyToBool_eq_partyEnc]; rfl
  · dsimp only [fig8AdaptQ, fig8SmCodec, smCodec, toVal, toDenSM, Expr.eval, Env.get]
    rw [partyToBool_eq_partyEnc]; rfl

theorem fig8AdaptR_eval_sm
    (t : (CryptoGames.SM.spec (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ)
      (BitVec 256) (Fig8C Pt)).Domain)
    (r₁ : (smCodec Unit (Fig8St Pt) Unit (LibsignalMsgPublicPart × Plain ℓ)
      (BitVec 256) Unit (Fig8C Pt)).R.denote) :
    (fig8SmCodec ℓ Pt).rdec t
      ((fig8AdaptR ℓ Pt C Dh encPt encT lam).eval
        (.cons (toVal (fSortSM ℓ Pt) (toDenSM ℓ Pt)
          (smCodec Unit (Fig8St Pt) Unit (LibsignalMsgPublicPart × Plain ℓ)
            (BitVec 256) Unit (Fig8C Pt)).R r₁)
          (.cons ((fig8SmCodec ℓ Pt).qenc t) .nil))) =
      (smCodec Unit (Fig8St Pt) Unit (LibsignalMsgPublicPart × Plain ℓ)
        (BitVec 256) Unit (Fig8C Pt)).rdec t r₁ := by
  rw [fig8SmCodec_rdec_adaptR]
  rcases t with (((_ | _) | _) | _) | _ <;> rcases r₁ with ((((r | r) | r) | r) | r) <;> try rfl
  · cases r <;> simp [decodeSrcR, toVal, toDenSM, fig8CtOfV_fig8CtV]
  · cases r <;> simp [decodeSrcR, toVal, toDenSM, fig8CtOfV_fig8CtV]
  · rcases r with _ | ⟨⟨⟩ | ⟨_, _, _ | ⟨_, _⟩⟩⟩ <;>
      simp [decodeSrcR, toVal, toDenSM, ReductionDsl.smRrDec, CryptoGames.SM.smRrDec, lpubOfV_lpubV]
  · rcases r with _ | ⟨⟨⟩ | ⟨_, _, _ | ⟨_, _⟩⟩⟩ <;>
      simp [decodeSrcR, toVal, toDenSM, ReductionDsl.smRrDec, CryptoGames.SM.smRrDec, lpubOfV_lpubV]
  · cases r <;> simp [decodeSrcR, toVal, toDenSM, fig8StOfV_fig8StV]

theorem fig8AdaptQDF_eval_sm
    (t : (CryptoGames.SM.specDF (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ)
      (BitVec 256) (Fig8C Pt)).Domain) :
    (fig8AdaptQDF ℓ Pt C Dh encPt encT lam).eval (.cons ((fig8SmCodecDF ℓ Pt).qenc t) .nil) =
      toVal (fSortSM ℓ Pt) (toDenSM ℓ Pt)
        (smCodecDF Unit (Fig8St Pt) Unit (LibsignalMsgPublicPart × Plain ℓ)
          (BitVec 256) Unit (Fig8C Pt)).Q
        ((smCodecDF Unit (Fig8St Pt) Unit (LibsignalMsgPublicPart × Plain ℓ)
          (BitVec 256) Unit (Fig8C Pt)).qenc t) := by
  rcases t with
    ((((⟨p, ⟨pub, m⟩, r⟩ | ⟨p, ⟨pub0, m0⟩, ⟨pub1, m1⟩, r⟩) | ⟨p, c⟩) | ⟨p, c⟩) | p) | ⟨p, c1, c2⟩
  · dsimp only [fig8AdaptQDF, fig8SmCodecDF, smCodecDF, smCodec, toVal, toDenSM, Expr.eval, Env.get]
    rw [partyToBool_eq_partyEnc]; cases r <;> rfl
  · dsimp only [fig8AdaptQDF, fig8SmCodecDF, smCodecDF, smCodec, toVal, toDenSM, Expr.eval, Env.get]
    rw [partyToBool_eq_partyEnc]; cases r <;> rfl
  · dsimp only [fig8AdaptQDF, fig8SmCodecDF, smCodecDF, smCodec, toVal, toDenSM, Expr.eval, Env.get]
    rw [partyToBool_eq_partyEnc]; rfl
  · dsimp only [fig8AdaptQDF, fig8SmCodecDF, smCodecDF, smCodec, toVal, toDenSM, Expr.eval, Env.get]
    rw [partyToBool_eq_partyEnc]; rfl
  · dsimp only [fig8AdaptQDF, fig8SmCodecDF, smCodecDF, smCodec, toVal, toDenSM, Expr.eval, Env.get]
    rw [partyToBool_eq_partyEnc]; rfl
  · dsimp only [fig8AdaptQDF, fig8SmCodecDF, smCodecDF, smCodec, toVal, toDenSM, Expr.eval, Env.get]
    rw [partyToBool_eq_partyEnc]; rfl

theorem fig8AdaptRDF_eval_sm
    (t : (CryptoGames.SM.specDF (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ)
      (BitVec 256) (Fig8C Pt)).Domain)
    (r₁ : (smCodecDF Unit (Fig8St Pt) Unit (LibsignalMsgPublicPart × Plain ℓ)
      (BitVec 256) Unit (Fig8C Pt)).R.denote) :
    (fig8SmCodecDF ℓ Pt).rdec t
      ((fig8AdaptRDF ℓ Pt C Dh encPt encT lam).eval
        (.cons (toVal (fSortSM ℓ Pt) (toDenSM ℓ Pt)
          (smCodecDF Unit (Fig8St Pt) Unit (LibsignalMsgPublicPart × Plain ℓ)
            (BitVec 256) Unit (Fig8C Pt)).R r₁)
          (.cons ((fig8SmCodecDF ℓ Pt).qenc t) .nil))) =
      (smCodecDF Unit (Fig8St Pt) Unit (LibsignalMsgPublicPart × Plain ℓ)
        (BitVec 256) Unit (Fig8C Pt)).rdec t r₁ := by
  rw [fig8SmCodecDF_rdec_adaptRDF]
  rcases t with ((((_ | _) | _) | _) | _) | _ <;>
    rcases r₁ with (((((r | r) | r) | r) | r) | r) <;> try rfl
  · cases r <;> simp [decodeSrcRDF, decodeSrcR, toVal, toDenSM, fig8CtOfV_fig8CtV]
  · cases r <;> simp [decodeSrcRDF, decodeSrcR, toVal, toDenSM, fig8CtOfV_fig8CtV]
  · rcases r with _ | ⟨⟨⟩ | ⟨_, _, _ | ⟨_, _⟩⟩⟩ <;>
      simp [decodeSrcRDF, decodeSrcR, toVal, toDenSM, ReductionDsl.smRrDec, CryptoGames.SM.smRrDec, lpubOfV_lpubV]
  · rcases r with _ | ⟨⟨⟩ | ⟨_, _, _ | ⟨_, _⟩⟩⟩ <;>
      simp [decodeSrcRDF, decodeSrcR, toVal, toDenSM, ReductionDsl.smRrDec, CryptoGames.SM.smRrDec, lpubOfV_lpubV]
  · cases r <;> simp [decodeSrcRDF, decodeSrcR, toVal, toDenSM, fig8StOfV_fig8StV]
  · rcases r with _ | ⟨⟨⟩ | ⟨_, _, _ | ⟨_, _⟩⟩⟩ <;>
      simp [decodeSrcRDF, toVal, toDenSM, ReductionDsl.smRrDec, CryptoGames.SM.smRrDec, lpubOfV_lpubV]

theorem fig8AdaptQ_eval_cka
    (t : (CryptoGames.SM.spec (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ)
      (BitVec 256) (Fig8C Pt)).Domain) :
    (fig8AdaptQ ℓ Pt C Dh encPt encT lam).eval (.cons ((fig8SmCodec ℓ Pt).qenc t) .nil) =
      toVal (fSortCKA ℓ Pt) (toDenCKA ℓ Pt)
        (ckaSMCodec (BitVec 256) (CryptoGames.CKA.DDH.State (BitVec 256) Pt) (BitVec 256) Pt Pt
          (BitVec 256) (BitVec 256) (BitVec 256)
          (RatchetSenderState (BitVec 256)) (RatchetReceiverState (BitVec 256) (BitVec 256))
          (LibsignalMsgPublicPart × Plain ℓ) (ℕ × LibsignalCiphertextWithSalt32)).Q
        ((ckaSMCodec (BitVec 256) (CryptoGames.CKA.DDH.State (BitVec 256) Pt) (BitVec 256) Pt Pt
          (BitVec 256) (BitVec 256) (BitVec 256)
          (RatchetSenderState (BitVec 256)) (RatchetReceiverState (BitVec 256) (BitVec 256))
          (LibsignalMsgPublicPart × Plain ℓ) (ℕ × LibsignalCiphertextWithSalt32)).qenc t) := by
  rcases t with (((⟨p, ⟨pub, m⟩, r⟩ | ⟨p, ⟨pub0, m0⟩, ⟨pub1, m1⟩, r⟩) | ⟨p, ⟨ep, t?⟩, c⟩) | ⟨p, ⟨ep, t?⟩, c⟩) | p
  · dsimp only [fig8AdaptQ, fig8SmCodec, ckaSMCodec, toVal, toDenCKA, Expr.eval, Env.get]
    rw [partyToBool_eq_partyEnc]; cases r <;> rfl
  · dsimp only [fig8AdaptQ, fig8SmCodec, ckaSMCodec, toVal, toDenCKA, Expr.eval, Env.get]
    rw [partyToBool_eq_partyEnc]; cases r <;> rfl
  · dsimp only [fig8AdaptQ, fig8SmCodec, ckaSMCodec, fig8CtV, toVal, toDenCKA, Expr.eval, Env.get]
    rw [partyToBool_eq_partyEnc]; cases t? <;> rfl
  · dsimp only [fig8AdaptQ, fig8SmCodec, ckaSMCodec, fig8CtV, toVal, toDenCKA, Expr.eval, Env.get]
    rw [partyToBool_eq_partyEnc]; cases t? <;> rfl
  · dsimp only [fig8AdaptQ, fig8SmCodec, ckaSMCodec, toVal, toDenCKA, Expr.eval, Env.get]
    rw [partyToBool_eq_partyEnc]; rfl

theorem fig8AdaptR_eval_cka
    (t : (CryptoGames.SM.spec (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ)
      (BitVec 256) (Fig8C Pt)).Domain)
    (r₁ : (ckaSMCodec (BitVec 256) (CryptoGames.CKA.DDH.State (BitVec 256) Pt) (BitVec 256) Pt Pt
      (BitVec 256) (BitVec 256) (BitVec 256)
      (RatchetSenderState (BitVec 256)) (RatchetReceiverState (BitVec 256) (BitVec 256))
      (LibsignalMsgPublicPart × Plain ℓ) (ℕ × LibsignalCiphertextWithSalt32)).R.denote) :
    (fig8SmCodec ℓ Pt).rdec t
      ((fig8AdaptR ℓ Pt C Dh encPt encT lam).eval
        (.cons (toVal (fSortCKA ℓ Pt) (toDenCKA ℓ Pt)
          (ckaSMCodec (BitVec 256) (CryptoGames.CKA.DDH.State (BitVec 256) Pt) (BitVec 256) Pt Pt
            (BitVec 256) (BitVec 256) (BitVec 256)
            (RatchetSenderState (BitVec 256)) (RatchetReceiverState (BitVec 256) (BitVec 256))
            (LibsignalMsgPublicPart × Plain ℓ) (ℕ × LibsignalCiphertextWithSalt32)).R r₁)
          (.cons ((fig8SmCodec ℓ Pt).qenc t) .nil))) =
      (ckaSMCodec (BitVec 256) (CryptoGames.CKA.DDH.State (BitVec 256) Pt) (BitVec 256) Pt Pt
        (BitVec 256) (BitVec 256) (BitVec 256)
        (RatchetSenderState (BitVec 256)) (RatchetReceiverState (BitVec 256) (BitVec 256))
        (LibsignalMsgPublicPart × Plain ℓ) (ℕ × LibsignalCiphertextWithSalt32)).rdec t r₁ := by
  rw [fig8SmCodec_rdec_adaptR]
  rcases t with (((_ | _) | _) | _) | _ <;> rcases r₁ with ((((r | r) | r) | r) | r) <;> try rfl
  · rcases r with _ | ⟨⟨ep, t?⟩, c⟩ <;> [rfl; (cases t? <;> simp [decodeSrcR, fig8CtOfV, toVal, toDenCKA, lctOfV_lctV])]
  · rcases r with _ | ⟨⟨ep, t?⟩, c⟩ <;> [rfl; (cases t? <;> simp [decodeSrcR, fig8CtOfV, toVal, toDenCKA, lctOfV_lctV])]
  · rcases r with _ | ⟨⟨⟩ | ⟨_, _, _ | ⟨_, _⟩⟩⟩ <;>
      simp [decodeSrcR, toVal, toDenCKA, ReductionDsl.smRrDec, CryptoGames.SM.smRrDec, lpubOfV_lpubV]
  · rcases r with _ | ⟨⟨⟩ | ⟨_, _, _ | ⟨_, _⟩⟩⟩ <;>
      simp [decodeSrcR, toVal, toDenCKA, ReductionDsl.smRrDec, CryptoGames.SM.smRrDec, lpubOfV_lpubV]
  · rcases r with _ | ps
    · rfl
    · dsimp only [decodeSrcR, ckaSMCodec, Option.map]
      exact congrArg some (fig8StOfV_toVal_ckaPsTy ℓ Pt ps)

theorem fig8AdaptQDF_eval_cka
    (t : (CryptoGames.SM.specDF (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ)
      (BitVec 256) (Fig8C Pt)).Domain) :
    (fig8AdaptQDF ℓ Pt C Dh encPt encT lam).eval (.cons ((fig8SmCodecDF ℓ Pt).qenc t) .nil) =
      toVal (fSortCKA ℓ Pt) (toDenCKA ℓ Pt)
        (ckaSMCodecDF (BitVec 256) (CryptoGames.CKA.DDH.State (BitVec 256) Pt) (BitVec 256) Pt Pt
          (BitVec 256) (BitVec 256) (BitVec 256)
          (RatchetSenderState (BitVec 256)) (RatchetReceiverState (BitVec 256) (BitVec 256))
          (LibsignalMsgPublicPart × Plain ℓ) (ℕ × LibsignalCiphertextWithSalt32)).Q
        ((ckaSMCodecDF (BitVec 256) (CryptoGames.CKA.DDH.State (BitVec 256) Pt) (BitVec 256) Pt Pt
          (BitVec 256) (BitVec 256) (BitVec 256)
          (RatchetSenderState (BitVec 256)) (RatchetReceiverState (BitVec 256) (BitVec 256))
          (LibsignalMsgPublicPart × Plain ℓ) (ℕ × LibsignalCiphertextWithSalt32)).qenc t) := by
  rcases t with
    ((((⟨p, ⟨pub, m⟩, r⟩ | ⟨p, ⟨pub0, m0⟩, ⟨pub1, m1⟩, r⟩) | ⟨p, ⟨ep, t?⟩, c⟩) | ⟨p, ⟨ep, t?⟩, c⟩) | p) |
      ⟨p, ⟨⟨ep1, t1?⟩, c1⟩, ⟨⟨ep2, t2?⟩, c2⟩⟩
  · dsimp only [fig8AdaptQDF, fig8SmCodecDF, ckaSMCodecDF, ckaSMCodec, toVal, toDenCKA, Expr.eval, Env.get]
    rw [partyToBool_eq_partyEnc]; cases r <;> rfl
  · dsimp only [fig8AdaptQDF, fig8SmCodecDF, ckaSMCodecDF, ckaSMCodec, toVal, toDenCKA, Expr.eval, Env.get]
    rw [partyToBool_eq_partyEnc]; cases r <;> rfl
  · dsimp only [fig8AdaptQDF, fig8SmCodecDF, ckaSMCodecDF, ckaSMCodec, fig8CtV, toVal, toDenCKA, Expr.eval, Env.get]
    rw [partyToBool_eq_partyEnc]; cases t? <;> rfl
  · dsimp only [fig8AdaptQDF, fig8SmCodecDF, ckaSMCodecDF, ckaSMCodec, fig8CtV, toVal, toDenCKA, Expr.eval, Env.get]
    rw [partyToBool_eq_partyEnc]; cases t? <;> rfl
  · dsimp only [fig8AdaptQDF, fig8SmCodecDF, ckaSMCodecDF, ckaSMCodec, toVal, toDenCKA, Expr.eval, Env.get]
    rw [partyToBool_eq_partyEnc]; rfl
  · dsimp only [fig8AdaptQDF, fig8SmCodecDF, ckaSMCodecDF, ckaSMCodec, fig8CtV, toVal, toDenCKA, Expr.eval, Env.get]
    rw [partyToBool_eq_partyEnc]; cases t1? <;> cases t2? <;> rfl

theorem fig8AdaptRDF_eval_cka
    (t : (CryptoGames.SM.specDF (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ)
      (BitVec 256) (Fig8C Pt)).Domain)
    (r₁ : (ckaSMCodecDF (BitVec 256) (CryptoGames.CKA.DDH.State (BitVec 256) Pt) (BitVec 256) Pt Pt
      (BitVec 256) (BitVec 256) (BitVec 256)
      (RatchetSenderState (BitVec 256)) (RatchetReceiverState (BitVec 256) (BitVec 256))
      (LibsignalMsgPublicPart × Plain ℓ) (ℕ × LibsignalCiphertextWithSalt32)).R.denote) :
    (fig8SmCodecDF ℓ Pt).rdec t
      ((fig8AdaptRDF ℓ Pt C Dh encPt encT lam).eval
        (.cons (toVal (fSortCKA ℓ Pt) (toDenCKA ℓ Pt)
          (ckaSMCodecDF (BitVec 256) (CryptoGames.CKA.DDH.State (BitVec 256) Pt) (BitVec 256) Pt Pt
            (BitVec 256) (BitVec 256) (BitVec 256)
            (RatchetSenderState (BitVec 256)) (RatchetReceiverState (BitVec 256) (BitVec 256))
            (LibsignalMsgPublicPart × Plain ℓ) (ℕ × LibsignalCiphertextWithSalt32)).R r₁)
          (.cons ((fig8SmCodecDF ℓ Pt).qenc t) .nil))) =
      (ckaSMCodecDF (BitVec 256) (CryptoGames.CKA.DDH.State (BitVec 256) Pt) (BitVec 256) Pt Pt
        (BitVec 256) (BitVec 256) (BitVec 256)
        (RatchetSenderState (BitVec 256)) (RatchetReceiverState (BitVec 256) (BitVec 256))
        (LibsignalMsgPublicPart × Plain ℓ) (ℕ × LibsignalCiphertextWithSalt32)).rdec t r₁ := by
  rw [fig8SmCodecDF_rdec_adaptRDF]
  rcases t with ((((_ | _) | _) | _) | _) | _ <;>
    rcases r₁ with (((((r | r) | r) | r) | r) | r) <;> try rfl
  · rcases r with _ | ⟨⟨ep, t?⟩, c⟩ <;> [rfl; (cases t? <;> simp [decodeSrcRDF, decodeSrcR, fig8CtOfV, toVal, toDenCKA, lctOfV_lctV])]
  · rcases r with _ | ⟨⟨ep, t?⟩, c⟩ <;> [rfl; (cases t? <;> simp [decodeSrcRDF, decodeSrcR, fig8CtOfV, toVal, toDenCKA, lctOfV_lctV])]
  · rcases r with _ | ⟨⟨⟩ | ⟨_, _, _ | ⟨_, _⟩⟩⟩ <;>
      simp [decodeSrcRDF, decodeSrcR, toVal, toDenCKA, ReductionDsl.smRrDec, CryptoGames.SM.smRrDec, lpubOfV_lpubV]
  · rcases r with _ | ⟨⟨⟩ | ⟨_, _, _ | ⟨_, _⟩⟩⟩ <;>
      simp [decodeSrcRDF, decodeSrcR, toVal, toDenCKA, ReductionDsl.smRrDec, CryptoGames.SM.smRrDec, lpubOfV_lpubV]
  · rcases r with _ | ps
    · rfl
    · dsimp only [decodeSrcRDF, decodeSrcR, ckaSMCodecDF, ckaSMCodec, Option.map]
      exact congrArg some (fig8StOfV_toVal_ckaPsTy ℓ Pt ps)
  · rcases r with _ | ⟨⟨⟩ | ⟨_, _, _ | ⟨_, _⟩⟩⟩ <;>
      simp [decodeSrcRDF, toVal, toDenCKA, ReductionDsl.smRrDec, CryptoGames.SM.smRrDec, lpubOfV_lpubV]

end SortAndAdapters

section Bundles

variable (ℓ : ℕ) (Pt : Type) [DecidableEq Pt] [Zero Pt] [SampleableType Pt]
  (C : Crypto) (Dh : DHFun (BitVec 256) Pt) (encPt : Pt → List (BitVec 8))
  (encT : Pt → PublicKey) (idOf : Party → IdentityKey) (lam : Pt)

local notation "S₂" => atomicSig ℓ Pt
local notation "O₂" => atomicFig8Ops ℓ Pt C Dh encPt encT lam

@[reducible] def sampBV256Atomic : ProbComp (BitVec 256) :=
  ($ᵗ (BitVec 256) : ProbComp (BitVec 256))

@[reducible] def fig8SmOpsShallow :
    Ops (smSig Unit (Fig8St Pt) Unit (LibsignalMsgPublicPart × Plain ℓ)
      (BitVec 256) Unit (Fig8C Pt)) :=
  smOps
    (Key := Unit) (St := Fig8St Pt) (St₂ := Unit)
    (Msg := LibsignalMsgPublicPart × Plain ℓ) (Coins := BitVec 256) (RCoins := Unit)
    (C := Fig8C Pt)
    (init := fun _ _ => none)
    (send := fun _ _ _ => none)
    (receive := fun _ _ _ => none)
    (eqMsg := @BEq.beq (LibsignalMsgPublicPart × Plain ℓ) instBEqOfDecidableEq)
    (eqCt := @BEq.beq (Fig8C Pt) instBEqOfDecidableEq)
    (blank := lBlank ℓ)
    (injOK := fun _ => true)
    (stOK := fun _ _ => true)
    (φ := fun _ => none)

def smOpMacro :
    (o : SMOp) →
      Expr O₂
        [mapTy (fSortSM ℓ Pt) ((fig8SmOpsShallow ℓ Pt).dom o), .prod IdKey IdKey]
        (mapTy (fSortSM ℓ Pt) ((fig8SmOpsShallow ℓ Pt).cod o))
  | .init => .none
  | .send => .none
  | .receive _ => .none
  | .eqMsg => eqMExpr ℓ Pt C Dh encPt encT lam
  | .eqCt => smEqCtExpr ℓ Pt C Dh encPt encT lam
  | .blank => smBlankExpr ℓ Pt C Dh encPt encT lam
  | .injOK => .bool true
  | .stOK => .bool true
  | .relabelSt => .none

def smSampMacro :
    (s : SMSamp) →
      Comp O₂ (fig8SmIface ℓ Pt)
        [mapTy (fSortSM ℓ Pt) ((smIface Unit (Fig8St Pt) Unit
          (LibsignalMsgPublicPart × Plain ℓ) (BitVec 256) Unit (Fig8C Pt)).smp.sDom s),
         .prod IdKey IdKey]
        (mapTy (fSortSM ℓ Pt) ((smIface Unit (Fig8St Pt) Unit
          (LibsignalMsgPublicPart × Plain ℓ) (BitVec 256) Unit (Fig8C Pt)).smp.sTy s))
  | .bit => Comp.sample (O := O₂) (I := fig8SmIface ℓ Pt) UniformSamplerTag.bool .unit
  | .key => .ret .none
  | .coins => .ret .none
  | .rcoins => .ret .none

def smDFSampMacro :
    (s : SMSamp) →
      Comp O₂ (fig8SmIfaceDF ℓ Pt)
        [mapTy (fSortSM ℓ Pt) ((smIfaceDF Unit (Fig8St Pt) Unit
          (LibsignalMsgPublicPart × Plain ℓ) (BitVec 256) Unit (Fig8C Pt)).smp.sDom s),
         .prod IdKey IdKey]
        (mapTy (fSortSM ℓ Pt) ((smIfaceDF Unit (Fig8St Pt) Unit
          (LibsignalMsgPublicPart × Plain ℓ) (BitVec 256) Unit (Fig8C Pt)).smp.sTy s))
  | .bit => Comp.sample (O := O₂) (I := fig8SmIfaceDF ℓ Pt) UniformSamplerTag.bool .unit
  | .key => .ret .none
  | .coins => .ret .none
  | .rcoins => .ret .none

@[reducible] def smPureAuxBundle :
    PureAuxBundle
      (smSig Unit (Fig8St Pt) Unit (LibsignalMsgPublicPart × Plain ℓ)
        (BitVec 256) Unit (Fig8C Pt))
      S₂
      (fig8SmOpsShallow ℓ Pt)
      O₂
      (smIface Unit (Fig8St Pt) Unit (LibsignalMsgPublicPart × Plain ℓ)
        (BitVec 256) Unit (Fig8C Pt))
      (fig8SmIface ℓ Pt)
      (.prod IdKey IdKey) where
  fSort := fSortSM ℓ Pt
  opMacro := smOpMacro ℓ Pt C Dh encPt encT lam
  sampMacro := smSampMacro ℓ Pt C Dh encPt encT lam
  queryMacro
    | .tr => Comp.query (O := O₂) (I := fig8SmIface ℓ Pt) ReductionDsl.SMTag.tr (.var .zero)
    | .ch => Comp.query (O := O₂) (I := fig8SmIface ℓ Pt) ReductionDsl.SMTag.ch (.var .zero)
    | .dl => Comp.query (O := O₂) (I := fig8SmIface ℓ Pt) ReductionDsl.SMTag.dl (.var .zero)
    | .ij => Comp.query (O := O₂) (I := fig8SmIface ℓ Pt) ReductionDsl.SMTag.ij (.var .zero)
    | .cr => Comp.query (O := O₂) (I := fig8SmIface ℓ Pt) ReductionDsl.SMTag.cr (.var .zero)

@[reducible] def smDFPureAuxBundle :
    PureAuxBundle
      (smSig Unit (Fig8St Pt) Unit (LibsignalMsgPublicPart × Plain ℓ)
        (BitVec 256) Unit (Fig8C Pt))
      S₂
      (fig8SmOpsShallow ℓ Pt)
      O₂
      (smIfaceDF Unit (Fig8St Pt) Unit (LibsignalMsgPublicPart × Plain ℓ)
        (BitVec 256) Unit (Fig8C Pt))
      (fig8SmIfaceDF ℓ Pt)
      (.prod IdKey IdKey) where
  fSort := fSortSM ℓ Pt
  opMacro := smOpMacro ℓ Pt C Dh encPt encT lam
  sampMacro := smDFSampMacro ℓ Pt C Dh encPt encT lam
  queryMacro
    | .tr => Comp.query (O := O₂) (I := fig8SmIfaceDF ℓ Pt) ReductionDsl.SMTagDF.tr (.var .zero)
    | .ch => Comp.query (O := O₂) (I := fig8SmIfaceDF ℓ Pt) ReductionDsl.SMTagDF.ch (.var .zero)
    | .dl => Comp.query (O := O₂) (I := fig8SmIfaceDF ℓ Pt) ReductionDsl.SMTagDF.dl (.var .zero)
    | .ij => Comp.query (O := O₂) (I := fig8SmIfaceDF ℓ Pt) ReductionDsl.SMTagDF.ij (.var .zero)
    | .cr => Comp.query (O := O₂) (I := fig8SmIfaceDF ℓ Pt) ReductionDsl.SMTagDF.cr (.var .zero)
    | .df => Comp.query (O := O₂) (I := fig8SmIfaceDF ℓ Pt) ReductionDsl.SMTagDF.df (.var .zero)


@[reducible] def fig8CkaOpsShallow (B0 : ℕ) :
    Ops (ckaSig (BitVec 256) (CryptoGames.CKA.DDH.State (BitVec 256) Pt) (BitVec 256) Pt Pt
      (BitVec 256) (BitVec 256) (BitVec 256)
      (RatchetSenderState (BitVec 256)) (RatchetReceiverState (BitVec 256) (BitVec 256))
      (LibsignalMsgPublicPart × Plain ℓ) (ℕ × LibsignalCiphertextWithSalt32)) :=
  ckaSchemeOps (dhSchemeFb Dh) (rootPRNG C.F encPt) (fsAtomicB C ℓ encT idOf B0) lam

def ckaOpMacro (B0 : ℕ) :
    (o : CKAOp) →
      Expr O₂
        [mapTy (fSortCKA ℓ Pt) ((fig8CkaOpsShallow ℓ Pt C Dh encPt encT idOf lam B0).dom o),
         .prod IdKey IdKey]
        (mapTy (fSortCKA ℓ Pt) ((fig8CkaOpsShallow ℓ Pt C Dh encPt encT idOf lam B0).cod o))
  | .ckaInitA => ckaInitAExpr ℓ Pt C Dh encPt encT lam
  | .ckaInitB => ckaInitBExpr ℓ Pt C Dh encPt encT lam
  | .ckaSend => ckaSendExpr ℓ Pt C Dh encPt encT lam
  | .ckaReceive => ckaRecvExpr ℓ Pt C Dh encPt encT lam
  | .prngInit => prngInitExpr ℓ Pt C Dh encPt encT lam
  | .prngUp => prngUpExpr ℓ Pt C Dh encPt encT lam
  | .fsInitSender => fsInitSendExpr ℓ Pt C Dh encPt encT lam
  | .fsInitReceiver => fsInitRecvExpr ℓ Pt C Dh encPt encT lam
  | .fsSend => fsSendExpr ℓ Pt C Dh encPt encT lam
  | .fsReceive B => fsRecvExpr ℓ Pt C Dh encPt encT lam B0 B
  | .eqT => eqPtExpr ℓ Pt C Dh encPt encT lam
  | .eqI => eqPtExpr ℓ Pt C Dh encPt encT lam
  | .eqM => eqMExpr ℓ Pt C Dh encPt encT lam
  | .eqE => eqEExpr ℓ Pt C Dh encPt encT lam
  | .lamI => lamIExpr ℓ Pt C Dh encPt encT lam
  | .defaultE => defaultEExpr ℓ Pt C Dh encPt encT lam

def ckaSampMacro (sampBV : ProbComp (BitVec 256)) :
    (s : CKASamp) →
      Comp O₂ (ckaTargetIface ℓ Pt)
        [mapTy (fSortCKA ℓ Pt)
          ((ckaSamplers (Γ := CryptoGames.CKA.DDH.State (BitVec 256) Pt) (T := Pt)
            (RSt := BitVec 256) (SS := RatchetSenderState (BitVec 256))
            (RS := RatchetReceiverState (BitVec 256) (BitVec 256))
            (M := LibsignalMsgPublicPart × Plain ℓ) (E := ℕ × LibsignalCiphertextWithSalt32)
            sampBV sampBV sampBV ($ᵗ Pt) sampBV).sDom s),
         .prod IdKey IdKey]
        (mapTy (fSortCKA ℓ Pt)
          ((ckaSamplers (Γ := CryptoGames.CKA.DDH.State (BitVec 256) Pt) (T := Pt)
            (RSt := BitVec 256) (SS := RatchetSenderState (BitVec 256))
            (RS := RatchetReceiverState (BitVec 256) (BitVec 256))
            (M := LibsignalMsgPublicPart × Plain ℓ) (E := ℕ × LibsignalCiphertextWithSalt32)
            sampBV sampBV sampBV ($ᵗ Pt) sampBV).sTy s))
  | .bit => Comp.sample (O := O₂) (I := ckaTargetIface ℓ Pt) UniformSamplerTag.bool .unit
  | .kr | .kc | .ccoins | .k =>
      Comp.sample (O := O₂) (I := ckaTargetIface ℓ Pt) (UniformSamplerTag.base AtomicUnifBase.bv256) .unit
  | .i =>
      Comp.sample (O := O₂) (I := ckaTargetIface ℓ Pt) (UniformSamplerTag.base AtomicUnifBase.pt) .unit

def prngSampMacro (sampBV : ProbComp (BitVec 256)) :
    (s : CKASamp) →
      Comp O₂ (prngTargetIface ℓ Pt)
        [mapTy (fSortCKA ℓ Pt)
          ((ckaSamplers (Γ := CryptoGames.CKA.DDH.State (BitVec 256) Pt) (T := Pt)
            (RSt := BitVec 256) (SS := RatchetSenderState (BitVec 256))
            (RS := RatchetReceiverState (BitVec 256) (BitVec 256))
            (M := LibsignalMsgPublicPart × Plain ℓ) (E := ℕ × LibsignalCiphertextWithSalt32)
            sampBV sampBV sampBV ($ᵗ Pt) sampBV).sDom s),
         .prod IdKey IdKey]
        (mapTy (fSortCKA ℓ Pt)
          ((ckaSamplers (Γ := CryptoGames.CKA.DDH.State (BitVec 256) Pt) (T := Pt)
            (RSt := BitVec 256) (SS := RatchetSenderState (BitVec 256))
            (RS := RatchetReceiverState (BitVec 256) (BitVec 256))
            (M := LibsignalMsgPublicPart × Plain ℓ) (E := ℕ × LibsignalCiphertextWithSalt32)
            sampBV sampBV sampBV ($ᵗ Pt) sampBV).sTy s))
  | .bit => Comp.sample (O := O₂) (I := prngTargetIface ℓ Pt) UniformSamplerTag.bool .unit
  | .kr | .kc | .ccoins | .k =>
      Comp.sample (O := O₂) (I := prngTargetIface ℓ Pt) (UniformSamplerTag.base AtomicUnifBase.bv256) .unit
  | .i =>
      Comp.sample (O := O₂) (I := prngTargetIface ℓ Pt) (UniformSamplerTag.base AtomicUnifBase.pt) .unit

def fsSampMacro (sampBV : ProbComp (BitVec 256)) :
    (s : CKASamp) →
      Comp O₂ (fsaeadHeaderIface ℓ Pt)
        [mapTy (fSortCKA ℓ Pt)
          ((ckaSamplers (Γ := CryptoGames.CKA.DDH.State (BitVec 256) Pt) (T := Pt)
            (RSt := BitVec 256) (SS := RatchetSenderState (BitVec 256))
            (RS := RatchetReceiverState (BitVec 256) (BitVec 256))
            (M := LibsignalMsgPublicPart × Plain ℓ) (E := ℕ × LibsignalCiphertextWithSalt32)
            sampBV sampBV sampBV ($ᵗ Pt) sampBV).sDom s),
         .prod IdKey IdKey]
        (mapTy (fSortCKA ℓ Pt)
          ((ckaSamplers (Γ := CryptoGames.CKA.DDH.State (BitVec 256) Pt) (T := Pt)
            (RSt := BitVec 256) (SS := RatchetSenderState (BitVec 256))
            (RS := RatchetReceiverState (BitVec 256) (BitVec 256))
            (M := LibsignalMsgPublicPart × Plain ℓ) (E := ℕ × LibsignalCiphertextWithSalt32)
            sampBV sampBV sampBV ($ᵗ Pt) sampBV).sTy s))
  | .bit => Comp.sample (O := O₂) (I := fsaeadHeaderIface ℓ Pt) UniformSamplerTag.bool .unit
  | .kr | .kc | .ccoins | .k =>
      Comp.sample (O := O₂) (I := fsaeadHeaderIface ℓ Pt) (UniformSamplerTag.base AtomicUnifBase.bv256) .unit
  | .i =>
      Comp.sample (O := O₂) (I := fsaeadHeaderIface ℓ Pt) (UniformSamplerTag.base AtomicUnifBase.pt) .unit

@[reducible] def ckaPureAuxBundle (B0 : ℕ) (sampBV : ProbComp (BitVec 256)) :
    PureAuxBundle
      (ckaSig (BitVec 256) (CryptoGames.CKA.DDH.State (BitVec 256) Pt) (BitVec 256) Pt Pt
        (BitVec 256) (BitVec 256) (BitVec 256)
        (RatchetSenderState (BitVec 256)) (RatchetReceiverState (BitVec 256) (BitVec 256))
        (LibsignalMsgPublicPart × Plain ℓ) (ℕ × LibsignalCiphertextWithSalt32))
      S₂
      (fig8CkaOpsShallow ℓ Pt C Dh encPt encT idOf lam B0)
      O₂
      (ckaIface (BitVec 256) (CryptoGames.CKA.DDH.State (BitVec 256) Pt) (BitVec 256) Pt Pt
        (BitVec 256) (BitVec 256) (BitVec 256)
        (RatchetSenderState (BitVec 256)) (RatchetReceiverState (BitVec 256) (BitVec 256))
        (LibsignalMsgPublicPart × Plain ℓ) (ℕ × LibsignalCiphertextWithSalt32)
        sampBV sampBV sampBV ($ᵗ Pt) sampBV)
      (ckaTargetIface ℓ Pt)
      (.prod IdKey IdKey) where
  fSort := fSortCKA ℓ Pt
  opMacro := ckaOpMacro ℓ Pt C Dh encPt encT idOf lam B0
  sampMacro := ckaSampMacro ℓ Pt C Dh encPt encT lam sampBV
  queryMacro
    | .send => Comp.query (O := O₂) (I := ckaTargetIface ℓ Pt) ReductionDsl.CKATag.send (.var .zero)
    | .sendBad => Comp.query (O := O₂) (I := ckaTargetIface ℓ Pt) ReductionDsl.CKATag.sendBad (.var .zero)
    | .chall => Comp.query (O := O₂) (I := ckaTargetIface ℓ Pt) ReductionDsl.CKATag.chall (.var .zero)
    | .receive => Comp.query (O := O₂) (I := ckaTargetIface ℓ Pt) ReductionDsl.CKATag.receive (.var .zero)
    | .corr => Comp.query (O := O₂) (I := ckaTargetIface ℓ Pt) ReductionDsl.CKATag.corr (.var .zero)

@[reducible] def prngPureAuxBundle (B0 : ℕ) (sampBV : ProbComp (BitVec 256)) :
    PureAuxBundle
      (prngSig (BitVec 256) (CryptoGames.CKA.DDH.State (BitVec 256) Pt) (BitVec 256) Pt Pt
        (BitVec 256) (BitVec 256) (BitVec 256)
        (RatchetSenderState (BitVec 256)) (RatchetReceiverState (BitVec 256) (BitVec 256))
        (LibsignalMsgPublicPart × Plain ℓ) (ℕ × LibsignalCiphertextWithSalt32))
      S₂
      (fig8CkaOpsShallow ℓ Pt C Dh encPt encT idOf lam B0)
      O₂
      (prngIface (BitVec 256) (CryptoGames.CKA.DDH.State (BitVec 256) Pt) (BitVec 256) Pt Pt
        (BitVec 256) (BitVec 256) (BitVec 256)
        (RatchetSenderState (BitVec 256)) (RatchetReceiverState (BitVec 256) (BitVec 256))
        (LibsignalMsgPublicPart × Plain ℓ) (ℕ × LibsignalCiphertextWithSalt32)
        sampBV sampBV sampBV ($ᵗ Pt) sampBV)
      (prngTargetIface ℓ Pt)
      (.prod IdKey IdKey) where
  fSort := fSortCKA ℓ Pt
  opMacro := ckaOpMacro ℓ Pt C Dh encPt encT idOf lam B0
  sampMacro := prngSampMacro ℓ Pt C Dh encPt encT lam sampBV
  queryMacro
    | .process => Comp.query (O := O₂) (I := prngTargetIface ℓ Pt) ReductionDsl.PRNGTag.process (.var .zero)
    | .challPrng => Comp.query (O := O₂) (I := prngTargetIface ℓ Pt) ReductionDsl.PRNGTag.challPrng (.var .zero)
    | .challPrf => Comp.query (O := O₂) (I := prngTargetIface ℓ Pt) ReductionDsl.PRNGTag.challPrf (.var .zero)
    | .corr => Comp.query (O := O₂) (I := prngTargetIface ℓ Pt) ReductionDsl.PRNGTag.corr (.var .zero)

@[reducible] def fsPureAuxBundle (B0 : ℕ) (sampBV : ProbComp (BitVec 256)) :
    PureAuxBundle
      (prngSig (BitVec 256) (CryptoGames.CKA.DDH.State (BitVec 256) Pt) (BitVec 256) Pt Pt
        (BitVec 256) (BitVec 256) (BitVec 256)
        (RatchetSenderState (BitVec 256)) (RatchetReceiverState (BitVec 256) (BitVec 256))
        (LibsignalMsgPublicPart × Plain ℓ) (ℕ × LibsignalCiphertextWithSalt32))
      S₂
      (fig8CkaOpsShallow ℓ Pt C Dh encPt encT idOf lam B0)
      O₂
      (fsaeadHeaderAdIface (BitVec 256) (CryptoGames.CKA.DDH.State (BitVec 256) Pt) (BitVec 256) Pt Pt
        (BitVec 256) (BitVec 256) (BitVec 256)
        (RatchetSenderState (BitVec 256)) (RatchetReceiverState (BitVec 256) (BitVec 256))
        (LibsignalMsgPublicPart × Plain ℓ) (ℕ × LibsignalCiphertextWithSalt32)
        sampBV sampBV sampBV ($ᵗ Pt) sampBV)
      (fsaeadHeaderIface ℓ Pt)
      (.prod IdKey IdKey) where
  fSort := fSortCKA ℓ Pt
  opMacro := ckaOpMacro ℓ Pt C Dh encPt encT idOf lam B0
  sampMacro := fsSampMacro ℓ Pt C Dh encPt encT lam sampBV
  queryMacro
    | .tr => Comp.query (O := O₂) (I := fsaeadHeaderIface ℓ Pt) ReductionDsl.FSAEADTag.tr (.var .zero)
    | .ch => Comp.query (O := O₂) (I := fsaeadHeaderIface ℓ Pt) ReductionDsl.FSAEADTag.ch (.var .zero)
    | .cs => Comp.query (O := O₂) (I := fsaeadHeaderIface ℓ Pt) ReductionDsl.FSAEADTag.cs (.var .zero)
    | .cr => Comp.query (O := O₂) (I := fsaeadHeaderIface ℓ Pt) ReductionDsl.FSAEADTag.cr (.var .zero)
    | .dl => Comp.query (O := O₂) (I := fsaeadHeaderIface ℓ Pt) ReductionDsl.FSAEADTag.dl (.var .zero)
    | .ij => Comp.query (O := O₂) (I := fsaeadHeaderIface ℓ Pt) ReductionDsl.FSAEADTag.ij (.var .zero)


omit [DecidableEq Pt] [Zero Pt] [SampleableType Pt] in
theorem smRrEnc_eq_toVal_smRrEnc (rr : CryptoGames.SM.RecvResult (LibsignalMsgPublicPart × Plain ℓ)) :
    ReductionDsl.smRrEnc (msgT := fig8MsgT ℓ Pt) (fun (pub, m) => (lpubV pub, m)) rr =
      toVal (fSortSM ℓ Pt) (toDenSM ℓ Pt)
        (CryptoGames.SM.smRrTy Unit (Fig8St Pt) Unit (LibsignalMsgPublicPart × Plain ℓ)
          (BitVec 256) Unit (Fig8C Pt))
        (CryptoGames.SM.smRrEnc rr) := by
  rcases rr with _ | ⟨t, i, _ | ⟨pub, m⟩⟩ <;> rfl

omit [DecidableEq Pt] [Zero Pt] [SampleableType Pt] in
theorem fsRrEnc_eq_toVal_fsHdrRrEnc
    (rr : CryptoGames.FSAEAD.ReceiveResult (LibsignalMsgPublicPart × Plain ℓ)) :
    ReductionDsl.fsRrEnc (ℓ := ℓ) (Pt := Pt) (msgT := fig8MsgT ℓ Pt)
        (fun (pub, m) => (lpubV pub, m)) rr =
      toVal (fSortCKA ℓ Pt) (toDenCKA ℓ Pt)
        (CryptoGames.PRFPRNG.fsHdrRrTy (BitVec 256) (CryptoGames.CKA.DDH.State (BitVec 256) Pt)
          (BitVec 256) Pt Pt (BitVec 256) (BitVec 256) (BitVec 256)
          (RatchetSenderState (BitVec 256)) (RatchetReceiverState (BitVec 256) (BitVec 256))
          (LibsignalMsgPublicPart × Plain ℓ) (ℕ × LibsignalCiphertextWithSalt32))
        (fsHdrRrEnc rr) := by
  rcases rr with _ | ⟨i, _ | ⟨pub, m⟩⟩ <;> rfl

theorem sampBV256Atomic_evalDistEq :
    sampBV256Atomic =ᵈ ($ᵗ (BitVec 256) : ProbComp (BitVec 256)) := by
  simpa only [id_map] using
    @SampleableType.map_uniformSample_evalDistEq_of_bijective
      (BitVec 256) (BitVec 256) inferInstance inferInstance
      id Function.bijective_id

omit [Zero Pt] [SampleableType Pt] in
private theorem fig8C_beq_eq_dec (c1 c2 : Fig8C Pt) :
    (c1 == c2) = @BEq.beq (Fig8C Pt) instBEqOfDecidableEq c1 c2 :=
  Bool.eq_iff_iff.mpr (beq_iff_eq.trans decide_eq_true_iff.symm)

omit [SampleableType Pt] in
theorem smOpMacro_eval (o : SMOp)
    (z : ((fig8SmOpsShallow ℓ Pt).dom o).denote) :
    (smOpMacro ℓ Pt C Dh encPt encT lam o).eval
      (.cons (toVal (fSortSM ℓ Pt) (toDenSM ℓ Pt) ((fig8SmOpsShallow ℓ Pt).dom o) z)
        (.cons (idOf .A, idOf .B) .nil)) =
      toVal (fSortSM ℓ Pt) (toDenSM ℓ Pt) ((fig8SmOpsShallow ℓ Pt).cod o)
        ((fig8SmOpsShallow ℓ Pt).eval o z) := by
  cases o with
  | init | send | receive _ | injOK | stOK | relabelSt => rfl
  | eqMsg =>
    rcases z with ⟨⟨p1, m1⟩, ⟨p2, m2⟩⟩
    exact eqMExpr_eval ℓ Pt C Dh encPt encT lam idOf (p1, m1) (p2, m2)
  | eqCt =>
    rcases z with ⟨c1, c2⟩
    dsimp only [smOpMacro, fig8SmOpsShallow, smOps, toVal, toDenSM]
    rw [smEqCtExpr_eval ℓ Pt C Dh encPt encT lam idOf c1 c2, fig8C_beq_eq_dec]
  | blank =>
    rcases z with ⟨p, m⟩
    exact smBlankExpr_eval ℓ Pt C Dh encPt encT lam idOf (p, m)

private theorem liftP_congr {ι : Type} {T : OracleSpec.{0, 0} ι} {S₁' S₂' : Sig}
    (I₂ : Iface S₂' T) (I₁ : Iface S₁' T) (hFwdU : ∀ n, I₂.fwdU n = I₁.fwdU n)
    {α : Type} (p : ProbComp α) : I₂.liftP p = I₁.liftP p := by
  unfold Iface.liftP
  rw [funext hFwdU]

private theorem env_get_zero {S' : Sig} {a : Ty S'} {Γ : List (Ty S')}
    (x : a.denote) (ρ : Env Γ) : (Env.cons x ρ).get .zero = x := rfl

theorem smPureAuxBundle_samp_eval
    (s : SMSamp)
    (z : ((smIface Unit (Fig8St Pt) Unit (LibsignalMsgPublicPart × Plain ℓ)
      (BitVec 256) Unit (Fig8C Pt)).smp.sDom s).denote) :
    ((smPureAuxBundle ℓ Pt C Dh encPt encT lam).sampMacro s).eval
      (.cons (toVal (fSortSM ℓ Pt) (toDenSM ℓ Pt)
        ((smIface Unit (Fig8St Pt) Unit (LibsignalMsgPublicPart × Plain ℓ)
          (BitVec 256) Unit (Fig8C Pt)).smp.sDom s) z)
        (.cons (idOf .A, idOf .B) .nil)) =
      toVal (fSortSM ℓ Pt) (toDenSM ℓ Pt)
        ((smIface Unit (Fig8St Pt) Unit (LibsignalMsgPublicPart × Plain ℓ)
          (BitVec 256) Unit (Fig8C Pt)).smp.sTy s) <$>
        (smIface Unit (Fig8St Pt) Unit (LibsignalMsgPublicPart × Plain ℓ)
          (BitVec 256) Unit (Fig8C Pt)).liftP
          ((smIface Unit (Fig8St Pt) Unit (LibsignalMsgPublicPart × Plain ℓ)
            (BitVec 256) Unit (Fig8C Pt)).smp.samp s z) := by
  cases s with
  | bit =>
    change (fig8SmIface ℓ Pt).liftP ($ᵗ Bool) = (id : Bool → Bool) <$> _
    rw [id_map]
    exact liftP_congr (fig8SmIface ℓ Pt) _ (fun _ => rfl) _
  | key | coins | rcoins => rfl

theorem smDFPureAuxBundle_samp_eval
    (s : SMSamp)
    (z : ((smIfaceDF Unit (Fig8St Pt) Unit (LibsignalMsgPublicPart × Plain ℓ)
      (BitVec 256) Unit (Fig8C Pt)).smp.sDom s).denote) :
    ((smDFPureAuxBundle ℓ Pt C Dh encPt encT lam).sampMacro s).eval
      (.cons (toVal (fSortSM ℓ Pt) (toDenSM ℓ Pt)
        ((smIfaceDF Unit (Fig8St Pt) Unit (LibsignalMsgPublicPart × Plain ℓ)
          (BitVec 256) Unit (Fig8C Pt)).smp.sDom s) z)
        (.cons (idOf .A, idOf .B) .nil)) =
      toVal (fSortSM ℓ Pt) (toDenSM ℓ Pt)
        ((smIfaceDF Unit (Fig8St Pt) Unit (LibsignalMsgPublicPart × Plain ℓ)
          (BitVec 256) Unit (Fig8C Pt)).smp.sTy s) <$>
        (smIfaceDF Unit (Fig8St Pt) Unit (LibsignalMsgPublicPart × Plain ℓ)
          (BitVec 256) Unit (Fig8C Pt)).liftP
          ((smIfaceDF Unit (Fig8St Pt) Unit (LibsignalMsgPublicPart × Plain ℓ)
            (BitVec 256) Unit (Fig8C Pt)).smp.samp s z) := by
  cases s with
  | bit =>
    change (fig8SmIfaceDF ℓ Pt).liftP ($ᵗ Bool) = (id : Bool → Bool) <$> _
    rw [id_map]
    exact liftP_congr (fig8SmIfaceDF ℓ Pt) _ (fun _ => rfl) _
  | key | coins | rcoins => rfl

theorem smPureAuxBundle_query_eval
    (g : (smIface Unit (Fig8St Pt) Unit (LibsignalMsgPublicPart × Plain ℓ)
      (BitVec 256) Unit (Fig8C Pt)).Tag)
    (z : ((smIface Unit (Fig8St Pt) Unit (LibsignalMsgPublicPart × Plain ℓ)
      (BitVec 256) Unit (Fig8C Pt)).dom g).denote) :
    ((smPureAuxBundle ℓ Pt C Dh encPt encT lam).queryMacro g).eval
      (.cons (toVal (fSortSM ℓ Pt) (toDenSM ℓ Pt)
        ((smIface Unit (Fig8St Pt) Unit (LibsignalMsgPublicPart × Plain ℓ)
          (BitVec 256) Unit (Fig8C Pt)).dom g) z)
        (.cons (idOf .A, idOf .B) .nil)) =
      toVal (fSortSM ℓ Pt) (toDenSM ℓ Pt)
        ((smIface Unit (Fig8St Pt) Unit (LibsignalMsgPublicPart × Plain ℓ)
          (BitVec 256) Unit (Fig8C Pt)).cod g) <$>
        ((smIface Unit (Fig8St Pt) Unit (LibsignalMsgPublicPart × Plain ℓ)
          (BitVec 256) Unit (Fig8C Pt)).dec g z <$>
          (liftM (OracleSpec.query
            (spec := unifSpec + CryptoGames.SM.spec (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ)
              (BitVec 256) (Fig8C Pt))
            ((smIface Unit (Fig8St Pt) Unit (LibsignalMsgPublicPart × Plain ℓ)
              (BitVec 256) Unit (Fig8C Pt)).enc g z)) :
            OracleComp (unifSpec + CryptoGames.SM.spec (Fig8St Pt)
              (LibsignalMsgPublicPart × Plain ℓ) (BitVec 256) (Fig8C Pt)) _)) := by
  cases g with
  | tr =>
    rcases z with ⟨p, ⟨pub, m⟩, _ | r⟩ <;>
      (dsimp only [smPureAuxBundle, Comp.eval, Expr.eval, Option.map, fig8SmIface,
        smIface, toVal, toDenSM]
       simp only [env_get_zero, Functor.map_map]
       rw [boolToParty_eq_partyDec, lpubOfV_lpubV])
  | ch =>
    rcases z with ⟨p, ⟨pub0, m0⟩, ⟨pub1, m1⟩, _ | r⟩ <;>
      (dsimp only [smPureAuxBundle, Comp.eval, Expr.eval, Option.map, fig8SmIface,
        smIface, toVal, toDenSM]
       simp only [env_get_zero, Functor.map_map]
       rw [boolToParty_eq_partyDec, lpubOfV_lpubV pub0, lpubOfV_lpubV pub1])
  | dl | ij =>
    rcases z with ⟨p, c⟩
    dsimp only [smPureAuxBundle, Comp.eval, Expr.eval, fig8SmIface, smIface,
      toVal, toDenSM]
    simp only [env_get_zero, Functor.map_map]
    rw [boolToParty_eq_partyDec, fig8CtOfV_fig8CtV]
    congr 1; funext r; cases r <;> simp [toVal, toDenSM, smRrEnc_eq_toVal_smRrEnc]
  | cr =>
    dsimp only [smPureAuxBundle, Comp.eval, Expr.eval, fig8SmIface, smIface,
      toVal, toDenSM]
    simp only [env_get_zero, Functor.map_map]
    rw [boolToParty_eq_partyDec]

theorem smDFPureAuxBundle_query_eval
    (g : (smIfaceDF Unit (Fig8St Pt) Unit (LibsignalMsgPublicPart × Plain ℓ)
      (BitVec 256) Unit (Fig8C Pt)).Tag)
    (z : ((smIfaceDF Unit (Fig8St Pt) Unit (LibsignalMsgPublicPart × Plain ℓ)
      (BitVec 256) Unit (Fig8C Pt)).dom g).denote) :
    ((smDFPureAuxBundle ℓ Pt C Dh encPt encT lam).queryMacro g).eval
      (.cons (toVal (fSortSM ℓ Pt) (toDenSM ℓ Pt)
        ((smIfaceDF Unit (Fig8St Pt) Unit (LibsignalMsgPublicPart × Plain ℓ)
          (BitVec 256) Unit (Fig8C Pt)).dom g) z)
        (.cons (idOf .A, idOf .B) .nil)) =
      toVal (fSortSM ℓ Pt) (toDenSM ℓ Pt)
        ((smIfaceDF Unit (Fig8St Pt) Unit (LibsignalMsgPublicPart × Plain ℓ)
          (BitVec 256) Unit (Fig8C Pt)).cod g) <$>
        ((smIfaceDF Unit (Fig8St Pt) Unit (LibsignalMsgPublicPart × Plain ℓ)
          (BitVec 256) Unit (Fig8C Pt)).dec g z <$>
          (liftM (OracleSpec.query
            (spec := unifSpec + CryptoGames.SM.specDF (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ)
              (BitVec 256) (Fig8C Pt))
            ((smIfaceDF Unit (Fig8St Pt) Unit (LibsignalMsgPublicPart × Plain ℓ)
              (BitVec 256) Unit (Fig8C Pt)).enc g z)) :
            OracleComp (unifSpec + CryptoGames.SM.specDF (Fig8St Pt)
              (LibsignalMsgPublicPart × Plain ℓ) (BitVec 256) (Fig8C Pt)) _)) := by
  cases g with
  | tr =>
    rcases z with ⟨p, ⟨pub, m⟩, _ | r⟩ <;>
      (dsimp only [smDFPureAuxBundle, Comp.eval, Expr.eval, Option.map, fig8SmIfaceDF,
        smIfaceDF, toVal, toDenSM]
       simp only [env_get_zero, Functor.map_map]
       rw [boolToParty_eq_partyDec, lpubOfV_lpubV])
  | ch =>
    rcases z with ⟨p, ⟨pub0, m0⟩, ⟨pub1, m1⟩, _ | r⟩ <;>
      (dsimp only [smDFPureAuxBundle, Comp.eval, Expr.eval, Option.map, fig8SmIfaceDF,
        smIfaceDF, toVal, toDenSM]
       simp only [env_get_zero, Functor.map_map]
       rw [boolToParty_eq_partyDec, lpubOfV_lpubV pub0, lpubOfV_lpubV pub1])
  | dl | ij =>
    rcases z with ⟨p, c⟩
    dsimp only [smDFPureAuxBundle, Comp.eval, Expr.eval, fig8SmIfaceDF, smIfaceDF,
      toVal, toDenSM]
    simp only [env_get_zero, Functor.map_map]
    rw [boolToParty_eq_partyDec, fig8CtOfV_fig8CtV]
    congr 1; funext r; cases r <;> simp [toVal, toDenSM, smRrEnc_eq_toVal_smRrEnc]
  | cr =>
    dsimp only [smDFPureAuxBundle, Comp.eval, Expr.eval, fig8SmIfaceDF, smIfaceDF,
      toVal, toDenSM]
    simp only [env_get_zero, Functor.map_map]
    rw [boolToParty_eq_partyDec]
  | df =>
    rcases z with ⟨p, c1, c2⟩
    dsimp only [smDFPureAuxBundle, Comp.eval, Expr.eval, fig8SmIfaceDF, smIfaceDF,
      toVal, toDenSM]
    simp only [env_get_zero, Functor.map_map]
    rw [boolToParty_eq_partyDec, fig8CtOfV_fig8CtV c1, fig8CtOfV_fig8CtV c2]
    congr 1; funext r; cases r <;> simp [toVal, toDenSM, smRrEnc_eq_toVal_smRrEnc]

omit [SampleableType Pt] in
theorem ckaOpMacro_eval (B0 : ℕ) (o : CKAOp)
    (z : ((fig8CkaOpsShallow ℓ Pt C Dh encPt encT idOf lam B0).dom o).denote) :
    (ckaOpMacro ℓ Pt C Dh encPt encT idOf lam B0 o).eval
      (.cons (toVal (fSortCKA ℓ Pt) (toDenCKA ℓ Pt)
        ((fig8CkaOpsShallow ℓ Pt C Dh encPt encT idOf lam B0).dom o) z)
        (.cons (idOf .A, idOf .B) .nil)) =
      toVal (fSortCKA ℓ Pt) (toDenCKA ℓ Pt)
        ((fig8CkaOpsShallow ℓ Pt C Dh encPt encT idOf lam B0).cod o)
        ((fig8CkaOpsShallow ℓ Pt C Dh encPt encT idOf lam B0).eval o z) := by
  cases o with
  | ckaInitA => exact ckaInitAExpr_eval ℓ Pt C Dh encPt encT lam idOf z
  | ckaInitB => exact ckaInitBExpr_eval ℓ Pt C Dh encPt encT lam idOf z
  | prngInit => exact prngInitExpr_eval ℓ Pt C Dh encPt encT lam idOf z
  | lamI => exact lamIExpr_eval ℓ Pt C Dh encPt encT lam idOf
  | ckaSend =>
    rcases z with ⟨γ, x⟩
    exact ckaSendExpr_eval ℓ Pt C Dh encPt encT lam idOf γ x
  | ckaReceive =>
    rcases z with ⟨γ, t⟩
    exact ckaRecvExpr_eval ℓ Pt C Dh encPt encT lam idOf γ t
  | prngUp =>
    rcases z with ⟨σ, I⟩
    exact prngUpExpr_eval ℓ Pt C Dh encPt encT lam idOf σ I
  | fsInitSender => rfl
  | fsInitReceiver => exact fsInitRecvExpr_eval ℓ Pt C Dh encPt encT lam idOf B0 z
  | fsSend =>
    rcases z with ⟨ss, ⟨ep, _ | T⟩, p, m⟩
    · exact fsSendExpr_eval ℓ Pt C Dh encPt encT lam idOf B0 ss (ep, none) p m
    · exact fsSendExpr_eval ℓ Pt C Dh encPt encT lam idOf B0 ss (ep, some T) p m
  | fsReceive B =>
    rcases z with ⟨rs, ⟨ep, _ | T⟩, c⟩
    · have hr := fsRecvExpr_eval ℓ Pt C Dh encPt encT lam idOf B0 B rs (ep, none) c
      dsimp only [ckaOpMacro, fig8CkaOpsShallow, ckaSchemeOps, ckaOps, toVal, toDenCKA, Option.map]
      rw [hr]
      rcases (fsAtomicB C ℓ encT idOf B0).receive rs (ep, none) c with _ | ⟨rs', idx, p, m⟩ <;> rfl
    · have hr := fsRecvExpr_eval ℓ Pt C Dh encPt encT lam idOf B0 B rs (ep, some T) c
      dsimp only [ckaOpMacro, fig8CkaOpsShallow, ckaSchemeOps, ckaOps, toVal, toDenCKA, Option.map]
      rw [hr]
      rcases (fsAtomicB C ℓ encT idOf B0).receive rs (ep, some T) c with _ | ⟨rs', idx, p, m⟩ <;> rfl
  | eqT | eqI =>
    rcases z with ⟨a, b⟩
    exact eqPtExpr_eval ℓ Pt C Dh encPt encT lam idOf a b
  | eqM =>
    rcases z with ⟨⟨p1, m1⟩, ⟨p2, m2⟩⟩
    exact eqMExpr_eval ℓ Pt C Dh encPt encT lam idOf (p1, m1) (p2, m2)
  | eqE =>
    rcases z with ⟨e1, e2⟩
    exact eqEExpr_eval ℓ Pt C Dh encPt encT lam idOf e1 e2
  | defaultE =>
    exact defaultEExpr_eval ℓ Pt C Dh encPt encT lam idOf

theorem ckaPureAuxBundle_samp_eval_atomic (B0 : ℕ) (s : CKASamp)
    (z : ((ckaIface (BitVec 256) (CryptoGames.CKA.DDH.State (BitVec 256) Pt) (BitVec 256) Pt Pt
      (BitVec 256) (BitVec 256) (BitVec 256)
      (RatchetSenderState (BitVec 256)) (RatchetReceiverState (BitVec 256) (BitVec 256))
      (LibsignalMsgPublicPart × Plain ℓ) (ℕ × LibsignalCiphertextWithSalt32)
      sampBV256Atomic sampBV256Atomic sampBV256Atomic ($ᵗ Pt) sampBV256Atomic).smp.sDom s).denote) :
    ((ckaPureAuxBundle ℓ Pt C Dh encPt encT idOf lam B0 sampBV256Atomic).sampMacro s).eval
      (.cons (toVal (fSortCKA ℓ Pt) (toDenCKA ℓ Pt) _ z) (.cons (idOf .A, idOf .B) .nil)) =
      toVal (fSortCKA ℓ Pt) (toDenCKA ℓ Pt)
        ((ckaIface (BitVec 256) (CryptoGames.CKA.DDH.State (BitVec 256) Pt) (BitVec 256) Pt Pt
          (BitVec 256) (BitVec 256) (BitVec 256)
          (RatchetSenderState (BitVec 256)) (RatchetReceiverState (BitVec 256) (BitVec 256))
          (LibsignalMsgPublicPart × Plain ℓ) (ℕ × LibsignalCiphertextWithSalt32)
          sampBV256Atomic sampBV256Atomic sampBV256Atomic ($ᵗ Pt) sampBV256Atomic).smp.sTy s) <$>
        (ckaIface (BitVec 256) (CryptoGames.CKA.DDH.State (BitVec 256) Pt) (BitVec 256) Pt Pt
          (BitVec 256) (BitVec 256) (BitVec 256)
          (RatchetSenderState (BitVec 256)) (RatchetReceiverState (BitVec 256) (BitVec 256))
          (LibsignalMsgPublicPart × Plain ℓ) (ℕ × LibsignalCiphertextWithSalt32)
          sampBV256Atomic sampBV256Atomic sampBV256Atomic ($ᵗ Pt) sampBV256Atomic).liftP
          ((ckaIface (BitVec 256) (CryptoGames.CKA.DDH.State (BitVec 256) Pt) (BitVec 256) Pt Pt
            (BitVec 256) (BitVec 256) (BitVec 256)
            (RatchetSenderState (BitVec 256)) (RatchetReceiverState (BitVec 256) (BitVec 256))
            (LibsignalMsgPublicPart × Plain ℓ) (ℕ × LibsignalCiphertextWithSalt32)
            sampBV256Atomic sampBV256Atomic sampBV256Atomic ($ᵗ Pt) sampBV256Atomic).smp.samp s z) := by
  cases s <;>
    exact (liftP_congr (ckaTargetIface ℓ Pt) _ (fun _ => rfl) _).trans (id_map _).symm

theorem ckaPureAuxBundle_samp_coinSimEquiv (B0 : ℕ) (s : CKASamp)
    (z : ((ckaIface (BitVec 256) (CryptoGames.CKA.DDH.State (BitVec 256) Pt) (BitVec 256) Pt Pt
      (BitVec 256) (BitVec 256) (BitVec 256)
      (RatchetSenderState (BitVec 256)) (RatchetReceiverState (BitVec 256) (BitVec 256))
      (LibsignalMsgPublicPart × Plain ℓ) (ℕ × LibsignalCiphertextWithSalt32)
      ($ᵗ (BitVec 256)) ($ᵗ (BitVec 256)) ($ᵗ (BitVec 256)) ($ᵗ Pt) ($ᵗ (BitVec 256))).smp.sDom s).denote) :
    CoinSimEquiv (ckaTargetIface ℓ Pt).fwdU
      (((ckaPureAuxBundle ℓ Pt C Dh encPt encT idOf lam B0 ($ᵗ (BitVec 256))).sampMacro s).eval
        (.cons (toVal (fSortCKA ℓ Pt) (toDenCKA ℓ Pt) _ z) (.cons (idOf .A, idOf .B) .nil)))
      (toVal (fSortCKA ℓ Pt) (toDenCKA ℓ Pt)
        ((ckaIface (BitVec 256) (CryptoGames.CKA.DDH.State (BitVec 256) Pt) (BitVec 256) Pt Pt
          (BitVec 256) (BitVec 256) (BitVec 256)
          (RatchetSenderState (BitVec 256)) (RatchetReceiverState (BitVec 256) (BitVec 256))
          (LibsignalMsgPublicPart × Plain ℓ) (ℕ × LibsignalCiphertextWithSalt32)
          ($ᵗ (BitVec 256)) ($ᵗ (BitVec 256)) ($ᵗ (BitVec 256)) ($ᵗ Pt) ($ᵗ (BitVec 256))).smp.sTy s) <$>
        (ckaIface (BitVec 256) (CryptoGames.CKA.DDH.State (BitVec 256) Pt) (BitVec 256) Pt Pt
          (BitVec 256) (BitVec 256) (BitVec 256)
          (RatchetSenderState (BitVec 256)) (RatchetReceiverState (BitVec 256) (BitVec 256))
          (LibsignalMsgPublicPart × Plain ℓ) (ℕ × LibsignalCiphertextWithSalt32)
          ($ᵗ (BitVec 256)) ($ᵗ (BitVec 256)) ($ᵗ (BitVec 256)) ($ᵗ Pt) ($ᵗ (BitVec 256))).liftP
          ((ckaIface (BitVec 256) (CryptoGames.CKA.DDH.State (BitVec 256) Pt) (BitVec 256) Pt Pt
            (BitVec 256) (BitVec 256) (BitVec 256)
            (RatchetSenderState (BitVec 256)) (RatchetReceiverState (BitVec 256) (BitVec 256))
            (LibsignalMsgPublicPart × Plain ℓ) (ℕ × LibsignalCiphertextWithSalt32)
            ($ᵗ (BitVec 256)) ($ᵗ (BitVec 256)) ($ᵗ (BitVec 256)) ($ᵗ Pt) ($ᵗ (BitVec 256))).smp.samp s z)) := by
  cases s with
  | bit | i =>
    apply CoinSimEquiv.of_eq
    exact (liftP_congr (ckaTargetIface ℓ Pt) _ (fun _ => rfl) _).trans (id_map _).symm
  | kr | kc | ccoins | k =>
    change CoinSimEquiv (ckaTargetIface ℓ Pt).fwdU
      ((ckaTargetIface ℓ Pt).liftP sampBV256Atomic) (id <$> _)
    rw [id_map, ← liftP_congr (ckaTargetIface ℓ Pt) _ (fun _ => rfl)]
    exact coinSimEquiv_liftP (ckaTargetIface ℓ Pt) sampBV256Atomic_evalDistEq

theorem prngPureAuxBundle_samp_eval_atomic (B0 : ℕ) (s : CKASamp)
    (z : ((prngIface (BitVec 256) (CryptoGames.CKA.DDH.State (BitVec 256) Pt) (BitVec 256) Pt Pt
      (BitVec 256) (BitVec 256) (BitVec 256)
      (RatchetSenderState (BitVec 256)) (RatchetReceiverState (BitVec 256) (BitVec 256))
      (LibsignalMsgPublicPart × Plain ℓ) (ℕ × LibsignalCiphertextWithSalt32)
      sampBV256Atomic sampBV256Atomic sampBV256Atomic ($ᵗ Pt) sampBV256Atomic).smp.sDom s).denote) :
    ((prngPureAuxBundle ℓ Pt C Dh encPt encT idOf lam B0 sampBV256Atomic).sampMacro s).eval
      (.cons (toVal (fSortCKA ℓ Pt) (toDenCKA ℓ Pt) _ z) (.cons (idOf .A, idOf .B) .nil)) =
      toVal (fSortCKA ℓ Pt) (toDenCKA ℓ Pt)
        ((prngIface (BitVec 256) (CryptoGames.CKA.DDH.State (BitVec 256) Pt) (BitVec 256) Pt Pt
          (BitVec 256) (BitVec 256) (BitVec 256)
          (RatchetSenderState (BitVec 256)) (RatchetReceiverState (BitVec 256) (BitVec 256))
          (LibsignalMsgPublicPart × Plain ℓ) (ℕ × LibsignalCiphertextWithSalt32)
          sampBV256Atomic sampBV256Atomic sampBV256Atomic ($ᵗ Pt) sampBV256Atomic).smp.sTy s) <$>
        (prngIface (BitVec 256) (CryptoGames.CKA.DDH.State (BitVec 256) Pt) (BitVec 256) Pt Pt
          (BitVec 256) (BitVec 256) (BitVec 256)
          (RatchetSenderState (BitVec 256)) (RatchetReceiverState (BitVec 256) (BitVec 256))
          (LibsignalMsgPublicPart × Plain ℓ) (ℕ × LibsignalCiphertextWithSalt32)
          sampBV256Atomic sampBV256Atomic sampBV256Atomic ($ᵗ Pt) sampBV256Atomic).liftP
          ((prngIface (BitVec 256) (CryptoGames.CKA.DDH.State (BitVec 256) Pt) (BitVec 256) Pt Pt
            (BitVec 256) (BitVec 256) (BitVec 256)
            (RatchetSenderState (BitVec 256)) (RatchetReceiverState (BitVec 256) (BitVec 256))
            (LibsignalMsgPublicPart × Plain ℓ) (ℕ × LibsignalCiphertextWithSalt32)
            sampBV256Atomic sampBV256Atomic sampBV256Atomic ($ᵗ Pt) sampBV256Atomic).smp.samp s z) := by
  cases s <;>
    exact (liftP_congr (prngTargetIface ℓ Pt) _ (fun _ => rfl) _).trans (id_map _).symm

theorem prngPureAuxBundle_samp_coinSimEquiv (B0 : ℕ) (s : CKASamp)
    (z : ((prngIface (BitVec 256) (CryptoGames.CKA.DDH.State (BitVec 256) Pt) (BitVec 256) Pt Pt
      (BitVec 256) (BitVec 256) (BitVec 256)
      (RatchetSenderState (BitVec 256)) (RatchetReceiverState (BitVec 256) (BitVec 256))
      (LibsignalMsgPublicPart × Plain ℓ) (ℕ × LibsignalCiphertextWithSalt32)
      ($ᵗ (BitVec 256)) ($ᵗ (BitVec 256)) ($ᵗ (BitVec 256)) ($ᵗ Pt) ($ᵗ (BitVec 256))).smp.sDom s).denote) :
    CoinSimEquiv (prngTargetIface ℓ Pt).fwdU
      (((prngPureAuxBundle ℓ Pt C Dh encPt encT idOf lam B0 ($ᵗ (BitVec 256))).sampMacro s).eval
        (.cons (toVal (fSortCKA ℓ Pt) (toDenCKA ℓ Pt) _ z) (.cons (idOf .A, idOf .B) .nil)))
      (toVal (fSortCKA ℓ Pt) (toDenCKA ℓ Pt)
        ((prngIface (BitVec 256) (CryptoGames.CKA.DDH.State (BitVec 256) Pt) (BitVec 256) Pt Pt
          (BitVec 256) (BitVec 256) (BitVec 256)
          (RatchetSenderState (BitVec 256)) (RatchetReceiverState (BitVec 256) (BitVec 256))
          (LibsignalMsgPublicPart × Plain ℓ) (ℕ × LibsignalCiphertextWithSalt32)
          ($ᵗ (BitVec 256)) ($ᵗ (BitVec 256)) ($ᵗ (BitVec 256)) ($ᵗ Pt) ($ᵗ (BitVec 256))).smp.sTy s) <$>
        (prngIface (BitVec 256) (CryptoGames.CKA.DDH.State (BitVec 256) Pt) (BitVec 256) Pt Pt
          (BitVec 256) (BitVec 256) (BitVec 256)
          (RatchetSenderState (BitVec 256)) (RatchetReceiverState (BitVec 256) (BitVec 256))
          (LibsignalMsgPublicPart × Plain ℓ) (ℕ × LibsignalCiphertextWithSalt32)
          ($ᵗ (BitVec 256)) ($ᵗ (BitVec 256)) ($ᵗ (BitVec 256)) ($ᵗ Pt) ($ᵗ (BitVec 256))).liftP
          ((prngIface (BitVec 256) (CryptoGames.CKA.DDH.State (BitVec 256) Pt) (BitVec 256) Pt Pt
            (BitVec 256) (BitVec 256) (BitVec 256)
            (RatchetSenderState (BitVec 256)) (RatchetReceiverState (BitVec 256) (BitVec 256))
            (LibsignalMsgPublicPart × Plain ℓ) (ℕ × LibsignalCiphertextWithSalt32)
            ($ᵗ (BitVec 256)) ($ᵗ (BitVec 256)) ($ᵗ (BitVec 256)) ($ᵗ Pt) ($ᵗ (BitVec 256))).smp.samp s z)) := by
  cases s with
  | bit | i =>
    apply CoinSimEquiv.of_eq
    exact (liftP_congr (prngTargetIface ℓ Pt) _ (fun _ => rfl) _).trans (id_map _).symm
  | kr | kc | ccoins | k =>
    change CoinSimEquiv (prngTargetIface ℓ Pt).fwdU
      ((prngTargetIface ℓ Pt).liftP sampBV256Atomic) (id <$> _)
    rw [id_map, ← liftP_congr (prngTargetIface ℓ Pt) _ (fun _ => rfl)]
    exact coinSimEquiv_liftP (prngTargetIface ℓ Pt) sampBV256Atomic_evalDistEq

theorem fsPureAuxBundle_samp_eval_atomic (B0 : ℕ) (s : CKASamp)
    (z : ((fsaeadHeaderAdIface (BitVec 256) (CryptoGames.CKA.DDH.State (BitVec 256) Pt)
      (BitVec 256) Pt Pt (BitVec 256) (BitVec 256) (BitVec 256)
      (RatchetSenderState (BitVec 256)) (RatchetReceiverState (BitVec 256) (BitVec 256))
      (LibsignalMsgPublicPart × Plain ℓ) (ℕ × LibsignalCiphertextWithSalt32)
      sampBV256Atomic sampBV256Atomic sampBV256Atomic ($ᵗ Pt) sampBV256Atomic).smp.sDom s).denote) :
    ((fsPureAuxBundle ℓ Pt C Dh encPt encT idOf lam B0 sampBV256Atomic).sampMacro s).eval
      (.cons (toVal (fSortCKA ℓ Pt) (toDenCKA ℓ Pt) _ z) (.cons (idOf .A, idOf .B) .nil)) =
      toVal (fSortCKA ℓ Pt) (toDenCKA ℓ Pt)
        ((fsaeadHeaderAdIface (BitVec 256) (CryptoGames.CKA.DDH.State (BitVec 256) Pt)
          (BitVec 256) Pt Pt (BitVec 256) (BitVec 256) (BitVec 256)
          (RatchetSenderState (BitVec 256)) (RatchetReceiverState (BitVec 256) (BitVec 256))
          (LibsignalMsgPublicPart × Plain ℓ) (ℕ × LibsignalCiphertextWithSalt32)
          sampBV256Atomic sampBV256Atomic sampBV256Atomic ($ᵗ Pt) sampBV256Atomic).smp.sTy s) <$>
        (fsaeadHeaderAdIface (BitVec 256) (CryptoGames.CKA.DDH.State (BitVec 256) Pt)
          (BitVec 256) Pt Pt (BitVec 256) (BitVec 256) (BitVec 256)
          (RatchetSenderState (BitVec 256)) (RatchetReceiverState (BitVec 256) (BitVec 256))
          (LibsignalMsgPublicPart × Plain ℓ) (ℕ × LibsignalCiphertextWithSalt32)
          sampBV256Atomic sampBV256Atomic sampBV256Atomic ($ᵗ Pt) sampBV256Atomic).liftP
          ((fsaeadHeaderAdIface (BitVec 256) (CryptoGames.CKA.DDH.State (BitVec 256) Pt)
            (BitVec 256) Pt Pt (BitVec 256) (BitVec 256) (BitVec 256)
            (RatchetSenderState (BitVec 256)) (RatchetReceiverState (BitVec 256) (BitVec 256))
            (LibsignalMsgPublicPart × Plain ℓ) (ℕ × LibsignalCiphertextWithSalt32)
            sampBV256Atomic sampBV256Atomic sampBV256Atomic ($ᵗ Pt) sampBV256Atomic).smp.samp s z) := by
  cases s <;>
    exact (liftP_congr (fsaeadHeaderIface ℓ Pt) _ (fun _ => rfl) _).trans (id_map _).symm

theorem fsPureAuxBundle_samp_coinSimEquiv (B0 : ℕ) (s : CKASamp)
    (z : ((fsaeadHeaderAdIface (BitVec 256) (CryptoGames.CKA.DDH.State (BitVec 256) Pt)
      (BitVec 256) Pt Pt (BitVec 256) (BitVec 256) (BitVec 256)
      (RatchetSenderState (BitVec 256)) (RatchetReceiverState (BitVec 256) (BitVec 256))
      (LibsignalMsgPublicPart × Plain ℓ) (ℕ × LibsignalCiphertextWithSalt32)
      ($ᵗ (BitVec 256)) ($ᵗ (BitVec 256)) ($ᵗ (BitVec 256)) ($ᵗ Pt) ($ᵗ (BitVec 256))).smp.sDom s).denote) :
    CoinSimEquiv (fsaeadHeaderIface ℓ Pt).fwdU
      (((fsPureAuxBundle ℓ Pt C Dh encPt encT idOf lam B0 ($ᵗ (BitVec 256))).sampMacro s).eval
        (.cons (toVal (fSortCKA ℓ Pt) (toDenCKA ℓ Pt) _ z) (.cons (idOf .A, idOf .B) .nil)))
      (toVal (fSortCKA ℓ Pt) (toDenCKA ℓ Pt)
        ((fsaeadHeaderAdIface (BitVec 256) (CryptoGames.CKA.DDH.State (BitVec 256) Pt)
          (BitVec 256) Pt Pt (BitVec 256) (BitVec 256) (BitVec 256)
          (RatchetSenderState (BitVec 256)) (RatchetReceiverState (BitVec 256) (BitVec 256))
          (LibsignalMsgPublicPart × Plain ℓ) (ℕ × LibsignalCiphertextWithSalt32)
          ($ᵗ (BitVec 256)) ($ᵗ (BitVec 256)) ($ᵗ (BitVec 256)) ($ᵗ Pt) ($ᵗ (BitVec 256))).smp.sTy s) <$>
        (fsaeadHeaderAdIface (BitVec 256) (CryptoGames.CKA.DDH.State (BitVec 256) Pt)
          (BitVec 256) Pt Pt (BitVec 256) (BitVec 256) (BitVec 256)
          (RatchetSenderState (BitVec 256)) (RatchetReceiverState (BitVec 256) (BitVec 256))
          (LibsignalMsgPublicPart × Plain ℓ) (ℕ × LibsignalCiphertextWithSalt32)
          ($ᵗ (BitVec 256)) ($ᵗ (BitVec 256)) ($ᵗ (BitVec 256)) ($ᵗ Pt) ($ᵗ (BitVec 256))).liftP
          ((fsaeadHeaderAdIface (BitVec 256) (CryptoGames.CKA.DDH.State (BitVec 256) Pt)
            (BitVec 256) Pt Pt (BitVec 256) (BitVec 256) (BitVec 256)
            (RatchetSenderState (BitVec 256)) (RatchetReceiverState (BitVec 256) (BitVec 256))
            (LibsignalMsgPublicPart × Plain ℓ) (ℕ × LibsignalCiphertextWithSalt32)
            ($ᵗ (BitVec 256)) ($ᵗ (BitVec 256)) ($ᵗ (BitVec 256)) ($ᵗ Pt) ($ᵗ (BitVec 256))).smp.samp s z)) := by
  cases s with
  | bit | i =>
    apply CoinSimEquiv.of_eq
    exact (liftP_congr (fsaeadHeaderIface ℓ Pt) _ (fun _ => rfl) _).trans (id_map _).symm
  | kr | kc | ccoins | k =>
    change CoinSimEquiv (fsaeadHeaderIface ℓ Pt).fwdU
      ((fsaeadHeaderIface ℓ Pt).liftP sampBV256Atomic) (id <$> _)
    rw [id_map, ← liftP_congr (fsaeadHeaderIface ℓ Pt) _ (fun _ => rfl)]
    exact coinSimEquiv_liftP (fsaeadHeaderIface ℓ Pt) sampBV256Atomic_evalDistEq

theorem ckaPureAuxBundle_query_eval (B0 : ℕ) (sampBV : ProbComp (BitVec 256))
    (g : (ckaIface (BitVec 256) (CryptoGames.CKA.DDH.State (BitVec 256) Pt) (BitVec 256) Pt Pt
      (BitVec 256) (BitVec 256) (BitVec 256)
      (RatchetSenderState (BitVec 256)) (RatchetReceiverState (BitVec 256) (BitVec 256))
      (LibsignalMsgPublicPart × Plain ℓ) (ℕ × LibsignalCiphertextWithSalt32)
      sampBV sampBV sampBV ($ᵗ Pt) sampBV).Tag)
    (z : ((ckaIface (BitVec 256) (CryptoGames.CKA.DDH.State (BitVec 256) Pt) (BitVec 256) Pt Pt
      (BitVec 256) (BitVec 256) (BitVec 256)
      (RatchetSenderState (BitVec 256)) (RatchetReceiverState (BitVec 256) (BitVec 256))
      (LibsignalMsgPublicPart × Plain ℓ) (ℕ × LibsignalCiphertextWithSalt32)
      sampBV sampBV sampBV ($ᵗ Pt) sampBV).dom g).denote) :
    ((ckaPureAuxBundle ℓ Pt C Dh encPt encT idOf lam B0 sampBV).queryMacro g).eval
      (.cons (toVal (fSortCKA ℓ Pt) (toDenCKA ℓ Pt) _ z)
        (.cons (idOf .A, idOf .B) .nil)) =
      toVal (fSortCKA ℓ Pt) (toDenCKA ℓ Pt) _ <$>
        ((ckaIface (BitVec 256) (CryptoGames.CKA.DDH.State (BitVec 256) Pt) (BitVec 256) Pt Pt
          (BitVec 256) (BitVec 256) (BitVec 256)
          (RatchetSenderState (BitVec 256)) (RatchetReceiverState (BitVec 256) (BitVec 256))
          (LibsignalMsgPublicPart × Plain ℓ) (ℕ × LibsignalCiphertextWithSalt32)
          sampBV sampBV sampBV ($ᵗ Pt) sampBV).dec g z <$>
          (liftM (OracleSpec.query
            (spec := unifSpec + CryptoGames.CKA.spec (CryptoGames.CKA.DDH.State (BitVec 256) Pt)
              (BitVec 256) Pt Pt)
            ((ckaIface (BitVec 256) (CryptoGames.CKA.DDH.State (BitVec 256) Pt) (BitVec 256) Pt Pt
              (BitVec 256) (BitVec 256) (BitVec 256)
              (RatchetSenderState (BitVec 256)) (RatchetReceiverState (BitVec 256) (BitVec 256))
              (LibsignalMsgPublicPart × Plain ℓ) (ℕ × LibsignalCiphertextWithSalt32)
              sampBV sampBV sampBV ($ᵗ Pt) sampBV).enc g z)) :
            OracleComp (unifSpec + CryptoGames.CKA.spec
              (CryptoGames.CKA.DDH.State (BitVec 256) Pt) (BitVec 256) Pt Pt) _)) := by
  cases g with
  | send | chall | receive =>
    dsimp only [ckaPureAuxBundle, Comp.eval, Expr.eval, ckaTargetIface, ckaIface,
      toVal, toDenCKA]
    simp only [env_get_zero, Functor.map_map]
    congr 1; funext r; cases r <;> rfl
  | sendBad =>
    rcases z with ⟨p, r⟩
    dsimp only [ckaPureAuxBundle, Comp.eval, Expr.eval, ckaTargetIface, ckaIface,
      toVal, toDenCKA]
    simp only [env_get_zero, Functor.map_map]
    congr 1; funext x; cases x <;> rfl
  | corr =>
    dsimp only [ckaPureAuxBundle, Comp.eval, Expr.eval, ckaTargetIface, ckaIface,
      toVal, toDenCKA]
    simp only [env_get_zero, Functor.map_map]
    rw [boolToParty_eq_partyDec]

theorem prngPureAuxBundle_query_eval (B0 : ℕ) (sampBV : ProbComp (BitVec 256))
    (g : (prngIface (BitVec 256) (CryptoGames.CKA.DDH.State (BitVec 256) Pt) (BitVec 256) Pt Pt
      (BitVec 256) (BitVec 256) (BitVec 256)
      (RatchetSenderState (BitVec 256)) (RatchetReceiverState (BitVec 256) (BitVec 256))
      (LibsignalMsgPublicPart × Plain ℓ) (ℕ × LibsignalCiphertextWithSalt32)
      sampBV sampBV sampBV ($ᵗ Pt) sampBV).Tag)
    (z : ((prngIface (BitVec 256) (CryptoGames.CKA.DDH.State (BitVec 256) Pt) (BitVec 256) Pt Pt
      (BitVec 256) (BitVec 256) (BitVec 256)
      (RatchetSenderState (BitVec 256)) (RatchetReceiverState (BitVec 256) (BitVec 256))
      (LibsignalMsgPublicPart × Plain ℓ) (ℕ × LibsignalCiphertextWithSalt32)
      sampBV sampBV sampBV ($ᵗ Pt) sampBV).dom g).denote) :
    ((prngPureAuxBundle ℓ Pt C Dh encPt encT idOf lam B0 sampBV).queryMacro g).eval
      (.cons (toVal (fSortCKA ℓ Pt) (toDenCKA ℓ Pt) _ z)
        (.cons (idOf .A, idOf .B) .nil)) =
      toVal (fSortCKA ℓ Pt) (toDenCKA ℓ Pt) _ <$>
        ((prngIface (BitVec 256) (CryptoGames.CKA.DDH.State (BitVec 256) Pt) (BitVec 256) Pt Pt
          (BitVec 256) (BitVec 256) (BitVec 256)
          (RatchetSenderState (BitVec 256)) (RatchetReceiverState (BitVec 256) (BitVec 256))
          (LibsignalMsgPublicPart × Plain ℓ) (ℕ × LibsignalCiphertextWithSalt32)
          sampBV sampBV sampBV ($ᵗ Pt) sampBV).dec g z <$>
          (liftM (OracleSpec.query
            (spec := unifSpec + CryptoGames.PRFPRNG.spec (BitVec 256) Pt (BitVec 256))
            ((prngIface (BitVec 256) (CryptoGames.CKA.DDH.State (BitVec 256) Pt) (BitVec 256) Pt Pt
              (BitVec 256) (BitVec 256) (BitVec 256)
              (RatchetSenderState (BitVec 256)) (RatchetReceiverState (BitVec 256) (BitVec 256))
              (LibsignalMsgPublicPart × Plain ℓ) (ℕ × LibsignalCiphertextWithSalt32)
              sampBV sampBV sampBV ($ᵗ Pt) sampBV).enc g z)) :
            OracleComp (unifSpec + CryptoGames.PRFPRNG.spec (BitVec 256) Pt (BitVec 256)) _)) := by
  cases g with
  | process | challPrng =>
    cases z <;>
      (dsimp only [prngPureAuxBundle, Comp.eval, Expr.eval, Option.map, prngTargetIface,
        prngIface, toVal, toDenCKA]
       simp only [env_get_zero, Functor.map_map]
       congr 1; funext r; cases r <;> rfl)
  | challPrf | corr =>
    dsimp only [prngPureAuxBundle, Comp.eval, Expr.eval, prngTargetIface, prngIface,
      toVal, toDenCKA]
    simp only [env_get_zero, Functor.map_map]
    congr 1; funext r; cases r <;> rfl

theorem fsPureAuxBundle_query_eval (B0 : ℕ) (sampBV : ProbComp (BitVec 256))
    (g : (fsaeadHeaderAdIface (BitVec 256) (CryptoGames.CKA.DDH.State (BitVec 256) Pt)
      (BitVec 256) Pt Pt (BitVec 256) (BitVec 256) (BitVec 256)
      (RatchetSenderState (BitVec 256)) (RatchetReceiverState (BitVec 256) (BitVec 256))
      (LibsignalMsgPublicPart × Plain ℓ) (ℕ × LibsignalCiphertextWithSalt32)
      sampBV sampBV sampBV ($ᵗ Pt) sampBV).Tag)
    (z : ((fsaeadHeaderAdIface (BitVec 256) (CryptoGames.CKA.DDH.State (BitVec 256) Pt)
      (BitVec 256) Pt Pt (BitVec 256) (BitVec 256) (BitVec 256)
      (RatchetSenderState (BitVec 256)) (RatchetReceiverState (BitVec 256) (BitVec 256))
      (LibsignalMsgPublicPart × Plain ℓ) (ℕ × LibsignalCiphertextWithSalt32)
      sampBV sampBV sampBV ($ᵗ Pt) sampBV).dom g).denote) :
    ((fsPureAuxBundle ℓ Pt C Dh encPt encT idOf lam B0 sampBV).queryMacro g).eval
      (.cons (toVal (fSortCKA ℓ Pt) (toDenCKA ℓ Pt) _ z)
        (.cons (idOf .A, idOf .B) .nil)) =
      toVal (fSortCKA ℓ Pt) (toDenCKA ℓ Pt) _ <$>
        ((fsaeadHeaderAdIface (BitVec 256) (CryptoGames.CKA.DDH.State (BitVec 256) Pt)
          (BitVec 256) Pt Pt (BitVec 256) (BitVec 256) (BitVec 256)
          (RatchetSenderState (BitVec 256)) (RatchetReceiverState (BitVec 256) (BitVec 256))
          (LibsignalMsgPublicPart × Plain ℓ) (ℕ × LibsignalCiphertextWithSalt32)
          sampBV sampBV sampBV ($ᵗ Pt) sampBV).dec g z <$>
          (liftM (OracleSpec.query
            (spec := unifSpec + CryptoGames.FSAEAD.spec (RatchetSenderState (BitVec 256))
              (RatchetReceiverState (BitVec 256) (BitVec 256))
              (CryptoGames.SM.Construction.Header Pt) (LibsignalMsgPublicPart × Plain ℓ)
              (ℕ × LibsignalCiphertextWithSalt32))
            ((fsaeadHeaderAdIface (BitVec 256) (CryptoGames.CKA.DDH.State (BitVec 256) Pt)
              (BitVec 256) Pt Pt (BitVec 256) (BitVec 256) (BitVec 256)
              (RatchetSenderState (BitVec 256)) (RatchetReceiverState (BitVec 256) (BitVec 256))
              (LibsignalMsgPublicPart × Plain ℓ) (ℕ × LibsignalCiphertextWithSalt32)
              sampBV sampBV sampBV ($ᵗ Pt) sampBV).enc g z)) :
            OracleComp (unifSpec + CryptoGames.FSAEAD.spec (RatchetSenderState (BitVec 256))
              (RatchetReceiverState (BitVec 256) (BitVec 256))
              (CryptoGames.SM.Construction.Header Pt) (LibsignalMsgPublicPart × Plain ℓ)
              (ℕ × LibsignalCiphertextWithSalt32)) _)) := by
  cases g with
  | tr =>
    rcases z with ⟨⟨ep, _ | T⟩, pub, m⟩ <;>
      (dsimp only [fsPureAuxBundle, Comp.eval, Expr.eval, Option.map, fsaeadHeaderIface,
        fsaeadHeaderAdIface, toVal, toDenCKA]
       simp only [env_get_zero, Functor.map_map]
       rw [lpubOfV_lpubV])
  | ch =>
    rcases z with ⟨⟨ep, _ | T⟩, ⟨pub0, m0⟩, ⟨pub1, m1⟩⟩ <;>
      (dsimp only [fsPureAuxBundle, Comp.eval, Expr.eval, Option.map, fsaeadHeaderIface,
        fsaeadHeaderAdIface, toVal, toDenCKA]
       simp only [env_get_zero, Functor.map_map]
       rw [lpubOfV_lpubV pub0, lpubOfV_lpubV pub1])
  | cs =>
    dsimp only [fsPureAuxBundle, Comp.eval, Expr.eval, fsaeadHeaderIface,
      fsaeadHeaderAdIface, toVal, toDenCKA]
    simp only [Functor.map_map]
  | cr =>
    dsimp only [fsPureAuxBundle, Comp.eval, Expr.eval, fsaeadHeaderIface,
      fsaeadHeaderAdIface, toVal, toDenCKA]
    simp only [Functor.map_map]
  | dl | ij =>
    rcases z with ⟨⟨ep, _ | T⟩, c⟩ <;>
      (dsimp only [fsPureAuxBundle, Comp.eval, Expr.eval, Option.map, fsaeadHeaderIface,
        fsaeadHeaderAdIface, toVal, toDenCKA]
       simp only [env_get_zero, Functor.map_map]
       rw [lctOfV_lctV]
       congr 1; funext r; rcases r with _ | (_ | ⟨idx, _ | ⟨pub, m⟩⟩) <;> rfl)

def compileSmAtomic
    (R : CostedReduction (fig8SmOpsShallow ℓ Pt)
      (smIface Unit (Fig8St Pt) Unit (LibsignalMsgPublicPart × Plain ℓ) (BitVec 256) Unit (Fig8C Pt))
      (CryptoGames.SM.spec (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (BitVec 256) (Fig8C Pt))
      (smCodec Unit (Fig8St Pt) Unit (LibsignalMsgPublicPart × Plain ℓ) (BitVec 256) Unit (Fig8C Pt))
      .unit .unit .bool .bool) :
    CostedReduction O₂ (fig8SmIface ℓ Pt)
      (CryptoGames.SM.spec (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (BitVec 256) (Fig8C Pt))
      (fig8SmCodec ℓ Pt) .unit .unit .bool .bool :=
  guardRed (ℓ < 10 ^ 6)
    (compilePureAuxRed (smPureAuxBundle ℓ Pt C Dh encPt encT lam)
      (smToFig8Adapters ℓ Pt C Dh encPt encT idOf lam) R)
    .unit (.inl .none) (.bool false)

def compileSmDFAtomic
    (R : CostedReduction (fig8SmOpsShallow ℓ Pt)
      (smIfaceDF Unit (Fig8St Pt) Unit (LibsignalMsgPublicPart × Plain ℓ) (BitVec 256) Unit (Fig8C Pt))
      (CryptoGames.SM.specDF (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (BitVec 256) (Fig8C Pt))
      (smCodecDF Unit (Fig8St Pt) Unit (LibsignalMsgPublicPart × Plain ℓ) (BitVec 256) Unit (Fig8C Pt))
      .unit .unit .bool .bool) :
    CostedReduction O₂ (fig8SmIfaceDF ℓ Pt)
      (CryptoGames.SM.specDF (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (BitVec 256) (Fig8C Pt))
      (fig8SmCodecDF ℓ Pt) .unit .unit .bool .bool :=
  guardRed (ℓ < 10 ^ 6)
    (compilePureAuxRed (smDFPureAuxBundle ℓ Pt C Dh encPt encT lam)
      (smDFToFig8Adapters ℓ Pt C Dh encPt encT idOf lam) R)
    .unit (.inl .none) (.bool false)

def compileCkaAtomic (B0 : ℕ)
    (R : CostedReduction (fig8CkaOpsShallow ℓ Pt C Dh encPt encT idOf lam B0)
      (ckaIface (BitVec 256) (CryptoGames.CKA.DDH.State (BitVec 256) Pt) (BitVec 256) Pt Pt
        (BitVec 256) (BitVec 256) (BitVec 256)
        (RatchetSenderState (BitVec 256)) (RatchetReceiverState (BitVec 256) (BitVec 256))
        (LibsignalMsgPublicPart × Plain ℓ) (ℕ × LibsignalCiphertextWithSalt32)
        ($ᵗ (BitVec 256)) ($ᵗ (BitVec 256)) ($ᵗ (BitVec 256)) ($ᵗ Pt) ($ᵗ (BitVec 256)))
      (CryptoGames.SM.spec (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (BitVec 256) (Fig8C Pt))
      (ckaSMCodec (BitVec 256) (CryptoGames.CKA.DDH.State (BitVec 256) Pt) (BitVec 256) Pt Pt
        (BitVec 256) (BitVec 256) (BitVec 256)
        (RatchetSenderState (BitVec 256)) (RatchetReceiverState (BitVec 256) (BitVec 256))
        (LibsignalMsgPublicPart × Plain ℓ) (ℕ × LibsignalCiphertextWithSalt32))
      .unit .unit .bool .bool) :
    CostedReduction O₂ (ckaTargetIface ℓ Pt)
      (CryptoGames.SM.spec (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (BitVec 256) (Fig8C Pt))
      (fig8SmCodec ℓ Pt) .unit .unit .bool .bool :=
  guardRed (ℓ < 10 ^ 6)
    (compilePureAuxRed (ckaPureAuxBundle ℓ Pt C Dh encPt encT idOf lam B0 ($ᵗ (BitVec 256)))
      (ckaToFig8Adapters ℓ Pt C Dh encPt encT idOf lam) R)
    .unit (.inl .none) (.bool false)

def compileCkaDFAtomic (B0 : ℕ)
    (R : CostedReduction (fig8CkaOpsShallow ℓ Pt C Dh encPt encT idOf lam B0)
      (ckaIface (BitVec 256) (CryptoGames.CKA.DDH.State (BitVec 256) Pt) (BitVec 256) Pt Pt
        (BitVec 256) (BitVec 256) (BitVec 256)
        (RatchetSenderState (BitVec 256)) (RatchetReceiverState (BitVec 256) (BitVec 256))
        (LibsignalMsgPublicPart × Plain ℓ) (ℕ × LibsignalCiphertextWithSalt32)
        ($ᵗ (BitVec 256)) ($ᵗ (BitVec 256)) ($ᵗ (BitVec 256)) ($ᵗ Pt) ($ᵗ (BitVec 256)))
      (CryptoGames.SM.specDF (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (BitVec 256) (Fig8C Pt))
      (ckaSMCodecDF (BitVec 256) (CryptoGames.CKA.DDH.State (BitVec 256) Pt) (BitVec 256) Pt Pt
        (BitVec 256) (BitVec 256) (BitVec 256)
        (RatchetSenderState (BitVec 256)) (RatchetReceiverState (BitVec 256) (BitVec 256))
        (LibsignalMsgPublicPart × Plain ℓ) (ℕ × LibsignalCiphertextWithSalt32))
      .unit .unit .bool .bool) :
    CostedReduction O₂ (ckaTargetIface ℓ Pt)
      (CryptoGames.SM.specDF (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (BitVec 256) (Fig8C Pt))
      (fig8SmCodecDF ℓ Pt) .unit .unit .bool .bool :=
  guardRed (ℓ < 10 ^ 6)
    (compilePureAuxRed (ckaPureAuxBundle ℓ Pt C Dh encPt encT idOf lam B0 ($ᵗ (BitVec 256)))
      (ckaDFToFig8Adapters ℓ Pt C Dh encPt encT idOf lam) R)
    .unit (.inl .none) (.bool false)

def compilePrngAtomic (B0 : ℕ)
    (R : CostedReduction (fig8CkaOpsShallow ℓ Pt C Dh encPt encT idOf lam B0)
      (prngIface (BitVec 256) (CryptoGames.CKA.DDH.State (BitVec 256) Pt) (BitVec 256) Pt Pt
        (BitVec 256) (BitVec 256) (BitVec 256)
        (RatchetSenderState (BitVec 256)) (RatchetReceiverState (BitVec 256) (BitVec 256))
        (LibsignalMsgPublicPart × Plain ℓ) (ℕ × LibsignalCiphertextWithSalt32)
        ($ᵗ (BitVec 256)) ($ᵗ (BitVec 256)) ($ᵗ (BitVec 256)) ($ᵗ Pt) ($ᵗ (BitVec 256)))
      (CryptoGames.SM.spec (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (BitVec 256) (Fig8C Pt))
      (CryptoGames.PRFPRNG.prngSMCodec (BitVec 256) (CryptoGames.CKA.DDH.State (BitVec 256) Pt)
        (BitVec 256) Pt Pt (BitVec 256) (BitVec 256) (BitVec 256)
        (RatchetSenderState (BitVec 256)) (RatchetReceiverState (BitVec 256) (BitVec 256))
        (LibsignalMsgPublicPart × Plain ℓ) (ℕ × LibsignalCiphertextWithSalt32))
      .unit .unit .bool .bool) :
    CostedReduction O₂ (prngTargetIface ℓ Pt)
      (CryptoGames.SM.spec (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (BitVec 256) (Fig8C Pt))
      (fig8SmCodec ℓ Pt) .unit .unit .bool .bool :=
  guardRed (ℓ < 10 ^ 6)
    (compilePureAuxRed (prngPureAuxBundle ℓ Pt C Dh encPt encT idOf lam B0 ($ᵗ (BitVec 256)))
      (ckaToFig8Adapters ℓ Pt C Dh encPt encT idOf lam) R)
    .unit (.inl .none) (.bool false)

def compilePrngDFAtomic (B0 : ℕ)
    (R : CostedReduction (fig8CkaOpsShallow ℓ Pt C Dh encPt encT idOf lam B0)
      (prngIface (BitVec 256) (CryptoGames.CKA.DDH.State (BitVec 256) Pt) (BitVec 256) Pt Pt
        (BitVec 256) (BitVec 256) (BitVec 256)
        (RatchetSenderState (BitVec 256)) (RatchetReceiverState (BitVec 256) (BitVec 256))
        (LibsignalMsgPublicPart × Plain ℓ) (ℕ × LibsignalCiphertextWithSalt32)
        ($ᵗ (BitVec 256)) ($ᵗ (BitVec 256)) ($ᵗ (BitVec 256)) ($ᵗ Pt) ($ᵗ (BitVec 256)))
      (CryptoGames.SM.specDF (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (BitVec 256) (Fig8C Pt))
      (CryptoGames.PRFPRNG.prngSMCodecDF (BitVec 256) (CryptoGames.CKA.DDH.State (BitVec 256) Pt)
        (BitVec 256) Pt Pt (BitVec 256) (BitVec 256) (BitVec 256)
        (RatchetSenderState (BitVec 256)) (RatchetReceiverState (BitVec 256) (BitVec 256))
        (LibsignalMsgPublicPart × Plain ℓ) (ℕ × LibsignalCiphertextWithSalt32))
      .unit .unit .bool .bool) :
    CostedReduction O₂ (prngTargetIface ℓ Pt)
      (CryptoGames.SM.specDF (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (BitVec 256) (Fig8C Pt))
      (fig8SmCodecDF ℓ Pt) .unit .unit .bool .bool :=
  guardRed (ℓ < 10 ^ 6)
    (compilePureAuxRed (prngPureAuxBundle ℓ Pt C Dh encPt encT idOf lam B0 ($ᵗ (BitVec 256)))
      (ckaDFToFig8Adapters ℓ Pt C Dh encPt encT idOf lam) R)
    .unit (.inl .none) (.bool false)

def compileFsAtomic (B0 : ℕ)
    (R : CostedReduction (fig8CkaOpsShallow ℓ Pt C Dh encPt encT idOf lam B0)
      (fsaeadHeaderAdIface (BitVec 256) (CryptoGames.CKA.DDH.State (BitVec 256) Pt) (BitVec 256) Pt Pt
        (BitVec 256) (BitVec 256) (BitVec 256)
        (RatchetSenderState (BitVec 256)) (RatchetReceiverState (BitVec 256) (BitVec 256))
        (LibsignalMsgPublicPart × Plain ℓ) (ℕ × LibsignalCiphertextWithSalt32)
        ($ᵗ (BitVec 256)) ($ᵗ (BitVec 256)) ($ᵗ (BitVec 256)) ($ᵗ Pt) ($ᵗ (BitVec 256)))
      (CryptoGames.SM.spec (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (BitVec 256) (Fig8C Pt))
      (CryptoGames.PRFPRNG.prngSMCodec (BitVec 256) (CryptoGames.CKA.DDH.State (BitVec 256) Pt)
        (BitVec 256) Pt Pt (BitVec 256) (BitVec 256) (BitVec 256)
        (RatchetSenderState (BitVec 256)) (RatchetReceiverState (BitVec 256) (BitVec 256))
        (LibsignalMsgPublicPart × Plain ℓ) (ℕ × LibsignalCiphertextWithSalt32))
      .unit .unit .bool .bool) :
    CostedReduction O₂ (fsaeadHeaderIface ℓ Pt)
      (CryptoGames.SM.spec (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (BitVec 256) (Fig8C Pt))
      (fig8SmCodec ℓ Pt) .unit .unit .bool .bool :=
  guardRed (ℓ < 10 ^ 6)
    (compilePureAuxRed (fsPureAuxBundle ℓ Pt C Dh encPt encT idOf lam B0 ($ᵗ (BitVec 256)))
      (ckaToFig8Adapters ℓ Pt C Dh encPt encT idOf lam) R)
    .unit (.inl .none) (.bool false)

def compileFsDFAtomic (B0 : ℕ)
    (R : CostedReduction (fig8CkaOpsShallow ℓ Pt C Dh encPt encT idOf lam B0)
      (fsaeadHeaderAdIface (BitVec 256) (CryptoGames.CKA.DDH.State (BitVec 256) Pt) (BitVec 256) Pt Pt
        (BitVec 256) (BitVec 256) (BitVec 256)
        (RatchetSenderState (BitVec 256)) (RatchetReceiverState (BitVec 256) (BitVec 256))
        (LibsignalMsgPublicPart × Plain ℓ) (ℕ × LibsignalCiphertextWithSalt32)
        ($ᵗ (BitVec 256)) ($ᵗ (BitVec 256)) ($ᵗ (BitVec 256)) ($ᵗ Pt) ($ᵗ (BitVec 256)))
      (CryptoGames.SM.specDF (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (BitVec 256) (Fig8C Pt))
      (CryptoGames.PRFPRNG.prngSMCodecDF (BitVec 256) (CryptoGames.CKA.DDH.State (BitVec 256) Pt)
        (BitVec 256) Pt Pt (BitVec 256) (BitVec 256) (BitVec 256)
        (RatchetSenderState (BitVec 256)) (RatchetReceiverState (BitVec 256) (BitVec 256))
        (LibsignalMsgPublicPart × Plain ℓ) (ℕ × LibsignalCiphertextWithSalt32))
      .unit .unit .bool .bool) :
    CostedReduction O₂ (fsaeadHeaderIface ℓ Pt)
      (CryptoGames.SM.specDF (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (BitVec 256) (Fig8C Pt))
      (fig8SmCodecDF ℓ Pt) .unit .unit .bool .bool :=
  guardRed (ℓ < 10 ^ 6)
    (compilePureAuxRed (fsPureAuxBundle ℓ Pt C Dh encPt encT idOf lam B0 ($ᵗ (BitVec 256)))
      (ckaDFToFig8Adapters ℓ Pt C Dh encPt encT idOf lam) R)
    .unit (.inl .none) (.bool false)

end Bundles

section ConcreteInstances

variable {Pt : Type} [DecidableEq Pt] [Zero Pt] [SampleableType Pt]

local instance : Inhabited Pt := ⟨0⟩

/-- Concrete atomic `Fig8CostedReds` bundle over `ReductionDsl.atomicFig8Ops`. -/
def fig8RedsInst (Dh : DHFun (BitVec 256) Pt) (encPt : Pt → List (BitVec 8))
    (C : Crypto) (codec : SignalMessageProtoCodec)
    (ℓ : ℕ) (encT : Pt → PublicKey) (idOf : Party → IdentityKey) (lam : Pt) (qep q : ℕ) :
    Fig8CostedReds Dh encPt C codec ℓ encT idOf lam :=
  let B0 := (q + 1) * (maxForwardJumps + 1)
  { challSim :=
      compileSmAtomic ℓ Pt C Dh encPt encT idOf lam
        (CryptoGames.SM.challSimProg q (2 + 1) qep)
    privRedB := fun i =>
      compileSmAtomic ℓ Pt C Dh encPt encT idOf lam
        (CryptoGames.SM.privRedBProg q (2 + 1) qep i)
    redCKAAuth := fun tL t =>
      compileCkaAtomic ℓ Pt C Dh encPt encT idOf lam B0
        (CryptoGames.SM.Construction.redCKAAuthProg (q + 1) B0 1 qep maxForwardJumps tL t)
    redPRNGAuth := fun tL t =>
      compilePrngAtomic ℓ Pt C Dh encPt encT idOf lam B0
        (CryptoGames.SM.Construction.redPRNGAuthProg (q + 1) B0 1 qep maxForwardJumps tL t)
    redFSAuth := fun j tL t =>
      compileFsAtomic ℓ Pt C Dh encPt encT idOf lam B0
        (CryptoGames.SM.Construction.redFSAuthProg (q + 1) B0 1 qep maxForwardJumps j tL t)
    redCKAPriv := fun tL i =>
      compileCkaAtomic ℓ Pt C Dh encPt encT idOf lam B0
        (CryptoGames.SM.Construction.redCKAPrivProg (q + 1) B0 1 qep maxForwardJumps tL i)
    redPRNGPriv := fun tL i =>
      compilePrngAtomic ℓ Pt C Dh encPt encT idOf lam B0
        (CryptoGames.SM.Construction.redPRNGPrivProg (q + 1) B0 1 qep maxForwardJumps tL i)
    redFSPriv := fun tL i =>
      compileFsAtomic ℓ Pt C Dh encPt encT idOf lam B0
        (CryptoGames.SM.Construction.redFSPrivProg (q + 1) B0 1 qep maxForwardJumps tL i)
    redFSPrivCoin := fun tL i =>
      compileFsAtomic ℓ Pt C Dh encPt encT idOf lam B0
        (CryptoGames.SM.Construction.redFSPrivCoinProg (q + 1) B0 1 qep maxForwardJumps tL i) }

def challSimDFAtomicProg (Dh : DHFun (BitVec 256) Pt) (encPt : Pt → List (BitVec 8))
    (C : Crypto) (ℓ : ℕ) (encT : Pt → PublicKey) (idOf : Party → IdentityKey) (lam : Pt)
    (qep q : ℕ) :
    CostedReduction (atomicFig8Ops ℓ Pt C Dh encPt encT lam) (fig8SmIfaceDF ℓ Pt)
      (CryptoGames.SM.specDF (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (BitVec 256) (Fig8C Pt))
      (fig8SmCodecDF ℓ Pt) .unit .unit .bool .bool :=
  compileSmDFAtomic ℓ Pt C Dh encPt encT idOf lam
    (CryptoGames.SM.challSimDFProg q (2 + 1) qep)

def redCKAAuthDFAtomicProg (Dh : DHFun (BitVec 256) Pt) (encPt : Pt → List (BitVec 8))
    (C : Crypto) (ℓ : ℕ) (encT : Pt → PublicKey) (idOf : Party → IdentityKey) (lam : Pt)
    (qep q : ℕ) (tL : Option ℕ) (t : ℕ) :
    CostedReduction (atomicFig8Ops ℓ Pt C Dh encPt encT lam) (ckaTargetIface ℓ Pt)
      (CryptoGames.SM.specDF (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (BitVec 256) (Fig8C Pt))
      (fig8SmCodecDF ℓ Pt) .unit .unit .bool .bool :=
  let B0 := (q + 1) * (maxForwardJumps + 1)
  compileCkaDFAtomic ℓ Pt C Dh encPt encT idOf lam B0
    (CryptoGames.SM.Construction.redCKAAuthDFProg (q + 1) B0 1 qep maxForwardJumps tL t)

def redPRNGAuthDFAtomicProg (Dh : DHFun (BitVec 256) Pt) (encPt : Pt → List (BitVec 8))
    (C : Crypto) (ℓ : ℕ) (encT : Pt → PublicKey) (idOf : Party → IdentityKey) (lam : Pt)
    (qep q : ℕ) (tL : Option ℕ) (t : ℕ) :
    CostedReduction (atomicFig8Ops ℓ Pt C Dh encPt encT lam) (prngTargetIface ℓ Pt)
      (CryptoGames.SM.specDF (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (BitVec 256) (Fig8C Pt))
      (fig8SmCodecDF ℓ Pt) .unit .unit .bool .bool :=
  let B0 := (q + 1) * (maxForwardJumps + 1)
  compilePrngDFAtomic ℓ Pt C Dh encPt encT idOf lam B0
    (CryptoGames.SM.Construction.redPRNGAuthDFProg (q + 1) B0 1 qep maxForwardJumps tL t)

def redFSAuthDFAtomicProg (Dh : DHFun (BitVec 256) Pt) (encPt : Pt → List (BitVec 8))
    (C : Crypto) (ℓ : ℕ) (encT : Pt → PublicKey) (idOf : Party → IdentityKey) (lam : Pt)
    (qep q : ℕ) (j : ℕ) (tL : Option ℕ) (t : ℕ) :
    CostedReduction (atomicFig8Ops ℓ Pt C Dh encPt encT lam) (fsaeadHeaderIface ℓ Pt)
      (CryptoGames.SM.specDF (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (BitVec 256) (Fig8C Pt))
      (fig8SmCodecDF ℓ Pt) .unit .unit .bool .bool :=
  let B0 := (q + 1) * (maxForwardJumps + 1)
  compileFsDFAtomic ℓ Pt C Dh encPt encT idOf lam B0
    (CryptoGames.SM.Construction.redFSAuthDFProg (q + 1) B0 1 qep maxForwardJumps j tL t)

end ConcreteInstances


section QuerySubsumesLiftP

private theorem querySubsumes_pure_liftP_of_mem_support
    {κ : Type} {G : OracleSpec.{0, 0} κ} {S₁' : Sig}
    (I₁ : Iface S₁' (unifSpec + G))
    (hFwd₁ : ∀ n, I₁.fwdU n = liftM (OracleSpec.query (spec := unifSpec + G) (.inl n)))
    {β γ : Type} (f : β → γ) (p₂ : ProbComp β) {y : β} (hy : y ∈ support p₂) :
    QuerySubsumes (pure (f y) : OracleComp (unifSpec + G) γ) (f <$> I₁.liftP p₂) := by
  induction p₂ using OracleComp.inductionOn with
  | pure b =>
    simp only [support_pure, Set.mem_singleton_iff] at hy
    subst hy
    simp only [Iface.liftP, simulateQ_pure, map_pure]
    exact .ret (f y)
  | query_bind n mx ih =>
    rw [mem_support_bind_iff] at hy
    obtain ⟨u, _, hy⟩ := hy
    have hStep : f <$> I₁.liftP (liftM (OracleSpec.query n) >>= mx) =
        liftM (OracleSpec.query (spec := unifSpec + G) (.inl n)) >>= fun v => f <$> I₁.liftP (mx v) := by
      simp [Iface.liftP, hFwd₁, map_bind]
    rw [hStep]
    exact .coin_r _ n _ u (ih u hy)

private theorem querySubsumes_liftP_of_forall_mem_support
    {κ : Type} {G : OracleSpec.{0, 0} κ} {S₂' : Sig}
    (I₂ : Iface S₂' (unifSpec + G))
    (hFwd₂ : ∀ n, I₂.fwdU n = liftM (OracleSpec.query (spec := unifSpec + G) (.inl n)))
    {β γ : Type} (f : β → γ) (p₁ : ProbComp β)
    {oa₂ : OracleComp (unifSpec + G) γ}
    (h : ∀ x ∈ support p₁, QuerySubsumes (pure (f x)) oa₂) :
    QuerySubsumes (f <$> I₂.liftP p₁) oa₂ := by
  induction p₁ using OracleComp.inductionOn with
  | pure b =>
    simp only [Iface.liftP, simulateQ_pure, map_pure]
    exact h b (by simp)
  | query_bind n mx ih =>
    have hStep : f <$> I₂.liftP (liftM (OracleSpec.query n) >>= mx) =
        liftM (OracleSpec.query (spec := unifSpec + G) (.inl n)) >>= fun u => f <$> I₂.liftP (mx u) := by
      simp [Iface.liftP, hFwd₂, map_bind]
    rw [hStep]
    exact .coin_l n _ oa₂ fun u => ih u fun x hx =>
      h x (by rw [mem_support_bind_iff]; exact ⟨u, by simp, hx⟩)

theorem querySubsumes_liftP_of_support_subset
    {κ : Type} {G : OracleSpec.{0, 0} κ} {S₁' S₂' : Sig}
    (I₂ : Iface S₂' (unifSpec + G)) (I₁ : Iface S₁' (unifSpec + G))
    (hFwd₂ : ∀ n, I₂.fwdU n = liftM (OracleSpec.query (spec := unifSpec + G) (.inl n)))
    (hFwd₁ : ∀ n, I₁.fwdU n = liftM (OracleSpec.query (spec := unifSpec + G) (.inl n)))
    {β : Type} {p₁ p₂ : ProbComp β} (hsup : ∀ x ∈ support p₁, x ∈ support p₂) :
    QuerySubsumes (I₂.liftP p₁) ((fun x => x) <$> I₁.liftP p₂) := by
  have h := querySubsumes_liftP_of_forall_mem_support I₂ hFwd₂ id p₁ fun x hx =>
    querySubsumes_pure_liftP_of_mem_support I₁ hFwd₁ id p₂ (hsup x hx)
  rwa [id_map] at h

theorem fsPureAuxBundle_samp_querySubsumes
    (ℓ : ℕ) (Pt : Type) [DecidableEq Pt] [Zero Pt] [SampleableType Pt]
    (C : Crypto) (Dh : DHFun (BitVec 256) Pt) (encPt : Pt → List (BitVec 8))
    (encT : Pt → PublicKey) (idOf : Party → IdentityKey) (lam : Pt)
    (B0 : ℕ) (s : CKASamp)
    (z : ((fsaeadHeaderAdIface (BitVec 256) (CryptoGames.CKA.DDH.State (BitVec 256) Pt)
      (BitVec 256) Pt Pt (BitVec 256) (BitVec 256) (BitVec 256)
      (RatchetSenderState (BitVec 256)) (RatchetReceiverState (BitVec 256) (BitVec 256))
      (LibsignalMsgPublicPart × Plain ℓ) (ℕ × LibsignalCiphertextWithSalt32)
      ($ᵗ (BitVec 256)) ($ᵗ (BitVec 256)) ($ᵗ (BitVec 256)) ($ᵗ Pt) ($ᵗ (BitVec 256))).smp.sDom s).denote) :
    QuerySubsumes
      (((fsPureAuxBundle ℓ Pt C Dh encPt encT idOf lam B0 ($ᵗ (BitVec 256))).sampMacro s).eval
        (.cons (toVal (fSortCKA ℓ Pt) (toDenCKA ℓ Pt) _ z) (.cons (idOf .A, idOf .B) .nil)))
      (toVal (fSortCKA ℓ Pt) (toDenCKA ℓ Pt)
        ((fsaeadHeaderAdIface (BitVec 256) (CryptoGames.CKA.DDH.State (BitVec 256) Pt)
          (BitVec 256) Pt Pt (BitVec 256) (BitVec 256) (BitVec 256)
          (RatchetSenderState (BitVec 256)) (RatchetReceiverState (BitVec 256) (BitVec 256))
          (LibsignalMsgPublicPart × Plain ℓ) (ℕ × LibsignalCiphertextWithSalt32)
          ($ᵗ (BitVec 256)) ($ᵗ (BitVec 256)) ($ᵗ (BitVec 256)) ($ᵗ Pt) ($ᵗ (BitVec 256))).smp.sTy s) <$>
        (fsaeadHeaderAdIface (BitVec 256) (CryptoGames.CKA.DDH.State (BitVec 256) Pt)
          (BitVec 256) Pt Pt (BitVec 256) (BitVec 256) (BitVec 256)
          (RatchetSenderState (BitVec 256)) (RatchetReceiverState (BitVec 256) (BitVec 256))
          (LibsignalMsgPublicPart × Plain ℓ) (ℕ × LibsignalCiphertextWithSalt32)
          ($ᵗ (BitVec 256)) ($ᵗ (BitVec 256)) ($ᵗ (BitVec 256)) ($ᵗ Pt) ($ᵗ (BitVec 256))).liftP
          ((fsaeadHeaderAdIface (BitVec 256) (CryptoGames.CKA.DDH.State (BitVec 256) Pt)
            (BitVec 256) Pt Pt (BitVec 256) (BitVec 256) (BitVec 256)
            (RatchetSenderState (BitVec 256)) (RatchetReceiverState (BitVec 256) (BitVec 256))
            (LibsignalMsgPublicPart × Plain ℓ) (ℕ × LibsignalCiphertextWithSalt32)
            ($ᵗ (BitVec 256)) ($ᵗ (BitVec 256)) ($ᵗ (BitVec 256)) ($ᵗ Pt) ($ᵗ (BitVec 256))).smp.samp s z)) := by
  cases s with
  | bit | i =>
    apply QuerySubsumes.of_eq
    exact (liftP_congr (fsaeadHeaderIface ℓ Pt) _ (fun _ => rfl) _).trans (id_map _).symm
  | kr | kc | ccoins | k =>
    exact
      querySubsumes_liftP_of_support_subset (fsaeadHeaderIface ℓ Pt)
        (fsaeadHeaderAdIface (BitVec 256) (CryptoGames.CKA.DDH.State (BitVec 256) Pt)
          (BitVec 256) Pt Pt (BitVec 256) (BitVec 256) (BitVec 256)
          (RatchetSenderState (BitVec 256)) (RatchetReceiverState (BitVec 256) (BitVec 256))
          (LibsignalMsgPublicPart × Plain ℓ) (ℕ × LibsignalCiphertextWithSalt32)
          ($ᵗ (BitVec 256)) ($ᵗ (BitVec 256)) ($ᵗ (BitVec 256)) ($ᵗ Pt) ($ᵗ (BitVec 256)))
        (fun _ => rfl) (fun _ => rfl) (fun _ _ => by simp)

end QuerySubsumesLiftP

section PureAuxSize

@[simp] theorem callPureMacroAux_size {S₁ S₂ : Sig} (f : S₁.Base → Ty S₂) (auxT : Ty S₂)
    (Γ : List (Ty S₁)) {O₂ : Ops S₂} {a b : Ty S₂} (e : Expr O₂ [a, auxT] b) :
    (callPureMacroAux f auxT Γ e).size = e.size :=
  Expr.renameM_size _ e

@[simp] theorem callAdaptR_size {S₂ : Sig} {O₂ : Ops S₂} {r₁T q₂T r₂T a b c d e : Ty S₂}
    (adR : Expr O₂ [r₁T, q₂T] r₂T) :
    (callAdaptR (a := a) (b := b) (c := c) (d := d) (e := e) adR).size = adR.size :=
  Expr.renameM_size _ adR

/-- Weighted AST node/bit size of `Expr O Γ t` with custom per-operator size weight `opS`. -/
def exprSizeW {S : Sig} {O : Ops S} (opS : O.Op → ℕ) :
    {Γ : List (Ty S)} → {t : Ty S} → Expr O Γ t → ℕ
  | _, _, .var _ | _, _, .unit | _, _, .bool _ | _, _, .none | _, _, .nil => 1
  | _, _, .nat n => bits n
  | _, _, .add a b | _, _, .sub a b | _, _, .lt a b | _, _, .eqN a b
  | _, _, .and a b | _, _, .pair a b | _, _, .cons a b | _, _, .take a b
  | _, _, .tget a b | _, _, .letE a b => exprSizeW opS a + exprSizeW opS b + 1
  | _, _, .mulK k a | _, _, .divK k a | _, _, .modK k a => exprSizeW opS a + bits k + 1
  | _, _, .not a | _, _, .fst a | _, _, .snd a | _, _, .inl a | _, _, .inr a
  | _, _, .some a | _, _, .len a | _, _, .tconst a => exprSizeW opS a + 1
  | _, _, .ite c a b | _, _, .caseOpt c a b | _, _, .caseSum c a b | _, _, .tset c a b =>
    exprSizeW opS c + exprSizeW opS a + exprSizeW opS b + 1
  | _, _, .op o a => exprSizeW opS a + opS o
  | _, _, .appendL K a b => exprSizeW opS a + exprSizeW opS b + bits K + 1
  | _, _, .findB K l p | _, _, .anyB K l p | _, _, .mapB K l p =>
    exprSizeW opS l + exprSizeW opS p + bits K + 1
  | _, _, .foldrB K l z f =>
    exprSizeW opS l + exprSizeW opS z + exprSizeW opS f + bits K + 1

/-- Weighted AST node/bit size of `Comp O I Γ t` with custom op, sampler, and query size weights. -/
def compSizeW {S : Sig} {O : Ops S} {ι : Type} {T : OracleSpec ι} {I : Iface S T}
    (opS : O.Op → ℕ) (sS : I.smp.Samp → ℕ) (qS : I.Tag → ℕ) :
    {Γ : List (Ty S)} → {t : Ty S} → Comp O I Γ t → ℕ
  | _, _, .ret e => exprSizeW opS e + 1
  | _, _, .bind c k => compSizeW opS sS qS c + compSizeW opS sS qS k + 1
  | _, _, .ite b c d | _, _, .caseOpt b c d | _, _, .caseSum b c d =>
    exprSizeW opS b + compSizeW opS sS qS c + compSizeW opS sS qS d + 1
  | _, _, .sample s e => exprSizeW opS e + sS s
  | _, _, .query g e => exprSizeW opS e + qS g
  | _, _, .iter n e body | _, _, .findM n e body | _, _, .anyM n e body | _, _, .mapM n e body =>
    exprSizeW opS e + compSizeW opS sS qS body + bits n + 1
  | _, _, .consumeFirstM K l p mk =>
    exprSizeW opS l + compSizeW opS sS qS p + exprSizeW opS mk + bits K + 1
  | _, _, .foldM K l z f =>
    exprSizeW opS l + exprSizeW opS z + compSizeW opS sS qS f + bits K + 1

@[simp] theorem exprSizeW_renameM {S : Sig} {O : Ops S} (opS : O.Op → ℕ)
    {Γ Δ : List (Ty S)} (ξ : ∀ ⦃u⦄, ReductionDsl.Var Γ u → ReductionDsl.Var Δ u)
    {t : Ty S} (e : Expr O Γ t) :
    exprSizeW opS (Expr.renameM ξ e) = exprSizeW opS e := by
  induction e generalizing Δ <;> simp [Expr.renameM, exprSizeW, *]

@[simp] theorem compSizeW_renameM {S : Sig} {O : Ops S} {ι : Type} {T : OracleSpec ι}
    {I : Iface S T} (opS : O.Op → ℕ) (sS : I.smp.Samp → ℕ) (qS : I.Tag → ℕ)
    {Γ Δ : List (Ty S)} (ξ : ∀ ⦃u⦄, ReductionDsl.Var Γ u → ReductionDsl.Var Δ u)
    {t : Ty S} (c : Comp O I Γ t) :
    compSizeW opS sS qS (Comp.renameM ξ c) = compSizeW opS sS qS c := by
  induction c generalizing Δ <;> simp [Comp.renameM, compSizeW, *]

theorem compilePureAuxExpr_size_le {S₁ S₂ : Sig} {O₁ : Ops S₁} {O₂ : Ops S₂}
    {ι : Type} {T : OracleSpec ι} {I₁ : Iface S₁ T} {I₂ : Iface S₂ T} {auxT : Ty S₂}
    (M : PureAuxBundle S₁ S₂ O₁ O₂ I₁ I₂ auxT)
    (opS : O₁.Op → ℕ) (hOp : ∀ o, (M.opMacro o).size + 1 ≤ opS o)
    {Γ : List (Ty S₁)} {t : Ty S₁} (e : Expr O₁ Γ t) :
    (compilePureAuxExpr M e).size ≤ exprSizeW opS e := by
  induction e with
  | var _ | unit | bool _ | nat _ | none | nil =>
    simp only [compilePureAuxExpr, Expr.size, exprSizeW]; omega
  | add _ _ ih1 ih2 | sub _ _ ih1 ih2 | lt _ _ ih1 ih2 | eqN _ _ ih1 ih2 | and _ _ ih1 ih2
  | pair _ _ ih1 ih2 | cons _ _ ih1 ih2 | take _ _ ih1 ih2 | appendL _ _ _ ih1 ih2
  | tget _ _ ih1 ih2 | letE _ _ ih1 ih2 =>
    simp only [compilePureAuxExpr, Expr.size, exprSizeW]; omega
  | mulK _ _ ih | divK _ _ ih | modK _ _ ih | not _ ih | fst _ ih | snd _ ih
  | inl _ ih | inr _ ih | some _ ih | len _ ih | tconst _ ih =>
    simp only [compilePureAuxExpr, Expr.size, exprSizeW]; omega
  | ite _ _ _ ihc iha ihb | caseOpt _ _ _ ihc iha ihb | caseSum _ _ _ ihc iha ihb
  | foldrB _ _ _ _ ihc iha ihb | tset _ _ _ ihc iha ihb =>
    simp only [compilePureAuxExpr, Expr.size, exprSizeW]; omega
  | op o _ iha =>
    have ho := hOp o
    simp only [compilePureAuxExpr, Expr.size, callPureMacroAux_size, exprSizeW]; omega
  | findB _ _ _ ihl ihp | anyB _ _ _ ihl ihp | mapB _ _ _ ihl ihp =>
    simp only [compilePureAuxExpr, Expr.size, exprSizeW]; omega

theorem compilePureAuxComp_size_le {S₁ S₂ : Sig} {O₁ : Ops S₁} {O₂ : Ops S₂}
    {ι : Type} {T : OracleSpec ι} {I₁ : Iface S₁ T} {I₂ : Iface S₂ T} {auxT : Ty S₂}
    (M : PureAuxBundle S₁ S₂ O₁ O₂ I₁ I₂ auxT)
    (opS : O₁.Op → ℕ) (sS : I₁.smp.Samp → ℕ) (qS : I₁.Tag → ℕ)
    (hOp : ∀ o, (M.opMacro o).size + 1 ≤ opS o)
    (hSamp : ∀ s, (M.sampMacro s).size + 2 ≤ sS s)
    (hQuery : ∀ g, (M.queryMacro g).size + 2 ≤ qS g)
    {Γ : List (Ty S₁)} {t : Ty S₁} (c : Comp O₁ I₁ Γ t) :
    (compilePureAuxComp M c).size ≤ compSizeW opS sS qS c := by
  induction c with
  | ret e =>
    have he := compilePureAuxExpr_size_le M opS hOp e
    simp only [compilePureAuxComp, Comp.size, compSizeW]; omega
  | bind _ _ ihc ihk =>
    simp only [compilePureAuxComp, Comp.size, compSizeW]; omega
  | ite b _ _ ihc ihd | caseOpt b _ _ ihc ihd | caseSum b _ _ ihc ihd =>
    have hb := compilePureAuxExpr_size_le M opS hOp b
    simp only [compilePureAuxComp, Comp.size, compSizeW]; omega
  | sample s e =>
    have he := compilePureAuxExpr_size_le M opS hOp e
    have hs := hSamp s
    simp only [compilePureAuxComp, Comp.size, callMacroAux_size, compSizeW]; omega
  | query g e =>
    have he := compilePureAuxExpr_size_le M opS hOp e
    have hq := hQuery g
    simp only [compilePureAuxComp, Comp.size, callMacroAux_size, compSizeW]; omega
  | iter _ e _ ihb | findM _ e _ ihb | anyM _ e _ ihb | mapM _ e _ ihb =>
    have he := compilePureAuxExpr_size_le M opS hOp e
    simp only [compilePureAuxComp, Comp.size, compSizeW]; omega
  | consumeFirstM _ l _ mk ihp =>
    have hl := compilePureAuxExpr_size_le M opS hOp l
    have hmk := compilePureAuxExpr_size_le M opS hOp mk
    simp only [compilePureAuxComp, Comp.size, compSizeW]; omega
  | foldM _ l z _ ihf =>
    have hl := compilePureAuxExpr_size_le M opS hOp l
    have hz := compilePureAuxExpr_size_le M opS hOp z
    simp only [compilePureAuxComp, Comp.size, compSizeW]; omega

theorem compilePureAuxRed_size_le {S₁ S₂ : Sig} {O₁ : Ops S₁} {O₂ : Ops S₂}
    {ι κ : Type} {T : OracleSpec ι} {G : OracleSpec κ}
    {I₁ : Iface S₁ T} {I₂ : Iface S₂ T}
    {C₁ : ReductionDsl.GameCodec S₁ G} {C₂ : ReductionDsl.GameCodec S₂ G} {auxT : Ty S₂}
    (M : PureAuxBundle S₁ S₂ O₁ O₂ I₁ I₂ auxT)
    {rIn₁ aIn₁ aOut₁ out₁ : Ty S₁} {rIn₂ aIn₂ aOut₂ out₂ : Ty S₂}
    (A : PureAuxAdapters M.fSort O₂ C₁ C₂ auxT rIn₁ aIn₁ aOut₁ out₁ rIn₂ aIn₂ aOut₂ out₂)
    (R : CostedReduction O₁ I₁ G C₁ rIn₁ aIn₁ aOut₁ out₁)
    (opS : O₁.Op → ℕ) (sS : I₁.smp.Samp → ℕ) (qS : I₁.Tag → ℕ)
    (hOp : ∀ o, (M.opMacro o).size + 1 ≤ opS o)
    (hSamp : ∀ s, (M.sampMacro s).size + 2 ≤ sS s)
    (hQuery : ∀ g, (M.queryMacro g).size + 2 ≤ qS g) :
    (compilePureAuxRed M A R).size ≤
      compSizeW opS sS qS R.init + compSizeW opS sS qS R.handle + compSizeW opS sS qS R.finish +
        A.splitIn.size + A.adaptAIn.size + A.adaptQ.size + A.adaptR.size +
        A.adaptAOut.size + A.adaptOut.size + 74 := by
  have hi := compilePureAuxComp_size_le M opS sS qS hOp hSamp hQuery R.init
  have hh := compilePureAuxComp_size_le M opS sS qS hOp hSamp hQuery R.handle
  have hf := compilePureAuxComp_size_le M opS sS qS hOp hSamp hQuery R.finish
  simp only [CostedReduction.size, compilePureAuxRed, Comp.size, Comp.renameM_size,
    Expr.renameM_size, callAdaptR_size, Expr.size]
  omega

theorem exprSizeW_le_mul_size {S : Sig} {O : Ops S} (opS : O.Op → ℕ)
    (K : ℕ) (hK : 2 ≤ K) (hOp : ∀ o, opS o ≤ K)
    {Γ : List (Ty S)} {t : Ty S} (e : Expr O Γ t) :
    exprSizeW opS e ≤ K * e.size := by
  induction e with
  | var _ | unit | bool _ | none | nil =>
    simp only [exprSizeW, Expr.size]; omega
  | nat _ =>
    simp only [exprSizeW, Expr.size]; nlinarith
  | add _ _ ih1 ih2 | sub _ _ ih1 ih2 | lt _ _ ih1 ih2 | eqN _ _ ih1 ih2 | and _ _ ih1 ih2
  | pair _ _ ih1 ih2 | cons _ _ ih1 ih2 | take _ _ ih1 ih2 | appendL _ _ _ ih1 ih2
  | tget _ _ ih1 ih2 | letE _ _ ih1 ih2 =>
    simp only [exprSizeW, Expr.size]; nlinarith
  | mulK k _ ih | divK k _ ih | modK k _ ih =>
    have hk := _root_.ReductionDsl.one_le_bits k
    simp only [exprSizeW, Expr.size]; nlinarith
  | not _ ih | fst _ ih | snd _ ih
  | inl _ ih | inr _ ih | some _ ih | len _ ih | tconst _ ih =>
    simp only [exprSizeW, Expr.size]; nlinarith
  | ite _ _ _ ihc iha ihb | caseOpt _ _ _ ihc iha ihb | caseSum _ _ _ ihc iha ihb
  | foldrB _ _ _ _ ihc iha ihb | tset _ _ _ ihc iha ihb =>
    simp only [exprSizeW, Expr.size]; nlinarith
  | op o _ iha =>
    have ho := hOp o
    simp only [exprSizeW, Expr.size]; nlinarith
  | findB _ _ _ ihl ihp | anyB _ _ _ ihl ihp | mapB _ _ _ ihl ihp =>
    simp only [exprSizeW, Expr.size]; nlinarith

theorem compSizeW_le_mul_size {S : Sig} {O : Ops S} {ι : Type} {T : OracleSpec ι} {I : Iface S T}
    (opS : O.Op → ℕ) (sS : I.smp.Samp → ℕ) (qS : I.Tag → ℕ)
    (K : ℕ) (hK : 2 ≤ K)
    (hOp : ∀ o, opS o ≤ K) (hSamp : ∀ s, sS s ≤ K) (hQuery : ∀ g, qS g ≤ K)
    {Γ : List (Ty S)} {t : Ty S} (c : Comp O I Γ t) :
    compSizeW opS sS qS c ≤ K * c.size := by
  induction c with
  | ret e =>
    have he := exprSizeW_le_mul_size opS K hK hOp e
    simp only [compSizeW, Comp.size]; nlinarith
  | bind _ _ ihc ihk =>
    simp only [compSizeW, Comp.size]; nlinarith
  | ite b _ _ ihc ihd | caseOpt b _ _ ihc ihd | caseSum b _ _ ihc ihd =>
    have hb := exprSizeW_le_mul_size opS K hK hOp b
    simp only [compSizeW, Comp.size]; nlinarith
  | sample s e =>
    have he := exprSizeW_le_mul_size opS K hK hOp e
    have hs := hSamp s
    simp only [compSizeW, Comp.size]; nlinarith
  | query g e =>
    have he := exprSizeW_le_mul_size opS K hK hOp e
    have hq := hQuery g
    simp only [compSizeW, Comp.size]; nlinarith
  | iter _ e _ ihb | findM _ e _ ihb | anyM _ e _ ihb | mapM _ e _ ihb =>
    have he := exprSizeW_le_mul_size opS K hK hOp e
    simp only [compSizeW, Comp.size]; nlinarith
  | consumeFirstM _ l _ mk ihp =>
    have hl := exprSizeW_le_mul_size opS K hK hOp l
    have hmk := exprSizeW_le_mul_size opS K hK hOp mk
    simp only [compSizeW, Comp.size]; nlinarith
  | foldM _ l z _ ihf =>
    have hl := exprSizeW_le_mul_size opS K hK hOp l
    have hz := exprSizeW_le_mul_size opS K hK hOp z
    simp only [compSizeW, Comp.size]; nlinarith

def smOpS : SMOp → ℕ := fun _ => 125
def smSampS : SMSamp → ℕ := fun _ => 10
def smQueryS {Tag : Type} : Tag → ℕ := fun _ => 10

def ckaOpS (B0 : ℕ) : CKAOp → ℕ
  | .fsReceive B => 3 * bits B0 + 2 * bits B + 1205
  | _ => 305

def ckaSampS : CKASamp → ℕ := fun _ => 10
def ckaQueryS {Tag : Type} : Tag → ℕ := fun _ => 10

theorem smOpMacro_size_le (ℓ : ℕ) (Pt : Type) [DecidableEq Pt] [Zero Pt]
    (C : Crypto) (Dh : DHFun (BitVec 256) Pt) (encPt : Pt → List (BitVec 8))
    (encT : Pt → PublicKey) (lam : Pt) (o : SMOp) :
    (smOpMacro ℓ Pt C Dh encPt encT lam o).size + 1 ≤ smOpS o := by
  have h1 := eqMExpr_size ℓ Pt C Dh encPt encT lam
  have h2 := smEqCtExpr_size ℓ Pt C Dh encPt encT lam
  have h3 := smBlankExpr_size ℓ Pt C Dh encPt encT lam
  cases o <;> simp only [smOpMacro, smOpS, Expr.size] <;> omega

theorem ckaOpMacro_size_le (ℓ : ℕ) (Pt : Type) [DecidableEq Pt] [Zero Pt]
    (C : Crypto) (Dh : DHFun (BitVec 256) Pt) (encPt : Pt → List (BitVec 8))
    (encT : Pt → PublicKey) (idOf : Party → IdentityKey) (lam : Pt) (B0 : ℕ) (o : CKAOp) :
    (ckaOpMacro ℓ Pt C Dh encPt encT idOf lam B0 o).size + 1 ≤ ckaOpS B0 o := by
  have h1 := ckaInitAExpr_size ℓ Pt C Dh encPt encT lam
  have h2 := ckaInitBExpr_size ℓ Pt C Dh encPt encT lam
  have h3 := ckaSendExpr_size ℓ Pt C Dh encPt encT lam
  have h4 := ckaRecvExpr_size ℓ Pt C Dh encPt encT lam
  have h5 := prngInitExpr_size ℓ Pt C Dh encPt encT lam
  have h6 := prngUpExpr_size ℓ Pt C Dh encPt encT lam
  have h7 := fsInitSendExpr_size ℓ Pt C Dh encPt encT lam
  have h8 := fsInitRecvExpr_size ℓ Pt C Dh encPt encT lam
  have h9 := fsSendExpr_size ℓ Pt C Dh encPt encT lam
  have h10 := eqPtExpr_size ℓ Pt C Dh encPt encT lam
  have h11 := eqMExpr_size ℓ Pt C Dh encPt encT lam
  have h12 := eqEExpr_size ℓ Pt C Dh encPt encT lam
  have h13 := lamIExpr_size ℓ Pt C Dh encPt encT lam
  have h14 := defaultEExpr_size ℓ Pt C Dh encPt encT lam
  cases o with
  | fsReceive B =>
    have h15 := fsRecvExpr_size ℓ Pt C Dh encPt encT lam B0 B
    simp only [ckaOpMacro, ckaOpS]; omega
  | _ => simp only [ckaOpMacro, ckaOpS]; omega

end PureAuxSize

end Computational.Proofs.SessionCostedFig8.Bundles
