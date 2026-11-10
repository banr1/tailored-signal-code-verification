/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Computational.Specifications.Pqxdh.Bound
public import Computational.Specifications.Pqxdh.Security.Headline
public import Computational.Specifications.Pqxdh.Security.CostedBudgets
public import Computational.Proofs.SignalPqxdh.AtomicLift -- proof-setup: allow-public-import
public import Computational.Proofs.SignalPqxdh.Delta.KeyInd1KeyActiveProgs -- proof-setup: allow-public-import
public import Computational.Proofs.SignalPqxdh.Delta.KindSplit.KeyInd1KeyKindProgs -- proof-setup: allow-public-import
public import Computational.Proofs.SignalPqxdh.Security.ReductionDsl.KeyIndGapDh -- proof-setup: allow-public-import
public import Computational.Proofs.SignalPqxdh.Security.ReductionDsl.KindSplit.KeyIndGapDhK -- proof-setup: allow-public-import
public import Computational.Proofs.SignalPqxdh.Security.ReductionDsl.KindSplit.KeyIndGapDhKSimBase -- proof-setup: allow-public-import
import Computational.Proofs.ReductionDsl.StepSim
import Computational.Proofs.GameHop.ReductionDsl.SupportWP
import Computational.Proofs.SignalPqxdh.Security.ReductionDsl.KeyIndCore
import Computational.Proofs.SignalPqxdh.Security.ReductionDsl.KeyIndSigKem
import Computational.Proofs.SignalPqxdh.Security.ReductionDsl.KeyInd1KeySigProg
import Computational.Proofs.SignalPqxdh.Security.ReductionDsl.KeyInd1KeySigBounds
import Computational.Proofs.SignalPqxdh.Security.ReductionDsl.KeyInd1KeySigEval
import Computational.Proofs.SignalPqxdh.Security.ReductionDsl.KeyInd1KeyGapDh
import Computational.Proofs.SignalPqxdh.Security.ReductionDsl.KeyInd1KeyGapDhEvalEq
import Computational.Proofs.SignalPqxdh.Security.ReductionDsl.SplitRo.AvlRoTableDefs
import Computational.Proofs.SignalPqxdh.Security.ReductionDsl.KindSplit.KeyIndCoreK
import Computational.Proofs.SignalPqxdh.Security.ReductionDsl.KindSplit.KeyIndCoreKSimBase

/-!
# State-Growing Non-Session Step Simulation for Shadow-Indexed `KeyInd` Gap-DH

Proves the `KeyIndStepSim` obligations for the four state-growing non-session, non-RO query arms
(`initPrin`, `genSPK`, `genOPK`, `registerKey`) across `gdhShadowHandle2Atomic`,
`sigKeyInd1KeyKindAtomicProg`, and `fgKeyInd1KeyGapDhKindAtomicProg`.
-/

set_option autoImplicit false

namespace Computational.Proofs.SignalPqxdh.Security.ReductionDsl.KindSplit.KeyIndGapDhKSimMiscArms

public section

open OracleSpec OracleComp
open _root_.ReductionDsl (
  Ty Var Expr Comp Env Iface CostedReduction pqAtomicSig pqAtomicOps pqKeyIndCodec
)
open _root_.SignalPqxdh (Bytes Setup QueryBudget KeyIndQuery isKeyIndOnlineQuery isKeyIndRoQuery)
open _root_.SignalPqxdh.Security (keyIndQueryKind)
open _root_.SignalPqxdh.Costed (PB)
open _root_.SignalPqxdh.LegacyCosted (pqSig pqxdhOps pqGapDhIface pqSigAndDdhIface B U32 sidT)
open _root_.SignalPqxdh.Security.ReductionDsl.KeyInd (
  PT Ext v letV bindV caseOptV caseSumV eMap eFind eAny findMV anyMV mapMV foldMV
  keyIndStateTy keyIndQueryTy keyIndRespTy spkBundleEntryTy
  paramsTy params2Ty simTy gdhStateTy gdhState2Ty
  paU paV paUp paPrinFlag paPrinIdx paDhFlag paEphIdx paSpkIdx paOpkMode paOpkIdx paMode paMk
  pa2U pa2V pa2Up pa2PrinTarget pa2SpkTarget pa2OpkMode pa2OpkTarget pa2Mode pa2Mk
  smBase smFgL smRaw smLog smPows smMk smUpd
  stPrin stSpks stOpks stSess stResps stUsedO stUsedN stKyb stRo stAdv stUpd
  initPrin1KeyB corruptB genSpkB genOpkB testB revealB revealSpkB
  rNone rInitPrin rBundle
  wrapBase wrapSim wrapBase2 wrapSim2
  initPrinGdh2B genSpkGdh2B genOpkGdh2B registerGdhB gdhHandle2
  sig1KeyStTy s1Fg s1Base s1Target s1Pk s1Budget s1Forgery s1Mk s1Upd
  sig1KeyTargetGenSpkB
)
open _root_.SignalPqxdh.Security.ReductionDsl.KeyInd1KeyGapDh (
  gdh1KeyStateTy liftGdhComp liftGdhComp_eval liftGdhToSign_pure liftGdhToSign_bind
  mem_support_liftGdhToSign twoVarRen pullEnv_twoVarRen renameComp renameComp_eval
)
open Computational.Proofs.ReductionDsl.StepSim (bumpPred bind_congr_support)
open Computational.Proofs.SignalPqxdh.AtomicLift (
  AtomicIface TagLift embedTy embedVal projVal embedEnv
  mapComp mapComp_eval liftKeyIndHandle liftKeyIndHandle_eval liftKeyInd1Stage
  tlGapDhKeyInd tlSigDdhKeyInd
)
open Computational.Proofs.SignalPqxdh.Delta.KeyInd1KeyActiveProgs (
  optNatMatchesE sig1KeyActiveStTy gdh1KeyActiveStateTy saTP saInner
  sig1KeyActiveInitPrinB sig1KeyActivePreDispatchC sig1KeyActiveHandleC
  callGdhActiveHandle initPrin1KeyActiveGdhB genSpkGdhActiveB
  genSpk1KeyActiveGdhB genOpkActiveGdhB gdh1KeyActiveHandle
  sigKeyInd1KeyActiveDslProg sigKeyInd1KeyActiveAtomicProg
  fgKeyInd1KeyGapDhActiveDslProg fgKeyInd1KeyGapDhActiveAtomicProg
)
open Computational.Proofs.SignalPqxdh.Security.ReductionDsl.KindSplit.KeyIndCoreK (
  keyIndSentinel dispatchKeyIndQ runAt2 finPairToNatE finTripleToNatE
)
open Computational.Proofs.SignalPqxdh.Security.ReductionDsl.SplitRo.AvlRoTableDefs (aop)
open Computational.Proofs.SignalPqxdh.Security.ReductionDsl.KindSplit.KeyIndGapDhK (
  KeyIndKFuels keyIndKFuelsOfBudget
  fgShadowAtomicTy simShadowAtomicTy gdhShadowState2AtomicTy forgetGdhShadow2
  GdhAtomicLift gdhLift2Key gdhLift1Key liftGdhAtomic
  liftKind0NoFgArm wrapNoFgArm gdhShadowHandle2Atomic
)
open Computational.Proofs.SignalPqxdh.Delta.KindSplit.KeyInd1KeyKindProgs (
  liftSigDdhNoFgArm
  sigKindInitPrinLeg sigKindGenSpkLeg sigWrapGdh2NoFgLeg sig1KeyKindHandleC
  gdhKindInitPrinLeg gdhKindGenSpkLeg gdhKindGenOpkLeg gdhWrapDelegNoFgLeg gdh1KeyKindHandleC
  sigKeyInd1KeyKindAtomicProg fgKeyInd1KeyGapDhKindAtomicProg
  sig1KeyActiveInitPrinB_unsupported sig1KeyTargetGenSpkB_unsupported
  extract1KeyActiveC_unsupported initPrin1KeyActiveGdhB_unsupported
  genSpk1KeyActiveGdhB_unsupported genOpkActiveGdhB_unsupported
)
open Computational.Proofs.SignalPqxdh.Security.ReductionDsl.KindSplit.KeyIndCoreKSimBase (
  keyIndSimBounds keyIndSimPred keyIndSimPred_zero_iff_kind keyIndSimPred_one_iff_kind fixSent
  beq_fixSent_of_le_mOn
  stPrinList stSpksList stOpksList stSessList stRespsList
  stUsedOList stUsedNList stKybList stRoList stAdvList
  BaseOnlineLenInv dispatchKeyIndQ_eval runAt2_eval
  initPrin1KeyB_min_eq corruptB_min_eq genSpkB_min_eq genOpkB_min_eq
  testB_min_eq revealB_min_eq revealSpkB_min_eq
)
open Computational.Proofs.SignalPqxdh.Security.ReductionDsl.KindSplit.KeyIndGapDhKSimBase (
  GdhAtomicLiftValid gdhLift1Key_valid gdhLift2Key_valid
  fixSig1KeyActiveSent fixParamsSent fixGdh1KeyActiveSent
  forgetSig1KeyActiveK forgetGdh1KeyActiveK
  GdhSimInv Gdh2SimInv Sig1KeyActiveSimInv Gdh1KeyActiveSimInv
  KeyIndStepSim
)

section Arms

set_option allowUnsafeReducibility true
attribute [local implicit_reducible]
  _root_.SignalPqxdh.LegacyCosted.pqChalIface
  _root_.SignalPqxdh.LegacyCosted.pqPrimIface
  _root_.SignalPqxdh.LegacyCosted.pqGapDhIface
  _root_.SignalPqxdh.LegacyCosted.pqSigAndDdhIface
  _root_.SignalPqxdh.LegacyCosted.sigAndDdhOracle
  _root_.SignalPqxdh.sigAndDdhSpec
  _root_.SignalPqxdh.sigOracleSpec
  _root_.SignalPqxdh.gapDhOracleSpec
  _root_.SignalPqxdh.LegacyCosted.gapDhDdhOracle
  sigKeyInd1KeyKindAtomicProg
  fgKeyInd1KeyGapDhKindAtomicProg
  sigKeyInd1KeyActiveAtomicProg
  fgKeyInd1KeyGapDhActiveAtomicProg
  sigKeyInd1KeyActiveDslProg
  fgKeyInd1KeyGapDhActiveDslProg
  _root_.ReductionDsl.CostedReduction.σ
  Env.get

private theorem bumpPred_online_0 {S : Setup} {c : Fin 3 → ℕ} {t : KeyIndQuery S}
    (hOn : keyIndQueryKind t = 0) :
    bumpPred (keyIndSimPred S) c t 0 = c 0 + 1 := by
  simp [bumpPred, keyIndSimPred_zero_iff_kind, hOn]

private theorem bumpPred_online_1 {S : Setup} {c : Fin 3 → ℕ} {t : KeyIndQuery S}
    (hOn : keyIndQueryKind t = 0) :
    bumpPred (keyIndSimPred S) c t 1 = c 1 := by
  simp [bumpPred, keyIndSimPred_one_iff_kind, hOn]

private theorem bumpPred_online_2 {S : Setup} {c : Fin 3 → ℕ} {t : KeyIndQuery S}
    (_hOn : keyIndQueryKind t = 0) :
    bumpPred (keyIndSimPred S) c t 2 = c 2 + 1 := by
  simp [bumpPred, keyIndSimPred]

private theorem BaseOnlineLenInv.upd_online {S : Setup} {c : Fin 3 → ℕ} {t : KeyIndQuery S}
    {bSt bSt' : keyIndStateTy.denote}
    (hInv : BaseOnlineLenInv c bSt) (hOn : keyIndQueryKind t = 0)
    (hPrin  : (stPrinList bSt').length ≤ (stPrinList bSt).length + 1)
    (hSpks  : (stSpksList bSt').length ≤ (stSpksList bSt).length + 1)
    (hOpks  : (stOpksList bSt').length ≤ (stOpksList bSt).length + 1)
    (hSess  : (stSessList bSt').length ≤ (stSessList bSt).length)
    (hResps : (stRespsList bSt').length ≤ (stRespsList bSt).length)
    (hUsedO : (stUsedOList bSt').length ≤ (stUsedOList bSt).length)
    (hUsedN : (stUsedNList bSt').length ≤ (stUsedNList bSt).length)
    (hKyb   : (stKybList bSt').length ≤ (stKybList bSt).length)
    (hAdv   : (stAdvList bSt').length ≤ (stAdvList bSt).length + 1) :
    BaseOnlineLenInv (bumpPred (keyIndSimPred S) c t) bSt' := by
  have h0 := bumpPred_online_0 (c := c) hOn
  have h1 := bumpPred_online_1 (c := c) hOn
  have h2 := bumpPred_online_2 (c := c) hOn
  have hP := hInv.prin_le; have hSp := hInv.spks_le; have hOp := hInv.opks_le
  have hSe := hInv.sess_le; have hRe := hInv.resps_le
  have hUO := hInv.usedO_le; have hUN := hInv.usedN_le
  have hKy := hInv.kyb_le; have hAd := hInv.adv_le; have hCnt := hInv.counts_eq
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> omega

private theorem GdhSimInv.upd_online_base_pows {S : Setup} {b : QueryBudget}
    {c : Fin 3 → ℕ} {t : KeyIndQuery S}
    {sm sm' : simTy.denote} {sh : fgShadowAtomicTy.denote}
    (hInv : GdhSimInv S b c (embedVal simTy sm, sh))
    (hOn : keyIndQueryKind t = 0)
    (hBase : BaseOnlineLenInv (bumpPred (keyIndSimPred S) c t) sm'.1)
    (hFgL  : sm'.2.1 = sm.2.1)
    (hRaw  : sm'.2.2.1 = sm.2.2.1)
    (hLog  : sm'.2.2.2.1 = sm.2.2.2.1)
    (hPows : sm'.2.2.2.2.length ≤ sm.2.2.2.2.length + 1) :
    GdhSimInv S b (bumpPred (keyIndSimPred S) c t) (embedVal simTy sm', sh) := by
  have h0 := bumpPred_online_0 (c := c) hOn
  have h1 := bumpPred_online_1 (c := c) hOn
  have hProj : projVal keyIndStateTy (embedVal simTy sm').1 = sm'.1 :=
    congrArg Prod.fst (AtomicLift.projVal_embedVal simTy sm')
  have hFgEq : (embedVal simTy sm').2.1 = (embedVal simTy sm).2.1 :=
    congrArg (List.map _) hFgL
  have hRawEq : (embedVal simTy sm').2.2.1 = (embedVal simTy sm).2.2.1 :=
    congrArg (List.map _) hRaw
  have hLogEq : (embedVal simTy sm').2.2.2.1 = (embedVal simTy sm).2.2.2.1 :=
    congrArg (List.map _) hLog
  have hPowsOld : sm.2.2.2.2.length ≤ c 0 := by
    have hp := hInv.pows_len
    have hpEq : (embedVal simTy sm).2.2.2.2 = sm.2.2.2.2.map (embedVal (.prod (B 32) (B 32))) := rfl
    rw [hpEq, List.length_map] at hp; exact hp
  have hPowsNew : (embedVal simTy sm').2.2.2.2.length ≤ bumpPred (keyIndSimPred S) c t 0 := by
    have hpEq : (embedVal simTy sm').2.2.2.2 = sm'.2.2.2.2.map (embedVal (.prod (B 32) (B 32))) := rfl
    rw [hpEq, List.length_map]; omega
  refine
    { online_len := hProj ▸ hBase
      fg_sess_le := Nat.le_trans hInv.fg_sess_le (by omega)
      fg_shadow := ?_
      raw_len := by rw [hRawEq, h1]; exact hInv.raw_len
      raw_shadow := hRawEq ▸ hInv.raw_shadow
      log_len := by rw [hLogEq, h1]; exact hInv.log_len
      pows_len := hPowsNew }
  obtain ⟨tagged, hRel, hWf, hRoLe⟩ := hInv.fg_shadow
  exact ⟨tagged, hFgEq ▸ hRel, hWf, h1 ▸ hRoLe⟩

private theorem eFind_eq_of_le {Γ : List PT} {τ : PT} {K₁ K₂ : ℕ}
    (xs : Expr pqxdhOps Γ (.list τ))
    (p : Var (τ :: Γ) τ → Expr pqxdhOps (τ :: Γ) .bool) (env : Env Γ)
    (hLen : (xs.eval env).length ≤ K₁) (hLe : K₁ ≤ K₂) :
    (eFind K₁ xs p).eval env = (eFind K₂ xs p).eval env := by
  simp only [eFind, Expr.eval,
    List.take_of_length_le hLen, List.take_of_length_le (Nat.le_trans hLen hLe)]

private theorem eAny_eq_of_le {Γ : List PT} {τ : PT} {K₁ K₂ : ℕ}
    (xs : Expr pqxdhOps Γ (.list τ))
    (p : Var (τ :: Γ) τ → Expr pqxdhOps (τ :: Γ) .bool) (env : Env Γ)
    (hLen : (xs.eval env).length ≤ K₁) (hLe : K₁ ≤ K₂) :
    (eAny K₁ xs p).eval env = (eAny K₂ xs p).eval env := by
  simp only [eAny, Expr.eval,
    List.take_of_length_le hLen, List.take_of_length_le (Nat.le_trans hLen hLe)]

private theorem initPrinGdh2B_eq_of_le {K₁ K₂ : ℕ}
    {Γ₁ Γ₂ Γ₃ Γ₄ Δ : List PT} [Ext Γ₁ Δ] [Ext Γ₂ Δ] [Ext Γ₃ Δ] [Ext Γ₄ Δ]
    (pa : Var Γ₁ params2Ty) (sm : Var Γ₂ simTy) (bSt : Var Γ₃ keyIndStateTy) (u : Var Γ₄ .nat)
    (env : Env Δ)
    (hLen : (stPrinList ((v bSt).eval env)).length ≤ K₁) (hLe : K₁ ≤ K₂) :
    (initPrinGdh2B K₁ pa sm bSt u).eval env = (initPrinGdh2B K₂ pa sm bSt u).eval env := by
  simp only [initPrinGdh2B, Comp.eval]
  rw [eAny_eq_of_le _ _ _ (by simpa [stPrin, stPrinList, Expr.eval] using hLen) hLe]

private theorem genSpkGdh2B_eq_of_le {K₁ K₂ : ℕ}
    {Γ₁ Γ₂ Γ₃ Γ₄ Δ : List PT} [Ext Γ₁ Δ] [Ext Γ₂ Δ] [Ext Γ₃ Δ] [Ext Γ₄ Δ]
    (pa : Var Γ₁ params2Ty) (sm : Var Γ₂ simTy) (bSt : Var Γ₃ keyIndStateTy)
    (x : Var Γ₄ (.prod .nat .nat)) (env : Env Δ) {c : Fin 3 → ℕ}
    (hInv : BaseOnlineLenInv c ((v bSt).eval env)) (hc : c 0 ≤ K₁) (hLe : K₁ ≤ K₂) :
    (genSpkGdh2B K₁ pa sm bSt x).eval env = (genSpkGdh2B K₂ pa sm bSt x).eval env := by
  have hSpks := Nat.le_trans hInv.spks_le hc
  have hPrin := Nat.le_trans hInv.prin_le hc
  simp only [genSpkGdh2B, caseOptV, Comp.eval]
  rw [eAny_eq_of_le _ _ _ (by simpa [stSpks, stSpksList, Expr.eval] using hSpks) hLe,
      eFind_eq_of_le _ _ _ (by simpa [stPrin, stPrinList, Expr.eval] using hPrin) hLe]

private theorem genOpkGdh2B_eq_of_le {K₁ K₂ : ℕ}
    {Γ₁ Γ₂ Γ₃ Γ₄ Δ : List PT} [Ext Γ₁ Δ] [Ext Γ₂ Δ] [Ext Γ₃ Δ] [Ext Γ₄ Δ]
    (pa : Var Γ₁ params2Ty) (sm : Var Γ₂ simTy) (bSt : Var Γ₃ keyIndStateTy)
    (x : Var Γ₄ (.prod .nat (.prod .nat .nat))) (env : Env Δ)
    (hLen : (stOpksList ((v bSt).eval env)).length ≤ K₁) (hLe : K₁ ≤ K₂) :
    (genOpkGdh2B K₁ pa sm bSt x).eval env = (genOpkGdh2B K₂ pa sm bSt x).eval env := by
  simp only [genOpkGdh2B, Comp.eval]
  rw [eAny_eq_of_le _ _ _ (by simpa [stOpks, stOpksList, Expr.eval] using hLen) hLe]

section LocalUnsupHelpers
open _root_.SignalPqxdh.LegacyCosted (
  pqChalIface pqPrimIface gapDhDdhOracle sigAndDdhOracle pqSamplers bundleT
)
open _root_.SignalPqxdh.Security.ReductionDsl.KeyInd (
  sBool sBytes32 sRandom64 sDrKey96 sIndex
  qX25519 qX25519Base qPow8 qIsCanonical qSigPkGen qSigSign qSigVerify
  qKemKeyGen qKemEncaps qKemDecaps qHkdfDerive96
  gPrim liftBase ddhQ s1Prim qSigDdhSign liftGdhToSigDdh
  findHonestC isAdvRegC isGameSpkC isGameOpkC
  koskBundleOkC koskSenderOkC resolveSigPkC honestPeerC checkProvC
  keyIndSessionEntryTy keyIndRespEntryTy partnerC recordRespC accInpTy acceptKeysC
  preCheckC checkSigsC preKeyBundleTy koskSenderOkPowsC koskBundleOkPowsC lookupSpkSkC
  chooseRespRandC chooseInitRandC mkSecretPosC mkPairPosC computePosC computeOptPosInitC
  fgPosTy ddhEqC ddhEqOptC fgPatchEntryTy entryMatchesC fgPatchC
  initiateGdh2B acceptOpkGdh2B acceptNoOpkGdhB finishAcceptGdhC roParsedC roRawFallbackC
)
open Computational.Proofs.SignalPqxdh.AtomicLift (keyIndUnsupportedPrimW)
set_option allowUnsafeReducibility true in
attribute [local implicit_reducible] pqChalIface pqPrimIface pqGapDhIface pqSigAndDdhIface gapDhDdhOracle sigAndDdhOracle pqSamplers
@[local simp] private theorem letV_queries' {ι : Type} {T : OracleSpec ι} {I : Iface pqSig T}
    {Γ : List PT} {a b : PT} (w : I.Tag → ℕ) (ws : I.smp.Samp → ℕ)
    (e : Expr pqxdhOps Γ a) (k : Var (a :: Γ) a → Comp pqxdhOps I (a :: Γ) b) :
    (letV e k).queries w ws = (k .zero).queries w ws := by simp [letV, Comp.queries]
@[local simp] private theorem bindV_queries' {ι : Type} {T : OracleSpec ι} {I : Iface pqSig T}
    {Γ : List PT} {a b : PT} (w : I.Tag → ℕ) (ws : I.smp.Samp → ℕ)
    (c : Comp pqxdhOps I Γ a) (k : Var (a :: Γ) a → Comp pqxdhOps I (a :: Γ) b) :
    (bindV c k).queries w ws = c.queries w ws + (k .zero).queries w ws := rfl
@[local simp] private theorem caseOptV_queries' {ι : Type} {T : OracleSpec ι} {I : Iface pqSig T}
    {Γ : List PT} {a b : PT} (w : I.Tag → ℕ) (ws : I.smp.Samp → ℕ)
    (e : Expr pqxdhOps Γ (.opt a)) (cNone : Comp pqxdhOps I Γ b)
    (cSome : Var (a :: Γ) a → Comp pqxdhOps I (a :: Γ) b) :
    (caseOptV e cNone cSome).queries w ws = max (cNone.queries w ws) ((cSome .zero).queries w ws) := rfl
@[local simp] private theorem caseSumV_queries' {ι : Type} {T : OracleSpec ι} {I : Iface pqSig T}
    {Γ : List PT} {a b c : PT} (w : I.Tag → ℕ) (ws : I.smp.Samp → ℕ)
    (e : Expr pqxdhOps Γ (.sum a b))
    (cL : Var (a :: Γ) a → Comp pqxdhOps I (a :: Γ) c)
    (cR : Var (b :: Γ) b → Comp pqxdhOps I (b :: Γ) c) :
    (caseSumV e cL cR).queries w ws = max ((cL .zero).queries w ws) ((cR .zero).queries w ws) := rfl
@[local simp] private theorem findMV_queries' {ι : Type} {T : OracleSpec ι} {I : Iface pqSig T}
    {Γ : List PT} {a : PT} (w : I.Tag → ℕ) (ws : I.smp.Samp → ℕ) (fuel : ℕ)
    (xs : Expr pqxdhOps Γ (.list a)) (p : Var (a :: Γ) a → Comp pqxdhOps I (a :: Γ) .bool) :
    (findMV fuel xs p).queries w ws = fuel * (p .zero).queries w ws := by simp [findMV, Comp.queries]
@[local simp] private theorem anyMV_queries' {ι : Type} {T : OracleSpec ι} {I : Iface pqSig T}
    {Γ : List PT} {a : PT} (w : I.Tag → ℕ) (ws : I.smp.Samp → ℕ) (fuel : ℕ)
    (xs : Expr pqxdhOps Γ (.list a)) (p : Var (a :: Γ) a → Comp pqxdhOps I (a :: Γ) .bool) :
    (anyMV fuel xs p).queries w ws = fuel * (p .zero).queries w ws := by simp [anyMV, Comp.queries]
private abbrev zPrimWS : pqPrimIface.smp.Samp → ℕ := fun _ => 0
private abbrev zGapDhW : pqGapDhIface.Tag → ℕ := tlGapDhKeyInd.unsupportedW
private abbrev zGapDhWS : pqGapDhIface.smp.Samp → ℕ := fun _ => 0
private abbrev zSigDdhW : _root_.SignalPqxdh.LegacyCosted.pqSigAndDdhIface.Tag → ℕ := tlSigDdhKeyInd.unsupportedW
private abbrev zSigDdhWS : _root_.SignalPqxdh.LegacyCosted.pqSigAndDdhIface.smp.Samp → ℕ := fun _ => 0
@[local simp] private theorem sBool_unsup {Γ : List PT} : (sBool (Γ := Γ)).queries keyIndUnsupportedPrimW zPrimWS = 0 := rfl
@[local simp] private theorem sBytes32_unsup {Γ : List PT} : (sBytes32 (Γ := Γ)).queries keyIndUnsupportedPrimW zPrimWS = 0 := rfl
@[local simp] private theorem sRandom64_unsup {Γ : List PT} : (sRandom64 (Γ := Γ)).queries keyIndUnsupportedPrimW zPrimWS = 0 := rfl
@[local simp] private theorem sDrKey96_unsup {Γ : List PT} : (sDrKey96 (Γ := Γ)).queries keyIndUnsupportedPrimW zPrimWS = 0 := rfl
@[local simp] private theorem sIndex_unsup (N : ℕ) {Γ : List PT} : (sIndex N (Γ := Γ)).queries keyIndUnsupportedPrimW zPrimWS = 0 := rfl
@[local simp] private theorem qX25519_unsup {Γ : List PT} (e : Expr pqxdhOps Γ (.prod (B 32) (B 32))) : (qX25519 e).queries keyIndUnsupportedPrimW zPrimWS = 0 := rfl
@[local simp] private theorem qX25519Base_unsup {Γ : List PT} (e : Expr pqxdhOps Γ (B 32)) : (qX25519Base e).queries keyIndUnsupportedPrimW zPrimWS = 0 := rfl
@[local simp] private theorem qPow8_unsup {Γ : List PT} (e : Expr pqxdhOps Γ (B 32)) : (qPow8 e).queries keyIndUnsupportedPrimW zPrimWS = 0 := rfl
@[local simp] private theorem qIsCanonical_unsup {Γ : List PT} (e : Expr pqxdhOps Γ (B 32)) : (qIsCanonical e).queries keyIndUnsupportedPrimW zPrimWS = 0 := rfl
@[local simp] private theorem qSigPkGen_unsup {Γ : List PT} (e : Expr pqxdhOps Γ (B 32)) : (qSigPkGen e).queries keyIndUnsupportedPrimW zPrimWS = 0 := rfl
@[local simp] private theorem qSigSign_unsup (m : ℕ+) {Γ : List PT} (e : Expr pqxdhOps Γ (.prod (B 32) (.prod (B m) (B 64)))) : (qSigSign m e).queries keyIndUnsupportedPrimW zPrimWS = 0 := rfl
@[local simp] private theorem qSigVerify_unsup (m : ℕ+) {Γ : List PT} (e : Expr pqxdhOps Γ (.prod (B 32) (.prod (B m) (B 64)))) : (qSigVerify m e).queries keyIndUnsupportedPrimW zPrimWS = 0 := rfl
@[local simp] private theorem qKemKeyGen_unsup {Γ : List PT} (e : Expr pqxdhOps Γ (B 64)) : (qKemKeyGen e).queries keyIndUnsupportedPrimW zPrimWS = 0 := rfl
@[local simp] private theorem qKemEncaps_unsup {Γ : List PT} (e : Expr pqxdhOps Γ (.prod (B 1568) (B 32))) : (qKemEncaps e).queries keyIndUnsupportedPrimW zPrimWS = 0 := rfl
@[local simp] private theorem qKemDecaps_unsup {Γ : List PT} (e : Expr pqxdhOps Γ (.prod (B 3168) (B 1568))) : (qKemDecaps e).queries keyIndUnsupportedPrimW zPrimWS = 0 := rfl
@[local simp] private theorem qHkdfDerive96_unsup (w : ℕ+) {Γ : List PT} (e : Expr pqxdhOps Γ (B w)) : (qHkdfDerive96 w e).queries keyIndUnsupportedPrimW zPrimWS = 0 := rfl
@[local simp] private theorem gPrim_unsup {Γ : List PT} {t : PT} (c : Comp pqxdhOps pqPrimIface Γ t) :
    (gPrim c).queries zGapDhW zGapDhWS = c.queries keyIndUnsupportedPrimW zPrimWS := by
  unfold gPrim; induction c with | query _ _ => rfl | sample _ _ => rfl | _ => simp_all [liftBase, Comp.queries]
@[local simp] private theorem ddhQ_unsup {Γ : List PT} (x y z : Expr pqxdhOps Γ (B 32)) : (ddhQ x y z).queries zGapDhW zGapDhWS = 0 := rfl
@[local simp] private theorem s1Prim_unsup {Γ : List PT} {t : PT} (c : Comp pqxdhOps pqPrimIface Γ t) :
    (s1Prim c).queries zSigDdhW zSigDdhWS = c.queries keyIndUnsupportedPrimW zPrimWS := by
  unfold s1Prim; induction c with | query _ _ => rfl | sample _ _ => rfl | _ => simp_all [liftBase, Comp.queries]
@[local simp] private theorem qSigDdhSign_unsup (m : ℕ+) {Γ : List PT} (msg : Expr pqxdhOps Γ (B m)) : (qSigDdhSign m msg).queries zSigDdhW zSigDdhWS = 0 := rfl
@[local simp] private theorem liftGdhToSigDdh_unsup {Γ : List PT} {t : PT} (c : Comp pqxdhOps pqGapDhIface Γ t) :
    (liftGdhToSigDdh c).queries zSigDdhW zSigDdhWS = c.queries zGapDhW zGapDhWS := by
  induction c with | query g _ => (rcases g with _ | ⟨⟩ <;> rfl) | sample _ _ => rfl | _ => simp_all [liftGdhToSigDdh, Comp.queries]
@[local simp] private theorem wrapBase2_unsup {Γ₁ Γ₂ Δ : List PT} [Ext Γ₁ Δ] [Ext Γ₂ Δ] (pa : Var Γ₁ params2Ty) (sm : Var Γ₂ simTy)
    (c : Comp pqxdhOps pqPrimIface Δ (.prod keyIndRespTy keyIndStateTy)) :
    (wrapBase2 pa sm c).queries zGapDhW zGapDhWS = c.queries keyIndUnsupportedPrimW zPrimWS := by simp [wrapBase2, bindV, Comp.queries]
@[local simp] private theorem wrapSim2_unsup {Γ₁ Δ : List PT} [Ext Γ₁ Δ] (pa : Var Γ₁ params2Ty) (c : Comp pqxdhOps pqGapDhIface Δ (.prod keyIndRespTy simTy)) :
    (wrapSim2 pa c).queries zGapDhW zGapDhWS = c.queries zGapDhW zGapDhWS := by simp [wrapSim2, bindV, Comp.queries]
@[local simp] private theorem findHonestC_unsup (S : Setup) (K : Nat) {Γ Δ : List PT} (st : Var Γ keyIndStateTy) [Ext Γ Δ] (ik : Expr pqxdhOps Δ (B 32)) :
    (findHonestC S K st ik).queries keyIndUnsupportedPrimW zPrimWS = 0 := by simp [findHonestC, Comp.queries]
@[local simp] private theorem isAdvRegC_unsup (K : Nat) {Γ Δ : List PT} (st : Var Γ keyIndStateTy) [Ext Γ Δ] (pk : Expr pqxdhOps Δ (B 32)) :
    (isAdvRegC K st pk).queries keyIndUnsupportedPrimW zPrimWS = 0 := by simp [isAdvRegC, Comp.queries]
@[local simp] private theorem isGameSpkC_unsup (S : Setup) (K : Nat) {Γ Δ : List PT} (st : Var Γ keyIndStateTy) [Ext Γ Δ] (pk : Expr pqxdhOps Δ (B 32)) :
    (isGameSpkC S K st pk).queries keyIndUnsupportedPrimW zPrimWS = 0 := by simp [isGameSpkC, Comp.queries]
@[local simp] private theorem isGameOpkC_unsup (S : Setup) (K : Nat) {Γ Δ : List PT} (st : Var Γ keyIndStateTy) [Ext Γ Δ] (pk : Expr pqxdhOps Δ (B 32)) :
    (isGameOpkC S K st pk).queries keyIndUnsupportedPrimW zPrimWS = 0 := by simp [isGameOpkC, Comp.queries]
@[local simp] private theorem koskBundleOkC_unsup (S : Setup) (K : Nat) {Γ₁ Γ₂ Δ : List PT} (st : Var Γ₁ keyIndStateTy) (bu : Var Γ₂ bundleT) [Ext Γ₁ Δ] [Ext Γ₂ Δ] :
    (koskBundleOkC (Δ := Δ) S K st bu).queries keyIndUnsupportedPrimW zPrimWS = 0 := by simp [koskBundleOkC, Comp.queries]
@[local simp] private theorem koskSenderOkC_unsup (S : Setup) (K : Nat) {Γ Δ : List PT} (st : Var Γ keyIndStateTy) [Ext Γ Δ] (ik : Expr pqxdhOps Δ (B 32)) :
    (koskSenderOkC S K st ik).queries keyIndUnsupportedPrimW zPrimWS = 0 := by simp [koskSenderOkC, Comp.queries]
@[local simp] private theorem resolveSigPkC_unsup (S : Setup) (K : Nat) {Γ Δ : List PT} (st : Var Γ keyIndStateTy) [Ext Γ Δ] (ik : Expr pqxdhOps Δ (B 32)) :
    (resolveSigPkC S K st ik).queries keyIndUnsupportedPrimW zPrimWS = 0 := by simp [resolveSigPkC, Comp.queries]
@[local simp] private theorem honestPeerC_unsup (S : Setup) (K : Nat) {Γ Δ : List PT} (st : Var Γ keyIndStateTy) [Ext Γ Δ] (ik : Expr pqxdhOps Δ (B 32)) :
    (honestPeerC S K st ik).queries keyIndUnsupportedPrimW zPrimWS = 0 := by simp [honestPeerC, Comp.queries]
@[local simp] private theorem checkProvC_unsup (S : Setup) (K : Nat) {Γ₁ Γ₂ Δ : List PT} (st : Var Γ₁ keyIndStateTy) (bu : Var Γ₂ bundleT) [Ext Γ₁ Δ] [Ext Γ₂ Δ] :
    (checkProvC (Δ := Δ) S K st bu).queries keyIndUnsupportedPrimW zPrimWS = 0 := by simp [checkProvC, Comp.queries]
@[local simp] private theorem partnerC_unsup {Γ₁ Γ₂ Δ : List PT} (s : Var Γ₁ keyIndSessionEntryTy) (r : Var Γ₂ keyIndRespEntryTy) [Ext Γ₁ Δ] [Ext Γ₂ Δ] :
    (partnerC (Δ := Δ) s r).queries keyIndUnsupportedPrimW zPrimWS = 0 := rfl
@[local simp] private theorem recordRespC_unsup (S : Setup) (K : Nat) {Δ : List PT} (p : Expr pqxdhOps Δ (.prod keyIndRespEntryTy keyIndStateTy)) :
    (recordRespC S K p).queries keyIndUnsupportedPrimW zPrimWS = 0 := by simp [recordRespC, Comp.queries]
@[local simp] private theorem acceptKeysC_unsup {Δ : List PT} (inp : Expr pqxdhOps Δ accInpTy) :
    (acceptKeysC inp).queries keyIndUnsupportedPrimW zPrimWS = 0 := rfl
@[local simp] private theorem preCheckC_unsup (S : Setup) (K : Nat) {Γ₁ Γ₂ Γ₃ Γ₄ Δ : List PT}
    (st : Var Γ₁ keyIndStateTy) (sid : Var Γ₂ sidT) (u : Var Γ₃ .nat) (bu : Var Γ₄ bundleT) [Ext Γ₁ Δ] [Ext Γ₂ Δ] [Ext Γ₃ Δ] [Ext Γ₄ Δ] :
    (preCheckC (Δ := Δ) S K st sid u bu).queries keyIndUnsupportedPrimW zPrimWS = 0 := by simp [preCheckC, Comp.queries]
@[local simp] private theorem checkSigsC_unsup (S : Setup) (K : Nat) {Γ₁ Γ₂ Δ : List PT} (st : Var Γ₁ keyIndStateTy) (bu : Var Γ₂ bundleT) [Ext Γ₁ Δ] [Ext Γ₂ Δ] :
    (checkSigsC (Δ := Δ) S K st bu).queries keyIndUnsupportedPrimW zPrimWS = 0 := by simp [checkSigsC, Comp.queries]
@[local simp] private theorem koskSenderOkPowsC_unsup (S : Setup) (K : Nat) {Γ Δ : List PT} [Ext Γ Δ] (st : Var Γ keyIndStateTy)
    (pows : Expr pqxdhOps Δ (.list (.prod (B 32) (B 32)))) (ik : Expr pqxdhOps Δ (B 32)) :
    (koskSenderOkPowsC S K st pows ik).queries keyIndUnsupportedPrimW zPrimWS = 0 := by simp [koskSenderOkPowsC, Comp.queries]
@[local simp] private theorem koskBundleOkPowsC_unsup (S : Setup) (K : Nat) {Γ₁ Γ₂ Δ : List PT} [Ext Γ₁ Δ] [Ext Γ₂ Δ] (st : Var Γ₁ keyIndStateTy)
    (pows : Expr pqxdhOps Δ (.list (.prod (B 32) (B 32)))) (bu : Var Γ₂ preKeyBundleTy) :
    (koskBundleOkPowsC S K st pows bu).queries keyIndUnsupportedPrimW zPrimWS = 0 := by simp [koskBundleOkPowsC, Comp.queries]
@[local simp] private theorem lookupSpkSkC_unsup (S : Setup) (K : Nat) {Γ Δ : List PT} [Ext Γ Δ] (st : Var Γ keyIndStateTy)
    (pows : Expr pqxdhOps Δ (.list (.prod (B 32) (B 32)))) (spkPk : Expr pqxdhOps Δ (B 32)) :
    (lookupSpkSkC S K st pows spkPk).queries keyIndUnsupportedPrimW zPrimWS = 0 := by simp [lookupSpkSkC, Comp.queries]
@[local simp] private theorem chooseRespRandC_unsup (S : Setup) (K : Nat) {Γ Δ : List PT} [Ext Γ Δ] (st : Var Γ keyIndStateTy) (r : Var Δ keyIndRespEntryTy) :
    (chooseRespRandC S K st r).queries zGapDhW zGapDhWS = 0 := by simp [chooseRespRandC, Comp.queries]
@[local simp] private theorem chooseInitRandC_unsup (S : Setup) (K : Nat) {Γ Δ : List PT} [Ext Γ Δ] (st : Var Γ keyIndStateTy) (s : Var Δ keyIndSessionEntryTy) :
    (chooseInitRandC S K st s).queries zGapDhW zGapDhWS = 0 := by simp [chooseInitRandC, Comp.queries]
@[local simp] private theorem mkSecretPosC_unsup {Γ : List PT} (z : Expr pqxdhOps Γ (B 32)) : (mkSecretPosC z).queries zGapDhW zGapDhWS = 0 := by simp [mkSecretPosC, Comp.queries]
@[local simp] private theorem mkPairPosC_unsup {Γ : List PT} (pk1 pk2 : Expr pqxdhOps Γ (B 32)) : (mkPairPosC pk1 pk2).queries zGapDhW zGapDhWS = 0 := by simp [mkPairPosC, Comp.queries]
@[local simp] private theorem computePosC_unsup {Γ : List PT} (sk1 sk2 pk1 pk2 : Expr pqxdhOps Γ (B 32)) : (computePosC sk1 sk2 pk1 pk2).queries zGapDhW zGapDhWS = 0 := by simp [computePosC, Comp.queries]
@[local simp] private theorem computeOptPosInitC_unsup {Γ : List PT} (sk1 pk1 : Expr pqxdhOps Γ (B 32)) (opkB? : Expr pqxdhOps Γ (.opt (.prod U32 (B 32)))) :
    (computeOptPosInitC sk1 pk1 opkB?).queries zGapDhW zGapDhWS = 0 := by simp [computeOptPosInitC, Comp.queries]
@[local simp] private theorem ddhEqC_unsup {Γ : List PT} (p1 p2 : Expr pqxdhOps Γ fgPosTy) : (ddhEqC p1 p2).queries zGapDhW zGapDhWS = 0 := by simp [ddhEqC, Comp.queries]
@[local simp] private theorem ddhEqOptC_unsup {Γ : List PT} (p1? p2? : Expr pqxdhOps Γ (.opt fgPosTy)) : (ddhEqOptC p1? p2?).queries zGapDhW zGapDhWS = 0 := by simp [ddhEqOptC, Comp.queries]
@[local simp] private theorem entryMatchesC_unsup {Γ₁ Γ₂ Γ₃ Γ₄ Γ₅ Δ : List PT} [Ext Γ₁ Δ] [Ext Γ₂ Δ] [Ext Γ₃ Δ] [Ext Γ₄ Δ] [Ext Γ₅ Δ]
    (pos1 : Var Γ₁ fgPosTy) (pos2 : Var Γ₂ fgPosTy) (pos3 : Var Γ₃ fgPosTy) (pos4? : Var Γ₄ (.opt fgPosTy)) (ss : Var Γ₅ (B 32)) (e : Var Δ fgPatchEntryTy) :
    (entryMatchesC pos1 pos2 pos3 pos4? ss e).queries zGapDhW zGapDhWS = 0 := by simp [entryMatchesC, Comp.queries]
@[local simp] private theorem fgPatchC_unsup (K : Nat) {Γ₁ Γ₂ Γ₃ Γ₄ Γ₅ Δ : List PT} [Ext Γ₁ Δ] [Ext Γ₂ Δ] [Ext Γ₃ Δ] [Ext Γ₄ Δ] [Ext Γ₅ Δ]
    (pos1 : Var Γ₁ fgPosTy) (pos2 : Var Γ₂ fgPosTy) (pos3 : Var Γ₃ fgPosTy) (pos4? : Var Γ₄ (.opt fgPosTy)) (ss : Var Γ₅ (B 32)) (fgL : Expr pqxdhOps Δ (.list fgPatchEntryTy)) :
    (fgPatchC K pos1 pos2 pos3 pos4? ss fgL).queries zGapDhW zGapDhWS = 0 := by simp [fgPatchC, Comp.queries]

private theorem gdhHandle2_unsupported (S : Setup) (K : Nat) :
    (gdhHandle2 S K).queries tlGapDhKeyInd.unsupportedW (fun _ => 0) = 0 := by
  change (gdhHandle2 S K).queries zGapDhW zGapDhWS = 0
  simp [gdhHandle2, initPrinGdh2B, genSpkGdh2B, genOpkGdh2B, initiateGdh2B, acceptOpkGdh2B,
    acceptNoOpkGdhB, finishAcceptGdhC, corruptB, testB, roParsedC, roRawFallbackC,
    revealB, registerGdhB, revealSpkB, letV, bindV, caseOptV, caseSumV, Comp.queries]

private theorem wrapNoFg_initPrinGdh2B_unsup (K : Nat) :
    (wrapNoFgArm (qPayTy := .nat) fun pa sm bSt u => wrapSim2 pa (initPrinGdh2B K pa sm bSt u)).queries
      tlGapDhKeyInd.unsupportedW (fun _ => 0) = 0 := by
  change (wrapNoFgArm fun pa sm bSt u => wrapSim2 pa (initPrinGdh2B K pa sm bSt u)).queries zGapDhW zGapDhWS = 0
  simp [wrapNoFgArm, initPrinGdh2B, Comp.queries]

private theorem wrapNoFg_genSpkGdh2B_unsup (K : Nat) :
    (wrapNoFgArm (qPayTy := .prod .nat .nat) fun pa sm bSt x => wrapSim2 pa (genSpkGdh2B K pa sm bSt x)).queries
      tlGapDhKeyInd.unsupportedW (fun _ => 0) = 0 := by
  change (wrapNoFgArm fun pa sm bSt x => wrapSim2 pa (genSpkGdh2B K pa sm bSt x)).queries zGapDhW zGapDhWS = 0
  simp [wrapNoFgArm, genSpkGdh2B, Comp.queries]

private theorem wrapNoFg_genOpkGdh2B_unsup (K : Nat) :
    (wrapNoFgArm (qPayTy := .prod .nat (.prod .nat .nat)) fun pa sm bSt x => wrapSim2 pa (genOpkGdh2B K pa sm bSt x)).queries
      tlGapDhKeyInd.unsupportedW (fun _ => 0) = 0 := by
  change (wrapNoFgArm fun pa sm bSt x => wrapSim2 pa (genOpkGdh2B K pa sm bSt x)).queries zGapDhW zGapDhWS = 0
  simp [wrapNoFgArm, genOpkGdh2B, Comp.queries]

private theorem wrapNoFg_registerGdhB_unsup :
    (wrapNoFgArm (qPayTy := B 32) fun pa sm bSt sk => wrapSim2 pa (registerGdhB sm bSt sk)).queries
      tlGapDhKeyInd.unsupportedW (fun _ => 0) = 0 := by
  change (wrapNoFgArm fun pa sm bSt sk => wrapSim2 pa (registerGdhB sm bSt sk)).queries zGapDhW zGapDhWS = 0
  simp [wrapNoFgArm, registerGdhB, Comp.queries]

private theorem sig1KeyActiveHandleC_unsupported (S : Setup) (K : Nat) :
    (sig1KeyActiveHandleC S K).queries tlSigDdhKeyInd.unsupportedW (fun _ => 0) = 0 := by
  have hGdh : ∀ {Δ} (ρ : ∀ {τ}, Var [gdhState2Ty, keyIndQueryTy] τ → Var Δ τ),
      (liftGdhToSigDdh ((gdhHandle2 S K).rename ρ)).queries zSigDdhW zSigDdhWS = 0 := by
    intro Δ ρ
    rw [liftGdhToSigDdh_unsup, _root_.ReductionDsl.Comp.rename_queries]
    exact gdhHandle2_unsupported S K
  have hInit := @sig1KeyActiveInitPrinB_unsupported K
  have hSpk := @sig1KeyTargetGenSpkB_unsupported K
  have hExt := @extract1KeyActiveC_unsupported S K
  simp only [sig1KeyActiveHandleC, sig1KeyActivePreDispatchC,
    Computational.Proofs.SignalPqxdh.Delta.KeyInd1KeyActiveProgs.sig1KeyActiveInitiateCheckC,
    letV_queries', bindV_queries', caseSumV_queries', Comp.queries,
    hGdh, hInit, hSpk, hExt, max_self, Nat.add_zero]

private theorem sigKindInitPrinLeg_unsupported (K : Nat) :
    (sigKindInitPrinLeg K).queries tlSigDdhKeyInd.unsupportedW (fun _ => 0) = 0 := by
  simpa [sigKindInitPrinLeg, Comp.queries] using
    (sig1KeyActiveInitPrinB_unsupported K (st := .zero) (u := .succ .zero))

private theorem sigKindGenSpkLeg_unsupported (K : Nat) :
    (sigKindGenSpkLeg K).queries tlSigDdhKeyInd.unsupportedW (fun _ => 0) = 0 := by
  change (sigKindGenSpkLeg K).queries zSigDdhW zSigDdhWS = 0
  have hSpk := @sig1KeyTargetGenSpkB_unsupported K
  simp [sigKindGenSpkLeg, genSpkGdh2B, hSpk, Comp.queries]
end LocalUnsupHelpers

private theorem baseOnlineLenInv_of_gdhSimInv {S : Setup} {b : QueryBudget}
    {c : Fin 3 → ℕ} {sm : simTy.denote} {sh : fgShadowAtomicTy.denote}
    (hInv : GdhSimInv S b c (embedVal simTy sm, sh)) :
    BaseOnlineLenInv c sm.1 :=
  (congrArg Prod.fst (AtomicLift.projVal_embedVal simTy sm)) ▸ hInv.online_len

private theorem c0_le_kOn {S : Setup} {b : QueryBudget} {c : Fin 3 → ℕ}
    {bSt : keyIndStateTy.denote} (hBase : BaseOnlineLenInv c bSt)
    (hB : ∀ j, c j ≤ keyIndSimBounds b j) :
    c 0 ≤ (keyIndKFuelsOfBudget S b).kOn := by
  have h0 := hB 0
  have h2 := hB 2
  have hCnt := hBase.counts_eq
  dsimp only [keyIndSimBounds, keyIndKFuelsOfBudget] at h0 h2 ⊢
  omega

private theorem kOn_le_q_total (S : Setup) (b : QueryBudget) :
    (keyIndKFuelsOfBudget S b).kOn ≤ b.q_total :=
  Nat.min_le_right _ _

private theorem gdhSimInv_unchanged_online {S : Setup} {b : QueryBudget}
    {c : Fin 3 → ℕ} {t : KeyIndQuery S}
    {sm : simTy.denote} {sh : fgShadowAtomicTy.denote}
    (hInv : GdhSimInv S b c (embedVal simTy sm, sh))
    (hOn : keyIndQueryKind t = 0) :
    GdhSimInv S b (bumpPred (keyIndSimPred S) c t) (embedVal simTy sm, sh) := by
  have hBase := baseOnlineLenInv_of_gdhSimInv hInv
  exact GdhSimInv.upd_online_base_pows hInv hOn
    (BaseOnlineLenInv.upd_online hBase hOn (Nat.le_succ _) (Nat.le_succ _) (Nat.le_succ _)
      (Nat.le_refl _) (Nat.le_refl _) (Nat.le_refl _) (Nat.le_refl _) (Nat.le_refl _)
      (Nat.le_succ _))
    rfl rfl rfl (Nat.le_succ _)

private theorem initPrinGdh2B_inv {S : Setup} {b : QueryBudget} {K : ℕ}
    {Γ₁ Γ₂ Γ₃ Γ₄ Δ : List PT} [Ext Γ₁ Δ] [Ext Γ₂ Δ] [Ext Γ₃ Δ] [Ext Γ₄ Δ]
    (pa : Var Γ₁ params2Ty) (sm : Var Γ₂ simTy) (bSt : Var Γ₃ keyIndStateTy) (u : Var Γ₄ .nat)
    (env : Env Δ) {c : Fin 3 → ℕ} {t : KeyIndQuery S}
    {smVal : simTy.denote} {sh : fgShadowAtomicTy.denote}
    (hSm : (v sm).eval env = smVal) (hBSt : (v bSt).eval env = smVal.1)
    (hInv : GdhSimInv S b c (embedVal simTy smVal, sh))
    (hOn : keyIndQueryKind t = 0)
    {p : (keyIndRespTy.prod simTy).denote}
    (hp : p ∈ support ((initPrinGdh2B K pa sm bSt u).eval env)) :
    GdhSimInv S b (bumpPred (keyIndSimPred S) c t) (embedVal simTy p.2, sh) := by
  have hBase := baseOnlineLenInv_of_gdhSimInv hInv
  unfold initPrinGdh2B at hp
  simp only [Comp.eval] at hp
  split_ifs at hp
  · simp only [mem_support_pure_iff, Expr.eval] at hp
    rw [hp, hSm]; exact gdhSimInv_unchanged_online hInv hOn
  · simp only [letV, bindV, Comp.eval, pure_bind, mem_support_bind_iff, mem_support_pure_iff] at hp
    rcases hp with ⟨sk0, _, pk0, _, skS, _, pkS, _, rfl⟩
    simp only [v, Expr.eval] at hSm hBSt
    refine GdhSimInv.upd_online_base_pows hInv hOn ?_ ?_ ?_ ?_ ?_
    · refine BaseOnlineLenInv.upd_online hBase hOn ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ <;>
        simp only [smUpd, smMk, stUpd, _root_.SignalPqxdh.Security.ReductionDsl.KeyInd.stMk,
          stPrin, stSpks, stOpks, stSess, stResps, stUsedO, stUsedN,
          stKyb, stAdv, smFgL, smRaw, smLog, smPows,
          stPrinList, stSpksList, stOpksList, stSessList, stRespsList, stUsedOList, stUsedNList,
          stKybList, stAdvList, v,
          _root_.SignalPqxdh.Security.ReductionDsl.KeyInd.Ext.step_wk',
          _root_.SignalPqxdh.Security.ReductionDsl.KeyInd.Ext.refl_wk',
          _root_.SignalPqxdh.Security.ReductionDsl.KeyInd.Env.get_succ',
          Expr.eval, hBSt, List.length_cons, Nat.le_refl, Nat.le_succ]
    · simp only [smUpd, smMk, smFgL, v, _root_.SignalPqxdh.Security.ReductionDsl.KeyInd.Ext.step_wk',
        _root_.SignalPqxdh.Security.ReductionDsl.KeyInd.Ext.refl_wk',
        _root_.SignalPqxdh.Security.ReductionDsl.KeyInd.Env.get_succ', Expr.eval, hSm]
    · simp only [smUpd, smMk, smRaw, v, _root_.SignalPqxdh.Security.ReductionDsl.KeyInd.Ext.step_wk',
        _root_.SignalPqxdh.Security.ReductionDsl.KeyInd.Ext.refl_wk',
        _root_.SignalPqxdh.Security.ReductionDsl.KeyInd.Env.get_succ', Expr.eval, hSm]
    · simp only [smUpd, smMk, smLog, v, _root_.SignalPqxdh.Security.ReductionDsl.KeyInd.Ext.step_wk',
        _root_.SignalPqxdh.Security.ReductionDsl.KeyInd.Ext.refl_wk',
        _root_.SignalPqxdh.Security.ReductionDsl.KeyInd.Env.get_succ', Expr.eval, hSm]
    · simp only [smUpd, smMk, smPows, v, _root_.SignalPqxdh.Security.ReductionDsl.KeyInd.Ext.step_wk',
        _root_.SignalPqxdh.Security.ReductionDsl.KeyInd.Ext.refl_wk',
        _root_.SignalPqxdh.Security.ReductionDsl.KeyInd.Env.get_succ', Expr.eval, hSm, Nat.le_succ]

private theorem genSpkGdh2B_inv {S : Setup} {b : QueryBudget} {K : ℕ}
    {Γ₁ Γ₂ Γ₃ Γ₄ Δ : List PT} [Ext Γ₁ Δ] [Ext Γ₂ Δ] [Ext Γ₃ Δ] [Ext Γ₄ Δ]
    (pa : Var Γ₁ params2Ty) (sm : Var Γ₂ simTy) (bSt : Var Γ₃ keyIndStateTy)
    (x : Var Γ₄ (.prod .nat .nat)) (env : Env Δ) {c : Fin 3 → ℕ} {t : KeyIndQuery S}
    {smVal : simTy.denote} {sh : fgShadowAtomicTy.denote}
    (hSm : (v sm).eval env = smVal) (hBSt : (v bSt).eval env = smVal.1)
    (hInv : GdhSimInv S b c (embedVal simTy smVal, sh))
    (hOn : keyIndQueryKind t = 0)
    {p : (keyIndRespTy.prod simTy).denote}
    (hp : p ∈ support ((genSpkGdh2B K pa sm bSt x).eval env)) :
    GdhSimInv S b (bumpPred (keyIndSimPred S) c t) (embedVal simTy p.2, sh) := by
  have hBase := baseOnlineLenInv_of_gdhSimInv hInv
  unfold genSpkGdh2B at hp
  simp only [caseOptV, Comp.eval] at hp
  split_ifs at hp
  · simp only [mem_support_pure_iff, Expr.eval] at hp
    rw [hp, hSm]; exact gdhSimInv_unchanged_online hInv hOn
  · cases hFind : (eFind K (stPrin (v bSt)) fun p =>
        _root_.SignalPqxdh.Security.ReductionDsl.KeyInd.natEq (.fst (v p)) (.fst (v x))).eval env with
    | none =>
      rw [hFind] at hp; simp only [mem_support_pure_iff, Expr.eval] at hp
      rw [hp, hSm]; exact gdhSimInv_unchanged_online hInv hOn
    | some ue =>
      rw [hFind] at hp
      simp only [letV, bindV, Comp.eval, pure_bind, mem_support_bind_iff, mem_support_pure_iff] at hp
      rcases hp with ⟨spkSkRaw, _, spkPkRaw, _, rSpk, _, spkSig, _, seed, _, kp, _, rPq, _, pqSig, _, rfl⟩
      simp only [v, Expr.eval] at hSm hBSt
      refine GdhSimInv.upd_online_base_pows hInv hOn ?_ ?_ ?_ ?_ ?_
      · refine BaseOnlineLenInv.upd_online hBase hOn ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ <;>
          simp only [smUpd, smMk, stUpd, _root_.SignalPqxdh.Security.ReductionDsl.KeyInd.stMk,
            stPrin, stSpks, stOpks, stSess, stResps, stUsedO, stUsedN,
            stKyb, stAdv, smFgL, smRaw, smLog, smPows,
            stPrinList, stSpksList, stOpksList, stSessList, stRespsList, stUsedOList, stUsedNList,
            stKybList, stAdvList, v,
            _root_.SignalPqxdh.Security.ReductionDsl.KeyInd.Ext.step_wk',
            _root_.SignalPqxdh.Security.ReductionDsl.KeyInd.Ext.refl_wk',
            _root_.SignalPqxdh.Security.ReductionDsl.KeyInd.Env.get_succ',
            Expr.eval, hBSt, List.length_cons, Nat.le_refl, Nat.le_succ]
      · simp only [smUpd, smMk, smFgL, v, _root_.SignalPqxdh.Security.ReductionDsl.KeyInd.Ext.step_wk',
          _root_.SignalPqxdh.Security.ReductionDsl.KeyInd.Ext.refl_wk',
          _root_.SignalPqxdh.Security.ReductionDsl.KeyInd.Env.get_succ', Expr.eval, hSm]
      · simp only [smUpd, smMk, smRaw, v, _root_.SignalPqxdh.Security.ReductionDsl.KeyInd.Ext.step_wk',
          _root_.SignalPqxdh.Security.ReductionDsl.KeyInd.Ext.refl_wk',
          _root_.SignalPqxdh.Security.ReductionDsl.KeyInd.Env.get_succ', Expr.eval, hSm]
      · simp only [smUpd, smMk, smLog, v, _root_.SignalPqxdh.Security.ReductionDsl.KeyInd.Ext.step_wk',
          _root_.SignalPqxdh.Security.ReductionDsl.KeyInd.Ext.refl_wk',
          _root_.SignalPqxdh.Security.ReductionDsl.KeyInd.Env.get_succ', Expr.eval, hSm]
      · simp only [smUpd, smMk, smPows, v, _root_.SignalPqxdh.Security.ReductionDsl.KeyInd.Ext.step_wk',
          _root_.SignalPqxdh.Security.ReductionDsl.KeyInd.Ext.refl_wk',
          _root_.SignalPqxdh.Security.ReductionDsl.KeyInd.Env.get_succ', Expr.eval, hSm, Nat.le_succ]

private theorem genOpkGdh2B_inv {S : Setup} {b : QueryBudget} {K : ℕ}
    {Γ₁ Γ₂ Γ₃ Γ₄ Δ : List PT} [Ext Γ₁ Δ] [Ext Γ₂ Δ] [Ext Γ₃ Δ] [Ext Γ₄ Δ]
    (pa : Var Γ₁ params2Ty) (sm : Var Γ₂ simTy) (bSt : Var Γ₃ keyIndStateTy)
    (x : Var Γ₄ (.prod .nat (.prod .nat .nat))) (env : Env Δ) {c : Fin 3 → ℕ} {t : KeyIndQuery S}
    {smVal : simTy.denote} {sh : fgShadowAtomicTy.denote}
    (hSm : (v sm).eval env = smVal) (hBSt : (v bSt).eval env = smVal.1)
    (hInv : GdhSimInv S b c (embedVal simTy smVal, sh))
    (hOn : keyIndQueryKind t = 0)
    {p : (keyIndRespTy.prod simTy).denote}
    (hp : p ∈ support ((genOpkGdh2B K pa sm bSt x).eval env)) :
    GdhSimInv S b (bumpPred (keyIndSimPred S) c t) (embedVal simTy p.2, sh) := by
  have hBase := baseOnlineLenInv_of_gdhSimInv hInv
  unfold genOpkGdh2B at hp
  simp only [Comp.eval] at hp
  split_ifs at hp
  · simp only [mem_support_pure_iff, Expr.eval] at hp
    rw [hp, hSm]; exact gdhSimInv_unchanged_online hInv hOn
  · simp only [letV, bindV, Comp.eval, pure_bind, mem_support_bind_iff, mem_support_pure_iff] at hp
    rcases hp with ⟨opkSkRaw, _, opkPkRaw, _, rfl⟩
    simp only [v, Expr.eval] at hSm hBSt
    refine GdhSimInv.upd_online_base_pows hInv hOn ?_ ?_ ?_ ?_ ?_
    · refine BaseOnlineLenInv.upd_online hBase hOn ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ <;>
        simp only [smUpd, smMk, stUpd, _root_.SignalPqxdh.Security.ReductionDsl.KeyInd.stMk,
          stPrin, stSpks, stOpks, stSess, stResps, stUsedO, stUsedN,
          stKyb, stAdv, smFgL, smRaw, smLog, smPows,
          stPrinList, stSpksList, stOpksList, stSessList, stRespsList, stUsedOList, stUsedNList,
          stKybList, stAdvList, v,
          _root_.SignalPqxdh.Security.ReductionDsl.KeyInd.Ext.step_wk',
          _root_.SignalPqxdh.Security.ReductionDsl.KeyInd.Ext.refl_wk',
          _root_.SignalPqxdh.Security.ReductionDsl.KeyInd.Env.get_succ',
          Expr.eval, hBSt, List.length_cons, Nat.le_refl, Nat.le_succ]
    · simp only [smUpd, smMk, smFgL, v, _root_.SignalPqxdh.Security.ReductionDsl.KeyInd.Ext.step_wk',
        _root_.SignalPqxdh.Security.ReductionDsl.KeyInd.Ext.refl_wk',
        _root_.SignalPqxdh.Security.ReductionDsl.KeyInd.Env.get_succ', Expr.eval, hSm]
    · simp only [smUpd, smMk, smRaw, v, _root_.SignalPqxdh.Security.ReductionDsl.KeyInd.Ext.step_wk',
        _root_.SignalPqxdh.Security.ReductionDsl.KeyInd.Ext.refl_wk',
        _root_.SignalPqxdh.Security.ReductionDsl.KeyInd.Env.get_succ', Expr.eval, hSm]
    · simp only [smUpd, smMk, smLog, v, _root_.SignalPqxdh.Security.ReductionDsl.KeyInd.Ext.step_wk',
        _root_.SignalPqxdh.Security.ReductionDsl.KeyInd.Ext.refl_wk',
        _root_.SignalPqxdh.Security.ReductionDsl.KeyInd.Env.get_succ', Expr.eval, hSm]
    · simp only [smUpd, smMk, smPows, v, _root_.SignalPqxdh.Security.ReductionDsl.KeyInd.Ext.step_wk',
        _root_.SignalPqxdh.Security.ReductionDsl.KeyInd.Ext.refl_wk',
        _root_.SignalPqxdh.Security.ReductionDsl.KeyInd.Env.get_succ', Expr.eval, hSm, Nat.le_succ]

private theorem registerGdhB_inv {S : Setup} {b : QueryBudget}
    {Γ₂ Γ₃ Γ₄ Δ : List PT} [Ext Γ₂ Δ] [Ext Γ₃ Δ] [Ext Γ₄ Δ]
    (sm : Var Γ₂ simTy) (bSt : Var Γ₃ keyIndStateTy) (sk : Var Γ₄ (B 32))
    (env : Env Δ) {c : Fin 3 → ℕ} {t : KeyIndQuery S}
    {smVal : simTy.denote} {sh : fgShadowAtomicTy.denote}
    (hSm : (v sm).eval env = smVal) (hBSt : (v bSt).eval env = smVal.1)
    (hInv : GdhSimInv S b c (embedVal simTy smVal, sh))
    (hOn : keyIndQueryKind t = 0)
    {p : (keyIndRespTy.prod simTy).denote}
    (hp : p ∈ support ((registerGdhB sm bSt sk).eval env)) :
    GdhSimInv S b (bumpPred (keyIndSimPred S) c t) (embedVal simTy p.2, sh) := by
  have hBase := baseOnlineLenInv_of_gdhSimInv hInv
  unfold registerGdhB at hp
  simp only [Comp.eval] at hp
  split_ifs at hp
  · simp only [mem_support_pure_iff, Expr.eval] at hp
    rw [hp, hSm]; exact gdhSimInv_unchanged_online hInv hOn
  · simp only [bindV, Comp.eval, mem_support_bind_iff, mem_support_pure_iff] at hp
    rcases hp with ⟨pk, _, wPk, _, rfl⟩
    simp only [v, Expr.eval] at hSm hBSt
    refine GdhSimInv.upd_online_base_pows hInv hOn ?_ ?_ ?_ ?_ ?_
    · refine BaseOnlineLenInv.upd_online hBase hOn ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ <;>
        simp only [smUpd, smMk, stUpd, _root_.SignalPqxdh.Security.ReductionDsl.KeyInd.stMk,
          stPrin, stSpks, stOpks, stSess, stResps, stUsedO, stUsedN,
          stKyb, stAdv, smFgL, smRaw, smLog, smPows,
          stPrinList, stSpksList, stOpksList, stSessList, stRespsList, stUsedOList, stUsedNList,
          stKybList, stAdvList, v,
          _root_.SignalPqxdh.Security.ReductionDsl.KeyInd.Ext.step_wk',
          _root_.SignalPqxdh.Security.ReductionDsl.KeyInd.Ext.refl_wk',
          _root_.SignalPqxdh.Security.ReductionDsl.KeyInd.Env.get_succ',
          Expr.eval, hBSt, List.length_cons, Nat.le_refl, Nat.le_succ]
    · simp only [smUpd, smMk, smFgL, v, _root_.SignalPqxdh.Security.ReductionDsl.KeyInd.Ext.step_wk',
        _root_.SignalPqxdh.Security.ReductionDsl.KeyInd.Ext.refl_wk',
        _root_.SignalPqxdh.Security.ReductionDsl.KeyInd.Env.get_succ', Expr.eval, hSm]
    · simp only [smUpd, smMk, smRaw, v, _root_.SignalPqxdh.Security.ReductionDsl.KeyInd.Ext.step_wk',
        _root_.SignalPqxdh.Security.ReductionDsl.KeyInd.Ext.refl_wk',
        _root_.SignalPqxdh.Security.ReductionDsl.KeyInd.Env.get_succ', Expr.eval, hSm]
    · simp only [smUpd, smMk, smLog, v, _root_.SignalPqxdh.Security.ReductionDsl.KeyInd.Ext.step_wk',
        _root_.SignalPqxdh.Security.ReductionDsl.KeyInd.Ext.refl_wk',
        _root_.SignalPqxdh.Security.ReductionDsl.KeyInd.Env.get_succ', Expr.eval, hSm]
    · simp only [smUpd, smMk, smPows, v, _root_.SignalPqxdh.Security.ReductionDsl.KeyInd.Ext.step_wk',
        _root_.SignalPqxdh.Security.ReductionDsl.KeyInd.Ext.refl_wk',
        _root_.SignalPqxdh.Security.ReductionDsl.KeyInd.Env.get_succ', Expr.eval, hSm,
        List.length_cons, Nat.le_refl]

private theorem gdhShadowHandle2_noFg_step {ι : Type} {T : OracleSpec ι} {A : AtomicIface T}
    {gl : GdhAtomicLift A}
    {evalGdh : ∀ {α : Type}, OracleComp _root_.SignalPqxdh.Security.FgGapDh.GdhSimSpec α → OracleComp T α}
    (hgl : GdhAtomicLiftValid gl evalGdh)
    (S : Setup) (b : QueryBudget) (t : KeyIndQuery S)
    {qPayTy : PT} {PayAtomic : Ty pqAtomicSig}
    (pay : PayAtomic.denote) (payLeg : qPayTy.denote)
    (payE : Expr pqAtomicOps
      (PayAtomic :: [.prod (embedTy gdhState2Ty) fgShadowAtomicTy, (pqKeyIndCodec S).Q])
      (embedTy qPayTy))
    (bodyK bodyQ :
      Var [params2Ty, gdhState2Ty, qPayTy] params2Ty →
      Var [simTy, params2Ty, gdhState2Ty, qPayTy] simTy →
      Var [keyIndStateTy, simTy, params2Ty, gdhState2Ty, qPayTy] keyIndStateTy →
      Var [gdhState2Ty, qPayTy] qPayTy →
      Comp pqxdhOps pqGapDhIface
        [keyIndStateTy, simTy, params2Ty, gdhState2Ty, qPayTy]
        (.prod keyIndRespTy simTy))
    (hUnsupK :
      (wrapNoFgArm fun pa sm bSt x => wrapSim2 pa (bodyK pa sm bSt x)).queries
        tlGapDhKeyInd.unsupportedW (fun _ => 0) = 0)
    (hDispK : ∀ s' : gdhShadowState2AtomicTy.denote,
      (gdhShadowHandle2Atomic gl S (keyIndKFuelsOfBudget S b)).eval
        (.cons s' (.cons ((pqKeyIndCodec S).qenc t) .nil)) =
      (liftKind0NoFgArm gl S payE (wrapNoFgArm fun pa sm bSt x => wrapSim2 pa (bodyK pa sm bSt x))).eval
        (.cons pay (.cons s' (.cons ((pqKeyIndCodec S).qenc t) .nil))))
    (hPayE : ∀ s' : gdhShadowState2AtomicTy.denote,
      payE.eval (.cons pay (.cons s' (.cons ((pqKeyIndCodec S).qenc t) .nil))) =
        embedVal qPayTy payLeg)
    (hDispQ : ∀ (pa : params2Ty.denote) (sm : simTy.denote),
      (gdhHandle2 S b.q_total).eval
        (.cons (pa, sm) (.cons ((_root_.SignalPqxdh.LegacyCosted.keyIndCodec S).qenc t) .nil)) =
      (wrapSim2 (.zero : Var [params2Ty, gdhState2Ty, qPayTy] params2Ty)
        (bodyQ .zero .zero .zero (.succ .zero))).eval
        (.cons sm.1 (.cons sm (.cons pa (.cons (pa, sm) (.cons payLeg .nil))))))
    (hFuelEq : ∀ (c : Fin 3 → ℕ) (pa : params2Ty.denote) (sm : simTy.denote)
        (fgSh : fgShadowAtomicTy.denote),
      (∀ j, c j ≤ keyIndSimBounds b j) →
      GdhSimInv S b c (embedVal simTy sm, fgSh) →
      (bodyK .zero .zero .zero (.succ .zero)).eval
        (.cons sm.1 (.cons sm (.cons pa (.cons (pa, sm) (.cons payLeg .nil))))) =
      (bodyQ .zero .zero .zero (.succ .zero)).eval
        (.cons sm.1 (.cons sm (.cons pa (.cons (pa, sm) (.cons payLeg .nil))))))
    (hInvStep : ∀ (c : Fin 3 → ℕ) (pa : params2Ty.denote) (sm : simTy.denote)
        (fgSh : fgShadowAtomicTy.denote) (r : (keyIndRespTy.prod simTy).denote),
      GdhSimInv S b c (embedVal simTy sm, fgSh) →
      r ∈ support ((bodyK .zero .zero .zero (.succ .zero)).eval
        (.cons sm.1 (.cons sm (.cons pa (.cons (pa, sm) (.cons payLeg .nil)))))) →
      GdhSimInv S b (bumpPred (keyIndSimPred S) c t) (embedVal simTy r.2, fgSh)) :
    KeyIndStepSim S b forgetGdhShadow2 (Gdh2SimInv S b)
      (gdhShadowHandle2Atomic gl S (keyIndKFuelsOfBudget S b))
      (liftKeyIndHandle gl.tl S (gl.liftI (gdhHandle2 S b.q_total))) t := by
  intro c s' hB _hRoom hInv
  let pa := (projVal gdhState2Ty s'.1).1
  let sm := (projVal gdhState2Ty s'.1).2
  have hs1 : embedVal gdhState2Ty (pa, sm) = s'.1 :=
    AtomicLift.embedVal_projVal gdhState2Ty s'.1
  have hInvSm : GdhSimInv S b c (embedVal simTy sm, s'.2) := by
    have h2 : (embedVal gdhState2Ty (pa, sm)).2 = embedVal simTy sm := rfl
    rw [← h2, hs1]; exact hInv
  have hArmEval :
      (liftKind0NoFgArm gl S payE (wrapNoFgArm fun pa sm bSt x => wrapSim2 pa (bodyK pa sm bSt x))).eval
        (.cons pay (.cons s' (.cons ((pqKeyIndCodec S).qenc t) .nil))) =
      (fun v0 => (v0.1, (v0.2, s'.2))) <$>
        (embedVal (.prod keyIndRespTy gdhState2Ty) <$>
          evalGdh ((wrapSim2 (.zero : Var [params2Ty, gdhState2Ty, qPayTy] params2Ty)
            (bodyK .zero .zero .zero (.succ .zero))).eval
            (.cons sm.1 (.cons sm (.cons pa (.cons (pa, sm) (.cons payLeg .nil))))))) := by
    unfold liftKind0NoFgArm
    simp only [Comp.eval, runAt2_eval, _root_.ReductionDsl.Expr.v0, _root_.ReductionDsl.Expr.v1,
      _root_.ReductionDsl.Expr.v2, Expr.eval, Env.get, hPayE s', map_eq_bind_pure_comp,
      Function.comp_def]
    have hEnv :
        (Env.cons s'.1 (.cons (embedVal qPayTy payLeg) .nil) :
          Env [embedTy gdhState2Ty, embedTy qPayTy]) =
        embedEnv (.cons (pa, sm) (.cons payLeg .nil) : Env [gdhState2Ty, qPayTy]) := by
      rw [← hs1]
    rw [hEnv, hgl.liftGdhAtomic_eval _ hUnsupK _]
    simp only [wrapNoFgArm, letV, smBase, v,
      _root_.SignalPqxdh.Security.ReductionDsl.KeyInd.Ext.step_wk',
      _root_.SignalPqxdh.Security.ReductionDsl.KeyInd.Ext.refl_wk',
      _root_.SignalPqxdh.Security.ReductionDsl.KeyInd.Env.get_zero',
      _root_.SignalPqxdh.Security.ReductionDsl.KeyInd.Env.get_succ',
      Comp.eval, Expr.eval, pure_bind, map_eq_bind_pure_comp, Function.comp_def]
  rw [hDispK s', hArmEval]
  refine ⟨?_, ?_⟩
  · rw [Functor.map_map, Functor.map_map]
    have hRhs :
        (liftKeyIndHandle gl.tl S (gl.liftI (gdhHandle2 S b.q_total))).eval
          (.cons (forgetGdhShadow2 s') (.cons ((pqKeyIndCodec S).qenc t) .nil)) =
        embedVal (.prod keyIndRespTy gdhState2Ty) <$>
          evalGdh ((gdhHandle2 S b.q_total).eval
            (.cons (pa, sm) (.cons ((_root_.SignalPqxdh.LegacyCosted.keyIndCodec S).qenc t) .nil))) := by
      have hf : forgetGdhShadow2 s' = embedVal gdhState2Ty (pa, sm) := hs1.symm
      rw [hf]
      exact (liftKeyIndHandle_eval gl.tl S (gl.liftI (gdhHandle2 S b.q_total))
        ((hgl.unsupported_eq (gdhHandle2 S b.q_total)).trans (gdhHandle2_unsupported S b.q_total))
        (pa, sm) t).trans
        (congrArg (Functor.map (embedVal (.prod keyIndRespTy gdhState2Ty)))
          (hgl.eval_liftI (gdhHandle2 S b.q_total) _))
    rw [hRhs, hDispQ pa sm]
    simp only [wrapSim2, bindV, Comp.eval, hFuelEq c pa sm s'.2 hB hInvSm]
    rfl
  · intro p hp
    simp only [map_eq_bind_pure_comp, Function.comp_def, mem_support_bind_iff, mem_support_pure_iff] at hp
    rcases hp with ⟨_, ⟨p0, hp0, rfl⟩, rfl⟩
    have hp0' := hgl.mem_support_evalGdh hp0
    simp only [wrapSim2, bindV, v, _root_.SignalPqxdh.Security.ReductionDsl.KeyInd.Ext.step_wk',
      _root_.SignalPqxdh.Security.ReductionDsl.KeyInd.Ext.refl_wk',
      _root_.SignalPqxdh.Security.ReductionDsl.KeyInd.Env.get_zero',
      _root_.SignalPqxdh.Security.ReductionDsl.KeyInd.Env.get_succ',
      Comp.eval, Expr.eval, mem_support_bind_iff, mem_support_pure_iff] at hp0'
    rcases hp0' with ⟨r0, hr0, rfl⟩
    exact hInvStep c pa sm s'.2 r0 hInvSm hr0

theorem gdhShadowHandle2Atomic_hStep_initPrin {ι : Type} {T : OracleSpec ι} {A : AtomicIface T}
    {gl : GdhAtomicLift A}
    {evalGdh : ∀ {α : Type}, OracleComp _root_.SignalPqxdh.Security.FgGapDh.GdhSimSpec α → OracleComp T α}
    (hgl : GdhAtomicLiftValid gl evalGdh)
    (S : Setup) (b : QueryBudget) (u : Fin S.N_id) :
    KeyIndStepSim S b forgetGdhShadow2 (Gdh2SimInv S b)
      (gdhShadowHandle2Atomic gl S (keyIndKFuelsOfBudget S b))
      (liftKeyIndHandle gl.tl S (gl.liftI (gdhHandle2 S b.q_total)))
      (.initPrin u) := by
  refine gdhShadowHandle2_noFg_step hgl S b (.initPrin u) u u.val
    (aop (.finVal S.N_id) .v0)
    (fun pa sm bSt u => initPrinGdh2B (keyIndKFuelsOfBudget S b).kOn pa sm bSt u)
    (fun pa sm bSt u => initPrinGdh2B b.q_total pa sm bSt u)
    (wrapNoFg_initPrinGdh2B_unsup _)
    (fun s' => by
      unfold gdhShadowHandle2Atomic
      exact dispatchKeyIndQ_eval S _ _ _ _ _ _ _ _ _ _ _ _ _ _ s' (.initPrin u))
    (fun _ => rfl)
    (fun pa sm => by
      simp only [gdhHandle2, _root_.SignalPqxdh.LegacyCosted.keyIndCodec,
        _root_.SignalPqxdh.LegacyCosted.keyIndQenc, letV, caseSumV, smBase, v,
        _root_.SignalPqxdh.Security.ReductionDsl.KeyInd.Ext.step_wk',
        _root_.SignalPqxdh.Security.ReductionDsl.KeyInd.Ext.refl_wk',
        _root_.SignalPqxdh.Security.ReductionDsl.KeyInd.Env.get_zero',
        _root_.SignalPqxdh.Security.ReductionDsl.KeyInd.Env.get_succ',
        Comp.eval, Expr.eval, pure_bind]; rfl)
    (fun c pa sm fgSh hB hInv => by
      have hBase := baseOnlineLenInv_of_gdhSimInv hInv
      exact initPrinGdh2B_eq_of_le _ _ _ _ _
        (Nat.le_trans hBase.prin_le (c0_le_kOn hBase hB)) (kOn_le_q_total S b))
    (fun c pa sm fgSh r hInv hr =>
      initPrinGdh2B_inv _ _ _ _ _ rfl rfl hInv rfl hr)

theorem gdhShadowHandle2Atomic_hStep_genSPK {ι : Type} {T : OracleSpec ι} {A : AtomicIface T}
    {gl : GdhAtomicLift A}
    {evalGdh : ∀ {α : Type}, OracleComp _root_.SignalPqxdh.Security.FgGapDh.GdhSimSpec α → OracleComp T α}
    (hgl : GdhAtomicLiftValid gl evalGdh)
    (S : Setup) (b : QueryBudget) (u : Fin S.N_id) (j : Fin S.N_recv) :
    KeyIndStepSim S b forgetGdhShadow2 (Gdh2SimInv S b)
      (gdhShadowHandle2Atomic gl S (keyIndKFuelsOfBudget S b))
      (liftKeyIndHandle gl.tl S (gl.liftI (gdhHandle2 S b.q_total)))
      (.genSPK u j) := by
  refine gdhShadowHandle2_noFg_step hgl S b (.genSPK u j) (u, j) (u.val, j.val)
    (finPairToNatE S.N_id S.N_recv .v0)
    (fun pa sm bSt x => genSpkGdh2B (keyIndKFuelsOfBudget S b).kOn pa sm bSt x)
    (fun pa sm bSt x => genSpkGdh2B b.q_total pa sm bSt x)
    (wrapNoFg_genSpkGdh2B_unsup _)
    (fun s' => by
      unfold gdhShadowHandle2Atomic
      exact dispatchKeyIndQ_eval S _ _ _ _ _ _ _ _ _ _ _ _ _ _ s' (.genSPK u j))
    (fun _ => rfl)
    (fun pa sm => by
      simp only [gdhHandle2, _root_.SignalPqxdh.LegacyCosted.keyIndCodec,
        _root_.SignalPqxdh.LegacyCosted.keyIndQenc, letV, caseSumV, smBase, v,
        _root_.SignalPqxdh.Security.ReductionDsl.KeyInd.Ext.step_wk',
        _root_.SignalPqxdh.Security.ReductionDsl.KeyInd.Ext.refl_wk',
        _root_.SignalPqxdh.Security.ReductionDsl.KeyInd.Env.get_zero',
        _root_.SignalPqxdh.Security.ReductionDsl.KeyInd.Env.get_succ',
        Comp.eval, Expr.eval, pure_bind]; rfl)
    (fun c pa sm fgSh hB hInv => by
      have hBase := baseOnlineLenInv_of_gdhSimInv hInv
      exact genSpkGdh2B_eq_of_le _ _ _ _ _ hBase (c0_le_kOn hBase hB) (kOn_le_q_total S b))
    (fun c pa sm fgSh r hInv hr =>
      genSpkGdh2B_inv _ _ _ _ _ rfl rfl hInv rfl hr)

theorem gdhShadowHandle2Atomic_hStep_genOPK {ι : Type} {T : OracleSpec ι} {A : AtomicIface T}
    {gl : GdhAtomicLift A}
    {evalGdh : ∀ {α : Type}, OracleComp _root_.SignalPqxdh.Security.FgGapDh.GdhSimSpec α → OracleComp T α}
    (hgl : GdhAtomicLiftValid gl evalGdh)
    (S : Setup) (b : QueryBudget) (u : Fin S.N_id) (j : Fin S.N_recv) (o : Fin S.N_opk) :
    KeyIndStepSim S b forgetGdhShadow2 (Gdh2SimInv S b)
      (gdhShadowHandle2Atomic gl S (keyIndKFuelsOfBudget S b))
      (liftKeyIndHandle gl.tl S (gl.liftI (gdhHandle2 S b.q_total)))
      (.genOPK u j o) := by
  refine gdhShadowHandle2_noFg_step hgl S b (.genOPK u j o) (u, (j, o)) (u.val, (j.val, o.val))
    (finTripleToNatE S.N_id S.N_recv S.N_opk .v0)
    (fun pa sm bSt x => genOpkGdh2B (keyIndKFuelsOfBudget S b).kOn pa sm bSt x)
    (fun pa sm bSt x => genOpkGdh2B b.q_total pa sm bSt x)
    (wrapNoFg_genOpkGdh2B_unsup _)
    (fun s' => by
      unfold gdhShadowHandle2Atomic
      exact dispatchKeyIndQ_eval S _ _ _ _ _ _ _ _ _ _ _ _ _ _ s' (.genOPK u j o))
    (fun _ => rfl)
    (fun pa sm => by
      simp only [gdhHandle2, _root_.SignalPqxdh.LegacyCosted.keyIndCodec,
        _root_.SignalPqxdh.LegacyCosted.keyIndQenc, letV, caseSumV, smBase, v,
        _root_.SignalPqxdh.Security.ReductionDsl.KeyInd.Ext.step_wk',
        _root_.SignalPqxdh.Security.ReductionDsl.KeyInd.Ext.refl_wk',
        _root_.SignalPqxdh.Security.ReductionDsl.KeyInd.Env.get_zero',
        _root_.SignalPqxdh.Security.ReductionDsl.KeyInd.Env.get_succ',
        Comp.eval, Expr.eval, pure_bind]; rfl)
    (fun c pa sm fgSh hB hInv => by
      have hBase := baseOnlineLenInv_of_gdhSimInv hInv
      exact genOpkGdh2B_eq_of_le _ _ _ _ _
        (Nat.le_trans hBase.opks_le (c0_le_kOn hBase hB)) (kOn_le_q_total S b))
    (fun c pa sm fgSh r hInv hr =>
      genOpkGdh2B_inv _ _ _ _ _ rfl rfl hInv rfl hr)

theorem gdhShadowHandle2Atomic_hStep_registerKey {ι : Type} {T : OracleSpec ι} {A : AtomicIface T}
    {gl : GdhAtomicLift A}
    {evalGdh : ∀ {α : Type}, OracleComp _root_.SignalPqxdh.Security.FgGapDh.GdhSimSpec α → OracleComp T α}
    (hgl : GdhAtomicLiftValid gl evalGdh)
    (S : Setup) (b : QueryBudget) (sk : Bytes) :
    KeyIndStepSim S b forgetGdhShadow2 (Gdh2SimInv S b)
      (gdhShadowHandle2Atomic gl S (keyIndKFuelsOfBudget S b))
      (liftKeyIndHandle gl.tl S (gl.liftI (gdhHandle2 S b.q_total)))
      (.registerKey sk) := by
  refine gdhShadowHandle2_noFg_step hgl S b (.registerKey sk) sk sk .v0
    (fun _ sm bSt sk => registerGdhB sm bSt sk)
    (fun _ sm bSt sk => registerGdhB sm bSt sk)
    wrapNoFg_registerGdhB_unsup
    (fun s' => by
      unfold gdhShadowHandle2Atomic
      exact dispatchKeyIndQ_eval S _ _ _ _ _ _ _ _ _ _ _ _ _ _ s' (.registerKey sk))
    (fun _ => rfl)
    (fun pa sm => by
      simp only [gdhHandle2, _root_.SignalPqxdh.LegacyCosted.keyIndCodec,
        _root_.SignalPqxdh.LegacyCosted.keyIndQenc, letV, caseSumV, smBase, v,
        _root_.SignalPqxdh.Security.ReductionDsl.KeyInd.Ext.step_wk',
        _root_.SignalPqxdh.Security.ReductionDsl.KeyInd.Ext.refl_wk',
        _root_.SignalPqxdh.Security.ReductionDsl.KeyInd.Env.get_zero',
        _root_.SignalPqxdh.Security.ReductionDsl.KeyInd.Env.get_succ',
        Comp.eval, Expr.eval, pure_bind]; rfl)
    (fun _ _ _ _ _ _ => rfl)
    (fun c _ sm fgSh r hInv hr =>
      registerGdhB_inv _ _ _ _ rfl rfl hInv rfl hr)

section L2AHelpers
open _root_.SignalPqxdh.LegacyCosted (keyIndCodec keyIndQenc pqPrimIface)
open _root_.SignalPqxdh.Security.ReductionDsl.KeyInd (
  peMk peSecIKAsign peIkAPk sbMk oeMk buMk
  natEq nat2Eq nat3Eq isSomeE eCaseOpt eLet eLet2 lenB litB u32OfNat encEC encKEM
  sBytes32 sRandom64 qX25519Base qPow8 qSigSign qKemKeyGen gPrim rPk rs
  liftGdhToSigDdh liftGdhToSigDdh_eval renamePair
)
open _root_.SignalPqxdh.Security.ReductionDsl.KeyInd1KeyGapDh (sigChalQ_dsl)
open Computational.Proofs.SignalPqxdh.AtomicLift (keyIndUnsupportedPrimW)

section L2AUnsup
set_option allowUnsafeReducibility true in
attribute [local implicit_reducible]
  _root_.SignalPqxdh.LegacyCosted.pqChalIface
  _root_.SignalPqxdh.LegacyCosted.pqPrimIface
  _root_.SignalPqxdh.LegacyCosted.pqGapDhIface
  _root_.SignalPqxdh.LegacyCosted.pqSigAndDdhIface
  _root_.SignalPqxdh.LegacyCosted.gapDhDdhOracle
  _root_.SignalPqxdh.LegacyCosted.sigAndDdhOracle
  _root_.SignalPqxdh.LegacyCosted.pqSamplers
attribute [local simp]
  letV_queries' bindV_queries' caseOptV_queries' caseSumV_queries' findMV_queries' anyMV_queries'

private theorem l2a_sigGenOpkLeg_unsup (K : ℕ) :
    (sigWrapGdh2NoFgLeg fun pa sm bSt x => wrapSim2 pa (genOpkGdh2B K pa sm bSt x)).queries
      tlSigDdhKeyInd.unsupportedW (fun _ => 0) = 0 := by
  have hLift : ∀ {Γ : List PT} {t : PT} (c : Comp pqxdhOps pqGapDhIface Γ t),
      (liftGdhToSigDdh c).queries tlSigDdhKeyInd.unsupportedW (fun _ => 0) =
        c.queries tlGapDhKeyInd.unsupportedW (fun _ => 0) := by
    intro Γ t c
    induction c with
    | query g _ => rcases g with _ | ⟨⟩ <;> rfl
    | sample _ _ => rfl
    | _ => simp_all [liftGdhToSigDdh, Comp.queries]
  have hPrim : ∀ {Γ : List PT} {t : PT} (c : Comp pqxdhOps pqPrimIface Γ t),
      (gPrim c).queries tlGapDhKeyInd.unsupportedW (fun _ => 0) =
        c.queries keyIndUnsupportedPrimW (fun _ => 0) := by
    intro Γ t c
    unfold gPrim
    induction c with
    | query _ _ => rfl
    | sample _ _ => rfl
    | _ => simp_all [_root_.SignalPqxdh.Security.ReductionDsl.KeyInd.liftBase, Comp.queries]
  simp [sigWrapGdh2NoFgLeg, wrapSim2, genOpkGdh2B, letV, bindV, Comp.queries,
    hLift, hPrim, sBytes32, qX25519Base, keyIndUnsupportedPrimW]

end L2AUnsup

private theorem l2a_liftGdhToSigDdh_comp_rename :
    ∀ {Γ : List PT} {t : PT} (c : Comp pqxdhOps pqGapDhIface Γ t) {Δ : List PT}
      (ξ : ∀ {τ}, Var Γ τ → Var Δ τ),
      liftGdhToSigDdh (c.rename ξ) = (liftGdhToSigDdh c).rename ξ := by
  intro Γ t c
  induction c with
  | query g _ => intro Δ ξ; rcases g with _ | ⟨⟩ <;> rfl
  | sample _ _ => intro Δ ξ; rfl
  | _ => intro Δ ξ; simp_all [liftGdhToSigDdh, Comp.rename]

section L2ALiftKeyIndHandle
set_option allowUnsafeReducibility true in
attribute [local implicit_reducible]
  _root_.SignalPqxdh.LegacyCosted.keyIndCodec

private theorem l2a_liftKeyIndHandle_eval_mapComp {ι : Type} {T : OracleSpec ι}
    {I : Iface pqSig T} {A : AtomicIface T}
    (tl : TagLift I A) (S : Setup) {σ outH : Ty pqSig}
    (h : Comp pqxdhOps I [σ, keyIndQueryTy] outH)
    (s : σ.denote) (t : KeyIndQuery S) :
    (liftKeyIndHandle tl S h).eval
      (.cons (embedVal σ s) (.cons ((pqKeyIndCodec S).qenc t) .nil)) =
    (mapComp tl h).eval
      (embedEnv (Γ := [σ, keyIndQueryTy])
        (.cons s (.cons (keyIndQenc t) .nil))) := by
  unfold liftKeyIndHandle
  simp only [Comp.eval, pure_bind]
  rw [AtomicLift.finKeyIndQToNatExpr_eval S (embedVal σ s) t]
  rw [AtomicLift.compRename_eval (mapComp tl h) AtomicLift.swapHandlerVar
    (embedEnv (.cons s (.cons (keyIndQenc t) .nil)))]
  intro a v
  dsimp only [AtomicLift.embedCtx] at v
  cases v with
  | zero => rfl
  | succ v => cases v with
    | zero => rfl
    | succ v => nomatch v

end L2ALiftKeyIndHandle

private theorem l2a_mapComp_caseSum_eval {ι : Type} {T : OracleSpec ι}
    {I : Iface pqSig T} {A : AtomicIface T} (tl : TagLift I A)
    {Γ : List (Ty pqSig)} {a b t : Ty pqSig} (e : Expr pqxdhOps Γ (.sum a b))
    (l : Comp pqxdhOps I (a :: Γ) t) (r : Comp pqxdhOps I (b :: Γ) t) (ρ : Env Γ) :
    (mapComp tl (.caseSum e l r)).eval (embedEnv ρ) =
      match e.eval ρ with
      | .inl x => (mapComp tl l).eval (embedEnv (.cons x ρ))
      | .inr y => (mapComp tl r).eval (embedEnv (.cons y ρ)) := by
  simp only [mapComp, Comp.eval, AtomicLift.mapExpr_eval]
  cases e.eval ρ <;> rfl

private theorem l2a_mapComp_caseSum_inl {ι : Type} {T : OracleSpec ι}
    {I : Iface pqSig T} {A : AtomicIface T} (tl : TagLift I A)
    {Γ : List (Ty pqSig)} {a b t : Ty pqSig} (e : Expr pqxdhOps Γ (.sum a b))
    (l : Comp pqxdhOps I (a :: Γ) t) (r : Comp pqxdhOps I (b :: Γ) t)
    (ρ : Env Γ) (x : a.denote) (he : e.eval ρ = .inl x) :
    (mapComp tl (.caseSum e l r)).eval (embedEnv ρ) =
      (mapComp tl l).eval (embedEnv (.cons x ρ)) := by
  rw [l2a_mapComp_caseSum_eval tl, he]

private theorem l2a_mapComp_caseSum_inr {ι : Type} {T : OracleSpec ι}
    {I : Iface pqSig T} {A : AtomicIface T} (tl : TagLift I A)
    {Γ : List (Ty pqSig)} {a b t : Ty pqSig} (e : Expr pqxdhOps Γ (.sum a b))
    (l : Comp pqxdhOps I (a :: Γ) t) (r : Comp pqxdhOps I (b :: Γ) t)
    (ρ : Env Γ) (y : b.denote) (he : e.eval ρ = .inr y) :
    (mapComp tl (.caseSum e l r)).eval (embedEnv ρ) =
      (mapComp tl r).eval (embedEnv (.cons y ρ)) := by
  rw [l2a_mapComp_caseSum_eval tl, he]

private theorem l2a_liftSigDdhNoFgArm_eval (S : Setup) {stTy qPayTy : PT} {PayAtomic : Ty pqAtomicSig}
    (payE : Expr pqAtomicOps
      (PayAtomic :: [.prod (embedTy stTy) fgShadowAtomicTy, (pqKeyIndCodec S).Q])
      (embedTy qPayTy))
    (arm : Comp pqxdhOps _root_.SignalPqxdh.LegacyCosted.pqSigAndDdhIface
      [stTy, qPayTy] (.prod keyIndRespTy stTy))
    (hUnsup : arm.queries tlSigDdhKeyInd.unsupportedW (fun _ => 0) = 0)
    (payA : PayAtomic.denote) (stL : stTy.denote) (sh : fgShadowAtomicTy.denote)
    (qenc : ((pqKeyIndCodec S).Q).denote) (payL : qPayTy.denote)
    (hPay : payE.eval (.cons payA (.cons (embedVal stTy stL, sh) (.cons qenc .nil))) =
      embedVal qPayTy payL) :
    (liftSigDdhNoFgArm S payE arm).eval
      (.cons payA (.cons (embedVal stTy stL, sh) (.cons qenc .nil))) =
    (fun r => (embedVal keyIndRespTy r.1, (embedVal stTy r.2, sh))) <$>
      arm.eval (.cons stL (.cons payL .nil)) := by
  unfold liftSigDdhNoFgArm
  simp only [Comp.eval, runAt2_eval, Expr.eval, Env.get, Expr.v0, Expr.v1, Expr.v2, hPay]
  have hEnv :
      (Env.cons (embedVal stTy stL) (.cons (embedVal qPayTy payL) .nil) :
        Env [embedTy stTy, AtomicLift.embedTy qPayTy]) =
      embedEnv (.cons stL (.cons payL .nil)) := rfl
  rw [hEnv, mapComp_eval tlSigDdhKeyInd arm hUnsup]
  simp only [map_eq_bind_pure_comp, Function.comp_def, bind_assoc, pure_bind]
  rfl

private def l2a_fixSig1KeyActiveSentLeg (S : Setup) (b : QueryBudget)
    (st : sig1KeyActiveStTy.denote) : sig1KeyActiveStTy.denote :=
  let (tp?, (sm, (ord, rest))) := st
  (tp?, (sm, (fixSent S b ord, rest)))

private theorem l2a_forgetSig1KeyActiveK_embed (S : Setup) (b : QueryBudget)
    (stL : sig1KeyActiveStTy.denote) (sh : fgShadowAtomicTy.denote) :
    forgetSig1KeyActiveK S b (embedVal sig1KeyActiveStTy stL, sh) =
      embedVal sig1KeyActiveStTy (l2a_fixSig1KeyActiveSentLeg S b stL) := by
  rcases stL with ⟨tp?, sm, ord, rest⟩
  rfl

private def l2a_fixParamsSentLeg (S : Setup) (b : QueryBudget) (pa : paramsTy.denote) :
    paramsTy.denote :=
  let (u, (vPk, (up, (prinFlag, (prinIdx, (dhFlag, (ephIdx, (spkIdx, (opkMode, (opkIdx, mode)))))))))) := pa
  (u, (vPk, (up, (prinFlag, (fixSent S b prinIdx,
    (dhFlag, (fixSent S b ephIdx, (fixSent S b spkIdx, (opkMode, (fixSent S b opkIdx, mode))))))))))

private def l2a_fixGdh1KeyActiveSentLeg (S : Setup) (b : QueryBudget)
    (stA : gdh1KeyActiveStateTy.denote) : gdh1KeyActiveStateTy.denote :=
  let (((pa, sm), sigB), rest) := stA
  (((l2a_fixParamsSentLeg S b pa, sm), sigB), rest)

private theorem l2a_forgetGdh1KeyActiveK_embed (S : Setup) (b : QueryBudget)
    (stL : gdh1KeyActiveStateTy.denote) (sh : fgShadowAtomicTy.denote) :
    forgetGdh1KeyActiveK S b (embedVal gdh1KeyActiveStateTy stL, sh) =
      embedVal gdh1KeyActiveStateTy (l2a_fixGdh1KeyActiveSentLeg S b stL) := by
  rcases stL with ⟨⟨⟨⟨u0, v0, up0, pf, pi, df, ei, si, om, oi, md⟩, sm⟩, sigB⟩, rest⟩
  rfl

private theorem l2a_Sig1KeyActiveSimInv_of_embed {S : Setup} {b : QueryBudget}
    {c : Fin 3 → ℕ} {tp? : Option ℕ} {sm' : simTy.denote}
    {rest : (Ty.prod .nat (.prod (B 32) (.prod .nat (.opt (.prod (B 1569) (B 64)))))).denote}
    {sh : fgShadowAtomicTy.denote}
    (hSim : GdhSimInv S b c (embedVal simTy sm', sh)) :
    Sig1KeyActiveSimInv S b c (embedVal sig1KeyActiveStTy (tp?, (sm', rest)), sh) :=
  hSim

private theorem l2a_Gdh1KeyActiveSimInv_of_embed {S : Setup} {b : QueryBudget}
    {c : Fin 3 → ℕ} {pa : paramsTy.denote} {sm' : simTy.denote}
    {sigB : ℕ} {tp? : Option ℕ} {cnt : ℕ} {sh : fgShadowAtomicTy.denote}
    (hSim : GdhSimInv S b c (embedVal simTy sm', sh))
    (hCnt : cnt ≤ c 0) :
    Gdh1KeyActiveSimInv S b c
      (embedVal gdh1KeyActiveStateTy (((pa, sm'), sigB), (tp?, cnt)), sh) :=
  ⟨hSim, hCnt⟩

private theorem l2a_decide_eq_fixSent_of_le_mOn {S : Setup} {b : QueryBudget} {n x : ℕ}
    (hn : n ≤ (keyIndKFuelsOfBudget S b).kOn) :
    decide (n = x) = decide (n = fixSent S b x) := by
  simpa [beq_iff_eq] using beq_fixSent_of_le_mOn (S := S) (b := b) (n := x) hn

private noncomputable def l2a_evalSDBytes32 :=
  (liftGdhComp (gPrim (sBytes32 (Γ := [])))).eval .nil
private noncomputable def l2a_evalSDRandom64 :=
  (liftGdhComp (gPrim (sRandom64 (Γ := [])))).eval .nil
private def l2a_litB32_nil : Bytes :=
  (litB (Γ := []) 32 []).eval .nil
private theorem l2a_eval_litB32_nil {Γ : List PT} (ρ : Env Γ) :
    (litB 32 []).eval ρ = l2a_litB32_nil := rfl
private noncomputable def l2a_evalSDX25519Base (x : Bytes) :=
  (liftGdhComp (gPrim (qX25519Base (Γ := [B 32]) (.var .zero)))).eval (.cons x .nil)
private noncomputable def l2a_evalSDKemKeyGen (seed : Bytes) :=
  (liftGdhComp (gPrim (qKemKeyGen (Γ := [B 64]) (.var .zero)))).eval (.cons seed .nil)
private noncomputable def l2a_evalSDSigSign (m : ℕ+)
    (arg : (Ty.prod (B 32) (.prod (B m) (B 64))).denote) :=
  (liftGdhComp (gPrim (qSigSign m (Γ := [.prod (B 32) (.prod (B m) (B 64))]) (.var .zero)))).eval
    (.cons arg .nil)
private noncomputable def l2a_evalSDSigChal (m : ℕ+) (msg : Bytes) :=
  (sigChalQ_dsl m (Γ := [B m]) (.var .zero)).eval (.cons msg .nil)

private theorem l2a_eval_liftGdhComp_sBytes32 {Γ : List PT} (ρ : Env Γ) :
    (liftGdhComp (gPrim (sBytes32 (Γ := Γ)))).eval ρ = l2a_evalSDBytes32 := rfl
private theorem l2a_eval_liftGdhComp_sRandom64 {Γ : List PT} (ρ : Env Γ) :
    (liftGdhComp (gPrim (sRandom64 (Γ := Γ)))).eval ρ = l2a_evalSDRandom64 := rfl
private theorem l2a_eval_liftGdhComp_qX25519Base {Γ : List PT} (e : Expr pqxdhOps Γ (B 32)) (ρ : Env Γ) :
    (liftGdhComp (gPrim (qX25519Base e))).eval ρ = l2a_evalSDX25519Base (e.eval ρ) := rfl
private theorem l2a_eval_liftGdhComp_qKemKeyGen {Γ : List PT} (e : Expr pqxdhOps Γ (B 64)) (ρ : Env Γ) :
    (liftGdhComp (gPrim (qKemKeyGen e))).eval ρ = l2a_evalSDKemKeyGen (e.eval ρ) := rfl
private theorem l2a_eval_liftGdhComp_qSigSign (m : ℕ+) {Γ : List PT}
    (e : Expr pqxdhOps Γ (.prod (B 32) (.prod (B m) (B 64)))) (ρ : Env Γ) :
    (liftGdhComp (gPrim (qSigSign m e))).eval ρ = l2a_evalSDSigSign m (e.eval ρ) := rfl
private theorem l2a_eval_sigChalQ_dsl (m : ℕ+) {Γ : List PT}
    (e : Expr pqxdhOps Γ (B m)) (ρ : Env Γ) :
    (sigChalQ_dsl m e).eval ρ = l2a_evalSDSigChal m (e.eval ρ) := rfl
private theorem l2a_eval_liftGdhToSigDdh_sBytes32 {Γ : List PT} (ρ : Env Γ) :
    (liftGdhToSigDdh (gPrim (sBytes32 (Γ := Γ)))).eval ρ = l2a_evalSDBytes32 := rfl
private theorem l2a_eval_liftGdhToSigDdh_sRandom64 {Γ : List PT} (ρ : Env Γ) :
    (liftGdhToSigDdh (gPrim (sRandom64 (Γ := Γ)))).eval ρ = l2a_evalSDRandom64 := rfl
private theorem l2a_eval_liftGdhToSigDdh_qX25519Base {Γ : List PT} (e : Expr pqxdhOps Γ (B 32)) (ρ : Env Γ) :
    (liftGdhToSigDdh (gPrim (qX25519Base e))).eval ρ = l2a_evalSDX25519Base (e.eval ρ) := rfl
private theorem l2a_eval_liftGdhToSigDdh_qKemKeyGen {Γ : List PT} (e : Expr pqxdhOps Γ (B 64)) (ρ : Env Γ) :
    (liftGdhToSigDdh (gPrim (qKemKeyGen e))).eval ρ = l2a_evalSDKemKeyGen (e.eval ρ) := rfl
private theorem l2a_eval_liftGdhToSigDdh_qSigSign (m : ℕ+) {Γ : List PT}
    (e : Expr pqxdhOps Γ (.prod (B 32) (.prod (B m) (B 64)))) (ρ : Env Γ) :
    (liftGdhToSigDdh (gPrim (qSigSign m e))).eval ρ = l2a_evalSDSigSign m (e.eval ρ) := rfl

private theorem l2a_smUpd_base_eval {Γ : List PT}
    (sm : Expr pqxdhOps Γ simTy)
    (base : Expr pqxdhOps Γ keyIndStateTy) (ρ : Env Γ) :
    (smUpd sm (base := base)).eval ρ = (base.eval ρ, (sm.eval ρ).2) := by
  dsimp only [smUpd, smMk, smFgL, smRaw, smLog, smPows, Expr.eval]

end L2AHelpers

private theorem icAtom_registerGdhB_eval_eq {Γ₁ Γ₂ Γ₃ Δ : List PT}
    [Ext Γ₁ Δ] [Ext Γ₂ Δ] [Ext Γ₃ Δ]
    (sm : Var Γ₁ simTy) (bSt : Var Γ₂ keyIndStateTy) (sk : Var Γ₃ (B 32)) (env : Env Δ) :
    (registerGdhB sm bSt sk).eval env =
      (registerGdhB (.zero : Var [simTy, keyIndStateTy, B 32] simTy)
        (.succ .zero : Var [simTy, keyIndStateTy, B 32] keyIndStateTy)
        (.succ (.succ .zero) : Var [simTy, keyIndStateTy, B 32] (B 32))).eval
        (.cons ((v sm).eval env) (.cons ((v bSt).eval env)
          (.cons (t := B 32) ((v sk).eval env) .nil))) := by
  simp [registerGdhB, bindV, smUpd, smMk, stUpd,
    _root_.SignalPqxdh.Security.ReductionDsl.KeyInd.stMk,
    _root_.SignalPqxdh.Security.ReductionDsl.KeyInd.stSecb,
    stPrin, stSpks, stOpks, stSess, stResps, stUsedO, stUsedN, stKyb, stRo, stAdv,
    smFgL, smRaw, smLog, smPows,
    _root_.SignalPqxdh.Security.ReductionDsl.KeyInd.rPk, rNone,
    _root_.SignalPqxdh.Security.ReductionDsl.KeyInd.gPrim,
    _root_.SignalPqxdh.Security.ReductionDsl.KeyInd.qX25519Base,
    _root_.SignalPqxdh.Security.ReductionDsl.KeyInd.qPow8,
    _root_.SignalPqxdh.Security.ReductionDsl.KeyInd.Ext.step_wk',
    _root_.SignalPqxdh.Security.ReductionDsl.KeyInd.Ext.refl_wk',
    _root_.SignalPqxdh.Security.ReductionDsl.KeyInd.Env.get_zero',
    _root_.SignalPqxdh.Security.ReductionDsl.KeyInd.Env.get_succ',
    Comp.eval, Expr.eval, v]

section IcAtomUnsup
set_option allowUnsafeReducibility true in
attribute [local implicit_reducible]
  _root_.SignalPqxdh.LegacyCosted.pqChalIface
  _root_.SignalPqxdh.LegacyCosted.pqPrimIface
  _root_.SignalPqxdh.LegacyCosted.pqGapDhIface
  _root_.SignalPqxdh.LegacyCosted.pqSigAndDdhIface
  _root_.SignalPqxdh.LegacyCosted.gapDhDdhOracle
  _root_.SignalPqxdh.LegacyCosted.sigAndDdhOracle
  _root_.SignalPqxdh.LegacyCosted.pqSamplers
attribute [local simp]
  letV_queries' bindV_queries' caseOptV_queries' caseSumV_queries' findMV_queries' anyMV_queries'
  sBytes32_unsup qX25519Base_unsup qPow8_unsup qSigVerify_unsup qKemEncaps_unsup
  gPrim_unsup liftGdhToSigDdh_unsup
  koskBundleOkPowsC_unsup resolveSigPkC_unsup lookupSpkSkC_unsup computePosC_unsup
  computeOptPosInitC_unsup fgPatchC_unsup honestPeerC_unsup checkProvC_unsup
  chooseInitRandC_unsup findHonestC_unsup

private theorem icAtom_liftGdhComp_unsup {Γ : List PT} {t : PT}
    (c : Comp pqxdhOps pqGapDhIface Γ t) :
    (liftGdhComp c).queries tlSigDdhKeyInd.unsupportedW (fun _ => 0) =
      c.queries tlGapDhKeyInd.unsupportedW (fun _ => 0) := by
  induction c with
  | query g _ => rcases g with _ | ⟨⟩ <;> rfl
  | sample _ => rfl
  | _ => simp_all [liftGdhComp, Comp.queries]

private theorem icAtom_renameComp_queries {ι : Type} {T : OracleSpec ι}
    {I : Iface pqSig T} (w : I.Tag → ℕ) (ws : I.smp.Samp → ℕ) :
    ∀ {Γ Δ : List PT} {t : PT}
      (ρ : _root_.SignalPqxdh.Security.ReductionDsl.KeyInd1KeyGapDh.Ren Γ Δ)
      (c : Comp pqxdhOps I Γ t),
      (renameComp ρ c).queries w ws = c.queries w ws := by
  intro Γ Δ t ρ c
  induction c generalizing Δ <;> simp_all [renameComp, Comp.queries]

private theorem icAtom_sigRegKey_unsup :
    (sigWrapGdh2NoFgLeg fun pa sm bSt sk => wrapSim2 pa (registerGdhB sm bSt sk)).queries
      tlSigDdhKeyInd.unsupportedW (fun _ => 0) = 0 := by
  change (sigWrapGdh2NoFgLeg fun pa sm bSt sk => wrapSim2 pa (registerGdhB sm bSt sk)).queries
    zSigDdhW zSigDdhWS = 0
  simp [sigWrapGdh2NoFgLeg, wrapSim2, registerGdhB, letV, bindV,
    liftGdhToSigDdh_unsup, gPrim_unsup, qX25519Base_unsup, qPow8_unsup, Comp.queries]

private theorem icAtom_gdhRegKey_unsup :
    (gdhWrapDelegNoFgLeg fun pa2 sm bSt sk => wrapSim2 pa2 (registerGdhB sm bSt sk)).queries
      tlSigDdhKeyInd.unsupportedW (fun _ => 0) = 0 := by
  change (gdhWrapDelegNoFgLeg fun pa2 sm bSt sk => wrapSim2 pa2 (registerGdhB sm bSt sk)).queries
    zSigDdhW zSigDdhWS = 0
  simp [gdhWrapDelegNoFgLeg, wrapSim2, registerGdhB, letV, bindV,
    icAtom_liftGdhComp_unsup, gPrim_unsup, qX25519Base_unsup, qPow8_unsup, Comp.queries]

private theorem icAtom_gdhActiveHandle_unsup (S : Setup) (K : Nat) :
    (gdh1KeyActiveHandle S K).queries tlSigDdhKeyInd.unsupportedW (fun _ => 0) = 0 := by
  have hCall : ∀ {Δ : List PT} (stAV : Var Δ gdh1KeyActiveStateTy) (qV : Var Δ keyIndQueryTy),
      (callGdhActiveHandle S K stAV qV).queries tlSigDdhKeyInd.unsupportedW (fun _ => 0) = 0 := by
    intro Δ stAV qV
    simp [callGdhActiveHandle, letV, bindV, icAtom_liftGdhComp_unsup, icAtom_renameComp_queries,
      gdhHandle2_unsupported S K, Comp.queries]
  have hSess : ∀ (hasOpk : Bool) {Γ₁ Γ₂ Δ : List PT} [Ext Γ₁ Δ] [Ext Γ₂ Δ]
      (stA : Var Γ₁ gdh1KeyActiveStateTy)
      (x : Var Γ₂ _root_.SignalPqxdh.Security.ReductionDsl.KeyInd.initQTy),
      (Computational.Proofs.SignalPqxdh.Delta.KeyInd1KeyActiveProgs.initiateActiveGdhB
        S K hasOpk (Δ := Δ) stA x).queries tlSigDdhKeyInd.unsupportedW (fun _ => 0) = 0 := by
    intro hasOpk Γ₁ Γ₂ Δ _ _ stA x
    simp [Computational.Proofs.SignalPqxdh.Delta.KeyInd1KeyActiveProgs.initiateActiveGdhB,
      Computational.Proofs.SignalPqxdh.Delta.KeyInd1KeyActiveProgs.initiateGdhActiveInnerB,
      icAtom_liftGdhComp_unsup, letV, bindV, caseOptV,
      gPrim_unsup, sBytes32_unsup, qSigVerify_unsup, qKemEncaps_unsup, qX25519Base_unsup,
      koskBundleOkPowsC_unsup, resolveSigPkC_unsup, lookupSpkSkC_unsup, computePosC_unsup,
      computeOptPosInitC_unsup, fgPatchC_unsup, honestPeerC_unsup, checkProvC_unsup,
      chooseInitRandC_unsup, findHonestC_unsup, Comp.queries]
  simp only [gdh1KeyActiveHandle, caseSumV_queries', initPrin1KeyActiveGdhB_unsupported,
    genSpk1KeyActiveGdhB_unsupported, genOpkActiveGdhB_unsupported, hCall, hSess, max_self]

end IcAtomUnsup

private theorem icAtom_mem_support_embedGdhSigDdh {α : Type}
    (oa : OracleComp _root_.SignalPqxdh.Security.FgGapDh.GdhSimSpec α) (y : α) :
    y ∈ support (_root_.SignalPqxdh.Security.Sig1Key.embedGdhSigDdh oa) ↔ y ∈ support oa := by
  induction oa using OracleComp.inductionOn with
  | pure a => rfl
  | query_bind q r ih =>
    rcases q with pq | dq
    · change y ∈ support (liftM (OracleSpec.query
          (spec := _root_.SignalPqxdh.Security.Sig1Key.SigDdhSimSpec) (Sum.inl pq)) >>=
          fun u => _root_.SignalPqxdh.Security.Sig1Key.embedGdhSigDdh (r u)) ↔ _
      simp only [mem_support_bind_iff, support_query, Set.mem_univ, true_and]
      exact exists_congr fun u => ih u
    · change y ∈ support (liftM (OracleSpec.query
          (spec := _root_.SignalPqxdh.Security.Sig1Key.SigDdhSimSpec) (Sum.inr (Sum.inr dq))) >>=
          fun u => _root_.SignalPqxdh.Security.Sig1Key.embedGdhSigDdh (r u)) ↔ _
      simp only [mem_support_bind_iff, support_query, Set.mem_univ, true_and]
      exact exists_congr fun u => ih u

private theorem icAtom_liftNoFg_eval (S : Setup) {stTy : PT}
    (arm : Comp pqxdhOps pqSigAndDdhIface [stTy, B 32] (.prod keyIndRespTy stTy))
    (hUnsup : arm.queries tlSigDdhKeyInd.unsupportedW (fun _ => 0) = 0)
    (sk : Bytes) (stL : stTy.denote) (sh : fgShadowAtomicTy.denote)
    (qenc : ((pqKeyIndCodec S).Q).denote) :
    (liftSigDdhNoFgArm S .v0 arm).eval
      (.cons sk (.cons (embedVal stTy stL, sh) (.cons qenc .nil))) =
    (fun r => (embedVal keyIndRespTy r.1, (embedVal stTy r.2, sh))) <$>
      arm.eval (.cons stL (.cons (t := B 32) sk .nil)) := by
  unfold liftSigDdhNoFgArm
  simp only [Comp.eval, runAt2_eval, _root_.ReductionDsl.Expr.v0, _root_.ReductionDsl.Expr.v1,
    _root_.ReductionDsl.Expr.v2, Expr.eval, Env.get]
  have hEnv :
      (Env.cons (embedVal stTy stL) (.cons (t := PB 32) sk .nil) :
        Env [embedTy stTy, embedTy (B 32)]) =
      embedEnv (.cons stL (.cons (t := B 32) sk .nil) : Env [stTy, B 32]) := rfl
  rw [hEnv, mapComp_eval tlSigDdhKeyInd arm hUnsup]
  simp only [map_eq_bind_pure_comp, Function.comp_def, bind_assoc, pure_bind]; rfl

private def icAtom_fixSigLeg (S : Setup) (b : QueryBudget)
    (st : sig1KeyActiveStTy.denote) : sig1KeyActiveStTy.denote :=
  (st.1, (st.2.1, (fixSent S b st.2.2.1, st.2.2.2)))

private def icAtom_fixParamsLeg (S : Setup) (b : QueryBudget)
    (pa : paramsTy.denote) : paramsTy.denote :=
  let (u, (vPk, (up, (pf, (pi, (df, (ei, (si, (om, (oi, md)))))))))) := pa
  (u, (vPk, (up, (pf, (fixSent S b pi,
    (df, (fixSent S b ei, (fixSent S b si, (om, (fixSent S b oi, md))))))))))

private def icAtom_fixGdhLeg (S : Setup) (b : QueryBudget)
    (stA : gdh1KeyActiveStateTy.denote) : gdh1KeyActiveStateTy.denote :=
  (((icAtom_fixParamsLeg S b stA.1.1.1, stA.1.1.2), stA.1.2), stA.2)

private def fixSigLeg (S : Setup) (b : QueryBudget)
    (st : sig1KeyActiveStTy.denote) : sig1KeyActiveStTy.denote :=
  (st.1, (st.2.1, (fixSent S b st.2.2.1, st.2.2.2)))

private theorem mem_support_liftGdhToSigDdh_eval {Γ : List PT} {t : PT}
    {c : Comp pqxdhOps pqGapDhIface Γ t} {env : Env Γ} {x : t.denote}
    (hx : x ∈ support ((_root_.SignalPqxdh.Security.ReductionDsl.KeyInd.liftGdhToSigDdh c).eval env)) :
    x ∈ support (c.eval env) := by
  rw [_root_.SignalPqxdh.Security.ReductionDsl.KeyInd.liftGdhToSigDdh_eval] at hx
  exact _root_.SignalPqxdh.Security.ReductionDsl.KeyInd.AllOut_embedGdhSigDdh (fun _ h => h) x hx

private theorem sigNoFg_step (S : Setup) (b : QueryBudget) (t : KeyIndQuery S)
    {qPayTy : PT} {PayAtomic : Ty pqAtomicSig}
    (pay : PayAtomic.denote) (payLeg : qPayTy.denote)
    (payE : Expr pqAtomicOps
      (PayAtomic :: [.prod (embedTy sig1KeyActiveStTy) fgShadowAtomicTy, (pqKeyIndCodec S).Q])
      (embedTy qPayTy))
    (arm : Comp pqxdhOps pqSigAndDdhIface [sig1KeyActiveStTy, qPayTy]
      (.prod keyIndRespTy sig1KeyActiveStTy))
    (hUnsup : arm.queries tlSigDdhKeyInd.unsupportedW (fun _ => 0) = 0)
    (hDispK : ∀ s' : (Ty.prod (embedTy sig1KeyActiveStTy) fgShadowAtomicTy).denote,
      (sig1KeyKindHandleC S b).eval (.cons s' (.cons ((pqKeyIndCodec S).qenc t) .nil)) =
      (liftSigDdhNoFgArm S payE arm).eval
        (.cons pay (.cons s' (.cons ((pqKeyIndCodec S).qenc t) .nil))))
    (hPayE : ∀ s' : (Ty.prod (embedTy sig1KeyActiveStTy) fgShadowAtomicTy).denote,
      payE.eval (.cons pay (.cons s' (.cons ((pqKeyIndCodec S).qenc t) .nil))) =
        embedVal qPayTy payLeg)
    (hSim : ∀ (c : Fin 3 → ℕ) (st : sig1KeyActiveStTy.denote) (sh : fgShadowAtomicTy.denote),
      (∀ j, c j ≤ keyIndSimBounds b j) →
      GdhSimInv S b c (embedVal simTy st.2.1, sh) →
      ((fun r => (r.1, fixSigLeg S b r.2)) <$> arm.eval (.cons st (.cons payLeg .nil))) =
      (sig1KeyActiveHandleC S b.q_total).eval
        (.cons (fixSigLeg S b st)
          (.cons ((_root_.SignalPqxdh.LegacyCosted.keyIndCodec S).qenc t) .nil)))
    (hInvStep : ∀ (c : Fin 3 → ℕ) (st : sig1KeyActiveStTy.denote) (sh : fgShadowAtomicTy.denote)
        (r : (keyIndRespTy.prod sig1KeyActiveStTy).denote),
      (∀ j, c j ≤ keyIndSimBounds b j) →
      GdhSimInv S b c (embedVal simTy st.2.1, sh) →
      r ∈ support (arm.eval (.cons st (.cons payLeg .nil))) →
      GdhSimInv S b (bumpPred (keyIndSimPred S) c t) (embedVal simTy r.2.2.1, sh)) :
    KeyIndStepSim S b (forgetSig1KeyActiveK S b) (Sig1KeyActiveSimInv S b)
      (sig1KeyKindHandleC S b) (sigKeyInd1KeyActiveAtomicProg S b).handle t := by
  intro c s' hB _hRoom hInv
  let st := projVal sig1KeyActiveStTy s'.1
  have hs1 : embedVal sig1KeyActiveStTy st = s'.1 :=
    AtomicLift.embedVal_projVal sig1KeyActiveStTy s'.1
  have hInvSm : GdhSimInv S b c (embedVal simTy st.2.1, s'.2) := by
    have h2 : (embedVal sig1KeyActiveStTy st).2.1 = embedVal simTy st.2.1 := rfl
    rw [← h2, hs1]; exact hInv
  have hArmEval :
      (liftSigDdhNoFgArm S payE arm).eval
        (.cons pay (.cons s' (.cons ((pqKeyIndCodec S).qenc t) .nil))) =
      (fun v0 => (v0.1, (v0.2, s'.2))) <$>
        (embedVal (.prod keyIndRespTy sig1KeyActiveStTy) <$>
          arm.eval (.cons st (.cons payLeg .nil))) := by
    unfold liftSigDdhNoFgArm
    simp only [Comp.eval, runAt2_eval, _root_.ReductionDsl.Expr.v0, _root_.ReductionDsl.Expr.v1,
      _root_.ReductionDsl.Expr.v2, Expr.eval, Env.get, hPayE s', map_eq_bind_pure_comp,
      Function.comp_def]
    have hEnv :
        (Env.cons s'.1 (.cons (embedVal qPayTy payLeg) .nil) :
          Env [embedTy sig1KeyActiveStTy, embedTy qPayTy]) =
        embedEnv (.cons st (.cons payLeg .nil) : Env [sig1KeyActiveStTy, qPayTy]) := by
      rw [← hs1]
    rw [hEnv, mapComp_eval tlSigDdhKeyInd arm hUnsup]
    simp only [map_eq_bind_pure_comp, Function.comp_def]
  rw [hDispK s', hArmEval]
  refine ⟨?_, ?_⟩
  · rw [Functor.map_map, Functor.map_map]
    have hf : forgetSig1KeyActiveK S b s' = embedVal sig1KeyActiveStTy (fixSigLeg S b st) := by
      have hs' : s' = (embedVal sig1KeyActiveStTy st, s'.2) := Prod.ext hs1.symm rfl
      rw [hs']; rfl
    have hRhs :
        (sigKeyInd1KeyActiveAtomicProg S b).handle.eval
          (.cons (forgetSig1KeyActiveK S b s') (.cons ((pqKeyIndCodec S).qenc t) .nil)) =
        embedVal (.prod keyIndRespTy sig1KeyActiveStTy) <$>
          (sig1KeyActiveHandleC S b.q_total).eval
            (.cons (fixSigLeg S b st)
              (.cons ((_root_.SignalPqxdh.LegacyCosted.keyIndCodec S).qenc t) .nil)) := by
      rw [hf]
      exact liftKeyIndHandle_eval tlSigDdhKeyInd S (sigKeyInd1KeyActiveDslProg S b).handle
        (sig1KeyActiveHandleC_unsupported S b.q_total) (fixSigLeg S b st) t
    rw [hRhs, ← hSim c st s'.2 hB hInvSm, Functor.map_map]
    rfl
  · intro p hp
    simp only [map_eq_bind_pure_comp, Function.comp_def, mem_support_bind_iff, mem_support_pure_iff] at hp
    rcases hp with ⟨_, ⟨r, hr, rfl⟩, rfl⟩
    exact hInvStep c st s'.2 r hB hInvSm hr

private theorem decide_eq_fixSent_of_le_mOn {S : Setup} {b : QueryBudget} {len n : ℕ}
    (hLen : len ≤ min b.q_on b.q_total) :
    decide (len = n) = decide (len = fixSent S b n) := by
  simpa [beq_iff_eq] using beq_fixSent_of_le_mOn (S := S) (b := b) (n := n) hLen

private noncomputable def evalS1Bytes32 :=
  (_root_.SignalPqxdh.Security.ReductionDsl.KeyInd.s1Prim
    (_root_.SignalPqxdh.Security.ReductionDsl.KeyInd.sBytes32 (Γ := []))).eval .nil
private noncomputable def evalS1Random64 :=
  (_root_.SignalPqxdh.Security.ReductionDsl.KeyInd.s1Prim
    (_root_.SignalPqxdh.Security.ReductionDsl.KeyInd.sRandom64 (Γ := []))).eval .nil
private noncomputable def evalS1X25519Base (x : Bytes) :=
  (_root_.SignalPqxdh.Security.ReductionDsl.KeyInd.s1Prim
    (_root_.SignalPqxdh.Security.ReductionDsl.KeyInd.qX25519Base (Γ := [B 32]) (.var .zero))).eval
    (.cons x .nil)
private noncomputable def evalS1KemKeyGen (seed : Bytes) :=
  (_root_.SignalPqxdh.Security.ReductionDsl.KeyInd.s1Prim
    (_root_.SignalPqxdh.Security.ReductionDsl.KeyInd.qKemKeyGen (Γ := [B 64]) (.var .zero))).eval
    (.cons seed .nil)
private noncomputable def evalQSigDdhSign (m : ℕ+) (msg : Bytes) :=
  (_root_.SignalPqxdh.Security.ReductionDsl.KeyInd.qSigDdhSign m (Γ := [B m]) (.var .zero)).eval
    (.cons msg .nil)
private theorem eval_s1Prim_sBytes32 {Γ : List PT} (ρ : Env Γ) :
    (_root_.SignalPqxdh.Security.ReductionDsl.KeyInd.s1Prim
      (_root_.SignalPqxdh.Security.ReductionDsl.KeyInd.sBytes32 (Γ := Γ))).eval ρ =
      evalS1Bytes32 := rfl
private theorem eval_s1Prim_sRandom64 {Γ : List PT} (ρ : Env Γ) :
    (_root_.SignalPqxdh.Security.ReductionDsl.KeyInd.s1Prim
      (_root_.SignalPqxdh.Security.ReductionDsl.KeyInd.sRandom64 (Γ := Γ))).eval ρ =
      evalS1Random64 := rfl
private theorem eval_s1Prim_qX25519Base {Γ : List PT} (e : Expr pqxdhOps Γ (B 32)) (ρ : Env Γ) :
    (_root_.SignalPqxdh.Security.ReductionDsl.KeyInd.s1Prim
      (_root_.SignalPqxdh.Security.ReductionDsl.KeyInd.qX25519Base e)).eval ρ =
      evalS1X25519Base (e.eval ρ) := rfl
private theorem eval_s1Prim_qKemKeyGen {Γ : List PT} (e : Expr pqxdhOps Γ (B 64)) (ρ : Env Γ) :
    (_root_.SignalPqxdh.Security.ReductionDsl.KeyInd.s1Prim
      (_root_.SignalPqxdh.Security.ReductionDsl.KeyInd.qKemKeyGen e)).eval ρ =
      evalS1KemKeyGen (e.eval ρ) := rfl
private theorem eval_qSigDdhSign (m : ℕ+) {Γ : List PT} (e : Expr pqxdhOps Γ (B m)) (ρ : Env Γ) :
    (_root_.SignalPqxdh.Security.ReductionDsl.KeyInd.qSigDdhSign m e).eval ρ =
      evalQSigDdhSign m (e.eval ρ) := rfl
private theorem smUpd_base_eval {Γ : List PT}
    (sm : Expr pqxdhOps Γ simTy) (base : Expr pqxdhOps Γ keyIndStateTy) (ρ : Env Γ) :
    (smUpd sm (base := base)).eval ρ = (base.eval ρ, (sm.eval ρ).2) := by
  dsimp only [smUpd, smMk, smFgL, smRaw, smLog, smPows, Expr.eval]
private def optNatMatchesVal (tp? : Option ℕ) (u : ℕ) : Bool :=
  match tp? with | none => false | some tp => decide (u = tp)
private theorem optNatMatchesE_eval {Γ : List PT}
    (tpOpt : Expr pqxdhOps Γ (.opt .nat)) (u : Expr pqxdhOps Γ .nat) (ρ : Env Γ) :
    (optNatMatchesE tpOpt u).eval ρ = optNatMatchesVal (tpOpt.eval ρ) (u.eval ρ) := by
  simp only [optNatMatchesE, _root_.SignalPqxdh.Security.ReductionDsl.KeyInd.eLet2,
    _root_.SignalPqxdh.Security.ReductionDsl.KeyInd.eLet,
    _root_.SignalPqxdh.Security.ReductionDsl.KeyInd.eCaseOpt,
    _root_.SignalPqxdh.Security.ReductionDsl.KeyInd.natEq,
    Expr.eval, v, _root_.SignalPqxdh.Security.ReductionDsl.KeyInd.Ext.wk,
    _root_.SignalPqxdh.Security.ReductionDsl.KeyInd.Env.get_zero',
    _root_.SignalPqxdh.Security.ReductionDsl.KeyInd.Env.get_succ']
  cases tpOpt.eval ρ <;> rfl

theorem sigKeyInd1KeyKindAtomicProg_hStep_initPrin (S : Setup) (b : QueryBudget) (u : Fin S.N_id) :
    KeyIndStepSim S b (forgetSig1KeyActiveK S b) (Sig1KeyActiveSimInv S b)
      (sig1KeyKindHandleC S b) (sigKeyInd1KeyActiveAtomicProg S b).handle (.initPrin u) := by
  refine sigNoFg_step S b (.initPrin u) u u.val (aop (.finVal S.N_id) .v0)
    (sigKindInitPrinLeg (keyIndKFuelsOfBudget S b).kOn)
    (sigKindInitPrinLeg_unsupported (keyIndKFuelsOfBudget S b).kOn)
    (fun s' => by
      unfold sig1KeyKindHandleC
      exact dispatchKeyIndQ_eval S _ _ _ _ _ _ _ _ _ _ _ _ _ _ s' (.initPrin u))
    (fun _ => rfl) ?_ ?_
  · intro c ⟨tp?, sm, ord, pk, sigB, fg?⟩ sh hB hInv
    change GdhSimInv S b c (embedVal simTy sm, sh) at hInv
    have hBase := baseOnlineLenInv_of_gdhSimInv hInv
    have hLenM : sm.1.2.1.length ≤ min b.q_on b.q_total :=
      Nat.le_trans hBase.prin_le (hB 0)
    have hLenK : sm.1.2.1.length ≤ (keyIndKFuelsOfBudget S b).kOn :=
      Nat.le_trans hBase.prin_le (c0_le_kOn hBase hB)
    have hLenQ : sm.1.2.1.length ≤ b.q_total :=
      Nat.le_trans hLenK (kOn_le_q_total S b)
    have hTakeK : List.take (keyIndKFuelsOfBudget S b).kOn sm.1.2.1 = sm.1.2.1 :=
      List.take_of_length_le hLenK
    have hTakeQ : List.take b.q_total sm.1.2.1 = sm.1.2.1 :=
      List.take_of_length_le hLenQ
    have hBeq : decide (sm.1.2.1.length = ord) = decide (sm.1.2.1.length = fixSent S b ord) :=
      decide_eq_fixSent_of_le_mOn hLenM
    cases fg? with
    | some fg =>
      simp only [sigKindInitPrinLeg, sig1KeyActiveHandleC, sig1KeyActivePreDispatchC, fixSigLeg,
        saInner, s1Forgery, _root_.SignalPqxdh.Security.ReductionDsl.KeyInd.isSomeE, rNone,
        bindV, caseSumV, v, _root_.SignalPqxdh.Security.ReductionDsl.KeyInd.Ext.wk,
        _root_.SignalPqxdh.Security.ReductionDsl.KeyInd.Ext.step_wk',
        _root_.SignalPqxdh.Security.ReductionDsl.KeyInd.Ext.refl_wk',
        _root_.SignalPqxdh.Security.ReductionDsl.KeyInd.Env.get_zero',
        _root_.SignalPqxdh.Security.ReductionDsl.KeyInd.Env.get_succ',
        Comp.eval, Expr.eval, ite_true, pure_bind, map_pure]
    | none =>
      simp only [sigKindInitPrinLeg, sig1KeyActiveHandleC, sig1KeyActivePreDispatchC,
        sig1KeyActiveInitPrinB, fixSigLeg, _root_.SignalPqxdh.LegacyCosted.keyIndCodec,
        _root_.SignalPqxdh.LegacyCosted.keyIndQenc, saInner, saTP, s1Fg, s1Base, smBase, s1Target,
        s1Pk, s1Budget, s1Forgery, s1Upd, s1Mk, smUpd_base_eval, stPrin,
        eAny, rNone, rInitPrin, _root_.SignalPqxdh.Security.ReductionDsl.KeyInd.isSomeE,
        _root_.SignalPqxdh.Security.ReductionDsl.KeyInd.natEq, l2a_eval_litB32_nil,
        eval_s1Prim_sBytes32, eval_s1Prim_qX25519Base,
        letV, bindV, caseSumV, v, _root_.SignalPqxdh.Security.ReductionDsl.KeyInd.Ext.wk,
        _root_.SignalPqxdh.Security.ReductionDsl.KeyInd.Ext.step_wk',
        _root_.SignalPqxdh.Security.ReductionDsl.KeyInd.Ext.refl_wk',
        Comp.eval, Expr.eval, Env.get, hTakeK, hTakeQ, Bool.false_eq_true, ↓reduceIte,
        pure_bind, bind_assoc, map_eq_bind_pure_comp, Function.comp_def]
      cases hDup : List.any sm.1.2.1 (fun x => decide (x.1 = u.val))
      · simp only [Bool.false_eq_true, ↓reduceIte, bind_assoc, pure_bind]
        refine bind_congr_support _ _ _ fun s0 _ => ?_
        refine bind_congr_support _ _ _ fun ik _ => ?_
        rw [hBeq]
      · simp only [↓reduceIte, pure_bind]
  · intro c ⟨tp?, sm, ord, pk, sigB, fg?⟩ sh r hB hInv hr
    change GdhSimInv S b c (embedVal simTy sm, sh) at hInv
    have hBase := baseOnlineLenInv_of_gdhSimInv hInv
    have hTakeK : List.take (keyIndKFuelsOfBudget S b).kOn sm.1.2.1 = sm.1.2.1 :=
      List.take_of_length_le (Nat.le_trans hBase.prin_le (c0_le_kOn hBase hB))
    cases fg? with
    | some fg =>
      simp only [sigKindInitPrinLeg, saInner, s1Forgery,
        _root_.SignalPqxdh.Security.ReductionDsl.KeyInd.isSomeE, v,
        _root_.SignalPqxdh.Security.ReductionDsl.KeyInd.Ext.wk,
        _root_.SignalPqxdh.Security.ReductionDsl.KeyInd.Env.get_zero',
        Comp.eval, Expr.eval, ↓reduceIte, mem_support_pure_iff] at hr
      rw [hr]; exact gdhSimInv_unchanged_online hInv rfl
    | none =>
      simp only [sigKindInitPrinLeg, sig1KeyActiveInitPrinB, saInner, saTP, s1Fg, s1Base, smBase,
        s1Target, s1Pk, s1Budget, s1Forgery, s1Upd, s1Mk, smUpd_base_eval, stPrin,
        eAny, _root_.SignalPqxdh.Security.ReductionDsl.KeyInd.isSomeE,
        _root_.SignalPqxdh.Security.ReductionDsl.KeyInd.natEq,
        eval_s1Prim_sBytes32, eval_s1Prim_qX25519Base,
        letV, bindV, v, _root_.SignalPqxdh.Security.ReductionDsl.KeyInd.Ext.wk,
        _root_.SignalPqxdh.Security.ReductionDsl.KeyInd.Ext.step_wk',
        _root_.SignalPqxdh.Security.ReductionDsl.KeyInd.Ext.refl_wk',
        Comp.eval, Expr.eval, Env.get, hTakeK, Bool.false_eq_true, ↓reduceIte, pure_bind] at hr
      cases hDup : List.any sm.1.2.1 (fun x => decide (x.1 = u.val)) <;>
        simp only [hDup, Bool.false_eq_true, ↓reduceIte] at hr
      · simp only [mem_support_bind_iff, mem_support_pure_iff] at hr
        rcases hr with ⟨s0, _, ik, _, rfl⟩
        exact GdhSimInv.upd_online_base_pows hInv rfl
          (BaseOnlineLenInv.upd_online hBase rfl
            (Nat.le_refl _) (Nat.le_succ _) (Nat.le_succ _)
            le_rfl le_rfl le_rfl le_rfl le_rfl (Nat.le_succ _))
          rfl rfl rfl (Nat.le_succ _)
      · rw [mem_support_pure_iff] at hr; rw [hr]; exact gdhSimInv_unchanged_online hInv rfl

theorem sigKeyInd1KeyKindAtomicProg_hStep_genSPK (S : Setup) (b : QueryBudget)
    (u : Fin S.N_id) (j : Fin S.N_recv) :
    KeyIndStepSim S b (forgetSig1KeyActiveK S b) (Sig1KeyActiveSimInv S b)
      (sig1KeyKindHandleC S b) (sigKeyInd1KeyActiveAtomicProg S b).handle (.genSPK u j) := by
  refine sigNoFg_step S b (.genSPK u j) (u, j) (u.val, j.val)
    (finPairToNatE S.N_id S.N_recv .v0)
    (sigKindGenSpkLeg (keyIndKFuelsOfBudget S b).kOn)
    (sigKindGenSpkLeg_unsupported (keyIndKFuelsOfBudget S b).kOn)
    (fun s' => by
      unfold sig1KeyKindHandleC
      exact dispatchKeyIndQ_eval S _ _ _ _ _ _ _ _ _ _ _ _ _ _ s' (.genSPK u j))
    (fun _ => rfl) ?_ ?_
  · intro c ⟨tp?, sm, ord, pk, sigB, fg?⟩ sh hB hInv
    change GdhSimInv S b c (embedVal simTy sm, sh) at hInv
    have hBase := baseOnlineLenInv_of_gdhSimInv hInv
    have hFkLe : (keyIndKFuelsOfBudget S b).kOn ≤ b.q_total := kOn_le_q_total S b
    have hPrinLen : sm.1.2.1.length ≤ (keyIndKFuelsOfBudget S b).kOn :=
      Nat.le_trans hBase.prin_le (c0_le_kOn hBase hB)
    have hSpksLen : sm.1.2.2.1.length ≤ (keyIndKFuelsOfBudget S b).kOn :=
      Nat.le_trans hBase.spks_le (c0_le_kOn hBase hB)
    have hTakePrinK : List.take (keyIndKFuelsOfBudget S b).kOn sm.1.2.1 = sm.1.2.1 :=
      List.take_of_length_le hPrinLen
    have hTakePrinQ : List.take b.q_total sm.1.2.1 = sm.1.2.1 :=
      List.take_of_length_le (Nat.le_trans hPrinLen hFkLe)
    have hTakeSpksK : List.take (keyIndKFuelsOfBudget S b).kOn sm.1.2.2.1 = sm.1.2.2.1 :=
      List.take_of_length_le hSpksLen
    have hTakeSpksQ : List.take b.q_total sm.1.2.2.1 = sm.1.2.2.1 :=
      List.take_of_length_le (Nat.le_trans hSpksLen hFkLe)
    cases fg? with
    | some fg =>
      simp only [sigKindGenSpkLeg, sig1KeyActiveHandleC, sig1KeyActivePreDispatchC, fixSigLeg,
        saInner, s1Forgery, _root_.SignalPqxdh.Security.ReductionDsl.KeyInd.isSomeE, rNone,
        bindV, caseSumV, v, _root_.SignalPqxdh.Security.ReductionDsl.KeyInd.Ext.wk,
        _root_.SignalPqxdh.Security.ReductionDsl.KeyInd.Ext.step_wk',
        _root_.SignalPqxdh.Security.ReductionDsl.KeyInd.Ext.refl_wk',
        _root_.SignalPqxdh.Security.ReductionDsl.KeyInd.Env.get_zero',
        _root_.SignalPqxdh.Security.ReductionDsl.KeyInd.Env.get_succ',
        Comp.eval, Expr.eval, ite_true, pure_bind, map_pure]
    | none =>
      cases hMatch : optNatMatchesVal tp? u.val
      · simp only [sigKindGenSpkLeg, sig1KeyActiveHandleC, sig1KeyActivePreDispatchC, fixSigLeg,
          _root_.SignalPqxdh.LegacyCosted.keyIndCodec, _root_.SignalPqxdh.LegacyCosted.keyIndQenc,
          optNatMatchesE_eval, hMatch, rNone, rBundle,
          _root_.SignalPqxdh.Security.ReductionDsl.KeyInd.peSecIKAsign,
          _root_.SignalPqxdh.Security.ReductionDsl.KeyInd.peIkAPk,
          _root_.SignalPqxdh.Security.ReductionDsl.KeyInd.sbMk,
          _root_.SignalPqxdh.Security.ReductionDsl.KeyInd.buMk,
          _root_.SignalPqxdh.Security.ReductionDsl.KeyInd.u32OfNat,
          _root_.SignalPqxdh.Security.ReductionDsl.KeyInd.encEC,
          _root_.SignalPqxdh.Security.ReductionDsl.KeyInd.encKEM,
          _root_.SignalPqxdh.Security.ReductionDsl.KeyInd.isSomeE,
          _root_.SignalPqxdh.Security.ReductionDsl.KeyInd.eCaseOpt,
          _root_.SignalPqxdh.Security.ReductionDsl.KeyInd.renamePair,
          _root_.ReductionDsl.Env.ofRename,
          l2a_liftGdhToSigDdh_comp_rename, _root_.ReductionDsl.Comp.rename_eval,
          gdhHandle2, wrapSim2, genSpkGdh2B,
          _root_.SignalPqxdh.Security.ReductionDsl.KeyInd.liftGdhToSigDdh,
          s1Forgery, saInner, saTP, s1Pk, s1Fg, s1Upd, s1Mk, s1Target, s1Budget,
          smBase, stSpks, stPrin, pa2SpkTarget, pa2V, pa2Mk,
          _root_.SignalPqxdh.Security.ReductionDsl.KeyInd.natEq,
          _root_.SignalPqxdh.Security.ReductionDsl.KeyInd.nat2Eq,
          l2a_eval_litB32_nil, smUpd_base_eval,
          l2a_eval_liftGdhToSigDdh_sBytes32, l2a_eval_liftGdhToSigDdh_sRandom64,
          l2a_eval_liftGdhToSigDdh_qX25519Base, l2a_eval_liftGdhToSigDdh_qKemKeyGen,
          l2a_eval_liftGdhToSigDdh_qSigSign,
          caseOptV, letV, bindV, caseSumV, eAny, eFind,
          Comp.eval, Expr.eval, Env.get, v,
          _root_.SignalPqxdh.Security.ReductionDsl.KeyInd.Ext.wk,
          _root_.SignalPqxdh.Security.ReductionDsl.KeyInd.Ext.refl_wk',
          _root_.SignalPqxdh.Security.ReductionDsl.KeyInd.Ext.step_wk',
          hTakeSpksK, hTakeSpksQ, hTakePrinK, hTakePrinQ,
          Bool.false_eq_true, ↓reduceIte,
          map_eq_bind_pure_comp, Function.comp_def, bind_assoc, pure_bind]
        cases hDup : List.any sm.1.2.2.1
            (fun x => decide (x.1.1 = u.val) && decide (x.1.2 = j.val))
        · simp only [Bool.false_eq_true, ↓reduceIte]
          cases hFind : List.find? (fun x => decide (x.1 = u.val)) sm.1.2.1
          · simp only [pure_bind]
          · simp only [bind_assoc, pure_bind]
            refine bind_congr_support _ _ _ fun spkSkRaw _ => ?_
            refine bind_congr_support _ _ _ fun spkPkRaw _ => ?_
            refine bind_congr_support _ _ _ fun rSpk _ => ?_
            refine bind_congr_support _ _ _ fun spkSig _ => ?_
            refine bind_congr_support _ _ _ fun seed _ => ?_
            refine bind_congr_support _ _ _ fun kp _ => ?_
            refine bind_congr_support _ _ _ fun rPq _ => ?_
            refine bind_congr_support _ _ _ fun pqSig _ => ?_
            rfl
        · simp only [↓reduceIte, pure_bind]
      · simp only [sigKindGenSpkLeg, sig1KeyActiveHandleC, sig1KeyActivePreDispatchC,
          _root_.SignalPqxdh.Security.ReductionDsl.KeyInd.sig1KeyTargetGenSpkB, fixSigLeg,
          _root_.SignalPqxdh.LegacyCosted.keyIndCodec, _root_.SignalPqxdh.LegacyCosted.keyIndQenc,
          optNatMatchesE_eval, hMatch, rNone, rBundle,
          _root_.SignalPqxdh.Security.ReductionDsl.KeyInd.peIkAPk,
          _root_.SignalPqxdh.Security.ReductionDsl.KeyInd.sbMk,
          _root_.SignalPqxdh.Security.ReductionDsl.KeyInd.buMk,
          _root_.SignalPqxdh.Security.ReductionDsl.KeyInd.u32OfNat,
          _root_.SignalPqxdh.Security.ReductionDsl.KeyInd.encEC,
          _root_.SignalPqxdh.Security.ReductionDsl.KeyInd.encKEM,
          _root_.SignalPqxdh.Security.ReductionDsl.KeyInd.isSomeE,
          s1Forgery, saInner, saTP, s1Pk, s1Fg, s1Base, smBase, s1Upd, s1Mk, s1Target, s1Budget,
          stSpks, stPrin, smUpd_base_eval,
          _root_.SignalPqxdh.Security.ReductionDsl.KeyInd.natEq,
          _root_.SignalPqxdh.Security.ReductionDsl.KeyInd.nat2Eq,
          eval_s1Prim_sBytes32, eval_s1Prim_sRandom64,
          eval_s1Prim_qX25519Base, eval_s1Prim_qKemKeyGen,
          caseOptV, letV, bindV, caseSumV, eAny, eFind,
          Comp.eval, Expr.eval, Env.get, v,
          _root_.SignalPqxdh.Security.ReductionDsl.KeyInd.Ext.wk,
          _root_.SignalPqxdh.Security.ReductionDsl.KeyInd.Ext.refl_wk',
          _root_.SignalPqxdh.Security.ReductionDsl.KeyInd.Ext.step_wk',
          hTakeSpksK, hTakeSpksQ, hTakePrinK, hTakePrinQ,
          Bool.false_eq_true, ↓reduceIte,
          map_eq_bind_pure_comp, Function.comp_def, bind_assoc, pure_bind]
        cases hDup : List.any sm.1.2.2.1
            (fun x => decide (x.1.1 = u.val) && decide (x.1.2 = j.val))
        · simp only [Bool.false_eq_true, ↓reduceIte]
          cases hFind : List.find? (fun x => decide (x.1 = u.val)) sm.1.2.1
          · simp only [pure_bind]
          · cases hBud : decide (sigB = 0)
            · simp only [Bool.false_eq_true, ↓reduceIte, bind_assoc, pure_bind]
              refine bind_congr_support _ _ _ fun spkSk _ => ?_
              refine bind_congr_support _ _ _ fun spkPk _ => ?_
              refine bind_congr_support _ _ _ fun sig1 _ => ?_
              refine bind_congr_support _ _ _ fun seed _ => ?_
              refine bind_congr_support _ _ _ fun kp _ => ?_
              refine bind_congr_support _ _ _ fun sig2 _ => ?_
              rfl
            · simp only [↓reduceIte, pure_bind]
        · simp only [↓reduceIte, pure_bind]
  · intro c ⟨tp?, sm, ord, pk, sigB, fg?⟩ sh r hB hInv hr
    change GdhSimInv S b c (embedVal simTy sm, sh) at hInv
    have hBase := baseOnlineLenInv_of_gdhSimInv hInv
    have hTakePrinK : List.take (keyIndKFuelsOfBudget S b).kOn sm.1.2.1 = sm.1.2.1 :=
      List.take_of_length_le (Nat.le_trans hBase.prin_le (c0_le_kOn hBase hB))
    have hTakeSpksK : List.take (keyIndKFuelsOfBudget S b).kOn sm.1.2.2.1 = sm.1.2.2.1 :=
      List.take_of_length_le (Nat.le_trans hBase.spks_le (c0_le_kOn hBase hB))
    cases fg? with
    | some fg =>
      simp only [sigKindGenSpkLeg, saInner, s1Forgery,
        _root_.SignalPqxdh.Security.ReductionDsl.KeyInd.isSomeE, v,
        _root_.SignalPqxdh.Security.ReductionDsl.KeyInd.Ext.wk,
        _root_.SignalPqxdh.Security.ReductionDsl.KeyInd.Env.get_zero',
        Comp.eval, Expr.eval, ↓reduceIte, mem_support_pure_iff] at hr
      rw [hr]; exact gdhSimInv_unchanged_online hInv rfl
    | none =>
      cases hMatch : optNatMatchesVal tp? u.val
      · simp only [sigKindGenSpkLeg, optNatMatchesE_eval, hMatch, saInner, saTP, s1Fg, s1Pk, s1Upd,
          s1Mk, smBase, wrapSim2, _root_.SignalPqxdh.Security.ReductionDsl.KeyInd.isSomeE,
          s1Forgery, letV, bindV, v, _root_.SignalPqxdh.Security.ReductionDsl.KeyInd.Ext.wk,
          _root_.SignalPqxdh.Security.ReductionDsl.KeyInd.liftGdhToSigDdh_eval,
          _root_.SignalPqxdh.Security.ReductionDsl.KeyInd.embedGdhSigDdh_bind,
          _root_.SignalPqxdh.Security.ReductionDsl.KeyInd.embedGdhSigDdh_pure,
          Comp.eval, Expr.eval, Env.get, Bool.false_eq_true, ↓reduceIte, bind_assoc, pure_bind,
          mem_support_bind_iff, mem_support_pure_iff] at hr
        rcases hr with ⟨p0, hp0, rfl⟩
        exact genSpkGdh2B_inv _ _ _ _ _ rfl rfl hInv rfl
          ((icAtom_mem_support_embedGdhSigDdh _ _).mp hp0)
      · simp only [sigKindGenSpkLeg, _root_.SignalPqxdh.Security.ReductionDsl.KeyInd.sig1KeyTargetGenSpkB,
          optNatMatchesE_eval, hMatch, saInner, saTP, s1Fg, s1Base, smBase, s1Target, s1Pk,
          s1Budget, s1Forgery, s1Upd, s1Mk, smUpd_base_eval, stSpks, stPrin,
          _root_.SignalPqxdh.Security.ReductionDsl.KeyInd.isSomeE,
          _root_.SignalPqxdh.Security.ReductionDsl.KeyInd.natEq,
          _root_.SignalPqxdh.Security.ReductionDsl.KeyInd.nat2Eq,
          eval_s1Prim_sBytes32, eval_s1Prim_sRandom64,
          eval_s1Prim_qX25519Base, eval_s1Prim_qKemKeyGen, eval_qSigDdhSign,
          caseOptV, letV, bindV, eAny, eFind, v,
          _root_.SignalPqxdh.Security.ReductionDsl.KeyInd.Ext.wk,
          _root_.SignalPqxdh.Security.ReductionDsl.KeyInd.Ext.step_wk',
          _root_.SignalPqxdh.Security.ReductionDsl.KeyInd.Ext.refl_wk',
          Comp.eval, Expr.eval, Env.get, hTakeSpksK, hTakePrinK, Bool.false_eq_true, ↓reduceIte,
          pure_bind] at hr
        cases hDup : List.any sm.1.2.2.1
            (fun x => decide (x.1.1 = u.val) && decide (x.1.2 = j.val)) <;>
          simp only [hDup, Bool.false_eq_true, ↓reduceIte] at hr
        · cases hFind : List.find? (fun x => decide (x.1 = u.val)) sm.1.2.1 <;>
            simp only [hFind] at hr
          · simp only [pure_bind, mem_support_pure_iff] at hr
            rw [hr]; exact gdhSimInv_unchanged_online hInv rfl
          · cases hBud : decide (sigB = 0) <;>
              simp only [hBud, Bool.false_eq_true, ↓reduceIte] at hr
            · simp only [bind_assoc, pure_bind, mem_support_bind_iff, mem_support_pure_iff] at hr
              rcases hr with ⟨spkSk, _, spkPk, _, sig1, _, seed, _, kp, _, sig2, _, rfl⟩
              exact GdhSimInv.upd_online_base_pows hInv rfl
                (BaseOnlineLenInv.upd_online hBase rfl
                  (Nat.le_succ _) (Nat.le_refl _) (Nat.le_succ _)
                  le_rfl le_rfl le_rfl le_rfl le_rfl (Nat.le_succ _))
                rfl rfl rfl (Nat.le_succ _)
            · simp only [pure_bind, mem_support_pure_iff] at hr
              rw [hr]; exact gdhSimInv_unchanged_online hInv rfl
        · simp only [pure_bind, mem_support_pure_iff] at hr
          rw [hr]; exact gdhSimInv_unchanged_online hInv rfl

theorem sigKeyInd1KeyKindAtomicProg_hStep_genOPK (S : Setup) (b : QueryBudget)
    (u : Fin S.N_id) (j : Fin S.N_recv) (o : Fin S.N_opk) :
    KeyIndStepSim S b (forgetSig1KeyActiveK S b) (Sig1KeyActiveSimInv S b)
      (sig1KeyKindHandleC S b) (sigKeyInd1KeyActiveAtomicProg S b).handle (.genOPK u j o) := by
  intro c s' hB _hStepB hInv
  rcases s' with ⟨stAt, sh⟩
  have hStAt : stAt = embedVal sig1KeyActiveStTy (projVal sig1KeyActiveStTy stAt) :=
    (AtomicLift.embedVal_projVal sig1KeyActiveStTy stAt).symm
  rw [hStAt] at hInv ⊢
  generalize projVal sig1KeyActiveStTy stAt = stL at hInv ⊢
  rcases stL with ⟨tp?, ⟨sm, ⟨ord, ⟨pk, ⟨bud, fg?⟩⟩⟩⟩⟩
  have hSim : GdhSimInv S b c (embedVal simTy sm, sh) := hInv
  have hBase : BaseOnlineLenInv c sm.1 := baseOnlineLenInv_of_gdhSimInv hSim
  let f := keyIndKFuelsOfBudget S b
  have hc0 : c 0 ≤ f.kOn := hB 0
  have hFkLe : f.kOn ≤ b.q_total := kOn_le_q_total S b
  have hOpksLen : (stOpksList sm.1).length ≤ f.kOn := Nat.le_trans hBase.opks_le hc0
  have hLHS :
      (sig1KeyKindHandleC S b).eval
        (.cons (embedVal sig1KeyActiveStTy (tp?, (sm, (ord, (pk, (bud, fg?))))), sh)
          (.cons ((pqKeyIndCodec S).qenc (.genOPK u j o)) .nil)) =
      (fun r => (embedVal keyIndRespTy r.1, (embedVal sig1KeyActiveStTy r.2, sh))) <$>
        (sigWrapGdh2NoFgLeg fun pa sm bSt x => wrapSim2 pa (genOpkGdh2B f.kOn pa sm bSt x)).eval
          (.cons (tp?, (sm, (ord, (pk, (bud, fg?))))) (.cons (u.val, (j.val, o.val)) .nil)) := by
    unfold sig1KeyKindHandleC
    rw [dispatchKeyIndQ_eval]
    refine l2a_liftSigDdhNoFgArm_eval S _
      (sigWrapGdh2NoFgLeg fun pa sm bSt x => wrapSim2 pa (genOpkGdh2B f.kOn pa sm bSt x))
      (l2a_sigGenOpkLeg_unsup f.kOn)
      _ (tp?, (sm, (ord, (pk, (bud, fg?))))) sh
      ((pqKeyIndCodec S).qenc (.genOPK u j o)) (u.val, (j.val, o.val)) ?_
    rfl
  rw [hLHS]
  have hTakeK : List.take f.kOn sm.1.2.2.2.1 = sm.1.2.2.2.1 := List.take_of_length_le hOpksLen
  have hTakeB : List.take b.q_total sm.1.2.2.2.1 = sm.1.2.2.2.1 :=
    List.take_of_length_le (Nat.le_trans hOpksLen hFkLe)
  have hUnchanged : ∀ rest, Sig1KeyActiveSimInv S b (bumpPred (keyIndSimPred S) c (.genOPK u j o))
      (embedVal sig1KeyActiveStTy (tp?, (sm, rest)), sh) := fun _ =>
    l2a_Sig1KeyActiveSimInv_of_embed (gdhSimInv_unchanged_online hSim rfl)
  constructor
  · rw [l2a_forgetSig1KeyActiveK_embed]
    change _ = (liftKeyIndHandle tlSigDdhKeyInd S (sig1KeyActiveHandleC S b.q_total)).eval _
    rw [liftKeyIndHandle_eval tlSigDdhKeyInd S (sig1KeyActiveHandleC S b.q_total)
      (sig1KeyActiveHandleC_unsupported S b.q_total)
      (l2a_fixSig1KeyActiveSentLeg S b (tp?, (sm, (ord, (pk, (bud, fg?))))))
      (.genOPK u j o)]
    cases fg? with
    | some fgv =>
      simp only [sigWrapGdh2NoFgLeg, sig1KeyActiveHandleC, sig1KeyActivePreDispatchC,
        l2a_fixSig1KeyActiveSentLeg,
        _root_.SignalPqxdh.Security.ReductionDsl.KeyInd.isSomeE,
        s1Forgery, saInner, letV, bindV, caseSumV,
        Comp.eval, Expr.eval, Env.get, v,
        _root_.SignalPqxdh.Security.ReductionDsl.KeyInd.Ext.wk,
        _root_.SignalPqxdh.Security.ReductionDsl.KeyInd.Ext.refl_wk',
        _root_.SignalPqxdh.Security.ReductionDsl.KeyInd.Ext.step_wk',
        map_eq_bind_pure_comp, Function.comp_def, bind_assoc, pure_bind]
      rfl
    | none =>
      simp only [sigWrapGdh2NoFgLeg, sig1KeyActiveHandleC, sig1KeyActivePreDispatchC,
        l2a_fixSig1KeyActiveSentLeg,
        _root_.SignalPqxdh.LegacyCosted.keyIndCodec, _root_.SignalPqxdh.LegacyCosted.keyIndQenc,
        _root_.SignalPqxdh.Security.ReductionDsl.KeyInd.isSomeE,
        _root_.SignalPqxdh.Security.ReductionDsl.KeyInd.eCaseOpt,
        _root_.SignalPqxdh.Security.ReductionDsl.KeyInd.renamePair,
        _root_.ReductionDsl.Env.ofRename,
        l2a_liftGdhToSigDdh_comp_rename, _root_.ReductionDsl.Comp.rename_eval,
        gdhHandle2, wrapSim2, genOpkGdh2B,
        _root_.SignalPqxdh.Security.ReductionDsl.KeyInd.liftGdhToSigDdh,
        s1Forgery, saInner, saTP, s1Pk, s1Fg, s1Upd, s1Mk, s1Target, s1Budget,
        smBase, stOpks, pa2OpkMode, pa2OpkTarget, pa2V, pa2Mk,
        _root_.SignalPqxdh.Security.ReductionDsl.KeyInd.natEq,
        _root_.SignalPqxdh.Security.ReductionDsl.KeyInd.nat2Eq,
        _root_.SignalPqxdh.Security.ReductionDsl.KeyInd.nat3Eq,
        l2a_eval_liftGdhToSigDdh_sBytes32, l2a_eval_liftGdhToSigDdh_qX25519Base,
        letV, bindV, caseSumV, eAny,
        Comp.eval, Expr.eval, Env.get, v,
        _root_.SignalPqxdh.Security.ReductionDsl.KeyInd.Ext.wk,
        _root_.SignalPqxdh.Security.ReductionDsl.KeyInd.Ext.refl_wk',
        _root_.SignalPqxdh.Security.ReductionDsl.KeyInd.Ext.step_wk',
        hTakeK, hTakeB, Bool.false_eq_true, Bool.false_and, ↓reduceIte,
        map_eq_bind_pure_comp, Function.comp_def, bind_assoc, pure_bind]
      cases hDup : List.any sm.1.2.2.2.1
          (fun x => decide (x.1.1 = u.val) && (decide (x.1.2.1 = j.val) && decide (x.1.2.2 = o.val)))
      · simp only [Bool.false_eq_true, ↓reduceIte, bind_assoc, pure_bind]
        refine bind_congr_support _ _ _ fun opkSkRaw _ => ?_
        refine bind_congr_support _ _ _ fun opkPkRaw _ => ?_
        rfl
      · simp only [↓reduceIte, pure_bind]
        rfl
  · intro p hp
    rw [map_eq_bind_pure_comp, mem_support_bind_iff] at hp
    obtain ⟨r, hr, hp⟩ := hp
    rw [Function.comp_apply, mem_support_pure_iff] at hp
    subst hp
    cases fg? with
    | some fgv =>
      simp only [sigWrapGdh2NoFgLeg, _root_.SignalPqxdh.Security.ReductionDsl.KeyInd.isSomeE,
        s1Forgery, saInner, Comp.eval, Expr.eval, Env.get, v,
        _root_.SignalPqxdh.Security.ReductionDsl.KeyInd.Ext.wk,
        _root_.SignalPqxdh.Security.ReductionDsl.KeyInd.Ext.refl_wk',
        ↓reduceIte, mem_support_pure_iff] at hr
      subst hr
      exact hUnchanged _
    | none =>
      simp only [sigWrapGdh2NoFgLeg, wrapSim2, genOpkGdh2B,
        _root_.SignalPqxdh.Security.ReductionDsl.KeyInd.liftGdhToSigDdh,
        _root_.SignalPqxdh.Security.ReductionDsl.KeyInd.isSomeE,
        _root_.SignalPqxdh.Security.ReductionDsl.KeyInd.eCaseOpt,
        s1Forgery, saInner, saTP, s1Pk, s1Fg, s1Upd, s1Mk, s1Target, s1Budget,
        smBase, stOpks, pa2OpkMode, pa2OpkTarget, pa2V, pa2Mk,
        _root_.SignalPqxdh.Security.ReductionDsl.KeyInd.natEq,
        _root_.SignalPqxdh.Security.ReductionDsl.KeyInd.nat2Eq,
        _root_.SignalPqxdh.Security.ReductionDsl.KeyInd.nat3Eq,
        l2a_eval_liftGdhToSigDdh_sBytes32, l2a_eval_liftGdhToSigDdh_qX25519Base,
        l2a_smUpd_base_eval,
        letV, bindV, eAny, Comp.eval, Expr.eval, Env.get, v,
        _root_.SignalPqxdh.Security.ReductionDsl.KeyInd.Ext.wk,
        _root_.SignalPqxdh.Security.ReductionDsl.KeyInd.Ext.refl_wk',
        _root_.SignalPqxdh.Security.ReductionDsl.KeyInd.Ext.step_wk',
        Bool.false_eq_true, Bool.false_and, ↓reduceIte, bind_assoc, pure_bind, hTakeK] at hr
      cases hDup : List.any sm.1.2.2.2.1
          (fun x => decide (x.1.1 = u.val) && (decide (x.1.2.1 = j.val) && decide (x.1.2.2 = o.val))) <;>
        simp only [hDup, Bool.false_eq_true, ↓reduceIte, bind_assoc, pure_bind] at hr
      · simp only [mem_support_bind_iff, mem_support_pure_iff] at hr
        obtain ⟨opkSkRaw, _, opkPkRaw, _, rfl⟩ := hr
        apply l2a_Sig1KeyActiveSimInv_of_embed
        apply GdhSimInv.upd_online_base_pows (t := .genOPK u j o) hSim rfl
        · exact BaseOnlineLenInv.upd_online hBase rfl (Nat.le_succ _) (Nat.le_succ _) (Nat.le_refl _)
            le_rfl le_rfl le_rfl le_rfl le_rfl (Nat.le_succ _)
        · rfl
        · rfl
        · rfl
        · exact Nat.le_succ _
      · rw [mem_support_pure_iff] at hr; subst hr
        exact hUnchanged _

theorem sigKeyInd1KeyKindAtomicProg_hStep_registerKey (S : Setup) (b : QueryBudget)
    (sk : Bytes) :
    KeyIndStepSim S b (forgetSig1KeyActiveK S b) (Sig1KeyActiveSimInv S b)
      (sig1KeyKindHandleC S b) (sigKeyInd1KeyActiveAtomicProg S b).handle (.registerKey sk) := by
  intro c ⟨stA, sh⟩ _ _ hInv
  set stL := projVal sig1KeyActiveStTy stA
  have hStA : stA = embedVal sig1KeyActiveStTy stL :=
    (AtomicLift.embedVal_projVal sig1KeyActiveStTy stA).symm
  rw [hStA] at hInv ⊢
  unfold sig1KeyKindHandleC; dsimp only; rw [dispatchKeyIndQ_eval]; dsimp only
  rw [icAtom_liftNoFg_eval S _ icAtom_sigRegKey_unsup sk stL sh _]
  have hFg : forgetSig1KeyActiveK S b (embedVal sig1KeyActiveStTy stL, sh) =
      embedVal sig1KeyActiveStTy (icAtom_fixSigLeg S b stL) := rfl
  have hRhs : (sigKeyInd1KeyActiveAtomicProg S b).handle.eval
      (.cons (forgetSig1KeyActiveK S b (embedVal sig1KeyActiveStTy stL, sh))
        (.cons ((pqKeyIndCodec S).qenc (.registerKey sk)) .nil)) =
      embedVal (.prod keyIndRespTy sig1KeyActiveStTy) <$>
        (sig1KeyActiveHandleC S b.q_total).eval
          (.cons (icAtom_fixSigLeg S b stL)
            (.cons ((_root_.SignalPqxdh.LegacyCosted.keyIndCodec S).qenc (.registerKey sk)) .nil)) := by
    rw [hFg]; exact liftKeyIndHandle_eval tlSigDdhKeyInd S (sig1KeyActiveHandleC S b.q_total)
      (sig1KeyActiveHandleC_unsupported S b.q_total) (icAtom_fixSigLeg S b stL) (.registerKey sk)
  rcases stL with ⟨tp?, sm, ord, pk, sigB, fg?⟩
  cases fg? with
  | some fg =>
    have hL : (sigWrapGdh2NoFgLeg fun pa sm bSt sk => wrapSim2 pa (registerGdhB sm bSt sk)).eval
        (.cons (tp?, (sm, (ord, (pk, (sigB, some fg))))) (.cons (t := B 32) sk .nil)) =
        pure ((rNone : Expr pqxdhOps [] keyIndRespTy).eval .nil,
          (tp?, (sm, (ord, (pk, (sigB, some fg)))))) := by
      simp [sigWrapGdh2NoFgLeg, saInner, s1Forgery,
        _root_.SignalPqxdh.Security.ReductionDsl.KeyInd.isSomeE, rNone,
        Comp.eval, Expr.eval, v, Ext.wk]
    have hR : (sig1KeyActiveHandleC S b.q_total).eval
        (.cons (icAtom_fixSigLeg S b (tp?, (sm, (ord, (pk, (sigB, some fg))))))
          (.cons ((_root_.SignalPqxdh.LegacyCosted.keyIndCodec S).qenc (.registerKey sk)) .nil)) =
        pure ((rNone : Expr pqxdhOps [] keyIndRespTy).eval .nil,
          icAtom_fixSigLeg S b (tp?, (sm, (ord, (pk, (sigB, some fg)))))) := by
      simp [sig1KeyActiveHandleC, sig1KeyActivePreDispatchC, icAtom_fixSigLeg, saInner, s1Forgery,
        _root_.SignalPqxdh.Security.ReductionDsl.KeyInd.isSomeE, rNone, bindV, caseSumV,
        Comp.eval, Expr.eval, v, Ext.wk]
    rw [hL]
    refine ⟨?_, ?_⟩
    · rw [hRhs, hR]; rfl
    · simp only [map_pure, support_pure, Set.mem_singleton_iff, forall_eq]
      exact gdhSimInv_unchanged_online hInv rfl
  | none =>
    set cReg := (registerGdhB (.zero : Var [simTy, keyIndStateTy, B 32] simTy)
      (.succ .zero : Var [simTy, keyIndStateTy, B 32] keyIndStateTy)
      (.succ (.succ .zero) : Var [simTy, keyIndStateTy, B 32] (B 32))).eval
      (.cons sm (.cons sm.1 (.cons (t := B 32) sk .nil)))
    have hL : (sigWrapGdh2NoFgLeg fun pa sm bSt sk => wrapSim2 pa (registerGdhB sm bSt sk)).eval
        (.cons (tp?, (sm, (ord, (pk, (sigB, none))))) (.cons (t := B 32) sk .nil)) =
        (fun r0 => (r0.1, (tp?, (r0.2, (ord, (pk, (sigB, none))))))) <$>
          _root_.SignalPqxdh.Security.Sig1Key.embedGdhSigDdh cReg := by
      simp only [sigWrapGdh2NoFgLeg, wrapSim2, saInner, saTP, s1Forgery, s1Pk, s1Fg, s1Upd, s1Mk,
        s1Target, s1Budget, smBase, _root_.SignalPqxdh.Security.ReductionDsl.KeyInd.isSomeE,
        _root_.SignalPqxdh.Security.ReductionDsl.KeyInd.liftGdhToSigDdh_eval,
        letV, bindV, Comp.eval, Expr.eval, v, Ext.wk, Env.get, pure_bind, Bool.false_eq_true, ↓reduceIte]
      rw [icAtom_registerGdhB_eval_eq]
      simp only [_root_.SignalPqxdh.Security.ReductionDsl.KeyInd.embedGdhSigDdh_bind,
        _root_.SignalPqxdh.Security.ReductionDsl.KeyInd.embedGdhSigDdh_pure,
        map_eq_bind_pure_comp, Function.comp_def, bind_assoc, pure_bind, Expr.eval, v, Ext.wk, Env.get]
      rfl
    have hPre : (sig1KeyActivePreDispatchC S b.q_total
        (.zero : Var [sig1KeyActiveStTy, keyIndQueryTy] sig1KeyActiveStTy)
        (.succ .zero : Var [sig1KeyActiveStTy, keyIndQueryTy] keyIndQueryTy)).eval
        (.cons (t := sig1KeyActiveStTy) (icAtom_fixSigLeg S b (tp?, (sm, (ord, (pk, (sigB, none))))))
          (.cons (t := keyIndQueryTy)
            (_root_.SignalPqxdh.LegacyCosted.keyIndQenc (S := S) (.registerKey sk)) .nil)) =
        pure (.inr ()) := by
      simp [sig1KeyActivePreDispatchC, icAtom_fixSigLeg, _root_.SignalPqxdh.LegacyCosted.keyIndQenc,
        saInner, s1Forgery, _root_.SignalPqxdh.Security.ReductionDsl.KeyInd.isSomeE,
        caseSumV, Comp.eval, Expr.eval, v, Ext.wk]
    have hR : (sig1KeyActiveHandleC S b.q_total).eval
        (.cons (icAtom_fixSigLeg S b (tp?, (sm, (ord, (pk, (sigB, none))))))
          (.cons ((_root_.SignalPqxdh.LegacyCosted.keyIndCodec S).qenc (.registerKey sk)) .nil)) =
        (fun r0 => (r0.1, icAtom_fixSigLeg S b (tp?, (r0.2, (ord, (pk, (sigB, none))))))) <$>
          _root_.SignalPqxdh.Security.Sig1Key.embedGdhSigDdh cReg := by
      dsimp only [_root_.SignalPqxdh.LegacyCosted.keyIndCodec]
      simp only [sig1KeyActiveHandleC, bindV, caseSumV, letV, Comp.eval]
      rw [hPre]
      simp only [pure_bind, _root_.SignalPqxdh.Security.ReductionDsl.KeyInd.liftGdhToSigDdh_eval,
        _root_.ReductionDsl.Comp.rename_eval, _root_.ReductionDsl.Env.ofRename,
        _root_.ReductionDsl.Env.get, _root_.SignalPqxdh.Security.ReductionDsl.KeyInd.renamePair,
        gdhHandle2, _root_.SignalPqxdh.LegacyCosted.keyIndQenc, wrapSim2, smBase, icAtom_fixSigLeg,
        s1Pk, letV, bindV, caseSumV, Comp.eval, Expr.eval, v, Ext.wk]
      rw [icAtom_registerGdhB_eval_eq]
      simp only [_root_.SignalPqxdh.Security.ReductionDsl.KeyInd.embedGdhSigDdh_bind,
        _root_.SignalPqxdh.Security.ReductionDsl.KeyInd.embedGdhSigDdh_pure,
        map_eq_bind_pure_comp, Function.comp_def, bind_assoc, pure_bind, Expr.eval, v, Ext.wk, Env.get]
      rfl
    rw [hL]
    refine ⟨?_, ?_⟩
    · simp only [hRhs, hR, Functor.map_map]; rfl
    · intro p hp
      rw [Functor.map_map] at hp
      simp only [map_eq_bind_pure_comp, Function.comp_def,
        mem_support_bind_iff, mem_support_pure_iff] at hp
      rcases hp with ⟨r0, hr0, rfl⟩
      exact registerGdhB_inv (S := S) (b := b) (c := c) (t := .registerKey sk)
        (smVal := sm) (sh := sh)
        (.zero : Var [simTy, keyIndStateTy, B 32] simTy)
        (.succ .zero : Var [simTy, keyIndStateTy, B 32] keyIndStateTy)
        (.succ (.succ .zero) : Var [simTy, keyIndStateTy, B 32] (B 32))
        (.cons sm (.cons sm.1 (.cons (t := B 32) sk .nil)))
        rfl rfl hInv rfl ((icAtom_mem_support_embedGdhSigDdh _ _).mp hr0)

theorem fgKeyInd1KeyGapDhKindAtomicProg_hStep_initPrin (S : Setup) (b : QueryBudget)
    (u : Fin S.N_id) :
    KeyIndStepSim S b (forgetGdh1KeyActiveK S b) (Gdh1KeyActiveSimInv S b)
      (gdh1KeyKindHandleC S b) (fgKeyInd1KeyGapDhActiveAtomicProg S b).handle (.initPrin u) := by
  intro c s' hB _hStepB hInv
  rcases s' with ⟨stAt, sh⟩
  have hStAt : stAt = embedVal gdh1KeyActiveStateTy (projVal gdh1KeyActiveStateTy stAt) :=
    (AtomicLift.embedVal_projVal gdh1KeyActiveStateTy stAt).symm
  rw [hStAt] at hInv ⊢
  generalize projVal gdh1KeyActiveStateTy stAt = stL at hInv ⊢
  rcases stL with ⟨⟨⟨pa, sm⟩, sigB⟩, ⟨tp?, cnt⟩⟩
  have hSim : GdhSimInv S b c (embedVal simTy sm, sh) := hInv.sim_inv
  have hCnt : cnt ≤ c 0 := hInv.sendOpkCnt_le
  have hBase : BaseOnlineLenInv c sm.1 := baseOnlineLenInv_of_gdhSimInv hSim
  let f := keyIndKFuelsOfBudget S b
  have hc0 : c 0 ≤ f.kOn := hB 0
  have hFkLe : f.kOn ≤ b.q_total := kOn_le_q_total S b
  have hPrinLen : (stPrinList sm.1).length ≤ f.kOn := Nat.le_trans hBase.prin_le hc0
  have hLHS :
      (gdh1KeyKindHandleC S b).eval
        (.cons (embedVal gdh1KeyActiveStateTy (((pa, sm), sigB), (tp?, cnt)), sh)
          (.cons ((pqKeyIndCodec S).qenc (.initPrin u)) .nil)) =
      (fun r => (embedVal keyIndRespTy r.1, (embedVal gdh1KeyActiveStateTy r.2, sh))) <$>
        (gdhKindInitPrinLeg f.kOn).eval
          (.cons (((pa, sm), sigB), (tp?, cnt)) (.cons u.val .nil)) := by
    unfold gdh1KeyKindHandleC
    rw [dispatchKeyIndQ_eval]
    refine l2a_liftSigDdhNoFgArm_eval S _ (gdhKindInitPrinLeg f.kOn)
      (initPrin1KeyActiveGdhB_unsupported f.kOn .zero (.succ .zero))
      _ (((pa, sm), sigB), (tp?, cnt)) sh ((pqKeyIndCodec S).qenc (.initPrin u)) u.val ?_
    rfl
  rw [hLHS]
  rcases pa with ⟨u0, v0, up0, prinFlag, prinIdx, dhFlag, ephIdx, spkIdx, opkMode, opkIdx, mode⟩
  have hTakeK : List.take f.kOn sm.1.2.1 = sm.1.2.1 := List.take_of_length_le hPrinLen
  have hTakeB : List.take b.q_total sm.1.2.1 = sm.1.2.1 :=
    List.take_of_length_le (Nat.le_trans hPrinLen hFkLe)
  have hBeq : decide (sm.1.2.1.length = prinIdx) = decide (sm.1.2.1.length = fixSent S b prinIdx) :=
    l2a_decide_eq_fixSent_of_le_mOn hPrinLen
  have hBump0 : bumpPred (keyIndSimPred S) c (.initPrin u) 0 = c 0 + 1 := bumpPred_online_0 rfl
  constructor
  · rw [l2a_forgetGdh1KeyActiveK_embed]
    change _ = (liftKeyIndHandle tlSigDdhKeyInd S (gdh1KeyActiveHandle S b.q_total)).eval _
    rw [l2a_liftKeyIndHandle_eval_mapComp tlSigDdhKeyInd S (gdh1KeyActiveHandle S b.q_total)
      (l2a_fixGdh1KeyActiveSentLeg S b
        ((((u0, v0, up0, prinFlag, prinIdx, dhFlag, ephIdx, spkIdx, opkMode, opkIdx, mode), sm),
          sigB), tp?, cnt))
      (.initPrin u)]
    unfold gdh1KeyActiveHandle caseSumV
    rw [l2a_mapComp_caseSum_inl tlSigDdhKeyInd _ _ _ _ _ rfl]
    rw [mapComp_eval tlSigDdhKeyInd _ (initPrin1KeyActiveGdhB_unsupported b.q_total _ _)]
    simp only [gdhKindInitPrinLeg, initPrin1KeyActiveGdhB,
      l2a_fixGdh1KeyActiveSentLeg, l2a_fixParamsSentLeg,
      letV, bindV, eAny, smBase, stPrin, paPrinFlag, paPrinIdx, paUp,
      _root_.SignalPqxdh.Security.ReductionDsl.KeyInd.natEq,
      l2a_eval_liftGdhComp_sBytes32, l2a_eval_liftGdhComp_qX25519Base,
      Comp.eval, Expr.eval, Env.get, v,
      _root_.SignalPqxdh.Security.ReductionDsl.KeyInd.Ext.wk,
      _root_.SignalPqxdh.Security.ReductionDsl.KeyInd.Ext.refl_wk',
      _root_.SignalPqxdh.Security.ReductionDsl.KeyInd.Ext.step_wk',
      hTakeK, hTakeB,
      map_eq_bind_pure_comp, Function.comp_def, bind_assoc, pure_bind]
    rw [hBeq]
    cases hDup : List.any sm.1.2.1 (fun x => decide (x.1 = u.val))
    · simp only [Bool.false_eq_true, ↓reduceIte, bind_assoc, pure_bind]
      refine bind_congr_support _ _ _ fun sk0 _ => ?_
      refine bind_congr_support _ _ _ fun pk0 _ => ?_
      rfl
    · simp only [↓reduceIte, pure_bind]
      rfl
  · intro p hp
    rw [map_eq_bind_pure_comp, mem_support_bind_iff] at hp
    obtain ⟨r, hr, hp⟩ := hp
    rw [Function.comp_apply, mem_support_pure_iff] at hp
    subst hp
    simp only [gdhKindInitPrinLeg, initPrin1KeyActiveGdhB, letV, bindV, eAny, smBase, stPrin,
      _root_.SignalPqxdh.Security.ReductionDsl.KeyInd.natEq,
      l2a_eval_liftGdhComp_sBytes32, l2a_eval_liftGdhComp_qX25519Base,
      l2a_smUpd_base_eval,
      Comp.eval, Expr.eval, Env.get, v,
      _root_.SignalPqxdh.Security.ReductionDsl.KeyInd.Ext.wk,
      _root_.SignalPqxdh.Security.ReductionDsl.KeyInd.Ext.refl_wk',
      _root_.SignalPqxdh.Security.ReductionDsl.KeyInd.Ext.step_wk',
      pure_bind, hTakeK] at hr
    cases hDup : List.any sm.1.2.1 (fun x => decide (x.1 = u.val)) <;>
      simp only [hDup, Bool.false_eq_true, ↓reduceIte] at hr
    · simp only [mem_support_bind_iff, mem_support_pure_iff] at hr
      obtain ⟨sk0, _, pk0, _, rfl⟩ := hr
      apply l2a_Gdh1KeyActiveSimInv_of_embed
      · apply GdhSimInv.upd_online_base_pows (t := .initPrin u) hSim rfl
        · exact BaseOnlineLenInv.upd_online hBase rfl (Nat.le_refl _) (Nat.le_succ _) (Nat.le_succ _)
            le_rfl le_rfl le_rfl le_rfl le_rfl (Nat.le_succ _)
        · rfl
        · rfl
        · rfl
        · exact Nat.le_succ _
      · rw [hBump0]; exact Nat.le_trans hCnt (Nat.le_succ _)
    · rw [mem_support_pure_iff] at hr; subst hr
      apply l2a_Gdh1KeyActiveSimInv_of_embed (gdhSimInv_unchanged_online hSim rfl)
      rw [hBump0]; exact Nat.le_trans hCnt (Nat.le_succ _)

theorem fgKeyInd1KeyGapDhKindAtomicProg_hStep_genSPK (S : Setup) (b : QueryBudget)
    (u : Fin S.N_id) (j : Fin S.N_recv) :
    KeyIndStepSim S b (forgetGdh1KeyActiveK S b) (Gdh1KeyActiveSimInv S b)
      (gdh1KeyKindHandleC S b) (fgKeyInd1KeyGapDhActiveAtomicProg S b).handle (.genSPK u j) := by
  intro c s' hB _hStepB hInv
  rcases s' with ⟨stAt, sh⟩
  have hStAt : stAt = embedVal gdh1KeyActiveStateTy (projVal gdh1KeyActiveStateTy stAt) :=
    (AtomicLift.embedVal_projVal gdh1KeyActiveStateTy stAt).symm
  rw [hStAt] at hInv ⊢
  generalize projVal gdh1KeyActiveStateTy stAt = stL at hInv ⊢
  rcases stL with ⟨⟨⟨pa, sm⟩, sigB⟩, ⟨tp?, cnt⟩⟩
  have hSim : GdhSimInv S b c (embedVal simTy sm, sh) := hInv.sim_inv
  have hCnt : cnt ≤ c 0 := hInv.sendOpkCnt_le
  have hBase : BaseOnlineLenInv c sm.1 := baseOnlineLenInv_of_gdhSimInv hSim
  let f := keyIndKFuelsOfBudget S b
  have hc0 : c 0 ≤ f.kOn := hB 0
  have hFkLe : f.kOn ≤ b.q_total := kOn_le_q_total S b
  have hPrinLen : (stPrinList sm.1).length ≤ f.kOn := Nat.le_trans hBase.prin_le hc0
  have hSpksLen : (stSpksList sm.1).length ≤ f.kOn := Nat.le_trans hBase.spks_le hc0
  have hLHS :
      (gdh1KeyKindHandleC S b).eval
        (.cons (embedVal gdh1KeyActiveStateTy (((pa, sm), sigB), (tp?, cnt)), sh)
          (.cons ((pqKeyIndCodec S).qenc (.genSPK u j)) .nil)) =
      (fun r => (embedVal keyIndRespTy r.1, (embedVal gdh1KeyActiveStateTy r.2, sh))) <$>
        (gdhKindGenSpkLeg f.kOn).eval
          (.cons (((pa, sm), sigB), (tp?, cnt)) (.cons (u.val, j.val) .nil)) := by
    unfold gdh1KeyKindHandleC
    rw [dispatchKeyIndQ_eval]
    refine l2a_liftSigDdhNoFgArm_eval S _ (gdhKindGenSpkLeg f.kOn)
      (genSpk1KeyActiveGdhB_unsupported f.kOn .zero (.succ .zero))
      _ (((pa, sm), sigB), (tp?, cnt)) sh ((pqKeyIndCodec S).qenc (.genSPK u j)) (u.val, j.val) ?_
    rfl
  rw [hLHS]
  rcases pa with ⟨u0, v0, up0, prinFlag, prinIdx, dhFlag, ephIdx, spkIdx, opkMode, opkIdx, mode⟩
  have hTakePrinK : List.take f.kOn sm.1.2.1 = sm.1.2.1 := List.take_of_length_le hPrinLen
  have hTakePrinB : List.take b.q_total sm.1.2.1 = sm.1.2.1 :=
    List.take_of_length_le (Nat.le_trans hPrinLen hFkLe)
  have hTakeSpksK : List.take f.kOn sm.1.2.2.1 = sm.1.2.2.1 := List.take_of_length_le hSpksLen
  have hTakeSpksB : List.take b.q_total sm.1.2.2.1 = sm.1.2.2.1 :=
    List.take_of_length_le (Nat.le_trans hSpksLen hFkLe)
  have hBeq : decide (sm.1.2.2.1.length = spkIdx) = decide (sm.1.2.2.1.length = fixSent S b spkIdx) :=
    l2a_decide_eq_fixSent_of_le_mOn hSpksLen
  have hBump0 : bumpPred (keyIndSimPred S) c (.genSPK u j) 0 = c 0 + 1 := bumpPred_online_0 rfl
  have hUnchanged : ∀ tpOpt, Gdh1KeyActiveSimInv S b (bumpPred (keyIndSimPred S) c (.genSPK u j))
      (embedVal gdh1KeyActiveStateTy
        ((((u0, v0, up0, prinFlag, prinIdx, dhFlag, ephIdx, spkIdx, opkMode, opkIdx, mode), sm),
          sigB), (tpOpt, cnt)), sh) := fun _ =>
    l2a_Gdh1KeyActiveSimInv_of_embed (gdhSimInv_unchanged_online hSim rfl)
      (by rw [hBump0]; exact Nat.le_trans hCnt (Nat.le_succ _))
  have hGrown : ∀ tpOpt sigB' bE,
      Gdh1KeyActiveSimInv S b (bumpPred (keyIndSimPred S) c (.genSPK u j))
        (embedVal gdh1KeyActiveStateTy
          ((((u0, v0, up0, prinFlag, prinIdx, dhFlag, ephIdx, spkIdx, opkMode, opkIdx, mode),
            ((sm.1.1, (sm.1.2.1, (((u.val, j.val), bE) :: sm.1.2.2.1, sm.1.2.2.2))), sm.2)),
            sigB'), (tpOpt, cnt)), sh) := by
    intro tpOpt sigB' bE
    apply l2a_Gdh1KeyActiveSimInv_of_embed
    · apply GdhSimInv.upd_online_base_pows (t := .genSPK u j) hSim rfl
      · exact BaseOnlineLenInv.upd_online hBase rfl (Nat.le_succ _) (Nat.le_refl _) (Nat.le_succ _)
          le_rfl le_rfl le_rfl le_rfl le_rfl (Nat.le_succ _)
      · rfl
      · rfl
      · rfl
      · exact Nat.le_succ _
    · rw [hBump0]; exact Nat.le_trans hCnt (Nat.le_succ _)
  constructor
  · rw [l2a_forgetGdh1KeyActiveK_embed]
    change _ = (liftKeyIndHandle tlSigDdhKeyInd S (gdh1KeyActiveHandle S b.q_total)).eval _
    rw [l2a_liftKeyIndHandle_eval_mapComp tlSigDdhKeyInd S (gdh1KeyActiveHandle S b.q_total)
      (l2a_fixGdh1KeyActiveSentLeg S b
        ((((u0, v0, up0, prinFlag, prinIdx, dhFlag, ephIdx, spkIdx, opkMode, opkIdx, mode), sm),
          sigB), tp?, cnt))
      (.genSPK u j)]
    unfold gdh1KeyActiveHandle caseSumV
    rw [l2a_mapComp_caseSum_inr tlSigDdhKeyInd _ _ _ _ _ rfl]
    rw [l2a_mapComp_caseSum_inr tlSigDdhKeyInd _ _ _ _ _ rfl]
    rw [l2a_mapComp_caseSum_inl tlSigDdhKeyInd _ _ _ _ _ rfl]
    rw [mapComp_eval tlSigDdhKeyInd _ (genSpk1KeyActiveGdhB_unsupported b.q_total _ _)]
    cases tp? with
    | none =>
      simp only [gdhKindGenSpkLeg, genSpk1KeyActiveGdhB, genSpkGdhActiveB, liftGdhComp,
        l2a_fixGdh1KeyActiveSentLeg, l2a_fixParamsSentLeg,
        optNatMatchesE, _root_.SignalPqxdh.Security.ReductionDsl.KeyInd.eLet2,
        _root_.SignalPqxdh.Security.ReductionDsl.KeyInd.eLet,
        _root_.SignalPqxdh.Security.ReductionDsl.KeyInd.eCaseOpt,
        caseOptV, letV, bindV, eAny, eFind,
        smBase, stSpks, stPrin, paSpkIdx, paV,
        _root_.SignalPqxdh.Security.ReductionDsl.KeyInd.natEq,
        _root_.SignalPqxdh.Security.ReductionDsl.KeyInd.nat2Eq,
        l2a_eval_litB32_nil, l2a_smUpd_base_eval,
        l2a_eval_liftGdhComp_sBytes32, l2a_eval_liftGdhComp_sRandom64,
        l2a_eval_liftGdhComp_qX25519Base, l2a_eval_liftGdhComp_qKemKeyGen,
        l2a_eval_liftGdhComp_qSigSign,
        Comp.eval, Expr.eval, Env.get, v,
        _root_.SignalPqxdh.Security.ReductionDsl.KeyInd.Ext.wk,
        _root_.SignalPqxdh.Security.ReductionDsl.KeyInd.Ext.refl_wk',
        _root_.SignalPqxdh.Security.ReductionDsl.KeyInd.Ext.step_wk',
        hTakePrinK, hTakePrinB, hTakeSpksK, hTakeSpksB,
        Bool.false_eq_true, ↓reduceIte,
        map_eq_bind_pure_comp, Function.comp_def, bind_assoc, pure_bind, Prod.map, id_eq]
      rw [hBeq]
      cases hDup : List.any sm.1.2.2.1 (fun x => decide (x.1.1 = u.val) && decide (x.1.2 = j.val))
      · simp only [Bool.false_eq_true, ↓reduceIte]
        cases hFind : List.find? (fun x => decide (x.1 = u.val)) sm.1.2.1
        · simp only [pure_bind]; rfl
        · simp only [bind_assoc, pure_bind]
          refine bind_congr_support _ _ _ fun spkSkRaw _ => ?_
          refine bind_congr_support _ _ _ fun spkPkRaw _ => ?_
          refine bind_congr_support _ _ _ fun rSpk _ => ?_
          refine bind_congr_support _ _ _ fun spkSig _ => ?_
          refine bind_congr_support _ _ _ fun seed _ => ?_
          refine bind_congr_support _ _ _ fun kp _ => ?_
          refine bind_congr_support _ _ _ fun rPq _ => ?_
          refine bind_congr_support _ _ _ fun pqSig _ => ?_
          rfl
      · simp only [↓reduceIte, pure_bind]; rfl
    | some tp =>
      simp only [gdhKindGenSpkLeg, genSpk1KeyActiveGdhB,
        l2a_fixGdh1KeyActiveSentLeg,
        optNatMatchesE, _root_.SignalPqxdh.Security.ReductionDsl.KeyInd.eLet2,
        _root_.SignalPqxdh.Security.ReductionDsl.KeyInd.eLet,
        _root_.SignalPqxdh.Security.ReductionDsl.KeyInd.eCaseOpt,
        letV, smBase, _root_.SignalPqxdh.Security.ReductionDsl.KeyInd.natEq,
        Comp.eval, Expr.eval, Env.get, v,
        _root_.SignalPqxdh.Security.ReductionDsl.KeyInd.Ext.wk,
        _root_.SignalPqxdh.Security.ReductionDsl.KeyInd.Ext.refl_wk',
        _root_.SignalPqxdh.Security.ReductionDsl.KeyInd.Ext.step_wk',
        pure_bind]
      cases hTp : decide (u.val = tp)
      · simp only [Bool.false_eq_true, ↓reduceIte, genSpkGdhActiveB, liftGdhComp,
          l2a_fixParamsSentLeg,
          caseOptV, letV, bindV, eAny, eFind, stSpks, stPrin, paSpkIdx, paV,
          _root_.SignalPqxdh.Security.ReductionDsl.KeyInd.natEq,
          _root_.SignalPqxdh.Security.ReductionDsl.KeyInd.nat2Eq,
          l2a_eval_litB32_nil, l2a_smUpd_base_eval,
          l2a_eval_liftGdhComp_sBytes32, l2a_eval_liftGdhComp_sRandom64,
          l2a_eval_liftGdhComp_qX25519Base, l2a_eval_liftGdhComp_qKemKeyGen,
          l2a_eval_liftGdhComp_qSigSign,
          Comp.eval, Expr.eval, Env.get, v,
          _root_.SignalPqxdh.Security.ReductionDsl.KeyInd.Ext.wk,
          _root_.SignalPqxdh.Security.ReductionDsl.KeyInd.Ext.refl_wk',
          _root_.SignalPqxdh.Security.ReductionDsl.KeyInd.Ext.step_wk',
          hTakePrinK, hTakePrinB, hTakeSpksK, hTakeSpksB,
          map_eq_bind_pure_comp, Function.comp_def, bind_assoc, pure_bind, Prod.map, id_eq]
        rw [hBeq]
        cases hDup : List.any sm.1.2.2.1 (fun x => decide (x.1.1 = u.val) && decide (x.1.2 = j.val))
        · simp only [Bool.false_eq_true, ↓reduceIte]
          cases hFind : List.find? (fun x => decide (x.1 = u.val)) sm.1.2.1
          · simp only [pure_bind]; rfl
          · simp only [bind_assoc, pure_bind]
            refine bind_congr_support _ _ _ fun spkSkRaw _ => ?_
            refine bind_congr_support _ _ _ fun spkPkRaw _ => ?_
            refine bind_congr_support _ _ _ fun rSpk _ => ?_
            refine bind_congr_support _ _ _ fun spkSig _ => ?_
            refine bind_congr_support _ _ _ fun seed _ => ?_
            refine bind_congr_support _ _ _ fun kp _ => ?_
            refine bind_congr_support _ _ _ fun rPq _ => ?_
            refine bind_congr_support _ _ _ fun pqSig _ => ?_
            rfl
        · simp only [↓reduceIte, pure_bind]; rfl
      · simp only [↓reduceIte,
          l2a_fixParamsSentLeg,
          caseOptV, bindV, eAny, eFind, stSpks, stPrin, paSpkIdx, paV,
          _root_.SignalPqxdh.Security.ReductionDsl.KeyInd.natEq,
          _root_.SignalPqxdh.Security.ReductionDsl.KeyInd.nat2Eq,
          l2a_eval_litB32_nil, l2a_smUpd_base_eval,
          l2a_eval_liftGdhComp_sBytes32, l2a_eval_liftGdhComp_sRandom64,
          l2a_eval_liftGdhComp_qX25519Base, l2a_eval_liftGdhComp_qKemKeyGen,
          l2a_eval_sigChalQ_dsl,
          Comp.eval, Expr.eval, Env.get,
          hTakePrinK, hTakePrinB, hTakeSpksK, hTakeSpksB,
          map_eq_bind_pure_comp, Function.comp_def, bind_assoc, pure_bind, Prod.map, id_eq]
        rw [hBeq]
        cases hDup : List.any sm.1.2.2.1 (fun x => decide (x.1.1 = u.val) && decide (x.1.2 = j.val))
        · simp only [Bool.false_eq_true, ↓reduceIte]
          cases hFind : List.find? (fun x => decide (x.1 = u.val)) sm.1.2.1
          · simp only [pure_bind]; rfl
          · cases hSig0 : decide (sigB = 0)
            · simp only [Bool.false_eq_true, ↓reduceIte, bind_assoc, pure_bind]
              refine bind_congr_support _ _ _ fun spkSkRaw _ => ?_
              refine bind_congr_support _ _ _ fun spkPkRaw _ => ?_
              refine bind_congr_support _ _ _ fun spkSig _ => ?_
              refine bind_congr_support _ _ _ fun seed _ => ?_
              refine bind_congr_support _ _ _ fun kp _ => ?_
              refine bind_congr_support _ _ _ fun pqSig _ => ?_
              rfl
            · simp only [↓reduceIte, pure_bind]; rfl
        · simp only [↓reduceIte, pure_bind]; rfl
  · intro p hp
    rw [map_eq_bind_pure_comp, mem_support_bind_iff] at hp
    obtain ⟨r, hr, hp⟩ := hp
    rw [Function.comp_apply, mem_support_pure_iff] at hp
    subst hp
    cases tp? with
    | none =>
      simp only [gdhKindGenSpkLeg, genSpk1KeyActiveGdhB, genSpkGdhActiveB, liftGdhComp,
        optNatMatchesE, _root_.SignalPqxdh.Security.ReductionDsl.KeyInd.eLet2,
        _root_.SignalPqxdh.Security.ReductionDsl.KeyInd.eLet,
        _root_.SignalPqxdh.Security.ReductionDsl.KeyInd.eCaseOpt,
        caseOptV, letV, bindV, eAny, eFind, smBase, stSpks, stPrin, paSpkIdx, paV,
        _root_.SignalPqxdh.Security.ReductionDsl.KeyInd.natEq,
        _root_.SignalPqxdh.Security.ReductionDsl.KeyInd.nat2Eq,
        l2a_eval_liftGdhComp_sBytes32, l2a_eval_liftGdhComp_sRandom64,
        l2a_eval_liftGdhComp_qX25519Base, l2a_eval_liftGdhComp_qKemKeyGen,
        l2a_eval_liftGdhComp_qSigSign, l2a_smUpd_base_eval,
        Comp.eval, Expr.eval, Env.get, v,
        _root_.SignalPqxdh.Security.ReductionDsl.KeyInd.Ext.wk,
        _root_.SignalPqxdh.Security.ReductionDsl.KeyInd.Ext.refl_wk',
        _root_.SignalPqxdh.Security.ReductionDsl.KeyInd.Ext.step_wk',
        Bool.false_eq_true, ↓reduceIte, pure_bind, hTakePrinK, hTakeSpksK] at hr
      cases hDup : List.any sm.1.2.2.1 (fun x => decide (x.1.1 = u.val) && decide (x.1.2 = j.val)) <;>
        simp only [hDup, Bool.false_eq_true, ↓reduceIte, pure_bind] at hr
      · cases hFind : List.find? (fun x => decide (x.1 = u.val)) sm.1.2.1 <;>
          simp only [hFind, bind_assoc, pure_bind] at hr
        · rw [mem_support_pure_iff] at hr; subst hr; exact hUnchanged _
        · simp only [mem_support_bind_iff, mem_support_pure_iff] at hr
          obtain ⟨spkSkRaw, _, spkPkRaw, _, rSpk, _, spkSig, _, seed, _, kp, _, rPq, _, pqSig, _, rfl⟩ := hr
          exact hGrown _ _ _
      · rw [mem_support_pure_iff] at hr; subst hr; exact hUnchanged _
    | some tp =>
      simp only [gdhKindGenSpkLeg, genSpk1KeyActiveGdhB, genSpkGdhActiveB, liftGdhComp,
        optNatMatchesE, _root_.SignalPqxdh.Security.ReductionDsl.KeyInd.eLet2,
        _root_.SignalPqxdh.Security.ReductionDsl.KeyInd.eLet,
        _root_.SignalPqxdh.Security.ReductionDsl.KeyInd.eCaseOpt,
        caseOptV, letV, bindV, eAny, eFind, smBase, stSpks, stPrin, paSpkIdx, paV,
        _root_.SignalPqxdh.Security.ReductionDsl.KeyInd.natEq,
        _root_.SignalPqxdh.Security.ReductionDsl.KeyInd.nat2Eq,
        l2a_eval_liftGdhComp_sBytes32, l2a_eval_liftGdhComp_sRandom64,
        l2a_eval_liftGdhComp_qX25519Base, l2a_eval_liftGdhComp_qKemKeyGen,
        l2a_eval_liftGdhComp_qSigSign, l2a_eval_sigChalQ_dsl,
        l2a_smUpd_base_eval,
        Comp.eval, Expr.eval, Env.get, v,
        _root_.SignalPqxdh.Security.ReductionDsl.KeyInd.Ext.wk,
        _root_.SignalPqxdh.Security.ReductionDsl.KeyInd.Ext.refl_wk',
        _root_.SignalPqxdh.Security.ReductionDsl.KeyInd.Ext.step_wk',
        pure_bind, hTakePrinK, hTakeSpksK] at hr
      cases hTp : decide (u.val = tp) <;>
        simp only [hTp, Bool.false_eq_true, ↓reduceIte] at hr
      · cases hDup : List.any sm.1.2.2.1 (fun x => decide (x.1.1 = u.val) && decide (x.1.2 = j.val)) <;>
          simp only [hDup, Bool.false_eq_true, ↓reduceIte, pure_bind] at hr
        · cases hFind : List.find? (fun x => decide (x.1 = u.val)) sm.1.2.1 <;>
            simp only [hFind, bind_assoc, pure_bind] at hr
          · rw [mem_support_pure_iff] at hr; subst hr; exact hUnchanged _
          · simp only [mem_support_bind_iff, mem_support_pure_iff] at hr
            obtain ⟨spkSkRaw, _, spkPkRaw, _, rSpk, _, spkSig, _, seed, _, kp, _, rPq, _, pqSig, _, rfl⟩ := hr
            exact hGrown _ _ _
        · rw [mem_support_pure_iff] at hr; subst hr; exact hUnchanged _
      · cases hDup : List.any sm.1.2.2.1 (fun x => decide (x.1.1 = u.val) && decide (x.1.2 = j.val)) <;>
          simp only [hDup, Bool.false_eq_true, ↓reduceIte] at hr
        · cases hFind : List.find? (fun x => decide (x.1 = u.val)) sm.1.2.1 <;>
            simp only [hFind] at hr
          · rw [mem_support_pure_iff] at hr; subst hr; exact hUnchanged _
          · cases hSig0 : decide (sigB = 0) <;>
              simp only [hSig0, Bool.false_eq_true, ↓reduceIte] at hr
            · simp only [mem_support_bind_iff, mem_support_pure_iff] at hr
              obtain ⟨spkSkRaw, _, spkPkRaw, _, spkSig, _, seed, _, kp, _, pqSig, _, rfl⟩ := hr
              exact hGrown _ _ _
            · rw [mem_support_pure_iff] at hr; subst hr; exact hUnchanged _
        · rw [mem_support_pure_iff] at hr; subst hr; exact hUnchanged _

theorem fgKeyInd1KeyGapDhKindAtomicProg_hStep_genOPK (S : Setup) (b : QueryBudget)
    (u : Fin S.N_id) (j : Fin S.N_recv) (o : Fin S.N_opk) :
    KeyIndStepSim S b (forgetGdh1KeyActiveK S b) (Gdh1KeyActiveSimInv S b)
      (gdh1KeyKindHandleC S b) (fgKeyInd1KeyGapDhActiveAtomicProg S b).handle (.genOPK u j o) := by
  intro c s' hB _hStepB hInv
  rcases s' with ⟨stAt, sh⟩
  have hStAt : stAt = embedVal gdh1KeyActiveStateTy (projVal gdh1KeyActiveStateTy stAt) :=
    (AtomicLift.embedVal_projVal gdh1KeyActiveStateTy stAt).symm
  rw [hStAt] at hInv ⊢
  generalize projVal gdh1KeyActiveStateTy stAt = stL at hInv ⊢
  rcases stL with ⟨⟨⟨pa, sm⟩, sigB⟩, ⟨tp?, cnt⟩⟩
  have hSim : GdhSimInv S b c (embedVal simTy sm, sh) := hInv.sim_inv
  have hCnt : cnt ≤ c 0 := hInv.sendOpkCnt_le
  have hBase : BaseOnlineLenInv c sm.1 := baseOnlineLenInv_of_gdhSimInv hSim
  let f := keyIndKFuelsOfBudget S b
  have hc0 : c 0 ≤ f.kOn := hB 0
  have hFkLe : f.kOn ≤ b.q_total := kOn_le_q_total S b
  have hOpksLen : (stOpksList sm.1).length ≤ f.kOn := Nat.le_trans hBase.opks_le hc0
  have hLHS :
      (gdh1KeyKindHandleC S b).eval
        (.cons (embedVal gdh1KeyActiveStateTy (((pa, sm), sigB), (tp?, cnt)), sh)
          (.cons ((pqKeyIndCodec S).qenc (.genOPK u j o)) .nil)) =
      (fun r => (embedVal keyIndRespTy r.1, (embedVal gdh1KeyActiveStateTy r.2, sh))) <$>
        (gdhKindGenOpkLeg f.kOn).eval
          (.cons (((pa, sm), sigB), (tp?, cnt)) (.cons (u.val, (j.val, o.val)) .nil)) := by
    unfold gdh1KeyKindHandleC
    rw [dispatchKeyIndQ_eval]
    refine l2a_liftSigDdhNoFgArm_eval S _ (gdhKindGenOpkLeg f.kOn)
      (genOpkActiveGdhB_unsupported f.kOn .zero (.succ .zero))
      _ (((pa, sm), sigB), (tp?, cnt)) sh
      ((pqKeyIndCodec S).qenc (.genOPK u j o)) (u.val, (j.val, o.val)) ?_
    rfl
  rw [hLHS]
  rcases pa with ⟨u0, v0, up0, prinFlag, prinIdx, dhFlag, ephIdx, spkIdx, opkMode, opkIdx, mode⟩
  have hTakeK : List.take f.kOn sm.1.2.2.2.1 = sm.1.2.2.2.1 := List.take_of_length_le hOpksLen
  have hTakeB : List.take b.q_total sm.1.2.2.2.1 = sm.1.2.2.2.1 :=
    List.take_of_length_le (Nat.le_trans hOpksLen hFkLe)
  have hBeq : decide (sm.1.2.2.2.1.length = opkIdx) = decide (sm.1.2.2.2.1.length = fixSent S b opkIdx) :=
    l2a_decide_eq_fixSent_of_le_mOn hOpksLen
  have hBump0 : bumpPred (keyIndSimPred S) c (.genOPK u j o) 0 = c 0 + 1 := bumpPred_online_0 rfl
  constructor
  · rw [l2a_forgetGdh1KeyActiveK_embed]
    change _ = (liftKeyIndHandle tlSigDdhKeyInd S (gdh1KeyActiveHandle S b.q_total)).eval _
    rw [l2a_liftKeyIndHandle_eval_mapComp tlSigDdhKeyInd S (gdh1KeyActiveHandle S b.q_total)
      (l2a_fixGdh1KeyActiveSentLeg S b
        ((((u0, v0, up0, prinFlag, prinIdx, dhFlag, ephIdx, spkIdx, opkMode, opkIdx, mode), sm),
          sigB), tp?, cnt))
      (.genOPK u j o)]
    unfold gdh1KeyActiveHandle caseSumV
    rw [l2a_mapComp_caseSum_inr tlSigDdhKeyInd _ _ _ _ _ rfl]
    rw [l2a_mapComp_caseSum_inr tlSigDdhKeyInd _ _ _ _ _ rfl]
    rw [l2a_mapComp_caseSum_inr tlSigDdhKeyInd _ _ _ _ _ rfl]
    rw [l2a_mapComp_caseSum_inl tlSigDdhKeyInd _ _ _ _ _ rfl]
    rw [mapComp_eval tlSigDdhKeyInd _ (genOpkActiveGdhB_unsupported b.q_total _ _)]
    simp only [gdhKindGenOpkLeg, genOpkActiveGdhB,
      l2a_fixGdh1KeyActiveSentLeg, l2a_fixParamsSentLeg,
      letV, bindV, eAny, smBase, stOpks, paOpkMode, paOpkIdx, paV,
      _root_.SignalPqxdh.Security.ReductionDsl.KeyInd.natEq,
      _root_.SignalPqxdh.Security.ReductionDsl.KeyInd.nat2Eq,
      _root_.SignalPqxdh.Security.ReductionDsl.KeyInd.nat3Eq,
      l2a_eval_liftGdhComp_sBytes32, l2a_eval_liftGdhComp_qX25519Base,
      Comp.eval, Expr.eval, Env.get, v,
      _root_.SignalPqxdh.Security.ReductionDsl.KeyInd.Ext.wk,
      _root_.SignalPqxdh.Security.ReductionDsl.KeyInd.Ext.refl_wk',
      _root_.SignalPqxdh.Security.ReductionDsl.KeyInd.Ext.step_wk',
      hTakeK, hTakeB,
      map_eq_bind_pure_comp, Function.comp_def, bind_assoc, pure_bind]
    rw [hBeq]
    cases hDup : List.any sm.1.2.2.2.1
        (fun x => decide (x.1.1 = u.val) && (decide (x.1.2.1 = j.val) && decide (x.1.2.2 = o.val)))
    · simp only [Bool.false_eq_true, ↓reduceIte, bind_assoc, pure_bind]
      refine bind_congr_support _ _ _ fun opkSkRaw _ => ?_
      refine bind_congr_support _ _ _ fun opkPkRaw _ => ?_
      rfl
    · simp only [↓reduceIte, pure_bind]
      rfl
  · intro p hp
    rw [map_eq_bind_pure_comp, mem_support_bind_iff] at hp
    obtain ⟨r, hr, hp⟩ := hp
    rw [Function.comp_apply, mem_support_pure_iff] at hp
    subst hp
    simp only [gdhKindGenOpkLeg, genOpkActiveGdhB, letV, bindV, eAny, smBase, stOpks,
      _root_.SignalPqxdh.Security.ReductionDsl.KeyInd.natEq,
      _root_.SignalPqxdh.Security.ReductionDsl.KeyInd.nat2Eq,
      _root_.SignalPqxdh.Security.ReductionDsl.KeyInd.nat3Eq,
      l2a_eval_liftGdhComp_sBytes32, l2a_eval_liftGdhComp_qX25519Base,
      l2a_smUpd_base_eval,
      Comp.eval, Expr.eval, Env.get, v,
      _root_.SignalPqxdh.Security.ReductionDsl.KeyInd.Ext.wk,
      _root_.SignalPqxdh.Security.ReductionDsl.KeyInd.Ext.refl_wk',
      _root_.SignalPqxdh.Security.ReductionDsl.KeyInd.Ext.step_wk',
      pure_bind, hTakeK] at hr
    cases hDup : List.any sm.1.2.2.2.1
        (fun x => decide (x.1.1 = u.val) && (decide (x.1.2.1 = j.val) && decide (x.1.2.2 = o.val))) <;>
      simp only [hDup, Bool.false_eq_true, ↓reduceIte] at hr
    · simp only [mem_support_bind_iff, mem_support_pure_iff] at hr
      obtain ⟨opkSkRaw, _, opkPkRaw, _, rfl⟩ := hr
      apply l2a_Gdh1KeyActiveSimInv_of_embed
      · apply GdhSimInv.upd_online_base_pows (t := .genOPK u j o) hSim rfl
        · exact BaseOnlineLenInv.upd_online hBase rfl (Nat.le_succ _) (Nat.le_succ _) (Nat.le_refl _)
            le_rfl le_rfl le_rfl le_rfl le_rfl (Nat.le_succ _)
        · rfl
        · rfl
        · rfl
        · exact Nat.le_succ _
      · rw [hBump0]; exact Nat.le_trans hCnt (Nat.le_succ _)
    · rw [mem_support_pure_iff] at hr; subst hr
      apply l2a_Gdh1KeyActiveSimInv_of_embed (gdhSimInv_unchanged_online hSim rfl)
      rw [hBump0]; exact Nat.le_trans hCnt (Nat.le_succ _)

theorem fgKeyInd1KeyGapDhKindAtomicProg_hStep_registerKey (S : Setup) (b : QueryBudget)
    (sk : Bytes) :
    KeyIndStepSim S b (forgetGdh1KeyActiveK S b) (Gdh1KeyActiveSimInv S b)
      (gdh1KeyKindHandleC S b) (fgKeyInd1KeyGapDhActiveAtomicProg S b).handle (.registerKey sk) := by
  intro c ⟨stA, sh⟩ _ _ hInv
  set stL := projVal gdh1KeyActiveStateTy stA
  have hStA : stA = embedVal gdh1KeyActiveStateTy stL :=
    (AtomicLift.embedVal_projVal gdh1KeyActiveStateTy stA).symm
  rw [hStA] at hInv ⊢
  unfold gdh1KeyKindHandleC; dsimp only; rw [dispatchKeyIndQ_eval]; dsimp only
  rw [icAtom_liftNoFg_eval S _ icAtom_gdhRegKey_unsup sk stL sh _]
  have hFg : forgetGdh1KeyActiveK S b (embedVal gdh1KeyActiveStateTy stL, sh) =
      embedVal gdh1KeyActiveStateTy (icAtom_fixGdhLeg S b stL) := by
    rcases stL with ⟨⟨⟨⟨u, vPk, up, pf, pi, df, ei, si, om, oi, md⟩, sm⟩, sigB⟩, rp?, cnt⟩
    rfl
  have hRhs : (fgKeyInd1KeyGapDhActiveAtomicProg S b).handle.eval
      (.cons (forgetGdh1KeyActiveK S b (embedVal gdh1KeyActiveStateTy stL, sh))
        (.cons ((pqKeyIndCodec S).qenc (.registerKey sk)) .nil)) =
      embedVal (.prod keyIndRespTy gdh1KeyActiveStateTy) <$>
        (gdh1KeyActiveHandle S b.q_total).eval
          (.cons (icAtom_fixGdhLeg S b stL)
            (.cons ((_root_.SignalPqxdh.LegacyCosted.keyIndCodec S).qenc (.registerKey sk)) .nil)) := by
    rw [hFg]; exact liftKeyIndHandle_eval tlSigDdhKeyInd S (gdh1KeyActiveHandle S b.q_total)
      (icAtom_gdhActiveHandle_unsup S b.q_total) (icAtom_fixGdhLeg S b stL) (.registerKey sk)
  rcases stL with ⟨⟨⟨pa, sm⟩, sigB⟩, rp?, cnt⟩
  set cReg := (registerGdhB (.zero : Var [simTy, keyIndStateTy, B 32] simTy)
    (.succ .zero : Var [simTy, keyIndStateTy, B 32] keyIndStateTy)
    (.succ (.succ .zero) : Var [simTy, keyIndStateTy, B 32] (B 32))).eval
    (.cons sm (.cons sm.1 (.cons (t := B 32) sk .nil)))
  have hL : (gdhWrapDelegNoFgLeg fun pa2 sm bSt sk => wrapSim2 pa2 (registerGdhB sm bSt sk)).eval
      (.cons (((pa, sm), sigB), rp?, cnt) (.cons (t := B 32) sk .nil)) =
      (fun r0 => (r0.1, (((pa, r0.2), sigB), rp?, cnt))) <$>
        _root_.SignalPqxdh.Security.FgGapDh1Key.liftGdhToSign cReg := by
    simp only [gdhWrapDelegNoFgLeg, wrapSim2, smBase, liftGdhComp_eval,
      letV, bindV, Comp.eval, Expr.eval, v, Ext.wk, Env.get, pure_bind]
    rw [icAtom_registerGdhB_eval_eq]
    simp only [liftGdhToSign_bind, liftGdhToSign_pure, map_eq_bind_pure_comp,
      Function.comp_def, bind_assoc, pure_bind, Expr.eval, v, Ext.wk, Env.get]
    rfl
  have hR : (gdh1KeyActiveHandle S b.q_total).eval
      (.cons (icAtom_fixGdhLeg S b (((pa, sm), sigB), rp?, cnt))
        (.cons ((_root_.SignalPqxdh.LegacyCosted.keyIndCodec S).qenc (.registerKey sk)) .nil)) =
      (fun r0 => (r0.1, icAtom_fixGdhLeg S b (((pa, r0.2), sigB), rp?, cnt))) <$>
        _root_.SignalPqxdh.Security.FgGapDh1Key.liftGdhToSign cReg := by
    simp only [gdh1KeyActiveHandle, callGdhActiveHandle, icAtom_fixGdhLeg,
      _root_.SignalPqxdh.LegacyCosted.keyIndCodec, _root_.SignalPqxdh.LegacyCosted.keyIndQenc,
      renameComp_eval, pullEnv_twoVarRen, liftGdhComp_eval, gdhHandle2, wrapSim2, smBase,
      letV, bindV, caseSumV, Comp.eval, Expr.eval, v, Ext.wk, Env.get, pure_bind]
    rw [icAtom_registerGdhB_eval_eq]
    simp only [liftGdhToSign_bind, liftGdhToSign_pure, map_eq_bind_pure_comp,
      Function.comp_def, bind_assoc, pure_bind, Expr.eval, v, Ext.wk, Env.get]
    rfl
  rw [hL]
  refine ⟨?_, ?_⟩
  · simp only [hRhs, hR, Functor.map_map]
    refine congrArg (fun f => f <$> _root_.SignalPqxdh.Security.FgGapDh1Key.liftGdhToSign cReg)
      (funext fun r0 => ?_)
    rcases pa with ⟨u, vPk, up, pf, pi, df, ei, si, om, oi, md⟩
    rfl
  · intro p hp
    rw [Functor.map_map] at hp
    simp only [map_eq_bind_pure_comp, Function.comp_def,
      mem_support_bind_iff, mem_support_pure_iff] at hp
    rcases hp with ⟨r0, hr0, rfl⟩
    exact
      { sim_inv := registerGdhB_inv (S := S) (b := b) (c := c) (t := .registerKey sk)
          (smVal := sm) (sh := sh)
          (.zero : Var [simTy, keyIndStateTy, B 32] simTy)
          (.succ .zero : Var [simTy, keyIndStateTy, B 32] keyIndStateTy)
          (.succ (.succ .zero) : Var [simTy, keyIndStateTy, B 32] (B 32))
          (.cons sm (.cons sm.1 (.cons (t := B 32) sk .nil)))
          rfl rfl hInv.sim_inv rfl (mem_support_liftGdhToSign hr0)
        sendOpkCnt_le := by
          rw [bumpPred_online_0 (S := S) rfl]
          exact Nat.le_succ_of_le hInv.sendOpkCnt_le }

end Arms

end

end Computational.Proofs.SignalPqxdh.Security.ReductionDsl.KindSplit.KeyIndGapDhKSimMiscArms
