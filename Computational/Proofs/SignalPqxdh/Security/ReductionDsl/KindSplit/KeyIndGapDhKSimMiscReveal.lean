/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Computational.Specifications.Pqxdh.Security.Headline
public import Computational.Specifications.Pqxdh.Security.CostedBudgets
public import Computational.Proofs.SignalPqxdh.Delta.KeyInd1KeyActiveProgs -- proof-setup: allow-public-import
public import Computational.Proofs.SignalPqxdh.Delta.KindSplit.KeyInd1KeyKindProgs -- proof-setup: allow-public-import
public import Computational.Proofs.SignalPqxdh.Security.ReductionDsl.KindSplit.KeyIndGapDhKSimBase -- proof-setup: allow-public-import
import Computational.Proofs.ReductionDsl.StepSim
import Computational.Proofs.SignalPqxdh.AtomicLift
import Computational.Proofs.SignalPqxdh.Security.ReductionDsl.KeyIndGapDh
import Computational.Proofs.SignalPqxdh.Security.ReductionDsl.KeyInd1KeySigEval
import Computational.Proofs.SignalPqxdh.Security.ReductionDsl.KeyInd1KeyGapDh
import Computational.Proofs.SignalPqxdh.Security.ReductionDsl.KeyInd1KeyGapDhEvalEq
import Computational.Proofs.SignalPqxdh.Security.ReductionDsl.KindSplit.KeyIndCoreK
import Computational.Proofs.SignalPqxdh.Security.ReductionDsl.KindSplit.KeyIndCoreKSimBase
import Computational.Proofs.SignalPqxdh.Security.ReductionDsl.KindSplit.KeyIndGapDhK

/-!
# Reveal, Corrupt, and Test Step Simulation for Shadow-Indexed `KeyInd` Gap-DH

Proves the `KeyIndStepSim` obligations for `.corruptIK`, `.testSession`, `.revealDhSecrets`,
`.revealSessionKey`, and `.revealSpkSk` across `sigKeyInd1KeyKindAtomicProg` and
`fgKeyInd1KeyGapDhKindAtomicProg`.
-/

namespace Computational.Proofs.SignalPqxdh.Security.ReductionDsl.KindSplit.KeyIndGapDhKSimMiscReveal

set_option autoImplicit false

public section

open OracleSpec OracleComp
open _root_.ReductionDsl (Sig Ty Var Expr Comp Env Iface pqAtomicSig pqAtomicOps pqKeyIndCodec)
open _root_.SignalPqxdh (Bytes Setup QueryBudget KeyIndQuery)
open _root_.SignalPqxdh.Security (keyIndQueryKind)
open _root_.SignalPqxdh.LegacyCosted (
  pqSig pqxdhOps pqPrimIface pqGapDhIface pqSigAndDdhIface B sidT keyIndCodec
)
open Computational.Proofs.ReductionDsl.StepSim (bumpPred)
open Computational.Proofs.SignalPqxdh.AtomicLift (
  aop embedTy embedVal projVal projVal_embedVal embedVal_projVal embedEnv
  compRename compRename_eval mapComp mapComp_eval
  finSidToNatExpr tlPrimKeyInd tlGapDhKeyInd tlSigDdhKeyInd
  keyIndUnsupportedPrimW liftKeyIndHandle liftKeyIndHandle_eval liftKeyInd1Stage
)
open _root_.SignalPqxdh.Security.ReductionDsl.KeyInd (
  PT Ext v letV bindV caseOptV caseSumV findMV anyMV eLet eLet2 eFind eAny eMap eCaseOpt
  letV_eval Ext.refl_wk' Ext.step_wk' Env.get_zero' Env.get_succ'
  keyIndQueryTy keyIndRespTy keyIndStateTy simTy paramsTy params2Ty gdhState2Ty
  sig1KeyStTy sessionIdToVal rNone rCorr rDrKey rSpkSk rs
  stSecb stUpd stPrin stSpks stOpks stSess stResps freshE
  peSecIKA0 peSecIKAsign peUpd sbSpkSk sbUpd
  seSid seFresh seTested seRevealed seDrReal seDrRand seUpd
  reSid reSenderHonest reTested reRevealed reDrReal reDrRand reUpd
  natEq nat2Eq corruptB testB revealB revealSpkB
  sBytes32 sRandom64 sDrKey96 qX25519 qX25519Base qPow8 qIsCanonical
  qSigPkGen qSigSign qSigVerify qKemKeyGen qKemEncaps qKemDecaps qSigDdhSign
  gPrim s1Prim chooseInitRandC chooseRespRandC lookupSpkSkC computePosC mkPairPosC
  fgPatchC findHonestC honestPeerC checkProvC koskBundleOkPowsC koskSenderOkPowsC
  computeOptPosInitC mkSecretPosC isGameSpkC isGameOpkC resolveSigPkC partnerC
  smBase smFgL smRaw smLog smPows smMk smUpd pa2Mk paU paV paUp paOpkMode
  wrapBase2 wrapSim2 gdhHandle2
  initPrinGdh2B genSpkGdh2B genOpkGdh2B initiateGdh2B acceptOpkGdh2B
  acceptNoOpkGdhB finishAcceptGdhC roParsedC roRawFallbackC registerGdhB
  s1Mk s1Target s1Budget s1Forgery s1Fg s1Pk s1Upd sig1KeyTargetGenSpkB
  liftGdhToSigDdh liftGdhToSigDdh_eval renamePair litB isSomeE
)
open _root_.SignalPqxdh.Security.ReductionDsl.KeyInd1KeyGapDh (
  gdh1KeyStateTy liftGdhComp liftGdhComp_eval liftGdhToSign_pure
  twoVarRen pullEnv_twoVarRen renameComp renameComp_eval
)
open Computational.Proofs.SignalPqxdh.Delta.KeyInd1KeyActiveProgs (
  sig1KeyActiveStTy S1ARS saTP saInner extract1KeyActiveC
  sig1KeyActiveInitPrinB sig1KeyActiveInitiateCheckC sig1KeyActivePreDispatchC
  sig1KeyActiveHandleC sigKeyInd1KeyActiveDslProg sigKeyInd1KeyActiveAtomicProg
  gdh1KeyActiveStateTy callGdhActiveHandle
  initPrin1KeyActiveGdhB genSpk1KeyActiveGdhB genSpkGdhActiveB genOpkActiveGdhB
  initiateActiveGdhB initiateGdhActiveInnerB gdh1KeyActiveHandle
  fgKeyInd1KeyGapDhActiveDslProg fgKeyInd1KeyGapDhActiveAtomicProg
)
open Computational.Proofs.SignalPqxdh.Delta.KindSplit.KeyInd1KeyKindProgs (
  liftSigDdhNoFgArm sigWrapGdh2NoFgLeg gdhWrapDelegNoFgLeg
  sig1KeyKindHandleC gdh1KeyKindHandleC
)
open Computational.Proofs.SignalPqxdh.Security.ReductionDsl.KindSplit.KeyIndCoreK (
  dispatchKeyIndQ runAt2 atomicRNoneE finPairToNatE
)
open Computational.Proofs.SignalPqxdh.Security.ReductionDsl.KindSplit.KeyIndCoreKSimBase (
  fixSent keyIndSimPred keyIndSimBounds keyIndSimPred_zero_iff_kind keyIndSimPred_one_iff_kind
  stPrinList stSpksList stOpksList stSessList stRespsList
  stUsedOList stUsedNList stKybList stAdvList
  BaseOnlineLenInv dispatchKeyIndQ_eval runAt2_eval
  corruptB_min_eq testB_min_eq revealB_min_eq revealSpkB_min_eq
)
open Computational.Proofs.SignalPqxdh.Security.ReductionDsl.KindSplit.KeyIndGapDhK (
  keyIndKFuelsOfBudget fgShadowAtomicTy simShadowAtomicTy
)
open Computational.Proofs.SignalPqxdh.Security.ReductionDsl.KindSplit.KeyIndGapDhKSimBase (
  KeyIndStepSim
  ddhEqC_unsupported_zero ddhEqOptC_unsupported_zero entryMatchesC_unsupported_zero
  fixParamsSent fixSig1KeyActiveSent forgetSig1KeyActiveK Sig1KeyActiveSimInv
  fixGdh1KeyActiveSent forgetGdh1KeyActiveK Gdh1KeyActiveSimInv GdhSimInv
)

section Helpers

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
  sigKeyInd1KeyActiveAtomicProg
  fgKeyInd1KeyGapDhActiveAtomicProg
  sigKeyInd1KeyActiveDslProg
  fgKeyInd1KeyGapDhActiveDslProg
  _root_.ReductionDsl.CostedReduction.σ
  Env.get

private theorem bumpPred_online_0 {S : Setup} {c : Fin 3 → ℕ} {t : KeyIndQuery S}
    (hOn : keyIndQueryKind t = 0) :
    bumpPred (keyIndSimPred S) c t 0 = c 0 + 1 := by
  have hP : keyIndSimPred S 0 t := (keyIndSimPred_zero_iff_kind t).mpr hOn
  simp [bumpPred, hP]

private theorem bumpPred_online_1 {S : Setup} {c : Fin 3 → ℕ} {t : KeyIndQuery S}
    (hOn : keyIndQueryKind t = 0) :
    bumpPred (keyIndSimPred S) c t 1 = c 1 := by
  have hNot : ¬ keyIndSimPred S 1 t := by
    rw [keyIndSimPred_one_iff_kind]; rw [hOn]; decide
  simp [bumpPred, hNot]

private theorem bumpPred_online_2 {S : Setup} {c : Fin 3 → ℕ} {t : KeyIndQuery S}
    (_hOn : keyIndQueryKind t = 0) :
    bumpPred (keyIndSimPred S) c t 2 = c 2 + 1 := by
  have hP : keyIndSimPred S 2 t := trivial
  simp [bumpPred, hP]

private def BaseOnlineNonInc (bSt bSt' : keyIndStateTy.denote) : Prop :=
  (stPrinList bSt').length ≤ (stPrinList bSt).length ∧
  (stSpksList bSt').length ≤ (stSpksList bSt).length ∧
  (stOpksList bSt').length ≤ (stOpksList bSt).length ∧
  (stSessList bSt').length ≤ (stSessList bSt).length ∧
  (stRespsList bSt').length ≤ (stRespsList bSt).length ∧
  (stUsedOList bSt').length ≤ (stUsedOList bSt).length ∧
  (stUsedNList bSt').length ≤ (stUsedNList bSt).length ∧
  (stKybList bSt').length ≤ (stKybList bSt).length ∧
  (stAdvList bSt').length ≤ (stAdvList bSt).length

private theorem BaseOnlineNonInc.refl (bSt : keyIndStateTy.denote) :
    BaseOnlineNonInc bSt bSt :=
  ⟨le_rfl, le_rfl, le_rfl, le_rfl, le_rfl, le_rfl, le_rfl, le_rfl, le_rfl⟩

private theorem BaseOnlineLenInv.upd_noninc {S : Setup} {c : Fin 3 → ℕ} {t : KeyIndQuery S}
    {bSt bSt' : keyIndStateTy.denote}
    (hInv : BaseOnlineLenInv c bSt) (hOn : keyIndQueryKind t = 0)
    (hNI : BaseOnlineNonInc bSt bSt') :
    BaseOnlineLenInv (bumpPred (keyIndSimPred S) c t) bSt' := by
  have h0 := bumpPred_online_0 (c := c) hOn
  have h1 := bumpPred_online_1 (c := c) hOn
  have h2 := bumpPred_online_2 (c := c) hOn
  rcases hNI with ⟨h1', h2', h3', h4', h5', h6', h7', h8', h9'⟩
  have hP := hInv.prin_le; have hSp := hInv.spks_le; have hOp := hInv.opks_le
  have hSe := hInv.sess_le; have hRe := hInv.resps_le
  have hUO := hInv.usedO_le; have hUN := hInv.usedN_le
  have hKy := hInv.kyb_le; have hAd := hInv.adv_le; have hCnt := hInv.counts_eq
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> omega

private theorem GdhSimInv.upd_online_base_only {S : Setup} {b : QueryBudget}
    {c : Fin 3 → ℕ} {t : KeyIndQuery S}
    {sm : simTy.denote} {bSt' : keyIndStateTy.denote} {sh : fgShadowAtomicTy.denote}
    (hInv : GdhSimInv S b c (embedVal simTy sm, sh))
    (hOn : keyIndQueryKind t = 0)
    (hNI : BaseOnlineNonInc sm.1 bSt') :
    GdhSimInv S b (bumpPred (keyIndSimPred S) c t) (embedVal simTy (bSt', sm.2), sh) := by
  have h0 := bumpPred_online_0 (c := c) hOn
  have h1 := bumpPred_online_1 (c := c) hOn
  have hProjOld : projVal keyIndStateTy (embedVal simTy sm).1 = sm.1 :=
    congrArg Prod.fst (projVal_embedVal simTy sm)
  have hProjNew : projVal keyIndStateTy (embedVal simTy (bSt', sm.2)).1 = bSt' :=
    congrArg Prod.fst (projVal_embedVal simTy (bSt', sm.2))
  have hBaseOld : BaseOnlineLenInv c sm.1 := hProjOld ▸ hInv.online_len
  have hBaseNew : BaseOnlineLenInv (bumpPred (keyIndSimPred S) c t) bSt' :=
    BaseOnlineLenInv.upd_noninc hBaseOld hOn hNI
  refine
    { online_len := by simpa [hProjNew] using hBaseNew
      fg_sess_le := Nat.le_trans hInv.fg_sess_le (by omega)
      fg_shadow  := ?_
      raw_len    := h1 ▸ hInv.raw_len
      raw_shadow := hInv.raw_shadow
      log_len    := h1 ▸ hInv.log_len
      pows_len   := Nat.le_trans hInv.pows_len (by omega) }
  obtain ⟨tagged, hRel, hWf, hRoLe⟩ := hInv.fg_shadow
  exact ⟨tagged, hRel, hWf, h1 ▸ hRoLe⟩

private theorem eMap_length_le {Γ : List PT} {α β : PT} (K : ℕ)
    {l : Expr pqxdhOps Γ (.list α)}
    {f : Var (α :: Γ) α → Expr pqxdhOps (α :: Γ) β} (env : Env Γ) :
    ((eMap K l f).eval env).length ≤ (l.eval env).length := by
  simp only [eMap, Expr.eval, List.length_map, List.length_take]
  exact Nat.min_le_right _ _

private theorem corruptB_eval_pure {K : ℕ} {Γ₁ Γ₂ Δ : List PT} [Ext Γ₁ Δ] [Ext Γ₂ Δ]
    (bSt : Var Γ₁ keyIndStateTy) (u : Var Γ₂ .nat) (env : Env Δ) :
    ∃ r bSt', (corruptB K bSt u).eval env = pure (r, bSt') ∧
      BaseOnlineNonInc ((v bSt).eval env) bSt' := by
  simp only [corruptB, caseOptV, Comp.eval]
  cases (eFind K (stPrin (v bSt)) _).eval env with
  | none => exact ⟨_, _, rfl, BaseOnlineNonInc.refl _⟩
  | some pe =>
    dsimp only [rs, stUpd, Expr.eval]
    refine ⟨_, _, rfl, ?_, le_rfl, le_rfl, le_rfl, le_rfl, le_rfl, le_rfl, le_rfl, le_rfl⟩
    dsimp only [stPrin, stPrinList, Expr.eval, v, Ext.wk, Env.get]
    exact eMap_length_le K (.cons pe env)

private theorem testB_eval_pure {K : ℕ} {Γ₁ Γ₂ Δ : List PT} [Ext Γ₁ Δ] [Ext Γ₂ Δ]
    (bSt : Var Γ₁ keyIndStateTy) (sid : Var Γ₂ sidT) (env : Env Δ) :
    ∃ r bSt', (testB K bSt sid).eval env = pure (r, bSt') ∧
      BaseOnlineNonInc ((v bSt).eval env) bSt' := by
  simp only [testB, caseOptV, Comp.eval]
  split_ifs
  · exact ⟨_, _, rfl, BaseOnlineNonInc.refl _⟩
  · cases (eFind K (stSess (v bSt)) _).eval env with
    | none =>
      dsimp only
      cases (eFind K (stResps (v bSt)) _).eval env with
      | none => exact ⟨_, _, rfl, BaseOnlineNonInc.refl _⟩
      | some re =>
        dsimp only [rs, stUpd, Expr.eval]
        refine ⟨_, _, rfl, le_rfl, le_rfl, le_rfl, le_rfl, ?_, le_rfl, le_rfl, le_rfl, le_rfl⟩
        dsimp only [stResps, stRespsList, Expr.eval, v, Ext.wk, Env.get]
        exact eMap_length_le K (.cons re env)
    | some se =>
      dsimp only [rs, stUpd, Expr.eval]
      refine ⟨_, _, rfl, le_rfl, le_rfl, le_rfl, ?_, le_rfl, le_rfl, le_rfl, le_rfl, le_rfl⟩
      dsimp only [stSess, stSessList, Expr.eval, v, Ext.wk, Env.get]
      exact eMap_length_le K (.cons se env)

private theorem revealB_eval_pure {K : ℕ} {Γ₁ Γ₂ Δ : List PT} [Ext Γ₁ Δ] [Ext Γ₂ Δ]
    (bSt : Var Γ₁ keyIndStateTy) (sid : Var Γ₂ sidT) (env : Env Δ) :
    ∃ r bSt', (revealB K bSt sid).eval env = pure (r, bSt') ∧
      BaseOnlineNonInc ((v bSt).eval env) bSt' := by
  simp only [revealB, caseOptV, Comp.eval]
  cases (eFind K (stSess (v bSt)) _).eval env with
  | none =>
    dsimp only
    cases (eFind K (stResps (v bSt)) _).eval env with
    | none => exact ⟨_, _, rfl, BaseOnlineNonInc.refl _⟩
    | some re =>
      dsimp only
      split_ifs
      · exact ⟨_, _, rfl, BaseOnlineNonInc.refl _⟩
      · dsimp only [rs, stUpd, Expr.eval]
        refine ⟨_, _, rfl, le_rfl, le_rfl, le_rfl, le_rfl, ?_, le_rfl, le_rfl, le_rfl, le_rfl⟩
        dsimp only [stResps, stRespsList, Expr.eval, v, Ext.wk, Env.get]
        exact eMap_length_le K (.cons re env)
  | some se =>
    dsimp only
    split_ifs
    · exact ⟨_, _, rfl, BaseOnlineNonInc.refl _⟩
    · dsimp only [rs, stUpd, Expr.eval]
      refine ⟨_, _, rfl, le_rfl, le_rfl, le_rfl, ?_, le_rfl, le_rfl, le_rfl, le_rfl, le_rfl⟩
      dsimp only [stSess, stSessList, Expr.eval, v, Ext.wk, Env.get]
      exact eMap_length_le K (.cons se env)

private theorem revealSpkB_eval_pure {K : ℕ} {Γ₁ Γ₂ Δ : List PT} [Ext Γ₁ Δ] [Ext Γ₂ Δ]
    (bSt : Var Γ₁ keyIndStateTy) (x : Var Γ₂ (.prod .nat .nat)) (env : Env Δ) :
    ∃ r bSt', (revealSpkB K bSt x).eval env = pure (r, bSt') ∧
      BaseOnlineNonInc ((v bSt).eval env) bSt' := by
  simp only [revealSpkB, caseOptV, Comp.eval]
  cases (eFind K (stSpks (v bSt)) _).eval env with
  | none => exact ⟨_, _, rfl, BaseOnlineNonInc.refl _⟩
  | some sb =>
    dsimp only [rs, stUpd, Expr.eval]
    refine ⟨_, _, rfl, le_rfl, ?_, le_rfl, le_rfl, le_rfl, le_rfl, le_rfl, le_rfl, le_rfl⟩
    dsimp only [stSpks, stSpksList, Expr.eval, v, Ext.wk, Env.get]
    exact eMap_length_le K (.cons sb env)

@[local simp] private theorem liftGdhToSigDdh_unsupported {Γ : List PT} {t : PT}
    (c : Comp pqxdhOps pqGapDhIface Γ t) :
    (liftGdhToSigDdh c).queries tlSigDdhKeyInd.unsupportedW (fun _ => 0) =
      c.queries tlGapDhKeyInd.unsupportedW (fun _ => 0) := by
  induction c with
  | query g _ => rcases g with _ | ⟨⟩ <;> rfl
  | sample _ _ => rfl
  | _ => simp_all [liftGdhToSigDdh, Comp.queries]

@[local simp] private theorem liftGdhComp_unsupported {Γ : List PT} {t : PT}
    (c : Comp pqxdhOps pqGapDhIface Γ t) :
    (liftGdhComp c).queries tlSigDdhKeyInd.unsupportedW (fun _ => 0) =
      c.queries tlGapDhKeyInd.unsupportedW (fun _ => 0) := by
  induction c with
  | query g _ => rcases g with _ | ⟨⟩ <;> rfl
  | sample _ _ => rfl
  | _ => simp_all [liftGdhComp, Comp.queries]

@[local simp] private theorem renameComp_queries_loc {ι : Type} {T : OracleSpec ι}
    {I : Iface pqSig T} (w : I.Tag → ℕ) (ws : I.smp.Samp → ℕ) :
    ∀ {Γ Δ : List PT} {t : PT}
      (ρ : _root_.SignalPqxdh.Security.ReductionDsl.KeyInd1KeyGapDh.Ren Γ Δ)
      (c : Comp pqxdhOps I Γ t),
      (renameComp ρ c).queries w ws = c.queries w ws := by
  intro Γ Δ t ρ c
  induction c generalizing Δ <;> simp_all [renameComp, Comp.queries]

@[local simp] private theorem liftBase_queries_loc
    {C : _root_.SignalPqxdh.LegacyCosted.ChallengerOracle}
    (w : (_root_.SignalPqxdh.LegacyCosted.pqChalIface C).Tag → ℕ)
    (ws : (_root_.SignalPqxdh.LegacyCosted.pqChalIface C).smp.Samp → ℕ)
    {Γ : List PT} {τ : PT} (c : Comp pqxdhOps pqPrimIface Γ τ) :
    (_root_.SignalPqxdh.Security.ReductionDsl.KeyInd.liftBase (C := C) c).queries w ws =
      Comp.queries (I := pqPrimIface) (fun g => w (.inl g)) (fun s => ws s) c := by
  induction c <;> simp_all [_root_.SignalPqxdh.Security.ReductionDsl.KeyInd.liftBase, Comp.queries]

@[local simp] private theorem comp_rename_queries_loc {ι : Type} {T : OracleSpec ι}
    {I : Iface pqSig T} (w : I.Tag → ℕ) (ws : I.smp.Samp → ℕ) :
    ∀ {Γ Δ : List PT} {t : PT} (c : Comp pqxdhOps I Γ t) (ρ : ∀ {τ}, Var Γ τ → Var Δ τ),
      (c.rename ρ).queries w ws = c.queries w ws := by
  intro Γ Δ t c ρ
  induction c generalizing Δ <;> simp_all [_root_.ReductionDsl.Comp.rename, Comp.queries]

@[local simp] private theorem wrapBase2_unsupported {Γ₁ Γ₂ Δ : List PT} [Ext Γ₁ Δ] [Ext Γ₂ Δ]
    (pa : Var Γ₁ params2Ty) (sm : Var Γ₂ simTy)
    (c : Comp pqxdhOps pqPrimIface Δ (.prod keyIndRespTy keyIndStateTy)) :
    (wrapBase2 pa sm c).queries tlGapDhKeyInd.unsupportedW (fun _ => 0) =
      c.queries keyIndUnsupportedPrimW (fun _ => 0) := by
  simp [wrapBase2, _root_.SignalPqxdh.Security.ReductionDsl.KeyInd.gPrim, bindV, Comp.queries,
    tlGapDhKeyInd]

@[local simp] private theorem wrapSim2_unsupported {Γ₁ Δ : List PT} [Ext Γ₁ Δ]
    (pa : Var Γ₁ params2Ty)
    (c : Comp pqxdhOps pqGapDhIface Δ (.prod keyIndRespTy simTy)) :
    (wrapSim2 pa c).queries tlGapDhKeyInd.unsupportedW (fun _ => 0) =
      c.queries tlGapDhKeyInd.unsupportedW (fun _ => 0) := by
  simp [wrapSim2, bindV, Comp.queries]

private theorem gdhHandle2_unsupported (S : Setup) (K : Nat) :
    (gdhHandle2 S K).queries tlGapDhKeyInd.unsupportedW (fun _ => 0) = 0 := by
  simp only [gdhHandle2, wrapBase2_unsupported, wrapSim2_unsupported, entryMatchesC_unsupported_zero,
    initPrinGdh2B, genSpkGdh2B, genOpkGdh2B, initiateGdh2B, acceptOpkGdh2B, acceptNoOpkGdhB,
    finishAcceptGdhC, corruptB, testB, roParsedC, roRawFallbackC, revealB, registerGdhB, revealSpkB,
    gPrim, chooseInitRandC, chooseRespRandC, lookupSpkSkC, computePosC, mkPairPosC, fgPatchC,
    findHonestC, honestPeerC, checkProvC, koskBundleOkPowsC, koskSenderOkPowsC, computeOptPosInitC,
    mkSecretPosC, isGameSpkC, isGameOpkC, resolveSigPkC, partnerC, findMV, anyMV,
    liftBase_queries_loc, letV, bindV, caseOptV, caseSumV, Comp.queries]
  simp [sBytes32, sRandom64, sDrKey96, qX25519, qX25519Base, qPow8, qIsCanonical, qSigPkGen,
    qSigSign, qSigVerify, qKemKeyGen, qKemEncaps, qKemDecaps, Comp.queries, tlGapDhKeyInd,
    keyIndUnsupportedPrimW]

private theorem sigActive_handle_unsupported (S : Setup) (b : QueryBudget) :
    (sigKeyInd1KeyActiveDslProg S b).handle.queries tlSigDdhKeyInd.unsupportedW (fun _ => 0) = 0 := by
  change (sig1KeyActiveHandleC S b.q_total).queries tlSigDdhKeyInd.unsupportedW (fun _ => 0) = 0
  simp only [sig1KeyActiveHandleC, sig1KeyActivePreDispatchC, sig1KeyActiveInitPrinB,
    sig1KeyTargetGenSpkB, sig1KeyActiveInitiateCheckC, extract1KeyActiveC, s1Prim, honestPeerC,
    findHonestC, findMV, liftGdhToSigDdh_unsupported, comp_rename_queries_loc,
    gdhHandle2_unsupported S b.q_total, liftBase_queries_loc, letV, bindV, caseOptV, caseSumV,
    Comp.queries]
  simp [sBytes32, sRandom64, qX25519Base, qPow8, qSigVerify, qKemKeyGen, qSigDdhSign,
    Comp.queries, tlSigDdhKeyInd, keyIndUnsupportedPrimW]

@[local simp] private theorem sigChalQ_dsl_unsupported (m : ℕ+) {Γ : List PT}
    (msg : Expr pqxdhOps Γ (B m)) :
    (_root_.SignalPqxdh.Security.ReductionDsl.KeyInd1KeyGapDh.sigChalQ_dsl m msg).queries
      tlSigDdhKeyInd.unsupportedW (fun _ => 0) = 0 := rfl

@[local simp] private theorem callGdhActiveHandle_unsupported (S : Setup) (K : Nat) {Δ : List PT}
    (stA : Var Δ gdh1KeyActiveStateTy) (q : Var Δ keyIndQueryTy) :
    (callGdhActiveHandle S K stA q).queries tlSigDdhKeyInd.unsupportedW (fun _ => 0) = 0 := by
  have hGdh := gdhHandle2_unsupported S K
  simp [callGdhActiveHandle, hGdh, letV, bindV, Comp.queries]

private theorem gdhActive_handle_unsupported (S : Setup) (b : QueryBudget) :
    (fgKeyInd1KeyGapDhActiveDslProg S b).handle.queries tlSigDdhKeyInd.unsupportedW (fun _ => 0) = 0 := by
  change (gdh1KeyActiveHandle S b.q_total).queries tlSigDdhKeyInd.unsupportedW (fun _ => 0) = 0
  simp only [gdh1KeyActiveHandle, callGdhActiveHandle_unsupported, entryMatchesC_unsupported_zero,
    initPrin1KeyActiveGdhB, genSpk1KeyActiveGdhB, genSpkGdhActiveB, genOpkActiveGdhB,
    initiateActiveGdhB, initiateGdhActiveInnerB, gPrim, chooseInitRandC, lookupSpkSkC,
    computePosC, mkPairPosC, fgPatchC, findHonestC, honestPeerC, checkProvC, koskBundleOkPowsC,
    computeOptPosInitC, mkSecretPosC, isGameSpkC, isGameOpkC, resolveSigPkC, partnerC, findMV,
    anyMV, liftGdhComp_unsupported, sigChalQ_dsl_unsupported, liftBase_queries_loc,
    letV, bindV, caseOptV, caseSumV, Comp.queries]
  simp [sBytes32, sRandom64, sDrKey96, qX25519, qX25519Base, qPow8, qIsCanonical, qSigSign,
    qSigVerify, qKemKeyGen, qKemEncaps, Comp.queries, tlGapDhKeyInd, keyIndUnsupportedPrimW]

private theorem GdhSimInv.bump_online_unchanged {S : Setup} {b : QueryBudget}
    {c : Fin 3 → ℕ} {t : KeyIndQuery S} {sK : simShadowAtomicTy.denote}
    (hInv : GdhSimInv S b c sK) (hOn : keyIndQueryKind t = 0) :
    GdhSimInv S b (bumpPred (keyIndSimPred S) c t) sK := by
  rcases sK with ⟨smA, sh⟩
  have hSm : smA = embedVal simTy (projVal simTy smA) := (embedVal_projVal simTy smA).symm
  rw [hSm] at hInv ⊢
  exact GdhSimInv.upd_online_base_only hInv hOn (BaseOnlineNonInc.refl _)

private theorem sigActiveAtomic_handle_eval (S : Setup) (b : QueryBudget)
    (st : sig1KeyActiveStTy.denote) (t : KeyIndQuery S) :
    (sigKeyInd1KeyActiveAtomicProg S b).handle.eval
        (.cons (embedVal sig1KeyActiveStTy st : (sigKeyInd1KeyActiveAtomicProg S b).σ.denote)
          (.cons ((pqKeyIndCodec S).qenc t) .nil)) =
      embedVal S1ARS <$>
        (sig1KeyActiveHandleC S b.q_total).eval
          (.cons st (.cons ((keyIndCodec S).qenc t) .nil)) :=
  liftKeyIndHandle_eval tlSigDdhKeyInd S (sigKeyInd1KeyActiveDslProg S b).handle
    (sigActive_handle_unsupported S b) st t

private theorem gdhActiveAtomic_handle_eval (S : Setup) (b : QueryBudget)
    (stA : gdh1KeyActiveStateTy.denote) (t : KeyIndQuery S) :
    (fgKeyInd1KeyGapDhActiveAtomicProg S b).handle.eval
        (.cons (embedVal gdh1KeyActiveStateTy stA :
            (fgKeyInd1KeyGapDhActiveAtomicProg S b).σ.denote)
          (.cons ((pqKeyIndCodec S).qenc t) .nil)) =
      embedVal (.prod keyIndRespTy gdh1KeyActiveStateTy) <$>
        (gdh1KeyActiveHandle S b.q_total).eval
          (.cons stA (.cons ((keyIndCodec S).qenc t) .nil)) :=
  liftKeyIndHandle_eval tlSigDdhKeyInd S (fgKeyInd1KeyGapDhActiveDslProg S b).handle
    (gdhActive_handle_unsupported S b) stA t

private def fixSigLeg (S : Setup) (b : QueryBudget)
    (st : sig1KeyActiveStTy.denote) : sig1KeyActiveStTy.denote :=
  (st.1, (st.2.1, (fixSent S b st.2.2.1, st.2.2.2)))

private theorem forgetSig1KeyActiveK_embedVal (S : Setup) (b : QueryBudget)
    (st : sig1KeyActiveStTy.denote) (sh : fgShadowAtomicTy.denote) :
    forgetSig1KeyActiveK S b (embedVal sig1KeyActiveStTy st, sh) =
      embedVal sig1KeyActiveStTy (fixSigLeg S b st) := rfl

private def fixParamsLeg (S : Setup) (b : QueryBudget)
    (pa : paramsTy.denote) : paramsTy.denote :=
  let (u, (vPk, (up, (prinFlag, (prinIdx, (dhFlag, (ephIdx, (spkIdx, (opkMode, (opkIdx, mode)))))))))) := pa
  (u, (vPk, (up, (prinFlag, (fixSent S b prinIdx,
    (dhFlag, (fixSent S b ephIdx, (fixSent S b spkIdx, (opkMode, (fixSent S b opkIdx, mode))))))))))

private def fixGdhLeg (S : Setup) (b : QueryBudget)
    (stA : gdh1KeyActiveStateTy.denote) : gdh1KeyActiveStateTy.denote :=
  (((fixParamsLeg S b stA.1.1.1, stA.1.1.2), stA.1.2), stA.2)

private theorem forgetGdh1KeyActiveK_embedVal (S : Setup) (b : QueryBudget)
    (stA : gdh1KeyActiveStateTy.denote) (sh : fgShadowAtomicTy.denote) :
    forgetGdh1KeyActiveK S b (embedVal gdh1KeyActiveStateTy stA, sh) =
      embedVal gdh1KeyActiveStateTy (fixGdhLeg S b stA) := rfl

private theorem wrapBase2_eval_of_pure {Γ₁ Γ₂ Δ : List PT} [Ext Γ₁ Δ] [Ext Γ₂ Δ]
    (pa : Var Γ₁ params2Ty) (sm : Var Γ₂ simTy)
    (c : Comp pqxdhOps pqPrimIface Δ (.prod keyIndRespTy keyIndStateTy))
    (env : Env Δ) {resp : keyIndRespTy.denote} {bSt' : keyIndStateTy.denote}
    (hc : c.eval env = pure (resp, bSt')) :
    (wrapBase2 pa sm c).eval env =
      pure (resp, ((v pa).eval env, (bSt', ((v sm).eval env).2))) := by
  simp [wrapBase2, smUpd, _root_.SignalPqxdh.Security.ReductionDsl.KeyInd.smMk,
    _root_.SignalPqxdh.Security.ReductionDsl.KeyInd.smFgL,
    _root_.SignalPqxdh.Security.ReductionDsl.KeyInd.smRaw,
    _root_.SignalPqxdh.Security.ReductionDsl.KeyInd.smLog,
    _root_.SignalPqxdh.Security.ReductionDsl.KeyInd.smPows,
    bindV, Comp.eval, Expr.eval, v, Ext.wk, hc,
    _root_.SignalPqxdh.Security.embedPrim]

private theorem liftSigDdhNoFgArm_eval_of_pure (S : Setup) {stTy qPayTy : PT}
    {PayAtomic : Ty pqAtomicSig}
    (payE : Expr pqAtomicOps
      (PayAtomic :: [.prod (embedTy stTy) fgShadowAtomicTy, (pqKeyIndCodec S).Q])
      (embedTy qPayTy))
    (arm : Comp pqxdhOps pqSigAndDdhIface [stTy, qPayTy] (.prod keyIndRespTy stTy))
    (hUnsup : arm.queries tlSigDdhKeyInd.unsupportedW (fun _ => 0) = 0)
    (payA : PayAtomic.denote) (stL : stTy.denote) (sh : fgShadowAtomicTy.denote)
    (qEnc : (pqKeyIndCodec S).Q.denote) (payLeg : qPayTy.denote)
    (hPay : payE.eval (.cons payA (.cons (embedVal stTy stL, sh) (.cons qEnc .nil))) =
      embedVal qPayTy payLeg)
    {respL : keyIndRespTy.denote} {stL' : stTy.denote}
    (hEval : arm.eval (.cons stL (.cons payLeg .nil)) = pure (respL, stL')) :
    (liftSigDdhNoFgArm S payE arm).eval
        (.cons payA (.cons (embedVal stTy stL, sh) (.cons qEnc .nil))) =
      pure (embedVal keyIndRespTy respL, (embedVal stTy stL', sh)) := by
  simp only [liftSigDdhNoFgArm, Comp.eval, runAt2_eval, Expr.eval, hPay]
  change (do
    let r ← (mapComp tlSigDdhKeyInd arm).eval (embedEnv (.cons stL (.cons payLeg .nil)))
    pure (r.1, (r.2, sh))) = _
  rw [mapComp_eval tlSigDdhKeyInd arm hUnsup, hEval]
  rfl

private theorem sig1KeyKindHandleC_eval_revDh (S : Setup) (b : QueryBudget)
    (stK : (Ty.prod (embedTy sig1KeyActiveStTy) fgShadowAtomicTy).denote) :
    (sig1KeyKindHandleC S b).eval
        (.cons stK (.cons ((pqKeyIndCodec S).qenc .revealDhSecrets) .nil)) =
      pure ((atomicRNoneE (S := S) (Γ := [])).eval .nil, stK) := by
  unfold sig1KeyKindHandleC
  dsimp only
  rw [dispatchKeyIndQ_eval]
  rfl

private theorem sig1KeyActiveHandleC_eval_revDh (S : Setup) (K : Nat)
    (st : sig1KeyActiveStTy.denote) :
    (sig1KeyActiveHandleC S K).eval
        (.cons st (.cons ((keyIndCodec S).qenc .revealDhSecrets) .nil)) =
      pure (((rNone : Expr pqxdhOps [] keyIndRespTy).eval .nil), st) := by
  rcases st with ⟨tp?, sm, ord, pk, sigB, fg?⟩
  cases fg? <;>
    simp [sig1KeyActiveHandleC, sig1KeyActivePreDispatchC, keyIndCodec,
      _root_.SignalPqxdh.LegacyCosted.keyIndQenc, gdhHandle2,
      _root_.ReductionDsl.Env.ofRename, renamePair,
      saInner, saTP, s1Forgery, s1Pk, s1Fg, s1Upd, isSomeE, rNone,
      letV, bindV, caseSumV, Comp.eval, Expr.eval, v, Ext.wk]

private theorem gdh1KeyKindHandleC_eval_revDh (S : Setup) (b : QueryBudget)
    (stK : (Ty.prod (embedTy gdh1KeyActiveStateTy) fgShadowAtomicTy).denote) :
    (gdh1KeyKindHandleC S b).eval
        (.cons stK (.cons ((pqKeyIndCodec S).qenc .revealDhSecrets) .nil)) =
      pure ((atomicRNoneE (S := S) (Γ := [])).eval .nil, stK) := by
  unfold gdh1KeyKindHandleC
  dsimp only
  rw [dispatchKeyIndQ_eval]
  rfl

private theorem gdh1KeyActiveHandle_eval_revDh (S : Setup) (K : Nat)
    (stA : gdh1KeyActiveStateTy.denote) :
    (gdh1KeyActiveHandle S K).eval
        (.cons stA (.cons ((keyIndCodec S).qenc .revealDhSecrets) .nil)) =
      pure (((rNone : Expr pqxdhOps [] keyIndRespTy).eval .nil), stA) := by
  rcases stA with ⟨⟨⟨pa, sm⟩, sigB⟩, rp?, cnt⟩
  simp [gdh1KeyActiveHandle, callGdhActiveHandle, keyIndCodec,
    _root_.SignalPqxdh.LegacyCosted.keyIndQenc, gdhHandle2,
    renameComp_eval, pullEnv_twoVarRen, rNone,
    letV, bindV, caseSumV, Comp.eval, Expr.eval, v]

@[local simp] private theorem v_eval_cons {Γ Δ : List PT} {σ τ : PT} [Ext Γ Δ]
    (x : Var Γ τ) (a : σ.denote) (env : Env Δ) :
    (@_root_.SignalPqxdh.Security.ReductionDsl.KeyInd.v Γ (σ :: Δ) τ Ext.step x).eval
        (.cons a env) =
      (_root_.SignalPqxdh.Security.ReductionDsl.KeyInd.v x).eval env := rfl

@[local simp] private theorem v_zero_eval {Γ : List PT} {τ : PT} (a : τ.denote) (env : Env Γ) :
    (@_root_.SignalPqxdh.Security.ReductionDsl.KeyInd.v (τ :: Γ) (τ :: Γ) τ Ext.refl .zero).eval
        (.cons a env) = a := rfl

@[local simp] private theorem v_succ_eval {Γ : List PT} {σ τ : PT}
    (x : Var Γ τ) (a : σ.denote) (env : Env Γ) :
    (@_root_.SignalPqxdh.Security.ReductionDsl.KeyInd.v (σ :: Γ) (σ :: Γ) τ Ext.refl (.succ x)).eval
        (.cons a env) =
      (@_root_.SignalPqxdh.Security.ReductionDsl.KeyInd.v Γ Γ τ Ext.refl x).eval env := rfl

private theorem corruptB_eval_eq (K : Nat) {Γ₁ Γ₂ Δ : List PT} [Ext Γ₁ Δ] [Ext Γ₂ Δ]
    (bSt : Var Γ₁ keyIndStateTy) (u : Var Γ₂ .nat) (env : Env Δ) :
    (corruptB K bSt u).eval env =
      (corruptB K (.zero : Var [keyIndStateTy, .nat] keyIndStateTy)
        (.succ .zero : Var [keyIndStateTy, .nat] .nat)).eval
        (.cons ((v bSt).eval env) (.cons ((v u).eval env) .nil)) := by
  simp [corruptB, caseOptV, eFind, eMap, rs, rNone, rCorr, stPrin, stUpd, peSecIKA0, peSecIKAsign,
    peUpd, natEq, Comp.eval, Expr.eval]
  rfl

private theorem freshE_eval_eq (K : Nat) {Γ Δ : List PT}
    (st : Expr pqxdhOps Γ keyIndStateTy) (sid : Expr pqxdhOps Γ sidT) (env : Env Γ)
    (st' : Expr pqxdhOps Δ keyIndStateTy) (sid' : Expr pqxdhOps Δ sidT) (env' : Env Δ)
    (hst : st.eval env = st'.eval env') (hsid : sid.eval env = sid'.eval env') :
    (freshE K st sid).eval env = (freshE K st' sid').eval env' := by
  simp [freshE, eLet2, eLet, eCaseOpt, eFind, stSess, stResps, seSid, seFresh, seTested,
    seRevealed, reSid, reSenderHonest, reTested, reRevealed, Expr.eval, hst, hsid]

private theorem testB_eval_eq (K : Nat) {Γ₁ Γ₂ Δ : List PT} [Ext Γ₁ Δ] [Ext Γ₂ Δ]
    (bSt : Var Γ₁ keyIndStateTy) (sid : Var Γ₂ sidT) (env : Env Δ) :
    (testB K bSt sid).eval env =
      (testB K (.zero : Var [keyIndStateTy, sidT] keyIndStateTy)
        (.succ .zero : Var [keyIndStateTy, sidT] sidT)).eval
        (.cons ((v bSt).eval env) (.cons ((v sid).eval env) .nil)) := by
  have hFr := freshE_eval_eq K (v bSt) (v sid) env
    (v (.zero : Var [keyIndStateTy, sidT] keyIndStateTy))
    (v (.succ .zero : Var [keyIndStateTy, sidT] sidT))
    (.cons ((v bSt).eval env) (.cons ((v sid).eval env) .nil)) rfl rfl
  simp only [testB, caseOptV, Comp.eval]
  have hNot : (Expr.not (freshE K (v bSt) (v sid))).eval env =
      (Expr.not (freshE K (v (.zero : Var [keyIndStateTy, sidT] keyIndStateTy))
        (v (.succ .zero : Var [keyIndStateTy, sidT] sidT)))).eval
        (.cons ((v bSt).eval env) (.cons ((v sid).eval env) .nil)) := by
    simp only [Expr.eval, hFr]
  rw [hNot]
  split_ifs
  · simp [rs, rNone, Expr.eval]
  · simp [eFind, eMap, rs, rNone, rDrKey, stSecb, stSess, stResps, stUpd, seSid, seDrReal,
      seDrRand, seUpd, reSid, reDrReal, reDrRand, reUpd, Expr.eval]
    rfl

private theorem revealB_eval_eq (K : Nat) {Γ₁ Γ₂ Δ : List PT} [Ext Γ₁ Δ] [Ext Γ₂ Δ]
    (bSt : Var Γ₁ keyIndStateTy) (sid : Var Γ₂ sidT) (env : Env Δ) :
    (revealB K bSt sid).eval env =
      (revealB K (.zero : Var [keyIndStateTy, sidT] keyIndStateTy)
        (.succ .zero : Var [keyIndStateTy, sidT] sidT)).eval
        (.cons ((v bSt).eval env) (.cons ((v sid).eval env) .nil)) := by
  simp [revealB, caseOptV, eFind, eMap, rs, rNone, rDrKey, stSess, stResps, stUpd, seSid,
    seTested, seDrReal, seUpd, reSid, reTested, reDrReal, reUpd, Comp.eval, Expr.eval]

private theorem revealSpkB_eval_eq (K : Nat) {Γ₁ Γ₂ Δ : List PT} [Ext Γ₁ Δ] [Ext Γ₂ Δ]
    (bSt : Var Γ₁ keyIndStateTy) (x : Var Γ₂ (.prod .nat .nat)) (env : Env Δ) :
    (revealSpkB K bSt x).eval env =
      (revealSpkB K (.zero : Var [keyIndStateTy, .prod .nat .nat] keyIndStateTy)
        (.succ .zero : Var [keyIndStateTy, .prod .nat .nat] (.prod .nat .nat))).eval
        (.cons ((v bSt).eval env) (.cons ((v x).eval env) .nil)) := by
  simp [revealSpkB, caseOptV, eFind, eMap, rs, rNone, rSpkSk, stSpks, stUpd, nat2Eq, natEq,
    sbSpkSk, sbUpd, Comp.eval, Expr.eval]
  rfl

private theorem sigWrapGdh2NoFgLeg_unsupported {qPayTy : PT}
    (gdhBody : Var [params2Ty, sig1KeyStTy, sig1KeyActiveStTy, qPayTy] params2Ty →
      Var [simTy, params2Ty, sig1KeyStTy, sig1KeyActiveStTy, qPayTy] simTy →
      Var [keyIndStateTy, simTy, params2Ty, sig1KeyStTy, sig1KeyActiveStTy, qPayTy] keyIndStateTy →
      Var [sig1KeyActiveStTy, qPayTy] qPayTy →
      Comp pqxdhOps pqGapDhIface
        [keyIndStateTy, simTy, params2Ty, sig1KeyStTy, sig1KeyActiveStTy, qPayTy]
        (.prod keyIndRespTy gdhState2Ty))
    (hBody : ∀ pa sm bSt x,
      (gdhBody pa sm bSt x).queries tlGapDhKeyInd.unsupportedW (fun _ => 0) = 0) :
    (sigWrapGdh2NoFgLeg gdhBody).queries tlSigDdhKeyInd.unsupportedW (fun _ => 0) = 0 := by
  simp [sigWrapGdh2NoFgLeg, liftGdhToSigDdh_unsupported, hBody, letV, bindV, Comp.queries]

private theorem gdhWrapDelegNoFgLeg_unsupported {qPayTy : PT}
    (gdhBody : Var [params2Ty, paramsTy, gdh1KeyStateTy, gdh1KeyActiveStateTy, qPayTy] params2Ty →
      Var [simTy, params2Ty, paramsTy, gdh1KeyStateTy, gdh1KeyActiveStateTy, qPayTy] simTy →
      Var [keyIndStateTy, simTy, params2Ty, paramsTy, gdh1KeyStateTy,
        gdh1KeyActiveStateTy, qPayTy] keyIndStateTy →
      Var [gdh1KeyActiveStateTy, qPayTy] qPayTy →
      Comp pqxdhOps pqGapDhIface
        [keyIndStateTy, simTy, params2Ty, paramsTy, gdh1KeyStateTy, gdh1KeyActiveStateTy, qPayTy]
        (.prod keyIndRespTy gdhState2Ty))
    (hBody : ∀ pa2 sm bSt x,
      (gdhBody pa2 sm bSt x).queries tlGapDhKeyInd.unsupportedW (fun _ => 0) = 0) :
    (gdhWrapDelegNoFgLeg gdhBody).queries tlSigDdhKeyInd.unsupportedW (fun _ => 0) = 0 := by
  simp [gdhWrapDelegNoFgLeg, liftGdhComp_unsupported, hBody, letV, bindV, Comp.queries]

private theorem sigWrapGdh2NoFgLeg_wrapBase2_eval {qPayTy : PT}
    (body : ∀ {Γ₁ Γ₂ Δ : List PT} [Ext Γ₁ Δ] [Ext Γ₂ Δ],
      Var Γ₁ keyIndStateTy → Var Γ₂ qPayTy → Comp pqxdhOps pqPrimIface Δ
        (.prod keyIndRespTy keyIndStateTy))
    (st : sig1KeyActiveStTy.denote) (payLeg : qPayTy.denote)
    {resp : keyIndRespTy.denote} {bSt' : keyIndStateTy.denote}
    (hBody : ∀ {Γ₁ Γ₂ Δ : List PT} [Ext Γ₁ Δ] [Ext Γ₂ Δ]
      (bSt : Var Γ₁ keyIndStateTy) (x : Var Γ₂ qPayTy) (env : Env Δ),
      (v bSt).eval env = st.2.1.1 → (v x).eval env = payLeg →
      (body bSt x).eval env = pure (resp, bSt')) :
    (sigWrapGdh2NoFgLeg fun pa sm bSt x => wrapBase2 pa sm (body bSt x)).eval
        (.cons st (.cons payLeg .nil)) =
      match st.2.2.2.2.2 with
      | some _ => pure ((rNone : Expr pqxdhOps [] keyIndRespTy).eval .nil, st)
      | none =>
          pure (resp,
            (st.1, ((bSt', st.2.1.2), st.2.2.1, st.2.2.2.1, st.2.2.2.2.1, none))) := by
  rcases st with ⟨tp?, sm, ord, pk, sigB, fg?⟩
  cases fg? with
  | some fg =>
      simp [sigWrapGdh2NoFgLeg, saInner, s1Forgery, isSomeE, rNone, Comp.eval, Expr.eval]
  | none =>
      simp only [sigWrapGdh2NoFgLeg, saInner, saTP, s1Forgery, s1Pk, s1Fg, s1Upd,
        _root_.SignalPqxdh.Security.ReductionDsl.KeyInd.s1Mk,
        _root_.SignalPqxdh.Security.ReductionDsl.KeyInd.s1Target,
        _root_.SignalPqxdh.Security.ReductionDsl.KeyInd.s1Budget,
        smBase, isSomeE, letV, bindV, Comp.eval, Expr.eval, v, Ext.wk, Env.get,
        pure_bind, Bool.false_eq_true, ↓reduceIte]
      rw [liftGdhToSigDdh_eval, wrapBase2_eval_of_pure _ _ _ _ (hBody _ _ _ rfl rfl)]
      simp [Expr.eval, v, Ext.wk]

private theorem gdhWrapDelegNoFgLeg_wrapBase2_eval {qPayTy : PT}
    (body : ∀ {Γ₁ Γ₂ Δ : List PT} [Ext Γ₁ Δ] [Ext Γ₂ Δ],
      Var Γ₁ keyIndStateTy → Var Γ₂ qPayTy → Comp pqxdhOps pqPrimIface Δ
        (.prod keyIndRespTy keyIndStateTy))
    (stA : gdh1KeyActiveStateTy.denote) (payLeg : qPayTy.denote)
    {resp : keyIndRespTy.denote} {bSt' : keyIndStateTy.denote}
    (hBody : ∀ {Γ₁ Γ₂ Δ : List PT} [Ext Γ₁ Δ] [Ext Γ₂ Δ]
      (bSt : Var Γ₁ keyIndStateTy) (x : Var Γ₂ qPayTy) (env : Env Δ),
      (v bSt).eval env = stA.1.1.2.1 → (v x).eval env = payLeg →
      (body bSt x).eval env = pure (resp, bSt')) :
    (gdhWrapDelegNoFgLeg fun pa2 sm bSt x => wrapBase2 pa2 sm (body bSt x)).eval
        (.cons stA (.cons payLeg .nil)) =
      pure (resp, (((stA.1.1.1, (bSt', stA.1.1.2.2)), stA.1.2), stA.2)) := by
  rcases stA with ⟨⟨⟨pa, sm⟩, sigB⟩, rp?, cnt⟩
  simp only [gdhWrapDelegNoFgLeg, smBase, letV, bindV, Comp.eval, Expr.eval, v, Ext.wk, Env.get,
    pure_bind]
  rw [liftGdhComp_eval, wrapBase2_eval_of_pure _ _ _ _ (hBody _ _ _ rfl rfl)]
  simp [Expr.eval, v, Ext.wk]

private theorem finSidToNatExpr_sidV (S : Setup) {Γ : List (Ty pqAtomicSig)}
    (sid : _root_.SignalPqxdh.SessionId S) (env : _root_.ReductionDsl.Env Γ) :
    (finSidToNatExpr S .v0).eval
        (.cons (_root_.ReductionDsl.sidV (Pt := Empty) sid) env) =
      embedVal sidT (_root_.SignalPqxdh.Security.ReductionDsl.KeyInd.sessionIdToVal sid) := by
  cases sid <;> rfl

private theorem GdhSimInv.base_online_len {S : Setup} {b : QueryBudget}
    {c : Fin 3 → ℕ} {sm : simTy.denote} {sh : fgShadowAtomicTy.denote}
    (hInv : GdhSimInv S b c (embedVal simTy sm, sh)) :
    BaseOnlineLenInv c sm.1 := by
  have hProj : projVal keyIndStateTy (embedVal simTy sm).1 = sm.1 :=
    congrArg Prod.fst (projVal_embedVal simTy sm)
  exact hProj ▸ hInv.online_len

private theorem corruptB_unsup (K : Nat) {Γ₁ Γ₂ Δ : List PT} [Ext Γ₁ Δ] [Ext Γ₂ Δ]
    (bSt : Var Γ₁ keyIndStateTy) (u : Var Γ₂ .nat) :
    (corruptB K (Δ := Δ) bSt u).queries keyIndUnsupportedPrimW (fun _ => 0) = 0 := by
  simp [corruptB, caseOptV, Comp.queries]

private theorem testB_unsup (K : Nat) {Γ₁ Γ₂ Δ : List PT} [Ext Γ₁ Δ] [Ext Γ₂ Δ]
    (bSt : Var Γ₁ keyIndStateTy) (sid : Var Γ₂ sidT) :
    (testB K (Δ := Δ) bSt sid).queries keyIndUnsupportedPrimW (fun _ => 0) = 0 := by
  simp [testB, caseOptV, Comp.queries]

private theorem revealB_unsup (K : Nat) {Γ₁ Γ₂ Δ : List PT} [Ext Γ₁ Δ] [Ext Γ₂ Δ]
    (bSt : Var Γ₁ keyIndStateTy) (sid : Var Γ₂ sidT) :
    (revealB K (Δ := Δ) bSt sid).queries keyIndUnsupportedPrimW (fun _ => 0) = 0 := by
  simp [revealB, caseOptV, Comp.queries]

private theorem revealSpkB_unsup (K : Nat) {Γ₁ Γ₂ Δ : List PT} [Ext Γ₁ Δ] [Ext Γ₂ Δ]
    (bSt : Var Γ₁ keyIndStateTy) (x : Var Γ₂ (.prod .nat .nat)) :
    (revealSpkB K (Δ := Δ) bSt x).queries keyIndUnsupportedPrimW (fun _ => 0) = 0 := by
  simp [revealSpkB, caseOptV, Comp.queries]

private theorem gdhHandle2_eval_corrupt (S : Setup) (K : Nat)
    (pa : params2Ty.denote) (sm : simTy.denote) (u : Fin S.N_id)
    {resp : keyIndRespTy.denote} {bSt' : keyIndStateTy.denote}
    (hBody : (corruptB K (.zero : Var [keyIndStateTy, .nat] keyIndStateTy)
      (.succ .zero : Var [keyIndStateTy, .nat] .nat)).eval
      (.cons sm.1 (.cons (t := .nat) u.val .nil)) = pure (resp, bSt')) :
    (gdhHandle2 S K).eval (.cons (pa, sm) (.cons ((keyIndCodec S).qenc (.corruptIK u)) .nil)) =
      pure (resp, (pa, (bSt', sm.2))) := by
  simp only [gdhHandle2, keyIndCodec, _root_.SignalPqxdh.LegacyCosted.keyIndQenc, smBase,
    letV, caseSumV, Comp.eval, Expr.eval, v, Ext.wk, Env.get, pure_bind]
  exact wrapBase2_eval_of_pure _ _ _ _ ((corruptB_eval_eq K _ _ _).trans hBody)

private theorem gdhHandle2_eval_test (S : Setup) (K : Nat)
    (pa : params2Ty.denote) (sm : simTy.denote) (sid : _root_.SignalPqxdh.SessionId S)
    {resp : keyIndRespTy.denote} {bSt' : keyIndStateTy.denote}
    (hBody : (testB K (.zero : Var [keyIndStateTy, sidT] keyIndStateTy)
      (.succ .zero : Var [keyIndStateTy, sidT] sidT)).eval
      (.cons sm.1 (.cons (sessionIdToVal sid) .nil)) = pure (resp, bSt')) :
    (gdhHandle2 S K).eval (.cons (pa, sm) (.cons ((keyIndCodec S).qenc (.testSession sid)) .nil)) =
      pure (resp, (pa, (bSt', sm.2))) := by
  simp only [gdhHandle2, keyIndCodec, _root_.SignalPqxdh.LegacyCosted.keyIndQenc, smBase,
    letV, caseSumV, Comp.eval, Expr.eval, v, Ext.wk, Env.get, pure_bind]
  exact wrapBase2_eval_of_pure _ _ _ _ ((testB_eval_eq K _ _ _).trans hBody)

private theorem gdhHandle2_eval_reveal (S : Setup) (K : Nat)
    (pa : params2Ty.denote) (sm : simTy.denote) (sid : _root_.SignalPqxdh.SessionId S)
    {resp : keyIndRespTy.denote} {bSt' : keyIndStateTy.denote}
    (hBody : (revealB K (.zero : Var [keyIndStateTy, sidT] keyIndStateTy)
      (.succ .zero : Var [keyIndStateTy, sidT] sidT)).eval
      (.cons sm.1 (.cons (sessionIdToVal sid) .nil)) = pure (resp, bSt')) :
    (gdhHandle2 S K).eval
        (.cons (pa, sm) (.cons ((keyIndCodec S).qenc (.revealSessionKey sid)) .nil)) =
      pure (resp, (pa, (bSt', sm.2))) := by
  simp only [gdhHandle2, keyIndCodec, _root_.SignalPqxdh.LegacyCosted.keyIndQenc, smBase,
    letV, caseSumV, Comp.eval, Expr.eval, v, Ext.wk, Env.get, pure_bind]
  exact wrapBase2_eval_of_pure _ _ _ _ ((revealB_eval_eq K _ _ _).trans hBody)

private theorem gdhHandle2_eval_revealSpk (S : Setup) (K : Nat)
    (pa : params2Ty.denote) (sm : simTy.denote) (u : Fin S.N_id) (j : Fin S.N_recv)
    {resp : keyIndRespTy.denote} {bSt' : keyIndStateTy.denote}
    (hBody : (revealSpkB K (.zero : Var [keyIndStateTy, .prod .nat .nat] keyIndStateTy)
      (.succ .zero : Var [keyIndStateTy, .prod .nat .nat] (.prod .nat .nat))).eval
      (.cons sm.1 (.cons (t := .prod .nat .nat) (u.val, j.val) .nil)) = pure (resp, bSt')) :
    (gdhHandle2 S K).eval
        (.cons (pa, sm) (.cons ((keyIndCodec S).qenc (.revealSpkSk u j)) .nil)) =
      pure (resp, (pa, (bSt', sm.2))) := by
  simp only [gdhHandle2, keyIndCodec, _root_.SignalPqxdh.LegacyCosted.keyIndQenc, smBase,
    letV, caseSumV, Comp.eval, Expr.eval, v, Ext.wk, Env.get, pure_bind]
  exact wrapBase2_eval_of_pure _ _ _ _ ((revealSpkB_eval_eq K _ _ _).trans hBody)

private def isDelegNoFgQuery {S : Setup} : KeyIndQuery S → Prop
  | .corruptIK _ | .testSession _ | .revealSessionKey _ | .revealSpkSk _ _ => True
  | _ => False

private theorem sig1KeyActiveHandleC_eval_of_gdh2 (S : Setup) (K : Nat)
    (st : sig1KeyActiveStTy.denote) (q : KeyIndQuery S) (hDeleg : isDelegNoFgQuery q)
    {resp : keyIndRespTy.denote} {bSt' : keyIndStateTy.denote}
    (hGdh2 : ∀ pa, (gdhHandle2 S K).eval (.cons (pa, st.2.1) (.cons ((keyIndCodec S).qenc q) .nil)) =
      pure (resp, (pa, (bSt', st.2.1.2)))) :
    (sig1KeyActiveHandleC S K).eval (.cons st (.cons ((keyIndCodec S).qenc q) .nil)) =
      match st.2.2.2.2.2 with
      | some _ => pure ((rNone : Expr pqxdhOps [] keyIndRespTy).eval .nil, st)
      | none => pure (resp, (st.1, ((bSt', st.2.1.2), st.2.2.1, st.2.2.2.1, st.2.2.2.2.1, none))) := by
  rcases st with ⟨tp?, sm, ord, pk, sigB, fg?⟩
  cases fg? with
  | some fg =>
      simp [sig1KeyActiveHandleC, sig1KeyActivePreDispatchC, saInner, s1Forgery, isSomeE, rNone,
        bindV, caseSumV, Comp.eval, Expr.eval, v, Ext.wk]
  | none =>
      have hPre :
          (sig1KeyActivePreDispatchC S K
            (.zero : Var [sig1KeyActiveStTy, (keyIndCodec S).Q] sig1KeyActiveStTy)
            (.succ .zero : Var [sig1KeyActiveStTy, (keyIndCodec S).Q] (keyIndCodec S).Q)).eval
            (.cons (t := sig1KeyActiveStTy) (tp?, (sm, ord, pk, sigB, none))
              (.cons ((keyIndCodec S).qenc q) .nil)) = pure (.inr ()) := by
        cases q <;> try cases hDeleg
        all_goals simp [sig1KeyActivePreDispatchC, keyIndCodec,
          _root_.SignalPqxdh.LegacyCosted.keyIndQenc, saInner, s1Forgery, isSomeE,
          caseSumV, Comp.eval, Expr.eval, v, Ext.wk]
      simp only [sig1KeyActiveHandleC, bindV, caseSumV, letV, Comp.eval]
      erw [hPre]
      simp only [pure_bind, liftGdhToSigDdh_eval, _root_.ReductionDsl.Comp.rename_eval,
        _root_.ReductionDsl.Env.ofRename, renamePair, s1Pk, Expr.eval, v, Ext.wk, Env.get]
      erw [hGdh2]; simp

private theorem gdh1KeyActiveHandle_eval_of_gdh2 (S : Setup) (K : Nat)
    (stA : gdh1KeyActiveStateTy.denote) (q : KeyIndQuery S) (hDeleg : isDelegNoFgQuery q)
    {resp : keyIndRespTy.denote} {bSt' : keyIndStateTy.denote}
    (hGdh2 : ∀ pa2, (gdhHandle2 S K).eval
      (.cons (pa2, stA.1.1.2) (.cons ((keyIndCodec S).qenc q) .nil)) =
      pure (resp, (pa2, (bSt', stA.1.1.2.2)))) :
    (gdh1KeyActiveHandle S K).eval (.cons stA (.cons ((keyIndCodec S).qenc q) .nil)) =
      pure (resp, (((stA.1.1.1, (bSt', stA.1.1.2.2)), stA.1.2), stA.2)) := by
  rcases stA with ⟨⟨⟨pa, sm⟩, sigB⟩, rp?, cnt⟩
  have hCall : ∀ {Δ : List PT} (stAV : Var Δ gdh1KeyActiveStateTy) (qV : Var Δ keyIndQueryTy)
      (env : Env Δ), env.get stAV = (((pa, sm), sigB), rp?, cnt) →
      env.get qV = (keyIndCodec S).qenc q →
      (callGdhActiveHandle S K stAV qV).eval env =
        pure (resp, (((pa, (bSt', sm.2)), sigB), rp?, cnt)) := by
    intro Δ stAV qV env hst hq
    simp only [callGdhActiveHandle, letV, bindV, Comp.eval, renameComp_eval, pullEnv_twoVarRen,
      liftGdhComp_eval, Expr.eval, v, Ext.wk, Env.get, pure_bind, hst, hq]
    rw [hGdh2]; simp
  cases q <;> try cases hDeleg
  all_goals
    simp only [gdh1KeyActiveHandle, keyIndCodec, _root_.SignalPqxdh.LegacyCosted.keyIndQenc,
      caseSumV, Comp.eval, Expr.eval, v, Ext.wk, Env.get]
    exact hCall _ _ _ rfl rfl

private theorem sigStepSim_of_pure (S : Setup) (b : QueryBudget) (t : KeyIndQuery S)
    (hOn : keyIndQueryKind t = 0) (hDeleg : isDelegNoFgQuery t)
    (hStep : ∀ c, (∀ j, c j ≤ keyIndSimBounds b j) →
      ∀ (stL : sig1KeyActiveStTy.denote) (sh : fgShadowAtomicTy.denote),
      BaseOnlineLenInv c stL.2.1.1 →
      ∃ resp bSt', BaseOnlineNonInc stL.2.1.1 bSt' ∧
        (∀ pa, (gdhHandle2 S b.q_total).eval (.cons (pa, stL.2.1) (.cons ((keyIndCodec S).qenc t) .nil)) =
          pure (resp, (pa, (bSt', stL.2.1.2)))) ∧
        (sig1KeyKindHandleC S b).eval
          (.cons (embedVal sig1KeyActiveStTy stL, sh) (.cons ((pqKeyIndCodec S).qenc t) .nil)) =
          match stL.2.2.2.2.2 with
          | some _ => pure (embedVal keyIndRespTy ((rNone : Expr pqxdhOps [] keyIndRespTy).eval .nil),
              (embedVal sig1KeyActiveStTy stL, sh))
          | none => pure (embedVal keyIndRespTy resp, (embedVal sig1KeyActiveStTy
              (stL.1, ((bSt', stL.2.1.2), stL.2.2.1, stL.2.2.2.1, stL.2.2.2.2.1, none)), sh))) :
    KeyIndStepSim S b (forgetSig1KeyActiveK S b) (Sig1KeyActiveSimInv S b)
      (sig1KeyKindHandleC S b) (sigKeyInd1KeyActiveAtomicProg S b).handle t := by
  intro c ⟨stA, sh⟩ hB _ hInv
  set stL := projVal sig1KeyActiveStTy stA
  have hStA : stA = embedVal sig1KeyActiveStTy stL := (embedVal_projVal sig1KeyActiveStTy stA).symm
  rw [hStA] at hInv ⊢
  obtain ⟨resp, bSt', hNI, hGdh2, hKind⟩ := hStep c hB stL sh (GdhSimInv.base_online_len hInv)
  rw [hKind]
  rcases stL with ⟨tp?, sm, ord, pk, sigB, fg?⟩
  cases fg? with
  | some fg =>
      refine ⟨?_, ?_⟩
      · simp only [map_pure, Prod.map_apply, id_eq]
        refine Eq.trans ?_ (sigActiveAtomic_handle_eval S b
          (fixSigLeg S b (tp?, (sm, ord, pk, sigB, some fg))) t).symm
        rw [sig1KeyActiveHandleC_eval_of_gdh2 S b.q_total
          (fixSigLeg S b (tp?, (sm, ord, pk, sigB, some fg))) t hDeleg hGdh2]; rfl
      · simp only [support_pure, Set.mem_singleton_iff, forall_eq]
        exact GdhSimInv.bump_online_unchanged hInv hOn
  | none =>
      refine ⟨?_, ?_⟩
      · simp only [map_pure, Prod.map_apply, id_eq]
        refine Eq.trans ?_ (sigActiveAtomic_handle_eval S b
          (fixSigLeg S b (tp?, (sm, ord, pk, sigB, none))) t).symm
        rw [sig1KeyActiveHandleC_eval_of_gdh2 S b.q_total
          (fixSigLeg S b (tp?, (sm, ord, pk, sigB, none))) t hDeleg hGdh2]; rfl
      · simp only [support_pure, Set.mem_singleton_iff, forall_eq]
        exact GdhSimInv.upd_online_base_only hInv hOn hNI

private theorem fgStepSim_of_pure (S : Setup) (b : QueryBudget) (t : KeyIndQuery S)
    (hOn : keyIndQueryKind t = 0) (hDeleg : isDelegNoFgQuery t)
    (hStep : ∀ c, (∀ j, c j ≤ keyIndSimBounds b j) →
      ∀ (stL : gdh1KeyActiveStateTy.denote) (sh : fgShadowAtomicTy.denote),
      BaseOnlineLenInv c stL.1.1.2.1 →
      ∃ resp bSt', BaseOnlineNonInc stL.1.1.2.1 bSt' ∧
        (∀ pa2, (gdhHandle2 S b.q_total).eval (.cons (pa2, stL.1.1.2) (.cons ((keyIndCodec S).qenc t) .nil)) =
          pure (resp, (pa2, (bSt', stL.1.1.2.2)))) ∧
        (gdh1KeyKindHandleC S b).eval
          (.cons (embedVal gdh1KeyActiveStateTy stL, sh) (.cons ((pqKeyIndCodec S).qenc t) .nil)) =
          pure (embedVal keyIndRespTy resp,
            (embedVal gdh1KeyActiveStateTy (((stL.1.1.1, (bSt', stL.1.1.2.2)), stL.1.2), stL.2), sh))) :
    KeyIndStepSim S b (forgetGdh1KeyActiveK S b) (Gdh1KeyActiveSimInv S b)
      (gdh1KeyKindHandleC S b) (fgKeyInd1KeyGapDhActiveAtomicProg S b).handle t := by
  intro c ⟨stA, sh⟩ hB _ hInv
  set stL := projVal gdh1KeyActiveStateTy stA
  have hStA : stA = embedVal gdh1KeyActiveStateTy stL := (embedVal_projVal gdh1KeyActiveStateTy stA).symm
  rw [hStA] at hInv ⊢
  obtain ⟨resp, bSt', hNI, hGdh2, hKind⟩ := hStep c hB stL sh (GdhSimInv.base_online_len hInv.sim_inv)
  rw [hKind]
  rcases stL with ⟨⟨⟨pa, sm⟩, sigB⟩, rp?, cnt⟩
  refine ⟨?_, ?_⟩
  · simp only [map_pure, Prod.map_apply, id_eq]
    refine Eq.trans ?_ (gdhActiveAtomic_handle_eval S b
      (fixGdhLeg S b (((pa, sm), sigB), rp?, cnt)) t).symm
    rw [gdh1KeyActiveHandle_eval_of_gdh2 S b.q_total
      (fixGdhLeg S b (((pa, sm), sigB), rp?, cnt)) t hDeleg hGdh2]; rfl
  · simp only [support_pure, Set.mem_singleton_iff, forall_eq]
    exact { sim_inv := GdhSimInv.upd_online_base_only hInv.sim_inv hOn hNI
            sendOpkCnt_le := by rw [bumpPred_online_0 (S := S) hOn]
                                exact Nat.le_succ_of_le hInv.sendOpkCnt_le }

private theorem liftSigDdhNoFgArm_sigWrap_eval (S : Setup) {qPayTy : PT}
    {PayAtomic : Ty pqAtomicSig}
    (payE : Expr pqAtomicOps
      (PayAtomic :: [.prod (embedTy sig1KeyActiveStTy) fgShadowAtomicTy, (pqKeyIndCodec S).Q])
      (embedTy qPayTy))
    (body : ∀ {Γ₁ Γ₂ Δ : List PT} [Ext Γ₁ Δ] [Ext Γ₂ Δ],
      Var Γ₁ keyIndStateTy → Var Γ₂ qPayTy → Comp pqxdhOps pqPrimIface Δ
        (.prod keyIndRespTy keyIndStateTy))
    (hUnsup : ∀ {Γ₁ Γ₂ Δ : List PT} [h₁ : Ext Γ₁ Δ] [h₂ : Ext Γ₂ Δ]
      (bSt : Var Γ₁ keyIndStateTy) (x : Var Γ₂ qPayTy),
      (@body Γ₁ Γ₂ Δ h₁ h₂ bSt x).queries keyIndUnsupportedPrimW (fun _ => 0) = 0)
    (payA : PayAtomic.denote) (stL : sig1KeyActiveStTy.denote) (sh : fgShadowAtomicTy.denote)
    (qEnc : (pqKeyIndCodec S).Q.denote) (payLeg : qPayTy.denote)
    (hPay : payE.eval (.cons payA (.cons (embedVal sig1KeyActiveStTy stL, sh) (.cons qEnc .nil))) =
      embedVal qPayTy payLeg)
    {resp : keyIndRespTy.denote} {bSt' : keyIndStateTy.denote}
    (hBody : ∀ {Γ₁ Γ₂ Δ : List PT} [Ext Γ₁ Δ] [Ext Γ₂ Δ]
      (bSt : Var Γ₁ keyIndStateTy) (x : Var Γ₂ qPayTy) (env : Env Δ),
      (v bSt).eval env = stL.2.1.1 → (v x).eval env = payLeg →
      (body bSt x).eval env = pure (resp, bSt')) :
    (liftSigDdhNoFgArm S payE
      (sigWrapGdh2NoFgLeg fun pa sm bSt x => wrapBase2 pa sm (body bSt x))).eval
        (.cons payA (.cons (embedVal sig1KeyActiveStTy stL, sh) (.cons qEnc .nil))) =
      match stL.2.2.2.2.2 with
      | some _ =>
          pure (embedVal keyIndRespTy ((rNone : Expr pqxdhOps [] keyIndRespTy).eval .nil),
            (embedVal sig1KeyActiveStTy stL, sh))
      | none =>
          pure (embedVal keyIndRespTy resp,
            (embedVal sig1KeyActiveStTy
              (stL.1, ((bSt', stL.2.1.2), stL.2.2.1, stL.2.2.2.1, stL.2.2.2.2.1, none)), sh)) := by
  have hArmU := sigWrapGdh2NoFgLeg_unsupported
    (fun pa sm bSt x => wrapBase2 pa sm (body bSt x))
    (fun pa sm bSt x => by rw [wrapBase2_unsupported, hUnsup])
  have hEv := sigWrapGdh2NoFgLeg_wrapBase2_eval body stL payLeg hBody
  rcases stL with ⟨tp?, sm, ord, pk, sigB, fg?⟩
  cases fg? <;>
    exact liftSigDdhNoFgArm_eval_of_pure S payE _ hArmU payA _ sh qEnc payLeg hPay hEv

private theorem liftSigDdhNoFgArm_gdhWrap_eval (S : Setup) {qPayTy : PT}
    {PayAtomic : Ty pqAtomicSig}
    (payE : Expr pqAtomicOps
      (PayAtomic :: [.prod (embedTy gdh1KeyActiveStateTy) fgShadowAtomicTy, (pqKeyIndCodec S).Q])
      (embedTy qPayTy))
    (body : ∀ {Γ₁ Γ₂ Δ : List PT} [Ext Γ₁ Δ] [Ext Γ₂ Δ],
      Var Γ₁ keyIndStateTy → Var Γ₂ qPayTy → Comp pqxdhOps pqPrimIface Δ
        (.prod keyIndRespTy keyIndStateTy))
    (hUnsup : ∀ {Γ₁ Γ₂ Δ : List PT} [h₁ : Ext Γ₁ Δ] [h₂ : Ext Γ₂ Δ]
      (bSt : Var Γ₁ keyIndStateTy) (x : Var Γ₂ qPayTy),
      (@body Γ₁ Γ₂ Δ h₁ h₂ bSt x).queries keyIndUnsupportedPrimW (fun _ => 0) = 0)
    (payA : PayAtomic.denote) (stL : gdh1KeyActiveStateTy.denote) (sh : fgShadowAtomicTy.denote)
    (qEnc : (pqKeyIndCodec S).Q.denote) (payLeg : qPayTy.denote)
    (hPay : payE.eval (.cons payA (.cons (embedVal gdh1KeyActiveStateTy stL, sh) (.cons qEnc .nil))) =
      embedVal qPayTy payLeg)
    {resp : keyIndRespTy.denote} {bSt' : keyIndStateTy.denote}
    (hBody : ∀ {Γ₁ Γ₂ Δ : List PT} [Ext Γ₁ Δ] [Ext Γ₂ Δ]
      (bSt : Var Γ₁ keyIndStateTy) (x : Var Γ₂ qPayTy) (env : Env Δ),
      (v bSt).eval env = stL.1.1.2.1 → (v x).eval env = payLeg →
      (body bSt x).eval env = pure (resp, bSt')) :
    (liftSigDdhNoFgArm S payE
      (gdhWrapDelegNoFgLeg fun pa2 sm bSt x => wrapBase2 pa2 sm (body bSt x))).eval
        (.cons payA (.cons (embedVal gdh1KeyActiveStateTy stL, sh) (.cons qEnc .nil))) =
      pure (embedVal keyIndRespTy resp,
        (embedVal gdh1KeyActiveStateTy
          (((stL.1.1.1, (bSt', stL.1.1.2.2)), stL.1.2), stL.2), sh)) := by
  have hArmU := gdhWrapDelegNoFgLeg_unsupported
    (fun pa2 sm bSt x => wrapBase2 pa2 sm (body bSt x))
    (fun pa2 sm bSt x => by rw [wrapBase2_unsupported, hUnsup])
  exact liftSigDdhNoFgArm_eval_of_pure S payE _ hArmU payA stL sh qEnc payLeg hPay
    (gdhWrapDelegNoFgLeg_wrapBase2_eval body stL payLeg hBody)

private theorem kOn_eq_simBounds0 (S : Setup) (b : QueryBudget) :
    (keyIndKFuelsOfBudget S b).kOn = keyIndSimBounds b 0 := rfl

end Helpers

/-- `.corruptIK` step simulation for active 1-key `sigKeyInd1KeyKindAtomicProg`. -/
theorem sigKeyInd1KeyKindAtomicProg_hStep_corruptIK (S : Setup) (b : QueryBudget) :
    ∀ u, KeyIndStepSim S b (forgetSig1KeyActiveK S b) (Sig1KeyActiveSimInv S b)
      (sig1KeyKindHandleC S b) (sigKeyInd1KeyActiveAtomicProg S b).handle
      (.corruptIK u) := by
  intro u
  refine sigStepSim_of_pure S b (.corruptIK u) rfl trivial fun c hB stL sh hBase => ?_
  obtain ⟨resp, bSt', hPure, hNI⟩ := corruptB_eval_pure (K := b.q_total)
    (.zero : Var [keyIndStateTy, .nat] keyIndStateTy)
    (.succ .zero : Var [keyIndStateTy, .nat] .nat)
    (.cons stL.2.1.1 (.cons (t := .nat) u.val .nil))
  refine ⟨resp, bSt', hNI, fun pa => gdhHandle2_eval_corrupt S b.q_total pa stL.2.1 u hPure, ?_⟩
  unfold sig1KeyKindHandleC; dsimp only; rw [dispatchKeyIndQ_eval]
  refine liftSigDdhNoFgArm_sigWrap_eval S _
    (fun bSt x => corruptB (keyIndKFuelsOfBudget S b).kOn bSt x)
    (fun {Γ₁ Γ₂ Δ} _ _ bSt x => corruptB_unsup _ (Δ := Δ) bSt x) _ stL sh _ u.val ?_
    (fun bSt x env hb hx => by
      rw [corruptB_eval_eq, hb, hx, kOn_eq_simBounds0,
        corruptB_min_eq _ _ _ (Nat.le_trans hBase.prin_le (hB 0)) (Nat.min_le_right _ _)]
      exact hPure); rfl

/-- `.testSession` step simulation for active 1-key `sigKeyInd1KeyKindAtomicProg`. -/
theorem sigKeyInd1KeyKindAtomicProg_hStep_testSession (S : Setup) (b : QueryBudget) :
    ∀ sid, KeyIndStepSim S b (forgetSig1KeyActiveK S b) (Sig1KeyActiveSimInv S b)
      (sig1KeyKindHandleC S b) (sigKeyInd1KeyActiveAtomicProg S b).handle
      (.testSession sid) := by
  intro sid
  refine sigStepSim_of_pure S b (.testSession sid) rfl trivial fun c hB stL sh hBase => ?_
  obtain ⟨resp, bSt', hPure, hNI⟩ := testB_eval_pure (K := b.q_total)
    (.zero : Var [keyIndStateTy, sidT] keyIndStateTy)
    (.succ .zero : Var [keyIndStateTy, sidT] sidT)
    (.cons stL.2.1.1 (.cons (sessionIdToVal sid) .nil))
  refine ⟨resp, bSt', hNI, fun pa => gdhHandle2_eval_test S b.q_total pa stL.2.1 sid hPure, ?_⟩
  unfold sig1KeyKindHandleC; dsimp only; rw [dispatchKeyIndQ_eval]
  exact liftSigDdhNoFgArm_sigWrap_eval S _
    (fun bSt x => testB (keyIndKFuelsOfBudget S b).kOn bSt x)
    (fun {Γ₁ Γ₂ Δ} _ _ bSt x => testB_unsup _ (Δ := Δ) bSt x) _ stL sh _ (sessionIdToVal sid)
    (finSidToNatExpr_sidV S sid _) fun bSt x env hb hx => by
      rw [testB_eval_eq, hb, hx, kOn_eq_simBounds0,
        testB_min_eq _ _ _ hBase (hB 0) (Nat.min_le_right _ _)]
      exact hPure

/-- `.revealDhSecrets` step simulation for active 1-key `sigKeyInd1KeyKindAtomicProg`. -/
theorem sigKeyInd1KeyKindAtomicProg_hStep_revealDhSecrets (S : Setup) (b : QueryBudget) :
    KeyIndStepSim S b (forgetSig1KeyActiveK S b) (Sig1KeyActiveSimInv S b)
      (sig1KeyKindHandleC S b) (sigKeyInd1KeyActiveAtomicProg S b).handle
      .revealDhSecrets := by
  intro c stK _ _ hInv
  rw [sig1KeyKindHandleC_eval_revDh]
  refine ⟨?_, ?_⟩
  · rcases stK with ⟨stA, sh⟩
    set stL := projVal sig1KeyActiveStTy stA
    have hStA : stA = embedVal sig1KeyActiveStTy stL :=
      (embedVal_projVal sig1KeyActiveStTy stA).symm
    rw [hStA, forgetSig1KeyActiveK_embedVal]
    refine Eq.trans ?_ (sigActiveAtomic_handle_eval S b (fixSigLeg S b stL) .revealDhSecrets).symm
    rw [sig1KeyActiveHandleC_eval_revDh]; rfl
  · simp only [support_pure, Set.mem_singleton_iff, forall_eq]
    exact GdhSimInv.bump_online_unchanged hInv rfl

/-- `.revealSessionKey` step simulation for active 1-key `sigKeyInd1KeyKindAtomicProg`. -/
theorem sigKeyInd1KeyKindAtomicProg_hStep_revealSessionKey (S : Setup) (b : QueryBudget) :
    ∀ sid, KeyIndStepSim S b (forgetSig1KeyActiveK S b) (Sig1KeyActiveSimInv S b)
      (sig1KeyKindHandleC S b) (sigKeyInd1KeyActiveAtomicProg S b).handle
      (.revealSessionKey sid) := by
  intro sid
  refine sigStepSim_of_pure S b (.revealSessionKey sid) rfl trivial fun c hB stL sh hBase => ?_
  obtain ⟨resp, bSt', hPure, hNI⟩ := revealB_eval_pure (K := b.q_total)
    (.zero : Var [keyIndStateTy, sidT] keyIndStateTy)
    (.succ .zero : Var [keyIndStateTy, sidT] sidT)
    (.cons stL.2.1.1 (.cons (sessionIdToVal sid) .nil))
  refine ⟨resp, bSt', hNI, fun pa => gdhHandle2_eval_reveal S b.q_total pa stL.2.1 sid hPure, ?_⟩
  unfold sig1KeyKindHandleC; dsimp only; rw [dispatchKeyIndQ_eval]
  exact liftSigDdhNoFgArm_sigWrap_eval S _
    (fun bSt x => revealB (keyIndKFuelsOfBudget S b).kOn bSt x)
    (fun {Γ₁ Γ₂ Δ} _ _ bSt x => revealB_unsup _ (Δ := Δ) bSt x) _ stL sh _ (sessionIdToVal sid)
    (finSidToNatExpr_sidV S sid _) fun bSt x env hb hx => by
      rw [revealB_eval_eq, hb, hx, kOn_eq_simBounds0,
        revealB_min_eq _ _ _ hBase (hB 0) (Nat.min_le_right _ _)]
      exact hPure

/-- `.revealSpkSk` step simulation for active 1-key `sigKeyInd1KeyKindAtomicProg`. -/
theorem sigKeyInd1KeyKindAtomicProg_hStep_revealSpkSk (S : Setup) (b : QueryBudget) :
    ∀ u j, KeyIndStepSim S b (forgetSig1KeyActiveK S b) (Sig1KeyActiveSimInv S b)
      (sig1KeyKindHandleC S b) (sigKeyInd1KeyActiveAtomicProg S b).handle
      (.revealSpkSk u j) := by
  intro u j
  refine sigStepSim_of_pure S b (.revealSpkSk u j) rfl trivial fun c hB stL sh hBase => ?_
  obtain ⟨resp, bSt', hPure, hNI⟩ := revealSpkB_eval_pure (K := b.q_total)
    (.zero : Var [keyIndStateTy, .prod .nat .nat] keyIndStateTy)
    (.succ .zero : Var [keyIndStateTy, .prod .nat .nat] (.prod .nat .nat))
    (.cons stL.2.1.1 (.cons (t := .prod .nat .nat) (u.val, j.val) .nil))
  refine ⟨resp, bSt', hNI,
    fun pa => gdhHandle2_eval_revealSpk S b.q_total pa stL.2.1 u j hPure, ?_⟩
  unfold sig1KeyKindHandleC; dsimp only; rw [dispatchKeyIndQ_eval]
  refine liftSigDdhNoFgArm_sigWrap_eval S _
    (fun bSt x => revealSpkB (keyIndKFuelsOfBudget S b).kOn bSt x)
    (fun {Γ₁ Γ₂ Δ} _ _ bSt x => revealSpkB_unsup _ (Δ := Δ) bSt x) _ stL sh _ (u.val, j.val)
    ?_ (fun bSt x env hb hx => by
      rw [revealSpkB_eval_eq, hb, hx, kOn_eq_simBounds0,
        revealSpkB_min_eq _ _ _ (Nat.le_trans hBase.spks_le (hB 0)) (Nat.min_le_right _ _)]
      exact hPure); rfl

/-- `.corruptIK` step simulation for active 1-key `fgKeyInd1KeyGapDhKindAtomicProg`. -/
theorem fgKeyInd1KeyGapDhKindAtomicProg_hStep_corruptIK (S : Setup) (b : QueryBudget) :
    ∀ u, KeyIndStepSim S b (forgetGdh1KeyActiveK S b) (Gdh1KeyActiveSimInv S b)
      (gdh1KeyKindHandleC S b) (fgKeyInd1KeyGapDhActiveAtomicProg S b).handle
      (.corruptIK u) := by
  intro u
  refine fgStepSim_of_pure S b (.corruptIK u) rfl trivial fun c hB stL sh hBase => ?_
  obtain ⟨resp, bSt', hPure, hNI⟩ := corruptB_eval_pure (K := b.q_total)
    (.zero : Var [keyIndStateTy, .nat] keyIndStateTy)
    (.succ .zero : Var [keyIndStateTy, .nat] .nat)
    (.cons stL.1.1.2.1 (.cons (t := .nat) u.val .nil))
  refine ⟨resp, bSt', hNI,
    fun pa2 => gdhHandle2_eval_corrupt S b.q_total pa2 stL.1.1.2 u hPure, ?_⟩
  unfold gdh1KeyKindHandleC; dsimp only; rw [dispatchKeyIndQ_eval]
  refine liftSigDdhNoFgArm_gdhWrap_eval S _
    (fun bSt x => corruptB (keyIndKFuelsOfBudget S b).kOn bSt x)
    (fun {Γ₁ Γ₂ Δ} _ _ bSt x => corruptB_unsup _ (Δ := Δ) bSt x) _ stL sh _ u.val ?_
    (fun bSt x env hb hx => by
      rw [corruptB_eval_eq, hb, hx, kOn_eq_simBounds0,
        corruptB_min_eq _ _ _ (Nat.le_trans hBase.prin_le (hB 0)) (Nat.min_le_right _ _)]
      exact hPure); rfl

/-- `.testSession` step simulation for active 1-key `fgKeyInd1KeyGapDhKindAtomicProg`. -/
theorem fgKeyInd1KeyGapDhKindAtomicProg_hStep_testSession (S : Setup) (b : QueryBudget) :
    ∀ sid, KeyIndStepSim S b (forgetGdh1KeyActiveK S b) (Gdh1KeyActiveSimInv S b)
      (gdh1KeyKindHandleC S b) (fgKeyInd1KeyGapDhActiveAtomicProg S b).handle
      (.testSession sid) := by
  intro sid
  refine fgStepSim_of_pure S b (.testSession sid) rfl trivial fun c hB stL sh hBase => ?_
  obtain ⟨resp, bSt', hPure, hNI⟩ := testB_eval_pure (K := b.q_total)
    (.zero : Var [keyIndStateTy, sidT] keyIndStateTy)
    (.succ .zero : Var [keyIndStateTy, sidT] sidT)
    (.cons stL.1.1.2.1 (.cons (sessionIdToVal sid) .nil))
  refine ⟨resp, bSt', hNI,
    fun pa2 => gdhHandle2_eval_test S b.q_total pa2 stL.1.1.2 sid hPure, ?_⟩
  unfold gdh1KeyKindHandleC; dsimp only; rw [dispatchKeyIndQ_eval]
  exact liftSigDdhNoFgArm_gdhWrap_eval S _
    (fun bSt x => testB (keyIndKFuelsOfBudget S b).kOn bSt x)
    (fun {Γ₁ Γ₂ Δ} _ _ bSt x => testB_unsup _ (Δ := Δ) bSt x) _ stL sh _ (sessionIdToVal sid)
    (finSidToNatExpr_sidV S sid _) fun bSt x env hb hx => by
      rw [testB_eval_eq, hb, hx, kOn_eq_simBounds0,
        testB_min_eq _ _ _ hBase (hB 0) (Nat.min_le_right _ _)]
      exact hPure

/-- `.revealDhSecrets` step simulation for active 1-key `fgKeyInd1KeyGapDhKindAtomicProg`. -/
theorem fgKeyInd1KeyGapDhKindAtomicProg_hStep_revealDhSecrets (S : Setup) (b : QueryBudget) :
    KeyIndStepSim S b (forgetGdh1KeyActiveK S b) (Gdh1KeyActiveSimInv S b)
      (gdh1KeyKindHandleC S b) (fgKeyInd1KeyGapDhActiveAtomicProg S b).handle
      .revealDhSecrets := by
  intro c stK _ _ hInv
  rw [gdh1KeyKindHandleC_eval_revDh]
  refine ⟨?_, ?_⟩
  · rcases stK with ⟨stA, sh⟩
    set stL := projVal gdh1KeyActiveStateTy stA
    have hStA : stA = embedVal gdh1KeyActiveStateTy stL :=
      (embedVal_projVal gdh1KeyActiveStateTy stA).symm
    rw [hStA, forgetGdh1KeyActiveK_embedVal]
    refine Eq.trans ?_ (gdhActiveAtomic_handle_eval S b (fixGdhLeg S b stL) .revealDhSecrets).symm
    rw [gdh1KeyActiveHandle_eval_revDh]; rfl
  · simp only [support_pure, Set.mem_singleton_iff, forall_eq]
    exact
      { sim_inv := GdhSimInv.bump_online_unchanged hInv.sim_inv rfl
        sendOpkCnt_le := by
          rw [bumpPred_online_0 (S := S) rfl]
          exact Nat.le_succ_of_le hInv.sendOpkCnt_le }

/-- `.revealSessionKey` step simulation for active 1-key `fgKeyInd1KeyGapDhKindAtomicProg`. -/
theorem fgKeyInd1KeyGapDhKindAtomicProg_hStep_revealSessionKey (S : Setup) (b : QueryBudget) :
    ∀ sid, KeyIndStepSim S b (forgetGdh1KeyActiveK S b) (Gdh1KeyActiveSimInv S b)
      (gdh1KeyKindHandleC S b) (fgKeyInd1KeyGapDhActiveAtomicProg S b).handle
      (.revealSessionKey sid) := by
  intro sid
  refine fgStepSim_of_pure S b (.revealSessionKey sid) rfl trivial fun c hB stL sh hBase => ?_
  obtain ⟨resp, bSt', hPure, hNI⟩ := revealB_eval_pure (K := b.q_total)
    (.zero : Var [keyIndStateTy, sidT] keyIndStateTy)
    (.succ .zero : Var [keyIndStateTy, sidT] sidT)
    (.cons stL.1.1.2.1 (.cons (sessionIdToVal sid) .nil))
  refine ⟨resp, bSt', hNI,
    fun pa2 => gdhHandle2_eval_reveal S b.q_total pa2 stL.1.1.2 sid hPure, ?_⟩
  unfold gdh1KeyKindHandleC; dsimp only; rw [dispatchKeyIndQ_eval]
  exact liftSigDdhNoFgArm_gdhWrap_eval S _
    (fun bSt x => revealB (keyIndKFuelsOfBudget S b).kOn bSt x)
    (fun {Γ₁ Γ₂ Δ} _ _ bSt x => revealB_unsup _ (Δ := Δ) bSt x) _ stL sh _ (sessionIdToVal sid)
    (finSidToNatExpr_sidV S sid _) fun bSt x env hb hx => by
      rw [revealB_eval_eq, hb, hx, kOn_eq_simBounds0,
        revealB_min_eq _ _ _ hBase (hB 0) (Nat.min_le_right _ _)]
      exact hPure

/-- `.revealSpkSk` step simulation for active 1-key `fgKeyInd1KeyGapDhKindAtomicProg`. -/
theorem fgKeyInd1KeyGapDhKindAtomicProg_hStep_revealSpkSk (S : Setup) (b : QueryBudget) :
    ∀ u j, KeyIndStepSim S b (forgetGdh1KeyActiveK S b) (Gdh1KeyActiveSimInv S b)
      (gdh1KeyKindHandleC S b) (fgKeyInd1KeyGapDhActiveAtomicProg S b).handle
      (.revealSpkSk u j) := by
  intro u j
  refine fgStepSim_of_pure S b (.revealSpkSk u j) rfl trivial fun c hB stL sh hBase => ?_
  obtain ⟨resp, bSt', hPure, hNI⟩ := revealSpkB_eval_pure (K := b.q_total)
    (.zero : Var [keyIndStateTy, .prod .nat .nat] keyIndStateTy)
    (.succ .zero : Var [keyIndStateTy, .prod .nat .nat] (.prod .nat .nat))
    (.cons stL.1.1.2.1 (.cons (t := .prod .nat .nat) (u.val, j.val) .nil))
  refine ⟨resp, bSt', hNI,
    fun pa2 => gdhHandle2_eval_revealSpk S b.q_total pa2 stL.1.1.2 u j hPure, ?_⟩
  unfold gdh1KeyKindHandleC; dsimp only; rw [dispatchKeyIndQ_eval]
  refine liftSigDdhNoFgArm_gdhWrap_eval S _
    (fun bSt x => revealSpkB (keyIndKFuelsOfBudget S b).kOn bSt x)
    (fun {Γ₁ Γ₂ Δ} _ _ bSt x => revealSpkB_unsup _ (Δ := Δ) bSt x) _ stL sh _ (u.val, j.val)
    ?_ (fun bSt x env hb hx => by
      rw [revealSpkB_eval_eq, hb, hx, kOn_eq_simBounds0,
        revealSpkB_min_eq _ _ _ (Nat.le_trans hBase.spks_le (hB 0)) (Nat.min_le_right _ _)]
      exact hPure); rfl

end

end Computational.Proofs.SignalPqxdh.Security.ReductionDsl.KindSplit.KeyIndGapDhKSimMiscReveal
