/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Computational.Specifications.Pqxdh.Security.Headline
public import Computational.Specifications.Pqxdh.Security.CostedBudgets
public import Computational.Proofs.ReductionDsl.StepSimTwoStage -- proof-setup: allow-public-import
public import Computational.Proofs.SignalPqxdh.Delta.KeyInd1KeyActiveProgs -- proof-setup: allow-public-import
public import Computational.Proofs.SignalPqxdh.Delta.KindSplit.KeyInd1KeyKindProgs -- proof-setup: allow-public-import
public import Computational.Proofs.SignalPqxdh.Security.ReductionDsl.KindSplit.KeyIndCoreKSimBase -- proof-setup: allow-public-import
public import Computational.Proofs.SignalPqxdh.Security.ReductionDsl.KindSplit.KeyIndCoreKSimArms -- proof-setup: allow-public-import
import Computational.Proofs.SignalPqxdh.Security.ReductionDsl.KindSplit.KeyIndCoreKSimHelpers

/-!
# Session Arm Forgetful Simulation Lemmas

Proves forgetful simulation and `ShcrSimInv` / `ShcrPauseInv` preservation for the session-related
arms of `shcrKindHandlePostC true` and `shcrKindHandlePreC true` (`initiateOPK`, `initiateNoOPK`,
`acceptOPK`, `acceptNoOPK`, `testSession`, and `revealSessionKey`).
-/

public section

set_option autoImplicit false

namespace Computational.Proofs.SignalPqxdh.Security.ReductionDsl.KindSplit.KeyIndCoreKSimArmsSess

open OracleSpec OracleComp
open _root_.SignalPqxdh (
  Setup QueryBudget KeyIndQuery keyIndSpec isKeyIndOnlineQuery isKeyIndRoQuery
)
open _root_.ReductionDsl (
  Ty Var Expr Comp Env pqAtomicSig pqAtomicOps pqPrimIface pqKeyIndCodec
  PB bundleT bundleV hdrT hdrV sidT sidV
)
open _root_.SignalPqxdh.LegacyCosted (pqSig pqxdhOps)
open _root_.Computational.Proofs.SignalPqxdh.AtomicLift (
  embedTy embedVal projVal embedEnv mapComp compRename
  embedVal_projVal projVal_embedVal mapComp_eval compRename_eval
  tlPrimKeyInd finSidToNatExpr
)
open _root_.Computational.Proofs.SignalPqxdh.Security.ReductionDsl.SplitRo.AvlRoTableDefs (aop)
open _root_.Computational.Proofs.ReductionDsl.StepSim (bumpPred)
open _root_.Computational.Proofs.ReductionDsl.StepSimTwoStage (forgetPreOut)
open _root_.SignalPqxdh.Security.ReductionDsl.KeyInd (
  Ext PT RS SCS accQTy bindV buIkB buOpkB buPqspkB buPqspkId buSpkB buSpkId caseOptV
  checkSigsC corruptB eAny eFind eMap eqU32 findHonestC freshE
  genOpkB genSpkB hdEkAPk hdIkAPk hdKemCt hdOpkId hdPqspkId hdSpkId
  initGuardE initPrin1KeyB initQTy initSidE isNoneRespE isSomeE keyIndLoopBound
  keyIndStateTy koskSenderOkC kyberCheckE lenB letV nat2Eq nat3Eq natEq oeConsumed oeOpkPk oeOpkSk
  oeUpd onBase optU32Eq pauseTy peIkAPk peSecIKA0 peSecIKAsign
  preCheckC principalEntryTy qHdr qJ qK qKJO qKemDecaps qKemEncaps qO qSigSign qX25519 qX25519Base
  rAccFresh rBundle rDrKey rNone rPk rSpkSk reMk recordRespC registerB
  revealB revealDhB revealSpkB roB rs sBytes32 sRandom64 sbMk sbPqspkPk
  sbPqspkSk sbSpkPk sbSpkSk scBase scChosen scCnt scIR scRR scSIdx scTB scTPk scTSk scUpd seMk
  seUpd shcrAcceptB shcrFinE shcrInitiateC shcrStTy spkBundleEntryTy
  stAdv stKyb stOpks stPrin stResps stRo stSess stSpks stUpd stUsedN stUsedO testB tryPauseC u32OfNat v
  acceptKeysC acceptNoOpkB acceptOpkB buildSecretsE hkdfOrRoC initFinishC pauseCheckC
)
open _root_.Computational.Proofs.SignalPqxdh.Delta.KeyInd1KeyActiveProgs (
  shcr1KeyActivePostC shcr1KeyActivePreC shcrActiveGenSpkB shcrActivePostTailC
)
open _root_.Computational.Proofs.SignalPqxdh.Security.ReductionDsl.KindSplit.KeyIndCoreK (
  accPayToNatE atomicRNoneE coreAcceptPreRoC finPairToNatE finTripleToNatE
  initFinishPostRoC initFinishPreRoC initPayToNatE keyIndCoreFuels roAvlTy roListLegacyTy roShadowQueryC
  runAt2 runAt3 runAt4 runAt5 shcrAccArmPostK shcrAccMidTy shcrAcceptPostRoC shcrAcceptPreRoC
  shcrActiveGenSpkLeg shcrCorruptLeg shcrGenOpkLeg shcrInitArmPostK shcrInitArmPreK shcrInitMidTy
  shcrInitPrin1KeyLeg shcrInitiatePostRoC shcrInitiatePreRoC shcrKindStTy shcrLiftLegArmK
  shcrRegKeyLeg shcrRevDhLeg shcrRevSessLeg shcrRevSpkLeg shcrRoArmK shcrRoListAtomicE
  shcrSetRoRespC shcrTestLeg wkTop3
)
open _root_.Computational.Proofs.SignalPqxdh.Security.ReductionDsl.KindSplit.KeyIndCoreKSimBase (
  BaseOnlineLenInv CoreInv RoCacheAvlInv ShcrPauseInv ShcrSimInv beq_fixSent_of_le_mOn
  checkSigsC_min_eq corruptB_min_eq findHonestC_min_eq fixSent forgetShcrKindActive
  genOpkB_min_eq initPrin1KeyB_min_eq keyIndSimBounds keyIndSimPred
  koskSenderOkC_min_eq kyberCheckE_min_eq preCheckC_min_eq recordRespC_min_eq
  revealB_min_eq revealDhB_min_eq revealSpkB_min_eq roShadowQueryC_eval_sim runAt2_eval runAt3_eval
  runAt4_eval runAt5_eval shcrActiveGenSpkLeg_min_eq stAdvList stKybList stOpksList
  stPrinList stRespsList stRoList stSessList stSpksList stUsedNList stUsedOList testB_min_eq
)
open _root_.Computational.Proofs.SignalPqxdh.Security.ReductionDsl.KindSplit.KeyIndCoreKSimHelpers (
  eAny_eq_of_le eFind_eq_of_le eMap_eq_of_le embedVal_roList_eq fixShcrLegacySent
  forgetShcrKindActive_eq_embed hkdfOrRoC_eval_congr hkdfOrRoC_unsup initFinishC_true_eq_split
  initFinishPostRoC_fuel_eq initFinishPostRoC_mem_support
  ro_bounds_of_le shcrAcceptPostRoC_unsup shcrAcceptPreRoC_unsup shcrActiveGenSpkLeg_unsup
  shcrCorruptLeg_unsup shcrGenOpkLeg_unsup shcrInitPrin1KeyLeg_unsup shcrInitiatePostRoC_fixSent_comm
  shcrInitiatePostRoC_unsup shcrInitiatePreRoC_unsup shcrLiftLegArmK_eval_eq
  shcrLiftLegArmK_map_forget shcrRegKeyLeg_unsup shcrRevDhLeg_unsup shcrRevSessLeg_unsup
  shcrRevSpkLeg_unsup shcrRoListAtomicE_eval shcrSetRoRespC_unsup shcrTestLeg_unsup
  tryPauseC_unsup v_eval_cons v_zero_eval
)
open _root_.Computational.Proofs.SignalPqxdh.Security.ReductionDsl.KindSplit.KeyIndCoreKSimArms (
  BaseOnlineLenInv.mono_online activePostEval activePreEval bumpPred_online bumpPred_ro
  shcrOnBaseArm_sim
)

private theorem online_fuel_bounds (S : Setup) (b : QueryBudget) (c : Fin 3 → ℕ)
    {t : KeyIndQuery S} (hOn : isKeyIndOnlineQuery (.inr t) = true)
    (hBound : ∀ j, bumpPred (keyIndSimPred S) c t j ≤ keyIndSimBounds b j) :
    c 0 + 1 ≤ (keyIndCoreFuels S b).M_on ∧ (keyIndCoreFuels S b).M_on ≤ keyIndLoopBound b := by
  obtain ⟨h0, _, _⟩ := bumpPred_online S c hOn
  have hb0 := hBound 0
  rw [h0] at hb0
  simp only [keyIndSimBounds, keyIndCoreFuels, keyIndLoopBound] at hb0 ⊢
  omega

private theorem le_bounds_of_bump (S : Setup) (b : QueryBudget) {c : Fin 3 → ℕ}
    {t : KeyIndQuery S}
    (hBound : ∀ j, bumpPred (keyIndSimPred S) c t j ≤ keyIndSimBounds b j) :
    ∀ j, c j ≤ keyIndSimBounds b j := by
  intro j
  exact Nat.le_trans (by simp [bumpPred]) (hBound j)

private def ren2Var {A B : PT} {Γ₁ Γ₂ Δ : List PT}
    (aV : Var Γ₁ A) (bV : Var Γ₂ B) [Ext Γ₁ Δ] [Ext Γ₂ Δ] :
    ∀ {τ}, Var [A, B] τ → Var Δ τ
  | _, .zero => Ext.wk aV
  | _, .succ .zero => Ext.wk bV

private theorem ren2Var_env_get {A B : PT} {Γ₁ Γ₂ Δ : List PT}
    (aV : Var Γ₁ A) (bV : Var Γ₂ B) [Ext Γ₁ Δ] [Ext Γ₂ Δ] (env : Env Δ) :
    ∀ {τ} (x : Var [A, B] τ),
      env.get (ren2Var (Δ := Δ) aV bV x) =
        (Env.cons ((v aV).eval env) (.cons ((v bV).eval env) .nil)).get x
  | _, .zero => rfl
  | _, .succ .zero => rfl

private theorem initPayToNatE_v0_eval (S : Setup) (N_s : ℕ) {B C : Ty pqAtomicSig}
    (u : Fin S.N_id) (i : Fin N_s) (bu : _root_.SignalPqxdh.PreKeyBundleInput)
    (bVal : B.denote) (cVal : C.denote) :
    (initPayToNatE N_s S
      (Γ := [.prod (.base (.fin S.N_id)) (.prod (.base (.fin N_s)) (bundleT (ℓ := 0) (Pt := Empty))), B, C])
      .v0).eval (.cons (u, (i, bundleV bu)) (.cons bVal (.cons cVal .nil))) =
    embedVal initQTy (u.val, (i.val, _root_.SignalPqxdh.LegacyCosted.bundleV bu)) := by
  rcases bu with ⟨ikB, spkId, spkB, spkSig, _ | ⟨opkId, opkPk⟩, pqspkId, pqspkB, pqspkSig⟩ <;> rfl

private theorem shcrInitiateC_eval_congr (S : Setup) (K : ℕ) (opk : Bool) {Γ₁ Γ₂ Δ : List PT}
    (s : Var Γ₁ shcrStTy) (x : Var Γ₂ initQTy)
    [Ext Γ₁ Δ] [Ext Γ₂ Δ] (env : Env Δ) :
    (shcrInitiateC S K opk (Δ := Δ) s x).eval env =
      (shcrInitiateC S K opk (Γ₁ := [shcrStTy, initQTy]) (Γ₂ := [shcrStTy, initQTy])
        (Δ := [shcrStTy, initQTy]) .zero (.succ .zero)).eval
        (.cons ((v s).eval env) (.cons ((v x).eval env) .nil)) := by
  have hRen : compRename (ren2Var (Δ := Δ) s x)
      (shcrInitiateC S K opk (Γ₁ := [shcrStTy, initQTy]) (Γ₂ := [shcrStTy, initQTy])
        (Δ := [shcrStTy, initQTy]) .zero (.succ .zero)) =
      shcrInitiateC S K opk (Δ := Δ) s x := by
    cases opk <;> rfl
  rw [← hRen]
  exact compRename_eval _ (ren2Var (Δ := Δ) s x) _ env (ren2Var_env_get s x env)

private def ren9Var {T₁ T₂ T₃ T₄ T₅ T₆ T₇ T₈ T₉ : PT}
    {Γ₁ Γ₂ Γ₃ Γ₄ Γ₅ Γ₆ Γ₇ Γ₈ Γ₉ Δ : List PT}
    (v₁ : Var Γ₁ T₁) (v₂ : Var Γ₂ T₂) (v₃ : Var Γ₃ T₃) (v₄ : Var Γ₄ T₄) (v₅ : Var Γ₅ T₅)
    (v₆ : Var Γ₆ T₆) (v₇ : Var Γ₇ T₇) (v₈ : Var Γ₈ T₈) (v₉ : Var Γ₉ T₉)
    [Ext Γ₁ Δ] [Ext Γ₂ Δ] [Ext Γ₃ Δ] [Ext Γ₄ Δ] [Ext Γ₅ Δ]
    [Ext Γ₆ Δ] [Ext Γ₇ Δ] [Ext Γ₈ Δ] [Ext Γ₉ Δ] :
    ∀ {τ}, Var [T₉, T₈, T₇, T₆, T₅, T₄, T₃, T₂, T₁] τ → Var Δ τ
  | _, .zero => Ext.wk v₉
  | _, .succ .zero => Ext.wk v₈
  | _, .succ (.succ .zero) => Ext.wk v₇
  | _, .succ (.succ (.succ .zero)) => Ext.wk v₆
  | _, .succ (.succ (.succ (.succ .zero))) => Ext.wk v₅
  | _, .succ (.succ (.succ (.succ (.succ .zero)))) => Ext.wk v₄
  | _, .succ (.succ (.succ (.succ (.succ (.succ .zero))))) => Ext.wk v₃
  | _, .succ (.succ (.succ (.succ (.succ (.succ (.succ .zero)))))) => Ext.wk v₂
  | _, .succ (.succ (.succ (.succ (.succ (.succ (.succ (.succ .zero))))))) => Ext.wk v₁

private theorem ren9Var_env_get {T₁ T₂ T₃ T₄ T₅ T₆ T₇ T₈ T₉ : PT}
    {Γ₁ Γ₂ Γ₃ Γ₄ Γ₅ Γ₆ Γ₇ Γ₈ Γ₉ Δ : List PT}
    (v₁ : Var Γ₁ T₁) (v₂ : Var Γ₂ T₂) (v₃ : Var Γ₃ T₃) (v₄ : Var Γ₄ T₄) (v₅ : Var Γ₅ T₅)
    (v₆ : Var Γ₆ T₆) (v₇ : Var Γ₇ T₇) (v₈ : Var Γ₈ T₈) (v₉ : Var Γ₉ T₉)
    [Ext Γ₁ Δ] [Ext Γ₂ Δ] [Ext Γ₃ Δ] [Ext Γ₄ Δ] [Ext Γ₅ Δ]
    [Ext Γ₆ Δ] [Ext Γ₇ Δ] [Ext Γ₈ Δ] [Ext Γ₉ Δ] (env : Env Δ) :
    ∀ {τ} (x : Var [T₉, T₈, T₇, T₆, T₅, T₄, T₃, T₂, T₁] τ),
      env.get (ren9Var (Δ := Δ) v₁ v₂ v₃ v₄ v₅ v₆ v₇ v₈ v₉ x) =
        (Env.cons ((v v₉).eval env) (.cons ((v v₈).eval env) (.cons ((v v₇).eval env)
          (.cons ((v v₆).eval env) (.cons ((v v₅).eval env) (.cons ((v v₄).eval env)
            (.cons ((v v₃).eval env) (.cons ((v v₂).eval env) (.cons ((v v₁).eval env) .nil))))))))).get x
  | _, .zero => rfl
  | _, .succ .zero => rfl
  | _, .succ (.succ .zero) => rfl
  | _, .succ (.succ (.succ .zero)) => rfl
  | _, .succ (.succ (.succ (.succ .zero))) => rfl
  | _, .succ (.succ (.succ (.succ (.succ .zero)))) => rfl
  | _, .succ (.succ (.succ (.succ (.succ (.succ .zero))))) => rfl
  | _, .succ (.succ (.succ (.succ (.succ (.succ (.succ .zero)))))) => rfl
  | _, .succ (.succ (.succ (.succ (.succ (.succ (.succ (.succ .zero))))))) => rfl

private theorem letV_eval_step {Γ : List PT} {σ τ : PT} (e : Expr pqxdhOps Γ σ)
    (k : Var (σ :: Γ) σ → Comp pqxdhOps _root_.SignalPqxdh.LegacyCosted.pqPrimIface (σ :: Γ) τ)
    (env : Env Γ) :
    (letV e k).eval env = (k .zero).eval (.cons (e.eval env) env) := by
  simp [letV, Comp.eval]

private abbrev initPostCtx1 : List PT := [keyIndStateTy]
private abbrev initPostCtx2 : List PT := _root_.SignalPqxdh.LegacyCosted.sidT :: initPostCtx1
private abbrev initPostCtx3 : List PT := _root_.SignalPqxdh.LegacyCosted.bundleT :: initPostCtx2
private abbrev initPostCtx4 : List PT := .prod .nat principalEntryTy :: initPostCtx3
private abbrev initPostCtx5 : List PT := _root_.SignalPqxdh.LegacyCosted.B 32 :: initPostCtx4
private abbrev initPostCtx6 : List PT :=
  .prod (_root_.SignalPqxdh.LegacyCosted.B 32) (_root_.SignalPqxdh.LegacyCosted.B 1568) :: initPostCtx5
private abbrev initPostCtx7 : List PT := _root_.SignalPqxdh.LegacyCosted.B 32 :: initPostCtx6
private abbrev initPostCtx8 : List PT := _root_.SignalPqxdh.LegacyCosted.drKeyT :: initPostCtx7
private abbrev initPostCtx9 : List PT := roListLegacyTy :: initPostCtx8

private theorem initFinishPostRoC_eval_congr (S : Setup) (K : ℕ)
    {Γ₁ Γ₂ Γ₃ Γ₄ Γ₅ Γ₆ Γ₇ Γ₈ Γ₉ Δ : List PT}
    (st : Var Γ₁ keyIndStateTy) (sid : Var Γ₂ _root_.SignalPqxdh.LegacyCosted.sidT)
    (bu : Var Γ₃ _root_.SignalPqxdh.LegacyCosted.bundleT)
    (uE : Var Γ₄ (.prod .nat principalEntryTy))
    (ekSk : Var Γ₅ (_root_.SignalPqxdh.LegacyCosted.B 32))
    (sc : Var Γ₆ (.prod (_root_.SignalPqxdh.LegacyCosted.B 32) (_root_.SignalPqxdh.LegacyCosted.B 1568)))
    (ekPk : Var Γ₇ (_root_.SignalPqxdh.LegacyCosted.B 32))
    (dk : Var Γ₈ _root_.SignalPqxdh.LegacyCosted.drKeyT) (roNew : Var Γ₉ roListLegacyTy)
    [Ext Γ₁ Δ] [Ext Γ₂ Δ] [Ext Γ₃ Δ] [Ext Γ₄ Δ] [Ext Γ₅ Δ]
    [Ext Γ₆ Δ] [Ext Γ₇ Δ] [Ext Γ₈ Δ] [Ext Γ₉ Δ] (env : Env Δ) :
    (initFinishPostRoC (Δ := Δ) S K st sid bu uE ekSk sc ekPk dk roNew).eval env =
      (initFinishPostRoC S K
        (Γ₁ := initPostCtx1) (Γ₂ := initPostCtx2) (Γ₃ := initPostCtx3)
        (Γ₄ := initPostCtx4) (Γ₅ := initPostCtx5) (Γ₆ := initPostCtx6)
        (Γ₇ := initPostCtx7) (Γ₈ := initPostCtx8) (Γ₉ := initPostCtx9) (Δ := initPostCtx9)
        .zero .zero .zero .zero .zero .zero .zero .zero .zero).eval
        (.cons ((v roNew).eval env) (.cons ((v dk).eval env) (.cons ((v ekPk).eval env)
          (.cons ((v sc).eval env) (.cons ((v ekSk).eval env) (.cons ((v uE).eval env)
            (.cons ((v bu).eval env) (.cons ((v sid).eval env) (.cons ((v st).eval env) .nil))))))))) := by
  let c := initFinishPostRoC S K
    (Γ₁ := initPostCtx1) (Γ₂ := initPostCtx2) (Γ₃ := initPostCtx3)
    (Γ₄ := initPostCtx4) (Γ₅ := initPostCtx5) (Γ₆ := initPostCtx6)
    (Γ₇ := initPostCtx7) (Γ₈ := initPostCtx8) (Γ₉ := initPostCtx9) (Δ := initPostCtx9)
    .zero .zero .zero .zero .zero .zero .zero .zero .zero
  have hRen : compRename (ren9Var (Δ := Δ) st sid bu uE ekSk sc ekPk dk roNew) c =
      initFinishPostRoC (Δ := Δ) S K st sid bu uE ekSk sc ekPk dk roNew := rfl
  rw [← hRen]
  exact compRename_eval c (ren9Var (Δ := Δ) st sid bu uE ekSk sc ekPk dk roNew) _ env
    (ren9Var_env_get st sid bu uE ekSk sc ekPk dk roNew env)

private def ren4Var {A B C D : PT} {Γ₁ Γ₂ Γ₃ Γ₄ Δ : List PT}
    (aV : Var Γ₁ A) (bV : Var Γ₂ B) (cV : Var Γ₃ C) (dV : Var Γ₄ D)
    [Ext Γ₁ Δ] [Ext Γ₂ Δ] [Ext Γ₃ Δ] [Ext Γ₄ Δ] :
    ∀ {τ}, Var [A, B, C, D] τ → Var Δ τ
  | _, .zero => Ext.wk aV
  | _, .succ .zero => Ext.wk bV
  | _, .succ (.succ .zero) => Ext.wk cV
  | _, .succ (.succ (.succ .zero)) => Ext.wk dV

private theorem ren4Var_env_get {A B C D : PT} {Γ₁ Γ₂ Γ₃ Γ₄ Δ : List PT}
    (aV : Var Γ₁ A) (bV : Var Γ₂ B) (cV : Var Γ₃ C) (dV : Var Γ₄ D)
    [Ext Γ₁ Δ] [Ext Γ₂ Δ] [Ext Γ₃ Δ] [Ext Γ₄ Δ] (env : Env Δ) :
    ∀ {τ} (x : Var [A, B, C, D] τ),
      env.get (ren4Var (Δ := Δ) aV bV cV dV x) =
        (Env.cons ((v aV).eval env) (.cons ((v bV).eval env)
          (.cons ((v cV).eval env) (.cons ((v dV).eval env) .nil)))).get x
  | _, .zero => rfl
  | _, .succ .zero => rfl
  | _, .succ (.succ .zero) => rfl
  | _, .succ (.succ (.succ .zero)) => rfl

private abbrev preCheckCtx : List PT :=
  [keyIndStateTy, _root_.SignalPqxdh.LegacyCosted.sidT, .nat, _root_.SignalPqxdh.LegacyCosted.bundleT]

private theorem preCheckC_eval_congr (S : Setup) (K : ℕ) {Γ₁ Γ₂ Γ₃ Γ₄ Δ : List PT}
    (st : Var Γ₁ keyIndStateTy) (sid : Var Γ₂ _root_.SignalPqxdh.LegacyCosted.sidT)
    (u : Var Γ₃ .nat) (bu : Var Γ₄ _root_.SignalPqxdh.LegacyCosted.bundleT)
    [Ext Γ₁ Δ] [Ext Γ₂ Δ] [Ext Γ₃ Δ] [Ext Γ₄ Δ] (env : Env Δ) :
    (preCheckC S K (Δ := Δ) st sid u bu).eval env =
      (preCheckC S K (Γ₁ := preCheckCtx) (Γ₂ := preCheckCtx) (Γ₃ := preCheckCtx) (Γ₄ := preCheckCtx) (Δ := preCheckCtx)
        .zero (.succ .zero) (.succ (.succ .zero)) (.succ (.succ (.succ .zero)))).eval
        (.cons ((v st).eval env) (.cons ((v sid).eval env)
          (.cons ((v u).eval env) (.cons ((v bu).eval env) .nil)))) := by
  let c := preCheckC S K (Γ₁ := preCheckCtx) (Γ₂ := preCheckCtx) (Γ₃ := preCheckCtx) (Γ₄ := preCheckCtx) (Δ := preCheckCtx)
    .zero (.succ .zero) (.succ (.succ .zero)) (.succ (.succ (.succ .zero)))
  have hRen : compRename (ren4Var (Δ := Δ) st sid u bu) c = preCheckC S K (Δ := Δ) st sid u bu := rfl
  rw [← hRen]
  exact compRename_eval c (ren4Var (Δ := Δ) st sid u bu) _ env (ren4Var_env_get st sid u bu env)

private abbrev checkSigsCtx : List PT := [keyIndStateTy, _root_.SignalPqxdh.LegacyCosted.bundleT]

private theorem checkSigsC_eval_congr (S : Setup) (K : ℕ) {Γ₁ Γ₂ Δ : List PT}
    (st : Var Γ₁ keyIndStateTy) (bu : Var Γ₂ _root_.SignalPqxdh.LegacyCosted.bundleT)
    [Ext Γ₁ Δ] [Ext Γ₂ Δ] (env : Env Δ) :
    (checkSigsC S K (Δ := Δ) st bu).eval env =
      (checkSigsC S K (Γ₁ := checkSigsCtx) (Γ₂ := checkSigsCtx) (Δ := checkSigsCtx) .zero (.succ .zero)).eval
        (.cons ((v st).eval env) (.cons ((v bu).eval env) .nil)) := by
  let c := checkSigsC S K (Γ₁ := checkSigsCtx) (Γ₂ := checkSigsCtx) (Δ := checkSigsCtx) .zero (.succ .zero)
  have hRen : compRename (ren2Var (Δ := Δ) st bu) c = checkSigsC S K (Δ := Δ) st bu := rfl
  rw [← hRen]
  exact compRename_eval c (ren2Var (Δ := Δ) st bu) _ env (ren2Var_env_get st bu env)

private abbrev initPreCtx : List PT :=
  [_root_.SignalPqxdh.LegacyCosted.bundleT, .prod .nat principalEntryTy,
   _root_.SignalPqxdh.LegacyCosted.B 32,
   .prod (_root_.SignalPqxdh.LegacyCosted.B 32) (_root_.SignalPqxdh.LegacyCosted.B 1568)]

private theorem initFinishPreRoC_eval_congr {Γ₁ Γ₂ Γ₃ Γ₄ Δ : List PT}
    (bu : Var Γ₁ _root_.SignalPqxdh.LegacyCosted.bundleT)
    (uE : Var Γ₂ (.prod .nat principalEntryTy))
    (ekSk : Var Γ₃ (_root_.SignalPqxdh.LegacyCosted.B 32))
    (sc : Var Γ₄ (.prod (_root_.SignalPqxdh.LegacyCosted.B 32) (_root_.SignalPqxdh.LegacyCosted.B 1568)))
    [Ext Γ₁ Δ] [Ext Γ₂ Δ] [Ext Γ₃ Δ] [Ext Γ₄ Δ] (env : Env Δ) :
    (initFinishPreRoC (Δ := Δ) bu uE ekSk sc).eval env =
      (initFinishPreRoC (Γ₁ := initPreCtx) (Γ₂ := initPreCtx) (Γ₃ := initPreCtx) (Γ₄ := initPreCtx) (Δ := initPreCtx)
        .zero (.succ .zero) (.succ (.succ .zero)) (.succ (.succ (.succ .zero)))).eval
        (.cons ((v bu).eval env) (.cons ((v uE).eval env)
          (.cons ((v ekSk).eval env) (.cons ((v sc).eval env) .nil)))) := by
  let c := initFinishPreRoC (Γ₁ := initPreCtx) (Γ₂ := initPreCtx) (Γ₃ := initPreCtx) (Γ₄ := initPreCtx) (Δ := initPreCtx)
    .zero (.succ .zero) (.succ (.succ .zero)) (.succ (.succ (.succ .zero)))
  have hRen : compRename (ren4Var (Δ := Δ) bu uE ekSk sc) c = initFinishPreRoC (Δ := Δ) bu uE ekSk sc := rfl
  rw [← hRen]
  exact compRename_eval c (ren4Var (Δ := Δ) bu uE ekSk sc) _ env (ren4Var_env_get bu uE ekSk sc env)

private theorem shcrInitiatePreRoC_fuel_eq (S : Setup) {K₁ K₂ : ℕ} {c : Fin 3 → ℕ}
    (opk : Bool) (sL : shcrStTy.denote) (p : initQTy.denote)
    (hInv : BaseOnlineLenInv c sL.1) (hc0 : c 0 ≤ K₁) (hLe : K₁ ≤ K₂) :
    (shcrInitiatePreRoC S K₁ opk).eval (.cons sL (.cons p .nil)) =
      (shcrInitiatePreRoC S K₂ opk).eval (.cons sL (.cons p .nil)) := by
  have hPrin : (stPrinList sL.1).length ≤ K₁ := Nat.le_trans hInv.prin_le hc0
  simp only [shcrInitiatePreRoC, letV, bindV, caseOptV, Comp.eval, pure_bind]
  split_ifs with hG
  · rfl
  · rw [preCheckC_min_eq S _ _ _ _ _ (by simpa [scBase, Expr.eval, v_eval_cons, v_zero_eval, v, Ext.wk, Env.get] using hInv) hc0 hLe]
    congr 1; funext pc
    cases pc with
    | none => simp [Expr.eval, v_zero_eval]
    | some uE =>
      simp only [Expr.eval, v_zero_eval]
      congr 1; funext ekSk
      congr 1; funext coins
      rw [checkSigsC_min_eq S _ _ _ (by simpa [scBase, Expr.eval, v_eval_cons, v_zero_eval, v, Ext.wk, Env.get] using hPrin) hLe]

private theorem shcrInitiatePreRoC_fixSent_comm (S : Setup) (b : QueryBudget) (K : ℕ)
    (opk : Bool) (sL : shcrStTy.denote) (p : initQTy.denote) :
    Sum.map (Prod.map id (fixShcrLegacySent S b)) id <$>
        (shcrInitiatePreRoC S K opk).eval (.cons sL (.cons p .nil)) =
      (shcrInitiatePreRoC S K opk).eval (.cons (fixShcrLegacySent S b sL) (.cons p .nil)) := by
  rcases sL with ⟨bSt, tb, tpk, tsk, cnt, ir, rr, sidx, ch⟩
  have hRNone : ∀ {Γ} (ρ : Env Γ), (rNone (Γ := Γ)).eval ρ = Sum.inl () := fun _ => rfl
  have hSB : ∀ {Γ₁ Γ₂} (ρ₁ : Env Γ₁) (ρ₂ : Env Γ₂),
      (sBytes32 (Γ := Γ₁)).eval ρ₁ = (sBytes32 (Γ := Γ₂)).eval ρ₂ := fun _ _ => rfl
  have hKem : ∀ {Γ₁ Γ₂} (e₁ : Expr pqxdhOps Γ₁ _) (e₂ : Expr pqxdhOps Γ₂ _)
      (ρ₁ : Env Γ₁) (ρ₂ : Env Γ₂),
      e₁.eval ρ₁ = e₂.eval ρ₂ → (qKemEncaps e₁).eval ρ₁ = (qKemEncaps e₂).eval ρ₂ :=
    fun _ _ _ _ h => congrArg (fun x => (qKemEncaps (Γ := [_]) (.var .zero)).eval (.cons x .nil)) h
  have hGuard :
      (initGuardE opk (.var (.succ .zero))).eval
        (.cons (t := shcrStTy) (bSt, tb, tpk, tsk, cnt, ir, rr, fixSent S b sidx, ch) (.cons p .nil)) =
      (initGuardE opk (.var (.succ .zero))).eval
        (.cons (t := shcrStTy) (bSt, tb, tpk, tsk, cnt, ir, rr, sidx, ch) (.cons p .nil)) := by
    cases opk <;> rfl
  have hSid : ∀ sidx' : ℕ,
      (initSidE opk (.var (.succ (.succ .zero)))).eval
        (.cons p.2.2 (.cons (t := shcrStTy) (bSt, tb, tpk, tsk, cnt, ir, rr, sidx', ch) (.cons p .nil))) =
      (initSidE opk (.var .zero)).eval (.cons p .nil) := by
    intro _; cases opk <;> rfl
  dsimp only [shcrInitiatePreRoC, fixShcrLegacySent]
  simp only [Comp.eval, map_eq_bind_pure_comp, Function.comp_def, hGuard, v, Ext.wk]
  by_cases hG : (initGuardE opk (.var (.succ .zero))).eval
      (.cons (t := shcrStTy) (bSt, tb, tpk, tsk, cnt, ir, rr, sidx, ch) (.cons p .nil)) = true
  · simp [hG, Expr.eval, hRNone, fixShcrLegacySent]
  · have hGf : (initGuardE opk (.var (.succ .zero))).eval
        (.cons (t := shcrStTy) (bSt, tb, tpk, tsk, cnt, ir, rr, sidx, ch) (.cons p .nil)) = false :=
      Bool.eq_false_iff.mpr hG
    simp only [hGf, Bool.false_eq_true, ↓reduceIte, letV_eval_step, bindV, caseOptV, Comp.eval,
      bind_assoc, scBase, Expr.eval, Env.get, hSid]
    rw [preCheckC_eval_congr S K, eq_comm, preCheckC_eval_congr S K, eq_comm]
    simp only [v, Ext.wk, Expr.eval, Env.get]
    refine congrArg₂ Bind.bind rfl (funext fun pc => ?_)
    cases pc with
    | none => simp [hRNone, fixShcrLegacySent]
    | some uE =>
      simp only [bind_assoc]
      refine congrArg₂ Bind.bind (hSB _ _) (funext fun ekSk => ?_)
      refine congrArg₂ Bind.bind (hSB _ _) (funext fun coins => ?_)
      rw [checkSigsC_eval_congr S K, eq_comm, checkSigsC_eval_congr S K, eq_comm]
      simp only [v, Ext.wk, Expr.eval, Env.get]
      refine congrArg₂ Bind.bind rfl (funext fun ok => ?_)
      cases ok with
      | false =>
        simp [hRNone, fixShcrLegacySent]
      | true =>
        simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte, bind_assoc]
        refine congrArg₂ Bind.bind (hKem _ _ _ _ (by simp only [Expr.eval, Env.get]))
          (funext fun enc => ?_)
        cases enc with
        | none =>
          simp [hRNone, fixShcrLegacySent]
        | some sc =>
          simp only [bind_assoc]
          rw [initFinishPreRoC_eval_congr, eq_comm, initFinishPreRoC_eval_congr, eq_comm]
          simp only [v, Ext.wk, Expr.eval, Env.get]
          refine congrArg₂ Bind.bind rfl (funext fun sp => ?_)
          simp

private theorem shcrInitiatePreRoC_inl_mem (S : Setup) (K : ℕ) (opk : Bool)
    (sL : shcrStTy.denote) (p : initQTy.denote) {rsOut : SCS.denote}
    (hMem : Sum.inl rsOut ∈ support ((shcrInitiatePreRoC S K opk).eval (.cons sL (.cons p .nil)))) :
    rsOut.2.1 = sL.1 ∧ rsOut.2.2.2.2.2.1 ≤ sL.2.2.2.2.1 + 1 ∧
    rsOut.2.2.2.2.2.2.1 = sL.2.2.2.2.2.1 ∧ rsOut.2.2.2.2.2.2.2.1 = sL.2.2.2.2.2.2.1 := by
  rcases sL with ⟨bSt, tb, tpk, tsk, cnt, ir, rr, sidx, ch⟩
  simp only [shcrInitiatePreRoC, letV, bindV, caseOptV, Comp.eval, pure_bind] at hMem
  split_ifs at hMem with hG
  · simp only [support_pure, Set.mem_singleton_iff, Sum.inl.injEq, Expr.eval, v_zero_eval] at hMem
    subst hMem; exact ⟨rfl, Nat.le_succ _, rfl, rfl⟩
  · simp only [mem_support_bind_iff] at hMem
    rcases hMem with ⟨pc, _, hMem⟩
    cases pc with
    | none =>
      simp only [support_pure, Set.mem_singleton_iff, Sum.inl.injEq,
        Expr.eval, v_eval_cons, v_zero_eval] at hMem
      subst hMem; exact ⟨rfl, Nat.le_succ _, rfl, rfl⟩
    | some uE =>
      simp only [Expr.eval, v_zero_eval, mem_support_bind_iff] at hMem
      rcases hMem with ⟨ekSk, _, coins, _, ok, _, hMem⟩
      cases ok with
      | false =>
        simp only [Bool.not_false, ↓reduceIte, support_pure, Set.mem_singleton_iff,
          Sum.inl.injEq, v_eval_cons, v_zero_eval] at hMem
        subst hMem; exact ⟨rfl, Nat.le_succ _, rfl, rfl⟩
      | true =>
        simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte,
          mem_support_bind_iff] at hMem
        rcases hMem with ⟨enc, _, hMem⟩
        cases enc with
        | none =>
          simp only [v_zero_eval, support_pure, Set.mem_singleton_iff, Sum.inl.injEq,
            v_eval_cons] at hMem
          subst hMem; exact ⟨rfl, Nat.le_refl _, rfl, rfl⟩
        | some sc =>
          simp only [mem_support_bind_iff, support_pure,
            Set.mem_singleton_iff] at hMem
          rcases hMem with ⟨_, _, hEq⟩
          exact nomatch hEq

private theorem shcrInitiatePostRoC_fuel_eq (S : Setup) {K₁ K₂ : ℕ} {c : Fin 3 → ℕ}
    (dk : _root_.SignalPqxdh.LegacyCosted.drKeyT.denote) (roNew : roListLegacyTy.denote)
    (mid : shcrInitMidTy.denote) (sL : shcrStTy.denote)
    (hInv : BaseOnlineLenInv c sL.1) (hc0 : c 0 ≤ K₁) (hLe : K₁ ≤ K₂) :
    (shcrInitiatePostRoC S K₁).eval (.cons dk (.cons roNew (.cons mid (.cons sL .nil)))) =
      (shcrInitiatePostRoC S K₂).eval (.cons dk (.cons roNew (.cons mid (.cons sL .nil)))) := by
  simp only [shcrInitiatePostRoC, letV, bindV, Comp.eval, pure_bind]
  rw [initFinishPostRoC_fuel_eq S _ _ _ _ _ _ _ _ _ _
    (by simpa [scBase, Expr.eval, v_eval_cons, v_zero_eval, v, Ext.wk, Env.get] using hInv) hc0 hLe]

private theorem shcrInitiatePostRoC_mem_support (S : Setup) (K : ℕ)
    (dk : _root_.SignalPqxdh.LegacyCosted.drKeyT.denote) (roNew : roListLegacyTy.denote)
    (mid : shcrInitMidTy.denote) (sL : shcrStTy.denote) {rsOut : SCS.denote}
    (hMem : rsOut ∈ support ((shcrInitiatePostRoC S K).eval
      (.cons dk (.cons roNew (.cons mid (.cons sL .nil)))))) :
    stPrinList rsOut.2.1 = stPrinList sL.1 ∧ stSpksList rsOut.2.1 = stSpksList sL.1 ∧
    stOpksList rsOut.2.1 = stOpksList sL.1 ∧
    (stSessList rsOut.2.1).length = (stSessList sL.1).length + 1 ∧
    stRespsList rsOut.2.1 = stRespsList sL.1 ∧ stUsedOList rsOut.2.1 = stUsedOList sL.1 ∧
    stUsedNList rsOut.2.1 = stUsedNList sL.1 ∧ stKybList rsOut.2.1 = stKybList sL.1 ∧
    stRoList rsOut.2.1 = roNew ∧ stAdvList rsOut.2.1 = stAdvList sL.1 ∧
    rsOut.2.2.2.2.2.1 = sL.2.2.2.2.1 + 1 ∧
    rsOut.2.2.2.2.2.2.1.length = sL.2.2.2.2.2.1.length + 1 ∧
    rsOut.2.2.2.2.2.2.2.1 = sL.2.2.2.2.2.2.1 := by
  rcases sL with ⟨bSt, tb, tpk, tsk, cnt, ir, rr, sidx, ch⟩
  simp only [shcrInitiatePostRoC, letV, bindV, Comp.eval, pure_bind,
    mem_support_bind_iff, support_pure, Set.mem_singleton_iff] at hMem
  rcases hMem with ⟨r, hrMem, rfl⟩
  obtain ⟨hP, hS, hO, hSe, hRe, hUO, hUN, hKy, hRo, hAd⟩ :=
    initFinishPostRoC_mem_support S K _ _ _ _ _ _ _ _ _ _ hrMem
  simp only [Expr.eval, v_eval_cons, v_zero_eval] at hP hS hO hSe hRe hUO hUN hKy hRo hAd
  dsimp only [shcrFinE, scUpd, scBase, scTB, scTPk, scTSk, scCnt, scIR, scRR, scSIdx, scChosen,
    Expr.eval, v_eval_cons, v_zero_eval]
  exact ⟨hP, hS, hO, hSe, hRe, hUO, hUN, hKy, hRo, hAd, rfl, rfl, rfl⟩

private theorem shcrInitiateC_eq_pre_ro_post (S : Setup) (K : ℕ) (opk : Bool)
    (sF : shcrStTy.denote) (p : initQTy.denote) :
    (shcrInitiateC S K opk (Γ₁ := [shcrStTy, initQTy]) (Γ₂ := [shcrStTy, initQTy])
      (Δ := [shcrStTy, initQTy]) .zero (.succ .zero)).eval (.cons sF (.cons p .nil)) =
    (shcrInitiatePreRoC S K opk).eval (.cons sF (.cons p .nil)) >>= fun pre =>
      match pre with
      | .inl rsOut => pure rsOut
      | .inr mid =>
          (hkdfOrRoC K true
            (Γ := [keyIndStateTy, _root_.SignalPqxdh.LegacyCosted.B 192])
            (Δ := [keyIndStateTy, _root_.SignalPqxdh.LegacyCosted.B 192])
            .zero (.var (.succ .zero))).eval (.cons sF.1 (.cons mid.1 .nil)) >>= fun dr =>
            (shcrInitiatePostRoC S K).eval (.cons dr.1 (.cons dr.2 (.cons mid (.cons sF .nil)))) := by
  simp only [shcrInitiateC, shcrInitiatePreRoC, letV, bindV, caseOptV, Comp.eval, pure_bind]
  split_ifs with hG
  · rfl
  · simp only [bind_assoc]
    refine congrArg₂ Bind.bind rfl (funext fun pc => ?_)
    cases pc with
    | none => simp [Expr.eval, v_zero_eval]
    | some uE =>
      simp only [Expr.eval, v_zero_eval, bind_assoc]
      refine congrArg₂ Bind.bind rfl (funext fun ekSk => ?_)
      refine congrArg₂ Bind.bind rfl (funext fun coins => ?_)
      refine congrArg₂ Bind.bind rfl (funext fun ok => ?_)
      cases ok with
      | false =>
        simp [pure_bind, Expr.eval, v_eval_cons, v_zero_eval]
      | true =>
        simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte, bind_assoc]
        refine congrArg₂ Bind.bind rfl (funext fun enc => ?_)
        cases enc with
        | none => simp [Expr.eval, v_eval_cons, v_zero_eval]
        | some sc =>
          simp only [bind_assoc]
          rw [initFinishC_true_eq_split S K]
          simp only [bind_assoc]
          refine congrArg₂ Bind.bind ?_ (funext fun sp => ?_)
          · rw [initFinishPreRoC_eval_congr, eq_comm, initFinishPreRoC_eval_congr]
          · simp only [pure_bind, v, Ext.wk, Expr.eval, Env.get]
            refine congrArg₂ Bind.bind ?_ (funext fun dr => ?_)
            · simp [Ext.wk, Expr.eval]
            · simp only [shcrInitiatePostRoC, letV, bindV, Comp.eval, pure_bind]
              refine congrArg₂ Bind.bind ?_ (funext fun r => ?_)
              · rw [eq_comm, initFinishPostRoC_eval_congr S K]
                simp [v, Ext.wk, Expr.eval]
              · simp [shcrFinE, scUpd, scTB, scTPk, scTSk, scCnt, scIR, scRR, scSIdx,
                  scChosen, v, Ext.wk, Expr.eval]

private theorem comp_bind_eval {A B : Ty pqAtomicSig} {Γ : List (Ty pqAtomicSig)}
    (m : Comp pqAtomicOps pqPrimIface Γ A)
    (k : Comp pqAtomicOps pqPrimIface (A :: Γ) B) (ρ : Env Γ) :
    (m.bind k).eval ρ = m.eval ρ >>= fun x => k.eval (.cons x ρ) := rfl

private theorem caseSum_v0_inl {A B R : Ty pqAtomicSig} {Γ : List (Ty pqAtomicSig)}
    (l : Comp pqAtomicOps pqPrimIface (A :: Ty.sum A B :: Γ) R)
    (r : Comp pqAtomicOps pqPrimIface (B :: Ty.sum A B :: Γ) R)
    (x : (Ty.sum A B).denote) (a : A.denote) (hx : x = .inl a) (ρ : Env Γ) :
    (Comp.caseSum .v0 l r).eval (.cons x ρ) = l.eval (.cons a (.cons x ρ)) := by
  subst hx; rfl

private theorem caseSum_v0_inr {A B R : Ty pqAtomicSig} {Γ : List (Ty pqAtomicSig)}
    (l : Comp pqAtomicOps pqPrimIface (A :: Ty.sum A B :: Γ) R)
    (r : Comp pqAtomicOps pqPrimIface (B :: Ty.sum A B :: Γ) R)
    (x : (Ty.sum A B).denote) (b : B.denote) (hx : x = .inr b) (ρ : Env Γ) :
    (Comp.caseSum .v0 l r).eval (.cons x ρ) = r.eval (.cons b (.cons x ρ)) := by
  subst hx; rfl

private theorem shcrInitArmPost_inv_gen (S : Setup) (b : QueryBudget) (c : Fin 3 → ℕ)
    (N_s : ℕ) (opk : Bool) (sK : shcrKindStTy.denote)
    (u : Fin S.N_id) (i : Fin N_s) (bu : _root_.SignalPqxdh.PreKeyBundleInput)
    (t : KeyIndQuery S) (hOn : isKeyIndOnlineQuery (.inr t) = true)
    (hInv : ShcrSimInv S b c sK)
    (hPreEval :
      let f := keyIndCoreFuels S b
      let env0 : Env (S := pqAtomicSig)
        [.prod (.base (.fin S.N_id)) (.prod (.base (.fin N_s)) (bundleT (ℓ := 0) (Pt := Empty))),
         shcrKindStTy, (pqKeyIndCodec S).Q] :=
        .cons (u, (i, bundleV bu)) (.cons sK (.cons ((pqKeyIndCodec S).qenc t) .nil))
      (runAt2 (.fst .v1) (initPayToNatE N_s S .v0)
        (mapComp tlPrimKeyInd (shcrInitiatePreRoC S f.M_on opk))).eval env0 =
      embedVal (.sum SCS shcrInitMidTy) <$>
        (shcrInitiatePreRoC S f.M_on opk).eval
          (.cons (projVal shcrStTy sK.1)
            (.cons (u.val, (i.val, _root_.SignalPqxdh.LegacyCosted.bundleV bu)) .nil)))
    (hMidMem : ∀ mid : shcrInitMidTy.denote,
      let f := keyIndCoreFuels S b
      let env0 : Env (S := pqAtomicSig)
        [.prod (.base (.fin S.N_id)) (.prod (.base (.fin N_s)) (bundleT (ℓ := 0) (Pt := Empty))),
         shcrKindStTy, (pqKeyIndCodec S).Q] :=
        .cons (u, (i, bundleV bu)) (.cons sK (.cons ((pqKeyIndCodec S).qenc t) .nil))
      let envMid := Env.cons (embedVal shcrInitMidTy mid)
        (.cons (embedVal (.sum SCS shcrInitMidTy) (.inr mid)) env0)
      ∀ out ∈ support ((roShadowQueryC tlPrimKeyInd f.roCap
          (shcrRoListAtomicE (.fst .v3)) (.snd .v3) (.fst .v0)).eval envMid),
        RoCacheAvlInv (keyIndLoopBound b) f.roCap out.2.1 out.2.2 ∧
        out.2.1.length ≤ (stRoList (projVal shcrStTy sK.1).1).length + 1) :
    let f := keyIndCoreFuels S b
    let arm := shcrInitArmPostK S f.M_on f.roCap N_s opk
    ∀ vs' ∈ support (arm.eval
        (.cons (u, (i, bundleV bu)) (.cons sK (.cons ((pqKeyIndCodec S).qenc t) .nil)))),
      ShcrSimInv S b (bumpPred (keyIndSimPred S) c t) vs'.2 := by
  dsimp only
  set f := keyIndCoreFuels S b
  set env0 : Env (S := pqAtomicSig)
      [.prod (.base (.fin S.N_id)) (.prod (.base (.fin N_s)) (bundleT (ℓ := 0) (Pt := Empty))),
       shcrKindStTy, (pqKeyIndCodec S).Q] :=
    .cons (u, (i, bundleV bu)) (.cons sK (.cons ((pqKeyIndCodec S).qenc t) .nil))
  set p : initQTy.denote := (u.val, (i.val, _root_.SignalPqxdh.LegacyCosted.bundleV bu))
  set sL : shcrStTy.denote := projVal shcrStTy sK.1
  have hsK1 : sK.1 = embedVal shcrStTy sL := (embedVal_projVal shcrStTy sK.1).symm
  have hbSt : projVal keyIndStateTy sK.1.1 = sL.1 := by
    rw [hsK1]; exact projVal_embedVal keyIndStateTy sL.1
  have hScsSnd : ∀ x : SCS.denote, (embedVal SCS x).2 = embedVal shcrStTy x.2 := fun _ => rfl
  have hStFst : ∀ x : shcrStTy.denote,
      (embedVal shcrStTy x).1 = embedVal keyIndStateTy x.1 := fun _ => rfl
  obtain ⟨h0, _, h2⟩ := bumpPred_online S c hOn
  have hCoreOnline : BaseOnlineLenInv c sL.1 := by
    simpa only [hbSt] using hInv.core_inv.online_len
  have hRoLen : (stRoList sL.1).length ≤ c 2 := by
    simpa only [hbSt] using hInv.core_inv.ro_len
  intro vs' hvs'
  dsimp only [shcrInitArmPostK] at hvs'
  rw [comp_bind_eval, hPreEval] at hvs'
  simp only [map_eq_bind_pure_comp, bind_assoc, pure_bind, Function.comp_def,
    mem_support_bind_iff] at hvs'
  rcases hvs' with ⟨pre, hPreMem, hvs'⟩
  cases pre with
  | inl rsOut =>
    rw [caseSum_v0_inl _ _ (embedVal (.sum SCS shcrInitMidTy) (.inl rsOut))
      (embedVal SCS rsOut) rfl] at hvs'
    simp only [Comp.eval, Expr.eval, Env.get, Expr.v0, Expr.v3, env0,
      support_pure, Set.mem_singleton_iff] at hvs'
    subst hvs'
    obtain ⟨hB, hCnt', hIr', hRr'⟩ := shcrInitiatePreRoC_inl_mem S f.M_on opk sL p hPreMem
    have hProjS' : projVal shcrStTy (embedVal SCS rsOut).2 = rsOut.2 := by
      rw [hScsSnd rsOut]; exact projVal_embedVal shcrStTy rsOut.2
    have hProjB' : projVal keyIndStateTy (embedVal SCS rsOut).2.1 = sL.1 := by
      rw [hScsSnd rsOut, hStFst rsOut.2, ← hB]
      exact projVal_embedVal keyIndStateTy rsOut.2.1
    refine ⟨⟨?_, ?_, ?_⟩, ?_, ?_, ?_⟩
    · rw [hProjB']; exact BaseOnlineLenInv.mono_online hOn hCoreOnline
    · rw [hProjB', h2]; exact Nat.le_succ_of_le hRoLen
    · rw [hProjB']; simpa only [hbSt] using hInv.core_inv.ro_avl
    · rw [hProjS', h0]; exact Nat.le_trans hCnt' (Nat.succ_le_succ hInv.cnt_le)
    · rw [hProjS', hIr', h0]; exact Nat.le_succ_of_le hInv.ir_le
    · rw [hProjS', hRr', h0]; exact Nat.le_succ_of_le hInv.rr_le
  | inr mid =>
    have hMemRo := hMidMem mid
    rw [caseSum_v0_inr _ _ (embedVal (.sum SCS shcrInitMidTy) (.inr mid))
      (embedVal shcrInitMidTy mid) rfl, comp_bind_eval] at hvs'
    simp only [comp_bind_eval, mem_support_bind_iff] at hvs'
    rcases hvs' with ⟨out, hOutMem, v0, hv0Mem, hvs'⟩
    simp only [Comp.eval, Expr.eval, Env.get, Expr.v0, Expr.v1,
      support_pure, Set.mem_singleton_iff] at hvs'
    subst hvs'
    obtain ⟨hAvlOut, hLenOut⟩ := hMemRo out hOutMem
    rw [runAt4_eval] at hv0Mem
    simp only [env0, Expr.eval, Env.get, Expr.v0, Expr.v1, Expr.v4, hsK1] at hv0Mem
    rw [← embedVal_projVal _root_.SignalPqxdh.LegacyCosted.drKeyT out.1,
      ← embedVal_projVal roListLegacyTy out.2.1] at hv0Mem
    have hMC := mapComp_eval tlPrimKeyInd (shcrInitiatePostRoC S f.M_on)
      (shcrInitiatePostRoC_unsup S f.M_on)
      (.cons (projVal _root_.SignalPqxdh.LegacyCosted.drKeyT out.1)
        (.cons (projVal roListLegacyTy out.2.1) (.cons mid (.cons sL .nil))))
    have hEnv4 : embedEnv (.cons (projVal _root_.SignalPqxdh.LegacyCosted.drKeyT out.1)
        (.cons (projVal roListLegacyTy out.2.1) (.cons mid (.cons sL .nil)))) =
      .cons (embedVal _root_.SignalPqxdh.LegacyCosted.drKeyT
          (projVal _root_.SignalPqxdh.LegacyCosted.drKeyT out.1))
        (.cons (embedVal roListLegacyTy (projVal roListLegacyTy out.2.1))
          (.cons (embedVal shcrInitMidTy mid) (.cons (embedVal shcrStTy sL) .nil))) := rfl
    rw [hEnv4] at hMC
    rw [hMC, map_eq_bind_pure_comp, mem_support_bind_iff] at hv0Mem
    rcases hv0Mem with ⟨rsOut, hrsMem, hv0Eq⟩
    simp only [Function.comp_def, support_pure, Set.mem_singleton_iff] at hv0Eq
    subst hv0Eq
    obtain ⟨hP, hSp, hOp, hSe, hRe, hUO, hUN, hKy, hRo', hAd, hCnt', hIr', hRr'⟩ :=
      shcrInitiatePostRoC_mem_support S f.M_on
        (projVal _root_.SignalPqxdh.LegacyCosted.drKeyT out.1)
        (projVal roListLegacyTy out.2.1) mid sL hrsMem
    have hProjS' : projVal shcrStTy (embedVal SCS rsOut).2 = rsOut.2 := by
      rw [hScsSnd rsOut]; exact projVal_embedVal shcrStTy rsOut.2
    have hProjB' : projVal keyIndStateTy (embedVal SCS rsOut).2.1 = rsOut.2.1 := by
      rw [hScsSnd rsOut, hStFst rsOut.2]
      exact projVal_embedVal keyIndStateTy rsOut.2.1
    have hCntS : sL.2.2.2.2.1 ≤ c 0 := hInv.cnt_le
    have hIrS : sL.2.2.2.2.2.1.length ≤ c 0 := hInv.ir_le
    have hRrS : sL.2.2.2.2.2.2.1.length ≤ c 0 := hInv.rr_le
    refine ⟨⟨⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, ?_, ?_⟩, ?_, ?_, ?_⟩
    · rw [hProjB', hP, h0]; exact Nat.le_succ_of_le hCoreOnline.prin_le
    · rw [hProjB', hSp, h0]; exact Nat.le_succ_of_le hCoreOnline.spks_le
    · rw [hProjB', hOp, h0]; exact Nat.le_succ_of_le hCoreOnline.opks_le
    · rw [hProjB', hSe, h0]; exact Nat.succ_le_succ hCoreOnline.sess_le
    · rw [hProjB', hRe, h0]; exact Nat.le_succ_of_le hCoreOnline.resps_le
    · rw [hProjB', hUO, h0]; exact Nat.le_succ_of_le hCoreOnline.usedO_le
    · rw [hProjB', hUN, h0]; exact Nat.le_succ_of_le hCoreOnline.usedN_le
    · rw [hProjB', hKy, h0]; exact Nat.le_succ_of_le hCoreOnline.kyb_le
    · rw [hProjB', hAd, h0]; exact Nat.le_succ_of_le hCoreOnline.adv_le
    · have hSum := hCoreOnline.counts_eq; omega
    · rw [hProjB', hRo', h2]
      have hRoLen' : (projVal roListLegacyTy out.2.1).length = out.2.1.length := by
        have := embedVal_projVal roListLegacyTy out.2.1
        rw [embedVal_roList_eq] at this; exact congrArg List.length this
      omega
    · rw [hProjB', hRo', embedVal_projVal]
      exact hAvlOut
    · rw [hProjS', hCnt', h0]; exact Nat.succ_le_succ hCntS
    · rw [hProjS', hIr', h0]; exact Nat.succ_le_succ hIrS
    · rw [hProjS', hRr', h0]; exact Nat.le_succ_of_le hRrS

private theorem shcrInitArmPost_sim_gen (S : Setup) (b : QueryBudget) (c : Fin 3 → ℕ)
    (N_s : ℕ) (opk : Bool) (sK : shcrKindStTy.denote)
    (u : Fin S.N_id) (i : Fin N_s) (bu : _root_.SignalPqxdh.PreKeyBundleInput)
    (t : KeyIndQuery S) (hOn : isKeyIndOnlineQuery (.inr t) = true)
    (hInv : ShcrSimInv S b c sK)
    (hBound : ∀ k, bumpPred (keyIndSimPred S) c t k ≤ keyIndSimBounds b k)
    (hRhs : activePostEval S b sK t =
      embedVal SCS <$>
        (shcrInitiateC S (keyIndLoopBound b) opk
          (Γ₁ := [shcrStTy, initQTy]) (Γ₂ := [shcrStTy, initQTy]) (Δ := [shcrStTy, initQTy])
          .zero (.succ .zero)).eval
          (.cons (fixShcrLegacySent S b (projVal shcrStTy sK.1))
            (.cons (u.val, (i.val, _root_.SignalPqxdh.LegacyCosted.bundleV bu)) .nil))) :
    let f := keyIndCoreFuels S b
    let arm := shcrInitArmPostK S f.M_on f.roCap N_s opk
    Prod.map id (forgetShcrKindActive S b) <$>
        arm.eval (.cons (u, (i, bundleV bu)) (.cons sK (.cons ((pqKeyIndCodec S).qenc t) .nil))) =
      activePostEval S b sK t ∧
    ∀ vs' ∈ support (arm.eval
        (.cons (u, (i, bundleV bu)) (.cons sK (.cons ((pqKeyIndCodec S).qenc t) .nil)))),
      ShcrSimInv S b (bumpPred (keyIndSimPred S) c t) vs'.2 := by
  dsimp only
  set f := keyIndCoreFuels S b
  set env0 : Env (S := pqAtomicSig)
      [.prod (.base (.fin S.N_id)) (.prod (.base (.fin N_s)) (bundleT (ℓ := 0) (Pt := Empty))),
       shcrKindStTy, (pqKeyIndCodec S).Q] :=
    .cons (u, (i, bundleV bu)) (.cons sK (.cons ((pqKeyIndCodec S).qenc t) .nil))
  set p : initQTy.denote := (u.val, (i.val, _root_.SignalPqxdh.LegacyCosted.bundleV bu))
  set sL : shcrStTy.denote := projVal shcrStTy sK.1
  have hsK1 : sK.1 = embedVal shcrStTy sL := (embedVal_projVal shcrStTy sK.1).symm
  have hbSt : projVal keyIndStateTy sK.1.1 = sL.1 := by
    rw [hsK1]; exact projVal_embedVal keyIndStateTy sL.1
  obtain ⟨hc0_1, hM_le⟩ := online_fuel_bounds S b c hOn hBound
  have hc0 : c 0 ≤ f.M_on := Nat.le_of_succ_le hc0_1
  have hc : ∀ j, c j ≤ keyIndSimBounds b j := le_bounds_of_bump S b hBound
  have hCoreOnline : BaseOnlineLenInv c sL.1 := by
    simpa only [hbSt] using hInv.core_inv.online_len
  have hRoLen : (stRoList sL.1).length ≤ c 2 := by
    simpa only [hbSt] using hInv.core_inv.ro_len
  obtain ⟨hLtK, hRoom⟩ := ro_bounds_of_le S b hc hCoreOnline.counts_eq hRoLen
  have hPreEval :
      (runAt2 (.fst .v1) (initPayToNatE N_s S .v0)
        (mapComp tlPrimKeyInd (shcrInitiatePreRoC S f.M_on opk))).eval env0 =
      embedVal (.sum SCS shcrInitMidTy) <$>
        (shcrInitiatePreRoC S f.M_on opk).eval (.cons sL (.cons p .nil)) := by
    rw [runAt2_eval, initPayToNatE_v0_eval]
    simp only [env0, Expr.eval, Env.get, Expr.v1, hsK1]
    exact mapComp_eval tlPrimKeyInd (shcrInitiatePreRoC S f.M_on opk)
      (shcrInitiatePreRoC_unsup S f.M_on opk) (.cons sL (.cons p .nil))
  have hMidSim : ∀ mid : shcrInitMidTy.denote,
      let envMid := Env.cons (embedVal shcrInitMidTy mid)
        (.cons (embedVal (.sum SCS shcrInitMidTy) (.inr mid)) env0)
      Prod.map id Prod.fst <$>
        (roShadowQueryC tlPrimKeyInd f.roCap
          (shcrRoListAtomicE (.fst .v3)) (.snd .v3) (.fst .v0)).eval envMid =
        embedVal (.prod _root_.SignalPqxdh.LegacyCosted.drKeyT roListLegacyTy) <$>
          (hkdfOrRoC (keyIndLoopBound b) true
            (Γ := [keyIndStateTy, _root_.SignalPqxdh.LegacyCosted.B 192])
            (Δ := [keyIndStateTy, _root_.SignalPqxdh.LegacyCosted.B 192])
            .zero (.var (.succ .zero))).eval (.cons sL.1 (.cons mid.1 .nil)) ∧
      ∀ out ∈ support ((roShadowQueryC tlPrimKeyInd f.roCap
          (shcrRoListAtomicE (.fst .v3)) (.snd .v3) (.fst .v0)).eval envMid),
        RoCacheAvlInv (keyIndLoopBound b) f.roCap out.2.1 out.2.2 ∧
        out.2.1.length ≤ (stRoList sL.1).length + 1 := by
    intro mid envMid
    have hRoEq : (shcrRoListAtomicE (.fst .v3)).eval envMid =
        embedVal roListLegacyTy (stRoList sL.1) := by
      rw [shcrRoListAtomicE_eval]
      simp only [envMid, env0, Expr.eval, Env.get, Expr.v3]
      rfl
    have hRoAvl : RoCacheAvlInv (keyIndLoopBound b) f.roCap
        ((shcrRoListAtomicE (.fst .v3)).eval envMid)
        ((Expr.snd (O := pqAtomicOps) .v3).eval envMid) := by
      rw [hRoEq]
      simpa only [envMid, env0, Expr.eval, Env.get, Expr.v3, hbSt] using hInv.core_inv.ro_avl
    have hLenEq : ((shcrRoListAtomicE (.fst .v3)).eval envMid).length =
        (stRoList sL.1).length := by
      rw [hRoEq, embedVal_roList_eq]
    obtain ⟨hSim, hMem⟩ := roShadowQueryC_eval_sim tlPrimKeyInd envMid
      (keyIndLoopBound b) f.roCap (shcrRoListAtomicE (.fst .v3)) (.snd .v3) (.fst .v0) sL.1
      (hkdfOrRoC_unsup (keyIndLoopBound b)) hRoEq hRoAvl
      (by rw [hLenEq]; exact hLtK) (by rw [hLenEq]; exact hRoom)
    refine ⟨?_, fun out hOut => ?_⟩
    · rw [hSim]
      exact mapComp_eval tlPrimKeyInd
        (hkdfOrRoC (keyIndLoopBound b) true
          (Γ := [keyIndStateTy, _root_.SignalPqxdh.LegacyCosted.B 192])
          (Δ := [keyIndStateTy, _root_.SignalPqxdh.LegacyCosted.B 192])
          .zero (.var (.succ .zero)))
        (hkdfOrRoC_unsup (keyIndLoopBound b)) (.cons sL.1 (.cons mid.1 .nil))
    · obtain ⟨hAvl', hL'⟩ := hMem out hOut
      exact ⟨hAvl', by simpa only [hLenEq] using hL'⟩
  refine ⟨?_, ?_⟩
  · rw [hRhs, shcrInitiateC_eq_pre_ro_post,
      ← shcrInitiatePreRoC_fixSent_comm S b (keyIndLoopBound b) opk sL p,
      ← shcrInitiatePreRoC_fuel_eq S opk sL p hCoreOnline hc0 hM_le]
    dsimp only [shcrInitArmPostK]
    rw [comp_bind_eval, hPreEval]
    simp only [map_eq_bind_pure_comp, bind_assoc, pure_bind, Function.comp_def]
    congr 1; funext pre
    cases pre with
    | inl rsOut =>
      have hPair : embedVal SCS rsOut = (embedVal _ rsOut.1, embedVal shcrStTy rsOut.2) := rfl
      rw [caseSum_v0_inl _ _ (embedVal (.sum SCS shcrInitMidTy) (.inl rsOut)) (embedVal SCS rsOut) rfl]
      simp only [Comp.eval, Expr.eval, Env.get, Expr.v0, Expr.v3, env0, hPair, pure_bind]
      rfl
    | inr mid =>
      obtain ⟨hSimRo, _⟩ := hMidSim mid
      rw [caseSum_v0_inr _ _ (embedVal (.sum SCS shcrInitMidTy) (.inr mid))
        (embedVal shcrInitMidTy mid) rfl, comp_bind_eval]
      simp only [comp_bind_eval, bind_assoc]
      have hStepPost : ∀ out : (embedTy _root_.SignalPqxdh.LegacyCosted.drKeyT).denote ×
            ((embedTy roListLegacyTy).denote × roAvlTy.denote),
          (do
            let v0 ← (runAt4 (.fst .v0) (.fst (.snd .v0)) .v1 (.fst .v4)
              (mapComp tlPrimKeyInd (shcrInitiatePostRoC S f.M_on))).eval
              (.cons out (.cons (embedVal shcrInitMidTy mid)
                (.cons (embedVal (.sum SCS shcrInitMidTy) (.inr mid)) env0)))
            let x ← (Comp.ret (O := pqAtomicOps) (I := pqPrimIface)
              (.pair (.fst .v0) (.pair (.snd .v0) (.snd (.snd .v1))))).eval
              (.cons v0 (.cons out (.cons (embedVal shcrInitMidTy mid)
                (.cons (embedVal (.sum SCS shcrInitMidTy) (.inr mid)) env0))))
            pure (Prod.map id (forgetShcrKindActive S b) x)) =
          (do
            let rsOut ← (shcrInitiatePostRoC S (keyIndLoopBound b)).eval
              (.cons (projVal _root_.SignalPqxdh.LegacyCosted.drKeyT out.1)
                (.cons (projVal roListLegacyTy out.2.1)
                  (.cons mid (.cons (fixShcrLegacySent S b sL) .nil))))
            pure (embedVal SCS rsOut)) := by
        intro out
        simp only [Comp.eval, Expr.eval, Env.get, Expr.v0, Expr.v1, pure_bind]
        rw [runAt4_eval]
        simp only [env0, Expr.eval, Env.get, Expr.v4, hsK1]
        conv_lhs =>
          rw [← embedVal_projVal _root_.SignalPqxdh.LegacyCosted.drKeyT out.1,
            ← embedVal_projVal roListLegacyTy out.2.1]
        have hMC := mapComp_eval tlPrimKeyInd (shcrInitiatePostRoC S f.M_on)
          (shcrInitiatePostRoC_unsup S f.M_on)
          (.cons (projVal _root_.SignalPqxdh.LegacyCosted.drKeyT out.1)
            (.cons (projVal roListLegacyTy out.2.1) (.cons mid (.cons sL .nil))))
        have hEnv4 : embedEnv (.cons (projVal _root_.SignalPqxdh.LegacyCosted.drKeyT out.1)
            (.cons (projVal roListLegacyTy out.2.1) (.cons mid (.cons sL .nil)))) =
          .cons (embedVal _root_.SignalPqxdh.LegacyCosted.drKeyT
              (projVal _root_.SignalPqxdh.LegacyCosted.drKeyT out.1))
            (.cons (embedVal roListLegacyTy (projVal roListLegacyTy out.2.1))
              (.cons (embedVal shcrInitMidTy mid) (.cons (embedVal shcrStTy sL) .nil))) := rfl
        rw [hEnv4] at hMC
        rw [hMC]
        have hFix := shcrInitiatePostRoC_fixSent_comm S b f.M_on
          (projVal _root_.SignalPqxdh.LegacyCosted.drKeyT out.1)
          (projVal roListLegacyTy out.2.1) mid sL
        have hFuel := shcrInitiatePostRoC_fuel_eq S
          (projVal _root_.SignalPqxdh.LegacyCosted.drKeyT out.1)
          (projVal roListLegacyTy out.2.1) mid (fixShcrLegacySent S b sL)
          (by rcases sL with ⟨_, _, _, _, _, _, _, _, _⟩; exact hCoreOnline) hc0 hM_le
        rw [← hFuel, ← hFix]
        simp only [map_eq_bind_pure_comp, bind_assoc, pure_bind, Function.comp_def]
        rfl
      conv_lhs => arg 2; ext out; rw [hStepPost]
      have hBindFst :
          (do
            let out ← (roShadowQueryC tlPrimKeyInd f.roCap
              (shcrRoListAtomicE (.fst .v3)) (.snd .v3) (.fst .v0)).eval
              (.cons (embedVal shcrInitMidTy mid)
                (.cons (embedVal (.sum SCS shcrInitMidTy) (.inr mid)) env0))
            let rsOut ← (shcrInitiatePostRoC S (keyIndLoopBound b)).eval
              (.cons (projVal _root_.SignalPqxdh.LegacyCosted.drKeyT out.1)
                (.cons (projVal roListLegacyTy out.2.1)
                  (.cons mid (.cons (fixShcrLegacySent S b sL) .nil))))
            pure (embedVal SCS rsOut)) =
          (do
            let drK ← Prod.map id Prod.fst <$>
              (roShadowQueryC tlPrimKeyInd f.roCap
                (shcrRoListAtomicE (.fst .v3)) (.snd .v3) (.fst .v0)).eval
                (.cons (embedVal shcrInitMidTy mid)
                  (.cons (embedVal (.sum SCS shcrInitMidTy) (.inr mid)) env0))
            let rsOut ← (shcrInitiatePostRoC S (keyIndLoopBound b)).eval
              (.cons (projVal _root_.SignalPqxdh.LegacyCosted.drKeyT drK.1)
                (.cons (projVal roListLegacyTy drK.2)
                  (.cons mid (.cons (fixShcrLegacySent S b sL) .nil))))
            pure (embedVal SCS rsOut)) := by
        simp only [map_eq_bind_pure_comp, bind_assoc, pure_bind, Function.comp_def, Prod.map, id_eq]
      rw [hBindFst, hSimRo]
      have hFixBSt : (fixShcrLegacySent S b sL).1 = sL.1 := by
        rcases sL with ⟨_, _, _, _, _, _, _, _, _⟩; rfl
      have hSumInr : Sum.map (Prod.map id (fixShcrLegacySent S b)) id
          (.inr mid : (SCS.sum shcrInitMidTy).denote) = .inr mid := rfl
      have hDrPair : ∀ y : (_root_.SignalPqxdh.LegacyCosted.drKeyT.prod roListLegacyTy).denote,
          embedVal (.prod _root_.SignalPqxdh.LegacyCosted.drKeyT roListLegacyTy) y =
            (embedVal _root_.SignalPqxdh.LegacyCosted.drKeyT y.1,
             embedVal roListLegacyTy y.2) := fun _ => rfl
      rw [hFixBSt, hSumInr]
      simp only [map_eq_bind_pure_comp, bind_assoc, pure_bind, Function.comp_def,
        hDrPair, projVal_embedVal]
  · exact shcrInitArmPost_inv_gen S b c N_s opk sK u i bu t hOn hInv hPreEval
      (fun mid => (hMidSim mid).2)

theorem shcrInitOpkArmPost_sim (S : Setup) (b : QueryBudget) (c : Fin 3 → ℕ)
    (sK : shcrKindStTy.denote) (u : Fin S.N_id) (i : Fin S.N_send_opk)
    (bu : _root_.SignalPqxdh.PreKeyBundleInput)
    (hInv : ShcrSimInv S b c sK)
    (hBound : ∀ k, bumpPred (keyIndSimPred S) c (.initiateOPK u i bu) k ≤ keyIndSimBounds b k) :
    let f := keyIndCoreFuels S b
    let t : KeyIndQuery S := .initiateOPK u i bu
    let arm := shcrInitArmPostK S f.M_on f.roCap S.N_send_opk true
    Prod.map id (forgetShcrKindActive S b) <$>
        arm.eval (.cons (u, (i, bundleV bu)) (.cons sK (.cons ((pqKeyIndCodec S).qenc t) .nil))) =
      activePostEval S b sK t ∧
    ∀ vs' ∈ support (arm.eval
        (.cons (u, (i, bundleV bu)) (.cons sK (.cons ((pqKeyIndCodec S).qenc t) .nil)))),
      ShcrSimInv S b (bumpPred (keyIndSimPred S) c t) vs'.2 := by
  intro f t arm
  have hOn : isKeyIndOnlineQuery (.inr t) = true := by simp [isKeyIndOnlineQuery, t]
  refine shcrInitArmPost_sim_gen S b c S.N_send_opk true sK u i bu t hOn hInv hBound ?_
  simp only [activePostEval, shcr1KeyActivePostC, shcrActivePostTailC,
    _root_.SignalPqxdh.Security.ReductionDsl.KeyInd.caseSumV,
    _root_.SignalPqxdh.LegacyCosted.keyIndCodec, _root_.SignalPqxdh.LegacyCosted.keyIndQenc,
    Comp.eval, v_eval_cons, v_zero_eval, t]
  rw [shcrInitiateC_eval_congr S (keyIndLoopBound b) true]
  rfl

theorem shcrInitNoOpkArmPost_sim (S : Setup) (b : QueryBudget) (c : Fin 3 → ℕ)
    (sK : shcrKindStTy.denote) (u : Fin S.N_id) (i : Fin S.N_send_no_opk)
    (bu : _root_.SignalPqxdh.PreKeyBundleInput)
    (hInv : ShcrSimInv S b c sK)
    (hBound : ∀ k, bumpPred (keyIndSimPred S) c (.initiateNoOPK u i bu) k ≤ keyIndSimBounds b k) :
    let f := keyIndCoreFuels S b
    let t : KeyIndQuery S := .initiateNoOPK u i bu
    let arm := shcrInitArmPostK S f.M_on f.roCap S.N_send_no_opk false
    Prod.map id (forgetShcrKindActive S b) <$>
        arm.eval (.cons (u, (i, bundleV bu)) (.cons sK (.cons ((pqKeyIndCodec S).qenc t) .nil))) =
      activePostEval S b sK t ∧
    ∀ vs' ∈ support (arm.eval
        (.cons (u, (i, bundleV bu)) (.cons sK (.cons ((pqKeyIndCodec S).qenc t) .nil)))),
      ShcrSimInv S b (bumpPred (keyIndSimPred S) c t) vs'.2 := by
  intro f t arm
  have hOn : isKeyIndOnlineQuery (.inr t) = true := by simp [isKeyIndOnlineQuery, t]
  refine shcrInitArmPost_sim_gen S b c S.N_send_no_opk false sK u i bu t hOn hInv hBound ?_
  simp only [activePostEval, shcr1KeyActivePostC, shcrActivePostTailC,
    _root_.SignalPqxdh.Security.ReductionDsl.KeyInd.caseSumV,
    _root_.SignalPqxdh.LegacyCosted.keyIndCodec, _root_.SignalPqxdh.LegacyCosted.keyIndQenc,
    Comp.eval, v_eval_cons, v_zero_eval, t]
  rw [shcrInitiateC_eval_congr S (keyIndLoopBound b) false]
  rfl

private theorem accPayToNatE_eval (N_o : ℕ) (S : Setup)
    {Γ : List (Ty pqAtomicSig)}
    (e : Expr pqAtomicOps Γ
      (.prod (.base (.fin S.N_id))
        (.prod (.base (.fin S.N_recv))
          (.prod (.base (.fin N_o)) (hdrT (ℓ := 0) (Pt := Empty))))))
    (k : Fin S.N_id) (j : Fin S.N_recv) (o : Fin N_o)
    (hdr : _root_.SignalPqxdh.HandshakeHdr) (ρ : Env Γ)
    (he : e.eval ρ = (k, (j, (o, hdrV hdr)))) :
    (accPayToNatE N_o S e).eval ρ =
      embedVal accQTy (k.val, (j.val, (o.val, _root_.SignalPqxdh.LegacyCosted.hdrV hdr))) := by
  dsimp only [accPayToNatE, Expr.eval]
  rw [he]
  rcases hdr with ⟨_, _, _, _ | _, _, _⟩ <;> rfl

private theorem shcrAcceptB_eval_congr (S : Setup) (K : ℕ) (opk : Bool)
    {Γ₁ Γ₂ Δ : List PT} (sV : Var Γ₁ shcrStTy) (xV : Var Γ₂ accQTy)
    [Ext Γ₁ Δ] [Ext Γ₂ Δ] (env : Env Δ) :
    (shcrAcceptB S K opk (Δ := Δ) sV xV).eval env =
      (shcrAcceptB S K opk
        (Γ₁ := [shcrStTy, accQTy]) (Γ₂ := [shcrStTy, accQTy]) (Δ := [shcrStTy, accQTy])
        .zero (.succ .zero)).eval
        (.cons ((v sV).eval env) (.cons ((v xV).eval env) .nil)) := by
  have hRen : compRename (ren2Var (Δ := Δ) sV xV)
      (shcrAcceptB S K opk
        (Γ₁ := [shcrStTy, accQTy]) (Γ₂ := [shcrStTy, accQTy]) (Δ := [shcrStTy, accQTy])
        .zero (.succ .zero)) =
      shcrAcceptB S K opk (Δ := Δ) sV xV := by
    cases opk <;> rfl
  rw [← hRen]
  exact compRename_eval _ (ren2Var (Δ := Δ) sV xV) _ env (ren2Var_env_get sV xV env)

private theorem coreAcceptPreRoC_eval_congr (S : Setup) (K : ℕ) (opk : Bool)
    {Γ₁ Γ₂ Δ : List PT} (stV : Var Γ₁ keyIndStateTy) (xV : Var Γ₂ accQTy)
    [Ext Γ₁ Δ] [Ext Γ₂ Δ] (env : Env Δ) :
    (coreAcceptPreRoC S K opk (Δ := Δ) stV xV).eval env =
      (coreAcceptPreRoC S K opk
        (Γ₁ := [keyIndStateTy, accQTy]) (Γ₂ := [keyIndStateTy, accQTy])
        (Δ := [keyIndStateTy, accQTy]) .zero (.succ .zero)).eval
        (.cons ((v stV).eval env) (.cons ((v xV).eval env) .nil)) := by
  have hRen : compRename (ren2Var (Δ := Δ) stV xV)
      (coreAcceptPreRoC S K opk
        (Γ₁ := [keyIndStateTy, accQTy]) (Γ₂ := [keyIndStateTy, accQTy])
        (Δ := [keyIndStateTy, accQTy]) .zero (.succ .zero)) =
      coreAcceptPreRoC S K opk (Δ := Δ) stV xV := by
    cases opk <;> rfl
  rw [← hRen]
  exact compRename_eval _ (ren2Var (Δ := Δ) stV xV) _ env (ren2Var_env_get stV xV env)

private theorem shcrAcceptPreRoC_fixSent_eq (S : Setup) (b : QueryBudget) (K : ℕ)
    (opk : Bool) (sL : shcrStTy.denote) (p : accQTy.denote) :
    (shcrAcceptPreRoC S K opk).eval (.cons (fixShcrLegacySent S b sL) (.cons p .nil)) =
      (shcrAcceptPreRoC S K opk).eval (.cons sL (.cons p .nil)) := by
  have hFixB : (fixShcrLegacySent S b sL).1 = sL.1 := by
    rcases sL with ⟨_, _, _, _, _, _, _, _, _⟩; rfl
  simp only [shcrAcceptPreRoC, letV, Comp.eval, pure_bind]
  rw [coreAcceptPreRoC_eval_congr, eq_comm, coreAcceptPreRoC_eval_congr, eq_comm]
  simp only [Expr.eval, v, Ext.wk, Env.get, hFixB]

private theorem findHonestC_qHdr_eval (S : Setup) (K : ℕ) {Γ₁ Γ₂ Δ : List PT}
    (stV : Var Γ₁ keyIndStateTy) (xV : Var Γ₂ accQTy) [Ext Γ₁ Δ] [Ext Γ₂ Δ] (env : Env Δ) :
    (findHonestC S K (Δ := Δ) stV (hdIkAPk (qHdr (v xV)))).eval env =
      (findHonestC S K
        (Γ := [keyIndStateTy, accQTy]) (Δ := [keyIndStateTy, accQTy])
        .zero (hdIkAPk (qHdr (.var (.succ .zero))))).eval
        (.cons ((v stV).eval env) (.cons ((v xV).eval env) .nil)) := by
  have hRen : compRename (ren2Var (Δ := Δ) stV xV)
      (findHonestC S K
        (Γ := [keyIndStateTy, accQTy]) (Δ := [keyIndStateTy, accQTy])
        .zero (hdIkAPk (qHdr (.var (.succ .zero))))) =
      findHonestC S K (Δ := Δ) stV (hdIkAPk (qHdr (v xV))) := rfl
  rw [← hRen]
  exact compRename_eval _ (ren2Var (Δ := Δ) stV xV) _ env (ren2Var_env_get stV xV env)

private abbrev respPairTy : PT :=
  .prod _root_.SignalPqxdh.Security.ReductionDsl.KeyInd.keyIndRespEntryTy keyIndStateTy

private def renPP {A : PT} {Δ : List PT} (aV : Var Δ A) :
    ∀ {τ}, Var [A, A] τ → Var Δ τ
  | _, .zero => aV
  | _, .succ .zero => aV

private theorem renPP_env_get {A : PT} {Δ : List PT} (x : A.denote) (env : Env Δ) :
    ∀ {τ} (w : Var [A, A] τ),
      (Env.cons (t := A) x env).get (renPP (.zero : Var (A :: Δ) A) w) =
        (Env.cons (t := A) x (Env.cons (t := A) x .nil)).get w
  | _, .zero => rfl
  | _, .succ .zero => rfl

private def recordRespBody (S : Setup) (K : ℕ) {Γ0 : List PT} :
    Comp pqxdhOps _root_.SignalPqxdh.LegacyCosted.pqPrimIface (respPairTy :: Γ0) keyIndStateTy :=
  letV (.fst (v (.zero : Var (respPairTy :: Γ0) respPairTy))) fun r =>
  bindV (_root_.SignalPqxdh.Security.ReductionDsl.KeyInd.findMV (min K S.N_dh)
      (stSess (.snd (v (.zero : Var (respPairTy :: Γ0) respPairTy))))
      fun s => _root_.SignalPqxdh.Security.ReductionDsl.KeyInd.partnerC s r) fun found =>
  bindV (caseOptV (v found) _root_.SignalPqxdh.Security.ReductionDsl.KeyInd.sDrKey96
      fun s => .ret (_root_.SignalPqxdh.Security.ReductionDsl.KeyInd.seDrRand (v s))) fun dr =>
  .ret (stUpd (.snd (v (.zero : Var (respPairTy :: Γ0) respPairTy)))
    (resps := .cons (_root_.SignalPqxdh.Security.ReductionDsl.KeyInd.reUpd (v r) (drRand := v dr))
      (stResps (.snd (v (.zero : Var (respPairTy :: Γ0) respPairTy))))))

private theorem recordRespC_eval_congr (S : Setup) (K : ℕ) {Δ : List PT}
    (pE : Expr pqxdhOps Δ respPairTy) (env : Env Δ) :
    (recordRespC S K pE).eval env =
      (recordRespC S K (Δ := [respPairTy]) (.var .zero)).eval (.cons (pE.eval env) .nil) := by
  dsimp only [recordRespC]
  conv_lhs => rw [letV_eval_step]
  conv_rhs => rw [letV_eval_step]; simp only [Expr.eval, Env.get]
  change (recordRespBody S K (Γ0 := Δ)).eval (Env.cons (t := respPairTy) (pE.eval env) env) =
    (recordRespBody S K (Γ0 := [respPairTy])).eval
      (Env.cons (t := respPairTy) (pE.eval env) (Env.cons (t := respPairTy) (pE.eval env) .nil))
  have hRen : compRename (renPP (.zero : Var (respPairTy :: Δ) respPairTy))
      (recordRespBody S K (Γ0 := [respPairTy])) = recordRespBody S K (Γ0 := Δ) := rfl
  rw [← hRen]
  exact compRename_eval (recordRespBody S K (Γ0 := [respPairTy]))
    (renPP (.zero : Var (respPairTy :: Δ) respPairTy)) _ _ (renPP_env_get (pE.eval env) env)

private theorem kyberCheckE_snd_len_le {Γ : List PT} (K : ℕ)
    (used : Expr pqxdhOps Γ (.list (.prod .nat (.prod _root_.SignalPqxdh.LegacyCosted.U32
      (.prod _root_.SignalPqxdh.LegacyCosted.U32 (_root_.SignalPqxdh.LegacyCosted.B 32))))))
    (entry : Expr pqxdhOps Γ (.prod .nat (.prod _root_.SignalPqxdh.LegacyCosted.U32
      (.prod _root_.SignalPqxdh.LegacyCosted.U32 (_root_.SignalPqxdh.LegacyCosted.B 32)))))
    (env : Env Γ) :
    ((kyberCheckE K used entry).eval env).2.length ≤ (used.eval env).length + 1 := by
  simp only [kyberCheckE, _root_.SignalPqxdh.Security.ReductionDsl.KeyInd.eLet2,
    _root_.SignalPqxdh.Security.ReductionDsl.KeyInd.eLet, Expr.eval, v_eval_cons, v_zero_eval]
  have hBound : ∀ (p : Prop) [Decidable p],
      (if p then (false, used.eval env) else (true, entry.eval env :: used.eval env)).2.length ≤
        (used.eval env).length + 1 := by
    intro p _; by_cases hp : p
    · simp only [hp, ↓reduceIte]; exact Nat.le_succ _
    · simp only [hp, ↓reduceIte, List.length_cons]; exact Nat.le_refl _
  exact hBound _

private theorem eMap_len_le {Γ : List PT} {τ₁ τ₂ : PT} (K : ℕ)
    (xs : Expr pqxdhOps Γ (.list τ₁))
    (f : Var (τ₁ :: Γ) τ₁ → Expr pqxdhOps (τ₁ :: Γ) τ₂) (env : Env Γ) :
    ((eMap K xs f).eval env).length ≤ (xs.eval env).length := by
  simp only [eMap, Expr.eval, List.length_map, List.length_take, Nat.min_le_right]

private theorem recordRespC_mem_support (S : Setup) (K : ℕ) {Δ : List PT}
    (pE : Expr pqxdhOps Δ respPairTy) (env : Env Δ) {st2 : keyIndStateTy.denote}
    (hMem : st2 ∈ support ((recordRespC S K pE).eval env)) :
    let st1 := (pE.eval env).2
    stPrinList st2 = stPrinList st1 ∧ stSpksList st2 = stSpksList st1 ∧
    stOpksList st2 = stOpksList st1 ∧ stSessList st2 = stSessList st1 ∧
    (stRespsList st2).length = (stRespsList st1).length + 1 ∧
    stUsedOList st2 = stUsedOList st1 ∧ stUsedNList st2 = stUsedNList st1 ∧
    stKybList st2 = stKybList st1 ∧ stRoList st2 = stRoList st1 ∧
    stAdvList st2 = stAdvList st1 := by
  dsimp only
  simp only [recordRespC, letV, bindV, Comp.eval, pure_bind,
    mem_support_bind_iff, support_pure, Set.mem_singleton_iff] at hMem
  rcases hMem with ⟨_, _, _, _, rfl⟩
  rcases pE.eval env with ⟨_, _, _, _, _, _, _, _, _, _, _, _⟩
  exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

private theorem caseOpt_v0_none {A R : Ty pqAtomicSig} {Γ : List (Ty pqAtomicSig)}
    (n : Comp pqAtomicOps pqPrimIface (Ty.opt A :: Γ) R)
    (s : Comp pqAtomicOps pqPrimIface (A :: Ty.opt A :: Γ) R)
    (x : (Ty.opt A).denote) (hx : x = none) (ρ : Env Γ) :
    (Comp.caseOpt .v0 n s).eval (.cons x ρ) = n.eval (.cons x ρ) := by
  subst hx; simp only [Comp.eval, Expr.eval, Expr.v0, Env.get]

private theorem caseOpt_v0_some {A R : Ty pqAtomicSig} {Γ : List (Ty pqAtomicSig)}
    (n : Comp pqAtomicOps pqPrimIface (Ty.opt A :: Γ) R)
    (s : Comp pqAtomicOps pqPrimIface (A :: Ty.opt A :: Γ) R)
    (x : (Ty.opt A).denote) (a : A.denote) (hx : x = some a) (ρ : Env Γ) :
    (Comp.caseOpt .v0 n s).eval (.cons x ρ) = s.eval (.cons a (.cons x ρ)) := by
  subst hx; simp only [Comp.eval, Expr.eval, Expr.v0, Env.get]

private theorem ite_eval {ι : Type} {T : OracleSpec ι} {I : _root_.ReductionDsl.Iface pqSig T}
    {Γ : List PT} {R : PT}
    (c : Expr pqxdhOps Γ .bool) (t e : Comp pqxdhOps I Γ R) (env : Env Γ) :
    (Comp.ite c t e).eval env = if c.eval env = true then t.eval env else e.eval env := by
  simp only [Comp.eval]

private theorem caseOptV_eval {ι : Type} {T : OracleSpec ι}
    {I : _root_.ReductionDsl.Iface pqSig T} {Γ : List PT} {τ₁ τ₂ : PT}
    (o : Expr pqxdhOps Γ (.opt τ₁)) (kn : Comp pqxdhOps I Γ τ₂)
    (ks : Var (τ₁ :: Γ) τ₁ → Comp pqxdhOps I (τ₁ :: Γ) τ₂) (env : Env Γ) :
    (caseOptV o kn ks).eval env =
      match o.eval env with
      | none => kn.eval env
      | some a => (ks .zero).eval (.cons a env) := by
  cases h : o.eval env <;> simp only [caseOptV, Comp.eval, h]

private theorem caseOptV_v0_none {ι : Type} {T : OracleSpec ι}
    {I : _root_.ReductionDsl.Iface pqSig T} {Γ : List PT} {τ₁ τ₂ : PT}
    (kn : Comp pqxdhOps I (.opt τ₁ :: Γ) τ₂)
    (ks : Var (τ₁ :: .opt τ₁ :: Γ) τ₁ → Comp pqxdhOps I (τ₁ :: .opt τ₁ :: Γ) τ₂)
    (env : Env Γ) :
    (caseOptV (v (.zero : Var (.opt τ₁ :: Γ) (.opt τ₁))) kn ks).eval (.cons none env) =
      kn.eval (.cons none env) := by
  simp only [caseOptV_eval, v_zero_eval]

private theorem caseOptV_v0_some {ι : Type} {T : OracleSpec ι}
    {I : _root_.ReductionDsl.Iface pqSig T} {Γ : List PT} {τ₁ τ₂ : PT}
    (kn : Comp pqxdhOps I (.opt τ₁ :: Γ) τ₂)
    (ks : Var (τ₁ :: .opt τ₁ :: Γ) τ₁ → Comp pqxdhOps I (τ₁ :: .opt τ₁ :: Γ) τ₂)
    (a : τ₁.denote) (env : Env Γ) :
    (caseOptV (v (.zero : Var (.opt τ₁ :: Γ) (.opt τ₁))) kn ks).eval (.cons (some a) env) =
      (ks .zero).eval (.cons a (.cons (some a) env)) := by
  simp only [caseOptV_eval, v_zero_eval]

private theorem expr_some_eval {Γ : List PT} {τ : PT} (e : Expr pqxdhOps Γ τ) (env : Env Γ) :
    (Expr.some e).eval env = some (e.eval env) := by
  simp only [Expr.eval]

private theorem bindV_eval {ι : Type} {T : OracleSpec ι}
    {I : _root_.ReductionDsl.Iface pqSig T} {Γ : List PT} {τ₁ τ₂ : PT}
    (m : Comp pqxdhOps I Γ τ₁) (k : Var (τ₁ :: Γ) τ₁ → Comp pqxdhOps I (τ₁ :: Γ) τ₂)
    (env : Env Γ) :
    (bindV m k).eval env = (m.eval env >>= fun x => (k .zero).eval (.cons x env)) := by
  simp only [bindV, Comp.eval]

private theorem bind_congr_mem {ι : Type} {spec : OracleSpec.{0, 0} ι} {α β : Type}
    (mx : OracleComp spec α) (f₁ f₂ : α → OracleComp spec β)
    (h : ∀ x ∈ support mx, f₁ x = f₂ x) :
    (mx >>= f₁) = (mx >>= f₂) := by
  induction mx using OracleComp.inductionOn with
  | pure a => exact h a (by simp only [support_pure, Set.mem_singleton_iff])
  | query_bind t m ih =>
    simp only [bind_assoc]
    congr 1; funext u
    exact ih u fun x hx => h x (by
      simp only [support_bind, Set.mem_iUnion]
      exact ⟨u, mem_support_query t u, hx⟩)

private theorem shcrAcceptPreRoC_fuel_eq (S : Setup) {K₁ K₂ : ℕ} {c : Fin 3 → ℕ}
    (opk : Bool) (sL : shcrStTy.denote) (p : accQTy.denote)
    (hInv : BaseOnlineLenInv c sL.1) (hc0 : c 0 ≤ K₁) (hLe : K₁ ≤ K₂) :
    (shcrAcceptPreRoC S K₁ opk).eval (.cons sL (.cons p .nil)) =
      (shcrAcceptPreRoC S K₂ opk).eval (.cons sL (.cons p .nil)) := by
  have hPrin  : (stPrinList sL.1).length ≤ K₁  := Nat.le_trans hInv.prin_le hc0
  have hSpks  : (stSpksList sL.1).length ≤ K₁  := Nat.le_trans hInv.spks_le hc0
  have hOpks  : (stOpksList sL.1).length ≤ K₁  := Nat.le_trans hInv.opks_le hc0
  have hUsedO : (stUsedOList sL.1).length ≤ K₁ := Nat.le_trans hInv.usedO_le hc0
  have hUsedN : (stUsedNList sL.1).length ≤ K₁ := Nat.le_trans hInv.usedN_le hc0
  have hKyb   : (stKybList sL.1).length ≤ K₁   := Nat.le_trans hInv.kyb_le hc0
  cases opk with
  | false =>
    simp only [shcrAcceptPreRoC, coreAcceptPreRoC, Bool.false_eq_true, ↓reduceIte]
    conv_lhs => rw [letV_eval_step, ite_eval]
    conv_rhs => rw [letV_eval_step, ite_eval]
    split_ifs with hHdr
    · rfl
    · conv_lhs => rw [ite_eval]
      conv_rhs => rw [ite_eval]
      rw [eAny_eq_of_le _ _ _
        (by simpa only [scBase, stUsedN, stUsedNList, Expr.eval, Env.get, v, Ext.wk] using hUsedN) hLe]
      split_ifs with hAny
      · rfl
      · conv_lhs => rw [bindV_eval]
        conv_rhs => rw [bindV_eval]
        rw [koskSenderOkC_min_eq S _ _ _
          (by simpa only [scBase, Expr.eval, Env.get, v, Ext.wk] using hInv) hc0 hLe]
        refine bind_congr_mem _ _ _ fun ok _ => ?_
        conv_lhs => rw [ite_eval]
        conv_rhs => rw [ite_eval]
        split_ifs with hOk
        · rfl
        · conv_lhs => rw [caseOptV_eval]
          conv_rhs => rw [caseOptV_eval]
          rw [eFind_eq_of_le _ _ _
            (by simpa only [scBase, stPrin, stPrinList, Expr.eval, Env.get, v, Ext.wk] using hPrin) hLe]
          cases (eFind K₂ _ _).eval _ with
          | none => rfl
          | some kE =>
            dsimp only
            conv_lhs => rw [caseOptV_eval]
            conv_rhs => rw [caseOptV_eval]
            rw [eFind_eq_of_le _ _ _
              (by simpa only [scBase, stSpks, stSpksList, Expr.eval, Env.get, v, Ext.wk] using hSpks) hLe]
            cases (eFind K₂ _ _).eval _ with
            | none => rfl
            | some bE =>
              dsimp only
              conv_lhs => rw [letV_eval_step]
              conv_rhs => rw [letV_eval_step]
              rw [kyberCheckE_min_eq _ _ _
                (by simpa only [scBase, stKyb, stKybList, Expr.eval, Env.get, v, Ext.wk] using hKyb) hLe]
  | true =>
    simp only [shcrAcceptPreRoC, coreAcceptPreRoC, ↓reduceIte]
    conv_lhs => rw [letV_eval_step, ite_eval]
    conv_rhs => rw [letV_eval_step, ite_eval]
    split_ifs with hHdr
    · rfl
    · conv_lhs => rw [ite_eval]
      conv_rhs => rw [ite_eval]
      rw [eAny_eq_of_le _ _ _
        (by simpa only [scBase, stUsedO, stUsedOList, Expr.eval, Env.get, v, Ext.wk] using hUsedO) hLe]
      split_ifs with hAny
      · rfl
      · conv_lhs => rw [bindV_eval]
        conv_rhs => rw [bindV_eval]
        rw [koskSenderOkC_min_eq S _ _ _
          (by simpa only [scBase, Expr.eval, Env.get, v, Ext.wk] using hInv) hc0 hLe]
        refine bind_congr_mem _ _ _ fun ok _ => ?_
        conv_lhs => rw [ite_eval]
        conv_rhs => rw [ite_eval]
        split_ifs with hOk
        · rfl
        · conv_lhs => rw [caseOptV_eval]
          conv_rhs => rw [caseOptV_eval]
          rw [eFind_eq_of_le _ _ _
            (by simpa only [scBase, stPrin, stPrinList, Expr.eval, Env.get, v, Ext.wk] using hPrin) hLe]
          cases (eFind K₂ _ _).eval _ with
          | none => rfl
          | some kE =>
            dsimp only
            conv_lhs => rw [caseOptV_eval]
            conv_rhs => rw [caseOptV_eval]
            rw [eFind_eq_of_le _ _ _
              (by simpa only [scBase, stSpks, stSpksList, Expr.eval, Env.get, v, Ext.wk] using hSpks) hLe]
            cases (eFind K₂ _ _).eval _ with
            | none => rfl
            | some bE =>
              dsimp only
              conv_lhs => rw [caseOptV_eval]
              conv_rhs => rw [caseOptV_eval]
              rw [eFind_eq_of_le _ _ _
                (by simpa only [scBase, stOpks, stOpksList, Expr.eval, Env.get, v, Ext.wk] using hOpks) hLe]
              cases (eFind K₂ _ _).eval _ with
              | none => rfl
              | some oE =>
                dsimp only
                conv_lhs => rw [ite_eval]
                conv_rhs => rw [ite_eval]
                split_ifs with hCons
                · rfl
                · conv_lhs => rw [letV_eval_step]
                  conv_rhs => rw [letV_eval_step]
                  rw [kyberCheckE_min_eq _ _ _
                    (by simpa only [scBase, stKyb, stKybList, Expr.eval, Env.get, v, Ext.wk] using hKyb) hLe]
                  conv_lhs => rw [bindV_eval]
                  conv_rhs => rw [bindV_eval]
                  refine bind_congr_mem _ _ _ fun acc _ => ?_
                  cases acc with
                  | none =>
                    rw [caseOptV_v0_none, caseOptV_v0_none]
                  | some aVal =>
                    rw [caseOptV_v0_some, caseOptV_v0_some]
                    conv_lhs => rw [bindV_eval]
                    conv_rhs => rw [bindV_eval]
                    refine bind_congr_mem _ _ _ fun ss? _ => ?_
                    cases ss? with
                    | none =>
                      rw [caseOptV_v0_none, caseOptV_v0_none]
                    | some ss =>
                      rw [caseOptV_v0_some, caseOptV_v0_some]
                      conv_lhs => rw [bindV_eval]
                      conv_rhs => rw [bindV_eval]
                      refine bind_congr_mem _ _ _ fun dh1 _ => ?_
                      conv_lhs => rw [bindV_eval]
                      conv_rhs => rw [bindV_eval]
                      refine bind_congr_mem _ _ _ fun dh2 _ => ?_
                      conv_lhs => rw [bindV_eval]
                      conv_rhs => rw [bindV_eval]
                      refine bind_congr_mem _ _ _ fun dh3 _ => ?_
                      conv_lhs => rw [bindV_eval]
                      conv_rhs => rw [bindV_eval]
                      refine bind_congr_mem _ _ _ fun dh4 _ => ?_
                      dsimp only [Comp.eval, Expr.eval, stUpd]
                      rw [eMap_eq_of_le _ _ _
                        (by simpa only [scBase, stOpks, stOpksList, Expr.eval, Env.get, v, Ext.wk] using hOpks) hLe]

private theorem shcrAcceptPreRoC_some_mem (S : Setup) (K : ℕ) (opk : Bool)
    (sL : shcrStTy.denote) (p : accQTy.denote) {mid : shcrAccMidTy.denote}
    (hMem : some mid ∈ support ((shcrAcceptPreRoC S K opk).eval (.cons sL (.cons p .nil)))) :
    stPrinList mid.2.1 = stPrinList sL.1 ∧ stSpksList mid.2.1 = stSpksList sL.1 ∧
    (stOpksList mid.2.1).length ≤ (stOpksList sL.1).length ∧
    stSessList mid.2.1 = stSessList sL.1 ∧ stRespsList mid.2.1 = stRespsList sL.1 ∧
    (stUsedOList mid.2.1).length ≤ (stUsedOList sL.1).length + 1 ∧
    (stUsedNList mid.2.1).length ≤ (stUsedNList sL.1).length + 1 ∧
    (stKybList mid.2.1).length ≤ (stKybList sL.1).length + 1 ∧
    stAdvList mid.2.1 = stAdvList sL.1 := by
  cases opk with
  | false =>
    simp only [shcrAcceptPreRoC, coreAcceptPreRoC, Bool.false_eq_true, ↓reduceIte] at hMem
    rw [letV_eval_step, ite_eval] at hMem
    split_ifs at hMem with hHdr
    · simp only [Comp.eval, Expr.eval, support_pure, Set.mem_singleton_iff] at hMem
      exact nomatch hMem
    · rw [ite_eval] at hMem
      split_ifs at hMem with hAny
      · simp only [Comp.eval, Expr.eval, support_pure, Set.mem_singleton_iff] at hMem
        exact nomatch hMem
      · rw [bindV_eval, mem_support_bind_iff] at hMem
        rcases hMem with ⟨ok, _, hMem⟩
        rw [ite_eval] at hMem
        split_ifs at hMem with hOk
        · simp only [Comp.eval, Expr.eval, support_pure, Set.mem_singleton_iff] at hMem
          exact nomatch hMem
        · rw [caseOptV_eval] at hMem
          cases hK : (eFind K _ _).eval _ with
          | none =>
            rw [hK] at hMem
            simp only [Comp.eval, Expr.eval, support_pure, Set.mem_singleton_iff] at hMem
            exact nomatch hMem
          | some kE =>
            rw [hK] at hMem; dsimp only at hMem
            rw [caseOptV_eval] at hMem
            cases hB : (eFind K _ _).eval _ with
            | none =>
              rw [hB] at hMem
              simp only [Comp.eval, Expr.eval, support_pure, Set.mem_singleton_iff] at hMem
              exact nomatch hMem
            | some bE =>
              rw [hB] at hMem; dsimp only at hMem
              rw [letV_eval_step] at hMem
              rw [bindV_eval, mem_support_bind_iff] at hMem
              rcases hMem with ⟨acc, _, hMem⟩
              cases acc with
              | none =>
                rw [caseOptV_v0_none] at hMem
                simp only [Comp.eval, Expr.eval, support_pure, Set.mem_singleton_iff] at hMem
                exact nomatch hMem
              | some aVal =>
                rw [caseOptV_v0_some] at hMem
                rw [bindV_eval, mem_support_bind_iff] at hMem
                rcases hMem with ⟨ss?, _, hMem⟩
                cases ss? with
                | none =>
                  rw [caseOptV_v0_none] at hMem
                  simp only [Comp.eval, Expr.eval, support_pure, Set.mem_singleton_iff] at hMem
                  exact nomatch hMem
                | some ss =>
                  rw [caseOptV_v0_some] at hMem
                  simp only [bindV_eval, Comp.eval, expr_some_eval, mem_support_bind_iff,
                    support_pure, Set.mem_singleton_iff, Option.some.injEq] at hMem
                  rcases hMem with ⟨_, _, _, _, _, _, hMidEq⟩
                  subst hMidEq
                  have hKyb := kyberCheckE_snd_len_le K
                    (stKyb (v (.zero : Var [keyIndStateTy, shcrStTy, accQTy] keyIndStateTy)))
                    (.pair (qK (v (.succ .zero : Var [shcrStTy, accQTy] accQTy)))
                      (.pair (hdPqspkId (qHdr (v (.succ .zero : Var [shcrStTy, accQTy] accQTy))))
                        (.pair (hdSpkId (qHdr (v (.succ .zero : Var [shcrStTy, accQTy] accQTy))))
                          (hdEkAPk (qHdr (v (.succ .zero : Var [shcrStTy, accQTy] accQTy)))))))
                    (.cons bE (.cons kE (.cons ok
                      (.cons ((scBase (v (.zero : Var [shcrStTy, accQTy] shcrStTy))).eval (.cons sL (.cons p .nil)))
                        (.cons sL (.cons p .nil))))))
                  simp only [stPrinList, stSpksList, stOpksList, stSessList, stRespsList,
                    stUsedOList, stUsedNList, stKybList, stAdvList, stKyb,
                    Expr.eval, v_eval_cons, v_zero_eval, List.length_cons] at hKyb ⊢
                  exact ⟨trivial, trivial, Nat.le_refl _, trivial, trivial,
                    Nat.le_succ _, Nat.le_refl _, hKyb, trivial⟩
  | true =>
    simp only [shcrAcceptPreRoC, coreAcceptPreRoC, ↓reduceIte] at hMem
    rw [letV_eval_step, ite_eval] at hMem
    split_ifs at hMem with hHdr
    · simp only [Comp.eval, Expr.eval, support_pure, Set.mem_singleton_iff] at hMem
      exact nomatch hMem
    · rw [ite_eval] at hMem
      split_ifs at hMem with hAny
      · simp only [Comp.eval, Expr.eval, support_pure, Set.mem_singleton_iff] at hMem
        exact nomatch hMem
      · rw [bindV_eval, mem_support_bind_iff] at hMem
        rcases hMem with ⟨ok, _, hMem⟩
        rw [ite_eval] at hMem
        split_ifs at hMem with hOk
        · simp only [Comp.eval, Expr.eval, support_pure, Set.mem_singleton_iff] at hMem
          exact nomatch hMem
        · rw [caseOptV_eval] at hMem
          cases hK : (eFind K _ _).eval _ with
          | none =>
            rw [hK] at hMem
            simp only [Comp.eval, Expr.eval, support_pure, Set.mem_singleton_iff] at hMem
            exact nomatch hMem
          | some kE =>
            rw [hK] at hMem; dsimp only at hMem
            rw [caseOptV_eval] at hMem
            cases hB : (eFind K _ _).eval _ with
            | none =>
              rw [hB] at hMem
              simp only [Comp.eval, Expr.eval, support_pure, Set.mem_singleton_iff] at hMem
              exact nomatch hMem
            | some bE =>
              rw [hB] at hMem; dsimp only at hMem
              rw [caseOptV_eval] at hMem
              cases hO : (eFind K _ _).eval _ with
              | none =>
                rw [hO] at hMem
                simp only [Comp.eval, Expr.eval, support_pure, Set.mem_singleton_iff] at hMem
                exact nomatch hMem
              | some oE =>
                rw [hO] at hMem; dsimp only at hMem
                rw [ite_eval] at hMem
                split_ifs at hMem with hCons
                · simp only [Comp.eval, Expr.eval, support_pure, Set.mem_singleton_iff] at hMem
                  exact nomatch hMem
                · rw [letV_eval_step] at hMem
                  rw [bindV_eval, mem_support_bind_iff] at hMem
                  rcases hMem with ⟨acc, _, hMem⟩
                  cases acc with
                  | none =>
                    rw [caseOptV_v0_none] at hMem
                    simp only [Comp.eval, Expr.eval, support_pure, Set.mem_singleton_iff] at hMem
                    exact nomatch hMem
                  | some aVal =>
                    rw [caseOptV_v0_some] at hMem
                    rw [bindV_eval, mem_support_bind_iff] at hMem
                    rcases hMem with ⟨ss?, _, hMem⟩
                    cases ss? with
                    | none =>
                      rw [caseOptV_v0_none] at hMem
                      simp only [Comp.eval, Expr.eval, support_pure, Set.mem_singleton_iff] at hMem
                      exact nomatch hMem
                    | some ss =>
                      rw [caseOptV_v0_some] at hMem
                      simp only [bindV_eval, Comp.eval, expr_some_eval, mem_support_bind_iff,
                        support_pure, Set.mem_singleton_iff, Option.some.injEq] at hMem
                      rcases hMem with ⟨_, _, _, _, _, _, _, _, hMidEq⟩
                      subst hMidEq
                      have hKyb := kyberCheckE_snd_len_le K
                        (stKyb (v (.zero : Var [keyIndStateTy, shcrStTy, accQTy] keyIndStateTy)))
                        (.pair (qK (v (.succ .zero : Var [shcrStTy, accQTy] accQTy)))
                          (.pair (hdPqspkId (qHdr (v (.succ .zero : Var [shcrStTy, accQTy] accQTy))))
                            (.pair (hdSpkId (qHdr (v (.succ .zero : Var [shcrStTy, accQTy] accQTy))))
                              (hdEkAPk (qHdr (v (.succ .zero : Var [shcrStTy, accQTy] accQTy)))))))
                        (.cons oE (.cons bE (.cons kE (.cons ok
                          (.cons ((scBase (v (.zero : Var [shcrStTy, accQTy] shcrStTy))).eval (.cons sL (.cons p .nil)))
                            (.cons sL (.cons p .nil)))))))
                      have hOpks := eMap_len_le K
                        (stOpks (v (.zero : Var [keyIndStateTy, shcrStTy, accQTy] keyIndStateTy)))
                        (fun entry => .ite (nat3Eq (.fst (v entry)) (qKJO (v (.succ .zero : Var [shcrStTy, accQTy] accQTy))))
                          (.pair (.fst (v entry)) (oeUpd (.snd (v entry)) (consumed := .bool true)))
                          (v entry))
                        (.cons oE (.cons bE (.cons kE (.cons ok
                          (.cons ((scBase (v (.zero : Var [shcrStTy, accQTy] shcrStTy))).eval (.cons sL (.cons p .nil)))
                            (.cons sL (.cons p .nil)))))))
                      simp only [stPrinList, stSpksList, stOpksList, stSessList, stRespsList,
                        stUsedOList, stUsedNList, stKybList, stAdvList, stOpks, stKyb,
                        Expr.eval, v_eval_cons, v_zero_eval, List.length_cons] at hKyb hOpks ⊢
                      exact ⟨trivial, trivial, hOpks, trivial, trivial,
                        Nat.le_refl _, Nat.le_succ _, hKyb, trivial⟩

private theorem shcrAcceptPostRoC_fuel_eq (S : Setup) {K₁ K₂ : ℕ} (opk : Bool)
    (dk : _root_.SignalPqxdh.LegacyCosted.drKeyT.denote) (roNew : roListLegacyTy.denote)
    (mid : shcrAccMidTy.denote) (sL : shcrStTy.denote) (p : accQTy.denote)
    (hPrin : (stPrinList sL.1).length ≤ K₁)
    (hSess : (stSessList mid.2.1).length ≤ K₁)
    (hSpks : (stSpksList mid.2.1).length ≤ K₁) (hLe : K₁ ≤ K₂) :
    (shcrAcceptPostRoC S K₁ opk).eval (.cons dk (.cons roNew (.cons mid (.cons sL (.cons p .nil))))) =
      (shcrAcceptPostRoC S K₂ opk).eval (.cons dk (.cons roNew (.cons mid (.cons sL (.cons p .nil))))) := by
  rcases mid with ⟨m0, ⟨b0, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10⟩, kE, bE, opkPk?⟩
  dsimp only [shcrAcceptPostRoC]
  simp only [letV_eval_step, bindV_eval, v, Ext.wk, Expr.eval, Env.get]
  rw [findHonestC_min_eq S _ _ _ (by simpa only [v, Ext.wk, Expr.eval, Env.get] using hPrin) hLe]
  refine congrArg₂ Bind.bind rfl (funext fun sh => ?_)
  rw [recordRespC_min_eq S _ _ (by simpa only [stSessList, Expr.eval, Env.get] using hSess) hLe]
  refine bind_congr_mem _ _ _ fun st2 hst2 => ?_
  obtain ⟨_, hSp2, _, _, _, _, _, _, _, _⟩ := recordRespC_mem_support S K₂ _ _ hst2
  have hSpks2 : st2.2.2.1.length ≤ K₁ := by
    simp only [stSpksList, Expr.eval, Env.get] at hSp2 hSpks
    rw [hSp2]
    exact hSpks
  rw [findHonestC_min_eq S _ _ _ (by simpa only [v, Ext.wk, Expr.eval, Env.get] using hPrin) hLe]
  refine congrArg₂ Bind.bind rfl (funext fun sh2 => ?_)
  rw [ite_eval, ite_eval]
  split_ifs with hN
  · rfl
  · rw [caseOptV_eval, caseOptV_eval, eFind_eq_of_le _ _ _
      (by simpa only [Expr.eval, Env.get] using hSpks2) hLe]

private theorem shcrAcceptPostRoC_fixSent_comm (S : Setup) (b : QueryBudget) (K : ℕ) (opk : Bool)
    (dk : _root_.SignalPqxdh.LegacyCosted.drKeyT.denote) (roNew : roListLegacyTy.denote)
    (mid : shcrAccMidTy.denote) (sL : shcrStTy.denote) (p : accQTy.denote) :
    Prod.map id (fixShcrLegacySent S b) <$>
        (shcrAcceptPostRoC S K opk).eval (.cons dk (.cons roNew (.cons mid (.cons sL (.cons p .nil))))) =
      (shcrAcceptPostRoC S K opk).eval
        (.cons dk (.cons roNew (.cons mid (.cons (fixShcrLegacySent S b sL) (.cons p .nil))))) := by
  rcases sL with ⟨bSt, tb, tpk, tsk, cnt, ir, rr, sidx, ch⟩
  rcases mid with ⟨m0, ⟨b0, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10⟩, kE, bE, opkPk?⟩
  have hKemDec : ∀ {Γ₁ Γ₂} (e₁ : Expr pqxdhOps Γ₁ _) (e₂ : Expr pqxdhOps Γ₂ _)
      (ρ₁ : Env Γ₁) (ρ₂ : Env Γ₂),
      e₁.eval ρ₁ = e₂.eval ρ₂ → (qKemDecaps e₁).eval ρ₁ = (qKemDecaps e₂).eval ρ₂ :=
    fun _ _ _ _ h => congrArg (fun x => (qKemDecaps (Γ := [_]) (.var .zero)).eval (.cons x .nil)) h
  dsimp only [shcrAcceptPostRoC, fixShcrLegacySent]
  simp only [map_eq_bind_pure_comp, Function.comp_def, letV_eval_step, bindV_eval, bind_assoc]
  refine congrArg₂ Bind.bind ?_ (funext fun sh => ?_)
  · rw [findHonestC_qHdr_eval S K, eq_comm, findHonestC_qHdr_eval S K]
    simp only [v, Ext.wk, Expr.eval, Env.get]
  · refine congrArg₂ Bind.bind ?_ (funext fun st2 => ?_)
    · rw [recordRespC_eval_congr S K, eq_comm, recordRespC_eval_congr S K]
      cases opk <;>
        simp only [Bool.false_eq_true, ↓reduceIte, qKJO, qK, qJ, qO, qHdr, isSomeE,
          v, Ext.wk, Expr.eval, Env.get]
    · refine congrArg₂ Bind.bind ?_ (funext fun sh2 => ?_)
      · rw [findHonestC_qHdr_eval S K, eq_comm, findHonestC_qHdr_eval S K]
        simp only [v, Ext.wk, Expr.eval, Env.get]
      · cases sh2 <;>
        · simp only [ite_eval, isNoneRespE,
            _root_.SignalPqxdh.Security.ReductionDsl.KeyInd.eCaseSum,
            _root_.SignalPqxdh.Security.ReductionDsl.KeyInd.eCaseOpt,
            rDrKey, rAccFresh, v, Ext.wk, Expr.eval, Env.get,
            Bool.false_eq_true, ↓reduceIte]
          rw [caseOptV_eval, caseOptV_eval]
          simp only [eFind, stSpks, scBase, nat2Eq, natEq, qK, qJ, Expr.eval, Env.get]
          cases List.find? _ (List.take K st2.2.2.1) with
          | none => simp only [Comp.eval, pure_bind, Expr.eval, Env.get]; rfl
          | some bE2 =>
            dsimp only
            simp only [bindV_eval, bind_assoc]
            refine congrArg₂ Bind.bind
              (hKemDec _ _ _ _ (by simp only [qHdr, Expr.eval, Env.get]))
              (funext fun ss? => ?_)
            cases ss? with
            | none =>
              rw [caseOptV_eval, caseOptV_eval]
              simp only [Comp.eval, pure_bind, Expr.eval, Env.get]; rfl
            | some ss =>
              rw [caseOptV_eval, caseOptV_eval]
              dsimp only [scUpd, scBase, scTB, scTPk, scTSk, scCnt, scIR, scRR, scSIdx, scChosen,
                qK, qJ, qHdr, sbPqspkPk, sbPqspkSk, hdKemCt]
              simp only [Comp.eval, pure_bind, Expr.eval, Env.get]; rfl

private theorem shcrAcceptPostRoC_mem_support (S : Setup) (K : ℕ) (opk : Bool)
    (dk : _root_.SignalPqxdh.LegacyCosted.drKeyT.denote) (roNew : roListLegacyTy.denote)
    (mid : shcrAccMidTy.denote) (sL : shcrStTy.denote) (p : accQTy.denote) {rsOut : SCS.denote}
    (hMem : rsOut ∈ support ((shcrAcceptPostRoC S K opk).eval
      (.cons dk (.cons roNew (.cons mid (.cons sL (.cons p .nil))))))) :
    stPrinList rsOut.2.1 = stPrinList mid.2.1 ∧ stSpksList rsOut.2.1 = stSpksList mid.2.1 ∧
    stOpksList rsOut.2.1 = stOpksList mid.2.1 ∧ stSessList rsOut.2.1 = stSessList mid.2.1 ∧
    (stRespsList rsOut.2.1).length = (stRespsList mid.2.1).length + 1 ∧
    stUsedOList rsOut.2.1 = stUsedOList mid.2.1 ∧ stUsedNList rsOut.2.1 = stUsedNList mid.2.1 ∧
    stKybList rsOut.2.1 = stKybList mid.2.1 ∧ stRoList rsOut.2.1 = roNew ∧
    stAdvList rsOut.2.1 = stAdvList mid.2.1 ∧
    rsOut.2.2.2.2.2.1 = sL.2.2.2.2.1 ∧
    rsOut.2.2.2.2.2.2.1 = sL.2.2.2.2.2.1 ∧
    rsOut.2.2.2.2.2.2.2.1.length ≤ sL.2.2.2.2.2.2.1.length + 1 := by
  rcases sL with ⟨bSt, tb, tpk, tsk, cnt, ir, rr, sidx, ch⟩
  rcases mid with ⟨m0, ⟨b0, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10⟩, kE, bE, opkPk?⟩
  dsimp only [shcrAcceptPostRoC] at hMem
  simp only [letV_eval_step, bindV_eval, mem_support_bind_iff, v, Ext.wk, Expr.eval, Env.get] at hMem
  rcases hMem with ⟨sh, _, st2, hst2Mem, sh2, _, hMem⟩
  obtain ⟨hP, hSp, hOp, hSe, hRe, hUO, hUN, hKy, hRo, hAd⟩ :=
    recordRespC_mem_support S K _ _ hst2Mem
  simp only [Expr.eval, Env.get] at hP hSp hOp hSe hRe hUO hUN hKy hRo hAd
  have hEnd : rsOut.2.1 = st2 ∧ rsOut.2.2.2.2.2.1 = cnt ∧
      rsOut.2.2.2.2.2.2.1 = ir ∧
      rsOut.2.2.2.2.2.2.2.1.length ≤ rr.length + 1 := by
    rw [ite_eval] at hMem
    split_ifs at hMem with hN
    · simp only [Comp.eval, support_pure, Set.mem_singleton_iff, Expr.eval, Env.get] at hMem
      rw [hMem]; exact ⟨rfl, rfl, rfl, Nat.le_succ _⟩
    · rw [caseOptV_eval] at hMem
      cases hF : (eFind K _ _).eval _ with
      | none =>
        rw [hF] at hMem
        simp only [Comp.eval, support_pure, Set.mem_singleton_iff, Expr.eval, Env.get] at hMem
        rw [hMem]; exact ⟨rfl, rfl, rfl, Nat.le_succ _⟩
      | some bE2 =>
        rw [hF] at hMem; dsimp only at hMem
        rw [bindV_eval, mem_support_bind_iff] at hMem
        rcases hMem with ⟨ss?, _, hMem⟩
        cases ss? with
        | none =>
          rw [caseOptV_eval] at hMem
          simp only [Comp.eval, support_pure, Set.mem_singleton_iff, Expr.eval, Env.get] at hMem
          rw [hMem]; exact ⟨rfl, rfl, rfl, Nat.le_succ _⟩
        | some ss =>
          rw [caseOptV_eval] at hMem
          simp only [Comp.eval, support_pure, Set.mem_singleton_iff, Expr.eval, Env.get] at hMem
          rw [hMem]; exact ⟨rfl, rfl, rfl, Nat.le_refl _⟩
  obtain ⟨hRBase, hRCnt, hRIr, hRRr⟩ := hEnd
  rw [hRBase]
  exact ⟨hP, hSp, hOp, hSe, hRe, hUO, hUN, hKy, hRo, hAd, hRCnt, hRIr, hRRr⟩

private theorem shcrAcceptB_false_eq_pre_ro_post (S : Setup) (K : ℕ)
    (sF : shcrStTy.denote) (p : accQTy.denote) :
    (shcrAcceptB S K false (Γ₁ := [shcrStTy, accQTy]) (Γ₂ := [shcrStTy, accQTy])
      (Δ := [shcrStTy, accQTy]) .zero (.succ .zero)).eval (.cons sF (.cons p .nil)) =
    (shcrAcceptPreRoC S K false).eval (.cons sF (.cons p .nil)) >>= fun pre =>
      match pre with
      | none => pure (Sum.inl (), sF)
      | some mid =>
          (hkdfOrRoC K true
            (Γ := [keyIndStateTy, _root_.SignalPqxdh.LegacyCosted.B 192])
            (Δ := [keyIndStateTy, _root_.SignalPqxdh.LegacyCosted.B 192])
            .zero (.var (.succ .zero))).eval (.cons sF.1 (.cons mid.1 .nil)) >>= fun dr =>
            (shcrAcceptPostRoC S K false).eval
              (.cons dr.1 (.cons dr.2 (.cons mid (.cons sF (.cons p .nil))))) := by
  rcases sF with ⟨⟨b0, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10⟩, tb, tpk, tsk, cnt, ir, rr, sidx, ch⟩
  have hNoneRet : ∀ {Γ : List PT} [Ext [keyIndStateTy, shcrStTy, accQTy] Γ] (env : Env Γ)
      (tl : Comp pqxdhOps _root_.SignalPqxdh.LegacyCosted.pqPrimIface (SCS :: [shcrStTy, accQTy]) SCS)
      (hst : (@v [keyIndStateTy, shcrStTy, accQTy] Γ keyIndStateTy _ .zero).eval env =
        (b0, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10)),
      ((Comp.ret (I := _root_.SignalPqxdh.LegacyCosted.pqPrimIface)
          (rs rNone (@v [keyIndStateTy, shcrStTy, accQTy] Γ keyIndStateTy _ .zero))).eval env >>=
        fun (g1 : RS.denote) =>
          (Comp.ret (I := _root_.SignalPqxdh.LegacyCosted.pqPrimIface)
            (.pair (.fst (v (.zero : Var (RS :: [shcrStTy, accQTy]) RS)))
              (scUpd (@v [shcrStTy, accQTy] (RS :: [shcrStTy, accQTy]) shcrStTy Ext.step .zero)
                (base := .snd (v (.zero : Var (RS :: [shcrStTy, accQTy]) RS)))))).eval
            (.cons (t := RS) g1
              (.cons ((b0, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10), tb, tpk, tsk, cnt, ir, rr, sidx, ch)
                (.cons p .nil))) >>=
        fun (r : SCS.denote) =>
          (Comp.ite (isNoneRespE (.fst (v (.zero : Var (SCS :: [shcrStTy, accQTy]) SCS))))
            (.ret (v (.zero : Var (SCS :: [shcrStTy, accQTy]) SCS))) tl).eval
            (.cons (t := SCS) r
              (.cons ((b0, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10), tb, tpk, tsk, cnt, ir, rr, sidx, ch)
                (.cons p .nil)))) =
      pure (Sum.inl (), ((b0, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10), tb, tpk, tsk, cnt, ir, rr, sidx, ch)) := by
    intro Γ _ env tl hst
    simp only [Comp.eval, pure_bind, rs, rNone, isNoneRespE,
      _root_.SignalPqxdh.Security.ReductionDsl.KeyInd.eCaseSum,
      Expr.eval, v_eval_cons, v_zero_eval, hst, ↓reduceIte]
  have hKemDec : ∀ {Γ₁ Γ₂} (e₁ : Expr pqxdhOps Γ₁ _) (e₂ : Expr pqxdhOps Γ₂ _)
      (ρ₁ : Env Γ₁) (ρ₂ : Env Γ₂),
      e₁.eval ρ₁ = e₂.eval ρ₂ → (qKemDecaps e₁).eval ρ₁ = (qKemDecaps e₂).eval ρ₂ :=
    fun _ _ _ _ h => congrArg (fun x => (qKemDecaps (Γ := [_]) (.var .zero)).eval (.cons x .nil)) h
  simp only [shcrAcceptB, onBase, acceptNoOpkB, shcrAcceptPreRoC, coreAcceptPreRoC,
    Bool.false_eq_true, ↓reduceIte]
  conv_lhs => rw [bindV_eval, bindV_eval, letV_eval_step]
  conv_rhs => arg 1; rw [letV_eval_step]
  simp only [bind_assoc]
  conv_lhs => arg 1; rw [ite_eval]
  conv_rhs => arg 1; rw [ite_eval]
  split_ifs with hHdr
  · conv_rhs => simp only [Comp.eval, Expr.eval, pure_bind]
    refine hNoneRet _ _ ?_; simp only [Expr.eval, v_zero_eval]
  · conv_lhs => arg 1; rw [ite_eval]
    conv_rhs => arg 1; rw [ite_eval]
    split_ifs with hAny
    · conv_rhs => simp only [Comp.eval, Expr.eval, pure_bind]
      refine hNoneRet _ _ ?_; simp only [Expr.eval, v_zero_eval]
    · conv_lhs => arg 1; rw [bindV_eval]
      conv_rhs => arg 1; rw [bindV_eval]
      simp only [bind_assoc]
      refine bind_congr_mem _ _ _ fun ok _ => ?_
      conv_lhs => arg 1; rw [ite_eval]
      conv_rhs => arg 1; rw [ite_eval]
      split_ifs with hOk
      · conv_rhs => simp only [Comp.eval, Expr.eval, pure_bind]
        refine hNoneRet _ _ ?_; simp only [Expr.eval, v_eval_cons, v_zero_eval]
      · conv_lhs => arg 1; rw [caseOptV_eval]
        conv_rhs => arg 1; rw [caseOptV_eval]
        cases (eFind K _ _).eval _ with
        | none =>
          conv_rhs => simp only [Comp.eval, Expr.eval, pure_bind]
          refine hNoneRet _ _ ?_; simp only [Expr.eval, v_eval_cons, v_zero_eval]
        | some kE =>
          dsimp only
          conv_lhs => arg 1; rw [caseOptV_eval]
          conv_rhs => arg 1; rw [caseOptV_eval]
          cases (eFind K _ _).eval _ with
          | none =>
            conv_rhs => simp only [Comp.eval, Expr.eval, pure_bind]
            refine hNoneRet _ _ ?_; simp only [Expr.eval, v_eval_cons, v_zero_eval]
          | some bE =>
            dsimp only
            conv_lhs => arg 1; rw [letV_eval_step]
            conv_rhs => arg 1; rw [letV_eval_step]
            conv_lhs => arg 1; rw [bindV_eval]
            conv_rhs => arg 1; rw [bindV_eval]
            simp only [bind_assoc]
            refine bind_congr_mem _ _ _ fun acc _ => ?_
            cases acc with
            | none =>
              conv_lhs => arg 1; rw [caseOptV_v0_none]
              conv_rhs => arg 1; rw [caseOptV_v0_none]
              conv_rhs => simp only [Comp.eval, Expr.eval, pure_bind]
              refine hNoneRet _ _ ?_; simp only [Expr.eval, v_eval_cons, v_zero_eval]
            | some aVal =>
              conv_lhs => arg 1; rw [caseOptV_v0_some]
              conv_rhs => arg 1; rw [caseOptV_v0_some]
              conv_lhs => arg 1; rw [bindV_eval]
              conv_rhs => arg 1; rw [bindV_eval]
              simp only [bind_assoc]
              refine bind_congr_mem _ _ _ fun ss? _ => ?_
              cases ss? with
              | none =>
                conv_lhs => arg 1; rw [caseOptV_v0_none]
                conv_rhs => arg 1; rw [caseOptV_v0_none]
                conv_rhs => simp only [Comp.eval, Expr.eval, pure_bind]
                refine hNoneRet _ _ ?_; simp only [Expr.eval, v_eval_cons, v_zero_eval]
              | some ss =>
                conv_lhs => arg 1; rw [caseOptV_v0_some]
                conv_rhs => arg 1; rw [caseOptV_v0_some]
                conv_lhs => arg 1; rw [bindV_eval]
                conv_rhs => arg 1; rw [bindV_eval]
                simp only [bind_assoc]
                refine bind_congr_mem _ _ _ fun dh1 _ => ?_
                conv_lhs => arg 1; rw [bindV_eval]
                conv_rhs => arg 1; rw [bindV_eval]
                simp only [bind_assoc]
                refine bind_congr_mem _ _ _ fun dh2 _ => ?_
                conv_lhs => arg 1; rw [bindV_eval]
                conv_rhs => arg 1; rw [bindV_eval]
                simp only [bind_assoc]
                refine bind_congr_mem _ _ _ fun dh3 _ => ?_
                conv_rhs => arg 1; simp only [Comp.eval, expr_some_eval]
                conv_rhs => rw [pure_bind]
                conv_lhs => arg 1; rw [bindV_eval]
                simp only [bind_assoc]
                conv_lhs => arg 1; rw [hkdfOrRoC_eval_congr K]
                conv_lhs => arg 1; simp only [scBase, buildSecretsE, Expr.eval, v_eval_cons, v_zero_eval]
                conv_rhs => arg 1; simp only [scBase, buildSecretsE, Expr.eval, v_eval_cons, v_zero_eval]
                refine bind_congr_mem _ _ _ fun dr _ => ?_
                generalize (buildSecretsE _ _ _ _ _).eval _ = secR
                simp only [shcrAcceptPostRoC, Bool.false_eq_true, ↓reduceIte]
                conv_lhs => arg 1; rw [letV_eval_step]
                conv_rhs =>
                  rw [letV_eval_step]; (conv => arg 2; simp only [v, Ext.wk, Expr.eval, Env.get])
                  rw [letV_eval_step]; (conv => arg 2; simp only [v, Ext.wk, Expr.eval, Env.get])
                  rw [letV_eval_step]; (conv => arg 2; simp only [v, Ext.wk, Expr.eval, Env.get])
                  rw [letV_eval_step]; (conv => arg 2; simp only [v, Ext.wk, Expr.eval, Env.get])
                  rw [letV_eval_step]
                conv_lhs => arg 1; rw [bindV_eval]
                conv_rhs => rw [bindV_eval]
                simp only [bind_assoc]
                refine congrArg₂ Bind.bind ?_ (funext fun sh => ?_)
                · rw [findHonestC_qHdr_eval S K, eq_comm, findHonestC_qHdr_eval S K, eq_comm]
                  simp only [v, Ext.wk, Expr.eval, Env.get]
                · conv_lhs => arg 1; rw [bindV_eval]
                  conv_rhs => rw [bindV_eval]
                  simp only [bind_assoc]
                  refine congrArg₂ Bind.bind ?_ (funext fun st2 => ?_)
                  · rw [recordRespC_eval_congr S K, eq_comm, recordRespC_eval_congr S K, eq_comm]
                    simp only [stKyb, qKJO, qHdr, qK, qJ, qO, isSomeE, v, Ext.wk, Expr.eval, Env.get]
                  · conv_lhs => arg 1; rw [bindV_eval]
                    conv_rhs => rw [bindV_eval]
                    simp only [bind_assoc]
                    refine congrArg₂ Bind.bind ?_ (funext fun sh2 => ?_)
                    · rw [findHonestC_qHdr_eval S K, eq_comm, findHonestC_qHdr_eval S K, eq_comm]
                      simp only [v, Ext.wk, Expr.eval, Env.get]
                    · conv_lhs => arg 1; rw [Comp.eval]
                      rw [pure_bind]
                      conv_lhs => arg 1; rw [Comp.eval]
                      rw [pure_bind]
                      conv_rhs => rw [letV_eval_step]
                      simp only [ite_eval, isNoneRespE,
                        _root_.SignalPqxdh.Security.ReductionDsl.KeyInd.eCaseSum,
                        _root_.SignalPqxdh.Security.ReductionDsl.KeyInd.eCaseOpt,
                        rs, rDrKey, rAccFresh, v, Ext.wk, Expr.eval, Env.get]
                      split_ifs with hN
                      · simp only [Comp.eval, Expr.eval, Env.get]
                      · rw [caseOptV_eval, caseOptV_eval]
                        simp only [eFind, nat2Eq, natEq, qK, qJ, Expr.eval, Env.get]
                        cases List.find? _ (List.take K st2.2.2.1) with
                        | none => simp only [Comp.eval, Expr.eval, Env.get]
                        | some bE2 =>
                          dsimp only
                          simp only [bindV_eval]
                          refine congrArg₂ Bind.bind
                            (hKemDec _ _ _ _ (by simp only [qHdr, Expr.eval, Env.get]))
                            (funext fun ss2? => ?_)
                          cases ss2? with
                          | none =>
                            rw [caseOptV_eval, caseOptV_eval]
                            simp only [Comp.eval, Expr.eval, Env.get]
                          | some ss2 =>
                            rw [caseOptV_eval, caseOptV_eval]
                            simp only [Comp.eval, qHdr, Expr.eval, Env.get]

private theorem shcrAcceptB_true_eq_pre_ro_post (S : Setup) (K : ℕ)
    (sF : shcrStTy.denote) (p : accQTy.denote) :
    (shcrAcceptB S K true (Γ₁ := [shcrStTy, accQTy]) (Γ₂ := [shcrStTy, accQTy])
      (Δ := [shcrStTy, accQTy]) .zero (.succ .zero)).eval (.cons sF (.cons p .nil)) =
    (shcrAcceptPreRoC S K true).eval (.cons sF (.cons p .nil)) >>= fun pre =>
      match pre with
      | none => pure (Sum.inl (), sF)
      | some mid =>
          (hkdfOrRoC K true
            (Γ := [keyIndStateTy, _root_.SignalPqxdh.LegacyCosted.B 192])
            (Δ := [keyIndStateTy, _root_.SignalPqxdh.LegacyCosted.B 192])
            .zero (.var (.succ .zero))).eval (.cons sF.1 (.cons mid.1 .nil)) >>= fun dr =>
            (shcrAcceptPostRoC S K true).eval
              (.cons dr.1 (.cons dr.2 (.cons mid (.cons sF (.cons p .nil))))) := by
  rcases sF with ⟨⟨b0, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10⟩, tb, tpk, tsk, cnt, ir, rr, sidx, ch⟩
  have hNoneRet : ∀ {Γ : List PT} [Ext [keyIndStateTy, shcrStTy, accQTy] Γ] (env : Env Γ)
      (tl : Comp pqxdhOps _root_.SignalPqxdh.LegacyCosted.pqPrimIface (SCS :: [shcrStTy, accQTy]) SCS)
      (hst : (@v [keyIndStateTy, shcrStTy, accQTy] Γ keyIndStateTy _ .zero).eval env =
        (b0, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10)),
      ((Comp.ret (I := _root_.SignalPqxdh.LegacyCosted.pqPrimIface)
          (rs rNone (@v [keyIndStateTy, shcrStTy, accQTy] Γ keyIndStateTy _ .zero))).eval env >>=
        fun (g1 : RS.denote) =>
          (Comp.ret (I := _root_.SignalPqxdh.LegacyCosted.pqPrimIface)
            (.pair (.fst (v (.zero : Var (RS :: [shcrStTy, accQTy]) RS)))
              (scUpd (@v [shcrStTy, accQTy] (RS :: [shcrStTy, accQTy]) shcrStTy Ext.step .zero)
                (base := .snd (v (.zero : Var (RS :: [shcrStTy, accQTy]) RS)))))).eval
            (.cons (t := RS) g1
              (.cons ((b0, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10), tb, tpk, tsk, cnt, ir, rr, sidx, ch)
                (.cons p .nil))) >>=
        fun (r : SCS.denote) =>
          (Comp.ite (isNoneRespE (.fst (v (.zero : Var (SCS :: [shcrStTy, accQTy]) SCS))))
            (.ret (v (.zero : Var (SCS :: [shcrStTy, accQTy]) SCS))) tl).eval
            (.cons (t := SCS) r
              (.cons ((b0, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10), tb, tpk, tsk, cnt, ir, rr, sidx, ch)
                (.cons p .nil)))) =
      pure (Sum.inl (), ((b0, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10), tb, tpk, tsk, cnt, ir, rr, sidx, ch)) := by
    intro Γ _ env tl hst
    simp only [Comp.eval, pure_bind, rs, rNone, isNoneRespE,
      _root_.SignalPqxdh.Security.ReductionDsl.KeyInd.eCaseSum,
      Expr.eval, v_eval_cons, v_zero_eval, hst, ↓reduceIte]
  have hKemDec : ∀ {Γ₁ Γ₂} (e₁ : Expr pqxdhOps Γ₁ _) (e₂ : Expr pqxdhOps Γ₂ _)
      (ρ₁ : Env Γ₁) (ρ₂ : Env Γ₂),
      e₁.eval ρ₁ = e₂.eval ρ₂ → (qKemDecaps e₁).eval ρ₁ = (qKemDecaps e₂).eval ρ₂ :=
    fun _ _ _ _ h => congrArg (fun x => (qKemDecaps (Γ := [_]) (.var .zero)).eval (.cons x .nil)) h
  simp only [shcrAcceptB, onBase, acceptOpkB, shcrAcceptPreRoC, coreAcceptPreRoC, ↓reduceIte]
  conv_lhs => rw [bindV_eval, bindV_eval, letV_eval_step]
  conv_rhs => arg 1; rw [letV_eval_step]
  simp only [bind_assoc]
  conv_lhs => arg 1; rw [ite_eval]
  conv_rhs => arg 1; rw [ite_eval]
  split_ifs with hHdr
  · conv_rhs => simp only [Comp.eval, Expr.eval, pure_bind]
    refine hNoneRet _ _ ?_; simp only [Expr.eval, v_zero_eval]
  · conv_lhs => arg 1; rw [ite_eval]
    conv_rhs => arg 1; rw [ite_eval]
    split_ifs with hAny
    · conv_rhs => simp only [Comp.eval, Expr.eval, pure_bind]
      refine hNoneRet _ _ ?_; simp only [Expr.eval, v_zero_eval]
    · conv_lhs => arg 1; rw [bindV_eval]
      conv_rhs => arg 1; rw [bindV_eval]
      simp only [bind_assoc]
      refine bind_congr_mem _ _ _ fun ok _ => ?_
      conv_lhs => arg 1; rw [ite_eval]
      conv_rhs => arg 1; rw [ite_eval]
      split_ifs with hOk
      · conv_rhs => simp only [Comp.eval, Expr.eval, pure_bind]
        refine hNoneRet _ _ ?_; simp only [Expr.eval, v_eval_cons, v_zero_eval]
      · conv_lhs => arg 1; rw [caseOptV_eval]
        conv_rhs => arg 1; rw [caseOptV_eval]
        cases (eFind K _ _).eval _ with
        | none =>
          conv_rhs => simp only [Comp.eval, Expr.eval, pure_bind]
          refine hNoneRet _ _ ?_; simp only [Expr.eval, v_eval_cons, v_zero_eval]
        | some kE =>
          dsimp only
          conv_lhs => arg 1; rw [caseOptV_eval]
          conv_rhs => arg 1; rw [caseOptV_eval]
          cases (eFind K _ _).eval _ with
          | none =>
            conv_rhs => simp only [Comp.eval, Expr.eval, pure_bind]
            refine hNoneRet _ _ ?_; simp only [Expr.eval, v_eval_cons, v_zero_eval]
          | some bE =>
            dsimp only
            conv_lhs => arg 1; rw [caseOptV_eval]
            conv_rhs => arg 1; rw [caseOptV_eval]
            cases (eFind K _ _).eval _ with
            | none =>
              conv_rhs => simp only [Comp.eval, Expr.eval, pure_bind]
              refine hNoneRet _ _ ?_; simp only [Expr.eval, v_eval_cons, v_zero_eval]
            | some oE =>
              dsimp only
              conv_lhs => arg 1; rw [ite_eval]
              conv_rhs => arg 1; rw [ite_eval]
              split_ifs with hCons
              · conv_rhs => simp only [Comp.eval, Expr.eval, pure_bind]
                refine hNoneRet _ _ ?_; simp only [Expr.eval, v_eval_cons, v_zero_eval]
              · conv_lhs => arg 1; rw [letV_eval_step]
                conv_rhs => arg 1; rw [letV_eval_step]
                conv_lhs => arg 1; rw [bindV_eval]
                conv_rhs => arg 1; rw [bindV_eval]
                simp only [bind_assoc]
                refine bind_congr_mem _ _ _ fun acc _ => ?_
                cases acc with
                | none =>
                  conv_lhs => arg 1; rw [caseOptV_v0_none]
                  conv_rhs => arg 1; rw [caseOptV_v0_none]
                  conv_rhs => simp only [Comp.eval, Expr.eval, pure_bind]
                  refine hNoneRet _ _ ?_; simp only [Expr.eval, v_eval_cons, v_zero_eval]
                | some aVal =>
                  conv_lhs => arg 1; rw [caseOptV_v0_some]
                  conv_rhs => arg 1; rw [caseOptV_v0_some]
                  conv_lhs => arg 1; rw [bindV_eval]
                  conv_rhs => arg 1; rw [bindV_eval]
                  simp only [bind_assoc]
                  refine bind_congr_mem _ _ _ fun ss? _ => ?_
                  cases ss? with
                  | none =>
                    conv_lhs => arg 1; rw [caseOptV_v0_none]
                    conv_rhs => arg 1; rw [caseOptV_v0_none]
                    conv_rhs => simp only [Comp.eval, Expr.eval, pure_bind]
                    refine hNoneRet _ _ ?_; simp only [Expr.eval, v_eval_cons, v_zero_eval]
                  | some ss =>
                    conv_lhs => arg 1; rw [caseOptV_v0_some]
                    conv_rhs => arg 1; rw [caseOptV_v0_some]
                    conv_lhs => arg 1; rw [bindV_eval]
                    conv_rhs => arg 1; rw [bindV_eval]
                    simp only [bind_assoc]
                    refine bind_congr_mem _ _ _ fun dh1 _ => ?_
                    conv_lhs => arg 1; rw [bindV_eval]
                    conv_rhs => arg 1; rw [bindV_eval]
                    simp only [bind_assoc]
                    refine bind_congr_mem _ _ _ fun dh2 _ => ?_
                    conv_lhs => arg 1; rw [bindV_eval]
                    conv_rhs => arg 1; rw [bindV_eval]
                    simp only [bind_assoc]
                    refine bind_congr_mem _ _ _ fun dh3 _ => ?_
                    conv_lhs => arg 1; rw [bindV_eval]
                    conv_rhs => arg 1; rw [bindV_eval]
                    simp only [bind_assoc]
                    refine bind_congr_mem _ _ _ fun dh4 _ => ?_
                    conv_rhs => arg 1; simp only [Comp.eval, expr_some_eval]
                    conv_rhs => rw [pure_bind]
                    conv_lhs => arg 1; rw [bindV_eval]
                    simp only [bind_assoc]
                    conv_lhs => arg 1; rw [hkdfOrRoC_eval_congr K]
                    conv_lhs => arg 1; simp only [scBase, buildSecretsE, Expr.eval, v_eval_cons, v_zero_eval]
                    conv_rhs => arg 1; simp only [scBase, buildSecretsE, Expr.eval, v_eval_cons, v_zero_eval]
                    refine bind_congr_mem _ _ _ fun dr _ => ?_
                    generalize (buildSecretsE _ _ _ _ _).eval _ = secR
                    simp only [shcrAcceptPostRoC, ↓reduceIte]
                    conv_lhs => arg 1; rw [letV_eval_step]
                    conv_rhs =>
                      rw [letV_eval_step]; (conv => arg 2; simp only [v, Ext.wk, Expr.eval, Env.get])
                      rw [letV_eval_step]; (conv => arg 2; simp only [v, Ext.wk, Expr.eval, Env.get])
                      rw [letV_eval_step]; (conv => arg 2; simp only [v, Ext.wk, Expr.eval, Env.get])
                      rw [letV_eval_step]; (conv => arg 2; simp only [v, Ext.wk, Expr.eval, Env.get])
                      rw [letV_eval_step]
                    conv_lhs => arg 1; rw [bindV_eval]
                    conv_rhs => rw [bindV_eval]
                    simp only [bind_assoc]
                    refine congrArg₂ Bind.bind ?_ (funext fun sh => ?_)
                    · rw [findHonestC_qHdr_eval S K, eq_comm, findHonestC_qHdr_eval S K, eq_comm]
                      simp only [v, Ext.wk, Expr.eval, Env.get]
                    · conv_lhs => arg 1; rw [bindV_eval]
                      conv_rhs => rw [bindV_eval]
                      simp only [bind_assoc]
                      refine congrArg₂ Bind.bind ?_ (funext fun st2 => ?_)
                      · rw [recordRespC_eval_congr S K, eq_comm, recordRespC_eval_congr S K, eq_comm]
                        simp only [stOpks, stKyb, eMap, nat3Eq, nat2Eq, natEq, oeUpd,
                          oeOpkSk, oeOpkPk, _root_.SignalPqxdh.Security.ReductionDsl.KeyInd.oeMk,
                          qKJO, qHdr, qK, qJ, qO, isSomeE, v, Ext.wk, Expr.eval, Env.get]
                      · conv_lhs => arg 1; rw [bindV_eval]
                        conv_rhs => rw [bindV_eval]
                        simp only [bind_assoc]
                        refine congrArg₂ Bind.bind ?_ (funext fun sh2 => ?_)
                        · rw [findHonestC_qHdr_eval S K, eq_comm, findHonestC_qHdr_eval S K, eq_comm]
                          simp only [v, Ext.wk, Expr.eval, Env.get]
                        · conv_lhs => arg 1; rw [Comp.eval]
                          rw [pure_bind]
                          conv_lhs => arg 1; rw [Comp.eval]
                          rw [pure_bind]
                          conv_rhs => rw [letV_eval_step]
                          simp only [ite_eval, isNoneRespE,
                            _root_.SignalPqxdh.Security.ReductionDsl.KeyInd.eCaseSum,
                            _root_.SignalPqxdh.Security.ReductionDsl.KeyInd.eCaseOpt,
                            rs, rDrKey, rAccFresh, v, Ext.wk, Expr.eval, Env.get]
                          split_ifs with hN
                          · simp only [Comp.eval, Expr.eval, Env.get]
                          · rw [caseOptV_eval, caseOptV_eval]
                            simp only [eFind, nat2Eq, natEq, qK, qJ, Expr.eval, Env.get]
                            cases List.find? _ (List.take K st2.2.2.1) with
                            | none => simp only [Comp.eval, Expr.eval, Env.get]
                            | some bE2 =>
                              dsimp only
                              simp only [bindV_eval]
                              refine congrArg₂ Bind.bind
                                (hKemDec _ _ _ _ (by simp only [qHdr, Expr.eval, Env.get]))
                                (funext fun ss2? => ?_)
                              cases ss2? with
                              | none =>
                                rw [caseOptV_eval, caseOptV_eval]
                                simp only [Comp.eval, Expr.eval, Env.get]
                              | some ss2 =>
                                rw [caseOptV_eval, caseOptV_eval]
                                simp only [Comp.eval, qHdr, Expr.eval, Env.get]

private theorem shcrAcceptB_eq_pre_ro_post (S : Setup) (K : ℕ) (opk : Bool)
    (sF : shcrStTy.denote) (p : accQTy.denote) :
    (shcrAcceptB S K opk (Γ₁ := [shcrStTy, accQTy]) (Γ₂ := [shcrStTy, accQTy])
      (Δ := [shcrStTy, accQTy]) .zero (.succ .zero)).eval (.cons sF (.cons p .nil)) =
    (shcrAcceptPreRoC S K opk).eval (.cons sF (.cons p .nil)) >>= fun pre =>
      match pre with
      | none => pure (Sum.inl (), sF)
      | some mid =>
          (hkdfOrRoC K true
            (Γ := [keyIndStateTy, _root_.SignalPqxdh.LegacyCosted.B 192])
            (Δ := [keyIndStateTy, _root_.SignalPqxdh.LegacyCosted.B 192])
            .zero (.var (.succ .zero))).eval (.cons sF.1 (.cons mid.1 .nil)) >>= fun dr =>
            (shcrAcceptPostRoC S K opk).eval
              (.cons dr.1 (.cons dr.2 (.cons mid (.cons sF (.cons p .nil))))) := by
  cases opk
  · exact shcrAcceptB_false_eq_pre_ro_post S K sF p
  · exact shcrAcceptB_true_eq_pre_ro_post S K sF p

private theorem shcrAccArmPost_inv_gen (S : Setup) (b : QueryBudget) (c : Fin 3 → ℕ)
    (N_o : ℕ) (opk : Bool) (sK : shcrKindStTy.denote)
    (k : Fin S.N_id) (j : Fin S.N_recv) (o : Fin N_o)
    (hdr : _root_.SignalPqxdh.HandshakeHdr)
    (t : KeyIndQuery S) (hOn : isKeyIndOnlineQuery (.inr t) = true)
    (hInv : ShcrSimInv S b c sK)
    (hPreEval :
      let f := keyIndCoreFuels S b
      let env0 : Env (S := pqAtomicSig)
        [.prod (.base (.fin S.N_id))
          (.prod (.base (.fin S.N_recv))
            (.prod (.base (.fin N_o)) (hdrT (ℓ := 0) (Pt := Empty)))),
         shcrKindStTy, (pqKeyIndCodec S).Q] :=
        .cons (k, (j, (o, hdrV hdr))) (.cons sK (.cons ((pqKeyIndCodec S).qenc t) .nil))
      (runAt2 (.fst .v1) (accPayToNatE N_o S .v0)
        (mapComp tlPrimKeyInd (shcrAcceptPreRoC S f.M_on opk))).eval env0 =
      embedVal (.opt shcrAccMidTy) <$>
        (shcrAcceptPreRoC S f.M_on opk).eval
          (.cons (projVal shcrStTy sK.1)
            (.cons (k.val, (j.val, (o.val, _root_.SignalPqxdh.LegacyCosted.hdrV hdr))) .nil)))
    (hMidMem : ∀ mid : shcrAccMidTy.denote,
      let f := keyIndCoreFuels S b
      let env0 : Env (S := pqAtomicSig)
        [.prod (.base (.fin S.N_id))
          (.prod (.base (.fin S.N_recv))
            (.prod (.base (.fin N_o)) (hdrT (ℓ := 0) (Pt := Empty)))),
         shcrKindStTy, (pqKeyIndCodec S).Q] :=
        .cons (k, (j, (o, hdrV hdr))) (.cons sK (.cons ((pqKeyIndCodec S).qenc t) .nil))
      let envMid := Env.cons (embedVal shcrAccMidTy mid)
        (.cons (embedVal (.opt shcrAccMidTy) (some mid)) env0)
      ∀ out ∈ support ((roShadowQueryC tlPrimKeyInd f.roCap
          (shcrRoListAtomicE (.fst .v3)) (.snd .v3) (.fst .v0)).eval envMid),
        RoCacheAvlInv (keyIndLoopBound b) f.roCap out.2.1 out.2.2 ∧
        out.2.1.length ≤ (stRoList (projVal shcrStTy sK.1).1).length + 1) :
    let f := keyIndCoreFuels S b
    let arm := shcrAccArmPostK S f.M_on f.roCap N_o opk
    ∀ vs' ∈ support (arm.eval
        (.cons (k, (j, (o, hdrV hdr))) (.cons sK (.cons ((pqKeyIndCodec S).qenc t) .nil)))),
      ShcrSimInv S b (bumpPred (keyIndSimPred S) c t) vs'.2 := by
  dsimp only
  set f := keyIndCoreFuels S b
  set env0 : Env (S := pqAtomicSig)
      [.prod (.base (.fin S.N_id))
        (.prod (.base (.fin S.N_recv))
          (.prod (.base (.fin N_o)) (hdrT (ℓ := 0) (Pt := Empty)))),
       shcrKindStTy, (pqKeyIndCodec S).Q] :=
    .cons (k, (j, (o, hdrV hdr))) (.cons sK (.cons ((pqKeyIndCodec S).qenc t) .nil))
  set p : accQTy.denote := (k.val, (j.val, (o.val, _root_.SignalPqxdh.LegacyCosted.hdrV hdr)))
  set sL : shcrStTy.denote := projVal shcrStTy sK.1
  have hsK1 : sK.1 = embedVal shcrStTy sL := (embedVal_projVal shcrStTy sK.1).symm
  have hbSt : projVal keyIndStateTy sK.1.1 = sL.1 := by
    rw [hsK1]; exact projVal_embedVal keyIndStateTy sL.1
  have hScsSnd : ∀ x : SCS.denote, (embedVal SCS x).2 = embedVal shcrStTy x.2 := fun _ => rfl
  have hStFst : ∀ x : shcrStTy.denote,
      (embedVal shcrStTy x).1 = embedVal keyIndStateTy x.1 := fun _ => rfl
  obtain ⟨h0, _, h2⟩ := bumpPred_online S c hOn
  have hCoreOnline : BaseOnlineLenInv c sL.1 := by
    simpa only [hbSt] using hInv.core_inv.online_len
  have hRoLen : (stRoList sL.1).length ≤ c 2 := by
    simpa only [hbSt] using hInv.core_inv.ro_len
  intro vs' hvs'
  dsimp only [shcrAccArmPostK] at hvs'
  rw [comp_bind_eval, hPreEval] at hvs'
  simp only [map_eq_bind_pure_comp, bind_assoc, pure_bind, Function.comp_def,
    mem_support_bind_iff] at hvs'
  rcases hvs' with ⟨pre, hPreMem, hvs'⟩
  cases pre with
  | none =>
    rw [caseOpt_v0_none _ _ (embedVal (.opt shcrAccMidTy) none) rfl] at hvs'
    simp only [Comp.eval, Expr.eval, Env.get, Expr.v2, env0,
      support_pure, Set.mem_singleton_iff] at hvs'
    subst hvs'
    refine ⟨⟨?_, ?_, ?_⟩, ?_, ?_, ?_⟩
    · exact BaseOnlineLenInv.mono_online hOn hInv.core_inv.online_len
    · rw [h2]; exact Nat.le_succ_of_le hInv.core_inv.ro_len
    · exact hInv.core_inv.ro_avl
    · rw [h0]; exact Nat.le_succ_of_le hInv.cnt_le
    · rw [h0]; exact Nat.le_succ_of_le hInv.ir_le
    · rw [h0]; exact Nat.le_succ_of_le hInv.rr_le
  | some mid =>
    obtain ⟨hMP, hMSp, hMOp, hMSe, hMRe, hMUO, hMUN, hMKy, hMAd⟩ :=
      shcrAcceptPreRoC_some_mem S f.M_on opk sL p hPreMem
    have hMemRo := hMidMem mid
    rw [caseOpt_v0_some _ _ (embedVal (.opt shcrAccMidTy) (some mid))
      (embedVal shcrAccMidTy mid) rfl, comp_bind_eval] at hvs'
    simp only [comp_bind_eval, mem_support_bind_iff] at hvs'
    rcases hvs' with ⟨out, hOutMem, v0, hv0Mem, hvs'⟩
    simp only [Comp.eval, Expr.eval, Env.get, Expr.v0, Expr.v1,
      support_pure, Set.mem_singleton_iff] at hvs'
    subst hvs'
    obtain ⟨hAvlOut, hLenOut⟩ := hMemRo out hOutMem
    rw [runAt5_eval, accPayToNatE_eval N_o S .v3 k j o hdr _
      (by simp only [env0, Expr.eval, Env.get, Expr.v3])] at hv0Mem
    simp only [env0, Expr.eval, Env.get, Expr.v0, Expr.v1, Expr.v4, hsK1] at hv0Mem
    rw [← embedVal_projVal _root_.SignalPqxdh.LegacyCosted.drKeyT out.1,
      ← embedVal_projVal roListLegacyTy out.2.1] at hv0Mem
    have hMC := mapComp_eval tlPrimKeyInd (shcrAcceptPostRoC S f.M_on opk)
      (shcrAcceptPostRoC_unsup S f.M_on opk)
      (.cons (projVal _root_.SignalPqxdh.LegacyCosted.drKeyT out.1)
        (.cons (projVal roListLegacyTy out.2.1) (.cons mid (.cons sL (.cons p .nil)))))
    have hEnv5 : embedEnv (.cons (projVal _root_.SignalPqxdh.LegacyCosted.drKeyT out.1)
        (.cons (projVal roListLegacyTy out.2.1) (.cons mid (.cons sL (.cons p .nil))))) =
      .cons (embedVal _root_.SignalPqxdh.LegacyCosted.drKeyT
          (projVal _root_.SignalPqxdh.LegacyCosted.drKeyT out.1))
        (.cons (embedVal roListLegacyTy (projVal roListLegacyTy out.2.1))
          (.cons (embedVal shcrAccMidTy mid)
            (.cons (embedVal shcrStTy sL) (.cons (embedVal accQTy p) .nil)))) := rfl
    rw [hEnv5] at hMC
    rw [hMC, map_eq_bind_pure_comp, mem_support_bind_iff] at hv0Mem
    rcases hv0Mem with ⟨rsOut, hrsMem, hv0Eq⟩
    simp only [Function.comp_def, support_pure, Set.mem_singleton_iff] at hv0Eq
    subst hv0Eq
    obtain ⟨hP, hSp, hOp, hSe, hRe, hUO, hUN, hKy, hRo', hAd, hCnt', hIr', hRr'⟩ :=
      shcrAcceptPostRoC_mem_support S f.M_on opk
        (projVal _root_.SignalPqxdh.LegacyCosted.drKeyT out.1)
        (projVal roListLegacyTy out.2.1) mid sL p hrsMem
    have hProjS' : projVal shcrStTy (embedVal SCS rsOut).2 = rsOut.2 := by
      rw [hScsSnd rsOut]; exact projVal_embedVal shcrStTy rsOut.2
    have hProjB' : projVal keyIndStateTy (embedVal SCS rsOut).2.1 = rsOut.2.1 := by
      rw [hScsSnd rsOut, hStFst rsOut.2]
      exact projVal_embedVal keyIndStateTy rsOut.2.1
    have hCntS : sL.2.2.2.2.1 ≤ c 0 := hInv.cnt_le
    have hIrS : sL.2.2.2.2.2.1.length ≤ c 0 := hInv.ir_le
    have hRrS : sL.2.2.2.2.2.2.1.length ≤ c 0 := hInv.rr_le
    refine ⟨⟨⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, ?_, ?_⟩, ?_, ?_, ?_⟩
    · rw [hProjB', hP, hMP, h0]; exact Nat.le_succ_of_le hCoreOnline.prin_le
    · rw [hProjB', hSp, hMSp, h0]; exact Nat.le_succ_of_le hCoreOnline.spks_le
    · rw [hProjB', hOp, h0]; exact Nat.le_succ_of_le (Nat.le_trans hMOp hCoreOnline.opks_le)
    · rw [hProjB', hSe, hMSe, h0]; exact Nat.le_succ_of_le hCoreOnline.sess_le
    · rw [hProjB', hRe, hMRe, h0]; exact Nat.succ_le_succ hCoreOnline.resps_le
    · rw [hProjB', hUO, h0]; exact Nat.le_trans hMUO (Nat.succ_le_succ hCoreOnline.usedO_le)
    · rw [hProjB', hUN, h0]; exact Nat.le_trans hMUN (Nat.succ_le_succ hCoreOnline.usedN_le)
    · rw [hProjB', hKy, h0]; exact Nat.le_trans hMKy (Nat.succ_le_succ hCoreOnline.kyb_le)
    · rw [hProjB', hAd, hMAd, h0]; exact Nat.le_succ_of_le hCoreOnline.adv_le
    · have hSum := hCoreOnline.counts_eq; omega
    · rw [hProjB', hRo', h2]
      have hRoLen' : (projVal roListLegacyTy out.2.1).length = out.2.1.length := by
        have := embedVal_projVal roListLegacyTy out.2.1
        rw [embedVal_roList_eq] at this; exact congrArg List.length this
      omega
    · rw [hProjB', hRo', embedVal_projVal]
      exact hAvlOut
    · rw [hProjS', hCnt', h0]; exact Nat.le_succ_of_le hCntS
    · rw [hProjS', hIr', h0]; exact Nat.le_succ_of_le hIrS
    · rw [hProjS', h0]; exact Nat.le_trans hRr' (Nat.succ_le_succ hRrS)

private theorem shcrAccArmPost_sim_gen (S : Setup) (b : QueryBudget) (c : Fin 3 → ℕ)
    (N_o : ℕ) (opk : Bool) (sK : shcrKindStTy.denote)
    (k : Fin S.N_id) (j : Fin S.N_recv) (o : Fin N_o)
    (hdr : _root_.SignalPqxdh.HandshakeHdr)
    (t : KeyIndQuery S) (hOn : isKeyIndOnlineQuery (.inr t) = true)
    (hInv : ShcrSimInv S b c sK)
    (hBound : ∀ idx, bumpPred (keyIndSimPred S) c t idx ≤ keyIndSimBounds b idx)
    (hRhs : activePostEval S b sK t =
      embedVal SCS <$>
        (shcrAcceptB S (keyIndLoopBound b) opk
          (Γ₁ := [shcrStTy, accQTy]) (Γ₂ := [shcrStTy, accQTy]) (Δ := [shcrStTy, accQTy])
          .zero (.succ .zero)).eval
          (.cons (fixShcrLegacySent S b (projVal shcrStTy sK.1))
            (.cons (k.val, (j.val, (o.val, _root_.SignalPqxdh.LegacyCosted.hdrV hdr))) .nil))) :
    let f := keyIndCoreFuels S b
    let arm := shcrAccArmPostK S f.M_on f.roCap N_o opk
    Prod.map id (forgetShcrKindActive S b) <$>
        arm.eval (.cons (k, (j, (o, hdrV hdr))) (.cons sK (.cons ((pqKeyIndCodec S).qenc t) .nil))) =
      activePostEval S b sK t ∧
    ∀ vs' ∈ support (arm.eval
        (.cons (k, (j, (o, hdrV hdr))) (.cons sK (.cons ((pqKeyIndCodec S).qenc t) .nil)))),
      ShcrSimInv S b (bumpPred (keyIndSimPred S) c t) vs'.2 := by
  dsimp only
  set f := keyIndCoreFuels S b
  set env0 : Env (S := pqAtomicSig)
      [.prod (.base (.fin S.N_id))
        (.prod (.base (.fin S.N_recv))
          (.prod (.base (.fin N_o)) (hdrT (ℓ := 0) (Pt := Empty)))),
       shcrKindStTy, (pqKeyIndCodec S).Q] :=
    .cons (k, (j, (o, hdrV hdr))) (.cons sK (.cons ((pqKeyIndCodec S).qenc t) .nil))
  set p : accQTy.denote := (k.val, (j.val, (o.val, _root_.SignalPqxdh.LegacyCosted.hdrV hdr)))
  set sL : shcrStTy.denote := projVal shcrStTy sK.1
  have hsK1 : sK.1 = embedVal shcrStTy sL := (embedVal_projVal shcrStTy sK.1).symm
  have hbSt : projVal keyIndStateTy sK.1.1 = sL.1 := by
    rw [hsK1]; exact projVal_embedVal keyIndStateTy sL.1
  have hEmbDR : ∀ d : (_root_.SignalPqxdh.LegacyCosted.drKeyT.prod roListLegacyTy).denote,
      embedVal (.prod _root_.SignalPqxdh.LegacyCosted.drKeyT roListLegacyTy) d =
        (embedVal _ d.1, embedVal roListLegacyTy d.2) := fun _ => rfl
  obtain ⟨hc0_1, hM_le⟩ := online_fuel_bounds S b c hOn hBound
  have hc0 : c 0 ≤ f.M_on := Nat.le_of_succ_le hc0_1
  have hc : ∀ idx, c idx ≤ keyIndSimBounds b idx := le_bounds_of_bump S b hBound
  have hCoreOnline : BaseOnlineLenInv c sL.1 := by
    simpa only [hbSt] using hInv.core_inv.online_len
  have hRoLen : (stRoList sL.1).length ≤ c 2 := by
    simpa only [hbSt] using hInv.core_inv.ro_len
  obtain ⟨hLtK, hRoom⟩ := ro_bounds_of_le S b hc hCoreOnline.counts_eq hRoLen
  have hPreEval :
      (runAt2 (.fst .v1) (accPayToNatE N_o S .v0)
        (mapComp tlPrimKeyInd (shcrAcceptPreRoC S f.M_on opk))).eval env0 =
      embedVal (.opt shcrAccMidTy) <$>
        (shcrAcceptPreRoC S f.M_on opk).eval (.cons sL (.cons p .nil)) := by
    rw [runAt2_eval, accPayToNatE_eval N_o S .v0 k j o hdr env0
      (by simp only [env0, Expr.eval, Env.get, Expr.v0])]
    simp only [env0, Expr.eval, Env.get, Expr.v1, hsK1]
    exact mapComp_eval tlPrimKeyInd (shcrAcceptPreRoC S f.M_on opk)
      (shcrAcceptPreRoC_unsup S f.M_on opk) (.cons sL (.cons p .nil))
  have hMidSim : ∀ mid : shcrAccMidTy.denote,
      let envMid := Env.cons (embedVal shcrAccMidTy mid)
        (.cons (embedVal (.opt shcrAccMidTy) (some mid)) env0)
      Prod.map id Prod.fst <$>
        (roShadowQueryC tlPrimKeyInd f.roCap
          (shcrRoListAtomicE (.fst .v3)) (.snd .v3) (.fst .v0)).eval envMid =
        embedVal (.prod _root_.SignalPqxdh.LegacyCosted.drKeyT roListLegacyTy) <$>
          (hkdfOrRoC (keyIndLoopBound b) true
            (Γ := [keyIndStateTy, _root_.SignalPqxdh.LegacyCosted.B 192])
            (Δ := [keyIndStateTy, _root_.SignalPqxdh.LegacyCosted.B 192])
            .zero (.var (.succ .zero))).eval (.cons sL.1 (.cons mid.1 .nil)) ∧
      ∀ out ∈ support ((roShadowQueryC tlPrimKeyInd f.roCap
          (shcrRoListAtomicE (.fst .v3)) (.snd .v3) (.fst .v0)).eval envMid),
        RoCacheAvlInv (keyIndLoopBound b) f.roCap out.2.1 out.2.2 ∧
        out.2.1.length ≤ (stRoList sL.1).length + 1 := by
    intro mid envMid
    have hRoEq : (shcrRoListAtomicE (.fst .v3)).eval envMid =
        embedVal roListLegacyTy (stRoList sL.1) := by
      rw [shcrRoListAtomicE_eval]
      simp only [envMid, env0, Expr.eval, Env.get, Expr.v3]; rfl
    have hRoAvl : RoCacheAvlInv (keyIndLoopBound b) f.roCap
        ((shcrRoListAtomicE (.fst .v3)).eval envMid)
        ((Expr.snd (O := pqAtomicOps) .v3).eval envMid) := by
      rw [hRoEq]
      simpa only [envMid, env0, Expr.eval, Env.get, Expr.v3, hbSt] using hInv.core_inv.ro_avl
    have hLenEq : ((shcrRoListAtomicE (.fst .v3)).eval envMid).length =
        (stRoList sL.1).length := by
      rw [hRoEq, embedVal_roList_eq]
    have hMid1 : (Expr.fst (O := pqAtomicOps) .v0).eval envMid =
        embedVal (_root_.SignalPqxdh.LegacyCosted.B 192) mid.1 := by
      simp only [envMid, Expr.eval, Env.get, Expr.v0]; rfl
    obtain ⟨hSim, hMem⟩ := roShadowQueryC_eval_sim tlPrimKeyInd envMid
      (keyIndLoopBound b) f.roCap (shcrRoListAtomicE (.fst .v3)) (.snd .v3) (.fst .v0) sL.1
      (hkdfOrRoC_unsup (keyIndLoopBound b)) hRoEq hRoAvl
      (by rw [hLenEq]; exact hLtK) (by rw [hLenEq]; exact hRoom)
    refine ⟨?_, fun out hOut => ?_⟩
    · rw [hSim, hMid1]
      exact mapComp_eval tlPrimKeyInd
        (hkdfOrRoC (keyIndLoopBound b) true
          (Γ := [keyIndStateTy, _root_.SignalPqxdh.LegacyCosted.B 192])
          (Δ := [keyIndStateTy, _root_.SignalPqxdh.LegacyCosted.B 192])
          .zero (.var (.succ .zero)))
        (hkdfOrRoC_unsup (keyIndLoopBound b)) (.cons sL.1 (.cons mid.1 .nil))
    · obtain ⟨hAvl', hL'⟩ := hMem out hOut
      exact ⟨hAvl', by simpa only [hLenEq] using hL'⟩
  refine ⟨?_, shcrAccArmPost_inv_gen S b c N_o opk sK k j o hdr t hOn hInv hPreEval
    (fun mid => (hMidSim mid).2)⟩
  rw [hRhs, shcrAcceptB_eq_pre_ro_post,
    shcrAcceptPreRoC_fixSent_eq S b (keyIndLoopBound b) opk sL p,
    ← shcrAcceptPreRoC_fuel_eq S opk sL p hCoreOnline hc0 hM_le]
  dsimp only [shcrAccArmPostK]
  rw [comp_bind_eval, hPreEval]
  simp only [map_eq_bind_pure_comp, bind_assoc, pure_bind, Function.comp_def]
  refine bind_congr_mem _ _ _ fun pre hPreMem => ?_
  cases pre with
  | none =>
    rw [caseOpt_v0_none _ _ (embedVal (.opt shcrAccMidTy) none) rfl]
    simp only [Comp.eval, Expr.eval, Env.get, Expr.v2, env0, pure_bind, atomicRNoneE]
    dsimp only [Prod.map, id]
    rw [forgetShcrKindActive_eq_embed]
    rfl
  | some mid =>
    obtain ⟨_, hMSp, _, hMSe, _, _, _, _, _⟩ :=
      shcrAcceptPreRoC_some_mem S f.M_on opk sL p hPreMem
    obtain ⟨hSimRo, _⟩ := hMidSim mid
    rw [caseOpt_v0_some _ _ (embedVal (.opt shcrAccMidTy) (some mid))
      (embedVal shcrAccMidTy mid) rfl, comp_bind_eval]
    simp only [comp_bind_eval, bind_assoc]
    have hStepPost : ∀ out : (embedTy _root_.SignalPqxdh.LegacyCosted.drKeyT).denote ×
          ((embedTy roListLegacyTy).denote × roAvlTy.denote),
        (do
          let v0 ← (runAt5 (.fst .v0) (.fst (.snd .v0)) .v1 (.fst .v4) (accPayToNatE N_o S .v3)
            (mapComp tlPrimKeyInd (shcrAcceptPostRoC S f.M_on opk))).eval
            (.cons out (.cons (embedVal shcrAccMidTy mid)
              (.cons (embedVal (.opt shcrAccMidTy) (some mid)) env0)))
          let x ← (Comp.ret (O := pqAtomicOps) (I := pqPrimIface)
            (.pair (.fst .v0) (.pair (.snd .v0) (.snd (.snd .v1))))).eval
            (.cons v0 (.cons out (.cons (embedVal shcrAccMidTy mid)
              (.cons (embedVal (.opt shcrAccMidTy) (some mid)) env0))))
          pure (Prod.map id (forgetShcrKindActive S b) x)) =
        (do
          let rsOut ← (shcrAcceptPostRoC S (keyIndLoopBound b) opk).eval
            (.cons (projVal _root_.SignalPqxdh.LegacyCosted.drKeyT out.1)
              (.cons (projVal roListLegacyTy out.2.1)
                (.cons mid (.cons (fixShcrLegacySent S b sL) (.cons p .nil)))))
          pure (embedVal SCS rsOut)) := by
      intro out
      simp only [Comp.eval, Expr.eval, Env.get, Expr.v0, Expr.v1, pure_bind]
      rw [runAt5_eval, accPayToNatE_eval N_o S .v3 k j o hdr _
        (by simp only [env0, Expr.eval, Env.get, Expr.v3])]
      simp only [env0, Expr.eval, Env.get, Expr.v4, hsK1]
      conv_lhs =>
        rw [← embedVal_projVal _root_.SignalPqxdh.LegacyCosted.drKeyT out.1,
          ← embedVal_projVal roListLegacyTy out.2.1]
      have hMC := mapComp_eval tlPrimKeyInd (shcrAcceptPostRoC S f.M_on opk)
        (shcrAcceptPostRoC_unsup S f.M_on opk)
        (.cons (projVal _root_.SignalPqxdh.LegacyCosted.drKeyT out.1)
          (.cons (projVal roListLegacyTy out.2.1) (.cons mid (.cons sL (.cons p .nil)))))
      have hEnv5 : embedEnv (.cons (projVal _root_.SignalPqxdh.LegacyCosted.drKeyT out.1)
          (.cons (projVal roListLegacyTy out.2.1) (.cons mid (.cons sL (.cons p .nil))))) =
        .cons (embedVal _root_.SignalPqxdh.LegacyCosted.drKeyT
            (projVal _root_.SignalPqxdh.LegacyCosted.drKeyT out.1))
          (.cons (embedVal roListLegacyTy (projVal roListLegacyTy out.2.1))
            (.cons (embedVal shcrAccMidTy mid)
              (.cons (embedVal shcrStTy sL) (.cons (embedVal accQTy p) .nil)))) := rfl
      rw [hEnv5] at hMC
      rw [hMC]
      have hFix := shcrAcceptPostRoC_fixSent_comm S b f.M_on opk
        (projVal _root_.SignalPqxdh.LegacyCosted.drKeyT out.1)
        (projVal roListLegacyTy out.2.1) mid sL p
      have hFixBSt : (fixShcrLegacySent S b sL).1 = sL.1 := by
        rcases sL with ⟨_, _, _, _, _, _, _, _, _⟩; rfl
      have hFuel := shcrAcceptPostRoC_fuel_eq S opk
        (projVal _root_.SignalPqxdh.LegacyCosted.drKeyT out.1)
        (projVal roListLegacyTy out.2.1) mid (fixShcrLegacySent S b sL) p
        (by rw [hFixBSt]; exact Nat.le_trans hCoreOnline.prin_le hc0)
        (by rw [hMSe]; exact Nat.le_trans hCoreOnline.sess_le hc0)
        (by rw [hMSp]; exact Nat.le_trans hCoreOnline.spks_le hc0) hM_le
      rw [← hFuel, ← hFix]
      simp only [map_eq_bind_pure_comp, bind_assoc, pure_bind, Function.comp_def]; rfl
    conv_lhs => arg 2; ext out; rw [hStepPost]
    have hBindFst :
        (do
          let out ← (roShadowQueryC tlPrimKeyInd f.roCap
            (shcrRoListAtomicE (.fst .v3)) (.snd .v3) (.fst .v0)).eval
            (.cons (embedVal shcrAccMidTy mid)
              (.cons (embedVal (.opt shcrAccMidTy) (some mid)) env0))
          let rsOut ← (shcrAcceptPostRoC S (keyIndLoopBound b) opk).eval
            (.cons (projVal _root_.SignalPqxdh.LegacyCosted.drKeyT out.1)
              (.cons (projVal roListLegacyTy out.2.1)
                (.cons mid (.cons (fixShcrLegacySent S b sL) (.cons p .nil)))))
          pure (embedVal SCS rsOut)) =
        (do
          let drK ← Prod.map id Prod.fst <$>
            (roShadowQueryC tlPrimKeyInd f.roCap
              (shcrRoListAtomicE (.fst .v3)) (.snd .v3) (.fst .v0)).eval
              (.cons (embedVal shcrAccMidTy mid)
                (.cons (embedVal (.opt shcrAccMidTy) (some mid)) env0))
          let rsOut ← (shcrAcceptPostRoC S (keyIndLoopBound b) opk).eval
            (.cons (projVal _root_.SignalPqxdh.LegacyCosted.drKeyT drK.1)
              (.cons (projVal roListLegacyTy drK.2)
                (.cons mid (.cons (fixShcrLegacySent S b sL) (.cons p .nil)))))
          pure (embedVal SCS rsOut)) := by
      simp only [map_eq_bind_pure_comp, bind_assoc, pure_bind, Function.comp_def, Prod.map]; rfl
    rw [hBindFst, hSimRo]
    have hFixBSt : (fixShcrLegacySent S b sL).1 = sL.1 := by
      rcases sL with ⟨_, _, _, _, _, _, _, _, _⟩; rfl
    rw [hFixBSt]
    simp only [map_eq_bind_pure_comp, bind_assoc, pure_bind, Function.comp_def,
      hEmbDR, projVal_embedVal]

theorem shcrAccOpkArmPost_sim (S : Setup) (b : QueryBudget) (c : Fin 3 → ℕ)
    (sK : shcrKindStTy.denote) (k : Fin S.N_id) (j : Fin S.N_recv) (o : Fin S.N_opk)
    (hdr : _root_.SignalPqxdh.HandshakeHdr)
    (hInv : ShcrSimInv S b c sK)
    (hBound : ∀ idx, bumpPred (keyIndSimPred S) c (.acceptOPK k j o hdr) idx ≤ keyIndSimBounds b idx) :
    let f := keyIndCoreFuels S b
    let t : KeyIndQuery S := .acceptOPK k j o hdr
    let arm := shcrAccArmPostK S f.M_on f.roCap S.N_opk true
    Prod.map id (forgetShcrKindActive S b) <$>
        arm.eval (.cons (k, (j, (o, hdrV hdr))) (.cons sK (.cons ((pqKeyIndCodec S).qenc t) .nil))) =
      activePostEval S b sK t ∧
    ∀ vs' ∈ support (arm.eval
        (.cons (k, (j, (o, hdrV hdr))) (.cons sK (.cons ((pqKeyIndCodec S).qenc t) .nil)))),
      ShcrSimInv S b (bumpPred (keyIndSimPred S) c t) vs'.2 := by
  intro f t arm
  have hOn : isKeyIndOnlineQuery (.inr t) = true := by simp [isKeyIndOnlineQuery, t]
  refine shcrAccArmPost_sim_gen S b c S.N_opk true sK k j o hdr t hOn hInv hBound ?_
  simp only [activePostEval, shcr1KeyActivePostC, shcrActivePostTailC,
    _root_.SignalPqxdh.Security.ReductionDsl.KeyInd.caseSumV,
    _root_.SignalPqxdh.LegacyCosted.keyIndCodec, _root_.SignalPqxdh.LegacyCosted.keyIndQenc,
    Comp.eval, v_eval_cons, v_zero_eval, t]
  rw [shcrAcceptB_eval_congr S (keyIndLoopBound b) true]
  simp only [v_eval_cons, v_zero_eval]

theorem shcrAccNoOpkArmPost_sim (S : Setup) (b : QueryBudget) (c : Fin 3 → ℕ)
    (sK : shcrKindStTy.denote) (k : Fin S.N_id) (j : Fin S.N_recv) (l : Fin S.N_no_opk)
    (hdr : _root_.SignalPqxdh.HandshakeHdr)
    (hInv : ShcrSimInv S b c sK)
    (hBound : ∀ idx, bumpPred (keyIndSimPred S) c (.acceptNoOPK k j l hdr) idx ≤ keyIndSimBounds b idx) :
    let f := keyIndCoreFuels S b
    let t : KeyIndQuery S := .acceptNoOPK k j l hdr
    let arm := shcrAccArmPostK S f.M_on f.roCap S.N_no_opk false
    Prod.map id (forgetShcrKindActive S b) <$>
        arm.eval (.cons (k, (j, (l, hdrV hdr))) (.cons sK (.cons ((pqKeyIndCodec S).qenc t) .nil))) =
      activePostEval S b sK t ∧
    ∀ vs' ∈ support (arm.eval
        (.cons (k, (j, (l, hdrV hdr))) (.cons sK (.cons ((pqKeyIndCodec S).qenc t) .nil)))),
      ShcrSimInv S b (bumpPred (keyIndSimPred S) c t) vs'.2 := by
  intro f t arm
  have hOn : isKeyIndOnlineQuery (.inr t) = true := by simp [isKeyIndOnlineQuery, t]
  refine shcrAccArmPost_sim_gen S b c S.N_no_opk false sK k j l hdr t hOn hInv hBound ?_
  simp only [activePostEval, shcr1KeyActivePostC, shcrActivePostTailC,
    _root_.SignalPqxdh.Security.ReductionDsl.KeyInd.caseSumV,
    _root_.SignalPqxdh.LegacyCosted.keyIndCodec, _root_.SignalPqxdh.LegacyCosted.keyIndQenc,
    Comp.eval, v_eval_cons, v_zero_eval, t]
  rw [shcrAcceptB_eval_congr S (keyIndLoopBound b) false]
  simp only [v_eval_cons, v_zero_eval]

private theorem finSidToNatExpr_v0_eval (S : Setup) {B C : Ty pqAtomicSig}
    (sid : _root_.SignalPqxdh.SessionId S) (bVal : B.denote) (cVal : C.denote) :
    (finSidToNatExpr S (Γ := [sidT (ℓ := 0) (Pt := Empty) S, B, C]) .v0).eval
      (.cons (sidV sid) (.cons bVal (.cons cVal .nil))) =
    embedVal _root_.SignalPqxdh.LegacyCosted.sidT (_root_.SignalPqxdh.LegacyCosted.sidV sid) := by
  cases sid <;> rfl

private theorem testB_eval_congr (K : ℕ) {Γ₁ Γ₂ Δ : List PT}
    (st : Var Γ₁ keyIndStateTy) (sid : Var Γ₂ _root_.SignalPqxdh.LegacyCosted.sidT)
    [Ext Γ₁ Δ] [Ext Γ₂ Δ] (env : Env Δ) :
    (testB K (Δ := Δ) st sid).eval env =
      (testB K (Γ₁ := [keyIndStateTy, _root_.SignalPqxdh.LegacyCosted.sidT])
        (Γ₂ := [keyIndStateTy, _root_.SignalPqxdh.LegacyCosted.sidT])
        (Δ := [keyIndStateTy, _root_.SignalPqxdh.LegacyCosted.sidT])
        .zero (.succ .zero)).eval
        (.cons ((v st).eval env) (.cons ((v sid).eval env) .nil)) := by
  have hRen : compRename (ren2Var (Δ := Δ) st sid)
      (testB K (Γ₁ := [keyIndStateTy, _root_.SignalPqxdh.LegacyCosted.sidT])
        (Γ₂ := [keyIndStateTy, _root_.SignalPqxdh.LegacyCosted.sidT])
        (Δ := [keyIndStateTy, _root_.SignalPqxdh.LegacyCosted.sidT])
        .zero (.succ .zero)) = testB K (Δ := Δ) st sid := rfl
  rw [← hRen]
  exact compRename_eval _ (ren2Var (Δ := Δ) st sid) _ env (ren2Var_env_get st sid env)

private abbrev keySidCtx : List PT := [keyIndStateTy, _root_.SignalPqxdh.LegacyCosted.sidT]

private theorem revealB_eval_congr (K : ℕ) {Γ₁ Γ₂ Δ : List PT}
    (st : Var Γ₁ keyIndStateTy) (sid : Var Γ₂ _root_.SignalPqxdh.LegacyCosted.sidT)
    [Ext Γ₁ Δ] [Ext Γ₂ Δ] (env : Env Δ) :
    (revealB K (Δ := Δ) st sid).eval env =
      (revealB K (Γ₁ := keySidCtx) (Γ₂ := keySidCtx) (Δ := keySidCtx) .zero (.succ .zero)).eval
        (.cons ((v st).eval env) (.cons ((v sid).eval env) .nil)) := by
  let c := revealB K (Γ₁ := keySidCtx) (Γ₂ := keySidCtx) (Δ := keySidCtx) .zero (.succ .zero)
  have hRen : compRename (ren2Var (Δ := Δ) st sid) c = revealB K (Δ := Δ) st sid := rfl
  rw [← hRen]
  exact compRename_eval c (ren2Var (Δ := Δ) st sid) _ env (ren2Var_env_get st sid env)

private abbrev shcrSidCtx : List PT := [shcrStTy, _root_.SignalPqxdh.LegacyCosted.sidT]

private theorem onBaseTestB_eval_congr (K : ℕ) {Γ₁ Γ₂ Δ : List PT}
    (s : Var Γ₁ shcrStTy) (sid : Var Γ₂ _root_.SignalPqxdh.LegacyCosted.sidT)
    [Ext Γ₁ Δ] [Ext Γ₂ Δ] (env : Env Δ) :
    (onBase (Δ := Δ) s fun g => testB K g sid).eval env =
      (onBase (Γ₁ := shcrSidCtx) (Δ := shcrSidCtx) .zero
        fun g => testB K g
          (.succ (.succ .zero) : Var [keyIndStateTy, shcrStTy, _root_.SignalPqxdh.LegacyCosted.sidT] _)).eval
        (.cons ((v s).eval env) (.cons ((v sid).eval env) .nil)) := by
  let c := onBase (Γ₁ := shcrSidCtx) (Δ := shcrSidCtx) .zero
    fun g => testB K g
      (.succ (.succ .zero) : Var [keyIndStateTy, shcrStTy, _root_.SignalPqxdh.LegacyCosted.sidT] _)
  have hRen : compRename (ren2Var (Δ := Δ) s sid) c = (onBase (Δ := Δ) s fun g => testB K g sid) := rfl
  rw [← hRen]
  exact compRename_eval c (ren2Var (Δ := Δ) s sid) _ env (ren2Var_env_get s sid env)

private theorem onBaseRevealB_eval_congr (K : ℕ) {Γ₁ Γ₂ Δ : List PT}
    (s : Var Γ₁ shcrStTy) (sid : Var Γ₂ _root_.SignalPqxdh.LegacyCosted.sidT)
    [Ext Γ₁ Δ] [Ext Γ₂ Δ] (env : Env Δ) :
    (onBase (Δ := Δ) s fun g => revealB K g sid).eval env =
      (onBase (Γ₁ := shcrSidCtx) (Δ := shcrSidCtx) .zero
        fun g => revealB K g
          (.succ (.succ .zero) : Var [keyIndStateTy, shcrStTy, _root_.SignalPqxdh.LegacyCosted.sidT] _)).eval
        (.cons ((v s).eval env) (.cons ((v sid).eval env) .nil)) := by
  let c := onBase (Γ₁ := shcrSidCtx) (Δ := shcrSidCtx) .zero
    fun g => revealB K g
      (.succ (.succ .zero) : Var [keyIndStateTy, shcrStTy, _root_.SignalPqxdh.LegacyCosted.sidT] _)
  have hRen : compRename (ren2Var (Δ := Δ) s sid) c = (onBase (Δ := Δ) s fun g => revealB K g sid) := rfl
  rw [← hRen]
  exact compRename_eval c (ren2Var (Δ := Δ) s sid) _ env (ren2Var_env_get s sid env)

private theorem baseOnlineLenInv_of_le_sess_resps {S : Setup} {c : Fin 3 → ℕ} {t : KeyIndQuery S}
    (hOn : isKeyIndOnlineQuery (.inr t) = true) {bSt bSt' : keyIndStateTy.denote}
    (hInv : BaseOnlineLenInv c bSt)
    (hP : stPrinList bSt' = stPrinList bSt) (hSp : stSpksList bSt' = stSpksList bSt)
    (hOp : stOpksList bSt' = stOpksList bSt)
    (hSe : (stSessList bSt').length ≤ (stSessList bSt).length)
    (hRe : (stRespsList bSt').length ≤ (stRespsList bSt).length)
    (hUO : stUsedOList bSt' = stUsedOList bSt) (hUN : stUsedNList bSt' = stUsedNList bSt)
    (hKy : stKybList bSt' = stKybList bSt) (hAd : stAdvList bSt' = stAdvList bSt) :
    BaseOnlineLenInv (bumpPred (keyIndSimPred S) c t) bSt' := by
  obtain ⟨h0, h1, h2⟩ := bumpPred_online S c hOn
  have hSum := hInv.counts_eq
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, by rw [h0, h1, h2]; omega⟩
  · rw [hP, h0]; exact Nat.le_succ_of_le hInv.prin_le
  · rw [hSp, h0]; exact Nat.le_succ_of_le hInv.spks_le
  · rw [hOp, h0]; exact Nat.le_succ_of_le hInv.opks_le
  · rw [h0]; exact Nat.le_trans hSe (Nat.le_succ_of_le hInv.sess_le)
  · rw [h0]; exact Nat.le_trans hRe (Nat.le_succ_of_le hInv.resps_le)
  · rw [hUO, h0]; exact Nat.le_succ_of_le hInv.usedO_le
  · rw [hUN, h0]; exact Nat.le_succ_of_le hInv.usedN_le
  · rw [hKy, h0]; exact Nat.le_succ_of_le hInv.kyb_le
  · rw [hAd, h0]; exact Nat.le_succ_of_le hInv.adv_le

private theorem stUpd_resps_mem {S : Setup} {c : Fin 3 → ℕ} {t : KeyIndQuery S}
    (hOn : isKeyIndOnlineQuery (.inr t) = true) {bSt : keyIndStateTy.denote}
    (hInv : BaseOnlineLenInv c bSt) (resps' : (Ty.list _root_.SignalPqxdh.Security.ReductionDsl.KeyInd.keyIndRespEntryTy).denote)
    (hRe : resps'.length ≤ (stRespsList bSt).length) :
    let bSt' : keyIndStateTy.denote :=
      (bSt.1, bSt.2.1, bSt.2.2.1, bSt.2.2.2.1, bSt.2.2.2.2.1, resps',
       bSt.2.2.2.2.2.2.1, bSt.2.2.2.2.2.2.2.1, bSt.2.2.2.2.2.2.2.2.1,
       bSt.2.2.2.2.2.2.2.2.2.1, bSt.2.2.2.2.2.2.2.2.2.2)
    BaseOnlineLenInv (bumpPred (keyIndSimPred S) c t) bSt' ∧ stRoList bSt' = stRoList bSt :=
  ⟨baseOnlineLenInv_of_le_sess_resps hOn hInv rfl rfl rfl (Nat.le_refl _) hRe rfl rfl rfl rfl, rfl⟩

private theorem stUpd_sess_mem {S : Setup} {c : Fin 3 → ℕ} {t : KeyIndQuery S}
    (hOn : isKeyIndOnlineQuery (.inr t) = true) {bSt : keyIndStateTy.denote}
    (hInv : BaseOnlineLenInv c bSt) (sess' : (Ty.list _root_.SignalPqxdh.Security.ReductionDsl.KeyInd.keyIndSessionEntryTy).denote)
    (hSe : sess'.length ≤ (stSessList bSt).length) :
    let bSt' : keyIndStateTy.denote :=
      (bSt.1, bSt.2.1, bSt.2.2.1, bSt.2.2.2.1, sess', bSt.2.2.2.2.2.1,
       bSt.2.2.2.2.2.2.1, bSt.2.2.2.2.2.2.2.1, bSt.2.2.2.2.2.2.2.2.1,
       bSt.2.2.2.2.2.2.2.2.2.1, bSt.2.2.2.2.2.2.2.2.2.2)
    BaseOnlineLenInv (bumpPred (keyIndSimPred S) c t) bSt' ∧ stRoList bSt' = stRoList bSt :=
  ⟨baseOnlineLenInv_of_le_sess_resps hOn hInv rfl rfl rfl hSe (Nat.le_refl _) rfl rfl rfl rfl, rfl⟩

private abbrev testRevCtx : List PT := [keyIndStateTy, shcrStTy, _root_.SignalPqxdh.LegacyCosted.sidT]

private theorem v_succ2_eval {A B C : PT} (a : A.denote) (b : B.denote) (c : C.denote) :
    (v (.succ (.succ .zero) : Var [A, B, C] C)).eval (.cons a (.cons b (.cons c .nil))) = c := rfl

private theorem testB_mem_support {S : Setup} {c : Fin 3 → ℕ} {t : KeyIndQuery S} (K : ℕ)
    (hOn : isKeyIndOnlineQuery (.inr t) = true) (bSt : keyIndStateTy.denote)
    (sL : shcrStTy.denote) (p : _root_.SignalPqxdh.LegacyCosted.sidT.denote)
    (hBInv : BaseOnlineLenInv c bSt) :
    ∀ r ∈ support ((testB K (.zero : Var testRevCtx _)
        (.succ (.succ .zero) : Var testRevCtx _)).eval
        (.cons bSt (.cons sL (.cons p .nil)))),
      BaseOnlineLenInv (bumpPred (keyIndSimPred S) c t) r.2 ∧ stRoList r.2 = stRoList bSt := by
  intro r hr
  simp only [testB, caseOptV, Comp.eval] at hr
  split_ifs at hr with hNot
  · simp only [support_pure, Set.mem_singleton_iff, rs, v, Ext.wk, Expr.eval, Env.get] at hr
    subst hr; exact ⟨BaseOnlineLenInv.mono_online hOn hBInv, rfl⟩
  · rcases hF1 : (eFind K _ _).eval _ with _ | sE
    · rw [hF1] at hr
      rcases hF2 : (eFind K _ _).eval _ with _ | rE
      · rw [hF2] at hr
        simp only [support_pure, Set.mem_singleton_iff, rs, v, Ext.wk, Expr.eval, Env.get] at hr
        subst hr; exact ⟨BaseOnlineLenInv.mono_online hOn hBInv, rfl⟩
      · rw [hF2] at hr
        simp only [support_pure, Set.mem_singleton_iff, rs, stUpd,
          _root_.SignalPqxdh.Security.ReductionDsl.KeyInd.stMk,
          _root_.SignalPqxdh.Security.ReductionDsl.KeyInd.stSecb,
          stPrin, stSpks, stOpks, stSess, stResps, stUsedO, stUsedN, stKyb, stRo, stAdv,
          v, Ext.wk, Expr.eval, Env.get] at hr
        subst hr
        apply stUpd_resps_mem hOn hBInv
        simp only [eMap, Expr.eval, List.length_map, List.length_take, stRespsList]
        exact Nat.min_le_right _ _
    · rw [hF1] at hr
      simp only [support_pure, Set.mem_singleton_iff, rs, stUpd,
        _root_.SignalPqxdh.Security.ReductionDsl.KeyInd.stMk,
        _root_.SignalPqxdh.Security.ReductionDsl.KeyInd.stSecb,
        stPrin, stSpks, stOpks, stSess, stResps, stUsedO, stUsedN, stKyb, stRo, stAdv,
        v, Ext.wk, Expr.eval, Env.get] at hr
      subst hr
      apply stUpd_sess_mem hOn hBInv
      simp only [eMap, Expr.eval, List.length_map, List.length_take, stSessList]
      exact Nat.min_le_right _ _

private theorem revealB_mem_support {S : Setup} {c : Fin 3 → ℕ} {t : KeyIndQuery S} (K : ℕ)
    (hOn : isKeyIndOnlineQuery (.inr t) = true) (bSt : keyIndStateTy.denote)
    (sL : shcrStTy.denote) (p : _root_.SignalPqxdh.LegacyCosted.sidT.denote)
    (hBInv : BaseOnlineLenInv c bSt) :
    ∀ r ∈ support ((revealB K (.zero : Var testRevCtx _)
        (.succ (.succ .zero) : Var testRevCtx _)).eval
        (.cons bSt (.cons sL (.cons p .nil)))),
      BaseOnlineLenInv (bumpPred (keyIndSimPred S) c t) r.2 ∧ stRoList r.2 = stRoList bSt := by
  intro r hr
  simp only [revealB, caseOptV, Comp.eval] at hr
  rcases hF1 : (eFind K _ _).eval _ with _ | sE
  · rw [hF1] at hr
    rcases hF2 : (eFind K _ _).eval _ with _ | rE
    · rw [hF2] at hr
      simp only [support_pure, Set.mem_singleton_iff, rs, v, Ext.wk, Expr.eval, Env.get] at hr
      subst hr; exact ⟨BaseOnlineLenInv.mono_online hOn hBInv, rfl⟩
    · rw [hF2] at hr
      dsimp only at hr
      split_ifs at hr with hT
      · simp only [support_pure, Set.mem_singleton_iff, rs, v, Ext.wk, Expr.eval, Env.get] at hr
        subst hr; exact ⟨BaseOnlineLenInv.mono_online hOn hBInv, rfl⟩
      · simp only [support_pure, Set.mem_singleton_iff, rs, stUpd,
          _root_.SignalPqxdh.Security.ReductionDsl.KeyInd.stMk,
          _root_.SignalPqxdh.Security.ReductionDsl.KeyInd.stSecb,
          stPrin, stSpks, stOpks, stSess, stResps, stUsedO, stUsedN, stKyb, stRo, stAdv,
          v, Ext.wk, Expr.eval, Env.get] at hr
        subst hr
        apply stUpd_resps_mem hOn hBInv
        simp only [eMap, Expr.eval, List.length_map, List.length_take, stRespsList]
        exact Nat.min_le_right _ _
  · rw [hF1] at hr
    dsimp only at hr
    split_ifs at hr with hT
    · simp only [support_pure, Set.mem_singleton_iff, rs, v, Ext.wk, Expr.eval, Env.get] at hr
      subst hr; exact ⟨BaseOnlineLenInv.mono_online hOn hBInv, rfl⟩
    · simp only [support_pure, Set.mem_singleton_iff, rs, stUpd,
        _root_.SignalPqxdh.Security.ReductionDsl.KeyInd.stMk,
        _root_.SignalPqxdh.Security.ReductionDsl.KeyInd.stSecb,
        stPrin, stSpks, stOpks, stSess, stResps, stUsedO, stUsedN, stKyb, stRo, stAdv,
        v, Ext.wk, Expr.eval, Env.get] at hr
      subst hr
      apply stUpd_sess_mem hOn hBInv
      simp only [eMap, Expr.eval, List.length_map, List.length_take, stSessList]
      exact Nat.min_le_right _ _

private theorem caseSum_eval {Γ : List PT} {τ₁ τ₂ τ : PT}
    (e : Expr pqxdhOps Γ (.sum τ₁ τ₂))
    (kl : Comp pqxdhOps _root_.SignalPqxdh.LegacyCosted.pqPrimIface (τ₁ :: Γ) τ)
    (kr : Comp pqxdhOps _root_.SignalPqxdh.LegacyCosted.pqPrimIface (τ₂ :: Γ) τ)
    (env : Env Γ) :
    (Comp.caseSum e kl kr).eval env =
      match e.eval env with
      | .inl a => kl.eval (.cons a env)
      | .inr b => kr.eval (.cons b env) := by
  cases h : e.eval env <;> simp only [Comp.eval, h]

private theorem shcr1KeyActivePostC_test_eval (S : Setup) (K : ℕ)
    (sF : shcrStTy.denote) (sid : _root_.SignalPqxdh.SessionId S) :
    (shcr1KeyActivePostC S K
      (Γ₁ := [shcrStTy, _root_.SignalPqxdh.Security.ReductionDsl.KeyInd.keyIndQueryTy])
      (Γ₂ := [_root_.SignalPqxdh.Security.ReductionDsl.KeyInd.keyIndQueryTy])
      (Δ := [shcrStTy, _root_.SignalPqxdh.Security.ReductionDsl.KeyInd.keyIndQueryTy])
      .zero .zero).eval
      (.cons sF (.cons ((_root_.SignalPqxdh.LegacyCosted.keyIndCodec S).qenc (.testSession sid)) .nil)) =
    (onBase (Γ₁ := shcrSidCtx) (Δ := shcrSidCtx) .zero
      fun g => testB K g (.succ (.succ .zero) : Var testRevCtx _)).eval
      (.cons sF (.cons (_root_.SignalPqxdh.LegacyCosted.sidV sid) .nil)) := by
  simp only [shcr1KeyActivePostC, shcrActivePostTailC,
    _root_.SignalPqxdh.Security.ReductionDsl.KeyInd.caseSumV,
    _root_.SignalPqxdh.LegacyCosted.keyIndCodec, _root_.SignalPqxdh.LegacyCosted.keyIndQenc,
    caseSum_eval, v_eval_cons, v_zero_eval]
  rw [onBaseTestB_eval_congr K]
  simp only [v_eval_cons, v_zero_eval]

private theorem shcr1KeyActivePostC_revSess_eval (S : Setup) (K : ℕ)
    (sF : shcrStTy.denote) (sid : _root_.SignalPqxdh.SessionId S) :
    (shcr1KeyActivePostC S K
      (Γ₁ := [shcrStTy, _root_.SignalPqxdh.Security.ReductionDsl.KeyInd.keyIndQueryTy])
      (Γ₂ := [_root_.SignalPqxdh.Security.ReductionDsl.KeyInd.keyIndQueryTy])
      (Δ := [shcrStTy, _root_.SignalPqxdh.Security.ReductionDsl.KeyInd.keyIndQueryTy])
      .zero .zero).eval
      (.cons sF (.cons ((_root_.SignalPqxdh.LegacyCosted.keyIndCodec S).qenc (.revealSessionKey sid)) .nil)) =
    (onBase (Γ₁ := shcrSidCtx) (Δ := shcrSidCtx) .zero
      fun g => revealB K g (.succ (.succ .zero) : Var testRevCtx _)).eval
      (.cons sF (.cons (_root_.SignalPqxdh.LegacyCosted.sidV sid) .nil)) := by
  simp only [shcr1KeyActivePostC, shcrActivePostTailC,
    _root_.SignalPqxdh.Security.ReductionDsl.KeyInd.caseSumV,
    _root_.SignalPqxdh.LegacyCosted.keyIndCodec, _root_.SignalPqxdh.LegacyCosted.keyIndQenc,
    caseSum_eval, v_eval_cons, v_zero_eval]
  rw [onBaseRevealB_eval_congr K]
  simp only [v_eval_cons, v_zero_eval]

theorem shcrTestArm_sim (S : Setup) (b : QueryBudget) (c : Fin 3 → ℕ)
    (sK : shcrKindStTy.denote) (sid : _root_.SignalPqxdh.SessionId S)
    (hInv : ShcrSimInv S b c sK)
    (hBound : ∀ k, bumpPred (keyIndSimPred S) c (.testSession sid) k ≤ keyIndSimBounds b k) :
    let f := keyIndCoreFuels S b
    let t : KeyIndQuery S := .testSession sid
    let arm := shcrLiftLegArmK S (P := _root_.SignalPqxdh.LegacyCosted.sidT)
      (finSidToNatExpr S .v0) (shcrTestLeg f.M_on)
    Prod.map id (forgetShcrKindActive S b) <$>
        arm.eval (.cons (sidV sid) (.cons sK (.cons ((pqKeyIndCodec S).qenc t) .nil))) =
      activePostEval S b sK t ∧
    ∀ vs' ∈ support (arm.eval
        (.cons (sidV sid) (.cons sK (.cons ((pqKeyIndCodec S).qenc t) .nil)))),
      ShcrSimInv S b (bumpPred (keyIndSimPred S) c t) vs'.2 := by
  dsimp only [shcrTestLeg]
  have hOn : isKeyIndOnlineQuery (.inr (.testSession sid)) = true := by simp [isKeyIndOnlineQuery]
  obtain ⟨hc0Succ, hLeK⟩ := online_fuel_bounds S b c hOn hBound
  have hc0 : c 0 ≤ (keyIndCoreFuels S b).M_on := Nat.le_of_succ_le hc0Succ
  have hBInv : BaseOnlineLenInv c (projVal shcrStTy sK.1).1 := by
    have h := hInv.core_inv.online_len
    rwa [show projVal keyIndStateTy sK.1.1 = (projVal shcrStTy sK.1).1 from rfl] at h
  have hSim := shcrOnBaseArm_sim S b c (finSidToNatExpr S .v0)
    (fun g => testB (keyIndCoreFuels S b).M_on g (.succ (.succ .zero)))
    (fun g => testB (keyIndLoopBound b) g (.succ (.succ .zero)))
    (shcrTestLeg_unsup (keyIndCoreFuels S b).M_on) (sidV sid) sK (.testSession sid)
    (_root_.SignalPqxdh.LegacyCosted.sidV sid)
    (finSidToNatExpr_v0_eval S sid sK _) hOn hInv
    (by
      have hMin := testB_min_eq (.zero : Var testRevCtx _) (.succ (.succ .zero) : Var testRevCtx _)
        (.cons (projVal shcrStTy sK.1).1 (.cons (projVal shcrStTy sK.1)
          (.cons (_root_.SignalPqxdh.LegacyCosted.sidV sid) .nil)))
        (by rwa [v_zero_eval]) hc0 hLeK
      rw [hMin,
        testB_eval_congr (keyIndLoopBound b) (.zero : Var testRevCtx _) (.succ (.succ .zero) : Var testRevCtx _),
        testB_eval_congr (keyIndLoopBound b) (.zero : Var testRevCtx _) (.succ (.succ .zero) : Var testRevCtx _)]
      simp only [v_zero_eval, v_succ2_eval])
    (testB_mem_support (keyIndCoreFuels S b).M_on hOn _ _ _ hBInv)
  exact ⟨hSim.1.trans (congrArg (Functor.map (embedVal SCS))
    (shcr1KeyActivePostC_test_eval S (keyIndLoopBound b) _ sid).symm), hSim.2⟩

theorem shcrRevSessArm_sim (S : Setup) (b : QueryBudget) (c : Fin 3 → ℕ)
    (sK : shcrKindStTy.denote) (sid : _root_.SignalPqxdh.SessionId S)
    (hInv : ShcrSimInv S b c sK)
    (hBound : ∀ k, bumpPred (keyIndSimPred S) c (.revealSessionKey sid) k ≤ keyIndSimBounds b k) :
    let f := keyIndCoreFuels S b
    let t : KeyIndQuery S := .revealSessionKey sid
    let arm := shcrLiftLegArmK S (P := _root_.SignalPqxdh.LegacyCosted.sidT)
      (finSidToNatExpr S .v0) (shcrRevSessLeg f.M_on)
    Prod.map id (forgetShcrKindActive S b) <$>
        arm.eval (.cons (sidV sid) (.cons sK (.cons ((pqKeyIndCodec S).qenc t) .nil))) =
      activePostEval S b sK t ∧
    ∀ vs' ∈ support (arm.eval
        (.cons (sidV sid) (.cons sK (.cons ((pqKeyIndCodec S).qenc t) .nil)))),
      ShcrSimInv S b (bumpPred (keyIndSimPred S) c t) vs'.2 := by
  dsimp only [shcrRevSessLeg]
  have hOn : isKeyIndOnlineQuery (.inr (.revealSessionKey sid)) = true := by simp [isKeyIndOnlineQuery]
  obtain ⟨hc0Succ, hLeK⟩ := online_fuel_bounds S b c hOn hBound
  have hc0 : c 0 ≤ (keyIndCoreFuels S b).M_on := Nat.le_of_succ_le hc0Succ
  have hBInv : BaseOnlineLenInv c (projVal shcrStTy sK.1).1 := by
    have h := hInv.core_inv.online_len
    rwa [show projVal keyIndStateTy sK.1.1 = (projVal shcrStTy sK.1).1 from rfl] at h
  have hSim := shcrOnBaseArm_sim S b c (finSidToNatExpr S .v0)
    (fun g => revealB (keyIndCoreFuels S b).M_on g (.succ (.succ .zero)))
    (fun g => revealB (keyIndLoopBound b) g (.succ (.succ .zero)))
    (shcrRevSessLeg_unsup (keyIndCoreFuels S b).M_on) (sidV sid) sK (.revealSessionKey sid)
    (_root_.SignalPqxdh.LegacyCosted.sidV sid)
    (finSidToNatExpr_v0_eval S sid sK _) hOn hInv
    (by
      have hMin := revealB_min_eq (.zero : Var testRevCtx _) (.succ (.succ .zero) : Var testRevCtx _)
        (.cons (projVal shcrStTy sK.1).1 (.cons (projVal shcrStTy sK.1)
          (.cons (_root_.SignalPqxdh.LegacyCosted.sidV sid) .nil)))
        (by rwa [v_zero_eval]) hc0 hLeK
      rw [hMin,
        revealB_eval_congr (keyIndLoopBound b) (.zero : Var testRevCtx _) (.succ (.succ .zero) : Var testRevCtx _),
        revealB_eval_congr (keyIndLoopBound b) (.zero : Var testRevCtx _) (.succ (.succ .zero) : Var testRevCtx _)]
      simp only [v_zero_eval, v_succ2_eval])
    (revealB_mem_support (keyIndCoreFuels S b).M_on hOn _ _ _ hBInv)
  exact ⟨hSim.1.trans (congrArg (Functor.map (embedVal SCS))
    (shcr1KeyActivePostC_revSess_eval S (keyIndLoopBound b) _ sid).symm), hSim.2⟩

private theorem atomic_env_get_zero {τ : Ty pqAtomicSig} {Γ : List (Ty pqAtomicSig)}
    (x : τ.denote) (env : Env Γ) : (Env.cons x env).get .zero = x := rfl

private theorem atomic_env_get_succ {σ τ : Ty pqAtomicSig} {Γ : List (Ty pqAtomicSig)}
    (x : σ.denote) (v : Var Γ τ) (env : Env Γ) : (Env.cons x env).get (.succ v) = env.get v := rfl

private theorem wkTop3_env_get {A B C X : Ty pqAtomicSig} (xVal : X.denote)
    (env : Env [A, B, C]) :
    ∀ {a} (x : Var [A, B, C] a), (Env.cons xVal env).get (wkTop3 x) = env.get x
  | _, .zero => rfl
  | _, .succ .zero => rfl
  | _, .succ (.succ .zero) => rfl

private theorem tryPauseC_eval_congr (S : Setup) (K : ℕ) (opk : Bool) {Γ₁ Γ₂ Δ : List PT}
    (s : Var Γ₁ shcrStTy) (x : Var Γ₂ initQTy) [Ext Γ₁ Δ] [Ext Γ₂ Δ] (env : Env Δ) :
    (tryPauseC S K opk (Δ := Δ) s x).eval env =
      (tryPauseC S K opk (Γ₁ := [shcrStTy, initQTy]) (Γ₂ := [initQTy])
        (Δ := [shcrStTy, initQTy]) .zero .zero).eval
        (.cons ((v s).eval env) (.cons ((v x).eval env) .nil)) := by
  have hRen : compRename (ren2Var (Δ := Δ) s x)
      (tryPauseC S K opk (Γ₁ := [shcrStTy, initQTy]) (Γ₂ := [initQTy])
        (Δ := [shcrStTy, initQTy]) .zero .zero) =
      tryPauseC S K opk (Δ := Δ) s x := by
    cases opk <;> rfl
  rw [← hRen]
  exact compRename_eval _ (ren2Var (Δ := Δ) s x) _ env (ren2Var_env_get s x env)

private theorem tryPauseC_fuel_eq (S : Setup) {K₁ K₂ : ℕ} {c : Fin 3 → ℕ}
    (opk : Bool) (sL : shcrStTy.denote) (p : initQTy.denote)
    (hInv : BaseOnlineLenInv c sL.1) (hc0 : c 0 ≤ K₁) (hLe : K₁ ≤ K₂) :
    (tryPauseC S K₁ opk (Γ₁ := [shcrStTy, initQTy]) (Γ₂ := [initQTy])
      (Δ := [shcrStTy, initQTy]) .zero .zero).eval (.cons sL (.cons p .nil)) =
    (tryPauseC S K₂ opk (Γ₁ := [shcrStTy, initQTy]) (Γ₂ := [initQTy])
      (Δ := [shcrStTy, initQTy]) .zero .zero).eval (.cons sL (.cons p .nil)) := by
  have hPrin : (stPrinList sL.1).length ≤ K₁ := Nat.le_trans hInv.prin_le hc0
  simp only [tryPauseC, letV_eval_step, bindV, caseOptV, Comp.eval]
  split_ifs with hG
  · rfl
  · rw [preCheckC_min_eq S _ _ _ _ _
      (by simpa [scBase, Expr.eval, v_eval_cons, v_zero_eval, v, Ext.wk, Env.get] using hInv) hc0 hLe]
    apply congrArg (Bind.bind _); funext pc
    cases pc with
    | none => simp [Expr.eval, v_zero_eval]
    | some uE =>
      simp only [Expr.eval, v_zero_eval]
      rw [checkSigsC_min_eq S _ _ _
        (by simpa [scBase, Expr.eval, v_eval_cons, v_zero_eval, v, Ext.wk, Env.get] using hPrin) hLe]

private theorem tryPauseC_fixSent_eq (S : Setup) (b : QueryBudget) (K : ℕ)
    (opk : Bool) (sL : shcrStTy.denote) (p : initQTy.denote)
    (hCnt : sL.2.2.2.2.1 ≤ min b.q_on b.q_total) :
    (tryPauseC S K opk (Γ₁ := [shcrStTy, initQTy]) (Γ₂ := [initQTy])
      (Δ := [shcrStTy, initQTy]) .zero .zero).eval (.cons sL (.cons p .nil)) =
    (tryPauseC S K opk (Γ₁ := [shcrStTy, initQTy]) (Γ₂ := [initQTy])
      (Δ := [shcrStTy, initQTy]) .zero .zero).eval
      (.cons (fixShcrLegacySent S b sL) (.cons p .nil)) := by
  rcases sL with ⟨bSt, tb, tpk, tsk, cnt, ir, rr, sidx, ch⟩
  have hGuard :
      (initGuardE opk (.var (.succ .zero))).eval
        (.cons (t := shcrStTy) (bSt, tb, tpk, tsk, cnt, ir, rr, fixSent S b sidx, ch) (.cons p .nil)) =
      (initGuardE opk (.var (.succ .zero))).eval
        (.cons (t := shcrStTy) (bSt, tb, tpk, tsk, cnt, ir, rr, sidx, ch) (.cons p .nil)) := by
    cases opk <;> rfl
  have hSid : ∀ sidx' : ℕ,
      (initSidE opk (.var (.succ (.succ .zero)))).eval
        (.cons p.2.2 (.cons (t := shcrStTy) (bSt, tb, tpk, tsk, cnt, ir, rr, sidx', ch) (.cons p .nil))) =
      (initSidE opk (.var .zero)).eval (.cons p .nil) := by
    intro _; cases opk <;> rfl
  dsimp only [tryPauseC, fixShcrLegacySent, v, Ext.wk]
  simp only [Comp.eval, hGuard]
  by_cases hG : (initGuardE opk (.var (.succ .zero))).eval
      (.cons (t := shcrStTy) (bSt, tb, tpk, tsk, cnt, ir, rr, sidx, ch) (.cons p .nil)) = true
  · simp [hG, Expr.eval]
  · simp only [hG, Bool.false_eq_true, ↓reduceIte, letV_eval_step, bindV, caseOptV, Comp.eval,
      scBase, Expr.eval, Env.get, hSid]
    rw [preCheckC_eval_congr S K, eq_comm, preCheckC_eval_congr S K, eq_comm]
    simp only [v, Ext.wk, Expr.eval, Env.get]
    apply congrArg (Bind.bind _); funext pc
    cases pc with
    | none => rfl
    | some uE =>
      dsimp only
      rw [checkSigsC_eval_congr S K, eq_comm, checkSigsC_eval_congr S K, eq_comm]
      simp only [v, Ext.wk, Expr.eval, Env.get]
      apply congrArg (Bind.bind _); funext ok
      cases ok with
      | false => simp
      | true =>
        have hBeq := beq_fixSent_of_le_mOn (S := S) (n := sidx) hCnt
        have hDec : decide (cnt = sidx) = decide (cnt = fixSent S b sidx) :=
          decide_eq_decide.mpr ⟨fun h => beq_iff_eq.mp (hBeq ▸ beq_iff_eq.mpr h),
            fun h => beq_iff_eq.mp (hBeq.symm ▸ beq_iff_eq.mpr h)⟩
        simp only [natEq, scCnt, scSIdx, Expr.eval, Env.get]
        rw [hDec]

private theorem shcrInitArmPre_sim_gen (S : Setup) (b : QueryBudget) (c : Fin 3 → ℕ)
    (N_s : ℕ) (opk : Bool) (sK : shcrKindStTy.denote)
    (u : Fin S.N_id) (i : Fin N_s) (bu : _root_.SignalPqxdh.PreKeyBundleInput)
    (t : KeyIndQuery S) (hOn : isKeyIndOnlineQuery (.inr t) = true)
    (hInv : ShcrSimInv S b c sK)
    (hBound : ∀ k, bumpPred (keyIndSimPred S) c t k ≤ keyIndSimBounds b k)
    (hPostSim :
      Prod.map id (forgetShcrKindActive S b) <$>
          (shcrInitArmPostK S (keyIndCoreFuels S b).M_on (keyIndCoreFuels S b).roCap N_s opk).eval
            (.cons (u, (i, bundleV bu)) (.cons sK (.cons ((pqKeyIndCodec S).qenc t) .nil))) =
        activePostEval S b sK t ∧
      ∀ vs' ∈ support
          ((shcrInitArmPostK S (keyIndCoreFuels S b).M_on (keyIndCoreFuels S b).roCap N_s opk).eval
            (.cons (u, (i, bundleV bu)) (.cons sK (.cons ((pqKeyIndCodec S).qenc t) .nil)))),
        ShcrSimInv S b (bumpPred (keyIndSimPred S) c t) vs'.2)
    (hPauseEq :
      (pauseCheckC S (keyIndLoopBound b)
        (Γ₁ := [shcrStTy, _root_.SignalPqxdh.Security.ReductionDsl.KeyInd.keyIndQueryTy])
        (Γ₂ := [_root_.SignalPqxdh.Security.ReductionDsl.KeyInd.keyIndQueryTy])
        (Δ := [shcrStTy, _root_.SignalPqxdh.Security.ReductionDsl.KeyInd.keyIndQueryTy])
        .zero .zero).eval
        (.cons (fixShcrLegacySent S b (projVal shcrStTy sK.1))
          (.cons ((_root_.SignalPqxdh.LegacyCosted.keyIndCodec S).qenc t) .nil)) =
      (tryPauseC S (keyIndLoopBound b) opk
        (Γ₁ := [shcrStTy, initQTy]) (Γ₂ := [initQTy]) (Δ := [shcrStTy, initQTy])
        .zero .zero).eval
        (.cons (fixShcrLegacySent S b (projVal shcrStTy sK.1))
          (.cons (u.val, (i.val, _root_.SignalPqxdh.LegacyCosted.bundleV bu)) .nil)))
    (hActPostWk :
      (shcr1KeyActivePostC S (keyIndLoopBound b)
        (Γ₁ := [shcrStTy, _root_.SignalPqxdh.Security.ReductionDsl.KeyInd.keyIndQueryTy])
        (Γ₂ := [_root_.SignalPqxdh.Security.ReductionDsl.KeyInd.keyIndQueryTy])
        (Δ := .opt pauseTy :: [shcrStTy, _root_.SignalPqxdh.Security.ReductionDsl.KeyInd.keyIndQueryTy])
        .zero .zero).eval
        (.cons none (.cons (fixShcrLegacySent S b (projVal shcrStTy sK.1))
          (.cons ((_root_.SignalPqxdh.LegacyCosted.keyIndCodec S).qenc t) .nil))) =
      (shcr1KeyActivePostC S (keyIndLoopBound b)
        (Γ₁ := [shcrStTy, _root_.SignalPqxdh.Security.ReductionDsl.KeyInd.keyIndQueryTy])
        (Γ₂ := [_root_.SignalPqxdh.Security.ReductionDsl.KeyInd.keyIndQueryTy])
        (Δ := [shcrStTy, _root_.SignalPqxdh.Security.ReductionDsl.KeyInd.keyIndQueryTy])
        .zero .zero).eval
        (.cons (fixShcrLegacySent S b (projVal shcrStTy sK.1))
          (.cons ((_root_.SignalPqxdh.LegacyCosted.keyIndCodec S).qenc t) .nil))) :
    let f := keyIndCoreFuels S b
    let arm := shcrInitArmPreK S f.M_on f.roCap N_s opk
    forgetPreOut id (forgetShcrKindActive S b) <$>
        arm.eval (.cons (u, (i, bundleV bu)) (.cons sK (.cons ((pqKeyIndCodec S).qenc t) .nil))) =
      activePreEval S b sK t ∧
    (∀ vs' : (pqKeyIndCodec S).R.denote × shcrKindStTy.denote,
      Sum.inl vs' ∈ support (arm.eval
        (.cons (u, (i, bundleV bu)) (.cons sK (.cons ((pqKeyIndCodec S).qenc t) .nil)))) →
      ShcrSimInv S b (bumpPred (keyIndSimPred S) c t) vs'.2) ∧
    (∀ cp : (PB (ℓ := 0) (Pt := Empty) 1568).denote ×
        ((embedTy pauseTy).denote × shcrKindStTy.denote),
      Sum.inr cp ∈ support (arm.eval
        (.cons (u, (i, bundleV bu)) (.cons sK (.cons ((pqKeyIndCodec S).qenc t) .nil)))) →
      ShcrPauseInv S b (bumpPred (keyIndSimPred S) c t) cp.2.1 cp.2.2) := by
  dsimp only
  set f := keyIndCoreFuels S b
  set env0 : Env (S := pqAtomicSig)
      [.prod (.base (.fin S.N_id)) (.prod (.base (.fin N_s)) (bundleT (ℓ := 0) (Pt := Empty))),
       shcrKindStTy, (pqKeyIndCodec S).Q] :=
    .cons (u, (i, bundleV bu)) (.cons sK (.cons ((pqKeyIndCodec S).qenc t) .nil))
  set p : initQTy.denote := (u.val, (i.val, _root_.SignalPqxdh.LegacyCosted.bundleV bu))
  set sL : shcrStTy.denote := projVal shcrStTy sK.1
  have hsK1 : sK.1 = embedVal shcrStTy sL := (embedVal_projVal shcrStTy sK.1).symm
  have hbSt : projVal keyIndStateTy sK.1.1 = sL.1 := by
    rw [hsK1]; exact projVal_embedVal keyIndStateTy sL.1
  obtain ⟨hc0_1, hM_le⟩ := online_fuel_bounds S b c hOn hBound
  have hc0 : c 0 ≤ f.M_on := Nat.le_of_succ_le hc0_1
  obtain ⟨h0, _, h2⟩ := bumpPred_online S c hOn
  have hCoreOnline : BaseOnlineLenInv c sL.1 := by
    simpa only [hbSt] using hInv.core_inv.online_len
  have hCntMOn : sL.2.2.2.2.1 ≤ min b.q_on b.q_total := Nat.le_trans hInv.cnt_le hc0
  have hTryEval :
      (runAt2 (.fst .v1) (initPayToNatE N_s S .v0)
        (mapComp tlPrimKeyInd (tryPauseC S f.M_on opk
          (Γ₁ := [shcrStTy, initQTy]) (Γ₂ := [initQTy]) (Δ := [shcrStTy, initQTy])
          .zero .zero))).eval env0 =
      embedVal (.opt pauseTy) <$>
        (tryPauseC S f.M_on opk
          (Γ₁ := [shcrStTy, initQTy]) (Γ₂ := [initQTy]) (Δ := [shcrStTy, initQTy])
          .zero .zero).eval (.cons sL (.cons p .nil)) := by
    rw [runAt2_eval, initPayToNatE_v0_eval]
    simp only [env0, Expr.eval, Env.get, Expr.v1, hsK1]
    exact mapComp_eval tlPrimKeyInd _ (tryPauseC_unsup S f.M_on opk) (.cons sL (.cons p .nil))
  have hPostWk : ∀ xVal : (embedTy (.opt pauseTy)).denote,
      (compRename wkTop3 (shcrInitArmPostK S f.M_on f.roCap N_s opk)).eval (.cons xVal env0) =
        (shcrInitArmPostK S f.M_on f.roCap N_s opk).eval env0 := fun xVal =>
    compRename_eval _ wkTop3 _ (.cons xVal env0) (wkTop3_env_get xVal env0)
  refine ⟨?_, ?_, ?_⟩
  · simp only [activePreEval, shcr1KeyActivePreC, bindV, caseOptV, Comp.eval,
      map_eq_bind_pure_comp, bind_assoc, Function.comp_def]
    rw [hPauseEq, ← tryPauseC_fixSent_eq S b (keyIndLoopBound b) opk sL p hCntMOn,
      ← tryPauseC_fuel_eq S opk sL p hCoreOnline hc0 hM_le]
    simp only [shcrInitArmPreK, Comp.eval, hTryEval, map_eq_bind_pure_comp, bind_assoc,
      pure_bind, Function.comp_def]
    congr 1; funext optP
    cases optP with
    | none =>
      simp only [embedVal, Expr.v0, Expr.eval, Env.get, v, Ext.wk]
      rw [hPostWk, hActPostWk]
      let RRight := (PB (ℓ := 0) (Pt := Empty) 1568).denote ×
        ((embedTy pauseTy).denote × (embedTy shcrStTy).denote)
      have h1 := congrArg (fun m => (Sum.inl (β := RRight)) <$> m) hPostSim.1
      simpa only [activePostEval, forgetPreOut, embedVal, map_eq_bind_pure_comp, bind_assoc,
        pure_bind, Function.comp_def, Sum.map_inl, sL] using h1
    | some dL =>
      simp only [embedVal, forgetPreOut, Sum.map_inr, Prod.map_apply, id_eq,
        Expr.v0, Expr.v3, Expr.eval, Env.get, v, Ext.wk, env0, pure_bind,
        forgetShcrKindActive_eq_embed]
  · intro vs' hMem
    simp only [shcrInitArmPreK, Comp.eval, hTryEval, map_eq_bind_pure_comp, bind_assoc,
      pure_bind, Function.comp_def, mem_support_bind_iff] at hMem
    rcases hMem with ⟨optP, _, hMem⟩
    cases optP with
    | none =>
      simp only [embedVal, Expr.v0, Expr.eval, atomic_env_get_zero] at hMem
      rw [hPostWk] at hMem
      simp only [mem_support_bind_iff, support_pure, Set.mem_singleton_iff, Sum.inl.injEq] at hMem
      rcases hMem with ⟨vs'', hvs'', rfl⟩
      exact hPostSim.2 vs' hvs''
    | some dL =>
      simp only [embedVal, Expr.v0, Expr.v3, Expr.eval, atomic_env_get_zero,
        atomic_env_get_succ, support_pure, Set.mem_singleton_iff] at hMem
      exact nomatch hMem
  · intro cp hMem
    simp only [shcrInitArmPreK, Comp.eval, hTryEval, map_eq_bind_pure_comp, bind_assoc,
      pure_bind, Function.comp_def, mem_support_bind_iff] at hMem
    rcases hMem with ⟨optP, _, hMem⟩
    cases optP with
    | none =>
      simp only [embedVal, Expr.v0, Expr.eval, atomic_env_get_zero] at hMem
      rw [hPostWk] at hMem
      simp only [mem_support_bind_iff, support_pure, Set.mem_singleton_iff] at hMem
      rcases hMem with ⟨_, _, hEq⟩
      exact nomatch hEq
    | some dL =>
      simp only [embedVal, Expr.v0, Expr.v3, Expr.eval, atomic_env_get_zero,
        atomic_env_get_succ, env0, support_pure, Set.mem_singleton_iff, Sum.inr.injEq] at hMem
      subst hMem
      refine ⟨BaseOnlineLenInv.mono_online hOn hInv.core_inv.online_len,
        ?_, ?_, hInv.core_inv.ro_avl, ?_, ?_, ?_⟩
      · rw [h0]; exact Nat.succ_le_succ hInv.core_inv.online_len.sess_le
      · rw [h2]; exact Nat.succ_le_succ hInv.core_inv.ro_len
      · rw [h0]; exact Nat.succ_le_succ hInv.cnt_le
      · rw [h0]; exact Nat.succ_le_succ hInv.ir_le
      · rw [h0]; exact Nat.le_succ_of_le hInv.rr_le

theorem shcrInitOpkArmPre_sim (S : Setup) (b : QueryBudget) (c : Fin 3 → ℕ)
    (sK : shcrKindStTy.denote) (u : Fin S.N_id) (i : Fin S.N_send_opk)
    (bu : _root_.SignalPqxdh.PreKeyBundleInput)
    (hInv : ShcrSimInv S b c sK)
    (hBound : ∀ k, bumpPred (keyIndSimPred S) c (.initiateOPK u i bu) k ≤ keyIndSimBounds b k) :
    let f := keyIndCoreFuels S b
    let t : KeyIndQuery S := .initiateOPK u i bu
    let arm := shcrInitArmPreK S f.M_on f.roCap S.N_send_opk true
    forgetPreOut id (forgetShcrKindActive S b) <$>
        arm.eval (.cons (u, (i, bundleV bu)) (.cons sK (.cons ((pqKeyIndCodec S).qenc t) .nil))) =
      activePreEval S b sK t ∧
    (∀ vs' : (pqKeyIndCodec S).R.denote × shcrKindStTy.denote,
      Sum.inl vs' ∈ support (arm.eval
        (.cons (u, (i, bundleV bu)) (.cons sK (.cons ((pqKeyIndCodec S).qenc t) .nil)))) →
      ShcrSimInv S b (bumpPred (keyIndSimPred S) c t) vs'.2) ∧
    (∀ cp : (PB (ℓ := 0) (Pt := Empty) 1568).denote ×
        ((embedTy pauseTy).denote × shcrKindStTy.denote),
      Sum.inr cp ∈ support (arm.eval
        (.cons (u, (i, bundleV bu)) (.cons sK (.cons ((pqKeyIndCodec S).qenc t) .nil)))) →
      ShcrPauseInv S b (bumpPred (keyIndSimPred S) c t) cp.2.1 cp.2.2) := by
  intro f t arm
  have hOn : isKeyIndOnlineQuery (.inr t) = true := by simp [isKeyIndOnlineQuery, t]
  refine shcrInitArmPre_sim_gen S b c S.N_send_opk true sK u i bu t hOn hInv hBound
    (shcrInitOpkArmPost_sim S b c sK u i bu hInv hBound) ?_ ?_
  · simp only [pauseCheckC, _root_.SignalPqxdh.Security.ReductionDsl.KeyInd.caseSumV,
      _root_.SignalPqxdh.LegacyCosted.keyIndCodec, _root_.SignalPqxdh.LegacyCosted.keyIndQenc,
      Comp.eval, v_eval_cons, v_zero_eval, t]
    exact tryPauseC_eval_congr S (keyIndLoopBound b) true _ _ _
  · simp only [shcr1KeyActivePostC, shcrActivePostTailC,
      _root_.SignalPqxdh.Security.ReductionDsl.KeyInd.caseSumV,
      _root_.SignalPqxdh.LegacyCosted.keyIndCodec, _root_.SignalPqxdh.LegacyCosted.keyIndQenc,
      Comp.eval, v_eval_cons, v_zero_eval, t]
    rw [shcrInitiateC_eval_congr S (keyIndLoopBound b) true, eq_comm,
      shcrInitiateC_eval_congr S (keyIndLoopBound b) true]
    simp [v_eval_cons, v_zero_eval]

theorem shcrInitNoOpkArmPre_sim (S : Setup) (b : QueryBudget) (c : Fin 3 → ℕ)
    (sK : shcrKindStTy.denote) (u : Fin S.N_id) (i : Fin S.N_send_no_opk)
    (bu : _root_.SignalPqxdh.PreKeyBundleInput)
    (hInv : ShcrSimInv S b c sK)
    (hBound : ∀ k, bumpPred (keyIndSimPred S) c (.initiateNoOPK u i bu) k ≤ keyIndSimBounds b k) :
    let f := keyIndCoreFuels S b
    let t : KeyIndQuery S := .initiateNoOPK u i bu
    let arm := shcrInitArmPreK S f.M_on f.roCap S.N_send_no_opk false
    forgetPreOut id (forgetShcrKindActive S b) <$>
        arm.eval (.cons (u, (i, bundleV bu)) (.cons sK (.cons ((pqKeyIndCodec S).qenc t) .nil))) =
      activePreEval S b sK t ∧
    (∀ vs' : (pqKeyIndCodec S).R.denote × shcrKindStTy.denote,
      Sum.inl vs' ∈ support (arm.eval
        (.cons (u, (i, bundleV bu)) (.cons sK (.cons ((pqKeyIndCodec S).qenc t) .nil)))) →
      ShcrSimInv S b (bumpPred (keyIndSimPred S) c t) vs'.2) ∧
    (∀ cp : (PB (ℓ := 0) (Pt := Empty) 1568).denote ×
        ((embedTy pauseTy).denote × shcrKindStTy.denote),
      Sum.inr cp ∈ support (arm.eval
        (.cons (u, (i, bundleV bu)) (.cons sK (.cons ((pqKeyIndCodec S).qenc t) .nil)))) →
      ShcrPauseInv S b (bumpPred (keyIndSimPred S) c t) cp.2.1 cp.2.2) := by
  intro f t arm
  have hOn : isKeyIndOnlineQuery (.inr t) = true := by simp [isKeyIndOnlineQuery, t]
  refine shcrInitArmPre_sim_gen S b c S.N_send_no_opk false sK u i bu t hOn hInv hBound
    (shcrInitNoOpkArmPost_sim S b c sK u i bu hInv hBound) ?_ ?_
  · simp only [pauseCheckC, _root_.SignalPqxdh.Security.ReductionDsl.KeyInd.caseSumV,
      _root_.SignalPqxdh.LegacyCosted.keyIndCodec, _root_.SignalPqxdh.LegacyCosted.keyIndQenc,
      Comp.eval, v_eval_cons, v_zero_eval, t]
    exact tryPauseC_eval_congr S (keyIndLoopBound b) false _ _ _
  · simp only [shcr1KeyActivePostC, shcrActivePostTailC,
      _root_.SignalPqxdh.Security.ReductionDsl.KeyInd.caseSumV,
      _root_.SignalPqxdh.LegacyCosted.keyIndCodec, _root_.SignalPqxdh.LegacyCosted.keyIndQenc,
      Comp.eval, v_eval_cons, v_zero_eval, t]
    rw [shcrInitiateC_eval_congr S (keyIndLoopBound b) false, eq_comm,
      shcrInitiateC_eval_congr S (keyIndLoopBound b) false]
    simp [v_eval_cons, v_zero_eval]

end Computational.Proofs.SignalPqxdh.Security.ReductionDsl.KindSplit.KeyIndCoreKSimArmsSess
