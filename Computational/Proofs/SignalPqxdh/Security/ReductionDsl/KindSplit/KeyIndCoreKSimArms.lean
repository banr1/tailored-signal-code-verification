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
public import Computational.Proofs.SignalPqxdh.Security.ReductionDsl.KindSplit.KeyIndCoreKSimHelpers -- proof-setup: allow-public-import

/-!
# Per-Arm Forgetful Simulation Lemmas for `shcrKeyInd1KeyKindAtomicProg`

Proves forgetful simulation and `ShcrSimInv` preservation for the random-oracle and non-session
query arms of `shcrKindHandlePostC true` and `shcrKindHandlePreC true`.
-/

public section

set_option autoImplicit false

namespace Computational.Proofs.SignalPqxdh.Security.ReductionDsl.KindSplit.KeyIndCoreKSimArms

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
  Ext PT RS SCS accQTy bindV buIkB buMk buOpkB buPqspkB buPqspkId buSpkB buSpkId caseOptV caseSumV
  checkSigsC corruptB eAny eFind eMap encEC encKEM eqU32 findHonestC freshE
  genOpkB genSpkB hdEkAPk hdIkAPk hdKemCt hdOpkId hdPqspkId hdSpkId
  initGuardE initPrin1KeyB initQTy initSidE isNoneRespE isSomeE keyIndLoopBound
  keyIndStateTy koskSenderOkC kyberCheckE lenB letV nat2Eq nat3Eq natEq oeConsumed oeOpkPk oeOpkSk
  oeUpd onBase optU32Eq pauseTy peIkAPk peSecIKA0 peSecIKAsign
  preCheckC principalEntryTy qHdr qJ qK qKJO qKemDecaps qKemEncaps qKemKeyGen qO qSigSign qX25519
  qX25519Base rAccFresh rBundle rDrKey rNone rPk rSpkSk reMk recordRespC registerB
  revealB revealDhB revealSpkB roB rs sBytes32 sRandom64 sbMk sbPqspkPk
  sbPqspkSk sbSpkPk sbSpkSk scBase scChosen scCnt scIR scRR scSIdx scTB scTPk scTSk scUpd seMk
  seUpd shcrAcceptB shcrFinE shcrInitiateC shcrStTy spkBundleEntryTy
  stAdv stKyb stOpks stPrin stResps stRo stSecb stSess stSpks stUpd stUsedN stUsedO testB tryPauseC
  u32OfNat v acceptKeysC acceptNoOpkB acceptOpkB buildSecretsE hkdfOrRoC
)
open _root_.Computational.Proofs.SignalPqxdh.Delta.KeyInd1KeyActiveProgs (
  shcr1KeyActivePostC shcr1KeyActivePreC shcrActiveGenSpkB shcrActivePostTailC
)
open _root_.Computational.Proofs.SignalPqxdh.Security.ReductionDsl.KindSplit.KeyIndCoreK (
  accPayToNatE atomicRNoneE coreAcceptPreRoC finPairToNatE finTripleToNatE
  initFinishPostRoC initPayToNatE keyIndCoreFuels roAvlTy roListLegacyTy roShadowQueryC
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
  eAny_eq_of_le eFind_eq_of_le eMap_eq_of_le embedVal_roList_eq
  env_get_succ env_get_zero ext_refl_wk ext_step_wk fixShcrLegacySent
  forgetShcrKindActive_eq_embed hkdfOrRoC_eval_congr hkdfOrRoC_unsup initFinishC_true_eq_split
  initFinishPostRoC_fuel_eq initFinishPostRoC_mem_support
  ro_bounds_of_le shcrAcceptPostRoC_unsup shcrAcceptPreRoC_unsup shcrActiveGenSpkLeg_unsup
  shcrCorruptLeg_unsup shcrGenOpkLeg_unsup shcrInitPrin1KeyLeg_unsup shcrInitiatePostRoC_fixSent_comm
  shcrInitiatePostRoC_unsup shcrInitiatePreRoC_unsup shcrLiftLegArmK_eval_eq
  shcrLiftLegArmK_map_forget shcrRegKeyLeg_unsup shcrRevDhLeg_unsup shcrRevSessLeg_unsup
  shcrRevSpkLeg_unsup shcrRoListAtomicE_eval shcrSetRoRespC_unsup shcrTestLeg_unsup
  tryPauseC_unsup v_eval_cons v_zero_eval
)

theorem bumpPred_online (S : Setup) (c : Fin 3 → ℕ) {t : KeyIndQuery S}
    (hOn : isKeyIndOnlineQuery (.inr t) = true) :
    bumpPred (keyIndSimPred S) c t 0 = c 0 + 1 ∧
    bumpPred (keyIndSimPred S) c t 1 = c 1 ∧
    bumpPred (keyIndSimPred S) c t 2 = c 2 + 1 := by
  have hRo : isKeyIndRoQuery (.inr t) = false := by
    cases t <;> simp_all [isKeyIndOnlineQuery, isKeyIndRoQuery]
  refine ⟨?_, ?_, ?_⟩ <;>
    simp [bumpPred, keyIndSimPred, hOn, hRo]

theorem bumpPred_ro (S : Setup) (c : Fin 3 → ℕ) (sec : _root_.SignalPqxdh.Bytes) :
    bumpPred (keyIndSimPred S) c (.roQuery sec) 0 = c 0 ∧
    bumpPred (keyIndSimPred S) c (.roQuery sec) 1 = c 1 + 1 ∧
    bumpPred (keyIndSimPred S) c (.roQuery sec) 2 = c 2 + 1 := by
  refine ⟨?_, ?_, ?_⟩ <;>
    simp [bumpPred, keyIndSimPred, isKeyIndOnlineQuery, isKeyIndRoQuery]

theorem BaseOnlineLenInv.mono_online {S : Setup} {c : Fin 3 → ℕ} {bSt : keyIndStateTy.denote}
    {t : KeyIndQuery S} (hOn : isKeyIndOnlineQuery (.inr t) = true) (h : BaseOnlineLenInv c bSt) :
    BaseOnlineLenInv (bumpPred (keyIndSimPred S) c t) bSt := by
  obtain ⟨h0, h1, h2⟩ := bumpPred_online S c hOn
  have hSum := h.counts_eq
  exact ⟨by rw [h0]; exact Nat.le_succ_of_le h.prin_le,
         by rw [h0]; exact Nat.le_succ_of_le h.spks_le,
         by rw [h0]; exact Nat.le_succ_of_le h.opks_le,
         by rw [h0]; exact Nat.le_succ_of_le h.sess_le,
         by rw [h0]; exact Nat.le_succ_of_le h.resps_le,
         by rw [h0]; exact Nat.le_succ_of_le h.usedO_le,
         by rw [h0]; exact Nat.le_succ_of_le h.usedN_le,
         by rw [h0]; exact Nat.le_succ_of_le h.kyb_le,
         by rw [h0]; exact Nat.le_succ_of_le h.adv_le,
         by rw [h0, h1, h2]; omega⟩

theorem shcrOnBaseArm_sim (S : Setup) (b : QueryBudget) (c : Fin 3 → ℕ)
    {A : Ty pqAtomicSig} {P : Ty pqSig}
    (payE : Expr pqAtomicOps [A, shcrKindStTy, (pqKeyIndCodec S).Q] (embedTy P))
    (brK brFull : (g : Var [keyIndStateTy, shcrStTy, P] keyIndStateTy) →
      Comp pqxdhOps _root_.SignalPqxdh.LegacyCosted.pqPrimIface [keyIndStateTy, shcrStTy, P] RS)
    (hUnsup : (onBase (Γ₁ := [shcrStTy, P]) .zero brK).queries
      tlPrimKeyInd.unsupportedW (fun _ => 0) = 0)
    (a : A.denote) (sK : shcrKindStTy.denote) (t : KeyIndQuery S) (p : P.denote)
    (hPay : payE.eval (.cons a (.cons sK (.cons ((pqKeyIndCodec S).qenc t) .nil))) = embedVal P p)
    (hOn : isKeyIndOnlineQuery (.inr t) = true)
    (hInv : ShcrSimInv S b c sK)
    (hFuelEq : (brK .zero).eval
        (.cons (projVal shcrStTy sK.1).1 (.cons (projVal shcrStTy sK.1) (.cons p .nil))) =
      (brFull .zero).eval
        (.cons (projVal shcrStTy sK.1).1
          (.cons (fixShcrLegacySent S b (projVal shcrStTy sK.1)) (.cons p .nil))))
    (hMemPres : ∀ r ∈ support ((brK .zero).eval
        (.cons (projVal shcrStTy sK.1).1 (.cons (projVal shcrStTy sK.1) (.cons p .nil)))),
      BaseOnlineLenInv (bumpPred (keyIndSimPred S) c t) r.2 ∧
      stRoList r.2 = stRoList (projVal shcrStTy sK.1).1) :
    Prod.map id (forgetShcrKindActive S b) <$>
        (shcrLiftLegArmK S payE (onBase (Γ₁ := [shcrStTy, P]) .zero brK)).eval
          (.cons a (.cons sK (.cons ((pqKeyIndCodec S).qenc t) .nil))) =
      embedVal SCS <$>
        (onBase (Γ₁ := [shcrStTy, P]) .zero brFull).eval
          (.cons (fixShcrLegacySent S b (projVal shcrStTy sK.1)) (.cons p .nil)) ∧
    ∀ vs' ∈ support ((shcrLiftLegArmK S payE (onBase (Γ₁ := [shcrStTy, P]) .zero brK)).eval
        (.cons a (.cons sK (.cons ((pqKeyIndCodec S).qenc t) .nil)))),
      ShcrSimInv S b (bumpPred (keyIndSimPred S) c t) vs'.2 := by
  rcases hsL : projVal shcrStTy sK.1 with ⟨bSt, tb, tpk, tsk, cnt, ir, rr, sidx, ch⟩
  obtain ⟨h0, _, h2⟩ := bumpPred_online S c hOn
  simp only [hsL] at hFuelEq hMemPres
  refine ⟨?_, ?_⟩
  · rw [shcrLiftLegArmK_map_forget S b payE _ hUnsup a sK _ p hPay]
    congr 1
    simp only [hsL, onBase, letV, bindV, Comp.eval, pure_bind, map_eq_bind_pure_comp, bind_assoc,
      Function.comp_def, scBase, scUpd, scCnt, scIR, scRR, scTB, scTPk, scTSk, scSIdx, scChosen,
      Expr.eval, Env.get, v, Ext.wk]
    rw [show (fixShcrLegacySent S b (bSt, tb, tpk, tsk, cnt, ir, rr, sidx, ch)).1 = bSt from rfl,
      hFuelEq]
    rfl
  · intro vs' hvs'
    rw [shcrLiftLegArmK_eval_eq S payE _ hUnsup a sK _ p hPay, map_eq_bind_pure_comp,
      mem_support_bind_iff] at hvs'
    rcases hvs' with ⟨rsOut, hrsMem, hvsEq⟩
    simp only [Function.comp_def, support_pure, Set.mem_singleton_iff] at hvsEq
    subst hvsEq
    simp only [hsL, onBase, letV, bindV, Comp.eval, pure_bind, mem_support_bind_iff, support_pure,
      Set.mem_singleton_iff, scBase, scUpd, scTB, scTPk, scTSk, scCnt, scIR, scRR, scSIdx, scChosen,
      Expr.eval, Env.get, v, Ext.wk] at hrsMem
    rcases hrsMem with ⟨r, hrMem, hrsEq⟩
    subst hrsEq
    obtain ⟨hOnline', hRoEq⟩ := hMemPres r hrMem
    have hBSt : projVal keyIndStateTy sK.1.1 = bSt := congrArg Prod.fst hsL
    let sNew : shcrStTy.denote := (r.2, tb, tpk, tsk, cnt, ir, rr, sidx, ch)
    have hProjS' : projVal shcrStTy (embedVal shcrStTy sNew) = sNew := projVal_embedVal shcrStTy sNew
    have hProjB' : projVal keyIndStateTy (embedVal shcrStTy sNew).1 = r.2 :=
      projVal_embedVal keyIndStateTy r.2
    change ShcrSimInv S b (bumpPred (keyIndSimPred S) c t) (embedVal shcrStTy sNew, sK.2)
    refine ⟨⟨?_, ?_, ?_⟩, ?_, ?_, ?_⟩
    · simpa only [hProjB'] using hOnline'
    · simp only [hProjB', hRoEq, h2]
      have hRoLen : (stRoList bSt).length ≤ c 2 := by simpa only [hBSt] using hInv.core_inv.ro_len
      exact Nat.le_succ_of_le hRoLen
    · simp only [hProjB', hRoEq]
      simpa only [hBSt] using hInv.core_inv.ro_avl
    · simp only [hProjS', sNew, h0]; exact Nat.le_succ_of_le (by simpa only [hsL] using hInv.cnt_le)
    · simp only [hProjS', sNew, h0]; exact Nat.le_succ_of_le (by simpa only [hsL] using hInv.ir_le)
    · simp only [hProjS', sNew, h0]; exact Nat.le_succ_of_le (by simpa only [hsL] using hInv.rr_le)

private theorem online_fuel_bounds (S : Setup) (b : QueryBudget) {c : Fin 3 → ℕ}
    {t : KeyIndQuery S} (hOn : isKeyIndOnlineQuery (.inr t) = true) (hSum : c 0 + c 1 = c 2)
    (hBound : ∀ j, bumpPred (keyIndSimPred S) c t j ≤ keyIndSimBounds b j) :
    c 0 + 1 ≤ (keyIndCoreFuels S b).M_on ∧ (keyIndCoreFuels S b).M_on ≤ keyIndLoopBound b := by
  obtain ⟨h0, _, h2⟩ := bumpPred_online S c hOn
  have hb0 := hBound 0; have hb2 := hBound 2; rw [h0] at hb0; rw [h2] at hb2
  simp only [keyIndSimBounds, keyIndLoopBound, keyIndCoreFuels] at hb0 hb2 ⊢; omega

private theorem baseTuple_preserves_online_ro {c c' : Fin 3 → ℕ} (s0 : keyIndStateTy.denote)
    (prin : (Ty.list (.prod .nat principalEntryTy)).denote)
    (spks : (Ty.list (.prod (.prod .nat .nat) spkBundleEntryTy)).denote)
    (opks : (Ty.list (.prod (.prod .nat (.prod .nat .nat))
      _root_.SignalPqxdh.Security.ReductionDsl.KeyInd.opkEntryTy)).denote)
    (adv : (Ty.list (.prod (_root_.SignalPqxdh.LegacyCosted.B 32)
      (_root_.SignalPqxdh.LegacyCosted.B 32))).denote)
    (hb : BaseOnlineLenInv c s0) (hle : c 0 ≤ c' 0) (hSum' : c' 0 + c' 1 = c' 2)
    (hp : prin.length ≤ c' 0) (hs : spks.length ≤ c' 0)
    (ho : opks.length ≤ c' 0) (ha : adv.length ≤ c' 0) :
    let s' : keyIndStateTy.denote :=
      (s0.1, prin, spks, opks, s0.2.2.2.2.1, s0.2.2.2.2.2.1,
       s0.2.2.2.2.2.2.1, s0.2.2.2.2.2.2.2.1, s0.2.2.2.2.2.2.2.2.1, s0.2.2.2.2.2.2.2.2.2.1, adv)
    BaseOnlineLenInv c' s' ∧ stRoList s' = stRoList s0 :=
  ⟨{ prin_le := hp, spks_le := hs, opks_le := ho, sess_le := Nat.le_trans hb.sess_le hle,
     resps_le := Nat.le_trans hb.resps_le hle, usedO_le := Nat.le_trans hb.usedO_le hle,
     usedN_le := Nat.le_trans hb.usedN_le hle, kyb_le := Nat.le_trans hb.kyb_le hle,
     adv_le := ha, counts_eq := hSum' }, rfl⟩

@[expose] def activePostEval (S : Setup) (b : QueryBudget) (sK : shcrKindStTy.denote)
    (t : KeyIndQuery S) :
    OracleComp _root_.SignalPqxdh.PrimBaseSpec ((pqKeyIndCodec S).R.denote × (embedTy shcrStTy).denote) :=
  embedVal SCS <$>
    (shcr1KeyActivePostC S (keyIndLoopBound b)
      (Γ₁ := [shcrStTy, _root_.SignalPqxdh.Security.ReductionDsl.KeyInd.keyIndQueryTy])
      (Γ₂ := [_root_.SignalPqxdh.Security.ReductionDsl.KeyInd.keyIndQueryTy])
      (Δ := [shcrStTy, _root_.SignalPqxdh.Security.ReductionDsl.KeyInd.keyIndQueryTy])
      .zero .zero).eval
      (.cons (fixShcrLegacySent S b (projVal shcrStTy sK.1))
        (.cons ((_root_.SignalPqxdh.LegacyCosted.keyIndCodec S).qenc t) .nil))

@[expose] def activePreEval (S : Setup) (b : QueryBudget) (sK : shcrKindStTy.denote)
    (t : KeyIndQuery S) :
    OracleComp _root_.SignalPqxdh.PrimBaseSpec
      ((pqKeyIndCodec S).R.denote × (embedTy shcrStTy).denote ⊕
        (PB (ℓ := 0) (Pt := Empty) 1568).denote ×
          ((embedTy pauseTy).denote × (embedTy shcrStTy).denote)) :=
  embedVal (.sum SCS (.prod (_root_.SignalPqxdh.LegacyCosted.B 1568) (.prod pauseTy shcrStTy))) <$>
    (shcr1KeyActivePreC S (keyIndLoopBound b)
      (Γ₁ := [shcrStTy, _root_.SignalPqxdh.Security.ReductionDsl.KeyInd.keyIndQueryTy])
      (Γ₂ := [_root_.SignalPqxdh.Security.ReductionDsl.KeyInd.keyIndQueryTy])
      (Δ := [shcrStTy, _root_.SignalPqxdh.Security.ReductionDsl.KeyInd.keyIndQueryTy])
      .zero .zero).eval
      (.cons (fixShcrLegacySent S b (projVal shcrStTy sK.1))
        (.cons ((_root_.SignalPqxdh.LegacyCosted.keyIndCodec S).qenc t) .nil))

private theorem initPrin1KeyB_eval_congr (K : ℕ)
    {Γ₁ Γ₂ Δ : List PT} (st : Var Γ₁ keyIndStateTy) (u : Var Γ₂ .nat)
    [Ext Γ₁ Δ] [Ext Γ₂ Δ] (env : Env Δ)
    {Γ₁' Γ₂' Δ' : List PT} (st' : Var Γ₁' keyIndStateTy) (u' : Var Γ₂' .nat)
    [Ext Γ₁' Δ'] [Ext Γ₂' Δ'] (env' : Env Δ')
    (hst : (v st).eval env = (v st').eval env')
    (hu : (v u).eval env = (v u').eval env') :
    (initPrin1KeyB K st u).eval env = (initPrin1KeyB K st' u').eval env' := by
  simp only [initPrin1KeyB, bindV, eAny, natEq, sBytes32, qX25519Base,
    stPrin, stSecb, stSpks, stOpks, stSess,
    stResps, stUsedO, stUsedN, stKyb, stRo, stAdv, stUpd,
    _root_.SignalPqxdh.Security.ReductionDsl.KeyInd.stMk,
    _root_.SignalPqxdh.Security.ReductionDsl.KeyInd.peMk, rs, rNone,
    _root_.SignalPqxdh.Security.ReductionDsl.KeyInd.rInitPrin,
    Comp.eval, Expr.eval, v_eval_cons, v_zero_eval, hst, hu]
  rfl

private theorem initPrin1KeyB_pres (S : Setup) (K : ℕ) {c : Fin 3 → ℕ}
    {t : KeyIndQuery S} (hOn : isKeyIndOnlineQuery (.inr t) = true)
    {Γ₁ Γ₂ Δ : List PT} (st : Var Γ₁ keyIndStateTy) (u : Var Γ₂ .nat)
    [Ext Γ₁ Δ] [Ext Γ₂ Δ] (env : Env Δ)
    (hb : BaseOnlineLenInv c ((v st).eval env)) :
    ∀ r ∈ support ((initPrin1KeyB K st u).eval env),
      BaseOnlineLenInv (bumpPred (keyIndSimPred S) c t) r.2 ∧
      stRoList r.2 = stRoList ((v st).eval env) := by
  obtain ⟨h0, h1, h2⟩ := bumpPred_online S c hOn
  have hSum' : bumpPred (keyIndSimPred S) c t 0 + bumpPred (keyIndSimPred S) c t 1 =
      bumpPred (keyIndSimPred S) c t 2 := by
    have := hb.counts_eq; omega
  have hle : c 0 ≤ bumpPred (keyIndSimPred S) c t 0 := by omega
  intro r hr
  simp only [initPrin1KeyB, bindV, Comp.eval] at hr
  split_ifs at hr
  · simp only [rs, mem_support_pure_iff, Expr.eval] at hr
    subst hr
    exact ⟨BaseOnlineLenInv.mono_online hOn hb, rfl⟩
  · simp only [mem_support_bind_iff, mem_support_pure_iff] at hr
    rcases hr with ⟨s0, _, ik, _, rfl⟩
    simp only [rs, stUpd, _root_.SignalPqxdh.Security.ReductionDsl.KeyInd.stMk,
      stSecb, stPrin, stSpks, stOpks, stSess, stResps, stUsedO, stUsedN, stKyb, stRo, stAdv,
      Expr.eval, v_eval_cons, v_zero_eval]
    exact baseTuple_preserves_online_ro ((v st).eval env) _ _ _ _ hb hle hSum'
      (by simp only [List.length_cons]; have h := hb.prin_le; simp only [stPrinList] at h; omega)
      (Nat.le_trans hb.spks_le hle)
      (Nat.le_trans hb.opks_le hle)
      (Nat.le_trans hb.adv_le hle)

theorem shcrInitPrinArm_sim (S : Setup) (b : QueryBudget) (c : Fin 3 → ℕ)
    (sK : shcrKindStTy.denote) (u : Fin S.N_id)
    (hInv : ShcrSimInv S b c sK)
    (hBound : ∀ j, bumpPred (keyIndSimPred S) c (.initPrin u) j ≤ keyIndSimBounds b j) :
    let f := keyIndCoreFuels S b
    let t : KeyIndQuery S := .initPrin u
    let arm := shcrLiftLegArmK S (P := .nat) (aop (.finVal S.N_id) .v0) (shcrInitPrin1KeyLeg f.M_on)
    Prod.map id (forgetShcrKindActive S b) <$>
        arm.eval (.cons u (.cons sK (.cons ((pqKeyIndCodec S).qenc t) .nil))) =
      activePostEval S b sK t ∧
    ∀ vs' ∈ support (arm.eval (.cons u (.cons sK (.cons ((pqKeyIndCodec S).qenc t) .nil)))),
      ShcrSimInv S b (bumpPred (keyIndSimPred S) c t) vs'.2 := by
  intro f t arm
  have hOn : isKeyIndOnlineQuery (.inr t) = true := by simp [isKeyIndOnlineQuery, t]
  have hOnInv : BaseOnlineLenInv c (projVal shcrStTy sK.1).1 := hInv.core_inv.online_len
  obtain ⟨hc0, hMle⟩ := online_fuel_bounds S b hOn hOnInv.counts_eq hBound
  let xV : Var [keyIndStateTy, shcrStTy, .nat] .nat := .succ (.succ .zero)
  have hSim := shcrOnBaseArm_sim S b c (aop (.finVal S.N_id) .v0)
    (fun g => initPrin1KeyB f.M_on g xV)
    (fun g => initPrin1KeyB (keyIndLoopBound b) g xV)
    (shcrInitPrin1KeyLeg_unsup f.M_on) u sK t u.val rfl hOn hInv
    (by
      rw [initPrin1KeyB_min_eq .zero xV _
        (Nat.le_trans hOnInv.prin_le (Nat.le_of_succ_le hc0)) hMle]
      refine initPrin1KeyB_eval_congr (keyIndLoopBound b) _ _ _ _ _ _ ?_ ?_ <;> rfl)
    (initPrin1KeyB_pres S f.M_on hOn .zero xV _ hOnInv)
  refine ⟨hSim.1.trans ?_, hSim.2⟩
  dsimp only [activePostEval]
  apply congrArg (embedVal SCS <$> ·)
  simp only [shcr1KeyActivePostC, _root_.SignalPqxdh.LegacyCosted.keyIndCodec,
    _root_.SignalPqxdh.LegacyCosted.keyIndQenc, caseSumV, onBase, letV, bindV,
    Comp.eval, Expr.eval, pure_bind, Env.get, v, Ext.wk]
  exact congrArg₂ Bind.bind
    (by refine initPrin1KeyB_eval_congr (keyIndLoopBound b) _ _ _ _ _ _ ?_ ?_ <;> rfl) rfl

private theorem corruptB_eval_congr (K : ℕ)
    {Γ₁ Γ₂ Δ : List PT} (st : Var Γ₁ keyIndStateTy) (u : Var Γ₂ .nat)
    [Ext Γ₁ Δ] [Ext Γ₂ Δ] (env : Env Δ)
    {Γ₁' Γ₂' Δ' : List PT} (st' : Var Γ₁' keyIndStateTy) (u' : Var Γ₂' .nat)
    [Ext Γ₁' Δ'] [Ext Γ₂' Δ'] (env' : Env Δ')
    (hst : (v st).eval env = (v st').eval env')
    (hu : (v u).eval env = (v u').eval env') :
    (corruptB K st u).eval env = (corruptB K st' u').eval env' := by
  have hFind : (eFind K (stPrin (v st)) fun e => natEq (.fst (v e)) (v u)).eval env =
      (eFind K (stPrin (v st')) fun e => natEq (.fst (v e)) (v u')).eval env' := by
    simp only [eFind, stPrin, natEq, Expr.eval, v_eval_cons, v_zero_eval, hst, hu]
    rfl
  simp only [corruptB, caseOptV, Comp.eval, hFind]
  cases (eFind K (stPrin (v st')) fun e => natEq (.fst (v e)) (v u')).eval env' with
  | none =>
    simp only [rs, rNone, Expr.eval, hst]
  | some eVal =>
    simp only [rs, _root_.SignalPqxdh.Security.ReductionDsl.KeyInd.rCorr, peSecIKA0, peSecIKAsign,
      _root_.SignalPqxdh.Security.ReductionDsl.KeyInd.peUpd,
      _root_.SignalPqxdh.Security.ReductionDsl.KeyInd.peMk,
      _root_.SignalPqxdh.Security.ReductionDsl.KeyInd.peIkAPk,
      _root_.SignalPqxdh.Security.ReductionDsl.KeyInd.peIkSignPk,
      stUpd, _root_.SignalPqxdh.Security.ReductionDsl.KeyInd.stMk,
      stSecb, stPrin, stSpks, stOpks, stSess, stResps, stUsedO, stUsedN, stKyb, stRo, stAdv,
      eMap, natEq, Expr.eval, v_eval_cons, v_zero_eval, hst, hu]
    rfl

private theorem corruptB_pres (S : Setup) (K : ℕ) {c : Fin 3 → ℕ}
    {t : KeyIndQuery S} (hOn : isKeyIndOnlineQuery (.inr t) = true)
    {Γ₁ Γ₂ Δ : List PT} (st : Var Γ₁ keyIndStateTy) (u : Var Γ₂ .nat)
    [Ext Γ₁ Δ] [Ext Γ₂ Δ] (env : Env Δ)
    (hb : BaseOnlineLenInv c ((v st).eval env)) :
    ∀ r ∈ support ((corruptB K st u).eval env),
      BaseOnlineLenInv (bumpPred (keyIndSimPred S) c t) r.2 ∧
      stRoList r.2 = stRoList ((v st).eval env) := by
  obtain ⟨h0, h1, h2⟩ := bumpPred_online S c hOn
  have hSum' : bumpPred (keyIndSimPred S) c t 0 + bumpPred (keyIndSimPred S) c t 1 =
      bumpPred (keyIndSimPred S) c t 2 := by have := hb.counts_eq; omega
  have hle : c 0 ≤ bumpPred (keyIndSimPred S) c t 0 := by omega
  intro r hr
  simp only [corruptB, caseOptV, Comp.eval] at hr
  split at hr
  · simp only [rs, mem_support_pure_iff, Expr.eval] at hr
    subst hr
    exact ⟨BaseOnlineLenInv.mono_online hOn hb, rfl⟩
  · simp only [mem_support_pure_iff] at hr
    subst hr
    simp only [rs, stUpd, _root_.SignalPqxdh.Security.ReductionDsl.KeyInd.stMk,
      stSecb, stPrin, stSpks, stOpks, stSess, stResps, stUsedO, stUsedN, stKyb, stRo, stAdv,
      eMap, Expr.eval, v_eval_cons, v_zero_eval]
    refine baseTuple_preserves_online_ro ((v st).eval env) _ _ _ _ hb hle hSum'
      ?_ (Nat.le_trans hb.spks_le hle) (Nat.le_trans hb.opks_le hle) (Nat.le_trans hb.adv_le hle)
    simp only [List.length_map, List.length_take]
    exact Nat.le_trans (Nat.min_le_right _ _) (Nat.le_trans hb.prin_le hle)

theorem shcrCorruptArm_sim (S : Setup) (b : QueryBudget) (c : Fin 3 → ℕ)
    (sK : shcrKindStTy.denote) (u : Fin S.N_id)
    (hInv : ShcrSimInv S b c sK)
    (hBound : ∀ j, bumpPred (keyIndSimPred S) c (.corruptIK u) j ≤ keyIndSimBounds b j) :
    let f := keyIndCoreFuels S b
    let t : KeyIndQuery S := .corruptIK u
    let arm := shcrLiftLegArmK S (P := .nat) (aop (.finVal S.N_id) .v0) (shcrCorruptLeg f.M_on)
    Prod.map id (forgetShcrKindActive S b) <$>
        arm.eval (.cons u (.cons sK (.cons ((pqKeyIndCodec S).qenc t) .nil))) =
      activePostEval S b sK t ∧
    ∀ vs' ∈ support (arm.eval (.cons u (.cons sK (.cons ((pqKeyIndCodec S).qenc t) .nil)))),
      ShcrSimInv S b (bumpPred (keyIndSimPred S) c t) vs'.2 := by
  intro f t arm
  have hOn : isKeyIndOnlineQuery (.inr t) = true := by simp [isKeyIndOnlineQuery, t]
  have hOnInv : BaseOnlineLenInv c (projVal shcrStTy sK.1).1 := hInv.core_inv.online_len
  obtain ⟨hc0, hMle⟩ := online_fuel_bounds S b hOn hOnInv.counts_eq hBound
  let xV : Var [keyIndStateTy, shcrStTy, .nat] .nat := .succ (.succ .zero)
  have hSim := shcrOnBaseArm_sim S b c (aop (.finVal S.N_id) .v0)
    (fun g => corruptB f.M_on g xV)
    (fun g => corruptB (keyIndLoopBound b) g xV)
    (shcrCorruptLeg_unsup f.M_on) u sK t u.val rfl hOn hInv
    (by
      rw [corruptB_min_eq .zero xV _
        (Nat.le_trans hOnInv.prin_le (Nat.le_of_succ_le hc0)) hMle]
      refine corruptB_eval_congr (keyIndLoopBound b) _ _ _ _ _ _ ?_ ?_ <;> rfl)
    (corruptB_pres S f.M_on hOn .zero xV _ hOnInv)
  refine ⟨hSim.1.trans ?_, hSim.2⟩
  dsimp only [activePostEval]
  apply congrArg (embedVal SCS <$> ·)
  simp only [shcr1KeyActivePostC, shcrActivePostTailC,
    _root_.SignalPqxdh.LegacyCosted.keyIndCodec,
    _root_.SignalPqxdh.LegacyCosted.keyIndQenc, caseSumV, onBase, letV, bindV,
    Comp.eval, Expr.eval, pure_bind, Env.get, v, Ext.wk]
  exact congrArg₂ Bind.bind
    (by refine corruptB_eval_congr (keyIndLoopBound b) _ _ _ _ _ _ ?_ ?_ <;> rfl) rfl

private theorem genSpkB_eval_congr (K : ℕ)
    {Γ₁ Γ₂ Δ : List PT} (st : Var Γ₁ keyIndStateTy)
    (x : Var Γ₂ (.prod .nat .nat))
    [Ext Γ₁ Δ] [Ext Γ₂ Δ] (env : Env Δ)
    {Γ₁' Γ₂' Δ' : List PT} (st' : Var Γ₁' keyIndStateTy)
    (x' : Var Γ₂' (.prod .nat .nat))
    [Ext Γ₁' Δ'] [Ext Γ₂' Δ'] (env' : Env Δ')
    (hst : (v st).eval env = (v st').eval env')
    (hx : (v x).eval env = (v x').eval env') :
    (genSpkB K st x).eval env = (genSpkB K st' x').eval env' := by
  have hAny : (eAny K (stSpks (v st)) fun e => nat2Eq (.fst (v e)) (v x)).eval env =
      (eAny K (stSpks (v st')) fun e => nat2Eq (.fst (v e)) (v x')).eval env' := by
    simp only [eAny, stSpks, nat2Eq, natEq, Expr.eval, v_eval_cons, v_zero_eval, hst, hx]
    rfl
  have hFind : (eFind K (stPrin (v st)) fun e => natEq (.fst (v e)) (.fst (v x))).eval env =
      (eFind K (stPrin (v st')) fun e => natEq (.fst (v e)) (.fst (v x'))).eval env' := by
    simp only [eFind, stPrin, natEq, Expr.eval, v_eval_cons, v_zero_eval, hst, hx]
    rfl
  simp only [genSpkB, caseOptV, Comp.eval, hAny, hFind]
  split_ifs
  · simp only [rs, rNone, Expr.eval, hst]
  · cases (eFind K (stPrin (v st')) fun e => natEq (.fst (v e)) (.fst (v x'))).eval env' with
    | none => simp only [rs, rNone, Expr.eval, hst]
    | some uE =>
      simp only [bindV, Comp.eval, sBytes32, qX25519Base, sRandom64, qSigSign, qKemKeyGen,
        _root_.SignalPqxdh.Security.ReductionDsl.KeyInd.consB,
        rs, rBundle, buMk, peIkAPk, peSecIKAsign, u32OfNat,
        encEC, encKEM, sbMk, stUpd, _root_.SignalPqxdh.Security.ReductionDsl.KeyInd.stMk,
        stSecb, stPrin, stSpks, stOpks, stSess, stResps, stUsedO, stUsedN, stKyb, stRo, stAdv,
        Expr.eval, v_eval_cons, v_zero_eval, hst, hx]
      refine congrArg₂ Bind.bind rfl (funext fun spkSk => congrArg₂ Bind.bind rfl (funext fun spkPk =>
        congrArg₂ Bind.bind rfl (funext fun r1 => congrArg₂ Bind.bind rfl (funext fun sig1 =>
        congrArg₂ Bind.bind rfl (funext fun seed => congrArg₂ Bind.bind rfl (funext fun kp =>
        congrArg₂ Bind.bind rfl (funext fun r2 => congrArg₂ Bind.bind rfl (funext fun sig2 => ?_))))))))
      apply congrArg pure
      exact congrArg (fun p : ℕ × ℕ => ((Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inl
        (uE.2.2.1, pqxdhOps.eval (.inr .ofNat) p.2, spkPk, sig1, none,
         pqxdhOps.eval (.inr .ofNat) p.2, kp.1, sig2))))),
        ((v st').eval env').1, ((v st').eval env').2.1,
        ((v x').eval env', spkSk, spkPk, sig1, kp.2, kp.1, sig2, false) :: ((v st').eval env').2.2.1,
        ((v st').eval env').2.2.2.1, ((v st').eval env').2.2.2.2.1, ((v st').eval env').2.2.2.2.2.1,
        ((v st').eval env').2.2.2.2.2.2.1, ((v st').eval env').2.2.2.2.2.2.2.1,
        ((v st').eval env').2.2.2.2.2.2.2.2.1, ((v st').eval env').2.2.2.2.2.2.2.2.2.1,
        ((v st').eval env').2.2.2.2.2.2.2.2.2.2) : _root_.SignalPqxdh.Security.ReductionDsl.KeyInd.RS.denote)) hx

private theorem genSpkB_pres (S : Setup) (K : ℕ) {c : Fin 3 → ℕ}
    {t : KeyIndQuery S} (hOn : isKeyIndOnlineQuery (.inr t) = true)
    {Γ₁ Γ₂ Δ : List PT} (st : Var Γ₁ keyIndStateTy)
    (x : Var Γ₂ (.prod .nat .nat))
    [Ext Γ₁ Δ] [Ext Γ₂ Δ] (env : Env Δ)
    (hb : BaseOnlineLenInv c ((v st).eval env)) :
    ∀ r ∈ support ((genSpkB K st x).eval env),
      BaseOnlineLenInv (bumpPred (keyIndSimPred S) c t) r.2 ∧
      stRoList r.2 = stRoList ((v st).eval env) := by
  obtain ⟨h0, h1, h2⟩ := bumpPred_online S c hOn
  have hSum' : bumpPred (keyIndSimPred S) c t 0 + bumpPred (keyIndSimPred S) c t 1 =
      bumpPred (keyIndSimPred S) c t 2 := by have := hb.counts_eq; omega
  have hle : c 0 ≤ bumpPred (keyIndSimPred S) c t 0 := by omega
  intro r hr
  simp only [genSpkB, caseOptV, bindV, Comp.eval] at hr
  split_ifs at hr
  · simp only [rs, mem_support_pure_iff, Expr.eval] at hr
    subst hr
    exact ⟨BaseOnlineLenInv.mono_online hOn hb, rfl⟩
  · split at hr
    · simp only [rs, mem_support_pure_iff, Expr.eval] at hr
      subst hr
      exact ⟨BaseOnlineLenInv.mono_online hOn hb, rfl⟩
    · simp only [mem_support_bind_iff, mem_support_pure_iff] at hr
      rcases hr with ⟨spkSk, _, spkPk, _, r1, _, sig1, _, seed, _, kp, _, r2, _, sig2, _, rfl⟩
      simp only [rs, stUpd, _root_.SignalPqxdh.Security.ReductionDsl.KeyInd.stMk,
        stSecb, stPrin, stSpks, stOpks, stSess, stResps, stUsedO, stUsedN, stKyb, stRo, stAdv,
        Expr.eval, v_eval_cons, v_zero_eval]
      exact baseTuple_preserves_online_ro ((v st).eval env) _ _ _ _ hb hle hSum'
        (Nat.le_trans hb.prin_le hle)
        (by simp only [List.length_cons]; have h := hb.spks_le; simp only [stSpksList] at h; omega)
        (Nat.le_trans hb.opks_le hle)
        (Nat.le_trans hb.adv_le hle)

private theorem shcrActiveGenSpkLeg_forget_eq (S : Setup) (b : QueryBudget) (K : ℕ)
    (sL : shcrStTy.denote) (p : (Ty.prod .nat .nat).denote)
    {Γ₁ Γ₂ Δ : List PT} (s : Var Γ₁ shcrStTy) (x : Var Γ₂ (.prod .nat .nat))
    [Ext Γ₁ Δ] [Ext Γ₂ Δ] (env' : Env Δ)
    (hs : (v s).eval env' = fixShcrLegacySent S b sL)
    (hx : (v x).eval env' = p) :
    Prod.map id (fixShcrLegacySent S b) <$>
        (shcrActiveGenSpkLeg S K).eval (.cons sL (.cons p .nil)) =
      (shcrActiveGenSpkB S K s x).eval env' := by
  have hsGet : env'.get (Ext.wk s) = fixShcrLegacySent S b sL := hs
  have hxGet : env'.get (Ext.wk x) = p := hx
  rcases sL with ⟨bSt, tb, tpk, tsk, cnt, ir, rr, sidx, ch⟩
  have hTBL : (scTB (v (Δ := [shcrStTy, .prod .nat .nat])
      (.zero : Var [shcrStTy, .prod .nat .nat] shcrStTy))).eval
      (.cons (bSt, tb, tpk, tsk, cnt, ir, rr, sidx, ch) (.cons p .nil)) = tb := rfl
  have hTB : (scTB (v s)).eval env' = tb := by
    simp only [Expr.eval, v, hsGet, fixShcrLegacySent]
  have hMapBindPure : ∀ {α β γ : Type} (g : β → γ)
      (m : OracleComp _root_.SignalPqxdh.PrimBaseSpec α) (f : α → β),
      (g <$> (m >>= fun r => pure (f r))) = (m >>= fun r => pure (g (f r))) := by
    intro α β γ g m f
    rw [map_eq_bind_pure_comp, bind_assoc]
    simp only [pure_bind, Function.comp_def]
  simp only [shcrActiveGenSpkLeg, shcrActiveGenSpkB, caseOptV, Comp.eval, hTBL, hTB]
  cases tb with
  | none =>
    simp only [onBase, letV, bindV, Comp.eval, pure_bind]
    rw [hMapBindPure]
    refine congrArg₂ Bind.bind
      (genSpkB_eval_congr K _ _ _ _ _ _
        (by simp only [fixShcrLegacySent, Expr.eval, v, ext_refl_wk, env_get_zero, hsGet])
        (by simp only [Expr.eval, v, ext_step_wk, ext_refl_wk, env_get_succ, env_get_zero, hxGet]))
      (funext fun r => by
        simp only [Prod.map, id_eq, fixShcrLegacySent, Expr.eval, v, ext_step_wk,
          ext_refl_wk, env_get_succ, env_get_zero, hsGet])
  | some spkOrd =>
    dsimp only
    let s0 : shcrStTy.denote := (bSt, some spkOrd, tpk, tsk, cnt, ir, rr, sidx, ch)
    have hAny : (eAny K (stSpks (scBase (v (.zero : Var [shcrStTy, .prod .nat .nat] shcrStTy))))
        fun e => nat2Eq (.fst (v e))
          (v (.succ .zero : Var [shcrStTy, .prod .nat .nat] (.prod .nat .nat)))).eval
        (.cons spkOrd (.cons s0 (.cons p .nil))) =
        (eAny K (stSpks (scBase (v s))) fun e => nat2Eq (.fst (v e)) (v x)).eval
          (.cons spkOrd env') := by
      simp only [eAny, stSpks, scBase, nat2Eq, natEq, Expr.eval, v, ext_step_wk, ext_refl_wk,
        env_get_succ, env_get_zero, hsGet, hxGet, fixShcrLegacySent]
      rfl
    have hFind : (eFind K (stPrin (scBase (v (.zero : Var [shcrStTy, .prod .nat .nat] shcrStTy))))
        fun e => natEq (.fst (v e))
          (.fst (v (.succ .zero : Var [shcrStTy, .prod .nat .nat] (.prod .nat .nat))))).eval
        (.cons spkOrd (.cons s0 (.cons p .nil))) =
        (eFind K (stPrin (scBase (v s))) fun e => natEq (.fst (v e)) (.fst (v x))).eval
          (.cons spkOrd env') := by
      simp only [eFind, stPrin, scBase, natEq, Expr.eval, v, ext_step_wk, ext_refl_wk,
        env_get_succ, env_get_zero, hsGet, hxGet, fixShcrLegacySent]
      rfl
    rw [hAny]
    split_ifs
    · simp only [map_pure, Prod.map, id_eq, rNone, Expr.eval, v, ext_step_wk,
        ext_refl_wk, env_get_succ, env_get_zero, hsGet]
    · rw [hFind]
      cases (eFind K (stPrin (scBase (v s))) fun e => natEq (.fst (v e)) (.fst (v x))).eval
          (.cons spkOrd env') with
      | none =>
        simp only [map_pure, Prod.map, id_eq, rNone, Expr.eval, v, ext_step_wk,
          ext_refl_wk, env_get_succ, env_get_zero, hsGet]
      | some uE =>
        dsimp only
        have hLenEq : (Expr.not (natEq (.len (stSpks (scBase
            (v (.zero : Var [shcrStTy, .prod .nat .nat] shcrStTy)))))
            (.fst (v (.zero : Var (.prod .nat .nat :: [shcrStTy, .prod .nat .nat])
              (.prod .nat .nat)))))).eval
            (.cons uE (.cons spkOrd (.cons s0 (.cons p .nil)))) =
            (Expr.not (natEq (.len (stSpks (scBase (v s))))
              (.fst (v (.zero : Var (.prod .nat .nat :: Δ) (.prod .nat .nat)))))).eval
              (.cons uE (.cons spkOrd env')) := by
          simp only [natEq, stSpks, scBase, Expr.eval, v, ext_step_wk, ext_refl_wk,
            env_get_succ, env_get_zero, hsGet, fixShcrLegacySent]
          rfl
        rw [hLenEq]
        split_ifs
        · simp only [onBase, letV, bindV, Comp.eval, pure_bind]
          rw [hMapBindPure]
          refine congrArg₂ Bind.bind
            (genSpkB_eval_congr K _ _ _ _ _ _
              (by simp only [fixShcrLegacySent, Expr.eval, v, ext_step_wk, ext_refl_wk,
                    env_get_succ, env_get_zero, hsGet])
              (by simp only [Expr.eval, v, ext_step_wk, ext_refl_wk, env_get_succ, env_get_zero, hxGet]))
            (funext fun r => by
              simp only [Prod.map, id_eq, fixShcrLegacySent, Expr.eval, v, ext_step_wk,
                ext_refl_wk, env_get_succ, env_get_zero, hsGet])
        · have hStep : ∀ {Γ : List PT} {σ : PT}
              (c : Comp pqxdhOps _root_.SignalPqxdh.LegacyCosted.pqPrimIface Γ σ)
              (k : Var (σ :: Γ) σ → Comp pqxdhOps _root_.SignalPqxdh.LegacyCosted.pqPrimIface (σ :: Γ) SCS)
              (e : Env Γ),
              Prod.map id (fixShcrLegacySent S b) <$> (bindV c k).eval e =
                (c.eval e >>= fun z =>
                  Prod.map id (fixShcrLegacySent S b) <$> (k .zero).eval (.cons z e)) := by
            have hMB : ∀ {α β γ : Type} (g : β → γ)
                (m : OracleComp _root_.SignalPqxdh.PrimBaseSpec α)
                (f : α → OracleComp _root_.SignalPqxdh.PrimBaseSpec β),
                (g <$> (m >>= f)) = (m >>= fun z => g <$> f z) := by
              intro α β γ g m f
              rw [map_eq_bind_pure_comp, bind_assoc]
              exact bind_congr fun z => by rw [map_eq_bind_pure_comp]
            intro Γ σ c k e
            exact hMB (Prod.map id (fixShcrLegacySent S b)) (c.eval e)
              (fun z => (k .zero).eval (.cons z e))
          have hBV : ∀ {Γ : List PT} {σ τ : PT}
              (c : Comp pqxdhOps _root_.SignalPqxdh.LegacyCosted.pqPrimIface Γ σ)
              (k : Var (σ :: Γ) σ → Comp pqxdhOps _root_.SignalPqxdh.LegacyCosted.pqPrimIface (σ :: Γ) τ)
              (e : Env Γ),
              (bindV c k).eval e = (c.eval e >>= fun z => (k .zero).eval (.cons z e)) :=
            fun _ _ _ => rfl
          have hBC : ∀ {α β : Type}
              {m₁ m₂ : OracleComp _root_.SignalPqxdh.PrimBaseSpec α}
              {f₁ f₂ : α → OracleComp _root_.SignalPqxdh.PrimBaseSpec β},
              m₁ = m₂ → (∀ z, f₁ z = f₂ z) → (m₁ >>= f₁) = (m₂ >>= f₂) :=
            fun hm hf => hm ▸ bind_congr hf
          rw [hStep]; (conv_rhs => rw [hBV]); refine hBC rfl fun spkSk => ?_
          rw [hStep]; (conv_rhs => rw [hBV]); refine hBC rfl fun spkPk => ?_
          rw [hStep]; (conv_rhs => rw [hBV]); refine hBC rfl fun r1 => ?_
          rw [hStep]; (conv_rhs => rw [hBV]); refine hBC rfl fun sig1 => ?_
          rw [hStep]; (conv_rhs => rw [hBV]); refine hBC rfl fun r2 => ?_
          rw [hStep]; (conv_rhs => rw [hBV])
          have hEncEq :
              (encKEM (scTPk (v (.zero : Var [shcrStTy, .prod .nat .nat] shcrStTy)))).eval
                (.cons r2 (.cons sig1 (.cons r1 (.cons spkPk (.cons spkSk
                  (.cons uE (.cons spkOrd (.cons s0 (.cons p .nil))))))))) =
              (encKEM (scTPk (v s))).eval
                (.cons r2 (.cons sig1 (.cons r1 (.cons spkPk (.cons spkSk
                  (.cons uE (.cons spkOrd env'))))))) :=
            congrArg (fun stS : shcrStTy.denote =>
              (encKEM (Γ := [_root_.SignalPqxdh.LegacyCosted.B 1568]) (.var .zero)).eval
                (.cons (t := _root_.SignalPqxdh.LegacyCosted.B 1568) stS.2.2.1 .nil)) hsGet.symm
          have hQSign : ∀ {Γ₁' Γ₂' : List PT}
              (tag : _root_.SignalPqxdh.LegacyCosted.PTag)
              (e₁ : Expr pqxdhOps Γ₁' (_root_.SignalPqxdh.LegacyCosted.pqPrimIface.dom tag))
              (e₂ : Expr pqxdhOps Γ₂' (_root_.SignalPqxdh.LegacyCosted.pqPrimIface.dom tag))
              (ρ₁ : Env Γ₁') (ρ₂ : Env Γ₂'),
              e₁.eval ρ₁ = e₂.eval ρ₂ →
                (Comp.query (I := _root_.SignalPqxdh.LegacyCosted.pqPrimIface) tag e₁).eval ρ₁ =
                  (Comp.query (I := _root_.SignalPqxdh.LegacyCosted.pqPrimIface) tag e₂).eval ρ₂ := by
            intro _ _ tag e₁ e₂ ρ₁ ρ₂ h
            dsimp only [Comp.eval]
            exact congrArg (fun a => _root_.SignalPqxdh.LegacyCosted.pqPrimIface.dec tag a <$>
              liftM (OracleSpec.query (_root_.SignalPqxdh.LegacyCosted.pqPrimIface.enc tag a))) h
          refine hBC (hQSign (.sigSign 1569) _ _ _ _ (by
            simp only [Expr.eval]
            exact Prod.ext rfl (Prod.ext hEncEq rfl))) fun sig2 => ?_
          have hU32R :
              (u32OfNat (.snd (v (Δ := _root_.SignalPqxdh.LegacyCosted.B 64 ::
                _root_.SignalPqxdh.LegacyCosted.B 64 :: _root_.SignalPqxdh.LegacyCosted.B 64 ::
                _root_.SignalPqxdh.LegacyCosted.B 64 :: _root_.SignalPqxdh.LegacyCosted.B 32 ::
                _root_.SignalPqxdh.LegacyCosted.B 32 :: .prod .nat principalEntryTy ::
                .prod .nat .nat :: Δ) x))).eval
                (.cons sig2 (.cons r2 (.cons sig1 (.cons r1 (.cons spkPk
                  (.cons spkSk (.cons uE (.cons spkOrd env')))))))) =
              (u32OfNat (Γ := [.nat]) (.var .zero)).eval (.cons p.2 .nil) :=
            congrArg (fun q : ℕ × ℕ => (u32OfNat (Γ := [.nat]) (.var .zero)).eval (.cons q.2 .nil)) hxGet
          simp only [Comp.eval, map_pure]
          apply congrArg pure
          simp only [rBundle, Expr.eval, hU32R]
          simp only [Expr.eval, v, ext_step_wk, ext_refl_wk, env_get_succ, env_get_zero, hsGet, hxGet]
          rfl

private theorem shcrActiveGenSpkLeg_pres (S : Setup) (K : ℕ) {c : Fin 3 → ℕ}
    {t : KeyIndQuery S} (hOn : isKeyIndOnlineQuery (.inr t) = true)
    (sL : shcrStTy.denote) (p : (Ty.prod .nat .nat).denote)
    (hb : BaseOnlineLenInv c sL.1) :
    ∀ rsOut ∈ support ((shcrActiveGenSpkLeg S K).eval (.cons sL (.cons p .nil))),
      ∃ bSt', rsOut.2 = (bSt', sL.2) ∧
        BaseOnlineLenInv (bumpPred (keyIndSimPred S) c t) bSt' ∧
        stRoList bSt' = stRoList sL.1 := by
  rcases sL with ⟨bSt, tb, tpk, tsk, cnt, ir, rr, sidx, ch⟩
  obtain ⟨h0, h1, h2⟩ := bumpPred_online S c hOn
  have hSum' : bumpPred (keyIndSimPred S) c t 0 + bumpPred (keyIndSimPred S) c t 1 =
      bumpPred (keyIndSimPred S) c t 2 := by have := hb.counts_eq; omega
  have hle : c 0 ≤ bumpPred (keyIndSimPred S) c t 0 := by omega
  have hOnBase : ∀ {Δ' : List PT} [Ext [shcrStTy, .prod .nat .nat] Δ']
      (env₀ : Env Δ') (s₀ : shcrStTy.denote) (p₀ : (Ty.prod .nat .nat).denote),
      env₀.get (Ext.wk (.zero : Var [shcrStTy, .prod .nat .nat] shcrStTy)) = s₀ →
      env₀.get (Ext.wk (.succ .zero : Var [shcrStTy, .prod .nat .nat] (.prod .nat .nat))) = p₀ →
      (onBase (Δ := Δ') (.zero : Var [shcrStTy, .prod .nat .nat] shcrStTy)
        fun g => genSpkB K g (.succ .zero : Var [shcrStTy, .prod .nat .nat] (.prod .nat .nat))).eval env₀ =
      ((genSpkB K (.zero : Var [keyIndStateTy, .prod .nat .nat] keyIndStateTy)
          (.succ .zero : Var [keyIndStateTy, .prod .nat .nat] (.prod .nat .nat))).eval
          (.cons s₀.1 (.cons p₀ .nil)) >>= fun r =>
        pure (r.1, (r.2, s₀.2))) := by
    intro Δ' _ env₀ s₀ p₀ hs₀ hp₀
    simp only [onBase, letV, bindV, Comp.eval, pure_bind]
    refine congrArg₂ Bind.bind
      (genSpkB_eval_congr K _ _ _ _ _ _
        (by simp only [Expr.eval, v, ext_refl_wk, env_get_zero, hs₀])
        (by simp only [Expr.eval, v, ext_step_wk, ext_refl_wk, env_get_succ, env_get_zero, hp₀]))
      (funext fun r => ?_)
    apply congrArg pure
    simp only [Expr.eval, v, ext_step_wk, ext_refl_wk, env_get_succ, env_get_zero, hs₀]
  intro rsOut hrs
  simp only [shcrActiveGenSpkLeg, caseOptV, Comp.eval] at hrs
  have hTB0 : (scTB (v (Δ := [shcrStTy, .prod .nat .nat])
      (.zero : Var [shcrStTy, .prod .nat .nat] shcrStTy))).eval
      (.cons (bSt, tb, tpk, tsk, cnt, ir, rr, sidx, ch) (.cons p .nil)) = tb := rfl
  rw [hTB0] at hrs
  cases tb with
  | none =>
    rw [hOnBase _ (bSt, none, tpk, tsk, cnt, ir, rr, sidx, ch) p rfl rfl] at hrs
    rw [mem_support_bind_iff] at hrs
    rcases hrs with ⟨r, hr, hrs⟩
    rw [mem_support_pure_iff] at hrs
    subst hrs
    exact ⟨r.2, rfl, genSpkB_pres S K hOn
      (.zero : Var [keyIndStateTy, .prod .nat .nat] keyIndStateTy)
      (.succ .zero : Var [keyIndStateTy, .prod .nat .nat] (.prod .nat .nat))
      (.cons bSt (.cons p .nil)) hb r hr⟩
  | some spkOrd =>
    dsimp only at hrs; split_ifs at hrs
    · rw [mem_support_pure_iff] at hrs; subst hrs
      exact ⟨bSt, rfl, BaseOnlineLenInv.mono_online hOn hb, rfl⟩
    · split at hrs
      · rw [mem_support_pure_iff] at hrs; subst hrs
        exact ⟨bSt, rfl, BaseOnlineLenInv.mono_online hOn hb, rfl⟩
      · split_ifs at hrs
        · rw [hOnBase _ (bSt, some spkOrd, tpk, tsk, cnt, ir, rr, sidx, ch) p rfl rfl] at hrs
          rw [mem_support_bind_iff] at hrs
          rcases hrs with ⟨r, hr, hrs⟩
          rw [mem_support_pure_iff] at hrs
          subst hrs
          exact ⟨r.2, rfl, genSpkB_pres S K hOn
            (.zero : Var [keyIndStateTy, .prod .nat .nat] keyIndStateTy)
            (.succ .zero : Var [keyIndStateTy, .prod .nat .nat] (.prod .nat .nat))
            (.cons bSt (.cons p .nil)) hb r hr⟩
        · simp only [bindV, Comp.eval, mem_support_bind_iff, mem_support_pure_iff] at hrs
          rcases hrs with ⟨spkSk, _, spkPk, _, r1, _, sig1, _, r2, _, sig2, _, rfl⟩
          simp only [Expr.eval, v, ext_step_wk, ext_refl_wk, env_get_succ, env_get_zero]
          exact ⟨_, rfl, baseTuple_preserves_online_ro bSt _ _ _ _ hb hle hSum'
            (Nat.le_trans hb.prin_le hle)
            (by simp only [List.length_cons]; have h := hb.spks_le; simp only [stSpksList] at h; omega)
            (Nat.le_trans hb.opks_le hle)
            (Nat.le_trans hb.adv_le hle)⟩

theorem shcrGenSpkArm_sim (S : Setup) (b : QueryBudget) (c : Fin 3 → ℕ)
    (sK : shcrKindStTy.denote) (u : Fin S.N_id) (j : Fin S.N_recv)
    (hInv : ShcrSimInv S b c sK)
    (hBound : ∀ k, bumpPred (keyIndSimPred S) c (.genSPK u j) k ≤ keyIndSimBounds b k) :
    let f := keyIndCoreFuels S b
    let t : KeyIndQuery S := .genSPK u j
    let arm := shcrLiftLegArmK S (P := .prod .nat .nat)
      (finPairToNatE S.N_id S.N_recv .v0) (shcrActiveGenSpkLeg S f.M_on)
    Prod.map id (forgetShcrKindActive S b) <$>
        arm.eval (.cons (u, j) (.cons sK (.cons ((pqKeyIndCodec S).qenc t) .nil))) =
      activePostEval S b sK t ∧
    ∀ vs' ∈ support (arm.eval (.cons (u, j) (.cons sK (.cons ((pqKeyIndCodec S).qenc t) .nil)))),
      ShcrSimInv S b (bumpPred (keyIndSimPred S) c t) vs'.2 := by
  intro f t arm
  have hOn : isKeyIndOnlineQuery (.inr t) = true := by simp [isKeyIndOnlineQuery, t]
  have hOnInv : BaseOnlineLenInv c (projVal shcrStTy sK.1).1 := hInv.core_inv.online_len
  obtain ⟨hc0, hMle⟩ := online_fuel_bounds S b hOn hOnInv.counts_eq hBound
  obtain ⟨hb0, _, hb2⟩ := bumpPred_online S c hOn
  refine ⟨?_, ?_⟩
  · rw [shcrLiftLegArmK_map_forget S b (finPairToNatE S.N_id S.N_recv .v0)
      (shcrActiveGenSpkLeg S f.M_on) (shcrActiveGenSpkLeg_unsup S f.M_on)
      (u, j) sK _ (u.val, j.val) rfl]
    rw [shcrActiveGenSpkLeg_min_eq S (.cons (projVal shcrStTy sK.1) (.cons (u.val, j.val) .nil))
      hOnInv (Nat.le_of_succ_le hc0) hMle]
    congr 1
    simp only [shcr1KeyActivePostC, shcrActivePostTailC,
      _root_.SignalPqxdh.LegacyCosted.keyIndCodec,
      _root_.SignalPqxdh.LegacyCosted.keyIndQenc, caseSumV, Comp.eval, Expr.eval, Env.get, v,
      Ext.wk]
    exact shcrActiveGenSpkLeg_forget_eq S b (keyIndLoopBound b) (projVal shcrStTy sK.1)
      (u.val, j.val) _ _ _ rfl rfl
  · rcases hsL : projVal shcrStTy sK.1 with ⟨bSt, tb, tpk, tsk, cnt, ir, rr, sidx, ch⟩
    have hBSt : projVal keyIndStateTy sK.1.1 = bSt := congrArg Prod.fst hsL
    have hbBSt : BaseOnlineLenInv c bSt := by simpa only [hsL] using hOnInv
    intro vs' hvs'
    rw [shcrLiftLegArmK_eval_eq S (finPairToNatE S.N_id S.N_recv .v0)
      (shcrActiveGenSpkLeg S f.M_on) (shcrActiveGenSpkLeg_unsup S f.M_on)
      (u, j) sK _ (u.val, j.val) rfl, map_eq_bind_pure_comp, mem_support_bind_iff] at hvs'
    rcases hvs' with ⟨rsOut, hrsMem, hvsEq⟩
    simp only [Function.comp_def, mem_support_pure_iff] at hvsEq
    subst hvsEq
    rw [hsL] at hrsMem
    obtain ⟨bSt', hrs2, hOnline', hRoEq⟩ :=
      shcrActiveGenSpkLeg_pres S f.M_on hOn (bSt, tb, tpk, tsk, cnt, ir, rr, sidx, ch)
        (u.val, j.val) hbBSt rsOut hrsMem
    let sNew : shcrStTy.denote := (bSt', tb, tpk, tsk, cnt, ir, rr, sidx, ch)
    have hProjS' : projVal shcrStTy (embedVal shcrStTy sNew) = sNew := projVal_embedVal shcrStTy sNew
    have hProjB' : projVal keyIndStateTy (embedVal shcrStTy sNew).1 = bSt' :=
      projVal_embedVal keyIndStateTy bSt'
    rw [hrs2]
    change ShcrSimInv S b (bumpPred (keyIndSimPred S) c t) (embedVal shcrStTy sNew, sK.2)
    refine ⟨⟨?_, ?_, ?_⟩, ?_, ?_, ?_⟩
    · simpa only [hProjB'] using hOnline'
    · simp only [hProjB', hRoEq, hb2]
      exact Nat.le_succ_of_le (by simpa only [hBSt] using hInv.core_inv.ro_len)
    · simp only [hProjB', hRoEq]
      simpa only [hBSt] using hInv.core_inv.ro_avl
    · simp only [hProjS', sNew, hb0]
      exact Nat.le_succ_of_le (by simpa only [hsL] using hInv.cnt_le)
    · simp only [hProjS', sNew, hb0]
      exact Nat.le_succ_of_le (by simpa only [hsL] using hInv.ir_le)
    · simp only [hProjS', sNew, hb0]
      exact Nat.le_succ_of_le (by simpa only [hsL] using hInv.rr_le)

private theorem genOpkB_eval_congr (K : ℕ)
    {Γ₁ Γ₂ Δ : List PT} (st : Var Γ₁ keyIndStateTy)
    (x : Var Γ₂ (.prod .nat (.prod .nat .nat)))
    [Ext Γ₁ Δ] [Ext Γ₂ Δ] (env : Env Δ)
    {Γ₁' Γ₂' Δ' : List PT} (st' : Var Γ₁' keyIndStateTy)
    (x' : Var Γ₂' (.prod .nat (.prod .nat .nat)))
    [Ext Γ₁' Δ'] [Ext Γ₂' Δ'] (env' : Env Δ')
    (hst : (v st).eval env = (v st').eval env')
    (hx : (v x).eval env = (v x').eval env') :
    (genOpkB K st x).eval env = (genOpkB K st' x').eval env' := by
  simp only [genOpkB, bindV, eAny, nat3Eq, nat2Eq, natEq, sBytes32, qX25519Base,
    stOpks, stPrin, stSecb, stSpks, stSess,
    stResps, stUsedO, stUsedN, stKyb, stRo, stAdv, stUpd,
    _root_.SignalPqxdh.Security.ReductionDsl.KeyInd.stMk,
    _root_.SignalPqxdh.Security.ReductionDsl.KeyInd.oeMk, rs, rNone, rPk,
    Comp.eval, Expr.eval, v_eval_cons, v_zero_eval, hst, hx]
  rfl

private theorem genOpkB_pres (S : Setup) (K : ℕ) {c : Fin 3 → ℕ}
    {t : KeyIndQuery S} (hOn : isKeyIndOnlineQuery (.inr t) = true)
    {Γ₁ Γ₂ Δ : List PT} (st : Var Γ₁ keyIndStateTy)
    (x : Var Γ₂ (.prod .nat (.prod .nat .nat)))
    [Ext Γ₁ Δ] [Ext Γ₂ Δ] (env : Env Δ)
    (hb : BaseOnlineLenInv c ((v st).eval env)) :
    ∀ r ∈ support ((genOpkB K st x).eval env),
      BaseOnlineLenInv (bumpPred (keyIndSimPred S) c t) r.2 ∧
      stRoList r.2 = stRoList ((v st).eval env) := by
  obtain ⟨h0, h1, h2⟩ := bumpPred_online S c hOn
  have hSum' : bumpPred (keyIndSimPred S) c t 0 + bumpPred (keyIndSimPred S) c t 1 =
      bumpPred (keyIndSimPred S) c t 2 := by have := hb.counts_eq; omega
  have hle : c 0 ≤ bumpPred (keyIndSimPred S) c t 0 := by omega
  intro r hr
  simp only [genOpkB, bindV, Comp.eval] at hr
  split_ifs at hr
  · simp only [rs, mem_support_pure_iff, Expr.eval] at hr
    subst hr
    exact ⟨BaseOnlineLenInv.mono_online hOn hb, rfl⟩
  · simp only [mem_support_bind_iff, mem_support_pure_iff] at hr
    rcases hr with ⟨sk, _, pk, _, rfl⟩
    simp only [rs, stUpd, _root_.SignalPqxdh.Security.ReductionDsl.KeyInd.stMk,
      stSecb, stPrin, stSpks, stOpks, stSess, stResps, stUsedO, stUsedN, stKyb, stRo, stAdv,
      Expr.eval, v_eval_cons, v_zero_eval]
    exact baseTuple_preserves_online_ro ((v st).eval env) _ _ _ _ hb hle hSum'
      (Nat.le_trans hb.prin_le hle)
      (Nat.le_trans hb.spks_le hle)
      (by simp only [List.length_cons]; have h := hb.opks_le; simp only [stOpksList] at h; omega)
      (Nat.le_trans hb.adv_le hle)

theorem shcrGenOpkArm_sim (S : Setup) (b : QueryBudget) (c : Fin 3 → ℕ)
    (sK : shcrKindStTy.denote) (u : Fin S.N_id) (j : Fin S.N_recv) (o : Fin S.N_opk)
    (hInv : ShcrSimInv S b c sK)
    (hBound : ∀ k, bumpPred (keyIndSimPred S) c (.genOPK u j o) k ≤ keyIndSimBounds b k) :
    let f := keyIndCoreFuels S b
    let t : KeyIndQuery S := .genOPK u j o
    let arm := shcrLiftLegArmK S (P := .prod .nat (.prod .nat .nat))
      (finTripleToNatE S.N_id S.N_recv S.N_opk .v0) (shcrGenOpkLeg f.M_on)
    Prod.map id (forgetShcrKindActive S b) <$>
        arm.eval (.cons (u, (j, o)) (.cons sK (.cons ((pqKeyIndCodec S).qenc t) .nil))) =
      activePostEval S b sK t ∧
    ∀ vs' ∈ support (arm.eval (.cons (u, (j, o)) (.cons sK (.cons ((pqKeyIndCodec S).qenc t) .nil)))),
      ShcrSimInv S b (bumpPred (keyIndSimPred S) c t) vs'.2 := by
  intro f t arm
  have hOn : isKeyIndOnlineQuery (.inr t) = true := by simp [isKeyIndOnlineQuery, t]
  have hOnInv : BaseOnlineLenInv c (projVal shcrStTy sK.1).1 := hInv.core_inv.online_len
  obtain ⟨hc0, hMle⟩ := online_fuel_bounds S b hOn hOnInv.counts_eq hBound
  let xV : Var [keyIndStateTy, shcrStTy, .prod .nat (.prod .nat .nat)]
      (.prod .nat (.prod .nat .nat)) := .succ (.succ .zero)
  have hSim := shcrOnBaseArm_sim S b c (finTripleToNatE S.N_id S.N_recv S.N_opk .v0)
    (fun g => genOpkB f.M_on g xV)
    (fun g => genOpkB (keyIndLoopBound b) g xV)
    (shcrGenOpkLeg_unsup f.M_on) (u, (j, o)) sK t (u.val, (j.val, o.val)) rfl hOn hInv
    (by
      rw [genOpkB_min_eq .zero xV _
        (Nat.le_trans hOnInv.opks_le (Nat.le_of_succ_le hc0)) hMle]
      refine genOpkB_eval_congr (keyIndLoopBound b) _ _ _ _ _ _ ?_ ?_ <;> rfl)
    (genOpkB_pres S f.M_on hOn .zero xV _ hOnInv)
  refine ⟨hSim.1.trans ?_, hSim.2⟩
  dsimp only [activePostEval]
  apply congrArg (embedVal SCS <$> ·)
  simp only [shcr1KeyActivePostC, shcrActivePostTailC,
    _root_.SignalPqxdh.LegacyCosted.keyIndCodec,
    _root_.SignalPqxdh.LegacyCosted.keyIndQenc, caseSumV, onBase, letV, bindV,
    Comp.eval, Expr.eval, pure_bind, Env.get, v, Ext.wk]
  exact congrArg₂ Bind.bind
    (by refine genOpkB_eval_congr (keyIndLoopBound b) _ _ _ _ _ _ ?_ ?_ <;> rfl) rfl

theorem shcrRoArmK_sim (S : Setup) (b : QueryBudget) (c : Fin 3 → ℕ)
    (sK : shcrKindStTy.denote) (sec : (PB (ℓ := 0) (Pt := Empty) 192).denote)
    (hInv : ShcrSimInv S b c sK)
    (hBound : ∀ k, bumpPred (keyIndSimPred S) c (.roQuery sec) k ≤ keyIndSimBounds b k) :
    let f := keyIndCoreFuels S b
    let t : KeyIndQuery S := .roQuery sec
    let arm := shcrRoArmK S f.roCap
    Prod.map id (forgetShcrKindActive S b) <$>
        arm.eval (.cons sec (.cons sK (.cons ((pqKeyIndCodec S).qenc t) .nil))) =
      activePostEval S b sK t ∧
    ∀ vs' ∈ support (arm.eval (.cons sec (.cons sK (.cons ((pqKeyIndCodec S).qenc t) .nil)))),
      ShcrSimInv S b (bumpPred (keyIndSimPred S) c t) vs'.2 := by
  intro f t arm
  obtain ⟨hb0, hb1, hb2⟩ := bumpPred_ro S c sec
  have hc : ∀ k, c k ≤ keyIndSimBounds b k := by
    intro ⟨k, hk⟩
    match k with
    | 0 => change c 0 ≤ keyIndSimBounds b 0; have := hBound 0; omega
    | 1 => change c 1 ≤ keyIndSimBounds b 1; have := hBound 1; omega
    | 2 => change c 2 ≤ keyIndSimBounds b 2; have := hBound 2; omega
  rcases hsL : projVal shcrStTy sK.1 with ⟨bSt, tb, tpk, tsk, cnt, ir, rr, sidx, ch⟩
  have hBSt : projVal keyIndStateTy sK.1.1 = bSt := congrArg Prod.fst hsL
  have hOnInv : BaseOnlineLenInv c bSt := by simpa only [hBSt] using hInv.core_inv.online_len
  let env : Env [PB 192, shcrKindStTy, (pqKeyIndCodec S).Q] :=
    .cons sec (.cons sK (.cons ((pqKeyIndCodec S).qenc t) .nil))
  have hRoEval : (shcrRoListAtomicE (.fst .v1)).eval env = embedVal roListLegacyTy (stRoList bSt) := by
    rw [shcrRoListAtomicE_eval]
    simp only [env, Expr.eval, Expr.v1, Env.get, hsL]
  have hAvl : RoCacheAvlInv (keyIndLoopBound b) f.roCap
      ((shcrRoListAtomicE (.fst .v1)).eval env)
      ((Expr.snd (O := pqAtomicOps) Expr.v1).eval env) := by
    rw [hRoEval]
    simpa only [env, Expr.eval, Expr.v1, Env.get, hBSt] using hInv.core_inv.ro_avl
  have hRoLen : ((shcrRoListAtomicE (.fst .v1)).eval env).length ≤ c 2 := by
    rw [hRoEval, embedVal_roList_eq]
    simpa only [hBSt] using hInv.core_inv.ro_len
  obtain ⟨hLtK, hRoom⟩ := ro_bounds_of_le S b hc hOnInv.counts_eq hRoLen
  obtain ⟨hShadowSim, hShadowPres⟩ :=
    roShadowQueryC_eval_sim tlPrimKeyInd env (keyIndLoopBound b) f.roCap
      (shcrRoListAtomicE (.fst .v1)) (.snd .v1) .v0 bSt
      (hkdfOrRoC_unsup (keyIndLoopBound b)) hRoEval hAvl hLtK hRoom
  have hArmEval : arm.eval env =
      (fun out =>
        let dk := projVal _root_.SignalPqxdh.LegacyCosted.drKeyT out.1
        let ro' := projVal roListLegacyTy out.2.1
        let bSt' : keyIndStateTy.denote :=
          (bSt.1, bSt.2.1, bSt.2.2.1, bSt.2.2.2.1, bSt.2.2.2.2.1, bSt.2.2.2.2.2.1,
           bSt.2.2.2.2.2.2.1, bSt.2.2.2.2.2.2.2.1, bSt.2.2.2.2.2.2.2.2.1, ro',
           bSt.2.2.2.2.2.2.2.2.2.2)
        let sNew : shcrStTy.denote := (bSt', tb, tpk, tsk, cnt, ir, rr, sidx, ch)
        (embedVal _root_.SignalPqxdh.LegacyCosted.keyIndRT
          ((rDrKey (.var .zero : Expr pqxdhOps [_] _)).eval (.cons dk .nil)),
         (embedVal shcrStTy sNew, out.2.2))) <$>
      (roShadowQueryC tlPrimKeyInd f.roCap (shcrRoListAtomicE (.fst .v1)) (.snd .v1) .v0).eval env := by
    simp only [arm, shcrRoArmK, Comp.eval, map_eq_bind_pure_comp, Function.comp_def]
    refine bind_congr fun out => ?_
    rw [runAt3_eval]
    have hEnv3 : Env.cons ((Expr.fst Expr.v0 : Expr pqAtomicOps _ _).eval (.cons out env))
        (.cons ((Expr.fst (Expr.snd Expr.v0) : Expr pqAtomicOps _ _).eval (.cons out env))
          (.cons ((Expr.fst Expr.v2 : Expr pqAtomicOps _ _).eval (.cons out env)) .nil)) =
        embedEnv (.cons (projVal _root_.SignalPqxdh.LegacyCosted.drKeyT out.1)
          (.cons (projVal roListLegacyTy out.2.1) (.cons (projVal shcrStTy sK.1) .nil))) := by
      simp only [env, Expr.eval, Expr.v0, Expr.v2, Env.get, embedEnv, embedVal_projVal]
    rw [hEnv3, mapComp_eval tlPrimKeyInd shcrSetRoRespC shcrSetRoRespC_unsup]
    simp only [hsL, shcrSetRoRespC, Comp.eval, map_pure, pure_bind,
      scBase, scUpd, scTB, scTPk, scTSk, scCnt, scIR, scRR, scSIdx, scChosen,
      stUpd, _root_.SignalPqxdh.Security.ReductionDsl.KeyInd.stMk,
      stSecb, stPrin, stSpks, stOpks, stSess, stResps, stUsedO, stUsedN, stKyb, stAdv,
      rDrKey, Expr.eval, Expr.v0, Expr.v1, v_zero_eval, Env.get]
    rfl
  refine ⟨?_, ?_⟩
  · change Prod.map id (forgetShcrKindActive S b) <$> arm.eval env = activePostEval S b sK t
    have hStep1 :
        Prod.map id (forgetShcrKindActive S b) <$> arm.eval env =
        (fun p : (embedTy _root_.SignalPqxdh.LegacyCosted.drKeyT).denote × roListLegacyTy.denote =>
          let dk := projVal _root_.SignalPqxdh.LegacyCosted.drKeyT p.1
          let ro' := projVal roListLegacyTy p.2
          let bSt' : keyIndStateTy.denote :=
            (bSt.1, bSt.2.1, bSt.2.2.1, bSt.2.2.2.1, bSt.2.2.2.2.1, bSt.2.2.2.2.2.1,
             bSt.2.2.2.2.2.2.1, bSt.2.2.2.2.2.2.2.1, bSt.2.2.2.2.2.2.2.2.1, ro',
             bSt.2.2.2.2.2.2.2.2.2.2)
          let sNew' : shcrStTy.denote := (bSt', tb, tpk, tsk, cnt, ir, rr, fixSent S b sidx, ch)
          embedVal SCS
            (((rDrKey (.var .zero : Expr pqxdhOps [_] _)).eval (.cons dk .nil)), sNew')) <$>
        (Prod.map id Prod.fst <$>
          (roShadowQueryC tlPrimKeyInd f.roCap (shcrRoListAtomicE (.fst .v1)) (.snd .v1) .v0).eval env) := by
      rw [hArmEval, Functor.map_map, Functor.map_map]
      congr 1
    rw [hStep1, hShadowSim]
    have hSecEval : (Expr.v0 : Expr pqAtomicOps _ _).eval env = sec := rfl
    rw [hSecEval]
    have hEnv2 : Env.cons (embedVal keyIndStateTy bSt) (.cons sec .nil) =
        embedEnv (.cons bSt (.cons (projVal (_root_.SignalPqxdh.LegacyCosted.B 192) sec) .nil)) := by
      simp only [embedEnv, embedVal_projVal]
    rw [hEnv2, mapComp_eval tlPrimKeyInd _ (hkdfOrRoC_unsup (keyIndLoopBound b)), Functor.map_map]
    have hRoB : ∀ {Γ₁ Γ₂ Δ' : List PT} [Ext Γ₁ Δ'] [Ext Γ₂ Δ']
        (st : Var Γ₁ keyIndStateTy) (sc : Var Γ₂ (_root_.SignalPqxdh.LegacyCosted.B 192)),
        roB (Δ := Δ') true (keyIndLoopBound b) st sc =
          (bindV (hkdfOrRoC (keyIndLoopBound b) true st (v (Δ := Δ') sc)) fun r =>
            .ret (rs (rDrKey (.fst (v r))) (stUpd (v st) (ro := .snd (v r))))) :=
      fun _ _ => rfl
    dsimp only [t]
    simp only [activePostEval, hsL, shcr1KeyActivePostC, shcrActivePostTailC,
      _root_.SignalPqxdh.LegacyCosted.keyIndCodec,
      _root_.SignalPqxdh.LegacyCosted.keyIndQenc, caseSumV, onBase, hRoB, letV, bindV,
      Comp.eval, pure_bind, rs, rDrKey, fixShcrLegacySent, Expr.eval,
      v, ext_step_wk, ext_refl_wk, env_get_succ, env_get_zero]
    (conv_rhs => rw [hkdfOrRoC_eval_congr (keyIndLoopBound b) .zero _ _])
    have hMapBindPure2 : ∀ {α β₁ β₂ γ : Type} (g : β₂ → γ)
        (m : OracleComp _root_.SignalPqxdh.PrimBaseSpec α) (h₁ : α → β₁) (h₂ : β₁ → β₂),
        g <$> ((m >>= fun r => pure (h₁ r)) >>= fun x => pure (h₂ x)) =
          (fun r => g (h₂ (h₁ r))) <$> m := by
      intro α β₁ β₂ γ g m h₁ h₂
      rw [bind_assoc]
      simp only [pure_bind]
      rw [map_eq_bind_pure_comp, bind_assoc]
      simp only [pure_bind, Function.comp_def]
      rw [map_eq_bind_pure_comp]
      rfl
    rw [hMapBindPure2]
    refine congrArg₂ Functor.map (funext fun r => ?_) rfl
    rcases r with ⟨dkR, roR⟩
    have hProjR : projVal (.prod _root_.SignalPqxdh.LegacyCosted.drKeyT roListLegacyTy)
        (embedVal (.prod _root_.SignalPqxdh.LegacyCosted.drKeyT roListLegacyTy) (dkR, roR)) =
          (dkR, roR) :=
      projVal_embedVal (.prod _root_.SignalPqxdh.LegacyCosted.drKeyT roListLegacyTy) (dkR, roR)
    have hP1 : projVal _root_.SignalPqxdh.LegacyCosted.drKeyT
        (embedVal (.prod _root_.SignalPqxdh.LegacyCosted.drKeyT roListLegacyTy) (dkR, roR)).1 =
          dkR :=
      congrArg
        (fun q : _root_.SignalPqxdh.LegacyCosted.drKeyT.denote × roListLegacyTy.denote => q.1)
        hProjR
    have hP2 : projVal roListLegacyTy
        (embedVal (.prod _root_.SignalPqxdh.LegacyCosted.drKeyT roListLegacyTy) (dkR, roR)).2 =
          roR :=
      congrArg
        (fun q : _root_.SignalPqxdh.LegacyCosted.drKeyT.denote × roListLegacyTy.denote => q.2)
        hProjR
    rw [hP1, hP2]
  · intro vs' hvs'
    change vs' ∈ support (arm.eval env) at hvs'
    rw [hArmEval, map_eq_bind_pure_comp, mem_support_bind_iff] at hvs'
    rcases hvs' with ⟨out, hout, hvsEq⟩
    simp only [Function.comp_def, mem_support_pure_iff] at hvsEq
    subst hvsEq
    obtain ⟨hAvl', hLen'⟩ := hShadowPres out hout
    let ro' := projVal roListLegacyTy out.2.1
    let bSt' : keyIndStateTy.denote :=
      (bSt.1, bSt.2.1, bSt.2.2.1, bSt.2.2.2.1, bSt.2.2.2.2.1, bSt.2.2.2.2.2.1,
       bSt.2.2.2.2.2.2.1, bSt.2.2.2.2.2.2.2.1, bSt.2.2.2.2.2.2.2.2.1, ro',
       bSt.2.2.2.2.2.2.2.2.2.2)
    let sNew : shcrStTy.denote := (bSt', tb, tpk, tsk, cnt, ir, rr, sidx, ch)
    have hProjS' : projVal shcrStTy (embedVal shcrStTy sNew) = sNew := projVal_embedVal shcrStTy sNew
    have hProjB' : projVal keyIndStateTy (embedVal shcrStTy sNew).1 = bSt' :=
      projVal_embedVal keyIndStateTy bSt'
    have hEmbedRo' : embedVal roListLegacyTy (stRoList bSt') = out.2.1 :=
      embedVal_projVal roListLegacyTy out.2.1
    change ShcrSimInv S b (bumpPred (keyIndSimPred S) c t) (embedVal shcrStTy sNew, out.2.2)
    refine ⟨⟨?_, ?_, ?_⟩, ?_, ?_, ?_⟩
    · simp only [hProjB', t]
      exact {
        prin_le   := by rw [hb0]; exact hOnInv.prin_le
        spks_le   := by rw [hb0]; exact hOnInv.spks_le
        opks_le   := by rw [hb0]; exact hOnInv.opks_le
        sess_le   := by rw [hb0]; exact hOnInv.sess_le
        resps_le  := by rw [hb0]; exact hOnInv.resps_le
        usedO_le  := by rw [hb0]; exact hOnInv.usedO_le
        usedN_le  := by rw [hb0]; exact hOnInv.usedN_le
        kyb_le    := by rw [hb0]; exact hOnInv.kyb_le
        adv_le    := by rw [hb0]; exact hOnInv.adv_le
        counts_eq := by rw [hb0, hb1, hb2]; have := hOnInv.counts_eq; omega
      }
    · simp only [hProjB', t, hb2]
      have hLenEq : (stRoList bSt').length = out.2.1.length := by
        rw [← embedVal_roList_eq (stRoList bSt'), hEmbedRo']
      omega
    · simpa only [hProjB', hEmbedRo'] using hAvl'
    · simp only [hProjS', sNew, t, hb0]
      simpa only [hsL] using hInv.cnt_le
    · simp only [hProjS', sNew, t, hb0]
      simpa only [hsL] using hInv.ir_le
    · simp only [hProjS', sNew, t, hb0]
      simpa only [hsL] using hInv.rr_le

theorem shcrRevDhArm_sim (S : Setup) (b : QueryBudget) (c : Fin 3 → ℕ)
    (sK : shcrKindStTy.denote)
    (hInv : ShcrSimInv S b c sK)
    (hBound : ∀ k, bumpPred (keyIndSimPred S) c .revealDhSecrets k ≤ keyIndSimBounds b k) :
    let f := keyIndCoreFuels S b
    let t : KeyIndQuery S := .revealDhSecrets
    let arm := shcrLiftLegArmK S (P := .unit) .unit (shcrRevDhLeg f.M_on)
    let u0 : (Ty.unit : Ty pqAtomicSig).denote := ()
    Prod.map id (forgetShcrKindActive S b) <$>
        arm.eval (.cons u0 (.cons sK (.cons ((pqKeyIndCodec S).qenc t) .nil))) =
      activePostEval S b sK t ∧
    ∀ vs' ∈ support (arm.eval (.cons u0 (.cons sK (.cons ((pqKeyIndCodec S).qenc t) .nil)))),
      ShcrSimInv S b (bumpPred (keyIndSimPred S) c t) vs'.2 := by
  intro f t arm u0
  let _ := hBound
  have hOn : isKeyIndOnlineQuery (.inr t) = true := by simp [isKeyIndOnlineQuery, t]
  have hOnInv : BaseOnlineLenInv c (projVal shcrStTy sK.1).1 := hInv.core_inv.online_len
  have hSim := shcrOnBaseArm_sim S b c .unit
    (fun g => revealDhB true f.M_on g)
    (fun g => revealDhB true (keyIndLoopBound b) g)
    (shcrRevDhLeg_unsup f.M_on) u0 sK t () rfl hOn hInv
    rfl
    (by
      intro r hr
      simp only [revealDhB, ↓reduceIte, rs, rNone, Comp.eval, Expr.eval,
        mem_support_pure_iff, v_zero_eval] at hr
      subst hr
      exact ⟨BaseOnlineLenInv.mono_online hOn hOnInv, rfl⟩)
  refine ⟨hSim.1.trans ?_, hSim.2⟩
  congr 1

private theorem registerB_eval_congr
    {Γ₁ Γ₂ Δ : List PT} (st : Var Γ₁ keyIndStateTy)
    (sk : Var Γ₂ (_root_.SignalPqxdh.LegacyCosted.B 32))
    [Ext Γ₁ Δ] [Ext Γ₂ Δ] (env : Env Δ)
    {Γ₁' Γ₂' Δ' : List PT} (st' : Var Γ₁' keyIndStateTy)
    (sk' : Var Γ₂' (_root_.SignalPqxdh.LegacyCosted.B 32))
    [Ext Γ₁' Δ'] [Ext Γ₂' Δ'] (env' : Env Δ')
    (hst : (v st).eval env = (v st').eval env')
    (hsk : (v sk).eval env = (v sk').eval env') :
    (registerB st sk).eval env = (registerB st' sk').eval env' := by
  simp only [registerB, bindV, Comp.eval]
  have hCond : (Expr.not (natEq (lenB (v sk)) (.nat 32))).eval env =
      (Expr.not (natEq (lenB (v sk')) (.nat 32))).eval env' :=
    congrArg (fun x =>
      (Expr.not (natEq (lenB (Γ := [_root_.SignalPqxdh.LegacyCosted.B 32]) (.var .zero))
        (.nat 32))).eval (.cons (t := _root_.SignalPqxdh.LegacyCosted.B 32) x .nil)) hsk
  rw [hCond]; split_ifs
  · exact congrArg (fun b =>
      (Comp.ret (I := _root_.SignalPqxdh.LegacyCosted.pqPrimIface)
        (rs (Γ := [keyIndStateTy]) rNone (.var .zero))).eval (.cons b .nil)) hst
  · refine congrArg₂ Bind.bind
      (congrArg (fun x =>
        (qX25519Base (Γ := [_root_.SignalPqxdh.LegacyCosted.B 32]) (.var .zero)).eval
          (.cons (t := _root_.SignalPqxdh.LegacyCosted.B 32) x .nil)) hsk)
      (funext fun pk => ?_)
    refine congrArg₂ Bind.bind rfl (funext fun p8 => ?_)
    apply congrArg pure
    dsimp only [v, Expr.eval] at hst
    exact congrArg (fun b : keyIndStateTy.denote => ((Sum.inr (Sum.inr (Sum.inl pk)),
      b.1, b.2.1, b.2.2.1, b.2.2.2.1, b.2.2.2.2.1, b.2.2.2.2.2.1, b.2.2.2.2.2.2.1,
      b.2.2.2.2.2.2.2.1, b.2.2.2.2.2.2.2.2.1, b.2.2.2.2.2.2.2.2.2.1,
      (p8, pk) :: b.2.2.2.2.2.2.2.2.2.2) :
      _root_.SignalPqxdh.Security.ReductionDsl.KeyInd.RS.denote)) hst

private theorem registerB_pres (S : Setup) {c : Fin 3 → ℕ}
    {t : KeyIndQuery S} (hOn : isKeyIndOnlineQuery (.inr t) = true)
    {Γ₁ Γ₂ Δ : List PT} (st : Var Γ₁ keyIndStateTy)
    (sk : Var Γ₂ (_root_.SignalPqxdh.LegacyCosted.B 32))
    [Ext Γ₁ Δ] [Ext Γ₂ Δ] (env : Env Δ)
    (hb : BaseOnlineLenInv c ((v st).eval env)) :
    ∀ r ∈ support ((registerB st sk).eval env),
      BaseOnlineLenInv (bumpPred (keyIndSimPred S) c t) r.2 ∧
      stRoList r.2 = stRoList ((v st).eval env) := by
  obtain ⟨h0, h1, h2⟩ := bumpPred_online S c hOn
  have hSum' : bumpPred (keyIndSimPred S) c t 0 + bumpPred (keyIndSimPred S) c t 1 =
      bumpPred (keyIndSimPred S) c t 2 := by have := hb.counts_eq; omega
  have hle : c 0 ≤ bumpPred (keyIndSimPred S) c t 0 := by omega
  intro r hr
  simp only [registerB, bindV, Comp.eval] at hr
  split_ifs at hr
  · simp only [rs, mem_support_pure_iff, Expr.eval] at hr
    subst hr
    exact ⟨BaseOnlineLenInv.mono_online hOn hb, rfl⟩
  · simp only [mem_support_bind_iff, mem_support_pure_iff] at hr
    rcases hr with ⟨pk, _, p8, _, rfl⟩
    simp only [rs, stUpd, _root_.SignalPqxdh.Security.ReductionDsl.KeyInd.stMk,
      stSecb, stPrin, stSpks, stOpks, stSess, stResps, stUsedO, stUsedN, stKyb, stRo, stAdv,
      Expr.eval, v_eval_cons, v_zero_eval]
    exact baseTuple_preserves_online_ro ((v st).eval env) _ _ _ _ hb hle hSum'
      (Nat.le_trans hb.prin_le hle)
      (Nat.le_trans hb.spks_le hle)
      (Nat.le_trans hb.opks_le hle)
      (by simp only [List.length_cons]; have h := hb.adv_le; simp only [stAdvList] at h; omega)

theorem shcrRegKeyArm_sim (S : Setup) (b : QueryBudget) (c : Fin 3 → ℕ)
    (sK : shcrKindStTy.denote) (sk : (PB (ℓ := 0) (Pt := Empty) 32).denote)
    (hInv : ShcrSimInv S b c sK)
    (hBound : ∀ k, bumpPred (keyIndSimPred S) c (.registerKey sk) k ≤ keyIndSimBounds b k) :
    let t : KeyIndQuery S := .registerKey sk
    let arm := shcrLiftLegArmK S (P := _root_.SignalPqxdh.LegacyCosted.B 32) .v0 shcrRegKeyLeg
    Prod.map id (forgetShcrKindActive S b) <$>
        arm.eval (.cons sk (.cons sK (.cons ((pqKeyIndCodec S).qenc t) .nil))) =
      activePostEval S b sK t ∧
    ∀ vs' ∈ support (arm.eval (.cons sk (.cons sK (.cons ((pqKeyIndCodec S).qenc t) .nil)))),
      ShcrSimInv S b (bumpPred (keyIndSimPred S) c t) vs'.2 := by
  intro t arm
  let _ := hBound
  have hOn : isKeyIndOnlineQuery (.inr t) = true := by simp [isKeyIndOnlineQuery, t]
  have hOnInv : BaseOnlineLenInv c (projVal shcrStTy sK.1).1 := hInv.core_inv.online_len
  let xV : Var [keyIndStateTy, shcrStTy, _root_.SignalPqxdh.LegacyCosted.B 32]
      (_root_.SignalPqxdh.LegacyCosted.B 32) := .succ (.succ .zero)
  have hSim := shcrOnBaseArm_sim S b c .v0
    (fun g => registerB g xV)
    (fun g => registerB g xV)
    shcrRegKeyLeg_unsup sk sK t sk rfl hOn hInv
    (by refine registerB_eval_congr _ _ _ _ _ _ ?_ ?_ <;> rfl)
    (registerB_pres S hOn .zero xV _ hOnInv)
  refine ⟨hSim.1.trans ?_, hSim.2⟩
  dsimp only [activePostEval]
  apply congrArg (embedVal SCS <$> ·)
  simp only [shcr1KeyActivePostC, shcrActivePostTailC,
    _root_.SignalPqxdh.LegacyCosted.keyIndCodec,
    _root_.SignalPqxdh.LegacyCosted.keyIndQenc, caseSumV, onBase, letV, bindV,
    Comp.eval, Expr.eval, pure_bind, Env.get, v, Ext.wk]
  exact congrArg₂ Bind.bind
    (by refine registerB_eval_congr _ _ _ _ _ _ ?_ ?_ <;> rfl) rfl

private theorem revealSpkB_eval_congr (K : ℕ)
    {Γ₁ Γ₂ Δ : List PT} (st : Var Γ₁ keyIndStateTy)
    (x : Var Γ₂ (.prod .nat .nat))
    [Ext Γ₁ Δ] [Ext Γ₂ Δ] (env : Env Δ)
    {Γ₁' Γ₂' Δ' : List PT} (st' : Var Γ₁' keyIndStateTy)
    (x' : Var Γ₂' (.prod .nat .nat))
    [Ext Γ₁' Δ'] [Ext Γ₂' Δ'] (env' : Env Δ')
    (hst : (v st).eval env = (v st').eval env')
    (hx : (v x).eval env = (v x').eval env') :
    (revealSpkB K st x).eval env = (revealSpkB K st' x').eval env' := by
  have hFind : (eFind K (stSpks (v st)) fun e => nat2Eq (.fst (v e)) (v x)).eval env =
      (eFind K (stSpks (v st')) fun e => nat2Eq (.fst (v e)) (v x')).eval env' := by
    simp only [eFind, stSpks, nat2Eq, natEq, Expr.eval, v_eval_cons, v_zero_eval, hst, hx]
    rfl
  simp only [revealSpkB, caseOptV, Comp.eval, hFind]
  cases (eFind K (stSpks (v st')) fun e => nat2Eq (.fst (v e)) (v x')).eval env' with
  | none =>
    simp only [rs, rNone, Expr.eval, hst]
  | some bE =>
    simp only [rs, rSpkSk, sbSpkSk, sbSpkPk, sbPqspkSk, sbPqspkPk,
      _root_.SignalPqxdh.Security.ReductionDsl.KeyInd.sbUpd,
      _root_.SignalPqxdh.Security.ReductionDsl.KeyInd.sbSpkSig,
      _root_.SignalPqxdh.Security.ReductionDsl.KeyInd.sbPqspkSig,
      sbMk, stUpd, _root_.SignalPqxdh.Security.ReductionDsl.KeyInd.stMk,
      stSecb, stPrin, stSpks, stOpks, stSess, stResps, stUsedO, stUsedN, stKyb, stRo, stAdv,
      eMap, nat2Eq, natEq, Expr.eval, v_eval_cons, v_zero_eval, hst, hx]
    rfl

private theorem revealSpkB_pres (S : Setup) (K : ℕ) {c : Fin 3 → ℕ}
    {t : KeyIndQuery S} (hOn : isKeyIndOnlineQuery (.inr t) = true)
    {Γ₁ Γ₂ Δ : List PT} (st : Var Γ₁ keyIndStateTy)
    (x : Var Γ₂ (.prod .nat .nat))
    [Ext Γ₁ Δ] [Ext Γ₂ Δ] (env : Env Δ)
    (hb : BaseOnlineLenInv c ((v st).eval env)) :
    ∀ r ∈ support ((revealSpkB K st x).eval env),
      BaseOnlineLenInv (bumpPred (keyIndSimPred S) c t) r.2 ∧
      stRoList r.2 = stRoList ((v st).eval env) := by
  obtain ⟨h0, h1, h2⟩ := bumpPred_online S c hOn
  have hSum' : bumpPred (keyIndSimPred S) c t 0 + bumpPred (keyIndSimPred S) c t 1 =
      bumpPred (keyIndSimPred S) c t 2 := by have := hb.counts_eq; omega
  have hle : c 0 ≤ bumpPred (keyIndSimPred S) c t 0 := by omega
  intro r hr
  simp only [revealSpkB, caseOptV, Comp.eval] at hr
  split at hr
  · simp only [rs, mem_support_pure_iff, Expr.eval] at hr
    subst hr
    exact ⟨BaseOnlineLenInv.mono_online hOn hb, rfl⟩
  · simp only [mem_support_pure_iff] at hr
    subst hr
    simp only [rs, stUpd, _root_.SignalPqxdh.Security.ReductionDsl.KeyInd.stMk,
      stSecb, stPrin, stSpks, stOpks, stSess, stResps, stUsedO, stUsedN, stKyb, stRo, stAdv,
      eMap, Expr.eval, v_eval_cons, v_zero_eval]
    refine baseTuple_preserves_online_ro ((v st).eval env) _ _ _ _ hb hle hSum'
      (Nat.le_trans hb.prin_le hle) ?_ (Nat.le_trans hb.opks_le hle) (Nat.le_trans hb.adv_le hle)
    simp only [List.length_map, List.length_take]
    exact Nat.le_trans (Nat.min_le_right _ _) (Nat.le_trans hb.spks_le hle)

theorem shcrRevSpkArm_sim (S : Setup) (b : QueryBudget) (c : Fin 3 → ℕ)
    (sK : shcrKindStTy.denote) (u : Fin S.N_id) (j : Fin S.N_recv)
    (hInv : ShcrSimInv S b c sK)
    (hBound : ∀ k, bumpPred (keyIndSimPred S) c (.revealSpkSk u j) k ≤ keyIndSimBounds b k) :
    let f := keyIndCoreFuels S b
    let t : KeyIndQuery S := .revealSpkSk u j
    let arm := shcrLiftLegArmK S (P := .prod .nat .nat)
      (finPairToNatE S.N_id S.N_recv .v0) (shcrRevSpkLeg f.M_on)
    Prod.map id (forgetShcrKindActive S b) <$>
        arm.eval (.cons (u, j) (.cons sK (.cons ((pqKeyIndCodec S).qenc t) .nil))) =
      activePostEval S b sK t ∧
    ∀ vs' ∈ support (arm.eval (.cons (u, j) (.cons sK (.cons ((pqKeyIndCodec S).qenc t) .nil)))),
      ShcrSimInv S b (bumpPred (keyIndSimPred S) c t) vs'.2 := by
  intro f t arm
  have hOn : isKeyIndOnlineQuery (.inr t) = true := by simp [isKeyIndOnlineQuery, t]
  have hOnInv : BaseOnlineLenInv c (projVal shcrStTy sK.1).1 := hInv.core_inv.online_len
  obtain ⟨hc0, hMle⟩ := online_fuel_bounds S b hOn hOnInv.counts_eq hBound
  let xV : Var [keyIndStateTy, shcrStTy, .prod .nat .nat] (.prod .nat .nat) := .succ (.succ .zero)
  have hSim := shcrOnBaseArm_sim S b c (finPairToNatE S.N_id S.N_recv .v0)
    (fun g => revealSpkB f.M_on g xV)
    (fun g => revealSpkB (keyIndLoopBound b) g xV)
    (shcrRevSpkLeg_unsup f.M_on) (u, j) sK t (u.val, j.val) rfl hOn hInv
    (by
      rw [revealSpkB_min_eq .zero xV _
        (Nat.le_trans hOnInv.spks_le (Nat.le_of_succ_le hc0)) hMle]
      refine revealSpkB_eval_congr (keyIndLoopBound b) _ _ _ _ _ _ ?_ ?_ <;> rfl)
    (revealSpkB_pres S f.M_on hOn .zero xV _ hOnInv)
  refine ⟨hSim.1.trans ?_, hSim.2⟩
  dsimp only [activePostEval]
  apply congrArg (embedVal SCS <$> ·)
  simp only [shcr1KeyActivePostC, shcrActivePostTailC,
    _root_.SignalPqxdh.LegacyCosted.keyIndCodec,
    _root_.SignalPqxdh.LegacyCosted.keyIndQenc, caseSumV, onBase, letV, bindV,
    Comp.eval, Expr.eval, pure_bind, Env.get, v, Ext.wk]
  exact congrArg₂ Bind.bind
    (by refine revealSpkB_eval_congr (keyIndLoopBound b) _ _ _ _ _ _ ?_ ?_ <;> rfl) rfl

end Computational.Proofs.SignalPqxdh.Security.ReductionDsl.KindSplit.KeyIndCoreKSimArms
