/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Computational.Specifications.Pqxdh.Security.Headline
public import Computational.Specifications.Pqxdh.Security.CostedBudgets
public import Computational.Proofs.ReductionDsl.StepSim -- proof-setup: allow-public-import
public import Computational.Proofs.SignalPqxdh.AtomicLift -- proof-setup: allow-public-import
public import Computational.Proofs.SignalPqxdh.Security.ReductionDsl.KeyIndGapDh -- proof-setup: allow-public-import
public import Computational.Proofs.SignalPqxdh.Delta.KeyInd1KeyActiveProgs -- proof-setup: allow-public-import
public import Computational.Proofs.SignalPqxdh.Delta.KindSplit.KeyInd1KeyKindProgs -- proof-setup: allow-public-import
public import Computational.Proofs.SignalPqxdh.Security.ReductionDsl.KindSplit.KeyIndCoreKSimBase -- proof-setup: allow-public-import
public import Computational.Proofs.SignalPqxdh.Security.ReductionDsl.KindSplit.KeyIndGapDhK -- proof-setup: allow-public-import
public import Computational.Proofs.SignalPqxdh.Security.ReductionDsl.KindSplit.KeyIndGapDhKSimBase -- proof-setup: allow-public-import
import Computational.Proofs.SignalPqxdh.Security.ReductionDsl.SplitRo.AvlRoCacheRefine
import Computational.Proofs.SignalPqxdh.Security.ReductionDsl.AuthHandshake
import Computational.Proofs.SignalPqxdh.Security.ReductionDsl.KeyInd1KeySigEval
import Computational.Proofs.SignalPqxdh.Security.ReductionDsl.KeyInd1KeyGapDh
import Computational.Proofs.SignalPqxdh.Security.ReductionDsl.KeyInd1KeyGapDhEvalEq

/-!
# Shadow-Indexed Session-Arm Simulation for `KeyInd` Gap-DH

Forgetful step-simulation (`KeyIndStepSim`) and `GdhSimInv` preservation for the four online
session query arms (`.initiateOPK`, `.initiateNoOPK`, `.acceptOPK`, `.acceptNoOPK`) across the
shadow-indexed `KeyInd` Gap-DH and 1-key active reductions.
-/

namespace Computational.Proofs.SignalPqxdh.Security.ReductionDsl.KindSplit.KeyIndGapDhKSimSess

set_option autoImplicit false

public section

open OracleSpec OracleComp
open _root_.ReductionDsl (Sig Ty Var Expr Comp Env Iface pqAtomicSig pqAtomicOps pqKeyIndCodec drKeyT findML)
open _root_.SignalPqxdh (Bytes Setup QueryBudget KeyIndQuery F_X25519)
open _root_.SignalPqxdh.Security.FgGapDh (GdhSimSpec)
open _root_.SignalPqxdh.Security.FgGapDh1Key (liftGdhToSign)
open _root_.SignalPqxdh.LegacyCosted (pqSig pqxdhOps pqPrimIface pqGapDhIface pqSigAndDdhIface B U32)
open Computational.Proofs.ReductionDsl.StepSim (bumpPred)
open Computational.Proofs.SignalPqxdh.AtomicLift (
  AtomicIface embedTy embedVal projVal projVal_embedVal embedEnv
  mapComp mapComp_eval tlGapDhKeyInd tlSigDdhKeyInd liftKeyInd1Stage
)
open Computational.Proofs.SignalPqxdh.Delta.KeyInd1KeyActiveProgs (
  sigKeyInd1KeyActiveAtomicProg fgKeyInd1KeyGapDhActiveAtomicProg
)
open Computational.Proofs.SignalPqxdh.Delta.KindSplit.KeyInd1KeyKindProgs (
  sig1KeyKindHandleC gdh1KeyKindHandleC
)
open Computational.Proofs.SignalPqxdh.Security.ReductionDsl.SplitRo.AvlRoCacheRefine (
  TaggedEntry roEntriesOf roEntriesOf_cons_sess ShadowRelB192
)
open Computational.Proofs.SignalPqxdh.Security.ReductionDsl.KindSplit.KeyIndCoreKSimBase (
  keyIndSimPred keyIndSimBounds keyIndSimPred_zero_iff_kind bumpPred_keyIndSimPred_sum
  fixSent beq_fixSent_of_le_mOn
  stPrinList stSpksList stOpksList stSessList stRespsList stUsedOList stUsedNList stKybList stAdvList
  BaseOnlineLenInv take_min_eq_of_length_le
  findHonestC_min_eq isGameSpkC_min_eq isGameOpkC_min_eq resolveSigPkC_min_eq
  honestPeerC_min_eq checkProvC_min_eq kyberCheckE_min_eq
)
open Computational.Proofs.SignalPqxdh.Security.ReductionDsl.KindSplit.KeyIndGapDhK (
  KeyIndKFuels keyIndKFuelsOfBudget
  seqFgEntryTy fgSessCtrTy fgListAndShadowTy fgPatchShadowC
  fgShadowAtomicTy simShadowAtomicTy
  gdhShadowStateAtomicTy forgetGdhShadow forgetGdhShadow2
  initiateGdhShadowB initiateGdh2ShadowB initiateGdhActiveShadowInnerB
  acceptOpkGdhCoreShadowB acceptOpkGdhShadowB acceptOpkGdh2ShadowB acceptNoOpkGdhShadowB
  GdhAtomicLift gdhLift2Key gdhLift1Key liftGdhAtomic liftKind0SessArm wrapSimSessArm
  gdhShadowHandle2Atomic gdhShadowHandleAtomic
)
open _root_.SignalPqxdh.Security.ReductionDsl.KeyInd (
  PT Ext v letV bindV caseOptV caseSumV findMV anyMV eFind eAny eMap eLet eCaseOpt
  letV_eval Ext.refl_wk' Ext.step_wk' Env.get_zero' Env.get_succ'
  drKeyTy fgPosTy fgPatchEntryTy keyIndStateTy simTy paramsTy params2Ty
  principalEntryTy spkBundleEntryTy opkEntryTy preKeyBundleTy
  keyIndSessionEntryTy keyIndRespEntryTy keyIndRespTy initQTy accQTy sessionIdTy
  fePos1 fePos2 fePos3 fePos4 feSs feDk feMk
  stPrin stSpks stOpks stSess stResps stUsedO stUsedN stKyb stAdv stUpd
  smBase smFgL smPows smUpd
  peSecIKA0 peIkAPk peIkSignPk peCorrupted sbSpkSk sbSpkPk sbPqspkSk sbPqspkPk
  oeOpkSk oeOpkPk oeConsumed oeUpd
  buIkB buSpkId buSpkB buSpkSig buOpkB buPqspkId buPqspkB buPqspkSig
  hdIkAPk hdEkAPk hdSpkId hdOpkId hdPqspkId hdKemCt hdMk
  seSid sePeerIk sePeerSpk sePeerOpk sePeerPqspk seHdr seDrRand seMk seUpd
  reRespIk reSpk reOpk rePqspk reHdr reDrRand reMk reUpd
  ddhEqC ddhEqOptC entryMatchesC fgPatchC eqB orE isSomeE natEq nat2Eq nat3Eq
  eqU32 optU32Eq optBytesEq getDBytes u32OfNat lenB litB nonZero32 encEC encKEM
  qPow8 qSigVerify qKemEncaps qKemDecaps qX25519Base qX25519 qIsCanonical sBytes32
  findHonestC isGameSpkC isGameOpkC resolveSigPkC honestPeerC checkProvC partnerC kyberCheckE
  isAdvPowsE koskSenderOkPowsC koskBundleOkPowsC lookupSpkSkC chooseRespRandC chooseInitRandC
  mkSecretPosC computePosC computeOptPosInitC finishAcceptGdhC
  fgKeyIndGapDhProg fgKeyIndGapDh2Prog
  gPrim sDrKey96
)
open Computational.Proofs.SignalPqxdh.Security.ReductionDsl.KindSplit.KeyIndGapDhKSimBase (
  FgEntryA DrKeyA fgEntryDk RoFgEntryWf
  GdhAtomicLiftValid gdhLift2Key_valid gdhLift1Key_valid
  fixParamsSent forgetSig1KeyActiveK forgetGdh1KeyActiveK
  GdhSimInv Gdh2SimInv Sig1KeyActiveSimInv Gdh1KeyActiveSimInv
  KeyIndStepSim
)

private theorem bind_congr' {ι : Type} {spec : OracleSpec ι} {α β : Type}
    {m₁ m₂ : OracleComp spec α} {k₁ k₂ : α → OracleComp spec β}
    (hm : m₁ = m₂) (hk : ∀ a, k₁ a = k₂ a) :
    (m₁ >>= k₁) = (m₂ >>= k₂) := by
  rw [hm]; exact congrArg (_ >>= ·) (funext hk)

private theorem ddhEqC_eval_congr {Γ₁ Γ₂ : List PT}
    (p1₁ p2₁ : Expr pqxdhOps Γ₁ fgPosTy)
    (p1₂ p2₂ : Expr pqxdhOps Γ₂ fgPosTy)
    (env₁ : Env Γ₁) (env₂ : Env Γ₂)
    (hp1 : p1₁.eval env₁ = p1₂.eval env₂)
    (hp2 : p2₁.eval env₁ = p2₂.eval env₂) :
    (ddhEqC p1₁ p2₁).eval env₁ = (ddhEqC p1₂ p2₂).eval env₂ := by
  unfold ddhEqC
  simp only [letV_eval, caseSumV, Comp.eval, Expr.eval, v,
    Env.get_zero', Env.get_succ', Ext.step_wk', Ext.refl_wk', hp1, hp2]
  rcases p1₂.eval env₂ with x1 | y1 <;> rcases p2₂.eval env₂ with x2 | y2 <;> rfl

private theorem ddhEqOptC_eval_congr {Γ₁ Γ₂ : List PT}
    (p1₁ p2₁ : Expr pqxdhOps Γ₁ (.opt fgPosTy))
    (p1₂ p2₂ : Expr pqxdhOps Γ₂ (.opt fgPosTy))
    (env₁ : Env Γ₁) (env₂ : Env Γ₂)
    (hp1 : p1₁.eval env₁ = p1₂.eval env₂)
    (hp2 : p2₁.eval env₁ = p2₂.eval env₂) :
    (ddhEqOptC p1₁ p2₁).eval env₁ = (ddhEqOptC p1₂ p2₂).eval env₂ := by
  unfold ddhEqOptC
  simp only [letV_eval, caseOptV, Comp.eval, Expr.eval, v,
    Env.get_zero', Env.get_succ', Ext.step_wk', Ext.refl_wk', hp1, hp2]
  rcases p1₂.eval env₂ with _ | x1 <;> rcases p2₂.eval env₂ with _ | x2
  · rfl
  · rfl
  · rfl
  · exact ddhEqC_eval_congr _ _ _ _ _ _ rfl rfl

private theorem entryMatchesC_eval_congr
    {Γ₁ Γ₂ Γ₃ Γ₄ Γ₅ Δ₁ Γ₁' Γ₂' Γ₃' Γ₄' Γ₅' Δ₂ : List PT}
    [Ext Γ₁ Δ₁] [Ext Γ₂ Δ₁] [Ext Γ₃ Δ₁] [Ext Γ₄ Δ₁] [Ext Γ₅ Δ₁]
    [Ext Γ₁' Δ₂] [Ext Γ₂' Δ₂] [Ext Γ₃' Δ₂] [Ext Γ₄' Δ₂] [Ext Γ₅' Δ₂]
    (pos1₁ : Var Γ₁ fgPosTy) (pos2₁ : Var Γ₂ fgPosTy) (pos3₁ : Var Γ₃ fgPosTy)
    (pos4₁ : Var Γ₄ (.opt fgPosTy)) (ss₁ : Var Γ₅ (B 32)) (e₁ : Var Δ₁ fgPatchEntryTy)
    (pos1₂ : Var Γ₁' fgPosTy) (pos2₂ : Var Γ₂' fgPosTy) (pos3₂ : Var Γ₃' fgPosTy)
    (pos4₂ : Var Γ₄' (.opt fgPosTy)) (ss₂ : Var Γ₅' (B 32)) (e₂ : Var Δ₂ fgPatchEntryTy)
    (env₁ : Env Δ₁) (env₂ : Env Δ₂)
    (hp1 : env₁.get (Ext.wk pos1₁) = env₂.get (Ext.wk pos1₂))
    (hp2 : env₁.get (Ext.wk pos2₁) = env₂.get (Ext.wk pos2₂))
    (hp3 : env₁.get (Ext.wk pos3₁) = env₂.get (Ext.wk pos3₂))
    (hp4 : env₁.get (Ext.wk pos4₁) = env₂.get (Ext.wk pos4₂))
    (hss : env₁.get (Ext.wk ss₁) = env₂.get (Ext.wk ss₂))
    (he  : env₁.get e₁ = env₂.get e₂) :
    (entryMatchesC pos1₁ pos2₁ pos3₁ pos4₁ ss₁ e₁).eval env₁ =
      (entryMatchesC pos1₂ pos2₂ pos3₂ pos4₂ ss₂ e₂).eval env₂ := by
  unfold entryMatchesC
  have hCond : (Expr.not (eqB (v ss₁) (feSs (v e₁)))).eval env₁ =
      (Expr.not (eqB (v ss₂) (feSs (v e₂)))).eval env₂ := by
    simp only [Expr.eval, v, feSs, eqB, Ext.refl_wk', hss, he]
  simp only [Comp.eval, hCond]
  split_ifs
  · rfl
  · simp only [bindV, Comp.eval]
    refine bind_congr' (ddhEqC_eval_congr _ _ _ _ _ _
      (by simp [v, Expr.eval, hp1]) (by simp [fePos1, v, Expr.eval, Ext.refl_wk', he])) fun b1 => ?_
    refine bind_congr' (ddhEqC_eval_congr _ _ _ _ _ _
      (by simp [v, Expr.eval, Env.get_succ', Ext.step_wk', hp2])
      (by simp [fePos2, v, Expr.eval, Env.get_succ', Ext.step_wk', Ext.refl_wk', he])) fun b2 => ?_
    refine bind_congr' (ddhEqC_eval_congr _ _ _ _ _ _
      (by simp [v, Expr.eval, Env.get_succ', Ext.step_wk', hp3])
      (by simp [fePos3, v, Expr.eval, Env.get_succ', Ext.step_wk', Ext.refl_wk', he])) fun b3 => ?_
    refine bind_congr' (ddhEqOptC_eval_congr _ _ _ _ _ _
      (by simp [v, Expr.eval, Env.get_succ', Ext.step_wk', hp4])
      (by simp [fePos4, v, Expr.eval, Env.get_succ', Ext.step_wk', Ext.refl_wk', he])) fun _ => rfl

/-- Online `fgPatchShadowC` vs `fgPatchC` simulation and `ShadowRelB192` preservation. -/
theorem fgPatchShadowC_sim {S : Setup} {b : QueryBudget}
    {Γ₁ Γ₂ Γ₃ Γ₄ Γ₅ Δ₁ Γ₁' Γ₂' Γ₃' Γ₄' Γ₅' Δ₂ : List PT}
    [Ext Γ₁ Δ₁] [Ext Γ₂ Δ₁] [Ext Γ₃ Δ₁] [Ext Γ₄ Δ₁] [Ext Γ₅ Δ₁]
    [Ext Γ₁' Δ₂] [Ext Γ₂' Δ₂] [Ext Γ₃' Δ₂] [Ext Γ₄' Δ₂] [Ext Γ₅' Δ₂]
    (pos1₁ : Var Γ₁ fgPosTy) (pos2₁ : Var Γ₂ fgPosTy) (pos3₁ : Var Γ₃ fgPosTy)
    (pos4₁ : Var Γ₄ (.opt fgPosTy)) (ss₁ : Var Γ₅ (B 32))
    (fgL₁ : Expr pqxdhOps Δ₁ (.list fgPatchEntryTy))
    (fgSess₁ : Expr pqxdhOps Δ₁ (.list seqFgEntryTy))
    (ctr₁ : Expr pqxdhOps Δ₁ .nat)
    (pos1₂ : Var Γ₁' fgPosTy) (pos2₂ : Var Γ₂' fgPosTy) (pos3₂ : Var Γ₃' fgPosTy)
    (pos4₂ : Var Γ₄' (.opt fgPosTy)) (ss₂ : Var Γ₅' (B 32))
    (fgL₂ : Expr pqxdhOps Δ₂ (.list fgPatchEntryTy))
    (env₁ : Env Δ₁) (env₂ : Env Δ₂)
    (fgRoAvl : _)
    (hp1 : env₁.get (Ext.wk pos1₁) = env₂.get (Ext.wk pos1₂))
    (hp2 : env₁.get (Ext.wk pos2₁) = env₂.get (Ext.wk pos2₂))
    (hp3 : env₁.get (Ext.wk pos3₁) = env₂.get (Ext.wk pos3₂))
    (hp4 : env₁.get (Ext.wk pos4₁) = env₂.get (Ext.wk pos4₂))
    (hss : env₁.get (Ext.wk ss₁) = env₂.get (Ext.wk ss₂))
    (hL  : fgL₁.eval env₁ = fgL₂.eval env₂)
    (hLenK : (fgL₁.eval env₁).length ≤ (keyIndKFuelsOfBudget S b).kFg)
    (hLenQ : (fgL₁.eval env₁).length ≤ b.q_total)
    (hCtrRoom : ctr₁.eval env₁ + 1 ≤ b.q_total)
    {c1 : ℕ}
    (hShadow : ∃ tagged : List (TaggedEntry Bytes FgEntryA),
      ShadowRelB192 (drKeyT (ℓ := 0) (Pt := Empty)) b.q_total (keyIndKFuelsOfBudget S b).kAvl
        fgEntryDk (embedVal (.list fgPatchEntryTy) (fgL₁.eval env₁))
        tagged fgRoAvl (embedVal (.list seqFgEntryTy) (fgSess₁.eval env₁)) (ctr₁.eval env₁) ∧
      (∀ te ∈ tagged, ∀ sec, te.tag = .ro sec → RoFgEntryWf sec te.entry) ∧
      (roEntriesOf fgEntryDk tagged).length ≤ c1) :
    (fun r => (r.1, r.2.1)) <$>
      (fgPatchShadowC (keyIndKFuelsOfBudget S b).kFg
        pos1₁ pos2₁ pos3₁ pos4₁ ss₁ fgL₁ fgSess₁ ctr₁).eval env₁ =
      (fgPatchC b.q_total pos1₂ pos2₂ pos3₂ pos4₂ ss₂ fgL₂).eval env₂ ∧
    ∀ r ∈ support
      ((fgPatchShadowC (keyIndKFuelsOfBudget S b).kFg
        pos1₁ pos2₁ pos3₁ pos4₁ ss₁ fgL₁ fgSess₁ ctr₁).eval env₁),
      (embedVal (.list seqFgEntryTy) r.2.2.1).length ≤
        (embedVal (.list seqFgEntryTy) (fgSess₁.eval env₁)).length + 1 ∧
      ∃ tagged' : List (TaggedEntry Bytes FgEntryA),
        ShadowRelB192 (drKeyT (ℓ := 0) (Pt := Empty)) b.q_total (keyIndKFuelsOfBudget S b).kAvl
          fgEntryDk (embedVal (.list fgPatchEntryTy) r.2.1)
          tagged' fgRoAvl (embedVal (.list seqFgEntryTy) r.2.2.1) r.2.2.2 ∧
        (∀ te ∈ tagged', ∀ sec, te.tag = .ro sec → RoFgEntryWf sec te.entry) ∧
        (roEntriesOf fgEntryDk tagged').length ≤ c1 := by
  obtain ⟨tagged, hRel, hValidRo, hRoLe⟩ := hShadow
  have hTake1 : List.take (keyIndKFuelsOfBudget S b).kFg (fgL₁.eval env₁) = fgL₁.eval env₁ :=
    List.take_of_length_le hLenK
  have hTake2 : List.take b.q_total (fgL₂.eval env₂) = fgL₁.eval env₁ := by
    rw [← hL]; exact List.take_of_length_le hLenQ
  unfold fgPatchShadowC fgPatchC
  simp only [letV_eval, bindV, caseOptV, findMV, Comp.eval, v, Expr.eval,
    Env.get_zero', Env.get_succ', Ext.step_wk', Ext.refl_wk', hTake1, hTake2, map_bind]
  have hFind :
      findML (fun x => (entryMatchesC pos1₁ pos2₁ pos3₁ pos4₁ ss₁ .zero).eval
        (Env.cons (t := fgPatchEntryTy) x
          (Env.cons (t := fgListAndShadowTy) (fgL₁.eval env₁, (fgSess₁.eval env₁, ctr₁.eval env₁))
            env₁)))
        (fgL₁.eval env₁) =
      findML (fun x => (entryMatchesC pos1₂ pos2₂ pos3₂ pos4₂ ss₂ .zero).eval
        (Env.cons (t := fgPatchEntryTy) x
          (Env.cons (t := .list fgPatchEntryTy) (fgL₂.eval env₂) env₂)))
        (fgL₁.eval env₁) := by
    congr 1; funext x
    exact entryMatchesC_eval_congr _ _ _ _ _ _ _ _ _ _ _ _ _ _
      (by simpa [Env.get_succ', Ext.step_wk', Ext.refl_wk'] using hp1)
      (by simpa [Env.get_succ', Ext.step_wk', Ext.refl_wk'] using hp2)
      (by simpa [Env.get_succ', Ext.step_wk', Ext.refl_wk'] using hp3)
      (by simpa [Env.get_succ', Ext.step_wk', Ext.refl_wk'] using hp4)
      (by simpa [Env.get_succ', Ext.step_wk', Ext.refl_wk'] using hss)
      rfl
  constructor
  · rw [hFind]
    congr 1; funext o
    rcases o with _ | e
    · dsimp only [Comp.eval]
      simp only [map_bind, map_pure]
      refine bind_congr' rfl fun dk => ?_
      simp only [feMk, Expr.eval, Env.get_zero', Env.get_succ',
        hp1, hp2, hp3, hp4, hss, hL]
    · simp only [feDk, Expr.eval, Env.get_zero', hL, map_pure]
  · intro r hr
    simp only [mem_support_bind_iff] at hr
    rcases hr with ⟨o, _, hr⟩
    rcases o with _ | e
    · simp only [mem_support_bind_iff, mem_support_pure_iff] at hr
      rcases hr with ⟨dk, _, rfl⟩
      let newE : fgPatchEntryTy.denote :=
        (env₁.get (Ext.wk pos1₁),
          (env₁.get (Ext.wk pos2₁),
            (env₁.get (Ext.wk pos3₁),
              (env₁.get (Ext.wk pos4₁),
                (env₁.get (Ext.wk ss₁), dk)))))
      refine ⟨?_, ⟨⟨ctr₁.eval env₁, .sess, embedVal fgPatchEntryTy newE⟩ :: tagged, ?_, ?_, ?_⟩⟩
      · change (embedVal seqFgEntryTy _ :: embedVal (.list seqFgEntryTy) _).length ≤ _
        simp only [List.length_cons]; omega
      · exact hRel.cons_sess (embedVal fgPatchEntryTy newE) hCtrRoom
      · intro te hMem sec hTag
        rcases List.mem_cons.mp hMem with rfl | hMem'
        · cases hTag
        · exact hValidRo te hMem' sec hTag
      · rw [roEntriesOf_cons_sess]; exact hRoLe
    · simp only [mem_support_pure_iff] at hr
      subst hr
      refine ⟨Nat.le_succ _, ⟨tagged, hRel, hValidRo, hRoLe⟩⟩

private theorem findML_congr {ι : Type} {spec : OracleSpec ι} {α : Type}
    {p₁ p₂ : α → OracleComp spec Bool} (L : List α)
    (hp : ∀ x, p₁ x = p₂ x) :
    findML p₁ L = findML p₂ L := by
  congr 1; exact funext hp

private theorem anyML_congr {ι : Type} {spec : OracleSpec ι} {α : Type}
    {p₁ p₂ : α → OracleComp spec Bool} (L : List α)
    (hp : ∀ x, p₁ x = p₂ x) :
    ReductionDsl.anyML p₁ L = ReductionDsl.anyML p₂ L := by
  congr 1; exact funext hp

private theorem eFind_congr_le {Γ₁ Γ₂ : List PT} {τ : PT} {K₁ K₂ : ℕ}
    (xs₁ : Expr pqxdhOps Γ₁ (.list τ)) (xs₂ : Expr pqxdhOps Γ₂ (.list τ))
    (p₁ : Var (τ :: Γ₁) τ → Expr pqxdhOps (τ :: Γ₁) .bool)
    (p₂ : Var (τ :: Γ₂) τ → Expr pqxdhOps (τ :: Γ₂) .bool)
    (env₁ : Env Γ₁) (env₂ : Env Γ₂)
    (hxs : xs₁.eval env₁ = xs₂.eval env₂)
    (hLen : (xs₁.eval env₁).length ≤ K₁) (hLe : K₁ ≤ K₂)
    (hp : ∀ x, (p₁ .zero).eval (.cons x env₁) = (p₂ .zero).eval (.cons x env₂)) :
    (eFind K₁ xs₁ p₁).eval env₁ = (eFind K₂ xs₂ p₂).eval env₂ := by
  simp only [eFind, Expr.eval, List.take_of_length_le hLen,
    ← hxs, List.take_of_length_le (Nat.le_trans hLen hLe)]
  congr 1; exact funext hp

private theorem eAny_congr_le {Γ₁ Γ₂ : List PT} {τ : PT} {K₁ K₂ : ℕ}
    (xs₁ : Expr pqxdhOps Γ₁ (.list τ)) (xs₂ : Expr pqxdhOps Γ₂ (.list τ))
    (p₁ : Var (τ :: Γ₁) τ → Expr pqxdhOps (τ :: Γ₁) .bool)
    (p₂ : Var (τ :: Γ₂) τ → Expr pqxdhOps (τ :: Γ₂) .bool)
    (env₁ : Env Γ₁) (env₂ : Env Γ₂)
    (hxs : xs₁.eval env₁ = xs₂.eval env₂)
    (hLen : (xs₁.eval env₁).length ≤ K₁) (hLe : K₁ ≤ K₂)
    (hp : ∀ x, (p₁ .zero).eval (.cons x env₁) = (p₂ .zero).eval (.cons x env₂)) :
    (eAny K₁ xs₁ p₁).eval env₁ = (eAny K₂ xs₂ p₂).eval env₂ := by
  simp only [eAny, Expr.eval, List.take_of_length_le hLen,
    ← hxs, List.take_of_length_le (Nat.le_trans hLen hLe)]
  congr 1; exact funext hp

private theorem eMap_congr_le {Γ₁ Γ₂ : List PT} {τ₁ τ₂ : PT} {K₁ K₂ : ℕ}
    (xs₁ : Expr pqxdhOps Γ₁ (.list τ₁)) (xs₂ : Expr pqxdhOps Γ₂ (.list τ₁))
    (f₁ : Var (τ₁ :: Γ₁) τ₁ → Expr pqxdhOps (τ₁ :: Γ₁) τ₂)
    (f₂ : Var (τ₁ :: Γ₂) τ₁ → Expr pqxdhOps (τ₁ :: Γ₂) τ₂)
    (env₁ : Env Γ₁) (env₂ : Env Γ₂)
    (hxs : xs₁.eval env₁ = xs₂.eval env₂)
    (hLen : (xs₁.eval env₁).length ≤ K₁) (hLe : K₁ ≤ K₂)
    (hf : ∀ x, (f₁ .zero).eval (.cons x env₁) = (f₂ .zero).eval (.cons x env₂)) :
    (eMap K₁ xs₁ f₁).eval env₁ = (eMap K₂ xs₂ f₂).eval env₂ := by
  simp only [eMap, Expr.eval, List.take_of_length_le hLen,
    ← hxs, List.take_of_length_le (Nat.le_trans hLen hLe)]
  congr 1; exact funext hf

private theorem findMV_min_congr {ι : Type} {T : OracleSpec ι} {I : Iface pqSig T}
    {Γ₁ Γ₂ : List PT} {τ : PT} {K₁ K₂ N : ℕ}
    (xs₁ : Expr pqxdhOps Γ₁ (.list τ)) (xs₂ : Expr pqxdhOps Γ₂ (.list τ))
    (p₁ : Var (τ :: Γ₁) τ → Comp pqxdhOps I (τ :: Γ₁) .bool)
    (p₂ : Var (τ :: Γ₂) τ → Comp pqxdhOps I (τ :: Γ₂) .bool)
    (env₁ : Env Γ₁) (env₂ : Env Γ₂)
    (hxs : xs₁.eval env₁ = xs₂.eval env₂)
    (hLen : (xs₁.eval env₁).length ≤ K₁) (hLe : K₁ ≤ K₂)
    (hp : ∀ x, (p₁ .zero).eval (.cons x env₁) = (p₂ .zero).eval (.cons x env₂)) :
    (findMV (min K₁ N) xs₁ p₁).eval env₁ = (findMV (min K₂ N) xs₂ p₂).eval env₂ := by
  simp only [findMV, Comp.eval, ← hxs, take_min_eq_of_length_le (xs₁.eval env₁) hLen hLe]
  exact findML_congr _ hp

private theorem anyMV_min_congr {ι : Type} {T : OracleSpec ι} {I : Iface pqSig T}
    {Γ₁ Γ₂ : List PT} {τ : PT} {K₁ K₂ N : ℕ}
    (xs₁ : Expr pqxdhOps Γ₁ (.list τ)) (xs₂ : Expr pqxdhOps Γ₂ (.list τ))
    (p₁ : Var (τ :: Γ₁) τ → Comp pqxdhOps I (τ :: Γ₁) .bool)
    (p₂ : Var (τ :: Γ₂) τ → Comp pqxdhOps I (τ :: Γ₂) .bool)
    (env₁ : Env Γ₁) (env₂ : Env Γ₂)
    (hxs : xs₁.eval env₁ = xs₂.eval env₂)
    (hLen : (xs₁.eval env₁).length ≤ K₁) (hLe : K₁ ≤ K₂)
    (hp : ∀ x, (p₁ .zero).eval (.cons x env₁) = (p₂ .zero).eval (.cons x env₂)) :
    (anyMV (min K₁ N) xs₁ p₁).eval env₁ = (anyMV (min K₂ N) xs₂ p₂).eval env₂ := by
  simp only [anyMV, Comp.eval, ← hxs, take_min_eq_of_length_le (xs₁.eval env₁) hLen hLe]
  exact anyML_congr _ hp

@[local simp] private theorem v_eval_cons {Γ Δ : List PT} {σ τ : PT} [Ext Γ Δ]
    (x : Var Γ τ) (a : σ.denote) (env : Env Δ) :
    (@v Γ (σ :: Δ) τ Ext.step x).eval (.cons a env) = (v x).eval env := rfl

@[local simp] private theorem v_zero_eval {Γ : List PT} {τ : PT} (a : τ.denote) (env : Env Γ) :
    (@v (τ :: Γ) (τ :: Γ) τ Ext.refl .zero).eval (.cons a env) = a := rfl

@[local simp] private theorem env_get_zero {Γ : List PT} {τ : PT}
    (x : τ.denote) (env : Env Γ) :
    (Env.cons x env).get Var.zero = x := rfl

@[local simp] private theorem env_get_succ {Γ : List PT} {τ σ : PT}
    (i : Var Γ τ) (x : σ.denote) (env : Env Γ) :
    (Env.cons x env).get (Var.succ i) = env.get i := rfl

private theorem query_eval_congr {ι : Type} {T : OracleSpec ι} {I : Iface pqSig T}
    {Γ₁ Γ₂ : List PT} {tag : I.Tag}
    {e₁ : Expr pqxdhOps Γ₁ (I.dom tag)} {e₂ : Expr pqxdhOps Γ₂ (I.dom tag)}
    {env₁ : Env Γ₁} {env₂ : Env Γ₂} (h : e₁.eval env₁ = e₂.eval env₂) :
    (Comp.query tag e₁ : Comp pqxdhOps I Γ₁ (I.cod tag)).eval env₁ =
      (Comp.query tag e₂ : Comp pqxdhOps I Γ₂ (I.cod tag)).eval env₂ := by
  simp only [Comp.eval]; rw [h]

private theorem qPow8_eval_congr {Γ₁ Γ₂ : List PT}
    (e₁ : Expr pqxdhOps Γ₁ (B 32)) (e₂ : Expr pqxdhOps Γ₂ (B 32))
    (env₁ : Env Γ₁) (env₂ : Env Γ₂) (h : e₁.eval env₁ = e₂.eval env₂) :
    (qPow8 e₁).eval env₁ = (qPow8 e₂).eval env₂ :=
  query_eval_congr h

private theorem findHonestC_sim (S : Setup) {K₁ K₂ : ℕ} {Γ₁ Δ₁ Γ₂ Δ₂ : List PT}
    [Ext Γ₁ Δ₁] [Ext Γ₂ Δ₂]
    (st₁ : Var Γ₁ keyIndStateTy) (ik₁ : Expr pqxdhOps Δ₁ (B 32))
    (st₂ : Var Γ₂ keyIndStateTy) (ik₂ : Expr pqxdhOps Δ₂ (B 32))
    (env₁ : Env Δ₁) (env₂ : Env Δ₂)
    (hst : (v st₁).eval env₁ = (v st₂).eval env₂)
    (hik : ik₁.eval env₁ = ik₂.eval env₂)
    (hLen : (stPrinList ((v st₁).eval env₁)).length ≤ K₁) (hLe : K₁ ≤ K₂) :
    (findHonestC S K₁ st₁ ik₁).eval env₁ = (findHonestC S K₂ st₂ ik₂).eval env₂ := by
  simp only [findHonestC, letV_eval]
  refine findMV_min_congr _ _ _ _ _ _ ?_ ?_ hLe fun e => ?_
  · simp [Expr.eval, hst]
  · simpa [stPrin, stPrinList, Expr.eval] using hLen
  · refine bind_congr' (qPow8_eval_congr _ _ _ _ (by simp [hik])) fun p1 => ?_
    refine bind_congr' (qPow8_eval_congr _ _ _ _ (by simp [Expr.eval])) fun p2 => ?_
    simp [Comp.eval, eqB, Expr.eval]

private theorem isGameSpkC_sim (S : Setup) {K₁ K₂ : ℕ} {Γ₁ Δ₁ Γ₂ Δ₂ : List PT}
    [Ext Γ₁ Δ₁] [Ext Γ₂ Δ₂]
    (st₁ : Var Γ₁ keyIndStateTy) (pk₁ : Expr pqxdhOps Δ₁ (B 32))
    (st₂ : Var Γ₂ keyIndStateTy) (pk₂ : Expr pqxdhOps Δ₂ (B 32))
    (env₁ : Env Δ₁) (env₂ : Env Δ₂)
    (hst : (v st₁).eval env₁ = (v st₂).eval env₂)
    (hpk : pk₁.eval env₁ = pk₂.eval env₂)
    (hLen : (stSpksList ((v st₁).eval env₁)).length ≤ K₁) (hLe : K₁ ≤ K₂) :
    (isGameSpkC S K₁ st₁ pk₁).eval env₁ = (isGameSpkC S K₂ st₂ pk₂).eval env₂ := by
  simp only [isGameSpkC, letV_eval]
  refine anyMV_min_congr _ _ _ _ _ _ ?_ ?_ hLe fun e => ?_
  · simp [Expr.eval, hst]
  · simpa [stSpks, stSpksList, Expr.eval] using hLen
  · refine bind_congr' (qPow8_eval_congr _ _ _ _ (by simp [Expr.eval])) fun p1 => ?_
    refine bind_congr' (qPow8_eval_congr _ _ _ _ (by simp [hpk])) fun p2 => ?_
    simp [Comp.eval, eqB, Expr.eval]

private theorem isGameOpkC_sim (S : Setup) {K₁ K₂ : ℕ} {Γ₁ Δ₁ Γ₂ Δ₂ : List PT}
    [Ext Γ₁ Δ₁] [Ext Γ₂ Δ₂]
    (st₁ : Var Γ₁ keyIndStateTy) (pk₁ : Expr pqxdhOps Δ₁ (B 32))
    (st₂ : Var Γ₂ keyIndStateTy) (pk₂ : Expr pqxdhOps Δ₂ (B 32))
    (env₁ : Env Δ₁) (env₂ : Env Δ₂)
    (hst : (v st₁).eval env₁ = (v st₂).eval env₂)
    (hpk : pk₁.eval env₁ = pk₂.eval env₂)
    (hLen : (stOpksList ((v st₁).eval env₁)).length ≤ K₁) (hLe : K₁ ≤ K₂) :
    (isGameOpkC S K₁ st₁ pk₁).eval env₁ = (isGameOpkC S K₂ st₂ pk₂).eval env₂ := by
  simp only [isGameOpkC, letV_eval]
  refine anyMV_min_congr _ _ _ _ _ _ ?_ ?_ hLe fun e => ?_
  · simp [Expr.eval, hst]
  · simpa [stOpks, stOpksList, Expr.eval] using hLen
  · refine bind_congr' (qPow8_eval_congr _ _ _ _ (by simp [Expr.eval])) fun p1 => ?_
    refine bind_congr' (qPow8_eval_congr _ _ _ _ (by simp [hpk])) fun p2 => ?_
    simp [Comp.eval, eqB, Expr.eval]

private theorem isAdvPowsE_sim {K₁ K₂ : ℕ} {Γ₁ Γ₂ : List PT}
    (pows₁ : Expr pqxdhOps Γ₁ (.list (.prod (B 32) (B 32)))) (wPk₁ : Expr pqxdhOps Γ₁ (B 32))
    (pows₂ : Expr pqxdhOps Γ₂ (.list (.prod (B 32) (B 32)))) (wPk₂ : Expr pqxdhOps Γ₂ (B 32))
    (env₁ : Env Γ₁) (env₂ : Env Γ₂)
    (hpows : pows₁.eval env₁ = pows₂.eval env₂) (hw : wPk₁.eval env₁ = wPk₂.eval env₂)
    (hLen : (pows₁.eval env₁).length ≤ K₁) (hLe : K₁ ≤ K₂) :
    (isAdvPowsE K₁ pows₁ wPk₁).eval env₁ = (isAdvPowsE K₂ pows₂ wPk₂).eval env₂ := by
  simp only [isAdvPowsE, eLet, Expr.eval]
  refine eAny_congr_le _ _ _ _ _ _
    (by simp [Expr.eval, hpows])
    (by simpa [Expr.eval] using hLen) hLe fun p => ?_
  simp [Expr.eval, hw]

private theorem koskSenderOkPowsC_sim (S : Setup) {K₁ K₂ : ℕ} {Γ₁ Δ₁ Γ₂ Δ₂ : List PT}
    [Ext Γ₁ Δ₁] [Ext Γ₂ Δ₂]
    (st₁ : Var Γ₁ keyIndStateTy) (pows₁ : Expr pqxdhOps Δ₁ (.list (.prod (B 32) (B 32))))
    (ik₁ : Expr pqxdhOps Δ₁ (B 32))
    (st₂ : Var Γ₂ keyIndStateTy) (pows₂ : Expr pqxdhOps Δ₂ (.list (.prod (B 32) (B 32))))
    (ik₂ : Expr pqxdhOps Δ₂ (B 32))
    (env₁ : Env Δ₁) (env₂ : Env Δ₂)
    (hst : (v st₁).eval env₁ = (v st₂).eval env₂)
    (hpows : pows₁.eval env₁ = pows₂.eval env₂) (hik : ik₁.eval env₁ = ik₂.eval env₂)
    (hPrin : (stPrinList ((v st₁).eval env₁)).length ≤ K₁)
    (hPows : (pows₁.eval env₁).length ≤ K₁) (hLe : K₁ ≤ K₂) :
    (koskSenderOkPowsC S K₁ st₁ pows₁ ik₁).eval env₁ =
      (koskSenderOkPowsC S K₂ st₂ pows₂ ik₂).eval env₂ := by
  simp only [koskSenderOkPowsC, letV_eval]
  refine bind_congr' (findHonestC_sim S st₁ _ st₂ _ _ _
    (by simp [hst]) (by simp [Expr.eval, hik])
    (by simpa using hPrin) hLe) fun hp => ?_
  refine bind_congr' (qPow8_eval_congr _ _ _ _ (by simp [Expr.eval, hik])) fun wIk => ?_
  simp only [Comp.eval, orE, isSomeE, Expr.eval, v_eval_cons, v_zero_eval]
  congr 1; congr 1
  exact isAdvPowsE_sim _ _ _ _ _ _
    (by simp [Expr.eval, hpows]) (by simp)
    (by simpa [Expr.eval] using hPows) hLe

private theorem koskBundleOkPowsC_sim (S : Setup) {K₁ K₂ : ℕ}
    {Γ₁ Γ₂ Δ₁ Γ₁' Γ₂' Δ₂ : List PT}
    [Ext Γ₁ Δ₁] [Ext Γ₂ Δ₁] [Ext Γ₁' Δ₂] [Ext Γ₂' Δ₂]
    (st₁ : Var Γ₁ keyIndStateTy) (pows₁ : Expr pqxdhOps Δ₁ (.list (.prod (B 32) (B 32))))
    (bu₁ : Var Γ₂ preKeyBundleTy)
    (st₂ : Var Γ₁' keyIndStateTy) (pows₂ : Expr pqxdhOps Δ₂ (.list (.prod (B 32) (B 32))))
    (bu₂ : Var Γ₂' preKeyBundleTy)
    (env₁ : Env Δ₁) (env₂ : Env Δ₂)
    (hst : (v st₁).eval env₁ = (v st₂).eval env₂)
    (hpows : pows₁.eval env₁ = pows₂.eval env₂)
    (hbu : (v bu₁).eval env₁ = (v bu₂).eval env₂)
    {c : Fin 3 → ℕ} (hInv : BaseOnlineLenInv c ((v st₁).eval env₁))
    (hc : c 0 ≤ K₁) (hPows : (pows₁.eval env₁).length ≤ K₁) (hLe : K₁ ≤ K₂) :
    (koskBundleOkPowsC S K₁ st₁ pows₁ bu₁).eval env₁ =
      (koskBundleOkPowsC S K₂ st₂ pows₂ bu₂).eval env₂ := by
  have hPrin := Nat.le_trans hInv.prin_le hc
  have hSpks := Nat.le_trans hInv.spks_le hc
  have hOpks := Nat.le_trans hInv.opks_le hc
  simp only [koskBundleOkPowsC, letV_eval]
  refine bind_congr' (findHonestC_sim S st₁ _ st₂ _ _ _
    (by simp [hst]) (by simp [Expr.eval, hbu])
    (by simpa using hPrin) hLe) fun hp => ?_
  refine bind_congr' (qPow8_eval_congr _ _ _ _ (by simp [Expr.eval, hbu])) fun wIk => ?_
  refine bind_congr' (isGameSpkC_sim S st₁ _ st₂ _ _ _
    (by simp [hst]) (by simp [Expr.eval, hbu])
    (by simpa using hSpks) hLe) fun gSpk => ?_
  refine bind_congr' (qPow8_eval_congr _ _ _ _ (by simp [Expr.eval, hbu])) fun wSpk => ?_
  refine bind_congr' ?_ fun opkOk => ?_
  · simp only [caseOptV, Comp.eval]
    have hOpt : (buOpkB (v bu₁)).eval
        (.cons wSpk (.cons gSpk (.cons wIk (.cons hp (.cons (pows₁.eval env₁) env₁))))) =
      (buOpkB (v bu₂)).eval
        (.cons wSpk (.cons gSpk (.cons wIk (.cons hp (.cons (pows₂.eval env₂) env₂))))) := by
      simp [Expr.eval, hbu]
    rw [hOpt]
    cases (buOpkB (v bu₂)).eval
        (.cons wSpk (.cons gSpk (.cons wIk (.cons hp (.cons (pows₂.eval env₂) env₂))))) with
    | none => rfl
    | some opk =>
      refine bind_congr' (isGameOpkC_sim S st₁ _ st₂ _ _ _
        (by simp [hst]) (by simp [Expr.eval])
        (by simpa using hOpks) hLe) fun gOpk => ?_
      refine bind_congr' (qPow8_eval_congr _ _ _ _ (by simp [Expr.eval])) fun wOpk => ?_
      simp only [Comp.eval, orE, Expr.eval, v_eval_cons, v_zero_eval]
      congr 1; congr 1
      exact isAdvPowsE_sim _ _ _ _ _ _
        (by simp [hpows]) (by simp)
        (by simpa using hPows) hLe
  · simp only [Comp.eval, Expr.eval]
    congr 1; congr 1
    · congr 1
      · simp only [orE, isSomeE, Expr.eval, v_eval_cons, v_zero_eval]
        congr 1
        exact isAdvPowsE_sim _ _ _ _ _ _
          (by simp [hpows]) (by simp)
          (by simpa using hPows) hLe
      · simp only [orE, Expr.eval, v_eval_cons, v_zero_eval]
        congr 1
        exact isAdvPowsE_sim _ _ _ _ _ _
          (by simp [hpows]) (by simp)
          (by simpa using hPows) hLe

private theorem liftBase_eq_liftChal {C : _root_.SignalPqxdh.LegacyCosted.ChallengerOracle}
    {Γ : List PT} {t : PT} (c : Comp pqxdhOps pqPrimIface Γ t) :
    _root_.SignalPqxdh.Security.ReductionDsl.KeyInd.liftBase (C := C) c =
      _root_.ReductionDsl.Comp.liftChal (C := C) c := by
  induction c <;> simp [_root_.SignalPqxdh.Security.ReductionDsl.KeyInd.liftBase,
    _root_.ReductionDsl.Comp.liftChal, *] <;> rfl

private theorem liftBase_eval_congr {C : _root_.SignalPqxdh.LegacyCosted.ChallengerOracle}
    {Γ₁ Γ₂ : List PT} {t : PT}
    (c₁ : Comp pqxdhOps pqPrimIface Γ₁ t) (c₂ : Comp pqxdhOps pqPrimIface Γ₂ t)
    (env₁ : Env Γ₁) (env₂ : Env Γ₂) (h : c₁.eval env₁ = c₂.eval env₂) :
    (_root_.SignalPqxdh.Security.ReductionDsl.KeyInd.liftBase (C := C) c₁).eval env₁ =
      (_root_.SignalPqxdh.Security.ReductionDsl.KeyInd.liftBase (C := C) c₂).eval env₂ := by
  rw [liftBase_eq_liftChal, liftBase_eq_liftChal,
    _root_.ReductionDsl.Comp.eval_liftChal,
    _root_.ReductionDsl.Comp.eval_liftChal, h]

private theorem qSigVerify_eval_congr (n : ℕ+) {Γ₁ Γ₂ : List PT}
    (e₁ : Expr pqxdhOps Γ₁ (.prod (B 32) (.prod (B n) (B 64))))
    (e₂ : Expr pqxdhOps Γ₂ (.prod (B 32) (.prod (B n) (B 64))))
    (env₁ : Env Γ₁) (env₂ : Env Γ₂) (h : e₁.eval env₁ = e₂.eval env₂) :
    (qSigVerify n e₁).eval env₁ = (qSigVerify n e₂).eval env₂ :=
  query_eval_congr h

private theorem qKemEncaps_eval_congr {Γ₁ Γ₂ : List PT}
    (e₁ : Expr pqxdhOps Γ₁ (.prod (B 1568) (B 32)))
    (e₂ : Expr pqxdhOps Γ₂ (.prod (B 1568) (B 32)))
    (env₁ : Env Γ₁) (env₂ : Env Γ₂) (h : e₁.eval env₁ = e₂.eval env₂) :
    (qKemEncaps e₁).eval env₁ = (qKemEncaps e₂).eval env₂ :=
  query_eval_congr h

private theorem qKemDecaps_eval_congr {Γ₁ Γ₂ : List PT}
    (e₁ : Expr pqxdhOps Γ₁ (.prod (B 3168) (B 1568)))
    (e₂ : Expr pqxdhOps Γ₂ (.prod (B 3168) (B 1568)))
    (env₁ : Env Γ₁) (env₂ : Env Γ₂) (h : e₁.eval env₁ = e₂.eval env₂) :
    (qKemDecaps e₁).eval env₁ = (qKemDecaps e₂).eval env₂ :=
  query_eval_congr h

private theorem qX25519Base_eval_congr {Γ₁ Γ₂ : List PT}
    (e₁ : Expr pqxdhOps Γ₁ (B 32)) (e₂ : Expr pqxdhOps Γ₂ (B 32))
    (env₁ : Env Γ₁) (env₂ : Env Γ₂) (h : e₁.eval env₁ = e₂.eval env₂) :
    (qX25519Base e₁).eval env₁ = (qX25519Base e₂).eval env₂ :=
  query_eval_congr h

private theorem qX25519_eval_congr {Γ₁ Γ₂ : List PT}
    (e₁ : Expr pqxdhOps Γ₁ (.prod (B 32) (B 32)))
    (e₂ : Expr pqxdhOps Γ₂ (.prod (B 32) (B 32)))
    (env₁ : Env Γ₁) (env₂ : Env Γ₂) (h : e₁.eval env₁ = e₂.eval env₂) :
    (qX25519 e₁).eval env₁ = (qX25519 e₂).eval env₂ :=
  query_eval_congr h

private theorem qIsCanonical_eval_congr {Γ₁ Γ₂ : List PT}
    (e₁ : Expr pqxdhOps Γ₁ (B 32)) (e₂ : Expr pqxdhOps Γ₂ (B 32))
    (env₁ : Env Γ₁) (env₂ : Env Γ₂) (h : e₁.eval env₁ = e₂.eval env₂) :
    (qIsCanonical e₁).eval env₁ = (qIsCanonical e₂).eval env₂ :=
  query_eval_congr h

private theorem sBytes32_eval_const {Γ₁ Γ₂ : List PT} (env₁ : Env Γ₁) (env₂ : Env Γ₂) :
    (sBytes32 : Comp pqxdhOps pqPrimIface Γ₁ (B 32)).eval env₁ =
      (sBytes32 : Comp pqxdhOps pqPrimIface Γ₂ (B 32)).eval env₂ := rfl

private theorem sDrKey96_eval_const {Γ₁ Γ₂ : List PT} (env₁ : Env Γ₁) (env₂ : Env Γ₂) :
    (sDrKey96 : Comp pqxdhOps pqPrimIface Γ₁ drKeyTy).eval env₁ =
      (sDrKey96 : Comp pqxdhOps pqPrimIface Γ₂ drKeyTy).eval env₂ := rfl

private theorem mkSecretPosC_congr {Γ₁ Γ₂ : List PT}
    (z₁ : Expr pqxdhOps Γ₁ (B 32)) (z₂ : Expr pqxdhOps Γ₂ (B 32))
    (env₁ : Env Γ₁) (env₂ : Env Γ₂) (hz : z₁.eval env₁ = z₂.eval env₂) :
    (mkSecretPosC z₁).eval env₁ = (mkSecretPosC z₂).eval env₂ := by
  simp only [mkSecretPosC, letV_eval]
  refine bind_congr' (liftBase_eval_congr _ _ _ _
    (qIsCanonical_eval_congr _ _ _ _ (by simp [hz]))) fun c => ?_
  simp [Comp.eval, Expr.eval, hz]

private theorem mkPairPosC_congr {Γ₁ Γ₂ : List PT}
    (pk1₁ pk2₁ : Expr pqxdhOps Γ₁ (B 32)) (pk1₂ pk2₂ : Expr pqxdhOps Γ₂ (B 32))
    (env₁ : Env Γ₁) (env₂ : Env Γ₂)
    (h1 : pk1₁.eval env₁ = pk1₂.eval env₂) (h2 : pk2₁.eval env₁ = pk2₂.eval env₂) :
    (_root_.SignalPqxdh.Security.ReductionDsl.KeyInd.mkPairPosC pk1₁ pk2₁).eval env₁ =
      (_root_.SignalPqxdh.Security.ReductionDsl.KeyInd.mkPairPosC pk1₂ pk2₂).eval env₂ := by
  simp only [_root_.SignalPqxdh.Security.ReductionDsl.KeyInd.mkPairPosC, letV_eval]
  refine bind_congr' (liftBase_eval_congr _ _ _ _
    (qPow8_eval_congr _ _ _ _ (by simp [Expr.eval, h1]))) fun w1 => ?_
  refine bind_congr' (liftBase_eval_congr _ _ _ _
    (qPow8_eval_congr _ _ _ _ (by simp [Expr.eval, h2]))) fun w2 => ?_
  simp [Comp.eval, Expr.eval, h1, h2]

private theorem computePosC_congr {Γ₁ Γ₂ : List PT}
    (sk1₁ sk2₁ pk1₁ pk2₁ : Expr pqxdhOps Γ₁ (B 32))
    (sk1₂ sk2₂ pk1₂ pk2₂ : Expr pqxdhOps Γ₂ (B 32))
    (env₁ : Env Γ₁) (env₂ : Env Γ₂)
    (hsk1 : sk1₁.eval env₁ = sk1₂.eval env₂) (hsk2 : sk2₁.eval env₁ = sk2₂.eval env₂)
    (hpk1 : pk1₁.eval env₁ = pk1₂.eval env₂) (hpk2 : pk2₁.eval env₁ = pk2₂.eval env₂) :
    (computePosC sk1₁ sk2₁ pk1₁ pk2₁).eval env₁ =
      (computePosC sk1₂ sk2₂ pk1₂ pk2₂).eval env₂ := by
  have hLenB : ∀ {Γa Γb : List PT} (a : Expr pqxdhOps Γa (B 32)) (b : Expr pqxdhOps Γb (B 32))
      (ρa : Env Γa) (ρb : Env Γb), a.eval ρa = b.eval ρb → (lenB a).eval ρa = (lenB b).eval ρb :=
    fun _ _ _ _ h => congrArg (pqxdhOps.eval (Sum.inl (.len 32))) h
  have hb1 : (Expr.not (natEq (lenB sk1₁) (.nat 0))).eval env₁ =
      (Expr.not (natEq (lenB sk1₂) (.nat 0))).eval env₂ := by
    simp [natEq, Expr.eval, hLenB _ _ _ _ hsk1]
  have hb2 : (Expr.not (natEq (lenB sk2₁) (.nat 0))).eval env₁ =
      (Expr.not (natEq (lenB sk2₂) (.nat 0))).eval env₂ := by
    simp [natEq, Expr.eval, hLenB _ _ _ _ hsk2]
  unfold computePosC
  simp only [Comp.eval, hb1, hb2]
  split_ifs with hc1 hc2
  · refine bind_congr' (liftBase_eval_congr _ _ _ _
      (qX25519_eval_congr _ _ _ _ (by simp [Expr.eval, hsk1, hpk2]))) fun z => ?_
    exact mkSecretPosC_congr _ _ _ _ rfl
  · refine bind_congr' (liftBase_eval_congr _ _ _ _
      (qX25519_eval_congr _ _ _ _ (by simp [Expr.eval, hsk2, hpk1]))) fun z => ?_
    exact mkSecretPosC_congr _ _ _ _ rfl
  · exact mkPairPosC_congr _ _ _ _ _ _ hpk1 hpk2

private theorem computeOptPosInitC_congr {Γ₁ Γ₂ : List PT}
    (sk1₁ pk1₁ : Expr pqxdhOps Γ₁ (B 32)) (opk₁ : Expr pqxdhOps Γ₁ (.opt (.prod U32 (B 32))))
    (sk1₂ pk1₂ : Expr pqxdhOps Γ₂ (B 32)) (opk₂ : Expr pqxdhOps Γ₂ (.opt (.prod U32 (B 32))))
    (env₁ : Env Γ₁) (env₂ : Env Γ₂)
    (hsk1 : sk1₁.eval env₁ = sk1₂.eval env₂) (hpk1 : pk1₁.eval env₁ = pk1₂.eval env₂)
    (hopk : opk₁.eval env₁ = opk₂.eval env₂) :
    (computeOptPosInitC sk1₁ pk1₁ opk₁).eval env₁ =
      (computeOptPosInitC sk1₂ pk1₂ opk₂).eval env₂ := by
  simp only [computeOptPosInitC, letV_eval, caseOptV, Comp.eval, Expr.eval, v_zero_eval]
  rw [hopk]
  cases opk₂.eval env₂ with
  | none => rfl
  | some p =>
    refine bind_congr' (computePosC_congr _ _ _ _ _ _ _ _ _ _
      (by simp [Expr.eval, hsk1]) rfl
      (by simp [Expr.eval, hpk1]) (by simp [Expr.eval])) fun pos => ?_
    rfl

private theorem lookupSpkSkC_sim (S : Setup) {K₁ K₂ : Nat}
    {Γs₁ Δ₁ Γs₂ Δ₂ : List PT} [Ext Γs₁ Δ₁] [Ext Γs₂ Δ₂]
    (st₁ : Var Γs₁ keyIndStateTy) (pows₁ : Expr pqxdhOps Δ₁ (.list (.prod (B 32) (B 32))))
    (spk₁ : Expr pqxdhOps Δ₁ (B 32))
    (st₂ : Var Γs₂ keyIndStateTy) (pows₂ : Expr pqxdhOps Δ₂ (.list (.prod (B 32) (B 32))))
    (spk₂ : Expr pqxdhOps Δ₂ (B 32))
    (env₁ : Env Δ₁) (env₂ : Env Δ₂)
    (hst : (v st₁).eval env₁ = (v st₂).eval env₂)
    (hpows : pows₁.eval env₁ = pows₂.eval env₂)
    (hspk : spk₁.eval env₁ = spk₂.eval env₂)
    (hSpks : (stSpksList ((v st₁).eval env₁)).length ≤ K₁)
    (hPows : (pows₁.eval env₁).length ≤ K₁) (hLe : K₁ ≤ K₂) :
    (lookupSpkSkC S K₁ st₁ pows₁ spk₁).eval env₁ =
      (lookupSpkSkC S K₂ st₂ pows₂ spk₂).eval env₂ := by
  simp only [lookupSpkSkC, letV_eval]
  refine bind_congr' (qPow8_eval_congr _ _ _ _ (by simp [Expr.eval, hspk])) fun wSpk => ?_
  refine bind_congr' (findMV_min_congr _ _ _ _ _ _
    (by simp [Expr.eval, hst])
    (by simpa [stSpks, stSpksList, Expr.eval] using hSpks) hLe ?_) fun foundSpk => ?_
  · intro sb
    refine bind_congr' (qPow8_eval_congr _ _ _ _ (by simp [Expr.eval])) fun p1 => ?_
    simp [Comp.eval, eqB, Expr.eval]
  · simp only [Comp.eval, eCaseOpt, eFind, eqB, litB, Expr.eval, v_eval_cons, v_zero_eval]
    cases foundSpk with
    | some sb => rfl
    | none =>
      rw [List.take_of_length_le hPows, hpows,
        List.take_of_length_le (Nat.le_trans (hpows ▸ hPows) hLe)]

private theorem resolveSigPkC_sim (S : Setup) {K₁ K₂ : Nat}
    {Γ₁ Δ₁ Γ₂ Δ₂ : List PT} [Ext Γ₁ Δ₁] [Ext Γ₂ Δ₂]
    (st₁ : Var Γ₁ keyIndStateTy) (ik₁ : Expr pqxdhOps Δ₁ (B 32))
    (st₂ : Var Γ₂ keyIndStateTy) (ik₂ : Expr pqxdhOps Δ₂ (B 32))
    (env₁ : Env Δ₁) (env₂ : Env Δ₂)
    (hst : (v st₁).eval env₁ = (v st₂).eval env₂) (hik : ik₁.eval env₁ = ik₂.eval env₂)
    (hLen : (stPrinList ((v st₁).eval env₁)).length ≤ K₁) (hLe : K₁ ≤ K₂) :
    (resolveSigPkC S K₁ st₁ ik₁).eval env₁ = (resolveSigPkC S K₂ st₂ ik₂).eval env₂ := by
  simp only [resolveSigPkC, letV_eval]
  refine bind_congr' (findHonestC_sim S st₁ _ st₂ _ _ _
    (by simp [hst]) (by simp [hik]) (by simpa using hLen) hLe) fun f => ?_
  simp only [Comp.eval, eCaseOpt, Expr.eval, v_zero_eval]
  cases f <;> simp [hik]

private theorem honestPeerC_sim (S : Setup) {K₁ K₂ : Nat}
    {Γ₁ Δ₁ Γ₂ Δ₂ : List PT} [Ext Γ₁ Δ₁] [Ext Γ₂ Δ₂]
    (st₁ : Var Γ₁ keyIndStateTy) (ik₁ : Expr pqxdhOps Δ₁ (B 32))
    (st₂ : Var Γ₂ keyIndStateTy) (ik₂ : Expr pqxdhOps Δ₂ (B 32))
    (env₁ : Env Δ₁) (env₂ : Env Δ₂)
    (hst : (v st₁).eval env₁ = (v st₂).eval env₂) (hik : ik₁.eval env₁ = ik₂.eval env₂)
    (hLen : (stPrinList ((v st₁).eval env₁)).length ≤ K₁) (hLe : K₁ ≤ K₂) :
    (honestPeerC S K₁ st₁ ik₁).eval env₁ = (honestPeerC S K₂ st₂ ik₂).eval env₂ := by
  simp only [honestPeerC]
  refine bind_congr' (findHonestC_sim S st₁ _ st₂ _ _ _ hst hik hLen hLe) fun f => ?_
  simp only [Comp.eval, eCaseOpt, Expr.eval, v_zero_eval]
  cases f <;> simp

private theorem letV_congr {ι : Type} {T : OracleSpec ι} {I : Iface pqSig T}
    {Γ₁ Γ₂ : List PT} {σ τ : PT}
    (e₁ : Expr pqxdhOps Γ₁ σ) (e₂ : Expr pqxdhOps Γ₂ σ)
    (f₁ : Var (σ :: Γ₁) σ → Comp pqxdhOps I (σ :: Γ₁) τ)
    (f₂ : Var (σ :: Γ₂) σ → Comp pqxdhOps I (σ :: Γ₂) τ)
    (env₁ : Env Γ₁) (env₂ : Env Γ₂)
    (he : e₁.eval env₁ = e₂.eval env₂)
    (hf : ∀ x, (f₁ .zero).eval (.cons x env₁) = (f₂ .zero).eval (.cons x env₂)) :
    (letV e₁ f₁).eval env₁ = (letV e₂ f₂).eval env₂ := by
  simp only [letV_eval, he]; exact hf _

private theorem checkProvC_sim (S : Setup) {K₁ K₂ : Nat}
    {Γs₁ Γb₁ Δ₁ Γs₂ Γb₂ Δ₂ : List PT} [Ext Γs₁ Δ₁] [Ext Γb₁ Δ₁] [Ext Γs₂ Δ₂] [Ext Γb₂ Δ₂]
    (st₁ : Var Γs₁ keyIndStateTy) (bu₁ : Var Γb₁ preKeyBundleTy)
    (st₂ : Var Γs₂ keyIndStateTy) (bu₂ : Var Γb₂ preKeyBundleTy)
    (env₁ : Env Δ₁) (env₂ : Env Δ₂) {c : Fin 3 → ℕ}
    (hst : (v st₁).eval env₁ = (v st₂).eval env₂) (hbu : (v bu₁).eval env₁ = (v bu₂).eval env₂)
    (hInv : BaseOnlineLenInv c ((v st₁).eval env₁)) (hc : c 0 ≤ K₁) (hLe : K₁ ≤ K₂) :
    (checkProvC S K₁ st₁ bu₁).eval env₁ = (checkProvC S K₂ st₂ bu₂).eval env₂ := by
  have hPrin := Nat.le_trans hInv.prin_le hc
  have hSpks := Nat.le_trans hInv.spks_le hc
  have hOpks := Nat.le_trans hInv.opks_le hc
  simp only [checkProvC]
  refine bind_congr' (findHonestC_sim S st₁ _ st₂ _ _ _ hst
    (by simp [Expr.eval, hbu]) hPrin hLe) fun f => ?_
  simp only [caseOptV, Comp.eval, v_zero_eval]
  cases f with
  | none => rfl
  | some kE =>
    refine bind_congr' (anyMV_min_congr _ _ _ _ _ _
      (by simp [Expr.eval, hst])
      (by simpa [stSpks, stSpksList, Expr.eval] using hSpks) hLe ?_) fun spkHon => ?_
    · intro e
      refine bind_congr' (qPow8_eval_congr _ _ _ _ (by simp [Expr.eval])) fun p1 => ?_
      refine bind_congr' (qPow8_eval_congr _ _ _ _ (by simp [Expr.eval, hbu])) fun p2 => ?_
      simp only [Comp.eval, natEq, eqB, Expr.eval, v_eval_cons, v_zero_eval]; rfl
    · refine letV_congr _ _ _ _ _ _
        (eAny_congr_le _ _ _ _ _ _
          (by simp [Expr.eval, hst])
          (by simpa [stSpks, stSpksList, Expr.eval] using hSpks) hLe
          (fun x => by
            simp only [natEq, eqB, sbPqspkPk, buPqspkB, Expr.eval, v_eval_cons, v_zero_eval]
            exact congrArg₂ Bool.and rfl (congrArg (pqxdhOps.eval (Sum.inl (.eq 1568 1568)))
              (Prod.ext rfl (by simp [hbu])))))
        fun pqHon => ?_
      refine bind_congr' ?_ fun opkHon => ?_
      · simp only [Comp.eval, Expr.eval, v_eval_cons]
        rw [hbu]
        cases ((v bu₂).eval env₂).2.2.2.2.1 with
        | none => rfl
        | some o =>
          exact anyMV_min_congr _ _ _ _ _ _
            (by simp [Expr.eval, hst])
            (by simpa [stOpks, stOpksList, Expr.eval] using hOpks) hLe fun e => by
              refine bind_congr' (qPow8_eval_congr _ _ _ _ (by simp [Expr.eval])) fun p1 => ?_
              refine bind_congr' (qPow8_eval_congr _ _ _ _ (by simp [Expr.eval])) fun p2 => ?_
              simp only [Comp.eval, natEq, eqB, Expr.eval, v_eval_cons, v_zero_eval]; rfl
      · simp only [Comp.eval, Expr.eval, v_eval_cons, v_zero_eval]

private theorem partnerC_congr {Γs₁ Γr₁ Δ₁ Γs₂ Γr₂ Δ₂ : List PT}
    [Ext Γs₁ Δ₁] [Ext Γr₁ Δ₁] [Ext Γs₂ Δ₂] [Ext Γr₂ Δ₂]
    (s₁ : Var Γs₁ keyIndSessionEntryTy) (r₁ : Var Γr₁ keyIndRespEntryTy)
    (s₂ : Var Γs₂ keyIndSessionEntryTy) (r₂ : Var Γr₂ keyIndRespEntryTy)
    (env₁ : Env Δ₁) (env₂ : Env Δ₂)
    (hs : (v s₁).eval env₁ = (v s₂).eval env₂) (hr : (v r₁).eval env₁ = (v r₂).eval env₂) :
    (partnerC s₁ r₁).eval env₁ = (partnerC s₂ r₂).eval env₂ := by
  simp only [partnerC]
  refine bind_congr' (qPow8_eval_congr _ _ _ _ (by simp [Expr.eval, hs])) fun sIk => ?_
  refine bind_congr' (qPow8_eval_congr _ _ _ _ (by simp [Expr.eval, hr])) fun rIk => ?_
  refine bind_congr' (qPow8_eval_congr _ _ _ _ (by simp [Expr.eval, hs])) fun sPeer => ?_
  refine bind_congr' (qPow8_eval_congr _ _ _ _ (by simp [Expr.eval, hr])) fun rResp => ?_
  refine bind_congr' (qPow8_eval_congr _ _ _ _ (by simp [Expr.eval, hs])) fun sSpk => ?_
  refine bind_congr' (qPow8_eval_congr _ _ _ _ (by simp [Expr.eval, hr])) fun rSpk => ?_
  refine bind_congr' (qPow8_eval_congr _ _ _ _ (by
    simp only [getDBytes, eCaseOpt, sePeerOpk, litB, Expr.eval, v_eval_cons, v_zero_eval]
    rw [hs])) fun sOpk => ?_
  refine bind_congr' (qPow8_eval_congr _ _ _ _ (by
    simp only [getDBytes, eCaseOpt, reOpk, litB, Expr.eval, v_eval_cons, v_zero_eval]
    rw [hr])) fun rOpk => ?_
  simp only [Comp.eval, optBytesEq, _root_.SignalPqxdh.Security.ReductionDsl.KeyInd.eLet2,
    eLet, eCaseOpt, eqB, sePeerOpk, reOpk, hdEkAPk, seHdr, reHdr,
    sePeerPqspk, rePqspk, hdKemCt, Expr.eval, v_eval_cons, v_zero_eval]
  rw [hs, hr]

private theorem chooseInitRandC_sim (S : Setup) {K₁ K₂ : Nat}
    {Γ₁ Δ₁ Γ₂ Δ₂ : List PT} [Ext Γ₁ Δ₁] [Ext Γ₂ Δ₂]
    (st₁ : Var Γ₁ keyIndStateTy) (s₁ : Var Δ₁ keyIndSessionEntryTy)
    (st₂ : Var Γ₂ keyIndStateTy) (s₂ : Var Δ₂ keyIndSessionEntryTy)
    (env₁ : Env Δ₁) (env₂ : Env Δ₂)
    (hst : (v st₁).eval env₁ = (v st₂).eval env₂) (hs : (v s₁).eval env₁ = (v s₂).eval env₂)
    (hLen : (stRespsList ((v st₁).eval env₁)).length ≤ K₁) (hLe : K₁ ≤ K₂) :
    (chooseInitRandC S K₁ st₁ s₁).eval env₁ = (chooseInitRandC S K₂ st₂ s₂).eval env₂ := by
  simp only [chooseInitRandC]
  refine bind_congr' (liftBase_eval_congr _ _ _ _
    (findMV_min_congr _ _ _ _ _ _
      (by simp [Expr.eval, hst])
      (by simpa [stResps, stRespsList, Expr.eval] using hLen) hLe fun r =>
      partnerC_congr _ _ _ _ _ _ (by simp [hs]) rfl)) fun f => ?_
  simp only [caseOptV, Comp.eval, v_zero_eval]
  cases f with
  | none => exact liftBase_eval_congr _ _ _ _ (sDrKey96_eval_const _ _)
  | some r => simp [Expr.eval]

private theorem chooseRespRandC_sim (S : Setup) {K₁ K₂ : Nat}
    {Γ₁ Δ₁ Γ₂ Δ₂ : List PT} [Ext Γ₁ Δ₁] [Ext Γ₂ Δ₂]
    (st₁ : Var Γ₁ keyIndStateTy) (r₁ : Var Δ₁ keyIndRespEntryTy)
    (st₂ : Var Γ₂ keyIndStateTy) (r₂ : Var Δ₂ keyIndRespEntryTy)
    (env₁ : Env Δ₁) (env₂ : Env Δ₂)
    (hst : (v st₁).eval env₁ = (v st₂).eval env₂) (hr : (v r₁).eval env₁ = (v r₂).eval env₂)
    (hLen : (stSessList ((v st₁).eval env₁)).length ≤ K₁) (hLe : K₁ ≤ K₂) :
    (chooseRespRandC S K₁ st₁ r₁).eval env₁ = (chooseRespRandC S K₂ st₂ r₂).eval env₂ := by
  simp only [chooseRespRandC]
  refine bind_congr' (liftBase_eval_congr _ _ _ _
    (findMV_min_congr _ _ _ _ _ _
      (by simp [Expr.eval, hst])
      (by simpa [stSess, stSessList, Expr.eval] using hLen) hLe fun s =>
      partnerC_congr _ _ _ _ _ _ rfl (by simp [hr]))) fun f => ?_
  simp only [caseOptV, Comp.eval, v_zero_eval]
  cases f with
  | none => exact liftBase_eval_congr _ _ _ _ (sDrKey96_eval_const _ _)
  | some s => simp [Expr.eval]

private theorem kyberCheckE_sim {K₁ K₂ : Nat} {Δ₁ Δ₂ : List PT}
    (used₁ : Expr pqxdhOps Δ₁ (.list (.prod .nat (.prod U32 (.prod U32 (B 32))))))
    (entry₁ : Expr pqxdhOps Δ₁ (.prod .nat (.prod U32 (.prod U32 (B 32)))))
    (used₂ : Expr pqxdhOps Δ₂ (.list (.prod .nat (.prod U32 (.prod U32 (B 32))))))
    (entry₂ : Expr pqxdhOps Δ₂ (.prod .nat (.prod U32 (.prod U32 (B 32)))))
    (env₁ : Env Δ₁) (env₂ : Env Δ₂)
    (hu : used₁.eval env₁ = used₂.eval env₂) (he : entry₁.eval env₁ = entry₂.eval env₂)
    (hLen : (used₁.eval env₁).length ≤ K₁) (hLe : K₁ ≤ K₂) :
    (kyberCheckE K₁ used₁ entry₁).eval env₁ = (kyberCheckE K₂ used₂ entry₂).eval env₂ := by
  simp only [kyberCheckE, _root_.SignalPqxdh.Security.ReductionDsl.KeyInd.eLet2, eLet,
    Expr.eval, v_eval_cons, v_zero_eval]
  refine if_congr
    (Eq.to_iff (congrArg (· = true)
      (eAny_congr_le _ _ _ _ _ _
        (by simp [hu])
        (by simpa using hLen) hLe
        (fun x => by
          simp only [_root_.SignalPqxdh.Security.ReductionDsl.KeyInd.kyberEq,
            natEq, eqU32, eqB, Expr.eval, v_eval_cons, v_zero_eval, he]; rfl))))
    (by simp [hu])
    (by simp [hu, he])

private theorem finishAcceptGdhC_sim (S : Setup) {K₁ K₂ : Nat}
    {Γ₂a Γ₃a Γ₄a Γ₅a Γ₆a Γ₇a Δ₁ Γ₂b Γ₃b Γ₄b Γ₅b Γ₆b Γ₇b Δ₂ : List PT}
    [Ext Γ₂a Δ₁] [Ext Γ₃a Δ₁] [Ext Γ₄a Δ₁] [Ext Γ₅a Δ₁] [Ext Γ₆a Δ₁] [Ext Γ₇a Δ₁]
    [Ext Γ₂b Δ₂] [Ext Γ₃b Δ₂] [Ext Γ₄b Δ₂] [Ext Γ₅b Δ₂] [Ext Γ₆b Δ₂] [Ext Γ₇b Δ₂]
    (sm₁ : Var Γ₂a simTy) (bSt₁ : Var Γ₃a keyIndStateTy) (hasOpk : Bool) (x₁ : Var Γ₄a accQTy)
    (ke₁ : Var Γ₅a (.prod .nat principalEntryTy))
    (be₁ : Var Γ₆a (.prod (.prod .nat .nat) spkBundleEntryTy))
    (opkPkOpt₁ : Expr pqxdhOps Δ₁ (.opt (B 32)))
    (opks₁ : Expr pqxdhOps Δ₁ (.list (.prod (.prod .nat (.prod .nat .nat)) opkEntryTy)))
    (usedO₁ usedN₁ : Expr pqxdhOps Δ₁ (.list (.prod .nat (.prod .nat .nat))))
    (kyb₁ : Expr pqxdhOps Δ₁ (.list (.prod .nat (.prod U32 (.prod U32 (B 32))))))
    (patchR₁ : Var Γ₇a (.prod drKeyTy (.list fgPatchEntryTy)))
    (sm₂ : Var Γ₂b simTy) (bSt₂ : Var Γ₃b keyIndStateTy) (x₂ : Var Γ₄b accQTy)
    (ke₂ : Var Γ₅b (.prod .nat principalEntryTy))
    (be₂ : Var Γ₆b (.prod (.prod .nat .nat) spkBundleEntryTy))
    (opkPkOpt₂ : Expr pqxdhOps Δ₂ (.opt (B 32)))
    (opks₂ : Expr pqxdhOps Δ₂ (.list (.prod (.prod .nat (.prod .nat .nat)) opkEntryTy)))
    (usedO₂ usedN₂ : Expr pqxdhOps Δ₂ (.list (.prod .nat (.prod .nat .nat))))
    (kyb₂ : Expr pqxdhOps Δ₂ (.list (.prod .nat (.prod U32 (.prod U32 (B 32))))))
    (patchR₂ : Var Γ₇b (.prod drKeyTy (.list fgPatchEntryTy)))
    (env₁ : Env Δ₁) (env₂ : Env Δ₂) {c : Fin 3 → ℕ}
    (hsm : (v sm₁).eval env₁ = (v sm₂).eval env₂)
    (hbSt : (v bSt₁).eval env₁ = (v bSt₂).eval env₂)
    (hx : (v x₁).eval env₁ = (v x₂).eval env₂)
    (hke : (v ke₁).eval env₁ = (v ke₂).eval env₂)
    (hbe : (v be₁).eval env₁ = (v be₂).eval env₂)
    (hopkPk : opkPkOpt₁.eval env₁ = opkPkOpt₂.eval env₂)
    (hopks : opks₁.eval env₁ = opks₂.eval env₂)
    (husedO : usedO₁.eval env₁ = usedO₂.eval env₂)
    (husedN : usedN₁.eval env₁ = usedN₂.eval env₂)
    (hkyb : kyb₁.eval env₁ = kyb₂.eval env₂)
    (hpatch : (v patchR₁).eval env₁ = (v patchR₂).eval env₂)
    (hInv : BaseOnlineLenInv c ((v bSt₁).eval env₁)) (hc : c 0 ≤ K₁) (hLe : K₁ ≤ K₂) :
    (finishAcceptGdhC S K₁ sm₁ bSt₁ hasOpk x₁ ke₁ be₁ opkPkOpt₁ opks₁ usedO₁ usedN₁ kyb₁ patchR₁).eval env₁ =
      (finishAcceptGdhC S K₂ sm₂ bSt₂ hasOpk x₂ ke₂ be₂ opkPkOpt₂ opks₂ usedO₂ usedN₂ kyb₂ patchR₂).eval env₂ := by
  have hPrin := Nat.le_trans hInv.prin_le hc
  have hSess := Nat.le_trans hInv.sess_le hc
  simp only [finishAcceptGdhC, letV_eval]
  refine bind_congr' (liftBase_eval_congr _ _ _ _
    (findHonestC_sim S bSt₁ _ bSt₂ _ _ _ (by simp [hbSt])
      (by simp [_root_.SignalPqxdh.Security.ReductionDsl.KeyInd.qHdr, Expr.eval, hx])
      (by simpa using hPrin) hLe)) fun shOpt => ?_
  simp only [letV_eval]
  refine bind_congr' (chooseRespRandC_sim S bSt₁ _ bSt₂ _ _ _
    (by simp [hbSt])
    (by cases hasOpk <;>
          simp [_root_.SignalPqxdh.Security.ReductionDsl.KeyInd.qKJO,
            _root_.SignalPqxdh.Security.ReductionDsl.KeyInd.qK,
            _root_.SignalPqxdh.Security.ReductionDsl.KeyInd.qJ,
            _root_.SignalPqxdh.Security.ReductionDsl.KeyInd.qO,
            _root_.SignalPqxdh.Security.ReductionDsl.KeyInd.qHdr,
            isSomeE, Expr.eval, hx, hke, hbe, hopkPk, hpatch])
    (by simpa using hSess) hLe) fun dkRand => ?_
  simp only [letV_eval, Comp.eval, eCaseOpt, Expr.eval, v_zero_eval]
  cases hasOpk <;> cases shOpt <;>
    simp [smUpd, _root_.SignalPqxdh.Security.ReductionDsl.KeyInd.smMk, stUpd,
      _root_.SignalPqxdh.Security.ReductionDsl.KeyInd.stSecb, stPrin, stSpks, stSess, stResps,
      _root_.SignalPqxdh.Security.ReductionDsl.KeyInd.stRo, stAdv,
      _root_.SignalPqxdh.Security.ReductionDsl.KeyInd.smRaw,
      _root_.SignalPqxdh.Security.ReductionDsl.KeyInd.smLog, smPows,
      reUpd, reMk, _root_.SignalPqxdh.Security.ReductionDsl.KeyInd.qKJO,
      _root_.SignalPqxdh.Security.ReductionDsl.KeyInd.qK,
      _root_.SignalPqxdh.Security.ReductionDsl.KeyInd.qJ,
      _root_.SignalPqxdh.Security.ReductionDsl.KeyInd.qO,
      _root_.SignalPqxdh.Security.ReductionDsl.KeyInd.qHdr,
      isSomeE, _root_.SignalPqxdh.Security.ReductionDsl.KeyInd.rDrKey,
      _root_.SignalPqxdh.Security.ReductionDsl.KeyInd.rAccFresh,
      Expr.eval, hsm, hbSt, hx, hke, hbe, hopkPk, hopks, husedO, husedN, hkyb, hpatch]

/-- Congruence for `extract1KeyActiveC` under fuel clamping `K₁ ≤ K₂` when `BaseOnlineLenInv` holds. -/
theorem extract1KeyActiveC_sim (S : Setup) {K₁ K₂ : Nat}
    {Γs₁ Γb₁ Δ₁ Γs₂ Γb₂ Δ₂ : List PT} [Ext Γs₁ Δ₁] [Ext Γb₁ Δ₁] [Ext Γs₂ Δ₂] [Ext Γb₂ Δ₂]
    (st₁ : Var Γs₁ Computational.Proofs.SignalPqxdh.Delta.KeyInd1KeyActiveProgs.sig1KeyActiveStTy)
    (bu₁ : Var Γb₁ preKeyBundleTy)
    (st₂ : Var Γs₂ Computational.Proofs.SignalPqxdh.Delta.KeyInd1KeyActiveProgs.sig1KeyActiveStTy)
    (bu₂ : Var Γb₂ preKeyBundleTy)
    (env₁ : Env Δ₁) (env₂ : Env Δ₂) {c : Fin 3 → ℕ}
    (htp : ((v st₁).eval env₁).1 = ((v st₂).eval env₂).1)
    (hsm : ((v st₁).eval env₁).2.1 = ((v st₂).eval env₂).2.1)
    (hpk : ((v st₁).eval env₁).2.2.2.1 = ((v st₂).eval env₂).2.2.2.1)
    (hfg : ((v st₁).eval env₁).2.2.2.2.2 = ((v st₂).eval env₂).2.2.2.2.2)
    (hbu : (v bu₁).eval env₁ = (v bu₂).eval env₂)
    (hInv : BaseOnlineLenInv c ((v st₁).eval env₁).2.1.1) (hc : c 0 ≤ K₁) (hLe : K₁ ≤ K₂) :
    (Computational.Proofs.SignalPqxdh.Delta.KeyInd1KeyActiveProgs.extract1KeyActiveC
      S K₁ st₁ bu₁).eval env₁ =
    (Computational.Proofs.SignalPqxdh.Delta.KeyInd1KeyActiveProgs.extract1KeyActiveC
      S K₂ st₂ bu₂).eval env₂ := by
  have hPrin := Nat.le_trans hInv.prin_le hc
  have hSpks := Nat.le_trans hInv.spks_le hc
  have hEncEc : ∀ {Γa Γb : List PT} (a : Expr pqxdhOps Γa (B 32)) (b : Expr pqxdhOps Γb (B 32))
      (ρa : Env Γa) (ρb : Env Γb), a.eval ρa = b.eval ρb → (encEC a).eval ρa = (encEC b).eval ρb :=
    fun _ _ _ _ h => congrArg (pqxdhOps.eval (Sum.inl (.cons _ 32))) h
  have hEncKem : ∀ {Γa Γb : List PT} (a : Expr pqxdhOps Γa (B 1568)) (b : Expr pqxdhOps Γb (B 1568))
      (ρa : Env Γa) (ρb : Env Γb), a.eval ρa = b.eval ρb → (encKEM a).eval ρa = (encKEM b).eval ρb :=
    fun _ _ _ _ h => congrArg (pqxdhOps.eval (Sum.inl (.cons _ 1568))) h
  have hWidenEc : ∀ {Γa Γb : List PT} (a : Expr pqxdhOps Γa (B 33)) (b : Expr pqxdhOps Γb (B 33))
      (ρa : Env Γa) (ρb : Env Γb), a.eval ρa = b.eval ρb →
      (_root_.SignalPqxdh.Security.ReductionDsl.KeyInd.widenEC a).eval ρa =
        (_root_.SignalPqxdh.Security.ReductionDsl.KeyInd.widenEC b).eval ρb :=
    fun _ _ _ _ h => congrArg (pqxdhOps.eval (Sum.inl (.widen 33 1569))) h
  have hEqB : ∀ {n m : ℕ+} {Γa Γb : List PT}
      (a₁ : Expr pqxdhOps Γa (B n)) (b₁ : Expr pqxdhOps Γa (B m))
      (a₂ : Expr pqxdhOps Γb (B n)) (b₂ : Expr pqxdhOps Γb (B m))
      (ρa : Env Γa) (ρb : Env Γb),
      a₁.eval ρa = a₂.eval ρb → b₁.eval ρa = b₂.eval ρb →
      (eqB a₁ b₁).eval ρa = (eqB a₂ b₂).eval ρb :=
    fun _ _ _ _ _ _ ha hb => congrArg (pqxdhOps.eval (Sum.inl (.eq _ _))) (Prod.ext ha hb)
  simp only [Computational.Proofs.SignalPqxdh.Delta.KeyInd1KeyActiveProgs.extract1KeyActiveC,
    letV_eval]
  refine bind_congr' (liftBase_eval_congr _ _ _ _ ?_) fun peer => ?_
  · simp only [letV_eval]
    exact honestPeerC_sim S .zero _ .zero _ _ _
      (by simp [_root_.SignalPqxdh.Security.ReductionDsl.KeyInd.s1Base,
        _root_.SignalPqxdh.Security.ReductionDsl.KeyInd.s1Fg, smBase, Expr.eval, hsm])
      (by simp [Expr.eval, hbu])
      (by simpa [_root_.SignalPqxdh.Security.ReductionDsl.KeyInd.s1Base,
        _root_.SignalPqxdh.Security.ReductionDsl.KeyInd.s1Fg, smBase, Expr.eval] using hPrin) hLe
  · refine bind_congr' (liftBase_eval_congr _ _ _ _
      (qSigVerify_eval_congr 33 _ _ _ _ (by
        simp only [buSpkB, Expr.eval, v_eval_cons, v_zero_eval]
        refine Prod.ext (by simp [hpk])
          (Prod.ext (hEncEc _ _ _ _ (by simp [Expr.eval, hbu]))
            (by simp [hbu]))))) fun v1 => ?_
    refine bind_congr' (liftBase_eval_congr _ _ _ _
      (qSigVerify_eval_congr 1569 _ _ _ _ (by
        simp only [buPqspkB, Expr.eval, v_eval_cons, v_zero_eval]
        refine Prod.ext (by simp [hpk])
          (Prod.ext (hEncKem _ _ _ _ (by simp [Expr.eval, hbu]))
            (by simp [hbu]))))) fun v2 => ?_
    simp only [Comp.eval, eCaseOpt,
      _root_.SignalPqxdh.Security.ReductionDsl.KeyInd.s1Forgery,
      Expr.eval, v_eval_cons, v_zero_eval, hfg]
    cases ((v st₂).eval env₂).2.2.2.2.2 with
    | some fg => rfl
    | none =>
      cases peer with
      | none => rfl
      | some k =>
        congr 1
        refine if_congr
          (Eq.to_iff (congrArg (· = true) (by
            simp only [Computational.Proofs.SignalPqxdh.Delta.KeyInd1KeyActiveProgs.optNatMatchesE,
              Computational.Proofs.SignalPqxdh.Delta.KeyInd1KeyActiveProgs.saTP,
              _root_.SignalPqxdh.Security.ReductionDsl.KeyInd.eLet2, eLet, eCaseOpt, natEq,
              Expr.eval, v_eval_cons, v_zero_eval, htp]; rfl)))
          (if_congr
            (Eq.to_iff (congrArg (· = true) (congrArg₂ Bool.and rfl (congrArg Bool.not
              (eAny_congr_le _ _ _ _ _ _
                (by simp [_root_.SignalPqxdh.Security.ReductionDsl.KeyInd.s1Base,
                  _root_.SignalPqxdh.Security.ReductionDsl.KeyInd.s1Fg, smBase, Expr.eval, hsm])
                (by simpa [_root_.SignalPqxdh.Security.ReductionDsl.KeyInd.s1Base,
                  _root_.SignalPqxdh.Security.ReductionDsl.KeyInd.s1Fg, stSpks, stSpksList, smBase,
                  Expr.eval] using hSpks) hLe
                (fun x => by
                  simp only [natEq, Expr.eval, v_eval_cons, v_zero_eval]
                  exact congrArg₂ Bool.and rfl (hEqB _ _ _ _ _ _
                    (by simp [Expr.eval])
                    (by simp [Expr.eval, hbu]))))))))
            (congrArg Option.some
              (Prod.ext (hWidenEc _ _ _ _ (hEncEc _ _ _ _ (by simp [Expr.eval, hbu])))
                (by simp [hbu])))
            (if_congr
              (Eq.to_iff (congrArg (· = true) (congrArg₂ Bool.and rfl (congrArg Bool.not
                (eAny_congr_le _ _ _ _ _ _
                  (by simp [_root_.SignalPqxdh.Security.ReductionDsl.KeyInd.s1Base,
                    _root_.SignalPqxdh.Security.ReductionDsl.KeyInd.s1Fg, smBase, Expr.eval, hsm])
                  (by simpa [_root_.SignalPqxdh.Security.ReductionDsl.KeyInd.s1Base,
                    _root_.SignalPqxdh.Security.ReductionDsl.KeyInd.s1Fg, stSpks, stSpksList, smBase,
                    Expr.eval] using hSpks) hLe
                  (fun x => by
                    simp only [natEq, Expr.eval, v_eval_cons, v_zero_eval]
                    exact congrArg₂ Bool.and rfl (hEqB _ _ _ _ _ _
                      (by simp [Expr.eval])
                      (by simp [Expr.eval, hbu]))))))))
              (congrArg Option.some
                (Prod.ext (hEncKem _ _ _ _ (by simp [Expr.eval, hbu]))
                  (by simp [hbu])))
              rfl))
          rfl

private theorem pure_sim {ι : Type} {T : OracleSpec ι} {α β : Type}
    (proj : α → β) (x : α) (y : β) {P : α → Prop}
    (hxy : proj x = y) (hP : P x) :
    proj <$> (pure x : OracleComp T α) = pure y ∧
    ∀ r ∈ support (pure x : OracleComp T α), P r := by
  refine ⟨by simp [hxy], fun r hr => ?_⟩
  simp only [mem_support_pure_iff] at hr
  subst hr; exact hP

private theorem bind_sim_same {ι : Type} {T : OracleSpec ι} {γ α β : Type}
    (proj : α → β) (oa₁ oa₂ : OracleComp T γ)
    (f : γ → OracleComp T α) (g : γ → OracleComp T β) {P : α → Prop}
    (hoa : oa₁ = oa₂)
    (hEq : ∀ x, proj <$> f x = g x)
    (hP : ∀ x ∈ support oa₁, ∀ r ∈ support (f x), P r) :
    proj <$> (oa₁ >>= f) = (oa₂ >>= g) ∧
    ∀ r ∈ support (oa₁ >>= f), P r := by
  subst hoa
  refine ⟨by rw [map_bind]; exact bind_congr' rfl hEq, fun r hr => ?_⟩
  simp only [mem_support_bind_iff] at hr
  rcases hr with ⟨x, hx, hr'⟩
  exact hP x hx r hr'

private theorem bind_sim_of_map {ι : Type} {T : OracleSpec ι} {γ₁ γ₂ α β : Type}
    (pγ : γ₁ → γ₂) (proj : α → β)
    (oa₁ : OracleComp T γ₁) (oa₂ : OracleComp T γ₂)
    (f : γ₁ → OracleComp T α) (g : γ₂ → OracleComp T β) {P : α → Prop}
    (hoa : pγ <$> oa₁ = oa₂)
    (hEq : ∀ x, proj <$> f x = g (pγ x))
    (hP : ∀ x ∈ support oa₁, ∀ r ∈ support (f x), P r) :
    proj <$> (oa₁ >>= f) = (oa₂ >>= g) ∧
    ∀ r ∈ support (oa₁ >>= f), P r := by
  subst hoa
  refine ⟨by rw [map_bind, bind_map_left]; exact bind_congr' rfl hEq, fun r hr => ?_⟩
  simp only [mem_support_bind_iff] at hr
  rcases hr with ⟨x, hx, hr'⟩
  exact hP x hx r hr'

private theorem BaseOnlineLenInv_bump_online {S : Setup} {c : Fin 3 → ℕ} {t : KeyIndQuery S}
    {bSt : keyIndStateTy.denote}
    (ht0 : keyIndSimPred S 0 t) (hInv : BaseOnlineLenInv c bSt) :
    BaseOnlineLenInv (bumpPred (keyIndSimPred S) c t) bSt := by
  have hc0 : bumpPred (keyIndSimPred S) c t 0 = c 0 + 1 := by simp [bumpPred, ht0]
  exact
    { prin_le   := by rw [hc0]; exact Nat.le_succ_of_le hInv.prin_le
      spks_le   := by rw [hc0]; exact Nat.le_succ_of_le hInv.spks_le
      opks_le   := by rw [hc0]; exact Nat.le_succ_of_le hInv.opks_le
      sess_le   := by rw [hc0]; exact Nat.le_succ_of_le hInv.sess_le
      resps_le  := by rw [hc0]; exact Nat.le_succ_of_le hInv.resps_le
      usedO_le  := by rw [hc0]; exact Nat.le_succ_of_le hInv.usedO_le
      usedN_le  := by rw [hc0]; exact Nat.le_succ_of_le hInv.usedN_le
      kyb_le    := by rw [hc0]; exact Nat.le_succ_of_le hInv.kyb_le
      adv_le    := by rw [hc0]; exact Nat.le_succ_of_le hInv.adv_le
      counts_eq := bumpPred_keyIndSimPred_sum t hInv.counts_eq }

private theorem GdhSimInv_bump_online {S : Setup} {b : QueryBudget}
    {c : Fin 3 → ℕ} {t : KeyIndQuery S} {sK : simShadowAtomicTy.denote}
    (ht0 : keyIndSimPred S 0 t) (ht1 : ¬ keyIndSimPred S 1 t)
    (hInv : GdhSimInv S b c sK) :
    GdhSimInv S b (bumpPred (keyIndSimPred S) c t) sK := by
  have hc0 : bumpPred (keyIndSimPred S) c t 0 = c 0 + 1 := by simp [bumpPred, ht0]
  have hc1 : bumpPred (keyIndSimPred S) c t 1 = c 1 := by simp [bumpPred, ht1]
  obtain ⟨tagged, hRel, hWf, hRoLe⟩ := hInv.fg_shadow
  exact
    { online_len := BaseOnlineLenInv_bump_online ht0 hInv.online_len
      fg_sess_le := by rw [hc0]; exact Nat.le_succ_of_le hInv.fg_sess_le
      fg_shadow  := ⟨tagged, hRel, hWf, hc1 ▸ hRoLe⟩
      raw_len    := hc1 ▸ hInv.raw_len
      raw_shadow := hInv.raw_shadow
      log_len    := hc1 ▸ hInv.log_len
      pows_len   := by rw [hc0]; exact Nat.le_succ_of_le hInv.pows_len }

private theorem BaseOnlineLenInv_initiate {S : Setup} {c : Fin 3 → ℕ} {t : KeyIndQuery S}
    {bSt : keyIndStateTy.denote} (sFinal : keyIndSessionEntryTy.denote)
    (ht0 : keyIndSimPred S 0 t) (hInv : BaseOnlineLenInv c bSt) :
    BaseOnlineLenInv (bumpPred (keyIndSimPred S) c t)
      (bSt.1, (bSt.2.1, (bSt.2.2.1, (bSt.2.2.2.1,
        (sFinal :: bSt.2.2.2.2.1, bSt.2.2.2.2.2))))) := by
  have hc0 : bumpPred (keyIndSimPred S) c t 0 = c 0 + 1 := by simp [bumpPred, ht0]
  exact
    { prin_le   := by rw [hc0]; exact Nat.le_succ_of_le hInv.prin_le
      spks_le   := by rw [hc0]; exact Nat.le_succ_of_le hInv.spks_le
      opks_le   := by rw [hc0]; exact Nat.le_succ_of_le hInv.opks_le
      sess_le   := by
        rw [hc0]
        simpa [stSessList] using Nat.succ_le_succ hInv.sess_le
      resps_le  := by rw [hc0]; exact Nat.le_succ_of_le hInv.resps_le
      usedO_le  := by rw [hc0]; exact Nat.le_succ_of_le hInv.usedO_le
      usedN_le  := by rw [hc0]; exact Nat.le_succ_of_le hInv.usedN_le
      kyb_le    := by rw [hc0]; exact Nat.le_succ_of_le hInv.kyb_le
      adv_le    := by rw [hc0]; exact Nat.le_succ_of_le hInv.adv_le
      counts_eq := bumpPred_keyIndSimPred_sum t hInv.counts_eq }

private theorem BaseOnlineLenInv_accept {S : Setup} {c : Fin 3 → ℕ} {t : KeyIndQuery S}
    {bSt : keyIndStateTy.denote}
    (rFinal : keyIndRespEntryTy.denote)
    (opks' : List _) (usedO' usedN' : List _) (kyb' : List _)
    (ht0 : keyIndSimPred S 0 t) (hInv : BaseOnlineLenInv c bSt)
    (hOpks : opks'.length ≤ (stOpksList bSt).length + 1)
    (hUsedO : usedO'.length ≤ (stUsedOList bSt).length + 1)
    (hUsedN : usedN'.length ≤ (stUsedNList bSt).length + 1)
    (hKyb : kyb'.length ≤ (stKybList bSt).length + 1) :
    BaseOnlineLenInv (bumpPred (keyIndSimPred S) c t)
      (bSt.1, (bSt.2.1, (bSt.2.2.1, (opks',
        (bSt.2.2.2.2.1, (rFinal :: bSt.2.2.2.2.2.1,
          (usedO', (usedN', (kyb', bSt.2.2.2.2.2.2.2.2.2))))))))) := by
  have hc0 : bumpPred (keyIndSimPred S) c t 0 = c 0 + 1 := by simp [bumpPred, ht0]
  have h1 := hInv.opks_le
  have h2 := hInv.usedO_le
  have h3 := hInv.usedN_le
  have h4 := hInv.kyb_le
  exact
    { prin_le   := by rw [hc0]; exact Nat.le_succ_of_le hInv.prin_le
      spks_le   := by rw [hc0]; exact Nat.le_succ_of_le hInv.spks_le
      opks_le   := by rw [hc0]; dsimp [stOpksList] at *; omega
      sess_le   := by rw [hc0]; exact Nat.le_succ_of_le hInv.sess_le
      resps_le  := by
        rw [hc0]
        simpa [stRespsList] using Nat.succ_le_succ hInv.resps_le
      usedO_le  := by rw [hc0]; dsimp [stUsedOList] at *; omega
      usedN_le  := by rw [hc0]; dsimp [stUsedNList] at *; omega
      kyb_le    := by rw [hc0]; dsimp [stKybList] at *; omega
      adv_le    := by rw [hc0]; exact Nat.le_succ_of_le hInv.adv_le
      counts_eq := bumpPred_keyIndSimPred_sum t hInv.counts_eq }

private theorem GdhSimInv_after_fgPatch {S : Setup} {b : QueryBudget}
    {c : Fin 3 → ℕ} {t : KeyIndQuery S}
    (sm : simTy.denote) (fgSh : fgSessCtrTy.denote) (fgShFull : fgShadowAtomicTy.denote)
    (bSt' : keyIndStateTy.denote)
    (fgL' : (Ty.list fgPatchEntryTy).denote)
    (fgSh' : fgSessCtrTy.denote)
    (ht0 : keyIndSimPred S 0 t) (ht1 : ¬ keyIndSimPred S 1 t)
    (hInv : GdhSimInv S b c
      (embedVal simTy sm,
        ((embedVal fgSessCtrTy fgSh).1, ((embedVal fgSessCtrTy fgSh).2, fgShFull.2.2))))
    (hbSt' : BaseOnlineLenInv (bumpPred (keyIndSimPred S) c t) bSt')
    (hSessLen : (embedVal (.list seqFgEntryTy) fgSh'.1).length ≤
      (embedVal (.list seqFgEntryTy) fgSh.1).length + 1)
    (hShadow' : ∃ tagged' : List (TaggedEntry Bytes FgEntryA),
      ShadowRelB192 (drKeyT (ℓ := 0) (Pt := Empty)) b.q_total (keyIndKFuelsOfBudget S b).kAvl
        fgEntryDk (embedVal (.list fgPatchEntryTy) fgL')
        tagged' fgShFull.2.2.1 (embedVal (.list seqFgEntryTy) fgSh'.1) fgSh'.2 ∧
      (∀ te ∈ tagged', ∀ sec, te.tag = .ro sec → RoFgEntryWf sec te.entry) ∧
      (roEntriesOf fgEntryDk tagged').length ≤ c 1) :
    GdhSimInv S b (bumpPred (keyIndSimPred S) c t)
      (embedVal simTy (bSt', (fgL', sm.2.2)),
        ((embedVal fgSessCtrTy fgSh').1, ((embedVal fgSessCtrTy fgSh').2, fgShFull.2.2))) := by
  have hc0 : bumpPred (keyIndSimPred S) c t 0 = c 0 + 1 := by simp [bumpPred, ht0]
  have hc1 : bumpPred (keyIndSimPred S) c t 1 = c 1 := by simp [bumpPred, ht1]
  obtain ⟨tagged', hRel', hWf', hRoLe'⟩ := hShadow'
  refine
    { online_len := ?_
      fg_sess_le := ?_
      fg_shadow  := ⟨tagged', hRel', hWf', hc1 ▸ hRoLe'⟩
      raw_len    := hc1 ▸ hInv.raw_len
      raw_shadow := hInv.raw_shadow
      log_len    := hc1 ▸ hInv.log_len
      pows_len   := by rw [hc0]; exact Nat.le_succ_of_le hInv.pows_len }
  · have hProj : projVal keyIndStateTy (embedVal simTy (bSt', (fgL', sm.2.2))).1 = bSt' :=
      projVal_embedVal keyIndStateTy bSt'
    rw [hProj]
    exact hbSt'
  · rw [hc0]
    exact Nat.le_trans hSessLen (Nat.succ_le_succ hInv.fg_sess_le)

private theorem sim_letV {ι : Type} {T : OracleSpec ι} {I : Iface pqSig T}
    {Γ₁ Γ₂ : List PT} {σ τ₁ τ₂ : PT}
    {e₁ : Expr pqxdhOps Γ₁ σ} {e₂ : Expr pqxdhOps Γ₂ σ}
    {k₁ : Var (σ :: Γ₁) σ → Comp pqxdhOps I (σ :: Γ₁) τ₁}
    {k₂ : Var (σ :: Γ₂) σ → Comp pqxdhOps I (σ :: Γ₂) τ₂}
    {env₁ : Env Γ₁} {env₂ : Env Γ₂}
    {f : τ₁.denote → τ₂.denote} {P : τ₁.denote → Prop}
    (he : e₁.eval env₁ = e₂.eval env₂)
    (hk : ∀ a : σ.denote,
      f <$> (k₁ .zero).eval (.cons a env₁) = (k₂ .zero).eval (.cons a env₂) ∧
      ∀ r ∈ support ((k₁ .zero).eval (.cons a env₁)), P r) :
    f <$> (letV e₁ k₁).eval env₁ = (letV e₂ k₂).eval env₂ ∧
    ∀ r ∈ support ((letV e₁ k₁).eval env₁), P r := by
  simp only [letV_eval, he]
  exact hk (e₂.eval env₂)

private theorem sim_ite {ι : Type} {T : OracleSpec ι} {I : Iface pqSig T}
    {Γ₁ Γ₂ : List PT} {τ₁ τ₂ : PT}
    {b₁ : Expr pqxdhOps Γ₁ .bool} {b₂ : Expr pqxdhOps Γ₂ .bool}
    {t₁ e₁ : Comp pqxdhOps I Γ₁ τ₁} {t₂ e₂ : Comp pqxdhOps I Γ₂ τ₂}
    {env₁ : Env Γ₁} {env₂ : Env Γ₂}
    {f : τ₁.denote → τ₂.denote} {P : τ₁.denote → Prop}
    (hb : b₁.eval env₁ = b₂.eval env₂)
    (ht : f <$> t₁.eval env₁ = t₂.eval env₂ ∧ ∀ r ∈ support (t₁.eval env₁), P r)
    (he : f <$> e₁.eval env₁ = e₂.eval env₂ ∧ ∀ r ∈ support (e₁.eval env₁), P r) :
    f <$> (Comp.ite b₁ t₁ e₁).eval env₁ = (Comp.ite b₂ t₂ e₂).eval env₂ ∧
    ∀ r ∈ support ((Comp.ite b₁ t₁ e₁).eval env₁), P r := by
  simp only [Comp.eval, hb]
  cases b₂.eval env₂
  · exact he
  · exact ht

private theorem sim_caseOptV {ι : Type} {T : OracleSpec ι} {I : Iface pqSig T}
    {Γ₁ Γ₂ : List PT} {σ τ₁ τ₂ : PT}
    {o₁ : Expr pqxdhOps Γ₁ (.opt σ)} {o₂ : Expr pqxdhOps Γ₂ (.opt σ)}
    {n₁ : Comp pqxdhOps I Γ₁ τ₁} {n₂ : Comp pqxdhOps I Γ₂ τ₂}
    {s₁ : Var (σ :: Γ₁) σ → Comp pqxdhOps I (σ :: Γ₁) τ₁}
    {s₂ : Var (σ :: Γ₂) σ → Comp pqxdhOps I (σ :: Γ₂) τ₂}
    {env₁ : Env Γ₁} {env₂ : Env Γ₂}
    {f : τ₁.denote → τ₂.denote} {P : τ₁.denote → Prop}
    (ho : o₁.eval env₁ = o₂.eval env₂)
    (hn : f <$> n₁.eval env₁ = n₂.eval env₂ ∧ ∀ r ∈ support (n₁.eval env₁), P r)
    (hs : ∀ a : σ.denote,
      f <$> (s₁ .zero).eval (.cons a env₁) = (s₂ .zero).eval (.cons a env₂) ∧
      ∀ r ∈ support ((s₁ .zero).eval (.cons a env₁)), P r) :
    f <$> (caseOptV o₁ n₁ s₁).eval env₁ = (caseOptV o₂ n₂ s₂).eval env₂ ∧
    ∀ r ∈ support ((caseOptV o₁ n₁ s₁).eval env₁), P r := by
  simp only [caseOptV, Comp.eval, ho]
  cases o₂.eval env₂ with
  | none => exact hn
  | some a => exact hs a

private theorem sim_bindV {ι : Type} {T : OracleSpec ι} {I : Iface pqSig T}
    {Γ₁ Γ₂ : List PT} {σ τ₁ τ₂ : PT}
    {c₁ : Comp pqxdhOps I Γ₁ σ} {c₂ : Comp pqxdhOps I Γ₂ σ}
    {k₁ : Var (σ :: Γ₁) σ → Comp pqxdhOps I (σ :: Γ₁) τ₁}
    {k₂ : Var (σ :: Γ₂) σ → Comp pqxdhOps I (σ :: Γ₂) τ₂}
    {env₁ : Env Γ₁} {env₂ : Env Γ₂}
    {f : τ₁.denote → τ₂.denote} {P : τ₁.denote → Prop}
    (hc : c₁.eval env₁ = c₂.eval env₂)
    (hk : ∀ a : σ.denote,
      f <$> (k₁ .zero).eval (.cons a env₁) = (k₂ .zero).eval (.cons a env₂) ∧
      ∀ r ∈ support ((k₁ .zero).eval (.cons a env₁)), P r) :
    f <$> (bindV c₁ k₁).eval env₁ = (bindV c₂ k₂).eval env₂ ∧
    ∀ r ∈ support ((bindV c₁ k₁).eval env₁), P r := by
  simp only [bindV, Comp.eval]
  refine ⟨by rw [hc, map_bind]; exact bind_congr' rfl fun a => (hk a).1, fun r hr => ?_⟩
  rw [mem_support_bind_iff] at hr
  rcases hr with ⟨a, _, hr'⟩
  exact (hk a).2 r hr'

private theorem sim_bindV_proj {ι : Type} {T : OracleSpec ι} {I : Iface pqSig T}
    {Γ₁ Γ₂ : List PT} {σ₁ σ₂ τ₁ τ₂ : PT}
    {c₁ : Comp pqxdhOps I Γ₁ σ₁} {c₂ : Comp pqxdhOps I Γ₂ σ₂}
    {k₁ : Var (σ₁ :: Γ₁) σ₁ → Comp pqxdhOps I (σ₁ :: Γ₁) τ₁}
    {k₂ : Var (σ₂ :: Γ₂) σ₂ → Comp pqxdhOps I (σ₂ :: Γ₂) τ₂}
    {env₁ : Env Γ₁} {env₂ : Env Γ₂}
    {g : σ₁.denote → σ₂.denote} {Q : σ₁.denote → Prop}
    {f : τ₁.denote → τ₂.denote} {P : τ₁.denote → Prop}
    (hc : g <$> c₁.eval env₁ = c₂.eval env₂ ∧ ∀ a ∈ support (c₁.eval env₁), Q a)
    (hk : ∀ a : σ₁.denote,
      f <$> (k₁ .zero).eval (.cons a env₁) = (k₂ .zero).eval (.cons (g a) env₂) ∧
      (Q a → ∀ r ∈ support ((k₁ .zero).eval (.cons a env₁)), P r)) :
    f <$> (bindV c₁ k₁).eval env₁ = (bindV c₂ k₂).eval env₂ ∧
    ∀ r ∈ support ((bindV c₁ k₁).eval env₁), P r := by
  simp only [bindV, Comp.eval]
  refine ⟨?_, fun r hr => ?_⟩
  · calc f <$> (c₁.eval env₁ >>= fun a => (k₁ .zero).eval (.cons a env₁))
        = c₁.eval env₁ >>= fun a => f <$> (k₁ .zero).eval (.cons a env₁) := map_bind _ _ _
      _ = c₁.eval env₁ >>= fun a => (k₂ .zero).eval (.cons (g a) env₂) :=
          bind_congr' rfl fun a => (hk a).1
      _ = (g <$> c₁.eval env₁) >>= fun b => (k₂ .zero).eval (.cons b env₂) := by
          rw [map_eq_bind_pure_comp, bind_assoc]
          exact bind_congr' rfl fun a => by rw [Function.comp_apply, pure_bind]
      _ = c₂.eval env₂ >>= fun b => (k₂ .zero).eval (.cons b env₂) := by rw [hc.1]
  · rw [mem_support_bind_iff] at hr
    rcases hr with ⟨a, ha, hr'⟩
    exact (hk a).2 (hc.2 a ha) r hr'

private theorem sim_bindV_cond {ι : Type} {T : OracleSpec ι} {I : Iface pqSig T}
    {Γ₁ Γ₂ : List PT} {σ τ₁ τ₂ : PT} {Q : Prop}
    {c₁ : Comp pqxdhOps I Γ₁ σ} {c₂ : Comp pqxdhOps I Γ₂ σ}
    {k₁ : Var (σ :: Γ₁) σ → Comp pqxdhOps I (σ :: Γ₁) τ₁}
    {k₂ : Var (σ :: Γ₂) σ → Comp pqxdhOps I (σ :: Γ₂) τ₂}
    {env₁ : Env Γ₁} {env₂ : Env Γ₂}
    {f : τ₁.denote → τ₂.denote} {P : τ₁.denote → Prop}
    (hc : c₁.eval env₁ = c₂.eval env₂)
    (hk : ∀ a : σ.denote,
      f <$> (k₁ .zero).eval (.cons a env₁) = (k₂ .zero).eval (.cons a env₂) ∧
      (Q → ∀ r ∈ support ((k₁ .zero).eval (.cons a env₁)), P r)) :
    f <$> (bindV c₁ k₁).eval env₁ = (bindV c₂ k₂).eval env₂ ∧
    (Q → ∀ r ∈ support ((bindV c₁ k₁).eval env₁), P r) := by
  simp only [bindV, Comp.eval]
  refine ⟨by rw [hc, map_bind]; exact bind_congr' rfl fun a => (hk a).1, fun hQ r hr => ?_⟩
  rw [mem_support_bind_iff] at hr
  rcases hr with ⟨a, _, hr'⟩
  exact (hk a).2 hQ r hr'

private theorem sim_letV_cond {ι : Type} {T : OracleSpec ι} {I : Iface pqSig T}
    {Γ₁ Γ₂ : List PT} {σ τ₁ τ₂ : PT} {Q : Prop}
    {e₁ : Expr pqxdhOps Γ₁ σ} {e₂ : Expr pqxdhOps Γ₂ σ}
    {k₁ : Var (σ :: Γ₁) σ → Comp pqxdhOps I (σ :: Γ₁) τ₁}
    {k₂ : Var (σ :: Γ₂) σ → Comp pqxdhOps I (σ :: Γ₂) τ₂}
    {env₁ : Env Γ₁} {env₂ : Env Γ₂}
    {f : τ₁.denote → τ₂.denote} {P : τ₁.denote → Prop}
    (he : e₁.eval env₁ = e₂.eval env₂)
    (hk : ∀ a : σ.denote, a = e₁.eval env₁ →
      f <$> (k₁ .zero).eval (.cons a env₁) = (k₂ .zero).eval (.cons a env₂) ∧
      (Q → ∀ r ∈ support ((k₁ .zero).eval (.cons a env₁)), P r)) :
    f <$> (letV e₁ k₁).eval env₁ = (letV e₂ k₂).eval env₂ ∧
    (Q → ∀ r ∈ support ((letV e₁ k₁).eval env₁), P r) := by
  simp only [letV_eval]
  rw [← he]
  exact hk (e₁.eval env₁) rfl

private theorem sim_letV_lhs_cond {ι : Type} {T : OracleSpec ι} {I : Iface pqSig T}
    {Γ₁ Γ₂ : List PT} {σ τ₁ τ₂ : PT} {Q : Prop}
    {e₁ : Expr pqxdhOps Γ₁ σ}
    {k₁ : Var (σ :: Γ₁) σ → Comp pqxdhOps I (σ :: Γ₁) τ₁}
    {c₂ : Comp pqxdhOps I Γ₂ τ₂}
    {env₁ : Env Γ₁} {env₂ : Env Γ₂}
    {f : τ₁.denote → τ₂.denote} {P : τ₁.denote → Prop}
    (hk : ∀ a : σ.denote, a = e₁.eval env₁ →
      f <$> (k₁ .zero).eval (.cons a env₁) = c₂.eval env₂ ∧
      (Q → ∀ r ∈ support ((k₁ .zero).eval (.cons a env₁)), P r)) :
    f <$> (letV e₁ k₁).eval env₁ = c₂.eval env₂ ∧
    (Q → ∀ r ∈ support ((letV e₁ k₁).eval env₁), P r) := by
  simp only [letV_eval]
  exact hk (e₁.eval env₁) rfl

private theorem gdhSimInv_online_unchanged {S : Setup} {b : QueryBudget}
    {c : Fin 3 → ℕ} {t : KeyIndQuery S} {sK : simShadowAtomicTy.denote}
    (ht0 : keyIndSimPred S 0 t = true) (ht1 : keyIndSimPred S 1 t = false)
    (hInv : GdhSimInv S b c sK) :
    GdhSimInv S b (bumpPred (keyIndSimPred S) c t) sK :=
  GdhSimInv_bump_online (ht0.symm ▸ (rfl : true = true))
    (fun h => Bool.noConfusion (ht1 ▸ h)) hInv

private def fgPatchPost (S : Setup) (b : QueryBudget) (c1 : ℕ)
    (fgShVal : fgSessCtrTy.denote) (fgShFull : fgShadowAtomicTy.denote)
    (r : (Ty.prod drKeyTy (.prod (.list fgPatchEntryTy) fgSessCtrTy)).denote) : Prop :=
  (embedVal (.list seqFgEntryTy) r.2.2.1).length ≤
    (embedVal (.list seqFgEntryTy) fgShVal.1).length + 1 ∧
  ∃ tagged' : List (TaggedEntry Bytes FgEntryA),
    ShadowRelB192 (drKeyT (ℓ := 0) (Pt := Empty)) b.q_total
      (keyIndKFuelsOfBudget S b).kAvl fgEntryDk
      (embedVal (.list fgPatchEntryTy) r.2.1)
      tagged' fgShFull.2.2.1 (embedVal (.list seqFgEntryTy) r.2.2.1) r.2.2.2 ∧
    (∀ te ∈ tagged', ∀ sec, te.tag = .ro sec → RoFgEntryWf sec te.entry) ∧
    (roEntriesOf fgEntryDk tagged').length ≤ c1

private theorem sim_fgPatch {S : Setup} {b : QueryBudget} {c : Fin 3 → ℕ}
    {Γ₁ Γ₂ Γ₃ Γ₄ Γ₅ Δ₁ Γ₁' Γ₂' Γ₃' Γ₄' Γ₅' Δ₂ : List PT}
    [Ext Γ₁ Δ₁] [Ext Γ₂ Δ₁] [Ext Γ₃ Δ₁] [Ext Γ₄ Δ₁] [Ext Γ₅ Δ₁]
    [Ext Γ₁' Δ₂] [Ext Γ₂' Δ₂] [Ext Γ₃' Δ₂] [Ext Γ₄' Δ₂] [Ext Γ₅' Δ₂]
    {τ₁ τ₂ : PT}
    {pos1₁ : Var Γ₁ fgPosTy} {pos2₁ : Var Γ₂ fgPosTy} {pos3₁ : Var Γ₃ fgPosTy}
    {pos4₁ : Var Γ₄ (.opt fgPosTy)} {ss₁ : Var Γ₅ (B 32)}
    {fgL₁ : Expr pqxdhOps Δ₁ (.list fgPatchEntryTy)}
    {fgSess₁ : Expr pqxdhOps Δ₁ (.list seqFgEntryTy)}
    {ctr₁ : Expr pqxdhOps Δ₁ .nat}
    {pos1₂ : Var Γ₁' fgPosTy} {pos2₂ : Var Γ₂' fgPosTy} {pos3₂ : Var Γ₃' fgPosTy}
    {pos4₂ : Var Γ₄' (.opt fgPosTy)} {ss₂ : Var Γ₅' (B 32)}
    {fgL₂ : Expr pqxdhOps Δ₂ (.list fgPatchEntryTy)}
    {k₁ : Var (Ty.prod drKeyTy (.prod (.list fgPatchEntryTy) fgSessCtrTy) :: Δ₁)
            (Ty.prod drKeyTy (.prod (.list fgPatchEntryTy) fgSessCtrTy)) →
          Comp pqxdhOps pqGapDhIface
            (Ty.prod drKeyTy (.prod (.list fgPatchEntryTy) fgSessCtrTy) :: Δ₁) τ₁}
    {k₂ : Var (Ty.prod drKeyTy (.list fgPatchEntryTy) :: Δ₂)
            (Ty.prod drKeyTy (.list fgPatchEntryTy)) →
          Comp pqxdhOps pqGapDhIface
            (Ty.prod drKeyTy (.list fgPatchEntryTy) :: Δ₂) τ₂}
    {env₁ : Env Δ₁} {env₂ : Env Δ₂}
    {f : τ₁.denote → τ₂.denote} {P : τ₁.denote → Prop}
    (smVal : simTy.denote) (fgShVal : fgSessCtrTy.denote) (fgShFull : fgShadowAtomicTy.denote)
    (hp1 : env₁.get (Ext.wk pos1₁) = env₂.get (Ext.wk pos1₂))
    (hp2 : env₁.get (Ext.wk pos2₁) = env₂.get (Ext.wk pos2₂))
    (hp3 : env₁.get (Ext.wk pos3₁) = env₂.get (Ext.wk pos3₂))
    (hp4 : env₁.get (Ext.wk pos4₁) = env₂.get (Ext.wk pos4₂))
    (hss : env₁.get (Ext.wk ss₁) = env₂.get (Ext.wk ss₂))
    (hL1 : fgL₁.eval env₁ = smVal.2.1)
    (hL2 : fgL₂.eval env₂ = smVal.2.1)
    (hSess : fgSess₁.eval env₁ = fgShVal.1)
    (hCtr : ctr₁.eval env₁ = fgShVal.2)
    (hB : ∀ j, c j ≤ keyIndSimBounds b j)
    (hCtrRoom : fgShVal.2 + 1 ≤ b.q_total)
    (hInv : GdhSimInv S b c
      (embedVal simTy smVal,
        ((embedVal fgSessCtrTy fgShVal).1, ((embedVal fgSessCtrTy fgShVal).2, fgShFull.2.2))))
    (hk : ∀ patchR : (Ty.prod drKeyTy (.prod (.list fgPatchEntryTy) fgSessCtrTy)).denote,
      f <$> (k₁ .zero).eval (.cons patchR env₁) =
        (k₂ .zero).eval (.cons ((patchR.1, patchR.2.1) : (Ty.prod drKeyTy (.list fgPatchEntryTy)).denote) env₂) ∧
      (fgPatchPost S b (c 1) fgShVal fgShFull patchR →
        ∀ r ∈ support ((k₁ .zero).eval (.cons patchR env₁)), P r)) :
    f <$>
      (bindV (fgPatchShadowC (keyIndKFuelsOfBudget S b).kFg
        pos1₁ pos2₁ pos3₁ pos4₁ ss₁ fgL₁ fgSess₁ ctr₁) k₁).eval env₁ =
      (bindV (fgPatchC b.q_total pos1₂ pos2₂ pos3₂ pos4₂ ss₂ fgL₂) k₂).eval env₂ ∧
    ∀ r ∈ support
      ((bindV (fgPatchShadowC (keyIndKFuelsOfBudget S b).kFg
        pos1₁ pos2₁ pos3₁ pos4₁ ss₁ fgL₁ fgSess₁ ctr₁) k₁).eval env₁), P r := by
  have hLenK : (fgL₁.eval env₁).length ≤ (keyIndKFuelsOfBudget S b).kFg := by
    rw [hL1]; simpa [embedVal] using hInv.fgL_length_le_kFg hB
  have hLenQ : (fgL₁.eval env₁).length ≤ b.q_total := by
    rw [hL1]; simpa [embedVal] using hInv.fgL_length_le_q_total hB
  have hfg := fgPatchShadowC_sim (S := S) (b := b)
    pos1₁ pos2₁ pos3₁ pos4₁ ss₁ fgL₁ fgSess₁ ctr₁
    pos1₂ pos2₂ pos3₂ pos4₂ ss₂ fgL₂ env₁ env₂ fgShFull.2.2.1
    hp1 hp2 hp3 hp4 hss (by rw [hL1, hL2]) hLenK hLenQ
    (by rw [hCtr]; exact hCtrRoom)
    (by rw [hL1, hSess, hCtr]; exact hInv.fg_shadow)
  exact sim_bindV_proj
    ⟨hfg.1, fun r hr => by simpa [fgPatchPost, hSess] using hfg.2 r hr⟩ hk

private theorem gdhSimInv_online_cons_sess {S : Setup} {b : QueryBudget}
    {c : Fin 3 → ℕ} {t : KeyIndQuery S}
    (smVal : simTy.denote) (fgShVal : fgSessCtrTy.denote)
    (patchR : (Ty.prod drKeyTy (.prod (.list fgPatchEntryTy) fgSessCtrTy)).denote)
    (fgShFull : fgShadowAtomicTy.denote)
    (sVal : keyIndSessionEntryTy.denote)
    (ht0 : keyIndSimPred S 0 t = true) (ht1 : keyIndSimPred S 1 t = false)
    (hInv : GdhSimInv S b c
      (embedVal simTy smVal,
        ((embedVal fgSessCtrTy fgShVal).1, ((embedVal fgSessCtrTy fgShVal).2, fgShFull.2.2))))
    (hPatch : fgPatchPost S b (c 1) fgShVal fgShFull patchR) :
    let bSt := smVal.1
    let bSt' : keyIndStateTy.denote :=
      (bSt.1, (bSt.2.1, (bSt.2.2.1, (bSt.2.2.2.1, (sVal :: bSt.2.2.2.2.1, bSt.2.2.2.2.2)))))
    let sm' : simTy.denote :=
      (bSt', (patchR.2.1, (smVal.2.2.1, (smVal.2.2.2.1, smVal.2.2.2.2))))
    GdhSimInv S b (bumpPred (keyIndSimPred S) c t)
      (embedVal simTy sm',
        ((embedVal fgSessCtrTy patchR.2.2).1, ((embedVal fgSessCtrTy patchR.2.2).2, fgShFull.2.2))) := by
  intro bSt bSt' sm'
  have hOn : BaseOnlineLenInv c bSt := by
    have h := hInv.online_len
    change BaseOnlineLenInv c (projVal keyIndStateTy (embedVal keyIndStateTy bSt)) at h
    rwa [projVal_embedVal] at h
  exact GdhSimInv_after_fgPatch smVal fgShVal fgShFull bSt' patchR.2.1 patchR.2.2
    (ht0.symm ▸ (rfl : true = true)) (fun h => Bool.noConfusion (ht1 ▸ h)) hInv
    (BaseOnlineLenInv_initiate sVal (ht0.symm ▸ (rfl : true = true)) hOn) hPatch.1 hPatch.2

/-- Arm-level simulation and `GdhSimInv` preservation for `initiateGdh2ShadowB` vs `initiateGdh2B`. -/
theorem initiateGdh2ShadowB_sim (S : Setup) (b : QueryBudget) (hasOpk : Bool)
    {Γ₁a Γ₂a Γ₃a Γ₄a Γ₅a Δ₁ Γ₁b Γ₂b Γ₃b Γ₄b Δ₂ : List PT}
    [Ext Γ₁a Δ₁] [Ext Γ₂a Δ₁] [Ext Γ₃a Δ₁] [Ext Γ₄a Δ₁] [Ext Γ₅a Δ₁]
    [Ext Γ₁b Δ₂] [Ext Γ₂b Δ₂] [Ext Γ₃b Δ₂] [Ext Γ₄b Δ₂]
    (pa₁ : Var Γ₁a params2Ty) (sm₁ : Var Γ₂a simTy) (bSt₁ : Var Γ₃a keyIndStateTy)
    (fgSh₁ : Var Γ₅a fgSessCtrTy) (x₁ : Var Γ₄a initQTy)
    (pa₂ : Var Γ₁b params2Ty) (sm₂ : Var Γ₂b simTy) (bSt₂ : Var Γ₃b keyIndStateTy)
    (x₂ : Var Γ₄b initQTy)
    (env₁ : Env Δ₁) (env₂ : Env Δ₂)
    (c : Fin 3 → ℕ) (t : KeyIndQuery S)
    (fgShFull : fgShadowAtomicTy.denote)
    (hpa : (v pa₁).eval env₁ = (v pa₂).eval env₂)
    (hsm : (v sm₁).eval env₁ = (v sm₂).eval env₂)
    (hbSt : (v bSt₁).eval env₁ = ((v sm₁).eval env₁).1)
    (hbSt₂ : (v bSt₂).eval env₂ = ((v sm₂).eval env₂).1)
    (hx : (v x₁).eval env₁ = (v x₂).eval env₂)
    (ht0 : keyIndSimPred S 0 t = true)
    (ht1 : keyIndSimPred S 1 t = false)
    (hB : ∀ j, c j ≤ keyIndSimBounds b j)
    (hRoom : ∀ j, keyIndSimPred S j t → c j + 1 ≤ keyIndSimBounds b j)
    (hInv : GdhSimInv S b c
      (embedVal simTy ((v sm₁).eval env₁),
        ((embedVal fgSessCtrTy ((v fgSh₁).eval env₁)).1,
          ((embedVal fgSessCtrTy ((v fgSh₁).eval env₁)).2, fgShFull.2.2)))) :
    (fun r => (r.1, r.2.1)) <$>
      (initiateGdh2ShadowB S (keyIndKFuelsOfBudget S b) pa₁ sm₁ bSt₁ fgSh₁ hasOpk x₁).eval env₁ =
      (_root_.SignalPqxdh.Security.ReductionDsl.KeyInd.initiateGdh2B
        S b.q_total pa₂ sm₂ bSt₂ hasOpk x₂).eval env₂ ∧
    ∀ r ∈ support
      ((initiateGdh2ShadowB S (keyIndKFuelsOfBudget S b) pa₁ sm₁ bSt₁ fgSh₁ hasOpk x₁).eval env₁),
      GdhSimInv S b (bumpPred (keyIndSimPred S) c t)
        (embedVal simTy r.2.1,
          ((embedVal fgSessCtrTy r.2.2).1, ((embedVal fgSessCtrTy r.2.2).2, fgShFull.2.2))) := by
  have hbStEq : (v bSt₁).eval env₁ = (v bSt₂).eval env₂ := by rw [hbSt, hbSt₂, hsm]
  have hOn : BaseOnlineLenInv c ((v bSt₁).eval env₁) := by
    have h := hInv.online_len
    change BaseOnlineLenInv c (projVal keyIndStateTy (embedVal keyIndStateTy ((v sm₁).eval env₁).1)) at h
    rwa [projVal_embedVal, ← hbSt] at h
  have hc0K : c 0 ≤ (keyIndKFuelsOfBudget S b).kOn := by
    simpa [keyIndKFuelsOfBudget, keyIndSimBounds] using hB 0
  have hkOnLe : (keyIndKFuelsOfBudget S b).kOn ≤ b.q_total := Nat.min_le_right _ _
  have hPowsLe : ((v sm₁).eval env₁).2.2.2.2.length ≤ (keyIndKFuelsOfBudget S b).kOn := by
    simpa [embedVal] using hInv.smPows_length_le_kOn hB
  have hCtrRoom : ((v fgSh₁).eval env₁).2 + 1 ≤ b.q_total :=
    hInv.ctr_add_one_le_q_total hRoom
  let proj : (Ty.prod keyIndRespTy (.prod simTy fgSessCtrTy)).denote →
      (Ty.prod keyIndRespTy simTy).denote := fun r => (r.1, r.2.1)
  have hAbort : ∀ {Γa Γb : List PT} {e₁ : Expr pqxdhOps Γa keyIndRespTy}
      {e₂ : Expr pqxdhOps Γb keyIndRespTy} {ρ₁ : Env Γa} {ρ₂ : Env Γb}
      {smV₁ : Expr pqxdhOps Γa simTy} {fgShV₁ : Expr pqxdhOps Γa fgSessCtrTy}
      {smV₂ : Expr pqxdhOps Γb simTy},
      e₁.eval ρ₁ = e₂.eval ρ₂ →
      smV₁.eval ρ₁ = (v sm₁).eval env₁ →
      fgShV₁.eval ρ₁ = (v fgSh₁).eval env₁ →
      smV₂.eval ρ₂ = (v sm₂).eval env₂ →
      proj <$>
        (Comp.ret (.pair e₁ (.pair smV₁ fgShV₁)) : Comp pqxdhOps pqGapDhIface _ _).eval ρ₁ =
        (Comp.ret (.pair e₂ smV₂) : Comp pqxdhOps pqGapDhIface _ _).eval ρ₂ ∧
      ∀ r ∈ support ((Comp.ret (.pair e₁ (.pair smV₁ fgShV₁)) : Comp pqxdhOps pqGapDhIface _ _).eval ρ₁),
        GdhSimInv S b (bumpPred (keyIndSimPred S) c t)
          (embedVal simTy r.2.1,
            ((embedVal fgSessCtrTy r.2.2).1, ((embedVal fgSessCtrTy r.2.2).2, fgShFull.2.2))) := by
    intro _ _ _ _ _ _ _ _ _ he hsm1 hfg1 hsm2
    refine ⟨by dsimp only [proj]; simp [Comp.eval, Expr.eval, map_pure, he, hsm1, hsm2, hsm],
      fun r hr => ?_⟩
    simp only [Comp.eval, Expr.eval, hsm1, hfg1, mem_support_pure_iff] at hr
    subst hr
    exact gdhSimInv_online_unchanged ht0 ht1 hInv
  change proj <$> _ = _ ∧ _
  unfold initiateGdh2ShadowB _root_.SignalPqxdh.Security.ReductionDsl.KeyInd.initiateGdh2B
  refine sim_letV (congrArg (fun p => p.2.2) hx) fun bu => ?_
  refine sim_ite
    (by cases hasOpk <;> simp [isSomeE, buOpkB, Expr.eval])
    (hAbort (by simp [_root_.SignalPqxdh.Security.ReductionDsl.KeyInd.rNone, Expr.eval])
      rfl rfl rfl) ?_
  refine sim_letV (by cases hasOpk <;>
    simp [_root_.SignalPqxdh.Security.ReductionDsl.KeyInd.initSidE, Expr.eval, hx]) fun sid => ?_
  refine sim_ite (eAny_congr_le _ _ _ _ _ _
      (by simp [Expr.eval, hbStEq])
      (by simpa [stSess, stSessList, Expr.eval] using Nat.le_trans hOn.sess_le hc0K) hkOnLe
      fun s => by simp [_root_.SignalPqxdh.Security.ReductionDsl.KeyInd.sidEq_eval, seSid, Expr.eval])
    (hAbort (by simp [_root_.SignalPqxdh.Security.ReductionDsl.KeyInd.rNone, Expr.eval])
      rfl rfl rfl) ?_
  refine sim_caseOptV (eFind_congr_le _ _ _ _ _ _
      (by simp [Expr.eval, hbStEq])
      (by simpa [stPrin, stPrinList, Expr.eval] using Nat.le_trans hOn.prin_le hc0K) hkOnLe
      fun p => by simp [natEq, Expr.eval, hx]; try rfl)
    (hAbort (by simp [_root_.SignalPqxdh.Security.ReductionDsl.KeyInd.rNone, Expr.eval])
      rfl rfl rfl) fun ue => ?_
  refine sim_bindV (liftBase_eval_congr _ _ _ _
      (koskBundleOkPowsC_sim S _ _ _ _ _ _ _ _
        (by simp [hbStEq]) (by simp [smPows, Expr.eval, hsm]) rfl
        (by simpa using hOn) hc0K (by simpa [smPows, Expr.eval] using hPowsLe) hkOnLe)) fun ok => ?_
  refine sim_ite (by simp [Expr.eval])
    (hAbort (by simp [_root_.SignalPqxdh.Security.ReductionDsl.KeyInd.rNone, Expr.eval])
      rfl rfl rfl) ?_
  refine sim_letV ?_ fun isTE => ?_
  · simp only [_root_.SignalPqxdh.Security.ReductionDsl.KeyInd.pa2DhFlag,
      _root_.SignalPqxdh.Security.ReductionDsl.KeyInd.pa2EphTarget,
      _root_.SignalPqxdh.Security.ReductionDsl.KeyInd.ephSidMatchesE,
      eCaseOpt, _root_.SignalPqxdh.Security.ReductionDsl.KeyInd.eCaseSum,
      nat2Eq, natEq, Expr.eval, v_eval_cons, v_zero_eval, hpa]
    try rfl
  · refine sim_bindV (liftBase_eval_congr _ _ _ _ (sBytes32_eval_const _ _)) fun ekSkRaw => ?_
    refine sim_bindV (liftBase_eval_congr _ _ _ _ (sBytes32_eval_const _ _)) fun coins => ?_
    refine sim_bindV (liftBase_eval_congr _ _ _ _
      (resolveSigPkC_sim S _ _ _ _ _ _ (by simp [hbStEq]) (by simp [Expr.eval])
        (by simpa using Nat.le_trans hOn.prin_le hc0K) hkOnLe)) fun sigPk => ?_
    refine sim_bindV (liftBase_eval_congr _ _ _ _
      (qSigVerify_eval_congr 33 _ _ _ _
        (by simp [_root_.SignalPqxdh.Security.ReductionDsl.KeyInd.encEC_eval,
          buSpkB, Expr.eval]))) fun v1 => ?_
    refine sim_bindV (liftBase_eval_congr _ _ _ _
      (qSigVerify_eval_congr 1569 _ _ _ _
        (by simp [_root_.SignalPqxdh.Security.ReductionDsl.KeyInd.encKEM_eval,
          buPqspkB, Expr.eval]))) fun v2 => ?_
    refine sim_ite (by simp [Expr.eval])
      (hAbort (by simp [_root_.SignalPqxdh.Security.ReductionDsl.KeyInd.rNone, Expr.eval])
        rfl rfl rfl) ?_
    refine sim_bindV (liftBase_eval_congr _ _ _ _
      (qKemEncaps_eval_congr _ _ _ _ (by simp [Expr.eval]))) fun krOpt => ?_
    refine sim_caseOptV (by simp)
      (hAbort (by simp [_root_.SignalPqxdh.Security.ReductionDsl.KeyInd.rNone, Expr.eval])
        rfl rfl rfl) fun kr => ?_
    refine sim_bindV (liftBase_eval_congr _ _ _ _
      (qX25519Base_eval_congr _ _ _ _ (by simp))) fun ekPkRaw => ?_
    refine sim_letV
      (by simp [_root_.SignalPqxdh.Security.ReductionDsl.KeyInd.litB_eval, Expr.eval]; try rfl) fun ekSk => ?_
    refine sim_letV
      (by simp [_root_.SignalPqxdh.Security.ReductionDsl.KeyInd.pa2U, Expr.eval, hpa]; try rfl) fun ekPk => ?_
    refine sim_bindV (liftBase_eval_congr _ _ _ _
      (lookupSpkSkC_sim S _ _ _ _ _ _ _ _
        (by simp [hbStEq]) (by simp [smPows, Expr.eval, hsm]) (by simp [Expr.eval])
        (by simpa using Nat.le_trans hOn.spks_le hc0K)
        (by simpa [smPows, Expr.eval] using hPowsLe) hkOnLe)) fun spkSk => ?_
    refine sim_bindV (computePosC_congr _ _ _ _ _ _ _ _ _ _
      (by simp [Expr.eval]) (by simp)
      (by simp [Expr.eval]) (by simp [Expr.eval])) fun p1 => ?_
    refine sim_bindV (computePosC_congr _ _ _ _ _ _ _ _ _ _
      (by simp) (by simp [_root_.SignalPqxdh.Security.ReductionDsl.KeyInd.litB_eval])
      (by simp) (by simp [Expr.eval])) fun p2 => ?_
    refine sim_bindV (computePosC_congr _ _ _ _ _ _ _ _ _ _
      (by simp) (by simp [_root_.SignalPqxdh.Security.ReductionDsl.KeyInd.litB_eval])
      (by simp) (by simp [Expr.eval])) fun p3 => ?_
    refine sim_bindV (computeOptPosInitC_congr _ _ _ _ _ _ _ _
      (by simp) (by simp) (by simp [Expr.eval])) fun p4 => ?_
    refine sim_letV (by simp [Expr.eval]) fun ss => ?_
    refine sim_fgPatch ((v sm₁).eval env₁) ((v fgSh₁).eval env₁) fgShFull
      rfl rfl rfl rfl rfl
      (by simp [smFgL, Expr.eval]) (by simp [smFgL, Expr.eval, ← hsm])
      (by simp [Expr.eval]) (by simp [Expr.eval])
      hB hCtrRoom hInv fun patchR => ?_
    refine sim_letV_cond (by simp [Expr.eval]) fun dkReal _ => ?_
    refine sim_letV_cond (by simp [Expr.eval]) fun fgL' hfgL' => ?_
    refine sim_letV_lhs_cond fun fgSh' hfgSh' => ?_
    refine sim_letV_cond
      (by simp [_root_.SignalPqxdh.Security.ReductionDsl.KeyInd.optFst,
        eCaseOpt, buOpkB, Expr.eval]; try rfl) fun hdr _ => ?_
    refine sim_bindV_cond (liftBase_eval_congr _ _ _ _
      (honestPeerC_sim S _ _ _ _ _ _ (by simp [hbStEq]) (by simp [Expr.eval])
        (by simpa using Nat.le_trans hOn.prin_le hc0K) hkOnLe)) fun hp => ?_
    refine sim_bindV_cond (liftBase_eval_congr _ _ _ _
      (checkProvC_sim S _ _ _ _ _ _ (by simp [hbStEq]) (by simp)
        (by simpa using hOn) hc0K hkOnLe)) fun prov => ?_
    refine sim_letV_cond
      (by simp [_root_.SignalPqxdh.Security.ReductionDsl.KeyInd.optSnd,
        eCaseOpt, isSomeE, buOpkB, Expr.eval]; try rfl) fun sInit _ => ?_
    refine sim_bindV_cond (chooseInitRandC_sim S _ _ _ _ _ _
      (by simp [hbStEq]) (by simp)
      (by simpa using Nat.le_trans hOn.resps_le hc0K) hkOnLe) fun dkRand => ?_
    refine sim_letV_cond
      (by simp [smUpd, _root_.SignalPqxdh.Security.ReductionDsl.KeyInd.smMk,
        stUpd, _root_.SignalPqxdh.Security.ReductionDsl.KeyInd.stSecb, stPrin, stSpks, stOpks,
        stSess, stResps, _root_.SignalPqxdh.Security.ReductionDsl.KeyInd.stUsedO,
        _root_.SignalPqxdh.Security.ReductionDsl.KeyInd.stUsedN,
        _root_.SignalPqxdh.Security.ReductionDsl.KeyInd.stKyb,
        _root_.SignalPqxdh.Security.ReductionDsl.KeyInd.stRo, stAdv,
        _root_.SignalPqxdh.Security.ReductionDsl.KeyInd.smRaw,
        _root_.SignalPqxdh.Security.ReductionDsl.KeyInd.smLog, smPows,
        seUpd, Expr.eval, hbSt, hbSt₂, hsm]) fun smV hsmV => ?_
    refine sim_bindV_cond (liftBase_eval_congr _ _ _ _
      (findHonestC_sim S _ _ _ _ _ _ (by simp [hbStEq]) (by simp [Expr.eval])
        (by simpa using Nat.le_trans hOn.prin_le hc0K) hkOnLe)) fun fh => ?_
    refine ⟨?_, fun hPatch r hr => ?_⟩
    · cases fh <;>
        dsimp only [proj] <;>
        simp [Comp.eval, eCaseOpt, map_pure,
          _root_.SignalPqxdh.Security.ReductionDsl.KeyInd.rInitUnfresh,
          _root_.SignalPqxdh.Security.ReductionDsl.KeyInd.rHdr, Expr.eval]
    · cases fh <;>
      · simp only [Comp.eval, eCaseOpt, Expr.eval, v_eval_cons, v_zero_eval,
          mem_support_pure_iff] at hr
        subst hr
        rw [hsmV, hfgSh']
        simpa [smUpd, _root_.SignalPqxdh.Security.ReductionDsl.KeyInd.smMk,
          stUpd, _root_.SignalPqxdh.Security.ReductionDsl.KeyInd.stSecb, stPrin, stSpks, stOpks,
          stSess, stResps, _root_.SignalPqxdh.Security.ReductionDsl.KeyInd.stUsedO,
          _root_.SignalPqxdh.Security.ReductionDsl.KeyInd.stUsedN,
          _root_.SignalPqxdh.Security.ReductionDsl.KeyInd.stKyb,
          _root_.SignalPqxdh.Security.ReductionDsl.KeyInd.stRo, stAdv,
          _root_.SignalPqxdh.Security.ReductionDsl.KeyInd.smRaw,
          _root_.SignalPqxdh.Security.ReductionDsl.KeyInd.smLog, smPows,
          Expr.eval, hbSt, hfgL'] using
          gdhSimInv_online_cons_sess ((v sm₁).eval env₁) ((v fgSh₁).eval env₁) patchR
            fgShFull _ ht0 ht1 hInv hPatch

/-- Arm-level simulation and `GdhSimInv` preservation for `initiateGdhShadowB` vs `initiateGdhB`. -/
theorem initiateGdhShadowB_sim (S : Setup) (b : QueryBudget) (hasOpk : Bool)
    {Γ₁a Γ₂a Γ₃a Γ₄a Γ₅a Δ₁ Γ₁b Γ₂b Γ₃b Γ₄b Δ₂ : List PT}
    [Ext Γ₁a Δ₁] [Ext Γ₂a Δ₁] [Ext Γ₃a Δ₁] [Ext Γ₄a Δ₁] [Ext Γ₅a Δ₁]
    [Ext Γ₁b Δ₂] [Ext Γ₂b Δ₂] [Ext Γ₃b Δ₂] [Ext Γ₄b Δ₂]
    (pa₁ : Var Γ₁a paramsTy) (sm₁ : Var Γ₂a simTy) (bSt₁ : Var Γ₃a keyIndStateTy)
    (fgSh₁ : Var Γ₅a fgSessCtrTy) (x₁ : Var Γ₄a initQTy)
    (pa₂ : Var Γ₁b paramsTy) (sm₂ : Var Γ₂b simTy) (bSt₂ : Var Γ₃b keyIndStateTy)
    (x₂ : Var Γ₄b initQTy)
    (env₁ : Env Δ₁) (env₂ : Env Δ₂)
    (c : Fin 3 → ℕ) (t : KeyIndQuery S)
    (fgShFull : fgShadowAtomicTy.denote)
    (hpa : (v pa₁).eval env₁ = (v pa₂).eval env₂)
    (hsm : (v sm₁).eval env₁ = (v sm₂).eval env₂)
    (hbSt : (v bSt₁).eval env₁ = ((v sm₁).eval env₁).1)
    (hbSt₂ : (v bSt₂).eval env₂ = ((v sm₂).eval env₂).1)
    (hx : (v x₁).eval env₁ = (v x₂).eval env₂)
    (ht0 : keyIndSimPred S 0 t = true)
    (ht1 : keyIndSimPred S 1 t = false)
    (hB : ∀ j, c j ≤ keyIndSimBounds b j)
    (hRoom : ∀ j, keyIndSimPred S j t → c j + 1 ≤ keyIndSimBounds b j)
    (hInv : GdhSimInv S b c
      (embedVal simTy ((v sm₁).eval env₁),
        ((embedVal fgSessCtrTy ((v fgSh₁).eval env₁)).1,
          ((embedVal fgSessCtrTy ((v fgSh₁).eval env₁)).2, fgShFull.2.2)))) :
    (fun r => (fun x => x) (r.1, r.2.1)) <$>
      (initiateGdhShadowB S (keyIndKFuelsOfBudget S b) pa₁ sm₁ bSt₁ fgSh₁ hasOpk x₁).eval env₁ =
      (_root_.SignalPqxdh.Security.ReductionDsl.KeyInd.initiateGdhB
        S b.q_total pa₂ sm₂ bSt₂ hasOpk x₂).eval env₂ ∧
    ∀ r ∈ support
      ((initiateGdhShadowB S (keyIndKFuelsOfBudget S b) pa₁ sm₁ bSt₁ fgSh₁ hasOpk x₁).eval env₁),
      GdhSimInv S b (bumpPred (keyIndSimPred S) c t)
        (embedVal simTy r.2.1,
          ((embedVal fgSessCtrTy r.2.2).1, ((embedVal fgSessCtrTy r.2.2).2, fgShFull.2.2))) := by
  have hbStEq : (v bSt₁).eval env₁ = (v bSt₂).eval env₂ := by rw [hbSt, hbSt₂, hsm]
  have hOn : BaseOnlineLenInv c ((v bSt₁).eval env₁) := by
    have h := hInv.online_len
    change BaseOnlineLenInv c (projVal keyIndStateTy (embedVal keyIndStateTy ((v sm₁).eval env₁).1)) at h
    rwa [projVal_embedVal, ← hbSt] at h
  have hc0K : c 0 ≤ (keyIndKFuelsOfBudget S b).kOn := by
    simpa [keyIndKFuelsOfBudget, keyIndSimBounds] using hB 0
  have hkOnLe : (keyIndKFuelsOfBudget S b).kOn ≤ b.q_total := Nat.min_le_right _ _
  have hPowsLe : ((v sm₁).eval env₁).2.2.2.2.length ≤ (keyIndKFuelsOfBudget S b).kOn := by
    simpa [embedVal] using hInv.smPows_length_le_kOn hB
  have hCtrRoom : ((v fgSh₁).eval env₁).2 + 1 ≤ b.q_total :=
    hInv.ctr_add_one_le_q_total hRoom
  let proj : (Ty.prod keyIndRespTy (.prod simTy fgSessCtrTy)).denote →
      (Ty.prod keyIndRespTy simTy).denote := fun r => (r.1, r.2.1)
  have hAbort : ∀ {Γa Γb : List PT} {e₁ : Expr pqxdhOps Γa keyIndRespTy}
      {e₂ : Expr pqxdhOps Γb keyIndRespTy} {ρ₁ : Env Γa} {ρ₂ : Env Γb}
      {smV₁ : Expr pqxdhOps Γa simTy} {fgShV₁ : Expr pqxdhOps Γa fgSessCtrTy}
      {smV₂ : Expr pqxdhOps Γb simTy},
      e₁.eval ρ₁ = e₂.eval ρ₂ →
      smV₁.eval ρ₁ = (v sm₁).eval env₁ →
      fgShV₁.eval ρ₁ = (v fgSh₁).eval env₁ →
      smV₂.eval ρ₂ = (v sm₂).eval env₂ →
      proj <$>
        (Comp.ret (.pair e₁ (.pair smV₁ fgShV₁)) : Comp pqxdhOps pqGapDhIface _ _).eval ρ₁ =
        (Comp.ret (.pair e₂ smV₂) : Comp pqxdhOps pqGapDhIface _ _).eval ρ₂ ∧
      ∀ r ∈ support ((Comp.ret (.pair e₁ (.pair smV₁ fgShV₁)) : Comp pqxdhOps pqGapDhIface _ _).eval ρ₁),
        GdhSimInv S b (bumpPred (keyIndSimPred S) c t)
          (embedVal simTy r.2.1,
            ((embedVal fgSessCtrTy r.2.2).1, ((embedVal fgSessCtrTy r.2.2).2, fgShFull.2.2))) := by
    intro _ _ _ _ _ _ _ _ _ he hsm1 hfg1 hsm2
    refine ⟨by dsimp only [proj]; simp [Comp.eval, Expr.eval, map_pure, he, hsm1, hsm2, hsm],
      fun r hr => ?_⟩
    simp only [Comp.eval, Expr.eval, hsm1, hfg1, mem_support_pure_iff] at hr
    subst hr
    exact gdhSimInv_online_unchanged ht0 ht1 hInv
  dsimp only
  change proj <$> _ = _ ∧ _
  unfold initiateGdhShadowB _root_.SignalPqxdh.Security.ReductionDsl.KeyInd.initiateGdhB
  refine sim_letV (congrArg (fun p => p.2.2) hx) fun bu => ?_
  refine sim_ite
    (by cases hasOpk <;> simp [isSomeE, buOpkB, Expr.eval])
    (hAbort (by simp [_root_.SignalPqxdh.Security.ReductionDsl.KeyInd.rNone, Expr.eval])
      rfl rfl rfl) ?_
  refine sim_letV (by cases hasOpk <;>
    simp [_root_.SignalPqxdh.Security.ReductionDsl.KeyInd.initSidE, Expr.eval, hx]) fun sid => ?_
  refine sim_ite (eAny_congr_le _ _ _ _ _ _
      (by simp [Expr.eval, hbStEq])
      (by simpa [stSess, stSessList, Expr.eval] using Nat.le_trans hOn.sess_le hc0K) hkOnLe
      fun s => by simp [_root_.SignalPqxdh.Security.ReductionDsl.KeyInd.sidEq_eval, seSid, Expr.eval])
    (hAbort (by simp [_root_.SignalPqxdh.Security.ReductionDsl.KeyInd.rNone, Expr.eval])
      rfl rfl rfl) ?_
  refine sim_caseOptV (eFind_congr_le _ _ _ _ _ _
      (by simp [Expr.eval, hbStEq])
      (by simpa [stPrin, stPrinList, Expr.eval] using Nat.le_trans hOn.prin_le hc0K) hkOnLe
      fun p => by simp [natEq, Expr.eval, hx]; try rfl)
    (hAbort (by simp [_root_.SignalPqxdh.Security.ReductionDsl.KeyInd.rNone, Expr.eval])
      rfl rfl rfl) fun ue => ?_
  refine sim_bindV (liftBase_eval_congr _ _ _ _
      (koskBundleOkPowsC_sim S _ _ _ _ _ _ _ _
        (by simp [hbStEq]) (by simp [smPows, Expr.eval, hsm]) rfl
        (by simpa using hOn) hc0K (by simpa [smPows, Expr.eval] using hPowsLe) hkOnLe)) fun ok => ?_
  refine sim_ite (by simp [Expr.eval])
    (hAbort (by simp [_root_.SignalPqxdh.Security.ReductionDsl.KeyInd.rNone, Expr.eval])
      rfl rfl rfl) ?_
  refine sim_letV ?_ fun isTE => ?_
  · simp only [_root_.SignalPqxdh.Security.ReductionDsl.KeyInd.paDhFlag,
      _root_.SignalPqxdh.Security.ReductionDsl.KeyInd.paEphIdx,
      _root_.SignalPqxdh.Security.ReductionDsl.KeyInd.initSlotIdxE,
      _root_.SignalPqxdh.Security.ReductionDsl.KeyInd.eCaseSum,
      _root_.SignalPqxdh.Security.ReductionDsl.KeyInd.mulRight,
      natEq, Expr.eval, v_eval_cons, v_zero_eval, hpa]
    try rfl
  · refine sim_bindV (liftBase_eval_congr _ _ _ _ (sBytes32_eval_const _ _)) fun ekSkRaw => ?_
    refine sim_bindV (liftBase_eval_congr _ _ _ _ (sBytes32_eval_const _ _)) fun coins => ?_
    refine sim_bindV (liftBase_eval_congr _ _ _ _
      (resolveSigPkC_sim S _ _ _ _ _ _ (by simp [hbStEq]) (by simp [Expr.eval])
        (by simpa using Nat.le_trans hOn.prin_le hc0K) hkOnLe)) fun sigPk => ?_
    refine sim_bindV (liftBase_eval_congr _ _ _ _
      (qSigVerify_eval_congr 33 _ _ _ _
        (by simp [_root_.SignalPqxdh.Security.ReductionDsl.KeyInd.encEC_eval,
          buSpkB, Expr.eval]))) fun v1 => ?_
    refine sim_bindV (liftBase_eval_congr _ _ _ _
      (qSigVerify_eval_congr 1569 _ _ _ _
        (by simp [_root_.SignalPqxdh.Security.ReductionDsl.KeyInd.encKEM_eval,
          buPqspkB, Expr.eval]))) fun v2 => ?_
    refine sim_ite (by simp [Expr.eval])
      (hAbort (by simp [_root_.SignalPqxdh.Security.ReductionDsl.KeyInd.rNone, Expr.eval])
        rfl rfl rfl) ?_
    refine sim_bindV (liftBase_eval_congr _ _ _ _
      (qKemEncaps_eval_congr _ _ _ _ (by simp [Expr.eval]))) fun krOpt => ?_
    refine sim_caseOptV (by simp)
      (hAbort (by simp [_root_.SignalPqxdh.Security.ReductionDsl.KeyInd.rNone, Expr.eval])
        rfl rfl rfl) fun kr => ?_
    refine sim_bindV (liftBase_eval_congr _ _ _ _
      (qX25519Base_eval_congr _ _ _ _ (by simp))) fun ekPkRaw => ?_
    refine sim_letV (by simp [_root_.SignalPqxdh.Security.ReductionDsl.KeyInd.litB_eval, Expr.eval]; try rfl) fun ekSk => ?_
    refine sim_letV
      (by simp [_root_.SignalPqxdh.Security.ReductionDsl.KeyInd.paU, Expr.eval, hpa]) fun ekPk => ?_
    refine sim_bindV (liftBase_eval_congr _ _ _ _
      (lookupSpkSkC_sim S _ _ _ _ _ _ _ _
        (by simp [hbStEq]) (by simp [smPows, Expr.eval, hsm]) (by simp [Expr.eval])
        (by simpa using Nat.le_trans hOn.spks_le hc0K)
        (by simpa [smPows, Expr.eval] using hPowsLe) hkOnLe)) fun spkSk => ?_
    refine sim_bindV (computePosC_congr _ _ _ _ _ _ _ _ _ _
      (by simp [Expr.eval]) (by simp)
      (by simp [Expr.eval]) (by simp [Expr.eval])) fun p1 => ?_
    refine sim_bindV (computePosC_congr _ _ _ _ _ _ _ _ _ _
      (by simp) (by simp [_root_.SignalPqxdh.Security.ReductionDsl.KeyInd.litB_eval])
      (by simp) (by simp [Expr.eval])) fun p2 => ?_
    refine sim_bindV (computePosC_congr _ _ _ _ _ _ _ _ _ _
      (by simp) (by simp [_root_.SignalPqxdh.Security.ReductionDsl.KeyInd.litB_eval])
      (by simp) (by simp [Expr.eval])) fun p3 => ?_
    refine sim_bindV (computeOptPosInitC_congr _ _ _ _ _ _ _ _
      (by simp) (by simp) (by simp [Expr.eval])) fun p4 => ?_
    refine sim_letV (by simp [Expr.eval]) fun ss => ?_
    refine sim_fgPatch ((v sm₁).eval env₁) ((v fgSh₁).eval env₁) fgShFull
      rfl rfl rfl rfl rfl
      (by simp [smFgL, Expr.eval]) (by simp [smFgL, Expr.eval, ← hsm])
      (by simp [Expr.eval]) (by simp [Expr.eval])
      hB hCtrRoom hInv fun patchR => ?_
    refine sim_letV_cond (by simp [Expr.eval]) fun dkReal _ => ?_
    refine sim_letV_cond (by simp [Expr.eval]) fun fgL' hfgL' => ?_
    refine sim_letV_lhs_cond fun fgSh' hfgSh' => ?_
    refine sim_letV_cond
      (by simp [_root_.SignalPqxdh.Security.ReductionDsl.KeyInd.optFst,
        eCaseOpt, buOpkB, Expr.eval]; try rfl) fun hdr _ => ?_
    refine sim_bindV_cond (liftBase_eval_congr _ _ _ _
      (honestPeerC_sim S _ _ _ _ _ _ (by simp [hbStEq]) (by simp [Expr.eval]; try rfl)
        (by simpa using Nat.le_trans hOn.prin_le hc0K) hkOnLe)) fun hp => ?_
    refine sim_bindV_cond (liftBase_eval_congr _ _ _ _
      (checkProvC_sim S _ _ _ _ _ _ (by simp [hbStEq]) (by simp)
        (by simpa using hOn) hc0K hkOnLe)) fun prov => ?_
    refine sim_letV_cond
      (by simp [_root_.SignalPqxdh.Security.ReductionDsl.KeyInd.optSnd,
        eCaseOpt, isSomeE, buOpkB, Expr.eval]; try rfl) fun sInit _ => ?_
    refine sim_bindV_cond (chooseInitRandC_sim S _ _ _ _ _ _
      (by simp [hbStEq]) (by simp)
      (by simpa using Nat.le_trans hOn.resps_le hc0K) hkOnLe) fun dkRand => ?_
    refine sim_letV_cond
      (by simp [smUpd, _root_.SignalPqxdh.Security.ReductionDsl.KeyInd.smMk,
        stUpd, _root_.SignalPqxdh.Security.ReductionDsl.KeyInd.stSecb, stPrin, stSpks, stOpks,
        stSess, stResps, _root_.SignalPqxdh.Security.ReductionDsl.KeyInd.stUsedO,
        _root_.SignalPqxdh.Security.ReductionDsl.KeyInd.stUsedN,
        _root_.SignalPqxdh.Security.ReductionDsl.KeyInd.stKyb,
        _root_.SignalPqxdh.Security.ReductionDsl.KeyInd.stRo, stAdv,
        _root_.SignalPqxdh.Security.ReductionDsl.KeyInd.smRaw,
        _root_.SignalPqxdh.Security.ReductionDsl.KeyInd.smLog, smPows,
        seUpd, Expr.eval, hbSt, hbSt₂, hsm]) fun smV hsmV => ?_
    refine sim_bindV_cond (liftBase_eval_congr _ _ _ _
      (findHonestC_sim S _ _ _ _ _ _ (by simp [hbStEq]) (by simp [Expr.eval]; try rfl)
        (by simpa using Nat.le_trans hOn.prin_le hc0K) hkOnLe)) fun fh => ?_
    refine ⟨?_, fun hPatch r hr => ?_⟩
    · cases fh <;>
        dsimp only [proj] <;>
        simp [Comp.eval, eCaseOpt, map_pure,
          _root_.SignalPqxdh.Security.ReductionDsl.KeyInd.rInitUnfresh,
          _root_.SignalPqxdh.Security.ReductionDsl.KeyInd.rHdr, Expr.eval]
    · cases fh <;>
      · simp only [Comp.eval, eCaseOpt, Expr.eval, v_eval_cons, v_zero_eval,
          mem_support_pure_iff] at hr
        subst hr
        rw [hsmV, hfgSh']
        simpa [smUpd, _root_.SignalPqxdh.Security.ReductionDsl.KeyInd.smMk,
          stUpd, _root_.SignalPqxdh.Security.ReductionDsl.KeyInd.stSecb, stPrin, stSpks, stOpks,
          stSess, stResps, _root_.SignalPqxdh.Security.ReductionDsl.KeyInd.stUsedO,
          _root_.SignalPqxdh.Security.ReductionDsl.KeyInd.stUsedN,
          _root_.SignalPqxdh.Security.ReductionDsl.KeyInd.stKyb,
          _root_.SignalPqxdh.Security.ReductionDsl.KeyInd.stRo, stAdv,
          _root_.SignalPqxdh.Security.ReductionDsl.KeyInd.smRaw,
          _root_.SignalPqxdh.Security.ReductionDsl.KeyInd.smLog, smPows,
          Expr.eval, hbSt, hfgL'] using
          gdhSimInv_online_cons_sess ((v sm₁).eval env₁) ((v fgSh₁).eval env₁) patchR
            fgShFull _ ht0 ht1 hInv hPatch

private theorem fixParamsSent_fields {S : Setup} {b : QueryBudget}
    {pa₁ pa₂ : paramsTy.denote}
    (h : embedVal paramsTy pa₂ =
      Computational.Proofs.SignalPqxdh.Security.ReductionDsl.KindSplit.KeyIndGapDhKSimBase.fixParamsSent
        S b (embedVal paramsTy pa₁)) :
    pa₁.1 = pa₂.1 ∧
    pa₁.2.2.2.2.2.1 = pa₂.2.2.2.2.2.1 ∧
    pa₂.2.2.2.2.2.2.1 = fixSent S b pa₁.2.2.2.2.2.2.1 ∧
    pa₁.2.2.2.2.2.2.2.2.1 = pa₂.2.2.2.2.2.2.2.2.1 := by
  rcases pa₁ with ⟨u1, v1, up1, pf1, pi1, df1, ei1, si1, om1, oi1, md1⟩
  rcases pa₂ with ⟨u2, v2, up2, pf2, pi2, df2, ei2, si2, om2, oi2, md2⟩
  dsimp [embedVal,
    Computational.Proofs.SignalPqxdh.Security.ReductionDsl.KindSplit.KeyIndGapDhKSimBase.fixParamsSent] at h
  obtain ⟨rfl, -, -, -, -, rfl, rfl, -, rfl, -, -⟩ :=
    show u2 = u1 ∧ v2 = v1 ∧ up2 = up1 ∧ pf2 = pf1 ∧ pi2 = fixSent S b pi1 ∧
      df2 = df1 ∧ ei2 = fixSent S b ei1 ∧ si2 = fixSent S b si1 ∧
      om2 = om1 ∧ oi2 = fixSent S b oi1 ∧ md2 = md1 by
      simpa only [Prod.mk.injEq] using h
  exact ⟨rfl, rfl, rfl, rfl⟩

/-- Arm-level simulation, `GdhSimInv` preservation, and `sendOpkCnt` bound preservation for
    `initiateGdhActiveShadowInnerB` vs `initiateGdhActiveInnerB`. -/
theorem initiateGdhActiveShadowInnerB_sim (S : Setup) (b : QueryBudget) (hasOpk : Bool)
    {Γ₁a Γ₂a Γ₃a Γ₄a Γ₅a Γ₆a Δ₁ Γ₁b Γ₂b Γ₃b Γ₄b Γ₅b Δ₂ : List PT}
    [Ext Γ₁a Δ₁] [Ext Γ₂a Δ₁] [Ext Γ₃a Δ₁] [Ext Γ₄a Δ₁] [Ext Γ₅a Δ₁] [Ext Γ₆a Δ₁]
    [Ext Γ₁b Δ₂] [Ext Γ₂b Δ₂] [Ext Γ₃b Δ₂] [Ext Γ₄b Δ₂] [Ext Γ₅b Δ₂]
    (pa₁ : Var Γ₁a paramsTy) (sm₁ : Var Γ₂a simTy) (bSt₁ : Var Γ₃a keyIndStateTy)
    (fgSh₁ : Var Γ₆a fgSessCtrTy) (sendOpkCnt₁ : Var Γ₅a .nat) (x₁ : Var Γ₄a initQTy)
    (pa₂ : Var Γ₁b paramsTy) (sm₂ : Var Γ₂b simTy) (bSt₂ : Var Γ₃b keyIndStateTy)
    (sendOpkCnt₂ : Var Γ₅b .nat) (x₂ : Var Γ₄b initQTy)
    (env₁ : Env Δ₁) (env₂ : Env Δ₂)
    (c : Fin 3 → ℕ) (t : KeyIndQuery S)
    (fgShFull : fgShadowAtomicTy.denote)
    (hpa : embedVal paramsTy ((v pa₂).eval env₂) =
      Computational.Proofs.SignalPqxdh.Security.ReductionDsl.KindSplit.KeyIndGapDhKSimBase.fixParamsSent
        S b (embedVal paramsTy ((v pa₁).eval env₁)))
    (hsm : (v sm₁).eval env₁ = (v sm₂).eval env₂)
    (hbSt : (v bSt₁).eval env₁ = ((v sm₁).eval env₁).1)
    (hbSt₂ : (v bSt₂).eval env₂ = ((v sm₂).eval env₂).1)
    (hcnt : (v sendOpkCnt₁).eval env₁ = (v sendOpkCnt₂).eval env₂)
    (hcntLe : (v sendOpkCnt₁).eval env₁ ≤ c 0)
    (hx : (v x₁).eval env₁ = (v x₂).eval env₂)
    (ht0 : keyIndSimPred S 0 t = true)
    (ht1 : keyIndSimPred S 1 t = false)
    (hB : ∀ j, c j ≤ keyIndSimBounds b j)
    (hRoom : ∀ j, keyIndSimPred S j t → c j + 1 ≤ keyIndSimBounds b j)
    (hInv : GdhSimInv S b c
      (embedVal simTy ((v sm₁).eval env₁),
        ((embedVal fgSessCtrTy ((v fgSh₁).eval env₁)).1,
          ((embedVal fgSessCtrTy ((v fgSh₁).eval env₁)).2, fgShFull.2.2)))) :
    (fun r => (r.1, (r.2.1.1, r.2.2))) <$>
      (initiateGdhActiveShadowInnerB S (keyIndKFuelsOfBudget S b)
        pa₁ sm₁ bSt₁ fgSh₁ sendOpkCnt₁ hasOpk x₁).eval env₁ =
      (Computational.Proofs.SignalPqxdh.Delta.KeyInd1KeyActiveProgs.initiateGdhActiveInnerB
        S b.q_total pa₂ sm₂ bSt₂ sendOpkCnt₂ hasOpk x₂).eval env₂ ∧
    ∀ r ∈ support
      ((initiateGdhActiveShadowInnerB S (keyIndKFuelsOfBudget S b)
        pa₁ sm₁ bSt₁ fgSh₁ sendOpkCnt₁ hasOpk x₁).eval env₁),
      GdhSimInv S b (bumpPred (keyIndSimPred S) c t)
        (embedVal simTy r.2.1.1,
          ((embedVal fgSessCtrTy r.2.1.2).1, ((embedVal fgSessCtrTy r.2.1.2).2, fgShFull.2.2))) ∧
      r.2.2 ≤ bumpPred (keyIndSimPred S) c t 0 := by
  obtain ⟨hpaU, hpaDf, hpaEi, hpaOm⟩ := fixParamsSent_fields hpa
  have hbStEq : (v bSt₁).eval env₁ = (v bSt₂).eval env₂ := by rw [hbSt, hbSt₂, hsm]
  have hOn : BaseOnlineLenInv c ((v bSt₁).eval env₁) := by
    have h := hInv.online_len
    change BaseOnlineLenInv c (projVal keyIndStateTy (embedVal keyIndStateTy ((v sm₁).eval env₁).1)) at h
    rwa [projVal_embedVal, ← hbSt] at h
  have hc0Bump : bumpPred (keyIndSimPred S) c t 0 = c 0 + 1 := by simp [bumpPred, ht0]
  have hc0K : c 0 ≤ (keyIndKFuelsOfBudget S b).kOn := by
    simpa [keyIndKFuelsOfBudget, keyIndSimBounds] using hB 0
  have hkOnLe : (keyIndKFuelsOfBudget S b).kOn ≤ b.q_total := Nat.min_le_right _ _
  have hSessLenM : ((v bSt₁).eval env₁).2.2.2.2.1.length ≤ min b.q_on b.q_total :=
    Nat.le_trans hOn.sess_le hc0K
  have hCntM : (v sendOpkCnt₁).eval env₁ ≤ min b.q_on b.q_total :=
    Nat.le_trans hcntLe hc0K
  have hPowsLe : ((v sm₁).eval env₁).2.2.2.2.length ≤ (keyIndKFuelsOfBudget S b).kOn := by
    simpa [embedVal] using hInv.smPows_length_le_kOn hB
  have hCtrRoom : ((v fgSh₁).eval env₁).2 + 1 ≤ b.q_total :=
    hInv.ctr_add_one_le_q_total hRoom
  let proj : (Ty.prod keyIndRespTy (.prod (.prod simTy fgSessCtrTy) .nat)).denote →
      (Ty.prod keyIndRespTy (.prod simTy .nat)).denote := fun r => (r.1, (r.2.1.1, r.2.2))
  have hAbort : ∀ {Γa Γb : List PT} {e₁ : Expr pqxdhOps Γa keyIndRespTy}
      {e₂ : Expr pqxdhOps Γb keyIndRespTy} {ρ₁ : Env Γa} {ρ₂ : Env Γb}
      {smV₁ : Expr pqxdhOps Γa simTy} {fgShV₁ : Expr pqxdhOps Γa fgSessCtrTy}
      {cntV₁ : Expr pqxdhOps Γa .nat}
      {smV₂ : Expr pqxdhOps Γb simTy} {cntV₂ : Expr pqxdhOps Γb .nat},
      e₁.eval ρ₁ = e₂.eval ρ₂ →
      smV₁.eval ρ₁ = (v sm₁).eval env₁ →
      fgShV₁.eval ρ₁ = (v fgSh₁).eval env₁ →
      cntV₁.eval ρ₁ = (v sendOpkCnt₁).eval env₁ →
      smV₂.eval ρ₂ = (v sm₂).eval env₂ →
      cntV₂.eval ρ₂ = (v sendOpkCnt₂).eval env₂ →
      proj <$>
        (Comp.ret (.pair e₁ (.pair (.pair smV₁ fgShV₁) cntV₁)) :
          Comp pqxdhOps pqGapDhIface _ _).eval ρ₁ =
        (Comp.ret (.pair e₂ (.pair smV₂ cntV₂)) : Comp pqxdhOps pqGapDhIface _ _).eval ρ₂ ∧
      ∀ r ∈ support ((Comp.ret (.pair e₁ (.pair (.pair smV₁ fgShV₁) cntV₁)) :
          Comp pqxdhOps pqGapDhIface _ _).eval ρ₁),
        GdhSimInv S b (bumpPred (keyIndSimPred S) c t)
          (embedVal simTy r.2.1.1,
            ((embedVal fgSessCtrTy r.2.1.2).1, ((embedVal fgSessCtrTy r.2.1.2).2, fgShFull.2.2))) ∧
        r.2.2 ≤ bumpPred (keyIndSimPred S) c t 0 := by
    intro _ _ _ _ _ _ _ _ _ _ _ he hsm1 hfg1 hcnt1 hsm2 hcnt2
    refine ⟨by dsimp only [proj]; simp [Comp.eval, Expr.eval, map_pure, he, hsm1, hsm2, hsm, hcnt1, hcnt2, hcnt],
      fun r hr => ?_⟩
    simp only [Comp.eval, Expr.eval, hsm1, hfg1, hcnt1, mem_support_pure_iff] at hr
    subst hr
    exact ⟨gdhSimInv_online_unchanged ht0 ht1 hInv, hc0Bump ▸ Nat.le_succ_of_le hcntLe⟩
  change proj <$> _ = _ ∧ _
  unfold initiateGdhActiveShadowInnerB
    Computational.Proofs.SignalPqxdh.Delta.KeyInd1KeyActiveProgs.initiateGdhActiveInnerB
  refine sim_letV (congrArg (fun p => p.2.2) hx) fun bu => ?_
  refine sim_ite
    (by cases hasOpk <;> simp [isSomeE, buOpkB, Expr.eval])
    (hAbort (by simp [_root_.SignalPqxdh.Security.ReductionDsl.KeyInd.rNone, Expr.eval])
      rfl rfl rfl rfl rfl) ?_
  refine sim_letV (by cases hasOpk <;>
    simp [_root_.SignalPqxdh.Security.ReductionDsl.KeyInd.initSidE, Expr.eval, hx]) fun sid => ?_
  refine sim_ite (eAny_congr_le _ _ _ _ _ _
      (by simp [Expr.eval, hbStEq])
      (by simpa [stSess, stSessList, Expr.eval] using Nat.le_trans hOn.sess_le hc0K) hkOnLe
      fun s => by simp [_root_.SignalPqxdh.Security.ReductionDsl.KeyInd.sidEq_eval, seSid, Expr.eval])
    (hAbort (by simp [_root_.SignalPqxdh.Security.ReductionDsl.KeyInd.rNone, Expr.eval])
      rfl rfl rfl rfl rfl) ?_
  refine sim_caseOptV (eFind_congr_le _ _ _ _ _ _
      (by simp [Expr.eval, hbStEq])
      (by simpa [stPrin, stPrinList, Expr.eval] using Nat.le_trans hOn.prin_le hc0K) hkOnLe
      fun p => by simp [natEq, Expr.eval, hx]; try rfl)
    (hAbort (by simp [_root_.SignalPqxdh.Security.ReductionDsl.KeyInd.rNone, Expr.eval])
      rfl rfl rfl rfl rfl) fun ue => ?_
  refine sim_bindV (liftBase_eval_congr _ _ _ _
      (koskBundleOkPowsC_sim S _ _ _ _ _ _ _ _
        (by simp [hbStEq]) (by simp [smPows, Expr.eval, hsm]) rfl
        (by simpa using hOn) hc0K (by simpa [smPows, Expr.eval] using hPowsLe) hkOnLe)) fun ok => ?_
  refine sim_ite (by simp [Expr.eval])
    (hAbort (by simp [_root_.SignalPqxdh.Security.ReductionDsl.KeyInd.rNone, Expr.eval])
      rfl rfl rfl rfl rfl) ?_
  refine sim_letV ?_ fun isTE => ?_
  · cases hasOpk
    · simp only [Bool.false_eq_true, ↓reduceIte,
        _root_.SignalPqxdh.Security.ReductionDsl.KeyInd.natEq_eval,
        _root_.SignalPqxdh.Security.ReductionDsl.KeyInd.paDhFlag,
        _root_.SignalPqxdh.Security.ReductionDsl.KeyInd.paOpkMode,
        _root_.SignalPqxdh.Security.ReductionDsl.KeyInd.paEphIdx,
        stSess, Expr.eval, v_eval_cons, hpaDf, hpaOm, hpaEi, ← hbStEq]
      rw [← beq_fixSent_of_le_mOn hSessLenM]
    · simp only [↓reduceIte,
        _root_.SignalPqxdh.Security.ReductionDsl.KeyInd.natEq_eval,
        _root_.SignalPqxdh.Security.ReductionDsl.KeyInd.paDhFlag,
        _root_.SignalPqxdh.Security.ReductionDsl.KeyInd.paOpkMode,
        _root_.SignalPqxdh.Security.ReductionDsl.KeyInd.paEphIdx,
        stSess, Expr.eval, v_eval_cons, hpaDf, hpaOm, hpaEi, ← hcnt, ← hbStEq]
      cases ((v pa₂).eval env₂).2.2.2.2.2.2.2.2.1
      · simp [← beq_fixSent_of_le_mOn hSessLenM]
      · simp [← beq_fixSent_of_le_mOn hCntM]
  · refine sim_bindV (liftBase_eval_congr _ _ _ _ (sBytes32_eval_const _ _)) fun ekSkRaw => ?_
    refine sim_bindV (liftBase_eval_congr _ _ _ _ (sBytes32_eval_const _ _)) fun coins => ?_
    refine sim_bindV (liftBase_eval_congr _ _ _ _
      (resolveSigPkC_sim S _ _ _ _ _ _ (by simp [hbStEq]) (by simp [Expr.eval])
        (by simpa using Nat.le_trans hOn.prin_le hc0K) hkOnLe)) fun sigPk => ?_
    refine sim_bindV (liftBase_eval_congr _ _ _ _
      (qSigVerify_eval_congr 33 _ _ _ _
        (by simp [_root_.SignalPqxdh.Security.ReductionDsl.KeyInd.encEC_eval,
          buSpkB, Expr.eval]))) fun v1 => ?_
    refine sim_bindV (liftBase_eval_congr _ _ _ _
      (qSigVerify_eval_congr 1569 _ _ _ _
        (by simp [_root_.SignalPqxdh.Security.ReductionDsl.KeyInd.encKEM_eval,
          buPqspkB, Expr.eval]))) fun v2 => ?_
    refine sim_ite (by simp [Expr.eval])
      (hAbort (by simp [_root_.SignalPqxdh.Security.ReductionDsl.KeyInd.rNone, Expr.eval])
        rfl rfl rfl rfl rfl) ?_
    refine sim_bindV (liftBase_eval_congr _ _ _ _
      (qKemEncaps_eval_congr _ _ _ _ (by simp [Expr.eval]))) fun krOpt => ?_
    refine sim_caseOptV (by simp)
      (hAbort (by simp [_root_.SignalPqxdh.Security.ReductionDsl.KeyInd.rNone, Expr.eval])
        rfl rfl rfl rfl rfl) fun kr => ?_
    refine sim_bindV (liftBase_eval_congr _ _ _ _
      (qX25519Base_eval_congr _ _ _ _ (by simp))) fun ekPkRaw => ?_
    refine sim_letV (by simp [_root_.SignalPqxdh.Security.ReductionDsl.KeyInd.litB_eval, Expr.eval]; try rfl) fun ekSk => ?_
    refine sim_letV
      (by simp [_root_.SignalPqxdh.Security.ReductionDsl.KeyInd.paU, Expr.eval, hpaU]) fun ekPk => ?_
    refine sim_bindV (liftBase_eval_congr _ _ _ _
      (lookupSpkSkC_sim S _ _ _ _ _ _ _ _
        (by simp [hbStEq]) (by simp [smPows, Expr.eval, hsm]) (by simp [Expr.eval])
        (by simpa using Nat.le_trans hOn.spks_le hc0K)
        (by simpa [smPows, Expr.eval] using hPowsLe) hkOnLe)) fun spkSk => ?_
    refine sim_bindV (computePosC_congr _ _ _ _ _ _ _ _ _ _
      (by simp [Expr.eval]) (by simp)
      (by simp [Expr.eval]) (by simp [Expr.eval])) fun p1 => ?_
    refine sim_bindV (computePosC_congr _ _ _ _ _ _ _ _ _ _
      (by simp) (by simp [_root_.SignalPqxdh.Security.ReductionDsl.KeyInd.litB_eval])
      (by simp) (by simp [Expr.eval])) fun p2 => ?_
    refine sim_bindV (computePosC_congr _ _ _ _ _ _ _ _ _ _
      (by simp) (by simp [_root_.SignalPqxdh.Security.ReductionDsl.KeyInd.litB_eval])
      (by simp) (by simp [Expr.eval])) fun p3 => ?_
    refine sim_bindV (computeOptPosInitC_congr _ _ _ _ _ _ _ _
      (by simp) (by simp) (by simp [Expr.eval])) fun p4 => ?_
    refine sim_letV (by simp [Expr.eval]) fun ss => ?_
    refine sim_fgPatch ((v sm₁).eval env₁) ((v fgSh₁).eval env₁) fgShFull
      rfl rfl rfl rfl rfl
      (by simp [smFgL, Expr.eval]) (by simp [smFgL, Expr.eval, ← hsm])
      (by simp [Expr.eval]) (by simp [Expr.eval])
      hB hCtrRoom hInv fun patchR => ?_
    refine sim_letV_cond (by simp [Expr.eval]) fun dkReal _ => ?_
    refine sim_letV_cond (by simp [Expr.eval]) fun fgL' hfgL' => ?_
    refine sim_letV_lhs_cond fun fgSh' hfgSh' => ?_
    refine sim_letV_cond
      (by simp [_root_.SignalPqxdh.Security.ReductionDsl.KeyInd.optFst,
        eCaseOpt, buOpkB, Expr.eval]; try rfl) fun hdr _ => ?_
    refine sim_bindV_cond (liftBase_eval_congr _ _ _ _
      (honestPeerC_sim S _ _ _ _ _ _ (by simp [hbStEq]) (by simp [Expr.eval]; try rfl)
        (by simpa using Nat.le_trans hOn.prin_le hc0K) hkOnLe)) fun hp => ?_
    refine sim_bindV_cond (liftBase_eval_congr _ _ _ _
      (checkProvC_sim S _ _ _ _ _ _ (by simp [hbStEq]) (by simp)
        (by simpa using hOn) hc0K hkOnLe)) fun prov => ?_
    refine sim_letV_cond
      (by simp [_root_.SignalPqxdh.Security.ReductionDsl.KeyInd.optSnd,
        eCaseOpt, isSomeE, buOpkB, Expr.eval]; try rfl) fun sInit _ => ?_
    refine sim_bindV_cond (chooseInitRandC_sim S _ _ _ _ _ _
      (by simp [hbStEq]) (by simp)
      (by simpa using Nat.le_trans hOn.resps_le hc0K) hkOnLe) fun dkRand => ?_
    refine sim_letV_cond
      (by simp [smUpd, _root_.SignalPqxdh.Security.ReductionDsl.KeyInd.smMk,
        stUpd, _root_.SignalPqxdh.Security.ReductionDsl.KeyInd.stSecb, stPrin, stSpks, stOpks,
        stSess, stResps, _root_.SignalPqxdh.Security.ReductionDsl.KeyInd.stUsedO,
        _root_.SignalPqxdh.Security.ReductionDsl.KeyInd.stUsedN,
        _root_.SignalPqxdh.Security.ReductionDsl.KeyInd.stKyb,
        _root_.SignalPqxdh.Security.ReductionDsl.KeyInd.stRo, stAdv,
        _root_.SignalPqxdh.Security.ReductionDsl.KeyInd.smRaw,
        _root_.SignalPqxdh.Security.ReductionDsl.KeyInd.smLog, smPows,
        seUpd, Expr.eval, hbSt, hbSt₂, hsm]) fun smV hsmV => ?_
    refine sim_letV_cond
      (by cases hasOpk <;> simp [Expr.eval, hcnt]) fun cntV hcntV => ?_
    refine sim_bindV_cond (liftBase_eval_congr _ _ _ _
      (findHonestC_sim S _ _ _ _ _ _ (by simp [hbStEq]) (by simp [Expr.eval]; try rfl)
        (by simpa using Nat.le_trans hOn.prin_le hc0K) hkOnLe)) fun fh => ?_
    refine ⟨?_, fun hPatch r hr => ?_⟩
    · cases fh <;>
        dsimp only [proj] <;>
        simp [Comp.eval, eCaseOpt, map_pure,
          _root_.SignalPqxdh.Security.ReductionDsl.KeyInd.rInitUnfresh,
          _root_.SignalPqxdh.Security.ReductionDsl.KeyInd.rHdr, Expr.eval]
    · cases fh <;>
      · simp only [Comp.eval, eCaseOpt, Expr.eval, v_eval_cons, v_zero_eval,
          mem_support_pure_iff] at hr
        subst hr
        refine ⟨?_, ?_⟩
        · rw [hsmV, hfgSh']
          simpa [smUpd, _root_.SignalPqxdh.Security.ReductionDsl.KeyInd.smMk,
            stUpd, _root_.SignalPqxdh.Security.ReductionDsl.KeyInd.stSecb, stPrin, stSpks, stOpks,
            stSess, stResps, _root_.SignalPqxdh.Security.ReductionDsl.KeyInd.stUsedO,
            _root_.SignalPqxdh.Security.ReductionDsl.KeyInd.stUsedN,
            _root_.SignalPqxdh.Security.ReductionDsl.KeyInd.stKyb,
            _root_.SignalPqxdh.Security.ReductionDsl.KeyInd.stRo, stAdv,
            _root_.SignalPqxdh.Security.ReductionDsl.KeyInd.smRaw,
            _root_.SignalPqxdh.Security.ReductionDsl.KeyInd.smLog, smPows,
            Expr.eval, hbSt, hfgL'] using
            gdhSimInv_online_cons_sess ((v sm₁).eval env₁) ((v fgSh₁).eval env₁) patchR
              fgShFull _ ht0 ht1 hInv hPatch
        · dsimp only
          rw [hcntV, hc0Bump]
          cases hasOpk
          · simp only [Bool.false_eq_true, ↓reduceIte, v_eval_cons]
            exact Nat.le_succ_of_le hcntLe
          · change (v sendOpkCnt₁).eval _ + 1 ≤ c 0 + 1
            simp only [v_eval_cons]
            exact Nat.add_le_add_right hcntLe 1

private theorem gdhSimInv_bump_noop {S : Setup} {b : QueryBudget}
    {c : Fin 3 → ℕ} {t : KeyIndQuery S} {sK : simShadowAtomicTy.denote}
    (hInv : GdhSimInv S b c sK)
    (ht0 : keyIndSimPred S 0 t = true) (ht1 : keyIndSimPred S 1 t = false) :
    GdhSimInv S b (bumpPred (keyIndSimPred S) c t) sK := by
  have hc0 : c 0 ≤ bumpPred (keyIndSimPred S) c t 0 := by simp [bumpPred, ht0]
  have hc1 : bumpPred (keyIndSimPred S) c t 1 = c 1 := by simp [bumpPred, ht1]
  have hSum : bumpPred (keyIndSimPred S) c t 0 + bumpPred (keyIndSimPred S) c t 1 =
      bumpPred (keyIndSimPred S) c t 2 :=
    Computational.Proofs.SignalPqxdh.Security.ReductionDsl.KindSplit.KeyIndCoreKSimBase.bumpPred_keyIndSimPred_sum
      t hInv.online_len.counts_eq
  refine
    { online_len :=
        { prin_le   := Nat.le_trans hInv.online_len.prin_le hc0
          spks_le   := Nat.le_trans hInv.online_len.spks_le hc0
          opks_le   := Nat.le_trans hInv.online_len.opks_le hc0
          sess_le   := Nat.le_trans hInv.online_len.sess_le hc0
          resps_le  := Nat.le_trans hInv.online_len.resps_le hc0
          usedO_le  := Nat.le_trans hInv.online_len.usedO_le hc0
          usedN_le  := Nat.le_trans hInv.online_len.usedN_le hc0
          kyb_le    := Nat.le_trans hInv.online_len.kyb_le hc0
          adv_le    := Nat.le_trans hInv.online_len.adv_le hc0
          counts_eq := hSum }
      fg_sess_le := Nat.le_trans hInv.fg_sess_le hc0
      fg_shadow  := hc1 ▸ hInv.fg_shadow
      raw_len    := hc1 ▸ hInv.raw_len
      raw_shadow := hInv.raw_shadow
      log_len    := hc1 ▸ hInv.log_len
      pows_len   := Nat.le_trans hInv.pows_len hc0 }

private theorem eLet_eval {Γ : List PT} {τ₁ τ₂ : PT} (a : Expr pqxdhOps Γ τ₁)
    (k : Var (τ₁ :: Γ) τ₁ → Expr pqxdhOps (τ₁ :: Γ) τ₂) (env : Env Γ) :
    (eLet a k).eval env = (k .zero).eval (.cons (a.eval env) env) := rfl

private theorem ite_pair_cons_eval_snd_length_le {Γ : List PT} {τ : PT}
    (c : Expr pqxdhOps Γ .bool) (u : Expr pqxdhOps Γ (.list τ)) (e : Expr pqxdhOps Γ τ)
    (env : Env Γ) :
    (((Expr.ite c (.pair (.bool false) u) (.pair (.bool true) (.cons e u))).eval env).2).length ≤
      (u.eval env).length + 1 := by
  let b : Bool := c.eval env
  change ((@ite (Bool × List τ.denote) (b = true) _
    (false, u.eval env) (true, e.eval env :: u.eval env)).2).length ≤ (u.eval env).length + 1
  cases b
  · exact Nat.le_refl ((u.eval env).length + 1)
  · exact Nat.le_succ (u.eval env).length

private theorem kyberCheckE_snd_length_le {K : Nat} {Δ : List PT}
    (used : Expr pqxdhOps Δ (.list (.prod .nat (.prod U32 (.prod U32 (B 32))))))
    (entry : Expr pqxdhOps Δ (.prod .nat (.prod U32 (.prod U32 (B 32)))))
    (env : Env Δ) :
    (((kyberCheckE K used entry).eval env).2).length ≤ (used.eval env).length + 1 := by
  rw [kyberCheckE, _root_.SignalPqxdh.Security.ReductionDsl.KeyInd.eLet2,
    eLet_eval, eLet_eval, eLet_eval]
  exact ite_pair_cons_eval_snd_length_le _ _ _ _

private theorem mem_support_finishAcceptGdhC (S : Setup) (K : Nat) (hasOpk : Bool)
    {Γ₂ Γ₃ Γ₄ Γ₅ Γ₆ Γ₇ Δ : List PT}
    [Ext Γ₂ Δ] [Ext Γ₃ Δ] [Ext Γ₄ Δ] [Ext Γ₅ Δ] [Ext Γ₆ Δ] [Ext Γ₇ Δ]
    (sm : Var Γ₂ simTy) (bSt : Var Γ₃ keyIndStateTy)
    (x : Var Γ₄ accQTy) (ke : Var Γ₅ (.prod .nat principalEntryTy))
    (be : Var Γ₆ (.prod (.prod .nat .nat) spkBundleEntryTy))
    (opkPkOpt : Expr pqxdhOps Δ (.opt (B 32)))
    (opks' : Expr pqxdhOps Δ (.list (.prod (.prod .nat (.prod .nat .nat)) opkEntryTy)))
    (usedO' usedN' : Expr pqxdhOps Δ (.list (.prod .nat (.prod .nat .nat))))
    (kyb' : Expr pqxdhOps Δ (.list (.prod .nat (.prod U32 (.prod U32 (B 32))))))
    (patchR : Var Γ₇ (.prod drKeyTy (.list fgPatchEntryTy)))
    (env : Env Δ) {accRes : (Ty.prod keyIndRespTy simTy).denote}
    (hMem : accRes ∈ support
      ((finishAcceptGdhC S K sm bSt hasOpk x ke be opkPkOpt opks' usedO' usedN' kyb' patchR).eval env)) :
    stPrinList accRes.2.1 = stPrinList ((v bSt).eval env) ∧
    stSpksList accRes.2.1 = stSpksList ((v bSt).eval env) ∧
    stOpksList accRes.2.1 = opks'.eval env ∧
    stSessList accRes.2.1 = stSessList ((v bSt).eval env) ∧
    (stRespsList accRes.2.1).length = (stRespsList ((v bSt).eval env)).length + 1 ∧
    stUsedOList accRes.2.1 = usedO'.eval env ∧
    stUsedNList accRes.2.1 = usedN'.eval env ∧
    stKybList accRes.2.1 = kyb'.eval env ∧
    stAdvList accRes.2.1 = stAdvList ((v bSt).eval env) ∧
    accRes.2.2.1 = ((v patchR).eval env).2 ∧
    accRes.2.2.2 = ((v sm).eval env).2.2 := by
  simp only [finishAcceptGdhC, letV_eval, bindV, Comp.eval,
    mem_support_bind_iff, mem_support_pure_iff] at hMem
  rcases hMem with ⟨shOpt, _, dkRand, _, rfl⟩
  cases shOpt <;>
    simp [eCaseOpt, smUpd, _root_.SignalPqxdh.Security.ReductionDsl.KeyInd.smMk,
      stUpd, _root_.SignalPqxdh.Security.ReductionDsl.KeyInd.stMk,
      stPrin, stSpks, stSess, stResps, stAdv,
      _root_.SignalPqxdh.Security.ReductionDsl.KeyInd.smRaw,
      _root_.SignalPqxdh.Security.ReductionDsl.KeyInd.smLog, smPows,
      stPrinList, stSpksList, stOpksList, stSessList, stRespsList,
      stUsedOList, stUsedNList, stKybList, stAdvList, Expr.eval]

private theorem embedVal_prod_fst (t u : PT) (p : (Ty.prod t u).denote) :
    (embedVal (.prod t u) p).1 = embedVal t p.1 := by
  cases p; simp [embedVal]

private theorem embedVal_prod_snd (t u : PT) (p : (Ty.prod t u).denote) :
    (embedVal (.prod t u) p).2 = embedVal u p.2 := by
  cases p; simp [embedVal]

private theorem embedVal_nat_eq (n : ℕ) : embedVal .nat n = n := by
  simp [embedVal]

private theorem embedVal_list_length (t : PT) (l : List t.denote) :
    (embedVal (.list t) l).length = l.length := by
  simp [embedVal]

private def SimAndInv {ι : Type} {T : OracleSpec ι}
    (S : Setup) (b : QueryBudget) (c : Fin 3 → ℕ) (t : KeyIndQuery S)
    (fgShFull : fgShadowAtomicTy.denote)
    (m₁ : OracleComp T ((Ty.prod keyIndRespTy (.prod simTy fgSessCtrTy)).denote))
    (m₂ : OracleComp T ((Ty.prod keyIndRespTy simTy).denote)) : Prop :=
  (fun r => (r.1, r.2.1)) <$> m₁ = m₂ ∧
  ∀ r ∈ support m₁,
    GdhSimInv S b (bumpPred (keyIndSimPred S) c t)
      (embedVal simTy r.2.1,
        ((embedVal fgSessCtrTy r.2.2).1, ((embedVal fgSessCtrTy r.2.2).2, fgShFull.2.2)))

private theorem simAndInv_ret_none {S : Setup} {b : QueryBudget} {c : Fin 3 → ℕ} {t : KeyIndQuery S}
    {fgShFull : fgShadowAtomicTy.denote}
    {Γ₂a Γ₅a Δ₁ Γ₂b Δ₂ : List PT} [Ext Γ₂a Δ₁] [Ext Γ₅a Δ₁] [Ext Γ₂b Δ₂]
    (sm₁ : Var Γ₂a simTy) (fgSh₁ : Var Γ₅a fgSessCtrTy) (sm₂ : Var Γ₂b simTy)
    (ρ₁ : Env Δ₁) (ρ₂ : Env Δ₂)
    (hsm : (v sm₁).eval ρ₁ = (v sm₂).eval ρ₂)
    (ht0 : keyIndSimPred S 0 t = true) (ht1 : keyIndSimPred S 1 t = false)
    (hInv : GdhSimInv S b c
      (embedVal simTy ((v sm₁).eval ρ₁),
        ((embedVal fgSessCtrTy ((v fgSh₁).eval ρ₁)).1,
          ((embedVal fgSessCtrTy ((v fgSh₁).eval ρ₁)).2, fgShFull.2.2)))) :
    SimAndInv S b c t fgShFull
      ((Comp.ret (.pair _root_.SignalPqxdh.Security.ReductionDsl.KeyInd.rNone
        (.pair (v sm₁) (v fgSh₁))) : Comp pqxdhOps pqGapDhIface Δ₁ _).eval ρ₁)
      ((Comp.ret (.pair _root_.SignalPqxdh.Security.ReductionDsl.KeyInd.rNone
        (v sm₂)) : Comp pqxdhOps pqGapDhIface Δ₂ _).eval ρ₂) := by
  constructor
  · simp [Comp.eval, _root_.SignalPqxdh.Security.ReductionDsl.KeyInd.rNone, Expr.eval, map_pure, hsm]
  · intro r hr
    simp only [Comp.eval, mem_support_pure_iff, Expr.eval] at hr
    subst hr
    exact gdhSimInv_bump_noop hInv ht0 ht1

private theorem simAndInv_iteC {S : Setup} {b : QueryBudget} {c : Fin 3 → ℕ} {t : KeyIndQuery S}
    {fgShFull : fgShadowAtomicTy.denote} {Δ₁ Δ₂ : List PT}
    {b₁ : Expr pqxdhOps Δ₁ .bool} {b₂ : Expr pqxdhOps Δ₂ .bool}
    {t₁ e₁ : Comp pqxdhOps pqGapDhIface Δ₁ (.prod keyIndRespTy (.prod simTy fgSessCtrTy))}
    {t₂ e₂ : Comp pqxdhOps pqGapDhIface Δ₂ (.prod keyIndRespTy simTy)}
    {ρ₁ : Env Δ₁} {ρ₂ : Env Δ₂}
    (hb : b₁.eval ρ₁ = b₂.eval ρ₂)
    (ht : b₁.eval ρ₁ = true → SimAndInv S b c t fgShFull (t₁.eval ρ₁) (t₂.eval ρ₂))
    (he : b₁.eval ρ₁ = false → SimAndInv S b c t fgShFull (e₁.eval ρ₁) (e₂.eval ρ₂)) :
    SimAndInv S b c t fgShFull ((Comp.ite b₁ t₁ e₁).eval ρ₁) ((Comp.ite b₂ t₂ e₂).eval ρ₂) := by
  simp only [Comp.eval, ← hb]
  cases h : b₁.eval ρ₁
  · simpa using he h
  · simpa using ht h

private theorem simAndInv_caseOptV {S : Setup} {b : QueryBudget} {c : Fin 3 → ℕ} {t : KeyIndQuery S}
    {fgShFull : fgShadowAtomicTy.denote} {Δ₁ Δ₂ : List PT} {τ : PT}
    {o₁ : Expr pqxdhOps Δ₁ (.opt τ)} {o₂ : Expr pqxdhOps Δ₂ (.opt τ)}
    {n₁ : Comp pqxdhOps pqGapDhIface Δ₁ (.prod keyIndRespTy (.prod simTy fgSessCtrTy))}
    {n₂ : Comp pqxdhOps pqGapDhIface Δ₂ (.prod keyIndRespTy simTy)}
    {s₁ : Var (τ :: Δ₁) τ → Comp pqxdhOps pqGapDhIface (τ :: Δ₁) (.prod keyIndRespTy (.prod simTy fgSessCtrTy))}
    {s₂ : Var (τ :: Δ₂) τ → Comp pqxdhOps pqGapDhIface (τ :: Δ₂) (.prod keyIndRespTy simTy)}
    {ρ₁ : Env Δ₁} {ρ₂ : Env Δ₂}
    (ho : o₁.eval ρ₁ = o₂.eval ρ₂)
    (hn : SimAndInv S b c t fgShFull (n₁.eval ρ₁) (n₂.eval ρ₂))
    (hs : ∀ z, o₁.eval ρ₁ = some z →
      SimAndInv S b c t fgShFull ((s₁ .zero).eval (.cons z ρ₁)) ((s₂ .zero).eval (.cons z ρ₂))) :
    SimAndInv S b c t fgShFull ((caseOptV o₁ n₁ s₁).eval ρ₁) ((caseOptV o₂ n₂ s₂).eval ρ₂) := by
  simp only [caseOptV, Comp.eval, ← ho]
  cases h : o₁.eval ρ₁ with
  | none => exact hn
  | some z => exact hs z h

private theorem simAndInv_bindV {S : Setup} {b : QueryBudget} {c : Fin 3 → ℕ} {t : KeyIndQuery S}
    {fgShFull : fgShadowAtomicTy.denote} {Δ₁ Δ₂ : List PT} {τ : PT}
    {q₁ : Comp pqxdhOps pqGapDhIface Δ₁ τ} {q₂ : Comp pqxdhOps pqGapDhIface Δ₂ τ}
    {k₁ : Var (τ :: Δ₁) τ → Comp pqxdhOps pqGapDhIface (τ :: Δ₁) (.prod keyIndRespTy (.prod simTy fgSessCtrTy))}
    {k₂ : Var (τ :: Δ₂) τ → Comp pqxdhOps pqGapDhIface (τ :: Δ₂) (.prod keyIndRespTy simTy)}
    {ρ₁ : Env Δ₁} {ρ₂ : Env Δ₂}
    (hq : q₁.eval ρ₁ = q₂.eval ρ₂)
    (hk : ∀ z, SimAndInv S b c t fgShFull ((k₁ .zero).eval (.cons z ρ₁)) ((k₂ .zero).eval (.cons z ρ₂))) :
    SimAndInv S b c t fgShFull ((bindV q₁ k₁).eval ρ₁) ((bindV q₂ k₂).eval ρ₂) := by
  simp only [bindV, Comp.eval, hq]
  refine ⟨?_, fun r hr => ?_⟩
  · rw [map_bind]; exact bind_congr' rfl fun z => (hk z).1
  · rw [mem_support_bind_iff] at hr
    rcases hr with ⟨z, _, hrz⟩
    exact (hk z).2 r hrz

private theorem simAndInv_letV {S : Setup} {b : QueryBudget} {c : Fin 3 → ℕ} {t : KeyIndQuery S}
    {fgShFull : fgShadowAtomicTy.denote} {Δ₁ Δ₂ : List PT} {τ : PT}
    {e₁ : Expr pqxdhOps Δ₁ τ} {e₂ : Expr pqxdhOps Δ₂ τ}
    {k₁ : Var (τ :: Δ₁) τ → Comp pqxdhOps pqGapDhIface (τ :: Δ₁) (.prod keyIndRespTy (.prod simTy fgSessCtrTy))}
    {k₂ : Var (τ :: Δ₂) τ → Comp pqxdhOps pqGapDhIface (τ :: Δ₂) (.prod keyIndRespTy simTy)}
    {ρ₁ : Env Δ₁} {ρ₂ : Env Δ₂}
    (he : e₁.eval ρ₁ = e₂.eval ρ₂)
    (hk : SimAndInv S b c t fgShFull
      ((k₁ .zero).eval (.cons (e₁.eval ρ₁) ρ₁)) ((k₂ .zero).eval (.cons (e₁.eval ρ₁) ρ₂))) :
    SimAndInv S b c t fgShFull ((letV e₁ k₁).eval ρ₁) ((letV e₂ k₂).eval ρ₂) := by
  simp only [letV_eval, ← he]
  exact hk

private theorem patchAndFinishAccept_sim (S : Setup) (b : QueryBudget) (hasOpk : Bool)
    {Γ₂a Γ₃a Γ₄a Γ₅a Γ₆a Γ₇a Γp1a Γp2a Γp3a Γp4a Γssa Δ₁
     Γ₂b Γ₃b Γ₄b Γ₆b Γ₇b Γp1b Γp2b Γp3b Γp4b Γssb Δ₂ : List PT}
    [Ext Γ₂a Δ₁] [Ext Γ₃a Δ₁] [Ext Γ₄a Δ₁] [Ext Γ₅a Δ₁] [Ext Γ₆a Δ₁] [Ext Γ₇a Δ₁]
    [Ext Γp1a Δ₁] [Ext Γp2a Δ₁] [Ext Γp3a Δ₁] [Ext Γp4a Δ₁] [Ext Γssa Δ₁]
    [Ext Γ₂b Δ₂] [Ext Γ₃b Δ₂] [Ext Γ₄b Δ₂] [Ext Γ₆b Δ₂] [Ext Γ₇b Δ₂]
    [Ext Γp1b Δ₂] [Ext Γp2b Δ₂] [Ext Γp3b Δ₂] [Ext Γp4b Δ₂] [Ext Γssb Δ₂]
    (sm₁ : Var Γ₂a simTy) (bSt₁ : Var Γ₃a keyIndStateTy) (fgSh₁ : Var Γ₅a fgSessCtrTy)
    (x₁ : Var Γ₄a accQTy) (ke₁ : Var Γ₆a (.prod .nat principalEntryTy))
    (be₁ : Var Γ₇a (.prod (.prod .nat .nat) spkBundleEntryTy))
    (p1₁ : Var Γp1a fgPosTy) (p2₁ : Var Γp2a fgPosTy) (p3₁ : Var Γp3a fgPosTy)
    (p4₁ : Var Γp4a (.opt fgPosTy)) (ss₁ : Var Γssa (B 32))
    (opkPkOpt₁' : Expr pqxdhOps (.prod drKeyTy (.list fgPatchEntryTy) :: .prod drKeyTy fgListAndShadowTy :: Δ₁)
      (.opt (B 32)))
    (opks₁ : Expr pqxdhOps (.prod drKeyTy (.list fgPatchEntryTy) :: .prod drKeyTy fgListAndShadowTy :: Δ₁)
      (.list (.prod (.prod .nat (.prod .nat .nat)) opkEntryTy)))
    (usedO₁ usedN₁ : Expr pqxdhOps (.prod drKeyTy (.list fgPatchEntryTy) :: .prod drKeyTy fgListAndShadowTy :: Δ₁)
      (.list (.prod .nat (.prod .nat .nat))))
    (kyb₁ : Expr pqxdhOps (.prod drKeyTy (.list fgPatchEntryTy) :: .prod drKeyTy fgListAndShadowTy :: Δ₁)
      (.list (.prod .nat (.prod U32 (.prod U32 (B 32))))))
    (sm₂ : Var Γ₂b simTy) (bSt₂ : Var Γ₃b keyIndStateTy)
    (x₂ : Var Γ₄b accQTy) (ke₂ : Var Γ₆b (.prod .nat principalEntryTy))
    (be₂ : Var Γ₇b (.prod (.prod .nat .nat) spkBundleEntryTy))
    (p1₂ : Var Γp1b fgPosTy) (p2₂ : Var Γp2b fgPosTy) (p3₂ : Var Γp3b fgPosTy)
    (p4₂ : Var Γp4b (.opt fgPosTy)) (ss₂ : Var Γssb (B 32))
    (opkPkOpt₂ : Expr pqxdhOps (.prod drKeyTy (.list fgPatchEntryTy) :: Δ₂) (.opt (B 32)))
    (opks₂ : Expr pqxdhOps (.prod drKeyTy (.list fgPatchEntryTy) :: Δ₂)
      (.list (.prod (.prod .nat (.prod .nat .nat)) opkEntryTy)))
    (usedO₂ usedN₂ : Expr pqxdhOps (.prod drKeyTy (.list fgPatchEntryTy) :: Δ₂)
      (.list (.prod .nat (.prod .nat .nat))))
    (kyb₂ : Expr pqxdhOps (.prod drKeyTy (.list fgPatchEntryTy) :: Δ₂)
      (.list (.prod .nat (.prod U32 (.prod U32 (B 32))))))
    (env₁ : Env Δ₁) (env₂ : Env Δ₂)
    (c : Fin 3 → ℕ) (t : KeyIndQuery S) (fgShFull : fgShadowAtomicTy.denote)
    (hsm : (v sm₁).eval env₁ = (v sm₂).eval env₂)
    (hbSt : (v bSt₁).eval env₁ = ((v sm₁).eval env₁).1)
    (hbSt₂ : (v bSt₂).eval env₂ = ((v sm₂).eval env₂).1)
    (hx : (v x₁).eval env₁ = (v x₂).eval env₂)
    (hke : (v ke₁).eval env₁ = (v ke₂).eval env₂)
    (hbe : (v be₁).eval env₁ = (v be₂).eval env₂)
    (hp1 : (v p1₁).eval env₁ = (v p1₂).eval env₂)
    (hp2 : (v p2₁).eval env₁ = (v p2₂).eval env₂)
    (hp3 : (v p3₁).eval env₁ = (v p3₂).eval env₂)
    (hp4 : (v p4₁).eval env₁ = (v p4₂).eval env₂)
    (hss : (v ss₁).eval env₁ = (v ss₂).eval env₂)
    (hopkPk : ∀ pf pr, opkPkOpt₁'.eval (.cons pr (.cons pf env₁)) = opkPkOpt₂.eval (.cons pr env₂))
    (hopks : ∀ pf pr, opks₁.eval (.cons pr (.cons pf env₁)) = opks₂.eval (.cons pr env₂))
    (husedO : ∀ pf pr, usedO₁.eval (.cons pr (.cons pf env₁)) = usedO₂.eval (.cons pr env₂))
    (husedN : ∀ pf pr, usedN₁.eval (.cons pr (.cons pf env₁)) = usedN₂.eval (.cons pr env₂))
    (hkyb : ∀ pf pr, kyb₁.eval (.cons pr (.cons pf env₁)) = kyb₂.eval (.cons pr env₂))
    (hopksLen : ∀ pf pr, (opks₁.eval (.cons pr (.cons pf env₁))).length ≤ c 0 + 1)
    (husedOLen : ∀ pf pr, (usedO₁.eval (.cons pr (.cons pf env₁))).length ≤ c 0 + 1)
    (husedNLen : ∀ pf pr, (usedN₁.eval (.cons pr (.cons pf env₁))).length ≤ c 0 + 1)
    (hkybLen : ∀ pf pr, (kyb₁.eval (.cons pr (.cons pf env₁))).length ≤ c 0 + 1)
    (ht0 : keyIndSimPred S 0 t = true) (ht1 : keyIndSimPred S 1 t = false)
    (hB : ∀ j, c j ≤ keyIndSimBounds b j)
    (hRoom : ∀ j, keyIndSimPred S j t → c j + 1 ≤ keyIndSimBounds b j)
    (hInv : GdhSimInv S b c
      (embedVal simTy ((v sm₁).eval env₁),
        ((embedVal fgSessCtrTy ((v fgSh₁).eval env₁)).1,
          ((embedVal fgSessCtrTy ((v fgSh₁).eval env₁)).2, fgShFull.2.2)))) :
    let f := keyIndKFuelsOfBudget S b
    SimAndInv S b c t fgShFull
      ((bindV (fgPatchShadowC f.kFg p1₁ p2₁ p3₁ p4₁ ss₁
        (smFgL (v sm₁)) (.fst (v fgSh₁)) (.snd (v fgSh₁))) fun patchFull =>
       letV (.pair (.fst (v patchFull)) (.fst (.snd (v patchFull)))) fun patchR =>
       bindV (finishAcceptGdhC S f.kOn sm₁ bSt₁ hasOpk x₁ ke₁ be₁
         opkPkOpt₁' opks₁ usedO₁ usedN₁ kyb₁ patchR) fun accRes =>
       .ret (.pair (.fst (v accRes))
         (.pair (.snd (v accRes)) (.snd (.snd (v patchFull)))))).eval env₁)
      ((bindV (fgPatchC b.q_total p1₂ p2₂ p3₂ p4₂ ss₂ (smFgL (v sm₂))) fun patchR =>
       finishAcceptGdhC S b.q_total sm₂ bSt₂ hasOpk x₂ ke₂ be₂
         opkPkOpt₂ opks₂ usedO₂ usedN₂ kyb₂ patchR).eval env₂) := by
  intro f
  have hcOn : c 0 ≤ f.kOn := by
    have h0 := hB 0
    dsimp only [keyIndSimBounds, f, keyIndKFuelsOfBudget] at h0 ⊢
    exact h0
  have hLe : f.kOn ≤ b.q_total := Nat.min_le_right _ _
  have hProjBase : projVal keyIndStateTy (embedVal simTy ((v sm₁).eval env₁)).1 = (v bSt₁).eval env₁ := by
    rw [hbSt]; exact congrArg Prod.fst (projVal_embedVal simTy ((v sm₁).eval env₁))
  have hBaseInv : BaseOnlineLenInv c ((v bSt₁).eval env₁) := hProjBase ▸ hInv.online_len
  have hFgLEmb : ∀ s : simTy.denote, (embedVal simTy s).2.1 = embedVal (.list fgPatchEntryTy) s.2.1 := fun s => by
    rw [embedVal_prod_snd, embedVal_prod_fst]
  have hRawEmb : ∀ s : simTy.denote,
      (embedVal simTy s).2.2.1 = embedVal (.list (.prod (B 192) drKeyTy)) s.2.2.1 := fun s => by
    rw [embedVal_prod_snd, embedVal_prod_snd, embedVal_prod_fst]
  have hLogEmb : ∀ s : simTy.denote,
      (embedVal simTy s).2.2.2.1 = embedVal (.list (B 192)) s.2.2.2.1 := fun s => by
    rw [embedVal_prod_snd, embedVal_prod_snd, embedVal_prod_snd, embedVal_prod_fst]
  have hPowsEmb : ∀ s : simTy.denote,
      (embedVal simTy s).2.2.2.2 = embedVal (.list (.prod (B 32) (B 32))) s.2.2.2.2 := fun s => by
    rw [embedVal_prod_snd, embedVal_prod_snd, embedVal_prod_snd, embedVal_prod_snd]
  have hShFstEmb : ∀ sh : fgSessCtrTy.denote,
      (embedVal fgSessCtrTy sh).1 = embedVal (.list seqFgEntryTy) sh.1 := fun sh =>
    embedVal_prod_fst _ _ sh
  have hShSndEmb : ∀ sh : fgSessCtrTy.denote,
      (embedVal fgSessCtrTy sh).2 = sh.2 := fun sh => by
    rw [embedVal_prod_snd, embedVal_nat_eq]
  have hPatch := fgPatchShadowC_sim (S := S) (b := b)
    p1₁ p2₁ p3₁ p4₁ ss₁ (smFgL (v sm₁)) (.fst (v fgSh₁)) (.snd (v fgSh₁))
    p1₂ p2₂ p3₂ p4₂ ss₂ (smFgL (v sm₂)) env₁ env₂ fgShFull.2.2.1
    hp1 hp2 hp3 hp4 hss
    (by simp [smFgL, Expr.eval, hsm])
    (by have h := hInv.fgL_length_le_kFg hB; dsimp only at h; rw [hFgLEmb, embedVal_list_length] at h; exact h)
    (by have h := hInv.fgL_length_le_q_total hB; dsimp only at h; rw [hFgLEmb, embedVal_list_length] at h; exact h)
    (by have h := hInv.ctr_add_one_le_q_total hRoom; dsimp only at h; rw [hShSndEmb] at h; exact h)
    (by have h := hInv.fg_shadow; dsimp only at h; rw [hFgLEmb, hShFstEmb, hShSndEmb] at h; exact h)
  constructor
  · simp only [bindV, letV_eval, Comp.eval, map_bind, map_pure, v_zero_eval, v_eval_cons, Expr.eval]
    rw [← hPatch.1, ← bind_pure_comp, bind_assoc]
    refine bind_congr' rfl fun pf => ?_
    simp only [pure_bind]
    rw [bind_pure]
    exact finishAcceptGdhC_sim S sm₁ bSt₁ hasOpk x₁ ke₁ be₁ opkPkOpt₁' opks₁ usedO₁ usedN₁ kyb₁ .zero
      sm₂ bSt₂ x₂ ke₂ be₂ opkPkOpt₂ opks₂ usedO₂ usedN₂ kyb₂ .zero _ _
      (by simp [hsm]) (by simp [hbSt, hbSt₂, hsm]) (by simp [hx]) (by simp [hke]) (by simp [hbe])
      (hopkPk pf (pf.1, pf.2.1)) (hopks pf (pf.1, pf.2.1)) (husedO pf (pf.1, pf.2.1))
      (husedN pf (pf.1, pf.2.1)) (hkyb pf (pf.1, pf.2.1)) (by simp)
      (by simpa using hBaseInv) hcOn hLe
  · intro r hr
    simp only [bindV, letV_eval, Comp.eval, mem_support_bind_iff, mem_support_pure_iff,
      v_zero_eval, v_eval_cons, Expr.eval] at hr
    rcases hr with ⟨pf, hpf, accRes, hacc, rfl⟩
    obtain ⟨hSessLen, hSh'⟩ := hPatch.2 pf hpf
    obtain ⟨hPrin', hSpks', hOpks', hSess', hResps', hUsedO', hUsedN', hKyb', hAdv', hFgL', hRest'⟩ :=
      mem_support_finishAcceptGdhC S f.kOn hasOpk sm₁ bSt₁ x₁ ke₁ be₁
        opkPkOpt₁' opks₁ usedO₁ usedN₁ kyb₁ .zero _ hacc
    have hc0' : bumpPred (keyIndSimPred S) c t 0 = c 0 + 1 := by simp [bumpPred, ht0]
    have hc1' : bumpPred (keyIndSimPred S) c t 1 = c 1 := by simp [bumpPred, ht1]
    have hSum' : bumpPred (keyIndSimPred S) c t 0 + bumpPred (keyIndSimPred S) c t 1 =
        bumpPred (keyIndSimPred S) c t 2 :=
      Computational.Proofs.SignalPqxdh.Security.ReductionDsl.KindSplit.KeyIndCoreKSimBase.bumpPred_keyIndSimPred_sum
        t hInv.online_len.counts_eq
    have hProjOut : projVal keyIndStateTy (embedVal simTy accRes.2).1 = accRes.2.1 :=
      congrArg Prod.fst (projVal_embedVal simTy accRes.2)
    refine
      { online_len := ?_
        fg_sess_le := ?_
        fg_shadow  := ?_
        raw_len    := ?_
        raw_shadow := ?_
        log_len    := ?_
        pows_len   := ?_ }
    · rw [hProjOut]
      refine
        { prin_le   := by rw [hPrin', hc0']; exact Nat.le_succ_of_le hBaseInv.prin_le
          spks_le   := by rw [hSpks', hc0']; exact Nat.le_succ_of_le hBaseInv.spks_le
          opks_le   := by rw [hOpks', hc0']; exact hopksLen pf (pf.1, pf.2.1)
          sess_le   := by rw [hSess', hc0']; exact Nat.le_succ_of_le hBaseInv.sess_le
          resps_le  := by rw [hResps', hc0']; exact Nat.add_le_add_right hBaseInv.resps_le 1
          usedO_le  := by rw [hUsedO', hc0']; exact husedOLen pf (pf.1, pf.2.1)
          usedN_le  := by rw [hUsedN', hc0']; exact husedNLen pf (pf.1, pf.2.1)
          kyb_le    := by rw [hKyb', hc0']; exact hkybLen pf (pf.1, pf.2.1)
          adv_le    := by rw [hAdv', hc0']; exact Nat.le_succ_of_le hBaseInv.adv_le
          counts_eq := hSum' }
    · dsimp only
      rw [hShFstEmb, hc0']
      have hOldSess : (embedVal (.list seqFgEntryTy) ((v fgSh₁).eval env₁).1).length ≤ c 0 := by
        have h := hInv.fg_sess_le; dsimp only at h; rwa [hShFstEmb] at h
      exact Nat.le_trans hSessLen (Nat.add_le_add_right hOldSess 1)
    · dsimp only
      rw [hFgLEmb, hShFstEmb, hShSndEmb, hc1', show accRes.2.2.1 = pf.2.1 from hFgL']
      exact hSh'
    · dsimp only
      rw [hRawEmb, hc1', show accRes.2.2.2 = ((v sm₁).eval env₁).2.2 from hRest']
      have h := hInv.raw_len; dsimp only at h; rwa [hRawEmb] at h
    · dsimp only
      rw [hRawEmb, show accRes.2.2.2 = ((v sm₁).eval env₁).2.2 from hRest']
      have h := hInv.raw_shadow; dsimp only at h; rwa [hRawEmb] at h
    · dsimp only
      rw [hLogEmb, hc1', show accRes.2.2.2 = ((v sm₁).eval env₁).2.2 from hRest']
      have h := hInv.log_len; dsimp only at h; rwa [hLogEmb] at h
    · dsimp only
      rw [hPowsEmb, hc0', show accRes.2.2.2 = ((v sm₁).eval env₁).2.2 from hRest']
      have h := hInv.pows_len; dsimp only at h; rw [hPowsEmb] at h
      exact Nat.le_succ_of_le h

private theorem eqU32_eval_congr {Γ₁ Γ₂ : List PT}
    (a₁ b₁ : Expr pqxdhOps Γ₁ U32) (a₂ b₂ : Expr pqxdhOps Γ₂ U32)
    (env₁ : Env Γ₁) (env₂ : Env Γ₂)
    (ha : a₁.eval env₁ = a₂.eval env₂) (hb : b₁.eval env₁ = b₂.eval env₂) :
    (eqU32 a₁ b₁).eval env₁ = (eqU32 a₂ b₂).eval env₂ := by
  simp only [eqU32, Expr.eval]; exact congrArg (pqxdhOps.eval _) (Prod.ext ha hb)

private theorem optU32Eq_eval_congr {Γ₁ Γ₂ : List PT}
    (a₁ b₁ : Expr pqxdhOps Γ₁ (.opt U32)) (a₂ b₂ : Expr pqxdhOps Γ₂ (.opt U32))
    (env₁ : Env Γ₁) (env₂ : Env Γ₂)
    (ha : a₁.eval env₁ = a₂.eval env₂) (hb : b₁.eval env₁ = b₂.eval env₂) :
    (optU32Eq a₁ b₁).eval env₁ = (optU32Eq a₂ b₂).eval env₂ := by
  simp only [optU32Eq, _root_.SignalPqxdh.Security.ReductionDsl.KeyInd.eLet2, eLet,
    eCaseOpt, Expr.eval, v_zero_eval, v_eval_cons]
  cases ha2 : a₂.eval env₂ <;> cases hb2 : b₂.eval env₂ <;>
    simp only [ha.trans ha2, hb.trans hb2]
  exact eqU32_eval_congr _ _ _ _ _ _ (by simp) (by simp)

private theorem u32OfNat_eval_congr {Γ₁ Γ₂ : List PT}
    (e₁ : Expr pqxdhOps Γ₁ .nat) (e₂ : Expr pqxdhOps Γ₂ .nat)
    (env₁ : Env Γ₁) (env₂ : Env Γ₂) (he : e₁.eval env₁ = e₂.eval env₂) :
    (u32OfNat e₁).eval env₁ = (u32OfNat e₂).eval env₂ := by
  simp only [u32OfNat, Expr.eval]; exact congrArg (pqxdhOps.eval _) he

private theorem lenB_eval_congr {n : PNat} {Γ₁ Γ₂ : List PT}
    (e₁ : Expr pqxdhOps Γ₁ (B n)) (e₂ : Expr pqxdhOps Γ₂ (B n))
    (env₁ : Env Γ₁) (env₂ : Env Γ₂) (he : e₁.eval env₁ = e₂.eval env₂) :
    (lenB e₁).eval env₁ = (lenB e₂).eval env₂ := by
  simp only [lenB, Expr.eval]; exact congrArg (pqxdhOps.eval _) he

private theorem natEq_eval_congr {Γ₁ Γ₂ : List PT}
    (a₁ b₁ : Expr pqxdhOps Γ₁ .nat) (a₂ b₂ : Expr pqxdhOps Γ₂ .nat)
    (env₁ : Env Γ₁) (env₂ : Env Γ₂)
    (ha : a₁.eval env₁ = a₂.eval env₂) (hb : b₁.eval env₁ = b₂.eval env₂) :
    (natEq a₁ b₁).eval env₁ = (natEq a₂ b₂).eval env₂ := by
  simp only [natEq, Expr.eval, ha, hb]

private theorem nat2Eq_eval_congr {Γ₁ Γ₂ : List PT}
    (a₁ b₁ : Expr pqxdhOps Γ₁ (.prod .nat .nat))
    (a₂ b₂ : Expr pqxdhOps Γ₂ (.prod .nat .nat))
    (env₁ : Env Γ₁) (env₂ : Env Γ₂)
    (ha : a₁.eval env₁ = a₂.eval env₂) (hb : b₁.eval env₁ = b₂.eval env₂) :
    (nat2Eq a₁ b₁).eval env₁ = (nat2Eq a₂ b₂).eval env₂ :=
  congrArg₂ Bool.and
    (natEq_eval_congr _ _ _ _ env₁ env₂ (congrArg Prod.fst ha) (congrArg Prod.fst hb))
    (natEq_eval_congr _ _ _ _ env₁ env₂ (congrArg Prod.snd ha) (congrArg Prod.snd hb))

private theorem nat3Eq_eval_congr {Γ₁ Γ₂ : List PT}
    (a₁ b₁ : Expr pqxdhOps Γ₁ (.prod .nat (.prod .nat .nat)))
    (a₂ b₂ : Expr pqxdhOps Γ₂ (.prod .nat (.prod .nat .nat)))
    (env₁ : Env Γ₁) (env₂ : Env Γ₂)
    (ha : a₁.eval env₁ = a₂.eval env₂) (hb : b₁.eval env₁ = b₂.eval env₂) :
    (nat3Eq a₁ b₁).eval env₁ = (nat3Eq a₂ b₂).eval env₂ :=
  congrArg₂ Bool.and
    (natEq_eval_congr _ _ _ _ env₁ env₂ (congrArg Prod.fst ha) (congrArg Prod.fst hb))
    (nat2Eq_eval_congr _ _ _ _ env₁ env₂ (congrArg Prod.snd ha) (congrArg Prod.snd hb))

private theorem ite_eval_congr {Γ₁ Γ₂ : List PT} {τ : PT}
    (c₁ : Expr pqxdhOps Γ₁ .bool) (t₁ e₁ : Expr pqxdhOps Γ₁ τ)
    (c₂ : Expr pqxdhOps Γ₂ .bool) (t₂ e₂ : Expr pqxdhOps Γ₂ τ)
    (env₁ : Env Γ₁) (env₂ : Env Γ₂)
    (hc : c₁.eval env₁ = c₂.eval env₂)
    (ht : t₁.eval env₁ = t₂.eval env₂)
    (he : e₁.eval env₁ = e₂.eval env₂) :
    (Expr.ite c₁ t₁ e₁).eval env₁ = (Expr.ite c₂ t₂ e₂).eval env₂ :=
  congr (congr (congrArg (fun (b : Bool) (x y : τ.denote) => if b = true then x else y) hc) ht) he

private theorem eMap_length_le {Γ : List PT} {τ₁ τ₂ : PT} {K : ℕ}
    (xs : Expr pqxdhOps Γ (.list τ₁))
    (f : Var (τ₁ :: Γ) τ₁ → Expr pqxdhOps (τ₁ :: Γ) τ₂) (env : Env Γ) :
    ((eMap K xs f).eval env).length ≤ (xs.eval env).length := by
  simp only [eMap, Expr.eval, List.length_map, List.length_take]
  exact Nat.min_le_right _ _

open _root_.SignalPqxdh.Security.ReductionDsl.KeyInd (qHdr qK qJ qO qKJO rNone) in
private def acceptOpkGdhRefCoreB (S : Setup) (K : Nat) {τpa : PT}
    (getOpkM : ∀ {Γ : List PT}, Expr pqxdhOps Γ τpa → Expr pqxdhOps Γ .bool)
    {Γ₁ Γ₂ Γ₃ Γ₄ Δ : List PT}
    [Ext Γ₁ Δ] [Ext Γ₂ Δ] [Ext Γ₃ Δ] [Ext Γ₄ Δ]
    (pa : Var Γ₁ τpa) (sm : Var Γ₂ simTy) (bSt : Var Γ₃ keyIndStateTy)
    (x : Var Γ₄ accQTy) :
    Comp pqxdhOps pqGapDhIface Δ (.prod keyIndRespTy simTy) :=
  let hdr := qHdr (v x)
  let guardOk := Expr.and
    (.and (.and (.and (eqU32 (hdSpkId hdr) (u32OfNat (qJ (v x))))
                      (eqU32 (hdPqspkId hdr) (u32OfNat (qJ (v x)))))
                (optU32Eq (hdOpkId hdr) (.some (u32OfNat (qO (v x))))))
          (natEq (lenB (hdIkAPk hdr)) (.nat 32)))
    (natEq (lenB (hdEkAPk hdr)) (.nat 32))
  .ite (.not guardOk) (.ret (.pair rNone (v sm)))
    (.ite (eAny K (stUsedO (v bSt)) fun u => nat3Eq (v u) (qKJO (v x)))
      (.ret (.pair rNone (v sm)))
      (bindV (gPrim (koskSenderOkPowsC S K bSt (smPows (v sm)) (hdIkAPk (qHdr (v x))))) fun sOk =>
       .ite (.not (v sOk)) (.ret (.pair rNone (v sm)))
         (caseOptV (eFind K (stPrin (v bSt)) fun p => natEq (.fst (v p)) (qK (v x)))
           (.ret (.pair rNone (v sm)))
           fun ke =>
             caseOptV (eFind K (stSpks (v bSt)) fun p =>
               nat2Eq (.fst (v p)) (.pair (qK (v x)) (qJ (v x))))
               (.ret (.pair rNone (v sm)))
               fun be =>
                 caseOptV (eFind K (stOpks (v bSt)) fun p => nat3Eq (.fst (v p)) (qKJO (v x)))
                   (.ret (.pair rNone (v sm)))
                   fun oe =>
                     .ite (oeConsumed (.snd (v oe))) (.ret (.pair rNone (v sm)))
                       (letV (kyberCheckE K (stKyb (v bSt)) (.pair (qK (v x))
                         (.pair (hdPqspkId (qHdr (v x)))
                           (.pair (hdSpkId (qHdr (v x))) (hdEkAPk (qHdr (v x))))))) fun kybR =>
                        bindV (gPrim (qIsCanonical (hdEkAPk (qHdr (v x))))) fun canon =>
                        bindV (gPrim (qX25519 (.pair (litB 32 (List.replicate 32 0))
                          (hdIkAPk (qHdr (v x)))))) fun dh1Z =>
                        bindV (gPrim (qX25519 (.pair (litB 32 (List.replicate 32 0))
                          (hdEkAPk (qHdr (v x)))))) fun dh2Z =>
                        .ite (getOpkM (v pa))
                          (bindV (gPrim (qKemDecaps (.pair (sbPqspkSk (.snd (v be)))
                            (hdKemCt (qHdr (v x)))))) fun ssOpt =>
                           .ite (.not (.and (.and (.and (.fst (v kybR)) (v canon))
                             (nonZero32 (v dh1Z))) (nonZero32 (v dh2Z))))
                             (.ret (.pair rNone (v sm)))
                             (caseOptV (v ssOpt) (.ret (.pair rNone (v sm))) fun ss =>
                               bindV (computePosC (litB 32 []) (sbSpkSk (.snd (v be)))
                                 (hdIkAPk (qHdr (v x))) (sbSpkPk (.snd (v be)))) fun p1 =>
                               bindV (computePosC (litB 32 []) (peSecIKA0 (.snd (v ke)))
                                 (hdEkAPk (qHdr (v x))) (peIkAPk (.snd (v ke)))) fun p2 =>
                               bindV (computePosC (litB 32 []) (sbSpkSk (.snd (v be)))
                                 (hdEkAPk (qHdr (v x))) (sbSpkPk (.snd (v be)))) fun p3 =>
                               bindV (computePosC (litB 32 []) (oeOpkSk (.snd (v oe)))
                                 (hdEkAPk (qHdr (v x))) (oeOpkPk (.snd (v oe)))) fun p4Raw =>
                               letV (.some (v p4Raw)) fun p4 =>
                               bindV (fgPatchC K p1 p2 p3 p4 ss (smFgL (v sm))) fun patchR =>
                               let opks' := eMap K (stOpks (v bSt)) fun p =>
                                 .ite (nat3Eq (.fst (v p)) (qKJO (v x)))
                                   (.pair (.fst (v p))
                                     (oeUpd (.snd (v p)) (consumed := .bool true)))
                                   (v p)
                               finishAcceptGdhC S K sm bSt true x ke be
                                 (.some (oeOpkPk (.snd (v oe)))) opks'
                                 (.cons (qKJO (v x)) (stUsedO (v bSt)))
                                 (stUsedN (v bSt)) (.snd (v kybR)) patchR))
                          (bindV (gPrim (qX25519 (.pair (oeOpkSk (.snd (v oe)))
                            (hdEkAPk (qHdr (v x)))))) fun dh4 =>
                           bindV (gPrim (qKemDecaps (.pair (sbPqspkSk (.snd (v be)))
                             (hdKemCt (qHdr (v x)))))) fun ssOpt =>
                           .ite (.not (.and (.and (.and (.and (.fst (v kybR)) (v canon))
                             (nonZero32 (v dh1Z))) (nonZero32 (v dh2Z))) (nonZero32 (v dh4))))
                             (.ret (.pair rNone (v sm)))
                             (caseOptV (v ssOpt) (.ret (.pair rNone (v sm))) fun ss =>
                               bindV (computePosC (litB 32 []) (sbSpkSk (.snd (v be)))
                                 (hdIkAPk (qHdr (v x))) (sbSpkPk (.snd (v be)))) fun p1 =>
                               bindV (computePosC (litB 32 []) (peSecIKA0 (.snd (v ke)))
                                 (hdEkAPk (qHdr (v x))) (peIkAPk (.snd (v ke)))) fun p2 =>
                               bindV (computePosC (litB 32 []) (sbSpkSk (.snd (v be)))
                                 (hdEkAPk (qHdr (v x))) (sbSpkPk (.snd (v be)))) fun p3 =>
                               bindV (mkSecretPosC (v dh4)) fun p4Raw =>
                               letV (.some (v p4Raw)) fun p4 =>
                               bindV (fgPatchC K p1 p2 p3 p4 ss (smFgL (v sm))) fun patchR =>
                               let opks' := eMap K (stOpks (v bSt)) fun p =>
                                 .ite (nat3Eq (.fst (v p)) (qKJO (v x)))
                                   (.pair (.fst (v p))
                                     (oeUpd (.snd (v p)) (consumed := .bool true)))
                                   (v p)
                               finishAcceptGdhC S K sm bSt true x ke be
                                 (.some (oeOpkPk (.snd (v oe)))) opks'
                                 (.cons (qKJO (v x)) (stUsedO (v bSt)))
                                 (stUsedN (v bSt)) (.snd (v kybR)) patchR))))))

private theorem acceptOpkGdhCoreShadowB_sim (S : Setup) (b : QueryBudget) {τpa : PT}
    (getOpkM : ∀ {Γ : List PT}, Expr pqxdhOps Γ τpa → Expr pqxdhOps Γ .bool)
    (evalOpkM : τpa.denote → Bool)
    (hGetOpkM : ∀ {Γ : List PT} (e : Expr pqxdhOps Γ τpa) (ρ : Env Γ),
      (getOpkM e).eval ρ = evalOpkM (e.eval ρ))
    {Γ₁a Γ₂a Γ₃a Γ₄a Γ₅a Δ₁ Γ₁b Γ₂b Γ₃b Γ₄b Δ₂ : List PT}
    [Ext Γ₁a Δ₁] [Ext Γ₂a Δ₁] [Ext Γ₃a Δ₁] [Ext Γ₄a Δ₁] [Ext Γ₅a Δ₁]
    [Ext Γ₁b Δ₂] [Ext Γ₂b Δ₂] [Ext Γ₃b Δ₂] [Ext Γ₄b Δ₂]
    (opkM₁ : Var Γ₁a .bool) (sm₁ : Var Γ₂a simTy) (bSt₁ : Var Γ₃a keyIndStateTy)
    (fgSh₁ : Var Γ₅a fgSessCtrTy) (x₁ : Var Γ₄a accQTy)
    (pa₂ : Var Γ₁b τpa) (sm₂ : Var Γ₂b simTy) (bSt₂ : Var Γ₃b keyIndStateTy)
    (x₂ : Var Γ₄b accQTy)
    (env₁ : Env Δ₁) (env₂ : Env Δ₂)
    (c : Fin 3 → ℕ) (t : KeyIndQuery S)
    (fgShFull : fgShadowAtomicTy.denote)
    (hopkM : (v opkM₁).eval env₁ = evalOpkM ((v pa₂).eval env₂))
    (hsm : (v sm₁).eval env₁ = (v sm₂).eval env₂)
    (hbSt : (v bSt₁).eval env₁ = ((v sm₁).eval env₁).1)
    (hbSt₂ : (v bSt₂).eval env₂ = ((v sm₂).eval env₂).1)
    (hx : (v x₁).eval env₁ = (v x₂).eval env₂)
    (ht0 : keyIndSimPred S 0 t = true)
    (ht1 : keyIndSimPred S 1 t = false)
    (hB : ∀ j, c j ≤ keyIndSimBounds b j)
    (hRoom : ∀ j, keyIndSimPred S j t → c j + 1 ≤ keyIndSimBounds b j)
    (hInv : GdhSimInv S b c
      (embedVal simTy ((v sm₁).eval env₁),
        ((embedVal fgSessCtrTy ((v fgSh₁).eval env₁)).1,
          ((embedVal fgSessCtrTy ((v fgSh₁).eval env₁)).2, fgShFull.2.2)))) :
    SimAndInv S b c t fgShFull
      ((acceptOpkGdhCoreShadowB S (keyIndKFuelsOfBudget S b) opkM₁ sm₁ bSt₁ fgSh₁ x₁).eval env₁)
      ((acceptOpkGdhRefCoreB S b.q_total getOpkM pa₂ sm₂ bSt₂ x₂).eval env₂) := by
  let f := keyIndKFuelsOfBudget S b
  have hcOn : c 0 ≤ f.kOn := by
    have h0 := hB 0; dsimp only [keyIndSimBounds, f, keyIndKFuelsOfBudget] at h0 ⊢; exact h0
  have hLe : f.kOn ≤ b.q_total := Nat.min_le_right _ _
  have hProjBase : projVal keyIndStateTy (embedVal simTy ((v sm₁).eval env₁)).1 = (v bSt₁).eval env₁ := by
    rw [hbSt]; exact congrArg Prod.fst (projVal_embedVal simTy ((v sm₁).eval env₁))
  have hBaseInv : BaseOnlineLenInv c ((v bSt₁).eval env₁) := hProjBase ▸ hInv.online_len
  have hbStEq : (v bSt₁).eval env₁ = (v bSt₂).eval env₂ := by rw [hbSt, hbSt₂, hsm]
  have hPowsLen : ((smPows (v sm₁)).eval env₁).length ≤ f.kOn := by
    have h := hInv.pows_len; dsimp only at h
    rw [embedVal_prod_snd, embedVal_prod_snd, embedVal_prod_snd, embedVal_prod_snd, embedVal_list_length] at h
    exact Nat.le_trans h hcOn
  unfold acceptOpkGdhCoreShadowB acceptOpkGdhRefCoreB
  refine simAndInv_iteC
    (by
      have hOpt := optU32Eq_eval_congr
        (hdOpkId (_root_.SignalPqxdh.Security.ReductionDsl.KeyInd.qHdr (v x₁)))
        (.some (u32OfNat (_root_.SignalPqxdh.Security.ReductionDsl.KeyInd.qO (v x₁))))
        (hdOpkId (_root_.SignalPqxdh.Security.ReductionDsl.KeyInd.qHdr (v x₂)))
        (.some (u32OfNat (_root_.SignalPqxdh.Security.ReductionDsl.KeyInd.qO (v x₂)))) env₁ env₂
        (by simp [_root_.SignalPqxdh.Security.ReductionDsl.KeyInd.qHdr, Expr.eval, hx])
        (by simp only [Expr.eval]; exact congrArg some (u32OfNat_eval_congr _ _ _ _
          (by simp [_root_.SignalPqxdh.Security.ReductionDsl.KeyInd.qO, Expr.eval, hx])))
      have hJ := u32OfNat_eval_congr
        (_root_.SignalPqxdh.Security.ReductionDsl.KeyInd.qJ (v x₁))
        (_root_.SignalPqxdh.Security.ReductionDsl.KeyInd.qJ (v x₂)) env₁ env₂
        (by simp [_root_.SignalPqxdh.Security.ReductionDsl.KeyInd.qJ, Expr.eval, hx])
      have hL1 := lenB_eval_congr
        (hdIkAPk (_root_.SignalPqxdh.Security.ReductionDsl.KeyInd.qHdr (v x₁)))
        (hdIkAPk (_root_.SignalPqxdh.Security.ReductionDsl.KeyInd.qHdr (v x₂))) env₁ env₂
        (by simp [_root_.SignalPqxdh.Security.ReductionDsl.KeyInd.qHdr, Expr.eval, hx])
      have hL2 := lenB_eval_congr
        (hdEkAPk (_root_.SignalPqxdh.Security.ReductionDsl.KeyInd.qHdr (v x₁)))
        (hdEkAPk (_root_.SignalPqxdh.Security.ReductionDsl.KeyInd.qHdr (v x₂))) env₁ env₂
        (by simp [_root_.SignalPqxdh.Security.ReductionDsl.KeyInd.qHdr, Expr.eval, hx])
      have hEq1 := eqU32_eval_congr
        (hdSpkId (_root_.SignalPqxdh.Security.ReductionDsl.KeyInd.qHdr (v x₁)))
        (u32OfNat (_root_.SignalPqxdh.Security.ReductionDsl.KeyInd.qJ (v x₁)))
        (hdSpkId (_root_.SignalPqxdh.Security.ReductionDsl.KeyInd.qHdr (v x₂)))
        (u32OfNat (_root_.SignalPqxdh.Security.ReductionDsl.KeyInd.qJ (v x₂))) env₁ env₂
        (by simp [_root_.SignalPqxdh.Security.ReductionDsl.KeyInd.qHdr, Expr.eval, hx]) hJ
      have hEq2 := eqU32_eval_congr
        (hdPqspkId (_root_.SignalPqxdh.Security.ReductionDsl.KeyInd.qHdr (v x₁)))
        (u32OfNat (_root_.SignalPqxdh.Security.ReductionDsl.KeyInd.qJ (v x₁)))
        (hdPqspkId (_root_.SignalPqxdh.Security.ReductionDsl.KeyInd.qHdr (v x₂)))
        (u32OfNat (_root_.SignalPqxdh.Security.ReductionDsl.KeyInd.qJ (v x₂))) env₁ env₂
        (by simp [_root_.SignalPqxdh.Security.ReductionDsl.KeyInd.qHdr, Expr.eval, hx]) hJ
      simp only [natEq, Expr.eval]
      rw [hEq1, hEq2, hOpt, hL1, hL2]; rfl)
    (fun _ => simAndInv_ret_none sm₁ fgSh₁ sm₂ _ _ hsm ht0 ht1 hInv) fun _ => ?_
  refine simAndInv_iteC
    (eAny_congr_le _ _ _ _ _ _ (by simp [Expr.eval, hbStEq])
      (by simpa [stUsedOList, Expr.eval] using Nat.le_trans hBaseInv.usedO_le hcOn) hLe fun u =>
      nat3Eq_eval_congr _ _ _ _ _ _ (by simp only [v_zero_eval])
        (by simp only [_root_.SignalPqxdh.Security.ReductionDsl.KeyInd.qKJO,
          _root_.SignalPqxdh.Security.ReductionDsl.KeyInd.qK,
          _root_.SignalPqxdh.Security.ReductionDsl.KeyInd.qJ,
          _root_.SignalPqxdh.Security.ReductionDsl.KeyInd.qO, Expr.eval, v_eval_cons, hx]))
    (fun _ => simAndInv_ret_none sm₁ fgSh₁ sm₂ _ _ hsm ht0 ht1 hInv) fun _ => ?_
  refine simAndInv_bindV
    (liftBase_eval_congr _ _ _ _
      (koskSenderOkPowsC_sim S bSt₁ _ _ bSt₂ _ _ _ _ hbStEq
        (by simp [smPows, Expr.eval, hsm])
        (by simp [_root_.SignalPqxdh.Security.ReductionDsl.KeyInd.qHdr, Expr.eval, hx])
        (Nat.le_trans hBaseInv.prin_le hcOn) hPowsLen hLe)) fun sOk => ?_
  refine simAndInv_iteC rfl
    (fun _ => simAndInv_ret_none sm₁ fgSh₁ sm₂ _ _ (by simp [hsm]) ht0 ht1 (by simpa using hInv)) fun _ => ?_
  refine simAndInv_caseOptV
    (eFind_congr_le _ _ _ _ _ _ (by simp [Expr.eval, hbStEq])
      (by simpa [stPrinList, Expr.eval] using Nat.le_trans hBaseInv.prin_le hcOn) hLe fun p =>
      natEq_eval_congr _ _ _ _ _ _ (by simp only [Expr.eval, v_zero_eval])
        (by simp only [_root_.SignalPqxdh.Security.ReductionDsl.KeyInd.qK,
          Expr.eval, v_eval_cons, hx]))
    (simAndInv_ret_none sm₁ fgSh₁ sm₂ _ _ (by simp [hsm]) ht0 ht1 (by simpa using hInv)) fun ke _ => ?_
  refine simAndInv_caseOptV
    (eFind_congr_le _ _ _ _ _ _ (by simp [Expr.eval, hbStEq])
      (by simpa [stSpksList, Expr.eval] using Nat.le_trans hBaseInv.spks_le hcOn) hLe fun p =>
      nat2Eq_eval_congr _ _ _ _ _ _ (by simp only [Expr.eval, v_zero_eval])
        (by simp only [_root_.SignalPqxdh.Security.ReductionDsl.KeyInd.qK,
          _root_.SignalPqxdh.Security.ReductionDsl.KeyInd.qJ, Expr.eval, v_eval_cons, hx]))
    (simAndInv_ret_none sm₁ fgSh₁ sm₂ _ _ (by simp [hsm]) ht0 ht1 (by simpa using hInv)) fun be _ => ?_
  refine simAndInv_caseOptV
    (eFind_congr_le _ _ _ _ _ _ (by simp [Expr.eval, hbStEq])
      (by simpa [stOpksList, Expr.eval] using Nat.le_trans hBaseInv.opks_le hcOn) hLe fun p =>
      nat3Eq_eval_congr _ _ _ _ _ _ (by simp only [Expr.eval, v_zero_eval])
        (by simp only [_root_.SignalPqxdh.Security.ReductionDsl.KeyInd.qKJO,
          _root_.SignalPqxdh.Security.ReductionDsl.KeyInd.qK,
          _root_.SignalPqxdh.Security.ReductionDsl.KeyInd.qJ,
          _root_.SignalPqxdh.Security.ReductionDsl.KeyInd.qO, Expr.eval, v_eval_cons, hx]))
    (simAndInv_ret_none sm₁ fgSh₁ sm₂ _ _ (by simp [hsm]) ht0 ht1 (by simpa using hInv)) fun oe _ => ?_
  refine simAndInv_iteC rfl
    (fun _ => simAndInv_ret_none sm₁ fgSh₁ sm₂ _ _ (by simp [hsm]) ht0 ht1 (by simpa using hInv)) fun _ => ?_
  have hKybLen := Nat.le_trans
    (kyberCheckE_snd_length_le (K := f.kOn) (stKyb (v bSt₁))
      (.pair (_root_.SignalPqxdh.Security.ReductionDsl.KeyInd.qK (v x₁))
        (.pair (hdPqspkId (_root_.SignalPqxdh.Security.ReductionDsl.KeyInd.qHdr (v x₁)))
          (.pair (hdSpkId (_root_.SignalPqxdh.Security.ReductionDsl.KeyInd.qHdr (v x₁)))
            (hdEkAPk (_root_.SignalPqxdh.Security.ReductionDsl.KeyInd.qHdr (v x₁))))))
      (.cons oe (.cons be (.cons ke (.cons sOk env₁)))))
    (Nat.add_le_add_right (by simpa [stKybList, Expr.eval] using hBaseInv.kyb_le) 1)
  refine simAndInv_letV
    (kyberCheckE_sim _ _ _ _ _ _ (by simp [Expr.eval, hbStEq])
      (by simp [_root_.SignalPqxdh.Security.ReductionDsl.KeyInd.qK,
        _root_.SignalPqxdh.Security.ReductionDsl.KeyInd.qHdr, Expr.eval, hx])
      (by simpa [stKybList, Expr.eval] using Nat.le_trans hBaseInv.kyb_le hcOn) hLe) ?_
  refine simAndInv_bindV
    (liftBase_eval_congr _ _ _ _
      (qIsCanonical_eval_congr _ _ _ _
        (by simp [_root_.SignalPqxdh.Security.ReductionDsl.KeyInd.qHdr, Expr.eval, hx]))) fun canon => ?_
  refine simAndInv_bindV
    (liftBase_eval_congr _ _ _ _
      (qX25519_eval_congr _ _ _ _
        (by simp [_root_.SignalPqxdh.Security.ReductionDsl.KeyInd.qHdr, Expr.eval, hx]))) fun dh1Z => ?_
  refine simAndInv_bindV
    (liftBase_eval_congr _ _ _ _
      (qX25519_eval_congr _ _ _ _
        (by simp [_root_.SignalPqxdh.Security.ReductionDsl.KeyInd.qHdr, Expr.eval, hx]))) fun dh2Z => ?_
  refine simAndInv_iteC
    (by rw [hGetOpkM]; simp only [v_eval_cons]; exact hopkM)
    (fun _ => ?_) (fun _ => ?_)
  · refine simAndInv_bindV
      (liftBase_eval_congr _ _ _ _
        (qKemDecaps_eval_congr _ _ _ _
          (by simp [_root_.SignalPqxdh.Security.ReductionDsl.KeyInd.qHdr, Expr.eval, hx]))) fun ssOpt => ?_
    refine simAndInv_iteC (by simp [nonZero32, eqB, litB, Expr.eval])
      (fun _ => simAndInv_ret_none sm₁ fgSh₁ sm₂ _ _ (by simp [hsm]) ht0 ht1 (by simpa using hInv)) fun _ => ?_
    refine simAndInv_caseOptV rfl
      (simAndInv_ret_none sm₁ fgSh₁ sm₂ _ _ (by simp [hsm]) ht0 ht1 (by simpa using hInv)) fun ss _ => ?_
    refine simAndInv_bindV
      (computePosC_congr _ _ _ _ _ _ _ _ _ _ rfl (by simp [Expr.eval])
        (by simp [_root_.SignalPqxdh.Security.ReductionDsl.KeyInd.qHdr, Expr.eval, hx])
        (by simp [Expr.eval])) fun p1 => ?_
    refine simAndInv_bindV
      (computePosC_congr _ _ _ _ _ _ _ _ _ _ rfl (by simp [Expr.eval])
        (by simp [_root_.SignalPqxdh.Security.ReductionDsl.KeyInd.qHdr, Expr.eval, hx])
        (by simp [Expr.eval])) fun p2 => ?_
    refine simAndInv_bindV
      (computePosC_congr _ _ _ _ _ _ _ _ _ _ rfl (by simp [Expr.eval])
        (by simp [_root_.SignalPqxdh.Security.ReductionDsl.KeyInd.qHdr, Expr.eval, hx])
        (by simp [Expr.eval])) fun p3 => ?_
    refine simAndInv_bindV
      (computePosC_congr _ _ _ _ _ _ _ _ _ _ rfl (by simp [Expr.eval])
        (by simp [_root_.SignalPqxdh.Security.ReductionDsl.KeyInd.qHdr, Expr.eval, hx])
        (by simp [Expr.eval])) fun p4Raw => ?_
    refine simAndInv_letV rfl ?_
    exact patchAndFinishAccept_sim S b true sm₁ bSt₁ fgSh₁ x₁ .zero .zero
      .zero .zero .zero .zero .zero _ _ _ _ _
      sm₂ bSt₂ x₂ .zero .zero .zero .zero .zero .zero .zero _ _ _ _ _
      _ _ c t fgShFull
      (by simp [hsm]) (by simp [hbSt]) (by simp [hbSt₂]) (by simp [hx]) (by simp) (by simp)
      (by simp) (by simp) (by simp) (by simp) (by simp)
      (fun _ _ => by simp [Expr.eval])
      (fun _ _ => eMap_congr_le _ _ _ _ _ _ (by simp [Expr.eval, hbStEq])
        (by simpa [stOpksList, Expr.eval] using Nat.le_trans hBaseInv.opks_le hcOn) hLe fun p =>
        ite_eval_congr _ _ _ _ _ _ _ _
          (nat3Eq_eval_congr _ _ _ _ _ _ (by simp only [Expr.eval, v_zero_eval])
            (by simp only [_root_.SignalPqxdh.Security.ReductionDsl.KeyInd.qKJO,
              _root_.SignalPqxdh.Security.ReductionDsl.KeyInd.qK,
              _root_.SignalPqxdh.Security.ReductionDsl.KeyInd.qJ,
              _root_.SignalPqxdh.Security.ReductionDsl.KeyInd.qO, Expr.eval, v_eval_cons, hx]))
          (by simp only [Expr.eval, v_zero_eval])
          (by simp only [v_zero_eval]))
      (fun _ _ => by simp [_root_.SignalPqxdh.Security.ReductionDsl.KeyInd.qKJO,
        _root_.SignalPqxdh.Security.ReductionDsl.KeyInd.qK,
        _root_.SignalPqxdh.Security.ReductionDsl.KeyInd.qJ,
        _root_.SignalPqxdh.Security.ReductionDsl.KeyInd.qO, Expr.eval, hbStEq, hx])
      (fun _ _ => by simp [Expr.eval, hbStEq])
      (fun _ _ => rfl)
      (fun _ _ => Nat.le_succ_of_le (Nat.le_trans (eMap_length_le _ _ _)
        (by simpa [stOpksList, Expr.eval] using hBaseInv.opks_le)))
      (fun _ _ => by
        simp only [Expr.eval, v_eval_cons, List.length_cons]
        exact Nat.add_le_add_right hBaseInv.usedO_le 1)
      (fun _ _ => by simpa [stUsedNList, Expr.eval] using Nat.le_succ_of_le hBaseInv.usedN_le)
      (fun _ _ => by simpa [Expr.eval] using hKybLen)
      ht0 ht1 hB hRoom (by simpa using hInv)
  · refine simAndInv_bindV
      (liftBase_eval_congr _ _ _ _
        (qX25519_eval_congr _ _ _ _
          (by simp [_root_.SignalPqxdh.Security.ReductionDsl.KeyInd.qHdr, Expr.eval, hx]))) fun dh4 => ?_
    refine simAndInv_bindV
      (liftBase_eval_congr _ _ _ _
        (qKemDecaps_eval_congr _ _ _ _
          (by simp [_root_.SignalPqxdh.Security.ReductionDsl.KeyInd.qHdr, Expr.eval, hx]))) fun ssOpt => ?_
    refine simAndInv_iteC (by simp [nonZero32, eqB, litB, Expr.eval])
      (fun _ => simAndInv_ret_none sm₁ fgSh₁ sm₂ _ _ (by simp [hsm]) ht0 ht1 (by simpa using hInv)) fun _ => ?_
    refine simAndInv_caseOptV rfl
      (simAndInv_ret_none sm₁ fgSh₁ sm₂ _ _ (by simp [hsm]) ht0 ht1 (by simpa using hInv)) fun ss _ => ?_
    refine simAndInv_bindV
      (computePosC_congr _ _ _ _ _ _ _ _ _ _ rfl (by simp [Expr.eval])
        (by simp [_root_.SignalPqxdh.Security.ReductionDsl.KeyInd.qHdr, Expr.eval, hx])
        (by simp [Expr.eval])) fun p1 => ?_
    refine simAndInv_bindV
      (computePosC_congr _ _ _ _ _ _ _ _ _ _ rfl (by simp [Expr.eval])
        (by simp [_root_.SignalPqxdh.Security.ReductionDsl.KeyInd.qHdr, Expr.eval, hx])
        (by simp [Expr.eval])) fun p2 => ?_
    refine simAndInv_bindV
      (computePosC_congr _ _ _ _ _ _ _ _ _ _ rfl (by simp [Expr.eval])
        (by simp [_root_.SignalPqxdh.Security.ReductionDsl.KeyInd.qHdr, Expr.eval, hx])
        (by simp [Expr.eval])) fun p3 => ?_
    refine simAndInv_bindV (mkSecretPosC_congr _ _ _ _ rfl) fun p4Raw => ?_
    refine simAndInv_letV rfl ?_
    exact patchAndFinishAccept_sim S b true sm₁ bSt₁ fgSh₁ x₁ .zero .zero
      .zero .zero .zero .zero .zero _ _ _ _ _
      sm₂ bSt₂ x₂ .zero .zero .zero .zero .zero .zero .zero _ _ _ _ _
      _ _ c t fgShFull
      (by simp [hsm]) (by simp [hbSt]) (by simp [hbSt₂]) (by simp [hx]) (by simp) (by simp)
      (by simp) (by simp) (by simp) (by simp) (by simp)
      (fun _ _ => by simp [Expr.eval])
      (fun _ _ => eMap_congr_le _ _ _ _ _ _ (by simp [Expr.eval, hbStEq])
        (by simpa [stOpksList, Expr.eval] using Nat.le_trans hBaseInv.opks_le hcOn) hLe fun p =>
        ite_eval_congr _ _ _ _ _ _ _ _
          (nat3Eq_eval_congr _ _ _ _ _ _ (by simp only [Expr.eval, v_zero_eval])
            (by simp only [_root_.SignalPqxdh.Security.ReductionDsl.KeyInd.qKJO,
              _root_.SignalPqxdh.Security.ReductionDsl.KeyInd.qK,
              _root_.SignalPqxdh.Security.ReductionDsl.KeyInd.qJ,
              _root_.SignalPqxdh.Security.ReductionDsl.KeyInd.qO, Expr.eval, v_eval_cons, hx]))
          (by simp only [Expr.eval, v_zero_eval])
          (by simp only [v_zero_eval]))
      (fun _ _ => by simp [_root_.SignalPqxdh.Security.ReductionDsl.KeyInd.qKJO,
        _root_.SignalPqxdh.Security.ReductionDsl.KeyInd.qK,
        _root_.SignalPqxdh.Security.ReductionDsl.KeyInd.qJ,
        _root_.SignalPqxdh.Security.ReductionDsl.KeyInd.qO, Expr.eval, hbStEq, hx])
      (fun _ _ => by simp [Expr.eval, hbStEq])
      (fun _ _ => rfl)
      (fun _ _ => Nat.le_succ_of_le (Nat.le_trans (eMap_length_le _ _ _)
        (by simpa [stOpksList, Expr.eval] using hBaseInv.opks_le)))
      (fun _ _ => by
        simp only [Expr.eval, v_eval_cons, List.length_cons]
        exact Nat.add_le_add_right hBaseInv.usedO_le 1)
      (fun _ _ => by simpa [stUsedNList, Expr.eval] using Nat.le_succ_of_le hBaseInv.usedN_le)
      (fun _ _ => by simpa [Expr.eval] using hKybLen)
      ht0 ht1 hB hRoom (by simpa using hInv)

/-- Arm-level simulation and `GdhSimInv` preservation for `acceptOpkGdh2ShadowB` vs `acceptOpkGdh2B`. -/
theorem acceptOpkGdh2ShadowB_sim (S : Setup) (b : QueryBudget)
    {Γ₁a Γ₂a Γ₃a Γ₄a Γ₅a Δ₁ Γ₁b Γ₂b Γ₃b Γ₄b Δ₂ : List PT}
    [Ext Γ₁a Δ₁] [Ext Γ₂a Δ₁] [Ext Γ₃a Δ₁] [Ext Γ₄a Δ₁] [Ext Γ₅a Δ₁]
    [Ext Γ₁b Δ₂] [Ext Γ₂b Δ₂] [Ext Γ₃b Δ₂] [Ext Γ₄b Δ₂]
    (pa₁ : Var Γ₁a params2Ty) (sm₁ : Var Γ₂a simTy) (bSt₁ : Var Γ₃a keyIndStateTy)
    (fgSh₁ : Var Γ₅a fgSessCtrTy) (x₁ : Var Γ₄a accQTy)
    (pa₂ : Var Γ₁b params2Ty) (sm₂ : Var Γ₂b simTy) (bSt₂ : Var Γ₃b keyIndStateTy)
    (x₂ : Var Γ₄b accQTy)
    (env₁ : Env Δ₁) (env₂ : Env Δ₂)
    (c : Fin 3 → ℕ) (t : KeyIndQuery S)
    (fgShFull : fgShadowAtomicTy.denote)
    (hpa : (v pa₁).eval env₁ = (v pa₂).eval env₂)
    (hsm : (v sm₁).eval env₁ = (v sm₂).eval env₂)
    (hbSt : (v bSt₁).eval env₁ = ((v sm₁).eval env₁).1)
    (hbSt₂ : (v bSt₂).eval env₂ = ((v sm₂).eval env₂).1)
    (hx : (v x₁).eval env₁ = (v x₂).eval env₂)
    (ht0 : keyIndSimPred S 0 t = true)
    (ht1 : keyIndSimPred S 1 t = false)
    (hB : ∀ j, c j ≤ keyIndSimBounds b j)
    (hRoom : ∀ j, keyIndSimPred S j t → c j + 1 ≤ keyIndSimBounds b j)
    (hInv : GdhSimInv S b c
      (embedVal simTy ((v sm₁).eval env₁),
        ((embedVal fgSessCtrTy ((v fgSh₁).eval env₁)).1,
          ((embedVal fgSessCtrTy ((v fgSh₁).eval env₁)).2, fgShFull.2.2)))) :
    (fun r => (r.1, r.2.1)) <$>
      (acceptOpkGdh2ShadowB S (keyIndKFuelsOfBudget S b) pa₁ sm₁ bSt₁ fgSh₁ x₁).eval env₁ =
      (_root_.SignalPqxdh.Security.ReductionDsl.KeyInd.acceptOpkGdh2B
        S b.q_total pa₂ sm₂ bSt₂ x₂).eval env₂ ∧
    ∀ r ∈ support
      ((acceptOpkGdh2ShadowB S (keyIndKFuelsOfBudget S b) pa₁ sm₁ bSt₁ fgSh₁ x₁).eval env₁),
      GdhSimInv S b (bumpPred (keyIndSimPred S) c t)
        (embedVal simTy r.2.1,
          ((embedVal fgSessCtrTy r.2.2).1, ((embedVal fgSessCtrTy r.2.2).2, fgShFull.2.2))) := by
  simp only [acceptOpkGdh2ShadowB, letV_eval]
  exact acceptOpkGdhCoreShadowB_sim S b
    _root_.SignalPqxdh.Security.ReductionDsl.KeyInd.pa2OpkMode
    (fun p => p.2.2.2.2.2.2.2.1) (fun _ _ => rfl)
    .zero sm₁ bSt₁ fgSh₁ x₁ pa₂ sm₂ bSt₂ x₂ _ env₂ c t fgShFull
    (by simp [_root_.SignalPqxdh.Security.ReductionDsl.KeyInd.pa2OpkMode, Expr.eval, hpa])
    (by simp [hsm]) (by simp [hbSt]) hbSt₂ (by simp [hx])
    ht0 ht1 hB hRoom (by simpa using hInv)

/-- Arm-level simulation and `GdhSimInv` preservation for `acceptOpkGdhShadowB` vs `acceptOpkGdhB`. -/
theorem acceptOpkGdhShadowB_sim (S : Setup) (b : QueryBudget)
    {Γ₁a Γ₂a Γ₃a Γ₄a Γ₅a Δ₁ Γ₁b Γ₂b Γ₃b Γ₄b Δ₂ : List PT}
    [Ext Γ₁a Δ₁] [Ext Γ₂a Δ₁] [Ext Γ₃a Δ₁] [Ext Γ₄a Δ₁] [Ext Γ₅a Δ₁]
    [Ext Γ₁b Δ₂] [Ext Γ₂b Δ₂] [Ext Γ₃b Δ₂] [Ext Γ₄b Δ₂]
    (pa₁ : Var Γ₁a paramsTy) (sm₁ : Var Γ₂a simTy) (bSt₁ : Var Γ₃a keyIndStateTy)
    (fgSh₁ : Var Γ₅a fgSessCtrTy) (x₁ : Var Γ₄a accQTy)
    (pa₂ : Var Γ₁b paramsTy) (sm₂ : Var Γ₂b simTy) (bSt₂ : Var Γ₃b keyIndStateTy)
    (x₂ : Var Γ₄b accQTy)
    (env₁ : Env Δ₁) (env₂ : Env Δ₂)
    (c : Fin 3 → ℕ) (t : KeyIndQuery S)
    (fgShFull : fgShadowAtomicTy.denote)
    (hpa : (_root_.SignalPqxdh.Security.ReductionDsl.KeyInd.paOpkMode (v pa₁)).eval env₁ =
      (_root_.SignalPqxdh.Security.ReductionDsl.KeyInd.paOpkMode (v pa₂)).eval env₂)
    (hsm : (v sm₁).eval env₁ = (v sm₂).eval env₂)
    (hbSt : (v bSt₁).eval env₁ = ((v sm₁).eval env₁).1)
    (hbSt₂ : (v bSt₂).eval env₂ = ((v sm₂).eval env₂).1)
    (hx : (v x₁).eval env₁ = (v x₂).eval env₂)
    (ht0 : keyIndSimPred S 0 t = true)
    (ht1 : keyIndSimPred S 1 t = false)
    (hB : ∀ j, c j ≤ keyIndSimBounds b j)
    (hRoom : ∀ j, keyIndSimPred S j t → c j + 1 ≤ keyIndSimBounds b j)
    (hInv : GdhSimInv S b c
      (embedVal simTy ((v sm₁).eval env₁),
        ((embedVal fgSessCtrTy ((v fgSh₁).eval env₁)).1,
          ((embedVal fgSessCtrTy ((v fgSh₁).eval env₁)).2, fgShFull.2.2)))) :
    (fun r => (r.1, r.2.1)) <$>
      (acceptOpkGdhShadowB S (keyIndKFuelsOfBudget S b) pa₁ sm₁ bSt₁ fgSh₁ x₁).eval env₁ =
      (_root_.SignalPqxdh.Security.ReductionDsl.KeyInd.acceptOpkGdhB
        S b.q_total pa₂ sm₂ bSt₂ x₂).eval env₂ ∧
    ∀ r ∈ support
      ((acceptOpkGdhShadowB S (keyIndKFuelsOfBudget S b) pa₁ sm₁ bSt₁ fgSh₁ x₁).eval env₁),
      GdhSimInv S b (bumpPred (keyIndSimPred S) c t)
        (embedVal simTy r.2.1,
          ((embedVal fgSessCtrTy r.2.2).1, ((embedVal fgSessCtrTy r.2.2).2, fgShFull.2.2))) := by
  simp only [acceptOpkGdhShadowB, letV_eval]
  exact acceptOpkGdhCoreShadowB_sim S b
    _root_.SignalPqxdh.Security.ReductionDsl.KeyInd.paOpkMode
    (fun p => p.2.2.2.2.2.2.2.2.1) (fun _ _ => rfl)
    .zero sm₁ bSt₁ fgSh₁ x₁ pa₂ sm₂ bSt₂ x₂ _ env₂ c t fgShFull
    (by simpa [v_zero_eval, _root_.SignalPqxdh.Security.ReductionDsl.KeyInd.paOpkMode, Expr.eval] using hpa)
    (by simp [hsm]) (by simp [hbSt]) hbSt₂ (by simp [hx])
    ht0 ht1 hB hRoom (by simpa using hInv)

/-- Arm-level simulation and `GdhSimInv` preservation for `acceptNoOpkGdhShadowB` vs `acceptNoOpkGdhB`. -/
theorem acceptNoOpkGdhShadowB_sim (S : Setup) (b : QueryBudget)
    {Γ₂a Γ₃a Γ₄a Γ₅a Δ₁ Γ₂b Γ₃b Γ₄b Δ₂ : List PT}
    [Ext Γ₂a Δ₁] [Ext Γ₃a Δ₁] [Ext Γ₄a Δ₁] [Ext Γ₅a Δ₁]
    [Ext Γ₂b Δ₂] [Ext Γ₃b Δ₂] [Ext Γ₄b Δ₂]
    (sm₁ : Var Γ₂a simTy) (bSt₁ : Var Γ₃a keyIndStateTy)
    (fgSh₁ : Var Γ₅a fgSessCtrTy) (x₁ : Var Γ₄a accQTy)
    (sm₂ : Var Γ₂b simTy) (bSt₂ : Var Γ₃b keyIndStateTy) (x₂ : Var Γ₄b accQTy)
    (env₁ : Env Δ₁) (env₂ : Env Δ₂)
    (c : Fin 3 → ℕ) (t : KeyIndQuery S)
    (fgShFull : fgShadowAtomicTy.denote)
    (hsm : (v sm₁).eval env₁ = (v sm₂).eval env₂)
    (hbSt : (v bSt₁).eval env₁ = ((v sm₁).eval env₁).1)
    (hbSt₂ : (v bSt₂).eval env₂ = ((v sm₂).eval env₂).1)
    (hx : (v x₁).eval env₁ = (v x₂).eval env₂)
    (ht0 : keyIndSimPred S 0 t = true)
    (ht1 : keyIndSimPred S 1 t = false)
    (hB : ∀ j, c j ≤ keyIndSimBounds b j)
    (hRoom : ∀ j, keyIndSimPred S j t → c j + 1 ≤ keyIndSimBounds b j)
    (hInv : GdhSimInv S b c
      (embedVal simTy ((v sm₁).eval env₁),
        ((embedVal fgSessCtrTy ((v fgSh₁).eval env₁)).1,
          ((embedVal fgSessCtrTy ((v fgSh₁).eval env₁)).2, fgShFull.2.2)))) :
    (fun r => (r.1, r.2.1)) <$>
      (acceptNoOpkGdhShadowB S (keyIndKFuelsOfBudget S b) sm₁ bSt₁ fgSh₁ x₁).eval env₁ =
      (_root_.SignalPqxdh.Security.ReductionDsl.KeyInd.acceptNoOpkGdhB
        S b.q_total sm₂ bSt₂ x₂).eval env₂ ∧
    ∀ r ∈ support
      ((acceptNoOpkGdhShadowB S (keyIndKFuelsOfBudget S b) sm₁ bSt₁ fgSh₁ x₁).eval env₁),
      GdhSimInv S b (bumpPred (keyIndSimPred S) c t)
        (embedVal simTy r.2.1,
          ((embedVal fgSessCtrTy r.2.2).1, ((embedVal fgSessCtrTy r.2.2).2, fgShFull.2.2))) := by
  let f := keyIndKFuelsOfBudget S b
  have hcOn : c 0 ≤ f.kOn := by
    have h0 := hB 0; dsimp only [keyIndSimBounds, f, keyIndKFuelsOfBudget] at h0 ⊢; exact h0
  have hLe : f.kOn ≤ b.q_total := Nat.min_le_right _ _
  have hProjBase : projVal keyIndStateTy (embedVal simTy ((v sm₁).eval env₁)).1 = (v bSt₁).eval env₁ := by
    rw [hbSt]; exact congrArg Prod.fst (projVal_embedVal simTy ((v sm₁).eval env₁))
  have hBaseInv : BaseOnlineLenInv c ((v bSt₁).eval env₁) := hProjBase ▸ hInv.online_len
  have hbStEq : (v bSt₁).eval env₁ = (v bSt₂).eval env₂ := by rw [hbSt, hbSt₂, hsm]
  have hPowsLen : ((smPows (v sm₁)).eval env₁).length ≤ f.kOn := by
    have h := hInv.pows_len; dsimp only at h
    rw [embedVal_prod_snd, embedVal_prod_snd, embedVal_prod_snd, embedVal_prod_snd, embedVal_list_length] at h
    exact Nat.le_trans h hcOn
  change SimAndInv S b c t fgShFull _ _
  unfold acceptNoOpkGdhShadowB _root_.SignalPqxdh.Security.ReductionDsl.KeyInd.acceptNoOpkGdhB
  refine simAndInv_iteC
    (by
      have hOpt := optU32Eq_eval_congr
        (hdOpkId (_root_.SignalPqxdh.Security.ReductionDsl.KeyInd.qHdr (v x₁))) .none
        (hdOpkId (_root_.SignalPqxdh.Security.ReductionDsl.KeyInd.qHdr (v x₂))) .none env₁ env₂
        (by simp [_root_.SignalPqxdh.Security.ReductionDsl.KeyInd.qHdr, Expr.eval, hx]) rfl
      have hJ := u32OfNat_eval_congr
        (_root_.SignalPqxdh.Security.ReductionDsl.KeyInd.qJ (v x₁))
        (_root_.SignalPqxdh.Security.ReductionDsl.KeyInd.qJ (v x₂)) env₁ env₂
        (by simp [_root_.SignalPqxdh.Security.ReductionDsl.KeyInd.qJ, Expr.eval, hx])
      have hL1 := lenB_eval_congr
        (hdIkAPk (_root_.SignalPqxdh.Security.ReductionDsl.KeyInd.qHdr (v x₁)))
        (hdIkAPk (_root_.SignalPqxdh.Security.ReductionDsl.KeyInd.qHdr (v x₂))) env₁ env₂
        (by simp [_root_.SignalPqxdh.Security.ReductionDsl.KeyInd.qHdr, Expr.eval, hx])
      have hL2 := lenB_eval_congr
        (hdEkAPk (_root_.SignalPqxdh.Security.ReductionDsl.KeyInd.qHdr (v x₁)))
        (hdEkAPk (_root_.SignalPqxdh.Security.ReductionDsl.KeyInd.qHdr (v x₂))) env₁ env₂
        (by simp [_root_.SignalPqxdh.Security.ReductionDsl.KeyInd.qHdr, Expr.eval, hx])
      have hEq1 := eqU32_eval_congr
        (hdSpkId (_root_.SignalPqxdh.Security.ReductionDsl.KeyInd.qHdr (v x₁)))
        (u32OfNat (_root_.SignalPqxdh.Security.ReductionDsl.KeyInd.qJ (v x₁)))
        (hdSpkId (_root_.SignalPqxdh.Security.ReductionDsl.KeyInd.qHdr (v x₂)))
        (u32OfNat (_root_.SignalPqxdh.Security.ReductionDsl.KeyInd.qJ (v x₂))) env₁ env₂
        (by simp [_root_.SignalPqxdh.Security.ReductionDsl.KeyInd.qHdr, Expr.eval, hx]) hJ
      have hEq2 := eqU32_eval_congr
        (hdPqspkId (_root_.SignalPqxdh.Security.ReductionDsl.KeyInd.qHdr (v x₁)))
        (u32OfNat (_root_.SignalPqxdh.Security.ReductionDsl.KeyInd.qJ (v x₁)))
        (hdPqspkId (_root_.SignalPqxdh.Security.ReductionDsl.KeyInd.qHdr (v x₂)))
        (u32OfNat (_root_.SignalPqxdh.Security.ReductionDsl.KeyInd.qJ (v x₂))) env₁ env₂
        (by simp [_root_.SignalPqxdh.Security.ReductionDsl.KeyInd.qHdr, Expr.eval, hx]) hJ
      simp only [natEq, Expr.eval]
      rw [hEq1, hEq2, hOpt, hL1, hL2]; rfl)
    (fun _ => simAndInv_ret_none sm₁ fgSh₁ sm₂ _ _ hsm ht0 ht1 hInv) fun _ => ?_
  refine simAndInv_iteC
    (eAny_congr_le _ _ _ _ _ _ (by simp [Expr.eval, hbStEq])
      (by simpa [stUsedNList, Expr.eval] using Nat.le_trans hBaseInv.usedN_le hcOn) hLe fun u =>
      nat3Eq_eval_congr _ _ _ _ _ _ (by simp only [v_zero_eval])
        (by simp only [_root_.SignalPqxdh.Security.ReductionDsl.KeyInd.qKJO,
          _root_.SignalPqxdh.Security.ReductionDsl.KeyInd.qK,
          _root_.SignalPqxdh.Security.ReductionDsl.KeyInd.qJ,
          _root_.SignalPqxdh.Security.ReductionDsl.KeyInd.qO, Expr.eval, v_eval_cons, hx]))
    (fun _ => simAndInv_ret_none sm₁ fgSh₁ sm₂ _ _ hsm ht0 ht1 hInv) fun _ => ?_
  refine simAndInv_bindV
    (liftBase_eval_congr _ _ _ _
      (koskSenderOkPowsC_sim S bSt₁ _ _ bSt₂ _ _ _ _ hbStEq
        (by simp [smPows, Expr.eval, hsm])
        (by simp [_root_.SignalPqxdh.Security.ReductionDsl.KeyInd.qHdr, Expr.eval, hx])
        (Nat.le_trans hBaseInv.prin_le hcOn) hPowsLen hLe)) fun sOk => ?_
  refine simAndInv_iteC rfl
    (fun _ => simAndInv_ret_none sm₁ fgSh₁ sm₂ _ _ (by simp [hsm]) ht0 ht1 (by simpa using hInv)) fun _ => ?_
  refine simAndInv_caseOptV
    (eFind_congr_le _ _ _ _ _ _ (by simp [Expr.eval, hbStEq])
      (by simpa [stPrinList, Expr.eval] using Nat.le_trans hBaseInv.prin_le hcOn) hLe fun p =>
      natEq_eval_congr _ _ _ _ _ _ (by simp only [Expr.eval, v_zero_eval])
        (by simp only [_root_.SignalPqxdh.Security.ReductionDsl.KeyInd.qK,
          Expr.eval, v_eval_cons, hx]))
    (simAndInv_ret_none sm₁ fgSh₁ sm₂ _ _ (by simp [hsm]) ht0 ht1 (by simpa using hInv)) fun ke _ => ?_
  refine simAndInv_caseOptV
    (eFind_congr_le _ _ _ _ _ _ (by simp [Expr.eval, hbStEq])
      (by simpa [stSpksList, Expr.eval] using Nat.le_trans hBaseInv.spks_le hcOn) hLe fun p =>
      nat2Eq_eval_congr _ _ _ _ _ _ (by simp only [Expr.eval, v_zero_eval])
        (by simp only [_root_.SignalPqxdh.Security.ReductionDsl.KeyInd.qK,
          _root_.SignalPqxdh.Security.ReductionDsl.KeyInd.qJ, Expr.eval, v_eval_cons, hx]))
    (simAndInv_ret_none sm₁ fgSh₁ sm₂ _ _ (by simp [hsm]) ht0 ht1 (by simpa using hInv)) fun be _ => ?_
  have hKybLen := Nat.le_trans
    (kyberCheckE_snd_length_le (K := f.kOn) (stKyb (v bSt₁))
      (.pair (_root_.SignalPqxdh.Security.ReductionDsl.KeyInd.qK (v x₁))
        (.pair (hdPqspkId (_root_.SignalPqxdh.Security.ReductionDsl.KeyInd.qHdr (v x₁)))
          (.pair (hdSpkId (_root_.SignalPqxdh.Security.ReductionDsl.KeyInd.qHdr (v x₁)))
            (hdEkAPk (_root_.SignalPqxdh.Security.ReductionDsl.KeyInd.qHdr (v x₁))))))
      (.cons be (.cons ke (.cons sOk env₁))))
    (Nat.add_le_add_right (by simpa [stKybList, Expr.eval] using hBaseInv.kyb_le) 1)
  refine simAndInv_letV
    (kyberCheckE_sim _ _ _ _ _ _ (by simp [Expr.eval, hbStEq])
      (by simp [_root_.SignalPqxdh.Security.ReductionDsl.KeyInd.qK,
        _root_.SignalPqxdh.Security.ReductionDsl.KeyInd.qHdr, Expr.eval, hx])
      (by simpa [stKybList, Expr.eval] using Nat.le_trans hBaseInv.kyb_le hcOn) hLe) ?_
  refine simAndInv_bindV
    (liftBase_eval_congr _ _ _ _
      (qIsCanonical_eval_congr _ _ _ _
        (by simp [_root_.SignalPqxdh.Security.ReductionDsl.KeyInd.qHdr, Expr.eval, hx]))) fun canon => ?_
  refine simAndInv_bindV
    (liftBase_eval_congr _ _ _ _
      (qX25519_eval_congr _ _ _ _
        (by simp [_root_.SignalPqxdh.Security.ReductionDsl.KeyInd.qHdr, Expr.eval, hx]))) fun dh1Z => ?_
  refine simAndInv_bindV
    (liftBase_eval_congr _ _ _ _
      (qX25519_eval_congr _ _ _ _
        (by simp [_root_.SignalPqxdh.Security.ReductionDsl.KeyInd.qHdr, Expr.eval, hx]))) fun dh2Z => ?_
  refine simAndInv_bindV
    (liftBase_eval_congr _ _ _ _
      (qKemDecaps_eval_congr _ _ _ _
        (by simp [_root_.SignalPqxdh.Security.ReductionDsl.KeyInd.qHdr, Expr.eval, hx]))) fun ssOpt => ?_
  refine simAndInv_iteC (by simp [nonZero32, eqB, litB, Expr.eval])
    (fun _ => simAndInv_ret_none sm₁ fgSh₁ sm₂ _ _ (by simp [hsm]) ht0 ht1 (by simpa using hInv)) fun _ => ?_
  refine simAndInv_caseOptV rfl
    (simAndInv_ret_none sm₁ fgSh₁ sm₂ _ _ (by simp [hsm]) ht0 ht1 (by simpa using hInv)) fun ss _ => ?_
  refine simAndInv_bindV
    (computePosC_congr _ _ _ _ _ _ _ _ _ _ rfl (by simp [Expr.eval])
      (by simp [_root_.SignalPqxdh.Security.ReductionDsl.KeyInd.qHdr, Expr.eval, hx])
      (by simp [Expr.eval])) fun p1 => ?_
  refine simAndInv_bindV
    (computePosC_congr _ _ _ _ _ _ _ _ _ _ rfl (by simp [Expr.eval])
      (by simp [_root_.SignalPqxdh.Security.ReductionDsl.KeyInd.qHdr, Expr.eval, hx])
      (by simp [Expr.eval])) fun p2 => ?_
  refine simAndInv_bindV
    (computePosC_congr _ _ _ _ _ _ _ _ _ _ rfl (by simp [Expr.eval])
      (by simp [_root_.SignalPqxdh.Security.ReductionDsl.KeyInd.qHdr, Expr.eval, hx])
      (by simp [Expr.eval])) fun p3 => ?_
  refine simAndInv_letV rfl ?_
  exact patchAndFinishAccept_sim S b false sm₁ bSt₁ fgSh₁ x₁ .zero .zero
    .zero .zero .zero .zero .zero _ _ _ _ _
    sm₂ bSt₂ x₂ .zero .zero .zero .zero .zero .zero .zero _ _ _ _ _
    _ _ c t fgShFull
    (by simp [hsm]) (by simp [hbSt]) (by simp [hbSt₂]) (by simp [hx]) (by simp) (by simp)
    (by simp) (by simp) (by simp) (by simp) (by simp)
    (fun _ _ => rfl)
    (fun _ _ => by simp [Expr.eval, hbStEq])
    (fun _ _ => by simp [Expr.eval, hbStEq])
    (fun _ _ => by simp [_root_.SignalPqxdh.Security.ReductionDsl.KeyInd.qKJO,
      _root_.SignalPqxdh.Security.ReductionDsl.KeyInd.qK,
      _root_.SignalPqxdh.Security.ReductionDsl.KeyInd.qJ,
      _root_.SignalPqxdh.Security.ReductionDsl.KeyInd.qO, Expr.eval, hbStEq, hx])
    (fun _ _ => rfl)
    (fun _ _ => by simpa [stOpksList, Expr.eval] using Nat.le_succ_of_le hBaseInv.opks_le)
    (fun _ _ => by simpa [stUsedOList, Expr.eval] using Nat.le_succ_of_le hBaseInv.usedO_le)
    (fun _ _ => by
      simp only [Expr.eval, v_eval_cons, List.length_cons]
      exact Nat.add_le_add_right hBaseInv.usedN_le 1)
    (fun _ _ => by simpa [Expr.eval] using hKybLen)
    ht0 ht1 hB hRoom (by simpa using hInv)

private theorem liftBase_queries_h2
    {C : _root_.SignalPqxdh.LegacyCosted.ChallengerOracle}
    (w : (_root_.SignalPqxdh.LegacyCosted.pqChalIface C).Tag → ℕ)
    (ws : (_root_.SignalPqxdh.LegacyCosted.pqChalIface C).smp.Samp → ℕ)
    {Γ : List PT} {τ : PT} (c : Comp pqxdhOps pqPrimIface Γ τ) :
    (_root_.SignalPqxdh.Security.ReductionDsl.KeyInd.liftBase (C := C) c).queries w ws =
      Comp.queries (I := pqPrimIface) (fun g => w (.inl g)) (fun s => ws s) c := by
  induction c <;> simp_all [_root_.SignalPqxdh.Security.ReductionDsl.KeyInd.liftBase, Comp.queries]

private theorem wrapBase2_unsup_h2 {Γ₁ Γ₂ Δ : List PT} [Ext Γ₁ Δ] [Ext Γ₂ Δ]
    (pa : Var Γ₁ params2Ty) (sm : Var Γ₂ simTy)
    (c : Comp pqxdhOps pqPrimIface Δ (.prod keyIndRespTy keyIndStateTy)) :
    (_root_.SignalPqxdh.Security.ReductionDsl.KeyInd.wrapBase2 pa sm c).queries
        tlGapDhKeyInd.unsupportedW (fun _ => 0) =
      c.queries Computational.Proofs.SignalPqxdh.AtomicLift.keyIndUnsupportedPrimW (fun _ => 0) := by
  dsimp only [_root_.SignalPqxdh.Security.ReductionDsl.KeyInd.wrapBase2,
    _root_.SignalPqxdh.Security.ReductionDsl.KeyInd.gPrim, pqGapDhIface, bindV, tlGapDhKeyInd]
  simp only [Comp.queries, liftBase_queries_h2, Nat.add_zero]

private theorem wrapSim2_unsup_h2 {Γ₁ Δ : List PT} [Ext Γ₁ Δ]
    (pa : Var Γ₁ params2Ty)
    (c : Comp pqxdhOps pqGapDhIface Δ (.prod keyIndRespTy simTy)) :
    (_root_.SignalPqxdh.Security.ReductionDsl.KeyInd.wrapSim2 pa c).queries
        tlGapDhKeyInd.unsupportedW (fun _ => 0) =
      c.queries tlGapDhKeyInd.unsupportedW (fun _ => 0) := by
  dsimp only [_root_.SignalPqxdh.Security.ReductionDsl.KeyInd.wrapSim2, bindV]
  simp only [Comp.queries, Nat.add_zero]

private theorem wrapSimSessArm_unsup_h2 {qPayTy : PT}
    (body :
      Var [params2Ty, .prod params2Ty simTy, .prod (.prod params2Ty simTy) fgSessCtrTy, qPayTy] params2Ty →
      Var [simTy, params2Ty, .prod params2Ty simTy, .prod (.prod params2Ty simTy) fgSessCtrTy, qPayTy] simTy →
      Var [keyIndStateTy, simTy, params2Ty, .prod params2Ty simTy,
        .prod (.prod params2Ty simTy) fgSessCtrTy, qPayTy] keyIndStateTy →
      Var [fgSessCtrTy, keyIndStateTy, simTy, params2Ty, .prod params2Ty simTy,
        .prod (.prod params2Ty simTy) fgSessCtrTy, qPayTy] fgSessCtrTy →
      Var [.prod (.prod params2Ty simTy) fgSessCtrTy, qPayTy] qPayTy →
      Comp pqxdhOps pqGapDhIface
        [fgSessCtrTy, keyIndStateTy, simTy, params2Ty, .prod params2Ty simTy,
          .prod (.prod params2Ty simTy) fgSessCtrTy, qPayTy]
        (.prod keyIndRespTy (.prod simTy fgSessCtrTy))) :
    (wrapSimSessArm body).queries tlGapDhKeyInd.unsupportedW (fun _ => 0) =
      (body .zero .zero .zero .zero (.succ .zero)).queries
        tlGapDhKeyInd.unsupportedW (fun _ => 0) := by
  dsimp only [wrapSimSessArm, letV, bindV]
  simp only [Comp.queries, Nat.zero_add, Nat.add_zero]

private theorem gdhHandle2_unsup_h2 (S : Setup) (K : Nat) :
    (_root_.SignalPqxdh.Security.ReductionDsl.KeyInd.gdhHandle2 S K).queries
        tlGapDhKeyInd.unsupportedW (fun _ => 0) = 0 := by
  dsimp only [_root_.SignalPqxdh.Security.ReductionDsl.KeyInd.gdhHandle2,
    _root_.SignalPqxdh.Security.ReductionDsl.KeyInd.initPrinGdh2B,
    _root_.SignalPqxdh.Security.ReductionDsl.KeyInd.genSpkGdh2B,
    _root_.SignalPqxdh.Security.ReductionDsl.KeyInd.genOpkGdh2B,
    _root_.SignalPqxdh.Security.ReductionDsl.KeyInd.initiateGdh2B,
    _root_.SignalPqxdh.Security.ReductionDsl.KeyInd.acceptOpkGdh2B,
    _root_.SignalPqxdh.Security.ReductionDsl.KeyInd.acceptNoOpkGdhB,
    finishAcceptGdhC,
    _root_.SignalPqxdh.Security.ReductionDsl.KeyInd.corruptB,
    _root_.SignalPqxdh.Security.ReductionDsl.KeyInd.testB,
    _root_.SignalPqxdh.Security.ReductionDsl.KeyInd.roParsedC,
    _root_.SignalPqxdh.Security.ReductionDsl.KeyInd.roRawFallbackC,
    _root_.SignalPqxdh.Security.ReductionDsl.KeyInd.revealB,
    _root_.SignalPqxdh.Security.ReductionDsl.KeyInd.registerGdhB,
    _root_.SignalPqxdh.Security.ReductionDsl.KeyInd.revealSpkB,
    gPrim, chooseInitRandC, chooseRespRandC, lookupSpkSkC, computePosC,
    _root_.SignalPqxdh.Security.ReductionDsl.KeyInd.mkPairPosC, fgPatchC,
    findHonestC, honestPeerC, checkProvC, koskBundleOkPowsC, koskSenderOkPowsC,
    computeOptPosInitC, mkSecretPosC, isGameSpkC, isGameOpkC, resolveSigPkC, partnerC,
    findMV, anyMV, letV, bindV, caseOptV, caseSumV, pqGapDhIface]
  simp only [wrapBase2_unsup_h2, wrapSim2_unsup_h2,
    Computational.Proofs.SignalPqxdh.Security.ReductionDsl.KindSplit.KeyIndGapDhKSimBase.entryMatchesC_unsupported_zero,
    liftBase_queries_h2, Comp.queries]
  dsimp [sBytes32, _root_.SignalPqxdh.Security.ReductionDsl.KeyInd.sRandom64, sDrKey96,
    qX25519, qX25519Base, qPow8, qIsCanonical,
    _root_.SignalPqxdh.Security.ReductionDsl.KeyInd.qSigPkGen,
    _root_.SignalPqxdh.Security.ReductionDsl.KeyInd.qSigSign, qSigVerify,
    _root_.SignalPqxdh.Security.ReductionDsl.KeyInd.qKemKeyGen, qKemEncaps, qKemDecaps,
    _root_.SignalPqxdh.Security.ReductionDsl.KeyInd.ddhQ,
    Comp.queries, tlGapDhKeyInd,
    Computational.Proofs.SignalPqxdh.AtomicLift.keyIndUnsupportedPrimW]
  omega

private theorem wrapSimSessArm_initiate2_unsup_h2 (S : Setup) (f : KeyIndKFuels) (hasOpk : Bool) :
    (wrapSimSessArm (paTy := params2Ty) (qPayTy := initQTy)
      fun pa sm bSt fgSh x => initiateGdh2ShadowB S f pa sm bSt fgSh hasOpk x).queries
        tlGapDhKeyInd.unsupportedW (fun _ => 0) = 0 := by
  rw [wrapSimSessArm_unsup_h2]
  dsimp only [initiateGdh2ShadowB, fgPatchShadowC,
    gPrim, chooseInitRandC, lookupSpkSkC, computePosC,
    _root_.SignalPqxdh.Security.ReductionDsl.KeyInd.mkPairPosC,
    findHonestC, honestPeerC, checkProvC, koskBundleOkPowsC, computeOptPosInitC,
    mkSecretPosC, isGameSpkC, isGameOpkC, resolveSigPkC, partnerC,
    findMV, anyMV, letV, bindV, caseOptV, caseSumV, pqGapDhIface]
  simp only [
    Computational.Proofs.SignalPqxdh.Security.ReductionDsl.KindSplit.KeyIndGapDhKSimBase.entryMatchesC_unsupported_zero,
    liftBase_queries_h2, Comp.queries]
  dsimp [sBytes32, _root_.SignalPqxdh.Security.ReductionDsl.KeyInd.sRandom64, sDrKey96,
    qX25519, qX25519Base, qPow8, qIsCanonical, qSigVerify, qKemEncaps,
    _root_.SignalPqxdh.Security.ReductionDsl.KeyInd.ddhQ,
    Comp.queries, tlGapDhKeyInd,
    Computational.Proofs.SignalPqxdh.AtomicLift.keyIndUnsupportedPrimW]
  omega

private theorem wrapSimSessArm_acceptOpk2_unsup_h2 (S : Setup) (f : KeyIndKFuels) :
    (wrapSimSessArm (paTy := params2Ty) (qPayTy := accQTy)
      fun pa sm bSt fgSh x => acceptOpkGdh2ShadowB S f pa sm bSt fgSh x).queries
        tlGapDhKeyInd.unsupportedW (fun _ => 0) = 0 := by
  rw [wrapSimSessArm_unsup_h2]
  dsimp only [acceptOpkGdh2ShadowB, acceptOpkGdhCoreShadowB, fgPatchShadowC, finishAcceptGdhC,
    gPrim, chooseRespRandC, computePosC,
    _root_.SignalPqxdh.Security.ReductionDsl.KeyInd.mkPairPosC,
    findHonestC, honestPeerC, koskSenderOkPowsC, mkSecretPosC, partnerC,
    findMV, anyMV, letV, bindV, caseOptV, caseSumV, pqGapDhIface]
  simp only [
    Computational.Proofs.SignalPqxdh.Security.ReductionDsl.KindSplit.KeyIndGapDhKSimBase.entryMatchesC_unsupported_zero,
    liftBase_queries_h2, Comp.queries]
  dsimp [_root_.SignalPqxdh.Security.ReductionDsl.KeyInd.sRandom64, sDrKey96,
    qX25519, qPow8, qIsCanonical, qKemDecaps,
    _root_.SignalPqxdh.Security.ReductionDsl.KeyInd.ddhQ,
    Comp.queries, tlGapDhKeyInd,
    Computational.Proofs.SignalPqxdh.AtomicLift.keyIndUnsupportedPrimW]
  omega

private theorem wrapSimSessArm_acceptNoOpk2_unsup_h2 (S : Setup) (f : KeyIndKFuels) :
    (wrapSimSessArm (paTy := params2Ty) (qPayTy := accQTy)
      fun _ sm bSt fgSh x => acceptNoOpkGdhShadowB S f sm bSt fgSh x).queries
        tlGapDhKeyInd.unsupportedW (fun _ => 0) = 0 := by
  rw [wrapSimSessArm_unsup_h2]
  dsimp only [acceptNoOpkGdhShadowB, fgPatchShadowC, finishAcceptGdhC,
    gPrim, chooseRespRandC, computePosC,
    _root_.SignalPqxdh.Security.ReductionDsl.KeyInd.mkPairPosC,
    findHonestC, honestPeerC, koskSenderOkPowsC, mkSecretPosC, partnerC,
    findMV, anyMV, letV, bindV, caseOptV, caseSumV, pqGapDhIface]
  simp only [
    Computational.Proofs.SignalPqxdh.Security.ReductionDsl.KindSplit.KeyIndGapDhKSimBase.entryMatchesC_unsupported_zero,
    liftBase_queries_h2, Comp.queries]
  dsimp [_root_.SignalPqxdh.Security.ReductionDsl.KeyInd.sRandom64, sDrKey96,
    qX25519, qPow8, qIsCanonical, qKemDecaps,
    _root_.SignalPqxdh.Security.ReductionDsl.KeyInd.ddhQ,
    Comp.queries, tlGapDhKeyInd,
    Computational.Proofs.SignalPqxdh.AtomicLift.keyIndUnsupportedPrimW]
  omega

private theorem gdhShadowHandle2_sess_step
    (S : Setup) (b : QueryBudget) (t : KeyIndQuery S)
    {qPayTy : PT} {PayAtomic : Ty pqAtomicSig}
    (pay : PayAtomic.denote) (payLeg : qPayTy.denote)
    (payE : Expr pqAtomicOps
      (PayAtomic :: [.prod (embedTy _root_.SignalPqxdh.Security.ReductionDsl.KeyInd.gdhState2Ty)
        fgShadowAtomicTy, (pqKeyIndCodec S).Q])
      (embedTy qPayTy))
    (bodyK :
      Var [params2Ty, _root_.SignalPqxdh.Security.ReductionDsl.KeyInd.gdhState2Ty,
        .prod _root_.SignalPqxdh.Security.ReductionDsl.KeyInd.gdhState2Ty fgSessCtrTy, qPayTy] params2Ty →
      Var [simTy, params2Ty, _root_.SignalPqxdh.Security.ReductionDsl.KeyInd.gdhState2Ty,
        .prod _root_.SignalPqxdh.Security.ReductionDsl.KeyInd.gdhState2Ty fgSessCtrTy, qPayTy] simTy →
      Var [keyIndStateTy, simTy, params2Ty, _root_.SignalPqxdh.Security.ReductionDsl.KeyInd.gdhState2Ty,
        .prod _root_.SignalPqxdh.Security.ReductionDsl.KeyInd.gdhState2Ty fgSessCtrTy, qPayTy] keyIndStateTy →
      Var [fgSessCtrTy, keyIndStateTy, simTy, params2Ty,
        _root_.SignalPqxdh.Security.ReductionDsl.KeyInd.gdhState2Ty,
        .prod _root_.SignalPqxdh.Security.ReductionDsl.KeyInd.gdhState2Ty fgSessCtrTy, qPayTy] fgSessCtrTy →
      Var [.prod _root_.SignalPqxdh.Security.ReductionDsl.KeyInd.gdhState2Ty fgSessCtrTy, qPayTy] qPayTy →
      Comp pqxdhOps pqGapDhIface
        [fgSessCtrTy, keyIndStateTy, simTy, params2Ty,
          _root_.SignalPqxdh.Security.ReductionDsl.KeyInd.gdhState2Ty,
          .prod _root_.SignalPqxdh.Security.ReductionDsl.KeyInd.gdhState2Ty fgSessCtrTy, qPayTy]
        (.prod keyIndRespTy (.prod simTy fgSessCtrTy)))
    (rhsComp : params2Ty.denote → simTy.denote →
      OracleComp GdhSimSpec (keyIndRespTy.denote × simTy.denote))
    (hUnsupK :
      (wrapSimSessArm bodyK).queries tlGapDhKeyInd.unsupportedW (fun _ => 0) = 0)
    (hDispK : ∀ s' : Computational.Proofs.SignalPqxdh.Security.ReductionDsl.KindSplit.KeyIndGapDhK.gdhShadowState2AtomicTy.denote,
      (gdhShadowHandle2Atomic gdhLift2Key S (keyIndKFuelsOfBudget S b)).eval
        (.cons s' (.cons ((pqKeyIndCodec S).qenc t) .nil)) =
      (liftKind0SessArm gdhLift2Key S payE (wrapSimSessArm bodyK)).eval
        (.cons pay (.cons s' (.cons ((pqKeyIndCodec S).qenc t) .nil))))
    (hPayE : ∀ s' : Computational.Proofs.SignalPqxdh.Security.ReductionDsl.KindSplit.KeyIndGapDhK.gdhShadowState2AtomicTy.denote,
      payE.eval (.cons pay (.cons s' (.cons ((pqKeyIndCodec S).qenc t) .nil))) =
        embedVal qPayTy payLeg)
    (hDispQ : ∀ (pa : params2Ty.denote) (sm : simTy.denote),
      (_root_.SignalPqxdh.Security.ReductionDsl.KeyInd.gdhHandle2 S b.q_total).eval
        (.cons (pa, sm) (.cons ((_root_.SignalPqxdh.LegacyCosted.keyIndCodec S).qenc t) .nil)) =
      (fun rq => (rq.1, (pa, rq.2))) <$> rhsComp pa sm)
    (hSim : ∀ (c : Fin 3 → ℕ) (pa : params2Ty.denote) (sm : simTy.denote)
        (fgSc : fgSessCtrTy.denote) (fgFull : fgShadowAtomicTy.denote),
      (∀ j, c j ≤ keyIndSimBounds b j) →
      (∀ j, keyIndSimPred S j t → c j + 1 ≤ keyIndSimBounds b j) →
      GdhSimInv S b c
        (embedVal simTy sm,
          ((embedVal fgSessCtrTy fgSc).1, ((embedVal fgSessCtrTy fgSc).2, fgFull.2.2))) →
      (fun r => (r.1, r.2.1)) <$>
        (bodyK .zero .zero .zero .zero (.succ .zero)).eval
          (.cons fgSc (.cons sm.1 (.cons sm (.cons pa (.cons (pa, sm)
            (.cons ((pa, sm), fgSc) (.cons payLeg .nil))))))) =
        rhsComp pa sm ∧
      ∀ r ∈ support
        ((bodyK .zero .zero .zero .zero (.succ .zero)).eval
          (.cons fgSc (.cons sm.1 (.cons sm (.cons pa (.cons (pa, sm)
            (.cons ((pa, sm), fgSc) (.cons payLeg .nil)))))))),
        GdhSimInv S b (bumpPred (keyIndSimPred S) c t)
          (embedVal simTy r.2.1,
            ((embedVal fgSessCtrTy r.2.2).1, ((embedVal fgSessCtrTy r.2.2).2, fgFull.2.2)))) :
    KeyIndStepSim S b forgetGdhShadow2 (Gdh2SimInv S b)
      (gdhShadowHandle2Atomic gdhLift2Key S (keyIndKFuelsOfBudget S b))
      (liftKeyInd1Stage tlGapDhKeyInd S (fgKeyIndGapDh2Prog S b.q_total)).handle t := by
  intro c s' hB hRoom hInv
  let pa := (projVal _root_.SignalPqxdh.Security.ReductionDsl.KeyInd.gdhState2Ty s'.1).1
  let sm := (projVal _root_.SignalPqxdh.Security.ReductionDsl.KeyInd.gdhState2Ty s'.1).2
  let fgSc := projVal fgSessCtrTy (s'.2.1, s'.2.2.1)
  have hs1 : embedVal _root_.SignalPqxdh.Security.ReductionDsl.KeyInd.gdhState2Ty (pa, sm) = s'.1 :=
    Computational.Proofs.SignalPqxdh.AtomicLift.embedVal_projVal _ s'.1
  have hfgSc : embedVal fgSessCtrTy fgSc = (s'.2.1, s'.2.2.1) :=
    Computational.Proofs.SignalPqxdh.AtomicLift.embedVal_projVal fgSessCtrTy (s'.2.1, s'.2.2.1)
  have hInvSm : GdhSimInv S b c
      (embedVal simTy sm,
        ((embedVal fgSessCtrTy fgSc).1, ((embedVal fgSessCtrTy fgSc).2, s'.2.2.2))) := by
    have hSmEq : embedVal simTy sm = s'.1.2 := congrArg Prod.snd hs1
    have hFg1 : (embedVal fgSessCtrTy fgSc).1 = s'.2.1 := congrArg Prod.fst hfgSc
    have hFg2 : (embedVal fgSessCtrTy fgSc).2 = s'.2.2.1 := congrArg Prod.snd hfgSc
    rw [hSmEq, hFg1, hFg2]; exact hInv
  have hStep := hSim c pa sm fgSc s'.2 hB hRoom hInvSm
  have hArmEval :
      (liftKind0SessArm gdhLift2Key S payE (wrapSimSessArm bodyK)).eval
        (.cons pay (.cons s' (.cons ((pqKeyIndCodec S).qenc t) .nil))) =
      (fun r =>
        (embedVal keyIndRespTy r.1,
          ((embedVal params2Ty pa, embedVal simTy r.2.1),
            ((embedVal fgSessCtrTy r.2.2).1, ((embedVal fgSessCtrTy r.2.2).2, s'.2.2.2))))) <$>
        (bodyK .zero .zero .zero .zero (.succ .zero)).eval
          (.cons fgSc (.cons sm.1 (.cons sm (.cons pa (.cons (pa, sm)
            (.cons ((pa, sm), fgSc) (.cons payLeg .nil))))))) := by
    unfold liftKind0SessArm
    simp only [Comp.eval,
      Computational.Proofs.SignalPqxdh.Security.ReductionDsl.KindSplit.KeyIndCoreKSimBase.runAt2_eval,
      _root_.ReductionDsl.Expr.v0, _root_.ReductionDsl.Expr.v1, _root_.ReductionDsl.Expr.v2,
      Expr.eval, Env.get, hPayE s', map_eq_bind_pure_comp, Function.comp_def]
    have hEnv :
        (Env.cons (s'.1, (s'.2.1, s'.2.2.1)) (.cons (embedVal qPayTy payLeg) .nil) :
          Env [embedTy (.prod _root_.SignalPqxdh.Security.ReductionDsl.KeyInd.gdhState2Ty fgSessCtrTy),
            embedTy qPayTy]) =
        embedEnv (.cons ((pa, sm), fgSc) (.cons payLeg .nil) :
          Env [.prod _root_.SignalPqxdh.Security.ReductionDsl.KeyInd.gdhState2Ty fgSessCtrTy, qPayTy]) := by
      dsimp only [embedEnv]
      rw [← hs1, ← hfgSc]
      rfl
    rw [hEnv, gdhLift2Key_valid.liftGdhAtomic_eval _ hUnsupK _]
    simp only [wrapSimSessArm, letV, bindV, smBase, v,
      Ext.step_wk', Ext.refl_wk', Env.get_zero', Env.get_succ',
      Comp.eval, Expr.eval, bind_assoc, pure_bind, map_eq_bind_pure_comp, Function.comp_def]
    rfl
  rw [hDispK s', hArmEval]
  refine ⟨?_, ?_⟩
  · have hRhs :
        (liftKeyInd1Stage tlGapDhKeyInd S (fgKeyIndGapDh2Prog S b.q_total)).handle.eval
          (.cons (forgetGdhShadow2 s') (.cons ((pqKeyIndCodec S).qenc t) .nil)) =
        embedVal (.prod keyIndRespTy _root_.SignalPqxdh.Security.ReductionDsl.KeyInd.gdhState2Ty) <$>
          (_root_.SignalPqxdh.Security.ReductionDsl.KeyInd.gdhHandle2 S b.q_total).eval
            (.cons (pa, sm) (.cons ((_root_.SignalPqxdh.LegacyCosted.keyIndCodec S).qenc t) .nil)) := by
      have hf : forgetGdhShadow2 s' =
          embedVal _root_.SignalPqxdh.Security.ReductionDsl.KeyInd.gdhState2Ty (pa, sm) := hs1.symm
      rw [hf]
      exact Computational.Proofs.SignalPqxdh.AtomicLift.liftKeyIndHandle_eval
        tlGapDhKeyInd S (_root_.SignalPqxdh.Security.ReductionDsl.KeyInd.gdhHandle2 S b.q_total)
        (gdhHandle2_unsup_h2 S b.q_total) (pa, sm) t
    refine Eq.trans ?_ hRhs.symm
    rw [hDispQ pa sm, ← hStep.1]
    simp only [_root_.Functor.map_map, Prod.map, id, forgetGdhShadow2, embedVal]
  · intro p hp
    simp only [support_map, Set.mem_image] at hp
    rcases hp with ⟨r, hr, rfl⟩
    exact hStep.2 r hr

private theorem wrapSim2_eval_h2 {Γ₁ Δ : List PT} [Ext Γ₁ Δ]
    (pa : Var Γ₁ params2Ty)
    (c : Comp pqxdhOps pqGapDhIface Δ (.prod keyIndRespTy simTy)) (env : Env Δ) :
    (_root_.SignalPqxdh.Security.ReductionDsl.KeyInd.wrapSim2 pa c).eval env =
      (fun rq => (rq.1, ((v pa).eval env, rq.2))) <$> c.eval env := by
  simp only [_root_.SignalPqxdh.Security.ReductionDsl.KeyInd.wrapSim2, bindV, v,
    Ext.step_wk', Ext.refl_wk', Env.get_zero', Env.get_succ', Comp.eval, Expr.eval,
    map_eq_bind_pure_comp, Function.comp_def]

/-- `.initiateOPK` step simulation for tuple-keyed `gdhShadowHandle2Atomic`. -/
theorem gdhShadowHandle2_hStep_initiateOPK (S : Setup) (b : QueryBudget) :
    ∀ u i bu, KeyIndStepSim S b forgetGdhShadow2 (Gdh2SimInv S b)
      (gdhShadowHandle2Atomic gdhLift2Key S (keyIndKFuelsOfBudget S b))
      (liftKeyInd1Stage tlGapDhKeyInd S (fgKeyIndGapDh2Prog S b.q_total)).handle
      (.initiateOPK u i bu) := by
  intro u i bu
  refine gdhShadowHandle2_sess_step S b (.initiateOPK u i bu)
    (u, (i, _root_.ReductionDsl.bundleV bu))
    (u.val, (i.val, _root_.SignalPqxdh.LegacyCosted.bundleV bu))
    (Computational.Proofs.SignalPqxdh.Security.ReductionDsl.KindSplit.KeyIndCoreK.initPayToNatE
      S.N_send_opk S .v0)
    (fun pa sm bSt fgSh x => initiateGdh2ShadowB S (keyIndKFuelsOfBudget S b) pa sm bSt fgSh true x)
    _
    (wrapSimSessArm_initiate2_unsup_h2 S (keyIndKFuelsOfBudget S b) true)
    (fun s' => by
      unfold gdhShadowHandle2Atomic
      exact Computational.Proofs.SignalPqxdh.Security.ReductionDsl.KindSplit.KeyIndCoreKSimBase.dispatchKeyIndQ_eval
        S _ _ _ _ _ _ _ _ _ _ _ _ _ _ s' (.initiateOPK u i bu))
    (fun _ => by rcases bu with ⟨_, _, _, _, _ | ⟨_, _⟩, _, _, _⟩ <;> rfl)
    (fun pa sm => by
      simp only [_root_.SignalPqxdh.Security.ReductionDsl.KeyInd.gdhHandle2,
        _root_.SignalPqxdh.LegacyCosted.keyIndCodec,
        _root_.SignalPqxdh.LegacyCosted.keyIndQenc,
        letV_eval, caseSumV, smBase, v,
        Ext.step_wk', Ext.refl_wk', Env.get_zero', Env.get_succ',
        Comp.eval, Expr.eval, wrapSim2_eval_h2]
      rfl)
    (fun c pa sm fgSc fgFull hB hRoom hInv => by
      exact initiateGdh2ShadowB_sim S b true .zero .zero .zero .zero (.succ .zero)
        .zero .zero .zero .zero _ _ c (.initiateOPK u i bu) fgFull
        rfl rfl rfl rfl rfl
        (by simp [keyIndSimPred, _root_.SignalPqxdh.isKeyIndOnlineQuery])
        (by simp [keyIndSimPred, _root_.SignalPqxdh.isKeyIndRoQuery])
        hB hRoom
        (by simpa only [v, Ext.step_wk', Ext.refl_wk', Env.get_zero', Env.get_succ', Expr.eval]
          using hInv))

/-- `.initiateNoOPK` step simulation for tuple-keyed `gdhShadowHandle2Atomic`. -/
theorem gdhShadowHandle2_hStep_initiateNoOPK (S : Setup) (b : QueryBudget) :
    ∀ u i bu, KeyIndStepSim S b forgetGdhShadow2 (Gdh2SimInv S b)
      (gdhShadowHandle2Atomic gdhLift2Key S (keyIndKFuelsOfBudget S b))
      (liftKeyInd1Stage tlGapDhKeyInd S (fgKeyIndGapDh2Prog S b.q_total)).handle
      (.initiateNoOPK u i bu) := by
  intro u i bu
  refine gdhShadowHandle2_sess_step S b (.initiateNoOPK u i bu)
    (u, (i, _root_.ReductionDsl.bundleV bu))
    (u.val, (i.val, _root_.SignalPqxdh.LegacyCosted.bundleV bu))
    (Computational.Proofs.SignalPqxdh.Security.ReductionDsl.KindSplit.KeyIndCoreK.initPayToNatE
      S.N_send_no_opk S .v0)
    (fun pa sm bSt fgSh x => initiateGdh2ShadowB S (keyIndKFuelsOfBudget S b) pa sm bSt fgSh false x)
    _
    (wrapSimSessArm_initiate2_unsup_h2 S (keyIndKFuelsOfBudget S b) false)
    (fun s' => by
      unfold gdhShadowHandle2Atomic
      exact Computational.Proofs.SignalPqxdh.Security.ReductionDsl.KindSplit.KeyIndCoreKSimBase.dispatchKeyIndQ_eval
        S _ _ _ _ _ _ _ _ _ _ _ _ _ _ s' (.initiateNoOPK u i bu))
    (fun _ => by rcases bu with ⟨_, _, _, _, _ | ⟨_, _⟩, _, _, _⟩ <;> rfl)
    (fun pa sm => by
      simp only [_root_.SignalPqxdh.Security.ReductionDsl.KeyInd.gdhHandle2,
        _root_.SignalPqxdh.LegacyCosted.keyIndCodec,
        _root_.SignalPqxdh.LegacyCosted.keyIndQenc,
        letV_eval, caseSumV, smBase, v,
        Ext.step_wk', Ext.refl_wk', Env.get_zero', Env.get_succ',
        Comp.eval, Expr.eval, wrapSim2_eval_h2]
      rfl)
    (fun c pa sm fgSc fgFull hB hRoom hInv => by
      exact initiateGdh2ShadowB_sim S b false .zero .zero .zero .zero (.succ .zero)
        .zero .zero .zero .zero _ _ c (.initiateNoOPK u i bu) fgFull
        rfl rfl rfl rfl rfl
        (by simp [keyIndSimPred, _root_.SignalPqxdh.isKeyIndOnlineQuery])
        (by simp [keyIndSimPred, _root_.SignalPqxdh.isKeyIndRoQuery])
        hB hRoom
        (by simpa only [v, Ext.step_wk', Ext.refl_wk', Env.get_zero', Env.get_succ', Expr.eval]
          using hInv))

/-- `.acceptOPK` step simulation for tuple-keyed `gdhShadowHandle2Atomic`. -/
theorem gdhShadowHandle2_hStep_acceptOPK (S : Setup) (b : QueryBudget) :
    ∀ k j o hdr, KeyIndStepSim S b forgetGdhShadow2 (Gdh2SimInv S b)
      (gdhShadowHandle2Atomic gdhLift2Key S (keyIndKFuelsOfBudget S b))
      (liftKeyInd1Stage tlGapDhKeyInd S (fgKeyIndGapDh2Prog S b.q_total)).handle
      (.acceptOPK k j o hdr) := by
  intro k j o hdr
  refine gdhShadowHandle2_sess_step S b (.acceptOPK k j o hdr)
    (k, (j, (o, _root_.ReductionDsl.hdrV hdr)))
    (k.val, (j.val, (o.val, _root_.SignalPqxdh.LegacyCosted.hdrV hdr)))
    (Computational.Proofs.SignalPqxdh.Security.ReductionDsl.KindSplit.KeyIndCoreK.accPayToNatE
      S.N_opk S .v0)
    (fun pa sm bSt fgSh x => acceptOpkGdh2ShadowB S (keyIndKFuelsOfBudget S b) pa sm bSt fgSh x)
    _
    (wrapSimSessArm_acceptOpk2_unsup_h2 S (keyIndKFuelsOfBudget S b))
    (fun s' => by
      unfold gdhShadowHandle2Atomic
      exact Computational.Proofs.SignalPqxdh.Security.ReductionDsl.KindSplit.KeyIndCoreKSimBase.dispatchKeyIndQ_eval
        S _ _ _ _ _ _ _ _ _ _ _ _ _ _ s' (.acceptOPK k j o hdr))
    (fun _ => by rcases hdr with ⟨_, _, _, _ | _, _, _⟩ <;> rfl)
    (fun pa sm => by
      simp only [_root_.SignalPqxdh.Security.ReductionDsl.KeyInd.gdhHandle2,
        _root_.SignalPqxdh.LegacyCosted.keyIndCodec,
        _root_.SignalPqxdh.LegacyCosted.keyIndQenc,
        letV_eval, caseSumV, smBase, v,
        Ext.step_wk', Ext.refl_wk', Env.get_zero', Env.get_succ',
        Comp.eval, Expr.eval, wrapSim2_eval_h2]
      rfl)
    (fun c pa sm fgSc fgFull hB hRoom hInv => by
      exact acceptOpkGdh2ShadowB_sim S b .zero .zero .zero .zero (.succ .zero)
        .zero .zero .zero .zero _ _ c (.acceptOPK k j o hdr) fgFull
        rfl rfl rfl rfl rfl
        (by simp [keyIndSimPred, _root_.SignalPqxdh.isKeyIndOnlineQuery])
        (by simp [keyIndSimPred, _root_.SignalPqxdh.isKeyIndRoQuery])
        hB hRoom
        (by simpa only [v, Ext.step_wk', Ext.refl_wk', Env.get_zero', Env.get_succ', Expr.eval]
          using hInv))

/-- `.acceptNoOPK` step simulation for tuple-keyed `gdhShadowHandle2Atomic`. -/
theorem gdhShadowHandle2_hStep_acceptNoOPK (S : Setup) (b : QueryBudget) :
    ∀ k j l hdr, KeyIndStepSim S b forgetGdhShadow2 (Gdh2SimInv S b)
      (gdhShadowHandle2Atomic gdhLift2Key S (keyIndKFuelsOfBudget S b))
      (liftKeyInd1Stage tlGapDhKeyInd S (fgKeyIndGapDh2Prog S b.q_total)).handle
      (.acceptNoOPK k j l hdr) := by
  intro k j l hdr
  refine gdhShadowHandle2_sess_step S b (.acceptNoOPK k j l hdr)
    (k, (j, (l, _root_.ReductionDsl.hdrV hdr)))
    (k.val, (j.val, (l.val, _root_.SignalPqxdh.LegacyCosted.hdrV hdr)))
    (Computational.Proofs.SignalPqxdh.Security.ReductionDsl.KindSplit.KeyIndCoreK.accPayToNatE
      S.N_no_opk S .v0)
    (fun _ sm bSt fgSh x => acceptNoOpkGdhShadowB S (keyIndKFuelsOfBudget S b) sm bSt fgSh x)
    _
    (wrapSimSessArm_acceptNoOpk2_unsup_h2 S (keyIndKFuelsOfBudget S b))
    (fun s' => by
      unfold gdhShadowHandle2Atomic
      exact Computational.Proofs.SignalPqxdh.Security.ReductionDsl.KindSplit.KeyIndCoreKSimBase.dispatchKeyIndQ_eval
        S _ _ _ _ _ _ _ _ _ _ _ _ _ _ s' (.acceptNoOPK k j l hdr))
    (fun _ => by rcases hdr with ⟨_, _, _, _ | _, _, _⟩ <;> rfl)
    (fun pa sm => by
      simp only [_root_.SignalPqxdh.Security.ReductionDsl.KeyInd.gdhHandle2,
        _root_.SignalPqxdh.LegacyCosted.keyIndCodec,
        _root_.SignalPqxdh.LegacyCosted.keyIndQenc,
        letV_eval, caseSumV, smBase, v,
        Ext.step_wk', Ext.refl_wk', Env.get_zero', Env.get_succ',
        Comp.eval, Expr.eval, wrapSim2_eval_h2]
      rfl)
    (fun c pa sm fgSc fgFull hB hRoom hInv => by
      exact acceptNoOpkGdhShadowB_sim S b .zero .zero .zero (.succ .zero)
        .zero .zero .zero _ _ c (.acceptNoOPK k j l hdr) fgFull
        rfl rfl rfl rfl
        (by simp [keyIndSimPred, _root_.SignalPqxdh.isKeyIndOnlineQuery])
        (by simp [keyIndSimPred, _root_.SignalPqxdh.isKeyIndRoQuery])
        hB hRoom
        (by simpa only [v, Ext.step_wk', Ext.refl_wk', Env.get_zero', Env.get_succ', Expr.eval]
          using hInv))

section Stage1HandleHelpers

open _root_.ReductionDsl (bundleT hdrT bundleV hdrV)
open _root_.SignalPqxdh.LegacyCosted (keyIndCodec keyIndQenc)
open Computational.Proofs.SignalPqxdh.AtomicLift (
  aop embedVal_projVal keyIndUnsupportedPrimW liftKeyIndHandle liftKeyIndHandle_eval
)
open Computational.Proofs.SignalPqxdh.Security.ReductionDsl.KindSplit.KeyIndCoreK (
  initPayToNatE accPayToNatE dispatchKeyIndQ runAt2
)
open Computational.Proofs.SignalPqxdh.Security.ReductionDsl.KindSplit.KeyIndCoreKSimBase (
  dispatchKeyIndQ_eval runAt2_eval
)
open Computational.Proofs.SignalPqxdh.Security.ReductionDsl.KindSplit.KeyIndGapDhKSimBase (
  entryMatchesC_unsupported_zero
)
open _root_.SignalPqxdh.Security.ReductionDsl.KeyInd (
  gdhStateTy gdhHandle wrapBase wrapSim
  initPrinGdhB genSpkGdhB genOpkGdhB initiateGdhB acceptOpkGdhB acceptNoOpkGdhB
  corruptB testB roParsedC roRawFallbackC revealB registerGdhB revealSpkB
  rNone sRandom64 qSigPkGen qSigSign qKemKeyGen mkPairPosC
  preKeyBundleToVal handshakeHdrToVal paOpkMode
)

set_option allowUnsafeReducibility true
attribute [local implicit_reducible]
  _root_.SignalPqxdh.LegacyCosted.pqChalIface
  _root_.SignalPqxdh.LegacyCosted.pqPrimIface
  _root_.SignalPqxdh.LegacyCosted.pqGapDhIface
  _root_.SignalPqxdh.gapDhOracleSpec
  _root_.SignalPqxdh.LegacyCosted.gapDhDdhOracle
  fgKeyIndGapDhProg
  _root_.ReductionDsl.CostedReduction.σ
  Env.get

@[local simp] private theorem liftBase_queries_loc
    {C : _root_.SignalPqxdh.LegacyCosted.ChallengerOracle}
    (w : (_root_.SignalPqxdh.LegacyCosted.pqChalIface C).Tag → ℕ)
    (ws : (_root_.SignalPqxdh.LegacyCosted.pqChalIface C).smp.Samp → ℕ)
    {Γ : List PT} {τ : PT} (c : Comp pqxdhOps pqPrimIface Γ τ) :
    (_root_.SignalPqxdh.Security.ReductionDsl.KeyInd.liftBase (C := C) c).queries w ws =
      Comp.queries (I := pqPrimIface) (fun g => w (.inl g)) (fun s => ws s) c := by
  induction c <;> simp_all [_root_.SignalPqxdh.Security.ReductionDsl.KeyInd.liftBase, Comp.queries]

@[local simp] private theorem wrapBase_unsupported {Γ₁ Γ₂ Δ : List PT} [Ext Γ₁ Δ] [Ext Γ₂ Δ]
    (pa : Var Γ₁ paramsTy) (sm : Var Γ₂ simTy)
    (c : Comp pqxdhOps pqPrimIface Δ (.prod keyIndRespTy keyIndStateTy)) :
    (wrapBase pa sm c).queries tlGapDhKeyInd.unsupportedW (fun _ => 0) =
      c.queries keyIndUnsupportedPrimW (fun _ => 0) := by
  simp [wrapBase, gPrim, bindV, Comp.queries, tlGapDhKeyInd]

@[local simp] private theorem wrapSim_unsupported {Γ₁ Δ : List PT} [Ext Γ₁ Δ]
    (pa : Var Γ₁ paramsTy)
    (c : Comp pqxdhOps pqGapDhIface Δ (.prod keyIndRespTy simTy)) :
    (wrapSim pa c).queries tlGapDhKeyInd.unsupportedW (fun _ => 0) =
      c.queries tlGapDhKeyInd.unsupportedW (fun _ => 0) := by
  simp [wrapSim, bindV, Comp.queries]

private theorem wrapSimSessArm_unsupported {paTy qPayTy : PT}
    (body :
      Var [paTy, .prod paTy simTy, .prod (.prod paTy simTy) fgSessCtrTy, qPayTy] paTy →
      Var [simTy, paTy, .prod paTy simTy, .prod (.prod paTy simTy) fgSessCtrTy, qPayTy] simTy →
      Var [keyIndStateTy, simTy, paTy, .prod paTy simTy,
        .prod (.prod paTy simTy) fgSessCtrTy, qPayTy] keyIndStateTy →
      Var [fgSessCtrTy, keyIndStateTy, simTy, paTy, .prod paTy simTy,
        .prod (.prod paTy simTy) fgSessCtrTy, qPayTy] fgSessCtrTy →
      Var [.prod (.prod paTy simTy) fgSessCtrTy, qPayTy] qPayTy →
      Comp pqxdhOps pqGapDhIface
        [fgSessCtrTy, keyIndStateTy, simTy, paTy, .prod paTy simTy,
          .prod (.prod paTy simTy) fgSessCtrTy, qPayTy]
        (.prod keyIndRespTy (.prod simTy fgSessCtrTy)))
    (hBody :
      (body .zero .zero .zero .zero (.succ .zero)).queries
        tlGapDhKeyInd.unsupportedW (fun _ => 0) = 0) :
    (wrapSimSessArm body).queries tlGapDhKeyInd.unsupportedW (fun _ => 0) = 0 := by
  simp [wrapSimSessArm, letV, bindV, Comp.queries, hBody]

private theorem initiateGdhShadowB_unsupported (S : Setup) (f : KeyIndKFuels) (hasOpk : Bool)
    {Γ₁ Γ₂ Γ₃ Γ₄ Γ₅ Δ : List PT}
    [Ext Γ₁ Δ] [Ext Γ₂ Δ] [Ext Γ₃ Δ] [Ext Γ₄ Δ] [Ext Γ₅ Δ]
    (pa : Var Γ₁ paramsTy) (sm : Var Γ₂ simTy) (bSt : Var Γ₃ keyIndStateTy)
    (fgSh : Var Γ₅ fgSessCtrTy) (x : Var Γ₄ initQTy) :
    (initiateGdhShadowB (Δ := Δ) S f pa sm bSt fgSh hasOpk x).queries
        tlGapDhKeyInd.unsupportedW (fun _ => 0) = 0 := by
  simp only [initiateGdhShadowB, fgPatchShadowC, entryMatchesC_unsupported_zero,
    gPrim, chooseInitRandC, lookupSpkSkC, computePosC, mkPairPosC, mkSecretPosC, computeOptPosInitC,
    findHonestC, honestPeerC, checkProvC, koskBundleOkPowsC, isGameSpkC, isGameOpkC,
    resolveSigPkC, partnerC, findMV, anyMV, letV, bindV, caseOptV, Comp.queries,
    liftBase_queries_loc]
  simp [sBytes32, sDrKey96, qX25519, qX25519Base, qPow8, qIsCanonical,
    qSigVerify, qKemEncaps, Comp.queries,
    tlGapDhKeyInd, keyIndUnsupportedPrimW]

private theorem acceptOpkGdhShadowB_unsupported (S : Setup) (f : KeyIndKFuels)
    {Γ₁ Γ₂ Γ₃ Γ₄ Γ₅ Δ : List PT}
    [Ext Γ₁ Δ] [Ext Γ₂ Δ] [Ext Γ₃ Δ] [Ext Γ₄ Δ] [Ext Γ₅ Δ]
    (pa : Var Γ₁ paramsTy) (sm : Var Γ₂ simTy) (bSt : Var Γ₃ keyIndStateTy)
    (fgSh : Var Γ₅ fgSessCtrTy) (x : Var Γ₄ accQTy) :
    (acceptOpkGdhShadowB (Δ := Δ) S f pa sm bSt fgSh x).queries
        tlGapDhKeyInd.unsupportedW (fun _ => 0) = 0 := by
  simp only [acceptOpkGdhShadowB, acceptOpkGdhCoreShadowB, fgPatchShadowC, entryMatchesC_unsupported_zero,
    finishAcceptGdhC, gPrim, chooseRespRandC, computePosC, mkPairPosC, mkSecretPosC,
    findHonestC, koskSenderOkPowsC, partnerC, findMV, letV, bindV, caseOptV,
    Comp.queries, liftBase_queries_loc]
  simp [sDrKey96, qX25519, qPow8, qIsCanonical, qKemDecaps, Comp.queries,
    tlGapDhKeyInd, keyIndUnsupportedPrimW]

private theorem acceptNoOpkGdhShadowB_unsupported (S : Setup) (f : KeyIndKFuels)
    {Γ₂ Γ₃ Γ₄ Γ₅ Δ : List PT}
    [Ext Γ₂ Δ] [Ext Γ₃ Δ] [Ext Γ₄ Δ] [Ext Γ₅ Δ]
    (sm : Var Γ₂ simTy) (bSt : Var Γ₃ keyIndStateTy)
    (fgSh : Var Γ₅ fgSessCtrTy) (x : Var Γ₄ accQTy) :
    (acceptNoOpkGdhShadowB (Δ := Δ) S f sm bSt fgSh x).queries
        tlGapDhKeyInd.unsupportedW (fun _ => 0) = 0 := by
  simp only [acceptNoOpkGdhShadowB, fgPatchShadowC, entryMatchesC_unsupported_zero,
    finishAcceptGdhC, gPrim, chooseRespRandC, computePosC, mkPairPosC, mkSecretPosC,
    findHonestC, koskSenderOkPowsC, partnerC, findMV, letV, bindV, caseOptV,
    Comp.queries, liftBase_queries_loc]
  simp [sDrKey96, qX25519, qPow8, qIsCanonical, qKemDecaps, Comp.queries,
    tlGapDhKeyInd, keyIndUnsupportedPrimW]

private theorem gdhHandle_unsupported (S : Setup) (K : Nat) :
    (gdhHandle S K).queries tlGapDhKeyInd.unsupportedW (fun _ => 0) = 0 := by
  simp only [gdhHandle, wrapBase_unsupported, wrapSim_unsupported, entryMatchesC_unsupported_zero,
    initPrinGdhB, genSpkGdhB, genOpkGdhB, initiateGdhB, acceptOpkGdhB, acceptNoOpkGdhB,
    finishAcceptGdhC, corruptB, testB, roParsedC, roRawFallbackC, revealB, registerGdhB, revealSpkB,
    gPrim, chooseInitRandC, chooseRespRandC, lookupSpkSkC, computePosC, mkPairPosC, fgPatchC,
    findHonestC, honestPeerC, checkProvC, koskBundleOkPowsC, koskSenderOkPowsC, computeOptPosInitC,
    mkSecretPosC, isGameSpkC, isGameOpkC, resolveSigPkC, partnerC, findMV, anyMV,
    liftBase_queries_loc, letV, bindV, caseOptV, caseSumV, Comp.queries]
  simp [sBytes32, sRandom64, sDrKey96, qX25519, qX25519Base, qPow8, qIsCanonical,
    qSigPkGen, qSigSign, qSigVerify, qKemKeyGen, qKemEncaps, qKemDecaps, Comp.queries,
    tlGapDhKeyInd, keyIndUnsupportedPrimW]

private theorem initPayToNatE_eval (N_s : ℕ) (S : Setup) {σ : Ty pqAtomicSig}
    (u : Fin S.N_id) (i : Fin N_s) (bu : _root_.SignalPqxdh.PreKeyBundleInput)
    (s : σ.denote) (qEnc : (pqKeyIndCodec S).Q.denote) :
    (initPayToNatE N_s S
      (_root_.ReductionDsl.Expr.v0 :
        Expr pqAtomicOps
          [.prod (.base (.fin S.N_id)) (.prod (.base (.fin N_s)) (bundleT (ℓ := 0) (Pt := Empty))),
           σ, (pqKeyIndCodec S).Q] _)).eval
      (.cons (u, (i, bundleV bu)) (.cons s (.cons qEnc .nil))) =
      embedVal initQTy (u.val, (i.val, preKeyBundleToVal bu)) := by
  rcases bu with ⟨_, _, _, _, _ | ⟨_, _⟩, _, _, _⟩ <;> rfl

private theorem accPayToNatE_eval (N_o : ℕ) (S : Setup) {σ : Ty pqAtomicSig}
    (k : Fin S.N_id) (j : Fin S.N_recv) (o : Fin N_o) (hdr : _root_.SignalPqxdh.HandshakeHdr)
    (s : σ.denote) (qEnc : (pqKeyIndCodec S).Q.denote) :
    (accPayToNatE N_o S
      (_root_.ReductionDsl.Expr.v0 :
        Expr pqAtomicOps
          [.prod (.base (.fin S.N_id))
            (.prod (.base (.fin S.N_recv))
              (.prod (.base (.fin N_o)) (hdrT (ℓ := 0) (Pt := Empty)))),
           σ, (pqKeyIndCodec S).Q] _)).eval
      (.cons (k, (j, (o, hdrV hdr))) (.cons s (.cons qEnc .nil))) =
      embedVal accQTy (k.val, (j.val, (o.val, handshakeHdrToVal hdr))) := by
  rcases hdr with ⟨_, _, _, _ | _, _, _⟩ <;> rfl

private theorem liftKind0SessArm_gdh2Key_eval (S : Setup)
    {paTy qPayTy : PT} {PayAtomic : Ty pqAtomicSig}
    (payE : Expr pqAtomicOps
      (PayAtomic :: [.prod (embedTy (.prod paTy simTy)) fgShadowAtomicTy, (pqKeyIndCodec S).Q])
      (embedTy qPayTy))
    (body :
      Var [paTy, .prod paTy simTy, .prod (.prod paTy simTy) fgSessCtrTy, qPayTy] paTy →
      Var [simTy, paTy, .prod paTy simTy, .prod (.prod paTy simTy) fgSessCtrTy, qPayTy] simTy →
      Var [keyIndStateTy, simTy, paTy, .prod paTy simTy,
        .prod (.prod paTy simTy) fgSessCtrTy, qPayTy] keyIndStateTy →
      Var [fgSessCtrTy, keyIndStateTy, simTy, paTy, .prod paTy simTy,
        .prod (.prod paTy simTy) fgSessCtrTy, qPayTy] fgSessCtrTy →
      Var [.prod (.prod paTy simTy) fgSessCtrTy, qPayTy] qPayTy →
      Comp pqxdhOps pqGapDhIface
        [fgSessCtrTy, keyIndStateTy, simTy, paTy, .prod paTy simTy,
          .prod (.prod paTy simTy) fgSessCtrTy, qPayTy]
        (.prod keyIndRespTy (.prod simTy fgSessCtrTy)))
    (hUnsup : (wrapSimSessArm body).queries tlGapDhKeyInd.unsupportedW (fun _ => 0) = 0)
    (payA : PayAtomic.denote)
    (s' : (Ty.prod (embedTy (.prod paTy simTy)) fgShadowAtomicTy).denote)
    (qEnc : (pqKeyIndCodec S).Q.denote)
    (payLeg : qPayTy.denote)
    (hPay : payE.eval (.cons payA (.cons s' (.cons qEnc .nil))) = embedVal qPayTy payLeg) :
    let paL : paTy.denote := projVal paTy s'.1.1
    let smL : simTy.denote := projVal simTy s'.1.2
    let fgScL : fgSessCtrTy.denote := projVal fgSessCtrTy (s'.2.1, s'.2.2.1)
    let env₁ : Env [fgSessCtrTy, keyIndStateTy, simTy, paTy, .prod paTy simTy,
        .prod (.prod paTy simTy) fgSessCtrTy, qPayTy] :=
      .cons fgScL (.cons smL.1 (.cons smL (.cons paL (.cons (paL, smL)
        (.cons ((paL, smL), fgScL) (.cons payLeg .nil))))))
    (liftKind0SessArm gdhLift2Key S payE (wrapSimSessArm body)).eval
        (.cons payA (.cons s' (.cons qEnc .nil))) =
      (fun r : (Ty.prod keyIndRespTy (.prod simTy fgSessCtrTy)).denote =>
        (embedVal keyIndRespTy r.1,
          ((embedVal paTy paL, embedVal simTy r.2.1),
            ((embedVal fgSessCtrTy r.2.2).1,
              ((embedVal fgSessCtrTy r.2.2).2, s'.2.2.2))))) <$>
        (body .zero .zero .zero .zero (.succ .zero)).eval env₁ := by
  intro paL smL fgScL env₁
  have hs1 : s'.1 = embedVal (.prod paTy simTy) (paL, smL) := by
    change s'.1 = (embedVal paTy paL, embedVal simTy smL)
    exact Prod.ext (embedVal_projVal paTy s'.1.1).symm (embedVal_projVal simTy s'.1.2).symm
  have hfg : (s'.2.1, s'.2.2.1) = embedVal fgSessCtrTy fgScL :=
    (embedVal_projVal fgSessCtrTy (s'.2.1, s'.2.2.1)).symm
  simp only [liftKind0SessArm, Comp.eval]
  rw [runAt2_eval]
  have hEnv :
      Env.cons ((Expr.pair (.fst _root_.ReductionDsl.Expr.v1)
        (.pair (.fst (.snd _root_.ReductionDsl.Expr.v1))
          (.fst (.snd (.snd _root_.ReductionDsl.Expr.v1)))) :
        Expr pqAtomicOps
          (PayAtomic :: [.prod (embedTy (.prod paTy simTy)) fgShadowAtomicTy, (pqKeyIndCodec S).Q])
          (embedTy (.prod (.prod paTy simTy) fgSessCtrTy))).eval
          (.cons payA (.cons s' (.cons qEnc .nil))))
        (.cons (payE.eval (.cons payA (.cons s' (.cons qEnc .nil)))) .nil) =
      embedEnv (Env.cons (t := .prod (.prod paTy simTy) fgSessCtrTy) ((paL, smL), fgScL)
        (.cons payLeg .nil)) := by
    simp only [Expr.eval, _root_.ReductionDsl.Expr.v1, Env.get, hs1, hfg, hPay]; rfl
  rw [hEnv, gdhLift2Key_valid.liftGdhAtomic_eval (wrapSimSessArm body) hUnsup]
  simp only [wrapSimSessArm, smBase, letV, bindV, Comp.eval, Expr.eval,
    v_eval_cons, v_zero_eval, map_eq_bind_pure_comp, bind_assoc, pure_bind,
    Function.comp_def, _root_.ReductionDsl.Expr.v0, _root_.ReductionDsl.Expr.v2, Env.get]
  rfl

private theorem wrapSim_eval_h1 {Γ₁ Δ : List PT} [Ext Γ₁ Δ]
    (pa : Var Γ₁ paramsTy)
    (c : Comp pqxdhOps pqGapDhIface Δ (.prod keyIndRespTy simTy)) (env : Env Δ) :
    (wrapSim pa c).eval env =
      (fun rq => (rq.1, ((v pa).eval env, rq.2))) <$> c.eval env := by
  simp only [wrapSim, bindV, v, Ext.step_wk', Ext.refl_wk', Env.get_zero', Env.get_succ',
    Comp.eval, Expr.eval, map_eq_bind_pure_comp, Function.comp_def]

private theorem gdhShadowHandle_sess_step
    (S : Setup) (b : QueryBudget) (t : KeyIndQuery S)
    {qPayTy : PT} {PayAtomic : Ty pqAtomicSig}
    (pay : PayAtomic.denote) (payLeg : qPayTy.denote)
    (payE : Expr pqAtomicOps
      (PayAtomic :: [.prod (embedTy gdhStateTy) fgShadowAtomicTy, (pqKeyIndCodec S).Q])
      (embedTy qPayTy))
    (bodyK :
      Var [paramsTy, gdhStateTy, .prod gdhStateTy fgSessCtrTy, qPayTy] paramsTy →
      Var [simTy, paramsTy, gdhStateTy, .prod gdhStateTy fgSessCtrTy, qPayTy] simTy →
      Var [keyIndStateTy, simTy, paramsTy, gdhStateTy, .prod gdhStateTy fgSessCtrTy, qPayTy] keyIndStateTy →
      Var [fgSessCtrTy, keyIndStateTy, simTy, paramsTy, gdhStateTy, .prod gdhStateTy fgSessCtrTy, qPayTy] fgSessCtrTy →
      Var [.prod gdhStateTy fgSessCtrTy, qPayTy] qPayTy →
      Comp pqxdhOps pqGapDhIface
        [fgSessCtrTy, keyIndStateTy, simTy, paramsTy, gdhStateTy, .prod gdhStateTy fgSessCtrTy, qPayTy]
        (.prod keyIndRespTy (.prod simTy fgSessCtrTy)))
    (rhsComp : paramsTy.denote → simTy.denote →
      OracleComp GdhSimSpec (keyIndRespTy.denote × simTy.denote))
    (hUnsupK : (wrapSimSessArm bodyK).queries tlGapDhKeyInd.unsupportedW (fun _ => 0) = 0)
    (hDispK : ∀ s' : gdhShadowStateAtomicTy.denote,
      (gdhShadowHandleAtomic gdhLift2Key S (keyIndKFuelsOfBudget S b)).eval
        (.cons s' (.cons ((pqKeyIndCodec S).qenc t) .nil)) =
      (liftKind0SessArm gdhLift2Key S payE (wrapSimSessArm bodyK)).eval
        (.cons pay (.cons s' (.cons ((pqKeyIndCodec S).qenc t) .nil))))
    (hPayE : ∀ s' : gdhShadowStateAtomicTy.denote,
      payE.eval (.cons pay (.cons s' (.cons ((pqKeyIndCodec S).qenc t) .nil))) =
        embedVal qPayTy payLeg)
    (hDispQ : ∀ (pa : paramsTy.denote) (sm : simTy.denote),
      (gdhHandle S b.q_total).eval
        (.cons (pa, sm) (.cons ((keyIndCodec S).qenc t) .nil)) =
      (fun rq => (rq.1, (pa, rq.2))) <$> rhsComp pa sm)
    (hSim : ∀ (c : Fin 3 → ℕ) (pa : paramsTy.denote) (sm : simTy.denote)
        (fgSc : fgSessCtrTy.denote) (fgFull : fgShadowAtomicTy.denote),
      (∀ j, c j ≤ keyIndSimBounds b j) →
      (∀ j, keyIndSimPred S j t → c j + 1 ≤ keyIndSimBounds b j) →
      GdhSimInv S b c
        (embedVal simTy sm,
          ((embedVal fgSessCtrTy fgSc).1, ((embedVal fgSessCtrTy fgSc).2, fgFull.2.2))) →
      (fun r => (r.1, r.2.1)) <$>
        (bodyK .zero .zero .zero .zero (.succ .zero)).eval
          (.cons fgSc (.cons sm.1 (.cons sm (.cons pa (.cons (pa, sm)
            (.cons ((pa, sm), fgSc) (.cons payLeg .nil))))))) =
        rhsComp pa sm ∧
      ∀ r ∈ support
        ((bodyK .zero .zero .zero .zero (.succ .zero)).eval
          (.cons fgSc (.cons sm.1 (.cons sm (.cons pa (.cons (pa, sm)
            (.cons ((pa, sm), fgSc) (.cons payLeg .nil)))))))),
        GdhSimInv S b (bumpPred (keyIndSimPred S) c t)
          (embedVal simTy r.2.1,
            ((embedVal fgSessCtrTy r.2.2).1, ((embedVal fgSessCtrTy r.2.2).2, fgFull.2.2)))) :
    KeyIndStepSim S b forgetGdhShadow
      (fun c (st : gdhShadowStateAtomicTy.denote) => GdhSimInv S b c (st.1.2, st.2))
      (gdhShadowHandleAtomic gdhLift2Key S (keyIndKFuelsOfBudget S b))
      (liftKeyInd1Stage tlGapDhKeyInd S (fgKeyIndGapDhProg S b.q_total)).handle t := by
  intro c s' hB hRoom hInv
  let pa := projVal paramsTy s'.1.1
  let sm := projVal simTy s'.1.2
  let fgSc := projVal fgSessCtrTy (s'.2.1, s'.2.2.1)
  have hs1 : embedVal gdhStateTy (pa, sm) = s'.1 := by
    change (embedVal paramsTy pa, embedVal simTy sm) = s'.1
    exact Prod.ext (embedVal_projVal paramsTy s'.1.1) (embedVal_projVal simTy s'.1.2)
  have hfgSc : embedVal fgSessCtrTy fgSc = (s'.2.1, s'.2.2.1) :=
    embedVal_projVal fgSessCtrTy (s'.2.1, s'.2.2.1)
  have hInvSm : GdhSimInv S b c
      (embedVal simTy sm,
        ((embedVal fgSessCtrTy fgSc).1, ((embedVal fgSessCtrTy fgSc).2, s'.2.2.2))) := by
    rw [embedVal_projVal simTy s'.1.2, hfgSc]; exact hInv
  have hStep := hSim c pa sm fgSc s'.2 hB hRoom hInvSm
  have hArmEval := liftKind0SessArm_gdh2Key_eval S payE bodyK hUnsupK pay s'
    ((pqKeyIndCodec S).qenc t) payLeg (hPayE s')
  rw [hDispK s', hArmEval]
  refine ⟨?_, ?_⟩
  · have hRhs :
        (liftKeyInd1Stage tlGapDhKeyInd S (fgKeyIndGapDhProg S b.q_total)).handle.eval
          (.cons (forgetGdhShadow s') (.cons ((pqKeyIndCodec S).qenc t) .nil)) =
        embedVal (.prod keyIndRespTy gdhStateTy) <$>
          (gdhHandle S b.q_total).eval
            (.cons (pa, sm) (.cons ((keyIndCodec S).qenc t) .nil)) := by
      have hf : forgetGdhShadow s' = embedVal gdhStateTy (pa, sm) := hs1.symm
      rw [hf]
      exact liftKeyIndHandle_eval tlGapDhKeyInd S (gdhHandle S b.q_total)
        (gdhHandle_unsupported S b.q_total) (pa, sm) t
    refine Eq.trans ?_ hRhs.symm
    rw [hDispQ pa sm, ← hStep.1]
    simp only [_root_.Functor.map_map, Prod.map, id, forgetGdhShadow, embedVal]; rfl
  · intro p hp
    simp only [support_map, Set.mem_image] at hp
    rcases hp with ⟨r, hr, rfl⟩
    exact hStep.2 r hr

/-- `.initiateOPK` step simulation for stage-1 `gdhShadowHandleAtomic`. -/
theorem gdhShadowHandle_hStep_initiateOPK (S : Setup) (b : QueryBudget) :
    ∀ u i bu, KeyIndStepSim S b forgetGdhShadow
      (fun c (st : gdhShadowStateAtomicTy.denote) => GdhSimInv S b c (st.1.2, st.2))
      (gdhShadowHandleAtomic gdhLift2Key S (keyIndKFuelsOfBudget S b))
      (liftKeyInd1Stage tlGapDhKeyInd S (fgKeyIndGapDhProg S b.q_total)).handle
      (.initiateOPK u i bu) := by
  intro u i bu
  refine gdhShadowHandle_sess_step S b (.initiateOPK u i bu)
    (u, (i, bundleV bu))
    (u.val, (i.val, preKeyBundleToVal bu))
    (initPayToNatE S.N_send_opk S .v0)
    (fun pa sm bSt fgSh x => initiateGdhShadowB S (keyIndKFuelsOfBudget S b) pa sm bSt fgSh true x)
    _
    (wrapSimSessArm_unsupported _ (initiateGdhShadowB_unsupported S _ true _ _ _ _ _))
    (fun s' => by
      unfold gdhShadowHandleAtomic
      exact dispatchKeyIndQ_eval S _ _ _ _ _ _ _ _ _ _ _ _ _ _ s' (.initiateOPK u i bu))
    (fun s' => initPayToNatE_eval S.N_send_opk S u i bu s' _)
    (fun pa sm => by
      simp only [gdhHandle, keyIndCodec, keyIndQenc, letV_eval, caseSumV, smBase, v,
        Ext.step_wk', Ext.refl_wk', Env.get_zero', Env.get_succ',
        Comp.eval, Expr.eval, wrapSim_eval_h1]
      rfl)
    (fun c pa sm fgSc fgFull hB hRoom hInv => by
      exact initiateGdhShadowB_sim S b true .zero .zero .zero .zero (.succ .zero)
        .zero .zero .zero .zero _ _ c (.initiateOPK u i bu) fgFull
        rfl rfl rfl rfl rfl
        (by simp [keyIndSimPred, _root_.SignalPqxdh.isKeyIndOnlineQuery])
        (by simp [keyIndSimPred, _root_.SignalPqxdh.isKeyIndRoQuery])
        hB hRoom
        (by simpa only [v, Ext.step_wk', Ext.refl_wk', Env.get_zero', Env.get_succ', Expr.eval]
          using hInv))

/-- `.initiateNoOPK` step simulation for stage-1 `gdhShadowHandleAtomic`. -/
theorem gdhShadowHandle_hStep_initiateNoOPK (S : Setup) (b : QueryBudget) :
    ∀ u i bu, KeyIndStepSim S b forgetGdhShadow
      (fun c (st : gdhShadowStateAtomicTy.denote) => GdhSimInv S b c (st.1.2, st.2))
      (gdhShadowHandleAtomic gdhLift2Key S (keyIndKFuelsOfBudget S b))
      (liftKeyInd1Stage tlGapDhKeyInd S (fgKeyIndGapDhProg S b.q_total)).handle
      (.initiateNoOPK u i bu) := by
  intro u i bu
  refine gdhShadowHandle_sess_step S b (.initiateNoOPK u i bu)
    (u, (i, bundleV bu))
    (u.val, (i.val, preKeyBundleToVal bu))
    (initPayToNatE S.N_send_no_opk S .v0)
    (fun pa sm bSt fgSh x => initiateGdhShadowB S (keyIndKFuelsOfBudget S b) pa sm bSt fgSh false x)
    _
    (wrapSimSessArm_unsupported _ (initiateGdhShadowB_unsupported S _ false _ _ _ _ _))
    (fun s' => by
      unfold gdhShadowHandleAtomic
      exact dispatchKeyIndQ_eval S _ _ _ _ _ _ _ _ _ _ _ _ _ _ s' (.initiateNoOPK u i bu))
    (fun s' => initPayToNatE_eval S.N_send_no_opk S u i bu s' _)
    (fun pa sm => by
      simp only [gdhHandle, keyIndCodec, keyIndQenc, letV_eval, caseSumV, smBase, v,
        Ext.step_wk', Ext.refl_wk', Env.get_zero', Env.get_succ',
        Comp.eval, Expr.eval, wrapSim_eval_h1]
      rfl)
    (fun c pa sm fgSc fgFull hB hRoom hInv => by
      exact initiateGdhShadowB_sim S b false .zero .zero .zero .zero (.succ .zero)
        .zero .zero .zero .zero _ _ c (.initiateNoOPK u i bu) fgFull
        rfl rfl rfl rfl rfl
        (by simp [keyIndSimPred, _root_.SignalPqxdh.isKeyIndOnlineQuery])
        (by simp [keyIndSimPred, _root_.SignalPqxdh.isKeyIndRoQuery])
        hB hRoom
        (by simpa only [v, Ext.step_wk', Ext.refl_wk', Env.get_zero', Env.get_succ', Expr.eval]
          using hInv))

/-- `.acceptOPK` step simulation for stage-1 `gdhShadowHandleAtomic`. -/
theorem gdhShadowHandle_hStep_acceptOPK (S : Setup) (b : QueryBudget) :
    ∀ k j o hdr, KeyIndStepSim S b forgetGdhShadow
      (fun c (st : gdhShadowStateAtomicTy.denote) => GdhSimInv S b c (st.1.2, st.2))
      (gdhShadowHandleAtomic gdhLift2Key S (keyIndKFuelsOfBudget S b))
      (liftKeyInd1Stage tlGapDhKeyInd S (fgKeyIndGapDhProg S b.q_total)).handle
      (.acceptOPK k j o hdr) := by
  intro k j o hdr
  refine gdhShadowHandle_sess_step S b (.acceptOPK k j o hdr)
    (k, (j, (o, hdrV hdr)))
    (k.val, (j.val, (o.val, handshakeHdrToVal hdr)))
    (accPayToNatE S.N_opk S .v0)
    (fun pa sm bSt fgSh x => acceptOpkGdhShadowB S (keyIndKFuelsOfBudget S b) pa sm bSt fgSh x)
    _
    (wrapSimSessArm_unsupported _ (acceptOpkGdhShadowB_unsupported S _ _ _ _ _ _))
    (fun s' => by
      unfold gdhShadowHandleAtomic
      exact dispatchKeyIndQ_eval S _ _ _ _ _ _ _ _ _ _ _ _ _ _ s' (.acceptOPK k j o hdr))
    (fun s' => accPayToNatE_eval S.N_opk S k j o hdr s' _)
    (fun pa sm => by
      simp only [gdhHandle, keyIndCodec, keyIndQenc, letV_eval, caseSumV, smBase, v,
        Ext.step_wk', Ext.refl_wk', Env.get_zero', Env.get_succ',
        Comp.eval, Expr.eval, wrapSim_eval_h1]
      rfl)
    (fun c pa sm fgSc fgFull hB hRoom hInv => by
      exact acceptOpkGdhShadowB_sim S b .zero .zero .zero .zero (.succ .zero)
        .zero .zero .zero .zero _ _ c (.acceptOPK k j o hdr) fgFull
        rfl rfl rfl rfl rfl
        (by simp [keyIndSimPred, _root_.SignalPqxdh.isKeyIndOnlineQuery])
        (by simp [keyIndSimPred, _root_.SignalPqxdh.isKeyIndRoQuery])
        hB hRoom
        (by simpa only [v, Ext.step_wk', Ext.refl_wk', Env.get_zero', Env.get_succ', Expr.eval]
          using hInv))

/-- `.acceptNoOPK` step simulation for stage-1 `gdhShadowHandleAtomic`. -/
theorem gdhShadowHandle_hStep_acceptNoOPK (S : Setup) (b : QueryBudget) :
    ∀ k j l hdr, KeyIndStepSim S b forgetGdhShadow
      (fun c (st : gdhShadowStateAtomicTy.denote) => GdhSimInv S b c (st.1.2, st.2))
      (gdhShadowHandleAtomic gdhLift2Key S (keyIndKFuelsOfBudget S b))
      (liftKeyInd1Stage tlGapDhKeyInd S (fgKeyIndGapDhProg S b.q_total)).handle
      (.acceptNoOPK k j l hdr) := by
  intro k j l hdr
  refine gdhShadowHandle_sess_step S b (.acceptNoOPK k j l hdr)
    (k, (j, (l, hdrV hdr)))
    (k.val, (j.val, (l.val, handshakeHdrToVal hdr)))
    (accPayToNatE S.N_no_opk S .v0)
    (fun _ sm bSt fgSh x => acceptNoOpkGdhShadowB S (keyIndKFuelsOfBudget S b) sm bSt fgSh x)
    _
    (wrapSimSessArm_unsupported _ (acceptNoOpkGdhShadowB_unsupported S _ _ _ _ _))
    (fun s' => by
      unfold gdhShadowHandleAtomic
      exact dispatchKeyIndQ_eval S _ _ _ _ _ _ _ _ _ _ _ _ _ _ s' (.acceptNoOPK k j l hdr))
    (fun s' => accPayToNatE_eval S.N_no_opk S k j l hdr s' _)
    (fun pa sm => by
      simp only [gdhHandle, keyIndCodec, keyIndQenc, letV_eval, caseSumV, smBase, v,
        Ext.step_wk', Ext.refl_wk', Env.get_zero', Env.get_succ',
        Comp.eval, Expr.eval, wrapSim_eval_h1]
      rfl)
    (fun c pa sm fgSc fgFull hB hRoom hInv => by
      exact acceptNoOpkGdhShadowB_sim S b .zero .zero .zero (.succ .zero)
        .zero .zero .zero _ _ c (.acceptNoOPK k j l hdr) fgFull
        rfl rfl rfl rfl
        (by simp [keyIndSimPred, _root_.SignalPqxdh.isKeyIndOnlineQuery])
        (by simp [keyIndSimPred, _root_.SignalPqxdh.isKeyIndRoQuery])
        hB hRoom
        (by simpa only [v, Ext.step_wk', Ext.refl_wk', Env.get_zero', Env.get_succ', Expr.eval]
          using hInv))

end Stage1HandleHelpers

section SessSigProgramWrappers

open _root_.SignalPqxdh.Security (keyIndQueryKind)
open _root_.SignalPqxdh.LegacyCosted (keyIndCodec)
open Computational.Proofs.SignalPqxdh.AtomicLift (
  aop embedVal_projVal compRename compRename_eval
  tlPrimKeyInd keyIndUnsupportedPrimW liftKeyIndHandle liftKeyIndHandle_eval
)
open _root_.SignalPqxdh.Security.ReductionDsl.KeyInd (
  keyIndQueryTy gdhState2Ty sig1KeyStTy rNone rs
  gdhHandle2 pa2Mk pa2U pa2V pa2Up pa2DhFlag pa2EphTarget pa2OpkMode
  ephSidMatchesE wrapBase2 wrapSim2 initPrinGdh2B genSpkGdh2B genOpkGdh2B
  initiateGdh2B acceptOpkGdh2B acceptNoOpkGdhB corruptB testB roParsedC roRawFallbackC
  revealB registerGdhB revealSpkB initSidE sidEq
  paU paV paUp paDhFlag paEphIdx paOpkMode
  s1Forgery s1Fg s1Pk s1Upd sig1KeyTargetGenSpkB
  liftGdhToSigDdh liftGdhToSigDdh_eval renamePair
)
open _root_.SignalPqxdh.Security.ReductionDsl.KeyInd1KeyGapDh (
  gdh1KeyStateTy liftGdhComp liftGdhComp_eval liftGdhToSign_pure
  twoVarRen pullEnv_twoVarRen renameComp renameComp_eval
)
open Computational.Proofs.SignalPqxdh.Delta.KeyInd1KeyActiveProgs (
  sig1KeyActiveStTy S1ARS saTP saInner extract1KeyActiveC
  sig1KeyActiveInitPrinB sig1KeyActiveInitiateCheckC sig1KeyActivePreDispatchC
  sig1KeyActiveHandleC sigKeyInd1KeyActiveDslProg
  gdh1KeyActiveStateTy callGdhActiveHandle
  initPrin1KeyActiveGdhB genSpk1KeyActiveGdhB genSpkGdhActiveB genOpkActiveGdhB
  initiateActiveGdhB initiateGdhActiveInnerB gdh1KeyActiveHandle
  fgKeyInd1KeyGapDhActiveDslProg
)
open Computational.Proofs.SignalPqxdh.Delta.KindSplit.KeyInd1KeyKindProgs (
  sig1KeyActiveKindStTy gdh1KeyActiveKindStateTy
  sigKindInitiateSessLeg sigKindAcceptOpkSessLeg sigKindAcceptNoOpkSessLeg
  gdhKindInitiateSessLeg gdhKindAcceptOpkSessLeg gdhKindAcceptNoOpkSessLeg
  liftSigDdhSessArm
)
open Computational.Proofs.SignalPqxdh.Security.ReductionDsl.KindSplit.KeyIndCoreK (
  dispatchKeyIndQ runAt2 atomicRNoneE initPayToNatE accPayToNatE
)
open Computational.Proofs.SignalPqxdh.Security.ReductionDsl.KindSplit.KeyIndCoreKSimBase (
  keyIndSimPred_one_iff_kind dispatchKeyIndQ_eval runAt2_eval
)
open Computational.Proofs.SignalPqxdh.Security.ReductionDsl.KindSplit.KeyIndGapDhKSimBase (
  ddhEqC_unsupported_zero ddhEqOptC_unsupported_zero entryMatchesC_unsupported_zero
  fixSig1KeyActiveSent fixGdh1KeyActiveSent
)

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

private theorem sessWrap_bumpPred_online_0 {S : Setup} {c : Fin 3 → ℕ} {t : KeyIndQuery S}
    (hOn : keyIndQueryKind t = 0) :
    bumpPred (keyIndSimPred S) c t 0 = c 0 + 1 := by
  have hP : keyIndSimPred S 0 t := (keyIndSimPred_zero_iff_kind t).mpr hOn
  simp [bumpPred, hP]

private theorem sessWrap_bumpPred_online_1 {S : Setup} {c : Fin 3 → ℕ} {t : KeyIndQuery S}
    (hOn : keyIndQueryKind t = 0) :
    bumpPred (keyIndSimPred S) c t 1 = c 1 := by
  have hNot : ¬ keyIndSimPred S 1 t := by
    rw [keyIndSimPred_one_iff_kind, hOn]; decide
  simp [bumpPred, hNot]

private theorem sessWrap_bumpPred_online_2 {S : Setup} {c : Fin 3 → ℕ} {t : KeyIndQuery S}
    (_hOn : keyIndQueryKind t = 0) :
    bumpPred (keyIndSimPred S) c t 2 = c 2 + 1 := by
  have hP : keyIndSimPred S 2 t := trivial
  simp [bumpPred, hP]

private theorem sessWrap_simPred_0 {S : Setup} {t : KeyIndQuery S}
    (hOn : keyIndQueryKind t = 0) :
    keyIndSimPred S 0 t = (true = true) :=
  propext ⟨fun _ => rfl, fun _ => (keyIndSimPred_zero_iff_kind t).mpr hOn⟩

private theorem sessWrap_simPred_1 {S : Setup} {t : KeyIndQuery S}
    (hOn : keyIndQueryKind t = 0) :
    keyIndSimPred S 1 t = (false = true) := by
  have hNot : ¬ keyIndSimPred S 1 t := by
    rw [keyIndSimPred_one_iff_kind, hOn]; decide
  exact propext ⟨fun h => False.elim (hNot h), Bool.noConfusion⟩

private theorem sessWrap_GdhSimInv_bump_online_unchanged {S : Setup} {b : QueryBudget}
    {c : Fin 3 → ℕ} {t : KeyIndQuery S} {sK : simShadowAtomicTy.denote}
    (hInv : GdhSimInv S b c sK) (hOn : keyIndQueryKind t = 0) :
    GdhSimInv S b (bumpPred (keyIndSimPred S) c t) sK := by
  have hb0 := sessWrap_bumpPred_online_0 (c := c) hOn
  have hb1 := sessWrap_bumpPred_online_1 (c := c) hOn
  have hb2 := sessWrap_bumpPred_online_2 (c := c) hOn
  have ho := hInv.online_len
  refine
    { online_len :=
        { prin_le  := by rw [hb0]; exact Nat.le_succ_of_le ho.prin_le
          spks_le  := by rw [hb0]; exact Nat.le_succ_of_le ho.spks_le
          opks_le  := by rw [hb0]; exact Nat.le_succ_of_le ho.opks_le
          sess_le  := by rw [hb0]; exact Nat.le_succ_of_le ho.sess_le
          resps_le := by rw [hb0]; exact Nat.le_succ_of_le ho.resps_le
          usedO_le := by rw [hb0]; exact Nat.le_succ_of_le ho.usedO_le
          usedN_le := by rw [hb0]; exact Nat.le_succ_of_le ho.usedN_le
          kyb_le   := by rw [hb0]; exact Nat.le_succ_of_le ho.kyb_le
          adv_le   := by rw [hb0]; exact Nat.le_succ_of_le ho.adv_le
          counts_eq := by rw [hb0, hb1, hb2]; have := ho.counts_eq; omega }
      fg_sess_le := by rw [hb0]; exact Nat.le_succ_of_le hInv.fg_sess_le
      fg_shadow  := by rw [hb1]; exact hInv.fg_shadow
      raw_len    := by rw [hb1]; exact hInv.raw_len
      raw_shadow := hInv.raw_shadow
      log_len    := by rw [hb1]; exact hInv.log_len
      pows_len   := by rw [hb0]; exact Nat.le_succ_of_le hInv.pows_len }

@[local simp] private theorem sessWrap_liftGdhToSigDdh_unsupported {Γ : List PT} {t : PT}
    (c : Comp pqxdhOps pqGapDhIface Γ t) :
    (liftGdhToSigDdh c).queries tlSigDdhKeyInd.unsupportedW (fun _ => 0) =
      c.queries tlGapDhKeyInd.unsupportedW (fun _ => 0) := by
  induction c with
  | query g _ => rcases g with _ | ⟨⟩ <;> rfl
  | sample _ _ => rfl
  | _ => simp_all [liftGdhToSigDdh, Comp.queries]

@[local simp] private theorem sessWrap_liftBase_queries_loc
    {C : _root_.SignalPqxdh.LegacyCosted.ChallengerOracle}
    (w : (_root_.SignalPqxdh.LegacyCosted.pqChalIface C).Tag → ℕ)
    (ws : (_root_.SignalPqxdh.LegacyCosted.pqChalIface C).smp.Samp → ℕ)
    {Γ : List PT} {τ : PT} (c : Comp pqxdhOps pqPrimIface Γ τ) :
    (_root_.SignalPqxdh.Security.ReductionDsl.KeyInd.liftBase (C := C) c).queries w ws =
      Comp.queries (I := pqPrimIface) (fun g => w (.inl g)) (fun s => ws s) c := by
  induction c <;> simp_all [_root_.SignalPqxdh.Security.ReductionDsl.KeyInd.liftBase, Comp.queries]

@[local simp] private theorem sessWrap_comp_rename_queries_loc {ι : Type} {T : OracleSpec ι}
    {I : Iface pqSig T} (w : I.Tag → ℕ) (ws : I.smp.Samp → ℕ) :
    ∀ {Γ Δ : List PT} {t : PT} (c : Comp pqxdhOps I Γ t) (ρ : ∀ {τ}, Var Γ τ → Var Δ τ),
      (c.rename ρ).queries w ws = c.queries w ws := by
  intro Γ Δ t c ρ
  induction c generalizing Δ <;> simp_all [_root_.ReductionDsl.Comp.rename, Comp.queries]

@[local simp] private theorem sessWrap_wrapBase2_unsupported {Γ₁ Γ₂ Δ : List PT} [Ext Γ₁ Δ] [Ext Γ₂ Δ]
    (pa : Var Γ₁ params2Ty) (sm : Var Γ₂ simTy)
    (c : Comp pqxdhOps pqPrimIface Δ (.prod keyIndRespTy keyIndStateTy)) :
    (wrapBase2 pa sm c).queries tlGapDhKeyInd.unsupportedW (fun _ => 0) =
      c.queries keyIndUnsupportedPrimW (fun _ => 0) := by
  simp [wrapBase2, _root_.SignalPqxdh.Security.ReductionDsl.KeyInd.gPrim, bindV, Comp.queries,
    tlGapDhKeyInd]

@[local simp] private theorem sessWrap_wrapSim2_unsupported {Γ₁ Δ : List PT} [Ext Γ₁ Δ]
    (pa : Var Γ₁ params2Ty)
    (c : Comp pqxdhOps pqGapDhIface Δ (.prod keyIndRespTy simTy)) :
    (wrapSim2 pa c).queries tlGapDhKeyInd.unsupportedW (fun _ => 0) =
      c.queries tlGapDhKeyInd.unsupportedW (fun _ => 0) := by
  simp [wrapSim2, bindV, Comp.queries]

private theorem sessWrap_gdhHandle2_unsupported (S : Setup) (K : Nat) :
    (gdhHandle2 S K).queries tlGapDhKeyInd.unsupportedW (fun _ => 0) = 0 := by
  simp only [gdhHandle2, sessWrap_wrapBase2_unsupported, sessWrap_wrapSim2_unsupported,
    entryMatchesC_unsupported_zero,
    initPrinGdh2B, genSpkGdh2B, genOpkGdh2B, initiateGdh2B, acceptOpkGdh2B,
    acceptNoOpkGdhB, finishAcceptGdhC, corruptB, testB, roParsedC, roRawFallbackC,
    revealB, registerGdhB, revealSpkB, _root_.SignalPqxdh.Security.ReductionDsl.KeyInd.gPrim,
    _root_.SignalPqxdh.Security.ReductionDsl.KeyInd.chooseInitRandC,
    _root_.SignalPqxdh.Security.ReductionDsl.KeyInd.chooseRespRandC,
    _root_.SignalPqxdh.Security.ReductionDsl.KeyInd.lookupSpkSkC,
    _root_.SignalPqxdh.Security.ReductionDsl.KeyInd.computePosC,
    _root_.SignalPqxdh.Security.ReductionDsl.KeyInd.mkPairPosC,
    _root_.SignalPqxdh.Security.ReductionDsl.KeyInd.fgPatchC,
    _root_.SignalPqxdh.Security.ReductionDsl.KeyInd.findHonestC,
    _root_.SignalPqxdh.Security.ReductionDsl.KeyInd.honestPeerC,
    _root_.SignalPqxdh.Security.ReductionDsl.KeyInd.checkProvC,
    _root_.SignalPqxdh.Security.ReductionDsl.KeyInd.koskBundleOkPowsC,
    _root_.SignalPqxdh.Security.ReductionDsl.KeyInd.koskSenderOkPowsC,
    _root_.SignalPqxdh.Security.ReductionDsl.KeyInd.computeOptPosInitC,
    _root_.SignalPqxdh.Security.ReductionDsl.KeyInd.mkSecretPosC,
    _root_.SignalPqxdh.Security.ReductionDsl.KeyInd.isGameSpkC,
    _root_.SignalPqxdh.Security.ReductionDsl.KeyInd.isGameOpkC,
    _root_.SignalPqxdh.Security.ReductionDsl.KeyInd.resolveSigPkC,
    _root_.SignalPqxdh.Security.ReductionDsl.KeyInd.partnerC,
    _root_.SignalPqxdh.Security.ReductionDsl.KeyInd.findMV,
    _root_.SignalPqxdh.Security.ReductionDsl.KeyInd.anyMV,
    sessWrap_liftBase_queries_loc, letV, bindV, caseOptV, caseSumV, Comp.queries]
  simp [_root_.SignalPqxdh.Security.ReductionDsl.KeyInd.sBytes32,
    _root_.SignalPqxdh.Security.ReductionDsl.KeyInd.sRandom64,
    _root_.SignalPqxdh.Security.ReductionDsl.KeyInd.sDrKey96,
    _root_.SignalPqxdh.Security.ReductionDsl.KeyInd.qX25519,
    _root_.SignalPqxdh.Security.ReductionDsl.KeyInd.qX25519Base,
    _root_.SignalPqxdh.Security.ReductionDsl.KeyInd.qPow8,
    _root_.SignalPqxdh.Security.ReductionDsl.KeyInd.qIsCanonical,
    _root_.SignalPqxdh.Security.ReductionDsl.KeyInd.qSigPkGen,
    _root_.SignalPqxdh.Security.ReductionDsl.KeyInd.qSigSign,
    _root_.SignalPqxdh.Security.ReductionDsl.KeyInd.qSigVerify,
    _root_.SignalPqxdh.Security.ReductionDsl.KeyInd.qKemKeyGen,
    _root_.SignalPqxdh.Security.ReductionDsl.KeyInd.qKemEncaps,
    _root_.SignalPqxdh.Security.ReductionDsl.KeyInd.qKemDecaps,
    Comp.queries, tlGapDhKeyInd, keyIndUnsupportedPrimW]

private theorem sessWrap_sigActive_handle_unsupported (S : Setup) (b : QueryBudget) :
    (sigKeyInd1KeyActiveDslProg S b).handle.queries tlSigDdhKeyInd.unsupportedW (fun _ => 0) = 0 := by
  change (sig1KeyActiveHandleC S b.q_total).queries tlSigDdhKeyInd.unsupportedW (fun _ => 0) = 0
  simp only [sig1KeyActiveHandleC, sig1KeyActivePreDispatchC, sig1KeyActiveInitPrinB,
    sig1KeyTargetGenSpkB, sig1KeyActiveInitiateCheckC, extract1KeyActiveC,
    _root_.SignalPqxdh.Security.ReductionDsl.KeyInd.s1Prim,
    _root_.SignalPqxdh.Security.ReductionDsl.KeyInd.honestPeerC,
    _root_.SignalPqxdh.Security.ReductionDsl.KeyInd.findHonestC,
    _root_.SignalPqxdh.Security.ReductionDsl.KeyInd.findMV,
    sessWrap_liftGdhToSigDdh_unsupported, sessWrap_comp_rename_queries_loc,
    sessWrap_gdhHandle2_unsupported S b.q_total,
    sessWrap_liftBase_queries_loc, letV, bindV, caseOptV, caseSumV, Comp.queries]
  simp [_root_.SignalPqxdh.Security.ReductionDsl.KeyInd.sBytes32,
    _root_.SignalPqxdh.Security.ReductionDsl.KeyInd.sRandom64,
    _root_.SignalPqxdh.Security.ReductionDsl.KeyInd.qX25519Base,
    _root_.SignalPqxdh.Security.ReductionDsl.KeyInd.qPow8,
    _root_.SignalPqxdh.Security.ReductionDsl.KeyInd.qSigVerify,
    _root_.SignalPqxdh.Security.ReductionDsl.KeyInd.qKemKeyGen,
    _root_.SignalPqxdh.Security.ReductionDsl.KeyInd.qSigDdhSign,
    Comp.queries, tlSigDdhKeyInd, keyIndUnsupportedPrimW]

private theorem sessWrap_sigKindInitiateSessLeg_unsupported (S : Setup) (f : KeyIndKFuels)
    (hasOpk : Bool) :
    (sigKindInitiateSessLeg S f hasOpk).queries tlSigDdhKeyInd.unsupportedW (fun _ => 0) = 0 := by
  simp only [sigKindInitiateSessLeg, extract1KeyActiveC, initiateGdh2ShadowB, fgPatchShadowC,
    entryMatchesC_unsupported_zero, sessWrap_liftGdhToSigDdh_unsupported,
    _root_.SignalPqxdh.Security.ReductionDsl.KeyInd.s1Prim,
    _root_.SignalPqxdh.Security.ReductionDsl.KeyInd.gPrim,
    _root_.SignalPqxdh.Security.ReductionDsl.KeyInd.chooseInitRandC,
    _root_.SignalPqxdh.Security.ReductionDsl.KeyInd.lookupSpkSkC,
    _root_.SignalPqxdh.Security.ReductionDsl.KeyInd.computePosC,
    _root_.SignalPqxdh.Security.ReductionDsl.KeyInd.mkPairPosC,
    _root_.SignalPqxdh.Security.ReductionDsl.KeyInd.findHonestC,
    _root_.SignalPqxdh.Security.ReductionDsl.KeyInd.honestPeerC,
    _root_.SignalPqxdh.Security.ReductionDsl.KeyInd.checkProvC,
    _root_.SignalPqxdh.Security.ReductionDsl.KeyInd.koskBundleOkPowsC,
    _root_.SignalPqxdh.Security.ReductionDsl.KeyInd.computeOptPosInitC,
    _root_.SignalPqxdh.Security.ReductionDsl.KeyInd.mkSecretPosC,
    _root_.SignalPqxdh.Security.ReductionDsl.KeyInd.isGameSpkC,
    _root_.SignalPqxdh.Security.ReductionDsl.KeyInd.isGameOpkC,
    _root_.SignalPqxdh.Security.ReductionDsl.KeyInd.resolveSigPkC,
    _root_.SignalPqxdh.Security.ReductionDsl.KeyInd.partnerC,
    _root_.SignalPqxdh.Security.ReductionDsl.KeyInd.findMV,
    _root_.SignalPqxdh.Security.ReductionDsl.KeyInd.anyMV,
    sessWrap_liftBase_queries_loc, letV, bindV, caseOptV, Comp.queries]
  simp [_root_.SignalPqxdh.Security.ReductionDsl.KeyInd.sBytes32,
    _root_.SignalPqxdh.Security.ReductionDsl.KeyInd.sDrKey96,
    _root_.SignalPqxdh.Security.ReductionDsl.KeyInd.qX25519,
    _root_.SignalPqxdh.Security.ReductionDsl.KeyInd.qX25519Base,
    _root_.SignalPqxdh.Security.ReductionDsl.KeyInd.qPow8,
    _root_.SignalPqxdh.Security.ReductionDsl.KeyInd.qIsCanonical,
    _root_.SignalPqxdh.Security.ReductionDsl.KeyInd.qSigVerify,
    _root_.SignalPqxdh.Security.ReductionDsl.KeyInd.qKemEncaps,
    Comp.queries, tlSigDdhKeyInd, tlGapDhKeyInd, keyIndUnsupportedPrimW]

private theorem sessWrap_sigKindAcceptOpkSessLeg_unsupported (S : Setup) (f : KeyIndKFuels) :
    (sigKindAcceptOpkSessLeg S f).queries tlSigDdhKeyInd.unsupportedW (fun _ => 0) = 0 := by
  simp only [sigKindAcceptOpkSessLeg, acceptOpkGdh2ShadowB, acceptOpkGdhCoreShadowB,
    finishAcceptGdhC, fgPatchShadowC, entryMatchesC_unsupported_zero,
    sessWrap_liftGdhToSigDdh_unsupported,
    _root_.SignalPqxdh.Security.ReductionDsl.KeyInd.gPrim,
    _root_.SignalPqxdh.Security.ReductionDsl.KeyInd.chooseRespRandC,
    _root_.SignalPqxdh.Security.ReductionDsl.KeyInd.computePosC,
    _root_.SignalPqxdh.Security.ReductionDsl.KeyInd.mkPairPosC,
    _root_.SignalPqxdh.Security.ReductionDsl.KeyInd.mkSecretPosC,
    _root_.SignalPqxdh.Security.ReductionDsl.KeyInd.findHonestC,
    _root_.SignalPqxdh.Security.ReductionDsl.KeyInd.koskSenderOkPowsC,
    _root_.SignalPqxdh.Security.ReductionDsl.KeyInd.partnerC,
    _root_.SignalPqxdh.Security.ReductionDsl.KeyInd.findMV,
    sessWrap_liftBase_queries_loc, letV, bindV, caseOptV, Comp.queries]
  simp [_root_.SignalPqxdh.Security.ReductionDsl.KeyInd.sDrKey96,
    _root_.SignalPqxdh.Security.ReductionDsl.KeyInd.qX25519,
    _root_.SignalPqxdh.Security.ReductionDsl.KeyInd.qPow8,
    _root_.SignalPqxdh.Security.ReductionDsl.KeyInd.qIsCanonical,
    _root_.SignalPqxdh.Security.ReductionDsl.KeyInd.qKemDecaps,
    Comp.queries, tlGapDhKeyInd, keyIndUnsupportedPrimW]

private theorem sessWrap_sigKindAcceptNoOpkSessLeg_unsupported (S : Setup) (f : KeyIndKFuels) :
    (sigKindAcceptNoOpkSessLeg S f).queries tlSigDdhKeyInd.unsupportedW (fun _ => 0) = 0 := by
  simp only [sigKindAcceptNoOpkSessLeg, acceptNoOpkGdhShadowB,
    finishAcceptGdhC, fgPatchShadowC, entryMatchesC_unsupported_zero,
    sessWrap_liftGdhToSigDdh_unsupported,
    _root_.SignalPqxdh.Security.ReductionDsl.KeyInd.gPrim,
    _root_.SignalPqxdh.Security.ReductionDsl.KeyInd.chooseRespRandC,
    _root_.SignalPqxdh.Security.ReductionDsl.KeyInd.computePosC,
    _root_.SignalPqxdh.Security.ReductionDsl.KeyInd.mkPairPosC,
    _root_.SignalPqxdh.Security.ReductionDsl.KeyInd.mkSecretPosC,
    _root_.SignalPqxdh.Security.ReductionDsl.KeyInd.findHonestC,
    _root_.SignalPqxdh.Security.ReductionDsl.KeyInd.koskSenderOkPowsC,
    _root_.SignalPqxdh.Security.ReductionDsl.KeyInd.partnerC,
    _root_.SignalPqxdh.Security.ReductionDsl.KeyInd.findMV,
    sessWrap_liftBase_queries_loc, letV, bindV, caseOptV, Comp.queries]
  simp [_root_.SignalPqxdh.Security.ReductionDsl.KeyInd.sDrKey96,
    _root_.SignalPqxdh.Security.ReductionDsl.KeyInd.qX25519,
    _root_.SignalPqxdh.Security.ReductionDsl.KeyInd.qPow8,
    _root_.SignalPqxdh.Security.ReductionDsl.KeyInd.qIsCanonical,
    _root_.SignalPqxdh.Security.ReductionDsl.KeyInd.qKemDecaps,
    Comp.queries, tlGapDhKeyInd, keyIndUnsupportedPrimW]

private theorem sessWrap_liftSigDdhSessArm_eval (S : Setup) {stTy qPayTy : PT}
    {PayAtomic : Ty pqAtomicSig}
    (payE : Expr pqAtomicOps
      (PayAtomic :: [.prod (embedTy stTy) fgShadowAtomicTy, (pqKeyIndCodec S).Q])
      (embedTy qPayTy))
    (arm : Comp pqxdhOps pqSigAndDdhIface [.prod stTy fgSessCtrTy, qPayTy]
      (.prod keyIndRespTy (.prod stTy fgSessCtrTy)))
    (hUnsup : arm.queries tlSigDdhKeyInd.unsupportedW (fun _ => 0) = 0)
    (payA : PayAtomic.denote) (stL : stTy.denote) (fgSc : fgSessCtrTy.denote)
    (sh : fgShadowAtomicTy.denote)
    (hSc : (sh.1, sh.2.1) = embedVal fgSessCtrTy fgSc)
    (qEnc : (pqKeyIndCodec S).Q.denote) (payLeg : qPayTy.denote)
    (hPay : payE.eval (.cons payA (.cons (embedVal stTy stL, sh) (.cons qEnc .nil))) =
      embedVal qPayTy payLeg) :
    (liftSigDdhSessArm S payE arm).eval
        (.cons payA (.cons (embedVal stTy stL, sh) (.cons qEnc .nil))) =
      (fun r => (embedVal keyIndRespTy r.1,
        (embedVal stTy r.2.1,
          ((embedVal fgSessCtrTy r.2.2).1, ((embedVal fgSessCtrTy r.2.2).2, sh.2.2))))) <$>
        arm.eval (.cons (stL, fgSc) (.cons payLeg .nil)) := by
  simp only [liftSigDdhSessArm, Comp.eval, runAt2_eval, Expr.eval, Env.get,
    Expr.v0, Expr.v1, Expr.v2, hSc, hPay]
  change (do
    let r ← (mapComp tlSigDdhKeyInd arm).eval (embedEnv (.cons (stL, fgSc) (.cons payLeg .nil)))
    pure (r.1, (r.2.1, (r.2.2.1, (r.2.2.2, sh.2.2))))) = _
  rw [mapComp_eval tlSigDdhKeyInd arm hUnsup, map_eq_bind_pure_comp, map_eq_bind_pure_comp]
  simp only [bind_assoc, pure_bind, Function.comp_def]
  rfl

private theorem sessWrap_sigActiveAtomic_handle_eval (S : Setup) (b : QueryBudget)
    (st : sig1KeyActiveStTy.denote) (t : KeyIndQuery S) :
    (sigKeyInd1KeyActiveAtomicProg S b).handle.eval
        (.cons (embedVal sig1KeyActiveStTy st : (sigKeyInd1KeyActiveAtomicProg S b).σ.denote)
          (.cons ((pqKeyIndCodec S).qenc t) .nil)) =
      embedVal S1ARS <$>
        (sig1KeyActiveHandleC S b.q_total).eval
          (.cons st (.cons ((keyIndCodec S).qenc t) .nil)) :=
  liftKeyIndHandle_eval tlSigDdhKeyInd S (sigKeyInd1KeyActiveDslProg S b).handle
    (sessWrap_sigActive_handle_unsupported S b) st t

private def sessWrap_fixSigLeg (S : Setup) (b : QueryBudget)
    (st : sig1KeyActiveStTy.denote) : sig1KeyActiveStTy.denote :=
  (st.1, (st.2.1, (fixSent S b st.2.2.1, st.2.2.2)))

private theorem sessWrap_forgetSig1KeyActiveK_embedVal (S : Setup) (b : QueryBudget)
    (st : sig1KeyActiveStTy.denote) (sh : fgShadowAtomicTy.denote) :
    forgetSig1KeyActiveK S b (embedVal sig1KeyActiveStTy st, sh) =
      embedVal sig1KeyActiveStTy (sessWrap_fixSigLeg S b st) := rfl

private theorem sessWrap_sig_liftGdh_step (S : Setup) (b : QueryBudget)
    (c' : Fin 3 → ℕ)
    (tp? : Option Nat) (ord : Nat) (pk : Bytes) (sigB : Nat)
    (sh : fgShadowAtomicTy.denote)
    (mK : OracleComp GdhSimSpec
      (keyIndRespTy.denote × (simTy.denote × fgSessCtrTy.denote)))
    (mOld : OracleComp GdhSimSpec (keyIndRespTy.denote × simTy.denote))
    (hEqM : (fun r => (r.1, r.2.1)) <$> mK = mOld)
    (hInvM : ∀ r ∈ support mK,
      GdhSimInv S b c'
        (embedVal simTy r.2.1,
          ((embedVal fgSessCtrTy r.2.2).1, ((embedVal fgSessCtrTy r.2.2).2, sh.2.2)))) :
    let outK : OracleComp _ ((pqKeyIndCodec S).R.denote × sig1KeyActiveKindStTy.denote) :=
      (fun r : keyIndRespTy.denote × (sig1KeyActiveStTy.denote × fgSessCtrTy.denote) =>
        (embedVal keyIndRespTy r.1,
          (embedVal sig1KeyActiveStTy r.2.1,
            ((embedVal fgSessCtrTy r.2.2).1, ((embedVal fgSessCtrTy r.2.2).2, sh.2.2))))) <$>
        ((fun r : keyIndRespTy.denote × (simTy.denote × fgSessCtrTy.denote) =>
          (r.1, ((tp?, (r.2.1, (ord, (pk, (sigB, none))))), r.2.2))) <$>
          liftGdhToSign mK)
    Prod.map id (forgetSig1KeyActiveK S b) <$> outK =
      embedVal S1ARS <$>
        ((fun p => (p.1, (tp?, (p.2, (fixSent S b ord, (pk, (sigB, none))))))) <$>
          liftGdhToSign mOld) ∧
    ∀ y ∈ support outK, Sig1KeyActiveSimInv S b c' y.2 := by
  intro outK
  constructor
  · have hLift : (fun r => (r.1, r.2.1)) <$> liftGdhToSign mK = liftGdhToSign mOld := by
      rw [← gdhLift1Key_valid.evalGdh_map, hEqM]
    calc Prod.map id (forgetSig1KeyActiveK S b) <$> outK
        = (fun p => (embedVal keyIndRespTy p.1,
            embedVal sig1KeyActiveStTy (tp?, (p.2, (fixSent S b ord, (pk, (sigB, none))))))) <$>
          ((fun r => (r.1, r.2.1)) <$> liftGdhToSign mK) := by
          simp only [outK, Functor.map_map]
          rfl
      _ = embedVal S1ARS <$>
          ((fun p => (p.1, (tp?, (p.2, (fixSent S b ord, (pk, (sigB, none))))))) <$>
            liftGdhToSign mOld) := by
          rw [hLift, Functor.map_map]
          rfl
  · intro y hy
    simp only [outK, map_eq_bind_pure_comp, mem_support_bind_iff,
      mem_support_pure_iff, Function.comp_def] at hy
    rcases hy with ⟨_, ⟨r, hrLift, rfl⟩, rfl⟩
    exact hInvM r (gdhLift1Key_valid.mem_support_evalGdh hrLift)

private theorem sessWrap_initPay_eval {N_s : ℕ} (S : Setup) {σ' : Ty pqAtomicSig}
    (u : Fin S.N_id) (i : Fin N_s) (bu : _root_.SignalPqxdh.PreKeyBundleInput)
    (s : σ'.denote) (qEnc : (pqKeyIndCodec S).Q.denote) :
    (initPayToNatE N_s S (Γ := [_, σ', (pqKeyIndCodec S).Q]) .v0).eval
        (.cons (u, (i, _root_.ReductionDsl.bundleV bu)) (.cons s (.cons qEnc .nil))) =
      embedVal initQTy (u.val, (i.val, _root_.SignalPqxdh.LegacyCosted.bundleV bu)) := by
  rcases bu with ⟨ikB, spkId, spkB, spkSig, _ | ⟨opkId, opkPk⟩, pqspkId, pqspkB, pqspkSig⟩ <;> rfl

private theorem sessWrap_accPay_eval {N_o : ℕ} (S : Setup) {σ' : Ty pqAtomicSig}
    (k : Fin S.N_id) (j : Fin S.N_recv) (o : Fin N_o) (hdr : _root_.SignalPqxdh.HandshakeHdr)
    (s : σ'.denote) (qEnc : (pqKeyIndCodec S).Q.denote) :
    (accPayToNatE N_o S (Γ := [_, σ', (pqKeyIndCodec S).Q]) .v0).eval
        (.cons (k, (j, (o, _root_.ReductionDsl.hdrV hdr))) (.cons s (.cons qEnc .nil))) =
      embedVal accQTy (k.val, (j.val, (o.val, _root_.SignalPqxdh.LegacyCosted.hdrV hdr))) := by
  rcases hdr with ⟨ikAPk, ekAPk, spkId, _ | opkId, pqspkId, kemCt⟩ <;> rfl

private theorem sessWrap_gdhHandle2_eval_initiateOPK (S : Setup) (K : Nat)
    (pa2 : params2Ty.denote) (sm : simTy.denote)
    (u : Fin S.N_id) (i : Fin S.N_send_opk) (bu : _root_.SignalPqxdh.PreKeyBundleInput) :
    ∃ (Γ₁ Γ₂ Γ₃ Γ₄ Δ : List PT)
      (paV : Var Γ₁ params2Ty) (smV : Var Γ₂ simTy) (bStV : Var Γ₃ keyIndStateTy)
      (xV : Var Γ₄ initQTy)
      (_ : Ext Γ₁ Δ) (_ : Ext Γ₂ Δ) (_ : Ext Γ₃ Δ) (_ : Ext Γ₄ Δ)
      (env : Env Δ),
      (gdhHandle2 S K).eval
          (.cons (pa2, sm) (.cons ((keyIndCodec S).qenc (.initiateOPK u i bu)) .nil)) =
        (fun r => (r.1, (pa2, r.2))) <$>
          (initiateGdh2B S K paV smV bStV true xV).eval env ∧
      (v paV).eval env = pa2 ∧
      (v smV).eval env = sm ∧
      (v bStV).eval env = sm.1 ∧
      (v xV).eval env = (u.val, (i.val, _root_.SignalPqxdh.LegacyCosted.bundleV bu)) := by
  simp only [gdhHandle2, wrapSim2, keyIndCodec, _root_.SignalPqxdh.LegacyCosted.keyIndQenc,
    smBase, letV_eval, bindV, caseSumV, Comp.eval, Expr.eval, v,
    map_eq_bind_pure_comp, Function.comp_def]
  exact ⟨_, _, _, _, _, _, _, _, _, inferInstance, inferInstance, inferInstance, inferInstance, _,
    rfl, rfl, rfl, rfl, rfl⟩

private theorem sessWrap_gdhHandle2_eval_initiateNoOPK (S : Setup) (K : Nat)
    (pa2 : params2Ty.denote) (sm : simTy.denote)
    (u : Fin S.N_id) (i : Fin S.N_send_no_opk) (bu : _root_.SignalPqxdh.PreKeyBundleInput) :
    ∃ (Γ₁ Γ₂ Γ₃ Γ₄ Δ : List PT)
      (paV : Var Γ₁ params2Ty) (smV : Var Γ₂ simTy) (bStV : Var Γ₃ keyIndStateTy)
      (xV : Var Γ₄ initQTy)
      (_ : Ext Γ₁ Δ) (_ : Ext Γ₂ Δ) (_ : Ext Γ₃ Δ) (_ : Ext Γ₄ Δ)
      (env : Env Δ),
      (gdhHandle2 S K).eval
          (.cons (pa2, sm) (.cons ((keyIndCodec S).qenc (.initiateNoOPK u i bu)) .nil)) =
        (fun r => (r.1, (pa2, r.2))) <$>
          (initiateGdh2B S K paV smV bStV false xV).eval env ∧
      (v paV).eval env = pa2 ∧
      (v smV).eval env = sm ∧
      (v bStV).eval env = sm.1 ∧
      (v xV).eval env = (u.val, (i.val, _root_.SignalPqxdh.LegacyCosted.bundleV bu)) := by
  simp only [gdhHandle2, wrapSim2, keyIndCodec, _root_.SignalPqxdh.LegacyCosted.keyIndQenc,
    smBase, letV_eval, bindV, caseSumV, Comp.eval, Expr.eval, v,
    map_eq_bind_pure_comp, Function.comp_def]
  exact ⟨_, _, _, _, _, _, _, _, _, inferInstance, inferInstance, inferInstance, inferInstance, _,
    rfl, rfl, rfl, rfl, rfl⟩

private theorem sessWrap_gdhHandle2_eval_acceptOPK (S : Setup) (K : Nat)
    (pa2 : params2Ty.denote) (sm : simTy.denote)
    (k : Fin S.N_id) (j : Fin S.N_recv) (o : Fin S.N_opk) (hdr : _root_.SignalPqxdh.HandshakeHdr) :
    ∃ (Γ₁ Γ₂ Γ₃ Γ₄ Δ : List PT)
      (paV : Var Γ₁ params2Ty) (smV : Var Γ₂ simTy) (bStV : Var Γ₃ keyIndStateTy)
      (xV : Var Γ₄ accQTy)
      (_ : Ext Γ₁ Δ) (_ : Ext Γ₂ Δ) (_ : Ext Γ₃ Δ) (_ : Ext Γ₄ Δ)
      (env : Env Δ),
      (gdhHandle2 S K).eval
          (.cons (pa2, sm) (.cons ((keyIndCodec S).qenc (.acceptOPK k j o hdr)) .nil)) =
        (fun r => (r.1, (pa2, r.2))) <$>
          (acceptOpkGdh2B S K paV smV bStV xV).eval env ∧
      (v paV).eval env = pa2 ∧
      (v smV).eval env = sm ∧
      (v bStV).eval env = sm.1 ∧
      (v xV).eval env = (k.val, (j.val, (o.val, _root_.SignalPqxdh.LegacyCosted.hdrV hdr))) := by
  simp only [gdhHandle2, wrapSim2, keyIndCodec, _root_.SignalPqxdh.LegacyCosted.keyIndQenc,
    smBase, letV_eval, bindV, caseSumV, Comp.eval, Expr.eval, v,
    map_eq_bind_pure_comp, Function.comp_def]
  exact ⟨_, _, _, _, _, _, _, _, _, inferInstance, inferInstance, inferInstance, inferInstance, _,
    rfl, rfl, rfl, rfl, rfl⟩

private theorem sessWrap_gdhHandle2_eval_acceptNoOPK (S : Setup) (K : Nat)
    (pa2 : params2Ty.denote) (sm : simTy.denote)
    (k : Fin S.N_id) (j : Fin S.N_recv) (l : Fin S.N_no_opk) (hdr : _root_.SignalPqxdh.HandshakeHdr) :
    ∃ (Γ₂ Γ₃ Γ₄ Δ : List PT)
      (smV : Var Γ₂ simTy) (bStV : Var Γ₃ keyIndStateTy)
      (xV : Var Γ₄ accQTy)
      (_ : Ext Γ₂ Δ) (_ : Ext Γ₃ Δ) (_ : Ext Γ₄ Δ)
      (env : Env Δ),
      (gdhHandle2 S K).eval
          (.cons (pa2, sm) (.cons ((keyIndCodec S).qenc (.acceptNoOPK k j l hdr)) .nil)) =
        (fun r => (r.1, (pa2, r.2))) <$>
          (acceptNoOpkGdhB S K smV bStV xV).eval env ∧
      (v smV).eval env = sm ∧
      (v bStV).eval env = sm.1 ∧
      (v xV).eval env = (k.val, (j.val, (l.val, _root_.SignalPqxdh.LegacyCosted.hdrV hdr))) := by
  simp only [gdhHandle2, wrapSim2, keyIndCodec, _root_.SignalPqxdh.LegacyCosted.keyIndQenc,
    smBase, letV_eval, bindV, caseSumV, Comp.eval, Expr.eval, v,
    map_eq_bind_pure_comp, Function.comp_def]
  exact ⟨_, _, _, _, _, _, _, inferInstance, inferInstance, inferInstance, _,
    rfl, rfl, rfl, rfl⟩

private theorem sessWrap_sig_init_bind_step (S : Setup) (b : QueryBudget)
    (c : Fin 3 → ℕ) (t : KeyIndQuery S) (hOn : keyIndQueryKind t = 0)
    (tp? : Option Nat) (sm : simTy.denote) (ord : Nat) (pk : Bytes) (sigB : Nat)
    (fgSc : fgSessCtrTy.denote) (sh : fgShadowAtomicTy.denote)
    (hSc : (sh.1, sh.2.1) = embedVal fgSessCtrTy fgSc)
    (hInv : Sig1KeyActiveSimInv S b c
      (embedVal sig1KeyActiveStTy (tp?, (sm, (ord, (pk, (sigB, none))))), sh))
    (mExtK mExtOld : OracleComp (_root_.SignalPqxdh.PrimBaseSpec + _root_.SignalPqxdh.LegacyCosted.sigAndDdhOracle.spec)
      (Ty.opt (.prod (B 1569) (B 64))).denote)
    (kBody : (Ty.opt (.prod (B 1569) (B 64))).denote →
      OracleComp (_root_.SignalPqxdh.PrimBaseSpec + _root_.SignalPqxdh.LegacyCosted.sigAndDdhOracle.spec)
        (keyIndRespTy.denote × (sig1KeyActiveStTy.denote × fgSessCtrTy.denote)))
    (oldBody : (Ty.opt (.prod (B 1569) (B 64))).denote →
      OracleComp (_root_.SignalPqxdh.PrimBaseSpec + _root_.SignalPqxdh.LegacyCosted.sigAndDdhOracle.spec) S1ARS.denote)
    (hExt : mExtK = mExtOld)
    (hSome : ∀ fgVal,
      kBody (some fgVal) =
        pure (((rNone : Expr pqxdhOps [] keyIndRespTy).eval .nil),
          ((tp?, (sm, (ord, (pk, (sigB, some fgVal))))), fgSc)) ∧
      oldBody (some fgVal) =
        pure (((rNone : Expr pqxdhOps [] keyIndRespTy).eval .nil),
          (tp?, (sm, (fixSent S b ord, (pk, (sigB, some fgVal)))))))
    (mK : OracleComp GdhSimSpec
      (keyIndRespTy.denote × (simTy.denote × fgSessCtrTy.denote)))
    (mOld : OracleComp GdhSimSpec (keyIndRespTy.denote × simTy.denote))
    (hNoneK : kBody none =
      (fun r => (r.1, ((tp?, (r.2.1, (ord, (pk, (sigB, none))))), r.2.2))) <$>
        liftGdhToSign mK)
    (hNoneOld : oldBody none =
      (fun p => (p.1, (tp?, (p.2, (fixSent S b ord, (pk, (sigB, none))))))) <$>
        liftGdhToSign mOld)
    (hEqM : (fun r => (r.1, r.2.1)) <$> mK = mOld)
    (hInvM : ∀ r ∈ support mK,
      GdhSimInv S b (bumpPred (keyIndSimPred S) c t)
        (embedVal simTy r.2.1,
          ((embedVal fgSessCtrTy r.2.2).1, ((embedVal fgSessCtrTy r.2.2).2, sh.2.2)))) :
    let outK : OracleComp _ ((pqKeyIndCodec S).R.denote × sig1KeyActiveKindStTy.denote) :=
      (fun r => (embedVal keyIndRespTy r.1,
        (embedVal sig1KeyActiveStTy r.2.1,
          ((embedVal fgSessCtrTy r.2.2).1, ((embedVal fgSessCtrTy r.2.2).2, sh.2.2))))) <$>
        (mExtK >>= kBody)
    Prod.map id (forgetSig1KeyActiveK S b) <$> outK =
      embedVal S1ARS <$> (mExtOld >>= oldBody) ∧
    ∀ y ∈ support outK, Sig1KeyActiveSimInv S b (bumpPred (keyIndSimPred S) c t) y.2 := by
  intro outK
  have hNone := sessWrap_sig_liftGdh_step S b (bumpPred (keyIndSimPred S) c t)
    tp? ord pk sigB sh mK mOld hEqM hInvM
  constructor
  · simp only [outK, hExt, Functor.map_map, map_bind]
    refine congrArg (mExtOld >>= ·) (funext fun fg => ?_)
    cases fg with
    | some fgVal =>
      rcases hSome fgVal with ⟨hK1, hO1⟩
      rw [hK1, hO1]
      simp only [map_pure, Prod.map_apply, ← hSc]
      rfl
    | none =>
      rw [hNoneK, hNoneOld]
      simpa only [Functor.map_map] using hNone.1
  · intro y hy
    simp only [outK, map_eq_bind_pure_comp, mem_support_bind_iff, mem_support_pure_iff,
      Function.comp_def] at hy
    rcases hy with ⟨r, ⟨fg, _, hr⟩, rfl⟩
    cases fg with
    | some fgVal =>
      rcases hSome fgVal with ⟨hK1, _⟩
      rw [hK1] at hr
      simp only [mem_support_pure_iff] at hr
      subst hr
      simp only [← hSc]
      exact sessWrap_GdhSimInv_bump_online_unchanged hInv hOn
    | none =>
      rw [hNoneK] at hr
      simp only [map_eq_bind_pure_comp, mem_support_bind_iff, mem_support_pure_iff,
        Function.comp_def] at hr
      rcases hr with ⟨r', hrLift, rfl⟩
      exact hInvM r' (gdhLift1Key_valid.mem_support_evalGdh hrLift)

/-- `.initiateOPK` step simulation for active 1-key `sigKeyInd1KeyKindAtomicProg`. -/
theorem sigKeyInd1KeyKindAtomicProg_hStep_initiateOPK (S : Setup) (b : QueryBudget) :
    ∀ u i bu, KeyIndStepSim S b (forgetSig1KeyActiveK S b) (Sig1KeyActiveSimInv S b)
      (sig1KeyKindHandleC S b) (sigKeyInd1KeyActiveAtomicProg S b).handle
      (.initiateOPK u i bu) := by
  intro u i bu c stK hB hRoom hInv
  let t : KeyIndQuery S := .initiateOPK u i bu
  let stL : sig1KeyActiveStTy.denote := projVal sig1KeyActiveStTy stK.1
  let sh : fgShadowAtomicTy.denote := stK.2
  let fgSc : fgSessCtrTy.denote := projVal fgSessCtrTy (sh.1, sh.2.1)
  have hStK : stK = (embedVal sig1KeyActiveStTy stL, sh) :=
    Prod.ext (embedVal_projVal sig1KeyActiveStTy stK.1).symm rfl
  have hSc : (sh.1, sh.2.1) = embedVal fgSessCtrTy fgSc :=
    (embedVal_projVal fgSessCtrTy (sh.1, sh.2.1)).symm
  rw [hStK] at hInv ⊢
  rw [sessWrap_forgetSig1KeyActiveK_embedVal, sessWrap_sigActiveAtomic_handle_eval]
  have hLhs :
      (sig1KeyKindHandleC S b).eval
        (.cons (embedVal sig1KeyActiveStTy stL, sh) (.cons ((pqKeyIndCodec S).qenc t) .nil)) =
      (fun r => (embedVal keyIndRespTy r.1,
        (embedVal sig1KeyActiveStTy r.2.1,
          ((embedVal fgSessCtrTy r.2.2).1, ((embedVal fgSessCtrTy r.2.2).2, sh.2.2))))) <$>
        (sigKindInitiateSessLeg S (keyIndKFuelsOfBudget S b) true).eval
          (.cons (stL, fgSc)
            (.cons (u.val, (i.val, _root_.SignalPqxdh.LegacyCosted.bundleV bu)) .nil)) := by
    unfold sig1KeyKindHandleC
    dsimp only
    rw [dispatchKeyIndQ_eval]
    exact sessWrap_liftSigDdhSessArm_eval S _ _
      (sessWrap_sigKindInitiateSessLeg_unsupported S _ true) _ stL fgSc sh hSc _ _
      (sessWrap_initPay_eval S u i bu _ _)
  rw [hLhs]
  rcases stL with ⟨tp?, sm, ord, pk, sigB, fg?⟩
  cases fg? with
  | some fgVal =>
    have hLegK :
        (sigKindInitiateSessLeg S (keyIndKFuelsOfBudget S b) true).eval
          (.cons ((tp?, sm, ord, pk, sigB, some fgVal), fgSc)
            (.cons (u.val, (i.val, _root_.SignalPqxdh.LegacyCosted.bundleV bu)) .nil)) =
        pure (((rNone : Expr pqxdhOps [] keyIndRespTy).eval .nil),
          ((tp?, sm, ord, pk, sigB, some fgVal), fgSc)) := by
      simp [sigKindInitiateSessLeg, saInner, s1Forgery, isSomeE, rNone,
        letV_eval, Comp.eval, Expr.eval, v]
    have hLegOld :
        (sig1KeyActiveHandleC S b.q_total).eval
          (.cons (sessWrap_fixSigLeg S b (tp?, sm, ord, pk, sigB, some fgVal))
            (.cons ((keyIndCodec S).qenc t) .nil)) =
        pure (((rNone : Expr pqxdhOps [] keyIndRespTy).eval .nil),
          sessWrap_fixSigLeg S b (tp?, sm, ord, pk, sigB, some fgVal)) := by
      simp [sig1KeyActiveHandleC, sig1KeyActivePreDispatchC, sessWrap_fixSigLeg,
        saInner, s1Forgery, isSomeE, rNone, bindV, caseSumV, Comp.eval, Expr.eval, v]
    rw [hLegK, hLegOld]
    simp only [map_pure, Prod.map_apply, ← hSc]
    refine ⟨rfl, ?_⟩
    intro y hy
    simp only [support_pure, Set.mem_singleton_iff] at hy
    subst hy
    exact sessWrap_GdhSimInv_bump_online_unchanged hInv rfl
  | none =>
    let pa2 : params2Ty.denote :=
      ([], (pk, ([], (none, (false, (none, (none, (false, (none, 1)))))))))
    have hOnline : BaseOnlineLenInv c sm.1 :=
      congrArg Prod.fst (projVal_embedVal simTy sm) ▸ hInv.online_len
    have hKBind :
        ∃ (Γs₁ Γb₁ Δe₁ : List PT)
          (st₁ : Var Γs₁ sig1KeyActiveStTy) (bu₁ : Var Γb₁ preKeyBundleTy)
          (_ : Ext Γs₁ Δe₁) (_ : Ext Γb₁ Δe₁) (envE₁ : Env Δe₁)
          (kBody : (Ty.opt (.prod (B 1569) (B 64))).denote →
            OracleComp (_root_.SignalPqxdh.PrimBaseSpec + _root_.SignalPqxdh.LegacyCosted.sigAndDdhOracle.spec)
              (keyIndRespTy.denote × (sig1KeyActiveStTy.denote × fgSessCtrTy.denote)))
          (Γ₁a Γ₂a Γ₃a Γ₄a Γ₅a Δ₁ : List PT)
          (pa₁ : Var Γ₁a params2Ty) (sm₁ : Var Γ₂a simTy) (bSt₁ : Var Γ₃a keyIndStateTy)
          (fgSh₁ : Var Γ₅a fgSessCtrTy) (x₁ : Var Γ₄a initQTy)
          (_ : Ext Γ₁a Δ₁) (_ : Ext Γ₂a Δ₁) (_ : Ext Γ₃a Δ₁) (_ : Ext Γ₄a Δ₁) (_ : Ext Γ₅a Δ₁)
          (env₁ : Env Δ₁),
          (sigKindInitiateSessLeg S (keyIndKFuelsOfBudget S b) true).eval
            (.cons ((tp?, (sm, (ord, (pk, (sigB, none))))), fgSc)
              (.cons (u.val, (i.val, _root_.SignalPqxdh.LegacyCosted.bundleV bu)) .nil)) =
            ((extract1KeyActiveC S (keyIndKFuelsOfBudget S b).kOn st₁ bu₁).eval envE₁ >>= kBody) ∧
          (v st₁).eval envE₁ = (tp?, (sm, (ord, (pk, (sigB, none))))) ∧
          (v bu₁).eval envE₁ = _root_.SignalPqxdh.LegacyCosted.bundleV bu ∧
          (∀ fgVal, kBody (some fgVal) =
            pure (((rNone : Expr pqxdhOps [] keyIndRespTy).eval .nil),
              ((tp?, (sm, (ord, (pk, (sigB, some fgVal))))), fgSc))) ∧
          kBody none =
            (fun r : keyIndRespTy.denote × (simTy.denote × fgSessCtrTy.denote) =>
              (r.1, (((tp?, (r.2.1, (ord, (pk, (sigB, none))))) : sig1KeyActiveStTy.denote), r.2.2))) <$>
              liftGdhToSign
                ((initiateGdh2ShadowB S (keyIndKFuelsOfBudget S b)
                  pa₁ sm₁ bSt₁ fgSh₁ true x₁).eval env₁) ∧
          (v pa₁).eval env₁ = pa2 ∧
          (v sm₁).eval env₁ = sm ∧
          (v bSt₁).eval env₁ = sm.1 ∧
          (v fgSh₁).eval env₁ = fgSc ∧
          (v x₁).eval env₁ = (u.val, (i.val, _root_.SignalPqxdh.LegacyCosted.bundleV bu)) := by
      simp only [sigKindInitiateSessLeg, saInner, saTP, s1Forgery, s1Pk, s1Fg, s1Upd,
        pa2Mk, smBase, litB, isSomeE, liftGdhToSigDdh_eval,
        letV_eval, bindV, Comp.eval, Expr.eval, v]
      refine ⟨_, _, _, _, _, inferInstance, inferInstance, _, _,
        _, _, _, _, _, _, _, _, _, _, _,
        inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, _,
        rfl, rfl, rfl, fun fgVal => rfl,
        by simp only [map_eq_bind_pure_comp, Function.comp_def]; rfl,
        rfl, rfl, rfl, rfl, rfl⟩
    obtain ⟨Γs₁, Γb₁, Δe₁, st₁, bu₁, _, _, envE₁, kBody,
      Γ₁a, Γ₂a, Γ₃a, Γ₄a, Γ₅a, Δ₁, pa₁, sm₁, bSt₁, fgSh₁, x₁,
      _, _, _, _, _, env₁, hK, hst₁, hbu₁, hKSome, hKNone,
      hpa₁, hsm₁, hbSt₁, hfg₁, hx₁⟩ := hKBind
    obtain ⟨Γ₁b, Γ₂b, Γ₃b, Γ₄b, Δ₂, pa₂, sm₂, bSt₂, x₂,
      _, _, _, _, env₂, hGdh2, hpa₂, hsm₂, hbSt₂, hx₂⟩ :=
      sessWrap_gdhHandle2_eval_initiateOPK S b.q_total pa2 sm u i bu
    have hOBind :
        ∃ (Γs₂ Γb₂ Δe₂ : List PT)
          (st₂ : Var Γs₂ sig1KeyActiveStTy) (bu₂ : Var Γb₂ preKeyBundleTy)
          (_ : Ext Γs₂ Δe₂) (_ : Ext Γb₂ Δe₂) (envE₂ : Env Δe₂)
          (oldBody : (Ty.opt (.prod (B 1569) (B 64))).denote →
            OracleComp (_root_.SignalPqxdh.PrimBaseSpec + _root_.SignalPqxdh.LegacyCosted.sigAndDdhOracle.spec) S1ARS.denote),
          (sig1KeyActiveHandleC S b.q_total).eval
            (.cons (sessWrap_fixSigLeg S b (tp?, (sm, (ord, (pk, (sigB, none))))))
              (.cons ((keyIndCodec S).qenc t) .nil)) =
            ((extract1KeyActiveC S b.q_total st₂ bu₂).eval envE₂ >>= oldBody) ∧
          (v st₂).eval envE₂ = (tp?, (sm, (fixSent S b ord, (pk, (sigB, none))))) ∧
          (v bu₂).eval envE₂ = _root_.SignalPqxdh.LegacyCosted.bundleV bu ∧
          (∀ fgVal, oldBody (some fgVal) =
            pure (((rNone : Expr pqxdhOps [] keyIndRespTy).eval .nil),
              (tp?, (sm, (fixSent S b ord, (pk, (sigB, some fgVal))))))) ∧
          oldBody none =
            (fun p : keyIndRespTy.denote × simTy.denote =>
              (p.1, ((tp?, (p.2, (fixSent S b ord, (pk, (sigB, none))))) : sig1KeyActiveStTy.denote))) <$>
              liftGdhToSign
                ((initiateGdh2B S b.q_total pa₂ sm₂ bSt₂ true x₂).eval env₂) := by
      have hPre :
          ∃ (Γs₂ Γb₂ Δe₂ : List PT)
            (st₂ : Var Γs₂ sig1KeyActiveStTy) (bu₂ : Var Γb₂ preKeyBundleTy)
            (_ : Ext Γs₂ Δe₂) (_ : Ext Γb₂ Δe₂) (envE₂ : Env Δe₂)
            (preK : (Ty.opt (.prod (B 1569) (B 64))).denote →
              OracleComp (_root_.SignalPqxdh.PrimBaseSpec + _root_.SignalPqxdh.LegacyCosted.sigAndDdhOracle.spec)
                (S1ARS.denote ⊕ Unit)),
            (sig1KeyActivePreDispatchC S b.q_total
              (.zero : Var [sig1KeyActiveStTy, keyIndQueryTy] sig1KeyActiveStTy)
              (.succ .zero : Var [sig1KeyActiveStTy, keyIndQueryTy] keyIndQueryTy)).eval
              (.cons (t := sig1KeyActiveStTy)
                (sessWrap_fixSigLeg S b (tp?, (sm, (ord, (pk, (sigB, none))))))
                (.cons (t := keyIndQueryTy) ((keyIndCodec S).qenc t) .nil)) =
              ((extract1KeyActiveC S b.q_total st₂ bu₂).eval envE₂ >>= preK) ∧
            (v st₂).eval envE₂ = (tp?, (sm, (fixSent S b ord, (pk, (sigB, none))))) ∧
            (v bu₂).eval envE₂ = _root_.SignalPqxdh.LegacyCosted.bundleV bu ∧
            (∀ fgVal, preK (some fgVal) =
              pure (Sum.inl (((rNone : Expr pqxdhOps [] keyIndRespTy).eval .nil),
                (tp?, (sm, (fixSent S b ord, (pk, (sigB, some fgVal)))))))) ∧
            preK none = pure (Sum.inr ()) := by
        simp only [sig1KeyActivePreDispatchC, sig1KeyActiveInitiateCheckC,
          sessWrap_fixSigLeg, t, keyIndCodec, _root_.SignalPqxdh.LegacyCosted.keyIndQenc,
          saInner, saTP, s1Forgery, s1Upd, isSomeE, letV_eval, bindV, caseSumV,
          Comp.eval, Expr.eval, v, Ext.wk, Env.get]
        exact ⟨_, _, _, _, _, inferInstance, inferInstance, _, _,
          rfl, rfl, rfl, fun _ => rfl, rfl⟩
      obtain ⟨Γs₂, Γb₂, Δe₂, st₂, bu₂, _, _, envE₂, preK,
        hPreEq, hst₂, hbu₂, hPreSome, hPreNone⟩ := hPre
      simp only [sig1KeyActiveHandleC, bindV, Comp.eval]
      erw [hPreEq, bind_assoc]
      refine ⟨Γs₂, Γb₂, Δe₂, st₂, bu₂, inferInstance, inferInstance, envE₂, _,
        rfl, hst₂, hbu₂, fun fgVal => ?_, ?_⟩
      · erw [hPreSome fgVal, pure_bind]
        simp only [caseSumV, Comp.eval, Expr.eval, v, Ext.wk, Env.get]
      · erw [hPreNone, pure_bind]
        simp only [caseSumV, letV_eval, Comp.rename_eval,
          _root_.ReductionDsl.Env.ofRename, renamePair, saInner, saTP, s1Pk, s1Fg, s1Upd,
          pa2Mk, litB, sessWrap_fixSigLeg,
          liftGdhToSigDdh_eval, Expr.eval, v, Ext.wk, Env.get, Comp.eval]
        change (do
            let r ← liftGdhToSign
              ((gdhHandle2 S b.q_total).eval (.cons (pa2, sm) (.cons ((keyIndCodec S).qenc t) .nil)))
            pure (r.1, (tp?, (r.2.2, (fixSent S b ord, (pk, (sigB, none))))))) = _
        rw [hGdh2, gdhLift1Key_valid.evalGdh_map]
        simp only [map_eq_bind_pure_comp, bind_assoc, pure_bind, Function.comp_def]
    obtain ⟨Γs₂, Γb₂, Δe₂, st₂, bu₂, _, _, envE₂, oldBody,
      hO, hst₂, hbu₂, hOSome, hONone⟩ := hOBind
    rw [hK, hO]
    have hExt :
        (extract1KeyActiveC S (keyIndKFuelsOfBudget S b).kOn st₁ bu₁).eval envE₁ =
        (extract1KeyActiveC S b.q_total st₂ bu₂).eval envE₂ :=
      extract1KeyActiveC_sim S st₁ bu₁ st₂ bu₂ envE₁ envE₂
        (by rw [hst₁, hst₂])
        (by rw [hst₁, hst₂])
        (by rw [hst₁, hst₂])
        (by rw [hst₁, hst₂])
        (hbu₁.trans hbu₂.symm)
        (by rw [hst₁]; exact hOnline)
        (hB 0)
        (Nat.min_le_right b.q_on b.q_total)
    have hInvSm :
        GdhSimInv S b c
          (embedVal simTy ((v sm₁).eval env₁),
            ((embedVal fgSessCtrTy ((v fgSh₁).eval env₁)).1,
              ((embedVal fgSessCtrTy ((v fgSh₁).eval env₁)).2, sh.2.2))) := by
      rw [hsm₁, hfg₁, ← hSc]; exact hInv
    have ⟨hEqM, hInvM⟩ :=
      initiateGdh2ShadowB_sim S b true pa₁ sm₁ bSt₁ fgSh₁ x₁ pa₂ sm₂ bSt₂ x₂ env₁ env₂
        c t sh (hpa₁.trans hpa₂.symm) (hsm₁.trans hsm₂.symm)
        (hbSt₁.trans (congrArg Prod.fst hsm₁.symm))
        (hbSt₂.trans (congrArg Prod.fst hsm₂.symm))
        (hx₁.trans hx₂.symm) (sessWrap_simPred_0 rfl) (sessWrap_simPred_1 rfl) hB hRoom hInvSm
    exact sessWrap_sig_init_bind_step S b c t rfl tp? sm ord pk sigB fgSc sh hSc hInv
      _ _ kBody oldBody hExt (fun fgVal => ⟨hKSome fgVal, hOSome fgVal⟩)
      _ _ hKNone hONone hEqM hInvM

/-- `.initiateNoOPK` step simulation for active 1-key `sigKeyInd1KeyKindAtomicProg`. -/
theorem sigKeyInd1KeyKindAtomicProg_hStep_initiateNoOPK (S : Setup) (b : QueryBudget) :
    ∀ u i bu, KeyIndStepSim S b (forgetSig1KeyActiveK S b) (Sig1KeyActiveSimInv S b)
      (sig1KeyKindHandleC S b) (sigKeyInd1KeyActiveAtomicProg S b).handle
      (.initiateNoOPK u i bu) := by
  intro u i bu c stK hB hRoom hInv
  let t : KeyIndQuery S := .initiateNoOPK u i bu
  let stL : sig1KeyActiveStTy.denote := projVal sig1KeyActiveStTy stK.1
  let sh : fgShadowAtomicTy.denote := stK.2
  let fgSc : fgSessCtrTy.denote := projVal fgSessCtrTy (sh.1, sh.2.1)
  have hStK : stK = (embedVal sig1KeyActiveStTy stL, sh) :=
    Prod.ext (embedVal_projVal sig1KeyActiveStTy stK.1).symm rfl
  have hSc : (sh.1, sh.2.1) = embedVal fgSessCtrTy fgSc :=
    (embedVal_projVal fgSessCtrTy (sh.1, sh.2.1)).symm
  rw [hStK] at hInv ⊢
  rw [sessWrap_forgetSig1KeyActiveK_embedVal, sessWrap_sigActiveAtomic_handle_eval]
  have hLhs :
      (sig1KeyKindHandleC S b).eval
        (.cons (embedVal sig1KeyActiveStTy stL, sh) (.cons ((pqKeyIndCodec S).qenc t) .nil)) =
      (fun r => (embedVal keyIndRespTy r.1,
        (embedVal sig1KeyActiveStTy r.2.1,
          ((embedVal fgSessCtrTy r.2.2).1, ((embedVal fgSessCtrTy r.2.2).2, sh.2.2))))) <$>
        (sigKindInitiateSessLeg S (keyIndKFuelsOfBudget S b) false).eval
          (.cons (stL, fgSc)
            (.cons (u.val, (i.val, _root_.SignalPqxdh.LegacyCosted.bundleV bu)) .nil)) := by
    unfold sig1KeyKindHandleC
    dsimp only
    rw [dispatchKeyIndQ_eval]
    exact sessWrap_liftSigDdhSessArm_eval S _ _
      (sessWrap_sigKindInitiateSessLeg_unsupported S _ false) _ stL fgSc sh hSc _ _
      (sessWrap_initPay_eval S u i bu _ _)
  rw [hLhs]
  rcases stL with ⟨tp?, sm, ord, pk, sigB, fg?⟩
  cases fg? with
  | some fgVal =>
    have hLegK :
        (sigKindInitiateSessLeg S (keyIndKFuelsOfBudget S b) false).eval
          (.cons ((tp?, sm, ord, pk, sigB, some fgVal), fgSc)
            (.cons (u.val, (i.val, _root_.SignalPqxdh.LegacyCosted.bundleV bu)) .nil)) =
        pure (((rNone : Expr pqxdhOps [] keyIndRespTy).eval .nil),
          ((tp?, sm, ord, pk, sigB, some fgVal), fgSc)) := by
      simp [sigKindInitiateSessLeg, saInner, s1Forgery, isSomeE, rNone,
        letV_eval, Comp.eval, Expr.eval, v]
    have hLegOld :
        (sig1KeyActiveHandleC S b.q_total).eval
          (.cons (sessWrap_fixSigLeg S b (tp?, sm, ord, pk, sigB, some fgVal))
            (.cons ((keyIndCodec S).qenc t) .nil)) =
        pure (((rNone : Expr pqxdhOps [] keyIndRespTy).eval .nil),
          sessWrap_fixSigLeg S b (tp?, sm, ord, pk, sigB, some fgVal)) := by
      simp [sig1KeyActiveHandleC, sig1KeyActivePreDispatchC, sessWrap_fixSigLeg,
        saInner, s1Forgery, isSomeE, rNone, bindV, caseSumV, Comp.eval, Expr.eval, v]
    rw [hLegK, hLegOld]
    simp only [map_pure, Prod.map_apply, ← hSc]
    refine ⟨rfl, ?_⟩
    intro y hy
    simp only [support_pure, Set.mem_singleton_iff] at hy
    subst hy
    exact sessWrap_GdhSimInv_bump_online_unchanged hInv rfl
  | none =>
    let pa2 : params2Ty.denote :=
      ([], (pk, ([], (none, (false, (none, (none, (false, (none, 1)))))))))
    have hOnline : BaseOnlineLenInv c sm.1 :=
      congrArg Prod.fst (projVal_embedVal simTy sm) ▸ hInv.online_len
    have hKBind :
        ∃ (Γs₁ Γb₁ Δe₁ : List PT)
          (st₁ : Var Γs₁ sig1KeyActiveStTy) (bu₁ : Var Γb₁ preKeyBundleTy)
          (_ : Ext Γs₁ Δe₁) (_ : Ext Γb₁ Δe₁) (envE₁ : Env Δe₁)
          (kBody : (Ty.opt (.prod (B 1569) (B 64))).denote →
            OracleComp (_root_.SignalPqxdh.PrimBaseSpec + _root_.SignalPqxdh.LegacyCosted.sigAndDdhOracle.spec)
              (keyIndRespTy.denote × (sig1KeyActiveStTy.denote × fgSessCtrTy.denote)))
          (Γ₁a Γ₂a Γ₃a Γ₄a Γ₅a Δ₁ : List PT)
          (pa₁ : Var Γ₁a params2Ty) (sm₁ : Var Γ₂a simTy) (bSt₁ : Var Γ₃a keyIndStateTy)
          (fgSh₁ : Var Γ₅a fgSessCtrTy) (x₁ : Var Γ₄a initQTy)
          (_ : Ext Γ₁a Δ₁) (_ : Ext Γ₂a Δ₁) (_ : Ext Γ₃a Δ₁) (_ : Ext Γ₄a Δ₁) (_ : Ext Γ₅a Δ₁)
          (env₁ : Env Δ₁),
          (sigKindInitiateSessLeg S (keyIndKFuelsOfBudget S b) false).eval
            (.cons ((tp?, (sm, (ord, (pk, (sigB, none))))), fgSc)
              (.cons (u.val, (i.val, _root_.SignalPqxdh.LegacyCosted.bundleV bu)) .nil)) =
            ((extract1KeyActiveC S (keyIndKFuelsOfBudget S b).kOn st₁ bu₁).eval envE₁ >>= kBody) ∧
          (v st₁).eval envE₁ = (tp?, (sm, (ord, (pk, (sigB, none))))) ∧
          (v bu₁).eval envE₁ = _root_.SignalPqxdh.LegacyCosted.bundleV bu ∧
          (∀ fgVal, kBody (some fgVal) =
            pure (((rNone : Expr pqxdhOps [] keyIndRespTy).eval .nil),
              ((tp?, (sm, (ord, (pk, (sigB, some fgVal))))), fgSc))) ∧
          kBody none =
            (fun r : keyIndRespTy.denote × (simTy.denote × fgSessCtrTy.denote) =>
              (r.1, (((tp?, (r.2.1, (ord, (pk, (sigB, none))))) : sig1KeyActiveStTy.denote), r.2.2))) <$>
              liftGdhToSign
                ((initiateGdh2ShadowB S (keyIndKFuelsOfBudget S b)
                  pa₁ sm₁ bSt₁ fgSh₁ false x₁).eval env₁) ∧
          (v pa₁).eval env₁ = pa2 ∧
          (v sm₁).eval env₁ = sm ∧
          (v bSt₁).eval env₁ = sm.1 ∧
          (v fgSh₁).eval env₁ = fgSc ∧
          (v x₁).eval env₁ = (u.val, (i.val, _root_.SignalPqxdh.LegacyCosted.bundleV bu)) := by
      simp only [sigKindInitiateSessLeg, saInner, saTP, s1Forgery, s1Pk, s1Fg, s1Upd,
        pa2Mk, smBase, litB, isSomeE, liftGdhToSigDdh_eval,
        letV_eval, bindV, Comp.eval, Expr.eval, v]
      refine ⟨_, _, _, _, _, inferInstance, inferInstance, _, _,
        _, _, _, _, _, _, _, _, _, _, _,
        inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, _,
        rfl, rfl, rfl, fun fgVal => rfl,
        by simp only [map_eq_bind_pure_comp, Function.comp_def]; rfl,
        rfl, rfl, rfl, rfl, rfl⟩
    obtain ⟨Γs₁, Γb₁, Δe₁, st₁, bu₁, _, _, envE₁, kBody,
      Γ₁a, Γ₂a, Γ₃a, Γ₄a, Γ₅a, Δ₁, pa₁, sm₁, bSt₁, fgSh₁, x₁,
      _, _, _, _, _, env₁, hK, hst₁, hbu₁, hKSome, hKNone,
      hpa₁, hsm₁, hbSt₁, hfg₁, hx₁⟩ := hKBind
    obtain ⟨Γ₁b, Γ₂b, Γ₃b, Γ₄b, Δ₂, pa₂, sm₂, bSt₂, x₂,
      _, _, _, _, env₂, hGdh2, hpa₂, hsm₂, hbSt₂, hx₂⟩ :=
      sessWrap_gdhHandle2_eval_initiateNoOPK S b.q_total pa2 sm u i bu
    have hOBind :
        ∃ (Γs₂ Γb₂ Δe₂ : List PT)
          (st₂ : Var Γs₂ sig1KeyActiveStTy) (bu₂ : Var Γb₂ preKeyBundleTy)
          (_ : Ext Γs₂ Δe₂) (_ : Ext Γb₂ Δe₂) (envE₂ : Env Δe₂)
          (oldBody : (Ty.opt (.prod (B 1569) (B 64))).denote →
            OracleComp (_root_.SignalPqxdh.PrimBaseSpec + _root_.SignalPqxdh.LegacyCosted.sigAndDdhOracle.spec) S1ARS.denote),
          (sig1KeyActiveHandleC S b.q_total).eval
            (.cons (sessWrap_fixSigLeg S b (tp?, (sm, (ord, (pk, (sigB, none))))))
              (.cons ((keyIndCodec S).qenc t) .nil)) =
            ((extract1KeyActiveC S b.q_total st₂ bu₂).eval envE₂ >>= oldBody) ∧
          (v st₂).eval envE₂ = (tp?, (sm, (fixSent S b ord, (pk, (sigB, none))))) ∧
          (v bu₂).eval envE₂ = _root_.SignalPqxdh.LegacyCosted.bundleV bu ∧
          (∀ fgVal, oldBody (some fgVal) =
            pure (((rNone : Expr pqxdhOps [] keyIndRespTy).eval .nil),
              (tp?, (sm, (fixSent S b ord, (pk, (sigB, some fgVal))))))) ∧
          oldBody none =
            (fun p : keyIndRespTy.denote × simTy.denote =>
              (p.1, ((tp?, (p.2, (fixSent S b ord, (pk, (sigB, none))))) : sig1KeyActiveStTy.denote))) <$>
              liftGdhToSign
                ((initiateGdh2B S b.q_total pa₂ sm₂ bSt₂ false x₂).eval env₂) := by
      have hPre :
          ∃ (Γs₂ Γb₂ Δe₂ : List PT)
            (st₂ : Var Γs₂ sig1KeyActiveStTy) (bu₂ : Var Γb₂ preKeyBundleTy)
            (_ : Ext Γs₂ Δe₂) (_ : Ext Γb₂ Δe₂) (envE₂ : Env Δe₂)
            (preK : (Ty.opt (.prod (B 1569) (B 64))).denote →
              OracleComp (_root_.SignalPqxdh.PrimBaseSpec + _root_.SignalPqxdh.LegacyCosted.sigAndDdhOracle.spec)
                (S1ARS.denote ⊕ Unit)),
            (sig1KeyActivePreDispatchC S b.q_total
              (.zero : Var [sig1KeyActiveStTy, keyIndQueryTy] sig1KeyActiveStTy)
              (.succ .zero : Var [sig1KeyActiveStTy, keyIndQueryTy] keyIndQueryTy)).eval
              (.cons (t := sig1KeyActiveStTy)
                (sessWrap_fixSigLeg S b (tp?, (sm, (ord, (pk, (sigB, none))))))
                (.cons (t := keyIndQueryTy) ((keyIndCodec S).qenc t) .nil)) =
              ((extract1KeyActiveC S b.q_total st₂ bu₂).eval envE₂ >>= preK) ∧
            (v st₂).eval envE₂ = (tp?, (sm, (fixSent S b ord, (pk, (sigB, none))))) ∧
            (v bu₂).eval envE₂ = _root_.SignalPqxdh.LegacyCosted.bundleV bu ∧
            (∀ fgVal, preK (some fgVal) =
              pure (Sum.inl (((rNone : Expr pqxdhOps [] keyIndRespTy).eval .nil),
                (tp?, (sm, (fixSent S b ord, (pk, (sigB, some fgVal)))))))) ∧
            preK none = pure (Sum.inr ()) := by
        simp only [sig1KeyActivePreDispatchC, sig1KeyActiveInitiateCheckC,
          sessWrap_fixSigLeg, t, keyIndCodec, _root_.SignalPqxdh.LegacyCosted.keyIndQenc,
          saInner, saTP, s1Forgery, s1Upd, isSomeE, letV_eval, bindV, caseSumV,
          Comp.eval, Expr.eval, v, Ext.wk, Env.get]
        exact ⟨_, _, _, _, _, inferInstance, inferInstance, _, _,
          rfl, rfl, rfl, fun _ => rfl, rfl⟩
      obtain ⟨Γs₂, Γb₂, Δe₂, st₂, bu₂, _, _, envE₂, preK,
        hPreEq, hst₂, hbu₂, hPreSome, hPreNone⟩ := hPre
      simp only [sig1KeyActiveHandleC, bindV, Comp.eval]
      erw [hPreEq, bind_assoc]
      refine ⟨Γs₂, Γb₂, Δe₂, st₂, bu₂, inferInstance, inferInstance, envE₂, _,
        rfl, hst₂, hbu₂, fun fgVal => ?_, ?_⟩
      · erw [hPreSome fgVal, pure_bind]
        simp only [caseSumV, Comp.eval, Expr.eval, v, Ext.wk, Env.get]
      · erw [hPreNone, pure_bind]
        simp only [caseSumV, letV_eval, Comp.rename_eval,
          _root_.ReductionDsl.Env.ofRename, renamePair, saInner, saTP, s1Pk, s1Fg, s1Upd,
          pa2Mk, litB, sessWrap_fixSigLeg,
          liftGdhToSigDdh_eval, Expr.eval, v, Ext.wk, Env.get, Comp.eval]
        change (do
            let r ← liftGdhToSign
              ((gdhHandle2 S b.q_total).eval (.cons (pa2, sm) (.cons ((keyIndCodec S).qenc t) .nil)))
            pure (r.1, (tp?, (r.2.2, (fixSent S b ord, (pk, (sigB, none))))))) = _
        rw [hGdh2, gdhLift1Key_valid.evalGdh_map]
        simp only [map_eq_bind_pure_comp, bind_assoc, pure_bind, Function.comp_def]
    obtain ⟨Γs₂, Γb₂, Δe₂, st₂, bu₂, _, _, envE₂, oldBody,
      hO, hst₂, hbu₂, hOSome, hONone⟩ := hOBind
    rw [hK, hO]
    have hExt :
        (extract1KeyActiveC S (keyIndKFuelsOfBudget S b).kOn st₁ bu₁).eval envE₁ =
        (extract1KeyActiveC S b.q_total st₂ bu₂).eval envE₂ :=
      extract1KeyActiveC_sim S st₁ bu₁ st₂ bu₂ envE₁ envE₂
        (by rw [hst₁, hst₂])
        (by rw [hst₁, hst₂])
        (by rw [hst₁, hst₂])
        (by rw [hst₁, hst₂])
        (hbu₁.trans hbu₂.symm)
        (by rw [hst₁]; exact hOnline)
        (hB 0)
        (Nat.min_le_right b.q_on b.q_total)
    have hInvSm :
        GdhSimInv S b c
          (embedVal simTy ((v sm₁).eval env₁),
            ((embedVal fgSessCtrTy ((v fgSh₁).eval env₁)).1,
              ((embedVal fgSessCtrTy ((v fgSh₁).eval env₁)).2, sh.2.2))) := by
      rw [hsm₁, hfg₁, ← hSc]; exact hInv
    have ⟨hEqM, hInvM⟩ :=
      initiateGdh2ShadowB_sim S b false pa₁ sm₁ bSt₁ fgSh₁ x₁ pa₂ sm₂ bSt₂ x₂ env₁ env₂
        c t sh (hpa₁.trans hpa₂.symm) (hsm₁.trans hsm₂.symm)
        (hbSt₁.trans (congrArg Prod.fst hsm₁.symm))
        (hbSt₂.trans (congrArg Prod.fst hsm₂.symm))
        (hx₁.trans hx₂.symm) (sessWrap_simPred_0 rfl) (sessWrap_simPred_1 rfl) hB hRoom hInvSm
    exact sessWrap_sig_init_bind_step S b c t rfl tp? sm ord pk sigB fgSc sh hSc hInv
      _ _ kBody oldBody hExt (fun fgVal => ⟨hKSome fgVal, hOSome fgVal⟩)
      _ _ hKNone hONone hEqM hInvM

/-- `.acceptOPK` step simulation for active 1-key `sigKeyInd1KeyKindAtomicProg`. -/
theorem sigKeyInd1KeyKindAtomicProg_hStep_acceptOPK (S : Setup) (b : QueryBudget) :
    ∀ k j o hdr, KeyIndStepSim S b (forgetSig1KeyActiveK S b) (Sig1KeyActiveSimInv S b)
      (sig1KeyKindHandleC S b) (sigKeyInd1KeyActiveAtomicProg S b).handle
      (.acceptOPK k j o hdr) := by
  intro k j o hdr c stK hB hRoom hInv
  let t : KeyIndQuery S := .acceptOPK k j o hdr
  let stL : sig1KeyActiveStTy.denote := projVal sig1KeyActiveStTy stK.1
  let sh : fgShadowAtomicTy.denote := stK.2
  let fgSc : fgSessCtrTy.denote := projVal fgSessCtrTy (sh.1, sh.2.1)
  have hStK : stK = (embedVal sig1KeyActiveStTy stL, sh) :=
    Prod.ext (embedVal_projVal sig1KeyActiveStTy stK.1).symm rfl
  have hSc : (sh.1, sh.2.1) = embedVal fgSessCtrTy fgSc :=
    (embedVal_projVal fgSessCtrTy (sh.1, sh.2.1)).symm
  rw [hStK] at hInv ⊢
  rw [sessWrap_forgetSig1KeyActiveK_embedVal, sessWrap_sigActiveAtomic_handle_eval]
  have hLhs :
      (sig1KeyKindHandleC S b).eval
        (.cons (embedVal sig1KeyActiveStTy stL, sh) (.cons ((pqKeyIndCodec S).qenc t) .nil)) =
      (fun r => (embedVal keyIndRespTy r.1,
        (embedVal sig1KeyActiveStTy r.2.1,
          ((embedVal fgSessCtrTy r.2.2).1, ((embedVal fgSessCtrTy r.2.2).2, sh.2.2))))) <$>
        (sigKindAcceptOpkSessLeg S (keyIndKFuelsOfBudget S b)).eval
          (.cons (stL, fgSc)
            (.cons (k.val, (j.val, (o.val, _root_.SignalPqxdh.LegacyCosted.hdrV hdr))) .nil)) := by
    unfold sig1KeyKindHandleC
    dsimp only
    rw [dispatchKeyIndQ_eval]
    exact sessWrap_liftSigDdhSessArm_eval S _ _
      (sessWrap_sigKindAcceptOpkSessLeg_unsupported S _) _ stL fgSc sh hSc _ _
      (sessWrap_accPay_eval S k j o hdr _ _)
  rw [hLhs]
  rcases stL with ⟨tp?, sm, ord, pk, sigB, fg?⟩
  cases fg? with
  | some fgVal =>
    have hLegK :
        (sigKindAcceptOpkSessLeg S (keyIndKFuelsOfBudget S b)).eval
          (.cons ((tp?, sm, ord, pk, sigB, some fgVal), fgSc)
            (.cons (k.val, (j.val, (o.val, _root_.SignalPqxdh.LegacyCosted.hdrV hdr))) .nil)) =
        pure (((rNone : Expr pqxdhOps [] keyIndRespTy).eval .nil),
          ((tp?, sm, ord, pk, sigB, some fgVal), fgSc)) := by
      simp [sigKindAcceptOpkSessLeg, saInner, s1Forgery, isSomeE, rNone,
        letV_eval, Comp.eval, Expr.eval, v]
    have hLegOld :
        (sig1KeyActiveHandleC S b.q_total).eval
          (.cons (sessWrap_fixSigLeg S b (tp?, sm, ord, pk, sigB, some fgVal))
            (.cons ((keyIndCodec S).qenc t) .nil)) =
        pure (((rNone : Expr pqxdhOps [] keyIndRespTy).eval .nil),
          sessWrap_fixSigLeg S b (tp?, sm, ord, pk, sigB, some fgVal)) := by
      simp [sig1KeyActiveHandleC, sig1KeyActivePreDispatchC, sessWrap_fixSigLeg,
        saInner, s1Forgery, isSomeE, rNone, bindV, caseSumV, Comp.eval, Expr.eval, v]
    rw [hLegK, hLegOld]
    simp only [map_pure, Prod.map_apply, ← hSc]
    refine ⟨rfl, ?_⟩
    intro y hy
    simp only [support_pure, Set.mem_singleton_iff] at hy
    subst hy
    exact sessWrap_GdhSimInv_bump_online_unchanged hInv rfl
  | none =>
    let pa2 : params2Ty.denote :=
      ([], (pk, ([], (none, (false, (none, (none, (false, (none, 1)))))))))
    have hLegK :
        ∃ (Γ₁a Γ₂a Γ₃a Γ₄a Γ₅a Δ₁ : List PT)
          (pa₁ : Var Γ₁a params2Ty) (sm₁ : Var Γ₂a simTy) (bSt₁ : Var Γ₃a keyIndStateTy)
          (fgSh₁ : Var Γ₅a fgSessCtrTy) (x₁ : Var Γ₄a accQTy)
          (_ : Ext Γ₁a Δ₁) (_ : Ext Γ₂a Δ₁) (_ : Ext Γ₃a Δ₁) (_ : Ext Γ₄a Δ₁) (_ : Ext Γ₅a Δ₁)
          (env₁ : Env Δ₁),
          (sigKindAcceptOpkSessLeg S (keyIndKFuelsOfBudget S b)).eval
            (.cons ((tp?, (sm, (ord, (pk, (sigB, none))))), fgSc)
              (.cons (k.val, (j.val, (o.val, _root_.SignalPqxdh.LegacyCosted.hdrV hdr))) .nil)) =
          (fun r => (r.1, ((tp?, (r.2.1, (ord, (pk, (sigB, none))))), r.2.2))) <$>
            liftGdhToSign
              ((acceptOpkGdh2ShadowB S (keyIndKFuelsOfBudget S b) pa₁ sm₁ bSt₁ fgSh₁ x₁).eval env₁) ∧
          (v pa₁).eval env₁ = pa2 ∧
          (v sm₁).eval env₁ = sm ∧
          (v bSt₁).eval env₁ = sm.1 ∧
          (v fgSh₁).eval env₁ = fgSc ∧
          (v x₁).eval env₁ =
            (k.val, (j.val, (o.val, _root_.SignalPqxdh.LegacyCosted.hdrV hdr))) := by
      simp only [sigKindAcceptOpkSessLeg, saInner, saTP, s1Forgery, s1Pk, s1Fg, s1Upd,
        pa2Mk, smBase, litB, isSomeE, liftGdhToSigDdh_eval,
        letV_eval, bindV, Comp.eval, Expr.eval, v, map_eq_bind_pure_comp, Function.comp_def]
      exact ⟨_, _, _, _, _, _, _, _, _, _, _,
        inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, _,
        rfl, rfl, rfl, rfl, rfl, rfl⟩
    obtain ⟨Γ₁a, Γ₂a, Γ₃a, Γ₄a, Γ₅a, Δ₁, pa₁, sm₁, bSt₁, fgSh₁, x₁,
      _, _, _, _, _, env₁, hK, hpa₁, hsm₁, hbSt₁, hfg₁, hx₁⟩ := hLegK
    obtain ⟨Γ₁b, Γ₂b, Γ₃b, Γ₄b, Δ₂, pa₂, sm₂, bSt₂, x₂,
      _, _, _, _, env₂, hGdh2, hpa₂, hsm₂, hbSt₂, hx₂⟩ :=
      sessWrap_gdhHandle2_eval_acceptOPK S b.q_total pa2 sm k j o hdr
    have hLegOld :
        (sig1KeyActiveHandleC S b.q_total).eval
          (.cons (sessWrap_fixSigLeg S b (tp?, (sm, (ord, (pk, (sigB, none))))))
            (.cons ((keyIndCodec S).qenc t) .nil)) =
        (fun p => (p.1, (tp?, (p.2, (fixSent S b ord, (pk, (sigB, none))))))) <$>
          liftGdhToSign
            ((acceptOpkGdh2B S b.q_total pa₂ sm₂ bSt₂ x₂).eval env₂) := by
      simp only [sig1KeyActiveHandleC, sig1KeyActivePreDispatchC, sessWrap_fixSigLeg,
        t, keyIndCodec, _root_.SignalPqxdh.LegacyCosted.keyIndQenc,
        Comp.rename_eval, _root_.ReductionDsl.Env.ofRename, renamePair,
        saInner, saTP, s1Forgery, s1Pk, s1Fg, s1Upd, pa2Mk, litB, isSomeE,
        liftGdhToSigDdh_eval, letV_eval, bindV, caseSumV, Comp.eval, Expr.eval, v, Ext.wk]
      change (do
          let r ← liftGdhToSign
            ((gdhHandle2 S b.q_total).eval (.cons (pa2, sm) (.cons ((keyIndCodec S).qenc t) .nil)))
          pure (r.1, (tp?, (r.2.2, (fixSent S b ord, (pk, (sigB, none))))))) = _
      rw [hGdh2, gdhLift1Key_valid.evalGdh_map]
      simp only [map_eq_bind_pure_comp, bind_assoc, pure_bind, Function.comp_def]
    rw [hK, hLegOld]
    have hInvSm :
        GdhSimInv S b c
          (embedVal simTy ((v sm₁).eval env₁),
            ((embedVal fgSessCtrTy ((v fgSh₁).eval env₁)).1,
              ((embedVal fgSessCtrTy ((v fgSh₁).eval env₁)).2, sh.2.2))) := by
      rw [hsm₁, hfg₁, ← hSc]; exact hInv
    have ⟨hEqM, hInvM⟩ :=
      acceptOpkGdh2ShadowB_sim S b pa₁ sm₁ bSt₁ fgSh₁ x₁ pa₂ sm₂ bSt₂ x₂ env₁ env₂
        c t sh (hpa₁.trans hpa₂.symm) (hsm₁.trans hsm₂.symm)
        (hbSt₁.trans (congrArg Prod.fst hsm₁.symm))
        (hbSt₂.trans (congrArg Prod.fst hsm₂.symm))
        (hx₁.trans hx₂.symm) (sessWrap_simPred_0 rfl) (sessWrap_simPred_1 rfl) hB hRoom hInvSm
    exact sessWrap_sig_liftGdh_step S b (bumpPred (keyIndSimPred S) c t)
      tp? ord pk sigB sh _ _ hEqM hInvM

/-- `.acceptNoOPK` step simulation for active 1-key `sigKeyInd1KeyKindAtomicProg`. -/
theorem sigKeyInd1KeyKindAtomicProg_hStep_acceptNoOPK (S : Setup) (b : QueryBudget) :
    ∀ k j l hdr, KeyIndStepSim S b (forgetSig1KeyActiveK S b) (Sig1KeyActiveSimInv S b)
      (sig1KeyKindHandleC S b) (sigKeyInd1KeyActiveAtomicProg S b).handle
      (.acceptNoOPK k j l hdr) := by
  intro k j l hdr c stK hB hRoom hInv
  let t : KeyIndQuery S := .acceptNoOPK k j l hdr
  let stL : sig1KeyActiveStTy.denote := projVal sig1KeyActiveStTy stK.1
  let sh : fgShadowAtomicTy.denote := stK.2
  let fgSc : fgSessCtrTy.denote := projVal fgSessCtrTy (sh.1, sh.2.1)
  have hStK : stK = (embedVal sig1KeyActiveStTy stL, sh) :=
    Prod.ext (embedVal_projVal sig1KeyActiveStTy stK.1).symm rfl
  have hSc : (sh.1, sh.2.1) = embedVal fgSessCtrTy fgSc :=
    (embedVal_projVal fgSessCtrTy (sh.1, sh.2.1)).symm
  rw [hStK] at hInv ⊢
  rw [sessWrap_forgetSig1KeyActiveK_embedVal, sessWrap_sigActiveAtomic_handle_eval]
  have hLhs :
      (sig1KeyKindHandleC S b).eval
        (.cons (embedVal sig1KeyActiveStTy stL, sh) (.cons ((pqKeyIndCodec S).qenc t) .nil)) =
      (fun r => (embedVal keyIndRespTy r.1,
        (embedVal sig1KeyActiveStTy r.2.1,
          ((embedVal fgSessCtrTy r.2.2).1, ((embedVal fgSessCtrTy r.2.2).2, sh.2.2))))) <$>
        (sigKindAcceptNoOpkSessLeg S (keyIndKFuelsOfBudget S b)).eval
          (.cons (stL, fgSc)
            (.cons (k.val, (j.val, (l.val, _root_.SignalPqxdh.LegacyCosted.hdrV hdr))) .nil)) := by
    unfold sig1KeyKindHandleC
    dsimp only
    rw [dispatchKeyIndQ_eval]
    exact sessWrap_liftSigDdhSessArm_eval S _ _
      (sessWrap_sigKindAcceptNoOpkSessLeg_unsupported S _) _ stL fgSc sh hSc _ _
      (sessWrap_accPay_eval S k j l hdr _ _)
  rw [hLhs]
  rcases stL with ⟨tp?, sm, ord, pk, sigB, fg?⟩
  cases fg? with
  | some fgVal =>
    have hLegK :
        (sigKindAcceptNoOpkSessLeg S (keyIndKFuelsOfBudget S b)).eval
          (.cons ((tp?, sm, ord, pk, sigB, some fgVal), fgSc)
            (.cons (k.val, (j.val, (l.val, _root_.SignalPqxdh.LegacyCosted.hdrV hdr))) .nil)) =
        pure (((rNone : Expr pqxdhOps [] keyIndRespTy).eval .nil),
          ((tp?, sm, ord, pk, sigB, some fgVal), fgSc)) := by
      simp [sigKindAcceptNoOpkSessLeg, saInner, s1Forgery, isSomeE, rNone,
        letV_eval, Comp.eval, Expr.eval, v]
    have hLegOld :
        (sig1KeyActiveHandleC S b.q_total).eval
          (.cons (sessWrap_fixSigLeg S b (tp?, sm, ord, pk, sigB, some fgVal))
            (.cons ((keyIndCodec S).qenc t) .nil)) =
        pure (((rNone : Expr pqxdhOps [] keyIndRespTy).eval .nil),
          sessWrap_fixSigLeg S b (tp?, sm, ord, pk, sigB, some fgVal)) := by
      simp [sig1KeyActiveHandleC, sig1KeyActivePreDispatchC, sessWrap_fixSigLeg,
        saInner, s1Forgery, isSomeE, rNone, bindV, caseSumV, Comp.eval, Expr.eval, v]
    rw [hLegK, hLegOld]
    simp only [map_pure, Prod.map_apply, ← hSc]
    refine ⟨rfl, ?_⟩
    intro y hy
    simp only [support_pure, Set.mem_singleton_iff] at hy
    subst hy
    exact sessWrap_GdhSimInv_bump_online_unchanged hInv rfl
  | none =>
    let pa2 : params2Ty.denote :=
      ([], (pk, ([], (none, (false, (none, (none, (false, (none, 1)))))))))
    have hLegK :
        ∃ (Γ₂a Γ₃a Γ₄a Γ₅a Δ₁ : List PT)
          (sm₁ : Var Γ₂a simTy) (bSt₁ : Var Γ₃a keyIndStateTy)
          (fgSh₁ : Var Γ₅a fgSessCtrTy) (x₁ : Var Γ₄a accQTy)
          (_ : Ext Γ₂a Δ₁) (_ : Ext Γ₃a Δ₁) (_ : Ext Γ₄a Δ₁) (_ : Ext Γ₅a Δ₁)
          (env₁ : Env Δ₁),
          (sigKindAcceptNoOpkSessLeg S (keyIndKFuelsOfBudget S b)).eval
            (.cons ((tp?, (sm, (ord, (pk, (sigB, none))))), fgSc)
              (.cons (k.val, (j.val, (l.val, _root_.SignalPqxdh.LegacyCosted.hdrV hdr))) .nil)) =
          (fun r => (r.1, ((tp?, (r.2.1, (ord, (pk, (sigB, none))))), r.2.2))) <$>
            liftGdhToSign
              ((acceptNoOpkGdhShadowB S (keyIndKFuelsOfBudget S b) sm₁ bSt₁ fgSh₁ x₁).eval env₁) ∧
          (v sm₁).eval env₁ = sm ∧
          (v bSt₁).eval env₁ = sm.1 ∧
          (v fgSh₁).eval env₁ = fgSc ∧
          (v x₁).eval env₁ =
            (k.val, (j.val, (l.val, _root_.SignalPqxdh.LegacyCosted.hdrV hdr))) := by
      simp only [sigKindAcceptNoOpkSessLeg, saInner, saTP, s1Forgery, s1Fg, s1Upd,
        smBase, isSomeE, liftGdhToSigDdh_eval,
        letV_eval, bindV, Comp.eval, Expr.eval, v, map_eq_bind_pure_comp, Function.comp_def]
      exact ⟨_, _, _, _, _, _, _, _, _,
        inferInstance, inferInstance, inferInstance, inferInstance, _,
        rfl, rfl, rfl, rfl, rfl⟩
    obtain ⟨Γ₂a, Γ₃a, Γ₄a, Γ₅a, Δ₁, sm₁, bSt₁, fgSh₁, x₁,
      _, _, _, _, env₁, hK, hsm₁, hbSt₁, hfg₁, hx₁⟩ := hLegK
    obtain ⟨Γ₂b, Γ₃b, Γ₄b, Δ₂, sm₂, bSt₂, x₂,
      _, _, _, env₂, hGdh2, hsm₂, hbSt₂, hx₂⟩ :=
      sessWrap_gdhHandle2_eval_acceptNoOPK S b.q_total pa2 sm k j l hdr
    have hLegOld :
        (sig1KeyActiveHandleC S b.q_total).eval
          (.cons (sessWrap_fixSigLeg S b (tp?, (sm, (ord, (pk, (sigB, none))))))
            (.cons ((keyIndCodec S).qenc t) .nil)) =
        (fun p => (p.1, (tp?, (p.2, (fixSent S b ord, (pk, (sigB, none))))))) <$>
          liftGdhToSign
            ((acceptNoOpkGdhB S b.q_total sm₂ bSt₂ x₂).eval env₂) := by
      simp only [sig1KeyActiveHandleC, sig1KeyActivePreDispatchC, sessWrap_fixSigLeg,
        t, keyIndCodec, _root_.SignalPqxdh.LegacyCosted.keyIndQenc,
        Comp.rename_eval, _root_.ReductionDsl.Env.ofRename, renamePair,
        saInner, saTP, s1Forgery, s1Pk, s1Fg, s1Upd, pa2Mk, litB, isSomeE,
        liftGdhToSigDdh_eval, letV_eval, bindV, caseSumV, Comp.eval, Expr.eval, v, Ext.wk]
      change (do
          let r ← liftGdhToSign
            ((gdhHandle2 S b.q_total).eval (.cons (pa2, sm) (.cons ((keyIndCodec S).qenc t) .nil)))
          pure (r.1, (tp?, (r.2.2, (fixSent S b ord, (pk, (sigB, none))))))) = _
      rw [hGdh2, gdhLift1Key_valid.evalGdh_map]
      simp only [map_eq_bind_pure_comp, bind_assoc, pure_bind, Function.comp_def]
    rw [hK, hLegOld]
    have hInvSm :
        GdhSimInv S b c
          (embedVal simTy ((v sm₁).eval env₁),
            ((embedVal fgSessCtrTy ((v fgSh₁).eval env₁)).1,
              ((embedVal fgSessCtrTy ((v fgSh₁).eval env₁)).2, sh.2.2))) := by
      rw [hsm₁, hfg₁, ← hSc]; exact hInv
    have ⟨hEqM, hInvM⟩ :=
      acceptNoOpkGdhShadowB_sim S b sm₁ bSt₁ fgSh₁ x₁ sm₂ bSt₂ x₂ env₁ env₂
        c t sh (hsm₁.trans hsm₂.symm)
        (hbSt₁.trans (congrArg Prod.fst hsm₁.symm))
        (hbSt₂.trans (congrArg Prod.fst hsm₂.symm))
        (hx₁.trans hx₂.symm) (sessWrap_simPred_0 rfl) (sessWrap_simPred_1 rfl) hB hRoom hInvSm
    exact sessWrap_sig_liftGdh_step S b (bumpPred (keyIndSimPred S) c t)
      tp? ord pk sigB sh _ _ hEqM hInvM

end SessSigProgramWrappers

section FgProgSessWrappers

open _root_.SignalPqxdh.Security (keyIndQueryKind)
open _root_.SignalPqxdh.LegacyCosted (keyIndCodec)
open Computational.Proofs.SignalPqxdh.AtomicLift (
  embedVal_projVal keyIndUnsupportedPrimW liftKeyIndHandle_eval
)
open _root_.SignalPqxdh.Security.ReductionDsl.KeyInd (
  keyIndQueryTy gdhState2Ty rNone pa2Mk paU paV paUp paOpkMode
  wrapBase2 wrapSim2 gdhHandle2
  initPrinGdh2B genSpkGdh2B genOpkGdh2B initiateGdh2B acceptOpkGdh2B acceptNoOpkGdhB
  corruptB testB roParsedC roRawFallbackC revealB registerGdhB revealSpkB
  sRandom64 qSigPkGen qSigSign qKemKeyGen
)
open _root_.SignalPqxdh.Security.ReductionDsl.KeyInd1KeyGapDh (
  gdh1KeyStateTy liftGdhComp liftGdhComp_eval
  liftGdhToSign_bind liftGdhToSign_map liftGdhToSign_pure mem_support_liftGdhToSign
  twoVarRen pullEnv_twoVarRen renameComp renameComp_eval
)
open Computational.Proofs.SignalPqxdh.Delta.KeyInd1KeyActiveProgs (
  gdh1KeyActiveStateTy callGdhActiveHandle
  initPrin1KeyActiveGdhB genSpk1KeyActiveGdhB genSpkGdhActiveB genOpkActiveGdhB
  initiateActiveGdhB initiateGdhActiveInnerB gdh1KeyActiveHandle
  fgKeyInd1KeyGapDhActiveDslProg
)
open Computational.Proofs.SignalPqxdh.Delta.KindSplit.KeyInd1KeyKindProgs (
  liftSigDdhSessArm gdhKindInitiateSessLeg gdhKindAcceptOpkSessLeg gdhKindAcceptNoOpkSessLeg
)
open Computational.Proofs.SignalPqxdh.Security.ReductionDsl.KindSplit.KeyIndCoreK (
  dispatchKeyIndQ runAt2 initPayToNatE accPayToNatE
)
open Computational.Proofs.SignalPqxdh.Security.ReductionDsl.KindSplit.KeyIndCoreKSimBase (
  keyIndSimPred_one_iff_kind dispatchKeyIndQ_eval runAt2_eval
)
open Computational.Proofs.SignalPqxdh.Security.ReductionDsl.KindSplit.KeyIndGapDhKSimBase (
  entryMatchesC_unsupported_zero
)

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
  fgKeyInd1KeyGapDhActiveAtomicProg
  fgKeyInd1KeyGapDhActiveDslProg
  _root_.ReductionDsl.CostedReduction.σ
  Env.get

@[local simp] private theorem liftGdhComp_unsup_fg {Γ : List PT} {t : PT}
    (c : Comp pqxdhOps pqGapDhIface Γ t) :
    (liftGdhComp c).queries tlSigDdhKeyInd.unsupportedW (fun _ => 0) =
      c.queries tlGapDhKeyInd.unsupportedW (fun _ => 0) := by
  induction c with
  | query g _ => rcases g with _ | ⟨⟩ <;> rfl
  | sample _ _ => rfl
  | _ => simp_all [liftGdhComp, Comp.queries]

@[local simp] private theorem renameComp_queries_fg {ι : Type} {T : OracleSpec ι}
    {I : Iface pqSig T} (w : I.Tag → ℕ) (ws : I.smp.Samp → ℕ) :
    ∀ {Γ Δ : List PT} {t : PT}
      (ρ : _root_.SignalPqxdh.Security.ReductionDsl.KeyInd1KeyGapDh.Ren Γ Δ)
      (c : Comp pqxdhOps I Γ t),
      (renameComp ρ c).queries w ws = c.queries w ws := by
  intro Γ Δ t ρ c
  induction c generalizing Δ <;> simp_all [renameComp, Comp.queries]

@[local simp] private theorem liftBase_queries_fg
    {C : _root_.SignalPqxdh.LegacyCosted.ChallengerOracle}
    (w : (_root_.SignalPqxdh.LegacyCosted.pqChalIface C).Tag → ℕ)
    (ws : (_root_.SignalPqxdh.LegacyCosted.pqChalIface C).smp.Samp → ℕ)
    {Γ : List PT} {τ : PT} (c : Comp pqxdhOps pqPrimIface Γ τ) :
    (_root_.SignalPqxdh.Security.ReductionDsl.KeyInd.liftBase (C := C) c).queries w ws =
      Comp.queries (I := pqPrimIface) (fun g => w (.inl g)) (fun s => ws s) c := by
  induction c <;> simp_all [_root_.SignalPqxdh.Security.ReductionDsl.KeyInd.liftBase, Comp.queries]

@[local simp] private theorem wrapBase2_unsup_fg {Γ₁ Γ₂ Δ : List PT} [Ext Γ₁ Δ] [Ext Γ₂ Δ]
    (pa : Var Γ₁ params2Ty) (sm : Var Γ₂ simTy)
    (c : Comp pqxdhOps pqPrimIface Δ (.prod keyIndRespTy keyIndStateTy)) :
    (wrapBase2 pa sm c).queries tlGapDhKeyInd.unsupportedW (fun _ => 0) =
      c.queries keyIndUnsupportedPrimW (fun _ => 0) := by
  simp [wrapBase2, gPrim, bindV, Comp.queries, tlGapDhKeyInd]

@[local simp] private theorem wrapSim2_unsup_fg {Γ₁ Δ : List PT} [Ext Γ₁ Δ]
    (pa : Var Γ₁ params2Ty)
    (c : Comp pqxdhOps pqGapDhIface Δ (.prod keyIndRespTy simTy)) :
    (wrapSim2 pa c).queries tlGapDhKeyInd.unsupportedW (fun _ => 0) =
      c.queries tlGapDhKeyInd.unsupportedW (fun _ => 0) := by
  simp [wrapSim2, bindV, Comp.queries]

private theorem gdhHandle2_unsup_fg (S : Setup) (K : Nat) :
    (gdhHandle2 S K).queries tlGapDhKeyInd.unsupportedW (fun _ => 0) = 0 := by
  simp only [gdhHandle2, wrapBase2_unsup_fg, wrapSim2_unsup_fg, entryMatchesC_unsupported_zero,
    initPrinGdh2B, genSpkGdh2B, genOpkGdh2B, initiateGdh2B, acceptOpkGdh2B, acceptNoOpkGdhB,
    finishAcceptGdhC, corruptB, testB, roParsedC, roRawFallbackC, revealB, registerGdhB, revealSpkB,
    gPrim, chooseInitRandC, chooseRespRandC, lookupSpkSkC, computePosC,
    _root_.SignalPqxdh.Security.ReductionDsl.KeyInd.mkPairPosC, fgPatchC,
    findHonestC, honestPeerC, checkProvC, koskBundleOkPowsC, koskSenderOkPowsC, computeOptPosInitC,
    mkSecretPosC, isGameSpkC, isGameOpkC, resolveSigPkC, partnerC, findMV, anyMV,
    liftBase_queries_fg, letV, bindV, caseOptV, caseSumV, Comp.queries]
  simp [sBytes32, sRandom64, sDrKey96, qX25519, qX25519Base, qPow8, qIsCanonical, qSigPkGen,
    qSigSign, qSigVerify, qKemKeyGen, qKemEncaps, qKemDecaps, Comp.queries, tlGapDhKeyInd,
    keyIndUnsupportedPrimW]

@[local simp] private theorem sigChalQ_dsl_unsup_fg (m : ℕ+) {Γ : List PT}
    (msg : Expr pqxdhOps Γ (B m)) :
    (_root_.SignalPqxdh.Security.ReductionDsl.KeyInd1KeyGapDh.sigChalQ_dsl m msg).queries
      tlSigDdhKeyInd.unsupportedW (fun _ => 0) = 0 := rfl

@[local simp] private theorem callGdhActiveHandle_unsup_fg (S : Setup) (K : Nat) {Δ : List PT}
    (stA : Var Δ gdh1KeyActiveStateTy) (q : Var Δ keyIndQueryTy) :
    (callGdhActiveHandle S K stA q).queries tlSigDdhKeyInd.unsupportedW (fun _ => 0) = 0 := by
  have hGdh := gdhHandle2_unsup_fg S K
  simp [callGdhActiveHandle, hGdh, letV, bindV, Comp.queries]

private theorem gdhActive_handle_unsup_fg (S : Setup) (b : QueryBudget) :
    (fgKeyInd1KeyGapDhActiveDslProg S b).handle.queries tlSigDdhKeyInd.unsupportedW (fun _ => 0) = 0 := by
  change (gdh1KeyActiveHandle S b.q_total).queries tlSigDdhKeyInd.unsupportedW (fun _ => 0) = 0
  simp only [gdh1KeyActiveHandle, callGdhActiveHandle_unsup_fg, entryMatchesC_unsupported_zero,
    initPrin1KeyActiveGdhB, genSpk1KeyActiveGdhB, genSpkGdhActiveB, genOpkActiveGdhB,
    initiateActiveGdhB, initiateGdhActiveInnerB, gPrim, chooseInitRandC, lookupSpkSkC,
    computePosC, _root_.SignalPqxdh.Security.ReductionDsl.KeyInd.mkPairPosC, fgPatchC,
    findHonestC, honestPeerC, checkProvC, koskBundleOkPowsC,
    computeOptPosInitC, mkSecretPosC, isGameSpkC, isGameOpkC, resolveSigPkC, partnerC, findMV,
    anyMV, liftGdhComp_unsup_fg, sigChalQ_dsl_unsup_fg, liftBase_queries_fg,
    letV, bindV, caseOptV, caseSumV, Comp.queries]
  simp [sBytes32, sRandom64, sDrKey96, qX25519, qX25519Base, qPow8, qIsCanonical, qSigSign,
    qSigVerify, qKemKeyGen, qKemEncaps, Comp.queries, tlGapDhKeyInd, keyIndUnsupportedPrimW]

private theorem gdhActiveAtomic_handle_eval_fg (S : Setup) (b : QueryBudget)
    (stA : gdh1KeyActiveStateTy.denote) (t : KeyIndQuery S) :
    (fgKeyInd1KeyGapDhActiveAtomicProg S b).handle.eval
        (.cons (embedVal gdh1KeyActiveStateTy stA :
            (fgKeyInd1KeyGapDhActiveAtomicProg S b).σ.denote)
          (.cons ((pqKeyIndCodec S).qenc t) .nil)) =
      embedVal (.prod keyIndRespTy gdh1KeyActiveStateTy) <$>
        (gdh1KeyActiveHandle S b.q_total).eval
          (.cons stA (.cons ((keyIndCodec S).qenc t) .nil)) :=
  liftKeyIndHandle_eval tlSigDdhKeyInd S (fgKeyInd1KeyGapDhActiveDslProg S b).handle
    (gdhActive_handle_unsup_fg S b) stA t

private def fixParamsLeg_fg (S : Setup) (b : QueryBudget)
    (pa : paramsTy.denote) : paramsTy.denote :=
  let (u, (vPk, (up, (prinFlag, (prinIdx, (dhFlag, (ephIdx, (spkIdx, (opkMode, (opkIdx, mode)))))))))) := pa
  (u, (vPk, (up, (prinFlag, (fixSent S b prinIdx,
    (dhFlag, (fixSent S b ephIdx, (fixSent S b spkIdx, (opkMode, (fixSent S b opkIdx, mode))))))))))

private def fixGdhLeg_fg (S : Setup) (b : QueryBudget)
    (stA : gdh1KeyActiveStateTy.denote) : gdh1KeyActiveStateTy.denote :=
  (((fixParamsLeg_fg S b stA.1.1.1, stA.1.1.2), stA.1.2), stA.2)

private theorem forgetGdh1KeyActiveK_embedVal_fg (S : Setup) (b : QueryBudget)
    (stA : gdh1KeyActiveStateTy.denote) (sh : fgShadowAtomicTy.denote) :
    forgetGdh1KeyActiveK S b (embedVal gdh1KeyActiveStateTy stA, sh) =
      embedVal gdh1KeyActiveStateTy (fixGdhLeg_fg S b stA) := rfl

private theorem embedVal_fixParamsLeg_fg (S : Setup) (b : QueryBudget)
    (pa : paramsTy.denote) :
    embedVal paramsTy (fixParamsLeg_fg S b pa) =
      fixParamsSent S b (embedVal paramsTy pa) := rfl

private theorem gdhKindInitiateSessLeg_unsup_fg (S : Setup) (f : KeyIndKFuels) (hasOpk : Bool) :
    (gdhKindInitiateSessLeg S f hasOpk).queries tlSigDdhKeyInd.unsupportedW (fun _ => 0) = 0 := by
  simp only [gdhKindInitiateSessLeg, initiateGdhActiveShadowInnerB, fgPatchShadowC,
    entryMatchesC_unsupported_zero, gPrim, chooseInitRandC, lookupSpkSkC, computePosC,
    _root_.SignalPqxdh.Security.ReductionDsl.KeyInd.mkPairPosC, findHonestC, honestPeerC,
    checkProvC, koskBundleOkPowsC, computeOptPosInitC, mkSecretPosC, isGameSpkC, isGameOpkC,
    resolveSigPkC, partnerC, findMV, anyMV, liftGdhComp_unsup_fg, liftBase_queries_fg,
    letV, bindV, caseOptV, Comp.queries]
  simp [sBytes32, sDrKey96, qX25519, qX25519Base, qPow8, qIsCanonical,
    qSigVerify, qKemEncaps, Comp.queries, tlGapDhKeyInd, keyIndUnsupportedPrimW]

private theorem liftSigDdhSessArm_eval_fg (S : Setup) {stTy qPayTy : PT}
    {PayAtomic : Ty pqAtomicSig}
    (payE : Expr pqAtomicOps
      (PayAtomic :: [.prod (embedTy stTy) fgShadowAtomicTy, (pqKeyIndCodec S).Q])
      (embedTy qPayTy))
    (arm : Comp pqxdhOps pqSigAndDdhIface
      [.prod stTy fgSessCtrTy, qPayTy]
      (.prod keyIndRespTy (.prod stTy fgSessCtrTy)))
    (hUnsup : arm.queries tlSigDdhKeyInd.unsupportedW (fun _ => 0) = 0)
    (payA : PayAtomic.denote) (stL : stTy.denote) (sh : fgShadowAtomicTy.denote)
    (qEnc : (pqKeyIndCodec S).Q.denote) (payLeg : qPayTy.denote)
    (hPay : payE.eval (.cons payA (.cons (embedVal stTy stL, sh) (.cons qEnc .nil))) =
      embedVal qPayTy payLeg) :
    (liftSigDdhSessArm S payE arm).eval
        (.cons payA (.cons (embedVal stTy stL, sh) (.cons qEnc .nil))) =
      (fun r =>
        (embedVal keyIndRespTy r.1,
          (embedVal stTy r.2.1,
            ((embedVal fgSessCtrTy r.2.2).1,
              ((embedVal fgSessCtrTy r.2.2).2, sh.2.2))))) <$>
        arm.eval (.cons (stL, projVal fgSessCtrTy (sh.1, sh.2.1)) (.cons payLeg .nil)) :=
  sessWrap_liftSigDdhSessArm_eval S payE arm hUnsup payA stL
    (projVal fgSessCtrTy (sh.1, sh.2.1)) sh (embedVal_projVal fgSessCtrTy (sh.1, sh.2.1)).symm
    qEnc payLeg hPay

private theorem initPayToNatE_bundleV_fg (N_s : ℕ) (S : Setup)
    (u : Fin S.N_id) (i : Fin N_s) (bu : _root_.SignalPqxdh.PreKeyBundleInput)
    (stK : (Ty.prod (embedTy gdh1KeyActiveStateTy) fgShadowAtomicTy).denote)
    (qEnc : (pqKeyIndCodec S).Q.denote) :
    (initPayToNatE N_s S .v0).eval
        (.cons (u, (i, _root_.ReductionDsl.bundleV bu)) (.cons stK (.cons qEnc .nil))) =
      embedVal initQTy (u.val, (i.val, _root_.SignalPqxdh.LegacyCosted.bundleV bu)) := by
  rcases bu with ⟨_, _, _, _, _ | ⟨_, _⟩, _, _, _⟩ <;> rfl

private theorem accPayToNatE_hdrV_fg (N_o : ℕ) (S : Setup)
    (k : Fin S.N_id) (j : Fin S.N_recv) (o : Fin N_o)
    (hdr : _root_.SignalPqxdh.HandshakeHdr)
    (stK : (Ty.prod (embedTy gdh1KeyActiveStateTy) fgShadowAtomicTy).denote)
    (qEnc : (pqKeyIndCodec S).Q.denote) :
    (accPayToNatE N_o S .v0).eval
        (.cons (k, (j, (o, _root_.ReductionDsl.hdrV hdr))) (.cons stK (.cons qEnc .nil))) =
      embedVal accQTy (k.val, (j.val, (o.val, _root_.SignalPqxdh.LegacyCosted.hdrV hdr))) := by
  rcases hdr with ⟨_, _, _, _ | _, _, _⟩ <;> rfl

private theorem gdhKindAcceptOpkSessLeg_unsup_fg (S : Setup) (f : KeyIndKFuels) :
    (gdhKindAcceptOpkSessLeg S f).queries tlSigDdhKeyInd.unsupportedW (fun _ => 0) = 0 := by
  simp only [gdhKindAcceptOpkSessLeg, acceptOpkGdh2ShadowB, acceptOpkGdhCoreShadowB,
    fgPatchShadowC, finishAcceptGdhC, entryMatchesC_unsupported_zero, gPrim, chooseRespRandC,
    computePosC, _root_.SignalPqxdh.Security.ReductionDsl.KeyInd.mkPairPosC,
    findHonestC, koskSenderOkPowsC, mkSecretPosC, partnerC, findMV,
    liftGdhComp_unsup_fg, liftBase_queries_fg, letV, bindV, caseOptV, Comp.queries]
  simp [sDrKey96, qX25519, qPow8, qIsCanonical, qKemDecaps,
    Comp.queries, tlGapDhKeyInd, keyIndUnsupportedPrimW]

private theorem gdhKindAcceptNoOpkSessLeg_unsup_fg (S : Setup) (f : KeyIndKFuels) :
    (gdhKindAcceptNoOpkSessLeg S f).queries tlSigDdhKeyInd.unsupportedW (fun _ => 0) = 0 := by
  simp only [gdhKindAcceptNoOpkSessLeg, acceptNoOpkGdhShadowB, fgPatchShadowC, finishAcceptGdhC,
    entryMatchesC_unsupported_zero, gPrim, chooseRespRandC, computePosC,
    _root_.SignalPqxdh.Security.ReductionDsl.KeyInd.mkPairPosC, findHonestC,
    koskSenderOkPowsC, mkSecretPosC, partnerC, findMV, liftGdhComp_unsup_fg,
    liftBase_queries_fg, letV, bindV, caseOptV, Comp.queries]
  simp [sDrKey96, qX25519, qPow8, qIsCanonical, qKemDecaps,
    Comp.queries, tlGapDhKeyInd, keyIndUnsupportedPrimW]

private theorem liftGdh_bind_sim_fg {α β γ δ : Type}
    {m₁ : OracleComp _root_.SignalPqxdh.Security.FgGapDh.GdhSimSpec α}
    {m₂ : OracleComp _root_.SignalPqxdh.Security.FgGapDh.GdhSimSpec β}
    (proj : α → β) {k₁ : α → γ} {k₁' : α → δ} {k₂ : β → δ}
    {Q : γ → Prop} {R : α → Prop}
    (hSim : proj <$> m₁ = m₂ ∧ ∀ r ∈ support m₁, R r)
    (hk : ∀ r, k₁' r = k₂ (proj r))
    (hQR : ∀ r, R r → Q (k₁ r)) :
    (liftGdhToSign m₁ >>= fun r => pure (k₁' r)) =
      (liftGdhToSign m₂ >>= fun b => pure (k₂ b)) ∧
    ∀ p ∈ support (liftGdhToSign m₁ >>= fun r => pure (k₁ r)), Q p := by
  refine ⟨?_, ?_⟩
  · have h1 := congrArg liftGdhToSign hSim.1
    rw [liftGdhToSign_map, map_eq_bind_pure_comp] at h1
    rw [← h1, bind_assoc]
    simp only [Function.comp_def, pure_bind, hk]
  · intro p hp
    simp only [MonadAttach.mem_support_bind, support_pure, Set.mem_singleton_iff] at hp
    rcases hp with ⟨r, hr, rfl⟩
    exact hQR r (hSim.2 r (mem_support_liftGdhToSign hr))

/-- `.initiateOPK` step simulation for active 1-key `fgKeyInd1KeyGapDhKindAtomicProg`. -/
theorem fgKeyInd1KeyGapDhKindAtomicProg_hStep_initiateOPK (S : Setup) (b : QueryBudget) :
    ∀ u i bu, KeyIndStepSim S b (forgetGdh1KeyActiveK S b) (Gdh1KeyActiveSimInv S b)
      (gdh1KeyKindHandleC S b) (fgKeyInd1KeyGapDhActiveAtomicProg S b).handle
      (.initiateOPK u i bu) := by
  intro u i bu c ⟨stA, sh⟩ hB hRoom hInv
  set stL := projVal gdh1KeyActiveStateTy stA
  have hStA : stA = embedVal gdh1KeyActiveStateTy stL :=
    (embedVal_projVal gdh1KeyActiveStateTy stA).symm
  rw [hStA] at hInv ⊢
  rcases stL with ⟨⟨⟨pa, sm⟩, sigB⟩, rp?, cnt⟩
  have hK : (gdh1KeyKindHandleC S b).eval
      (.cons (embedVal gdh1KeyActiveStateTy (((pa, sm), sigB), rp?, cnt), sh)
        (.cons ((pqKeyIndCodec S).qenc (.initiateOPK u i bu)) .nil)) =
      (fun r =>
        (embedVal keyIndRespTy r.1,
          (embedVal gdh1KeyActiveStateTy r.2.1,
            ((embedVal fgSessCtrTy r.2.2).1,
              ((embedVal fgSessCtrTy r.2.2).2, sh.2.2))))) <$>
        (gdhKindInitiateSessLeg S (keyIndKFuelsOfBudget S b) true).eval
          (.cons ((((pa, sm), sigB), rp?, cnt), projVal fgSessCtrTy (sh.1, sh.2.1))
            (.cons (u.val, (i.val, _root_.SignalPqxdh.LegacyCosted.bundleV bu)) .nil)) := by
    unfold gdh1KeyKindHandleC; dsimp only; rw [dispatchKeyIndQ_eval]
    exact liftSigDdhSessArm_eval_fg S _ _
      (gdhKindInitiateSessLeg_unsup_fg S (keyIndKFuelsOfBudget S b) true)
      _ (((pa, sm), sigB), rp?, cnt) sh _
      (u.val, (i.val, _root_.SignalPqxdh.LegacyCosted.bundleV bu))
      (initPayToNatE_bundleV_fg S.N_send_opk S u i bu _ _)
  rw [hK, forgetGdh1KeyActiveK_embedVal_fg, gdhActiveAtomic_handle_eval_fg]
  have hFgSc : embedVal fgSessCtrTy (projVal fgSessCtrTy (sh.1, sh.2.1)) = (sh.1, sh.2.1) :=
    embedVal_projVal fgSessCtrTy (sh.1, sh.2.1)
  simp only [gdhKindInitiateSessLeg, gdh1KeyActiveHandle, initiateActiveGdhB, fixGdhLeg_fg,
    keyIndCodec, _root_.SignalPqxdh.LegacyCosted.keyIndQenc,
    letV, bindV, caseSumV, Comp.eval, liftGdhComp_eval, Expr.eval, v, Ext.wk, Env.get,
    pure_bind, map_eq_bind_pure_comp, Function.comp_apply, bind_assoc]
  apply liftGdh_bind_sim_fg (fun r => (r.1, (r.2.1.1, r.2.2)))
  · apply initiateGdhActiveShadowInnerB_sim (c := c) (t := .initiateOPK u i bu) (fgShFull := sh)
    · exact embedVal_fixParamsLeg_fg S b pa
    · rfl
    · rfl
    · rfl
    · rfl
    · exact hInv.sendOpkCnt_le
    · rfl
    · simp [keyIndSimPred_zero_iff_kind, keyIndQueryKind]
    · simp [keyIndSimPred_one_iff_kind, keyIndQueryKind]
    · exact hB
    · exact hRoom
    · simp only [Expr.eval, v, Ext.wk, Env.get, hFgSc]; exact hInv.sim_inv
  · intro _; rfl
  · intro _ h; exact ⟨h.1, h.2⟩

/-- `.initiateNoOPK` step simulation for active 1-key `fgKeyInd1KeyGapDhKindAtomicProg`. -/
theorem fgKeyInd1KeyGapDhKindAtomicProg_hStep_initiateNoOPK (S : Setup) (b : QueryBudget) :
    ∀ u i bu, KeyIndStepSim S b (forgetGdh1KeyActiveK S b) (Gdh1KeyActiveSimInv S b)
      (gdh1KeyKindHandleC S b) (fgKeyInd1KeyGapDhActiveAtomicProg S b).handle
      (.initiateNoOPK u i bu) := by
  intro u i bu c ⟨stA, sh⟩ hB hRoom hInv
  set stL := projVal gdh1KeyActiveStateTy stA
  have hStA : stA = embedVal gdh1KeyActiveStateTy stL :=
    (embedVal_projVal gdh1KeyActiveStateTy stA).symm
  rw [hStA] at hInv ⊢
  rcases stL with ⟨⟨⟨pa, sm⟩, sigB⟩, rp?, cnt⟩
  have hK : (gdh1KeyKindHandleC S b).eval
      (.cons (embedVal gdh1KeyActiveStateTy (((pa, sm), sigB), rp?, cnt), sh)
        (.cons ((pqKeyIndCodec S).qenc (.initiateNoOPK u i bu)) .nil)) =
      (fun r =>
        (embedVal keyIndRespTy r.1,
          (embedVal gdh1KeyActiveStateTy r.2.1,
            ((embedVal fgSessCtrTy r.2.2).1,
              ((embedVal fgSessCtrTy r.2.2).2, sh.2.2))))) <$>
        (gdhKindInitiateSessLeg S (keyIndKFuelsOfBudget S b) false).eval
          (.cons ((((pa, sm), sigB), rp?, cnt), projVal fgSessCtrTy (sh.1, sh.2.1))
            (.cons (u.val, (i.val, _root_.SignalPqxdh.LegacyCosted.bundleV bu)) .nil)) := by
    unfold gdh1KeyKindHandleC; dsimp only; rw [dispatchKeyIndQ_eval]
    exact liftSigDdhSessArm_eval_fg S _ _
      (gdhKindInitiateSessLeg_unsup_fg S (keyIndKFuelsOfBudget S b) false)
      _ (((pa, sm), sigB), rp?, cnt) sh _
      (u.val, (i.val, _root_.SignalPqxdh.LegacyCosted.bundleV bu))
      (initPayToNatE_bundleV_fg S.N_send_no_opk S u i bu _ _)
  rw [hK, forgetGdh1KeyActiveK_embedVal_fg, gdhActiveAtomic_handle_eval_fg]
  have hFgSc : embedVal fgSessCtrTy (projVal fgSessCtrTy (sh.1, sh.2.1)) = (sh.1, sh.2.1) :=
    embedVal_projVal fgSessCtrTy (sh.1, sh.2.1)
  simp only [gdhKindInitiateSessLeg, gdh1KeyActiveHandle, initiateActiveGdhB, fixGdhLeg_fg,
    keyIndCodec, _root_.SignalPqxdh.LegacyCosted.keyIndQenc,
    letV, bindV, caseSumV, Comp.eval, liftGdhComp_eval, Expr.eval, v, Ext.wk, Env.get,
    pure_bind, map_eq_bind_pure_comp, Function.comp_apply, bind_assoc]
  apply liftGdh_bind_sim_fg (fun r => (r.1, (r.2.1.1, r.2.2)))
  · apply initiateGdhActiveShadowInnerB_sim (c := c) (t := .initiateNoOPK u i bu) (fgShFull := sh)
    · exact embedVal_fixParamsLeg_fg S b pa
    · rfl
    · rfl
    · rfl
    · rfl
    · exact hInv.sendOpkCnt_le
    · rfl
    · simp [keyIndSimPred_zero_iff_kind, keyIndQueryKind]
    · simp [keyIndSimPred_one_iff_kind, keyIndQueryKind]
    · exact hB
    · exact hRoom
    · simp only [Expr.eval, v, Ext.wk, Env.get, hFgSc]; exact hInv.sim_inv
  · intro _; rfl
  · intro _ h; exact ⟨h.1, h.2⟩

/-- `.acceptOPK` step simulation for active 1-key `fgKeyInd1KeyGapDhKindAtomicProg`. -/
theorem fgKeyInd1KeyGapDhKindAtomicProg_hStep_acceptOPK (S : Setup) (b : QueryBudget) :
    ∀ k j o hdr, KeyIndStepSim S b (forgetGdh1KeyActiveK S b) (Gdh1KeyActiveSimInv S b)
      (gdh1KeyKindHandleC S b) (fgKeyInd1KeyGapDhActiveAtomicProg S b).handle
      (.acceptOPK k j o hdr) := by
  intro k j o hdr c ⟨stA, sh⟩ hB hRoom hInv
  set stL := projVal gdh1KeyActiveStateTy stA
  have hStA : stA = embedVal gdh1KeyActiveStateTy stL :=
    (embedVal_projVal gdh1KeyActiveStateTy stA).symm
  rw [hStA] at hInv ⊢
  rcases stL with ⟨⟨⟨pa, sm⟩, sigB⟩, rp?, cnt⟩
  have hK : (gdh1KeyKindHandleC S b).eval
      (.cons (embedVal gdh1KeyActiveStateTy (((pa, sm), sigB), rp?, cnt), sh)
        (.cons ((pqKeyIndCodec S).qenc (.acceptOPK k j o hdr)) .nil)) =
      (fun r =>
        (embedVal keyIndRespTy r.1,
          (embedVal gdh1KeyActiveStateTy r.2.1,
            ((embedVal fgSessCtrTy r.2.2).1,
              ((embedVal fgSessCtrTy r.2.2).2, sh.2.2))))) <$>
        (gdhKindAcceptOpkSessLeg S (keyIndKFuelsOfBudget S b)).eval
          (.cons ((((pa, sm), sigB), rp?, cnt), projVal fgSessCtrTy (sh.1, sh.2.1))
            (.cons (k.val, (j.val, (o.val, _root_.SignalPqxdh.LegacyCosted.hdrV hdr))) .nil)) := by
    unfold gdh1KeyKindHandleC; dsimp only; rw [dispatchKeyIndQ_eval]
    exact liftSigDdhSessArm_eval_fg S _ _
      (gdhKindAcceptOpkSessLeg_unsup_fg S (keyIndKFuelsOfBudget S b))
      _ (((pa, sm), sigB), rp?, cnt) sh _
      (k.val, (j.val, (o.val, _root_.SignalPqxdh.LegacyCosted.hdrV hdr)))
      (accPayToNatE_hdrV_fg S.N_opk S k j o hdr _ _)
  rw [hK, forgetGdh1KeyActiveK_embedVal_fg, gdhActiveAtomic_handle_eval_fg]
  have hFgSc : embedVal fgSessCtrTy (projVal fgSessCtrTy (sh.1, sh.2.1)) = (sh.1, sh.2.1) :=
    embedVal_projVal fgSessCtrTy (sh.1, sh.2.1)
  have ht0 : keyIndSimPred S 0 (.acceptOPK k j o hdr) = true := by
    simp [keyIndSimPred_zero_iff_kind, keyIndQueryKind]
  simp only [gdhKindAcceptOpkSessLeg, gdh1KeyActiveHandle, callGdhActiveHandle, gdhHandle2,
    wrapSim2, fixGdhLeg_fg, keyIndCodec, _root_.SignalPqxdh.LegacyCosted.keyIndQenc,
    renameComp_eval, pullEnv_twoVarRen, liftGdhComp_eval,
    letV, bindV, caseSumV, Comp.eval, Expr.eval, v, Ext.wk, Env.get,
    pure_bind, liftGdhToSign_bind, liftGdhToSign_pure, map_eq_bind_pure_comp,
    Function.comp_apply, bind_assoc]
  apply liftGdh_bind_sim_fg (fun r => (r.1, r.2.1))
  · apply acceptOpkGdh2ShadowB_sim (c := c) (t := .acceptOPK k j o hdr) (fgShFull := sh)
    · rfl
    · rfl
    · rfl
    · rfl
    · rfl
    · exact ht0
    · simp [keyIndSimPred_one_iff_kind, keyIndQueryKind]
    · exact hB
    · exact hRoom
    · simp only [Expr.eval, v, Ext.wk, Env.get, hFgSc]; exact hInv.sim_inv
  · intro _; rfl
  · intro _ h
    exact ⟨h, by simp only [bumpPred, ht0, ↓reduceIte]; exact Nat.le_succ_of_le hInv.sendOpkCnt_le⟩

/-- `.acceptNoOPK` step simulation for active 1-key `fgKeyInd1KeyGapDhKindAtomicProg`. -/
theorem fgKeyInd1KeyGapDhKindAtomicProg_hStep_acceptNoOPK (S : Setup) (b : QueryBudget) :
    ∀ k j l hdr, KeyIndStepSim S b (forgetGdh1KeyActiveK S b) (Gdh1KeyActiveSimInv S b)
      (gdh1KeyKindHandleC S b) (fgKeyInd1KeyGapDhActiveAtomicProg S b).handle
      (.acceptNoOPK k j l hdr) := by
  intro k j l hdr c ⟨stA, sh⟩ hB hRoom hInv
  set stL := projVal gdh1KeyActiveStateTy stA
  have hStA : stA = embedVal gdh1KeyActiveStateTy stL :=
    (embedVal_projVal gdh1KeyActiveStateTy stA).symm
  rw [hStA] at hInv ⊢
  rcases stL with ⟨⟨⟨pa, sm⟩, sigB⟩, rp?, cnt⟩
  have hK : (gdh1KeyKindHandleC S b).eval
      (.cons (embedVal gdh1KeyActiveStateTy (((pa, sm), sigB), rp?, cnt), sh)
        (.cons ((pqKeyIndCodec S).qenc (.acceptNoOPK k j l hdr)) .nil)) =
      (fun r =>
        (embedVal keyIndRespTy r.1,
          (embedVal gdh1KeyActiveStateTy r.2.1,
            ((embedVal fgSessCtrTy r.2.2).1,
              ((embedVal fgSessCtrTy r.2.2).2, sh.2.2))))) <$>
        (gdhKindAcceptNoOpkSessLeg S (keyIndKFuelsOfBudget S b)).eval
          (.cons ((((pa, sm), sigB), rp?, cnt), projVal fgSessCtrTy (sh.1, sh.2.1))
            (.cons (k.val, (j.val, (l.val, _root_.SignalPqxdh.LegacyCosted.hdrV hdr))) .nil)) := by
    unfold gdh1KeyKindHandleC; dsimp only; rw [dispatchKeyIndQ_eval]
    exact liftSigDdhSessArm_eval_fg S _ _
      (gdhKindAcceptNoOpkSessLeg_unsup_fg S (keyIndKFuelsOfBudget S b))
      _ (((pa, sm), sigB), rp?, cnt) sh _
      (k.val, (j.val, (l.val, _root_.SignalPqxdh.LegacyCosted.hdrV hdr)))
      (accPayToNatE_hdrV_fg S.N_no_opk S k j l hdr _ _)
  rw [hK, forgetGdh1KeyActiveK_embedVal_fg, gdhActiveAtomic_handle_eval_fg]
  have hFgSc : embedVal fgSessCtrTy (projVal fgSessCtrTy (sh.1, sh.2.1)) = (sh.1, sh.2.1) :=
    embedVal_projVal fgSessCtrTy (sh.1, sh.2.1)
  have ht0 : keyIndSimPred S 0 (.acceptNoOPK k j l hdr) = true := by
    simp [keyIndSimPred_zero_iff_kind, keyIndQueryKind]
  simp only [gdhKindAcceptNoOpkSessLeg, gdh1KeyActiveHandle, callGdhActiveHandle, gdhHandle2,
    wrapSim2, fixGdhLeg_fg, keyIndCodec, _root_.SignalPqxdh.LegacyCosted.keyIndQenc,
    renameComp_eval, pullEnv_twoVarRen, liftGdhComp_eval,
    letV, bindV, caseSumV, Comp.eval, Expr.eval, v, Ext.wk, Env.get,
    pure_bind, liftGdhToSign_bind, liftGdhToSign_pure, map_eq_bind_pure_comp,
    Function.comp_apply, bind_assoc]
  apply liftGdh_bind_sim_fg (fun r => (r.1, r.2.1))
  · apply acceptNoOpkGdhShadowB_sim (c := c) (t := .acceptNoOPK k j l hdr) (fgShFull := sh)
    · rfl
    · rfl
    · rfl
    · rfl
    · exact ht0
    · simp [keyIndSimPred_one_iff_kind, keyIndQueryKind]
    · exact hB
    · exact hRoom
    · simp only [Expr.eval, v, Ext.wk, Env.get, hFgSc]; exact hInv.sim_inv
  · intro _; rfl
  · intro _ h
    exact ⟨h, by simp only [bumpPred, ht0, ↓reduceIte]; exact Nat.le_succ_of_le hInv.sendOpkCnt_le⟩

end FgProgSessWrappers

end

end Computational.Proofs.SignalPqxdh.Security.ReductionDsl.KindSplit.KeyIndGapDhKSimSess
