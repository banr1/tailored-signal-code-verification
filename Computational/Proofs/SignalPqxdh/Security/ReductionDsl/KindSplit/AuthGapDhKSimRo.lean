/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Computational.Proofs.SignalPqxdh.Security.ReductionDsl.KindSplit.AuthGapDhKSimBase -- proof-setup: allow-public-import
import Computational.Proofs.ReductionDsl.StepSim
import Computational.Proofs.SignalPqxdh.AtomicLift
import Computational.Proofs.SignalPqxdh.Security.ReductionDsl.AuthHandshake
import Computational.Proofs.SignalPqxdh.Security.ReductionDsl.AuthHandshakeGapDh
import Computational.Proofs.SignalPqxdh.Security.ReductionDsl.Auth1KeyGapDh
import Computational.Proofs.SignalPqxdh.Security.ReductionDsl.AuthGapDhStepBase
import Computational.Proofs.SignalPqxdh.Security.ReductionDsl.KeyInd1KeyGapDhEvalEq
import Computational.Proofs.SignalPqxdh.Security.ReductionDsl.SplitRo.AvlRoTableDefs
import Computational.Proofs.SignalPqxdh.Security.ReductionDsl.SplitRo.AvlRoTableSpec
import Computational.Proofs.SignalPqxdh.Security.ReductionDsl.SplitRo.AvlRoCacheRefine
import Computational.Proofs.SignalPqxdh.Security.ReductionDsl.KindSplit.AuthCoreK
import Computational.Proofs.SignalPqxdh.Security.ReductionDsl.KindSplit.AuthCoreKSimBase
import Computational.Proofs.SignalPqxdh.Security.ReductionDsl.KindSplit.AuthGapDhK
import Computational.Proofs.SignalPqxdh.Security.ReductionDsl.KindSplit.AuthGapDhKSimRoRoot

/-!
# `.roQuery` Arm Simulation for `Auth` Gap-DH and EUF-CMA

**Checked by Lean.** Proves `fgArmSim_roQuery`, relating `fgCoreArm_roQuery` to `legacyCoreArmEval`
on `.roQuery` inputs while preserving `FgSimShadowInv`.
-/

public section

set_option autoImplicit false

namespace Computational.Proofs.SignalPqxdh.Security.ReductionDsl.KindSplit.AuthGapDhKSimRo

open OracleSpec OracleComp
open _root_.ReductionDsl (Ty Var Expr Comp Env PB pqAtomicSig pqAtomicOps drKeyT findML)
open _root_.Computational.Proofs.ReductionDsl.StepSim (bumpPred)
open _root_.Computational.Proofs.SignalPqxdh.AtomicLift
  (embedTy embedVal projVal embedVal_projVal embedEnv exprRename exprRename_eval
   compRename compRename_eval mapExpr mapExpr_eval mapComp mapComp_eval
   comp_queries_zero_of_zero tlAuthSigDdh)
open _root_.SignalPqxdh (Setup QueryBudget AuthQuery Bytes F_X25519)
open _root_.SignalPqxdh.LegacyCosted (pqSig pqxdhOps pqSigAndDdhIface pqGapDhIface B)
open _root_.SignalPqxdh.Costed (authCodec)
open _root_.SignalPqxdh.Security.ReductionDsl (fgPosTy fgPatchEntryTy drKeyTy authQueryTy authRespTy)
open _root_.SignalPqxdh.Security.ReductionDsl.AuthHs
  (Ext v letV bindV caseOptV caseSumV findMV
   fgSimTy patchKeyTy a1gParams2Ty a1gPre2C fgStep2C
   fsRootL fsUpd fsMk fsBase fsL fsRaw fsLog fsResp fsPows
   pkP1 pkP2 pkP3 pkP4 pkSs feP1 feP2 feP3 feP4 feSs feDk aDrKey slice32
   mkSecretPosC mkSecretPosC_eval entryMatchesC entryMatchesC_eval patchC fgRoC)
open _root_.SignalPqxdh.Security.ReductionDsl.KeyInd1KeyGapDh
  (liftGdhComp liftGdhComp_eval liftGdhToSign_bind liftGdhToSign_pure)
open _root_.Computational.Proofs.SignalPqxdh.Security.ReductionDsl.SplitRo.AvlRoTableDefs
  (aop avlSearchB192C avlInsertAtPathC)
open _root_.Computational.Proofs.SignalPqxdh.Security.ReductionDsl.SplitRo.AvlRoCacheRefine
  (TaggedEntry ShadowRelB192 RoCacheRelB192 roEntriesOf shadowScanMinIdx findML_take_eq_shadowScanMinIdx)
open _root_.Computational.Proofs.SignalPqxdh.Security.ReductionDsl.KindSplit.AuthCoreK
  (AuthKindFuels wk1 wk2 liftExpr1 liftExpr2 aDrKeyAtomicE)
open _root_.Computational.Proofs.SignalPqxdh.Security.ReductionDsl.KindSplit.AuthCoreKSimBase
  (authSimPred authSimBounds AuthCounterInv)
open _root_.Computational.Proofs.SignalPqxdh.Security.ReductionDsl.KindSplit.AuthGapDhK
  (fgAuthShadowAuxTy seqFgEntryTy
   auxFgSess auxFgCtr auxFgRoAvl auxFgRootSess auxFgRootCtr auxFgRootRoAvl
   auxRawAvl auxFgSessE auxFgCtrE auxFgRoAvlE auxFgRootSessE auxFgRootCtrE auxFgRootRoAvlE
   auxRawAvlE fgAuxMkE wk0 liftCs0 liftCs1 liftGdh0 liftGdh1
   roParsedPrePosC fgSessScanC simPrependLogE simPrependRawAndLogE simPrependFgAndLogE
   fgCoreArm_roQuery)
open _root_.Computational.Proofs.SignalPqxdh.Security.ReductionDsl.KindSplit.AuthGapDhKSimBase
  (ValidParsedRoFgEntry FgTableShadow FgSimShadowInv AuthSigDdhSpec
   legacyCoreArmComp legacyCoreArmEval FgArmSim armEval_roQuery entryMatchesC_atomic_on_parsedRo)
open _root_.Computational.Proofs.SignalPqxdh.Security.ReductionDsl.KindSplit.AuthGapDhKSimRoRoot
  (liftGdh0_eval liftGdh1_eval mkSecretPosAtom mkSecretPosAtom_support)

private theorem bump_ro_counts {S : Setup} (c : Fin 4 → ℕ) (sec : Bytes) :
    let t := AuthQuery.roQuery (S := S) sec
    bumpPred (authSimPred S) c t 0 = c 0 ∧
    bumpPred (authSimPred S) c t 1 = c 1 + 1 ∧
    bumpPred (authSimPred S) c t 2 = c 2 ∧
    bumpPred (authSimPred S) c t 3 = c 3 + 1 := by
  have h0 : ¬ authSimPred S 0 (.roQuery sec) := by
    simp [authSimPred, SignalPqxdh.isAuthOnlineQuery]
  have h1 : authSimPred S 1 (.roQuery sec) := by
    simp [authSimPred, SignalPqxdh.isAuthRoQuery]
  have h2 : ¬ authSimPred S 2 (.roQuery sec) := by
    simp [authSimPred, SignalPqxdh.isAuthRoRootQuery]
  have h3 : authSimPred S 3 (.roQuery sec) := trivial
  simp [bumpPred, h0, h1, h2, h3]

private theorem ro_room_arith {S : Setup} {b : QueryBudget} {c : Fin 4 → ℕ}
    {sec : Bytes} (hCounter : AuthCounterInv b c)
    (hroom : ∀ j, authSimPred S j (.roQuery sec) → c j + 1 ≤ authSimBounds b j) :
    let F := AuthKindFuels.ofBudget S b
    c 0 ≤ F.K_on ∧
    c 0 + (c 1 + 1) ≤ b.q_total ∧
    c 1 + 1 ≤ b.q_total ∧
    c 0 + (c 1 + 1) ≤ F.K_cap ∧
    c 1 + 1 ≤ F.K_cap := by
  have hRo : authSimPred S 1 (.roQuery sec) := by
    simp [authSimPred, SignalPqxdh.isAuthRoQuery]
  have hStep := hCounter.ro_step_bounds hRo hroom
  have hOn := hCounter.on_le
  dsimp only [AuthKindFuels.ofBudget] at hStep ⊢
  omega

private def simConsLogVal (sim : (embedTy fgSimTy).denote) (sec : Bytes) :
    (embedTy fgSimTy).denote :=
  (sim.1, (sim.2.1, (sim.2.2.1, (sim.2.2.2.1, (sec :: sim.2.2.2.2.1, sim.2.2.2.2.2)))))

private theorem ro_inv_log_cons {S : Setup} {b : QueryBudget} {c : Fin 4 → ℕ}
    {sim : (embedTy fgSimTy).denote} {aux : fgAuthShadowAuxTy.denote} {sec : Bytes}
    (hroom : ∀ j, authSimPred S j (.roQuery sec) → c j + 1 ≤ authSimBounds b j)
    (hInv : FgSimShadowInv S b c sim aux) :
    FgSimShadowInv S b (bumpPred (authSimPred S) c (.roQuery sec))
      (simConsLogVal sim sec) aux := by
  obtain ⟨hb0, hb1, hb2, _⟩ := bump_ro_counts (S := S) c sec
  refine ⟨hInv.counter_inv.bump (.roQuery sec) hroom,
    hb0.symm ▸ hInv.base_online,
    hb0.symm ▸ hInv.pows_len,
    hb0.symm ▸ hInv.resp_len,
    ?_, ?_,
    hb0.symm ▸ hb2.symm ▸ hInv.root_shadow,
    hInv.raw_rel,
    ?_⟩
  · rw [hb1]
    have hLog := hInv.log_len
    simp only [simConsLogVal, List.length_cons]
    omega
  · rw [hb0, hb1]
    obtain ⟨ft, hRel, hSess, hRo, hLen, hValid⟩ := hInv.fg_shadow
    exact ⟨ft, hRel.mono_cap (by omega), hSess, by omega, by omega, hValid⟩
  · rw [hb1]
    have hRaw := hInv.raw_len
    simp only [simConsLogVal]
    omega

private def sampleDrKeyAtom :
    OracleComp AuthSigDdhSpec (drKeyT (ℓ := 0) (Pt := Empty)).denote :=
  (mapComp tlAuthSigDdh (liftGdhComp (Γ := []) .sampleDrKey96C)).eval .nil

private def aDrKeyAtomVal (dk : (drKeyT (ℓ := 0) (Pt := Empty)).denote) :
    (embedTy authRespTy).denote :=
  (aDrKeyAtomicE (Γ := [drKeyT (ℓ := 0) (Pt := Empty)]) (.var .zero)).eval (.cons dk .nil)

private theorem aDrKeyAtomicE_eval {Γ : List (Ty pqAtomicSig)}
    (dkE : Expr pqAtomicOps Γ (drKeyT (ℓ := 0) (Pt := Empty))) (ρ : Env Γ) :
    (aDrKeyAtomicE dkE).eval ρ = aDrKeyAtomVal (dkE.eval ρ) := by
  simp only [aDrKeyAtomicE, aDrKeyAtomVal, liftExpr1, Expr.eval]
  exact exprRename_eval _ wk1 (.cons (dkE.eval ρ) .nil) (.cons (dkE.eval ρ) ρ)
    (fun v => by cases v with | zero => rfl | succ v => nomatch v)

private def fgPatchEntryOfPkDk (pk : (embedTy patchKeyTy).denote)
    (dk : (drKeyT (ℓ := 0) (Pt := Empty)).denote) : (embedTy fgPatchEntryTy).denote :=
  (pk.1, (pk.2.1, (pk.2.2.1, (pk.2.2.2.1, (pk.2.2.2.2, dk)))))

private def simConsRawAndLogVal (sim : (embedTy fgSimTy).denote) (sec : Bytes)
    (dk : (drKeyT (ℓ := 0) (Pt := Empty)).denote) : (embedTy fgSimTy).denote :=
  (sim.1, (sim.2.1, (sim.2.2.1, ((sec, dk) :: sim.2.2.2.1,
    (sec :: sim.2.2.2.2.1, sim.2.2.2.2.2)))))

private def simConsFgAndLogVal (sim : (embedTy fgSimTy).denote)
    (pk : (embedTy patchKeyTy).denote) (sec : Bytes)
    (dk : (drKeyT (ℓ := 0) (Pt := Empty)).denote) : (embedTy fgSimTy).denote :=
  (sim.1, (fgPatchEntryOfPkDk pk dk :: sim.2.1, (sim.2.2.1, (sim.2.2.2.1,
    (sec :: sim.2.2.2.2.1, sim.2.2.2.2.2)))))

private theorem simPrependLogE_eval {Γ : List (Ty pqAtomicSig)}
    (simE : Expr pqAtomicOps Γ (embedTy fgSimTy))
    (secE : Expr pqAtomicOps Γ (PB 192)) (ρ : Env Γ) :
    (simPrependLogE simE secE).eval ρ = simConsLogVal (simE.eval ρ) (secE.eval ρ) := by
  simp only [simPrependLogE, liftExpr2, Expr.eval]
  rw [exprRename_eval _ Var.succ ρ (.cons (secE.eval ρ) ρ) (fun _ => rfl)]
  rw [exprRename_eval _ wk2 (.cons (simE.eval ρ) (.cons (secE.eval ρ) .nil))
    (.cons (simE.eval ρ) (.cons (secE.eval ρ) ρ))
    (fun v => by
      cases v with
      | zero => rfl
      | succ v => cases v with
        | zero => rfl
        | succ v => nomatch v)]
  rfl

private theorem simPrependRawAndLogE_eval {Γ : List (Ty pqAtomicSig)}
    (simE : Expr pqAtomicOps Γ (embedTy fgSimTy))
    (secDkE : Expr pqAtomicOps Γ (.prod (PB 192) (drKeyT (ℓ := 0) (Pt := Empty))))
    (ρ : Env Γ) :
    (simPrependRawAndLogE simE secDkE).eval ρ =
      simConsRawAndLogVal (simE.eval ρ) (secDkE.eval ρ).1 (secDkE.eval ρ).2 := by
  simp only [simPrependRawAndLogE, liftExpr2, Expr.eval]
  rw [exprRename_eval _ Var.succ ρ (.cons (secDkE.eval ρ) ρ) (fun _ => rfl)]
  rw [exprRename_eval _ wk2 (.cons (simE.eval ρ) (.cons (secDkE.eval ρ) .nil))
    (.cons (simE.eval ρ) (.cons (secDkE.eval ρ) ρ))
    (fun v => by
      cases v with
      | zero => rfl
      | succ v => cases v with
        | zero => rfl
        | succ v => nomatch v)]
  rfl

private theorem simPrependFgAndLogE_eval {Γ : List (Ty pqAtomicSig)}
    (simE : Expr pqAtomicOps Γ (embedTy fgSimTy))
    (pkSecDkE : Expr pqAtomicOps Γ
      (.prod (embedTy patchKeyTy) (.prod (PB 192) (drKeyT (ℓ := 0) (Pt := Empty)))))
    (ρ : Env Γ) :
    (simPrependFgAndLogE simE pkSecDkE).eval ρ =
      simConsFgAndLogVal (simE.eval ρ) (pkSecDkE.eval ρ).1
        (pkSecDkE.eval ρ).2.1 (pkSecDkE.eval ρ).2.2 := by
  simp only [simPrependFgAndLogE, liftExpr2, Expr.eval]
  rw [exprRename_eval _ Var.succ ρ (.cons (pkSecDkE.eval ρ) ρ) (fun _ => rfl)]
  rw [exprRename_eval _ wk2 (.cons (simE.eval ρ) (.cons (pkSecDkE.eval ρ) .nil))
    (.cons (simE.eval ρ) (.cons (pkSecDkE.eval ρ) ρ))
    (fun v => by
      cases v with
      | zero => rfl
      | succ v => cases v with
        | zero => rfl
        | succ v => nomatch v)]
  rfl

private def roParsedGuardVal (sec : Bytes) : Bool :=
  (List.take 32 sec == List.take 32 F_X25519) &&
    (if decide (sec.length = 160) then true else decide (sec.length = 192))

private def roParsedPrePosAtom (sec : Bytes) :
    OracleComp AuthSigDdhSpec (Option (embedTy patchKeyTy).denote) :=
  (mapComp tlAuthSigDdh (liftGdhComp roParsedPrePosC)).eval (.cons (t := PB 192) sec .nil)

private theorem roParsedPrePosAtom_eq (sec : Bytes) :
    roParsedPrePosAtom sec =
      if roParsedGuardVal sec = true then
        mkSecretPosAtom (List.take 32 (List.drop 32 sec)) >>= fun p1 =>
        mkSecretPosAtom (List.take 32 (List.drop 64 sec)) >>= fun p2 =>
        mkSecretPosAtom (List.take 32 (List.drop 96 sec)) >>= fun p3 =>
        (if decide (sec.length = 192) = true then
          mkSecretPosAtom (List.take 32 (List.drop 128 sec)) >>= fun p => pure (some p)
         else pure none) >>= fun p4 =>
        pure (some (p1, (p2, (p3, (p4,
          if decide (sec.length = 192) = true then
            List.take 32 (List.drop 160 sec)
          else List.take 32 (List.drop 128 sec))))))
      else pure none := by
  simp only [roParsedPrePosAtom, roParsedPrePosC, roParsedGuardVal,
    mkSecretPosAtom, mkSecretPosC, slice32,
    SignalPqxdh.Security.ReductionDsl.AuthHs.natEq,
    Expr.litBytes, Expr.bytesTakeK, Expr.bytesDrop, Expr.bytesLen, Expr.bytesBeq,
    Comp.iteC, letV, bindV, v, Comp.letC, Var.vs,
    SignalPqxdh.Security.ReductionDsl.AuthHs.Ext.wk, Var.vz, AtomicLift.embedVar,
    liftGdhComp, mapComp, mapExpr, AtomicLift.mapOpExpr,
    Comp.eval, Expr.eval, pqAtomicOps, ReductionDsl.AtomicPureOp.eval, Env.get,
    pure_bind, bind_assoc]
  rfl

private theorem roParsedPrePosAtom_some_support {sec : Bytes}
    {pk : (embedTy patchKeyTy).denote}
    (hpk : some pk ∈ support (roParsedPrePosAtom sec)) :
    ∀ (dk : (drKeyT (ℓ := 0) (Pt := Empty)).denote),
      ValidParsedRoFgEntry sec (fgPatchEntryOfPkDk pk dk) := by
  intro dk
  rw [roParsedPrePosAtom_eq] at hpk
  by_cases hG : roParsedGuardVal sec = true
  · simp only [hG, ↓reduceIte, mem_support_bind_iff, mem_support_pure_iff,
      Option.some.injEq] at hpk
    have hTakeF : List.take 32 F_X25519 = F_X25519 := by
      simp [F_X25519]
    have hG' := hG
    simp only [roParsedGuardVal, hTakeF, Bool.and_eq_true, beq_iff_eq] at hG'
    obtain ⟨hPfx, hLenBool⟩ := hG'
    have hLen : sec.length = 160 ∨ sec.length = 192 := by
      split_ifs at hLenBool with h160
      · exact Or.inl (of_decide_eq_true h160)
      · exact Or.inr (of_decide_eq_true hLenBool)
    obtain ⟨p1, hp1, p2, hp2, p3, hp3, p4, hp4, hpkEq⟩ := hpk
    subst hpkEq
    obtain ⟨c1, rfl⟩ := mkSecretPosAtom_support hp1
    obtain ⟨c2, rfl⟩ := mkSecretPosAtom_support hp2
    obtain ⟨c3, rfl⟩ := mkSecretPosAtom_support hp3
    refine ⟨hPfx, hLen, ⟨c1, rfl⟩, ⟨c2, rfl⟩, ⟨c3, rfl⟩, ?_⟩
    by_cases h192 : decide (sec.length = 192) = true
    · simp only [h192, ↓reduceIte, mem_support_bind_iff, mem_support_pure_iff] at hp4
      obtain ⟨p, hp, rfl⟩ := hp4
      obtain ⟨c4, rfl⟩ := mkSecretPosAtom_support hp
      refine Or.inl ⟨of_decide_eq_true h192, ⟨c4, rfl⟩, ?_⟩
      simp [fgPatchEntryOfPkDk, h192]
    · simp only [h192, Bool.false_eq_true, ↓reduceIte, mem_support_pure_iff] at hp4
      subst hp4
      rcases hLen with h160 | h192'
      · refine Or.inr ⟨h160, ?_, ?_⟩
        · rfl
        · simp [fgPatchEntryOfPkDk, h192]
      · exact absurd (decide_eq_true h192') h192
  · simp only [hG, Bool.false_eq_true, ↓reduceIte, mem_support_pure_iff] at hpk
    nomatch hpk

private def fgMatchAtom (pk : (embedTy patchKeyTy).denote)
    (e : (embedTy fgPatchEntryTy).denote) : OracleComp AuthSigDdhSpec Bool :=
  (mapComp tlAuthSigDdh
    (liftGdhComp (Γ := [fgPatchEntryTy, patchKeyTy])
      (entryMatchesC (Δ := [fgPatchEntryTy, patchKeyTy])
        (.succ .zero : Var [fgPatchEntryTy, patchKeyTy] patchKeyTy)
        (.zero : Var [fgPatchEntryTy, patchKeyTy] fgPatchEntryTy)))).eval
    (.cons (t := embedTy fgPatchEntryTy) e (.cons (t := embedTy patchKeyTy) pk .nil))

private theorem fgMatchAtom_on_parsedRo {sec sec' : Bytes}
    {pk : (embedTy patchKeyTy).denote}
    {dk0 : (drKeyT (ℓ := 0) (Pt := Empty)).denote}
    {e : (embedTy fgPatchEntryTy).denote}
    (hValidPk : ValidParsedRoFgEntry sec (fgPatchEntryOfPkDk pk dk0))
    (hEntry : ValidParsedRoFgEntry sec' e) :
    fgMatchAtom pk e = pure (sec' == sec) := by
  obtain ⟨c1, hc1⟩ := hValidPk.p1_inl
  obtain ⟨c2, hc2⟩ := hValidPk.p2_inl
  obtain ⟨c3, hc3⟩ := hValidPk.p3_inl
  have hpk : pk = embedVal patchKeyTy (projVal patchKeyTy pk) :=
    (embedVal_projVal patchKeyTy pk).symm
  unfold fgMatchAtom
  conv_lhs => rw [hpk]
  apply entryMatchesC_atomic_on_parsedRo (Δ := [patchKeyTy])
    (.succ .zero : Var [fgPatchEntryTy, patchKeyTy] patchKeyTy)
    (.cons (projVal patchKeyTy pk) .nil) hValidPk.prefix_eq
  · dsimp only [Env.get, SignalPqxdh.Security.ReductionDsl.AuthHs.Ext.wk, projVal]
    rcases pk with ⟨p1, p2, p3, p4, ss⟩
    dsimp only [fgPatchEntryOfPkDk] at hc1
    subst hc1; rfl
  · dsimp only [Env.get, SignalPqxdh.Security.ReductionDsl.AuthHs.Ext.wk, projVal]
    rcases pk with ⟨p1, p2, p3, p4, ss⟩
    dsimp only [fgPatchEntryOfPkDk] at hc2
    subst hc2; rfl
  · dsimp only [Env.get, SignalPqxdh.Security.ReductionDsl.AuthHs.Ext.wk, projVal]
    rcases pk with ⟨p1, p2, p3, p4, ss⟩
    dsimp only [fgPatchEntryOfPkDk] at hc3
    subst hc3; rfl
  · dsimp only [Env.get, SignalPqxdh.Security.ReductionDsl.AuthHs.Ext.wk, projVal]
    rcases pk with ⟨p1, p2, p3, p4, ss⟩
    rcases hValidPk.p4_ss_shape with ⟨h192, ⟨c4, hc4⟩, hss⟩ | ⟨h160, hc4, hss⟩
    · dsimp only [fgPatchEntryOfPkDk] at hc4 hss
      subst hc4; subst hss
      exact Or.inl ⟨h192, ⟨c4, rfl⟩, rfl⟩
    · dsimp only [fgPatchEntryOfPkDk] at hc4 hss
      subst hc4; subst hss
      exact Or.inr ⟨h160, rfl, rfl⟩
  · exact hEntry

private def projEnv : ∀ {Γ : List (Ty pqSig)}, Env (AtomicLift.embedCtx Γ) → Env Γ
  | [], .nil => .nil
  | t :: _, .cons x ρ => .cons (projVal t x) (projEnv ρ)

private theorem embedEnv_projEnv : ∀ {Γ : List (Ty pqSig)} (ρ : Env (AtomicLift.embedCtx Γ)),
    embedEnv (projEnv ρ) = ρ
  | [], .nil => rfl
  | _ :: _, .cons _ ρ => by
    simp only [projEnv, embedEnv, embedVal_projVal, embedEnv_projEnv]

private theorem entryMatchesC_atomic_eval
    {Γ₁ Δ : List (Ty pqSig)} (k : Var Γ₁ patchKeyTy) [h₁ : Ext Γ₁ (fgPatchEntryTy :: Δ)]
    (e : (embedTy fgPatchEntryTy).denote) (ρ : Env (AtomicLift.embedCtx Δ))
    (pk : (embedTy patchKeyTy).denote)
    (hk : Env.get (.cons (projVal fgPatchEntryTy e) (projEnv ρ)) (h₁.wk k) =
      projVal patchKeyTy pk) :
    (mapComp tlAuthSigDdh
      (liftGdhComp (entryMatchesC (Δ := fgPatchEntryTy :: Δ) k
        (.zero : Var (fgPatchEntryTy :: Δ) fgPatchEntryTy)))).eval (.cons e ρ) =
      fgMatchAtom pk e := by
  have h1 : Env.cons e ρ = embedEnv (.cons (projVal fgPatchEntryTy e) (projEnv ρ)) := by
    simp only [embedEnv, embedVal_projVal, embedEnv_projEnv]
  have h2 : Env.cons (t := embedTy fgPatchEntryTy) e (.cons (t := embedTy patchKeyTy) pk .nil) =
      embedEnv (.cons (projVal fgPatchEntryTy e) (.cons (projVal patchKeyTy pk) .nil)) := by
    simp only [embedEnv, embedVal_projVal]
  unfold fgMatchAtom
  rw [h1, h2,
    mapComp_eval tlAuthSigDdh _ (comp_queries_zero_of_zero (fun _ => rfl) _),
    mapComp_eval tlAuthSigDdh _ (comp_queries_zero_of_zero (fun _ => rfl) _)]
  simp only [liftGdhComp_eval, entryMatchesC_eval, hk]
  rfl

private theorem fgSessScan_atomic_eval (K_on : ℕ) (pk : (embedTy patchKeyTy).denote)
    (minIdx : ℕ) (sessL : (embedTy (.list seqFgEntryTy)).denote) :
    (mapComp tlAuthSigDdh (liftGdhComp (fgSessScanC K_on))).eval
      (.cons (t := embedTy (.prod patchKeyTy (.prod .nat (.list seqFgEntryTy))))
        (pk, (minIdx, sessL)) .nil) =
      findML
        (fun ie => if decide (minIdx ≤ ie.1) then fgMatchAtom pk ie.2 else pure false)
        (sessL.take K_on) := by
  simp only [fgSessScanC, letV, findMV, v, Comp.letC, Comp.findBoundedM, Var.vs,
    SignalPqxdh.Security.ReductionDsl.AuthHs.Ext.wk, Var.vz, AtomicLift.embedVar,
    liftGdhComp, mapComp, mapExpr, Comp.eval, Expr.eval, Env.get, pure_bind]
  congr 1
  funext ie
  by_cases h : (ie.1 : ℕ) < minIdx
  · have hle : ¬ minIdx ≤ (ie.1 : ℕ) := Nat.not_le_of_lt h
    simp [h, hle]
    rfl
  · have hle : minIdx ≤ (ie.1 : ℕ) := Nat.le_of_not_lt h
    simp only [h, hle, decide_false, Bool.false_eq_true, ↓reduceIte, decide_true]
    exact entryMatchesC_atomic_eval
      (Δ := [seqFgEntryTy, .nat, patchKeyTy, .prod patchKeyTy (.prod .nat (.list seqFgEntryTy))])
      (.zero : Var [patchKeyTy, .prod patchKeyTy (.prod .nat (.list seqFgEntryTy))] patchKeyTy)
      ie.2
      (.cons (t := embedTy seqFgEntryTy) ie
        (.cons (t := .nat) minIdx
          (.cons (t := embedTy patchKeyTy) pk
            (.cons (t := embedTy (.prod patchKeyTy (.prod .nat (.list seqFgEntryTy))))
              (pk, (minIdx, sessL)) .nil))))
      pk rfl

private theorem bind_ite_bool_eq {m : Type → Type} [Bind m] {α β : Type} {c c' : Bool}
    (hc : c = c') (t e : m α) (k : α → m β) :
    ((if c = true then t else e) >>= k) = ((if c' = true then t else e) >>= k) := by
  subst hc; rfl

private theorem bind_congr_eq {m : Type → Type} [Bind m] {α β : Type}
    {x x' : m α} {k k' : α → m β} (hx : x = x') (hk : ∀ a, k a = k' a) :
    (x >>= k) = (x' >>= k') := by
  cases hx; exact congrArg (Bind.bind x) (funext hk)

private theorem findML_congr {m : Type → Type} [Monad m] {α : Type}
    {p1 p2 : α → m Bool} {l1 l2 : List α} (hp : ∀ x, p1 x = p2 x) (hl : l1 = l2) :
    findML p1 l1 = findML p2 l2 := by
  cases hl; congr 1; funext x; exact hp x

private theorem mkSecretPosC_atomic_eval {Δ : List (Ty pqSig)} (e : Expr pqxdhOps Δ (B 32))
    (ρ : Env (AtomicLift.embedCtx Δ)) (b32 : Bytes)
    (hb : (mapExpr e).eval ρ = b32) :
    (mapComp tlAuthSigDdh (liftGdhComp (Γ := Δ) (mkSecretPosC e))).eval ρ =
      mkSecretPosAtom b32 := by
  subst hb
  simp only [mkSecretPosAtom, mkSecretPosC, letV, bindV, v, Comp.letC, Var.vs,
    SignalPqxdh.Security.ReductionDsl.AuthHs.Ext.wk, Var.vz, AtomicLift.embedVar,
    liftGdhComp, mapComp, mapExpr, Comp.eval, Expr.eval, Env.get, pure_bind]
  rfl

private theorem sampleDrKey96C_atomic_eval {Δ : List (Ty pqSig)}
    (ρ : Env (AtomicLift.embedCtx Δ)) :
    (mapComp tlAuthSigDdh (liftGdhComp (Γ := Δ) Comp.sampleDrKey96C)).eval ρ =
      sampleDrKeyAtom :=
  rfl

private theorem fgStepP4_map_bind_eq (b : QueryBudget) (sim : (embedTy fgSimTy).denote)
    (sigB : ℕ) (sec : Bytes)
    (p1 p2 p3 : (embedTy fgPosTy).denote)
    (p4 : Option (embedTy fgPosTy).denote) (ss : Bytes) :
    (let pk : (embedTy patchKeyTy).denote := (p1, (p2, (p3, (p4, ss))))
     (Option.map (fun e : (embedTy fgPatchEntryTy).denote => e.2.2.2.2.2) <$>
       findML (fgMatchAtom pk) (sim.2.1.take b.q_total)) >>= fun hit? =>
       match hit? with
       | some dk => pure (aDrKeyAtomVal dk, (simConsLogVal sim sec, sigB))
       | none => sampleDrKeyAtom >>= fun dk =>
           pure (aDrKeyAtomVal dk, (simConsFgAndLogVal sim pk sec dk, sigB))) =
    (let pk : (embedTy patchKeyTy).denote := (p1, (p2, (p3, (p4, ss))))
     findML (fgMatchAtom pk) (sim.2.1.take b.q_total) >>= fun f =>
       match f with
       | some e => pure (aDrKeyAtomVal e.2.2.2.2.2, (simConsLogVal sim sec, sigB))
       | none => sampleDrKeyAtom >>= fun dk =>
           pure (aDrKeyAtomVal dk, (simConsFgAndLogVal sim pk sec dk, sigB))) := by
  simp only [bind_map_left]
  refine congrArg (Bind.bind _) (funext fun f => ?_)
  cases f <;> simp

set_option maxHeartbeats 400000 in
private theorem legacyCoreArmEval_roQuery_eq (S : Setup) (b : QueryBudget)
    (pa : (embedTy a1gParams2Ty).denote) (sim : (embedTy fgSimTy).denote)
    (sigB : ℕ) (sec : Bytes) :
    legacyCoreArmEval S b pa sim sigB (.roQuery sec) =
      (roParsedPrePosAtom sec >>= fun pk? =>
        match pk? with
        | none =>
          match ((sim.2.2.2.1.take b.q_total).find? (fun p => p.1 == sec)).map Prod.snd with
          | some dk => pure (aDrKeyAtomVal dk, (simConsLogVal sim sec, sigB))
          | none =>
            sampleDrKeyAtom >>= fun dk =>
              pure (aDrKeyAtomVal dk, (simConsRawAndLogVal sim sec dk, sigB))
        | some pk =>
          (Option.map (fun e : (embedTy fgPatchEntryTy).denote => e.2.2.2.2.2) <$>
            findML (fgMatchAtom pk) (sim.2.1.take b.q_total)) >>= fun hit? =>
            match hit? with
            | some dk => pure (aDrKeyAtomVal dk, (simConsLogVal sim sec, sigB))
            | none =>
              sampleDrKeyAtom >>= fun dk =>
                pure (aDrKeyAtomVal dk, (simConsFgAndLogVal sim pk sec dk, sigB))) := by
  rw [roParsedPrePosAtom_eq]
  simp only [legacyCoreArmEval, legacyCoreArmComp, a1gPre2C, fgStep2C, fgRoC, patchC,
    Comp.iteC, letV, bindV, caseSumV, caseOptV, findMV, v,
    Comp.letC, Comp.findBoundedM, Comp.caseOptC, Var.vs,
    fsUpd, fsMk, fsBase, fsL, fsRootL, fsRaw, fsLog, fsResp, fsPows,
    pkP1, pkP2, pkP3, pkP4, pkSs, aDrKey, slice32,
    SignalPqxdh.Security.ReductionDsl.AuthHs.natEq,
    SignalPqxdh.Security.ReductionDsl.AuthHs.eFind,
    Expr.boolAnd, Expr.boolOr, Expr.bytesBeq, Expr.bytesTakeK, Expr.bytesDrop, Expr.bytesLen,
    Expr.litBytes, Expr.litNat, Expr.listCons, Expr.findBounded,
    SignalPqxdh.Security.ReductionDsl.AuthHs.Ext.wk, Var.vz, AtomicLift.embedVar,
    liftGdhComp, mapComp, mapExpr, AtomicLift.mapOpExpr, Comp.eval, Expr.eval, Env.get,
    authCodec, SignalPqxdh.Costed.authQenc, pure_bind, bind_assoc]
  refine Eq.trans (bind_ite_bool_eq (c' := roParsedGuardVal sec) rfl _ _ _) ?_
  by_cases hG : roParsedGuardVal sec = true
  · simp only [hG, ↓reduceIte, bind_assoc, pure_bind]
    refine bind_congr_eq (mkSecretPosC_atomic_eval _ _ (List.take 32 (List.drop 32 sec)) rfl) fun p1 => ?_
    refine bind_congr_eq (mkSecretPosC_atomic_eval _ _ (List.take 32 (List.drop 64 sec)) rfl) fun p2 => ?_
    refine bind_congr_eq (mkSecretPosC_atomic_eval _ _ (List.take 32 (List.drop 96 sec)) rfl) fun p3 => ?_
    refine Eq.trans (bind_ite_bool_eq (c' := decide (sec.length = 192)) rfl _ _ _) ?_
    by_cases h192 : decide (sec.length = 192) = true
    · simp only [h192, ↓reduceIte, bind_assoc, pure_bind]
      refine bind_congr_eq (mkSecretPosC_atomic_eval _ _ (List.take 32 (List.drop 128 sec)) rfl) fun p4v => ?_
      rw [fgStepP4_map_bind_eq b sim sigB sec p1 p2 p3 (some p4v) (List.take 32 (List.drop 160 sec))]
      refine bind_congr_eq (findML_congr (fun e => ?_) rfl) fun f => ?_
      · refine entryMatchesC_atomic_eval _ e _
          (p1, (p2, (p3, (some p4v, List.take 32 (List.drop 160 sec))))) ?_
        change projVal patchKeyTy (p1, (p2, (p3, (some p4v,
            if decide (sec.length = 192) = true then List.take 32 (List.drop 160 sec)
            else List.take 32 (List.drop 128 sec))))) = _
        simp only [h192, ↓reduceIte]
      · cases f with
        | some e => simp only [pure_bind]; rfl
        | none =>
          simp only [bind_assoc, pure_bind]
          refine bind_congr_eq (sampleDrKey96C_atomic_eval _) fun dk => ?_
          change pure (aDrKeyAtomVal dk,
              (simConsFgAndLogVal sim (p1, (p2, (p3, (some p4v,
                if decide (sec.length = 192) = true then List.take 32 (List.drop 160 sec)
                else List.take 32 (List.drop 128 sec))))) sec dk, sigB)) = _
          simp only [h192, ↓reduceIte]; rfl
    · simp only [h192, Bool.false_eq_true, ↓reduceIte, pure_bind]
      rw [fgStepP4_map_bind_eq b sim sigB sec p1 p2 p3 none (List.take 32 (List.drop 128 sec))]
      refine bind_congr_eq (findML_congr (fun e => ?_) rfl) fun f => ?_
      · refine entryMatchesC_atomic_eval _ e _
          (p1, (p2, (p3, (none, List.take 32 (List.drop 128 sec))))) ?_
        change projVal patchKeyTy (p1, (p2, (p3, (none,
            if decide (sec.length = 192) = true then List.take 32 (List.drop 160 sec)
            else List.take 32 (List.drop 128 sec))))) = _
        simp only [h192, Bool.false_eq_true, ↓reduceIte]
      · cases f with
        | some e => simp only [pure_bind]; rfl
        | none =>
          simp only [bind_assoc, pure_bind]
          refine bind_congr_eq (sampleDrKey96C_atomic_eval _) fun dk => ?_
          change pure (aDrKeyAtomVal dk,
              (simConsFgAndLogVal sim (p1, (p2, (p3, (none,
                if decide (sec.length = 192) = true then List.take 32 (List.drop 160 sec)
                else List.take 32 (List.drop 128 sec))))) sec dk, sigB)) = _
          simp only [h192, Bool.false_eq_true, ↓reduceIte]; rfl
  · simp only [hG, Bool.false_eq_true, ↓reduceIte, pure_bind]
    dsimp only [ReductionDsl.AtomicPureOp.eval]
    cases hFind : List.find? (fun p : Bytes × (drKeyT (ℓ := 0) (Pt := Empty)).denote => p.1 == sec)
        (List.take b.q_total sim.2.2.2.1) with
    | none =>
      simp only [Option.map_none, bind_assoc, pure_bind]
      refine bind_congr_eq (sampleDrKey96C_atomic_eval _) fun dk => rfl
    | some kv => simp only [Option.map_some, pure_bind]; rfl

/-- Forgetful simulation for the `.roQuery` arm. -/
theorem fgArmSim_roQuery (S : Setup) (b : QueryBudget) :
    FgArmSim S b AuthQuery.roQuery (armEval_roQuery S b) := by
  dsimp only [FgArmSim]
  intro c pa sim sigB aux sec hc hroom hInv
  let F := AuthKindFuels.ofBudget S b
  obtain ⟨hKon, hTot, hRoTot, hRoCap, hKcap⟩ := ro_room_arith hInv.counter_inv hroom
  change c 0 ≤ F.K_on at hKon
  change c 0 + (c 1 + 1) ≤ F.K_cap at hRoCap
  change c 1 + 1 ≤ F.K_cap at hKcap
  obtain ⟨fgTagged, hRel0, hSessLen, hRoLen, hTaggedLen, hValidRo⟩ := hInv.fg_shadow
  have hFuelS : (auxFgSess aux).length ≤ F.K_on := Nat.le_trans hSessLen hKon
  have hListCap : auxFgCtr aux + 1 ≤ c 0 + (c 1 + 1) := by
    have hCtr := hRel0.1.ctr_eq
    have hLen := hRel0.1.len_le
    omega
  have hAvlCap : (roEntriesOf (fun e => e.2.2.2.2.2) fgTagged).length + 1 ≤ F.K_cap := by omega
  have hRawListCap : sim.2.2.2.1.length + 1 ≤ b.q_total := by
    have hRaw := hInv.raw_len; omega
  have hRawAvlCap : sim.2.2.2.1.length + 1 ≤ F.K_cap := by
    have hRaw := hInv.raw_len; omega
  have hRel1 : ShadowRelB192 (drKeyT (ℓ := 0) (Pt := Empty)) (c 0 + (c 1 + 1)) F.K_cap
      (fun e => e.2.2.2.2.2) sim.2.1 fgTagged (auxFgRoAvl aux)
      (auxFgSess aux) (auxFgCtr aux) :=
    hRel0.mono_cap (by omega)
  let tup0Ty : Ty pqAtomicSig :=
    .prod (embedTy fgSimTy) (.prod .nat (.prod fgAuthShadowAuxTy
      (.prod (PB 192) (_root_.ReductionDsl.B 192 : Ty pqAtomicSig))))
  let tup0 : tup0Ty.denote :=
    (sim, (sigB, (aux, (sec, CryptoVerification.E2E.ofU8 sec))))
  let ρ₀ := Env.cons (t := PB 192) sec
    (.cons (t := embedTy a1gParams2Ty) pa
      (.cons (t := embedTy fgSimTy) sim
        (.cons (t := .nat) sigB (.cons (t := fgAuthShadowAuxTy) aux .nil))))
  let ρ₁ (pk? : Option (embedTy patchKeyTy).denote) :=
    Env.cons (t := .opt (embedTy patchKeyTy)) pk? (.cons (t := tup0Ty) tup0 ρ₀)
  let ρ₂ (pk : (embedTy patchKeyTy).denote) :=
    Env.cons (t := embedTy patchKeyTy) pk (ρ₁ (some pk))
  have hNewUnfold :
      armEval_roQuery S b pa sim sigB aux sec =
        (roParsedPrePosAtom sec >>= fun pk? =>
          match pk? with
          | none =>
            (avlSearchB192C (I := SignalPqxdh.Costed.pqAuthSigAndDdhIface) F.K_cap
                (auxRawAvlE (.fst (.snd (.snd .v1))))
                (.snd (.snd (.snd (.snd .v1))))).eval (ρ₁ none) >>= fun searchRes =>
              match searchRes.1 with
              | some dk => pure (aDrKeyAtomVal dk, ((simConsLogVal sim sec, sigB), aux))
              | none =>
                sampleDrKeyAtom >>= fun dk =>
                  (avlInsertAtPathC (I := SignalPqxdh.Costed.pqAuthSigAndDdhIface) F.K_cap
                      (.var .zero) (.var (.succ .zero))
                      (.var (.succ (.succ .zero))) (.var (.succ (.succ (.succ .zero))))).eval
                    (.cons (auxRawAvl aux) (.cons searchRes.2
                      (.cons (CryptoVerification.E2E.ofU8 sec) (.cons dk .nil)))) >>= fun rawAvl' =>
                    pure (aDrKeyAtomVal dk,
                      ((simConsRawAndLogVal sim sec dk, sigB),
                        (auxFgSess aux, (auxFgCtr aux, (auxFgRoAvl aux,
                          (auxFgRootSess aux, (auxFgRootCtr aux,
                            (auxFgRootRoAvl aux, rawAvl'))))))))
          | some pk =>
            (avlSearchB192C (I := SignalPqxdh.Costed.pqAuthSigAndDdhIface) F.K_cap
                (auxFgRoAvlE (.fst (.snd (.snd .v2))))
                (.snd (.snd (.snd (.snd .v2))))).eval (ρ₂ pk) >>= fun searchRes =>
              let minIdx : ℕ := match searchRes.1 with | none => 0 | some p => p.2 + 1
              findML
                (fun ie => if decide (minIdx ≤ ie.1) then fgMatchAtom pk ie.2 else pure false)
                ((auxFgSess aux).take F.K_on) >>=
                fun (sessHit? : Option (embedTy seqFgEntryTy).denote) =>
                match sessHit? with
                | some se =>
                  pure (aDrKeyAtomVal se.2.2.2.2.2.2, ((simConsLogVal sim sec, sigB), aux))
                | none =>
                  match searchRes.1 with
                  | some dkIdx =>
                    pure (aDrKeyAtomVal dkIdx.1, ((simConsLogVal sim sec, sigB), aux))
                  | none =>
                    sampleDrKeyAtom >>= fun dk =>
                      (avlInsertAtPathC (I := SignalPqxdh.Costed.pqAuthSigAndDdhIface) F.K_cap
                          (.var .zero) (.var (.succ .zero))
                          (.var (.succ (.succ .zero))) (.var (.succ (.succ (.succ .zero))))).eval
                        (.cons (auxFgRoAvl aux) (.cons searchRes.2
                          (.cons (CryptoVerification.E2E.ofU8 sec)
                            (.cons (dk, auxFgCtr aux) .nil)))) >>= fun fgRoAvl' =>
                        pure (aDrKeyAtomVal dk,
                          ((simConsFgAndLogVal sim pk sec dk, sigB),
                            (auxFgSess aux, (auxFgCtr aux + 1, (fgRoAvl',
                              (auxFgRootSess aux, (auxFgRootCtr aux,
                                (auxFgRootRoAvl aux, auxRawAvl aux))))))))) := by
    simp only [armEval_roQuery, fgCoreArm_roQuery, Comp.eval, Expr.eval, Env.get,
      pqAtomicOps, ReductionDsl.AtomicPureOp.eval, pure_bind]
    rw [liftGdh1_eval]
    refine congrArg (Bind.bind (roParsedPrePosAtom sec)) (funext fun pk? => ?_)
    cases pk? with
    | none =>
      dsimp only
      refine congrArg (Bind.bind _) (funext fun searchRes => ?_)
      rcases searchRes with ⟨_ | dk, path0⟩
      · dsimp only [Comp.eval, Expr.eval, Env.get, Expr.v0, Expr.v1, Expr.v2, Expr.v3]
        rw [liftGdh0_eval]
        refine congrArg (Bind.bind sampleDrKeyAtom) (funext fun dk => ?_)
        change (avlInsertAtPathC (I := SignalPqxdh.Costed.pqAuthSigAndDdhIface) F.K_cap
            (auxRawAvlE (.fst (.snd (.snd .v3))))
            (.snd .v1) (.snd (.snd (.snd (.snd .v3)))) .v0).eval
            (.cons (t := drKeyT (ℓ := 0) (Pt := Empty)) dk
              (.cons (t := SplitRo.AvlRoTableDefs.avlSearchResTy (drKeyT (ℓ := 0) (Pt := Empty)))
                (none, path0) (ρ₁ none))) >>= _ = _
        rw [SplitRo.AvlRoTableSpec.avlInsertAtPathC_eval_congr F.K_cap]
        dsimp only [auxRawAvlE, Expr.eval, Env.get, Expr.v0, Expr.v1, Expr.v3, ρ₁, tup0]
        refine congrArg (Bind.bind _) (funext fun rawAvl' => ?_)
        simp only [aDrKeyAtomicE_eval, simPrependRawAndLogE_eval, fgAuxMkE,
          auxFgSessE, auxFgCtrE, auxFgRoAvlE, auxFgRootSessE, auxFgRootCtrE, auxFgRootRoAvlE,
          Expr.eval, Env.get]
        rfl
      · dsimp only [Comp.eval, Expr.eval, Env.get, Expr.v0, Expr.v1, Expr.v2, Expr.v3]
        simp only [aDrKeyAtomicE_eval, simPrependLogE_eval, Expr.eval, Env.get]
    | some pk =>
      dsimp only
      refine congrArg (Bind.bind _) (funext fun searchRes => ?_)
      rw [liftGdh1_eval]
      have hArg :
          (Expr.pair .v1
            (.pair (Expr.caseOpt (.fst .v0) (.nat 0) (.add (.snd .v0) (.nat 1)))
              (auxFgSessE (.fst (.snd (.snd .v3)))))).eval
            (.cons (t := SplitRo.AvlRoTableDefs.avlSearchResTy
              (.prod (drKeyT (ℓ := 0) (Pt := Empty)) .nat)) searchRes (ρ₂ pk)) =
          ((pk, ((match searchRes.1 with | none => 0 | some p => p.2 + 1), auxFgSess aux)) :
            (embedTy (.prod patchKeyTy (.prod .nat (.list seqFgEntryTy)))).denote) := by
        rcases searchRes with ⟨_ | _, _⟩ <;> rfl
      erw [hArg, fgSessScan_atomic_eval]
      refine congrArg (Bind.bind _) (funext fun sessHit? => ?_)
      cases sessHit? with
      | some se =>
        simp only [aDrKeyAtomicE_eval, simPrependLogE_eval, Expr.eval]
        rfl
      | none =>
        rcases searchRes with ⟨_ | dkIdx, path0⟩
        · dsimp only [Comp.eval, Expr.eval, Env.get, Expr.v0, Expr.v1, Expr.v2, Expr.v4, Expr.v5]
          rw [liftGdh0_eval]
          refine congrArg (Bind.bind sampleDrKeyAtom) (funext fun dk => ?_)
          change (avlInsertAtPathC (I := SignalPqxdh.Costed.pqAuthSigAndDdhIface) F.K_cap
              (auxFgRoAvlE (.fst (.snd (.snd .v5))))
              (.snd .v2) (.snd (.snd (.snd (.snd .v5))))
              (.pair .v0 (auxFgCtrE (.fst (.snd (.snd .v5)))))).eval
              (.cons (t := drKeyT (ℓ := 0) (Pt := Empty)) dk
                (.cons (t := .opt (embedTy seqFgEntryTy)) none
                  (.cons (t := SplitRo.AvlRoTableDefs.avlSearchResTy
                    (.prod (drKeyT (ℓ := 0) (Pt := Empty)) .nat)) (none, path0) (ρ₂ pk)))) >>= _ = _
          rw [SplitRo.AvlRoTableSpec.avlInsertAtPathC_eval_congr F.K_cap]
          dsimp only [auxFgRoAvlE, auxFgCtrE, Expr.eval, Env.get,
            Expr.v0, Expr.v2, Expr.v5, ρ₂, ρ₁, tup0]
          refine congrArg (Bind.bind _) (funext fun fgRoAvl' => ?_)
          simp only [aDrKeyAtomicE_eval, simPrependFgAndLogE_eval, fgAuxMkE,
            auxFgSessE, auxFgRootSessE, auxFgRootCtrE, auxFgRootRoAvlE, auxRawAvlE,
            Expr.eval, Env.get]
        · dsimp only [Comp.eval, Expr.eval, Env.get, Expr.v0, Expr.v1, Expr.v5]
          simp only [aDrKeyAtomicE_eval, simPrependLogE_eval, Expr.eval, Env.get]
  constructor
  ·
    rw [hNewUnfold, legacyCoreArmEval_roQuery_eq, map_bind]
    refine MonadAttach.bind_congr_of_forall_mem_support (roParsedPrePosAtom sec) fun pk? hpk => ?_
    cases pk? with
    | none =>
      obtain ⟨path, hSearch, hInsSpec⟩ :=
        RoCacheRelB192.search_and_insert_spec
          (I := SignalPqxdh.Costed.pqAuthSigAndDdhIface)
          (auxRawAvlE (.fst (.snd (.snd .v1))))
          (.snd (.snd (.snd (.snd .v1))))
          (ρ₁ none) sec rfl hInv.raw_rel
      have hRawTblEval :
          (auxRawAvlE (.fst (.snd (.snd .v1)))).eval (ρ₁ none) = auxRawAvl aux := rfl
      rw [hSearch, hInv.raw_rel.1.find?_take_map_snd sec]
      simp only [pure_bind]
      cases hRawHit : (sim.2.2.2.1.find? (fun p => p.1 == sec)).map Prod.snd with
      | some dk =>
        simp only [map_pure, Prod.map]
        rfl
      | none =>
        simp only [map_bind]
        refine congrArg (Bind.bind sampleDrKeyAtom) (funext fun dk => ?_)
        obtain ⟨rawAvl', hInsEval, _⟩ := hInsSpec hRawHit hRawListCap hRawAvlCap dk
        rw [hRawTblEval] at hInsEval
        rw [hInsEval]
        simp only [pure_bind, map_pure, Prod.map]
        rfl
    | some pk =>
      dsimp only
      let dkDummy : (drKeyT (ℓ := 0) (Pt := Empty)).denote :=
        SplitRo.AvlRoTableDefs.dfltDrKeyE.eval .nil
      have hValidPk := roParsedPrePosAtom_some_support hpk dkDummy
      obtain ⟨path, hSearch, hInsSpec⟩ :=
        ShadowRelB192.search_and_insert_spec
          (I := SignalPqxdh.Costed.pqAuthSigAndDdhIface)
          (auxFgRoAvlE (.fst (.snd (.snd .v2))))
          (.snd (.snd (.snd (.snd .v2))))
          (ρ₂ pk) sec rfl hRel1
      have hFgTblEval :
          (auxFgRoAvlE (.fst (.snd (.snd .v2)))).eval (ρ₂ pk) = auxFgRoAvl aux := rfl
      rw [hSearch]
      simp only [pure_bind, map_bind]
      have hScanEq :=
        findML_take_eq_shadowScanMinIdx
          (hRel0.1.mono_cap (by omega : c 0 + c 1 ≤ b.q_total))
          hFuelS sec (fgMatchAtom pk)
          (fun te hte sec' htag => fgMatchAtom_on_parsedRo hValidPk (hValidRo te hte sec' htag))
      rw [hScanEq]
      simp only [shadowScanMinIdx, bind_map_left]
      rcases hAvl :
          ((roEntriesOf (fun e => e.2.2.2.2.2) fgTagged).find?
            (fun p => p.1 == sec)).map Prod.snd with _ | ⟨dk0, idx_ro⟩
      · try rw [hAvl]
        dsimp only
        refine congrArg (Bind.bind _) (funext fun sessHit? => ?_)
        cases sessHit? with
        | some se =>
          simp only [map_pure, Prod.map]
          rfl
        | none =>
          simp only [Option.map_none, map_bind]
          refine congrArg (Bind.bind sampleDrKeyAtom) (funext fun dk => ?_)
          obtain ⟨fgRoAvl', hInsEval, _⟩ :=
            hInsSpec hAvl hListCap hAvlCap (fgPatchEntryOfPkDk pk dk)
          rw [hFgTblEval] at hInsEval
          dsimp only [fgPatchEntryOfPkDk] at hInsEval
          rw [hInsEval]
          simp only [pure_bind, map_pure, Prod.map]
          rfl
      · try rw [hAvl]
        dsimp only
        refine congrArg (Bind.bind _) (funext fun sessHit? => ?_)
        cases sessHit? with
        | some se =>
          simp only [map_pure, Prod.map]
          rfl
        | none =>
          simp only [Option.map_some, map_pure, Prod.map]
          rfl
  ·
    intro out hout
    rw [hNewUnfold, mem_support_bind_iff] at hout
    obtain ⟨pk?, hpk, hout⟩ := hout
    cases pk? with
    | none =>
      obtain ⟨path, hSearch, hInsSpec⟩ :=
        RoCacheRelB192.search_and_insert_spec
          (I := SignalPqxdh.Costed.pqAuthSigAndDdhIface)
          (auxRawAvlE (.fst (.snd (.snd .v1))))
          (.snd (.snd (.snd (.snd .v1))))
          (ρ₁ none) sec rfl hInv.raw_rel
      have hRawTblEval :
          (auxRawAvlE (.fst (.snd (.snd .v1)))).eval (ρ₁ none) = auxRawAvl aux := rfl
      rw [hSearch, pure_bind] at hout
      cases hRawHit : (sim.2.2.2.1.find? (fun p => p.1 == sec)).map Prod.snd with
      | some dk =>
        simp only [hRawHit, mem_support_pure_iff] at hout
        subst hout
        exact ro_inv_log_cons hroom hInv
      | none =>
        simp only [hRawHit, mem_support_bind_iff] at hout
        obtain ⟨dk, _, hout⟩ := hout
        obtain ⟨rawAvl', hInsEval, hRawRel'⟩ := hInsSpec hRawHit hRawListCap hRawAvlCap dk
        rw [hRawTblEval] at hInsEval
        rw [hInsEval] at hout
        simp only [mem_support_pure_iff] at hout
        rcases hout with ⟨_, rfl, rfl⟩
        obtain ⟨hb0, hb1, hb2, _⟩ := bump_ro_counts (S := S) c sec
        refine ⟨hInv.counter_inv.bump (.roQuery sec) hroom,
          hb0.symm ▸ hInv.base_online,
          hb0.symm ▸ hInv.pows_len,
          hb0.symm ▸ hInv.resp_len,
          ?_, ?_,
          hb0.symm ▸ hb2.symm ▸ hInv.root_shadow,
          hRawRel', ?_⟩
        · rw [hb1]
          have hLog := hInv.log_len
          simp only [simConsRawAndLogVal, List.length_cons]
          omega
        · rw [hb0, hb1]
          exact ⟨fgTagged, hRel1, hSessLen, by omega, by omega, hValidRo⟩
        · rw [hb1]
          have hRaw := hInv.raw_len
          simp only [simConsRawAndLogVal, List.length_cons]
          omega
    | some pk =>
      dsimp only at hout
      obtain ⟨path, hSearch, hInsSpec⟩ :=
        ShadowRelB192.search_and_insert_spec
          (I := SignalPqxdh.Costed.pqAuthSigAndDdhIface)
          (auxFgRoAvlE (.fst (.snd (.snd .v2))))
          (.snd (.snd (.snd (.snd .v2))))
          (ρ₂ pk) sec rfl hRel1
      have hFgTblEval :
          (auxFgRoAvlE (.fst (.snd (.snd .v2)))).eval (ρ₂ pk) = auxFgRoAvl aux := rfl
      rw [hSearch, pure_bind, mem_support_bind_iff] at hout
      obtain ⟨sessHit?, _, hout⟩ := hout
      set avlHit? := ((roEntriesOf (fun e => e.2.2.2.2.2) fgTagged).find?
        (fun p => p.1 == sec)).map Prod.snd
      cases sessHit? with
      | some se =>
        rw [mem_support_pure_iff] at hout
        subst hout
        exact ro_inv_log_cons hroom hInv
      | none =>
        cases hAvl : avlHit? with
        | some dkIdx =>
          simp only [hAvl, mem_support_pure_iff] at hout
          subst hout
          exact ro_inv_log_cons hroom hInv
        | none =>
          simp only [hAvl, mem_support_bind_iff] at hout
          obtain ⟨dk, _, hout⟩ := hout
          let newFE : (embedTy fgPatchEntryTy).denote := fgPatchEntryOfPkDk pk dk
          obtain ⟨fgRoAvl', hInsEval, hRelNew⟩ :=
            hInsSpec hAvl hListCap hAvlCap newFE
          rw [hFgTblEval] at hInsEval
          dsimp only [newFE, fgPatchEntryOfPkDk] at hInsEval
          rw [hInsEval] at hout
          simp only [mem_support_pure_iff] at hout
          rcases hout with ⟨_, rfl, rfl⟩
          obtain ⟨hb0, hb1, hb2, _⟩ := bump_ro_counts (S := S) c sec
          refine ⟨hInv.counter_inv.bump (.roQuery sec) hroom,
            hb0.symm ▸ hInv.base_online,
            hb0.symm ▸ hInv.pows_len,
            hb0.symm ▸ hInv.resp_len,
            ?_, ?_,
            hb0.symm ▸ hb2.symm ▸ hInv.root_shadow,
            hInv.raw_rel, ?_⟩
          · rw [hb1]
            have hLog := hInv.log_len
            simp only [simConsFgAndLogVal, List.length_cons]
            omega
          · rw [hb0, hb1]
            refine ⟨⟨auxFgCtr aux, .ro sec, newFE⟩ :: fgTagged,
              hRelNew, hSessLen, ?_, ?_, ?_⟩
            · have hRoCons :
                  (roEntriesOf (fun e : (embedTy fgPatchEntryTy).denote => e.2.2.2.2.2)
                    (⟨auxFgCtr aux, .ro sec, newFE⟩ :: fgTagged)).length =
                  (roEntriesOf (fun e : (embedTy fgPatchEntryTy).denote => e.2.2.2.2.2)
                    fgTagged).length + 1 := rfl
              rw [hRoCons]
              omega
            · simp only [List.length_cons]
              omega
            · intro te hte sec' htag
              rcases List.mem_cons.mp hte with rfl | hmem
              · cases htag
                exact roParsedPrePosAtom_some_support hpk dk
              · exact hValidRo te hmem sec' htag
          · rw [hb1]
            have hRaw := hInv.raw_len
            simp only [simConsFgAndLogVal]
            omega

end Computational.Proofs.SignalPqxdh.Security.ReductionDsl.KindSplit.AuthGapDhKSimRo
