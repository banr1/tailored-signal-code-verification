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

/-!
# `.roRootQuery` Arm Simulation for `Auth` Gap-DH and EUF-CMA

**Checked by Lean.** Proves `fgArmSim_roRootQuery`, relating `fgCoreArm_roRootQuery` to
`legacyCoreArmEval` on `.roRootQuery` inputs while preserving `FgSimShadowInv`.
-/

public section

set_option autoImplicit false

namespace Computational.Proofs.SignalPqxdh.Security.ReductionDsl.KindSplit.AuthGapDhKSimRoRoot

open OracleSpec OracleComp
open _root_.ReductionDsl (Ty Var Expr Comp Env PB pqAtomicSig pqAtomicOps findML)
open _root_.Computational.Proofs.ReductionDsl.StepSim (bumpPred)
open _root_.Computational.Proofs.SignalPqxdh.AtomicLift
  (embedTy embedVal projVal embedVal_projVal embedEnv exprRename exprRename_eval
   compRename compRename_eval mapExpr mapExpr_eval mapComp mapComp_eval
   comp_queries_zero_of_zero tlAuthSigDdh)
open _root_.SignalPqxdh (Setup QueryBudget AuthQuery Bytes)
open _root_.SignalPqxdh.LegacyCosted (pqSig pqxdhOps pqSigAndDdhIface pqGapDhIface B)
open _root_.SignalPqxdh.Costed (authCodec)
open _root_.SignalPqxdh.Security.ReductionDsl (fgPosTy authQueryTy authRespTy)
open _root_.SignalPqxdh.Security.ReductionDsl.AuthHs
  (v letV bindV caseOptV caseSumV findMV
   fgSimTy rootEntryTy a1gParams2Ty a1gPre2C fgStep2C
   fsRootL fsUpd fsMk fsBase fsL fsRaw fsLog fsResp fsPows
   reRk rePos reRk1 reCk aRootKdf
   mkSecretPosC mkSecretPosC_eval ddhEqC rootPatchC fgRoRootC)
open _root_.SignalPqxdh.Security.ReductionDsl.KeyInd1KeyGapDh
  (liftGdhComp liftGdhComp_eval liftGdhToSign_bind liftGdhToSign_pure)
open _root_.Computational.Proofs.SignalPqxdh.Security.ReductionDsl.SplitRo.AvlRoTableDefs
  (aop avlSearchPair32C avlInsertAtPathC)
open _root_.Computational.Proofs.SignalPqxdh.Security.ReductionDsl.SplitRo.AvlRoCacheRefine
  (TaggedEntry ShadowRelPair32 roEntriesOf shadowScanMinIdx findML_take_eq_shadowScanMinIdx)
open _root_.Computational.Proofs.SignalPqxdh.Security.ReductionDsl.KindSplit.AuthCoreK
  (AuthKindFuels wk1 wk2 liftExpr1 liftExpr2 aRootKdfAtomicE)
open _root_.Computational.Proofs.SignalPqxdh.Security.ReductionDsl.KindSplit.AuthCoreKSimBase
  (authSimPred authSimBounds AuthCounterInv)
open _root_.Computational.Proofs.SignalPqxdh.Security.ReductionDsl.KindSplit.AuthGapDhK
  (fgAuthShadowAuxTy seqRootEntryTy
   auxFgSess auxFgCtr auxFgRoAvl auxFgRootSess auxFgRootCtr auxFgRootRoAvl
   auxRawAvl auxFgSessE auxFgCtrE auxFgRoAvlE auxFgRootSessE auxFgRootCtrE auxFgRootRoAvlE
   auxRawAvlE fgAuxMkE wk0 liftCs0 liftCs1 liftGdh0 liftGdh1
   sampleRootPair64LegC rootSessScanC simPrependRootE fgCoreArm_roRootQuery)
open _root_.Computational.Proofs.SignalPqxdh.Security.ReductionDsl.KindSplit.AuthGapDhKSimBase
  (ValidRoRootEntry RootTableShadow FgSimShadowInv AuthSigDdhSpec
   legacyCoreArmComp legacyCoreArmEval FgArmSim armEval_roRootQuery rootMatchC_atomic_on_ro)

private theorem bump_roRoot_counts {S : Setup} (c : Fin 4 → ℕ) (rk dh : Bytes) :
    let t := AuthQuery.roRootQuery (S := S) rk dh
    bumpPred (authSimPred S) c t 0 = c 0 ∧
    bumpPred (authSimPred S) c t 1 = c 1 ∧
    bumpPred (authSimPred S) c t 2 = c 2 + 1 ∧
    bumpPred (authSimPred S) c t 3 = c 3 + 1 := by
  have h0 : ¬ authSimPred S 0 (.roRootQuery rk dh) := by
    simp [authSimPred, SignalPqxdh.isAuthOnlineQuery]
  have h1 : ¬ authSimPred S 1 (.roRootQuery rk dh) := by
    simp [authSimPred, SignalPqxdh.isAuthRoQuery]
  have h2 : authSimPred S 2 (.roRootQuery rk dh) := by
    simp [authSimPred, SignalPqxdh.isAuthRoRootQuery]
  have h3 : authSimPred S 3 (.roRootQuery rk dh) := trivial
  simp [bumpPred, h0, h1, h2, h3]

private theorem roRoot_room_arith {S : Setup} {b : QueryBudget} {c : Fin 4 → ℕ}
    {rk dh : Bytes} (hCounter : AuthCounterInv b c)
    (hroom : ∀ j, authSimPred S j (.roRootQuery rk dh) → c j + 1 ≤ authSimBounds b j) :
    let F := AuthKindFuels.ofBudget S b
    c 0 ≤ F.K_on ∧
    c 0 + (c 2 + 1) ≤ b.q_total ∧
    c 2 + 1 ≤ F.K_cap := by
  have hRt : authSimPred S 2 (.roRootQuery rk dh) := by
    simp [authSimPred, SignalPqxdh.isAuthRoRootQuery]
  have hStep := hCounter.roRoot_step_bounds hRt hroom
  have h2 := hroom 2 hRt
  have hOn := hCounter.on_le
  dsimp only [AuthKindFuels.ofBudget, authSimBounds] at hStep h2 ⊢
  omega

private theorem roRoot_inv_unchanged {S : Setup} {b : QueryBudget} {c : Fin 4 → ℕ}
    {sim : (embedTy fgSimTy).denote} {aux : fgAuthShadowAuxTy.denote} {rk dh : Bytes}
    (hroom : ∀ j, authSimPred S j (.roRootQuery rk dh) → c j + 1 ≤ authSimBounds b j)
    (hInv : FgSimShadowInv S b c sim aux) :
    FgSimShadowInv S b (bumpPred (authSimPred S) c (.roRootQuery rk dh)) sim aux := by
  obtain ⟨hb0, hb1, hb2, _⟩ := bump_roRoot_counts (S := S) c rk dh
  refine ⟨hInv.counter_inv.bump (.roRootQuery rk dh) hroom,
    hb0.symm ▸ hInv.base_online,
    hb0.symm ▸ hInv.pows_len,
    hb0.symm ▸ hInv.resp_len,
    hb1.symm ▸ hInv.log_len,
    hb0.symm ▸ hb1.symm ▸ hInv.fg_shadow,
    ?_, hInv.raw_rel, hb1.symm ▸ hInv.raw_len⟩
  rw [hb0, hb2]
  obtain ⟨rt, hRel, hSess, hRo, hLen, hValid⟩ := hInv.root_shadow
  exact ⟨rt, hRel.mono_cap (by omega), hSess, by omega, by omega, hValid⟩

theorem liftGdh0_eval {out : Ty pqSig} {Γ : List (Ty pqAtomicSig)}
    (c : Comp pqxdhOps pqGapDhIface [] out) (ρ : Env Γ) :
    (liftGdh0 c).eval ρ = (mapComp tlAuthSigDdh (liftGdhComp c)).eval .nil :=
  compRename_eval (mapComp tlAuthSigDdh (liftGdhComp c)) wk0 .nil ρ (fun v => nomatch v)

theorem liftGdh1_eval {a out : Ty pqSig} {Γ : List (Ty pqAtomicSig)}
    (c : Comp pqxdhOps pqGapDhIface [a] out)
    (argE : Expr pqAtomicOps Γ (embedTy a)) (ρ : Env Γ) :
    (liftGdh1 c argE).eval ρ =
      (mapComp tlAuthSigDdh (liftGdhComp c)).eval (.cons (argE.eval ρ) .nil) := by
  simp only [liftGdh1, liftCs1, Comp.eval, pure_bind]
  exact compRename_eval (mapComp tlAuthSigDdh (liftGdhComp c)) wk1
    (.cons (argE.eval ρ) .nil) (.cons (argE.eval ρ) ρ)
    (fun v => by cases v with | zero => rfl | succ v => nomatch v)

@[expose] def mkSecretPosAtom (dh : Bytes) :
    OracleComp AuthSigDdhSpec (embedTy fgPosTy).denote :=
  (mapComp tlAuthSigDdh (liftGdhComp (mkSecretPosC (Δ := [B 32]) (.var .zero)))).eval
    (.cons (t := embedTy (B 32)) dh .nil)

theorem mkSecretPosAtom_support {dh : Bytes} {pos : (embedTy fgPosTy).denote}
    (hpos : pos ∈ support (mkSecretPosAtom dh)) :
    ∃ isCan : Bool, pos = Sum.inl (dh, isCan) := by
  change pos ∈ support ((mapComp tlAuthSigDdh
    (liftGdhComp (mkSecretPosC (Δ := [B 32]) (.var .zero)))).eval
    (embedEnv (.cons (t := B 32) dh .nil))) at hpos
  rw [mapComp_eval tlAuthSigDdh _ (comp_queries_zero_of_zero (fun _ => rfl) _),
    liftGdhComp_eval, mkSecretPosC_eval, SignalPqxdh.Security.FgGapDh.mkSecretPos] at hpos
  simp only [Expr.eval, Env.get, map_bind, map_pure, liftGdhToSign_bind, liftGdhToSign_pure,
    mem_support_bind_iff, mem_support_pure_iff] at hpos
  rcases hpos with ⟨isCan, _, rfl⟩
  exact ⟨isCan, rfl⟩

private def sampleRootPairAtom : OracleComp AuthSigDdhSpec (Bytes × Bytes) :=
  (mapComp tlAuthSigDdh (liftGdhComp sampleRootPair64LegC)).eval .nil

private def aRootKdfAtomVal (rkCk : Bytes × Bytes) : (embedTy authRespTy).denote :=
  (aRootKdfAtomicE (Γ := [.prod (PB 32) (PB 32)]) (.var .zero)).eval (.cons rkCk .nil)

private theorem aRootKdfAtomicE_eval {Γ : List (Ty pqAtomicSig)}
    (rkCkE : Expr pqAtomicOps Γ (.prod (PB 32) (PB 32))) (ρ : Env Γ) :
    (aRootKdfAtomicE rkCkE).eval ρ = aRootKdfAtomVal (rkCkE.eval ρ) := by
  simp only [aRootKdfAtomicE, aRootKdfAtomVal, liftExpr1, Expr.eval]
  exact exprRename_eval _ wk1 (.cons (rkCkE.eval ρ) .nil) (.cons (rkCkE.eval ρ) ρ)
    (fun v => by cases v with | zero => rfl | succ v => nomatch v)

private def simConsRootVal (sim : (embedTy fgSimTy).denote)
    (re : (embedTy rootEntryTy).denote) : (embedTy fgSimTy).denote :=
  (sim.1, (sim.2.1, (re :: sim.2.2.1, sim.2.2.2)))

private theorem simPrependRootE_eval {Γ : List (Ty pqAtomicSig)}
    (simE : Expr pqAtomicOps Γ (embedTy fgSimTy))
    (newReE : Expr pqAtomicOps Γ (embedTy rootEntryTy)) (ρ : Env Γ) :
    (simPrependRootE simE newReE).eval ρ = simConsRootVal (simE.eval ρ) (newReE.eval ρ) := by
  simp only [simPrependRootE, liftExpr2, Expr.eval]
  rw [exprRename_eval _ Var.succ ρ (.cons (newReE.eval ρ) ρ) (fun _ => rfl)]
  rw [exprRename_eval _ wk2 (.cons (simE.eval ρ) (.cons (newReE.eval ρ) .nil))
    (.cons (simE.eval ρ) (.cons (newReE.eval ρ) ρ))
    (fun v => by
      cases v with
      | zero => rfl
      | succ v => cases v with
        | zero => rfl
        | succ v => nomatch v)]
  rfl

private def rootMatchAtom (rk : Bytes) (pos : (embedTy fgPosTy).denote)
    (e : (embedTy rootEntryTy).denote) : OracleComp AuthSigDdhSpec Bool :=
  (mapComp tlAuthSigDdh
    (liftGdhComp (Γ := [rootEntryTy, B 32, fgPosTy])
      (.iteC (.boolNot (.bytesBeq (.var (.succ .zero)) (reRk (.var .zero))))
        (.ret (.litBool false))
        (ddhEqC (.var (.succ (.succ .zero))) (rePos (.var .zero)))))).eval
    (.cons (t := embedTy rootEntryTy) e
      (.cons (t := embedTy (B 32)) rk (.cons (t := embedTy fgPosTy) pos .nil)))

private theorem rootMatchAtom_on_ro {rk dh : Bytes} {isCan : Bool}
    {k' : Bytes × Bytes} {e : (embedTy rootEntryTy).denote}
    (hEntry : ValidRoRootEntry k' e) :
    rootMatchAtom rk (Sum.inl (dh, isCan)) e = pure (k' == (rk, dh)) :=
  rootMatchC_atomic_on_ro
    (Δ := [B 32, fgPosTy])
    (.var (.succ .zero)) (.var (.succ (.succ .zero)))
    (.cons (t := B 32) rk (.cons (t := fgPosTy) (Sum.inl (dh, isCan)) .nil))
    rfl rfl hEntry

private theorem rootSessScan_atomic_eval (K_on : ℕ) (rk : Bytes)
    (pos : (embedTy fgPosTy).denote) (minIdx : ℕ)
    (sessL : (embedTy (.list seqRootEntryTy)).denote) :
    (mapComp tlAuthSigDdh (liftGdhComp (rootSessScanC K_on))).eval
      (.cons (t := embedTy (.prod (.prod (B 32) fgPosTy) (.prod .nat (.list seqRootEntryTy))))
        ((rk, pos), (minIdx, sessL)) .nil) =
      findML
        (fun ie => if decide (minIdx ≤ ie.1) then rootMatchAtom rk pos ie.2 else pure false)
        (sessL.take K_on) := by
  simp only [rootSessScanC, letV, findMV, v, Comp.letC, Comp.findBoundedM, Var.vs,
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
    exact compRename_eval
      (mapComp tlAuthSigDdh
        (liftGdhComp (Γ := [rootEntryTy, B 32, fgPosTy])
          (.iteC (.boolNot (.bytesBeq (.var (.succ .zero)) (reRk (.var .zero))))
            (.ret (.litBool false))
            (ddhEqC (.var (.succ (.succ .zero))) (rePos (.var .zero))))))
      (fun {a} v => match v with
        | .zero => .zero
        | .succ .zero => .succ (.succ (.succ (.succ .zero)))
        | .succ (.succ .zero) => .succ (.succ (.succ .zero))
        | .succ (.succ (.succ v)) => nomatch v)
      (.cons (t := embedTy rootEntryTy) ie.2
        (.cons (t := embedTy (B 32)) rk (.cons (t := embedTy fgPosTy) pos .nil)))
      (.cons (t := embedTy rootEntryTy) ie.2
        (.cons (t := embedTy seqRootEntryTy) ie
          (.cons (t := .nat) minIdx
            (.cons (t := embedTy fgPosTy) pos
              (.cons (t := embedTy (B 32)) rk
                (.cons (t := embedTy (.prod (.prod (B 32) fgPosTy)
                  (.prod .nat (.list seqRootEntryTy))))
                  ((rk, pos), (minIdx, sessL)) .nil))))))
      (fun v => by
        cases v with
        | zero => rfl
        | succ v => cases v with
          | zero => rfl
          | succ v => cases v with
            | zero => rfl
            | succ v => nomatch v)

private theorem legacyCoreArmEval_roRootQuery_eq (S : Setup) (b : QueryBudget)
    (pa : (embedTy a1gParams2Ty).denote) (sim : (embedTy fgSimTy).denote)
    (sigB : ℕ) (rk dh : Bytes) :
    legacyCoreArmEval S b pa sim sigB (.roRootQuery rk dh) =
      (mkSecretPosAtom dh >>= fun pos =>
        (Option.map (fun e : (embedTy rootEntryTy).denote => e.2.2) <$>
          findML (rootMatchAtom rk pos) (sim.2.2.1.take b.q_total)) >>= fun hit? =>
          match hit? with
          | some rkCk => pure (aRootKdfAtomVal rkCk, (sim, sigB))
          | none =>
            sampleRootPairAtom >>= fun rkCk =>
              pure (aRootKdfAtomVal rkCk,
                (simConsRootVal sim (rk, (pos, rkCk)), sigB))) := by
  simp only [legacyCoreArmEval, legacyCoreArmComp, a1gPre2C, fgStep2C, fgRoRootC, rootPatchC,
    letV, bindV, caseSumV, caseOptV, findMV, v,
    Comp.letC, Comp.findBoundedM, Comp.caseOptC, Var.vs, fsRootL, reRk1, reCk,
    SignalPqxdh.Security.ReductionDsl.AuthHs.Ext.wk, Var.vz, AtomicLift.embedVar,
    liftGdhComp, mapComp, mapExpr, Comp.eval, Expr.eval, Env.get,
    authCodec, SignalPqxdh.Costed.authQenc, pure_bind, bind_assoc]
  have hPre :
      ∀ {Δ : List (Ty pqSig)} (ρTail : Env (AtomicLift.embedCtx Δ)),
        (mapComp tlAuthSigDdh
          (liftGdhComp (Γ := Ty.prod (B 32) (B 32) :: Δ) (mkSecretPosC (.snd (.var .zero))))).eval
          (.cons (t := embedTy (.prod (B 32) (B 32))) (rk, dh) ρTail) = mkSecretPosAtom dh := by
    intro Δ ρTail
    simp only [mkSecretPosAtom, mkSecretPosC, letV, bindV, v, Comp.letC, Var.vs,
      SignalPqxdh.Security.ReductionDsl.AuthHs.Ext.wk, Var.vz, AtomicLift.embedVar,
      liftGdhComp, mapComp, mapExpr, Comp.eval, Expr.eval, Env.get, pure_bind]
    rfl
  erw [hPre]
  refine congrArg (mkSecretPosAtom dh >>= ·) (funext fun pos => ?_)
  simp only [bind_map_left]
  refine Eq.trans
    (congrArg (· >>= _) ?_)
    (congrArg (findML (rootMatchAtom rk pos) (List.take b.q_total sim.2.2.1) >>= ·)
      (funext fun f => ?_))
  · congr 1
  · cases f with
    | some e =>
      simp only [Option.map_some, pure_bind]
      rfl
    | none =>
      simp only [Option.map_none, sampleRootPairAtom, sampleRootPair64LegC,
        bindV, v,
        SignalPqxdh.Security.ReductionDsl.AuthHs.Ext.wk, Var.vz, AtomicLift.embedVar,
        liftGdhComp, mapComp, mapExpr,
        ReductionDsl.Comp.sampleBytes32C,
        AtomicLift.mapSampH, AtomicLift.mapSampCast, AtomicLift.mapSamp,
        Comp.eval, Expr.eval, Env.get, pure_bind, bind_assoc]
      rfl

/-- Forgetful simulation for the `.roRootQuery` arm. -/
theorem fgArmSim_roRootQuery (S : Setup) (b : QueryBudget) :
    FgArmSim S b (fun p => AuthQuery.roRootQuery p.1 p.2) (armEval_roRootQuery S b) := by
  dsimp only [FgArmSim]
  intro c pa sim sigB aux ⟨rk, dh⟩ hc hroom hInv
  let F := AuthKindFuels.ofBudget S b
  obtain ⟨hKon, hTot, hKcap⟩ := roRoot_room_arith hInv.counter_inv hroom
  change c 0 ≤ F.K_on at hKon
  change c 2 + 1 ≤ F.K_cap at hKcap
  obtain ⟨rootTagged, hRel0, hSessLen, hRoLen, hTaggedLen, hValidRo⟩ := hInv.root_shadow
  have hFuelS : (auxFgRootSess aux).length ≤ F.K_on := Nat.le_trans hSessLen hKon
  have hListCap : auxFgRootCtr aux + 1 ≤ c 0 + (c 2 + 1) := by
    have hCtr := hRel0.1.ctr_eq
    have hLen := hRel0.1.len_le
    omega
  have hAvlCap : (roEntriesOf (fun e => e.2.2) rootTagged).length + 1 ≤ F.K_cap := by omega
  have hRel1 : ShadowRelPair32 (.prod (PB 32) (PB 32)) (c 0 + (c 2 + 1)) F.K_cap
      (fun e => e.2.2) sim.2.2.1 rootTagged (auxFgRootRoAvl aux)
      (auxFgRootSess aux) (auxFgRootCtr aux) :=
    hRel0.mono_cap (by omega)
  let tup0Ty : Ty pqAtomicSig :=
    .prod (embedTy fgSimTy) (.prod .nat (.prod fgAuthShadowAuxTy
      (.prod (.prod (PB 32) (PB 32))
        (.prod (_root_.ReductionDsl.B 32 : Ty pqAtomicSig)
          (_root_.ReductionDsl.B 32 : Ty pqAtomicSig)))))
  let tup0 : tup0Ty.denote :=
    (sim, (sigB, (aux, ((rk, dh),
      (CryptoVerification.E2E.ofU8 rk, CryptoVerification.E2E.ofU8 dh)))))
  let ρ₀ := Env.cons (t := .prod (PB 32) (PB 32)) (rk, dh)
    (.cons (t := embedTy a1gParams2Ty) pa
      (.cons (t := embedTy fgSimTy) sim
        (.cons (t := .nat) sigB (.cons (t := fgAuthShadowAuxTy) aux .nil))))
  let ρ₂ (pos : (embedTy fgPosTy).denote) :=
    Env.cons (t := embedTy fgPosTy) pos (.cons (t := tup0Ty) tup0 ρ₀)
  have hNewUnfold :
      armEval_roRootQuery S b pa sim sigB aux (rk, dh) =
        (mkSecretPosAtom dh >>= fun pos =>
          (avlSearchPair32C (I := SignalPqxdh.Costed.pqAuthSigAndDdhIface) F.K_cap
              (auxFgRootRoAvlE (.fst (.snd (.snd .v1))))
              (.snd (.snd (.snd (.snd .v1))))).eval (ρ₂ pos) >>= fun searchRes =>
            let minIdx : ℕ := match searchRes.1 with | none => 0 | some p => p.2 + 1
            findML
              (fun ie => if decide (minIdx ≤ ie.1) then rootMatchAtom rk pos ie.2 else pure false)
              ((auxFgRootSess aux).take F.K_on) >>=
              fun (sessHit? : Option (embedTy seqRootEntryTy).denote) =>
              match sessHit? with
              | some se =>
                pure (aRootKdfAtomVal se.2.2.2, ((sim, sigB), aux))
              | none =>
                match searchRes.1 with
                | some rkCkIdx =>
                  pure (aRootKdfAtomVal rkCkIdx.1, ((sim, sigB), aux))
                | none =>
                  sampleRootPairAtom >>= fun rkCk =>
                    (avlInsertAtPathC (I := SignalPqxdh.Costed.pqAuthSigAndDdhIface) F.K_cap
                        (.var .zero) (.var (.succ .zero))
                        (.var (.succ (.succ .zero))) (.var (.succ (.succ (.succ .zero))))).eval
                      (.cons (auxFgRootRoAvl aux) (.cons searchRes.2
                        (.cons (CryptoVerification.E2E.ofU8 rk, CryptoVerification.E2E.ofU8 dh)
                          (.cons (rkCk, auxFgRootCtr aux) .nil)))) >>= fun fgRootRoAvl' =>
                      pure (aRootKdfAtomVal rkCk,
                        ((simConsRootVal sim (rk, (pos, rkCk)), sigB),
                          (auxFgSess aux, (auxFgCtr aux, (auxFgRoAvl aux,
                            (auxFgRootSess aux, (auxFgRootCtr aux + 1,
                              (fgRootRoAvl', auxRawAvl aux))))))))) := by
    simp only [armEval_roRootQuery, fgCoreArm_roRootQuery, Comp.eval, Expr.eval, Env.get,
      pure_bind]
    rw [liftGdh1_eval]
    refine congrArg (mkSecretPosAtom dh >>= ·) (funext fun pos => ?_)
    refine congrArg (_ >>= ·) (funext fun searchRes => ?_)
    rw [liftGdh1_eval]
    have hArg :
        (Expr.pair
          (.pair (.fst (.fst (.snd (.snd (.snd .v2))))) .v1)
          (.pair (Expr.caseOpt (.fst .v0) (.nat 0) (.add (.snd .v0) (.nat 1)))
            (auxFgRootSessE (.fst (.snd (.snd .v2)))))).eval
          (.cons (t := SplitRo.AvlRoTableDefs.avlSearchResTy (.prod (.prod (PB 32) (PB 32)) .nat))
            searchRes (ρ₂ pos)) =
        (((rk, pos), ((match searchRes.1 with | none => 0 | some p => p.2 + 1),
          auxFgRootSess aux)) :
          (embedTy (.prod (.prod (B 32) fgPosTy) (.prod .nat (.list seqRootEntryTy)))).denote) := by
      rcases searchRes with ⟨_ | _, _⟩ <;> rfl
    erw [hArg, rootSessScan_atomic_eval]
    refine congrArg (_ >>= ·) (funext fun sessHit? => ?_)
    cases sessHit? with
    | some se =>
      simp only [aRootKdfAtomicE_eval, Expr.eval]
      rfl
    | none =>
      rcases searchRes with ⟨_ | rkCkIdx, path0⟩
      · dsimp only [Comp.eval, Expr.eval, Env.get, Expr.v0, Expr.v1, Expr.v2, Expr.v3]
        rw [liftGdh0_eval]
        refine congrArg (sampleRootPairAtom >>= ·) (funext fun rkCk => ?_)
        change (avlInsertAtPathC (I := SignalPqxdh.Costed.pqAuthSigAndDdhIface) F.K_cap
            (auxFgRootRoAvlE (.fst (.snd (.snd .v4))))
            (.snd .v2) (.snd (.snd (.snd (.snd .v4))))
            (.pair .v0 (auxFgRootCtrE (.fst (.snd (.snd .v4)))))).eval
            (.cons (t := .prod (PB 32) (PB 32)) rkCk
              (.cons (t := .opt (embedTy seqRootEntryTy)) none
                (.cons (t := SplitRo.AvlRoTableDefs.avlSearchResTy (.prod (.prod (PB 32) (PB 32)) .nat))
                  (none, path0) (ρ₂ pos)))) >>= _ = _
        rw [SplitRo.AvlRoTableSpec.avlInsertAtPathC_eval_congr F.K_cap]
        dsimp only [auxFgRootRoAvlE, auxFgRootCtrE, Expr.eval, Env.get,
          Expr.v0, Expr.v2, Expr.v4, ρ₂, tup0]
        refine congrArg (_ >>= ·) (funext fun fgRootRoAvl' => ?_)
        simp only [aRootKdfAtomicE_eval, simPrependRootE_eval, fgAuxMkE,
          auxFgSessE, auxFgCtrE, auxFgRoAvlE, auxFgRootSessE, auxRawAvlE,
          Expr.eval, Env.get]
        rfl
      · dsimp only [Comp.eval, Expr.eval, Env.get, Expr.v0, Expr.v1, Expr.v2, Expr.v3]
        simp only [aRootKdfAtomicE_eval, Expr.eval]
        rfl
  constructor
  ·
    dsimp only
    rw [hNewUnfold, legacyCoreArmEval_roRootQuery_eq, map_bind]
    refine MonadAttach.bind_congr_of_forall_mem_support (mkSecretPosAtom dh) fun pos hpos => ?_
    obtain ⟨isCan, rfl⟩ := mkSecretPosAtom_support hpos
    obtain ⟨path, hSearch, hInsSpec⟩ :=
      ShadowRelPair32.search_and_insert_spec
        (I := SignalPqxdh.Costed.pqAuthSigAndDdhIface)
        (auxFgRootRoAvlE (.fst (.snd (.snd .v1))))
        (.snd (.snd (.snd (.snd .v1))))
        (ρ₂ (Sum.inl (dh, isCan))) rk dh rfl hRel1
    have hTblEval :
        (auxFgRootRoAvlE (.fst (.snd (.snd .v1)))).eval (ρ₂ (Sum.inl (dh, isCan))) =
          auxFgRootRoAvl aux := rfl
    rw [hSearch]
    simp only [pure_bind, map_bind]
    have hScanEq :=
      findML_take_eq_shadowScanMinIdx
        (hRel0.1.mono_cap (by omega : c 0 + c 2 ≤ b.q_total))
        hFuelS (rk, dh) (rootMatchAtom rk (Sum.inl (dh, isCan)))
        (fun te hte k' htag => rootMatchAtom_on_ro (hValidRo te hte k' htag))
    rw [hScanEq]
    simp only [shadowScanMinIdx, bind_map_left]
    rcases hAvl :
        ((roEntriesOf (fun e => e.2.2) rootTagged).find?
          (fun p => p.1 == (rk, dh))).map Prod.snd with _ | ⟨rkCk0, idx_ro⟩
    · try rw [hAvl]
      dsimp only
      refine congrArg (Bind.bind _) (funext fun sessHit? => ?_)
      cases sessHit? with
      | some se =>
        simp only [map_pure, Prod.map]
        rfl
      | none =>
        simp only [Option.map_none, map_bind]
        refine congrArg (Bind.bind sampleRootPairAtom) (funext fun rkCk => ?_)
        obtain ⟨tbl', hInsEval, _⟩ :=
          hInsSpec hAvl hListCap hAvlCap (rk, (Sum.inl (dh, isCan), rkCk))
        rw [hTblEval] at hInsEval
        dsimp only at hInsEval
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
    obtain ⟨pos, hpos, hout⟩ := hout
    obtain ⟨isCan, rfl⟩ := mkSecretPosAtom_support hpos
    obtain ⟨path, hSearch, hInsSpec⟩ :=
      ShadowRelPair32.search_and_insert_spec
        (I := SignalPqxdh.Costed.pqAuthSigAndDdhIface)
        (auxFgRootRoAvlE (.fst (.snd (.snd .v1))))
        (.snd (.snd (.snd (.snd .v1))))
        (ρ₂ (Sum.inl (dh, isCan))) rk dh rfl hRel1
    have hTblEval :
        (auxFgRootRoAvlE (.fst (.snd (.snd .v1)))).eval (ρ₂ (Sum.inl (dh, isCan))) =
          auxFgRootRoAvl aux := rfl
    rw [hSearch, pure_bind, mem_support_bind_iff] at hout
    obtain ⟨sessHit?, _, hout⟩ := hout
    set avlHit? := ((roEntriesOf (fun e => e.2.2) rootTagged).find?
      (fun p => p.1 == (rk, dh))).map Prod.snd
    cases sessHit? with
    | some se =>
      rw [mem_support_pure_iff] at hout
      subst hout
      exact roRoot_inv_unchanged hroom hInv
    | none =>
      cases hAvl : avlHit? with
      | some rkCkIdx =>
        simp only [hAvl, mem_support_pure_iff] at hout
        subst hout
        exact roRoot_inv_unchanged hroom hInv
      | none =>
        simp only [hAvl, mem_support_bind_iff] at hout
        obtain ⟨rkCk, _, hout⟩ := hout
        let newRE : (embedTy rootEntryTy).denote := (rk, (Sum.inl (dh, isCan), rkCk))
        obtain ⟨tbl', hInsEval, hRelNew⟩ :=
          hInsSpec hAvl hListCap hAvlCap newRE
        rw [hTblEval] at hInsEval
        dsimp only [newRE] at hInsEval
        rw [hInsEval] at hout
        simp only [mem_support_pure_iff] at hout
        rcases hout with ⟨_, rfl, rfl⟩
        obtain ⟨hb0, hb1, hb2, _⟩ := bump_roRoot_counts (S := S) c rk dh
        refine ⟨hInv.counter_inv.bump (.roRootQuery rk dh) hroom,
          hb0.symm ▸ hInv.base_online,
          hb0.symm ▸ hInv.pows_len,
          hb0.symm ▸ hInv.resp_len,
          hb1.symm ▸ hInv.log_len,
          hb0.symm ▸ hb1.symm ▸ hInv.fg_shadow,
          ?_, hInv.raw_rel, hb1.symm ▸ hInv.raw_len⟩
        rw [hb0, hb2]
        refine ⟨⟨auxFgRootCtr aux, .ro (rk, dh), newRE⟩ :: rootTagged,
          hRelNew, hSessLen, ?_, ?_, ?_⟩
        · have hRoCons :
              (roEntriesOf (fun e : (embedTy rootEntryTy).denote => e.2.2)
                (⟨auxFgRootCtr aux, .ro (rk, dh), newRE⟩ :: rootTagged)).length =
              (roEntriesOf (fun e : (embedTy rootEntryTy).denote => e.2.2) rootTagged).length + 1 :=
            rfl
          rw [hRoCons]
          omega
        · simp only [List.length_cons]
          omega
        · intro te hte k' htag
          rcases List.mem_cons.mp hte with rfl | hmem
          · cases htag
            exact ⟨rfl, ⟨isCan, rfl⟩⟩
          · exact hValidRo te hmem k' htag

end Computational.Proofs.SignalPqxdh.Security.ReductionDsl.KindSplit.AuthGapDhKSimRoRoot
