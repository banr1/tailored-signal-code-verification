/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.Placed.BudgetPoolSync
public import LibsignalBinary.Proofs.Placed.BudgetVmSteps
public meta import LibsignalBinary.Proofs.Placed.BudgetVmSteps -- shake: keep
public meta import ProofLib -- shake: keep
public meta import Lean -- shake: keep
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Compose.Arms.R1b.DeserClonePlacedBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Compose.Arms.R1b.DeserCloneTailPlaced
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Compose.Arms.R1b.WorkFramePlacedFd
import Arm64.Trusted.Spec.Hoare
import Arm64.Trusted.Spec.SepLogic
import LibsignalBinary.Proofs.Common.SharedHelpers
meta import LibsignalBinary.Proofs.Common.SharedHelpers -- shake: keep
import LibsignalBinary.Proofs.SignalSession.Cli.Main.Proofs.CallSites
import LibsignalBinary.Proofs.SignalSession.Cli.Main.Proofs.M4Layout
import LibsignalBinary.Proofs.SignalSession.Cli.Run.Compose.Arms.R1b.CommonPlacedBudget
import LibsignalBinary.Proofs.SignalSession.Cli.Run.Compose.Arms.R1b.ReadKpkPlacedBudgetAux
import LibsignalBinary.Proofs.SignalSession.Cli.Run.Compose.Arms.R1b.ReadRegSpkPlacedBudgetAux
import LibsignalBinary.Proofs.SpqrV1.Kdf.HkdfToSlice
import LibsignalBinary.Proofs.TripleRatchet.GeneralizeEntry
import LibsignalBinary.Proofs.TripleRatchet.GeneralizeEntryEq

/-!
# `FdsGe3Closed`-Threaded Stage 4b Tail (`0x2744 → 0x27bc`) of Arm `R1b`

Proves `r1b_tail_2744_placed_fd` (`0x2744 → 0x27bc`, `FreeOnlyEvs`) on Block `579`, preserving
`FdsGe3Closed` across the Stage-2 to Stage-3 stack copy and `kpkBs`, `spkBs`, and `regBs`
deallocations.
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 200000
set_option linter.unusedSimpArgs false

namespace LibsignalBinary.Proofs.SignalSession.Cli.Run.Compose.Arms.R1b.DeserCloneTailPlacedBudgetAuxFd

open Arm64 Arm64.Process ProofLib ProofLib.ProgramReflection SepProp
open CryptoVerification (LibsignalHooks LibsignalPlacement lsρ)
open CryptoVerification.LibsignalTripleRatchet.Wire
  (sevenBytesHeadAt sevenBytesHeadAt_eq_tailAt sevenBytesTailAt)
open CryptoVerification.SignalSession (lsRustDeallocSymCli)
open CryptoVerification.SignalSession.Cli.MainHops (RunCall ownedBytes sepWPp_weaken_pre)
open CryptoVerification.SignalSession.Cli.Run.Placed
  (blkLib_eq_579 blkPC_579 blkPl_579 lsProg_579)
open CryptoVerification.SignalSession.Cli.RunCompose
  (Init1Data PanicK RunSem r1b_CodeOk r1b_StackBounds r1b_bind_state_placed
   r1b_cell8_to_region r1b_entails_frame_core r1b_fsp_align r1b_head7_to_region r1b_join_region
   r1b_opkStage2At r1b_opkStage3At r1b_ownedBytes_cap0_emp r1b_sepWPp_frame_core
   runFsp runPcPlaced_eq runProgPlaced)
open CryptoVerification.SignalSession.Cli.RunSkeleton (RunBudgets runFrame)
open LibsignalBinary.Heap
  (AllocCostModel AllocEvent BudgetLimits FreeOnlyEvs RustCliAllocBudget VmPreserved
   rustDeallocEvents)
open LibsignalBinary.Proofs.Placed.BudgetPoolSync (hooksException sepWP_seg_ls_vm)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Compose.Arms.R1b.CommonPlacedBudget
  (r1b_call_dealloc_ownedBytes_placed)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Compose.Arms.R1b.ReadKpkPlacedBudgetAux
  (r1b_seq_lscro_oom)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Compose.Arms.R1b.ReadRegSpkPlacedBudgetAux
  (blk579_noSvc0)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Compose.Arms.R1b.WorkFramePlacedFd
  (r1b_OkCtxPlacedFd)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.SkeletonPlacedBudget (RunHooksPlaced)

attribute [local irreducible] Program.fetch Program.externAt?
attribute [local simp, local arm64_norm, local wp_norm]
  runPcPlaced_eq BitVec.ofNat_eq_ofNat
  State.fs_writeReg64 State.fs_writeReg32 State.fs_writeVReg128
  State.fs_advancePC State.fs_setPC State.fs_setPState
  State.fs_setMem State.fs_setStatus State.fs_appendTrace

@[local simp, local arm64_norm, local wp_norm]
private theorem r1b_fs_setMem_local (s : State) (m : Memory) : (s.setMem m).fs = s.fs := rfl

@[local simp, local arm64_norm, local wp_norm]
private theorem r1b_fs_setPState_local (s : State) (ps : PState) : (s.setPState ps).fs = s.fs := rfl

local macro (priority := high) "r1b_ac_dct" : tactic =>
  `(tactic| ((try dsimp +zetaDelta only) <;> first | rfl | simp only [emp_sepConj] | sep_ac_rfl))

private meta def r1bStripLetsDCT : Nat → Lean.Expr → Lean.Expr
  | 0, e => e
  | n + 1, .letE _ _ v b _ => r1bStripLetsDCT n (b.instantiate1 v)
  | n + 1, .mdata _ e => r1bStripLetsDCT n e
  | _, e => e

private meta def r1bSplitSepDCT : Nat → Lean.Expr → Lean.Expr → Array Lean.Expr
  | 0, _, e => #[e]
  | fuel + 1, sepSample, e =>
    let e := r1bStripLetsDCT 64 e
    let fn := sepSample.getAppFn.constName!
    let ar := sepSample.getAppNumArgs
    if e.isAppOfArity fn ar then
      r1bSplitSepDCT fuel sepSample (e.getArg! (ar - 2)) ++
        r1bSplitSepDCT fuel sepSample (e.getArg! (ar - 1))
    else #[e]

private meta def r1bIsDefEqPureDCT (x a : Lean.Expr) : Lean.Elab.TermElabM Bool := do
  let x := r1bStripLetsDCT 64 x; let a := r1bStripLetsDCT 64 a
  let xf := x.getAppFn; let af := a.getAppFn
  if xf.constName? != af.constName? then return false
  let n := x.getAppNumArgs
  if n != a.getAppNumArgs then return false
  let st ← Lean.saveState
  let mut ok ← if xf.constName?.isNone then
      if xf.isFVar != af.isFVar || xf.isProj != af.isProj then pure false
      else Lean.Meta.withReducibleAndInstances <| Lean.Meta.isDefEq xf af
    else pure true
  for i in [0:n] do
    if ok then
      ok ← Lean.Meta.withReducibleAndInstances <| Lean.Meta.isDefEq (x.getArg! i) (a.getArg! i)
  st.restore
  return ok

private meta def r1bComputeRestDCT (ctxName : String) (p a1 : Lean.Expr) :
    Lean.Elab.TermElabM Lean.Expr := do
  let sepTy := Lean.mkConst ``SepProp []
  let sepSample ← Lean.Elab.Term.elabTerm (← `(emp ∗ emp)) (some sepTy)
  let empExpr ← Lean.Elab.Term.elabTerm (← `(emp)) (some sepTy)
  let ps := (r1bSplitSepDCT 64 sepSample (← Lean.instantiateMVars p)).toList
  let a1s := (r1bSplitSepDCT 64 sepSample (← Lean.instantiateMVars a1)).toList
  let mut rem := ps
  for a in a1s do
    let mut removed := false
    let mut next : List Lean.Expr := []
    for x in rem do
      if !removed && (← r1bIsDefEqPureDCT x a) then removed := true
      else next := next.concat x
    if !removed then
      throwError "{ctxName}: unmatched atom:\n  {a}\nin:\n  {rem}"
    rem := next
  let ar := sepSample.getAppNumArgs
  let mkSep (l r : Lean.Expr) : Lean.Expr :=
    sepSample.withApp fun f args => Lean.mkAppN f (args.extract 0 (ar - 2) ++ #[l, r])
  match rem.reverse with
  | [] => return empExpr
  | last :: rest => return rest.foldl (fun acc x => mkSep x acc) last

local elab (priority := high) "r1b_entails_frame_dct " t1:term:arg h:term:arg t2:term:arg :
    term <= expectedType => do
  let exp ← Lean.instantiateMVars expectedType
  if exp.isMVar then Lean.Elab.Term.tryPostpone
  let entSample ← Lean.Elab.Term.elabTerm (← `(emp ⊢ emp)) none
  let ear := entSample.getAppNumArgs
  let expS := r1bStripLetsDCT 64 exp
  let p := expS.getArg! (ear - 2)
  let q := expS.getArg! (ear - 1)
  if (← Lean.instantiateMVars p).isMVar then Lean.Elab.Term.tryPostpone
  if (← Lean.instantiateMVars q).isMVar then Lean.Elab.Term.tryPostpone
  let hExpr ← Lean.Elab.Term.elabTerm h none
  let hTy := r1bStripLetsDCT 64 (← Lean.instantiateMVars (← Lean.Meta.inferType hExpr))
  let a1 := hTy.getArg! (ear - 2)
  let a2 := hTy.getArg! (ear - 1)
  let r ← r1bComputeRestDCT "r1b_entails_frame_dct" p a1
  let sepTy := Lean.mkConst ``SepProp []
  let empExpr ← Lean.Elab.Term.elabTerm (← `(emp)) (some sepTy)
  let sepSample ← Lean.Elab.Term.elabTerm (← `(emp ∗ emp)) (some sepTy)
  let sar := sepSample.getAppNumArgs
  let mkSep (x y : Lean.Expr) : Lean.Expr :=
    sepSample.withApp fun f args => Lean.mkAppN f (args.extract 0 (sar - 2) ++ #[x, y])
  let rIsEmp ← r1bIsDefEqPureDCT r empExpr
  if rIsEmp then
    let eq1 ← Lean.Meta.mkEq p a1
    let eq2 ← Lean.Meta.mkEq a2 q
    let h1Expr ← Lean.Elab.Term.elabTerm t1 (some eq1)
    let h2Expr ← Lean.Elab.Term.elabTerm t2 (some eq2)
    Lean.Meta.mkAppM ``Entails.trans #[← Lean.Meta.mkAppM ``Entails.of_eq #[h1Expr],
      ← Lean.Meta.mkAppM ``Entails.trans #[hExpr, ← Lean.Meta.mkAppM ``Entails.of_eq #[h2Expr]]]
  else
    let eq1 ← Lean.Meta.mkEq p (mkSep a1 r)
    let eq2 ← Lean.Meta.mkEq (mkSep a2 r) q
    let h1Expr ← Lean.Elab.Term.elabTerm t1 (some eq1)
    let h2Expr ← Lean.Elab.Term.elabTerm t2 (some eq2)
    Lean.Meta.mkAppOptM ``r1b_entails_frame_core
      #[some a1, some a2, some r, some p, some q, h1Expr, hExpr, h2Expr]

local elab (priority := high) "r1b_sepWPp_frame_dct " t1:term:arg h:term:arg t2:term:arg hk:term:arg :
    term <= expectedType => do
  let exp ← Lean.instantiateMVars expectedType
  if exp.isMVar then Lean.Elab.Term.tryPostpone
  let expS := r1bStripLetsDCT 64 exp
  let args := expS.getAppArgs
  let prog := args[0]!; let ret := args[1]!; let st := args[2]!; let p := args[3]!
  let q := args[4]!; let qp := args[5]!; let oom := args[6]!
  let entSample ← Lean.Elab.Term.elabTerm (← `(emp ⊢ emp)) none
  let ear := entSample.getAppNumArgs
  let hExpr ← Lean.Elab.Term.elabTerm h none
  let hTy := r1bStripLetsDCT 64 (← Lean.instantiateMVars (← Lean.Meta.inferType hExpr))
  let a1 := hTy.getArg! (ear - 2)
  let a2 := hTy.getArg! (ear - 1)
  let r ← r1bComputeRestDCT "r1b_sepWPp_frame_dct" p a1
  let sepTy := Lean.mkConst ``SepProp []
  let empExpr ← Lean.Elab.Term.elabTerm (← `(emp)) (some sepTy)
  let sepSample ← Lean.Elab.Term.elabTerm (← `(emp ∗ emp)) (some sepTy)
  let sar := sepSample.getAppNumArgs
  let mkSep (x y : Lean.Expr) : Lean.Expr :=
    sepSample.withApp fun f args => Lean.mkAppN f (args.extract 0 (sar - 2) ++ #[x, y])
  let rIsEmp ← r1bIsDefEqPureDCT r empExpr
  if rIsEmp then
    let eq1 ← Lean.Meta.mkEq p a1
    let eq2 ← Lean.Meta.mkEq a2 a2
    let h1Expr ← Lean.Elab.Term.elabTerm t1 (some eq1)
    let h2Expr ← Lean.Elab.Term.elabTerm t2 (some eq2)
    let hkTy := Lean.mkAppN expS.getAppFn #[prog, ret, st, a2, q, qp, oom]
    let hkExpr ← Lean.Elab.Term.elabTerm hk (some hkTy)
    let hent ← Lean.Meta.mkAppM ``Entails.trans #[← Lean.Meta.mkAppM ``Entails.of_eq #[h1Expr],
      ← Lean.Meta.mkAppM ``Entails.trans #[hExpr, ← Lean.Meta.mkAppM ``Entails.of_eq #[h2Expr]]]
    Lean.Meta.mkAppM ``sepWPp_weaken_pre #[hent, hkExpr]
  else
    let a2IsEmp ← r1bIsDefEqPureDCT a2 empExpr
    let p' := if a2IsEmp then r else mkSep a2 r
    let eq1 ← Lean.Meta.mkEq p (mkSep a1 r)
    let eq2 ← Lean.Meta.mkEq (mkSep a2 r) p'
    let h1Expr ← Lean.Elab.Term.elabTerm t1 (some eq1)
    let h2Expr ← Lean.Elab.Term.elabTerm t2 (some eq2)
    let hkTy := Lean.mkAppN expS.getAppFn #[prog, ret, st, p', q, qp, oom]
    let hkExpr ← Lean.Elab.Term.elabTerm hk (some hkTy)
    Lean.Meta.mkAppOptM ``r1b_sepWPp_frame_core
      #[some prog, some ret, some st, some a1, some a2, some r, some p, some p',
        some q, some qp, some oom, h1Expr, hExpr, h2Expr, hkExpr]

local elab:10 (priority := high) "r1b_call_frame_dct" "<|" h:term:10 : term <= expectedType => do
  let exp ← Lean.instantiateMVars expectedType
  if exp.isMVar then Lean.Elab.Term.tryPostpone
  let expS := r1bStripLetsDCT 64 exp
  let hExpr ← Lean.Elab.Term.elabTerm h none
  let hTy0 := r1bStripLetsDCT 64 (← Lean.instantiateMVars (← Lean.Meta.inferType hExpr))
  for idx in [0, 1, 2, 4, 5, 6] do
    if !(← Lean.Meta.withReducibleAndInstances <| Lean.Meta.isDefEq (hTy0.getArg! idx) (expS.getArg! idx)) then
      discard <| Lean.Meta.isDefEq (hTy0.getArg! idx) (expS.getArg! idx)
  let p ← Lean.instantiateMVars (expS.getArg! 3)
  let p' ← Lean.instantiateMVars ((r1bStripLetsDCT 64 (← Lean.instantiateMVars hTy0)).getArg! 3)
  let sepTy := Lean.mkConst ``SepProp []
  let sepSample ← Lean.Elab.Term.elabTerm (← `(emp ∗ emp)) (some sepTy)
  let empExpr ← Lean.Elab.Term.elabTerm (← `(emp)) (some sepTy)
  let sar := sepSample.getAppNumArgs
  let mkSep (x y : Lean.Expr) : Lean.Expr :=
    sepSample.withApp fun f args => Lean.mkAppN f (args.extract 0 (sar - 2) ++ #[x, y])
  let ps := (r1bSplitSepDCT 64 sepSample p).toList
  let p's := (r1bSplitSepDCT 64 sepSample p').toList
  let mut mvarFOpt : Option Lean.Expr := none
  let mut a1s : List Lean.Expr := []
  for a in p's do
    let ai ← Lean.instantiateMVars a
    if mvarFOpt.isNone && ai.isMVar then mvarFOpt := some ai
    else a1s := a1s.concat ai
  let mut rem := ps
  for a in a1s do
    let mut removed := false
    let mut next : List Lean.Expr := []
    for x in rem do
      if !removed && (← r1bIsDefEqPureDCT x a) then removed := true
      else next := next.concat x
    if !removed then
      throwError "r1b_call_frame_dct: unmatched callee atom:\n  {a}\nin:\n  {rem}"
    rem := next
  let remProd := match rem.reverse with
    | [] => empExpr
    | last :: rest => rest.foldl (fun acc x => mkSep x acc) last
  if let some mf := mvarFOpt then
    discard <| Lean.Meta.isDefEq mf remProd
  let eqTy ← Lean.Meta.mkEq (← Lean.instantiateMVars p) (← Lean.instantiateMVars p')
  let eqProof ← Lean.Elab.Term.elabTerm (← `(by r1b_ac_dct)) (some eqTy)
  let ent ← Lean.Meta.mkAppM ``Entails.of_eq #[eqProof]
  Lean.Meta.mkAppM ``sepWPp_weaken_pre #[ent, hExpr]


private theorem r1b_stage2_close_stage3 (fsp : BitVec 64)
    (spkW0 : BitVec 64) (spkW8 : BitVec 32) (spkW16 spkW24 : BitVec 64)
    (b0 b1 b2 b3 b4 b5 b6 : BitVec 8)
    (s2_b0 s2_b1 s2_b2 s2_b3 s2_b4 s2_b5 s2_b6 : BitVec 8)
    (c0 c1 c2 c3 c4 c5 c6 : BitVec 8)
    (w0e0 w0e4 w9 s2_w9 c9 : BitVec 32)
    (w13 s2_w13 c13 : BitVec 16)
    (w15 w23 s2_w23 c23 : BitVec 64)
    (b31 s2_b31 c31 : BitVec 8) :
    r1b_opkStage2At fsp spkW0 spkW8 spkW16 spkW24
      b0 b1 b2 b3 b4 b5 b6
      s2_b0 s2_b1 s2_b2 s2_b3 s2_b4 s2_b5 s2_b6
      c0 c1 c2 c3 c4 c5 c6
      w0e0 w0e4 w9 s2_w9 c9 w13 s2_w13 c13 w15 w23 s2_w23 c23 b31 s2_b31 c31 ⊢
    r1b_opkStage3At fsp spkW0 spkW8 spkW16 spkW24
      c0 c1 c2 c3 c4 c5 c6 w0e0 w0e4 c9 c13 w15 c23 c31 := by
  dsimp only [r1b_opkStage2At, r1b_opkStage3At]
  have h220 :
      ((fsp + 0x220#64) ↦₆₄ w23) ∗ ((fsp + 0x228#64) ↦₈ b31) ∗
        memRegion (fsp + 0x229#64) 0x37 ⊢
        memRegion (fsp + 0x220#64) 0x40 := by
    refine Entails.trans (r1b_entails_frame_dct (by r1b_ac_dct)
      (sepConj_mono (pointsTo64_entails_memRegion _ _) (r1b_cell8_to_region _ _)) (by r1b_ac_dct)) ?_
    simp only [sepConj_assoc]
    rw [r1b_join_region fsp 0x228 1 0x37, r1b_join_region fsp 0x220 8 0x38]
    exact Entails.of_eq (by r1b_ac_dct)
  have h2c0 :
      memRegion (fsp + 0x2c0#64) 0x40 ∗
        ((fsp + 0x300#64) ↦₃₂ s2_w9) ∗ ((fsp + 0x304#64) ↦₁₆ s2_w13) ∗
        memRegion (fsp + 0x306#64) 0x1a ∗
        ((fsp + 0x320#64) ↦₆₄ s2_w23) ∗ ((fsp + 0x328#64) ↦₈ s2_b31) ∗
        memRegion (fsp + 0x329#64) 0x57 ∗
        sevenBytesHeadAt (fsp + 0x380#64) s2_b0 s2_b1 s2_b2 s2_b3 s2_b4 s2_b5 s2_b6 ∗
        memRegion (fsp + 0x387#64) 0x31 ∗
        sevenBytesHeadAt (fsp + 0x3b8#64) b0 b1 b2 b3 b4 b5 b6 ∗
        memRegion (fsp + 0x3bf#64) 0x19 ∗
        ((fsp + 0x3d8#64) ↦₃₂ w9) ∗ ((fsp + 0x3dc#64) ↦₁₆ w13) ∗
        memRegion (fsp + 0x3de#64) 0xf2 ⊢
        memRegion (fsp + 0x2c0#64) 0x210 := by
    refine Entails.trans (r1b_entails_frame_dct (by r1b_ac_dct)
      (sepConj_mono (pointsTo32_entails_memRegion _ _)
        (sepConj_mono (pointsTo16_entails_memRegion _ _)
          (sepConj_mono (pointsTo64_entails_memRegion _ _)
            (sepConj_mono (r1b_cell8_to_region _ _)
              (sepConj_mono (r1b_head7_to_region _ _ _ _ _ _ _ _)
                (sepConj_mono (r1b_head7_to_region _ _ _ _ _ _ _ _)
                  (sepConj_mono (pointsTo32_entails_memRegion _ _)
                    (pointsTo16_entails_memRegion _ _)))))))) (by r1b_ac_dct)) ?_
    refine Entails.trans (Entails.of_eq (show _ =
      memRegion (fsp + 0x2c0#64) 0x40 ∗
        memRegion (fsp + 0x300#64) 4 ∗ memRegion (fsp + 0x304#64) 2 ∗
        memRegion (fsp + 0x306#64) 0x1a ∗
        memRegion (fsp + 0x320#64) 8 ∗ memRegion (fsp + 0x328#64) 1 ∗
        memRegion (fsp + 0x329#64) 0x57 ∗
        memRegion (fsp + 0x380#64) 7 ∗ memRegion (fsp + 0x387#64) 0x31 ∗
        memRegion (fsp + 0x3b8#64) 7 ∗ memRegion (fsp + 0x3bf#64) 0x19 ∗
        memRegion (fsp + 0x3d8#64) 4 ∗ memRegion (fsp + 0x3dc#64) 2 ∗
        memRegion (fsp + 0x3de#64) 0xf2 by r1b_ac_dct)) ?_
    rw [r1b_join_region fsp 0x3dc 2 0xf2,
      r1b_join_region fsp 0x3d8 4 0xf4,
      r1b_join_region fsp 0x3bf 0x19 0xf8,
      r1b_join_region fsp 0x3b8 7 0x111,
      r1b_join_region fsp 0x387 0x31 0x118,
      r1b_join_region fsp 0x380 7 0x149,
      r1b_join_region fsp 0x329 0x57 0x150,
      r1b_join_region fsp 0x328 1 0x1a7,
      r1b_join_region fsp 0x320 8 0x1a8,
      r1b_join_region fsp 0x306 0x1a 0x1b0,
      r1b_join_region fsp 0x304 2 0x1ca,
      r1b_join_region fsp 0x300 4 0x1cc,
      r1b_join_region fsp 0x2c0 0x40 0x1d0]
    exact Entails.refl _
  exact r1b_entails_frame_dct (by r1b_ac_dct) (sepConj_mono h220 h2c0) (by r1b_ac_dct)


set_option maxHeartbeats 800000 in
/-- `FdsGe3Closed`-threaded Stage-2 to Stage-3 copy (`0x2744 → 0x277c`) and buffer deallocations (`0x277c → 0x27bc`). -/
theorem r1b_tail_2744_placed_fd [LibsignalPlacement] {M : AllocCostModel}
    {S : RunSem} {A : RustCliAllocBudget M} {lim : BudgetLimits} {st : M.σ}
    {H : LibsignalHooks} {B : RunBudgets}
    {g : RunCall} {d : Init1Data} {s0 s : State} {resStack : Nat}
    {spkW0 : BitVec 64} {spkW8 spkW12 : BitVec 32} {spkW16 spkW24 : BitVec 64}
    {b0 b1 b2 b3 b4 b5 b6 : BitVec 8}
    {s2_b0 s2_b1 s2_b2 s2_b3 s2_b4 s2_b5 s2_b6 : BitVec 8}
    {c0_in c1_in c2_in c3_in c4_in c5_in c6_in : BitVec 8}
    {w0e0 w0e4 w9 s2_w9 c9_in : BitVec 32}
    {w13 s2_w13 c13_in : BitVec 16}
    {w15 w23 s2_w23 c23_in : BitVec 64}
    {b31 s2_b31 c31_in : BitVec 8}
    {opkFlag kpkId : BitVec 32}
    {kpkCap kpkPtr spkCap spkPtr regCap regPtr : BitVec 64}
    {kpkBs spkBs regBs : List (BitVec 8)}
    {F : SepProp} {Q Qp : State → SepProp → Prop} {oom : State → SepProp}
    (hh : RunHooksPlaced A lim H)
    (hbnd : r1b_StackBounds B resStack)
    (hok : r1b_OkCtxPlacedFd r1b_CodeOk S g d s0 s 0x2744)
    (hx23 : s.readReg64 (.gpr 23#5) = kpkId.zeroExtend 64)
    (hx24 : s.readReg64 (.gpr 24#5) = runFsp s0 + 0x380#64)
    (hx25 : s.readReg64 (.gpr 25#5) = opkFlag.zeroExtend 64)
    (hx26 : s.readReg64 (.gpr 26#5) = opkFlag.zeroExtend 64)
    (hx27 : s.readReg64 (.gpr 27#5) = spkW12.zeroExtend 64)
    (hx28 : s.readReg64 (.gpr 28#5) = 64#64)
    (hpanic : PanicK g s0 Qp)
    (hk : ∀ (sf : State) (evs : List AllocEvent),
      FreeOnlyEvs evs →
      r1b_OkCtxPlacedFd r1b_CodeOk S g d s0 sf 0x27bc →
      sf.readReg64 (.gpr 23#5) = kpkId.zeroExtend 64 →
      sf.readReg64 (.gpr 24#5) = (spkW12.zeroExtend 64) <<< 32 →
      sf.readReg64 (.gpr 25#5) = opkFlag.zeroExtend 64 →
      sf.readReg64 (.gpr 26#5) = opkFlag.zeroExtend 64 →
      sf.readReg64 (.gpr 28#5) = 64#64 →
      let fsp := runFsp s0
      SepWPp (runProgPlaced H) (s0.readReg64 .lr) sf
        (r1b_opkStage3At fsp spkW0 spkW8 spkW16 spkW24
            s2_b0 s2_b1 s2_b2 s2_b3 s2_b4 s2_b5 s2_b6
            w0e0 w0e4 s2_w9 s2_w13 w15 s2_w23 s2_b31 ∗
          ((fsp + 0x128#64) ↦₆₄ kpkPtr) ∗ ((fsp + 0x150#64) ↦₆₄ kpkCap) ∗
          ((fsp + 0x168#64) ↦₆₄ spkPtr) ∗ ((fsp + 0x170#64) ↦₆₄ spkCap) ∗
          ((fsp + 0x198#64) ↦₆₄ regCap) ∗ ((fsp + 0x1a0#64) ↦₆₄ regPtr) ∗
          stackAt fsp (resStack - runFrame) ∗ A.pool lim (M.stepEvents evs st) sf ∗ F)
        Q Qp oom) :
    let fsp := runFsp s0
    SepWPp (runProgPlaced H) (s0.readReg64 .lr) s
      (r1b_opkStage2At fsp spkW0 spkW8 spkW16 spkW24
          b0 b1 b2 b3 b4 b5 b6
          s2_b0 s2_b1 s2_b2 s2_b3 s2_b4 s2_b5 s2_b6
          c0_in c1_in c2_in c3_in c4_in c5_in c6_in
          w0e0 w0e4 w9 s2_w9 c9_in w13 s2_w13 c13_in w15 w23 s2_w23 c23_in b31 s2_b31 c31_in ∗
        ownedBytes A.repAlloc kpkCap kpkPtr (BitVec.ofNat 64 kpkBs.length) kpkBs ∗
        ownedBytes A.repAlloc spkCap spkPtr (BitVec.ofNat 64 spkBs.length) spkBs ∗
        ownedBytes A.repAlloc regCap regPtr 4#64 regBs ∗
        ((fsp + 0x128#64) ↦₆₄ kpkPtr) ∗ ((fsp + 0x150#64) ↦₆₄ kpkCap) ∗
        ((fsp + 0x168#64) ↦₆₄ spkPtr) ∗ ((fsp + 0x170#64) ↦₆₄ spkCap) ∗
        ((fsp + 0x198#64) ↦₆₄ regCap) ∗ ((fsp + 0x1a0#64) ↦₆₄ regPtr) ∗
        stackAt fsp (resStack - runFrame) ∗ A.pool lim st s ∗ F)
      Q Qp oom := by
  intro fsp
  change s.readReg64 (.gpr 24#5) = fsp + 0x380#64 at hx24
  let _ := hx23; let _ := hx24; let _ := hx25; let _ := hx26; let _ := hx27; let _ := hx28
  have hst := hok.st
  have hs_run : s.status = .Running := hst.run
  have hs_sp : s.sp = fsp := hst.sp
  let _ := hs_run; let _ := hs_sp
  have hal : fsp &&& 15#64 = 0#64 := r1b_fsp_align hst.sp hst.spAligned
  have hal380 : (fsp + 0x380#64) &&& 3#64 = 0#64 :=
    (fun (x : BitVec 64) (hx : x &&& 15#64 = 0#64) => show (x + 0x380#64) &&& 3#64 = 0#64 by bv_bits) fsp hal
  have hal200 : (fsp + 0x200#64) &&& 3#64 = 0#64 :=
    (fun (x : BitVec 64) (hx : x &&& 15#64 = 0#64) => show (x + 0x200#64) &&& 3#64 = 0#64 by bv_bits) fsp hal
  have hal300 : (fsp + 0x300#64) &&& 3#64 = 0#64 :=
    (fun (x : BitVec 64) (hx : x &&& 15#64 = 0#64) => show (x + 0x300#64) &&& 3#64 = 0#64 by bv_bits) fsp hal
  have hal304 : (fsp + 0x304#64) &&& 1#64 = 0#64 :=
    (fun (x : BitVec 64) (hx : x &&& 15#64 = 0#64) => show (x + 0x304#64) &&& 1#64 = 0#64 by bv_bits) fsp hal
  have hal320 : (fsp + 0x320#64) &&& 7#64 = 0#64 :=
    (fun (x : BitVec 64) (hx : x &&& 15#64 = 0#64) => show (x + 0x320#64) &&& 7#64 = 0#64 by bv_bits) fsp hal
  have hal1f8 : (fsp + 0x1f8#64) &&& 3#64 = 0#64 :=
    (fun (x : BitVec 64) (hx : x &&& 15#64 = 0#64) => show (x + 0x1f8#64) &&& 3#64 = 0#64 by bv_bits) fsp hal
  have hal1fc : (fsp + 0x1fc#64) &&& 1#64 = 0#64 :=
    (fun (x : BitVec 64) (hx : x &&& 15#64 = 0#64) => show (x + 0x1fc#64) &&& 1#64 = 0#64 by bv_bits) fsp hal
  have hal1e8 : (fsp + 0x1e8#64) &&& 7#64 = 0#64 :=
    (fun (x : BitVec 64) (hx : x &&& 15#64 = 0#64) => show (x + 0x1e8#64) &&& 7#64 = 0#64 by bv_bits) fsp hal
  let _ := hal; let _ := hal380; let _ := hal200; let _ := hal300; let _ := hal304
  let _ := hal320; let _ := hal1f8; let _ := hal1fc; let _ := hal1e8
  have hpc0 := hst.pc
  change s.pc = (blkPl_579).base + 10052#64 at hpc0
  dsimp only [r1b_opkStage2At, sevenBytesHeadAt]
  simp only [BitVec.add_assoc, BitVec.reduceAdd, sepConj_assoc]
  have hpc := hpc0; have hrun := hst.run; have hsp : s.sp = fsp := hst.sp
  apply r1b_seq_lscro_oom (mid := (blkPl_579).base + 10056#64) hst.inv
  dsimp only [runProgPlaced, lsProg_579]
  apply sepWP_seg_ls_vm (Q := (blkPC_579).rebase (blkPl_579).base (hooksException _))
    blkLib_eq_579 blk579_noSvc0 (mid := (blkPl_579).base + 10056#64)
  intro _m_strip; wp_steps
  refine SepWP.done (by simp only [wp_norm, arm64_norm, *]; try bv_omega)
    (by simp only [wp_norm, arm64_norm, *]) fun _m_real hnsp => ?_
  have hvmp1 : VmPreserved s _ :=
    hnsp.toVmPreserved (by simp only [wp_norm, arm64_norm, *])
  simp -failIfUnchanged only [State.setMem_setMem] at hvmp1 ⊢
  apply SepWP.done (by simp only [wp_norm, arm64_norm, *])
    (by simp only [wp_norm, arm64_norm, *])
  clear hpc hrun hsp
  refine r1b_bind_state_placed fun sm1 hsm1 hinv1 => by
    have hvm1 : VmPreserved s sm1 := hsm1 ▸ hvmp1
    rw [← A.pool_transport lim st s sm1 hvm1]
    have hflip380 :
        ((fsp + 0x380#64) ↦₃₂ (s2_b3 ++ s2_b2 ++ s2_b1 ++ s2_b0)) ∗
          ((fsp + 0x384#64) ↦₈ s2_b4) ∗ ((fsp + 0x385#64) ↦₈ s2_b5) ∗
          ((fsp + 0x386#64) ↦₈ s2_b6) ⊢
        ((fsp + 0x380#64) ↦₈ s2_b0) ∗ ((fsp + 0x381#64) ↦₈ s2_b1) ∗
          ((fsp + 0x382#64) ↦₈ s2_b2) ∗
          ((fsp + 0x383#64) ↦₃₂ (s2_b6 ++ s2_b5 ++ s2_b4 ++ s2_b3)) := by
      have heq := sevenBytesHeadAt_eq_tailAt (fsp + 0x380#64)
        s2_b0 s2_b1 s2_b2 s2_b3 s2_b4 s2_b5 s2_b6
      dsimp only [sevenBytesHeadAt, sevenBytesTailAt] at heq
      simp only [BitVec.add_assoc, BitVec.reduceAdd] at heq
      rw [heq]; exact Entails.refl _
    refine r1b_sepWPp_frame_dct (by r1b_ac_dct) hflip380 (by r1b_ac_dct) ?_
    simp only [sepConj_assoc]
    have hpc : sm1.pc = (blkPl_579).base + 10056#64 := by simp only [hsm1, wp_norm, arm64_norm]
    have hrun : sm1.status = .Running := by simp only [hsm1, wp_norm, arm64_norm, hst.run]
    have hsp : sm1.sp = fsp := by simpa only [hsm1, wp_norm, arm64_norm] using hst.sp
    have hx24_1 : sm1.readReg64 (.gpr 24#5) = fsp + 0x380#64 := by
      simpa only [hsm1, wp_norm, arm64_norm] using hx24
    let _ := hx24_1
    apply r1b_seq_lscro_oom (mid := (blkPl_579).base + 10072#64) hinv1
    apply sepWP_seg_ls_vm (Q := (blkPC_579).rebase (blkPl_579).base (hooksException _))
      blkLib_eq_579 blk579_noSvc0 (mid := (blkPl_579).base + 10072#64)
    intro _m_strip; wp_steps
    refine SepWP.done (by simp only [wp_norm, arm64_norm, *]; try bv_omega)
      (by simp only [wp_norm, arm64_norm, *]) fun _m_real hnsp => ?_
    have hvmp2 : VmPreserved sm1 _ :=
      hnsp.toVmPreserved (by simp only [wp_norm, arm64_norm, *])
    simp -failIfUnchanged only [State.setMem_setMem] at hvmp2 ⊢
    apply SepWP.done (by simp only [wp_norm, arm64_norm, *])
      (by simp only [wp_norm, arm64_norm, *])
    clear hpc hrun hsp
    refine r1b_bind_state_placed fun sm2 hsm2 hinv2 => by
      have hvm2 : VmPreserved sm1 sm2 := hsm2 ▸ hvmp2
      rw [← A.pool_transport lim st sm1 sm2 hvm2]
      have hw200 : (((((s2_b3 ++ s2_b2 ++ s2_b1 ++ s2_b0).zeroExtend 64).truncate 32) : BitVec 32)) =
          (s2_b3 ++ s2_b2 ++ s2_b1 ++ s2_b0) := by bv_bits
      let _ := hw200
      simp -failIfUnchanged only [hsm1, arm64_norm, hw200]
      have hflip200 :
          ((fsp + 0x200#64) ↦₃₂ (s2_b3 ++ s2_b2 ++ s2_b1 ++ s2_b0)) ∗
            ((fsp + 0x204#64) ↦₈ c4_in) ∗ ((fsp + 0x205#64) ↦₈ c5_in) ∗
            ((fsp + 0x206#64) ↦₈ c6_in) ⊢
          ((fsp + 0x200#64) ↦₈ s2_b0) ∗ ((fsp + 0x201#64) ↦₈ s2_b1) ∗
            ((fsp + 0x202#64) ↦₈ s2_b2) ∗
            ((fsp + 0x203#64) ↦₃₂ (c6_in ++ c5_in ++ c4_in ++ s2_b3)) := by
        have heq := sevenBytesHeadAt_eq_tailAt (fsp + 0x200#64)
          s2_b0 s2_b1 s2_b2 s2_b3 c4_in c5_in c6_in
        dsimp only [sevenBytesHeadAt, sevenBytesTailAt] at heq
        simp only [BitVec.add_assoc, BitVec.reduceAdd] at heq
        rw [heq]; exact Entails.refl _
      refine r1b_sepWPp_frame_dct (by r1b_ac_dct) hflip200 (by r1b_ac_dct) ?_
      simp only [sepConj_assoc]
      have hpc : sm2.pc = (blkPl_579).base + 10072#64 := by
        simp only [hsm2, hsm1, wp_norm, arm64_norm]
      have hrun : sm2.status = .Running := by
        simp only [hsm2, wp_norm, arm64_norm, hst.run]
      have hsp : sm2.sp = fsp := by
        simpa only [hsm2, hsm1, wp_norm, arm64_norm] using hst.sp
      have hx11_2 : sm2.readReg64 (.gpr 11#5) = fsp + 0x104#64 := by
        simp only [hsm2, hsm1, wp_norm, arm64_norm]
      let _ := hx11_2
      apply r1b_seq_lscro_oom (mid := (blkPl_579).base + 10108#64) hinv2
      apply sepWP_seg_ls_vm (Q := (blkPC_579).rebase (blkPl_579).base (hooksException _))
        blkLib_eq_579 blk579_noSvc0 (mid := (blkPl_579).base + 10108#64)
      intro _m_strip; wp_steps
      refine SepWP.done (by simp only [wp_norm, arm64_norm, *]; try bv_omega)
        (by simp only [wp_norm, arm64_norm, *]) fun _m_real hnsp => ?_
      have hvmp3 : VmPreserved sm2 _ :=
        hnsp.toVmPreserved (by simp only [wp_norm, arm64_norm, *])
      simp -failIfUnchanged only [State.setMem_setMem] at hvmp3 ⊢
      apply SepWP.done (by simp only [wp_norm, arm64_norm, *])
        (by simp only [wp_norm, arm64_norm, *])
      clear hpc hrun hsp
      refine r1b_bind_state_placed fun sm3 hsm3 hinv3 => by
        have hvm3 : VmPreserved sm2 sm3 := hsm3 ▸ hvmp3
        rw [← A.pool_transport lim st sm2 sm3 hvm3]
        have hback200 :
            ((fsp + 0x200#64) ↦₈ s2_b0) ∗ ((fsp + 0x201#64) ↦₈ s2_b1) ∗
              ((fsp + 0x202#64) ↦₈ s2_b2) ∗
              ((fsp + 0x203#64) ↦₃₂ (s2_b6 ++ s2_b5 ++ s2_b4 ++ s2_b3)) ⊢
            sevenBytesHeadAt (fsp + 0x200#64) s2_b0 s2_b1 s2_b2 s2_b3 s2_b4 s2_b5 s2_b6 := by
          have heq := (sevenBytesHeadAt_eq_tailAt (fsp + 0x200#64)
            s2_b0 s2_b1 s2_b2 s2_b3 s2_b4 s2_b5 s2_b6).symm
          dsimp only [sevenBytesTailAt] at heq
          simp only [BitVec.add_assoc, BitVec.reduceAdd] at heq
          rw [heq]; exact Entails.refl _
        have hback380 :
            ((fsp + 0x380#64) ↦₈ s2_b0) ∗ ((fsp + 0x381#64) ↦₈ s2_b1) ∗
              ((fsp + 0x382#64) ↦₈ s2_b2) ∗
              ((fsp + 0x383#64) ↦₃₂ (s2_b6 ++ s2_b5 ++ s2_b4 ++ s2_b3)) ⊢
            sevenBytesHeadAt (fsp + 0x380#64) s2_b0 s2_b1 s2_b2 s2_b3 s2_b4 s2_b5 s2_b6 := by
          have heq := (sevenBytesHeadAt_eq_tailAt (fsp + 0x380#64)
            s2_b0 s2_b1 s2_b2 s2_b3 s2_b4 s2_b5 s2_b6).symm
          dsimp only [sevenBytesTailAt] at heq
          simp only [BitVec.add_assoc, BitVec.reduceAdd] at heq
          rw [heq]; exact Entails.refl _
        have hback3b8 :
            ((fsp + 0x3b8#64) ↦₃₂ (b3 ++ b2 ++ b1 ++ b0)) ∗
              ((fsp + 0x3bc#64) ↦₈ b4) ∗ ((fsp + 0x3bd#64) ↦₈ b5) ∗
              ((fsp + 0x3be#64) ↦₈ b6) ⊢
            sevenBytesHeadAt (fsp + 0x3b8#64) b0 b1 b2 b3 b4 b5 b6 := by
          dsimp only [sevenBytesHeadAt]; simp only [BitVec.add_assoc, BitVec.reduceAdd]
          exact Entails.refl _
        refine r1b_sepWPp_frame_dct (by r1b_ac_dct)
          (sepConj_mono hback200 (sepConj_mono hback380 hback3b8)) (by r1b_ac_dct) ?_
        have hclose_s3 := r1b_stage2_close_stage3 fsp spkW0 spkW8 spkW16 spkW24
          b0 b1 b2 b3 b4 b5 b6
          s2_b0 s2_b1 s2_b2 s2_b3 s2_b4 s2_b5 s2_b6
          s2_b0 s2_b1 s2_b2 s2_b3 s2_b4 s2_b5 s2_b6
          w0e0 w0e4 w9 s2_w9 s2_w9 w13 s2_w13 s2_w13 w15 w23 s2_w23 s2_w23 b31 s2_b31 s2_b31
        dsimp only [r1b_opkStage2At] at hclose_s3
        refine r1b_sepWPp_frame_dct (by r1b_ac_dct) hclose_s3 (by r1b_ac_dct) ?_
        generalize hS3 : r1b_opkStage3At fsp spkW0 spkW8 spkW16 spkW24
          s2_b0 s2_b1 s2_b2 s2_b3 s2_b4 s2_b5 s2_b6 w0e0 w0e4 s2_w9 s2_w13 w15 s2_w23 s2_b31 = stage3
        have hok3 : r1b_OkCtxPlacedFd r1b_CodeOk S g d s0 sm3 0x277c := hok.of_step
          { pc := by simp only [hsm3, hsm2, hsm1, wp_norm, arm64_norm]
            run := by simp only [hsm3, hsm2, hsm1, wp_norm, arm64_norm, hst.run]
            sp := by simpa only [hsm3, hsm2, hsm1, wp_norm, arm64_norm] using hst.sp
            fp := by simpa only [hsm3, hsm2, hsm1, wp_norm, arm64_norm] using hst.fp
            inv := hinv3
            vregs := by simpa only [calleeSavedVRegs, hsm3, hsm2, hsm1, wp_norm, arm64_norm] using hst.vregs
            spAligned := hst.spAligned }
          (by simp only [hsm3, hsm2, hsm1, wp_norm, arm64_norm])
          (by simp only [hsm3, hsm2, hsm1, wp_norm, arm64_norm])
          (by simp only [hsm3, hsm2, hsm1, wp_norm, arm64_norm])
          (by simp only [hsm3, hsm2, hsm1, wp_norm, arm64_norm])
          (by simp only [hsm3, hsm2, hsm1, wp_norm, arm64_norm])
          (by simp only [hsm3, hsm2, hsm1, wp_norm, arm64_norm])
        have hsm3_run : sm3.status = .Running := hok3.st.run
        have hsm3_sp : sm3.sp = fsp := hok3.st.sp
        let _ := hsm3_run; let _ := hsm3_sp
        have hx8_3 : sm3.readReg64 (.gpr 8#5) = kpkCap := by
          simp only [hsm3, hsm2, hsm1, wp_norm, arm64_norm]
        have hx23_3 : sm3.readReg64 (.gpr 23#5) = kpkId.zeroExtend 64 := by
          simpa only [hsm3, hsm2, hsm1, wp_norm, arm64_norm] using hx23
        have hx25_3 : sm3.readReg64 (.gpr 25#5) = opkFlag.zeroExtend 64 := by
          simpa only [hsm3, hsm2, hsm1, wp_norm, arm64_norm] using hx25
        have hx26_3 : sm3.readReg64 (.gpr 26#5) = opkFlag.zeroExtend 64 := by
          simpa only [hsm3, hsm2, hsm1, wp_norm, arm64_norm] using hx26
        have hx27_3 : sm3.readReg64 (.gpr 27#5) = spkW12.zeroExtend 64 := by
          simpa only [hsm3, hsm2, hsm1, wp_norm, arm64_norm] using hx27
        have hx28_3 : sm3.readReg64 (.gpr 28#5) = 64#64 := by
          simpa only [hsm3, hsm2, hsm1, wp_norm, arm64_norm] using hx28
        let _ := hx8_3; let _ := hx23_3; let _ := hx25_3; let _ := hx26_3; let _ := hx27_3; let _ := hx28_3
        have hpc3 : sm3.pc = (blkPl_579).base + 10108#64 := by
          simp only [hsm3, hsm2, hsm1, wp_norm, arm64_norm]
        clear hsm3 hsm2 hsm1
        suffices h2790 : ∀ (sf4 : State) (evs1 : List AllocEvent),
            FreeOnlyEvs evs1 →
            r1b_OkCtxPlacedFd r1b_CodeOk S g d s0 sf4 0x2790 →
            sf4.readReg64 (.gpr 23#5) = kpkId.zeroExtend 64 →
            sf4.readReg64 (.gpr 25#5) = opkFlag.zeroExtend 64 →
            sf4.readReg64 (.gpr 26#5) = opkFlag.zeroExtend 64 →
            sf4.readReg64 (.gpr 27#5) = spkW12.zeroExtend 64 →
            sf4.readReg64 (.gpr 28#5) = 64#64 →
            SepWPp (runProgPlaced H) (s0.readReg64 .lr) sf4
              (stage3 ∗
                ownedBytes A.repAlloc spkCap spkPtr (BitVec.ofNat 64 spkBs.length) spkBs ∗
                ownedBytes A.repAlloc regCap regPtr 4#64 regBs ∗
                ((fsp + 0x128#64) ↦₆₄ kpkPtr) ∗ ((fsp + 0x150#64) ↦₆₄ kpkCap) ∗
                ((fsp + 0x168#64) ↦₆₄ spkPtr) ∗ ((fsp + 0x170#64) ↦₆₄ spkCap) ∗
                ((fsp + 0x198#64) ↦₆₄ regCap) ∗ ((fsp + 0x1a0#64) ↦₆₄ regPtr) ∗
                stackAt fsp (resStack - runFrame) ∗ A.pool lim (M.stepEvents evs1 st) sf4 ∗ F)
              Q Qp oom by
          by_cases hkpk0 : kpkCap = 0#64
          · subst hkpk0
            have hpc := hpc3
            have hrun := hok3.st.run; have hsp : sm3.sp = fsp := hok3.st.sp
            apply r1b_seq_lscro_oom (mid := (blkPl_579).base + 10128#64) hinv3
            apply sepWP_seg_ls_vm (Q := (blkPC_579).rebase (blkPl_579).base (hooksException _))
              blkLib_eq_579 blk579_noSvc0 (mid := (blkPl_579).base + 10128#64)
            intro _m_strip; wp_steps
            refine SepWP.done (by simp only [wp_norm, arm64_norm, *]; try bv_omega)
              (by simp only [wp_norm, arm64_norm, *]) fun _m_real hnsp => ?_
            have hvmp4 : VmPreserved sm3 _ :=
              hnsp.toVmPreserved (by simp only [wp_norm, arm64_norm, *])
            simp -failIfUnchanged only [State.setMem_setMem] at hvmp4 ⊢
            apply SepWP.done (by simp only [wp_norm, arm64_norm, *])
              (by simp only [wp_norm, arm64_norm, *])
            clear hpc hrun hsp
            refine r1b_bind_state_placed fun sm4 hsm4 hinv4 => by
              have hvm4 : VmPreserved sm3 sm4 := hsm4 ▸ hvmp4
              rw [← A.pool_transport lim st sm3 sm4 hvm4]
              change SepWPp (runProgPlaced H) _ _ _ _ _ _
              have hcap0 := r1b_ownedBytes_cap0_emp A.repAlloc kpkPtr (BitVec.ofNat 64 kpkBs.length) kpkBs
              refine r1b_sepWPp_frame_dct (by r1b_ac_dct) hcap0 (by r1b_ac_dct) ?_
              exact h2790 sm4 [] (fun _ h => nomatch h)
                (hok3.of_step
                  { pc := by simp only [hsm4, wp_norm, arm64_norm]
                    run := by simp only [hsm4, wp_norm, arm64_norm, hok3.st.run]
                    sp := by simpa only [hsm4, wp_norm, arm64_norm] using hok3.st.sp
                    fp := by simpa only [hsm4, wp_norm, arm64_norm] using hok3.st.fp
                    inv := hinv4
                    vregs := by simpa only [calleeSavedVRegs, hsm4, wp_norm, arm64_norm] using hok3.st.vregs
                    spAligned := hst.spAligned }
                  (by simp only [hsm4, wp_norm, arm64_norm])
                  (by simp only [hsm4, wp_norm, arm64_norm])
                  (by simp only [hsm4, wp_norm, arm64_norm])
                  (by simp only [hsm4, wp_norm, arm64_norm])
                  (by simp only [hsm4, wp_norm, arm64_norm])
                  (by simp only [hsm4, wp_norm, arm64_norm]))
                (by simpa only [hsm4, wp_norm, arm64_norm] using hx23_3)
                (by simpa only [hsm4, wp_norm, arm64_norm] using hx25_3)
                (by simpa only [hsm4, wp_norm, arm64_norm] using hx26_3)
                (by simpa only [hsm4, wp_norm, arm64_norm] using hx27_3)
                (by simpa only [hsm4, wp_norm, arm64_norm] using hx28_3)
          · have hbeq : (kpkCap == 0#64) = false := beq_false_of_ne hkpk0
            let _ := hbeq
            have hpc := hpc3
            have hrun := hok3.st.run; have hsp : sm3.sp = fsp := hok3.st.sp
            apply r1b_seq_lscro_oom (mid := lsρ lsRustDeallocSymCli) hinv3
            apply sepWP_seg_ls_vm (Q := (blkPC_579).rebase (blkPl_579).base (hooksException _))
              blkLib_eq_579 blk579_noSvc0 (mid := lsρ lsRustDeallocSymCli)
            intro _m_strip; wp_steps
            refine SepWP.done (by simp only [wp_norm, arm64_norm, *]; try bv_omega)
              (by simp only [wp_norm, arm64_norm, *]) fun _m_real hnsp => ?_
            have hvmp4 : VmPreserved sm3 _ :=
              hnsp.toVmPreserved (by simp only [wp_norm, arm64_norm, *])
            simp -failIfUnchanged only [State.setMem_setMem] at hvmp4 ⊢
            apply SepWP.done (by simp only [wp_norm, arm64_norm, *])
              (by simp only [wp_norm, arm64_norm, *])
            clear hpc hrun hsp
            refine r1b_bind_state_placed fun sm4 hsm4 hinv4 => by
              have hvm4 : VmPreserved sm3 sm4 := hsm4 ▸ hvmp4
              rw [← A.pool_transport lim st sm3 sm4 hvm4]
              change SepWPp (runProgPlaced H) _ _ _ _ _ _
              refine r1b_call_frame_dct <|
                r1b_call_dealloc_ownedBytes_placed (cap := kpkCap) (ptr := kpkPtr)
                  (len := BitVec.ofNat 64 kpkBs.length) (bs := kpkBs)
                  hh hbnd hinv4
                  (by simp only [hsm4, wp_norm, arm64_norm])
                  (by simp only [hsm4, wp_norm, arm64_norm, hok3.st.run])
                  (by simpa only [hsm4, wp_norm, arm64_norm] using hok3.st.sp)
                  (by simpa only [hsm4, wp_norm, arm64_norm] using hok3.st.fp)
                  (by simpa only [calleeSavedVRegs, hsm4, wp_norm, arm64_norm] using hok3.st.vregs)
                  hst.spAligned (retOff := 0x2790)
                  (by simp only [hsm4, wp_norm, arm64_norm])
                  (by simp only [hsm4, wp_norm, arm64_norm])
                  (by simp only [hsm4, wp_norm, arm64_norm])
                  (by simp only [hsm4, wp_norm, arm64_norm])
                  hkpk0 hpanic (fun sf4 hin4 hcs4 hfs4 htr4 => ?_)
              exact sepWPp_weaken_pre (Entails.of_eq (by r1b_ac_dct))
                (h2790 sf4 (rustDeallocEvents kpkCap.toNat 1)
                  (FreeOnlyEvs.singleton 1 kpkCap.toNat)
                  (hok3.after_call
                    (by simp only [hsm4, wp_norm, arm64_norm])
                    (by simp only [hsm4, wp_norm, arm64_norm])
                    (by simp only [hsm4, wp_norm, arm64_norm])
                    (by simp only [hsm4, wp_norm, arm64_norm])
                    (by simp only [hsm4, wp_norm, arm64_norm])
                    (by simp only [hsm4, wp_norm, arm64_norm])
                    hin4 hcs4 hfs4 htr4)
                  (hcs4.2.2.2.2.1.trans (by simpa only [hsm4, wp_norm, arm64_norm] using hx23_3))
                  (hcs4.2.2.2.2.2.2.1.trans (by simpa only [hsm4, wp_norm, arm64_norm] using hx25_3))
                  (hcs4.2.2.2.2.2.2.2.1.trans (by simpa only [hsm4, wp_norm, arm64_norm] using hx26_3))
                  (hcs4.2.2.2.2.2.2.2.2.1.trans (by simpa only [hsm4, wp_norm, arm64_norm] using hx27_3))
                  (hcs4.2.2.2.2.2.2.2.2.2.1.trans (by simpa only [hsm4, wp_norm, arm64_norm] using hx28_3)))
        intro sf4 evs1 hfo1 hok4 hx23_4 hx25_4 hx26_4 hx27_4 hx28_4
        have hsf4_run : sf4.status = .Running := hok4.st.run
        have hsf4_sp : sf4.sp = fsp := hok4.st.sp
        let _ := hsf4_run; let _ := hsf4_sp
        let _ := hx23_4; let _ := hx25_4; let _ := hx26_4; let _ := hx27_4; let _ := hx28_4
        suffices h27a4 : ∀ (sf5 : State) (evs12 : List AllocEvent),
            FreeOnlyEvs evs12 →
            r1b_OkCtxPlacedFd r1b_CodeOk S g d s0 sf5 0x27a4 →
            sf5.readReg64 (.gpr 23#5) = kpkId.zeroExtend 64 →
            sf5.readReg64 (.gpr 25#5) = opkFlag.zeroExtend 64 →
            sf5.readReg64 (.gpr 26#5) = opkFlag.zeroExtend 64 →
            sf5.readReg64 (.gpr 27#5) = spkW12.zeroExtend 64 →
            sf5.readReg64 (.gpr 28#5) = 64#64 →
            SepWPp (runProgPlaced H) (s0.readReg64 .lr) sf5
              (stage3 ∗
                ownedBytes A.repAlloc regCap regPtr 4#64 regBs ∗
                ((fsp + 0x128#64) ↦₆₄ kpkPtr) ∗ ((fsp + 0x150#64) ↦₆₄ kpkCap) ∗
                ((fsp + 0x168#64) ↦₆₄ spkPtr) ∗ ((fsp + 0x170#64) ↦₆₄ spkCap) ∗
                ((fsp + 0x198#64) ↦₆₄ regCap) ∗ ((fsp + 0x1a0#64) ↦₆₄ regPtr) ∗
                stackAt fsp (resStack - runFrame) ∗ A.pool lim (M.stepEvents evs12 st) sf5 ∗ F)
              Q Qp oom by
          have hpc4 := hok4.st.pc
          change sf4.pc = (blkPl_579).base + 10128#64 at hpc4
          by_cases hspk0 : spkCap = 0#64
          · subst hspk0
            have hpc := hpc4; have hrun := hok4.st.run; have hsp : sf4.sp = fsp := hok4.st.sp
            apply r1b_seq_lscro_oom (mid := (blkPl_579).base + 10148#64) hok4.st.inv
            dsimp only [runProgPlaced, lsProg_579]
            apply sepWP_seg_ls_vm (Q := (blkPC_579).rebase (blkPl_579).base (hooksException _))
              blkLib_eq_579 blk579_noSvc0 (mid := (blkPl_579).base + 10148#64)
            intro _m_strip; wp_steps
            refine SepWP.done (by simp only [wp_norm, arm64_norm, *]; try bv_omega)
              (by simp only [wp_norm, arm64_norm, *]) fun _m_real hnsp => ?_
            have hvmp5 : VmPreserved sf4 _ :=
              hnsp.toVmPreserved (by simp only [wp_norm, arm64_norm, *])
            simp -failIfUnchanged only [State.setMem_setMem] at hvmp5 ⊢
            apply SepWP.done (by simp only [wp_norm, arm64_norm, *])
              (by simp only [wp_norm, arm64_norm, *])
            clear hpc hrun hsp
            refine r1b_bind_state_placed fun sm5 hsm5 hinv5 => by
              have hvm5 : VmPreserved sf4 sm5 := hsm5 ▸ hvmp5
              rw [← A.pool_transport lim (M.stepEvents evs1 st) sf4 sm5 hvm5]
              change SepWPp (runProgPlaced H) _ _ _ _ _ _
              have hcap0 := r1b_ownedBytes_cap0_emp A.repAlloc spkPtr (BitVec.ofNat 64 spkBs.length) spkBs
              refine r1b_sepWPp_frame_dct (by r1b_ac_dct) hcap0 (by r1b_ac_dct) ?_
              exact h27a4 sm5 evs1 hfo1
                (hok4.of_step
                  { pc := by simp only [hsm5, wp_norm, arm64_norm]
                    run := by simp only [hsm5, wp_norm, arm64_norm, hok4.st.run]
                    sp := by simpa only [hsm5, wp_norm, arm64_norm] using hok4.st.sp
                    fp := by simpa only [hsm5, wp_norm, arm64_norm] using hok4.st.fp
                    inv := hinv5
                    vregs := by simpa only [calleeSavedVRegs, hsm5, wp_norm, arm64_norm] using hok4.st.vregs
                    spAligned := hst.spAligned }
                  (by simp only [hsm5, wp_norm, arm64_norm])
                  (by simp only [hsm5, wp_norm, arm64_norm])
                  (by simp only [hsm5, wp_norm, arm64_norm])
                  (by simp only [hsm5, wp_norm, arm64_norm])
                  (by simp only [hsm5, wp_norm, arm64_norm])
                  (by simp only [hsm5, wp_norm, arm64_norm]))
                (by simpa only [hsm5, wp_norm, arm64_norm] using hx23_4)
                (by simpa only [hsm5, wp_norm, arm64_norm] using hx25_4)
                (by simpa only [hsm5, wp_norm, arm64_norm] using hx26_4)
                (by simpa only [hsm5, wp_norm, arm64_norm] using hx27_4)
                (by simpa only [hsm5, wp_norm, arm64_norm] using hx28_4)
          · have hbeq : (spkCap == 0#64) = false := beq_false_of_ne hspk0
            let _ := hbeq
            have hpc := hpc4; have hrun := hok4.st.run; have hsp : sf4.sp = fsp := hok4.st.sp
            apply r1b_seq_lscro_oom (mid := lsρ lsRustDeallocSymCli) hok4.st.inv
            dsimp only [runProgPlaced, lsProg_579]
            apply sepWP_seg_ls_vm (Q := (blkPC_579).rebase (blkPl_579).base (hooksException _))
              blkLib_eq_579 blk579_noSvc0 (mid := lsρ lsRustDeallocSymCli)
            intro _m_strip; wp_steps
            refine SepWP.done (by simp only [wp_norm, arm64_norm, *]; try bv_omega)
              (by simp only [wp_norm, arm64_norm, *]) fun _m_real hnsp => ?_
            have hvmp5 : VmPreserved sf4 _ :=
              hnsp.toVmPreserved (by simp only [wp_norm, arm64_norm, *])
            simp -failIfUnchanged only [State.setMem_setMem] at hvmp5 ⊢
            apply SepWP.done (by simp only [wp_norm, arm64_norm, *])
              (by simp only [wp_norm, arm64_norm, *])
            clear hpc hrun hsp
            refine r1b_bind_state_placed fun sm5 hsm5 hinv5 => by
              have hvm5 : VmPreserved sf4 sm5 := hsm5 ▸ hvmp5
              rw [← A.pool_transport lim (M.stepEvents evs1 st) sf4 sm5 hvm5]
              change SepWPp (runProgPlaced H) _ _ _ _ _ _
              refine r1b_call_frame_dct <|
                r1b_call_dealloc_ownedBytes_placed (cap := spkCap) (ptr := spkPtr)
                  (len := BitVec.ofNat 64 spkBs.length) (bs := spkBs)
                  hh hbnd hinv5
                  (by simp only [hsm5, wp_norm, arm64_norm])
                  (by simp only [hsm5, wp_norm, arm64_norm, hok4.st.run])
                  (by simpa only [hsm5, wp_norm, arm64_norm] using hok4.st.sp)
                  (by simpa only [hsm5, wp_norm, arm64_norm] using hok4.st.fp)
                  (by simpa only [calleeSavedVRegs, hsm5, wp_norm, arm64_norm] using hok4.st.vregs)
                  hst.spAligned (retOff := 0x27a4)
                  (by simp only [hsm5, wp_norm, arm64_norm])
                  (by simp only [hsm5, wp_norm, arm64_norm])
                  (by simp only [hsm5, wp_norm, arm64_norm])
                  (by simp only [hsm5, wp_norm, arm64_norm])
                  hspk0 hpanic (fun sf5 hin5 hcs5 hfs5 htr5 => ?_)
              rw [← M.stepEvents_append]
              exact sepWPp_weaken_pre (Entails.of_eq (by r1b_ac_dct))
                (h27a4 sf5 (evs1 ++ rustDeallocEvents spkCap.toNat 1)
                  (FreeOnlyEvs.append hfo1 (FreeOnlyEvs.singleton 1 spkCap.toNat))
                  (hok4.after_call
                    (by simp only [hsm5, wp_norm, arm64_norm])
                    (by simp only [hsm5, wp_norm, arm64_norm])
                    (by simp only [hsm5, wp_norm, arm64_norm])
                    (by simp only [hsm5, wp_norm, arm64_norm])
                    (by simp only [hsm5, wp_norm, arm64_norm])
                    (by simp only [hsm5, wp_norm, arm64_norm])
                    hin5 hcs5 hfs5 htr5)
                  (hcs5.2.2.2.2.1.trans (by simpa only [hsm5, wp_norm, arm64_norm] using hx23_4))
                  (hcs5.2.2.2.2.2.2.1.trans (by simpa only [hsm5, wp_norm, arm64_norm] using hx25_4))
                  (hcs5.2.2.2.2.2.2.2.1.trans (by simpa only [hsm5, wp_norm, arm64_norm] using hx26_4))
                  (hcs5.2.2.2.2.2.2.2.2.1.trans (by simpa only [hsm5, wp_norm, arm64_norm] using hx27_4))
                  (hcs5.2.2.2.2.2.2.2.2.2.1.trans (by simpa only [hsm5, wp_norm, arm64_norm] using hx28_4)))
        intro sf5 evs12 hfo12 hok5 hx23_5 hx25_5 hx26_5 hx27_5 hx28_5
        have hsf5_run : sf5.status = .Running := hok5.st.run
        have hsf5_sp : sf5.sp = fsp := hok5.st.sp
        let _ := hsf5_run; let _ := hsf5_sp
        let _ := hx23_5; let _ := hx25_5; let _ := hx26_5; let _ := hx27_5; let _ := hx28_5
        have hpc5 := hok5.st.pc
        change sf5.pc = (blkPl_579).base + 10148#64 at hpc5
        by_cases hreg0 : regCap = 0#64
        · subst hreg0
          have hpc := hpc5; have hrun := hok5.st.run; have hsp : sf5.sp = fsp := hok5.st.sp
          apply r1b_seq_lscro_oom (mid := (blkPl_579).base + 10172#64) hok5.st.inv
          dsimp only [runProgPlaced, lsProg_579]
          apply sepWP_seg_ls_vm (Q := (blkPC_579).rebase (blkPl_579).base (hooksException _))
            blkLib_eq_579 blk579_noSvc0 (mid := (blkPl_579).base + 10172#64)
          intro _m_strip; wp_steps
          refine SepWP.done (by simp only [wp_norm, arm64_norm, *]; try bv_omega)
            (by simp only [wp_norm, arm64_norm, *]) fun _m_real hnsp => ?_
          have hvmp6 : VmPreserved sf5 _ :=
            hnsp.toVmPreserved (by simp only [wp_norm, arm64_norm, *])
          simp -failIfUnchanged only [State.setMem_setMem] at hvmp6 ⊢
          apply SepWP.done (by simp only [wp_norm, arm64_norm, *])
            (by simp only [wp_norm, arm64_norm, *])
          clear hpc hrun hsp
          refine r1b_bind_state_placed fun sm6 hsm6 hinv6 => by
            have hvm6 : VmPreserved sf5 sm6 := hsm6 ▸ hvmp6
            rw [← A.pool_transport lim (M.stepEvents evs12 st) sf5 sm6 hvm6]
            change SepWPp (runProgPlaced H) _ _ _ _ _ _
            have hcap0 := r1b_ownedBytes_cap0_emp A.repAlloc regPtr 4#64 regBs
            refine r1b_sepWPp_frame_dct (by r1b_ac_dct) hcap0 (by r1b_ac_dct) ?_
            refine sepWPp_weaken_pre (Entails.of_eq (by rw [← hS3]))
              (hk sm6 evs12 hfo12
                (hok5.of_step
                  { pc := by simp only [hsm6, wp_norm, arm64_norm]
                    run := by simp only [hsm6, wp_norm, arm64_norm, hok5.st.run]
                    sp := by simpa only [hsm6, wp_norm, arm64_norm] using hok5.st.sp
                    fp := by simpa only [hsm6, wp_norm, arm64_norm] using hok5.st.fp
                    inv := hinv6
                    vregs := by simpa only [calleeSavedVRegs, hsm6, wp_norm, arm64_norm] using hok5.st.vregs
                    spAligned := hst.spAligned }
                  (by simp only [hsm6, wp_norm, arm64_norm])
                  (by simp only [hsm6, wp_norm, arm64_norm])
                  (by simp only [hsm6, wp_norm, arm64_norm])
                  (by simp only [hsm6, wp_norm, arm64_norm])
                  (by simp only [hsm6, wp_norm, arm64_norm])
                  (by simp only [hsm6, wp_norm, arm64_norm]))
                (by simpa only [hsm6, wp_norm, arm64_norm] using hx23_5)
                (by simp only [hsm6, arm64_norm])
                (by simpa only [hsm6, wp_norm, arm64_norm] using hx25_5)
                (by simpa only [hsm6, wp_norm, arm64_norm] using hx26_5)
                (by simpa only [hsm6, wp_norm, arm64_norm] using hx28_5))
        · have hbeq : (regCap == 0#64) = false := beq_false_of_ne hreg0
          let _ := hbeq
          have hpc := hpc5; have hrun := hok5.st.run; have hsp : sf5.sp = fsp := hok5.st.sp
          apply r1b_seq_lscro_oom (mid := lsρ lsRustDeallocSymCli) hok5.st.inv
          dsimp only [runProgPlaced, lsProg_579]
          apply sepWP_seg_ls_vm (Q := (blkPC_579).rebase (blkPl_579).base (hooksException _))
            blkLib_eq_579 blk579_noSvc0 (mid := lsρ lsRustDeallocSymCli)
          intro _m_strip; wp_steps
          refine SepWP.done (by simp only [wp_norm, arm64_norm, *]; try bv_omega)
            (by simp only [wp_norm, arm64_norm, *]) fun _m_real hnsp => ?_
          have hvmp6 : VmPreserved sf5 _ :=
            hnsp.toVmPreserved (by simp only [wp_norm, arm64_norm, *])
          simp -failIfUnchanged only [State.setMem_setMem] at hvmp6 ⊢
          apply SepWP.done (by simp only [wp_norm, arm64_norm, *])
            (by simp only [wp_norm, arm64_norm, *])
          clear hpc hrun hsp
          refine r1b_bind_state_placed fun sm6 hsm6 hinv6 => by
            have hvm6 : VmPreserved sf5 sm6 := hsm6 ▸ hvmp6
            rw [← A.pool_transport lim (M.stepEvents evs12 st) sf5 sm6 hvm6]
            change SepWPp (runProgPlaced H) _ _ _ _ _ _
            have hx24_6 : sm6.readReg64 (.gpr 24#5) = (spkW12.zeroExtend 64) <<< 32 := by
              simp only [hsm6, arm64_norm]
            refine r1b_call_frame_dct <|
              r1b_call_dealloc_ownedBytes_placed (cap := regCap) (ptr := regPtr) (len := 4#64) (bs := regBs)
                hh hbnd hinv6
                (by simp only [hsm6, wp_norm, arm64_norm])
                (by simp only [hsm6, wp_norm, arm64_norm, hok5.st.run])
                (by simpa only [hsm6, wp_norm, arm64_norm] using hok5.st.sp)
                (by simpa only [hsm6, wp_norm, arm64_norm] using hok5.st.fp)
                (by simpa only [calleeSavedVRegs, hsm6, wp_norm, arm64_norm] using hok5.st.vregs)
                hst.spAligned (retOff := 0x27bc)
                (by simp only [hsm6, wp_norm, arm64_norm])
                (by simp only [hsm6, wp_norm, arm64_norm])
                (by simp only [hsm6, wp_norm, arm64_norm])
                (by simp only [hsm6, wp_norm, arm64_norm])
                hreg0 hpanic (fun sf6 hin6 hcs6 hfs6 htr6 => ?_)
            rw [← M.stepEvents_append]
            exact sepWPp_weaken_pre (Entails.of_eq (by rw [← hS3]; r1b_ac_dct))
              (hk sf6 (evs12 ++ rustDeallocEvents regCap.toNat 1)
                (FreeOnlyEvs.append hfo12 (FreeOnlyEvs.singleton 1 regCap.toNat))
                (hok5.after_call
                  (by simp only [hsm6, wp_norm, arm64_norm])
                  (by simp only [hsm6, wp_norm, arm64_norm])
                  (by simp only [hsm6, wp_norm, arm64_norm])
                  (by simp only [hsm6, wp_norm, arm64_norm])
                  (by simp only [hsm6, wp_norm, arm64_norm])
                  (by simp only [hsm6, wp_norm, arm64_norm])
                  hin6 hcs6 hfs6 htr6)
                (hcs6.2.2.2.2.1.trans (by simpa only [hsm6, wp_norm, arm64_norm] using hx23_5))
                (hcs6.2.2.2.2.2.1.trans hx24_6)
                (hcs6.2.2.2.2.2.2.1.trans (by simpa only [hsm6, wp_norm, arm64_norm] using hx25_5))
                (hcs6.2.2.2.2.2.2.2.1.trans (by simpa only [hsm6, wp_norm, arm64_norm] using hx26_5))
                (hcs6.2.2.2.2.2.2.2.2.2.1.trans (by simpa only [hsm6, wp_norm, arm64_norm] using hx28_5)))


end LibsignalBinary.Proofs.SignalSession.Cli.Run.Compose.Arms.R1b.DeserCloneTailPlacedBudgetAuxFd
