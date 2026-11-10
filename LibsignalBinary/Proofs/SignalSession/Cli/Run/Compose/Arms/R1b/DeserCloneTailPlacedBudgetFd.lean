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
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Compose.Arms.R1b.DeserCloneTailPlacedBudgetAuxFd
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Compose.Arms.R1b.WorkFramePlacedFd
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Compose.Arms.R1bProofPlacedBudgetFd
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
# `FdsGe3Closed`-Threaded Stage 4b (`0x25f4 → 0x27bc`) of Arm `R1b`

Proves `r1b_step_tail_25f4_placed_raw_fd` and `r1b_step_tail_25f4_placed_fd` (`0x25f4 → 0x27bc`,
`FreeOnlyEvs`) on Block `579`, threading `FdsGe3Closed` across `opk` stack staging and `kpkBs`,
`spkBs`, and `regBs` deallocations.
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 200000
set_option linter.unusedSimpArgs false

namespace LibsignalBinary.Proofs.SignalSession.Cli.Run.Compose.Arms.R1b.DeserCloneTailPlacedBudgetFd

open Arm64 Arm64.Process ProofLib ProofLib.ProgramReflection SepProp
open CryptoGames.LibsignalSession (PublicKey)
open CryptoVerification (LibsignalHooks LibsignalPlacement)
open CryptoVerification.LibsignalTripleRatchet.Wire
  (pkBytesOf sevenBytesHeadAt sevenBytesHeadAt_eq_tailAt sevenBytesTailAt)
open CryptoVerification.SignalSession.Cli (splitId)
open CryptoVerification.SignalSession.Cli.MainHops (RunCall ownedBytes sepWPp_weaken_pre)
open CryptoVerification.SignalSession.Cli.Run.Placed
  (blkLib_eq_579 blkPC_579 blkPl_579 lsProg_579)
open CryptoVerification.SignalSession.Cli.RunCompose
  (Init1Data PanicK RunSem r1b_CodeOk r1b_StackBounds r1b_bind_state_placed
   r1b_entails_frame_core r1b_fsp_align r1b_memRegion7_to_head7 r1b_opkStage1SpkAt
   r1b_opkStage2At r1b_opkStage3At r1b_sepWPp_frame_core r1b_splitId_bytes r1b_split_region
   runFsp runPcPlaced_eq runProgPlaced)
open CryptoVerification.SignalSession.Cli.RunSkeleton (RunBudgets runFrame)
open LibsignalBinary.Heap
  (AllocCostModel AllocEvent BudgetLimits FreeOnlyEvs RustCliAllocBudget VmPreserved)
open LibsignalBinary.Proofs.Placed.BudgetPoolSync (hooksException sepWP_seg_ls_vm)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Compose.Arms.R1b.DeserCloneTailPlacedBudgetAuxFd
  (r1b_tail_2744_placed_fd)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Compose.Arms.R1b.ReadKpkPlacedBudgetAux
  (r1b_seq_lscro_oom)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Compose.Arms.R1b.ReadRegSpkPlacedBudgetAux
  (blk579_noSvc0)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Compose.Arms.R1b.WorkFramePlacedFd
  (r1b_OkCtxPlacedFd)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Compose.Arms.R1bProofPlacedBudgetFd
  (R1bStepTail25f4PlacedFd)
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


private theorem r1b_stage1Spk_open_stage2 (fsp : BitVec 64)
    (spkW0 : BitVec 64) (spkW8 : BitVec 32) (spkW16 spkW24 : BitVec 64)
    (b0 b1 b2 b3 b4 b5 b6 : BitVec 8)
    (w0e0 w0e4 w9 : BitVec 32) (w13 : BitVec 16) (w15 w23 : BitVec 64) (b31 : BitVec 8) :
    r1b_opkStage1SpkAt fsp spkW0 spkW8 spkW16 spkW24
      b0 b1 b2 b3 b4 b5 b6 w0e0 w0e4 w9 w13 w15 w23 b31 ⊢
    ∃∗ s2_b0 : BitVec 8, ∃∗ s2_b1 : BitVec 8, ∃∗ s2_b2 : BitVec 8, ∃∗ s2_b3 : BitVec 8,
    ∃∗ s2_b4 : BitVec 8, ∃∗ s2_b5 : BitVec 8, ∃∗ s2_b6 : BitVec 8,
    ∃∗ c0 : BitVec 8, ∃∗ c1 : BitVec 8, ∃∗ c2 : BitVec 8, ∃∗ c3 : BitVec 8,
    ∃∗ c4 : BitVec 8, ∃∗ c5 : BitVec 8, ∃∗ c6 : BitVec 8,
    ∃∗ s2_w9 : BitVec 32, ∃∗ c9 : BitVec 32,
    ∃∗ s2_w13 : BitVec 16, ∃∗ c13 : BitVec 16,
    ∃∗ s2_w23 : BitVec 64, ∃∗ c23 : BitVec 64,
    ∃∗ s2_b31 : BitVec 8, ∃∗ c31 : BitVec 8,
      r1b_opkStage2At fsp spkW0 spkW8 spkW16 spkW24
        b0 b1 b2 b3 b4 b5 b6
        s2_b0 s2_b1 s2_b2 s2_b3 s2_b4 s2_b5 s2_b6
        c0 c1 c2 c3 c4 c5 c6
        w0e0 w0e4 w9 s2_w9 c9 w13 s2_w13 c13 w15 w23 s2_w23 c23 b31 s2_b31 c31 := by
  dsimp only [r1b_opkStage1SpkAt]
  have h1d0 : memRegion (fsp + 0x1d0#64) 0x50 =
      memRegion (fsp + 0x1d0#64) 0x18 ∗
        memRegion (fsp + 0x1e8#64) 8 ∗ memRegion (fsp + 0x1f0#64) 1 ∗
        memRegion (fsp + 0x1f1#64) 7 ∗ memRegion (fsp + 0x1f8#64) 4 ∗
        memRegion (fsp + 0x1fc#64) 2 ∗ memRegion (fsp + 0x1fe#64) 2 ∗
        memRegion (fsp + 0x200#64) 7 ∗ memRegion (fsp + 0x207#64) 0x19 := by
    rw [r1b_split_region fsp 0x1d0 0x18 0x38,
      r1b_split_region fsp 0x1e8 8 0x30,
      r1b_split_region fsp 0x1f0 1 0x2f,
      r1b_split_region fsp 0x1f1 7 0x28,
      r1b_split_region fsp 0x1f8 4 0x24,
      r1b_split_region fsp 0x1fc 2 0x22,
      r1b_split_region fsp 0x1fe 2 0x20,
      r1b_split_region fsp 0x200 7 0x19]
  have h2c0 : memRegion (fsp + 0x2c0#64) 0xf8 =
      memRegion (fsp + 0x2c0#64) 0x40 ∗
        memRegion (fsp + 0x300#64) 4 ∗ memRegion (fsp + 0x304#64) 2 ∗
        memRegion (fsp + 0x306#64) 0x1a ∗ memRegion (fsp + 0x320#64) 8 ∗
        memRegion (fsp + 0x328#64) 1 ∗ memRegion (fsp + 0x329#64) 0x57 ∗
        memRegion (fsp + 0x380#64) 7 ∗ memRegion (fsp + 0x387#64) 0x31 := by
    rw [r1b_split_region fsp 0x2c0 0x40 0xb8,
      r1b_split_region fsp 0x300 4 0xb4,
      r1b_split_region fsp 0x304 2 0xb2,
      r1b_split_region fsp 0x306 0x1a 0x98,
      r1b_split_region fsp 0x320 8 0x90,
      r1b_split_region fsp 0x328 1 0x8f,
      r1b_split_region fsp 0x329 0x57 0x38,
      r1b_split_region fsp 0x380 7 0x31]
  rw [h1d0, h2c0,
    ProofLib.memRegion_eight (fsp + 0x1e8#64),
    ProofLib.memRegion_one (fsp + 0x1f0#64),
    ProofLib.memRegion_four (fsp + 0x1f8#64),
    ProofLib.memRegion_two (fsp + 0x1fc#64),
    ProofLib.memRegion_four (fsp + 0x300#64),
    ProofLib.memRegion_two (fsp + 0x304#64),
    ProofLib.memRegion_eight (fsp + 0x320#64),
    ProofLib.memRegion_one (fsp + 0x328#64)]
  refine Entails.trans
    (r1b_entails_frame_dct (by r1b_ac_dct)
      (sepConj_mono (r1b_memRegion7_to_head7 (fsp + 0x200#64))
        (r1b_memRegion7_to_head7 (fsp + 0x380#64))) (by r1b_ac_dct)) ?_
  simp only [sepExists_sepConj_left, sepExists_sepConj_right]
  refine Entails.sepExists_elim fun s2_b31 =>
    Entails.sepExists_elim fun s2_w23 =>
    Entails.sepExists_elim fun s2_w13 =>
    Entails.sepExists_elim fun s2_w9 =>
    Entails.sepExists_elim fun c13 =>
    Entails.sepExists_elim fun c9 =>
    Entails.sepExists_elim fun c31 =>
    Entails.sepExists_elim fun c23 =>
    Entails.sepExists_elim fun s2_b0 =>
    Entails.sepExists_elim fun s2_b1 =>
    Entails.sepExists_elim fun s2_b2 =>
    Entails.sepExists_elim fun s2_b3 =>
    Entails.sepExists_elim fun s2_b4 =>
    Entails.sepExists_elim fun s2_b5 =>
    Entails.sepExists_elim fun s2_b6 =>
    Entails.sepExists_elim fun c0 =>
    Entails.sepExists_elim fun c1 =>
    Entails.sepExists_elim fun c2 =>
    Entails.sepExists_elim fun c3 =>
    Entails.sepExists_elim fun c4 =>
    Entails.sepExists_elim fun c5 =>
    Entails.sepExists_elim fun c6 => ?_
  refine Entails.sepExists_right s2_b0 (Entails.sepExists_right s2_b1
    (Entails.sepExists_right s2_b2 (Entails.sepExists_right s2_b3
    (Entails.sepExists_right s2_b4 (Entails.sepExists_right s2_b5
    (Entails.sepExists_right s2_b6 (Entails.sepExists_right c0
    (Entails.sepExists_right c1 (Entails.sepExists_right c2
    (Entails.sepExists_right c3 (Entails.sepExists_right c4
    (Entails.sepExists_right c5 (Entails.sepExists_right c6
    (Entails.sepExists_right s2_w9 (Entails.sepExists_right c9
    (Entails.sepExists_right s2_w13 (Entails.sepExists_right c13
    (Entails.sepExists_right s2_w23 (Entails.sepExists_right c23
    (Entails.sepExists_right s2_b31 (Entails.sepExists_right c31 ?_)))))))))))))))))))))
  dsimp only [r1b_opkStage2At]
  exact Entails.of_eq (by r1b_ac_dct)


set_option maxHeartbeats 800000 in
/-- `FdsGe3Closed`-threaded Stage 4b step (`0x25f4 → 0x27bc`): stages `opk` into Stage-3 stack slots and frees `kpkBs`, `spkBs`, and `regBs`. -/
theorem r1b_step_tail_25f4_placed_raw_fd [LibsignalPlacement] {M : AllocCostModel}
    {S : RunSem} {A : RustCliAllocBudget M} {lim : BudgetLimits} {st : M.σ}
    {H : LibsignalHooks} {B : RunBudgets}
    {g : RunCall} {d : Init1Data} {s0 s : State} {resStack : Nat}
    {spkW0 : BitVec 64} {spkW8 spkW12 : BitVec 32} {spkW16 spkW24 : BitVec 64}
    {b0 b1 b2 b3 b4 b5 b6 : BitVec 8}
    {w0e0 w0e4 w9 : BitVec 32} {w13 : BitVec 16} {w15 w23 : BitVec 64} {b31 : BitVec 8}
    {kpkId v11c : BitVec 32}
    {opkBs kpkBs spkBs regBs : List (BitVec 8)}
    {opk : Option (BitVec 32 × PublicKey)}
    {kpkCap kpkPtr spkCap spkPtr regCap regPtr : BitVec 64}
    {F : SepProp} {Q Qp : State → SepProp → Prop} {oom : State → SepProp}
    (hh : RunHooksPlaced A lim H)
    (hbnd : r1b_StackBounds B resStack)
    (hok : r1b_OkCtxPlacedFd r1b_CodeOk S g d s0 s 0x25f4)
    (hopk_sem : (opkBs = [] ∧ opk = none) ∨
      (∃ opkId opkKey opkPk, opkBs ≠ [] ∧ opkBs.length < 2 ^ 63 ∧
        splitId opkBs = some (opkId, opkKey) ∧
        PublicKey.deserialize opkKey = .ok opkPk ∧ opk = some (opkId, opkPk) ∧
        v11c = opkId ∧
        opkPk.bytes.toList = pkBytesOf b0 b1 b2 b3 b4 b5 b6
          (w0e4.truncate 8) (w0e0.truncate 8) w9 w13 w15 w23 b31))
    (hx23 : s.readReg64 (.gpr 23#5) = kpkId.zeroExtend 64)
    (hx24 : s.readReg64 (.gpr 24#5) = runFsp s0 + 0x380#64)
    (hx25 : s.readReg64 (.gpr 25#5) = BitVec.ofNat 64 opkBs.length)
    (hx27 : s.readReg64 (.gpr 27#5) = spkW12.zeroExtend 64)
    (hx28 : s.readReg64 (.gpr 28#5) = 64#64)
    (hpanic : PanicK g s0 Qp)
    (hk : ∀ (sf : State) (evs : List AllocEvent)
        (c0 c1 c2 c3 c4 c5 c6 : BitVec 8) (c9 : BitVec 32) (c13 : BitVec 16)
        (c23 : BitVec 64) (c31 : BitVec 8),
      let opkFlag : BitVec 32 := if opk.isSome then 1#32 else 0#32
      FreeOnlyEvs evs →
      r1b_OkCtxPlacedFd r1b_CodeOk S g d s0 sf 0x27bc →
      (∀ p, opk = some p → v11c = p.1 ∧
        p.2.bytes.toList = pkBytesOf c0 c1 c2 c3 c4 c5 c6
          (w0e4.truncate 8) (w0e0.truncate 8) c9 c13 w15 c23 c31) →
      sf.readReg64 (.gpr 23#5) = kpkId.zeroExtend 64 →
      sf.readReg64 (.gpr 24#5) = (spkW12.zeroExtend 64) <<< 32 →
      sf.readReg64 (.gpr 25#5) = opkFlag.zeroExtend 64 →
      sf.readReg64 (.gpr 26#5) = opkFlag.zeroExtend 64 →
      sf.readReg64 (.gpr 28#5) = 64#64 →
      let fsp := runFsp s0
      SepWPp (runProgPlaced H) (s0.readReg64 .lr) sf
        (r1b_opkStage3At fsp spkW0 spkW8 spkW16 spkW24
            c0 c1 c2 c3 c4 c5 c6 w0e0 w0e4 c9 c13 w15 c23 c31 ∗
          ((fsp + 0x128#64) ↦₆₄ kpkPtr) ∗ ((fsp + 0x150#64) ↦₆₄ kpkCap) ∗
          ((fsp + 0x168#64) ↦₆₄ spkPtr) ∗ ((fsp + 0x170#64) ↦₆₄ spkCap) ∗
          ((fsp + 0x198#64) ↦₆₄ regCap) ∗ ((fsp + 0x1a0#64) ↦₆₄ regPtr) ∗
          stackAt fsp (resStack - runFrame) ∗ A.pool lim (M.stepEvents evs st) sf ∗ F)
        Q Qp oom) :
    let fsp := runFsp s0
    SepWPp (runProgPlaced H) (s0.readReg64 .lr) s
      (r1b_opkStage1SpkAt fsp spkW0 spkW8 spkW16 spkW24
          b0 b1 b2 b3 b4 b5 b6 w0e0 w0e4 w9 w13 w15 w23 b31 ∗
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
  let _ := hx23; let _ := hx24; let _ := hx25; let _ := hx27; let _ := hx28
  have hst := hok.st
  have hs_run : s.status = .Running := hst.run
  have hs_sp : s.sp = fsp := hst.sp
  let _ := hs_run; let _ := hs_sp
  have hal : fsp &&& 15#64 = 0#64 := r1b_fsp_align hst.sp hst.spAligned
  let _ := hal
  refine r1b_sepWPp_frame_dct (by r1b_ac_dct)
    (r1b_stage1Spk_open_stage2 fsp spkW0 spkW8 spkW16 spkW24
      b0 b1 b2 b3 b4 b5 b6 w0e0 w0e4 w9 w13 w15 w23 b31) (by r1b_ac_dct) ?_
  simp only [sepExists_sepConj_left]
  refine SepWPp.exists_elim fun s2_b0 => SepWPp.exists_elim fun s2_b1 =>
    SepWPp.exists_elim fun s2_b2 => SepWPp.exists_elim fun s2_b3 =>
    SepWPp.exists_elim fun s2_b4 => SepWPp.exists_elim fun s2_b5 =>
    SepWPp.exists_elim fun s2_b6 =>
    SepWPp.exists_elim fun c0_in => SepWPp.exists_elim fun c1_in =>
    SepWPp.exists_elim fun c2_in => SepWPp.exists_elim fun c3_in =>
    SepWPp.exists_elim fun c4_in => SepWPp.exists_elim fun c5_in =>
    SepWPp.exists_elim fun c6_in =>
    SepWPp.exists_elim fun s2_w9 => SepWPp.exists_elim fun c9_in =>
    SepWPp.exists_elim fun s2_w13 => SepWPp.exists_elim fun c13_in =>
    SepWPp.exists_elim fun s2_w23 => SepWPp.exists_elim fun c23_in =>
    SepWPp.exists_elim fun s2_b31 => SepWPp.exists_elim fun c31_in => ?_
  have hpc0 := hst.pc
  change s.pc = (blkPl_579).base + 9716#64 at hpc0
  rcases hopk_sem with ⟨rfl, rfl⟩ |
      ⟨_opkId, _opkKey, _opkPk, _hne_nil, h63, hsp_o, _hd_o, rfl, hv11c, hbytes⟩
  ·
    have hpc := hpc0; have hrun := hst.run; have hsp : s.sp = fsp := hst.sp
    apply r1b_seq_lscro_oom (mid := (blkPl_579).base + 10052#64) hst.inv
    dsimp only [runProgPlaced, lsProg_579]
    apply sepWP_seg_ls_vm (Q := (blkPC_579).rebase (blkPl_579).base (hooksException _))
      blkLib_eq_579 blk579_noSvc0 (mid := (blkPl_579).base + 10052#64)
    intro _m_strip; wp_steps
    refine SepWP.done (by simp only [wp_norm, arm64_norm, *]; try bv_omega)
      (by simp only [wp_norm, arm64_norm, *]) fun _m_real hnsp => ?_
    have hvmp : VmPreserved s _ :=
      hnsp.toVmPreserved (by simp only [wp_norm, arm64_norm, *])
    simp -failIfUnchanged only [State.setMem_setMem] at hvmp ⊢
    apply SepWP.done (by simp only [wp_norm, arm64_norm, *])
      (by simp only [wp_norm, arm64_norm, *])
    clear hpc hrun hsp
    refine r1b_bind_state_placed fun sm hsm hinv_m => by
      have hvm : VmPreserved s sm := hsm ▸ hvmp
      rw [← A.pool_transport lim st s sm hvm]
      change SepWPp (runProgPlaced H) _ _ _ _ _ _
      exact r1b_tail_2744_placed_fd (opkFlag := 0#32) hh hbnd
        (hok.of_step
          { pc := by simp only [hsm, wp_norm, arm64_norm]
            run := by simp only [hsm, wp_norm, arm64_norm, hst.run]
            sp := by simpa only [hsm, wp_norm, arm64_norm] using hst.sp
            fp := by simpa only [hsm, wp_norm, arm64_norm] using hst.fp
            inv := hinv_m
            vregs := by simpa only [calleeSavedVRegs, hsm, wp_norm, arm64_norm] using hst.vregs
            spAligned := hst.spAligned }
          (by simp only [hsm, wp_norm, arm64_norm])
          (by simp only [hsm, wp_norm, arm64_norm])
          (by simp only [hsm, wp_norm, arm64_norm])
          (by simp only [hsm, wp_norm, arm64_norm])
          (by simp only [hsm, wp_norm, arm64_norm])
          (by simp only [hsm, wp_norm, arm64_norm]))
        (by simp only [hsm, hx23, wp_norm, arm64_norm])
        (by change _ = fsp + 0x380#64; simp only [hsm, hx24, wp_norm, arm64_norm])
        (by simp only [hsm, hx25, wp_norm, arm64_norm])
        (by simp only [hsm, wp_norm, arm64_norm])
        (by simp only [hsm, hx27, wp_norm, arm64_norm])
        (by simp only [hsm, hx28, wp_norm, arm64_norm])
        hpanic fun sf evs hfo hok_f hx23_f hx24_f hx25_f hx26_f hx28_f =>
          hk sf evs s2_b0 s2_b1 s2_b2 s2_b3 s2_b4 s2_b5 s2_b6 s2_w9 s2_w13 s2_w23 s2_b31
            hfo hok_f (fun _ hp => by cases hp) hx23_f hx24_f hx25_f hx26_f hx28_f
  ·
    have h4len : 4 ≤ opkBs.length := by
      have ⟨_, _, hlen_o⟩ := r1b_splitId_bytes hsp_o; omega
    have hne0 : (BitVec.ofNat 64 opkBs.length == 0#64) = false := by
      apply beq_false_of_ne
      intro heq
      have hn : (BitVec.ofNat 64 opkBs.length).toNat = 0 := congrArg BitVec.toNat heq
      simp only [BitVec.toNat_ofNat] at hn
      omega
    have hal3b8 : (fsp + 0x3b8#64) &&& 3#64 = 0#64 :=
      (fun (x : BitVec 64) (hx : x &&& 15#64 = 0#64) => show (x + 0x3b8#64) &&& 3#64 = 0#64 by bv_bits) fsp hal
    have hal380 : (fsp + 0x380#64) &&& 3#64 = 0#64 :=
      (fun (x : BitVec 64) (hx : x &&& 15#64 = 0#64) => show (x + 0x380#64) &&& 3#64 = 0#64 by bv_bits) fsp hal
    have hal3d8 : (fsp + 0x3d8#64) &&& 3#64 = 0#64 :=
      (fun (x : BitVec 64) (hx : x &&& 15#64 = 0#64) => show (x + 0x3d8#64) &&& 3#64 = 0#64 by bv_bits) fsp hal
    have hal3dc : (fsp + 0x3dc#64) &&& 1#64 = 0#64 :=
      (fun (x : BitVec 64) (hx : x &&& 15#64 = 0#64) => show (x + 0x3dc#64) &&& 1#64 = 0#64 by bv_bits) fsp hal
    have hal220 : (fsp + 0x220#64) &&& 7#64 = 0#64 :=
      (fun (x : BitVec 64) (hx : x &&& 15#64 = 0#64) => show (x + 0x220#64) &&& 7#64 = 0#64 by bv_bits) fsp hal
    have hal300 : (fsp + 0x300#64) &&& 3#64 = 0#64 :=
      (fun (x : BitVec 64) (hx : x &&& 15#64 = 0#64) => show (x + 0x300#64) &&& 3#64 = 0#64 by bv_bits) fsp hal
    have hal304 : (fsp + 0x304#64) &&& 1#64 = 0#64 :=
      (fun (x : BitVec 64) (hx : x &&& 15#64 = 0#64) => show (x + 0x304#64) &&& 1#64 = 0#64 by bv_bits) fsp hal
    have hal320 : (fsp + 0x320#64) &&& 7#64 = 0#64 :=
      (fun (x : BitVec 64) (hx : x &&& 15#64 = 0#64) => show (x + 0x320#64) &&& 7#64 = 0#64 by bv_bits) fsp hal
    let _ := hne0
    let _ := hal3b8; let _ := hal380; let _ := hal3d8; let _ := hal3dc
    let _ := hal220; let _ := hal300; let _ := hal304; let _ := hal320
    dsimp only [r1b_opkStage2At, sevenBytesHeadAt]
    simp only [BitVec.add_assoc, BitVec.reduceAdd, sepConj_assoc]
    have hpc := hpc0; have hrun := hst.run; have hsp : s.sp = fsp := hst.sp
    apply r1b_seq_lscro_oom (mid := (blkPl_579).base + 9724#64) hst.inv
    dsimp only [runProgPlaced, lsProg_579]
    apply sepWP_seg_ls_vm (Q := (blkPC_579).rebase (blkPl_579).base (hooksException _))
      blkLib_eq_579 blk579_noSvc0 (mid := (blkPl_579).base + 9724#64)
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
      have hflip3b8 :
          ((fsp + 0x3b8#64) ↦₃₂ (b3 ++ b2 ++ b1 ++ b0)) ∗
            ((fsp + 0x3bc#64) ↦₈ b4) ∗ ((fsp + 0x3bd#64) ↦₈ b5) ∗
            ((fsp + 0x3be#64) ↦₈ b6) ⊢
          ((fsp + 0x3b8#64) ↦₈ b0) ∗ ((fsp + 0x3b9#64) ↦₈ b1) ∗
            ((fsp + 0x3ba#64) ↦₈ b2) ∗
            ((fsp + 0x3bb#64) ↦₃₂ (b6 ++ b5 ++ b4 ++ b3)) := by
        have heq := sevenBytesHeadAt_eq_tailAt (fsp + 0x3b8#64) b0 b1 b2 b3 b4 b5 b6
        dsimp only [sevenBytesHeadAt, sevenBytesTailAt] at heq
        simp only [BitVec.add_assoc, BitVec.reduceAdd] at heq
        rw [heq]; exact Entails.refl _
      refine r1b_sepWPp_frame_dct (by r1b_ac_dct) hflip3b8 (by r1b_ac_dct) ?_
      simp only [sepConj_assoc]
      have hpc : sm1.pc = (blkPl_579).base + 9724#64 := by simp only [hsm1, wp_norm, arm64_norm]
      have hrun : sm1.status = .Running := by simp only [hsm1, wp_norm, arm64_norm, hst.run]
      have hsp : sm1.sp = fsp := by simpa only [hsm1, wp_norm, arm64_norm] using hst.sp
      have hx24_1 : sm1.readReg64 (.gpr 24#5) = fsp + 0x380#64 := by
        simp only [hsm1, hx24, wp_norm, arm64_norm]
      let _ := hx24_1
      apply r1b_seq_lscro_oom (mid := (blkPl_579).base + 9744#64) hinv1
      apply sepWP_seg_ls_vm (Q := (blkPC_579).rebase (blkPl_579).base (hooksException _))
        blkLib_eq_579 blk579_noSvc0 (mid := (blkPl_579).base + 9744#64)
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
        have hw380 : (((((b3 ++ b2 ++ b1 ++ b0).zeroExtend 64).truncate 32) : BitVec 32)) =
            (b3 ++ b2 ++ b1 ++ b0) := by bv_bits
        let _ := hw380
        simp -failIfUnchanged only [hsm1, arm64_norm, hw380]
        have hflip380 :
            ((fsp + 0x380#64) ↦₃₂ (b3 ++ b2 ++ b1 ++ b0)) ∗
              ((fsp + 0x384#64) ↦₈ s2_b4) ∗ ((fsp + 0x385#64) ↦₈ s2_b5) ∗
              ((fsp + 0x386#64) ↦₈ s2_b6) ⊢
            ((fsp + 0x380#64) ↦₈ b0) ∗ ((fsp + 0x381#64) ↦₈ b1) ∗
              ((fsp + 0x382#64) ↦₈ b2) ∗
              ((fsp + 0x383#64) ↦₃₂ (s2_b6 ++ s2_b5 ++ s2_b4 ++ b3)) := by
          have heq := sevenBytesHeadAt_eq_tailAt (fsp + 0x380#64)
            b0 b1 b2 b3 s2_b4 s2_b5 s2_b6
          dsimp only [sevenBytesHeadAt, sevenBytesTailAt] at heq
          simp only [BitVec.add_assoc, BitVec.reduceAdd] at heq
          rw [heq]; exact Entails.refl _
        refine r1b_sepWPp_frame_dct (by r1b_ac_dct) hflip380 (by r1b_ac_dct) ?_
        simp only [sepConj_assoc]
        have hpc : sm2.pc = (blkPl_579).base + 9744#64 := by
          simp only [hsm2, hsm1, wp_norm, arm64_norm]
        have hrun : sm2.status = .Running := by
          simp only [hsm2, hsm1, wp_norm, arm64_norm, hst.run]
        have hsp : sm2.sp = fsp := by
          simpa only [hsm2, hsm1, wp_norm, arm64_norm] using hst.sp
        have hx24_2 : sm2.readReg64 (.gpr 24#5) = fsp + 0x380#64 := by
          simp only [hsm2, hsm1, hx24, wp_norm, arm64_norm]
        let _ := hx24_2
        apply r1b_seq_lscro_oom (mid := (blkPl_579).base + 10052#64) hinv2
        apply sepWP_seg_ls_vm (Q := (blkPC_579).rebase (blkPl_579).base (hooksException _))
          blkLib_eq_579 blk579_noSvc0 (mid := (blkPl_579).base + 10052#64)
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
          change SepWPp (runProgPlaced H) _ _ _ _ _ _
          have hback380 :
              ((fsp + 0x380#64) ↦₈ b0) ∗ ((fsp + 0x381#64) ↦₈ b1) ∗
                ((fsp + 0x382#64) ↦₈ b2) ∗
                ((fsp + 0x383#64) ↦₃₂ (b6 ++ b5 ++ b4 ++ b3)) ⊢
              sevenBytesHeadAt (fsp + 0x380#64) b0 b1 b2 b3 b4 b5 b6 := by
            have heq := (sevenBytesHeadAt_eq_tailAt (fsp + 0x380#64) b0 b1 b2 b3 b4 b5 b6).symm
            dsimp only [sevenBytesTailAt] at heq
            simp only [BitVec.add_assoc, BitVec.reduceAdd] at heq
            rw [heq]; exact Entails.refl _
          have hback3b8 :
              ((fsp + 0x3b8#64) ↦₈ b0) ∗ ((fsp + 0x3b9#64) ↦₈ b1) ∗
                ((fsp + 0x3ba#64) ↦₈ b2) ∗
                ((fsp + 0x3bb#64) ↦₃₂ (b6 ++ b5 ++ b4 ++ b3)) ⊢
              sevenBytesHeadAt (fsp + 0x3b8#64) b0 b1 b2 b3 b4 b5 b6 := by
            have heq := (sevenBytesHeadAt_eq_tailAt (fsp + 0x3b8#64) b0 b1 b2 b3 b4 b5 b6).symm
            dsimp only [sevenBytesTailAt] at heq
            simp only [BitVec.add_assoc, BitVec.reduceAdd] at heq
            rw [heq]; exact Entails.refl _
          have hback200 :
              ((fsp + 0x200#64) ↦₃₂ (c3_in ++ c2_in ++ c1_in ++ c0_in)) ∗
                ((fsp + 0x204#64) ↦₈ c4_in) ∗ ((fsp + 0x205#64) ↦₈ c5_in) ∗
                ((fsp + 0x206#64) ↦₈ c6_in) ⊢
              sevenBytesHeadAt (fsp + 0x200#64) c0_in c1_in c2_in c3_in c4_in c5_in c6_in := by
            dsimp only [sevenBytesHeadAt]
            simp only [BitVec.add_assoc, BitVec.reduceAdd]
            exact Entails.refl _
          refine r1b_sepWPp_frame_dct (by r1b_ac_dct)
            (sepConj_mono hback380 (sepConj_mono hback3b8 hback200)) (by r1b_ac_dct) ?_
          have hfold :
              (memRegion fsp 0x0e0 ∗
                ((fsp + 0x0e0#64) ↦₃₂ w0e0) ∗ ((fsp + 0x0e4#64) ↦₃₂ w0e4) ∗
                ((fsp + 0x0e8#64) ↦₆₄ w15) ∗ ((fsp + 0x0f0#64) ↦₆₄ spkW8.zeroExtend 64) ∗
                ((fsp + 0x0f8#64) ↦₆₄ spkW24) ∗ ((fsp + 0x100#64) ↦₆₄ spkW16) ∗
                ((fsp + 0x108#64) ↦₆₄ spkW0) ∗ memRegion (fsp + 0x1d0#64) 0x18 ∗
                ((fsp + 0x1e8#64) ↦₆₄ c23_in) ∗ ((fsp + 0x1f0#64) ↦₈ c31_in) ∗
                memRegion (fsp + 0x1f1#64) 7 ∗ ((fsp + 0x1f8#64) ↦₃₂ c9_in) ∗
                ((fsp + 0x1fc#64) ↦₁₆ c13_in) ∗ memRegion (fsp + 0x1fe#64) 2 ∗
                sevenBytesHeadAt (fsp + 0x200#64) c0_in c1_in c2_in c3_in c4_in c5_in c6_in ∗
                memRegion (fsp + 0x207#64) 0x19 ∗
                ((fsp + 0x220#64) ↦₆₄ w23) ∗ ((fsp + 0x228#64) ↦₈ b31) ∗
                memRegion (fsp + 0x229#64) 0x37 ∗ memRegion (fsp + 0x2c0#64) 0x40 ∗
                ((fsp + 0x300#64) ↦₃₂ w9) ∗ ((fsp + 0x304#64) ↦₁₆ w13) ∗
                memRegion (fsp + 0x306#64) 0x1a ∗
                ((fsp + 0x320#64) ↦₆₄ w23) ∗ ((fsp + 0x328#64) ↦₈ b31) ∗
                memRegion (fsp + 0x329#64) 0x57 ∗
                sevenBytesHeadAt (fsp + 0x380#64) b0 b1 b2 b3 b4 b5 b6 ∗
                memRegion (fsp + 0x387#64) 0x31 ∗
                sevenBytesHeadAt (fsp + 0x3b8#64) b0 b1 b2 b3 b4 b5 b6 ∗
                memRegion (fsp + 0x3bf#64) 0x19 ∗
                ((fsp + 0x3d8#64) ↦₃₂ w9) ∗ ((fsp + 0x3dc#64) ↦₁₆ w13) ∗
                memRegion (fsp + 0x3de#64) 0xf2) ⊢
              r1b_opkStage2At fsp spkW0 spkW8 spkW16 spkW24
                b0 b1 b2 b3 b4 b5 b6
                b0 b1 b2 b3 b4 b5 b6
                c0_in c1_in c2_in c3_in c4_in c5_in c6_in
                w0e0 w0e4 w9 w9 c9_in w13 w13 c13_in w15 w23 w23 c23_in b31 b31 c31_in := by
            dsimp only [r1b_opkStage2At]; exact Entails.of_eq (by r1b_ac_dct)
          refine r1b_sepWPp_frame_dct (by r1b_ac_dct) hfold (by r1b_ac_dct) ?_
          exact r1b_tail_2744_placed_fd (opkFlag := 1#32) hh hbnd
            (hok.of_step
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
              (by simp only [hsm3, hsm2, hsm1, wp_norm, arm64_norm]))
            (by simp only [hsm3, hsm2, hsm1, hx23, wp_norm, arm64_norm])
            (by change _ = fsp + 0x380#64; simp only [hsm3, hsm2, hsm1, hx24, wp_norm, arm64_norm])
            (by simp only [hsm3, hsm2, hsm1, wp_norm, arm64_norm])
            (by simp only [hsm3, hsm2, hsm1, wp_norm, arm64_norm])
            (by simp only [hsm3, hsm2, hsm1, hx27, wp_norm, arm64_norm])
            (by simp only [hsm3, hsm2, hsm1, hx28, wp_norm, arm64_norm])
            hpanic fun sf evs hfo hok_f hx23_f hx24_f hx25_f hx26_f hx28_f =>
              hk sf evs b0 b1 b2 b3 b4 b5 b6 w9 w13 w23 b31 hfo hok_f
                (fun p hp => by
                  injection hp with hp'
                  subst hp'
                  exact ⟨hv11c, hbytes⟩)
                hx23_f hx24_f hx25_f hx26_f hx28_f


theorem r1b_step_tail_25f4_placed_fd [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {H : LibsignalHooks} {B : RunBudgets} {S : RunSem} {resStack : Nat} :
    R1bStepTail25f4PlacedFd A lim H B S resStack :=
  fun hh hbnd hok hopk_sem hx23 hx24 hx25 hx27 hx28 hpanic hk =>
    r1b_step_tail_25f4_placed_raw_fd hh hbnd hok hopk_sem hx23 hx24 hx25 hx27 hx28 hpanic hk

end LibsignalBinary.Proofs.SignalSession.Cli.Run.Compose.Arms.R1b.DeserCloneTailPlacedBudgetFd
