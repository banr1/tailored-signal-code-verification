/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.Placed.BudgetVmSteps
public meta import LibsignalBinary.Proofs.Placed.BudgetVmSteps -- shake: keep
public meta import ProofLib -- shake: keep
public meta import Lean -- shake: keep
public import LibsignalBinary.Proofs.SignalSession.Cli.F3.HRead.FdThreadKit
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Compose.Arms.R1b.CallHelpersParsePlacedBudgetFd
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Compose.Arms.R1b.ReadRegSpkPlacedBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Compose.Arms.R1b.ReadRegSpkPlacedBudgetAux
import Arm64.Trusted.Spec.Hoare
import Arm64.Trusted.Spec.SepLogic
import LibsignalBinary.Proofs.Common.SharedHelpers
meta import LibsignalBinary.Proofs.Common.SharedHelpers -- shake: keep
import LibsignalBinary.Proofs.SignalSession.Cli.Main.Proofs.M4Layout

/-!
# `State.fs`- and `FdsGe3Closed`-Threaded Stage 1 `split_signed` Step (`0x1230 → 0x1260`) of Arm `R1b`

Proves `r1b_after_spk_dealloc_placed_fd` and `r1b_after_spk_dealloc_placed_fds` (`0x1230 → 0x1260`)
on Block `579`, preserving `State.fs` and `FdsGe3Closed` across `split_signed` on `spkBs`.
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 200000
set_option linter.unusedSimpArgs false

namespace LibsignalBinary.Proofs.SignalSession.Cli.Run.Compose.Arms.R1b.ReadRegSpkPlacedBudgetFd

open Arm64 Arm64.Process ProofLib SepProp
open CryptoVerification (LibsignalHooks LibsignalPlacement lsLogFilterAddr lsmpl)
open CryptoVerification.LibsignalTripleRatchetRepr (speWord)
open CryptoVerification.SignalSession.Cli (StoresGhost ofLe32 splitOkTag splitSigned utf8)
open CryptoVerification.SignalSession.Cli.MainHops (RunCall cliIo ownedBytes sepWPp_weaken_pre)
open CryptoVerification.SignalSession.Cli.Run.Placed (blkPl_579 lsProg_579)
open CryptoVerification.SignalSession.Cli.RunCompose
  (Init1Data PanicK RejectKind RunSem r1b_CodeOk r1b_ErrCtxPlaced r1b_OkCtxPlaced
   r1b_StackBounds r1b_bind_state_placed r1b_cell64_cons r1b_cmn1_false_of_lt63
   r1b_entails_frame_core r1b_errCommon r1b_fsp_align r1b_invCore_placed r1b_join_region
   r1b_none_spk_split r1b_ownedBytes_rejoin r1b_ownedRest r1b_sepWPp_borrow_core
   r1b_sepWPp_frame_core r1b_stage_to_err_placed r1b_u64_split32
   runFiles runFsp runPcPlaced_eq runProgPlaced)
open CryptoVerification.SignalSession.Cli.RunSkeleton (RunBudgets RunSlots runFrame)
open LibsignalBinary.Heap
  (AllocCostModel AllocEvent BudgetLimits FitsEnv FreeOnlyEvs RustCliAllocBudget)
open LibsignalBinary.Proofs.SignalSession.Cli.F3.HRead.ReadFileBudgetPlaced (FdsGe3Closed)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Compose.Arms.R1b.CallHelpersParsePlacedBudgetFd
  (r1b_call_splitSigned_placed_fd)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Compose.Arms.R1b.ErrCleanupPlacedBudget
  (sepWP_with_vm_oom)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Compose.Arms.R1b.ReadRegSpkPlacedBudgetAux
  (r1b_err_13bc_placed r1b_seq_lscro_oom)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Compose.HopsPlacedBudget (RejectKPlacedEnv)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DropSpeOwnedPlacedBudget
  (DropSpeOwnedOkAtBlock)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.SkeletonPlacedBudget
  (RunCalleesEnvs RunHooksPlaced)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.SkeletonPlacedBudgetFd (RunCalleesPlacedFd)

attribute [local irreducible] Program.fetch Program.externAt?
attribute [local simp, local arm64_norm, local wp_norm] runPcPlaced_eq BitVec.ofNat_eq_ofNat

local syntax "by_vm_open " tacticSeq : tactic
local elab_rules : tactic
  | `(tactic| by_vm_open $tac:tacticSeq) => do
    Lean.Elab.Tactic.evalTactic (← `(tactic| apply sepWP_with_vm_oom))
    let g ← Lean.Elab.Tactic.getMainGoal
    g.withContext do
      let ty := (← Lean.instantiateMVars (← g.getType)).consumeMData
      let e2 := ty.getArg! 0
      let e1 := e2.getArg! 0
      let ty1 := Lean.mkAppN ty.getAppFn #[e1, ty.getArg! 1, ty.getArg! 2, ty.getArg! 3, ty.getArg! 4, ty.getArg! 5]
      let g1 ← Lean.Meta.mkFreshExprMVar ty1
      let savedGoals ← Lean.Elab.Tactic.getGoals
      Lean.Elab.Tactic.setGoals [g1.mvarId!]
      Lean.Elab.Tactic.evalTactic (← `(tactic| ($tac)))
      let rem ← Lean.Elab.Tactic.getGoals
      unless rem.isEmpty do
        throwError "by_vm_open: inner tactic left {rem.length} unsolved goal(s)"
      Lean.Elab.Tactic.setGoals savedGoals.tail!
      let prf1 ← Lean.instantiateMVars g1
      let prf2 := prf1.replace fun sub =>
        if sub.eqv e2 then some e2 else if sub.eqv e1 then some e2 else none
      g.assign prf2

local macro (priority := high) "r1b_ac" : tactic =>
  `(tactic| ((try dsimp +zetaDelta only) <;> first | rfl | simp only [emp_sepConj] | sep_ac_rfl))

private meta def r1bStripLetsRB : Nat → Lean.Expr → Lean.Expr
  | 0, e => e
  | n + 1, .letE _ _ v b _ => r1bStripLetsRB n (b.instantiate1 v)
  | n + 1, .mdata _ e => r1bStripLetsRB n e
  | _, e => e

private meta def r1bSplitSepRB : Nat → Lean.Expr → Lean.Expr → Array Lean.Expr
  | 0, _, e => #[e]
  | fuel + 1, sepSample, e =>
    let e := r1bStripLetsRB 64 e
    let fn := sepSample.getAppFn.constName!
    let ar := sepSample.getAppNumArgs
    if e.isAppOfArity fn ar then
      r1bSplitSepRB fuel sepSample (e.getArg! (ar - 2)) ++
        r1bSplitSepRB fuel sepSample (e.getArg! (ar - 1))
    else #[e]

private meta def r1bIsDefEqPureRB (x a : Lean.Expr) : Lean.Elab.TermElabM Bool := do
  let x := r1bStripLetsRB 64 x; let a := r1bStripLetsRB 64 a
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

private meta def r1bComputeRestRB (ctxName : String) (p a1 : Lean.Expr) :
    Lean.Elab.TermElabM Lean.Expr := do
  let sepTy := Lean.mkConst ``SepProp []
  let sepSample ← Lean.Elab.Term.elabTerm (← `(emp ∗ emp)) (some sepTy)
  let empExpr ← Lean.Elab.Term.elabTerm (← `(emp)) (some sepTy)
  let ps := (r1bSplitSepRB 64 sepSample (← Lean.instantiateMVars p)).toList
  let a1s := (r1bSplitSepRB 64 sepSample (← Lean.instantiateMVars a1)).toList
  let mut rem := ps
  for a in a1s do
    let mut removed := false
    let mut next : List Lean.Expr := []
    for x in rem do
      if !removed && (← r1bIsDefEqPureRB x a) then removed := true
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

local elab (priority := high) "r1b_entails_frame " t1:term:arg h:term:arg t2:term:arg :
    term <= expectedType => do
  let exp ← Lean.instantiateMVars expectedType
  if exp.isMVar then Lean.Elab.Term.tryPostpone
  let entSample ← Lean.Elab.Term.elabTerm (← `(emp ⊢ emp)) none
  let ear := entSample.getAppNumArgs
  let expS := r1bStripLetsRB 64 exp
  let p := expS.getArg! (ear - 2)
  let q := expS.getArg! (ear - 1)
  if (← Lean.instantiateMVars p).isMVar then Lean.Elab.Term.tryPostpone
  if (← Lean.instantiateMVars q).isMVar then Lean.Elab.Term.tryPostpone
  let hExpr ← Lean.Elab.Term.elabTerm h none
  let hTy := r1bStripLetsRB 64 (← Lean.instantiateMVars (← Lean.Meta.inferType hExpr))
  let a1 := hTy.getArg! (ear - 2)
  let a2 := hTy.getArg! (ear - 1)
  let r ← r1bComputeRestRB "r1b_entails_frame" p a1
  let sepTy := Lean.mkConst ``SepProp []
  let empExpr ← Lean.Elab.Term.elabTerm (← `(emp)) (some sepTy)
  let sepSample ← Lean.Elab.Term.elabTerm (← `(emp ∗ emp)) (some sepTy)
  let sar := sepSample.getAppNumArgs
  let mkSep (x y : Lean.Expr) : Lean.Expr :=
    sepSample.withApp fun f args => Lean.mkAppN f (args.extract 0 (sar - 2) ++ #[x, y])
  let rIsEmp ← r1bIsDefEqPureRB r empExpr
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

local elab (priority := high) "r1b_sepWPp_frame " t1:term:arg h:term:arg t2:term:arg hk:term:arg :
    term <= expectedType => do
  let exp ← Lean.instantiateMVars expectedType
  if exp.isMVar then Lean.Elab.Term.tryPostpone
  let expS := r1bStripLetsRB 64 exp
  let args := expS.getAppArgs
  let prog := args[0]!; let ret := args[1]!; let st := args[2]!; let p := args[3]!
  let q := args[4]!; let qp := args[5]!; let oom := args[6]!
  let entSample ← Lean.Elab.Term.elabTerm (← `(emp ⊢ emp)) none
  let ear := entSample.getAppNumArgs
  let hExpr ← Lean.Elab.Term.elabTerm h none
  let hTy := r1bStripLetsRB 64 (← Lean.instantiateMVars (← Lean.Meta.inferType hExpr))
  let a1 := hTy.getArg! (ear - 2)
  let a2 := hTy.getArg! (ear - 1)
  let r ← r1bComputeRestRB "r1b_sepWPp_frame" p a1
  let sepTy := Lean.mkConst ``SepProp []
  let empExpr ← Lean.Elab.Term.elabTerm (← `(emp)) (some sepTy)
  let sepSample ← Lean.Elab.Term.elabTerm (← `(emp ∗ emp)) (some sepTy)
  let sar := sepSample.getAppNumArgs
  let mkSep (x y : Lean.Expr) : Lean.Expr :=
    sepSample.withApp fun f args => Lean.mkAppN f (args.extract 0 (sar - 2) ++ #[x, y])
  let rIsEmp ← r1bIsDefEqPureRB r empExpr
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
    let a2IsEmp ← r1bIsDefEqPureRB a2 empExpr
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

local elab:10 (priority := high) "r1b_call_frame" "<|" h:term:10 : term <= expectedType => do
  let exp ← Lean.instantiateMVars expectedType
  if exp.isMVar then Lean.Elab.Term.tryPostpone
  let expS := r1bStripLetsRB 64 exp
  let hExpr ← Lean.Elab.Term.elabTerm h none
  let hTy0 := r1bStripLetsRB 64 (← Lean.instantiateMVars (← Lean.Meta.inferType hExpr))
  for idx in [0, 1, 2, 4, 5, 6] do
    if !(← Lean.Meta.withReducibleAndInstances <| Lean.Meta.isDefEq (hTy0.getArg! idx) (expS.getArg! idx)) then
      discard <| Lean.Meta.isDefEq (hTy0.getArg! idx) (expS.getArg! idx)
  let p ← Lean.instantiateMVars (expS.getArg! 3)
  let p' ← Lean.instantiateMVars ((r1bStripLetsRB 64 (← Lean.instantiateMVars hTy0)).getArg! 3)
  let sepTy := Lean.mkConst ``SepProp []
  let sepSample ← Lean.Elab.Term.elabTerm (← `(emp ∗ emp)) (some sepTy)
  let empExpr ← Lean.Elab.Term.elabTerm (← `(emp)) (some sepTy)
  let sar := sepSample.getAppNumArgs
  let mkSep (x y : Lean.Expr) : Lean.Expr :=
    sepSample.withApp fun f args => Lean.mkAppN f (args.extract 0 (sar - 2) ++ #[x, y])
  let ps := (r1bSplitSepRB 64 sepSample p).toList
  let p's := (r1bSplitSepRB 64 sepSample p').toList
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
      if !removed && (← r1bIsDefEqPureRB x a) then removed := true
      else next := next.concat x
    if !removed then
      throwError "r1b_call_frame: unmatched callee atom:\n  {a}\nin:\n  {rem}"
    rem := next
  let remProd := match rem.reverse with
    | [] => empExpr
    | last :: rest => rest.foldl (fun acc x => mkSep x acc) last
  if let some mf := mvarFOpt then
    discard <| Lean.Meta.isDefEq mf remProd
  let eqTy ← Lean.Meta.mkEq (← Lean.instantiateMVars p) (← Lean.instantiateMVars p')
  let eqProof ← Lean.Elab.Term.elabTerm (← `(by r1b_ac)) (some eqTy)
  let ent ← Lean.Meta.mkAppM ``Entails.of_eq #[eqProof]
  Lean.Meta.mkAppM ``sepWPp_weaken_pre #[ent, hExpr]

/-! ## `split_signed` Step (`0x1230 → 0x1260`) -/

set_option maxHeartbeats 800000 in
private theorem r1b_after_spk_dealloc_err_placed_fd [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {st : M.σ}
    {EnvAt : StoresGhost → RejectKind → M.σ → Prop}
    {H : LibsignalHooks} {B : RunBudgets}
    {g : RunCall} {d : Init1Data} {s0 sf1 : State} {resStack : Nat}
    {r0 r1 r2 r3 : BitVec 8}
    {eCap ePtr regCap regPtr spkCap spkPtr : BitVec 64} {eBs spkBs : List (BitVec 8)}
    {Q Qp : State → SepProp → Prop} {oom : State → SepProp}
    (hh : RunHooksPlaced A lim H)
    (hdrop : DropSpeOwnedOkAtBlock (runProgPlaced H) A lim)
    (hbnd : r1b_StackBounds B resStack)
    (hc1 : r1b_ErrCtxPlaced r1b_CodeOk g d s0 sf1 0x1248)
    (hspk_le : spkBs.length ≤ spkCap.toNat)
    (hspk_lt : spkCap.toNat < 2 ^ 63) (hspk_ne : spkPtr ≠ 0)
    (henv : ∀ evsFree, FreeOnlyEvs evsFree →
      EnvAt StoresGhost.opened .postDispatch (M.stepEvents evsFree st))
    (hpanic : PanicK g s0 Qp)
    (hrej : RejectKPlacedEnv r1b_CodeOk H A lim EnvAt g s0 resStack Q Qp oom) :
    let fsp := runFsp s0
    SepWPp (runProgPlaced H) (s0.readReg64 .lr) sf1
      (((fsp + 0x4d0#64) ↦₆₄ speWord 1) ∗
        ((fsp + 0x4d0#64 + 8#64) ↦₆₄ eCap) ∗ ((fsp + 0x4d0#64 + 16#64) ↦₆₄ ePtr) ∗
        ((fsp + 0x4d0#64 + 24#64) ↦₆₄ BitVec.ofNat 64 eBs.length) ∗
        memRegion (fsp + 0x4d0#64 + 32#64) 16 ∗
        ownedBytes A.repAlloc eCap ePtr (BitVec.ofNat 64 eBs.length) eBs ∗
        (spkPtr ↦ₛ spkBs) ∗
        stackAt fsp (resStack - runFrame) ∗ A.pool lim st sf1 ∗
        (r1b_ownedRest A.repAlloc spkCap spkPtr spkBs.length ∗
          ((fsp + 0x168#64) ↦₆₄ spkPtr) ∗
          ownedBytes A.repAlloc regCap regPtr 4#64 [r0, r1, r2, r3] ∗
          r1b_invCore_placed A.repAlloc g d s0 ∗ (lsLogFilterAddr ↦₆₄ 0#64) ∗
          ownedBytes A.repAlloc d.dirCap d.dirPtr (BitVec.ofNat 64 d.dir.length) d.dir ∗
          memRegion fsp 0x110 ∗ memRegion (fsp + 0x110#64) 8 ∗ memRegion (fsp + 0x11c#64) 4 ∗
          memRegion (fsp + 0x120#64) 16 ∗ memRegion (fsp + 0x130#64) 0x20 ∗
          memRegion (fsp + 0x150#64) 16 ∗ ((fsp + 0x164#64) ↦₃₂ ofLe32 r0 r1 r2 r3) ∗
          ((fsp + 0x170#64) ↦₆₄ spkCap) ∗
          memRegion (fsp + 0x178#64) 8 ∗ memRegion (fsp + 0x188#64) 8 ∗
          ((fsp + 0x190#64) ↦₆₄ d.ikW3) ∗ ((fsp + 0x198#64) ↦₆₄ regCap) ∗
          ((fsp + 0x1a0#64) ↦₆₄ regPtr) ∗ ((fsp + 0x1a8#64) ↦₆₄ d.ikW1) ∗
          ((fsp + 0x1b0#64) ↦₃₂ d.peerV.device.zeroExtend 32) ∗
          memRegion (fsp + 0x1b4#64) 4 ∗ memRegion (fsp + 0x1750#64) 24))
      Q Qp oom := by
  intro fsp
  generalize hinvCore : r1b_invCore_placed A.repAlloc g d s0 = invCore
  have hin1 := hc1.st
  have hal : fsp &&& 15#64 = 0#64 := r1b_fsp_align hin1.sp hin1.spAligned
  have hrejoin := r1b_ownedBytes_rejoin A.repAlloc spkCap spkPtr spkBs hspk_le hspk_lt hspk_ne
  have he8 : ((fsp + 0x4e8#64) ↦₆₄ BitVec.ofNat 64 eBs.length) =
      ((fsp + 0x4e8#64) ↦₃₂ (BitVec.ofNat 64 eBs.length).truncate 32) ∗
        ((fsp + 0x4ec#64) ↦₃₂ ((BitVec.ofNat 64 eBs.length) >>> 32).truncate 32) := by
    have hz := r1b_u64_split32 (fsp + 0x4e8#64) (BitVec.ofNat 64 eBs.length)
    have ha : (fsp + 0x4e8#64) + 4#64 = fsp + 0x4ec#64 := by bv_omega
    rwa [ha] at hz
  refine r1b_sepWPp_frame (by r1b_ac) hrejoin (by r1b_ac) ?_
  simp only [BitVec.add_assoc, BitVec.reduceAdd]
  rw [he8]; simp only [sepConj_assoc]; dsimp only [speWord]
  have hpc1 := hin1.pc; change sf1.pc = (blkPl_579).base + 4680#64 at hpc1
  have hrun1 := hin1.run; have hsp1 : sf1.sp = fsp := hin1.sp
  apply r1b_seq_lscro_oom (mid := (blkPl_579).base + 5052#64) hin1.inv
  dsimp only [runProgPlaced, lsProg_579]
  by_vm_open (
    wp_steps
    refine SepWP.done (by simp only [wp_norm, arm64_norm, *]; try bv_omega)
      (by simp only [wp_norm, arm64_norm, *])
      ⟨by simp only [wp_norm, arm64_norm, *], fun hvm2 => ?_⟩
    refine r1b_bind_state_placed fun sm2 hsm2 hinv2 => ?_
    rw [← hsm2] at hvm2
    rw [← A.pool_transport lim st sf1 sm2 hvm2]
    change SepWPp (runProgPlaced H) _ _ _ _ _ _
    have hc2 : r1b_ErrCtxPlaced r1b_CodeOk g d s0 sm2 0x13bc := hc1.of_step
      { pc := by simp only [hsm2, wp_norm, arm64_norm]
        run := by simp only [hsm2, wp_norm, arm64_norm, hin1.run]
        sp := by simpa only [hsm2, wp_norm, arm64_norm] using hin1.sp
        fp := by simpa only [hsm2, wp_norm, arm64_norm] using hin1.fp
        inv := hinv2
        vregs := by simpa only [calleeSavedVRegs, hsm2, wp_norm, arm64_norm] using hin1.vregs
        spAligned := hin1.spAligned }
      (by simp only [hsm2, wp_norm, arm64_norm]) (by simp only [hsm2, wp_norm, arm64_norm])
      (by simp only [hsm2, wp_norm, arm64_norm]) (by simp only [hsm2, wp_norm, arm64_norm])
      (by simp only [hsm2, wp_norm, arm64_norm])
    have he8' : ((fsp + 0x4e8#64) ↦₃₂ (BitVec.ofNat 64 eBs.length).truncate 32) ∗
        ((fsp + 0x4ec#64) ↦₃₂ ((BitVec.ofNat 64 eBs.length) >>> 32).truncate 32) ⊢
        ((fsp + 0x4e8#64) ↦₆₄ BitVec.ofNat 64 eBs.length) := by
      rw [← he8]; exact Entails.refl _
    generalize herrCommon :
      r1b_errCommon (A.atState lim st sm2) g d s0 resStack = errCommon
    have hst_err :
        (invCore ∗ (lsLogFilterAddr ↦₆₄ 0#64) ∗
          ownedBytes A.repAlloc d.dirCap d.dirPtr (BitVec.ofNat 64 d.dir.length) d.dir ∗
          memRegion fsp 0x110 ∗ memRegion (fsp + 0x130#64) 0x20 ∗
          ((fsp + 0x164#64) ↦₃₂ ofLe32 r0 r1 r2 r3) ∗ ((fsp + 0x190#64) ↦₆₄ d.ikW3) ∗
          ((fsp + 0x1a8#64) ↦₆₄ d.ikW1) ∗ ((fsp + 0x1b0#64) ↦₃₂ d.peerV.device.zeroExtend 32) ∗
          memRegion (fsp + 0x1b4#64) 4 ∗ memRegion (fsp + 0x1750#64) 24 ∗
          stackAt fsp (resStack - runFrame) ∗ A.pool lim st sm2) ⊢
          errCommon ∗ memRegion (fsp + 0x190#64) 8 ∗ memRegion (fsp + 0x1a8#64) 16 := by
      rw [← hinvCore, ← herrCommon]
      exact r1b_stage_to_err_placed (A.atState lim st sm2) g d s0 resStack (ofLe32 r0 r1 r2 r3)
    have h188 : memRegion (fsp + 0x188#64) 8 ∗ memRegion (fsp + 0x190#64) 8 ⊢
        memRegion (fsp + 0x188#64) 16 := by
      rw [r1b_join_region fsp 0x188 8 8]; exact Entails.refl _
    have hex :
        (memRegion (fsp + 0x188#64) 8 ∗
          (invCore ∗ (lsLogFilterAddr ↦₆₄ 0#64) ∗
            ownedBytes A.repAlloc d.dirCap d.dirPtr (BitVec.ofNat 64 d.dir.length) d.dir ∗
            memRegion fsp 0x110 ∗ memRegion (fsp + 0x130#64) 0x20 ∗
            ((fsp + 0x164#64) ↦₃₂ ofLe32 r0 r1 r2 r3) ∗ ((fsp + 0x190#64) ↦₆₄ d.ikW3) ∗
            ((fsp + 0x1a8#64) ↦₆₄ d.ikW1) ∗ ((fsp + 0x1b0#64) ↦₃₂ d.peerV.device.zeroExtend 32) ∗
            memRegion (fsp + 0x1b4#64) 4 ∗ memRegion (fsp + 0x1750#64) 24 ∗
            stackAt fsp (resStack - runFrame) ∗ A.pool lim st sm2)) ⊢
          errCommon ∗ memRegion (fsp + 0x188#64) 16 ∗ memRegion (fsp + 0x1a8#64) 16 :=
      Entails.trans (sepConj_mono_right hst_err)
        (r1b_entails_frame (by r1b_ac) h188 (by r1b_ac))
    have hcl := r1b_err_13bc_placed (st := st) (eCap := eCap) (ePtr := ePtr) (eBs := eBs)
      (spkCap := spkCap) (spkPtr := spkPtr) (spkBs := spkBs)
      (regCap := regCap) (regPtr := regPtr) (regBs := [r0, r1, r2, r3]) hh hdrop hbnd hc2
      (by simp only [hsm2, wp_norm, arm64_norm, speWord])
      (by simp only [hsm2, wp_norm, arm64_norm])
      (by simp only [hsm2, wp_norm, arm64_norm])
      (by simp only [hsm2, wp_norm, arm64_norm])
      henv hpanic hrej
    dsimp only at hcl
    rw [herrCommon] at hcl
    refine sepWPp_weaken_pre ?_ hcl
    exact r1b_entails_frame (by r1b_ac) (sepConj_mono he8' hex) (by r1b_ac)
  )

set_option maxHeartbeats 600000 in
theorem r1b_after_spk_dealloc_placed_fd [LibsignalPlacement] {M : AllocCostModel}
    {S : RunSem} {A : RustCliAllocBudget M} {lim : BudgetLimits} {st : M.σ}
    {cEnvs : RunCalleesEnvs} {EnvAt : StoresGhost → RejectKind → M.σ → Prop}
    {H : LibsignalHooks} {B : RunBudgets} {σ : RunSlots}
    {g : RunCall} {d : Init1Data} {s0 s : State} {resStack : Nat}
    {r0 r1 r2 r3 : BitVec 8}
    {regCap regPtr spkCap spkPtr : BitVec 64} {spkBs : List (BitVec 8)}
    {Q Qp : State → SepProp → Prop} {oom : State → SepProp}
    (hh : RunHooksPlaced A lim H)
    (hc : RunCalleesPlacedFd A lim cEnvs H B σ)
    (hdrop : DropSpeOwnedOkAtBlock (runProgPlaced H) A lim)
    (hbnd : r1b_StackBounds B resStack)
    (hok : r1b_OkCtxPlaced r1b_CodeOk S g d s0 s 0x1230)
    (hreg_rd :
      cliIo.rd (runFiles g.i) (d.dir ++ [0x2f#8] ++ utf8 "registration-id") = .ok [r0, r1, r2, r3])
    (hspk_rd : cliIo.rd (runFiles g.i) (d.dir ++ [0x2f#8] ++ utf8 "signed-pre-key") = .ok spkBs)
    (hx23 : s.readReg64 (.gpr 23#5) = spkCap)
    (hx9 : s.readReg64 (.gpr 9#5) = spkPtr)
    (hx2 : s.readReg64 .x2 = BitVec.ofNat 64 spkBs.length)
    (hx26 : s.readReg64 (.gpr 26#5) = d.dirPtr)
    (hx28 : s.readReg64 (.gpr 28#5) = BitVec.ofNat 64 d.dir.length)
    (hfit_sp : FitsEnv M lim st (cEnvs.splitSigned spkBs))
    (henv_sp_err : ∀ evsSp evsFree2,
      splitSigned spkBs = none →
      cEnvs.splitSigned spkBs evsSp →
      FreeOnlyEvs evsFree2 →
      EnvAt StoresGhost.opened .postDispatch (M.stepEvents (evsSp ++ evsFree2) st))
    (hpanic : PanicK g s0 Qp)
    (hrej : RejectKPlacedEnv r1b_CodeOk H A lim EnvAt g s0 resStack Q Qp oom)
    (hk : ∀ (sf : State) (evsSp : List AllocEvent)
        (spkId : BitVec 32) (spkKey spkSig : List (BitVec 8)),
      cEnvs.splitSigned spkBs evsSp →
      r1b_OkCtxPlaced r1b_CodeOk S g d s0 sf 0x1260 →
      splitSigned spkBs = some (spkId, spkKey, spkSig) →
      sf.fs = s.fs →
      sf.readReg64 (.gpr 10#5) = spkPtr + 4#64 →
      sf.readReg64 (.gpr 27#5) = BitVec.ofNat 64 spkKey.length →
      sf.readReg64 .x2 = spkId.zeroExtend 64 →
      sf.readReg64 (.gpr 26#5) = d.dirPtr →
      sf.readReg64 (.gpr 28#5) = BitVec.ofNat 64 d.dir.length →
      let fsp := runFsp s0
      SepWPp (runProgPlaced H) (s0.readReg64 .lr) sf
        (((fsp + 0x4f0#64) ↦₆₄ (spkPtr + 4#64 + BitVec.ofNat 64 spkKey.length)) ∗
          ((fsp + 0x4f8#64) ↦₆₄ 64#64) ∗ memRegion (fsp + 0x4d0#64) 32 ∗
          ownedBytes A.repAlloc spkCap spkPtr (BitVec.ofNat 64 spkBs.length) spkBs ∗
          ownedBytes A.repAlloc regCap regPtr 4#64 [r0, r1, r2, r3] ∗
          r1b_invCore_placed A.repAlloc g d s0 ∗ (lsLogFilterAddr ↦₆₄ 0#64) ∗
          ownedBytes A.repAlloc d.dirCap d.dirPtr (BitVec.ofNat 64 d.dir.length) d.dir ∗
          memRegion fsp 0x110 ∗ memRegion (fsp + 0x110#64) 8 ∗ memRegion (fsp + 0x11c#64) 4 ∗
          memRegion (fsp + 0x120#64) 16 ∗ memRegion (fsp + 0x130#64) 0x20 ∗
          memRegion (fsp + 0x150#64) 16 ∗ ((fsp + 0x164#64) ↦₃₂ ofLe32 r0 r1 r2 r3) ∗
          ((fsp + 0x168#64) ↦₆₄ spkPtr) ∗ ((fsp + 0x170#64) ↦₆₄ spkCap) ∗
          memRegion (fsp + 0x178#64) 8 ∗ memRegion (fsp + 0x188#64) 8 ∗
          ((fsp + 0x190#64) ↦₆₄ d.ikW3) ∗ ((fsp + 0x198#64) ↦₆₄ regCap) ∗
          ((fsp + 0x1a0#64) ↦₆₄ regPtr) ∗ ((fsp + 0x1a8#64) ↦₆₄ d.ikW1) ∗
          ((fsp + 0x1b0#64) ↦₃₂ d.peerV.device.zeroExtend 32) ∗
          memRegion (fsp + 0x1b4#64) 4 ∗ memRegion (fsp + 0x1750#64) 24 ∗
          stackAt fsp (resStack - runFrame) ∗
          A.pool lim (M.stepEvents evsSp st) sf)
        Q Qp oom) :
    let fsp := runFsp s0
    SepWPp (runProgPlaced H) (s0.readReg64 .lr) s
      (memRegion (fsp + 0x4d0#64) 48 ∗
        ownedBytes A.repAlloc spkCap spkPtr (BitVec.ofNat 64 spkBs.length) spkBs ∗
        ownedBytes A.repAlloc regCap regPtr 4#64 [r0, r1, r2, r3] ∗
        r1b_invCore_placed A.repAlloc g d s0 ∗ (lsLogFilterAddr ↦₆₄ 0#64) ∗
        ownedBytes A.repAlloc d.dirCap d.dirPtr (BitVec.ofNat 64 d.dir.length) d.dir ∗
        memRegion fsp 0x110 ∗ memRegion (fsp + 0x110#64) 8 ∗ memRegion (fsp + 0x11c#64) 4 ∗
        memRegion (fsp + 0x120#64) 16 ∗ memRegion (fsp + 0x130#64) 0x20 ∗
        memRegion (fsp + 0x150#64) 16 ∗ ((fsp + 0x164#64) ↦₃₂ ofLe32 r0 r1 r2 r3) ∗
        memRegion (fsp + 0x168#64) 8 ∗ ((fsp + 0x170#64) ↦₆₄ spkCap) ∗
        memRegion (fsp + 0x178#64) 8 ∗ memRegion (fsp + 0x188#64) 8 ∗
        ((fsp + 0x190#64) ↦₆₄ d.ikW3) ∗ ((fsp + 0x198#64) ↦₆₄ regCap) ∗
        ((fsp + 0x1a0#64) ↦₆₄ regPtr) ∗ ((fsp + 0x1a8#64) ↦₆₄ d.ikW1) ∗
        ((fsp + 0x1b0#64) ↦₃₂ d.peerV.device.zeroExtend 32) ∗
        memRegion (fsp + 0x1b4#64) 4 ∗ memRegion (fsp + 0x1750#64) 24 ∗
        stackAt fsp (resStack - runFrame) ∗ A.pool lim st s)
      Q Qp oom := by
  intro fsp
  let _ := hreg_rd
  generalize hinvCore : r1b_invCore_placed A.repAlloc g d s0 = invCore at *
  have hst := hok.st; have hpc := hst.pc; have hrun := hst.run
  have hsp : s.sp = fsp := hst.sp
  have hal : fsp &&& 15#64 = 0#64 := r1b_fsp_align hst.sp hst.spAligned
  rw [ProofLib.memRegion_eight (fsp + 0x168#64)]
  simp only [sepExists_sepConj_left, sepExists_sepConj_right]
  refine SepWPp.exists_elim fun v168 =>
    r1b_call_frame <| r1b_sepWPp_borrow_core A.repAlloc (cap := spkCap) (ptr := spkPtr)
      (len := BitVec.ofNat 64 spkBs.length) (bs := spkBs)
      fun ⟨_, hspk_le, hspk_lt, hspk_ne⟩ => ?_
  have hcmn_f : (spkCap + 1#64 == 0#64) = false := beq_false_of_ne (r1b_cmn1_false_of_lt63 hspk_lt)
  have hlen_nat : (BitVec.ofNat 64 spkBs.length).toNat = spkBs.length := by
    simp only [BitVec.toNat_ofNat]; omega
  change s.pc = (blkPl_579).base + 4656#64 at hpc
  apply r1b_seq_lscro_oom (mid := lsmpl.base 592) hst.inv
  dsimp only [runProgPlaced, lsProg_579]
  by_vm_open (
    wp_steps
    refine SepWP.done (by simp only [wp_norm, arm64_norm, *]; try bv_omega)
      (by simp only [wp_norm, arm64_norm, *])
      ⟨by simp only [wp_norm, arm64_norm, *], fun hvm1 => ?_⟩
    refine r1b_bind_state_placed fun sm1 hsm1 hinv1 => ?_
    have hfs_sm1 : sm1.fs = s.fs := by simp only [hsm1, wp_norm, arm64_norm]
    rw [← hsm1] at hvm1
    rw [← A.pool_transport lim st s sm1 hvm1]
    change SepWPp (runProgPlaced H) _ _ _ _ _ _
    refine r1b_call_frame <|
      r1b_call_splitSigned_placed_fd (g := g) (ret := fsp + 0x4d0#64) (fp := spkPtr) (file := spkBs)
        hh hc hbnd hinv1
        (by simp only [hsm1, wp_norm, arm64_norm])
        (by simp only [hsm1, wp_norm, arm64_norm, hst.run])
        (by simpa only [hsm1, wp_norm, arm64_norm] using hst.sp)
        (by simpa only [hsm1, wp_norm, arm64_norm] using hst.fp)
        (by simpa only [calleeSavedVRegs, hsm1, wp_norm, arm64_norm] using hst.vregs)
        hst.spAligned (retOff := 0x1248)
        (by simp only [hsm1, wp_norm, arm64_norm])
        (by simp only [hsm1, wp_norm, arm64_norm])
        (by simp only [hsm1, wp_norm, arm64_norm])
        (by simp only [hsm1, wp_norm, arm64_norm, hx2]; exact hlen_nat)
        hfit_sp hpanic
        (fun sf1 evsSp eCap ePtr eBs hevsSp hin1 hcs1 hsp_none hfs1 htr1 => ?_)
        (fun sf1 evsSp spkId spkKey spkSig hevsSp hin1 hcs1 hsp_ok hfs_eq1 hfs1 htr1 => ?_)
    · have hok1 : r1b_OkCtxPlaced r1b_CodeOk S g d s0 sf1 0x1248 := hok.after_call
        (by simp only [hsm1, wp_norm, arm64_norm]) (by simp only [hsm1, wp_norm, arm64_norm])
        (by simp only [hsm1, wp_norm, arm64_norm]) (by simp only [hsm1, wp_norm, arm64_norm])
        (by simp only [hsm1, wp_norm, arm64_norm]) (by simp only [hsm1, wp_norm, arm64_norm])
        hin1 hcs1 hfs1 htr1
      have hc1 : r1b_ErrCtxPlaced r1b_CodeOk g d s0 sf1 0x1248 :=
        hok1.to_err (r1b_none_spk_split hspk_rd hsp_none)
      have hcl := r1b_after_spk_dealloc_err_placed_fd (st := M.stepEvents evsSp st)
        (r0 := r0) (r1 := r1) (r2 := r2) (r3 := r3)
        (eCap := eCap) (ePtr := ePtr) (regCap := regCap) (regPtr := regPtr)
        (spkCap := spkCap) (spkPtr := spkPtr) (eBs := eBs) (spkBs := spkBs)
        hh hdrop hbnd hc1 hspk_le hspk_lt hspk_ne
        (fun evsFree2 hfo2 => by
          rw [← M.stepEvents_append]
          exact henv_sp_err evsSp evsFree2 hsp_none hevsSp hfo2)
        hpanic hrej
      dsimp only at hcl
      rw [hinvCore] at hcl
      refine sepWPp_weaken_pre ?_ hcl
      exact Entails.of_eq (by r1b_ac)
    · have hok1 : r1b_OkCtxPlaced r1b_CodeOk S g d s0 sf1 0x1248 := hok.after_call
        (by simp only [hsm1, wp_norm, arm64_norm]) (by simp only [hsm1, wp_norm, arm64_norm])
        (by simp only [hsm1, wp_norm, arm64_norm]) (by simp only [hsm1, wp_norm, arm64_norm])
        (by simp only [hsm1, wp_norm, arm64_norm]) (by simp only [hsm1, wp_norm, arm64_norm])
        hin1 hcs1 hfs1 htr1
      have hx26_1 : sf1.readReg64 (.gpr 26#5) = d.dirPtr :=
        hcs1.2.2.2.2.2.2.2.1.trans (by simpa only [hsm1, wp_norm, arm64_norm] using hx26)
      have hx28_1 : sf1.readReg64 (.gpr 28#5) = BitVec.ofNat 64 d.dir.length :=
        hcs1.2.2.2.2.2.2.2.2.2.1.trans (by simpa only [hsm1, wp_norm, arm64_norm] using hx28)
      have hrejoin := r1b_ownedBytes_rejoin A.repAlloc spkCap spkPtr spkBs hspk_le hspk_lt hspk_ne
      refine r1b_sepWPp_frame (by r1b_ac) hrejoin (by r1b_ac) ?_
      simp only [BitVec.add_assoc, BitVec.reduceAdd]; dsimp only [splitOkTag]
      have hpc1 := hin1.pc; change sf1.pc = (blkPl_579).base + 4680#64 at hpc1
      have hrun1 := hin1.run; have hsp1 : sf1.sp = fsp := hin1.sp
      apply r1b_seq_lscro_oom (mid := (blkPl_579).base + 4704#64) hin1.inv
      dsimp only [runProgPlaced, lsProg_579]
      by_vm_open (
        wp_steps
        refine SepWP.done (by simp only [wp_norm, arm64_norm, *]; try bv_omega)
          (by simp only [wp_norm, arm64_norm, *])
          ⟨by simp only [wp_norm, arm64_norm, *], fun hvm2 => ?_⟩
        refine r1b_bind_state_placed fun sm2 hsm2 hinv2 => ?_
        have hfs_sm2 : sm2.fs = sf1.fs := by simp only [hsm2, wp_norm, arm64_norm]
        rw [← hsm2] at hvm2
        rw [← A.pool_transport lim (M.stepEvents evsSp st) sf1 sm2 hvm2]
        change SepWPp (runProgPlaced H) _ _ _ _ _ _
        have hok2 : r1b_OkCtxPlaced r1b_CodeOk S g d s0 sm2 0x1260 := hok1.of_step
          { pc := by simp only [hsm2, wp_norm, arm64_norm]
            run := by simp only [hsm2, wp_norm, arm64_norm, hin1.run]
            sp := by simpa only [hsm2, wp_norm, arm64_norm] using hin1.sp
            fp := by simpa only [hsm2, wp_norm, arm64_norm] using hin1.fp
            inv := hinv2
            vregs := by simpa only [calleeSavedVRegs, hsm2, wp_norm, arm64_norm] using hin1.vregs
            spAligned := hst.spAligned }
          (by simp only [hsm2, wp_norm, arm64_norm]) (by simp only [hsm2, wp_norm, arm64_norm])
          (by simp only [hsm2, wp_norm, arm64_norm]) (by simp only [hsm2, wp_norm, arm64_norm])
          (by simp only [hsm2, wp_norm, arm64_norm]) (by simp only [hsm2, wp_norm, arm64_norm])
        have h4d0 :
            ((fsp + 0x4d0#64) ↦₆₄ 0xfffffffffffffffe#64) ∗
              ((fsp + 0x4d8#64) ↦₆₄ (spkPtr + 4#64)) ∗
              ((fsp + 0x4e0#64) ↦₆₄ BitVec.ofNat 64 spkKey.length) ∗
              (((fsp + 0x4e8#64) ↦₃₂ spkId) ∗ memRegion (fsp + 0x4ec#64) 4) ⊢
              memRegion (fsp + 0x4d0#64) 32 := by
          refine Entails.trans (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
            (sepConj_mono_left (pointsTo32_entails_memRegion _ _))))) ?_
          rw [r1b_join_region fsp 0x4e8 4 4]
          refine Entails.trans (sepConj_mono_right (sepConj_mono_right
            (by
              simpa only [BitVec.add_assoc, BitVec.reduceAdd] using
                r1b_cell64_cons (a := fsp + 0x4e0#64)
                  (BitVec.ofNat 64 spkKey.length) (n := 8) (by decide)))) ?_
          refine Entails.trans (sepConj_mono_right
            (by
              simpa only [BitVec.add_assoc, BitVec.reduceAdd] using
                r1b_cell64_cons (a := fsp + 0x4d8#64) (spkPtr + 4#64) (n := 16) (by decide))) ?_
          simpa only [BitVec.add_assoc, BitVec.reduceAdd] using
            r1b_cell64_cons (a := fsp + 0x4d0#64) 0xfffffffffffffffe#64 (n := 24) (by decide)
        have hcont := hk sm2 evsSp spkId spkKey spkSig hevsSp hok2 hsp_ok
          (hfs_sm2.trans (hfs_eq1.trans hfs_sm1))
          (by simp only [hsm2, wp_norm, arm64_norm])
          (by simp only [hsm2, wp_norm, arm64_norm])
          (by simp only [hsm2, wp_norm, arm64_norm])
          (by simpa only [hsm2, wp_norm, arm64_norm] using hx26_1)
          (by simpa only [hsm2, wp_norm, arm64_norm] using hx28_1)
        dsimp only [fsp] at h4d0 ⊢
        simp only [BitVec.add_assoc, BitVec.reduceAdd] at hcont h4d0 ⊢
        refine sepWPp_weaken_pre ?_ hcont
        exact r1b_entails_frame (by r1b_ac) h4d0 (by r1b_ac)
      )
  )

theorem r1b_after_spk_dealloc_placed_fds [LibsignalPlacement] {M : AllocCostModel}
    {S : RunSem} {A : RustCliAllocBudget M} {lim : BudgetLimits} {st : M.σ}
    {cEnvs : RunCalleesEnvs} {EnvAt : StoresGhost → RejectKind → M.σ → Prop}
    {H : LibsignalHooks} {B : RunBudgets} {σ : RunSlots}
    {g : RunCall} {d : Init1Data} {s0 s : State} {resStack : Nat}
    {r0 r1 r2 r3 : BitVec 8}
    {regCap regPtr spkCap spkPtr : BitVec 64} {spkBs : List (BitVec 8)}
    {Q Qp : State → SepProp → Prop} {oom : State → SepProp}
    (hh : RunHooksPlaced A lim H)
    (hc : RunCalleesPlacedFd A lim cEnvs H B σ)
    (hdrop : DropSpeOwnedOkAtBlock (runProgPlaced H) A lim)
    (hbnd : r1b_StackBounds B resStack)
    (hok : r1b_OkCtxPlaced r1b_CodeOk S g d s0 s 0x1230)
    (hfds : FdsGe3Closed s.fs)
    (hreg_rd :
      cliIo.rd (runFiles g.i) (d.dir ++ [0x2f#8] ++ utf8 "registration-id") = .ok [r0, r1, r2, r3])
    (hspk_rd : cliIo.rd (runFiles g.i) (d.dir ++ [0x2f#8] ++ utf8 "signed-pre-key") = .ok spkBs)
    (hx23 : s.readReg64 (.gpr 23#5) = spkCap)
    (hx9 : s.readReg64 (.gpr 9#5) = spkPtr)
    (hx2 : s.readReg64 .x2 = BitVec.ofNat 64 spkBs.length)
    (hx26 : s.readReg64 (.gpr 26#5) = d.dirPtr)
    (hx28 : s.readReg64 (.gpr 28#5) = BitVec.ofNat 64 d.dir.length)
    (hfit_sp : FitsEnv M lim st (cEnvs.splitSigned spkBs))
    (henv_sp_err : ∀ evsSp evsFree2,
      splitSigned spkBs = none →
      cEnvs.splitSigned spkBs evsSp →
      FreeOnlyEvs evsFree2 →
      EnvAt StoresGhost.opened .postDispatch (M.stepEvents (evsSp ++ evsFree2) st))
    (hpanic : PanicK g s0 Qp)
    (hrej : RejectKPlacedEnv r1b_CodeOk H A lim EnvAt g s0 resStack Q Qp oom)
    (hk : ∀ (sf : State) (evsSp : List AllocEvent)
        (spkId : BitVec 32) (spkKey spkSig : List (BitVec 8)),
      cEnvs.splitSigned spkBs evsSp →
      r1b_OkCtxPlaced r1b_CodeOk S g d s0 sf 0x1260 →
      FdsGe3Closed sf.fs →
      splitSigned spkBs = some (spkId, spkKey, spkSig) →
      sf.readReg64 (.gpr 10#5) = spkPtr + 4#64 →
      sf.readReg64 (.gpr 27#5) = BitVec.ofNat 64 spkKey.length →
      sf.readReg64 .x2 = spkId.zeroExtend 64 →
      sf.readReg64 (.gpr 26#5) = d.dirPtr →
      sf.readReg64 (.gpr 28#5) = BitVec.ofNat 64 d.dir.length →
      let fsp := runFsp s0
      SepWPp (runProgPlaced H) (s0.readReg64 .lr) sf
        (((fsp + 0x4f0#64) ↦₆₄ (spkPtr + 4#64 + BitVec.ofNat 64 spkKey.length)) ∗
          ((fsp + 0x4f8#64) ↦₆₄ 64#64) ∗ memRegion (fsp + 0x4d0#64) 32 ∗
          ownedBytes A.repAlloc spkCap spkPtr (BitVec.ofNat 64 spkBs.length) spkBs ∗
          ownedBytes A.repAlloc regCap regPtr 4#64 [r0, r1, r2, r3] ∗
          r1b_invCore_placed A.repAlloc g d s0 ∗ (lsLogFilterAddr ↦₆₄ 0#64) ∗
          ownedBytes A.repAlloc d.dirCap d.dirPtr (BitVec.ofNat 64 d.dir.length) d.dir ∗
          memRegion fsp 0x110 ∗ memRegion (fsp + 0x110#64) 8 ∗ memRegion (fsp + 0x11c#64) 4 ∗
          memRegion (fsp + 0x120#64) 16 ∗ memRegion (fsp + 0x130#64) 0x20 ∗
          memRegion (fsp + 0x150#64) 16 ∗ ((fsp + 0x164#64) ↦₃₂ ofLe32 r0 r1 r2 r3) ∗
          ((fsp + 0x168#64) ↦₆₄ spkPtr) ∗ ((fsp + 0x170#64) ↦₆₄ spkCap) ∗
          memRegion (fsp + 0x178#64) 8 ∗ memRegion (fsp + 0x188#64) 8 ∗
          ((fsp + 0x190#64) ↦₆₄ d.ikW3) ∗ ((fsp + 0x198#64) ↦₆₄ regCap) ∗
          ((fsp + 0x1a0#64) ↦₆₄ regPtr) ∗ ((fsp + 0x1a8#64) ↦₆₄ d.ikW1) ∗
          ((fsp + 0x1b0#64) ↦₃₂ d.peerV.device.zeroExtend 32) ∗
          memRegion (fsp + 0x1b4#64) 4 ∗ memRegion (fsp + 0x1750#64) 24 ∗
          stackAt fsp (resStack - runFrame) ∗
          A.pool lim (M.stepEvents evsSp st) sf)
        Q Qp oom) :
    let fsp := runFsp s0
    SepWPp (runProgPlaced H) (s0.readReg64 .lr) s
      (memRegion (fsp + 0x4d0#64) 48 ∗
        ownedBytes A.repAlloc spkCap spkPtr (BitVec.ofNat 64 spkBs.length) spkBs ∗
        ownedBytes A.repAlloc regCap regPtr 4#64 [r0, r1, r2, r3] ∗
        r1b_invCore_placed A.repAlloc g d s0 ∗ (lsLogFilterAddr ↦₆₄ 0#64) ∗
        ownedBytes A.repAlloc d.dirCap d.dirPtr (BitVec.ofNat 64 d.dir.length) d.dir ∗
        memRegion fsp 0x110 ∗ memRegion (fsp + 0x110#64) 8 ∗ memRegion (fsp + 0x11c#64) 4 ∗
        memRegion (fsp + 0x120#64) 16 ∗ memRegion (fsp + 0x130#64) 0x20 ∗
        memRegion (fsp + 0x150#64) 16 ∗ ((fsp + 0x164#64) ↦₃₂ ofLe32 r0 r1 r2 r3) ∗
        memRegion (fsp + 0x168#64) 8 ∗ ((fsp + 0x170#64) ↦₆₄ spkCap) ∗
        memRegion (fsp + 0x178#64) 8 ∗ memRegion (fsp + 0x188#64) 8 ∗
        ((fsp + 0x190#64) ↦₆₄ d.ikW3) ∗ ((fsp + 0x198#64) ↦₆₄ regCap) ∗
        ((fsp + 0x1a0#64) ↦₆₄ regPtr) ∗ ((fsp + 0x1a8#64) ↦₆₄ d.ikW1) ∗
        ((fsp + 0x1b0#64) ↦₃₂ d.peerV.device.zeroExtend 32) ∗
        memRegion (fsp + 0x1b4#64) 4 ∗ memRegion (fsp + 0x1750#64) 24 ∗
        stackAt fsp (resStack - runFrame) ∗ A.pool lim st s)
      Q Qp oom :=
  r1b_after_spk_dealloc_placed_fd hh hc hdrop hbnd hok hreg_rd hspk_rd hx23 hx9 hx2 hx26 hx28
    hfit_sp henv_sp_err hpanic hrej fun sf evsSp spkId spkKey spkSig hevs hok_f hsp_ok hfs_eq =>
      hk sf evsSp spkId spkKey spkSig hevs hok_f (hfs_eq ▸ hfds) hsp_ok

end LibsignalBinary.Proofs.SignalSession.Cli.Run.Compose.Arms.R1b.ReadRegSpkPlacedBudgetFd
