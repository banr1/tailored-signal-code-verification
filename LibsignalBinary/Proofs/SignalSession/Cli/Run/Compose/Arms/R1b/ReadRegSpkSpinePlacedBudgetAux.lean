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
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Compose.Arms.R1b.CallHelpersParsePlacedBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Compose.Arms.R1b.ErrCleanupSpkRegPlacedBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Compose.Arms.R1b.ReadRegSpkPlacedBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Compose.Arms.R1b.ReadRegSpkSpinePlaced
import Arm64.Trusted.Spec.Hoare
import Arm64.Trusted.Spec.SepLogic
import LibsignalBinary.Proofs.Common.SharedHelpers
meta import LibsignalBinary.Proofs.Common.SharedHelpers -- shake: keep
import LibsignalBinary.Proofs.SignalSession.Cli.Main.Proofs.M4Layout
import LibsignalBinary.Proofs.SignalSession.Cli.Main.Proofs.CallSites

/-!
# Budget-Threaded Stage 1 Spine Helpers (`0x0c6c → 0x11f4 → 0x1260`) of Arm `R1b`

Defines `r1bFreeCapEvs` and proves `r1b_spk_dealloc_11f4_placed` (`0x11f4 → 0x1260`) and
`r1b_after_reg_dealloc_placed` (`0x0c6c → 0x1260`) on Block `579` under `[LibsignalPlacement]` and
`RustCliAllocBudget M`.
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 200000
set_option linter.unusedSimpArgs false

namespace LibsignalBinary.Proofs.SignalSession.Cli.Run.Compose.Arms.R1b.ReadRegSpkSpinePlacedBudgetAux

open Arm64 Arm64.Process ProofLib ProofLib.ProgramReflection SepProp
open CryptoVerification
  (LibsignalHooks LibsignalPlacement lsLogFilterAddr lsmpl lsρ)
open CryptoVerification.LibsignalPublicApi.StoreKit (LibsignalCodeRoLoaded)
open CryptoVerification.SignalSession (lsReadFileSym lsRustDeallocSymCli)
open CryptoVerification.SignalSession.Cli (StoresGhost ofLe32 splitSigned utf8)
open CryptoVerification.SignalSession.Cli.MainHops
  (RunCall cliIo cliWrOk ownedBytes sepWPp_weaken_pre)
open CryptoVerification.SignalSession.Cli.Run.Placed
  (blkLib_eq_579 blkPC_579 blkPl_579 lsProg_579)
open CryptoVerification.SignalSession.Cli.RunCompose
  (AtRejectPlaced AtRunEntryPlaced Init1Data InRunPlaced PanicK RejectKind RunSem bundleNames
   r1b_CodeOk r1b_ErrCtxPlaced r1b_OkCtxPlaced r1b_StackBounds r1b_bind_state_placed
   r1b_cell64_cons r1b_cells3_to_region24 r1b_cmn1_false_of_lt63 r1b_entails_frame_core
   r1b_errCommon r1b_exists_4bytes r1b_fsp_align r1b_init_path_facts_placed
   r1b_invCore_placed r1b_invCore_to_errCommon_placed r1b_join_region r1b_none_reg_len
   r1b_none_spk_rd r1b_ofNat64_ne4 r1b_ownedBytes_facts r1b_ownedBytes_rejoin
   r1b_ownedBytes_zero r1b_pointsToBytes4_eq_u32 r1b_ro_spk_placed r1b_sepWPp_borrow_core
   r1b_sepWPp_frame_core r1b_sepWPp_pure_left r1b_split_region r1b_stage_to_err_placed
   rejectMem runFiles runFsp runPcPlaced runPcPlaced_eq runProgPlaced)
open CryptoVerification.SignalSession.Cli.RunSkeleton (RunBudgets RunSlots runFrame)
open LibsignalBinary.Heap
  (AllocCostModel AllocEvent BudgetLimits FitsEnv FitsEvents FreeOnlyEvs RustCliAllocBudget
   VmPreserved rustDeallocEvents)
open LibsignalBinary.Proofs.Placed.BudgetPoolSync (hooksException sepWP_seg_ls_vm)
open LibsignalBinary.Proofs.SignalSession.Cli.Dir.Path.PlacedBudget (PathEnv)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Compose.Arms.R1b.CallHelpersPlacedBudget
  (r1b_call_path_ro_placed r1b_call_readFile_placed)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Compose.Arms.R1b.CommonPlacedBudget
  (r1b_call_dealloc_ownedBytes_placed)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Compose.Arms.R1b.ErrCleanupPlacedBudget
  (sepWP_with_vm_oom)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Compose.Arms.R1b.ReadRegSpkPlacedBudget
  (r1b_after_spk_dealloc_placed r1b_err_0df0_placed r1b_err_11b4_placed)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Compose.Arms.R1b.ReadRegSpkPlacedBudgetAux
  (blk579_noSvc0)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Compose.HopsPlacedBudget (RejectKPlacedEnv)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DropSpeOwnedPlacedBudget
  (DropSpeOwnedOkAtBlock)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.SkeletonPlacedBudget
  (RunCalleesEnvs RunCalleesPlaced RunHooksPlaced)

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

theorem r1b_seq_lscro_oom [LibsignalPlacement] {prog : Program} {ret mid : BitVec 64}
    {s : State} {P : SepProp} {Q Qp : State → SepProp → Prop} {oom : State → SepProp}
    (hcrl : LibsignalCodeRoLoaded lsmpl s.mem)
    (h : SepWP prog mid s P (fun sm Pm =>
      LibsignalCodeRoLoaded lsmpl sm.mem → SepWPp prog ret sm Pm Q Qp oom) oom) :
    SepWPp prog ret s P Q Qp oom :=
  SepWPp.seq_frozen (fun _ _ h0 hkf => h0.of_keepsFrozen hkf) hcrl h

/-- Conditional `Vec<u8>` path-buffer drop events: `[]` when `cap = 0`, and `rustDeallocEvents cap.toNat 1` otherwise. -/
def r1bFreeCapEvs (cap : BitVec 64) : List AllocEvent :=
  if cap = 0#64 then [] else rustDeallocEvents cap.toNat 1

@[simp]
theorem r1bFreeCapEvs_zero : r1bFreeCapEvs 0#64 = [] := rfl

theorem r1bFreeCapEvs_of_ne {cap : BitVec 64} (h : cap ≠ 0#64) :
    r1bFreeCapEvs cap = rustDeallocEvents cap.toNat 1 := by
  simp only [r1bFreeCapEvs, h, ↓reduceIte]

theorem freeOnlyEvs_r1bFreeCapEvs (cap : BitVec 64) : FreeOnlyEvs (r1bFreeCapEvs cap) := by
  unfold r1bFreeCapEvs
  split
  · intro ev hev; nomatch hev
  · intro ev hev
    simp only [rustDeallocEvents, List.mem_singleton] at hev
    exact ⟨_, _, hev⟩

theorem freeOnlyEvs_append {xs ys : List AllocEvent}
    (hx : FreeOnlyEvs xs) (hy : FreeOnlyEvs ys) :
    FreeOnlyEvs (xs ++ ys) := by
  intro ev hev
  rcases List.mem_append.mp hev with h1 | h2
  · exact hx ev h1
  · exact hy ev h2

local macro (priority := high) "r1b_ac" : tactic =>
  `(tactic| ((try dsimp +zetaDelta only) <;> first | rfl | simp only [emp_sepConj] | sep_ac_rfl))

private meta def r1bStripLetsSP : Nat → Lean.Expr → Lean.Expr
  | 0, e => e
  | n + 1, .letE _ _ v b _ => r1bStripLetsSP n (b.instantiate1 v)
  | n + 1, .mdata _ e => r1bStripLetsSP n e
  | _, e => e

private meta def r1bSplitSepSP : Nat → Lean.Expr → Lean.Expr → Array Lean.Expr
  | 0, _, e => #[e]
  | fuel + 1, sepSample, e =>
    let e := r1bStripLetsSP 64 e
    let fn := sepSample.getAppFn.constName!
    let ar := sepSample.getAppNumArgs
    if e.isAppOfArity fn ar then
      r1bSplitSepSP fuel sepSample (e.getArg! (ar - 2)) ++
        r1bSplitSepSP fuel sepSample (e.getArg! (ar - 1))
    else #[e]

private meta def r1bIsDefEqPureSP (x a : Lean.Expr) : Lean.Elab.TermElabM Bool := do
  let x := r1bStripLetsSP 64 x; let a := r1bStripLetsSP 64 a
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

private meta def r1bComputeRestSP (ctxName : String) (p a1 : Lean.Expr) : Lean.Elab.TermElabM Lean.Expr := do
  let sepTy := Lean.mkConst ``SepProp []
  let sepSample ← Lean.Elab.Term.elabTerm (← `(emp ∗ emp)) (some sepTy)
  let empExpr ← Lean.Elab.Term.elabTerm (← `(emp)) (some sepTy)
  let ps := (r1bSplitSepSP 64 sepSample (← Lean.instantiateMVars p)).toList
  let a1s := (r1bSplitSepSP 64 sepSample (← Lean.instantiateMVars a1)).toList
  let mut rem := ps
  for a in a1s do
    let mut removed := false
    let mut next : List Lean.Expr := []
    for x in rem do
      if !removed && (← r1bIsDefEqPureSP x a) then removed := true
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

local elab (priority := high) "r1b_entails_frame " t1:term:arg h:term:arg t2:term:arg : term <= expectedType => do
  let exp ← Lean.instantiateMVars expectedType
  if exp.isMVar then Lean.Elab.Term.tryPostpone
  let entSample ← Lean.Elab.Term.elabTerm (← `(emp ⊢ emp)) none
  let ear := entSample.getAppNumArgs
  let expS := r1bStripLetsSP 64 exp
  let p := expS.getArg! (ear - 2)
  let q := expS.getArg! (ear - 1)
  if (← Lean.instantiateMVars p).isMVar then Lean.Elab.Term.tryPostpone
  if (← Lean.instantiateMVars q).isMVar then Lean.Elab.Term.tryPostpone
  let hExpr ← Lean.Elab.Term.elabTerm h none
  let hTy := r1bStripLetsSP 64 (← Lean.instantiateMVars (← Lean.Meta.inferType hExpr))
  let a1 := hTy.getArg! (ear - 2)
  let a2 := hTy.getArg! (ear - 1)
  let r ← r1bComputeRestSP "r1b_entails_frame" p a1
  let sepTy := Lean.mkConst ``SepProp []
  let empExpr ← Lean.Elab.Term.elabTerm (← `(emp)) (some sepTy)
  let sepSample ← Lean.Elab.Term.elabTerm (← `(emp ∗ emp)) (some sepTy)
  let sar := sepSample.getAppNumArgs
  let mkSep (x y : Lean.Expr) : Lean.Expr :=
    sepSample.withApp fun f args => Lean.mkAppN f (args.extract 0 (sar - 2) ++ #[x, y])
  let rIsEmp ← r1bIsDefEqPureSP r empExpr
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
    Lean.Meta.mkAppOptM ``r1b_entails_frame_core #[some a1, some a2, some r, some p, some q, h1Expr, hExpr, h2Expr]

local elab (priority := high) "r1b_sepWPp_frame " t1:term:arg h:term:arg t2:term:arg hk:term:arg : term <= expectedType => do
  let exp ← Lean.instantiateMVars expectedType
  if exp.isMVar then Lean.Elab.Term.tryPostpone
  let expS := r1bStripLetsSP 64 exp
  let args := expS.getAppArgs
  let prog := args[0]!; let ret := args[1]!; let st := args[2]!; let p := args[3]!
  let q := args[4]!; let qp := args[5]!; let oom := args[6]!
  let entSample ← Lean.Elab.Term.elabTerm (← `(emp ⊢ emp)) none
  let ear := entSample.getAppNumArgs
  let hExpr ← Lean.Elab.Term.elabTerm h none
  let hTy := r1bStripLetsSP 64 (← Lean.instantiateMVars (← Lean.Meta.inferType hExpr))
  let a1 := hTy.getArg! (ear - 2)
  let a2 := hTy.getArg! (ear - 1)
  let r ← r1bComputeRestSP "r1b_sepWPp_frame" p a1
  let sepTy := Lean.mkConst ``SepProp []
  let empExpr ← Lean.Elab.Term.elabTerm (← `(emp)) (some sepTy)
  let sepSample ← Lean.Elab.Term.elabTerm (← `(emp ∗ emp)) (some sepTy)
  let sar := sepSample.getAppNumArgs
  let mkSep (x y : Lean.Expr) : Lean.Expr :=
    sepSample.withApp fun f args => Lean.mkAppN f (args.extract 0 (sar - 2) ++ #[x, y])
  let rIsEmp ← r1bIsDefEqPureSP r empExpr
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
    let a2IsEmp ← r1bIsDefEqPureSP a2 empExpr
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
  let expS := r1bStripLetsSP 64 exp
  let hExpr ← Lean.Elab.Term.elabTerm h none
  let hTy0 := r1bStripLetsSP 64 (← Lean.instantiateMVars (← Lean.Meta.inferType hExpr))
  for idx in [0, 1, 2, 4, 5, 6] do
    if !(← Lean.Meta.withReducibleAndInstances <| Lean.Meta.isDefEq (hTy0.getArg! idx) (expS.getArg! idx)) then
      discard <| Lean.Meta.isDefEq (hTy0.getArg! idx) (expS.getArg! idx)
  let p ← Lean.instantiateMVars (expS.getArg! 3)
  let p' ← Lean.instantiateMVars ((r1bStripLetsSP 64 (← Lean.instantiateMVars hTy0)).getArg! 3)
  let sepTy := Lean.mkConst ``SepProp []
  let sepSample ← Lean.Elab.Term.elabTerm (← `(emp ∗ emp)) (some sepTy)
  let empExpr ← Lean.Elab.Term.elabTerm (← `(emp)) (some sepTy)
  let sar := sepSample.getAppNumArgs
  let mkSep (x y : Lean.Expr) : Lean.Expr :=
    sepSample.withApp fun f args => Lean.mkAppN f (args.extract 0 (sar - 2) ++ #[x, y])
  let ps := (r1bSplitSepSP 64 sepSample p).toList
  let p's := (r1bSplitSepSP 64 sepSample p').toList
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
      if !removed && (← r1bIsDefEqPureSP x a) then removed := true
      else next := next.concat x
    if !removed then
      throwError "r1b_call_frame: unmatched callee atom:\n  {a}\nin:\n  {rem}"
    rem := next
  let remProd := match rem.reverse with
    | [] => empExpr
    | last :: rest => rest.foldl (fun acc x => mkSep x acc) last
  if let some mf := mvarFOpt then
    discard <| Lean.Meta.withReducibleAndInstances <| Lean.Meta.isDefEq mf remProd
  let eqTy ← Lean.Meta.mkEq (← Lean.instantiateMVars p) (← Lean.instantiateMVars p')
  let eqProof ← Lean.Elab.Term.elabTerm (← `(by r1b_ac)) (some eqTy)
  let ent ← Lean.Meta.mkAppM ``Entails.of_eq #[eqProof]
  Lean.Meta.mkAppM ``sepWPp_weaken_pre #[ent, hExpr]

set_option maxHeartbeats 800000 in
theorem r1b_spk_dealloc_11f4_placed [LibsignalPlacement] {M : AllocCostModel}
    {S : RunSem} {A : RustCliAllocBudget M} {lim : BudgetLimits} {st : M.σ}
    {cEnvs : RunCalleesEnvs} {EnvAt : StoresGhost → RejectKind → M.σ → Prop}
    {H : LibsignalHooks} {B : RunBudgets} {σ : RunSlots}
    {g : RunCall} {d : Init1Data} {s0 s : State} {resStack : Nat}
    {r0 r1 r2 r3 : BitVec 8}
    {pCap pPtr regCap regPtr spkCap spkPtr : BitVec 64}
    {pBs spkBs : List (BitVec 8)}
    {Q Qp : State → SepProp → Prop} {oom : State → SepProp}
    (hh : RunHooksPlaced A lim H) (hc : RunCalleesPlaced A lim cEnvs H B σ)
    (hdrop : DropSpeOwnedOkAtBlock (runProgPlaced H) A lim)
    (hbnd : r1b_StackBounds B resStack)
    (hok : r1b_OkCtxPlaced r1b_CodeOk S g d s0 s 0x11f4)
    (hreg_rd : cliIo.rd (runFiles g.i) (d.dir ++ [0x2f#8] ++ utf8 "registration-id") =
      .ok [r0, r1, r2, r3])
    (hspk_rd : cliIo.rd (runFiles g.i) (d.dir ++ [0x2f#8] ++ utf8 "signed-pre-key") = .ok spkBs)
    (hx27 : s.readReg64 (.gpr 27#5) = pPtr)
    (hx23 : s.readReg64 (.gpr 23#5) = spkCap)
    (hx9 : s.readReg64 (.gpr 9#5) = spkPtr)
    (hx2 : s.readReg64 .x2 = BitVec.ofNat 64 spkBs.length)
    (hx12 : s.readReg64 (.gpr 12#5) = 0xfffffffffffffffe#64)
    (hx26 : s.readReg64 (.gpr 26#5) = d.dirPtr)
    (hx28 : s.readReg64 (.gpr 28#5) = BitVec.ofNat 64 d.dir.length)
    (hfit_sp : ∀ evsFree, FreeOnlyEvs evsFree →
      FitsEnv M lim (M.stepEvents evsFree st) (cEnvs.splitSigned spkBs))
    (henv_sp_err : ∀ evsFree1 evsSp evsFree2,
      FreeOnlyEvs evsFree1 →
      splitSigned spkBs = none →
      cEnvs.splitSigned spkBs evsSp →
      FreeOnlyEvs evsFree2 →
      EnvAt StoresGhost.opened .postDispatch
        (M.stepEvents (evsFree1 ++ evsSp ++ evsFree2) st))
    (hpanic : PanicK g s0 Qp)
    (hrej : RejectKPlacedEnv r1b_CodeOk H A lim EnvAt g s0 resStack Q Qp oom)
    (hk : ∀ (sf : State) (evsFree evsSp : List AllocEvent)
        (spkId : BitVec 32) (spkKey spkSig : List (BitVec 8)),
      FreeOnlyEvs evsFree →
      cEnvs.splitSigned spkBs evsSp →
      r1b_OkCtxPlaced r1b_CodeOk S g d s0 sf 0x1260 →
      splitSigned spkBs = some (spkId, spkKey, spkSig) →
      sf.readReg64 (.gpr 10#5) = spkPtr + 4#64 →
      sf.readReg64 (.gpr 27#5) = BitVec.ofNat 64 spkKey.length →
      sf.readReg64 .x2 = spkId.zeroExtend 64 →
      sf.readReg64 (.gpr 26#5) = d.dirPtr →
      sf.readReg64 (.gpr 28#5) = BitVec.ofNat 64 d.dir.length →
      let fsp := runFsp s0
      SepWPp (runProgPlaced H) (s0.readReg64 .lr) sf
        (((fsp + 0x4f0#64) ↦₆₄ (spkPtr + 4#64 + BitVec.ofNat 64 spkKey.length)) ∗
          ((fsp + 0x4f8#64) ↦₆₄ 64#64) ∗
          memRegion (fsp + 0x4d0#64) 32 ∗
          ownedBytes A.repAlloc spkCap spkPtr (BitVec.ofNat 64 spkBs.length) spkBs ∗
          ownedBytes A.repAlloc regCap regPtr 4#64 [r0, r1, r2, r3] ∗
          r1b_invCore_placed A.repAlloc g d s0 ∗ (lsLogFilterAddr ↦₆₄ 0#64) ∗
          ownedBytes A.repAlloc d.dirCap d.dirPtr (BitVec.ofNat 64 d.dir.length) d.dir ∗
          memRegion fsp 0x110 ∗
          memRegion (fsp + 0x110#64) 8 ∗ memRegion (fsp + 0x11c#64) 4 ∗
          memRegion (fsp + 0x120#64) 16 ∗ memRegion (fsp + 0x130#64) 0x20 ∗
          memRegion (fsp + 0x150#64) 16 ∗
          ((fsp + 0x164#64) ↦₃₂ ofLe32 r0 r1 r2 r3) ∗
          ((fsp + 0x168#64) ↦₆₄ spkPtr) ∗ ((fsp + 0x170#64) ↦₆₄ spkCap) ∗
          memRegion (fsp + 0x178#64) 8 ∗
          memRegion (fsp + 0x188#64) 8 ∗ ((fsp + 0x190#64) ↦₆₄ d.ikW3) ∗
          ((fsp + 0x198#64) ↦₆₄ regCap) ∗ ((fsp + 0x1a0#64) ↦₆₄ regPtr) ∗
          ((fsp + 0x1a8#64) ↦₆₄ d.ikW1) ∗
          ((fsp + 0x1b0#64) ↦₃₂ d.peerV.device.zeroExtend 32) ∗
          memRegion (fsp + 0x1b4#64) 4 ∗ memRegion (fsp + 0x1750#64) 24 ∗
          stackAt fsp (resStack - runFrame) ∗
          A.pool lim (M.stepEvents (evsFree ++ evsSp) st) sf)
        Q Qp oom) :
    let fsp := runFsp s0
    SepWPp (runProgPlaced H) (s0.readReg64 .lr) s
      (((fsp + 0x4d0#64) ↦₆₄ pCap) ∗ memRegion (fsp + 0x4d8#64) 40 ∗
        ownedBytes A.repAlloc pCap pPtr (BitVec.ofNat 64 pBs.length) pBs ∗
        ownedBytes A.repAlloc spkCap spkPtr (BitVec.ofNat 64 spkBs.length) spkBs ∗
        ownedBytes A.repAlloc regCap regPtr 4#64 [r0, r1, r2, r3] ∗
        r1b_invCore_placed A.repAlloc g d s0 ∗ (lsLogFilterAddr ↦₆₄ 0#64) ∗
        ownedBytes A.repAlloc d.dirCap d.dirPtr (BitVec.ofNat 64 d.dir.length) d.dir ∗
        memRegion fsp 0x110 ∗
        memRegion (fsp + 0x110#64) 8 ∗ memRegion (fsp + 0x11c#64) 4 ∗
        memRegion (fsp + 0x120#64) 16 ∗ memRegion (fsp + 0x130#64) 0x20 ∗
        memRegion (fsp + 0x150#64) 16 ∗
        ((fsp + 0x164#64) ↦₃₂ ofLe32 r0 r1 r2 r3) ∗
        memRegion (fsp + 0x168#64) 8 ∗ ((fsp + 0x170#64) ↦₆₄ spkCap) ∗
        memRegion (fsp + 0x178#64) 8 ∗
        memRegion (fsp + 0x188#64) 8 ∗ ((fsp + 0x190#64) ↦₆₄ d.ikW3) ∗
        ((fsp + 0x198#64) ↦₆₄ regCap) ∗ ((fsp + 0x1a0#64) ↦₆₄ regPtr) ∗
        ((fsp + 0x1a8#64) ↦₆₄ d.ikW1) ∗
        ((fsp + 0x1b0#64) ↦₃₂ d.peerV.device.zeroExtend 32) ∗
        memRegion (fsp + 0x1b4#64) 4 ∗ memRegion (fsp + 0x1750#64) 24 ∗
        stackAt fsp (resStack - runFrame) ∗ A.pool lim st s)
      Q Qp oom := by
  intro fsp
  let _ := hx27; let _ := hx23; let _ := hx9; let _ := hx2; let _ := hx12; let _ := hx26; let _ := hx28
  generalize hinvCore : r1b_invCore_placed A.repAlloc g d s0 = invCore
  have hst := hok.st
  have hal : fsp &&& 15#64 = 0#64 := r1b_fsp_align hst.sp hst.spAligned
  have hpc_in := hst.pc; change s.pc = (blkPl_579).base + 0x11f4#64 at hpc_in
  by_cases hpCap : pCap = 0#64
  · subst hpCap
    have hfo0 : FreeOnlyEvs ([] : List AllocEvent) := fun _ h => nomatch h
    have hpc := hpc_in; have hrun := hst.run; have hsp : s.sp = fsp := hst.sp
    apply r1b_seq_lscro_oom (mid := (blkPl_579).base + 0x1230#64) hst.inv
    dsimp only [runProgPlaced, lsProg_579]
    by_vm_open (
      wp_steps
      refine SepWP.done (by simp only [wp_norm, arm64_norm, *]; try bv_omega)
        (by simp only [wp_norm, arm64_norm, *])
        ⟨by simp only [wp_norm, arm64_norm, *], fun hvm => ?_⟩
      refine r1b_bind_state_placed fun sm1 hsm1 hinv1 => ?_
      rw [← hsm1] at hvm
      rw [← A.pool_transport lim st s sm1 hvm]
      change SepWPp (runProgPlaced H) _ _ _ _ _ _
      have hok1 : r1b_OkCtxPlaced r1b_CodeOk S g d s0 sm1 0x1230 := hok.of_step
        { pc := by simp only [hsm1, wp_norm, arm64_norm]
          run := by simp only [hsm1, wp_norm, arm64_norm, hst.run]
          sp := by simpa only [hsm1, wp_norm, arm64_norm] using hst.sp
          fp := by simpa only [hsm1, wp_norm, arm64_norm] using hst.fp
          inv := hinv1
          vregs := by simpa only [calleeSavedVRegs, hsm1, wp_norm, arm64_norm] using hst.vregs
          spAligned := hst.spAligned }
        (by simp only [hsm1, wp_norm, arm64_norm]) (by simp only [hsm1, wp_norm, arm64_norm])
        (by simp only [hsm1, wp_norm, arm64_norm]) (by simp only [hsm1, wp_norm, arm64_norm])
        (by simp only [hsm1, wp_norm, arm64_norm]) (by simp only [hsm1, wp_norm, arm64_norm])
      have h4d0 : ((fsp + 0x4d0#64) ↦₆₄ 0#64) ∗ memRegion (fsp + 0x4d8#64) 40 ⊢
          memRegion (fsp + 0x4d0#64) 48 := by
        simpa only [BitVec.add_assoc, BitVec.reduceAdd] using
          r1b_cell64_cons (a := fsp + 0x4d0#64) 0#64 (n := 40) (by decide)
      have h0own : ownedBytes A.repAlloc 0#64 pPtr (BitVec.ofNat 64 pBs.length) pBs ⊢ emp :=
        r1b_ownedBytes_zero A.repAlloc pPtr _ pBs
      refine r1b_sepWPp_frame (by r1b_ac) h0own (by simp only [emp_sepConj]) ?_
      refine sepWPp_weaken_pre ?_
        (r1b_after_spk_dealloc_placed (st := st) hh hc hdrop hbnd hok1 hreg_rd hspk_rd
          (by simp only [hsm1, wp_norm, arm64_norm]; try exact hx23)
          (by simp only [hsm1, wp_norm, arm64_norm]; try exact hx9)
          (by simp only [hsm1, wp_norm, arm64_norm]; try exact hx2)
          (by simp only [hsm1, wp_norm, arm64_norm]; try exact hx26)
          (by simp only [hsm1, wp_norm, arm64_norm]; try exact hx28)
          (by simpa only [M.stepEvents_nil] using hfit_sp [] hfo0)
          (fun evsSp evsFree2 hnone hsp_ev hfo2 => by
            simpa only [List.nil_append, M.stepEvents_append] using
              henv_sp_err [] evsSp evsFree2 hfo0 hnone hsp_ev hfo2)
          hpanic hrej
          (fun sf evsSp spkId spkKey spkSig hsp_ev hok_f hsp_ok hx10_f hx27_f hx2_f hx26_f hx28_f => by
            simpa only [List.nil_append] using
              hk sf [] evsSp spkId spkKey spkSig hfo0 hsp_ev hok_f hsp_ok
                hx10_f hx27_f hx2_f hx26_f hx28_f))
      try dsimp only
      rw [hinvCore]
      exact r1b_entails_frame (by r1b_ac) h4d0 (by r1b_ac)
    )
  · have hpCap_f : (pCap == 0#64) = false := beq_false_of_ne hpCap
    let _ := hpCap_f
    have hfo_p : FreeOnlyEvs (rustDeallocEvents pCap.toNat 1) := by
      simpa only [r1bFreeCapEvs_of_ne hpCap] using freeOnlyEvs_r1bFreeCapEvs pCap
    rw [ProofLib.memRegion_eight (fsp + 0x188#64)]
    simp only [sepExists_sepConj_left, sepExists_sepConj_right]
    refine SepWPp.exists_elim fun _v188 => ?_
    have hpc := hpc_in; have hrun := hst.run; have hsp : s.sp = fsp := hst.sp
    apply r1b_seq_lscro_oom (mid := lsρ lsRustDeallocSymCli) hst.inv
    dsimp only [runProgPlaced, lsProg_579]
    by_vm_open (
      wp_steps
      refine SepWP.done (by simp only [wp_norm, arm64_norm, *]; try bv_omega)
        (by simp only [wp_norm, arm64_norm, *])
        ⟨by simp only [wp_norm, arm64_norm, *], fun hvm1 => ?_⟩
      refine r1b_bind_state_placed fun sm1 hsm1 hinv1 => ?_
      rw [← hsm1] at hvm1
      rw [← A.pool_transport lim st s sm1 hvm1]
      change SepWPp (runProgPlaced H) _ _ _ _ _ _
      refine r1b_call_frame <|
        r1b_call_dealloc_ownedBytes_placed (ptr := pPtr) (cap := pCap) (bs := pBs) hh hbnd hinv1
          (by simp only [hsm1, wp_norm, arm64_norm])
          (by simp only [hsm1, wp_norm, arm64_norm, hst.run])
          (by simpa only [hsm1, wp_norm, arm64_norm] using hst.sp)
          (by simpa only [hsm1, wp_norm, arm64_norm] using hst.fp)
          (by simpa only [calleeSavedVRegs, hsm1, wp_norm, arm64_norm] using hst.vregs)
          hst.spAligned (retOff := 0x121c)
          (by simp only [hsm1, wp_norm, arm64_norm])
          (by simp only [hsm1, wp_norm, arm64_norm]; try exact hx27)
          (by simp only [hsm1, wp_norm, arm64_norm]) (by simp only [hsm1, wp_norm, arm64_norm])
          hpCap hpanic
          fun sf1 hin1 hcs1 hfs1 htr1 => ?_
      have hok1 : r1b_OkCtxPlaced r1b_CodeOk S g d s0 sf1 0x121c := hok.after_call
        (by simp only [hsm1, wp_norm, arm64_norm]) (by simp only [hsm1, wp_norm, arm64_norm])
        (by simp only [hsm1, wp_norm, arm64_norm]) (by simp only [hsm1, wp_norm, arm64_norm])
        (by simp only [hsm1, wp_norm, arm64_norm]) (by simp only [hsm1, wp_norm, arm64_norm])
        hin1 hcs1 (congrArg FsState.files hfs1) htr1
      have hx23_1 : sf1.readReg64 (.gpr 23#5) = BitVec.ofNat 64 spkBs.length :=
        hcs1.2.2.2.2.1.trans (by simp only [hsm1, wp_norm, arm64_norm]; try exact hx2)
      have hx25_1 : sf1.readReg64 (.gpr 25#5) = d.dirPtr :=
        hcs1.2.2.2.2.2.2.1.trans (by simp only [hsm1, wp_norm, arm64_norm]; try exact hx26)
      have hx26_1 : sf1.readReg64 (.gpr 26#5) = 0xfffffffffffffffe#64 :=
        hcs1.2.2.2.2.2.2.2.1.trans (by simp only [hsm1, wp_norm, arm64_norm]; try exact hx12)
      have hx27_1 : sf1.readReg64 (.gpr 27#5) = spkPtr :=
        hcs1.2.2.2.2.2.2.2.2.1.trans (by simp only [hsm1, wp_norm, arm64_norm]; try exact hx9)
      have hx28_1 : sf1.readReg64 (.gpr 28#5) = BitVec.ofNat 64 d.dir.length :=
        hcs1.2.2.2.2.2.2.2.2.2.1.trans (by simp only [hsm1, wp_norm, arm64_norm]; try exact hx28)
      let _ := hx23_1; let _ := hx25_1; let _ := hx26_1; let _ := hx27_1; let _ := hx28_1
      have hv188 : ((fsp + 0x188#64) ↦₆₄ s.readReg64 (.gpr 23#5)) = ((fsp + 0x188#64) ↦₆₄ spkCap) :=
        congrArg ((fsp + 0x188#64) ↦₆₄ ·) hx23
      try rw [hv188]
      have hpc1 := hin1.pc; change sf1.pc = (blkPl_579).base + 0x121c#64 at hpc1
      have hpc := hpc1; have hrun := hin1.run; have hsp : sf1.sp = fsp := hin1.sp
      apply r1b_seq_lscro_oom (mid := (blkPl_579).base + 0x1230#64) hin1.inv
      dsimp only [runProgPlaced, lsProg_579]
      by_vm_open (
        wp_steps
        refine SepWP.done (by simp only [wp_norm, arm64_norm, *]; try bv_omega)
          (by simp only [wp_norm, arm64_norm, *])
          ⟨by simp only [wp_norm, arm64_norm, *], fun hvm2 => ?_⟩
        refine r1b_bind_state_placed fun sm2 hsm2 hinv2 => ?_
        rw [← hsm2] at hvm2
        rw [← A.pool_transport lim (M.stepEvents (rustDeallocEvents pCap.toNat 1) st) sf1 sm2 hvm2]
        change SepWPp (runProgPlaced H) _ _ _ _ _ _
        have hok2 : r1b_OkCtxPlaced r1b_CodeOk S g d s0 sm2 0x1230 := hok1.of_step
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
        have h4d0 : ((fsp + 0x4d0#64) ↦₆₄ pCap) ∗ memRegion (fsp + 0x4d8#64) 40 ⊢
            memRegion (fsp + 0x4d0#64) 48 := by
          simpa only [BitVec.add_assoc, BitVec.reduceAdd] using
            r1b_cell64_cons (a := fsp + 0x4d0#64) pCap (n := 40) (by decide)
        have h188 : ((fsp + 0x188#64) ↦₆₄ spkCap) ⊢ memRegion (fsp + 0x188#64) 8 :=
          pointsTo64_entails_memRegion _ _
        refine sepWPp_weaken_pre ?_
          (r1b_after_spk_dealloc_placed
            (st := M.stepEvents (rustDeallocEvents pCap.toNat 1) st)
            (r0 := r0) (r1 := r1) (r2 := r2) (r3 := r3)
            (regCap := regCap) (regPtr := regPtr)
            (spkCap := spkCap) (spkPtr := spkPtr) (spkBs := spkBs)
            hh hc hdrop hbnd hok2 hreg_rd hspk_rd
            (by simp only [hsm2, wp_norm, arm64_norm])
            (by simp only [hsm2, wp_norm, arm64_norm]; try exact hx27_1)
            (by simp only [hsm2, wp_norm, arm64_norm]; try exact hx23_1)
            (by simp only [hsm2, wp_norm, arm64_norm]; try exact hx25_1)
            (by simp only [hsm2, wp_norm, arm64_norm]; try exact hx28_1)
            (hfit_sp (rustDeallocEvents pCap.toNat 1) hfo_p)
            (fun evsSp evsFree2 hnone hsp_ev hfo2 => by
              simpa only [M.stepEvents_append, List.append_assoc] using
                henv_sp_err (rustDeallocEvents pCap.toNat 1) evsSp evsFree2 hfo_p hnone hsp_ev hfo2)
            hpanic hrej
            (fun sf evsSp spkId spkKey spkSig hsp_ev hok_f hsp_ok hx10_f hx27_f hx2_f hx26_f hx28_f => by
              simpa only [M.stepEvents_append] using
                hk sf (rustDeallocEvents pCap.toNat 1) evsSp spkId spkKey spkSig
                  hfo_p hsp_ev hok_f hsp_ok hx10_f hx27_f hx2_f hx26_f hx28_f))
        try dsimp only
        rw [hinvCore]
        exact r1b_entails_frame (by r1b_ac) (sepConj_mono h4d0 h188) (by r1b_ac)
      )
    )

set_option maxHeartbeats 1200000 in
theorem r1b_after_reg_dealloc_placed [LibsignalPlacement] {M : AllocCostModel}
    {S : RunSem} {A : RustCliAllocBudget M} {lim : BudgetLimits} {st : M.σ}
    {cEnvs : RunCalleesEnvs} {EnvAt : StoresGhost → RejectKind → M.σ → Prop}
    {H : LibsignalHooks} {B : RunBudgets} {σ : RunSlots}
    {g : RunCall} {d : Init1Data} {s0 s : State} {resStack : Nat}
    {regCap regPtr : BitVec 64} {regBs : List (BitVec 8)}
    {Q Qp : State → SepProp → Prop} {oom : State → SepProp}
    (hh : RunHooksPlaced A lim H)
    (hc : RunCalleesPlaced A lim cEnvs H B σ)
    (hdrop : DropSpeOwnedOkAtBlock (runProgPlaced H) A lim)
    (hbnd : r1b_StackBounds B resStack)
    (he : AtRunEntryPlaced r1b_CodeOk S g s0)
    (hok : r1b_OkCtxPlaced r1b_CodeOk S g d s0 s 0x0c6c)
    (hreg_rd : cliIo.rd (runFiles g.i) (d.dir ++ [0x2f#8] ++ utf8 "registration-id") = .ok regBs)
    (hx23 : s.readReg64 (.gpr 23#5) = regCap)
    (hx25 : s.readReg64 (.gpr 25#5) = BitVec.ofNat 64 regBs.length)
    (hx26 : s.readReg64 (.gpr 26#5) = d.dirPtr)
    (hx28 : s.readReg64 (.gpr 28#5) = BitVec.ofNat 64 d.dir.length)
    (hfit_bad_reg : regBs.length ≠ 4 → FitsEvents M lim st [AllocEvent.alloc 14])
    (henv_bad_reg : ∀ evsFree, regBs.length ≠ 4 → FreeOnlyEvs evsFree →
      EnvAt StoresGhost.opened .postDispatch
        (M.stepEvents ([AllocEvent.alloc 14] ++ evsFree) st))
    (hfit_spk_path : regBs.length = 4 →
      FitsEnv M lim st (PathEnv d.dir (utf8 "signed-pre-key")))
    (hfit_spk_rd : ∀ evsP, regBs.length = 4 →
      PathEnv d.dir (utf8 "signed-pre-key") evsP →
      FitsEnv M lim (M.stepEvents evsP st)
        (cEnvs.readFile (runFiles g.i) (d.dir ++ [0x2f#8] ++ utf8 "signed-pre-key")))
    (hfit_spk_rd_err : ∀ evsP evsRd, regBs.length = 4 →
      PathEnv d.dir (utf8 "signed-pre-key") evsP →
      cliIo.rd (runFiles g.i) (d.dir ++ [0x2f#8] ++ utf8 "signed-pre-key") = .error () →
      cEnvs.readFile (runFiles g.i) (d.dir ++ [0x2f#8] ++ utf8 "signed-pre-key") evsRd →
      FitsEvents M lim (M.stepEvents (evsP ++ evsRd) st) [AllocEvent.alloc 22])
    (henv_spk_rd_err : ∀ evsP evsRd evsFree, regBs.length = 4 →
      PathEnv d.dir (utf8 "signed-pre-key") evsP →
      cliIo.rd (runFiles g.i) (d.dir ++ [0x2f#8] ++ utf8 "signed-pre-key") = .error () →
      cEnvs.readFile (runFiles g.i) (d.dir ++ [0x2f#8] ++ utf8 "signed-pre-key") evsRd →
      FreeOnlyEvs evsFree →
      EnvAt StoresGhost.opened .postDispatch
        (M.stepEvents (evsP ++ evsRd ++ [AllocEvent.alloc 22] ++ evsFree) st))
    (hfit_spk_split : ∀ evsP evsRd evsFree spkBs, regBs.length = 4 →
      PathEnv d.dir (utf8 "signed-pre-key") evsP →
      cliIo.rd (runFiles g.i) (d.dir ++ [0x2f#8] ++ utf8 "signed-pre-key") = .ok spkBs →
      cEnvs.readFile (runFiles g.i) (d.dir ++ [0x2f#8] ++ utf8 "signed-pre-key") evsRd →
      FreeOnlyEvs evsFree →
      FitsEnv M lim (M.stepEvents (evsP ++ evsRd ++ evsFree) st) (cEnvs.splitSigned spkBs))
    (henv_spk_split_err : ∀ evsP evsRd evsFree1 spkBs evsSp evsFree2, regBs.length = 4 →
      PathEnv d.dir (utf8 "signed-pre-key") evsP →
      cliIo.rd (runFiles g.i) (d.dir ++ [0x2f#8] ++ utf8 "signed-pre-key") = .ok spkBs →
      cEnvs.readFile (runFiles g.i) (d.dir ++ [0x2f#8] ++ utf8 "signed-pre-key") evsRd →
      FreeOnlyEvs evsFree1 →
      splitSigned spkBs = none →
      cEnvs.splitSigned spkBs evsSp →
      FreeOnlyEvs evsFree2 →
      EnvAt StoresGhost.opened .postDispatch
        (M.stepEvents (evsP ++ evsRd ++ evsFree1 ++ evsSp ++ evsFree2) st))
    (hpanic : PanicK g s0 Qp)
    (hrej : RejectKPlacedEnv r1b_CodeOk H A lim EnvAt g s0 resStack Q Qp oom)
    (hk : ∀ (sf : State) (evsP evsRd evsFree evsSp : List AllocEvent)
        (r0 r1 r2 r3 : BitVec 8)
        (spkCap spkPtr : BitVec 64) (spkBs spkKey spkSig : List (BitVec 8)) (spkId : BitVec 32),
      PathEnv d.dir (utf8 "signed-pre-key") evsP →
      cEnvs.readFile (runFiles g.i) (d.dir ++ [0x2f#8] ++ utf8 "signed-pre-key") evsRd →
      FreeOnlyEvs evsFree →
      cEnvs.splitSigned spkBs evsSp →
      r1b_OkCtxPlaced r1b_CodeOk S g d s0 sf 0x1260 →
      cliIo.rd (runFiles g.i) (d.dir ++ [0x2f#8] ++ utf8 "registration-id") =
        .ok [r0, r1, r2, r3] →
      cliIo.rd (runFiles g.i) (d.dir ++ [0x2f#8] ++ utf8 "signed-pre-key") = .ok spkBs →
      splitSigned spkBs = some (spkId, spkKey, spkSig) →
      sf.readReg64 (.gpr 10#5) = spkPtr + 4#64 →
      sf.readReg64 (.gpr 27#5) = BitVec.ofNat 64 spkKey.length →
      sf.readReg64 .x2 = spkId.zeroExtend 64 →
      sf.readReg64 (.gpr 26#5) = d.dirPtr →
      sf.readReg64 (.gpr 28#5) = BitVec.ofNat 64 d.dir.length →
      let fsp := runFsp s0
      SepWPp (runProgPlaced H) (s0.readReg64 .lr) sf
        (((fsp + 0x4f0#64) ↦₆₄ (spkPtr + 4#64 + BitVec.ofNat 64 spkKey.length)) ∗
          ((fsp + 0x4f8#64) ↦₆₄ 64#64) ∗
          memRegion (fsp + 0x4d0#64) 32 ∗
          ownedBytes A.repAlloc spkCap spkPtr (BitVec.ofNat 64 spkBs.length) spkBs ∗
          ownedBytes A.repAlloc regCap regPtr 4#64 [r0, r1, r2, r3] ∗
          r1b_invCore_placed A.repAlloc g d s0 ∗ (lsLogFilterAddr ↦₆₄ 0#64) ∗
          ownedBytes A.repAlloc d.dirCap d.dirPtr (BitVec.ofNat 64 d.dir.length) d.dir ∗
          memRegion fsp 0x110 ∗
          memRegion (fsp + 0x110#64) 8 ∗ memRegion (fsp + 0x11c#64) 4 ∗
          memRegion (fsp + 0x120#64) 16 ∗ memRegion (fsp + 0x130#64) 0x20 ∗
          memRegion (fsp + 0x150#64) 16 ∗
          ((fsp + 0x164#64) ↦₃₂ ofLe32 r0 r1 r2 r3) ∗
          ((fsp + 0x168#64) ↦₆₄ spkPtr) ∗ ((fsp + 0x170#64) ↦₆₄ spkCap) ∗
          memRegion (fsp + 0x178#64) 8 ∗
          memRegion (fsp + 0x188#64) 8 ∗ ((fsp + 0x190#64) ↦₆₄ d.ikW3) ∗
          ((fsp + 0x198#64) ↦₆₄ regCap) ∗ ((fsp + 0x1a0#64) ↦₆₄ regPtr) ∗
          ((fsp + 0x1a8#64) ↦₆₄ d.ikW1) ∗
          ((fsp + 0x1b0#64) ↦₃₂ d.peerV.device.zeroExtend 32) ∗
          memRegion (fsp + 0x1b4#64) 4 ∗ memRegion (fsp + 0x1750#64) 24 ∗
          stackAt fsp (resStack - runFrame) ∗
          A.pool lim (M.stepEvents (evsP ++ evsRd ++ evsFree ++ evsSp) st) sf)
        Q Qp oom) :
    let fsp := runFsp s0
    SepWPp (runProgPlaced H) (s0.readReg64 .lr) s
      (memRegion (fsp + 0x4d0#64) 48 ∗
        ownedBytes A.repAlloc regCap regPtr (BitVec.ofNat 64 regBs.length) regBs ∗
        r1b_invCore_placed A.repAlloc g d s0 ∗ (lsLogFilterAddr ↦₆₄ 0#64) ∗
        ownedBytes A.repAlloc d.dirCap d.dirPtr (BitVec.ofNat 64 d.dir.length) d.dir ∗
        memRegion fsp 0x110 ∗
        memRegion (fsp + 0x110#64) 8 ∗ memRegion (fsp + 0x11c#64) 4 ∗
        memRegion (fsp + 0x120#64) 16 ∗ memRegion (fsp + 0x130#64) 0x20 ∗
        memRegion (fsp + 0x150#64) 16 ∗
        memRegion (fsp + 0x164#64) 4 ∗
        memRegion (fsp + 0x168#64) 8 ∗ memRegion (fsp + 0x170#64) 8 ∗
        memRegion (fsp + 0x178#64) 8 ∗
        memRegion (fsp + 0x188#64) 8 ∗ ((fsp + 0x190#64) ↦₆₄ d.ikW3) ∗
        ((fsp + 0x198#64) ↦₆₄ regCap) ∗ ((fsp + 0x1a0#64) ↦₆₄ regPtr) ∗
        ((fsp + 0x1a8#64) ↦₆₄ d.ikW1) ∗
        ((fsp + 0x1b0#64) ↦₃₂ d.peerV.device.zeroExtend 32) ∗
        memRegion (fsp + 0x1b4#64) 4 ∗ memRegion (fsp + 0x1750#64) 24 ∗
        stackAt fsp (resStack - runFrame) ∗ A.pool lim st s)
      Q Qp oom := by
  intro fsp
  let _ := hx23; let _ := hx25; let _ := hx26; let _ := hx28
  generalize hinvCore : r1b_invCore_placed A.repAlloc g d s0 = invCore
  have hst := hok.st
  have hal : fsp &&& 15#64 = 0#64 := r1b_fsp_align hst.sp hst.spAligned
  have ⟨hdir32, hpaths⟩ := r1b_init_path_facts_placed he hok.callEq
  have ⟨hspk_ok, hspk_len32⟩ := hpaths "signed-pre-key" (by simp [bundleNames])
  refine r1b_sepWPp_frame (by r1b_ac)
    (r1b_ownedBytes_facts A.repAlloc regCap regPtr (BitVec.ofNat 64 regBs.length) regBs)
    (by r1b_ac) ?_
  simp only [sepConj_assoc]
  refine r1b_sepWPp_pure_left fun ⟨_, hreg_cap, hreg_len63, _⟩ => ?_
  have hcmn_f : (regCap + 1#64 == 0#64) = false :=
    beq_false_of_ne (r1b_cmn1_false_of_lt63 hreg_cap)
  let _ := hcmn_f
  have hpc_in := hst.pc; change s.pc = (blkPl_579).base + 0x0c6c#64 at hpc_in
  by_cases hlen4 : regBs.length = 4
  · have hlen4_fixed : regBs.length = 4 := hlen4
    rcases r1b_exists_4bytes hlen4 with ⟨r0, r1, r2, r3, rfl⟩
    rw [show BitVec.ofNat 64 [r0, r1, r2, r3].length = 4#64 from rfl]
    have hx25 : s.readReg64 (.gpr 25#5) = 4#64 := hx25
    let _ := hreg_len63
    have hdir_nat : (BitVec.ofNat 64 d.dir.length).toNat = d.dir.length := by
      simp only [BitVec.toNat_ofNat]; omega
    have h4d0_sp : memRegion (fsp + 0x4d0#64) 48 =
        memRegion (fsp + 0x4d0#64) 24 ∗ memRegion (fsp + 0x4e8#64) 24 :=
      r1b_split_region fsp 0x4d0 24 24
    rw [h4d0_sp]
    simp only [sepConj_assoc]
    refine r1b_call_frame <|
      r1b_sepWPp_borrow_core A.repAlloc (cap := regCap) (ptr := regPtr) (len := 4#64)
        (bs := [r0, r1, r2, r3]) fun ⟨_, hreg_le, _, hreg_ne⟩ => ?_
    rw [r1b_pointsToBytes4_eq_u32 regPtr r0 r1 r2 r3]
    have hpc := hpc_in; have hrun := hst.run; have hsp : s.sp = fsp := hst.sp
    apply r1b_seq_lscro_oom (mid := lsmpl.base 596) hst.inv
    dsimp only [runProgPlaced, lsProg_579]
    apply LibsignalBinary.Proofs.Placed.BudgetPoolSync.sepWP_seg_ls_vm
      (Q := (blkPC_579).rebase (blkPl_579).base
        (LibsignalBinary.Proofs.Placed.BudgetPoolSync.hooksException _))
      blkLib_eq_579 blk579_noSvc0 (mid := lsmpl.base 596)
    intro _m_strip
    wp_steps
    refine SepWP.done (by simp only [wp_norm, arm64_norm, *]; try bv_omega)
      (by simp only [wp_norm, arm64_norm, *]) fun _m_real hnsp => ?_
    have hvmp1 : VmPreserved s _ :=
      hnsp.toVmPreserved (by simp only [wp_norm, arm64_norm, *])
    simp only [State.setMem_setMem] at hvmp1 ⊢
    apply SepWP.done (by simp only [wp_norm, arm64_norm, *])
      (by simp only [wp_norm, arm64_norm, *])
    refine r1b_bind_state_placed fun sm1 hsm1 hinv1 => by
      have hvm1 : VmPreserved s sm1 := hsm1 ▸ hvmp1
      rw [← A.pool_transport lim st s sm1 hvm1]
      change SepWPp (runProgPlaced H) _ _ _ _ _ _
      rw [← r1b_pointsToBytes4_eq_u32 regPtr r0 r1 r2 r3]
      have hrejoin_reg := r1b_ownedBytes_rejoin A.repAlloc regCap regPtr [r0, r1, r2, r3]
        hreg_le hreg_cap hreg_ne
      refine r1b_sepWPp_frame (by r1b_ac) hrejoin_reg (by r1b_ac) ?_
      have h14 : (utf8 "signed-pre-key").length = 14 := by
        simp only [utf8, List.length_map, String.toUTF8_eq_toByteArray]; decide +kernel
      have hspk_name_len : (utf8 "signed-pre-key").length < 2 ^ 32 := by omega
      refine r1b_call_frame <|
        r1b_call_path_ro_placed (ret := fsp + 0x4d0#64)
          (dirCap := d.dirCap) (dirPtr := d.dirPtr) (dir := d.dir)
          hh hbnd hinv1 r1b_ro_spk_placed
          (by simp only [hsm1, wp_norm, arm64_norm])
          (by simp only [hsm1, wp_norm, arm64_norm, hst.run])
          (by simpa only [hsm1, wp_norm, arm64_norm] using hst.sp)
          (by simpa only [hsm1, wp_norm, arm64_norm] using hst.fp)
          (by simpa only [calleeSavedVRegs, hsm1, wp_norm, arm64_norm] using hst.vregs)
          hst.spAligned (retOff := 0x0ca0)
          (by simp only [hsm1, wp_norm, arm64_norm])
          (by simp only [hsm1, wp_norm, arm64_norm]; try exact congrArg (· + 0x4d0#64) hst.sp)
          (by simp only [hsm1, wp_norm, arm64_norm]; try exact hx26)
          (by simp only [hsm1, wp_norm, arm64_norm]; exact hdir_nat)
          (by simp only [hsm1, wp_norm, arm64_norm]; rfl)
          (by rw [h14]; simp only [hsm1, wp_norm, arm64_norm])
          hdir32 hspk_name_len (hfit_spk_path rfl) hpanic
          fun sf1 evsP pCap pPtr hevsP hin1 hcs1 hfs1 htr1 => ?_
      have hok1 : r1b_OkCtxPlaced r1b_CodeOk S g d s0 sf1 0x0ca0 := hok.after_call
        (by simp only [hsm1, wp_norm, arm64_norm]) (by simp only [hsm1, wp_norm, arm64_norm])
        (by simp only [hsm1, wp_norm, arm64_norm]) (by simp only [hsm1, wp_norm, arm64_norm])
        (by simp only [hsm1, wp_norm, arm64_norm]) (by simp only [hsm1, wp_norm, arm64_norm])
        hin1 hcs1 hfs1 htr1
      have hx25_1 : sf1.readReg64 (.gpr 25#5) = (ofLe32 r0 r1 r2 r3).zeroExtend 64 :=
        hcs1.2.2.2.2.2.2.1.trans (by simp only [hsm1, wp_norm, arm64_norm])
      have hx26_1 : sf1.readReg64 (.gpr 26#5) = d.dirPtr :=
        hcs1.2.2.2.2.2.2.2.1.trans (by simp only [hsm1, wp_norm, arm64_norm]; try exact hx26)
      have hx28_1 : sf1.readReg64 (.gpr 28#5) = BitVec.ofNat 64 d.dir.length :=
        hcs1.2.2.2.2.2.2.2.2.2.1.trans (by simp only [hsm1, wp_norm, arm64_norm]; try exact hx28)
      let _ := hx25_1; let _ := hx26_1; let _ := hx28_1
      have hspk_path_nat :
          (BitVec.ofNat 64 (d.dir ++ [0x2f#8] ++ utf8 "signed-pre-key").length).toNat =
            (d.dir ++ [0x2f#8] ++ utf8 "signed-pre-key").length := by
        simp only [BitVec.toNat_ofNat]; omega
      simp only [BitVec.add_assoc, BitVec.reduceAdd]
      have hpc1 := hin1.pc; change sf1.pc = (blkPl_579).base + 0x0ca0#64 at hpc1
      have hpc := hpc1; have hrun := hin1.run; have hsp : sf1.sp = fsp := hin1.sp
      apply r1b_seq_lscro_oom (mid := lsρ lsReadFileSym) hin1.inv
      dsimp only [runProgPlaced, lsProg_579]
      apply sepWP_seg_ls_vm (Q := (blkPC_579).rebase (blkPl_579).base (hooksException _))
        blkLib_eq_579 blk579_noSvc0 (mid := lsρ lsReadFileSym)
      intro _m_strip; wp_steps
      refine SepWP.done (by simp only [wp_norm, arm64_norm, *]; try bv_omega)
        (by simp only [wp_norm, arm64_norm, *]) fun _m_real hnsp2 => ?_
      have hvmp2 : VmPreserved sf1 _ := hnsp2.toVmPreserved (by simp only [wp_norm, arm64_norm, *])
      try simp only [State.setMem_setMem] at hvmp2 ⊢
      apply SepWP.done (by simp only [wp_norm, arm64_norm, *])
        (by simp only [wp_norm, arm64_norm, *])
      refine r1b_bind_state_placed fun sm2 hsm2 hinv2 => by
        have hvm2 : VmPreserved sf1 sm2 := hsm2 ▸ hvmp2
        rw [← A.pool_transport lim (M.stepEvents evsP st) sf1 sm2 hvm2]
        change SepWPp (runProgPlaced H) _ _ _ _ _ _
        have h4e0 :
            ((fsp + 0x4e0#64) ↦₆₄
              BitVec.ofNat 64 (d.dir ++ [0x2f#8] ++ utf8 "signed-pre-key").length) ∗
              memRegion (fsp + 0x4e8#64) 24 ⊢ memRegion (fsp + 0x4e0#64) 32 := by
          simpa only [BitVec.add_assoc, BitVec.reduceAdd] using
            r1b_cell64_cons (a := fsp + 0x4e0#64)
              (BitVec.ofNat 64 (d.dir ++ [0x2f#8] ++ utf8 "signed-pre-key").length)
              (n := 24) (by decide)
        have h4d8 :
            ((fsp + 0x4d8#64) ↦₆₄ pPtr) ∗
              ((fsp + 0x4e0#64) ↦₆₄
                BitVec.ofNat 64 (d.dir ++ [0x2f#8] ++ utf8 "signed-pre-key").length) ∗
              memRegion (fsp + 0x4e8#64) 24 ⊢ memRegion (fsp + 0x4d8#64) 40 := by
          refine Entails.trans (sepConj_mono_right h4e0) ?_
          simpa only [BitVec.add_assoc, BitVec.reduceAdd] using
            r1b_cell64_cons (a := fsp + 0x4d8#64) pPtr (n := 32) (by decide)
        have hfiles_sm2 : sm2.fs.files = runFiles g.i := by
          rw [show sm2.fs.files = sf1.fs.files by simp only [hsm2, wp_norm, arm64_norm]]
          exact hok1.fs
        refine r1b_sepWPp_frame (by r1b_ac) h4d8 (by r1b_ac) ?_
        refine r1b_call_frame <|
          r1b_call_readFile_placed hh hc hbnd hinv2
            (by simp only [hsm2, wp_norm, arm64_norm])
            (by simp only [hsm2, wp_norm, arm64_norm, hin1.run])
            (by simpa only [hsm2, wp_norm, arm64_norm] using hin1.sp)
            (by simpa only [hsm2, wp_norm, arm64_norm] using hin1.fp)
            (by simpa only [calleeSavedVRegs, hsm2, wp_norm, arm64_norm] using hin1.vregs)
            hst.spAligned (retOff := 0x0cb8)
            (by simp only [hsm2, wp_norm, arm64_norm])
            (pathCap := pCap) (pathPtr := pPtr)
            (path := d.dir ++ [0x2f#8] ++ utf8 "signed-pre-key") (ret := fsp + 0x1750#64)
            (by simp only [hsm2, wp_norm, arm64_norm])
            (by simpa only [hsm2, wp_norm, arm64_norm] using hspk_path_nat)
            (by simp only [hsm2, wp_norm, arm64_norm]; try exact congrArg (· + 0x1750#64) hin1.sp)
            hspk_len32 hspk_ok
            (by rw [hfiles_sm2]; exact hfit_spk_rd evsP rfl hevsP)
            hpanic
            (fun sf2 evsRd w1 w2 hevsRd hin2 hcs2 hout2 => ?_)
            (fun sf2 evsRd spkCap spkPtr spkBs hevsRd hin2 hcs2 hspk_rd_sf hfs2 htr2 => ?_)
        · have hevsRd' :
              cEnvs.readFile (runFiles g.i) (d.dir ++ [0x2f#8] ++ utf8 "signed-pre-key") evsRd :=
            hfiles_sm2 ▸ hevsRd
          have hrd_err :
              cliIo.rd (runFiles g.i) (d.dir ++ [0x2f#8] ++ utf8 "signed-pre-key") = .error () :=
            hfiles_sm2 ▸ hout2.1
          have hc2 : r1b_ErrCtxPlaced r1b_CodeOk g d s0 sf2 0x0cb8 :=
            hok1.after_readErr
              (by simp only [hsm2, wp_norm, arm64_norm]) (by simp only [hsm2, wp_norm, arm64_norm])
              (by simp only [hsm2, wp_norm, arm64_norm]) (by simp only [hsm2, wp_norm, arm64_norm])
              (by simp only [hsm2, wp_norm, arm64_norm]) (by simp only [hsm2, wp_norm, arm64_norm])
              hin2 hcs2 hout2 r1b_none_spk_rd
          have hx27_2 : sf2.readReg64 (.gpr 27#5) = pPtr :=
            hcs2.2.2.2.2.2.2.2.2.1.trans (by simp only [hsm2, wp_norm, arm64_norm])
          let _ := hx27_2
          rw [ProofLib.memRegion_four (fsp + 0x164#64)]
          simp only [sepExists_sepConj_left, sepExists_sepConj_right]
          try simp only [BitVec.add_assoc]; try simp only [BitVec.reduceAdd]
          try simp only [sepConj_assoc]
          refine SepWPp.exists_elim fun _v164 => ?_
          have hpc2 := hin2.pc; change sf2.pc = (blkPl_579).base + 0x0cb8#64 at hpc2
          have hpc := hpc2; have hrun := hin2.run; have hsp : sf2.sp = fsp := hin2.sp
          apply r1b_seq_lscro_oom (mid := (blkPl_579).base + 0x11b4#64) hin2.inv
          dsimp only [runProgPlaced, lsProg_579]
          apply sepWP_seg_ls_vm (Q := (blkPC_579).rebase (blkPl_579).base (hooksException _))
            blkLib_eq_579 blk579_noSvc0 (mid := (blkPl_579).base + 0x11b4#64)
          intro _m_strip; wp_steps
          refine SepWP.done (by simp only [wp_norm, arm64_norm, *]; try bv_omega)
            (by simp only [wp_norm, arm64_norm, *]) fun _m_real hnsp3 => ?_
          have hvmp3 : VmPreserved sf2 _ :=
            hnsp3.toVmPreserved (by simp only [wp_norm, arm64_norm, *])
          try simp only [State.setMem_setMem] at hvmp3 ⊢
          apply SepWP.done (by simp only [wp_norm, arm64_norm, *])
            (by simp only [wp_norm, arm64_norm, *])
          refine r1b_bind_state_placed fun sm3 hsm3 hinv3 => by
            have hvm3 : VmPreserved sf2 sm3 := hsm3 ▸ hvmp3
            rw [← A.pool_transport lim (M.stepEvents evsRd (M.stepEvents evsP st)) sf2 sm3 hvm3]
            change SepWPp (runProgPlaced H) _ _ _ _ _ _
            have hc3 : r1b_ErrCtxPlaced r1b_CodeOk g d s0 sm3 0x11b4 := hc2.of_step
              { pc := by simp only [hsm3, wp_norm, arm64_norm]
                run := by simp only [hsm3, wp_norm, arm64_norm, hin2.run]
                sp := by simpa only [hsm3, wp_norm, arm64_norm] using hin2.sp
                fp := by simpa only [hsm3, wp_norm, arm64_norm] using hin2.fp
                inv := hinv3
                vregs := by simpa only [calleeSavedVRegs, hsm3, wp_norm, arm64_norm] using hin2.vregs
                spAligned := hst.spAligned }
              (by simp only [hsm3, wp_norm, arm64_norm]) (by simp only [hsm3, wp_norm, arm64_norm])
              (by simp only [hsm3, wp_norm, arm64_norm]) (by simp only [hsm3, wp_norm, arm64_norm])
              (by simp only [hsm3, wp_norm, arm64_norm])
            have h1750 :
                ((fsp + 0x1750#64) ↦₆₄ 0xffffffffffffffff#64) ∗
                  ((fsp + 0x1758#64) ↦₆₄ w1) ∗ ((fsp + 0x1760#64) ↦₆₄ w2) ⊢
                  memRegion (fsp + 0x1750#64) 24 := by
              simpa only [BitVec.add_assoc, BitVec.reduceAdd] using
                r1b_cells3_to_region24 (fsp + 0x1750#64) 0xffffffffffffffff#64 w1 w2
            have hst_err :
                (invCore ∗ (lsLogFilterAddr ↦₆₄ 0#64) ∗
                  ownedBytes A.repAlloc d.dirCap d.dirPtr (BitVec.ofNat 64 d.dir.length) d.dir ∗
                  memRegion fsp 0x110 ∗ memRegion (fsp + 0x130#64) 0x20 ∗
                  ((fsp + 0x164#64) ↦₃₂ (sf2.readReg64 (.gpr 25#5)).truncate 32) ∗
                  ((fsp + 0x190#64) ↦₆₄ d.ikW3) ∗
                  ((fsp + 0x1a8#64) ↦₆₄ d.ikW1) ∗
                  ((fsp + 0x1b0#64) ↦₃₂ d.peerV.device.zeroExtend 32) ∗
                  memRegion (fsp + 0x1b4#64) 4 ∗ memRegion (fsp + 0x1750#64) 24 ∗
                  stackAt fsp (resStack - runFrame) ∗
                  A.pool lim (M.stepEvents evsRd (M.stepEvents evsP st)) sm3) ⊢
                r1b_errCommon (A.atState lim (M.stepEvents evsRd (M.stepEvents evsP st)) sm3)
                  g d s0 resStack ∗
                  memRegion (fsp + 0x190#64) 8 ∗ memRegion (fsp + 0x1a8#64) 16 := by
              rw [← hinvCore]
              exact r1b_stage_to_err_placed
                (A.atState lim (M.stepEvents evsRd (M.stepEvents evsP st)) sm3)
                g d s0 resStack ((sf2.readReg64 (.gpr 25#5)).truncate 32)
            generalize herrCommon :
              r1b_errCommon (A.atState lim (M.stepEvents evsRd (M.stepEvents evsP st)) sm3)
                g d s0 resStack = errCommon at hst_err
            refine r1b_sepWPp_frame (by r1b_ac) h1750 (by r1b_ac) ?_
            refine sepWPp_weaken_pre ?_
              (r1b_err_11b4_placed (st := M.stepEvents evsRd (M.stepEvents evsP st))
                (pCap := pCap) (pPtr := pPtr)
                (pBs := d.dir ++ [0x2f#8] ++ utf8 "signed-pre-key")
                (regCap := regCap) (regPtr := regPtr) (regBs := [r0, r1, r2, r3])
                hh hdrop hbnd hc3
                (by simp only [hsm3, wp_norm, arm64_norm])
                (by simp only [hsm3, wp_norm, arm64_norm]; try exact hx27_2)
                (by
                  simpa only [M.stepEvents_append] using
                    hfit_spk_rd_err evsP evsRd rfl hevsP hrd_err hevsRd')
                (fun evsFree hfo => by
                  simpa only [M.stepEvents_append, List.append_assoc] using
                    henv_spk_rd_err evsP evsRd evsFree rfl hevsP hrd_err hevsRd' hfo)
                hpanic hrej)
            try dsimp only
            rw [herrCommon]
            exact r1b_entails_frame (by r1b_ac) hst_err (by r1b_ac)
        · have hevsRd' :
              cEnvs.readFile (runFiles g.i) (d.dir ++ [0x2f#8] ++ utf8 "signed-pre-key") evsRd :=
            hfiles_sm2 ▸ hevsRd
          have hok2 : r1b_OkCtxPlaced r1b_CodeOk S g d s0 sf2 0x0cb8 := hok1.after_call
            (by simp only [hsm2, wp_norm, arm64_norm]) (by simp only [hsm2, wp_norm, arm64_norm])
            (by simp only [hsm2, wp_norm, arm64_norm]) (by simp only [hsm2, wp_norm, arm64_norm])
            (by simp only [hsm2, wp_norm, arm64_norm]) (by simp only [hsm2, wp_norm, arm64_norm])
            hin2 hcs2 hfs2 htr2
          have hspk_rd : cliIo.rd (runFiles g.i) (d.dir ++ [0x2f#8] ++ utf8 "signed-pre-key") =
              .ok spkBs := hfiles_sm2 ▸ hspk_rd_sf
          have hx25_2 : sf2.readReg64 (.gpr 25#5) = (ofLe32 r0 r1 r2 r3).zeroExtend 64 :=
            hcs2.2.2.2.2.2.2.1.trans (by simp only [hsm2, wp_norm, arm64_norm]; try exact hx25_1)
          have hx26_2 : sf2.readReg64 (.gpr 26#5) = d.dirPtr :=
            hcs2.2.2.2.2.2.2.2.1.trans (by simp only [hsm2, wp_norm, arm64_norm]; try exact hx26_1)
          have hx27_2 : sf2.readReg64 (.gpr 27#5) = pPtr :=
            hcs2.2.2.2.2.2.2.2.2.1.trans (by simp only [hsm2, wp_norm, arm64_norm])
          have hx28_2 : sf2.readReg64 (.gpr 28#5) = BitVec.ofNat 64 d.dir.length :=
            hcs2.2.2.2.2.2.2.2.2.2.1.trans (by simp only [hsm2, wp_norm, arm64_norm]; try exact hx28_1)
          let _ := hx25_2; let _ := hx26_2; let _ := hx27_2; let _ := hx28_2
          refine r1b_sepWPp_frame (by r1b_ac)
            (r1b_ownedBytes_facts A.repAlloc spkCap spkPtr (BitVec.ofNat 64 spkBs.length) spkBs)
            (by r1b_ac) ?_
          try simp only [BitVec.add_assoc]; try simp only [BitVec.reduceAdd]
          try simp only [sepConj_assoc]
          refine r1b_sepWPp_pure_left fun ⟨_, hspk_cap, _, _⟩ => ?_
          have hcmn_spk : (spkCap + 1#64 == 0#64) = false :=
            beq_false_of_ne (r1b_cmn1_false_of_lt63 hspk_cap)
          let _ := hcmn_spk
          rw [ProofLib.memRegion_four (fsp + 0x164#64), ProofLib.memRegion_eight (fsp + 0x170#64)]
          simp only [sepExists_sepConj_left, sepExists_sepConj_right]
          try simp only [sepConj_assoc]
          refine SepWPp.exists_elim fun _v164 => SepWPp.exists_elim fun _v170 => ?_
          have hpc2 := hin2.pc; change sf2.pc = (blkPl_579).base + 0x0cb8#64 at hpc2
          have hpc := hpc2; have hrun := hin2.run; have hsp : sf2.sp = fsp := hin2.sp
          apply r1b_seq_lscro_oom (mid := (blkPl_579).base + 0x11f4#64) hin2.inv
          dsimp only [runProgPlaced, lsProg_579]
          apply sepWP_seg_ls_vm (Q := (blkPC_579).rebase (blkPl_579).base (hooksException _))
            blkLib_eq_579 blk579_noSvc0 (mid := (blkPl_579).base + 0x11f4#64)
          intro _m_strip; wp_steps
          refine SepWP.done (by simp only [wp_norm, arm64_norm, *]; try bv_omega)
            (by simp only [wp_norm, arm64_norm, *]) fun _m_real hnsp3 => ?_
          have hvmp3 : VmPreserved sf2 _ :=
            hnsp3.toVmPreserved (by simp only [wp_norm, arm64_norm, *])
          try simp only [State.setMem_setMem] at hvmp3 ⊢
          apply SepWP.done (by simp only [wp_norm, arm64_norm, *])
            (by simp only [wp_norm, arm64_norm, *])
          refine r1b_bind_state_placed fun sm3 hsm3 hinv3 => by
            have hvm3 : VmPreserved sf2 sm3 := hsm3 ▸ hvmp3
            rw [← A.pool_transport lim (M.stepEvents evsRd (M.stepEvents evsP st)) sf2 sm3 hvm3]
            change SepWPp (runProgPlaced H) _ _ _ _ _ _
            have hok3 : r1b_OkCtxPlaced r1b_CodeOk S g d s0 sm3 0x11f4 := hok2.of_step
              { pc := by simp only [hsm3, wp_norm, arm64_norm]
                run := by simp only [hsm3, wp_norm, arm64_norm, hin2.run]
                sp := by simpa only [hsm3, wp_norm, arm64_norm] using hin2.sp
                fp := by simpa only [hsm3, wp_norm, arm64_norm] using hin2.fp
                inv := hinv3
                vregs := by simpa only [calleeSavedVRegs, hsm3, wp_norm, arm64_norm] using hin2.vregs
                spAligned := hst.spAligned }
              (by simp only [hsm3, wp_norm, arm64_norm]) (by simp only [hsm3, wp_norm, arm64_norm])
              (by simp only [hsm3, wp_norm, arm64_norm]) (by simp only [hsm3, wp_norm, arm64_norm])
              (by simp only [hsm3, wp_norm, arm64_norm]) (by simp only [hsm3, wp_norm, arm64_norm])
            have hv164 : ((sf2.readReg64 (.gpr 25#5)).truncate 32) = ofLe32 r0 r1 r2 r3 := by
              rw [hx25_2]; bv_bits
            have hv164' : (((ofLe32 r0 r1 r2 r3).zeroExtend 64).truncate 32) = ofLe32 r0 r1 r2 r3 := by
              bv_bits
            try rw [hv164]
            try rw [hv164']
            have h1750 :
                ((fsp + 0x1750#64) ↦₆₄ spkCap) ∗
                  ((fsp + 0x1758#64) ↦₆₄ spkPtr) ∗
                  ((fsp + 0x1760#64) ↦₆₄ BitVec.ofNat 64 spkBs.length) ⊢
                  memRegion (fsp + 0x1750#64) 24 := by
              simpa only [BitVec.add_assoc, BitVec.reduceAdd] using
                r1b_cells3_to_region24 (fsp + 0x1750#64) spkCap spkPtr (BitVec.ofNat 64 spkBs.length)
            refine sepWPp_weaken_pre ?_
              (r1b_spk_dealloc_11f4_placed
                (st := M.stepEvents evsRd (M.stepEvents evsP st))
                (r0 := r0) (r1 := r1) (r2 := r2) (r3 := r3)
                (pCap := pCap) (pPtr := pPtr) (pBs := d.dir ++ [0x2f#8] ++ utf8 "signed-pre-key")
                (regCap := regCap) (regPtr := regPtr) (spkCap := spkCap) (spkPtr := spkPtr)
                (spkBs := spkBs) hh hc hdrop hbnd hok3 hreg_rd hspk_rd
                (by simp only [hsm3, wp_norm, arm64_norm]; try exact hx27_2)
                (by simp only [hsm3, wp_norm, arm64_norm])
                (by simp only [hsm3, wp_norm, arm64_norm])
                (by simp only [hsm3, wp_norm, arm64_norm])
                (by simp only [hsm3, wp_norm, arm64_norm])
                (by simp only [hsm3, wp_norm, arm64_norm]; try exact hx26_2)
                (by simp only [hsm3, wp_norm, arm64_norm]; try exact hx28_2)
                (fun evsFree hfo => by
                  simpa only [M.stepEvents_append, List.append_assoc] using
                    hfit_spk_split evsP evsRd evsFree spkBs rfl hevsP hspk_rd hevsRd' hfo)
                (fun evsFree1 evsSp evsFree2 hfo1 hnone hsp_ev hfo2 => by
                  simpa only [M.stepEvents_append, List.append_assoc] using
                    henv_spk_split_err evsP evsRd evsFree1 spkBs evsSp evsFree2
                      rfl hevsP hspk_rd hevsRd' hfo1 hnone hsp_ev hfo2)
                hpanic hrej
                fun sf4 evsFree evsSp spkId spkKey spkSig hfo hsp_ev
                    hok4 hsp_s hx10_4 hx27_4 hx2_4 hx26_4 hx28_4 => by
                  simpa only [M.stepEvents_append, List.append_assoc] using
                    hk sf4 evsP evsRd evsFree evsSp r0 r1 r2 r3
                      spkCap spkPtr spkBs spkKey spkSig spkId
                      hevsP hevsRd' hfo hsp_ev
                      hok4 hreg_rd hspk_rd hsp_s hx10_4 hx27_4 hx2_4 hx26_4 hx28_4)
            try dsimp only
            rw [hinvCore]
            exact r1b_entails_frame (by r1b_ac) h1750 (by r1b_ac)
  · have hcmp4 : (BitVec.ofNat 64 regBs.length == 4#64) = false :=
      r1b_ofNat64_ne4 hreg_len63 hlen4
    let _ := hcmp4
    have hpc := hpc_in; have hrun := hst.run; have hsp : s.sp = fsp := hst.sp
    apply r1b_seq_lscro_oom (mid := (blkPl_579).base + 0x0df0#64) hst.inv
    dsimp only [runProgPlaced, lsProg_579]
    apply sepWP_seg_ls_vm (Q := (blkPC_579).rebase (blkPl_579).base (hooksException _))
      blkLib_eq_579 blk579_noSvc0 (mid := (blkPl_579).base + 0x0df0#64)
    intro _m_strip; wp_steps
    refine SepWP.done (by simp only [wp_norm, arm64_norm, *]; try bv_omega)
      (by simp only [wp_norm, arm64_norm, *]) fun _m_real hnsp1 => ?_
    have hvmp1 : VmPreserved s _ := hnsp1.toVmPreserved (by simp only [wp_norm, arm64_norm, *])
    try simp only [State.setMem_setMem] at hvmp1 ⊢
    apply SepWP.done (by simp only [wp_norm, arm64_norm, *])
      (by simp only [wp_norm, arm64_norm, *])
    refine r1b_bind_state_placed fun sm1 hsm1 hinv1 => by
      have hvm1 : VmPreserved s sm1 := hsm1 ▸ hvmp1
      rw [← A.pool_transport lim st s sm1 hvm1]
      change SepWPp (runProgPlaced H) _ _ _ _ _ _
      have hc1 : r1b_ErrCtxPlaced r1b_CodeOk g d s0 sm1 0x0df0 :=
        (hok.of_step
          { pc := by simp only [hsm1, wp_norm, arm64_norm]
            run := by simp only [hsm1, wp_norm, arm64_norm, hst.run]
            sp := by simpa only [hsm1, wp_norm, arm64_norm] using hst.sp
            fp := by simpa only [hsm1, wp_norm, arm64_norm] using hst.fp
            inv := hinv1
            vregs := by simpa only [calleeSavedVRegs, hsm1, wp_norm, arm64_norm] using hst.vregs
            spAligned := hst.spAligned }
          (by simp only [hsm1, wp_norm, arm64_norm]) (by simp only [hsm1, wp_norm, arm64_norm])
          (by simp only [hsm1, wp_norm, arm64_norm]) (by simp only [hsm1, wp_norm, arm64_norm])
          (by simp only [hsm1, wp_norm, arm64_norm]) (by simp only [hsm1, wp_norm, arm64_norm])).to_err
        (r1b_none_reg_len hreg_rd hlen4)
      have hcore :
          (invCore ∗ (lsLogFilterAddr ↦₆₄ 0#64) ∗
            ownedBytes A.repAlloc d.dirCap d.dirPtr (BitVec.ofNat 64 d.dir.length) d.dir ∗
            memRegion fsp 0x110 ∗ memRegion (fsp + 0x130#64) 0x20 ∗
            memRegion (fsp + 0x164#64) 4 ∗ memRegion (fsp + 0x1750#64) 24 ∗
            stackAt fsp (resStack - runFrame) ∗ A.pool lim st sm1) ⊢
          r1b_errCommon (A.atState lim st sm1) g d s0 resStack := by
        rw [← hinvCore]
        exact r1b_invCore_to_errCommon_placed (A.atState lim st sm1) g d s0 resStack
      generalize herrCommon :
        r1b_errCommon (A.atState lim st sm1) g d s0 resStack = errCommon at hcore
      have h168 :
          memRegion (fsp + 0x168#64) 8 ∗ memRegion (fsp + 0x170#64) 8 ∗
            memRegion (fsp + 0x178#64) 8 ⊢ memRegion (fsp + 0x168#64) 24 := by
        rw [r1b_join_region fsp 0x170 8 8, r1b_join_region fsp 0x168 8 16]
        exact Entails.refl _
      have h188 :
          memRegion (fsp + 0x188#64) 8 ∗ ((fsp + 0x190#64) ↦₆₄ d.ikW3) ⊢
            memRegion (fsp + 0x188#64) 16 := by
        refine Entails.trans (sepConj_mono_right (pointsTo64_entails_memRegion _ _)) ?_
        rw [r1b_join_region fsp 0x188 8 8]; exact Entails.refl _
      have h1a8 :
          ((fsp + 0x1a8#64) ↦₆₄ d.ikW1) ∗
            ((fsp + 0x1b0#64) ↦₃₂ d.peerV.device.zeroExtend 32) ∗
            memRegion (fsp + 0x1b4#64) 4 ⊢ memRegion (fsp + 0x1a8#64) 16 := by
        refine Entails.trans (sepConj_mono_right (sepConj_mono_left
          (pointsTo32_entails_memRegion _ _))) ?_
        rw [r1b_join_region fsp 0x1b0 4 4]
        simpa only [BitVec.add_assoc, BitVec.reduceAdd] using
          r1b_cell64_cons (a := fsp + 0x1a8#64) d.ikW1 (n := 8) (by decide)
      refine sepWPp_weaken_pre ?_
        (r1b_err_0df0_placed (st := st) (regCap := regCap) (regPtr := regPtr) (regBs := regBs)
          hh hdrop hbnd hc1 (hfit_bad_reg hlen4) (henv_bad_reg · hlen4) hpanic hrej)
      try dsimp only
      rw [herrCommon]
      exact r1b_entails_frame (by r1b_ac)
        (sepConj_mono hcore (sepConj_mono h168 (sepConj_mono h188 h1a8))) (by r1b_ac)

end LibsignalBinary.Proofs.SignalSession.Cli.Run.Compose.Arms.R1b.ReadRegSpkSpinePlacedBudgetAux
