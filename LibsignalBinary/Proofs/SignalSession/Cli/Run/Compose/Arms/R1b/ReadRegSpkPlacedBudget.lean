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
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Compose.Arms.R1b.CallHelpersParsePlacedBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Compose.Arms.R1b.ReadRegSpkPlacedBudgetAux
import Arm64.Trusted.Spec.Hoare
import Arm64.Trusted.Spec.SepLogic
import LibsignalBinary.Proofs.Common.SharedHelpers
meta import LibsignalBinary.Proofs.Common.SharedHelpers -- shake: keep
import LibsignalBinary.Proofs.SignalSession.Cli.Main.Proofs.M4Layout

/-!
# Budget-Threaded Stage 1 Error Exits and `split_signed` Step of Arm `R1b`

Verifies `r1b_err_0c14_placed` (`0x0c14 → 0x0cec → 0x2bf0`, unreadable `registration-id`),
`r1b_after_spk_dealloc_placed` (`0x1230 → 0x1260`, `split_signed` on `spkBs`), and re-exports
`r1b_err_11b4_placed` and `r1b_err_0df0_placed` on Block `579` under `[LibsignalPlacement]` and
`RustCliAllocBudget M`.
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 200000
set_option linter.unusedSimpArgs false

namespace LibsignalBinary.Proofs.SignalSession.Cli.Run.Compose.Arms.R1b.ReadRegSpkPlacedBudget

open Arm64 Arm64.Process ProofLib SepProp
open CryptoVerification (LibsignalHooks LibsignalPlacement lsLogFilterAddr lsmpl lsρ)
open CryptoVerification.LibsignalTripleRatchetRepr (speWord)
open CryptoVerification.SignalSession
  (lsRustAllocSymCli lsRustDeallocSymCli lsRustNoAllocShimSymCli)
open CryptoVerification.SignalSession.Cli (StoresGhost ofLe32 splitOkTag splitSigned utf8)
open CryptoVerification.SignalSession.Cli.MainHops (RunCall cliIo ownedBytes sepWPp_weaken_pre)
open CryptoVerification.SignalSession.Cli.Run.Placed (blkPl_579 lsProg_579)
open CryptoVerification.SignalSession.Cli.RunCompose
  (Init1Data InRunPlaced PanicK RejectKind RunSem r1b_CodeOk r1b_ErrCtxPlaced r1b_OkCtxPlaced
   r1b_SpePayload r1b_SpePayload_str r1b_StackBounds r1b_bind_state_placed r1b_buf22_owned
   r1b_buf22_realign r1b_buf22_split1 r1b_cell64_cons r1b_cells2_to_region16
   r1b_cmn1_false_of_lt63 r1b_entails_frame_core r1b_errCommon r1b_errCore r1b_fsp_align
   r1b_invCore_placed r1b_join_region r1b_layout1 r1b_none_spk_split r1b_ownedBytes_rejoin
   r1b_ownedBytes_zero r1b_ownedRest r1b_region16_to_cells r1b_ro_split22
   r1b_ro_unreadable_placed r1b_sepWPp_borrow_core r1b_sepWPp_drop_left r1b_sepWPp_frame_core
   r1b_sepWPp_pure_left r1b_sepWPp_with_ro_placed r1b_stage_to_err_placed r1b_u64_split32
   r1b_unreadSym runFiles runFsp runPcPlaced runPcPlaced_eq runProgPlaced)
open CryptoVerification.SignalSession.Cli.RunSkeleton (RunBudgets RunSlots runFrame)
open LibsignalBinary.Heap
  (AllocCostModel AllocEvent BudgetLimits FitsEnv FitsEvents FreeOnlyEvs RustCliAllocBudget
   VmPreserved rustAllocEvents rustDeallocEvents)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Compose.Arms.R1b.CallHelpersParsePlacedBudget
  (r1b_call_splitSigned_placed)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Compose.Arms.R1b.CallHelpersPlacedBudget
  (r1b_call_alloc_placed r1b_call_shim_pool_placed)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Compose.Arms.R1b.CommonPlacedBudget
  (r1b_call_dealloc_ownedBytes_placed)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Compose.Arms.R1b.ErrCleanupPlacedBudget
  (r1b_cleanup_2bf0_placed_env r1b_errCommon_atState_eq sepWP_with_vm_oom)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Compose.Arms.R1b.ReadRegSpkPlacedBudgetAux
  (freeOnlyEvs_rustDealloc_append r1b_err_13bc_placed r1b_seq_lscro_oom)
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

local macro "r1b_prove_spe_str" : tactic =>
  `(tactic| (refine r1b_SpePayload_str _ ?_; refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> bv_bits))

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

/-! ## Error Exits Re-Exported from `ReadRegSpkPlacedBudgetAux` and `0x0c14` -/

theorem r1b_err_11b4_placed [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {st : M.σ}
    {EnvAt : StoresGhost → RejectKind → M.σ → Prop}
    {H : LibsignalHooks} {B : RunBudgets}
    {g : RunCall} {d : Init1Data} {s0 s : State} {resStack : Nat}
    {pCap pPtr regCap regPtr : BitVec 64} {pBs regBs : List (BitVec 8)}
    {Q Qp : State → SepProp → Prop} {oom : State → SepProp}
    (hh : RunHooksPlaced A lim H)
    (hdrop : DropSpeOwnedOkAtBlock (runProgPlaced H) A lim)
    (hbnd : r1b_StackBounds B resStack)
    (hc : r1b_ErrCtxPlaced r1b_CodeOk g d s0 s 0x11b4)
    (hx23 : s.readReg64 (.gpr 23#5) = 0xffffffffffffffff#64)
    (hx27 : s.readReg64 (.gpr 27#5) = pPtr)
    (hfit : FitsEvents M lim st [AllocEvent.alloc 22])
    (henv : ∀ evsFree, FreeOnlyEvs evsFree →
      EnvAt StoresGhost.opened .postDispatch (M.stepEvents ([AllocEvent.alloc 22] ++ evsFree) st))
    (hpanic : PanicK g s0 Qp)
    (hrej : RejectKPlacedEnv r1b_CodeOk H A lim EnvAt g s0 resStack Q Qp oom) :
    let fsp := runFsp s0
    SepWPp (runProgPlaced H) (s0.readReg64 .lr) s
      (((fsp + 0x4d0#64) ↦₆₄ pCap) ∗ memRegion (fsp + 0x4d8#64) 40 ∗
        ownedBytes A.repAlloc pCap pPtr (BitVec.ofNat 64 pBs.length) pBs ∗
        ownedBytes A.repAlloc regCap regPtr (BitVec.ofNat 64 regBs.length) regBs ∗
        r1b_errCommon (A.atState lim st s) g d s0 resStack ∗
        memRegion (fsp + 0x110#64) 8 ∗ memRegion (fsp + 0x11c#64) 4 ∗
        memRegion (fsp + 0x120#64) 16 ∗ memRegion (fsp + 0x150#64) 16 ∗
        memRegion (fsp + 0x168#64) 8 ∗ memRegion (fsp + 0x170#64) 8 ∗
        memRegion (fsp + 0x178#64) 8 ∗ memRegion (fsp + 0x188#64) 8 ∗
        memRegion (fsp + 0x190#64) 8 ∗
        ((fsp + 0x198#64) ↦₆₄ regCap) ∗ ((fsp + 0x1a0#64) ↦₆₄ regPtr) ∗
        memRegion (fsp + 0x1a8#64) 16)
      Q Qp oom :=
  ReadRegSpkPlacedBudgetAux.r1b_err_11b4_placed hh hdrop hbnd hc hx23 hx27 hfit henv hpanic hrej

theorem r1b_err_0df0_placed [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {st : M.σ}
    {EnvAt : StoresGhost → RejectKind → M.σ → Prop}
    {H : LibsignalHooks} {B : RunBudgets}
    {g : RunCall} {d : Init1Data} {s0 s : State} {resStack : Nat}
    {regCap regPtr : BitVec 64} {regBs : List (BitVec 8)}
    {Q Qp : State → SepProp → Prop} {oom : State → SepProp}
    (hh : RunHooksPlaced A lim H)
    (hdrop : DropSpeOwnedOkAtBlock (runProgPlaced H) A lim)
    (hbnd : r1b_StackBounds B resStack)
    (hc : r1b_ErrCtxPlaced r1b_CodeOk g d s0 s 0x0df0)
    (hfit : FitsEvents M lim st [AllocEvent.alloc 14])
    (henv : ∀ evsFree, FreeOnlyEvs evsFree →
      EnvAt StoresGhost.opened .postDispatch (M.stepEvents ([AllocEvent.alloc 14] ++ evsFree) st))
    (hpanic : PanicK g s0 Qp)
    (hrej : RejectKPlacedEnv r1b_CodeOk H A lim EnvAt g s0 resStack Q Qp oom) :
    let fsp := runFsp s0
    SepWPp (runProgPlaced H) (s0.readReg64 .lr) s
      (ownedBytes A.repAlloc regCap regPtr (BitVec.ofNat 64 regBs.length) regBs ∗
        r1b_errCommon (A.atState lim st s) g d s0 resStack ∗
        memRegion (fsp + 0x110#64) 8 ∗ memRegion (fsp + 0x11c#64) 4 ∗
        memRegion (fsp + 0x120#64) 16 ∗ memRegion (fsp + 0x150#64) 16 ∗
        memRegion (fsp + 0x168#64) 24 ∗ memRegion (fsp + 0x188#64) 16 ∗
        ((fsp + 0x198#64) ↦₆₄ regCap) ∗ ((fsp + 0x1a0#64) ↦₆₄ regPtr) ∗
        memRegion (fsp + 0x1a8#64) 16 ∗ memRegion (fsp + 0x4d0#64) 48)
      Q Qp oom :=
  ReadRegSpkPlacedBudgetAux.r1b_err_0df0_placed hh hdrop hbnd hc hfit henv hpanic hrej

private theorem r1b_err_0cec_placed [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {st : M.σ}
    {EnvAt : StoresGhost → RejectKind → M.σ → Prop}
    {H : LibsignalHooks} {B : RunBudgets}
    {g : RunCall} {d : Init1Data} {s0 s : State} {resStack : Nat}
    {buf d2 pCap : BitVec 64} {Q Qp : State → SepProp → Prop} {oom : State → SepProp}
    (hh : RunHooksPlaced A lim H)
    (hdrop : DropSpeOwnedOkAtBlock (runProgPlaced H) A lim)
    (hbnd : r1b_StackBounds B resStack)
    (hc : r1b_ErrCtxPlaced r1b_CodeOk g d s0 s 0x0cec) (hbuf : buf ≠ 0#64)
    (hx12 : s.readReg64 (.gpr 12#5) = speWord 1)
    (_hx25 : s.readReg64 (.gpr 25#5) = 22#64)
    (henv : ∀ evsFree, FreeOnlyEvs evsFree →
      EnvAt StoresGhost.opened .postDispatch (M.stepEvents evsFree st))
    (hpanic : PanicK g s0 Qp)
    (hrej : RejectKPlacedEnv r1b_CodeOk H A lim EnvAt g s0 resStack Q Qp oom) :
    let fsp := runFsp s0
    SepWPp (runProgPlaced H) (s0.readReg64 .lr) s
      (A.repAlloc.live buf 22 1 ∗ memRegion buf 14 ∗ ((buf + 14#64) ↦₆₄ d2) ∗
        ((fsp + 0x4d0#64) ↦₆₄ pCap) ∗ memRegion (fsp + 0x4d8#64) 40 ∗
        r1b_errCommon (A.atState lim st s) g d s0 resStack ∗
        memRegion (fsp + 0x110#64) 8 ∗ memRegion (fsp + 0x11c#64) 4 ∗
        memRegion (fsp + 0x120#64) 16 ∗ memRegion (fsp + 0x150#64) 16 ∗
        memRegion (fsp + 0x168#64) 24 ∗ memRegion (fsp + 0x188#64) 16 ∗
        ((fsp + 0x198#64) ↦₆₄ 22#64) ∗ ((fsp + 0x1a0#64) ↦₆₄ buf) ∗
        memRegion (fsp + 0x1a8#64) 16)
      Q Qp oom := by
  intro fsp
  rw [r1b_errCommon_atState_eq]
  generalize herrCore : r1b_errCore A.repAlloc g d s0 = errCore
  have hst := hc.st; have hpc := hst.pc; have hrun := hst.run
  have hsp : s.sp = fsp := hst.sp
  have hal : fsp &&& 15#64 = 0#64 := r1b_fsp_align hst.sp hst.spAligned
  change s.pc = (blkPl_579).base + 0x0cec#64 at hpc
  apply r1b_seq_lscro_oom (mid := (blkPl_579).base + 0x2bf0#64) hst.inv
  dsimp only [runProgPlaced, lsProg_579]
  wp_steps
  apply SepWP.done (by simp only [wp_norm, arm64_norm, *]; try bv_omega)
    (by simp only [wp_norm, arm64_norm, *])
  refine r1b_bind_state_placed fun sm hsm hinv_m => ?_
  have hvm : VmPreserved s sm := by simp only [hsm, wp_norm, arm64_norm]
  rw [← A.pool_transport lim st s sm hvm]
  change SepWPp (runProgPlaced H) _ _ _ _ _ _
  have hc_m : r1b_ErrCtxPlaced r1b_CodeOk g d s0 sm 0x2bf0 := hc.of_step
    { pc := by simp only [hsm, wp_norm, arm64_norm]
      run := by simp only [hsm, wp_norm, arm64_norm, hst.run]
      sp := by simpa only [hsm, wp_norm, arm64_norm] using hst.sp
      fp := by simpa only [hsm, wp_norm, arm64_norm] using hst.fp
      inv := hinv_m
      vregs := by simpa only [calleeSavedVRegs, hsm, wp_norm, arm64_norm] using hst.vregs
      spAligned := hst.spAligned }
    (by simp only [hsm, wp_norm, arm64_norm]) (by simp only [hsm, wp_norm, arm64_norm])
    (by simp only [hsm, wp_norm, arm64_norm]) (by simp only [hsm, wp_norm, arm64_norm])
    (by simp only [hsm, wp_norm, arm64_norm])
  refine r1b_sepWPp_frame (by r1b_ac) (r1b_buf22_owned A.repAlloc buf d2 hbuf) (by r1b_ac) ?_
  simp only [sepExists_sepConj_left, sepConj_assoc]
  refine SepWPp.exists_elim fun eBs => r1b_sepWPp_pure_left fun _ => ?_
  have hcl := r1b_cleanup_2bf0_placed_env (st := st) hh hdrop hbnd hc_m hpanic hrej henv
  dsimp only at hcl
  rw [r1b_errCommon_atState_eq, herrCore] at hcl
  refine sepWPp_weaken_pre ?_ hcl
  have hpay : ownedBytes A.repAlloc 22#64 buf 22#64 eBs ⊢
      r1b_SpePayload A.repAlloc (sm.readReg64 (.gpr 12#5)) (sm.readReg64 (.gpr 9#5))
        (sm.readReg64 (.gpr 23#5)) (sm.readReg64 (.gpr 27#5))
        (sm.readReg64 (.gpr 16#5)) (sm.readReg64 (.gpr 14#5))
        (sm.readReg64 (.gpr 15#5)) (sm.readReg64 (.gpr 28#5))
        (sm.readReg64 (.gpr 22#5)) := by
    simp only [hsm, wp_norm, arm64_norm, hx12]; r1b_prove_spe_str
  have h4d0 : ((fsp + 0x4d0#64) ↦₆₄ pCap) ∗ memRegion (fsp + 0x4d8#64) 40 ⊢
      memRegion (fsp + 0x4d0#64) 48 := by
    simpa only [BitVec.add_assoc, BitVec.reduceAdd] using
      r1b_cell64_cons (a := fsp + 0x4d0#64) pCap (n := 40) (by decide)
  have h188 : memRegion (fsp + 0x188#64) 16 ∗ ((fsp + 0x198#64) ↦₆₄ 22#64) ∗
      ((fsp + 0x1a0#64) ↦₆₄ buf) ∗ memRegion (fsp + 0x1a8#64) 16 ⊢
      memRegion (fsp + 0x188#64) 48 := by
    rw [← sepConj_assoc ((fsp + 0x198#64) ↦₆₄ 22#64)]
    refine Entails.trans (sepConj_mono_right (sepConj_mono_left
      (by simpa only [BitVec.add_assoc, BitVec.reduceAdd] using
        r1b_cells2_to_region16 (fsp + 0x198#64) 22#64 buf))) ?_
    rw [r1b_join_region fsp 0x198 16 16, r1b_join_region fsp 0x188 16 32]; exact Entails.refl _
  exact r1b_entails_frame (by r1b_ac) (sepConj_mono hpay (sepConj_mono h4d0 h188)) (by r1b_ac)

set_option maxHeartbeats 400000 in
private theorem r1b_err_0c24_placed [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {st : M.σ}
    {EnvAt : StoresGhost → RejectKind → M.σ → Prop}
    {H : LibsignalHooks} {B : RunBudgets}
    {g : RunCall} {d : Init1Data} {s0 sf2 : State} {resStack : Nat}
    {buf pCap pPtr : BitVec 64} {pBs : List (BitVec 8)}
    {errCore : SepProp} {Q Qp : State → SepProp → Prop} {oom : State → SepProp}
    (hh : RunHooksPlaced A lim H)
    (hdrop : DropSpeOwnedOkAtBlock (runProgPlaced H) A lim)
    (hbnd : r1b_StackBounds B resStack)
    (herrCore : r1b_errCore A.repAlloc g d s0 = errCore)
    (hc2 : r1b_ErrCtxPlaced r1b_CodeOk g d s0 sf2 0x0c24)
    (hx0_buf : sf2.readReg64 .x0 = buf) (hbuf : buf ≠ 0#64)
    (hx23_2 : sf2.readReg64 (.gpr 23#5) = 0xffffffffffffffff#64)
    (hx27_2 : sf2.readReg64 (.gpr 27#5) = pPtr)
    (henv : ∀ evsFree, FreeOnlyEvs evsFree →
      EnvAt StoresGhost.opened .postDispatch (M.stepEvents evsFree st))
    (hpanic : PanicK g s0 Qp)
    (hrej : RejectKPlacedEnv r1b_CodeOk H A lim EnvAt g s0 resStack Q Qp oom) :
    let fsp := runFsp s0
    SepWPp (runProgPlaced H) (s0.readReg64 .lr) sf2
      (A.repAlloc.live buf 22 1 ∗ memRegion buf 22 ∗
        stackAt fsp (resStack - runFrame) ∗ A.pool lim st sf2 ∗
        ((fsp + 0x4d0#64) ↦₆₄ pCap) ∗ memRegion (fsp + 0x4d8#64) 40 ∗
        ownedBytes A.repAlloc pCap pPtr (BitVec.ofNat 64 pBs.length) pBs ∗
        errCore ∗ anyHeap ∗
        memRegion (fsp + 0x110#64) 8 ∗ memRegion (fsp + 0x11c#64) 4 ∗
        memRegion (fsp + 0x120#64) 16 ∗ memRegion (fsp + 0x150#64) 16 ∗
        memRegion (fsp + 0x168#64) 24 ∗ memRegion (fsp + 0x188#64) 16 ∗
        memRegion (fsp + 0x198#64) 16 ∗ memRegion (fsp + 0x1a8#64) 16)
      Q Qp oom := by
  intro fsp
  have hin2 := hc2.st
  have hbuf_f : (buf == 0#64) = false := beq_false_of_ne hbuf
  have hal : fsp &&& 15#64 = 0#64 := r1b_fsp_align hin2.sp hin2.spAligned
  have hpc2_in := hin2.pc; change sf2.pc = (blkPl_579).base + 0x0c24#64 at hpc2_in
  have hrun2_in := hin2.run
  apply r1b_seq_lscro_oom (mid := (blkPl_579).base + 0x0c30#64) hin2.inv
  dsimp only [runProgPlaced, lsProg_579]
  wp_steps
  apply SepWP.done (by simp only [wp_norm, arm64_norm, *]; try bv_omega)
    (by simp only [wp_norm, arm64_norm, *])
  refine r1b_bind_state_placed fun sm_a hsm_a hinv_a => by
    have hvm_a : VmPreserved sf2 sm_a := by simp only [hsm_a, wp_norm, arm64_norm]
    rw [← A.pool_transport lim st sf2 sm_a hvm_a]
    change SepWPp (runProgPlaced H) _ _ _ _ _ _
    have hin2 : InRunPlaced r1b_CodeOk s0 sm_a 0x0c30 :=
      { pc := by simp only [hsm_a, wp_norm, arm64_norm]
        run := by simp only [hsm_a, wp_norm, arm64_norm, hin2.run]
        sp := by simpa only [hsm_a, wp_norm, arm64_norm] using hin2.sp
        fp := by simpa only [hsm_a, wp_norm, arm64_norm] using hin2.fp
        inv := hinv_a
        vregs := by simpa only [calleeSavedVRegs, hsm_a, wp_norm, arm64_norm] using hin2.vregs
        spAligned := hin2.spAligned }
    have hc2 : r1b_ErrCtxPlaced r1b_CodeOk g d s0 sm_a 0x0c30 := hc2.of_step hin2
      (by simp only [hsm_a, wp_norm, arm64_norm]) (by simp only [hsm_a, wp_norm, arm64_norm])
      (by simp only [hsm_a, wp_norm, arm64_norm]) (by simp only [hsm_a, wp_norm, arm64_norm])
      (by simp only [hsm_a, wp_norm, arm64_norm])
    have hx0_buf : sm_a.readReg64 .x0 = buf := by
      simpa only [hsm_a, wp_norm, arm64_norm] using hx0_buf
    have hx23_2 : sm_a.readReg64 (.gpr 23#5) = 0xffffffffffffffff#64 := by
      simpa only [hsm_a, wp_norm, arm64_norm] using hx23_2
    have hx27_2 : sm_a.readReg64 (.gpr 27#5) = pPtr := by
      simpa only [hsm_a, wp_norm, arm64_norm] using hx27_2
    have hx8_ro : sm_a.readReg64 (.gpr 8#5) = lsρ r1b_unreadSym := by
      simp only [hsm_a, wp_norm, arm64_norm]
    refine r1b_sepWPp_with_ro_placed hin2.inv r1b_ro_unreadable_placed ?_
    obtain ⟨ro0, ro1, ro2, roRem, hroEq⟩ := r1b_ro_split22 (sm_a.readReg64 (.gpr 8#5))
    conv at hroEq => lhs; rw [hx8_ro]
    clear hsm_a hx8_ro
    have h198 := r1b_region16_to_cells (fsp + 0x198#64)
    have ha1a0 : (fsp + 0x198#64) + 8#64 = fsp + 0x1a0#64 := by bv_omega
    rw [ha1a0] at h198
    rw [hroEq, r1b_buf22_split1 buf, h198]
    simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
    refine SepWPp.exists_elim fun d0 => SepWPp.exists_elim fun d1 =>
      SepWPp.exists_elim fun v198 => SepWPp.exists_elim fun v1a0 => ?_
    have hpc2 := hin2.pc; change sm_a.pc = (blkPl_579).base + 0x0c30#64 at hpc2
    have hrun2 := hin2.run; have hsp2 : sm_a.sp = fsp := hin2.sp
    apply r1b_seq_lscro_oom (mid := (blkPl_579).base + 0x0c44#64) hin2.inv
    dsimp only [runProgPlaced, lsProg_579]
    by_vm_open (
      wp_steps
      refine SepWP.done (by simp only [wp_norm, arm64_norm, *]; try bv_omega)
        (by simp only [wp_norm, arm64_norm, *])
        ⟨by simp only [wp_norm, arm64_norm, *], fun hvm3 => ?_⟩
      refine r1b_bind_state_placed fun sm3 hsm3 hinv3 => ?_
      rw [← hsm3] at hvm3
      rw [← A.pool_transport lim st sm_a sm3 hvm3]
      change SepWPp (runProgPlaced H) _ _ _ _ _ _
      refine r1b_sepWPp_drop_left <| r1b_sepWPp_drop_left <|
        r1b_sepWPp_drop_left <| r1b_sepWPp_drop_left ?_
      refine r1b_sepWPp_frame (by r1b_ac) (r1b_buf22_realign buf _ _) (by r1b_ac) ?_
      simp only [sepExists_sepConj_left, sepConj_assoc]
      refine SepWPp.exists_elim fun d2 => ?_
      by_cases hpCap : pCap = 0#64
      · subst hpCap
        have hpc : sm3.pc = (blkPl_579).base + 0x0c44#64 := by
          simp only [hsm3, wp_norm, arm64_norm]
        have hrun : sm3.status = .Running := by
          simp only [hsm3, wp_norm, arm64_norm, hin2.run]
        have hsp : sm3.sp = fsp := by simpa only [hsm3, wp_norm, arm64_norm] using hin2.sp
        have hr0 : sm3.readReg64 .x0 = buf := by simpa only [hsm3, wp_norm, arm64_norm] using hx0_buf
        have hr23 : sm3.readReg64 (.gpr 23#5) = 0xffffffffffffffff#64 := by
          simpa only [hsm3, wp_norm, arm64_norm] using hx23_2
        apply r1b_seq_lscro_oom (mid := (blkPl_579).base + 0x0cec#64) hinv3
        dsimp only [runProgPlaced, lsProg_579]
        by_vm_open (
          wp_steps
          refine SepWP.done (by simp only [wp_norm, arm64_norm, *]; try bv_omega)
            (by simp only [wp_norm, arm64_norm, *])
            ⟨by simp only [wp_norm, arm64_norm, *], fun hvm4 => ?_⟩
          refine r1b_bind_state_placed fun sm4 hsm4 hinv4 => ?_
          rw [← hsm4] at hvm4
          rw [← A.pool_transport lim st sm3 sm4 hvm4]
          change SepWPp (runProgPlaced H) _ _ _ _ _ _
          have hc4 : r1b_ErrCtxPlaced r1b_CodeOk g d s0 sm4 0x0cec := hc2.of_step
            { pc := by simp only [hsm4, wp_norm, arm64_norm]
              run := by simp only [hsm4, wp_norm, arm64_norm, hin2.run]
              sp := by simpa only [hsm4, wp_norm, arm64_norm] using hin2.sp
              fp := by simpa only [hsm4, wp_norm, arm64_norm] using hin2.fp
              inv := hinv4
              vregs := by simpa only [calleeSavedVRegs, hsm4, wp_norm, arm64_norm] using hin2.vregs
              spAligned := hin2.spAligned }
            (by simp only [hsm4, wp_norm, arm64_norm]) (by simp only [hsm4, wp_norm, arm64_norm])
            (by simp only [hsm4, wp_norm, arm64_norm]) (by simp only [hsm4, wp_norm, arm64_norm])
            (by simp only [hsm4, wp_norm, arm64_norm])
          refine r1b_sepWPp_frame (by r1b_ac)
            (r1b_ownedBytes_zero A.repAlloc pPtr (BitVec.ofNat 64 pBs.length) pBs)
            (by simp only [emp_sepConj]) ?_
          have hcl := r1b_err_0cec_placed (st := st) (d2 := ro2) (pCap := 0#64)
            hh hdrop hbnd hc4 hbuf
            (by simp only [hsm4, wp_norm, arm64_norm, speWord])
            (by simp only [hsm4, wp_norm, arm64_norm])
            henv hpanic hrej
          dsimp only at hcl
          rw [r1b_errCommon_atState_eq, herrCore] at hcl
          refine sepWPp_weaken_pre ?_ hcl
          (try dsimp +zetaDelta only)
          generalize runFsp s0 = fsp0; exact Entails.of_eq (by r1b_ac)
        )
      · have hpCap_f : (pCap == 0#64) = false := beq_false_of_ne hpCap
        have hpc : sm3.pc = (blkPl_579).base + 0x0c44#64 := by
          simp only [hsm3, wp_norm, arm64_norm]
        have hrun : sm3.status = .Running := by
          simp only [hsm3, wp_norm, arm64_norm, hin2.run]
        have hsp : sm3.sp = fsp := by simpa only [hsm3, wp_norm, arm64_norm] using hin2.sp
        have hr0 : sm3.readReg64 .x0 = buf := by simpa only [hsm3, wp_norm, arm64_norm] using hx0_buf
        apply r1b_seq_lscro_oom (mid := lsρ lsRustDeallocSymCli) hinv3
        dsimp only [runProgPlaced, lsProg_579]
        by_vm_open (
          wp_steps
          refine SepWP.done (by simp only [wp_norm, arm64_norm, *]; try bv_omega)
            (by simp only [wp_norm, arm64_norm, *])
            ⟨by simp only [wp_norm, arm64_norm, *], fun hvm4 => ?_⟩
          refine r1b_bind_state_placed fun sm4 hsm4 hinv4 => ?_
          rw [← hsm4] at hvm4
          rw [← A.pool_transport lim st sm3 sm4 hvm4]
          change SepWPp (runProgPlaced H) _ _ _ _ _ _
          have hx0_sm4 : sm4.readReg64 .x0 = pPtr := by simp only [hsm4, wp_norm, arm64_norm]
          refine r1b_call_frame <|
            r1b_call_dealloc_ownedBytes_placed (bs := pBs) hh hbnd hinv4
              (by simp only [hsm4, wp_norm, arm64_norm])
              (by simp only [hsm4, wp_norm, arm64_norm, hin2.run])
              (by simpa only [hsm4, wp_norm, arm64_norm] using hin2.sp)
              (by simpa only [hsm4, wp_norm, arm64_norm] using hin2.fp)
              (by simpa only [calleeSavedVRegs, hsm4, wp_norm, arm64_norm] using hin2.vregs)
              hin2.spAligned (retOff := 0x0c68)
              (by simp only [hsm4, wp_norm, arm64_norm]) hx0_sm4
              (by simp only [hsm4, wp_norm, arm64_norm]) (by simp only [hsm4, wp_norm, arm64_norm])
              hpCap hpanic fun sf4 hin4 hcs4 hfs4 htr4 => ?_
          have hc4 : r1b_ErrCtxPlaced r1b_CodeOk g d s0 sf4 0x0c68 := hc2.after_call
            (by simp only [hsm4, wp_norm, arm64_norm]) (by simp only [hsm4, wp_norm, arm64_norm])
            (by simp only [hsm4, wp_norm, arm64_norm]) (by simp only [hsm4, wp_norm, arm64_norm])
            (by simp only [hsm4, wp_norm, arm64_norm])
            hin4 hcs4 (congrArg FsState.files hfs4) htr4
          have hx23_4 : sf4.readReg64 (.gpr 23#5) = 0xffffffffffffffff#64 :=
            hcs4.2.2.2.2.1.trans (by simpa only [hsm4, wp_norm, arm64_norm] using hx23_2)
          have hx25_4 : sf4.readReg64 (.gpr 25#5) = 22#64 :=
            hcs4.2.2.2.2.2.2.1.trans (by simp only [hsm4, wp_norm, arm64_norm])
          have hx27_4 : sf4.readReg64 (.gpr 27#5) = speWord 1 :=
            hcs4.2.2.2.2.2.2.2.2.1.trans (by simp only [hsm4, wp_norm, arm64_norm, speWord])
          have hpc4 := hin4.pc; change sf4.pc = (blkPl_579).base + 0x0c68#64 at hpc4
          have hrun4 := hin4.run
          apply r1b_seq_lscro_oom (mid := (blkPl_579).base + 0x0cec#64) hin4.inv
          dsimp only [runProgPlaced, lsProg_579]
          by_vm_open (
            wp_steps
            refine SepWP.done (by simp only [wp_norm, arm64_norm, *]; try bv_omega)
              (by simp only [wp_norm, arm64_norm, *])
              ⟨by simp only [wp_norm, arm64_norm, *], fun hvm5 => ?_⟩
            refine r1b_bind_state_placed fun sm5 hsm5 hinv5 => ?_
            rw [← hsm5] at hvm5
            rw [← A.pool_transport lim (M.stepEvents (rustDeallocEvents pCap.toNat 1) st) sf4 sm5 hvm5]
            change SepWPp (runProgPlaced H) _ _ _ _ _ _
            have hc5 : r1b_ErrCtxPlaced r1b_CodeOk g d s0 sm5 0x0cec := hc4.of_step
              { pc := by simp only [hsm5, wp_norm, arm64_norm]
                run := by simp only [hsm5, wp_norm, arm64_norm, hin4.run]
                sp := by simpa only [hsm5, wp_norm, arm64_norm] using hin4.sp
                fp := by simpa only [hsm5, wp_norm, arm64_norm] using hin4.fp
                inv := hinv5
                vregs := by simpa only [calleeSavedVRegs, hsm5, wp_norm, arm64_norm] using hin4.vregs
                spAligned := hin2.spAligned }
              (by simp only [hsm5, wp_norm, arm64_norm]) (by simp only [hsm5, wp_norm, arm64_norm])
              (by simp only [hsm5, wp_norm, arm64_norm]) (by simp only [hsm5, wp_norm, arm64_norm])
              (by simp only [hsm5, wp_norm, arm64_norm])
            have hcl := r1b_err_0cec_placed
              (st := M.stepEvents (rustDeallocEvents pCap.toNat 1) st)
              (d2 := ro2) (pCap := pCap) hh hdrop hbnd hc5 hbuf
              (by simp only [hsm5, wp_norm, arm64_norm, speWord])
              (by simpa only [hsm5, wp_norm, arm64_norm] using hx25_4)
              (fun evsFree hfo => by
                rw [← M.stepEvents_append]
                exact henv _ (freeOnlyEvs_rustDealloc_append pCap.toNat hfo))
              hpanic hrej
            dsimp only at hcl
            rw [r1b_errCommon_atState_eq, herrCore] at hcl
            refine sepWPp_weaken_pre ?_ hcl
            (try dsimp +zetaDelta only)
            generalize runFsp s0 = fsp0; exact Entails.of_eq (by r1b_ac)
          )
        )
    )

theorem r1b_err_0c14_placed [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {st : M.σ}
    {EnvAt : StoresGhost → RejectKind → M.σ → Prop}
    {H : LibsignalHooks} {B : RunBudgets}
    {g : RunCall} {d : Init1Data} {s0 s : State} {resStack : Nat}
    {pCap pPtr : BitVec 64} {pBs : List (BitVec 8)}
    {Q Qp : State → SepProp → Prop} {oom : State → SepProp}
    (hh : RunHooksPlaced A lim H)
    (hdrop : DropSpeOwnedOkAtBlock (runProgPlaced H) A lim)
    (hbnd : r1b_StackBounds B resStack)
    (hc : r1b_ErrCtxPlaced r1b_CodeOk g d s0 s 0x0c14)
    (hx23 : s.readReg64 (.gpr 23#5) = 0xffffffffffffffff#64)
    (hx27 : s.readReg64 (.gpr 27#5) = pPtr)
    (hfit : FitsEvents M lim st [AllocEvent.alloc 22])
    (henv : ∀ evsFree, FreeOnlyEvs evsFree →
      EnvAt StoresGhost.opened .postDispatch (M.stepEvents ([AllocEvent.alloc 22] ++ evsFree) st))
    (hpanic : PanicK g s0 Qp)
    (hrej : RejectKPlacedEnv r1b_CodeOk H A lim EnvAt g s0 resStack Q Qp oom) :
    let fsp := runFsp s0
    SepWPp (runProgPlaced H) (s0.readReg64 .lr) s
      (((fsp + 0x4d0#64) ↦₆₄ pCap) ∗ memRegion (fsp + 0x4d8#64) 40 ∗
        ownedBytes A.repAlloc pCap pPtr (BitVec.ofNat 64 pBs.length) pBs ∗
        r1b_errCommon (A.atState lim st s) g d s0 resStack ∗
        memRegion (fsp + 0x110#64) 8 ∗ memRegion (fsp + 0x11c#64) 4 ∗
        memRegion (fsp + 0x120#64) 16 ∗ memRegion (fsp + 0x150#64) 16 ∗
        memRegion (fsp + 0x168#64) 24 ∗ memRegion (fsp + 0x188#64) 16 ∗
        memRegion (fsp + 0x198#64) 16 ∗ memRegion (fsp + 0x1a8#64) 16)
      Q Qp oom := by
  intro fsp
  rw [r1b_errCommon_atState_eq]
  generalize herrCore : r1b_errCore A.repAlloc g d s0 = errCore
  have hst := hc.st; have hpc := hst.pc; have hrun := hst.run
  change s.pc = (blkPl_579).base + 0x0c14#64 at hpc
  apply r1b_seq_lscro_oom (mid := lsρ lsRustNoAllocShimSymCli) hst.inv
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
      r1b_call_shim_pool_placed (g := g) hh hbnd hinv1
        (by simp only [hsm1, wp_norm, arm64_norm])
        (by simp only [hsm1, wp_norm, arm64_norm, hst.run])
        (by simpa only [hsm1, wp_norm, arm64_norm] using hst.sp)
        (by simpa only [hsm1, wp_norm, arm64_norm] using hst.fp)
        (by simpa only [calleeSavedVRegs, hsm1, wp_norm, arm64_norm] using hst.vregs)
        hst.spAligned (retOff := 0x0c18)
        (by simp only [hsm1, wp_norm, arm64_norm])
        hpanic fun sf1 hin1 hcs1 htr_fs1 htr1 => ?_
    have hc1 : r1b_ErrCtxPlaced r1b_CodeOk g d s0 sf1 0x0c18 := hc.after_call
      (by simp only [hsm1, wp_norm, arm64_norm]) (by simp only [hsm1, wp_norm, arm64_norm])
      (by simp only [hsm1, wp_norm, arm64_norm]) (by simp only [hsm1, wp_norm, arm64_norm])
      (by simp only [hsm1, wp_norm, arm64_norm])
      hin1 hcs1 (congrArg FsState.files htr_fs1) htr1
    have hx23_1 : sf1.readReg64 (.gpr 23#5) = 0xffffffffffffffff#64 :=
      hcs1.2.2.2.2.1.trans (by simpa only [hsm1, wp_norm, arm64_norm] using hx23)
    have hx27_1 : sf1.readReg64 (.gpr 27#5) = pPtr :=
      hcs1.2.2.2.2.2.2.2.2.1.trans (by simpa only [hsm1, wp_norm, arm64_norm] using hx27)
    have hpc1 := hin1.pc; change sf1.pc = (blkPl_579).base + 0x0c18#64 at hpc1
    have hrun1 := hin1.run
    apply r1b_seq_lscro_oom (mid := lsρ lsRustAllocSymCli) hin1.inv
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
      have haev : rustAllocEvents 22 1 = [AllocEvent.alloc 22] := rfl
      refine r1b_call_frame <|
        r1b_call_alloc_placed (size := 22) (align := 1) hh hbnd hinv2
          (by simp only [hsm2, wp_norm, arm64_norm])
          (by simp only [hsm2, wp_norm, arm64_norm, hin1.run])
          (by simpa only [hsm2, wp_norm, arm64_norm] using hin1.sp)
          (by simpa only [hsm2, wp_norm, arm64_norm] using hin1.fp)
          (by simpa only [calleeSavedVRegs, hsm2, wp_norm, arm64_norm] using hin1.vregs)
          hst.spAligned (retOff := 0x0c24)
          (by simp only [hsm2, wp_norm, arm64_norm])
          (by simp only [hsm2, wp_norm, arm64_norm]) (by simp only [hsm2, wp_norm, arm64_norm])
          (by decide) (r1b_layout1 22) (by decide) (haev ▸ hfit) hpanic
          fun sf2 buf hin2 hcs2 hx0_buf hbuf _hmod hfs2 htr2 => ?_
      have hlive_eq : A.live buf 22 1 = A.repAlloc.live buf 22 1 := rfl
      rw [hlive_eq, haev]
      have hc2 : r1b_ErrCtxPlaced r1b_CodeOk g d s0 sf2 0x0c24 := hc1.after_call
        (by simp only [hsm2, wp_norm, arm64_norm]) (by simp only [hsm2, wp_norm, arm64_norm])
        (by simp only [hsm2, wp_norm, arm64_norm]) (by simp only [hsm2, wp_norm, arm64_norm])
        (by simp only [hsm2, wp_norm, arm64_norm])
        hin2 hcs2 (congrArg FsState.files hfs2) htr2
      have hx23_2 : sf2.readReg64 (.gpr 23#5) = 0xffffffffffffffff#64 :=
        hcs2.2.2.2.2.1.trans (by simpa only [hsm2, wp_norm, arm64_norm] using hx23_1)
      have hx27_2 : sf2.readReg64 (.gpr 27#5) = pPtr :=
        hcs2.2.2.2.2.2.2.2.2.1.trans (by simpa only [hsm2, wp_norm, arm64_norm] using hx27_1)
      exact sepWPp_weaken_pre (Entails.of_eq (by r1b_ac))
        (r1b_err_0c24_placed (st := M.stepEvents [AllocEvent.alloc 22] st)
          hh hdrop hbnd herrCore hc2 hx0_buf hbuf hx23_2 hx27_2
          (fun evsFree hfo => by
            rw [← M.stepEvents_append]
            exact henv evsFree hfo)
          hpanic hrej)
    )
  )

/-! ## `split_signed` Step (`0x1230 → 0x1260`) -/

set_option maxHeartbeats 800000 in
private theorem r1b_after_spk_dealloc_err_placed [LibsignalPlacement] {M : AllocCostModel}
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
  have hpc1 := hin1.pc; change sf1.pc = (blkPl_579).base + 0x1248#64 at hpc1
  have hrun1 := hin1.run; have hsp1 : sf1.sp = fsp := hin1.sp
  apply r1b_seq_lscro_oom (mid := (blkPl_579).base + 0x13bc#64) hin1.inv
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
theorem r1b_after_spk_dealloc_placed [LibsignalPlacement] {M : AllocCostModel}
    {S : RunSem} {A : RustCliAllocBudget M} {lim : BudgetLimits} {st : M.σ}
    {cEnvs : RunCalleesEnvs} {EnvAt : StoresGhost → RejectKind → M.σ → Prop}
    {H : LibsignalHooks} {B : RunBudgets} {σ : RunSlots}
    {g : RunCall} {d : Init1Data} {s0 s : State} {resStack : Nat}
    {r0 r1 r2 r3 : BitVec 8}
    {regCap regPtr spkCap spkPtr : BitVec 64} {spkBs : List (BitVec 8)}
    {Q Qp : State → SepProp → Prop} {oom : State → SepProp}
    (hh : RunHooksPlaced A lim H)
    (hc : RunCalleesPlaced A lim cEnvs H B σ)
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
  change s.pc = (blkPl_579).base + 0x1230#64 at hpc
  apply r1b_seq_lscro_oom (mid := lsmpl.base 592) hst.inv
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
      r1b_call_splitSigned_placed (g := g) (ret := fsp + 0x4d0#64) (fp := spkPtr) (file := spkBs)
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
        (fun sf1 evsSp spkId spkKey spkSig hevsSp hin1 hcs1 hsp_ok hfs1 htr1 => ?_)
    · have hok1 : r1b_OkCtxPlaced r1b_CodeOk S g d s0 sf1 0x1248 := hok.after_call
        (by simp only [hsm1, wp_norm, arm64_norm]) (by simp only [hsm1, wp_norm, arm64_norm])
        (by simp only [hsm1, wp_norm, arm64_norm]) (by simp only [hsm1, wp_norm, arm64_norm])
        (by simp only [hsm1, wp_norm, arm64_norm]) (by simp only [hsm1, wp_norm, arm64_norm])
        hin1 hcs1 hfs1 htr1
      have hc1 : r1b_ErrCtxPlaced r1b_CodeOk g d s0 sf1 0x1248 :=
        hok1.to_err (r1b_none_spk_split hspk_rd hsp_none)
      have hcl := r1b_after_spk_dealloc_err_placed (st := M.stepEvents evsSp st)
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
      have hpc1 := hin1.pc; change sf1.pc = (blkPl_579).base + 0x1248#64 at hpc1
      have hrun1 := hin1.run; have hsp1 : sf1.sp = fsp := hin1.sp
      apply r1b_seq_lscro_oom (mid := (blkPl_579).base + 0x1260#64) hin1.inv
      dsimp only [runProgPlaced, lsProg_579]
      by_vm_open (
        wp_steps
        refine SepWP.done (by simp only [wp_norm, arm64_norm, *]; try bv_omega)
          (by simp only [wp_norm, arm64_norm, *])
          ⟨by simp only [wp_norm, arm64_norm, *], fun hvm2 => ?_⟩
        refine r1b_bind_state_placed fun sm2 hsm2 hinv2 => ?_
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

end LibsignalBinary.Proofs.SignalSession.Cli.Run.Compose.Arms.R1b.ReadRegSpkPlacedBudget
