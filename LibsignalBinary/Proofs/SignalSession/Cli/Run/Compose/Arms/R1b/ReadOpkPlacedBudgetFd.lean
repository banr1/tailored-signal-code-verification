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
public import LibsignalBinary.Proofs.SignalSession.Cli.F3.HRead.FdThreadKit
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Compose.Arms.R1b.ErrCleanupUpperPlacedBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Compose.Arms.R1b.ReadKpkPlaced
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Compose.Arms.R1b.ReadKpkPlacedBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Compose.Arms.R1b.ReadOpkPlaced
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Compose.Arms.R1b.ReadOpkPlacedBudget
import Arm64.Trusted.Spec.Hoare
import Arm64.Trusted.Spec.SepLogic
import LibsignalBinary.Proofs.Common.SharedHelpers
meta import LibsignalBinary.Proofs.Common.SharedHelpers -- shake: keep
import LibsignalBinary.Proofs.SignalSession.Cli.Main.Proofs.M4Layout

/-!
# `State.fs`-Preserving Stage 3 Copy and Free (`0x2490 → 0x24dc → 0x24ec`) for Arm `R1b`

Proves `r1b_opk_free_24dc_placed_fd` (`0x24dc → 0x24ec`) and `r1b_opk_copy1_2490_placed_fd`
(`0x2490 → 0x24dc → 0x24ec`), preserving `sf.fs = s.fs` on Block `579`.
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 200000
set_option linter.unreachableTactic false
set_option linter.unusedTactic false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

namespace LibsignalBinary.Proofs.SignalSession.Cli.Run.Compose.Arms.R1b.ReadOpkPlacedBudgetFd

open Arm64 Arm64.Process ProofLib ProofLib.ProgramReflection SepProp
open CryptoVerification (LibsignalHooks LibsignalPlacement lsLogFilterAddr lsρ)
open CryptoVerification.LibsignalTripleRatchet.Wire
  (pkLayoutAt pkLayoutAt_entails_memRegion32 pkRestAt
   sevenBytesHeadAt sevenBytesHeadAt_eq_tailAt sevenBytesTailAt)
open CryptoVerification.SignalSession (lsRustDeallocSymCli)
open CryptoVerification.SignalSession.Cli (ofLe32)
open CryptoVerification.SignalSession.Cli.MainHops (RunCall ownedBytes sepWPp_weaken_pre)
open CryptoVerification.SignalSession.Cli.Run.Placed
  (blkLib_eq_579 blkPC_579 blkPl_579 lsProg_579)
open CryptoVerification.SignalSession.Cli.RunCompose
  (Init1Data PanicK RunSem r1b_CodeOk r1b_OkCtxPlaced r1b_StackBounds r1b_bind_state_placed
   r1b_cell8_to_region r1b_entails_frame_core r1b_fsp_align r1b_invCoreBase_placed
   r1b_join_region r1b_opkStage1At r1b_ownedBytes_cap0_emp r1b_sepWPp_frame_core
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
open LibsignalBinary.Proofs.SignalSession.Cli.Run.SkeletonPlacedBudget (RunHooksPlaced)

attribute [local irreducible] Program.fetch Program.externAt?
attribute [local simp, local arm64_norm, local wp_norm] runPcPlaced_eq BitVec.ofNat_eq_ofNat

local macro (priority := high) "r1b_ac" : tactic =>
  `(tactic| ((try dsimp +zetaDelta only) <;> first | rfl | simp only [emp_sepConj] | sep_ac_rfl))

private meta def r1bStripLetsRO : Nat → Lean.Expr → Lean.Expr
  | 0, e => e
  | n + 1, .letE _ _ v b _ => r1bStripLetsRO n (b.instantiate1 v)
  | n + 1, .mdata _ e => r1bStripLetsRO n e
  | _, e => e

private meta def r1bSplitSepRO : Nat → Lean.Expr → Lean.Expr → Array Lean.Expr
  | 0, _, e => #[e]
  | fuel + 1, sepSample, e =>
    let e := r1bStripLetsRO 64 e
    let fn := sepSample.getAppFn.constName!
    let ar := sepSample.getAppNumArgs
    if e.isAppOfArity fn ar then
      r1bSplitSepRO fuel sepSample (e.getArg! (ar - 2)) ++
        r1bSplitSepRO fuel sepSample (e.getArg! (ar - 1))
    else #[e]

private meta def r1bIsDefEqPureRO (x a : Lean.Expr) : Lean.Elab.TermElabM Bool := do
  let x := r1bStripLetsRO 64 x; let a := r1bStripLetsRO 64 a
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

private meta def r1bComputeRestRO (ctxName : String) (p a1 : Lean.Expr) :
    Lean.Elab.TermElabM Lean.Expr := do
  let sepTy := Lean.mkConst ``SepProp []
  let sepSample ← Lean.Elab.Term.elabTerm (← `(emp ∗ emp)) (some sepTy)
  let empExpr ← Lean.Elab.Term.elabTerm (← `(emp)) (some sepTy)
  let ps := (r1bSplitSepRO 64 sepSample (← Lean.instantiateMVars p)).toList
  let a1s := (r1bSplitSepRO 64 sepSample (← Lean.instantiateMVars a1)).toList
  let mut rem := ps
  for a in a1s do
    let mut removed := false
    let mut next : List Lean.Expr := []
    for x in rem do
      if !removed && (← r1bIsDefEqPureRO x a) then removed := true
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

local elab (priority := high) "r1b_entails_frame_ro " t1:term:arg h:term:arg t2:term:arg :
    term <= expectedType => do
  let exp ← Lean.instantiateMVars expectedType
  if exp.isMVar then Lean.Elab.Term.tryPostpone
  let entSample ← Lean.Elab.Term.elabTerm (← `(emp ⊢ emp)) none
  let ear := entSample.getAppNumArgs
  let expS := r1bStripLetsRO 64 exp
  let p := expS.getArg! (ear - 2)
  let q := expS.getArg! (ear - 1)
  if (← Lean.instantiateMVars p).isMVar then Lean.Elab.Term.tryPostpone
  if (← Lean.instantiateMVars q).isMVar then Lean.Elab.Term.tryPostpone
  let hExpr ← Lean.Elab.Term.elabTerm h none
  let hTy := r1bStripLetsRO 64 (← Lean.instantiateMVars (← Lean.Meta.inferType hExpr))
  let a1 := hTy.getArg! (ear - 2)
  let a2 := hTy.getArg! (ear - 1)
  let r ← r1bComputeRestRO "r1b_entails_frame" p a1
  let sepTy := Lean.mkConst ``SepProp []
  let empExpr ← Lean.Elab.Term.elabTerm (← `(emp)) (some sepTy)
  let sepSample ← Lean.Elab.Term.elabTerm (← `(emp ∗ emp)) (some sepTy)
  let sar := sepSample.getAppNumArgs
  let mkSep (x y : Lean.Expr) : Lean.Expr :=
    sepSample.withApp fun f args => Lean.mkAppN f (args.extract 0 (sar - 2) ++ #[x, y])
  let rIsEmp ← r1bIsDefEqPureRO r empExpr
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

local elab (priority := high) "r1b_sepWPp_frame_ro " t1:term:arg h:term:arg t2:term:arg hk:term:arg :
    term <= expectedType => do
  let exp ← Lean.instantiateMVars expectedType
  if exp.isMVar then Lean.Elab.Term.tryPostpone
  let expS := r1bStripLetsRO 64 exp
  let args := expS.getAppArgs
  let prog := args[0]!; let ret := args[1]!; let st := args[2]!; let p := args[3]!
  let q := args[4]!; let qp := args[5]!; let oom := args[6]!
  let entSample ← Lean.Elab.Term.elabTerm (← `(emp ⊢ emp)) none
  let ear := entSample.getAppNumArgs
  let hExpr ← Lean.Elab.Term.elabTerm h none
  let hTy := r1bStripLetsRO 64 (← Lean.instantiateMVars (← Lean.Meta.inferType hExpr))
  let a1 := hTy.getArg! (ear - 2)
  let a2 := hTy.getArg! (ear - 1)
  let r ← r1bComputeRestRO "r1b_sepWPp_frame" p a1
  let sepTy := Lean.mkConst ``SepProp []
  let empExpr ← Lean.Elab.Term.elabTerm (← `(emp)) (some sepTy)
  let sepSample ← Lean.Elab.Term.elabTerm (← `(emp ∗ emp)) (some sepTy)
  let sar := sepSample.getAppNumArgs
  let mkSep (x y : Lean.Expr) : Lean.Expr :=
    sepSample.withApp fun f args => Lean.mkAppN f (args.extract 0 (sar - 2) ++ #[x, y])
  let rIsEmp ← r1bIsDefEqPureRO r empExpr
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
    let a2IsEmp ← r1bIsDefEqPureRO a2 empExpr
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

local elab:10 (priority := high) "r1b_call_frame_ro" "<|" h:term:10 : term <= expectedType => do
  let exp ← Lean.instantiateMVars expectedType
  if exp.isMVar then Lean.Elab.Term.tryPostpone
  let expS := r1bStripLetsRO 64 exp
  let hExpr ← Lean.Elab.Term.elabTerm h none
  let hTy0 := r1bStripLetsRO 64 (← Lean.instantiateMVars (← Lean.Meta.inferType hExpr))
  for idx in [0, 1, 2, 4, 5, 6] do
    if !(← Lean.Meta.withReducibleAndInstances <| Lean.Meta.isDefEq (hTy0.getArg! idx) (expS.getArg! idx)) then
      discard <| Lean.Meta.isDefEq (hTy0.getArg! idx) (expS.getArg! idx)
  let p ← Lean.instantiateMVars (expS.getArg! 3)
  let p' ← Lean.instantiateMVars ((r1bStripLetsRO 64 (← Lean.instantiateMVars hTy0)).getArg! 3)
  let sepTy := Lean.mkConst ``SepProp []
  let sepSample ← Lean.Elab.Term.elabTerm (← `(emp ∗ emp)) (some sepTy)
  let empExpr ← Lean.Elab.Term.elabTerm (← `(emp)) (some sepTy)
  let sar := sepSample.getAppNumArgs
  let mkSep (x y : Lean.Expr) : Lean.Expr :=
    sepSample.withApp fun f args => Lean.mkAppN f (args.extract 0 (sar - 2) ++ #[x, y])
  let ps := (r1bSplitSepRO 64 sepSample p).toList
  let p's := (r1bSplitSepRO 64 sepSample p').toList
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
      if !removed && (← r1bIsDefEqPureRO x a) then removed := true
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

/-! ## Shared Free Merge (`0x24dc → 0x24ec`) and Unaligned Stack Copy (`0x2490 → 0x24dc`) -/

theorem r1b_opk_free_24dc_placed_fd [LibsignalPlacement] {M : AllocCostModel}
    {S : RunSem} {A : RustCliAllocBudget M} {lim : BudgetLimits} {st : M.σ}
    {H : LibsignalHooks} {B : RunBudgets}
    {g : RunCall} {d : Init1Data} {s0 s : State} {resStack : Nat}
    {r0 r1 r2 r3 : BitVec 8}
    {opkCap opkPtr kpkCap kpkPtr spkCap spkPtr regCap regPtr : BitVec 64}
    {opkBs kpkBs kpkKey kpkSig spkBs spkKey spkSig : List (BitVec 8)}
    {kpkId spkId v11c : BitVec 32}
    {b0 b1 b2 b3 b4 b5 b6 : BitVec 8}
    {w0e0 w0e4 w9 : BitVec 32} {w13 : BitVec 16} {w15 w23 : BitVec 64} {b31 : BitVec 8}
    {Q Qp : State → SepProp → Prop} {oom : State → SepProp}
    (hh : RunHooksPlaced A lim H)
    (hbnd : r1b_StackBounds B resStack)
    (hok : r1b_OkCtxPlaced r1b_CodeOk S g d s0 s 0x24dc)
    (hx1 : s.readReg64 .x1 = opkCap)
    (hx23 : s.readReg64 (.gpr 23#5) = kpkId.zeroExtend 64)
    (hx24 : s.readReg64 (.gpr 24#5) = runFsp s0 + 0x380#64)
    (hx25 : s.readReg64 (.gpr 25#5) = BitVec.ofNat 64 opkBs.length)
    (hx27 : s.readReg64 (.gpr 27#5) = BitVec.ofNat 64 spkKey.length)
    (hx28 : s.readReg64 (.gpr 28#5) = 64#64)
    (hpanic : PanicK g s0 Qp)
    (hk : ∀ (sf : State) (evs : List AllocEvent),
      FreeOnlyEvs evs →
      r1b_OkCtxPlaced r1b_CodeOk S g d s0 sf 0x24ec →
      sf.fs = s.fs →
      sf.readReg64 (.gpr 23#5) = kpkId.zeroExtend 64 →
      sf.readReg64 (.gpr 24#5) = runFsp s0 + 0x380#64 →
      sf.readReg64 (.gpr 25#5) = BitVec.ofNat 64 opkBs.length →
      sf.readReg64 (.gpr 27#5) = BitVec.ofNat 64 spkKey.length →
      sf.readReg64 (.gpr 28#5) = 64#64 →
      let fsp := runFsp s0
      SepWPp (runProgPlaced H) (s0.readReg64 .lr) sf
        (memRegion (fsp + 0x4d0#64) 48 ∗
          ownedBytes A.repAlloc kpkCap kpkPtr (BitVec.ofNat 64 kpkBs.length) kpkBs ∗
          ownedBytes A.repAlloc spkCap spkPtr (BitVec.ofNat 64 spkBs.length) spkBs ∗
          ownedBytes A.repAlloc regCap regPtr 4#64 [r0, r1, r2, r3] ∗
          r1b_invCoreBase_placed A.repAlloc g d s0 ∗ (lsLogFilterAddr ↦₆₄ 0#64) ∗
          ownedBytes A.repAlloc d.dirCap d.dirPtr (BitVec.ofNat 64 d.dir.length) d.dir ∗
          r1b_opkStage1At fsp b0 b1 b2 b3 b4 b5 b6 w0e0 w0e4 w9 w13 w15 w23 b31 ∗
          memRegion (fsp + 0x110#64) 8 ∗ ((fsp + 0x11c#64) ↦₃₂ v11c) ∗
          memRegion (fsp + 0x120#64) 8 ∗ ((fsp + 0x128#64) ↦₆₄ kpkPtr) ∗
          ((fsp + 0x130#64) ↦₆₄ (kpkPtr + 4#64 + BitVec.ofNat 64 kpkKey.length)) ∗
          ((fsp + 0x138#64) ↦₆₄ BitVec.ofNat 64 kpkKey.length) ∗
          ((fsp + 0x140#64) ↦₆₄ (kpkPtr + 4#64)) ∗
          ((fsp + 0x148#64) ↦₆₄ 64#64) ∗
          ((fsp + 0x150#64) ↦₆₄ kpkCap) ∗
          ((fsp + 0x158#64) ↦₆₄ (spkPtr + 4#64 + BitVec.ofNat 64 spkKey.length)) ∗
          ((fsp + 0x164#64) ↦₃₂ ofLe32 r0 r1 r2 r3) ∗
          ((fsp + 0x168#64) ↦₆₄ spkPtr) ∗ ((fsp + 0x170#64) ↦₆₄ spkCap) ∗
          ((fsp + 0x178#64) ↦₆₄ (spkPtr + 4#64)) ∗
          ((fsp + 0x188#64) ↦₆₄ spkId.zeroExtend 64) ∗ ((fsp + 0x190#64) ↦₆₄ d.ikW3) ∗
          ((fsp + 0x198#64) ↦₆₄ regCap) ∗ ((fsp + 0x1a0#64) ↦₆₄ regPtr) ∗
          ((fsp + 0x1a8#64) ↦₆₄ d.ikW1) ∗
          ((fsp + 0x1b0#64) ↦₃₂ d.peerV.device.zeroExtend 32) ∗
          memRegion (fsp + 0x1b4#64) 4 ∗ memRegion (fsp + 0x1750#64) 24 ∗
          stackAt fsp (resStack - runFrame) ∗ A.pool lim (M.stepEvents evs st) sf)
        Q Qp oom) :
    let fsp := runFsp s0
    SepWPp (runProgPlaced H) (s0.readReg64 .lr) s
      (ownedBytes A.repAlloc opkCap opkPtr (BitVec.ofNat 64 opkBs.length) opkBs ∗
        memRegion (fsp + 0x4d0#64) 48 ∗
        ownedBytes A.repAlloc kpkCap kpkPtr (BitVec.ofNat 64 kpkBs.length) kpkBs ∗
        ownedBytes A.repAlloc spkCap spkPtr (BitVec.ofNat 64 spkBs.length) spkBs ∗
        ownedBytes A.repAlloc regCap regPtr 4#64 [r0, r1, r2, r3] ∗
        r1b_invCoreBase_placed A.repAlloc g d s0 ∗ (lsLogFilterAddr ↦₆₄ 0#64) ∗
        ownedBytes A.repAlloc d.dirCap d.dirPtr (BitVec.ofNat 64 d.dir.length) d.dir ∗
        r1b_opkStage1At fsp b0 b1 b2 b3 b4 b5 b6 w0e0 w0e4 w9 w13 w15 w23 b31 ∗
        memRegion (fsp + 0x110#64) 8 ∗ ((fsp + 0x11c#64) ↦₃₂ v11c) ∗
        ((fsp + 0x120#64) ↦₆₄ opkPtr) ∗ ((fsp + 0x128#64) ↦₆₄ kpkPtr) ∗
        ((fsp + 0x130#64) ↦₆₄ (kpkPtr + 4#64 + BitVec.ofNat 64 kpkKey.length)) ∗
        ((fsp + 0x138#64) ↦₆₄ BitVec.ofNat 64 kpkKey.length) ∗
        ((fsp + 0x140#64) ↦₆₄ (kpkPtr + 4#64)) ∗
        ((fsp + 0x148#64) ↦₆₄ 64#64) ∗
        ((fsp + 0x150#64) ↦₆₄ kpkCap) ∗
        ((fsp + 0x158#64) ↦₆₄ (spkPtr + 4#64 + BitVec.ofNat 64 spkKey.length)) ∗
        ((fsp + 0x164#64) ↦₃₂ ofLe32 r0 r1 r2 r3) ∗
        ((fsp + 0x168#64) ↦₆₄ spkPtr) ∗ ((fsp + 0x170#64) ↦₆₄ spkCap) ∗
        ((fsp + 0x178#64) ↦₆₄ (spkPtr + 4#64)) ∗
        ((fsp + 0x188#64) ↦₆₄ spkId.zeroExtend 64) ∗ ((fsp + 0x190#64) ↦₆₄ d.ikW3) ∗
        ((fsp + 0x198#64) ↦₆₄ regCap) ∗ ((fsp + 0x1a0#64) ↦₆₄ regPtr) ∗
        ((fsp + 0x1a8#64) ↦₆₄ d.ikW1) ∗
        ((fsp + 0x1b0#64) ↦₃₂ d.peerV.device.zeroExtend 32) ∗
        memRegion (fsp + 0x1b4#64) 4 ∗ memRegion (fsp + 0x1750#64) 24 ∗
        stackAt fsp (resStack - runFrame) ∗ A.pool lim st s)
      Q Qp oom := by
  intro fsp
  let _ := hx1; let _ := hx23; let _ := hx24; let _ := hx25; let _ := hx27; let _ := hx28
  have hst := hok.st
  have hal : fsp &&& 15#64 = 0#64 := r1b_fsp_align hst.sp hst.spAligned
  have hpc_in := hst.pc; change s.pc = (blkPl_579).base + 9436#64 at hpc_in
  by_cases hcap : opkCap = 0#64
  · subst hcap
    have hpc := hpc_in; have hrun := hst.run; have hsp : s.sp = fsp := hst.sp
    apply r1b_seq_lscro_oom (mid := (blkPl_579).base + 9452#64) hst.inv
    dsimp only [runProgPlaced, lsProg_579]
    apply sepWP_seg_ls_vm (Q := (blkPC_579).rebase (blkPl_579).base (hooksException _))
      blkLib_eq_579 blk579_noSvc0 (mid := (blkPl_579).base + 9452#64)
    intro _m_strip; wp_steps
    refine SepWP.done (by simp only [wp_norm, arm64_norm, *]; try bv_omega)
      (by simp only [wp_norm, arm64_norm, *]) fun _m_real hnsp => ?_
    have hvmp : VmPreserved s _ :=
      hnsp.toVmPreserved (by simp only [wp_norm, arm64_norm, *])
    try simp only [State.setMem_setMem] at hvmp ⊢
    apply SepWP.done (by simp only [wp_norm, arm64_norm, *])
      (by simp only [wp_norm, arm64_norm, *])
    refine r1b_bind_state_placed fun sm hsm hinv_m => by
      have hvm : VmPreserved s sm := hsm ▸ hvmp
      have hfs_m : sm.fs = s.fs := by
        first
        | simp only [hsm, wp_norm, arm64_norm]
        | simpa only [← hsm, wp_norm, arm64_norm] using hnsp.2.2.2.2.2.2
      rw [← A.pool_transport lim st s sm hvm]
      change SepWPp (runProgPlaced H) _ _ _ _ _ _
      have hok_m : r1b_OkCtxPlaced r1b_CodeOk S g d s0 sm 0x24ec := hok.of_step
        { pc := by simp only [hsm, wp_norm, arm64_norm]
          run := by simp only [hsm, wp_norm, arm64_norm, hst.run]
          sp := by simpa only [hsm, wp_norm, arm64_norm] using hst.sp
          fp := by simpa only [hsm, wp_norm, arm64_norm] using hst.fp
          inv := hinv_m
          vregs := by simpa only [calleeSavedVRegs, hsm, wp_norm, arm64_norm] using hst.vregs
          spAligned := hst.spAligned }
        (by simp only [hsm, wp_norm, arm64_norm]) (by simp only [hsm, wp_norm, arm64_norm])
        (by simp only [hsm, wp_norm, arm64_norm]) (by simp only [hsm, wp_norm, arm64_norm])
        (by simp only [hsm, wp_norm, arm64_norm]) (by simp only [hsm, wp_norm, arm64_norm])
      have h120 : ((fsp + 0x120#64) ↦₆₄ opkPtr) ⊢ memRegion (fsp + 0x120#64) 8 :=
        pointsTo64_entails_memRegion _ _
      have hcap0 := r1b_ownedBytes_cap0_emp A.repAlloc opkPtr (BitVec.ofNat 64 opkBs.length) opkBs
      refine r1b_sepWPp_frame_ro (by r1b_ac) hcap0 (by r1b_ac) ?_
      have hstep0 : M.stepEvents [] st = st := rfl
      have hnext := hk sm [] FreeOnlyEvs.nil hok_m hfs_m
        (by solve | simp only [hsm, wp_norm, arm64_norm] | simpa only [hsm, wp_norm, arm64_norm] using hx23)
        (by solve | simp only [hsm, wp_norm, arm64_norm] | simpa only [hsm, wp_norm, arm64_norm] using hx24)
        (by solve | simp only [hsm, wp_norm, arm64_norm] | simpa only [hsm, wp_norm, arm64_norm] using hx25)
        (by solve | simp only [hsm, wp_norm, arm64_norm] | simpa only [hsm, wp_norm, arm64_norm] using hx27)
        (by solve | simp only [hsm, wp_norm, arm64_norm] | simpa only [hsm, wp_norm, arm64_norm] using hx28)
      dsimp only at hnext
      rw [hstep0] at hnext
      exact sepWPp_weaken_pre (r1b_entails_frame_ro (by r1b_ac) h120 (by r1b_ac)) hnext
  · have hbeq : (opkCap == 0#64) = false := beq_false_of_ne hcap
    have hpc := hpc_in; have hrun := hst.run; have hsp : s.sp = fsp := hst.sp
    apply r1b_seq_lscro_oom (mid := lsρ lsRustDeallocSymCli) hst.inv
    dsimp only [runProgPlaced, lsProg_579]
    apply sepWP_seg_ls_vm (Q := (blkPC_579).rebase (blkPl_579).base (hooksException _))
      blkLib_eq_579 blk579_noSvc0 (mid := lsρ lsRustDeallocSymCli)
    intro _m_strip; wp_steps
    refine SepWP.done (by simp only [wp_norm, arm64_norm, *]; try bv_omega)
      (by simp only [wp_norm, arm64_norm, *]) fun _m_real hnsp => ?_
    have hvmp : VmPreserved s _ :=
      hnsp.toVmPreserved (by simp only [wp_norm, arm64_norm, *])
    try simp only [State.setMem_setMem] at hvmp ⊢
    apply SepWP.done (by simp only [wp_norm, arm64_norm, *])
      (by simp only [wp_norm, arm64_norm, *])
    refine r1b_bind_state_placed fun sm hsm hinv_m => by
      have hvm : VmPreserved s sm := hsm ▸ hvmp
      have hfs_m : sm.fs = s.fs := by
        first
        | simp only [hsm, wp_norm, arm64_norm]
        | simpa only [← hsm, wp_norm, arm64_norm] using hnsp.2.2.2.2.2.2
      rw [← A.pool_transport lim st s sm hvm]
      change SepWPp (runProgPlaced H) _ _ _ _ _ _
      refine r1b_call_frame_ro <|
        r1b_call_dealloc_ownedBytes_placed (Q := Q) (Qp := Qp) (oom := oom)
          (cap := opkCap) (ptr := opkPtr)
          (len := BitVec.ofNat 64 opkBs.length) (bs := opkBs) hh hbnd hinv_m
          (by simp only [hsm, wp_norm, arm64_norm])
          (by simp only [hsm, wp_norm, arm64_norm, hst.run])
          (by simpa only [hsm, wp_norm, arm64_norm] using hst.sp)
          (by simpa only [hsm, wp_norm, arm64_norm] using hst.fp)
          (by simpa only [calleeSavedVRegs, hsm, wp_norm, arm64_norm] using hst.vregs)
          hst.spAligned (retOff := 0x24ec)
          (by simp only [hsm, wp_norm, arm64_norm])
          (by simp only [hsm, wp_norm, arm64_norm])
          (by solve | simp only [hsm, wp_norm, arm64_norm] | simpa only [hsm, wp_norm, arm64_norm] using hx1)
          (by simp only [hsm, wp_norm, arm64_norm])
          hcap hpanic fun sf hin_f hcs_f hfs_f htr_f => ?_
      have hok_f : r1b_OkCtxPlaced r1b_CodeOk S g d s0 sf 0x24ec := hok.after_call
        (by simp only [hsm, wp_norm, arm64_norm]) (by simp only [hsm, wp_norm, arm64_norm])
        (by simp only [hsm, wp_norm, arm64_norm]) (by simp only [hsm, wp_norm, arm64_norm])
        (by simp only [hsm, wp_norm, arm64_norm]) (by simp only [hsm, wp_norm, arm64_norm])
        hin_f hcs_f (congrArg FsState.files hfs_f) htr_f
      have h120 : ((fsp + 0x120#64) ↦₆₄ opkPtr) ⊢ memRegion (fsp + 0x120#64) 8 :=
        pointsTo64_entails_memRegion _ _
      exact sepWPp_weaken_pre
        (r1b_entails_frame_ro (by r1b_ac) h120 (by r1b_ac))
        (hk sf (rustDeallocEvents opkCap.toNat 1) (FreeOnlyEvs.singleton 1 opkCap.toNat) hok_f
          (hfs_f.trans hfs_m)
          (hcs_f.2.2.2.2.1.trans
            (by solve | simp only [hsm, wp_norm, arm64_norm] | simpa only [hsm, wp_norm, arm64_norm] using hx23))
          (hcs_f.2.2.2.2.2.1.trans
            (by solve | simp only [hsm, wp_norm, arm64_norm] | simpa only [hsm, wp_norm, arm64_norm] using hx24))
          (hcs_f.2.2.2.2.2.2.1.trans
            (by solve | simp only [hsm, wp_norm, arm64_norm] | simpa only [hsm, wp_norm, arm64_norm] using hx25))
          (hcs_f.2.2.2.2.2.2.2.2.1.trans
            (by solve | simp only [hsm, wp_norm, arm64_norm] | simpa only [hsm, wp_norm, arm64_norm] using hx27))
          (hcs_f.2.2.2.2.2.2.2.2.2.1.trans
            (by solve | simp only [hsm, wp_norm, arm64_norm] | simpa only [hsm, wp_norm, arm64_norm] using hx28)))

private theorem r1b_pk4d0_ok_to_region48_placed_fd (fsp : BitVec 64)
    (b0 b1 b2 b3 b4 b5 b6 b7 b8 : BitVec 8)
    (w9 : BitVec 32) (w13 : BitVec 16) (w15 w23 : BitVec 64) (b31 : BitVec 8) :
    ((fsp + 0x4d0#64) ↦₈ 0#8) ∗
      pkLayoutAt (fsp + 0x4d1#64) b0 b1 b2 b3 b4 b5 b6 b7 b8 w9 w13 w15 w23 b31 ∗
      memRegion (fsp + 0x4f1#64) 15 ⊢
      memRegion (fsp + 0x4d0#64) 48 := by
  refine Entails.trans (sepConj_mono (r1b_cell8_to_region _ _)
    (sepConj_mono_left (pkLayoutAt_entails_memRegion32 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _))) ?_
  rw [r1b_join_region fsp 0x4d1 32 15, r1b_join_region fsp 0x4d0 1 47]
  exact Entails.refl _

set_option maxHeartbeats 400000 in
theorem r1b_opk_copy1_2490_placed_fd [LibsignalPlacement] {M : AllocCostModel}
    {S : RunSem} {A : RustCliAllocBudget M} {lim : BudgetLimits} {st : M.σ}
    {H : LibsignalHooks} {B : RunBudgets}
    {g : RunCall} {d : Init1Data} {s0 s : State} {resStack : Nat}
    {r0 r1 r2 r3 : BitVec 8}
    {opkCap opkPtr kpkCap kpkPtr spkCap spkPtr regCap regPtr : BitVec 64}
    {opkBs kpkBs kpkKey kpkSig spkBs spkKey spkSig : List (BitVec 8)}
    {kpkId spkId opkId : BitVec 32}
    {b0 b1 b2 b3 b4 b5 b6 b7 b8 : BitVec 8}
    {w9 : BitVec 32} {w13 : BitVec 16} {w15 w23 : BitVec 64} {b31 : BitVec 8}
    {c0 c1 c2 c3 c4 c5 c6 : BitVec 8}
    {w0e0_in w0e4_in w9_in : BitVec 32} {w13_in : BitVec 16} {w15_in w23_in : BitVec 64}
    {b31_in : BitVec 8}
    {Q Qp : State → SepProp → Prop} {oom : State → SepProp}
    (hh : RunHooksPlaced A lim H)
    (hbnd : r1b_StackBounds B resStack)
    (hok : r1b_OkCtxPlaced r1b_CodeOk S g d s0 s 0x2490)
    (hx23 : s.readReg64 (.gpr 23#5) = kpkId.zeroExtend 64)
    (hx24 : s.readReg64 (.gpr 24#5) = runFsp s0 + 0x380#64)
    (hx25 : s.readReg64 (.gpr 25#5) = BitVec.ofNat 64 opkBs.length)
    (hx27 : s.readReg64 (.gpr 27#5) = BitVec.ofNat 64 spkKey.length)
    (hx28 : s.readReg64 (.gpr 28#5) = 64#64)
    (hpanic : PanicK g s0 Qp)
    (hk : ∀ (sf : State) (evs : List AllocEvent),
      FreeOnlyEvs evs →
      r1b_OkCtxPlaced r1b_CodeOk S g d s0 sf 0x24ec →
      sf.fs = s.fs →
      sf.readReg64 (.gpr 23#5) = kpkId.zeroExtend 64 →
      sf.readReg64 (.gpr 24#5) = runFsp s0 + 0x380#64 →
      sf.readReg64 (.gpr 25#5) = BitVec.ofNat 64 opkBs.length →
      sf.readReg64 (.gpr 27#5) = BitVec.ofNat 64 spkKey.length →
      sf.readReg64 (.gpr 28#5) = 64#64 →
      let fsp := runFsp s0
      SepWPp (runProgPlaced H) (s0.readReg64 .lr) sf
        (memRegion (fsp + 0x4d0#64) 48 ∗
          ownedBytes A.repAlloc kpkCap kpkPtr (BitVec.ofNat 64 kpkBs.length) kpkBs ∗
          ownedBytes A.repAlloc spkCap spkPtr (BitVec.ofNat 64 spkBs.length) spkBs ∗
          ownedBytes A.repAlloc regCap regPtr 4#64 [r0, r1, r2, r3] ∗
          r1b_invCoreBase_placed A.repAlloc g d s0 ∗ (lsLogFilterAddr ↦₆₄ 0#64) ∗
          ownedBytes A.repAlloc d.dirCap d.dirPtr (BitVec.ofNat 64 d.dir.length) d.dir ∗
          r1b_opkStage1At fsp b0 b1 b2 b3 b4 b5 b6
            (b8.zeroExtend 32) (b7.zeroExtend 32) w9 w13 w15 w23 b31 ∗
          memRegion (fsp + 0x110#64) 8 ∗ ((fsp + 0x11c#64) ↦₃₂ opkId) ∗
          memRegion (fsp + 0x120#64) 8 ∗ ((fsp + 0x128#64) ↦₆₄ kpkPtr) ∗
          ((fsp + 0x130#64) ↦₆₄ (kpkPtr + 4#64 + BitVec.ofNat 64 kpkKey.length)) ∗
          ((fsp + 0x138#64) ↦₆₄ BitVec.ofNat 64 kpkKey.length) ∗
          ((fsp + 0x140#64) ↦₆₄ (kpkPtr + 4#64)) ∗
          ((fsp + 0x148#64) ↦₆₄ 64#64) ∗
          ((fsp + 0x150#64) ↦₆₄ kpkCap) ∗
          ((fsp + 0x158#64) ↦₆₄ (spkPtr + 4#64 + BitVec.ofNat 64 spkKey.length)) ∗
          ((fsp + 0x164#64) ↦₃₂ ofLe32 r0 r1 r2 r3) ∗
          ((fsp + 0x168#64) ↦₆₄ spkPtr) ∗ ((fsp + 0x170#64) ↦₆₄ spkCap) ∗
          ((fsp + 0x178#64) ↦₆₄ (spkPtr + 4#64)) ∗
          ((fsp + 0x188#64) ↦₆₄ spkId.zeroExtend 64) ∗ ((fsp + 0x190#64) ↦₆₄ d.ikW3) ∗
          ((fsp + 0x198#64) ↦₆₄ regCap) ∗ ((fsp + 0x1a0#64) ↦₆₄ regPtr) ∗
          ((fsp + 0x1a8#64) ↦₆₄ d.ikW1) ∗
          ((fsp + 0x1b0#64) ↦₃₂ d.peerV.device.zeroExtend 32) ∗
          memRegion (fsp + 0x1b4#64) 4 ∗ memRegion (fsp + 0x1750#64) 24 ∗
          stackAt fsp (resStack - runFrame) ∗ A.pool lim (M.stepEvents evs st) sf)
        Q Qp oom) :
    let fsp := runFsp s0
    SepWPp (runProgPlaced H) (s0.readReg64 .lr) s
      (((fsp + 0x4d0#64) ↦₈ 0#8) ∗
        pkLayoutAt (fsp + 0x4d1#64) b0 b1 b2 b3 b4 b5 b6 b7 b8 w9 w13 w15 w23 b31 ∗
        memRegion (fsp + 0x4f1#64) 15 ∗
        ownedBytes A.repAlloc opkCap opkPtr (BitVec.ofNat 64 opkBs.length) opkBs ∗
        ownedBytes A.repAlloc kpkCap kpkPtr (BitVec.ofNat 64 kpkBs.length) kpkBs ∗
        ownedBytes A.repAlloc spkCap spkPtr (BitVec.ofNat 64 spkBs.length) spkBs ∗
        ownedBytes A.repAlloc regCap regPtr 4#64 [r0, r1, r2, r3] ∗
        r1b_invCoreBase_placed A.repAlloc g d s0 ∗ (lsLogFilterAddr ↦₆₄ 0#64) ∗
        ownedBytes A.repAlloc d.dirCap d.dirPtr (BitVec.ofNat 64 d.dir.length) d.dir ∗
        r1b_opkStage1At fsp c0 c1 c2 c3 c4 c5 c6
          w0e0_in w0e4_in w9_in w13_in w15_in w23_in b31_in ∗
        ((fsp + 0x110#64) ↦₆₄ opkCap) ∗ ((fsp + 0x11c#64) ↦₃₂ opkId) ∗
        ((fsp + 0x120#64) ↦₆₄ opkPtr) ∗ ((fsp + 0x128#64) ↦₆₄ kpkPtr) ∗
        ((fsp + 0x130#64) ↦₆₄ (kpkPtr + 4#64 + BitVec.ofNat 64 kpkKey.length)) ∗
        ((fsp + 0x138#64) ↦₆₄ BitVec.ofNat 64 kpkKey.length) ∗
        ((fsp + 0x140#64) ↦₆₄ (kpkPtr + 4#64)) ∗
        ((fsp + 0x148#64) ↦₆₄ 64#64) ∗
        ((fsp + 0x150#64) ↦₆₄ kpkCap) ∗
        ((fsp + 0x158#64) ↦₆₄ (spkPtr + 4#64 + BitVec.ofNat 64 spkKey.length)) ∗
        ((fsp + 0x164#64) ↦₃₂ ofLe32 r0 r1 r2 r3) ∗
        ((fsp + 0x168#64) ↦₆₄ spkPtr) ∗ ((fsp + 0x170#64) ↦₆₄ spkCap) ∗
        ((fsp + 0x178#64) ↦₆₄ (spkPtr + 4#64)) ∗
        ((fsp + 0x188#64) ↦₆₄ spkId.zeroExtend 64) ∗ ((fsp + 0x190#64) ↦₆₄ d.ikW3) ∗
        ((fsp + 0x198#64) ↦₆₄ regCap) ∗ ((fsp + 0x1a0#64) ↦₆₄ regPtr) ∗
        ((fsp + 0x1a8#64) ↦₆₄ d.ikW1) ∗
        ((fsp + 0x1b0#64) ↦₃₂ d.peerV.device.zeroExtend 32) ∗
        memRegion (fsp + 0x1b4#64) 4 ∗ memRegion (fsp + 0x1750#64) 24 ∗
        stackAt fsp (resStack - runFrame) ∗ A.pool lim st s)
      Q Qp oom := by
  intro fsp
  change s.readReg64 (.gpr 24#5) = fsp + 0x380#64 at hx24
  let _ := hx23; let _ := hx24; let _ := hx25; let _ := hx27; let _ := hx28
  have hst := hok.st
  have hs_run : s.status = .Running := hst.run
  have hs_sp : s.sp = fsp := hst.sp
  let _ := hs_run; let _ := hs_sp
  have hal : fsp &&& 15#64 = 0#64 := r1b_fsp_align hst.sp hst.spAligned
  have hal4d4 : (fsp + 0x4d4#64) &&& 3#64 = 0#64 := by bv_bits
  have hal4da : (fsp + 0x4da#64) &&& 1#64 = 0#64 := by bv_bits
  have hal4de : (fsp + 0x4de#64) &&& 1#64 = 0#64 := by bv_bits
  have hal4e8 : (fsp + 0x4e8#64) &&& 7#64 = 0#64 := by bv_bits
  have hal3b8 : (fsp + 0x3b8#64) &&& 3#64 = 0#64 := by bv_bits
  have hal3d8 : (fsp + 0x3d8#64) &&& 3#64 = 0#64 := by bv_bits
  have hal3dc : (fsp + 0x3dc#64) &&& 1#64 = 0#64 := by bv_bits
  have hal0e4 : (fsp + 0x0e4#64) &&& 3#64 = 0#64 := by bv_bits
  have hal0e8 : (fsp + 0x0e8#64) &&& 7#64 = 0#64 := by bv_bits
  have hpc_in := hst.pc; change s.pc = (blkPl_579).base + 9360#64 at hpc_in
  dsimp only [pkLayoutAt, pkRestAt, r1b_opkStage1At]
  rw [sevenBytesHeadAt_eq_tailAt (fsp + 0x4d1#64)]
  dsimp only [sevenBytesTailAt, sevenBytesHeadAt]
  try simp only [BitVec.add_assoc]; try simp only [BitVec.reduceAdd]; try simp only [sepConj_assoc]
  try rw [← BitVec.add_assoc kpkPtr 4#64]; try rw [← BitVec.add_assoc spkPtr 4#64]
  have hpc := hpc_in; have hrun := hst.run; have hsp : s.sp = fsp := hst.sp
  apply r1b_seq_lscro_oom (mid := (blkPl_579).base + 9372#64) hst.inv
  dsimp only [runProgPlaced, lsProg_579]
  apply sepWP_seg_ls_vm (Q := (blkPC_579).rebase (blkPl_579).base (hooksException _))
    blkLib_eq_579 blk579_noSvc0 (mid := (blkPl_579).base + 9372#64)
  intro _m_strip1; wp_steps
  refine SepWP.done (by simp only [wp_norm, arm64_norm, *]; try bv_omega)
    (by simp only [wp_norm, arm64_norm, *]) fun _m_real1 hnsp1 => ?_
  have hvmp1 : VmPreserved s _ :=
    hnsp1.toVmPreserved (by simp only [wp_norm, arm64_norm, *])
  try simp only [State.setMem_setMem] at hvmp1 ⊢
  apply SepWP.done (by simp only [wp_norm, arm64_norm, *])
    (by simp only [wp_norm, arm64_norm, *])
  refine r1b_bind_state_placed fun sm1 hsm1 hinv1 => by
    have hvm1 : VmPreserved s sm1 := hsm1 ▸ hvmp1
    rw [← A.pool_transport lim st s sm1 hvm1]
    change SepWPp (runProgPlaced H) _ _ _ _ _ _
    clear hpc hrun hsp
    have hflip4d1 :
        ((fsp + 0x4d1#64) ↦₈ b0) ∗ ((fsp + 0x4d2#64) ↦₈ b1) ∗
          ((fsp + 0x4d3#64) ↦₈ b2) ∗ ((fsp + 0x4d4#64) ↦₃₂ (b6 ++ b5 ++ b4 ++ b3)) ⊢
        ((fsp + 0x4d1#64) ↦₃₂ (b3 ++ b2 ++ b1 ++ b0)) ∗
          ((fsp + 0x4d5#64) ↦₈ b4) ∗ ((fsp + 0x4d6#64) ↦₈ b5) ∗
          ((fsp + 0x4d7#64) ↦₈ b6) := by
      have heq := (sevenBytesHeadAt_eq_tailAt (fsp + 0x4d1#64) b0 b1 b2 b3 b4 b5 b6).symm
      dsimp only [sevenBytesHeadAt, sevenBytesTailAt] at heq
      simp only [BitVec.add_assoc, BitVec.reduceAdd, sepConj_assoc] at heq
      rw [heq]; exact Entails.refl _
    refine r1b_sepWPp_frame_ro (by r1b_ac) hflip4d1 (by r1b_ac) ?_
    try simp only [sepConj_assoc]
    have hpc : sm1.pc = (blkPl_579).base + 9372#64 := by simp only [hsm1, wp_norm, arm64_norm]
    have hrun : sm1.status = .Running := by simp only [hsm1, wp_norm, arm64_norm, hst.run]
    have hsp : sm1.sp = fsp := by simpa only [hsm1, wp_norm, arm64_norm] using hst.sp
    have hx10_1 : sm1.readReg64 (.gpr 10#5) = fsp + 0x4d0#64 := by
      solve
      | simp only [hsm1, wp_norm, arm64_norm]
      | simpa only [hsm1, wp_norm, arm64_norm] using congrArg (· + 0x4d0#64) hst.sp
    have hx24_1 : sm1.readReg64 (.gpr 24#5) = fsp + 0x380#64 := by
      solve
      | simp only [hsm1, wp_norm, arm64_norm]
      | simpa only [hsm1, wp_norm, arm64_norm] using hx24
    let _ := hx10_1; let _ := hx24_1
    apply r1b_seq_lscro_oom (mid := (blkPl_579).base + 9400#64) hinv1
    dsimp only [runProgPlaced, lsProg_579]
    apply sepWP_seg_ls_vm (Q := (blkPC_579).rebase (blkPl_579).base (hooksException _))
      blkLib_eq_579 blk579_noSvc0 (mid := (blkPl_579).base + 9400#64)
    intro _m_strip2; wp_steps
    refine SepWP.done (by simp only [wp_norm, arm64_norm, *]; try bv_omega)
      (by simp only [wp_norm, arm64_norm, *]) fun _m_real2 hnsp2 => ?_
    have hvmp2 : VmPreserved sm1 _ :=
      hnsp2.toVmPreserved (by simp only [wp_norm, arm64_norm, *])
    try simp only [State.setMem_setMem] at hvmp2 ⊢
    apply SepWP.done (by simp only [wp_norm, arm64_norm, *])
      (by simp only [wp_norm, arm64_norm, *])
    refine r1b_bind_state_placed fun sm2 hsm2 hinv2 => by
      have hvm2 : VmPreserved sm1 sm2 := hsm2 ▸ hvmp2
      rw [← A.pool_transport lim st sm1 sm2 hvm2]
      change SepWPp (runProgPlaced H) _ _ _ _ _ _
      clear hpc hrun hsp
      have hflip3b8_in :
          ((fsp + 0x3b8#64) ↦₃₂ (b3 ++ b2 ++ b1 ++ b0)) ∗
            ((fsp + 0x3bc#64) ↦₈ c4) ∗ ((fsp + 0x3bd#64) ↦₈ c5) ∗
            ((fsp + 0x3be#64) ↦₈ c6) ⊢
          ((fsp + 0x3b8#64) ↦₈ b0) ∗ ((fsp + 0x3b9#64) ↦₈ b1) ∗
            ((fsp + 0x3ba#64) ↦₈ b2) ∗ ((fsp + 0x3bb#64) ↦₃₂ (c6 ++ c5 ++ c4 ++ b3)) := by
        have heq := sevenBytesHeadAt_eq_tailAt (fsp + 0x3b8#64) b0 b1 b2 b3 c4 c5 c6
        dsimp only [sevenBytesHeadAt, sevenBytesTailAt] at heq
        simp only [BitVec.add_assoc, BitVec.reduceAdd, sepConj_assoc] at heq
        rw [heq]; exact Entails.refl _
      refine r1b_sepWPp_frame_ro (by r1b_ac) hflip3b8_in (by r1b_ac) ?_
      try simp only [sepConj_assoc]
      have hpc : sm2.pc = (blkPl_579).base + 9400#64 := by simp only [hsm2, wp_norm, arm64_norm]
      have hrun : sm2.status = .Running := by simp only [hsm2, hsm1, wp_norm, arm64_norm, hst.run]
      have hsp : sm2.sp = fsp := by simpa only [hsm2, hsm1, wp_norm, arm64_norm] using hst.sp
      have hx24_2 : sm2.readReg64 (.gpr 24#5) = fsp + 0x380#64 := by
        solve
        | simp only [hsm2, hsm1, wp_norm, arm64_norm]
        | simpa only [hsm2, hsm1, wp_norm, arm64_norm] using hx24
      have hx9_2 : sm2.readReg64 (.gpr 9#5) = (b6 ++ b5 ++ b4 ++ b3).zeroExtend 64 := by
        simp only [hsm2, hsm1, wp_norm, arm64_norm]
      let _ := hx24_2; let _ := hx9_2
      apply r1b_seq_lscro_oom (mid := (blkPl_579).base + 9436#64) hinv2
      dsimp only [runProgPlaced, lsProg_579]
      apply sepWP_seg_ls_vm (Q := (blkPC_579).rebase (blkPl_579).base (hooksException _))
        blkLib_eq_579 blk579_noSvc0 (mid := (blkPl_579).base + 9436#64)
      intro _m_strip3; wp_steps
      refine SepWP.done (by simp only [wp_norm, arm64_norm, *]; try bv_omega)
        (by simp only [wp_norm, arm64_norm, *]) fun _m_real3 hnsp3 => ?_
      have hvmp3 : VmPreserved sm2 _ :=
        hnsp3.toVmPreserved (by simp only [wp_norm, arm64_norm, *])
      try simp only [State.setMem_setMem] at hvmp3 ⊢
      apply SepWP.done (by simp only [wp_norm, arm64_norm, *])
        (by simp only [wp_norm, arm64_norm, *])
      refine r1b_bind_state_placed fun sm3 hsm3 hinv3 => by
        have hvm3 : VmPreserved sm2 sm3 := hsm3 ▸ hvmp3
        have hfs_m3 : sm3.fs = s.fs := by simp only [hsm3, hsm2, hsm1, wp_norm, arm64_norm]
        rw [← A.pool_transport lim st sm2 sm3 hvm3]
        change SepWPp (runProgPlaced H) _ _ _ _ _ _
        have hok3 : r1b_OkCtxPlaced r1b_CodeOk S g d s0 sm3 0x24dc := hok.of_step
          { pc := by simp only [hsm3, wp_norm, arm64_norm]
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
        have hw3bb : ((((b6 ++ b5 ++ b4 ++ b3).zeroExtend 64).truncate 32) : BitVec 32) =
            (b6 ++ b5 ++ b4 ++ b3) := by bv_bits
        have hw3d8 : ((w9.zeroExtend 64).truncate 32 : BitVec 32) = w9 := by bv_bits
        have hw3dc : (((w13.zeroExtend 32).zeroExtend 64).truncate 16 : BitVec 16) = w13 := by bv_bits
        have hw228 : (((b31.zeroExtend 32).zeroExtend 64).truncate 8 : BitVec 8) = b31 := by bv_bits
        have hw0e0 : (((b8.zeroExtend 32).zeroExtend 64).truncate 32 : BitVec 32) =
            b8.zeroExtend 32 := by bv_bits
        have hw0e4 : (((b7.zeroExtend 32).zeroExtend 64).truncate 32 : BitVec 32) =
            b7.zeroExtend 32 := by bv_bits
        simp only [hsm1, hsm2, wp_norm, arm64_norm, hw3bb, hw3d8, hw3dc, hw228, hw0e0, hw0e4]
        try rw [← BitVec.add_assoc kpkPtr 4#64]; try rw [← BitVec.add_assoc spkPtr 4#64]
        have hflip3b8_out :
            ((fsp + 0x3b8#64) ↦₈ b0) ∗ ((fsp + 0x3b9#64) ↦₈ b1) ∗
              ((fsp + 0x3ba#64) ↦₈ b2) ∗ ((fsp + 0x3bb#64) ↦₃₂ (b6 ++ b5 ++ b4 ++ b3)) ⊢
            sevenBytesHeadAt (fsp + 0x3b8#64) b0 b1 b2 b3 b4 b5 b6 := by
          have heq := (sevenBytesHeadAt_eq_tailAt (fsp + 0x3b8#64) b0 b1 b2 b3 b4 b5 b6).symm
          dsimp only [sevenBytesTailAt] at heq
          simp only [BitVec.add_assoc, BitVec.reduceAdd, sepConj_assoc] at heq
          rw [heq]; exact Entails.refl _
        have h4d0_48 :
            ((fsp + 0x4d0#64) ↦₈ 0#8) ∗
              ((fsp + 0x4d1#64) ↦₃₂ (b3 ++ b2 ++ b1 ++ b0)) ∗
              ((fsp + 0x4d5#64) ↦₈ b4) ∗ ((fsp + 0x4d6#64) ↦₈ b5) ∗
              ((fsp + 0x4d7#64) ↦₈ b6) ∗ ((fsp + 0x4d8#64) ↦₈ b7) ∗
              ((fsp + 0x4d9#64) ↦₈ b8) ∗ ((fsp + 0x4da#64) ↦₃₂ w9) ∗
              ((fsp + 0x4de#64) ↦₁₆ w13) ∗ ((fsp + 0x4e0#64) ↦₆₄ w15) ∗
              ((fsp + 0x4e8#64) ↦₆₄ w23) ∗ ((fsp + 0x4f0#64) ↦₈ b31) ∗
              memRegion (fsp + 0x4f1#64) 15 ⊢
              memRegion (fsp + 0x4d0#64) 48 := by
          have h48 := r1b_pk4d0_ok_to_region48_placed_fd fsp b0 b1 b2 b3 b4 b5 b6 b7 b8 w9 w13 w15 w23 b31
          dsimp only [pkLayoutAt, sevenBytesHeadAt, pkRestAt] at h48
          simpa only [BitVec.add_assoc, BitVec.reduceAdd, sepConj_assoc] using h48
        have h110 : ((fsp + 0x110#64) ↦₆₄ opkCap) ⊢ memRegion (fsp + 0x110#64) 8 :=
          pointsTo64_entails_memRegion _ _
        have hx24_run : sm3.readReg64 (.gpr 24#5) = runFsp s0 + 0x380#64 := by
          change sm3.readReg64 (.gpr 24#5) = fsp + 0x380#64
          simpa only [hsm3, hsm2, hsm1, wp_norm, arm64_norm] using hx24
        refine sepWPp_weaken_pre ?_
          (r1b_opk_free_24dc_placed_fd (st := st) (opkCap := opkCap) (opkPtr := opkPtr) (opkBs := opkBs)
            (kpkKey := kpkKey) (kpkSig := kpkSig) (spkKey := spkKey) (spkSig := spkSig)
            hh hbnd hok3
            (by simp only [hsm3, hsm2, wp_norm, arm64_norm])
            (by solve
              | simp only [hsm3, hsm2, hsm1, wp_norm, arm64_norm]
              | simpa only [hsm3, hsm2, hsm1, wp_norm, arm64_norm] using hx23)
            hx24_run
            (by solve
              | simp only [hsm3, hsm2, hsm1, wp_norm, arm64_norm]
              | simpa only [hsm3, hsm2, hsm1, wp_norm, arm64_norm] using hx25)
            (by solve
              | simp only [hsm3, hsm2, hsm1, wp_norm, arm64_norm]
              | simpa only [hsm3, hsm2, hsm1, wp_norm, arm64_norm] using hx27)
            (by solve
              | simp only [hsm3, hsm2, hsm1, wp_norm, arm64_norm]
              | simpa only [hsm3, hsm2, hsm1, wp_norm, arm64_norm] using hx28)
            hpanic
            (fun sf evs hfo hok_f hfs_f hx23_f hx24_f hx25_f hx27_f hx28_f =>
              hk sf evs hfo hok_f (hfs_f.trans hfs_m3) hx23_f hx24_f hx25_f hx27_f hx28_f))
        dsimp only [r1b_opkStage1At]
        exact r1b_entails_frame_ro (by r1b_ac)
          (sepConj_mono hflip3b8_out (sepConj_mono h4d0_48 h110)) (by r1b_ac)

end LibsignalBinary.Proofs.SignalSession.Cli.Run.Compose.Arms.R1b.ReadOpkPlacedBudgetFd
