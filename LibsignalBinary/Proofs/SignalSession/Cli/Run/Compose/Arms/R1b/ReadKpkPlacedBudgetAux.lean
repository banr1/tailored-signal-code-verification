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
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Compose.Arms.R1b.ErrCleanupSpkRegPlacedBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Compose.Arms.R1b.ReadKpkPlaced
import Arm64.Trusted.Spec.Hoare
import Arm64.Trusted.Spec.SepLogic
import LibsignalBinary.Proofs.Common.SharedHelpers
meta import LibsignalBinary.Proofs.Common.SharedHelpers -- shake: keep
import LibsignalBinary.Proofs.SignalSession.Cli.Main.Proofs.M4Layout

/-!
# Budget-Threaded Stage 2 Error Exits and `2adc` Cleanup for Arm `R1b`

Verifies `r1b_cleanup_2adc_placed` (`0x2adc → 0x2b24`, optional `kpk` `Vec<u8>` buffer deallocation),
`r1b_err_1aa8_placed` (`0x1aa8 → 0x2b28`, unreadable `kyber-pre-key`), and `r1b_err_1b60_placed`
(`0x1b60 → 0x2adc`, malformed `kyber-pre-key`) on Block `579` under `[LibsignalPlacement]` and
`RustCliAllocBudget M`.
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 200000
set_option linter.unusedSimpArgs false

namespace LibsignalBinary.Proofs.SignalSession.Cli.Run.Compose.Arms.R1b.ReadKpkPlacedBudgetAux

open Arm64 Arm64.Process ProofLib SepProp
open CryptoVerification (LibsignalHooks LibsignalPlacement lsmpl lsρ)
open CryptoVerification.LibsignalPublicApi.StoreKit (LibsignalCodeRoLoaded)
open CryptoVerification.LibsignalTripleRatchetRepr (speWord)
open CryptoVerification.SignalSession (lsRustDeallocSymCli)
open CryptoVerification.SignalSession.Cli (StoresGhost)
open CryptoVerification.SignalSession.Cli.MainHops (RunCall ownedBytes sepWPp_weaken_pre)
open CryptoVerification.SignalSession.Cli.Run.Placed (blkPl_579 lsProg_579)
open CryptoVerification.SignalSession.Cli.RunCompose
  (AtRejectPlaced Init1Data PanicK RejectKind r1b_CodeOk r1b_ErrCtxPlaced
   r1b_SpePayload r1b_SpePayload_str r1b_StackBounds r1b_bind_state_placed
   r1b_cell64_cons r1b_cells2_to_region16 r1b_cells6_to_region48 r1b_entails_frame_core
   r1b_errCommon r1b_errCore r1b_errLow4 r1b_fold_low4 r1b_fsp_align
   r1b_region16_to_cells r1b_u64_split32 rejectMem runFsp runPcPlaced runPcPlaced_eq
   runProgPlaced)
open CryptoVerification.SignalSession.Cli.RunSkeleton (RunBudgets runFrame)
open LibsignalBinary.Heap
  (AllocCostModel AllocEvent BudgetLimits FreeOnlyEvs RustCliAllocBudget VmPreserved
   rustDeallocEvents)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Compose.Arms.R1b.CommonPlacedBudget
  (r1b_call_dealloc_ownedBytes_placed)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Compose.Arms.R1b.ErrCleanupPlacedBudget
  (r1b_errCommon_atState_eq sepWP_with_vm_oom)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Compose.Arms.R1b.ErrCleanupSpkRegPlacedBudget
  (r1b_cleanup_2b24_placed r1b_cleanup_2b28_placed_env)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Compose.HopsPlacedBudget (RejectKPlacedEnv)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DropSpeOwnedPlacedBudget
  (DropSpeOwnedOkAtBlock)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.SkeletonPlacedBudget (RunHooksPlaced)

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

local macro "r1b_prove_spe_str" : tactic =>
  `(tactic| (refine r1b_SpePayload_str _ ?_; refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> bv_bits))

local macro (priority := high) "r1b_ac" : tactic =>
  `(tactic| ((try dsimp +zetaDelta only) <;> first | rfl | simp only [emp_sepConj] | sep_ac_rfl))

private meta def r1bStripLetsKA : Nat → Lean.Expr → Lean.Expr
  | 0, e => e
  | n + 1, .letE _ _ v b _ => r1bStripLetsKA n (b.instantiate1 v)
  | n + 1, .mdata _ e => r1bStripLetsKA n e
  | _, e => e

private meta def r1bSplitSepKA : Nat → Lean.Expr → Lean.Expr → Array Lean.Expr
  | 0, _, e => #[e]
  | fuel + 1, sepSample, e =>
    let e := r1bStripLetsKA 64 e
    let fn := sepSample.getAppFn.constName!
    let ar := sepSample.getAppNumArgs
    if e.isAppOfArity fn ar then
      r1bSplitSepKA fuel sepSample (e.getArg! (ar - 2)) ++
        r1bSplitSepKA fuel sepSample (e.getArg! (ar - 1))
    else #[e]

private meta def r1bIsDefEqPureKA (x a : Lean.Expr) : Lean.Elab.TermElabM Bool := do
  let x := r1bStripLetsKA 64 x; let a := r1bStripLetsKA 64 a
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

private meta def r1bComputeRestKA (ctxName : String) (p a1 : Lean.Expr) :
    Lean.Elab.TermElabM Lean.Expr := do
  let sepTy := Lean.mkConst ``SepProp []
  let sepSample ← Lean.Elab.Term.elabTerm (← `(emp ∗ emp)) (some sepTy)
  let empExpr ← Lean.Elab.Term.elabTerm (← `(emp)) (some sepTy)
  let ps := (r1bSplitSepKA 64 sepSample (← Lean.instantiateMVars p)).toList
  let a1s := (r1bSplitSepKA 64 sepSample (← Lean.instantiateMVars a1)).toList
  let mut rem := ps
  for a in a1s do
    let mut removed := false
    let mut next : List Lean.Expr := []
    for x in rem do
      if !removed && (← r1bIsDefEqPureKA x a) then removed := true
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

local elab (priority := high) "r1b_entails_frame_ka " t1:term:arg h:term:arg t2:term:arg :
    term <= expectedType => do
  let exp ← Lean.instantiateMVars expectedType
  if exp.isMVar then Lean.Elab.Term.tryPostpone
  let entSample ← Lean.Elab.Term.elabTerm (← `(emp ⊢ emp)) none
  let ear := entSample.getAppNumArgs
  let expS := r1bStripLetsKA 64 exp
  let p := expS.getArg! (ear - 2)
  let q := expS.getArg! (ear - 1)
  if (← Lean.instantiateMVars p).isMVar then Lean.Elab.Term.tryPostpone
  if (← Lean.instantiateMVars q).isMVar then Lean.Elab.Term.tryPostpone
  let hExpr ← Lean.Elab.Term.elabTerm h none
  let hTy := r1bStripLetsKA 64 (← Lean.instantiateMVars (← Lean.Meta.inferType hExpr))
  let a1 := hTy.getArg! (ear - 2)
  let a2 := hTy.getArg! (ear - 1)
  let r ← r1bComputeRestKA "r1b_entails_frame" p a1
  let sepTy := Lean.mkConst ``SepProp []
  let empExpr ← Lean.Elab.Term.elabTerm (← `(emp)) (some sepTy)
  let sepSample ← Lean.Elab.Term.elabTerm (← `(emp ∗ emp)) (some sepTy)
  let sar := sepSample.getAppNumArgs
  let mkSep (x y : Lean.Expr) : Lean.Expr :=
    sepSample.withApp fun f args => Lean.mkAppN f (args.extract 0 (sar - 2) ++ #[x, y])
  let rIsEmp ← r1bIsDefEqPureKA r empExpr
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

/-! ## `2adc → 2b24` Cleanup (`kpk` `Vec<u8>` Optional Drop) -/

private theorem r1b_cleanup_2adc_cap0_placed [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {st : M.σ}
    {H : LibsignalHooks} {B : RunBudgets}
    {g : RunCall} {d : Init1Data} {s0 s : State} {resStack : Nat}
    {v188 kpkPtr kpkLen spkCap spkPtr spkLen regCap regPtr regLen : BitVec 64}
    {kpkBs spkBs regBs : List (BitVec 8)}
    {Q Qp : State → SepProp → Prop} {oom : State → SepProp}
    (hh : RunHooksPlaced A lim H) (hdrop : DropSpeOwnedOkAtBlock (runProgPlaced H) A lim)
    (hbnd : r1b_StackBounds B resStack)
    (hc : r1b_ErrCtxPlaced r1b_CodeOk g d s0 s 0x2adc)
    (hx1 : s.readReg64 (.gpr 1#5) = 0#64)
    (hpanic : PanicK g s0 Qp)
    (hrej : ∀ (sf : State) (evs : List AllocEvent),
      FreeOnlyEvs evs →
      AtRejectPlaced r1b_CodeOk g StoresGhost.opened .postDispatch s0 sf →
      SepWPp (runProgPlaced H) (s0.readReg64 .lr) sf
        (rejectMem (A.atState lim (M.stepEvents evs st) sf)
          g StoresGhost.opened .postDispatch s0 resStack)
        Q Qp oom) :
    let fsp := runFsp s0
    SepWPp (runProgPlaced H) (s0.readReg64 .lr) s
      (r1b_SpePayload A.repAlloc (s.readReg64 (.gpr 12#5))
          (s.readReg64 (.gpr 10#5)) (s.readReg64 (.gpr 23#5))
          (s.readReg64 (.gpr 27#5)) (s.readReg64 (.gpr 16#5))
          (s.readReg64 (.gpr 14#5)) (s.readReg64 (.gpr 15#5))
          (s.readReg64 (.gpr 28#5)) v188 ∗
        ownedBytes A.repAlloc 0#64 kpkPtr kpkLen kpkBs ∗
        ownedBytes A.repAlloc spkCap spkPtr spkLen spkBs ∗
        ownedBytes A.repAlloc regCap regPtr regLen regBs ∗
        r1b_errCommon (A.atState lim st s) g d s0 resStack ∗
        memRegion (fsp + 0x110#64) 8 ∗ memRegion (fsp + 0x11c#64) 4 ∗
        memRegion (fsp + 0x120#64) 16 ∗ memRegion (fsp + 0x150#64) 16 ∗
        ((fsp + 0x168#64) ↦₆₄ spkPtr) ∗ ((fsp + 0x170#64) ↦₆₄ spkCap) ∗
        memRegion (fsp + 0x178#64) 8 ∗
        ((fsp + 0x188#64) ↦₆₄ v188) ∗ memRegion (fsp + 0x190#64) 8 ∗
        ((fsp + 0x198#64) ↦₆₄ regCap) ∗ ((fsp + 0x1a0#64) ↦₆₄ regPtr) ∗
        memRegion (fsp + 0x1a8#64) 16 ∗ memRegion (fsp + 0x4d0#64) 48)
      Q Qp oom := by
  intro fsp
  have hfsp_eq : runFsp s0 = fsp := rfl
  rw [r1b_errCommon_atState_eq]
  generalize herrCore : r1b_errCore A.repAlloc g d s0 = errCore
  rw [hfsp_eq, r1b_fold_low4]
  have hpc := hc.st.pc; have hrun := hc.st.run
  have hsp : s.sp = fsp := hc.st.sp
  have hfp := hc.st.fp; have hinv := hc.st.inv; have hvregs := hc.st.vregs
  have hsp0 := hc.st.spAligned
  change s.pc = (blkPl_579).base + 0x2adc#64 at hpc
  apply r1b_seq_lscro_oom (mid := (blkPl_579).base + 0x2b24#64) hinv
  dsimp only [runProgPlaced, lsProg_579]
  by_vm_open (
    wp_steps
    refine SepWP.done (by simp only [wp_norm, arm64_norm, *]; try bv_omega)
      (by simp only [wp_norm, arm64_norm, *])
      ⟨by simp only [wp_norm, arm64_norm], fun hvm => ?_⟩
    refine r1b_bind_state_placed fun sm hsm hinv_m => ?_
    rw [← hsm] at hvm
    rw [← A.pool_transport lim st s sm hvm]
    change SepWPp (runProgPlaced H) _ _ _ _ _ _
    have hc_m : r1b_ErrCtxPlaced r1b_CodeOk g d s0 sm 0x2b24 := {
      st := {
        pc := by simp only [hsm, wp_norm, arm64_norm]
        run := by simp only [hsm, wp_norm, arm64_norm, hrun]
        sp := by simpa only [hsm, wp_norm, arm64_norm] using hc.st.sp
        fp := by simpa only [hsm, wp_norm, arm64_norm] using hfp
        inv := hinv_m
        vregs := by simpa only [calleeSavedVRegs, hsm, wp_norm, arm64_norm] using hvregs
        spAligned := hsp0
      }
      x19 := by simpa only [hsm, wp_norm, arm64_norm] using hc.x19
      x20 := by simpa only [hsm, wp_norm, arm64_norm] using hc.x20
      x21 := by simpa only [hsm, wp_norm, arm64_norm] using hc.x21
      trace := by simpa only [hsm, wp_norm, arm64_norm] using hc.trace
      hist := ⟨by simpa only [hsm, wp_norm, arm64_norm] using hc.hist.1,
        by simpa only [hsm, wp_norm, arm64_norm] using hc.hist.2⟩
      ans := hc.ans
    }
    have hr12 : sm.readReg64 (.gpr 12#5) = s.readReg64 (.gpr 12#5) := by
      simp only [hsm, wp_norm, arm64_norm]
    have hr10 : sm.readReg64 (.gpr 10#5) = s.readReg64 (.gpr 10#5) := by
      simp only [hsm, wp_norm, arm64_norm]
    have hr23 : sm.readReg64 (.gpr 23#5) = s.readReg64 (.gpr 23#5) := by
      simp only [hsm, wp_norm, arm64_norm]
    have hr27 : sm.readReg64 (.gpr 27#5) = s.readReg64 (.gpr 27#5) := by
      simp only [hsm, wp_norm, arm64_norm]
    have hr16 : sm.readReg64 (.gpr 16#5) = s.readReg64 (.gpr 16#5) := by
      simp only [hsm, wp_norm, arm64_norm]
    have hr14 : sm.readReg64 (.gpr 14#5) = s.readReg64 (.gpr 14#5) := by
      simp only [hsm, wp_norm, arm64_norm]
    have hr15 : sm.readReg64 (.gpr 15#5) = s.readReg64 (.gpr 15#5) := by
      simp only [hsm, wp_norm, arm64_norm]
    have hr28 : sm.readReg64 (.gpr 28#5) = s.readReg64 (.gpr 28#5) := by
      simp only [hsm, wp_norm, arm64_norm]
    refine sepWPp_weaken_pre ?_
      (r1b_cleanup_2b24_placed (st := st) (v188 := v188)
        (spkCap := spkCap) (spkPtr := spkPtr) (spkLen := spkLen) (spkBs := spkBs)
        (regCap := regCap) (regPtr := regPtr) (regLen := regLen) (regBs := regBs)
        hh hdrop hbnd hc_m hpanic hrej)
    rw [hr12, hr10, hr23, hr27, hr16, hr14, hr15, hr28]
    rw [r1b_errCommon_atState_eq, herrCore, r1b_fold_low4]
    dsimp only [fsp]
    have hdrop_kpk : ownedBytes A.repAlloc 0#64 kpkPtr kpkLen kpkBs ∗ anyHeap ⊢ anyHeap :=
      entails_anyHeap _
    refine Entails.trans (Entails.of_eq (show _ =
      r1b_SpePayload A.repAlloc (s.readReg64 (.gpr 12#5))
        (s.readReg64 (.gpr 10#5)) (s.readReg64 (.gpr 23#5))
        (s.readReg64 (.gpr 27#5)) (s.readReg64 (.gpr 16#5))
        (s.readReg64 (.gpr 14#5)) (s.readReg64 (.gpr 15#5))
        (s.readReg64 (.gpr 28#5)) v188 ∗
      ownedBytes A.repAlloc spkCap spkPtr spkLen spkBs ∗
      ownedBytes A.repAlloc regCap regPtr regLen regBs ∗
      (errCore ∗ stackAt (runFsp s0) (resStack - runFrame) ∗ A.pool lim st sm ∗
        (ownedBytes A.repAlloc 0#64 kpkPtr kpkLen kpkBs ∗ anyHeap)) ∗
      r1b_errLow4 (runFsp s0) ∗
      ((runFsp s0 + 0x168#64) ↦₆₄ spkPtr) ∗ ((runFsp s0 + 0x170#64) ↦₆₄ spkCap) ∗
      memRegion (runFsp s0 + 0x178#64) 8 ∗
      ((runFsp s0 + 0x188#64) ↦₆₄ v188) ∗ memRegion (runFsp s0 + 0x190#64) 8 ∗
      ((runFsp s0 + 0x198#64) ↦₆₄ regCap) ∗ ((runFsp s0 + 0x1a0#64) ↦₆₄ regPtr) ∗
      memRegion (runFsp s0 + 0x1a8#64) 16 ∗ memRegion (runFsp s0 + 0x4d0#64) 48 by sep_ac_rfl)) ?_
    exact sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
      (sepConj_mono_left (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right hdrop_kpk))))))
  )

set_option maxHeartbeats 400000 in
private theorem r1b_cleanup_2adc_capNe_placed [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {st : M.σ}
    {H : LibsignalHooks} {B : RunBudgets}
    {g : RunCall} {d : Init1Data} {s0 s : State} {resStack : Nat}
    {v188 kpkCap kpkPtr kpkLen spkCap spkPtr spkLen regCap regPtr regLen : BitVec 64}
    {kpkBs spkBs regBs : List (BitVec 8)}
    {Q Qp : State → SepProp → Prop} {oom : State → SepProp}
    (hh : RunHooksPlaced A lim H) (hdrop : DropSpeOwnedOkAtBlock (runProgPlaced H) A lim)
    (hbnd : r1b_StackBounds B resStack)
    (hc : r1b_ErrCtxPlaced r1b_CodeOk g d s0 s 0x2adc)
    (hx1 : s.readReg64 (.gpr 1#5) = kpkCap)
    (hx26 : s.readReg64 (.gpr 26#5) = kpkPtr)
    (hcap : kpkCap ≠ 0#64)
    (hpanic : PanicK g s0 Qp)
    (hrej : ∀ (sf : State) (evs : List AllocEvent),
      FreeOnlyEvs evs →
      AtRejectPlaced r1b_CodeOk g StoresGhost.opened .postDispatch s0 sf →
      SepWPp (runProgPlaced H) (s0.readReg64 .lr) sf
        (rejectMem (A.atState lim (M.stepEvents evs st) sf)
          g StoresGhost.opened .postDispatch s0 resStack)
        Q Qp oom) :
    let fsp := runFsp s0
    SepWPp (runProgPlaced H) (s0.readReg64 .lr) s
      (r1b_SpePayload A.repAlloc (s.readReg64 (.gpr 12#5))
          (s.readReg64 (.gpr 10#5)) (s.readReg64 (.gpr 23#5))
          (s.readReg64 (.gpr 27#5)) (s.readReg64 (.gpr 16#5))
          (s.readReg64 (.gpr 14#5)) (s.readReg64 (.gpr 15#5))
          (s.readReg64 (.gpr 28#5)) v188 ∗
        ownedBytes A.repAlloc kpkCap kpkPtr kpkLen kpkBs ∗
        ownedBytes A.repAlloc spkCap spkPtr spkLen spkBs ∗
        ownedBytes A.repAlloc regCap regPtr regLen regBs ∗
        r1b_errCommon (A.atState lim st s) g d s0 resStack ∗
        memRegion (fsp + 0x110#64) 8 ∗ memRegion (fsp + 0x11c#64) 4 ∗
        memRegion (fsp + 0x120#64) 16 ∗ memRegion (fsp + 0x150#64) 16 ∗
        ((fsp + 0x168#64) ↦₆₄ spkPtr) ∗ ((fsp + 0x170#64) ↦₆₄ spkCap) ∗
        memRegion (fsp + 0x178#64) 8 ∗
        ((fsp + 0x188#64) ↦₆₄ v188) ∗ memRegion (fsp + 0x190#64) 8 ∗
        ((fsp + 0x198#64) ↦₆₄ regCap) ∗ ((fsp + 0x1a0#64) ↦₆₄ regPtr) ∗
        memRegion (fsp + 0x1a8#64) 16 ∗ memRegion (fsp + 0x4d0#64) 48)
      Q Qp oom := by
  intro fsp
  have hfsp_eq : runFsp s0 = fsp := rfl
  rw [r1b_errCommon_atState_eq]
  generalize herrCore : r1b_errCore A.repAlloc g d s0 = errCore
  rw [hfsp_eq, r1b_fold_low4]
  have hpc := hc.st.pc; have hrun := hc.st.run
  have hsp : s.sp = fsp := hc.st.sp
  have hfp := hc.st.fp; have hinv := hc.st.inv; have hvregs := hc.st.vregs
  have hsp0 := hc.st.spAligned
  have hal : fsp &&& 15#64 = 0#64 := r1b_fsp_align hc.st.sp hsp0
  have hcap_f : (kpkCap == 0#64) = false := beq_false_of_ne hcap
  rw [ProofLib.memRegion_eight (fsp + 0x190#64), r1b_region16_to_cells (fsp + 0x1a8#64)]
  simp only [sepExists_sepConj_left, sepExists_sepConj_right]
  refine SepWPp.exists_elim fun v190 => SepWPp.exists_elim fun v1a8 =>
    SepWPp.exists_elim fun v1b0 => ?_
  have ho1b0 : fsp + 0x1a8#64 + 8#64 = fsp + 0x1b0#64 := by bv_omega
  rw [ho1b0]
  change s.pc = (blkPl_579).base + 0x2adc#64 at hpc
  apply r1b_seq_lscro_oom (mid := lsρ lsRustDeallocSymCli) hinv
  dsimp only [runProgPlaced, lsProg_579]
  by_vm_open (
    wp_steps
    refine SepWP.done (by simp only [wp_norm, arm64_norm, *]; try bv_omega)
      (by simp only [wp_norm, arm64_norm, *])
      ⟨by simp only [wp_norm, arm64_norm], fun hvm => ?_⟩
    refine r1b_bind_state_placed fun sm hsm hinv_m => ?_
    rw [← hsm] at hvm
    rw [← A.pool_transport lim st s sm hvm]
    change SepWPp (runProgPlaced H) _ _ _ _ _ _
    have hsm_run : sm.status = .Running := by simp only [hsm, wp_norm, arm64_norm, hrun]
    have hsm_sp0 : sm.sp = runFsp s0 := by simpa only [hsm, wp_norm, arm64_norm] using hc.st.sp
    have hsm_fp : sm.readReg64 .fp = s0.sp - 0x60#64 :=
      by simpa only [hsm, wp_norm, arm64_norm] using hfp
    have hsm_vr : calleeSavedVRegs sm = calleeSavedVRegs s0 := by
      simpa only [calleeSavedVRegs, hsm, wp_norm, arm64_norm] using hvregs
    have hsm_pc : sm.pc = lsρ lsRustDeallocSymCli := by simp only [hsm, wp_norm, arm64_norm]
    have hsm_lr : sm.readReg64 .lr = runPcPlaced 0x2b08 := by simp only [hsm, wp_norm, arm64_norm]
    have hsm_a0 : sm.readReg64 .x0 = kpkPtr := by simp only [hsm, wp_norm, arm64_norm]
    have hsm_a1 : sm.readReg64 .x1 = kpkCap := by simp only [hsm, wp_norm, arm64_norm, hx1]
    have hsm_a2 : sm.readReg64 .x2 = 1#64 := by simp only [hsm, wp_norm, arm64_norm]
    have hsm_x19 : sm.readReg64 (.gpr 19#5) = g.stores :=
      by simpa only [hsm, wp_norm, arm64_norm] using hc.x19
    have hsm_x20 : sm.readReg64 (.gpr 20#5) = g.res :=
      by simpa only [hsm, wp_norm, arm64_norm] using hc.x20
    have hsm_x21 : sm.readReg64 (.gpr 21#5) = d.meG.name.cap :=
      by simpa only [hsm, wp_norm, arm64_norm] using hc.x21
    have hsm_r22 : sm.readReg64 (.gpr 22#5) = s.readReg64 (.gpr 16#5) := by
      simp only [hsm, wp_norm, arm64_norm]
    have hsm_r23 : sm.readReg64 (.gpr 23#5) = s.readReg64 (.gpr 14#5) := by
      simp only [hsm, wp_norm, arm64_norm]
    have hsm_r24 : sm.readReg64 (.gpr 24#5) = s.readReg64 (.gpr 10#5) := by
      simp only [hsm, wp_norm, arm64_norm]
    have hsm_r25 : sm.readReg64 (.gpr 25#5) = s.readReg64 (.gpr 12#5) := by
      simp only [hsm, wp_norm, arm64_norm]
    have hsm_r26 : sm.readReg64 (.gpr 26#5) = s.readReg64 (.gpr 15#5) := by
      simp only [hsm, wp_norm, arm64_norm]
    have hsm_r27 : sm.readReg64 (.gpr 27#5) = s.readReg64 (.gpr 27#5) := by
      simp only [hsm, wp_norm, arm64_norm]
    have hsm_r28 : sm.readReg64 (.gpr 28#5) = s.readReg64 (.gpr 28#5) := by
      simp only [hsm, wp_norm, arm64_norm]
    have hsm_fs : sm.fs = s.fs := by simp only [hsm, wp_norm, arm64_norm]
    have hsm_tr : sm.trace = s.trace := by simp only [hsm, wp_norm, arm64_norm]
    clear hsm
    rw [← hfsp_eq]
    refine sepWPp_weaken_pre (P' :=
        ownedBytes A.repAlloc kpkCap kpkPtr kpkLen kpkBs ∗
        stackAt (runFsp s0) (resStack - runFrame) ∗ A.pool lim st sm ∗
        (r1b_SpePayload A.repAlloc (s.readReg64 (.gpr 12#5))
            (s.readReg64 (.gpr 10#5)) (s.readReg64 (.gpr 23#5))
            (s.readReg64 (.gpr 27#5)) (s.readReg64 (.gpr 16#5))
            (s.readReg64 (.gpr 14#5)) (s.readReg64 (.gpr 15#5))
            (s.readReg64 (.gpr 28#5)) v188 ∗
          ownedBytes A.repAlloc spkCap spkPtr spkLen spkBs ∗
          ownedBytes A.repAlloc regCap regPtr regLen regBs ∗
          errCore ∗ anyHeap ∗ r1b_errLow4 (runFsp s0) ∗
          ((runFsp s0 + 0x168#64) ↦₆₄ spkPtr) ∗ ((runFsp s0 + 0x170#64) ↦₆₄ spkCap) ∗
          memRegion (runFsp s0 + 0x178#64) 8 ∗
          ((runFsp s0 + 0x188#64) ↦₆₄ v188) ∗
          ((runFsp s0 + 0x190#64) ↦₆₄ s.readReg64 (.gpr 11#5)) ∗
          ((runFsp s0 + 0x198#64) ↦₆₄ regCap) ∗ ((runFsp s0 + 0x1a0#64) ↦₆₄ regPtr) ∗
          ((runFsp s0 + 0x1a8#64) ↦₆₄ s.readReg64 (.gpr 13#5)) ∗
          ((runFsp s0 + 0x1b0#64) ↦₆₄ s.readReg64 (.gpr 23#5)) ∗
          memRegion (runFsp s0 + 0x4d0#64) 48)) ?_ ?_
    · exact Entails.of_eq (by sep_ac_rfl)
    refine r1b_call_dealloc_ownedBytes_placed (Q := Q) (cap := kpkCap) (ptr := kpkPtr)
      (len := kpkLen) (bs := kpkBs)
      hh hbnd hinv_m hsm_pc hsm_run
      hsm_sp0 hsm_fp hsm_vr hsp0 hsm_lr
      hsm_a0 hsm_a1 hsm_a2
      hcap hpanic ?_
    intro s1 hin1 hcs1 hfs1 htr1
    rw [hfsp_eq]
    have hpc1 := hin1.pc; have hrun1 := hin1.run
    have hsp1 : s1.sp = fsp := hin1.sp
    have hfp1 := hin1.fp; have hinv1 := hin1.inv; have hvregs1 := hin1.vregs
    change s1.pc = (blkPl_579).base + 0x2b08#64 at hpc1
    apply r1b_seq_lscro_oom (mid := (blkPl_579).base + 0x2b24#64) hinv1
    dsimp only [runProgPlaced, lsProg_579]
    by_vm_open (
      wp_steps
      refine SepWP.done (by simp only [wp_norm, arm64_norm, *]; try bv_omega)
        (by simp only [wp_norm, arm64_norm, *])
        ⟨by simp only [wp_norm, arm64_norm], fun hvm2 => ?_⟩
      refine r1b_bind_state_placed fun sm2 hsm2 hinv2 => ?_
      rw [← hsm2] at hvm2
      rw [← A.pool_transport lim _ s1 sm2 hvm2]
      change SepWPp (runProgPlaced H) _ _ _ _ _ _
      rcases hcs1 with ⟨hc19, hc20, hc21, hc22, hc24, hc25, hc26, hc27, hc28, hc29, _, _⟩
      have htr2 : sm2.trace = s.trace := by
        simp only [hsm2, wp_norm, arm64_norm]; exact htr1.trans hsm_tr
      have hfs2 : sm2.fs = s.fs := by
        simp only [hsm2, wp_norm, arm64_norm]; exact hfs1.trans hsm_fs
      have hc_m2 : r1b_ErrCtxPlaced r1b_CodeOk g d s0 sm2 0x2b24 := {
        st := {
          pc := by simp only [hsm2, wp_norm, arm64_norm]
          run := by simp only [hsm2, wp_norm, arm64_norm, hrun1]
          sp := by simpa only [hsm2, wp_norm, arm64_norm] using hin1.sp
          fp := by simpa only [hsm2, wp_norm, arm64_norm] using hfp1
          inv := hinv2
          vregs := by simpa only [calleeSavedVRegs, hsm2, wp_norm, arm64_norm] using hvregs1
          spAligned := hsp0
        }
        x19 := by simp only [hsm2, wp_norm, arm64_norm, hc19, hsm_x19]
        x20 := by simp only [hsm2, wp_norm, arm64_norm, hc20, hsm_x20]
        x21 := by simp only [hsm2, wp_norm, arm64_norm, hc21, hsm_x21]
        trace := htr2 ▸ hc.trace
        hist := ⟨by rw [hfs2]; exact hc.hist.1, by rw [htr2]; exact hc.hist.2⟩
        ans := hc.ans
      }
      have hr12 : sm2.readReg64 (.gpr 12#5) = s.readReg64 (.gpr 12#5) := by
        simp only [hsm2, wp_norm, arm64_norm, hc26, hsm_r25]
      have hr10 : sm2.readReg64 (.gpr 10#5) = s.readReg64 (.gpr 10#5) := by
        simp only [hsm2, wp_norm, arm64_norm, hc25, hsm_r24]
      have hr23 : sm2.readReg64 (.gpr 23#5) = s.readReg64 (.gpr 23#5) := by
        simp only [hsm2, wp_norm, arm64_norm]
      have hr27 : sm2.readReg64 (.gpr 27#5) = s.readReg64 (.gpr 27#5) := by
        simp only [hsm2, wp_norm, arm64_norm, hc28, hsm_r27]
      have hr16 : sm2.readReg64 (.gpr 16#5) = s.readReg64 (.gpr 16#5) := by
        simp only [hsm2, wp_norm, arm64_norm, hc22, hsm_r22]
      have hr14 : sm2.readReg64 (.gpr 14#5) = s.readReg64 (.gpr 14#5) := by
        simp only [hsm2, wp_norm, arm64_norm, hc24, hsm_r23]
      have hr15 : sm2.readReg64 (.gpr 15#5) = s.readReg64 (.gpr 15#5) := by
        simp only [hsm2, wp_norm, arm64_norm, hc27, hsm_r26]
      have hr28 : sm2.readReg64 (.gpr 28#5) = s.readReg64 (.gpr 28#5) := by
        simp only [hsm2, wp_norm, arm64_norm, hc29, hsm_r28]
      clear hsm2
      have hre190 : ((fsp + 0x190#64) ↦₆₄ s.readReg64 (.gpr 11#5)) ⊢ memRegion (fsp + 0x190#64) 8 :=
        pointsTo64_entails_memRegion _ _
      have hre1a8 : ((fsp + 0x1a8#64) ↦₆₄ s.readReg64 (.gpr 13#5)) ∗
          ((fsp + 0x1b0#64) ↦₆₄ s.readReg64 (.gpr 23#5)) ⊢ memRegion (fsp + 0x1a8#64) 16 := by
        have ha2 : fsp + 0x1b0#64 = (fsp + 0x1a8#64) + 8#64 := by bv_omega
        rw [ha2]; exact r1b_cells2_to_region16 _ _ _
      refine sepWPp_weaken_pre ?_
        (r1b_cleanup_2b24_placed (st := M.stepEvents (rustDeallocEvents kpkCap.toNat 1) st)
          (v188 := v188) (spkCap := spkCap) (spkPtr := spkPtr) (spkLen := spkLen)
          (spkBs := spkBs) (regCap := regCap) (regPtr := regPtr) (regLen := regLen) (regBs := regBs)
          hh hdrop hbnd hc_m2 hpanic fun sf2 evs2 hfo2 hrej2 => ?_)
      · rw [hr12, hr10, hr23, hr27, hr16, hr14, hr15, hr28]
        rw [r1b_errCommon_atState_eq, herrCore, r1b_fold_low4]
        dsimp only [fsp] at hre190 hre1a8 ⊢
        refine Entails.trans (Entails.of_eq (show _ =
          r1b_SpePayload A.repAlloc (s.readReg64 (.gpr 12#5))
            (s.readReg64 (.gpr 10#5)) (s.readReg64 (.gpr 23#5))
            (s.readReg64 (.gpr 27#5)) (s.readReg64 (.gpr 16#5))
            (s.readReg64 (.gpr 14#5)) (s.readReg64 (.gpr 15#5))
            (s.readReg64 (.gpr 28#5)) v188 ∗
          ownedBytes A.repAlloc spkCap spkPtr spkLen spkBs ∗
          ownedBytes A.repAlloc regCap regPtr regLen regBs ∗
          (errCore ∗ stackAt (runFsp s0) (resStack - runFrame) ∗
            A.pool lim (M.stepEvents (rustDeallocEvents kpkCap.toNat 1) st) sm2 ∗ anyHeap) ∗
          r1b_errLow4 (runFsp s0) ∗
          ((runFsp s0 + 0x168#64) ↦₆₄ spkPtr) ∗ ((runFsp s0 + 0x170#64) ↦₆₄ spkCap) ∗
          memRegion (runFsp s0 + 0x178#64) 8 ∗
          ((runFsp s0 + 0x188#64) ↦₆₄ v188) ∗
          ((runFsp s0 + 0x190#64) ↦₆₄ s.readReg64 (.gpr 11#5)) ∗
          ((runFsp s0 + 0x198#64) ↦₆₄ regCap) ∗ ((runFsp s0 + 0x1a0#64) ↦₆₄ regPtr) ∗
          (((runFsp s0 + 0x1a8#64) ↦₆₄ s.readReg64 (.gpr 13#5)) ∗
            ((runFsp s0 + 0x1b0#64) ↦₆₄ s.readReg64 (.gpr 23#5))) ∗
          memRegion (runFsp s0 + 0x4d0#64) 48 by sep_ac_rfl)) ?_
        exact sepConj_mono_right (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
          (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
            (sepConj_mono_right
              (sepConj_mono hre190
                (sepConj_mono_right (sepConj_mono_right
                  (sepConj_mono_left hre1a8))))))))))))
      · rw [← M.stepEvents_append]
        exact hrej sf2 (rustDeallocEvents kpkCap.toNat 1 ++ evs2)
          (FreeOnlyEvs.append (FreeOnlyEvs.singleton 1 kpkCap.toNat) hfo2) hrej2
    )
  )

theorem r1b_cleanup_2adc_placed [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {st : M.σ}
    {H : LibsignalHooks} {B : RunBudgets}
    {g : RunCall} {d : Init1Data} {s0 s : State} {resStack : Nat}
    {v188 kpkCap kpkPtr kpkLen spkCap spkPtr spkLen regCap regPtr regLen : BitVec 64}
    {kpkBs spkBs regBs : List (BitVec 8)}
    {Q Qp : State → SepProp → Prop} {oom : State → SepProp}
    (hh : RunHooksPlaced A lim H) (hdrop : DropSpeOwnedOkAtBlock (runProgPlaced H) A lim)
    (hbnd : r1b_StackBounds B resStack)
    (hc : r1b_ErrCtxPlaced r1b_CodeOk g d s0 s 0x2adc)
    (hx1 : s.readReg64 (.gpr 1#5) = kpkCap)
    (hx26 : s.readReg64 (.gpr 26#5) = kpkPtr)
    (hpanic : PanicK g s0 Qp)
    (hrej : ∀ (sf : State) (evs : List AllocEvent),
      FreeOnlyEvs evs →
      AtRejectPlaced r1b_CodeOk g StoresGhost.opened .postDispatch s0 sf →
      SepWPp (runProgPlaced H) (s0.readReg64 .lr) sf
        (rejectMem (A.atState lim (M.stepEvents evs st) sf)
          g StoresGhost.opened .postDispatch s0 resStack)
        Q Qp oom) :
    let fsp := runFsp s0
    SepWPp (runProgPlaced H) (s0.readReg64 .lr) s
      (r1b_SpePayload A.repAlloc (s.readReg64 (.gpr 12#5))
          (s.readReg64 (.gpr 10#5)) (s.readReg64 (.gpr 23#5))
          (s.readReg64 (.gpr 27#5)) (s.readReg64 (.gpr 16#5))
          (s.readReg64 (.gpr 14#5)) (s.readReg64 (.gpr 15#5))
          (s.readReg64 (.gpr 28#5)) v188 ∗
        ownedBytes A.repAlloc kpkCap kpkPtr kpkLen kpkBs ∗
        ownedBytes A.repAlloc spkCap spkPtr spkLen spkBs ∗
        ownedBytes A.repAlloc regCap regPtr regLen regBs ∗
        r1b_errCommon (A.atState lim st s) g d s0 resStack ∗
        memRegion (fsp + 0x110#64) 8 ∗ memRegion (fsp + 0x11c#64) 4 ∗
        memRegion (fsp + 0x120#64) 16 ∗ memRegion (fsp + 0x150#64) 16 ∗
        ((fsp + 0x168#64) ↦₆₄ spkPtr) ∗ ((fsp + 0x170#64) ↦₆₄ spkCap) ∗
        memRegion (fsp + 0x178#64) 8 ∗
        ((fsp + 0x188#64) ↦₆₄ v188) ∗ memRegion (fsp + 0x190#64) 8 ∗
        ((fsp + 0x198#64) ↦₆₄ regCap) ∗ ((fsp + 0x1a0#64) ↦₆₄ regPtr) ∗
        memRegion (fsp + 0x1a8#64) 16 ∗ memRegion (fsp + 0x4d0#64) 48)
      Q Qp oom := by
  by_cases hcap : kpkCap = 0#64
  · subst hcap; exact r1b_cleanup_2adc_cap0_placed hh hdrop hbnd hc hx1 hpanic hrej
  · exact r1b_cleanup_2adc_capNe_placed hh hdrop hbnd hc hx1 hx26 hcap hpanic hrej

theorem r1b_cleanup_2adc_placed_env [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {st : M.σ}
    {EnvAt : StoresGhost → RejectKind → M.σ → Prop}
    {H : LibsignalHooks} {B : RunBudgets}
    {g : RunCall} {d : Init1Data} {s0 s : State} {resStack : Nat}
    {v188 kpkCap kpkPtr kpkLen spkCap spkPtr spkLen regCap regPtr regLen : BitVec 64}
    {kpkBs spkBs regBs : List (BitVec 8)}
    {Q Qp : State → SepProp → Prop} {oom : State → SepProp}
    (hh : RunHooksPlaced A lim H) (hdrop : DropSpeOwnedOkAtBlock (runProgPlaced H) A lim)
    (hbnd : r1b_StackBounds B resStack)
    (hc : r1b_ErrCtxPlaced r1b_CodeOk g d s0 s 0x2adc)
    (hx1 : s.readReg64 (.gpr 1#5) = kpkCap)
    (hx26 : s.readReg64 (.gpr 26#5) = kpkPtr)
    (hpanic : PanicK g s0 Qp)
    (hrej : RejectKPlacedEnv r1b_CodeOk H A lim EnvAt g s0 resStack Q Qp oom)
    (henv : ∀ evs, FreeOnlyEvs evs → EnvAt StoresGhost.opened .postDispatch (M.stepEvents evs st)) :
    let fsp := runFsp s0
    SepWPp (runProgPlaced H) (s0.readReg64 .lr) s
      (r1b_SpePayload A.repAlloc (s.readReg64 (.gpr 12#5))
          (s.readReg64 (.gpr 10#5)) (s.readReg64 (.gpr 23#5))
          (s.readReg64 (.gpr 27#5)) (s.readReg64 (.gpr 16#5))
          (s.readReg64 (.gpr 14#5)) (s.readReg64 (.gpr 15#5))
          (s.readReg64 (.gpr 28#5)) v188 ∗
        ownedBytes A.repAlloc kpkCap kpkPtr kpkLen kpkBs ∗
        ownedBytes A.repAlloc spkCap spkPtr spkLen spkBs ∗
        ownedBytes A.repAlloc regCap regPtr regLen regBs ∗
        r1b_errCommon (A.atState lim st s) g d s0 resStack ∗
        memRegion (fsp + 0x110#64) 8 ∗ memRegion (fsp + 0x11c#64) 4 ∗
        memRegion (fsp + 0x120#64) 16 ∗ memRegion (fsp + 0x150#64) 16 ∗
        ((fsp + 0x168#64) ↦₆₄ spkPtr) ∗ ((fsp + 0x170#64) ↦₆₄ spkCap) ∗
        memRegion (fsp + 0x178#64) 8 ∗
        ((fsp + 0x188#64) ↦₆₄ v188) ∗ memRegion (fsp + 0x190#64) 8 ∗
        ((fsp + 0x198#64) ↦₆₄ regCap) ∗ ((fsp + 0x1a0#64) ↦₆₄ regPtr) ∗
        memRegion (fsp + 0x1a8#64) 16 ∗ memRegion (fsp + 0x4d0#64) 48)
      Q Qp oom :=
  r1b_cleanup_2adc_placed hh hdrop hbnd hc hx1 hx26 hpanic fun sf evs hfo hrej_f =>
    hrej sf (M.stepEvents evs st) StoresGhost.opened .postDispatch hrej_f (henv evs hfo)

/-! ## Error Exits (`0x1aa8 → 0x2b28`, `0x1b60 → 0x2adc`) -/

theorem r1b_err_1aa8_placed [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {st : M.σ}
    {EnvAt : StoresGhost → RejectKind → M.σ → Prop}
    {H : LibsignalHooks} {B : RunBudgets}
    {g : RunCall} {d : Init1Data} {s0 s : State} {resStack : Nat}
    {eCap ePtr spkCap spkPtr regCap regPtr : BitVec 64}
    {eBs spkBs regBs : List (BitVec 8)}
    {Q Qp : State → SepProp → Prop} {oom : State → SepProp}
    (hh : RunHooksPlaced A lim H)
    (hdrop : DropSpeOwnedOkAtBlock (runProgPlaced H) A lim)
    (hbnd : r1b_StackBounds B resStack)
    (hc : r1b_ErrCtxPlaced r1b_CodeOk g d s0 s 0x1aa8)
    (hx12 : s.readReg64 (.gpr 12#5) = speWord 1)
    (hx9 : s.readReg64 (.gpr 9#5) = eCap)
    (hx26 : s.readReg64 (.gpr 26#5) = ePtr)
    (hx2 : s.readReg64 .x2 = BitVec.ofNat 64 eBs.length)
    (henv : ∀ evsFree, FreeOnlyEvs evsFree →
      EnvAt StoresGhost.opened .postDispatch (M.stepEvents evsFree st))
    (hpanic : PanicK g s0 Qp)
    (hrej : RejectKPlacedEnv r1b_CodeOk H A lim EnvAt g s0 resStack Q Qp oom) :
    let fsp := runFsp s0
    SepWPp (runProgPlaced H) (s0.readReg64 .lr) s
      (((fsp + 0x4d0#64) ↦₆₄ speWord 1) ∗
        ((fsp + 0x4d8#64) ↦₆₄ eCap) ∗ ((fsp + 0x4e0#64) ↦₆₄ ePtr) ∗
        ((fsp + 0x4e8#64) ↦₆₄ BitVec.ofNat 64 eBs.length) ∗
        memRegion (fsp + 0x4f0#64) 16 ∗
        ownedBytes A.repAlloc eCap ePtr (BitVec.ofNat 64 eBs.length) eBs ∗
        ownedBytes A.repAlloc spkCap spkPtr (BitVec.ofNat 64 spkBs.length) spkBs ∗
        ownedBytes A.repAlloc regCap regPtr (BitVec.ofNat 64 regBs.length) regBs ∗
        r1b_errCommon (A.atState lim st s) g d s0 resStack ∗
        memRegion (fsp + 0x110#64) 8 ∗ memRegion (fsp + 0x11c#64) 4 ∗
        memRegion (fsp + 0x120#64) 16 ∗ memRegion (fsp + 0x150#64) 16 ∗
        ((fsp + 0x168#64) ↦₆₄ spkPtr) ∗ ((fsp + 0x170#64) ↦₆₄ spkCap) ∗
        memRegion (fsp + 0x178#64) 8 ∗ memRegion (fsp + 0x188#64) 16 ∗
        ((fsp + 0x198#64) ↦₆₄ regCap) ∗ ((fsp + 0x1a0#64) ↦₆₄ regPtr) ∗
        memRegion (fsp + 0x1a8#64) 16)
      Q Qp oom := by
  intro fsp
  let _ := hx12; let _ := hx9; let _ := hx26; let _ := hx2
  rw [r1b_errCommon_atState_eq]
  generalize herrCore : r1b_errCore A.repAlloc g d s0 = errCore
  have hst := hc.st
  have hal : fsp &&& 15#64 = 0#64 := r1b_fsp_align hst.sp hst.spAligned
  have hsplit16 := r1b_region16_to_cells (fsp + 0x4f0#64)
  have h4f8 : (fsp + 0x4f0#64) + 8#64 = fsp + 0x4f8#64 := by bv_omega
  rw [h4f8] at hsplit16
  rw [hsplit16]
  simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
  refine SepWPp.exists_elim fun w4 => SepWPp.exists_elim fun w5 => ?_
  have hpc := hst.pc; change s.pc = (blkPl_579).base + 0x1aa8#64 at hpc
  have hrun := hst.run; have hsp : s.sp = fsp := hst.sp
  apply r1b_seq_lscro_oom (mid := (blkPl_579).base + 0x2b28#64) hst.inv
  dsimp only [runProgPlaced, lsProg_579]
  by_vm_open (
    wp_steps
    refine SepWP.done (by simp only [wp_norm, arm64_norm, *]; try bv_omega)
      (by simp only [wp_norm, arm64_norm, *])
      ⟨by simp only [wp_norm, arm64_norm, *], fun hvm => ?_⟩
    refine r1b_bind_state_placed fun sm hsm hinv_m => ?_
    rw [← hsm] at hvm
    rw [← A.pool_transport lim st s sm hvm]
    change SepWPp (runProgPlaced H) _ _ _ _ _ _
    have hc_m : r1b_ErrCtxPlaced r1b_CodeOk g d s0 sm 0x2b28 := hc.of_step
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
    have h4d0 :
        ((fsp + 0x4d0#64) ↦₆₄ speWord 1) ∗ ((fsp + 0x4d8#64) ↦₆₄ eCap) ∗
          ((fsp + 0x4e0#64) ↦₆₄ ePtr) ∗
          ((fsp + 0x4e8#64) ↦₆₄ BitVec.ofNat 64 eBs.length) ∗
          ((fsp + 0x4f0#64) ↦₆₄ w4) ∗ ((fsp + 0x4f8#64) ↦₆₄ w5) ⊢
          memRegion (fsp + 0x4d0#64) 48 := by
      simpa only [BitVec.add_assoc, BitVec.reduceAdd, sepConj_assoc] using
        r1b_cells6_to_region48 (fsp + 0x4d0#64) (speWord 1) eCap ePtr
          (BitVec.ofNat 64 eBs.length) w4 w5
    have hpay : ownedBytes A.repAlloc eCap ePtr (BitVec.ofNat 64 eBs.length) eBs ⊢
        r1b_SpePayload A.repAlloc (sm.readReg64 (.gpr 12#5)) (sm.readReg64 (.gpr 10#5))
          (sm.readReg64 (.gpr 23#5)) (sm.readReg64 (.gpr 27#5))
          (sm.readReg64 (.gpr 16#5)) (sm.readReg64 (.gpr 14#5))
          (sm.readReg64 (.gpr 15#5)) (sm.readReg64 (.gpr 28#5))
          (sm.readReg64 (.gpr 2#5)) := by
      simp only [hsm, wp_norm, arm64_norm]
      try rw [hx12]
      try rw [hx2]
      r1b_prove_spe_str
    have hcl := r1b_cleanup_2b28_placed_env (st := st) (spkCap := spkCap) (spkPtr := spkPtr)
      (spkLen := BitVec.ofNat 64 spkBs.length) (spkBs := spkBs)
      (regCap := regCap) (regPtr := regPtr)
      (regLen := BitVec.ofNat 64 regBs.length) (regBs := regBs)
      hh hdrop hbnd hc_m hpanic hrej henv
    dsimp only at hcl
    rw [r1b_errCommon_atState_eq, herrCore] at hcl
    refine sepWPp_weaken_pre ?_ hcl
    exact r1b_entails_frame_ka (by r1b_ac) (sepConj_mono hpay h4d0) (by r1b_ac)
  )

theorem r1b_err_1b60_placed [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {st : M.σ}
    {EnvAt : StoresGhost → RejectKind → M.σ → Prop}
    {H : LibsignalHooks} {B : RunBudgets}
    {g : RunCall} {d : Init1Data} {s0 s : State} {resStack : Nat}
    {eCap ePtr kpkCap kpkPtr spkCap spkPtr regCap regPtr v188_in : BitVec 64}
    {eBs kpkBs spkBs regBs : List (BitVec 8)}
    {Q Qp : State → SepProp → Prop} {oom : State → SepProp}
    (hh : RunHooksPlaced A lim H)
    (hdrop : DropSpeOwnedOkAtBlock (runProgPlaced H) A lim)
    (hbnd : r1b_StackBounds B resStack)
    (hc : r1b_ErrCtxPlaced r1b_CodeOk g d s0 s 0x1b60)
    (hx12 : s.readReg64 (.gpr 12#5) = speWord 1)
    (hx10 : s.readReg64 (.gpr 10#5) = eCap)
    (hx9 : s.readReg64 (.gpr 9#5) = ePtr)
    (hx23 : s.readReg64 (.gpr 23#5) = ((BitVec.ofNat 64 eBs.length).truncate 32).zeroExtend 64)
    (hx26 : s.readReg64 (.gpr 26#5) = kpkPtr)
    (henv : ∀ evsFree, FreeOnlyEvs evsFree →
      EnvAt StoresGhost.opened .postDispatch (M.stepEvents evsFree st))
    (hpanic : PanicK g s0 Qp)
    (hrej : RejectKPlacedEnv r1b_CodeOk H A lim EnvAt g s0 resStack Q Qp oom) :
    let fsp := runFsp s0
    SepWPp (runProgPlaced H) (s0.readReg64 .lr) s
      (((fsp + 0x4d0#64) ↦₆₄ speWord 1) ∗
        ((fsp + 0x4d8#64) ↦₆₄ eCap) ∗ ((fsp + 0x4e0#64) ↦₆₄ ePtr) ∗
        ((fsp + 0x4e8#64) ↦₆₄ BitVec.ofNat 64 eBs.length) ∗
        memRegion (fsp + 0x4f0#64) 16 ∗
        ownedBytes A.repAlloc eCap ePtr (BitVec.ofNat 64 eBs.length) eBs ∗
        ownedBytes A.repAlloc kpkCap kpkPtr (BitVec.ofNat 64 kpkBs.length) kpkBs ∗
        ownedBytes A.repAlloc spkCap spkPtr (BitVec.ofNat 64 spkBs.length) spkBs ∗
        ownedBytes A.repAlloc regCap regPtr (BitVec.ofNat 64 regBs.length) regBs ∗
        r1b_errCommon (A.atState lim st s) g d s0 resStack ∗
        memRegion (fsp + 0x110#64) 8 ∗ memRegion (fsp + 0x11c#64) 4 ∗
        memRegion (fsp + 0x120#64) 16 ∗
        ((fsp + 0x150#64) ↦₆₄ kpkCap) ∗ memRegion (fsp + 0x158#64) 8 ∗
        ((fsp + 0x168#64) ↦₆₄ spkPtr) ∗ ((fsp + 0x170#64) ↦₆₄ spkCap) ∗
        memRegion (fsp + 0x178#64) 8 ∗
        ((fsp + 0x188#64) ↦₆₄ v188_in) ∗ memRegion (fsp + 0x190#64) 8 ∗
        ((fsp + 0x198#64) ↦₆₄ regCap) ∗ ((fsp + 0x1a0#64) ↦₆₄ regPtr) ∗
        memRegion (fsp + 0x1a8#64) 16)
      Q Qp oom := by
  intro fsp
  let _ := hx12; let _ := hx10; let _ := hx9; let _ := hx23; let _ := hx26
  rw [r1b_errCommon_atState_eq]
  generalize herrCore : r1b_errCore A.repAlloc g d s0 = errCore
  have hst := hc.st
  have hal : fsp &&& 15#64 = 0#64 := r1b_fsp_align hst.sp hst.spAligned
  have hsplit16 := r1b_region16_to_cells (fsp + 0x4f0#64)
  have h4f8 : (fsp + 0x4f0#64) + 8#64 = fsp + 0x4f8#64 := by bv_omega
  rw [h4f8] at hsplit16
  have he8 : ((fsp + 0x4e8#64) ↦₆₄ BitVec.ofNat 64 eBs.length) =
      ((fsp + 0x4e8#64) ↦₃₂ (BitVec.ofNat 64 eBs.length).truncate 32) ∗
        ((fsp + 0x4ec#64) ↦₃₂ ((BitVec.ofNat 64 eBs.length) >>> 32).truncate 32) := by
    have hz := r1b_u64_split32 (fsp + 0x4e8#64) (BitVec.ofNat 64 eBs.length)
    have ha : (fsp + 0x4e8#64) + 4#64 = fsp + 0x4ec#64 := by bv_omega
    rwa [ha] at hz
  rw [he8, hsplit16]
  simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
  refine SepWPp.exists_elim fun w4 => SepWPp.exists_elim fun w5 => ?_
  have hpc := hst.pc; change s.pc = (blkPl_579).base + 0x1b60#64 at hpc
  have hrun := hst.run; have hsp : s.sp = fsp := hst.sp
  apply r1b_seq_lscro_oom (mid := (blkPl_579).base + 0x2adc#64) hst.inv
  dsimp only [runProgPlaced, lsProg_579]
  by_vm_open (
    wp_steps
    refine SepWP.done (by simp only [wp_norm, arm64_norm, *]; try bv_omega)
      (by simp only [wp_norm, arm64_norm, *])
      ⟨by simp only [wp_norm, arm64_norm, *], fun hvm => ?_⟩
    refine r1b_bind_state_placed fun sm hsm hinv_m => ?_
    rw [← hsm] at hvm
    rw [← A.pool_transport lim st s sm hvm]
    change SepWPp (runProgPlaced H) _ _ _ _ _ _
    have hc_m : r1b_ErrCtxPlaced r1b_CodeOk g d s0 sm 0x2adc := hc.of_step
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
    have h4d0 :
        ((fsp + 0x4d0#64) ↦₆₄ speWord 1) ∗ ((fsp + 0x4d8#64) ↦₆₄ eCap) ∗
          ((fsp + 0x4e0#64) ↦₆₄ ePtr) ∗
          (((fsp + 0x4e8#64) ↦₃₂ (BitVec.ofNat 64 eBs.length).truncate 32) ∗
            ((fsp + 0x4ec#64) ↦₃₂ ((BitVec.ofNat 64 eBs.length) >>> 32).truncate 32)) ∗
          ((fsp + 0x4f0#64) ↦₆₄ w4) ∗ ((fsp + 0x4f8#64) ↦₆₄ w5) ⊢
          memRegion (fsp + 0x4d0#64) 48 := by
      rw [← he8]
      simpa only [BitVec.add_assoc, BitVec.reduceAdd, sepConj_assoc] using
        r1b_cells6_to_region48 (fsp + 0x4d0#64) (speWord 1) eCap ePtr
          (BitVec.ofNat 64 eBs.length) w4 w5
    have h150 : ((fsp + 0x150#64) ↦₆₄ kpkCap) ∗ memRegion (fsp + 0x158#64) 8 ⊢
        memRegion (fsp + 0x150#64) 16 := by
      simpa only [BitVec.add_assoc, BitVec.reduceAdd] using
        r1b_cell64_cons (a := fsp + 0x150#64) kpkCap (n := 8) (by decide)
    have hpay : ownedBytes A.repAlloc eCap ePtr (BitVec.ofNat 64 eBs.length) eBs ⊢
        r1b_SpePayload A.repAlloc (sm.readReg64 (.gpr 12#5)) (sm.readReg64 (.gpr 10#5))
          (sm.readReg64 (.gpr 23#5)) (sm.readReg64 (.gpr 27#5))
          (sm.readReg64 (.gpr 16#5)) (sm.readReg64 (.gpr 14#5))
          (sm.readReg64 (.gpr 15#5)) (sm.readReg64 (.gpr 28#5))
          (sm.readReg64 (.gpr 9#5)) := by
      simp only [hsm, wp_norm, arm64_norm]
      try rw [hx12]
      try rw [hx10]
      r1b_prove_spe_str
    rw [show ((fsp + 0x188#64) ↦₆₄ ((BitVec.ofNat 64 eBs.length).truncate 32).zeroExtend 64) =
      ((fsp + 0x188#64) ↦₆₄ sm.readReg64 (.gpr 9#5)) by
      simp only [hsm, wp_norm, arm64_norm]]
    have hcl := r1b_cleanup_2adc_placed_env (st := st) (v188 := sm.readReg64 (.gpr 9#5))
      (kpkCap := kpkCap) (kpkPtr := kpkPtr)
      (kpkLen := BitVec.ofNat 64 kpkBs.length) (kpkBs := kpkBs)
      (spkCap := spkCap) (spkPtr := spkPtr)
      (spkLen := BitVec.ofNat 64 spkBs.length) (spkBs := spkBs)
      (regCap := regCap) (regPtr := regPtr)
      (regLen := BitVec.ofNat 64 regBs.length) (regBs := regBs)
      hh hdrop hbnd hc_m
      (by simp only [hsm, wp_norm, arm64_norm])
      (by solve | simp only [hsm, wp_norm, arm64_norm] | simpa only [hsm, wp_norm, arm64_norm] using hx26)
      hpanic hrej henv
    dsimp only at hcl
    rw [r1b_errCommon_atState_eq, herrCore] at hcl
    refine sepWPp_weaken_pre ?_ hcl
    exact r1b_entails_frame_ka (by r1b_ac) (sepConj_mono hpay (sepConj_mono h4d0 h150)) (by r1b_ac)
  )

end LibsignalBinary.Proofs.SignalSession.Cli.Run.Compose.Arms.R1b.ReadKpkPlacedBudgetAux
