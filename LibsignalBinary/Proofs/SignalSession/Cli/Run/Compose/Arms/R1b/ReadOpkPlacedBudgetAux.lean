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
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Compose.Arms.R1b.ErrCleanupUpperPlacedBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Compose.Arms.R1b.ReadKpkPlaced
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Compose.Arms.R1b.ReadKpkPlacedBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Compose.Arms.R1b.ReadOpkPlaced
import Arm64.Trusted.Spec.Hoare
import Arm64.Trusted.Spec.SepLogic
import LibsignalBinary.Proofs.Common.SharedHelpers
meta import LibsignalBinary.Proofs.Common.SharedHelpers -- shake: keep
import LibsignalBinary.Proofs.SignalSession.Cli.Main.Proofs.M4Layout

/-!
# Budget-Threaded Stage 3 (`one-time-pre-key`) Error Exits for Arm `R1b`

Verifies `r1b_err_1b98_placed` (`0x1b98 → 0x2adc`), `r1b_err_2420_placed` (`0x2420 → 0x2aa8`), and
`r1b_opk_deser_err_1360_placed` (`0x1360 → 0x2a88 / 0x2a60 / 0x2a8c`) on Block `579` under
`[LibsignalPlacement]` and `RustCliAllocBudget M`.
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 200000
set_option linter.unreachableTactic false
set_option linter.unusedTactic false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

namespace LibsignalBinary.Proofs.SignalSession.Cli.Run.Compose.Arms.R1b.ReadOpkPlacedBudgetAux

open Arm64 Arm64.Process ProofLib ProofLib.ProgramReflection SepProp
open CryptoGames.LibsignalSession (PublicKey SignalProtocolError)
open CryptoVerification (LibsignalHooks LibsignalPlacement)
open CryptoVerification.LibsignalTripleRatchet.Wire
  (deserializeResult33At memRegion33_of_err_badKeyLength memRegion33_of_err_badKeyType
   memRegion33_of_err_base)
open CryptoVerification.LibsignalTripleRatchetRepr (speWord)
open CryptoVerification.SignalSession.Cli (StoresGhost)
open CryptoVerification.SignalSession.Cli.MainHops (RunCall ownedBytes sepWPp_weaken_pre)
open CryptoVerification.SignalSession.Cli.Run.Placed
  (blkLib_eq_579 blkPC_579 blkPl_579 lsProg_579)
open CryptoVerification.SignalSession.Cli.RunCompose
  (AtRejectPlaced Init1Data PanicK RejectKind r1b_CodeOk r1b_ErrCtxPlaced
   r1b_SpePayload r1b_SpePayload_str r1b_StackBounds r1b_bind_state_placed
   r1b_cells2_to_region16 r1b_cells6_to_region48 r1b_entails_frame_core
   r1b_errCommon r1b_errCore r1b_fsp_align r1b_join_region
   r1b_region16_to_cells rejectMem runFsp runPcPlaced_eq runProgPlaced)
open CryptoVerification.SignalSession.Cli.RunSkeleton (RunBudgets)
open LibsignalBinary.Heap
  (AllocCostModel AllocEvent BudgetLimits FreeOnlyEvs RustCliAllocBudget VmPreserved)
open LibsignalBinary.Proofs.Placed.BudgetPoolSync (hooksException sepWP_seg_ls_vm)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Compose.Arms.R1b.ErrCleanupPlacedBudget
  (r1b_errCommon_atState_eq)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Compose.Arms.R1b.ErrCleanupUpperPlacedBudget
  (r1b_cleanup_2a60_placed r1b_cleanup_2a88_placed r1b_cleanup_2a8c_placed r1b_cleanup_2aa8_placed)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Compose.Arms.R1b.ReadKpkPlacedBudgetAux
  (r1b_cleanup_2adc_placed r1b_seq_lscro_oom)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Compose.Arms.R1b.ReadRegSpkPlacedBudgetAux
  (blk579_noSvc0)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Compose.HopsPlacedBudget (RejectKPlacedEnv)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DropSpeOwnedPlacedBudget
  (DropSpeOwnedOkAtBlock)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.SkeletonPlacedBudget (RunHooksPlaced)

attribute [local irreducible] Program.fetch Program.externAt?
attribute [local simp, local arm64_norm, local wp_norm] runPcPlaced_eq BitVec.ofNat_eq_ofNat

local macro (priority := high) "r1b_ac" : tactic =>
  `(tactic| ((try dsimp +zetaDelta only) <;> first | rfl | simp only [emp_sepConj] | sep_ac_rfl))

private meta def r1bStripLetsRA : Nat → Lean.Expr → Lean.Expr
  | 0, e => e
  | n + 1, .letE _ _ v b _ => r1bStripLetsRA n (b.instantiate1 v)
  | n + 1, .mdata _ e => r1bStripLetsRA n e
  | _, e => e

private meta def r1bSplitSepRA : Nat → Lean.Expr → Lean.Expr → Array Lean.Expr
  | 0, _, e => #[e]
  | fuel + 1, sepSample, e =>
    let e := r1bStripLetsRA 64 e
    let fn := sepSample.getAppFn.constName!
    let ar := sepSample.getAppNumArgs
    if e.isAppOfArity fn ar then
      r1bSplitSepRA fuel sepSample (e.getArg! (ar - 2)) ++
        r1bSplitSepRA fuel sepSample (e.getArg! (ar - 1))
    else #[e]

private meta def r1bIsDefEqPureRA (x a : Lean.Expr) : Lean.Elab.TermElabM Bool := do
  let x := r1bStripLetsRA 64 x; let a := r1bStripLetsRA 64 a
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

private meta def r1bComputeRestRA (ctxName : String) (p a1 : Lean.Expr) :
    Lean.Elab.TermElabM Lean.Expr := do
  let sepTy := Lean.mkConst ``SepProp []
  let sepSample ← Lean.Elab.Term.elabTerm (← `(emp ∗ emp)) (some sepTy)
  let empExpr ← Lean.Elab.Term.elabTerm (← `(emp)) (some sepTy)
  let ps := (r1bSplitSepRA 64 sepSample (← Lean.instantiateMVars p)).toList
  let a1s := (r1bSplitSepRA 64 sepSample (← Lean.instantiateMVars a1)).toList
  let mut rem := ps
  for a in a1s do
    let mut removed := false
    let mut next : List Lean.Expr := []
    for x in rem do
      if !removed && (← r1bIsDefEqPureRA x a) then removed := true
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

local elab (priority := high) "r1b_entails_frame_ra " t1:term:arg h:term:arg t2:term:arg :
    term <= expectedType => do
  let exp ← Lean.instantiateMVars expectedType
  if exp.isMVar then Lean.Elab.Term.tryPostpone
  let entSample ← Lean.Elab.Term.elabTerm (← `(emp ⊢ emp)) none
  let ear := entSample.getAppNumArgs
  let expS := r1bStripLetsRA 64 exp
  let p := expS.getArg! (ear - 2)
  let q := expS.getArg! (ear - 1)
  if (← Lean.instantiateMVars p).isMVar then Lean.Elab.Term.tryPostpone
  if (← Lean.instantiateMVars q).isMVar then Lean.Elab.Term.tryPostpone
  let hExpr ← Lean.Elab.Term.elabTerm h none
  let hTy := r1bStripLetsRA 64 (← Lean.instantiateMVars (← Lean.Meta.inferType hExpr))
  let a1 := hTy.getArg! (ear - 2)
  let a2 := hTy.getArg! (ear - 1)
  let r ← r1bComputeRestRA "r1b_entails_frame" p a1
  let sepTy := Lean.mkConst ``SepProp []
  let empExpr ← Lean.Elab.Term.elabTerm (← `(emp)) (some sepTy)
  let sepSample ← Lean.Elab.Term.elabTerm (← `(emp ∗ emp)) (some sepTy)
  let sar := sepSample.getAppNumArgs
  let mkSep (x y : Lean.Expr) : Lean.Expr :=
    sepSample.withApp fun f args => Lean.mkAppN f (args.extract 0 (sar - 2) ++ #[x, y])
  let rIsEmp ← r1bIsDefEqPureRA r empExpr
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

/-! ## Read and Length Error Exits (`0x1b98 → 0x2adc`, `0x2420 → 0x2aa8`) -/

theorem r1b_err_1b98_placed [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {st : M.σ}
    {H : LibsignalHooks} {B : RunBudgets}
    {g : RunCall} {d : Init1Data} {s0 s : State} {resStack : Nat}
    {eCap ePtr kpkCap kpkPtr spkCap spkPtr regCap regPtr v158 v188_in : BitVec 64}
    {eBs kpkBs spkBs regBs : List (BitVec 8)}
    {Q Qp : State → SepProp → Prop} {oom : State → SepProp}
    (hh : RunHooksPlaced A lim H) (hdrop : DropSpeOwnedOkAtBlock (runProgPlaced H) A lim)
    (hbnd : r1b_StackBounds B resStack)
    (hc : r1b_ErrCtxPlaced r1b_CodeOk g d s0 s 0x1b98)
    (hx12 : s.readReg64 (.gpr 12#5) = speWord 1)
    (hx1 : s.readReg64 .x1 = eCap)
    (hx14 : s.readReg64 (.gpr 14#5) = ePtr)
    (hx25 : s.readReg64 (.gpr 25#5) = BitVec.ofNat 64 eBs.length)
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
        ((fsp + 0x150#64) ↦₆₄ kpkCap) ∗ ((fsp + 0x158#64) ↦₆₄ v158) ∗
        ((fsp + 0x168#64) ↦₆₄ spkPtr) ∗ ((fsp + 0x170#64) ↦₆₄ spkCap) ∗
        memRegion (fsp + 0x178#64) 8 ∗
        ((fsp + 0x188#64) ↦₆₄ v188_in) ∗ memRegion (fsp + 0x190#64) 8 ∗
        ((fsp + 0x198#64) ↦₆₄ regCap) ∗ ((fsp + 0x1a0#64) ↦₆₄ regPtr) ∗
        memRegion (fsp + 0x1a8#64) 16)
      Q Qp oom := by
  intro fsp
  let _ := hx12; let _ := hx1; let _ := hx14; let _ := hx25; let _ := hx26
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
  have hpc := hst.pc; change s.pc = (blkPl_579).base + 0x1b98#64 at hpc
  have hrun := hst.run; have hsp : s.sp = fsp := hst.sp
  apply r1b_seq_lscro_oom (mid := (blkPl_579).base + 0x2adc#64) hst.inv
  dsimp only [runProgPlaced, lsProg_579]
  apply sepWP_seg_ls_vm (Q := (blkPC_579).rebase (blkPl_579).base (hooksException _))
    blkLib_eq_579 blk579_noSvc0 (mid := (blkPl_579).base + 0x2adc#64)
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
    have h150 : ((fsp + 0x150#64) ↦₆₄ kpkCap) ∗ ((fsp + 0x158#64) ↦₆₄ v158) ⊢
        memRegion (fsp + 0x150#64) 16 := by
      simpa only [BitVec.add_assoc, BitVec.reduceAdd] using
        r1b_cells2_to_region16 (fsp + 0x150#64) kpkCap v158
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
          (BitVec.ofNat 64 eBs.length) := by
      simp only [hsm, wp_norm, arm64_norm]
      try rw [hx12]
      try rw [hx1]
      try rw [hx14]
      try rw [hx25]
      refine r1b_SpePayload_str A.repAlloc ?_
      refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> bv_bits
    try rw [hx25]
    have hcl := r1b_cleanup_2adc_placed (st := st) (v188 := BitVec.ofNat 64 eBs.length)
      (kpkCap := kpkCap) (kpkPtr := kpkPtr)
      (kpkLen := BitVec.ofNat 64 kpkBs.length) (kpkBs := kpkBs)
      (spkCap := spkCap) (spkPtr := spkPtr)
      (spkLen := BitVec.ofNat 64 spkBs.length) (spkBs := spkBs)
      (regCap := regCap) (regPtr := regPtr)
      (regLen := BitVec.ofNat 64 regBs.length) (regBs := regBs)
      hh hdrop hbnd hc_m
      (by simp only [hsm, wp_norm, arm64_norm])
      (by solve | simp only [hsm, wp_norm, arm64_norm] | simpa only [hsm, wp_norm, arm64_norm] using hx26)
      hpanic hrej
    dsimp only at hcl
    rw [r1b_errCommon_atState_eq, herrCore] at hcl
    refine sepWPp_weaken_pre ?_ hcl
    exact r1b_entails_frame_ra (by r1b_ac)
      (sepConj_mono hpay (sepConj_mono h150 h4d0)) (by r1b_ac)

theorem r1b_err_1b98_placed_env [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {st : M.σ}
    {EnvAt : StoresGhost → RejectKind → M.σ → Prop}
    {H : LibsignalHooks} {B : RunBudgets}
    {g : RunCall} {d : Init1Data} {s0 s : State} {resStack : Nat}
    {eCap ePtr kpkCap kpkPtr spkCap spkPtr regCap regPtr v158 v188_in : BitVec 64}
    {eBs kpkBs spkBs regBs : List (BitVec 8)}
    {Q Qp : State → SepProp → Prop} {oom : State → SepProp}
    (hh : RunHooksPlaced A lim H) (hdrop : DropSpeOwnedOkAtBlock (runProgPlaced H) A lim)
    (hbnd : r1b_StackBounds B resStack)
    (hc : r1b_ErrCtxPlaced r1b_CodeOk g d s0 s 0x1b98)
    (hx12 : s.readReg64 (.gpr 12#5) = speWord 1)
    (hx1 : s.readReg64 .x1 = eCap)
    (hx14 : s.readReg64 (.gpr 14#5) = ePtr)
    (hx25 : s.readReg64 (.gpr 25#5) = BitVec.ofNat 64 eBs.length)
    (hx26 : s.readReg64 (.gpr 26#5) = kpkPtr)
    (hpanic : PanicK g s0 Qp)
    (hrej : RejectKPlacedEnv r1b_CodeOk H A lim EnvAt g s0 resStack Q Qp oom)
    (henv : ∀ evs, FreeOnlyEvs evs → EnvAt StoresGhost.opened .postDispatch (M.stepEvents evs st)) :
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
        ((fsp + 0x150#64) ↦₆₄ kpkCap) ∗ ((fsp + 0x158#64) ↦₆₄ v158) ∗
        ((fsp + 0x168#64) ↦₆₄ spkPtr) ∗ ((fsp + 0x170#64) ↦₆₄ spkCap) ∗
        memRegion (fsp + 0x178#64) 8 ∗
        ((fsp + 0x188#64) ↦₆₄ v188_in) ∗ memRegion (fsp + 0x190#64) 8 ∗
        ((fsp + 0x198#64) ↦₆₄ regCap) ∗ ((fsp + 0x1a0#64) ↦₆₄ regPtr) ∗
        memRegion (fsp + 0x1a8#64) 16)
      Q Qp oom :=
  r1b_err_1b98_placed hh hdrop hbnd hc hx12 hx1 hx14 hx25 hx26 hpanic fun sf evs hfo hrej_f =>
    hrej sf (M.stepEvents evs st) StoresGhost.opened .postDispatch hrej_f (henv evs hfo)

theorem r1b_err_2420_placed [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {st : M.σ}
    {H : LibsignalHooks} {B : RunBudgets}
    {g : RunCall} {d : Init1Data} {s0 s : State} {resStack : Nat}
    {eCap ePtr opkCap opkPtr kpkCap kpkPtr spkCap spkPtr regCap regPtr
      v158 v188 v190 v1a8 v1b0 : BitVec 64}
    {eBs opkBs kpkBs spkBs regBs : List (BitVec 8)}
    {Q Qp : State → SepProp → Prop} {oom : State → SepProp}
    (hh : RunHooksPlaced A lim H) (hdrop : DropSpeOwnedOkAtBlock (runProgPlaced H) A lim)
    (hbnd : r1b_StackBounds B resStack)
    (hc : r1b_ErrCtxPlaced r1b_CodeOk g d s0 s 0x2420)
    (hx8 : s.readReg64 .x8 = speWord 1)
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
      (((fsp + 0x4d0#64) ↦₆₄ speWord 1) ∗
        ((fsp + 0x4d8#64) ↦₃₂ ((eCap.extractLsb' 0 32).zeroExtend 64).truncate 32) ∗
        ((fsp + 0x4dc#64) ↦₃₂ eCap.extractLsb' 32 32) ∗
        ((fsp + 0x4e0#64) ↦₆₄ ePtr) ∗
        ((fsp + 0x4e8#64) ↦₆₄ BitVec.ofNat 64 eBs.length) ∗
        memRegion (fsp + 0x4f0#64) 16 ∗
        ownedBytes A.repAlloc eCap ePtr (BitVec.ofNat 64 eBs.length) eBs ∗
        ownedBytes A.repAlloc opkCap opkPtr (BitVec.ofNat 64 opkBs.length) opkBs ∗
        ownedBytes A.repAlloc kpkCap kpkPtr (BitVec.ofNat 64 kpkBs.length) kpkBs ∗
        ownedBytes A.repAlloc spkCap spkPtr (BitVec.ofNat 64 spkBs.length) spkBs ∗
        ownedBytes A.repAlloc regCap regPtr (BitVec.ofNat 64 regBs.length) regBs ∗
        r1b_errCommon (A.atState lim st s) g d s0 resStack ∗
        ((fsp + 0x110#64) ↦₆₄ opkCap) ∗
        ((fsp + 0x11c#64) ↦₃₂ ((eCap.extractLsb' 0 32).zeroExtend 64).truncate 32) ∗
        ((fsp + 0x120#64) ↦₆₄ opkPtr) ∗ ((fsp + 0x128#64) ↦₆₄ kpkPtr) ∗
        ((fsp + 0x150#64) ↦₆₄ kpkCap) ∗ ((fsp + 0x158#64) ↦₆₄ v158) ∗
        ((fsp + 0x168#64) ↦₆₄ spkPtr) ∗ ((fsp + 0x170#64) ↦₆₄ spkCap) ∗
        memRegion (fsp + 0x178#64) 8 ∗
        ((fsp + 0x188#64) ↦₆₄ v188) ∗ ((fsp + 0x190#64) ↦₆₄ v190) ∗
        ((fsp + 0x198#64) ↦₆₄ regCap) ∗ ((fsp + 0x1a0#64) ↦₆₄ regPtr) ∗
        ((fsp + 0x1a8#64) ↦₆₄ v1a8) ∗ ((fsp + 0x1b0#64) ↦₆₄ v1b0))
      Q Qp oom := by
  intro fsp
  let _ := hx8
  rw [r1b_errCommon_atState_eq]
  generalize herrCore : r1b_errCore A.repAlloc g d s0 = errCore
  have hst := hc.st
  have hal : fsp &&& 15#64 = 0#64 := r1b_fsp_align hst.sp hst.spAligned
  have hal4 : (fsp + 0x4dc#64) &&& 3#64 = 0#64 := by bv_bits
  have hsplit16 := r1b_region16_to_cells (fsp + 0x4f0#64)
  have h4f8 : (fsp + 0x4f0#64) + 8#64 = fsp + 0x4f8#64 := by bv_omega
  rw [h4f8] at hsplit16
  rw [hsplit16]
  simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
  refine SepWPp.exists_elim fun w4 => SepWPp.exists_elim fun w5 => ?_
  have hpc := hst.pc; change s.pc = (blkPl_579).base + 0x2420#64 at hpc
  have hrun := hst.run; have hsp : s.sp = fsp := hst.sp
  apply r1b_seq_lscro_oom (mid := (blkPl_579).base + 0x2aa8#64) hst.inv
  dsimp only [runProgPlaced, lsProg_579]
  apply sepWP_seg_ls_vm (Q := (blkPC_579).rebase (blkPl_579).base (hooksException _))
    blkLib_eq_579 blk579_noSvc0 (mid := (blkPl_579).base + 0x2aa8#64)
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
    rw [← A.pool_transport lim st s sm hvm]
    change SepWPp (runProgPlaced H) _ _ _ _ _ _
    have hc_m : r1b_ErrCtxPlaced r1b_CodeOk g d s0 sm 0x2aa8 := hc.of_step
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
    have htr32 : ((eCap.extractLsb' 0 32).zeroExtend 64).truncate 32 = eCap.extractLsb' 0 32 := by
      bv_bits
    have h4d8 :
        ((fsp + 0x4d8#64) ↦₃₂ ((eCap.extractLsb' 0 32).zeroExtend 64).truncate 32) ∗
          ((fsp + 0x4dc#64) ↦₃₂ eCap.extractLsb' 32 32) =
          ((fsp + 0x4d8#64) ↦₆₄ eCap) := by
      rw [htr32]
      have hp := pointsTo64_split32 (fsp + 0x4d8#64) eCap
      simpa only [BitVec.add_assoc, BitVec.reduceAdd] using hp.symm
    have h4d0 :
        ((fsp + 0x4d0#64) ↦₆₄ speWord 1) ∗
          ((fsp + 0x4d8#64) ↦₃₂ ((eCap.extractLsb' 0 32).zeroExtend 64).truncate 32) ∗
          ((fsp + 0x4dc#64) ↦₃₂ eCap.extractLsb' 32 32) ∗
          ((fsp + 0x4e0#64) ↦₆₄ ePtr) ∗
          ((fsp + 0x4e8#64) ↦₆₄ BitVec.ofNat 64 eBs.length) ∗
          ((fsp + 0x4f0#64) ↦₆₄ w4) ∗ ((fsp + 0x4f8#64) ↦₆₄ w5) ⊢
          memRegion (fsp + 0x4d0#64) 48 := by
      have h4d0_eq :
          ((fsp + 0x4d0#64) ↦₆₄ speWord 1) ∗
            ((fsp + 0x4d8#64) ↦₃₂ ((eCap.extractLsb' 0 32).zeroExtend 64).truncate 32) ∗
            ((fsp + 0x4dc#64) ↦₃₂ eCap.extractLsb' 32 32) ∗
            ((fsp + 0x4e0#64) ↦₆₄ ePtr) ∗
            ((fsp + 0x4e8#64) ↦₆₄ BitVec.ofNat 64 eBs.length) ∗
            ((fsp + 0x4f0#64) ↦₆₄ w4) ∗ ((fsp + 0x4f8#64) ↦₆₄ w5) =
          ((fsp + 0x4d0#64) ↦₆₄ speWord 1) ∗
            (((fsp + 0x4d8#64) ↦₃₂ ((eCap.extractLsb' 0 32).zeroExtend 64).truncate 32) ∗
              ((fsp + 0x4dc#64) ↦₃₂ eCap.extractLsb' 32 32)) ∗
            ((fsp + 0x4e0#64) ↦₆₄ ePtr) ∗
            ((fsp + 0x4e8#64) ↦₆₄ BitVec.ofNat 64 eBs.length) ∗
            ((fsp + 0x4f0#64) ↦₆₄ w4) ∗ ((fsp + 0x4f8#64) ↦₆₄ w5) := by r1b_ac
      rw [h4d0_eq, h4d8]
      simpa only [BitVec.add_assoc, BitVec.reduceAdd, sepConj_assoc] using
        r1b_cells6_to_region48 (fsp + 0x4d0#64) (speWord 1) eCap ePtr
          (BitVec.ofNat 64 eBs.length) w4 w5
    have hpay : ownedBytes A.repAlloc eCap ePtr (BitVec.ofNat 64 eBs.length) eBs ⊢
        r1b_SpePayload A.repAlloc (speWord 1)
          ((((eCap.extractLsb' 0 32).zeroExtend 64).truncate 32).zeroExtend 64)
          ((eCap.extractLsb' 32 32).zeroExtend 64)
          (sm.readReg64 (.gpr 27#5))
          (ePtr >>> 56)
          (sm.readReg64 (.gpr 24#5))
          (sm.readReg64 (.gpr 23#5))
          (sm.readReg64 (.gpr 28#5))
          (BitVec.ofNat 64 eBs.length) := by
      simp only [hsm, wp_norm, arm64_norm]
      refine r1b_SpePayload_str A.repAlloc ?_
      refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> bv_bits
    try rw [hx8]
    have hcl := r1b_cleanup_2aa8_placed (st := st)
      (v11c := ((eCap.extractLsb' 0 32).zeroExtend 64).truncate 32)
      (v158 := speWord 1)
      (v188 := BitVec.ofNat 64 eBs.length)
      (v190 := ePtr >>> 56)
      (v1a8 := w5)
      (v1b0 := (eCap.extractLsb' 32 32).zeroExtend 64)
      (opkCap := opkCap) (opkPtr := opkPtr)
      (opkLen := BitVec.ofNat 64 opkBs.length) (opkBs := opkBs)
      (kpkCap := kpkCap) (kpkPtr := kpkPtr)
      (kpkLen := BitVec.ofNat 64 kpkBs.length) (kpkBs := kpkBs)
      (spkCap := spkCap) (spkPtr := spkPtr)
      (spkLen := BitVec.ofNat 64 spkBs.length) (spkBs := spkBs)
      (regCap := regCap) (regPtr := regPtr)
      (regLen := BitVec.ofNat 64 regBs.length) (regBs := regBs)
      hh hdrop hbnd hc_m hpanic hrej
    dsimp only at hcl
    rw [r1b_errCommon_atState_eq, herrCore] at hcl
    refine sepWPp_weaken_pre ?_ hcl
    exact r1b_entails_frame_ra (by r1b_ac) (sepConj_mono hpay h4d0) (by r1b_ac)

theorem r1b_err_2420_placed_env [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {st : M.σ}
    {EnvAt : StoresGhost → RejectKind → M.σ → Prop}
    {H : LibsignalHooks} {B : RunBudgets}
    {g : RunCall} {d : Init1Data} {s0 s : State} {resStack : Nat}
    {eCap ePtr opkCap opkPtr kpkCap kpkPtr spkCap spkPtr regCap regPtr
      v158 v188 v190 v1a8 v1b0 : BitVec 64}
    {eBs opkBs kpkBs spkBs regBs : List (BitVec 8)}
    {Q Qp : State → SepProp → Prop} {oom : State → SepProp}
    (hh : RunHooksPlaced A lim H) (hdrop : DropSpeOwnedOkAtBlock (runProgPlaced H) A lim)
    (hbnd : r1b_StackBounds B resStack)
    (hc : r1b_ErrCtxPlaced r1b_CodeOk g d s0 s 0x2420)
    (hx8 : s.readReg64 .x8 = speWord 1)
    (hpanic : PanicK g s0 Qp)
    (hrej : RejectKPlacedEnv r1b_CodeOk H A lim EnvAt g s0 resStack Q Qp oom)
    (henv : ∀ evs, FreeOnlyEvs evs → EnvAt StoresGhost.opened .postDispatch (M.stepEvents evs st)) :
    let fsp := runFsp s0
    SepWPp (runProgPlaced H) (s0.readReg64 .lr) s
      (((fsp + 0x4d0#64) ↦₆₄ speWord 1) ∗
        ((fsp + 0x4d8#64) ↦₃₂ ((eCap.extractLsb' 0 32).zeroExtend 64).truncate 32) ∗
        ((fsp + 0x4dc#64) ↦₃₂ eCap.extractLsb' 32 32) ∗
        ((fsp + 0x4e0#64) ↦₆₄ ePtr) ∗
        ((fsp + 0x4e8#64) ↦₆₄ BitVec.ofNat 64 eBs.length) ∗
        memRegion (fsp + 0x4f0#64) 16 ∗
        ownedBytes A.repAlloc eCap ePtr (BitVec.ofNat 64 eBs.length) eBs ∗
        ownedBytes A.repAlloc opkCap opkPtr (BitVec.ofNat 64 opkBs.length) opkBs ∗
        ownedBytes A.repAlloc kpkCap kpkPtr (BitVec.ofNat 64 kpkBs.length) kpkBs ∗
        ownedBytes A.repAlloc spkCap spkPtr (BitVec.ofNat 64 spkBs.length) spkBs ∗
        ownedBytes A.repAlloc regCap regPtr (BitVec.ofNat 64 regBs.length) regBs ∗
        r1b_errCommon (A.atState lim st s) g d s0 resStack ∗
        ((fsp + 0x110#64) ↦₆₄ opkCap) ∗
        ((fsp + 0x11c#64) ↦₃₂ ((eCap.extractLsb' 0 32).zeroExtend 64).truncate 32) ∗
        ((fsp + 0x120#64) ↦₆₄ opkPtr) ∗ ((fsp + 0x128#64) ↦₆₄ kpkPtr) ∗
        ((fsp + 0x150#64) ↦₆₄ kpkCap) ∗ ((fsp + 0x158#64) ↦₆₄ v158) ∗
        ((fsp + 0x168#64) ↦₆₄ spkPtr) ∗ ((fsp + 0x170#64) ↦₆₄ spkCap) ∗
        memRegion (fsp + 0x178#64) 8 ∗
        ((fsp + 0x188#64) ↦₆₄ v188) ∗ ((fsp + 0x190#64) ↦₆₄ v190) ∗
        ((fsp + 0x198#64) ↦₆₄ regCap) ∗ ((fsp + 0x1a0#64) ↦₆₄ regPtr) ∗
        ((fsp + 0x1a8#64) ↦₆₄ v1a8) ∗ ((fsp + 0x1b0#64) ↦₆₄ v1b0))
      Q Qp oom :=
  r1b_err_2420_placed hh hdrop hbnd hc hx8 hpanic fun sf evs hfo hrej_f =>
    hrej sf (M.stepEvents evs st) StoresGhost.opened .postDispatch hrej_f (henv evs hfo)

/-! ## Deserialization Error Exit (`0x1360 → 0x2a88 / 0x2a60 / 0x2a8c`) -/

theorem r1b_opk_deser_err_1360_placed [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {st : M.σ}
    {H : LibsignalHooks} {B : RunBudgets}
    {g : RunCall} {d : Init1Data} {s0 s : State} {resStack : Nat}
    {opkCap opkPtr kpkCap kpkPtr spkCap spkPtr regCap regPtr : BitVec 64}
    {opkBs opkKey kpkBs spkBs regBs : List (BitVec 8)}
    {e : SignalProtocolError}
    {Q Qp : State → SepProp → Prop} {oom : State → SepProp}
    (hh : RunHooksPlaced A lim H) (hdrop : DropSpeOwnedOkAtBlock (runProgPlaced H) A lim)
    (hbnd : r1b_StackBounds B resStack)
    (hc : r1b_ErrCtxPlaced r1b_CodeOk g d s0 s 0x1360)
    (_hd : PublicKey.deserialize opkKey = .error e)
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
      (deserializeResult33At (fsp + 0x4d0#64) (.error e) ∗
        memRegion (fsp + 0x4f1#64) 15 ∗
        ownedBytes A.repAlloc opkCap opkPtr (BitVec.ofNat 64 opkBs.length) opkBs ∗
        ownedBytes A.repAlloc kpkCap kpkPtr (BitVec.ofNat 64 kpkBs.length) kpkBs ∗
        ownedBytes A.repAlloc spkCap spkPtr (BitVec.ofNat 64 spkBs.length) spkBs ∗
        ownedBytes A.repAlloc regCap regPtr (BitVec.ofNat 64 regBs.length) regBs ∗
        r1b_errCommon (A.atState lim st s) g d s0 resStack ∗
        ((fsp + 0x110#64) ↦₆₄ opkCap) ∗ memRegion (fsp + 0x11c#64) 4 ∗
        ((fsp + 0x120#64) ↦₆₄ opkPtr) ∗ ((fsp + 0x128#64) ↦₆₄ kpkPtr) ∗
        ((fsp + 0x150#64) ↦₆₄ kpkCap) ∗ memRegion (fsp + 0x158#64) 8 ∗
        ((fsp + 0x168#64) ↦₆₄ spkPtr) ∗ ((fsp + 0x170#64) ↦₆₄ spkCap) ∗
        memRegion (fsp + 0x178#64) 8 ∗
        memRegion (fsp + 0x188#64) 16 ∗
        ((fsp + 0x198#64) ↦₆₄ regCap) ∗ ((fsp + 0x1a0#64) ↦₆₄ regPtr) ∗
        memRegion (fsp + 0x1a8#64) 16)
      Q Qp oom := by
  intro fsp
  rw [r1b_errCommon_atState_eq]
  generalize herrCore : r1b_errCore A.repAlloc g d s0 = errCore
  have hst := hc.st
  have hal : fsp &&& 15#64 = 0#64 := r1b_fsp_align hst.sp hst.spAligned
  have hpc_in := hst.pc; change s.pc = (blkPl_579).base + 0x1360#64 at hpc_in
  cases e with
  | noKeyTypeIdentifier =>
    dsimp only [deserializeResult33At]
    simp only [BitVec.add_assoc, BitVec.reduceAdd, sepConj_assoc]
    have hpc := hpc_in; have hrun := hst.run; have hsp : s.sp = fsp := hst.sp
    apply r1b_seq_lscro_oom (mid := (blkPl_579).base + 0x2a88#64) hst.inv
    dsimp only [runProgPlaced, lsProg_579]
    apply sepWP_seg_ls_vm (Q := (blkPC_579).rebase (blkPl_579).base (hooksException _))
      blkLib_eq_579 blk579_noSvc0 (mid := (blkPl_579).base + 0x2a88#64)
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
      rw [← A.pool_transport lim st s sm hvm]
      change SepWPp (runProgPlaced H) _ _ _ _ _ _
      have hc_m : r1b_ErrCtxPlaced r1b_CodeOk g d s0 sm 0x2a88 := hc.of_step
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
          ((fsp + 0x4d0#64) ↦₈ 1#8) ∗ memRegion (fsp + 0x4d1#64) 7 ∗
            ((fsp + 0x4d8#64) ↦₈ 0#8) ∗ memRegion (fsp + 0x4d9#64) 24 ∗
            memRegion (fsp + 0x4f1#64) 15 ⊢
            memRegion (fsp + 0x4d0#64) 48 := by
        have h33 := memRegion33_of_err_base (fsp + 0x4d0#64) 0#8
        simp only [BitVec.add_assoc, BitVec.reduceAdd, sepConj_assoc] at h33
        refine Entails.trans (r1b_entails_frame_ra (by r1b_ac) h33 (by r1b_ac)) ?_
        rw [r1b_join_region fsp 0x4d0 33 15]; exact Entails.refl _
      have hcl := r1b_cleanup_2a88_placed (st := st) (i := 7)
        (opkCap := opkCap) (opkPtr := opkPtr)
        (opkLen := BitVec.ofNat 64 opkBs.length) (opkBs := opkBs)
        (kpkCap := kpkCap) (kpkPtr := kpkPtr)
        (kpkLen := BitVec.ofNat 64 kpkBs.length) (kpkBs := kpkBs)
        (spkCap := spkCap) (spkPtr := spkPtr)
        (spkLen := BitVec.ofNat 64 spkBs.length) (spkBs := spkBs)
        (regCap := regCap) (regPtr := regPtr)
        (regLen := BitVec.ofNat 64 regBs.length) (regBs := regBs)
        hh hdrop hbnd hc_m (by decide)
        (by simp only [hsm, wp_norm, arm64_norm, speWord]) hpanic hrej
      dsimp only at hcl
      rw [r1b_errCommon_atState_eq, herrCore] at hcl
      refine sepWPp_weaken_pre ?_ hcl
      exact r1b_entails_frame_ra (by r1b_ac) h4d0 (by r1b_ac)
  | badKeyType t =>
    dsimp only [deserializeResult33At]
    simp only [BitVec.add_assoc, BitVec.reduceAdd, sepConj_assoc]
    have hpc := hpc_in; have hrun := hst.run; have hsp : s.sp = fsp := hst.sp
    apply r1b_seq_lscro_oom (mid := (blkPl_579).base + 0x2a60#64) hst.inv
    dsimp only [runProgPlaced, lsProg_579]
    apply sepWP_seg_ls_vm (Q := (blkPC_579).rebase (blkPl_579).base (hooksException _))
      blkLib_eq_579 blk579_noSvc0 (mid := (blkPl_579).base + 0x2a60#64)
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
      rw [← A.pool_transport lim st s sm hvm]
      change SepWPp (runProgPlaced H) _ _ _ _ _ _
      have hc_m : r1b_ErrCtxPlaced r1b_CodeOk g d s0 sm 0x2a60 := hc.of_step
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
          ((fsp + 0x4d0#64) ↦₈ 1#8) ∗ memRegion (fsp + 0x4d1#64) 7 ∗
            ((fsp + 0x4d8#64) ↦₈ 1#8) ∗ ((fsp + 0x4d9#64) ↦₈ t) ∗
            memRegion (fsp + 0x4da#64) 23 ∗ memRegion (fsp + 0x4f1#64) 15 ⊢
            memRegion (fsp + 0x4d0#64) 48 := by
        have h33 := memRegion33_of_err_badKeyType (fsp + 0x4d0#64) t
        simp only [BitVec.add_assoc, BitVec.reduceAdd, sepConj_assoc] at h33
        refine Entails.trans (r1b_entails_frame_ra (by r1b_ac) h33 (by r1b_ac)) ?_
        rw [r1b_join_region fsp 0x4d0 33 15]; exact Entails.refl _
      have hcl := r1b_cleanup_2a60_placed (st := st)
        (opkCap := opkCap) (opkPtr := opkPtr)
        (opkLen := BitVec.ofNat 64 opkBs.length) (opkBs := opkBs)
        (kpkCap := kpkCap) (kpkPtr := kpkPtr)
        (kpkLen := BitVec.ofNat 64 kpkBs.length) (kpkBs := kpkBs)
        (spkCap := spkCap) (spkPtr := spkPtr)
        (spkLen := BitVec.ofNat 64 spkBs.length) (spkBs := spkBs)
        (regCap := regCap) (regPtr := regPtr)
        (regLen := BitVec.ofNat 64 regBs.length) (regBs := regBs)
        hh hdrop hbnd hc_m hpanic hrej
      dsimp only at hcl
      rw [r1b_errCommon_atState_eq, herrCore] at hcl
      refine sepWPp_weaken_pre ?_ hcl
      exact r1b_entails_frame_ra (by r1b_ac) h4d0 (by r1b_ac)
  | badKeyLength n =>
    dsimp only [deserializeResult33At]
    rw [ProofLib.memRegion_eight (fsp + 0x158#64)]
    simp only [sepExists_sepConj_left, sepExists_sepConj_right, BitVec.add_assoc,
      BitVec.reduceAdd, sepConj_assoc]
    refine SepWPp.exists_elim fun v158 => ?_
    have hpc := hpc_in; have hrun := hst.run; have hsp : s.sp = fsp := hst.sp
    apply r1b_seq_lscro_oom (mid := (blkPl_579).base + 0x2a8c#64) hst.inv
    dsimp only [runProgPlaced, lsProg_579]
    apply sepWP_seg_ls_vm (Q := (blkPC_579).rebase (blkPl_579).base (hooksException _))
      blkLib_eq_579 blk579_noSvc0 (mid := (blkPl_579).base + 0x2a8c#64)
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
      rw [← A.pool_transport lim st s sm hvm]
      change SepWPp (runProgPlaced H) _ _ _ _ _ _
      have hc_m : r1b_ErrCtxPlaced r1b_CodeOk g d s0 sm 0x2a8c := hc.of_step
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
          ((fsp + 0x4d0#64) ↦₈ 1#8) ∗ memRegion (fsp + 0x4d1#64) 7 ∗
            ((fsp + 0x4d8#64) ↦₈ 2#8) ∗ memRegion (fsp + 0x4d9#64) 7 ∗
            ((fsp + 0x4e0#64) ↦₆₄ BitVec.ofNat 64 n) ∗ memRegion (fsp + 0x4e8#64) 9 ∗
            memRegion (fsp + 0x4f1#64) 15 ⊢
            memRegion (fsp + 0x4d0#64) 48 := by
        have h33 := memRegion33_of_err_badKeyLength (fsp + 0x4d0#64) n
        simp only [BitVec.add_assoc, BitVec.reduceAdd, sepConj_assoc] at h33
        refine Entails.trans (r1b_entails_frame_ra (by r1b_ac) h33 (by r1b_ac)) ?_
        rw [r1b_join_region fsp 0x4d0 33 15]; exact Entails.refl _
      have h158_eq : ((fsp + 0x158#64) ↦₆₄ 0x8000000000000009#64) =
          ((fsp + 0x158#64) ↦₆₄ speWord 9) := rfl
      rw [h158_eq]
      have hcl := r1b_cleanup_2a8c_placed (st := st) (i := 9)
        (opkCap := opkCap) (opkPtr := opkPtr)
        (opkLen := BitVec.ofNat 64 opkBs.length) (opkBs := opkBs)
        (kpkCap := kpkCap) (kpkPtr := kpkPtr)
        (kpkLen := BitVec.ofNat 64 kpkBs.length) (kpkBs := kpkBs)
        (spkCap := spkCap) (spkPtr := spkPtr)
        (spkLen := BitVec.ofNat 64 spkBs.length) (spkBs := spkBs)
        (regCap := regCap) (regPtr := regPtr)
        (regLen := BitVec.ofNat 64 regBs.length) (regBs := regBs)
        hh hdrop hbnd hc_m (by decide) hpanic hrej
      dsimp only at hcl
      rw [r1b_errCommon_atState_eq, herrCore] at hcl
      refine sepWPp_weaken_pre ?_ hcl
      exact r1b_entails_frame_ra (by r1b_ac) h4d0 (by r1b_ac)
  | _ =>
    dsimp only [deserializeResult33At]
    exact SepWPp.pure_elim False.elim

theorem r1b_opk_deser_err_1360_placed_env [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {st : M.σ}
    {EnvAt : StoresGhost → RejectKind → M.σ → Prop}
    {H : LibsignalHooks} {B : RunBudgets}
    {g : RunCall} {d : Init1Data} {s0 s : State} {resStack : Nat}
    {opkCap opkPtr kpkCap kpkPtr spkCap spkPtr regCap regPtr : BitVec 64}
    {opkBs opkKey kpkBs spkBs regBs : List (BitVec 8)}
    {e : SignalProtocolError}
    {Q Qp : State → SepProp → Prop} {oom : State → SepProp}
    (hh : RunHooksPlaced A lim H) (hdrop : DropSpeOwnedOkAtBlock (runProgPlaced H) A lim)
    (hbnd : r1b_StackBounds B resStack)
    (hc : r1b_ErrCtxPlaced r1b_CodeOk g d s0 s 0x1360)
    (hd : PublicKey.deserialize opkKey = .error e)
    (hpanic : PanicK g s0 Qp)
    (hrej : RejectKPlacedEnv r1b_CodeOk H A lim EnvAt g s0 resStack Q Qp oom)
    (henv : ∀ evs, FreeOnlyEvs evs → EnvAt StoresGhost.opened .postDispatch (M.stepEvents evs st)) :
    let fsp := runFsp s0
    SepWPp (runProgPlaced H) (s0.readReg64 .lr) s
      (deserializeResult33At (fsp + 0x4d0#64) (.error e) ∗
        memRegion (fsp + 0x4f1#64) 15 ∗
        ownedBytes A.repAlloc opkCap opkPtr (BitVec.ofNat 64 opkBs.length) opkBs ∗
        ownedBytes A.repAlloc kpkCap kpkPtr (BitVec.ofNat 64 kpkBs.length) kpkBs ∗
        ownedBytes A.repAlloc spkCap spkPtr (BitVec.ofNat 64 spkBs.length) spkBs ∗
        ownedBytes A.repAlloc regCap regPtr (BitVec.ofNat 64 regBs.length) regBs ∗
        r1b_errCommon (A.atState lim st s) g d s0 resStack ∗
        ((fsp + 0x110#64) ↦₆₄ opkCap) ∗ memRegion (fsp + 0x11c#64) 4 ∗
        ((fsp + 0x120#64) ↦₆₄ opkPtr) ∗ ((fsp + 0x128#64) ↦₆₄ kpkPtr) ∗
        ((fsp + 0x150#64) ↦₆₄ kpkCap) ∗ memRegion (fsp + 0x158#64) 8 ∗
        ((fsp + 0x168#64) ↦₆₄ spkPtr) ∗ ((fsp + 0x170#64) ↦₆₄ spkCap) ∗
        memRegion (fsp + 0x178#64) 8 ∗
        memRegion (fsp + 0x188#64) 16 ∗
        ((fsp + 0x198#64) ↦₆₄ regCap) ∗ ((fsp + 0x1a0#64) ↦₆₄ regPtr) ∗
        memRegion (fsp + 0x1a8#64) 16)
      Q Qp oom :=
  r1b_opk_deser_err_1360_placed hh hdrop hbnd hc hd hpanic fun sf evs hfo hrej_f =>
    hrej sf (M.stepEvents evs st) StoresGhost.opened .postDispatch hrej_f (henv evs hfo)

end LibsignalBinary.Proofs.SignalSession.Cli.Run.Compose.Arms.R1b.ReadOpkPlacedBudgetAux
