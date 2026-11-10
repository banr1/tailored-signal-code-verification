/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Kits.StageP2DefsPlacedBudget
public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Kits.StageP2BlocksErrAPlacedBudget
public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Kits.StageP2BlocksErrBPlaced
public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Kits.StageP1StepsXExtPlacedBudgetAux
public import LibsignalBinary.Heap.IfaceBudget
public import LibsignalBinary.Heap.IfaceBudgetLemmas
public import LibsignalBinary.Proofs.Placed.BudgetVmSteps
public meta import Lean.Elab.Tactic -- shake: keep
import LibsignalBinary.Proofs.Common.SharedHelpers
meta import LibsignalBinary.Proofs.Common.SharedHelpers -- shake: keep
import Arm64.Trusted.Spec.Hoare
import Arm64.Trusted.Spec.SepLogic
import LibsignalBinary.Proofs.E2E.InMem.HashbrownBin.SessionStoreFutures.StoreCommon
import LibsignalBinary.Proofs.E2E.Record.Serialization.SessionCloneAux.Base
import LibsignalBinary.Proofs.SpqrV1.Poly.EncoderFromPb.Defs
import LibsignalBinary.Proofs.SpqrV1.Poly.EncoderIntoPb.Defs
import LibsignalBinary.Proofs.SpqrV1.Prost.MessageEncode.Base
import LibsignalBinary.Proofs.SpqrV1.Prost.MessageMerge.PolyCommon
import LibsignalBinary.Proofs.TripleRatchet.GeneralizeEntry
import LibsignalBinary.Proofs.TripleRatchet.ReceiveRatchet.From.Step244

/-!
# Budget-Threaded Relocatable Stage P2 Basic Blocks — Error Arms 2, 3, and 4

`RustCliAllocBudget M` / `VmPreserved` basic-block lemmas for Stage P2 store-error unwind Arms 2,
3, and 4 into `+0x1648` on Block `518`.
-/

@[expose] public section

set_option autoImplicit false

namespace LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Kits.StageP2BlocksErrBPlacedBudget

open Arm64 ProofLib ProofLib.ProgramReflection
open LibsignalBinary.Heap (
  AllocCallPreserved AllocCostModel BudgetLimits RustCliAllocBudget VmPreserved
  rustDeallocEvents
)
open LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Kits.StageP1StepsXExtPlacedBudgetAux (
  sepWP_seg_rebase_vm
)
open LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Kits.StageP2DefsPlacedBudget (
  StageP2ClosureHooksPlaced
)
open CryptoVerification (
  LibsignalPlacement lsRustDeallocSym lsρ
)
open CryptoVerification.RustHeap (allocHookStack)
open CryptoVerification.E2E.Pqxdh.ResponderClosure (
  bytes7At keyPair64UnalignedAt preKeyRecordOut64At
)
open CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.Kits (
  stageP1EntryPlaced stageP1ProgPlaced
)
open CryptoVerification.CliHandshake.RespClosurePlaced (blkPC_518 blkPl_518)

set_option maxRecDepth 200000

attribute [local irreducible] Program.fetch Program.externAt? Program.fnOff
attribute [local arm64_norm] bv_sub_add_lit BitVec.add_assoc BitVec.toNat_zero

local elab "wp_steps_sync_pool_518 " _ext:term:max mid:term : tactic => do
  Lean.Elab.Tactic.evalTactic
    (← `(tactic| apply sepWP_seg_rebase_vm (P := blkPC_518) (b := blkPl_518.base) (mid := $mid)))
  let g ← Lean.Elab.Tactic.getMainGoal
  g.withContext do
    let outerLCtx ← Lean.getLCtx
    let ty := (← Lean.instantiateMVars (← g.getType)).consumeMData
    let e2 := ty.getArg! 0
    let e1 := e2.getArg! 0
    let ty1 := Lean.mkAppN ty.getAppFn
      #[e1, ty.getArg! 1, ty.getArg! 2, ty.getArg! 3, ty.getArg! 4, ty.getArg! 5]
    let g1 ← Lean.Meta.mkFreshExprMVar ty1
    let savedGoals ← Lean.Elab.Tactic.getGoals
    Lean.Elab.Tactic.setGoals [g1.mvarId!]
    Lean.Elab.Tactic.evalTactic (← `(tactic| (
      wp_steps
      refine SepWP.done (by simp_all +zetaDelta [arm64_norm]) (by simp_all +zetaDelta [arm64_norm])
        ⟨by first | rfl | simp only [wp_norm, arm64_norm], ?_⟩)))
    let rem ← Lean.Elab.Tactic.getGoals
    let [remId] := rem
      | throwError "wp_steps_sync_pool_518: expected 1 continuation goal, got {rem.length}"
    let (newArgFVars, newNames, contForallType) ← remId.withContext do
      let remLCtx ← Lean.getLCtx
      let mut fvs : Array Lean.Expr := #[]
      let mut argFvs : Array Lean.Expr := #[]
      let mut nms : Array Lean.Name := #[]
      for decl in remLCtx do
        if !decl.isImplementationDetail && !outerLCtx.contains decl.fvarId then
          fvs := fvs.push decl.toExpr
          if !decl.isLet then
            argFvs := argFvs.push decl.toExpr
          nms := nms.push decl.userName
      let remType ← Lean.instantiateMVars (← remId.getType)
      let cTy ← Lean.Meta.mkForallFVars fvs remType (usedLetOnly := false)
      pure (argFvs, nms, cTy)
    let gNext ← Lean.Meta.mkFreshExprMVar contForallType
    Lean.Meta.withLocalDeclD `_fn_next contForallType fun fnNext => do
      remId.assign (Lean.mkAppN fnNext newArgFVars)
      let prf1 ← Lean.instantiateMVars g1
      let prf2 := prf1.replace fun sub =>
        if sub.eqv e2 then some e2
        else if sub.eqv e1 then some e2
        else none
      let prfLam ← Lean.Meta.mkLambdaFVars #[fnNext] prf2
      g.assign (Lean.mkApp prfLam gNext)
    let mut gCur := gNext.mvarId!
    for nm in newNames do
      let (_, gCur') ← gCur.intro nm
      gCur := gCur'
    Lean.Elab.Tactic.setGoals (gCur :: savedGoals.tail!)
    let idHvm := Lean.mkIdent `_hvm
    let idHpcm := Lean.mkIdent `_hpcm
    let idHrunm := Lean.mkIdent `_hrunm
    Lean.Elab.Tactic.evalTactic
      (← `(tactic| (
        intro $idHvm:ident $idHpcm:ident $idHrunm:ident
        try refine SepWP.transport_budgetPool $idHvm:ident (hnext := ?_))))

/-! ## Arm 2: `kpkKit.get` `.error` (`+0x0998 -> kyberDropAddr -> +0x0c3c -> +0x1648`) -/

set_option maxHeartbeats 1000000 in
/-- Segment P2.Err2a (`+0x0998 -> kyberDropAddr`) on `stageP1ProgPlaced ext` with `VmPreserved`. -/
theorem p2_err2a_ext_placed_wp [LibsignalPlacement] (ext : String → Option (State → State))
    (s : State) (coroPtr kyberFutPtr kyberFutVt kyberDropAddr w0
    v_98 v_a0 v_b0 u_90 u_98 u_a0 u_a8 u_b0 u_b8 u_d0
    w1 w2 w3 w4 w5 u_418 : BitVec 64)
    (hdrop_nz : kyberDropAddr ≠ 0#64)
    (hpc : s.pc = stageP1EntryPlaced + 0x998#64)
    (hrun : s.status = .Running) (_hsp_align : (s.sp &&& 15#64 == 0#64) = true)
    (hx19 : s.readReg64 .x19 = coroPtr) (hx21 : s.readReg64 .x21 = v_b0)
    (hx23 : s.readReg64 .x23 = v_a0) (hx26 : s.readReg64 .x26 = v_98) :
    SepWP (stageP1ProgPlaced ext) kyberDropAddr s
      (preKeyRecordOut64At (s.sp + 0x3e0#64) 0xffffffffffffffff#64 w0 w1 w2 w3 w4 w5 u_418 ∗
       ((coroPtr + 0x4f8#64) ↦₆₄ kyberFutPtr) ∗
       ((coroPtr + 0x500#64) ↦₆₄ kyberFutVt) ∗
       ((kyberFutVt + 0x0#64) ↦₆₄ᵣ kyberDropAddr) ∗
       ((s.sp + 0x90#64) ↦₆₄ u_90) ∗
       ((s.sp + 0x98#64) ↦₆₄ u_98) ∗
       ((s.sp + 0xa0#64) ↦₆₄ u_a0) ∗
       ((s.sp + 0xa8#64) ↦₆₄ u_a8) ∗
       ((s.sp + 0xb0#64) ↦₆₄ u_b0) ∗
       ((s.sp + 0xb8#64) ↦₆₄ u_b8) ∗
       ((s.sp + 0xd0#64) ↦₆₄ u_d0))
      (fun s1 P_f =>
        (P_f ⊢
          preKeyRecordOut64At (s.sp + 0x3e0#64) 0xffffffffffffffff#64 w0 w1 w2 w3 w4 w5 u_418 ∗
          ((coroPtr + 0x4f8#64) ↦₆₄ kyberFutPtr) ∗
          ((coroPtr + 0x500#64) ↦₆₄ kyberFutVt) ∗
          ((kyberFutVt + 0x0#64) ↦₆₄ᵣ kyberDropAddr) ∗
          ((s.sp + 0x90#64) ↦₆₄ w5) ∗
          ((s.sp + 0x98#64) ↦₆₄ v_98) ∗
          ((s.sp + 0xa0#64) ↦₆₄ v_a0) ∗
          ((s.sp + 0xa8#64) ↦₆₄ w4) ∗
          ((s.sp + 0xb0#64) ↦₆₄ v_b0) ∗
          ((s.sp + 0xb8#64) ↦₆₄ w2) ∗
          ((s.sp + 0xd0#64) ↦₆₄ w3)) ∧
        s1.sp = s.sp ∧
        s1.trace = s.trace ∧
        s1.readReg64 .x0 = kyberFutPtr ∧
        s1.readReg64 .x19 = coroPtr ∧
        s1.readReg64 .x20 = u_418 ∧
        s1.readReg64 .x21 = kyberFutPtr ∧
        s1.readReg64 .x22 = w1 ∧
        s1.readReg64 .x23 = w0 ∧
        s1.readReg64 .x24 = kyberFutVt ∧
        s1.readReg64 .x25 = s.readReg64 .x25 ∧
        s1.readReg64 .x26 = v_98 ∧
        s1.readReg64 .x27 = s.readReg64 .x27 ∧
        s1.readReg64 .x28 = 0xffffffffffffffff#64 ∧
        s1.readReg64 .x29 = s.readReg64 .x29 ∧
        s1.readReg64 .x30 = stageP1EntryPlaced + 0xc3c#64 ∧
        calleeSavedVRegs s1 = calleeSavedVRegs s ∧
        VmPreserved s s1) := by
  have _hdrop_beq : (kyberDropAddr == 0#64) = false := beq_eq_false_iff_ne.mpr hdrop_nz
  have hx19' : s.readReg64 (Reg.gpr 19#5) = coroPtr := hx19
  have hx21' : s.readReg64 (Reg.gpr 21#5) = v_b0 := hx21
  have hx23' : s.readReg64 (Reg.gpr 23#5) = v_a0 := hx23
  have hx26' : s.readReg64 (Reg.gpr 26#5) = v_98 := hx26
  dsimp only [stageP1ProgPlaced, stageP1EntryPlaced, preKeyRecordOut64At] at hpc ⊢
  conv =>
    arg 4
    simp (config := { maxSteps := 1000000 }) only [
      BitVec.add_assoc, BitVec.reduceAdd, sepConj_assoc]
  wp_steps_sync_pool_518 ext kyberDropAddr
  refine SepWP.done _hpcm _hrunm ?_
  refine ⟨?_, rfl, rfl,
    by simp_all [arm64_norm], by simp_all [arm64_norm], by simp_all [arm64_norm],
    by simp_all [arm64_norm], by simp_all [arm64_norm], by simp_all [arm64_norm],
    by simp_all [arm64_norm], by simp_all [arm64_norm], by simp_all [arm64_norm],
    by simp_all [arm64_norm], by simp_all [arm64_norm], by simp_all [arm64_norm],
    by simp_all [arm64_norm], by simp_all [arm64_norm], _hvm⟩
  simp only [BitVec.add_assoc, BitVec.reduceAdd]
  exact Entails.of_eq (by sep_ac_rfl)

set_option maxHeartbeats 1200000 in
/-- Segment P2.Err2b (`+0x0c3c -> +0x1648`, generic `kyberBoxSize`) on `stageP1ProgPlaced ext`,
threading `A.pool lim st s -> A.pool lim (M.stepEvents (rustDeallocEvents kyberBoxSize 8) st) s1`
across `rustCliDeallocBudgetSpec M A lim`. -/
theorem p2_err2b_hooks_placed_wp [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {st : M.σ}
    (ext : String → Option (State → State))
    (hH : StageP2ClosureHooksPlaced A lim ext)
    (s : State) (coroPtr kyberFutPtr kyberFutVt outPtr
    w0 w1 w2 w4 w5 v_c0 u_c0 : BitVec 64)
    (b_4f1 : BitVec 8)
    (kyberBoxSize : Nat)
    (hbs_nz : BitVec.ofNat 64 kyberBoxSize ≠ 0#64)
    (hbs_lt : kyberBoxSize < 2 ^ 64)
    (hpc : s.pc = stageP1EntryPlaced + 0xc3c#64)
    (hrun : s.status = .Running) (_hsp_align : (s.sp &&& 15#64 == 0#64) = true)
    (hx19 : s.readReg64 .x19 = coroPtr)
    (hx21 : s.readReg64 .x21 = kyberFutPtr)
    (hx22 : s.readReg64 .x22 = w1)
    (hx23 : s.readReg64 .x23 = w0)
    (hx24 : s.readReg64 .x24 = kyberFutVt)
    (hx27 : s.readReg64 .x27 = v_c0)
    (hx28 : s.readReg64 .x28 = 0xffffffffffffffff#64) :
    SepWP (stageP1ProgPlaced ext) (stageP1EntryPlaced + 0x1648#64) s
      (((kyberFutVt + 0x8#64) ↦₆₄ᵣ BitVec.ofNat 64 kyberBoxSize) ∗
       ((kyberFutVt + 0x10#64) ↦₆₄ᵣ 8#64) ∗
       A.live kyberFutPtr kyberBoxSize 8 ∗
       memRegion kyberFutPtr kyberBoxSize ∗
       A.pool lim st s ∗
       stackAt s.sp allocHookStack ∗
       ((coroPtr + 0x4f1#64) ↦₈ b_4f1) ∗
       ((s.sp + 0x90#64) ↦₆₄ w5) ∗
       ((s.sp + 0xa8#64) ↦₆₄ w4) ∗
       ((s.sp + 0xb8#64) ↦₆₄ w2) ∗
       ((s.sp + 0xc0#64) ↦₆₄ u_c0) ∗
       ((s.sp + 0xc8#64) ↦₆₄ outPtr))
      (fun s1 P_f =>
        let st' := M.stepEvents (rustDeallocEvents kyberBoxSize 8) st
        (P_f ⊢
          ((kyberFutVt + 0x8#64) ↦₆₄ᵣ BitVec.ofNat 64 kyberBoxSize) ∗
          ((kyberFutVt + 0x10#64) ↦₆₄ᵣ 8#64) ∗
          A.pool lim st' s1 ∗
          stackAt s.sp allocHookStack ∗
          ((coroPtr + 0x4f1#64) ↦₈ 0#8) ∗
          ((s.sp + 0x90#64) ↦₆₄ w5) ∗
          ((s.sp + 0xa8#64) ↦₆₄ w4) ∗
          ((s.sp + 0xb8#64) ↦₆₄ w2) ∗
          ((s.sp + 0xc0#64) ↦₆₄ v_c0) ∗
          ((s.sp + 0xc8#64) ↦₆₄ outPtr)) ∧
        s1.sp = s.sp ∧
        s1.trace = s.trace ∧
        s1.readReg64 .x10 = w2 ∧
        s1.readReg64 .x19 = coroPtr ∧
        s1.readReg64 .x20 = w0 ∧
        s1.readReg64 .x21 = w4 >>> 8 ∧
        s1.readReg64 .x22 = w1 >>> 32 ∧
        s1.readReg64 .x23 = (w1.extractLsb' 0 32).zeroExtend 64 ∧
        s1.readReg64 .x24 = w2 >>> 32 ∧
        s1.readReg64 .x25 = s.readReg64 .x25 ∧
        s1.readReg64 .x26 = outPtr ∧
        s1.readReg64 .x27 = w5 ∧
        s1.readReg64 .x28 = s.sp + 0xa90#64 ∧
        s1.readReg64 .x29 = s.readReg64 .x29 ∧
        calleeSavedVRegs s1 = calleeSavedVRegs s ∧
        M.liveBytes st' ≤ M.liveBytes st) := by
  have hdealloc := hH.dealloc
  have _hbs_beq : (BitVec.ofNat 64 kyberBoxSize == 0#64) = false := beq_eq_false_iff_ne.mpr hbs_nz
  have _hbs_toNat : (BitVec.ofNat 64 kyberBoxSize).toNat = kyberBoxSize := Nat.mod_eq_of_lt hbs_lt
  have hx19' : s.readReg64 (Reg.gpr 19#5) = coroPtr := hx19
  have hx21' : s.readReg64 (Reg.gpr 21#5) = kyberFutPtr := hx21
  have hx22' : s.readReg64 (Reg.gpr 22#5) = w1 := hx22
  have hx23' : s.readReg64 (Reg.gpr 23#5) = w0 := hx23
  have hx24' : s.readReg64 (Reg.gpr 24#5) = kyberFutVt := hx24
  have hx27' : s.readReg64 (Reg.gpr 27#5) = v_c0 := hx27
  have hx28' : s.readReg64 (Reg.gpr 28#5) = 0xffffffffffffffff#64 := hx28
  dsimp only [stageP1ProgPlaced, stageP1EntryPlaced, lsRustDeallocSym] at hdealloc hpc ⊢
  wp_steps_sync_pool_518 ext (lsρ "_RNvCs1njKG4L9aB3_7___rustc14___rust_dealloc")
  clear _hvm _hpcm _hrunm
  wp_call hdealloc (kyberFutPtr, kyberBoxSize, 8, st)
  wp_steps_sync_pool_518 ext (blkPl_518.base + 5704#64)
  refine SepWP.done _hpcm _hrunm ?_
  refine ⟨Entails.of_eq (by sep_ac_rfl),
    by simp_all [arm64_norm], by simp_all [arm64_norm, AllocCallPreserved],
    by simp_all [arm64_norm], by simp_all [arm64_norm], by simp_all [arm64_norm],
    by simp_all [arm64_norm],
    by simp_all [arm64_norm]; clear * -; bv_bits,
    by simp_all [arm64_norm]; clear * -; bv_bits,
    by simp_all [arm64_norm], by simp_all [arm64_norm], by simp_all [arm64_norm],
    by simp_all [arm64_norm], by simp_all [arm64_norm], by simp_all [arm64_norm],
    by simp_all [arm64_norm], M.liveBytes_free_le 8 kyberBoxSize st⟩

abbrev p2_err2b_4k_placed_wp := @p2_err2b_hooks_placed_wp
abbrev p2_err2b_ext_placed_wp := @p2_err2b_hooks_placed_wp
abbrev p2_err2b_gen_placed_wp := @p2_err2b_hooks_placed_wp

/-! ## Arm 3a: `pkKit.get` `.error` Poll-Unpack (`+0x09c4 -> opkDropAddr`) -/

set_option maxHeartbeats 1000000 in
/-- Segment P2.Err3a (`+0x09c4 -> opkDropAddr`) on `stageP1ProgPlaced ext` with `VmPreserved`. -/
theorem p2_err3a_ext_placed_wp [LibsignalPlacement] (ext : String → Option (State → State))
    (s : State) (coroPtr ctxPtr opkFutPtr opkFutVt opkDropAddr
    w0 w1 w2 w3 w4 w5 u_ac8
    v_98 v_a0 v_b0 u_98 u_a0 u_a8 u_b0 u_b8 u_c0 u_d0 : BitVec 64)
    (hdrop_nz : opkDropAddr ≠ 0#64)
    (hpc : s.pc = stageP1EntryPlaced + 0x9c4#64)
    (hrun : s.status = .Running)
    (_hsp_align : (s.sp &&& 15#64 == 0#64) = true)
    (hx19 : s.readReg64 .x19 = coroPtr)
    (hx21 : s.readReg64 .x21 = v_b0)
    (hx23 : s.readReg64 .x23 = v_a0)
    (hx26 : s.readReg64 .x26 = v_98)
    (hx27 : s.readReg64 .x27 = ctxPtr) :
    SepWP (stageP1ProgPlaced ext) opkDropAddr s
      (preKeyRecordOut64At (s.sp + 0xa90#64) 0xffffffffffffffff#64 w0 w1 w2 w3 w4 w5 u_ac8 ∗
       ((coroPtr + 0x4f8#64) ↦₆₄ opkFutPtr) ∗
       ((coroPtr + 0x500#64) ↦₆₄ opkFutVt) ∗
       ((opkFutVt + 0x0#64) ↦₆₄ᵣ opkDropAddr) ∗
       ((s.sp + 0x98#64) ↦₆₄ u_98) ∗
       ((s.sp + 0xa0#64) ↦₆₄ u_a0) ∗
       ((s.sp + 0xa8#64) ↦₆₄ u_a8) ∗
       ((s.sp + 0xb0#64) ↦₆₄ u_b0) ∗
       ((s.sp + 0xb8#64) ↦₆₄ u_b8) ∗
       ((s.sp + 0xc0#64) ↦₆₄ u_c0) ∗
       ((s.sp + 0xd0#64) ↦₆₄ u_d0))
      (fun s1 P_f =>
        (P_f ⊢
          preKeyRecordOut64At (s.sp + 0xa90#64) 0xffffffffffffffff#64 w0 w1 w2 w3 w4 w5 u_ac8 ∗
          ((coroPtr + 0x4f8#64) ↦₆₄ opkFutPtr) ∗
          ((coroPtr + 0x500#64) ↦₆₄ opkFutVt) ∗
          ((opkFutVt + 0x0#64) ↦₆₄ᵣ opkDropAddr) ∗
          ((s.sp + 0x98#64) ↦₆₄ v_98) ∗
          ((s.sp + 0xa0#64) ↦₆₄ v_a0) ∗
          ((s.sp + 0xa8#64) ↦₆₄ w4) ∗
          ((s.sp + 0xb0#64) ↦₆₄ v_b0) ∗
          ((s.sp + 0xb8#64) ↦₆₄ w2) ∗
          ((s.sp + 0xc0#64) ↦₆₄ ctxPtr) ∗
          ((s.sp + 0xd0#64) ↦₆₄ w3)) ∧
        s1.sp = s.sp ∧
        s1.trace = s.trace ∧
        s1.readReg64 .x0 = opkFutPtr ∧
        s1.readReg64 .x19 = coroPtr ∧
        s1.readReg64 .x21 = opkFutPtr ∧
        s1.readReg64 .x22 = 0xffffffffffffffff#64 ∧
        s1.readReg64 .x23 = w1 ∧
        s1.readReg64 .x24 = opkFutVt ∧
        s1.readReg64 .x25 = s.readReg64 .x25 ∧
        s1.readReg64 .x26 = w0 ∧
        s1.readReg64 .x27 = w5 ∧
        s1.readReg64 .x28 = s.readReg64 .x28 ∧
        s1.readReg64 .x29 = s.readReg64 .x29 ∧
        s1.readReg64 .x30 = stageP1EntryPlaced + 0xe40#64 ∧
        calleeSavedVRegs s1 = calleeSavedVRegs s ∧
        VmPreserved s s1) := by
  have _hdrop_beq : (opkDropAddr == 0#64) = false := beq_eq_false_iff_ne.mpr hdrop_nz
  have hx19' : s.readReg64 (Reg.gpr 19#5) = coroPtr := hx19
  have hx21' : s.readReg64 (Reg.gpr 21#5) = v_b0 := hx21
  have hx23' : s.readReg64 (Reg.gpr 23#5) = v_a0 := hx23
  have hx26' : s.readReg64 (Reg.gpr 26#5) = v_98 := hx26
  have hx27' : s.readReg64 (Reg.gpr 27#5) = ctxPtr := hx27
  dsimp only [stageP1ProgPlaced, stageP1EntryPlaced, preKeyRecordOut64At] at hpc ⊢
  conv =>
    arg 4
    simp (config := { maxSteps := 1000000 }) only [
      BitVec.add_assoc, BitVec.reduceAdd, sepConj_assoc]
  wp_steps_sync_pool_518 ext opkDropAddr
  refine SepWP.done _hpcm _hrunm ?_
  refine ⟨?_, rfl, rfl,
    by simp_all [arm64_norm], by simp_all [arm64_norm], by simp_all [arm64_norm],
    by simp_all [arm64_norm], by simp_all [arm64_norm], by simp_all [arm64_norm],
    by simp_all [arm64_norm], by simp_all [arm64_norm], by simp_all [arm64_norm],
    by simp_all [arm64_norm], by simp_all [arm64_norm], by simp_all [arm64_norm],
    by simp_all [arm64_norm], _hvm⟩
  simp only [BitVec.add_assoc, BitVec.reduceAdd]
  exact Entails.of_eq (by sep_ac_rfl)

/-! ## Arm 4a: `skit.kp` `.error` Poll-Unpack (`+0x07bc -> idKpDropAddr`) -/

set_option maxHeartbeats 1000000 in
/-- Segment P2.Err4a (`+0x07bc -> idKpDropAddr`) on `stageP1ProgPlaced ext` (fp-generalized) with
`VmPreserved`. -/
theorem p2_err4a_fp_ext_placed_wp [LibsignalPlacement] (ext : String → Option (State → State))
    (s : State) (coroPtr msgPtr ctxPtr idKpFutPtr idKpFutVt idKpDropAddr fp
    v_98 v_a0 v_b0 u_98 u_a0 u_a8 u_b0 u_b8 u_c0 u_d0 u_fp80 : BitVec 64)
    (opkId : BitVec 32)
    (b0 b1 b2 b3 b4 b5 b6 b63
     s0 s1_b s2 s3 s4 s5 s6 b_fp78 : BitVec 8)
    (w0 w1 w2 w3 w4 w5 w6 : BitVec 64)
    (hdrop_nz : idKpDropAddr ≠ 0#64)
    (hpc : s.pc = stageP1EntryPlaced + 0x7bc#64)
    (hrun : s.status = .Running)
    (_hsp_align : (s.sp &&& 15#64 == 0#64) = true)
    (hx19 : s.readReg64 .x19 = coroPtr)
    (hx21 : s.readReg64 .x21 = v_b0)
    (hx23 : s.readReg64 .x23 = v_a0)
    (hx24 : s.readReg64 .x24 = s.sp + 0x370#64)
    (hx26 : s.readReg64 .x26 = v_98)
    (hx27 : s.readReg64 .x27 = ctxPtr)
    (hx29 : s.readReg64 .x29 = fp) :
    SepWP (stageP1ProgPlaced ext) idKpDropAddr s
      (((s.sp + 0x3e0#64) ↦₈ 1#8) ∗
       keyPair64UnalignedAt (s.sp + 0x3e1#64) b0 b1 b2 b3 b4 b5 b6 w0 w1 w2 w3 w4 w5 w6 b63 ∗
       bytes7At (s.sp + 0x3c8#64) s0 s1_b s2 s3 s4 s5 s6 ∗
       ((fp + 0xffffffffffffff80#64) ↦₆₄ u_fp80) ∗
       ((fp + 0xffffffffffffff88#64) ↦₈ b_fp78) ∗
       ((s.sp + 0x98#64) ↦₆₄ u_98) ∗
       ((s.sp + 0xa0#64) ↦₆₄ u_a0) ∗
       ((s.sp + 0xa8#64) ↦₆₄ u_a8) ∗
       ((s.sp + 0xb0#64) ↦₆₄ u_b0) ∗
       ((s.sp + 0xb8#64) ↦₆₄ u_b8) ∗
       ((s.sp + 0xc0#64) ↦₆₄ u_c0) ∗
       ((s.sp + 0xd0#64) ↦₆₄ u_d0) ∗
       ((coroPtr + 0x4f8#64) ↦₆₄ idKpFutPtr) ∗
       ((coroPtr + 0x500#64) ↦₆₄ idKpFutVt) ∗
       ((msgPtr + 0x7c#64) ↦₃₂ opkId) ∗
       ((idKpFutVt + 0x0#64) ↦₆₄ᵣ idKpDropAddr))
      (fun s1 P_f =>
        (P_f ⊢
          ((s.sp + 0x3e0#64) ↦₈ 1#8) ∗
          keyPair64UnalignedAt (s.sp + 0x3e1#64) b0 b1 b2 b3 b4 b5 b6 w0 w1 w2 w3 w4 w5 w6 b63 ∗
          bytes7At (s.sp + 0x3c8#64) b0 b1 b2 b3 b4 b5 b6 ∗
          ((fp + 0xffffffffffffff80#64) ↦₆₄ w6) ∗
          ((fp + 0xffffffffffffff88#64) ↦₈ b63) ∗
          ((s.sp + 0x98#64) ↦₆₄ v_98) ∗
          ((s.sp + 0xa0#64) ↦₆₄ v_a0) ∗
          ((s.sp + 0xa8#64) ↦₆₄ w4) ∗
          ((s.sp + 0xb0#64) ↦₆₄ v_b0) ∗
          ((s.sp + 0xb8#64) ↦₆₄ w2) ∗
          ((s.sp + 0xc0#64) ↦₆₄ ctxPtr) ∗
          ((s.sp + 0xd0#64) ↦₆₄ w3) ∗
          ((coroPtr + 0x4f8#64) ↦₆₄ idKpFutPtr) ∗
          ((coroPtr + 0x500#64) ↦₆₄ idKpFutVt) ∗
          ((msgPtr + 0x7c#64) ↦₃₂ opkId) ∗
          ((idKpFutVt + 0x0#64) ↦₆₄ᵣ idKpDropAddr)) ∧
        s1.sp = s.sp ∧
        s1.trace = s.trace ∧
        s1.readReg64 .x0 = idKpFutPtr ∧
        s1.readReg64 .x19 = coroPtr ∧
        s1.readReg64 .x20 = w0 ∧
        s1.readReg64 .x21 = idKpFutPtr ∧
        s1.readReg64 .x22 = 1#64 ∧
        s1.readReg64 .x23 = w1 ∧
        s1.readReg64 .x24 = idKpFutVt ∧
        s1.readReg64 .x25 = s.readReg64 .x25 ∧
        s1.readReg64 .x26 = v_98 ∧
        s1.readReg64 .x27 = w5 ∧
        s1.readReg64 .x28 = s.readReg64 .x28 ∧
        s1.readReg64 .x29 = fp ∧
        s1.readReg64 .x30 = stageP1EntryPlaced + 0xac4#64 ∧
        calleeSavedVRegs s1 = calleeSavedVRegs s ∧
        VmPreserved s s1) := by
  have _hdrop_beq : (idKpDropAddr == 0#64) = false := beq_eq_false_iff_ne.mpr hdrop_nz
  have hx19' : s.readReg64 (Reg.gpr 19#5) = coroPtr := hx19
  have hx21' : s.readReg64 (Reg.gpr 21#5) = v_b0 := hx21
  have hx23' : s.readReg64 (Reg.gpr 23#5) = v_a0 := hx23
  have hx24' : s.readReg64 (Reg.gpr 24#5) = s.sp + 0x370#64 := hx24
  have hx26' : s.readReg64 (Reg.gpr 26#5) = v_98 := hx26
  have hx27' : s.readReg64 (Reg.gpr 27#5) = ctxPtr := hx27
  have hx29' : s.readReg64 (Reg.gpr 29#5) = fp := hx29
  dsimp only [stageP1ProgPlaced, stageP1EntryPlaced, keyPair64UnalignedAt, bytes7At] at hpc ⊢
  conv =>
    arg 4
    simp (config := { maxSteps := 1000000 }) only [
      BitVec.add_assoc, BitVec.reduceAdd, sepConj_assoc]
  wp_steps_sync_pool_518 ext idKpDropAddr
  refine SepWP.done _hpcm _hrunm ?_
  refine ⟨?_, rfl, rfl,
    by simp_all [arm64_norm], by simp_all [arm64_norm], by simp_all [arm64_norm],
    by simp_all [arm64_norm], by simp_all [arm64_norm], by simp_all [arm64_norm],
    by simp_all [arm64_norm], by simp_all [arm64_norm], by simp_all [arm64_norm],
    by simp_all [arm64_norm], by simp_all [arm64_norm], by simp_all [arm64_norm],
    by simp_all [arm64_norm], by simp_all [arm64_norm], _hvm⟩
  simp only [BitVec.add_assoc, BitVec.reduceAdd]
  exact Entails.of_eq (by sep_ac_rfl)

/-! ## Arm 3b & Arm 4b: Future Dealloc + Kyber Keypair Dealloc (`-> +0x1648`) -/

set_option maxHeartbeats 1200000 in
/-- Segment P2.Err3b (`+0x0e40 -> +0x1648`, generic `opkBoxSize`) on `stageP1ProgPlaced ext`,
threading `A.pool lim st s` across the 3 deallocations (`opkFutPtr`, `pkBuf` `1568` B, `skBuf`
`3168` B). -/
theorem p2_err3b_1568_hooks_placed_wp [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {st : M.σ}
    (ext : String → Option (State → State))
    (hH : StageP2ClosureHooksPlaced A lim ext)
    (s : State) (coroPtr opkFutPtr opkFutVt pkBuf skBuf outPtr
    w0 w1 w2 w4 w5 : BitVec 64)
    (opkBoxSize : Nat)
    (hbs_nz : BitVec.ofNat 64 opkBoxSize ≠ 0#64)
    (hbs_lt : opkBoxSize < 2 ^ 64)
    (hpc : s.pc = stageP1EntryPlaced + 0xe40#64)
    (hrun : s.status = .Running)
    (_hsp_align : (s.sp &&& 15#64 == 0#64) = true)
    (hx19 : s.readReg64 .x19 = coroPtr)
    (hx21 : s.readReg64 .x21 = opkFutPtr)
    (hx22 : s.readReg64 .x22 = 0xffffffffffffffff#64)
    (hx23 : s.readReg64 .x23 = w1)
    (hx24 : s.readReg64 .x24 = opkFutVt)
    (hx26 : s.readReg64 .x26 = w0)
    (hx27 : s.readReg64 .x27 = w5)
    (hx28 : s.readReg64 .x28 = s.sp + 0xa90#64) :
    SepWP (stageP1ProgPlaced ext) (stageP1EntryPlaced + 0x1648#64) s
      (((opkFutVt + 0x8#64) ↦₆₄ᵣ BitVec.ofNat 64 opkBoxSize) ∗
       ((opkFutVt + 0x10#64) ↦₆₄ᵣ 8#64) ∗
       A.live opkFutPtr opkBoxSize 8 ∗
       memRegion opkFutPtr opkBoxSize ∗
       ((coroPtr + 0x3d8#64) ↦₆₄ pkBuf) ∗
       ((coroPtr + 0x3e0#64) ↦₆₄ 0x620#64) ∗
       ((coroPtr + 0x3e8#64) ↦₆₄ skBuf) ∗
       ((coroPtr + 0x3f0#64) ↦₆₄ 0xc60#64) ∗
       A.live pkBuf 1568 1 ∗ memRegion pkBuf 1568 ∗
       A.live skBuf 3168 1 ∗ memRegion skBuf 3168 ∗
       A.pool lim st s ∗
       stackAt s.sp allocHookStack ∗
       ((coroPtr + 0x4f1#64) ↦₈ 1#8) ∗
       ((s.sp + 0xa8#64) ↦₆₄ w4) ∗
       ((s.sp + 0xb8#64) ↦₆₄ w2) ∗
       ((s.sp + 0xc8#64) ↦₆₄ outPtr))
      (fun s1 P_f =>
        let st' := M.stepEvents
          (rustDeallocEvents opkBoxSize 8 ++ rustDeallocEvents 1568 1 ++ rustDeallocEvents 3168 1) st
        (P_f ⊢
          ((opkFutVt + 0x8#64) ↦₆₄ᵣ BitVec.ofNat 64 opkBoxSize) ∗
          ((opkFutVt + 0x10#64) ↦₆₄ᵣ 8#64) ∗
          ((coroPtr + 0x3d8#64) ↦₆₄ pkBuf) ∗
          ((coroPtr + 0x3e0#64) ↦₆₄ 0x620#64) ∗
          ((coroPtr + 0x3e8#64) ↦₆₄ skBuf) ∗
          ((coroPtr + 0x3f0#64) ↦₆₄ 0xc60#64) ∗
          A.pool lim st' s1 ∗
          stackAt s.sp allocHookStack ∗
          ((coroPtr + 0x4f1#64) ↦₈ 0#8) ∗
          ((s.sp + 0xa8#64) ↦₆₄ w4) ∗
          ((s.sp + 0xb8#64) ↦₆₄ w2) ∗
          ((s.sp + 0xc8#64) ↦₆₄ outPtr)) ∧
        s1.sp = s.sp ∧
        s1.trace = s.trace ∧
        s1.readReg64 .x10 = w2 ∧
        s1.readReg64 .x19 = coroPtr ∧
        s1.readReg64 .x20 = w0 ∧
        s1.readReg64 .x21 = w4 >>> 8 ∧
        s1.readReg64 .x22 = w1 >>> 32 ∧
        s1.readReg64 .x23 = w1 ∧
        s1.readReg64 .x24 = w2 >>> 32 ∧
        s1.readReg64 .x25 = s.readReg64 .x25 ∧
        s1.readReg64 .x26 = outPtr ∧
        s1.readReg64 .x27 = w5 ∧
        s1.readReg64 .x28 = s.sp + 0xa90#64 ∧
        s1.readReg64 .x29 = s.readReg64 .x29 ∧
        calleeSavedVRegs s1 = calleeSavedVRegs s ∧
        M.liveBytes st' ≤ M.liveBytes st) := by
  have hdealloc := hH.dealloc
  have _hbs_beq : (BitVec.ofNat 64 opkBoxSize == 0#64) = false := beq_eq_false_iff_ne.mpr hbs_nz
  have _hbs_toNat : (BitVec.ofNat 64 opkBoxSize).toNat = opkBoxSize := Nat.mod_eq_of_lt hbs_lt
  have hx19' : s.readReg64 (Reg.gpr 19#5) = coroPtr := hx19
  have hx21' : s.readReg64 (Reg.gpr 21#5) = opkFutPtr := hx21
  have hx22' : s.readReg64 (Reg.gpr 22#5) = 0xffffffffffffffff#64 := hx22
  have hx23' : s.readReg64 (Reg.gpr 23#5) = w1 := hx23
  have hx24' : s.readReg64 (Reg.gpr 24#5) = opkFutVt := hx24
  have hx26' : s.readReg64 (Reg.gpr 26#5) = w0 := hx26
  have hx27' : s.readReg64 (Reg.gpr 27#5) = w5 := hx27
  have hx28' : s.readReg64 (Reg.gpr 28#5) = s.sp + 0xa90#64 := hx28
  dsimp only [stageP1ProgPlaced, stageP1EntryPlaced, lsRustDeallocSym] at hdealloc hpc ⊢
  wp_steps_sync_pool_518 ext (lsρ "_RNvCs1njKG4L9aB3_7___rustc14___rust_dealloc")
  clear _hvm _hpcm _hrunm
  wp_call hdealloc (opkFutPtr, opkBoxSize, 8, st)
  wp_steps_sync_pool_518 ext (lsρ "_RNvCs1njKG4L9aB3_7___rustc14___rust_dealloc")
  clear _hvm _hpcm _hrunm
  wp_call hdealloc (pkBuf, 1568, 1, M.stepEvents (rustDeallocEvents opkBoxSize 8) st)
  wp_steps_sync_pool_518 ext (lsρ "_RNvCs1njKG4L9aB3_7___rustc14___rust_dealloc")
  clear _hvm _hpcm _hrunm
  rw [hsp_sf]
  wp_call hdealloc (skBuf, 3168, 1,
    M.stepEvents (rustDeallocEvents 1568 1) (M.stepEvents (rustDeallocEvents opkBoxSize 8) st))
  wp_steps_sync_pool_518 ext (blkPl_518.base + 5704#64)
  rw [hsp_sf_1, hsp_sf]
  refine SepWP.done _hpcm _hrunm ?_
  refine ⟨?_,
    by simp_all [arm64_norm], by simp_all [arm64_norm, AllocCallPreserved],
    by simp_all [arm64_norm], by simp_all [arm64_norm], by simp_all [arm64_norm],
    by simp_all [arm64_norm], by simp_all [arm64_norm], by simp_all [arm64_norm],
    by simp_all [arm64_norm], by simp_all [arm64_norm], by simp_all [arm64_norm],
    by simp_all [arm64_norm], by simp_all [arm64_norm], by simp_all [arm64_norm],
    by simp_all [arm64_norm],
    Nat.le_trans
      (M.liveBytes_free_le 1 3168 (M.step (.free 1 1568) (M.step (.free 8 opkBoxSize) st)))
      (Nat.le_trans
        (M.liveBytes_free_le 1 1568 (M.step (.free 8 opkBoxSize) st))
        (M.liveBytes_free_le 8 opkBoxSize st))⟩
  rw [← M.stepEvents_append, ← M.stepEvents_append, ← List.append_assoc]
  exact Entails.of_eq (by sep_ac_rfl)

abbrev p2_err3b_1568_4k_placed_wp := @p2_err3b_1568_hooks_placed_wp
abbrev p2_err3b_1568_ext_placed_wp := @p2_err3b_1568_hooks_placed_wp
abbrev p2_err3b_1568_gen_placed_wp := @p2_err3b_1568_hooks_placed_wp

set_option maxHeartbeats 1200000 in
/-- Segment P2.Err4b (`+0x0ac4 -> +0x1648`, generic `kpBoxSize`) on `stageP1ProgPlaced ext`,
threading `A.pool lim st s` across the 3 deallocations (`idKpFutPtr`, `pkBuf` `1568` B, `skBuf`
`3168` B). -/
theorem p2_err4b_1568_hooks_placed_wp [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {st : M.σ}
    (ext : String → Option (State → State))
    (hH : StageP2ClosureHooksPlaced A lim ext)
    (s : State) (coroPtr idKpFutPtr idKpFutVt pkBuf skBuf outPtr
    w0 w1 w2 w4 w5 : BitVec 64)
    (kpBoxSize : Nat)
    (hbs_nz : BitVec.ofNat 64 kpBoxSize ≠ 0#64)
    (hbs_lt : kpBoxSize < 2 ^ 64)
    (hpc : s.pc = stageP1EntryPlaced + 0xac4#64)
    (hrun : s.status = .Running)
    (_hsp_align : (s.sp &&& 15#64 == 0#64) = true)
    (hx19 : s.readReg64 .x19 = coroPtr)
    (hx20 : s.readReg64 .x20 = w0)
    (hx21 : s.readReg64 .x21 = idKpFutPtr)
    (hx22 : s.readReg64 .x22 = 1#64)
    (hx23 : s.readReg64 .x23 = w1)
    (hx24 : s.readReg64 .x24 = idKpFutVt)
    (hx27 : s.readReg64 .x27 = w5)
    (hx28 : s.readReg64 .x28 = s.sp + 0xa90#64) :
    SepWP (stageP1ProgPlaced ext) (stageP1EntryPlaced + 0x1648#64) s
      (((idKpFutVt + 0x8#64) ↦₆₄ᵣ BitVec.ofNat 64 kpBoxSize) ∗
       ((idKpFutVt + 0x10#64) ↦₆₄ᵣ 8#64) ∗
       A.live idKpFutPtr kpBoxSize 8 ∗
       memRegion idKpFutPtr kpBoxSize ∗
       ((coroPtr + 0x3d8#64) ↦₆₄ pkBuf) ∗
       ((coroPtr + 0x3e0#64) ↦₆₄ 0x620#64) ∗
       ((coroPtr + 0x3e8#64) ↦₆₄ skBuf) ∗
       ((coroPtr + 0x3f0#64) ↦₆₄ 0xc60#64) ∗
       A.live pkBuf 1568 1 ∗ memRegion pkBuf 1568 ∗
       A.live skBuf 3168 1 ∗ memRegion skBuf 3168 ∗
       A.pool lim st s ∗
       stackAt s.sp allocHookStack ∗
       ((coroPtr + 0x4f1#64) ↦₈ 1#8) ∗
       ((s.sp + 0xa8#64) ↦₆₄ w4) ∗
       ((s.sp + 0xb8#64) ↦₆₄ w2) ∗
       ((s.sp + 0xc8#64) ↦₆₄ outPtr))
      (fun s1 P_f =>
        let st' := M.stepEvents
          (rustDeallocEvents kpBoxSize 8 ++ rustDeallocEvents 1568 1 ++ rustDeallocEvents 3168 1) st
        (P_f ⊢
          ((idKpFutVt + 0x8#64) ↦₆₄ᵣ BitVec.ofNat 64 kpBoxSize) ∗
          ((idKpFutVt + 0x10#64) ↦₆₄ᵣ 8#64) ∗
          ((coroPtr + 0x3d8#64) ↦₆₄ pkBuf) ∗
          ((coroPtr + 0x3e0#64) ↦₆₄ 0x620#64) ∗
          ((coroPtr + 0x3e8#64) ↦₆₄ skBuf) ∗
          ((coroPtr + 0x3f0#64) ↦₆₄ 0xc60#64) ∗
          A.pool lim st' s1 ∗
          stackAt s.sp allocHookStack ∗
          ((coroPtr + 0x4f1#64) ↦₈ 0#8) ∗
          ((s.sp + 0xa8#64) ↦₆₄ w4) ∗
          ((s.sp + 0xb8#64) ↦₆₄ w2) ∗
          ((s.sp + 0xc8#64) ↦₆₄ outPtr)) ∧
        s1.sp = s.sp ∧
        s1.trace = s.trace ∧
        s1.readReg64 .x10 = w2 ∧
        s1.readReg64 .x19 = coroPtr ∧
        s1.readReg64 .x20 = w0 ∧
        s1.readReg64 .x21 = w4 >>> 8 ∧
        s1.readReg64 .x22 = w1 >>> 32 ∧
        s1.readReg64 .x23 = w1 ∧
        s1.readReg64 .x24 = w2 >>> 32 ∧
        s1.readReg64 .x25 = s.readReg64 .x25 ∧
        s1.readReg64 .x26 = outPtr ∧
        s1.readReg64 .x27 = w5 ∧
        s1.readReg64 .x28 = s.sp + 0xa90#64 ∧
        s1.readReg64 .x29 = s.readReg64 .x29 ∧
        calleeSavedVRegs s1 = calleeSavedVRegs s ∧
        M.liveBytes st' ≤ M.liveBytes st) := by
  have hdealloc := hH.dealloc
  have _hbs_beq : (BitVec.ofNat 64 kpBoxSize == 0#64) = false := beq_eq_false_iff_ne.mpr hbs_nz
  have _hbs_toNat : (BitVec.ofNat 64 kpBoxSize).toNat = kpBoxSize := Nat.mod_eq_of_lt hbs_lt
  have hx19' : s.readReg64 (Reg.gpr 19#5) = coroPtr := hx19
  have hx20' : s.readReg64 (Reg.gpr 20#5) = w0 := hx20
  have hx21' : s.readReg64 (Reg.gpr 21#5) = idKpFutPtr := hx21
  have hx22' : s.readReg64 (Reg.gpr 22#5) = 1#64 := hx22
  have hx23' : s.readReg64 (Reg.gpr 23#5) = w1 := hx23
  have hx24' : s.readReg64 (Reg.gpr 24#5) = idKpFutVt := hx24
  have hx27' : s.readReg64 (Reg.gpr 27#5) = w5 := hx27
  have hx28' : s.readReg64 (Reg.gpr 28#5) = s.sp + 0xa90#64 := hx28
  dsimp only [stageP1ProgPlaced, stageP1EntryPlaced, lsRustDeallocSym] at hdealloc hpc ⊢
  wp_steps_sync_pool_518 ext (lsρ "_RNvCs1njKG4L9aB3_7___rustc14___rust_dealloc")
  clear _hvm _hpcm _hrunm
  wp_call hdealloc (idKpFutPtr, kpBoxSize, 8, st)
  wp_steps_sync_pool_518 ext (lsρ "_RNvCs1njKG4L9aB3_7___rustc14___rust_dealloc")
  clear _hvm _hpcm _hrunm
  wp_call hdealloc (pkBuf, 1568, 1, M.stepEvents (rustDeallocEvents kpBoxSize 8) st)
  wp_steps_sync_pool_518 ext (lsρ "_RNvCs1njKG4L9aB3_7___rustc14___rust_dealloc")
  clear _hvm _hpcm _hrunm
  rw [hsp_sf]
  wp_call hdealloc (skBuf, 3168, 1,
    M.stepEvents (rustDeallocEvents 1568 1) (M.stepEvents (rustDeallocEvents kpBoxSize 8) st))
  wp_steps_sync_pool_518 ext (blkPl_518.base + 5704#64)
  rw [hsp_sf_1, hsp_sf]
  refine SepWP.done _hpcm _hrunm ?_
  refine ⟨?_,
    by simp_all [arm64_norm], by simp_all [arm64_norm, AllocCallPreserved],
    by simp_all [arm64_norm], by simp_all [arm64_norm], by simp_all [arm64_norm],
    by simp_all [arm64_norm], by simp_all [arm64_norm], by simp_all [arm64_norm],
    by simp_all [arm64_norm], by simp_all [arm64_norm], by simp_all [arm64_norm],
    by simp_all [arm64_norm], by simp_all [arm64_norm], by simp_all [arm64_norm],
    by simp_all [arm64_norm],
    Nat.le_trans
      (M.liveBytes_free_le 1 3168 (M.step (.free 1 1568) (M.step (.free 8 kpBoxSize) st)))
      (Nat.le_trans
        (M.liveBytes_free_le 1 1568 (M.step (.free 8 kpBoxSize) st))
        (M.liveBytes_free_le 8 kpBoxSize st))⟩
  rw [← M.stepEvents_append, ← M.stepEvents_append, ← List.append_assoc]
  exact Entails.of_eq (by sep_ac_rfl)

abbrev p2_err4b_1568_4k_placed_wp := @p2_err4b_1568_hooks_placed_wp
abbrev p2_err4b_1568_ext_placed_wp := @p2_err4b_1568_hooks_placed_wp
abbrev p2_err4b_1568_gen_placed_wp := @p2_err4b_1568_hooks_placed_wp

end LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Kits.StageP2BlocksErrBPlacedBudget
