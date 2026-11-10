/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Kits.StageP2DefsPlacedBudget
public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Kits.StageP2BlocksErrBPlacedBudget
public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Kits.StageP2BlocksErrCPlaced
public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Kits.StageP1StepsXExtPlacedBudgetAux
public import LibsignalBinary.Heap.IfaceBudget
public import LibsignalBinary.Heap.IfaceBudgetLemmas
public import LibsignalBinary.Proofs.Placed.BudgetVmSteps
public meta import Lean.Elab.Tactic -- shake: keep
import LibsignalBinary.Proofs.Common.SharedHelpers
meta import LibsignalBinary.Proofs.Common.SharedHelpers -- shake: keep
import Arm64.Trusted.Spec.Hoare
import Arm64.Trusted.Spec.SepLogic
import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.GenP3.DropSs3ExtPlaced
import LibsignalBinary.Proofs.E2E.InMem.HashbrownBin.IdentityKeyStoreFutures.SaveIdentity
import LibsignalBinary.Proofs.E2E.InMem.HashbrownBin.SessionStoreFutures.StoreCommon
import LibsignalBinary.Proofs.E2E.Record.Serialization.SessionCloneAux.Base
import LibsignalBinary.Proofs.SpqrV1.Poly.EncoderFromPb.Defs
import LibsignalBinary.Proofs.SpqrV1.Poly.EncoderIntoPb.Defs
import LibsignalBinary.Proofs.SpqrV1.Prost.MessageEncode.Base
import LibsignalBinary.Proofs.SpqrV1.Prost.MessageMerge.PolyCommon
import LibsignalBinary.Proofs.TripleRatchet.GeneralizeEntry
import LibsignalBinary.Proofs.TripleRatchet.ReceiveRatchet.From.Callees
import LibsignalBinary.Proofs.TripleRatchet.ReceiveRatchet.From.Step244

/-!
# Budget-Threaded Relocatable Stage P2 Basic Blocks — Error Arms 5 and 6 and Shared Epilogue

`RustCliAllocBudget M` / `VmPreserved` basic-block lemmas for Stage P2 unwind Arms 5 and 6 and the
`prevCap ≠ 0` return epilogue (`+0x359c → retAddr`) on Block `518`.
-/

@[expose] public section

set_option autoImplicit false

namespace LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Kits.StageP2BlocksErrCPlacedBudget

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
  LibsignalPlacement lsRustDeallocSym lsmpl lsρ
)
open CryptoVerification.RustHeap (allocHookStack)
open CryptoVerification.LibsignalPublicApi.StoreKit (speWordsAt)
open CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.Kits (
  p2_cond_ne_adds64_of_ne_neg2 p2_cond_ne_adds64_of_ne_neg3
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

/-! ## Arm 5: `initialize_bob_session` `Err` (`+0x125c -> +0x1648`) -/

set_option maxHeartbeats 1200000 in
/-- Segment P2.Err5 (`+0x125c -> +0x1648`) on `stageP1ProgPlaced ext`,
threading `A.pool lim st s` across the 2 Kyber keypair deallocations (`pkBuf` `1568` B and `skBuf`
`3168` B). -/
theorem p2_err5_1568_hooks_placed_wp [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {st : M.σ}
    (ext : String → Option (State → State))
    (hH : StageP2ClosureHooksPlaced A lim ext)
    (s : State) (coroPtr pkBuf skBuf outPtr
    w0 w1 w2 w3 w4 w5 u_88 u_a8 u_b8 u_d0 : BitVec 64)
    (hpc : s.pc = stageP1EntryPlaced + 0x125c#64)
    (hrun : s.status = .Running)
    (_hsp_align : (s.sp &&& 15#64 == 0#64) = true)
    (hx19 : s.readReg64 .x19 = coroPtr)
    (hx28 : s.readReg64 .x28 = s.sp + 0xa90#64) :
    SepWP (stageP1ProgPlaced ext) (stageP1EntryPlaced + 0x1648#64) s
      (((s.sp + 0x3e0#64) ↦₆₄ 0xffffffffffffffff#64) ∗
       speWordsAt (s.sp + 0x3e8#64) w0 w1 w2 w3 w4 w5 ∗
       ((coroPtr + 0x718#64) ↦₆₄ pkBuf) ∗
       ((coroPtr + 0x720#64) ↦₆₄ 0x620#64) ∗
       ((coroPtr + 0x728#64) ↦₆₄ skBuf) ∗
       ((coroPtr + 0x730#64) ↦₆₄ 0xc60#64) ∗
       A.live pkBuf 1568 1 ∗ memRegion pkBuf 1568 ∗
       A.live skBuf 3168 1 ∗ memRegion skBuf 3168 ∗
       A.pool lim st s ∗
       stackAt s.sp allocHookStack ∗
       ((coroPtr + 0x4f1#64) ↦₈ 0#8) ∗
       ((s.sp + 0x88#64) ↦₆₄ u_88) ∗
       ((s.sp + 0xa8#64) ↦₆₄ u_a8) ∗
       ((s.sp + 0xb8#64) ↦₆₄ u_b8) ∗
       ((s.sp + 0xc8#64) ↦₆₄ outPtr) ∗
       ((s.sp + 0xd0#64) ↦₆₄ u_d0))
      (fun s1 P_f =>
        let st' := M.stepEvents (rustDeallocEvents 1568 1 ++ rustDeallocEvents 3168 1) st
        (P_f ⊢
          ((s.sp + 0x3e0#64) ↦₆₄ 0xffffffffffffffff#64) ∗
          speWordsAt (s.sp + 0x3e8#64) w0 w1 w2 w3 w4 w5 ∗
          ((coroPtr + 0x718#64) ↦₆₄ pkBuf) ∗
          ((coroPtr + 0x720#64) ↦₆₄ 0x620#64) ∗
          ((coroPtr + 0x728#64) ↦₆₄ skBuf) ∗
          ((coroPtr + 0x730#64) ↦₆₄ 0xc60#64) ∗
          A.pool lim st' s1 ∗
          stackAt s.sp allocHookStack ∗
          ((coroPtr + 0x4f1#64) ↦₈ 0#8) ∗
          ((s.sp + 0x88#64) ↦₆₄ w0) ∗
          ((s.sp + 0xa8#64) ↦₆₄ w4) ∗
          ((s.sp + 0xb8#64) ↦₆₄ w2) ∗
          ((s.sp + 0xc8#64) ↦₆₄ outPtr) ∗
          ((s.sp + 0xd0#64) ↦₆₄ w3)) ∧
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
  have hx19' : s.readReg64 (Reg.gpr 19#5) = coroPtr := hx19
  have hx28' : s.readReg64 (Reg.gpr 28#5) = s.sp + 0xa90#64 := hx28
  dsimp only [stageP1ProgPlaced, stageP1EntryPlaced, lsRustDeallocSym, speWordsAt] at hdealloc hpc ⊢
  conv =>
    arg 4
    simp (config := { maxSteps := 1000000 }) only [
      BitVec.add_assoc, BitVec.reduceAdd, sepConj_assoc]
  wp_steps_sync_pool_518 ext (lsρ "_RNvCs1njKG4L9aB3_7___rustc14___rust_dealloc")
  clear _hvm _hpcm _hrunm
  wp_call hdealloc (pkBuf, 1568, 1, st)
  wp_steps_sync_pool_518 ext (lsρ "_RNvCs1njKG4L9aB3_7___rustc14___rust_dealloc")
  clear _hvm _hpcm _hrunm
  wp_call hdealloc (skBuf, 3168, 1, M.stepEvents (rustDeallocEvents 1568 1) st)
  wp_steps_sync_pool_518 ext (blkPl_518.base + 5704#64)
  rw [hsp_sf]
  refine SepWP.done _hpcm _hrunm ?_
  refine ⟨?_,
    by simp_all [arm64_norm], by simp_all [arm64_norm, AllocCallPreserved],
    by simp_all [arm64_norm], by simp_all [arm64_norm], by simp_all [arm64_norm],
    by simp_all [arm64_norm], by simp_all [arm64_norm], by simp_all [arm64_norm],
    by simp_all [arm64_norm], by simp_all [arm64_norm], by simp_all [arm64_norm],
    by simp_all [arm64_norm], by simp_all [arm64_norm], by simp_all [arm64_norm],
    by simp_all [arm64_norm],
    Nat.le_trans
      (M.liveBytes_free_le 1 3168 (M.step (.free 1 1568) st))
      (M.liveBytes_free_le 1 1568 st)⟩
  rw [← M.stepEvents_append]
  simp only [BitVec.add_assoc, BitVec.reduceAdd]
  exact Entails.of_eq (by sep_ac_rfl)

abbrev p2_err5_1568_4k_placed_wp := @p2_err5_1568_hooks_placed_wp
abbrev p2_err5_1568_ext_placed_wp := @p2_err5_1568_hooks_placed_wp

/-! ## Arm 6a: `skit.regId` `.error` Poll-Unpack (`+0x09f4 -> localRegIdDropAddr`) -/

set_option maxHeartbeats 1000000 in
/-- Segment P2.Err6a (`+0x09f4 -> localRegIdDropAddr`) on `stageP1ProgPlaced ext` with
`VmPreserved`. -/
theorem p2_err6a_ext_placed_wp [LibsignalPlacement] (ext : String → Option (State → State))
    (s : State) (coroPtr regIdFutPtr regIdFutVt localRegIdDropAddr
    w0 w1 w2 w3 w4 w5
    v_98 v_a0 v_b0 u_88 u_98 u_a0 u_a8 u_b0 u_b8 u_d0 : BitVec 64)
    (hw0_ne_neg3 : w0 ≠ 0xfffffffffffffffd#64)
    (hdrop_nz : localRegIdDropAddr ≠ 0#64)
    (hpc : s.pc = stageP1EntryPlaced + 0x9f4#64)
    (hrun : s.status = .Running)
    (_hsp_align : (s.sp &&& 15#64 == 0#64) = true)
    (hx19 : s.readReg64 .x19 = coroPtr)
    (hx21 : s.readReg64 .x21 = v_b0)
    (hx23 : s.readReg64 .x23 = v_a0)
    (hx26 : s.readReg64 .x26 = v_98) :
    SepWP (stageP1ProgPlaced ext) localRegIdDropAddr s
      (speWordsAt (s.sp + 0x3e0#64) w0 w1 w2 w3 w4 w5 ∗
       ((coroPtr + 0x788#64) ↦₆₄ regIdFutPtr) ∗
       ((coroPtr + 0x790#64) ↦₆₄ regIdFutVt) ∗
       ((regIdFutVt + 0x0#64) ↦₆₄ᵣ localRegIdDropAddr) ∗
       ((s.sp + 0x88#64) ↦₆₄ u_88) ∗
       ((s.sp + 0x98#64) ↦₆₄ u_98) ∗
       ((s.sp + 0xa0#64) ↦₆₄ u_a0) ∗
       ((s.sp + 0xa8#64) ↦₆₄ u_a8) ∗
       ((s.sp + 0xb0#64) ↦₆₄ u_b0) ∗
       ((s.sp + 0xb8#64) ↦₆₄ u_b8) ∗
       ((s.sp + 0xd0#64) ↦₆₄ u_d0))
      (fun s1 P_f =>
        (P_f ⊢
          speWordsAt (s.sp + 0x3e0#64) w0 w1 w2 w3 w4 w5 ∗
          ((coroPtr + 0x788#64) ↦₆₄ regIdFutPtr) ∗
          ((coroPtr + 0x790#64) ↦₆₄ regIdFutVt) ∗
          ((regIdFutVt + 0x0#64) ↦₆₄ᵣ localRegIdDropAddr) ∗
          ((s.sp + 0x88#64) ↦₆₄ w0) ∗
          ((s.sp + 0x98#64) ↦₆₄ v_98) ∗
          ((s.sp + 0xa0#64) ↦₆₄ v_a0) ∗
          ((s.sp + 0xa8#64) ↦₆₄ w4) ∗
          ((s.sp + 0xb0#64) ↦₆₄ v_b0) ∗
          ((s.sp + 0xb8#64) ↦₆₄ w2) ∗
          ((s.sp + 0xd0#64) ↦₆₄ w3)) ∧
        s1.sp = s.sp ∧
        s1.trace = s.trace ∧
        s1.readReg64 .x0 = regIdFutPtr ∧
        s1.readReg64 .x19 = coroPtr ∧
        s1.readReg64 .x21 = regIdFutPtr ∧
        s1.readReg64 .x22 = w1 >>> 32 ∧
        s1.readReg64 .x23 = (w1.extractLsb' 0 32).zeroExtend 64 ∧
        s1.readReg64 .x24 = regIdFutVt ∧
        s1.readReg64 .x25 = s.readReg64 .x25 ∧
        s1.readReg64 .x26 = v_98 ∧
        s1.readReg64 .x27 = w5 ∧
        s1.readReg64 .x28 = s.readReg64 .x28 ∧
        s1.readReg64 .x29 = s.readReg64 .x29 ∧
        s1.readReg64 .x30 = stageP1EntryPlaced + 0xb3c#64 ∧
        calleeSavedVRegs s1 = calleeSavedVRegs s ∧
        VmPreserved s s1) := by
  have _hcond_ne3 : ConditionHolds CondCode.NE (addsPState64 w0 3#64) = true :=
    p2_cond_ne_adds64_of_ne_neg3 hw0_ne_neg3
  have _hcond_eq3 : ConditionHolds CondCode.EQ (addsPState64 w0 3#64) = false := by
    simp only [ConditionHolds] at _hcond_ne3 ⊢
    revert _hcond_ne3
    cases (addsPState64 w0 3#64).z <;> decide
  have _hdrop_beq : (localRegIdDropAddr == 0#64) = false := beq_eq_false_iff_ne.mpr hdrop_nz
  have hx19' : s.readReg64 (Reg.gpr 19#5) = coroPtr := hx19
  have hx21' : s.readReg64 (Reg.gpr 21#5) = v_b0 := hx21
  have hx23' : s.readReg64 (Reg.gpr 23#5) = v_a0 := hx23
  have hx26' : s.readReg64 (Reg.gpr 26#5) = v_98 := hx26
  dsimp only [stageP1ProgPlaced, stageP1EntryPlaced, speWordsAt] at hpc ⊢
  conv =>
    arg 4
    simp (config := { maxSteps := 1000000 }) only [
      BitVec.add_assoc, BitVec.reduceAdd, sepConj_assoc]
  have hsplit3e8 :
      ((s.sp + 1000#64) ↦₆₄ w1) =
        (((s.sp + 1000#64) ↦₃₂ w1.extractLsb' 0 32) ∗
         ((s.sp + 1004#64) ↦₃₂ w1.extractLsb' 32 32)) := by
    simpa [BitVec.add_assoc, BitVec.reduceAdd] using (pointsTo64_split32 (s.sp + 1000#64) w1)
  conv =>
    arg 4
    rw [hsplit3e8]
    simp only [sepConj_assoc]
  wp_steps_sync_pool_518 ext localRegIdDropAddr
  refine SepWP.done _hpcm _hrunm ?_
  refine ⟨?_, rfl, rfl,
    by simp_all [arm64_norm], by simp_all [arm64_norm], by simp_all [arm64_norm],
    by simp_all [arm64_norm]; clear * -; bv_bits,
    by simp_all [arm64_norm], by simp_all [arm64_norm], by simp_all [arm64_norm],
    by simp_all [arm64_norm], by simp_all [arm64_norm], by simp_all [arm64_norm],
    by simp_all [arm64_norm], by simp_all [arm64_norm], by simp_all [arm64_norm],
    _hvm⟩
  simp only [BitVec.add_assoc, BitVec.reduceAdd, hsplit3e8]
  exact Entails.of_eq (by sep_ac_rfl)

/-! ## Arm 6b: `regIdFutPtr` Dealloc, `drop_session_structure3` Call Cut, & Kyber Keypair Dealloc -/

set_option maxHeartbeats 1000000 in
/-- Segment P2.Err6b-A (`+0x0b3c -> lsmpl.base 512`, generic `regIdBoxSize`) on
`stageP1ProgPlaced ext`, threading
`A.pool lim st s -> A.pool lim (M.stepEvents (rustDeallocEvents regIdBoxSize 8) st) s1`
across `rustCliDeallocBudgetSpec M A lim`. -/
theorem p2_err6b_a_hooks_placed_wp [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {st : M.σ}
    (ext : String → Option (State → State))
    (hH : StageP2ClosureHooksPlaced A lim ext)
    (s : State) (coroPtr regIdFutPtr regIdFutVt w0 : BitVec 64)
    (regIdBoxSize : Nat)
    (hw0_ne_neg2 : w0 ≠ 0xfffffffffffffffe#64)
    (hbs_nz : BitVec.ofNat 64 regIdBoxSize ≠ 0#64)
    (hbs_lt : regIdBoxSize < 2 ^ 64)
    (hpc : s.pc = stageP1EntryPlaced + 0xb3c#64)
    (hrun : s.status = .Running)
    (_hsp_align : (s.sp &&& 15#64 == 0#64) = true)
    (hx19 : s.readReg64 .x19 = coroPtr)
    (hx21 : s.readReg64 .x21 = regIdFutPtr)
    (hx24 : s.readReg64 .x24 = regIdFutVt) :
    SepWP (stageP1ProgPlaced ext) (lsmpl.base 512) s
      (((regIdFutVt + 0x8#64) ↦₆₄ᵣ BitVec.ofNat 64 regIdBoxSize) ∗
       ((regIdFutVt + 0x10#64) ↦₆₄ᵣ 8#64) ∗
       A.live regIdFutPtr regIdBoxSize 8 ∗
       memRegion regIdFutPtr regIdBoxSize ∗
       A.pool lim st s ∗
       stackAt s.sp allocHookStack ∗
       ((s.sp + 0x88#64) ↦₆₄ w0))
      (fun s1 P_f =>
        let st' := M.stepEvents (rustDeallocEvents regIdBoxSize 8) st
        (P_f ⊢
          ((regIdFutVt + 0x8#64) ↦₆₄ᵣ BitVec.ofNat 64 regIdBoxSize) ∗
          ((regIdFutVt + 0x10#64) ↦₆₄ᵣ 8#64) ∗
          A.pool lim st' s1 ∗
          stackAt s.sp allocHookStack ∗
          ((s.sp + 0x88#64) ↦₆₄ w0)) ∧
        s1.sp = s.sp ∧
        s1.trace = s.trace ∧
        s1.readReg64 .x0 = coroPtr + 0x4f8#64 ∧
        s1.readReg64 .x19 = coroPtr ∧
        s1.readReg64 .x22 = s.readReg64 .x22 ∧
        s1.readReg64 .x23 = s.readReg64 .x23 ∧
        s1.readReg64 .x25 = s.readReg64 .x25 ∧
        s1.readReg64 .x26 = s.readReg64 .x26 ∧
        s1.readReg64 .x27 = s.readReg64 .x27 ∧
        s1.readReg64 .x28 = s.readReg64 .x28 ∧
        s1.readReg64 .x29 = s.readReg64 .x29 ∧
        s1.readReg64 .x30 = stageP1EntryPlaced + 0x12f8#64 ∧
        calleeSavedVRegs s1 = calleeSavedVRegs s ∧
        M.liveBytes st' ≤ M.liveBytes st) := by
  have hdealloc := hH.dealloc
  have _hcond_ne2 : ConditionHolds CondCode.NE (addsPState64 w0 2#64) = true :=
    p2_cond_ne_adds64_of_ne_neg2 hw0_ne_neg2
  have _hcond_eq2 : ConditionHolds CondCode.EQ (addsPState64 w0 2#64) = false := by
    simp only [ConditionHolds] at _hcond_ne2 ⊢
    revert _hcond_ne2
    cases (addsPState64 w0 2#64).z <;> decide
  have _hbs_beq : (BitVec.ofNat 64 regIdBoxSize == 0#64) = false := beq_eq_false_iff_ne.mpr hbs_nz
  have _hbs_toNat : (BitVec.ofNat 64 regIdBoxSize).toNat = regIdBoxSize := Nat.mod_eq_of_lt hbs_lt
  have hx19' : s.readReg64 (Reg.gpr 19#5) = coroPtr := hx19
  have hx21' : s.readReg64 (Reg.gpr 21#5) = regIdFutPtr := hx21
  have hx24' : s.readReg64 (Reg.gpr 24#5) = regIdFutVt := hx24
  dsimp only [stageP1ProgPlaced, stageP1EntryPlaced, lsRustDeallocSym] at hdealloc hpc ⊢
  wp_steps_sync_pool_518 ext (lsρ "_RNvCs1njKG4L9aB3_7___rustc14___rust_dealloc")
  clear _hvm _hpcm _hrunm
  wp_call hdealloc (regIdFutPtr, regIdBoxSize, 8, st)
  wp_steps_sync_pool_518 ext (lsmpl.base 512)
  refine SepWP.done _hpcm _hrunm ?_
  refine ⟨Entails.of_eq (by sep_ac_rfl),
    by simp_all [arm64_norm], by simp_all [arm64_norm, AllocCallPreserved],
    by simp_all [arm64_norm], by simp_all [arm64_norm], by simp_all [arm64_norm],
    by simp_all [arm64_norm], by simp_all [arm64_norm], by simp_all [arm64_norm],
    by simp_all [arm64_norm], by simp_all [arm64_norm], by simp_all [arm64_norm],
    by simp_all [arm64_norm], by simp_all [arm64_norm],
    M.liveBytes_free_le 8 regIdBoxSize st⟩

abbrev p2_err6b_a_4k_placed_wp := @p2_err6b_a_hooks_placed_wp
abbrev p2_err6b_a_ext_placed_wp := @p2_err6b_a_hooks_placed_wp
abbrev p2_err6b_a_gen_placed_wp := @p2_err6b_a_hooks_placed_wp

set_option maxHeartbeats 1200000 in
/-- Segment P2.Err6b-B (`+0x12f8 -> +0x1648`) on `stageP1ProgPlaced ext`,
threading `A.pool lim st s` across the 2 Kyber keypair deallocations (`pkBuf` `1568` B and `skBuf`
`3168` B). -/
theorem p2_err6b_b_1568_hooks_placed_wp [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {st : M.σ}
    (ext : String → Option (State → State))
    (hH : StageP2ClosureHooksPlaced A lim ext)
    (s : State) (coroPtr pkBuf skBuf outPtr
    w0 w1 w2 w4 w5 : BitVec 64)
    (hpc : s.pc = stageP1EntryPlaced + 0x12f8#64)
    (hrun : s.status = .Running)
    (_hsp_align : (s.sp &&& 15#64 == 0#64) = true)
    (hx19 : s.readReg64 .x19 = coroPtr)
    (hx22 : s.readReg64 .x22 = w1 >>> 32)
    (hx23 : s.readReg64 .x23 = (w1.extractLsb' 0 32).zeroExtend 64)
    (hx27 : s.readReg64 .x27 = w5)
    (hx28 : s.readReg64 .x28 = s.sp + 0xa90#64) :
    SepWP (stageP1ProgPlaced ext) (stageP1EntryPlaced + 0x1648#64) s
      (((coroPtr + 0x718#64) ↦₆₄ pkBuf) ∗
       ((coroPtr + 0x720#64) ↦₆₄ 0x620#64) ∗
       ((coroPtr + 0x728#64) ↦₆₄ skBuf) ∗
       ((coroPtr + 0x730#64) ↦₆₄ 0xc60#64) ∗
       A.live pkBuf 1568 1 ∗ memRegion pkBuf 1568 ∗
       A.live skBuf 3168 1 ∗ memRegion skBuf 3168 ∗
       A.pool lim st s ∗
       stackAt s.sp allocHookStack ∗
       ((coroPtr + 0x4f1#64) ↦₈ 0#8) ∗
       ((s.sp + 0x88#64) ↦₆₄ w0) ∗
       ((s.sp + 0xa8#64) ↦₆₄ w4) ∗
       ((s.sp + 0xb8#64) ↦₆₄ w2) ∗
       ((s.sp + 0xc8#64) ↦₆₄ outPtr))
      (fun s1 P_f =>
        let st' := M.stepEvents (rustDeallocEvents 1568 1 ++ rustDeallocEvents 3168 1) st
        (P_f ⊢
          ((coroPtr + 0x718#64) ↦₆₄ pkBuf) ∗
          ((coroPtr + 0x720#64) ↦₆₄ 0x620#64) ∗
          ((coroPtr + 0x728#64) ↦₆₄ skBuf) ∗
          ((coroPtr + 0x730#64) ↦₆₄ 0xc60#64) ∗
          A.pool lim st' s1 ∗
          stackAt s.sp allocHookStack ∗
          ((coroPtr + 0x4f1#64) ↦₈ 0#8) ∗
          ((s.sp + 0x88#64) ↦₆₄ w0) ∗
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
  have hx19' : s.readReg64 (Reg.gpr 19#5) = coroPtr := hx19
  have hx22' : s.readReg64 (Reg.gpr 22#5) = w1 >>> 32 := hx22
  have hx23' : s.readReg64 (Reg.gpr 23#5) = (w1.extractLsb' 0 32).zeroExtend 64 := hx23
  have hx27' : s.readReg64 (Reg.gpr 27#5) = w5 := hx27
  have hx28' : s.readReg64 (Reg.gpr 28#5) = s.sp + 0xa90#64 := hx28
  dsimp only [stageP1ProgPlaced, stageP1EntryPlaced, lsRustDeallocSym] at hdealloc hpc ⊢
  wp_steps_sync_pool_518 ext (lsρ "_RNvCs1njKG4L9aB3_7___rustc14___rust_dealloc")
  clear _hvm _hpcm _hrunm
  wp_call hdealloc (pkBuf, 1568, 1, st)
  wp_steps_sync_pool_518 ext (lsρ "_RNvCs1njKG4L9aB3_7___rustc14___rust_dealloc")
  clear _hvm _hpcm _hrunm
  wp_call hdealloc (skBuf, 3168, 1, M.stepEvents (rustDeallocEvents 1568 1) st)
  wp_steps_sync_pool_518 ext (blkPl_518.base + 5704#64)
  rw [hsp_sf]
  refine SepWP.done _hpcm _hrunm ?_
  refine ⟨?_,
    by simp_all [arm64_norm], by simp_all [arm64_norm, AllocCallPreserved],
    by simp_all [arm64_norm], by simp_all [arm64_norm], by simp_all [arm64_norm],
    by simp_all [arm64_norm], by simp_all [arm64_norm], by simp_all [arm64_norm],
    by simp_all [arm64_norm], by simp_all [arm64_norm], by simp_all [arm64_norm],
    by simp_all [arm64_norm], by simp_all [arm64_norm], by simp_all [arm64_norm],
    by simp_all [arm64_norm],
    Nat.le_trans
      (M.liveBytes_free_le 1 3168 (M.step (.free 1 1568) st))
      (M.liveBytes_free_le 1 1568 st)⟩
  rw [← M.stepEvents_append]
  exact Entails.of_eq (by sep_ac_rfl)

abbrev p2_err6b_b_1568_4k_placed_wp := @p2_err6b_b_1568_hooks_placed_wp
abbrev p2_err6b_b_1568_ext_placed_wp := @p2_err6b_b_1568_hooks_placed_wp

/-! ## Shared Epilogue with `prevCap ≠ 0` (`+0x359c -> retAddr`) -/

set_option maxHeartbeats 1200000 in
/-- Segment P3.ErrTailPrevDealloc (`+0x359c -> retAddr` when `prevCap ≠ 0`) on
`stageP1ProgPlaced ext`, threading
`A.pool lim st s -> A.pool lim (M.stepEvents (rustDeallocEvents (prevCap.toNat * 24) 8) st) s1`
across `rustCliDeallocBudgetSpec M A lim`. -/
theorem p3_err_tail_prev_dealloc_hooks_placed_wp [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {st : M.σ}
    (ext : String → Option (State → State))
    (hH : StageP2ClosureHooksPlaced A lim ext)
    (s : State) (coroPtr outPtr errTag prevCap prevPtr
    w_370 w_378 w_380 w_388
    u_ret0 u_ret0c u_ret14 u_ret1c u_ret24
    savedX19 savedX20 savedX21 savedX22 savedX23 savedX24
    savedX25 savedX26 savedX27 savedX28 savedX29 retAddr : BitVec 64)
    (w_22 w_390 u_ret08 u_ret2c : BitVec 32)
    (b_2c0 : BitVec 8)
    (hcap_nz : prevCap ≠ 0#64)
    (hcap_lt : prevCap.toNat * 24 < 2 ^ 63)
    (hpc : s.pc = stageP1EntryPlaced + 0x359c#64)
    (hrun : s.status = .Running)
    (_hsp_align : (s.sp &&& 15#64 == 0#64) = true)
    (hx19 : s.readReg64 .x19 = coroPtr)
    (hx22 : s.readReg64 .x22 = w_22.zeroExtend 64)
    (hx25 : s.readReg64 .x25 = s.sp + 0x210#64)
    (hx26 : s.readReg64 .x26 = outPtr)
    (hx28 : s.readReg64 .x28 = errTag) :
    SepWP (stageP1ProgPlaced ext) retAddr s
      (((coroPtr + 0xe0#64) ↦₆₄ prevCap) ∗
       ((coroPtr + 0xe8#64) ↦₆₄ prevPtr) ∗
       ((coroPtr + 0xf0#64) ↦₆₄ 0#64) ∗
       A.live prevPtr (prevCap.toNat * 24) 8 ∗
       memRegion prevPtr (prevCap.toNat * 24) ∗
       A.pool lim st s ∗
       stackAt s.sp allocHookStack ∗
       ((coroPtr + 0x2c0#64) ↦₈ b_2c0) ∗
       ((outPtr + 0x0#64) ↦₆₄ u_ret0) ∗
       ((outPtr + 0x8#64) ↦₃₂ u_ret08) ∗
       ((outPtr + 0xc#64) ↦₆₄ u_ret0c) ∗
       ((outPtr + 0x14#64) ↦₆₄ u_ret14) ∗
       ((outPtr + 0x1c#64) ↦₆₄ u_ret1c) ∗
       ((outPtr + 0x24#64) ↦₆₄ u_ret24) ∗
       ((outPtr + 0x2c#64) ↦₃₂ u_ret2c) ∗
       ((s.sp + 0x370#64) ↦₆₄ w_370) ∗
       ((s.sp + 0x378#64) ↦₆₄ w_378) ∗
       ((s.sp + 0x380#64) ↦₆₄ w_380) ∗
       ((s.sp + 0x388#64) ↦₆₄ w_388) ∗
       ((s.sp + 0x390#64) ↦₃₂ w_390) ∗
       ((s.sp + 0xc70#64) ↦₆₄ savedX29) ∗
       ((s.sp + 0xc78#64) ↦₆₄ retAddr) ∗
       ((s.sp + 0xc80#64) ↦₆₄ savedX28) ∗
       ((s.sp + 0xc88#64) ↦₆₄ savedX27) ∗
       ((s.sp + 0xc90#64) ↦₆₄ savedX26) ∗
       ((s.sp + 0xc98#64) ↦₆₄ savedX25) ∗
       ((s.sp + 0xca0#64) ↦₆₄ savedX24) ∗
       ((s.sp + 0xca8#64) ↦₆₄ savedX23) ∗
       ((s.sp + 0xcb0#64) ↦₆₄ savedX22) ∗
       ((s.sp + 0xcb8#64) ↦₆₄ savedX21) ∗
       ((s.sp + 0xcc0#64) ↦₆₄ savedX20) ∗
       ((s.sp + 0xcc8#64) ↦₆₄ savedX19))
      (fun s1 P_f =>
        let st' := M.stepEvents (rustDeallocEvents (prevCap.toNat * 24) 8) st
        (P_f ⊢
          ((coroPtr + 0xe0#64) ↦₆₄ prevCap) ∗
          ((coroPtr + 0xe8#64) ↦₆₄ prevPtr) ∗
          ((coroPtr + 0xf0#64) ↦₆₄ 0#64) ∗
          A.pool lim st' s1 ∗
          stackAt s.sp allocHookStack ∗
          ((coroPtr + 0x2c0#64) ↦₈ 1#8) ∗
          ((outPtr + 0x0#64) ↦₆₄ errTag) ∗
          ((outPtr + 0x8#64) ↦₃₂ w_22) ∗
          ((outPtr + 0xc#64) ↦₆₄ w_370) ∗
          ((outPtr + 0x14#64) ↦₆₄ w_378) ∗
          ((outPtr + 0x1c#64) ↦₆₄ w_380) ∗
          ((outPtr + 0x24#64) ↦₆₄ w_388) ∗
          ((outPtr + 0x2c#64) ↦₃₂ w_390) ∗
          ((s.sp + 0x370#64) ↦₆₄ w_370) ∗
          ((s.sp + 0x378#64) ↦₆₄ w_378) ∗
          ((s.sp + 0x380#64) ↦₆₄ w_380) ∗
          ((s.sp + 0x388#64) ↦₆₄ w_388) ∗
          ((s.sp + 0x390#64) ↦₃₂ w_390) ∗
          ((s.sp + 0xc70#64) ↦₆₄ savedX29) ∗
          ((s.sp + 0xc78#64) ↦₆₄ retAddr) ∗
          ((s.sp + 0xc80#64) ↦₆₄ savedX28) ∗
          ((s.sp + 0xc88#64) ↦₆₄ savedX27) ∗
          ((s.sp + 0xc90#64) ↦₆₄ savedX26) ∗
          ((s.sp + 0xc98#64) ↦₆₄ savedX25) ∗
          ((s.sp + 0xca0#64) ↦₆₄ savedX24) ∗
          ((s.sp + 0xca8#64) ↦₆₄ savedX23) ∗
          ((s.sp + 0xcb0#64) ↦₆₄ savedX22) ∗
          ((s.sp + 0xcb8#64) ↦₆₄ savedX21) ∗
          ((s.sp + 0xcc0#64) ↦₆₄ savedX20) ∗
          ((s.sp + 0xcc8#64) ↦₆₄ savedX19)) ∧
        s1.sp = s.sp + 0xcd0#64 ∧
        s1.trace = s.trace ∧
        s1.readReg64 .x19 = savedX19 ∧
        s1.readReg64 .x20 = savedX20 ∧
        s1.readReg64 .x21 = savedX21 ∧
        s1.readReg64 .x22 = savedX22 ∧
        s1.readReg64 .x23 = savedX23 ∧
        s1.readReg64 .x24 = savedX24 ∧
        s1.readReg64 .x25 = savedX25 ∧
        s1.readReg64 .x26 = savedX26 ∧
        s1.readReg64 .x27 = savedX27 ∧
        s1.readReg64 .x28 = savedX28 ∧
        s1.readReg64 .x29 = savedX29 ∧
        s1.readReg64 .x30 = retAddr ∧
        calleeSavedVRegs s1 = calleeSavedVRegs s ∧
        M.liveBytes st' ≤ M.liveBytes st) := by
  have hdealloc := hH.dealloc
  have _hcap_beq : (prevCap == 0#64) = false := beq_eq_false_iff_ne.mpr hcap_nz
  have _hmul1 : 24#64 * prevCap = BitVec.ofNat 64 (prevCap.toNat * 24) := by bv_omega
  have _hmul2 : prevCap * 24#64 = BitVec.ofNat 64 (prevCap.toNat * 24) := by bv_omega
  have hx19' : s.readReg64 (Reg.gpr 19#5) = coroPtr := hx19
  have hx22' : s.readReg64 (Reg.gpr 22#5) = w_22.zeroExtend 64 := hx22
  have hx25' : s.readReg64 (Reg.gpr 25#5) = s.sp + 0x210#64 := hx25
  have hx26' : s.readReg64 (Reg.gpr 26#5) = outPtr := hx26
  have hx28' : s.readReg64 (Reg.gpr 28#5) = errTag := hx28
  dsimp only [stageP1ProgPlaced, stageP1EntryPlaced, lsRustDeallocSym] at hdealloc hpc ⊢
  wp_steps_sync_pool_518 ext (lsρ "_RNvCs1njKG4L9aB3_7___rustc14___rust_dealloc")
  clear _hvm _hpcm _hrunm
  wp_call hdealloc (prevPtr, prevCap.toNat * 24, 8, st)
  wp_steps_sync_pool_518 ext retAddr
  refine SepWP.done _hpcm _hrunm ?_
  refine ⟨Entails.of_eq (by simp only [BitVec.add_zero]; sep_ac_rfl),
    by simp_all [arm64_norm], by simp_all [arm64_norm, AllocCallPreserved],
    by simp_all [arm64_norm], by simp_all [arm64_norm], by simp_all [arm64_norm],
    by simp_all [arm64_norm], by simp_all [arm64_norm], by simp_all [arm64_norm],
    by simp_all [arm64_norm], by simp_all [arm64_norm], by simp_all [arm64_norm],
    by simp_all [arm64_norm], by simp_all [arm64_norm], by simp_all [arm64_norm],
    by simp_all [arm64_norm],
    M.liveBytes_free_le 8 (prevCap.toNat * 24) st⟩

abbrev p3_err_tail_prev_dealloc_4k_placed_wp := @p3_err_tail_prev_dealloc_hooks_placed_wp
abbrev p3_err_tail_prev_dealloc_ext_placed_wp := @p3_err_tail_prev_dealloc_hooks_placed_wp

end LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Kits.StageP2BlocksErrCPlacedBudget
