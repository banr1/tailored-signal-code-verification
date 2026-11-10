/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Kits.StageP2DefsPlacedBudget
public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Kits.StageP2BlocksB6Placed
public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Kits.StageP1StepsXExtPlacedBudgetAux
public import LibsignalBinary.Heap.IfaceBudget
public import LibsignalBinary.Heap.IfaceBudgetLemmas
public import LibsignalBinary.Heap.SpecBudget
public import LibsignalBinary.Proofs.Placed.BudgetVmSteps
public meta import Lean.Elab.Tactic -- shake: keep
import LibsignalBinary.Proofs.Common.SharedHelpers
meta import LibsignalBinary.Proofs.Common.SharedHelpers -- shake: keep
import Arm64.Trusted.Spec.Hoare
import Arm64.Trusted.Spec.SepLogic
import LibsignalBinary.Proofs.E2E.InMem.HashbrownBin.IdentityKeyStoreFutures.SaveIdentity
import LibsignalBinary.Proofs.E2E.InMem.HashbrownBin.SessionStoreFutures.StoreCommon
import LibsignalBinary.Proofs.E2E.Record.Serialization.SessionCloneAux.Base
import LibsignalBinary.Proofs.SpqrV1.Chain.AddEpoch
import LibsignalBinary.Proofs.SpqrV1.Poly.EncoderFromPb.Defs
import LibsignalBinary.Proofs.SpqrV1.Poly.EncoderIntoPb.Defs
import LibsignalBinary.Proofs.SpqrV1.Prost.MessageEncode.Base
import LibsignalBinary.Proofs.SpqrV1.Prost.MessageMerge.PolyCommon
import LibsignalBinary.Proofs.TripleRatchet.GeneralizeEntry
import LibsignalBinary.Proofs.TripleRatchet.ReceiveRatchet.From.Step244

/-!
# Budget-Threaded Relocatable Stage P2 Basic Blocks — Substage P2.6

`RustCliAllocBudget M` / `VmPreserved` basic-block lemmas for Substage P2.6 (`+0x125c → +0x1778`)
on Block `518` (`stageP1ProgPlaced ext`).
-/

@[expose] public section

set_option autoImplicit false

namespace LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Kits.StageP2BlocksB6PlacedBudget

open Arm64 ProofLib ProofLib.ProgramReflection
open LibsignalBinary.Heap (
  AllocCallPreserved AllocCostModel BudgetLimits RustCliAllocBudget VmPreserved
  rustDeallocEvents
)
open LibsignalBinary.Heap.SpecBudget (withVmPreserved)
open LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Kits.StageP1StepsXExtPlacedBudgetAux (
  sepWP_seg_rebase_vm
)
open LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Kits.StageP2DefsBudget (
  p2Memcpy4KSpec
)
open LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Kits.StageP2DefsPlacedBudget (
  StageP2ClosureHooksPlaced
)
open CryptoVerification (
  LibsignalPlacement libsignalSessionLib lsMemcpySym lsRustDeallocSym lsmpl lsρ
)
open CryptoVerification.RustHeap (allocHookStack)
open CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.Kits (
  stageP1EntryPlaced stageP1ProgPlaced
)
open CryptoVerification.CliHandshake.RespClosurePlaced (blkPC_518 blkPl_518)

set_option maxRecDepth 200000

attribute [local irreducible] Program.fetch Program.externAt? Program.fnOff
attribute [local arm64_norm] bv_sub_add_lit BitVec.add_assoc BitVec.toNat_zero
attribute [local wp_norm] p2Memcpy4KSpec withVmPreserved
  CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.Kits.p2Memcpy4KSpec libcMemcpySpec

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
      refine SepWP.done (by simp_all [arm64_norm]) (by simp_all [arm64_norm])
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

local elab "grab_vm " id:ident : tactic => do
  let g ← Lean.Elab.Tactic.getMainGoal
  g.withContext do
    let ty := (← Lean.instantiateMVars (← g.getType)).consumeMData
    let sCur := ty.getArg! 2
    let mut found? : Option (Lean.Expr × Lean.Expr) := none
    for d in (← Lean.getLCtx) do
      if !d.isImplementationDetail then
        let dty := (← Lean.instantiateMVars d.type).consumeMData
        if dty.isAppOfArity ``LibsignalBinary.Heap.VmPreserved 2 && (dty.getArg! 1).eqv sCur then
          found? := some (dty, d.toExpr)
    let some (dty, prf) := found?
      | throwError "grab_vm: no VmPreserved _ {sCur} in context"
    let g' ← g.assert id.getId dty prf
    let (_, g'') ← g'.intro id.getId
    Lean.Elab.Tactic.replaceMainGoal [g'']

/-! ## Substage P2.6 Basic Blocks (`+0x125c -> +0x1778`) -/

set_option maxHeartbeats 1200000 in
theorem p2_seg6a_hooks_placed_wp [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    (ext : String → Option (State → State))
    (hH : StageP2ClosureHooksPlaced A lim ext)
    (s : State) (coroPtr idStorePtr idStoreVt getLocalRegIdShimAddr
    ss0 ss1 ss2 ss3 ss4 ss5 ss6
    u_4f8 u_500 u_508 u_510 u_518 u_520 u_528 u_650 : BitVec 64)
    (ssRest : List (BitVec 8))
    (hss0_ne : ss0 + 1#64 ≠ 0#64)
    (hssRest_len : ssRest.length = 288)
    (hpc : s.pc = stageP1EntryPlaced + 0x125c#64)
    (hrun : s.status = .Running)
    (hsp_align : (s.sp &&& 15#64 == 0#64) = true)
    (hx19 : s.readReg64 .x19 = coroPtr) :
    SepWP (stageP1ProgPlaced ext) getLocalRegIdShimAddr s
      (((s.sp + 0x3e0#64) ↦₆₄ ss0) ∗ ((s.sp + 0x3e8#64) ↦₆₄ ss1) ∗
       ((s.sp + 0x3f0#64) ↦₆₄ ss2) ∗ ((s.sp + 0x3f8#64) ↦₆₄ ss3) ∗
       ((s.sp + 0x400#64) ↦₆₄ ss4) ∗ ((s.sp + 0x408#64) ↦₆₄ ss5) ∗
       ((s.sp + 0x410#64) ↦₆₄ ss6) ∗ ((s.sp + 0x418#64) ↦ₛ ssRest) ∗
       memRegion (s.sp + 0xa90#64) 288 ∗
       ((coroPtr + 0x4f8#64) ↦₆₄ u_4f8) ∗ ((coroPtr + 0x500#64) ↦₆₄ u_500) ∗
       ((coroPtr + 0x508#64) ↦₆₄ u_508) ∗ ((coroPtr + 0x510#64) ↦₆₄ u_510) ∗
       ((coroPtr + 0x518#64) ↦₆₄ u_518) ∗ ((coroPtr + 0x520#64) ↦₆₄ u_520) ∗
       ((coroPtr + 0x528#64) ↦₆₄ u_528) ∗ memRegion (coroPtr + 0x530#64) 288 ∗
       ((coroPtr + 0x650#64) ↦₆₄ u_650) ∗ ((coroPtr + 0x418#64) ↦₆₄ idStorePtr) ∗
       ((coroPtr + 0x420#64) ↦₆₄ idStoreVt) ∗
       ((idStoreVt + 0x20#64) ↦₆₄ᵣ getLocalRegIdShimAddr) ∗
       stackAt s.sp allocHookStack)
      (fun s1 P_f =>
        (P_f ⊢
          ((s.sp + 0x3e0#64) ↦₆₄ ss0) ∗ ((s.sp + 0x3e8#64) ↦₆₄ ss1) ∗
          ((s.sp + 0x3f0#64) ↦₆₄ ss2) ∗ ((s.sp + 0x3f8#64) ↦₆₄ ss3) ∗
          ((s.sp + 0x400#64) ↦₆₄ ss4) ∗ ((s.sp + 0x408#64) ↦₆₄ ss5) ∗
          ((s.sp + 0x410#64) ↦₆₄ ss6) ∗ ((s.sp + 0x418#64) ↦ₛ ssRest) ∗
          ((s.sp + 0xa90#64) ↦ₛ ssRest) ∗
          ((coroPtr + 0x4f8#64) ↦₆₄ ss0) ∗ ((coroPtr + 0x500#64) ↦₆₄ ss1) ∗
          ((coroPtr + 0x508#64) ↦₆₄ ss2) ∗ ((coroPtr + 0x510#64) ↦₆₄ ss3) ∗
          ((coroPtr + 0x518#64) ↦₆₄ ss4) ∗ ((coroPtr + 0x520#64) ↦₆₄ ss5) ∗
          ((coroPtr + 0x528#64) ↦₆₄ ss6) ∗ ((coroPtr + 0x530#64) ↦ₛ ssRest) ∗
          ((coroPtr + 0x650#64) ↦₆₄ (coroPtr + 0x4f8#64)) ∗
          ((coroPtr + 0x418#64) ↦₆₄ idStorePtr) ∗ ((coroPtr + 0x420#64) ↦₆₄ idStoreVt) ∗
          ((idStoreVt + 0x20#64) ↦₆₄ᵣ getLocalRegIdShimAddr) ∗
          stackAt s.sp allocHookStack) ∧
        s1.sp = s.sp ∧ s1.trace = s.trace ∧ s1.readReg64 .x0 = idStorePtr ∧
        s1.readReg64 .x19 = coroPtr ∧ s1.readReg64 .x20 = ss1 ∧
        s1.readReg64 .x21 = ss0 ∧ s1.readReg64 .x22 = ss4 ∧
        s1.readReg64 .x23 = ss2 ∧ s1.readReg64 .x24 = ss3 ∧
        s1.readReg64 .x25 = s.readReg64 .x25 ∧ s1.readReg64 .x26 = ss5 ∧
        s1.readReg64 .x27 = ss6 ∧ s1.readReg64 .x28 = s.readReg64 .x28 ∧
        s1.readReg64 .x29 = s.readReg64 .x29 ∧
        s1.readReg64 .x30 = stageP1EntryPlaced + 0x12d8#64 ∧
        calleeSavedVRegs s1 = calleeSavedVRegs s ∧
        VmPreserved s s1) := by
  have hmemcpy := hH.memcpy4K
  have hss0_beq : (ss0 + 1#64 == 0#64) = false := beq_eq_false_iff_ne.mpr hss0_ne
  dsimp only [stageP1ProgPlaced, stageP1EntryPlaced, lsMemcpySym] at hmemcpy hpc ⊢
  have hx19' : s.readReg64 (Reg.gpr 19#5) = coroPtr := hx19
  wp_steps_sync_pool_518 ext (lsρ "memcpy")
  have hvm1 := _hvm; clear _hvm _hpcm _hrunm
  wp_call hmemcpy (s.sp + 0xa90#64, s.sp + 0x418#64, ssRest)
  grab_vm hvm2
  wp_steps_sync_pool_518 ext (lsρ "memcpy")
  have hvm3 := _hvm; clear _hvm _hpcm _hrunm
  wp_call hmemcpy (coroPtr + 0x530#64, s.sp + 0xa90#64, ssRest)
  grab_vm hvm4
  wp_steps_sync_pool_518 ext getLocalRegIdShimAddr
  have hvm5 := _hvm
  rw [hsp_sf]
  refine SepWP.done _hpcm _hrunm ?_
  refine ⟨Entails.of_eq (by sep_ac_rfl), by simp_all [arm64_norm], by simp_all [arm64_norm],
    by simp_all [arm64_norm], by simp_all [arm64_norm], by simp_all [arm64_norm],
    by simp_all [arm64_norm], by simp_all [arm64_norm], by simp_all [arm64_norm],
    by simp_all [arm64_norm], by simp_all [arm64_norm], by simp_all [arm64_norm],
    by simp_all [arm64_norm], by simp_all [arm64_norm], by simp_all [arm64_norm],
    by simp_all [arm64_norm], by simp_all [arm64_norm],
    hvm1.trans (hvm2.trans (hvm3.trans (hvm4.trans hvm5)))⟩

abbrev p2_seg6a_4k_placed_wp := @p2_seg6a_hooks_placed_wp
abbrev p2_seg6a_ext_placed_wp := @p2_seg6a_hooks_placed_wp

set_option maxHeartbeats 1000000 in
theorem p2_seg6b_ext_placed_wp [LibsignalPlacement]
    (ext : String → Option (State → State))
    (s : State) (coroPtr ctxPtr regIdFutPtr regIdFutVt localRegIdPollAddr
    v_98 v_a0 v_b0 u_788 u_790 : BitVec 64)
    (hpc : s.pc = stageP1EntryPlaced + 0x12d8#64)
    (hrun : s.status = .Running)
    (_hsp_align : (s.sp &&& 15#64 == 0#64) = true)
    (hx0 : s.readReg64 .x0 = regIdFutPtr)
    (hx1 : s.readReg64 .x1 = regIdFutVt)
    (hx19 : s.readReg64 .x19 = coroPtr) :
    SepWP (stageP1ProgPlaced ext) localRegIdPollAddr s
      (((s.sp + 0x98#64) ↦₆₄ v_98) ∗ ((s.sp + 0xa0#64) ↦₆₄ v_a0) ∗
       ((s.sp + 0xb0#64) ↦₆₄ v_b0) ∗ ((s.sp + 0xc0#64) ↦₆₄ ctxPtr) ∗
       ((coroPtr + 0x788#64) ↦₆₄ u_788) ∗ ((coroPtr + 0x790#64) ↦₆₄ u_790) ∗
       ((regIdFutVt + 0x18#64) ↦₆₄ᵣ localRegIdPollAddr))
      (fun s1 P_f =>
        (P_f ⊢
          ((s.sp + 0x98#64) ↦₆₄ v_98) ∗ ((s.sp + 0xa0#64) ↦₆₄ v_a0) ∗
          ((s.sp + 0xb0#64) ↦₆₄ v_b0) ∗ ((s.sp + 0xc0#64) ↦₆₄ ctxPtr) ∗
          ((coroPtr + 0x788#64) ↦₆₄ regIdFutPtr) ∗ ((coroPtr + 0x790#64) ↦₆₄ regIdFutVt) ∗
          ((regIdFutVt + 0x18#64) ↦₆₄ᵣ localRegIdPollAddr)) ∧
        s1.sp = s.sp ∧ s1.trace = s.trace ∧ s1.readReg64 .x0 = regIdFutPtr ∧
        s1.readReg64 .x1 = ctxPtr ∧ s1.readReg64 .x8 = s.sp + 0x3e0#64 ∧
        s1.readReg64 .x19 = coroPtr ∧ s1.readReg64 .x21 = v_b0 ∧
        s1.readReg64 .x23 = v_a0 ∧ s1.readReg64 .x25 = s.readReg64 .x25 ∧
        s1.readReg64 .x26 = v_98 ∧ s1.readReg64 .x27 = ctxPtr ∧
        s1.readReg64 .x28 = s.readReg64 .x28 ∧ s1.readReg64 .x29 = s.readReg64 .x29 ∧
        s1.readReg64 .x30 = stageP1EntryPlaced + 0x9f4#64 ∧
        calleeSavedVRegs s1 = calleeSavedVRegs s ∧
        VmPreserved s s1) := by
  dsimp only [stageP1ProgPlaced, stageP1EntryPlaced] at hpc ⊢
  have hx0' : s.readReg64 (Reg.gpr 0#5) = regIdFutPtr := hx0
  have hx1' : s.readReg64 (Reg.gpr 1#5) = regIdFutVt := hx1
  have hx19' : s.readReg64 (Reg.gpr 19#5) = coroPtr := hx19
  wp_steps_sync_pool_518 ext localRegIdPollAddr
  refine SepWP.done _hpcm _hrunm ?_
  exact ⟨Entails.of_eq (by sep_ac_rfl), rfl, rfl,
    by simp_all [arm64_norm], by simp_all [arm64_norm], by simp_all [arm64_norm],
    by simp_all [arm64_norm], by simp_all [arm64_norm], by simp_all [arm64_norm],
    by simp_all [arm64_norm], by simp_all [arm64_norm], by simp_all [arm64_norm],
    by simp_all [arm64_norm], by simp_all [arm64_norm], by simp_all [arm64_norm],
    by simp_all [arm64_norm], _hvm⟩

set_option maxHeartbeats 1000000 in
theorem p2_seg6c_ext_placed_wp [LibsignalPlacement]
    (ext : String → Option (State → State))
    (s : State) (coroPtr regIdFutPtr regIdFutVt localRegIdDropAddr
    v_98 v_a0 v_b0 u_88 u_98 u_a0 u_a8 u_b0 u_b8 u_d0
    u_3f0 u_3f8 u_400 u_408 : BitVec 64)
    (localRegId u_3ec : BitVec 32)
    (hdrop_nz : localRegIdDropAddr ≠ 0#64)
    (hpc : s.pc = stageP1EntryPlaced + 0x9f4#64)
    (hrun : s.status = .Running)
    (_hsp_align : (s.sp &&& 15#64 == 0#64) = true)
    (hx19 : s.readReg64 .x19 = coroPtr)
    (hx21 : s.readReg64 .x21 = v_b0)
    (hx23 : s.readReg64 .x23 = v_a0)
    (hx26 : s.readReg64 .x26 = v_98) :
    SepWP (stageP1ProgPlaced ext) localRegIdDropAddr s
      (((s.sp + 0x3e0#64) ↦₆₄ 0xfffffffffffffffe#64) ∗
       ((s.sp + 0x3e8#64) ↦₃₂ localRegId) ∗ ((s.sp + 0x3ec#64) ↦₃₂ u_3ec) ∗
       ((s.sp + 0x3f0#64) ↦₆₄ u_3f0) ∗ ((s.sp + 0x3f8#64) ↦₆₄ u_3f8) ∗
       ((s.sp + 0x400#64) ↦₆₄ u_400) ∗ ((s.sp + 0x408#64) ↦₆₄ u_408) ∗
       ((coroPtr + 0x788#64) ↦₆₄ regIdFutPtr) ∗ ((coroPtr + 0x790#64) ↦₆₄ regIdFutVt) ∗
       ((regIdFutVt + 0x0#64) ↦₆₄ᵣ localRegIdDropAddr) ∗
       ((s.sp + 0x88#64) ↦₆₄ u_88) ∗ ((s.sp + 0x98#64) ↦₆₄ u_98) ∗
       ((s.sp + 0xa0#64) ↦₆₄ u_a0) ∗ ((s.sp + 0xa8#64) ↦₆₄ u_a8) ∗
       ((s.sp + 0xb0#64) ↦₆₄ u_b0) ∗ ((s.sp + 0xb8#64) ↦₆₄ u_b8) ∗
       ((s.sp + 0xd0#64) ↦₆₄ u_d0))
      (fun s1 P_f =>
        (P_f ⊢
          ((s.sp + 0x3e0#64) ↦₆₄ 0xfffffffffffffffe#64) ∗
          ((s.sp + 0x3e8#64) ↦₃₂ localRegId) ∗ ((s.sp + 0x3ec#64) ↦₃₂ u_3ec) ∗
          ((s.sp + 0x3f0#64) ↦₆₄ u_3f0) ∗ ((s.sp + 0x3f8#64) ↦₆₄ u_3f8) ∗
          ((s.sp + 0x400#64) ↦₆₄ u_400) ∗ ((s.sp + 0x408#64) ↦₆₄ u_408) ∗
          ((coroPtr + 0x788#64) ↦₆₄ regIdFutPtr) ∗ ((coroPtr + 0x790#64) ↦₆₄ regIdFutVt) ∗
          ((regIdFutVt + 0x0#64) ↦₆₄ᵣ localRegIdDropAddr) ∗
          ((s.sp + 0x88#64) ↦₆₄ 0xfffffffffffffffe#64) ∗ ((s.sp + 0x98#64) ↦₆₄ v_98) ∗
          ((s.sp + 0xa0#64) ↦₆₄ v_a0) ∗ ((s.sp + 0xa8#64) ↦₆₄ u_400) ∗
          ((s.sp + 0xb0#64) ↦₆₄ v_b0) ∗ ((s.sp + 0xb8#64) ↦₆₄ u_3f0) ∗
          ((s.sp + 0xd0#64) ↦₆₄ u_3f8)) ∧
        s1.sp = s.sp ∧ s1.trace = s.trace ∧ s1.readReg64 .x0 = regIdFutPtr ∧
        s1.readReg64 .x19 = coroPtr ∧ s1.readReg64 .x21 = regIdFutPtr ∧
        s1.readReg64 .x22 = u_3ec.zeroExtend 64 ∧
        s1.readReg64 .x23 = localRegId.zeroExtend 64 ∧
        s1.readReg64 .x24 = regIdFutVt ∧ s1.readReg64 .x25 = s.readReg64 .x25 ∧
        s1.readReg64 .x26 = v_98 ∧ s1.readReg64 .x27 = u_408 ∧
        s1.readReg64 .x28 = s.readReg64 .x28 ∧ s1.readReg64 .x29 = s.readReg64 .x29 ∧
        s1.readReg64 .x30 = stageP1EntryPlaced + 0xb3c#64 ∧
        calleeSavedVRegs s1 = calleeSavedVRegs s ∧
        VmPreserved s s1) := by
  have hdrop_beq : (localRegIdDropAddr == 0#64) = false := beq_eq_false_iff_ne.mpr hdrop_nz
  dsimp only [stageP1ProgPlaced, stageP1EntryPlaced] at hpc ⊢
  have hx19' : s.readReg64 (Reg.gpr 19#5) = coroPtr := hx19
  have hx21' : s.readReg64 (Reg.gpr 21#5) = v_b0 := hx21
  have hx23' : s.readReg64 (Reg.gpr 23#5) = v_a0 := hx23
  have hx26' : s.readReg64 (Reg.gpr 26#5) = v_98 := hx26
  wp_steps_sync_pool_518 ext localRegIdDropAddr
  refine SepWP.done _hpcm _hrunm ?_
  exact ⟨Entails.of_eq (by sep_ac_rfl), rfl, rfl,
    by simp_all [arm64_norm], by simp_all [arm64_norm], by simp_all [arm64_norm],
    by simp_all [arm64_norm], by simp_all [arm64_norm], by simp_all [arm64_norm],
    by simp_all [arm64_norm], by simp_all [arm64_norm], by simp_all [arm64_norm],
    by simp_all [arm64_norm], by simp_all [arm64_norm], by simp_all [arm64_norm],
    by simp_all [arm64_norm], _hvm⟩

set_option maxHeartbeats 1200000 in
theorem p2_seg6d1_gen_hooks_placed_wp [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {st : M.σ}
    (ext : String → Option (State → State))
    (hH : StageP2ClosureHooksPlaced A lim ext)
    (s : State) (coroPtr msgPtr regIdFutPtr regIdFutVt : BitVec 64)
    (localRegId remoteRegId u_648 u_64c : BitVec 32)
    (regIdBoxSize : Nat)
    (hpc : s.pc = stageP1EntryPlaced + 0xb3c#64)
    (hrun : s.status = .Running)
    (hsp_align : (s.sp &&& 15#64 == 0#64) = true)
    (hbs_nz : BitVec.ofNat 64 regIdBoxSize ≠ 0#64)
    (hbs_lt : regIdBoxSize < 2 ^ 64)
    (hx19 : s.readReg64 .x19 = coroPtr)
    (hx21 : s.readReg64 .x21 = regIdFutPtr)
    (hx23 : s.readReg64 .x23 = localRegId.zeroExtend 64)
    (hx24 : s.readReg64 .x24 = regIdFutVt) :
    SepWP (stageP1ProgPlaced ext) (stageP1EntryPlaced + 0xb80#64) s
      (((regIdFutVt + 0x8#64) ↦₆₄ᵣ BitVec.ofNat 64 regIdBoxSize) ∗
       ((regIdFutVt + 0x10#64) ↦₆₄ᵣ 8#64) ∗
       A.live regIdFutPtr regIdBoxSize 8 ∗ memRegion regIdFutPtr regIdBoxSize ∗
       A.pool lim st s ∗ stackAt s.sp allocHookStack ∗
       ((s.sp + 0x88#64) ↦₆₄ 0xfffffffffffffffe#64) ∗
       ((coroPtr + 0x468#64) ↦₆₄ msgPtr) ∗
       ((coroPtr + 0x480#64) ↦₆₄ (coroPtr + 0xe0#64)) ∗
       ((coroPtr + 0x648#64) ↦₃₂ u_648) ∗ ((coroPtr + 0x64c#64) ↦₃₂ u_64c) ∗
       ((coroPtr + 0x650#64) ↦₆₄ (coroPtr + 0x4f8#64)) ∗
       ((msgPtr + 0xe8#64) ↦₃₂ remoteRegId))
      (fun s1 P_f =>
        let st' := M.stepEvents (rustDeallocEvents regIdBoxSize 8) st
        (P_f ⊢
          ((regIdFutVt + 0x8#64) ↦₆₄ᵣ BitVec.ofNat 64 regIdBoxSize) ∗
          ((regIdFutVt + 0x10#64) ↦₆₄ᵣ 8#64) ∗
          A.pool lim st' s1 ∗ stackAt s.sp allocHookStack ∗
          ((s.sp + 0x88#64) ↦₆₄ 0xfffffffffffffffe#64) ∗
          ((coroPtr + 0x468#64) ↦₆₄ msgPtr) ∗
          ((coroPtr + 0x480#64) ↦₆₄ (coroPtr + 0xe0#64)) ∗
          ((coroPtr + 0x648#64) ↦₃₂ remoteRegId) ∗ ((coroPtr + 0x64c#64) ↦₃₂ localRegId) ∗
          ((coroPtr + 0x650#64) ↦₆₄ (coroPtr + 0x4f8#64)) ∗
          ((msgPtr + 0xe8#64) ↦₃₂ remoteRegId)) ∧
        s1.sp = s.sp ∧ s1.trace = s.trace ∧ s1.readReg64 .x0 = s.sp + 0x3e0#64 ∧
        s1.readReg64 .x1 = coroPtr + 0x4f8#64 ∧ s1.readReg64 .x2 = 344#64 ∧
        s1.readReg64 .x19 = coroPtr ∧ s1.readReg64 .x21 = coroPtr + 0xe0#64 ∧
        s1.readReg64 .x22 = s.readReg64 .x22 ∧
        s1.readReg64 .x23 = localRegId.zeroExtend 64 ∧
        s1.readReg64 .x24 = regIdFutVt ∧ s1.readReg64 .x25 = s.readReg64 .x25 ∧
        s1.readReg64 .x26 = s.readReg64 .x26 ∧ s1.readReg64 .x27 = s.readReg64 .x27 ∧
        s1.readReg64 .x28 = s.readReg64 .x28 ∧ s1.readReg64 .x29 = s.readReg64 .x29 ∧
        calleeSavedVRegs s1 = calleeSavedVRegs s ∧
        M.liveBytes st' ≤ M.liveBytes st) := by
  have hdealloc := hH.dealloc
  have hbs_beq : (BitVec.ofNat 64 regIdBoxSize == 0#64) = false := beq_eq_false_iff_ne.mpr hbs_nz
  have hbs_toNat : (BitVec.ofNat 64 regIdBoxSize).toNat = regIdBoxSize := Nat.mod_eq_of_lt hbs_lt
  dsimp only [stageP1ProgPlaced, stageP1EntryPlaced, lsRustDeallocSym] at hdealloc hpc ⊢
  have hx19' : s.readReg64 (Reg.gpr 19#5) = coroPtr := hx19
  have hx21' : s.readReg64 (Reg.gpr 21#5) = regIdFutPtr := hx21
  have hx23' : s.readReg64 (Reg.gpr 23#5) = localRegId.zeroExtend 64 := hx23
  have hx24' : s.readReg64 (Reg.gpr 24#5) = regIdFutVt := hx24
  wp_steps_sync_pool_518 ext (lsρ "_RNvCs1njKG4L9aB3_7___rustc14___rust_dealloc")
  clear _hvm _hpcm _hrunm
  wp_call hdealloc (regIdFutPtr, regIdBoxSize, 8, st)
  wp_steps_sync_pool_518 ext (blkPl_518.base + 2944#64)
  refine SepWP.done _hpcm _hrunm ?_
  refine ⟨Entails.of_eq (by sep_ac_rfl), by simp_all [arm64_norm],
    by simp_all [arm64_norm, AllocCallPreserved],
    by simp_all [arm64_norm], by simp_all [arm64_norm], by simp_all [arm64_norm],
    by simp_all [arm64_norm], by simp_all [arm64_norm], by simp_all [arm64_norm],
    by simp_all [arm64_norm], by simp_all [arm64_norm], by simp_all [arm64_norm],
    by simp_all [arm64_norm], by simp_all [arm64_norm], by simp_all [arm64_norm],
    by simp_all [arm64_norm], by simp_all [arm64_norm],
    M.liveBytes_free_le 8 regIdBoxSize st⟩

abbrev p2_seg6d1_gen_4k_placed_wp := @p2_seg6d1_gen_hooks_placed_wp
abbrev p2_seg6d1_gen_placed_wp := @p2_seg6d1_gen_hooks_placed_wp

set_option maxHeartbeats 1200000 in
theorem p2_seg6d2_hooks_placed_wp [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    (ext : String → Option (State → State))
    (hH : StageP2ClosureHooksPlaced A lim ext)
    (s : State) (coroPtr : BitVec 64) (ssBytes : List (BitVec 8))
    (hss_len : ssBytes.length = 344)
    (hpc : s.pc = stageP1EntryPlaced + 0xb80#64)
    (hrun : s.status = .Running)
    (hsp_align : (s.sp &&& 15#64 == 0#64) = true)
    (hx0 : s.readReg64 .x0 = s.sp + 0x3e0#64)
    (hx1 : s.readReg64 .x1 = coroPtr + 0x4f8#64)
    (hx2 : s.readReg64 .x2 = 344#64)
    (hx19 : s.readReg64 .x19 = coroPtr)
    (hx21 : s.readReg64 .x21 = coroPtr + 0xe0#64) :
    SepWP (stageP1ProgPlaced ext)
      (libsignalSessionLib.resolve lsmpl "<libsignal_protocol::state::session::SessionRecord>::promote_state") s
      (((coroPtr + 0x4f8#64) ↦ₛ ssBytes) ∗
       memRegion (s.sp + 0x3e0#64) 344 ∗
       stackAt s.sp allocHookStack)
      (fun s1 P_f =>
        (P_f ⊢
          ((coroPtr + 0x4f8#64) ↦ₛ ssBytes) ∗
          ((s.sp + 0x3e0#64) ↦ₛ ssBytes) ∗
          stackAt s.sp allocHookStack) ∧
        s1.sp = s.sp ∧ s1.trace = s.trace ∧ s1.readReg64 .x0 = coroPtr + 0xe0#64 ∧
        s1.readReg64 .x1 = s.sp + 0x3e0#64 ∧ s1.readReg64 .x19 = coroPtr ∧
        s1.readReg64 .x21 = coroPtr + 0xe0#64 ∧ s1.readReg64 .x22 = s.readReg64 .x22 ∧
        s1.readReg64 .x23 = s.readReg64 .x23 ∧ s1.readReg64 .x24 = s.readReg64 .x24 ∧
        s1.readReg64 .x25 = s.readReg64 .x25 ∧ s1.readReg64 .x26 = s.readReg64 .x26 ∧
        s1.readReg64 .x27 = s.readReg64 .x27 ∧ s1.readReg64 .x28 = s.readReg64 .x28 ∧
        s1.readReg64 .x29 = s.readReg64 .x29 ∧
        s1.readReg64 .x30 = stageP1EntryPlaced + 0xb90#64 ∧
        calleeSavedVRegs s1 = calleeSavedVRegs s ∧
        VmPreserved s s1) := by
  have hmemcpy := hH.memcpy4K
  dsimp only [stageP1ProgPlaced, stageP1EntryPlaced, lsMemcpySym] at hmemcpy hpc ⊢
  have hx0' : s.readReg64 (Reg.gpr 0#5) = s.sp + 0x3e0#64 := hx0
  have hx1' : s.readReg64 (Reg.gpr 1#5) = coroPtr + 0x4f8#64 := hx1
  have hx2' : s.readReg64 (Reg.gpr 2#5) = 344#64 := hx2
  have hx19' : s.readReg64 (Reg.gpr 19#5) = coroPtr := hx19
  have hx21' : s.readReg64 (Reg.gpr 21#5) = coroPtr + 0xe0#64 := hx21
  wp_steps_sync_pool_518 ext (lsρ "memcpy")
  have hvm1 := _hvm; clear _hvm _hpcm _hrunm
  wp_call hmemcpy (s.sp + 0x3e0#64, coroPtr + 0x4f8#64, ssBytes)
  grab_vm hvm2
  wp_steps_sync_pool_518 ext
    (libsignalSessionLib.resolve lsmpl "<libsignal_protocol::state::session::SessionRecord>::promote_state")
  have hvm3 := _hvm
  refine SepWP.done _hpcm _hrunm ?_
  refine ⟨Entails.of_eq (by sep_ac_rfl), by simp_all [arm64_norm], by simp_all [arm64_norm],
    by simp_all [arm64_norm], by simp_all [arm64_norm], by simp_all [arm64_norm],
    by simp_all [arm64_norm], by simp_all [arm64_norm], by simp_all [arm64_norm],
    by simp_all [arm64_norm], by simp_all [arm64_norm], by simp_all [arm64_norm],
    by simp_all [arm64_norm], by simp_all [arm64_norm], by simp_all [arm64_norm],
    by simp_all [arm64_norm], by simp_all [arm64_norm],
    hvm1.trans (hvm2.trans hvm3)⟩

abbrev p2_seg6d2_4k_placed_wp := @p2_seg6d2_hooks_placed_wp
abbrev p2_seg6d2_ext_placed_wp := @p2_seg6d2_hooks_placed_wp

set_option maxHeartbeats 1200000 in
theorem p2_seg6e_1568_hooks_placed_wp [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {st : M.σ}
    (ext : String → Option (State → State))
    (hH : StageP2ClosureHooksPlaced A lim ext)
    (s : State) (coroPtr msgPtr kyberCtCap kyberKpPubPtr kyberKpSecPtr
    v_c8 u_a8 u_d0 : BitVec 64)
    (opkIdIsSome opkId kyberPreKeyId signedPreKeyId : BitVec 32)
    (b_4f1 b_4f2 : BitVec 8)
    (hkyber_nz : kyberCtCap ≠ 0#64)
    (hpc : s.pc = stageP1EntryPlaced + 0xb90#64)
    (hrun : s.status = .Running)
    (hsp_align : (s.sp &&& 15#64 == 0#64) = true)
    (hx19 : s.readReg64 .x19 = coroPtr) :
    SepWP (stageP1ProgPlaced ext)
      (libsignalSessionLib.resolve lsmpl
        "core::ptr::drop_glue::<libsignal_protocol::session::process_prekey_impl::{closure#0}>") s
      (((coroPtr + 0x468#64) ↦₆₄ msgPtr) ∗
       ((coroPtr + 0x718#64) ↦₆₄ kyberKpPubPtr) ∗
       ((coroPtr + 0x720#64) ↦₆₄ 0x620#64) ∗
       ((coroPtr + 0x728#64) ↦₆₄ kyberKpSecPtr) ∗
       ((coroPtr + 0x730#64) ↦₆₄ 0xc60#64) ∗
       ((coroPtr + 0x4f1#64) ↦₈ b_4f1) ∗ ((coroPtr + 0x4f2#64) ↦₈ b_4f2) ∗
       ((msgPtr + 0x78#64) ↦₃₂ opkIdIsSome) ∗ ((msgPtr + 0x7c#64) ↦₃₂ opkId) ∗
       ((msgPtr + 0x90#64) ↦₆₄ kyberCtCap) ∗ ((msgPtr + 0xa0#64) ↦₃₂ kyberPreKeyId) ∗
       ((msgPtr + 0xec#64) ↦₃₂ signedPreKeyId) ∗
       ((s.sp + 0x98#64) ↦₆₄ (coroPtr + 0x398#64)) ∗
       ((s.sp + 0xa0#64) ↦₆₄ (coroPtr + 0x4f2#64)) ∗
       ((s.sp + 0xa8#64) ↦₆₄ u_a8) ∗ ((s.sp + 0xc8#64) ↦₆₄ v_c8) ∗
       ((s.sp + 0xd0#64) ↦₆₄ u_d0) ∗
       A.live kyberKpPubPtr 1568 1 ∗ memRegion kyberKpPubPtr 1568 ∗
       A.live kyberKpSecPtr 3168 1 ∗ memRegion kyberKpSecPtr 3168 ∗
       A.pool lim st s ∗ stackAt s.sp allocHookStack)
      (fun s1 P_f =>
        let st' := M.stepEvents (rustDeallocEvents 1568 1 ++ rustDeallocEvents 3168 1) st
        (P_f ⊢
          ((coroPtr + 0x468#64) ↦₆₄ msgPtr) ∗
          ((coroPtr + 0x718#64) ↦₆₄ kyberKpPubPtr) ∗
          ((coroPtr + 0x720#64) ↦₆₄ 0x620#64) ∗
          ((coroPtr + 0x728#64) ↦₆₄ kyberKpSecPtr) ∗
          ((coroPtr + 0x730#64) ↦₆₄ 0xc60#64) ∗
          ((coroPtr + 0x4f1#64) ↦₈ 0#8) ∗ ((coroPtr + 0x4f2#64) ↦₈ 1#8) ∗
          ((msgPtr + 0x78#64) ↦₃₂ opkIdIsSome) ∗ ((msgPtr + 0x7c#64) ↦₃₂ opkId) ∗
          ((msgPtr + 0x90#64) ↦₆₄ kyberCtCap) ∗ ((msgPtr + 0xa0#64) ↦₃₂ kyberPreKeyId) ∗
          ((msgPtr + 0xec#64) ↦₃₂ signedPreKeyId) ∗
          ((s.sp + 0x98#64) ↦₆₄ (coroPtr + 0x398#64)) ∗
          ((s.sp + 0xa0#64) ↦₆₄ (coroPtr + 0x4f2#64)) ∗
          ((s.sp + 0xa8#64) ↦₆₄ 0#64) ∗ ((s.sp + 0xc8#64) ↦₆₄ v_c8) ∗
          ((s.sp + 0xd0#64) ↦₆₄ signedPreKeyId.zeroExtend 64) ∗
          A.pool lim st' s1 ∗ stackAt s.sp allocHookStack) ∧
        s1.sp = s.sp ∧ s1.trace = s.trace ∧ s1.readReg64 .x0 = coroPtr + 0x398#64 ∧
        s1.readReg64 .x19 = coroPtr ∧ s1.readReg64 .x20 = 0xfffffffffffffffe#64 ∧
        s1.readReg64 .x21 = 0#64 ∧
        s1.readReg64 .x22 = (kyberPreKeyId.zeroExtend 64 <<< 32) ||| 1#64 ∧
        s1.readReg64 .x23 = opkIdIsSome.zeroExtend 64 ∧
        s1.readReg64 .x24 = opkIdIsSome.zeroExtend 64 ||| (opkId.zeroExtend 64 <<< 32) ∧
        s1.readReg64 .x25 = s.readReg64 .x25 ∧ s1.readReg64 .x26 = v_c8 ∧
        s1.readReg64 .x27 = s.readReg64 .x27 ∧ s1.readReg64 .x28 = s.readReg64 .x28 ∧
        s1.readReg64 .x29 = s.readReg64 .x29 ∧
        s1.readReg64 .x30 = stageP1EntryPlaced + 0x1698#64 ∧
        calleeSavedVRegs s1 = calleeSavedVRegs s ∧
        M.liveBytes st' ≤ M.liveBytes st) := by
  have hdealloc := hH.dealloc
  have hkyber_beq : (kyberCtCap - 0#64 == 0#64) = false := by
    rw [BitVec.sub_zero]; exact beq_eq_false_iff_ne.mpr hkyber_nz
  dsimp only [stageP1ProgPlaced, stageP1EntryPlaced, lsRustDeallocSym] at hdealloc hpc ⊢
  have hx19' : s.readReg64 (Reg.gpr 19#5) = coroPtr := hx19
  wp_steps_sync_pool_518 ext (lsρ "_RNvCs1njKG4L9aB3_7___rustc14___rust_dealloc")
  clear _hvm _hpcm _hrunm
  wp_call hdealloc (kyberKpPubPtr, 1568, 1, st)
  wp_steps_sync_pool_518 ext (lsρ "_RNvCs1njKG4L9aB3_7___rustc14___rust_dealloc")
  clear _hvm _hpcm _hrunm
  wp_call hdealloc (kyberKpSecPtr, 3168, 1, M.stepEvents (rustDeallocEvents 1568 1) st)
  wp_steps_sync_pool_518 ext
    (libsignalSessionLib.resolve lsmpl
      "core::ptr::drop_glue::<libsignal_protocol::session::process_prekey_impl::{closure#0}>")
  rw [hsp_sf]
  refine SepWP.done _hpcm _hrunm ?_
  refine ⟨?_, by simp_all [arm64_norm], by simp_all [arm64_norm, AllocCallPreserved],
    by simp_all [arm64_norm], by simp_all [arm64_norm], by simp_all [arm64_norm],
    by simp_all [arm64_norm],
    by simp_all [arm64_norm]; clear * -; bv_slice,
    by simp_all [arm64_norm],
    by simp_all [arm64_norm],
    by simp_all [arm64_norm], by simp_all [arm64_norm], by simp_all [arm64_norm],
    by simp_all [arm64_norm], by simp_all [arm64_norm], by simp_all [arm64_norm],
    by simp_all [arm64_norm],
    Nat.le_trans (M.liveBytes_free_le 1 3168 (M.step (.free 1 1568) st))
      (M.liveBytes_free_le 1 1568 st)⟩
  rw [← M.stepEvents_append]
  exact Entails.of_eq (by sep_ac_rfl)

abbrev p2_seg6e_1568_4k_placed_wp := @p2_seg6e_1568_hooks_placed_wp
abbrev p2_seg6e_1568_ext_placed_wp := @p2_seg6e_1568_hooks_placed_wp

set_option maxHeartbeats 1000000 in
theorem p2_seg6f_ext_placed_wp [LibsignalPlacement]
    (ext : String → Option (State → State))
    (s : State) (coroPtr msgPtr remoteAddrPtr localAddrPtr
    opkPacked kyberPacked ss0 v_330 v_388
    u_250 u_258 u_260 u_270 u_278 u_298 u_2a0
    u_80 u_88 u_90 u_a0 u_a8 u_b0
    u_3a0 u_3b0 u_3b8 u_3c0 u_3c8 u_3d0 u_3d8 : BitVec 64)
    (opkIdIsSome signedPreKeyId u_268 u_26c u_2a8 u_b8 : BitVec 32)
    (msgVerByte b_390 b_3ac : BitVec 8)
    (hss0_ne : ss0 + 1#64 ≠ 0#64)
    (hpack_lo : (opkPacked &&& 0xff#64) = (opkIdIsSome.zeroExtend 64 &&& 0xff#64))
    (hpc : s.pc = stageP1EntryPlaced + 0x1698#64)
    (hrun : s.status = .Running)
    (_hsp_align : (s.sp &&& 15#64 == 0#64) = true)
    (hx19 : s.readReg64 .x19 = coroPtr)
    (hx20 : s.readReg64 .x20 = 0xfffffffffffffffe#64)
    (hx22 : s.readReg64 .x22 = kyberPacked)
    (hx23 : s.readReg64 .x23 = opkIdIsSome.zeroExtend 64)
    (hx24 : s.readReg64 .x24 = opkPacked) :
    SepWP (stageP1ProgPlaced ext) (stageP1EntryPlaced + 0x1778#64) s
      (((coroPtr + 0x70#64) ↦₆₄ msgPtr) ∗ ((coroPtr + 0x78#64) ↦₆₄ remoteAddrPtr) ∗
       ((coroPtr + 0x80#64) ↦₆₄ localAddrPtr) ∗ ((coroPtr + 0xf8#64) ↦₆₄ ss0) ∗
       ((coroPtr + 0x250#64) ↦₆₄ u_250) ∗ ((coroPtr + 0x258#64) ↦₆₄ u_258) ∗
       ((coroPtr + 0x260#64) ↦₆₄ u_260) ∗ ((coroPtr + 0x268#64) ↦₃₂ u_268) ∗
       ((coroPtr + 0x26c#64) ↦₃₂ u_26c) ∗ ((coroPtr + 0x270#64) ↦₆₄ u_270) ∗
       ((coroPtr + 0x278#64) ↦₆₄ u_278) ∗ ((coroPtr + 0x298#64) ↦₆₄ u_298) ∗
       ((coroPtr + 0x2a0#64) ↦₆₄ u_2a0) ∗ ((coroPtr + 0x2a8#64) ↦₃₂ u_2a8) ∗
       ((coroPtr + 0x330#64) ↦₆₄ v_330) ∗ ((coroPtr + 0x388#64) ↦₆₄ v_388) ∗
       ((coroPtr + 0x390#64) ↦₈ b_390) ∗ ((msgPtr + 0x70#64) ↦₈ msgVerByte) ∗
       ((s.sp + 0x80#64) ↦₆₄ u_80) ∗ ((s.sp + 0x88#64) ↦₆₄ u_88) ∗
       ((s.sp + 0x90#64) ↦₆₄ u_90) ∗ ((s.sp + 0xa0#64) ↦₆₄ u_a0) ∗
       ((s.sp + 0xa8#64) ↦₆₄ u_a8) ∗ ((s.sp + 0xb0#64) ↦₆₄ u_b0) ∗
       ((s.sp + 0xb8#64) ↦₃₂ u_b8) ∗ ((s.sp + 0xd0#64) ↦₆₄ signedPreKeyId.zeroExtend 64) ∗
       ((s.sp + 0x3a0#64) ↦₆₄ u_3a0) ∗ ((s.sp + 0x3ac#64) ↦₈ b_3ac) ∗
       ((s.sp + 0x3b0#64) ↦₆₄ (s.sp + 0x3b0#64 - (s.sp + 0x3b0#64) + u_3b0)) ∗
       ((s.sp + 0x3b8#64) ↦₆₄ u_3b8) ∗ ((s.sp + 0x3c0#64) ↦₆₄ u_3c0) ∗
       ((s.sp + 0x3c8#64) ↦₆₄ u_3c8) ∗ ((s.sp + 0x3d0#64) ↦₆₄ u_3d0) ∗
       ((s.sp + 0x3d8#64) ↦₆₄ u_3d8))
      (fun s1 P_f =>
        (P_f ⊢
          ((coroPtr + 0x70#64) ↦₆₄ msgPtr) ∗ ((coroPtr + 0x78#64) ↦₆₄ remoteAddrPtr) ∗
          ((coroPtr + 0x80#64) ↦₆₄ localAddrPtr) ∗ ((coroPtr + 0xf8#64) ↦₆₄ ss0) ∗
          ((coroPtr + 0x250#64) ↦₆₄ 0xfffffffffffffffe#64) ∗
          ((coroPtr + 0x258#64) ↦₆₄ opkPacked) ∗ ((coroPtr + 0x260#64) ↦₆₄ kyberPacked) ∗
          ((coroPtr + 0x268#64) ↦₃₂ signedPreKeyId) ∗
          ((coroPtr + 0x26c#64) ↦₃₂ (s.readReg64 (Reg.gpr 11#5)).truncate 32) ∗
          ((coroPtr + 0x270#64) ↦₆₄ v_330) ∗ ((coroPtr + 0x278#64) ↦₆₄ v_388) ∗
          ((coroPtr + 0x298#64) ↦₆₄ opkPacked) ∗ ((coroPtr + 0x2a0#64) ↦₆₄ kyberPacked) ∗
          ((coroPtr + 0x2a8#64) ↦₃₂ signedPreKeyId) ∗ ((coroPtr + 0x330#64) ↦₆₄ v_330) ∗
          ((coroPtr + 0x388#64) ↦₆₄ v_388) ∗ ((coroPtr + 0x390#64) ↦₈ 1#8) ∗
          ((msgPtr + 0x70#64) ↦₈ msgVerByte) ∗ ((s.sp + 0x80#64) ↦₆₄ (coroPtr + 0xf8#64)) ∗
          ((s.sp + 0x88#64) ↦₆₄ (coroPtr + 0xe0#64)) ∗ ((s.sp + 0x90#64) ↦₆₄ v_388) ∗
          ((s.sp + 0xa0#64) ↦₆₄ localAddrPtr) ∗ ((s.sp + 0xa8#64) ↦₆₄ v_330) ∗
          ((s.sp + 0xb0#64) ↦₆₄ msgPtr) ∗ ((s.sp + 0xb8#64) ↦₃₂ msgVerByte.zeroExtend 32) ∗
          ((s.sp + 0xd0#64) ↦₆₄ signedPreKeyId.zeroExtend 64) ∗
          ((s.sp + 0x3a0#64) ↦₆₄ remoteAddrPtr) ∗ ((s.sp + 0x3ac#64) ↦₈ 3#8) ∗
          ((s.sp + 0x3b0#64) ↦₆₄ (s.sp + 0x3ac#64)) ∗ ((s.sp + 0x3b8#64) ↦₆₄ msgPtr) ∗
          ((s.sp + 0x3c0#64) ↦₆₄ (s.sp + 0x3a0#64)) ∗ ((s.sp + 0x3c8#64) ↦₆₄ 0#64) ∗
          ((s.sp + 0x3d0#64) ↦₆₄ 8#64) ∗ ((s.sp + 0x3d8#64) ↦₆₄ 0#64)) ∧
        s1.sp = s.sp ∧ s1.trace = s.trace ∧ s1.readReg64 .x8 = coroPtr + 0xe0#64 ∧
        s1.readReg64 .x9 = 8#64 ∧ s1.readReg64 .x10 = msgVerByte.zeroExtend 64 ∧
        s1.readReg64 .x11 = coroPtr + 0xf8#64 ∧ s1.readReg64 .x19 = coroPtr ∧
        s1.readReg64 .x20 = 0xfffffffffffffffe#64 ∧ s1.readReg64 .x22 = kyberPacked ∧
        s1.readReg64 .x23 = opkPacked ∧ s1.readReg64 .x24 = opkPacked ∧
        s1.readReg64 .x25 = s.readReg64 .x25 ∧ s1.readReg64 .x26 = v_330 ∧
        s1.readReg64 .x27 = s.sp + 0x370#64 ∧ s1.readReg64 .x28 = s.readReg64 .x28 ∧
        s1.readReg64 .x29 = s.readReg64 .x29 ∧
        calleeSavedVRegs s1 = calleeSavedVRegs s ∧
        VmPreserved s s1) := by
  have hss0_beq : (ss0 + 1#64 == 0#64) = false := beq_eq_false_iff_ne.mpr hss0_ne
  dsimp only [stageP1ProgPlaced, stageP1EntryPlaced] at hpc ⊢
  have hx19' : s.readReg64 (Reg.gpr 19#5) = coroPtr := hx19
  have hx20' : s.readReg64 (Reg.gpr 20#5) = 0xfffffffffffffffe#64 := hx20
  have hx22' : s.readReg64 (Reg.gpr 22#5) = kyberPacked := hx22
  have hx23' : s.readReg64 (Reg.gpr 23#5) = opkIdIsSome.zeroExtend 64 := hx23
  have hx24' : s.readReg64 (Reg.gpr 24#5) = opkPacked := hx24
  have hu3b0 : s.sp + 0x3b0#64 - (s.sp + 0x3b0#64) + u_3b0 = u_3b0 := by bv_omega
  rw [hu3b0]
  wp_steps_sync_pool_518 ext (blkPl_518.base + 6008#64)
  refine SepWP.done _hpcm _hrunm ?_
  have hbfm1 : ((opkIdIsSome.zeroExtend 64 &&& 255#64) |||
    ((opkPacked >>> 8 &&& 72057594037927935#64) <<< 8)) = opkPacked := by
    revert hpack_lo; clear * -; bv_slice
  refine ⟨?_, rfl, rfl,
    by simp_all [arm64_norm], by simp_all [arm64_norm], by simp_all [arm64_norm],
    by simp_all [arm64_norm], by simp_all [arm64_norm], by simp_all [arm64_norm],
    by simp_all [arm64_norm], by simp_all [arm64_norm], by simp_all [arm64_norm],
    by simp_all [arm64_norm], by simp_all [arm64_norm], by simp_all [arm64_norm],
    by simp_all [arm64_norm], by simp_all [arm64_norm], by simp_all [arm64_norm], _hvm⟩
  rw [hbfm1]
  exact Entails.of_eq (by sep_ac_rfl)

end LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Kits.StageP2BlocksB6PlacedBudget
