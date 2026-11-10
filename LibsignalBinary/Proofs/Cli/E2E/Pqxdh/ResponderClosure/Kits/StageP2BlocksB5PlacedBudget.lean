/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Kits.StageP2DefsPlacedBudget
public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Kits.StageP2BlocksB5Placed
public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Kits.StageP1StepsXExtPlacedBudgetAux
public import LibsignalBinary.Heap.IfaceBudget
public import LibsignalBinary.Heap.IfaceBudgetLemmas
public import LibsignalBinary.Proofs.Placed.BudgetVmSteps
public meta import Lean.Elab.Tactic -- shake: keep
import LibsignalBinary.Proofs.Common.SharedHelpers
meta import LibsignalBinary.Proofs.Common.SharedHelpers -- shake: keep
import Arm64.Trusted.Spec.Hoare
import Arm64.Trusted.Spec.SepLogic
import LibsignalBinary.Proofs.E2E.InMem.HashbrownBin.IdentityKeyStoreFutures.SaveIdentity
import LibsignalBinary.Proofs.E2E.InMem.HashbrownBin.SessionStoreFutures.StoreCommon
import LibsignalBinary.Proofs.E2E.Record.Serialization.SessionCloneAux.Base
import LibsignalBinary.Proofs.SpqrV1.Poly.EncoderFromPb.Defs
import LibsignalBinary.Proofs.SpqrV1.Poly.EncoderIntoPb.Defs
import LibsignalBinary.Proofs.SpqrV1.Prost.MessageEncode.Base
import LibsignalBinary.Proofs.TripleRatchet.GeneralizeEntry
import LibsignalBinary.Proofs.TripleRatchet.ReceiveRatchet.From.Step244

/-!
# Budget-Threaded Relocatable Stage P2 Basic Blocks — Substage P2.5

`RustCliAllocBudget M` / `VmPreserved` basic-block lemmas for Substage P2.5 (`+0x36ac →
initialize_bob_session`) on Block `518` (`stageP1ProgPlaced ext`).
-/

@[expose] public section

set_option autoImplicit false

namespace LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Kits.StageP2BlocksB5PlacedBudget

open Arm64 ProofLib ProofLib.ProgramReflection
open LibsignalBinary.Heap (
  AllocCallPreserved AllocCostModel BudgetLimits RustCliAllocBudget VmPreserved
  rustCliDeallocBudgetSpec rustDeallocEvents
)
open LibsignalBinary.Proofs.Placed.BudgetVmSteps (sepWP_rebase_vmPreserved trapHooks)
open LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Kits.StageP1StepsXExtPlacedBudgetAux (
  sepWP_seg_rebase_vm
)
open LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Kits.StageP2DefsPlacedBudget (
  StageP2ClosureHooksPlaced
)
open CryptoVerification (
  LibsignalPlacement libsignalSessionLib lsRustDeallocSym lsmpl lsρ
)
open CryptoVerification.RustHeap (allocHookStack)
open CryptoVerification.E2E.Pqxdh.ResponderClosure (
  bytes7At keyPair64UnalignedAt
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

/-! ## Substage P2.5 Basic Blocks (`+0x36ac -> initialize_bob_session`) -/

set_option maxHeartbeats 800000 in
theorem p2_seg5a_ext_placed_wp [LibsignalPlacement] (ext : String → Option (State → State))
    (s : State) (coroPtr ctxPtr idKpFutPtr idKpFutVt idKpPollAddr u_4f8 u_500 : BitVec 64)
    (hpc : s.pc = stageP1EntryPlaced + 0x36ac#64)
    (hrun : s.status = .Running)
    (hx0 : s.readReg64 .x0 = idKpFutPtr)
    (hx1 : s.readReg64 .x1 = idKpFutVt)
    (hx19 : s.readReg64 .x19 = coroPtr)
    (hx27 : s.readReg64 .x27 = ctxPtr) :
    SepWP (stageP1ProgPlaced ext) idKpPollAddr s
      (((coroPtr + 0x4f8#64) ↦₆₄ u_4f8) ∗
       ((coroPtr + 0x500#64) ↦₆₄ u_500) ∗
       ((idKpFutVt + 0x18#64) ↦₆₄ᵣ idKpPollAddr))
      (fun s1 P_f =>
        (P_f ⊢
          ((coroPtr + 0x4f8#64) ↦₆₄ idKpFutPtr) ∗
          ((coroPtr + 0x500#64) ↦₆₄ idKpFutVt) ∗
          ((idKpFutVt + 0x18#64) ↦₆₄ᵣ idKpPollAddr)) ∧
        s1.sp = s.sp ∧
        s1.trace = s.trace ∧
        s1.readReg64 .x0 = idKpFutPtr ∧
        s1.readReg64 .x1 = ctxPtr ∧
        s1.readReg64 .x8 = s.sp + 0x3e0#64 ∧
        s1.readReg64 .x19 = coroPtr ∧
        s1.readReg64 .x21 = s.readReg64 .x21 ∧
        s1.readReg64 .x23 = s.readReg64 .x23 ∧
        s1.readReg64 .x24 = s.readReg64 .x24 ∧
        s1.readReg64 .x25 = s.readReg64 .x25 ∧
        s1.readReg64 .x26 = s.readReg64 .x26 ∧
        s1.readReg64 .x27 = ctxPtr ∧
        s1.readReg64 .x28 = s.readReg64 .x28 ∧
        s1.readReg64 .x29 = s.readReg64 .x29 ∧
        s1.readReg64 .x30 = stageP1EntryPlaced + 0x7bc#64 ∧
        calleeSavedVRegs s1 = calleeSavedVRegs s ∧
        VmPreserved s s1) := by
  dsimp only [stageP1ProgPlaced, stageP1EntryPlaced] at hpc ⊢
  have hx0' : s.readReg64 (Reg.gpr 0#5) = idKpFutPtr := hx0
  have hx1' : s.readReg64 (Reg.gpr 1#5) = idKpFutVt := hx1
  have hx19' : s.readReg64 (Reg.gpr 19#5) = coroPtr := hx19
  have hx27' : s.readReg64 (Reg.gpr 27#5) = ctxPtr := hx27
  wp_steps_sync_pool_518 ext idKpPollAddr
  refine SepWP.done _hpcm _hrunm ?_
  exact ⟨Entails.of_eq (by sep_ac_rfl), rfl, rfl,
    by simp_all [arm64_norm], by simp_all [arm64_norm], by simp_all [arm64_norm],
    by simp_all [arm64_norm], by simp_all [arm64_norm], by simp_all [arm64_norm],
    by simp_all [arm64_norm], by simp_all [arm64_norm], by simp_all [arm64_norm],
    by simp_all [arm64_norm], by simp_all [arm64_norm], by simp_all [arm64_norm],
    by simp_all [arm64_norm], by simp_all [arm64_norm], _hvm⟩

set_option maxHeartbeats 1000000 in
theorem p2_seg5b_fp_ext_placed_wp [LibsignalPlacement] (ext : String → Option (State → State))
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
      (((s.sp + 0x3e0#64) ↦₈ 0#8) ∗
       keyPair64UnalignedAt (s.sp + 0x3e1#64) b0 b1 b2 b3 b4 b5 b6 w0 w1 w2 w3 w4 w5 w6 b63 ∗
       bytes7At (s.sp + 0x3c8#64) s0 s1_b s2 s3 s4 s5 s6 ∗
       ((fp + 0xffffffffffffff80#64) ↦₆₄ u_fp80) ∗ ((fp + 0xffffffffffffff88#64) ↦₈ b_fp78) ∗
       ((s.sp + 0x98#64) ↦₆₄ u_98) ∗ ((s.sp + 0xa0#64) ↦₆₄ u_a0) ∗
       ((s.sp + 0xa8#64) ↦₆₄ u_a8) ∗ ((s.sp + 0xb0#64) ↦₆₄ u_b0) ∗
       ((s.sp + 0xb8#64) ↦₆₄ u_b8) ∗ ((s.sp + 0xc0#64) ↦₆₄ u_c0) ∗
       ((s.sp + 0xd0#64) ↦₆₄ u_d0) ∗ ((coroPtr + 0x4f8#64) ↦₆₄ idKpFutPtr) ∗
       ((coroPtr + 0x500#64) ↦₆₄ idKpFutVt) ∗ ((msgPtr + 0x7c#64) ↦₃₂ opkId) ∗
       ((idKpFutVt + 0x0#64) ↦₆₄ᵣ idKpDropAddr))
      (fun s1 P_f =>
        (P_f ⊢
          ((s.sp + 0x3e0#64) ↦₈ 0#8) ∗
          keyPair64UnalignedAt (s.sp + 0x3e1#64) b0 b1 b2 b3 b4 b5 b6 w0 w1 w2 w3 w4 w5 w6 b63 ∗
          bytes7At (s.sp + 0x3c8#64) b0 b1 b2 b3 b4 b5 b6 ∗
          ((fp + 0xffffffffffffff80#64) ↦₆₄ w6) ∗ ((fp + 0xffffffffffffff88#64) ↦₈ b63) ∗
          ((s.sp + 0x98#64) ↦₆₄ v_98) ∗ ((s.sp + 0xa0#64) ↦₆₄ v_a0) ∗
          ((s.sp + 0xa8#64) ↦₆₄ w4) ∗ ((s.sp + 0xb0#64) ↦₆₄ v_b0) ∗
          ((s.sp + 0xb8#64) ↦₆₄ w2) ∗ ((s.sp + 0xc0#64) ↦₆₄ ctxPtr) ∗
          ((s.sp + 0xd0#64) ↦₆₄ w3) ∗ ((coroPtr + 0x4f8#64) ↦₆₄ idKpFutPtr) ∗
          ((coroPtr + 0x500#64) ↦₆₄ idKpFutVt) ∗ ((msgPtr + 0x7c#64) ↦₃₂ opkId) ∗
          ((idKpFutVt + 0x0#64) ↦₆₄ᵣ idKpDropAddr)) ∧
        s1.sp = s.sp ∧ s1.trace = s.trace ∧ s1.readReg64 .x0 = idKpFutPtr ∧
        s1.readReg64 .x19 = coroPtr ∧ s1.readReg64 .x20 = w0 ∧
        s1.readReg64 .x21 = idKpFutPtr ∧ s1.readReg64 .x22 = 0#64 ∧
        s1.readReg64 .x23 = w1 ∧ s1.readReg64 .x24 = idKpFutVt ∧
        s1.readReg64 .x25 = s.readReg64 .x25 ∧ s1.readReg64 .x26 = v_98 ∧
        s1.readReg64 .x27 = w5 ∧ s1.readReg64 .x28 = s.readReg64 .x28 ∧
        s1.readReg64 .x29 = fp ∧ s1.readReg64 .x30 = stageP1EntryPlaced + 0xac4#64 ∧
        calleeSavedVRegs s1 = calleeSavedVRegs s ∧
        VmPreserved s s1) := by
  have hdrop_beq : (idKpDropAddr == 0#64) = false := beq_eq_false_iff_ne.mpr hdrop_nz
  dsimp only [stageP1ProgPlaced, stageP1EntryPlaced, keyPair64UnalignedAt, bytes7At] at hpc ⊢
  have hx19' : s.readReg64 (Reg.gpr 19#5) = coroPtr := hx19
  have hx21' : s.readReg64 (Reg.gpr 21#5) = v_b0 := hx21
  have hx23' : s.readReg64 (Reg.gpr 23#5) = v_a0 := hx23
  have hx24' : s.readReg64 (Reg.gpr 24#5) = s.sp + 0x370#64 := hx24
  have hx26' : s.readReg64 (Reg.gpr 26#5) = v_98 := hx26
  have hx27' : s.readReg64 (Reg.gpr 27#5) = ctxPtr := hx27
  have hx29' : s.readReg64 (Reg.gpr 29#5) = fp := hx29
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

set_option maxHeartbeats 1200000 in
theorem p2_seg5c1_fp_gen_hooks_placed_wp [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {st : M.σ}
    (ext : String → Option (State → State))
    (hH : StageP2ClosureHooksPlaced A lim ext)
    (s : State) (coroPtr msgPtr remoteAddrPtr localAddrPtr idKpFutPtr idKpFutVt fp
    kyberPreKeyId64 w0 w1 w2 w3 w4 w5 w6
    cw0 cw1 cw2 cw3 cw4 cw5 : BitVec 64)
    (opkId : BitVec 32)
    (b0 b1 b2 b3 b4 b5 b6 b63
     c0 c1 c2 c3 c4 c5 c6 : BitVec 8)
    (kpBoxSize : Nat)
    (hpc : s.pc = stageP1EntryPlaced + 0xac4#64)
    (hrun : s.status = .Running)
    (hsp_align : (s.sp &&& 15#64 == 0#64) = true)
    (hbs_nz : BitVec.ofNat 64 kpBoxSize ≠ 0#64)
    (hbs_lt : kpBoxSize < 2 ^ 64)
    (hx19 : s.readReg64 .x19 = coroPtr)
    (hx20 : s.readReg64 .x20 = w0)
    (hx21 : s.readReg64 .x21 = idKpFutPtr)
    (hx22 : s.readReg64 .x22 = 0#64)
    (hx23 : s.readReg64 .x23 = w1)
    (hx24 : s.readReg64 .x24 = idKpFutVt)
    (hx27 : s.readReg64 .x27 = w5)
    (hx29 : s.readReg64 .x29 = fp) :
    SepWP (stageP1ProgPlaced ext) (stageP1EntryPlaced + 0x114c#64) s
      (((idKpFutVt + 0x8#64) ↦₆₄ᵣ BitVec.ofNat 64 kpBoxSize) ∗
       ((idKpFutVt + 0x10#64) ↦₆₄ᵣ 8#64) ∗
       A.live idKpFutPtr kpBoxSize 8 ∗ memRegion idKpFutPtr kpBoxSize ∗
       A.pool lim st s ∗ stackAt s.sp allocHookStack ∗
       bytes7At (s.sp + 0x3c8#64) b0 b1 b2 b3 b4 b5 b6 ∗
       bytes7At (coroPtr + 0x798#64) c0 c1 c2 c3 c4 c5 c6 ∗
       ((coroPtr + 0x79f#64) ↦₆₄ cw0) ∗ ((coroPtr + 0x7a7#64) ↦₆₄ cw1) ∗
       ((coroPtr + 0x7af#64) ↦₆₄ cw2) ∗ ((coroPtr + 0x7b7#64) ↦₆₄ cw3) ∗
       ((coroPtr + 0x7bf#64) ↦₆₄ cw4) ∗ ((coroPtr + 0x7c7#64) ↦₆₄ cw5) ∗
       ((s.sp + 0x98#64) ↦₆₄ (coroPtr + 0x398#64)) ∗ ((s.sp + 0xa8#64) ↦₆₄ w4) ∗
       ((s.sp + 0xb8#64) ↦₆₄ w2) ∗ ((s.sp + 0xd0#64) ↦₆₄ w3) ∗
       ((fp + 0xffffffffffffff80#64) ↦₆₄ w6) ∗ ((fp + 0xffffffffffffff88#64) ↦₈ b63) ∗
       ((coroPtr + 0x470#64) ↦₆₄ remoteAddrPtr) ∗ ((coroPtr + 0x478#64) ↦₆₄ localAddrPtr) ∗
       ((coroPtr + 0x488#64) ↦₆₄ kyberPreKeyId64) ∗ ((msgPtr + 0x7c#64) ↦₃₂ opkId))
      (fun s1 P_f =>
        let st' := M.stepEvents (rustDeallocEvents kpBoxSize 8) st
        (P_f ⊢
          ((idKpFutVt + 0x8#64) ↦₆₄ᵣ BitVec.ofNat 64 kpBoxSize) ∗
          ((idKpFutVt + 0x10#64) ↦₆₄ᵣ 8#64) ∗
          A.pool lim st' s1 ∗ stackAt s.sp allocHookStack ∗
          bytes7At (s.sp + 0x3c8#64) b0 b1 b2 b3 b4 b5 b6 ∗
          bytes7At (coroPtr + 0x798#64) b0 b1 b2 b3 b4 b5 b6 ∗
          ((coroPtr + 0x79f#64) ↦₆₄ w0) ∗ ((coroPtr + 0x7a7#64) ↦₆₄ w1) ∗
          ((coroPtr + 0x7af#64) ↦₆₄ w2) ∗ ((coroPtr + 0x7b7#64) ↦₆₄ w3) ∗
          ((coroPtr + 0x7bf#64) ↦₆₄ w4) ∗ ((coroPtr + 0x7c7#64) ↦₆₄ w5) ∗
          ((s.sp + 0x98#64) ↦₆₄ (coroPtr + 0x398#64)) ∗ ((s.sp + 0xa8#64) ↦₆₄ w4) ∗
          ((s.sp + 0xb8#64) ↦₆₄ w2) ∗ ((s.sp + 0xd0#64) ↦₆₄ w3) ∗
          ((fp + 0xffffffffffffff80#64) ↦₆₄ w6) ∗ ((fp + 0xffffffffffffff88#64) ↦₈ b63) ∗
          ((coroPtr + 0x470#64) ↦₆₄ remoteAddrPtr) ∗ ((coroPtr + 0x478#64) ↦₆₄ localAddrPtr) ∗
          ((coroPtr + 0x488#64) ↦₆₄ kyberPreKeyId64) ∗ ((msgPtr + 0x7c#64) ↦₃₂ opkId)) ∧
        s1.sp = s.sp ∧ s1.trace = s.trace ∧ s1.readReg64 .x0 = coroPtr + 0x798#64 ∧
        s1.readReg64 .x1 = localAddrPtr ∧ s1.readReg64 .x3 = remoteAddrPtr ∧
        s1.readReg64 .x8 = b63.zeroExtend 64 ∧ s1.readReg64 .x9 = w6 ∧
        s1.readReg64 .x10 = coroPtr + 0x798#64 ∧ s1.readReg64 .x11 = coroPtr + 0x7cf#64 ∧
        s1.readReg64 .x19 = coroPtr ∧ s1.readReg64 .x21 = kyberPreKeyId64 ∧
        s1.readReg64 .x22 = s.sp + 0x370#64 ∧ s1.readReg64 .x23 = s.sp + 0x930#64 ∧
        s1.readReg64 .x24 = coroPtr + 0x398#64 ∧ s1.readReg64 .x25 = s.readReg64 .x25 ∧
        s1.readReg64 .x26 = s.readReg64 .x26 ∧ s1.readReg64 .x27 = w5 ∧
        s1.readReg64 .x28 = s.readReg64 .x28 ∧ s1.readReg64 .x29 = fp ∧
        calleeSavedVRegs s1 = calleeSavedVRegs s ∧
        M.liveBytes st' ≤ M.liveBytes st) := by
  have hdealloc := hH.dealloc
  have hbs_beq : (BitVec.ofNat 64 kpBoxSize == 0#64) = false := beq_eq_false_iff_ne.mpr hbs_nz
  have hbs_toNat : (BitVec.ofNat 64 kpBoxSize).toNat = kpBoxSize := Nat.mod_eq_of_lt hbs_lt
  dsimp only [stageP1ProgPlaced, stageP1EntryPlaced, lsRustDeallocSym, bytes7At] at hdealloc hpc ⊢
  have hx19' : s.readReg64 (Reg.gpr 19#5) = coroPtr := hx19
  have hx20' : s.readReg64 (Reg.gpr 20#5) = w0 := hx20
  have hx21' : s.readReg64 (Reg.gpr 21#5) = idKpFutPtr := hx21
  have hx22' : s.readReg64 (Reg.gpr 22#5) = 0#64 := hx22
  have hx23' : s.readReg64 (Reg.gpr 23#5) = w1 := hx23
  have hx24' : s.readReg64 (Reg.gpr 24#5) = idKpFutVt := hx24
  have hx27' : s.readReg64 (Reg.gpr 27#5) = w5 := hx27
  have hx29' : s.readReg64 (Reg.gpr 29#5) = fp := hx29
  conv =>
    arg 4
    simp (config := { maxSteps := 1000000 }) only [
      BitVec.add_assoc, BitVec.reduceAdd, sepConj_assoc]
  wp_steps_sync_pool_518 ext (lsρ "_RNvCs1njKG4L9aB3_7___rustc14___rust_dealloc")
  clear _hvm _hpcm _hrunm
  wp_call hdealloc (idKpFutPtr, kpBoxSize, 8, st)
  wp_steps_sync_pool_518 ext (blkPl_518.base + 4428#64)
  refine SepWP.done _hpcm _hrunm ?_
  refine ⟨?_, by simp_all [arm64_norm], by simp_all [arm64_norm, AllocCallPreserved],
    by simp_all [arm64_norm], by simp_all [arm64_norm], by simp_all [arm64_norm],
    by simp_all [arm64_norm], by simp_all [arm64_norm], by simp_all [arm64_norm],
    by simp_all [arm64_norm], by simp_all [arm64_norm], by simp_all [arm64_norm],
    by simp_all [arm64_norm], by simp_all [arm64_norm], by simp_all [arm64_norm],
    by simp_all [arm64_norm], by simp_all [arm64_norm], by simp_all [arm64_norm],
    by simp_all [arm64_norm], by simp_all [arm64_norm], by simp_all [arm64_norm],
    by simp_all [arm64_norm]⟩
  have hfp80 : fp - 128#64 = fp + 0xffffffffffffff80#64 := by bv_omega
  have hfp78 : fp - 120#64 = fp + 0xffffffffffffff88#64 := by bv_omega
  simp only [hfp80, hfp78, BitVec.add_assoc, BitVec.reduceAdd, sepConj_assoc]
  exact Entails.of_eq (by sep_ac_rfl)

abbrev p2_seg5c1_fp_gen_4k_placed_wp := @p2_seg5c1_fp_gen_hooks_placed_wp
abbrev p2_seg5c1_fp_gen_placed_wp := @p2_seg5c1_fp_gen_hooks_placed_wp

set_option maxHeartbeats 1000000 in
theorem p2_seg5c2_ext_placed_wp [LibsignalPlacement]
    (ext : String → Option (State → State))
    (s : State) (coroPtr msgPtr ik0 ik1 ik2 ik3 w6 cw6
    u_930 u_938 u_940 u_948 : BitVec 64)
    (b63 c63 opk_b64 : BitVec 8)
    (hpc : s.pc = stageP1EntryPlaced + 0x114c#64)
    (hrun : s.status = .Running)
    (hx8 : s.readReg64 .x8 = b63.zeroExtend 64)
    (hx9 : s.readReg64 .x9 = w6)
    (hx10 : s.readReg64 .x10 = coroPtr + 0x798#64)
    (hx11 : s.readReg64 .x11 = coroPtr + 0x7cf#64)
    (hx19 : s.readReg64 .x19 = coroPtr)
    (hx23 : s.readReg64 .x23 = s.sp + 0x930#64) :
    SepWP (stageP1ProgPlaced ext) (stageP1EntryPlaced + 0x1168#64) s
      (((coroPtr + 0x798#64) ↦₆₄ ik0) ∗ ((coroPtr + 0x7a0#64) ↦₆₄ ik1) ∗
       ((coroPtr + 0x7a8#64) ↦₆₄ ik2) ∗ ((coroPtr + 0x7b0#64) ↦₆₄ ik3) ∗
       ((coroPtr + 0x7cf#64) ↦₆₄ cw6) ∗ ((coroPtr + 0x7d7#64) ↦₈ c63) ∗
       ((coroPtr + 0x4f0#64) ↦₈ opk_b64) ∗ ((coroPtr + 0x468#64) ↦₆₄ msgPtr) ∗
       ((s.sp + 0x930#64) ↦₆₄ u_930) ∗ ((s.sp + 0x938#64) ↦₆₄ u_938) ∗
       ((s.sp + 0x940#64) ↦₆₄ u_940) ∗ ((s.sp + 0x948#64) ↦₆₄ u_948))
      (fun s1 P_f =>
        (P_f ⊢
          ((coroPtr + 0x798#64) ↦₆₄ ik0) ∗ ((coroPtr + 0x7a0#64) ↦₆₄ ik1) ∗
          ((coroPtr + 0x7a8#64) ↦₆₄ ik2) ∗ ((coroPtr + 0x7b0#64) ↦₆₄ ik3) ∗
          ((coroPtr + 0x7cf#64) ↦₆₄ w6) ∗ ((coroPtr + 0x7d7#64) ↦₈ b63) ∗
          ((coroPtr + 0x4f0#64) ↦₈ opk_b64) ∗ ((coroPtr + 0x468#64) ↦₆₄ msgPtr) ∗
          ((s.sp + 0x930#64) ↦₆₄ ik0) ∗ ((s.sp + 0x938#64) ↦₆₄ ik1) ∗
          ((s.sp + 0x940#64) ↦₆₄ ik2) ∗ ((s.sp + 0x948#64) ↦₆₄ ik3)) ∧
        s1.sp = s.sp ∧ s1.trace = s.trace ∧ s1.readReg64 .x0 = s.readReg64 .x0 ∧
        s1.readReg64 .x1 = s.readReg64 .x1 ∧ s1.readReg64 .x2 = msgPtr + 0xc8#64 ∧
        s1.readReg64 .x3 = s.readReg64 .x3 ∧ s1.readReg64 .x8 = opk_b64.zeroExtend 64 ∧
        s1.readReg64 .x9 = msgPtr ∧ s1.readReg64 .x10 = coroPtr + 0x798#64 ∧
        s1.readReg64 .x19 = coroPtr ∧ s1.readReg64 .x21 = s.readReg64 .x21 ∧
        s1.readReg64 .x22 = s.readReg64 .x22 ∧ s1.readReg64 .x23 = s.sp + 0x930#64 ∧
        s1.readReg64 .x24 = s.readReg64 .x24 ∧ s1.readReg64 .x25 = s.readReg64 .x25 ∧
        s1.readReg64 .x26 = s.readReg64 .x26 ∧ s1.readReg64 .x27 = s.readReg64 .x27 ∧
        s1.readReg64 .x28 = s.readReg64 .x28 ∧ s1.readReg64 .x29 = s.readReg64 .x29 ∧
        calleeSavedVRegs s1 = calleeSavedVRegs s ∧
        VmPreserved s s1) := by
  dsimp only [stageP1ProgPlaced, stageP1EntryPlaced] at hpc ⊢
  have hx8' : s.readReg64 (Reg.gpr 8#5) = b63.zeroExtend 64 := hx8
  have hx9' : s.readReg64 (Reg.gpr 9#5) = w6 := hx9
  have hx10' : s.readReg64 (Reg.gpr 10#5) = coroPtr + 0x798#64 := hx10
  have hx11' : s.readReg64 (Reg.gpr 11#5) = coroPtr + 0x7cf#64 := hx11
  have hx19' : s.readReg64 (Reg.gpr 19#5) = coroPtr := hx19
  have hx23' : s.readReg64 (Reg.gpr 23#5) = s.sp + 0x930#64 := hx23
  wp_steps_sync_pool_518 ext (blkPl_518.base + 4456#64)
  refine SepWP.done _hpcm _hrunm ?_
  exact ⟨Entails.of_eq (by sep_ac_rfl), rfl, rfl,
    by simp_all [arm64_norm], by simp_all [arm64_norm], by simp_all [arm64_norm],
    by simp_all [arm64_norm], by simp_all [arm64_norm], by simp_all [arm64_norm],
    by simp_all [arm64_norm], by simp_all [arm64_norm], by simp_all [arm64_norm],
    by simp_all [arm64_norm], by simp_all [arm64_norm], by simp_all [arm64_norm],
    by simp_all [arm64_norm], by simp_all [arm64_norm], by simp_all [arm64_norm],
    by simp_all [arm64_norm], by simp_all [arm64_norm], by simp_all [arm64_norm], _hvm⟩

set_option maxHeartbeats 1000000 in
theorem p2_seg5c3_ext_placed_wp [LibsignalPlacement]
    (ext : String → Option (State → State))
    (s : State) (coroPtr msgPtr localAddrPtr remoteAddrPtr
    ik4 ik5 ik6 ik7 spk0 spk1 spk2 spk3 spk4 spk5 spk6 spk7
    opk0 opk1 opk2 opk3 opk4 opk5 opk6 opk7 kyb0 kyb1 kyb2 kyb3
    ikA0 ikA1 ikA2 ikA3 ekA0 ekA1 ekA2 ekA3
    u_950 u_958 u_960 u_968 u_a90 u_a98 u_aa0 u_aa8 u_ab0 u_ab8 u_ac0 u_ac8
    u_3e0 u_3e8 u_3f0 u_3f8 u_400 u_408 u_410 u_418
    u_560 u_568 u_570 u_578 u_6a0 u_6a8 u_6b0 u_6b8
    u_7e0 u_7e8 u_7f0 u_7f8 : BitVec 64)
    (opk_b64 u_420 b_4f1 : BitVec 8)
    (hpc : s.pc = stageP1EntryPlaced + 0x1168#64)
    (hrun : s.status = .Running)
    (_hsp_align : (s.sp &&& 15#64 == 0#64) = true)
    (hx0 : s.readReg64 .x0 = coroPtr + 0x798#64)
    (hx1 : s.readReg64 .x1 = localAddrPtr)
    (hx2 : s.readReg64 .x2 = msgPtr + 0xc8#64)
    (hx3 : s.readReg64 .x3 = remoteAddrPtr)
    (hx8 : s.readReg64 .x8 = opk_b64.zeroExtend 64)
    (hx9 : s.readReg64 .x9 = msgPtr)
    (hx10 : s.readReg64 .x10 = coroPtr + 0x798#64)
    (hx19 : s.readReg64 .x19 = coroPtr)
    (hx22 : s.readReg64 .x22 = s.sp + 0x370#64)
    (hx23 : s.readReg64 .x23 = s.sp + 0x930#64)
    (hx24 : s.readReg64 .x24 = coroPtr + 0x398#64)
    (hx28 : s.readReg64 .x28 = s.sp + 0xa90#64) :
    SepWP (stageP1ProgPlaced ext)
      (libsignalSessionLib.resolve lsmpl "<libsignal_protocol::identity_key::IdentityKey>::is_same_account") s
      (((coroPtr + 0x7b8#64) ↦₆₄ ik4) ∗ ((coroPtr + 0x7c0#64) ↦₆₄ ik5) ∗
       ((coroPtr + 0x7c8#64) ↦₆₄ ik6) ∗ ((coroPtr + 0x7d0#64) ↦₆₄ ik7) ∗
       ((coroPtr + 0x398#64) ↦₆₄ spk0) ∗ ((coroPtr + 0x3a0#64) ↦₆₄ spk1) ∗
       ((coroPtr + 0x3a8#64) ↦₆₄ spk2) ∗ ((coroPtr + 0x3b0#64) ↦₆₄ spk3) ∗
       ((coroPtr + 0x3b8#64) ↦₆₄ spk4) ∗ ((coroPtr + 0x3c0#64) ↦₆₄ spk5) ∗
       ((coroPtr + 0x3c8#64) ↦₆₄ spk6) ∗ ((coroPtr + 0x3d0#64) ↦₆₄ spk7) ∗
       ((coroPtr + 0x4b0#64) ↦₆₄ opk0) ∗ ((coroPtr + 0x4b8#64) ↦₆₄ opk1) ∗
       ((coroPtr + 0x4c0#64) ↦₆₄ opk2) ∗ ((coroPtr + 0x4c8#64) ↦₆₄ opk3) ∗
       ((coroPtr + 0x4d0#64) ↦₆₄ opk4) ∗ ((coroPtr + 0x4d8#64) ↦₆₄ opk5) ∗
       ((coroPtr + 0x4e0#64) ↦₆₄ opk6) ∗ ((coroPtr + 0x4e8#64) ↦₆₄ opk7) ∗
       ((coroPtr + 0x4f1#64) ↦₈ b_4f1) ∗ ((coroPtr + 0x3d8#64) ↦₆₄ kyb0) ∗
       ((coroPtr + 0x3e0#64) ↦₆₄ kyb1) ∗ ((coroPtr + 0x3e8#64) ↦₆₄ kyb2) ∗
       ((coroPtr + 0x3f0#64) ↦₆₄ kyb3) ∗ ((msgPtr + 0xa8#64) ↦₆₄ ekA0) ∗
       ((msgPtr + 0xb0#64) ↦₆₄ ekA1) ∗ ((msgPtr + 0xb8#64) ↦₆₄ ekA2) ∗
       ((msgPtr + 0xc0#64) ↦₆₄ ekA3) ∗ ((msgPtr + 0xc8#64) ↦₆₄ ikA0) ∗
       ((msgPtr + 0xd0#64) ↦₆₄ ikA1) ∗ ((msgPtr + 0xd8#64) ↦₆₄ ikA2) ∗
       ((msgPtr + 0xe0#64) ↦₆₄ ikA3) ∗ ((s.sp + 0x950#64) ↦₆₄ u_950) ∗
       ((s.sp + 0x958#64) ↦₆₄ u_958) ∗ ((s.sp + 0x960#64) ↦₆₄ u_960) ∗
       ((s.sp + 0x968#64) ↦₆₄ u_968) ∗ ((s.sp + 0xa90#64) ↦₆₄ u_a90) ∗
       ((s.sp + 0xa98#64) ↦₆₄ u_a98) ∗ ((s.sp + 0xaa0#64) ↦₆₄ u_aa0) ∗
       ((s.sp + 0xaa8#64) ↦₆₄ u_aa8) ∗ ((s.sp + 0xab0#64) ↦₆₄ u_ab0) ∗
       ((s.sp + 0xab8#64) ↦₆₄ u_ab8) ∗ ((s.sp + 0xac0#64) ↦₆₄ u_ac0) ∗
       ((s.sp + 0xac8#64) ↦₆₄ u_ac8) ∗ ((s.sp + 0x3e0#64) ↦₆₄ u_3e0) ∗
       ((s.sp + 0x3e8#64) ↦₆₄ u_3e8) ∗ ((s.sp + 0x3f0#64) ↦₆₄ u_3f0) ∗
       ((s.sp + 0x3f8#64) ↦₆₄ u_3f8) ∗ ((s.sp + 0x400#64) ↦₆₄ u_400) ∗
       ((s.sp + 0x408#64) ↦₆₄ u_408) ∗ ((s.sp + 0x410#64) ↦₆₄ u_410) ∗
       ((s.sp + 0x418#64) ↦₆₄ u_418) ∗ ((s.sp + 0x420#64) ↦₈ u_420) ∗
       ((s.sp + 0x560#64) ↦₆₄ u_560) ∗ ((s.sp + 0x568#64) ↦₆₄ u_568) ∗
       ((s.sp + 0x570#64) ↦₆₄ u_570) ∗ ((s.sp + 0x578#64) ↦₆₄ u_578) ∗
       ((s.sp + 0x6a0#64) ↦₆₄ u_6a0) ∗ ((s.sp + 0x6a8#64) ↦₆₄ u_6a8) ∗
       ((s.sp + 0x6b0#64) ↦₆₄ u_6b0) ∗ ((s.sp + 0x6b8#64) ↦₆₄ u_6b8) ∗
       ((s.sp + 0x7e0#64) ↦₆₄ u_7e0) ∗ ((s.sp + 0x7e8#64) ↦₆₄ u_7e8) ∗
       ((s.sp + 0x7f0#64) ↦₆₄ u_7f0) ∗ ((s.sp + 0x7f8#64) ↦₆₄ u_7f8))
      (fun s1 P_f =>
        (P_f ⊢
          ((coroPtr + 0x7b8#64) ↦₆₄ ik4) ∗ ((coroPtr + 0x7c0#64) ↦₆₄ ik5) ∗
          ((coroPtr + 0x7c8#64) ↦₆₄ ik6) ∗ ((coroPtr + 0x7d0#64) ↦₆₄ ik7) ∗
          ((coroPtr + 0x398#64) ↦₆₄ spk0) ∗ ((coroPtr + 0x3a0#64) ↦₆₄ spk1) ∗
          ((coroPtr + 0x3a8#64) ↦₆₄ spk2) ∗ ((coroPtr + 0x3b0#64) ↦₆₄ spk3) ∗
          ((coroPtr + 0x3b8#64) ↦₆₄ spk4) ∗ ((coroPtr + 0x3c0#64) ↦₆₄ spk5) ∗
          ((coroPtr + 0x3c8#64) ↦₆₄ spk6) ∗ ((coroPtr + 0x3d0#64) ↦₆₄ spk7) ∗
          ((coroPtr + 0x4b0#64) ↦₆₄ opk0) ∗ ((coroPtr + 0x4b8#64) ↦₆₄ opk1) ∗
          ((coroPtr + 0x4c0#64) ↦₆₄ opk2) ∗ ((coroPtr + 0x4c8#64) ↦₆₄ opk3) ∗
          ((coroPtr + 0x4d0#64) ↦₆₄ opk4) ∗ ((coroPtr + 0x4d8#64) ↦₆₄ opk5) ∗
          ((coroPtr + 0x4e0#64) ↦₆₄ opk6) ∗ ((coroPtr + 0x4e8#64) ↦₆₄ opk7) ∗
          ((coroPtr + 0x4f1#64) ↦₈ 0#8) ∗ ((coroPtr + 0x3d8#64) ↦₆₄ kyb0) ∗
          ((coroPtr + 0x3e0#64) ↦₆₄ kyb1) ∗ ((coroPtr + 0x3e8#64) ↦₆₄ kyb2) ∗
          ((coroPtr + 0x3f0#64) ↦₆₄ kyb3) ∗ ((msgPtr + 0xa8#64) ↦₆₄ ekA0) ∗
          ((msgPtr + 0xb0#64) ↦₆₄ ekA1) ∗ ((msgPtr + 0xb8#64) ↦₆₄ ekA2) ∗
          ((msgPtr + 0xc0#64) ↦₆₄ ekA3) ∗ ((msgPtr + 0xc8#64) ↦₆₄ ikA0) ∗
          ((msgPtr + 0xd0#64) ↦₆₄ ikA1) ∗ ((msgPtr + 0xd8#64) ↦₆₄ ikA2) ∗
          ((msgPtr + 0xe0#64) ↦₆₄ ikA3) ∗ ((s.sp + 0x950#64) ↦₆₄ ik4) ∗
          ((s.sp + 0x958#64) ↦₆₄ ik5) ∗ ((s.sp + 0x960#64) ↦₆₄ ik6) ∗
          ((s.sp + 0x968#64) ↦₆₄ ik7) ∗ ((s.sp + 0xa90#64) ↦₆₄ spk0) ∗
          ((s.sp + 0xa98#64) ↦₆₄ spk1) ∗ ((s.sp + 0xaa0#64) ↦₆₄ spk2) ∗
          ((s.sp + 0xaa8#64) ↦₆₄ spk3) ∗ ((s.sp + 0xab0#64) ↦₆₄ spk4) ∗
          ((s.sp + 0xab8#64) ↦₆₄ spk5) ∗ ((s.sp + 0xac0#64) ↦₆₄ spk6) ∗
          ((s.sp + 0xac8#64) ↦₆₄ spk7) ∗ ((s.sp + 0x3e0#64) ↦₆₄ opk0) ∗
          ((s.sp + 0x3e8#64) ↦₆₄ opk1) ∗ ((s.sp + 0x3f0#64) ↦₆₄ opk2) ∗
          ((s.sp + 0x3f8#64) ↦₆₄ opk3) ∗ ((s.sp + 0x400#64) ↦₆₄ opk4) ∗
          ((s.sp + 0x408#64) ↦₆₄ opk5) ∗ ((s.sp + 0x410#64) ↦₆₄ opk6) ∗
          ((s.sp + 0x418#64) ↦₆₄ opk7) ∗ ((s.sp + 0x420#64) ↦₈ opk_b64) ∗
          ((s.sp + 0x560#64) ↦₆₄ kyb0) ∗ ((s.sp + 0x568#64) ↦₆₄ kyb1) ∗
          ((s.sp + 0x570#64) ↦₆₄ kyb2) ∗ ((s.sp + 0x578#64) ↦₆₄ kyb3) ∗
          ((s.sp + 0x6a0#64) ↦₆₄ ikA0) ∗ ((s.sp + 0x6a8#64) ↦₆₄ ikA1) ∗
          ((s.sp + 0x6b0#64) ↦₆₄ ikA2) ∗ ((s.sp + 0x6b8#64) ↦₆₄ ikA3) ∗
          ((s.sp + 0x7e0#64) ↦₆₄ ekA0) ∗ ((s.sp + 0x7e8#64) ↦₆₄ ekA1) ∗
          ((s.sp + 0x7f0#64) ↦₆₄ ekA2) ∗ ((s.sp + 0x7f8#64) ↦₆₄ ekA3)) ∧
        s1.sp = s.sp ∧ s1.trace = s.trace ∧ s1.readReg64 .x0 = coroPtr + 0x798#64 ∧
        s1.readReg64 .x1 = localAddrPtr ∧ s1.readReg64 .x2 = msgPtr + 0xc8#64 ∧
        s1.readReg64 .x3 = remoteAddrPtr ∧ s1.readReg64 .x19 = coroPtr ∧
        s1.readReg64 .x21 = s.readReg64 .x21 ∧ s1.readReg64 .x22 = s.sp + 0x370#64 ∧
        s1.readReg64 .x23 = s.sp + 0x930#64 ∧ s1.readReg64 .x24 = coroPtr + 0x398#64 ∧
        s1.readReg64 .x25 = s.readReg64 .x25 ∧ s1.readReg64 .x26 = s.readReg64 .x26 ∧
        s1.readReg64 .x27 = s.readReg64 .x27 ∧ s1.readReg64 .x28 = s.sp + 0xa90#64 ∧
        s1.readReg64 .x29 = s.readReg64 .x29 ∧ s1.readReg64 .x30 = stageP1EntryPlaced + 0x11d0#64 ∧
        calleeSavedVRegs s1 = calleeSavedVRegs s ∧
        VmPreserved s s1) := by
  dsimp only [stageP1ProgPlaced, stageP1EntryPlaced] at hpc ⊢
  have hx0' : s.readReg64 (Reg.gpr 0#5) = coroPtr + 0x798#64 := hx0
  have hx1' : s.readReg64 (Reg.gpr 1#5) = localAddrPtr := hx1
  have hx2' : s.readReg64 (Reg.gpr 2#5) = msgPtr + 0xc8#64 := hx2
  have hx3' : s.readReg64 (Reg.gpr 3#5) = remoteAddrPtr := hx3
  have hx8' : s.readReg64 (Reg.gpr 8#5) = opk_b64.zeroExtend 64 := hx8
  have hx9' : s.readReg64 (Reg.gpr 9#5) = msgPtr := hx9
  have hx10' : s.readReg64 (Reg.gpr 10#5) = coroPtr + 0x798#64 := hx10
  have hx19' : s.readReg64 (Reg.gpr 19#5) = coroPtr := hx19
  have hx22' : s.readReg64 (Reg.gpr 22#5) = s.sp + 0x370#64 := hx22
  have hx23' : s.readReg64 (Reg.gpr 23#5) = s.sp + 0x930#64 := hx23
  have hx24' : s.readReg64 (Reg.gpr 24#5) = coroPtr + 0x398#64 := hx24
  have hx28' : s.readReg64 (Reg.gpr 28#5) = s.sp + 0xa90#64 := hx28
  wp_steps_sync_pool_518 ext
    (libsignalSessionLib.resolve lsmpl "<libsignal_protocol::identity_key::IdentityKey>::is_same_account")
  refine SepWP.done _hpcm _hrunm ?_
  exact ⟨Entails.of_eq (by sep_ac_rfl), rfl, rfl,
    by simp_all [arm64_norm], by simp_all [arm64_norm], by simp_all [arm64_norm],
    by simp_all [arm64_norm], by simp_all [arm64_norm], by simp_all [arm64_norm],
    by simp_all [arm64_norm], by simp_all [arm64_norm], by simp_all [arm64_norm],
    by simp_all [arm64_norm], by simp_all [arm64_norm], by simp_all [arm64_norm],
    by simp_all [arm64_norm], by simp_all [arm64_norm], by simp_all [arm64_norm],
    by simp_all [arm64_norm], _hvm⟩

set_option maxHeartbeats 1000000 in
theorem p2_seg5d_ext_placed_wp [LibsignalPlacement]
    (ext : String → Option (State → State))
    (s : State) (coroPtr kyberPreKeyId64 sameAcctWord
    ik0 ik1 ik2 ik3 ik4 ik5 ik6 ik7 spk0 spk1 spk2 spk3 spk4 spk5 spk6 spk7
    opk0 opk1 opk2 opk3 opk4 opk5 opk6 opk7 kyb0 kyb1 kyb2 kyb3
    ikA0 ikA1 ikA2 ikA3 ekA0 ekA1 ekA2 ekA3
    c_658 c_660 c_668 c_670 c_678 c_680 c_688 c_690
    c_698 c_6a0 c_6a8 c_6b0 c_6b8 c_6c0 c_6c8 c_6d0
    c_6d8 c_6e0 c_6e8 c_6f0 c_6f8 c_700 c_708 c_710
    c_718 c_720 c_728 c_730 c_738
    c_740 c_748 c_750 c_758 c_760 c_768 c_770 c_778 : BitVec 64)
    (opk_b64 c_780 c_781 : BitVec 8)
    (hpc : s.pc = stageP1EntryPlaced + 0x11d0#64)
    (hrun : s.status = .Running) (_hsp_align : (s.sp &&& 15#64 == 0#64) = true)
    (hx0 : s.readReg64 .x0 = sameAcctWord) (hx19 : s.readReg64 .x19 = coroPtr)
    (hx21 : s.readReg64 .x21 = kyberPreKeyId64) (hx22 : s.readReg64 .x22 = s.sp + 0x370#64)
    (hx23 : s.readReg64 .x23 = s.sp + 0x930#64) (hx24 : s.readReg64 .x24 = coroPtr + 0x398#64)
    (hx28 : s.readReg64 .x28 = s.sp + 0xa90#64) :
    SepWP (stageP1ProgPlaced ext)
      (libsignalSessionLib.resolve lsmpl "libsignal_protocol::ratchet::initialize_bob_session") s
      (((s.sp + 0x930#64) ↦₆₄ ik0) ∗ ((s.sp + 0x938#64) ↦₆₄ ik1) ∗
       ((s.sp + 0x940#64) ↦₆₄ ik2) ∗ ((s.sp + 0x948#64) ↦₆₄ ik3) ∗
       ((s.sp + 0x950#64) ↦₆₄ ik4) ∗ ((s.sp + 0x958#64) ↦₆₄ ik5) ∗
       ((s.sp + 0x960#64) ↦₆₄ ik6) ∗ ((s.sp + 0x968#64) ↦₆₄ ik7) ∗
       ((s.sp + 0xa90#64) ↦₆₄ spk0) ∗ ((s.sp + 0xa98#64) ↦₆₄ spk1) ∗
       ((s.sp + 0xaa0#64) ↦₆₄ spk2) ∗ ((s.sp + 0xaa8#64) ↦₆₄ spk3) ∗
       ((s.sp + 0xab0#64) ↦₆₄ spk4) ∗ ((s.sp + 0xab8#64) ↦₆₄ spk5) ∗
       ((s.sp + 0xac0#64) ↦₆₄ spk6) ∗ ((s.sp + 0xac8#64) ↦₆₄ spk7) ∗
       ((s.sp + 0x3e0#64) ↦₆₄ opk0) ∗ ((s.sp + 0x3e8#64) ↦₆₄ opk1) ∗
       ((s.sp + 0x3f0#64) ↦₆₄ opk2) ∗ ((s.sp + 0x3f8#64) ↦₆₄ opk3) ∗
       ((s.sp + 0x400#64) ↦₆₄ opk4) ∗ ((s.sp + 0x408#64) ↦₆₄ opk5) ∗
       ((s.sp + 0x410#64) ↦₆₄ opk6) ∗ ((s.sp + 0x418#64) ↦₆₄ opk7) ∗
       ((s.sp + 0x420#64) ↦₈ opk_b64) ∗
       ((s.sp + 0x560#64) ↦₆₄ kyb0) ∗ ((s.sp + 0x568#64) ↦₆₄ kyb1) ∗
       ((s.sp + 0x570#64) ↦₆₄ kyb2) ∗ ((s.sp + 0x578#64) ↦₆₄ kyb3) ∗
       ((s.sp + 0x6a0#64) ↦₆₄ ikA0) ∗ ((s.sp + 0x6a8#64) ↦₆₄ ikA1) ∗
       ((s.sp + 0x6b0#64) ↦₆₄ ikA2) ∗ ((s.sp + 0x6b8#64) ↦₆₄ ikA3) ∗
       ((s.sp + 0x7e0#64) ↦₆₄ ekA0) ∗ ((s.sp + 0x7e8#64) ↦₆₄ ekA1) ∗
       ((s.sp + 0x7f0#64) ↦₆₄ ekA2) ∗ ((s.sp + 0x7f8#64) ↦₆₄ ekA3) ∗
       ((coroPtr + 0x658#64) ↦₆₄ c_658) ∗ ((coroPtr + 0x660#64) ↦₆₄ c_660) ∗
       ((coroPtr + 0x668#64) ↦₆₄ c_668) ∗ ((coroPtr + 0x670#64) ↦₆₄ c_670) ∗
       ((coroPtr + 0x678#64) ↦₆₄ c_678) ∗ ((coroPtr + 0x680#64) ↦₆₄ c_680) ∗
       ((coroPtr + 0x688#64) ↦₆₄ c_688) ∗ ((coroPtr + 0x690#64) ↦₆₄ c_690) ∗
       ((coroPtr + 0x698#64) ↦₆₄ c_698) ∗ ((coroPtr + 0x6a0#64) ↦₆₄ c_6a0) ∗
       ((coroPtr + 0x6a8#64) ↦₆₄ c_6a8) ∗ ((coroPtr + 0x6b0#64) ↦₆₄ c_6b0) ∗
       ((coroPtr + 0x6b8#64) ↦₆₄ c_6b8) ∗ ((coroPtr + 0x6c0#64) ↦₆₄ c_6c0) ∗
       ((coroPtr + 0x6c8#64) ↦₆₄ c_6c8) ∗ ((coroPtr + 0x6d0#64) ↦₆₄ c_6d0) ∗
       ((coroPtr + 0x6d8#64) ↦₆₄ c_6d8) ∗ ((coroPtr + 0x6e0#64) ↦₆₄ c_6e0) ∗
       ((coroPtr + 0x6e8#64) ↦₆₄ c_6e8) ∗ ((coroPtr + 0x6f0#64) ↦₆₄ c_6f0) ∗
       ((coroPtr + 0x6f8#64) ↦₆₄ c_6f8) ∗ ((coroPtr + 0x700#64) ↦₆₄ c_700) ∗
       ((coroPtr + 0x708#64) ↦₆₄ c_708) ∗ ((coroPtr + 0x710#64) ↦₆₄ c_710) ∗
       ((coroPtr + 0x718#64) ↦₆₄ c_718) ∗ ((coroPtr + 0x720#64) ↦₆₄ c_720) ∗
       ((coroPtr + 0x728#64) ↦₆₄ c_728) ∗ ((coroPtr + 0x730#64) ↦₆₄ c_730) ∗
       ((coroPtr + 0x738#64) ↦₆₄ c_738) ∗ ((coroPtr + 0x740#64) ↦₆₄ c_740) ∗
       ((coroPtr + 0x748#64) ↦₆₄ c_748) ∗ ((coroPtr + 0x750#64) ↦₆₄ c_750) ∗
       ((coroPtr + 0x758#64) ↦₆₄ c_758) ∗ ((coroPtr + 0x760#64) ↦₆₄ c_760) ∗
       ((coroPtr + 0x768#64) ↦₆₄ c_768) ∗ ((coroPtr + 0x770#64) ↦₆₄ c_770) ∗
       ((coroPtr + 0x778#64) ↦₆₄ c_778) ∗
       ((coroPtr + 0x780#64) ↦₈ c_780) ∗ ((coroPtr + 0x781#64) ↦₈ c_781))
      (fun s1 P_f =>
        (P_f ⊢
          ((s.sp + 0x930#64) ↦₆₄ ik0) ∗ ((s.sp + 0x938#64) ↦₆₄ ik1) ∗
          ((s.sp + 0x940#64) ↦₆₄ ik2) ∗ ((s.sp + 0x948#64) ↦₆₄ ik3) ∗
          ((s.sp + 0x950#64) ↦₆₄ ik4) ∗ ((s.sp + 0x958#64) ↦₆₄ ik5) ∗
          ((s.sp + 0x960#64) ↦₆₄ ik6) ∗ ((s.sp + 0x968#64) ↦₆₄ ik7) ∗
          ((s.sp + 0xa90#64) ↦₆₄ spk0) ∗ ((s.sp + 0xa98#64) ↦₆₄ spk1) ∗
          ((s.sp + 0xaa0#64) ↦₆₄ spk2) ∗ ((s.sp + 0xaa8#64) ↦₆₄ spk3) ∗
          ((s.sp + 0xab0#64) ↦₆₄ spk4) ∗ ((s.sp + 0xab8#64) ↦₆₄ spk5) ∗
          ((s.sp + 0xac0#64) ↦₆₄ spk6) ∗ ((s.sp + 0xac8#64) ↦₆₄ spk7) ∗
          ((s.sp + 0x3e0#64) ↦₆₄ opk0) ∗ ((s.sp + 0x3e8#64) ↦₆₄ opk1) ∗
          ((s.sp + 0x3f0#64) ↦₆₄ opk2) ∗ ((s.sp + 0x3f8#64) ↦₆₄ opk3) ∗
          ((s.sp + 0x400#64) ↦₆₄ opk4) ∗ ((s.sp + 0x408#64) ↦₆₄ opk5) ∗
          ((s.sp + 0x410#64) ↦₆₄ opk6) ∗ ((s.sp + 0x418#64) ↦₆₄ opk7) ∗
          ((s.sp + 0x420#64) ↦₈ opk_b64) ∗
          ((s.sp + 0x560#64) ↦₆₄ kyb0) ∗ ((s.sp + 0x568#64) ↦₆₄ kyb1) ∗
          ((s.sp + 0x570#64) ↦₆₄ kyb2) ∗ ((s.sp + 0x578#64) ↦₆₄ kyb3) ∗
          ((s.sp + 0x6a0#64) ↦₆₄ ikA0) ∗ ((s.sp + 0x6a8#64) ↦₆₄ ikA1) ∗
          ((s.sp + 0x6b0#64) ↦₆₄ ikA2) ∗ ((s.sp + 0x6b8#64) ↦₆₄ ikA3) ∗
          ((s.sp + 0x7e0#64) ↦₆₄ ekA0) ∗ ((s.sp + 0x7e8#64) ↦₆₄ ekA1) ∗
          ((s.sp + 0x7f0#64) ↦₆₄ ekA2) ∗ ((s.sp + 0x7f8#64) ↦₆₄ ekA3) ∗
          ((coroPtr + 0x658#64) ↦₆₄ ik0) ∗ ((coroPtr + 0x660#64) ↦₆₄ ik1) ∗
          ((coroPtr + 0x668#64) ↦₆₄ ik2) ∗ ((coroPtr + 0x670#64) ↦₆₄ ik3) ∗
          ((coroPtr + 0x678#64) ↦₆₄ ik4) ∗ ((coroPtr + 0x680#64) ↦₆₄ ik5) ∗
          ((coroPtr + 0x688#64) ↦₆₄ ik6) ∗ ((coroPtr + 0x690#64) ↦₆₄ ik7) ∗
          ((coroPtr + 0x698#64) ↦₆₄ spk0) ∗ ((coroPtr + 0x6a0#64) ↦₆₄ spk1) ∗
          ((coroPtr + 0x6a8#64) ↦₆₄ spk2) ∗ ((coroPtr + 0x6b0#64) ↦₆₄ spk3) ∗
          ((coroPtr + 0x6b8#64) ↦₆₄ spk4) ∗ ((coroPtr + 0x6c0#64) ↦₆₄ spk5) ∗
          ((coroPtr + 0x6c8#64) ↦₆₄ spk6) ∗ ((coroPtr + 0x6d0#64) ↦₆₄ spk7) ∗
          ((coroPtr + 0x6d8#64) ↦₆₄ ikA0) ∗ ((coroPtr + 0x6e0#64) ↦₆₄ ikA1) ∗
          ((coroPtr + 0x6e8#64) ↦₆₄ ikA2) ∗ ((coroPtr + 0x6f0#64) ↦₆₄ ikA3) ∗
          ((coroPtr + 0x6f8#64) ↦₆₄ ekA0) ∗ ((coroPtr + 0x700#64) ↦₆₄ ekA1) ∗
          ((coroPtr + 0x708#64) ↦₆₄ ekA2) ∗ ((coroPtr + 0x710#64) ↦₆₄ ekA3) ∗
          ((coroPtr + 0x718#64) ↦₆₄ kyb0) ∗ ((coroPtr + 0x720#64) ↦₆₄ kyb1) ∗
          ((coroPtr + 0x728#64) ↦₆₄ kyb2) ∗ ((coroPtr + 0x730#64) ↦₆₄ kyb3) ∗
          ((coroPtr + 0x738#64) ↦₆₄ kyberPreKeyId64) ∗ ((coroPtr + 0x740#64) ↦₆₄ opk0) ∗
          ((coroPtr + 0x748#64) ↦₆₄ opk1) ∗ ((coroPtr + 0x750#64) ↦₆₄ opk2) ∗
          ((coroPtr + 0x758#64) ↦₆₄ opk3) ∗ ((coroPtr + 0x760#64) ↦₆₄ opk4) ∗
          ((coroPtr + 0x768#64) ↦₆₄ opk5) ∗ ((coroPtr + 0x770#64) ↦₆₄ opk6) ∗
          ((coroPtr + 0x778#64) ↦₆₄ opk7) ∗
          ((coroPtr + 0x780#64) ↦₈ opk_b64) ∗ ((coroPtr + 0x781#64) ↦₈ sameAcctWord.setWidth 8)) ∧
        s1.sp = s.sp ∧ s1.trace = s.trace ∧
        s1.readReg64 .x0 = coroPtr + 0x658#64 ∧ s1.readReg64 .x1 = coroPtr + 0x398#64 ∧
        s1.readReg64 .x8 = s.sp + 0x3e0#64 ∧ s1.readReg64 .x19 = coroPtr ∧
        s1.readReg64 .x21 = kyberPreKeyId64 ∧ s1.readReg64 .x22 = s.sp + 0x370#64 ∧
        s1.readReg64 .x23 = s.sp + 0x930#64 ∧ s1.readReg64 .x24 = coroPtr + 0x398#64 ∧
        s1.readReg64 .x25 = s.readReg64 .x25 ∧ s1.readReg64 .x26 = s.readReg64 .x26 ∧
        s1.readReg64 .x27 = s.readReg64 .x27 ∧ s1.readReg64 .x28 = s.sp + 0xa90#64 ∧
        s1.readReg64 .x29 = s.readReg64 .x29 ∧ s1.readReg64 .x30 = stageP1EntryPlaced + 0x125c#64 ∧
        calleeSavedVRegs s1 = calleeSavedVRegs s ∧
        VmPreserved s s1) := by
  dsimp only [stageP1ProgPlaced, stageP1EntryPlaced] at hpc ⊢
  have hx0' : s.readReg64 (Reg.gpr 0#5) = sameAcctWord := hx0
  have hx19' : s.readReg64 (Reg.gpr 19#5) = coroPtr := hx19
  have hx21' : s.readReg64 (Reg.gpr 21#5) = kyberPreKeyId64 := hx21
  have hx22' : s.readReg64 (Reg.gpr 22#5) = s.sp + 0x370#64 := hx22
  have hx23' : s.readReg64 (Reg.gpr 23#5) = s.sp + 0x930#64 := hx23
  have hx24' : s.readReg64 (Reg.gpr 24#5) = coroPtr + 0x398#64 := hx24
  have hx28' : s.readReg64 (Reg.gpr 28#5) = s.sp + 0xa90#64 := hx28
  wp_steps_sync_pool_518 ext
    (libsignalSessionLib.resolve lsmpl "libsignal_protocol::ratchet::initialize_bob_session")
  refine SepWP.done _hpcm _hrunm ?_
  exact ⟨Entails.of_eq (by sep_ac_rfl), rfl, rfl,
    by simp_all [arm64_norm], by simp_all [arm64_norm], by simp_all [arm64_norm],
    by simp_all [arm64_norm], by simp_all [arm64_norm], by simp_all [arm64_norm],
    by simp_all [arm64_norm], by simp_all [arm64_norm], by simp_all [arm64_norm],
    by simp_all [arm64_norm], by simp_all [arm64_norm], by simp_all [arm64_norm],
    by simp_all [arm64_norm], by simp_all [arm64_norm], by simp_all [arm64_norm], _hvm⟩

end LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Kits.StageP2BlocksB5PlacedBudget
