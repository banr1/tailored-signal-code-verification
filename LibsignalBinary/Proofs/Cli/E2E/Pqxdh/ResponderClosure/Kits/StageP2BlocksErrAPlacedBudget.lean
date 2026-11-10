/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Kits.StageP2DefsPlacedBudget
public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Kits.StageP2BlocksErrAPlaced
public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Kits.StageP1StepsXExtPlacedBudgetAux
public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.Reloc.CliHandshakeCodeSymA
public import LibsignalBinary.Heap.IfaceBudget
public import LibsignalBinary.Heap.IfaceBudgetLemmas
public import LibsignalBinary.Heap.SpecBudget
public import LibsignalBinary.Proofs.Placed.BudgetVmSteps
public meta import LibsignalBinary.Proofs.Placed.BudgetVmSteps -- shake: keep
public meta import Lean.Elab.Tactic -- shake: keep
import LibsignalBinary.Proofs.Common.SharedHelpers
meta import LibsignalBinary.Proofs.Common.SharedHelpers -- shake: keep
import ProofLib.SepLogic.WP.Apply
meta import ProofLib.SepLogic.WP.Apply -- shake: keep
import Arm64.Trusted.Spec.Hoare
import Arm64.Trusted.Spec.SepLogic
import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Kits.StageP1Steps
import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Kits.StageP1UntrustedAux
import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Kits.StageP2BlocksErrA
import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderStore.Fetch
import LibsignalBinary.Proofs.E2E.InMem.HashbrownBin.IdentityKeyStoreFutures.SaveIdentity
import LibsignalBinary.Proofs.E2E.InMem.HashbrownBin.SessionStoreFutures.StoreCommon
import LibsignalBinary.Proofs.E2E.Pqxdh.ResponderStore.SessionRecordCallees
import LibsignalBinary.Proofs.E2E.Record.Serialization.SessionCloneAux.Base
import LibsignalBinary.Proofs.SpqrV1.Poly.EncoderFromPb.Defs
import LibsignalBinary.Proofs.SpqrV1.Poly.EncoderIntoPb.Defs
import LibsignalBinary.Proofs.SpqrV1.Prost.MessageEncode.Base
import LibsignalBinary.Proofs.SpqrV1.Prost.MessageMerge.PolyCommon
import LibsignalBinary.Proofs.TripleRatchet.GeneralizeEntry
import LibsignalBinary.Proofs.TripleRatchet.Keys.CreateChain
import LibsignalBinary.Proofs.TripleRatchet.ReceiveRatchet.From.Callees
import LibsignalBinary.Proofs.TripleRatchet.ReceiveRatchet.From.Step244

/-!
# Budget-Threaded Relocatable Stage P2 Basic Blocks — Shared Error Funnel and Arm 1

`RustCliAllocBudget M` / `VmPreserved` basic-block lemmas for the shared Stage P2 error funnel
(`+0x1648 → retAddr`) and Arm 1 (`+0x0f38 → +0x1648`) on Block `518`.
-/

@[expose] public section

set_option autoImplicit false

namespace LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Kits.StageP2BlocksErrAPlacedBudget

open Arm64 ProofLib ProofLib.ProgramReflection
open LibsignalBinary.Heap (
  AllocCallPreserved AllocCostModel BudgetLimits RustCliAllocBudget VmPreserved
  rustDeallocEvents
)
open LibsignalBinary.Heap.SpecBudget (withVmPreserved)
open LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Kits.StageP1StepsXExtPlacedBudgetAux (
  sepWP_seg_rebase_vm
)
open LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Kits.StageP2DefsPlacedBudget (
  StageP2ClosureHooksPlaced dropProcessPrekeyImplState1Spec
)
open LibsignalBinary.Proofs.Placed.BudgetVmSteps (sepWP_rebase_vmPreserved trapHooks)
open CryptoVerification (
  LibsignalPlacement lsLogFilterAddr lsRustDeallocSym
  ls_subroutine_ok_of_block lsmpl lsρ subroutine_ok_withLsCodeLoaded_of_plain
  withLsCodeLoaded
)
open CryptoVerification.RustHeap (allocHookStack)
open CryptoVerification.E2E.Pqxdh.ResponderClosure (preKeyRecordOut64At)
open CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.Kits (
  bfi_mask_lsr8_id bfi_mask_lsr8_of_lo32 cond_ne_adds64_of_ne_neg2_std3
  coro_268_split32 evalBitfield_bfi_lsr8 evalBitfield_bfi_lsr8_of_lo32
  extractLsb_hi_lo_append p2_cond_ne_adds64_of_ne_neg2 p2_cond_ne_adds64_of_ne_neg3
  realign_40 stageP1EntryPlaced stageP1ProgPlaced
)
open CryptoVerification.CliHandshake.Placed (blkPl_509 lsProg_509)
open CryptoVerification.CliHandshake.RespClosurePlaced (
  blkPC_518 blkPl_518 lsProg_518
)

set_option maxRecDepth 200000

attribute [local irreducible] Program.fetch Program.externAt? Program.fnOff
attribute [local arm64_norm] bv_sub_add_lit BitVec.add_assoc BitVec.toNat_zero
attribute [local simp, local wp_norm, local arm64_norm]
  bfi_mask_lsr8_id evalBitfield_bfi_lsr8
attribute [local simp] extractLsb_hi_lo_append

local elab "wp_steps_sync_pool_518_tac " tac:tacticSeq mid:term : tactic => do
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
      ($tac)
      refine SepWP.done (by simp_all +zetaDelta [arm64_norm]) (by simp_all +zetaDelta [arm64_norm])
        ⟨by first | rfl | simp only [wp_norm, arm64_norm], ?_⟩)))
    let rem ← Lean.Elab.Tactic.getGoals
    let [remId] := rem
      | throwError "wp_steps_sync_pool_518_tac: expected 1 continuation goal, got {rem.length}"
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

local macro "wp_steps_sync_pool_518 " _ext:term:max mid:term : tactic =>
  `(tactic| wp_steps_sync_pool_518_tac (wp_steps) $mid)

private theorem vmPreserved_trans_write_setPC {s sm s1 : State} {r : Reg} {v pc : BitVec 64}
    (h1 : VmPreserved s sm) (h2 : VmPreserved ((sm.writeReg64 r v).setPC pc) s1) :
    VmPreserved s s1 :=
  have h1' : VmPreserved s ((sm.writeReg64 r v).setPC pc) := by
    simp only [wp_norm, arm64_norm]; exact h1
  h1'.trans h2

private theorem subroutine_ok_withVmPreserved_intro {α : Type} {prog : Program} {entry : BitVec 64}
    {spec : Spec α}
    (h : ∀ (x : α) (R : SepProp) (s0 : State),
      s0.pc = entry → s0.status = .Running → s0.mem ⊨ spec.pre x s0 ∗ R → s0.spAligned →
      SepWP prog (s0.readReg64 .x30) s0 (spec.pre x s0)
        (fun sf P_f => VmPreserved s0 sf ∧
          ((sf.mem ⊨ P_f ∗ R → sf.mem ⊨ spec.post x s0 sf ∗ R) ∧
           sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf))) :
    subroutine_ok prog entry (withVmPreserved spec) := by
  refine subroutine_ok_of_sepWP fun x R s0 hpc hrun hpre hal => ⟨spec.pre x s0, R, hpre, ?_⟩
  refine SepWP.mono (h x R s0 hpc hrun hpre hal) fun sf P_f _ _ hpost => ?_
  rcases hpost with ⟨hvm, hq, hsp, hcs⟩
  refine ⟨fun hm => ?_, hsp, hcs⟩
  dsimp only [withVmPreserved]
  rw [sepConj_assoc, satisfies_pure_sepConj]
  exact ⟨hvm, hq hm⟩

/-- Block `509` (`core::ptr::drop_glue::<libsignal_protocol::session::process_prekey_impl::{closure#0}>`)
state `1` under `[LibsignalPlacement]`, lifted to `stageP1ProgPlaced ext` with `VmPreserved`. -/
theorem drop_process_prekey_impl_state1_ext_placed_ok [LibsignalPlacement]
    {ext : String → Option (State → State)} :
    subroutine_ok (stageP1ProgPlaced ext) (lsmpl.base 509)
      (withLsCodeLoaded lsmpl dropProcessPrekeyImplState1Spec) := by
  have h509 : subroutine_ok (lsProg_509 ext) (blkPl_509).base dropProcessPrekeyImplState1Spec := by
    unfold dropProcessPrekeyImplState1Spec
    apply subroutine_ok_withVmPreserved_intro
    intro ptr _R s0 hpc hrun _hpre _hsp_align
    dsimp only [CryptoVerification.E2E.Pqxdh.ResponderStore.dropProcessPrekeyImplState1Spec,
      lsProg_509] at *
    simp only [cells, sepConj_emp, sepExists_sepConj_right,
      BitVec.add_assoc, BitVec.reduceAdd] at *
    by_vm_steps (
      wp_pull_exists
      refine SepWP.pure_elim ?_
      rintro rfl
      wp_steps
      wp_done
    )
  exact ls_subroutine_ok_of_block (i := 518) (j := 509)
    (subroutine_ok_withLsCodeLoaded_of_plain h509) (by decide)

set_option maxHeartbeats 800000 in
/-- Segment P2.ErrTailA (`+0x1648 -> drop_process_prekey_impl_state1`) on `stageP1ProgPlaced ext`,
tracking all 6 `SignalProtocolError` words `(w0..w5)` and `VmPreserved`. -/
theorem p2_err_tail_a_ext_placed_wp [LibsignalPlacement] (ext : String → Option (State → State))
    (s : State) (coroPtr outPtr w0 w1 w2 w4 w5 r23 u_c8 : BitVec 64)
    (b_4f2 : BitVec 8)
    (herr_ne_neg3 : w0 ≠ 0xfffffffffffffffd#64)
    (hr23_lo : r23.extractLsb' 0 32 = w1.extractLsb' 0 32)
    (hpc : s.pc = stageP1EntryPlaced + 0x1648#64)
    (hrun : s.status = .Running) (_hsp_align : (s.sp &&& 15#64 == 0#64) = true)
    (hx10 : s.readReg64 .x10 = w2)
    (hx19 : s.readReg64 .x19 = coroPtr)
    (hx20 : s.readReg64 .x20 = w0)
    (hx21 : s.readReg64 .x21 = w4 >>> 8)
    (hx22 : s.readReg64 .x22 = w1 >>> 32)
    (hx23 : s.readReg64 .x23 = r23)
    (hx24 : s.readReg64 .x24 = w2 >>> 32)
    (hx26 : s.readReg64 .x26 = outPtr)
    (hx27 : s.readReg64 .x27 = w5) :
    SepWP (stageP1ProgPlaced ext) (lsmpl.base 509) s
      (((s.sp + 0x98#64) ↦₆₄ (coroPtr + 0x398#64)) ∗
       ((s.sp + 0xa0#64) ↦₆₄ (coroPtr + 0x4f2#64)) ∗
       ((s.sp + 0xc8#64) ↦₆₄ u_c8) ∗
       ((coroPtr + 0x4f2#64) ↦₈ b_4f2))
      (fun s1 P_f =>
        (P_f ⊢
          ((s.sp + 0x98#64) ↦₆₄ (coroPtr + 0x398#64)) ∗
          ((s.sp + 0xa0#64) ↦₆₄ (coroPtr + 0x4f2#64)) ∗
          ((s.sp + 0xc8#64) ↦₆₄ outPtr) ∗
          ((coroPtr + 0x4f2#64) ↦₈ 1#8)) ∧
        s1.sp = s.sp ∧
        s1.trace = s.trace ∧
        s1.readReg64 .x0 = coroPtr + 0x398#64 ∧
        s1.readReg64 .x19 = coroPtr ∧
        s1.readReg64 .x20 = w0 ∧
        s1.readReg64 .x21 = w4 >>> 8 ∧
        s1.readReg64 .x22 = w2 ∧
        s1.readReg64 .x23 = r23 ∧
        s1.readReg64 .x24 = w1 ∧
        s1.readReg64 .x25 = s.readReg64 .x25 ∧
        s1.readReg64 .x26 = outPtr ∧
        s1.readReg64 .x27 = w5 ∧
        s1.readReg64 .x28 = s.readReg64 .x28 ∧
        s1.readReg64 .x29 = s.readReg64 .x29 ∧
        s1.readReg64 .x30 = stageP1EntryPlaced + 0x1698#64 ∧
        calleeSavedVRegs s1 = calleeSavedVRegs s ∧
        VmPreserved s s1) := by
  have _hcond := p2_cond_ne_adds64_of_ne_neg3 herr_ne_neg3
  have hx10' : s.readReg64 (Reg.gpr 10#5) = w2 := hx10
  have hx19' : s.readReg64 (Reg.gpr 19#5) = coroPtr := hx19
  have hx20' : s.readReg64 (Reg.gpr 20#5) = w0 := hx20
  have hx21' : s.readReg64 (Reg.gpr 21#5) = w4 >>> 8 := hx21
  have hx22' : s.readReg64 (Reg.gpr 22#5) = w1 >>> 32 := hx22
  have hx23' : s.readReg64 (Reg.gpr 23#5) = r23 := hx23
  have hx24' : s.readReg64 (Reg.gpr 24#5) = w2 >>> 32 := hx24
  have hx26' : s.readReg64 (Reg.gpr 26#5) = outPtr := hx26
  have hx27' : s.readReg64 (Reg.gpr 27#5) = w5 := hx27
  dsimp only [stageP1ProgPlaced, stageP1EntryPlaced] at hpc ⊢
  wp_steps_sync_pool_518 ext (lsmpl.base 509)
  refine SepWP.done _hpcm _hrunm ?_
  refine ⟨Entails.of_eq (by sep_ac_rfl), rfl, rfl,
    by simp_all [arm64_norm], by simp_all [arm64_norm], by simp_all [arm64_norm],
    by simp_all [arm64_norm],
    by simp_all [arm64_norm]; clear * -; bv_bits,
    by simp_all [arm64_norm],
    by simp_all [arm64_norm]; clear * - hr23_lo; bv_bits,
    by simp_all [arm64_norm], by simp_all [arm64_norm], by simp_all [arm64_norm],
    by simp_all [arm64_norm], by simp_all [arm64_norm], by simp_all [arm64_norm],
    by simp_all [arm64_norm], _hvm⟩

set_option maxHeartbeats 1200000 in
/-- Segment P2.ErrTailB1 (`+0x1698 -> +0x1898`) on `stageP1ProgPlaced ext`, reconstructing the
exact 6-word `SignalProtocolError` `(w0, w1, w2, w3, w4, w5)` at `coroPtr + 0x250..0x280` and
`sp + 0xa90..0xac0` while preserving `VmPreserved`. -/
theorem p2_err_tail_b1_ext_placed_wp [LibsignalPlacement] (ext : String → Option (State → State))
    (s : State) (coroPtr outPtr w0 w1 w2 w3 w4 w5 r23
    u_250 u_258 u_260 u_268 u_270 u_278
    u_a90 u_a98 u_aa0 u_aa8 u_ab0 u_ab8 : BitVec 64)
    (b_390 : BitVec 8)
    (herr_ne_neg2 : w0 ≠ 0xfffffffffffffffe#64)
    (hr23_lo : r23.extractLsb' 0 32 = w1.extractLsb' 0 32)
    (hpc : s.pc = stageP1EntryPlaced + 0x1698#64)
    (hrun : s.status = .Running) (_hsp_align : (s.sp &&& 15#64 == 0#64) = true)
    (hx19 : s.readReg64 .x19 = coroPtr)
    (hx20 : s.readReg64 .x20 = w0)
    (hx21 : s.readReg64 .x21 = w4 >>> 8)
    (hx22 : s.readReg64 .x22 = w2)
    (hx23 : s.readReg64 .x23 = r23)
    (hx24 : s.readReg64 .x24 = w1)
    (hx25 : s.readReg64 .x25 = s.sp + 0x210#64)
    (hx27 : s.readReg64 .x27 = w5)
    (hx28 : s.readReg64 .x28 = s.sp + 0xa90#64) :
    SepWP (stageP1ProgPlaced ext) (stageP1EntryPlaced + 0x1898#64) s
      (((s.sp + 0xa8#64) ↦₆₄ w4) ∗
       ((s.sp + 0xc8#64) ↦₆₄ outPtr) ∗
       ((s.sp + 0xd0#64) ↦₆₄ w3) ∗
       (lsLogFilterAddr ↦₆₄ 0#64) ∗
       ((coroPtr + 0x250#64) ↦₆₄ u_250) ∗
       ((coroPtr + 0x258#64) ↦₆₄ u_258) ∗
       ((coroPtr + 0x260#64) ↦₆₄ u_260) ∗
       ((coroPtr + 0x268#64) ↦₆₄ u_268) ∗
       ((coroPtr + 0x270#64) ↦₆₄ u_270) ∗
       ((coroPtr + 0x278#64) ↦₆₄ u_278) ∗
       ((coroPtr + 0x390#64) ↦₈ b_390) ∗
       ((s.sp + 0xa90#64) ↦₆₄ u_a90) ∗
       ((s.sp + 0xa98#64) ↦₆₄ u_a98) ∗
       ((s.sp + 0xaa0#64) ↦₆₄ u_aa0) ∗
       ((s.sp + 0xaa8#64) ↦₆₄ u_aa8) ∗
       ((s.sp + 0xab0#64) ↦₆₄ u_ab0) ∗
       ((s.sp + 0xab8#64) ↦₆₄ u_ab8))
      (fun s1 P_f =>
        (P_f ⊢
          ((s.sp + 0xa8#64) ↦₆₄ w4) ∗
          ((s.sp + 0xc8#64) ↦₆₄ outPtr) ∗
          ((s.sp + 0xd0#64) ↦₆₄ w3) ∗
          (lsLogFilterAddr ↦₆₄ 0#64) ∗
          ((coroPtr + 0x250#64) ↦₆₄ w0) ∗
          ((coroPtr + 0x258#64) ↦₆₄ w1) ∗
          ((coroPtr + 0x260#64) ↦₆₄ w2) ∗
          ((coroPtr + 0x268#64) ↦₆₄ w3) ∗
          ((coroPtr + 0x270#64) ↦₆₄ w4) ∗
          ((coroPtr + 0x278#64) ↦₆₄ w5) ∗
          ((coroPtr + 0x390#64) ↦₈ 1#8) ∗
          ((s.sp + 0xa90#64) ↦₆₄ w0) ∗
          ((s.sp + 0xa98#64) ↦₃₂ w1.extractLsb' 0 32) ∗
          ((s.sp + 0xa9c#64) ↦₆₄ (w2.extractLsb' 0 32 ++ w1.extractLsb' 32 32)) ∗
          ((s.sp + 0xaa4#64) ↦₆₄ (w3.extractLsb' 0 32 ++ w2.extractLsb' 32 32)) ∗
          ((s.sp + 0xaac#64) ↦₆₄ (w4.extractLsb' 0 32 ++ w3.extractLsb' 32 32)) ∗
          ((s.sp + 0xab4#64) ↦₆₄ (w5.extractLsb' 0 32 ++ w4.extractLsb' 32 32)) ∗
          ((s.sp + 0xabc#64) ↦₃₂ w5.extractLsb' 32 32)) ∧
        s1.sp = s.sp ∧
        s1.trace = s.trace ∧
        s1.readReg64 .x19 = coroPtr ∧
        s1.readReg64 .x20 = w0 ∧
        s1.readReg64 .x21 = s.sp + 0x370#64 ∧
        s1.readReg64 .x25 = s.sp + 0x210#64 ∧
        s1.readReg64 .x26 = outPtr ∧
        s1.readReg64 .x28 = s.sp + 0xa90#64 ∧
        s1.readReg64 .x29 = s.readReg64 .x29 ∧
        s1.readReg64 .x30 = s.readReg64 .x30 ∧
        calleeSavedVRegs s1 = calleeSavedVRegs s ∧
        VmPreserved s s1) := by
  have _hcond := p2_cond_ne_adds64_of_ne_neg2 herr_ne_neg2
  have _hcond' : ConditionHolds CondCode.NE (addsPState64 w0 2#64) = true :=
    cond_ne_adds64_of_ne_neg2_std3 herr_ne_neg2
  have hbfi_mask_r23 : (r23 &&& 255#64 ||| (w1 >>> 8 &&& 72057594037927935#64) <<< 8) = w1 :=
    bfi_mask_lsr8_of_lo32 hr23_lo
  have hbfi_r23 : evalBitfield .W64 .BFM r23 (w1 >>> 8) 56 55 = w1 :=
    evalBitfield_bfi_lsr8_of_lo32 hr23_lo
  have hrealign_a98 := realign_40 (s.sp + 0xa98#64) w1 w2 w3 w4 w5
  try simp only [BitVec.add_assoc] at hrealign_a98
  try simp only [BitVec.reduceAdd] at hrealign_a98
  have hx19' : s.readReg64 (Reg.gpr 19#5) = coroPtr := hx19
  have hx20' : s.readReg64 (Reg.gpr 20#5) = w0 := hx20
  have hx21' : s.readReg64 (Reg.gpr 21#5) = w4 >>> 8 := hx21
  have hx22' : s.readReg64 (Reg.gpr 22#5) = w2 := hx22
  have hx23' : s.readReg64 (Reg.gpr 23#5) = r23 := hx23
  have hx24' : s.readReg64 (Reg.gpr 24#5) = w1 := hx24
  have hx25' : s.readReg64 (Reg.gpr 25#5) = s.sp + 0x210#64 := hx25
  have hx27' : s.readReg64 (Reg.gpr 27#5) = w5 := hx27
  have hx28' : s.readReg64 (Reg.gpr 28#5) = s.sp + 0xa90#64 := hx28
  dsimp only [stageP1ProgPlaced, lsProg_518, stageP1EntryPlaced, lsLogFilterAddr] at hpc ⊢
  wp_steps_sync_pool_518_tac (
    apply SepWP.fold (Entails.of_eq (coro_268_split32 coroPtr u_268)) (by sep_focus)
    wp_simp_pre [sepConj_assoc]
    wp_steps
    have hw3_hi : (w3 >>> 32).setWidth 32 = w3.extractLsb' 32 32 := by
      clear * -; bv_bits
    have hw3_lo : w3.setWidth 32 = w3.extractLsb' 0 32 := by
      clear * -; bv_bits
    wp_simp_pre [hbfi_r23, hbfi_mask_r23, hw3_hi, hw3_lo]
    apply SepWP.fold (Entails.of_eq (coro_268_split32 coroPtr w3).symm) (by sep_focus)
    wp_simp_pre [sepConj_assoc]
    wp_steps
  ) (blkPl_518.base + 6076#64)
  have hvm_mid := _hvm
  wp_step
  clear _hvm _hpcm _hrunm
  wp_steps_sync_pool_518_tac (
    wp_steps
    wp_simp_pre [hbfi_r23, hbfi_mask_r23]
    apply SepWP.fold (Entails.of_eq hrealign_a98) (by sep_focus)
    wp_simp_pre [sepConj_assoc]
  ) (blkPl_518.base + 6296#64)
  refine SepWP.done _hpcm _hrunm ?_
  refine ⟨Entails.of_eq (by sep_ac_rfl),
    by simp_all [arm64_norm], by simp_all [arm64_norm],
    by simp_all [arm64_norm], by simp_all [arm64_norm],
    by simp_all [arm64_norm], by simp_all [arm64_norm],
    by simp_all [arm64_norm], by simp_all [arm64_norm],
    by simp_all [arm64_norm], by simp_all [arm64_norm],
    by simp_all [arm64_norm],
    vmPreserved_trans_write_setPC hvm_mid _hvm⟩

set_option maxHeartbeats 800000 in
/-- Segment P2.ErrTailB2 (`+0x1898 -> +0x359c`) on `stageP1ProgPlaced ext` with `VmPreserved`. -/
theorem p2_err_tail_b2_ext_placed_wp [LibsignalPlacement] (ext : String → Option (State → State))
    (s : State) (coroPtr errTag outPtr
    v_a9c v_aa4 v_aac v_ab4
    u_370 u_378 u_380 u_388 : BitVec 64)
    (v_a98 v_abc u_390 : BitVec 32)
    (hpc : s.pc = stageP1EntryPlaced + 0x1898#64)
    (hrun : s.status = .Running) (_hsp_align : (s.sp &&& 15#64 == 0#64) = true)
    (hx19 : s.readReg64 .x19 = coroPtr) (hx21 : s.readReg64 .x21 = s.sp + 0x370#64)
    (hx25 : s.readReg64 .x25 = s.sp + 0x210#64) (hx26 : s.readReg64 .x26 = outPtr)
    (hx28 : s.readReg64 .x28 = s.sp + 0xa90#64) :
    SepWP (stageP1ProgPlaced ext) (stageP1EntryPlaced + 0x359c#64) s
      (((coroPtr + 0xf8#64) ↦₆₄ 0xffffffffffffffff#64) ∗
       ((s.sp + 0xa90#64) ↦₆₄ errTag) ∗
       ((s.sp + 0xa98#64) ↦₃₂ v_a98) ∗
       ((s.sp + 0xa9c#64) ↦₆₄ v_a9c) ∗
       ((s.sp + 0xaa4#64) ↦₆₄ v_aa4) ∗
       ((s.sp + 0xaac#64) ↦₆₄ v_aac) ∗
       ((s.sp + 0xab4#64) ↦₆₄ v_ab4) ∗
       ((s.sp + 0xabc#64) ↦₃₂ v_abc) ∗
       ((s.sp + 0x370#64) ↦₆₄ u_370) ∗
       ((s.sp + 0x378#64) ↦₆₄ u_378) ∗
       ((s.sp + 0x380#64) ↦₆₄ u_380) ∗
       ((s.sp + 0x388#64) ↦₆₄ u_388) ∗
       ((s.sp + 0x390#64) ↦₃₂ u_390))
      (fun s1 P_f =>
        (P_f ⊢
          ((coroPtr + 0xf8#64) ↦₆₄ 0xffffffffffffffff#64) ∗
          ((s.sp + 0xa90#64) ↦₆₄ errTag) ∗
          ((s.sp + 0xa98#64) ↦₃₂ v_a98) ∗
          ((s.sp + 0xa9c#64) ↦₆₄ v_a9c) ∗
          ((s.sp + 0xaa4#64) ↦₆₄ v_aa4) ∗
          ((s.sp + 0xaac#64) ↦₆₄ v_aac) ∗
          ((s.sp + 0xab4#64) ↦₆₄ v_ab4) ∗
          ((s.sp + 0xabc#64) ↦₃₂ v_abc) ∗
          ((s.sp + 0x370#64) ↦₆₄ v_a9c) ∗
          ((s.sp + 0x378#64) ↦₆₄ v_aa4) ∗
          ((s.sp + 0x380#64) ↦₆₄ v_aac) ∗
          ((s.sp + 0x388#64) ↦₆₄ v_ab4) ∗
          ((s.sp + 0x390#64) ↦₃₂ v_abc)) ∧
        s1.sp = s.sp ∧
        s1.trace = s.trace ∧
        s1.readReg64 .x19 = coroPtr ∧
        s1.readReg64 .x22 = v_a98.zeroExtend 64 ∧
        s1.readReg64 .x25 = s.sp + 0x210#64 ∧
        s1.readReg64 .x26 = outPtr ∧
        s1.readReg64 .x28 = errTag ∧
        s1.readReg64 .x29 = s.readReg64 .x29 ∧
        s1.readReg64 .x30 = s.readReg64 .x30 ∧
        calleeSavedVRegs s1 = calleeSavedVRegs s ∧
        VmPreserved s s1) := by
  have hx19' : s.readReg64 (Reg.gpr 19#5) = coroPtr := hx19
  have hx21' : s.readReg64 (Reg.gpr 21#5) = s.sp + 0x370#64 := hx21
  have hx25' : s.readReg64 (Reg.gpr 25#5) = s.sp + 0x210#64 := hx25
  have hx26' : s.readReg64 (Reg.gpr 26#5) = outPtr := hx26
  have hx28' : s.readReg64 (Reg.gpr 28#5) = s.sp + 0xa90#64 := hx28
  dsimp only [stageP1ProgPlaced, stageP1EntryPlaced] at hpc ⊢
  wp_steps_sync_pool_518 ext (blkPl_518.base + 13724#64)
  refine SepWP.done _hpcm _hrunm ?_
  exact ⟨Entails.of_eq (by sep_ac_rfl), rfl, rfl,
    by simp_all [arm64_norm], by simp_all [arm64_norm], by simp_all [arm64_norm],
    by simp_all [arm64_norm], by simp_all [arm64_norm], by simp_all [arm64_norm],
    by simp_all [arm64_norm], by simp_all [arm64_norm], _hvm⟩

set_option maxHeartbeats 800000 in
/-- Segment P3.ErrTailB (`+0x359c -> retAddr`) on `stageP1ProgPlaced ext` with `VmPreserved`. -/
theorem p3_err_tail_b_ext_placed_wp [LibsignalPlacement] (ext : String → Option (State → State))
    (s : State) (coroPtr outPtr errTag prevStatesPtr
    w_370 w_378 w_380 w_388
    u_ret0 u_ret0c u_ret14 u_ret1c u_ret24
    savedX19 savedX20 savedX21 savedX22 savedX23 savedX24
    savedX25 savedX26 savedX27 savedX28 savedX29 retAddr : BitVec 64)
    (w_22 w_390 u_ret08 u_ret2c : BitVec 32)
    (b_2c0 : BitVec 8)
    (hpc : s.pc = stageP1EntryPlaced + 0x359c#64)
    (hrun : s.status = .Running)
    (_hsp_align : (s.sp &&& 15#64 == 0#64) = true)
    (hx19 : s.readReg64 .x19 = coroPtr)
    (hx22 : s.readReg64 .x22 = w_22.zeroExtend 64)
    (hx25 : s.readReg64 .x25 = s.sp + 0x210#64)
    (hx26 : s.readReg64 .x26 = outPtr)
    (hx28 : s.readReg64 .x28 = errTag) :
    SepWP (stageP1ProgPlaced ext) retAddr s
      (((coroPtr + 0xe0#64) ↦₆₄ 0#64) ∗
       ((coroPtr + 0xe8#64) ↦₆₄ prevStatesPtr) ∗
       ((coroPtr + 0xf0#64) ↦₆₄ 0#64) ∗
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
        (P_f ⊢
          ((coroPtr + 0xe0#64) ↦₆₄ 0#64) ∗
          ((coroPtr + 0xe8#64) ↦₆₄ prevStatesPtr) ∗
          ((coroPtr + 0xf0#64) ↦₆₄ 0#64) ∗
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
        VmPreserved s s1) := by
  have hx19' : s.readReg64 (Reg.gpr 19#5) = coroPtr := hx19
  have hx22' : s.readReg64 (Reg.gpr 22#5) = w_22.zeroExtend 64 := hx22
  have hx25' : s.readReg64 (Reg.gpr 25#5) = s.sp + 0x210#64 := hx25
  have hx26' : s.readReg64 (Reg.gpr 26#5) = outPtr := hx26
  have hx28' : s.readReg64 (Reg.gpr 28#5) = errTag := hx28
  dsimp only [stageP1ProgPlaced, stageP1EntryPlaced] at hpc ⊢
  wp_steps_sync_pool_518 ext retAddr
  refine SepWP.done _hpcm _hrunm ?_
  exact ⟨Entails.of_eq (by sep_ac_rfl),
    by simp_all [arm64_norm], rfl,
    by simp_all [arm64_norm], by simp_all [arm64_norm], by simp_all [arm64_norm],
    by simp_all [arm64_norm], by simp_all [arm64_norm], by simp_all [arm64_norm],
    by simp_all [arm64_norm], by simp_all [arm64_norm], by simp_all [arm64_norm],
    by simp_all [arm64_norm], by simp_all [arm64_norm], by simp_all [arm64_norm],
    by simp_all [arm64_norm], _hvm⟩

set_option maxHeartbeats 800000 in
/-- Segment P2.Err1a (`+0x0f38 -> spkDropAddr`) on `stageP1ProgPlaced ext` with `VmPreserved`. -/
theorem p2_err1a_ext_placed_wp [LibsignalPlacement] (ext : String → Option (State → State))
    (s : State) (coroPtr spkFutPtr spkFutVt spkDropAddr errTag
    v_98 v_a0 v_b0 u_90 u_98 u_a0 u_b0 u_b8 u_d0
    u_3f0 u_3f8 u_400 u_408 u_410 u_418 : BitVec 64)
    (hdrop_nz : spkDropAddr ≠ 0#64)
    (hpc : s.pc = stageP1EntryPlaced + 0xf38#64)
    (hrun : s.status = .Running) (_hsp_align : (s.sp &&& 15#64 == 0#64) = true)
    (hx19 : s.readReg64 .x19 = coroPtr) (hx21 : s.readReg64 .x21 = v_b0)
    (hx23 : s.readReg64 .x23 = v_a0)
    (hx26 : s.readReg64 .x26 = v_98) :
    SepWP (stageP1ProgPlaced ext) spkDropAddr s
      (preKeyRecordOut64At (s.sp + 0x3e0#64) 0xffffffffffffffff#64 errTag u_3f0
         u_3f8 u_400 u_408 u_410 u_418 ∗
       ((coroPtr + 0x4f8#64) ↦₆₄ spkFutPtr) ∗
       ((coroPtr + 0x500#64) ↦₆₄ spkFutVt) ∗
       ((spkFutVt + 0x0#64) ↦₆₄ᵣ spkDropAddr) ∗
       ((s.sp + 0x90#64) ↦₆₄ u_90) ∗
       ((s.sp + 0x98#64) ↦₆₄ u_98) ∗
       ((s.sp + 0xa0#64) ↦₆₄ u_a0) ∗
       ((s.sp + 0xb0#64) ↦₆₄ u_b0) ∗
       ((s.sp + 0xb8#64) ↦₆₄ u_b8) ∗
       ((s.sp + 0xd0#64) ↦₆₄ u_d0))
      (fun s1 P_f =>
        (P_f ⊢
          preKeyRecordOut64At (s.sp + 0x3e0#64) 0xffffffffffffffff#64 errTag u_3f0
            u_3f8 u_400 u_408 u_410 u_418 ∗
          ((coroPtr + 0x4f8#64) ↦₆₄ spkFutPtr) ∗
          ((coroPtr + 0x500#64) ↦₆₄ spkFutVt) ∗
          ((spkFutVt + 0x0#64) ↦₆₄ᵣ spkDropAddr) ∗
          ((s.sp + 0x90#64) ↦₆₄ u_410) ∗
          ((s.sp + 0x98#64) ↦₆₄ v_98) ∗
          ((s.sp + 0xa0#64) ↦₆₄ v_a0) ∗
          ((s.sp + 0xb0#64) ↦₆₄ v_b0) ∗
          ((s.sp + 0xb8#64) ↦₆₄ u_3f8) ∗
          ((s.sp + 0xd0#64) ↦₆₄ u_400)) ∧
        s1.sp = s.sp ∧
        s1.trace = s.trace ∧
        s1.readReg64 .x0 = spkFutPtr ∧
        s1.readReg64 .x19 = coroPtr ∧
        s1.readReg64 .x20 = u_418 ∧
        s1.readReg64 .x21 = spkFutPtr ∧
        s1.readReg64 .x22 = errTag ∧
        s1.readReg64 .x23 = u_3f0 ∧
        s1.readReg64 .x24 = spkFutVt ∧
        s1.readReg64 .x25 = s.readReg64 .x25 ∧
        s1.readReg64 .x26 = u_408 ∧
        s1.readReg64 .x27 = s.readReg64 .x27 ∧
        s1.readReg64 .x28 = 0xffffffffffffffff#64 ∧
        s1.readReg64 .x29 = s.readReg64 .x29 ∧
        s1.readReg64 .x30 = stageP1EntryPlaced + 0xf98#64 ∧
        calleeSavedVRegs s1 = calleeSavedVRegs s ∧
        VmPreserved s s1) := by
  have _hdrop_beq : (spkDropAddr == 0#64) = false := beq_eq_false_iff_ne.mpr hdrop_nz
  have hx19' : s.readReg64 (Reg.gpr 19#5) = coroPtr := hx19
  have hx21' : s.readReg64 (Reg.gpr 21#5) = v_b0 := hx21
  have hx23' : s.readReg64 (Reg.gpr 23#5) = v_a0 := hx23
  have hx26' : s.readReg64 (Reg.gpr 26#5) = v_98 := hx26
  dsimp only [stageP1ProgPlaced, stageP1EntryPlaced, preKeyRecordOut64At] at hpc ⊢
  conv =>
    arg 4
    simp (config := { maxSteps := 1000000 }) only [
      BitVec.add_assoc, BitVec.reduceAdd, sepConj_assoc]
  wp_steps_sync_pool_518 ext spkDropAddr
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
/-- Segment P2.Err1b (`+0x0f98 -> +0x1648`, generic `spkBoxSize`) on `stageP1ProgPlaced ext`,
threading `A.pool lim st s -> A.pool lim (M.stepEvents (rustDeallocEvents spkBoxSize 8) st) s1`
across `rustCliDeallocBudgetSpec M A lim`. -/
theorem p2_err1b_hooks_placed_wp [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {st : M.σ}
    (ext : String → Option (State → State))
    (hH : StageP2ClosureHooksPlaced A lim ext)
    (s : State) (coroPtr spkFutPtr spkFutVt outPtr
    w0 w1 w2 w4 w5 v_c0 u_a8 u_c0 : BitVec 64)
    (spkBoxSize : Nat)
    (hbs_nz : BitVec.ofNat 64 spkBoxSize ≠ 0#64)
    (hbs_lt : spkBoxSize < 2 ^ 64)
    (hpc : s.pc = stageP1EntryPlaced + 0xf98#64)
    (hrun : s.status = .Running) (_hsp_align : (s.sp &&& 15#64 == 0#64) = true)
    (hx19 : s.readReg64 .x19 = coroPtr)
    (hx21 : s.readReg64 .x21 = spkFutPtr)
    (hx22 : s.readReg64 .x22 = w0)
    (hx23 : s.readReg64 .x23 = w1)
    (hx24 : s.readReg64 .x24 = spkFutVt)
    (hx26 : s.readReg64 .x26 = w4)
    (hx27 : s.readReg64 .x27 = v_c0)
    (hx28 : s.readReg64 .x28 = 0xffffffffffffffff#64) :
    SepWP (stageP1ProgPlaced ext) (stageP1EntryPlaced + 0x1648#64) s
      (((spkFutVt + 0x8#64) ↦₆₄ᵣ BitVec.ofNat 64 spkBoxSize) ∗
       ((spkFutVt + 0x10#64) ↦₆₄ᵣ 8#64) ∗
       A.live spkFutPtr spkBoxSize 8 ∗
       memRegion spkFutPtr spkBoxSize ∗
       A.pool lim st s ∗
       stackAt s.sp allocHookStack ∗
       ((s.sp + 0x90#64) ↦₆₄ w5) ∗
       ((s.sp + 0xa8#64) ↦₆₄ u_a8) ∗
       ((s.sp + 0xb8#64) ↦₆₄ w2) ∗
       ((s.sp + 0xc0#64) ↦₆₄ u_c0) ∗
       ((s.sp + 0xc8#64) ↦₆₄ outPtr))
      (fun s1 P_f =>
        let st' := M.stepEvents (rustDeallocEvents spkBoxSize 8) st
        (P_f ⊢
          ((spkFutVt + 0x8#64) ↦₆₄ᵣ BitVec.ofNat 64 spkBoxSize) ∗
          ((spkFutVt + 0x10#64) ↦₆₄ᵣ 8#64) ∗
          A.pool lim st' s1 ∗
          stackAt s.sp allocHookStack ∗
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
  have _hbs_beq : (BitVec.ofNat 64 spkBoxSize == 0#64) = false := beq_eq_false_iff_ne.mpr hbs_nz
  have _hbs_toNat : (BitVec.ofNat 64 spkBoxSize).toNat = spkBoxSize := Nat.mod_eq_of_lt hbs_lt
  have hx19' : s.readReg64 (Reg.gpr 19#5) = coroPtr := hx19
  have hx21' : s.readReg64 (Reg.gpr 21#5) = spkFutPtr := hx21
  have hx22' : s.readReg64 (Reg.gpr 22#5) = w0 := hx22
  have hx23' : s.readReg64 (Reg.gpr 23#5) = w1 := hx23
  have hx24' : s.readReg64 (Reg.gpr 24#5) = spkFutVt := hx24
  have hx26' : s.readReg64 (Reg.gpr 26#5) = w4 := hx26
  have hx27' : s.readReg64 (Reg.gpr 27#5) = v_c0 := hx27
  have hx28' : s.readReg64 (Reg.gpr 28#5) = 0xffffffffffffffff#64 := hx28
  dsimp only [stageP1ProgPlaced, stageP1EntryPlaced, lsRustDeallocSym] at hdealloc hpc ⊢
  wp_steps_sync_pool_518 ext (lsρ "_RNvCs1njKG4L9aB3_7___rustc14___rust_dealloc")
  clear _hvm _hpcm _hrunm
  wp_call hdealloc (spkFutPtr, spkBoxSize, 8, st)
  wp_steps_sync_pool_518 ext (blkPl_518.base + 5704#64)
  refine SepWP.done _hpcm _hrunm ?_
  refine ⟨Entails.of_eq (by sep_ac_rfl),
    by simp_all [arm64_norm], by simp_all [arm64_norm, AllocCallPreserved],
    by simp_all [arm64_norm], by simp_all [arm64_norm], by simp_all [arm64_norm],
    by simp_all [arm64_norm], by simp_all [arm64_norm], by simp_all [arm64_norm],
    by simp_all [arm64_norm], by simp_all [arm64_norm], by simp_all [arm64_norm],
    by simp_all [arm64_norm], by simp_all [arm64_norm], by simp_all [arm64_norm],
    by simp_all [arm64_norm], M.liveBytes_free_le 8 spkBoxSize st⟩

abbrev p2_err1b_4k_placed_wp := @p2_err1b_hooks_placed_wp
abbrev p2_err1b_ext_placed_wp := @p2_err1b_hooks_placed_wp

end LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Kits.StageP2BlocksErrAPlacedBudget
