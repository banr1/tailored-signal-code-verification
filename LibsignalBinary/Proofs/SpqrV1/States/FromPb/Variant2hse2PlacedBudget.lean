/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.Placed.BudgetPoolSync
public meta import LibsignalBinary.Proofs.Placed.BudgetPoolSync -- shake: keep
public import LibsignalBinary.Proofs.Placed.BudgetVmSteps
public meta import LibsignalBinary.Proofs.Placed.BudgetVmSteps -- shake: keep
public import LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant2aPlacedBudget
public import LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant2hsdPlacedBudget
public import LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant2hse2
public import LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant2hse2Placed
import LibsignalBinary.Proofs.Common.SharedHelpers
meta import LibsignalBinary.Proofs.Common.SharedHelpers -- shake: keep
import LibsignalBinary.Proofs.SpqrV1.Poly.DecoderPb.FromPbCopyPlacedBudget
import LibsignalBinary.Proofs.SpqrV1.States.FromPb.CodeSymFetch3Placed
import ProofLib.SepLogic.WP.Apply
import ProofLib.SepLogic.WPp

/-!
# `<spqr::v1::chunked::states::States>::from_pb`: Budget-Threaded Variant 2 (`HeaderSent`) — Part E2

Relocatable Block-`333` `<PolyEncoder>::from_pb` call (`+9096`), `FreeOnlyEvs` `Err` cleanup,
and `Ok` `PolyEncoder` stack relocation (`+9100 -> +9328`) under `RustCliAllocBudget M`.
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 400000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

namespace LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant2hse2PlacedBudget

open Arm64 Arm64.Obj ProofLib ProofLib.ProgramReflection SepProp
open CryptoVerification
  (LibsignalCodeLoaded LibsignalPlacement blkLib_eq_333 blkPC_333 blkPl_333 lsProg_333
   lsmpl lsρ withLsCodeLoaded withMemEq)
open CryptoVerification.LibsignalSpqrV1 (PolyEncoder PolynomialError)
open CryptoVerification.LibsignalTripleRatchet (sessionMemcpySpec)
open CryptoVerification.RustHeap (allocHookStack)
open CryptoVerification.SpqrV1.Alloc (spqrMemcpySym spqr_hook_ok_of_mem)
open CryptoVerification.SpqrV1.Drop (vecCapPtrDealloc)
open CryptoVerification.SpqrV1.Poly (resultPolyEncoderFromPbAt)
open CryptoVerification.SpqrV1.Poly.EncoderFromPb (encoderFromPbStack loByte unshiftWord)
open CryptoVerification.SpqrV1.States.FromPb
  (TraceCalleeSaved v2hse_unchunkedEkSentWordsAt v2hse_unchunkedEkSentWordsAt_entails_80
   v2hse2_1888_32_368_entails_memRegion_400 v2hse2_1888_tag_392_to_memRegion_400
   v2hse2_240_spill_entails_memRegion_24 v2hse2_bv_add_add_lit v2hse2_fsp1400_to_threeWords_mixed_rest
   v2hse2_fsp1400_to_unaligned16_rest v2hse2_fsp1896_split_rest v2hse2_fsp1896_to_threeWords_rest
   v2hse2_fsp1896_to_unaligned16_rest v2hse2_fsp1896_unsplit_rest v2hse2_fsp_1264_add_137
   v2hse2_fsp_1264_add_137_sext v2hse2_fsp_1392_add_32 v2hse2_fsp_1401_add_8 v2hse2_fsp_1897_add_8
   v2hse2_fsp_240_add_8 v2hse2_fsp_248_realign_rest v2hse2_fsp_248_realign_w24_rest
   v2hse2_fsp_248_unrealign_w24_rest v2hse2_fsp_add_255_sext
   v2hse2_memRegion_1392_400_split_32_368 v2hse2_memRegion_240_24_split v2hse2_polyEncoderTag
   v2hse2_polyEncoderTag_eq v2hse2_polyEncoderTag_sub_two_beq_zero
   v2hse2_resultPolyEncoder_err_entails_tag_392 v2hse2_stackAt_encoderFromPbStack_eq_allocHook
   v2hse2_x24_add_32 v2hse2_x25_add_105 v2hse2_x25_add_105_sext v2hse2_zext32_setWidth8
   v2hse2_zext64_setWidth32_setWidth8 v2hse2_zext64_setWidth8)
open CryptoVerification.SpqrV1.Unchunked
  (extractLsb'_0_64_append extractLsb'_64_64_append)
open LibsignalBinary.Heap
  (AllocCostModel AllocEvent BudgetLimits FreeOnlyEvs RustCliAllocBudget VmPreserved
   allocMemcpyVmSpec rustCliDeallocBudgetSpec)
open LibsignalBinary.Proofs.Placed.BudgetPoolSync (hooksException sepWP_seg_ls_vm)
open LibsignalBinary.Proofs.Placed.BudgetVmSteps (sepWP_rebase_vmPreserved)
open LibsignalBinary.Proofs.SpqrV1.Poly.DecoderPb.FromPbCopyPlacedBudget
  (sessionMemcpyVmAcpSpec subroutine_ok_sessionMemcpyVmAcp_of_allocMemcpyVm)
open LibsignalBinary.Proofs.SpqrV1.Poly.EncodeBytes.DefsBudget
  (isTotalTrapHooks_withPanics_vmTrapHooks sepWP_lsBlock_vmPreserved
   stripS_calleeSavedVRegs stripS_pc stripS_readReg64 stripS_sp stripS_status stripS_trace
   vmTrapHooks)
open LibsignalBinary.Proofs.SpqrV1.Poly.EncoderFromPb.DefsBudget (encoderFromPbSpec)
open LibsignalBinary.Proofs.SpqrV1.States.FromPb.DefsBudget
  (FromPbAllocHooksPlacedBudget spqrRustDeallocSym)
open LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant1bPlacedBudgetAux2 (seq_clean_st)
open LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant2aPlacedBudgetAux
  (EncoderFromPbPlacedOkExt FromPbAllocHooksBudget blk333_noSvc0 encoder_from_pb_ok_of_alloc_placed
   entails_pre_st withMemEq_of_withLsCodeLoaded)
open LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant2dPlacedBudget (blk333_safeVm)
open LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant2hscPlacedBudget
  (v2hsc_sub_ok_dealloc_of_dealloc_placed v2hsc_sub_ok_dealloc_of_placedHooks
   v2hsc_sub_ok_dealloc_placed)
open LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant2hsdPlacedBudget
  (v2hsd_cleanup_9112_to_9212_of_sub_placed)

attribute [local irreducible] Program.fetch Program.externAt? Program.fnOff
  CryptoVerification.blkPC_333
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero
  extractLsb'_0_64_append extractLsb'_64_64_append
attribute [local simp, local arm64_norm, local wp_norm]
  v2hse2_polyEncoderTag_sub_two_beq_zero
  v2hse2_x25_add_105_sext
  v2hse2_x25_add_105
  v2hse2_fsp_1897_add_8
  v2hse2_x24_add_32
  v2hse2_fsp_1392_add_32
  v2hse2_fsp_240_add_8
  v2hse2_fsp_add_255_sext
  v2hse2_fsp_1264_add_137_sext
  v2hse2_fsp_1264_add_137
  v2hse2_fsp_1401_add_8
  v2hse2_zext64_setWidth32_setWidth8
  v2hse2_zext32_setWidth8
  v2hse2_zext64_setWidth8

private theorem blkPl_333_base [LibsignalPlacement] :
    (blkPl_333).base = lsmpl.base 333 := rfl

local macro "wp_steps_sync_333 " mid:term : tactic => `(tactic| (
  apply sepWP_seg_ls_vm
    (Q := (blkPC_333).rebase (blkPl_333).base (hooksException _))
    blkLib_eq_333 blk333_noSvc0 (mid := $mid)
  intro _m_strip
  try rw [← blkPl_333_base]
  wp_steps
  refine ProofLib.SepWP.done (by wp_norm_lhs) (by wp_norm_lhs) fun _m_real _hnsp => ?_
  refine ProofLib.SepWP.transport_budgetPool
    (_hnsp.toVmPreserved (by first | wp_norm_lhs | simp only [wp_norm, arm64_norm]))
    (hnext := ?_)
))

local elab "by_vm_steps_nest " tac:Lean.Parser.Tactic.tacticSeq : tactic => do
  Lean.Elab.Tactic.evalTactic
    (← `(tactic| apply LibsignalBinary.Proofs.Placed.BudgetVmSteps.sepWP_rebase_vmPreserved))
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
      Lean.Meta.throwTacticEx `by_vm_steps_nest g m!"inner tactic left {rem.length} unsolved goal(s)"
    Lean.Elab.Tactic.setGoals savedGoals.tail!
    let prf1 ← Lean.instantiateMVars g1
    let prf2 := prf1.replace fun sub =>
      if sub.isAppOfArity ``Arm64.Program.withSvc 2 then some sub
      else if sub.eqv e1 then some e2
      else none
    g.assign prf2

private theorem seq_vm_cont {prog : Program} {mid tgt : BitVec 64} {s : State}
    {Pre : SepProp} {post : State → SepProp → Prop}
    (h : SepWP prog mid s Pre
      (fun sm Pm => VmPreserved s sm ∧ (VmPreserved s sm → SepWP prog tgt sm Pm post))) :
    SepWP prog tgt s Pre post :=
  SepWP.seq (Mid := fun sm Pm => VmPreserved s sm ∧ (VmPreserved s sm → SepWP prog tgt sm Pm post)) h
    (fun _ _ _ _ ⟨hvm, hk⟩ => hk hvm)

private theorem align_post_tp {prog : Program} {target : BitVec 64} {s0 s : State}
    {P P' : SepProp} {Q : State → Prop}
    (h : P ⊢ P')
    (hwp : SepWP prog target s P (fun sm Pm => sm.tpidrEl0 = s0.tpidrEl0 ∧ (Pm ⊢ P) ∧ Q sm)) :
    SepWP prog target s P (fun sm Pm => sm.tpidrEl0 = s0.tpidrEl0 ∧ (Pm ⊢ P') ∧ Q sm) :=
  SepWP.mono hwp fun _ _ _ _ ⟨htp, hPm, hQ⟩ => ⟨htp, Entails.trans hPm h, hQ⟩

/-! ## `<PolyEncoder>::from_pb` Call (`+9096 -> lsmpl.base 374` / `+9100`) -/

theorem v2hse2_sub_ok_encoder_from_pb_placed [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {ext : String → Option (State → State)}
    (henc : EncoderFromPbPlacedOkExt M A lim ext) :
    subroutine_ok (lsProg_333 (Rust.withPanics ext))
      (lsmpl.base 374)
      (withLsCodeLoaded lsmpl (encoderFromPbSpec M A lim)) :=
  henc

theorem v2hse2_sub_ok_encoder_from_pb_of_alloc_placed [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {ext : String → Option (State → State)}
    (hA : FromPbAllocHooksBudget M A lim ext) :
    subroutine_ok (lsProg_333 (Rust.withPanics ext))
      (lsmpl.base 374)
      (withLsCodeLoaded lsmpl (encoderFromPbSpec M A lim)) :=
  encoder_from_pb_ok_of_alloc_placed hA

theorem v2hse2_sub_ok_encoder_from_pb_mem_placed [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {ext : String → Option (State → State)} {m : Memory}
    (henc : EncoderFromPbPlacedOkExt M A lim ext)
    (hcl : LibsignalCodeLoaded lsmpl m) :
    subroutine_ok ((blkPC_333).rebase (blkPl_333).base (Rust.withPanics ext))
      (lsmpl.base 374)
      (withMemEq m (encoderFromPbSpec M A lim)) :=
  withMemEq_of_withLsCodeLoaded henc hcl

/-- `VmPreserved`-strengthened `bl <PolyEncoder>::from_pb` step at `+9096` to `lsmpl.base 374`. -/
theorem v2hse2_bl_encoder_9096_to_32996_placed [LibsignalPlacement]
    {ext : String → Option (State → State)}
    (s0 s1 : State) (fsp out d0 ca3 pbA : BitVec 64)
    (P : SepProp)
    (hpc1 : s1.pc = lsmpl.base 333 + 9096#64)
    (hrun1 : s1.status = .Running)
    (hsp1 : s1.sp = fsp)
    (hx0_1 : s1.readReg64 .x0 = fsp + 1888#64)
    (hx1_1 : s1.readReg64 .x1 = fsp + 1792#64)
    (hx19_1 : s1.readReg64 .x19 = out)
    (hx22_1 : s1.readReg64 .x22 = d0)
    (hx24_1 : s1.readReg64 .x24 = fsp + 1888#64)
    (hx25_1 : s1.readReg64 .x25 = fsp + 1792#64)
    (hx26_1 : s1.readReg64 .x26 = ca3)
    (hx27_1 : s1.readReg64 .x27 = pbA)
    (htr1 : TraceCalleeSaved s1 s0) :
    SepWP (lsProg_333 (Rust.withPanics ext))
      (lsmpl.base 374) s1 P
      (fun sm Pm =>
        (Pm ⊢ P) ∧
        VmPreserved s1 sm ∧
        sm.sp = fsp ∧
        sm.readReg64 .x0 = fsp + 1888#64 ∧
        sm.readReg64 .x1 = fsp + 1792#64 ∧
        sm.readReg64 .x19 = out ∧
        sm.readReg64 .x21 = s1.readReg64 .x21 ∧
        sm.readReg64 .x22 = d0 ∧
        sm.readReg64 .x23 = s1.readReg64 .x23 ∧
        sm.readReg64 .x24 = fsp + 1888#64 ∧
        sm.readReg64 .x25 = fsp + 1792#64 ∧
        sm.readReg64 .x26 = ca3 ∧
        sm.readReg64 .x27 = pbA ∧
        sm.readReg64 .x28 = s1.readReg64 .x28 ∧
        sm.readReg64 .x30 = lsmpl.base 333 + 9100#64 ∧
        TraceCalleeSaved sm s0) := by
  refine sepWP_lsBlock_vmPreserved blkLib_eq_333
    isTotalTrapHooks_withPanics_vmTrapHooks blk333_safeVm
    (Variant2hse2Placed.v2hse2_bl_encoder_9096_to_32996_placed
      (ext := vmTrapHooks) s0
      (ProofLib.stripS (ProofLib.progKeep (lsProg_333 (Rust.withPanics vmTrapHooks))) s1)
      fsp out d0 ca3 pbA P
      (by simpa using hpc1) (by simpa using hrun1) (by simpa using hsp1)
      (by simpa using hx0_1) (by simpa using hx1_1) (by simpa using hx19_1)
      (by simpa using hx22_1) (by simpa using hx24_1) (by simpa using hx25_1)
      (by simpa using hx26_1) (by simpa using hx27_1)
      ⟨by simpa using htr1.1, by simpa using htr1.2⟩)
    fun sm Pm hvm ⟨hPm, hsp_m, hx0_m, hx1_m, hx19_m, hx21_m, hx22_m, hx23_m,
        hx24_m, hx25_m, hx26_m, hx27_m, hx28_m, hx30_m, htr_m⟩ =>
      ⟨hPm, hvm, by simpa using hsp_m, by simpa using hx0_m, by simpa using hx1_m,
       by simpa using hx19_m, by simpa using hx21_m, by simpa using hx22_m,
       by simpa using hx23_m, by simpa using hx24_m, by simpa using hx25_m,
       by simpa using hx26_m, by simpa using hx27_m, by simpa using hx28_m,
       by simpa using hx30_m, ⟨by simpa using htr_m.1, by simpa using htr_m.2⟩⟩

theorem v2hse2_bl_encoder_9096_to_32996_placed_budget [LibsignalPlacement]
    {M : AllocCostModel} (A : RustCliAllocBudget M) (lim : BudgetLimits) (st : M.σ)
    {ext : String → Option (State → State)}
    (s0 s1 : State) (fsp out d0 ca3 pbA : BitVec 64)
    (P : SepProp)
    (hpc1 : s1.pc = lsmpl.base 333 + 9096#64)
    (hrun1 : s1.status = .Running)
    (hsp1 : s1.sp = fsp)
    (hx0_1 : s1.readReg64 .x0 = fsp + 1888#64)
    (hx1_1 : s1.readReg64 .x1 = fsp + 1792#64)
    (hx19_1 : s1.readReg64 .x19 = out)
    (hx22_1 : s1.readReg64 .x22 = d0)
    (hx24_1 : s1.readReg64 .x24 = fsp + 1888#64)
    (hx25_1 : s1.readReg64 .x25 = fsp + 1792#64)
    (hx26_1 : s1.readReg64 .x26 = ca3)
    (hx27_1 : s1.readReg64 .x27 = pbA)
    (htr1 : TraceCalleeSaved s1 s0) :
    SepWP (lsProg_333 (Rust.withPanics ext))
      (lsmpl.base 374) s1 (P ∗ A.pool lim st s1)
      (fun sm Pm =>
        (Pm ⊢ P ∗ A.pool lim st sm) ∧
        VmPreserved s1 sm ∧
        sm.sp = fsp ∧
        sm.readReg64 .x0 = fsp + 1888#64 ∧
        sm.readReg64 .x1 = fsp + 1792#64 ∧
        sm.readReg64 .x19 = out ∧
        sm.readReg64 .x21 = s1.readReg64 .x21 ∧
        sm.readReg64 .x22 = d0 ∧
        sm.readReg64 .x23 = s1.readReg64 .x23 ∧
        sm.readReg64 .x24 = fsp + 1888#64 ∧
        sm.readReg64 .x25 = fsp + 1792#64 ∧
        sm.readReg64 .x26 = ca3 ∧
        sm.readReg64 .x27 = pbA ∧
        sm.readReg64 .x28 = s1.readReg64 .x28 ∧
        sm.readReg64 .x30 = lsmpl.base 333 + 9100#64 ∧
        TraceCalleeSaved sm s0) := by
  have hwp := v2hse2_bl_encoder_9096_to_32996_placed (ext := ext)
    s0 s1 fsp out d0 ca3 pbA (P ∗ A.pool lim st s1)
    hpc1 hrun1 hsp1 hx0_1 hx1_1 hx19_1 hx22_1 hx24_1 hx25_1 hx26_1 hx27_1 htr1
  refine SepWP.mono hwp fun sm Pm _ _ ⟨hPm, hvm, hrest⟩ => ?_
  rw [← A.pool_of_vmPreserved hvm] at hPm
  exact ⟨hPm, hvm, hrest⟩

/-! ## `<PolyEncoder>::from_pb = Err` Cleanup (`+9100 -> +9112 -> +9212`) -/

/-- When `<PolyEncoder>::from_pb` returns `.error err` at `fsp + 1888`, steps `+9100 -> +9112`,
deallocates `(ca1, pa1)`, `(ca2, pa2)`, `(ca3, pa3)` via `v2hsd_cleanup_9112_to_9212_of_sub_placed`,
and reaches `+9212` under `FreeOnlyEvs`. -/
theorem v2hse2_enc_err_9100_to_9212_of_sub_placed [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {ext : String → Option (State → State)}
    (hdealloc_ok : subroutine_ok ((blkPC_333).rebase (blkPl_333).base (Rust.withPanics ext))
      (lsρ spqrRustDeallocSym) (rustCliDeallocBudgetSpec M A lim))
    (s0 s1 : State) (fsp out d0 ca1 pa1 la1 ca2 pa2 la2 ca3 pa3 la3 epoch : BitVec 64)
    (err : PolynomialError) (st : M.σ) (Frame : SepProp)
    (hfsp_align : (fsp &&& 15#64 == 0#64) = true)
    (hpc1 : s1.pc = lsmpl.base 333 + 9100#64)
    (hrun1 : s1.status = .Running)
    (hsp1 : s1.sp = fsp)
    (hx19_1 : s1.readReg64 .x19 = out)
    (hx22_1 : s1.readReg64 .x22 = d0)
    (hx26_1 : s1.readReg64 .x26 = ca3)
    (htr1 : TraceCalleeSaved s1 s0) :
    SepWP (lsProg_333 (Rust.withPanics ext))
      (lsmpl.base 333 + 9212#64) s1
      (stackAt fsp encoderFromPbStack ∗
        resultPolyEncoderFromPbAt A.repAlloc (fsp + 1888#64) (.error err) ∗
        ((fsp + 200#64) ↦₆₄ ca1) ∗
        ((fsp + 184#64) ↦₆₄ pa2) ∗
        ((fsp + 232#64) ↦₆₄ ca2) ∗
        ((fsp + 176#64) ↦₆₄ pa3) ∗
        v2hse_unchunkedEkSentWordsAt (fsp + 1264#64) ca1 pa1 la1 ca2 pa2 la2 ca3 pa3 la3 epoch ∗
        vecCapPtrDealloc A.repAlloc ca1 pa1 ∗
        vecCapPtrDealloc A.repAlloc ca2 pa2 ∗
        vecCapPtrDealloc A.repAlloc ca3 pa3 ∗
        A.pool lim st s1 ∗
        Frame)
      (fun sm Pm =>
        ∃ evs : List AllocEvent, FreeOnlyEvs evs ∧
        (Pm ⊢
          stackAt fsp encoderFromPbStack ∗
          memRegion (fsp + 1888#64) 400 ∗
          ((fsp + 200#64) ↦₆₄ ca1) ∗
          ((fsp + 184#64) ↦₆₄ pa2) ∗
          ((fsp + 232#64) ↦₆₄ ca2) ∗
          ((fsp + 176#64) ↦₆₄ pa3) ∗
          memRegion (fsp + 1264#64) 80 ∗
          A.pool lim (M.stepEvents evs st) sm ∗
          Frame) ∧
        sm.sp = fsp ∧
        sm.readReg64 .x19 = out ∧
        sm.readReg64 .x22 = d0 ∧
        TraceCalleeSaved sm s0) := by
  unfold v2hse_unchunkedEkSentWordsAt
  simp only [v2hse2_bv_add_add_lit, Nat.reduceAdd, BitVec.ofNat_eq_ofNat]
  refine SepWP.weaken_pre
    (sepConj_mono_right (sepConj_mono_left
      (v2hse2_resultPolyEncoder_err_entails_tag_392 A.repAlloc fsp err))) ?_
  refine seq_clean_st
    (mid := lsmpl.base 333 + 9112#64)
    (P_mid := fun sm =>
      stackAt fsp encoderFromPbStack ∗
      ((fsp + 200#64) ↦₆₄ ca1) ∗
      ((fsp + 1272#64) ↦₆₄ pa1) ∗
      ((fsp + 184#64) ↦₆₄ pa2) ∗
      ((fsp + 232#64) ↦₆₄ ca2) ∗
      ((fsp + 176#64) ↦₆₄ pa3) ∗
      vecCapPtrDealloc A.repAlloc ca1 pa1 ∗
      vecCapPtrDealloc A.repAlloc ca2 pa2 ∗
      vecCapPtrDealloc A.repAlloc ca3 pa3 ∗
      A.pool lim st sm ∗
      (memRegion (fsp + 1888#64) 400 ∗
       ((fsp + 1264#64) ↦₆₄ ca1) ∗
       ((fsp + 1280#64) ↦₆₄ la1) ∗
       ((fsp + 1288#64) ↦₆₄ ca2) ∗
       ((fsp + 1296#64) ↦₆₄ pa2) ∗
       ((fsp + 1304#64) ↦₆₄ la2) ∗
       ((fsp + 1312#64) ↦₆₄ ca3) ∗
       ((fsp + 1320#64) ↦₆₄ pa3) ∗
       ((fsp + 1328#64) ↦₆₄ la3) ∗
       ((fsp + 1336#64) ↦₆₄ epoch) ∗
       Frame))
    (Q := fun sm =>
      sm.sp = fsp ∧
      sm.readReg64 .x19 = out ∧
      sm.readReg64 .x22 = d0 ∧
      sm.readReg64 .x26 = ca3 ∧
      TraceCalleeSaved sm s0)
    ?_ ?_
  · change s1.pc = (blkPl_333).base + 9100#64 at hpc1
    change SepWP ((blkPC_333).rebase (blkPl_333).base (Rust.withPanics ext))
      ((blkPl_333).base + 9112#64) s1 _ _
    wp_simp_pre [sepConj_assoc]
    wp_steps_sync_333 ((blkPl_333).base + 9112#64)
    refine entails_pre_st ?_ ?_
    · intro sc hsc
      rw [← hsc]
      have h400 := v2hse2_1888_tag_392_to_memRegion_400 fsp 2#64
      refine Entails.trans (Entails.of_eq (show _ =
        (((fsp + 1888#64) ↦₆₄ 2#64) ∗ memRegion (fsp + 1896#64) 392) ∗
        (stackAt fsp encoderFromPbStack ∗
         ((fsp + 200#64) ↦₆₄ ca1) ∗
         ((fsp + 1272#64) ↦₆₄ pa1) ∗
         ((fsp + 184#64) ↦₆₄ pa2) ∗
         ((fsp + 232#64) ↦₆₄ ca2) ∗
         ((fsp + 176#64) ↦₆₄ pa3) ∗
         vecCapPtrDealloc A.repAlloc ca1 pa1 ∗
         vecCapPtrDealloc A.repAlloc ca2 pa2 ∗
         vecCapPtrDealloc A.repAlloc ca3 pa3 ∗
         A.pool lim st sc ∗
         ((fsp + 1264#64) ↦₆₄ ca1) ∗
         ((fsp + 1280#64) ↦₆₄ la1) ∗
         ((fsp + 1288#64) ↦₆₄ ca2) ∗
         ((fsp + 1296#64) ↦₆₄ pa2) ∗
         ((fsp + 1304#64) ↦₆₄ la2) ∗
         ((fsp + 1312#64) ↦₆₄ ca3) ∗
         ((fsp + 1320#64) ↦₆₄ pa3) ∗
         ((fsp + 1328#64) ↦₆₄ la3) ∗
         ((fsp + 1336#64) ↦₆₄ epoch) ∗ Frame) by sep_ac_rfl)) ?_
      exact Entails.trans (sepConj_mono_left h400) (Entails.of_eq (by sep_ac_rfl))
    · wp_done
  · intro s2 hpc2 hrun2 ⟨hsp2, hx19_2, hx22_2, hx26_2, htr2⟩
    have h9112 := v2hsd_cleanup_9112_to_9212_of_sub_placed hdealloc_ok
      s0 s2 fsp out d0 ca1 pa1 ca2 pa2 ca3 pa3 st
      (memRegion (fsp + 1888#64) 400 ∗
       ((fsp + 1264#64) ↦₆₄ ca1) ∗
       ((fsp + 1280#64) ↦₆₄ la1) ∗
       ((fsp + 1288#64) ↦₆₄ ca2) ∗
       ((fsp + 1296#64) ↦₆₄ pa2) ∗
       ((fsp + 1304#64) ↦₆₄ la2) ∗
       ((fsp + 1312#64) ↦₆₄ ca3) ∗
       ((fsp + 1320#64) ↦₆₄ pa3) ∗
       ((fsp + 1328#64) ↦₆₄ la3) ∗
       ((fsp + 1336#64) ↦₆₄ epoch) ∗
       Frame)
      hfsp_align hpc2 hrun2 hsp2 hx19_2 hx22_2 hx26_2 htr2
    refine SepWP.mono h9112 fun sm _Pm _ _ ⟨evs, hevs, hPm, hq⟩ => ⟨evs, hevs, Entails.trans hPm ?_, hq⟩
    have hm80 := v2hse_unchunkedEkSentWordsAt_entails_80 (fsp + 1264#64) ca1 pa1 la1 ca2 pa2 la2 ca3 pa3 la3 epoch
    unfold v2hse_unchunkedEkSentWordsAt at hm80
    simp only [v2hse2_bv_add_add_lit, Nat.reduceAdd, BitVec.ofNat_eq_ofNat] at hm80
    refine Entails.trans (Entails.of_eq (show _ =
      (((fsp + 1264#64) ↦₆₄ ca1) ∗
       ((fsp + 1272#64) ↦₆₄ pa1) ∗
       ((fsp + 1280#64) ↦₆₄ la1) ∗
       ((fsp + 1288#64) ↦₆₄ ca2) ∗
       ((fsp + 1296#64) ↦₆₄ pa2) ∗
       ((fsp + 1304#64) ↦₆₄ la2) ∗
       ((fsp + 1312#64) ↦₆₄ ca3) ∗
       ((fsp + 1320#64) ↦₆₄ pa3) ∗
       ((fsp + 1328#64) ↦₆₄ la3) ∗
       ((fsp + 1336#64) ↦₆₄ epoch)) ∗
      (stackAt fsp encoderFromPbStack ∗
       memRegion (fsp + 1888#64) 400 ∗
       ((fsp + 200#64) ↦₆₄ ca1) ∗
       ((fsp + 184#64) ↦₆₄ pa2) ∗
       ((fsp + 232#64) ↦₆₄ ca2) ∗
       ((fsp + 176#64) ↦₆₄ pa3) ∗
       A.pool lim (M.stepEvents evs st) sm ∗ Frame) by sep_ac_rfl)) ?_
    exact Entails.trans (sepConj_mono_left hm80) (Entails.of_eq (by sep_ac_rfl))

theorem v2hse2_enc_err_9100_to_9212_of_dealloc_placed [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {ext : String → Option (State → State)}
    (hdealloc : HookSat (Rust.withPanics ext) spqrRustDeallocSym (rustCliDeallocBudgetSpec M A lim))
    (s0 s1 : State) (fsp out d0 ca1 pa1 la1 ca2 pa2 la2 ca3 pa3 la3 epoch : BitVec 64)
    (err : PolynomialError) (st : M.σ) (Frame : SepProp)
    (hfsp_align : (fsp &&& 15#64 == 0#64) = true)
    (hpc1 : s1.pc = lsmpl.base 333 + 9100#64)
    (hrun1 : s1.status = .Running)
    (hsp1 : s1.sp = fsp)
    (hx19_1 : s1.readReg64 .x19 = out)
    (hx22_1 : s1.readReg64 .x22 = d0)
    (hx26_1 : s1.readReg64 .x26 = ca3)
    (htr1 : TraceCalleeSaved s1 s0) :
    SepWP (lsProg_333 (Rust.withPanics ext))
      (lsmpl.base 333 + 9212#64) s1
      (stackAt fsp encoderFromPbStack ∗
        resultPolyEncoderFromPbAt A.repAlloc (fsp + 1888#64) (.error err) ∗
        ((fsp + 200#64) ↦₆₄ ca1) ∗
        ((fsp + 184#64) ↦₆₄ pa2) ∗
        ((fsp + 232#64) ↦₆₄ ca2) ∗
        ((fsp + 176#64) ↦₆₄ pa3) ∗
        v2hse_unchunkedEkSentWordsAt (fsp + 1264#64) ca1 pa1 la1 ca2 pa2 la2 ca3 pa3 la3 epoch ∗
        vecCapPtrDealloc A.repAlloc ca1 pa1 ∗
        vecCapPtrDealloc A.repAlloc ca2 pa2 ∗
        vecCapPtrDealloc A.repAlloc ca3 pa3 ∗
        A.pool lim st s1 ∗
        Frame)
      (fun sm Pm =>
        ∃ evs : List AllocEvent, FreeOnlyEvs evs ∧
        (Pm ⊢
          stackAt fsp encoderFromPbStack ∗
          memRegion (fsp + 1888#64) 400 ∗
          ((fsp + 200#64) ↦₆₄ ca1) ∗
          ((fsp + 184#64) ↦₆₄ pa2) ∗
          ((fsp + 232#64) ↦₆₄ ca2) ∗
          ((fsp + 176#64) ↦₆₄ pa3) ∗
          memRegion (fsp + 1264#64) 80 ∗
          A.pool lim (M.stepEvents evs st) sm ∗
          Frame) ∧
        sm.sp = fsp ∧
        sm.readReg64 .x19 = out ∧
        sm.readReg64 .x22 = d0 ∧
        TraceCalleeSaved sm s0) :=
  v2hse2_enc_err_9100_to_9212_of_sub_placed
    (v2hsc_sub_ok_dealloc_of_dealloc_placed hdealloc)
    s0 s1 fsp out d0 ca1 pa1 la1 ca2 pa2 la2 ca3 pa3 la3 epoch err st Frame
    hfsp_align hpc1 hrun1 hsp1 hx19_1 hx22_1 hx26_1 htr1

theorem v2hse2_enc_err_9100_to_9212_of_placedHooks [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {ext : String → Option (State → State)}
    (hA : FromPbAllocHooksPlacedBudget M A lim ext)
    (s0 s1 : State) (fsp out d0 ca1 pa1 la1 ca2 pa2 la2 ca3 pa3 la3 epoch : BitVec 64)
    (err : PolynomialError) (st : M.σ) (Frame : SepProp)
    (hfsp_align : (fsp &&& 15#64 == 0#64) = true)
    (hpc1 : s1.pc = lsmpl.base 333 + 9100#64)
    (hrun1 : s1.status = .Running)
    (hsp1 : s1.sp = fsp)
    (hx19_1 : s1.readReg64 .x19 = out)
    (hx22_1 : s1.readReg64 .x22 = d0)
    (hx26_1 : s1.readReg64 .x26 = ca3)
    (htr1 : TraceCalleeSaved s1 s0) :
    SepWP (lsProg_333 (Rust.withPanics ext))
      (lsmpl.base 333 + 9212#64) s1
      (stackAt fsp encoderFromPbStack ∗
        resultPolyEncoderFromPbAt A.repAlloc (fsp + 1888#64) (.error err) ∗
        ((fsp + 200#64) ↦₆₄ ca1) ∗
        ((fsp + 184#64) ↦₆₄ pa2) ∗
        ((fsp + 232#64) ↦₆₄ ca2) ∗
        ((fsp + 176#64) ↦₆₄ pa3) ∗
        v2hse_unchunkedEkSentWordsAt (fsp + 1264#64) ca1 pa1 la1 ca2 pa2 la2 ca3 pa3 la3 epoch ∗
        vecCapPtrDealloc A.repAlloc ca1 pa1 ∗
        vecCapPtrDealloc A.repAlloc ca2 pa2 ∗
        vecCapPtrDealloc A.repAlloc ca3 pa3 ∗
        A.pool lim st s1 ∗
        Frame)
      (fun sm Pm =>
        ∃ evs : List AllocEvent, FreeOnlyEvs evs ∧
        (Pm ⊢
          stackAt fsp encoderFromPbStack ∗
          memRegion (fsp + 1888#64) 400 ∗
          ((fsp + 200#64) ↦₆₄ ca1) ∗
          ((fsp + 184#64) ↦₆₄ pa2) ∗
          ((fsp + 232#64) ↦₆₄ ca2) ∗
          ((fsp + 176#64) ↦₆₄ pa3) ∗
          memRegion (fsp + 1264#64) 80 ∗
          A.pool lim (M.stepEvents evs st) sm ∗
          Frame) ∧
        sm.sp = fsp ∧
        sm.readReg64 .x19 = out ∧
        sm.readReg64 .x22 = d0 ∧
        TraceCalleeSaved sm s0) :=
  v2hse2_enc_err_9100_to_9212_of_sub_placed
    (v2hsc_sub_ok_dealloc_of_placedHooks hA)
    s0 s1 fsp out d0 ca1 pa1 la1 ca2 pa2 la2 ca3 pa3 la3 epoch err st Frame
    hfsp_align hpc1 hrun1 hsp1 hx19_1 hx22_1 hx26_1 htr1

theorem v2hse2_enc_err_9100_to_9212_placed [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {ext : String → Option (State → State)}
    (hA : FromPbAllocHooksBudget M A lim ext)
    (s0 s1 : State) (fsp out d0 ca1 pa1 la1 ca2 pa2 la2 ca3 pa3 la3 epoch : BitVec 64)
    (err : PolynomialError) (st : M.σ) (Frame : SepProp)
    (hfsp_align : (fsp &&& 15#64 == 0#64) = true)
    (hpc1 : s1.pc = lsmpl.base 333 + 9100#64)
    (hrun1 : s1.status = .Running)
    (hsp1 : s1.sp = fsp)
    (hx19_1 : s1.readReg64 .x19 = out)
    (hx22_1 : s1.readReg64 .x22 = d0)
    (hx26_1 : s1.readReg64 .x26 = ca3)
    (htr1 : TraceCalleeSaved s1 s0) :
    SepWP (lsProg_333 (Rust.withPanics ext))
      (lsmpl.base 333 + 9212#64) s1
      (stackAt fsp encoderFromPbStack ∗
        resultPolyEncoderFromPbAt A.repAlloc (fsp + 1888#64) (.error err) ∗
        ((fsp + 200#64) ↦₆₄ ca1) ∗
        ((fsp + 184#64) ↦₆₄ pa2) ∗
        ((fsp + 232#64) ↦₆₄ ca2) ∗
        ((fsp + 176#64) ↦₆₄ pa3) ∗
        v2hse_unchunkedEkSentWordsAt (fsp + 1264#64) ca1 pa1 la1 ca2 pa2 la2 ca3 pa3 la3 epoch ∗
        vecCapPtrDealloc A.repAlloc ca1 pa1 ∗
        vecCapPtrDealloc A.repAlloc ca2 pa2 ∗
        vecCapPtrDealloc A.repAlloc ca3 pa3 ∗
        A.pool lim st s1 ∗
        Frame)
      (fun sm Pm =>
        ∃ evs : List AllocEvent, FreeOnlyEvs evs ∧
        (Pm ⊢
          stackAt fsp encoderFromPbStack ∗
          memRegion (fsp + 1888#64) 400 ∗
          ((fsp + 200#64) ↦₆₄ ca1) ∗
          ((fsp + 184#64) ↦₆₄ pa2) ∗
          ((fsp + 232#64) ↦₆₄ ca2) ∗
          ((fsp + 176#64) ↦₆₄ pa3) ∗
          memRegion (fsp + 1264#64) 80 ∗
          A.pool lim (M.stepEvents evs st) sm ∗
          Frame) ∧
        sm.sp = fsp ∧
        sm.readReg64 .x19 = out ∧
        sm.readReg64 .x22 = d0 ∧
        TraceCalleeSaved sm s0) :=
  v2hse2_enc_err_9100_to_9212_of_sub_placed
    (v2hsc_sub_ok_dealloc_placed hA)
    s0 s1 fsp out d0 ca1 pa1 la1 ca2 pa2 la2 ca3 pa3 la3 epoch err st Frame
    hfsp_align hpc1 hrun1 hsp1 hx19_1 hx22_1 hx26_1 htr1

/-! ## `<PolyEncoder>::from_pb = Ok(enc)` Move (`+9100 -> +9248 -> +9328`) -/

set_option maxHeartbeats 1200000 in
/-- `VmPreserved`-strengthened `<PolyEncoder>::from_pb = .ok enc` move (`+9100 -> +9248 -> +9328`)
under `allocMemcpyVmSpec`. -/
theorem v2hse2_enc_ok_move_9100_to_9328_of_memcpy_placed [LibsignalPlacement]
    {ext : String → Option (State → State)}
    (hmemcpy_ok : subroutine_ok (lsProg_333 (Rust.withPanics ext))
      (lsρ spqrMemcpySym) allocMemcpyVmSpec)
    (s0 s1 : State) (fsp out d0 ca3 pbA slot56_old w8 w16 w24 : BitVec 64)
    (tail368 : { l : List (BitVec 8) // l.length = 368 })
    (enc : PolyEncoder) (Frame : SepProp)
    (hfsp_align : (fsp &&& 15#64 == 0#64) = true)
    (hpc1 : s1.pc = lsmpl.base 333 + 9100#64)
    (hrun1 : s1.status = .Running)
    (hsp1 : s1.sp = fsp)
    (hx19_1 : s1.readReg64 .x19 = out)
    (hx22_1 : s1.readReg64 .x22 = d0)
    (hx24_1 : s1.readReg64 .x24 = fsp + 1888#64)
    (hx25_1 : s1.readReg64 .x25 = fsp + 1792#64)
    (hx26_1 : s1.readReg64 .x26 = ca3)
    (hx27_1 : s1.readReg64 .x27 = pbA)
    (htr1 : TraceCalleeSaved s1 s0) :
    SepWP (lsProg_333 (Rust.withPanics ext))
      (lsmpl.base 333 + 9328#64) s1
      (stackAt fsp encoderFromPbStack ∗
        ((fsp + 1888#64) ↦₆₄ v2hse2_polyEncoderTag enc) ∗
        ((fsp + 1896#64) ↦₆₄ w8) ∗
        ((fsp + 1904#64) ↦₆₄ w16) ∗
        ((fsp + 1912#64) ↦₆₄ w24) ∗
        ((fsp + 1920#64) ↦ₛ tail368.val) ∗
        memRegion (fsp + 1392#64) 400 ∗
        memRegion (fsp + 240#64) 24 ∗
        ((fsp + 56#64) ↦₆₄ slot56_old) ∗
        Frame)
      (fun sm Pm =>
        (Pm ⊢
          stackAt fsp encoderFromPbStack ∗
          memRegion (fsp + 1888#64) 400 ∗
          ((fsp + 1392#64) ↦₆₄ v2hse2_polyEncoderTag enc) ∗
          ((fsp + 1400#64) ↦₆₄ w8) ∗
          ((fsp + 1408#64) ↦₆₄ w16) ∗
          ((fsp + 1416#64) ↦₆₄ w24) ∗
          ((fsp + 1424#64) ↦ₛ tail368.val) ∗
          memRegion (fsp + 240#64) 24 ∗
          ((fsp + 56#64) ↦₆₄ v2hse2_polyEncoderTag enc) ∗
          Frame) ∧
        VmPreserved s1 sm ∧
        sm.sp = fsp ∧
        sm.readReg64 .x19 = out ∧
        sm.readReg64 .x20 = (loByte w8).zeroExtend 64 ∧
        sm.readReg64 .x21 = s1.readReg64 .x21 ∧
        sm.readReg64 .x22 = d0 ∧
        sm.readReg64 .x23 = fsp + 1392#64 ∧
        sm.readReg64 .x24 = fsp + 1888#64 ∧
        sm.readReg64 .x25 = fsp + 1792#64 ∧
        sm.readReg64 .x26 = ca3 ∧
        sm.readReg64 .x27 = pbA ∧
        sm.readReg64 .x28 = s1.readReg64 .x28 ∧
        sm.pstate = addsPState64 d0 1#64 ∧
        TraceCalleeSaved sm s0) := by
  subst hsp1
  have hmemcpy : subroutine_ok ((blkPC_333).rebase (blkPl_333).base (Rust.withPanics ext))
      (lsρ spqrMemcpySym) (sessionMemcpyVmAcpSpec allocHookStack) :=
    subroutine_ok_sessionMemcpyVmAcp_of_allocMemcpyVm allocHookStack hmemcpy_ok
  simp only [sessionMemcpyVmAcpSpec, sessionMemcpySpec, allocHookStack] at hmemcpy
  wp_conv_pre =>
    rw [v2hse2_stackAt_encoderFromPbStack_eq_allocHook s1.sp]
  refine SepWP.weaken_pre
    (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
      (sepConj_mono_right (sepConj_mono_right
        (sepConj_mono (v2hse2_memRegion_1392_400_split_32_368 s1.sp)
          (sepConj_mono_left (v2hse2_memRegion_240_24_split s1.sp))))))))) ?_
  wp_simp_pre [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
  apply ProofLib.SepWP.exists_left; intro d16
  apply ProofLib.SepWP.exists_left; intro d8
  apply ProofLib.SepWP.exists_left; intro d0_spill
  apply ProofLib.SepWP.exists_left; intro e24
  apply ProofLib.SepWP.exists_left; intro e16
  apply ProofLib.SepWP.exists_left; intro e8
  apply ProofLib.SepWP.exists_left; intro e0
  have hcond : (v2hse2_polyEncoderTag enc != 2#64) = true := by
    rcases v2hse2_polyEncoderTag_eq enc with h | h <;> rw [h] <;> rfl
  change s1.pc = (blkPl_333).base + 9100#64 at hpc1
  change SepWP ((blkPC_333).rebase (blkPl_333).base (Rust.withPanics ext))
    ((blkPl_333).base + 9328#64) s1 _ _
  refine seq_vm_cont (mid := lsρ spqrMemcpySym) ?_
  by_vm_steps_nest (
    wp_simp_pre only [v2hse2_fsp1896_to_unaligned16_rest, sepConj_assoc]
    iterate 4 wp_step
    wp_simp_pre only [v2hse2_fsp1896_to_threeWords_rest, sepConj_assoc]
    iterate 2 wp_step
    wp_simp_pre only [v2hse2_fsp1896_split_rest, sepConj_assoc]
    wp_step
    wp_simp_pre only [v2hse2_fsp1896_unsplit_rest, sepConj_assoc]
    iterate 4 wp_step
    wp_simp_pre only [v2hse2_fsp_248_realign_rest, sepConj_assoc]
    iterate 3 wp_step
    refine SepWP.done
      (by dsimp only [blkPl_333, Obj.MultiPlacedLib.blockPlacement, lsρ, spqrMemcpySym]; wp_norm_lhs)
      (by wp_norm_lhs)
      ⟨by simp only [wp_norm, arm64_norm], fun hvm1 => ?_⟩
    have hlen368 : (368 : Nat) = tail368.val.length := tail368.property.symm
    wp_simp_pre [hlen368, sepConj_assoc]
    wp_call hmemcpy (s1.sp + 1424#64, s1.sp + 1920#64, tail368.val)
    have hvm_mc : VmPreserved s1 sf := hvm1.trans ‹VmPreserved _ sf›
    refine SepWP.mono
      (post := fun sm Pm =>
        VmPreserved sf sm ∧
        (Pm ⊢
          stackAt s1.sp encoderFromPbStack ∗
          memRegion (s1.sp + 1888#64) 400 ∗
          ((s1.sp + 1392#64) ↦₆₄ v2hse2_polyEncoderTag enc) ∗
          ((s1.sp + 1400#64) ↦₆₄ w8) ∗
          ((s1.sp + 1408#64) ↦₆₄ w16) ∗
          ((s1.sp + 1416#64) ↦₆₄ w24) ∗
          ((s1.sp + 1424#64) ↦ₛ tail368.val) ∗
          memRegion (s1.sp + 240#64) 24 ∗
          ((s1.sp + 56#64) ↦₆₄ v2hse2_polyEncoderTag enc) ∗
          Frame) ∧
        sm.sp = s1.sp ∧
        sm.readReg64 .x19 = out ∧
        sm.readReg64 .x20 = (loByte w8).zeroExtend 64 ∧
        sm.readReg64 .x21 = s1.readReg64 .x21 ∧
        sm.readReg64 .x22 = d0 ∧
        sm.readReg64 .x23 = s1.sp + 1392#64 ∧
        sm.readReg64 .x24 = s1.sp + 1888#64 ∧
        sm.readReg64 .x25 = s1.sp + 1792#64 ∧
        sm.readReg64 .x26 = ca3 ∧
        sm.readReg64 .x27 = pbA ∧
        sm.readReg64 .x28 = s1.readReg64 .x28 ∧
        sm.pstate = addsPState64 d0 1#64 ∧
        TraceCalleeSaved sm s0)
      ?_ (fun sm Pm _ _ ⟨hvm2, hPm, hregs⟩ => ⟨hPm, hvm_mc.trans hvm2, hregs⟩)
    by_vm_steps (
      wp_step
      wp_simp_pre only [v2hse2_fsp_248_unrealign_w24_rest, sepConj_assoc]
      wp_step
      wp_simp_pre only [v2hse2_fsp1400_to_unaligned16_rest, sepConj_assoc]
      iterate 4 wp_step
      wp_simp_pre only [v2hse2_fsp_248_realign_w24_rest, sepConj_assoc]
      wp_step
      wp_step
      wp_simp_pre only [v2hse2_fsp1400_to_threeWords_mixed_rest, sepConj_assoc]
      wp_step
      wp_simp_pre only [v2hse2_fsp_248_unrealign_w24_rest, sepConj_assoc]
      refine align_post_tp ?_ ?_
      · have h1888_400 := v2hse2_1888_32_368_entails_memRegion_400 s1.sp
          (v2hse2_polyEncoderTag enc) w8 w16 w24 tail368
        have h240_24 := v2hse2_240_spill_entails_memRegion_24 s1.sp
          (unshiftWord w8 (loByte w16)) (unshiftWord w16 (loByte w24))
          (w24 >>> 8) ((d16 >>> 56).setWidth 8)
        refine Entails.trans (Entails.of_eq (show _ =
          (memRegion (s1.sp - 4096#64) 4096 ∗ memRegion (s1.sp - 5152#64) 1056) ∗
          (((s1.sp + 1888#64) ↦₆₄ v2hse2_polyEncoderTag enc) ∗
           ((s1.sp + 1896#64) ↦₆₄ w8) ∗ ((s1.sp + 1904#64) ↦₆₄ w16) ∗
           ((s1.sp + 1912#64) ↦₆₄ w24) ∗ ((s1.sp + 1920#64) ↦ₛ tail368.val)) ∗
          ((s1.sp + 1392#64) ↦₆₄ v2hse2_polyEncoderTag enc) ∗
          ((s1.sp + 1400#64) ↦₆₄ w8) ∗ ((s1.sp + 1408#64) ↦₆₄ w16) ∗
          ((s1.sp + 1416#64) ↦₆₄ w24) ∗ ((s1.sp + 1424#64) ↦ₛ tail368.val) ∗
          (((s1.sp + 240#64) ↦₆₄ unshiftWord w8 (loByte w16)) ∗
           ((s1.sp + 248#64) ↦₆₄ unshiftWord w16 (loByte w24)) ∗
           (((s1.sp + 256#64) ↦ₛ CryptoVerification.SpqrV1.Poly.EncoderFromPb.loBytes7 (w24 >>> 8)) ∗
            ((s1.sp + 263#64) ↦₈ (d16 >>> 56).setWidth 8))) ∗
          ((s1.sp + 56#64) ↦₆₄ v2hse2_polyEncoderTag enc) ∗
          Frame by sep_ac_rfl)) ?_
        rw [← v2hse2_stackAt_encoderFromPbStack_eq_allocHook s1.sp]
        exact sepConj_mono (Entails.refl _) (sepConj_mono h1888_400
          (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
            (sepConj_mono_right (sepConj_mono h240_24 (Entails.refl _))))))))
      · wp_done
    )
  )

theorem v2hse2_enc_ok_move_9100_to_9328_of_placedHooks [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {ext : String → Option (State → State)}
    (hA : FromPbAllocHooksPlacedBudget M A lim ext)
    (s0 s1 : State) (fsp out d0 ca3 pbA slot56_old w8 w16 w24 : BitVec 64)
    (tail368 : { l : List (BitVec 8) // l.length = 368 })
    (enc : PolyEncoder) (Frame : SepProp)
    (hfsp_align : (fsp &&& 15#64 == 0#64) = true)
    (hpc1 : s1.pc = lsmpl.base 333 + 9100#64)
    (hrun1 : s1.status = .Running)
    (hsp1 : s1.sp = fsp)
    (hx19_1 : s1.readReg64 .x19 = out)
    (hx22_1 : s1.readReg64 .x22 = d0)
    (hx24_1 : s1.readReg64 .x24 = fsp + 1888#64)
    (hx25_1 : s1.readReg64 .x25 = fsp + 1792#64)
    (hx26_1 : s1.readReg64 .x26 = ca3)
    (hx27_1 : s1.readReg64 .x27 = pbA)
    (htr1 : TraceCalleeSaved s1 s0) :
    SepWP (lsProg_333 (Rust.withPanics ext))
      (lsmpl.base 333 + 9328#64) s1
      (stackAt fsp encoderFromPbStack ∗
        ((fsp + 1888#64) ↦₆₄ v2hse2_polyEncoderTag enc) ∗
        ((fsp + 1896#64) ↦₆₄ w8) ∗
        ((fsp + 1904#64) ↦₆₄ w16) ∗
        ((fsp + 1912#64) ↦₆₄ w24) ∗
        ((fsp + 1920#64) ↦ₛ tail368.val) ∗
        memRegion (fsp + 1392#64) 400 ∗
        memRegion (fsp + 240#64) 24 ∗
        ((fsp + 56#64) ↦₆₄ slot56_old) ∗
        Frame)
      (fun sm Pm =>
        (Pm ⊢
          stackAt fsp encoderFromPbStack ∗
          memRegion (fsp + 1888#64) 400 ∗
          ((fsp + 1392#64) ↦₆₄ v2hse2_polyEncoderTag enc) ∗
          ((fsp + 1400#64) ↦₆₄ w8) ∗
          ((fsp + 1408#64) ↦₆₄ w16) ∗
          ((fsp + 1416#64) ↦₆₄ w24) ∗
          ((fsp + 1424#64) ↦ₛ tail368.val) ∗
          memRegion (fsp + 240#64) 24 ∗
          ((fsp + 56#64) ↦₆₄ v2hse2_polyEncoderTag enc) ∗
          Frame) ∧
        VmPreserved s1 sm ∧
        sm.sp = fsp ∧
        sm.readReg64 .x19 = out ∧
        sm.readReg64 .x20 = (loByte w8).zeroExtend 64 ∧
        sm.readReg64 .x21 = s1.readReg64 .x21 ∧
        sm.readReg64 .x22 = d0 ∧
        sm.readReg64 .x23 = fsp + 1392#64 ∧
        sm.readReg64 .x24 = fsp + 1888#64 ∧
        sm.readReg64 .x25 = fsp + 1792#64 ∧
        sm.readReg64 .x26 = ca3 ∧
        sm.readReg64 .x27 = pbA ∧
        sm.readReg64 .x28 = s1.readReg64 .x28 ∧
        sm.pstate = addsPState64 d0 1#64 ∧
        TraceCalleeSaved sm s0) :=
  v2hse2_enc_ok_move_9100_to_9328_of_memcpy_placed hA.memcpy_ok
    s0 s1 fsp out d0 ca3 pbA slot56_old w8 w16 w24 tail368 enc Frame
    hfsp_align hpc1 hrun1 hsp1 hx19_1 hx22_1 hx24_1 hx25_1 hx26_1 hx27_1 htr1

theorem v2hse2_enc_ok_move_9100_to_9328_placed [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {ext : String → Option (State → State)}
    (hA : FromPbAllocHooksBudget M A lim ext)
    (s0 s1 : State) (fsp out d0 ca3 pbA slot56_old w8 w16 w24 : BitVec 64)
    (tail368 : { l : List (BitVec 8) // l.length = 368 })
    (enc : PolyEncoder) (Frame : SepProp)
    (hfsp_align : (fsp &&& 15#64 == 0#64) = true)
    (hpc1 : s1.pc = lsmpl.base 333 + 9100#64)
    (hrun1 : s1.status = .Running)
    (hsp1 : s1.sp = fsp)
    (hx19_1 : s1.readReg64 .x19 = out)
    (hx22_1 : s1.readReg64 .x22 = d0)
    (hx24_1 : s1.readReg64 .x24 = fsp + 1888#64)
    (hx25_1 : s1.readReg64 .x25 = fsp + 1792#64)
    (hx26_1 : s1.readReg64 .x26 = ca3)
    (hx27_1 : s1.readReg64 .x27 = pbA)
    (htr1 : TraceCalleeSaved s1 s0) :
    SepWP (lsProg_333 (Rust.withPanics ext))
      (lsmpl.base 333 + 9328#64) s1
      (stackAt fsp encoderFromPbStack ∗
        ((fsp + 1888#64) ↦₆₄ v2hse2_polyEncoderTag enc) ∗
        ((fsp + 1896#64) ↦₆₄ w8) ∗
        ((fsp + 1904#64) ↦₆₄ w16) ∗
        ((fsp + 1912#64) ↦₆₄ w24) ∗
        ((fsp + 1920#64) ↦ₛ tail368.val) ∗
        memRegion (fsp + 1392#64) 400 ∗
        memRegion (fsp + 240#64) 24 ∗
        ((fsp + 56#64) ↦₆₄ slot56_old) ∗
        Frame)
      (fun sm Pm =>
        (Pm ⊢
          stackAt fsp encoderFromPbStack ∗
          memRegion (fsp + 1888#64) 400 ∗
          ((fsp + 1392#64) ↦₆₄ v2hse2_polyEncoderTag enc) ∗
          ((fsp + 1400#64) ↦₆₄ w8) ∗
          ((fsp + 1408#64) ↦₆₄ w16) ∗
          ((fsp + 1416#64) ↦₆₄ w24) ∗
          ((fsp + 1424#64) ↦ₛ tail368.val) ∗
          memRegion (fsp + 240#64) 24 ∗
          ((fsp + 56#64) ↦₆₄ v2hse2_polyEncoderTag enc) ∗
          Frame) ∧
        VmPreserved s1 sm ∧
        sm.sp = fsp ∧
        sm.readReg64 .x19 = out ∧
        sm.readReg64 .x20 = (loByte w8).zeroExtend 64 ∧
        sm.readReg64 .x21 = s1.readReg64 .x21 ∧
        sm.readReg64 .x22 = d0 ∧
        sm.readReg64 .x23 = fsp + 1392#64 ∧
        sm.readReg64 .x24 = fsp + 1888#64 ∧
        sm.readReg64 .x25 = fsp + 1792#64 ∧
        sm.readReg64 .x26 = ca3 ∧
        sm.readReg64 .x27 = pbA ∧
        sm.readReg64 .x28 = s1.readReg64 .x28 ∧
        sm.pstate = addsPState64 d0 1#64 ∧
        TraceCalleeSaved sm s0) :=
  v2hse2_enc_ok_move_9100_to_9328_of_memcpy_placed (spqr_hook_ok_of_mem hA.memcpy)
    s0 s1 fsp out d0 ca3 pbA slot56_old w8 w16 w24 tail368 enc Frame
    hfsp_align hpc1 hrun1 hsp1 hx19_1 hx22_1 hx24_1 hx25_1 hx26_1 hx27_1 htr1

theorem v2hse2_enc_ok_move_9100_to_9328_placed_budget [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {ext : String → Option (State → State)}
    (hA : FromPbAllocHooksBudget M A lim ext)
    (s0 s1 : State) (fsp out d0 ca3 pbA slot56_old w8 w16 w24 : BitVec 64)
    (tail368 : { l : List (BitVec 8) // l.length = 368 })
    (enc : PolyEncoder) (st : M.σ) (Frame : SepProp)
    (hfsp_align : (fsp &&& 15#64 == 0#64) = true)
    (hpc1 : s1.pc = lsmpl.base 333 + 9100#64)
    (hrun1 : s1.status = .Running)
    (hsp1 : s1.sp = fsp)
    (hx19_1 : s1.readReg64 .x19 = out)
    (hx22_1 : s1.readReg64 .x22 = d0)
    (hx24_1 : s1.readReg64 .x24 = fsp + 1888#64)
    (hx25_1 : s1.readReg64 .x25 = fsp + 1792#64)
    (hx26_1 : s1.readReg64 .x26 = ca3)
    (hx27_1 : s1.readReg64 .x27 = pbA)
    (htr1 : TraceCalleeSaved s1 s0) :
    SepWP (lsProg_333 (Rust.withPanics ext))
      (lsmpl.base 333 + 9328#64) s1
      (stackAt fsp encoderFromPbStack ∗
        ((fsp + 1888#64) ↦₆₄ v2hse2_polyEncoderTag enc) ∗
        ((fsp + 1896#64) ↦₆₄ w8) ∗
        ((fsp + 1904#64) ↦₆₄ w16) ∗
        ((fsp + 1912#64) ↦₆₄ w24) ∗
        ((fsp + 1920#64) ↦ₛ tail368.val) ∗
        memRegion (fsp + 1392#64) 400 ∗
        memRegion (fsp + 240#64) 24 ∗
        ((fsp + 56#64) ↦₆₄ slot56_old) ∗
        A.pool lim st s1 ∗
        Frame)
      (fun sm Pm =>
        (Pm ⊢
          stackAt fsp encoderFromPbStack ∗
          memRegion (fsp + 1888#64) 400 ∗
          ((fsp + 1392#64) ↦₆₄ v2hse2_polyEncoderTag enc) ∗
          ((fsp + 1400#64) ↦₆₄ w8) ∗
          ((fsp + 1408#64) ↦₆₄ w16) ∗
          ((fsp + 1416#64) ↦₆₄ w24) ∗
          ((fsp + 1424#64) ↦ₛ tail368.val) ∗
          memRegion (fsp + 240#64) 24 ∗
          ((fsp + 56#64) ↦₆₄ v2hse2_polyEncoderTag enc) ∗
          A.pool lim st sm ∗
          Frame) ∧
        VmPreserved s1 sm ∧
        sm.sp = fsp ∧
        sm.readReg64 .x19 = out ∧
        sm.readReg64 .x20 = (loByte w8).zeroExtend 64 ∧
        sm.readReg64 .x21 = s1.readReg64 .x21 ∧
        sm.readReg64 .x22 = d0 ∧
        sm.readReg64 .x23 = fsp + 1392#64 ∧
        sm.readReg64 .x24 = fsp + 1888#64 ∧
        sm.readReg64 .x25 = fsp + 1792#64 ∧
        sm.readReg64 .x26 = ca3 ∧
        sm.readReg64 .x27 = pbA ∧
        sm.readReg64 .x28 = s1.readReg64 .x28 ∧
        sm.pstate = addsPState64 d0 1#64 ∧
        TraceCalleeSaved sm s0) := by
  have hwp := v2hse2_enc_ok_move_9100_to_9328_placed hA
    s0 s1 fsp out d0 ca3 pbA slot56_old w8 w16 w24 tail368 enc (A.pool lim st s1 ∗ Frame)
    hfsp_align hpc1 hrun1 hsp1 hx19_1 hx22_1 hx24_1 hx25_1 hx26_1 hx27_1 htr1
  refine SepWP.mono hwp fun sm Pm _ _ ⟨hPm, hvm, hrest⟩ => ?_
  rw [← A.pool_of_vmPreserved hvm] at hPm
  exact ⟨hPm, hvm, hrest⟩

end LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant2hse2PlacedBudget
