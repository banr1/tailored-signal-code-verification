/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Heap.IfaceBudgetLemmas
public import LibsignalBinary.Proofs.Placed.BudgetVmSteps
public import LibsignalBinary.Proofs.Placed.ElfLsRetAddr
public meta import LibsignalBinary.Proofs.Placed.BudgetVmSteps -- shake: keep
public import LibsignalBinary.Proofs.SpqrV1.States.Recv.ArmHeaderSent1Placed
public import LibsignalBinary.Proofs.SpqrV1.States.Recv.ArmNoHeaderReceivedStepsPlacedBudgetAux
public import LibsignalBinary.Proofs.SpqrV1.States.Recv.DropChunkedClPlacedBudget
import LibsignalBinary.Proofs.Common.SharedHelpers
meta import LibsignalBinary.Proofs.Common.SharedHelpers -- shake: keep
import LibsignalBinary.Proofs.SpqrV1.Kdf.HkdfToSliceExtract
import LibsignalBinary.Proofs.SpqrV1.Poly.EncoderIntoPb.Defs
import LibsignalBinary.Proofs.SpqrV1.States.Recv.ArmCt1Received1
import LibsignalBinary.Proofs.SpqrV1.States.Recv.ArmHeaderSent1
import LibsignalBinary.Proofs.SpqrV1.States.Recv.ArmsSendEk1
import LibsignalBinary.Proofs.SpqrV1.States.Recv.CodeSymFetch0Placed
import LibsignalBinary.Proofs.SpqrV1.States.Recv.CodeSymFetch1Placed
import LibsignalBinary.Proofs.SpqrV1.States.Recv.CodeSymFetch3Placed
import LibsignalBinary.Proofs.SpqrV1.States.Recv.DispatchPlaced
import LibsignalBinary.Proofs.SpqrV1.States.Recv.SendEkCommonPlaced
import ProofLib.SepLogic.WPp

/-!
# `<States>::recv` (Block `332`) — `.headerSent` Arm, Part 1 (Budget-Threaded)

Budget-threaded `[LibsignalPlacement]` proofs for the `FreeOnlyEvs` `msg.epoch > st.uc.epoch`
deallocation exit and `VmPreserved` `<` / `= ∧ ¬ .ct1` writeback branches of `.headerSent`
(`+780`, Block `332`).
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 400000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

namespace LibsignalBinary.Proofs.SpqrV1.States.Recv.ArmHeaderSent1PlacedBudget

open Arm64 ProofLib ProofLib.ProgramReflection
open CryptoGames.LibsignalSession (ShaCompress)
open CryptoVerification
open CryptoVerification.RustHeap
open CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalTripleRatchetRepr
open CryptoVerification.LibsignalSpqrV1
open CryptoVerification.SpqrV1
open CryptoVerification.SpqrV1.Auth
open CryptoVerification.SpqrV1.Poly
open CryptoVerification.SpqrV1.Drop
open CryptoVerification.SpqrV1.Top
open CryptoVerification.SpqrV1.Top.MessageSerialize
open CryptoVerification.SpqrV1.States
open CryptoVerification.SpqrV1.States.Leaves
open CryptoVerification.SpqrV1.States.Leaves.RecvHdrChunk
open CryptoVerification.SpqrV1.States.RecvCt2Chunk
open CryptoVerification.SpqrV1.States.Recv
open CryptoVerification.CodeLayout
open LibsignalBinary.Heap (
  AllocCallPreserved AllocCostModel AllocEvent BudgetLimits FreeOnlyEvs
  RustCliAllocBudget VmPreserved rustCliDeallocBudgetSpec
)
open LibsignalBinary.Heap.SpecBudget (withVmPreserved)
open LibsignalBinary.Proofs.SpqrV1.States.Recv.ArmNoHeaderReceivedStepsPlacedBudgetAux (
  seq_vm_cont call_memcpy_relocate_cs states_recv_writeback_59e88_placed
)
open LibsignalBinary.Proofs.Placed.ElfLsRetAddr (LsRetAddr624)

attribute [local irreducible] libsignalSessionCode Program.fetch Program.externAt? Program.fnOff
  CryptoVerification.blkPC_332
attribute [-arm64_norm]
  CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.sp_sub_688_eq_hsp
  CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.sp_add_neg688_eq_hsp
  CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.sp_sub_96_eq_hsp_592
  CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.sp_add_neg96_eq_hsp_592
attribute [local arm64_norm, local wp_norm]
  bv_sub_add_lit bv_sub_sub_recv BitVec.sub_add_cancel BitVec.toNat_zero
  Leaves.extractLsb'_0_64_append Leaves.extractLsb'_64_64_append
  sp_sub_96_add_16 sp_sub_96_add_32 sp_sub_96_add_48 sp_sub_96_add_64 sp_sub_96_add_80
  sp_sub_96_sub_4096 sp_sub_4192_sub_48 sp_sub_4240_add_48 sp_sub_4240_add_4096 sp_sub_144_add_48
  sp_sub_96_add_8_recv sp_sub_80_add_8_recv sp_sub_64_add_8_recv sp_sub_48_add_8_recv
  sp_sub_32_add_8_recv sp_sub_16_add_8_recv sp_sub_96_add_96_recv
  sp_sub_4240_add_4144_hs bv376_toNat_hs
  RustCliAllocBudget.pool_setPC RustCliAllocBudget.pool_advancePC
  RustCliAllocBudget.pool_setPState RustCliAllocBudget.pool_writeReg64
  RustCliAllocBudget.pool_writeReg32 RustCliAllocBudget.pool_writeReg

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

private theorem acpOfVm {s sm : State} (_ : VmPreserved s sm) (h : AllocCallPreserved s sm) :
    AllocCallPreserved s sm := h

@[reducible] private def vmMid {s sm : State} (_ : VmPreserved s sm) : State := sm

private theorem seq_vm_cont_lscl {prog : Program} {pl : Arm64.Obj.MultiPlacement}
    {mid tgt : BitVec 64} {s : State} {Pre : SepProp} {post : State → SepProp → Prop}
    (hcl : LibsignalCodeLoaded pl s.mem)
    (h : SepWP prog mid s Pre
      (fun sm Pm => VmPreserved s sm ∧
        (LibsignalCodeLoaded pl sm.mem → VmPreserved s sm → SepWP prog tgt sm Pm post))) :
    SepWP prog tgt s Pre post :=
  SepWP.seq_frozen (fun _ _ hcl' hkf => hcl'.of_keepsFrozen hkf) hcl
    (SepWP.mono h fun _ _ _ _ ⟨hvm, hk⟩ hclm => hk hclm hvm)

/-! ## 1. `.headerSent` (`+780`, Block `332`): `msg.epoch > st.uc.epoch` -/

/-- Budget-threaded relocatable `msg.epoch > st.uc.epoch` tail-call block (`+1144 -> s0.x30`, Block `332`)
    for `.headerSent`. -/
theorem headerSent_gt_558cc_placed [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits} {F : ShaCompress}
    {ext : String → Option (State → State)}
    (hdealloc : HookSat (Rust.withPanics ext) spqrDeallocSym (rustCliDeallocBudgetSpec M A lim))
    (st_cost : M.σ)
    (s0 s : State) (outA selfA : BitVec 64)
    (st : Chunked.SendEk.HeaderSent spqrPolyApi (spqrAuthApi F))
    (ep : BitVec 64) (P_rest : SepProp)
    (hcl : LibsignalCodeLoaded lsmpl s.mem)
    (hpc : s.pc = lsmpl.base 332 + 1144#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = s0.sp - 4240#64)
    (hsp_align : s0.spAligned = true)
    (hx8 : s.readReg64 .x8 = selfA + 8#64)
    (hx19 : s.readReg64 .x19 = outA)
    (hx25 : s.readReg64 .x25 = ep)
    (htr : TraceCalleeSaved s s0)
    (hlr_ls : LsRetAddr624 (s0.readReg64 .x30) := by
      first
      | assumption
      | simp (config := { decide := true }) only [Reg.x30, Reg.lr, arm64_norm, wp_norm]) :
    SepWP (lsProg_332 (Rust.withPanics ext)) (s0.readReg64 .x30) s
      (P_rest ∗
        memRegion outA v1RecvSize ∗
        (selfA ↦₆₄ 4#64) ∗
        chunkedHeaderSentAt A.repAlloc (selfA + 8#64) st ∗
        memRegion (selfA + 888#64) 40 ∗
        A.pool lim st_cost s ∗
        stackAt (s0.sp - 4240#64) statesRecvCalleeStackX ∗
        memRegion (s0.sp - 4240#64) 4144 ∗
        statesRecvSavedCells s0)
      (fun sf Pf =>
        ∃ evs : List AllocEvent,
          FreeOnlyEvs evs ∧
          (Pf ⊢
            P_rest ∗
            resultV1RecvAt A.repAlloc (F := F) outA (.error (.err (.epochOutOfRange ep))) ∗
            memRegion selfA chunkedStatesSize ∗
            A.pool lim (M.stepEvents evs st_cost) sf ∗
            stackAt s0.sp statesRecvStackX) ∧
          sf.sp = s0.sp ∧
          AllocCallPreserved s sf ∧
          CalleeSavedPreserved s0 sf ∧
          sf.trace = s0.trace) := by
  have hsp_align' : (s0.sp &&& 15#64 == 0#64) = true := hsp_align
  have hsp96_align : ((s0.sp - 96#64) &&& 15#64 == 0#64) = true :=
    spAligned_sub s0.sp 96#64 hsp_align (by decide)
  rw [lsmpl_base_332_eq] at hpc
  dsimp only [lsProg_332, chunkedHeaderSentSize, BitVec.ofNat_eq_ofNat] at hpc ⊢
  refine seq_vm_cont_lscl hcl (mid := lsmpl.base 276) ?_
  rw [memRegion_out_960_split_err outA]
  wp_pull_exists; rename_i v0 b8 v16
  unfold statesRecvSavedCells
  by_vm_steps_nest (
    generalize hsp0 : s0.sp = sp0 at hsp hsp_align' hsp96_align ⊢
    wp_steps
    subst hsp0
    refine SepWP.done rfl (by assumption) ⟨by simp only [wp_norm, arm64_norm], fun hcl1 hvm1 => ?_⟩
    have hacp1 :=
      acpOfVm hvm1 (by simp only [AllocCallPreserved, wp_norm, arm64_norm])
    have hdrop_raw := DropChunkedClPlacedBudget.drop_chunked_header_sent_mem_on (F := F)
      (callerProg := (blkPC_332).rebase (blkPl_332).base (Rust.withPanics ext)) hdealloc hcl1
    dsimp only [withMemEq, LibsignalBinary.Proofs.SpqrV1.Drop.ChunkedBudget.dropChunkedHeaderSentSpec,
      chunkedHeaderSentSize, BitVec.ofNat_eq_ofNat] at hdrop_raw
    wp_conv_pre => rw [← A.pool_of_vmPreserved hvm1]
    have hrest := stack_restore_statesRecv s0
    unfold statesRecvSavedCells at hrest
    refine SepWP.focus_weaken hrest (by sep_focus) ?_
    have hsplit_sp := stackAt_statesRecvStackX_split_dropStackPoly64 s0.sp
    refine SepWP.focus_weaken (Entails.of_eq hsplit_sp) (by sep_focus) ?_
    have hlr_ls' : LsRetAddr624 (s0.readReg64 .lr) := hlr_ls
    have hlr_ls_n : LsRetAddr624 (s0.readReg64 (Reg.gpr 30#5)) := hlr_ls
    wp_call hdrop_raw (⟨selfA + 8#64, st⟩, st_cost)
    have hacp_all : AllocCallPreserved s sf := by assumption
    have hevs_w : FreeOnlyEvs w := by assumption
    refine SepWP.focus_weaken (Entails.of_eq hsplit_sp.symm) (by sep_focus) ?_
    refine SepWP.fold
      (F := P_rest ∗ A.pool lim (M.stepEvents w st_cost) sf ∗ stackAt s0.sp statesRecvStackX)
      (sepConj_mono
        (err_epochOutOfRange_entails_resultV1RecvAt A.repAlloc (F := F) outA ep)
        (self_880_40_entails_memRegion_928 selfA 4#64))
      (by sep_ac_rfl) ?_
    refine SepWP.mono
      (post := fun sf' Pf' =>
        (Pf' ⊢
          P_rest ∗
          resultV1RecvAt A.repAlloc (F := F) outA (.error (.err (.epochOutOfRange ep))) ∗
          memRegion selfA chunkedStatesSize ∗
          A.pool lim (M.stepEvents w st_cost) sf' ∗
          stackAt s0.sp statesRecvStackX) ∧
        sf'.sp = s0.sp ∧
        AllocCallPreserved s sf' ∧
        CalleeSavedPreserved s0 sf' ∧
        sf'.trace = s0.trace)
      ?_ (fun _ _ _ _ h => ⟨w, hevs_w, h⟩)
    have htr_sf : sf.trace = s0.trace := by
      refine Eq.trans (by assumption) ?_
      try simp only [wp_norm, arm64_norm]
      exact htr.1
    rcases hacp_all with ⟨_, _, _, _, _, _, _⟩
    dsimp only [CalleeSavedPreserved, Reg.x19, Reg.x20, Reg.x21, Reg.x22, Reg.x23,
      Reg.x24, Reg.x25, Reg.x26, Reg.x27, Reg.x28, Reg.x29]
    wp_done
  )

/-- Budget-threaded relocatable `.headerSent` arm when `msg.epoch > st.uc.epoch`
    (`+780 -> s0.x30`, Block `332`). -/
theorem headerSent_arm_gt_placed [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits} {F : ShaCompress}
    {ext : String → Option (State → State)}
    (hdealloc : HookSat (Rust.withPanics ext) spqrDeallocSym (rustCliDeallocBudgetSpec M A lim))
    (st_cost : M.σ)
    (s0 s : State) (outA selfA msgA : BitVec 64)
    (st : Chunked.SendEk.HeaderSent spqrPolyApi (spqrAuthApi F))
    (msg : Message spqrPolyApi)
    (P_rest : SepProp)
    (hgt : msg.epoch > st.uc.epoch)
    (hcl : LibsignalCodeLoaded lsmpl s.mem)
    (hpc : s.pc = lsmpl.base 332 + 780#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = s0.sp - 4240#64)
    (hsp_align : s0.spAligned = true)
    (hx1 : s.readReg64 .x1 = selfA)
    (hx19 : s.readReg64 .x19 = outA)
    (hx24 : s.readReg64 .x24 = msgA)
    (htr : TraceCalleeSaved s s0)
    (hlr_ls : LsRetAddr624 (s0.readReg64 .x30) := by
      first
      | assumption
      | simp (config := { decide := true }) only [Reg.x30, Reg.lr, arm64_norm, wp_norm]) :
    SepWP (lsProg_332 (Rust.withPanics ext)) (s0.readReg64 .x30) s
      (P_rest ∗
        memRegion outA v1RecvSize ∗
        chunkedStatesAt A.repAlloc selfA (.headerSent st) ∗
        messageAt spqrPolyApi msgA msg ∗
        A.pool lim st_cost s ∗
        stackAt (s0.sp - 4240#64) statesRecvCalleeStackX ∗
        memRegion (s0.sp - 4240#64) 4144 ∗
        statesRecvSavedCells s0)
      (fun sf Pf =>
        ∃ evs : List AllocEvent,
          FreeOnlyEvs evs ∧
          (Pf ⊢
            P_rest ∗
            resultV1RecvAt A.repAlloc (F := F) outA (.error (.err (.epochOutOfRange msg.epoch))) ∗
            memRegion selfA chunkedStatesSize ∗
            messageAt spqrPolyApi msgA msg ∗
            A.pool lim (M.stepEvents evs st_cost) sf ∗
            stackAt s0.sp statesRecvStackX) ∧
          sf.sp = s0.sp ∧
          AllocCallPreserved s sf ∧
          CalleeSavedPreserved s0 sf ∧
          sf.trace = s0.trace) := by
  have hgt_nat : msg.epoch.toNat > st.uc.epoch.toNat := BitVec.lt_def.mp hgt
  have hcond1 := epoch_cmp_ct1r_eq_of_gt hgt_nat
  have hcond2 := epoch_cmp_ct1r_bne_1_of_gt hgt_nat
  have htail := @headerSent_gt_558cc_placed _ M A lim F ext hdealloc st_cost s0
  rw [lsmpl_base_332_eq] at hpc htail
  dsimp only [lsProg_332, chunkedStatesAt, messageAt, BitVec.ofNat_eq_ofNat] at hpc htail ⊢
  refine seq_vm_cont_lscl hcl (mid := (blkPl_332).base + 1144#64) ?_
  refine SepWP.fold (memRegion_4144_entails_sendEkFrame (s0.sp - 4240#64)) (by sep_focus) ?_
  wp_pull_exists; rename_i sp
  refine SepWP.fold (chunkedHeaderSentAt_extract63_376 A.repAlloc (selfA + 8#64) st) (by sep_focus) ?_
  wp_pull_exists; rename_i w tailBytes
  refine SepWP.pure_elim fun ⟨hw62, htail_len⟩ => ?_
  have hsp_align' : (s0.sp &&& 15#64 == 0#64) = true := hsp_align
  have hfsp_align : ((s0.sp - 4240#64) &&& 15#64 == 0#64) = true :=
    spAligned_sub s0.sp 4240#64 hsp_align (by decide)
  by_vm_steps_nest (
    generalize hsp0 : s0.sp = sp0 at hsp hsp_align' hfsp_align ⊢
    wp_conv_pre =>
      dsimp only [sendEkSpillsAt, words63At, words10At]
      rw [hw62]
      simp only [pointsTo128_eq_pair64_recv, BitVec.add_assoc, arm64_norm]
    wp_steps
    subst hsp0
    refine SepWP.done rfl (by assumption) ⟨by simp only [wp_norm, arm64_norm], fun hcl1 hvm1 => ?_⟩
    have hacp1 :=
      acpOfVm hvm1 (by simp only [AllocCallPreserved, wp_norm, arm64_norm])
    wp_conv_pre => rw [← A.pool_of_vmPreserved hvm1]
    let sp1 : SendEkSpills :=
      { b0 := ⟨w.b5.w2, w.b3.w5, w.b3.w1, sp.b0.w3, w.b3.w2, w.b4.w1, w.b4.w0, sp.b0.w7,
               w.b3.w4, w.b3.w3⟩
        b1 := ⟨w.b5.w7, w.b5.w5, w.b3.w9, w.b3.w6, w.b5.w3, w.b3.w7, sp.b1.w6, w.b5.w9,
               sp.b1.w8, sp.b1.w9⟩
        b2 := ⟨w.b4.w7, w.b5.w1, w.b4.w9, w.b4.w3, w.b4.w5, sp.b2.w5, w.b4.w8, sp.b2.w7,
               sp.b2.w8, w.b4.w2⟩
        b3 := ⟨sp.b3.w0, w.w62, sp.b3.w2, sp.b3.w3, sp.b3.w4, sp.b3.w5, w.b1.w3, w.b2.w5,
               sp.b3.w8, sp.b3.w9⟩
        b4 := ⟨w.b2.w6, w.b1.w2, sp.b4.w2, w.b1.w0, sp.b4.w4, sp.b4.w5, w.b0.w4, sp.b4.w7,
               sp.b4.w8, w.b2.w3⟩
        b5 := ⟨sp.b5.w0, w.b4.w4, w.b1.w4, w.b0.w8, sp.b5.w4, w.b5.w0, sp.b5.w6, w.b2.w4,
               w.b4.w6, sp.b5.w9⟩
        w60 := w.b5.w6
        w61 := sp.w61
        w62 := w.b0.w6
        q200 := sp.q200
        q210 := sp.q210
        q220 := sp.q220
        w230 := sp.w230
        q3c0 := sp.q3c0 }
    have hfold_frame :
        (words63At (selfA + 8#64) w ∗
         ((selfA + 8#64 + 504#64) ↦ₛ tailBytes) ∗
         relocatedHeap (fun dst => chunkedHeaderSentAt A.repAlloc dst st) (wordsBytes (words63List w) ++ tailBytes)) ∗
        (sendEkSpillsAt (s0.sp - 4240#64) sp1 ∗
         memRegion ((s0.sp - 4240#64) + 576#64) 376 ∗
         memRegion ((s0.sp - 4240#64) + 976#64) 880 ∗
         memRegion ((s0.sp - 4240#64) + 1856#64) 880 ∗
         sendEkUnusedAt (s0.sp - 4240#64)) ⊢
          chunkedHeaderSentAt A.repAlloc (selfA + 8#64) st ∗
          memRegion (s0.sp - 4240#64) 4144 :=
      sepConj_mono (recompose63_376 (selfA + 8#64) w tailBytes)
        (sendEkFrame_entails_memRegion_4144 (s0.sp - 4240#64) sp1)
    refine SepWP.fold
      (F := P_rest ∗
        memRegion outA v1RecvSize ∗
        (selfA ↦₆₄ 4#64) ∗
        memRegion (selfA + 888#64) 40 ∗
        ((msgA ↦₆₄ msg.epoch) ∗ messagePayloadAt spqrPolyApi msgA msg.payload) ∗
        A.pool lim st_cost (vmMid hvm1) ∗
        stackAt (s0.sp - 4240#64) statesRecvCalleeStackX ∗
        statesRecvSavedCells s0)
      hfold_frame ?_ ?_
    · dsimp only [sendEkSpillsAt, words63At, words10At, sp1]
      rw [hw62]
      simp only [pointsTo128_eq_pair64_recv, BitVec.add_assoc, arm64_norm]
      try sep_ac_rfl
    · rw [show (chunkedHeaderSentAt A.repAlloc (selfA + 8#64) st ∗ memRegion (s0.sp - 4240#64) 4144) ∗
          (P_rest ∗
            memRegion outA v1RecvSize ∗
            (selfA ↦₆₄ 4#64) ∗
            memRegion (selfA + 888#64) 40 ∗
            ((msgA ↦₆₄ msg.epoch) ∗ messagePayloadAt spqrPolyApi msgA msg.payload) ∗
            A.pool lim st_cost (vmMid hvm1) ∗
            stackAt (s0.sp - 4240#64) statesRecvCalleeStackX ∗
            statesRecvSavedCells s0) =
          (P_rest ∗ ((msgA ↦₆₄ msg.epoch) ∗ messagePayloadAt spqrPolyApi msgA msg.payload)) ∗
          memRegion outA v1RecvSize ∗
          (selfA ↦₆₄ 4#64) ∗
          chunkedHeaderSentAt A.repAlloc (selfA + 8#64) st ∗
          memRegion (selfA + 888#64) 40 ∗
          A.pool lim st_cost (vmMid hvm1) ∗
          stackAt (s0.sp - 4240#64) statesRecvCalleeStackX ∗
          memRegion (s0.sp - 4240#64) 4144 ∗
          statesRecvSavedCells s0 by sep_ac_rfl]
      refine SepWP.mono
        (htail (vmMid hvm1) outA selfA st msg.epoch
          (P_rest ∗ ((msgA ↦₆₄ msg.epoch) ∗ messagePayloadAt spqrPolyApi msgA msg.payload))
          hcl1 rfl (by assumption) (by simp only [wp_norm, arm64_norm, hsp]) hsp_align
          (by simp only [Reg.x8, wp_norm, arm64_norm, hx1])
          (by simp only [Reg.x19, wp_norm, arm64_norm, hx19])
          (by simp only [Reg.x25, wp_norm, arm64_norm, hx24])
          ⟨by simp only [wp_norm, arm64_norm]; exact htr.1,
           by simp only [wp_norm, arm64_norm]; exact htr.2⟩
          hlr_ls)
        (fun sf Pf _ _ ⟨evs, hevs, hPf, hsp_sf, hacp_sf, hcs_sf, htr_sf⟩ =>
          ⟨evs, hevs, Entails.trans hPf (Entails.of_eq (by sep_ac_rfl)),
           hsp_sf, hacp1.trans hacp_sf, hcs_sf, htr_sf⟩)
  )

/-! ## 2. `.headerSent` (`+780`, Block `332`): `msg.epoch < st.uc.epoch` -/

set_option maxHeartbeats 1200000 in
/-- Relocatable `.headerSent` arm when `msg.epoch < st.uc.epoch` (`+780 -> s0.x30`, Block `332`)
    with `VmPreserved s sf`. -/
theorem headerSent_arm_lt_placed [LibsignalPlacement]
    {A : RustAlloc} {F : ShaCompress} {ext : String → Option (State → State)}
    (hmemcpy : subroutine_ok (lsProg_332 (Rust.withPanics ext))
      (lsρ memcpyName) (withVmPreserved sessionMemcpyRegionSpec))
    (s0 s : State) (outA selfA msgA : BitVec 64)
    (st : Chunked.SendEk.HeaderSent spqrPolyApi (spqrAuthApi F))
    (msg : Message spqrPolyApi)
    (P_rest : SepProp)
    (hlt : msg.epoch < st.uc.epoch)
    (hpc : s.pc = lsmpl.base 332 + 780#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = s0.sp - 4240#64)
    (hsp_align : s0.spAligned = true)
    (hx1 : s.readReg64 .x1 = selfA)
    (hx19 : s.readReg64 .x19 = outA)
    (hx24 : s.readReg64 .x24 = msgA)
    (htr : TraceCalleeSaved s s0) :
    SepWP (lsProg_332 (Rust.withPanics ext)) (s0.readReg64 .x30) s
      (P_rest ∗
        memRegion outA v1RecvSize ∗
        chunkedStatesAt A selfA (.headerSent st) ∗
        messageAt spqrPolyApi msgA msg ∗
        A.pool ∗
        stackAt (s0.sp - 4240#64) statesRecvCalleeStackX ∗
        memRegion (s0.sp - 4240#64) 4144 ∗
        statesRecvSavedCells s0)
      (fun sf Pf =>
        VmPreserved s sf ∧
        (Pf ⊢
          P_rest ∗
          resultV1RecvAt A (F := F) outA (.ok { key := none, state := .headerSent st }) ∗
          memRegion selfA chunkedStatesSize ∗
          messageAt spqrPolyApi msgA msg ∗
          A.pool ∗
          stackAt s0.sp statesRecvStackX) ∧
        sf.sp = s0.sp ∧
        CalleeSavedPreserved s0 sf ∧
        sf.trace = s0.trace) := by
  have hlt_nat : msg.epoch.toNat < st.uc.epoch.toNat := BitVec.lt_def.mp hlt
  have hcond1 := epoch_cmp_ct1r_eq_of_lt hlt_nat
  have hcond2 := epoch_cmp_ct1r_bne_1_of_lt hlt_nat
  dsimp only [chunkedStatesAt]
  refine SepWP.fold (memRegion_4144_entails_sendEkFrame (s0.sp - 4240#64)) (by sep_focus) ?_
  wp_pull_exists; rename_i sp
  refine SepWP.fold (chunkedHeaderSentAt_extract63_376 A (selfA + 8#64) st) (by sep_focus) ?_
  wp_pull_exists; rename_i w tailBytes
  refine SepWP.pure_elim fun ⟨hw62, htail_len⟩ => ?_
  have hrel_tail := Relocatable.of_pointsToBytes tailBytes htail_len
  have hwb := @ArmNoHeaderReceivedStepsPlacedBudgetAux.states_recv_writeback_59e88_placed _ ext hmemcpy
    (F_tail := fun a => a ↦ₛ tailBytes) hrel_tail s0
  rw [lsmpl_base_332_eq] at hpc hwb
  dsimp only [lsProg_332, lsρ, memcpyName, chunkedStatesAt, messageAt,
    BitVec.ofNat_eq_ofNat] at hpc hmemcpy hwb ⊢
  have hsp_align' : (s0.sp &&& 15#64 == 0#64) = true := hsp_align
  have hfsp_align : ((s0.sp - 4240#64) &&& 15#64 == 0#64) = true :=
    spAligned_sub s0.sp 4240#64 hsp_align (by decide)
  have h512 : selfA + 8#64 + 504#64 = selfA + 512#64 := by bv_omega
  rw [h512]
  refine seq_vm_cont (mid := lsmpl.ρ "memcpy") ?_
  by_vm_steps_nest (
    generalize hsp0 : s0.sp = sp0 at hsp hsp_align' hfsp_align ⊢
    wp_conv_pre =>
      dsimp only [sendEkSpillsAt, words63At, words10At]
      rw [hw62]
      simp only [pointsTo128_eq_pair64_recv, BitVec.add_assoc, arm64_norm]
    wp_steps 200
    refine SepWP.done rfl (by assumption) ⟨by simp only [wp_norm, arm64_norm], fun hvm1 => ?_⟩
    refine ArmNoHeaderReceivedStepsPlacedBudgetAux.call_memcpy_relocate_cs (ret_pc := (blkPl_332).base + 10476#64)
      hmemcpy hrel_tail (sp0 - 3664#64) (selfA + 512#64)
      rfl (by assumption) (by simp only [wp_norm, arm64_norm, hsp]) hfsp_align rfl
      ⟨by simp only [wp_norm, arm64_norm]; exact htr.1,
       by simp only [wp_norm, arm64_norm]; exact htr.2⟩ rfl
      (by simp only [Reg.x1, wp_norm, arm64_norm, hx1])
      rfl (by sep_focus) ?_
    intro sf1 hpc1 hrun1 hsp1 hvm_mc hcs1 htr1
    have hx19_1 : sf1.readReg64 .x19 = outA :=
      hcs1.1.trans (by simp only [Reg.x19, wp_norm, arm64_norm, hx19])
    have hx20_1 : sf1.readReg64 .x20 = w.b1.w5 :=
      hcs1.2.1.trans (by simp only [Reg.x20, wp_norm, arm64_norm])
    have hx22_1 : sf1.readReg64 .x22 = w.b0.w0 :=
      hcs1.2.2.2.1.trans (by simp only [Reg.x22, wp_norm, arm64_norm])
    have hx25_1 : sf1.readReg64 .x25 = w.b0.w1 :=
      hcs1.2.2.2.2.2.2.1.trans (by simp only [Reg.x25, wp_norm, arm64_norm])
    have hx28_1 : sf1.readReg64 .x28 = w.b1.w6 :=
      hcs1.2.2.2.2.2.2.2.2.2.1.trans (by simp only [Reg.x28, wp_norm, arm64_norm])
    refine seq_vm_cont (mid := (blkPl_332).base + 18996#64) ?_
    by_vm_steps_nest (
      wp_steps
      subst hsp0
      refine SepWP.done rfl (by assumption) ⟨by simp only [wp_norm, arm64_norm], fun hvm2 => ?_⟩
      let sp1 : SendEkSpills :=
        { b0 := ⟨w.b5.w2, w.b3.w5, w.b3.w1, w.b2.w9, w.b3.w2, w.b4.w1, w.b4.w0, w.b3.w8,
                 w.b3.w4, w.b3.w3⟩
          b1 := ⟨w.b5.w7, w.b5.w5, w.b3.w9, w.b3.w6, w.b5.w3, w.b3.w7, sp.b1.w6, w.b5.w9,
                 sp.b1.w8, sp.b1.w9⟩
          b2 := ⟨w.b4.w7, w.b5.w1, w.b4.w9, w.b4.w3, w.b4.w5, sp.b2.w5, w.b4.w8, 4#64,
                 noneCap, w.b4.w2⟩
          b3 := ⟨w.b5.w8, w.w62, w.b1.w8, w.b2.w1, w.b2.w7, w.b0.w7, w.b1.w3, w.b2.w5,
                 w.b3.w0, w.b2.w8⟩
          b4 := ⟨w.b2.w6, w.b1.w2, w.b1.w9, w.b1.w0, w.b2.w2, w.b0.w5, w.b0.w4, w.b1.w1,
                 w.b2.w0, w.b2.w3⟩
          b5 := ⟨w.b0.w9, w.b4.w4, w.b1.w4, w.b0.w8, w.b1.w7, w.b5.w0, w.b0.w3, w.b2.w4,
                 w.b4.w6, w.b5.w4⟩
          w60 := w.b5.w6
          w61 := w.b0.w2
          w62 := w.b0.w6
          q200 := sp.q200
          q210 := sp.q210
          q220 := sp.q220
          w230 := sp.w230
          q3c0 := w.q60 }
      have hfold_self_sp :
          ((selfA ↦₆₄ 4#64) ∗ words63At (selfA + 8#64) w ∗
           memRegion (selfA + 512#64) 376 ∗ memRegion (selfA + 888#64) 40) ∗
          sendEkSpillsAt (s0.sp - 4240#64) sp1 ⊢
            memRegion selfA chunkedStatesSize ∗
            sendEkSpillsAt (s0.sp - 4240#64) sp1 := by
        have h880 := words63At_376_entails_memRegion_880 (selfA + 8#64) (selfA + 512#64) w (by bv_omega)
        have h928 : (selfA ↦₆₄ 4#64) ∗ (words63At (selfA + 8#64) w ∗ memRegion (selfA + 512#64) 376) ∗
            memRegion (selfA + 888#64) 40 ⊢ memRegion selfA chunkedStatesSize :=
          Entails.trans (sepConj_mono_right (sepConj_mono_left h880))
            (self_880_40_entails_memRegion_928 selfA 4#64)
        exact sepConj_mono_left (Entails.trans (Entails.of_eq (by sep_ac_rfl)) h928)
      have h3664 : s0.sp - 3664#64 = (s0.sp - 4240#64) + 576#64 := by bv_omega
      rw [h3664]
      refine SepWP.fold
        (F := P_rest ∗
          relocatedHeap (fun dst => chunkedHeaderSentAt A dst st) (wordsBytes (words63List w) ++ tailBytes) ∗
          ((msgA ↦₆₄ msg.epoch) ∗ messagePayloadAt spqrPolyApi msgA msg.payload) ∗
          A.pool ∗
          memRegion outA v1RecvSize ∗
          stackAt (s0.sp - 4240#64) statesRecvCalleeStackX ∗
          (((s0.sp - 4240#64) + 576#64) ↦ₛ tailBytes) ∗
          memRegion ((s0.sp - 4240#64) + 976#64) 880 ∗
          memRegion ((s0.sp - 4240#64) + 1856#64) 880 ∗
          sendEkUnusedAt (s0.sp - 4240#64) ∗
          statesRecvSavedCells s0)
        hfold_self_sp ?_ ?_
      · dsimp only [sendEkSpillsAt, words63At, words10At, sp1]
        rw [hw62]
        simp only [pointsTo128_eq_pair64_recv, BitVec.add_assoc, arm64_norm]
        sep_ac_rfl
      · rw [show (memRegion selfA chunkedStatesSize ∗ sendEkSpillsAt (s0.sp - 4240#64) sp1) ∗
            (P_rest ∗
              relocatedHeap (fun dst => chunkedHeaderSentAt A dst st) (wordsBytes (words63List w) ++ tailBytes) ∗
              ((msgA ↦₆₄ msg.epoch) ∗ messagePayloadAt spqrPolyApi msgA msg.payload) ∗
              A.pool ∗
              memRegion outA v1RecvSize ∗
              stackAt (s0.sp - 4240#64) statesRecvCalleeStackX ∗
              (((s0.sp - 4240#64) + 576#64) ↦ₛ tailBytes) ∗
              memRegion ((s0.sp - 4240#64) + 976#64) 880 ∗
              memRegion ((s0.sp - 4240#64) + 1856#64) 880 ∗
              sendEkUnusedAt (s0.sp - 4240#64) ∗
              statesRecvSavedCells s0) =
            (P_rest ∗
              relocatedHeap (fun dst => chunkedHeaderSentAt A dst st) (wordsBytes (words63List w) ++ tailBytes) ∗
              memRegion selfA chunkedStatesSize ∗
              ((msgA ↦₆₄ msg.epoch) ∗ messagePayloadAt spqrPolyApi msgA msg.payload) ∗
              A.pool) ∗
            memRegion outA v1RecvSize ∗
            stackAt (s0.sp - 4240#64) statesRecvCalleeStackX ∗
            sendEkSpillsAt (s0.sp - 4240#64) sp1 ∗
            (((s0.sp - 4240#64) + 576#64) ↦ₛ tailBytes) ∗
            memRegion ((s0.sp - 4240#64) + 976#64) 880 ∗
            memRegion ((s0.sp - 4240#64) + 1856#64) 880 ∗
            sendEkUnusedAt (s0.sp - 4240#64) ∗
            statesRecvSavedCells s0 by sep_ac_rfl]
        refine SepWP.mono
          (hwb _ outA sp1
            (P_rest ∗
              relocatedHeap (fun dst => chunkedHeaderSentAt A dst st) (wordsBytes (words63List w) ++ tailBytes) ∗
              memRegion selfA chunkedStatesSize ∗
              ((msgA ↦₆₄ msg.epoch) ∗ messagePayloadAt spqrPolyApi msgA msg.payload) ∗
              A.pool)
            rfl (by assumption) (by simp only [wp_norm, arm64_norm, hsp1]) hsp_align
            (by simp only [Reg.x19, wp_norm, arm64_norm, hx19_1])
            ⟨by simp only [wp_norm, arm64_norm]; exact htr1.1,
             by simp only [wp_norm, arm64_norm]; exact htr1.2⟩)
          (fun sf Pf _ _ ⟨hvm_wb, hPf, hsp_sf, hcs_sf, htr_sf⟩ =>
            ⟨hvm1.trans (hvm_mc.trans (hvm2.trans hvm_wb)), ?_, hsp_sf, hcs_sf, htr_sf⟩)
        refine Entails.trans hPf ?_
        have hrec := writeback_headerSent_entails_resultV1RecvAt A (F := F) outA st w tailBytes
          w.b5.w9 sp.q200
        refine Entails.trans (Entails.of_eq ?_)
          (sepConj_mono_right (sepConj_mono_left hrec))
        dsimp only [writebackWords63, sp1, Reg.x0, Reg.x1, Reg.x2, Reg.x3, Reg.x4, Reg.x5, Reg.x6,
          Reg.x7, Reg.x8, Reg.x9, Reg.x10, Reg.x11, Reg.x12, Reg.x13, Reg.x14, Reg.x15, Reg.x16,
          Reg.x17, Reg.x20, Reg.x21, Reg.x22, Reg.x23, Reg.x24, Reg.x25, Reg.x26, Reg.x27, Reg.x28,
          Reg.x30]
        simp only [wp_norm, arm64_norm, hx20_1, hx22_1, hx25_1, hx28_1, ← hw62]
        sep_ac_rfl
    )
  )

/-! ## 3. `.headerSent` (`+780`, Block `332`): `msg.epoch = st.uc.epoch` and `msg.payload ≠ .ct1 _` -/

set_option maxHeartbeats 1200000 in
/-- Relocatable `.headerSent` arm when `msg.epoch = st.uc.epoch` and `∀ c, msg.payload ≠ .ct1 c`
    (`+780 -> s0.x30`, Block `332`) with `VmPreserved s sf`. -/
theorem headerSent_arm_eq_other_placed [LibsignalPlacement]
    {A : RustAlloc} {F : ShaCompress} {ext : String → Option (State → State)}
    (hmemcpy : subroutine_ok (lsProg_332 (Rust.withPanics ext))
      (lsρ memcpyName) (withVmPreserved sessionMemcpyRegionSpec))
    (s0 s : State) (outA selfA msgA : BitVec 64)
    (st : Chunked.SendEk.HeaderSent spqrPolyApi (spqrAuthApi F))
    (msg : Message spqrPolyApi)
    (P_rest : SepProp)
    (heq : msg.epoch = st.uc.epoch)
    (hct1 : ∀ c, msg.payload ≠ .ct1 c)
    (hpc : s.pc = lsmpl.base 332 + 780#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = s0.sp - 4240#64)
    (hsp_align : s0.spAligned = true)
    (hx1 : s.readReg64 .x1 = selfA)
    (hx19 : s.readReg64 .x19 = outA)
    (hx24 : s.readReg64 .x24 = msgA)
    (htr : TraceCalleeSaved s s0) :
    SepWP (lsProg_332 (Rust.withPanics ext)) (s0.readReg64 .x30) s
      (P_rest ∗
        memRegion outA v1RecvSize ∗
        chunkedStatesAt A selfA (.headerSent st) ∗
        messageAt spqrPolyApi msgA msg ∗
        A.pool ∗
        stackAt (s0.sp - 4240#64) statesRecvCalleeStackX ∗
        memRegion (s0.sp - 4240#64) 4144 ∗
        statesRecvSavedCells s0)
      (fun sf Pf =>
        VmPreserved s sf ∧
        (Pf ⊢
          P_rest ∗
          resultV1RecvAt A (F := F) outA (.ok { key := none, state := .headerSent st }) ∗
          memRegion selfA chunkedStatesSize ∗
          messageAt spqrPolyApi msgA msg ∗
          A.pool ∗
          stackAt s0.sp statesRecvStackX) ∧
        sf.sp = s0.sp ∧
        CalleeSavedPreserved s0 sf ∧
        sf.trace = s0.trace) := by
  have hcond_eq := epoch_cmp_ct1r_eq_of_eq st.uc.epoch
  have hcond_tag1 := messagePayloadTag_eq_5_of_not_ct1 hct1
  have hcond_tag2 := messagePayloadTag_bne_5_of_not_ct1 hct1
  dsimp only [chunkedStatesAt]
  refine SepWP.fold (memRegion_4144_entails_sendEkFrame (s0.sp - 4240#64)) (by sep_focus) ?_
  wp_pull_exists; rename_i sp
  refine SepWP.fold (chunkedHeaderSentAt_extract63_376 A (selfA + 8#64) st) (by sep_focus) ?_
  wp_pull_exists; rename_i w tailBytes
  refine SepWP.pure_elim fun ⟨hw62, htail_len⟩ => ?_
  have hrel_tail := Relocatable.of_pointsToBytes tailBytes htail_len
  have hwb := @ArmNoHeaderReceivedStepsPlacedBudgetAux.states_recv_writeback_59e88_placed _ ext hmemcpy
    (F_tail := fun a => a ↦ₛ tailBytes) hrel_tail s0
  rw [lsmpl_base_332_eq] at hpc hwb
  dsimp only [lsProg_332, lsρ, memcpyName, chunkedStatesAt, messageAt,
    BitVec.ofNat_eq_ofNat] at hpc hmemcpy hwb ⊢
  have hsp_align' : (s0.sp &&& 15#64 == 0#64) = true := hsp_align
  have hfsp_align : ((s0.sp - 4240#64) &&& 15#64 == 0#64) = true :=
    spAligned_sub s0.sp 4240#64 hsp_align (by decide)
  have h512 : selfA + 8#64 + 504#64 = selfA + 512#64 := by bv_omega
  rw [h512]
  refine seq_vm_cont (mid := lsmpl.ρ "memcpy") ?_
  by_vm_steps_nest (
    generalize hsp0 : s0.sp = sp0 at hsp hsp_align' hfsp_align ⊢
    wp_conv_pre =>
      dsimp only [sendEkSpillsAt, words63At, words10At]
      rw [hw62, heq, messagePayloadAt_eq_tag_tail msgA msg.payload]
      simp only [pointsTo128_eq_pair64_recv, BitVec.add_assoc, arm64_norm]
    wp_steps 200
    refine SepWP.done rfl (by assumption) ⟨by simp only [wp_norm, arm64_norm], fun hvm1 => ?_⟩
    refine ArmNoHeaderReceivedStepsPlacedBudgetAux.call_memcpy_relocate_cs (ret_pc := (blkPl_332).base + 11296#64)
      hmemcpy hrel_tail (sp0 - 3664#64) (selfA + 512#64)
      rfl (by assumption) (by simp only [wp_norm, arm64_norm, hsp]) hfsp_align rfl
      ⟨by simp only [wp_norm, arm64_norm]; exact htr.1,
       by simp only [wp_norm, arm64_norm]; exact htr.2⟩ rfl
      (by simp only [Reg.x1, wp_norm, arm64_norm, hx1])
      rfl (by sep_focus) ?_
    intro sf1 hpc1 hrun1 hsp1 hvm_mc hcs1 htr1
    have hx19_1 : sf1.readReg64 .x19 = outA :=
      hcs1.1.trans (by simp only [Reg.x19, wp_norm, arm64_norm, hx19])
    have hx22_1 : sf1.readReg64 .x22 = w.b1.w5 :=
      hcs1.2.2.2.1.trans (by simp only [Reg.x22, wp_norm, arm64_norm])
    have hx25_1 : sf1.readReg64 .x25 = w.b0.w1 :=
      hcs1.2.2.2.2.2.2.1.trans (by simp only [Reg.x25, wp_norm, arm64_norm])
    have hx28_1 : sf1.readReg64 .x28 = w.b1.w6 :=
      hcs1.2.2.2.2.2.2.2.2.2.1.trans (by simp only [Reg.x28, wp_norm, arm64_norm])
    refine seq_vm_cont (mid := (blkPl_332).base + 18996#64) ?_
    by_vm_steps_nest (
      wp_steps
      subst hsp0
      refine SepWP.done rfl (by assumption) ⟨by simp only [wp_norm, arm64_norm], fun hvm2 => ?_⟩
      let sp1 : SendEkSpills :=
        { b0 := ⟨w.b5.w2, w.b3.w5, w.b3.w1, w.b2.w9, w.b3.w2, w.b4.w1, w.b4.w0, w.b3.w8,
                 w.b3.w4, w.b3.w3⟩
          b1 := ⟨w.b5.w7, w.b5.w5, w.b3.w9, w.b3.w6, w.b5.w3, w.b3.w7, w.b0.w0, w.b5.w9,
                 sp.b1.w8, sp.b1.w9⟩
          b2 := ⟨w.b4.w7, w.b5.w1, w.b4.w9, w.b4.w3, w.b4.w5, sp.b2.w5, w.b4.w8, 4#64,
                 noneCap, w.b4.w2⟩
          b3 := ⟨w.b5.w8, w.w62, w.b1.w8, w.b2.w1, w.b2.w7, w.b0.w7, w.b1.w3, w.b2.w5,
                 w.b3.w0, w.b2.w8⟩
          b4 := ⟨w.b2.w6, w.b1.w2, w.b1.w9, w.b1.w0, w.b2.w2, w.b0.w5, w.b0.w4, w.b1.w1,
                 w.b2.w0, w.b2.w3⟩
          b5 := ⟨w.b0.w9, w.b4.w4, w.b1.w4, w.b0.w8, w.b1.w7, w.b5.w0, w.b0.w3, w.b2.w4,
                 w.b4.w6, w.b5.w4⟩
          w60 := w.b5.w6
          w61 := w.b0.w2
          w62 := w.b0.w6
          q200 := sp.q200
          q210 := sp.q210
          q220 := sp.q220
          w230 := sp.w230
          q3c0 := w.q60 }
      have hfold_self_sp :
          ((selfA ↦₆₄ 4#64) ∗ words63At (selfA + 8#64) w ∗
           memRegion (selfA + 512#64) 376 ∗ memRegion (selfA + 888#64) 40) ∗
          (((msgA + 8#64) ↦₈ messagePayloadTag msg.payload) ∗ messagePayloadTailAt msgA msg.payload) ∗
          sendEkSpillsAt (s0.sp - 4240#64) sp1 ⊢
            memRegion selfA chunkedStatesSize ∗
            messagePayloadAt spqrPolyApi msgA msg.payload ∗
            sendEkSpillsAt (s0.sp - 4240#64) sp1 := by
        have h880 := words63At_376_entails_memRegion_880 (selfA + 8#64) (selfA + 512#64) w (by bv_omega)
        have h928 : (selfA ↦₆₄ 4#64) ∗ (words63At (selfA + 8#64) w ∗ memRegion (selfA + 512#64) 376) ∗
            memRegion (selfA + 888#64) 40 ⊢ memRegion selfA chunkedStatesSize :=
          Entails.trans (sepConj_mono_right (sepConj_mono_left h880))
            (self_880_40_entails_memRegion_928 selfA 4#64)
        exact sepConj_mono (Entails.trans (Entails.of_eq (by sep_ac_rfl)) h928)
          (sepConj_mono_left (Entails.of_eq (messagePayloadAt_eq_tag_tail msgA msg.payload).symm))
      have h3664 : s0.sp - 3664#64 = (s0.sp - 4240#64) + 576#64 := by bv_omega
      rw [h3664]
      refine SepWP.fold
        (F := P_rest ∗
          relocatedHeap (fun dst => chunkedHeaderSentAt A dst st) (wordsBytes (words63List w) ++ tailBytes) ∗
          (msgA ↦₆₄ msg.epoch) ∗
          A.pool ∗
          memRegion outA v1RecvSize ∗
          stackAt (s0.sp - 4240#64) statesRecvCalleeStackX ∗
          (((s0.sp - 4240#64) + 576#64) ↦ₛ tailBytes) ∗
          memRegion ((s0.sp - 4240#64) + 976#64) 880 ∗
          memRegion ((s0.sp - 4240#64) + 1856#64) 880 ∗
          sendEkUnusedAt (s0.sp - 4240#64) ∗
          statesRecvSavedCells s0)
        hfold_self_sp ?_ ?_
      · dsimp only [sendEkSpillsAt, words63At, words10At, sp1]
        rw [hw62, heq]
        simp only [pointsTo128_eq_pair64_recv, BitVec.add_assoc, arm64_norm]
        sep_ac_rfl
      · rw [show (memRegion selfA chunkedStatesSize ∗
              messagePayloadAt spqrPolyApi msgA msg.payload ∗
              sendEkSpillsAt (s0.sp - 4240#64) sp1) ∗
            (P_rest ∗
              relocatedHeap (fun dst => chunkedHeaderSentAt A dst st) (wordsBytes (words63List w) ++ tailBytes) ∗
              (msgA ↦₆₄ msg.epoch) ∗
              A.pool ∗
              memRegion outA v1RecvSize ∗
              stackAt (s0.sp - 4240#64) statesRecvCalleeStackX ∗
              (((s0.sp - 4240#64) + 576#64) ↦ₛ tailBytes) ∗
              memRegion ((s0.sp - 4240#64) + 976#64) 880 ∗
              memRegion ((s0.sp - 4240#64) + 1856#64) 880 ∗
              sendEkUnusedAt (s0.sp - 4240#64) ∗
              statesRecvSavedCells s0) =
            (P_rest ∗
              relocatedHeap (fun dst => chunkedHeaderSentAt A dst st) (wordsBytes (words63List w) ++ tailBytes) ∗
              memRegion selfA chunkedStatesSize ∗
              ((msgA ↦₆₄ msg.epoch) ∗ messagePayloadAt spqrPolyApi msgA msg.payload) ∗
              A.pool) ∗
            memRegion outA v1RecvSize ∗
            stackAt (s0.sp - 4240#64) statesRecvCalleeStackX ∗
            sendEkSpillsAt (s0.sp - 4240#64) sp1 ∗
            (((s0.sp - 4240#64) + 576#64) ↦ₛ tailBytes) ∗
            memRegion ((s0.sp - 4240#64) + 976#64) 880 ∗
            memRegion ((s0.sp - 4240#64) + 1856#64) 880 ∗
            sendEkUnusedAt (s0.sp - 4240#64) ∗
            statesRecvSavedCells s0 by sep_ac_rfl]
        refine SepWP.mono
          (hwb _ outA sp1
            (P_rest ∗
              relocatedHeap (fun dst => chunkedHeaderSentAt A dst st) (wordsBytes (words63List w) ++ tailBytes) ∗
              memRegion selfA chunkedStatesSize ∗
              ((msgA ↦₆₄ msg.epoch) ∗ messagePayloadAt spqrPolyApi msgA msg.payload) ∗
              A.pool)
            rfl (by assumption) (by simp only [wp_norm, arm64_norm, hsp1]) hsp_align
            (by simp only [Reg.x19, wp_norm, arm64_norm, hx19_1])
            ⟨by simp only [wp_norm, arm64_norm]; exact htr1.1,
             by simp only [wp_norm, arm64_norm]; exact htr1.2⟩)
          (fun sf Pf _ _ ⟨hvm_wb, hPf, hsp_sf, hcs_sf, htr_sf⟩ =>
            ⟨hvm1.trans (hvm_mc.trans (hvm2.trans hvm_wb)), ?_, hsp_sf, hcs_sf, htr_sf⟩)
        refine Entails.trans hPf ?_
        have hrec := writeback_headerSent_entails_resultV1RecvAt A (F := F) outA st w tailBytes
          w.b5.w9 sp.q200
        refine Entails.trans (Entails.of_eq ?_)
          (sepConj_mono_right (sepConj_mono_left hrec))
        dsimp only [writebackWords63, sp1, Reg.x0, Reg.x1, Reg.x2, Reg.x3, Reg.x4, Reg.x5, Reg.x6,
          Reg.x7, Reg.x8, Reg.x9, Reg.x10, Reg.x11, Reg.x12, Reg.x13, Reg.x14, Reg.x15, Reg.x16,
          Reg.x17, Reg.x20, Reg.x21, Reg.x22, Reg.x23, Reg.x24, Reg.x25, Reg.x26, Reg.x27, Reg.x28,
          Reg.x30]
        simp only [wp_norm, arm64_norm, hx22_1, hx25_1, hx28_1, ← hw62]
        sep_ac_rfl
    )
  )

end LibsignalBinary.Proofs.SpqrV1.States.Recv.ArmHeaderSent1PlacedBudget
