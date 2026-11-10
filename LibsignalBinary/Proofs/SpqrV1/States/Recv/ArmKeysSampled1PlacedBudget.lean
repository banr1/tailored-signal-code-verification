/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Heap.IfaceBudgetLemmas
public import LibsignalBinary.Proofs.Placed.BudgetVmSteps
public meta import LibsignalBinary.Proofs.Placed.BudgetVmSteps -- shake: keep
public import LibsignalBinary.Proofs.SpqrV1.States.Recv.ArmKeysSampled1Placed
public import LibsignalBinary.Proofs.SpqrV1.States.Recv.ArmNoHeaderReceivedStepsPlacedBudgetAux
public import LibsignalBinary.Proofs.SpqrV1.States.Recv.DropChunkedClPlacedBudget
import LibsignalBinary.Proofs.Common.SharedHelpers
meta import LibsignalBinary.Proofs.Common.SharedHelpers -- shake: keep
import LibsignalBinary.Proofs.SpqrV1.Kdf.HkdfToSliceExtract
import LibsignalBinary.Proofs.SpqrV1.Poly.EncoderIntoPb.Defs
import LibsignalBinary.Proofs.SpqrV1.States.Recv.ArmCt1Received1
import LibsignalBinary.Proofs.SpqrV1.States.Recv.ArmCt1Received2Placed
import LibsignalBinary.Proofs.SpqrV1.States.Recv.ArmHeaderSent1
import LibsignalBinary.Proofs.SpqrV1.States.Recv.ArmKeysSampled1
import LibsignalBinary.Proofs.SpqrV1.States.Recv.ArmsSendEk1
import LibsignalBinary.Proofs.SpqrV1.States.Recv.CodeSymFetch0Placed
import LibsignalBinary.Proofs.SpqrV1.States.Recv.CodeSymFetch2Placed
import LibsignalBinary.Proofs.SpqrV1.States.Recv.DispatchPlaced
import LibsignalBinary.Proofs.SpqrV1.States.Recv.SendEkCommonPlaced
import ProofLib.SepLogic.WPp

/-!
# `<States>::recv` (Block `332`) — `.keysSampled` Arm, Part 1 (Budget-Threaded)

Budget-threaded `[LibsignalPlacement]` post-call writeback, `FreeOnlyEvs` `msg.epoch >
st.uc.epoch` deallocation exit, and `VmPreserved` `msg.epoch < st.uc.epoch` branch for
`.keysSampled` (`+1796`, Block `332`).
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 400000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

namespace LibsignalBinary.Proofs.SpqrV1.States.Recv.ArmKeysSampled1PlacedBudget

open Arm64 ProofLib ProofLib.ProgramReflection
open CryptoGames.LibsignalSession (ShaCompress)
open CryptoVerification
open CryptoVerification.RustHeap
open CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalTripleRatchetRepr
open CryptoVerification.LibsignalSpqrV1
open CryptoVerification.SpqrV1
open CryptoVerification.SpqrV1.Alloc
open CryptoVerification.SpqrV1.Auth
open CryptoVerification.SpqrV1.Poly
open CryptoVerification.SpqrV1.Poly.AddChunk
open CryptoVerification.SpqrV1.Drop
open CryptoVerification.SpqrV1.States
open CryptoVerification.SpqrV1.States.Leaves
open CryptoVerification.SpqrV1.States.RecvCt2Chunk
open CryptoVerification.SpqrV1.States.Recv
open CryptoVerification.SpqrV1.Top
open CryptoVerification.SpqrV1.Top.MessageSerialize
open CryptoVerification.CodeLayout
open LibsignalBinary.Heap (
  AllocCallPreserved AllocCostModel AllocEvent BudgetLimits FreeOnlyEvs
  RustCliAllocBudget VmPreserved rustCliDeallocBudgetSpec
)
open LibsignalBinary.Heap.SpecBudget (withVmPreserved)
open LibsignalBinary.Proofs.SpqrV1.States.Recv.ArmNoHeaderReceivedStepsPlacedBudgetAux (
  seq_vm_cont
)

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

/-! ## 1. `.keysSampled` (`+1796`, Block `332`): Post-Call Writeback & `>` / `<` Arms -/

set_option maxHeartbeats 1200000 in
/-- Relocatable post-call writeback block (`+7748 -> s0.x30`, Block `332`) after
    `<KeysSampled>::recv_ct1_chunk` returns `outSt` at `fsp + 1856#64`, with `VmPreserved s sf`. -/
theorem keysSampled_post_call_57298_placed [LibsignalPlacement] {A : RustAlloc} {F : ShaCompress}
    {ext : String → Option (State → State)}
    (hmemcpy_sat : HookSat (Rust.withPanics ext) spqrMemcpySym (withVmPreserved sessionMemcpySpec))
    (s0 s : State) (outA : BitVec 64)
    (outSt : Chunked.SendEk.HeaderSent spqrPolyApi (spqrAuthApi F))
    (sp : SendEkSpills) (P_rest : SepProp)
    (hpc : s.pc = lsmpl.base 332 + 7748#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = s0.sp - 4240#64)
    (hsp_align : s0.spAligned = true)
    (hx19 : s.readReg64 .x19 = outA)
    (hx20 : s.readReg64 .x20 = (s0.sp - 4240#64) + 1856#64)
    (htr : TraceCalleeSaved s s0) :
    SepWP (lsProg_332 (Rust.withPanics ext)) (s0.readReg64 .x30) s
      (P_rest ∗
        memRegion outA v1RecvSize ∗
        stackAt (s0.sp - 4240#64) statesRecvCalleeStackX ∗
        sendEkSpillsAt (s0.sp - 4240#64) sp ∗
        memRegion ((s0.sp - 4240#64) + 576#64) 376 ∗
        memRegion ((s0.sp - 4240#64) + 976#64) 880 ∗
        chunkedHeaderSentAt A ((s0.sp - 4240#64) + 1856#64) outSt ∗
        sendEkUnusedAt (s0.sp - 4240#64) ∗
        statesRecvSavedCells s0)
      (fun sf Pf =>
        VmPreserved s sf ∧
        (Pf ⊢
          P_rest ∗
          resultV1RecvAt A (F := F) outA (.ok { key := none, state := .headerSent outSt }) ∗
          stackAt s0.sp statesRecvStackX) ∧
        sf.sp = s0.sp ∧
        CalleeSavedPreserved s0 sf ∧
        sf.trace = s0.trace) := by
  have hmemcpy : subroutine_ok (lsProg_332 (Rust.withPanics ext))
      (lsρ memcpyName) (withVmPreserved (sessionMemcpySpec 4096)) := spqr_hook_ok_of_mem hmemcpy_sat
  rw [lsmpl_base_332_eq] at hpc
  dsimp only [lsProg_332, lsρ, memcpyName, BitVec.ofNat_eq_ofNat] at hpc hmemcpy ⊢
  refine SepWP.fold (chunkedHeaderSentAt_extract63_376 A ((s0.sp - 4240#64) + 1856#64) outSt)
    (by sep_focus) ?_
  wp_pull_exists; rename_i w_out tailBytes
  refine SepWP.pure_elim fun ⟨hw62, htail_len⟩ => ?_
  have hrel_tail := Relocatable.of_pointsToBytes tailBytes htail_len
  have hwb := @ArmNoHeaderReceivedStepsPlacedBudgetAux.states_recv_writeback_59e88_sat_placed _ ext hmemcpy_sat
    (F_tail := fun a => a ↦ₛ tailBytes) hrel_tail s0
  rw [lsmpl_base_332_eq] at hwb
  dsimp only [lsProg_332, BitVec.ofNat_eq_ofNat] at hwb
  have hsp_align' : (s0.sp &&& 15#64 == 0#64) = true := hsp_align
  have hfsp_align : ((s0.sp - 4240#64) &&& 15#64 == 0#64) = true :=
    spAligned_sub s0.sp 4240#64 hsp_align (by decide)
  have h2360 : (s0.sp - 4240#64) + 1856#64 + 504#64 = (s0.sp - 4240#64) + 2360#64 := by bv_omega
  rw [h2360]
  refine seq_vm_cont (mid := lsmpl.ρ "memcpy") ?_
  by_vm_steps_nest (
    generalize hsp0 : s0.sp = sp0 at hsp hsp_align' hfsp_align hx20 ⊢
    wp_conv_pre =>
      dsimp only [sendEkSpillsAt, words63At, words10At]
      simp only [pointsTo128_eq_pair64_recv, BitVec.add_assoc, arm64_norm]
    wp_steps 200
    refine SepWP.done rfl (by assumption) ⟨by simp only [wp_norm, arm64_norm], fun hvm1 => ?_⟩
    rw [stackAt_statesRecvCallee_eq_allocHook (sp0 - 4240#64)]
    dsimp only [allocHookStack]
    refine ArmNoHeaderReceivedStepsPlacedBudgetAux.call_memcpy_relocate_cs_stack
      (ret_pc := (blkPl_332).base + 8156#64)
      hmemcpy hrel_tail (sp0 - 3664#64) (sp0 - 1880#64)
      rfl (by assumption) (by simp only [wp_norm, arm64_norm, hsp]) hfsp_align rfl
      ⟨by simp only [wp_norm, arm64_norm]; exact htr.1,
       by simp only [wp_norm, arm64_norm]; exact htr.2⟩ rfl
      (by simp only [Reg.x1, wp_norm, arm64_norm, hx20])
      rfl (by sep_focus) ?_
    intro sf1 hpc1 hrun1 hsp1 hvm_mc hcs1 htr1
    have hx19_1 : sf1.readReg64 .x19 = outA :=
      hcs1.1.trans (by simp only [Reg.x19, wp_norm, arm64_norm, hx19])
    have hx20_1 : sf1.readReg64 .x20 = sp0 - 2384#64 :=
      hcs1.2.1.trans (by simp only [Reg.x20, wp_norm, arm64_norm, hx20])
    have hx21_1 : sf1.readReg64 .x21 = w_out.b1.w5 :=
      hcs1.2.2.1.trans (by simp only [Reg.x21, wp_norm, arm64_norm])
    have hx22_1 : sf1.readReg64 .x22 = w_out.b5.w2 :=
      hcs1.2.2.2.1.trans (by simp only [Reg.x22, wp_norm, arm64_norm])
    have hx23_1 : sf1.readReg64 .x23 = w_out.b2.w9 :=
      hcs1.2.2.2.2.1.trans (by simp only [Reg.x23, wp_norm, arm64_norm])
    have hx24_1 : sf1.readReg64 .x24 = w_out.b4.w1 :=
      hcs1.2.2.2.2.2.1.trans (by simp only [Reg.x24, wp_norm, arm64_norm])
    have hx25_1 : sf1.readReg64 .x25 = w_out.b3.w2 :=
      hcs1.2.2.2.2.2.2.1.trans (by simp only [Reg.x25, wp_norm, arm64_norm])
    have hx26_1 : sf1.readReg64 .x26 = w_out.b1.w6 :=
      hcs1.2.2.2.2.2.2.2.1.trans (by simp only [Reg.x26, wp_norm, arm64_norm])
    have hx27_1 : sf1.readReg64 .x27 = w_out.b5.w0 :=
      hcs1.2.2.2.2.2.2.2.2.1.trans (by simp only [Reg.x27, wp_norm, arm64_norm])
    have hx28_1 : sf1.readReg64 .x28 = w_out.b1.w8 :=
      hcs1.2.2.2.2.2.2.2.2.2.1.trans (by simp only [Reg.x28, wp_norm, arm64_norm])
    refine seq_vm_cont (mid := (blkPl_332).base + 18996#64) ?_
    by_vm_steps_nest (
      wp_steps
      subst hsp0
      refine SepWP.done rfl (by assumption) ⟨by simp only [wp_norm, arm64_norm], fun hvm2 => ?_⟩
      let sp1 : SendEkSpills :=
        { b0 := ⟨sp.b0.w0, w_out.b3.w5, w_out.b3.w1, sp.b0.w3, sp.b0.w4, sp.b0.w5, w_out.b4.w0,
                 w_out.b3.w8, w_out.b3.w4, w_out.b3.w3⟩
          b1 := ⟨w_out.b5.w7, w_out.b5.w5, w_out.b3.w9, w_out.b3.w6, w_out.b5.w3, w_out.b3.w7,
                 w_out.b0.w0, outSt.uc.epoch, sp.b1.w8, sp.b1.w9⟩
          b2 := ⟨w_out.b4.w7, w_out.b5.w1, w_out.b4.w9, w_out.b4.w3, w_out.b4.w5, w_out.b0.w1,
                 w_out.b4.w8, 4#64, noneCap, w_out.b4.w2⟩
          b3 := ⟨w_out.b5.w8, w_out.w62, w_out.b1.w8, w_out.b2.w1, w_out.b2.w7, w_out.b0.w7,
                 w_out.b1.w3, w_out.b2.w5, w_out.b3.w0, w_out.b2.w8⟩
          b4 := ⟨w_out.b2.w6, w_out.b1.w2, w_out.b1.w9, w_out.b1.w0, w_out.b2.w2, w_out.b0.w5,
                 w_out.b0.w4, w_out.b1.w1, w_out.b2.w0, w_out.b2.w3⟩
          b5 := ⟨w_out.b0.w9, w_out.b4.w4, w_out.b1.w4, w_out.b0.w8, w_out.b1.w7, w_out.b5.w0,
                 w_out.b0.w3, w_out.b2.w4, w_out.b4.w6, w_out.b5.w4⟩
          w60 := w_out.b5.w6, w61 := w_out.b0.w2, w62 := w_out.b0.w6
          q200 := sp.q200, q210 := sp.q210, q220 := sp.q220, w230 := sp.w230, q3c0 := w_out.q60 }
      have h1880 : s0.sp - 1880#64 = (s0.sp - 4240#64) + 2360#64 := by bv_omega
      have h3664 : s0.sp - 3664#64 = (s0.sp - 4240#64) + 576#64 := by bv_omega
      rw [h1880, h3664]
      have hfold_sp1 :
          (words63At ((s0.sp - 4240#64) + 1856#64) w_out ∗
           memRegion ((s0.sp - 4240#64) + 2360#64) 376) ∗
          sendEkSpillsAt (s0.sp - 4240#64) sp1 ⊢
            memRegion ((s0.sp - 4240#64) + 1856#64) 880 ∗
            sendEkSpillsAt (s0.sp - 4240#64) sp1 :=
        sepConj_mono_left (words63At_376_entails_memRegion_880
          ((s0.sp - 4240#64) + 1856#64) ((s0.sp - 4240#64) + 2360#64) w_out (by bv_omega))
      refine SepWP.fold
        (F := P_rest ∗
          relocatedHeap (fun dst => chunkedHeaderSentAt A dst outSt) (wordsBytes (words63List w_out) ++ tailBytes) ∗
          memRegion outA v1RecvSize ∗ stackAt (s0.sp - 4240#64) statesRecvCalleeStackX ∗
          (((s0.sp - 4240#64) + 576#64) ↦ₛ tailBytes) ∗ memRegion ((s0.sp - 4240#64) + 976#64) 880 ∗
          sendEkUnusedAt (s0.sp - 4240#64) ∗ statesRecvSavedCells s0)
        hfold_sp1 ?_ ?_
      · rw [stackAt_statesRecvCallee_eq_allocHook (s0.sp - 4240#64)]
        dsimp only [allocHookStack, sendEkSpillsAt, words63At, words10At, sp1]
        simp only [pointsTo128_eq_pair64_recv, BitVec.add_assoc, arm64_norm]
        sep_ac_rfl
      · rw [show (memRegion ((s0.sp - 4240#64) + 1856#64) 880 ∗ sendEkSpillsAt (s0.sp - 4240#64) sp1) ∗
            (P_rest ∗
              relocatedHeap (fun dst => chunkedHeaderSentAt A dst outSt) (wordsBytes (words63List w_out) ++ tailBytes) ∗
              memRegion outA v1RecvSize ∗ stackAt (s0.sp - 4240#64) statesRecvCalleeStackX ∗
              (((s0.sp - 4240#64) + 576#64) ↦ₛ tailBytes) ∗ memRegion ((s0.sp - 4240#64) + 976#64) 880 ∗
              sendEkUnusedAt (s0.sp - 4240#64) ∗ statesRecvSavedCells s0) =
            (P_rest ∗
              relocatedHeap (fun dst => chunkedHeaderSentAt A dst outSt) (wordsBytes (words63List w_out) ++ tailBytes)) ∗
            memRegion outA v1RecvSize ∗ stackAt (s0.sp - 4240#64) statesRecvCalleeStackX ∗
            sendEkSpillsAt (s0.sp - 4240#64) sp1 ∗ (((s0.sp - 4240#64) + 576#64) ↦ₛ tailBytes) ∗
            memRegion ((s0.sp - 4240#64) + 976#64) 880 ∗ memRegion ((s0.sp - 4240#64) + 1856#64) 880 ∗
            sendEkUnusedAt (s0.sp - 4240#64) ∗ statesRecvSavedCells s0 by sep_ac_rfl]
        refine SepWP.mono
          (hwb _ outA sp1
            (P_rest ∗ relocatedHeap (fun dst => chunkedHeaderSentAt A dst outSt) (wordsBytes (words63List w_out) ++ tailBytes))
            rfl (by assumption) (by simp only [wp_norm, arm64_norm, hsp1]) hsp_align
            (by simp only [Reg.x19, wp_norm, arm64_norm, hx19_1])
            ⟨by simp only [wp_norm, arm64_norm]; exact htr1.1,
             by simp only [wp_norm, arm64_norm]; exact htr1.2⟩)
          (fun sf Pf _ _ ⟨hvm_wb, hPf, hsp_sf, hcs_sf, htr_sf⟩ =>
            ⟨hvm1.trans (hvm_mc.trans (hvm2.trans hvm_wb)), ?_, hsp_sf, hcs_sf, htr_sf⟩)
        refine Entails.trans hPf ?_
        have hrec := writeback_headerSent_entails_resultV1RecvAt A (F := F) outA outSt w_out tailBytes
          w_out.b5.w9 sp.q200
        refine Entails.trans (Entails.of_eq ?_)
          (sepConj_mono_right (sepConj_mono_left hrec))
        dsimp only [writebackWords63, sp1, Reg.x0, Reg.x1, Reg.x2, Reg.x3, Reg.x4, Reg.x5, Reg.x6,
          Reg.x7, Reg.x8, Reg.x9, Reg.x10, Reg.x11, Reg.x12, Reg.x13, Reg.x14, Reg.x15, Reg.x16,
          Reg.x17, Reg.x20, Reg.x21, Reg.x22, Reg.x23, Reg.x24, Reg.x25, Reg.x26, Reg.x27, Reg.x28,
          Reg.x30]
        simp only [wp_norm, arm64_norm, hx21_1, hx22_1, hx23_1, hx24_1, hx25_1, hx26_1, hx27_1, hx28_1, ← hw62]
        sep_ac_rfl
    )
  )

set_option maxHeartbeats 1200000 in
/-- Budget-threaded relocatable `.keysSampled` arm when `msg.epoch > st.uc.epoch`
    (`+1796 -> s0.x30`, Block `332`). -/
theorem keysSampled_arm_gt_placed [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits} {F : ShaCompress}
    {ext : String → Option (State → State)}
    (hdealloc : HookSat (Rust.withPanics ext) spqrDeallocSym (rustCliDeallocBudgetSpec M A lim))
    (st_cost : M.σ)
    (s0 s : State) (outA selfA msgA : BitVec 64)
    (st : Chunked.SendEk.KeysSampled spqrPolyApi (spqrAuthApi F))
    (msg : Message spqrPolyApi)
    (P_rest : SepProp)
    (hgt : msg.epoch > st.uc.epoch)
    (hcl : LibsignalCodeLoaded lsmpl s.mem)
    (hpc : s.pc = lsmpl.base 332 + 1796#64)
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
        chunkedStatesAt A.repAlloc selfA (.keysSampled st) ∗
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
  have hepilogue := @ArmNoHeaderReceivedStepsPlacedBudgetAux.states_recv_epilogue_59fd0_acp_placed _ ext s0
  rw [lsmpl_base_332_eq] at hpc hepilogue
  dsimp only [lsProg_332, chunkedCt1ReceivedSize,
    chunkedStatesAt, messageAt, BitVec.ofNat_eq_ofNat] at hpc hepilogue ⊢
  refine seq_vm_cont_lscl hcl (mid := lsmpl.base 277) ?_
  rw [memRegion_out_960_split_err outA]
  wp_pull_exists; rename_i v0 b8 v16
  refine SepWP.fold (memRegion_4144_entails_sendEkFrame (s0.sp - 4240#64)) (by sep_focus) ?_
  wp_pull_exists; rename_i sp
  refine SepWP.fold (sendEkUnusedAt_split_ac0 (s0.sp - 4240#64)) (by sep_focus) ?_
  wp_pull_exists; rename_i u_ac0
  refine SepWP.fold (chunkedKeysSampledAt_extract63 A.repAlloc (selfA + 8#64) st) (by sep_focus) ?_
  wp_pull_exists; rename_i w
  refine SepWP.pure_elim fun hw62 => ?_
  have hsp_align' : (s0.sp &&& 15#64 == 0#64) = true := hsp_align
  have hfsp_align : ((s0.sp - 4240#64) &&& 15#64 == 0#64) = true :=
    spAligned_sub s0.sp 4240#64 hsp_align (by decide)
  by_vm_steps_nest (
    generalize hsp0 : s0.sp = sp0 at hsp hsp_align' hfsp_align ⊢
    wp_conv_pre =>
      dsimp only [sendEkSpillsAt, words63At, words10At]
      rw [hw62]
      simp only [pointsTo128_eq_pair64_recv, BitVec.add_assoc, arm64_norm]
    wp_steps 200
    subst hsp0
    refine SepWP.done rfl (by assumption) ⟨by simp only [wp_norm, arm64_norm], fun hcl1 hvm1 => ?_⟩
    have hdrop_raw := DropChunkedClPlacedBudget.drop_chunked_ct1_received_mem_on (F := F)
      (callerProg := (blkPC_332).rebase (blkPl_332).base (Rust.withPanics ext)) hdealloc hcl1
    dsimp only [withMemEq, LibsignalBinary.Proofs.SpqrV1.Drop.ChunkedBudget.dropChunkedCt1ReceivedSpec,
      chunkedCt1ReceivedSize, BitVec.ofNat_eq_ofNat] at hdrop_raw
    let sp1 : SendEkSpills :=
      { b0 := ⟨sp.b0.w0, sp.b0.w1, sp.b0.w2, sp.b0.w3, sp.b0.w4, sp.b0.w5, sp.b0.w6, sp.b0.w7,
               sp.b0.w8, sp.b0.w9⟩
        b1 := ⟨w.b5.w7, w.b5.w5, w.b3.w9, sp.b1.w3, w.b5.w3, sp.b1.w5, w.b0.w0, w.b5.w9,
               w.b1.w5, w.b1.w6⟩
        b2 := ⟨w.b4.w7, w.b5.w1, w.b4.w9, sp.b2.w3, w.b4.w5, w.b0.w1, w.b4.w8, sp.b2.w7,
               sp.b2.w8, w.b4.w2⟩
        b3 := ⟨w.b5.w8, w.w62, sp.b3.w2, sp.b3.w3, w.b2.w7, w.b0.w7, w.b1.w3, w.b2.w5,
               w.b3.w0, w.b2.w8⟩
        b4 := ⟨w.b2.w6, sp.b4.w1, w.b1.w9, w.b1.w0, w.b2.w2, w.b0.w5, sp.b4.w6, w.b1.w1,
               w.b2.w0, w.b2.w3⟩
        b5 := ⟨w.b0.w9, sp.b5.w1, w.b1.w4, w.b0.w8, w.b1.w7, sp.b5.w5, sp.b5.w6, w.b2.w4,
               w.b4.w6, w.b5.w4⟩
        w60 := w.b5.w6, w61 := w.b0.w2, w62 := w.b0.w6
        q200 := sp.q200, q210 := sp.q210, q220 := sp.q220, w230 := sp.w230, q3c0 := sp.q3c0 }
    have hfold_unused :
        ((s0.sp - 4240#64 + 2752#64) ↦₁₂₈ w.q60) ∗
        memRegion (s0.sp - 4240#64) 8 ∗ memRegion (s0.sp - 4240#64 + 568#64) 8 ∗
        memRegion (s0.sp - 4240#64 + 952#64) 8 ∗ memRegion (s0.sp - 4240#64 + 2736#64) 16 ∗
        memRegion (s0.sp - 4240#64 + 2768#64) 1376 ⊢
          sendEkUnusedAt (s0.sp - 4240#64) :=
      sendEkUnusedAt_rejoin_ac0 (s0.sp - 4240#64) w.q60
    have hfold_frame :
        (words63At (selfA + 8#64) w ∗
         relocatedHeap (fun dst => chunkedKeysSampledAt A.repAlloc dst st) (wordsBytes (words63List w))) ∗
        (sendEkSpillsAt (s0.sp - 4240#64) sp1 ∗
         memRegion ((s0.sp - 4240#64) + 576#64) 376 ∗
         memRegion ((s0.sp - 4240#64) + 976#64) 880 ∗
         memRegion ((s0.sp - 4240#64) + 1856#64) 880 ∗
         (((s0.sp - 4240#64 + 2752#64) ↦₁₂₈ w.q60) ∗
          memRegion (s0.sp - 4240#64) 8 ∗ memRegion (s0.sp - 4240#64 + 568#64) 8 ∗
          memRegion (s0.sp - 4240#64 + 952#64) 8 ∗ memRegion (s0.sp - 4240#64 + 2736#64) 16 ∗
          memRegion (s0.sp - 4240#64 + 2768#64) 1376)) ⊢
          chunkedCt1ReceivedAt A.repAlloc (selfA + 8#64) (chunkedKeysSampledToCt1Received st) ∗
          memRegion (s0.sp - 4240#64) 4144 :=
      sepConj_mono (words63_keysSampled_entails_ct1ReceivedAt A.repAlloc (selfA + 8#64) st w)
        (Entails.trans
          (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right hfold_unused))))
          (sendEkFrame_entails_memRegion_4144 (s0.sp - 4240#64) sp1))
    refine SepWP.fold
      (F := P_rest ∗
        ((outA ↦₆₄ noneCap) ∗ ((outA + 8#64) ↦₈ 4#8) ∗ memRegion (outA + 9#64) 7 ∗
         ((outA + 16#64) ↦₆₄ msg.epoch) ∗ memRegion (outA + 24#64) 936) ∗
        (selfA ↦₆₄ 3#64) ∗ memRegion (selfA + 512#64) 416 ∗
        ((msgA ↦₆₄ msg.epoch) ∗ messagePayloadAt spqrPolyApi msgA msg.payload) ∗
        A.pool lim st_cost s ∗ stackAt (s0.sp - 4240#64) statesRecvCalleeStackX ∗
        statesRecvSavedCells s0)
      hfold_frame ?_ ?_
    · rw [← hw62]
      dsimp only [sendEkSpillsAt, words63At, words10At, sp1]
      simp only [pointsTo128_eq_pair64_recv, BitVec.add_assoc, arm64_norm]
      sep_ac_rfl
    · wp_conv_pre => rw [← A.pool_of_vmPreserved hvm1]
      have hsplit_sp := stackAt_statesRecvCallee_split_dropStack32 (s0.sp - 4240#64)
      refine SepWP.focus_weaken (Entails.of_eq hsplit_sp) (by sep_focus) ?_
      wp_call hdrop_raw (⟨selfA + 8#64, chunkedKeysSampledToCt1Received st⟩, st_cost)
      have hacp12 : AllocCallPreserved s sf := by assumption
      have hevs_d : FreeOnlyEvs w_1 := by assumption
      have hsp_sf1 : sf.sp = s0.sp - 4240#64 := by
        refine Eq.trans (by assumption) ?_
        try simp only [wp_norm, arm64_norm]
        exact hsp
      have htr_sf : TraceCalleeSaved sf s0 :=
        ⟨Eq.trans (by assumption) htr.1, Eq.trans (by assumption) htr.2⟩
      wp_conv_pre => rw [hsp]
      refine SepWP.focus_weaken (Entails.of_eq hsplit_sp.symm) (by sep_focus) ?_
      refine seq_vm_cont (mid := (blkPl_332).base + 19324#64) ?_
      by_vm_steps_nest (
        wp_steps
        refine SepWP.done rfl (by assumption) ⟨by simp only [wp_norm, arm64_norm], fun hvm2 => ?_⟩
        have hacp_step :=
          acpOfVm hvm2 (by simp only [AllocCallPreserved, wp_norm, arm64_norm])
        refine SepWP.fold
          (F := P_rest ∗ ((msgA ↦₆₄ msg.epoch) ∗ messagePayloadAt spqrPolyApi msgA msg.payload) ∗
            A.pool lim (M.stepEvents w_1 st_cost) sf ∗ stackAt (s0.sp - 4240#64) statesRecvCalleeStackX ∗
            memRegion (s0.sp - 4240#64) 4144 ∗ statesRecvSavedCells s0)
          (sepConj_mono
            (err_epochOutOfRange_entails_resultV1RecvAt A.repAlloc (F := F) outA msg.epoch)
            (self_504_416_entails_memRegion_928 selfA 3#64))
          (by sep_ac_rfl) ?_
        rw [show (resultV1RecvAt A.repAlloc (F := F) outA (.error (.err (.epochOutOfRange msg.epoch))) ∗
              memRegion selfA chunkedStatesSize) ∗
            (P_rest ∗ ((msgA ↦₆₄ msg.epoch) ∗ messagePayloadAt spqrPolyApi msgA msg.payload) ∗
              A.pool lim (M.stepEvents w_1 st_cost) sf ∗ stackAt (s0.sp - 4240#64) statesRecvCalleeStackX ∗
              memRegion (s0.sp - 4240#64) 4144 ∗ statesRecvSavedCells s0) =
            (P_rest ∗ resultV1RecvAt A.repAlloc (F := F) outA (.error (.err (.epochOutOfRange msg.epoch))) ∗
              memRegion selfA chunkedStatesSize ∗
              ((msgA ↦₆₄ msg.epoch) ∗ messagePayloadAt spqrPolyApi msgA msg.payload) ∗
              A.pool lim (M.stepEvents w_1 st_cost) sf) ∗
            stackAt (s0.sp - 4240#64) statesRecvCalleeStackX ∗
            memRegion (s0.sp - 4240#64) 4144 ∗
            statesRecvSavedCells s0 by sep_ac_rfl]
        wp_conv_pre => rw [← A.pool_of_vmPreserved hvm2]
        refine SepWP.mono
          (hepilogue (vmMid hvm2)
            (P_rest ∗ resultV1RecvAt A.repAlloc (F := F) outA (.error (.err (.epochOutOfRange msg.epoch))) ∗
              memRegion selfA chunkedStatesSize ∗
              ((msgA ↦₆₄ msg.epoch) ∗ messagePayloadAt spqrPolyApi msgA msg.payload) ∗
              A.pool lim (M.stepEvents w_1 st_cost) (vmMid hvm2))
            rfl (by assumption) (by simp only [wp_norm, arm64_norm, hsp_sf1])
            hsp_align
            ⟨by simp only [wp_norm, arm64_norm]; exact htr_sf.1,
             by simp only [wp_norm, arm64_norm]; exact htr_sf.2⟩)
          (fun sf_ret Pf _ _ ⟨hvm_ep, hPf, hsp_sf, hacp_ep, hcs_sf, htr_ret⟩ =>
            ⟨w_1, hevs_d,
              by
                rw [A.pool_of_vmPreserved hvm_ep]
                exact Entails.trans hPf (Entails.of_eq (by sep_ac_rfl)),
              hsp_sf, hacp12.trans (hacp_step.trans hacp_ep), hcs_sf, htr_ret⟩)
      )
  )

set_option maxHeartbeats 1200000 in
/-- Relocatable `.keysSampled` arm when `msg.epoch < st.uc.epoch`
    (`+1796 -> s0.x30`, Block `332`) with `VmPreserved s sf`. -/
theorem keysSampled_arm_lt_placed [LibsignalPlacement]
    {A : RustAlloc} {F : ShaCompress} {ext : String → Option (State → State)}
    (hmemcpy_sat : HookSat (Rust.withPanics ext) spqrMemcpySym (withVmPreserved sessionMemcpySpec))
    (s0 s : State) (outA selfA msgA : BitVec 64)
    (st : Chunked.SendEk.KeysSampled spqrPolyApi (spqrAuthApi F))
    (msg : Message spqrPolyApi)
    (P_rest : SepProp)
    (hlt : msg.epoch < st.uc.epoch)
    (hpc : s.pc = lsmpl.base 332 + 1796#64)
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
        chunkedStatesAt A selfA (.keysSampled st) ∗
        messageAt spqrPolyApi msgA msg ∗
        A.pool ∗
        stackAt (s0.sp - 4240#64) statesRecvCalleeStackX ∗
        memRegion (s0.sp - 4240#64) 4144 ∗
        statesRecvSavedCells s0)
      (fun sf Pf =>
        VmPreserved s sf ∧
        (Pf ⊢
          P_rest ∗
          resultV1RecvAt A (F := F) outA (.ok { key := none, state := .keysSampled st }) ∗
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
  have hwb := @ArmNoHeaderReceivedStepsPlacedBudgetAux.states_recv_writeback_59e88_sat_placed _ ext hmemcpy_sat
    (F_tail := fun a => memRegion a 376) (Relocatable.of_memRegion 376) s0
  rw [lsmpl_base_332_eq] at hpc hwb
  dsimp only [lsProg_332, chunkedStatesAt, messageAt, BitVec.ofNat_eq_ofNat] at hpc hwb ⊢
  refine seq_vm_cont (mid := (blkPl_332).base + 18996#64) ?_
  refine SepWP.fold (memRegion_4144_entails_sendEkFrame (s0.sp - 4240#64)) (by sep_focus) ?_
  wp_pull_exists; rename_i sp
  refine SepWP.fold (sendEkUnusedAt_split_ac0 (s0.sp - 4240#64)) (by sep_focus) ?_
  wp_pull_exists; rename_i u_ac0
  refine SepWP.fold (chunkedKeysSampledAt_extract63 A (selfA + 8#64) st) (by sep_focus) ?_
  wp_pull_exists; rename_i w
  refine SepWP.pure_elim fun hw62 => ?_
  have hsp_align' : (s0.sp &&& 15#64 == 0#64) = true := hsp_align
  have hfsp_align : ((s0.sp - 4240#64) &&& 15#64 == 0#64) = true :=
    spAligned_sub s0.sp 4240#64 hsp_align (by decide)
  by_vm_steps_nest (
    generalize hsp0 : s0.sp = sp0 at hsp hsp_align' hfsp_align ⊢
    wp_conv_pre =>
      dsimp only [sendEkSpillsAt, words63At, words10At]
      rw [hw62]
      simp only [pointsTo128_eq_pair64_recv, BitVec.add_assoc, arm64_norm]
    wp_steps 256
    subst hsp0
    refine SepWP.done rfl (by assumption) ⟨by simp only [wp_norm, arm64_norm], fun hvm1 => ?_⟩
    let sp1 : SendEkSpills :=
      { b0 := ⟨sp.b0.w0, sp.b0.w1, sp.b0.w2, sp.b0.w3, sp.b0.w4, sp.b0.w5, sp.b0.w6, sp.b0.w7,
               sp.b0.w8, sp.b0.w9⟩
        b1 := ⟨w.b5.w7, w.b5.w5, w.b3.w9, sp.b1.w3, w.b5.w3, w.b3.w7, w.b0.w0, w.b5.w9,
               w.b1.w5, w.b1.w6⟩
        b2 := ⟨w.b4.w7, w.b5.w1, w.b4.w9, w.b4.w3, w.b4.w5, w.b0.w1, w.b4.w8, 3#64,
               noneCap, w.b4.w2⟩
        b3 := ⟨w.b5.w8, w.w62, w.b1.w8, w.b2.w1, w.b2.w7, w.b0.w7, w.b1.w3, w.b2.w5,
               w.b3.w0, w.b2.w8⟩
        b4 := ⟨w.b2.w6, w.b1.w2, w.b1.w9, w.b1.w0, w.b2.w2, w.b0.w5, w.b0.w4, w.b1.w1,
               w.b2.w0, w.b2.w3⟩
        b5 := ⟨w.b0.w9, w.b4.w4, w.b1.w4, w.b0.w8, w.b1.w7, w.b5.w0, w.b0.w3, w.b2.w4,
               w.b4.w6, w.b5.w4⟩
        w60 := w.b5.w6, w61 := w.b0.w2, w62 := w.b0.w6
        q200 := sp.q200, q210 := sp.q210, q220 := sp.q220, w230 := sp.w230, q3c0 := w.q60 }
    have hfold_unused :
        ((s0.sp - 4240#64 + 2752#64) ↦₁₂₈ w.q60) ∗
        memRegion (s0.sp - 4240#64) 8 ∗ memRegion (s0.sp - 4240#64 + 568#64) 8 ∗
        memRegion (s0.sp - 4240#64 + 952#64) 8 ∗ memRegion (s0.sp - 4240#64 + 2736#64) 16 ∗
        memRegion (s0.sp - 4240#64 + 2768#64) 1376 ⊢
          sendEkUnusedAt (s0.sp - 4240#64) :=
      sendEkUnusedAt_rejoin_ac0 (s0.sp - 4240#64) w.q60
    have hfold_self_unused :
        ((selfA ↦₆₄ 3#64) ∗ words63At (selfA + 8#64) w ∗ memRegion (selfA + 512#64) 416) ∗
        (((s0.sp - 4240#64 + 2752#64) ↦₁₂₈ w.q60) ∗
         memRegion (s0.sp - 4240#64) 8 ∗ memRegion (s0.sp - 4240#64 + 568#64) 8 ∗
         memRegion (s0.sp - 4240#64 + 952#64) 8 ∗ memRegion (s0.sp - 4240#64 + 2736#64) 16 ∗
         memRegion (s0.sp - 4240#64 + 2768#64) 1376) ∗
        sendEkSpillsAt (s0.sp - 4240#64) sp1 ⊢
          memRegion selfA chunkedStatesSize ∗
          sendEkUnusedAt (s0.sp - 4240#64) ∗
          sendEkSpillsAt (s0.sp - 4240#64) sp1 :=
      sepConj_mono (words63At_self_entails_memRegion_928 selfA 3#64 w)
        (sepConj_mono_left hfold_unused)
    refine SepWP.fold
      (F := P_rest ∗
        relocatedHeap (fun dst => chunkedKeysSampledAt A dst st) (wordsBytes (words63List w)) ∗
        ((msgA ↦₆₄ msg.epoch) ∗ messagePayloadAt spqrPolyApi msgA msg.payload) ∗ A.pool ∗
        memRegion outA v1RecvSize ∗ stackAt (s0.sp - 4240#64) statesRecvCalleeStackX ∗
        memRegion ((s0.sp - 4240#64) + 576#64) 376 ∗ memRegion ((s0.sp - 4240#64) + 976#64) 880 ∗
        memRegion ((s0.sp - 4240#64) + 1856#64) 880 ∗ statesRecvSavedCells s0)
      hfold_self_unused ?_ ?_
    · rw [← hw62]
      dsimp only [sendEkSpillsAt, words63At, words10At, sp1]
      simp only [pointsTo128_eq_pair64_recv, BitVec.add_assoc, arm64_norm]
      sep_ac_rfl
    · rw [show (memRegion selfA chunkedStatesSize ∗
            sendEkUnusedAt (s0.sp - 4240#64) ∗
            sendEkSpillsAt (s0.sp - 4240#64) sp1) ∗
          (P_rest ∗
            relocatedHeap (fun dst => chunkedKeysSampledAt A dst st) (wordsBytes (words63List w)) ∗
            ((msgA ↦₆₄ msg.epoch) ∗ messagePayloadAt spqrPolyApi msgA msg.payload) ∗ A.pool ∗
            memRegion outA v1RecvSize ∗ stackAt (s0.sp - 4240#64) statesRecvCalleeStackX ∗
            memRegion ((s0.sp - 4240#64) + 576#64) 376 ∗ memRegion ((s0.sp - 4240#64) + 976#64) 880 ∗
            memRegion ((s0.sp - 4240#64) + 1856#64) 880 ∗ statesRecvSavedCells s0) =
          (P_rest ∗
            relocatedHeap (fun dst => chunkedKeysSampledAt A dst st) (wordsBytes (words63List w)) ∗
            memRegion selfA chunkedStatesSize ∗
            ((msgA ↦₆₄ msg.epoch) ∗ messagePayloadAt spqrPolyApi msgA msg.payload) ∗ A.pool) ∗
          memRegion outA v1RecvSize ∗ stackAt (s0.sp - 4240#64) statesRecvCalleeStackX ∗
          sendEkSpillsAt (s0.sp - 4240#64) sp1 ∗ memRegion ((s0.sp - 4240#64) + 576#64) 376 ∗
          memRegion ((s0.sp - 4240#64) + 976#64) 880 ∗ memRegion ((s0.sp - 4240#64) + 1856#64) 880 ∗
          sendEkUnusedAt (s0.sp - 4240#64) ∗ statesRecvSavedCells s0 by sep_ac_rfl]
      refine SepWP.mono
        (hwb _ outA sp1
          (P_rest ∗
            relocatedHeap (fun dst => chunkedKeysSampledAt A dst st) (wordsBytes (words63List w)) ∗
            memRegion selfA chunkedStatesSize ∗
            ((msgA ↦₆₄ msg.epoch) ∗ messagePayloadAt spqrPolyApi msgA msg.payload) ∗ A.pool)
          rfl (by assumption) (by simp only [wp_norm, arm64_norm, hsp]) hsp_align
          (by simp only [Reg.x19, wp_norm, arm64_norm, hx19])
          ⟨by simp only [wp_norm, arm64_norm]; exact htr.1,
           by simp only [wp_norm, arm64_norm]; exact htr.2⟩)
        (fun sf Pf _ _ ⟨hvm_wb, hPf, hsp_sf, hcs_sf, htr_sf⟩ =>
          ⟨hvm1.trans hvm_wb, ?_, hsp_sf, hcs_sf, htr_sf⟩)
      refine Entails.trans hPf ?_
      have hrec := writeback_keysSampled_entails_resultV1RecvAt A (F := F) outA st w
        w.b5.w9 sp.q200
      refine Entails.trans (Entails.of_eq ?_)
        (sepConj_mono_right (sepConj_mono_left hrec))
      dsimp only [writebackWords63, sp1, Reg.x0, Reg.x1, Reg.x2, Reg.x3, Reg.x4, Reg.x5, Reg.x6,
        Reg.x7, Reg.x8, Reg.x9, Reg.x10, Reg.x11, Reg.x12, Reg.x13, Reg.x14, Reg.x15, Reg.x16,
        Reg.x17, Reg.x20, Reg.x21, Reg.x22, Reg.x23, Reg.x24, Reg.x25, Reg.x26, Reg.x27, Reg.x28,
        Reg.x30]
      simp only [wp_norm, arm64_norm, hx1]
      sep_ac_rfl
  )

end LibsignalBinary.Proofs.SpqrV1.States.Recv.ArmKeysSampled1PlacedBudget
