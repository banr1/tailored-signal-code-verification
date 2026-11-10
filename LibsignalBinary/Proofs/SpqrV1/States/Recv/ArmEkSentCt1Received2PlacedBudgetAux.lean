/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Heap.SpecBudget
public import LibsignalBinary.Proofs.Placed.BudgetPoolSync
public import LibsignalBinary.Proofs.Placed.BudgetVmSteps
public meta import LibsignalBinary.Proofs.Placed.BudgetVmSteps -- shake: keep
public import LibsignalBinary.Proofs.SpqrV1.States.Recv.ArmEkSentCt1Received1PlacedBudget
public import LibsignalBinary.Proofs.SpqrV1.States.Recv.ArmEkSentCt1Received2Placed
public import LibsignalBinary.Proofs.SpqrV1.States.Recv.DefsPlacedBudget
public import LibsignalBinary.Proofs.SpqrV1.States.Recv.DispatchPlacedBudget
import LibsignalBinary.Proofs.Common.SharedHelpers
meta import LibsignalBinary.Proofs.Common.SharedHelpers -- shake: keep
import LibsignalBinary.Proofs.SpqrV1.Kdf.HkdfToSliceExtract
import LibsignalBinary.Proofs.SpqrV1.Poly.EncoderIntoPb.Defs
import LibsignalBinary.Proofs.SpqrV1.States.FromPb.Defs
import LibsignalBinary.Proofs.SpqrV1.States.Recv.ArmCt1Received1
import LibsignalBinary.Proofs.SpqrV1.States.Recv.ArmCt1Received2Placed
import LibsignalBinary.Proofs.SpqrV1.States.Recv.ArmEkSentCt1Received1
import LibsignalBinary.Proofs.SpqrV1.States.Recv.ArmEkSentCt1Received1Placed
import LibsignalBinary.Proofs.SpqrV1.States.Recv.ArmEkSentCt1Received2
import LibsignalBinary.Proofs.SpqrV1.States.Recv.ArmHeaderSent1
import LibsignalBinary.Proofs.SpqrV1.States.Recv.ArmsSendEk1
import LibsignalBinary.Proofs.SpqrV1.States.Recv.CodeSymFetch0Placed
import LibsignalBinary.Proofs.SpqrV1.States.Recv.CodeSymFetch1Placed
import LibsignalBinary.Proofs.SpqrV1.States.Recv.CodeSymFetch3Placed
import LibsignalBinary.Proofs.SpqrV1.States.Recv.CodeSymFetch4Placed
import LibsignalBinary.Proofs.SpqrV1.States.Recv.CodeSymFetch5Placed
import LibsignalBinary.Proofs.SpqrV1.States.Recv.DispatchPlaced
import LibsignalBinary.Proofs.SpqrV1.States.Recv.SendEkCommonPlaced
import LibsignalBinary.Proofs.TripleRatchet.Getters.GettersCodeSym

/-!
# `<States>::recv` (Block `332`) — `.ekSentCt1Received` Arm, Part 2 Aux (Budget-Threaded)

`VmPreserved` and budget-pool-threaded post-call `.stillReceiving` / `.done` writeback blocks
(`+4384 -> s0.x30`) and pre-call `eq_ct2` setup (`+228 -> lsmpl.base 350`) for
`.ekSentCt1Received`.
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 400000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

namespace LibsignalBinary.Proofs.SpqrV1.States.Recv.ArmEkSentCt1Received2PlacedBudgetAux

open Arm64 ProofLib ProofLib.ProgramReflection
open CryptoGames.LibsignalSession (ShaCompress)
open CryptoVerification
open CryptoVerification.RustHeap
open CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalTripleRatchet.Getters
open CryptoVerification.LibsignalTripleRatchetRepr
open CryptoVerification.LibsignalSpqrV1
open CryptoVerification.SpqrV1
open CryptoVerification.SpqrV1.Alloc
open CryptoVerification.SpqrV1.Auth
open CryptoVerification.SpqrV1.GF.UnacceleratedMul
open CryptoVerification.SpqrV1.GF.Mul2U16
open CryptoVerification.SpqrV1.Poly
open CryptoVerification.SpqrV1.Poly.AddChunk
open CryptoVerification.SpqrV1.Drop
open CryptoVerification.SpqrV1.Top
open CryptoVerification.SpqrV1.Top.MessageSerialize
open CryptoVerification.SpqrV1.Unchunked
open CryptoVerification.SpqrV1.States
open CryptoVerification.SpqrV1.States.Leaves
open CryptoVerification.SpqrV1.States.Leaves.RecvHdrChunk
open CryptoVerification.SpqrV1.States.RecvCt2Chunk
open CryptoVerification.SpqrV1.States.Recv
open CryptoVerification.CodeLayout
open LibsignalBinary.Proofs.SpqrV1.States.Recv (lsmpl_base_332_eq)
open LibsignalBinary.Heap (
  AllocCostModel BudgetLimits RustCliAllocBudget VmPreserved
)
open LibsignalBinary.Heap.SpecBudget (withVmPreserved)
open LibsignalBinary.Proofs.SpqrV1.States.Recv.ArmNoHeaderReceivedStepsPlacedBudgetAux (
  call_memcpy_relocate_cs_stack seq_vm_clean seq_vm_cont step_adrp_vm
)

attribute [local irreducible] Program.fetch Program.externAt? Program.fnOff
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
  Recv.none2Cap_add_two_beq_zero Recv.none2Cap_add_two_bne_zero
  Recv.noneCap_add_two_beq_zero Recv.noneCap_add_two_bne_zero
  Recv.noneCap_add_one_beq_zero Recv.noneCap_add_one_bne_zero
  messagePayloadTag_ct2
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

/-! ## 1. Post-Call `.ok (.stillReceiving outSt)` Path (`+4384 -> s0.x30`) -/

set_option maxHeartbeats 1200000 in
/-- Relocatable post-call block `0x56574..0x5658c -> 0x58598..0x5883c -> 0x59e88..0x59ff0`
    (`+4384 -> s0.x30`, Block `332`) when `recv_ct2_chunk` returns `.ok (.stillReceiving outSt)`,
    establishing `VmPreserved s sf`. -/
theorem ekSentCt1Received_post_call_still_56574_placed [LibsignalPlacement]
    {A : RustAlloc} {F : ShaCompress} {ext : String → Option (State → State)}
    (hmemcpy_sat : HookSat (Rust.withPanics ext) spqrMemcpySym (withVmPreserved sessionMemcpySpec))
    (s0 s : State) (outA : BitVec 64)
    (outSt : Chunked.SendEk.EkSentCt1Received spqrPolyApi (spqrAuthApi F))
    (sp : SendEkSpills) (P_rest : SepProp)
    (hpc : s.pc = lsmpl.base 332 + 4384#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = s0.sp - 4240#64)
    (hsp_align : s0.spAligned = true)
    (hx19 : s.readReg64 .x19 = outA)
    (htr : TraceCalleeSaved s s0) :
    SepWP (lsProg_332 (Rust.withPanics ext)) (s0.readReg64 .x30) s
      (P_rest ∗
        memRegion outA v1RecvSize ∗
        ekSentCt1ReceivedRecvChunkResultAt A (F := F) ((s0.sp - 4240#64) + 976#64)
          (.ok (.stillReceiving outSt)) ∗
        memRegion ((s0.sp - 4240#64) + 1480#64) 376 ∗
        memRegion ((s0.sp - 4240#64) + 1856#64) 504 ∗
        memRegion ((s0.sp - 4240#64) + 2360#64) 376 ∗
        stackAt (s0.sp - 4240#64) statesRecvCalleeStackX ∗
        sendEkSpillsAt (s0.sp - 4240#64) sp ∗
        memRegion ((s0.sp - 4240#64) + 576#64) 376 ∗
        sendEkUnusedAt (s0.sp - 4240#64) ∗
        statesRecvSavedCells s0)
      (fun sf Pf =>
        VmPreserved s sf ∧
        (Pf ⊢
          P_rest ∗
          resultV1RecvAt A (F := F) outA (.ok { key := none, state := .ekSentCt1Received outSt }) ∗
          stackAt s0.sp statesRecvStackX) ∧
        sf.sp = s0.sp ∧
        CalleeSavedPreserved s0 sf ∧
        sf.trace = s0.trace) := by
  have hwb := @ArmNoHeaderReceivedStepsPlacedBudgetAux.states_recv_writeback_59e88_sat_placed
    _ ext hmemcpy_sat (F_tail := fun a => memRegion a 376) (Relocatable.of_memRegion 376) s0
  rw [lsmpl_base_332_eq] at hpc hwb
  dsimp only [lsProg_332, BitVec.ofNat_eq_ofNat] at hpc hwb ⊢
  refine SepWP.fold (stillReceiving_result_976_extract A ((s0.sp - 4240#64) + 976#64) outSt)
    (by sep_focus) ?_
  wp_pull_exists; rename_i w_out
  refine SepWP.pure_elim fun ⟨hcap, _⟩ => ?_
  refine SepWP.fold (sendEkUnusedAt_split_ab0_ac0 (s0.sp - 4240#64)) (by sep_focus) ?_
  wp_pull_exists; rename_i qab0 qac0
  have hcond1 := cap_add_two_bne_zero_true hcap
  have hcond2 := Recv.cap_add_two_beq_zero_false hcap
  have hcond3 := cap_add_one_beq_zero_false_recv hcap
  have hcond4 := cap_add_one_bne_zero_true_recv hcap
  have hsp_align' : (s0.sp &&& 15#64 == 0#64) = true := hsp_align
  have hfsp_align : ((s0.sp - 4240#64) &&& 15#64 == 0#64) = true :=
    spAligned_sub s0.sp 4240#64 hsp_align (by decide)
  let sp1 : SendEkSpills :=
    { b0 := ⟨sp.b0.w0, sp.b0.w1, w_out.b3.w2, w_out.b2.w9, sp.b0.w4, sp.b0.w5, sp.b0.w6,
             sp.b0.w7, w_out.b3.w5, w_out.b3.w4⟩
      b1 := ⟨w_out.b5.w7, sp.b1.w1, sp.b1.w2, w_out.b3.w6, sp.b1.w4, sp.b1.w5, w_out.b0.w1,
             w_out.b5.w9, w_out.b1.w5, w_out.b1.w6⟩
      b2 := ⟨sp.b2.w0, sp.b2.w1, w_out.b4.w9, sp.b2.w3, w_out.b4.w5, w_out.b0.w1, w_out.b4.w8,
             6#64, noneCap, sp.b2.w9⟩
      b3 := ⟨w_out.b5.w8, w_out.w62, w_out.b1.w8, w_out.b2.w1, w_out.b2.w7, w_out.b0.w7,
             w_out.b1.w3, w_out.b2.w5, w_out.b3.w0, w_out.b2.w8⟩
      b4 := ⟨w_out.b2.w6, w_out.b1.w2, w_out.b1.w9, w_out.b1.w0, w_out.b2.w2, w_out.b0.w5,
             w_out.b0.w4, w_out.b1.w1, w_out.b2.w0, w_out.b2.w3⟩
      b5 := ⟨w_out.b0.w9, w_out.b4.w4, w_out.b1.w4, w_out.b0.w8, w_out.b1.w7, w_out.b5.w0,
             w_out.b0.w3, w_out.b2.w4, w_out.b4.w6, w_out.b5.w4⟩
      w60 := w_out.b5.w6
      w61 := w_out.b0.w2
      w62 := w_out.b0.w6
      q200 := sp.q200
      q210 := sp.q210
      q220 := sp.q220
      w230 := sp.w230
      q3c0 := w_out.q60 }
  refine seq_vm_clean (mid := (blkPl_332).base + 18996#64)
    (P_mid :=
      (P_rest ∗
        relocatedHeap (fun dst => chunkedEkSentCt1ReceivedAt A dst outSt) (wordsBytes (words63List w_out))) ∗
      memRegion outA v1RecvSize ∗
      stackAt (s0.sp - 4240#64) statesRecvCalleeStackX ∗
      sendEkSpillsAt (s0.sp - 4240#64) sp1 ∗
      memRegion ((s0.sp - 4240#64) + 576#64) 376 ∗
      memRegion ((s0.sp - 4240#64) + 976#64) 880 ∗
      memRegion ((s0.sp - 4240#64) + 1856#64) 880 ∗
      sendEkUnusedAt (s0.sp - 4240#64) ∗
      statesRecvSavedCells s0)
    (Q := fun sm =>
      sm.sp = s0.sp - 4240#64 ∧
      sm.readReg64 .x19 = outA ∧
      TraceCalleeSaved sm s0 ∧
      writebackWords63 sm sp1 = w_out)
    ?_ ?_
  · by_vm_steps (
      generalize hsp0 : s0.sp = sp0 at hsp hsp_align' hfsp_align ⊢
      wp_conv_pre =>
        dsimp only [sendEkSpillsAt, words63At, words10At]
        simp only [pointsTo128_eq_pair64_recv, BitVec.add_assoc, arm64_norm]
      wp_steps 200
      subst hsp0
      have h880_1856 :
          memRegion ((s0.sp - 4240#64) + 1856#64) 504 ∗
          memRegion ((s0.sp - 4240#64) + 2360#64) 376 ⊢
            memRegion ((s0.sp - 4240#64) + 1856#64) 880 := by
        rw [ProofLib.memRegion_split' (b := (s0.sp - 4240#64) + 1856#64) (n := 504) (k := 376)
          (b' := (s0.sp - 4240#64) + 2360#64) rfl (by bv_omega) (by decide)]
        exact Entails.refl _
      have hfold_unused := sendEkUnusedAt_rejoin_ab0_ac0 (s0.sp - 4240#64) w_out.q60 qac0
      have hfold_sp1 :
          (words63At ((s0.sp - 4240#64) + 976#64) w_out ∗
           memRegion ((s0.sp - 4240#64) + 1480#64) 376) ∗
          (memRegion ((s0.sp - 4240#64) + 1856#64) 504 ∗
           memRegion ((s0.sp - 4240#64) + 2360#64) 376) ∗
          (((s0.sp - 4240#64 + 2736#64) ↦₁₂₈ w_out.q60) ∗
           ((s0.sp - 4240#64 + 2752#64) ↦₁₂₈ qac0) ∗
           memRegion (s0.sp - 4240#64) 8 ∗
           memRegion (s0.sp - 4240#64 + 568#64) 8 ∗
           memRegion (s0.sp - 4240#64 + 952#64) 8 ∗
           memRegion (s0.sp - 4240#64 + 2768#64) 1376) ∗
          sendEkSpillsAt (s0.sp - 4240#64) sp1 ⊢
            memRegion ((s0.sp - 4240#64) + 976#64) 880 ∗
            memRegion ((s0.sp - 4240#64) + 1856#64) 880 ∗
            sendEkUnusedAt (s0.sp - 4240#64) ∗
            sendEkSpillsAt (s0.sp - 4240#64) sp1 :=
        sepConj_mono
          (words63At_376_entails_memRegion_880
            ((s0.sp - 4240#64) + 976#64) ((s0.sp - 4240#64) + 1480#64) w_out (by bv_omega))
          (sepConj_mono h880_1856 (sepConj_mono_left hfold_unused))
      refine SepWP.fold
        (F := P_rest ∗
          relocatedHeap (fun dst => chunkedEkSentCt1ReceivedAt A dst outSt) (wordsBytes (words63List w_out)) ∗
          memRegion outA v1RecvSize ∗
          stackAt (s0.sp - 4240#64) statesRecvCalleeStackX ∗
          memRegion ((s0.sp - 4240#64) + 576#64) 376 ∗
          statesRecvSavedCells s0)
        hfold_sp1
        (by
          dsimp only [sendEkSpillsAt, words63At, words10At, sp1, noneCap]
          simp only [pointsTo128_eq_pair64_recv, BitVec.add_assoc, arm64_norm]
          sep_ac_rfl) ?_
      refine DropChunkedClPlacedBudgetAux.align_pre_vm (by sep_ac_rfl) ?_
      rcases w_out with ⟨⟨_, _, _, _, _, _, _, _, _, _⟩, ⟨_, _, _, _, _, _, _, _, _, _⟩,
        ⟨_, _, _, _, _, _, _, _, _, _⟩, ⟨_, _, _, _, _, _, _, _, _, _⟩,
        ⟨_, _, _, _, _, _, _, _, _, _⟩, ⟨_, _, _, _, _, _, _, _, _, _⟩, _, _⟩
      dsimp only [writebackWords63, sp1, Reg.x0, Reg.x1, Reg.x2, Reg.x3, Reg.x4, Reg.x5, Reg.x6,
        Reg.x7, Reg.x8, Reg.x9, Reg.x10, Reg.x11, Reg.x12, Reg.x13, Reg.x14, Reg.x15, Reg.x16,
        Reg.x17, Reg.x19, Reg.x20, Reg.x21, Reg.x22, Reg.x23, Reg.x24, Reg.x25, Reg.x26, Reg.x27,
        Reg.x28, Reg.x30] at hx19 ⊢
      simp only [TraceCalleeSaved, hsp, hx19, htr.1, htr.2, wp_norm, arm64_norm]
      wp_done
    )
  · intro sm hpcm hrunm hvm_m ⟨hsp_m, hx19_m, htr_m, hwb_m⟩
    refine SepWP.mono
      (hwb sm outA sp1
        (P_rest ∗ relocatedHeap (fun dst => chunkedEkSentCt1ReceivedAt A dst outSt)
          (wordsBytes (words63List w_out)))
        hpcm hrunm hsp_m hsp_align hx19_m htr_m)
      (fun sf Pf _ _ ⟨hvm_wb, hPf, hsp_sf, hcs_sf, htr_sf⟩ =>
        ⟨hvm_m.trans hvm_wb, ?_, hsp_sf, hcs_sf, htr_sf⟩)
    refine Entails.trans hPf ?_
    have hrec := writeback_ekSentCt1Received_entails_resultV1RecvAt A (F := F) outA outSt w_out
      (sm.readReg64 .x20) sp.q200
    have htag : sp1.b2.w7 = 6#64 := rfl
    have hnone : sp1.b2.w8 = noneCap := rfl
    have hq200 : sp1.q200 = sp.q200 := rfl
    rw [htag, hnone, hq200, hwb_m]
    refine Entails.trans (Entails.of_eq (by sep_ac_rfl))
      (sepConj_mono_right (sepConj_mono_left hrec))

theorem ekSentCt1Received_post_call_still_56574_pool_placed [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits} {F : ShaCompress}
    {ext : String → Option (State → State)}
    (hmemcpy_sat : HookSat (Rust.withPanics ext) spqrMemcpySym (withVmPreserved sessionMemcpySpec))
    (st_cost : M.σ)
    (s0 s : State) (outA : BitVec 64)
    (outSt : Chunked.SendEk.EkSentCt1Received spqrPolyApi (spqrAuthApi F))
    (sp : SendEkSpills) (P_rest : SepProp)
    (hpc : s.pc = lsmpl.base 332 + 4384#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = s0.sp - 4240#64)
    (hsp_align : s0.spAligned = true)
    (hx19 : s.readReg64 .x19 = outA)
    (htr : TraceCalleeSaved s s0) :
    SepWP (lsProg_332 (Rust.withPanics ext)) (s0.readReg64 .x30) s
      (P_rest ∗
        A.pool lim st_cost s ∗
        memRegion outA v1RecvSize ∗
        ekSentCt1ReceivedRecvChunkResultAt A.repAlloc (F := F) ((s0.sp - 4240#64) + 976#64)
          (.ok (.stillReceiving outSt)) ∗
        memRegion ((s0.sp - 4240#64) + 1480#64) 376 ∗
        memRegion ((s0.sp - 4240#64) + 1856#64) 504 ∗
        memRegion ((s0.sp - 4240#64) + 2360#64) 376 ∗
        stackAt (s0.sp - 4240#64) statesRecvCalleeStackX ∗
        sendEkSpillsAt (s0.sp - 4240#64) sp ∗
        memRegion ((s0.sp - 4240#64) + 576#64) 376 ∗
        sendEkUnusedAt (s0.sp - 4240#64) ∗
        statesRecvSavedCells s0)
      (fun sf Pf =>
        VmPreserved s sf ∧
        (Pf ⊢
          P_rest ∗
          resultV1RecvAt A.repAlloc (F := F) outA
            (.ok { key := none, state := .ekSentCt1Received outSt }) ∗
          A.pool lim st_cost sf ∗
          stackAt s0.sp statesRecvStackX) ∧
        sf.sp = s0.sp ∧
        CalleeSavedPreserved s0 sf ∧
        sf.trace = s0.trace) := by
  refine SepWP.weaken_pre
    (Entails.of_eq (show _ =
      (P_rest ∗ A.pool lim st_cost s) ∗
      memRegion outA v1RecvSize ∗
      ekSentCt1ReceivedRecvChunkResultAt A.repAlloc (F := F) ((s0.sp - 4240#64) + 976#64)
        (.ok (.stillReceiving outSt)) ∗
      memRegion ((s0.sp - 4240#64) + 1480#64) 376 ∗
      memRegion ((s0.sp - 4240#64) + 1856#64) 504 ∗
      memRegion ((s0.sp - 4240#64) + 2360#64) 376 ∗
      stackAt (s0.sp - 4240#64) statesRecvCalleeStackX ∗
      sendEkSpillsAt (s0.sp - 4240#64) sp ∗
      memRegion ((s0.sp - 4240#64) + 576#64) 376 ∗
      sendEkUnusedAt (s0.sp - 4240#64) ∗
      statesRecvSavedCells s0 by sep_ac_rfl))
    (SepWP.mono
      (ekSentCt1Received_post_call_still_56574_placed (A := A.repAlloc) hmemcpy_sat s0 s outA outSt sp
        (P_rest ∗ A.pool lim st_cost s) hpc hrun hsp hsp_align hx19 htr)
      fun sf Pf _ _ ⟨hvm, hPf, hsp_sf, hcs_sf, htr_sf⟩ =>
        ⟨hvm, Entails.trans hPf (Entails.of_eq (by
          rw [← A.pool_transport lim st_cost s sf hvm]
          sep_ac_rfl)), hsp_sf, hcs_sf, htr_sf⟩)

/-! ## 2. Post-Call `.ok (.done (nhr, sec))` Path (`+4384 -> s0.x30`) -/

set_option maxHeartbeats 1600000 in
/-- Relocatable post-call block `0x56574..0x5658c -> 0x58598..0x586f4 -> 0x59950..0x599c8 -> 0x59a7c..0x59b34 -> 0x59e88..0x59ff0`
    (`+4384 -> s0.x30`, Block `332`) when `recv_ct2_chunk` returns `.ok (.done (nhr, sec))`,
    establishing `VmPreserved s sf`. -/
theorem ekSentCt1Received_post_call_done_56574_placed [LibsignalPlacement]
    {A : RustAlloc} {F : ShaCompress} {ext : String → Option (State → State)}
    (hmemcpy_sat : HookSat (Rust.withPanics ext) spqrMemcpySym (withVmPreserved sessionMemcpySpec))
    (s0 s : State) (outA : BitVec 64)
    (nhr : Chunked.SendCt.NoHeaderReceived spqrPolyApi (spqrAuthApi F))
    (sec : EpochSecret)
    (sp : SendEkSpills) (P_rest : SepProp)
    (hpc : s.pc = lsmpl.base 332 + 4384#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = s0.sp - 4240#64)
    (hsp_align : s0.spAligned = true)
    (hx19 : s.readReg64 .x19 = outA)
    (htr : TraceCalleeSaved s s0) :
    SepWP (lsProg_332 (Rust.withPanics ext)) (s0.readReg64 .x30) s
      (P_rest ∗
        memRegion outA v1RecvSize ∗
        ekSentCt1ReceivedRecvChunkResultAt A (F := F) ((s0.sp - 4240#64) + 976#64)
          (.ok (.done (nhr, sec))) ∗
        memRegion ((s0.sp - 4240#64) + 1480#64) 376 ∗
        memRegion ((s0.sp - 4240#64) + 1856#64) 504 ∗
        memRegion ((s0.sp - 4240#64) + 2360#64) 376 ∗
        (lsLogFilterAddr ↦₆₄ 0#64) ∗
        stackAt (s0.sp - 4240#64) statesRecvCalleeStackX ∗
        sendEkSpillsAt (s0.sp - 4240#64) sp ∗
        memRegion ((s0.sp - 4240#64) + 576#64) 376 ∗
        sendEkUnusedAt (s0.sp - 4240#64) ∗
        statesRecvSavedCells s0)
      (fun sf Pf =>
        VmPreserved s sf ∧
        (Pf ⊢
          P_rest ∗
          resultV1RecvAt A (F := F) outA (.ok { key := some sec, state := .noHeaderReceived nhr }) ∗
          (lsLogFilterAddr ↦₆₄ 0#64) ∗
          stackAt s0.sp statesRecvStackX) ∧
        sf.sp = s0.sp ∧
        CalleeSavedPreserved s0 sf ∧
        sf.trace = s0.trace) := by
  have hwb := @ArmNoHeaderReceivedStepsPlacedBudgetAux.states_recv_writeback_59e88_sat_placed
    _ ext hmemcpy_sat (F_tail := fun a => memRegion a 376) (Relocatable.of_memRegion 376) s0
  rw [lsmpl_base_332_eq] at hpc hwb
  dsimp only [lsProg_332, BitVec.ofNat_eq_ofNat] at hpc hwb ⊢
  refine SepWP.fold (done_result_976_extract A ((s0.sp - 4240#64) + 976#64) nhr sec)
    (by sep_focus) ?_
  wp_pull_exists; rename_i g p v_sec w_pad
  refine SepWP.fold (sendEkUnusedAt_split_ab0_ac0 (s0.sp - 4240#64)) (by sep_focus) ?_
  wp_pull_exists; rename_i qab0 qac0
  have hsp_align' : (s0.sp &&& 15#64 == 0#64) = true := hsp_align
  have hfsp_align : ((s0.sp - 4240#64) &&& 15#64 == 0#64) = true :=
    spAligned_sub s0.sp 4240#64 hsp_align (by decide)
  let w_out := mkWords63_done g nhr.uc.epoch p v_sec sec.epoch w_pad
  let sp1 : SendEkSpills :=
    { b0 := ⟨p.b4.w5, p.b2.w8, w_out.b3.w2, w_out.b3.w0, sp.b0.w4, p.b3.w4, sp.b0.w6,
             p.b3.w1, w_out.b3.w5, w_out.b3.w4⟩
      b1 := ⟨w_out.b5.w7, p.b4.w8, p.b3.w2, w_out.b3.w7, p.b4.w6, p.b3.w0, w_out.b0.w1,
             w_out.b5.w9, w_out.b1.w5, w_out.b1.w6⟩
      b2 := ⟨p.b4.w0, p.b4.w4, w_out.b5.w0, p.b3.w6, w_out.b4.w6, w_out.b0.w2, w_out.b4.w9,
             7#64, w_out.b5.w8, w_out.b4.w3⟩
      b3 := ⟨sp.b3.w0, sp.b3.w1, w_out.b1.w9, w_out.b2.w2, w_out.b2.w8, w_out.b0.w8,
             w_out.b1.w4, w_out.b2.w6, w_out.b3.w1, w_out.b2.w9⟩
      b4 := ⟨w_out.b2.w7, w_out.b1.w3, w_out.b2.w0, w_out.b1.w1, w_out.b2.w3, w_out.b0.w6,
             w_out.b0.w5, w_out.b1.w2, w_out.b2.w1, w_out.b2.w4⟩
      b5 := ⟨w_out.b1.w0, w_out.b4.w5, w_out.b1.w5, w_out.b0.w9, w_out.b1.w8, w_out.b5.w1,
             w_out.b0.w4, w_out.b2.w5, w_out.b4.w7, w_out.b5.w5⟩
      w60 := w_out.b5.w7
      w61 := w_out.b0.w3
      w62 := w_out.b0.w7
      q200 := w_out.q60
      q210 := sp.q210
      q220 := sp.q220
      w230 := sp.w230
      q3c0 := sp.q3c0 }
  refine seq_vm_clean (mid := (blkPl_332).base + 18996#64)
    (P_mid :=
      (P_rest ∗
        (lsLogFilterAddr ↦₆₄ 0#64) ∗
        relocatedHeap (fun dst => chunkedNoHeaderReceivedAt A dst nhr)
          (wordsBytes (ct2SentWordsList g nhr.uc.epoch ++ words5x10List p)) ∗
        relocatedHeap (fun dst => vecU8 A dst sec.secret)
          (wordsBytes (vecWordsList v_sec))) ∗
      memRegion outA v1RecvSize ∗
      stackAt (s0.sp - 4240#64) statesRecvCalleeStackX ∗
      sendEkSpillsAt (s0.sp - 4240#64) sp1 ∗
      memRegion ((s0.sp - 4240#64) + 576#64) 376 ∗
      memRegion ((s0.sp - 4240#64) + 976#64) 880 ∗
      memRegion ((s0.sp - 4240#64) + 1856#64) 880 ∗
      sendEkUnusedAt (s0.sp - 4240#64) ∗
      statesRecvSavedCells s0)
    (Q := fun sm =>
      sm.sp = s0.sp - 4240#64 ∧
      sm.readReg64 .x19 = outA ∧
      sm.readReg64 .x20 = v_sec.w1 ∧
      TraceCalleeSaved sm s0 ∧
      writebackWords63 sm sp1 =
        mkWords63_nhr_tail g nhr.uc.epoch p p.b2.w5 sp.b3.w0 w_out.b5.w9 sp.q3c0 sp.b3.w1)
    ?_ ?_
  · generalize hsp0 : s0.sp = sp0 at hsp hsp_align' hfsp_align ⊢
    refine seq_vm_cont (mid := (blkPl_332).base + 17696#64) ?_
    by_vm_steps_nest (
      wp_conv_pre =>
        dsimp only [sendEkSpillsAt, words63At, words10At, w_out, mkWords63_done, noneCap,
          lsLogFilterAddr, lsρ]
        simp only [pointsTo128_eq_pair64_recv, BitVec.add_assoc, arm64_norm]
      wp_steps 200
      refine SepWP.done (by simp only [wp_norm, arm64_norm])
        (by simp only [wp_norm, arm64_norm]; assumption)
        ⟨by simp only [wp_norm, arm64_norm], fun hvmm => ?_⟩
      refine step_adrp_vm hvmm
        (blkPC_332_pairStep_0x4520 ‹_› (blkPl_332).base (Rust.withPanics ext) rfl ?_ ?_) ?_
      · simp only [wp_norm, arm64_norm]
      · simp only [wp_norm, arm64_norm]; assumption
      · by_vm_steps_nest (
          wp_steps 200
          subst hsp0
          have h880_1856 :
              memRegion ((s0.sp - 4240#64) + 1856#64) 504 ∗
              memRegion ((s0.sp - 4240#64) + 2360#64) 376 ⊢
                memRegion ((s0.sp - 4240#64) + 1856#64) 880 := by
            rw [ProofLib.memRegion_split' (b := (s0.sp - 4240#64) + 1856#64) (n := 504) (k := 376)
              (b' := (s0.sp - 4240#64) + 2360#64) rfl (by bv_omega) (by decide)]
            exact Entails.refl _
          have hfold_unused := sendEkUnusedAt_rejoin_ab0_ac0 (s0.sp - 4240#64) w_out.q60 w_out.q60
          have hfold_sp1 :
              (words63At ((s0.sp - 4240#64) + 976#64) w_out ∗
               memRegion ((s0.sp - 4240#64) + 1480#64) 376) ∗
              (memRegion ((s0.sp - 4240#64) + 1856#64) 504 ∗
               memRegion ((s0.sp - 4240#64) + 2360#64) 376) ∗
              (((s0.sp - 4240#64 + 2736#64) ↦₁₂₈ w_out.q60) ∗
               ((s0.sp - 4240#64 + 2752#64) ↦₁₂₈ w_out.q60) ∗
               memRegion (s0.sp - 4240#64) 8 ∗
               memRegion (s0.sp - 4240#64 + 568#64) 8 ∗
               memRegion (s0.sp - 4240#64 + 952#64) 8 ∗
               memRegion (s0.sp - 4240#64 + 2768#64) 1376) ∗
              sendEkSpillsAt (s0.sp - 4240#64) sp1 ⊢
                memRegion ((s0.sp - 4240#64) + 976#64) 880 ∗
                memRegion ((s0.sp - 4240#64) + 1856#64) 880 ∗
                sendEkUnusedAt (s0.sp - 4240#64) ∗
                sendEkSpillsAt (s0.sp - 4240#64) sp1 :=
            sepConj_mono
              (words63At_376_entails_memRegion_880
                ((s0.sp - 4240#64) + 976#64) ((s0.sp - 4240#64) + 1480#64) w_out (by bv_omega))
              (sepConj_mono h880_1856 (sepConj_mono_left hfold_unused))
          refine SepWP.fold
            (F := P_rest ∗
              relocatedHeap (fun dst => chunkedNoHeaderReceivedAt A dst nhr)
                (wordsBytes (ct2SentWordsList g nhr.uc.epoch ++ words5x10List p)) ∗
              relocatedHeap (fun dst => vecU8 A dst sec.secret)
                (wordsBytes (vecWordsList v_sec)) ∗
              (lsLogFilterAddr ↦₆₄ 0#64) ∗
              memRegion outA v1RecvSize ∗
              stackAt (s0.sp - 4240#64) statesRecvCalleeStackX ∗
              memRegion ((s0.sp - 4240#64) + 576#64) 376 ∗
              statesRecvSavedCells s0)
            hfold_sp1
            (by
              dsimp only [sendEkSpillsAt, words63At, words10At, sp1, w_out, mkWords63_done, noneCap,
                lsLogFilterAddr, lsρ]
              simp only [pointsTo128_eq_pair64_recv, BitVec.add_assoc, arm64_norm]
              sep_ac_rfl) ?_
          refine DropChunkedClPlacedBudgetAux.align_pre_vm (by sep_ac_rfl) ?_
          dsimp only [writebackWords63, sp1, w_out, mkWords63_done, mkWords63_nhr_tail,
            Reg.x0, Reg.x1, Reg.x2, Reg.x3, Reg.x4, Reg.x5, Reg.x6,
            Reg.x7, Reg.x8, Reg.x9, Reg.x10, Reg.x11, Reg.x12, Reg.x13, Reg.x14, Reg.x15, Reg.x16,
            Reg.x17, Reg.x19, Reg.x20, Reg.x21, Reg.x22, Reg.x23, Reg.x24, Reg.x25, Reg.x26, Reg.x27,
            Reg.x28, Reg.x30] at hx19 ⊢
          simp only [TraceCalleeSaved, hsp, hx19, htr.1, htr.2, wp_norm, arm64_norm]
          wp_done
        )
    )
  · intro sm hpcm hrunm hvm_m ⟨hsp_m, hx19_m, hx20_m, htr_m, hwb_m⟩
    refine SepWP.mono
      (hwb sm outA sp1
        (P_rest ∗
          (lsLogFilterAddr ↦₆₄ 0#64) ∗
          relocatedHeap (fun dst => chunkedNoHeaderReceivedAt A dst nhr)
            (wordsBytes (ct2SentWordsList g nhr.uc.epoch ++ words5x10List p)) ∗
          relocatedHeap (fun dst => vecU8 A dst sec.secret)
            (wordsBytes (vecWordsList v_sec)))
        hpcm hrunm hsp_m hsp_align hx19_m htr_m)
      (fun sf Pf _ _ ⟨hvm_wb, hPf, hsp_sf, hcs_sf, htr_sf⟩ =>
        ⟨hvm_m.trans hvm_wb, ?_, hsp_sf, hcs_sf, htr_sf⟩)
    refine Entails.trans hPf ?_
    have hrec := writeback_noHeaderReceived_some_entails_resultV1RecvAt A (F := F) outA nhr sec g p v_sec
      p.b2.w5 sp.b3.w0 w_out.b5.w9 sp.q3c0 sp.b3.w1
    have htag : sp1.b2.w7 = 7#64 := rfl
    have hw928 : sp1.b2.w8 = v_sec.w0 := rfl
    have hq200 : sp1.q200 = sec.epoch ++ v_sec.w2 := rfl
    rw [htag, hw928, hq200, hx20_m, hwb_m]
    refine Entails.trans (Entails.of_eq (by sep_ac_rfl))
      (sepConj_mono_right (sepConj_mono_left hrec))

theorem ekSentCt1Received_post_call_done_56574_pool_placed [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits} {F : ShaCompress}
    {ext : String → Option (State → State)}
    (hmemcpy_sat : HookSat (Rust.withPanics ext) spqrMemcpySym (withVmPreserved sessionMemcpySpec))
    (st_cost : M.σ)
    (s0 s : State) (outA : BitVec 64)
    (nhr : Chunked.SendCt.NoHeaderReceived spqrPolyApi (spqrAuthApi F))
    (sec : EpochSecret)
    (sp : SendEkSpills) (P_rest : SepProp)
    (hpc : s.pc = lsmpl.base 332 + 4384#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = s0.sp - 4240#64)
    (hsp_align : s0.spAligned = true)
    (hx19 : s.readReg64 .x19 = outA)
    (htr : TraceCalleeSaved s s0) :
    SepWP (lsProg_332 (Rust.withPanics ext)) (s0.readReg64 .x30) s
      (P_rest ∗
        A.pool lim st_cost s ∗
        memRegion outA v1RecvSize ∗
        ekSentCt1ReceivedRecvChunkResultAt A.repAlloc (F := F) ((s0.sp - 4240#64) + 976#64)
          (.ok (.done (nhr, sec))) ∗
        memRegion ((s0.sp - 4240#64) + 1480#64) 376 ∗
        memRegion ((s0.sp - 4240#64) + 1856#64) 504 ∗
        memRegion ((s0.sp - 4240#64) + 2360#64) 376 ∗
        (lsLogFilterAddr ↦₆₄ 0#64) ∗
        stackAt (s0.sp - 4240#64) statesRecvCalleeStackX ∗
        sendEkSpillsAt (s0.sp - 4240#64) sp ∗
        memRegion ((s0.sp - 4240#64) + 576#64) 376 ∗
        sendEkUnusedAt (s0.sp - 4240#64) ∗
        statesRecvSavedCells s0)
      (fun sf Pf =>
        VmPreserved s sf ∧
        (Pf ⊢
          P_rest ∗
          resultV1RecvAt A.repAlloc (F := F) outA
            (.ok { key := some sec, state := .noHeaderReceived nhr }) ∗
          (lsLogFilterAddr ↦₆₄ 0#64) ∗
          A.pool lim st_cost sf ∗
          stackAt s0.sp statesRecvStackX) ∧
        sf.sp = s0.sp ∧
        CalleeSavedPreserved s0 sf ∧
        sf.trace = s0.trace) := by
  refine SepWP.weaken_pre
    (Entails.of_eq (show _ =
      (P_rest ∗ A.pool lim st_cost s) ∗
      memRegion outA v1RecvSize ∗
      ekSentCt1ReceivedRecvChunkResultAt A.repAlloc (F := F) ((s0.sp - 4240#64) + 976#64)
        (.ok (.done (nhr, sec))) ∗
      memRegion ((s0.sp - 4240#64) + 1480#64) 376 ∗
      memRegion ((s0.sp - 4240#64) + 1856#64) 504 ∗
      memRegion ((s0.sp - 4240#64) + 2360#64) 376 ∗
      (lsLogFilterAddr ↦₆₄ 0#64) ∗
      stackAt (s0.sp - 4240#64) statesRecvCalleeStackX ∗
      sendEkSpillsAt (s0.sp - 4240#64) sp ∗
      memRegion ((s0.sp - 4240#64) + 576#64) 376 ∗
      sendEkUnusedAt (s0.sp - 4240#64) ∗
      statesRecvSavedCells s0 by sep_ac_rfl))
    (SepWP.mono
      (ekSentCt1Received_post_call_done_56574_placed (A := A.repAlloc) hmemcpy_sat s0 s outA nhr sec sp
        (P_rest ∗ A.pool lim st_cost s) hpc hrun hsp hsp_align hx19 htr)
      fun sf Pf _ _ ⟨hvm, hPf, hsp_sf, hcs_sf, htr_sf⟩ =>
        ⟨hvm, Entails.trans hPf (Entails.of_eq (by
          rw [← A.pool_transport lim st_cost s sf hvm]
          sep_ac_rfl)), hsp_sf, hcs_sf, htr_sf⟩)

/-! ## 3. Pre-Call `eq_ct2` Segment (`+228 -> lsmpl.base 350`) -/

set_option maxHeartbeats 1600000 in
/-- Pre-call segment `+228 -> lsmpl.base 350` (`0x55538..0x5565c -> 0x56544..0x56570`, Block `332`)
    when `msg.epoch = st.uc.epoch` and `msg.payload = .ct2 chunk`, establishing `VmPreserved s sm`
    and transporting `A.pool lim st_cost`. -/
theorem ekSentCt1Received_pre_call_228_350_placed [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits} {F : ShaCompress}
    {ext : String → Option (State → State)}
    (hmemcpy_sat : HookSat (Rust.withPanics ext) spqrMemcpySym (withVmPreserved sessionMemcpySpec))
    (st_cost : M.σ)
    (s0 s : State) (outA selfA msgA : BitVec 64)
    (st : Chunked.SendEk.EkSentCt1Received spqrPolyApi (spqrAuthApi F))
    (msg : Message spqrPolyApi) (chunk : Chunk) (P_rest : SepProp)
    (heq : msg.epoch = st.uc.epoch) (hpay : msg.payload = .ct2 chunk)
    (hpc : s.pc = lsmpl.base 332 + 228#64)
    (hrun : s.status = .Running) (hsp : s.sp = s0.sp - 4240#64) (hsp_align : s0.spAligned = true)
    (hx1 : s.readReg64 .x1 = selfA) (hx19 : s.readReg64 .x19 = outA)
    (hx24 : s.readReg64 .x24 = msgA) (htr : TraceCalleeSaved s s0) :
    SepWP (lsProg_332 (Rust.withPanics ext)) (lsmpl.base 350) s
      (P_rest ∗ memRegion outA v1RecvSize ∗ chunkedStatesAt A.repAlloc selfA (.ekSentCt1Received st) ∗
        messageAt spqrPolyApi msgA msg ∗ (lsLogFilterAddr ↦₆₄ 0#64) ∗
        tokenInitPlacedAt ∗ reduceTablePlacedAt ∗ A.pool lim st_cost s ∗
        stackAt (s0.sp - 4240#64) statesRecvCalleeStackX ∗
        memRegion (s0.sp - 4240#64) 4144 ∗ statesRecvSavedCells s0)
      (fun sm Pm =>
        VmPreserved s sm ∧
        ∃ sp1 : SendEkSpills,
          (Pm ⊢
            (memRegion ((s0.sp - 4240#64) + 976#64) chunkedEkSentCt1ReceivedSize ∗
              ekSentCt1ReceivedAt A.repAlloc ((s0.sp - 4240#64) + 1856#64) st ∗
              chunkAt (msgA + 10#64) chunk ∗
              tokenInitPlacedAt ∗ reduceTablePlacedAt ∗
              A.pool lim st_cost sm ∗
              stackAt (s0.sp - 4240#64) recvCt2ChunkStackX) ∗
            (P_rest ∗ memRegion selfA chunkedStatesSize ∗
              ((msgA ↦₆₄ msg.epoch) ∗ ((msgA + 8#64) ↦₈ 6#8) ∗ memRegion (msgA + 9#64) 1 ∗
                memRegion (msgA + 44#64) 4) ∗
              (lsLogFilterAddr ↦₆₄ 0#64) ∗ memRegion outA v1RecvSize ∗
              memRegion ((s0.sp - 4240#64) + 576#64) 376 ∗
              memRegion ((s0.sp - 4240#64) + 1480#64) 376 ∗
              memRegion ((s0.sp - 4240#64) + 2360#64) 376 ∗
              sendEkUnusedAt (s0.sp - 4240#64) ∗ sendEkSpillsAt (s0.sp - 4240#64) sp1 ∗
              statesRecvSavedCells s0)) ∧
          sm.sp = s0.sp - 4240#64 ∧
          sm.readReg64 Reg.lr = lsmpl.base 332 + 4384#64 ∧
          sm.readReg64 .x0 = (s0.sp - 4240#64) + 976#64 ∧
          sm.readReg64 .x1 = (s0.sp - 4240#64) + 1856#64 ∧
          sm.readReg64 .x2 = st.uc.epoch ∧
          sm.readReg64 .x3 = msgA + 10#64 ∧
          sm.readReg64 .x19 = outA ∧
          TraceCalleeSaved sm s0) := by
  have hcond_eq := epoch_cmp_ct1r_eq_of_eq st.uc.epoch
  have hmemcpy : subroutine_ok (lsProg_332 (Rust.withPanics ext))
      (lsρ memcpyName) (withVmPreserved (sessionMemcpySpec 4096)) := spqr_hook_ok_of_mem hmemcpy_sat
  rw [lsmpl_base_332_eq] at hpc ⊢
  dsimp only [lsProg_332, lsρ, memcpyName, chunkedStatesAt, messageAt,
    BitVec.ofNat_eq_ofNat] at hpc hmemcpy ⊢
  refine SepWP.fold (memRegion_4144_entails_sendEkFrame (s0.sp - 4240#64)) (by sep_focus) ?_
  wp_pull_exists; rename_i sp
  refine SepWP.fold (chunkedEkSentCt1ReceivedAt_extract63 A.repAlloc (selfA + 8#64) st) (by sep_focus) ?_
  wp_pull_exists; rename_i w
  refine SepWP.pure_elim fun hw12 => ?_
  have hsp_align' : (s0.sp &&& 15#64 == 0#64) = true := hsp_align
  have hfsp_align : ((s0.sp - 4240#64) &&& 15#64 == 0#64) = true :=
    spAligned_sub s0.sp 4240#64 hsp_align (by decide)
  let sp1 : SendEkSpills :=
    { b0 := ⟨sp.b0.w0, sp.b0.w1, sp.b0.w2, w.b2.w9, sp.b0.w4, sp.b0.w5, sp.b0.w6, sp.b0.w7, sp.b0.w8, sp.b0.w9⟩
      b1 := ⟨w.b5.w7, w.b5.w5, sp.b1.w2, sp.b1.w3, sp.b1.w4, sp.b1.w5, w.b0.w0, w.b5.w9, w.b1.w5, w.b1.w6⟩
      b2 := ⟨w.b4.w7, sp.b2.w1, w.b4.w9, w.b4.w3, w.b4.w5, w.b0.w1, w.b4.w8, sp.b2.w7, sp.b2.w8, sp.b2.w9⟩
      b3 := ⟨w.b5.w8, w.w62, w.b1.w8, w.b2.w1, w.b2.w7, w.b0.w7, w.b1.w3, w.b2.w5, sp.b3.w8, w.b2.w8⟩
      b4 := ⟨w.b2.w6, st.uc.epoch, w.b1.w9, w.b1.w0, w.b2.w2, sp.b4.w5, w.b0.w4, w.b1.w1, w.b2.w0, w.b2.w3⟩
      b5 := ⟨w.b0.w9, w.b4.w4, w.b1.w4, w.b0.w8, w.b1.w7, sp.b5.w5, w.b0.w3, w.b2.w4, w.b4.w6, w.b5.w4⟩
      w60 := w.b5.w6, w61 := w.b0.w2, w62 := w.b0.w6
      q200 := sp.q200, q210 := sp.q210, q220 := sp.q220, w230 := sp.w230, q3c0 := sp.q3c0 }
  refine seq_vm_clean (mid := lsmpl.ρ "memcpy")
    (P_mid :=
      (memRegion ((s0.sp - 4240#64) + 1856#64) 504 ∗
        chunkedEkSentCt1ReceivedAt A.repAlloc (selfA + 8#64) st ∗
        stackAt (s0.sp - 4240#64) 4096) ∗
      (memRegion (s0.sp - 4240#64 - 19552#64) 15456 ∗
        P_rest ∗ memRegion outA v1RecvSize ∗
        (selfA ↦₆₄ 6#64) ∗ memRegion (selfA + 512#64) 416 ∗
        ((msgA ↦₆₄ msg.epoch) ∗ ((msgA + 8#64) ↦₈ 6#8) ∗ memRegion (msgA + 9#64) 1 ∗
          chunkAt (msgA + 10#64) chunk ∗ memRegion (msgA + 44#64) 4) ∗
        (lsLogFilterAddr ↦₆₄ 0#64) ∗ tokenInitPlacedAt ∗ reduceTablePlacedAt ∗
        A.pool lim st_cost s ∗
        memRegion ((s0.sp - 4240#64) + 576#64) 376 ∗
        memRegion ((s0.sp - 4240#64) + 976#64) 504 ∗
        memRegion ((s0.sp - 4240#64) + 1480#64) 376 ∗
        memRegion ((s0.sp - 4240#64) + 2360#64) 376 ∗
        sendEkUnusedAt (s0.sp - 4240#64) ∗ sendEkSpillsAt (s0.sp - 4240#64) sp1 ∗
        statesRecvSavedCells s0))
    (Q := fun sc =>
      sc.sp = s0.sp - 4240#64 ∧
      sc.readReg64 Reg.lr = (blkPl_332).base + 4364#64 ∧
      sc.readReg64 Reg.x0 = (s0.sp - 4240#64) + 1856#64 ∧
      sc.readReg64 Reg.x1 = selfA + 8#64 ∧
      (sc.readReg64 Reg.x2).toNat = 504 ∧
      sc.readReg64 .x19 = outA ∧
      sc.readReg64 .x24 = msgA ∧
      sc.readReg64 .x25 = st.uc.epoch ∧
      TraceCalleeSaved sc s0)
    ?_ ?_
  · by_vm_steps (
      generalize hsp0 : s0.sp = sp0 at hsp hsp_align' hfsp_align ⊢
      wp_conv_pre =>
        dsimp only [sendEkSpillsAt, words63At, words10At]
        rw [hw12, heq, hpay, messagePayloadAt_ct2 msgA chunk]
        simp only [pointsTo128_eq_pair64_recv, BitVec.add_assoc, arm64_norm]
      wp_steps 120
      subst hsp0
      have hfold_pre_memcpy :
          (words63At (selfA + 8#64) w ∗
           relocatedHeap (fun dst => chunkedEkSentCt1ReceivedAt A.repAlloc dst st)
             (wordsBytes (words63List w))) ∗
          memRegion ((s0.sp - 4240#64) + 976#64) 880 ∗
          memRegion ((s0.sp - 4240#64) + 1856#64) 880 ∗
          sendEkSpillsAt (s0.sp - 4240#64) sp1 ⊢
            chunkedEkSentCt1ReceivedAt A.repAlloc (selfA + 8#64) st ∗
            (memRegion ((s0.sp - 4240#64) + 976#64) 504 ∗
             memRegion ((s0.sp - 4240#64) + 1480#64) 376) ∗
            (memRegion ((s0.sp - 4240#64) + 1856#64) 504 ∗
             memRegion ((s0.sp - 4240#64) + 2360#64) 376) ∗
            sendEkSpillsAt (s0.sp - 4240#64) sp1 :=
        sepConj_mono (recompose63 (selfA + 8#64) w)
          (sepConj_mono
            (Entails.of_eq (memRegion_880_split_504_376_ct2
              ((s0.sp - 4240#64) + 976#64) ((s0.sp - 4240#64) + 1480#64) (by bv_omega)))
            (sepConj_mono_left
              (Entails.of_eq (memRegion_880_split_504_376_ct2
                ((s0.sp - 4240#64) + 1856#64) ((s0.sp - 4240#64) + 2360#64) (by bv_omega)))))
      refine SepWP.fold
        (F := P_rest ∗ memRegion outA v1RecvSize ∗ (selfA ↦₆₄ 6#64) ∗ memRegion (selfA + 512#64) 416 ∗
          ((msgA ↦₆₄ msg.epoch) ∗ ((msgA + 8#64) ↦₈ 6#8) ∗ memRegion (msgA + 9#64) 1 ∗
            chunkAt (msgA + 10#64) chunk ∗ memRegion (msgA + 44#64) 4) ∗
          (lsLogFilterAddr ↦₆₄ 0#64) ∗ tokenInitPlacedAt ∗ reduceTablePlacedAt ∗
          A.pool lim st_cost s ∗
          stackAt (s0.sp - 4240#64) statesRecvCalleeStackX ∗
          memRegion ((s0.sp - 4240#64) + 576#64) 376 ∗
          sendEkUnusedAt (s0.sp - 4240#64) ∗ statesRecvSavedCells s0)
        hfold_pre_memcpy
        (by
          dsimp only [sendEkSpillsAt, words63At, words10At, sp1]
          rw [hw12, heq]
          simp only [pointsTo128_eq_pair64_recv, BitVec.add_assoc, arm64_norm]
          sep_ac_rfl) ?_
      refine DropChunkedClPlacedBudgetAux.align_pre_vm ?_ ?_
      · rw [stackAt_statesRecvCallee_eq_allocHook (s0.sp - 4240#64)]
        dsimp only [allocHookStack]
        sep_ac_rfl
      · dsimp only [Reg.lr, Reg.x0, Reg.x1, Reg.x2, Reg.x19, Reg.x24, Reg.x25] at hx1 hx19 hx24 ⊢
        simp only [TraceCalleeSaved, hsp, hx1, hx19, hx24, htr.1, htr.2, wp_norm, arm64_norm]
        wp_done
    )
  · intro sc hpcc hrunc hvm0 ⟨hsp_c, hlr_c, hx0_c, hx1_c, hx2_c, hx19_c, hx24_c, hx25_c, htr_c⟩
    refine call_memcpy_relocate_cs_stack (ret_pc := (blkPl_332).base + 4364#64)
      hmemcpy (Recv.Relocatable.of_chunkedEkSentCt1ReceivedAt A.repAlloc st)
      ((s0.sp - 4240#64) + 1856#64) (selfA + 8#64)
      hpcc hrunc hsp_c hfsp_align hlr_c htr_c hx0_c hx1_c hx2_c rfl ?_
    intro sf1 hpc1 hrun1 hsp1 hvm1 hcs1 htr1
    have hvm01 : VmPreserved s sf1 := hvm0.trans hvm1
    have hx19_1 : sf1.readReg64 .x19 = outA := hcs1.1.trans hx19_c
    have hx24_1 : sf1.readReg64 .x24 = msgA := hcs1.2.2.2.2.2.1.trans hx24_c
    have hx25_1 : sf1.readReg64 .x25 = st.uc.epoch := hcs1.2.2.2.2.2.2.1.trans hx25_c
    have hfold_callee :
        memRegion (s0.sp - 4240#64 - 19552#64) 15456 ∗ stackAt (s0.sp - 4240#64) 4096 ⊢
          stackAt (s0.sp - 4240#64) statesRecvCalleeStackX :=
      Entails.of_eq (stackAt_statesRecvCallee_eq_allocHook (s0.sp - 4240#64)).symm
    refine SepWP.focus_weaken hfold_callee (by sep_focus) ?_
    have hfold_self :
        chunkedEkSentCt1ReceivedAt A.repAlloc ((s0.sp - 4240#64) + 1856#64) st ∗
        ((selfA ↦₆₄ 6#64) ∗ memRegion (selfA + 8#64) 504 ∗ memRegion (selfA + 512#64) 416) ⊢
          ekSentCt1ReceivedAt A.repAlloc ((s0.sp - 4240#64) + 1856#64) st ∗
          memRegion selfA chunkedStatesSize := by
      dsimp only [ekSentCt1ReceivedAt]
      unfold chunkedEkSentCt1ReceivedAt unchunkedEkSentCt1ReceivedAt
      rw [show ((s0.sp - 4240#64) + 1856#64) + 104#64 = (s0.sp - 4240#64) + 1960#64 by bv_omega]
      exact sepConj_mono_right (self_504_416_entails_memRegion_928 selfA 6#64)
    refine SepWP.focus_weaken hfold_self (by sep_focus) ?_
    refine SepWP.mono (post := fun sm Pm =>
        VmPreserved sf1 sm ∧
        (Pm ⊢
          (memRegion ((s0.sp - 4240#64) + 976#64) chunkedEkSentCt1ReceivedSize ∗
            ekSentCt1ReceivedAt A.repAlloc ((s0.sp - 4240#64) + 1856#64) st ∗
            chunkAt (msgA + 10#64) chunk ∗
            tokenInitPlacedAt ∗ reduceTablePlacedAt ∗
            A.pool lim st_cost s ∗
            stackAt (s0.sp - 4240#64) recvCt2ChunkStackX) ∗
          (P_rest ∗ memRegion selfA chunkedStatesSize ∗
            ((msgA ↦₆₄ msg.epoch) ∗ ((msgA + 8#64) ↦₈ 6#8) ∗ memRegion (msgA + 9#64) 1 ∗
              memRegion (msgA + 44#64) 4) ∗
            (lsLogFilterAddr ↦₆₄ 0#64) ∗ memRegion outA v1RecvSize ∗
            memRegion ((s0.sp - 4240#64) + 576#64) 376 ∗
            memRegion ((s0.sp - 4240#64) + 1480#64) 376 ∗
            memRegion ((s0.sp - 4240#64) + 2360#64) 376 ∗
            sendEkUnusedAt (s0.sp - 4240#64) ∗ sendEkSpillsAt (s0.sp - 4240#64) sp1 ∗
            statesRecvSavedCells s0)) ∧
        (sm.sp = s0.sp - 4240#64 ∧
         sm.readReg64 Reg.lr = (blkPl_332).base + 4384#64 ∧
         sm.readReg64 .x0 = (s0.sp - 4240#64) + 976#64 ∧
         sm.readReg64 .x1 = (s0.sp - 4240#64) + 1856#64 ∧
         sm.readReg64 .x2 = st.uc.epoch ∧
         sm.readReg64 .x3 = msgA + 10#64 ∧
         sm.readReg64 .x19 = outA ∧
         TraceCalleeSaved sm s0))
      (by
        by_vm_steps (
          generalize hsp0 : s0.sp = sp0 at hsp1 hfsp_align ⊢
          wp_steps 10
          subst hsp0
          refine DropChunkedClPlacedBudgetAux.align_pre_vm ?_ ?_
          · dsimp only [chunkedEkSentCt1ReceivedSize, statesRecvCalleeStackX, BitVec.ofNat_eq_ofNat]
            simp only [arm64_norm]
            sep_ac_rfl
          · dsimp only [Reg.lr, Reg.x0, Reg.x1, Reg.x2, Reg.x3, Reg.x19] at hx19_1 hx24_1 hx25_1 ⊢
            simp only [TraceCalleeSaved, hsp1, hx19_1, hx24_1, hx25_1, htr1.1, htr1.2, wp_norm,
              arm64_norm]
            wp_done
        ))
      (fun sm _ _ _ ⟨hvm2, hPm, hq⟩ =>
        let hvm_sm := hvm01.trans hvm2
        ⟨hvm_sm, sp1, Entails.trans hPm (Entails.of_eq (by
          rw [A.pool_transport lim st_cost s sm hvm_sm]
          sep_ac_rfl)), hq⟩)

end LibsignalBinary.Proofs.SpqrV1.States.Recv.ArmEkSentCt1Received2PlacedBudgetAux
