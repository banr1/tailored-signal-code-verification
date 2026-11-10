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
public import LibsignalBinary.Proofs.SpqrV1.States.Leaves.Batch2DefsPlacedBudget
public import LibsignalBinary.Proofs.SpqrV1.States.Recv.ArmCt1Acknowledged2
public import LibsignalBinary.Proofs.SpqrV1.States.Recv.ArmNoHeaderReceivedStepsPlacedBudgetAux
public import LibsignalBinary.Proofs.SpqrV1.States.Recv.CodeSymBasePlaced
public import LibsignalBinary.Proofs.SpqrV1.States.Recv.DefsPlaced
import LibsignalBinary.Proofs.Common.SharedHelpers
import LibsignalBinary.Proofs.SpqrV1.States.FromPb.Defs
import LibsignalBinary.Proofs.SpqrV1.States.Recv.ArmCt1Acknowledged1
import LibsignalBinary.Proofs.SpqrV1.States.Recv.ArmEkReceivedCt1SampledPlaced
import LibsignalBinary.Proofs.SpqrV1.States.Recv.CodeSymFetch1Placed
import LibsignalBinary.Proofs.SpqrV1.States.Recv.CodeSymFetch4Placed
import LibsignalBinary.Proofs.SpqrV1.States.Recv.DispatchPlaced
import ProofLib.SepLogic.WPp
meta import LibsignalBinary.Proofs.Common.SharedHelpers -- shake: keep
meta import LibsignalBinary.Proofs.Placed.BudgetVmSteps -- shake: keep

/-!
# `<States>::recv` (Block `332`) — `.ct1Acknowledged` Arm, Part 2 (Budget-Threaded)

`VmPreserved` shared tail and Branch B no-op, plus `RustCliAllocBudget`-threaded Branch C
`recv_ek_chunk` call (`lsmpl.base 349`), error path, and `.stillReceiving` path.
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 400000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

namespace LibsignalBinary.Proofs.SpqrV1.States.Recv.ArmCt1Acknowledged2PlacedBudget

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
open CryptoVerification.SpqrV1.GF.UnacceleratedMul
open CryptoVerification.SpqrV1.GF.Mul2U16
open CryptoVerification.SpqrV1.Poly
open CryptoVerification.SpqrV1.Poly.AddChunk
open CryptoVerification.SpqrV1.Poly.EncodeBytes
open CryptoVerification.SpqrV1.Drop
open CryptoVerification.SpqrV1.Alloc
open CryptoVerification.SpqrV1.Top
open CryptoVerification.SpqrV1.Top.MessageSerialize
open CryptoVerification.SpqrV1.Unchunked
open CryptoVerification.SpqrV1.States
open CryptoVerification.SpqrV1.States.Leaves
open CryptoVerification.SpqrV1.States.RecvCt2Chunk
open CryptoVerification.SpqrV1.States.Recv
open CryptoVerification.CodeLayout
open LibsignalBinary.Proofs.SpqrV1.States.Recv
open LibsignalBinary.Heap (
  AllocCostModel AllocEvent BudgetLimits FitsEnv RustCliAllocBudget VmPreserved
)
open LibsignalBinary.Heap.SpecBudget (withVmPreserved)
open LibsignalBinary.Proofs.SpqrV1.States.Leaves.Batch2DefsPlacedBudget (
  Ct1AcknowledgedRecvEkChunkPostEnv Ct1AcknowledgedRecvEkChunkPreEnv
  ct1AcknowledgedRecvEkChunkPlacedSpec ct1AcknowledgedRecvEkChunkPlacedSpecOfEnv
  ct1AcknowledgedRecvEkChunkPlacedSpecOfPrePostEnv
)
open LibsignalBinary.Proofs.SpqrV1.States.Recv.ArmNoHeaderReceivedStepsPlacedBudgetAux (
  seq_vm_clean
)

attribute [local irreducible] Program.fetch Program.externAt? Program.fnOff
  CryptoVerification.blkPC_332
attribute [-arm64_norm]
  CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.sp_sub_688_eq_hsp
  CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.sp_add_neg688_eq_hsp
  CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.sp_sub_96_eq_hsp_592
  CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.sp_add_neg96_eq_hsp_592
attribute [local arm64_norm, local wp_norm] bv_sub_add_lit BitVec.toNat_zero
  sp_sub_4240_add_4144 bv_add_lit_add_lit_recv
  Leaves.extractLsb'_0_64_append Leaves.extractLsb'_64_64_append
  Recv.sp_sub_96_add_16 Recv.sp_sub_96_add_32 Recv.sp_sub_96_add_48
  Recv.sp_sub_96_add_64 Recv.sp_sub_96_add_80
  sp_sub_96_sub_4096 sp_sub_4192_sub_48 sp_sub_4240_add_4096 sp_sub_144_add_48 sp_sub_4240_add_48
  RustCliAllocBudget.pool_setPC RustCliAllocBudget.pool_advancePC
  RustCliAllocBudget.pool_setPState RustCliAllocBudget.pool_writeReg64
  RustCliAllocBudget.pool_writeReg32 RustCliAllocBudget.pool_writeReg

/-! ## 1. Shared Tail (`+4924 -> +18996`) and Branch B (`+4516 -> +4924 -> s0.x30`) -/

set_option maxHeartbeats 800000 in
theorem ct1Ack_step_4924_18996_placed [LibsignalPlacement]
    {ext : String → Option (State → State)}
    (s : State) (fsp : BitVec 64) (sp : SendEkSpills) (Frame : SepProp)
    (hfsp_align : (fsp &&& 15#64 == 0#64) = true)
    (hpc : s.pc = lsmpl.base 332 + 4924#64)
    (hrun : s.status = .Running) (hsp : s.sp = fsp) :
    SepWP (lsProg_332 (Rust.withPanics ext))
      (lsmpl.base 332 + 18996#64) s
      (sendEkSpillsAt fsp sp ∗ Frame)
      (fun sm Pm =>
        VmPreserved s sm ∧
        (Pm ⊢ sendEkSpillsAt fsp (ct1AckSpills4924 s sp) ∗ Frame) ∧
        sm.sp = fsp ∧ sm.readReg64 .x0 = s.readReg64 .x25 ∧
        sm.readReg64 .x1 = s.readReg64 .x1 ∧ sm.readReg64 .x2 = s.readReg64 .x2 ∧
        sm.readReg64 .x3 = s.readReg64 .x3 ∧ sm.readReg64 .x4 = s.readReg64 .x4 ∧
        sm.readReg64 .x5 = s.readReg64 .x5 ∧ sm.readReg64 .x6 = s.readReg64 .x12 ∧
        sm.readReg64 .x7 = sp.b0.w7 ∧ sm.readReg64 .x8 = sp.b2.w5 ∧
        sm.readReg64 .x9 = sp.b2.w3 ∧ sm.readReg64 .x10 = sp.b0.w1 ∧
        sm.readReg64 .x11 = sp.b0.w8 ∧ sm.readReg64 .x12 = sp.b0.w9 ∧
        sm.readReg64 .x13 = s.readReg64 .x22 ∧ sm.readReg64 .x14 = s.readReg64 .x18 ∧
        sm.readReg64 .x15 = sp.b1.w3 ∧ sm.readReg64 .x16 = s.readReg64 .x0 ∧
        sm.readReg64 .x17 = s.readReg64 .x17 ∧ sm.readReg64 .x19 = s.readReg64 .x19 ∧
        sm.readReg64 .x20 = s.readReg64 .x30 ∧ sm.readReg64 .x21 = sp.b2.w9 ∧
        sm.readReg64 .x22 = s.readReg64 .x13 ∧ sm.readReg64 .x23 = sp.b1.w8 ∧
        sm.readReg64 .x24 = s.readReg64 .x24 ∧ sm.readReg64 .x25 = sp.b0.w4 ∧
        sm.readReg64 .x26 = s.readReg64 .x16 ∧ sm.readReg64 .x27 = s.readReg64 .x10 ∧
        sm.readReg64 .x28 = sp.b1.w5 ∧ sm.readReg64 .x29 = s.readReg64 .x29 ∧
        sm.readReg64 .x30 = sp.b0.w5 ∧ TraceCalleeSaved sm s) := by
  subst hsp
  rw [lsmpl_base_332_eq] at hpc ⊢
  dsimp only [lsProg_332, noneCap, BitVec.ofNat_eq_ofNat] at hpc ⊢
  by_vm_steps (
    wp_simp_pre [sendEkSpillsAt, ct1AckSpills4924, words10At, noneCap, bv_add_lit_add_lit_recv, Nat.reduceAdd, sepConj_assoc]
    wp_steps
    simp only [sendEkSpillsAt, ct1AckSpills4924, words10At, noneCap, bv_add_lit_add_lit_recv, Nat.reduceAdd, sepConj_assoc]
    wp_done
  )

set_option maxHeartbeats 1600000 in
theorem ct1Ack_step_4516_4924_placed [LibsignalPlacement]
    {ext : String → Option (State → State)}
    (s : State) (fsp selfA w592_old : BitVec 64) (q576_old : BitVec 128)
    (w : Words66) (sp : SendEkSpills) (Frame : SepProp)
    (hfsp_align : (fsp &&& 15#64 == 0#64) = true)
    (hpc : s.pc = lsmpl.base 332 + 4516#64)
    (hrun : s.status = .Running) (hsp : s.sp = fsp)
    (hx9 : s.readReg64 .x9 = w.b1.w5) (hx20 : s.readReg64 .x20 = selfA) :
    SepWP (lsProg_332 (Rust.withPanics ext))
      (lsmpl.base 332 + 4924#64) s
      (words66At (fsp + 976#64) w ∗
       ((selfA + 488#64) ↦₁₂₈ w.q60) ∗ ((selfA + 512#64) ↦₁₂₈ w.q63) ∗ ((selfA + 528#64) ↦₆₄ w.w65) ∗
       sendEkSpillsAt fsp sp ∗ ((fsp + 576#64) ↦₁₂₈ q576_old) ∗ ((fsp + 592#64) ↦₆₄ w592_old) ∗ Frame)
      (fun sm Pm =>
        VmPreserved s sm ∧
        (Pm ⊢ words66At (fsp + 976#64) w ∗
          ((selfA + 488#64) ↦₁₂₈ w.q60) ∗ ((selfA + 512#64) ↦₁₂₈ w.q63) ∗ ((selfA + 528#64) ↦₆₄ w.w65) ∗
          sendEkSpillsAt fsp (ct1AckSpills4516 sp w) ∗
          ((fsp + 576#64) ↦₁₂₈ w.q63) ∗ ((fsp + 592#64) ↦₆₄ w.w65) ∗ Frame) ∧
        sm.sp = fsp ∧ sm.readReg64 .x0 = w.b5.w5 ∧ sm.readReg64 .x1 = w.b0.w0 ∧
        sm.readReg64 .x2 = w.b5.w7 ∧ sm.readReg64 .x3 = w.b2.w9 ∧
        sm.readReg64 .x4 = w.b4.w9 ∧ sm.readReg64 .x5 = w.b4.w8 ∧
        sm.readReg64 .x6 = w.b5.w0 ∧ sm.readReg64 .x7 = w.b1.w9 ∧
        sm.readReg64 .x10 = w.b1.w6 ∧ sm.readReg64 .x11 = w.b5.w4 ∧
        sm.readReg64 .x12 = w.b4.w0 ∧ sm.readReg64 .x13 = w.b5.w1 ∧
        sm.readReg64 .x15 = w.b2.w7 ∧ sm.readReg64 .x16 = w.b4.w7 ∧
        sm.readReg64 .x17 = w.b4.w5 ∧ sm.readReg64 .x18 = w.b5.w3 ∧
        sm.readReg64 .x19 = s.readReg64 .x19 ∧ sm.readReg64 .x22 = w.b5.w2 ∧
        sm.readReg64 .x24 = w.b3.w1 ∧ sm.readReg64 .x25 = w.b3.w9 ∧
        sm.readReg64 .x26 = w.b0.w5 ∧ sm.readReg64 .x29 = s.readReg64 .x29 ∧
        sm.readReg64 .x30 = w.b5.w9 ∧ TraceCalleeSaved sm s) := by
  subst hsp hx20
  rw [lsmpl_base_332_eq] at hpc ⊢
  dsimp only [lsProg_332, BitVec.ofNat_eq_ofNat] at hpc ⊢
  by_vm_steps (
    wp_simp_pre [words66At, sendEkSpillsAt, ct1AckSpills4516, words10At, pointsTo128,
      bv_add_lit_add_lit_recv, Nat.reduceAdd, sepConj_assoc]
    wp_steps
    simp only [words66At, sendEkSpillsAt, ct1AckSpills4516, words10At, pointsTo128,
      bv_add_lit_add_lit_recv, Nat.reduceAdd, sepConj_assoc, hx9]
    wp_done
  )

theorem ct1Ack_noop_4516_ret_placed [LibsignalPlacement]
    {A : RustAlloc} {F : ShaCompress} {ext : String → Option (State → State)}
    (hmemcpy_sat : HookSat (Rust.withPanics ext) spqrMemcpySym (withVmPreserved sessionMemcpySpec))
    (s0 s1 : State) (outA selfA : BitVec 64)
    (st : Chunked.SendCt.Ct1Acknowledged spqrPolyApi (spqrAuthApi F))
    (w : Words66) (sp : SendEkSpills) (P_rest : SepProp)
    (hsp0_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hpc : s1.pc = lsmpl.base 332 + 4516#64)
    (hrun : s1.status = .Running) (hsp : s1.sp = s0.sp - 4240#64)
    (hx9 : s1.readReg64 .x9 = w.b1.w5) (hx19 : s1.readReg64 .x19 = outA)
    (hx20 : s1.readReg64 .x20 = selfA) (htr : TraceCalleeSaved s1 s0) :
    SepWP (lsProg_332 (Rust.withPanics ext)) (s0.readReg64 .x30) s1
      (P_rest ∗ memRegion outA v1RecvSize ∗ (selfA ↦₆₄ 11#64) ∗ words66At (selfA + 8#64) w ∗
        memRegion (selfA + 536#64) 392 ∗ words66At (s0.sp - 4240#64 + 976#64) w ∗
        relocatedHeap (fun dst => chunkedCt1AcknowledgedAt A dst st) (wordsBytes (words66List w)) ∗
        memRegion (s0.sp - 4240#64 + 1504#64) 352 ∗ stackAt (s0.sp - 4240#64) statesRecvCalleeStackX ∗
        sendEkSpillsAt (s0.sp - 4240#64) sp ∗ memRegion (s0.sp - 4240#64 + 576#64) 376 ∗
        memRegion (s0.sp - 4240#64 + 1856#64) 880 ∗ sendEkUnusedAt (s0.sp - 4240#64) ∗ statesRecvSavedCells s0)
      (fun sf Pf =>
        VmPreserved s1 sf ∧
        (Pf ⊢ P_rest ∗ resultV1RecvAt A (F := F) outA (.ok { key := none, state := .ct1Acknowledged st }) ∗
          memRegion selfA chunkedStatesSize ∗ stackAt s0.sp statesRecvStackX) ∧
        sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf ∧ sf.trace = s0.trace) := by
  have hfsp_align : ((s0.sp - 4240#64) &&& 15#64 == 0#64) = true :=
    spAligned_sub s0.sp 4240#64 hsp0_align (by decide)
  set fsp := s0.sp - 4240#64
  refine SepWP.fold (memRegion_576_376_split_ekTail fsp) (by sep_focus) ?_
  wp_pull_exists; rename_i q576_old w592_old
  set sp1 := ct1AckSpills4516 sp w
  refine seq_vm_clean (mid := lsmpl.base 332 + 4924#64)
    (P_mid := P_rest ∗ memRegion outA v1RecvSize ∗ memRegion selfA chunkedStatesSize ∗
      relocatedHeap (fun dst => chunkedCt1AcknowledgedAt A dst st) (wordsBytes (words66List w)) ∗
      stackAt fsp statesRecvCalleeStackX ∗ sendEkSpillsAt fsp sp1 ∗
      ekTail376 w.q63 w.w65 (fsp + 576#64) ∗ memRegion (fsp + 976#64) 880 ∗
      memRegion (fsp + 1856#64) 880 ∗ sendEkUnusedAt fsp ∗ statesRecvSavedCells s0)
    (Q := fun s2 =>
      s2.sp = fsp ∧ s2.readReg64 .x0 = w.b5.w5 ∧ s2.readReg64 .x1 = w.b0.w0 ∧
      s2.readReg64 .x2 = w.b5.w7 ∧ s2.readReg64 .x3 = w.b2.w9 ∧
      s2.readReg64 .x4 = w.b4.w9 ∧ s2.readReg64 .x5 = w.b4.w8 ∧
      s2.readReg64 .x6 = w.b5.w0 ∧ s2.readReg64 .x7 = w.b1.w9 ∧
      s2.readReg64 .x10 = w.b1.w6 ∧ s2.readReg64 .x11 = w.b5.w4 ∧
      s2.readReg64 .x12 = w.b4.w0 ∧ s2.readReg64 .x13 = w.b5.w1 ∧
      s2.readReg64 .x15 = w.b2.w7 ∧ s2.readReg64 .x16 = w.b4.w7 ∧
      s2.readReg64 .x17 = w.b4.w5 ∧ s2.readReg64 .x18 = w.b5.w3 ∧
      s2.readReg64 .x19 = outA ∧ s2.readReg64 .x22 = w.b5.w2 ∧
      s2.readReg64 .x24 = w.b3.w1 ∧ s2.readReg64 .x25 = w.b3.w9 ∧
      s2.readReg64 .x26 = w.b0.w5 ∧ s2.readReg64 .x30 = w.b5.w9 ∧ TraceCalleeSaved s2 s0)
    ?_ ?_
  · have hstep1 := ct1Ack_step_4516_4924_placed (ext := ext) s1 fsp selfA w592_old q576_old w sp
      (P_rest ∗ memRegion outA v1RecvSize ∗ (selfA ↦₆₄ 11#64) ∗
       words10At (selfA + 8#64) w.b0 ∗ words10At (selfA + 88#64) w.b1 ∗
       words10At (selfA + 168#64) w.b2 ∗ words10At (selfA + 248#64) w.b3 ∗
       words10At (selfA + 328#64) w.b4 ∗ words10At (selfA + 408#64) w.b5 ∗
       ((selfA + 504#64) ↦₆₄ w.w62) ∗ memRegion (selfA + 536#64) 392 ∗
       relocatedHeap (fun dst => chunkedCt1AcknowledgedAt A dst st) (wordsBytes (words66List w)) ∗
       memRegion (fsp + 1504#64) 352 ∗ stackAt fsp statesRecvCalleeStackX ∗
       memRegion (fsp + 600#64) 352 ∗ memRegion (fsp + 1856#64) 880 ∗
       sendEkUnusedAt fsp ∗ statesRecvSavedCells s0)
      hfsp_align hpc hrun hsp hx9 hx20
    refine SepWP.weaken_pre (Entails.of_eq ?_) (SepWP.mono hstep1 ?_)
    · dsimp only [words66At]; simp only [bv_add_lit_add_lit_recv, Nat.reduceAdd]; sep_ac_rfl
    · intro s2 Pm _ _ ⟨hvm1, hPm, hsp2, h2_0, h2_1, h2_2, h2_3, h2_4, h2_5, h2_6, h2_7,
        h2_10, h2_11, h2_12, h2_13, h2_15, h2_16, h2_17, h2_18, h2_19, h2_22,
        h2_24, h2_25, h2_26, _, h2_30, htr2⟩
      refine ⟨hvm1, Entails.trans hPm ?_, hsp2, h2_0, h2_1, h2_2, h2_3, h2_4, h2_5, h2_6, h2_7,
        h2_10, h2_11, h2_12, h2_13, h2_15, h2_16, h2_17, h2_18, h2_19.trans hx19, h2_22,
        h2_24, h2_25, h2_26, h2_30, htr2.trans htr⟩
      have hself := selfA_ct1Acknowledged_entails_memRegion selfA w
      have h976 := words66At_976_352_entails_memRegion_880 fsp w
      refine Entails.trans (Entails.of_eq (show _ =
        (((selfA ↦₆₄ 11#64) ∗ words66At (selfA + 8#64) w ∗ memRegion (selfA + 536#64) 392) ∗
         (words66At (fsp + 976#64) w ∗ memRegion (fsp + 1504#64) 352)) ∗
        (P_rest ∗ memRegion outA v1RecvSize ∗
         relocatedHeap (fun dst => chunkedCt1AcknowledgedAt A dst st) (wordsBytes (words66List w)) ∗
         stackAt fsp statesRecvCalleeStackX ∗ sendEkSpillsAt fsp sp1 ∗
         ekTail376 w.q63 w.w65 (fsp + 576#64) ∗ memRegion (fsp + 1856#64) 880 ∗
         sendEkUnusedAt fsp ∗ statesRecvSavedCells s0) by
          dsimp only [words66At, ekTail376, sp1]; simp only [bv_add_lit_add_lit_recv, Nat.reduceAdd]; sep_ac_rfl)) ?_
      exact Entails.trans (sepConj_mono_left (sepConj_mono hself h976)) (Entails.of_eq (by sep_ac_rfl))
  · intro s2 hpc2 hrun2 hvm1 ⟨hsp2, h2_0, h2_1, h2_2, h2_3, h2_4, h2_5, h2_6, h2_7,
      h2_10, h2_11, h2_12, h2_13, h2_15, h2_16, h2_17, h2_18, h2_19, h2_22,
      h2_24, h2_25, h2_26, h2_30, htr2⟩
    set sp2 := ct1AckSpills4924 s2 sp1
    refine seq_vm_clean (mid := lsmpl.base 332 + 18996#64)
      (P_mid := (P_rest ∗ memRegion selfA chunkedStatesSize ∗
         relocatedHeap (fun dst => chunkedCt1AcknowledgedAt A dst st) (wordsBytes (words66List w))) ∗
        memRegion outA v1RecvSize ∗ stackAt fsp statesRecvCalleeStackX ∗ sendEkSpillsAt fsp sp2 ∗
        ekTail376 w.q63 w.w65 (fsp + 576#64) ∗ memRegion (fsp + 976#64) 880 ∗
        memRegion (fsp + 1856#64) 880 ∗ sendEkUnusedAt fsp ∗ statesRecvSavedCells s0)
      (Q := fun s3 => s3.sp = fsp ∧ s3.readReg64 .x19 = outA ∧
        writebackWords63 s3 sp2 =
          { b0 := w.b0, b1 := w.b1, b2 := w.b2, b3 := w.b3, b4 := w.b4, b5 := w.b5,
            q60 := w.q60, w62 := w.w62 } ∧ TraceCalleeSaved s3 s0)
      ?_ ?_
    · have hstep2 := ct1Ack_step_4924_18996_placed (ext := ext) s2 fsp sp1
        (P_rest ∗ memRegion outA v1RecvSize ∗ memRegion selfA chunkedStatesSize ∗
         relocatedHeap (fun dst => chunkedCt1AcknowledgedAt A dst st) (wordsBytes (words66List w)) ∗
         stackAt fsp statesRecvCalleeStackX ∗ ekTail376 w.q63 w.w65 (fsp + 576#64) ∗
         memRegion (fsp + 976#64) 880 ∗ memRegion (fsp + 1856#64) 880 ∗
         sendEkUnusedAt fsp ∗ statesRecvSavedCells s0)
        hfsp_align hpc2 hrun2 hsp2
      refine SepWP.weaken_pre (Entails.of_eq (by sep_ac_rfl)) (SepWP.mono hstep2 ?_)
      intro s3 Pm _ _ ⟨hvm2, hPm, hsp3, h3_0, h3_1, h3_2, h3_3, h3_4, h3_5, h3_6, h3_7,
        h3_8, h3_9, h3_10, h3_11, h3_12, h3_13, h3_14, h3_15, h3_16, h3_17, h3_19,
        h3_20, h3_21, h3_22, h3_23, h3_24, h3_25, h3_26, h3_27, h3_28, _, h3_30, htr3⟩
      have hwb := writebackWords63_ct1Ack_noop s2 s3 sp w
        h2_0 h2_1 h2_2 h2_3 h2_4 h2_5 h2_6 h2_7 h2_10 h2_11 h2_12 h2_13
        h2_15 h2_16 h2_17 h2_18 h2_22 h2_24 h2_25 h2_26 h2_30
        h3_0 h3_1 h3_2 h3_3 h3_4 h3_5 h3_6 h3_7 h3_8 h3_9 h3_10 h3_11 h3_12
        h3_13 h3_14 h3_15 h3_16 h3_17 h3_20 h3_21 h3_22 h3_23 h3_24 h3_25
        h3_26 h3_27 h3_28 h3_30
      refine ⟨hvm2, Entails.trans hPm (Entails.of_eq (by dsimp only [sp2]; sep_ac_rfl)),
        hsp3, h3_19.trans h2_19, hwb, htr3.trans htr2⟩
    · intro s3 hpc3 hrun3 hvm2 ⟨hsp3, h3_19, hwb, htr3⟩
      have hwrite := ArmNoHeaderReceivedStepsPlacedBudgetAux.states_recv_writeback_59e88_sat_placed
        hmemcpy_sat (relocatable_ekTail376 w.q63 w.w65)
        s0 s3 outA sp2
        (P_rest ∗ memRegion selfA chunkedStatesSize ∗
         relocatedHeap (fun dst => chunkedCt1AcknowledgedAt A dst st) (wordsBytes (words66List w)))
        hpc3 hrun3 hsp3 hsp0_align h3_19 htr3
      refine SepWP.mono hwrite ?_
      intro sf Pf _ _ ⟨hvm3, hPf, hsp_sf, hcs_sf, htr_sf⟩
      refine ⟨hvm1.trans (hvm2.trans hvm3), Entails.trans hPf ?_, hsp_sf, hcs_sf, htr_sf⟩
      have htag : sp2.b2.w7 = 11#64 := rfl
      have hnone : sp2.b2.w8 = noneCap := rfl
      rw [htag, hnone, hwb]
      have hout := ct1Ack_noop_out_entails_resultV1RecvAt A (F := F) outA st w (s3.readReg64 .x20) sp2.q200
      refine Entails.trans (Entails.of_eq (show _ =
        P_rest ∗ ((outA ↦₆₄ 11#64) ∗
         words63At (outA + 8#64)
           { b0 := w.b0, b1 := w.b1, b2 := w.b2, b3 := w.b3, b4 := w.b4, b5 := w.b5,
             q60 := w.q60, w62 := w.w62 } ∗
         ekTail376 w.q63 w.w65 (outA + 512#64) ∗ memRegion (outA + 888#64) 40 ∗
         ((outA + 928#64) ↦₆₄ noneCap) ∗ ((outA + 936#64) ↦₆₄ s3.readReg64 .x20) ∗
         ((outA + 944#64) ↦₁₂₈ sp2.q200) ∗
         relocatedHeap (fun dst => chunkedCt1AcknowledgedAt A dst st) (wordsBytes (words66List w))) ∗
        memRegion selfA chunkedStatesSize ∗ stackAt s0.sp statesRecvStackX by sep_ac_rfl)) ?_
      exact sepConj_mono_right (sepConj_mono_left hout)

/-! ## 2. Branch C Call (`+4448 -> +4468`) and Error Path (`+4468 -> +19324 -> s0.x30`) -/

theorem ct1Ack_step_4448_call_placed [LibsignalPlacement]
    {ext : String → Option (State → State)}
    (s : State) (fsp selfA msgA msg_ep : BitVec 64) (Frame : SepProp)
    (hpc : s.pc = lsmpl.base 332 + 4448#64)
    (hrun : s.status = .Running) (hsp : s.sp = fsp) (hx2 : s.readReg64 .x2 = msg_ep)
    (hx20 : s.readReg64 .x20 = selfA) (hx24 : s.readReg64 .x24 = msgA) :
    SepWP (lsProg_332 (Rust.withPanics ext))
      (lsmpl.base 349) s Frame
      (fun sm Pm =>
        VmPreserved s sm ∧
        (Pm ⊢ Frame) ∧ sm.sp = fsp ∧
        sm.readReg64 .x0 = fsp + 1856#64 ∧ sm.readReg64 .x1 = selfA + 8#64 ∧
        sm.readReg64 .x2 = msg_ep ∧ sm.readReg64 .x3 = msgA + 10#64 ∧
        sm.readReg64 .x19 = s.readReg64 .x19 ∧ sm.readReg64 .x20 = fsp + 1856#64 ∧
        sm.readReg64 .x24 = msgA ∧ sm.readReg64 .x29 = s.readReg64 .x29 ∧
        sm.readReg64 .x30 = lsmpl.base 332 + 4468#64 ∧
        TraceCalleeSaved sm s) := by
  subst hsp hx2 hx20 hx24
  rw [lsmpl_base_332_eq] at hpc ⊢
  dsimp only [lsProg_332, BitVec.ofNat_eq_ofNat] at hpc ⊢
  wp_steps
  dsimp only [blkPl_332, Obj.MultiPlacedLib.blockPlacement]
  wp_done

theorem call_ct1AcknowledgedRecvEkChunk_placed_ofPrePostEnv [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {F : ShaCompress} {K : MlKem}
    {PreEnv PostEnv : Ct1AcknowledgedRecvEkChunkGhost F → List AllocEvent → Prop}
    {prog : Program} {entry ret_pc target_pc : BitVec 64}
    (hcall : subroutine_ok prog entry
      (withLsCodeRoLoaded lsmpl
        (ct1AcknowledgedRecvEkChunkPlacedSpecOfPrePostEnv M A lim F K PreEnv PostEnv)))
    (st_cost : M.σ)
    (outA stA chunkA : BitVec 64)
    (st : Chunked.SendCt.Ct1Acknowledged spqrPolyApi (spqrAuthApi F))
    (chunk : Chunk)
    (res : Except Error (Chunked.SendCt.Ct1AcknowledgedRecvChunk spqrPolyApi (spqrAuthApi F)))
    (hstrict : PolyDecoderStrictSorted st.receiving_ek)
    (hrecv : st.recv_ek_chunk K st.uc.epoch chunk = StatesResult.ofError res)
    (hfit : FitsEnv M lim st_cost (PreEnv ⟨outA, stA, chunkA, st, chunk, res⟩))
    {s0 s : State} {sp_call : BitVec 64} {P Frame : SepProp}
    {post : State → SepProp → Prop}
    (hcro : LibsignalCodeRoLoaded lsmpl s.mem)
    (hpc : s.pc = entry) (hrun : s.status = .Running) (hsp : s.sp = sp_call)
    (hsp_align : (sp_call &&& 15#64 == 0#64) = true)
    (hlr : s.readReg64 Reg.lr = ret_pc) (htrace : TraceCalleeSaved s s0)
    (hx0 : s.readReg64 Reg.x0 = outA) (hx1 : s.readReg64 Reg.x1 = stA)
    (hx2 : s.readReg64 Reg.x2 = st.uc.epoch) (hx3 : s.readReg64 Reg.x3 = chunkA)
    (hsplit : P = (memRegion outA 528 ∗
      chunkedCt1AcknowledgedAt A.repAlloc stA st ∗ chunkAt chunkA chunk ∗
      unchunkedSendCt2PlacedRoAt ∗ tokenInitPlacedAt ∗ reduceTablePlacedAt ∗
      A.pool lim st_cost s ∗ stackAt sp_call ct1AcknowledgedRecvEkChunkStack) ∗ Frame)
    (hnext : ∀ (sf : State) (evs : List AllocEvent),
      sf.pc = ret_pc → sf.status = .Running →
      sf.sp = sp_call → CalleeSavedPreserved s sf → TraceCalleeSaved sf s0 →
      PostEnv ⟨outA, stA, chunkA, st, chunk, res⟩ evs →
      SepWP prog target_pc sf
        ((ct1AcknowledgedRecvEkChunkResAt A.repAlloc outA res ∗
          memRegion stA 528 ∗ chunkAt chunkA chunk ∗
          unchunkedSendCt2PlacedRoAt ∗ tokenInitPlacedAt ∗ reduceTablePlacedAt ∗
          A.pool lim (M.stepEvents evs st_cost) sf ∗
          stackAt sp_call ct1AcknowledgedRecvEkChunkStack) ∗ Frame) post) :
    SepWP prog target_pc s P post := by
  rw [hsplit]
  refine SepWP.call_subroutine_frame hcall
    (x := (⟨outA, stA, chunkA, st, chunk, res⟩, st_cost)) (F := Frame)
    hpc hrun (by rw [State.spAligned, hsp]; exact hsp_align) hlr ?_
    (fun _ _ _ h => ((satisfies_pure_sepConj _ _ _).mp h).1)
    (fun _ _ _ _ h => ((satisfies_pure_sepConj _ _ _).mp h).1)
    (fun sf hpc_sf hrun_sf hsp_sf hcs_sf => ?_)
  · intro R' hm
    dsimp only [withLsCodeRoLoaded]
    rw [sepConj_assoc, sepConj_left_comm, satisfies_pure_sepConj]
    refine ⟨hcro, ?_⟩
    dsimp only [ct1AcknowledgedRecvEkChunkPlacedSpecOfPrePostEnv]
    rw [hsp]
    simp only [sepConj_assoc] at hm ⊢
    rw [satisfies_pure_sepConj]
    exact ⟨⟨hx0, hx1, hx2, hx3, hstrict, hrecv, hfit⟩, hm⟩
  · dsimp only [withLsCodeRoLoaded, ct1AcknowledgedRecvEkChunkPlacedSpecOfPrePostEnv]
    rw [hsp, sepExists_sepConj_left]
    apply SepWP.exists_elim; intro evs
    rw [sepConj_assoc]
    refine SepWP.pure_elim fun ⟨htr, hevs⟩ => ?_
    refine SepWP.weaken_pre (Entails.of_eq (show _ =
      ((ct1AcknowledgedRecvEkChunkResAt A.repAlloc outA res ∗
        memRegion stA 528 ∗ chunkAt chunkA chunk ∗
        unchunkedSendCt2PlacedRoAt ∗ tokenInitPlacedAt ∗ reduceTablePlacedAt ∗
        A.pool lim (M.stepEvents evs st_cost) sf ∗
        stackAt sp_call ct1AcknowledgedRecvEkChunkStack) ∗ Frame) by sep_ac_rfl)) ?_
    exact hnext sf evs hpc_sf hrun_sf (hsp_sf.trans hsp) hcs_sf
      ⟨htr.trans htrace.1, hcs_sf.2.2.2.2.2.2.2.2.2.2.2.trans htrace.2⟩ hevs

theorem call_ct1AcknowledgedRecvEkChunk_placed_ofEnv [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {F : ShaCompress} {K : MlKem}
    {Env : Ct1AcknowledgedRecvEkChunkGhost F → List AllocEvent → Prop}
    {prog : Program} {entry ret_pc target_pc : BitVec 64}
    (hcall : subroutine_ok prog entry
      (withLsCodeRoLoaded lsmpl
        (ct1AcknowledgedRecvEkChunkPlacedSpecOfEnv M A lim F K Env)))
    (st_cost : M.σ)
    (outA stA chunkA : BitVec 64)
    (st : Chunked.SendCt.Ct1Acknowledged spqrPolyApi (spqrAuthApi F))
    (chunk : Chunk)
    (res : Except Error (Chunked.SendCt.Ct1AcknowledgedRecvChunk spqrPolyApi (spqrAuthApi F)))
    (hstrict : PolyDecoderStrictSorted st.receiving_ek)
    (hrecv : st.recv_ek_chunk K st.uc.epoch chunk = StatesResult.ofError res)
    (hfit : FitsEnv M lim st_cost (Env ⟨outA, stA, chunkA, st, chunk, res⟩))
    {s0 s : State} {sp_call : BitVec 64} {P Frame : SepProp}
    {post : State → SepProp → Prop}
    (hcro : LibsignalCodeRoLoaded lsmpl s.mem)
    (hpc : s.pc = entry) (hrun : s.status = .Running) (hsp : s.sp = sp_call)
    (hsp_align : (sp_call &&& 15#64 == 0#64) = true)
    (hlr : s.readReg64 Reg.lr = ret_pc) (htrace : TraceCalleeSaved s s0)
    (hx0 : s.readReg64 Reg.x0 = outA) (hx1 : s.readReg64 Reg.x1 = stA)
    (hx2 : s.readReg64 Reg.x2 = st.uc.epoch) (hx3 : s.readReg64 Reg.x3 = chunkA)
    (hsplit : P = (memRegion outA 528 ∗
      chunkedCt1AcknowledgedAt A.repAlloc stA st ∗ chunkAt chunkA chunk ∗
      unchunkedSendCt2PlacedRoAt ∗ tokenInitPlacedAt ∗ reduceTablePlacedAt ∗
      A.pool lim st_cost s ∗ stackAt sp_call ct1AcknowledgedRecvEkChunkStack) ∗ Frame)
    (hnext : ∀ (sf : State) (evs : List AllocEvent),
      sf.pc = ret_pc → sf.status = .Running →
      sf.sp = sp_call → CalleeSavedPreserved s sf → TraceCalleeSaved sf s0 →
      Env ⟨outA, stA, chunkA, st, chunk, res⟩ evs →
      SepWP prog target_pc sf
        ((ct1AcknowledgedRecvEkChunkResAt A.repAlloc outA res ∗
          memRegion stA 528 ∗ chunkAt chunkA chunk ∗
          unchunkedSendCt2PlacedRoAt ∗ tokenInitPlacedAt ∗ reduceTablePlacedAt ∗
          A.pool lim (M.stepEvents evs st_cost) sf ∗
          stackAt sp_call ct1AcknowledgedRecvEkChunkStack) ∗ Frame) post) :
    SepWP prog target_pc s P post :=
  call_ct1AcknowledgedRecvEkChunk_placed_ofPrePostEnv hcall st_cost outA stA chunkA st chunk res
    hstrict hrecv hfit hcro hpc hrun hsp hsp_align hlr htrace hx0 hx1 hx2 hx3 hsplit hnext

theorem call_ct1AcknowledgedRecvEkChunk_placed [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {F : ShaCompress} {K : MlKem}
    {prog : Program} {entry ret_pc target_pc : BitVec 64}
    (hcall : subroutine_ok prog entry
      (withLsCodeRoLoaded lsmpl (ct1AcknowledgedRecvEkChunkPlacedSpec M A lim F K)))
    (st_cost : M.σ)
    (outA stA chunkA : BitVec 64)
    (st : Chunked.SendCt.Ct1Acknowledged spqrPolyApi (spqrAuthApi F))
    (chunk : Chunk)
    (res : Except Error (Chunked.SendCt.Ct1AcknowledgedRecvChunk spqrPolyApi (spqrAuthApi F)))
    (hstrict : PolyDecoderStrictSorted st.receiving_ek)
    (hrecv : st.recv_ek_chunk K st.uc.epoch chunk = StatesResult.ofError res)
    (hfit : FitsEnv M lim st_cost
      (Ct1AcknowledgedRecvEkChunkPreEnv K ⟨outA, stA, chunkA, st, chunk, res⟩))
    {s0 s : State} {sp_call : BitVec 64} {P Frame : SepProp}
    {post : State → SepProp → Prop}
    (hcro : LibsignalCodeRoLoaded lsmpl s.mem)
    (hpc : s.pc = entry) (hrun : s.status = .Running) (hsp : s.sp = sp_call)
    (hsp_align : (sp_call &&& 15#64 == 0#64) = true)
    (hlr : s.readReg64 Reg.lr = ret_pc) (htrace : TraceCalleeSaved s s0)
    (hx0 : s.readReg64 Reg.x0 = outA) (hx1 : s.readReg64 Reg.x1 = stA)
    (hx2 : s.readReg64 Reg.x2 = st.uc.epoch) (hx3 : s.readReg64 Reg.x3 = chunkA)
    (hsplit : P = (memRegion outA 528 ∗
      chunkedCt1AcknowledgedAt A.repAlloc stA st ∗ chunkAt chunkA chunk ∗
      unchunkedSendCt2PlacedRoAt ∗ tokenInitPlacedAt ∗ reduceTablePlacedAt ∗
      A.pool lim st_cost s ∗ stackAt sp_call ct1AcknowledgedRecvEkChunkStack) ∗ Frame)
    (hnext : ∀ (sf : State) (evs : List AllocEvent),
      sf.pc = ret_pc → sf.status = .Running →
      sf.sp = sp_call → CalleeSavedPreserved s sf → TraceCalleeSaved sf s0 →
      Ct1AcknowledgedRecvEkChunkPostEnv K ⟨outA, stA, chunkA, st, chunk, res⟩ evs →
      SepWP prog target_pc sf
        ((ct1AcknowledgedRecvEkChunkResAt A.repAlloc outA res ∗
          memRegion stA 528 ∗ chunkAt chunkA chunk ∗
          unchunkedSendCt2PlacedRoAt ∗ tokenInitPlacedAt ∗ reduceTablePlacedAt ∗
          A.pool lim (M.stepEvents evs st_cost) sf ∗
          stackAt sp_call ct1AcknowledgedRecvEkChunkStack) ∗ Frame) post) :
    SepWP prog target_pc s P post :=
  call_ct1AcknowledgedRecvEkChunk_placed_ofPrePostEnv hcall st_cost outA stA chunkA st chunk res
    hstrict hrecv hfit hcro hpc hrun hsp hsp_align hlr htrace hx0 hx1 hx2 hx3 hsplit hnext

theorem call_ct1AcknowledgedRecvEkChunk_sepWPp_placed_ofPrePostEnv [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {F : ShaCompress} {K : MlKem}
    {PreEnv PostEnv : Ct1AcknowledgedRecvEkChunkGhost F → List AllocEvent → Prop}
    {prog : Program} {entry ret_pc target_pc : BitVec 64}
    (hcall : subroutine_ok prog entry
      (withLsCodeRoLoaded lsmpl
        (ct1AcknowledgedRecvEkChunkPlacedSpecOfPrePostEnv M A lim F K PreEnv PostEnv)))
    (st_cost : M.σ)
    (outA stA chunkA : BitVec 64)
    (st : Chunked.SendCt.Ct1Acknowledged spqrPolyApi (spqrAuthApi F))
    (chunk : Chunk)
    (res : Except Error (Chunked.SendCt.Ct1AcknowledgedRecvChunk spqrPolyApi (spqrAuthApi F)))
    (hstrict : PolyDecoderStrictSorted st.receiving_ek)
    (hrecv : st.recv_ek_chunk K st.uc.epoch chunk = StatesResult.ofError res)
    (hfit : FitsEnv M lim st_cost (PreEnv ⟨outA, stA, chunkA, st, chunk, res⟩))
    {s0 s : State} {sp_call : BitVec 64} {P Frame : SepProp}
    {post Q_panic : State → SepProp → Prop}
    (hcro : LibsignalCodeRoLoaded lsmpl s.mem)
    (hpc : s.pc = entry) (hrun : s.status = .Running) (hsp : s.sp = sp_call)
    (hsp_align : (sp_call &&& 15#64 == 0#64) = true)
    (hlr : s.readReg64 Reg.lr = ret_pc) (htrace : TraceCalleeSaved s s0)
    (hx0 : s.readReg64 Reg.x0 = outA) (hx1 : s.readReg64 Reg.x1 = stA)
    (hx2 : s.readReg64 Reg.x2 = st.uc.epoch) (hx3 : s.readReg64 Reg.x3 = chunkA)
    (hsplit : P = (memRegion outA 528 ∗
      chunkedCt1AcknowledgedAt A.repAlloc stA st ∗ chunkAt chunkA chunk ∗
      unchunkedSendCt2PlacedRoAt ∗ tokenInitPlacedAt ∗ reduceTablePlacedAt ∗
      A.pool lim st_cost s ∗ stackAt sp_call ct1AcknowledgedRecvEkChunkStack) ∗ Frame)
    (hnext : ∀ (sf : State) (evs : List AllocEvent),
      sf.pc = ret_pc → sf.status = .Running →
      sf.sp = sp_call → CalleeSavedPreserved s sf → TraceCalleeSaved sf s0 →
      PostEnv ⟨outA, stA, chunkA, st, chunk, res⟩ evs →
      SepWPp prog target_pc sf
        ((ct1AcknowledgedRecvEkChunkResAt A.repAlloc outA res ∗
          memRegion stA 528 ∗ chunkAt chunkA chunk ∗
          unchunkedSendCt2PlacedRoAt ∗ tokenInitPlacedAt ∗ reduceTablePlacedAt ∗
          A.pool lim (M.stepEvents evs st_cost) sf ∗
          stackAt sp_call ct1AcknowledgedRecvEkChunkStack) ∗ Frame) post Q_panic) :
    SepWPp prog target_pc s P post Q_panic :=
  SepWPp.of_sepWP <|
    call_ct1AcknowledgedRecvEkChunk_placed_ofPrePostEnv (target_pc := ret_pc)
      hcall st_cost outA stA chunkA st chunk res
      hstrict hrecv hfit hcro hpc hrun hsp hsp_align hlr htrace hx0 hx1 hx2 hx3 hsplit
      (fun sf evs hpc_sf hrun_sf hsp_sf hcs_sf htr_sf hevs =>
        SepWP.done hpc_sf hrun_sf (hnext sf evs hpc_sf hrun_sf hsp_sf hcs_sf htr_sf hevs))

theorem call_ct1AcknowledgedRecvEkChunk_sepWPp_placed [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {F : ShaCompress} {K : MlKem}
    {prog : Program} {entry ret_pc target_pc : BitVec 64}
    (hcall : subroutine_ok prog entry
      (withLsCodeRoLoaded lsmpl (ct1AcknowledgedRecvEkChunkPlacedSpec M A lim F K)))
    (st_cost : M.σ)
    (outA stA chunkA : BitVec 64)
    (st : Chunked.SendCt.Ct1Acknowledged spqrPolyApi (spqrAuthApi F))
    (chunk : Chunk)
    (res : Except Error (Chunked.SendCt.Ct1AcknowledgedRecvChunk spqrPolyApi (spqrAuthApi F)))
    (hstrict : PolyDecoderStrictSorted st.receiving_ek)
    (hrecv : st.recv_ek_chunk K st.uc.epoch chunk = StatesResult.ofError res)
    (hfit : FitsEnv M lim st_cost
      (Ct1AcknowledgedRecvEkChunkPreEnv K ⟨outA, stA, chunkA, st, chunk, res⟩))
    {s0 s : State} {sp_call : BitVec 64} {P Frame : SepProp}
    {post Q_panic : State → SepProp → Prop}
    (hcro : LibsignalCodeRoLoaded lsmpl s.mem)
    (hpc : s.pc = entry) (hrun : s.status = .Running) (hsp : s.sp = sp_call)
    (hsp_align : (sp_call &&& 15#64 == 0#64) = true)
    (hlr : s.readReg64 Reg.lr = ret_pc) (htrace : TraceCalleeSaved s s0)
    (hx0 : s.readReg64 Reg.x0 = outA) (hx1 : s.readReg64 Reg.x1 = stA)
    (hx2 : s.readReg64 Reg.x2 = st.uc.epoch) (hx3 : s.readReg64 Reg.x3 = chunkA)
    (hsplit : P = (memRegion outA 528 ∗
      chunkedCt1AcknowledgedAt A.repAlloc stA st ∗ chunkAt chunkA chunk ∗
      unchunkedSendCt2PlacedRoAt ∗ tokenInitPlacedAt ∗ reduceTablePlacedAt ∗
      A.pool lim st_cost s ∗ stackAt sp_call ct1AcknowledgedRecvEkChunkStack) ∗ Frame)
    (hnext : ∀ (sf : State) (evs : List AllocEvent),
      sf.pc = ret_pc → sf.status = .Running →
      sf.sp = sp_call → CalleeSavedPreserved s sf → TraceCalleeSaved sf s0 →
      Ct1AcknowledgedRecvEkChunkPostEnv K ⟨outA, stA, chunkA, st, chunk, res⟩ evs →
      SepWPp prog target_pc sf
        ((ct1AcknowledgedRecvEkChunkResAt A.repAlloc outA res ∗
          memRegion stA 528 ∗ chunkAt chunkA chunk ∗
          unchunkedSendCt2PlacedRoAt ∗ tokenInitPlacedAt ∗ reduceTablePlacedAt ∗
          A.pool lim (M.stepEvents evs st_cost) sf ∗
          stackAt sp_call ct1AcknowledgedRecvEkChunkStack) ∗ Frame) post Q_panic) :
    SepWPp prog target_pc s P post Q_panic :=
  call_ct1AcknowledgedRecvEkChunk_sepWPp_placed_ofPrePostEnv hcall st_cost outA stA chunkA st chunk res
    hstrict hrecv hfit hcro hpc hrun hsp hsp_align hlr htrace hx0 hx1 hx2 hx3 hsplit hnext

theorem ct1Ack_step_4468_err_19324_placed [LibsignalPlacement]
    {ext : String → Option (State → State)}
    (s : State) (fsp out w1 w2 w3 sp_w61 o0 o1 o2 o3 : BitVec 64) (Frame : SepProp)
    (hfsp_align : (fsp &&& 15#64 == 0#64) = true)
    (hpc : s.pc = lsmpl.base 332 + 4468#64)
    (hrun : s.status = .Running) (hsp : s.sp = fsp) (hx19 : s.readReg64 .x19 = out) :
    SepWP (lsProg_332 (Rust.withPanics ext))
      (lsmpl.base 332 + 19324#64) s
      (((fsp + 1856#64) ↦₆₄ 0xfffffffffffffffe#64) ∗ ((fsp + 1864#64) ↦₆₄ w1) ∗
       ((fsp + 1872#64) ↦₆₄ w2) ∗ ((fsp + 1880#64) ↦₆₄ w3) ∗ ((fsp + 496#64) ↦₆₄ sp_w61) ∗
       (out ↦₆₄ o0) ∗ ((out + 8#64) ↦₆₄ o1) ∗ ((out + 16#64) ↦₆₄ o2) ∗ ((out + 24#64) ↦₆₄ o3) ∗ Frame)
      (fun sm Pm =>
        VmPreserved s sm ∧
        (Pm ⊢
          ((fsp + 1856#64) ↦₆₄ 0xfffffffffffffffe#64) ∗ ((fsp + 1864#64) ↦₆₄ w1) ∗
          ((fsp + 1872#64) ↦₆₄ w2) ∗ ((fsp + 1880#64) ↦₆₄ w3) ∗ ((fsp + 496#64) ↦₆₄ w3) ∗
          (out ↦₆₄ noneCap) ∗ ((out + 8#64) ↦₆₄ w1) ∗ ((out + 16#64) ↦₆₄ w2) ∗ ((out + 24#64) ↦₆₄ w3) ∗ Frame) ∧
        sm.sp = fsp ∧ sm.readReg64 .x29 = s.readReg64 .x29 ∧ TraceCalleeSaved sm s) := by
  subst hsp hx19
  rw [lsmpl_base_332_eq] at hpc ⊢
  dsimp only [lsProg_332, noneCap, BitVec.ofNat_eq_ofNat] at hpc ⊢
  by_vm_steps (
    wp_simp_pre [sepConj_assoc]
    wp_steps
    wp_done
  )

theorem ct1Ack_err_4468_ret_placed [LibsignalPlacement]
    {A : RustAlloc} {F : ShaCompress} {ext : String → Option (State → State)}
    (s0 s1 : State) (outA selfA : BitVec 64) (err : Error)
    (sp : SendEkSpills) (P_rest : SepProp) (hsp0_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hpc : s1.pc = lsmpl.base 332 + 4468#64)
    (hrun : s1.status = .Running) (hsp : s1.sp = s0.sp - 4240#64)
    (hx19 : s1.readReg64 .x19 = outA) (htr : TraceCalleeSaved s1 s0) :
    SepWP (lsProg_332 (Rust.withPanics ext)) (s0.readReg64 .x30) s1
      (P_rest ∗ memRegion outA v1RecvSize ∗ memRegion selfA chunkedStatesSize ∗
        ct1AcknowledgedRecvEkChunkResAt A (F := F) ((s0.sp - 4240#64) + 1856#64) (.error err) ∗
        stackAt (s0.sp - 4240#64) statesRecvCalleeStackX ∗ sendEkSpillsAt (s0.sp - 4240#64) sp ∗
        memRegion ((s0.sp - 4240#64) + 576#64) 376 ∗ memRegion ((s0.sp - 4240#64) + 976#64) 880 ∗
        memRegion ((s0.sp - 4240#64) + 2384#64) 352 ∗ sendEkUnusedAt (s0.sp - 4240#64) ∗
        statesRecvSavedCells s0)
      (fun sf Pf =>
        VmPreserved s1 sf ∧
        (Pf ⊢ P_rest ∗ resultV1RecvAt A (F := F) outA (.error (.err .erroneousDataReceived)) ∗
          memRegion selfA chunkedStatesSize ∗ stackAt s0.sp statesRecvStackX) ∧
        sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf ∧ sf.trace = s0.trace) := by
  have hfsp_align : ((s0.sp - 4240#64) &&& 15#64 == 0#64) = true :=
    spAligned_sub s0.sp 4240#64 hsp0_align (by decide)
  set fsp := s0.sp - 4240#64
  refine SepWP.fold (ct1Ack_memRegion_out_960_split_4words outA) (by sep_focus) ?_
  wp_pull_exists; rename_i o0 o1 o2 o3
  refine SepWP.fold (ct1Ack_err_1856_split (A := A) (F := F) fsp err) (by sep_focus) ?_
  wp_pull_exists; rename_i w1 w2 w3
  rw [ct1AckSpillsAt_split_w61 fsp sp]
  refine SepWP.weaken_pre (Entails.of_eq (show _ =
    ⌜∃ bs : List (BitVec 8), bs.length = 7 ∧ 12#8 :: bs = unpack64 w1⌝ ∗
    (((fsp + 1856#64) ↦₆₄ 0xfffffffffffffffe#64) ∗ ((fsp + 1864#64) ↦₆₄ w1) ∗
     ((fsp + 1872#64) ↦₆₄ w2) ∗ ((fsp + 1880#64) ↦₆₄ w3) ∗ ((fsp + 496#64) ↦₆₄ sp.w61) ∗
     (outA ↦₆₄ o0) ∗ ((outA + 8#64) ↦₆₄ o1) ∗ ((outA + 16#64) ↦₆₄ o2) ∗ ((outA + 24#64) ↦₆₄ o3) ∗
     (P_rest ∗ memRegion (outA + 32#64) 928 ∗ memRegion selfA chunkedStatesSize ∗
      memRegion (fsp + 1888#64) 496 ∗ stackAt fsp statesRecvCalleeStackX ∗
      ct1AckSpillsRestAt fsp sp ∗ memRegion (fsp + 576#64) 376 ∗
      memRegion (fsp + 976#64) 880 ∗ memRegion (fsp + 2384#64) 352 ∗
      sendEkUnusedAt fsp ∗ statesRecvSavedCells s0)) by sep_ac_rfl)) ?_
  refine SepWP.pure_elim fun hw1 => ?_
  refine seq_vm_clean (mid := lsmpl.base 332 + 19324#64)
    (P_mid := stackAt fsp statesRecvCalleeStackX ∗ memRegion fsp 4144 ∗ statesRecvSavedCells s0 ∗
      (P_rest ∗ resultV1RecvAt A (F := F) outA (.error (.err .erroneousDataReceived)) ∗
       memRegion selfA chunkedStatesSize))
    (Q := fun s2 => s2.sp = fsp ∧ TraceCalleeSaved s2 s0)
    ?_ ?_
  · have hstep := ct1Ack_step_4468_err_19324_placed (ext := ext) s1 fsp outA w1 w2 w3 sp.w61 o0 o1 o2 o3
      (P_rest ∗ memRegion (outA + 32#64) 928 ∗ memRegion selfA chunkedStatesSize ∗
       memRegion (fsp + 1888#64) 496 ∗ stackAt fsp statesRecvCalleeStackX ∗
       ct1AckSpillsRestAt fsp sp ∗ memRegion (fsp + 576#64) 376 ∗
       memRegion (fsp + 976#64) 880 ∗ memRegion (fsp + 2384#64) 352 ∗
       sendEkUnusedAt fsp ∗ statesRecvSavedCells s0)
      hfsp_align hpc hrun hsp hx19
    refine SepWP.mono hstep ?_
    intro s2 Pm _ _ ⟨hvm1, hPm, hsp2, _, htr2⟩
    refine ⟨hvm1, Entails.trans hPm ?_, hsp2, htr2.trans htr⟩
    have hout := ct1Ack_err_out_recompose A (F := F) outA w1 w2 w3 hw1
    have h1856 := ct1Ack_err_1856_rejoin_880 fsp 0xfffffffffffffffe#64 w1 w2 w3
    have hsp_rejoin := ct1AckSpillsAt_rejoin_w61 fsp sp w3
    have h4144 := sendEkFrame_entails_memRegion_4144 fsp { sp with w61 := w3 }
    refine Entails.trans (Entails.of_eq (show _ =
      stackAt fsp statesRecvCalleeStackX ∗
      ((((fsp + 496#64) ↦₆₄ w3) ∗ ct1AckSpillsRestAt fsp sp) ∗
       memRegion (fsp + 576#64) 376 ∗ memRegion (fsp + 976#64) 880 ∗
       (((fsp + 1856#64) ↦₆₄ 0xfffffffffffffffe#64) ∗ ((fsp + 1864#64) ↦₆₄ w1) ∗
        ((fsp + 1872#64) ↦₆₄ w2) ∗ ((fsp + 1880#64) ↦₆₄ w3) ∗
        memRegion (fsp + 1888#64) 496 ∗ memRegion (fsp + 2384#64) 352) ∗
       sendEkUnusedAt fsp) ∗
      statesRecvSavedCells s0 ∗
      (P_rest ∗
       ((outA ↦₆₄ noneCap) ∗ ((outA + 8#64) ↦₆₄ w1) ∗ ((outA + 16#64) ↦₆₄ w2) ∗
        ((outA + 24#64) ↦₆₄ w3) ∗ memRegion (outA + 32#64) 928) ∗
       memRegion selfA chunkedStatesSize) by sep_ac_rfl)) ?_
    rw [hsp_rejoin]
    refine Entails.trans (sepConj_mono_right (sepConj_mono
      (Entails.trans (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
        (sepConj_mono_left h1856)))) h4144)
      (sepConj_mono_right (sepConj_mono_right (sepConj_mono_left hout))))) ?_
    exact Entails.of_eq (by sep_ac_rfl)
  · intro s2 hpc2 hrun2 hvm1 ⟨hsp2, htr2⟩
    refine SepWP.mono
      (ArmNoHeaderReceivedStepsPlacedBudgetAux.states_recv_epilogue_19324_placed (ext := ext) s0 s2
        (P_rest ∗ resultV1RecvAt A (F := F) outA (.error (.err .erroneousDataReceived)) ∗
         memRegion selfA chunkedStatesSize)
        hsp0_align hpc2 hrun2 hsp2 htr2)
      (fun sf Pf _ _ ⟨hvm2, hPf, hsp_sf, hcs_sf, htr_sf⟩ =>
        ⟨hvm1.trans hvm2, Entails.trans hPf (Entails.of_eq (by sep_ac_rfl)), hsp_sf, hcs_sf, htr_sf⟩)

/-! ## 3. `.stillReceiving` Path (`+4468 -> +13292 -> +13660 -> +4924 -> s0.x30`) -/

set_option maxHeartbeats 2400000 in
theorem ct1Ack_step_4468_still_4924_placed [LibsignalPlacement]
    {ext : String → Option (State → State)}
    (s : State) (fsp w592_old we50 : BitVec 64) (q576_old qe40 qe60 : BitVec 128)
    (w : Words66) (sp : SendEkSpills) (Frame : SepProp)
    (hcap : w.b0.w0.toNat < 2 ^ 63)
    (hfsp_align : (fsp &&& 15#64 == 0#64) = true)
    (hpc : s.pc = lsmpl.base 332 + 4468#64)
    (hrun : s.status = .Running) (hsp : s.sp = fsp)
    (hx20 : s.readReg64 .x20 = fsp + 1856#64) :
    SepWP (lsProg_332 (Rust.withPanics ext))
      (lsmpl.base 332 + 4924#64) s
      (words66At (fsp + 1856#64) w ∗ sendEkSpillsAt fsp sp ∗
       ((fsp + 576#64) ↦₁₂₈ q576_old) ∗ ((fsp + 592#64) ↦₆₄ w592_old) ∗
       ((fsp + 3648#64) ↦₁₂₈ qe40) ∗ ((fsp + 3664#64) ↦₆₄ we50) ∗ ((fsp + 3680#64) ↦₁₂₈ qe60) ∗ Frame)
      (fun sm Pm =>
        VmPreserved s sm ∧
        (Pm ⊢ words66At (fsp + 1856#64) w ∗ sendEkSpillsAt fsp (ct1AckSpillsStill4924 sp w) ∗
          ((fsp + 576#64) ↦₁₂₈ w.q63) ∗ ((fsp + 592#64) ↦₆₄ w.w65) ∗
          ((fsp + 3648#64) ↦₁₂₈ w.q63) ∗ ((fsp + 3664#64) ↦₆₄ w.w65) ∗ ((fsp + 3680#64) ↦₁₂₈ w.q60) ∗ Frame) ∧
        sm.sp = fsp ∧ sm.readReg64 .x0 = w.b5.w5 ∧ sm.readReg64 .x1 = w.b0.w0 ∧
        sm.readReg64 .x2 = w.b5.w7 ∧ sm.readReg64 .x3 = w.b2.w9 ∧
        sm.readReg64 .x4 = w.b4.w9 ∧ sm.readReg64 .x5 = w.b4.w8 ∧
        sm.readReg64 .x6 = w.b5.w0 ∧ sm.readReg64 .x7 = w.b1.w9 ∧
        sm.readReg64 .x10 = w.b1.w6 ∧ sm.readReg64 .x11 = w.b5.w4 ∧
        sm.readReg64 .x12 = w.b4.w0 ∧ sm.readReg64 .x13 = w.b5.w1 ∧
        sm.readReg64 .x15 = w.b2.w7 ∧ sm.readReg64 .x16 = w.b4.w7 ∧
        sm.readReg64 .x17 = w.b4.w5 ∧ sm.readReg64 .x18 = w.b5.w3 ∧
        sm.readReg64 .x19 = s.readReg64 .x19 ∧ sm.readReg64 .x22 = w.b5.w2 ∧
        sm.readReg64 .x24 = w.b3.w1 ∧ sm.readReg64 .x25 = w.b3.w9 ∧
        sm.readReg64 .x26 = w.b0.w5 ∧ sm.readReg64 .x29 = s.readReg64 .x29 ∧
        sm.readReg64 .x30 = w.b5.w9 ∧ TraceCalleeSaved sm s) := by
  subst hsp
  have hcmn2 := ct1Ack_cap_add_two_beq_zero_false hcap
  have hne2 : (w.b0.w0 + 2#64 != 0#64) = true := by simp [bne, hcmn2]
  have hcmn1 := ct1Ack_cap_add_one_beq_zero_false hcap
  have hne1 : (w.b0.w0 + 1#64 != 0#64) = true := by simp [bne, hcmn1]
  rw [lsmpl_base_332_eq] at hpc ⊢
  dsimp only [lsProg_332, BitVec.ofNat_eq_ofNat] at hpc ⊢
  by_vm_steps (
    wp_simp_pre [words66At, sendEkSpillsAt, ct1AckSpillsStill4924, words10At, pointsTo128,
      bv_add_lit_add_lit_recv, Nat.reduceAdd, sepConj_assoc]
    wp_steps 256
    simp only [words66At, sendEkSpillsAt, ct1AckSpillsStill4924, words10At, pointsTo128,
      bv_add_lit_add_lit_recv, Nat.reduceAdd, sepConj_assoc]
    wp_done
  )

theorem ct1Ack_still_4468_ret_placed [LibsignalPlacement]
    {A : RustAlloc} {F : ShaCompress} {ext : String → Option (State → State)}
    (hmemcpy_sat : HookSat (Rust.withPanics ext) spqrMemcpySym (withVmPreserved sessionMemcpySpec))
    (s0 s1 : State) (outA selfA : BitVec 64)
    (outSt : Chunked.SendCt.Ct1Acknowledged spqrPolyApi (spqrAuthApi F))
    (sp : SendEkSpills) (P_rest : SepProp) (hsp0_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hpc : s1.pc = lsmpl.base 332 + 4468#64)
    (hrun : s1.status = .Running) (hsp : s1.sp = s0.sp - 4240#64)
    (hx19 : s1.readReg64 .x19 = outA) (hx20 : s1.readReg64 .x20 = (s0.sp - 4240#64) + 1856#64)
    (htr : TraceCalleeSaved s1 s0) :
    SepWP (lsProg_332 (Rust.withPanics ext)) (s0.readReg64 .x30) s1
      (P_rest ∗ memRegion outA v1RecvSize ∗ memRegion selfA chunkedStatesSize ∗
        ct1AcknowledgedRecvEkChunkResAt A (F := F) ((s0.sp - 4240#64) + 1856#64) (.ok (.stillReceiving outSt)) ∗
        stackAt (s0.sp - 4240#64) statesRecvCalleeStackX ∗ sendEkSpillsAt (s0.sp - 4240#64) sp ∗
        memRegion ((s0.sp - 4240#64) + 576#64) 376 ∗ memRegion ((s0.sp - 4240#64) + 976#64) 880 ∗
        memRegion ((s0.sp - 4240#64) + 2384#64) 352 ∗ sendEkUnusedAt (s0.sp - 4240#64) ∗
        statesRecvSavedCells s0)
      (fun sf Pf =>
        VmPreserved s1 sf ∧
        (Pf ⊢ P_rest ∗ resultV1RecvAt A (F := F) outA (.ok { key := none, state := .ct1Acknowledged outSt }) ∗
          memRegion selfA chunkedStatesSize ∗ stackAt s0.sp statesRecvStackX) ∧
        sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf ∧ sf.trace = s0.trace) := by
  have hfsp_align : ((s0.sp - 4240#64) &&& 15#64 == 0#64) = true :=
    spAligned_sub s0.sp 4240#64 hsp0_align (by decide)
  set fsp := s0.sp - 4240#64
  dsimp only [ct1AcknowledgedRecvEkChunkResAt]
  refine SepWP.fold (chunkedCt1AcknowledgedAt_extract66 A (fsp + 1856#64) outSt) (by sep_focus) ?_
  wp_pull_exists; rename_i w
  refine SepWP.fold (memRegion_576_376_split_ekTail fsp) (by sep_focus) ?_
  wp_pull_exists; rename_i q576_old w592_old
  refine SepWP.fold (sendEkUnusedAt_split_e40 fsp) (by sep_focus) ?_
  wp_pull_exists; rename_i qe40 we50 qe60
  refine SepWP.weaken_pre (Entails.of_eq (show _ =
    ⌜w.b0.w0.toNat < 2 ^ 63 ∧ w.b1.w5 = outSt.uc.epoch⌝ ∗
    (words66At (fsp + 1856#64) w ∗ sendEkSpillsAt fsp sp ∗
     ((fsp + 576#64) ↦₁₂₈ q576_old) ∗ ((fsp + 592#64) ↦₆₄ w592_old) ∗
     ((fsp + 3648#64) ↦₁₂₈ qe40) ∗ ((fsp + 3664#64) ↦₆₄ we50) ∗ ((fsp + 3680#64) ↦₁₂₈ qe60) ∗
     (P_rest ∗ memRegion outA v1RecvSize ∗ memRegion selfA chunkedStatesSize ∗
      relocatedHeap (fun dst => chunkedCt1AcknowledgedAt A dst outSt) (wordsBytes (words66List w)) ∗
      stackAt fsp statesRecvCalleeStackX ∗ memRegion (fsp + 600#64) 352 ∗
      memRegion (fsp + 976#64) 880 ∗ memRegion (fsp + 2384#64) 352 ∗
      ct1AckUnusedRestAt fsp ∗ statesRecvSavedCells s0)) by sep_ac_rfl)) ?_
  refine SepWP.pure_elim fun ⟨hcap, _⟩ => ?_
  set sp1 := ct1AckSpillsStill4924 sp w
  refine seq_vm_clean (mid := lsmpl.base 332 + 4924#64)
    (P_mid := P_rest ∗ memRegion outA v1RecvSize ∗ memRegion selfA chunkedStatesSize ∗
      relocatedHeap (fun dst => chunkedCt1AcknowledgedAt A dst outSt) (wordsBytes (words66List w)) ∗
      stackAt fsp statesRecvCalleeStackX ∗ sendEkSpillsAt fsp sp1 ∗
      ekTail376 w.q63 w.w65 (fsp + 576#64) ∗ memRegion (fsp + 976#64) 880 ∗
      memRegion (fsp + 1856#64) 880 ∗ sendEkUnusedAt fsp ∗ statesRecvSavedCells s0)
    (Q := fun s2 =>
      s2.sp = fsp ∧ s2.readReg64 .x0 = w.b5.w5 ∧ s2.readReg64 .x1 = w.b0.w0 ∧
      s2.readReg64 .x2 = w.b5.w7 ∧ s2.readReg64 .x3 = w.b2.w9 ∧
      s2.readReg64 .x4 = w.b4.w9 ∧ s2.readReg64 .x5 = w.b4.w8 ∧
      s2.readReg64 .x6 = w.b5.w0 ∧ s2.readReg64 .x7 = w.b1.w9 ∧
      s2.readReg64 .x10 = w.b1.w6 ∧ s2.readReg64 .x11 = w.b5.w4 ∧
      s2.readReg64 .x12 = w.b4.w0 ∧ s2.readReg64 .x13 = w.b5.w1 ∧
      s2.readReg64 .x15 = w.b2.w7 ∧ s2.readReg64 .x16 = w.b4.w7 ∧
      s2.readReg64 .x17 = w.b4.w5 ∧ s2.readReg64 .x18 = w.b5.w3 ∧
      s2.readReg64 .x19 = outA ∧ s2.readReg64 .x22 = w.b5.w2 ∧
      s2.readReg64 .x24 = w.b3.w1 ∧ s2.readReg64 .x25 = w.b3.w9 ∧
      s2.readReg64 .x26 = w.b0.w5 ∧ s2.readReg64 .x30 = w.b5.w9 ∧ TraceCalleeSaved s2 s0)
    ?_ ?_
  · have hstep1 := ct1Ack_step_4468_still_4924_placed (ext := ext) s1 fsp w592_old we50 q576_old qe40 qe60 w sp
      (P_rest ∗ memRegion outA v1RecvSize ∗ memRegion selfA chunkedStatesSize ∗
       relocatedHeap (fun dst => chunkedCt1AcknowledgedAt A dst outSt) (wordsBytes (words66List w)) ∗
       stackAt fsp statesRecvCalleeStackX ∗ memRegion (fsp + 600#64) 352 ∗
       memRegion (fsp + 976#64) 880 ∗ memRegion (fsp + 2384#64) 352 ∗
       ct1AckUnusedRestAt fsp ∗ statesRecvSavedCells s0)
      hcap hfsp_align hpc hrun hsp hx20
    refine SepWP.mono hstep1 ?_
    intro s2 Pm _ _ ⟨hvm1, hPm, hsp2, h2_0, h2_1, h2_2, h2_3, h2_4, h2_5, h2_6, h2_7,
      h2_10, h2_11, h2_12, h2_13, h2_15, h2_16, h2_17, h2_18, h2_19, h2_22,
      h2_24, h2_25, h2_26, _, h2_30, htr2⟩
    refine ⟨hvm1, Entails.trans hPm ?_, hsp2, h2_0, h2_1, h2_2, h2_3, h2_4, h2_5, h2_6, h2_7,
      h2_10, h2_11, h2_12, h2_13, h2_15, h2_16, h2_17, h2_18, h2_19.trans hx19, h2_22,
      h2_24, h2_25, h2_26, h2_30, htr2.trans htr⟩
    have h880 := words66At_352_entails_memRegion_880 fsp w
    have hunused := ct1AckUnusedRest_entails_sendEkUnusedAt fsp w.q63 w.w65 w.q60
    refine Entails.trans (Entails.of_eq (show _ =
      ((words66At (fsp + 1856#64) w ∗ memRegion (fsp + 2384#64) 352) ∗
       (((fsp + 3648#64) ↦₁₂₈ w.q63) ∗ ((fsp + 3664#64) ↦₆₄ w.w65) ∗
        ((fsp + 3680#64) ↦₁₂₈ w.q60) ∗ ct1AckUnusedRestAt fsp)) ∗
      (P_rest ∗ memRegion outA v1RecvSize ∗ memRegion selfA chunkedStatesSize ∗
       relocatedHeap (fun dst => chunkedCt1AcknowledgedAt A dst outSt) (wordsBytes (words66List w)) ∗
       stackAt fsp statesRecvCalleeStackX ∗ sendEkSpillsAt fsp sp1 ∗
       ekTail376 w.q63 w.w65 (fsp + 576#64) ∗ memRegion (fsp + 976#64) 880 ∗ statesRecvSavedCells s0) by
        dsimp only [ekTail376, sp1]; simp only [bv_add_lit_add_lit_recv, Nat.reduceAdd]; sep_ac_rfl)) ?_
    exact Entails.trans (sepConj_mono_left (sepConj_mono h880 hunused)) (Entails.of_eq (by sep_ac_rfl))
  · intro s2 hpc2 hrun2 hvm1 ⟨hsp2, h2_0, h2_1, h2_2, h2_3, h2_4, h2_5, h2_6, h2_7,
      h2_10, h2_11, h2_12, h2_13, h2_15, h2_16, h2_17, h2_18, h2_19, h2_22,
      h2_24, h2_25, h2_26, h2_30, htr2⟩
    set sp2 := ct1AckSpills4924 s2 sp1
    refine seq_vm_clean (mid := lsmpl.base 332 + 18996#64)
      (P_mid := (P_rest ∗ memRegion selfA chunkedStatesSize ∗
         relocatedHeap (fun dst => chunkedCt1AcknowledgedAt A dst outSt) (wordsBytes (words66List w))) ∗
        memRegion outA v1RecvSize ∗ stackAt fsp statesRecvCalleeStackX ∗ sendEkSpillsAt fsp sp2 ∗
        ekTail376 w.q63 w.w65 (fsp + 576#64) ∗ memRegion (fsp + 976#64) 880 ∗
        memRegion (fsp + 1856#64) 880 ∗ sendEkUnusedAt fsp ∗ statesRecvSavedCells s0)
      (Q := fun s3 => s3.sp = fsp ∧ s3.readReg64 .x19 = outA ∧
        writebackWords63 s3 sp2 =
          { b0 := w.b0, b1 := w.b1, b2 := w.b2, b3 := w.b3, b4 := w.b4, b5 := w.b5,
            q60 := w.q60, w62 := w.w62 } ∧ TraceCalleeSaved s3 s0)
      ?_ ?_
    · have hstep2 := ct1Ack_step_4924_18996_placed (ext := ext) s2 fsp sp1
        (P_rest ∗ memRegion outA v1RecvSize ∗ memRegion selfA chunkedStatesSize ∗
         relocatedHeap (fun dst => chunkedCt1AcknowledgedAt A dst outSt) (wordsBytes (words66List w)) ∗
         stackAt fsp statesRecvCalleeStackX ∗ ekTail376 w.q63 w.w65 (fsp + 576#64) ∗
         memRegion (fsp + 976#64) 880 ∗ memRegion (fsp + 1856#64) 880 ∗
         sendEkUnusedAt fsp ∗ statesRecvSavedCells s0)
        hfsp_align hpc2 hrun2 hsp2
      refine SepWP.weaken_pre (Entails.of_eq (by sep_ac_rfl)) (SepWP.mono hstep2 ?_)
      intro s3 Pm _ _ ⟨hvm2, hPm, hsp3, h3_0, h3_1, h3_2, h3_3, h3_4, h3_5, h3_6, h3_7,
        h3_8, h3_9, h3_10, h3_11, h3_12, h3_13, h3_14, h3_15, h3_16, h3_17, h3_19,
        h3_20, h3_21, h3_22, h3_23, h3_24, h3_25, h3_26, h3_27, h3_28, _, h3_30, htr3⟩
      have hwb := writebackWords63_ct1Ack_still s2 s3 sp w
        h2_0 h2_1 h2_2 h2_3 h2_4 h2_5 h2_6 h2_7 h2_10 h2_11 h2_12 h2_13
        h2_15 h2_16 h2_17 h2_18 h2_22 h2_24 h2_25 h2_26 h2_30
        h3_0 h3_1 h3_2 h3_3 h3_4 h3_5 h3_6 h3_7 h3_8 h3_9 h3_10 h3_11 h3_12
        h3_13 h3_14 h3_15 h3_16 h3_17 h3_20 h3_21 h3_22 h3_23 h3_24 h3_25
        h3_26 h3_27 h3_28 h3_30
      refine ⟨hvm2, Entails.trans hPm (Entails.of_eq (by dsimp only [sp2]; sep_ac_rfl)),
        hsp3, h3_19.trans h2_19, hwb, htr3.trans htr2⟩
    · intro s3 hpc3 hrun3 hvm2 ⟨hsp3, h3_19, hwb, htr3⟩
      have hwrite := ArmNoHeaderReceivedStepsPlacedBudgetAux.states_recv_writeback_59e88_sat_placed
        hmemcpy_sat (relocatable_ekTail376 w.q63 w.w65)
        s0 s3 outA sp2
        (P_rest ∗ memRegion selfA chunkedStatesSize ∗
         relocatedHeap (fun dst => chunkedCt1AcknowledgedAt A dst outSt) (wordsBytes (words66List w)))
        hpc3 hrun3 hsp3 hsp0_align h3_19 htr3
      refine SepWP.mono hwrite ?_
      intro sf Pf _ _ ⟨hvm3, hPf, hsp_sf, hcs_sf, htr_sf⟩
      refine ⟨hvm1.trans (hvm2.trans hvm3), Entails.trans hPf ?_, hsp_sf, hcs_sf, htr_sf⟩
      have htag : sp2.b2.w7 = 11#64 := rfl
      have hnone : sp2.b2.w8 = noneCap := rfl
      rw [htag, hnone, hwb]
      have hout := ct1Ack_noop_out_entails_resultV1RecvAt A (F := F) outA outSt w (s3.readReg64 .x20) sp2.q200
      refine Entails.trans (Entails.of_eq (show _ =
        P_rest ∗ ((outA ↦₆₄ 11#64) ∗
         words63At (outA + 8#64)
           { b0 := w.b0, b1 := w.b1, b2 := w.b2, b3 := w.b3, b4 := w.b4, b5 := w.b5,
             q60 := w.q60, w62 := w.w62 } ∗
         ekTail376 w.q63 w.w65 (outA + 512#64) ∗ memRegion (outA + 888#64) 40 ∗
         ((outA + 928#64) ↦₆₄ noneCap) ∗ ((outA + 936#64) ↦₆₄ s3.readReg64 .x20) ∗
         ((outA + 944#64) ↦₁₂₈ sp2.q200) ∗
         relocatedHeap (fun dst => chunkedCt1AcknowledgedAt A dst outSt) (wordsBytes (words66List w))) ∗
        memRegion selfA chunkedStatesSize ∗ stackAt s0.sp statesRecvStackX by sep_ac_rfl)) ?_
      exact sepConj_mono_right (sepConj_mono_left hout)

end LibsignalBinary.Proofs.SpqrV1.States.Recv.ArmCt1Acknowledged2PlacedBudget
