/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SpqrV1.States.Recv.Dispatch
public import LibsignalBinary.Proofs.SpqrV1.States.Recv.DefsPlaced
import LibsignalBinary.Proofs.SpqrV1.Kdf.HkdfToSliceExtract
import LibsignalBinary.Proofs.SpqrV1.States.Recv.CodeSymFetch0Placed
import LibsignalBinary.Proofs.SpqrV1.States.Recv.CodeSymFetch3Placed
import LibsignalBinary.Proofs.SpqrV1.States.Recv.CodeSymFetch5Placed
import LibsignalBinary.Proofs.TripleRatchet.Prost.BytesMerge.Defs
import ProofLib.SepLogic.WPp

/-!
# `<States>::recv` (Block `332`): Relocatable Prologue, Dispatch, and Epilogues

Relocatable `[LibsignalPlacement]` proofs of the prologue, jump-table dispatch, tail-call drop/dealloc
epilogues, and shared `Ok(V1Recv)` store epilogue for Block `332`.
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 400000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

namespace LibsignalBinary.Proofs.SpqrV1.States.Recv

open Arm64 Arm64.Obj ProofLib ProofLib.ProgramReflection
open CryptoGames.LibsignalSession (ShaCompress)
open CryptoVerification
open CryptoVerification.RustHeap
open CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchetRepr
open CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalSpqrV1
open CryptoVerification.SpqrV1.Alloc
open CryptoVerification.SpqrV1.Auth
open CryptoVerification.SpqrV1.Poly
open CryptoVerification.SpqrV1.Drop
open CryptoVerification.SpqrV1.States.Leaves
open CryptoVerification.SpqrV1.States.Leaves.RecvHdrChunk
open CryptoVerification.SpqrV1.States.Recv
open CryptoVerification.CodeLayout

attribute [local irreducible] Program.fetch Program.externAt? Program.fnOff CryptoVerification.blkPC_332
attribute [local arm64_norm, local wp_norm] bv_sub_add_lit BitVec.toNat_zero
attribute [-arm64_norm]
  CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.sp_sub_688_eq_hsp
  CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.sp_add_neg688_eq_hsp
  CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.sp_sub_96_eq_hsp_592
  CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.sp_add_neg96_eq_hsp_592

attribute [local arm64_norm, local wp_norm]
  sp_sub_4240_add_4144
  sp_sub_96_add_16 sp_sub_96_add_32 sp_sub_96_add_48 sp_sub_96_add_64 sp_sub_96_add_80
  sp_sub_96_sub_4096 sp_sub_4192_sub_48 sp_sub_4240_add_4096 sp_sub_144_add_48 sp_sub_4240_add_48
  out_488_add_8 out_888_add_8 out_888_add_16 out_904_add_8 bv376_toNat

theorem lsmpl_base_332_eq [LibsignalPlacement] : lsmpl.base 332 = (blkPl_332).base := rfl

/-! ## Prologue (`+0 -> +36`) -/

/-- Relocatable prologue of `States::recv` (Block `332`, `+0 -> +36`). -/
theorem states_recv_prologue_placed [LibsignalPlacement]
    {ext : String → Option (State → State)}
    (s0 : State) (Rest : SepProp)
    (hsp0_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hpc0 : s0.pc = lsmpl.base 332)
    (hrun0 : s0.status = .Running) :
    SepWP (lsProg_332 (Rust.withPanics ext))
      (lsmpl.base 332 + 36#64)
      s0
      (stackAt s0.sp statesRecvStackX ∗ Rest)
      (fun s1 P1 =>
        (P1 ⊢
          stackAt (s0.sp - 4240#64) statesRecvCalleeStackX ∗
          memRegion (s0.sp - 4240#64) 4144 ∗
          statesRecvSavedCells s0 ∗
          Rest) ∧
        s1.sp = s0.sp - 4240#64 ∧
        s1.readReg64 .x0 = s0.readReg64 .x0 ∧
        s1.readReg64 .x1 = s0.readReg64 .x1 ∧
        s1.readReg64 .x2 = s0.readReg64 .x2 ∧
        s1.readReg64 .x3 = s0.readReg64 .x3 ∧
        s1.readReg64 .x29 = s0.sp - 96#64 ∧
        TraceCalleeSaved s1 s0) := by
  have hsp96_align : ((s0.sp - 96#64) &&& 15#64 == 0#64) = true :=
    spAligned_sub s0.sp 96#64 hsp0_align (by decide)
  have hsp4192_align : ((s0.sp - 4192#64) &&& 15#64 == 0#64) = true :=
    spAligned_sub s0.sp 4192#64 hsp0_align (by decide)
  rw [lsmpl_base_332_eq] at hpc0 ⊢
  dsimp only [lsProg_332]
  rw [stackAt_statesRecv_split_96 s0.sp, stackAt_statesRecv_split_fsp s0.sp]
  nth_rw 1 [memRegion_4144_split_cell48 (s0.sp - 4240#64)]
  cells_unfold
  wp_simp_pre [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc, sp_sub_4240_add_48]
  apply ProofLib.SepWP.exists_left; intro v48
  apply ProofLib.SepWP.exists_left; intro v_fp
  apply ProofLib.SepWP.exists_left; intro v_lr
  apply ProofLib.SepWP.exists_left; intro v_x28
  apply ProofLib.SepWP.exists_left; intro v_x27
  apply ProofLib.SepWP.exists_left; intro v_x26
  apply ProofLib.SepWP.exists_left; intro v_x25
  apply ProofLib.SepWP.exists_left; intro v_x24
  apply ProofLib.SepWP.exists_left; intro v_x23
  apply ProofLib.SepWP.exists_left; intro v_x22
  apply ProofLib.SepWP.exists_left; intro v_x21
  apply ProofLib.SepWP.exists_left; intro v_x20
  apply ProofLib.SepWP.exists_left; intro v_x19
  wp_steps
  have hjoin4144 := cell48_4088_entails_memRegion_4144 (s0.sp - 4240#64) 0#64
  rw [sp_sub_4240_add_48] at hjoin4144
  have h4184 : (s0.sp - 4240#64) + 56#64 = s0.sp - 4184#64 := by bv_omega
  rw [h4184] at hjoin4144 ⊢
  refine SepWP.focus_weaken hjoin4144 (by sep_focus) ?_
  refine SpqrV1.States.Recv.align_pre ?_ ?_
  · simp only [statesRecvSavedCells, Reg.x19, Reg.x20, Reg.x21, Reg.x22, Reg.x23, Reg.x24,
      Reg.x25, Reg.x26, Reg.x27, Reg.x28, Reg.x29, Reg.x30]
    exact Entails.of_eq (by ac_rfl)
  · wp_done

/-! ## Shared Direct Epilogue (`+19324 -> s0.x30`) and Tail-Call Epilogues -/

/-- Relocatable shared direct epilogue at `+19324` (Block `332`):
    restores `sp = s0.sp` and `x19..x30` from `statesRecvSavedCells s0`, folds the stack back into
    `stackAt s0.sp statesRecvStackX`, and returns to `s0.readReg64 .x30`. -/
theorem states_recv_epilogue_19324_placed [LibsignalPlacement]
    {ext : String → Option (State → State)}
    (s0 s1 : State) (Rest : SepProp)
    (hsp0_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hpc1 : s1.pc = lsmpl.base 332 + 19324#64)
    (hrun1 : s1.status = .Running)
    (hsp1 : s1.sp = s0.sp - 4240#64)
    (htr1 : TraceCalleeSaved s1 s0) :
    SepWP (lsProg_332 (Rust.withPanics ext)) (s0.readReg64 .x30) s1
      (stackAt (s0.sp - 4240#64) statesRecvCalleeStackX ∗
        memRegion (s0.sp - 4240#64) 4144 ∗
        statesRecvSavedCells s0 ∗
        Rest)
      (fun sf Pf =>
        (Pf ⊢ Rest ∗ stackAt s0.sp statesRecvStackX) ∧
        sf.sp = s0.sp ∧
        CalleeSavedPreserved s0 sf ∧
        sf.trace = s0.trace) := by
  have hsp96_align : ((s0.sp - 96#64) &&& 15#64 == 0#64) = true :=
    spAligned_sub s0.sp 96#64 hsp0_align (by decide)
  rw [lsmpl_base_332_eq] at hpc1
  dsimp only [lsProg_332]
  unfold statesRecvSavedCells
  wp_steps
  refine SpqrV1.States.Recv.align_pre ?_ ?_
  · have hrest := stack_restore_statesRecv s0
    unfold statesRecvSavedCells at hrest
    refine Entails.trans
      (Entails.of_eq (show _ =
        Rest ∗
        (stackAt (s0.sp - 4240#64) statesRecvCalleeStackX ∗
         memRegion (s0.sp - 4240#64) 4144 ∗
         (((s0.sp - 96#64) ↦₆₄ s0.readReg64 .x29) ∗
          ((s0.sp - 88#64) ↦₆₄ s0.readReg64 .x30) ∗
          ((s0.sp - 80#64) ↦₆₄ s0.readReg64 .x28) ∗
          ((s0.sp - 72#64) ↦₆₄ s0.readReg64 .x27) ∗
          ((s0.sp - 64#64) ↦₆₄ s0.readReg64 .x26) ∗
          ((s0.sp - 56#64) ↦₆₄ s0.readReg64 .x25) ∗
          ((s0.sp - 48#64) ↦₆₄ s0.readReg64 .x24) ∗
          ((s0.sp - 40#64) ↦₆₄ s0.readReg64 .x23) ∗
          ((s0.sp - 32#64) ↦₆₄ s0.readReg64 .x22) ∗
          ((s0.sp - 24#64) ↦₆₄ s0.readReg64 .x21) ∗
          ((s0.sp - 16#64) ↦₆₄ s0.readReg64 .x20) ∗
          ((s0.sp - 8#64) ↦₆₄ s0.readReg64 .x19))) by ac_rfl))
      (sepConj_mono_right hrest)
  · wp_done

/-- Relocatable tail-call epilogue at `+192` (Block `332`):
    restores `sp = s0.sp` and `x19..x30`, tail-calls `__rust_dealloc(ptr, cap, 1)`,
    and returns to `s0.readReg64 .x30`. -/
theorem states_recv_tail_dealloc_192_placed [LibsignalPlacement]
    {A : RustAlloc} {ext : String → Option (State → State)}
    (hdealloc : HookSat (Rust.withPanics ext) spqrDeallocSym A.deallocSpec)
    (s0 s1 : State) (ptr cap : BitVec 64) (Rest : SepProp)
    (hsp0_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hpc1 : s1.pc = lsmpl.base 332 + 192#64)
    (hrun1 : s1.status = .Running)
    (hsp1 : s1.sp = s0.sp - 4240#64)
    (hx0_1 : s1.readReg64 .x0 = ptr)
    (hx1_1 : s1.readReg64 .x1 = cap)
    (hx2_1 : s1.readReg64 .x2 = 1#64)
    (hcap : cap.toNat ≠ 0)
    (htr1 : TraceCalleeSaved s1 s0) :
    SepWP (lsProg_332 (Rust.withPanics ext)) (s0.readReg64 .x30) s1
      (stackAt (s0.sp - 4240#64) statesRecvCalleeStackX ∗
        memRegion (s0.sp - 4240#64) 4144 ∗
        statesRecvSavedCells s0 ∗
        A.live ptr cap.toNat 1 ∗
        memRegion ptr cap.toNat ∗
        A.pool ∗
        Rest)
      (fun sf Pf =>
        (Pf ⊢ A.pool ∗ Rest ∗ stackAt s0.sp statesRecvStackX) ∧
        sf.sp = s0.sp ∧
        CalleeSavedPreserved s0 sf ∧
        sf.trace = s0.trace) := by
  have hsp96_align : ((s0.sp - 96#64) &&& 15#64 == 0#64) = true :=
    spAligned_sub s0.sp 96#64 hsp0_align (by decide)
  have hdealloc_ok : subroutine_ok ((blkPC_332).rebase (blkPl_332).base (Rust.withPanics ext))
      (lsρ spqrDeallocSym) A.deallocSpec :=
    spqr_hook_ok_of_mem hdealloc
  simp only [spqrDeallocSym, spqrRustDeallocSym, RustAlloc.deallocSpec, rustDeallocSpec, allocHookStack] at hdealloc_ok
  rw [lsmpl_base_332_eq] at hpc1
  dsimp only [lsProg_332]
  unfold statesRecvSavedCells
  wp_steps
  have hrest := stack_restore_statesRecv s0
  unfold statesRecvSavedCells at hrest
  refine SepWP.focus_weaken hrest (by sep_focus) ?_
  refine SepWP.focus_weaken (Entails.of_eq (stackAt_statesRecvStackX_eq_allocHook s0.sp)) (by sep_focus) ?_
  wp_call hdealloc_ok (ptr, cap.toNat, 1)
  refine SepWP.focus_weaken (Entails.of_eq (stackAt_statesRecvStackX_eq_allocHook s0.sp).symm) (by sep_focus) ?_
  refine SpqrV1.States.Recv.align_pre (Entails.of_eq (by ac_rfl)) ?_
  wp_done

theorem subroutine_ok_withMemEq_of_withLsCodeLoaded {α : Type} {prog : Program} {entry : BitVec 64}
    {pl : MultiPlacement} {spec : Spec α} {m : Memory}
    (h : subroutine_ok prog entry (withLsCodeLoaded pl spec))
    (hcl : LibsignalCodeLoaded pl m) :
    subroutine_ok prog entry (withMemEq m spec) :=
  subroutine_ok_mono h
    (fun _ _ s0 hp => by
      have ⟨hm, hpre⟩ := extract_withMemEq hp
      have hcl0 : LibsignalCodeLoaded pl s0.mem := hm ▸ hcl
      dsimp only [withLsCodeLoaded]
      rw [sepConj_assoc, sepConj_left_comm, satisfies_pure_sepConj]
      exact ⟨hcl0, hpre⟩)
    (fun _ _ _ _ hq => hq)

/-- Relocatable tail-call epilogue at `+552` (Block `332`):
    restores `sp = s0.sp` and `x19..x30`, tail-calls `drop_glue::<EkSentCt1Received>` (Block `278`),
    and returns to `s0.readReg64 .x30`. -/
theorem states_recv_tail_drop_ekSentCt1Received_552_placed [LibsignalPlacement]
    {A : RustAlloc} {F : ShaCompress} {ext : String → Option (State → State)}
    (hdrop : subroutine_ok (lsProg_332 (Rust.withPanics ext)) (lsmpl.base 278)
      (withLsCodeLoaded lsmpl (dropChunkedEkSentCt1ReceivedSpec A F)))
    (s0 s1 : State) (a : BitVec 64)
    (st : Chunked.SendEk.EkSentCt1Received spqrPolyApi (spqrAuthApi F))
    (Rest : SepProp)
    (hsp0_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hpc1 : s1.pc = lsmpl.base 332 + 552#64)
    (hrun1 : s1.status = .Running)
    (hsp1 : s1.sp = s0.sp - 4240#64)
    (hx0_1 : s1.readReg64 .x0 = a)
    (htr1 : TraceCalleeSaved s1 s0)
    (hcode : LibsignalCodeLoaded lsmpl s1.mem) :
    SepWP (lsProg_332 (Rust.withPanics ext)) (s0.readReg64 .x30) s1
      (stackAt (s0.sp - 4240#64) statesRecvCalleeStackX ∗
        memRegion (s0.sp - 4240#64) 4144 ∗
        statesRecvSavedCells s0 ∗
        chunkedEkSentCt1ReceivedAt A a st ∗
        A.pool ∗
        Rest)
      (fun sf Pf =>
        (Pf ⊢ memRegion a chunkedEkSentCt1ReceivedSize ∗ A.pool ∗ Rest ∗ stackAt s0.sp statesRecvStackX) ∧
        sf.sp = s0.sp ∧
        CalleeSavedPreserved s0 sf ∧
        sf.trace = s0.trace) := by
  have hsp96_align : ((s0.sp - 96#64) &&& 15#64 == 0#64) = true :=
    spAligned_sub s0.sp 96#64 hsp0_align (by decide)
  have hdrop_mem := subroutine_ok_withMemEq_of_withLsCodeLoaded hdrop hcode
  simp only [lsProg_332, withMemEq, dropChunkedEkSentCt1ReceivedSpec] at hdrop_mem
  rw [lsmpl_base_332_eq] at hpc1
  dsimp only [lsProg_332]
  unfold statesRecvSavedCells
  wp_steps
  have hrest := stack_restore_statesRecv s0
  unfold statesRecvSavedCells at hrest
  refine SepWP.focus_weaken hrest (by sep_focus) ?_
  refine SepWP.focus_weaken (Entails.of_eq (stackAt_statesRecvStackX_eq_dropStack32 s0.sp)) (by sep_focus) ?_
  wp_call hdrop_mem ⟨a, st⟩
  refine SepWP.focus_weaken (Entails.of_eq (stackAt_statesRecvStackX_eq_dropStack32 s0.sp).symm) (by sep_focus) ?_
  refine SpqrV1.States.Recv.align_pre (Entails.of_eq (by ac_rfl)) ?_
  wp_done

/-- Relocatable tail-call epilogue at `+1168` (Block `332`):
    restores `sp = s0.sp` and `x19..x30`, tail-calls `drop_glue::<HeaderSent>` (Block `276`),
    and returns to `s0.readReg64 .x30`. -/
theorem states_recv_tail_drop_headerSent_1168_placed [LibsignalPlacement]
    {A : RustAlloc} {F : ShaCompress} {ext : String → Option (State → State)}
    (hdrop : subroutine_ok (lsProg_332 (Rust.withPanics ext)) (lsmpl.base 276)
      (withLsCodeLoaded lsmpl (dropChunkedHeaderSentSpec A F)))
    (s0 s1 : State) (a : BitVec 64)
    (st : Chunked.SendEk.HeaderSent spqrPolyApi (spqrAuthApi F))
    (Rest : SepProp)
    (hsp0_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hpc1 : s1.pc = lsmpl.base 332 + 1168#64)
    (hrun1 : s1.status = .Running)
    (hsp1 : s1.sp = s0.sp - 4240#64)
    (hx0_1 : s1.readReg64 .x0 = a)
    (htr1 : TraceCalleeSaved s1 s0)
    (hcode : LibsignalCodeLoaded lsmpl s1.mem) :
    SepWP (lsProg_332 (Rust.withPanics ext)) (s0.readReg64 .x30) s1
      (stackAt (s0.sp - 4240#64) statesRecvCalleeStackX ∗
        memRegion (s0.sp - 4240#64) 4144 ∗
        statesRecvSavedCells s0 ∗
        chunkedHeaderSentAt A a st ∗
        A.pool ∗
        Rest)
      (fun sf Pf =>
        (Pf ⊢ memRegion a chunkedHeaderSentSize ∗ A.pool ∗ Rest ∗ stackAt s0.sp statesRecvStackX) ∧
        sf.sp = s0.sp ∧
        CalleeSavedPreserved s0 sf ∧
        sf.trace = s0.trace) := by
  have hsp96_align : ((s0.sp - 96#64) &&& 15#64 == 0#64) = true :=
    spAligned_sub s0.sp 96#64 hsp0_align (by decide)
  have hdrop_mem := subroutine_ok_withMemEq_of_withLsCodeLoaded hdrop hcode
  simp only [lsProg_332, withMemEq, dropChunkedHeaderSentSpec] at hdrop_mem
  rw [lsmpl_base_332_eq] at hpc1
  dsimp only [lsProg_332]
  unfold statesRecvSavedCells
  wp_steps
  have hrest := stack_restore_statesRecv s0
  unfold statesRecvSavedCells at hrest
  refine SepWP.focus_weaken hrest (by sep_focus) ?_
  refine SepWP.focus_weaken (Entails.of_eq (stackAt_statesRecvStackX_eq_dropStackPoly64 s0.sp)) (by sep_focus) ?_
  wp_call hdrop_mem ⟨a, st⟩
  refine SepWP.focus_weaken (Entails.of_eq (stackAt_statesRecvStackX_eq_dropStackPoly64 s0.sp).symm) (by sep_focus) ?_
  refine SpqrV1.States.Recv.align_pre (Entails.of_eq (by ac_rfl)) ?_
  wp_done

/-- Relocatable tail-call epilogue at `+1760` (Block `332`):
    restores `sp = s0.sp` and `x19..x30`, tail-calls `drop_glue::<[SortedSet<Pt>; 16]>` (Block `264`),
    and returns to `s0.readReg64 .x30`. -/
theorem states_recv_tail_drop_sortedSetPt16_1760_placed [LibsignalPlacement]
    {A : RustAlloc} {ext : String → Option (State → State)}
    (hdrop : subroutine_ok (lsProg_332 (Rust.withPanics ext)) (lsmpl.base 264)
      (withLsCodeLoaded lsmpl (dropGlueSortedSetPt16Spec A)))
    (s0 s1 : State) (arrA : BitVec 64) (vecs : List (List Pt))
    (hvecs : vecs.length = NUM_POLYS)
    (Rest : SepProp)
    (hsp0_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hpc1 : s1.pc = lsmpl.base 332 + 1760#64)
    (hrun1 : s1.status = .Running)
    (hsp1 : s1.sp = s0.sp - 4240#64)
    (hx0_1 : s1.readReg64 .x0 = arrA)
    (htr1 : TraceCalleeSaved s1 s0)
    (hcode : LibsignalCodeLoaded lsmpl s1.mem) :
    SepWP (lsProg_332 (Rust.withPanics ext)) (s0.readReg64 .x30) s1
      (stackAt (s0.sp - 4240#64) statesRecvCalleeStackX ∗
        memRegion (s0.sp - 4240#64) 4144 ∗
        statesRecvSavedCells s0 ∗
        vecPtListOf A arrA vecs ∗
        A.pool ∗
        Rest)
      (fun sf Pf =>
        (Pf ⊢ memRegion arrA polyArrayBytes ∗ A.pool ∗ Rest ∗ stackAt s0.sp statesRecvStackX) ∧
        sf.sp = s0.sp ∧
        CalleeSavedPreserved s0 sf ∧
        sf.trace = s0.trace) := by
  have hsp96_align : ((s0.sp - 96#64) &&& 15#64 == 0#64) = true :=
    spAligned_sub s0.sp 96#64 hsp0_align (by decide)
  have hdrop_mem := subroutine_ok_withMemEq_of_withLsCodeLoaded hdrop hcode
  simp only [lsProg_332, withMemEq, dropGlueSortedSetPt16Spec] at hdrop_mem
  rw [lsmpl_base_332_eq] at hpc1
  dsimp only [lsProg_332]
  unfold statesRecvSavedCells
  wp_steps
  have hrest := stack_restore_statesRecv s0
  unfold statesRecvSavedCells at hrest
  refine SepWP.focus_weaken hrest (by sep_focus) ?_
  refine SepWP.focus_weaken (Entails.of_eq (stackAt_statesRecvStackX_eq_dropGluePoly16 s0.sp)) (by sep_focus) ?_
  wp_call hdrop_mem ⟨arrA, vecs⟩
  refine SepWP.focus_weaken (Entails.of_eq (stackAt_statesRecvStackX_eq_dropGluePoly16 s0.sp).symm) (by sep_focus) ?_
  refine SpqrV1.States.Recv.align_pre (Entails.of_eq (by ac_rfl)) ?_
  wp_done

/-- Relocatable tail-call epilogue at `+10952` (Block `332`):
    restores `sp = s0.sp` and `x19..x30`, tail-calls `drop_glue::<Ct2Sampled>` (Block `274`),
    and returns to `s0.readReg64 .x30`. -/
theorem states_recv_tail_drop_ct2Sampled_10952_placed [LibsignalPlacement]
    {A : RustAlloc} {F : ShaCompress} {ext : String → Option (State → State)}
    (hdrop : subroutine_ok (lsProg_332 (Rust.withPanics ext)) (lsmpl.base 274)
      (withLsCodeLoaded lsmpl (dropChunkedCt2SampledSpec A F)))
    (s0 s1 : State) (a : BitVec 64)
    (st : Chunked.SendCt.Ct2Sampled spqrPolyApi (spqrAuthApi F))
    (Rest : SepProp)
    (hsp0_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hpc1 : s1.pc = lsmpl.base 332 + 10952#64)
    (hrun1 : s1.status = .Running)
    (hsp1 : s1.sp = s0.sp - 4240#64)
    (hx0_1 : s1.readReg64 .x0 = a)
    (htr1 : TraceCalleeSaved s1 s0)
    (hcode : LibsignalCodeLoaded lsmpl s1.mem) :
    SepWP (lsProg_332 (Rust.withPanics ext)) (s0.readReg64 .x30) s1
      (stackAt (s0.sp - 4240#64) statesRecvCalleeStackX ∗
        memRegion (s0.sp - 4240#64) 4144 ∗
        statesRecvSavedCells s0 ∗
        chunkedCt2SampledAt A a st ∗
        A.pool ∗
        Rest)
      (fun sf Pf =>
        (Pf ⊢ memRegion a chunkedCt2SampledSize ∗ A.pool ∗ Rest ∗ stackAt s0.sp statesRecvStackX) ∧
        sf.sp = s0.sp ∧
        CalleeSavedPreserved s0 sf ∧
        sf.trace = s0.trace) := by
  have hsp96_align : ((s0.sp - 96#64) &&& 15#64 == 0#64) = true :=
    spAligned_sub s0.sp 96#64 hsp0_align (by decide)
  have hdrop_mem := subroutine_ok_withMemEq_of_withLsCodeLoaded hdrop hcode
  simp only [lsProg_332, withMemEq, dropChunkedCt2SampledSpec] at hdrop_mem
  rw [lsmpl_base_332_eq] at hpc1
  dsimp only [lsProg_332]
  unfold statesRecvSavedCells
  wp_steps
  have hrest := stack_restore_statesRecv s0
  unfold statesRecvSavedCells at hrest
  refine SepWP.focus_weaken hrest (by sep_focus) ?_
  refine SepWP.focus_weaken (Entails.of_eq (stackAt_statesRecvStackX_eq_dropStack32 s0.sp)) (by sep_focus) ?_
  wp_call hdrop_mem ⟨a, st⟩
  refine SepWP.focus_weaken (Entails.of_eq (stackAt_statesRecvStackX_eq_dropStack32 s0.sp).symm) (by sep_focus) ?_
  refine SpqrV1.States.Recv.align_pre (Entails.of_eq (by ac_rfl)) ?_
  wp_done

/-! ## Relocatable Jump-Table Dispatch (`+36 -> +statesRecvArmOffset tag`) -/

theorem statesRecvJumpTablePlacedAt_eq [LibsignalPlacement] :
    statesRecvJumpTablePlacedAt = statesRecvJumpTablePlacedExpanded := by
  unfold statesRecvJumpTablePlacedAt statesRecvJumpTableBytes statesRecvJumpTablePlacedExpanded
  simp only [pointsToBytesRO_cons, pointsToBytesRO_nil, sepConj_emp, sepConj_assoc, arm64_norm]

set_option maxHeartbeats 1200000 in
/-- Relocatable jump-table dispatch (`+36 -> +statesRecvArmOffset tag` in Block `332`). -/
theorem states_recv_dispatch_placed [LibsignalPlacement]
    {ext : String → Option (State → State)}
    (s1 : State) (fsp st_ptr tag : BitVec 64) (Rest : SepProp)
    (htag : ValidStatesTag tag)
    (hpc1 : s1.pc = lsmpl.base 332 + 36#64)
    (hrun1 : s1.status = .Running)
    (hsp1 : s1.sp = fsp)
    (hx1_1 : s1.readReg64 .x1 = st_ptr) :
    SepWP (lsProg_332 (Rust.withPanics ext))
      (lsmpl.base 332 + statesRecvArmOffset tag)
      s1
      ((st_ptr ↦₆₄ tag) ∗ statesRecvRoPlacedAt ∗ Rest)
      (fun s2 P2 =>
        (P2 ⊢ (st_ptr ↦₆₄ tag) ∗ statesRecvRoPlacedAt ∗ Rest) ∧
        s2.sp = fsp ∧
        s2.readReg64 .x0 = s1.readReg64 .x0 ∧
        s2.readReg64 .x1 = st_ptr ∧
        s2.readReg64 .x2 = s1.readReg64 .x2 ∧
        s2.readReg64 .x3 = s1.readReg64 .x3 ∧
        s2.readReg64 .x8 = statesRecvJumpIdx tag ∧
        s2.readReg64 .x12 = tag ∧
        s2.readReg64 .x19 = s1.readReg64 .x0 ∧
        s2.readReg64 .x21 = fsp + 3856#64 ∧
        s2.readReg64 .x24 = s1.readReg64 .x2 ∧
        s2.readReg64 .x28 = fsp + 3272#64 ∧
        s2.readReg64 .x29 = s1.readReg64 .x29 ∧
        TraceCalleeSaved s2 s1) := by
  subst hsp1 hx1_1
  rw [lsmpl_base_332_eq] at hpc1 ⊢
  dsimp only [lsProg_332, statesRecvRoPlacedAt]
  rw [statesRecvJumpTablePlacedAt_eq]
  dsimp only [statesRecvJumpTablePlacedExpanded, statesRecvJumpTableSym, BitVec.ofNat_eq_ofNat] at hpc1 ⊢
  rcases htag with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
  · dsimp [statesRecvArmOffset, statesRecvJumpIdx]
    wp_steps
    wp_done

/-! ## Relocatable Shared `Ok(V1Recv)` Store Epilogue (`+18940 / +18996 -> +19324`) -/

theorem epilogue_step_18940_18996_placed [LibsignalPlacement]
    {ext : String → Option (State → State)}
    (s : State) (fsp : BitVec 64)
    (w8 w56 w64 w96 w128 w136 w152 w160 w168 w176 w184 w192 w216 u368 : BitVec 64)
    (Frame : SepProp)
    (hfsp_align : (fsp &&& 15#64 == 0#64) = true)
    (hpc : s.pc = lsmpl.base 332 + 18940#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = fsp) :
    SepWP (lsProg_332 (Rust.withPanics ext))
      (lsmpl.base 332 + 18996#64)
      s
      (((fsp + 8#64) ↦₆₄ w8) ∗
       ((fsp + 56#64) ↦₆₄ w56) ∗ ((fsp + 64#64) ↦₆₄ w64) ∗
       ((fsp + 96#64) ↦₆₄ w96) ∗
       ((fsp + 128#64) ↦₆₄ w128) ∗ ((fsp + 136#64) ↦₆₄ w136) ∗
       ((fsp + 152#64) ↦₆₄ w152) ∗ ((fsp + 160#64) ↦₆₄ w160) ∗
       ((fsp + 168#64) ↦₆₄ w168) ∗ ((fsp + 176#64) ↦₆₄ w176) ∗
       ((fsp + 184#64) ↦₆₄ w184) ∗ ((fsp + 192#64) ↦₆₄ w192) ∗
       ((fsp + 216#64) ↦₆₄ w216) ∗ ((fsp + 368#64) ↦₆₄ u368) ∗
       Frame)
      (fun sm Pm =>
        (Pm ⊢
          ((fsp + 8#64) ↦₆₄ w8) ∗
          ((fsp + 56#64) ↦₆₄ w56) ∗ ((fsp + 64#64) ↦₆₄ w64) ∗
          ((fsp + 96#64) ↦₆₄ w96) ∗
          ((fsp + 128#64) ↦₆₄ w128) ∗ ((fsp + 136#64) ↦₆₄ w136) ∗
          ((fsp + 152#64) ↦₆₄ w152) ∗ ((fsp + 160#64) ↦₆₄ w160) ∗
          ((fsp + 168#64) ↦₆₄ w168) ∗ ((fsp + 176#64) ↦₆₄ w176) ∗
          ((fsp + 184#64) ↦₆₄ w184) ∗ ((fsp + 192#64) ↦₆₄ w192) ∗
          ((fsp + 216#64) ↦₆₄ w216) ∗ ((fsp + 368#64) ↦₆₄ s.readReg64 .x0) ∗
          Frame) ∧
        sm.sp = fsp ∧
        sm.readReg64 .x0 = s.readReg64 .x11 ∧
        sm.readReg64 .x1 = w136 ∧
        sm.readReg64 .x2 = s.readReg64 .x2 ∧
        sm.readReg64 .x3 = s.readReg64 .x3 ∧
        sm.readReg64 .x4 = w184 ∧
        sm.readReg64 .x5 = w216 ∧
        sm.readReg64 .x6 = w56 ∧
        sm.readReg64 .x7 = w64 ∧
        sm.readReg64 .x8 = s.readReg64 .x14 ∧
        sm.readReg64 .x9 = w192 ∧
        sm.readReg64 .x10 = s.readReg64 .x10 ∧
        sm.readReg64 .x11 = s.readReg64 .x20 ∧
        sm.readReg64 .x12 = s.readReg64 .x12 ∧
        sm.readReg64 .x13 = w8 ∧
        sm.readReg64 .x14 = s.readReg64 .x17 ∧
        sm.readReg64 .x15 = s.readReg64 .x15 ∧
        sm.readReg64 .x16 = w96 ∧
        sm.readReg64 .x17 = s.readReg64 .x27 ∧
        sm.readReg64 .x19 = s.readReg64 .x19 ∧
        sm.readReg64 .x20 = s.readReg64 .x20 ∧
        sm.readReg64 .x21 = s.readReg64 .x21 ∧
        sm.readReg64 .x22 = w176 ∧
        sm.readReg64 .x23 = w152 ∧
        sm.readReg64 .x24 = s.readReg64 .x24 ∧
        sm.readReg64 .x25 = s.readReg64 .x25 ∧
        sm.readReg64 .x26 = w168 ∧
        sm.readReg64 .x27 = w160 ∧
        sm.readReg64 .x28 = w128 ∧
        sm.readReg64 .x29 = s.readReg64 .x29 ∧
        sm.readReg64 .x30 = s.readReg64 .x30 ∧
        TraceCalleeSaved sm s) := by
  subst hsp
  rw [lsmpl_base_332_eq] at hpc ⊢
  dsimp only [lsProg_332]
  wp_steps
  wp_done

set_option maxHeartbeats 1200000 in
theorem epilogue_step_18996_19128_placed [LibsignalPlacement]
    {ext : String → Option (State → State)}
    (s : State) (fsp out : BitVec 64)
    (u0 u8 u16 u24 u32 u40 u48 u56 u64 u72 u80 u88 u96 u104 u112 : BitVec 64)
    (u264 u272 u280 u288 u296 u304 u312 u320 u328 u336 u344 u352 u392 u400 u424 u432 : BitVec 64)
    (w224 w288 w296 w336 w352 w368 w376 w384 w408 w432 w456 w496 w504 : BitVec 64)
    (q960 : BitVec 128)
    (Frame : SepProp)
    (hfsp_align : (fsp &&& 15#64 == 0#64) = true)
    (hpc : s.pc = lsmpl.base 332 + 18996#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = fsp)
    (hx19 : s.readReg64 .x19 = out) :
    SepWP (lsProg_332 (Rust.withPanics ext))
      (lsmpl.base 332 + 19128#64)
      s
      (epilogueRecvOutPartA out u0 u8 u16 u24 u32 u40 u48 u56 u64 u72 u80 u88 u96 u104 u112
         u264 u272 u280 u288 u296 u304 u312 u320 u328 u336 u344 u352 u392 u400 u424 u432 ∗
       epilogueRecvStackPartA fsp w224 w288 w296 w336 w352 w368 w376 w384 w408 w432 w456 w496 w504 q960 ∗
       Frame)
      (fun sm Pm =>
        (Pm ⊢
          epilogueRecvOutPartA out
            w224 (s.readReg64 .x1) (s.readReg64 .x8) w496
            w456 w376 w368 w504
            w288 w432 w408 w352
            w384 w336 w296
            (s.readReg64 .x25) (s.readReg64 .x12) (s.readReg64 .x11) (s.readReg64 .x10)
            (s.readReg64 .x15) (s.readReg64 .x28) (s.readReg64 .x7) (s.readReg64 .x0)
            (s.readReg64 .x6) (s.readReg64 .x30) (s.readReg64 .x21) (s.readReg64 .x9)
            (s.readReg64 .x5) (s.readReg64 .x4) (s.readReg64 .x13) (s.readReg64 .x14) ∗
          epilogueRecvStackPartA fsp w224 w288 w296 w336 w352 w368 w376 w384 w408 w432 w456 w496 w504 q960 ∗
          Frame) ∧
        sm.sp = fsp ∧
        sm.readReg64 .x0 = out + 512#64 ∧
        sm.readReg64 .x1 = fsp + 576#64 ∧
        sm.readReg64 .x2 = s.readReg64 .x2 ∧
        sm.readReg64 .x3 = s.readReg64 .x3 ∧
        sm.readReg64 .x16 = s.readReg64 .x16 ∧
        sm.readReg64 .x17 = s.readReg64 .x17 ∧
        sm.readReg64 .x19 = out ∧
        sm.readReg64 .x20 = s.readReg64 .x20 ∧
        sm.readReg64 .x22 = s.readReg64 .x22 ∧
        sm.readReg64 .x23 = s.readReg64 .x23 ∧
        sm.readReg64 .x24 = s.readReg64 .x24 ∧
        sm.readReg64 .x26 = s.readReg64 .x26 ∧
        sm.readReg64 .x27 = s.readReg64 .x27 ∧
        sm.readReg64 .x29 = s.readReg64 .x29 ∧
        sm.readVReg128 0#5 = q960 ∧
        TraceCalleeSaved sm s) := by
  subst hsp hx19
  rw [lsmpl_base_332_eq] at hpc ⊢
  dsimp only [lsProg_332]
  wp_simp_pre [epilogueRecvOutPartA, epilogueRecvStackPartA, pointsTo128, sepConj_assoc]
  wp_steps
  simp only [epilogueRecvOutPartA, epilogueRecvStackPartA, pointsTo128, sepConj_assoc]
  wp_done

set_option maxHeartbeats 1600000 in
theorem epilogue_step_19128_19280_placed [LibsignalPlacement]
    {ext : String → Option (State → State)}
    (s : State) (fsp out : BitVec 64)
    (u120 u128 u136 u144 u152 u160 u168 u176 u184 u192 u200 u208 u216 u224 u232 u240 u248 u256 : BitVec 64)
    (u360 u368 u376 u384 u408 u416 u440 u448 u456 u464 u472 u480 : BitVec 64)
    (uq488 : BitVec 128) (u504 : BitVec 64)
    (w248 w256 w264 w272 w280 w304 w312 w320 w328 w344 w360 w392 w400 w416 w424 w440 w448 w464 w472 w480 w488 : BitVec 64)
    (Frame : SepProp)
    (hfsp_align : (fsp &&& 15#64 == 0#64) = true)
    (hpc : s.pc = lsmpl.base 332 + 19128#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = fsp)
    (hx0 : s.readReg64 .x0 = out + 512#64)
    (hx1 : s.readReg64 .x1 = fsp + 576#64)
    (hx19 : s.readReg64 .x19 = out) :
    SepWP (lsProg_332 (Rust.withPanics ext))
      (lsmpl.base 332 + 19280#64)
      s
      (epilogueRecvOutPartB out u120 u128 u136 u144 u152 u160 u168 u176 u184 u192 u200 u208 u216 u224 u232 u240 u248 u256
         u360 u368 u376 u384 u408 u416 u440 u448 u456 u464 u472 u480 uq488 u504 ∗
       epilogueRecvStackPartB fsp w248 w256 w264 w272 w280 w304 w312 w320 w328 w344 w360 w392 w400 w416 w424 w440 w448 w464 w472 w480 w488 ∗
       Frame)
      (fun sm Pm =>
        (Pm ⊢
          epilogueRecvOutPartB out
            w424 (s.readReg64 .x23) (s.readReg64 .x27) w440
            w264 w344 w392 w272
            w360 w400 w464 w304
            w328 w280 w320 (s.readReg64 .x3)
            w312 (s.readReg64 .x24)
            w416 (s.readReg64 .x17) w472 (s.readReg64 .x26)
            w448 (s.readReg64 .x22)
            w480 (s.readReg64 .x16) w488 (s.readReg64 .x2)
            w248 (s.readReg64 .x20)
            (s.readVReg128 0#5) w256 ∗
          epilogueRecvStackPartB fsp w248 w256 w264 w272 w280 w304 w312 w320 w328 w344 w360 w392 w400 w416 w424 w440 w448 w464 w472 w480 w488 ∗
          Frame) ∧
        sm.sp = fsp ∧
        sm.readReg64 .x0 = out + 512#64 ∧
        sm.readReg64 .x1 = fsp + 576#64 ∧
        sm.readReg64 .x2 = 376#64 ∧
        sm.readReg64 .x19 = out ∧
        sm.readReg64 .x20 = s.readReg64 .x20 ∧
        sm.readReg64 .x29 = s.readReg64 .x29 ∧
        TraceCalleeSaved sm s) := by
  subst hsp hx19
  rw [lsmpl_base_332_eq] at hpc ⊢
  dsimp only [lsProg_332]
  wp_simp_pre [epilogueRecvOutPartB, epilogueRecvStackPartB, pointsTo128, sepConj_assoc]
  wp_steps
  simp only [epilogueRecvOutPartB, epilogueRecvStackPartB, pointsTo128, sepConj_assoc]
  wp_done

theorem epilogue_step_19280_19324_placed [LibsignalPlacement]
    {ext : String → Option (State → State)}
    (hmemcpy_sat : HookSat (Rust.withPanics ext) spqrMemcpySym sessionMemcpySpec)
    (s : State) (fsp out : BitVec 64)
    (bs576 : List (BitVec 8)) (hbs576 : bs576.length = 376)
    (uq888 uq904 uq944 q512 q528 q544 : BitVec 128)
    (u920 u928 u936 w232 w560 : BitVec 64)
    (Frame : SepProp)
    (hfsp_align : (fsp &&& 15#64 == 0#64) = true)
    (hpc : s.pc = lsmpl.base 332 + 19280#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = fsp)
    (hx0 : s.readReg64 .x0 = out + 512#64)
    (hx1 : s.readReg64 .x1 = fsp + 576#64)
    (hx2 : s.readReg64 .x2 = 376#64)
    (hx19 : s.readReg64 .x19 = out) :
    SepWP (lsProg_332 (Rust.withPanics ext))
      (lsmpl.base 332 + 19324#64)
      s
      (stackAt fsp allocHookStack ∗
       memRegion (out + 512#64) 376 ∗
       ((out + 888#64) ↦₁₂₈ uq888) ∗ ((out + 904#64) ↦₁₂₈ uq904) ∗
       ((out + 920#64) ↦₆₄ u920) ∗ ((out + 928#64) ↦₆₄ u928) ∗
       ((out + 936#64) ↦₆₄ u936) ∗ ((out + 944#64) ↦₁₂₈ uq944) ∗
       ((fsp + 232#64) ↦₆₄ w232) ∗
       ((fsp + 512#64) ↦₁₂₈ q512) ∗ ((fsp + 528#64) ↦₁₂₈ q528) ∗
       ((fsp + 544#64) ↦₁₂₈ q544) ∗ ((fsp + 560#64) ↦₆₄ w560) ∗
       ((fsp + 576#64) ↦ₛ bs576) ∗
       Frame)
      (fun sm Pm =>
        (Pm ⊢
          stackAt fsp allocHookStack ∗
          ((out + 512#64) ↦ₛ bs576) ∗
          ((out + 888#64) ↦₁₂₈ q528) ∗ ((out + 904#64) ↦₁₂₈ q544) ∗
          ((out + 920#64) ↦₆₄ w560) ∗ ((out + 928#64) ↦₆₄ w232) ∗
          ((out + 936#64) ↦₆₄ s.readReg64 .x20) ∗ ((out + 944#64) ↦₁₂₈ q512) ∗
          ((fsp + 232#64) ↦₆₄ w232) ∗
          ((fsp + 512#64) ↦₁₂₈ q512) ∗ ((fsp + 528#64) ↦₁₂₈ q528) ∗
          ((fsp + 544#64) ↦₁₂₈ q544) ∗ ((fsp + 560#64) ↦₆₄ w560) ∗
          ((fsp + 576#64) ↦ₛ bs576) ∗
          Frame) ∧
        sm.sp = fsp ∧
        TraceCalleeSaved sm s) := by
  subst hsp hx19
  have hmemcpy : subroutine_ok ((blkPC_332).rebase (blkPl_332).base (Rust.withPanics ext))
      (lsρ "memcpy") sessionMemcpySpec :=
    spqr_hook_ok_of_mem hmemcpy_sat
  simp only [sessionMemcpySpec, allocHookStack] at hmemcpy ⊢
  rw [← hbs576]
  rw [lsmpl_base_332_eq] at hpc ⊢
  dsimp only [lsProg_332]
  wp_simp_pre [pointsTo128, sepConj_assoc]
  wp_steps
  wp_call hmemcpy (s.readReg64 .x19 + 512#64, s.sp + 576#64, bs576)
  wp_steps
  simp only [pointsTo128, sepConj_assoc]
  wp_done

end LibsignalBinary.Proofs.SpqrV1.States.Recv

namespace CryptoVerification.SpqrV1.States.Recv

export LibsignalBinary.Proofs.SpqrV1.States.Recv (
  lsmpl_base_332_eq
  states_recv_prologue_placed
  states_recv_epilogue_19324_placed
  states_recv_tail_dealloc_192_placed
  subroutine_ok_withMemEq_of_withLsCodeLoaded
  states_recv_tail_drop_ekSentCt1Received_552_placed
  states_recv_tail_drop_headerSent_1168_placed
  states_recv_tail_drop_sortedSetPt16_1760_placed
  states_recv_tail_drop_ct2Sampled_10952_placed
  statesRecvJumpTablePlacedAt_eq
  states_recv_dispatch_placed
  epilogue_step_18940_18996_placed
  epilogue_step_18996_19128_placed
  epilogue_step_19128_19280_placed
  epilogue_step_19280_19324_placed
)

end CryptoVerification.SpqrV1.States.Recv
