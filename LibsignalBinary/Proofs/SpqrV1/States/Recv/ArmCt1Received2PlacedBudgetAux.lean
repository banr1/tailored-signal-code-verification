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
public import LibsignalBinary.Proofs.Placed.ElfLsRetAddr
public import LibsignalBinary.Proofs.SpqrV1.States.Leaves.DefsPlacedBudget
public import LibsignalBinary.Proofs.SpqrV1.States.Recv.ArmCt1Received1PlacedBudget
public import LibsignalBinary.Proofs.SpqrV1.States.Recv.DefsPlacedBudget
public import LibsignalBinary.Proofs.SpqrV1.States.Recv.DispatchPlacedBudget
public import LibsignalBinary.Proofs.SpqrV1.States.Recv.SendEkCommon
import LibsignalBinary.Proofs.SpqrV1.Kdf.HkdfToSliceExtract
import LibsignalBinary.Proofs.SpqrV1.Poly.EncoderIntoPb.Defs
import LibsignalBinary.Proofs.SpqrV1.States.FromPb.Defs
import LibsignalBinary.Proofs.SpqrV1.States.Leaves.SendChunk1
import LibsignalBinary.Proofs.SpqrV1.States.Recv.ArmCt1Received1
import LibsignalBinary.Proofs.SpqrV1.States.Recv.ArmCt1Received2
import LibsignalBinary.Proofs.SpqrV1.States.Recv.CodeSymFetch0Placed
import LibsignalBinary.Proofs.SpqrV1.States.Recv.CodeSymFetch1Placed
import LibsignalBinary.Proofs.SpqrV1.States.Recv.CodeSymFetch2Placed
import LibsignalBinary.Proofs.SpqrV1.States.Recv.CodeSymFetch5Placed
import LibsignalBinary.Proofs.SpqrV1.States.Recv.DispatchPlaced
import LibsignalBinary.Proofs.SpqrV1.States.Recv.SendEkCommonPlaced
import LibsignalBinary.Proofs.TripleRatchet.Getters.GettersCodeSym
import ProofLib.SepLogic.WPp
meta import LibsignalBinary.Proofs.Common.SharedHelpers -- shake: keep
meta import LibsignalBinary.Proofs.Placed.BudgetVmSteps -- shake: keep

/-!
# `<States>::recv` (Block `332`) — `.ct1Received` Arm, Part 2 Aux (Budget-Threaded)

Allocator-event envelopes (`Ct1ReceivedArmPreEnv` / `Ct1ReceivedArmPostEnv`), `StatesRecvEnv`
subsumption, `VmPreserved`/pool-threaded helper blocks, and the `<Ct1Received>::recv_ct2_chunk`
(`.ct2`) path (`ct1Received_arm_eq_ct2_placed`).
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 400000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

namespace LibsignalBinary.Proofs.SpqrV1.States.Recv.ArmCt1Received2PlacedBudgetAux

open Arm64 ProofLib ProofLib.ProgramReflection
open LibsignalBinary.Proofs.Placed.ElfLsRetAddr (LsRetAddr624)
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
open CryptoVerification.SpqrV1.Poly
open CryptoVerification.SpqrV1.Poly.AddChunk
open CryptoVerification.SpqrV1.Drop
open CryptoVerification.SpqrV1.Unchunked
open CryptoVerification.SpqrV1.States
open CryptoVerification.SpqrV1.States.Leaves
open CryptoVerification.SpqrV1.States.RecvCt2Chunk
open CryptoVerification.SpqrV1.States.Recv
open CryptoVerification.SpqrV1.Top
open CryptoVerification.SpqrV1.Top.MessageSerialize
open CryptoVerification.SpqrV1.GF.Mul2U16
open CryptoVerification.SpqrV1.GF.UnacceleratedMul
open CryptoVerification.CodeLayout
open LibsignalBinary.Proofs.SpqrV1.States.Recv
open LibsignalBinary.Heap (
  AllocCallPreserved AllocCostModel AllocEvent BudgetLimits FitsEnv FreeOnlyEvs
  RustCliAllocBudget SeqEnv VmPreserved rustAllocEvents rustCliDeallocBudgetSpec
)
open LibsignalBinary.Heap.SpecBudget (withVmPreserved)
open LibsignalBinary.Proofs.SpqrV1.Poly.AddChunk.DefsBudget (
  AddChunkSlotEnv AddChunkSlotsEnv addChunkSlotsEnv_nil growOnePtEvents
)
open LibsignalBinary.Proofs.SpqrV1.States.Leaves.Batch2DefsPlacedBudget (
  Ct1ReceivedRecvCt2ChunkPostEnv Ct1ReceivedRecvCt2ChunkPreEnv
  ct1ReceivedRecvCt2ChunkSpec ct1ReceivedRecvCt2ChunkSpecOfPrePostEnv
)
open LibsignalBinary.Proofs.SpqrV1.States.Recv.ArmCt1Received1PlacedBudget (
  ct1Received_arm_gt_placed
)
open LibsignalBinary.Proofs.SpqrV1.States.Recv.ArmNoHeaderReceivedStepsPlacedBudgetAux (
  seq_vm_clean seq_vm_cont step_adrp_vm
)
open LibsignalBinary.Proofs.SpqrV1.States.Recv.DefsPlacedBudget (
  StatesRecvCalleeEnvs StatesRecvEnv sepWPp_of_statesRecv_exit_placed_ofPrePostEnv
)
open LibsignalBinary.Proofs.SpqrV1.States.Recv.DispatchPlacedBudget (
  states_recv_dispatch_pool_placed states_recv_prologue_pool_placed
  states_recv_writeback_59e88_sat_placed
)
open LibsignalBinary.Proofs.SpqrV1.Top.InitInner.DefsPlacedBudget (SpqrBoundedEvs)

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
  Recv.sp_sub_96_add_16 Recv.sp_sub_96_add_32 Recv.sp_sub_96_add_48 Recv.sp_sub_96_add_64 Recv.sp_sub_96_add_80
  sp_sub_96_sub_4096 sp_sub_4192_sub_48 sp_sub_4240_add_48 sp_sub_4240_add_4096 sp_sub_144_add_48
  RustCliAllocBudget.pool_setPC RustCliAllocBudget.pool_advancePC
  RustCliAllocBudget.pool_setPState RustCliAllocBudget.pool_writeReg64
  RustCliAllocBudget.pool_writeReg32 RustCliAllocBudget.pool_writeReg

/-! ## 1. Arm Envelopes & `StatesRecvEnv` Subsumption -/

/-- Each empty `SortedSetPt.new` slot in `add_chunk` emits either `[]` or `[.alloc 16]`,
    bounded by `SpqrBoundedEvs 1 16`. -/
theorem addChunkSlotEnv_new_bounded {evs : List AllocEvent}
    (h : AddChunkSlotEnv SortedSetPt.new evs) :
    SpqrBoundedEvs 1 16 evs := by
  rcases h with rfl | rfl
  · exact SpqrBoundedEvs.nil 1 16
  · have hgrow : growOnePtEvents SortedSetPt.new.vec.length = [.alloc 16] := by
      simp [SortedSetPt.new, growOnePtEvents, rustAllocEvents]
    rw [hgrow]
    refine ⟨Nat.le_refl 1, fun ev hev => ?_⟩
    simp only [List.mem_singleton] at hev
    subst hev
    exact ⟨by unfold AllocEvent.withinMaxAlloc; decide, Nat.le_refl 16,
      (fun _ _ h => nomatch h), (fun _ _ _ h => nomatch h)⟩

/-- Structural bound on `AddChunkSlotsEnv (List.replicate n SortedSetPt.new)` (`≤ n` allocations
    of `16` bytes each). -/
theorem addChunkSlotsEnv_replicate_new_bounded :
    ∀ (n : Nat) (evs : List AllocEvent),
      AddChunkSlotsEnv (List.replicate n SortedSetPt.new) evs →
      SpqrBoundedEvs n 16 evs
  | 0, evs, h => by
    dsimp only [List.replicate, AddChunkSlotsEnv] at h
    subst h
    exact SpqrBoundedEvs.nil 0 16
  | n + 1, evs, h => by
    rw [List.replicate_succ] at h
    dsimp only [AddChunkSlotsEnv] at h
    rcases h with h1 | ⟨evs₁, evs₂, rfl, h1, h2⟩
    · exact SpqrBoundedEvs.mono (by omega) (Nat.le_refl 16) (addChunkSlotEnv_new_bounded h1)
    · exact SpqrBoundedEvs.mono (by omega) (by omega)
        (SpqrBoundedEvs.append (addChunkSlotEnv_new_bounded h1)
          (addChunkSlotsEnv_replicate_new_bounded n evs₂ h2))

theorem ct1ReceivedRecvCt2ChunkPreEnv_bounded {F : ShaCompress}
    {y : Ct1ReceivedRecvCt2ChunkGhost F} {evs : List AllocEvent}
    (h : Ct1ReceivedRecvCt2ChunkPreEnv y evs) :
    SpqrBoundedEvs 16 16 evs :=
  addChunkSlotsEnv_replicate_new_bounded 16 evs h

theorem seq_addChunk16_freeOnly_bounded {evs : List AllocEvent}
    (h : SeqEnv (AddChunkSlotsEnv (List.replicate 16 SortedSetPt.new)) FreeOnlyEvs evs) :
    SpqrBoundedEvs 16 16 evs := by
  rcases h with h1 | ⟨evs₁, evs₂, rfl, h1, h2⟩
  · exact addChunkSlotsEnv_replicate_new_bounded 16 evs h1
  · exact SpqrBoundedEvs.mono (by omega) (by omega)
      (SpqrBoundedEvs.append (addChunkSlotsEnv_replicate_new_bounded 16 evs₁ h1)
        (SpqrBoundedEvs.of_freeOnly h2))

theorem ct1ReceivedRecvCt2ChunkPostEnv_bounded {F : ShaCompress}
    {y : Ct1ReceivedRecvCt2ChunkGhost F} {evs : List AllocEvent}
    (h : Ct1ReceivedRecvCt2ChunkPostEnv y evs) :
    SpqrBoundedEvs 16 16 evs :=
  seq_addChunk16_freeOnly_bounded h

theorem freeOnlyEvs_sub_statesRecvEnv {F : ShaCompress}
    (x : StatesRecvGhost F) {evs : List AllocEvent} (h : FreeOnlyEvs evs) :
    StatesRecvEnv x evs := by
  unfold DefsPlacedBudget.StatesRecvEnv Top.Recv.DefsPlacedBudget.StatesRecvEnv
  exact SpqrBoundedEvs.mono (by omega) (by omega) (SpqrBoundedEvs.of_freeOnly h)

theorem ct1ReceivedRecvCt2ChunkPreEnv_sub_statesRecvEnv {F : ShaCompress}
    (x : StatesRecvGhost F) {y : Ct1ReceivedRecvCt2ChunkGhost F} {evs : List AllocEvent}
    (h : Ct1ReceivedRecvCt2ChunkPreEnv y evs) :
    StatesRecvEnv x evs := by
  unfold DefsPlacedBudget.StatesRecvEnv Top.Recv.DefsPlacedBudget.StatesRecvEnv
  exact SpqrBoundedEvs.mono (by omega) (by omega) (ct1ReceivedRecvCt2ChunkPreEnv_bounded h)

theorem ct1ReceivedRecvCt2ChunkPostEnv_sub_statesRecvEnv {F : ShaCompress}
    (x : StatesRecvGhost F) {y : Ct1ReceivedRecvCt2ChunkGhost F} {evs : List AllocEvent}
    (h : Ct1ReceivedRecvCt2ChunkPostEnv y evs) :
    StatesRecvEnv x evs := by
  unfold DefsPlacedBudget.StatesRecvEnv Top.Recv.DefsPlacedBudget.StatesRecvEnv
  exact SpqrBoundedEvs.mono (by omega) (by omega) (ct1ReceivedRecvCt2ChunkPostEnv_bounded h)

/-- Allocation-phase prefix envelope for the `.ct1Received` arm of `<States>::recv`. -/
def Ct1ReceivedArmPreEnv {F : ShaCompress}
    (st : Chunked.SendEk.Ct1Received spqrPolyApi (spqrAuthApi F))
    (msg : Message spqrPolyApi) (evs : List AllocEvent) : Prop :=
  if msg.epoch > st.uc.epoch then
    evs = []
  else if msg.epoch < st.uc.epoch then
    evs = []
  else
    match msg.payload with
    | .ct2 _ => AddChunkSlotsEnv (List.replicate 16 SortedSetPt.new) evs
    | _ => evs = []

/-- Postcondition allocation envelope for the `.ct1Received` arm of `<States>::recv`. -/
def Ct1ReceivedArmPostEnv {F : ShaCompress}
    (st : Chunked.SendEk.Ct1Received spqrPolyApi (spqrAuthApi F))
    (msg : Message spqrPolyApi) (evs : List AllocEvent) : Prop :=
  if msg.epoch > st.uc.epoch then
    FreeOnlyEvs evs
  else if msg.epoch < st.uc.epoch then
    evs = []
  else
    match msg.payload with
    | .ct2 _ => SeqEnv (AddChunkSlotsEnv (List.replicate 16 SortedSetPt.new)) FreeOnlyEvs evs
    | _ => evs = []

theorem ct1ReceivedArmPreEnv_nil {F : ShaCompress}
    (st : Chunked.SendEk.Ct1Received spqrPolyApi (spqrAuthApi F))
    (msg : Message spqrPolyApi) :
    Ct1ReceivedArmPreEnv st msg [] := by
  unfold Ct1ReceivedArmPreEnv
  split
  · rfl
  · split
    · rfl
    · cases msg.payload <;>
        first | rfl | exact addChunkSlotsEnv_nil (List.replicate 16 SortedSetPt.new)

theorem ct1ReceivedArmPostEnv_nil {F : ShaCompress}
    (st : Chunked.SendEk.Ct1Received spqrPolyApi (spqrAuthApi F))
    (msg : Message spqrPolyApi) :
    Ct1ReceivedArmPostEnv st msg [] := by
  unfold Ct1ReceivedArmPostEnv
  split
  · exact FreeOnlyEvs.nil
  · split
    · rfl
    · cases msg.payload <;>
        first | rfl | exact Or.inl (addChunkSlotsEnv_nil (List.replicate 16 SortedSetPt.new))

theorem ct1ReceivedArmPreEnv_nonempty {F : ShaCompress}
    (st : Chunked.SendEk.Ct1Received spqrPolyApi (spqrAuthApi F))
    (msg : Message spqrPolyApi) :
    ∃ evs, Ct1ReceivedArmPreEnv st msg evs :=
  ⟨[], ct1ReceivedArmPreEnv_nil st msg⟩

theorem ct1ReceivedArmPostEnv_nonempty {F : ShaCompress}
    (st : Chunked.SendEk.Ct1Received spqrPolyApi (spqrAuthApi F))
    (msg : Message spqrPolyApi) :
    ∃ evs, Ct1ReceivedArmPostEnv st msg evs :=
  ⟨[], ct1ReceivedArmPostEnv_nil st msg⟩

theorem ct1ReceivedArmPreEnv_sub_statesRecvEnv {F : ShaCompress}
    (x : StatesRecvGhost F)
    (st : Chunked.SendEk.Ct1Received spqrPolyApi (spqrAuthApi F))
    (msg : Message spqrPolyApi) {evs : List AllocEvent}
    (h : Ct1ReceivedArmPreEnv st msg evs) :
    StatesRecvEnv x evs := by
  unfold Ct1ReceivedArmPreEnv at h
  unfold DefsPlacedBudget.StatesRecvEnv Top.Recv.DefsPlacedBudget.StatesRecvEnv
  split at h
  · subst h; exact SpqrBoundedEvs.nil _ _
  · split at h
    · subst h; exact SpqrBoundedEvs.nil _ _
    · cases hp : msg.payload <;> rw [hp] at h
      case ct2 =>
        exact SpqrBoundedEvs.mono (by omega) (by omega)
          (addChunkSlotsEnv_replicate_new_bounded 16 evs h)
      all_goals
        subst h; exact SpqrBoundedEvs.nil _ _

theorem ct1ReceivedArmPostEnv_sub_statesRecvEnv {F : ShaCompress}
    (x : StatesRecvGhost F)
    (st : Chunked.SendEk.Ct1Received spqrPolyApi (spqrAuthApi F))
    (msg : Message spqrPolyApi) {evs : List AllocEvent}
    (h : Ct1ReceivedArmPostEnv st msg evs) :
    StatesRecvEnv x evs := by
  unfold Ct1ReceivedArmPostEnv at h
  unfold DefsPlacedBudget.StatesRecvEnv Top.Recv.DefsPlacedBudget.StatesRecvEnv
  split at h
  · exact SpqrBoundedEvs.mono (by omega) (by omega) (SpqrBoundedEvs.of_freeOnly h)
  · split at h
    · subst h; exact SpqrBoundedEvs.nil _ _
    · cases hp : msg.payload <;> rw [hp] at h
      case ct2 =>
        exact SpqrBoundedEvs.mono (by omega) (by omega) (seq_addChunk16_freeOnly_bounded h)
      all_goals
        subst h; exact SpqrBoundedEvs.nil _ _

/-! ## 2. `VmPreserved` & Budget-Pool-Threaded Relocatable Helper Blocks -/

set_option maxHeartbeats 1200000 in
/-- Relocatable post-call writeback block (`+6436 -> s0.x30`, Block `332`) parameterized by
    `hmemcpy_sat : HookSat (Rust.withPanics ext) spqrMemcpySym (withVmPreserved sessionMemcpySpec)`,
    establishing `VmPreserved s sf`. -/
theorem ct1Received_post_call_56d78_sat_placed [LibsignalPlacement]
    {A : RustAlloc} {F : ShaCompress} {ext : String → Option (State → State)}
    (hmemcpy_sat : HookSat (Rust.withPanics ext) spqrMemcpySym (withVmPreserved sessionMemcpySpec))
    (s0 s : State) (outA : BitVec 64)
    (outSt : Chunked.SendEk.EkSentCt1Received spqrPolyApi (spqrAuthApi F))
    (sp : SendEkSpills) (P_rest : SepProp)
    (hpc : s.pc = lsmpl.base 332 + 6436#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = s0.sp - 4240#64)
    (hsp_align : s0.spAligned = true)
    (hx19 : s.readReg64 .x19 = outA)
    (htr : TraceCalleeSaved s s0) :
    SepWP (lsProg_332 (Rust.withPanics ext)) (s0.readReg64 .x30) s
      (P_rest ∗
        memRegion outA v1RecvSize ∗
        stackAt (s0.sp - 4240#64) statesRecvCalleeStackX ∗
        sendEkSpillsAt (s0.sp - 4240#64) sp ∗
        memRegion ((s0.sp - 4240#64) + 576#64) 376 ∗
        chunkedEkSentCt1ReceivedAt A ((s0.sp - 4240#64) + 976#64) outSt ∗
        memRegion ((s0.sp - 4240#64) + 1480#64) 376 ∗
        memRegion ((s0.sp - 4240#64) + 1856#64) 880 ∗
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
  have hwb := @states_recv_writeback_59e88_sat_placed _ ext hmemcpy_sat
    (F_tail := fun a => memRegion a 376) (Relocatable.of_memRegion 376) s0
  rw [lsmpl_base_332_eq] at hpc hwb
  dsimp only [lsProg_332, BitVec.ofNat_eq_ofNat] at hwb hpc ⊢
  refine SepWP.fold (chunkedEkSentCt1ReceivedAt_extract63 A ((s0.sp - 4240#64) + 976#64) outSt)
    (by sep_focus) ?_
  wp_pull_exists; rename_i w_out
  refine SepWP.pure_elim fun _ => ?_
  have hsp_align' : (s0.sp &&& 15#64 == 0#64) = true := hsp_align
  have hfsp_align : ((s0.sp - 4240#64) &&& 15#64 == 0#64) = true :=
    spAligned_sub s0.sp 4240#64 hsp_align (by decide)
  let sp1 : SendEkSpills :=
    { b0 := ⟨sp.b0.w0, sp.b0.w1, sp.b0.w2, sp.b0.w3, sp.b0.w4, w_out.b4.w1, sp.b0.w6, sp.b0.w7,
             sp.b0.w8, w_out.b3.w3⟩
      b1 := ⟨sp.b1.w0, sp.b1.w1, sp.b1.w2, sp.b1.w3, sp.b1.w4, sp.b1.w5, w_out.b0.w0,
             w_out.b5.w9, w_out.b1.w5, w_out.b1.w6⟩
      b2 := ⟨sp.b2.w0, sp.b2.w1, sp.b2.w2, w_out.b4.w3, sp.b2.w4, w_out.b0.w1, sp.b2.w6, 6#64,
             noneCap, w_out.b4.w2⟩
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
  · have hfold_sp1 :
        (words63At ((s0.sp - 4240#64) + 976#64) w_out ∗
         memRegion ((s0.sp - 4240#64) + 1480#64) 376) ∗
        sendEkSpillsAt (s0.sp - 4240#64) sp1 ⊢
          memRegion ((s0.sp - 4240#64) + 976#64) 880 ∗
          sendEkSpillsAt (s0.sp - 4240#64) sp1 :=
      sepConj_mono_left (words63At_376_entails_memRegion_880
        ((s0.sp - 4240#64) + 976#64) ((s0.sp - 4240#64) + 1480#64) w_out (by bv_omega))
    by_vm_steps (
      generalize hsp0 : s0.sp = sp0 at hsp hsp_align' hfsp_align hfold_sp1 ⊢
      wp_conv_pre =>
        dsimp only [sendEkSpillsAt, words63At, words10At]
        simp only [pointsTo128_eq_pair64_recv, BitVec.add_assoc, arm64_norm]
      wp_steps
      subst hsp0
      refine SepWP.fold
        (F := P_rest ∗
          relocatedHeap (fun dst => chunkedEkSentCt1ReceivedAt A dst outSt) (wordsBytes (words63List w_out)) ∗
          memRegion outA v1RecvSize ∗
          stackAt (s0.sp - 4240#64) statesRecvCalleeStackX ∗
          memRegion ((s0.sp - 4240#64) + 576#64) 376 ∗
          memRegion ((s0.sp - 4240#64) + 1856#64) 880 ∗
          sendEkUnusedAt (s0.sp - 4240#64) ∗
          statesRecvSavedCells s0)
        hfold_sp1
        (by
          dsimp only [sendEkSpillsAt, words63At, words10At, sp1]
          simp only [pointsTo128_eq_pair64_recv, BitVec.add_assoc, arm64_norm]
          sep_ac_rfl) ?_
      refine DropChunkedClPlacedBudgetAux.align_pre_vm (by sep_ac_rfl) ?_
      rcases w_out with ⟨⟨_, _, _, _, _, _, _, _, _, _⟩, ⟨_, _, _, _, _, _, _, _, _, _⟩,
        ⟨_, _, _, _, _, _, _, _, _, _⟩, ⟨_, _, _, _, _, _, _, _, _, _⟩,
        ⟨_, _, _, _, _, _, _, _, _, _⟩, ⟨_, _, _, _, _, _, _, _, _, _⟩, _, _⟩
      dsimp only [writebackWords63, sp1, Reg.x0, Reg.x1, Reg.x2, Reg.x3, Reg.x4, Reg.x5, Reg.x6,
        Reg.x7, Reg.x8, Reg.x9, Reg.x10, Reg.x11, Reg.x12, Reg.x13, Reg.x14, Reg.x15, Reg.x16,
        Reg.x17, Reg.x19, Reg.x20, Reg.x21, Reg.x22, Reg.x23, Reg.x24, Reg.x25, Reg.x26, Reg.x27, Reg.x28,
        Reg.x30] at hx19 ⊢
      simp only [TraceCalleeSaved, hsp, hx19, htr.1, htr.2, wp_norm, arm64_norm]
      wp_done
    )
  · intro sm hpcm hrunm hvm_m ⟨hsp_m, hx19_m, htr_m, hwb_m⟩
    refine SepWP.mono
      (hwb sm outA sp1
        (P_rest ∗ relocatedHeap (fun dst => chunkedEkSentCt1ReceivedAt A dst outSt) (wordsBytes (words63List w_out)))
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

set_option maxHeartbeats 1200000 in
/-- Relocatable `.ct1Received` arm when `msg.epoch < st.uc.epoch` parameterized by `hmemcpy_sat`,
    establishing `VmPreserved s sf`. -/
theorem ct1Received_arm_lt_sat_placed [LibsignalPlacement]
    {A : RustAlloc} {F : ShaCompress} {ext : String → Option (State → State)}
    (hmemcpy_sat : HookSat (Rust.withPanics ext) spqrMemcpySym (withVmPreserved sessionMemcpySpec))
    (s0 s : State) (outA selfA msgA : BitVec 64)
    (st : Chunked.SendEk.Ct1Received spqrPolyApi (spqrAuthApi F))
    (msg : Message spqrPolyApi)
    (P_rest : SepProp)
    (hlt : msg.epoch < st.uc.epoch)
    (hpc : s.pc = lsmpl.base 332 + 1204#64)
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
        chunkedStatesAt A selfA (.ct1Received st) ∗
        messageAt spqrPolyApi msgA msg ∗
        A.pool ∗
        stackAt (s0.sp - 4240#64) statesRecvCalleeStackX ∗
        memRegion (s0.sp - 4240#64) 4144 ∗
        statesRecvSavedCells s0)
      (fun sf Pf =>
        VmPreserved s sf ∧
        (Pf ⊢
          P_rest ∗
          resultV1RecvAt A (F := F) outA (.ok { key := none, state := .ct1Received st }) ∗
          memRegion selfA chunkedStatesSize ∗
          messageAt spqrPolyApi msgA msg ∗
          A.pool ∗
          stackAt s0.sp statesRecvStackX) ∧
        sf.sp = s0.sp ∧
        CalleeSavedPreserved s0 sf ∧
        sf.trace = s0.trace) := by
  have hlt_nat : msg.epoch.toNat < st.uc.epoch.toNat := BitVec.lt_def.mp hlt
  have hcond1 := epoch_cmp_ct1r_eq_of_lt hlt_nat
  have hcond2 := epoch_cmp_ct1r_eq_1_of_lt hlt_nat
  have hwb := @states_recv_writeback_59e88_sat_placed _ ext hmemcpy_sat
    (F_tail := fun a => memRegion a 376) (Relocatable.of_memRegion 376) s0
  rw [lsmpl_base_332_eq] at hpc hwb
  dsimp only [lsProg_332, chunkedStatesAt, messageAt, BitVec.ofNat_eq_ofNat] at hpc hwb ⊢
  refine SepWP.fold (memRegion_4144_entails_sendEkFrame (s0.sp - 4240#64)) (by sep_focus) ?_
  wp_pull_exists; rename_i sp
  refine SepWP.fold (sendEkUnusedAt_split_ac0 (s0.sp - 4240#64)) (by sep_focus) ?_
  wp_pull_exists; rename_i u_ac0
  refine SepWP.fold (chunkedCt1ReceivedAt_extract63 A (selfA + 8#64) st) (by sep_focus) ?_
  wp_pull_exists; rename_i w
  refine SepWP.pure_elim fun hw62 => ?_
  have hsp_align' : (s0.sp &&& 15#64 == 0#64) = true := hsp_align
  have hfsp_align : ((s0.sp - 4240#64) &&& 15#64 == 0#64) = true :=
    spAligned_sub s0.sp 4240#64 hsp_align (by decide)
  let sp1 : SendEkSpills :=
    { b0 := ⟨w.b5.w2, sp.b0.w1, w.b3.w1, sp.b0.w3, sp.b0.w4, w.b4.w1, w.b4.w0, sp.b0.w7,
             sp.b0.w8, w.b3.w3⟩
      b1 := ⟨sp.b1.w0, sp.b1.w1, w.b3.w9, sp.b1.w3, w.b5.w3, sp.b1.w5, w.b0.w0, w.b5.w9,
             w.b1.w5, w.b1.w6⟩
      b2 := ⟨w.b4.w7, w.b5.w1, w.b4.w9, w.b4.w3, w.b4.w5, w.b0.w1, w.b4.w8, 5#64,
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
  refine seq_vm_clean (mid := (blkPl_332).base + 18996#64)
    (P_mid :=
      (P_rest ∗
        relocatedHeap (fun dst => chunkedCt1ReceivedAt A dst st) (wordsBytes (words63List w)) ∗
        memRegion selfA chunkedStatesSize ∗
        ((msgA ↦₆₄ msg.epoch) ∗ messagePayloadAt spqrPolyApi msgA msg.payload) ∗
        A.pool) ∗
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
      writebackWords63 sm sp1 = w)
    ?_ ?_
  · have hfold_unused :
        ((s0.sp - 4240#64 + 2752#64) ↦₁₂₈ w.q60) ∗
        memRegion (s0.sp - 4240#64) 8 ∗
        memRegion (s0.sp - 4240#64 + 568#64) 8 ∗
        memRegion (s0.sp - 4240#64 + 952#64) 8 ∗
        memRegion (s0.sp - 4240#64 + 2736#64) 16 ∗
        memRegion (s0.sp - 4240#64 + 2768#64) 1376 ⊢
          sendEkUnusedAt (s0.sp - 4240#64) :=
      sendEkUnusedAt_rejoin_ac0 (s0.sp - 4240#64) w.q60
    have hfold_self_unused :
        ((selfA ↦₆₄ 5#64) ∗ words63At (selfA + 8#64) w ∗ memRegion (selfA + 512#64) 416) ∗
        (((s0.sp - 4240#64 + 2752#64) ↦₁₂₈ w.q60) ∗
         memRegion (s0.sp - 4240#64) 8 ∗
         memRegion (s0.sp - 4240#64 + 568#64) 8 ∗
         memRegion (s0.sp - 4240#64 + 952#64) 8 ∗
         memRegion (s0.sp - 4240#64 + 2736#64) 16 ∗
         memRegion (s0.sp - 4240#64 + 2768#64) 1376) ∗
        sendEkSpillsAt (s0.sp - 4240#64) sp1 ⊢
          memRegion selfA chunkedStatesSize ∗
          sendEkUnusedAt (s0.sp - 4240#64) ∗
          sendEkSpillsAt (s0.sp - 4240#64) sp1 :=
      sepConj_mono (words63At_self_entails_memRegion_928 selfA 5#64 w)
        (sepConj_mono_left hfold_unused)
    by_vm_steps (
      generalize hsp0 : s0.sp = sp0 at hsp hsp_align' hfsp_align hfold_unused hfold_self_unused ⊢
      wp_conv_pre =>
        dsimp only [sendEkSpillsAt, words63At, words10At]
        simp only [pointsTo128_eq_pair64_recv, BitVec.add_assoc, arm64_norm]
      rw [hw62]
      wp_steps 256
      subst hsp0
      refine SepWP.fold
        (F := P_rest ∗
          relocatedHeap (fun dst => chunkedCt1ReceivedAt A dst st) (wordsBytes (words63List w)) ∗
          ((msgA ↦₆₄ msg.epoch) ∗ messagePayloadAt spqrPolyApi msgA msg.payload) ∗
          A.pool ∗
          memRegion outA v1RecvSize ∗
          stackAt (s0.sp - 4240#64) statesRecvCalleeStackX ∗
          memRegion ((s0.sp - 4240#64) + 576#64) 376 ∗
          memRegion ((s0.sp - 4240#64) + 976#64) 880 ∗
          memRegion ((s0.sp - 4240#64) + 1856#64) 880 ∗
          statesRecvSavedCells s0)
        hfold_self_unused
        (by
          rw [← hw62]
          dsimp only [sendEkSpillsAt, words63At, words10At, sp1]
          simp only [pointsTo128_eq_pair64_recv, BitVec.add_assoc, arm64_norm]
          sep_ac_rfl) ?_
      refine DropChunkedClPlacedBudgetAux.align_pre_vm (by sep_ac_rfl) ?_
      rcases w with ⟨⟨_, _, _, _, _, _, _, _, _, _⟩, ⟨_, _, _, _, _, _, _, _, _, _⟩,
        ⟨_, _, _, _, _, _, _, _, _, _⟩, ⟨_, _, _, _, _, _, _, _, _, _⟩,
        ⟨_, _, _, _, _, _, _, _, _, _⟩, ⟨_, _, _, _, _, _, _, _, _, _⟩, _, _⟩
      dsimp only [writebackWords63, sp1, Reg.x0, Reg.x1, Reg.x2, Reg.x3, Reg.x4, Reg.x5, Reg.x6,
        Reg.x7, Reg.x8, Reg.x9, Reg.x10, Reg.x11, Reg.x12, Reg.x13, Reg.x14, Reg.x15, Reg.x16,
        Reg.x17, Reg.x19, Reg.x20, Reg.x21, Reg.x22, Reg.x23, Reg.x24, Reg.x25, Reg.x26, Reg.x27, Reg.x28,
        Reg.x30] at hx1 hx19 ⊢
      simp only [TraceCalleeSaved, hsp, hx1, hx19, htr.1, htr.2, wp_norm, arm64_norm]
      wp_done
    )
  · intro sm hpcm hrunm hvm_m ⟨hsp_m, hx19_m, htr_m, hwb_m⟩
    refine SepWP.mono
      (hwb sm outA sp1
        (P_rest ∗
          relocatedHeap (fun dst => chunkedCt1ReceivedAt A dst st) (wordsBytes (words63List w)) ∗
          memRegion selfA chunkedStatesSize ∗
          ((msgA ↦₆₄ msg.epoch) ∗ messagePayloadAt spqrPolyApi msgA msg.payload) ∗
          A.pool)
        hpcm hrunm hsp_m hsp_align hx19_m htr_m)
      (fun sf Pf _ _ ⟨hvm_wb, hPf, hsp_sf, hcs_sf, htr_sf⟩ =>
        ⟨hvm_m.trans hvm_wb, ?_, hsp_sf, hcs_sf, htr_sf⟩)
    refine Entails.trans hPf ?_
    have hrec := writeback_ct1Received_entails_resultV1RecvAt A (F := F) outA st w
      (sm.readReg64 .x20) sp.q200
    have htag : sp1.b2.w7 = 5#64 := rfl
    have hnone : sp1.b2.w8 = noneCap := rfl
    have hq200 : sp1.q200 = sp.q200 := rfl
    rw [htag, hnone, hq200, hwb_m]
    refine Entails.trans (Entails.of_eq (by sep_ac_rfl))
      (sepConj_mono_right (sepConj_mono_left hrec))

theorem ct1Received_arm_lt_pool_placed [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits} {F : ShaCompress}
    {ext : String → Option (State → State)}
    (hmemcpy_sat : HookSat (Rust.withPanics ext) spqrMemcpySym (withVmPreserved sessionMemcpySpec))
    (st_cost : M.σ)
    (s0 s : State) (outA selfA msgA : BitVec 64)
    (st : Chunked.SendEk.Ct1Received spqrPolyApi (spqrAuthApi F))
    (msg : Message spqrPolyApi)
    (P_rest : SepProp)
    (hlt : msg.epoch < st.uc.epoch)
    (hpc : s.pc = lsmpl.base 332 + 1204#64)
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
        chunkedStatesAt A.repAlloc selfA (.ct1Received st) ∗
        messageAt spqrPolyApi msgA msg ∗
        A.pool lim st_cost s ∗
        stackAt (s0.sp - 4240#64) statesRecvCalleeStackX ∗
        memRegion (s0.sp - 4240#64) 4144 ∗
        statesRecvSavedCells s0)
      (fun sf Pf =>
        VmPreserved s sf ∧
        (Pf ⊢
          P_rest ∗
          resultV1RecvAt A.repAlloc (F := F) outA (.ok { key := none, state := .ct1Received st }) ∗
          memRegion selfA chunkedStatesSize ∗
          messageAt spqrPolyApi msgA msg ∗
          A.pool lim st_cost sf ∗
          stackAt s0.sp statesRecvStackX) ∧
        sf.sp = s0.sp ∧
        CalleeSavedPreserved s0 sf ∧
        sf.trace = s0.trace) := by
  refine SepWP.weaken_pre
    (P' := (P_rest ∗ A.pool lim st_cost s) ∗
      memRegion outA v1RecvSize ∗
      chunkedStatesAt A.repAlloc selfA (.ct1Received st) ∗
      messageAt spqrPolyApi msgA msg ∗
      A.repAlloc.pool ∗
      stackAt (s0.sp - 4240#64) statesRecvCalleeStackX ∗
      memRegion (s0.sp - 4240#64) 4144 ∗
      statesRecvSavedCells s0)
    (Entails.of_eq (by simp only [RustCliAllocBudget.repAlloc_pool, emp_sepConj, sepConj_emp]; sep_ac_rfl))
    (SepWP.mono
      (ct1Received_arm_lt_sat_placed (A := A.repAlloc) hmemcpy_sat s0 s outA selfA msgA st msg
        (P_rest ∗ A.pool lim st_cost s) hlt hpc hrun hsp hsp_align hx1 hx19 hx24 htr)
      fun sf Pf _ _ ⟨hvm, hPf, hsp_sf, hcs_sf, htr_sf⟩ =>
        ⟨hvm, Entails.trans hPf (Entails.of_eq (by
          rw [← A.pool_transport lim st_cost s sf hvm]
          simp only [RustCliAllocBudget.repAlloc_pool, emp_sepConj, sepConj_emp]
          sep_ac_rfl)), hsp_sf, hcs_sf, htr_sf⟩)

set_option maxHeartbeats 1200000 in
/-- Relocatable `.ct1Received` arm when `msg.epoch = st.uc.epoch` and `msg.payload ≠ .ct2 _`
    (`+1204 -> s0.x30`, Block `332`), establishing `VmPreserved s sf`. -/
theorem ct1Received_arm_eq_other_placed [LibsignalPlacement]
    {A : RustAlloc} {F : ShaCompress} {ext : String → Option (State → State)}
    (hmemcpy_sat : HookSat (Rust.withPanics ext) spqrMemcpySym (withVmPreserved sessionMemcpySpec))
    (s0 s : State) (outA selfA msgA : BitVec 64)
    (st : Chunked.SendEk.Ct1Received spqrPolyApi (spqrAuthApi F))
    (msg : Message spqrPolyApi)
    (P_rest : SepProp)
    (heq : msg.epoch = st.uc.epoch)
    (hct2 : ∀ c, msg.payload ≠ .ct2 c)
    (hpc : s.pc = lsmpl.base 332 + 1204#64)
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
        chunkedStatesAt A selfA (.ct1Received st) ∗
        messageAt spqrPolyApi msgA msg ∗
        A.pool ∗
        stackAt (s0.sp - 4240#64) statesRecvCalleeStackX ∗
        memRegion (s0.sp - 4240#64) 4144 ∗
        statesRecvSavedCells s0)
      (fun sf Pf =>
        VmPreserved s sf ∧
        (Pf ⊢
          P_rest ∗
          resultV1RecvAt A (F := F) outA (.ok { key := none, state := .ct1Received st }) ∗
          memRegion selfA chunkedStatesSize ∗
          messageAt spqrPolyApi msgA msg ∗
          A.pool ∗
          stackAt s0.sp statesRecvStackX) ∧
        sf.sp = s0.sp ∧
        CalleeSavedPreserved s0 sf ∧
        sf.trace = s0.trace) := by
  have hcond1 := epoch_cmp_ct1r_eq_of_eq st.uc.epoch
  have hcond_tag1 := messagePayloadTag_eq_6_of_not_ct2 hct2
  have hcond_tag2 := messagePayloadTag_bne_6_of_not_ct2 hct2
  have hwb := @states_recv_writeback_59e88_sat_placed _ ext hmemcpy_sat
    (F_tail := fun a => memRegion a 376) (Relocatable.of_memRegion 376) s0
  rw [lsmpl_base_332_eq] at hpc hwb
  dsimp only [lsProg_332, chunkedStatesAt, messageAt, BitVec.ofNat_eq_ofNat] at hpc hwb ⊢
  refine SepWP.fold (memRegion_4144_entails_sendEkFrame (s0.sp - 4240#64)) (by sep_focus) ?_
  wp_pull_exists; rename_i sp
  refine SepWP.fold (sendEkUnusedAt_split_ac0 (s0.sp - 4240#64)) (by sep_focus) ?_
  wp_pull_exists; rename_i u_ac0
  refine SepWP.fold (chunkedCt1ReceivedAt_extract63 A (selfA + 8#64) st) (by sep_focus) ?_
  wp_pull_exists; rename_i w
  refine SepWP.pure_elim fun hw62 => ?_
  have hsp_align' : (s0.sp &&& 15#64 == 0#64) = true := hsp_align
  have hfsp_align : ((s0.sp - 4240#64) &&& 15#64 == 0#64) = true :=
    spAligned_sub s0.sp 4240#64 hsp_align (by decide)
  let sp1 : SendEkSpills :=
    { b0 := ⟨w.b5.w2, sp.b0.w1, w.b3.w1, sp.b0.w3, sp.b0.w4, w.b4.w1, w.b4.w0, sp.b0.w7,
             sp.b0.w8, w.b3.w3⟩
      b1 := ⟨sp.b1.w0, sp.b1.w1, w.b3.w9, sp.b1.w3, w.b5.w3, sp.b1.w5, w.b0.w0, w.b5.w9,
             w.b1.w5, w.b1.w6⟩
      b2 := ⟨w.b4.w7, w.b5.w1, w.b4.w9, w.b4.w3, w.b4.w5, w.b0.w1, w.b4.w8, 5#64,
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
  refine seq_vm_clean (mid := (blkPl_332).base + 18996#64)
    (P_mid :=
      (P_rest ∗
        relocatedHeap (fun dst => chunkedCt1ReceivedAt A dst st) (wordsBytes (words63List w)) ∗
        memRegion selfA chunkedStatesSize ∗
        ((msgA ↦₆₄ msg.epoch) ∗ messagePayloadAt spqrPolyApi msgA msg.payload) ∗
        A.pool) ∗
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
      writebackWords63 sm sp1 = w)
    ?_ ?_
  · have hfold_unused :
        ((s0.sp - 4240#64 + 2752#64) ↦₁₂₈ w.q60) ∗
        memRegion (s0.sp - 4240#64) 8 ∗
        memRegion (s0.sp - 4240#64 + 568#64) 8 ∗
        memRegion (s0.sp - 4240#64 + 952#64) 8 ∗
        memRegion (s0.sp - 4240#64 + 2736#64) 16 ∗
        memRegion (s0.sp - 4240#64 + 2768#64) 1376 ⊢
          sendEkUnusedAt (s0.sp - 4240#64) :=
      sendEkUnusedAt_rejoin_ac0 (s0.sp - 4240#64) w.q60
    have hfold_self_unused :
        ((selfA ↦₆₄ 5#64) ∗ words63At (selfA + 8#64) w ∗ memRegion (selfA + 512#64) 416) ∗
        (((s0.sp - 4240#64 + 2752#64) ↦₁₂₈ w.q60) ∗
         memRegion (s0.sp - 4240#64) 8 ∗
         memRegion (s0.sp - 4240#64 + 568#64) 8 ∗
         memRegion (s0.sp - 4240#64 + 952#64) 8 ∗
         memRegion (s0.sp - 4240#64 + 2736#64) 16 ∗
         memRegion (s0.sp - 4240#64 + 2768#64) 1376) ∗
        sendEkSpillsAt (s0.sp - 4240#64) sp1 ⊢
          memRegion selfA chunkedStatesSize ∗
          sendEkUnusedAt (s0.sp - 4240#64) ∗
          sendEkSpillsAt (s0.sp - 4240#64) sp1 :=
      sepConj_mono (words63At_self_entails_memRegion_928 selfA 5#64 w)
        (sepConj_mono_left hfold_unused)
    by_vm_steps (
      generalize hsp0 : s0.sp = sp0 at hsp hsp_align' hfsp_align hfold_unused hfold_self_unused ⊢
      wp_conv_pre =>
        dsimp only [sendEkSpillsAt, words63At, words10At]
        rw [hw62, heq, messagePayloadAt_eq_tag_tail msgA msg.payload]
        simp only [pointsTo128_eq_pair64_recv, BitVec.add_assoc, arm64_norm]
      wp_steps 256
      subst hsp0
      refine SepWP.fold
        (F := P_rest ∗
          relocatedHeap (fun dst => chunkedCt1ReceivedAt A dst st) (wordsBytes (words63List w)) ∗
          ((msgA ↦₆₄ msg.epoch) ∗ messagePayloadAt spqrPolyApi msgA msg.payload) ∗
          A.pool ∗
          memRegion outA v1RecvSize ∗
          stackAt (s0.sp - 4240#64) statesRecvCalleeStackX ∗
          memRegion ((s0.sp - 4240#64) + 576#64) 376 ∗
          memRegion ((s0.sp - 4240#64) + 976#64) 880 ∗
          memRegion ((s0.sp - 4240#64) + 1856#64) 880 ∗
          statesRecvSavedCells s0)
        hfold_self_unused
        (by
          dsimp only [sendEkSpillsAt, words63At, words10At, sp1]
          rw [hw62, heq, messagePayloadAt_eq_tag_tail msgA msg.payload]
          simp only [pointsTo128_eq_pair64_recv, BitVec.add_assoc, arm64_norm]
          sep_ac_rfl) ?_
      refine DropChunkedClPlacedBudgetAux.align_pre_vm (by sep_ac_rfl) ?_
      rcases w with ⟨⟨_, _, _, _, _, _, _, _, _, _⟩, ⟨_, _, _, _, _, _, _, _, _, _⟩,
        ⟨_, _, _, _, _, _, _, _, _, _⟩, ⟨_, _, _, _, _, _, _, _, _, _⟩,
        ⟨_, _, _, _, _, _, _, _, _, _⟩, ⟨_, _, _, _, _, _, _, _, _, _⟩, _, _⟩
      dsimp only [writebackWords63, sp1, Reg.x0, Reg.x1, Reg.x2, Reg.x3, Reg.x4, Reg.x5, Reg.x6,
        Reg.x7, Reg.x8, Reg.x9, Reg.x10, Reg.x11, Reg.x12, Reg.x13, Reg.x14, Reg.x15, Reg.x16,
        Reg.x17, Reg.x19, Reg.x20, Reg.x21, Reg.x22, Reg.x23, Reg.x24, Reg.x25, Reg.x26, Reg.x27, Reg.x28,
        Reg.x30] at hx1 hx19 ⊢
      simp only [TraceCalleeSaved, hsp, hx1, hx19, htr.1, htr.2, wp_norm, arm64_norm]
      wp_done
    )
  · intro sm hpcm hrunm hvm_m ⟨hsp_m, hx19_m, htr_m, hwb_m⟩
    refine SepWP.mono
      (hwb sm outA sp1
        (P_rest ∗
          relocatedHeap (fun dst => chunkedCt1ReceivedAt A dst st) (wordsBytes (words63List w)) ∗
          memRegion selfA chunkedStatesSize ∗
          ((msgA ↦₆₄ msg.epoch) ∗ messagePayloadAt spqrPolyApi msgA msg.payload) ∗
          A.pool)
        hpcm hrunm hsp_m hsp_align hx19_m htr_m)
      (fun sf Pf _ _ ⟨hvm_wb, hPf, hsp_sf, hcs_sf, htr_sf⟩ =>
        ⟨hvm_m.trans hvm_wb, ?_, hsp_sf, hcs_sf, htr_sf⟩)
    refine Entails.trans hPf ?_
    have hrec := writeback_ct1Received_entails_resultV1RecvAt A (F := F) outA st w
      (sm.readReg64 .x20) sp.q200
    have htag : sp1.b2.w7 = 5#64 := rfl
    have hnone : sp1.b2.w8 = noneCap := rfl
    have hq200 : sp1.q200 = sp.q200 := rfl
    rw [htag, hnone, hq200, hwb_m]
    refine Entails.trans (Entails.of_eq (by sep_ac_rfl))
      (sepConj_mono_right (sepConj_mono_left hrec))

theorem ct1Received_arm_eq_other_pool_placed [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits} {F : ShaCompress}
    {ext : String → Option (State → State)}
    (hmemcpy_sat : HookSat (Rust.withPanics ext) spqrMemcpySym (withVmPreserved sessionMemcpySpec))
    (st_cost : M.σ)
    (s0 s : State) (outA selfA msgA : BitVec 64)
    (st : Chunked.SendEk.Ct1Received spqrPolyApi (spqrAuthApi F))
    (msg : Message spqrPolyApi)
    (P_rest : SepProp)
    (heq : msg.epoch = st.uc.epoch)
    (hct2 : ∀ c, msg.payload ≠ .ct2 c)
    (hpc : s.pc = lsmpl.base 332 + 1204#64)
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
        chunkedStatesAt A.repAlloc selfA (.ct1Received st) ∗
        messageAt spqrPolyApi msgA msg ∗
        A.pool lim st_cost s ∗
        stackAt (s0.sp - 4240#64) statesRecvCalleeStackX ∗
        memRegion (s0.sp - 4240#64) 4144 ∗
        statesRecvSavedCells s0)
      (fun sf Pf =>
        VmPreserved s sf ∧
        (Pf ⊢
          P_rest ∗
          resultV1RecvAt A.repAlloc (F := F) outA (.ok { key := none, state := .ct1Received st }) ∗
          memRegion selfA chunkedStatesSize ∗
          messageAt spqrPolyApi msgA msg ∗
          A.pool lim st_cost sf ∗
          stackAt s0.sp statesRecvStackX) ∧
        sf.sp = s0.sp ∧
        CalleeSavedPreserved s0 sf ∧
        sf.trace = s0.trace) := by
  refine SepWP.weaken_pre
    (P' := (P_rest ∗ A.pool lim st_cost s) ∗
      memRegion outA v1RecvSize ∗
      chunkedStatesAt A.repAlloc selfA (.ct1Received st) ∗
      messageAt spqrPolyApi msgA msg ∗
      A.repAlloc.pool ∗
      stackAt (s0.sp - 4240#64) statesRecvCalleeStackX ∗
      memRegion (s0.sp - 4240#64) 4144 ∗
      statesRecvSavedCells s0)
    (Entails.of_eq (by simp only [RustCliAllocBudget.repAlloc_pool, emp_sepConj, sepConj_emp]; sep_ac_rfl))
    (SepWP.mono
      (ct1Received_arm_eq_other_placed (A := A.repAlloc) hmemcpy_sat s0 s outA selfA msgA st msg
        (P_rest ∗ A.pool lim st_cost s) heq hct2 hpc hrun hsp hsp_align hx1 hx19 hx24 htr)
      fun sf Pf _ _ ⟨hvm, hPf, hsp_sf, hcs_sf, htr_sf⟩ =>
        ⟨hvm, Entails.trans hPf (Entails.of_eq (by
          rw [← A.pool_transport lim st_cost s sf hvm]
          simp only [RustCliAllocBudget.repAlloc_pool, emp_sepConj, sepConj_emp]
          sep_ac_rfl)), hsp_sf, hcs_sf, htr_sf⟩)

/-! ## 3. Budget-Threaded `<Ct1Received>::recv_ct2_chunk` Call & `.ct2` Arm (`+1204 -> s0.x30`) -/

/-- Relocatable framed `SepWP` call rule for `ct1ReceivedRecvCt2ChunkSpecOfPrePostEnv` (Block `346`). -/
theorem call_ct1ReceivedRecvCt2Chunk_placed [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits} {F : ShaCompress}
    {CalleePre CalleePost : Ct1ReceivedRecvCt2ChunkGhost F → List AllocEvent → Prop}
    {prog : Program} {entry ret_pc target_pc : BitVec 64}
    (hcall : subroutine_ok prog entry
      (withLsCodeLoaded lsmpl
        (ct1ReceivedRecvCt2ChunkSpecOfPrePostEnv M A lim F CalleePre CalleePost)))
    (outA stA chunkA : BitVec 64)
    (st : Chunked.SendEk.Ct1Received spqrPolyApi (spqrAuthApi F))
    (chunk : Chunk)
    (outSt : Chunked.SendEk.EkSentCt1Received spqrPolyApi (spqrAuthApi F))
    (st_cost : M.σ)
    (hrecv : st.recv_ct2_chunk st.uc.epoch chunk = .ok outSt)
    (hfit : FitsEnv M lim st_cost (CalleePre ⟨outA, stA, chunkA, st, chunk, outSt⟩))
    {s0 s : State} {sp_call : BitVec 64} {P Frame : SepProp}
    {post : State → SepProp → Prop}
    (hcl : LibsignalCodeLoaded lsmpl s.mem)
    (hpc : s.pc = entry)
    (hrun : s.status = .Running)
    (hsp : s.sp = sp_call)
    (hsp_align : (sp_call &&& 15#64 == 0#64) = true)
    (hlr : s.readReg64 Reg.lr = ret_pc)
    (htrace : TraceCalleeSaved s s0)
    (hx0 : s.readReg64 Reg.x0 = outA)
    (hx1 : s.readReg64 .x1 = stA)
    (hx2 : s.readReg64 .x2 = st.uc.epoch)
    (hx3 : s.readReg64 .x3 = chunkA)
    (hsplit : P = (memRegion outA chunkedEkSentCt1ReceivedSize ∗
      chunkedCt1ReceivedAt A.repAlloc stA st ∗ chunkAt chunkA chunk ∗
      A.pool lim st_cost s ∗ stackAt sp_call ct1ReceivedRecvCt2ChunkStack) ∗ Frame)
    (hnext : ∀ (evs : List AllocEvent),
      CalleePost ⟨outA, stA, chunkA, st, chunk, outSt⟩ evs →
      ∀ sf : State, sf.pc = ret_pc → sf.status = .Running →
        sf.sp = sp_call → CalleeSavedPreserved s sf → TraceCalleeSaved sf s0 →
        SepWP prog target_pc sf
          ((chunkedEkSentCt1ReceivedAt A.repAlloc outA outSt ∗
            memRegion stA chunkedCt1ReceivedSize ∗ chunkAt chunkA chunk ∗
            A.pool lim (M.stepEvents evs st_cost) sf ∗
            stackAt sp_call ct1ReceivedRecvCt2ChunkStack) ∗ Frame) post)
    (hlr_ls : LsRetAddr624 ret_pc := by
      first | assumption | simp (config := { decide := true }) only [arm64_norm, wp_norm]) :
    SepWP prog target_pc s P post := by
  have hsp_align_s : s.spAligned = true := by
    rw [State.spAligned, hsp]; exact hsp_align
  refine SepWP.call_subroutine_frame hcall
    (x := (⟨outA, stA, chunkA, st, chunk, outSt⟩, st_cost))
    (F := Frame)
    hpc hrun hsp_align_s hlr ?_ ?_ ?_ ?_ ?_
  · intro R' hm
    rw [hsplit] at hm
    dsimp only [withLsCodeLoaded]
    rw [sepConj_assoc, sepConj_left_comm, satisfies_pure_sepConj]
    refine ⟨hcl, ?_⟩
    dsimp only [ct1ReceivedRecvCt2ChunkSpecOfPrePostEnv]
    rw [hsp]
    simp only [sepConj_assoc, satisfies_pure_sepConj]
    exact ⟨⟨hx0, hx1, hx2, hx3, hrecv, hfit, by rw [Reg.lr] at hlr; rw [hlr]; exact hlr_ls⟩,
      Satisfies.mono (Entails.of_eq (by sep_ac_rfl)) hm⟩
  · intro _ _ _ hp
    unfold withLsCodeLoaded ct1ReceivedRecvCt2ChunkSpecOfPrePostEnv at hp; dsimp only at hp
    exact ((satisfies_pure_sepConj _ _ _).mp hp).1
  · intro _ _ _ _ he
    unfold withLsCodeLoaded ct1ReceivedRecvCt2ChunkSpecOfPrePostEnv at he; dsimp only at he
    exact ((satisfies_pure_sepConj _ _ _).mp he).1
  · intro sf hpc_sf hrun_sf hsp_sf hcs_sf
    dsimp only [withLsCodeLoaded, ct1ReceivedRecvCt2ChunkSpecOfPrePostEnv]
    rw [hsp, sepExists_sepConj_left]
    apply ProofLib.SepWP.exists_left; intro evs
    simp only [sepConj_assoc]
    refine SepWP.pure_elim fun ⟨htr_sf, hevs⟩ => ?_
    exact SepWP.weaken_pre (Entails.of_eq (by sep_ac_rfl))
      (hnext evs hevs sf hpc_sf hrun_sf (hsp_sf.trans hsp) hcs_sf
        ⟨htr_sf.trans htrace.1, hcs_sf.2.2.2.2.2.2.2.2.2.2.2.trans htrace.2⟩)
  · intro _ _ _ ho
    unfold withLsCodeLoaded ct1ReceivedRecvCt2ChunkSpecOfPrePostEnv at ho; dsimp only at ho
    exact False.elim ((satisfies_pure_sepConj _ _ _).mp ho).1

end LibsignalBinary.Proofs.SpqrV1.States.Recv.ArmCt1Received2PlacedBudgetAux
