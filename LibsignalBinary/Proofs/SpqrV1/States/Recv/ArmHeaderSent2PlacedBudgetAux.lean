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
public import LibsignalBinary.Proofs.SpqrV1.States.Leaves.DefsPlacedBudget
public import LibsignalBinary.Proofs.SpqrV1.States.Recv.ArmHeaderSent1PlacedBudget
public import LibsignalBinary.Proofs.SpqrV1.States.Recv.ArmNoHeaderReceivedStepsPlacedBudgetAux
public import LibsignalBinary.Proofs.SpqrV1.States.Recv.DefsPlacedBudget
public import LibsignalBinary.Proofs.SpqrV1.States.Recv.DispatchPlacedBudget
public import LibsignalBinary.Proofs.SpqrV1.States.Recv.SendEkCommon
import LibsignalBinary.Proofs.Common.SharedHelpers
import LibsignalBinary.Proofs.SpqrV1.Kdf.HkdfToSliceExtract
import LibsignalBinary.Proofs.SpqrV1.Poly.EncoderIntoPb.Defs
import LibsignalBinary.Proofs.SpqrV1.States.FromPb.Defs
import LibsignalBinary.Proofs.SpqrV1.States.Recv.ArmCt1Received1
import LibsignalBinary.Proofs.SpqrV1.States.Recv.ArmCt1Received2Placed
import LibsignalBinary.Proofs.SpqrV1.States.Recv.ArmHeaderSent1
import LibsignalBinary.Proofs.SpqrV1.States.Recv.ArmHeaderSent1Placed
import LibsignalBinary.Proofs.SpqrV1.States.Recv.ArmHeaderSent2
import LibsignalBinary.Proofs.SpqrV1.States.Recv.ArmHeaderSent2Placed
import LibsignalBinary.Proofs.SpqrV1.States.Recv.ArmsSendEk1
import LibsignalBinary.Proofs.SpqrV1.States.Recv.CodeSymFetch0Placed
import LibsignalBinary.Proofs.SpqrV1.States.Recv.CodeSymFetch1Placed
import LibsignalBinary.Proofs.SpqrV1.States.Recv.CodeSymFetch3Placed
import LibsignalBinary.Proofs.SpqrV1.States.Recv.CodeSymFetch4Placed
import LibsignalBinary.Proofs.SpqrV1.States.Recv.DispatchPlaced
import LibsignalBinary.Proofs.SpqrV1.States.Recv.SendEkCommonPlaced
import LibsignalBinary.Proofs.TripleRatchet.Getters.GettersCodeSym
import ProofLib.SepLogic.WPp
meta import LibsignalBinary.Proofs.Common.SharedHelpers -- shake: keep
meta import LibsignalBinary.Proofs.Placed.BudgetVmSteps -- shake: keep

/-!
# `<States>::recv` (Block `332`) — `.headerSent` Arm, Part 2 Aux (Budget-Threaded)

Allocator-event envelopes (`HeaderSentArmPreEnv` / `HeaderSentArmPostEnv`), `VmPreserved` `<` /
`eq_other` / post-call writeback blocks, and the framed `<HeaderSent>::recv_ct1_chunk` call rule
(Block `337`).
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 400000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

namespace LibsignalBinary.Proofs.SpqrV1.States.Recv.ArmHeaderSent2PlacedBudgetAux

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
open LibsignalBinary.Heap (
  AllocCallPreserved AllocCostModel AllocEvent BudgetLimits FitsEnv FreeOnlyEvs
  RustCliAllocBudget SeqEnv VmPreserved rustCliDeallocBudgetSpec
)
open LibsignalBinary.Heap.SpecBudget (withVmPreserved)
open LibsignalBinary.Proofs.SpqrV1.Poly.AddChunk.DefsBudget (
  AddChunkSlotsEnv addChunkSlotsEnv_nil
)
open LibsignalBinary.Proofs.SpqrV1.Poly.DecodedMessage.DefsBudget (
  DecodedMessageEnv
)
open LibsignalBinary.Proofs.SpqrV1.States.Leaves.Batch2DefsPlacedBudget (
  HeaderSentRecvCt1ChunkEnv HeaderSentRecvCt1ChunkPostEnv HeaderSentRecvCt1ChunkPreEnv
  headerSentRecvCt1ChunkPlacedSpec headerSentRecvCt1ChunkPlacedSpecOfEnv
  headerSentRecvCt1ChunkPlacedSpecOfPrePostEnv
)
open LibsignalBinary.Proofs.SpqrV1.States.Recv.ArmNoHeaderReceivedStepsPlacedBudgetAux (
  call_memcpy_relocate_cs_stack seq_vm_cont step_adrp_vm
)
open LibsignalBinary.Proofs.SpqrV1.States.Recv.DispatchPlacedBudget (
  states_recv_writeback_59e88_sat_placed
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
  Recv.sp_sub_96_add_16 Recv.sp_sub_96_add_32 Recv.sp_sub_96_add_48
  Recv.sp_sub_96_add_64 Recv.sp_sub_96_add_80
  sp_sub_96_sub_4096 sp_sub_4192_sub_48 sp_sub_4240_add_48 sp_sub_4240_add_4096 sp_sub_144_add_48
  sp_sub_96_add_8_recv sp_sub_80_add_8_recv sp_sub_64_add_8_recv sp_sub_48_add_8_recv
  sp_sub_32_add_8_recv sp_sub_16_add_8_recv sp_sub_96_add_96_recv
  sp_sub_4240_add_4144_hs bv376_toNat_hs bv880_toNat_hs
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

/-! ## 1. Arm Envelopes for `.headerSent` -/

/-- Allocation-phase prefix envelope for the `.headerSent` arm of `<States>::recv`:
    - `msg.epoch ≠ st.uc.epoch` or `msg.payload ≠ .ct1 _`: `[]`
    - `msg.epoch = st.uc.epoch` and `msg.payload = .ct1 chunk`:
      `SeqEnv (AddChunkSlotsEnv st.receiving_ct1.pts) (DecodedMessageEnv (addChunkTotal st.receiving_ct1 chunk))` -/
def HeaderSentArmPreEnv {F : ShaCompress}
    (st : Chunked.SendEk.HeaderSent spqrPolyApi (spqrAuthApi F))
    (msg : Message spqrPolyApi) (evs : List AllocEvent) : Prop :=
  if msg.epoch > st.uc.epoch then
    evs = []
  else if msg.epoch < st.uc.epoch then
    evs = []
  else
    match msg.payload with
    | .ct1 chunk =>
      SeqEnv (AddChunkSlotsEnv st.receiving_ct1.pts)
        (DecodedMessageEnv (addChunkTotal st.receiving_ct1 chunk)) evs
    | _ => evs = []

/-- Postcondition allocator-event envelope for the `.headerSent` arm of `<States>::recv`:
    - `msg.epoch > st.uc.epoch`: `FreeOnlyEvs`
    - `msg.epoch < st.uc.epoch` or `msg.payload ≠ .ct1 _`: `[]`
    - `msg.epoch = st.uc.epoch` and `msg.payload = .ct1 chunk`:
      `SeqEnv (SeqEnv (AddChunkSlotsEnv st.receiving_ct1.pts) (DecodedMessageEnv (addChunkTotal st.receiving_ct1 chunk))) FreeOnlyEvs` -/
def HeaderSentArmPostEnv {F : ShaCompress}
    (st : Chunked.SendEk.HeaderSent spqrPolyApi (spqrAuthApi F))
    (msg : Message spqrPolyApi) (evs : List AllocEvent) : Prop :=
  if msg.epoch > st.uc.epoch then
    FreeOnlyEvs evs
  else if msg.epoch < st.uc.epoch then
    evs = []
  else
    match msg.payload with
    | .ct1 chunk =>
      SeqEnv
        (SeqEnv (AddChunkSlotsEnv st.receiving_ct1.pts)
          (DecodedMessageEnv (addChunkTotal st.receiving_ct1 chunk)))
        FreeOnlyEvs evs
    | _ => evs = []

abbrev HeaderSentArmEnv {F : ShaCompress} := @HeaderSentArmPostEnv F

theorem headerSentArmPreEnv_nil {F : ShaCompress}
    (st : Chunked.SendEk.HeaderSent spqrPolyApi (spqrAuthApi F))
    (msg : Message spqrPolyApi) :
    HeaderSentArmPreEnv st msg [] := by
  unfold HeaderSentArmPreEnv
  split
  · rfl
  · split
    · rfl
    · cases msg.payload <;>
        first | rfl | exact Or.inl (addChunkSlotsEnv_nil st.receiving_ct1.pts)

theorem headerSentArmPostEnv_nil {F : ShaCompress}
    (st : Chunked.SendEk.HeaderSent spqrPolyApi (spqrAuthApi F))
    (msg : Message spqrPolyApi) :
    HeaderSentArmPostEnv st msg [] := by
  unfold HeaderSentArmPostEnv
  split
  · exact FreeOnlyEvs.nil
  · split
    · rfl
    · cases msg.payload <;>
        first | rfl | exact Or.inl (Or.inl (addChunkSlotsEnv_nil st.receiving_ct1.pts))

theorem headerSentArmPreEnv_nonempty {F : ShaCompress}
    (st : Chunked.SendEk.HeaderSent spqrPolyApi (spqrAuthApi F))
    (msg : Message spqrPolyApi) :
    ∃ evs, HeaderSentArmPreEnv st msg evs :=
  ⟨[], headerSentArmPreEnv_nil st msg⟩

theorem headerSentArmPostEnv_nonempty {F : ShaCompress}
    (st : Chunked.SendEk.HeaderSent spqrPolyApi (spqrAuthApi F))
    (msg : Message spqrPolyApi) :
    ∃ evs, HeaderSentArmPostEnv st msg evs :=
  ⟨[], headerSentArmPostEnv_nil st msg⟩

theorem headerSentArmPreEnv_sub_postEnv {F : ShaCompress}
    (st : Chunked.SendEk.HeaderSent spqrPolyApi (spqrAuthApi F))
    (msg : Message spqrPolyApi) {evs : List AllocEvent}
    (h : HeaderSentArmPreEnv st msg evs) :
    HeaderSentArmPostEnv st msg evs := by
  revert h; unfold HeaderSentArmPreEnv HeaderSentArmPostEnv
  split
  · rintro rfl; exact FreeOnlyEvs.nil
  · split
    · exact id
    · cases msg.payload <;> first | exact id | exact Or.inl

theorem seqEnv_pre_sub_assoc {E₁ E₂ E₃ : List AllocEvent → Prop} {evs : List AllocEvent}
    (h : SeqEnv E₁ E₂ evs) :
    SeqEnv E₁ (SeqEnv E₂ E₃) evs := by
  rcases h with h1 | ⟨e1, e2, rfl, h1, h2⟩
  · exact Or.inl h1
  · exact Or.inr ⟨e1, e2, rfl, h1, Or.inl h2⟩

/-! ## 2. `VmPreserved` & Budget-Pool-Threaded `<` and `eq_other` Arms (`+780 -> s0.x30`) -/

set_option maxHeartbeats 1200000 in
/-- Relocatable `.headerSent` arm when `msg.epoch < st.uc.epoch` (`+780 -> s0.x30`, Block `332`)
    parameterized by `hmemcpy_sat : HookSat (Rust.withPanics ext) spqrMemcpySym (withVmPreserved sessionMemcpySpec)`,
    establishing `VmPreserved s sf`. -/
theorem headerSent_arm_lt_sat_placed [LibsignalPlacement]
    {A : RustAlloc} {F : ShaCompress} {ext : String → Option (State → State)}
    (hmemcpy_sat : HookSat (Rust.withPanics ext) spqrMemcpySym (withVmPreserved sessionMemcpySpec))
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
  have hmemcpy : subroutine_ok (lsProg_332 (Rust.withPanics ext))
      (lsρ memcpyName) (withVmPreserved (sessionMemcpySpec 4096)) := spqr_hook_ok_of_mem hmemcpy_sat
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
  have hwb := @states_recv_writeback_59e88_sat_placed _ ext hmemcpy_sat
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
    rw [stackAt_statesRecvCallee_eq_allocHook (sp0 - 4240#64)]
    dsimp only [allocHookStack]
    refine call_memcpy_relocate_cs_stack (ret_pc := lsmpl.base 332 + 10476#64)
      hmemcpy hrel_tail (sp0 - 3664#64) (selfA + 512#64)
      rfl (by assumption) (by simp only [wp_norm, arm64_norm, hsp]) hfsp_align
      (by rw [lsmpl_base_332_eq]; simp only [Reg.lr, wp_norm, arm64_norm])
      ⟨by simp only [wp_norm, arm64_norm]; exact htr.1,
       by simp only [wp_norm, arm64_norm]; exact htr.2⟩
      (by simp only [Reg.x0, wp_norm, arm64_norm, hsp])
      (by simp only [Reg.x1, wp_norm, arm64_norm, hx1])
      (by simp only [Reg.x2, wp_norm, arm64_norm])
      (by sep_focus) ?_
    intro sf1 hpc1 hrun1 hsp1 hvm_mc hcs1 htr1; rw [lsmpl_base_332_eq] at hpc1
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
    refine seq_vm_cont (mid := lsmpl.base 332 + 18996#64) ?_; rw [lsmpl_base_332_eq]
    by_vm_steps_nest (
      wp_steps
      subst hsp0
      refine SepWP.done rfl (by assumption) ⟨by simp only [wp_norm, arm64_norm], fun hvm2 => ?_⟩
      let sp1 : SendEkSpills :=
        { b0 := ⟨w.b5.w2, w.b3.w5, w.b3.w1, w.b2.w9, w.b3.w2, w.b4.w1, w.b4.w0, w.b3.w8, w.b3.w4, w.b3.w3⟩
          b1 := ⟨w.b5.w7, w.b5.w5, w.b3.w9, w.b3.w6, w.b5.w3, w.b3.w7, sp.b1.w6, w.b5.w9, sp.b1.w8, sp.b1.w9⟩
          b2 := ⟨w.b4.w7, w.b5.w1, w.b4.w9, w.b4.w3, w.b4.w5, sp.b2.w5, w.b4.w8, 4#64, noneCap, w.b4.w2⟩
          b3 := ⟨w.b5.w8, w.w62, w.b1.w8, w.b2.w1, w.b2.w7, w.b0.w7, w.b1.w3, w.b2.w5, w.b3.w0, w.b2.w8⟩
          b4 := ⟨w.b2.w6, w.b1.w2, w.b1.w9, w.b1.w0, w.b2.w2, w.b0.w5, w.b0.w4, w.b1.w1, w.b2.w0, w.b2.w3⟩
          b5 := ⟨w.b0.w9, w.b4.w4, w.b1.w4, w.b0.w8, w.b1.w7, w.b5.w0, w.b0.w3, w.b2.w4, w.b4.w6, w.b5.w4⟩
          w60 := w.b5.w6, w61 := w.b0.w2, w62 := w.b0.w6
          q200 := sp.q200, q210 := sp.q210, q220 := sp.q220, w230 := sp.w230, q3c0 := w.q60 }
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
      · rw [stackAt_statesRecvCallee_eq_allocHook (s0.sp - 4240#64)]
        dsimp only [allocHookStack, sendEkSpillsAt, words63At, words10At, sp1]
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

theorem headerSent_arm_lt_pool_placed [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits} {F : ShaCompress}
    {ext : String → Option (State → State)}
    (hmemcpy_sat : HookSat (Rust.withPanics ext) spqrMemcpySym (withVmPreserved sessionMemcpySpec))
    (st_cost : M.σ)
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
        chunkedStatesAt A.repAlloc selfA (.headerSent st) ∗
        messageAt spqrPolyApi msgA msg ∗
        A.pool lim st_cost s ∗
        stackAt (s0.sp - 4240#64) statesRecvCalleeStackX ∗
        memRegion (s0.sp - 4240#64) 4144 ∗
        statesRecvSavedCells s0)
      (fun sf Pf =>
        VmPreserved s sf ∧
        (Pf ⊢
          P_rest ∗
          resultV1RecvAt A.repAlloc (F := F) outA (.ok { key := none, state := .headerSent st }) ∗
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
      chunkedStatesAt A.repAlloc selfA (.headerSent st) ∗
      messageAt spqrPolyApi msgA msg ∗
      A.repAlloc.pool ∗
      stackAt (s0.sp - 4240#64) statesRecvCalleeStackX ∗
      memRegion (s0.sp - 4240#64) 4144 ∗
      statesRecvSavedCells s0)
    (Entails.of_eq (by simp only [RustCliAllocBudget.repAlloc_pool, emp_sepConj, sepConj_emp]; sep_ac_rfl))
    (SepWP.mono
      (headerSent_arm_lt_sat_placed (A := A.repAlloc) hmemcpy_sat s0 s outA selfA msgA st msg
        (P_rest ∗ A.pool lim st_cost s) hlt hpc hrun hsp hsp_align hx1 hx19 hx24 htr)
      fun sf Pf _ _ ⟨hvm, hPf, hsp_sf, hcs_sf, htr_sf⟩ =>
        ⟨hvm, Entails.trans hPf (Entails.of_eq (by
          rw [← A.pool_transport lim st_cost s sf hvm]
          simp only [RustCliAllocBudget.repAlloc_pool, emp_sepConj, sepConj_emp]
          sep_ac_rfl)), hsp_sf, hcs_sf, htr_sf⟩)

set_option maxHeartbeats 1200000 in
/-- Relocatable `.headerSent` arm when `msg.epoch = st.uc.epoch` and `∀ c, msg.payload ≠ .ct1 c`
    (`+780 -> s0.x30`, Block `332`) parameterized by `hmemcpy_sat`, establishing `VmPreserved s sf`. -/
theorem headerSent_arm_eq_other_sat_placed [LibsignalPlacement]
    {A : RustAlloc} {F : ShaCompress} {ext : String → Option (State → State)}
    (hmemcpy_sat : HookSat (Rust.withPanics ext) spqrMemcpySym (withVmPreserved sessionMemcpySpec))
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
  have hmemcpy : subroutine_ok (lsProg_332 (Rust.withPanics ext))
      (lsρ memcpyName) (withVmPreserved (sessionMemcpySpec 4096)) := spqr_hook_ok_of_mem hmemcpy_sat
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
  have hwb := @states_recv_writeback_59e88_sat_placed _ ext hmemcpy_sat
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
    rw [stackAt_statesRecvCallee_eq_allocHook (sp0 - 4240#64)]
    dsimp only [allocHookStack]
    refine call_memcpy_relocate_cs_stack (ret_pc := lsmpl.base 332 + 11296#64)
      hmemcpy hrel_tail (sp0 - 3664#64) (selfA + 512#64)
      rfl (by assumption) (by simp only [wp_norm, arm64_norm, hsp]) hfsp_align
      (by rw [lsmpl_base_332_eq]; simp only [Reg.lr, wp_norm, arm64_norm])
      ⟨by simp only [wp_norm, arm64_norm]; exact htr.1,
       by simp only [wp_norm, arm64_norm]; exact htr.2⟩
      (by simp only [Reg.x0, wp_norm, arm64_norm, hsp])
      (by simp only [Reg.x1, wp_norm, arm64_norm, hx1])
      (by simp only [Reg.x2, wp_norm, arm64_norm])
      (by sep_focus) ?_
    intro sf1 hpc1 hrun1 hsp1 hvm_mc hcs1 htr1; rw [lsmpl_base_332_eq] at hpc1
    have hx19_1 : sf1.readReg64 .x19 = outA :=
      hcs1.1.trans (by simp only [Reg.x19, wp_norm, arm64_norm, hx19])
    have hx22_1 : sf1.readReg64 .x22 = w.b1.w5 :=
      hcs1.2.2.2.1.trans (by simp only [Reg.x22, wp_norm, arm64_norm])
    have hx25_1 : sf1.readReg64 .x25 = w.b0.w1 :=
      hcs1.2.2.2.2.2.2.1.trans (by simp only [Reg.x25, wp_norm, arm64_norm])
    have hx28_1 : sf1.readReg64 .x28 = w.b1.w6 :=
      hcs1.2.2.2.2.2.2.2.2.2.1.trans (by simp only [Reg.x28, wp_norm, arm64_norm])
    refine seq_vm_cont (mid := lsmpl.base 332 + 18996#64) ?_; rw [lsmpl_base_332_eq]
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
      · rw [stackAt_statesRecvCallee_eq_allocHook (s0.sp - 4240#64)]
        dsimp only [allocHookStack, sendEkSpillsAt, words63At, words10At, sp1]
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

theorem headerSent_arm_eq_other_pool_placed [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits} {F : ShaCompress}
    {ext : String → Option (State → State)}
    (hmemcpy_sat : HookSat (Rust.withPanics ext) spqrMemcpySym (withVmPreserved sessionMemcpySpec))
    (st_cost : M.σ)
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
        chunkedStatesAt A.repAlloc selfA (.headerSent st) ∗
        messageAt spqrPolyApi msgA msg ∗
        A.pool lim st_cost s ∗
        stackAt (s0.sp - 4240#64) statesRecvCalleeStackX ∗
        memRegion (s0.sp - 4240#64) 4144 ∗
        statesRecvSavedCells s0)
      (fun sf Pf =>
        VmPreserved s sf ∧
        (Pf ⊢
          P_rest ∗
          resultV1RecvAt A.repAlloc (F := F) outA (.ok { key := none, state := .headerSent st }) ∗
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
      chunkedStatesAt A.repAlloc selfA (.headerSent st) ∗
      messageAt spqrPolyApi msgA msg ∗
      A.repAlloc.pool ∗
      stackAt (s0.sp - 4240#64) statesRecvCalleeStackX ∗
      memRegion (s0.sp - 4240#64) 4144 ∗
      statesRecvSavedCells s0)
    (Entails.of_eq (by simp only [RustCliAllocBudget.repAlloc_pool, emp_sepConj, sepConj_emp]; sep_ac_rfl))
    (SepWP.mono
      (headerSent_arm_eq_other_sat_placed (A := A.repAlloc) hmemcpy_sat s0 s outA selfA msgA st msg
        (P_rest ∗ A.pool lim st_cost s) heq hct1 hpc hrun hsp hsp_align hx1 hx19 hx24 htr)
      fun sf Pf _ _ ⟨hvm, hPf, hsp_sf, hcs_sf, htr_sf⟩ =>
        ⟨hvm, Entails.trans hPf (Entails.of_eq (by
          rw [← A.pool_transport lim st_cost s sf hvm]
          simp only [RustCliAllocBudget.repAlloc_pool, emp_sepConj, sepConj_emp]
          sep_ac_rfl)), hsp_sf, hcs_sf, htr_sf⟩)

/-! ## 3. `VmPreserved` Post-Call Writeback Blocks (`+5108 -> s0.x30`) -/

set_option maxHeartbeats 1200000 in
/-- Relocatable post-call writeback block (`+5108 -> s0.x30`, Block `332`) when
    `<HeaderSent>::recv_ct1_chunk` returns `.done outSt` at `fsp + 976#64`,
    establishing `VmPreserved s sf`. -/
theorem headerSent_post_call_done_56848_sat_placed [LibsignalPlacement]
    {A : RustAlloc} {F : ShaCompress} {ext : String → Option (State → State)}
    (hmemcpy_sat : HookSat (Rust.withPanics ext) spqrMemcpySym (withVmPreserved sessionMemcpySpec))
    (s0 s : State) (outA : BitVec 64)
    (outSt : Chunked.SendEk.Ct1Received spqrPolyApi (spqrAuthApi F))
    (sp : SendEkSpills) (P_rest : SepProp)
    (hpc : s.pc = lsmpl.base 332 + 5108#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = s0.sp - 4240#64)
    (hsp_align : s0.spAligned = true)
    (hx19 : s.readReg64 .x19 = outA)
    (hx21 : s.readReg64 .x21 = (s0.sp - 4240#64) + 976#64)
    (htr : TraceCalleeSaved s s0) :
    SepWP (lsProg_332 (Rust.withPanics ext)) (s0.readReg64 .x30) s
      (P_rest ∗
        (lsLogFilterAddr ↦₆₄ 0#64) ∗
        memRegion outA v1RecvSize ∗
        stackAt (s0.sp - 4240#64) statesRecvCalleeStackX ∗
        sendEkSpillsAt (s0.sp - 4240#64) sp ∗
        memRegion ((s0.sp - 4240#64) + 576#64) 376 ∗
        headerSentRecvChunkAt A ((s0.sp - 4240#64) + 976#64) (.done outSt) ∗
        memRegion ((s0.sp - 4240#64) + 1856#64) 880 ∗
        sendEkUnusedAt (s0.sp - 4240#64) ∗
        statesRecvSavedCells s0)
      (fun sf Pf =>
        VmPreserved s sf ∧
        (Pf ⊢
          P_rest ∗
          (lsLogFilterAddr ↦₆₄ 0#64) ∗
          resultV1RecvAt A (F := F) outA (.ok { key := none, state := .ct1Received outSt }) ∗
          stackAt s0.sp statesRecvStackX) ∧
        sf.sp = s0.sp ∧
        CalleeSavedPreserved s0 sf ∧
        sf.trace = s0.trace) := by
  have hwb := @states_recv_writeback_59e88_sat_placed _ ext hmemcpy_sat
    (F_tail := fun a => memRegion a 376) (Relocatable.of_memRegion 376) s0
  rw [lsmpl_base_332_eq] at hpc hwb
  dsimp only [lsProg_332, headerSentRecvChunkAt, BitVec.ofNat_eq_ofNat] at hpc hwb ⊢
  have h984 : ((s0.sp - 4240#64) + 976#64) + 8#64 = (s0.sp - 4240#64) + 984#64 := by bv_omega
  have h1488 : ((s0.sp - 4240#64) + 976#64) + 512#64 = (s0.sp - 4240#64) + 1488#64 := by bv_omega
  rw [h984, h1488]
  refine SepWP.fold (sendEkUnusedAt_split_f10 (s0.sp - 4240#64)) (by sep_focus) ?_
  wp_pull_exists; rename_i u_f10
  refine SepWP.fold (chunkedCt1ReceivedAt_extract63 A ((s0.sp - 4240#64) + 984#64) outSt)
    (by sep_focus) ?_
  wp_pull_exists; rename_i w_out
  refine SepWP.pure_elim fun _ => ?_
  have hsp_align' : (s0.sp &&& 15#64 == 0#64) = true := hsp_align
  have hfsp_align : ((s0.sp - 4240#64) &&& 15#64 == 0#64) = true :=
    spAligned_sub s0.sp 4240#64 hsp_align (by decide)
  generalize hsp0 : s0.sp = sp0 at hsp hx21 hsp_align' hfsp_align ⊢
  refine seq_vm_cont (mid := (blkPl_332).base + 5484#64) ?_
  by_vm_steps_nest (
    wp_conv_pre =>
      dsimp only [sendEkSpillsAt, words63At, words10At, lsLogFilterAddr]
      simp only [pointsTo128_eq_pair64_recv, BitVec.add_assoc, arm64_norm]
    wp_steps 200
    refine SepWP.done (by simp only [wp_norm, arm64_norm])
      (by simp only [wp_norm, arm64_norm]; assumption)
      ⟨by simp only [wp_norm, arm64_norm], fun hvm0 => ?_⟩
    refine step_adrp_vm (rd := 8#5)
      (v := Arm64.Obj.pageOf (blkPl_332.ρ "_RNvCs4Dv7yoBiUx4_3log20MAX_LOG_LEVEL_FILTER"))
      (next_pc := (blkPl_332).base + 5488#64) hvm0 ?_ ?_
    · apply blkPC_332_pairStep_0x156c
      · rfl
      · simp only [wp_norm, arm64_norm]
      · simp only [wp_norm, arm64_norm]; assumption
    · refine seq_vm_cont (mid := lsmpl.base 332 + 18996#64) ?_; rw [lsmpl_base_332_eq]
      by_vm_steps_nest (
        wp_steps 200
        subst hsp0
        refine SepWP.done (by simp only [wp_norm, arm64_norm])
          (by simp only [wp_norm, arm64_norm]; assumption)
          ⟨by simp only [wp_norm, arm64_norm], fun hvm1 => ?_⟩
        let sp1 : SendEkSpills :=
          { b0 := ⟨sp.b0.w0, sp.b0.w1, sp.b0.w2, w_out.b2.w9, sp.b0.w4, sp.b0.w5, sp.b0.w6, sp.b0.w7, sp.b0.w8, sp.b0.w9⟩
            b1 := ⟨w_out.b5.w7, sp.b1.w1, sp.b1.w2, sp.b1.w3, w_out.b5.w3, w_out.b3.w7, w_out.b0.w0, w_out.b5.w9, w_out.b1.w5, w_out.b1.w6⟩
            b2 := ⟨w_out.b4.w7, w_out.b5.w1, w_out.b4.w9, w_out.b4.w3, sp.b2.w4, sp.b2.w5, w_out.b4.w8, 5#64, noneCap, w_out.b4.w2⟩
            b3 := ⟨w_out.b5.w8, w_out.w62, w_out.b1.w8, w_out.b2.w1, w_out.b2.w7, w_out.b0.w7, w_out.b1.w3, w_out.b2.w5, w_out.b3.w0, w_out.b2.w8⟩
            b4 := ⟨w_out.b2.w6, w_out.b1.w2, w_out.b1.w9, w_out.b1.w0, w_out.b2.w2, w_out.b0.w5, w_out.b0.w4, w_out.b1.w1, w_out.b2.w0, w_out.b2.w3⟩
            b5 := ⟨w_out.b0.w9, w_out.b4.w4, w_out.b1.w4, w_out.b0.w8, w_out.b1.w7, w_out.b5.w0, w_out.b0.w3, w_out.b2.w4, w_out.b4.w6, w_out.b5.w4⟩
            w60 := w_out.b5.w6, w61 := w_out.b0.w2, w62 := w_out.b0.w6
            q200 := sp.q200, q210 := sp.q210, q220 := sp.q220, w230 := sp.w230, q3c0 := w_out.q60 }
        have hfold_976 :
            (((s0.sp - 4240#64) + 976#64) ↦₆₄ 2#64) ∗
            words63At ((s0.sp - 4240#64) + 984#64) w_out ∗
            memRegion ((s0.sp - 4240#64) + 1488#64) 368 ⊢
              memRegion ((s0.sp - 4240#64) + 976#64) 880 := by
          have h := done_976_entails_memRegion_880 ((s0.sp - 4240#64) + 976#64) w_out
          rw [h984, h1488] at h; exact h
        have hfold_unused := sendEkUnusedAt_rejoin_f10 (s0.sp - 4240#64) w_out.q60
        have hfold_all :
            ((((s0.sp - 4240#64) + 976#64) ↦₆₄ 2#64) ∗
             words63At ((s0.sp - 4240#64) + 984#64) w_out ∗
             memRegion ((s0.sp - 4240#64) + 1488#64) 368) ∗
            (((s0.sp - 4240#64 + 3856#64) ↦₁₂₈ w_out.q60) ∗
             memRegion (s0.sp - 4240#64) 8 ∗ memRegion (s0.sp - 4240#64 + 568#64) 8 ∗
             memRegion (s0.sp - 4240#64 + 952#64) 8 ∗ memRegion (s0.sp - 4240#64 + 2736#64) 1120 ∗
             memRegion (s0.sp - 4240#64 + 3872#64) 272) ∗
            sendEkSpillsAt (s0.sp - 4240#64) sp1 ⊢
              memRegion ((s0.sp - 4240#64) + 976#64) 880 ∗
              sendEkUnusedAt (s0.sp - 4240#64) ∗
              sendEkSpillsAt (s0.sp - 4240#64) sp1 :=
          sepConj_mono hfold_976 (sepConj_mono_left hfold_unused)
        refine SepWP.fold
          (F := P_rest ∗ (lsLogFilterAddr ↦₆₄ 0#64) ∗
            relocatedHeap (fun dst => chunkedCt1ReceivedAt A dst outSt) (wordsBytes (words63List w_out)) ∗
            memRegion outA v1RecvSize ∗ stackAt (s0.sp - 4240#64) statesRecvCalleeStackX ∗
            memRegion ((s0.sp - 4240#64) + 576#64) 376 ∗ memRegion ((s0.sp - 4240#64) + 1856#64) 880 ∗
            statesRecvSavedCells s0)
          hfold_all ?_ ?_
        · dsimp only [sendEkSpillsAt, words63At, words10At, lsLogFilterAddr, sp1]
          simp only [pointsTo128_eq_pair64_recv, BitVec.add_assoc, arm64_norm]
          sep_ac_rfl
        · rw [show (memRegion ((s0.sp - 4240#64) + 976#64) 880 ∗
                sendEkUnusedAt (s0.sp - 4240#64) ∗
                sendEkSpillsAt (s0.sp - 4240#64) sp1) ∗
              (P_rest ∗ (lsLogFilterAddr ↦₆₄ 0#64) ∗
                relocatedHeap (fun dst => chunkedCt1ReceivedAt A dst outSt) (wordsBytes (words63List w_out)) ∗
                memRegion outA v1RecvSize ∗ stackAt (s0.sp - 4240#64) statesRecvCalleeStackX ∗
                memRegion ((s0.sp - 4240#64) + 576#64) 376 ∗ memRegion ((s0.sp - 4240#64) + 1856#64) 880 ∗
                statesRecvSavedCells s0) =
              (P_rest ∗ (lsLogFilterAddr ↦₆₄ 0#64) ∗
                relocatedHeap (fun dst => chunkedCt1ReceivedAt A dst outSt) (wordsBytes (words63List w_out))) ∗
              memRegion outA v1RecvSize ∗ stackAt (s0.sp - 4240#64) statesRecvCalleeStackX ∗
              sendEkSpillsAt (s0.sp - 4240#64) sp1 ∗ memRegion ((s0.sp - 4240#64) + 576#64) 376 ∗
              memRegion ((s0.sp - 4240#64) + 976#64) 880 ∗ memRegion ((s0.sp - 4240#64) + 1856#64) 880 ∗
              sendEkUnusedAt (s0.sp - 4240#64) ∗ statesRecvSavedCells s0 by sep_ac_rfl]
          refine SepWP.mono
            (hwb _ outA sp1
              (P_rest ∗ (lsLogFilterAddr ↦₆₄ 0#64) ∗
                relocatedHeap (fun dst => chunkedCt1ReceivedAt A dst outSt) (wordsBytes (words63List w_out)))
              (by simp only [wp_norm, arm64_norm])
              (by simp only [wp_norm, arm64_norm]; assumption)
              (by simp only [wp_norm, arm64_norm, hsp]) hsp_align
              (by simp only [Reg.x19, wp_norm, arm64_norm, hx19])
              ⟨by simp only [wp_norm, arm64_norm]; exact htr.1,
               by simp only [wp_norm, arm64_norm]; exact htr.2⟩)
            (fun sf Pf _ _ ⟨hvm_wb, hPf, hsp_sf, hcs_sf, htr_sf⟩ =>
              ⟨hvm1.trans hvm_wb, ?_, hsp_sf, hcs_sf, htr_sf⟩)
          refine Entails.trans hPf ?_
          have hrec := writeback_ct1Received_entails_resultV1RecvAt A (F := F) outA outSt w_out
            w_out.b5.w9 sp.q200
          refine Entails.trans (Entails.of_eq ?_)
            (sepConj_mono_right (sepConj_mono_right (sepConj_mono_left hrec)))
          dsimp only [writebackWords63, words63At, words10At, sp1, Reg.x0, Reg.x1, Reg.x2, Reg.x3, Reg.x4,
            Reg.x5, Reg.x6, Reg.x7, Reg.x8, Reg.x9, Reg.x10, Reg.x11, Reg.x12, Reg.x13, Reg.x14, Reg.x15,
            Reg.x16, Reg.x17, Reg.x20, Reg.x21, Reg.x22, Reg.x23, Reg.x24, Reg.x25, Reg.x26, Reg.x27,
            Reg.x28, Reg.x30]
          simp only [wp_norm, arm64_norm]
          sep_ac_rfl
      )
  )

set_option maxHeartbeats 1200000 in
/-- Relocatable post-call writeback block (`+5108 -> s0.x30`, Block `332`) when
    `<HeaderSent>::recv_ct1_chunk` returns `.stillReceiving outSt` at `fsp + 976#64`,
    establishing `VmPreserved s sf`. -/
theorem headerSent_post_call_still_56848_sat_placed [LibsignalPlacement]
    {A : RustAlloc} {F : ShaCompress} {ext : String → Option (State → State)}
    (hmemcpy_sat : HookSat (Rust.withPanics ext) spqrMemcpySym (withVmPreserved sessionMemcpySpec))
    (s0 s : State) (outA : BitVec 64)
    (outSt : Chunked.SendEk.HeaderSent spqrPolyApi (spqrAuthApi F))
    (sp : SendEkSpills) (P_rest : SepProp)
    (hpc : s.pc = lsmpl.base 332 + 5108#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = s0.sp - 4240#64)
    (hsp_align : s0.spAligned = true)
    (hx19 : s.readReg64 .x19 = outA)
    (hx21 : s.readReg64 .x21 = (s0.sp - 4240#64) + 976#64)
    (htr : TraceCalleeSaved s s0) :
    SepWP (lsProg_332 (Rust.withPanics ext)) (s0.readReg64 .x30) s
      (P_rest ∗
        memRegion outA v1RecvSize ∗
        stackAt (s0.sp - 4240#64) statesRecvCalleeStackX ∗
        sendEkSpillsAt (s0.sp - 4240#64) sp ∗
        memRegion ((s0.sp - 4240#64) + 576#64) 376 ∗
        headerSentRecvChunkAt A ((s0.sp - 4240#64) + 976#64) (.stillReceiving outSt) ∗
        memRegion ((s0.sp - 4240#64) + 1856#64) 880 ∗
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
  dsimp only [lsProg_332, lsρ, memcpyName, headerSentRecvChunkAt,
    BitVec.ofNat_eq_ofNat] at hpc hmemcpy ⊢
  refine SepWP.fold (chunkedHeaderSentAt_extract63_376_tag A ((s0.sp - 4240#64) + 976#64) outSt)
    (by sep_focus) ?_
  wp_pull_exists; rename_i w_out tailBytes
  refine SepWP.pure_elim fun ⟨hw0, hw62, htail_len⟩ => ?_
  have hrel_tail := Relocatable.of_pointsToBytes tailBytes htail_len
  have hwb := @states_recv_writeback_59e88_sat_placed _ ext hmemcpy_sat
    (F_tail := fun a => a ↦ₛ tailBytes) hrel_tail s0
  rw [lsmpl_base_332_eq] at hwb
  dsimp only [lsProg_332, BitVec.ofNat_eq_ofNat] at hwb
  have hsp_align' : (s0.sp &&& 15#64 == 0#64) = true := hsp_align
  have hfsp_align : ((s0.sp - 4240#64) &&& 15#64 == 0#64) = true :=
    spAligned_sub s0.sp 4240#64 hsp_align (by decide)
  have h1480 : ((s0.sp - 4240#64) + 976#64) + 504#64 = s0.sp - 2760#64 := by bv_omega
  rw [h1480]
  refine seq_vm_cont (mid := lsmpl.ρ "memcpy") ?_
  by_vm_steps_nest (
    generalize hsp0 : s0.sp = sp0 at hsp hx21 hsp_align' hfsp_align ⊢
    wp_conv_pre =>
      dsimp only [sendEkSpillsAt, words63At, words10At]
      simp only [pointsTo128_eq_pair64_recv, BitVec.add_assoc, arm64_norm]
    wp_steps 200
    refine SepWP.done rfl (by assumption) ⟨by simp only [wp_norm, arm64_norm], fun hvm1 => ?_⟩
    rw [stackAt_statesRecvCallee_eq_allocHook (sp0 - 4240#64)]
    dsimp only [allocHookStack]
    refine call_memcpy_relocate_cs_stack (ret_pc := lsmpl.base 332 + 14836#64)
      hmemcpy hrel_tail (sp0 - 3664#64) (sp0 - 2760#64)
      rfl (by assumption) (by simp only [wp_norm, arm64_norm, hsp]) hfsp_align
      (by rw [lsmpl_base_332_eq]; simp only [Reg.lr, wp_norm, arm64_norm])
      ⟨by simp only [wp_norm, arm64_norm]; exact htr.1,
       by simp only [wp_norm, arm64_norm]; exact htr.2⟩
      (by simp only [Reg.x0, wp_norm, arm64_norm, hsp])
      (by simp only [Reg.x1, wp_norm, arm64_norm, hx21])
      (by simp only [Reg.x2, wp_norm, arm64_norm])
      (by sep_focus) ?_
    intro sf1 hpc1 hrun1 hsp1 hvm_mc hcs1 htr1; rw [lsmpl_base_332_eq] at hpc1
    have hx19_1 : sf1.readReg64 .x19 = outA :=
      hcs1.1.trans (by simp only [Reg.x19, wp_norm, arm64_norm, hx19])
    have hx20_1 : sf1.readReg64 .x20 = w_out.b5.w5 :=
      hcs1.2.1.trans (by simp only [Reg.x20, wp_norm, arm64_norm])
    have hx22_1 : sf1.readReg64 .x22 = w_out.b0.w1 :=
      hcs1.2.2.2.1.trans (by simp only [Reg.x22, wp_norm, arm64_norm])
    have hx23_1 : sf1.readReg64 .x23 = w_out.b1.w8 :=
      hcs1.2.2.2.2.1.trans (by simp only [Reg.x23, wp_norm, arm64_norm])
    have hx24_1 : sf1.readReg64 .x24 = w_out.b3.w1 :=
      hcs1.2.2.2.2.2.1.trans (by simp only [Reg.x24, wp_norm, arm64_norm])
    have hx25_1 : sf1.readReg64 .x25 = w_out.b3.w4 :=
      hcs1.2.2.2.2.2.2.1.trans (by simp only [Reg.x25, wp_norm, arm64_norm])
    have hx26_1 : sf1.readReg64 .x26 = w_out.b3.w2 :=
      hcs1.2.2.2.2.2.2.2.1.trans (by simp only [Reg.x26, wp_norm, arm64_norm])
    have hx27_1 : sf1.readReg64 .x27 = w_out.b3.w3 :=
      hcs1.2.2.2.2.2.2.2.2.1.trans (by simp only [Reg.x27, wp_norm, arm64_norm])
    have hx28_1 : sf1.readReg64 .x28 = w_out.b5.w2 :=
      hcs1.2.2.2.2.2.2.2.2.2.1.trans (by simp only [Reg.x28, wp_norm, arm64_norm])
    refine seq_vm_cont (mid := lsmpl.base 332 + 18996#64) ?_; rw [lsmpl_base_332_eq]
    by_vm_steps_nest (
      wp_steps
      subst hsp0
      refine SepWP.done rfl (by assumption) ⟨by simp only [wp_norm, arm64_norm], fun hvm2 => ?_⟩
      let sp1 : SendEkSpills :=
        { b0 := ⟨sp.b0.w0, w_out.b3.w5, sp.b0.w2, w_out.b2.w9, sp.b0.w4, w_out.b4.w1, w_out.b4.w0,
                 w_out.b3.w8, sp.b0.w8, sp.b0.w9⟩
          b1 := ⟨w_out.b5.w7, sp.b1.w1, w_out.b3.w9, w_out.b3.w6, w_out.b5.w3, w_out.b3.w7, w_out.b0.w0,
                 w_out.b5.w9, w_out.b1.w5, w_out.b1.w6⟩
          b2 := ⟨w_out.b4.w7, w_out.b5.w1, w_out.b4.w9, w_out.b4.w3, w_out.b4.w5, sp.b2.w5, w_out.b4.w8,
                 4#64, noneCap, w_out.b4.w2⟩
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
      have h3664 : s0.sp - 3664#64 = (s0.sp - 4240#64) + 576#64 := by bv_omega
      have h2760 : s0.sp - 2760#64 = (s0.sp - 4240#64) + 1480#64 := by bv_omega
      rw [h3664, h2760]
      have hfold_sp1 :
          (words63At ((s0.sp - 4240#64) + 976#64) w_out ∗
           memRegion ((s0.sp - 4240#64) + 1480#64) 376) ∗
          sendEkSpillsAt (s0.sp - 4240#64) sp1 ⊢
            memRegion ((s0.sp - 4240#64) + 976#64) 880 ∗
            sendEkSpillsAt (s0.sp - 4240#64) sp1 :=
        sepConj_mono_left (words63At_376_entails_memRegion_880
          ((s0.sp - 4240#64) + 976#64) ((s0.sp - 4240#64) + 1480#64) w_out (by bv_omega))
      refine SepWP.fold
        (F := P_rest ∗
          relocatedHeap (fun dst => chunkedHeaderSentAt A dst outSt) (wordsBytes (words63List w_out) ++ tailBytes) ∗
          memRegion outA v1RecvSize ∗ stackAt (s0.sp - 4240#64) statesRecvCalleeStackX ∗
          (((s0.sp - 4240#64) + 576#64) ↦ₛ tailBytes) ∗ memRegion ((s0.sp - 4240#64) + 1856#64) 880 ∗
          sendEkUnusedAt (s0.sp - 4240#64) ∗ statesRecvSavedCells s0)
        hfold_sp1 ?_ ?_
      · rw [stackAt_statesRecvCallee_eq_allocHook (s0.sp - 4240#64)]
        dsimp only [allocHookStack, sendEkSpillsAt, words63At, words10At, sp1, Reg.x23]
        simp only [pointsTo128_eq_pair64_recv, BitVec.add_assoc, wp_norm, arm64_norm, hx23_1, hw62]
        sep_ac_rfl
      · rw [show (memRegion ((s0.sp - 4240#64) + 976#64) 880 ∗ sendEkSpillsAt (s0.sp - 4240#64) sp1) ∗
            (P_rest ∗
              relocatedHeap (fun dst => chunkedHeaderSentAt A dst outSt) (wordsBytes (words63List w_out) ++ tailBytes) ∗
              memRegion outA v1RecvSize ∗ stackAt (s0.sp - 4240#64) statesRecvCalleeStackX ∗
              (((s0.sp - 4240#64) + 576#64) ↦ₛ tailBytes) ∗ memRegion ((s0.sp - 4240#64) + 1856#64) 880 ∗
              sendEkUnusedAt (s0.sp - 4240#64) ∗ statesRecvSavedCells s0) =
            (P_rest ∗
              relocatedHeap (fun dst => chunkedHeaderSentAt A dst outSt) (wordsBytes (words63List w_out) ++ tailBytes)) ∗
            memRegion outA v1RecvSize ∗ stackAt (s0.sp - 4240#64) statesRecvCalleeStackX ∗
            sendEkSpillsAt (s0.sp - 4240#64) sp1 ∗ (((s0.sp - 4240#64) + 576#64) ↦ₛ tailBytes) ∗
            memRegion ((s0.sp - 4240#64) + 976#64) 880 ∗ memRegion ((s0.sp - 4240#64) + 1856#64) 880 ∗
            sendEkUnusedAt (s0.sp - 4240#64) ∗ statesRecvSavedCells s0 by sep_ac_rfl]
        refine SepWP.mono
          (hwb _ outA sp1
            (P_rest ∗
              relocatedHeap (fun dst => chunkedHeaderSentAt A dst outSt) (wordsBytes (words63List w_out) ++ tailBytes))
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
        dsimp only [writebackWords63, words63At, words10At, sp1, Reg.x0, Reg.x1, Reg.x2, Reg.x3, Reg.x4,
          Reg.x5, Reg.x6, Reg.x7, Reg.x8, Reg.x9, Reg.x10, Reg.x11, Reg.x12, Reg.x13, Reg.x14, Reg.x15,
          Reg.x16, Reg.x17, Reg.x20, Reg.x21, Reg.x22, Reg.x23, Reg.x24, Reg.x25, Reg.x26, Reg.x27,
          Reg.x28, Reg.x30]
        simp only [wp_norm, arm64_norm, hx20_1, hx22_1, hx23_1, hx24_1, hx25_1, hx26_1, hx27_1, hx28_1, hw62]
        sep_ac_rfl
    )
  )

/-! ## 4. Budget-Threaded `<HeaderSent>::recv_ct1_chunk` Framed Call Rule (Block `337`) -/

/-- Relocatable framed `SepWP` call rule for `headerSentRecvCt1ChunkPlacedSpecOfPrePostEnv` (Block `337`). -/
theorem call_headerSentRecvCt1Chunk_placed [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits} {F : ShaCompress}
    {CalleePre CalleePost : HeaderSentRecvCt1ChunkGhost F → List AllocEvent → Prop}
    {prog : Program} {entry ret_pc target_pc : BitVec 64}
    (hcall : subroutine_ok prog entry
      (withLsCodeRoLoaded lsmpl
        (headerSentRecvCt1ChunkPlacedSpecOfPrePostEnv M A lim F CalleePre CalleePost)))
    (outA stA chunkA : BitVec 64)
    (st : Chunked.SendEk.HeaderSent spqrPolyApi (spqrAuthApi F))
    (chunk : Chunk)
    (outRes : Chunked.SendEk.HeaderSentRecvChunk spqrPolyApi (spqrAuthApi F))
    (st_cost : M.σ)
    (hsort : PolyDecoderStrictSorted st.receiving_ct1)
    (hrecv : st.recv_ct1_chunk st.uc.epoch chunk = .ok outRes)
    (hfit : FitsEnv M lim st_cost (CalleePre ⟨outA, stA, chunkA, st, chunk, outRes⟩))
    {s0 s : State} {sp_call : BitVec 64} {P Frame : SepProp}
    {post : State → SepProp → Prop}
    (hcro : LibsignalCodeRoLoaded lsmpl s.mem)
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
    (hsplit : P = (memRegion outA chunkedHeaderSentSize ∗
      chunkedHeaderSentAt A.repAlloc stA st ∗ chunkAt chunkA chunk ∗
      tokenInitPlacedAt ∗ reduceTablePlacedAt ∗
      A.pool lim st_cost s ∗ stackAt sp_call headerSentRecvCt1ChunkStack) ∗ Frame)
    (hnext : ∀ (evs : List AllocEvent),
      CalleePost ⟨outA, stA, chunkA, st, chunk, outRes⟩ evs →
      ∀ sf : State, sf.pc = ret_pc → sf.status = .Running →
        sf.sp = sp_call → CalleeSavedPreserved s sf → TraceCalleeSaved sf s0 →
        SepWP prog target_pc sf
          ((headerSentRecvChunkAt A.repAlloc outA outRes ∗
            memRegion stA chunkedHeaderSentSize ∗ chunkAt chunkA chunk ∗
            tokenInitPlacedAt ∗ reduceTablePlacedAt ∗
            A.pool lim (M.stepEvents evs st_cost) sf ∗
            stackAt sp_call headerSentRecvCt1ChunkStack) ∗ Frame) post) :
    SepWP prog target_pc s P post := by
  have hsp_align_s : s.spAligned = true := by
    rw [State.spAligned, hsp]; exact hsp_align
  refine SepWP.call_subroutine_frame hcall
    (x := (⟨outA, stA, chunkA, st, chunk, outRes⟩, st_cost))
    (F := Frame)
    hpc hrun hsp_align_s hlr ?_ ?_ ?_ ?_ ?_
  · intro R' hm
    rw [hsplit] at hm
    dsimp only [withLsCodeRoLoaded]
    rw [sepConj_assoc, sepConj_left_comm, satisfies_pure_sepConj]
    refine ⟨hcro, ?_⟩
    dsimp only [headerSentRecvCt1ChunkPlacedSpecOfPrePostEnv]
    rw [hsp]
    simp only [sepConj_assoc, satisfies_pure_sepConj]
    exact ⟨⟨hx0, hx1, hx2, hx3, hsort, hrecv, hfit⟩,
      Satisfies.mono (Entails.of_eq (by sep_ac_rfl)) hm⟩
  · intro _ _ _ hp
    unfold withLsCodeRoLoaded headerSentRecvCt1ChunkPlacedSpecOfPrePostEnv at hp; dsimp only at hp
    exact ((satisfies_pure_sepConj _ _ _).mp hp).1
  · intro _ _ _ _ he
    unfold withLsCodeRoLoaded headerSentRecvCt1ChunkPlacedSpecOfPrePostEnv at he; dsimp only at he
    exact ((satisfies_pure_sepConj _ _ _).mp he).1
  · intro sf hpc_sf hrun_sf hsp_sf hcs_sf
    dsimp only [withLsCodeRoLoaded, headerSentRecvCt1ChunkPlacedSpecOfPrePostEnv]
    rw [hsp, sepExists_sepConj_left]
    apply ProofLib.SepWP.exists_left; intro evs
    simp only [sepConj_assoc]
    refine SepWP.pure_elim fun ⟨htr_sf, hevs⟩ => ?_
    exact SepWP.weaken_pre (Entails.of_eq (by sep_ac_rfl))
      (hnext evs hevs sf hpc_sf hrun_sf (hsp_sf.trans hsp) hcs_sf
        ⟨htr_sf.trans htrace.1, hcs_sf.2.2.2.2.2.2.2.2.2.2.2.trans htrace.2⟩)
  · intro _ _ _ ho
    unfold withLsCodeRoLoaded headerSentRecvCt1ChunkPlacedSpecOfPrePostEnv at ho; dsimp only at ho
    exact False.elim ((satisfies_pure_sepConj _ _ _).mp ho).1

end LibsignalBinary.Proofs.SpqrV1.States.Recv.ArmHeaderSent2PlacedBudgetAux
