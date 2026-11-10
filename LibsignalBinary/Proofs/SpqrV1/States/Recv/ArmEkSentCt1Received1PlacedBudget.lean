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
public meta import LibsignalBinary.Proofs.Placed.BudgetVmSteps -- shake: keep
public import LibsignalBinary.Proofs.SpqrV1.States.Recv.ArmNoHeaderReceivedStepsPlacedBudgetAux
public import LibsignalBinary.Proofs.SpqrV1.States.Recv.DefsPlaced
public import LibsignalBinary.Proofs.SpqrV1.States.Recv.DropChunkedClPlacedBudget
public import LibsignalBinary.Proofs.SpqrV1.States.Recv.SendEkCommon
public import LibsignalBinary.Proofs.SpqrV1.States.RecvCt2Chunk.DefsPlacedBudget
import LibsignalBinary.Proofs.Common.SharedHelpers
meta import LibsignalBinary.Proofs.Common.SharedHelpers -- shake: keep
import LibsignalBinary.Proofs.SpqrV1.Kdf.HkdfToSliceExtract
import LibsignalBinary.Proofs.SpqrV1.Poly.EncoderIntoPb.Defs
import LibsignalBinary.Proofs.SpqrV1.States.Recv.ArmCt1Received1
import LibsignalBinary.Proofs.SpqrV1.States.Recv.ArmCt1Received2Placed
import LibsignalBinary.Proofs.SpqrV1.States.Recv.ArmEkSentCt1Received1
import LibsignalBinary.Proofs.SpqrV1.States.Recv.ArmHeaderSent1
import LibsignalBinary.Proofs.SpqrV1.States.Recv.CodeSymFetch0Placed
import LibsignalBinary.Proofs.SpqrV1.States.Recv.CodeSymFetch1Placed
import LibsignalBinary.Proofs.SpqrV1.States.Recv.CodeSymFetch2Placed
import LibsignalBinary.Proofs.SpqrV1.States.Recv.CodeSymFetch3Placed
import LibsignalBinary.Proofs.SpqrV1.States.Recv.DispatchPlaced
import LibsignalBinary.Proofs.SpqrV1.States.Recv.SendEkCommonPlaced
import ProofLib.SepLogic.WPp

/-!
# `<States>::recv` (Block `332`) — `.ekSentCt1Received` Arm, Part 1 (Budget-Threaded)

Budget-threaded `[LibsignalPlacement]` proofs for `.ekSentCt1Received` (`+228`, Block `332`):
`FreeOnlyEvs` `>` path, `VmPreserved` `<` / `= ∧ ¬ .ct2` / post-call `.error` paths, and
framed `<EkSentCt1Received>::recv_ct2_chunk` (Block `350`) call rules.
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 400000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

namespace LibsignalBinary.Proofs.SpqrV1.States.Recv.ArmEkSentCt1Received1PlacedBudget

open Arm64 ProofLib ProofLib.ProgramReflection
open CryptoGames.LibsignalSession (ShaCompress)
open CryptoVerification (
  LibsignalCodeLoaded LibsignalPlacement blkPC_332 blkPl_332 extract_withMemEq lsProg_332 lsmpl
  lsρ withLsCodeLoaded withMemEq
)
open CryptoVerification.RustHeap (RustAlloc)
open CryptoVerification.LibsignalTripleRatchet (
  LibsignalCodeRoLoaded memcpyName sessionMemcpyRegionSpec sessionMemcpySpec withLsCodeRoLoaded
)
open CryptoVerification.LibsignalTripleRatchetRepr (noneCap)
open CryptoVerification.LibsignalSpqrV1 (Chunk Message MlKem spqrAuthApi spqrPolyApi)
open CryptoVerification.SpqrV1.Alloc (spqrMemcpySym)
open CryptoVerification.SpqrV1.GF.Mul2U16 (tokenInitPlacedAt)
open CryptoVerification.SpqrV1.GF.UnacceleratedMul (reduceTablePlacedAt)
open CryptoVerification.SpqrV1.Poly (chunkAt)
open CryptoVerification.SpqrV1.Poly.AddChunk (PolyDecoderStrictSorted)
open CryptoVerification.SpqrV1.Drop (
  chunkedEkSentCt1ReceivedAt chunkedEkSentCt1ReceivedSize chunkedStatesAt chunkedStatesSize
  dropStack32 none2Cap
)
open CryptoVerification.SpqrV1.Top.MessageSerialize (messageAt messagePayloadAt)
open CryptoVerification.SpqrV1.States.Leaves (
  Relocatable extractLsb'_0_64_append extractLsb'_64_64_append relocatedHeap wordsBytes
)
open CryptoVerification.SpqrV1.States.RecvCt2Chunk (
  RecvCt2ChunkGhost ekSentCt1ReceivedAt ekSentCt1ReceivedRecvChunkResultAt recvCt2ChunkStackX
)
open CryptoVerification.SpqrV1.States.Recv (
  SendEkSpills TraceCalleeSaved bv376_toNat_hs bv_sub_sub_recv
  chunkedEkSentCt1ReceivedAt_extract63 epoch_cmp_ct1r_bne_1_of_gt epoch_cmp_ct1r_bne_1_of_lt
  epoch_cmp_ct1r_eq_of_eq epoch_cmp_ct1r_eq_of_gt epoch_cmp_ct1r_eq_of_lt
  err4_entails_resultV1RecvAt_macVerifyFailed errMacVerifyTag8Split
  err_epochOutOfRange_entails_resultV1RecvAt err_result_976_extract err_result_976_fold_880
  memRegion_4144_entails_sendEkFrame memRegion_960_split_err4 memRegion_out_960_split_err
  messagePayloadAt_eq_tag_tail messagePayloadTag messagePayloadTag_bne_6_of_not_ct2
  messagePayloadTag_eq_6_of_not_ct2 messagePayloadTailAt pointsTo128_eq_pair64_recv
  recompose63 resultV1RecvAt self_504_416_entails_memRegion_928 sendEkFrame_entails_memRegion_4144
  sendEkSpillsAt sendEkUnusedAt sp_sub_144_add_48 sp_sub_16_add_8_recv sp_sub_32_add_8_recv
  sp_sub_4192_sub_48 sp_sub_4240_add_4096 sp_sub_4240_add_4144_hs sp_sub_4240_add_48
  sp_sub_48_add_8_recv sp_sub_64_add_8_recv sp_sub_80_add_8_recv sp_sub_96_add_16
  sp_sub_96_add_32 sp_sub_96_add_48 sp_sub_96_add_64 sp_sub_96_add_80 sp_sub_96_add_8_recv
  sp_sub_96_add_96_recv sp_sub_96_sub_4096 spqrDeallocSym stackAt_statesRecvStackX_split_dropStack32
  stack_restore_statesRecv statesRecvCalleeStackX statesRecvSavedCells statesRecvStackX
  v1RecvSize words10At words63At words63At_self_entails_memRegion_928 words63List writebackWords63
  writeback_ekSentCt1Received_entails_resultV1RecvAt
)
open LibsignalBinary.Proofs.SpqrV1.States.Recv (lsmpl_base_332_eq)
open LibsignalBinary.Heap (
  AllocCallPreserved AllocCostModel AllocEvent BudgetLimits FitsEnv FreeOnlyEvs
  RustCliAllocBudget VmPreserved rustCliDeallocBudgetSpec
)
open LibsignalBinary.Heap.SpecBudget (withVmPreserved)
open LibsignalBinary.Proofs.SpqrV1.Drop.ChunkedBudget (dropChunkedEkSentCt1ReceivedSpec)
open LibsignalBinary.Proofs.SpqrV1.States.Recv.ArmNoHeaderReceivedStepsPlacedBudgetAux (
  seq_vm_clean states_recv_epilogue_59fd0_acp_placed
  states_recv_writeback_59e88_placed states_recv_writeback_59e88_sat_placed
)
open LibsignalBinary.Proofs.SpqrV1.States.Recv.DropChunkedClPlacedBudget (
  drop_chunked_ek_sent_ct1_received_cl_on
)
open LibsignalBinary.Proofs.SpqrV1.States.RecvCt2Chunk.DefsBudget (
  RecvCt2ChunkEnv recvCt2ChunkBudgetOnPanic recvCt2ChunkPlacedSpec
  recvCt2ChunkPlacedSpecOfPrePostEnv
)
open LibsignalBinary.Proofs.Placed.ElfLsRetAddr (LsRetAddr624)

attribute [local irreducible] Program.fetch Program.externAt? Program.fnOff
  CryptoVerification.blkPC_332
attribute [-arm64_norm]
  CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.sp_sub_688_eq_hsp
  CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.sp_add_neg688_eq_hsp
  CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.sp_sub_96_eq_hsp_592
  CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.sp_add_neg96_eq_hsp_592
attribute [local arm64_norm, local wp_norm]
  bv_sub_add_lit bv_sub_sub_recv BitVec.sub_add_cancel BitVec.toNat_zero
  extractLsb'_0_64_append extractLsb'_64_64_append
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

private theorem seq_vm_cont_lscl {prog : Program} {pl : Arm64.Obj.MultiPlacement}
    {mid tgt : BitVec 64} {s : State} {Pre : SepProp} {post : State → SepProp → Prop}
    (hcl : LibsignalCodeLoaded pl s.mem)
    (h : SepWP prog mid s Pre
      (fun sm Pm => VmPreserved s sm ∧
        (LibsignalCodeLoaded pl sm.mem → VmPreserved s sm → SepWP prog tgt sm Pm post))) :
    SepWP prog tgt s Pre post :=
  SepWP.seq_frozen (fun _ _ hcl' hkf => hcl'.of_keepsFrozen hkf) hcl
    (SepWP.mono h fun _ _ _ _ ⟨hvm, hk⟩ hclm => hk hclm hvm)

private theorem subroutine_ok_withMemEq_of_withLsCodeLoaded {α : Type} {prog : Program}
    {entry : BitVec 64} {pl : Arm64.Obj.MultiPlacement} {spec : Spec α} {m : Memory}
    (h : subroutine_ok prog entry (withLsCodeLoaded pl spec))
    (hcl : LibsignalCodeLoaded pl m) :
    subroutine_ok prog entry (withMemEq m spec) :=
  subroutine_ok_mono h
    (fun _ _ _ hp => by
      obtain ⟨hm, hpre⟩ := extract_withMemEq hp
      dsimp only [withLsCodeLoaded]
      rw [sepConj_assoc, sepConj_left_comm, satisfies_pure_sepConj]
      exact ⟨hm ▸ hcl, hpre⟩)
    (fun _ _ _ _ hq => hq)

/-! ## 1. `.ekSentCt1Received` (`+228`, Block `332`): `msg.epoch > st.uc.epoch` -/

/-- Contract-parameterized budget-threaded relocatable `msg.epoch > st.uc.epoch` tail-call block
    `0x55664..0x5569c` (`+528 -> s0.x30`, Block `332`) for `.ekSentCt1Received`:
    writes `Err(EpochOutOfRange(msg.epoch))` to `outA`, restores `sp = s0.sp` and `x19..x30`,
    and tail-calls Block `278` (`dropChunkedEkSentCt1ReceivedSpec`) on `selfA + 8#64`. -/
theorem ekSentCt1Received_gt_55664_of_drop_placed [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits} {F : ShaCompress}
    {ext : String → Option (State → State)}
    (hdrop_cl : subroutine_ok (lsProg_332 (Rust.withPanics ext)) (lsmpl.base 278)
      (withLsCodeLoaded lsmpl (dropChunkedEkSentCt1ReceivedSpec M A lim F)))
    (st_cost : M.σ)
    (s0 s : State) (outA selfA : BitVec 64)
    (st : CryptoVerification.LibsignalSpqrV1.Chunked.SendEk.EkSentCt1Received spqrPolyApi (spqrAuthApi F))
    (ep : BitVec 64) (P_rest : SepProp)
    (hcl : LibsignalCodeLoaded lsmpl s.mem)
    (hpc : s.pc = lsmpl.base 332 + 528#64)
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
        (selfA ↦₆₄ 6#64) ∗
        chunkedEkSentCt1ReceivedAt A.repAlloc (selfA + 8#64) st ∗
        memRegion (selfA + 512#64) 416 ∗
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
  dsimp only [lsProg_332, chunkedEkSentCt1ReceivedSize, BitVec.ofNat_eq_ofNat] at hdrop_cl hpc ⊢
  refine seq_vm_cont_lscl hcl (mid := lsmpl.base 278) ?_
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
    have hdrop_raw := subroutine_ok_withMemEq_of_withLsCodeLoaded hdrop_cl hcl1
    dsimp only [withMemEq, dropChunkedEkSentCt1ReceivedSpec,
      chunkedEkSentCt1ReceivedSize, BitVec.ofNat_eq_ofNat] at hdrop_raw
    wp_conv_pre => rw [← A.pool_of_vmPreserved hvm1]
    have hrest := stack_restore_statesRecv s0
    unfold statesRecvSavedCells at hrest
    refine SepWP.focus_weaken hrest (by sep_focus) ?_
    have hsplit_sp := stackAt_statesRecvStackX_split_dropStack32 s0.sp
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
        (self_504_416_entails_memRegion_928 selfA 6#64))
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

/-- `HookSat`-parameterized budget-threaded relocatable `msg.epoch > st.uc.epoch` tail-call block
    `0x55664..0x5569c` (`+528 -> s0.x30`, Block `332`) for `.ekSentCt1Received`. -/
theorem ekSentCt1Received_gt_55664_placed [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits} {F : ShaCompress}
    {ext : String → Option (State → State)}
    (hdealloc : HookSat (Rust.withPanics ext) spqrDeallocSym (rustCliDeallocBudgetSpec M A lim))
    (st_cost : M.σ)
    (s0 s : State) (outA selfA : BitVec 64)
    (st : CryptoVerification.LibsignalSpqrV1.Chunked.SendEk.EkSentCt1Received spqrPolyApi (spqrAuthApi F))
    (ep : BitVec 64) (P_rest : SepProp)
    (hcl : LibsignalCodeLoaded lsmpl s.mem)
    (hpc : s.pc = lsmpl.base 332 + 528#64)
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
        (selfA ↦₆₄ 6#64) ∗
        chunkedEkSentCt1ReceivedAt A.repAlloc (selfA + 8#64) st ∗
        memRegion (selfA + 512#64) 416 ∗
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
          sf.trace = s0.trace) :=
  ekSentCt1Received_gt_55664_of_drop_placed
    (drop_chunked_ek_sent_ct1_received_cl_on (idx := 332) hdealloc)
    st_cost s0 s outA selfA st ep P_rest hcl hpc hrun hsp hsp_align hx8 hx19 hx25 htr hlr_ls

/-- Contract-parameterized budget-threaded relocatable `.ekSentCt1Received` arm when
    `msg.epoch > st.uc.epoch` (`+228 -> s0.x30`, `0x55538..0x5569c -> b 0x4c92c`, Block `332`). -/
theorem ekSentCt1Received_arm_gt_of_drop_placed [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits} {F : ShaCompress}
    {ext : String → Option (State → State)}
    (hdrop_cl : subroutine_ok (lsProg_332 (Rust.withPanics ext)) (lsmpl.base 278)
      (withLsCodeLoaded lsmpl (dropChunkedEkSentCt1ReceivedSpec M A lim F)))
    (st_cost : M.σ)
    (s0 s : State) (outA selfA msgA : BitVec 64)
    (st : CryptoVerification.LibsignalSpqrV1.Chunked.SendEk.EkSentCt1Received spqrPolyApi (spqrAuthApi F))
    (msg : Message spqrPolyApi)
    (P_rest : SepProp)
    (hgt : msg.epoch > st.uc.epoch)
    (hcl : LibsignalCodeLoaded lsmpl s.mem)
    (hpc : s.pc = lsmpl.base 332 + 228#64)
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
        chunkedStatesAt A.repAlloc selfA (.ekSentCt1Received st) ∗
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
  have htail := @ekSentCt1Received_gt_55664_of_drop_placed _ M A lim F ext hdrop_cl st_cost s0
  rw [lsmpl_base_332_eq] at hpc htail
  dsimp only [lsProg_332, chunkedStatesAt, messageAt, BitVec.ofNat_eq_ofNat] at hpc htail ⊢
  refine seq_vm_cont_lscl hcl (mid := (blkPl_332).base + 528#64) ?_
  refine SepWP.fold (memRegion_4144_entails_sendEkFrame (s0.sp - 4240#64)) (by sep_focus) ?_
  wp_pull_exists; rename_i sp
  refine SepWP.fold (chunkedEkSentCt1ReceivedAt_extract63 A.repAlloc (selfA + 8#64) st) (by sep_focus) ?_
  wp_pull_exists; rename_i w
  refine SepWP.pure_elim fun hw12 => ?_
  have hsp_align' : (s0.sp &&& 15#64 == 0#64) = true := hsp_align
  have hfsp_align : ((s0.sp - 4240#64) &&& 15#64 == 0#64) = true :=
    spAligned_sub s0.sp 4240#64 hsp_align (by decide)
  by_vm_steps_nest (
    generalize hsp0 : s0.sp = sp0 at hsp hsp_align' hfsp_align ⊢
    wp_conv_pre =>
      dsimp only [sendEkSpillsAt, words63At, words10At]
      rw [hw12]
      simp only [pointsTo128_eq_pair64_recv, BitVec.add_assoc, arm64_norm]
    wp_steps
    subst hsp0
    refine SepWP.done rfl (by assumption) ⟨by simp only [wp_norm, arm64_norm], fun hcl1 hvm1 => ?_⟩
    have hacp1 :=
      acpOfVm hvm1 (by simp only [AllocCallPreserved, wp_norm, arm64_norm])
    let sp1 : SendEkSpills :=
      { b0 := ⟨sp.b0.w0, sp.b0.w1, sp.b0.w2, w.b2.w9, sp.b0.w4, sp.b0.w5, sp.b0.w6, sp.b0.w7,
               sp.b0.w8, sp.b0.w9⟩
        b1 := ⟨w.b5.w7, w.b5.w5, sp.b1.w2, sp.b1.w3, sp.b1.w4, sp.b1.w5, w.b0.w0, w.b5.w9,
               w.b1.w5, w.b1.w6⟩
        b2 := ⟨w.b4.w7, sp.b2.w1, w.b4.w9, w.b4.w3, w.b4.w5, w.b0.w1, w.b4.w8, sp.b2.w7,
               sp.b2.w8, sp.b2.w9⟩
        b3 := ⟨w.b5.w8, w.w62, w.b1.w8, w.b2.w1, w.b2.w7, w.b0.w7, w.b1.w3, w.b2.w5,
               sp.b3.w8, w.b2.w8⟩
        b4 := ⟨w.b2.w6, st.uc.epoch, w.b1.w9, w.b1.w0, w.b2.w2, sp.b4.w5, w.b0.w4, w.b1.w1,
               w.b2.w0, w.b2.w3⟩
        b5 := ⟨w.b0.w9, w.b4.w4, w.b1.w4, w.b0.w8, w.b1.w7, sp.b5.w5, w.b0.w3, w.b2.w4,
               w.b4.w6, w.b5.w4⟩
        w60 := w.b5.w6
        w61 := w.b0.w2
        w62 := w.b0.w6
        q200 := sp.q200
        q210 := sp.q210
        q220 := sp.q220
        w230 := sp.w230
        q3c0 := sp.q3c0 }
    have hfold_frame :
        (words63At (selfA + 8#64) w ∗
         relocatedHeap (fun dst => chunkedEkSentCt1ReceivedAt A.repAlloc dst st) (wordsBytes (words63List w))) ∗
        (sendEkSpillsAt (s0.sp - 4240#64) sp1 ∗
         memRegion ((s0.sp - 4240#64) + 576#64) 376 ∗
         memRegion ((s0.sp - 4240#64) + 976#64) 880 ∗
         memRegion ((s0.sp - 4240#64) + 1856#64) 880 ∗
         sendEkUnusedAt (s0.sp - 4240#64)) ⊢
          chunkedEkSentCt1ReceivedAt A.repAlloc (selfA + 8#64) st ∗
          memRegion (s0.sp - 4240#64) 4144 :=
      sepConj_mono (recompose63 (selfA + 8#64) w)
        (sendEkFrame_entails_memRegion_4144 (s0.sp - 4240#64) sp1)
    refine SepWP.fold
      (F := P_rest ∗
        memRegion outA v1RecvSize ∗
        (selfA ↦₆₄ 6#64) ∗
        memRegion (selfA + 512#64) 416 ∗
        ((msgA ↦₆₄ msg.epoch) ∗ messagePayloadAt spqrPolyApi msgA msg.payload) ∗
        A.pool lim st_cost s ∗
        stackAt (s0.sp - 4240#64) statesRecvCalleeStackX ∗
        statesRecvSavedCells s0)
      hfold_frame
      (by
        dsimp only [sendEkSpillsAt, words63At, words10At, sp1]
        rw [hw12]
        simp only [pointsTo128_eq_pair64_recv, BitVec.add_assoc, arm64_norm]) ?_
    rw [show (chunkedEkSentCt1ReceivedAt A.repAlloc (selfA + 8#64) st ∗ memRegion (s0.sp - 4240#64) 4144) ∗
          (P_rest ∗
            memRegion outA v1RecvSize ∗
            (selfA ↦₆₄ 6#64) ∗
            memRegion (selfA + 512#64) 416 ∗
            ((msgA ↦₆₄ msg.epoch) ∗ messagePayloadAt spqrPolyApi msgA msg.payload) ∗
            A.pool lim st_cost s ∗
            stackAt (s0.sp - 4240#64) statesRecvCalleeStackX ∗
            statesRecvSavedCells s0) =
          (P_rest ∗ ((msgA ↦₆₄ msg.epoch) ∗ messagePayloadAt spqrPolyApi msgA msg.payload)) ∗
          memRegion outA v1RecvSize ∗
          (selfA ↦₆₄ 6#64) ∗
          chunkedEkSentCt1ReceivedAt A.repAlloc (selfA + 8#64) st ∗
          memRegion (selfA + 512#64) 416 ∗
          A.pool lim st_cost s ∗
          stackAt (s0.sp - 4240#64) statesRecvCalleeStackX ∗
          memRegion (s0.sp - 4240#64) 4144 ∗
          statesRecvSavedCells s0 by sep_ac_rfl]
    wp_conv_pre => rw [← A.pool_of_vmPreserved hvm1]
    refine SepWP.mono
      (htail _ outA selfA st msg.epoch
        (P_rest ∗ ((msgA ↦₆₄ msg.epoch) ∗ messagePayloadAt spqrPolyApi msgA msg.payload))
        hcl1 rfl (by assumption)
        (by simp only [wp_norm, arm64_norm]; exact hsp)
        hsp_align
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

/-- `HookSat`-parameterized budget-threaded relocatable `.ekSentCt1Received` arm when
    `msg.epoch > st.uc.epoch` (`+228 -> s0.x30`, Block `332`). -/
theorem ekSentCt1Received_arm_gt_placed [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits} {F : ShaCompress}
    {ext : String → Option (State → State)}
    (hdealloc : HookSat (Rust.withPanics ext) spqrDeallocSym (rustCliDeallocBudgetSpec M A lim))
    (st_cost : M.σ)
    (s0 s : State) (outA selfA msgA : BitVec 64)
    (st : CryptoVerification.LibsignalSpqrV1.Chunked.SendEk.EkSentCt1Received spqrPolyApi (spqrAuthApi F))
    (msg : Message spqrPolyApi)
    (P_rest : SepProp)
    (hgt : msg.epoch > st.uc.epoch)
    (hcl : LibsignalCodeLoaded lsmpl s.mem)
    (hpc : s.pc = lsmpl.base 332 + 228#64)
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
        chunkedStatesAt A.repAlloc selfA (.ekSentCt1Received st) ∗
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
          sf.trace = s0.trace) :=
  ekSentCt1Received_arm_gt_of_drop_placed
    (drop_chunked_ek_sent_ct1_received_cl_on (idx := 332) hdealloc)
    st_cost s0 s outA selfA msgA st msg P_rest hgt hcl hpc hrun hsp hsp_align hx1 hx19 hx24 htr
    hlr_ls

/-! ## 2. `.ekSentCt1Received` (`+228`, Block `332`): `msg.epoch < st.uc.epoch` -/

set_option maxHeartbeats 1200000 in
/-- `subroutine_ok`-parameterized relocatable `.ekSentCt1Received` arm when `msg.epoch < st.uc.epoch`
    (`+228 -> s0.x30`, Block `332`), establishing `VmPreserved s sf`. -/
theorem ekSentCt1Received_arm_lt_sub_placed [LibsignalPlacement]
    {A : RustAlloc} {F : ShaCompress} {ext : String → Option (State → State)}
    (hmemcpy : subroutine_ok (lsProg_332 (Rust.withPanics ext))
      (lsρ memcpyName) (withVmPreserved sessionMemcpyRegionSpec))
    (s0 s : State) (outA selfA msgA : BitVec 64)
    (st : CryptoVerification.LibsignalSpqrV1.Chunked.SendEk.EkSentCt1Received spqrPolyApi (spqrAuthApi F))
    (msg : Message spqrPolyApi)
    (P_rest : SepProp)
    (hlt : msg.epoch < st.uc.epoch)
    (hpc : s.pc = lsmpl.base 332 + 228#64)
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
        chunkedStatesAt A selfA (.ekSentCt1Received st) ∗
        messageAt spqrPolyApi msgA msg ∗
        A.pool ∗
        stackAt (s0.sp - 4240#64) statesRecvCalleeStackX ∗
        memRegion (s0.sp - 4240#64) 4144 ∗
        statesRecvSavedCells s0)
      (fun sf Pf =>
        VmPreserved s sf ∧
        (Pf ⊢
          P_rest ∗
          resultV1RecvAt A (F := F) outA (.ok { key := none, state := .ekSentCt1Received st }) ∗
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
  have hwb := @ArmNoHeaderReceivedStepsPlacedBudgetAux.states_recv_writeback_59e88_placed _ ext hmemcpy
    (F_tail := fun a => memRegion a 376) (Relocatable.of_memRegion 376) s0
  rw [lsmpl_base_332_eq] at hpc hwb
  dsimp only [lsProg_332, chunkedStatesAt, messageAt, BitVec.ofNat_eq_ofNat] at hpc hwb ⊢
  refine SepWP.fold (memRegion_4144_entails_sendEkFrame (s0.sp - 4240#64)) (by sep_focus) ?_
  wp_pull_exists; rename_i sp
  refine SepWP.fold (chunkedEkSentCt1ReceivedAt_extract63 A (selfA + 8#64) st) (by sep_focus) ?_
  wp_pull_exists; rename_i w
  refine SepWP.pure_elim fun hw12 => ?_
  have hsp_align' : (s0.sp &&& 15#64 == 0#64) = true := hsp_align
  have hfsp_align : ((s0.sp - 4240#64) &&& 15#64 == 0#64) = true :=
    spAligned_sub s0.sp 4240#64 hsp_align (by decide)
  let sp1 : SendEkSpills :=
    { b0 := ⟨sp.b0.w0, sp.b0.w1, sp.b0.w2, w.b2.w9, sp.b0.w4, sp.b0.w5, sp.b0.w6, sp.b0.w7,
             sp.b0.w8, sp.b0.w9⟩
      b1 := ⟨w.b5.w7, w.b5.w5, sp.b1.w2, sp.b1.w3, sp.b1.w4, sp.b1.w5, w.b0.w0, w.b5.w9,
             w.b1.w5, w.b1.w6⟩
      b2 := ⟨w.b4.w7, w.b5.w1, w.b4.w9, w.b4.w3, w.b4.w5, w.b0.w1, w.b4.w8, 6#64,
             noneCap, sp.b2.w9⟩
      b3 := ⟨w.b5.w8, w.w62, w.b1.w8, w.b2.w1, w.b2.w7, w.b0.w7, w.b1.w3, w.b2.w5,
             w.b3.w0, w.b2.w8⟩
      b4 := ⟨w.b2.w6, st.uc.epoch, w.b1.w9, w.b1.w0, w.b2.w2, w.b0.w5, w.b0.w4, w.b1.w1,
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
        relocatedHeap (fun dst => chunkedEkSentCt1ReceivedAt A dst st) (wordsBytes (words63List w)) ∗
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
  · have hfold_self :
        ((selfA ↦₆₄ 6#64) ∗ words63At (selfA + 8#64) w ∗ memRegion (selfA + 512#64) 416) ∗
        sendEkSpillsAt (s0.sp - 4240#64) sp1 ⊢
          memRegion selfA chunkedStatesSize ∗
          sendEkSpillsAt (s0.sp - 4240#64) sp1 :=
      sepConj_mono_left (words63At_self_entails_memRegion_928 selfA 6#64 w)
    by_vm_steps (
      generalize hsp0 : s0.sp = sp0 at hsp hsp_align' hfsp_align hfold_self ⊢
      wp_conv_pre =>
        dsimp only [sendEkSpillsAt, words63At, words10At]
        rw [hw12]
        simp only [pointsTo128_eq_pair64_recv, BitVec.add_assoc, arm64_norm]
      wp_steps 256
      subst hsp0
      refine SepWP.fold
        (F := P_rest ∗
          relocatedHeap (fun dst => chunkedEkSentCt1ReceivedAt A dst st) (wordsBytes (words63List w)) ∗
          ((msgA ↦₆₄ msg.epoch) ∗ messagePayloadAt spqrPolyApi msgA msg.payload) ∗
          A.pool ∗
          memRegion outA v1RecvSize ∗
          stackAt (s0.sp - 4240#64) statesRecvCalleeStackX ∗
          memRegion ((s0.sp - 4240#64) + 576#64) 376 ∗
          memRegion ((s0.sp - 4240#64) + 976#64) 880 ∗
          memRegion ((s0.sp - 4240#64) + 1856#64) 880 ∗
          sendEkUnusedAt (s0.sp - 4240#64) ∗
          statesRecvSavedCells s0)
        hfold_self
        (by
          dsimp only [sendEkSpillsAt, words63At, words10At, sp1]
          rw [hw12]
          simp only [pointsTo128_eq_pair64_recv, BitVec.add_assoc, arm64_norm]
          sep_ac_rfl) ?_
      refine DropChunkedClPlacedBudgetAux.align_pre_vm (by sep_ac_rfl) ?_
      rcases w with ⟨⟨_, _, _, _, _, _, _, _, _, _⟩, ⟨_, _, _, _, _, _, _, _, _, _⟩,
        ⟨_, _, _, _, _, _, _, _, _, _⟩, ⟨_, _, _, _, _, _, _, _, _, _⟩,
        ⟨_, _, _, _, _, _, _, _, _, _⟩, ⟨_, _, _, _, _, _, _, _, _, _⟩, _, _⟩
      dsimp only at hw12
      subst hw12
      dsimp only [writebackWords63, sp1, Reg.x0, Reg.x1, Reg.x2, Reg.x3, Reg.x4, Reg.x5, Reg.x6,
        Reg.x7, Reg.x8, Reg.x9, Reg.x10, Reg.x11, Reg.x12, Reg.x13, Reg.x14, Reg.x15, Reg.x16,
        Reg.x17, Reg.x19, Reg.x20, Reg.x21, Reg.x22, Reg.x23, Reg.x24, Reg.x25, Reg.x26, Reg.x27,
        Reg.x28, Reg.x30] at hx1 hx19 ⊢
      simp only [TraceCalleeSaved, hsp, hx1, hx19, htr.1, htr.2, wp_norm, arm64_norm]
      wp_done
    )
  · intro sm hpcm hrunm hvm_m ⟨hsp_m, hx19_m, htr_m, hwb_m⟩
    refine SepWP.mono
      (hwb sm outA sp1
        (P_rest ∗
          relocatedHeap (fun dst => chunkedEkSentCt1ReceivedAt A dst st) (wordsBytes (words63List w)) ∗
          memRegion selfA chunkedStatesSize ∗
          ((msgA ↦₆₄ msg.epoch) ∗ messagePayloadAt spqrPolyApi msgA msg.payload) ∗
          A.pool)
        hpcm hrunm hsp_m hsp_align hx19_m htr_m)
      (fun sf Pf _ _ ⟨hvm_wb, hPf, hsp_sf, hcs_sf, htr_sf⟩ =>
        ⟨hvm_m.trans hvm_wb, ?_, hsp_sf, hcs_sf, htr_sf⟩)
    refine Entails.trans hPf ?_
    have hrec := writeback_ekSentCt1Received_entails_resultV1RecvAt A (F := F) outA st w
      (sm.readReg64 .x20) sp.q200
    have htag : sp1.b2.w7 = 6#64 := rfl
    have hnone : sp1.b2.w8 = noneCap := rfl
    have hq200 : sp1.q200 = sp.q200 := rfl
    rw [htag, hnone, hq200, hwb_m]
    refine Entails.trans (Entails.of_eq (by sep_ac_rfl))
      (sepConj_mono_right (sepConj_mono_left hrec))

set_option maxHeartbeats 1200000 in
/-- `HookSat`-parameterized relocatable `.ekSentCt1Received` arm when `msg.epoch < st.uc.epoch`
    (`+228 -> s0.x30`, Block `332`), establishing `VmPreserved s sf`. -/
theorem ekSentCt1Received_arm_lt_placed [LibsignalPlacement]
    {A : RustAlloc} {F : ShaCompress} {ext : String → Option (State → State)}
    (hmemcpy_sat : HookSat (Rust.withPanics ext) spqrMemcpySym (withVmPreserved sessionMemcpySpec))
    (s0 s : State) (outA selfA msgA : BitVec 64)
    (st : CryptoVerification.LibsignalSpqrV1.Chunked.SendEk.EkSentCt1Received spqrPolyApi (spqrAuthApi F))
    (msg : Message spqrPolyApi)
    (P_rest : SepProp)
    (hlt : msg.epoch < st.uc.epoch)
    (hpc : s.pc = lsmpl.base 332 + 228#64)
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
        chunkedStatesAt A selfA (.ekSentCt1Received st) ∗
        messageAt spqrPolyApi msgA msg ∗
        A.pool ∗
        stackAt (s0.sp - 4240#64) statesRecvCalleeStackX ∗
        memRegion (s0.sp - 4240#64) 4144 ∗
        statesRecvSavedCells s0)
      (fun sf Pf =>
        VmPreserved s sf ∧
        (Pf ⊢
          P_rest ∗
          resultV1RecvAt A (F := F) outA (.ok { key := none, state := .ekSentCt1Received st }) ∗
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
  have hwb := @states_recv_writeback_59e88_sat_placed _ ext hmemcpy_sat
    (F_tail := fun a => memRegion a 376) (Relocatable.of_memRegion 376) s0
  rw [lsmpl_base_332_eq] at hpc hwb
  dsimp only [lsProg_332, chunkedStatesAt, messageAt, BitVec.ofNat_eq_ofNat] at hpc hwb ⊢
  refine SepWP.fold (memRegion_4144_entails_sendEkFrame (s0.sp - 4240#64)) (by sep_focus) ?_
  wp_pull_exists; rename_i sp
  refine SepWP.fold (chunkedEkSentCt1ReceivedAt_extract63 A (selfA + 8#64) st) (by sep_focus) ?_
  wp_pull_exists; rename_i w
  refine SepWP.pure_elim fun hw12 => ?_
  have hsp_align' : (s0.sp &&& 15#64 == 0#64) = true := hsp_align
  have hfsp_align : ((s0.sp - 4240#64) &&& 15#64 == 0#64) = true :=
    spAligned_sub s0.sp 4240#64 hsp_align (by decide)
  let sp1 : SendEkSpills :=
    { b0 := ⟨sp.b0.w0, sp.b0.w1, sp.b0.w2, w.b2.w9, sp.b0.w4, sp.b0.w5, sp.b0.w6, sp.b0.w7,
             sp.b0.w8, sp.b0.w9⟩
      b1 := ⟨w.b5.w7, w.b5.w5, sp.b1.w2, sp.b1.w3, sp.b1.w4, sp.b1.w5, w.b0.w0, w.b5.w9,
             w.b1.w5, w.b1.w6⟩
      b2 := ⟨w.b4.w7, w.b5.w1, w.b4.w9, w.b4.w3, w.b4.w5, w.b0.w1, w.b4.w8, 6#64,
             noneCap, sp.b2.w9⟩
      b3 := ⟨w.b5.w8, w.w62, w.b1.w8, w.b2.w1, w.b2.w7, w.b0.w7, w.b1.w3, w.b2.w5,
             w.b3.w0, w.b2.w8⟩
      b4 := ⟨w.b2.w6, st.uc.epoch, w.b1.w9, w.b1.w0, w.b2.w2, w.b0.w5, w.b0.w4, w.b1.w1,
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
        relocatedHeap (fun dst => chunkedEkSentCt1ReceivedAt A dst st) (wordsBytes (words63List w)) ∗
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
  · have hfold_self :
        ((selfA ↦₆₄ 6#64) ∗ words63At (selfA + 8#64) w ∗ memRegion (selfA + 512#64) 416) ∗
        sendEkSpillsAt (s0.sp - 4240#64) sp1 ⊢
          memRegion selfA chunkedStatesSize ∗
          sendEkSpillsAt (s0.sp - 4240#64) sp1 :=
      sepConj_mono_left (words63At_self_entails_memRegion_928 selfA 6#64 w)
    by_vm_steps (
      generalize hsp0 : s0.sp = sp0 at hsp hsp_align' hfsp_align hfold_self ⊢
      wp_conv_pre =>
        dsimp only [sendEkSpillsAt, words63At, words10At]
        rw [hw12]
        simp only [pointsTo128_eq_pair64_recv, BitVec.add_assoc, arm64_norm]
      wp_steps 256
      subst hsp0
      refine SepWP.fold
        (F := P_rest ∗
          relocatedHeap (fun dst => chunkedEkSentCt1ReceivedAt A dst st) (wordsBytes (words63List w)) ∗
          ((msgA ↦₆₄ msg.epoch) ∗ messagePayloadAt spqrPolyApi msgA msg.payload) ∗
          A.pool ∗
          memRegion outA v1RecvSize ∗
          stackAt (s0.sp - 4240#64) statesRecvCalleeStackX ∗
          memRegion ((s0.sp - 4240#64) + 576#64) 376 ∗
          memRegion ((s0.sp - 4240#64) + 976#64) 880 ∗
          memRegion ((s0.sp - 4240#64) + 1856#64) 880 ∗
          sendEkUnusedAt (s0.sp - 4240#64) ∗
          statesRecvSavedCells s0)
        hfold_self
        (by
          dsimp only [sendEkSpillsAt, words63At, words10At, sp1]
          rw [hw12]
          simp only [pointsTo128_eq_pair64_recv, BitVec.add_assoc, arm64_norm]
          sep_ac_rfl) ?_
      refine DropChunkedClPlacedBudgetAux.align_pre_vm (by sep_ac_rfl) ?_
      rcases w with ⟨⟨_, _, _, _, _, _, _, _, _, _⟩, ⟨_, _, _, _, _, _, _, _, _, _⟩,
        ⟨_, _, _, _, _, _, _, _, _, _⟩, ⟨_, _, _, _, _, _, _, _, _, _⟩,
        ⟨_, _, _, _, _, _, _, _, _, _⟩, ⟨_, _, _, _, _, _, _, _, _, _⟩, _, _⟩
      dsimp only at hw12
      subst hw12
      dsimp only [writebackWords63, sp1, Reg.x0, Reg.x1, Reg.x2, Reg.x3, Reg.x4, Reg.x5, Reg.x6,
        Reg.x7, Reg.x8, Reg.x9, Reg.x10, Reg.x11, Reg.x12, Reg.x13, Reg.x14, Reg.x15, Reg.x16,
        Reg.x17, Reg.x19, Reg.x20, Reg.x21, Reg.x22, Reg.x23, Reg.x24, Reg.x25, Reg.x26, Reg.x27,
        Reg.x28, Reg.x30] at hx1 hx19 ⊢
      simp only [TraceCalleeSaved, hsp, hx1, hx19, htr.1, htr.2, wp_norm, arm64_norm]
      wp_done
    )
  · intro sm hpcm hrunm hvm_m ⟨hsp_m, hx19_m, htr_m, hwb_m⟩
    refine SepWP.mono
      (hwb sm outA sp1
        (P_rest ∗
          relocatedHeap (fun dst => chunkedEkSentCt1ReceivedAt A dst st) (wordsBytes (words63List w)) ∗
          memRegion selfA chunkedStatesSize ∗
          ((msgA ↦₆₄ msg.epoch) ∗ messagePayloadAt spqrPolyApi msgA msg.payload) ∗
          A.pool)
        hpcm hrunm hsp_m hsp_align hx19_m htr_m)
      (fun sf Pf _ _ ⟨hvm_wb, hPf, hsp_sf, hcs_sf, htr_sf⟩ =>
        ⟨hvm_m.trans hvm_wb, ?_, hsp_sf, hcs_sf, htr_sf⟩)
    refine Entails.trans hPf ?_
    have hrec := writeback_ekSentCt1Received_entails_resultV1RecvAt A (F := F) outA st w
      (sm.readReg64 .x20) sp.q200
    have htag : sp1.b2.w7 = 6#64 := rfl
    have hnone : sp1.b2.w8 = noneCap := rfl
    have hq200 : sp1.q200 = sp.q200 := rfl
    rw [htag, hnone, hq200, hwb_m]
    refine Entails.trans (Entails.of_eq (by sep_ac_rfl))
      (sepConj_mono_right (sepConj_mono_left hrec))

theorem ekSentCt1Received_arm_lt_pool_placed [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits} {F : ShaCompress}
    {ext : String → Option (State → State)}
    (hmemcpy_sat : HookSat (Rust.withPanics ext) spqrMemcpySym (withVmPreserved sessionMemcpySpec))
    (st_cost : M.σ)
    (s0 s : State) (outA selfA msgA : BitVec 64)
    (st : CryptoVerification.LibsignalSpqrV1.Chunked.SendEk.EkSentCt1Received spqrPolyApi (spqrAuthApi F))
    (msg : Message spqrPolyApi)
    (P_rest : SepProp)
    (hlt : msg.epoch < st.uc.epoch)
    (hpc : s.pc = lsmpl.base 332 + 228#64)
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
        chunkedStatesAt A.repAlloc selfA (.ekSentCt1Received st) ∗
        messageAt spqrPolyApi msgA msg ∗
        A.pool lim st_cost s ∗
        stackAt (s0.sp - 4240#64) statesRecvCalleeStackX ∗
        memRegion (s0.sp - 4240#64) 4144 ∗
        statesRecvSavedCells s0)
      (fun sf Pf =>
        VmPreserved s sf ∧
        (Pf ⊢
          P_rest ∗
          resultV1RecvAt A.repAlloc (F := F) outA (.ok { key := none, state := .ekSentCt1Received st }) ∗
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
      chunkedStatesAt A.repAlloc selfA (.ekSentCt1Received st) ∗
      messageAt spqrPolyApi msgA msg ∗
      A.repAlloc.pool ∗
      stackAt (s0.sp - 4240#64) statesRecvCalleeStackX ∗
      memRegion (s0.sp - 4240#64) 4144 ∗
      statesRecvSavedCells s0)
    (Entails.of_eq (by simp only [RustCliAllocBudget.repAlloc_pool, emp_sepConj, sepConj_emp]; sep_ac_rfl))
    (SepWP.mono
      (ekSentCt1Received_arm_lt_placed (A := A.repAlloc) hmemcpy_sat s0 s outA selfA msgA st msg
        (P_rest ∗ A.pool lim st_cost s) hlt hpc hrun hsp hsp_align hx1 hx19 hx24 htr)
      fun sf Pf _ _ ⟨hvm, hPf, hsp_sf, hcs_sf, htr_sf⟩ =>
        ⟨hvm, Entails.trans hPf (Entails.of_eq (by
          rw [← A.pool_transport lim st_cost s sf hvm]
          simp only [RustCliAllocBudget.repAlloc_pool, emp_sepConj, sepConj_emp]
          sep_ac_rfl)), hsp_sf, hcs_sf, htr_sf⟩)

/-! ## 3. `.ekSentCt1Received` (`+228`, Block `332`): `msg.epoch = st.uc.epoch` & `msg.payload ≠ .ct2 _` -/

set_option maxHeartbeats 1200000 in
/-- `subroutine_ok`-parameterized relocatable `.ekSentCt1Received` arm when `msg.epoch = st.uc.epoch`
    and `msg.payload ≠ .ct2 _` (`+228 -> s0.x30`, Block `332`), establishing `VmPreserved s sf`. -/
theorem ekSentCt1Received_arm_eq_other_sub_placed [LibsignalPlacement]
    {A : RustAlloc} {F : ShaCompress} {ext : String → Option (State → State)}
    (hmemcpy : subroutine_ok (lsProg_332 (Rust.withPanics ext))
      (lsρ memcpyName) (withVmPreserved sessionMemcpyRegionSpec))
    (s0 s : State) (outA selfA msgA : BitVec 64)
    (st : CryptoVerification.LibsignalSpqrV1.Chunked.SendEk.EkSentCt1Received spqrPolyApi (spqrAuthApi F))
    (msg : Message spqrPolyApi)
    (P_rest : SepProp)
    (heq : msg.epoch = st.uc.epoch)
    (hct2 : ∀ c, msg.payload ≠ .ct2 c)
    (hpc : s.pc = lsmpl.base 332 + 228#64)
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
        chunkedStatesAt A selfA (.ekSentCt1Received st) ∗
        messageAt spqrPolyApi msgA msg ∗
        A.pool ∗
        stackAt (s0.sp - 4240#64) statesRecvCalleeStackX ∗
        memRegion (s0.sp - 4240#64) 4144 ∗
        statesRecvSavedCells s0)
      (fun sf Pf =>
        VmPreserved s sf ∧
        (Pf ⊢
          P_rest ∗
          resultV1RecvAt A (F := F) outA (.ok { key := none, state := .ekSentCt1Received st }) ∗
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
  have hwb := @ArmNoHeaderReceivedStepsPlacedBudgetAux.states_recv_writeback_59e88_placed _ ext hmemcpy
    (F_tail := fun a => memRegion a 376) (Relocatable.of_memRegion 376) s0
  rw [lsmpl_base_332_eq] at hpc hwb
  dsimp only [lsProg_332, chunkedStatesAt, messageAt, BitVec.ofNat_eq_ofNat] at hpc hwb ⊢
  refine SepWP.fold (memRegion_4144_entails_sendEkFrame (s0.sp - 4240#64)) (by sep_focus) ?_
  wp_pull_exists; rename_i sp
  refine SepWP.fold (chunkedEkSentCt1ReceivedAt_extract63 A (selfA + 8#64) st) (by sep_focus) ?_
  wp_pull_exists; rename_i w
  refine SepWP.pure_elim fun hw12 => ?_
  have hsp_align' : (s0.sp &&& 15#64 == 0#64) = true := hsp_align
  have hfsp_align : ((s0.sp - 4240#64) &&& 15#64 == 0#64) = true :=
    spAligned_sub s0.sp 4240#64 hsp_align (by decide)
  let sp1 : SendEkSpills :=
    { b0 := ⟨sp.b0.w0, sp.b0.w1, sp.b0.w2, w.b2.w9, sp.b0.w4, sp.b0.w5, sp.b0.w6, sp.b0.w7,
             sp.b0.w8, sp.b0.w9⟩
      b1 := ⟨w.b5.w7, w.b5.w5, sp.b1.w2, sp.b1.w3, sp.b1.w4, sp.b1.w5, w.b0.w0, w.b5.w9,
             w.b1.w5, w.b1.w6⟩
      b2 := ⟨w.b4.w7, w.b5.w1, w.b4.w9, w.b4.w3, w.b4.w5, w.b0.w1, w.b4.w8, 6#64,
             noneCap, w.b4.w2⟩
      b3 := ⟨w.b5.w8, w.w62, w.b1.w8, w.b2.w1, w.b2.w7, w.b0.w7, w.b1.w3, w.b2.w5,
             w.b3.w0, w.b2.w8⟩
      b4 := ⟨w.b2.w6, st.uc.epoch, w.b1.w9, w.b1.w0, w.b2.w2, w.b0.w5, w.b0.w4, w.b1.w1,
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
        relocatedHeap (fun dst => chunkedEkSentCt1ReceivedAt A dst st) (wordsBytes (words63List w)) ∗
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
  · have hfold_self :
        ((selfA ↦₆₄ 6#64) ∗ words63At (selfA + 8#64) w ∗ memRegion (selfA + 512#64) 416) ∗
        (((msgA + 8#64) ↦₈ messagePayloadTag msg.payload) ∗ messagePayloadTailAt msgA msg.payload) ∗
        sendEkSpillsAt (s0.sp - 4240#64) sp1 ⊢
          memRegion selfA chunkedStatesSize ∗
          messagePayloadAt spqrPolyApi msgA msg.payload ∗
          sendEkSpillsAt (s0.sp - 4240#64) sp1 :=
      sepConj_mono (words63At_self_entails_memRegion_928 selfA 6#64 w)
        (sepConj_mono_left (Entails.of_eq (messagePayloadAt_eq_tag_tail msgA msg.payload).symm))
    by_vm_steps (
      generalize hsp0 : s0.sp = sp0 at hsp hsp_align' hfsp_align hfold_self ⊢
      wp_conv_pre =>
        dsimp only [sendEkSpillsAt, words63At, words10At]
        rw [hw12, heq, messagePayloadAt_eq_tag_tail msgA msg.payload]
        simp only [pointsTo128_eq_pair64_recv, BitVec.add_assoc, arm64_norm]
      wp_steps 256
      subst hsp0
      refine SepWP.fold
        (F := P_rest ∗
          relocatedHeap (fun dst => chunkedEkSentCt1ReceivedAt A dst st) (wordsBytes (words63List w)) ∗
          (msgA ↦₆₄ msg.epoch) ∗
          A.pool ∗
          memRegion outA v1RecvSize ∗
          stackAt (s0.sp - 4240#64) statesRecvCalleeStackX ∗
          memRegion ((s0.sp - 4240#64) + 576#64) 376 ∗
          memRegion ((s0.sp - 4240#64) + 976#64) 880 ∗
          memRegion ((s0.sp - 4240#64) + 1856#64) 880 ∗
          sendEkUnusedAt (s0.sp - 4240#64) ∗
          statesRecvSavedCells s0)
        hfold_self
        (by
          dsimp only [sendEkSpillsAt, words63At, words10At, sp1]
          rw [hw12, heq]
          simp only [pointsTo128_eq_pair64_recv, BitVec.add_assoc, arm64_norm]
          sep_ac_rfl) ?_
      refine DropChunkedClPlacedBudgetAux.align_pre_vm (by sep_ac_rfl) ?_
      rcases w with ⟨⟨_, _, _, _, _, _, _, _, _, _⟩, ⟨_, _, _, _, _, _, _, _, _, _⟩,
        ⟨_, _, _, _, _, _, _, _, _, _⟩, ⟨_, _, _, _, _, _, _, _, _, _⟩,
        ⟨_, _, _, _, _, _, _, _, _, _⟩, ⟨_, _, _, _, _, _, _, _, _, _⟩, _, _⟩
      dsimp only at hw12
      subst hw12
      dsimp only [writebackWords63, sp1, Reg.x0, Reg.x1, Reg.x2, Reg.x3, Reg.x4, Reg.x5, Reg.x6,
        Reg.x7, Reg.x8, Reg.x9, Reg.x10, Reg.x11, Reg.x12, Reg.x13, Reg.x14, Reg.x15, Reg.x16,
        Reg.x17, Reg.x19, Reg.x20, Reg.x21, Reg.x22, Reg.x23, Reg.x24, Reg.x25, Reg.x26, Reg.x27,
        Reg.x28, Reg.x30] at hx1 hx19 ⊢
      simp only [TraceCalleeSaved, hsp, hx1, hx19, htr.1, htr.2, wp_norm, arm64_norm]
      wp_done
    )
  · intro sm hpcm hrunm hvm_m ⟨hsp_m, hx19_m, htr_m, hwb_m⟩
    refine SepWP.mono
      (hwb sm outA sp1
        (P_rest ∗
          relocatedHeap (fun dst => chunkedEkSentCt1ReceivedAt A dst st) (wordsBytes (words63List w)) ∗
          memRegion selfA chunkedStatesSize ∗
          ((msgA ↦₆₄ msg.epoch) ∗ messagePayloadAt spqrPolyApi msgA msg.payload) ∗
          A.pool)
        hpcm hrunm hsp_m hsp_align hx19_m htr_m)
      (fun sf Pf _ _ ⟨hvm_wb, hPf, hsp_sf, hcs_sf, htr_sf⟩ =>
        ⟨hvm_m.trans hvm_wb, ?_, hsp_sf, hcs_sf, htr_sf⟩)
    refine Entails.trans hPf ?_
    have hrec := writeback_ekSentCt1Received_entails_resultV1RecvAt A (F := F) outA st w
      (sm.readReg64 .x20) sp.q200
    have htag : sp1.b2.w7 = 6#64 := rfl
    have hnone : sp1.b2.w8 = noneCap := rfl
    have hq200 : sp1.q200 = sp.q200 := rfl
    rw [htag, hnone, hq200, hwb_m]
    refine Entails.trans (Entails.of_eq (by sep_ac_rfl))
      (sepConj_mono_right (sepConj_mono_left hrec))

set_option maxHeartbeats 1200000 in
/-- `HookSat`-parameterized relocatable `.ekSentCt1Received` arm when `msg.epoch = st.uc.epoch`
    and `msg.payload ≠ .ct2 _` (`+228 -> s0.x30`, Block `332`), establishing `VmPreserved s sf`. -/
theorem ekSentCt1Received_arm_eq_other_placed [LibsignalPlacement]
    {A : RustAlloc} {F : ShaCompress} {ext : String → Option (State → State)}
    (hmemcpy_sat : HookSat (Rust.withPanics ext) spqrMemcpySym (withVmPreserved sessionMemcpySpec))
    (s0 s : State) (outA selfA msgA : BitVec 64)
    (st : CryptoVerification.LibsignalSpqrV1.Chunked.SendEk.EkSentCt1Received spqrPolyApi (spqrAuthApi F))
    (msg : Message spqrPolyApi)
    (P_rest : SepProp)
    (heq : msg.epoch = st.uc.epoch)
    (hct2 : ∀ c, msg.payload ≠ .ct2 c)
    (hpc : s.pc = lsmpl.base 332 + 228#64)
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
        chunkedStatesAt A selfA (.ekSentCt1Received st) ∗
        messageAt spqrPolyApi msgA msg ∗
        A.pool ∗
        stackAt (s0.sp - 4240#64) statesRecvCalleeStackX ∗
        memRegion (s0.sp - 4240#64) 4144 ∗
        statesRecvSavedCells s0)
      (fun sf Pf =>
        VmPreserved s sf ∧
        (Pf ⊢
          P_rest ∗
          resultV1RecvAt A (F := F) outA (.ok { key := none, state := .ekSentCt1Received st }) ∗
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
  refine SepWP.fold (chunkedEkSentCt1ReceivedAt_extract63 A (selfA + 8#64) st) (by sep_focus) ?_
  wp_pull_exists; rename_i w
  refine SepWP.pure_elim fun hw12 => ?_
  have hsp_align' : (s0.sp &&& 15#64 == 0#64) = true := hsp_align
  have hfsp_align : ((s0.sp - 4240#64) &&& 15#64 == 0#64) = true :=
    spAligned_sub s0.sp 4240#64 hsp_align (by decide)
  let sp1 : SendEkSpills :=
    { b0 := ⟨sp.b0.w0, sp.b0.w1, sp.b0.w2, w.b2.w9, sp.b0.w4, sp.b0.w5, sp.b0.w6, sp.b0.w7,
             sp.b0.w8, sp.b0.w9⟩
      b1 := ⟨w.b5.w7, w.b5.w5, sp.b1.w2, sp.b1.w3, sp.b1.w4, sp.b1.w5, w.b0.w0, w.b5.w9,
             w.b1.w5, w.b1.w6⟩
      b2 := ⟨w.b4.w7, w.b5.w1, w.b4.w9, w.b4.w3, w.b4.w5, w.b0.w1, w.b4.w8, 6#64,
             noneCap, w.b4.w2⟩
      b3 := ⟨w.b5.w8, w.w62, w.b1.w8, w.b2.w1, w.b2.w7, w.b0.w7, w.b1.w3, w.b2.w5,
             w.b3.w0, w.b2.w8⟩
      b4 := ⟨w.b2.w6, st.uc.epoch, w.b1.w9, w.b1.w0, w.b2.w2, w.b0.w5, w.b0.w4, w.b1.w1,
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
        relocatedHeap (fun dst => chunkedEkSentCt1ReceivedAt A dst st) (wordsBytes (words63List w)) ∗
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
  · have hfold_self :
        ((selfA ↦₆₄ 6#64) ∗ words63At (selfA + 8#64) w ∗ memRegion (selfA + 512#64) 416) ∗
        (((msgA + 8#64) ↦₈ messagePayloadTag msg.payload) ∗ messagePayloadTailAt msgA msg.payload) ∗
        sendEkSpillsAt (s0.sp - 4240#64) sp1 ⊢
          memRegion selfA chunkedStatesSize ∗
          messagePayloadAt spqrPolyApi msgA msg.payload ∗
          sendEkSpillsAt (s0.sp - 4240#64) sp1 :=
      sepConj_mono (words63At_self_entails_memRegion_928 selfA 6#64 w)
        (sepConj_mono_left (Entails.of_eq (messagePayloadAt_eq_tag_tail msgA msg.payload).symm))
    by_vm_steps (
      generalize hsp0 : s0.sp = sp0 at hsp hsp_align' hfsp_align hfold_self ⊢
      wp_conv_pre =>
        dsimp only [sendEkSpillsAt, words63At, words10At]
        rw [hw12, heq, messagePayloadAt_eq_tag_tail msgA msg.payload]
        simp only [pointsTo128_eq_pair64_recv, BitVec.add_assoc, arm64_norm]
      wp_steps 256
      subst hsp0
      refine SepWP.fold
        (F := P_rest ∗
          relocatedHeap (fun dst => chunkedEkSentCt1ReceivedAt A dst st) (wordsBytes (words63List w)) ∗
          (msgA ↦₆₄ msg.epoch) ∗
          A.pool ∗
          memRegion outA v1RecvSize ∗
          stackAt (s0.sp - 4240#64) statesRecvCalleeStackX ∗
          memRegion ((s0.sp - 4240#64) + 576#64) 376 ∗
          memRegion ((s0.sp - 4240#64) + 976#64) 880 ∗
          memRegion ((s0.sp - 4240#64) + 1856#64) 880 ∗
          sendEkUnusedAt (s0.sp - 4240#64) ∗
          statesRecvSavedCells s0)
        hfold_self
        (by
          dsimp only [sendEkSpillsAt, words63At, words10At, sp1]
          rw [hw12, heq]
          simp only [pointsTo128_eq_pair64_recv, BitVec.add_assoc, arm64_norm]
          sep_ac_rfl) ?_
      refine DropChunkedClPlacedBudgetAux.align_pre_vm (by sep_ac_rfl) ?_
      rcases w with ⟨⟨_, _, _, _, _, _, _, _, _, _⟩, ⟨_, _, _, _, _, _, _, _, _, _⟩,
        ⟨_, _, _, _, _, _, _, _, _, _⟩, ⟨_, _, _, _, _, _, _, _, _, _⟩,
        ⟨_, _, _, _, _, _, _, _, _, _⟩, ⟨_, _, _, _, _, _, _, _, _, _⟩, _, _⟩
      dsimp only at hw12
      subst hw12
      dsimp only [writebackWords63, sp1, Reg.x0, Reg.x1, Reg.x2, Reg.x3, Reg.x4, Reg.x5, Reg.x6,
        Reg.x7, Reg.x8, Reg.x9, Reg.x10, Reg.x11, Reg.x12, Reg.x13, Reg.x14, Reg.x15, Reg.x16,
        Reg.x17, Reg.x19, Reg.x20, Reg.x21, Reg.x22, Reg.x23, Reg.x24, Reg.x25, Reg.x26, Reg.x27,
        Reg.x28, Reg.x30] at hx1 hx19 ⊢
      simp only [TraceCalleeSaved, hsp, hx1, hx19, htr.1, htr.2, wp_norm, arm64_norm]
      wp_done
    )
  · intro sm hpcm hrunm hvm_m ⟨hsp_m, hx19_m, htr_m, hwb_m⟩
    refine SepWP.mono
      (hwb sm outA sp1
        (P_rest ∗
          relocatedHeap (fun dst => chunkedEkSentCt1ReceivedAt A dst st) (wordsBytes (words63List w)) ∗
          memRegion selfA chunkedStatesSize ∗
          ((msgA ↦₆₄ msg.epoch) ∗ messagePayloadAt spqrPolyApi msgA msg.payload) ∗
          A.pool)
        hpcm hrunm hsp_m hsp_align hx19_m htr_m)
      (fun sf Pf _ _ ⟨hvm_wb, hPf, hsp_sf, hcs_sf, htr_sf⟩ =>
        ⟨hvm_m.trans hvm_wb, ?_, hsp_sf, hcs_sf, htr_sf⟩)
    refine Entails.trans hPf ?_
    have hrec := writeback_ekSentCt1Received_entails_resultV1RecvAt A (F := F) outA st w
      (sm.readReg64 .x20) sp.q200
    have htag : sp1.b2.w7 = 6#64 := rfl
    have hnone : sp1.b2.w8 = noneCap := rfl
    have hq200 : sp1.q200 = sp.q200 := rfl
    rw [htag, hnone, hq200, hwb_m]
    refine Entails.trans (Entails.of_eq (by sep_ac_rfl))
      (sepConj_mono_right (sepConj_mono_left hrec))

theorem ekSentCt1Received_arm_eq_other_pool_placed [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits} {F : ShaCompress}
    {ext : String → Option (State → State)}
    (hmemcpy_sat : HookSat (Rust.withPanics ext) spqrMemcpySym (withVmPreserved sessionMemcpySpec))
    (st_cost : M.σ)
    (s0 s : State) (outA selfA msgA : BitVec 64)
    (st : CryptoVerification.LibsignalSpqrV1.Chunked.SendEk.EkSentCt1Received spqrPolyApi (spqrAuthApi F))
    (msg : Message spqrPolyApi)
    (P_rest : SepProp)
    (heq : msg.epoch = st.uc.epoch)
    (hct2 : ∀ c, msg.payload ≠ .ct2 c)
    (hpc : s.pc = lsmpl.base 332 + 228#64)
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
        chunkedStatesAt A.repAlloc selfA (.ekSentCt1Received st) ∗
        messageAt spqrPolyApi msgA msg ∗
        A.pool lim st_cost s ∗
        stackAt (s0.sp - 4240#64) statesRecvCalleeStackX ∗
        memRegion (s0.sp - 4240#64) 4144 ∗
        statesRecvSavedCells s0)
      (fun sf Pf =>
        VmPreserved s sf ∧
        (Pf ⊢
          P_rest ∗
          resultV1RecvAt A.repAlloc (F := F) outA (.ok { key := none, state := .ekSentCt1Received st }) ∗
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
      chunkedStatesAt A.repAlloc selfA (.ekSentCt1Received st) ∗
      messageAt spqrPolyApi msgA msg ∗
      A.repAlloc.pool ∗
      stackAt (s0.sp - 4240#64) statesRecvCalleeStackX ∗
      memRegion (s0.sp - 4240#64) 4144 ∗
      statesRecvSavedCells s0)
    (Entails.of_eq (by simp only [RustCliAllocBudget.repAlloc_pool, emp_sepConj, sepConj_emp]; sep_ac_rfl))
    (SepWP.mono
      (ekSentCt1Received_arm_eq_other_placed (A := A.repAlloc) hmemcpy_sat s0 s outA selfA msgA st msg
        (P_rest ∗ A.pool lim st_cost s) heq hct2 hpc hrun hsp hsp_align hx1 hx19 hx24 htr)
      fun sf Pf _ _ ⟨hvm, hPf, hsp_sf, hcs_sf, htr_sf⟩ =>
        ⟨hvm, Entails.trans hPf (Entails.of_eq (by
          rw [← A.pool_transport lim st_cost s sf hvm]
          simp only [RustCliAllocBudget.repAlloc_pool, emp_sepConj, sepConj_emp]
          sep_ac_rfl)), hsp_sf, hcs_sf, htr_sf⟩)

/-! ## 4. Post-Call `.error (.err .macVerifyFailed)` Path (`+4384 -> s0.x30`) and Call Rules -/

/-- Relocatable post-call block `0x56574..0x565a4 -> 0x59fd0..0x59ff0` (`+4384 -> s0.x30`, Block `332`)
    when `recv_ct2_chunk` returns `.error (.err .macVerifyFailed)`, without `LibsignalCodeLoaded`,
    establishing `VmPreserved s sf` and `AllocCallPreserved s sf`. -/
theorem ekSentCt1Received_post_call_err_56574_placed [LibsignalPlacement]
    {A : RustAlloc} {F : ShaCompress} {ext : String → Option (State → State)}
    (s0 s : State) (outA : BitVec 64)
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
          (.error (.err .macVerifyFailed)) ∗
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
          resultV1RecvAt A (F := F) outA (.error (.err .macVerifyFailed)) ∗
          stackAt s0.sp statesRecvStackX) ∧
        sf.sp = s0.sp ∧
        AllocCallPreserved s sf ∧
        CalleeSavedPreserved s0 sf ∧
        sf.trace = s0.trace) := by
  have hep := @states_recv_epilogue_59fd0_acp_placed _ ext s0
  rw [lsmpl_base_332_eq] at hpc hep
  dsimp only [lsProg_332, BitVec.ofNat_eq_ofNat] at hpc hep ⊢
  refine SepWP.fold (err_result_976_extract A (F := F) (s0.sp - 4240#64)) (by sep_focus) ?_
  wp_pull_exists; rename_i w1 w2 w3
  refine SepWP.fold (memRegion_960_split_err4 outA) (by sep_focus) ?_
  wp_pull_exists; rename_i v0 v8 v16 v24
  have hsp_align' : (s0.sp &&& 15#64 == 0#64) = true := hsp_align
  have hfsp_align : ((s0.sp - 4240#64) &&& 15#64 == 0#64) = true :=
    spAligned_sub s0.sp 4240#64 hsp_align (by decide)
  let sp_err : SendEkSpills := { sp with w61 := w3 }
  refine seq_vm_clean (mid := (blkPl_332).base + 19324#64)
    (P_mid :=
      (P_rest ∗ resultV1RecvAt A (F := F) outA (.error (.err .macVerifyFailed))) ∗
      stackAt (s0.sp - 4240#64) statesRecvCalleeStackX ∗
      memRegion (s0.sp - 4240#64) 4144 ∗
      statesRecvSavedCells s0)
    (Q := fun sm =>
      AllocCallPreserved s sm ∧
      sm.sp = s0.sp - 4240#64 ∧
      TraceCalleeSaved sm s0)
    ?_ ?_
  · subst hx19
    have h880_976 := err_result_976_fold_880 (s0.sp - 4240#64) w1 w2 w3
    have h880_1856 :
        memRegion ((s0.sp - 4240#64) + 1856#64) 504 ∗
        memRegion ((s0.sp - 4240#64) + 2360#64) 376 ⊢
          memRegion ((s0.sp - 4240#64) + 1856#64) 880 := by
      rw [ProofLib.memRegion_split' (b := (s0.sp - 4240#64) + 1856#64) (n := 504) (k := 376)
        (b' := (s0.sp - 4240#64) + 2360#64) rfl (by bv_omega) (by decide)]
      exact Entails.refl _
    have hout := err4_entails_resultV1RecvAt_macVerifyFailed A (F := F) (s.readReg64 .x19) w1 w2 w3
    have hfold_all :
        (((s.readReg64 .x19) ↦₆₄ noneCap) ∗ (((s.readReg64 .x19) + 8#64) ↦₆₄ w1) ∗
         errMacVerifyTag8Split.heap (unpack64 w1) ∗
         (((s.readReg64 .x19) + 16#64) ↦₆₄ w2) ∗ (((s.readReg64 .x19) + 24#64) ↦₆₄ w3) ∗
         memRegion ((s.readReg64 .x19) + 32#64) 928) ∗
        (sendEkSpillsAt (s0.sp - 4240#64) sp_err ∗
         memRegion ((s0.sp - 4240#64) + 576#64) 376 ∗
         (((s0.sp - 4240#64 + 976#64) ↦₆₄ none2Cap) ∗
          ((s0.sp - 4240#64 + 984#64) ↦₆₄ w1) ∗
          ((s0.sp - 4240#64 + 992#64) ↦₆₄ w2) ∗
          ((s0.sp - 4240#64 + 1000#64) ↦₆₄ w3) ∗
          memRegion ((s0.sp - 4240#64) + 1008#64) 472 ∗
          memRegion ((s0.sp - 4240#64) + 1480#64) 376) ∗
         (memRegion ((s0.sp - 4240#64) + 1856#64) 504 ∗
          memRegion ((s0.sp - 4240#64) + 2360#64) 376) ∗
         sendEkUnusedAt (s0.sp - 4240#64)) ⊢
          resultV1RecvAt A (F := F) (s.readReg64 .x19) (.error (.err .macVerifyFailed)) ∗
          memRegion (s0.sp - 4240#64) 4144 :=
      sepConj_mono hout
        (Entails.trans
          (sepConj_mono_right (sepConj_mono_right (sepConj_mono h880_976 (sepConj_mono_left h880_1856))))
          (sendEkFrame_entails_memRegion_4144 (s0.sp - 4240#64) sp_err))
    by_vm_steps (
      generalize hsp0 : s0.sp = sp0 at hsp hsp_align' hfsp_align h880_976 h880_1856 hfold_all ⊢
      wp_conv_pre =>
        dsimp only [sendEkSpillsAt, none2Cap, Reg.x19]
        simp only [BitVec.add_assoc, arm64_norm]
      wp_steps
      subst hsp0
      refine SepWP.fold
        (F := P_rest ∗
          stackAt (s0.sp - 4240#64) statesRecvCalleeStackX ∗
          statesRecvSavedCells s0)
        hfold_all
        (by
          dsimp only [sendEkSpillsAt, sp_err, none2Cap, noneCap, Reg.x19]
          simp only [BitVec.add_assoc, arm64_norm]
          sep_ac_rfl) ?_
      refine DropChunkedClPlacedBudgetAux.align_pre_vm (by sep_ac_rfl) ?_
      simp only [AllocCallPreserved, TraceCalleeSaved, hsp, htr.1, htr.2, wp_norm, arm64_norm]
      wp_done
    )
  · intro sm hpcm hrunm hvm_m ⟨hacp_m, hsp_m, htr_m⟩
    refine SepWP.mono
      (hep sm (P_rest ∗ resultV1RecvAt A (F := F) outA (.error (.err .macVerifyFailed)))
        hpcm hrunm hsp_m hsp_align htr_m)
      (fun sf Pf _ _ ⟨hvm_ep, hPf, hsp_sf, hacp_ep, hcs_sf, htr_sf⟩ =>
        ⟨hvm_m.trans hvm_ep, Entails.trans hPf (Entails.of_eq (by sep_ac_rfl)),
         hsp_sf, hacp_m.trans hacp_ep, hcs_sf, htr_sf⟩)

theorem ekSentCt1Received_post_call_err_56574_pool_placed [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits} {F : ShaCompress}
    {ext : String → Option (State → State)}
    (st_cost : M.σ)
    (s0 s : State) (outA : BitVec 64)
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
          (.error (.err .macVerifyFailed)) ∗
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
          resultV1RecvAt A.repAlloc (F := F) outA (.error (.err .macVerifyFailed)) ∗
          A.pool lim st_cost sf ∗
          stackAt s0.sp statesRecvStackX) ∧
        sf.sp = s0.sp ∧
        AllocCallPreserved s sf ∧
        CalleeSavedPreserved s0 sf ∧
        sf.trace = s0.trace) := by
  refine SepWP.weaken_pre
    (Entails.of_eq (show _ =
      (P_rest ∗ A.pool lim st_cost s) ∗
      memRegion outA v1RecvSize ∗
      ekSentCt1ReceivedRecvChunkResultAt A.repAlloc (F := F) ((s0.sp - 4240#64) + 976#64)
        (.error (.err .macVerifyFailed)) ∗
      memRegion ((s0.sp - 4240#64) + 1480#64) 376 ∗
      memRegion ((s0.sp - 4240#64) + 1856#64) 504 ∗
      memRegion ((s0.sp - 4240#64) + 2360#64) 376 ∗
      stackAt (s0.sp - 4240#64) statesRecvCalleeStackX ∗
      sendEkSpillsAt (s0.sp - 4240#64) sp ∗
      memRegion ((s0.sp - 4240#64) + 576#64) 376 ∗
      sendEkUnusedAt (s0.sp - 4240#64) ∗
      statesRecvSavedCells s0 by sep_ac_rfl))
    (SepWP.mono
      (ekSentCt1Received_post_call_err_56574_placed (A := A.repAlloc) s0 s outA sp
        (P_rest ∗ A.pool lim st_cost s) hpc hrun hsp hsp_align hx19 htr)
      fun sf Pf _ _ ⟨hvm, hPf, hsp_sf, hacp_sf, hcs_sf, htr_sf⟩ =>
        ⟨hvm, Entails.trans hPf (Entails.of_eq (by
          rw [← A.pool_transport lim st_cost s sf hvm]
          sep_ac_rfl)), hsp_sf, hacp_sf, hcs_sf, htr_sf⟩)

/-- Envelope-parametric relocatable framed call rule for
    `withLsCodeRoLoaded lsmpl (recvCt2ChunkPlacedSpecOfPrePostEnv K F M A lim CalleePre CalleePost)`
    (Block `350`). -/
theorem call_ekSentCt1ReceivedRecvCt2Chunk_ofPrePostEnv_placed [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {F : ShaCompress} {K : MlKem}
    {CalleePre CalleePost : RecvCt2ChunkGhost F → List AllocEvent → Prop}
    {prog : Program} {entry ret_pc : BitVec 64}
    (hcall : subroutine_ok prog entry
      (withLsCodeRoLoaded lsmpl
        (recvCt2ChunkPlacedSpecOfPrePostEnv K F M A lim CalleePre CalleePost)))
    (outA stA chunkA : BitVec 64)
    (st : CryptoVerification.LibsignalSpqrV1.Chunked.SendEk.EkSentCt1Received spqrPolyApi (spqrAuthApi F))
    (chunk : Chunk)
    (st_cost : M.σ)
    (hsort : PolyDecoderStrictSorted st.receiving_ct2)
    (hroot : st.uc.auth.rootKey.length + 32 < 2 ^ 63)
    (hfit : FitsEnv M lim st_cost (CalleePre ⟨outA, stA, st, st.uc.epoch, chunkA, chunk⟩))
    {s0 s : State} {sp_call : BitVec 64} {P Frame R : SepProp}
    {post Q_panic : State → SepProp → Prop}
    {oom : State → SepProp}
    (hcro_s : LibsignalCodeRoLoaded lsmpl s.mem)
    (hpc : s.pc = entry)
    (hrun : s.status = .Running)
    (hsp : s.sp = sp_call)
    (hsp_align : (sp_call &&& 15#64 == 0#64) = true)
    (hlr : s.readReg64 Reg.lr = ret_pc)
    (htrace : TraceCalleeSaved s s0)
    (hx0 : s.readReg64 Reg.x0 = outA)
    (hx1 : s.readReg64 Reg.x1 = stA)
    (hx2 : s.readReg64 Reg.x2 = st.uc.epoch)
    (hx3 : s.readReg64 Reg.x3 = chunkA)
    (hsplit : P = (memRegion outA chunkedEkSentCt1ReceivedSize ∗
      ekSentCt1ReceivedAt A.repAlloc stA st ∗ chunkAt chunkA chunk ∗
      tokenInitPlacedAt ∗ reduceTablePlacedAt ∗
      A.pool lim st_cost s ∗ stackAt sp_call recvCt2ChunkStackX) ∗ Frame)
    (hpanic : ∀ sf P_f,
      ((sf.mem ⊨ P_f ∗ R) →
        (sf.mem ⊨ (⌜(st.recv_ct2_chunk K st.uc.epoch chunk).isPanic = true ∧
            s0.trace <+: sf.trace⌝ ∗ anyHeap) ∗ R)) →
      Q_panic sf P_f)
    (hnext : ∀ (evs : List AllocEvent),
      CalleePost ⟨outA, stA, st, st.uc.epoch, chunkA, chunk⟩ evs →
      ∀ sf : State, sf.pc = ret_pc → sf.status = .Running →
        sf.sp = sp_call → CalleeSavedPreserved s sf → TraceCalleeSaved sf s0 →
        SepWP prog (s0.readReg64 Reg.lr) sf
          ((ekSentCt1ReceivedRecvChunkResultAt A.repAlloc (F := F) outA
              (st.recv_ct2_chunk K st.uc.epoch chunk) ∗
            memRegion stA chunkedEkSentCt1ReceivedSize ∗ chunkAt chunkA chunk ∗
            tokenInitPlacedAt ∗ reduceTablePlacedAt ∗
            A.pool lim (M.stepEvents evs st_cost) sf ∗ stackAt sp_call recvCt2ChunkStackX) ∗
           Frame) post oom) :
    SepWP prog entry s P
      (fun sm Pm =>
        SepWPp prog (s0.readReg64 Reg.lr) sm Pm post Q_panic oom) oom := by
  apply SepWP.done hpc hrun
  refine SepWPp.call hcall (x := (⟨outA, stA, st, st.uc.epoch, chunkA, chunk⟩, st_cost)) (F := Frame)
    hpc hrun (by rw [State.spAligned, hsp]; exact hsp_align) hlr ?_
    (fun _ _ _ _ hex => (not_satisfies_false_sepConj hex).elim)
    (fun sf _ => hpanic sf _ fun hmem => ?_)
    (fun sf hpc_sf hrun_sf hsp_sf hcs_sf => ?_)
    (fun _ _ _ hoom => (not_satisfies_false_sepConj hoom).elim)
  · intro R' hm
    rw [hsplit] at hm
    dsimp only [withLsCodeRoLoaded]
    rw [sepConj_assoc, sepConj_left_comm, satisfies_pure_sepConj]
    refine ⟨hcro_s, ?_⟩
    dsimp only [recvCt2ChunkPlacedSpecOfPrePostEnv]
    rw [hsp]
    simp only [sepConj_assoc] at hm ⊢
    rw [satisfies_pure_sepConj]
    exact ⟨⟨hx0, hx1, hx2, hx3, hsort, hroot, hfit⟩, hm⟩
  · dsimp only [withLsCodeRoLoaded, recvCt2ChunkPlacedSpecOfPrePostEnv,
      recvCt2ChunkBudgetOnPanic] at hmem
    exact allowPanic_frame (fun ⟨hisPanic, htr_sub⟩ => ⟨hisPanic, htrace.1 ▸ htr_sub⟩) hmem
  · dsimp only [withLsCodeRoLoaded, recvCt2ChunkPlacedSpecOfPrePostEnv]
    rw [hsp, sepExists_sepConj_left]
    apply SepWPp.exists_elim; intro evs
    simp only [sepConj_assoc]
    refine SepWPp.pure_elim fun ⟨htr, hevs⟩ => ?_
    apply SepWPp.of_sepWP_ret
    exact SepWP.weaken_pre (Entails.of_eq (by sep_ac_rfl))
      (hnext evs hevs sf hpc_sf hrun_sf (hsp_sf.trans hsp) hcs_sf
        ⟨htr.trans htrace.1, hcs_sf.2.2.2.2.2.2.2.2.2.2.2.trans htrace.2⟩)

/-- Canonical relocatable framed call rule for
    `withLsCodeRoLoaded lsmpl (recvCt2ChunkPlacedSpec K F M A lim)` (Block `350`). -/
theorem call_ekSentCt1ReceivedRecvCt2Chunk_placed [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {F : ShaCompress} {K : MlKem}
    {prog : Program} {entry ret_pc : BitVec 64}
    (hcall : subroutine_ok prog entry
      (withLsCodeRoLoaded lsmpl (recvCt2ChunkPlacedSpec K F M A lim)))
    (outA stA chunkA : BitVec 64)
    (st : CryptoVerification.LibsignalSpqrV1.Chunked.SendEk.EkSentCt1Received spqrPolyApi (spqrAuthApi F))
    (chunk : Chunk)
    (st_cost : M.σ)
    (hsort : PolyDecoderStrictSorted st.receiving_ct2)
    (hroot : st.uc.auth.rootKey.length + 32 < 2 ^ 63)
    (hfit : FitsEnv M lim st_cost (RecvCt2ChunkEnv ⟨outA, stA, st, st.uc.epoch, chunkA, chunk⟩))
    {s0 s : State} {sp_call : BitVec 64} {P Frame R : SepProp}
    {post Q_panic : State → SepProp → Prop}
    {oom : State → SepProp}
    (hcro_s : LibsignalCodeRoLoaded lsmpl s.mem)
    (hpc : s.pc = entry)
    (hrun : s.status = .Running)
    (hsp : s.sp = sp_call)
    (hsp_align : (sp_call &&& 15#64 == 0#64) = true)
    (hlr : s.readReg64 Reg.lr = ret_pc)
    (htrace : TraceCalleeSaved s s0)
    (hx0 : s.readReg64 Reg.x0 = outA)
    (hx1 : s.readReg64 Reg.x1 = stA)
    (hx2 : s.readReg64 Reg.x2 = st.uc.epoch)
    (hx3 : s.readReg64 Reg.x3 = chunkA)
    (hsplit : P = (memRegion outA chunkedEkSentCt1ReceivedSize ∗
      ekSentCt1ReceivedAt A.repAlloc stA st ∗ chunkAt chunkA chunk ∗
      tokenInitPlacedAt ∗ reduceTablePlacedAt ∗
      A.pool lim st_cost s ∗ stackAt sp_call recvCt2ChunkStackX) ∗ Frame)
    (hpanic : ∀ sf P_f,
      ((sf.mem ⊨ P_f ∗ R) →
        (sf.mem ⊨ (⌜(st.recv_ct2_chunk K st.uc.epoch chunk).isPanic = true ∧
            s0.trace <+: sf.trace⌝ ∗ anyHeap) ∗ R)) →
      Q_panic sf P_f)
    (hnext : ∀ (evs : List AllocEvent),
      RecvCt2ChunkEnv ⟨outA, stA, st, st.uc.epoch, chunkA, chunk⟩ evs →
      ∀ sf : State, sf.pc = ret_pc → sf.status = .Running →
        sf.sp = sp_call → CalleeSavedPreserved s sf → TraceCalleeSaved sf s0 →
        SepWP prog (s0.readReg64 Reg.lr) sf
          ((ekSentCt1ReceivedRecvChunkResultAt A.repAlloc (F := F) outA
              (st.recv_ct2_chunk K st.uc.epoch chunk) ∗
            memRegion stA chunkedEkSentCt1ReceivedSize ∗ chunkAt chunkA chunk ∗
            tokenInitPlacedAt ∗ reduceTablePlacedAt ∗
            A.pool lim (M.stepEvents evs st_cost) sf ∗ stackAt sp_call recvCt2ChunkStackX) ∗
           Frame) post oom) :
    SepWP prog entry s P
      (fun sm Pm =>
        SepWPp prog (s0.readReg64 Reg.lr) sm Pm post Q_panic oom) oom :=
  call_ekSentCt1ReceivedRecvCt2Chunk_ofPrePostEnv_placed hcall outA stA chunkA st chunk st_cost
    hsort hroot hfit hcro_s hpc hrun hsp hsp_align hlr htrace hx0 hx1 hx2 hx3 hsplit hpanic hnext

end LibsignalBinary.Proofs.SpqrV1.States.Recv.ArmEkSentCt1Received1PlacedBudget
