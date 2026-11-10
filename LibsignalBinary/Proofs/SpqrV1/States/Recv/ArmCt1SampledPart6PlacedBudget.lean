/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Heap.IfaceBudgetLemmas
public import LibsignalBinary.Heap.SpecBudget
public import LibsignalBinary.Proofs.Placed.BudgetVmSteps
public meta import LibsignalBinary.Proofs.Placed.BudgetVmSteps -- shake: keep
public import LibsignalBinary.Proofs.SpqrV1.States.Leaves.Batch2DefsPlacedBudget
public import LibsignalBinary.Proofs.SpqrV1.States.Recv.ArmCt1SampledPart3PlacedBudget
public import LibsignalBinary.Proofs.SpqrV1.States.Recv.ArmCt1SampledPart6Placed
public import LibsignalBinary.Proofs.SpqrV1.States.Recv.ArmNoHeaderReceivedStepsPlacedBudgetAux
public import LibsignalBinary.Proofs.SpqrV1.States.Recv.DropChunkedClPlacedBudget
public import LibsignalBinary.Proofs.SpqrV1.Unchunked.SendCt2PlacedBudget
import LibsignalBinary.Proofs.Common.SharedHelpers
meta import LibsignalBinary.Proofs.Common.SharedHelpers -- shake: keep
import LibsignalBinary.Proofs.SpqrV1.States.FromPb.Defs
import LibsignalBinary.Proofs.SpqrV1.States.Leaves.RecvCt2Chunk.Common
import LibsignalBinary.Proofs.SpqrV1.States.Leaves.SendChunk1
import LibsignalBinary.Proofs.SpqrV1.States.Recv.ArmCt1SampledPart1
import LibsignalBinary.Proofs.SpqrV1.States.Recv.ArmCt1SampledPart1Placed
import LibsignalBinary.Proofs.SpqrV1.States.Recv.ArmCt1SampledPart3
import LibsignalBinary.Proofs.SpqrV1.States.Recv.CodeSymFetch3Placed
import LibsignalBinary.Proofs.SpqrV1.States.Recv.CodeSymFetch4Placed
import LibsignalBinary.Proofs.SpqrV1.States.Recv.CodeSymFetch5Placed
import LibsignalBinary.Proofs.SpqrV1.States.Recv.DispatchPlacedBudget
import LibsignalBinary.Proofs.TripleRatchet.Getters.GettersCodeSym
import ProofLib.SepLogic.WP.Apply
import ProofLib.SepLogic.WP.FrameAuto
import ProofLib.SepLogic.WPp

/-!
# `<States>::recv` (Block `332`) — `.ct1Sampled` Arm, Part 6 (Budget-Threaded)

Budget-threaded `[LibsignalPlacement]` proofs for Path 5c (`outMsg = some decoded`,
`recv_ek = .ok uc_ek`, `ack = true`) and epilogue convergence (`+16596 -> +18996`).
-/

@[expose] public section

set_option autoImplicit false

namespace LibsignalBinary.Proofs.SpqrV1.States.Recv.ArmCt1SampledPart6PlacedBudget

open Arm64 ProofLib ProofLib.ProgramReflection
open scoped CryptoVerification.RustHeap CryptoVerification.LibsignalTripleRatchet
open CryptoGames.LibsignalSession (ShaCompress)
open CryptoVerification (
  LibsignalCodeLoaded LibsignalPlacement
  blkPC_332 blkPC_332_pairStep_0x443c blkPl_332 blkPl_347 blkPl_382
  libsignalSessionCode lsLogFilterAddr lsProg_332 lsmpl lsρ withLsCodeLoaded withMemEq
)
open CryptoVerification.RustHeap (allocHookStack)
open CryptoVerification.LibsignalTripleRatchet (sessionMemcpySpec)
open CryptoVerification.LibsignalTripleRatchetRepr (noneCap)
open CryptoVerification.LibsignalSpqrV1 (
  Bytes GF16 Mac MlKem NUM_POLYS PolyEncoder Pt spqrAuthApi spqrPolyApi
)
open CryptoVerification.LibsignalSpqrV1.Chunked.SendCt (send_ct2_encoder)
open CryptoVerification.LibsignalSpqrV1.Unchunked.SendCt (Ct1SentEkReceived Ct2Sent)
open CryptoVerification.SpqrV1.Alloc (spqrMemcpySym spqr_hook_ok_of_mem)
open CryptoVerification.SpqrV1.Drop (
  dropGluePoly16Stack unchunkedCt1SentEkReceivedAt unchunkedCt2SentAt
  vecCapPtrDealloc vecGF16ListOf vecPtListOf
)
open CryptoVerification.SpqrV1.Poly (polyArrayBytes polyEncoderAt)
open CryptoVerification.SpqrV1.Unchunked (unchunkedSendCt2PlacedRoAt)
open CryptoVerification.SpqrV1.States.Leaves (
  AuthWords SendCt2EncoderGhost UnchunkedSendCt2Ghost
  authWordsList cells_7_unfold ct2SentWordsList
  relocatedHeap sendCt2EncoderStack
  slice_and_tail_entails_vecCapPtrDealloc unchunkedCt2SentAt_extract unchunkedSendCt2Stack
  vecU8Tail vecU8_entails_slice_and_tail vecWordsList
  wordsAt wordsAt_6 wordsAt_7 wordsAt_16 wordsAt_entails_memRegion wordsBytes
)
open CryptoVerification.SpqrV1.States.Recv (
  CopyScratchStack EpilogueStoreStack TraceCalleeSaved Words5 Words16 Words50
  copyFullScratch copyFullScratchCt2 copyScratchStackAt
  epilogueRegsEqSplit928 epilogueStackOfSplit928 epilogueStoreStackPart1At epilogueStoreStackPart2At
  mid376At mid376At_eq_pointsToBytes mid376Bytes mid376Bytes_length mkSplit928Ct2Sampled
  sp_sub_144_add_48 sp_sub_4192_sub_48 sp_sub_4240_add_3272 sp_sub_4240_add_3856
  sp_sub_4240_add_4096 sp_sub_4240_add_4144 sp_sub_4240_add_48
  sp_sub_96_add_16 sp_sub_96_add_32 sp_sub_96_add_48 sp_sub_96_add_64
  sp_sub_96_add_80 sp_sub_96_sub_4096 spqrRustDeallocSym
  stackAt_statesRecvCallee_eq_allocHook' stackAt_statesRecvCallee_eq_dropGluePoly16'
  stackAt_statesRecvCallee_eq_sendCt2Encoder' stackAt_statesRecvCallee_eq_unchunkedSendCt2'
  statesRecvCalleeStackX statesRecvRoPlacedAt words50At wordsAt_5
)
open LibsignalBinary.Proofs.SpqrV1.States.Recv (spqrDeallocSym)
open LibsignalBinary.Heap (
  AllocCallPreserved AllocCostModel AllocEvent BudgetLimits FitsEnv FreeOnlyEvs
  RustCliAllocBudget VmPreserved rustCliDeallocBudgetSpec
)
open LibsignalBinary.Heap.SpecBudget (withVmPreserved)
open LibsignalBinary.Proofs.SpqrV1.States.Leaves.Batch2DefsPlacedBudget (
  SendCt2EncoderBytesPreEnv SendCt2EncoderPostEnv SendCt2EncoderPreEnv
  sendCt2EncoderSpec sendCt2EncoderSpecOfPrePostEnv
)
open LibsignalBinary.Proofs.SpqrV1.States.Recv.ArmCt1SampledPart3PlacedBudget (
  call_sendCt2Encoder_statesRecv_placed_ofPrePostEnv call_sendCt2_statesRecv_placed_ofPrePostEnv
)
open LibsignalBinary.Proofs.SpqrV1.States.Recv.ArmNoHeaderReceivedStepsPlacedBudgetAux (
  seq_vm_cont step_adrp_vm
)
open LibsignalBinary.Proofs.SpqrV1.States.Recv.DispatchPlacedBudget (lsmpl_base_332_eq)
open LibsignalBinary.Proofs.SpqrV1.Unchunked.SendCt2PlacedBudget (
  UnchunkedSendCt2PostEnv UnchunkedSendCt2PreEnv
  unchunkedCt1SentEkReceivedSendCt2PlacedSpec
  unchunkedCt1SentEkReceivedSendCt2PlacedSpecOfPrePostEnv
)

set_option maxRecDepth 400000
set_option maxHeartbeats 400000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

set_option allowUnsafeReducibility true in
attribute [local reducible] spqrPolyApi spqrAuthApi
attribute [local irreducible] libsignalSessionCode Program.fetch Program.externAt? Program.fnOff
  CryptoVerification.blkPC_332
attribute [local arm64_norm, local wp_norm]
  bv_sub_add_lit BitVec.toNat_zero
  sp_sub_96_add_16 sp_sub_96_add_32 sp_sub_96_add_48 sp_sub_96_add_64 sp_sub_96_add_80
  sp_sub_96_sub_4096 sp_sub_4192_sub_48 sp_sub_4240_add_48 sp_sub_4240_add_4096 sp_sub_144_add_48
  sp_sub_4240_add_4144 sp_sub_4240_add_3856 sp_sub_4240_add_3272 lsmpl_base_332_eq
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
      else if sub.eqv e2 then some e2
      else if sub.eqv e1 then some e2
      else none
    g.assign prf2

private theorem seq_vm_cont_lscl {prog : Program} {pl : Arm64.Obj.MultiPlacement}
    {mid tgt : BitVec 64} {s : State} {Pre : SepProp} {post : State → SepProp → Prop}
    (hcl : LibsignalCodeLoaded pl s.mem)
    (h : SepWP prog mid s Pre
      (fun sm Pm => VmPreserved s sm ∧
        (LibsignalCodeLoaded pl sm.mem → VmPreserved s sm → SepWP prog tgt sm Pm post))) :
    SepWP prog tgt s Pre post :=
  SepWP.seq_frozen (fun _ _ hcl' hkf => hcl'.of_keepsFrozen hkf) hcl
    (SepWP.mono h fun _ _ _ _ ⟨hvm, hk⟩ hclm => hk hclm hvm)

/-! ## 1. `Split928` Assembly and Reconstruction for `States.ct2Sampled` (Path 5c) -/

set_option maxHeartbeats 1200000 in
theorem ct1Sampled_send_ct2_mid_step_placed [LibsignalPlacement]
    {ext : String → Option (State → State)} (s_in : State) (fsp : BitVec 64)
    (g_uc : AuthWords) (epoch ct2Cap ct2Ptr ct2Len macCap macPtr macLen : BitVec 64) (Rest : SepProp)
    (hfsp_align : (fsp &&& 15#64 == 0#64) = true)
    (hpc : s_in.pc = (blkPl_332).base + 11636#64) (hrun : s_in.status = .Running) (hsp : s_in.sp = fsp)
    (hx21 : s_in.readReg64 .x21 = fsp + 3856#64) (hx29 : s_in.readReg64 .x29 = fsp + 4144#64) :
    SepWP (lsProg_332 (Rust.withPanics ext)) ((blkPl_382).base) s_in
      (wordsAt (fsp + 3992#64) (ct2SentWordsList g_uc epoch) ∗
        ((fsp + 4048#64) ↦₆₄ ct2Cap) ∗ ((fsp + 4056#64) ↦₆₄ ct2Ptr) ∗
        ((fsp + 4064#64) ↦₆₄ ct2Len) ∗ ((fsp + 4072#64) ↦₆₄ macCap) ∗
        ((fsp + 4080#64) ↦₆₄ macPtr) ∗ ((fsp + 4088#64) ↦₆₄ macLen) ∗
        memRegion (fsp + 2256#64) 56 ∗ Rest)
      (fun sf Pf =>
        VmPreserved s_in sf ∧
        (Pf ⊢ memRegion (fsp + 3992#64) 104 ∗ wordsAt (fsp + 2256#64) (ct2SentWordsList g_uc epoch) ∗ Rest) ∧
        sf.sp = fsp ∧ sf.readReg64 .x0 = fsp + 1856#64 ∧ sf.readReg64 .x1 = ct2Ptr ∧
        sf.readReg64 .x2 = ct2Len ∧ sf.readReg64 .x3 = macPtr ∧ sf.readReg64 .x4 = macLen ∧
        sf.readReg64 .x19 = s_in.readReg64 .x19 ∧ sf.readReg64 .x20 = macCap ∧
        sf.readReg64 .x21 = fsp + 3856#64 ∧ sf.readReg64 .x24 = s_in.readReg64 .x24 ∧
        sf.readReg64 .x25 = ct2Cap ∧ sf.readReg64 .x26 = ct2Ptr ∧ sf.readReg64 .x27 = macPtr ∧
        sf.readReg64 .x28 = s_in.readReg64 .x28 ∧ sf.readReg64 .x29 = fsp + 4144#64 ∧
        sf.readReg64 .x30 = (blkPl_332).base + 11696#64 ∧ TraceCalleeSaved sf s_in) := by
  subst hsp
  have hpre :
      wordsAt (s_in.sp + 3992#64) (ct2SentWordsList g_uc epoch) ∗
        ((s_in.sp + 4048#64) ↦₆₄ ct2Cap) ∗ ((s_in.sp + 4056#64) ↦₆₄ ct2Ptr) ∗
        ((s_in.sp + 4064#64) ↦₆₄ ct2Len) ∗ ((s_in.sp + 4072#64) ↦₆₄ macCap) ∗
        ((s_in.sp + 4080#64) ↦₆₄ macPtr) ∗ ((s_in.sp + 4088#64) ↦₆₄ macLen) ∗
        memRegion (s_in.sp + 2256#64) 56 ∗ Rest ⊢
      ∃∗ v0, ∃∗ v1, ∃∗ v2, ∃∗ v3, ∃∗ v4, ∃∗ v5, ∃∗ v6,
        wordsAt (s_in.sp + 3992#64) (ct2SentWordsList g_uc epoch) ∗
        ((s_in.sp + 4048#64) ↦₆₄ ct2Cap) ∗ ((s_in.sp + 4056#64) ↦₆₄ ct2Ptr) ∗
        ((s_in.sp + 4064#64) ↦₆₄ ct2Len) ∗ ((s_in.sp + 4072#64) ↦₆₄ macCap) ∗
        ((s_in.sp + 4080#64) ↦₆₄ macPtr) ∗ ((s_in.sp + 4088#64) ↦₆₄ macLen) ∗
        (((s_in.sp + 2256#64) ↦₆₄ v0) ∗ ((s_in.sp + 2264#64) ↦₆₄ v1) ∗
          ((s_in.sp + 2272#64) ↦₆₄ v2) ∗ ((s_in.sp + 2280#64) ↦₆₄ v3) ∗
          ((s_in.sp + 2288#64) ↦₆₄ v4) ∗ ((s_in.sp + 2296#64) ↦₆₄ v5) ∗
          ((s_in.sp + 2304#64) ↦₆₄ v6)) ∗ Rest := by
    refine Entails.trans (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
      (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
        (sepConj_mono_left (cells_7_unfold (s_in.sp + 2256#64)))))))))) ?_
    simp only [wordsAt_7, BitVec.add_assoc, BitVec.reduceAdd,
      sepExists_sepConj_left, sepExists_sepConj_right]
    apply Entails.sepExists_elim; intro v0; apply Entails.sepExists_elim; intro v1
    apply Entails.sepExists_elim; intro v2; apply Entails.sepExists_elim; intro v3
    apply Entails.sepExists_elim; intro v4; apply Entails.sepExists_elim; intro v5
    apply Entails.sepExists_elim; intro v6
    exact Entails.sepExists_right v0 (Entails.sepExists_right v1 (Entails.sepExists_right v2
      (Entails.sepExists_right v3 (Entails.sepExists_right v4 (Entails.sepExists_right v5
        (Entails.sepExists_right v6 (Entails.of_eq (by sep_ac_rfl))))))))
  refine SepWP.weaken_pre hpre ?_
  apply ProofLib.SepWP.exists_left; intro v0; apply ProofLib.SepWP.exists_left; intro v1
  apply ProofLib.SepWP.exists_left; intro v2; apply ProofLib.SepWP.exists_left; intro v3
  apply ProofLib.SepWP.exists_left; intro v4; apply ProofLib.SepWP.exists_left; intro v5
  apply ProofLib.SepWP.exists_left; intro v6
  refine SepWP.mono (post := fun sf Pf =>
      VmPreserved s_in sf ∧
      (Pf ⊢ (wordsAt (s_in.sp + 3992#64) (ct2SentWordsList g_uc epoch) ∗
          wordsAt (s_in.sp + 4048#64) [ct2Cap, ct2Ptr, ct2Len, macCap, macPtr, macLen]) ∗
        wordsAt (s_in.sp + 2256#64) (ct2SentWordsList g_uc epoch) ∗ Rest) ∧
      sf.sp = s_in.sp ∧ sf.readReg64 .x0 = s_in.sp + 1856#64 ∧ sf.readReg64 .x1 = ct2Ptr ∧
      sf.readReg64 .x2 = ct2Len ∧ sf.readReg64 .x3 = macPtr ∧ sf.readReg64 .x4 = macLen ∧
      sf.readReg64 .x19 = s_in.readReg64 .x19 ∧ sf.readReg64 .x20 = macCap ∧
      sf.readReg64 .x21 = s_in.sp + 3856#64 ∧ sf.readReg64 .x24 = s_in.readReg64 .x24 ∧
      sf.readReg64 .x25 = ct2Cap ∧ sf.readReg64 .x26 = ct2Ptr ∧ sf.readReg64 .x27 = macPtr ∧
      sf.readReg64 .x28 = s_in.readReg64 .x28 ∧ sf.readReg64 .x29 = s_in.sp + 4144#64 ∧
      sf.readReg64 .x30 = (blkPl_332).base + 11696#64 ∧ TraceCalleeSaved sf s_in) ?_
    (fun sf Pf _ _ ⟨hvm, hPf, hrest⟩ => ⟨hvm, Entails.trans hPf ?_, hrest⟩)
  · dsimp only [lsProg_332, BitVec.ofNat_eq_ofNat] at hpc ⊢
    dsimp only [ct2SentWordsList, authWordsList, vecWordsList]
    simp only [List.cons_append, List.nil_append,
      wordsAt_7, wordsAt_6, BitVec.add_assoc, BitVec.reduceAdd, hx21, hx29]
    by_vm_steps_nest (
      wp_steps
      dsimp only [TraceCalleeSaved, Reg.x0, Reg.x1, Reg.x2, Reg.x3, Reg.x4,
        Reg.x19, Reg.x20, Reg.x21, Reg.x24, Reg.x25, Reg.x26, Reg.x27, Reg.x28, Reg.x29, Reg.x30]
      wp_done
    )
  · have h56 := wordsAt_entails_memRegion (ct2SentWordsList g_uc epoch) (s_in.sp + 3992#64) 56 rfl
    have h48 := wordsAt_entails_memRegion [ct2Cap, ct2Ptr, ct2Len, macCap, macPtr, macLen]
      (s_in.sp + 4048#64) 48 rfl
    have h104 : wordsAt (s_in.sp + 3992#64) (ct2SentWordsList g_uc epoch) ∗
        wordsAt (s_in.sp + 4048#64) [ct2Cap, ct2Ptr, ct2Len, macCap, macPtr, macLen] ⊢
        memRegion (s_in.sp + 3992#64) 104 := by
      refine Entails.trans (sepConj_mono h56 h48) ?_
      rw [← ProofLib.memRegion_split' (b := s_in.sp + 3992#64) (n := 56) (k := 48)
            (b' := s_in.sp + 4048#64) rfl (by bv_omega) (by decide)]
      exact Entails.refl _
    exact sepConj_mono_left h104

theorem ct1Sampled_send_ct2_mid_step_pool_placed [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {ext : String → Option (State → State)} (st_cost : M.σ) (s_in : State) (fsp : BitVec 64)
    (g_uc : AuthWords) (epoch ct2Cap ct2Ptr ct2Len macCap macPtr macLen : BitVec 64) (Rest : SepProp)
    (hfsp_align : (fsp &&& 15#64 == 0#64) = true)
    (hpc : s_in.pc = (blkPl_332).base + 11636#64) (hrun : s_in.status = .Running) (hsp : s_in.sp = fsp)
    (hx21 : s_in.readReg64 .x21 = fsp + 3856#64) (hx29 : s_in.readReg64 .x29 = fsp + 4144#64) :
    SepWP (lsProg_332 (Rust.withPanics ext)) ((blkPl_382).base) s_in
      (wordsAt (fsp + 3992#64) (ct2SentWordsList g_uc epoch) ∗
        ((fsp + 4048#64) ↦₆₄ ct2Cap) ∗ ((fsp + 4056#64) ↦₆₄ ct2Ptr) ∗
        ((fsp + 4064#64) ↦₆₄ ct2Len) ∗ ((fsp + 4072#64) ↦₆₄ macCap) ∗
        ((fsp + 4080#64) ↦₆₄ macPtr) ∗ ((fsp + 4088#64) ↦₆₄ macLen) ∗
        memRegion (fsp + 2256#64) 56 ∗ A.pool lim st_cost s_in ∗ Rest)
      (fun sf Pf =>
        VmPreserved s_in sf ∧
        (Pf ⊢ memRegion (fsp + 3992#64) 104 ∗ wordsAt (fsp + 2256#64) (ct2SentWordsList g_uc epoch) ∗
          A.pool lim st_cost sf ∗ Rest) ∧
        sf.sp = fsp ∧ sf.readReg64 .x0 = fsp + 1856#64 ∧ sf.readReg64 .x1 = ct2Ptr ∧
        sf.readReg64 .x2 = ct2Len ∧ sf.readReg64 .x3 = macPtr ∧ sf.readReg64 .x4 = macLen ∧
        sf.readReg64 .x19 = s_in.readReg64 .x19 ∧ sf.readReg64 .x20 = macCap ∧
        sf.readReg64 .x21 = fsp + 3856#64 ∧ sf.readReg64 .x24 = s_in.readReg64 .x24 ∧
        sf.readReg64 .x25 = ct2Cap ∧ sf.readReg64 .x26 = ct2Ptr ∧ sf.readReg64 .x27 = macPtr ∧
        sf.readReg64 .x28 = s_in.readReg64 .x28 ∧ sf.readReg64 .x29 = fsp + 4144#64 ∧
        sf.readReg64 .x30 = (blkPl_332).base + 11696#64 ∧ TraceCalleeSaved sf s_in) :=
  SepWP.mono
    (ct1Sampled_send_ct2_mid_step_placed s_in fsp g_uc epoch
      ct2Cap ct2Ptr ct2Len macCap macPtr macLen (A.pool lim st_cost s_in ∗ Rest)
      hfsp_align hpc hrun hsp hx21 hx29)
    fun sf _ _ _ ⟨hvm, hPf, hq⟩ =>
      ⟨hvm, Entails.trans hPf (Entails.of_eq (by rw [A.pool_transport lim st_cost s_in sf hvm])), hq⟩

set_option maxHeartbeats 1200000 in
theorem ct1Sampled_send_ct2_and_encode_step_placed_ofPrePostEnv [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits} {F : ShaCompress} {K : MlKem}
    {ScPre ScPost : UnchunkedSendCt2Ghost F → List AllocEvent → Prop}
    {EncPre EncPost : SendCt2EncoderGhost → List AllocEvent → Prop}
    {ext : String → Option (State → State)}
    (hsendCt2 : subroutine_ok (lsProg_332 (Rust.withPanics ext)) (lsmpl.base 347)
      (withLsCodeLoaded lsmpl
        (unchunkedCt1SentEkReceivedSendCt2PlacedSpecOfPrePostEnv M A lim F K ScPre ScPost)))
    (hsendCt2Enc : subroutine_ok (lsProg_332 (Rust.withPanics ext)) (lsmpl.base 382)
      (withLsCodeLoaded lsmpl (sendCt2EncoderSpecOfPrePostEnv M A lim EncPre EncPost)))
    (st_cost : M.σ) (s0 s_in : State) (fsp : BitVec 64)
    (uc_ek : Ct1SentEkReceived (spqrAuthApi F)) (outUc : Ct2Sent (spqrAuthApi F))
    (ct2 : Bytes) (mac : Mac) (outEnc : PolyEncoder)
    (hsc : uc_ek.send_ct2 K = .ok (outUc, ct2, mac))
    (henc : send_ct2_encoder spqrPolyApi ct2 mac = .ok outEnc)
    (hfits_sc : FitsEnv M lim st_cost (ScPre ⟨fsp + 3992#64, fsp + 3856#64, uc_ek, outUc, ct2, mac⟩))
    (hfits_enc : ∀ (evsSc : List AllocEvent) (ct2Ptr macPtr : BitVec 64),
      ScPost ⟨fsp + 3992#64, fsp + 3856#64, uc_ek, outUc, ct2, mac⟩ evsSc →
      ct2Ptr ≠ 0#64 → macPtr ≠ 0#64 →
      FitsEnv M lim (M.stepEvents evsSc st_cost)
        (EncPre ⟨fsp + 1856#64, ct2Ptr, ct2, macPtr, mac, outEnc⟩))
    (Rest : SepProp) (hcl : LibsignalCodeLoaded lsmpl s_in.mem)
    (hfsp_align : (fsp &&& 15#64 == 0#64) = true)
    (hpc : s_in.pc = (blkPl_332).base + 11624#64) (hrun : s_in.status = .Running)
    (hsp : s_in.sp = fsp) (htr : TraceCalleeSaved s_in s0)
    (hx21 : s_in.readReg64 .x21 = fsp + 3856#64) (hx29 : s_in.readReg64 .x29 = fsp + 4144#64) :
    SepWP (lsProg_332 (Rust.withPanics ext)) ((blkPl_332).base + 11696#64) s_in
      ((memRegion (fsp + 1856#64) 400 ∗ memRegion (fsp + 2256#64) 56 ∗
        unchunkedCt1SentEkReceivedAt A.repAlloc (fsp + 3856#64) uc_ek ∗
        memRegion (fsp + 3992#64) 104 ∗ unchunkedSendCt2PlacedRoAt ∗
        A.pool lim st_cost s_in ∗ stackAt fsp statesRecvCalleeStackX) ∗ Rest)
      (fun sf Pf =>
        ∃ (evsSc evsEnc : List AllocEvent) (g_uc : AuthWords) (ct2Cap ct2Ptr macCap macPtr : BitVec 64),
          (Pf ⊢ (polyEncoderAt A.repAlloc (fsp + 1856#64) outEnc ∗
            wordsAt (fsp + 2256#64) (ct2SentWordsList g_uc outUc.epoch) ∗
            relocatedHeap (fun dst => unchunkedCt2SentAt A.repAlloc dst outUc)
              (wordsBytes (ct2SentWordsList g_uc outUc.epoch)) ∗
            vecCapPtrDealloc A.repAlloc ct2Cap ct2Ptr ∗ vecCapPtrDealloc A.repAlloc macCap macPtr ∗
            memRegion (fsp + 3856#64) 128 ∗ memRegion (fsp + 3992#64) 104 ∗
            unchunkedSendCt2PlacedRoAt ∗ A.pool lim (M.stepEvents (evsSc ++ evsEnc) st_cost) sf ∗
            stackAt fsp statesRecvCalleeStackX) ∗ Rest) ∧
          sf.sp = fsp ∧ sf.readReg64 .x19 = s_in.readReg64 .x19 ∧ sf.readReg64 .x20 = macCap ∧
          sf.readReg64 .x21 = fsp + 3856#64 ∧ sf.readReg64 .x24 = s_in.readReg64 .x24 ∧
          sf.readReg64 .x25 = ct2Cap ∧ sf.readReg64 .x26 = ct2Ptr ∧
          sf.readReg64 .x27 = macPtr ∧ sf.readReg64 .x28 = s_in.readReg64 .x28 ∧
          sf.readReg64 .x29 = fsp + 4144#64 ∧ TraceCalleeSaved sf s0 ∧ LibsignalCodeLoaded lsmpl sf.mem ∧
          ScPost ⟨fsp + 3992#64, fsp + 3856#64, uc_ek, outUc, ct2, mac⟩ evsSc ∧
          EncPost ⟨fsp + 1856#64, ct2Ptr, ct2, macPtr, mac, outEnc⟩ evsEnc) := by
  subst hsp
  have hsc_raw : subroutine_ok (lsProg_332 (Rust.withPanics ext)) ((blkPl_347).base)
      (withLsCodeLoaded lsmpl
        (unchunkedCt1SentEkReceivedSendCt2PlacedSpecOfPrePostEnv M A lim F K ScPre ScPost)) := hsendCt2
  have henc_raw : subroutine_ok (lsProg_332 (Rust.withPanics ext)) ((blkPl_382).base)
      (withLsCodeLoaded lsmpl (sendCt2EncoderSpecOfPrePostEnv M A lim EncPre EncPost)) := hsendCt2Enc
  have hsplit_sc := stackAt_statesRecvCallee_eq_unchunkedSendCt2' s_in.sp
  have hsplit_enc := stackAt_statesRecvCallee_eq_sendCt2Encoder' s_in.sp
  have hmid_lem := @ct1Sampled_send_ct2_mid_step_placed _ ext
  dsimp only [lsProg_332, BitVec.ofNat_eq_ofNat] at hpc hsc_raw henc_raw hsplit_sc hsplit_enc hmid_lem ⊢
  rw [hsplit_sc]; wp_steps
  refine call_sendCt2_statesRecv_placed_ofPrePostEnv hsc_raw st_cost
    (s_in.sp + 3992#64) (s_in.sp + 3856#64) uc_ek outUc ct2 mac hsc hfits_sc
    (s0 := s0) (s_pool := s_in) (ret_pc := (blkPl_332).base + 11636#64) (sp_call := s_in.sp)
    (by simpa only [State.mem, arm64_norm] using hcl)
    (by simp only [State.pc, arm64_norm]; rfl) (by simpa only [arm64_norm] using hrun)
    (by simp only [State.sp, arm64_norm]) hfsp_align
    (by simp only [Reg.lr, arm64_norm]) (by simp only [TraceCalleeSaved, arm64_norm, htr.1, htr.2])
    (by simp only [Reg.x0, arm64_norm, hx29]) (by simp only [Reg.x1, arm64_norm, hx21])
    (by sep_focus) (by simp only [arm64_norm])
    (fun sf1 evsSc hpc1 hrun1 hsp1 hcs1 htr1 hcl1 hevs_sc => ?_)
  rcases hcs1 with ⟨hx19_1, hx20_1, hx21_1, hx22_1, hx23_1, hx24_1, hx25_1, hx26_1, hx27_1, hx28_1, hx29_1, _⟩
  simp only [arm64_norm, hx21, hx29]
    at hx19_1 hx20_1 hx21_1 hx22_1 hx23_1 hx24_1 hx25_1 hx26_1 hx27_1 hx28_1 hx29_1
  have h56_eq : (s_in.sp + 3992#64) + 56#64 = s_in.sp + 4048#64 := by bv_omega
  have h80_eq : (s_in.sp + 3992#64) + 80#64 = s_in.sp + 4072#64 := by bv_omega
  wp_conv_pre => rw [h56_eq, h80_eq]
  refine SepWP.fold (unchunkedCt2SentAt_extract A.repAlloc (s_in.sp + 3992#64) outUc) (by sep_focus) ?_
  wp_pull_exists; rename_i g_uc
  refine SepWP.fold (vecU8_entails_slice_and_tail A.repAlloc (s_in.sp + 4048#64) ct2) (by sep_focus) ?_
  wp_pull_exists; rename_i ct2Cap ct2Ptr; wp_focus_pure; rintro ⟨hct2_le, hct2_lt, hct2_ne⟩
  refine SepWP.fold (vecU8_entails_slice_and_tail A.repAlloc (s_in.sp + 4072#64) mac) (by sep_focus) ?_
  wp_pull_exists; rename_i macCap macPtr; wp_focus_pure; rintro ⟨hmac_le, hmac_lt, hmac_ne⟩
  have hmid := hmid_lem sf1 s_in.sp g_uc outUc.epoch
    ct2Cap ct2Ptr (BitVec.ofNat 64 ct2.length) macCap macPtr (BitVec.ofNat 64 mac.length)
    (relocatedHeap (fun dst => unchunkedCt2SentAt A.repAlloc dst outUc)
        (wordsBytes (ct2SentWordsList g_uc outUc.epoch)) ∗
      (ct2Ptr ↦ₛ ct2) ∗ vecU8Tail A.repAlloc ct2Cap ct2Ptr ct2 ∗
      (macPtr ↦ₛ mac) ∗ vecU8Tail A.repAlloc macCap macPtr mac ∗
      memRegion (s_in.sp + 1856#64) 400 ∗ memRegion (s_in.sp + 3856#64) 128 ∗
      unchunkedSendCt2PlacedRoAt ∗ A.pool lim (M.stepEvents evsSc st_cost) sf1 ∗
      (memRegion (s_in.sp - 19552#64) 2832 ∗ stackAt s_in.sp unchunkedSendCt2Stack) ∗ Rest)
    hfsp_align hpc1 hrun1 hsp1 hx21_1 hx29_1
  refine SepWP.weaken_pre (Entails.of_eq (by sep_ac_rfl))
    (DropChunkedClPlacedBudgetAux.seq_vm_clean_lscl hcl1 hmid
      (fun sf2 hpc2 hrun2 hcl2 hvm2 ⟨hsp2, hx0_2, hx1_2, hx2_2, hx3_2, hx4_2,
        hx19_2, hx20_2, hx21_2, hx24_2, hx25_2, hx26_2, hx27_2, hx28_2, hx29_2, hx30_2, htr2⟩ => ?_))
  wp_conv_pre => rw [← hsplit_sc, hsplit_enc]
  refine call_sendCt2Encoder_statesRecv_placed_ofPrePostEnv henc_raw (M.stepEvents evsSc st_cost)
    (s_in.sp + 1856#64) ct2Ptr macPtr ct2 mac outEnc
    hct2_ne hmac_ne henc (hfits_enc evsSc ct2Ptr macPtr hevs_sc hct2_ne hmac_ne)
    (s0 := s0) (s_pool := sf1) (ret_pc := (blkPl_332).base + 11696#64) (sp_call := s_in.sp)
    hcl2 hpc2 hrun2 hsp2 hfsp_align hx30_2 (htr2.trans htr1)
    hx0_2 hx1_2 hx2_2 hx3_2 hx4_2 (by sep_focus)
    (A.pool_transport lim (M.stepEvents evsSc st_cost) sf1 sf2 hvm2).symm
    (fun sf3 evsEnc hpc3 hrun3 hsp3 hcs3 htr3 hcl3 hevs_enc => ?_)
  rcases hcs3 with ⟨hx19_3, hx20_3, hx21_3, hx22_3, hx23_3, hx24_3, hx25_3, hx26_3, hx27_3, hx28_3, hx29_3, _⟩
  simp only [arm64_norm, hx19_2, hx20_2, hx21_2, hx24_2, hx25_2, hx26_2, hx27_2, hx28_2, hx29_2,
    hx19_1, hx24_1, hx28_1] at hx19_3 hx20_3 hx21_3 hx22_3 hx23_3 hx24_3 hx25_3 hx26_3 hx27_3 hx28_3 hx29_3
  refine SepWP.fold (slice_and_tail_entails_vecCapPtrDealloc A.repAlloc ct2Cap ct2Ptr ct2 hct2_le hct2_lt)
    (by sep_focus) ?_
  refine SepWP.fold (slice_and_tail_entails_vecCapPtrDealloc A.repAlloc macCap macPtr mac hmac_le hmac_lt)
    (by sep_focus) ?_
  refine SepWP.fold (Entails.of_eq hsplit_enc.symm) (by sep_focus) ?_
  refine SepWP.done hpc3 hrun3
    ⟨evsSc, evsEnc, g_uc, ct2Cap, ct2Ptr, macCap, macPtr, ?_,
      hsp3, hx19_3, hx20_3, hx21_3, hx24_3, hx25_3, hx26_3, hx27_3, hx28_3, hx29_3,
      htr3, hcl3, hevs_sc, hevs_enc⟩
  simp only [LibsignalBinary.Heap.AllocCostModel.stepEvents_append]
  exact Entails.of_eq (by sep_ac_rfl)

theorem ct1Sampled_send_ct2_and_encode_step_placed [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits} {F : ShaCompress} {K : MlKem}
    {ext : String → Option (State → State)}
    (hsendCt2 : subroutine_ok (lsProg_332 (Rust.withPanics ext)) (lsmpl.base 347)
      (withLsCodeLoaded lsmpl (unchunkedCt1SentEkReceivedSendCt2PlacedSpec M A lim F K)))
    (hsendCt2Enc : subroutine_ok (lsProg_332 (Rust.withPanics ext)) (lsmpl.base 382)
      (withLsCodeLoaded lsmpl (sendCt2EncoderSpec M A lim)))
    (st_cost : M.σ) (s0 s_in : State) (fsp : BitVec 64)
    (uc_ek : Ct1SentEkReceived (spqrAuthApi F)) (outUc : Ct2Sent (spqrAuthApi F))
    (ct2 : Bytes) (mac : Mac) (outEnc : PolyEncoder)
    (hsc : uc_ek.send_ct2 K = .ok (outUc, ct2, mac))
    (henc : send_ct2_encoder spqrPolyApi ct2 mac = .ok outEnc)
    (hfits_sc : FitsEnv M lim st_cost
      (UnchunkedSendCt2PreEnv ⟨fsp + 3992#64, fsp + 3856#64, uc_ek, outUc, ct2, mac⟩))
    (hfits_enc : ∀ evsSc : List AllocEvent,
      UnchunkedSendCt2PostEnv ⟨fsp + 3992#64, fsp + 3856#64, uc_ek, outUc, ct2, mac⟩ evsSc →
      FitsEnv M lim (M.stepEvents evsSc st_cost) (SendCt2EncoderBytesPreEnv ct2.length mac.length))
    (Rest : SepProp) (hcl : LibsignalCodeLoaded lsmpl s_in.mem)
    (hfsp_align : (fsp &&& 15#64 == 0#64) = true)
    (hpc : s_in.pc = (blkPl_332).base + 11624#64) (hrun : s_in.status = .Running)
    (hsp : s_in.sp = fsp) (htr : TraceCalleeSaved s_in s0)
    (hx21 : s_in.readReg64 .x21 = fsp + 3856#64) (hx29 : s_in.readReg64 .x29 = fsp + 4144#64) :
    SepWP (lsProg_332 (Rust.withPanics ext)) ((blkPl_332).base + 11696#64) s_in
      ((memRegion (fsp + 1856#64) 400 ∗ memRegion (fsp + 2256#64) 56 ∗
        unchunkedCt1SentEkReceivedAt A.repAlloc (fsp + 3856#64) uc_ek ∗
        memRegion (fsp + 3992#64) 104 ∗ unchunkedSendCt2PlacedRoAt ∗
        A.pool lim st_cost s_in ∗ stackAt fsp statesRecvCalleeStackX) ∗ Rest)
      (fun sf Pf =>
        ∃ (evsSc evsEnc : List AllocEvent) (g_uc : AuthWords) (ct2Cap ct2Ptr macCap macPtr : BitVec 64),
          (Pf ⊢ (polyEncoderAt A.repAlloc (fsp + 1856#64) outEnc ∗
            wordsAt (fsp + 2256#64) (ct2SentWordsList g_uc outUc.epoch) ∗
            relocatedHeap (fun dst => unchunkedCt2SentAt A.repAlloc dst outUc)
              (wordsBytes (ct2SentWordsList g_uc outUc.epoch)) ∗
            vecCapPtrDealloc A.repAlloc ct2Cap ct2Ptr ∗ vecCapPtrDealloc A.repAlloc macCap macPtr ∗
            memRegion (fsp + 3856#64) 128 ∗ memRegion (fsp + 3992#64) 104 ∗
            unchunkedSendCt2PlacedRoAt ∗ A.pool lim (M.stepEvents (evsSc ++ evsEnc) st_cost) sf ∗
            stackAt fsp statesRecvCalleeStackX) ∗ Rest) ∧
          sf.sp = fsp ∧ sf.readReg64 .x19 = s_in.readReg64 .x19 ∧ sf.readReg64 .x20 = macCap ∧
          sf.readReg64 .x21 = fsp + 3856#64 ∧ sf.readReg64 .x24 = s_in.readReg64 .x24 ∧
          sf.readReg64 .x25 = ct2Cap ∧ sf.readReg64 .x26 = ct2Ptr ∧
          sf.readReg64 .x27 = macPtr ∧ sf.readReg64 .x28 = s_in.readReg64 .x28 ∧
          sf.readReg64 .x29 = fsp + 4144#64 ∧ TraceCalleeSaved sf s0 ∧ LibsignalCodeLoaded lsmpl sf.mem ∧
          UnchunkedSendCt2PostEnv ⟨fsp + 3992#64, fsp + 3856#64, uc_ek, outUc, ct2, mac⟩ evsSc ∧
          SendCt2EncoderPostEnv ⟨fsp + 1856#64, ct2Ptr, ct2, macPtr, mac, outEnc⟩ evsEnc) :=
  ct1Sampled_send_ct2_and_encode_step_placed_ofPrePostEnv hsendCt2 hsendCt2Enc st_cost
    s0 s_in fsp uc_ek outUc ct2 mac outEnc hsc henc hfits_sc
    (fun evsSc _ _ hevs _ _ => hfits_enc evsSc hevs) Rest hcl hfsp_align hpc hrun hsp htr hx21 hx29

theorem ct1Sampled_send_ct2_and_encode_placed_ofPrePostEnv [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits} {F : ShaCompress} {K : MlKem}
    {ScPre ScPost : UnchunkedSendCt2Ghost F → List AllocEvent → Prop}
    {EncPre EncPost : SendCt2EncoderGhost → List AllocEvent → Prop}
    {ext : String → Option (State → State)} {target_pc : BitVec 64}
    (hsendCt2 : subroutine_ok (lsProg_332 (Rust.withPanics ext)) (lsmpl.base 347)
      (withLsCodeLoaded lsmpl
        (unchunkedCt1SentEkReceivedSendCt2PlacedSpecOfPrePostEnv M A lim F K ScPre ScPost)))
    (hsendCt2Enc : subroutine_ok (lsProg_332 (Rust.withPanics ext)) (lsmpl.base 382)
      (withLsCodeLoaded lsmpl (sendCt2EncoderSpecOfPrePostEnv M A lim EncPre EncPost)))
    (st_cost : M.σ) (s0 s_in : State) (fsp : BitVec 64)
    (uc_ek : Ct1SentEkReceived (spqrAuthApi F)) (outUc : Ct2Sent (spqrAuthApi F))
    (ct2 : Bytes) (mac : Mac) (outEnc : PolyEncoder)
    (hsc : uc_ek.send_ct2 K = .ok (outUc, ct2, mac))
    (henc : send_ct2_encoder spqrPolyApi ct2 mac = .ok outEnc)
    (hfits_sc : FitsEnv M lim st_cost (ScPre ⟨fsp + 3992#64, fsp + 3856#64, uc_ek, outUc, ct2, mac⟩))
    (hfits_enc : ∀ (evsSc : List AllocEvent) (ct2Ptr macPtr : BitVec 64),
      ScPost ⟨fsp + 3992#64, fsp + 3856#64, uc_ek, outUc, ct2, mac⟩ evsSc →
      ct2Ptr ≠ 0#64 → macPtr ≠ 0#64 →
      FitsEnv M lim (M.stepEvents evsSc st_cost)
        (EncPre ⟨fsp + 1856#64, ct2Ptr, ct2, macPtr, mac, outEnc⟩))
    (Frame : SepProp) {post : State → SepProp → Prop} (hcl : LibsignalCodeLoaded lsmpl s_in.mem)
    (hfsp_align : (fsp &&& 15#64 == 0#64) = true)
    (hpc : s_in.pc = (blkPl_332).base + 11624#64) (hrun : s_in.status = .Running)
    (hsp : s_in.sp = fsp) (htr : TraceCalleeSaved s_in s0)
    (hx21 : s_in.readReg64 .x21 = fsp + 3856#64) (hx29 : s_in.readReg64 .x29 = fsp + 4144#64)
    (hnext : ∀ (sf : State) (evsSc evsEnc : List AllocEvent) (g_uc : AuthWords)
      (ct2Cap ct2Ptr macCap macPtr : BitVec 64),
      sf.pc = (blkPl_332).base + 11696#64 → sf.status = .Running → sf.sp = fsp →
      sf.readReg64 .x19 = s_in.readReg64 .x19 → sf.readReg64 .x20 = macCap →
      sf.readReg64 .x21 = fsp + 3856#64 → sf.readReg64 .x24 = s_in.readReg64 .x24 →
      sf.readReg64 .x25 = ct2Cap → sf.readReg64 .x26 = ct2Ptr →
      sf.readReg64 .x27 = macPtr → sf.readReg64 .x28 = s_in.readReg64 .x28 →
      sf.readReg64 .x29 = fsp + 4144#64 → TraceCalleeSaved sf s0 → LibsignalCodeLoaded lsmpl sf.mem →
      ScPost ⟨fsp + 3992#64, fsp + 3856#64, uc_ek, outUc, ct2, mac⟩ evsSc →
      EncPost ⟨fsp + 1856#64, ct2Ptr, ct2, macPtr, mac, outEnc⟩ evsEnc →
      SepWP (lsProg_332 (Rust.withPanics ext)) target_pc sf
        ((polyEncoderAt A.repAlloc (fsp + 1856#64) outEnc ∗
          wordsAt (fsp + 2256#64) (ct2SentWordsList g_uc outUc.epoch) ∗
          relocatedHeap (fun dst => unchunkedCt2SentAt A.repAlloc dst outUc)
            (wordsBytes (ct2SentWordsList g_uc outUc.epoch)) ∗
          vecCapPtrDealloc A.repAlloc ct2Cap ct2Ptr ∗ vecCapPtrDealloc A.repAlloc macCap macPtr ∗
          memRegion (fsp + 3856#64) 128 ∗ memRegion (fsp + 3992#64) 104 ∗
          unchunkedSendCt2PlacedRoAt ∗ A.pool lim (M.stepEvents (evsSc ++ evsEnc) st_cost) sf ∗
          stackAt fsp statesRecvCalleeStackX) ∗ Frame) post) :
    SepWP (lsProg_332 (Rust.withPanics ext)) target_pc s_in
      ((memRegion (fsp + 1856#64) 400 ∗ memRegion (fsp + 2256#64) 56 ∗
        unchunkedCt1SentEkReceivedAt A.repAlloc (fsp + 3856#64) uc_ek ∗
        memRegion (fsp + 3992#64) 104 ∗ unchunkedSendCt2PlacedRoAt ∗
        A.pool lim st_cost s_in ∗ stackAt fsp statesRecvCalleeStackX) ∗ Frame) post :=
  SepWP.seq
    (ct1Sampled_send_ct2_and_encode_step_placed_ofPrePostEnv hsendCt2 hsendCt2Enc st_cost
      s0 s_in fsp uc_ek outUc ct2 mac outEnc hsc henc hfits_sc hfits_enc Frame
      hcl hfsp_align hpc hrun hsp htr hx21 hx29)
    fun sf _ hpc_sf hrun_sf
      ⟨evsSc, evsEnc, g_uc, ct2Cap, ct2Ptr, macCap, macPtr, hPf,
        hsp_sf, hx19, hx20, hx21', hx24, hx25, hx26, hx27, hx28, hx29',
        htr_sf, hcl_sf, hevs_sc, hevs_enc⟩ =>
      SepWP.weaken_pre hPf
        (hnext sf evsSc evsEnc g_uc ct2Cap ct2Ptr macCap macPtr
          hpc_sf hrun_sf hsp_sf hx19 hx20 hx21' hx24 hx25 hx26 hx27 hx28 hx29'
          htr_sf hcl_sf hevs_sc hevs_enc)

theorem ct1Sampled_send_ct2_and_encode_placed [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits} {F : ShaCompress} {K : MlKem}
    {ext : String → Option (State → State)} {target_pc : BitVec 64}
    (hsendCt2 : subroutine_ok (lsProg_332 (Rust.withPanics ext)) (lsmpl.base 347)
      (withLsCodeLoaded lsmpl (unchunkedCt1SentEkReceivedSendCt2PlacedSpec M A lim F K)))
    (hsendCt2Enc : subroutine_ok (lsProg_332 (Rust.withPanics ext)) (lsmpl.base 382)
      (withLsCodeLoaded lsmpl (sendCt2EncoderSpec M A lim)))
    (st_cost : M.σ) (s0 s_in : State) (fsp : BitVec 64)
    (uc_ek : Ct1SentEkReceived (spqrAuthApi F)) (outUc : Ct2Sent (spqrAuthApi F))
    (ct2 : Bytes) (mac : Mac) (outEnc : PolyEncoder)
    (hsc : uc_ek.send_ct2 K = .ok (outUc, ct2, mac))
    (henc : send_ct2_encoder spqrPolyApi ct2 mac = .ok outEnc)
    (hfits_sc : FitsEnv M lim st_cost
      (UnchunkedSendCt2PreEnv ⟨fsp + 3992#64, fsp + 3856#64, uc_ek, outUc, ct2, mac⟩))
    (hfits_enc : ∀ evsSc : List AllocEvent,
      UnchunkedSendCt2PostEnv ⟨fsp + 3992#64, fsp + 3856#64, uc_ek, outUc, ct2, mac⟩ evsSc →
      FitsEnv M lim (M.stepEvents evsSc st_cost) (SendCt2EncoderBytesPreEnv ct2.length mac.length))
    (Frame : SepProp) {post : State → SepProp → Prop} (hcl : LibsignalCodeLoaded lsmpl s_in.mem)
    (hfsp_align : (fsp &&& 15#64 == 0#64) = true)
    (hpc : s_in.pc = (blkPl_332).base + 11624#64) (hrun : s_in.status = .Running)
    (hsp : s_in.sp = fsp) (htr : TraceCalleeSaved s_in s0)
    (hx21 : s_in.readReg64 .x21 = fsp + 3856#64) (hx29 : s_in.readReg64 .x29 = fsp + 4144#64)
    (hnext : ∀ (sf : State) (evsSc evsEnc : List AllocEvent) (g_uc : AuthWords)
      (ct2Cap ct2Ptr macCap macPtr : BitVec 64),
      sf.pc = (blkPl_332).base + 11696#64 → sf.status = .Running → sf.sp = fsp →
      sf.readReg64 .x19 = s_in.readReg64 .x19 → sf.readReg64 .x20 = macCap →
      sf.readReg64 .x21 = fsp + 3856#64 → sf.readReg64 .x24 = s_in.readReg64 .x24 →
      sf.readReg64 .x25 = ct2Cap → sf.readReg64 .x26 = ct2Ptr →
      sf.readReg64 .x27 = macPtr → sf.readReg64 .x28 = s_in.readReg64 .x28 →
      sf.readReg64 .x29 = fsp + 4144#64 → TraceCalleeSaved sf s0 → LibsignalCodeLoaded lsmpl sf.mem →
      UnchunkedSendCt2PostEnv ⟨fsp + 3992#64, fsp + 3856#64, uc_ek, outUc, ct2, mac⟩ evsSc →
      SendCt2EncoderPostEnv ⟨fsp + 1856#64, ct2Ptr, ct2, macPtr, mac, outEnc⟩ evsEnc →
      SepWP (lsProg_332 (Rust.withPanics ext)) target_pc sf
        ((polyEncoderAt A.repAlloc (fsp + 1856#64) outEnc ∗
          wordsAt (fsp + 2256#64) (ct2SentWordsList g_uc outUc.epoch) ∗
          relocatedHeap (fun dst => unchunkedCt2SentAt A.repAlloc dst outUc)
            (wordsBytes (ct2SentWordsList g_uc outUc.epoch)) ∗
          vecCapPtrDealloc A.repAlloc ct2Cap ct2Ptr ∗ vecCapPtrDealloc A.repAlloc macCap macPtr ∗
          memRegion (fsp + 3856#64) 128 ∗ memRegion (fsp + 3992#64) 104 ∗
          unchunkedSendCt2PlacedRoAt ∗ A.pool lim (M.stepEvents (evsSc ++ evsEnc) st_cost) sf ∗
          stackAt fsp statesRecvCalleeStackX) ∗ Frame) post) :
    SepWP (lsProg_332 (Rust.withPanics ext)) target_pc s_in
      ((memRegion (fsp + 1856#64) 400 ∗ memRegion (fsp + 2256#64) 56 ∗
        unchunkedCt1SentEkReceivedAt A.repAlloc (fsp + 3856#64) uc_ek ∗
        memRegion (fsp + 3992#64) 104 ∗ unchunkedSendCt2PlacedRoAt ∗
        A.pool lim st_cost s_in ∗ stackAt fsp statesRecvCalleeStackX) ∗ Frame) post :=
  ct1Sampled_send_ct2_and_encode_placed_ofPrePostEnv hsendCt2 hsendCt2Enc st_cost
    s0 s_in fsp uc_ek outUc ct2 mac outEnc hsc henc hfits_sc
    (fun evsSc _ _ hevs _ _ => hfits_enc evsSc hevs) Frame
    hcl hfsp_align hpc hrun hsp htr hx21 hx29 hnext

set_option maxHeartbeats 1600000 in
theorem ct1Sampled_copy_some_ack_stage_placed [LibsignalPlacement]
    {ext : String → Option (State → State)} (s_in : State) (fsp stA : BitVec 64)
    (c_enc : Words50) (g : AuthWords) (epoch : BitVec 64)
    (sc : CopyScratchStack) (k : EpilogueStoreStack) (Rest : SepProp)
    (hfsp_align : (fsp &&& 15#64 == 0#64) = true)
    (hpc : s_in.pc = (blkPl_332).base + 11696#64) (hrun : s_in.status = .Running)
    (hsp : s_in.sp = fsp) (hx29 : s_in.readReg64 .x29 = fsp + 4144#64) :
    let d := mkSplit928Ct2Sampled c_enc g epoch 0#64 k.wf8 k.w3c0 k.w3c8 k.w100 k.mid k.tail
    SepWP (lsProg_332 (Rust.withPanics ext)) ((blkPl_332).base + 12072#64) s_in
      (words50At (fsp + 1856#64) c_enc ∗ wordsAt (fsp + 2256#64) (ct2SentWordsList g epoch) ∗
        copyScratchStackAt fsp sc ∗ epilogueStoreStackPart1At fsp k ∗ Rest)
      (fun sf Pf =>
        VmPreserved s_in sf ∧
        (Pf ⊢ words50At (fsp + 1856#64) c_enc ∗ wordsAt (fsp + 2256#64) (ct2SentWordsList g epoch) ∗
          copyScratchStackAt fsp
            { (copyFullScratchCt2 sc d) with
              c0 := { (copyFullScratchCt2 sc d).c0 with w12 := sc.c0.w12 }, w88 := sc.w88 } ∗
          epilogueStoreStackPart1At fsp
            { (epilogueStackOfSplit928 d stA k.w200 k.w208) with
              we0 := k.we0, w118 := k.w118, w1e0 := k.w1e0, w3c0 := k.w3c0, w3c8 := k.w3c8 } ∗ Rest) ∧
        sf.sp = fsp ∧ sf.readReg64 .x1 = s_in.readReg64 .x20 ∧
        sf.readReg64 .x19 = s_in.readReg64 .x19 ∧ sf.readReg64 .x20 = c_enc.c1.w11 ∧
        sf.readReg64 .x21 = g.v2.w2 ∧ sf.readReg64 .x22 = g.v2.w1 ∧
        sf.readReg64 .x23 = c_enc.c0.w0 ∧ sf.readReg64 .x24 = s_in.readReg64 .x24 ∧
        sf.readReg64 .x25 = s_in.readReg64 .x25 ∧ sf.readReg64 .x26 = s_in.readReg64 .x26 ∧
        sf.readReg64 .x27 = s_in.readReg64 .x27 ∧ sf.readReg64 .x28 = s_in.readReg64 .x28 ∧
        sf.readReg64 .x29 = fsp + 4144#64 ∧ TraceCalleeSaved sf s_in) := by
  intro d; subst hsp
  dsimp only [lsProg_332, BitVec.ofNat_eq_ofNat] at hpc ⊢
  dsimp only [d, mkSplit928Ct2Sampled, copyScratchStackAt, copyFullScratchCt2, copyFullScratch,
    epilogueStoreStackPart1At, epilogueStackOfSplit928, words50At,
    ct2SentWordsList, authWordsList, vecWordsList, Words16.toList]
  simp only [List.cons_append, List.nil_append,
    wordsAt_16, wordsAt_7, BitVec.add_assoc, BitVec.reduceAdd, hx29]
  by_vm_steps_nest (
    wp_steps
    dsimp only [TraceCalleeSaved, Reg.x1, Reg.x19, Reg.x20, Reg.x21, Reg.x22, Reg.x23,
      Reg.x24, Reg.x25, Reg.x26, Reg.x27, Reg.x28, Reg.x29]
    wp_done
  )

theorem ct1Sampled_copy_some_ack_stage_pool_placed [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {ext : String → Option (State → State)}
    (st_cost : M.σ) (s_in : State) (fsp stA : BitVec 64)
    (c_enc : Words50) (g : AuthWords) (epoch : BitVec 64)
    (sc : CopyScratchStack) (k : EpilogueStoreStack) (Rest : SepProp)
    (hfsp_align : (fsp &&& 15#64 == 0#64) = true)
    (hpc : s_in.pc = (blkPl_332).base + 11696#64) (hrun : s_in.status = .Running)
    (hsp : s_in.sp = fsp) (hx29 : s_in.readReg64 .x29 = fsp + 4144#64) :
    let d := mkSplit928Ct2Sampled c_enc g epoch 0#64 k.wf8 k.w3c0 k.w3c8 k.w100 k.mid k.tail
    SepWP (lsProg_332 (Rust.withPanics ext)) ((blkPl_332).base + 12072#64) s_in
      (words50At (fsp + 1856#64) c_enc ∗ wordsAt (fsp + 2256#64) (ct2SentWordsList g epoch) ∗
        copyScratchStackAt fsp sc ∗ epilogueStoreStackPart1At fsp k ∗ A.pool lim st_cost s_in ∗ Rest)
      (fun sf Pf =>
        VmPreserved s_in sf ∧
        (Pf ⊢ words50At (fsp + 1856#64) c_enc ∗ wordsAt (fsp + 2256#64) (ct2SentWordsList g epoch) ∗
          copyScratchStackAt fsp
            { (copyFullScratchCt2 sc d) with
              c0 := { (copyFullScratchCt2 sc d).c0 with w12 := sc.c0.w12 }, w88 := sc.w88 } ∗
          epilogueStoreStackPart1At fsp
            { (epilogueStackOfSplit928 d stA k.w200 k.w208) with
              we0 := k.we0, w118 := k.w118, w1e0 := k.w1e0, w3c0 := k.w3c0, w3c8 := k.w3c8 } ∗
          A.pool lim st_cost sf ∗ Rest) ∧
        sf.sp = fsp ∧ sf.readReg64 .x1 = s_in.readReg64 .x20 ∧
        sf.readReg64 .x19 = s_in.readReg64 .x19 ∧ sf.readReg64 .x20 = c_enc.c1.w11 ∧
        sf.readReg64 .x21 = g.v2.w2 ∧ sf.readReg64 .x22 = g.v2.w1 ∧
        sf.readReg64 .x23 = c_enc.c0.w0 ∧ sf.readReg64 .x24 = s_in.readReg64 .x24 ∧
        sf.readReg64 .x25 = s_in.readReg64 .x25 ∧ sf.readReg64 .x26 = s_in.readReg64 .x26 ∧
        sf.readReg64 .x27 = s_in.readReg64 .x27 ∧ sf.readReg64 .x28 = s_in.readReg64 .x28 ∧
        sf.readReg64 .x29 = fsp + 4144#64 ∧ TraceCalleeSaved sf s_in) := by
  intro d
  exact SepWP.mono
    (ct1Sampled_copy_some_ack_stage_placed s_in fsp stA c_enc g epoch sc k
      (A.pool lim st_cost s_in ∗ Rest) hfsp_align hpc hrun hsp hx29)
    fun sf _ _ _ ⟨hvm, hPf, hq⟩ =>
      ⟨hvm, Entails.trans hPf (Entails.of_eq (by rw [A.pool_transport lim st_cost s_in sf hvm])), hq⟩

theorem ct1Sampled_dealloc_mac_12072_placed [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {ext : String → Option (State → State)}
    (hdealloc : HookSat (Rust.withPanics ext) spqrDeallocSym (rustCliDeallocBudgetSpec M A lim))
    (st_cost : M.σ) (s_in : State) (fsp macCap macPtr : BitVec 64) (Rest : SepProp)
    (hfsp_align : (fsp &&& 15#64 == 0#64) = true)
    (hpc : s_in.pc = (blkPl_332).base + 12072#64) (hrun : s_in.status = .Running)
    (hsp : s_in.sp = fsp) (hx1 : s_in.readReg64 .x1 = macCap) (hx27 : s_in.readReg64 .x27 = macPtr) :
    SepWP (lsProg_332 (Rust.withPanics ext)) ((blkPl_332).base + 12088#64) s_in
      (vecCapPtrDealloc A.repAlloc macCap macPtr ∗
        A.pool lim st_cost s_in ∗ stackAt fsp statesRecvCalleeStackX ∗ Rest)
      (fun sf Pf =>
        ∃ evs : List AllocEvent, FreeOnlyEvs evs ∧
          (Pf ⊢ A.pool lim (M.stepEvents evs st_cost) sf ∗ stackAt fsp statesRecvCalleeStackX ∗ Rest) ∧
          sf.sp = fsp ∧ AllocCallPreserved s_in sf ∧
          sf.readReg64 .x19 = s_in.readReg64 .x19 ∧ sf.readReg64 .x20 = s_in.readReg64 .x20 ∧
          sf.readReg64 .x21 = s_in.readReg64 .x21 ∧ sf.readReg64 .x22 = s_in.readReg64 .x22 ∧
          sf.readReg64 .x23 = s_in.readReg64 .x23 ∧ sf.readReg64 .x24 = s_in.readReg64 .x24 ∧
          sf.readReg64 .x25 = s_in.readReg64 .x25 ∧ sf.readReg64 .x26 = s_in.readReg64 .x26 ∧
          sf.readReg64 .x28 = s_in.readReg64 .x28 ∧ sf.readReg64 .x29 = s_in.readReg64 .x29 ∧
          TraceCalleeSaved sf s_in) := by
  subst hsp hx1 hx27
  have hdealloc_fo : subroutine_ok (lsProg_332 (Rust.withPanics ext))
      (lsρ spqrDeallocSym) (DropChunkedClPlacedBudgetAux.deallocFreeOnlySpec M A lim) :=
    DropChunkedClPlacedBudgetAux.subroutine_ok_deallocFreeOnly
      (spqr_hook_ok_of_mem (sym := spqrDeallocSym) hdealloc)
  simp only [DropChunkedClPlacedBudgetAux.deallocFreeOnlySpec, rustCliDeallocBudgetSpec] at hdealloc_fo
  have hsplit := stackAt_statesRecvCallee_eq_allocHook' s_in.sp
  dsimp only [lsProg_332, spqrDeallocSym, spqrRustDeallocSym, BitVec.ofNat_eq_ofNat]
    at hpc hdealloc_fo hsplit ⊢
  rw [hsplit]
  dsimp only [vecCapPtrDealloc, LibsignalBinary.Heap.RustCliAllocBudget.repAlloc_live]
  by_cases hmac : (s_in.readReg64 .x1 == 0#64) = true <;>
    simp only [hmac, Bool.false_eq_true, ↓reduceIte, sepConj_emp, emp_sepConj]
  · apply DropChunkedClPlacedBudgetAux.sepWP_evs_nil
    simp only [LibsignalBinary.Heap.AllocCostModel.stepEvents_nil]
    wp_steps; rw [← hsplit]
    dsimp only [AllocCallPreserved, TraceCalleeSaved,
      Reg.x19, Reg.x20, Reg.x21, Reg.x22, Reg.x23, Reg.x24, Reg.x25, Reg.x26, Reg.x28, Reg.x29]
    wp_done
  · apply DropChunkedClPlacedBudgetAux.sepWP_evs_dealloc (s_in.readReg64 .x1).toNat 1
    wp_steps; wp_apply; rw [← hsplit]
    have hacp_sf : AllocCallPreserved s_in sf := by assumption
    rcases hacp_sf with ⟨_, _, _, _, _, _, _⟩
    dsimp only [AllocCallPreserved, TraceCalleeSaved,
      Reg.x19, Reg.x20, Reg.x21, Reg.x22, Reg.x23, Reg.x24, Reg.x25, Reg.x26, Reg.x28, Reg.x29]
    wp_done

theorem ct1Sampled_dealloc_ct2_12088_placed [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {ext : String → Option (State → State)}
    (hdealloc : HookSat (Rust.withPanics ext) spqrDeallocSym (rustCliDeallocBudgetSpec M A lim))
    (st_cost : M.σ) (s_in : State) (fsp ct2Cap ct2Ptr : BitVec 64) (Rest : SepProp)
    (hfsp_align : (fsp &&& 15#64 == 0#64) = true)
    (hpc : s_in.pc = (blkPl_332).base + 12088#64) (hrun : s_in.status = .Running)
    (hsp : s_in.sp = fsp) (hx25 : s_in.readReg64 .x25 = ct2Cap) (hx26 : s_in.readReg64 .x26 = ct2Ptr) :
    SepWP (lsProg_332 (Rust.withPanics ext)) ((blkPl_332).base + 12108#64) s_in
      (vecCapPtrDealloc A.repAlloc ct2Cap ct2Ptr ∗
        A.pool lim st_cost s_in ∗ stackAt fsp statesRecvCalleeStackX ∗ Rest)
      (fun sf Pf =>
        ∃ evs : List AllocEvent, FreeOnlyEvs evs ∧
          (Pf ⊢ A.pool lim (M.stepEvents evs st_cost) sf ∗ stackAt fsp statesRecvCalleeStackX ∗ Rest) ∧
          sf.sp = fsp ∧ AllocCallPreserved s_in sf ∧
          sf.readReg64 .x19 = s_in.readReg64 .x19 ∧ sf.readReg64 .x20 = s_in.readReg64 .x20 ∧
          sf.readReg64 .x21 = s_in.readReg64 .x21 ∧ sf.readReg64 .x22 = s_in.readReg64 .x22 ∧
          sf.readReg64 .x23 = s_in.readReg64 .x23 ∧ sf.readReg64 .x24 = s_in.readReg64 .x24 ∧
          sf.readReg64 .x28 = s_in.readReg64 .x28 ∧ sf.readReg64 .x29 = s_in.readReg64 .x29 ∧
          TraceCalleeSaved sf s_in) := by
  subst hsp hx25 hx26
  have hdealloc_fo : subroutine_ok (lsProg_332 (Rust.withPanics ext))
      (lsρ spqrDeallocSym) (DropChunkedClPlacedBudgetAux.deallocFreeOnlySpec M A lim) :=
    DropChunkedClPlacedBudgetAux.subroutine_ok_deallocFreeOnly
      (spqr_hook_ok_of_mem (sym := spqrDeallocSym) hdealloc)
  simp only [DropChunkedClPlacedBudgetAux.deallocFreeOnlySpec, rustCliDeallocBudgetSpec] at hdealloc_fo
  have hsplit := stackAt_statesRecvCallee_eq_allocHook' s_in.sp
  dsimp only [lsProg_332, spqrDeallocSym, spqrRustDeallocSym, BitVec.ofNat_eq_ofNat]
    at hpc hdealloc_fo hsplit ⊢
  rw [hsplit]
  dsimp only [vecCapPtrDealloc, LibsignalBinary.Heap.RustCliAllocBudget.repAlloc_live]
  by_cases hct2 : (s_in.readReg64 .x25 == 0#64) = true <;>
    simp only [hct2, Bool.false_eq_true, ↓reduceIte, sepConj_emp, emp_sepConj]
  · apply DropChunkedClPlacedBudgetAux.sepWP_evs_nil
    simp only [LibsignalBinary.Heap.AllocCostModel.stepEvents_nil]
    wp_steps; rw [← hsplit]
    dsimp only [AllocCallPreserved, TraceCalleeSaved,
      Reg.x19, Reg.x20, Reg.x21, Reg.x22, Reg.x23, Reg.x24, Reg.x28, Reg.x29]
    wp_done
  · apply DropChunkedClPlacedBudgetAux.sepWP_evs_dealloc (s_in.readReg64 .x25).toNat 1
    wp_steps; wp_apply; rw [← hsplit]
    have hacp_sf : AllocCallPreserved s_in sf := by assumption
    rcases hacp_sf with ⟨_, _, _, _, _, _, _⟩
    dsimp only [AllocCallPreserved, TraceCalleeSaved,
      Reg.x19, Reg.x20, Reg.x21, Reg.x22, Reg.x23, Reg.x24, Reg.x28, Reg.x29]
    wp_done

set_option maxHeartbeats 1600000 in
theorem ct1Sampled_drop_and_finish_stage_12108_placed [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {ext : String → Option (State → State)}
    (hdealloc : HookSat (Rust.withPanics ext) spqrDeallocSym (rustCliDeallocBudgetSpec M A lim))
    (st_cost : M.σ) (s_in : State) (fsp stA : BitVec 64)
    (vecs_enc : List (List GF16)) (hvecs_enc_len : vecs_enc.length = NUM_POLYS)
    (vecs_dec : List (List Pt)) (hvecs_dec_len : vecs_dec.length = NUM_POLYS)
    (c_enc : Words50) (g : AuthWords) (epoch : BitVec 64)
    (sc : CopyScratchStack) (k : EpilogueStoreStack) (Rest : SepProp)
    (hcl : LibsignalCodeLoaded lsmpl s_in.mem)
    (hfsp_align : (fsp &&& 15#64 == 0#64) = true)
    (hpc : s_in.pc = (blkPl_332).base + 12108#64) (hrun : s_in.status = .Running) (hsp : s_in.sp = fsp)
    (hx20 : s_in.readReg64 .x20 = c_enc.c1.w11) (hx21 : s_in.readReg64 .x21 = g.v2.w2)
    (hx22 : s_in.readReg64 .x22 = g.v2.w1) (hx23 : s_in.readReg64 .x23 = c_enc.c0.w0) :
    let d := mkSplit928Ct2Sampled c_enc g epoch 0#64 k.wf8 k.w3c0 k.w3c8 k.w100 k.mid k.tail
    SepWP (lsProg_332 (Rust.withPanics ext)) ((blkPl_332).base + 16596#64) s_in
      (((fsp + 232#64) ↦₆₄ stA) ∗ vecGF16ListOf A.repAlloc (stA + 8#64) vecs_enc ∗
        vecPtListOf A.repAlloc (fsp + 2752#64) vecs_dec ∗ memRegion (fsp + 3136#64) 16 ∗
        copyScratchStackAt fsp
          { (copyFullScratchCt2 sc d) with
            c0 := { (copyFullScratchCt2 sc d).c0 with w12 := sc.c0.w12 }, w88 := sc.w88 } ∗
        epilogueStoreStackPart1At fsp
          { (epilogueStackOfSplit928 d stA k.w200 k.w208) with
            we0 := k.we0, w118 := k.w118, w1e0 := k.w1e0, w3c0 := k.w3c0, w3c8 := k.w3c8 } ∗
        A.pool lim st_cost s_in ∗ stackAt fsp statesRecvCalleeStackX ∗ Rest)
      (fun sf Pf =>
        ∃ evs : List AllocEvent, FreeOnlyEvs evs ∧
          (Pf ⊢ ((fsp + 232#64) ↦₆₄ stA) ∗ memRegion (stA + 8#64) 384 ∗
            memRegion (fsp + 2752#64) 400 ∗ copyScratchStackAt fsp (copyFullScratchCt2 sc d) ∗
            epilogueStoreStackPart1At fsp
              { (epilogueStackOfSplit928 d stA k.w200 k.w208) with
                we0 := k.we0, w3c0 := k.w3c0, w3c8 := k.w3c8 } ∗
            A.pool lim (M.stepEvents evs st_cost) sf ∗ stackAt fsp statesRecvCalleeStackX ∗ Rest) ∧
          sf.sp = fsp ∧ AllocCallPreserved s_in sf ∧
          sf.readReg64 .x19 = s_in.readReg64 .x19 ∧ sf.readReg64 .x23 = 4#64 ∧
          sf.readReg64 .x24 = s_in.readReg64 .x24 ∧ sf.readReg64 .x28 = s_in.readReg64 .x28 ∧
          sf.readReg64 .x29 = s_in.readReg64 .x29 ∧ TraceCalleeSaved sf s_in) := by
  intro d; subst hsp
  have hsplit := stackAt_statesRecvCallee_eq_dropGluePoly16' s_in.sp
  refine SepWP.mono (post := fun sf Pf =>
      ∃ evs : List AllocEvent, FreeOnlyEvs evs ∧
        (Pf ⊢ (((s_in.sp + 232#64) ↦₆₄ stA) ∗ memRegion (stA + 8#64) 384 ∗
            (memRegion (s_in.sp + 2752#64) 384 ∗ memRegion (s_in.sp + 3136#64) 16) ∗
            copyScratchStackAt s_in.sp (copyFullScratchCt2 sc d) ∗
            epilogueStoreStackPart1At s_in.sp
              { (epilogueStackOfSplit928 d stA k.w200 k.w208) with
                we0 := k.we0, w3c0 := k.w3c0, w3c8 := k.w3c8 }) ∗
          A.pool lim (M.stepEvents evs st_cost) sf ∗
          ((memRegion (s_in.sp - 19552#64) 15424 ∗ stackAt s_in.sp dropGluePoly16Stack) ∗ Rest)) ∧
        (sf.sp = s_in.sp ∧ AllocCallPreserved s_in sf ∧
          sf.readReg64 .x19 = s_in.readReg64 .x19 ∧ sf.readReg64 .x23 = 4#64 ∧
          sf.readReg64 .x24 = s_in.readReg64 .x24 ∧ sf.readReg64 .x28 = s_in.readReg64 .x28 ∧
          sf.readReg64 .x29 = s_in.readReg64 .x29 ∧ TraceCalleeSaved sf s_in)) ?_
    (fun sf Pf _ _ ⟨evs, hevs, hPf, hrest⟩ => ⟨evs, hevs, Entails.trans hPf ?_, hrest⟩)
  · rw [hsplit]
    refine DropChunkedClPlacedBudgetAux.seq_evs_step_lscl hcl (mid := (blkPl_332).base + 12124#64)
      (P_mid := fun st1 sm =>
        ((s_in.sp + 232#64) ↦₆₄ stA) ∗ memRegion (stA + 8#64) 384 ∗
        vecPtListOf A.repAlloc (s_in.sp + 2752#64) vecs_dec ∗ memRegion (s_in.sp + 3136#64) 16 ∗
        copyScratchStackAt s_in.sp
          { (copyFullScratchCt2 sc d) with
            c0 := { (copyFullScratchCt2 sc d).c0 with w12 := sc.c0.w12 }, w88 := sc.w88 } ∗
        epilogueStoreStackPart1At s_in.sp
          { (epilogueStackOfSplit928 d stA k.w200 k.w208) with
            we0 := k.we0, w1e0 := k.w1e0, w3c0 := k.w3c0, w3c8 := k.w3c8 } ∗
        A.pool lim st1 sm ∗ memRegion (s_in.sp - 19552#64) 15424 ∗
        stackAt s_in.sp dropGluePoly16Stack ∗ Rest)
      (Q_mid := fun sm =>
        sm.sp = s_in.sp ∧ AllocCallPreserved s_in sm ∧
        sm.readReg64 .x19 = s_in.readReg64 .x19 ∧ sm.readReg64 .x21 = g.v2.w2 ∧
        sm.readReg64 .x22 = g.v2.w1 ∧ sm.readReg64 .x23 = c_enc.c0.w0 ∧
        sm.readReg64 .x24 = s_in.readReg64 .x24 ∧ sm.readReg64 .x28 = s_in.readReg64 .x28 ∧
        sm.readReg64 .x29 = s_in.readReg64 .x29 ∧ TraceCalleeSaved sm s_in) ?_ ?_
    · dsimp only [lsProg_332, d, mkSplit928Ct2Sampled, epilogueStoreStackPart1At,
        epilogueStackOfSplit928, Words16.toList, BitVec.ofNat_eq_ofNat] at hpc ⊢
      refine seq_vm_cont_lscl hcl (mid := lsmpl.base 265) ?_
      by_vm_steps_nest (
        wp_steps
        refine SepWP.done rfl hrun ⟨by simp only [wp_norm, arm64_norm], fun hclm hvmm => ?_⟩
        have hdrop_poly := DropChunkedClPlacedBudgetAux.drop_glue_poly16_mem_on
          (callerProg := (blkPC_332).rebase (blkPl_332).base (Rust.withPanics ext)) hdealloc hclm
        dsimp only [withMemEq, LibsignalBinary.Proofs.SpqrV1.Drop.PolyBudget.dropGluePoly16Spec,
          polyArrayBytes, BitVec.ofNat_eq_ofNat] at hdrop_poly
        wp_conv_pre => rw [← A.pool_of_vmPreserved hvmm]
        wp_call hdrop_poly (⟨stA + 8#64, vecs_enc⟩, st_cost)
        have hacp1 : AllocCallPreserved s_in sf := by assumption
        have hevs1 : FreeOnlyEvs w := by assumption
        refine SepWP.mono (post := fun sm Pm =>
          (Pm ⊢ ((s_in.sp + 232#64) ↦₆₄ stA) ∗ memRegion (stA + 8#64) 384 ∗
            vecPtListOf A.repAlloc (s_in.sp + 2752#64) vecs_dec ∗ memRegion (s_in.sp + 3136#64) 16 ∗
            copyScratchStackAt s_in.sp
              { (copyFullScratchCt2 sc d) with
                c0 := { (copyFullScratchCt2 sc d).c0 with w12 := sc.c0.w12 }, w88 := sc.w88 } ∗
            epilogueStoreStackPart1At s_in.sp
              { (epilogueStackOfSplit928 d stA k.w200 k.w208) with
                we0 := k.we0, w1e0 := k.w1e0, w3c0 := k.w3c0, w3c8 := k.w3c8 } ∗
            A.pool lim (M.stepEvents w st_cost) sm ∗ memRegion (s_in.sp - 19552#64) 15424 ∗
            stackAt s_in.sp dropGluePoly16Stack ∗ Rest) ∧
          sm.sp = s_in.sp ∧ AllocCallPreserved sf sm ∧
          sm.readReg64 .x19 = s_in.readReg64 .x19 ∧ sm.readReg64 .x21 = g.v2.w2 ∧
          sm.readReg64 .x22 = g.v2.w1 ∧ sm.readReg64 .x23 = c_enc.c0.w0 ∧
          sm.readReg64 .x24 = s_in.readReg64 .x24 ∧ sm.readReg64 .x28 = s_in.readReg64 .x28 ∧
          sm.readReg64 .x29 = s_in.readReg64 .x29 ∧ TraceCalleeSaved sm s_in) ?_
          (fun _ _ _ _ ⟨hPm, hspm, hacp1b, hrestm⟩ => ⟨w, hevs1, hPm, hspm, hacp1.trans hacp1b, hrestm⟩)
        dsimp only [d, mkSplit928Ct2Sampled, epilogueStoreStackPart1At, epilogueStackOfSplit928,
          Words16.toList, AllocCallPreserved, TraceCalleeSaved,
          Reg.x19, Reg.x21, Reg.x22, Reg.x23, Reg.x24, Reg.x28, Reg.x29]
        wp_done
      )
    · intro st1 sm hpcm hrunm hclm ⟨hspm, hacp1, hx19m, hx21m, hx22m, hx23m, hx24m, hx28m, hx29m, htrm⟩
      dsimp only [lsProg_332, d, mkSplit928Ct2Sampled, copyScratchStackAt, copyFullScratchCt2,
        copyFullScratch, epilogueStoreStackPart1At, epilogueStackOfSplit928,
        Words16.toList, BitVec.ofNat_eq_ofNat] at hpcm ⊢
      rw [← hspm]
      simp only [wordsAt_16, BitVec.add_assoc, BitVec.reduceAdd, hx21m, hx22m, hx23m]
      refine seq_vm_cont_lscl hclm (mid := lsmpl.base 264) ?_
      by_vm_steps_nest (
        wp_steps
        refine SepWP.done rfl hrunm ⟨by simp only [wp_norm, arm64_norm], fun hclm2 hvmm2 => ?_⟩
        have hdrop_ss := DropChunkedClPlacedBudgetAux.drop_glue_sorted_set_pt16_mem_on
          (callerProg := (blkPC_332).rebase (blkPl_332).base (Rust.withPanics ext)) hdealloc hclm2
        dsimp only [withMemEq,
          LibsignalBinary.Proofs.SpqrV1.Drop.SortedSetPtBudget.dropGlueSortedSetPt16Spec,
          polyArrayBytes, BitVec.ofNat_eq_ofNat] at hdrop_ss
        wp_conv_pre => rw [← A.pool_of_vmPreserved hvmm2]
        wp_call hdrop_ss (⟨sm.sp + 2752#64, vecs_dec⟩, st1)
        have hacp2 : AllocCallPreserved sm sf := by assumption
        have hevs2 : FreeOnlyEvs w := by assumption
        refine SepWP.mono (post := fun sf2 Pf2 =>
          VmPreserved sf sf2 ∧
          (Pf2 ⊢ (((sm.sp + 232#64) ↦₆₄ stA) ∗ memRegion (stA + 8#64) 384 ∗
              (memRegion (sm.sp + 2752#64) 384 ∗ memRegion (sm.sp + 3136#64) 16) ∗
              copyScratchStackAt sm.sp (copyFullScratchCt2 sc d) ∗
              epilogueStoreStackPart1At sm.sp
                { (epilogueStackOfSplit928 d stA k.w200 k.w208) with
                  we0 := k.we0, w3c0 := k.w3c0, w3c8 := k.w3c8 }) ∗
            A.pool lim (M.stepEvents w st1) sf ∗
            ((memRegion (sm.sp - 19552#64) 15424 ∗ stackAt sm.sp dropGluePoly16Stack) ∗ Rest)) ∧
          sf2.sp = sm.sp ∧ AllocCallPreserved sf sf2 ∧
          sf2.readReg64 .x19 = sm.readReg64 .x19 ∧ sf2.readReg64 .x23 = 4#64 ∧
          sf2.readReg64 .x24 = sm.readReg64 .x24 ∧ sf2.readReg64 .x28 = sm.readReg64 .x28 ∧
          sf2.readReg64 .x29 = sm.readReg64 .x29 ∧ TraceCalleeSaved sf2 sm) ?_
          (fun sf2 Pf2 _ _ ⟨hvm3, hPf2, hsp2, hacp3, hx19_2, hx23_2, hx24_2, hx28_2, hx29_2, htr2⟩ =>
            ⟨w, hevs2, by
                dsimp only [d, mkSplit928Ct2Sampled, copyScratchStackAt, copyFullScratchCt2,
                  copyFullScratch, epilogueStoreStackPart1At, epilogueStackOfSplit928,
                  Words16.toList, BitVec.ofNat_eq_ofNat] at hPf2
                simp only [wordsAt_16, BitVec.add_assoc, BitVec.reduceAdd] at hPf2
                rw [A.pool_of_vmPreserved hvm3]
                exact hPf2,
              hsp2, hacp1.trans (hacp2.trans hacp3),
              hx19_2.trans hx19m, hx23_2, hx24_2.trans hx24m,
              hx28_2.trans hx28m, hx29_2.trans hx29m, htr2.trans htrm⟩)
        dsimp only [d, mkSplit928Ct2Sampled, copyScratchStackAt, copyFullScratchCt2, copyFullScratch,
          epilogueStoreStackPart1At, epilogueStackOfSplit928, Words16.toList]
        simp only [wordsAt_16, BitVec.add_assoc, BitVec.reduceAdd]
        by_vm_steps_nest (
          wp_steps
          dsimp only [AllocCallPreserved, TraceCalleeSaved, Reg.x19, Reg.x23, Reg.x24, Reg.x28, Reg.x29]
          wp_done
        )
      )
  · rw [← hsplit]
    have h2752_mr : memRegion (s_in.sp + 2752#64) 384 ∗ memRegion (s_in.sp + 3136#64) 16 ⊢
        memRegion (s_in.sp + 2752#64) 400 := by
      rw [ProofLib.memRegion_split' (b := s_in.sp + 2752#64) (n := 384) (k := 16)
            (b' := s_in.sp + 3136#64) rfl (by bv_omega) (by decide)]
      exact Entails.refl _
    refine Entails.trans (Entails.of_eq (show _ =
      ((s_in.sp + 232#64) ↦₆₄ stA) ∗ memRegion (stA + 8#64) 384 ∗
      (memRegion (s_in.sp + 2752#64) 384 ∗ memRegion (s_in.sp + 3136#64) 16) ∗
      copyScratchStackAt s_in.sp (copyFullScratchCt2 sc d) ∗
      epilogueStoreStackPart1At s_in.sp
        { (epilogueStackOfSplit928 d stA k.w200 k.w208) with we0 := k.we0, w3c0 := k.w3c0, w3c8 := k.w3c8 } ∗
      A.pool lim _ sf ∗ stackAt s_in.sp statesRecvCalleeStackX ∗ Rest by sep_ac_rfl)) ?_
    exact sepConj_mono_right (sepConj_mono_right (sepConj_mono_left h2752_mr))

/-! ## 2. Path 5c Epilogue Convergence (`+16596 -> +16800 -> +17464 -> +18892 -> +18996`) -/

theorem ct1Sampled_copy_some_ack_part2a_placed [LibsignalPlacement]
    {ext : String → Option (State → State)}
    (hmemcpy : HookSat (Rust.withPanics ext) spqrMemcpySym (withVmPreserved sessionMemcpySpec))
    (s_in : State) (fsp w0 w8 w16 : BitVec 64) (bs352_976 : List (BitVec 8))
    (c_1352 c_ca0 : Words5) (Rest : SepProp) (h976_len : bs352_976.length = 352)
    (hfsp_align : (fsp &&& 15#64 == 0#64) = true)
    (hpc : s_in.pc = (blkPl_332).base + 16596#64) (hrun : s_in.status = .Running)
    (hsp : s_in.sp = fsp) (hx23 : s_in.readReg64 .x23 = 4#64) (hx28 : s_in.readReg64 .x28 = fsp + 3272#64) :
    SepWP (lsProg_332 (Rust.withPanics ext)) ((blkPl_332).base + 16800#64) s_in
      (mid376At (fsp + 976#64) w0 w8 w16 bs352_976 ∗ wordsAt (fsp + 1352#64) c_1352.toList ∗
        wordsAt (fsp + 3232#64) c_ca0.toList ∗ memRegion (fsp + 3272#64) 376 ∗
        stackAt fsp statesRecvCalleeStackX ∗ Rest)
      (fun sf Pf =>
        VmPreserved s_in sf ∧
        (Pf ⊢ mid376At (fsp + 976#64) w0 w8 w16 bs352_976 ∗ wordsAt (fsp + 1352#64) c_1352.toList ∗
          wordsAt (fsp + 3232#64) c_1352.toList ∗ mid376At (fsp + 3272#64) w0 w8 w16 bs352_976 ∗
          stackAt fsp statesRecvCalleeStackX ∗ Rest) ∧
        sf.sp = fsp ∧ sf.readReg64 .x8 = 3#64 ∧ sf.readReg64 .x19 = s_in.readReg64 .x19 ∧
        sf.readReg64 .x28 = fsp + 3272#64 ∧ sf.readReg64 .x29 = s_in.readReg64 .x29 ∧
        TraceCalleeSaved sf s_in) := by
  subst hsp
  have hmemcpy_raw : subroutine_ok (lsProg_332 (Rust.withPanics ext))
      (lsρ spqrMemcpySym) (withVmPreserved (sessionMemcpySpec 4096)) :=
    spqr_hook_ok_of_mem (sym := spqrMemcpySym) hmemcpy
  have hsplit := stackAt_statesRecvCallee_eq_allocHook' s_in.sp
  have hmid376_len : (mid376Bytes w0 w8 w16 bs352_976).length = 376 :=
    mid376Bytes_length w0 w8 w16 h976_len
  rw [mid376At_eq_pointsToBytes (s_in.sp + 976#64) w0 w8 w16 bs352_976,
      mid376At_eq_pointsToBytes (s_in.sp + 3272#64) w0 w8 w16 bs352_976,
      hsplit, ← hmid376_len]
  dsimp only [lsProg_332, lsρ, spqrMemcpySym, BitVec.ofNat_eq_ofNat] at hpc hmemcpy_raw ⊢
  dsimp only [Words5.toList, withVmPreserved, sessionMemcpySpec, allocHookStack] at hmemcpy_raw ⊢
  simp only [wordsAt_5, BitVec.add_assoc, BitVec.reduceAdd, hx23, hx28]
  refine seq_vm_cont (mid := lsmpl.ρ "memcpy") ?_
  by_vm_steps_nest (
    wp_steps
    refine SepWP.done rfl hrun ⟨by simp only [wp_norm, arm64_norm], fun _ => ?_⟩
    wp_call hmemcpy_raw (s_in.sp + 3272#64, s_in.sp + 976#64, mid376Bytes w0 w8 w16 bs352_976)
    have hvm_all : VmPreserved s_in sf := by assumption
    refine SepWP.mono (post := fun sf2 Pf2 =>
      VmPreserved sf sf2 ∧ (Pf2 ⊢ _) ∧ sf2.sp = s_in.sp ∧ sf2.readReg64 .x8 = 3#64 ∧
      sf2.readReg64 .x19 = s_in.readReg64 .x19 ∧ sf2.readReg64 .x28 = s_in.sp + 3272#64 ∧
      sf2.readReg64 .x29 = s_in.readReg64 .x29 ∧ TraceCalleeSaved sf2 s_in) ?_
      (fun _ _ _ _ ⟨hvm2, hrest⟩ => ⟨hvm_all.trans hvm2, hrest⟩)
    by_vm_steps_nest (wp_steps; dsimp only [TraceCalleeSaved, Reg.x8, Reg.x19, Reg.x28, Reg.x29]; wp_done)
  )

theorem ct1Sampled_copy_some_ack_part2a_pool_placed [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {ext : String → Option (State → State)}
    (hmemcpy : HookSat (Rust.withPanics ext) spqrMemcpySym (withVmPreserved sessionMemcpySpec))
    (st_cost : M.σ) (s_in : State) (fsp w0 w8 w16 : BitVec 64) (bs352_976 : List (BitVec 8))
    (c_1352 c_ca0 : Words5) (Rest : SepProp) (h976_len : bs352_976.length = 352)
    (hfsp_align : (fsp &&& 15#64 == 0#64) = true)
    (hpc : s_in.pc = (blkPl_332).base + 16596#64) (hrun : s_in.status = .Running)
    (hsp : s_in.sp = fsp) (hx23 : s_in.readReg64 .x23 = 4#64) (hx28 : s_in.readReg64 .x28 = fsp + 3272#64) :
    SepWP (lsProg_332 (Rust.withPanics ext)) ((blkPl_332).base + 16800#64) s_in
      (mid376At (fsp + 976#64) w0 w8 w16 bs352_976 ∗ wordsAt (fsp + 1352#64) c_1352.toList ∗
        wordsAt (fsp + 3232#64) c_ca0.toList ∗ memRegion (fsp + 3272#64) 376 ∗
        A.pool lim st_cost s_in ∗ stackAt fsp statesRecvCalleeStackX ∗ Rest)
      (fun sf Pf =>
        VmPreserved s_in sf ∧
        (Pf ⊢ mid376At (fsp + 976#64) w0 w8 w16 bs352_976 ∗ wordsAt (fsp + 1352#64) c_1352.toList ∗
          wordsAt (fsp + 3232#64) c_1352.toList ∗ mid376At (fsp + 3272#64) w0 w8 w16 bs352_976 ∗
          A.pool lim st_cost sf ∗ stackAt fsp statesRecvCalleeStackX ∗ Rest) ∧
        sf.sp = fsp ∧ sf.readReg64 .x8 = 3#64 ∧ sf.readReg64 .x19 = s_in.readReg64 .x19 ∧
        sf.readReg64 .x28 = fsp + 3272#64 ∧ sf.readReg64 .x29 = s_in.readReg64 .x29 ∧
        TraceCalleeSaved sf s_in) := by
  have hw : SepWP (lsProg_332 (Rust.withPanics ext)) ((blkPl_332).base + 16800#64) s_in _
      (fun sf Pf =>
        VmPreserved s_in sf ∧
        (Pf ⊢ mid376At (fsp + 976#64) w0 w8 w16 bs352_976 ∗ wordsAt (fsp + 1352#64) c_1352.toList ∗
          wordsAt (fsp + 3232#64) c_1352.toList ∗ mid376At (fsp + 3272#64) w0 w8 w16 bs352_976 ∗
          A.pool lim st_cost sf ∗ stackAt fsp statesRecvCalleeStackX ∗ Rest) ∧
        sf.sp = fsp ∧ sf.readReg64 .x8 = 3#64 ∧ sf.readReg64 .x19 = s_in.readReg64 .x19 ∧
        sf.readReg64 .x28 = fsp + 3272#64 ∧ sf.readReg64 .x29 = s_in.readReg64 .x29 ∧
        TraceCalleeSaved sf s_in) :=
    SepWP.mono
      (ct1Sampled_copy_some_ack_part2a_placed hmemcpy s_in fsp w0 w8 w16 bs352_976 c_1352 c_ca0
        (A.pool lim st_cost s_in ∗ Rest) h976_len hfsp_align hpc hrun hsp hx23 hx28)
      fun sf _ _ _ ⟨hvm, hPf, hq⟩ =>
        ⟨hvm, Entails.trans hPf (Entails.of_eq (by rw [A.pool_transport lim st_cost s_in sf hvm]; sep_ac_rfl)), hq⟩
  exact SepWP.weaken_pre (Entails.of_eq (by sep_ac_rfl)) hw

set_option maxHeartbeats 1600000 in
theorem ct1Sampled_copy_some_ack_part2b_placed [LibsignalPlacement]
    {ext : String → Option (State → State)} (s_in : State) (fsp stA outA : BitVec 64)
    (c_enc : Words50) (g : AuthWords) (epoch v576 v584 v592 : BitVec 64)
    (bs352_576 : List (BitVec 8)) (sc : CopyScratchStack) (k : EpilogueStoreStack) (Rest : SepProp)
    (hfsp_align : (fsp &&& 15#64 == 0#64) = true)
    (hpc : s_in.pc = (blkPl_332).base + 16800#64) (hrun : s_in.status = .Running)
    (hsp : s_in.sp = fsp) (hx8 : s_in.readReg64 .x8 = 3#64) (hx19 : s_in.readReg64 .x19 = outA) :
    let d := mkSplit928Ct2Sampled c_enc g epoch (s_in.readReg64 .x2)
      k.wf8 k.w3c0 k.w3c8 k.w100 (mid376Bytes v576 v584 v592 bs352_576) k.tail
    SepWP (lsProg_332 (Rust.withPanics ext)) ((blkPl_332).base + 18996#64) s_in
      (copyScratchStackAt fsp (copyFullScratchCt2 sc d) ∗
        epilogueStoreStackPart1At fsp
          { (epilogueStackOfSplit928 d stA k.w200 k.w208) with we0 := k.we0, w3c0 := k.w3c0, w3c8 := k.w3c8 } ∗
        ((fsp + 232#64) ↦₆₄ stA) ∗ ((fsp + 512#64) ↦₆₄ k.w200) ∗ ((fsp + 520#64) ↦₆₄ k.w208) ∗
        wordsAt (fsp + 528#64) k.tail.toList ∗ mid376At (fsp + 576#64) v576 v584 v592 bs352_576 ∗
        statesRecvRoPlacedAt ∗ Rest)
      (fun sf Pf =>
        VmPreserved s_in sf ∧
        (Pf ⊢ copyScratchStackAt fsp (copyFullScratchCt2 sc d) ∗
          epilogueStoreStackPart1At fsp (epilogueStackOfSplit928 d noneCap k.w200 k.w208) ∗
          epilogueStoreStackPart2At fsp (epilogueStackOfSplit928 d noneCap k.w200 k.w208) ∗
          statesRecvRoPlacedAt ∗ Rest) ∧
        epilogueRegsEqSplit928 sf d ∧ sf.sp = fsp ∧ sf.readReg64 .x19 = outA ∧
        sf.readReg64 .x29 = s_in.readReg64 .x29 ∧ TraceCalleeSaved sf s_in) := by
  intro d; subst hsp hx19
  dsimp only [lsProg_332, statesRecvRoPlacedAt, unchunkedSendCt2PlacedRoAt,
    lsLogFilterAddr, BitVec.ofNat_eq_ofNat] at hpc ⊢
  dsimp only [epilogueStoreStackPart2At]
  rw [show (epilogueStackOfSplit928 d noneCap k.w200 k.w208).mid =
      mid376Bytes v576 v584 v592 bs352_576 from rfl,
      ← mid376At_eq_pointsToBytes (s_in.sp + 576#64) v576 v584 v592 bs352_576]
  dsimp only [d, mkSplit928Ct2Sampled, copyScratchStackAt, copyFullScratchCt2, copyFullScratch,
    epilogueStoreStackPart1At, epilogueStackOfSplit928, epilogueRegsEqSplit928,
    EpilogueStoreStack.tail, mid376At, noneCap, Words16.toList, Words5.toList]
  simp only [wordsAt_16, wordsAt_5, BitVec.add_assoc, BitVec.reduceAdd, hx8]
  refine seq_vm_cont (mid := (blkPl_332).base + 17468#64) ?_
  by_vm_steps_nest (
    wp_steps
    refine SepWP.done rfl (by simp only [wp_norm, arm64_norm]; exact hrun)
      ⟨by simp only [wp_norm, arm64_norm], fun hvmm => ?_⟩
    refine step_adrp_vm hvmm (blkPC_332_pairStep_0x443c inferInstance (blkPl_332).base
      (Rust.withPanics ext) rfl rfl (by simp only [wp_norm, arm64_norm]; exact hrun)) ?_
    by_vm_steps_nest (wp_steps; dsimp only [TraceCalleeSaved, Reg.x19, Reg.x29]; wp_done)
  )

theorem ct1Sampled_copy_some_ack_part2b_pool_placed [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {ext : String → Option (State → State)}
    (st_cost : M.σ) (s_in : State) (fsp stA outA : BitVec 64)
    (c_enc : Words50) (g : AuthWords) (epoch v576 v584 v592 : BitVec 64)
    (bs352_576 : List (BitVec 8)) (sc : CopyScratchStack) (k : EpilogueStoreStack) (Rest : SepProp)
    (hfsp_align : (fsp &&& 15#64 == 0#64) = true)
    (hpc : s_in.pc = (blkPl_332).base + 16800#64) (hrun : s_in.status = .Running)
    (hsp : s_in.sp = fsp) (hx8 : s_in.readReg64 .x8 = 3#64) (hx19 : s_in.readReg64 .x19 = outA) :
    let d := mkSplit928Ct2Sampled c_enc g epoch (s_in.readReg64 .x2)
      k.wf8 k.w3c0 k.w3c8 k.w100 (mid376Bytes v576 v584 v592 bs352_576) k.tail
    SepWP (lsProg_332 (Rust.withPanics ext)) ((blkPl_332).base + 18996#64) s_in
      (copyScratchStackAt fsp (copyFullScratchCt2 sc d) ∗
        epilogueStoreStackPart1At fsp
          { (epilogueStackOfSplit928 d stA k.w200 k.w208) with we0 := k.we0, w3c0 := k.w3c0, w3c8 := k.w3c8 } ∗
        ((fsp + 232#64) ↦₆₄ stA) ∗ ((fsp + 512#64) ↦₆₄ k.w200) ∗ ((fsp + 520#64) ↦₆₄ k.w208) ∗
        wordsAt (fsp + 528#64) k.tail.toList ∗ mid376At (fsp + 576#64) v576 v584 v592 bs352_576 ∗
        statesRecvRoPlacedAt ∗ A.pool lim st_cost s_in ∗ Rest)
      (fun sf Pf =>
        VmPreserved s_in sf ∧
        (Pf ⊢ copyScratchStackAt fsp (copyFullScratchCt2 sc d) ∗
          epilogueStoreStackPart1At fsp (epilogueStackOfSplit928 d noneCap k.w200 k.w208) ∗
          epilogueStoreStackPart2At fsp (epilogueStackOfSplit928 d noneCap k.w200 k.w208) ∗
          statesRecvRoPlacedAt ∗ A.pool lim st_cost sf ∗ Rest) ∧
        epilogueRegsEqSplit928 sf d ∧ sf.sp = fsp ∧ sf.readReg64 .x19 = outA ∧
        sf.readReg64 .x29 = s_in.readReg64 .x29 ∧ TraceCalleeSaved sf s_in) := by
  intro d
  exact SepWP.mono
    (ct1Sampled_copy_some_ack_part2b_placed s_in fsp stA outA c_enc g epoch
      v576 v584 v592 bs352_576 sc k (A.pool lim st_cost s_in ∗ Rest)
      hfsp_align hpc hrun hsp hx8 hx19)
    fun sf _ _ _ ⟨hvm, hPf, hq⟩ =>
      ⟨hvm, Entails.trans hPf (Entails.of_eq (by rw [A.pool_transport lim st_cost s_in sf hvm])), hq⟩

end LibsignalBinary.Proofs.SpqrV1.States.Recv.ArmCt1SampledPart6PlacedBudget
