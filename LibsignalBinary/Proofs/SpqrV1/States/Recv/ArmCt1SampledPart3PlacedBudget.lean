/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Heap.IfaceBudgetLemmas
public import LibsignalBinary.Heap.SpecBudget
public import LibsignalBinary.Proofs.Placed.BudgetPoolSync
public import LibsignalBinary.Proofs.Placed.BudgetVmSteps
public meta import LibsignalBinary.Proofs.Placed.BudgetVmSteps -- shake: keep
public import LibsignalBinary.Proofs.Placed.ElfLsRetAddr
public import LibsignalBinary.Proofs.SpqrV1.Poly.AddChunk.DefsBudget
public import LibsignalBinary.Proofs.SpqrV1.States.Leaves.Batch2DefsPlacedBudget
public import LibsignalBinary.Proofs.SpqrV1.States.Recv.ArmCt1SampledPart3Placed
public import LibsignalBinary.Proofs.SpqrV1.States.Recv.ArmCt1SampledPart3PlacedBudgetAux
public import LibsignalBinary.Proofs.SpqrV1.States.Recv.ArmNoHeaderReceivedStepsPlacedBudgetAux
public import LibsignalBinary.Proofs.SpqrV1.Unchunked.SendCt2PlacedBudget
import LibsignalBinary.Proofs.Common.SharedHelpers
meta import LibsignalBinary.Proofs.Common.SharedHelpers -- shake: keep
import LibsignalBinary.Proofs.SpqrV1.States.FromPb.Defs
import LibsignalBinary.Proofs.SpqrV1.States.Leaves.DefsPlaced
import LibsignalBinary.Proofs.SpqrV1.States.Leaves.SendChunk1
import LibsignalBinary.Proofs.SpqrV1.States.Leaves.UnchunkedRecvEk
import LibsignalBinary.Proofs.SpqrV1.States.Recv.ArmCt1SampledPart1
import LibsignalBinary.Proofs.SpqrV1.States.Recv.ArmCt1SampledPart2
import LibsignalBinary.Proofs.SpqrV1.States.Recv.ArmCt1SampledPart3
import LibsignalBinary.Proofs.SpqrV1.States.Recv.CodeSymFetch2Placed
import LibsignalBinary.Proofs.SpqrV1.States.Recv.CodeSymFetch3Placed
import LibsignalBinary.Proofs.SpqrV1.States.Recv.DispatchPlacedBudget
import ProofLib.SepLogic.WP.Apply
import ProofLib.SepLogic.WP.FrameAuto
import ProofLib.SepLogic.WPp

/-!
# `<States>::recv` (Block `332`) — `.ct1Sampled` Arm, Part 3 (Budget-Threaded)

Budget-threaded subroutine call helpers (Blocks `419`, `418`, `347`, `382`), `recv_ek_chunk`
common prefix (`+11404 -> +11496`), and `Option<Vec<u8>>` decode branch steppers (`+11496`).
-/

@[expose] public section

set_option autoImplicit false

namespace LibsignalBinary.Proofs.SpqrV1.States.Recv.ArmCt1SampledPart3PlacedBudget

open LibsignalBinary.Proofs.SpqrV1.States.Recv (subroutine_ok_post_lscl subroutine_ok_post_lscro)

open Arm64 ProofLib ProofLib.ProgramReflection
open LibsignalBinary.Proofs.Placed.ElfLsRetAddr (LsRetAddr624)
open scoped CryptoVerification.RustHeap CryptoVerification.LibsignalTripleRatchet
open CryptoGames.LibsignalSession (ShaCompress)
open CryptoVerification (
  IsLsBlockProg LibsignalCodeLoaded LibsignalHooks LibsignalPlacement
  blkPl_332 blkPl_347 blkPl_382 blkPl_418 blkPl_419
  libsignalMutatedBlocks libsignalSessionCode lsProg_332 lsmpl lsρ withLsCodeLoaded
)
open CryptoVerification.RustHeap (RustAlloc allocHookStack vecU8)
open CryptoVerification.LibsignalTripleRatchet (
  LibsignalCodeRoLoaded sessionMemcpySpec withLsCodeRoLoaded
)
open CryptoVerification.LibsignalTripleRatchetRepr (noneCap)
open CryptoVerification.LibsignalSpqrV1 (
  Bytes Chunk Mac MlKem PolyDecoder PolyEncoder spqrAuthApi spqrPolyApi
)
open CryptoVerification.LibsignalSpqrV1.Unchunked.SendCt (Ct1SentEkReceived Ct2Sent)
open CryptoVerification.SpqrV1.Alloc (spqrMemcpySym spqr_hook_ok_of_mem)
open CryptoVerification.SpqrV1.Drop (unchunkedCt1SentEkReceivedAt unchunkedCt2SentAt)
open CryptoVerification.SpqrV1.GF.Mul2U16 (tokenInitPlacedAt)
open CryptoVerification.SpqrV1.GF.UnacceleratedMul (reduceTablePlacedAt)
open CryptoVerification.SpqrV1.Poly (chunkAt polyDecoderAt polyEncoderAt)
open CryptoVerification.SpqrV1.Poly.AddChunk (
  AddChunkGhost PolyDecoderStrictSorted addChunkStackX addChunkTotal
)
open CryptoVerification.SpqrV1.Unchunked (unchunkedSendCt2PlacedRoAt)
open CryptoVerification.SpqrV1.States.Leaves (
  PolyDecoderDecodedMessageGhost Relocatable SendCt2EncoderGhost UnchunkedSendCt2Ghost
  optVecU8At optVecU8At_none_entails_memRegion_24 polyDecoderDecodedMessageStack
  relocatedHeap relocatedHeap_recompose sendCt2EncoderStack
  subroutine_ok_withLsCodeRoLoaded_of_withLsCodeLoaded unchunkedSendCt2Stack
  vecU8_entails_slice_and_tail vecU8_of_slice_and_tail wordsAt wordsAt_16
)
open CryptoVerification.SpqrV1.States.RecvCt2Chunk (polyDecodedMessageStackX)
open CryptoVerification.SpqrV1.States.Recv (
  TraceCalleeSaved Words16 cap_add_one_beq_zero_false memRegion_128_entails_words16
  sp_sub_144_add_48 sp_sub_4192_sub_48 sp_sub_4240_add_2752 sp_sub_4240_add_3272
  sp_sub_4240_add_3696 sp_sub_4240_add_3832 sp_sub_4240_add_3840 sp_sub_4240_add_3848
  sp_sub_4240_add_3856 sp_sub_4240_add_4096 sp_sub_4240_add_4144 sp_sub_4240_add_48
  sp_sub_96_add_16 sp_sub_96_add_32 sp_sub_96_add_48 sp_sub_96_add_64
  sp_sub_96_add_80 sp_sub_96_sub_4096 stackAt_statesRecvCallee_eq_addChunk
  stackAt_statesRecvCallee_eq_allocHook' stackAt_statesRecvCallee_eq_polyDecodedMessage
  statesRecvCalleeStackX statesRecvRoPlacedAt
)
open LibsignalBinary.Heap (
  AllocCallPreserved AllocCostModel AllocEvent BudgetLimits FitsEnv RustCliAllocBudget VmPreserved
)
open LibsignalBinary.Heap.SpecBudget (withVmPreserved)
open LibsignalBinary.Proofs.SpqrV1.Poly.AddChunk.DefsBudget (AddChunkEnv addChunkSpecX)
open LibsignalBinary.Proofs.SpqrV1.States.Leaves.Batch2DefsPlacedBudget (
  PolyDecoderDecodedMessagePostEnv PolyDecoderDecodedMessagePreEnv
  SendCt2EncoderPostEnv SendCt2EncoderPreEnv
  polyDecoderDecodedMessagePlacedSpec polyDecoderDecodedMessagePlacedSpecOfPrePostEnv
  sendCt2EncoderSpec sendCt2EncoderSpecOfPrePostEnv
)
open LibsignalBinary.Proofs.SpqrV1.States.Recv.ArmNoHeaderReceivedStepsPlacedBudgetAux (seq_vm_cont)
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
  sp_sub_4240_add_4144 sp_sub_4240_add_3856 sp_sub_4240_add_3272
  sp_sub_4240_add_2752 sp_sub_4240_add_3696 sp_sub_4240_add_3832
  sp_sub_4240_add_3840 sp_sub_4240_add_3848 lsmpl_base_332_eq
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

/-! ## 1. Budget-Threaded Subroutine Call Helpers (`Blocks 419, 418, 347, 382`) -/

theorem call_addChunkX_statesRecv_placed [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {prog : Program} {i : Nat} {H : LibsignalHooks} [IsLsBlockProg prog i H]
    {entry ret_pc target_pc : BitVec 64}
    (hcall : subroutine_ok prog entry (withLsCodeLoaded lsmpl (addChunkSpecX M A lim)))
    (st_cost : M.σ) (decA chunkA : BitVec 64) (dec : PolyDecoder) (chunk : Chunk)
    (hsorted : PolyDecoderStrictSorted dec)
    (hfits : FitsEnv M lim st_cost (AddChunkEnv ⟨decA, chunkA, dec, chunk⟩))
    {s0 s s_pool : State} {sp_call : BitVec 64} {P Frame : SepProp}
    {post : State → SepProp → Prop} {oom : State → SepProp}
    (hcl : LibsignalCodeLoaded lsmpl s.mem) (hpc : s.pc = entry) (hrun : s.status = .Running)
    (hsp : s.sp = sp_call) (hsp_align : (sp_call &&& 15#64 == 0#64) = true)
    (hlr : s.readReg64 Reg.lr = ret_pc) (htrace : TraceCalleeSaved s s0)
    (hx0 : s.readReg64 Reg.x0 = decA) (hx1 : s.readReg64 Reg.x1 = chunkA)
    (hsplit : P = (polyDecoderAt A.repAlloc decA dec ∗ chunkAt chunkA chunk ∗
      A.pool lim st_cost s_pool ∗ stackAt sp_call addChunkStackX) ∗ Frame)
    (hpool : A.pool lim st_cost s_pool = A.pool lim st_cost s := by simp only [arm64_norm])
    (hnext : ∀ (sf : State) (evs : List AllocEvent),
      sf.pc = ret_pc → sf.status = .Running → sf.sp = sp_call →
      AllocCallPreserved s sf → CalleeSavedPreserved s sf →
      TraceCalleeSaved sf s0 → LibsignalCodeLoaded lsmpl sf.mem →
      AddChunkEnv ⟨decA, chunkA, dec, chunk⟩ evs →
      PolyDecoderStrictSorted (addChunkTotal dec chunk) →
      SepWP prog target_pc sf
        ((polyDecoderAt A.repAlloc decA (addChunkTotal dec chunk) ∗ chunkAt chunkA chunk ∗
          A.pool lim (M.stepEvents evs st_cost) sf ∗ stackAt sp_call addChunkStackX) ∗ Frame)
        post oom)
    (hi : i < 619 := by decide) (hunmut : (i ∈ libsignalMutatedBlocks) = false := by decide) :
    SepWP prog target_pc s P post oom := by
  have hcall_cl := subroutine_ok_post_lscl hcall hi hunmut
  refine SepWP.call_subroutine_frame hcall_cl
    (x := (⟨decA, chunkA, dec, chunk⟩, st_cost)) (F := Frame)
    hpc hrun (by rw [State.spAligned, hsp]; exact hsp_align) hlr ?_
    (fun _ _ _ h => by dsimp only [withLsCodeLoaded, addChunkSpecX] at h; exact ((satisfies_pure_sepConj _ _ _).mp h).1)
    (fun _ _ _ _ h => by dsimp only [withLsCodeLoaded, addChunkSpecX] at h; exact ((satisfies_pure_sepConj _ _ _).mp h).1)
    (fun sf hpc_sf hrun_sf hsp_sf hcs_sf => ?_)
    (fun _ _ _ h => by dsimp only [withLsCodeLoaded, addChunkSpecX] at h; exact False.elim ((satisfies_pure_sepConj _ _ _).mp h).1)
  · intro R' hm
    rw [hsplit, hpool] at hm
    dsimp only [withLsCodeLoaded, addChunkSpecX]; rw [hsp]
    have hm' : s.mem ⊨ ⌜LibsignalCodeLoaded lsmpl s.mem⌝ ∗
        ⌜s.readReg64 .x0 = decA ∧ s.readReg64 .x1 = chunkA ∧ PolyDecoderStrictSorted dec ∧
          FitsEnv M lim st_cost (AddChunkEnv ⟨decA, chunkA, dec, chunk⟩)⌝ ∗
        ((polyDecoderAt A.repAlloc decA dec ∗ chunkAt chunkA chunk ∗
          A.pool lim st_cost s ∗ stackAt sp_call addChunkStackX) ∗ Frame ∗ R') := by
      rw [satisfies_pure_sepConj]
      exact ⟨hcl, by
        rw [satisfies_pure_sepConj]
        exact ⟨⟨hx0, hx1, hsorted, hfits⟩, by simpa only [sepConj_assoc] using hm⟩⟩
    exact Satisfies.mono (Entails.of_eq (by sep_ac_rfl)) hm'
  · dsimp only [withLsCodeLoaded, addChunkSpecX]; rw [hsp, sepConj_assoc]
    refine SepWP.pure_elim fun hcl_sf => ?_
    rw [sepExists_sepConj_left]; refine SepWP.exists_elim fun evs => ?_
    rw [sepConj_assoc]; refine SepWP.pure_elim fun ⟨htr, hacp, hevs, hsorted'⟩ => ?_
    exact hnext sf evs hpc_sf hrun_sf (hsp_sf.trans hsp) hacp hcs_sf
      ⟨htr.trans htrace.1, hcs_sf.2.2.2.2.2.2.2.2.2.2.2.trans htrace.2⟩ hcl_sf hevs hsorted'

theorem call_addChunkX_statesRecv_cro_placed [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {prog : Program} {i : Nat} {H : LibsignalHooks} [IsLsBlockProg prog i H]
    {entry ret_pc target_pc : BitVec 64}
    (hcall : subroutine_ok prog entry (withLsCodeLoaded lsmpl (addChunkSpecX M A lim)))
    (st_cost : M.σ) (decA chunkA : BitVec 64) (dec : PolyDecoder) (chunk : Chunk)
    (hsorted : PolyDecoderStrictSorted dec)
    (hfits : FitsEnv M lim st_cost (AddChunkEnv ⟨decA, chunkA, dec, chunk⟩))
    {s0 s s_pool : State} {sp_call : BitVec 64} {P Frame : SepProp}
    {post : State → SepProp → Prop} {oom : State → SepProp}
    (hcro : LibsignalCodeRoLoaded lsmpl s.mem) (hpc : s.pc = entry) (hrun : s.status = .Running)
    (hsp : s.sp = sp_call) (hsp_align : (sp_call &&& 15#64 == 0#64) = true)
    (hlr : s.readReg64 Reg.lr = ret_pc) (htrace : TraceCalleeSaved s s0)
    (hx0 : s.readReg64 Reg.x0 = decA) (hx1 : s.readReg64 Reg.x1 = chunkA)
    (hsplit : P = (polyDecoderAt A.repAlloc decA dec ∗ chunkAt chunkA chunk ∗
      A.pool lim st_cost s_pool ∗ stackAt sp_call addChunkStackX) ∗ Frame)
    (hpool : A.pool lim st_cost s_pool = A.pool lim st_cost s := by simp only [arm64_norm])
    (hnext : ∀ (sf : State) (evs : List AllocEvent),
      sf.pc = ret_pc → sf.status = .Running → sf.sp = sp_call →
      AllocCallPreserved s sf → CalleeSavedPreserved s sf →
      TraceCalleeSaved sf s0 → LibsignalCodeRoLoaded lsmpl sf.mem →
      AddChunkEnv ⟨decA, chunkA, dec, chunk⟩ evs →
      PolyDecoderStrictSorted (addChunkTotal dec chunk) →
      SepWP prog target_pc sf
        ((polyDecoderAt A.repAlloc decA (addChunkTotal dec chunk) ∗ chunkAt chunkA chunk ∗
          A.pool lim (M.stepEvents evs st_cost) sf ∗ stackAt sp_call addChunkStackX) ∗ Frame)
        post oom)
    (hi : i < 619 := by decide) (hunmut : (i ∈ libsignalMutatedBlocks) = false := by decide) :
    SepWP prog target_pc s P post oom := by
  have hcall_cro := subroutine_ok_post_lscro
    (subroutine_ok_withLsCodeRoLoaded_of_withLsCodeLoaded hcall) hi hunmut
  refine SepWP.call_subroutine_frame hcall_cro
    (x := (⟨decA, chunkA, dec, chunk⟩, st_cost)) (F := Frame)
    hpc hrun (by rw [State.spAligned, hsp]; exact hsp_align) hlr ?_
    (fun _ _ _ h => by dsimp only [withLsCodeRoLoaded, addChunkSpecX] at h; exact ((satisfies_pure_sepConj _ _ _).mp h).1)
    (fun _ _ _ _ h => by dsimp only [withLsCodeRoLoaded, addChunkSpecX] at h; exact ((satisfies_pure_sepConj _ _ _).mp h).1)
    (fun sf hpc_sf hrun_sf hsp_sf hcs_sf => ?_)
    (fun _ _ _ h => by dsimp only [withLsCodeRoLoaded, addChunkSpecX] at h; exact False.elim ((satisfies_pure_sepConj _ _ _).mp h).1)
  · intro R' hm
    rw [hsplit, hpool] at hm
    dsimp only [withLsCodeRoLoaded, addChunkSpecX]; rw [hsp]
    have hm' : s.mem ⊨ ⌜LibsignalCodeRoLoaded lsmpl s.mem⌝ ∗
        ⌜s.readReg64 .x0 = decA ∧ s.readReg64 .x1 = chunkA ∧ PolyDecoderStrictSorted dec ∧
          FitsEnv M lim st_cost (AddChunkEnv ⟨decA, chunkA, dec, chunk⟩)⌝ ∗
        ((polyDecoderAt A.repAlloc decA dec ∗ chunkAt chunkA chunk ∗
          A.pool lim st_cost s ∗ stackAt sp_call addChunkStackX) ∗ Frame ∗ R') := by
      rw [satisfies_pure_sepConj]
      exact ⟨hcro, by
        rw [satisfies_pure_sepConj]
        exact ⟨⟨hx0, hx1, hsorted, hfits⟩, by simpa only [sepConj_assoc] using hm⟩⟩
    exact Satisfies.mono (Entails.of_eq (by sep_ac_rfl)) hm'
  · dsimp only [withLsCodeRoLoaded, addChunkSpecX]; rw [hsp, sepConj_assoc]
    refine SepWP.pure_elim fun hcro_sf => ?_
    rw [sepExists_sepConj_left]; refine SepWP.exists_elim fun evs => ?_
    rw [sepConj_assoc]; refine SepWP.pure_elim fun ⟨htr, hacp, hevs, hsorted'⟩ => ?_
    exact hnext sf evs hpc_sf hrun_sf (hsp_sf.trans hsp) hacp hcs_sf
      ⟨htr.trans htrace.1, hcs_sf.2.2.2.2.2.2.2.2.2.2.2.trans htrace.2⟩ hcro_sf hevs hsorted'

theorem call_decodedMessage_statesRecv_placed_ofPrePostEnv [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {DecPre DecPost : PolyDecoderDecodedMessageGhost → List AllocEvent → Prop}
    {prog : Program} {i : Nat} {H : LibsignalHooks} [IsLsBlockProg prog i H]
    {entry ret_pc target_pc : BitVec 64}
    (hcall : subroutine_ok prog entry
      (withLsCodeRoLoaded lsmpl (polyDecoderDecodedMessagePlacedSpecOfPrePostEnv M A lim DecPre DecPost)))
    (st_cost : M.σ) (outA decA : BitVec 64) (dec : PolyDecoder) (outMsg : Option Bytes)
    (hsorted : PolyDecoderStrictSorted dec) (hdec : spqrPolyApi.decoded_message dec = .ok outMsg)
    (hfits : FitsEnv M lim st_cost (DecPre ⟨outA, decA, dec, outMsg⟩))
    {s0 s s_pool : State} {sp_call : BitVec 64} {P Frame : SepProp}
    {post : State → SepProp → Prop} {oom : State → SepProp}
    (hcro : LibsignalCodeRoLoaded lsmpl s.mem) (hpc : s.pc = entry) (hrun : s.status = .Running)
    (hsp : s.sp = sp_call) (hsp_align : (sp_call &&& 15#64 == 0#64) = true)
    (hlr : s.readReg64 Reg.lr = ret_pc) (htrace : TraceCalleeSaved s s0)
    (hx8 : s.readReg64 Reg.x8 = outA) (hx0 : s.readReg64 Reg.x0 = decA)
    (hsplit : P = (memRegion outA 24 ∗ polyDecoderAt A.repAlloc decA dec ∗
      tokenInitPlacedAt ∗ reduceTablePlacedAt ∗
      A.pool lim st_cost s_pool ∗ stackAt sp_call polyDecoderDecodedMessageStack) ∗ Frame)
    (hpool : A.pool lim st_cost s_pool = A.pool lim st_cost s := by simp only [arm64_norm])
    (hnext : ∀ (sf : State) (evs : List AllocEvent),
      sf.pc = ret_pc → sf.status = .Running → sf.sp = sp_call →
      CalleeSavedPreserved s sf → TraceCalleeSaved sf s0 →
      LibsignalCodeRoLoaded lsmpl sf.mem → DecPost ⟨outA, decA, dec, outMsg⟩ evs →
      SepWP prog target_pc sf
        ((optVecU8At A.repAlloc outA outMsg ∗ polyDecoderAt A.repAlloc decA dec ∗
          tokenInitPlacedAt ∗ reduceTablePlacedAt ∗
          A.pool lim (M.stepEvents evs st_cost) sf ∗ stackAt sp_call polyDecoderDecodedMessageStack) ∗ Frame)
        post oom)
    (hi : i < 619 := by decide) (hunmut : (i ∈ libsignalMutatedBlocks) = false := by decide) :
    SepWP prog target_pc s P post oom := by
  have hcall_cro := subroutine_ok_post_lscro hcall hi hunmut
  refine SepWP.call_subroutine_frame hcall_cro
    (x := (⟨outA, decA, dec, outMsg⟩, st_cost)) (F := Frame)
    hpc hrun (by rw [State.spAligned, hsp]; exact hsp_align) hlr ?_
    (fun _ _ _ h => by dsimp only [withLsCodeRoLoaded, polyDecoderDecodedMessagePlacedSpecOfPrePostEnv] at h; exact ((satisfies_pure_sepConj _ _ _).mp h).1)
    (fun _ _ _ _ h => by dsimp only [withLsCodeRoLoaded, polyDecoderDecodedMessagePlacedSpecOfPrePostEnv] at h; exact ((satisfies_pure_sepConj _ _ _).mp h).1)
    (fun sf hpc_sf hrun_sf hsp_sf hcs_sf => ?_)
    (fun _ _ _ h => by dsimp only [withLsCodeRoLoaded, polyDecoderDecodedMessagePlacedSpecOfPrePostEnv] at h; exact False.elim ((satisfies_pure_sepConj _ _ _).mp h).1)
  · intro R' hm
    rw [hsplit, hpool] at hm
    dsimp only [withLsCodeRoLoaded, polyDecoderDecodedMessagePlacedSpecOfPrePostEnv]; rw [hsp]
    have hm' : s.mem ⊨ ⌜LibsignalCodeRoLoaded lsmpl s.mem⌝ ∗
        ⌜s.readReg64 .x8 = outA ∧ s.readReg64 .x0 = decA ∧ PolyDecoderStrictSorted dec ∧
          spqrPolyApi.decoded_message dec = .ok outMsg ∧
          FitsEnv M lim st_cost (DecPre ⟨outA, decA, dec, outMsg⟩)⌝ ∗
        ((memRegion outA 24 ∗ polyDecoderAt A.repAlloc decA dec ∗
          tokenInitPlacedAt ∗ reduceTablePlacedAt ∗
          A.pool lim st_cost s ∗ stackAt sp_call polyDecoderDecodedMessageStack) ∗ Frame ∗ R') := by
      rw [satisfies_pure_sepConj]
      exact ⟨hcro, by
        rw [satisfies_pure_sepConj]
        exact ⟨⟨hx8, hx0, hsorted, hdec, hfits⟩, by simpa only [sepConj_assoc] using hm⟩⟩
    exact Satisfies.mono (Entails.of_eq (by sep_ac_rfl)) hm'
  · dsimp only [withLsCodeRoLoaded, polyDecoderDecodedMessagePlacedSpecOfPrePostEnv]; rw [hsp, sepConj_assoc]
    refine SepWP.pure_elim fun hcro_sf => ?_
    rw [sepExists_sepConj_left]; refine SepWP.exists_elim fun evs => ?_
    rw [sepConj_assoc]; refine SepWP.pure_elim fun ⟨htr, hevs⟩ => ?_
    exact hnext sf evs hpc_sf hrun_sf (hsp_sf.trans hsp) hcs_sf
      ⟨htr.trans htrace.1, hcs_sf.2.2.2.2.2.2.2.2.2.2.2.trans htrace.2⟩ hcro_sf hevs

theorem call_decodedMessage_statesRecv_placed [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {prog : Program} {i : Nat} {H : LibsignalHooks} [IsLsBlockProg prog i H]
    {entry ret_pc target_pc : BitVec 64}
    (hcall : subroutine_ok prog entry
      (withLsCodeRoLoaded lsmpl (polyDecoderDecodedMessagePlacedSpec M A lim)))
    (st_cost : M.σ) (outA decA : BitVec 64) (dec : PolyDecoder) (outMsg : Option Bytes)
    (hsorted : PolyDecoderStrictSorted dec) (hdec : spqrPolyApi.decoded_message dec = .ok outMsg)
    (hfits : FitsEnv M lim st_cost (PolyDecoderDecodedMessagePreEnv ⟨outA, decA, dec, outMsg⟩))
    {s0 s s_pool : State} {sp_call : BitVec 64} {P Frame : SepProp}
    {post : State → SepProp → Prop} {oom : State → SepProp}
    (hcro : LibsignalCodeRoLoaded lsmpl s.mem) (hpc : s.pc = entry) (hrun : s.status = .Running)
    (hsp : s.sp = sp_call) (hsp_align : (sp_call &&& 15#64 == 0#64) = true)
    (hlr : s.readReg64 Reg.lr = ret_pc) (htrace : TraceCalleeSaved s s0)
    (hx8 : s.readReg64 Reg.x8 = outA) (hx0 : s.readReg64 Reg.x0 = decA)
    (hsplit : P = (memRegion outA 24 ∗ polyDecoderAt A.repAlloc decA dec ∗
      tokenInitPlacedAt ∗ reduceTablePlacedAt ∗
      A.pool lim st_cost s_pool ∗ stackAt sp_call polyDecoderDecodedMessageStack) ∗ Frame)
    (hpool : A.pool lim st_cost s_pool = A.pool lim st_cost s := by simp only [arm64_norm])
    (hnext : ∀ (sf : State) (evs : List AllocEvent),
      sf.pc = ret_pc → sf.status = .Running → sf.sp = sp_call →
      CalleeSavedPreserved s sf → TraceCalleeSaved sf s0 →
      LibsignalCodeRoLoaded lsmpl sf.mem →
      PolyDecoderDecodedMessagePostEnv ⟨outA, decA, dec, outMsg⟩ evs →
      SepWP prog target_pc sf
        ((optVecU8At A.repAlloc outA outMsg ∗ polyDecoderAt A.repAlloc decA dec ∗
          tokenInitPlacedAt ∗ reduceTablePlacedAt ∗
          A.pool lim (M.stepEvents evs st_cost) sf ∗ stackAt sp_call polyDecoderDecodedMessageStack) ∗ Frame)
        post oom)
    (hi : i < 619 := by decide) (hunmut : (i ∈ libsignalMutatedBlocks) = false := by decide) :
    SepWP prog target_pc s P post oom :=
  call_decodedMessage_statesRecv_placed_ofPrePostEnv hcall st_cost outA decA dec outMsg
    hsorted hdec hfits hcro hpc hrun hsp hsp_align hlr htrace hx8 hx0 hsplit hpool hnext hi hunmut

theorem call_sendCt2_statesRecv_placed_ofPrePostEnv [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {F : ShaCompress} {K : MlKem}
    {ScPre ScPost : UnchunkedSendCt2Ghost F → List AllocEvent → Prop}
    {prog : Program} {i : Nat} {H : LibsignalHooks} [IsLsBlockProg prog i H]
    {entry ret_pc target_pc : BitVec 64}
    (hcall : subroutine_ok prog entry
      (withLsCodeLoaded lsmpl
        (unchunkedCt1SentEkReceivedSendCt2PlacedSpecOfPrePostEnv M A lim F K ScPre ScPost)))
    (st_cost : M.σ) (outA stA : BitVec 64)
    (st : Ct1SentEkReceived (spqrAuthApi F))
    (outUc : Ct2Sent (spqrAuthApi F)) (ct2 : Bytes) (mac : Mac)
    (hsc : st.send_ct2 K = .ok (outUc, ct2, mac))
    (hfits : FitsEnv M lim st_cost (ScPre ⟨outA, stA, st, outUc, ct2, mac⟩))
    {s0 s s_pool : State} {sp_call : BitVec 64} {P Frame : SepProp}
    {post : State → SepProp → Prop} {oom : State → SepProp}
    (hcl : LibsignalCodeLoaded lsmpl s.mem) (hpc : s.pc = entry) (hrun : s.status = .Running)
    (hsp : s.sp = sp_call) (hsp_align : (sp_call &&& 15#64 == 0#64) = true)
    (hlr : s.readReg64 Reg.lr = ret_pc) (htrace : TraceCalleeSaved s s0)
    (hx0 : s.readReg64 Reg.x0 = outA) (hx1 : s.readReg64 Reg.x1 = stA)
    (hsplit : P = (memRegion outA 104 ∗ unchunkedCt1SentEkReceivedAt A.repAlloc stA st ∗
      unchunkedSendCt2PlacedRoAt ∗ A.pool lim st_cost s_pool ∗ stackAt sp_call unchunkedSendCt2Stack) ∗ Frame)
    (hpool : A.pool lim st_cost s_pool = A.pool lim st_cost s := by simp only [arm64_norm])
    (hnext : ∀ (sf : State) (evs : List AllocEvent),
      sf.pc = ret_pc → sf.status = .Running → sf.sp = sp_call →
      CalleeSavedPreserved s sf → TraceCalleeSaved sf s0 →
      LibsignalCodeLoaded lsmpl sf.mem → ScPost ⟨outA, stA, st, outUc, ct2, mac⟩ evs →
      SepWP prog target_pc sf
        ((unchunkedCt2SentAt A.repAlloc outA outUc ∗ vecU8 A.repAlloc (outA + 56#64) ct2 ∗
          vecU8 A.repAlloc (outA + 80#64) mac ∗ memRegion stA 128 ∗
          unchunkedSendCt2PlacedRoAt ∗
          A.pool lim (M.stepEvents evs st_cost) sf ∗ stackAt sp_call unchunkedSendCt2Stack) ∗ Frame)
        post oom)
    (hi : i < 619 := by decide) (hunmut : (i ∈ libsignalMutatedBlocks) = false := by decide) :
    SepWP prog target_pc s P post oom := by
  have hcall_cl := subroutine_ok_post_lscl hcall hi hunmut
  refine SepWP.call_subroutine_frame hcall_cl
    (x := (⟨outA, stA, st, outUc, ct2, mac⟩, st_cost)) (F := Frame)
    hpc hrun (by rw [State.spAligned, hsp]; exact hsp_align) hlr ?_
    (fun _ _ _ h => by dsimp only [withLsCodeLoaded, unchunkedCt1SentEkReceivedSendCt2PlacedSpecOfPrePostEnv] at h; exact ((satisfies_pure_sepConj _ _ _).mp h).1)
    (fun _ _ _ _ h => by dsimp only [withLsCodeLoaded, unchunkedCt1SentEkReceivedSendCt2PlacedSpecOfPrePostEnv] at h; exact ((satisfies_pure_sepConj _ _ _).mp h).1)
    (fun sf hpc_sf hrun_sf hsp_sf hcs_sf => ?_)
    (fun _ _ _ h => by dsimp only [withLsCodeLoaded, unchunkedCt1SentEkReceivedSendCt2PlacedSpecOfPrePostEnv] at h; exact False.elim ((satisfies_pure_sepConj _ _ _).mp h).1)
  · intro R' hm
    rw [hsplit, hpool] at hm
    dsimp only [withLsCodeLoaded, unchunkedCt1SentEkReceivedSendCt2PlacedSpecOfPrePostEnv]; rw [hsp]
    have hm' : s.mem ⊨ ⌜LibsignalCodeLoaded lsmpl s.mem⌝ ∗
        ⌜s.readReg64 .x0 = outA ∧ s.readReg64 .x1 = stA ∧
          st.send_ct2 K = .ok (outUc, ct2, mac) ∧
          FitsEnv M lim st_cost (ScPre ⟨outA, stA, st, outUc, ct2, mac⟩)⌝ ∗
        ((memRegion outA 104 ∗ unchunkedCt1SentEkReceivedAt A.repAlloc stA st ∗
          unchunkedSendCt2PlacedRoAt ∗
          A.pool lim st_cost s ∗ stackAt sp_call unchunkedSendCt2Stack) ∗ Frame ∗ R') := by
      rw [satisfies_pure_sepConj]
      exact ⟨hcl, by
        rw [satisfies_pure_sepConj]
        exact ⟨⟨hx0, hx1, hsc, hfits⟩, by simpa only [sepConj_assoc] using hm⟩⟩
    exact Satisfies.mono (Entails.of_eq (by sep_ac_rfl)) hm'
  · dsimp only [withLsCodeLoaded, unchunkedCt1SentEkReceivedSendCt2PlacedSpecOfPrePostEnv]; rw [hsp, sepConj_assoc]
    refine SepWP.pure_elim fun hcl_sf => ?_
    rw [sepExists_sepConj_left]; refine SepWP.exists_elim fun evs => ?_
    rw [sepConj_assoc]; refine SepWP.pure_elim fun ⟨htr, hevs⟩ => ?_
    exact hnext sf evs hpc_sf hrun_sf (hsp_sf.trans hsp) hcs_sf
      ⟨htr.trans htrace.1, hcs_sf.2.2.2.2.2.2.2.2.2.2.2.trans htrace.2⟩ hcl_sf hevs

theorem call_sendCt2_statesRecv_placed [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {F : ShaCompress} {K : MlKem}
    {prog : Program} {i : Nat} {H : LibsignalHooks} [IsLsBlockProg prog i H]
    {entry ret_pc target_pc : BitVec 64}
    (hcall : subroutine_ok prog entry
      (withLsCodeLoaded lsmpl (unchunkedCt1SentEkReceivedSendCt2PlacedSpec M A lim F K)))
    (st_cost : M.σ) (outA stA : BitVec 64)
    (st : Ct1SentEkReceived (spqrAuthApi F))
    (outUc : Ct2Sent (spqrAuthApi F)) (ct2 : Bytes) (mac : Mac)
    (hsc : st.send_ct2 K = .ok (outUc, ct2, mac))
    (hfits : FitsEnv M lim st_cost (UnchunkedSendCt2PreEnv ⟨outA, stA, st, outUc, ct2, mac⟩))
    {s0 s s_pool : State} {sp_call : BitVec 64} {P Frame : SepProp}
    {post : State → SepProp → Prop} {oom : State → SepProp}
    (hcl : LibsignalCodeLoaded lsmpl s.mem) (hpc : s.pc = entry) (hrun : s.status = .Running)
    (hsp : s.sp = sp_call) (hsp_align : (sp_call &&& 15#64 == 0#64) = true)
    (hlr : s.readReg64 Reg.lr = ret_pc) (htrace : TraceCalleeSaved s s0)
    (hx0 : s.readReg64 Reg.x0 = outA) (hx1 : s.readReg64 Reg.x1 = stA)
    (hsplit : P = (memRegion outA 104 ∗ unchunkedCt1SentEkReceivedAt A.repAlloc stA st ∗
      unchunkedSendCt2PlacedRoAt ∗ A.pool lim st_cost s_pool ∗ stackAt sp_call unchunkedSendCt2Stack) ∗ Frame)
    (hpool : A.pool lim st_cost s_pool = A.pool lim st_cost s := by simp only [arm64_norm])
    (hnext : ∀ (sf : State) (evs : List AllocEvent),
      sf.pc = ret_pc → sf.status = .Running → sf.sp = sp_call →
      CalleeSavedPreserved s sf → TraceCalleeSaved sf s0 →
      LibsignalCodeLoaded lsmpl sf.mem →
      UnchunkedSendCt2PostEnv ⟨outA, stA, st, outUc, ct2, mac⟩ evs →
      SepWP prog target_pc sf
        ((unchunkedCt2SentAt A.repAlloc outA outUc ∗ vecU8 A.repAlloc (outA + 56#64) ct2 ∗
          vecU8 A.repAlloc (outA + 80#64) mac ∗ memRegion stA 128 ∗
          unchunkedSendCt2PlacedRoAt ∗
          A.pool lim (M.stepEvents evs st_cost) sf ∗ stackAt sp_call unchunkedSendCt2Stack) ∗ Frame)
        post oom)
    (hi : i < 619 := by decide) (hunmut : (i ∈ libsignalMutatedBlocks) = false := by decide) :
    SepWP prog target_pc s P post oom :=
  call_sendCt2_statesRecv_placed_ofPrePostEnv hcall st_cost outA stA st outUc ct2 mac
    hsc hfits hcl hpc hrun hsp hsp_align hlr htrace hx0 hx1 hsplit hpool hnext hi hunmut

theorem call_sendCt2Encoder_statesRecv_placed_ofPrePostEnv [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {EncPre EncPost : SendCt2EncoderGhost → List AllocEvent → Prop}
    {prog : Program} {i : Nat} {H : LibsignalHooks} [IsLsBlockProg prog i H]
    {entry ret_pc target_pc : BitVec 64}
    (hcall : subroutine_ok prog entry
      (withLsCodeLoaded lsmpl (sendCt2EncoderSpecOfPrePostEnv M A lim EncPre EncPost)))
    (st_cost : M.σ) (outA ct2Ptr macPtr : BitVec 64) (ct2 mac : Bytes) (enc : PolyEncoder)
    (hct2_ptr : ct2Ptr ≠ 0#64) (hmac_ptr : macPtr ≠ 0#64)
    (henc : CryptoVerification.LibsignalSpqrV1.Chunked.SendCt.send_ct2_encoder spqrPolyApi ct2 mac = .ok enc)
    (hfits : FitsEnv M lim st_cost (EncPre ⟨outA, ct2Ptr, ct2, macPtr, mac, enc⟩))
    {s0 s s_pool : State} {sp_call : BitVec 64} {P Frame : SepProp}
    {post : State → SepProp → Prop} {oom : State → SepProp}
    (hcl : LibsignalCodeLoaded lsmpl s.mem) (hpc : s.pc = entry) (hrun : s.status = .Running)
    (hsp : s.sp = sp_call) (hsp_align : (sp_call &&& 15#64 == 0#64) = true)
    (hlr : s.readReg64 Reg.lr = ret_pc) (htrace : TraceCalleeSaved s s0)
    (hx0 : s.readReg64 Reg.x0 = outA) (hx1 : s.readReg64 Reg.x1 = ct2Ptr)
    (hx2 : s.readReg64 Reg.x2 = BitVec.ofNat 64 ct2.length)
    (hx3 : s.readReg64 Reg.x3 = macPtr) (hx4 : s.readReg64 Reg.x4 = BitVec.ofNat 64 mac.length)
    (hsplit : P = (memRegion outA 400 ∗ (ct2Ptr ↦ₛ ct2) ∗ (macPtr ↦ₛ mac) ∗
      A.pool lim st_cost s_pool ∗ stackAt sp_call sendCt2EncoderStack) ∗ Frame)
    (hpool : A.pool lim st_cost s_pool = A.pool lim st_cost s := by simp only [arm64_norm])
    (hnext : ∀ (sf : State) (evs : List AllocEvent),
      sf.pc = ret_pc → sf.status = .Running → sf.sp = sp_call →
      CalleeSavedPreserved s sf → TraceCalleeSaved sf s0 →
      LibsignalCodeLoaded lsmpl sf.mem → EncPost ⟨outA, ct2Ptr, ct2, macPtr, mac, enc⟩ evs →
      SepWP prog target_pc sf
        ((polyEncoderAt A.repAlloc outA enc ∗ (ct2Ptr ↦ₛ ct2) ∗ (macPtr ↦ₛ mac) ∗
          A.pool lim (M.stepEvents evs st_cost) sf ∗ stackAt sp_call sendCt2EncoderStack) ∗ Frame)
        post oom)
    (hi : i < 619 := by decide) (hunmut : (i ∈ libsignalMutatedBlocks) = false := by decide)
    (hlr_ls : LsRetAddr624 ret_pc := by
      first | assumption | simp (config := { decide := true }) only [arm64_norm, wp_norm]) :
    SepWP prog target_pc s P post oom := by
  have hcall_cl := subroutine_ok_post_lscl hcall hi hunmut
  refine SepWP.call_subroutine_frame hcall_cl
    (x := (⟨outA, ct2Ptr, ct2, macPtr, mac, enc⟩, st_cost)) (F := Frame)
    hpc hrun (by rw [State.spAligned, hsp]; exact hsp_align) hlr ?_
    (fun _ _ _ h => by dsimp only [withLsCodeLoaded, sendCt2EncoderSpecOfPrePostEnv] at h; exact ((satisfies_pure_sepConj _ _ _).mp h).1)
    (fun _ _ _ _ h => by dsimp only [withLsCodeLoaded, sendCt2EncoderSpecOfPrePostEnv] at h; exact ((satisfies_pure_sepConj _ _ _).mp h).1)
    (fun sf hpc_sf hrun_sf hsp_sf hcs_sf => ?_)
    (fun _ _ _ h => by dsimp only [withLsCodeLoaded, sendCt2EncoderSpecOfPrePostEnv] at h; exact False.elim ((satisfies_pure_sepConj _ _ _).mp h).1)
  · intro R' hm
    rw [hsplit, hpool] at hm
    dsimp only [withLsCodeLoaded, sendCt2EncoderSpecOfPrePostEnv]; rw [hsp]
    have hm' : s.mem ⊨ ⌜LibsignalCodeLoaded lsmpl s.mem⌝ ∗
        ⌜s.readReg64 .x0 = outA ∧ s.readReg64 .x1 = ct2Ptr ∧
          s.readReg64 .x2 = BitVec.ofNat 64 ct2.length ∧ s.readReg64 .x3 = macPtr ∧
          s.readReg64 .x4 = BitVec.ofNat 64 mac.length ∧ ct2Ptr ≠ 0#64 ∧ macPtr ≠ 0#64 ∧
          CryptoVerification.LibsignalSpqrV1.Chunked.SendCt.send_ct2_encoder spqrPolyApi ct2 mac =
            .ok enc ∧
          FitsEnv M lim st_cost (EncPre ⟨outA, ct2Ptr, ct2, macPtr, mac, enc⟩) ∧
          LsRetAddr624 (s.readReg64 .lr)⌝ ∗
        ((memRegion outA 400 ∗ (ct2Ptr ↦ₛ ct2) ∗ (macPtr ↦ₛ mac) ∗
          A.pool lim st_cost s ∗ stackAt sp_call sendCt2EncoderStack) ∗ Frame ∗ R') := by
      rw [satisfies_pure_sepConj]
      exact ⟨hcl, by
        rw [satisfies_pure_sepConj]
        exact ⟨⟨hx0, hx1, hx2, hx3, hx4, hct2_ptr, hmac_ptr, henc, hfits,
          by rw [Reg.lr] at hlr; rw [hlr]; exact hlr_ls⟩,
          by simpa only [sepConj_assoc] using hm⟩⟩
    exact Satisfies.mono (Entails.of_eq (by sep_ac_rfl)) hm'
  · dsimp only [withLsCodeLoaded, sendCt2EncoderSpecOfPrePostEnv]; rw [hsp, sepConj_assoc]
    refine SepWP.pure_elim fun hcl_sf => ?_
    rw [sepExists_sepConj_left]; refine SepWP.exists_elim fun evs => ?_
    rw [sepConj_assoc]; refine SepWP.pure_elim fun ⟨htr, hevs⟩ => ?_
    exact hnext sf evs hpc_sf hrun_sf (hsp_sf.trans hsp) hcs_sf
      ⟨htr.trans htrace.1, hcs_sf.2.2.2.2.2.2.2.2.2.2.2.trans htrace.2⟩ hcl_sf hevs

theorem call_sendCt2Encoder_statesRecv_placed [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {prog : Program} {i : Nat} {H : LibsignalHooks} [IsLsBlockProg prog i H]
    {entry ret_pc target_pc : BitVec 64}
    (hcall : subroutine_ok prog entry (withLsCodeLoaded lsmpl (sendCt2EncoderSpec M A lim)))
    (st_cost : M.σ) (outA ct2Ptr macPtr : BitVec 64) (ct2 mac : Bytes) (enc : PolyEncoder)
    (hct2_ptr : ct2Ptr ≠ 0#64) (hmac_ptr : macPtr ≠ 0#64)
    (henc : CryptoVerification.LibsignalSpqrV1.Chunked.SendCt.send_ct2_encoder spqrPolyApi ct2 mac = .ok enc)
    (hfits : FitsEnv M lim st_cost (SendCt2EncoderPreEnv ⟨outA, ct2Ptr, ct2, macPtr, mac, enc⟩))
    {s0 s s_pool : State} {sp_call : BitVec 64} {P Frame : SepProp}
    {post : State → SepProp → Prop} {oom : State → SepProp}
    (hcl : LibsignalCodeLoaded lsmpl s.mem) (hpc : s.pc = entry) (hrun : s.status = .Running)
    (hsp : s.sp = sp_call) (hsp_align : (sp_call &&& 15#64 == 0#64) = true)
    (hlr : s.readReg64 Reg.lr = ret_pc) (htrace : TraceCalleeSaved s s0)
    (hx0 : s.readReg64 Reg.x0 = outA) (hx1 : s.readReg64 Reg.x1 = ct2Ptr)
    (hx2 : s.readReg64 Reg.x2 = BitVec.ofNat 64 ct2.length)
    (hx3 : s.readReg64 Reg.x3 = macPtr) (hx4 : s.readReg64 Reg.x4 = BitVec.ofNat 64 mac.length)
    (hsplit : P = (memRegion outA 400 ∗ (ct2Ptr ↦ₛ ct2) ∗ (macPtr ↦ₛ mac) ∗
      A.pool lim st_cost s_pool ∗ stackAt sp_call sendCt2EncoderStack) ∗ Frame)
    (hpool : A.pool lim st_cost s_pool = A.pool lim st_cost s := by simp only [arm64_norm])
    (hnext : ∀ (sf : State) (evs : List AllocEvent),
      sf.pc = ret_pc → sf.status = .Running → sf.sp = sp_call →
      CalleeSavedPreserved s sf → TraceCalleeSaved sf s0 →
      LibsignalCodeLoaded lsmpl sf.mem →
      SendCt2EncoderPostEnv ⟨outA, ct2Ptr, ct2, macPtr, mac, enc⟩ evs →
      SepWP prog target_pc sf
        ((polyEncoderAt A.repAlloc outA enc ∗ (ct2Ptr ↦ₛ ct2) ∗ (macPtr ↦ₛ mac) ∗
          A.pool lim (M.stepEvents evs st_cost) sf ∗ stackAt sp_call sendCt2EncoderStack) ∗ Frame)
        post oom)
    (hi : i < 619 := by decide) (hunmut : (i ∈ libsignalMutatedBlocks) = false := by decide)
    (hlr_ls : LsRetAddr624 ret_pc := by
      first | assumption | simp (config := { decide := true }) only [arm64_norm, wp_norm]) :
    SepWP prog target_pc s P post oom :=
  call_sendCt2Encoder_statesRecv_placed_ofPrePostEnv hcall st_cost outA ct2Ptr macPtr ct2 mac enc
    hct2_ptr hmac_ptr henc hfits hcl hpc hrun hsp hsp_align hlr htrace hx0 hx1 hx2 hx3 hx4
    hsplit hpool hnext hi hunmut hlr_ls

/-! ## 2. `recv_ek_chunk` Common Prefix (`+11404 -> +11508`) & Decode Branch Steppers -/

set_option maxHeartbeats 1200000 in
theorem ct1Sampled_recv_ek_prefix_copy_placed [LibsignalPlacement]
    {A : RustAlloc} {ext : String → Option (State → State)}
    (hmemcpy : HookSat (Rust.withPanics ext) spqrMemcpySym (withVmPreserved sessionMemcpySpec))
    (s_in : State) (fsp stA ve8 : BitVec 64)
    (c_uc : Words16) (dec : PolyDecoder) (Rest : SepProp)
    (hfsp_align : (fsp &&& 15#64 == 0#64) = true)
    (hpc : s_in.pc = (blkPl_332).base + 11404#64) (hrun : s_in.status = .Running)
    (hsp : s_in.sp = fsp) (hx1 : s_in.readReg64 .x1 = stA) :
    SepWP (lsProg_332 (Rust.withPanics ext)) ((blkPl_332).base + 11472#64) s_in
      (wordsAt (stA + 400#64) c_uc.toList ∗ polyDecoderAt A (stA + 528#64) dec ∗
        ((fsp + 232#64) ↦₆₄ ve8) ∗ memRegion (fsp + 2752#64) 400 ∗
        memRegion (fsp + 3696#64) 128 ∗ stackAt fsp statesRecvCalleeStackX ∗ Rest)
      (fun sf Pf =>
        VmPreserved s_in sf ∧
        (Pf ⊢
          wordsAt (stA + 400#64) c_uc.toList ∗ wordsAt (fsp + 3696#64) c_uc.toList ∗
          polyDecoderAt A (fsp + 2752#64) dec ∗ ((fsp + 232#64) ↦₆₄ stA) ∗
          memRegion (stA + 528#64) 400 ∗ stackAt fsp statesRecvCalleeStackX ∗ Rest) ∧
        sf.sp = fsp ∧
        sf.readReg64 .x19 = s_in.readReg64 .x19 ∧ sf.readReg64 .x20 = s_in.readReg64 .x20 ∧
        sf.readReg64 .x21 = s_in.readReg64 .x21 ∧ sf.readReg64 .x22 = s_in.readReg64 .x22 ∧
        sf.readReg64 .x23 = s_in.readReg64 .x23 ∧ sf.readReg64 .x24 = s_in.readReg64 .x24 ∧
        sf.readReg64 .x28 = s_in.readReg64 .x28 ∧ sf.readReg64 .x29 = s_in.readReg64 .x29 ∧
        TraceCalleeSaved sf s_in) := by
  have hrel_dec : Relocatable 400 (fun a => polyDecoderAt A a dec) :=
    Relocatable.of_polyDecoderAt A dec
  have hpre :
      wordsAt (stA + 400#64) c_uc.toList ∗ polyDecoderAt A (stA + 528#64) dec ∗
        ((fsp + 232#64) ↦₆₄ ve8) ∗ memRegion (fsp + 2752#64) 400 ∗
        memRegion (fsp + 3696#64) 128 ∗ stackAt fsp statesRecvCalleeStackX ∗ Rest ⊢
      ∃∗ c_dst : Words16, ∃∗ bs_dec : List (BitVec 8),
        ⌜bs_dec.length = 400⌝ ∗ wordsAt (stA + 400#64) c_uc.toList ∗
        wordsAt (fsp + 3696#64) c_dst.toList ∗ ((fsp + 232#64) ↦₆₄ ve8) ∗
        ((stA + 528#64) ↦ₛ bs_dec) ∗ memRegion (fsp + 2752#64) 400 ∗
        stackAt fsp statesRecvCalleeStackX ∗
        (relocatedHeap (fun a => polyDecoderAt A a dec) bs_dec ∗ Rest) := by
    refine Entails.trans (sepConj_mono_right
      (sepConj_mono (hrel_dec (stA + 528#64))
        (sepConj_mono_right (sepConj_mono_right
          (sepConj_mono_left (memRegion_128_entails_words16 (fsp + 3696#64))))))) ?_
    simp only [sepExists_sepConj_left]
    simp only [sepExists_sepConj_right]
    apply Entails.sepExists_elim; intro bs_dec
    apply Entails.sepExists_elim; intro c_dst
    refine Entails.sepExists_right c_dst (Entails.sepExists_right bs_dec ?_)
    exact Entails.of_eq (by sep_ac_rfl)
  refine SepWP.weaken_pre hpre ?_
  apply ProofLib.SepWP.exists_left; intro c_dst
  apply ProofLib.SepWP.exists_left; intro bs_dec
  wp_focus_pure; intro hlen_dec
  subst hsp hx1
  have hmemcpy_raw : subroutine_ok (lsProg_332 (Rust.withPanics ext))
      (lsρ spqrMemcpySym) (withVmPreserved sessionMemcpySpec) :=
    spqr_hook_ok_of_mem (sym := spqrMemcpySym) hmemcpy
  have hsplit := stackAt_statesRecvCallee_eq_allocHook' s_in.sp
  refine SepWP.mono (post := fun sf Pf =>
      VmPreserved s_in sf ∧
      (Pf ⊢
        wordsAt (s_in.readReg64 .x1 + 400#64) c_uc.toList ∗
        wordsAt (s_in.sp + 3696#64) c_uc.toList ∗
        ((s_in.sp + 2752#64) ↦ₛ bs_dec) ∗ ((s_in.sp + 232#64) ↦₆₄ s_in.readReg64 .x1) ∗
        ((s_in.readReg64 .x1 + 528#64) ↦ₛ bs_dec) ∗ stackAt s_in.sp statesRecvCalleeStackX ∗
        (relocatedHeap (fun a => polyDecoderAt A a dec) bs_dec ∗ Rest)) ∧
      sf.sp = s_in.sp ∧
      sf.readReg64 .x19 = s_in.readReg64 .x19 ∧ sf.readReg64 .x20 = s_in.readReg64 .x20 ∧
      sf.readReg64 .x21 = s_in.readReg64 .x21 ∧ sf.readReg64 .x22 = s_in.readReg64 .x22 ∧
      sf.readReg64 .x23 = s_in.readReg64 .x23 ∧ sf.readReg64 .x24 = s_in.readReg64 .x24 ∧
      sf.readReg64 .x28 = s_in.readReg64 .x28 ∧ sf.readReg64 .x29 = s_in.readReg64 .x29 ∧
      TraceCalleeSaved sf s_in) ?_
    (fun sf Pf _ _ ⟨hvm, hPf, hrest⟩ => ⟨hvm, Entails.trans hPf ?_, hrest⟩)
  · rw [hsplit, show memRegion (s_in.sp + 2752#64) 400 = memRegion (s_in.sp + 2752#64) bs_dec.length by rw [hlen_dec]]
    dsimp only [lsProg_332, lsρ, spqrMemcpySym, BitVec.ofNat_eq_ofNat] at hpc hmemcpy_raw ⊢
    dsimp only [Words16.toList, withVmPreserved, sessionMemcpySpec, allocHookStack] at hmemcpy_raw ⊢
    simp only [wordsAt_16, BitVec.add_assoc, BitVec.reduceAdd, lsmpl_base_332_eq]
    refine seq_vm_cont (mid := lsmpl.ρ "memcpy") ?_
    by_vm_steps_nest (
      wp_steps
      refine SepWP.done rfl hrun ⟨by simp only [wp_norm, arm64_norm], fun hvm1 => ?_⟩
      wp_call hmemcpy_raw (s_in.sp + 2752#64, s_in.readReg64 .x1 + 528#64, bs_dec)
      have hvm_all : VmPreserved s_in sf := hvm1.trans (by assumption)
      refine SepWP.mono (post := fun sf2 Pf2 =>
        VmPreserved sf sf2 ∧ (Pf2 ⊢ _) ∧ sf2.sp = s_in.sp ∧
        sf2.readReg64 .x19 = s_in.readReg64 .x19 ∧ sf2.readReg64 .x20 = s_in.readReg64 .x20 ∧
        sf2.readReg64 .x21 = s_in.readReg64 .x21 ∧ sf2.readReg64 .x22 = s_in.readReg64 .x22 ∧
        sf2.readReg64 .x23 = s_in.readReg64 .x23 ∧ sf2.readReg64 .x24 = s_in.readReg64 .x24 ∧
        sf2.readReg64 .x28 = s_in.readReg64 .x28 ∧ sf2.readReg64 .x29 = s_in.readReg64 .x29 ∧
        TraceCalleeSaved sf2 s_in) ?_
        (fun _ _ _ _ ⟨hvm2, hrest⟩ => ⟨hvm_all.trans hvm2, hrest⟩)
      by_vm_steps_nest (
        dsimp only [TraceCalleeSaved, Reg.x19, Reg.x20, Reg.x21, Reg.x22, Reg.x23, Reg.x24,
          Reg.x28, Reg.x29]
        wp_done
      )
    )
  · have hdec := relocatedHeap_recompose (fun a => polyDecoderAt A a dec) bs_dec (s_in.sp + 2752#64)
    have hdec_in : ((s_in.readReg64 .x1 + 528#64) ↦ₛ bs_dec) ⊢
        memRegion (s_in.readReg64 .x1 + 528#64) 400 := by
      rw [← hlen_dec]; exact ProofLib.pointsToBytes_entails_memRegion _ _
    refine Entails.trans (Entails.of_eq (show _ =
      wordsAt (s_in.readReg64 .x1 + 400#64) c_uc.toList ∗
      wordsAt (s_in.sp + 3696#64) c_uc.toList ∗
      (((s_in.sp + 2752#64) ↦ₛ bs_dec) ∗
        relocatedHeap (fun a => polyDecoderAt A a dec) bs_dec) ∗
      ((s_in.sp + 232#64) ↦₆₄ s_in.readReg64 .x1) ∗
      ((s_in.readReg64 .x1 + 528#64) ↦ₛ bs_dec) ∗
      stackAt s_in.sp statesRecvCalleeStackX ∗ Rest by sep_ac_rfl)) ?_
    exact sepConj_mono_right (sepConj_mono_right
      (sepConj_mono hdec (sepConj_mono_right (sepConj_mono_left hdec_in))))

theorem ct1Sampled_recv_ek_prefix_copy_pool_placed [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {ext : String → Option (State → State)}
    (hmemcpy : HookSat (Rust.withPanics ext) spqrMemcpySym (withVmPreserved sessionMemcpySpec))
    (st_cost : M.σ) (s_in : State) (fsp stA ve8 : BitVec 64)
    (c_uc : Words16) (dec : PolyDecoder) (Rest : SepProp)
    (hfsp_align : (fsp &&& 15#64 == 0#64) = true)
    (hpc : s_in.pc = (blkPl_332).base + 11404#64) (hrun : s_in.status = .Running)
    (hsp : s_in.sp = fsp) (hx1 : s_in.readReg64 .x1 = stA) :
    SepWP (lsProg_332 (Rust.withPanics ext)) ((blkPl_332).base + 11472#64) s_in
      (wordsAt (stA + 400#64) c_uc.toList ∗ polyDecoderAt A.repAlloc (stA + 528#64) dec ∗
        ((fsp + 232#64) ↦₆₄ ve8) ∗ memRegion (fsp + 2752#64) 400 ∗
        memRegion (fsp + 3696#64) 128 ∗ A.pool lim st_cost s_in ∗
        stackAt fsp statesRecvCalleeStackX ∗ Rest)
      (fun sf Pf =>
        VmPreserved s_in sf ∧
        (Pf ⊢
          wordsAt (stA + 400#64) c_uc.toList ∗ wordsAt (fsp + 3696#64) c_uc.toList ∗
          polyDecoderAt A.repAlloc (fsp + 2752#64) dec ∗ ((fsp + 232#64) ↦₆₄ stA) ∗
          memRegion (stA + 528#64) 400 ∗ A.pool lim st_cost sf ∗
          stackAt fsp statesRecvCalleeStackX ∗ Rest) ∧
        sf.sp = fsp ∧
        sf.readReg64 .x19 = s_in.readReg64 .x19 ∧ sf.readReg64 .x20 = s_in.readReg64 .x20 ∧
        sf.readReg64 .x21 = s_in.readReg64 .x21 ∧ sf.readReg64 .x22 = s_in.readReg64 .x22 ∧
        sf.readReg64 .x23 = s_in.readReg64 .x23 ∧ sf.readReg64 .x24 = s_in.readReg64 .x24 ∧
        sf.readReg64 .x28 = s_in.readReg64 .x28 ∧ sf.readReg64 .x29 = s_in.readReg64 .x29 ∧
        TraceCalleeSaved sf s_in) := by
  have hw : SepWP (lsProg_332 (Rust.withPanics ext)) ((blkPl_332).base + 11472#64) s_in _
      (fun sf Pf =>
        VmPreserved s_in sf ∧
        (Pf ⊢
          wordsAt (stA + 400#64) c_uc.toList ∗ wordsAt (fsp + 3696#64) c_uc.toList ∗
          polyDecoderAt A.repAlloc (fsp + 2752#64) dec ∗ ((fsp + 232#64) ↦₆₄ stA) ∗
          memRegion (stA + 528#64) 400 ∗ A.pool lim st_cost sf ∗
          stackAt fsp statesRecvCalleeStackX ∗ Rest) ∧
        sf.sp = fsp ∧
        sf.readReg64 .x19 = s_in.readReg64 .x19 ∧ sf.readReg64 .x20 = s_in.readReg64 .x20 ∧
        sf.readReg64 .x21 = s_in.readReg64 .x21 ∧ sf.readReg64 .x22 = s_in.readReg64 .x22 ∧
        sf.readReg64 .x23 = s_in.readReg64 .x23 ∧ sf.readReg64 .x24 = s_in.readReg64 .x24 ∧
        sf.readReg64 .x28 = s_in.readReg64 .x28 ∧ sf.readReg64 .x29 = s_in.readReg64 .x29 ∧
        TraceCalleeSaved sf s_in) :=
    SepWP.mono
      (ct1Sampled_recv_ek_prefix_copy_placed (A := A.repAlloc) hmemcpy s_in fsp stA ve8 c_uc dec
        (A.pool lim st_cost s_in ∗ Rest) hfsp_align hpc hrun hsp hx1)
      fun sf Pf _ _ ⟨hvm, hPf, hq⟩ =>
        ⟨hvm, Entails.trans hPf (Entails.of_eq (by rw [A.pool_transport lim st_cost s_in sf hvm]; sep_ac_rfl)), hq⟩
  exact SepWP.weaken_pre (Entails.of_eq (by sep_ac_rfl)) hw

theorem ct1Sampled_recv_ek_decode_branch_none_placed [LibsignalPlacement]
    {A : RustAlloc} {ext : String → Option (State → State)}
    (s_in : State) (fsp : BitVec 64) (Rest : SepProp)
    (hfsp_align : (fsp &&& 15#64 == 0#64) = true)
    (hpc : s_in.pc = (blkPl_332).base + 11496#64) (hrun : s_in.status = .Running)
    (hsp : s_in.sp = fsp) :
    SepWP (lsProg_332 (Rust.withPanics ext)) ((blkPl_332).base + 13968#64) s_in
      (optVecU8At A (fsp + 3832#64) none ∗ Rest)
      (fun sf Pf =>
        VmPreserved s_in sf ∧ (Pf ⊢ memRegion (fsp + 3832#64) 24 ∗ Rest) ∧ sf.sp = fsp ∧
        sf.readReg64 .x19 = s_in.readReg64 .x19 ∧ sf.readReg64 .x20 = s_in.readReg64 .x20 ∧
        sf.readReg64 .x21 = s_in.readReg64 .x21 ∧ sf.readReg64 .x22 = s_in.readReg64 .x22 ∧
        sf.readReg64 .x23 = s_in.readReg64 .x23 ∧ sf.readReg64 .x24 = s_in.readReg64 .x24 ∧
        sf.readReg64 .x28 = s_in.readReg64 .x28 ∧ sf.readReg64 .x29 = s_in.readReg64 .x29 ∧
        TraceCalleeSaved sf s_in) := by
  subst hsp
  have hfold := optVecU8At_none_entails_memRegion_24 A (s_in.sp + 3832#64)
  dsimp only [lsProg_332, optVecU8At, noneCap, BitVec.ofNat_eq_ofNat] at hpc hfold ⊢
  by_vm_steps_nest (
    wp_steps
    refine SepWP.focus_weaken hfold (by sep_focus) ?_
    dsimp only [TraceCalleeSaved, Reg.x19, Reg.x20, Reg.x21, Reg.x22, Reg.x23, Reg.x24,
      Reg.x28, Reg.x29]
    wp_done
  )

theorem ct1Sampled_recv_ek_decode_branch_none_pool_placed [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {ext : String → Option (State → State)}
    (st_cost : M.σ) (s_in : State) (fsp : BitVec 64) (Rest : SepProp)
    (hfsp_align : (fsp &&& 15#64 == 0#64) = true)
    (hpc : s_in.pc = (blkPl_332).base + 11496#64) (hrun : s_in.status = .Running)
    (hsp : s_in.sp = fsp) :
    SepWP (lsProg_332 (Rust.withPanics ext)) ((blkPl_332).base + 13968#64) s_in
      (optVecU8At A.repAlloc (fsp + 3832#64) none ∗ A.pool lim st_cost s_in ∗ Rest)
      (fun sf Pf =>
        VmPreserved s_in sf ∧
        (Pf ⊢ memRegion (fsp + 3832#64) 24 ∗ A.pool lim st_cost sf ∗ Rest) ∧ sf.sp = fsp ∧
        sf.readReg64 .x19 = s_in.readReg64 .x19 ∧ sf.readReg64 .x20 = s_in.readReg64 .x20 ∧
        sf.readReg64 .x21 = s_in.readReg64 .x21 ∧ sf.readReg64 .x22 = s_in.readReg64 .x22 ∧
        sf.readReg64 .x23 = s_in.readReg64 .x23 ∧ sf.readReg64 .x24 = s_in.readReg64 .x24 ∧
        sf.readReg64 .x28 = s_in.readReg64 .x28 ∧ sf.readReg64 .x29 = s_in.readReg64 .x29 ∧
        TraceCalleeSaved sf s_in) := by
  refine SepWP.mono
    (ct1Sampled_recv_ek_decode_branch_none_placed (A := A.repAlloc) s_in fsp
      (A.pool lim st_cost s_in ∗ Rest) hfsp_align hpc hrun hsp)
    fun sf Pf _ _ ⟨hvm, hPf, hq⟩ =>
      ⟨hvm, Entails.trans hPf (Entails.of_eq (by rw [A.pool_transport lim st_cost s_in sf hvm])), hq⟩

theorem ct1Sampled_recv_ek_decode_branch_some_placed [LibsignalPlacement]
    {A : RustAlloc} {ext : String → Option (State → State)}
    (s_in : State) (fsp : BitVec 64) (decoded : Bytes) (Rest : SepProp)
    (hfsp_align : (fsp &&& 15#64 == 0#64) = true)
    (hpc : s_in.pc = (blkPl_332).base + 11496#64) (hrun : s_in.status = .Running)
    (hsp : s_in.sp = fsp) :
    SepWP (lsProg_332 (Rust.withPanics ext)) ((blkPl_332).base + 11508#64) s_in
      (optVecU8At A (fsp + 3832#64) (some decoded) ∗ Rest)
      (fun sf Pf =>
        VmPreserved s_in sf ∧ (Pf ⊢ vecU8 A (fsp + 3832#64) decoded ∗ Rest) ∧ sf.sp = fsp ∧
        sf.readReg64 .x19 = s_in.readReg64 .x19 ∧ sf.readReg64 .x20 = s_in.readReg64 .x20 ∧
        sf.readReg64 .x21 = s_in.readReg64 .x21 ∧ sf.readReg64 .x22 = s_in.readReg64 .x22 ∧
        sf.readReg64 .x23 = s_in.readReg64 .x23 ∧ sf.readReg64 .x24 = s_in.readReg64 .x24 ∧
        sf.readReg64 .x28 = s_in.readReg64 .x28 ∧ sf.readReg64 .x29 = s_in.readReg64 .x29 ∧
        TraceCalleeSaved sf s_in) := by
  subst hsp
  dsimp only [optVecU8At]
  refine SepWP.weaken_pre
    (sepConj_mono_left (vecU8_entails_slice_and_tail A (s_in.sp + 3832#64) decoded)) ?_
  wp_simp_pre [sepExists_sepConj_left]
  apply ProofLib.SepWP.exists_left; intro cap
  apply ProofLib.SepWP.exists_left; intro ptr
  wp_focus_pure; rintro ⟨hle, hcap_lt, hptr_ne⟩
  have hcmn := cap_add_one_beq_zero_false hcap_lt
  have hrecomb := vecU8_of_slice_and_tail A (s_in.sp + 3832#64) cap ptr decoded hle hcap_lt hptr_ne
  dsimp only [lsProg_332, BitVec.ofNat_eq_ofNat] at hpc ⊢
  by_vm_steps_nest (
    wp_steps
    refine SepWP.focus_weaken hrecomb (by sep_focus) ?_
    dsimp only [TraceCalleeSaved, Reg.x19, Reg.x20, Reg.x21, Reg.x22, Reg.x23, Reg.x24,
      Reg.x28, Reg.x29]
    wp_done
  )

theorem ct1Sampled_recv_ek_decode_branch_some_pool_placed [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {ext : String → Option (State → State)}
    (st_cost : M.σ) (s_in : State) (fsp : BitVec 64) (decoded : Bytes) (Rest : SepProp)
    (hfsp_align : (fsp &&& 15#64 == 0#64) = true)
    (hpc : s_in.pc = (blkPl_332).base + 11496#64) (hrun : s_in.status = .Running)
    (hsp : s_in.sp = fsp) :
    SepWP (lsProg_332 (Rust.withPanics ext)) ((blkPl_332).base + 11508#64) s_in
      (optVecU8At A.repAlloc (fsp + 3832#64) (some decoded) ∗ A.pool lim st_cost s_in ∗ Rest)
      (fun sf Pf =>
        VmPreserved s_in sf ∧
        (Pf ⊢ vecU8 A.repAlloc (fsp + 3832#64) decoded ∗ A.pool lim st_cost sf ∗ Rest) ∧
        sf.sp = fsp ∧
        sf.readReg64 .x19 = s_in.readReg64 .x19 ∧ sf.readReg64 .x20 = s_in.readReg64 .x20 ∧
        sf.readReg64 .x21 = s_in.readReg64 .x21 ∧ sf.readReg64 .x22 = s_in.readReg64 .x22 ∧
        sf.readReg64 .x23 = s_in.readReg64 .x23 ∧ sf.readReg64 .x24 = s_in.readReg64 .x24 ∧
        sf.readReg64 .x28 = s_in.readReg64 .x28 ∧ sf.readReg64 .x29 = s_in.readReg64 .x29 ∧
        TraceCalleeSaved sf s_in) := by
  refine SepWP.mono
    (ct1Sampled_recv_ek_decode_branch_some_placed (A := A.repAlloc) s_in fsp decoded
      (A.pool lim st_cost s_in ∗ Rest) hfsp_align hpc hrun hsp)
    fun sf Pf _ _ ⟨hvm, hPf, hq⟩ =>
      ⟨hvm, Entails.trans hPf (Entails.of_eq (by rw [A.pool_transport lim st_cost s_in sf hvm])), hq⟩

set_option maxHeartbeats 1200000 in
theorem ct1Sampled_recv_ek_add_and_decode_placed_ofPrePostEnv [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {DecPre DecPost : PolyDecoderDecodedMessageGhost → List AllocEvent → Prop}
    {ext : String → Option (State → State)}
    (hadd_call : subroutine_ok (lsProg_332 (Rust.withPanics ext))
      (lsmpl.base 419) (withLsCodeLoaded lsmpl (addChunkSpecX M A lim)))
    (hdec_call : subroutine_ok (lsProg_332 (Rust.withPanics ext))
      (lsmpl.base 418)
      (withLsCodeRoLoaded lsmpl
        (polyDecoderDecodedMessagePlacedSpecOfPrePostEnv M A lim DecPre DecPost)))
    (st_cost : M.σ) (s0 s_in : State) (fsp msgA : BitVec 64)
    (dec : PolyDecoder) (chunk : Chunk) (outMsg : Option Bytes)
    (hsorted : PolyDecoderStrictSorted dec)
    (hdec_msg : spqrPolyApi.decoded_message (addChunkTotal dec chunk) = .ok outMsg)
    (hfits_add : FitsEnv M lim st_cost (AddChunkEnv ⟨fsp + 2752#64, msgA + 10#64, dec, chunk⟩))
    (hfits_dec : ∀ evsAdd,
      AddChunkEnv ⟨fsp + 2752#64, msgA + 10#64, dec, chunk⟩ evsAdd →
      FitsEnv M lim (M.stepEvents evsAdd st_cost)
        (DecPre ⟨fsp + 3832#64, fsp + 2752#64, addChunkTotal dec chunk, outMsg⟩))
    (Rest : SepProp) (hcro : LibsignalCodeRoLoaded lsmpl s_in.mem)
    (hfsp_align : (fsp &&& 15#64 == 0#64) = true)
    (hpc : s_in.pc = (blkPl_332).base + 11472#64) (hrun : s_in.status = .Running)
    (hsp : s_in.sp = fsp) (hx24 : s_in.readReg64 .x24 = msgA) (htr : TraceCalleeSaved s_in s0) :
    SepWP (lsProg_332 (Rust.withPanics ext)) ((blkPl_332).base + 11496#64) s_in
      (memRegion (fsp + 3832#64) 24 ∗ polyDecoderAt A.repAlloc (fsp + 2752#64) dec ∗
        chunkAt (msgA + 10#64) chunk ∗ statesRecvRoPlacedAt ∗
        A.pool lim st_cost s_in ∗ stackAt fsp statesRecvCalleeStackX ∗ Rest)
      (fun sf Pf =>
        ∃ evsAdd evsDec : List AllocEvent,
          (Pf ⊢
            optVecU8At A.repAlloc (fsp + 3832#64) outMsg ∗
            polyDecoderAt A.repAlloc (fsp + 2752#64) (addChunkTotal dec chunk) ∗
            chunkAt (msgA + 10#64) chunk ∗ statesRecvRoPlacedAt ∗
            A.pool lim (M.stepEvents (evsAdd ++ evsDec) st_cost) sf ∗
            stackAt fsp statesRecvCalleeStackX ∗ Rest) ∧
          sf.sp = fsp ∧
          sf.readReg64 .x19 = s_in.readReg64 .x19 ∧ sf.readReg64 .x20 = s_in.readReg64 .x20 ∧
          sf.readReg64 .x21 = s_in.readReg64 .x21 ∧ sf.readReg64 .x22 = s_in.readReg64 .x22 ∧
          sf.readReg64 .x23 = s_in.readReg64 .x23 ∧ sf.readReg64 .x24 = msgA ∧
          sf.readReg64 .x28 = s_in.readReg64 .x28 ∧ sf.readReg64 .x29 = s_in.readReg64 .x29 ∧
          TraceCalleeSaved sf s0 ∧ LibsignalCodeRoLoaded lsmpl sf.mem ∧
          AddChunkEnv ⟨fsp + 2752#64, msgA + 10#64, dec, chunk⟩ evsAdd ∧
          DecPost ⟨fsp + 3832#64, fsp + 2752#64, addChunkTotal dec chunk, outMsg⟩ evsDec ∧
          PolyDecoderStrictSorted (addChunkTotal dec chunk)) := by
  subst hsp hx24
  have hadd_raw : subroutine_ok (lsProg_332 (Rust.withPanics ext))
      ((blkPl_419).base) (withLsCodeLoaded lsmpl (addChunkSpecX M A lim)) := hadd_call
  have hdec_raw : subroutine_ok (lsProg_332 (Rust.withPanics ext))
      ((blkPl_418).base)
      (withLsCodeRoLoaded lsmpl
        (polyDecoderDecodedMessagePlacedSpecOfPrePostEnv M A lim DecPre DecPost)) := hdec_call
  have hsplit_add := stackAt_statesRecvCallee_eq_addChunk s_in.sp
  have hsplit_dec := stackAt_statesRecvCallee_eq_polyDecodedMessage s_in.sp
  dsimp only [lsProg_332, statesRecvRoPlacedAt, polyDecodedMessageStackX, BitVec.ofNat_eq_ofNat]
    at hpc hadd_raw hdec_raw hsplit_add hsplit_dec ⊢
  rw [hsplit_add]
  wp_steps
  refine call_addChunkX_statesRecv_cro_placed hadd_raw st_cost
    (s_in.sp + 2752#64) (s_in.readReg64 .x24 + 10#64) dec chunk hsorted hfits_add
    (s0 := s0) (s_pool := s_in) (ret_pc := (blkPl_332).base + 11484#64) (sp_call := s_in.sp)
    (by simpa only [State.mem, arm64_norm] using hcro)
    (by simp only [State.pc, arm64_norm]; rfl) (by wp_norm_lhs)
    (by simp only [State.sp, arm64_norm]) hfsp_align
    (by simp only [Reg.lr, arm64_norm]) (by simp only [TraceCalleeSaved, arm64_norm, htr.1, htr.2])
    (by simp only [Reg.x0, arm64_norm]) (by simp only [Reg.x1, Reg.x24, arm64_norm])
    (by sep_focus) (by simp only [arm64_norm])
    (fun sf1 evsAdd hpc1 hrun1 hsp1 _ hcs1 htr1 hcro1 hevs_add hsorted' => ?_)
  rcases hcs1 with ⟨hx19_1, hx20_1, hx21_1, hx22_1, hx23_1, hx24_1, hx25_1, hx26_1, hx27_1, hx28_1, hfp_1, _⟩
  simp only [arm64_norm] at hx19_1 hx20_1 hx21_1 hx22_1 hx23_1 hx24_1 hx25_1 hx26_1 hx27_1 hx28_1 hfp_1
  refine SepWP.focus_weaken (Entails.of_eq hsplit_add.symm) (by sep_focus) ?_
  refine SepWP.focus_weaken (Entails.of_eq hsplit_dec) (by sep_focus) ?_
  wp_steps
  refine call_decodedMessage_statesRecv_placed_ofPrePostEnv hdec_raw
    (M.stepEvents evsAdd st_cost)
    (s_in.sp + 3832#64) (s_in.sp + 2752#64) (addChunkTotal dec chunk) outMsg
    hsorted' hdec_msg (hfits_dec evsAdd hevs_add)
    (s0 := s0) (s_pool := sf1) (ret_pc := (blkPl_332).base + 11496#64) (sp_call := s_in.sp)
    (by simpa only [State.mem, arm64_norm] using hcro1)
    (by simp only [State.pc, arm64_norm]; rfl) (by wp_norm_lhs)
    (by simp only [State.sp, arm64_norm, hsp1]) hfsp_align
    (by simp only [Reg.lr, arm64_norm]) (by simp only [TraceCalleeSaved, arm64_norm, htr1.1, htr1.2])
    (by simp only [Reg.x8, arm64_norm, hsp1]) (by simp only [Reg.x0, arm64_norm, hsp1])
    (by sep_focus) (by simp only [arm64_norm])
    (fun sf2 evsDec hpc2 hrun2 hsp2 hcs2 htr2 hcro2 hevs_dec => ?_)
  rcases hcs2 with ⟨hx19_2, hx20_2, hx21_2, hx22_2, hx23_2, hx24_2, hx25_2, hx26_2, hx27_2, hx28_2, hfp_2, _⟩
  simp only [arm64_norm, hx19_1, hx20_1, hx21_1, hx22_1, hx23_1, hx24_1, hx28_1, hfp_1]
    at hx19_2 hx20_2 hx21_2 hx22_2 hx23_2 hx24_2 hx28_2 hfp_2
  refine SepWP.focus_weaken (Entails.of_eq hsplit_dec.symm) (by sep_focus) ?_
  refine SepWP.done hpc2 hrun2
    ⟨evsAdd, evsDec, ?_, hsp2, hx19_2, hx20_2, hx21_2, hx22_2, hx23_2, hx24_2, hx28_2, hfp_2,
      htr2, hcro2, hevs_add, hevs_dec, hsorted'⟩
  rw [← M.stepEvents_append evsAdd evsDec st_cost]
  exact Entails.of_eq (by sep_ac_rfl)

theorem ct1Sampled_recv_ek_add_and_decode_placed [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {ext : String → Option (State → State)}
    (hadd_call : subroutine_ok (lsProg_332 (Rust.withPanics ext))
      (lsmpl.base 419) (withLsCodeLoaded lsmpl (addChunkSpecX M A lim)))
    (hdec_call : subroutine_ok (lsProg_332 (Rust.withPanics ext))
      (lsmpl.base 418) (withLsCodeRoLoaded lsmpl (polyDecoderDecodedMessagePlacedSpec M A lim)))
    (st_cost : M.σ) (s0 s_in : State) (fsp msgA : BitVec 64)
    (dec : PolyDecoder) (chunk : Chunk) (outMsg : Option Bytes)
    (hsorted : PolyDecoderStrictSorted dec)
    (hdec_msg : spqrPolyApi.decoded_message (addChunkTotal dec chunk) = .ok outMsg)
    (hfits_add : FitsEnv M lim st_cost (AddChunkEnv ⟨fsp + 2752#64, msgA + 10#64, dec, chunk⟩))
    (hfits_dec : ∀ evsAdd,
      AddChunkEnv ⟨fsp + 2752#64, msgA + 10#64, dec, chunk⟩ evsAdd →
      FitsEnv M lim (M.stepEvents evsAdd st_cost)
        (PolyDecoderDecodedMessagePreEnv ⟨fsp + 3832#64, fsp + 2752#64, addChunkTotal dec chunk, outMsg⟩))
    (Rest : SepProp) (hcro : LibsignalCodeRoLoaded lsmpl s_in.mem)
    (hfsp_align : (fsp &&& 15#64 == 0#64) = true)
    (hpc : s_in.pc = (blkPl_332).base + 11472#64) (hrun : s_in.status = .Running)
    (hsp : s_in.sp = fsp) (hx24 : s_in.readReg64 .x24 = msgA) (htr : TraceCalleeSaved s_in s0) :
    SepWP (lsProg_332 (Rust.withPanics ext)) ((blkPl_332).base + 11496#64) s_in
      (memRegion (fsp + 3832#64) 24 ∗ polyDecoderAt A.repAlloc (fsp + 2752#64) dec ∗
        chunkAt (msgA + 10#64) chunk ∗ statesRecvRoPlacedAt ∗
        A.pool lim st_cost s_in ∗ stackAt fsp statesRecvCalleeStackX ∗ Rest)
      (fun sf Pf =>
        ∃ evsAdd evsDec : List AllocEvent,
          (Pf ⊢
            optVecU8At A.repAlloc (fsp + 3832#64) outMsg ∗
            polyDecoderAt A.repAlloc (fsp + 2752#64) (addChunkTotal dec chunk) ∗
            chunkAt (msgA + 10#64) chunk ∗ statesRecvRoPlacedAt ∗
            A.pool lim (M.stepEvents (evsAdd ++ evsDec) st_cost) sf ∗
            stackAt fsp statesRecvCalleeStackX ∗ Rest) ∧
          sf.sp = fsp ∧
          sf.readReg64 .x19 = s_in.readReg64 .x19 ∧ sf.readReg64 .x20 = s_in.readReg64 .x20 ∧
          sf.readReg64 .x21 = s_in.readReg64 .x21 ∧ sf.readReg64 .x22 = s_in.readReg64 .x22 ∧
          sf.readReg64 .x23 = s_in.readReg64 .x23 ∧ sf.readReg64 .x24 = msgA ∧
          sf.readReg64 .x28 = s_in.readReg64 .x28 ∧ sf.readReg64 .x29 = s_in.readReg64 .x29 ∧
          TraceCalleeSaved sf s0 ∧ LibsignalCodeRoLoaded lsmpl sf.mem ∧
          AddChunkEnv ⟨fsp + 2752#64, msgA + 10#64, dec, chunk⟩ evsAdd ∧
          PolyDecoderDecodedMessagePostEnv ⟨fsp + 3832#64, fsp + 2752#64, addChunkTotal dec chunk, outMsg⟩ evsDec ∧
          PolyDecoderStrictSorted (addChunkTotal dec chunk)) :=
  ct1Sampled_recv_ek_add_and_decode_placed_ofPrePostEnv hadd_call hdec_call st_cost
    s0 s_in fsp msgA dec chunk outMsg hsorted hdec_msg hfits_add hfits_dec Rest
    hcro hfsp_align hpc hrun hsp hx24 htr

theorem ct1Sampled_recv_ek_add_and_decode_cont_placed_ofPrePostEnv [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {DecPre DecPost : PolyDecoderDecodedMessageGhost → List AllocEvent → Prop}
    {ext : String → Option (State → State)} {target_pc : BitVec 64}
    (hadd_call : subroutine_ok (lsProg_332 (Rust.withPanics ext))
      (lsmpl.base 419) (withLsCodeLoaded lsmpl (addChunkSpecX M A lim)))
    (hdec_call : subroutine_ok (lsProg_332 (Rust.withPanics ext))
      (lsmpl.base 418)
      (withLsCodeRoLoaded lsmpl
        (polyDecoderDecodedMessagePlacedSpecOfPrePostEnv M A lim DecPre DecPost)))
    (st_cost : M.σ) (s0 s_in : State) (fsp msgA : BitVec 64)
    (dec : PolyDecoder) (chunk : Chunk) (outMsg : Option Bytes)
    (hsorted : PolyDecoderStrictSorted dec)
    (hdec_msg : spqrPolyApi.decoded_message (addChunkTotal dec chunk) = .ok outMsg)
    (hfits_add : FitsEnv M lim st_cost (AddChunkEnv ⟨fsp + 2752#64, msgA + 10#64, dec, chunk⟩))
    (hfits_dec : ∀ evsAdd,
      AddChunkEnv ⟨fsp + 2752#64, msgA + 10#64, dec, chunk⟩ evsAdd →
      FitsEnv M lim (M.stepEvents evsAdd st_cost)
        (DecPre ⟨fsp + 3832#64, fsp + 2752#64, addChunkTotal dec chunk, outMsg⟩))
    (Rest : SepProp) {post : State → SepProp → Prop}
    (hcro : LibsignalCodeRoLoaded lsmpl s_in.mem) (hfsp_align : (fsp &&& 15#64 == 0#64) = true)
    (hpc : s_in.pc = (blkPl_332).base + 11472#64) (hrun : s_in.status = .Running)
    (hsp : s_in.sp = fsp) (hx24 : s_in.readReg64 .x24 = msgA) (htr : TraceCalleeSaved s_in s0)
    (hnext : ∀ (sf : State) (evsAdd evsDec : List AllocEvent),
      sf.pc = (blkPl_332).base + 11496#64 → sf.status = .Running → sf.sp = fsp →
      sf.readReg64 .x19 = s_in.readReg64 .x19 → sf.readReg64 .x20 = s_in.readReg64 .x20 →
      sf.readReg64 .x21 = s_in.readReg64 .x21 → sf.readReg64 .x22 = s_in.readReg64 .x22 →
      sf.readReg64 .x23 = s_in.readReg64 .x23 → sf.readReg64 .x24 = msgA →
      sf.readReg64 .x28 = s_in.readReg64 .x28 → sf.readReg64 .x29 = s_in.readReg64 .x29 →
      TraceCalleeSaved sf s0 → LibsignalCodeRoLoaded lsmpl sf.mem →
      AddChunkEnv ⟨fsp + 2752#64, msgA + 10#64, dec, chunk⟩ evsAdd →
      DecPost ⟨fsp + 3832#64, fsp + 2752#64, addChunkTotal dec chunk, outMsg⟩ evsDec →
      PolyDecoderStrictSorted (addChunkTotal dec chunk) →
      SepWP (lsProg_332 (Rust.withPanics ext)) target_pc sf
        (optVecU8At A.repAlloc (fsp + 3832#64) outMsg ∗
          polyDecoderAt A.repAlloc (fsp + 2752#64) (addChunkTotal dec chunk) ∗
          chunkAt (msgA + 10#64) chunk ∗ statesRecvRoPlacedAt ∗
          A.pool lim (M.stepEvents (evsAdd ++ evsDec) st_cost) sf ∗
          stackAt fsp statesRecvCalleeStackX ∗ Rest) post) :
    SepWP (lsProg_332 (Rust.withPanics ext)) target_pc s_in
      (memRegion (fsp + 3832#64) 24 ∗ polyDecoderAt A.repAlloc (fsp + 2752#64) dec ∗
        chunkAt (msgA + 10#64) chunk ∗ statesRecvRoPlacedAt ∗
        A.pool lim st_cost s_in ∗ stackAt fsp statesRecvCalleeStackX ∗ Rest) post := by
  refine SepWP.seq
    (ct1Sampled_recv_ek_add_and_decode_placed_ofPrePostEnv hadd_call hdec_call st_cost
      s0 s_in fsp msgA dec chunk outMsg hsorted hdec_msg hfits_add hfits_dec Rest
      hcro hfsp_align hpc hrun hsp hx24 htr) ?_
  rintro sf Pf hpc_sf hrun_sf ⟨evsAdd, evsDec, hPf, hsp_sf, hx19_sf, hx20_sf, hx21_sf,
    hx22_sf, hx23_sf, hx24_sf, hx28_sf, hx29_sf, htr_sf, hcro_sf, hevs_add, hevs_dec, hsorted'⟩
  exact SepWP.weaken_pre hPf
    (hnext sf evsAdd evsDec hpc_sf hrun_sf hsp_sf hx19_sf hx20_sf hx21_sf hx22_sf hx23_sf
      hx24_sf hx28_sf hx29_sf htr_sf hcro_sf hevs_add hevs_dec hsorted')

theorem ct1Sampled_recv_ek_add_and_decode_cont_placed [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {ext : String → Option (State → State)} {target_pc : BitVec 64}
    (hadd_call : subroutine_ok (lsProg_332 (Rust.withPanics ext))
      (lsmpl.base 419) (withLsCodeLoaded lsmpl (addChunkSpecX M A lim)))
    (hdec_call : subroutine_ok (lsProg_332 (Rust.withPanics ext))
      (lsmpl.base 418) (withLsCodeRoLoaded lsmpl (polyDecoderDecodedMessagePlacedSpec M A lim)))
    (st_cost : M.σ) (s0 s_in : State) (fsp msgA : BitVec 64)
    (dec : PolyDecoder) (chunk : Chunk) (outMsg : Option Bytes)
    (hsorted : PolyDecoderStrictSorted dec)
    (hdec_msg : spqrPolyApi.decoded_message (addChunkTotal dec chunk) = .ok outMsg)
    (hfits_add : FitsEnv M lim st_cost (AddChunkEnv ⟨fsp + 2752#64, msgA + 10#64, dec, chunk⟩))
    (hfits_dec : ∀ evsAdd,
      AddChunkEnv ⟨fsp + 2752#64, msgA + 10#64, dec, chunk⟩ evsAdd →
      FitsEnv M lim (M.stepEvents evsAdd st_cost)
        (PolyDecoderDecodedMessagePreEnv ⟨fsp + 3832#64, fsp + 2752#64, addChunkTotal dec chunk, outMsg⟩))
    (Rest : SepProp) {post : State → SepProp → Prop}
    (hcro : LibsignalCodeRoLoaded lsmpl s_in.mem) (hfsp_align : (fsp &&& 15#64 == 0#64) = true)
    (hpc : s_in.pc = (blkPl_332).base + 11472#64) (hrun : s_in.status = .Running)
    (hsp : s_in.sp = fsp) (hx24 : s_in.readReg64 .x24 = msgA) (htr : TraceCalleeSaved s_in s0)
    (hnext : ∀ (sf : State) (evsAdd evsDec : List AllocEvent),
      sf.pc = (blkPl_332).base + 11496#64 → sf.status = .Running → sf.sp = fsp →
      sf.readReg64 .x19 = s_in.readReg64 .x19 → sf.readReg64 .x20 = s_in.readReg64 .x20 →
      sf.readReg64 .x21 = s_in.readReg64 .x21 → sf.readReg64 .x22 = s_in.readReg64 .x22 →
      sf.readReg64 .x23 = s_in.readReg64 .x23 → sf.readReg64 .x24 = msgA →
      sf.readReg64 .x28 = s_in.readReg64 .x28 → sf.readReg64 .x29 = s_in.readReg64 .x29 →
      TraceCalleeSaved sf s0 → LibsignalCodeRoLoaded lsmpl sf.mem →
      AddChunkEnv ⟨fsp + 2752#64, msgA + 10#64, dec, chunk⟩ evsAdd →
      PolyDecoderDecodedMessagePostEnv ⟨fsp + 3832#64, fsp + 2752#64, addChunkTotal dec chunk, outMsg⟩ evsDec →
      PolyDecoderStrictSorted (addChunkTotal dec chunk) →
      SepWP (lsProg_332 (Rust.withPanics ext)) target_pc sf
        (optVecU8At A.repAlloc (fsp + 3832#64) outMsg ∗
          polyDecoderAt A.repAlloc (fsp + 2752#64) (addChunkTotal dec chunk) ∗
          chunkAt (msgA + 10#64) chunk ∗ statesRecvRoPlacedAt ∗
          A.pool lim (M.stepEvents (evsAdd ++ evsDec) st_cost) sf ∗
          stackAt fsp statesRecvCalleeStackX ∗ Rest) post) :
    SepWP (lsProg_332 (Rust.withPanics ext)) target_pc s_in
      (memRegion (fsp + 3832#64) 24 ∗ polyDecoderAt A.repAlloc (fsp + 2752#64) dec ∗
        chunkAt (msgA + 10#64) chunk ∗ statesRecvRoPlacedAt ∗
        A.pool lim st_cost s_in ∗ stackAt fsp statesRecvCalleeStackX ∗ Rest) post :=
  ct1Sampled_recv_ek_add_and_decode_cont_placed_ofPrePostEnv hadd_call hdec_call st_cost
    s0 s_in fsp msgA dec chunk outMsg hsorted hdec_msg hfits_add hfits_dec Rest
    hcro hfsp_align hpc hrun hsp hx24 htr hnext

end LibsignalBinary.Proofs.SpqrV1.States.Recv.ArmCt1SampledPart3PlacedBudget
