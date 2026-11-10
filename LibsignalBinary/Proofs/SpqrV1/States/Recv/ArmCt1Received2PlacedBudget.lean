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
public import LibsignalBinary.Proofs.SpqrV1.States.Leaves.DefsPlacedBudget
public import LibsignalBinary.Proofs.SpqrV1.States.Recv.ArmCt1Received1PlacedBudget
public import LibsignalBinary.Proofs.SpqrV1.States.Recv.ArmCt1Received2PlacedBudgetAux
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
# `<States>::recv` (Block `332`) — `.ct1Received` Arm, Part 2 (Budget-Threaded)

Assembles the complete budget-threaded relocatable `.ct1Received` arm
(`states_recv_arm_ct1Received_placed*`) and top-level `subroutine_ok` contracts
(`states_recv_ct1Received_{placed_ok_ext,exact_placed_ok_ext,cro_placed_ok_ext}*`).
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 400000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

namespace LibsignalBinary.Proofs.SpqrV1.States.Recv.ArmCt1Received2PlacedBudget

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

private theorem seq_vm_lscl {prog : Program} {pl : Arm64.Obj.MultiPlacement} {mid tgt : BitVec 64}
    {s : State} {P P_mid : SepProp} {Q : State → Prop} {post : State → SepProp → Prop}
    (hcl : LibsignalCodeLoaded pl s.mem)
    (h1 : SepWP prog mid s P (fun sm Pm => VmPreserved s sm ∧ (Pm ⊢ P_mid) ∧ Q sm))
    (h2 : ∀ sm : State, sm.pc = mid → sm.status = .Running →
      LibsignalCodeLoaded pl sm.mem → VmPreserved s sm → Q sm →
      SepWP prog tgt sm P_mid post) :
    SepWP prog tgt s P post :=
  SepWP.seq_frozen (fun _ _ h hkf => h.of_keepsFrozen hkf) hcl
    (SepWP.mono h1 fun sm _ hpc hrun ⟨hvm, hPm, hQ⟩ hclm =>
      SepWP.weaken_pre hPm (h2 sm hpc hrun hclm hvm hQ))

private theorem sepWPp_seq_vm_lscl [LibsignalPlacement] {prog : Program} {mid target : BitVec 64}
    {s : State} {P : SepProp} {P_mid : State → SepProp} {Q : State → Prop}
    {post onPanic : State → SepProp → Prop}
    (hcl : LibsignalCodeLoaded lsmpl s.mem)
    (h1 : SepWP prog mid s P (fun sm Pm => VmPreserved s sm ∧ (Pm ⊢ P_mid sm) ∧ Q sm))
    (h2 : ∀ sm : State, sm.pc = mid → sm.status = .Running → VmPreserved s sm → Q sm →
      LibsignalCodeLoaded lsmpl sm.mem → SepWPp prog target sm (P_mid sm) post onPanic) :
    SepWPp prog target s P post onPanic :=
  SepWPp.of_sepWP (CryptoVerification.sepWP_seq_lscl hcl
    (SepWP.mono h1 fun sm _ hpc hrun ⟨hvm, hPm, hQ⟩ hcl' =>
      SepWP.done hpc hrun (SepWPp.weaken_pre hPm (h2 sm hpc hrun hvm hQ hcl'))))

export LibsignalBinary.Proofs.SpqrV1.States.Recv.ArmCt1Received2PlacedBudgetAux (
  Ct1ReceivedArmPostEnv
  Ct1ReceivedArmPreEnv
  addChunkSlotEnv_new_bounded
  addChunkSlotsEnv_replicate_new_bounded
  call_ct1ReceivedRecvCt2Chunk_placed
  ct1ReceivedArmPostEnv_nil
  ct1ReceivedArmPostEnv_nonempty
  ct1ReceivedArmPostEnv_sub_statesRecvEnv
  ct1ReceivedArmPreEnv_nil
  ct1ReceivedArmPreEnv_nonempty
  ct1ReceivedArmPreEnv_sub_statesRecvEnv
  ct1ReceivedRecvCt2ChunkPostEnv_bounded
  ct1ReceivedRecvCt2ChunkPostEnv_sub_statesRecvEnv
  ct1ReceivedRecvCt2ChunkPreEnv_bounded
  ct1ReceivedRecvCt2ChunkPreEnv_sub_statesRecvEnv
  ct1Received_arm_eq_other_placed
  ct1Received_arm_eq_other_pool_placed
  ct1Received_arm_lt_pool_placed
  ct1Received_arm_lt_sat_placed
  ct1Received_post_call_56d78_sat_placed
  freeOnlyEvs_sub_statesRecvEnv
  seq_addChunk16_freeOnly_bounded
)

set_option maxHeartbeats 1600000 in
/-- Budget-threaded relocatable `.ct1Received` arm when `msg.epoch = st.uc.epoch` and
    `msg.payload = .ct2 chunk` (`+1204 -> s0.x30`, Block `332`). -/
theorem ct1Received_arm_eq_ct2_placed [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits} {F : ShaCompress}
    {CalleePre CalleePost : Ct1ReceivedRecvCt2ChunkGhost F → List AllocEvent → Prop}
    {ext : String → Option (State → State)}
    (hcall : subroutine_ok (lsProg_332 (Rust.withPanics ext))
      (lsmpl.base 346)
      (withLsCodeLoaded lsmpl
        (ct1ReceivedRecvCt2ChunkSpecOfPrePostEnv M A lim F CalleePre CalleePost)))
    (hmemcpy_sat : HookSat (Rust.withPanics ext) spqrMemcpySym (withVmPreserved sessionMemcpySpec))
    (st_cost : M.σ)
    (s0 s : State) (outA selfA msgA : BitVec 64)
    (st : Chunked.SendEk.Ct1Received spqrPolyApi (spqrAuthApi F))
    (msg : Message spqrPolyApi) (chunk : Chunk)
    (outSt : Chunked.SendEk.EkSentCt1Received spqrPolyApi (spqrAuthApi F))
    (P_rest : SepProp)
    (hcl : LibsignalCodeLoaded lsmpl s.mem)
    (heq : msg.epoch = st.uc.epoch)
    (hpay : msg.payload = .ct2 chunk)
    (hrecv : st.recv_ct2_chunk st.uc.epoch chunk = .ok outSt)
    (hfit : FitsEnv M lim st_cost
      (CalleePre ⟨(s0.sp - 4240#64) + 976#64, (s0.sp - 4240#64) + 1856#64, msgA + 10#64,
        st, chunk, outSt⟩))
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
        (lsLogFilterAddr ↦₆₄ 0#64) ∗
        A.pool lim st_cost s ∗
        stackAt (s0.sp - 4240#64) statesRecvCalleeStackX ∗
        memRegion (s0.sp - 4240#64) 4144 ∗
        statesRecvSavedCells s0)
      (fun sf Pf =>
        ∃ evs : List AllocEvent,
          CalleePost ⟨(s0.sp - 4240#64) + 976#64, (s0.sp - 4240#64) + 1856#64, msgA + 10#64,
            st, chunk, outSt⟩ evs ∧
          (Pf ⊢
            P_rest ∗
            resultV1RecvAt A.repAlloc (F := F) outA (.ok { key := none, state := .ekSentCt1Received outSt }) ∗
            memRegion selfA chunkedStatesSize ∗
            messageAt spqrPolyApi msgA msg ∗
            (lsLogFilterAddr ↦₆₄ 0#64) ∗
            A.pool lim (M.stepEvents evs st_cost) sf ∗
            stackAt s0.sp statesRecvStackX) ∧
          sf.sp = s0.sp ∧
          CalleeSavedPreserved s0 sf ∧
          sf.trace = s0.trace) := by
  have hcond1 := epoch_cmp_ct1r_eq_of_eq st.uc.epoch
  have hpost := @ct1Received_post_call_56d78_sat_placed _ A.repAlloc F ext hmemcpy_sat s0
  rw [lsmpl_base_332_eq] at hpc hpost
  dsimp only [lsProg_332, chunkedStatesAt, messageAt, BitVec.ofNat_eq_ofNat] at hpc hcall hpost ⊢
  refine SepWP.fold (memRegion_4144_entails_sendEkFrame (s0.sp - 4240#64)) (by sep_focus) ?_
  wp_pull_exists; rename_i sp
  refine SepWP.fold (sendEkUnusedAt_split_ac0 (s0.sp - 4240#64)) (by sep_focus) ?_
  wp_pull_exists; rename_i u_ac0
  refine SepWP.fold (memRegion_880_entails_words63_376
    ((s0.sp - 4240#64) + 1856#64) ((s0.sp - 4240#64) + 2360#64) (by bv_omega)) (by sep_focus) ?_
  wp_pull_exists; rename_i w_arg
  refine SepWP.fold (chunkedCt1ReceivedAt_extract63 A.repAlloc (selfA + 8#64) st) (by sep_focus) ?_
  wp_pull_exists; rename_i w
  refine SepWP.pure_elim fun hw62 => ?_
  have hsp_align' : (s0.sp &&& 15#64 == 0#64) = true := hsp_align
  have hfsp_align : ((s0.sp - 4240#64) &&& 15#64 == 0#64) = true :=
    spAligned_sub s0.sp 4240#64 hsp_align (by decide)
  let sp1 : SendEkSpills :=
    { b0 := ⟨w.b5.w2, sp.b0.w1, w.b3.w1, sp.b0.w3, sp.b0.w4, sp.b0.w5, w.b4.w0, sp.b0.w7,
             sp.b0.w8, w.b3.w3⟩
      b1 := ⟨sp.b1.w0, sp.b1.w1, w.b3.w9, sp.b1.w3, w.b5.w3, sp.b1.w5, w.b0.w0, w.b5.w9,
             w.b1.w5, w.b1.w6⟩
      b2 := ⟨w.b4.w7, w.b5.w1, w.b4.w9, sp.b2.w3, w.b4.w5, w.b0.w1, w.b4.w8, sp.b2.w7,
             msgA, w.b4.w2⟩
      b3 := ⟨w.b5.w8, w.w62, sp.b3.w2, sp.b3.w3, sp.b3.w4, sp.b3.w5, sp.b3.w6, sp.b3.w7,
             w.b3.w0, sp.b3.w9⟩
      b4 := ⟨sp.b4.w0, w.b1.w2, w.b1.w9, w.b1.w0, w.b2.w2, w.b0.w5, sp.b4.w6, w.b1.w1,
             w.b2.w0, w.b2.w3⟩
      b5 := ⟨w.b0.w9, w.b4.w4, w.b1.w4, w.b0.w8, w.b1.w7, w.b5.w0, sp.b5.w6, w.b2.w4,
             w.b4.w6, w.b5.w4⟩
      w60 := w.b5.w6
      w61 := w.b0.w2
      w62 := w.b0.w6
      q200 := sp.q200
      q210 := sp.q210
      q220 := sp.q220
      w230 := sp.w230
      q3c0 := sp.q3c0 }
  refine seq_vm_lscl hcl (mid := lsmpl.base 346)
    (P_mid :=
      memRegion selfA chunkedStatesSize ∗
      chunkedCt1ReceivedAt A.repAlloc ((s0.sp - 4240#64) + 1856#64) st ∗
      sendEkUnusedAt (s0.sp - 4240#64) ∗
      sendEkSpillsAt (s0.sp - 4240#64) sp1 ∗
      P_rest ∗
      ((msgA ↦₆₄ msg.epoch) ∗ ((msgA + 8#64) ↦₈ 6#8) ∗ memRegion (msgA + 9#64) 1 ∗
        chunkAt (msgA + 10#64) chunk ∗ memRegion (msgA + 44#64) 4) ∗
      (lsLogFilterAddr ↦₆₄ 0#64) ∗
      A.pool lim st_cost s ∗
      memRegion outA v1RecvSize ∗
      stackAt (s0.sp - 4240#64) statesRecvCalleeStackX ∗
      memRegion ((s0.sp - 4240#64) + 576#64) 376 ∗
      memRegion ((s0.sp - 4240#64) + 976#64) 880 ∗
      memRegion ((s0.sp - 4240#64) + 2360#64) 376 ∗
      statesRecvSavedCells s0)
    (Q := fun sm =>
      sm.sp = s0.sp - 4240#64 ∧
      sm.readReg64 Reg.lr = (blkPl_332).base + 6436#64 ∧
      sm.readReg64 Reg.x0 = (s0.sp - 4240#64) + 976#64 ∧
      sm.readReg64 .x1 = (s0.sp - 4240#64) + 1856#64 ∧
      sm.readReg64 .x2 = st.uc.epoch ∧
      sm.readReg64 .x3 = msgA + 10#64 ∧
      sm.readReg64 .x19 = outA ∧
      TraceCalleeSaved sm s0)
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
    have hfold_pre_call :
        ((selfA ↦₆₄ 5#64) ∗ words63At (selfA + 8#64) w ∗ memRegion (selfA + 512#64) 416) ∗
        (words63At ((s0.sp - 4240#64) + 1856#64) w ∗
         relocatedHeap (fun dst => chunkedCt1ReceivedAt A.repAlloc dst st) (wordsBytes (words63List w))) ∗
        (((s0.sp - 4240#64 + 2752#64) ↦₁₂₈ w.q60) ∗
         memRegion (s0.sp - 4240#64) 8 ∗
         memRegion (s0.sp - 4240#64 + 568#64) 8 ∗
         memRegion (s0.sp - 4240#64 + 952#64) 8 ∗
         memRegion (s0.sp - 4240#64 + 2736#64) 16 ∗
         memRegion (s0.sp - 4240#64 + 2768#64) 1376) ∗
        sendEkSpillsAt (s0.sp - 4240#64) sp1 ⊢
          memRegion selfA chunkedStatesSize ∗
          chunkedCt1ReceivedAt A.repAlloc ((s0.sp - 4240#64) + 1856#64) st ∗
          sendEkUnusedAt (s0.sp - 4240#64) ∗
          sendEkSpillsAt (s0.sp - 4240#64) sp1 :=
      sepConj_mono (words63At_self_entails_memRegion_928 selfA 5#64 w)
        (sepConj_mono (recompose63 ((s0.sp - 4240#64) + 1856#64) w)
          (sepConj_mono_left hfold_unused))
    generalize hsp0 : s0.sp = sp0 at hsp hsp_align' hfsp_align hfold_unused hfold_pre_call ⊢
    refine seq_vm_cont (mid := (blkPl_332).base + 5780#64) ?_
    by_vm_steps_nest (
      wp_conv_pre =>
        dsimp only [sendEkSpillsAt, words63At, words10At, lsLogFilterAddr]
        rw [hw62, heq, hpay, messagePayloadAt_ct2 msgA chunk]
        simp only [pointsTo128_eq_pair64_recv, BitVec.add_assoc, arm64_norm]
      wp_steps 256
      refine SepWP.done (by simp only [wp_norm, arm64_norm])
        (by simp only [wp_norm, arm64_norm]; assumption)
        ⟨by simp only [wp_norm, arm64_norm], fun hvmm => ?_⟩
      refine step_adrp_vm (rd := 8#5)
        (v := Arm64.Obj.pageOf (blkPl_332.ρ "_RNvCs4Dv7yoBiUx4_3log20MAX_LOG_LEVEL_FILTER"))
        (next_pc := (blkPl_332).base + 5784#64) hvmm ?_ ?_
      · apply blkPC_332_pairStep_0x1694
        · rfl
        · simp only [wp_norm, arm64_norm]
        · simp only [wp_norm, arm64_norm]; assumption
      · by_vm_steps_nest (
          wp_steps 256
          subst hsp0
          refine SepWP.fold
            (F := P_rest ∗
              ((msgA ↦₆₄ msg.epoch) ∗ ((msgA + 8#64) ↦₈ 6#8) ∗ memRegion (msgA + 9#64) 1 ∗
                chunkAt (msgA + 10#64) chunk ∗ memRegion (msgA + 44#64) 4) ∗
              (lsLogFilterAddr ↦₆₄ 0#64) ∗
              A.pool lim st_cost s ∗
              memRegion outA v1RecvSize ∗
              stackAt (s0.sp - 4240#64) statesRecvCalleeStackX ∗
              memRegion ((s0.sp - 4240#64) + 576#64) 376 ∗
              memRegion ((s0.sp - 4240#64) + 976#64) 880 ∗
              memRegion ((s0.sp - 4240#64) + 2360#64) 376 ∗
              statesRecvSavedCells s0)
            hfold_pre_call
            (by
              dsimp only [sendEkSpillsAt, words63At, words10At, lsLogFilterAddr, sp1]
              rw [hw62, heq]
              simp only [pointsTo128_eq_pair64_recv, BitVec.add_assoc, arm64_norm]
              sep_ac_rfl) ?_
          refine DropChunkedClPlacedBudgetAux.align_pre_vm (by sep_ac_rfl) ?_
          simp only [TraceCalleeSaved, Reg.lr, Reg.x0, Reg.x1, Reg.x2, Reg.x3, Reg.x19, Reg.x30,
            hsp, hx1, hx19, hx24, htr.1, htr.2, wp_norm, arm64_norm]
          wp_done
        )
    )
  · intro sm hpcm hrunm hcl1 hvm1 ⟨hsp_m, hlr_m, hx0_m, hx1_m, hx2_m, hx3_m, hx19_m, htr_m⟩
    rw [← A.pool_transport lim st_cost s sm hvm1]
    refine SepWP.focus_weaken
      (Entails.of_eq (memRegion_880_split_504_376
        ((s0.sp - 4240#64) + 976#64) ((s0.sp - 4240#64) + 1480#64) (by bv_omega)))
      (by sep_focus) ?_
    refine SepWP.focus_weaken
      (Entails.of_eq (stackAt_statesRecvCallee_split_ct1RecvCt2 (s0.sp - 4240#64)))
      (by sep_focus) ?_
    refine call_ct1ReceivedRecvCt2Chunk_placed hcall
      ((s0.sp - 4240#64) + 976#64) ((s0.sp - 4240#64) + 1856#64) (msgA + 10#64)
      st chunk outSt st_cost hrecv hfit
      (s0 := s0) (sp_call := s0.sp - 4240#64) (ret_pc := (blkPl_332).base + 6436#64)
      (Frame :=
        P_rest ∗
        memRegion selfA chunkedStatesSize ∗
        ((msgA ↦₆₄ msg.epoch) ∗ ((msgA + 8#64) ↦₈ 6#8) ∗ memRegion (msgA + 9#64) 1 ∗
          memRegion (msgA + 44#64) 4) ∗
        (lsLogFilterAddr ↦₆₄ 0#64) ∗
        memRegion outA v1RecvSize ∗
        memRegion ((s0.sp - 4240#64) - 19552#64) 2576 ∗
        memRegion ((s0.sp - 4240#64) + 576#64) 376 ∗
        memRegion ((s0.sp - 4240#64) + 1480#64) 376 ∗
        memRegion ((s0.sp - 4240#64) + 2360#64) 376 ∗
        sendEkUnusedAt (s0.sp - 4240#64) ∗
        sendEkSpillsAt (s0.sp - 4240#64) sp1 ∗
        statesRecvSavedCells s0)
      hcl1 hpcm hrunm hsp_m hfsp_align hlr_m htr_m hx0_m hx1_m hx2_m hx3_m
      (by
        dsimp only [chunkedEkSentCt1ReceivedSize, statesRecvCalleeStackX, recvCt2ChunkStackX,
          recvCt2ChunkFrameBytes, polyDecodedMessageStackX, extHookStack,
          ct1ReceivedRecvCt2ChunkStack, BitVec.ofNat_eq_ofNat]
        simp only [arm64_norm]
        sep_ac_rfl)
      ?_
    intro evs hevs sf_c hpc_c hrun_c hsp_c hcs_c htr_c
    have hrejoin_1856 :
        memRegion ((s0.sp - 4240#64) + 1856#64) chunkedCt1ReceivedSize ∗
        memRegion ((s0.sp - 4240#64) + 2360#64) 376 ⊢
          memRegion ((s0.sp - 4240#64) + 1856#64) 880 :=
      Entails.of_eq (memRegion_880_split_504_376
        ((s0.sp - 4240#64) + 1856#64) ((s0.sp - 4240#64) + 2360#64) (by bv_omega)).symm
    refine SepWP.focus_weaken hrejoin_1856 (by sep_focus) ?_
    refine SepWP.focus_weaken
      (Entails.of_eq (stackAt_statesRecvCallee_split_ct1RecvCt2 (s0.sp - 4240#64)).symm)
      (by sep_focus) ?_
    have hmsg_eq :
        ((msgA ↦₆₄ msg.epoch) ∗ ((msgA + 8#64) ↦₈ 6#8) ∗ memRegion (msgA + 9#64) 1 ∗
         chunkAt (msgA + 10#64) chunk ∗ memRegion (msgA + 44#64) 4) =
        ((msgA ↦₆₄ msg.epoch) ∗ messagePayloadAt spqrPolyApi msgA msg.payload) := by
      rw [hpay, messagePayloadAt_ct2 msgA chunk]
    have hx19_c : sf_c.readReg64 .x19 = outA := hcs_c.1.trans hx19_m
    refine SepWP.weaken_pre (Entails.of_eq ?_)
      (SepWP.mono
        (hpost sf_c outA outSt sp1
          (P_rest ∗
           memRegion selfA chunkedStatesSize ∗
           ((msgA ↦₆₄ msg.epoch) ∗ messagePayloadAt spqrPolyApi msgA msg.payload) ∗
           (lsLogFilterAddr ↦₆₄ 0#64) ∗
           A.pool lim (M.stepEvents evs st_cost) sf_c)
          hpc_c hrun_c hsp_c hsp_align hx19_c htr_c)
        (fun sf Pf _ _ ⟨hvm_post, hPf, hsp_sf, hcs_sf, htr_sf⟩ =>
          ⟨evs, hevs, Entails.trans hPf (Entails.of_eq (by
            rw [← A.pool_transport lim (M.stepEvents evs st_cost) sf_c sf hvm_post]
            sep_ac_rfl)),
           hsp_sf, hcs_sf, htr_sf⟩))
    rw [← hmsg_eq]
    simp only [arm64_norm]
    sep_ac_rfl

/-! ## Complete Relocatable `.ct1Received` Arm & Top-Level `subroutine_ok` Contracts -/

/-- Two-envelope (`PreEnv` / `PostEnv`) relocatable `.ct1Received` arm of `<States>::recv`
    (`+1204 -> s0.x30`, Block `332`). -/
theorem states_recv_arm_ct1Received_placed_ofPrePostEnv [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {F : ShaCompress} {K : MlKem}
    {CalleePre CalleePost : Ct1ReceivedRecvCt2ChunkGhost F → List AllocEvent → Prop}
    {PreEnv PostEnv : StatesRecvGhost F → List AllocEvent → Prop}
    {ext : String → Option (State → State)}
    (hdealloc : HookSat (Rust.withPanics ext) spqrDeallocSym (rustCliDeallocBudgetSpec M A lim))
    (hcall : subroutine_ok (lsProg_332 (Rust.withPanics ext))
      (lsmpl.base 346)
      (withLsCodeLoaded lsmpl
        (ct1ReceivedRecvCt2ChunkSpecOfPrePostEnv M A lim F CalleePre CalleePost)))
    (hmemcpy_sat : HookSat (Rust.withPanics ext) spqrMemcpySym (withVmPreserved sessionMemcpySpec))
    (st_cost : M.σ)
    (s0 s : State) (outA selfA msgA : BitVec 64)
    (st : Chunked.SendEk.Ct1Received spqrPolyApi (spqrAuthApi F))
    (msg : Message spqrPolyApi)
    (R : SepProp)
    (hFit : FitsEnv M lim st_cost (PreEnv ⟨outA, selfA, msgA, .ct1Received st, msg⟩))
    (hPre_ct2 : ∀ chunk outSt,
      msg.epoch = st.uc.epoch →
      msg.payload = .ct2 chunk →
      st.recv_ct2_chunk st.uc.epoch chunk = .ok outSt →
      FitsEnv M lim st_cost (PreEnv ⟨outA, selfA, msgA, .ct1Received st, msg⟩) →
      FitsEnv M lim st_cost
        (CalleePre ⟨(s0.sp - 4240#64) + 976#64, (s0.sp - 4240#64) + 1856#64, msgA + 10#64,
          st, chunk, outSt⟩))
    (hPost_gt : msg.epoch > st.uc.epoch →
      ∀ evs, FreeOnlyEvs evs → PostEnv ⟨outA, selfA, msgA, .ct1Received st, msg⟩ evs)
    (hPost_lt : msg.epoch < st.uc.epoch →
      PostEnv ⟨outA, selfA, msgA, .ct1Received st, msg⟩ [])
    (hPost_ct2 : ∀ chunk outSt evs,
      msg.epoch = st.uc.epoch →
      msg.payload = .ct2 chunk →
      st.recv_ct2_chunk st.uc.epoch chunk = .ok outSt →
      CalleePost ⟨(s0.sp - 4240#64) + 976#64, (s0.sp - 4240#64) + 1856#64, msgA + 10#64,
        st, chunk, outSt⟩ evs →
      PostEnv ⟨outA, selfA, msgA, .ct1Received st, msg⟩ evs)
    (hPost_other : msg.epoch = st.uc.epoch →
      (∀ c, msg.payload ≠ .ct2 c) →
      PostEnv ⟨outA, selfA, msgA, .ct1Received st, msg⟩ [])
    (hcl : LibsignalCodeLoaded lsmpl s.mem)
    (hpc : s.pc = lsmpl.base 332 + 1204#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = s0.sp - 4240#64)
    (hsp_align : s0.spAligned = true)
    (hx1 : s.readReg64 .x1 = selfA)
    (hx19 : s.readReg64 .x19 = outA)
    (hx24 : s.readReg64 .x24 = msgA)
    (htr : TraceCalleeSaved s s0) :
    SepWPp (lsProg_332 (Rust.withPanics ext)) (s0.readReg64 Reg.lr) s
      (memRegion outA v1RecvSize ∗
        chunkedStatesAt A.repAlloc selfA (.ct1Received st) ∗
        messageAt spqrPolyApi msgA msg ∗
        statesRecvRoPlacedAt ∗
        A.pool lim st_cost s ∗
        stackAt (s0.sp - 4240#64) statesRecvCalleeStackX ∗
        memRegion (s0.sp - 4240#64) 4144 ∗
        statesRecvSavedCells s0)
      (fun sf P_f =>
        (sf.mem ⊨ P_f ∗ R →
          sf.mem ⊨
            (DefsPlacedBudget.statesRecvVariantPlacedSpecOfPrePostEnv M A lim F K (.ct1Received st) msg PreEnv PostEnv).post
              ((outA, selfA, msgA), st_cost) s0 sf ∗ R) ∧
        sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf)
      (fun sf P_f =>
        (sf.mem ⊨ P_f ∗ R) →
          (sf.mem ⊨
            (DefsPlacedBudget.statesRecvVariantPlacedSpecOfPrePostEnv M A lim F K (.ct1Received st) msg PreEnv PostEnv).onPanic
              ((outA, selfA, msgA), st_cost) s0 sf ∗ R)) := by
  by_cases hgt : msg.epoch > st.uc.epoch
  · refine sepWPp_of_statesRecv_exit_placed_ofPrePostEnv s0 s outA selfA msgA (.ct1Received st) msg
      st_cost _ R ?_
    rw [states_recv_ct1Received_gt K st msg hgt]
    refine SepWP.weaken_pre
      (P' := statesRecvRoPlacedAt ∗ memRegion outA v1RecvSize ∗
        chunkedStatesAt A.repAlloc selfA (.ct1Received st) ∗
        messageAt spqrPolyApi msgA msg ∗ A.pool lim st_cost s ∗
        stackAt (s0.sp - 4240#64) statesRecvCalleeStackX ∗ memRegion (s0.sp - 4240#64) 4144 ∗
        statesRecvSavedCells s0)
      (Entails.of_eq (by sep_ac_rfl))
      (SepWP.mono
        (ct1Received_arm_gt_placed hdealloc st_cost s0 s outA selfA msgA st msg statesRecvRoPlacedAt
          hgt hcl hpc hrun hsp hsp_align hx1 hx19 hx24 htr)
        fun sf Pf _ _ ⟨evs, hevs, hPf, hsp_sf, _, hcs_sf, htr_sf⟩ =>
          ⟨⟨evs, hPost_gt hgt evs hevs, Entails.trans hPf (Entails.of_eq (by sep_ac_rfl))⟩,
           hsp_sf, hcs_sf, htr_sf⟩)
  · by_cases hlt : msg.epoch < st.uc.epoch
    · refine sepWPp_of_statesRecv_exit_placed_ofPrePostEnv s0 s outA selfA msgA (.ct1Received st) msg
        st_cost _ R ?_
      rw [states_recv_ct1Received_lt K st msg hlt]
      refine SepWP.weaken_pre
        (P' := statesRecvRoPlacedAt ∗ memRegion outA v1RecvSize ∗
          chunkedStatesAt A.repAlloc selfA (.ct1Received st) ∗
          messageAt spqrPolyApi msgA msg ∗ A.pool lim st_cost s ∗
          stackAt (s0.sp - 4240#64) statesRecvCalleeStackX ∗ memRegion (s0.sp - 4240#64) 4144 ∗
          statesRecvSavedCells s0)
        (Entails.of_eq (by sep_ac_rfl))
        (SepWP.mono
          (ct1Received_arm_lt_pool_placed hmemcpy_sat st_cost s0 s outA selfA msgA st msg
            statesRecvRoPlacedAt hlt hpc hrun hsp hsp_align hx1 hx19 hx24 htr)
          fun sf Pf _ _ ⟨_, hPf, hsp_sf, hcs_sf, htr_sf⟩ =>
            ⟨⟨[], hPost_lt hlt, Entails.trans hPf (Entails.of_eq (by sep_ac_rfl))⟩,
             hsp_sf, hcs_sf, htr_sf⟩)
    · have heq : msg.epoch = st.uc.epoch := by
        have h1 : ¬ (st.uc.epoch < msg.epoch) := hgt
        have h2 : ¬ (msg.epoch < st.uc.epoch) := hlt
        exact BitVec.le_antisymm (BitVec.not_lt.mp h1) (BitVec.not_lt.mp h2)
      cases hpay : msg.payload with
      | ct2 chunk =>
        obtain ⟨outSt, hrecv, _⟩ := ct1Received_recv_ct2_chunk_eq_ok st chunk
        refine sepWPp_of_statesRecv_exit_placed_ofPrePostEnv s0 s outA selfA msgA (.ct1Received st) msg
          st_cost _ R ?_
        rw [states_recv_ct1Received_eq_ct2 K st msg chunk outSt heq hpay hrecv]
        refine SepWP.weaken_pre
          (P' := (statesRecvJumpTablePlacedAt ∗
              ((lsρ "spqr:.rodata..Lanon.137") ↦ᵣ Authenticator.ctLabel) ∗
              tokenInitPlacedAt ∗ reduceTablePlacedAt) ∗
            memRegion outA v1RecvSize ∗
            chunkedStatesAt A.repAlloc selfA (.ct1Received st) ∗
            messageAt spqrPolyApi msgA msg ∗
            (lsLogFilterAddr ↦₆₄ 0#64) ∗
            A.pool lim st_cost s ∗
            stackAt (s0.sp - 4240#64) statesRecvCalleeStackX ∗
            memRegion (s0.sp - 4240#64) 4144 ∗
            statesRecvSavedCells s0)
          (Entails.of_eq (by dsimp only [statesRecvRoPlacedAt, unchunkedSendCt2PlacedRoAt]; sep_ac_rfl))
          (SepWP.mono
            (ct1Received_arm_eq_ct2_placed hcall hmemcpy_sat st_cost s0 s outA selfA msgA st msg
              chunk outSt
              (statesRecvJumpTablePlacedAt ∗
                ((lsρ "spqr:.rodata..Lanon.137") ↦ᵣ Authenticator.ctLabel) ∗
                tokenInitPlacedAt ∗ reduceTablePlacedAt)
              hcl heq hpay hrecv (hPre_ct2 chunk outSt heq hpay hrecv hFit)
              hpc hrun hsp hsp_align hx1 hx19 hx24 htr)
            fun sf Pf _ _ ⟨evs, hevs, hPf, hsp_sf, hcs_sf, htr_sf⟩ =>
              ⟨⟨evs, hPost_ct2 chunk outSt evs heq hpay hrecv hevs,
                Entails.trans hPf (Entails.of_eq (by
                  dsimp only [statesRecvRoPlacedAt, unchunkedSendCt2PlacedRoAt]; sep_ac_rfl))⟩,
               hsp_sf, hcs_sf, htr_sf⟩)
      | none | hdr _ | ek _ | ekCt1Ack _ | ct1Ack _ | ct1 _ =>
        have hct2 : ∀ c, msg.payload ≠ .ct2 c := by intro c hc; rw [hpay] at hc; cases hc
        refine sepWPp_of_statesRecv_exit_placed_ofPrePostEnv s0 s outA selfA msgA (.ct1Received st) msg
          st_cost _ R ?_
        rw [states_recv_ct1Received_eq_other K st msg heq hct2]
        refine SepWP.weaken_pre
          (P' := statesRecvRoPlacedAt ∗ memRegion outA v1RecvSize ∗
            chunkedStatesAt A.repAlloc selfA (.ct1Received st) ∗
            messageAt spqrPolyApi msgA msg ∗ A.pool lim st_cost s ∗
            stackAt (s0.sp - 4240#64) statesRecvCalleeStackX ∗ memRegion (s0.sp - 4240#64) 4144 ∗
            statesRecvSavedCells s0)
          (Entails.of_eq (by sep_ac_rfl))
          (SepWP.mono
            (ct1Received_arm_eq_other_pool_placed hmemcpy_sat st_cost s0 s outA selfA msgA st msg
              statesRecvRoPlacedAt heq hct2 hpc hrun hsp hsp_align hx1 hx19 hx24 htr)
            fun sf Pf _ _ ⟨_, hPf, hsp_sf, hcs_sf, htr_sf⟩ =>
              ⟨⟨[], hPost_other heq hct2, Entails.trans hPf (Entails.of_eq (by sep_ac_rfl))⟩,
               hsp_sf, hcs_sf, htr_sf⟩)

/-- Exact-envelope (`Ct1ReceivedArmPreEnv` / `Ct1ReceivedArmPostEnv`) relocatable `.ct1Received` arm
    of `<States>::recv` (`+1204 -> s0.x30`, Block `332`). -/
theorem states_recv_arm_ct1Received_exact_placed [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {F : ShaCompress} {K : MlKem}
    {ext : String → Option (State → State)}
    (hdealloc : HookSat (Rust.withPanics ext) spqrDeallocSym (rustCliDeallocBudgetSpec M A lim))
    (hcall : subroutine_ok (lsProg_332 (Rust.withPanics ext))
      (lsmpl.base 346)
      (withLsCodeLoaded lsmpl (ct1ReceivedRecvCt2ChunkSpec M A lim F)))
    (hmemcpy_sat : HookSat (Rust.withPanics ext) spqrMemcpySym (withVmPreserved sessionMemcpySpec))
    (st_cost : M.σ)
    (s0 s : State) (outA selfA msgA : BitVec 64)
    (st : Chunked.SendEk.Ct1Received spqrPolyApi (spqrAuthApi F))
    (msg : Message spqrPolyApi)
    (R : SepProp)
    (hFit : FitsEnv M lim st_cost (Ct1ReceivedArmPreEnv st msg))
    (hcl : LibsignalCodeLoaded lsmpl s.mem)
    (hpc : s.pc = lsmpl.base 332 + 1204#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = s0.sp - 4240#64)
    (hsp_align : s0.spAligned = true)
    (hx1 : s.readReg64 .x1 = selfA)
    (hx19 : s.readReg64 .x19 = outA)
    (hx24 : s.readReg64 .x24 = msgA)
    (htr : TraceCalleeSaved s s0) :
    SepWPp (lsProg_332 (Rust.withPanics ext)) (s0.readReg64 Reg.lr) s
      (memRegion outA v1RecvSize ∗
        chunkedStatesAt A.repAlloc selfA (.ct1Received st) ∗
        messageAt spqrPolyApi msgA msg ∗
        statesRecvRoPlacedAt ∗
        A.pool lim st_cost s ∗
        stackAt (s0.sp - 4240#64) statesRecvCalleeStackX ∗
        memRegion (s0.sp - 4240#64) 4144 ∗
        statesRecvSavedCells s0)
      (fun sf P_f =>
        (sf.mem ⊨ P_f ∗ R →
          sf.mem ⊨
            (DefsPlacedBudget.statesRecvVariantPlacedSpecOfPrePostEnv M A lim F K (.ct1Received st) msg
              (fun _ => Ct1ReceivedArmPreEnv st msg)
              (fun _ => Ct1ReceivedArmPostEnv st msg)).post
              ((outA, selfA, msgA), st_cost) s0 sf ∗ R) ∧
        sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf)
      (fun sf P_f =>
        (sf.mem ⊨ P_f ∗ R) →
          (sf.mem ⊨
            (DefsPlacedBudget.statesRecvVariantPlacedSpecOfPrePostEnv M A lim F K (.ct1Received st) msg
              (fun _ => Ct1ReceivedArmPreEnv st msg)
              (fun _ => Ct1ReceivedArmPostEnv st msg)).onPanic
              ((outA, selfA, msgA), st_cost) s0 sf ∗ R)) := by
  refine states_recv_arm_ct1Received_placed_ofPrePostEnv
    (PreEnv := fun _ => Ct1ReceivedArmPreEnv st msg)
    (PostEnv := fun _ => Ct1ReceivedArmPostEnv st msg)
    hdealloc hcall hmemcpy_sat st_cost s0 s outA selfA msgA st msg R hFit
    ?_ ?_ (fun _ => ct1ReceivedArmPostEnv_nil st msg) ?_
    (fun _ _ => ct1ReceivedArmPostEnv_nil st msg)
    hcl hpc hrun hsp hsp_align hx1 hx19 hx24 htr
  · intro chunk outSt heq hpay _ hF
    have hEqEnv : Ct1ReceivedArmPreEnv st msg =
        Ct1ReceivedRecvCt2ChunkPreEnv
          ⟨(s0.sp - 4240#64) + 976#64, (s0.sp - 4240#64) + 1856#64, msgA + 10#64,
            st, chunk, outSt⟩ := by
      funext evs
      unfold Ct1ReceivedArmPreEnv Ct1ReceivedRecvCt2ChunkPreEnv
      have hngt : ¬ (msg.epoch > st.uc.epoch) := by rw [heq]; exact BitVec.lt_irrefl _
      have hnlt : ¬ (msg.epoch < st.uc.epoch) := by rw [heq]; exact BitVec.lt_irrefl _
      simp only [hngt, hnlt, ↓reduceIte, hpay]
    rwa [← hEqEnv]
  · intro hgt evs hevs
    unfold Ct1ReceivedArmPostEnv
    simp only [hgt, ↓reduceIte]
    exact hevs
  · intro chunk outSt evs heq hpay _ hevs
    unfold Ct1ReceivedArmPostEnv
    have hngt : ¬ (msg.epoch > st.uc.epoch) := by rw [heq]; exact BitVec.lt_irrefl _
    have hnlt : ¬ (msg.epoch < st.uc.epoch) := by rw [heq]; exact BitVec.lt_irrefl _
    simp only [hngt, hnlt, ↓reduceIte, hpay]
    exact hevs

/-- Default `StatesRecvEnv` relocatable `.ct1Received` arm of `<States>::recv`
    (`+1204 -> s0.x30`, Block `332`). -/
theorem states_recv_arm_ct1Received_placed [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {F : ShaCompress} {K : MlKem}
    {ext : String → Option (State → State)}
    (hdealloc : HookSat (Rust.withPanics ext) spqrDeallocSym (rustCliDeallocBudgetSpec M A lim))
    (hcall : subroutine_ok (lsProg_332 (Rust.withPanics ext))
      (lsmpl.base 346)
      (withLsCodeLoaded lsmpl (ct1ReceivedRecvCt2ChunkSpec M A lim F)))
    (hmemcpy_sat : HookSat (Rust.withPanics ext) spqrMemcpySym (withVmPreserved sessionMemcpySpec))
    (st_cost : M.σ)
    (s0 s : State) (outA selfA msgA : BitVec 64)
    (st : Chunked.SendEk.Ct1Received spqrPolyApi (spqrAuthApi F))
    (msg : Message spqrPolyApi)
    (R : SepProp)
    (hFit : FitsEnv M lim st_cost (StatesRecvEnv ⟨outA, selfA, msgA, .ct1Received st, msg⟩))
    (hcl : LibsignalCodeLoaded lsmpl s.mem)
    (hpc : s.pc = lsmpl.base 332 + 1204#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = s0.sp - 4240#64)
    (hsp_align : s0.spAligned = true)
    (hx1 : s.readReg64 .x1 = selfA)
    (hx19 : s.readReg64 .x19 = outA)
    (hx24 : s.readReg64 .x24 = msgA)
    (htr : TraceCalleeSaved s s0) :
    SepWPp (lsProg_332 (Rust.withPanics ext)) (s0.readReg64 Reg.lr) s
      (memRegion outA v1RecvSize ∗
        chunkedStatesAt A.repAlloc selfA (.ct1Received st) ∗
        messageAt spqrPolyApi msgA msg ∗
        statesRecvRoPlacedAt ∗
        A.pool lim st_cost s ∗
        stackAt (s0.sp - 4240#64) statesRecvCalleeStackX ∗
        memRegion (s0.sp - 4240#64) 4144 ∗
        statesRecvSavedCells s0)
      (fun sf P_f =>
        (sf.mem ⊨ P_f ∗ R →
          sf.mem ⊨
            (DefsPlacedBudget.statesRecvVariantPlacedSpec M A lim F K (.ct1Received st) msg).post
              ((outA, selfA, msgA), st_cost) s0 sf ∗ R) ∧
        sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf)
      (fun sf P_f =>
        (sf.mem ⊨ P_f ∗ R) →
          (sf.mem ⊨
            (DefsPlacedBudget.statesRecvVariantPlacedSpec M A lim F K (.ct1Received st) msg).onPanic
              ((outA, selfA, msgA), st_cost) s0 sf ∗ R)) :=
  states_recv_arm_ct1Received_placed_ofPrePostEnv
    (PreEnv := StatesRecvEnv) (PostEnv := StatesRecvEnv)
    hdealloc hcall hmemcpy_sat st_cost s0 s outA selfA msgA st msg R hFit
    (fun _ _ _ _ _ hF => FitsEnv.mono
      (fun _ h => ct1ReceivedRecvCt2ChunkPreEnv_sub_statesRecvEnv _ h) hF)
    (fun _ _ hevs => freeOnlyEvs_sub_statesRecvEnv _ hevs)
    (fun _ => Top.Recv.DefsPlacedBudget.StatesRecvEnv.nil _)
    (fun _ _ _ _ _ _ hevs => ct1ReceivedRecvCt2ChunkPostEnv_sub_statesRecvEnv _ hevs)
    (fun _ _ => Top.Recv.DefsPlacedBudget.StatesRecvEnv.nil _)
    hcl hpc hrun hsp hsp_align hx1 hx19 hx24 htr

/-- Envelope-parametric top-level relocatable `subroutine_ok` theorem for `<States>::recv`
    (Block `332`) on the `.ct1Received` variant with `withLsCodeLoaded lsmpl`. -/
theorem states_recv_ct1Received_placed_ok_ext_ofPrePostEnv [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {F : ShaCompress} {K : MlKem} {envs : StatesRecvCalleeEnvs F}
    {PreEnv PostEnv : StatesRecvGhost F → List AllocEvent → Prop}
    {ext : String → Option (State → State)}
    (hC : DefsPlacedBudget.StatesRecvPlacedContractsOfEnv M A lim F K envs ext)
    (st : Chunked.SendEk.Ct1Received spqrPolyApi (spqrAuthApi F))
    (msg : Message spqrPolyApi)
    (hPre_ct2 : ∀ (outA selfA msgA fsp : BitVec 64) (st_cost : M.σ) chunk outSt,
      msg.epoch = st.uc.epoch →
      msg.payload = .ct2 chunk →
      st.recv_ct2_chunk st.uc.epoch chunk = .ok outSt →
      FitsEnv M lim st_cost (PreEnv ⟨outA, selfA, msgA, .ct1Received st, msg⟩) →
      FitsEnv M lim st_cost
        (envs.ct1ReceivedRecvCt2Pre ⟨fsp + 976#64, fsp + 1856#64, msgA + 10#64,
          st, chunk, outSt⟩))
    (hPost_gt : ∀ outA selfA msgA, msg.epoch > st.uc.epoch →
      ∀ evs, FreeOnlyEvs evs → PostEnv ⟨outA, selfA, msgA, .ct1Received st, msg⟩ evs)
    (hPost_lt : ∀ outA selfA msgA, msg.epoch < st.uc.epoch →
      PostEnv ⟨outA, selfA, msgA, .ct1Received st, msg⟩ [])
    (hPost_ct2 : ∀ (outA selfA msgA fsp : BitVec 64) chunk outSt evs,
      msg.epoch = st.uc.epoch →
      msg.payload = .ct2 chunk →
      st.recv_ct2_chunk st.uc.epoch chunk = .ok outSt →
      envs.ct1ReceivedRecvCt2Post ⟨fsp + 976#64, fsp + 1856#64, msgA + 10#64,
        st, chunk, outSt⟩ evs →
      PostEnv ⟨outA, selfA, msgA, .ct1Received st, msg⟩ evs)
    (hPost_other : ∀ outA selfA msgA, msg.epoch = st.uc.epoch →
      (∀ c, msg.payload ≠ .ct2 c) →
      PostEnv ⟨outA, selfA, msgA, .ct1Received st, msg⟩ []) :
    subroutine_ok (lsProg_332 (Rust.withPanics ext))
      (lsmpl.base 332)
      (withLsCodeLoaded lsmpl
        (DefsPlacedBudget.statesRecvVariantPlacedSpecOfPrePostEnv M A lim F K (.ct1Received st) msg PreEnv PostEnv)) := by
  apply subroutine_ok_of_sepWPp
  rintro ⟨⟨outA, selfA, msgA⟩, st_cost⟩ R s0 hpc0 hrun0 hpre hsp0_align
  obtain ⟨hcl0, hpre⟩ := extract_withLsCodeLoaded hpre
  simp only [DefsPlacedBudget.statesRecvVariantPlacedSpecOfPrePostEnv, sepConj_assoc, satisfies_pure_sepConj] at hpre
  rcases hpre with ⟨⟨hx0, hx1, hx2, _, hfit, _hlr_ls⟩, hmem⟩
  refine ⟨stackAt s0.sp statesRecvStackX ∗ A.pool lim st_cost s0 ∗
      (memRegion outA v1RecvSize ∗ chunkedStatesAt A.repAlloc selfA (.ct1Received st) ∗
       messageAt spqrPolyApi msgA msg ∗ statesRecvRoPlacedAt),
    R, Satisfies.mono (Entails.of_eq (by sep_ac_rfl)) hmem, ?_⟩
  have hpro := states_recv_prologue_pool_placed (A := A) (lim := lim) (ext := ext) st_cost s0
    (memRegion outA v1RecvSize ∗ chunkedStatesAt A.repAlloc selfA (.ct1Received st) ∗
     messageAt spqrPolyApi msgA msg ∗ statesRecvRoPlacedAt) hsp0_align hpc0 hrun0
  refine sepWPp_seq_vm_lscl hcl0 hpro ?_
  intro s1 hpc1 hrun1 _ ⟨_, hsp1, hx0_1, hx1_1, hx2_1, _, hx29_1, htr1⟩ hcl1
  rw [hx0] at hx0_1; rw [hx1] at hx1_1; rw [hx2] at hx2_1
  dsimp only [chunkedStatesAt]
  have hdisp := states_recv_dispatch_pool_placed (A := A) (lim := lim) (ext := ext) st_cost s1
    (s0.sp - 4240#64) selfA 5#64
    (chunkedCt1ReceivedAt A.repAlloc (selfA + 8#64) st ∗ memRegion (selfA + 512#64) 416 ∗
     memRegion outA v1RecvSize ∗ messageAt spqrPolyApi msgA msg ∗
     stackAt (s0.sp - 4240#64) statesRecvCalleeStackX ∗ memRegion (s0.sp - 4240#64) 4144 ∗
     statesRecvSavedCells s0)
    (by unfold ValidStatesTag; decide) hpc1 hrun1 hsp1 hx1_1
  refine sepWPp_seq_vm_lscl hcl1 (SepWP.weaken_pre (Entails.of_eq (by sep_ac_rfl)) hdisp) ?_
  intro s2 hpc2 hrun2 _ ⟨hsp2, hx0_2, hx1_2, hx2_2, _, _, _, hx19_2, _, hx24_2, _, hx29_2, htr2⟩ hcl2
  rw [hx0_1] at hx19_2; rw [hx2_1] at hx24_2
  have hpre2 :
      (selfA ↦₆₄ 5#64) ∗ statesRecvRoPlacedAt ∗ A.pool lim st_cost s2 ∗
      (chunkedCt1ReceivedAt A.repAlloc (selfA + 8#64) st ∗ memRegion (selfA + 512#64) 416 ∗
       memRegion outA v1RecvSize ∗ messageAt spqrPolyApi msgA msg ∗
       stackAt (s0.sp - 4240#64) statesRecvCalleeStackX ∗ memRegion (s0.sp - 4240#64) 4144 ∗
       statesRecvSavedCells s0) ⊢
      memRegion outA v1RecvSize ∗ chunkedStatesAt A.repAlloc selfA (.ct1Received st) ∗
      messageAt spqrPolyApi msgA msg ∗ statesRecvRoPlacedAt ∗ A.pool lim st_cost s2 ∗
      stackAt (s0.sp - 4240#64) statesRecvCalleeStackX ∗ memRegion (s0.sp - 4240#64) 4144 ∗
      statesRecvSavedCells s0 := by
    dsimp only [chunkedStatesAt]; exact Entails.of_eq (by sep_ac_rfl)
  refine SepWPp.weaken_pre hpre2 ?_
  exact states_recv_arm_ct1Received_placed_ofPrePostEnv
    (PreEnv := PreEnv) (PostEnv := PostEnv)
    hC.hdealloc_sat hC.ct1ReceivedRecvCt2Chunk_ok hC.hmemcpy_sat st_cost
    s0 s2 outA selfA msgA st msg R hfit
    (hPre_ct2 outA selfA msgA (s0.sp - 4240#64) st_cost)
    (hPost_gt outA selfA msgA)
    (hPost_lt outA selfA msgA)
    (hPost_ct2 outA selfA msgA (s0.sp - 4240#64))
    (hPost_other outA selfA msgA)
    hcl2 hpc2 hrun2 hsp2 hsp0_align hx1_2 hx19_2 hx24_2 (htr2.trans htr1)

/-- Exact-envelope (`Ct1ReceivedArmPreEnv` / `Ct1ReceivedArmPostEnv`) top-level relocatable
    `subroutine_ok` theorem for `<States>::recv` (Block `332`) on the `.ct1Received` variant. -/
theorem states_recv_ct1Received_exact_placed_ok_ext [LibsignalPlacement]
    (M : AllocCostModel) (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (F : ShaCompress) (K : MlKem)
    (ext : String → Option (State → State))
    (hC : DefsPlacedBudget.StatesRecvPlacedContracts M A lim F K ext)
    (st : Chunked.SendEk.Ct1Received spqrPolyApi (spqrAuthApi F))
    (msg : Message spqrPolyApi) :
    subroutine_ok (lsProg_332 (Rust.withPanics ext))
      (lsmpl.base 332)
      (withLsCodeLoaded lsmpl
        (DefsPlacedBudget.statesRecvVariantPlacedSpecOfPrePostEnv M A lim F K (.ct1Received st) msg
          (fun _ => Ct1ReceivedArmPreEnv st msg)
          (fun _ => Ct1ReceivedArmPostEnv st msg))) := by
  refine states_recv_ct1Received_placed_ok_ext_ofPrePostEnv hC st msg ?_ ?_
    (fun _ _ _ _ => ct1ReceivedArmPostEnv_nil st msg) ?_
    (fun _ _ _ _ _ => ct1ReceivedArmPostEnv_nil st msg)
  · intro _ _ msgA fsp st_cost chunk outSt heq hpay _ hF
    have hEqEnv : Ct1ReceivedArmPreEnv st msg =
        Ct1ReceivedRecvCt2ChunkPreEnv
          ⟨fsp + 976#64, fsp + 1856#64, msgA + 10#64, st, chunk, outSt⟩ := by
      funext evs
      unfold Ct1ReceivedArmPreEnv Ct1ReceivedRecvCt2ChunkPreEnv
      have hngt : ¬ (msg.epoch > st.uc.epoch) := by rw [heq]; exact BitVec.lt_irrefl _
      have hnlt : ¬ (msg.epoch < st.uc.epoch) := by rw [heq]; exact BitVec.lt_irrefl _
      simp only [hngt, hnlt, ↓reduceIte, hpay]
    dsimp only [DefsPlacedBudget.statesRecvCalleeEnvs]
    rwa [← hEqEnv]
  · intro _ _ _ hgt evs hevs
    unfold Ct1ReceivedArmPostEnv
    simp only [hgt, ↓reduceIte]
    exact hevs
  · intro _ _ _ _ chunk outSt evs heq hpay _ hevs
    unfold Ct1ReceivedArmPostEnv
    have hngt : ¬ (msg.epoch > st.uc.epoch) := by rw [heq]; exact BitVec.lt_irrefl _
    have hnlt : ¬ (msg.epoch < st.uc.epoch) := by rw [heq]; exact BitVec.lt_irrefl _
    simp only [hngt, hnlt, ↓reduceIte, hpay]
    exact hevs

/-- Default `StatesRecvEnv` top-level relocatable `subroutine_ok` theorem for `<States>::recv`
    (Block `332`) on the `.ct1Received` variant with `withLsCodeLoaded lsmpl`. -/
theorem states_recv_ct1Received_placed_ok_ext [LibsignalPlacement]
    (M : AllocCostModel) (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (F : ShaCompress) (K : MlKem)
    (ext : String → Option (State → State))
    (hC : DefsPlacedBudget.StatesRecvPlacedContracts M A lim F K ext)
    (st : Chunked.SendEk.Ct1Received spqrPolyApi (spqrAuthApi F))
    (msg : Message spqrPolyApi) :
    subroutine_ok (lsProg_332 (Rust.withPanics ext))
      (lsmpl.base 332)
      (withLsCodeLoaded lsmpl
        (DefsPlacedBudget.statesRecvVariantPlacedSpec M A lim F K (.ct1Received st) msg)) :=
  states_recv_ct1Received_placed_ok_ext_ofPrePostEnv
    (PreEnv := StatesRecvEnv) (PostEnv := StatesRecvEnv)
    hC st msg
    (fun _ _ msgA fsp _ chunk outSt _ _ _ hF => FitsEnv.mono
      (fun _ (h : Ct1ReceivedRecvCt2ChunkPreEnv
          ⟨fsp + 976#64, fsp + 1856#64, msgA + 10#64, st, chunk, outSt⟩ _) =>
        ct1ReceivedRecvCt2ChunkPreEnv_sub_statesRecvEnv _ h) hF)
    (fun _ _ _ _ _ hevs => freeOnlyEvs_sub_statesRecvEnv _ hevs)
    (fun _ _ _ _ => Top.Recv.DefsPlacedBudget.StatesRecvEnv.nil _)
    (fun _ _ msgA fsp chunk outSt _ _ _ _
        (hevs : Ct1ReceivedRecvCt2ChunkPostEnv
          ⟨fsp + 976#64, fsp + 1856#64, msgA + 10#64, st, chunk, outSt⟩ _) =>
      ct1ReceivedRecvCt2ChunkPostEnv_sub_statesRecvEnv _ hevs)
    (fun _ _ _ _ _ => Top.Recv.DefsPlacedBudget.StatesRecvEnv.nil _)

theorem states_recv_ct1Received_cro_placed_ok_ext_ofPrePostEnv [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {F : ShaCompress} {K : MlKem} {envs : StatesRecvCalleeEnvs F}
    {PreEnv PostEnv : StatesRecvGhost F → List AllocEvent → Prop}
    {ext : String → Option (State → State)}
    (hC : DefsPlacedBudget.StatesRecvPlacedContractsOfEnv M A lim F K envs ext)
    (st : Chunked.SendEk.Ct1Received spqrPolyApi (spqrAuthApi F))
    (msg : Message spqrPolyApi)
    (hPre_ct2 : ∀ (outA selfA msgA fsp : BitVec 64) (st_cost : M.σ) chunk outSt,
      msg.epoch = st.uc.epoch →
      msg.payload = .ct2 chunk →
      st.recv_ct2_chunk st.uc.epoch chunk = .ok outSt →
      FitsEnv M lim st_cost (PreEnv ⟨outA, selfA, msgA, .ct1Received st, msg⟩) →
      FitsEnv M lim st_cost
        (envs.ct1ReceivedRecvCt2Pre ⟨fsp + 976#64, fsp + 1856#64, msgA + 10#64,
          st, chunk, outSt⟩))
    (hPost_gt : ∀ outA selfA msgA, msg.epoch > st.uc.epoch →
      ∀ evs, FreeOnlyEvs evs → PostEnv ⟨outA, selfA, msgA, .ct1Received st, msg⟩ evs)
    (hPost_lt : ∀ outA selfA msgA, msg.epoch < st.uc.epoch →
      PostEnv ⟨outA, selfA, msgA, .ct1Received st, msg⟩ [])
    (hPost_ct2 : ∀ (outA selfA msgA fsp : BitVec 64) chunk outSt evs,
      msg.epoch = st.uc.epoch →
      msg.payload = .ct2 chunk →
      st.recv_ct2_chunk st.uc.epoch chunk = .ok outSt →
      envs.ct1ReceivedRecvCt2Post ⟨fsp + 976#64, fsp + 1856#64, msgA + 10#64,
        st, chunk, outSt⟩ evs →
      PostEnv ⟨outA, selfA, msgA, .ct1Received st, msg⟩ evs)
    (hPost_other : ∀ outA selfA msgA, msg.epoch = st.uc.epoch →
      (∀ c, msg.payload ≠ .ct2 c) →
      PostEnv ⟨outA, selfA, msgA, .ct1Received st, msg⟩ []) :
    subroutine_ok (lsProg_332 (Rust.withPanics ext))
      (lsmpl.base 332)
      (withLsCodeRoLoaded lsmpl
        (DefsPlacedBudget.statesRecvVariantPlacedSpecOfPrePostEnv M A lim F K (.ct1Received st) msg PreEnv PostEnv)) :=
  Leaves.subroutine_ok_withLsCodeRoLoaded_of_withLsCodeLoaded
    (states_recv_ct1Received_placed_ok_ext_ofPrePostEnv
      hC st msg hPre_ct2 hPost_gt hPost_lt hPost_ct2 hPost_other)

theorem states_recv_ct1Received_cro_placed_ok_ext [LibsignalPlacement]
    (M : AllocCostModel) (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (F : ShaCompress) (K : MlKem)
    (ext : String → Option (State → State))
    (hC : DefsPlacedBudget.StatesRecvPlacedContracts M A lim F K ext)
    (st : Chunked.SendEk.Ct1Received spqrPolyApi (spqrAuthApi F))
    (msg : Message spqrPolyApi) :
    subroutine_ok (lsProg_332 (Rust.withPanics ext))
      (lsmpl.base 332)
      (withLsCodeRoLoaded lsmpl
        (DefsPlacedBudget.statesRecvVariantPlacedSpec M A lim F K (.ct1Received st) msg)) :=
  Leaves.subroutine_ok_withLsCodeRoLoaded_of_withLsCodeLoaded
    (states_recv_ct1Received_placed_ok_ext M A lim F K ext hC st msg)

end LibsignalBinary.Proofs.SpqrV1.States.Recv.ArmCt1Received2PlacedBudget
