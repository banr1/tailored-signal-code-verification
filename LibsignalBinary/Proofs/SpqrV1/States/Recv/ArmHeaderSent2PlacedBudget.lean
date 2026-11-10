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
public import LibsignalBinary.Proofs.SpqrV1.States.Leaves.Batch2DefsPlacedBudget
public import LibsignalBinary.Proofs.SpqrV1.States.Leaves.DefsPlacedBudget
public import LibsignalBinary.Proofs.SpqrV1.States.Recv.ArmHeaderSent1PlacedBudget
public import LibsignalBinary.Proofs.SpqrV1.States.Recv.ArmHeaderSent2PlacedBudgetAux
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
import LibsignalBinary.Proofs.SpqrV1.States.Recv.DropChunkedClPlacedBudgetAux
import LibsignalBinary.Proofs.SpqrV1.States.Recv.SendEkCommonPlaced
import LibsignalBinary.Proofs.TripleRatchet.Getters.GettersCodeSym
import ProofLib.SepLogic.WPp
meta import LibsignalBinary.Proofs.Common.SharedHelpers -- shake: keep
meta import LibsignalBinary.Proofs.Placed.BudgetVmSteps -- shake: keep

/-!
# `<States>::recv` (Block `332`) — `.headerSent` Arm, Part 2 (Budget-Threaded)

Budget-threaded `eq_ct1` branch (`headerSent_arm_eq_ct1_placed` via Block `337`), complete
relocatable `.headerSent` arm, and top-level `subroutine_ok` contracts
`states_recv_headerSent_{placed_ok_ext_ofPrePostEnv,exact_placed_ok_ext,env_placed_ok_ext}`.
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 400000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

namespace LibsignalBinary.Proofs.SpqrV1.States.Recv.ArmHeaderSent2PlacedBudget

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
  RustCliAllocBudget SeqEnv VmPreserved rustCliDeallocBudgetSpec
)
open LibsignalBinary.Heap.SpecBudget (withVmPreserved)
open LibsignalBinary.Proofs.SpqrV1.States.Leaves.Batch2DefsPlacedBudget (
  HeaderSentRecvCt1ChunkEnv HeaderSentRecvCt1ChunkPostEnv HeaderSentRecvCt1ChunkPreEnv
  headerSentRecvCt1ChunkPlacedSpec headerSentRecvCt1ChunkPlacedSpecOfEnv
  headerSentRecvCt1ChunkPlacedSpecOfPrePostEnv
)
open LibsignalBinary.Proofs.SpqrV1.States.Recv.ArmHeaderSent1PlacedBudget (
  headerSent_arm_gt_placed
)
open LibsignalBinary.Proofs.SpqrV1.States.Recv.ArmNoHeaderReceivedStepsPlacedBudgetAux (
  call_memcpy_relocate_cs_stack seq_vm_cont
)
open LibsignalBinary.Proofs.SpqrV1.States.Recv.DefsPlacedBudget (
  StatesRecvCalleeEnvs sepWPp_of_statesRecv_exit_placed_ofPrePostEnv
)
open LibsignalBinary.Proofs.SpqrV1.States.Recv.DispatchPlacedBudget (
  states_recv_dispatch_pool_placed states_recv_prologue_pool_placed
)

export LibsignalBinary.Proofs.SpqrV1.States.Recv.ArmHeaderSent2PlacedBudgetAux (
  HeaderSentArmEnv HeaderSentArmPostEnv HeaderSentArmPreEnv
  headerSentArmPostEnv_nil headerSentArmPreEnv_nil
)
export LibsignalBinary.Proofs.SpqrV1.States.Recv.ArmHeaderSent2PlacedBudgetAux (
  headerSentArmPostEnv_nonempty headerSentArmPreEnv_nonempty
  headerSentArmPreEnv_sub_postEnv seqEnv_pre_sub_assoc
)
export LibsignalBinary.Proofs.SpqrV1.States.Recv.ArmHeaderSent2PlacedBudgetAux (
  call_headerSentRecvCt1Chunk_placed
  headerSent_arm_eq_other_pool_placed headerSent_arm_eq_other_sat_placed
  headerSent_arm_lt_pool_placed headerSent_arm_lt_sat_placed
)
export LibsignalBinary.Proofs.SpqrV1.States.Recv.ArmHeaderSent2PlacedBudgetAux (
  headerSent_post_call_done_56848_sat_placed
  headerSent_post_call_still_56848_sat_placed
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

private theorem seq_vm_lscro [LibsignalPlacement] {ext : String → Option (State → State)}
    {mid tgt : BitVec 64} {s : State} {P P_mid : SepProp} {Q : State → Prop}
    {post : State → SepProp → Prop}
    (hcro : LibsignalCodeRoLoaded lsmpl s.mem)
    (h1 : SepWP (lsProg_332 (Rust.withPanics ext)) mid s P
      (fun sm Pm => VmPreserved s sm ∧ (Pm ⊢ P_mid) ∧ Q sm))
    (h2 : ∀ sm : State, sm.pc = mid → sm.status = .Running →
      LibsignalCodeRoLoaded lsmpl sm.mem → VmPreserved s sm → Q sm →
      SepWP (lsProg_332 (Rust.withPanics ext)) tgt sm P_mid post) :
    SepWP (lsProg_332 (Rust.withPanics ext)) tgt s P post :=
  sepWP_seq_lscro hcro
    (SepWP.mono h1 fun sm _ hpc hrun ⟨hvm, hPm, hQ⟩ hcrom =>
      SepWP.weaken_pre hPm (h2 sm hpc hrun hcrom hvm hQ))

private theorem sepWPp_seq_vm_lscro [LibsignalPlacement] {ext : String → Option (State → State)}
    {mid target : BitVec 64} {s : State} {P : SepProp} {P_mid : State → SepProp}
    {Q : State → Prop} {post onPanic : State → SepProp → Prop}
    (hcro : LibsignalCodeRoLoaded lsmpl s.mem)
    (h1 : SepWP (lsProg_332 (Rust.withPanics ext)) mid s P
      (fun sm Pm => VmPreserved s sm ∧ (Pm ⊢ P_mid sm) ∧ Q sm))
    (h2 : ∀ sm : State, sm.pc = mid → sm.status = .Running → VmPreserved s sm → Q sm →
      LibsignalCodeRoLoaded lsmpl sm.mem →
      SepWPp (lsProg_332 (Rust.withPanics ext)) target sm (P_mid sm) post onPanic) :
    SepWPp (lsProg_332 (Rust.withPanics ext)) target s P post onPanic :=
  SepWPp.of_sepWP (sepWP_seq_lscro hcro
    (SepWP.mono h1 fun sm _ hpc hrun ⟨hvm, hPm, hQ⟩ hcro' =>
      SepWP.done hpc hrun (SepWPp.weaken_pre hPm (h2 sm hpc hrun hvm hQ hcro'))))

/-! ## 1. Budget-Threaded `msg.epoch = st.uc.epoch ∧ msg.payload = .ct1 chunk` Path (`+780 -> s0.x30`) -/

set_option maxHeartbeats 1200000 in
/-- Relocatable budget-threaded `.headerSent` arm when `msg.epoch = st.uc.epoch` and
    `msg.payload = .ct1 chunk` (`+780 -> s0.x30`, Block `332`). -/
theorem headerSent_arm_eq_ct1_placed [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {F : ShaCompress} {K : MlKem}
    {CalleePre CalleePost : HeaderSentRecvCt1ChunkGhost F → List AllocEvent → Prop}
    {ext : String → Option (State → State)}
    (hcall : subroutine_ok (lsProg_332 (Rust.withPanics ext))
      (lsmpl.base 337)
      (withLsCodeRoLoaded lsmpl
        (headerSentRecvCt1ChunkPlacedSpecOfPrePostEnv M A lim F CalleePre CalleePost)))
    (hmemcpy_sat : HookSat (Rust.withPanics ext) spqrMemcpySym (withVmPreserved sessionMemcpySpec))
    (st_cost : M.σ)
    (s0 s : State) (outA selfA msgA : BitVec 64)
    (st : Chunked.SendEk.HeaderSent spqrPolyApi (spqrAuthApi F))
    (msg : Message spqrPolyApi) (chunk : Chunk)
    (P_rest : SepProp)
    (hcro : LibsignalCodeRoLoaded lsmpl s.mem)
    (hsort : PolyDecoderStrictSorted st.receiving_ct1)
    (heq : msg.epoch = st.uc.epoch)
    (hpay : msg.payload = .ct1 chunk)
    (hfit : ∀ outRes,
      st.recv_ct1_chunk st.uc.epoch chunk = .ok outRes →
      FitsEnv M lim st_cost
        (CalleePre ⟨(s0.sp - 4240#64) + 976#64, (s0.sp - 4240#64) + 1856#64, msgA + 10#64,
          st, chunk, outRes⟩))
    (hpc : s.pc = lsmpl.base 332 + 780#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = s0.sp - 4240#64)
    (hsp_align : s0.spAligned = true)
    (hx1 : s.readReg64 .x1 = selfA)
    (hx19 : s.readReg64 .x19 = outA)
    (hx24 : s.readReg64 .x24 = msgA)
    (htr : TraceCalleeSaved s s0) :
    SepWP (lsProg_332 (Rust.withPanics ext))
      (s0.readReg64 .x30) s
      (P_rest ∗
        memRegion outA v1RecvSize ∗
        chunkedStatesAt A.repAlloc selfA (.headerSent st) ∗
        messageAt spqrPolyApi msgA msg ∗
        (lsLogFilterAddr ↦₆₄ 0#64) ∗
        tokenInitPlacedAt ∗ reduceTablePlacedAt ∗
        A.pool lim st_cost s ∗
        stackAt (s0.sp - 4240#64) statesRecvCalleeStackX ∗
        memRegion (s0.sp - 4240#64) 4144 ∗
        statesRecvSavedCells s0)
      (fun sf Pf =>
        ∃ evs : List AllocEvent,
          (∃ outRes,
            st.recv_ct1_chunk st.uc.epoch chunk = .ok outRes ∧
            CalleePost ⟨(s0.sp - 4240#64) + 976#64, (s0.sp - 4240#64) + 1856#64, msgA + 10#64,
              st, chunk, outRes⟩ evs) ∧
          (Pf ⊢
            P_rest ∗
            resultV1RecvAt A.repAlloc (F := F) outA (States.recv K (.headerSent st) msg) ∗
            memRegion selfA chunkedStatesSize ∗
            messageAt spqrPolyApi msgA msg ∗
            (lsLogFilterAddr ↦₆₄ 0#64) ∗
            tokenInitPlacedAt ∗ reduceTablePlacedAt ∗
            A.pool lim (M.stepEvents evs st_cost) sf ∗
            stackAt s0.sp statesRecvStackX) ∧
          sf.sp = s0.sp ∧
          CalleeSavedPreserved s0 sf ∧
          sf.trace = s0.trace) := by
  have hcond_eq := epoch_cmp_ct1r_eq_of_eq st.uc.epoch
  have hmemcpy : subroutine_ok (lsProg_332 (Rust.withPanics ext))
      (lsρ memcpyName) (withVmPreserved (sessionMemcpySpec 4096)) := spqr_hook_ok_of_mem hmemcpy_sat
  have hpost_done := @headerSent_post_call_done_56848_sat_placed _ A.repAlloc F ext hmemcpy_sat s0
  have hpost_still := @headerSent_post_call_still_56848_sat_placed _ A.repAlloc F ext hmemcpy_sat s0
  have hsp_align' : (s0.sp &&& 15#64 == 0#64) = true := hsp_align
  have hfsp_align : ((s0.sp - 4240#64) &&& 15#64 == 0#64) = true :=
    spAligned_sub s0.sp 4240#64 hsp_align (by decide)
  dsimp only [chunkedStatesAt]
  refine SepWP.fold (chunkedHeaderSentAt_pts_length A.repAlloc (selfA + 8#64) st) (by sep_focus) ?_
  rw [sepConj_assoc]
  refine SepWP.pure_elim fun hlen_pts => ?_
  obtain ⟨outRes, hrecv, _⟩ := headerSent_recv_ct1_chunk_eq_ok st chunk hlen_pts hsort
  refine SepWP.fold (memRegion_4144_entails_sendEkFrame (s0.sp - 4240#64)) (by sep_focus) ?_
  wp_pull_exists; rename_i sp
  refine SepWP.fold (chunkedHeaderSentAt_extract63_376 A.repAlloc (selfA + 8#64) st) (by sep_focus) ?_
  wp_pull_exists; rename_i w tailBytes
  refine SepWP.pure_elim fun ⟨hw62, _⟩ => ?_
  let sp1 : SendEkSpills :=
    { b0 := ⟨w.b5.w2, w.b3.w5, w.b3.w1, sp.b0.w3, w.b3.w2, w.b4.w1, w.b4.w0, sp.b0.w7, w.b3.w4, w.b3.w3⟩
      b1 := ⟨w.b5.w7, w.b5.w5, w.b3.w9, w.b3.w6, w.b5.w3, w.b3.w7, sp.b1.w6, w.b5.w9, sp.b1.w8, sp.b1.w9⟩
      b2 := ⟨w.b4.w7, w.b5.w1, w.b4.w9, w.b4.w3, w.b4.w5, sp.b2.w5, w.b4.w8, sp.b2.w7, sp.b2.w8, w.b4.w2⟩
      b3 := ⟨sp.b3.w0, w.w62, sp.b3.w2, sp.b3.w3, sp.b3.w4, sp.b3.w5, w.b1.w3, w.b2.w5, sp.b3.w8, sp.b3.w9⟩
      b4 := ⟨w.b2.w6, w.b1.w2, sp.b4.w2, w.b1.w0, sp.b4.w4, sp.b4.w5, w.b0.w4, sp.b4.w7, sp.b4.w8, w.b2.w3⟩
      b5 := ⟨sp.b5.w0, w.b4.w4, w.b1.w4, w.b0.w8, sp.b5.w4, w.b5.w0, sp.b5.w6, w.b2.w4, w.b4.w6, sp.b5.w9⟩
      w60 := w.b5.w6, w61 := sp.w61, w62 := w.b0.w6
      q200 := sp.q200, q210 := sp.q210, q220 := sp.q220, w230 := sp.w230, q3c0 := sp.q3c0 }
  refine seq_vm_lscro hcro (mid := lsmpl.base 337)
    (P_mid :=
      P_rest ∗
      memRegion selfA chunkedStatesSize ∗
      ((msgA ↦₆₄ msg.epoch) ∗ ((msgA + 8#64) ↦₈ 5#8) ∗ memRegion (msgA + 9#64) 1 ∗
        chunkAt (msgA + 10#64) chunk ∗ memRegion (msgA + 44#64) 4) ∗
      (lsLogFilterAddr ↦₆₄ 0#64) ∗
      tokenInitPlacedAt ∗ reduceTablePlacedAt ∗
      A.pool lim st_cost s ∗
      memRegion outA v1RecvSize ∗
      stackAt (s0.sp - 4240#64) statesRecvCalleeStackX ∗
      memRegion ((s0.sp - 4240#64) + 576#64) 376 ∗
      memRegion ((s0.sp - 4240#64) + 976#64) 880 ∗
      chunkedHeaderSentAt A.repAlloc ((s0.sp - 4240#64) + 1856#64) st ∗
      sendEkUnusedAt (s0.sp - 4240#64) ∗
      sendEkSpillsAt (s0.sp - 4240#64) sp1 ∗
      statesRecvSavedCells s0)
    (Q := fun sm =>
      sm.sp = s0.sp - 4240#64 ∧
      sm.readReg64 .lr = lsmpl.base 332 + 5108#64 ∧
      sm.readReg64 .x0 = (s0.sp - 4240#64) + 976#64 ∧
      sm.readReg64 .x1 = (s0.sp - 4240#64) + 1856#64 ∧
      sm.readReg64 .x2 = st.uc.epoch ∧
      sm.readReg64 .x3 = msgA + 10#64 ∧
      sm.readReg64 .x19 = outA ∧
      sm.readReg64 .x21 = (s0.sp - 4240#64) + 976#64 ∧
      TraceCalleeSaved sm s0)
    ?_ ?_
  · rw [lsmpl_base_332_eq] at hpc ⊢
    dsimp only [lsProg_332, lsρ, memcpyName, messageAt, BitVec.ofNat_eq_ofNat] at hpc hmemcpy ⊢
    refine seq_vm_cont (mid := lsmpl.ρ "memcpy") ?_
    by_vm_steps_nest (
      generalize hsp0 : s0.sp = sp0 at hsp hsp_align' hfsp_align ⊢
      wp_conv_pre =>
        dsimp only [sendEkSpillsAt, words63At, words10At]
        rw [hw62, heq, hpay, messagePayloadAt_ct1 msgA chunk]
        simp only [pointsTo128_eq_pair64_recv, BitVec.add_assoc, arm64_norm]
      wp_steps 120
      subst hsp0
      refine SepWP.done (by simp only [wp_norm, arm64_norm])
        (by simp only [wp_norm, arm64_norm]; assumption)
        ⟨by simp only [wp_norm, arm64_norm], fun hvm1 => ?_⟩
      have hfold_pre_memcpy :
          (words63At (selfA + 8#64) w ∗
           ((selfA + 8#64 + 504#64) ↦ₛ tailBytes) ∗
           relocatedHeap (fun dst => chunkedHeaderSentAt A.repAlloc dst st) (wordsBytes (words63List w) ++ tailBytes)) ∗
          sendEkSpillsAt (s0.sp - 4240#64) sp1 ⊢
            chunkedHeaderSentAt A.repAlloc (selfA + 8#64) st ∗
            sendEkSpillsAt (s0.sp - 4240#64) sp1 :=
        sepConj_mono_left (recompose63_376 (selfA + 8#64) w tailBytes)
      refine SepWP.fold
        (F := P_rest ∗ memRegion outA v1RecvSize ∗ (selfA ↦₆₄ 4#64) ∗ memRegion (selfA + 888#64) 40 ∗
          ((msgA ↦₆₄ msg.epoch) ∗ ((msgA + 8#64) ↦₈ 5#8) ∗ memRegion (msgA + 9#64) 1 ∗
            chunkAt (msgA + 10#64) chunk ∗ memRegion (msgA + 44#64) 4) ∗
          (lsLogFilterAddr ↦₆₄ 0#64) ∗ tokenInitPlacedAt ∗ reduceTablePlacedAt ∗ A.pool lim st_cost s ∗
          stackAt (s0.sp - 4240#64) statesRecvCalleeStackX ∗
          memRegion ((s0.sp - 4240#64) + 576#64) 376 ∗ memRegion ((s0.sp - 4240#64) + 976#64) 880 ∗
          memRegion ((s0.sp - 4240#64) + 1856#64) 880 ∗ sendEkUnusedAt (s0.sp - 4240#64) ∗
          statesRecvSavedCells s0)
        hfold_pre_memcpy
        (by
          dsimp only [sendEkSpillsAt, words63At, words10At, sp1]
          rw [hw62, heq]
          simp only [pointsTo128_eq_pair64_recv, BitVec.add_assoc, arm64_norm]
          sep_ac_rfl) ?_
      rw [stackAt_statesRecvCallee_eq_allocHook (s0.sp - 4240#64)]
      dsimp only [allocHookStack]
      refine call_memcpy_relocate_cs_stack (ret_pc := (blkPl_332).base + 5084#64)
        hmemcpy (Recv.Relocatable.of_chunkedHeaderSentAt A.repAlloc st)
        ((s0.sp - 4240#64) + 1856#64) (selfA + 8#64)
        (by simp only [wp_norm, arm64_norm])
        (by simp only [wp_norm, arm64_norm]; assumption) (by simp only [wp_norm, arm64_norm, hsp]) hfsp_align
        (by simp only [Reg.lr, wp_norm, arm64_norm])
        ⟨by simp only [wp_norm, arm64_norm]; exact htr.1,
         by simp only [wp_norm, arm64_norm]; exact htr.2⟩
        (by simp only [Reg.x0, wp_norm, arm64_norm, hsp])
        (by simp only [Reg.x1, wp_norm, arm64_norm, hx1])
        (by simp only [Reg.x2, wp_norm, arm64_norm])
        (by sep_focus) ?_
      intro sf1 hpc1 hrun1 hsp1 hvm_mc hcs1 htr1
      have hx19_1 : sf1.readReg64 .x19 = outA :=
        hcs1.1.trans (by simp only [Reg.x19, wp_norm, arm64_norm, hx19])
      have hx24_1 : sf1.readReg64 .x24 = msgA :=
        hcs1.2.2.2.2.2.1.trans (by simp only [Reg.x24, wp_norm, arm64_norm, hx24])
      have hx25_1 : sf1.readReg64 .x25 = st.uc.epoch :=
        hcs1.2.2.2.2.2.2.1.trans (by simp only [Reg.x25, wp_norm, arm64_norm])
      have hfold_callee :
          memRegion (s0.sp - 4240#64 - 19552#64) 15456 ∗ stackAt (s0.sp - 4240#64) 4096 ⊢
            stackAt (s0.sp - 4240#64) statesRecvCalleeStackX :=
        Entails.of_eq (stackAt_statesRecvCallee_eq_allocHook (s0.sp - 4240#64)).symm
      refine SepWP.focus_weaken hfold_callee (by sep_focus) ?_
      have hfold_self :
          (selfA ↦₆₄ 4#64) ∗ memRegion (selfA + 8#64) 880 ∗ memRegion (selfA + 888#64) 40 ⊢
            memRegion selfA chunkedStatesSize :=
        self_880_40_entails_memRegion_928 selfA 4#64
      refine SepWP.focus_weaken hfold_self (by sep_focus) ?_
      rw [← stackAt_statesRecvCallee_eq_allocHook (s0.sp - 4240#64)]
      refine SepWP.mono
        (post := fun sm Pm =>
          VmPreserved sf1 sm ∧
          (Pm ⊢
            P_rest ∗
            memRegion selfA chunkedStatesSize ∗
            ((msgA ↦₆₄ msg.epoch) ∗ ((msgA + 8#64) ↦₈ 5#8) ∗ memRegion (msgA + 9#64) 1 ∗
              chunkAt (msgA + 10#64) chunk ∗ memRegion (msgA + 44#64) 4) ∗
            (lsLogFilterAddr ↦₆₄ 0#64) ∗
            tokenInitPlacedAt ∗ reduceTablePlacedAt ∗
            A.pool lim st_cost s ∗
            memRegion outA v1RecvSize ∗
            stackAt (s0.sp - 4240#64) statesRecvCalleeStackX ∗
            memRegion ((s0.sp - 4240#64) + 576#64) 376 ∗
            memRegion ((s0.sp - 4240#64) + 976#64) 880 ∗
            chunkedHeaderSentAt A.repAlloc ((s0.sp - 4240#64) + 1856#64) st ∗
            sendEkUnusedAt (s0.sp - 4240#64) ∗
            sendEkSpillsAt (s0.sp - 4240#64) sp1 ∗
            statesRecvSavedCells s0) ∧
          sm.sp = s0.sp - 4240#64 ∧
          sm.readReg64 .lr = (blkPl_332).base + 5108#64 ∧
          sm.readReg64 .x0 = (s0.sp - 4240#64) + 976#64 ∧
          sm.readReg64 .x1 = (s0.sp - 4240#64) + 1856#64 ∧
          sm.readReg64 .x2 = st.uc.epoch ∧
          sm.readReg64 .x3 = msgA + 10#64 ∧
          sm.readReg64 .x19 = outA ∧
          sm.readReg64 .x21 = (s0.sp - 4240#64) + 976#64 ∧
          TraceCalleeSaved sm s0)
        ?_
        (fun _ _ _ _ ⟨hvm2, hPm, hq⟩ => ⟨hvm1.trans (hvm_mc.trans hvm2), hPm, hq⟩)
      by_vm_steps_nest (
        generalize hsp0 : s0.sp = sp0 at hsp1 hfsp_align ⊢
        wp_steps 10
        subst hsp0
        refine DropChunkedClPlacedBudgetAux.align_pre_vm (by simp only [wp_norm, arm64_norm]; sep_ac_rfl) ?_
        simp only [TraceCalleeSaved, Reg.lr, Reg.x0, Reg.x1, Reg.x2, Reg.x3, Reg.x19, Reg.x21, Reg.x30,
          hsp1, hx19_1, hx24_1, hx25_1, htr1.1, htr1.2, wp_norm, arm64_norm]
        wp_done
      )
    )
  · intro sm hpcm hrunm hcro_m hvm_m ⟨hsp_m, hlr_m, hx0_m, hx1_m, hx2_m, hx3_m, hx19_m, hx21_m, htr_m⟩
    rw [← A.pool_transport lim st_cost s sm hvm_m]
    refine SepWP.focus_weaken
      (Entails.of_eq (stackAt_statesRecvCallee_split_headerSentRecvCt1 (s0.sp - 4240#64)))
      (by sep_focus) ?_
    refine call_headerSentRecvCt1Chunk_placed hcall
      ((s0.sp - 4240#64) + 976#64) ((s0.sp - 4240#64) + 1856#64) (msgA + 10#64)
      st chunk outRes st_cost hsort hrecv (hfit outRes hrecv)
      (s0 := s0) (sp_call := s0.sp - 4240#64) (ret_pc := lsmpl.base 332 + 5108#64)
      (Frame :=
        P_rest ∗ memRegion selfA chunkedStatesSize ∗
        ((msgA ↦₆₄ msg.epoch) ∗ ((msgA + 8#64) ↦₈ 5#8) ∗ memRegion (msgA + 9#64) 1 ∗
          memRegion (msgA + 44#64) 4) ∗
        (lsLogFilterAddr ↦₆₄ 0#64) ∗ memRegion outA v1RecvSize ∗
        memRegion ((s0.sp - 4240#64) - 19552#64) 928 ∗
        memRegion ((s0.sp - 4240#64) + 576#64) 376 ∗
        sendEkUnusedAt (s0.sp - 4240#64) ∗ sendEkSpillsAt (s0.sp - 4240#64) sp1 ∗
        statesRecvSavedCells s0)
      hcro_m hpcm hrunm hsp_m hfsp_align hlr_m htr_m hx0_m hx1_m hx2_m hx3_m
      (by
        dsimp only [chunkedHeaderSentSize, statesRecvCalleeStackX, headerSentRecvCt1ChunkStack,
          polyDecoderDecodedMessageStack, extHookStack, BitVec.ofNat_eq_ofNat]
        simp only [arm64_norm]
        sep_ac_rfl)
      ?_
    intro evs hevs sf2 hpc2 hrun2 hsp2 hcs2 htr2
    refine SepWP.focus_weaken
      (Entails.of_eq (stackAt_statesRecvCallee_split_headerSentRecvCt1 (s0.sp - 4240#64)).symm)
      (by sep_focus) ?_
    have hmsg_eq :
        ((msgA ↦₆₄ msg.epoch) ∗ ((msgA + 8#64) ↦₈ 5#8) ∗ memRegion (msgA + 9#64) 1 ∗
         chunkAt (msgA + 10#64) chunk ∗ memRegion (msgA + 44#64) 4) =
        messageAt spqrPolyApi msgA msg := by
      dsimp only [messageAt]
      rw [hpay, messagePayloadAt_ct1 msgA chunk]
    have hx19_2 : sf2.readReg64 .x19 = outA := hcs2.1.trans hx19_m
    have hx21_2 : sf2.readReg64 .x21 = (s0.sp - 4240#64) + 976#64 := hcs2.2.2.1.trans hx21_m
    cases outRes with
    | done outSt =>
      have hmodel := states_recv_headerSent_eq_ct1_done K st msg chunk outSt heq hpay hrecv
      refine SepWP.weaken_pre (Entails.of_eq ?_)
        (SepWP.mono
          (hpost_done sf2 outA outSt sp1
            (P_rest ∗ memRegion selfA chunkedStatesSize ∗ messageAt spqrPolyApi msgA msg ∗
             tokenInitPlacedAt ∗ reduceTablePlacedAt ∗ A.pool lim (M.stepEvents evs st_cost) sf2)
            hpc2 hrun2 hsp2 hsp_align hx19_2 hx21_2 htr2)
          (fun sf Pf _ _ ⟨hvm_post, hPf, hsp_sf, hcs_sf, htr_sf⟩ =>
            ⟨evs, ⟨.done outSt, hrecv, hevs⟩,
             by
               rw [hmodel]
               exact Entails.trans hPf (Entails.of_eq (by
                 rw [← A.pool_transport lim (M.stepEvents evs st_cost) sf2 sf hvm_post]
                 sep_ac_rfl)),
             hsp_sf, hcs_sf, htr_sf⟩))
      rw [← hmsg_eq]
      dsimp only [chunkedHeaderSentSize]
      simp only [arm64_norm]
      sep_ac_rfl
    | stillReceiving outSt =>
      have hmodel := states_recv_headerSent_eq_ct1_still K st msg chunk outSt heq hpay hrecv
      refine SepWP.weaken_pre (Entails.of_eq ?_)
        (SepWP.mono
          (hpost_still sf2 outA outSt sp1
            (P_rest ∗ memRegion selfA chunkedStatesSize ∗ messageAt spqrPolyApi msgA msg ∗
             (lsLogFilterAddr ↦₆₄ 0#64) ∗ tokenInitPlacedAt ∗ reduceTablePlacedAt ∗
             A.pool lim (M.stepEvents evs st_cost) sf2)
            hpc2 hrun2 hsp2 hsp_align hx19_2 hx21_2 htr2)
          (fun sf Pf _ _ ⟨hvm_post, hPf, hsp_sf, hcs_sf, htr_sf⟩ =>
            ⟨evs, ⟨.stillReceiving outSt, hrecv, hevs⟩,
             by
               rw [hmodel]
               exact Entails.trans hPf (Entails.of_eq (by
                 rw [← A.pool_transport lim (M.stepEvents evs st_cost) sf2 sf hvm_post]
                 sep_ac_rfl)),
             hsp_sf, hcs_sf, htr_sf⟩))
      rw [← hmsg_eq]
      dsimp only [chunkedHeaderSentSize]
      simp only [arm64_norm]
      sep_ac_rfl

/-! ## 2. Complete Relocatable `.headerSent` Arm & Top-Level `subroutine_ok` Contracts -/

/-- Two-envelope (`PreEnv` / `PostEnv`) relocatable `.headerSent` arm of `<States>::recv`
    (`+780 -> s0.x30`, Block `332`). -/
theorem states_recv_arm_headerSent_placed_ofPrePostEnv [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {F : ShaCompress} {K : MlKem}
    {CalleePre CalleePost : HeaderSentRecvCt1ChunkGhost F → List AllocEvent → Prop}
    {PreEnv PostEnv : StatesRecvGhost F → List AllocEvent → Prop}
    {ext : String → Option (State → State)}
    (hdealloc : HookSat (Rust.withPanics ext) spqrDeallocSym (rustCliDeallocBudgetSpec M A lim))
    (hcall : subroutine_ok (lsProg_332 (Rust.withPanics ext))
      (lsmpl.base 337)
      (withLsCodeRoLoaded lsmpl
        (headerSentRecvCt1ChunkPlacedSpecOfPrePostEnv M A lim F CalleePre CalleePost)))
    (hmemcpy_sat : HookSat (Rust.withPanics ext) spqrMemcpySym (withVmPreserved sessionMemcpySpec))
    (st_cost : M.σ)
    (s0 s : State) (outA selfA msgA : BitVec 64)
    (st : Chunked.SendEk.HeaderSent spqrPolyApi (spqrAuthApi F))
    (msg : Message spqrPolyApi)
    (R : SepProp)
    (hFit : FitsEnv M lim st_cost (PreEnv ⟨outA, selfA, msgA, .headerSent st, msg⟩))
    (hPre_ct1 : ∀ chunk outRes,
      msg.epoch = st.uc.epoch →
      msg.payload = .ct1 chunk →
      st.recv_ct1_chunk st.uc.epoch chunk = .ok outRes →
      FitsEnv M lim st_cost (PreEnv ⟨outA, selfA, msgA, .headerSent st, msg⟩) →
      FitsEnv M lim st_cost
        (CalleePre ⟨(s0.sp - 4240#64) + 976#64, (s0.sp - 4240#64) + 1856#64, msgA + 10#64,
          st, chunk, outRes⟩))
    (hPost_gt : msg.epoch > st.uc.epoch →
      ∀ evs, FreeOnlyEvs evs → PostEnv ⟨outA, selfA, msgA, .headerSent st, msg⟩ evs)
    (hPost_lt : msg.epoch < st.uc.epoch →
      PostEnv ⟨outA, selfA, msgA, .headerSent st, msg⟩ [])
    (hPost_ct1 : ∀ chunk outRes evs,
      msg.epoch = st.uc.epoch →
      msg.payload = .ct1 chunk →
      st.recv_ct1_chunk st.uc.epoch chunk = .ok outRes →
      CalleePost ⟨(s0.sp - 4240#64) + 976#64, (s0.sp - 4240#64) + 1856#64, msgA + 10#64,
        st, chunk, outRes⟩ evs →
      PostEnv ⟨outA, selfA, msgA, .headerSent st, msg⟩ evs)
    (hPost_other : msg.epoch = st.uc.epoch →
      (∀ c, msg.payload ≠ .ct1 c) →
      PostEnv ⟨outA, selfA, msgA, .headerSent st, msg⟩ [])
    (hcro : LibsignalCodeRoLoaded lsmpl s.mem)
    (hinv : statesRecvPreInv (.headerSent st))
    (hpc : s.pc = lsmpl.base 332 + 780#64)
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
    SepWPp (lsProg_332 (Rust.withPanics ext)) (s0.readReg64 Reg.lr) s
      (memRegion outA v1RecvSize ∗
        chunkedStatesAt A.repAlloc selfA (.headerSent st) ∗
        messageAt spqrPolyApi msgA msg ∗
        statesRecvRoPlacedAt ∗
        A.pool lim st_cost s ∗
        stackAt (s0.sp - 4240#64) statesRecvCalleeStackX ∗
        memRegion (s0.sp - 4240#64) 4144 ∗
        statesRecvSavedCells s0)
      (fun sf P_f =>
        (sf.mem ⊨ P_f ∗ R →
          sf.mem ⊨
            (DefsPlacedBudget.statesRecvVariantPlacedSpecOfPrePostEnv M A lim F K (.headerSent st) msg PreEnv PostEnv).post
              ((outA, selfA, msgA), st_cost) s0 sf ∗ R) ∧
        sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf)
      (fun sf P_f =>
        (sf.mem ⊨ P_f ∗ R) →
          (sf.mem ⊨
            (DefsPlacedBudget.statesRecvVariantPlacedSpecOfPrePostEnv M A lim F K (.headerSent st) msg PreEnv PostEnv).onPanic
              ((outA, selfA, msgA), st_cost) s0 sf ∗ R)) := by
  by_cases hgt : msg.epoch > st.uc.epoch
  · refine sepWPp_of_statesRecv_exit_placed_ofPrePostEnv s0 s outA selfA msgA (.headerSent st) msg
      st_cost _ R ?_
    rw [states_recv_headerSent_gt K st msg hgt]
    refine SepWP.weaken_pre
      (P' := statesRecvRoPlacedAt ∗ memRegion outA v1RecvSize ∗
        chunkedStatesAt A.repAlloc selfA (.headerSent st) ∗
        messageAt spqrPolyApi msgA msg ∗ A.pool lim st_cost s ∗
        stackAt (s0.sp - 4240#64) statesRecvCalleeStackX ∗ memRegion (s0.sp - 4240#64) 4144 ∗
        statesRecvSavedCells s0)
      (Entails.of_eq (by sep_ac_rfl))
      (SepWP.mono
        (ArmHeaderSent1PlacedBudget.headerSent_arm_gt_placed hdealloc st_cost s0 s outA selfA msgA
          st msg statesRecvRoPlacedAt hgt hcro.1 hpc hrun hsp hsp_align hx1 hx19 hx24 htr)
        fun sf Pf _ _ ⟨evs, hevs, hPf, hsp_sf, _, hcs_sf, htr_sf⟩ =>
          ⟨⟨evs, hPost_gt hgt evs hevs, Entails.trans hPf (Entails.of_eq (by sep_ac_rfl))⟩,
           hsp_sf, hcs_sf, htr_sf⟩)
  · by_cases hlt : msg.epoch < st.uc.epoch
    · refine sepWPp_of_statesRecv_exit_placed_ofPrePostEnv s0 s outA selfA msgA (.headerSent st) msg
        st_cost _ R ?_
      rw [states_recv_headerSent_lt K st msg hlt]
      refine SepWP.weaken_pre
        (P' := statesRecvRoPlacedAt ∗ memRegion outA v1RecvSize ∗
          chunkedStatesAt A.repAlloc selfA (.headerSent st) ∗
          messageAt spqrPolyApi msgA msg ∗ A.pool lim st_cost s ∗
          stackAt (s0.sp - 4240#64) statesRecvCalleeStackX ∗ memRegion (s0.sp - 4240#64) 4144 ∗
          statesRecvSavedCells s0)
        (Entails.of_eq (by sep_ac_rfl))
        (SepWP.mono
          (headerSent_arm_lt_pool_placed hmemcpy_sat st_cost s0 s outA selfA msgA st msg
            statesRecvRoPlacedAt hlt hpc hrun hsp hsp_align hx1 hx19 hx24 htr)
          fun sf Pf _ _ ⟨_, hPf, hsp_sf, hcs_sf, htr_sf⟩ =>
            ⟨⟨[], hPost_lt hlt, Entails.trans hPf (Entails.of_eq (by sep_ac_rfl))⟩,
             hsp_sf, hcs_sf, htr_sf⟩)
    · have heq : msg.epoch = st.uc.epoch := by
        have h1 : ¬ (st.uc.epoch < msg.epoch) := hgt
        have h2 : ¬ (msg.epoch < st.uc.epoch) := hlt
        exact BitVec.le_antisymm (BitVec.not_lt.mp h1) (BitVec.not_lt.mp h2)
      cases hpay : msg.payload with
      | ct1 chunk =>
        refine sepWPp_of_statesRecv_exit_placed_ofPrePostEnv s0 s outA selfA msgA (.headerSent st) msg
          st_cost _ R ?_
        refine SepWP.weaken_pre
          (P' := (statesRecvJumpTablePlacedAt ∗ ((lsρ "spqr:.rodata..Lanon.137") ↦ᵣ Authenticator.ctLabel)) ∗
            memRegion outA v1RecvSize ∗
            chunkedStatesAt A.repAlloc selfA (.headerSent st) ∗
            messageAt spqrPolyApi msgA msg ∗
            (lsLogFilterAddr ↦₆₄ 0#64) ∗
            tokenInitPlacedAt ∗ reduceTablePlacedAt ∗
            A.pool lim st_cost s ∗
            stackAt (s0.sp - 4240#64) statesRecvCalleeStackX ∗
            memRegion (s0.sp - 4240#64) 4144 ∗
            statesRecvSavedCells s0)
          (Entails.of_eq (by dsimp only [statesRecvRoPlacedAt, unchunkedSendCt2PlacedRoAt]; sep_ac_rfl))
          (SepWP.mono
            (headerSent_arm_eq_ct1_placed (K := K) hcall hmemcpy_sat st_cost s0 s outA selfA msgA
              st msg chunk
              (statesRecvJumpTablePlacedAt ∗ ((lsρ "spqr:.rodata..Lanon.137") ↦ᵣ Authenticator.ctLabel))
              hcro hinv heq hpay (fun outRes hrecv => hPre_ct1 chunk outRes heq hpay hrecv hFit)
              hpc hrun hsp hsp_align hx1 hx19 hx24 htr)
            fun sf Pf _ _ ⟨evs, ⟨outRes, hrecv, hevs⟩, hPf, hsp_sf, hcs_sf, htr_sf⟩ =>
              ⟨⟨evs, hPost_ct1 chunk outRes evs heq hpay hrecv hevs,
                Entails.trans hPf (Entails.of_eq (by
                  dsimp only [statesRecvRoPlacedAt, unchunkedSendCt2PlacedRoAt]; sep_ac_rfl))⟩,
               hsp_sf, hcs_sf, htr_sf⟩)
      | none | hdr _ | ek _ | ekCt1Ack _ | ct1Ack _ | ct2 _ =>
        have hct1 : ∀ c, msg.payload ≠ .ct1 c := by intro c hc; rw [hpay] at hc; cases hc
        refine sepWPp_of_statesRecv_exit_placed_ofPrePostEnv s0 s outA selfA msgA (.headerSent st) msg
          st_cost _ R ?_
        rw [states_recv_headerSent_eq_other K st msg heq hct1]
        refine SepWP.weaken_pre
          (P' := statesRecvRoPlacedAt ∗ memRegion outA v1RecvSize ∗
            chunkedStatesAt A.repAlloc selfA (.headerSent st) ∗
            messageAt spqrPolyApi msgA msg ∗ A.pool lim st_cost s ∗
            stackAt (s0.sp - 4240#64) statesRecvCalleeStackX ∗ memRegion (s0.sp - 4240#64) 4144 ∗
            statesRecvSavedCells s0)
          (Entails.of_eq (by sep_ac_rfl))
          (SepWP.mono
            (headerSent_arm_eq_other_pool_placed hmemcpy_sat st_cost s0 s outA selfA msgA st msg
              statesRecvRoPlacedAt heq hct1 hpc hrun hsp hsp_align hx1 hx19 hx24 htr)
            fun sf Pf _ _ ⟨_, hPf, hsp_sf, hcs_sf, htr_sf⟩ =>
              ⟨⟨[], hPost_other heq hct1, Entails.trans hPf (Entails.of_eq (by sep_ac_rfl))⟩,
               hsp_sf, hcs_sf, htr_sf⟩)

/-- Exact-envelope (`HeaderSentArmPreEnv` / `HeaderSentArmPostEnv`) relocatable `.headerSent` arm
    of `<States>::recv` (`+780 -> s0.x30`, Block `332`). -/
theorem states_recv_arm_headerSent_exact_placed [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {F : ShaCompress} {K : MlKem}
    {ext : String → Option (State → State)}
    (hdealloc : HookSat (Rust.withPanics ext) spqrDeallocSym (rustCliDeallocBudgetSpec M A lim))
    (hcall : subroutine_ok (lsProg_332 (Rust.withPanics ext))
      (lsmpl.base 337)
      (withLsCodeRoLoaded lsmpl (headerSentRecvCt1ChunkPlacedSpec M A lim F)))
    (hmemcpy_sat : HookSat (Rust.withPanics ext) spqrMemcpySym (withVmPreserved sessionMemcpySpec))
    (st_cost : M.σ)
    (s0 s : State) (outA selfA msgA : BitVec 64)
    (st : Chunked.SendEk.HeaderSent spqrPolyApi (spqrAuthApi F))
    (msg : Message spqrPolyApi)
    (R : SepProp)
    (hFit : FitsEnv M lim st_cost (HeaderSentArmPreEnv st msg))
    (hcro : LibsignalCodeRoLoaded lsmpl s.mem)
    (hinv : statesRecvPreInv (.headerSent st))
    (hpc : s.pc = lsmpl.base 332 + 780#64)
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
    SepWPp (lsProg_332 (Rust.withPanics ext)) (s0.readReg64 Reg.lr) s
      (memRegion outA v1RecvSize ∗
        chunkedStatesAt A.repAlloc selfA (.headerSent st) ∗
        messageAt spqrPolyApi msgA msg ∗
        statesRecvRoPlacedAt ∗
        A.pool lim st_cost s ∗
        stackAt (s0.sp - 4240#64) statesRecvCalleeStackX ∗
        memRegion (s0.sp - 4240#64) 4144 ∗
        statesRecvSavedCells s0)
      (fun sf P_f =>
        (sf.mem ⊨ P_f ∗ R →
          sf.mem ⊨
            (DefsPlacedBudget.statesRecvVariantPlacedSpecOfPrePostEnv M A lim F K (.headerSent st) msg
              (fun _ => HeaderSentArmPreEnv st msg)
              (fun _ => HeaderSentArmPostEnv st msg)).post
              ((outA, selfA, msgA), st_cost) s0 sf ∗ R) ∧
        sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf)
      (fun sf P_f =>
        (sf.mem ⊨ P_f ∗ R) →
          (sf.mem ⊨
            (DefsPlacedBudget.statesRecvVariantPlacedSpecOfPrePostEnv M A lim F K (.headerSent st) msg
              (fun _ => HeaderSentArmPreEnv st msg)
              (fun _ => HeaderSentArmPostEnv st msg)).onPanic
              ((outA, selfA, msgA), st_cost) s0 sf ∗ R)) := by
  refine states_recv_arm_headerSent_placed_ofPrePostEnv
    (PreEnv := fun _ => HeaderSentArmPreEnv st msg)
    (PostEnv := fun _ => HeaderSentArmPostEnv st msg)
    hdealloc hcall hmemcpy_sat st_cost s0 s outA selfA msgA st msg R hFit
    ?_ ?_ (fun _ => headerSentArmPostEnv_nil st msg) ?_
    (fun _ _ => headerSentArmPostEnv_nil st msg)
    hcro hinv hpc hrun hsp hsp_align hx1 hx19 hx24 htr
  · intro chunk outRes heq hpay _ hF
    have hEqEnv : HeaderSentArmPreEnv st msg =
        HeaderSentRecvCt1ChunkPreEnv
          ⟨(s0.sp - 4240#64) + 976#64, (s0.sp - 4240#64) + 1856#64, msgA + 10#64,
            st, chunk, outRes⟩ := by
      funext evs
      unfold HeaderSentArmPreEnv HeaderSentRecvCt1ChunkPreEnv
      have hngt : ¬ (msg.epoch > st.uc.epoch) := by rw [heq]; exact BitVec.lt_irrefl _
      have hnlt : ¬ (msg.epoch < st.uc.epoch) := by rw [heq]; exact BitVec.lt_irrefl _
      simp only [hngt, hnlt, ↓reduceIte, hpay]
    rwa [← hEqEnv]
  · intro hgt evs hevs
    unfold HeaderSentArmPostEnv
    simp only [hgt, ↓reduceIte]
    exact hevs
  · intro chunk outRes evs heq hpay _ hevs
    unfold HeaderSentRecvCt1ChunkPostEnv HeaderSentRecvCt1ChunkPreEnv at hevs
    unfold HeaderSentArmPostEnv
    have hngt : ¬ (msg.epoch > st.uc.epoch) := by rw [heq]; exact BitVec.lt_irrefl _
    have hnlt : ¬ (msg.epoch < st.uc.epoch) := by rw [heq]; exact BitVec.lt_irrefl _
    simp only [hngt, hnlt, ↓reduceIte, hpay]
    exact hevs

/-- Single-envelope (`HeaderSentArmEnv`) relocatable `.headerSent` arm of `<States>::recv`
    (`+780 -> s0.x30`, Block `332`). -/
theorem states_recv_arm_headerSent_env_placed [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {F : ShaCompress} {K : MlKem}
    {ext : String → Option (State → State)}
    (hdealloc : HookSat (Rust.withPanics ext) spqrDeallocSym (rustCliDeallocBudgetSpec M A lim))
    (hcall : subroutine_ok (lsProg_332 (Rust.withPanics ext))
      (lsmpl.base 337)
      (withLsCodeRoLoaded lsmpl (headerSentRecvCt1ChunkPlacedSpec M A lim F)))
    (hmemcpy_sat : HookSat (Rust.withPanics ext) spqrMemcpySym (withVmPreserved sessionMemcpySpec))
    (st_cost : M.σ)
    (s0 s : State) (outA selfA msgA : BitVec 64)
    (st : Chunked.SendEk.HeaderSent spqrPolyApi (spqrAuthApi F))
    (msg : Message spqrPolyApi)
    (R : SepProp)
    (hFit : FitsEnv M lim st_cost (HeaderSentArmEnv st msg))
    (hcro : LibsignalCodeRoLoaded lsmpl s.mem)
    (hinv : statesRecvPreInv (.headerSent st))
    (hpc : s.pc = lsmpl.base 332 + 780#64)
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
    SepWPp (lsProg_332 (Rust.withPanics ext)) (s0.readReg64 Reg.lr) s
      (memRegion outA v1RecvSize ∗
        chunkedStatesAt A.repAlloc selfA (.headerSent st) ∗
        messageAt spqrPolyApi msgA msg ∗
        statesRecvRoPlacedAt ∗
        A.pool lim st_cost s ∗
        stackAt (s0.sp - 4240#64) statesRecvCalleeStackX ∗
        memRegion (s0.sp - 4240#64) 4144 ∗
        statesRecvSavedCells s0)
      (fun sf P_f =>
        (sf.mem ⊨ P_f ∗ R →
          sf.mem ⊨
            (DefsPlacedBudget.statesRecvVariantPlacedSpecOfEnv M A lim F K (.headerSent st) msg
              (fun _ => HeaderSentArmEnv st msg)).post
              ((outA, selfA, msgA), st_cost) s0 sf ∗ R) ∧
        sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf)
      (fun sf P_f =>
        (sf.mem ⊨ P_f ∗ R) →
          (sf.mem ⊨
            (DefsPlacedBudget.statesRecvVariantPlacedSpecOfEnv M A lim F K (.headerSent st) msg
              (fun _ => HeaderSentArmEnv st msg)).onPanic
              ((outA, selfA, msgA), st_cost) s0 sf ∗ R)) :=
  states_recv_arm_headerSent_exact_placed
    hdealloc hcall hmemcpy_sat st_cost s0 s outA selfA msgA st msg R
    (FitsEnv.mono (fun _ h => headerSentArmPreEnv_sub_postEnv st msg h) hFit)
    hcro hinv hpc hrun hsp hsp_align hx1 hx19 hx24 htr

/-- Envelope-parametric top-level relocatable `subroutine_ok` theorem for `<States>::recv`
    (Block `332`) on the `.headerSent` variant with `withLsCodeRoLoaded lsmpl`. -/
theorem states_recv_headerSent_placed_ok_ext_ofPrePostEnv [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {F : ShaCompress} {K : MlKem} {envs : StatesRecvCalleeEnvs F}
    {PreEnv PostEnv : StatesRecvGhost F → List AllocEvent → Prop}
    {ext : String → Option (State → State)}
    (hC : DefsPlacedBudget.StatesRecvPlacedContractsOfEnv M A lim F K envs ext)
    (st : Chunked.SendEk.HeaderSent spqrPolyApi (spqrAuthApi F))
    (msg : Message spqrPolyApi)
    (hPre_ct1 : ∀ (outA selfA msgA fsp : BitVec 64) (st_cost : M.σ) chunk outRes,
      msg.epoch = st.uc.epoch →
      msg.payload = .ct1 chunk →
      st.recv_ct1_chunk st.uc.epoch chunk = .ok outRes →
      FitsEnv M lim st_cost (PreEnv ⟨outA, selfA, msgA, .headerSent st, msg⟩) →
      FitsEnv M lim st_cost
        (envs.headerSentRecvCt1Pre ⟨fsp + 976#64, fsp + 1856#64, msgA + 10#64,
          st, chunk, outRes⟩))
    (hPost_gt : ∀ outA selfA msgA, msg.epoch > st.uc.epoch →
      ∀ evs, FreeOnlyEvs evs → PostEnv ⟨outA, selfA, msgA, .headerSent st, msg⟩ evs)
    (hPost_lt : ∀ outA selfA msgA, msg.epoch < st.uc.epoch →
      PostEnv ⟨outA, selfA, msgA, .headerSent st, msg⟩ [])
    (hPost_ct1 : ∀ (outA selfA msgA fsp : BitVec 64) chunk outRes evs,
      msg.epoch = st.uc.epoch →
      msg.payload = .ct1 chunk →
      st.recv_ct1_chunk st.uc.epoch chunk = .ok outRes →
      envs.headerSentRecvCt1Post ⟨fsp + 976#64, fsp + 1856#64, msgA + 10#64,
        st, chunk, outRes⟩ evs →
      PostEnv ⟨outA, selfA, msgA, .headerSent st, msg⟩ evs)
    (hPost_other : ∀ outA selfA msgA, msg.epoch = st.uc.epoch →
      (∀ c, msg.payload ≠ .ct1 c) →
      PostEnv ⟨outA, selfA, msgA, .headerSent st, msg⟩ []) :
    subroutine_ok (lsProg_332 (Rust.withPanics ext))
      (lsmpl.base 332)
      (withLsCodeRoLoaded lsmpl
        (DefsPlacedBudget.statesRecvVariantPlacedSpecOfPrePostEnv M A lim F K (.headerSent st) msg PreEnv PostEnv)) := by
  apply subroutine_ok_of_sepWPp
  rintro ⟨⟨outA, selfA, msgA⟩, st_cost⟩ R s0 hpc0 hrun0 hpre hsp0_align
  obtain ⟨hcro0, hpre⟩ := extract_withLsCodeRoLoaded hpre
  simp only [DefsPlacedBudget.statesRecvVariantPlacedSpecOfPrePostEnv, sepConj_assoc, satisfies_pure_sepConj] at hpre
  rcases hpre with ⟨⟨hx0, hx1, hx2, hinv, hfit, hlr_ls⟩, hmem⟩
  have _hlr_x30 : LsRetAddr624 (s0.readReg64 .x30) := hlr_ls
  refine ⟨stackAt s0.sp statesRecvStackX ∗ A.pool lim st_cost s0 ∗
      (memRegion outA v1RecvSize ∗ chunkedStatesAt A.repAlloc selfA (.headerSent st) ∗
       messageAt spqrPolyApi msgA msg ∗ statesRecvRoPlacedAt),
    R, Satisfies.mono (Entails.of_eq (by sep_ac_rfl)) hmem, ?_⟩
  have hpro := states_recv_prologue_pool_placed (A := A) (lim := lim) (ext := ext) st_cost s0
    (memRegion outA v1RecvSize ∗ chunkedStatesAt A.repAlloc selfA (.headerSent st) ∗
     messageAt spqrPolyApi msgA msg ∗ statesRecvRoPlacedAt) hsp0_align hpc0 hrun0
  refine sepWPp_seq_vm_lscro hcro0 hpro ?_
  intro s1 hpc1 hrun1 _ ⟨_, hsp1, hx0_1, hx1_1, hx2_1, _, hx29_1, htr1⟩ hcro1
  rw [hx0] at hx0_1; rw [hx1] at hx1_1; rw [hx2] at hx2_1
  dsimp only [chunkedStatesAt]
  have hdisp := states_recv_dispatch_pool_placed (A := A) (lim := lim) (ext := ext) st_cost s1
    (s0.sp - 4240#64) selfA 4#64
    (chunkedHeaderSentAt A.repAlloc (selfA + 8#64) st ∗ memRegion (selfA + 888#64) 40 ∗
     memRegion outA v1RecvSize ∗ messageAt spqrPolyApi msgA msg ∗
     stackAt (s0.sp - 4240#64) statesRecvCalleeStackX ∗ memRegion (s0.sp - 4240#64) 4144 ∗
     statesRecvSavedCells s0)
    (by unfold ValidStatesTag; decide) hpc1 hrun1 hsp1 hx1_1
  refine sepWPp_seq_vm_lscro hcro1 (SepWP.weaken_pre (Entails.of_eq (by sep_ac_rfl)) hdisp) ?_
  intro s2 hpc2 hrun2 _ ⟨hsp2, hx0_2, hx1_2, hx2_2, _, _, _, hx19_2, _, hx24_2, _, hx29_2, htr2⟩ hcro2
  rw [hx0_1] at hx19_2; rw [hx2_1] at hx24_2
  have hpre2 :
      (selfA ↦₆₄ 4#64) ∗ statesRecvRoPlacedAt ∗ A.pool lim st_cost s2 ∗
      (chunkedHeaderSentAt A.repAlloc (selfA + 8#64) st ∗ memRegion (selfA + 888#64) 40 ∗
       memRegion outA v1RecvSize ∗ messageAt spqrPolyApi msgA msg ∗
       stackAt (s0.sp - 4240#64) statesRecvCalleeStackX ∗ memRegion (s0.sp - 4240#64) 4144 ∗
       statesRecvSavedCells s0) ⊢
      memRegion outA v1RecvSize ∗ chunkedStatesAt A.repAlloc selfA (.headerSent st) ∗
      messageAt spqrPolyApi msgA msg ∗ statesRecvRoPlacedAt ∗ A.pool lim st_cost s2 ∗
      stackAt (s0.sp - 4240#64) statesRecvCalleeStackX ∗ memRegion (s0.sp - 4240#64) 4144 ∗
      statesRecvSavedCells s0 := by
    dsimp only [chunkedStatesAt]; exact Entails.of_eq (by sep_ac_rfl)
  refine SepWPp.weaken_pre hpre2 ?_
  exact states_recv_arm_headerSent_placed_ofPrePostEnv
    (PreEnv := PreEnv) (PostEnv := PostEnv)
    hC.hdealloc_sat hC.headerSentRecvCt1Chunk_ok hC.hmemcpy_sat st_cost
    s0 s2 outA selfA msgA st msg R hfit
    (hPre_ct1 outA selfA msgA (s0.sp - 4240#64) st_cost)
    (hPost_gt outA selfA msgA)
    (hPost_lt outA selfA msgA)
    (hPost_ct1 outA selfA msgA (s0.sp - 4240#64))
    (hPost_other outA selfA msgA)
    hcro2 hinv hpc2 hrun2 hsp2 hsp0_align hx1_2 hx19_2 hx24_2 (htr2.trans htr1)

/-- Exact-envelope (`HeaderSentArmPreEnv` / `HeaderSentArmPostEnv`) top-level relocatable
    `subroutine_ok` theorem for `<States>::recv` (Block `332`) on the `.headerSent` variant. -/
theorem states_recv_headerSent_exact_placed_ok_ext [LibsignalPlacement]
    (M : AllocCostModel) (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (F : ShaCompress) (K : MlKem)
    (ext : String → Option (State → State))
    (hC : DefsPlacedBudget.StatesRecvPlacedContracts M A lim F K ext)
    (st : Chunked.SendEk.HeaderSent spqrPolyApi (spqrAuthApi F))
    (msg : Message spqrPolyApi) :
    subroutine_ok (lsProg_332 (Rust.withPanics ext))
      (lsmpl.base 332)
      (withLsCodeRoLoaded lsmpl
        (DefsPlacedBudget.statesRecvVariantPlacedSpecOfPrePostEnv M A lim F K (.headerSent st) msg
          (fun _ => HeaderSentArmPreEnv st msg)
          (fun _ => HeaderSentArmPostEnv st msg))) := by
  refine states_recv_headerSent_placed_ok_ext_ofPrePostEnv hC st msg ?_ ?_
    (fun _ _ _ _ => headerSentArmPostEnv_nil st msg) ?_
    (fun _ _ _ _ _ => headerSentArmPostEnv_nil st msg)
  · intro _ _ msgA fsp _ chunk outRes heq hpay _ hF
    have hEqEnv : HeaderSentArmPreEnv st msg =
        HeaderSentRecvCt1ChunkPreEnv
          ⟨fsp + 976#64, fsp + 1856#64, msgA + 10#64, st, chunk, outRes⟩ := by
      funext evs
      unfold HeaderSentArmPreEnv HeaderSentRecvCt1ChunkPreEnv
      have hngt : ¬ (msg.epoch > st.uc.epoch) := by rw [heq]; exact BitVec.lt_irrefl _
      have hnlt : ¬ (msg.epoch < st.uc.epoch) := by rw [heq]; exact BitVec.lt_irrefl _
      simp only [hngt, hnlt, ↓reduceIte, hpay]
    dsimp only [DefsPlacedBudget.statesRecvCalleeEnvs]
    rwa [← hEqEnv]
  · intro _ _ _ hgt evs hevs
    unfold HeaderSentArmPostEnv
    simp only [hgt, ↓reduceIte]
    exact hevs
  · intro _ _ _ _ chunk outRes evs heq hpay _ hevs
    dsimp only [DefsPlacedBudget.statesRecvCalleeEnvs] at hevs
    unfold HeaderSentRecvCt1ChunkPostEnv HeaderSentRecvCt1ChunkPreEnv at hevs
    unfold HeaderSentArmPostEnv
    have hngt : ¬ (msg.epoch > st.uc.epoch) := by rw [heq]; exact BitVec.lt_irrefl _
    have hnlt : ¬ (msg.epoch < st.uc.epoch) := by rw [heq]; exact BitVec.lt_irrefl _
    simp only [hngt, hnlt, ↓reduceIte, hpay]
    exact hevs

/-- Single-envelope (`HeaderSentArmEnv`) top-level relocatable `subroutine_ok` theorem for
    `<States>::recv` (Block `332`) on the `.headerSent` variant. -/
theorem states_recv_headerSent_env_placed_ok_ext [LibsignalPlacement]
    (M : AllocCostModel) (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (F : ShaCompress) (K : MlKem)
    (ext : String → Option (State → State))
    (hC : DefsPlacedBudget.StatesRecvPlacedContracts M A lim F K ext)
    (st : Chunked.SendEk.HeaderSent spqrPolyApi (spqrAuthApi F))
    (msg : Message spqrPolyApi) :
    subroutine_ok (lsProg_332 (Rust.withPanics ext))
      (lsmpl.base 332)
      (withLsCodeRoLoaded lsmpl
        (DefsPlacedBudget.statesRecvVariantPlacedSpecOfEnv M A lim F K (.headerSent st) msg
          (fun _ => HeaderSentArmEnv st msg))) :=
  DefsPlacedBudget.subroutine_ok_statesRecvVariantPlacedSpecOfPrePostEnv_weaken
    (fun _ _ _ _ hF => FitsEnv.mono (fun _ h => headerSentArmPreEnv_sub_postEnv st msg h) hF)
    (fun _ _ _ _ h => h)
    (states_recv_headerSent_exact_placed_ok_ext M A lim F K ext hC st msg)

abbrev states_recv_headerSent_cro_placed_ok_ext_ofPrePostEnv :=
  @states_recv_headerSent_placed_ok_ext_ofPrePostEnv

abbrev states_recv_headerSent_cro_exact_placed_ok_ext :=
  @states_recv_headerSent_exact_placed_ok_ext

abbrev states_recv_headerSent_cro_env_placed_ok_ext :=
  @states_recv_headerSent_env_placed_ok_ext

end LibsignalBinary.Proofs.SpqrV1.States.Recv.ArmHeaderSent2PlacedBudget
