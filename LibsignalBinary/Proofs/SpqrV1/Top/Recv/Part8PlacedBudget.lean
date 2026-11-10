/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Heap.IfaceBudgetLemmas
public import LibsignalBinary.Proofs.Placed.BudgetVmSteps
public import LibsignalBinary.Proofs.SpqrV1.Chain.IntoPbHelpersBudget
public import LibsignalBinary.Proofs.SpqrV1.Drop.ProtoTopBudget
public import LibsignalBinary.Proofs.SpqrV1.Prost.EncodeToVec.DefsBudget
public import LibsignalBinary.Proofs.SpqrV1.Top.Recv.DefsPlacedBudget
public import LibsignalBinary.Proofs.SpqrV1.Top.Recv.Part1PlacedBudget
public import LibsignalBinary.Proofs.SpqrV1.Top.Recv.Part2PlacedBudget
public import LibsignalBinary.Proofs.SpqrV1.Top.Recv.Part3PlacedBudget
public import LibsignalBinary.Proofs.SpqrV1.Top.Recv.Part8Placed
import LibsignalBinary.Proofs.Placed.BudgetPoolSync
import LibsignalBinary.Proofs.Placed.ElfLsRetAddr
import LibsignalBinary.Proofs.SpqrV1.Kdf.HkdfToSlice
import LibsignalBinary.Proofs.SpqrV1.Prost.EncodeToVec.AllocReservePhase
import LibsignalBinary.Proofs.SpqrV1.Prost.MessageEncode.Base
import LibsignalBinary.Proofs.SpqrV1.Top.Recv.Part3
import LibsignalBinary.Proofs.SpqrV1.Top.Recv.Part3Placed
import LibsignalBinary.Proofs.SpqrV1.Top.Recv.Part5
import LibsignalBinary.Proofs.SpqrV1.Top.Recv.Part5Placed
import LibsignalBinary.Proofs.SpqrV1.Top.Recv.Part6
import LibsignalBinary.Proofs.SpqrV1.Top.Recv.Part7
import LibsignalBinary.Proofs.SpqrV1.Top.Recv.Part8
import LibsignalBinary.Proofs.SpqrV1.Top.Recv.Pure
import ProofLib.SepLogic.WPp
meta import LibsignalBinary.Proofs.Common.SharedHelpers -- shake: keep
meta import LibsignalBinary.Proofs.Placed.BudgetVmSteps -- shake: keep

/-!
# Budget-Threaded Relocatable `Ordering::Greater` Continuations for `spqr::recv`

Envelope-parametric and default `SpqrRecvEnv` proofs of `step_v0_err_2388_placed` and
`step_v0_recvKey_ok_2184_placed` for `spqr::recv` (Block `329`).
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 400000
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false

namespace LibsignalBinary.Proofs.SpqrV1.Top.Recv.Part8PlacedBudget

open Arm64 ProofLib ProofLib.ProgramReflection
open CryptoGames.LibsignalSession (ShaCompress)
open CryptoVerification
  (LibsignalPlacement lsmpl sepWP_seq_lscl withMemEq)
open CryptoVerification.RustHeap (vecU8 vecU8Buf)
open CryptoVerification.LibsignalTripleRatchet (VecArg doReserveStackX)
open CryptoVerification.LibsignalSpqrV1
  (Bytes Chain Error MlKem PqRatchetState V1State VersionNegotiationPB recvResultExactKeyAt
   spqrV1Recv)
open CryptoVerification.SpqrV1.ChainProofs
  (ChainGhost ChainIntoPbCall chainAt chainIntoPbStackX chainRepr)
open CryptoVerification.SpqrV1.Drop
  (dropStack96 optProtoInnerStateJumpTablePlacedAt optProtoPqRatchetInnerAt
   protoPqRatchetStateAt protoPqRatchetStateSize)
open CryptoVerification.SpqrV1.Prost.EncodeToVec
  (PqRatchetStateEncodeToVecGhost encodeToVecStackOf extractLsb_hi_append64
   extractLsb_lo_append64 pqRatchetStatePBAt)
open CryptoVerification.SpqrV1.ProtoRepr (chainPBAt)
open CryptoVerification.SpqrV1.States.FromPb (StatesFromPbGhost)
open CryptoVerification.SpqrV1.States.IntoPb (StatesIntoPbGhost)
open CryptoVerification.SpqrV1.States.Recv (StatesRecvGhost)
open CryptoVerification.SpqrV1.Top.ChainFromVersionNegotiation (spqrErrorTag)
open CryptoVerification.SpqrV1.Top.DecodeState
  (DecodeStateGhost TraceVRegs V1InnerHeapPred optVersionNegotiationPBTailAt
   relocOptProtoPqRatchetInnerAt relocOptVersionNegotiationPBTailAt)
open CryptoVerification.SpqrV1.Top.InitInner (InitInnerGhost)
open CryptoVerification.SpqrV1.Top.Recv
  (SepWPpLS Words27 assemble_pqRatchetStatePBAt_3056 bytes224_expose_words28_move
   bytes32_expose_words4_move fp_sub_32_eq fp_sub_48_eq frame1912_split_err_2388
   frame4544_join_err_2388 frame_pure_pre hsp_add_544_eq_v0 hsp_add_560_eq_v0
   memRegion_224_sub_entails_words28 optProtoPqRatchetInnerAt_eq_drop
   ownFrame_join_4896_ok_2380 protoPqRatchetStateAt_eq_pqRatchetStatePBAt
   recv_err_q0_foldX recv_ok_some_foldX ret_48_split ret_48_split_6
   sp_sub_4992_aligned spqrRecvCalleeStackX spqrRecvPlacedEntry spqrRecvPlacedProg
   spqrRecvRoPlacedAt spqrRecvRoPlacedAt_expose_dropJumpTable spqrRecvSavedRegs
   spqrV1Recv_noPanic_of_recv_ok stackAt_spqrRecvCallee_split
   subroutine_ok_withMemEq_of_lscl vecU8_sub_entails_header_buf
   words27SubAt words3_sub2096_to_memRegion_24)
open CryptoVerification.SpqrV1.Top.Recv.Placed (blkLib_eq_329 blkPC_329 blkPl_329)
open LibsignalBinary.Heap
  (AllocCostModel AllocEvent BudgetLimits FitsEnv FreeOnlyEvs RustCliAllocBudget VmPreserved)
open LibsignalBinary.Proofs.Placed.BudgetPoolSync (hooksException sepWP_seg_ls_vm)
open LibsignalBinary.Proofs.SpqrV1.Chain.IntoPbHelpersBudget
  (ChainIntoPbAllocEnv ChainIntoPbEnv chainIntoPbSpecX)
open LibsignalBinary.Proofs.SpqrV1.Drop.ProtoTopBudget (dropProtoPqRatchetStatePlacedSpec)
open LibsignalBinary.Proofs.SpqrV1.Prost.EncodeToVec.DefsBudget
  (PqRatchetStateEncodeToVecEnv pqRatchetStateEncodeToVecSpecOf pqRatchetStateEncodeToVecSpecOfEnv
   pqRatchetStateEncodeToVecSpecX)
open LibsignalBinary.Proofs.SpqrV1.Top.Recv.DefsPlacedBudget
  (SpqrRecvPlacedContracts SpqrRecvPlacedContractsOfEnv)
open LibsignalBinary.Proofs.SpqrV1.Top.Recv.Part1PlacedBudget
  (SpqrRecvEnv sepWP_spqrRecvPlacedPostOfEnv_of_post0 spqrRecvBudgetPanicPost
   spqrRecvPlacedPost spqrRecvPlacedPostOfEnv step_epilogue_placed_ofEnv)
open LibsignalBinary.Proofs.SpqrV1.Top.Recv.Part2PlacedBudget
  (SpqrRecvDropContractsBudget SpqrRecvEnv.append_freeOnly freeOnlyWitness
   seq_vm_clean seq_vm_lscl)
open LibsignalBinary.Proofs.SpqrV1.Top.Recv.Part3PlacedBudget
  (SepWPpLS.call_lscro step_drop_pre_2540_placed_ofEnv)

export CryptoVerification.SpqrV1.Top.Recv (spqrRecvRoPlacedAt_expose_dropJumpTable)

variable [LibsignalPlacement]

attribute [local irreducible] Program.fetch Program.externAt? Program.fnAddr Program.fnOff Obj.lookup
attribute [local arm64_norm, local wp_norm] bv_sub_add_lit BitVec.toNat_zero
  RustCliAllocBudget.pool_setPC RustCliAllocBudget.pool_advancePC
  RustCliAllocBudget.pool_setPState RustCliAllocBudget.pool_writeReg64
  RustCliAllocBudget.pool_writeReg32 RustCliAllocBudget.pool_writeReg
attribute [local simp, local arm64_norm, local wp_norm, local arm64_norm ↓, local wp_norm ↓]
  extractLsb_lo_append64 extractLsb_hi_append64
attribute [local simp, local arm64_norm, local wp_norm]
  fp_sub_32_eq hsp_add_560_eq_v0 fp_sub_48_eq hsp_add_544_eq_v0

private theorem align_pre_wp {prog : Program} {target_pc : BitVec 64} {s : State}
    {P P' : SepProp} {post : State → SepProp → Prop}
    (heq : P = P') (hwp : SepWP prog target_pc s P' post) :
    SepWP prog target_pc s P post :=
  heq ▸ hwp

theorem SpqrRecvPlacedContractsOfEnv.toDropContracts {MC : AllocCostModel}
    {H_inner : V1InnerHeapPred} {A : RustCliAllocBudget MC} {lim : BudgetLimits}
    {F : ShaCompress} {K : MlKem}
    {DecodePreEnv DecodePostEnv : DecodeStateGhost → List AllocEvent → Prop}
    {InitEnv : InitInnerGhost → List AllocEvent → Prop}
    {FromPbEnv : V1State → List AllocEvent → Prop}
    {RecvEnv : StatesRecvGhost F → List AllocEvent → Prop}
    {IntoPbEnv : StatesIntoPbGhost F → List AllocEvent → Prop}
    {ext : String → Option (State → State)}
    (hC : SpqrRecvPlacedContractsOfEnv H_inner A lim F K
      DecodePreEnv DecodePostEnv InitEnv FromPbEnv RecvEnv IntoPbEnv ext) :
    SpqrRecvDropContractsBudget A lim F ext :=
  ⟨hC.dealloc_ok, hC.dropEpochSlice_ok, hC.dropOptProtoInnerState_ok,
    hC.dropOptProtoChain_ok, hC.dropChain_ok, hC.dropPqRatchetState_ok, hC.dropStates_ok⟩

omit [LibsignalPlacement] in
theorem chainIntoPbAllocEnv_indep (o1 p1 o2 p2 : BitVec 64) (g1 g2 : ChainGhost) (ch : Chain) :
    ChainIntoPbAllocEnv ⟨o1, p1, g1, ch⟩ = ChainIntoPbAllocEnv ⟨o2, p2, g2, ch⟩ := rfl

omit [LibsignalPlacement] in
theorem chainIntoPbEnv_indep (o1 p1 o2 p2 : BitVec 64) (g1 g2 : ChainGhost) (ch : Chain) :
    ChainIntoPbEnv ⟨o1, p1, g1, ch⟩ = ChainIntoPbEnv ⟨o2, p2, g2, ch⟩ := rfl

/-! ## 1. `step_v0_err_2388_placed` (`+2388 .. +2420 -> +2540`) -/

/-- Envelope-parametric shared error exit at `+2388 .. +2420 -> +2540` for `Ordering::Greater`:
    reads the 24-byte error payload from `s0.sp - 2088#64 .. s0.sp - 2064#64` (with `x22 = s0.sp
    - 2096#64`), writes `Err(e == .stateDecode)` to `ret` (`x19`), and jumps to `+2540`
    (`step_drop_pre_2540_placed_ofEnv`) to drop `vn` and `pb`. -/
theorem step_v0_err_2388_placed_ofEnv {MC : AllocCostModel}
    (A : RustCliAllocBudget MC) (lim : BudgetLimits) (st_cost : MC.σ)
    (Env : List AllocEvent → Prop) (evs0 : List AllocEvent)
    (hevs_free : ∀ evs_d, FreeOnlyEvs evs_d → Env (evs0 ++ evs_d))
    (F : ShaCompress) (K : MlKem)
    (ext : String → Option (State → State))
    (hC : SpqrRecvDropContractsBudget A lim F ext)
    (st msg : VecArg) (ret : BitVec 64)
    (vn : VersionNegotiationPB) (pb : V1State) (e : Error)
    (w0 w1 w0_err : BitVec 64)
    (herr : (spqrV1Recv F K).recv st.bytes msg.bytes = .error (e == .stateDecode))
    (hnp : ¬ (spqrV1Recv F K).recvPanics st.bytes msg.bytes)
    (s0 s : State) (P R : SepProp)
    (hs0_align : s0.spAligned = true)
    (hpc : s.pc = spqrRecvPlacedEntry + 2388#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = s0.sp - 4992#64)
    (htr : TraceVRegs s s0)
    (hx19 : s.readReg64 .x19 = ret)
    (hx20 : s.readReg64 .x20 = w0)
    (hx22 : s.readReg64 .x22 = s0.sp - 2096#64)
    (hx29 : s.readReg64 .x29 = s0.sp - 96#64)
    (hP : P =
      spqrRecvRoPlacedAt ∗
      st.at A.repAlloc ∗
      msg.at A.repAlloc ∗
      memRegion ret 48 ∗
      A.pool lim (MC.stepEvents evs0 st_cost) s ∗
      stackAt (s0.sp - 4992#64) spqrRecvCalleeStackX ∗
      ((s0.sp - 4992#64) ↦₆₄ w0) ∗
      ((s0.sp - 4984#64) ↦₆₄ w1) ∗
      optVersionNegotiationPBTailAt A.repAlloc w0 w1 (s0.sp - 4976#64) (some vn) ∗
      memRegion (s0.sp - 4944#64) 80 ∗
      optProtoPqRatchetInnerAt A.repAlloc (s0.sp - 4864#64) (some (.v1 pb)) ∗
      memRegion (s0.sp - 4640#64) 2544 ∗
      ((s0.sp - 2096#64) ↦₆₄ w0_err) ∗
      (∃∗ q0 : BitVec 128, ∃∗ w3 : BitVec 64,
        ⌜BitVec.truncate 8 q0 = spqrErrorTag e⌝ ∗
        ((s0.sp - 2088#64) ↦₆₄ q0.extractLsb' 0 64) ∗
        ((s0.sp - 2080#64) ↦₆₄ q0.extractLsb' 64 64) ∗
        ((s0.sp - 2072#64) ↦₆₄ w3)) ∗
      memRegion (s0.sp - 2064#64) 56 ∗
      memRegion (s0.sp - 2008#64) 1912 ∗
      spqrRecvSavedRegs (s0.sp - 4992#64) s0) :
    SepWPpLS (spqrRecvPlacedProg ext) (s0.readReg64 .x30) s P
      (spqrRecvPlacedPostOfEnv A lim st_cost Env (spqrV1Recv F K) st msg ret s0 R)
      (spqrRecvBudgetPanicPost (spqrV1Recv F K) st msg s0 R) := by
  rcases htr with ⟨htr_eq, hvregs⟩
  apply SepWPpLS.of_sepWP_ret_lscl; intro hcl
  subst hP
  dsimp only [spqrRecvPlacedProg, spqrRecvPlacedEntry, BitVec.ofNat_eq_ofNat] at hpc ⊢
  rw [frame1912_split_err_2388 s0.sp, ret_48_split ret]
  simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
  wp_pull_exists; rename_i d0 d1 d2 q0_err w3_err r0 r1 r2 r3
  wp_focus_pure; intro htag_q0
  have hret_fold :
      ((ret ↦₆₄ 0xFFFFFFFFFFFFFFFF#64) ∗
        ((ret + 8#64) ↦₆₄ q0_err.extractLsb' 0 64) ∗
        ((ret + 16#64) ↦₆₄ q0_err.extractLsb' 64 64) ∗
        ((ret + 24#64) ↦₆₄ w3_err) ∗
        memRegion (ret + 32#64) 16) ⊢
      recvResultExactKeyAt A.repAlloc ret ((spqrV1Recv F K).recv st.bytes msg.bytes) := by
    rw [herr]
    exact recv_err_q0_foldX A.repAlloc ret (q0_err.extractLsb' 64 64) w3_err q0_err e htag_q0
  refine seq_vm_lscl hcl (mid := (blkPl_329).base + 2540#64)
    (P_mid :=
      spqrRecvRoPlacedAt ∗
      st.at A.repAlloc ∗
      msg.at A.repAlloc ∗
      recvResultExactKeyAt A.repAlloc ret ((spqrV1Recv F K).recv st.bytes msg.bytes) ∗
      A.pool lim (MC.stepEvents evs0 st_cost) s ∗
      stackAt (s0.sp - 4992#64) spqrRecvCalleeStackX ∗
      ((s0.sp - 4992#64) ↦₆₄ w0) ∗
      ((s0.sp - 4984#64) ↦₆₄ w1) ∗
      optVersionNegotiationPBTailAt A.repAlloc w0 w1 (s0.sp - 4976#64) (some vn) ∗
      memRegion (s0.sp - 4944#64) 80 ∗
      optProtoPqRatchetInnerAt A.repAlloc (s0.sp - 4864#64) (some (.v1 pb)) ∗
      memRegion (s0.sp - 4640#64) 4544 ∗
      spqrRecvSavedRegs (s0.sp - 4992#64) s0)
    (Q := fun sm =>
      sm.sp = s0.sp - 4992#64 ∧
      TraceVRegs sm s0 ∧
      sm.readReg64 .x20 = w0)
    ?_ ?_
  · by_vm_steps (
      wp_steps 9
      refine SepWP.focus_weaken hret_fold (by sep_focus) ?_
      refine SepWP.focus_weaken
        (frame4544_join_err_2388 s0.sp w0_err
          (q0_err.extractLsb' 0 64) (q0_err.extractLsb' 64 64) w3_err
          (q0_err.extractLsb' 0 64) (q0_err.extractLsb' 64 64) w3_err)
        (by sep_focus) ?_
      refine align_pre_wp (by sep_ac_rfl) ?_
      wp_done
    )
  · intro s1 hpc1 hrun1 hcl1 hvm ⟨hsp1, htr1, hx20_1⟩
    rw [← A.pool_transport lim (MC.stepEvents evs0 st_cost) s s1 hvm]
    refine sepWP_spqrRecvPlacedPostOfEnv_of_post0 hnp ?_
    exact step_drop_pre_2540_placed_ofEnv A lim st_cost Env evs0 hevs_free
      (spqrV1Recv F K) ext hC st msg ret vn pb w0 w1
      s0 s1 _ R _ rfl hs0_align hpc1 hrun1 hsp1 htr1 hx20_1 rfl hcl1

theorem step_v0_err_2388_placed {MC : AllocCostModel}
    (A : RustCliAllocBudget MC) (lim : BudgetLimits) (st_cost : MC.σ)
    (F : ShaCompress) (K : MlKem)
    (ext : String → Option (State → State))
    (hC : SpqrRecvDropContractsBudget A lim F ext)
    (st msg : VecArg) (ret : BitVec 64)
    (evs0 : List AllocEvent) (hevs0 : SpqrRecvEnv st msg evs0)
    (vn : VersionNegotiationPB) (pb : V1State) (e : Error)
    (w0 w1 w0_err : BitVec 64)
    (herr : (spqrV1Recv F K).recv st.bytes msg.bytes = .error (e == .stateDecode))
    (hnp : ¬ (spqrV1Recv F K).recvPanics st.bytes msg.bytes)
    (s0 s : State) (P R : SepProp)
    (hs0_align : s0.spAligned = true)
    (hpc : s.pc = spqrRecvPlacedEntry + 2388#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = s0.sp - 4992#64)
    (htr : TraceVRegs s s0)
    (hx19 : s.readReg64 .x19 = ret)
    (hx20 : s.readReg64 .x20 = w0)
    (hx22 : s.readReg64 .x22 = s0.sp - 2096#64)
    (hx29 : s.readReg64 .x29 = s0.sp - 96#64)
    (hP : P =
      spqrRecvRoPlacedAt ∗
      st.at A.repAlloc ∗
      msg.at A.repAlloc ∗
      memRegion ret 48 ∗
      A.pool lim (MC.stepEvents evs0 st_cost) s ∗
      stackAt (s0.sp - 4992#64) spqrRecvCalleeStackX ∗
      ((s0.sp - 4992#64) ↦₆₄ w0) ∗
      ((s0.sp - 4984#64) ↦₆₄ w1) ∗
      optVersionNegotiationPBTailAt A.repAlloc w0 w1 (s0.sp - 4976#64) (some vn) ∗
      memRegion (s0.sp - 4944#64) 80 ∗
      optProtoPqRatchetInnerAt A.repAlloc (s0.sp - 4864#64) (some (.v1 pb)) ∗
      memRegion (s0.sp - 4640#64) 2544 ∗
      ((s0.sp - 2096#64) ↦₆₄ w0_err) ∗
      (∃∗ q0 : BitVec 128, ∃∗ w3 : BitVec 64,
        ⌜BitVec.truncate 8 q0 = spqrErrorTag e⌝ ∗
        ((s0.sp - 2088#64) ↦₆₄ q0.extractLsb' 0 64) ∗
        ((s0.sp - 2080#64) ↦₆₄ q0.extractLsb' 64 64) ∗
        ((s0.sp - 2072#64) ↦₆₄ w3)) ∗
      memRegion (s0.sp - 2064#64) 56 ∗
      memRegion (s0.sp - 2008#64) 1912 ∗
      spqrRecvSavedRegs (s0.sp - 4992#64) s0) :
    SepWPpLS (spqrRecvPlacedProg ext) (s0.readReg64 .x30) s P
      (spqrRecvPlacedPost A lim st_cost (spqrV1Recv F K) st msg ret s0 R)
      (spqrRecvBudgetPanicPost (spqrV1Recv F K) st msg s0 R) :=
  step_v0_err_2388_placed_ofEnv A lim st_cost (SpqrRecvEnv st msg) evs0
    (fun _ hd => SpqrRecvEnv.append_freeOnly hevs0 hd)
    F K ext hC st msg ret vn pb e w0 w1 w0_err herr hnp
    s0 s P R hs0_align hpc hrun hsp htr hx19 hx20 hx22 hx29 hP

/-! ## 2. `step_v0_recvKey_ok_2184_placed` (`+2184 .. +2380 -> +1040`) -/

/-- Envelope-parametric success continuation of `Chain::recv_key` in `Ordering::Greater` (`+2184
    .. +2380 -> +1040`): calls `Chain::into_pb` (Block `365`), moves `vn` (`48`B) and `inner`
    (`224`B) into `s0.sp - 3056#64`, calls `PqRatchetState::encode_to_vec` (Block `426`), writes
    `Ok((newStateBytes, Some(rawKey)))` to `ret` (`x19`), calls `drop_glue::<PqRatchetState>`
    (Block `270`), and jumps to `step_epilogue_placed_ofEnv`. -/
theorem step_v0_recvKey_ok_2184_placed_ofEnv {MC : AllocCostModel}
    {H_inner : V1InnerHeapPred} {A : RustCliAllocBudget MC} {lim : BudgetLimits}
    {F : ShaCompress} {K : MlKem}
    {DecodePreEnv DecodePostEnv : DecodeStateGhost → List AllocEvent → Prop}
    {InitEnv : InitInnerGhost → List AllocEvent → Prop}
    {FromPbEnv : V1State → List AllocEvent → Prop}
    {RecvEnv : StatesRecvGhost F → List AllocEvent → Prop}
    {IntoPbEnv : StatesIntoPbGhost F → List AllocEvent → Prop}
    {ext : String → Option (State → State)}
    (st_cost : MC.σ) (Env : List AllocEvent → Prop) (evs0 : List AllocEvent)
    (hC : SpqrRecvPlacedContractsOfEnv H_inner A lim F K
      DecodePreEnv DecodePostEnv InitEnv FromPbEnv RecvEnv IntoPbEnv ext)
    (st msg : VecArg) (ret : BitVec 64)
    (vn : VersionNegotiationPB) (pb : V1State)
    (chain1 : Chain) (rawKey : Bytes)
    (w0 w1 cap_rk ptr_rk : BitVec 64)
    (d880 d888 d896 u0 u1 u2 u3 u4 u5 e0 e1 e2 : BitVec 64)
    (henc_len :
      (PqRatchetState.encodeRaw
        { versionNegotiation := some vn, chain := some chain1.intoPb, inner := some (.v1 pb) }).length < 2 ^ 63)
    (hok : (spqrV1Recv F K).recv st.bytes msg.bytes =
      .ok (PqRatchetState.encodeRaw
        { versionNegotiation := some vn, chain := some chain1.intoPb, inner := some (.v1 pb) },
        some rawKey))
    (s0 s : State) (P R : SepProp)
    (hfits_into : ∀ gChain : ChainGhost,
      FitsEnv MC lim (MC.stepEvents evs0 st_cost)
        (ChainIntoPbAllocEnv ⟨s0.sp - 3008#64, s0.sp - 4288#64, gChain, chain1⟩))
    (hfits_enc : ∀ gChain evs_into,
      ChainIntoPbEnv ⟨s0.sp - 3008#64, s0.sp - 4288#64, gChain, chain1⟩ evs_into →
      FitsEnv MC lim (MC.stepEvents (evs0 ++ evs_into) st_cost)
        (PqRatchetStateEncodeToVecEnv
          { versionNegotiation := some vn, chain := some chain1.intoPb, inner := some (.v1 pb) }))
    (hevs_done : ∀ gChain evs_into evs_enc evs_drop,
      ChainIntoPbEnv ⟨s0.sp - 3008#64, s0.sp - 4288#64, gChain, chain1⟩ evs_into →
      PqRatchetStateEncodeToVecEnv
        { versionNegotiation := some vn, chain := some chain1.intoPb, inner := some (.v1 pb) } evs_enc →
      FreeOnlyEvs evs_drop →
      Env (evs0 ++ evs_into ++ evs_enc ++ evs_drop))
    (hs0_align : s0.spAligned = true)
    (hpc : s.pc = spqrRecvPlacedEntry + 2184#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = s0.sp - 4992#64)
    (htr : TraceVRegs s s0)
    (hx19 : s.readReg64 .x19 = ret)
    (hx21 : s.readReg64 .x21 = s0.sp - 3056#64)
    (hx22 : s.readReg64 .x22 = s0.sp - 2096#64)
    (hP : P =
      spqrRecvRoPlacedAt ∗
      st.at A.repAlloc ∗
      msg.at A.repAlloc ∗
      memRegion ret 48 ∗
      A.pool lim (MC.stepEvents evs0 st_cost) s ∗
      stackAt (s0.sp - 4992#64) spqrRecvCalleeStackX ∗
      ((s0.sp - 4992#64) ↦₆₄ w0) ∗
      ((s0.sp - 4984#64) ↦₆₄ w1) ∗
      optVersionNegotiationPBTailAt A.repAlloc w0 w1 (s0.sp - 4976#64) (some vn) ∗
      memRegion (s0.sp - 4944#64) 80 ∗
      optProtoPqRatchetInnerAt A.repAlloc (s0.sp - 4864#64) (some (.v1 pb)) ∗
      memRegion (s0.sp - 4640#64) 352 ∗
      chainRepr A.repAlloc (s0.sp - 4288#64) chain1 ∗
      memRegion (s0.sp - 4200#64) 88 ∗
      ((s0.sp - 4112#64) ↦₆₄ d880) ∗
      ((s0.sp - 4104#64) ↦₆₄ d888) ∗
      ((s0.sp - 4096#64) ↦₆₄ d896) ∗
      memRegion (s0.sp - 4088#64) 1032 ∗
      ((s0.sp - 3056#64) ↦₆₄ u0) ∗
      ((s0.sp - 3048#64) ↦₆₄ u1) ∗
      ((s0.sp - 3040#64) ↦₆₄ u2) ∗
      ((s0.sp - 3032#64) ↦₆₄ u3) ∗
      ((s0.sp - 3024#64) ↦₆₄ u4) ∗
      ((s0.sp - 3016#64) ↦₆₄ u5) ∗
      memRegion (s0.sp - 3008#64) 80 ∗
      memRegion (s0.sp - 2928#64) 224 ∗
      memRegion (s0.sp - 2704#64) 608 ∗
      ((s0.sp - 2096#64) ↦₆₄ cap_rk) ∗
      ((s0.sp - 2088#64) ↦₆₄ ptr_rk) ∗
      ((s0.sp - 2080#64) ↦₆₄ BitVec.ofNat 64 rawKey.length) ∗
      vecU8Buf A.repAlloc cap_rk ptr_rk rawKey ∗
      ((s0.sp - 2072#64) ↦₆₄ e0) ∗
      ((s0.sp - 2064#64) ↦₆₄ e1) ∗
      ((s0.sp - 2056#64) ↦₆₄ e2) ∗
      memRegion (s0.sp - 2048#64) 1952 ∗
      spqrRecvSavedRegs (s0.sp - 4992#64) s0) :
    SepWPpLS (spqrRecvPlacedProg ext) (s0.readReg64 .x30) s P
      (spqrRecvPlacedPostOfEnv A lim st_cost Env (spqrV1Recv F K) st msg ret s0 R)
      (spqrRecvBudgetPanicPost (spqrV1Recv F K) st msg s0 R) := by
  have hinto_pb := hC.chainIntoPb_ok
  have henc_ok := hC.encodeToVec_ok
  have hfsp_align : ((s0.sp - 4992#64) &&& 15#64 == 0#64) = true :=
    sp_sub_4992_aligned s0 hs0_align
  rcases htr with ⟨htr_eq, hvregs⟩
  subst hP
  apply SepWPpLS.of_sepWP (mid := lsmpl.base 365)
  dsimp only [spqrRecvPlacedProg, spqrRecvPlacedEntry, BitVec.ofNat_eq_ofNat] at hpc ⊢
  unfold chainRepr
  simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
  wp_pull_exists; rename_i G_c1
  refine seq_vm_clean (mid := lsmpl.base 365)
    (P_mid :=
      spqrRecvRoPlacedAt ∗
      st.at A.repAlloc ∗
      msg.at A.repAlloc ∗
      memRegion ret 48 ∗
      A.pool lim (MC.stepEvents evs0 st_cost) s ∗
      stackAt (s0.sp - 4992#64) spqrRecvCalleeStackX ∗
      ((s0.sp - 4992#64) ↦₆₄ w0) ∗
      ((s0.sp - 4984#64) ↦₆₄ w1) ∗
      optVersionNegotiationPBTailAt A.repAlloc w0 w1 (s0.sp - 4976#64) (some vn) ∗
      memRegion (s0.sp - 4944#64) 80 ∗
      optProtoPqRatchetInnerAt A.repAlloc (s0.sp - 4864#64) (some (.v1 pb)) ∗
      memRegion (s0.sp - 4640#64) 352 ∗
      chainAt A.repAlloc (s0.sp - 4288#64) G_c1 chain1 ∗
      memRegion (s0.sp - 4200#64) 88 ∗
      ((s0.sp - 4112#64) ↦₆₄ cap_rk) ∗
      ((s0.sp - 4104#64) ↦₆₄ ptr_rk) ∗
      ((s0.sp - 4096#64) ↦₆₄ BitVec.ofNat 64 rawKey.length) ∗
      memRegion (s0.sp - 4088#64) 1032 ∗
      ((s0.sp - 3056#64) ↦₆₄ u0) ∗
      ((s0.sp - 3048#64) ↦₆₄ u1) ∗
      ((s0.sp - 3040#64) ↦₆₄ u2) ∗
      ((s0.sp - 3032#64) ↦₆₄ u3) ∗
      ((s0.sp - 3024#64) ↦₆₄ u4) ∗
      ((s0.sp - 3016#64) ↦₆₄ u5) ∗
      memRegion (s0.sp - 3008#64) 80 ∗
      memRegion (s0.sp - 2928#64) 224 ∗
      memRegion (s0.sp - 2704#64) 608 ∗
      ((s0.sp - 2096#64) ↦₆₄ cap_rk) ∗
      ((s0.sp - 2088#64) ↦₆₄ ptr_rk) ∗
      ((s0.sp - 2080#64) ↦₆₄ BitVec.ofNat 64 rawKey.length) ∗
      vecU8Buf A.repAlloc cap_rk ptr_rk rawKey ∗
      ((s0.sp - 2072#64) ↦₆₄ e0) ∗
      ((s0.sp - 2064#64) ↦₆₄ e1) ∗
      ((s0.sp - 2056#64) ↦₆₄ e2) ∗
      memRegion (s0.sp - 2048#64) 1952 ∗
      spqrRecvSavedRegs (s0.sp - 4992#64) s0)
    (Q := fun s1 =>
      s1.sp = s0.sp - 4992#64 ∧
      TraceVRegs s1 s0 ∧
      s1.readReg64 .x8 = s0.sp - 3008#64 ∧
      s1.readReg64 .x0 = s0.sp - 4288#64 ∧
      s1.readReg64 .x19 = ret ∧
      s1.readReg64 .x21 = s0.sp - 3056#64 ∧
      s1.readReg64 .x22 = s0.sp - 2096#64 ∧
      s1.readReg64 Reg.lr = spqrRecvPlacedEntry + 2212#64)
    ?_ ?_
  · by_vm_steps (
      wp_steps 7
      refine align_pre_wp (by sep_ac_rfl) ?_
      wp_done
    )
  · intro s1 hpc1 hrun1 hvm1 ⟨hsp1, ⟨htr1, hvregs1⟩, hx8_1, hx0_1, hx19_1, hx21_1, hx22_1, hlr1⟩
    rw [← A.pool_transport lim (MC.stepEvents evs0 st_cost) s s1 hvm1]
    apply SepWP.done hpc1 hrun1
    refine SepWPpLS.focus_weaken
      (Entails.of_eq (stackAt_spqrRecvCallee_split (s0.sp - 4992#64) chainIntoPbStackX (by decide)))
      (by sep_focus) ?_
    have hs1_align : s1.spAligned = true := by
      rw [State.spAligned, hsp1]; exact hfsp_align
    refine SepWPpLS.call_lscro hinto_pb
      (⟨s0.sp - 3008#64, s0.sp - 4288#64, G_c1, chain1⟩, MC.stepEvents evs0 st_cost)
      hpc1 hrun1 hs1_align hlr1
      (by rw [htr1])
      (fun _ => Entails.trans (Entails.of_eq (sepConj_emp ⌜False⌝).symm)
        (Entails.pure_left False.elim))
      (fun _ _ => rfl)
      (by
        dsimp only [chainIntoPbSpecX]
        rw [← hsp1]
        exact frame_pure_pre ⟨hx8_1, hx0_1, hfits_into G_c1⟩ (by sep_focus))
      ?_
    intro sm hpcm hrunm hspm hcsm
    have hvregs_c := hcsm.2.2.2.2.2.2.2.2.2.2.2
    rcases hcsm with ⟨hx19_cm, _, hx21_cm, hx22_cm, _⟩
    dsimp only [chainIntoPbSpecX]
    simp only [sepExists_sepConj_left, sepConj_assoc]
    apply SepWPpLS.exists_elim; intro evs_into
    refine SepWPpLS.focus_pure (by sep_focus) ?_; rintro ⟨hevs_into, htr_sm, _⟩
    have htr_sm' : TraceVRegs sm s0 := ⟨by rw [htr_sm, htr1], by rw [hvregs_c, hvregs1]⟩
    have hspm' : sm.sp = s0.sp - 4992#64 := by rw [hspm, hsp1]
    have hx19_sm : sm.readReg64 .x19 = ret := by rw [hx19_cm, hx19_1]
    have hx21_sm : sm.readReg64 .x21 = s0.sp - 3056#64 := by rw [hx21_cm, hx21_1]
    have hx22_sm : sm.readReg64 .x22 = s0.sp - 2096#64 := by rw [hx22_cm, hx22_1]
    have hsp_stk1 : stackAt s1.sp chainIntoPbStackX = stackAt (s0.sp - 4992#64) chainIntoPbStackX := by
      rw [hsp1]
    refine SepWPpLS.focus_weaken (Entails.of_eq hsp_stk1) (by sep_focus) ?_
    refine SepWPpLS.focus_weaken
      (Entails.of_eq (stackAt_spqrRecvCallee_split (s0.sp - 4992#64) chainIntoPbStackX (by decide)).symm)
      (by sep_focus) ?_
    apply SepWPpLS.of_sepWP (mid := lsmpl.base 426)
    dsimp only [spqrRecvPlacedProg, spqrRecvPlacedEntry, BitVec.ofNat_eq_ofNat] at hpcm ⊢
    rw [← MC.stepEvents_append]
    refine SepWP.focus_weaken
      (words3_sub2096_to_memRegion_24 s0.sp cap_rk ptr_rk (BitVec.ofNat 64 rawKey.length))
      (by sep_focus) ?_
    refine SepWP.focus_weaken
      ((relocOptVersionNegotiationPBTailAt A.repAlloc w0 w1 (some vn)).2.to_bytes (s0.sp - 4976#64))
      (by sep_focus) ?_
    wp_pull_exists; rename_i bs32
    wp_focus_pure; intro hlen32
    refine SepWP.focus_weaken (bytes32_expose_words4_move s0.sp hlen32) (by sep_focus) ?_
    wp_pull_exists; rename_i v2 v3 v4 v5
    wp_focus_pure; intro hdst32
    rw [← optProtoPqRatchetInnerAt_eq_drop hC.h_inner_eq]
    refine SepWP.focus_weaken
      ((relocOptProtoPqRatchetInnerAt H_inner A.repAlloc (some (.v1 pb))).2.to_bytes (s0.sp - 4864#64))
      (by sep_focus) ?_
    wp_pull_exists; rename_i bs224
    wp_focus_pure; intro hlen224
    refine SepWP.focus_weaken (bytes224_expose_words28_move s0.sp hlen224) (by sep_focus) ?_
    wp_pull_exists; rename_i w_in0 d_in
    wp_focus_pure; intro hdst224
    refine SepWP.focus_weaken (memRegion_224_sub_entails_words28 s0.sp 2928) (by sep_focus) ?_
    wp_pull_exists; rename_i u_in0 u_in
    have hassemble := assemble_pqRatchetStatePBAt_3056 hC.h_inner_eq s0.sp w0 w1 vn chain1.intoPb pb hlen32 hlen224
    rw [← hdst32, ← hdst224] at hassemble
    dsimp only [words27SubAt, Nat.reduceSub, BitVec.ofNat_eq_ofNat] at hassemble ⊢
    simp only [sepConj_assoc]
    rcases htr_sm' with ⟨htr_sm_eq, hvregs_sm⟩
    refine seq_vm_clean (mid := lsmpl.base 426)
      (P_mid :=
        spqrRecvRoPlacedAt ∗
        st.at A.repAlloc ∗
        msg.at A.repAlloc ∗
        memRegion ret 48 ∗
        A.pool lim (MC.stepEvents (evs0 ++ evs_into) st_cost) sm ∗
        stackAt (s0.sp - 4992#64) spqrRecvCalleeStackX ∗
        ((s0.sp - 4992#64) ↦₆₄ w0) ∗
        ((s0.sp - 4984#64) ↦₆₄ w1) ∗
        ((s0.sp - 4976#64) ↦₆₄ v2) ∗
        ((s0.sp - 4968#64) ↦₆₄ v3) ∗
        ((s0.sp - 4960#64) ↦₆₄ v4) ∗
        ((s0.sp - 4952#64) ↦₆₄ v5) ∗
        memRegion (s0.sp - 4944#64) 80 ∗
        ((s0.sp - 4864#64) ↦₆₄ w_in0) ∗
        (let x := words27SubAt s0.sp 4864 d_in; x) ∗
        memRegion (s0.sp - 4640#64) 352 ∗
        memRegion (s0.sp - 4288#64) 88 ∗
        memRegion (s0.sp - 4200#64) 88 ∗
        ((s0.sp - 4112#64) ↦₆₄ cap_rk) ∗
        ((s0.sp - 4104#64) ↦₆₄ ptr_rk) ∗
        ((s0.sp - 4096#64) ↦₆₄ BitVec.ofNat 64 rawKey.length) ∗
        memRegion (s0.sp - 4088#64) 1032 ∗
        pqRatchetStatePBAt A.repAlloc (s0.sp - 3056#64)
          { versionNegotiation := some vn, chain := some chain1.intoPb, inner := some (.v1 pb) } ∗
        memRegion (s0.sp - 2704#64) 608 ∗
        memRegion (s0.sp - 2096#64) 24 ∗
        vecU8Buf A.repAlloc cap_rk ptr_rk rawKey ∗
        ((s0.sp - 2072#64) ↦₆₄ e0) ∗
        ((s0.sp - 2064#64) ↦₆₄ e1) ∗
        ((s0.sp - 2056#64) ↦₆₄ e2) ∗
        memRegion (s0.sp - 2048#64) 1952 ∗
        spqrRecvSavedRegs (s0.sp - 4992#64) s0)
      (Q := fun s2 =>
        s2.sp = s0.sp - 4992#64 ∧
        TraceVRegs s2 s0 ∧
        s2.readReg64 .x0 = s0.sp - 2096#64 ∧
        s2.readReg64 .x1 = s0.sp - 3056#64 ∧
        s2.readReg64 .x19 = ret ∧
        s2.readReg64 .x21 = s0.sp - 3056#64 ∧
        s2.readReg64 .x22 = s0.sp - 2096#64 ∧
        s2.readReg64 Reg.lr = spqrRecvPlacedEntry + 2336#64)
      ?_ ?_
    · dsimp only [words27SubAt, Nat.reduceSub, BitVec.ofNat_eq_ofNat]
      by_vm_steps (
        wp_steps 31
        refine SepWP.focus_weaken hassemble (by sep_focus) ?_
        refine align_pre_wp (by sep_ac_rfl) ?_
        wp_done
      )
    · intro s2 hpc2 hrun2 hvm2 ⟨hsp2, ⟨htr2, hvregs2⟩, hx0_2, hx1_2, hx19_2, hx21_2, hx22_2, hlr2⟩
      rw [← A.pool_transport lim (MC.stepEvents (evs0 ++ evs_into) st_cost) sm s2 hvm2]
      apply SepWP.done hpc2 hrun2
      refine SepWPpLS.focus_weaken
        (Entails.of_eq (stackAt_spqrRecvCallee_split (s0.sp - 4992#64)
          (encodeToVecStackOf doReserveStackX) (by decide)))
        (by sep_focus) ?_
      have hs2_align : s2.spAligned = true := by
        rw [State.spAligned, hsp2]; exact hfsp_align
      refine SepWPpLS.call_lscro henc_ok
        ((⟨s0.sp - 2096#64, s0.sp - 3056#64,
            { versionNegotiation := some vn, chain := some chain1.intoPb, inner := some (.v1 pb) }⟩ :
            PqRatchetStateEncodeToVecGhost),
          MC.stepEvents (evs0 ++ evs_into) st_cost)
        hpc2 hrun2 hs2_align hlr2
        (by rw [htr2])
        (fun _ => Entails.trans (Entails.of_eq (sepConj_emp ⌜False⌝).symm)
          (Entails.pure_left False.elim))
        (fun _ _ => rfl)
        (by
          dsimp only [pqRatchetStateEncodeToVecSpecX, pqRatchetStateEncodeToVecSpecOf,
            pqRatchetStateEncodeToVecSpecOfEnv]
          rw [← hsp2]
          exact frame_pure_pre
            ⟨hx0_2, hx1_2, henc_len, hfits_enc G_c1 evs_into hevs_into⟩
            (by sep_focus))
        ?_
      intro sn hpcn hrunn hspn hcsn
      have hvregs_cn := hcsn.2.2.2.2.2.2.2.2.2.2.2
      rcases hcsn with ⟨hx19_cn, _, hx21_cn, hx22_cn, _⟩
      dsimp only [pqRatchetStateEncodeToVecSpecX, pqRatchetStateEncodeToVecSpecOf,
        pqRatchetStateEncodeToVecSpecOfEnv]
      simp only [sepExists_sepConj_left, sepConj_assoc]
      apply SepWPpLS.exists_elim; intro evs_enc
      refine SepWPpLS.focus_pure (by sep_focus) ?_; rintro ⟨htr_sn, hevs_enc⟩
      have htr_sn' : TraceVRegs sn s0 := ⟨by rw [htr_sn, htr2], by rw [hvregs_cn, hvregs2]⟩
      have hspn' : sn.sp = s0.sp - 4992#64 := by rw [hspn, hsp2]
      have hx19_sn : sn.readReg64 .x19 = ret := by rw [hx19_cn, hx19_2]
      have hx21_sn : sn.readReg64 .x21 = s0.sp - 3056#64 := by rw [hx21_cn, hx21_2]
      have hx22_sn : sn.readReg64 .x22 = s0.sp - 2096#64 := by rw [hx22_cn, hx22_2]
      have hsp_stk2 :
          stackAt s2.sp (encodeToVecStackOf doReserveStackX) =
            stackAt (s0.sp - 4992#64) (encodeToVecStackOf doReserveStackX) := by
        rw [hsp2]
      refine SepWPpLS.focus_weaken (Entails.of_eq hsp_stk2) (by sep_focus) ?_
      refine SepWPpLS.focus_weaken
        (Entails.of_eq (stackAt_spqrRecvCallee_split (s0.sp - 4992#64)
          (encodeToVecStackOf doReserveStackX) (by decide)).symm)
        (by sep_focus) ?_
      apply SepWPpLS.of_sepWP_ret_lscl; intro hcl
      dsimp only [spqrRecvPlacedProg, spqrRecvPlacedEntry, BitVec.ofNat_eq_ofNat] at hpcn ⊢
      rw [← MC.stepEvents_append]
      refine SepWP.focus_weaken
        (vecU8_sub_entails_header_buf A.repAlloc s0.sp 2096
          (PqRatchetState.encodeRaw
            { versionNegotiation := some vn, chain := some chain1.intoPb, inner := some (.v1 pb) }))
        (by sep_focus) ?_
      wp_pull_exists; rename_i cap_st ptr_st
      rw [← protoPqRatchetStateAt_eq_pqRatchetStatePBAt]
      refine SepWP.focus_weaken spqrRecvRoPlacedAt_expose_dropJumpTable (by sep_focus) ?_
      wp_pull_exists; rename_i P_ro
      wp_focus_pure; intro hP_ro
      rw [ret_48_split_6 ret]
      wp_pull_exists; rename_i r5 r4 r3 r2 r1 r0
      have hfold_ret := recv_ok_some_foldX A.repAlloc ret
        (PqRatchetState.encodeRaw
          { versionNegotiation := some vn, chain := some chain1.intoPb, inner := some (.v1 pb) })
        rawKey cap_st ptr_st cap_rk ptr_rk
      rw [← hok] at hfold_ret
      rcases htr_sn' with ⟨htr_sn_eq, hvregs_sn⟩
      dsimp only [Nat.reduceSub, BitVec.ofNat_eq_ofNat]
      refine seq_vm_lscl hcl (mid := lsmpl.base 270)
        (P_mid :=
          P_ro ∗
          optProtoInnerStateJumpTablePlacedAt ∗
          st.at A.repAlloc ∗
          msg.at A.repAlloc ∗
          recvResultExactKeyAt A.repAlloc ret ((spqrV1Recv F K).recv st.bytes msg.bytes) ∗
          A.pool lim (MC.stepEvents (evs0 ++ evs_into ++ evs_enc) st_cost) sn ∗
          stackAt (s0.sp - 4992#64) spqrRecvCalleeStackX ∗
          ((s0.sp - 4992#64) ↦₆₄ w0) ∗
          ((s0.sp - 4984#64) ↦₆₄ w1) ∗
          ((s0.sp - 4976#64) ↦₆₄ v2) ∗
          ((s0.sp - 4968#64) ↦₆₄ v3) ∗
          ((s0.sp - 4960#64) ↦₆₄ v4) ∗
          ((s0.sp - 4952#64) ↦₆₄ v5) ∗
          memRegion (s0.sp - 4944#64) 80 ∗
          ((s0.sp - 4864#64) ↦₆₄ w_in0) ∗
          words27SubAt s0.sp 4864 d_in ∗
          memRegion (s0.sp - 4640#64) 352 ∗
          memRegion (s0.sp - 4288#64) 88 ∗
          memRegion (s0.sp - 4200#64) 88 ∗
          ((s0.sp - 4112#64) ↦₆₄ cap_rk) ∗
          ((s0.sp - 4104#64) ↦₆₄ ptr_rk) ∗
          ((s0.sp - 4096#64) ↦₆₄ BitVec.ofNat 64 rawKey.length) ∗
          memRegion (s0.sp - 4088#64) 1032 ∗
          protoPqRatchetStateAt A.repAlloc (s0.sp - 3056#64)
            { versionNegotiation := some vn, chain := some chain1.intoPb, inner := some (.v1 pb) } ∗
          memRegion (s0.sp - 2704#64) 608 ∗
          ((s0.sp - 2096#64) ↦₆₄ cap_st) ∗
          ((s0.sp - 2088#64) ↦₆₄ ptr_st) ∗
          ((s0.sp - 2080#64) ↦₆₄ BitVec.ofNat 64
            (PqRatchetState.encodeRaw
              { versionNegotiation := some vn, chain := some chain1.intoPb, inner := some (.v1 pb) }).length) ∗
          ((s0.sp - 2072#64) ↦₆₄ cap_rk) ∗
          ((s0.sp - 2064#64) ↦₆₄ ptr_rk) ∗
          ((s0.sp - 2056#64) ↦₆₄ BitVec.ofNat 64 rawKey.length) ∗
          memRegion (s0.sp - 2048#64) 1952 ∗
          spqrRecvSavedRegs (s0.sp - 4992#64) s0)
        (Q := fun s3 =>
          s3.sp = s0.sp - 4992#64 ∧
          TraceVRegs s3 s0 ∧
          s3.readReg64 .x0 = s0.sp - 3056#64 ∧
          s3.readReg64 .x30 = (blkPl_329).base + 2380#64)
        ?_ ?_
      · dsimp only [words27SubAt, Nat.reduceSub, BitVec.ofNat_eq_ofNat]
        apply sepWP_seg_ls_vm
          (Q := (blkPC_329).rebase (blkPl_329).base (hooksException (Rust.withPanics ext)))
          blkLib_eq_329 (mid := lsmpl.base 270)
        intro _m_strip
        wp_steps 11
        refine SepWP.focus_weaken hfold_ret (by sep_focus) ?_
        refine ProofLib.SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
          fun _m_real _hnsp => ?_
        exact ProofLib.SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
          ⟨_hnsp.toVmPreserved (by simp only [wp_norm, arm64_norm]),
           Entails.of_eq (by sep_ac_rfl),
           by simp only [wp_norm, arm64_norm, *],
           ⟨by simp only [wp_norm, arm64_norm, *], by simp only [wp_norm, arm64_norm, *]⟩,
           by simp only [wp_norm, arm64_norm, *],
           by simp only [wp_norm, arm64_norm, *]⟩
      · intro s3 hpc3 hrun3 hcl3 hvm3 ⟨hsp3, htr3, hx0_3, hlr3⟩
        rw [← A.pool_transport lim (MC.stepEvents (evs0 ++ evs_into ++ evs_enc) st_cost) sn s3 hvm3]
        refine SepWP.focus_weaken
          (Entails.of_eq (stackAt_spqrRecvCallee_split (s0.sp - 4992#64) dropStack96 (by decide)))
          (by sep_focus) ?_
        have hdrop_st := subroutine_ok_withMemEq_of_lscl hC.dropPqRatchetState_ok hcl3
        simp only [withMemEq, dropProtoPqRatchetStatePlacedSpec] at hdrop_st
        dsimp only [spqrRecvPlacedProg, BitVec.ofNat_eq_ofNat] at hdrop_st
        wp_call hdrop_st
          (⟨s0.sp - 3056#64,
              { versionNegotiation := some vn, chain := some chain1.intoPb, inner := some (.v1 pb) }⟩,
            MC.stepEvents (evs0 ++ evs_into ++ evs_enc) st_cost)
        have hevs_st := ‹FreeOnlyEvs _›
        have hsp_eq_drop : stackAt s3.sp dropStack96 = stackAt (s0.sp - 4992#64) dropStack96 := by
          rw [hsp3]
        refine SepWP.focus_weaken (Entails.of_eq hsp_eq_drop) (by sep_focus) ?_
        refine SepWP.focus_weaken
          (Entails.of_eq (stackAt_spqrRecvCallee_split (s0.sp - 4992#64) dropStack96 (by decide)).symm)
          (by sep_focus) ?_
        wp_steps 1
        refine SepWP.focus_weaken hP_ro (by sep_focus) ?_
        have hjoin := ownFrame_join_4896_ok_2380 s0.sp w0 w1 v2 v3 v4 v5 w_in0 d_in
          cap_rk ptr_rk (BitVec.ofNat 64 rawKey.length)
          cap_st ptr_st
          (BitVec.ofNat 64
            (PqRatchetState.encodeRaw
              { versionNegotiation := some vn, chain := some chain1.intoPb, inner := some (.v1 pb) }).length)
          cap_rk ptr_rk (BitVec.ofNat 64 rawKey.length)
        dsimp only [words27SubAt, Nat.reduceSub, BitVec.ofNat_eq_ofNat] at hjoin ⊢
        unfold protoPqRatchetStateSize
        refine SepWP.focus_weaken hjoin (by sep_focus) ?_
        refine sepWP_spqrRecvPlacedPostOfEnv_of_post0 (spqrV1Recv_noPanic_of_recv_ok hok) ?_
        exact step_epilogue_placed_ofEnv A lim st_cost Env
          (evs0 ++ evs_into ++ evs_enc ++ freeOnlyWitness hevs_st)
          (hevs_done G_c1 evs_into evs_enc (freeOnlyWitness hevs_st) hevs_into hevs_enc hevs_st)
          (spqrV1Recv F K) ext st msg ret s0 _ _ R _ rfl
          (by simp only [spqrRecvPlacedEntry, arm64_norm, *])
          (by simp only [arm64_norm, *])
          (by simp only [arm64_norm, *])
          hs0_align
          (by
            rcases htr3 with ⟨htr3_eq, hvregs3⟩
            exact ⟨by simp only [wp_norm, arm64_norm, *], by simp only [wp_norm, arm64_norm, *]⟩)
          (by
            simp only [← MC.stepEvents_append, List.append_assoc, freeOnlyWitness, wp_norm,
              arm64_norm, *]
            sep_ac_rfl)

theorem step_v0_recvKey_ok_2184_placed {MC : AllocCostModel}
    {H_inner : V1InnerHeapPred} {A : RustCliAllocBudget MC} {lim : BudgetLimits}
    {F : ShaCompress} {K : MlKem}
    {ext : String → Option (State → State)}
    (st_cost : MC.σ) (evs0 : List AllocEvent)
    (hC : SpqrRecvPlacedContracts H_inner A lim F K ext)
    (st msg : VecArg) (ret : BitVec 64)
    (vn : VersionNegotiationPB) (pb : V1State)
    (chain1 : Chain) (rawKey : Bytes)
    (w0 w1 cap_rk ptr_rk : BitVec 64)
    (d880 d888 d896 u0 u1 u2 u3 u4 u5 e0 e1 e2 : BitVec 64)
    (henc_len :
      (PqRatchetState.encodeRaw
        { versionNegotiation := some vn, chain := some chain1.intoPb, inner := some (.v1 pb) }).length < 2 ^ 63)
    (hok : (spqrV1Recv F K).recv st.bytes msg.bytes =
      .ok (PqRatchetState.encodeRaw
        { versionNegotiation := some vn, chain := some chain1.intoPb, inner := some (.v1 pb) },
        some rawKey))
    (s0 s : State) (P R : SepProp)
    (hfits_into : ∀ gChain : ChainGhost,
      FitsEnv MC lim (MC.stepEvents evs0 st_cost)
        (ChainIntoPbAllocEnv ⟨s0.sp - 3008#64, s0.sp - 4288#64, gChain, chain1⟩))
    (hfits_enc : ∀ gChain evs_into,
      ChainIntoPbEnv ⟨s0.sp - 3008#64, s0.sp - 4288#64, gChain, chain1⟩ evs_into →
      FitsEnv MC lim (MC.stepEvents (evs0 ++ evs_into) st_cost)
        (PqRatchetStateEncodeToVecEnv
          { versionNegotiation := some vn, chain := some chain1.intoPb, inner := some (.v1 pb) }))
    (hevs_done : ∀ gChain evs_into evs_enc evs_drop,
      ChainIntoPbEnv ⟨s0.sp - 3008#64, s0.sp - 4288#64, gChain, chain1⟩ evs_into →
      PqRatchetStateEncodeToVecEnv
        { versionNegotiation := some vn, chain := some chain1.intoPb, inner := some (.v1 pb) } evs_enc →
      FreeOnlyEvs evs_drop →
      SpqrRecvEnv st msg (evs0 ++ evs_into ++ evs_enc ++ evs_drop))
    (hs0_align : s0.spAligned = true)
    (hpc : s.pc = spqrRecvPlacedEntry + 2184#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = s0.sp - 4992#64)
    (htr : TraceVRegs s s0)
    (hx19 : s.readReg64 .x19 = ret)
    (hx21 : s.readReg64 .x21 = s0.sp - 3056#64)
    (hx22 : s.readReg64 .x22 = s0.sp - 2096#64)
    (hP : P =
      spqrRecvRoPlacedAt ∗
      st.at A.repAlloc ∗
      msg.at A.repAlloc ∗
      memRegion ret 48 ∗
      A.pool lim (MC.stepEvents evs0 st_cost) s ∗
      stackAt (s0.sp - 4992#64) spqrRecvCalleeStackX ∗
      ((s0.sp - 4992#64) ↦₆₄ w0) ∗
      ((s0.sp - 4984#64) ↦₆₄ w1) ∗
      optVersionNegotiationPBTailAt A.repAlloc w0 w1 (s0.sp - 4976#64) (some vn) ∗
      memRegion (s0.sp - 4944#64) 80 ∗
      optProtoPqRatchetInnerAt A.repAlloc (s0.sp - 4864#64) (some (.v1 pb)) ∗
      memRegion (s0.sp - 4640#64) 352 ∗
      chainRepr A.repAlloc (s0.sp - 4288#64) chain1 ∗
      memRegion (s0.sp - 4200#64) 88 ∗
      ((s0.sp - 4112#64) ↦₆₄ d880) ∗
      ((s0.sp - 4104#64) ↦₆₄ d888) ∗
      ((s0.sp - 4096#64) ↦₆₄ d896) ∗
      memRegion (s0.sp - 4088#64) 1032 ∗
      ((s0.sp - 3056#64) ↦₆₄ u0) ∗
      ((s0.sp - 3048#64) ↦₆₄ u1) ∗
      ((s0.sp - 3040#64) ↦₆₄ u2) ∗
      ((s0.sp - 3032#64) ↦₆₄ u3) ∗
      ((s0.sp - 3024#64) ↦₆₄ u4) ∗
      ((s0.sp - 3016#64) ↦₆₄ u5) ∗
      memRegion (s0.sp - 3008#64) 80 ∗
      memRegion (s0.sp - 2928#64) 224 ∗
      memRegion (s0.sp - 2704#64) 608 ∗
      ((s0.sp - 2096#64) ↦₆₄ cap_rk) ∗
      ((s0.sp - 2088#64) ↦₆₄ ptr_rk) ∗
      ((s0.sp - 2080#64) ↦₆₄ BitVec.ofNat 64 rawKey.length) ∗
      vecU8Buf A.repAlloc cap_rk ptr_rk rawKey ∗
      ((s0.sp - 2072#64) ↦₆₄ e0) ∗
      ((s0.sp - 2064#64) ↦₆₄ e1) ∗
      ((s0.sp - 2056#64) ↦₆₄ e2) ∗
      memRegion (s0.sp - 2048#64) 1952 ∗
      spqrRecvSavedRegs (s0.sp - 4992#64) s0) :
    SepWPpLS (spqrRecvPlacedProg ext) (s0.readReg64 .x30) s P
      (spqrRecvPlacedPost A lim st_cost (spqrV1Recv F K) st msg ret s0 R)
      (spqrRecvBudgetPanicPost (spqrV1Recv F K) st msg s0 R) :=
  step_v0_recvKey_ok_2184_placed_ofEnv st_cost (SpqrRecvEnv st msg) evs0 hC
    st msg ret vn pb chain1 rawKey w0 w1 cap_rk ptr_rk
    d880 d888 d896 u0 u1 u2 u3 u4 u5 e0 e1 e2
    henc_len hok s0 s P R hfits_into hfits_enc hevs_done
    hs0_align hpc hrun hsp htr hx19 hx21 hx22 hP

end LibsignalBinary.Proofs.SpqrV1.Top.Recv.Part8PlacedBudget
