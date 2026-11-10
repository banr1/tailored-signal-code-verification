/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.Placed.BudgetVmSteps
public import LibsignalBinary.Proofs.SpqrV1.Top.Recv.DefsPlacedBudget
public import LibsignalBinary.Proofs.SpqrV1.Top.Recv.Part2PlacedBudget
public import LibsignalBinary.Proofs.SpqrV1.Top.Recv.Part3PlacedBudget
public import LibsignalBinary.Proofs.SpqrV1.Top.Recv.V1Ratchet1PlacedBudget
public import LibsignalBinary.Proofs.SpqrV1.Top.Recv.V1Ratchet3
public import LibsignalBinary.Proofs.SpqrV1.Top.Recv.V1Ratchet3Placed
import LibsignalBinary.Proofs.SpqrV1.Prost.EncodeToVec.AllocReservePhase
import LibsignalBinary.Proofs.SpqrV1.Prost.MessageEncode.Base
import LibsignalBinary.Proofs.SpqrV1.Top.Recv.Part3
import LibsignalBinary.Proofs.SpqrV1.Top.Recv.Part3Placed
import LibsignalBinary.Proofs.SpqrV1.Top.Recv.Part5
import LibsignalBinary.Proofs.SpqrV1.Top.Recv.Part5Placed
import LibsignalBinary.Proofs.SpqrV1.Top.Recv.Part6
import LibsignalBinary.Proofs.SpqrV1.Top.Recv.V1Ratchet1
import LibsignalBinary.Proofs.SpqrV1.Top.Recv.V1Ratchet1Placed
import LibsignalBinary.Proofs.SpqrV1.Top.Recv.V1Ratchet2
import LibsignalBinary.Proofs.SpqrV1.Top.Recv.V1Ratchet2Placed
import LibsignalBinary.Proofs.SpqrV1.Top.Send.Pure
import ProofLib.SepLogic.WPp
meta import LibsignalBinary.Proofs.Common.SharedHelpers -- shake: keep
meta import LibsignalBinary.Proofs.Placed.BudgetVmSteps -- shake: keep

/-!
# Budget-Threaded Relocatable V1 `<Message>::deserialize` & `<States>::from_pb` (`+1532..+1736`)

Envelope-parametric and default `SpqrRecvEnv` steppers for `<Message>::deserialize` (`+1532..+1636`)
and `<States>::from_pb` (`+1636..+1736`) in `spqr::recv` (Block `329`).
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 400000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

namespace LibsignalBinary.Proofs.SpqrV1.Top.Recv.V1Ratchet3PlacedBudgetAux

open Arm64 ProofLib ProofLib.ProgramReflection
open CryptoGames.LibsignalSession (ShaCompress)
open CryptoVerification
  (LibsignalCodeLoaded LibsignalPlacement lsmpl lsρ sepWP_seq_lscl)
open CryptoVerification.LibsignalSpqrV1
  (Error Message MlKem MsgPreamble PqRatchetState SpqrRecvModel States
   V1State msgPreamble recvResultExactKeyAt spqrAuthApi spqrDecodeState spqrPolyApi spqrV1Recv)
open CryptoVerification.LibsignalTripleRatchet (VecArg framelessMemcpySpec)
open CryptoVerification.LibsignalTripleRatchetRepr (noneCap)
open CryptoVerification.SpqrV1.Drop
  (chunkedStatesAt optProtoInnerStateAt optProtoInnerStateSize)
open CryptoVerification.SpqrV1.Prost.EncodeToVec (extractLsb_hi_append64 extractLsb_lo_append64)
open CryptoVerification.SpqrV1.Prost.MessageMerge (v1StateJumpTablesPlacedAt)
open CryptoVerification.SpqrV1.ProtoRepr (optChainPBAt)
open CryptoVerification.SpqrV1.States.FromPb
  (StatesFromPbGhost resultChunkedStatesAt spqrErrorByte statesFromPbStackX v1StatePtsBound)
open CryptoVerification.SpqrV1.States.IntoPb (StatesIntoPbGhost)
open CryptoVerification.SpqrV1.States.Leaves (relocatedHeap)
open CryptoVerification.SpqrV1.States.Recv (StatesRecvGhost)
open CryptoVerification.SpqrV1.Top.DecodeState
  (DecodeStateGhost TraceVRegs V1InnerHeapPred optVersionNegotiationPBTailAt)
open CryptoVerification.SpqrV1.Top.InitInner (InitInnerGhost)
open CryptoVerification.SpqrV1.Top.MessageDeserialize
  (MessageDeserializeCall messageDeserializeStackX messageResultAt)
open CryptoVerification.SpqrV1.Top.MessageSerialize (messageAt)
open CryptoVerification.SpqrV1.Top.Send (chunkedStatesTail920At chunkedStatesWord0)
open CryptoVerification.SpqrV1.Top.Recv
  (MsgRemValid SepWPpLS chunkedStatesAt_entails_reloc_words hsp_add_544_eq hsp_add_560_eq
   memRegion_1168_split_statesFromPb memRegion_136_join_fp_spill memRegion_24_words3
   memRegion_4064_join_1968_928 memRegion_4064_split_2096 memRegion_4416_join_statesFromPb_err
   memRegion_928_split_header32_body896 memRegion_split_4288_for_1532 messageAt_expose_bytes39
   messageErrorAt_sub3056_expose msgRemFrame msg_expose_rem_bound msg_unexpose_rem
   reassemble_chunkedStatesAt_words reassemble_src_928_after_memcpy recv_chunkedStatesWord0_add_one_beq_zero
   recv_err_byte_foldX resultChunkedStatesAt_err_expose resultChunkedStatesAt_panic_false
   ret_48_split sp_sub_4992_aligned spqrErrorByte_eq_zero_iff spqrRecvCalleeStackX
   spqrRecvPlacedEntry spqrRecvPlacedProg spqrRecvRoPlacedAt spqrRecvSavedRegs
   spqrV1Recv_v1_msgDeserialize_err spqrV1Recv_v1_statesFromPb_err stackAt_spqrRecvCallee_split
   statesFromPbJumpTablePlacedAt statesFromPb_noneCap_add_one_beq_zero
   statesIntoPbJumpTablePlacedAt statesRecvRoPlacedAt tag_zeroExtend_beq_255_false
   tag_zeroExtend_sub_255_beq_0_false tag_zeroExtend_sub_255_bne_0_true)
open CryptoVerification.SpqrV1.Top.Recv.Placed (blkPC_329 blkPl_329)
open LibsignalBinary.Heap
  (AllocCostModel AllocEvent BudgetLimits FitsEnv FreeOnlyEvs RustCliAllocBudget VmPreserved)
open LibsignalBinary.Proofs.SpqrV1.States.FromPb.DefsBudget (StatesFromPbEnv)
open LibsignalBinary.Proofs.SpqrV1.Top.MessageDeserialize.DefsBudget (messageDeserializeSpecX)
open LibsignalBinary.Proofs.SpqrV1.Top.Recv.DefsPlacedBudget
  (SpqrRecvPlacedContracts SpqrRecvPlacedContractsOfEnv statesFromPbPlacedSpecXOfEnv)
open LibsignalBinary.Proofs.SpqrV1.Top.Recv.Part1PlacedBudget
  (SpqrRecvEnv sepWP_spqrRecvPlacedPostOfEnv_of_post0 spqrRecvBudgetPanicPost
   spqrRecvPlacedPost spqrRecvPlacedPost0 spqrRecvPlacedPost0OfEnv spqrRecvPlacedPostOfEnv)
open LibsignalBinary.Proofs.SpqrV1.Top.Recv.Part2PlacedBudget
  (SpqrRecvDropContractsBudget SpqrRecvEnv.append_freeOnly seq_vm_clean seq_vm_lscl)
open LibsignalBinary.Proofs.SpqrV1.Top.Recv.V1Ratchet1PlacedBudget
  (step_drop_vn_chain_2500_placed_ofEnv step_msgDeserialize_err_2060_placed_ofEnv
   step_msg_relocate_1568_placed)
open LibsignalBinary.Proofs.TripleRatchet.Wire.NewPureBudget (framelessMemcpyBudgetSpec)

variable [LibsignalPlacement]

attribute [local irreducible] Program.fetch Program.externAt? Program.fnAddr Program.fnOff Obj.lookup
attribute [local arm64_norm, local wp_norm] bv_sub_add_lit BitVec.toNat_zero
  RustCliAllocBudget.pool_setPC RustCliAllocBudget.pool_advancePC
  RustCliAllocBudget.pool_setPState RustCliAllocBudget.pool_writeReg64
  RustCliAllocBudget.pool_writeReg32 RustCliAllocBudget.pool_writeReg
attribute [local simp, local arm64_norm, local wp_norm, local arm64_norm ↓, local wp_norm ↓]
  extractLsb_lo_append64 extractLsb_hi_append64
  hsp_add_544_eq hsp_add_560_eq
attribute [local simp, local arm64_norm, local wp_norm]
  recv_chunkedStatesWord0_add_one_beq_zero statesFromPb_noneCap_add_one_beq_zero
  tag_zeroExtend_beq_255_false tag_zeroExtend_sub_255_beq_0_false tag_zeroExtend_sub_255_bne_0_true

theorem toDropContractsBudget {MC : AllocCostModel} {H_inner : V1InnerHeapPred}
    {A : RustCliAllocBudget MC} {lim : BudgetLimits} {F : ShaCompress} {K : MlKem}
    {DecodePreEnv DecodePostEnv : DecodeStateGhost → List AllocEvent → Prop}
    {InitEnv : InitInnerGhost → List AllocEvent → Prop}
    {FromPbEnv : V1State → List AllocEvent → Prop}
    {RecvEnv : StatesRecvGhost F → List AllocEvent → Prop}
    {IntoPbEnv : StatesIntoPbGhost F → List AllocEvent → Prop}
    {ext : String → Option (State → State)}
    (hC : SpqrRecvPlacedContractsOfEnv H_inner A lim F K
      DecodePreEnv DecodePostEnv InitEnv FromPbEnv RecvEnv IntoPbEnv ext) :
    SpqrRecvDropContractsBudget A lim F ext :=
  { dealloc_ok := hC.dealloc_ok
    dropEpochSlice_ok := hC.dropEpochSlice_ok
    dropOptProtoInnerState_ok := hC.dropOptProtoInnerState_ok
    dropOptProtoChain_ok := hC.dropOptProtoChain_ok
    dropChain_ok := hC.dropChain_ok
    dropPqRatchetState_ok := hC.dropPqRatchetState_ok
    dropStates_ok := hC.dropStates_ok }

theorem frame_pure_pre {Q : Prop} {P R F : SepProp} (hQ : Q) (heq : P = R ∗ F) :
    P ⊢ (⌜Q⌝ ∗ R) ∗ F := by
  rw [heq, sepConj_assoc]; exact Entails.pure_right hQ (Entails.refl _)

theorem onPanic_false_budget {M : SpqrRecvModel} {st msg : VecArg} (s sm : State) :
    (⌜False⌝ : SepProp) ⊢ ⌜M.recvPanics st.bytes msg.bytes ∧ s.trace <+: sm.trace⌝ ∗ anyHeap :=
  Entails.trans (Entails.of_eq (sepConj_emp ⌜False⌝).symm)
    (Entails.pure_left fun h => False.elim h)

omit [LibsignalPlacement] in
theorem traceVRegs_trans {s0 s1 s2 : State}
    (h1 : TraceVRegs s2 s1) (h0 : TraceVRegs s1 s0) : TraceVRegs s2 s0 :=
  ⟨h1.1.trans h0.1, h1.2.trans h0.2⟩

/-! ## 1. `<Message>::deserialize` Call, Error Path (`+2060`), and Relocation (`+1568..+1636`) -/

/-- Envelope-parametric budget-threaded `<Message>::deserialize` step (`+1532 .. +1636`, `b.eq
    +2060` on error). -/
theorem step_msgDeserialize_1532_placed_ofEnv {MC : AllocCostModel}
    {H_inner : V1InnerHeapPred} {A : RustCliAllocBudget MC} {lim : BudgetLimits} {st_cost : MC.σ}
    {F : ShaCompress} {K : MlKem}
    {DecodePreEnv DecodePostEnv : DecodeStateGhost → List AllocEvent → Prop}
    {InitEnv : InitInnerGhost → List AllocEvent → Prop}
    {FromPbEnv : V1State → List AllocEvent → Prop}
    {RecvEnv : StatesRecvGhost F → List AllocEvent → Prop}
    {IntoPbEnv : StatesIntoPbGhost F → List AllocEvent → Prop}
    {ext : String → Option (State → State)}
    (Env : List AllocEvent → Prop) (evs0 : List AllocEvent)
    (hevs_free : ∀ evs_d, FreeOnlyEvs evs_d → Env (evs0 ++ evs_d))
    (hC : SpqrRecvPlacedContractsOfEnv H_inner A lim F K
      DecodePreEnv DecodePostEnv InitEnv FromPbEnv RecvEnv IntoPbEnv ext)
    (st msg : VecArg) (ret : BitVec 64)
    (pre : MsgPreamble) (remPtr : BitVec 64) (pre_pb : PqRatchetState) (pb : V1State)
    (w0 w1 : BitVec 64)
    (hpre : msgPreamble msg.bytes = .ok pre)
    (hvalid : MsgRemValid msg remPtr pre.remaining)
    (hdec : spqrDecodeState st.bytes = .ok pre_pb)
    (hinner : pre_pb.inner = some (.v1 pb))
    (hmv : pre.version = 1#8)
    (hmin : ∀ vn, pre_pb.versionNegotiation = some vn → ¬(1#8 < vn.minVersion.truncate 8))
    (s0 s : State) (P R : SepProp)
    (hs0_align : s0.spAligned = true)
    (hpc : s.pc = spqrRecvPlacedEntry + 1532#64)
    (hrun : s.status = .Running) (hsp : s.sp = s0.sp - 4992#64) (htr : TraceVRegs s s0)
    (hx19 : s.readReg64 .x19 = ret) (hx20 : s.readReg64 .x20 = w0)
    (hx21 : s.readReg64 .x21 = pre.index.zeroExtend 64) (hx22 : s.readReg64 .x22 = pre.epoch)
    (hx23 : s.readReg64 .x23 = BitVec.ofNat 64 pre.remaining.length) (hx24 : s.readReg64 .x24 = remPtr)
    (hx26 : s.readReg64 .x26 = 0#64) (hx27 : s.readReg64 .x27 = s0.sp - 3056#64)
    (hx28 : s.readReg64 .x28 = s0.sp - 4288#64) (hx29 : s.readReg64 .x29 = s0.sp - 96#64)
    (hP : P =
      spqrRecvRoPlacedAt ∗ st.at A.repAlloc ∗ msg.at A.repAlloc ∗ memRegion ret 48 ∗
      A.pool lim (MC.stepEvents evs0 st_cost) s ∗
      stackAt (s0.sp - 4992#64) spqrRecvCalleeStackX ∗ memRegion (s0.sp - 4992#64) 352 ∗
      ((s0.sp - 4640#64) ↦₆₄ w0) ∗ ((s0.sp - 4632#64) ↦₆₄ w1) ∗
      optVersionNegotiationPBTailAt A.repAlloc w0 w1 (s0.sp - 4624#64) pre_pb.versionNegotiation ∗
      optChainPBAt A.repAlloc (s0.sp - 4592#64) pre_pb.chain ∗
      optProtoInnerStateAt A.repAlloc (s0.sp - 4512#64) pb.innerState ∗
      memRegion (s0.sp - 4288#64) 4192 ∗ spqrRecvSavedRegs (s0.sp - 4992#64) s0)
    (hok_tail : ∀ (evs_md : List AllocEvent) (sckaMsg : Message spqrPolyApi) (s1 : State) (P1 : SepProp),
      FreeOnlyEvs evs_md →
      Message.deserialize spqrPolyApi pre.epoch pre.remaining = .ok sckaMsg →
      s1.pc = spqrRecvPlacedEntry + 1636#64 →
      s1.status = .Running → s1.sp = s0.sp - 4992#64 → TraceVRegs s1 s0 →
      s1.readReg64 .x0 = s0.sp - 4512#64 → s1.readReg64 .x8 = s0.sp - 2096#64 →
      s1.readReg64 .x19 = ret → s1.readReg64 .x20 = w0 →
      s1.readReg64 .x21 = pre.index.zeroExtend 64 → s1.readReg64 .x22 = pre.epoch →
      s1.readReg64 .x24 = s0.sp - 2096#64 → s1.readReg64 .x25 = s0.sp - 4640#64 →
      s1.readReg64 .x26 = 0#64 → s1.readReg64 .x27 = s0.sp - 3056#64 →
      s1.readReg64 .x28 = s0.sp - 4288#64 → s1.readReg64 .x29 = s0.sp - 96#64 →
      P1 = (spqrRecvRoPlacedAt ∗ st.at A.repAlloc ∗ msg.at A.repAlloc ∗ memRegion ret 48 ∗
        A.pool lim (MC.stepEvents (evs0 ++ evs_md) st_cost) s1 ∗
        stackAt (s0.sp - 4992#64) spqrRecvCalleeStackX ∗ memRegion (s0.sp - 4992#64) 352 ∗
        ((s0.sp - 4640#64) ↦₆₄ w0) ∗ ((s0.sp - 4632#64) ↦₆₄ w1) ∗
        optVersionNegotiationPBTailAt A.repAlloc w0 w1 (s0.sp - 4624#64) pre_pb.versionNegotiation ∗
        optChainPBAt A.repAlloc (s0.sp - 4592#64) pre_pb.chain ∗
        optProtoInnerStateAt A.repAlloc (s0.sp - 4512#64) pb.innerState ∗
        memRegion (s0.sp - 4288#64) 176 ∗ messageAt spqrPolyApi (s0.sp - 4112#64) sckaMsg ∗
        memRegion (s0.sp - 4064#64) 3968 ∗ spqrRecvSavedRegs (s0.sp - 4992#64) s0) →
      SepWPpLS (spqrRecvPlacedProg ext) (s0.readReg64 .x30) s1 P1
        (spqrRecvPlacedPostOfEnv A lim st_cost Env (spqrV1Recv F K) st msg ret s0 R)
        (spqrRecvBudgetPanicPost (spqrV1Recv F K) st msg s0 R)) :
    SepWPpLS (spqrRecvPlacedProg ext) (s0.readReg64 .x30) s P
      (spqrRecvPlacedPostOfEnv A lim st_cost Env (spqrV1Recv F K) st msg ret s0 R)
      (spqrRecvBudgetPanicPost (spqrV1Recv F K) st msg s0 R) := by
  have hmd_call := hC.messageDeserialize_ok
  have hfsp_align : ((s0.sp - 4992#64) &&& 15#64 == 0#64) = true :=
    sp_sub_4992_aligned s0 hs0_align
  subst hP
  refine SepWPpLS.focus_weaken (msg_expose_rem_bound A.repAlloc msg remPtr pre.remaining hvalid) (by sep_focus) ?_
  refine SepWPpLS.focus_pure (by sep_focus) ?_; intro hrem_lt
  refine SepWPpLS.focus_weaken (memRegion_split_4288_for_1532 s0.sp) (by sep_focus) ?_
  apply SepWPpLS.of_sepWP (mid := lsmpl.base 351)
  let P_pre_md : SepProp :=
    (remPtr ↦ₛ pre.remaining) ∗
    msgRemFrame A.repAlloc msg remPtr pre.remaining ∗
    memRegion (s0.sp - 4288#64) 1232 ∗ memRegion (s0.sp - 3056#64) 48 ∗ memRegion (s0.sp - 3008#64) 2912 ∗
    spqrRecvRoPlacedAt ∗ st.at A.repAlloc ∗ memRegion ret 48 ∗
    A.pool lim (MC.stepEvents evs0 st_cost) s ∗
    stackAt (s0.sp - 4992#64) spqrRecvCalleeStackX ∗ memRegion (s0.sp - 4992#64) 352 ∗
    ((s0.sp - 4640#64) ↦₆₄ w0) ∗ ((s0.sp - 4632#64) ↦₆₄ w1) ∗
    optVersionNegotiationPBTailAt A.repAlloc w0 w1 (s0.sp - 4624#64) pre_pb.versionNegotiation ∗
    optChainPBAt A.repAlloc (s0.sp - 4592#64) pre_pb.chain ∗
    optProtoInnerStateAt A.repAlloc (s0.sp - 4512#64) pb.innerState ∗
    spqrRecvSavedRegs (s0.sp - 4992#64) s0
  dsimp only [spqrRecvPlacedProg, spqrRecvPlacedEntry, BitVec.ofNat_eq_ofNat] at hpc ⊢
  refine seq_vm_clean (mid := lsmpl.base 351) (P_mid := P_pre_md)
    (Q := fun sc =>
      sc.sp = s0.sp - 4992#64 ∧
      TraceVRegs sc s ∧
      sc.readReg64 .x0 = s0.sp - 3056#64 ∧
      sc.readReg64 .x1 = pre.epoch ∧
      sc.readReg64 .x2 = remPtr ∧
      sc.readReg64 .x3 = BitVec.ofNat 64 pre.remaining.length ∧
      sc.readReg64 .x19 = s.readReg64 .x19 ∧
      sc.readReg64 .x20 = s.readReg64 .x20 ∧
      sc.readReg64 .x21 = s.readReg64 .x21 ∧
      sc.readReg64 .x22 = pre.epoch ∧
      sc.readReg64 .x23 = BitVec.ofNat 64 pre.remaining.length ∧
      sc.readReg64 .x24 = remPtr ∧
      sc.readReg64 .x25 = s0.sp - 4640#64 ∧
      sc.readReg64 .x26 = s.readReg64 .x26 ∧
      sc.readReg64 .x27 = s.readReg64 .x27 ∧
      sc.readReg64 .x28 = s.readReg64 .x28 ∧
      sc.readReg64 .x29 = s.readReg64 .x29 ∧
      sc.readReg64 .x30 = spqrRecvPlacedEntry + 1556#64) ?_ ?_
  · by_vm_steps (
      wp_steps
      refine ProofLib.SepWP.done (by simp only [wp_norm, arm64_norm, *])
        (by simp only [wp_norm, arm64_norm, *])
        ⟨by simp only [wp_norm, arm64_norm],
         Entails.of_eq (by dsimp only [P_pre_md]; sep_ac_rfl), ?_⟩
      refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
      all_goals first | rfl | simp only [spqrRecvPlacedEntry, wp_norm, arm64_norm, *]
    )
  · intro sc hpc_sc hrun_sc hvm_sc ⟨hsp_sc, htr_sc, hx0_sc, hx1_sc, hx2_sc, hx3_sc,
      hx19_sc, hx20_sc, hx21_sc, hx22_sc, hx23_sc, hx24_sc, hx25_sc, hx26_sc, hx27_sc, hx28_sc, hx29_sc, hx30_sc⟩
    apply ProofLib.SepWP.done hpc_sc hrun_sc
    dsimp only [P_pre_md]
    rw [← A.pool_transport lim (MC.stepEvents evs0 st_cost) s sc hvm_sc]
    refine SepWPpLS.focus_weaken
      (Entails.of_eq (stackAt_spqrRecvCallee_split (s0.sp - 4992#64) messageDeserializeStackX (by decide)))
      (by sep_focus) ?_
    refine LibsignalBinary.Proofs.SpqrV1.Top.Recv.Part3PlacedBudget.SepWPpLS.call_lscro hmd_call
      ((⟨s0.sp - 3056#64, pre.epoch, remPtr, pre.remaining⟩ : MessageDeserializeCall),
        MC.stepEvents evs0 st_cost)
      hpc_sc hrun_sc
      (by simp only [State.spAligned, hsp_sc]; exact hfsp_align)
      hx30_sc (by rw [htr_sc.1, htr.1]) (fun sm => onPanic_false_budget _ sm) (fun _ _ => rfl)
      (by
        dsimp only [messageDeserializeSpecX]
        refine frame_pure_pre ⟨hx0_sc, hx1_sc, hx2_sc, hx3_sc, hrem_lt⟩ (by rw [hsp_sc]; sep_focus))
      ?_
    intro sm hpcm hrunm hspm hcsm
    rcases hcsm with ⟨hx19_c, hx20_c, hx21_c, hx22_c, hx23_c, hx24_c, hx25_c, hx26_c, hx27_c, hx28_c, hxfp_c, hvregs_c⟩
    dsimp only [messageDeserializeSpecX]
    simp only [sepExists_sepConj_left, sepConj_assoc]
    apply SepWPpLS.exists_elim; intro evs_md
    refine SepWPpLS.focus_pure (by sep_focus) ?_; rintro ⟨htr_sm, hevs_md⟩
    have htr_sm' : TraceVRegs sm s0 := ⟨by rw [htr_sm, htr_sc.1, htr.1], by rw [hvregs_c, htr_sc.2, htr.2]⟩
    have hspm' : sm.sp = s0.sp - 4992#64 := by rw [hspm, hsp_sc]
    have hx19_sm : sm.readReg64 .x19 = ret := by rw [hx19_c, hx19_sc, hx19]
    have hx20_sm : sm.readReg64 .x20 = w0 := by rw [hx20_c, hx20_sc, hx20]
    have hx21_sm : sm.readReg64 .x21 = pre.index.zeroExtend 64 := by rw [hx21_c, hx21_sc, hx21]
    have hx22_sm : sm.readReg64 .x22 = pre.epoch := by rw [hx22_c, hx22_sc]
    have hx23_sm : sm.readReg64 .x23 = BitVec.ofNat 64 pre.remaining.length := by rw [hx23_c, hx23_sc]
    have hx24_sm : sm.readReg64 .x24 = remPtr := by rw [hx24_c, hx24_sc]
    have hx25_sm : sm.readReg64 .x25 = s0.sp - 4640#64 := by rw [hx25_c, hx25_sc]
    have hx26_sm : sm.readReg64 .x26 = 0#64 := by rw [hx26_c, hx26_sc, hx26]
    have hx27_sm : sm.readReg64 .x27 = s0.sp - 3056#64 := by rw [hx27_c, hx27_sc, hx27]
    have hx28_sm : sm.readReg64 .x28 = s0.sp - 4288#64 := by rw [hx28_c, hx28_sc, hx28]
    have hx29_sm : sm.readReg64 .x29 = s0.sp - 96#64 := by
      change sm.readReg64 Reg.fp = s0.sp - 96#64
      rw [hxfp_c]; exact hx29_sc.trans hx29
    have hsp_eq := congrArg (stackAt · messageDeserializeStackX) (hspm.symm.trans hspm')
    refine SepWPpLS.focus_weaken (Entails.of_eq hsp_eq) (by sep_focus) ?_
    refine SepWPpLS.focus_weaken
      (Entails.of_eq (stackAt_spqrRecvCallee_split (s0.sp - 4992#64) messageDeserializeStackX (by decide)).symm)
      (by sep_focus) ?_
    refine SepWPpLS.focus_weaken (msg_unexpose_rem A.repAlloc msg remPtr pre.remaining) (by sep_focus) ?_
    rw [← MC.stepEvents_append]
    cases hmd : Message.deserialize spqrPolyApi pre.epoch pre.remaining with
    | error err =>
      dsimp only [messageResultAt]
      apply SepWPpLS.of_sepWP_ret_lscl; intro hcl
      refine SepWP.focus_weaken (messageErrorAt_sub3056_expose s0.sp err) (by sep_focus) ?_
      wp_pull_exists; rename_i q0_err w2_err
      wp_focus_pure; intro htag_err
      let Rest_err : SepProp :=
        memRegion (s0.sp - 3056#64) 8 ∗ memRegion (s0.sp - 3047#64) 7 ∗
        ((s0.sp - 3040#64) ↦₁₂₈ q0_err) ∗ ((s0.sp - 3024#64) ↦₆₄ w2_err) ∗
        memRegion (s0.sp - 3016#64) 8 ∗ msg.at A.repAlloc ∗
        stackAt (s0.sp - 4992#64) spqrRecvCalleeStackX ∗
        A.pool lim (MC.stepEvents (evs0 ++ evs_md) st_cost) sm ∗
        memRegion (s0.sp - 4288#64) 1232 ∗ memRegion (s0.sp - 3008#64) 2912 ∗
        spqrRecvRoPlacedAt ∗ st.at A.repAlloc ∗ memRegion ret 48 ∗ memRegion (s0.sp - 4992#64) 352 ∗
        ((s0.sp - 4640#64) ↦₆₄ w0) ∗ ((s0.sp - 4632#64) ↦₆₄ w1) ∗
        optVersionNegotiationPBTailAt A.repAlloc w0 w1 (s0.sp - 4624#64) pre_pb.versionNegotiation ∗
        optChainPBAt A.repAlloc (s0.sp - 4592#64) pre_pb.chain ∗
        optProtoInnerStateAt A.repAlloc (s0.sp - 4512#64) pb.innerState ∗
        spqrRecvSavedRegs (s0.sp - 4992#64) s0
      refine SepWP.weaken_pre
        (Entails.of_eq (show _ = ((s0.sp - 3048#64) ↦₈ 0xff#8) ∗ Rest_err by dsimp only [Rest_err]; ac_rfl)) ?_
      dsimp only [spqrRecvPlacedProg, spqrRecvPlacedEntry, BitVec.ofNat_eq_ofNat] at hpcm ⊢
      refine seq_vm_lscl (mid := (blkPl_329).base + 2060#64) hcl
        (P_mid := ((s0.sp - 3048#64) ↦₈ 0xff#8) ∗ Rest_err)
        (Q := fun s_err =>
          s_err.sp = s0.sp - 4992#64 ∧
          s_err.readReg64 .x19 = sm.readReg64 .x19 ∧
          s_err.readReg64 .x25 = sm.readReg64 .x25 ∧
          s_err.readReg64 .x26 = sm.readReg64 .x26 ∧
          TraceVRegs s_err sm) ?_ ?_
      · by_vm_steps (
          wp_steps
          refine ProofLib.SepWP.done (by simp only [wp_norm, arm64_norm, *])
            (by simp only [wp_norm, arm64_norm, *])
            ⟨by simp only [wp_norm, arm64_norm],
             Entails.of_eq (by sep_ac_rfl),
             by simp only [wp_norm, arm64_norm, *],
             by simp only [wp_norm, arm64_norm, *],
             by simp only [wp_norm, arm64_norm, *],
             by simp only [wp_norm, arm64_norm, *],
             by simp only [wp_norm, arm64_norm, *]⟩
        )
      · intro s_err hpc_err hrun_err hcl_err hvm_err ⟨hsp_err, hx19_err, hx25_err, hx26_err, htr_err⟩
        dsimp only [Rest_err]
        rw [← A.pool_transport lim (MC.stepEvents (evs0 ++ evs_md) st_cost) sm s_err hvm_err]
        refine sepWP_spqrRecvPlacedPostOfEnv_of_post0
          (spqrV1Recv_v1_msgDeserialize_err F K hpre hdec hinner hmv hmin hmd).2 ?_
        exact step_msgDeserialize_err_2060_placed_ofEnv A lim st_cost Env (evs0 ++ evs_md)
          (fun evs_d hd => by
            rw [List.append_assoc]
            exact hevs_free (evs_md ++ evs_d) (FreeOnlyEvs.append hevs_md hd))
          F K ext (toDropContractsBudget hC) st msg ret
          pre pre_pb pb w0 w1 err q0_err w2_err hpre hdec hinner hmv hmin hmd htag_err
          s0 s_err _ R _ rfl hs0_align hpc_err hrun_err hsp_err (traceVRegs_trans htr_err htr_sm')
          (hx19_err.trans hx19_sm) (hx25_err.trans hx25_sm) (hx26_err.trans hx26_sm)
          (by ac_rfl) hcl_err
    | ok sckaMsg =>
      dsimp only [messageResultAt]
      have hexp_msg := messageAt_expose_bytes39 spqrPolyApi (s0.sp - 3056#64) sckaMsg
      rw [bv_sub_add_lit s0.sp 3056 8, bv_sub_add_lit s0.sp 3056 9] at hexp_msg
      simp only [Nat.reduceSub, BitVec.ofNat_eq_ofNat] at hexp_msg
      let s0_1636 := s0.writeReg64 .x30 (spqrRecvPlacedEntry + 1636#64)
      have hs0_1636_sp : s0_1636.sp = s0.sp := rfl
      have hs0_1636_align : s0_1636.spAligned = true := hs0_align
      apply SepWPpLS.of_sepWP (mid := spqrRecvPlacedEntry + 1636#64)
      refine SepWP.focus_weaken hexp_msg (by sep_focus) ?_
      wp_pull_exists; rename_i tag bs39
      wp_focus_pure; rintro ⟨htag_ne, hbs39, hfold_msg⟩
      have htrunc : ((tag.zeroExtend 32).zeroExtend 64).truncate 8 = tag := by
        revert tag; bv_kernel
      let F_rest : SepProp :=
        spqrRecvRoPlacedAt ∗ st.at A.repAlloc ∗ msg.at A.repAlloc ∗ memRegion ret 48 ∗
        A.pool lim (MC.stepEvents (evs0 ++ evs_md) st_cost) sm ∗
        stackAt (s0.sp - 4992#64) spqrRecvCalleeStackX ∗ memRegion (s0.sp - 4992#64) 352 ∗
        ((s0.sp - 4640#64) ↦₆₄ w0) ∗ ((s0.sp - 4632#64) ↦₆₄ w1) ∗
        optVersionNegotiationPBTailAt A.repAlloc w0 w1 (s0.sp - 4624#64) pre_pb.versionNegotiation ∗
        optChainPBAt A.repAlloc (s0.sp - 4592#64) pre_pb.chain ∗
        optProtoInnerStateAt A.repAlloc (s0.sp - 4512#64) pb.innerState ∗
        spqrRecvSavedRegs (s0.sp - 4992#64) s0
      let Rest_1556 : SepProp :=
        memRegion (s0.sp - 4288#64) 1232 ∗ ((s0.sp - 3056#64) ↦₆₄ sckaMsg.epoch) ∗
        ((s0.sp - 3047#64) ↦ₛ bs39) ∗ memRegion (s0.sp - 3008#64) 2912 ∗ F_rest
      refine SepWP.weaken_pre
        (Entails.of_eq (show _ = ((s0.sp - 3048#64) ↦₈ tag) ∗ Rest_1556 by dsimp only [Rest_1556, F_rest]; ac_rfl)) ?_
      dsimp only [spqrRecvPlacedProg, spqrRecvPlacedEntry, BitVec.ofNat_eq_ofNat] at hpcm ⊢
      refine seq_vm_clean (mid := (blkPl_329).base + 1568#64)
        (P_mid := ((s0.sp - 3048#64) ↦₈ tag) ∗ Rest_1556)
        (Q := fun s_ok =>
          s_ok.sp = s0.sp - 4992#64 ∧
          TraceVRegs s_ok sm ∧
          (s_ok.readReg64 .x8).truncate 8 = tag ∧
          s_ok.readReg64 .x19 = sm.readReg64 .x19 ∧
          s_ok.readReg64 .x20 = sm.readReg64 .x20 ∧
          s_ok.readReg64 .x21 = sm.readReg64 .x21 ∧
          s_ok.readReg64 .x22 = sm.readReg64 .x22 ∧
          s_ok.readReg64 .x25 = sm.readReg64 .x25 ∧
          s_ok.readReg64 .x26 = sm.readReg64 .x26 ∧
          s_ok.readReg64 .x27 = sm.readReg64 .x27 ∧
          s_ok.readReg64 .x28 = sm.readReg64 .x28 ∧
          s_ok.readReg64 .x29 = sm.readReg64 .x29) ?_ ?_
      · by_vm_steps (
          wp_steps
          refine ProofLib.SepWP.done (by simp only [wp_norm, arm64_norm, *])
            (by simp only [wp_norm, arm64_norm, *])
            ⟨by simp only [wp_norm, arm64_norm],
             Entails.of_eq (by sep_ac_rfl), ?_⟩
          refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
          all_goals first | rfl | simp only [wp_norm, arm64_norm, *]
        )
      · intro s_ok hpc_ok hrun_ok hvm_ok
          ⟨hsp_ok, htr_ok, hx8_ok, hx19_ok, hx20_ok, hx21_ok, hx22_ok,
           hx25_ok, hx26_ok, hx27_ok, hx28_ok, hx29_ok⟩
        refine step_msg_relocate_1568_placed ext sckaMsg tag bs39 hbs39 hfold_msg s0_1636 s_ok _ F_rest _
          hs0_1636_align hpc_ok hrun_ok hsp_ok hx8_ok (hx25_ok.trans hx25_sm) (hx27_ok.trans hx27_sm)
          (by simp only [hs0_1636_sp, Rest_1556, F_rest]; ac_rfl) ?_
        intro s1 hpc1 hrun1 hvm_reloc hsp1 htr1 hx0_1 hx8_1
          hx19_1 hx20_1 hx21_1 hx22_1 hx24_1 hx25_1 hx26_1 hx27_1 hx28_1 hx29_1
        apply ProofLib.SepWP.done hpc1 hrun1
        dsimp only [F_rest]
        rw [← A.pool_transport lim (MC.stepEvents (evs0 ++ evs_md) st_cost) sm s1 (hvm_ok.trans hvm_reloc)]
        exact hok_tail evs_md sckaMsg s1 _ hevs_md hmd hpc1 hrun1 hsp1
          (traceVRegs_trans htr1 (traceVRegs_trans htr_ok htr_sm'))
          hx0_1 hx8_1
          (hx19_1.trans (hx19_ok.trans hx19_sm)) (hx20_1.trans (hx20_ok.trans hx20_sm))
          (hx21_1.trans (hx21_ok.trans hx21_sm)) (hx22_1.trans (hx22_ok.trans hx22_sm))
          hx24_1 hx25_1 (hx26_1.trans (hx26_ok.trans hx26_sm)) hx27_1
          (hx28_1.trans (hx28_ok.trans hx28_sm)) (hx29_1.trans (hx29_ok.trans hx29_sm))
          (by simp only [hs0_1636_sp]; ac_rfl)

theorem step_msgDeserialize_1532_placed {MC : AllocCostModel}
    {H_inner : V1InnerHeapPred} {A : RustCliAllocBudget MC} {lim : BudgetLimits} {st_cost : MC.σ}
    {F : ShaCompress} {K : MlKem} {ext : String → Option (State → State)}
    (hC : SpqrRecvPlacedContracts H_inner A lim F K ext)
    (st msg : VecArg) (ret : BitVec 64)
    (evs0 : List AllocEvent) (hevs0 : SpqrRecvEnv st msg evs0)
    (pre : MsgPreamble) (remPtr : BitVec 64) (pre_pb : PqRatchetState) (pb : V1State)
    (w0 w1 : BitVec 64)
    (hpre : msgPreamble msg.bytes = .ok pre)
    (hvalid : MsgRemValid msg remPtr pre.remaining)
    (hdec : spqrDecodeState st.bytes = .ok pre_pb)
    (hinner : pre_pb.inner = some (.v1 pb))
    (hmv : pre.version = 1#8)
    (hmin : ∀ vn, pre_pb.versionNegotiation = some vn → ¬(1#8 < vn.minVersion.truncate 8))
    (s0 s : State) (P R : SepProp)
    (hs0_align : s0.spAligned = true)
    (hpc : s.pc = spqrRecvPlacedEntry + 1532#64)
    (hrun : s.status = .Running) (hsp : s.sp = s0.sp - 4992#64) (htr : TraceVRegs s s0)
    (hx19 : s.readReg64 .x19 = ret) (hx20 : s.readReg64 .x20 = w0)
    (hx21 : s.readReg64 .x21 = pre.index.zeroExtend 64) (hx22 : s.readReg64 .x22 = pre.epoch)
    (hx23 : s.readReg64 .x23 = BitVec.ofNat 64 pre.remaining.length) (hx24 : s.readReg64 .x24 = remPtr)
    (hx26 : s.readReg64 .x26 = 0#64) (hx27 : s.readReg64 .x27 = s0.sp - 3056#64)
    (hx28 : s.readReg64 .x28 = s0.sp - 4288#64) (hx29 : s.readReg64 .x29 = s0.sp - 96#64)
    (hP : P =
      spqrRecvRoPlacedAt ∗ st.at A.repAlloc ∗ msg.at A.repAlloc ∗ memRegion ret 48 ∗
      A.pool lim (MC.stepEvents evs0 st_cost) s ∗
      stackAt (s0.sp - 4992#64) spqrRecvCalleeStackX ∗ memRegion (s0.sp - 4992#64) 352 ∗
      ((s0.sp - 4640#64) ↦₆₄ w0) ∗ ((s0.sp - 4632#64) ↦₆₄ w1) ∗
      optVersionNegotiationPBTailAt A.repAlloc w0 w1 (s0.sp - 4624#64) pre_pb.versionNegotiation ∗
      optChainPBAt A.repAlloc (s0.sp - 4592#64) pre_pb.chain ∗
      optProtoInnerStateAt A.repAlloc (s0.sp - 4512#64) pb.innerState ∗
      memRegion (s0.sp - 4288#64) 4192 ∗ spqrRecvSavedRegs (s0.sp - 4992#64) s0)
    (hok_tail : ∀ (evs_md : List AllocEvent) (sckaMsg : Message spqrPolyApi) (s1 : State) (P1 : SepProp),
      FreeOnlyEvs evs_md →
      Message.deserialize spqrPolyApi pre.epoch pre.remaining = .ok sckaMsg →
      s1.pc = spqrRecvPlacedEntry + 1636#64 →
      s1.status = .Running → s1.sp = s0.sp - 4992#64 → TraceVRegs s1 s0 →
      s1.readReg64 .x0 = s0.sp - 4512#64 → s1.readReg64 .x8 = s0.sp - 2096#64 →
      s1.readReg64 .x19 = ret → s1.readReg64 .x20 = w0 →
      s1.readReg64 .x21 = pre.index.zeroExtend 64 → s1.readReg64 .x22 = pre.epoch →
      s1.readReg64 .x24 = s0.sp - 2096#64 → s1.readReg64 .x25 = s0.sp - 4640#64 →
      s1.readReg64 .x26 = 0#64 → s1.readReg64 .x27 = s0.sp - 3056#64 →
      s1.readReg64 .x28 = s0.sp - 4288#64 → s1.readReg64 .x29 = s0.sp - 96#64 →
      P1 = (spqrRecvRoPlacedAt ∗ st.at A.repAlloc ∗ msg.at A.repAlloc ∗ memRegion ret 48 ∗
        A.pool lim (MC.stepEvents (evs0 ++ evs_md) st_cost) s1 ∗
        stackAt (s0.sp - 4992#64) spqrRecvCalleeStackX ∗ memRegion (s0.sp - 4992#64) 352 ∗
        ((s0.sp - 4640#64) ↦₆₄ w0) ∗ ((s0.sp - 4632#64) ↦₆₄ w1) ∗
        optVersionNegotiationPBTailAt A.repAlloc w0 w1 (s0.sp - 4624#64) pre_pb.versionNegotiation ∗
        optChainPBAt A.repAlloc (s0.sp - 4592#64) pre_pb.chain ∗
        optProtoInnerStateAt A.repAlloc (s0.sp - 4512#64) pb.innerState ∗
        memRegion (s0.sp - 4288#64) 176 ∗ messageAt spqrPolyApi (s0.sp - 4112#64) sckaMsg ∗
        memRegion (s0.sp - 4064#64) 3968 ∗ spqrRecvSavedRegs (s0.sp - 4992#64) s0) →
      SepWPpLS (spqrRecvPlacedProg ext) (s0.readReg64 .x30) s1 P1
        (spqrRecvPlacedPost A lim st_cost (spqrV1Recv F K) st msg ret s0 R)
        (spqrRecvBudgetPanicPost (spqrV1Recv F K) st msg s0 R)) :
    SepWPpLS (spqrRecvPlacedProg ext) (s0.readReg64 .x30) s P
      (spqrRecvPlacedPost A lim st_cost (spqrV1Recv F K) st msg ret s0 R)
      (spqrRecvBudgetPanicPost (spqrV1Recv F K) st msg s0 R) :=
  step_msgDeserialize_1532_placed_ofEnv (SpqrRecvEnv st msg) evs0
    (fun _ hd => SpqrRecvEnv.append_freeOnly hevs0 hd)
    hC st msg ret pre remPtr pre_pb pb w0 w1 hpre hvalid hdec hinner hmv hmin
    s0 s P R hs0_align hpc hrun hsp htr hx19 hx20 hx21 hx22 hx23 hx24 hx26 hx27 hx28 hx29 hP hok_tail

/-! ## 2. `<States>::from_pb` Call, Error Path (`+2144 -> +2492`), and Relocation (`+1640..+1736`) -/

/-- Envelope-parametric error branch after `<States>::from_pb` returns `.error (.err err)` at
    `+1640 .. +1668 -> +2144 .. +2160 -> +2492 .. +2500`. -/
theorem step_post_statesFromPb_err_1640_placed_ofEnv {MC : AllocCostModel}
    (A : RustCliAllocBudget MC) (lim : BudgetLimits) (st_cost : MC.σ)
    (Env : List AllocEvent → Prop) (evs0 : List AllocEvent)
    (hevs_free : ∀ evs_d, FreeOnlyEvs evs_d → Env (evs0 ++ evs_d))
    (F : ShaCompress) (K : MlKem)
    (ext : String → Option (State → State))
    (hC : SpqrRecvDropContractsBudget A lim F ext)
    (st msg : VecArg) (ret : BitVec 64)
    (pre : MsgPreamble) (pre_pb : PqRatchetState) (pb : V1State) (w0 w1 : BitVec 64)
    (sckaMsg : Message spqrPolyApi) (err : Error)
    (hpre : msgPreamble msg.bytes = .ok pre)
    (hdec : spqrDecodeState st.bytes = .ok pre_pb)
    (hinner : pre_pb.inner = some (.v1 pb))
    (hmv : pre.version = 1#8)
    (hmin : ∀ vn, pre_pb.versionNegotiation = some vn → ¬(1#8 < vn.minVersion.truncate 8))
    (hmsg : Message.deserialize spqrPolyApi pre.epoch pre.remaining = .ok sckaMsg)
    (hst0 : States.from_pb spqrPolyApi (spqrAuthApi F) pb = .error (.err err))
    (s0 s : State) (P R : SepProp) (post : State → SepProp → Prop)
    (hpost : post = spqrRecvPlacedPost0OfEnv A lim st_cost Env (spqrV1Recv F K) st msg ret s0 R)
    (hs0_align : s0.spAligned = true)
    (hpc : s.pc = spqrRecvPlacedEntry + 1640#64)
    (hrun : s.status = .Running) (hsp : s.sp = s0.sp - 4992#64) (htr : TraceVRegs s s0)
    (hx19 : s.readReg64 .x19 = ret) (hx25 : s.readReg64 .x25 = s0.sp - 4640#64)
    (hx26 : s.readReg64 .x26 = 0#64) (hx29 : s.readReg64 .x29 = s0.sp - 96#64)
    (hP : P =
      spqrRecvRoPlacedAt ∗ st.at A.repAlloc ∗ msg.at A.repAlloc ∗ memRegion ret 48 ∗
      A.pool lim (MC.stepEvents evs0 st_cost) s ∗
      stackAt (s0.sp - 4992#64) spqrRecvCalleeStackX ∗ memRegion (s0.sp - 4992#64) 352 ∗
      ((s0.sp - 4640#64) ↦₆₄ w0) ∗ ((s0.sp - 4632#64) ↦₆₄ w1) ∗
      optVersionNegotiationPBTailAt A.repAlloc w0 w1 (s0.sp - 4624#64) pre_pb.versionNegotiation ∗
      optChainPBAt A.repAlloc (s0.sp - 4592#64) pre_pb.chain ∗
      memRegion (s0.sp - 4512#64) 224 ∗ memRegion (s0.sp - 4288#64) 176 ∗
      messageAt spqrPolyApi (s0.sp - 4112#64) sckaMsg ∗ memRegion (s0.sp - 4064#64) 1968 ∗
      resultChunkedStatesAt A.repAlloc (F := F) (s0.sp - 2096#64) (.error (.err err)) ∗
      memRegion (s0.sp - 1168#64) 1072 ∗ spqrRecvSavedRegs (s0.sp - 4992#64) s0)
    (hcl : LibsignalCodeLoaded lsmpl s.mem) :
    SepWP (spqrRecvPlacedProg ext) (s0.readReg64 .x30) s P post := by
  have hfsp_align : ((s0.sp - 4992#64) &&& 15#64 == 0#64) = true :=
    sp_sub_4992_aligned s0 hs0_align
  have hfp : s.readReg64 .fp = s0.sp - 96#64 := hx29
  subst hP
  have hexp_err := resultChunkedStatesAt_err_expose A.repAlloc (F := F) (s0.sp - 2096#64) err
  rw [bv_sub_add_lit s0.sp 2096 8, bv_sub_add_lit s0.sp 2096 16,
      bv_sub_add_lit s0.sp 2096 24, bv_sub_add_lit s0.sp 2096 32] at hexp_err
  simp only [Nat.reduceSub, BitVec.ofNat_eq_ofNat] at hexp_err
  refine SepWP.focus_weaken hexp_err (by sep_focus) ?_
  wp_pull_exists; rename_i w1_err w2_err w3_err
  wp_focus_pure; intro hw1_err
  refine SepWP.focus_weaken (memRegion_1168_split_statesFromPb s0.sp) (by sep_focus) ?_
  have h24_fp := memRegion_24_words3 (s0.sp - 144#64)
  rw [bv_sub_add_lit s0.sp 144 8, bv_sub_add_lit s0.sp 144 16] at h24_fp
  simp only [Nat.reduceSub, BitVec.ofNat_eq_ofNat] at h24_fp
  refine SepWP.focus_weaken (Entails.of_eq h24_fp) (by sep_focus) ?_
  wp_pull_exists; rename_i f2 f1 f0
  rw [ret_48_split ret]
  wp_pull_exists; rename_i r3 r2 r1 r0
  dsimp only [spqrRecvPlacedProg, spqrRecvPlacedEntry, BitVec.ofNat_eq_ofNat] at hpc ⊢
  refine seq_vm_lscl (mid := (blkPl_329).base + 2500#64) hcl
    (P_mid :=
      spqrRecvRoPlacedAt ∗ st.at A.repAlloc ∗ msg.at A.repAlloc ∗
      recvResultExactKeyAt A.repAlloc ret ((spqrV1Recv F K).recv st.bytes msg.bytes) ∗
      A.pool lim (MC.stepEvents evs0 st_cost) s ∗
      stackAt (s0.sp - 4992#64) spqrRecvCalleeStackX ∗ memRegion (s0.sp - 4992#64) 352 ∗
      ((s0.sp - 4640#64) ↦₆₄ w0) ∗ ((s0.sp - 4632#64) ↦₆₄ w1) ∗
      optVersionNegotiationPBTailAt A.repAlloc w0 w1 (s0.sp - 4624#64) pre_pb.versionNegotiation ∗
      optChainPBAt A.repAlloc (s0.sp - 4592#64) pre_pb.chain ∗
      memRegion (s0.sp - 4512#64) 4416 ∗
      spqrRecvSavedRegs (s0.sp - 4992#64) s0)
    (Q := fun s1 =>
      s1.sp = s0.sp - 4992#64 ∧
      TraceVRegs s1 s0 ∧
      s1.readReg64 .x25 = s0.sp - 4640#64 ∧
      s1.readReg64 .x26 = 0#64) ?_ ?_
  · by_vm_steps (
      wp_steps 15
      refine SepWP.focus_weaken (hw1_err ret) (by sep_focus) ?_
      refine SepWP.focus_weaken
        (recv_err_byte_foldX A.repAlloc ret w2_err w3_err
          (spqrErrorByte err) (err == .stateDecode) (spqrErrorByte_eq_zero_iff hst0))
        (by sep_focus) ?_
      have hres_eq : recvResultExactKeyAt A.repAlloc ret (.error (err == .stateDecode)) =
          recvResultExactKeyAt A.repAlloc ret ((spqrV1Recv F K).recv st.bytes msg.bytes) := by
        rw [(spqrV1Recv_v1_statesFromPb_err F K hpre hdec hinner hmv hmin hmsg hst0).1]
      rw [hres_eq]
      refine SepWP.focus_weaken (memRegion_4416_join_statesFromPb_err s0.sp w1_err w2_err w3_err sckaMsg) (by sep_focus) ?_
      refine ProofLib.SepWP.done (by simp only [wp_norm, arm64_norm]; try rfl)
        (by simp only [wp_norm, arm64_norm, *])
        ⟨by simp only [wp_norm, arm64_norm],
         Entails.of_eq (by sep_ac_rfl),
         by simp only [wp_norm, arm64_norm, *],
         ⟨by simp only [wp_norm, arm64_norm, htr.1], by simp only [wp_norm, arm64_norm, htr.2]⟩,
         by simp only [wp_norm, arm64_norm, *],
         by simp only [wp_norm, arm64_norm, *]⟩
    )
  · intro s1 hpc1 hrun1 hcl1 hvm1 ⟨hsp1, htr1, hx25_1, hx26_1⟩
    rw [← A.pool_transport lim (MC.stepEvents evs0 st_cost) s s1 hvm1]
    exact step_drop_vn_chain_2500_placed_ofEnv A lim st_cost Env evs0 hevs_free
      (spqrV1Recv F K) ext hC st msg ret pre_pb w0 w1 s0 s1 _ R post
      hpost hs0_align hpc1 hrun1 hsp1 htr1 hx25_1 hx26_1 (by ac_rfl) hcl1

theorem step_post_statesFromPb_err_1640_placed {MC : AllocCostModel}
    (A : RustCliAllocBudget MC) (lim : BudgetLimits) (st_cost : MC.σ)
    (F : ShaCompress) (K : MlKem)
    (ext : String → Option (State → State))
    (hC : SpqrRecvDropContractsBudget A lim F ext)
    (st msg : VecArg) (ret : BitVec 64)
    (evs0 : List AllocEvent) (hevs0 : SpqrRecvEnv st msg evs0)
    (pre : MsgPreamble) (pre_pb : PqRatchetState) (pb : V1State) (w0 w1 : BitVec 64)
    (sckaMsg : Message spqrPolyApi) (err : Error)
    (hpre : msgPreamble msg.bytes = .ok pre)
    (hdec : spqrDecodeState st.bytes = .ok pre_pb)
    (hinner : pre_pb.inner = some (.v1 pb))
    (hmv : pre.version = 1#8)
    (hmin : ∀ vn, pre_pb.versionNegotiation = some vn → ¬(1#8 < vn.minVersion.truncate 8))
    (hmsg : Message.deserialize spqrPolyApi pre.epoch pre.remaining = .ok sckaMsg)
    (hst0 : States.from_pb spqrPolyApi (spqrAuthApi F) pb = .error (.err err))
    (s0 s : State) (P R : SepProp) (post : State → SepProp → Prop)
    (hpost : post = spqrRecvPlacedPost0 A lim st_cost (spqrV1Recv F K) st msg ret s0 R)
    (hs0_align : s0.spAligned = true)
    (hpc : s.pc = spqrRecvPlacedEntry + 1640#64)
    (hrun : s.status = .Running) (hsp : s.sp = s0.sp - 4992#64) (htr : TraceVRegs s s0)
    (hx19 : s.readReg64 .x19 = ret) (hx25 : s.readReg64 .x25 = s0.sp - 4640#64)
    (hx26 : s.readReg64 .x26 = 0#64) (hx29 : s.readReg64 .x29 = s0.sp - 96#64)
    (hP : P =
      spqrRecvRoPlacedAt ∗ st.at A.repAlloc ∗ msg.at A.repAlloc ∗ memRegion ret 48 ∗
      A.pool lim (MC.stepEvents evs0 st_cost) s ∗
      stackAt (s0.sp - 4992#64) spqrRecvCalleeStackX ∗ memRegion (s0.sp - 4992#64) 352 ∗
      ((s0.sp - 4640#64) ↦₆₄ w0) ∗ ((s0.sp - 4632#64) ↦₆₄ w1) ∗
      optVersionNegotiationPBTailAt A.repAlloc w0 w1 (s0.sp - 4624#64) pre_pb.versionNegotiation ∗
      optChainPBAt A.repAlloc (s0.sp - 4592#64) pre_pb.chain ∗
      memRegion (s0.sp - 4512#64) 224 ∗ memRegion (s0.sp - 4288#64) 176 ∗
      messageAt spqrPolyApi (s0.sp - 4112#64) sckaMsg ∗ memRegion (s0.sp - 4064#64) 1968 ∗
      resultChunkedStatesAt A.repAlloc (F := F) (s0.sp - 2096#64) (.error (.err err)) ∗
      memRegion (s0.sp - 1168#64) 1072 ∗ spqrRecvSavedRegs (s0.sp - 4992#64) s0)
    (hcl : LibsignalCodeLoaded lsmpl s.mem) :
    SepWP (spqrRecvPlacedProg ext) (s0.readReg64 .x30) s P post :=
  step_post_statesFromPb_err_1640_placed_ofEnv A lim st_cost (SpqrRecvEnv st msg) evs0
    (fun _ hd => SpqrRecvEnv.append_freeOnly hevs0 hd)
    F K ext hC st msg ret pre pre_pb pb w0 w1 sckaMsg err
    hpre hdec hinner hmv hmin hmsg hst0 s0 s P R post hpost hs0_align
    hpc hrun hsp htr hx19 hx25 hx26 hx29 hP hcl

/-- Ok branch after `<States>::from_pb` returns `.ok st0` at `+1640 .. +1736`, supplying
    `VmPreserved s s1` to `hnext` so budget callers can transport `A.pool` across the
    relocation. -/
theorem step_post_statesFromPb_ok_1640_placed {MC : AllocCostModel}
    (A : RustCliAllocBudget MC) (F : ShaCompress)
    (ext : String → Option (State → State))
    (hmemcpy_ok : subroutine_ok (spqrRecvPlacedProg ext) (lsρ "memcpy") framelessMemcpyBudgetSpec)
    (st0 : States spqrPolyApi (spqrAuthApi F))
    (s0 s : State) (P F_rest : SepProp) (post : State → SepProp → Prop)
    (hs0_align : s0.spAligned = true)
    (hpc : s.pc = spqrRecvPlacedEntry + 1640#64)
    (hrun : s.status = .Running) (hsp : s.sp = s0.sp - 4992#64)
    (hx24 : s.readReg64 .x24 = s0.sp - 2096#64) (hx25 : s.readReg64 .x25 = s0.sp - 4640#64)
    (hx26 : s.readReg64 .x26 = 0#64) (hx27 : s.readReg64 .x27 = s0.sp - 3056#64)
    (hx29 : s.readReg64 .x29 = s0.sp - 96#64)
    (hP : P =
      stackAt (s0.sp - 4992#64) spqrRecvCalleeStackX ∗
      memRegion (s0.sp - 4064#64) 1968 ∗
      chunkedStatesAt A.repAlloc (s0.sp - 2096#64) st0 ∗
      memRegion (s0.sp - 1168#64) 1072 ∗ F_rest)
    (hnext : ∀ s1 : State,
      s1.pc = spqrRecvPlacedEntry + 1736#64 →
      s1.status = .Running → VmPreserved s s1 →
      s1.sp = s0.sp - 4992#64 → TraceVRegs s1 s →
      s1.readReg64 .x0 = s0.sp - 3056#64 → s1.readReg64 .x1 = s0.sp - 1160#64 →
      s1.readReg64 .x2 = s0.sp - 4112#64 → s1.readReg64 .x19 = s.readReg64 .x19 →
      s1.readReg64 .x20 = s.readReg64 .x20 → s1.readReg64 .x21 = s.readReg64 .x21 →
      s1.readReg64 .x22 = s.readReg64 .x22 → s1.readReg64 .x24 = s0.sp - 3056#64 →
      s1.readReg64 .x25 = s0.sp - 4640#64 → s1.readReg64 .x26 = s0.sp - 1160#64 →
      s1.readReg64 .x27 = s0.sp - 3056#64 → s1.readReg64 .x28 = 0#64 →
      s1.readReg64 .x29 = s0.sp - 96#64 →
      SepWP (spqrRecvPlacedProg ext) (s0.readReg64 .x30) s1
        (stackAt (s0.sp - 4992#64) spqrRecvCalleeStackX ∗
          memRegion (s0.sp - 4064#64) 2896 ∗ memRegion (s0.sp - 1168#64) 8 ∗
          chunkedStatesAt A.repAlloc (s0.sp - 1160#64) st0 ∗
          memRegion (s0.sp - 232#64) 136 ∗ F_rest) post) :
    SepWP (spqrRecvPlacedProg ext) (s0.readReg64 .x30) s P post := by
  have hmemcpy_raw := hmemcpy_ok
  simp only [framelessMemcpyBudgetSpec, framelessMemcpySpec] at hmemcpy_raw
  have hfsp_align : ((s0.sp - 4992#64) &&& 15#64 == 0#64) = true :=
    sp_sub_4992_aligned s0 hs0_align
  have hfp : s.readReg64 .fp = s0.sp - 96#64 := hx29
  subst hP
  have hreloc := chunkedStatesAt_entails_reloc_words A.repAlloc (s0.sp - 2096#64) st0
  rw [bv_sub_add_lit s0.sp 2096 8, bv_sub_add_lit s0.sp 2096 16,
      bv_sub_add_lit s0.sp 2096 24, bv_sub_add_lit s0.sp 2096 32] at hreloc
  simp only [Nat.reduceSub, BitVec.ofNat_eq_ofNat] at hreloc
  refine SepWP.focus_weaken hreloc (by sep_focus) ?_
  wp_pull_exists; rename_i bs w1_st w2_st w3_st bs896
  wp_focus_pure; rintro ⟨hbs, hbs896⟩
  refine SepWP.focus_weaken (memRegion_1168_split_statesFromPb s0.sp) (by sep_focus) ?_
  have h928_dst := memRegion_928_split_header32_body896 (s0.sp - 1160#64)
  rw [bv_sub_add_lit s0.sp 1160 8, bv_sub_add_lit s0.sp 1160 16,
      bv_sub_add_lit s0.sp 1160 24, bv_sub_add_lit s0.sp 1160 32] at h928_dst
  simp only [Nat.reduceSub, BitVec.ofNat_eq_ofNat] at h928_dst
  refine SepWP.focus_weaken h928_dst (by sep_focus) ?_
  wp_pull_exists; rename_i d0 d1 d2 d3
  have h24_fp := memRegion_24_words3 (s0.sp - 144#64)
  rw [bv_sub_add_lit s0.sp 144 8, bv_sub_add_lit s0.sp 144 16] at h24_fp
  simp only [Nat.reduceSub, BitVec.ofNat_eq_ofNat] at h24_fp
  refine SepWP.focus_weaken (Entails.of_eq h24_fp) (by sep_focus) ?_
  wp_pull_exists; rename_i f2 f1 f0
  have h896_dst : memRegion (s0.sp - 1128#64) 896 = memRegion (s0.sp - 1128#64) bs896.length := by
    rw [hbs896]
  rw [h896_dst]
  have hlen_lt : bs896.length < 2 ^ 64 := by rw [hbs896]; decide
  have hlen_eq : (896#64 : BitVec 64).toNat = bs896.length := hbs896.symm
  dsimp only [spqrRecvPlacedProg, spqrRecvPlacedEntry, BitVec.ofNat_eq_ofNat] at hmemcpy_raw hpc hnext ⊢
  refine seq_vm_clean (mid := lsρ "memcpy")
    (P_mid :=
      stackAt (s0.sp - 4992#64) spqrRecvCalleeStackX ∗
      memRegion (s0.sp - 4064#64) 1968 ∗
      ((s0.sp - 2096#64) ↦₆₄ chunkedStatesWord0 st0) ∗
      ((s0.sp - 2088#64) ↦₆₄ w1_st) ∗
      ((s0.sp - 2080#64) ↦₆₄ w2_st) ∗
      ((s0.sp - 2072#64) ↦₆₄ w3_st) ∗
      ((s0.sp - 2064#64) ↦ₛ bs896) ∗
      relocatedHeap (fun dst => chunkedStatesTail920At A.repAlloc dst st0) bs ∗
      memRegion (s0.sp - 1168#64) 8 ∗
      ((s0.sp - 1160#64) ↦₆₄ d0) ∗
      ((s0.sp - 1152#64) ↦₆₄ d1) ∗
      ((s0.sp - 1144#64) ↦₆₄ d2) ∗
      ((s0.sp - 1136#64) ↦₆₄ d3) ∗
      memRegion (s0.sp - 1128#64) bs896.length ∗
      memRegion (s0.sp - 232#64) 88 ∗
      ((s0.sp - 144#64) ↦₆₄ w1_st) ∗
      ((s0.sp - 136#64) ↦₆₄ w2_st) ∗
      ((s0.sp - 128#64) ↦₆₄ w3_st) ∗
      memRegion (s0.sp - 120#64) 24 ∗ F_rest)
    (Q := fun s_mc =>
      s_mc.sp = s0.sp - 4992#64 ∧
      TraceVRegs s_mc s ∧
      s_mc.readReg64 .x0 = s0.sp - 1128#64 ∧
      s_mc.readReg64 .x1 = s0.sp - 2064#64 ∧
      s_mc.readReg64 .x2 = 896#64 ∧
      s_mc.readReg64 .x30 = (blkPl_329).base + 1700#64 ∧
      s_mc.readReg64 .x19 = s.readReg64 .x19 ∧
      s_mc.readReg64 .x20 = s.readReg64 .x20 ∧
      s_mc.readReg64 .x21 = s.readReg64 .x21 ∧
      s_mc.readReg64 .x22 = s.readReg64 .x22 ∧
      s_mc.readReg64 .x23 = chunkedStatesWord0 st0 ∧
      s_mc.readReg64 .x25 = s0.sp - 4640#64 ∧
      s_mc.readReg64 .x26 = s0.sp - 1160#64 ∧
      s_mc.readReg64 .x27 = s0.sp - 3056#64 ∧
      s_mc.readReg64 .x28 = 0#64 ∧
      s_mc.readReg64 .fp = s0.sp - 96#64) ?_ ?_
  · by_vm_steps (
      wp_steps 15
      refine ProofLib.SepWP.done (by simp only [wp_norm, arm64_norm, *])
        (by simp only [wp_norm, arm64_norm, *])
        ⟨by simp only [wp_norm, arm64_norm],
         Entails.of_eq (by sep_ac_rfl), ?_⟩
      refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
      all_goals first | rfl | simp only [wp_norm, arm64_norm, *]
    )
  · intro s_mc hpc_mc hrun_mc hvm1
      ⟨hsp_mc, htr_mc, hx0_mc, hx1_mc, hx2_mc, hlr_mc,
       hx19_mc, hx20_mc, hx21_mc, hx22_mc, hx23_mc, hx25_mc, hx26_mc, hx27_mc, hx28_mc, hfp_mc⟩
    have hs_mc_align : s_mc.spAligned = true := by
      rw [State.spAligned, hsp_mc]; exact hfsp_align
    wp_call hmemcpy_raw ⟨s0.sp - 1128#64, s0.sp - 2064#64, bs896⟩
    have hvm2 := ‹VmPreserved s_mc _›
    let s_post : State := (fun {a b : State} (_ : VmPreserved a b) => b) hvm2
    have hvm2' : VmPreserved s_mc s_post := hvm2
    have hfp_post : s_post.readReg64 .fp = s0.sp - 96#64 := by
      simp only [s_post, wp_norm, arm64_norm, *]
    refine seq_vm_clean (mid := (blkPl_329).base + 1736#64)
      (P_mid :=
        stackAt (s0.sp - 4992#64) spqrRecvCalleeStackX ∗
        memRegion (s0.sp - 4064#64) 2896 ∗ memRegion (s0.sp - 1168#64) 8 ∗
        chunkedStatesAt A.repAlloc (s0.sp - 1160#64) st0 ∗
        memRegion (s0.sp - 232#64) 136 ∗ F_rest)
      (Q := fun s1 =>
        s1.sp = s0.sp - 4992#64 ∧
        TraceVRegs s1 s ∧
        s1.readReg64 .x0 = s0.sp - 3056#64 ∧
        s1.readReg64 .x1 = s0.sp - 1160#64 ∧
        s1.readReg64 .x2 = s0.sp - 4112#64 ∧
        s1.readReg64 .x19 = s.readReg64 .x19 ∧
        s1.readReg64 .x20 = s.readReg64 .x20 ∧
        s1.readReg64 .x21 = s.readReg64 .x21 ∧
        s1.readReg64 .x22 = s.readReg64 .x22 ∧
        s1.readReg64 .x24 = s0.sp - 3056#64 ∧
        s1.readReg64 .x25 = s0.sp - 4640#64 ∧
        s1.readReg64 .x26 = s0.sp - 1160#64 ∧
        s1.readReg64 .x27 = s0.sp - 3056#64 ∧
        s1.readReg64 .x28 = 0#64 ∧
        s1.readReg64 .x29 = s0.sp - 96#64) ?_ ?_
    · by_vm_steps (
        wp_steps 9
        have hreassemble_dst := reassemble_chunkedStatesAt_words A.repAlloc (s0.sp - 1160#64) st0 w1_st w2_st w3_st hbs
        rw [bv_sub_add_lit s0.sp 1160 8, bv_sub_add_lit s0.sp 1160 16,
            bv_sub_add_lit s0.sp 1160 24, bv_sub_add_lit s0.sp 1160 32] at hreassemble_dst
        simp only [Nat.reduceSub, BitVec.ofNat_eq_ofNat] at hreassemble_dst
        refine SepWP.focus_weaken hreassemble_dst (by sep_focus) ?_
        have hreassemble_src := reassemble_src_928_after_memcpy (s0.sp - 2096#64) (chunkedStatesWord0 st0) w1_st w2_st w3_st hbs896
        rw [bv_sub_add_lit s0.sp 2096 8, bv_sub_add_lit s0.sp 2096 16,
            bv_sub_add_lit s0.sp 2096 24, bv_sub_add_lit s0.sp 2096 32] at hreassemble_src
        simp only [Nat.reduceSub, BitVec.ofNat_eq_ofNat] at hreassemble_src
        refine SepWP.focus_weaken hreassemble_src (by sep_focus) ?_
        refine SepWP.focus_weaken (memRegion_4064_join_1968_928 s0.sp) (by sep_focus) ?_
        refine SepWP.focus_weaken (memRegion_136_join_fp_spill s0.sp w1_st w2_st w3_st) (by sep_focus) ?_
        refine ProofLib.SepWP.done (by simp only [wp_norm, arm64_norm]; try rfl)
          (by simp only [wp_norm, arm64_norm, *])
          ⟨by simp only [wp_norm, arm64_norm],
           Entails.of_eq (by sep_ac_rfl), ?_⟩
        refine ⟨?_, ⟨?_, ?_⟩, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
        all_goals first | rfl | (change _ = s0.sp - 96#64; simp only [wp_norm, arm64_norm, *]) | simp only [htr_mc.1, htr_mc.2, wp_norm, arm64_norm, *]
      )
    · intro s1 hpc1 hrun1 hvm3
        ⟨hsp1, htr1, hx0_1, hx1_1, hx2_1, hx19_1, hx20_1, hx21_1, hx22_1,
         hx24_1, hx25_1, hx26_1, hx27_1, hx28_1, hx29_1⟩
      exact hnext s1 hpc1 hrun1 (hvm1.trans (hvm2'.trans hvm3)) hsp1 htr1
        hx0_1 hx1_1 hx2_1 hx19_1 hx20_1 hx21_1 hx22_1 hx24_1 hx25_1 hx26_1 hx27_1 hx28_1 hx29_1

/-- Envelope-parametric budget-threaded `<States>::from_pb` step (`+1636 .. +1736`, error via
    `+2500`). -/
theorem step_statesFromPb_1636_placed_ofEnv {MC : AllocCostModel}
    {H_inner : V1InnerHeapPred} {A : RustCliAllocBudget MC} {lim : BudgetLimits} {st_cost : MC.σ}
    {F : ShaCompress} {K : MlKem}
    {DecodePreEnv DecodePostEnv : DecodeStateGhost → List AllocEvent → Prop}
    {InitEnv : InitInnerGhost → List AllocEvent → Prop}
    {FromPbEnv : V1State → List AllocEvent → Prop}
    {RecvEnv : StatesRecvGhost F → List AllocEvent → Prop}
    {IntoPbEnv : StatesIntoPbGhost F → List AllocEvent → Prop}
    {ext : String → Option (State → State)}
    (Env : List AllocEvent → Prop) (evs0 : List AllocEvent)
    (hC : SpqrRecvPlacedContractsOfEnv H_inner A lim F K
      DecodePreEnv DecodePostEnv InitEnv FromPbEnv RecvEnv IntoPbEnv ext)
    (st msg : VecArg) (ret : BitVec 64)
    (pre : MsgPreamble) (pre_pb : PqRatchetState) (pb : V1State)
    (w0 w1 : BitVec 64) (sckaMsg : Message spqrPolyApi)
    (hpts : v1StatePtsBound pb)
    (hpre : msgPreamble msg.bytes = .ok pre)
    (hdec : spqrDecodeState st.bytes = .ok pre_pb)
    (hinner : pre_pb.inner = some (.v1 pb))
    (hmv : pre.version = 1#8)
    (hmin : ∀ vn, pre_pb.versionNegotiation = some vn → ¬(1#8 < vn.minVersion.truncate 8))
    (hmsg : Message.deserialize spqrPolyApi pre.epoch pre.remaining = .ok sckaMsg)
    (s0 s : State) (P R : SepProp)
    (hFit_fpb : FitsEnv MC lim (MC.stepEvents evs0 st_cost) (FromPbEnv pb))
    (hevs_err : ∀ evs_fpb evs_d, FromPbEnv pb evs_fpb → FreeOnlyEvs evs_d → Env ((evs0 ++ evs_fpb) ++ evs_d))
    (hs0_align : s0.spAligned = true)
    (hpc : s.pc = spqrRecvPlacedEntry + 1636#64)
    (hrun : s.status = .Running) (hsp : s.sp = s0.sp - 4992#64) (htr : TraceVRegs s s0)
    (hx0 : s.readReg64 .x0 = s0.sp - 4512#64) (hx8 : s.readReg64 .x8 = s0.sp - 2096#64)
    (hx19 : s.readReg64 .x19 = ret) (hx20 : s.readReg64 .x20 = w0)
    (hx21 : s.readReg64 .x21 = pre.index.zeroExtend 64) (hx22 : s.readReg64 .x22 = pre.epoch)
    (hx24 : s.readReg64 .x24 = s0.sp - 2096#64) (hx25 : s.readReg64 .x25 = s0.sp - 4640#64)
    (hx26 : s.readReg64 .x26 = 0#64) (hx27 : s.readReg64 .x27 = s0.sp - 3056#64)
    (hx29 : s.readReg64 .x29 = s0.sp - 96#64)
    (hP : P =
      spqrRecvRoPlacedAt ∗ st.at A.repAlloc ∗ msg.at A.repAlloc ∗ memRegion ret 48 ∗
      A.pool lim (MC.stepEvents evs0 st_cost) s ∗
      stackAt (s0.sp - 4992#64) spqrRecvCalleeStackX ∗ memRegion (s0.sp - 4992#64) 352 ∗
      ((s0.sp - 4640#64) ↦₆₄ w0) ∗ ((s0.sp - 4632#64) ↦₆₄ w1) ∗
      optVersionNegotiationPBTailAt A.repAlloc w0 w1 (s0.sp - 4624#64) pre_pb.versionNegotiation ∗
      optChainPBAt A.repAlloc (s0.sp - 4592#64) pre_pb.chain ∗
      optProtoInnerStateAt A.repAlloc (s0.sp - 4512#64) pb.innerState ∗
      memRegion (s0.sp - 4288#64) 176 ∗ messageAt spqrPolyApi (s0.sp - 4112#64) sckaMsg ∗
      memRegion (s0.sp - 4064#64) 3968 ∗ spqrRecvSavedRegs (s0.sp - 4992#64) s0)
    (hok_tail : ∀ (evs_fpb : List AllocEvent) (st0 : States spqrPolyApi (spqrAuthApi F))
      (s1 : State) (P1 : SepProp),
      FromPbEnv pb evs_fpb →
      States.from_pb spqrPolyApi (spqrAuthApi F) pb = .ok st0 →
      s1.pc = spqrRecvPlacedEntry + 1736#64 →
      s1.status = .Running → s1.sp = s0.sp - 4992#64 → TraceVRegs s1 s0 →
      s1.readReg64 .x0 = s0.sp - 3056#64 → s1.readReg64 .x1 = s0.sp - 1160#64 →
      s1.readReg64 .x2 = s0.sp - 4112#64 → s1.readReg64 .x19 = ret →
      s1.readReg64 .x20 = w0 → s1.readReg64 .x21 = pre.index.zeroExtend 64 →
      s1.readReg64 .x22 = pre.epoch → s1.readReg64 .x24 = s0.sp - 3056#64 →
      s1.readReg64 .x25 = s0.sp - 4640#64 → s1.readReg64 .x26 = s0.sp - 1160#64 →
      s1.readReg64 .x27 = s0.sp - 3056#64 → s1.readReg64 .x28 = 0#64 →
      s1.readReg64 .x29 = s0.sp - 96#64 →
      P1 = (spqrRecvRoPlacedAt ∗ st.at A.repAlloc ∗ msg.at A.repAlloc ∗ memRegion ret 48 ∗
        A.pool lim (MC.stepEvents (evs0 ++ evs_fpb) st_cost) s1 ∗
        stackAt (s0.sp - 4992#64) spqrRecvCalleeStackX ∗ memRegion (s0.sp - 4992#64) 352 ∗
        ((s0.sp - 4640#64) ↦₆₄ w0) ∗ ((s0.sp - 4632#64) ↦₆₄ w1) ∗
        optVersionNegotiationPBTailAt A.repAlloc w0 w1 (s0.sp - 4624#64) pre_pb.versionNegotiation ∗
        optChainPBAt A.repAlloc (s0.sp - 4592#64) pre_pb.chain ∗
        memRegion (s0.sp - 4512#64) 224 ∗ memRegion (s0.sp - 4288#64) 176 ∗
        messageAt spqrPolyApi (s0.sp - 4112#64) sckaMsg ∗
        memRegion (s0.sp - 4064#64) 2896 ∗ memRegion (s0.sp - 1168#64) 8 ∗
        chunkedStatesAt A.repAlloc (s0.sp - 1160#64) st0 ∗
        memRegion (s0.sp - 232#64) 136 ∗ spqrRecvSavedRegs (s0.sp - 4992#64) s0) →
      SepWPpLS (spqrRecvPlacedProg ext) (s0.readReg64 .x30) s1 P1
        (spqrRecvPlacedPostOfEnv A lim st_cost Env (spqrV1Recv F K) st msg ret s0 R)
        (spqrRecvBudgetPanicPost (spqrV1Recv F K) st msg s0 R)) :
    SepWPpLS (spqrRecvPlacedProg ext) (s0.readReg64 .x30) s P
      (spqrRecvPlacedPostOfEnv A lim st_cost Env (spqrV1Recv F K) st msg ret s0 R)
      (spqrRecvBudgetPanicPost (spqrV1Recv F K) st msg s0 R) := by
  have hfrom_call := hC.statesFromPb_ok
  have hfsp_align : ((s0.sp - 4992#64) &&& 15#64 == 0#64) = true :=
    sp_sub_4992_aligned s0 hs0_align
  subst hP
  refine SepWPpLS.focus_weaken (memRegion_4064_split_2096 s0.sp) (by sep_focus) ?_
  apply SepWPpLS.of_sepWP (mid := lsmpl.base 333)
  let P_pre_fpb : SepProp :=
    memRegion (s0.sp - 4064#64) 1968 ∗ memRegion (s0.sp - 2096#64) 928 ∗ memRegion (s0.sp - 1168#64) 1072 ∗
    spqrRecvRoPlacedAt ∗ st.at A.repAlloc ∗ msg.at A.repAlloc ∗ memRegion ret 48 ∗
    A.pool lim (MC.stepEvents evs0 st_cost) s ∗
    stackAt (s0.sp - 4992#64) spqrRecvCalleeStackX ∗ memRegion (s0.sp - 4992#64) 352 ∗
    ((s0.sp - 4640#64) ↦₆₄ w0) ∗ ((s0.sp - 4632#64) ↦₆₄ w1) ∗
    optVersionNegotiationPBTailAt A.repAlloc w0 w1 (s0.sp - 4624#64) pre_pb.versionNegotiation ∗
    optChainPBAt A.repAlloc (s0.sp - 4592#64) pre_pb.chain ∗
    optProtoInnerStateAt A.repAlloc (s0.sp - 4512#64) pb.innerState ∗
    memRegion (s0.sp - 4288#64) 176 ∗ messageAt spqrPolyApi (s0.sp - 4112#64) sckaMsg ∗
    spqrRecvSavedRegs (s0.sp - 4992#64) s0
  dsimp only [spqrRecvPlacedProg, spqrRecvPlacedEntry, BitVec.ofNat_eq_ofNat] at hpc ⊢
  refine seq_vm_clean (mid := lsmpl.base 333) (P_mid := P_pre_fpb)
    (Q := fun sc =>
      sc.sp = s.sp ∧
      TraceVRegs sc s ∧
      sc.readReg64 .x0 = s.readReg64 .x0 ∧
      sc.readReg64 .x8 = s.readReg64 .x8 ∧
      sc.readReg64 .x19 = s.readReg64 .x19 ∧
      sc.readReg64 .x20 = s.readReg64 .x20 ∧
      sc.readReg64 .x21 = s.readReg64 .x21 ∧
      sc.readReg64 .x22 = s.readReg64 .x22 ∧
      sc.readReg64 .x24 = s.readReg64 .x24 ∧
      sc.readReg64 .x25 = s.readReg64 .x25 ∧
      sc.readReg64 .x26 = s.readReg64 .x26 ∧
      sc.readReg64 .x27 = s.readReg64 .x27 ∧
      sc.readReg64 .x29 = s.readReg64 .x29 ∧
      sc.readReg64 .x30 = spqrRecvPlacedEntry + 1640#64) ?_ ?_
  · by_vm_steps (
      wp_steps
      refine ProofLib.SepWP.done (by simp only [wp_norm, arm64_norm, *])
        (by simp only [wp_norm, arm64_norm, *])
        ⟨by simp only [wp_norm, arm64_norm],
         Entails.of_eq (by dsimp only [P_pre_fpb]; sep_ac_rfl), ?_⟩
      refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
      all_goals first | rfl | simp only [spqrRecvPlacedEntry, wp_norm, arm64_norm, *]
    )
  · intro sc hpc_sc hrun_sc hvm_sc ⟨hsp_sc, htr_sc, hx0_sc, hx8_sc,
      hx19_sc, hx20_sc, hx21_sc, hx22_sc, hx24_sc, hx25_sc, hx26_sc, hx27_sc, hx29_sc, hx30_sc⟩
    apply ProofLib.SepWP.done hpc_sc hrun_sc
    dsimp only [P_pre_fpb]
    rw [← A.pool_transport lim (MC.stepEvents evs0 st_cost) s sc hvm_sc]
    unfold spqrRecvRoPlacedAt
    have hjmp_eq : statesFromPbJumpTablePlacedAt =
        CryptoVerification.SpqrV1.States.FromPb.statesFromPbJumpTablePlacedAt := rfl
    rw [hjmp_eq]
    refine SepWPpLS.focus_weaken
      (Entails.of_eq (stackAt_spqrRecvCallee_split (s0.sp - 4992#64) statesFromPbStackX (by decide)))
      (by sep_focus) ?_
    refine LibsignalBinary.Proofs.SpqrV1.Top.Recv.Part3PlacedBudget.SepWPpLS.call_lscro hfrom_call
      ((⟨s0.sp - 2096#64, s0.sp - 4512#64, pb⟩ : StatesFromPbGhost), MC.stepEvents evs0 st_cost)
      hpc_sc hrun_sc
      (by simp only [State.spAligned, hsp_sc, hsp]; exact hfsp_align)
      hx30_sc (by rw [htr_sc.1, htr.1]) (fun sm => onPanic_false_budget _ sm) (fun _ _ => rfl)
      (by
        dsimp only [statesFromPbPlacedSpecXOfEnv,
          LibsignalBinary.Proofs.SpqrV1.States.FromPb.DefsBudget.statesFromPbPlacedSpecXOfEnv]
        refine frame_pure_pre ⟨hx8_sc.trans hx8, hx0_sc.trans hx0, hpts, hFit_fpb⟩
          (by rw [hsp_sc, hsp]; sep_focus))
      ?_
    intro sm hpcm hrunm hspm hcsm
    rcases hcsm with ⟨hx19_c, hx20_c, hx21_c, hx22_c, _, hx24_c, hx25_c, hx26_c, hx27_c, _, hxfp_c, hvregs_c⟩
    dsimp only [statesFromPbPlacedSpecXOfEnv,
      LibsignalBinary.Proofs.SpqrV1.States.FromPb.DefsBudget.statesFromPbPlacedSpecXOfEnv]
    simp only [sepExists_sepConj_left, sepConj_assoc]
    apply SepWPpLS.exists_elim; intro evs_fpb
    refine SepWPpLS.focus_pure (by sep_focus) ?_; rintro ⟨htr_sm, hevs_fpb⟩
    have htr_sm' : TraceVRegs sm s0 := ⟨by rw [htr_sm, htr_sc.1, htr.1], by rw [hvregs_c, htr_sc.2, htr.2]⟩
    have hspm' : sm.sp = s0.sp - 4992#64 := by rw [hspm, hsp_sc, hsp]
    have hx19_sm : sm.readReg64 .x19 = ret := by rw [hx19_c, hx19_sc, hx19]
    have hx20_sm : sm.readReg64 .x20 = w0 := by rw [hx20_c, hx20_sc, hx20]
    have hx21_sm : sm.readReg64 .x21 = pre.index.zeroExtend 64 := by rw [hx21_c, hx21_sc, hx21]
    have hx22_sm : sm.readReg64 .x22 = pre.epoch := by rw [hx22_c, hx22_sc, hx22]
    have hx24_sm : sm.readReg64 .x24 = s0.sp - 2096#64 := by rw [hx24_c, hx24_sc, hx24]
    have hx25_sm : sm.readReg64 .x25 = s0.sp - 4640#64 := by rw [hx25_c, hx25_sc, hx25]
    have hx26_sm : sm.readReg64 .x26 = 0#64 := by rw [hx26_c, hx26_sc, hx26]
    have hx27_sm : sm.readReg64 .x27 = s0.sp - 3056#64 := by rw [hx27_c, hx27_sc, hx27]
    have hx29_sm : sm.readReg64 .x29 = s0.sp - 96#64 := by
      change sm.readReg64 Reg.fp = s0.sp - 96#64
      rw [hxfp_c]; exact hx29_sc.trans hx29
    have hsp_eq := congrArg (stackAt · statesFromPbStackX) (hspm.symm.trans hspm')
    refine SepWPpLS.focus_weaken (Entails.of_eq hsp_eq) (by sep_focus) ?_
    refine SepWPpLS.focus_weaken
      (Entails.of_eq (stackAt_spqrRecvCallee_split (s0.sp - 4992#64) statesFromPbStackX (by decide)).symm)
      (by sep_focus) ?_
    rw [← hjmp_eq]
    have hro_fold :
        v1StateJumpTablesPlacedAt ∗
          statesFromPbJumpTablePlacedAt ∗
          statesRecvRoPlacedAt ∗
          statesIntoPbJumpTablePlacedAt ⊢
        spqrRecvRoPlacedAt := Entails.refl _
    refine SepWPpLS.focus_weaken hro_fold (by sep_focus) ?_
    have h224_pb : memRegion (s0.sp - 4512#64) optProtoInnerStateSize = memRegion (s0.sp - 4512#64) 224 := rfl
    rw [h224_pb, ← MC.stepEvents_append]
    cases hfrom : States.from_pb spqrPolyApi (spqrAuthApi F) pb with
    | error se =>
      cases se with
      | panic p =>
        rw [resultChunkedStatesAt_panic_false]
        refine SepWPpLS.focus_pure (by sep_focus) False.elim
      | err err =>
        apply SepWPpLS.of_sepWP_ret_lscl; intro hcl
        refine sepWP_spqrRecvPlacedPostOfEnv_of_post0
          (spqrV1Recv_v1_statesFromPb_err F K hpre hdec hinner hmv hmin hmsg hfrom).2 ?_
        exact step_post_statesFromPb_err_1640_placed_ofEnv A lim st_cost Env (evs0 ++ evs_fpb)
          (fun evs_d hd => hevs_err evs_fpb evs_d hevs_fpb hd)
          F K ext (toDropContractsBudget hC) st msg ret
          pre pre_pb pb w0 w1 sckaMsg err hpre hdec hinner hmv hmin hmsg hfrom
          s0 sm _ R _ rfl hs0_align hpcm hrunm hspm' htr_sm' hx19_sm hx25_sm hx26_sm hx29_sm
          (by ac_rfl) hcl
    | ok st0 =>
      dsimp only [resultChunkedStatesAt]
      let s0_1736 := s0.writeReg64 .x30 (spqrRecvPlacedEntry + 1736#64)
      have hs0_1736_sp : s0_1736.sp = s0.sp := rfl
      have hs0_1736_align : s0_1736.spAligned = true := hs0_align
      apply SepWPpLS.of_sepWP (mid := spqrRecvPlacedEntry + 1736#64)
      let F_rest : SepProp :=
        spqrRecvRoPlacedAt ∗ st.at A.repAlloc ∗ msg.at A.repAlloc ∗ memRegion ret 48 ∗
        A.pool lim (MC.stepEvents (evs0 ++ evs_fpb) st_cost) sm ∗
        memRegion (s0.sp - 4992#64) 352 ∗ ((s0.sp - 4640#64) ↦₆₄ w0) ∗ ((s0.sp - 4632#64) ↦₆₄ w1) ∗
        optVersionNegotiationPBTailAt A.repAlloc w0 w1 (s0.sp - 4624#64) pre_pb.versionNegotiation ∗
        optChainPBAt A.repAlloc (s0.sp - 4592#64) pre_pb.chain ∗
        memRegion (s0.sp - 4512#64) 224 ∗ memRegion (s0.sp - 4288#64) 176 ∗
        messageAt spqrPolyApi (s0.sp - 4112#64) sckaMsg ∗
        spqrRecvSavedRegs (s0.sp - 4992#64) s0
      refine step_post_statesFromPb_ok_1640_placed A F ext hC.memcpy_ok st0 s0_1736 sm _ F_rest _
        hs0_1736_align hpcm hrunm hspm' hx24_sm hx25_sm hx26_sm hx27_sm hx29_sm
        (by simp only [hs0_1736_sp, F_rest]; ac_rfl) ?_
      intro s1 hpc1 hrun1 hvm1 hsp1 htr1
        hx0_1 hx1_1 hx2_1 hx19_1 hx20_1 hx21_1 hx22_1 hx24_1 hx25_1 hx26_1 hx27_1 hx28_1 hx29_1
      apply ProofLib.SepWP.done hpc1 hrun1
      dsimp only [F_rest]
      rw [← A.pool_transport lim (MC.stepEvents (evs0 ++ evs_fpb) st_cost) sm s1 hvm1]
      exact hok_tail evs_fpb st0 s1 _ hevs_fpb hfrom hpc1 hrun1 hsp1 (traceVRegs_trans htr1 htr_sm')
        hx0_1 hx1_1 hx2_1
        (hx19_1.trans hx19_sm) (hx20_1.trans hx20_sm)
        (hx21_1.trans hx21_sm) (hx22_1.trans hx22_sm)
        hx24_1 hx25_1 hx26_1 hx27_1 hx28_1 hx29_1
        (by simp only [hs0_1736_sp]; ac_rfl)

theorem step_statesFromPb_1636_placed {MC : AllocCostModel}
    {H_inner : V1InnerHeapPred} {A : RustCliAllocBudget MC} {lim : BudgetLimits} {st_cost : MC.σ}
    {F : ShaCompress} {K : MlKem} {ext : String → Option (State → State)}
    (evs0 : List AllocEvent)
    (hC : SpqrRecvPlacedContracts H_inner A lim F K ext)
    (st msg : VecArg) (ret : BitVec 64)
    (pre : MsgPreamble) (pre_pb : PqRatchetState) (pb : V1State)
    (w0 w1 : BitVec 64) (sckaMsg : Message spqrPolyApi)
    (hpts : v1StatePtsBound pb)
    (hpre : msgPreamble msg.bytes = .ok pre)
    (hdec : spqrDecodeState st.bytes = .ok pre_pb)
    (hinner : pre_pb.inner = some (.v1 pb))
    (hmv : pre.version = 1#8)
    (hmin : ∀ vn, pre_pb.versionNegotiation = some vn → ¬(1#8 < vn.minVersion.truncate 8))
    (hmsg : Message.deserialize spqrPolyApi pre.epoch pre.remaining = .ok sckaMsg)
    (s0 s : State) (P R : SepProp)
    (hFit_fpb : FitsEnv MC lim (MC.stepEvents evs0 st_cost) (StatesFromPbEnv pb))
    (hevs_fpb : ∀ evs_fpb, StatesFromPbEnv pb evs_fpb → SpqrRecvEnv st msg (evs0 ++ evs_fpb))
    (hs0_align : s0.spAligned = true)
    (hpc : s.pc = spqrRecvPlacedEntry + 1636#64)
    (hrun : s.status = .Running) (hsp : s.sp = s0.sp - 4992#64) (htr : TraceVRegs s s0)
    (hx0 : s.readReg64 .x0 = s0.sp - 4512#64) (hx8 : s.readReg64 .x8 = s0.sp - 2096#64)
    (hx19 : s.readReg64 .x19 = ret) (hx20 : s.readReg64 .x20 = w0)
    (hx21 : s.readReg64 .x21 = pre.index.zeroExtend 64) (hx22 : s.readReg64 .x22 = pre.epoch)
    (hx24 : s.readReg64 .x24 = s0.sp - 2096#64) (hx25 : s.readReg64 .x25 = s0.sp - 4640#64)
    (hx26 : s.readReg64 .x26 = 0#64) (hx27 : s.readReg64 .x27 = s0.sp - 3056#64)
    (hx29 : s.readReg64 .x29 = s0.sp - 96#64)
    (hP : P =
      spqrRecvRoPlacedAt ∗ st.at A.repAlloc ∗ msg.at A.repAlloc ∗ memRegion ret 48 ∗
      A.pool lim (MC.stepEvents evs0 st_cost) s ∗
      stackAt (s0.sp - 4992#64) spqrRecvCalleeStackX ∗ memRegion (s0.sp - 4992#64) 352 ∗
      ((s0.sp - 4640#64) ↦₆₄ w0) ∗ ((s0.sp - 4632#64) ↦₆₄ w1) ∗
      optVersionNegotiationPBTailAt A.repAlloc w0 w1 (s0.sp - 4624#64) pre_pb.versionNegotiation ∗
      optChainPBAt A.repAlloc (s0.sp - 4592#64) pre_pb.chain ∗
      optProtoInnerStateAt A.repAlloc (s0.sp - 4512#64) pb.innerState ∗
      memRegion (s0.sp - 4288#64) 176 ∗ messageAt spqrPolyApi (s0.sp - 4112#64) sckaMsg ∗
      memRegion (s0.sp - 4064#64) 3968 ∗ spqrRecvSavedRegs (s0.sp - 4992#64) s0)
    (hok_tail : ∀ (evs_fpb : List AllocEvent) (st0 : States spqrPolyApi (spqrAuthApi F))
      (s1 : State) (P1 : SepProp),
      StatesFromPbEnv pb evs_fpb →
      States.from_pb spqrPolyApi (spqrAuthApi F) pb = .ok st0 →
      s1.pc = spqrRecvPlacedEntry + 1736#64 →
      s1.status = .Running → s1.sp = s0.sp - 4992#64 → TraceVRegs s1 s0 →
      s1.readReg64 .x0 = s0.sp - 3056#64 → s1.readReg64 .x1 = s0.sp - 1160#64 →
      s1.readReg64 .x2 = s0.sp - 4112#64 → s1.readReg64 .x19 = ret →
      s1.readReg64 .x20 = w0 → s1.readReg64 .x21 = pre.index.zeroExtend 64 →
      s1.readReg64 .x22 = pre.epoch → s1.readReg64 .x24 = s0.sp - 3056#64 →
      s1.readReg64 .x25 = s0.sp - 4640#64 → s1.readReg64 .x26 = s0.sp - 1160#64 →
      s1.readReg64 .x27 = s0.sp - 3056#64 → s1.readReg64 .x28 = 0#64 →
      s1.readReg64 .x29 = s0.sp - 96#64 →
      P1 = (spqrRecvRoPlacedAt ∗ st.at A.repAlloc ∗ msg.at A.repAlloc ∗ memRegion ret 48 ∗
        A.pool lim (MC.stepEvents (evs0 ++ evs_fpb) st_cost) s1 ∗
        stackAt (s0.sp - 4992#64) spqrRecvCalleeStackX ∗ memRegion (s0.sp - 4992#64) 352 ∗
        ((s0.sp - 4640#64) ↦₆₄ w0) ∗ ((s0.sp - 4632#64) ↦₆₄ w1) ∗
        optVersionNegotiationPBTailAt A.repAlloc w0 w1 (s0.sp - 4624#64) pre_pb.versionNegotiation ∗
        optChainPBAt A.repAlloc (s0.sp - 4592#64) pre_pb.chain ∗
        memRegion (s0.sp - 4512#64) 224 ∗ memRegion (s0.sp - 4288#64) 176 ∗
        messageAt spqrPolyApi (s0.sp - 4112#64) sckaMsg ∗
        memRegion (s0.sp - 4064#64) 2896 ∗ memRegion (s0.sp - 1168#64) 8 ∗
        chunkedStatesAt A.repAlloc (s0.sp - 1160#64) st0 ∗
        memRegion (s0.sp - 232#64) 136 ∗ spqrRecvSavedRegs (s0.sp - 4992#64) s0) →
      SepWPpLS (spqrRecvPlacedProg ext) (s0.readReg64 .x30) s1 P1
        (spqrRecvPlacedPost A lim st_cost (spqrV1Recv F K) st msg ret s0 R)
        (spqrRecvBudgetPanicPost (spqrV1Recv F K) st msg s0 R)) :
    SepWPpLS (spqrRecvPlacedProg ext) (s0.readReg64 .x30) s P
      (spqrRecvPlacedPost A lim st_cost (spqrV1Recv F K) st msg ret s0 R)
      (spqrRecvBudgetPanicPost (spqrV1Recv F K) st msg s0 R) :=
  step_statesFromPb_1636_placed_ofEnv (SpqrRecvEnv st msg) evs0
    hC st msg ret pre pre_pb pb w0 w1 sckaMsg hpts hpre hdec hinner hmv hmin hmsg
    s0 s P R hFit_fpb
    (fun evs_fpb _ hfpb hd => SpqrRecvEnv.append_freeOnly (hevs_fpb evs_fpb hfpb) hd)
    hs0_align hpc hrun hsp htr hx0 hx8 hx19 hx20 hx21 hx22 hx24 hx25 hx26 hx27 hx29 hP
    hok_tail

end LibsignalBinary.Proofs.SpqrV1.Top.Recv.V1Ratchet3PlacedBudgetAux
