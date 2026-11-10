/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SpqrV1.Top.Recv.V1Ratchet3PlacedBudgetAux
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
# Budget-Threaded Relocatable V1 Ratchet First-Half Composition (`+1532..+1856`)

Budget-threaded `<States>::recv` steppers (`+1736..+1856`) and full `+1532..+1856` composition
for `spqr::recv` (Block `329`).
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 400000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

namespace LibsignalBinary.Proofs.SpqrV1.Top.Recv.V1Ratchet3PlacedBudget

open Arm64 ProofLib ProofLib.ProgramReflection
open CryptoGames.LibsignalSession (ShaCompress)
open CryptoVerification
  (LibsignalCodeLoaded LibsignalPlacement lsmpl lsρ)
open CryptoVerification.LibsignalSpqrV1
  (Error Message MlKem MsgPreamble PqRatchetState States V1Recv V1State
   msgPreamble recvResultExactKeyAt spqrAuthApi spqrDecodeState spqrPolyApi spqrV1Recv)
open CryptoVerification.LibsignalTripleRatchet (VecArg framelessMemcpySpec)
open CryptoVerification.SpqrV1.Drop
  (chunkedStatesAt chunkedStatesSize optProtoInnerStateAt)
open CryptoVerification.SpqrV1.Prost.EncodeToVec (extractLsb_hi_append64 extractLsb_lo_append64)
open CryptoVerification.SpqrV1.Prost.MessageMerge (v1StateJumpTablesPlacedAt)
open CryptoVerification.SpqrV1.ProtoRepr (optChainPBAt)
open CryptoVerification.SpqrV1.States.FromPb (v1StatePtsBound)
open CryptoVerification.SpqrV1.States.IntoPb (StatesIntoPbGhost)
open CryptoVerification.SpqrV1.States.Leaves (relocatedHeap)
open CryptoVerification.SpqrV1.States.Recv
  (StatesRecvGhost optEpochSecretAt resultV1RecvAt statesRecvPreInv statesRecvStackX v1RecvAt)
open CryptoVerification.SpqrV1.Top.DecodeState
  (DecodeStateGhost TraceVRegs V1InnerHeapPred optVersionNegotiationPBTailAt)
open CryptoVerification.SpqrV1.Top.InitInner (InitInnerGhost)
open CryptoVerification.SpqrV1.Top.MessageSerialize (messageAt)
open CryptoVerification.SpqrV1.Top.Recv
  (MsgRemValid SepWPpLS chunkedStatesAt_entails_reloc_words hsp_add_544_eq hsp_add_560_eq
   memRegion_16_split memRegion_24_words3 memRegion_2896_split_statesRecv
   memRegion_2992_join_statesRecv_ok memRegion_4416_join_statesRecv_err
   memRegion_928_split_header32_body896 msgPreamble_epoch_beq_zero_false
   optEpochSecretAt_expose_words reassemble_chunkedStatesAt_words reassemble_src_928_after_memcpy
   recvCt2_spqrErrorByte_eq_zero_iff recv_chunkedStatesWord0_add_one_beq_zero recv_err_byte_foldX
   resultV1RecvAt_err_expose resultV1RecvAt_panic_false ret_48_split sp_sub_3056_add_928
   sp_sub_4992_aligned spqrRecvCalleeStackX spqrRecvPlacedEntry spqrRecvPlacedProg
   spqrRecvRoPlacedAt spqrRecvSavedRegs spqrV1Recv_v1_statesRecv_err spqrV1Recv_v1_statesRecv_panic
   stackAt_spqrRecvCallee_split statesFromPbJumpTablePlacedAt statesFromPb_noneCap_add_one_beq_zero
   statesIntoPbJumpTablePlacedAt statesRecvPreInv_of_spqrDecodeState statesRecvRoPlacedAt)
open CryptoVerification.SpqrV1.Top.Recv.Placed (blkPC_329 blkPl_329)
open CryptoVerification.SpqrV1.Top.Send
  (chunkedStatesTail920At chunkedStatesWord0 v1StatePtsBound_of_spqrDecodeState)
open LibsignalBinary.Heap
  (AllocCostModel AllocEvent BudgetLimits FitsEnv FreeOnlyEvs RustCliAllocBudget VmPreserved)
open LibsignalBinary.Proofs.SpqrV1.States.FromPb.DefsBudget (StatesFromPbEnv)
open LibsignalBinary.Proofs.SpqrV1.Top.Recv.DefsPlacedBudget
  (SpqrRecvPlacedContracts SpqrRecvPlacedContractsOfEnv StatesRecvEnv
   statesRecvBudgetOnPanic statesRecvPlacedSpecOfEnv)
open LibsignalBinary.Proofs.SpqrV1.Top.Recv.Part1PlacedBudget
  (SpqrRecvEnv sepWP_spqrRecvPlacedPostOfEnv_of_post0 spqrRecvBudgetPanicPost
   spqrRecvPlacedPost spqrRecvPlacedPost0 spqrRecvPlacedPost0OfEnv spqrRecvPlacedPostOfEnv)
open LibsignalBinary.Proofs.SpqrV1.Top.Recv.Part2PlacedBudget
  (SpqrRecvDropContractsBudget SpqrRecvEnv.append_freeOnly seq_vm_clean seq_vm_lscl)
open LibsignalBinary.Proofs.SpqrV1.Top.Recv.V1Ratchet1PlacedBudget
  (step_drop_vn_chain_2500_placed_ofEnv)
open LibsignalBinary.Proofs.SpqrV1.Top.Recv.V1Ratchet3PlacedBudgetAux
  (frame_pure_pre step_msgDeserialize_1532_placed step_msgDeserialize_1532_placed_ofEnv
   step_post_statesFromPb_err_1640_placed step_post_statesFromPb_err_1640_placed_ofEnv
   step_post_statesFromPb_ok_1640_placed step_statesFromPb_1636_placed
   step_statesFromPb_1636_placed_ofEnv toDropContractsBudget traceVRegs_trans)
open LibsignalBinary.Proofs.TripleRatchet.Wire.NewPureBudget (framelessMemcpyBudgetSpec)

export LibsignalBinary.Proofs.SpqrV1.Top.Recv.V1Ratchet3PlacedBudgetAux
  (step_msgDeserialize_1532_placed_ofEnv step_msgDeserialize_1532_placed
   step_post_statesFromPb_err_1640_placed_ofEnv step_post_statesFromPb_err_1640_placed)
export LibsignalBinary.Proofs.SpqrV1.Top.Recv.V1Ratchet3PlacedBudgetAux
  (step_post_statesFromPb_ok_1640_placed step_statesFromPb_1636_placed_ofEnv
   step_statesFromPb_1636_placed)

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

omit [LibsignalPlacement] in
private theorem onPanic_of_statesRecv_budget {F : ShaCompress} {K : MlKem}
    {st msg : VecArg} {pre : MsgPreamble} {pre_pb : PqRatchetState} {pb : V1State}
    {sckaMsg : Message spqrPolyApi} {st0 : States spqrPolyApi (spqrAuthApi F)}
    {outA selfA msgA : BitVec 64} {sc sf : State}
    (hpre : msgPreamble msg.bytes = .ok pre)
    (hdec : spqrDecodeState st.bytes = .ok pre_pb)
    (hinner : pre_pb.inner = some (.v1 pb))
    (hmv : pre.version = 1#8)
    (hmin : ∀ vn, pre_pb.versionNegotiation = some vn → ¬(1#8 < vn.minVersion.truncate 8))
    (hmsg : Message.deserialize spqrPolyApi pre.epoch pre.remaining = .ok sckaMsg)
    (hfrom : States.from_pb spqrPolyApi (spqrAuthApi F) pb = .ok st0) :
    statesRecvBudgetOnPanic K ⟨outA, selfA, msgA, st0, sckaMsg⟩ sc sf ⊢
      ⌜(spqrV1Recv F K).recvPanics st.bytes msg.bytes ∧ sc.trace <+: sf.trace⌝ ∗ anyHeap := by
  unfold statesRecvBudgetOnPanic
  apply Entails.pure_left
  rintro ⟨hp, hpref⟩
  refine Entails.pure_right ⟨?_, hpref⟩ (Entails.refl _)
  cases hr : st0.recv K sckaMsg with
  | ok _ => rw [hr] at hp; contradiction
  | error se =>
    cases se with
    | err _ => rw [hr] at hp; contradiction
    | panic p =>
      exact spqrV1Recv_v1_statesRecv_panic F K hpre hdec hinner hmv hmin hmsg hfrom hr

/-! ## 1. `<States>::recv` Call, Error Path (`+2472 -> +2500`), and Relocation (`+1736..+1856`) -/

/-- Envelope-parametric error branch after `<States>::recv` returns `.error (.err err)` at
    `+1740 .. +1764 -> +2472 .. +2500`. -/
theorem step_post_statesRecv_err_1740_placed_ofEnv {MC : AllocCostModel}
    (A : RustCliAllocBudget MC) (lim : BudgetLimits) (st_cost : MC.σ)
    (Env : List AllocEvent → Prop) (evs0 : List AllocEvent)
    (hevs_free : ∀ evs_d, FreeOnlyEvs evs_d → Env (evs0 ++ evs_d))
    (F : ShaCompress) (K : MlKem)
    (ext : String → Option (State → State))
    (hC : SpqrRecvDropContractsBudget A lim F ext)
    (st msg : VecArg) (ret : BitVec 64)
    (pre : MsgPreamble) (pre_pb : PqRatchetState) (pb : V1State) (w0 w1 : BitVec 64)
    (sckaMsg : Message spqrPolyApi) (st0 : States spqrPolyApi (spqrAuthApi F)) (err : Error)
    (hpre : msgPreamble msg.bytes = .ok pre)
    (hdec : spqrDecodeState st.bytes = .ok pre_pb)
    (hinner : pre_pb.inner = some (.v1 pb))
    (hmv : pre.version = 1#8)
    (hmin : ∀ vn, pre_pb.versionNegotiation = some vn → ¬(1#8 < vn.minVersion.truncate 8))
    (hmsg : Message.deserialize spqrPolyApi pre.epoch pre.remaining = .ok sckaMsg)
    (hst0 : States.from_pb spqrPolyApi (spqrAuthApi F) pb = .ok st0)
    (hrecv : States.recv K st0 sckaMsg = .error (.err err))
    (s0 s : State) (P R : SepProp) (post : State → SepProp → Prop)
    (hpost : post = spqrRecvPlacedPost0OfEnv A lim st_cost Env (spqrV1Recv F K) st msg ret s0 R)
    (hs0_align : s0.spAligned = true)
    (hpc : s.pc = spqrRecvPlacedEntry + 1740#64)
    (hrun : s.status = .Running) (hsp : s.sp = s0.sp - 4992#64) (htr : TraceVRegs s s0)
    (hx19 : s.readReg64 .x19 = ret) (hx25 : s.readReg64 .x25 = s0.sp - 4640#64)
    (hx27 : s.readReg64 .x27 = s0.sp - 3056#64) (hx28 : s.readReg64 .x28 = 0#64)
    (hP : P =
      spqrRecvRoPlacedAt ∗ st.at A.repAlloc ∗ msg.at A.repAlloc ∗ memRegion ret 48 ∗
      A.pool lim (MC.stepEvents evs0 st_cost) s ∗
      stackAt (s0.sp - 4992#64) spqrRecvCalleeStackX ∗ memRegion (s0.sp - 4992#64) 352 ∗
      ((s0.sp - 4640#64) ↦₆₄ w0) ∗ ((s0.sp - 4632#64) ↦₆₄ w1) ∗
      optVersionNegotiationPBTailAt A.repAlloc w0 w1 (s0.sp - 4624#64) pre_pb.versionNegotiation ∗
      optChainPBAt A.repAlloc (s0.sp - 4592#64) pre_pb.chain ∗
      memRegion (s0.sp - 4512#64) 224 ∗ memRegion (s0.sp - 4288#64) 176 ∗
      messageAt spqrPolyApi (s0.sp - 4112#64) sckaMsg ∗
      memRegion (s0.sp - 4064#64) 32 ∗ memRegion (s0.sp - 4032#64) 16 ∗
      memRegion (s0.sp - 4016#64) 928 ∗ memRegion (s0.sp - 3088#64) 24 ∗
      memRegion (s0.sp - 3064#64) 8 ∗
      resultV1RecvAt A.repAlloc (F := F) (s0.sp - 3056#64) (.error (.err err)) ∗
      memRegion (s0.sp - 2096#64) 928 ∗ memRegion (s0.sp - 1168#64) 8 ∗
      memRegion (s0.sp - 1160#64) 928 ∗ memRegion (s0.sp - 232#64) 136 ∗
      spqrRecvSavedRegs (s0.sp - 4992#64) s0)
    (hcl : LibsignalCodeLoaded lsmpl s.mem) :
    SepWP (spqrRecvPlacedProg ext) (s0.readReg64 .x30) s P post := by
  have hfsp_align : ((s0.sp - 4992#64) &&& 15#64 == 0#64) = true :=
    sp_sub_4992_aligned s0 hs0_align
  subst hP
  have hexp_err := resultV1RecvAt_err_expose A.repAlloc (F := F) (s0.sp - 3056#64) err
  rw [bv_sub_add_lit s0.sp 3056 8, bv_sub_add_lit s0.sp 3056 16,
      bv_sub_add_lit s0.sp 3056 24, bv_sub_add_lit s0.sp 3056 32] at hexp_err
  simp only [Nat.reduceSub, BitVec.ofNat_eq_ofNat] at hexp_err
  refine SepWP.focus_weaken hexp_err (by sep_focus) ?_
  wp_pull_exists; rename_i w1_err w2_err w3_err
  wp_focus_pure; intro hw1_err
  have h24_scr := memRegion_24_words3 (s0.sp - 3088#64)
  rw [bv_sub_add_lit s0.sp 3088 8, bv_sub_add_lit s0.sp 3088 16] at h24_scr
  simp only [Nat.reduceSub, BitVec.ofNat_eq_ofNat] at h24_scr
  refine SepWP.focus_weaken (Entails.of_eq h24_scr) (by sep_focus) ?_
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
      wp_steps 14
      refine SepWP.focus_weaken (hw1_err ret) (by sep_focus) ?_
      refine SepWP.focus_weaken
        (recv_err_byte_foldX A.repAlloc ret w2_err w3_err
          (CryptoVerification.SpqrV1.States.RecvCt2Chunk.spqrErrorByte err)
          (err == .stateDecode) (recvCt2_spqrErrorByte_eq_zero_iff err))
        (by sep_focus) ?_
      have hres_eq : recvResultExactKeyAt A.repAlloc ret (.error (err == .stateDecode)) =
          recvResultExactKeyAt A.repAlloc ret ((spqrV1Recv F K).recv st.bytes msg.bytes) := by
        rw [(spqrV1Recv_v1_statesRecv_err F K hpre hdec hinner hmv hmin hmsg hst0 hrecv).1]
      rw [hres_eq]
      refine SepWP.focus_weaken (memRegion_4416_join_statesRecv_err s0.sp w1_err w2_err w3_err sckaMsg) (by sep_focus) ?_
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

theorem step_post_statesRecv_err_1740_placed {MC : AllocCostModel}
    (A : RustCliAllocBudget MC) (lim : BudgetLimits) (st_cost : MC.σ)
    (F : ShaCompress) (K : MlKem)
    (ext : String → Option (State → State))
    (hC : SpqrRecvDropContractsBudget A lim F ext)
    (st msg : VecArg) (ret : BitVec 64)
    (evs0 : List AllocEvent) (hevs0 : SpqrRecvEnv st msg evs0)
    (pre : MsgPreamble) (pre_pb : PqRatchetState) (pb : V1State) (w0 w1 : BitVec 64)
    (sckaMsg : Message spqrPolyApi) (st0 : States spqrPolyApi (spqrAuthApi F)) (err : Error)
    (hpre : msgPreamble msg.bytes = .ok pre)
    (hdec : spqrDecodeState st.bytes = .ok pre_pb)
    (hinner : pre_pb.inner = some (.v1 pb))
    (hmv : pre.version = 1#8)
    (hmin : ∀ vn, pre_pb.versionNegotiation = some vn → ¬(1#8 < vn.minVersion.truncate 8))
    (hmsg : Message.deserialize spqrPolyApi pre.epoch pre.remaining = .ok sckaMsg)
    (hst0 : States.from_pb spqrPolyApi (spqrAuthApi F) pb = .ok st0)
    (hrecv : States.recv K st0 sckaMsg = .error (.err err))
    (s0 s : State) (P R : SepProp) (post : State → SepProp → Prop)
    (hpost : post = spqrRecvPlacedPost0 A lim st_cost (spqrV1Recv F K) st msg ret s0 R)
    (hs0_align : s0.spAligned = true)
    (hpc : s.pc = spqrRecvPlacedEntry + 1740#64)
    (hrun : s.status = .Running) (hsp : s.sp = s0.sp - 4992#64) (htr : TraceVRegs s s0)
    (hx19 : s.readReg64 .x19 = ret) (hx25 : s.readReg64 .x25 = s0.sp - 4640#64)
    (hx27 : s.readReg64 .x27 = s0.sp - 3056#64) (hx28 : s.readReg64 .x28 = 0#64)
    (hP : P =
      spqrRecvRoPlacedAt ∗ st.at A.repAlloc ∗ msg.at A.repAlloc ∗ memRegion ret 48 ∗
      A.pool lim (MC.stepEvents evs0 st_cost) s ∗
      stackAt (s0.sp - 4992#64) spqrRecvCalleeStackX ∗ memRegion (s0.sp - 4992#64) 352 ∗
      ((s0.sp - 4640#64) ↦₆₄ w0) ∗ ((s0.sp - 4632#64) ↦₆₄ w1) ∗
      optVersionNegotiationPBTailAt A.repAlloc w0 w1 (s0.sp - 4624#64) pre_pb.versionNegotiation ∗
      optChainPBAt A.repAlloc (s0.sp - 4592#64) pre_pb.chain ∗
      memRegion (s0.sp - 4512#64) 224 ∗ memRegion (s0.sp - 4288#64) 176 ∗
      messageAt spqrPolyApi (s0.sp - 4112#64) sckaMsg ∗
      memRegion (s0.sp - 4064#64) 32 ∗ memRegion (s0.sp - 4032#64) 16 ∗
      memRegion (s0.sp - 4016#64) 928 ∗ memRegion (s0.sp - 3088#64) 24 ∗
      memRegion (s0.sp - 3064#64) 8 ∗
      resultV1RecvAt A.repAlloc (F := F) (s0.sp - 3056#64) (.error (.err err)) ∗
      memRegion (s0.sp - 2096#64) 928 ∗ memRegion (s0.sp - 1168#64) 8 ∗
      memRegion (s0.sp - 1160#64) 928 ∗ memRegion (s0.sp - 232#64) 136 ∗
      spqrRecvSavedRegs (s0.sp - 4992#64) s0)
    (hcl : LibsignalCodeLoaded lsmpl s.mem) :
    SepWP (spqrRecvPlacedProg ext) (s0.readReg64 .x30) s P post :=
  step_post_statesRecv_err_1740_placed_ofEnv A lim st_cost (SpqrRecvEnv st msg) evs0
    (fun _ hd => SpqrRecvEnv.append_freeOnly hevs0 hd)
    F K ext hC st msg ret pre pre_pb pb w0 w1 sckaMsg st0 err
    hpre hdec hinner hmv hmin hmsg hst0 hrecv s0 s P R post hpost hs0_align
    hpc hrun hsp htr hx19 hx25 hx27 hx28 hP hcl

/-- Ok branch after `<States>::recv` returns `.ok v` at `+1740 .. +1856`, supplying `VmPreserved
    s s1` to `hnext` so budget callers can transport `A.pool` across the relocation. -/
theorem step_post_statesRecv_ok_1740_placed {MC : AllocCostModel}
    (A : RustCliAllocBudget MC) (F : ShaCompress)
    (ext : String → Option (State → State))
    (hmemcpy_ok : subroutine_ok (spqrRecvPlacedProg ext) (lsρ "memcpy") framelessMemcpyBudgetSpec)
    (pre : MsgPreamble) (w0 : BitVec 64)
    (v : V1Recv spqrPolyApi (spqrAuthApi F))
    (hep0 : (pre.epoch == 0#64) = false)
    (s0 s : State) (P F_rest : SepProp) (post : State → SepProp → Prop)
    (hs0_align : s0.spAligned = true)
    (hpc : s.pc = spqrRecvPlacedEntry + 1740#64)
    (hrun : s.status = .Running) (hsp : s.sp = s0.sp - 4992#64)
    (hx22 : s.readReg64 .x22 = pre.epoch) (hx24 : s.readReg64 .x24 = s0.sp - 3056#64)
    (hx27 : s.readReg64 .x27 = s0.sp - 3056#64)
    (hP : P =
      stackAt (s0.sp - 4992#64) spqrRecvCalleeStackX ∗
      ((s0.sp - 4640#64) ↦₆₄ w0) ∗
      memRegion (s0.sp - 4032#64) 16 ∗ memRegion (s0.sp - 4016#64) 928 ∗
      memRegion (s0.sp - 3088#64) 24 ∗ memRegion (s0.sp - 3064#64) 8 ∗
      resultV1RecvAt A.repAlloc (F := F) (s0.sp - 3056#64) (.ok v) ∗
      memRegion (s0.sp - 2096#64) 928 ∗ memRegion (s0.sp - 1168#64) 8 ∗
      memRegion (s0.sp - 1160#64) 928 ∗ memRegion (s0.sp - 232#64) 136 ∗ F_rest)
    (hnext : ∀ (kw0 kw1 kw2 kw3 : BitVec 64) (P_key : SepProp) (s1 : State),
      (∀ dst : BitVec 64,
        (dst ↦₆₄ kw0) ∗ ((dst + 8#64) ↦₆₄ kw1) ∗ ((dst + 16#64) ↦₆₄ kw2) ∗ ((dst + 24#64) ↦₆₄ kw3) ∗ P_key ⊢
          optEpochSecretAt A.repAlloc dst v.key) →
      s1.pc = spqrRecvPlacedEntry + 1856#64 →
      s1.status = .Running → VmPreserved s s1 →
      s1.sp = s0.sp - 4992#64 → TraceVRegs s1 s →
      s1.readReg64 .x0 = s0.sp - 3056#64 → s1.readReg64 .x1 = s0.sp - 4592#64 →
      s1.readReg64 .x2 = (if (w0 + 1#64 == 0#64) then 0#64 else s0.sp - 4640#64) →
      s1.readReg64 .x19 = s.readReg64 .x19 → s1.readReg64 .x20 = s.readReg64 .x20 →
      s1.readReg64 .x21 = s.readReg64 .x21 → s1.readReg64 .x22 = pre.epoch →
      s1.readReg64 .x23 = w0 → s1.readReg64 .x24 = kw0 →
      s1.readReg64 .x25 = kw1 → s1.readReg64 .x26 = s.readReg64 .x26 →
      s1.readReg64 .x27 = s0.sp - 3056#64 → s1.readReg64 .x28 = s.readReg64 .x28 →
      s1.readReg64 .x29 = s.readReg64 .x29 →
      SepWP (spqrRecvPlacedProg ext) (s0.readReg64 .x30) s1
        (stackAt (s0.sp - 4992#64) spqrRecvCalleeStackX ∗
          ((s0.sp - 4640#64) ↦₆₄ w0) ∗
          ((s0.sp - 4032#64) ↦₆₄ kw2) ∗ ((s0.sp - 4024#64) ↦₆₄ kw3) ∗ P_key ∗
          chunkedStatesAt A.repAlloc (s0.sp - 4016#64) v.state ∗
          memRegion (s0.sp - 3088#64) 2992 ∗ F_rest) post) :
    SepWP (spqrRecvPlacedProg ext) (s0.readReg64 .x30) s P post := by
  have hmemcpy_raw := hmemcpy_ok
  simp only [framelessMemcpyBudgetSpec, framelessMemcpySpec] at hmemcpy_raw
  have hfsp_align : ((s0.sp - 4992#64) &&& 15#64 == 0#64) = true :=
    sp_sub_4992_aligned s0 hs0_align
  subst hP
  dsimp only [resultV1RecvAt, v1RecvAt]
  rw [sp_sub_3056_add_928 s0.sp]
  have hreloc := chunkedStatesAt_entails_reloc_words A.repAlloc (s0.sp - 3056#64) v.state
  rw [bv_sub_add_lit s0.sp 3056 8, bv_sub_add_lit s0.sp 3056 16,
      bv_sub_add_lit s0.sp 3056 24, bv_sub_add_lit s0.sp 3056 32] at hreloc
  simp only [Nat.reduceSub, BitVec.ofNat_eq_ofNat] at hreloc
  refine SepWP.focus_weaken hreloc (by sep_focus) ?_
  wp_pull_exists; rename_i bs w1_st w2_st w3_st bs896
  wp_focus_pure; rintro ⟨hbs, hbs896⟩
  have hexp_key := optEpochSecretAt_expose_words A.repAlloc (s0.sp - 2128#64) v.key
  rw [bv_sub_add_lit s0.sp 2128 8, bv_sub_add_lit s0.sp 2128 16,
      bv_sub_add_lit s0.sp 2128 24] at hexp_key
  simp only [Nat.reduceSub, BitVec.ofNat_eq_ofNat] at hexp_key
  refine SepWP.focus_weaken hexp_key (by sep_focus) ?_
  wp_pull_exists; rename_i kw0 kw1 kw2 kw3 P_key
  wp_focus_pure; intro hfold_key
  have h16_key := memRegion_16_split (s0.sp - 4032#64)
  rw [bv_sub_add_lit s0.sp 4032 8] at h16_key
  simp only [Nat.reduceSub, BitVec.ofNat_eq_ofNat] at h16_key
  refine SepWP.focus_weaken (Entails.of_eq h16_key) (by sep_focus) ?_
  wp_pull_exists; rename_i kd1 kd0
  have h928_dst := memRegion_928_split_header32_body896 (s0.sp - 4016#64)
  rw [bv_sub_add_lit s0.sp 4016 8, bv_sub_add_lit s0.sp 4016 16,
      bv_sub_add_lit s0.sp 4016 24, bv_sub_add_lit s0.sp 4016 32] at h928_dst
  simp only [Nat.reduceSub, BitVec.ofNat_eq_ofNat] at h928_dst
  refine SepWP.focus_weaken h928_dst (by sep_focus) ?_
  wp_pull_exists; rename_i d0 d1 d2 d3
  have h24_scr := memRegion_24_words3 (s0.sp - 3088#64)
  rw [bv_sub_add_lit s0.sp 3088 8, bv_sub_add_lit s0.sp 3088 16] at h24_scr
  simp only [Nat.reduceSub, BitVec.ofNat_eq_ofNat] at h24_scr
  refine SepWP.focus_weaken (Entails.of_eq h24_scr) (by sep_focus) ?_
  wp_pull_exists; rename_i f2 f1 f0
  have h896_dst : memRegion (s0.sp - 3984#64) 896 = memRegion (s0.sp - 3984#64) bs896.length := by
    rw [hbs896]
  rw [h896_dst]
  have hlen_lt : bs896.length < 2 ^ 64 := by rw [hbs896]; decide
  have hlen_eq : (896#64 : BitVec 64).toNat = bs896.length := hbs896.symm
  dsimp only [spqrRecvPlacedProg, spqrRecvPlacedEntry, BitVec.ofNat_eq_ofNat] at hmemcpy_raw hpc hnext ⊢
  refine seq_vm_clean (mid := lsρ "memcpy")
    (P_mid :=
      stackAt (s0.sp - 4992#64) spqrRecvCalleeStackX ∗
      ((s0.sp - 4640#64) ↦₆₄ w0) ∗
      ((s0.sp - 4032#64) ↦₆₄ kd0) ∗ ((s0.sp - 4024#64) ↦₆₄ kd1) ∗
      ((s0.sp - 4016#64) ↦₆₄ d0) ∗ ((s0.sp - 4008#64) ↦₆₄ d1) ∗
      ((s0.sp - 4000#64) ↦₆₄ d2) ∗ ((s0.sp - 3992#64) ↦₆₄ d3) ∗
      memRegion (s0.sp - 3984#64) bs896.length ∗
      ((s0.sp - 3088#64) ↦₆₄ w1_st) ∗ ((s0.sp - 3080#64) ↦₆₄ w2_st) ∗ ((s0.sp - 3072#64) ↦₆₄ w3_st) ∗
      memRegion (s0.sp - 3064#64) 8 ∗
      ((s0.sp - 3056#64) ↦₆₄ chunkedStatesWord0 v.state) ∗
      ((s0.sp - 3048#64) ↦₆₄ w1_st) ∗ ((s0.sp - 3040#64) ↦₆₄ w2_st) ∗
      ((s0.sp - 3032#64) ↦₆₄ w3_st) ∗ ((s0.sp - 3024#64) ↦ₛ bs896) ∗
      relocatedHeap (fun dst => chunkedStatesTail920At A.repAlloc dst v.state) bs ∗
      P_key ∗
      ((s0.sp - 2128#64) ↦₆₄ kw0) ∗ ((s0.sp - 2120#64) ↦₆₄ kw1) ∗
      ((s0.sp - 2112#64) ↦₆₄ kw2) ∗ ((s0.sp - 2104#64) ↦₆₄ kw3) ∗
      memRegion (s0.sp - 2096#64) 928 ∗ memRegion (s0.sp - 1168#64) 8 ∗
      memRegion (s0.sp - 1160#64) 928 ∗ memRegion (s0.sp - 232#64) 136 ∗ F_rest)
    (Q := fun s_mc =>
      s_mc.sp = s0.sp - 4992#64 ∧
      TraceVRegs s_mc s ∧
      s_mc.readReg64 .x0 = s0.sp - 3984#64 ∧
      s_mc.readReg64 .x1 = s0.sp - 3024#64 ∧
      s_mc.readReg64 .x2 = 896#64 ∧
      s_mc.readReg64 .x30 = (blkPl_329).base + 1788#64 ∧
      s_mc.readReg64 .x19 = s.readReg64 .x19 ∧
      s_mc.readReg64 .x20 = s.readReg64 .x20 ∧
      s_mc.readReg64 .x21 = s.readReg64 .x21 ∧
      s_mc.readReg64 .x22 = pre.epoch ∧
      s_mc.readReg64 .x23 = chunkedStatesWord0 v.state ∧
      s_mc.readReg64 .x26 = s.readReg64 .x26 ∧
      s_mc.readReg64 .x27 = s0.sp - 3056#64 ∧
      s_mc.readReg64 .x28 = s.readReg64 .x28 ∧
      s_mc.readReg64 .fp = s.readReg64 .fp) ?_ ?_
  · by_vm_steps (
      wp_steps 12
      refine ProofLib.SepWP.done (by simp only [wp_norm, arm64_norm, *])
        (by simp only [wp_norm, arm64_norm, *])
        ⟨by simp only [wp_norm, arm64_norm],
         Entails.of_eq (by sep_ac_rfl), ?_⟩
      refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
      all_goals first | rfl | simp only [wp_norm, arm64_norm, *]
    )
  · intro s_mc hpc_mc hrun_mc hvm1
      ⟨hsp_mc, htr_mc, hx0_mc, hx1_mc, hx2_mc, hlr_mc,
       hx19_mc, hx20_mc, hx21_mc, hx22_mc, hx23_mc, hx26_mc, hx27_mc, hx28_mc, hfp_mc⟩
    have hs_mc_align : s_mc.spAligned = true := by
      rw [State.spAligned, hsp_mc]; exact hfsp_align
    wp_call hmemcpy_raw ⟨s0.sp - 3984#64, s0.sp - 3024#64, bs896⟩
    have hvm2 := ‹VmPreserved s_mc _›
    let s_post : State := (fun {a b : State} (_ : VmPreserved a b) => b) hvm2
    have hvm2' : VmPreserved s_mc s_post := hvm2
    refine seq_vm_clean (mid := (blkPl_329).base + 1856#64)
      (P_mid :=
        stackAt (s0.sp - 4992#64) spqrRecvCalleeStackX ∗
        ((s0.sp - 4640#64) ↦₆₄ w0) ∗
        ((s0.sp - 4032#64) ↦₆₄ kw2) ∗ ((s0.sp - 4024#64) ↦₆₄ kw3) ∗ P_key ∗
        chunkedStatesAt A.repAlloc (s0.sp - 4016#64) v.state ∗
        memRegion (s0.sp - 3088#64) 2992 ∗ F_rest)
      (Q := fun s1 =>
        s1.sp = s0.sp - 4992#64 ∧
        TraceVRegs s1 s ∧
        s1.readReg64 .x0 = s0.sp - 3056#64 ∧
        s1.readReg64 .x1 = s0.sp - 4592#64 ∧
        s1.readReg64 .x2 = (if (w0 + 1#64 == 0#64) then 0#64 else s0.sp - 4640#64) ∧
        s1.readReg64 .x19 = s.readReg64 .x19 ∧
        s1.readReg64 .x20 = s.readReg64 .x20 ∧
        s1.readReg64 .x21 = s.readReg64 .x21 ∧
        s1.readReg64 .x22 = pre.epoch ∧
        s1.readReg64 .x23 = w0 ∧
        s1.readReg64 .x24 = kw0 ∧
        s1.readReg64 .x25 = kw1 ∧
        s1.readReg64 .x26 = s.readReg64 .x26 ∧
        s1.readReg64 .x27 = s0.sp - 3056#64 ∧
        s1.readReg64 .x28 = s.readReg64 .x28 ∧
        s1.readReg64 .x29 = s.readReg64 .x29) ?_ ?_
    · by_vm_steps (
        wp_steps 17
        have hreassemble_dst := reassemble_chunkedStatesAt_words A.repAlloc (s0.sp - 4016#64) v.state w1_st w2_st w3_st hbs
        rw [bv_sub_add_lit s0.sp 4016 8, bv_sub_add_lit s0.sp 4016 16,
            bv_sub_add_lit s0.sp 4016 24, bv_sub_add_lit s0.sp 4016 32] at hreassemble_dst
        simp only [Nat.reduceSub, BitVec.ofNat_eq_ofNat] at hreassemble_dst
        refine SepWP.focus_weaken hreassemble_dst (by sep_focus) ?_
        have hreassemble_src := reassemble_src_928_after_memcpy (s0.sp - 3056#64) (chunkedStatesWord0 v.state) w1_st w2_st w3_st hbs896
        rw [bv_sub_add_lit s0.sp 3056 8, bv_sub_add_lit s0.sp 3056 16,
            bv_sub_add_lit s0.sp 3056 24, bv_sub_add_lit s0.sp 3056 32] at hreassemble_src
        simp only [Nat.reduceSub, BitVec.ofNat_eq_ofNat] at hreassemble_src
        refine SepWP.focus_weaken hreassemble_src (by sep_focus) ?_
        refine SepWP.focus_weaken (memRegion_2992_join_statesRecv_ok s0.sp w1_st w2_st w3_st kw0 kw1 kw2 kw3) (by sep_focus) ?_
        refine ProofLib.SepWP.done (by simp only [wp_norm, arm64_norm]; try rfl)
          (by simp only [wp_norm, arm64_norm, *])
          ⟨by simp only [wp_norm, arm64_norm],
           Entails.of_eq (by sep_ac_rfl), ?_⟩
        refine ⟨?_, ⟨?_, ?_⟩, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
        all_goals first | rfl | (change _ = s.readReg64 .fp; simp only [wp_norm, arm64_norm, *]) | simp only [htr_mc.1, htr_mc.2, wp_norm, arm64_norm, *]
      )
    · intro s1 hpc1 hrun1 hvm3
        ⟨hsp1, htr1, hx0_1, hx1_1, hx2_1, hx19_1, hx20_1, hx21_1, hx22_1,
         hx23_1, hx24_1, hx25_1, hx26_1, hx27_1, hx28_1, hx29_1⟩
      exact hnext kw0 kw1 kw2 kw3 P_key s1 hfold_key hpc1 hrun1 (hvm1.trans (hvm2'.trans hvm3))
        hsp1 htr1 hx0_1 hx1_1 hx2_1 hx19_1 hx20_1 hx21_1 hx22_1 hx23_1 hx24_1 hx25_1
        hx26_1 hx27_1 hx28_1 hx29_1

/-- Envelope-parametric budget-threaded `<States>::recv` step (`+1736 .. +1856`, error via
    `+2500`). -/
theorem step_statesRecv_1736_placed_ofEnv {MC : AllocCostModel}
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
    (w0 w1 : BitVec 64) (sckaMsg : Message spqrPolyApi) (st0 : States spqrPolyApi (spqrAuthApi F))
    (hinv : statesRecvPreInv st0)
    (hpre : msgPreamble msg.bytes = .ok pre)
    (hdec : spqrDecodeState st.bytes = .ok pre_pb)
    (hinner : pre_pb.inner = some (.v1 pb))
    (hmv : pre.version = 1#8)
    (hmin : ∀ vn, pre_pb.versionNegotiation = some vn → ¬(1#8 < vn.minVersion.truncate 8))
    (hmsg : Message.deserialize spqrPolyApi pre.epoch pre.remaining = .ok sckaMsg)
    (hfrom : States.from_pb spqrPolyApi (spqrAuthApi F) pb = .ok st0)
    (s0 s : State) (P R : SepProp)
    (hFit_rcv : FitsEnv MC lim (MC.stepEvents evs0 st_cost)
      (RecvEnv ⟨s0.sp - 3056#64, s0.sp - 1160#64, s0.sp - 4112#64, st0, sckaMsg⟩))
    (hevs_err : ∀ evs_rcv evs_d,
      RecvEnv ⟨s0.sp - 3056#64, s0.sp - 1160#64, s0.sp - 4112#64, st0, sckaMsg⟩ evs_rcv →
      FreeOnlyEvs evs_d → Env ((evs0 ++ evs_rcv) ++ evs_d))
    (hs0_align : s0.spAligned = true)
    (hpc : s.pc = spqrRecvPlacedEntry + 1736#64)
    (hrun : s.status = .Running) (hsp : s.sp = s0.sp - 4992#64) (htr : TraceVRegs s s0)
    (hx0 : s.readReg64 .x0 = s0.sp - 3056#64) (hx1 : s.readReg64 .x1 = s0.sp - 1160#64)
    (hx2 : s.readReg64 .x2 = s0.sp - 4112#64) (hx19 : s.readReg64 .x19 = ret)
    (hx20 : s.readReg64 .x20 = w0) (hx21 : s.readReg64 .x21 = pre.index.zeroExtend 64)
    (hx22 : s.readReg64 .x22 = pre.epoch) (hx24 : s.readReg64 .x24 = s0.sp - 3056#64)
    (hx25 : s.readReg64 .x25 = s0.sp - 4640#64) (hx26 : s.readReg64 .x26 = s0.sp - 1160#64)
    (hx27 : s.readReg64 .x27 = s0.sp - 3056#64) (hx28 : s.readReg64 .x28 = 0#64)
    (hx29 : s.readReg64 .x29 = s0.sp - 96#64)
    (hP : P =
      spqrRecvRoPlacedAt ∗ st.at A.repAlloc ∗ msg.at A.repAlloc ∗ memRegion ret 48 ∗
      A.pool lim (MC.stepEvents evs0 st_cost) s ∗
      stackAt (s0.sp - 4992#64) spqrRecvCalleeStackX ∗ memRegion (s0.sp - 4992#64) 352 ∗
      ((s0.sp - 4640#64) ↦₆₄ w0) ∗ ((s0.sp - 4632#64) ↦₆₄ w1) ∗
      optVersionNegotiationPBTailAt A.repAlloc w0 w1 (s0.sp - 4624#64) pre_pb.versionNegotiation ∗
      optChainPBAt A.repAlloc (s0.sp - 4592#64) pre_pb.chain ∗
      memRegion (s0.sp - 4512#64) 224 ∗ memRegion (s0.sp - 4288#64) 176 ∗
      messageAt spqrPolyApi (s0.sp - 4112#64) sckaMsg ∗
      memRegion (s0.sp - 4064#64) 2896 ∗ memRegion (s0.sp - 1168#64) 8 ∗
      chunkedStatesAt A.repAlloc (s0.sp - 1160#64) st0 ∗
      memRegion (s0.sp - 232#64) 136 ∗ spqrRecvSavedRegs (s0.sp - 4992#64) s0)
    (hok_tail : ∀ (evs_rcv : List AllocEvent) (v : V1Recv spqrPolyApi (spqrAuthApi F))
      (kw0 kw1 kw2 kw3 : BitVec 64) (P_key : SepProp) (s1 : State) (P1 : SepProp),
      RecvEnv ⟨s0.sp - 3056#64, s0.sp - 1160#64, s0.sp - 4112#64, st0, sckaMsg⟩ evs_rcv →
      States.recv K st0 sckaMsg = .ok v →
      (∀ dst : BitVec 64,
        (dst ↦₆₄ kw0) ∗ ((dst + 8#64) ↦₆₄ kw1) ∗ ((dst + 16#64) ↦₆₄ kw2) ∗ ((dst + 24#64) ↦₆₄ kw3) ∗ P_key ⊢
          optEpochSecretAt A.repAlloc dst v.key) →
      s1.pc = spqrRecvPlacedEntry + 1856#64 →
      s1.status = .Running → s1.sp = s0.sp - 4992#64 → TraceVRegs s1 s0 →
      s1.readReg64 .x0 = s0.sp - 3056#64 → s1.readReg64 .x1 = s0.sp - 4592#64 →
      s1.readReg64 .x2 = (if (w0 + 1#64 == 0#64) then 0#64 else s0.sp - 4640#64) →
      s1.readReg64 .x19 = ret → s1.readReg64 .x20 = w0 →
      s1.readReg64 .x21 = pre.index.zeroExtend 64 → s1.readReg64 .x22 = pre.epoch →
      s1.readReg64 .x23 = w0 → s1.readReg64 .x24 = kw0 →
      s1.readReg64 .x25 = kw1 → s1.readReg64 .x26 = s0.sp - 1160#64 →
      s1.readReg64 .x27 = s0.sp - 3056#64 → s1.readReg64 .x28 = 0#64 →
      s1.readReg64 .x29 = s0.sp - 96#64 →
      P1 = (spqrRecvRoPlacedAt ∗ st.at A.repAlloc ∗ msg.at A.repAlloc ∗ memRegion ret 48 ∗
        A.pool lim (MC.stepEvents (evs0 ++ evs_rcv) st_cost) s1 ∗
        stackAt (s0.sp - 4992#64) spqrRecvCalleeStackX ∗ memRegion (s0.sp - 4992#64) 352 ∗
        ((s0.sp - 4640#64) ↦₆₄ w0) ∗ ((s0.sp - 4632#64) ↦₆₄ w1) ∗
        optVersionNegotiationPBTailAt A.repAlloc w0 w1 (s0.sp - 4624#64) pre_pb.versionNegotiation ∗
        optChainPBAt A.repAlloc (s0.sp - 4592#64) pre_pb.chain ∗
        memRegion (s0.sp - 4512#64) 224 ∗ memRegion (s0.sp - 4288#64) 176 ∗
        messageAt spqrPolyApi (s0.sp - 4112#64) sckaMsg ∗ memRegion (s0.sp - 4064#64) 32 ∗
        ((s0.sp - 4032#64) ↦₆₄ kw2) ∗ ((s0.sp - 4024#64) ↦₆₄ kw3) ∗ P_key ∗
        chunkedStatesAt A.repAlloc (s0.sp - 4016#64) v.state ∗
        memRegion (s0.sp - 3088#64) 2992 ∗ spqrRecvSavedRegs (s0.sp - 4992#64) s0) →
      SepWPpLS (spqrRecvPlacedProg ext) (s0.readReg64 .x30) s1 P1
        (spqrRecvPlacedPostOfEnv A lim st_cost Env (spqrV1Recv F K) st msg ret s0 R)
        (spqrRecvBudgetPanicPost (spqrV1Recv F K) st msg s0 R)) :
    SepWPpLS (spqrRecvPlacedProg ext) (s0.readReg64 .x30) s P
      (spqrRecvPlacedPostOfEnv A lim st_cost Env (spqrV1Recv F K) st msg ret s0 R)
      (spqrRecvBudgetPanicPost (spqrV1Recv F K) st msg s0 R) := by
  have hrecv_call := hC.statesRecv_ok
  have hfsp_align : ((s0.sp - 4992#64) &&& 15#64 == 0#64) = true :=
    sp_sub_4992_aligned s0 hs0_align
  subst hP
  refine SepWPpLS.focus_weaken (memRegion_2896_split_statesRecv s0.sp) (by sep_focus) ?_
  apply SepWPpLS.of_sepWP (mid := lsmpl.base 332)
  let P_pre_rcv : SepProp :=
    memRegion (s0.sp - 4064#64) 32 ∗ memRegion (s0.sp - 4032#64) 16 ∗ memRegion (s0.sp - 4016#64) 928 ∗
    memRegion (s0.sp - 3088#64) 24 ∗ memRegion (s0.sp - 3064#64) 8 ∗
    memRegion (s0.sp - 3056#64) 960 ∗ memRegion (s0.sp - 2096#64) 928 ∗
    spqrRecvRoPlacedAt ∗ st.at A.repAlloc ∗ msg.at A.repAlloc ∗ memRegion ret 48 ∗
    A.pool lim (MC.stepEvents evs0 st_cost) s ∗
    stackAt (s0.sp - 4992#64) spqrRecvCalleeStackX ∗ memRegion (s0.sp - 4992#64) 352 ∗
    ((s0.sp - 4640#64) ↦₆₄ w0) ∗ ((s0.sp - 4632#64) ↦₆₄ w1) ∗
    optVersionNegotiationPBTailAt A.repAlloc w0 w1 (s0.sp - 4624#64) pre_pb.versionNegotiation ∗
    optChainPBAt A.repAlloc (s0.sp - 4592#64) pre_pb.chain ∗
    memRegion (s0.sp - 4512#64) 224 ∗ memRegion (s0.sp - 4288#64) 176 ∗
    messageAt spqrPolyApi (s0.sp - 4112#64) sckaMsg ∗ memRegion (s0.sp - 1168#64) 8 ∗
    chunkedStatesAt A.repAlloc (s0.sp - 1160#64) st0 ∗
    memRegion (s0.sp - 232#64) 136 ∗ spqrRecvSavedRegs (s0.sp - 4992#64) s0
  dsimp only [spqrRecvPlacedProg, spqrRecvPlacedEntry, BitVec.ofNat_eq_ofNat] at hpc ⊢
  refine seq_vm_clean (mid := lsmpl.base 332) (P_mid := P_pre_rcv)
    (Q := fun sc =>
      sc.sp = s.sp ∧
      TraceVRegs sc s ∧
      sc.readReg64 .x0 = s.readReg64 .x0 ∧
      sc.readReg64 .x1 = s.readReg64 .x1 ∧
      sc.readReg64 .x2 = s.readReg64 .x2 ∧
      sc.readReg64 .x19 = s.readReg64 .x19 ∧
      sc.readReg64 .x20 = s.readReg64 .x20 ∧
      sc.readReg64 .x21 = s.readReg64 .x21 ∧
      sc.readReg64 .x22 = s.readReg64 .x22 ∧
      sc.readReg64 .x24 = s.readReg64 .x24 ∧
      sc.readReg64 .x25 = s.readReg64 .x25 ∧
      sc.readReg64 .x26 = s.readReg64 .x26 ∧
      sc.readReg64 .x27 = s.readReg64 .x27 ∧
      sc.readReg64 .x28 = s.readReg64 .x28 ∧
      sc.readReg64 .x29 = s.readReg64 .x29 ∧
      sc.readReg64 .x30 = spqrRecvPlacedEntry + 1740#64) ?_ ?_
  · by_vm_steps (
      wp_steps
      refine ProofLib.SepWP.done (by simp only [wp_norm, arm64_norm, *])
        (by simp only [wp_norm, arm64_norm, *])
        ⟨by simp only [wp_norm, arm64_norm],
         Entails.of_eq (by dsimp only [P_pre_rcv]; sep_ac_rfl), ?_⟩
      refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
      all_goals first | rfl | simp only [spqrRecvPlacedEntry, wp_norm, arm64_norm, *]
    )
  · intro sc hpc_sc hrun_sc hvm_sc ⟨hsp_sc, htr_sc, hx0_sc, hx1_sc, hx2_sc,
      hx19_sc, hx20_sc, hx21_sc, hx22_sc, hx24_sc, hx25_sc, hx26_sc, hx27_sc, hx28_sc, hx29_sc, hx30_sc⟩
    apply ProofLib.SepWP.done hpc_sc hrun_sc
    dsimp only [P_pre_rcv]
    rw [← A.pool_transport lim (MC.stepEvents evs0 st_cost) s sc hvm_sc]
    unfold spqrRecvRoPlacedAt
    refine SepWPpLS.focus_weaken
      (Entails.of_eq (stackAt_spqrRecvCallee_split (s0.sp - 4992#64) statesRecvStackX (by decide)))
      (by sep_focus) ?_
    refine LibsignalBinary.Proofs.SpqrV1.Top.Recv.Part3PlacedBudget.SepWPpLS.call_lscro hrecv_call
      ((⟨s0.sp - 3056#64, s0.sp - 1160#64, s0.sp - 4112#64, st0, sckaMsg⟩ : StatesRecvGhost F),
        MC.stepEvents evs0 st_cost)
      hpc_sc hrun_sc
      (by simp only [State.spAligned, hsp_sc, hsp]; exact hfsp_align)
      hx30_sc (by rw [htr_sc.1, htr.1])
      (fun sf => onPanic_of_statesRecv_budget hpre hdec hinner hmv hmin hmsg hfrom)
      (fun _ _ => rfl)
      (by
        dsimp only [statesRecvPlacedSpecOfEnv]
        refine frame_pure_pre
          ⟨hx0_sc.trans hx0, hx1_sc.trans hx1, hx2_sc.trans hx2, hinv, hFit_rcv,
            by rw [show sc.readReg64 .lr = spqrRecvPlacedEntry + 1740#64 from hx30_sc]
               dsimp only [spqrRecvPlacedEntry]
               simp (config := { decide := true }) only [arm64_norm, wp_norm]⟩
          (by rw [hsp_sc, hsp]; sep_focus))
      ?_
    intro sm hpcm hrunm hspm hcsm
    rcases hcsm with ⟨hx19_c, hx20_c, hx21_c, hx22_c, _, hx24_c, hx25_c, hx26_c, hx27_c, hx28_c, hxfp_c, hvregs_c⟩
    dsimp only [statesRecvPlacedSpecOfEnv]
    simp only [sepExists_sepConj_left, sepConj_assoc]
    apply SepWPpLS.exists_elim; intro evs_rcv
    refine SepWPpLS.focus_pure (by sep_focus) ?_; rintro ⟨htr_sm, hevs_rcv⟩
    have htr_sm' : TraceVRegs sm s0 := ⟨by rw [htr_sm, htr_sc.1, htr.1], by rw [hvregs_c, htr_sc.2, htr.2]⟩
    have hspm' : sm.sp = s0.sp - 4992#64 := by rw [hspm, hsp_sc, hsp]
    have hx19_sm : sm.readReg64 .x19 = ret := by rw [hx19_c, hx19_sc, hx19]
    have hx20_sm : sm.readReg64 .x20 = w0 := by rw [hx20_c, hx20_sc, hx20]
    have hx21_sm : sm.readReg64 .x21 = pre.index.zeroExtend 64 := by rw [hx21_c, hx21_sc, hx21]
    have hx22_sm : sm.readReg64 .x22 = pre.epoch := by rw [hx22_c, hx22_sc, hx22]
    have hx24_sm : sm.readReg64 .x24 = s0.sp - 3056#64 := by rw [hx24_c, hx24_sc, hx24]
    have hx25_sm : sm.readReg64 .x25 = s0.sp - 4640#64 := by rw [hx25_c, hx25_sc, hx25]
    have hx26_sm : sm.readReg64 .x26 = s0.sp - 1160#64 := by rw [hx26_c, hx26_sc, hx26]
    have hx27_sm : sm.readReg64 .x27 = s0.sp - 3056#64 := by rw [hx27_c, hx27_sc, hx27]
    have hx28_sm : sm.readReg64 .x28 = 0#64 := by rw [hx28_c, hx28_sc, hx28]
    have hx29_sm : sm.readReg64 .x29 = s0.sp - 96#64 := by
      change sm.readReg64 Reg.fp = s0.sp - 96#64
      rw [hxfp_c]; exact hx29_sc.trans hx29
    have hsp_eq := congrArg (stackAt · statesRecvStackX) (hspm.symm.trans hspm')
    refine SepWPpLS.focus_weaken (Entails.of_eq hsp_eq) (by sep_focus) ?_
    refine SepWPpLS.focus_weaken
      (Entails.of_eq (stackAt_spqrRecvCallee_split (s0.sp - 4992#64) statesRecvStackX (by decide)).symm)
      (by sep_focus) ?_
    have hro_fold :
        v1StateJumpTablesPlacedAt ∗
          statesFromPbJumpTablePlacedAt ∗
          statesRecvRoPlacedAt ∗
          statesIntoPbJumpTablePlacedAt ⊢
        spqrRecvRoPlacedAt := Entails.refl _
    refine SepWPpLS.focus_weaken hro_fold (by sep_focus) ?_
    have h928_self : memRegion (s0.sp - 1160#64) chunkedStatesSize = memRegion (s0.sp - 1160#64) 928 := rfl
    rw [h928_self, ← MC.stepEvents_append]
    have hrecv_eq : st0.recv K sckaMsg = States.recv K st0 sckaMsg := rfl
    rw [hrecv_eq]
    cases hrecv : States.recv K st0 sckaMsg with
    | error se =>
      cases se with
      | panic p =>
        rw [resultV1RecvAt_panic_false]
        refine SepWPpLS.focus_pure (by sep_focus) False.elim
      | err err =>
        apply SepWPpLS.of_sepWP_ret_lscl; intro hcl
        refine sepWP_spqrRecvPlacedPostOfEnv_of_post0
          (spqrV1Recv_v1_statesRecv_err F K hpre hdec hinner hmv hmin hmsg hfrom hrecv).2 ?_
        exact step_post_statesRecv_err_1740_placed_ofEnv A lim st_cost Env (evs0 ++ evs_rcv)
          (fun evs_d hd => hevs_err evs_rcv evs_d hevs_rcv hd)
          F K ext (toDropContractsBudget hC) st msg ret
          pre pre_pb pb w0 w1 sckaMsg st0 err hpre hdec hinner hmv hmin hmsg hfrom hrecv
          s0 sm _ R _ rfl hs0_align hpcm hrunm hspm' htr_sm' hx19_sm hx25_sm hx27_sm hx28_sm
          (by ac_rfl) hcl
    | ok v =>
      have hep0 := msgPreamble_epoch_beq_zero_false hpre hmv
      let s0_1856 := s0.writeReg64 .x30 (spqrRecvPlacedEntry + 1856#64)
      have hs0_1856_sp : s0_1856.sp = s0.sp := rfl
      have hs0_1856_align : s0_1856.spAligned = true := hs0_align
      apply SepWPpLS.of_sepWP (mid := spqrRecvPlacedEntry + 1856#64)
      let F_rest : SepProp :=
        spqrRecvRoPlacedAt ∗ st.at A.repAlloc ∗ msg.at A.repAlloc ∗ memRegion ret 48 ∗
        A.pool lim (MC.stepEvents (evs0 ++ evs_rcv) st_cost) sm ∗
        memRegion (s0.sp - 4992#64) 352 ∗ ((s0.sp - 4632#64) ↦₆₄ w1) ∗
        optVersionNegotiationPBTailAt A.repAlloc w0 w1 (s0.sp - 4624#64) pre_pb.versionNegotiation ∗
        optChainPBAt A.repAlloc (s0.sp - 4592#64) pre_pb.chain ∗
        memRegion (s0.sp - 4512#64) 224 ∗ memRegion (s0.sp - 4288#64) 176 ∗
        messageAt spqrPolyApi (s0.sp - 4112#64) sckaMsg ∗ memRegion (s0.sp - 4064#64) 32 ∗
        spqrRecvSavedRegs (s0.sp - 4992#64) s0
      refine step_post_statesRecv_ok_1740_placed A F ext hC.memcpy_ok pre w0 v hep0 s0_1856 sm _ F_rest _
        hs0_1856_align hpcm hrunm hspm' hx22_sm hx24_sm hx27_sm
        (by simp only [hs0_1856_sp, F_rest]; ac_rfl) ?_
      intro kw0 kw1 kw2 kw3 P_key s1 hfold_key hpc1 hrun1 hvm1 hsp1 htr1
        hx0_1 hx1_1 hx2_1 hx19_1 hx20_1 hx21_1 hx22_1 hx23_1 hx24_1 hx25_1 hx26_1 hx27_1 hx28_1 hx29_1
      apply ProofLib.SepWP.done hpc1 hrun1
      dsimp only [F_rest]
      rw [← A.pool_transport lim (MC.stepEvents (evs0 ++ evs_rcv) st_cost) sm s1 hvm1]
      exact hok_tail evs_rcv v kw0 kw1 kw2 kw3 P_key s1 _ hevs_rcv hrecv hfold_key
        hpc1 hrun1 hsp1 (traceVRegs_trans htr1 htr_sm')
        hx0_1 hx1_1 hx2_1
        (hx19_1.trans hx19_sm) (hx20_1.trans hx20_sm) (hx21_1.trans hx21_sm)
        hx22_1 hx23_1 hx24_1 hx25_1 (hx26_1.trans hx26_sm) hx27_1
        (hx28_1.trans hx28_sm) (hx29_1.trans hx29_sm)
        (by simp only [hs0_1856_sp]; ac_rfl)

theorem step_statesRecv_1736_placed {MC : AllocCostModel}
    {H_inner : V1InnerHeapPred} {A : RustCliAllocBudget MC} {lim : BudgetLimits} {st_cost : MC.σ}
    {F : ShaCompress} {K : MlKem} {ext : String → Option (State → State)}
    (evs0 : List AllocEvent)
    (hC : SpqrRecvPlacedContracts H_inner A lim F K ext)
    (st msg : VecArg) (ret : BitVec 64)
    (pre : MsgPreamble) (pre_pb : PqRatchetState) (pb : V1State)
    (w0 w1 : BitVec 64) (sckaMsg : Message spqrPolyApi) (st0 : States spqrPolyApi (spqrAuthApi F))
    (hinv : statesRecvPreInv st0)
    (hpre : msgPreamble msg.bytes = .ok pre)
    (hdec : spqrDecodeState st.bytes = .ok pre_pb)
    (hinner : pre_pb.inner = some (.v1 pb))
    (hmv : pre.version = 1#8)
    (hmin : ∀ vn, pre_pb.versionNegotiation = some vn → ¬(1#8 < vn.minVersion.truncate 8))
    (hmsg : Message.deserialize spqrPolyApi pre.epoch pre.remaining = .ok sckaMsg)
    (hfrom : States.from_pb spqrPolyApi (spqrAuthApi F) pb = .ok st0)
    (s0 s : State) (P R : SepProp)
    (hFit_rcv : FitsEnv MC lim (MC.stepEvents evs0 st_cost)
      (StatesRecvEnv ⟨s0.sp - 3056#64, s0.sp - 1160#64, s0.sp - 4112#64, st0, sckaMsg⟩))
    (hevs_rcv : ∀ evs_rcv,
      StatesRecvEnv ⟨s0.sp - 3056#64, s0.sp - 1160#64, s0.sp - 4112#64, st0, sckaMsg⟩ evs_rcv →
      SpqrRecvEnv st msg (evs0 ++ evs_rcv))
    (hs0_align : s0.spAligned = true)
    (hpc : s.pc = spqrRecvPlacedEntry + 1736#64)
    (hrun : s.status = .Running) (hsp : s.sp = s0.sp - 4992#64) (htr : TraceVRegs s s0)
    (hx0 : s.readReg64 .x0 = s0.sp - 3056#64) (hx1 : s.readReg64 .x1 = s0.sp - 1160#64)
    (hx2 : s.readReg64 .x2 = s0.sp - 4112#64) (hx19 : s.readReg64 .x19 = ret)
    (hx20 : s.readReg64 .x20 = w0) (hx21 : s.readReg64 .x21 = pre.index.zeroExtend 64)
    (hx22 : s.readReg64 .x22 = pre.epoch) (hx24 : s.readReg64 .x24 = s0.sp - 3056#64)
    (hx25 : s.readReg64 .x25 = s0.sp - 4640#64) (hx26 : s.readReg64 .x26 = s0.sp - 1160#64)
    (hx27 : s.readReg64 .x27 = s0.sp - 3056#64) (hx28 : s.readReg64 .x28 = 0#64)
    (hx29 : s.readReg64 .x29 = s0.sp - 96#64)
    (hP : P =
      spqrRecvRoPlacedAt ∗ st.at A.repAlloc ∗ msg.at A.repAlloc ∗ memRegion ret 48 ∗
      A.pool lim (MC.stepEvents evs0 st_cost) s ∗
      stackAt (s0.sp - 4992#64) spqrRecvCalleeStackX ∗ memRegion (s0.sp - 4992#64) 352 ∗
      ((s0.sp - 4640#64) ↦₆₄ w0) ∗ ((s0.sp - 4632#64) ↦₆₄ w1) ∗
      optVersionNegotiationPBTailAt A.repAlloc w0 w1 (s0.sp - 4624#64) pre_pb.versionNegotiation ∗
      optChainPBAt A.repAlloc (s0.sp - 4592#64) pre_pb.chain ∗
      memRegion (s0.sp - 4512#64) 224 ∗ memRegion (s0.sp - 4288#64) 176 ∗
      messageAt spqrPolyApi (s0.sp - 4112#64) sckaMsg ∗
      memRegion (s0.sp - 4064#64) 2896 ∗ memRegion (s0.sp - 1168#64) 8 ∗
      chunkedStatesAt A.repAlloc (s0.sp - 1160#64) st0 ∗
      memRegion (s0.sp - 232#64) 136 ∗ spqrRecvSavedRegs (s0.sp - 4992#64) s0)
    (hok_tail : ∀ (evs_rcv : List AllocEvent) (v : V1Recv spqrPolyApi (spqrAuthApi F))
      (kw0 kw1 kw2 kw3 : BitVec 64) (P_key : SepProp) (s1 : State) (P1 : SepProp),
      StatesRecvEnv ⟨s0.sp - 3056#64, s0.sp - 1160#64, s0.sp - 4112#64, st0, sckaMsg⟩ evs_rcv →
      States.recv K st0 sckaMsg = .ok v →
      (∀ dst : BitVec 64,
        (dst ↦₆₄ kw0) ∗ ((dst + 8#64) ↦₆₄ kw1) ∗ ((dst + 16#64) ↦₆₄ kw2) ∗ ((dst + 24#64) ↦₆₄ kw3) ∗ P_key ⊢
          optEpochSecretAt A.repAlloc dst v.key) →
      s1.pc = spqrRecvPlacedEntry + 1856#64 →
      s1.status = .Running → s1.sp = s0.sp - 4992#64 → TraceVRegs s1 s0 →
      s1.readReg64 .x0 = s0.sp - 3056#64 → s1.readReg64 .x1 = s0.sp - 4592#64 →
      s1.readReg64 .x2 = (if (w0 + 1#64 == 0#64) then 0#64 else s0.sp - 4640#64) →
      s1.readReg64 .x19 = ret → s1.readReg64 .x20 = w0 →
      s1.readReg64 .x21 = pre.index.zeroExtend 64 → s1.readReg64 .x22 = pre.epoch →
      s1.readReg64 .x23 = w0 → s1.readReg64 .x24 = kw0 →
      s1.readReg64 .x25 = kw1 → s1.readReg64 .x26 = s0.sp - 1160#64 →
      s1.readReg64 .x27 = s0.sp - 3056#64 → s1.readReg64 .x28 = 0#64 →
      s1.readReg64 .x29 = s0.sp - 96#64 →
      P1 = (spqrRecvRoPlacedAt ∗ st.at A.repAlloc ∗ msg.at A.repAlloc ∗ memRegion ret 48 ∗
        A.pool lim (MC.stepEvents (evs0 ++ evs_rcv) st_cost) s1 ∗
        stackAt (s0.sp - 4992#64) spqrRecvCalleeStackX ∗ memRegion (s0.sp - 4992#64) 352 ∗
        ((s0.sp - 4640#64) ↦₆₄ w0) ∗ ((s0.sp - 4632#64) ↦₆₄ w1) ∗
        optVersionNegotiationPBTailAt A.repAlloc w0 w1 (s0.sp - 4624#64) pre_pb.versionNegotiation ∗
        optChainPBAt A.repAlloc (s0.sp - 4592#64) pre_pb.chain ∗
        memRegion (s0.sp - 4512#64) 224 ∗ memRegion (s0.sp - 4288#64) 176 ∗
        messageAt spqrPolyApi (s0.sp - 4112#64) sckaMsg ∗ memRegion (s0.sp - 4064#64) 32 ∗
        ((s0.sp - 4032#64) ↦₆₄ kw2) ∗ ((s0.sp - 4024#64) ↦₆₄ kw3) ∗ P_key ∗
        chunkedStatesAt A.repAlloc (s0.sp - 4016#64) v.state ∗
        memRegion (s0.sp - 3088#64) 2992 ∗ spqrRecvSavedRegs (s0.sp - 4992#64) s0) →
      SepWPpLS (spqrRecvPlacedProg ext) (s0.readReg64 .x30) s1 P1
        (spqrRecvPlacedPost A lim st_cost (spqrV1Recv F K) st msg ret s0 R)
        (spqrRecvBudgetPanicPost (spqrV1Recv F K) st msg s0 R)) :
    SepWPpLS (spqrRecvPlacedProg ext) (s0.readReg64 .x30) s P
      (spqrRecvPlacedPost A lim st_cost (spqrV1Recv F K) st msg ret s0 R)
      (spqrRecvBudgetPanicPost (spqrV1Recv F K) st msg s0 R) :=
  step_statesRecv_1736_placed_ofEnv (SpqrRecvEnv st msg) evs0
    hC st msg ret pre pre_pb pb w0 w1 sckaMsg st0 hinv hpre hdec hinner hmv hmin hmsg hfrom
    s0 s P R hFit_rcv
    (fun evs_rcv _ hrcv hd => SpqrRecvEnv.append_freeOnly (hevs_rcv evs_rcv hrcv) hd)
    hs0_align hpc hrun hsp htr hx0 hx1 hx2 hx19 hx20 hx21 hx22 hx24 hx25 hx26 hx27 hx28 hx29 hP
    hok_tail

/-! ## 2. Composed First-Half V1 Ratchet Step (`+1532 .. +1856`) -/

/-- Envelope-parametric composition of `step_msgDeserialize_1532_placed_ofEnv`,
    `step_statesFromPb_1636_placed_ofEnv`, and `step_statesRecv_1736_placed_ofEnv` from `+1532`
    (`spqrRecvPlacedEntry + 1532#64`) to `+1856` (`spqrRecvPlacedEntry + 1856#64`). -/
theorem step_v1_ratchet_1532_to_1856_placed_ofEnv {MC : AllocCostModel}
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
    (pre : MsgPreamble) (remPtr : BitVec 64) (pre_pb : PqRatchetState) (pb : V1State)
    (w0 w1 : BitVec 64)
    (hst_len : st.bytes.length < 2 ^ 32)
    (hpre : msgPreamble msg.bytes = .ok pre)
    (hvalid : MsgRemValid msg remPtr pre.remaining)
    (hdec : spqrDecodeState st.bytes = .ok pre_pb)
    (hinner : pre_pb.inner = some (.v1 pb))
    (hmv : pre.version = 1#8)
    (hmin : ∀ vn, pre_pb.versionNegotiation = some vn → ¬(1#8 < vn.minVersion.truncate 8))
    (s0 s : State) (P R : SepProp)
    (hevs_md_err : ∀ evs_d, FreeOnlyEvs evs_d → Env (evs0 ++ evs_d))
    (hFit_fpb : ∀ evs_md, FreeOnlyEvs evs_md →
      FitsEnv MC lim (MC.stepEvents (evs0 ++ evs_md) st_cost) (FromPbEnv pb))
    (hevs_fpb_err : ∀ evs_md evs_fpb evs_d, FreeOnlyEvs evs_md → FromPbEnv pb evs_fpb →
      FreeOnlyEvs evs_d → Env (((evs0 ++ evs_md) ++ evs_fpb) ++ evs_d))
    (hFit_rcv : ∀ (sckaMsg : Message spqrPolyApi) (st0 : States spqrPolyApi (spqrAuthApi F))
        evs_md evs_fpb,
      Message.deserialize spqrPolyApi pre.epoch pre.remaining = .ok sckaMsg →
      States.from_pb spqrPolyApi (spqrAuthApi F) pb = .ok st0 →
      FreeOnlyEvs evs_md → FromPbEnv pb evs_fpb →
      FitsEnv MC lim (MC.stepEvents ((evs0 ++ evs_md) ++ evs_fpb) st_cost)
        (RecvEnv ⟨s0.sp - 3056#64, s0.sp - 1160#64, s0.sp - 4112#64, st0, sckaMsg⟩))
    (hevs_rcv_err : ∀ (sckaMsg : Message spqrPolyApi) (st0 : States spqrPolyApi (spqrAuthApi F))
        evs_md evs_fpb evs_rcv evs_d,
      Message.deserialize spqrPolyApi pre.epoch pre.remaining = .ok sckaMsg →
      States.from_pb spqrPolyApi (spqrAuthApi F) pb = .ok st0 →
      FreeOnlyEvs evs_md → FromPbEnv pb evs_fpb →
      RecvEnv ⟨s0.sp - 3056#64, s0.sp - 1160#64, s0.sp - 4112#64, st0, sckaMsg⟩ evs_rcv →
      FreeOnlyEvs evs_d → Env ((((evs0 ++ evs_md) ++ evs_fpb) ++ evs_rcv) ++ evs_d))
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
    (hok_1856 : ∀ (evs_md evs_fpb evs_rcv : List AllocEvent)
      (sckaMsg : Message spqrPolyApi) (st0 : States spqrPolyApi (spqrAuthApi F))
      (v : V1Recv spqrPolyApi (spqrAuthApi F))
      (kw0 kw1 kw2 kw3 : BitVec 64) (P_key : SepProp) (s1 : State) (P1 : SepProp),
      FreeOnlyEvs evs_md →
      FromPbEnv pb evs_fpb →
      RecvEnv ⟨s0.sp - 3056#64, s0.sp - 1160#64, s0.sp - 4112#64, st0, sckaMsg⟩ evs_rcv →
      Message.deserialize spqrPolyApi pre.epoch pre.remaining = .ok sckaMsg →
      States.from_pb spqrPolyApi (spqrAuthApi F) pb = .ok st0 →
      States.recv K st0 sckaMsg = .ok v →
      (∀ dst : BitVec 64,
        (dst ↦₆₄ kw0) ∗ ((dst + 8#64) ↦₆₄ kw1) ∗ ((dst + 16#64) ↦₆₄ kw2) ∗ ((dst + 24#64) ↦₆₄ kw3) ∗ P_key ⊢
          optEpochSecretAt A.repAlloc dst v.key) →
      s1.pc = spqrRecvPlacedEntry + 1856#64 →
      s1.status = .Running → s1.sp = s0.sp - 4992#64 → TraceVRegs s1 s0 →
      s1.readReg64 .x0 = s0.sp - 3056#64 → s1.readReg64 .x1 = s0.sp - 4592#64 →
      s1.readReg64 .x2 = (if (w0 + 1#64 == 0#64) then 0#64 else s0.sp - 4640#64) →
      s1.readReg64 .x19 = ret → s1.readReg64 .x20 = w0 →
      s1.readReg64 .x21 = pre.index.zeroExtend 64 → s1.readReg64 .x22 = pre.epoch →
      s1.readReg64 .x23 = w0 → s1.readReg64 .x24 = kw0 →
      s1.readReg64 .x25 = kw1 → s1.readReg64 .x26 = s0.sp - 1160#64 →
      s1.readReg64 .x27 = s0.sp - 3056#64 → s1.readReg64 .x28 = 0#64 →
      s1.readReg64 .x29 = s0.sp - 96#64 →
      P1 = (spqrRecvRoPlacedAt ∗ st.at A.repAlloc ∗ msg.at A.repAlloc ∗ memRegion ret 48 ∗
        A.pool lim (MC.stepEvents (((evs0 ++ evs_md) ++ evs_fpb) ++ evs_rcv) st_cost) s1 ∗
        stackAt (s0.sp - 4992#64) spqrRecvCalleeStackX ∗ memRegion (s0.sp - 4992#64) 352 ∗
        ((s0.sp - 4640#64) ↦₆₄ w0) ∗ ((s0.sp - 4632#64) ↦₆₄ w1) ∗
        optVersionNegotiationPBTailAt A.repAlloc w0 w1 (s0.sp - 4624#64) pre_pb.versionNegotiation ∗
        optChainPBAt A.repAlloc (s0.sp - 4592#64) pre_pb.chain ∗
        memRegion (s0.sp - 4512#64) 224 ∗ memRegion (s0.sp - 4288#64) 176 ∗
        messageAt spqrPolyApi (s0.sp - 4112#64) sckaMsg ∗ memRegion (s0.sp - 4064#64) 32 ∗
        ((s0.sp - 4032#64) ↦₆₄ kw2) ∗ ((s0.sp - 4024#64) ↦₆₄ kw3) ∗ P_key ∗
        chunkedStatesAt A.repAlloc (s0.sp - 4016#64) v.state ∗
        memRegion (s0.sp - 3088#64) 2992 ∗ spqrRecvSavedRegs (s0.sp - 4992#64) s0) →
      SepWPpLS (spqrRecvPlacedProg ext) (s0.readReg64 .x30) s1 P1
        (spqrRecvPlacedPostOfEnv A lim st_cost Env (spqrV1Recv F K) st msg ret s0 R)
        (spqrRecvBudgetPanicPost (spqrV1Recv F K) st msg s0 R)) :
    SepWPpLS (spqrRecvPlacedProg ext) (s0.readReg64 .x30) s P
      (spqrRecvPlacedPostOfEnv A lim st_cost Env (spqrV1Recv F K) st msg ret s0 R)
      (spqrRecvBudgetPanicPost (spqrV1Recv F K) st msg s0 R) := by
  have hpts : v1StatePtsBound pb :=
    v1StatePtsBound_of_spqrDecodeState (F := F) (K := K) hst_len hdec hinner
  refine step_msgDeserialize_1532_placed_ofEnv Env evs0 hevs_md_err hC st msg ret pre remPtr pre_pb pb w0 w1
    hpre hvalid hdec hinner hmv hmin s0 s P R hs0_align hpc hrun hsp htr
    hx19 hx20 hx21 hx22 hx23 hx24 hx26 hx27 hx28 hx29 hP ?_
  intro evs_md sckaMsg s1636 P1636 hevs_md hmsg hpc1636 hrun1636 hsp1636 htr1636
    hx0_1636 hx8_1636 hx19_1636 hx20_1636 hx21_1636 hx22_1636 hx24_1636 hx25_1636 hx26_1636 hx27_1636 _ hx29_1636 hP1636
  refine step_statesFromPb_1636_placed_ofEnv Env (evs0 ++ evs_md)
    hC st msg ret pre pre_pb pb w0 w1 sckaMsg
    hpts hpre hdec hinner hmv hmin hmsg s0 s1636 P1636 R
    (hFit_fpb evs_md hevs_md)
    (fun evs_fpb evs_d hfpb hd => hevs_fpb_err evs_md evs_fpb evs_d hevs_md hfpb hd)
    hs0_align
    hpc1636 hrun1636 hsp1636 htr1636
    hx0_1636 hx8_1636 hx19_1636 hx20_1636 hx21_1636 hx22_1636 hx24_1636 hx25_1636 hx26_1636 hx27_1636 hx29_1636 hP1636 ?_
  intro evs_fpb st0 s1736 P1736 hevs_fpb hfrom hpc1736 hrun1736 hsp1736 htr1736
    hx0_1736 hx1_1736 hx2_1736 hx19_1736 hx20_1736 hx21_1736 hx22_1736 hx24_1736 hx25_1736 hx26_1736 hx27_1736 hx28_1736 hx29_1736 hP1736
  have hinv : statesRecvPreInv st0 :=
    statesRecvPreInv_of_spqrDecodeState (F := F) (K := K) hst_len hdec hinner hfrom
  refine step_statesRecv_1736_placed_ofEnv Env ((evs0 ++ evs_md) ++ evs_fpb)
    hC st msg ret pre pre_pb pb w0 w1 sckaMsg st0
    hinv hpre hdec hinner hmv hmin hmsg hfrom s0 s1736 P1736 R
    (hFit_rcv sckaMsg st0 evs_md evs_fpb hmsg hfrom hevs_md hevs_fpb)
    (fun evs_rcv evs_d hrcv hd => hevs_rcv_err sckaMsg st0 evs_md evs_fpb evs_rcv evs_d hmsg hfrom hevs_md hevs_fpb hrcv hd)
    hs0_align
    hpc1736 hrun1736 hsp1736 htr1736
    hx0_1736 hx1_1736 hx2_1736 hx19_1736 hx20_1736 hx21_1736 hx22_1736 hx24_1736 hx25_1736 hx26_1736 hx27_1736 hx28_1736 hx29_1736 hP1736 ?_
  intro evs_rcv v kw0 kw1 kw2 kw3 P_key s1856 P1856 hevs_rcv hrecv hfold_key
  exact hok_1856 evs_md evs_fpb evs_rcv sckaMsg st0 v kw0 kw1 kw2 kw3 P_key s1856 P1856
    hevs_md hevs_fpb hevs_rcv hmsg hfrom hrecv hfold_key

theorem step_v1_ratchet_1532_to_1856_placed {MC : AllocCostModel}
    {H_inner : V1InnerHeapPred} {A : RustCliAllocBudget MC} {lim : BudgetLimits} {st_cost : MC.σ}
    {F : ShaCompress} {K : MlKem} {ext : String → Option (State → State)}
    (hC : SpqrRecvPlacedContracts H_inner A lim F K ext)
    (st msg : VecArg) (ret : BitVec 64)
    (pre : MsgPreamble) (remPtr : BitVec 64) (pre_pb : PqRatchetState) (pb : V1State)
    (w0 w1 : BitVec 64)
    (hst_len : st.bytes.length < 2 ^ 32)
    (hpre : msgPreamble msg.bytes = .ok pre)
    (hvalid : MsgRemValid msg remPtr pre.remaining)
    (hdec : spqrDecodeState st.bytes = .ok pre_pb)
    (hinner : pre_pb.inner = some (.v1 pb))
    (hmv : pre.version = 1#8)
    (hmin : ∀ vn, pre_pb.versionNegotiation = some vn → ¬(1#8 < vn.minVersion.truncate 8))
    (s0 s : State) (P R : SepProp)
    (evs0 : List AllocEvent) (hevs0 : SpqrRecvEnv st msg evs0)
    (hFit_fpb : ∀ evs_md, FreeOnlyEvs evs_md →
      FitsEnv MC lim (MC.stepEvents (evs0 ++ evs_md) st_cost) (StatesFromPbEnv pb))
    (hevs_fpb : ∀ evs_md evs_fpb, FreeOnlyEvs evs_md → StatesFromPbEnv pb evs_fpb →
      SpqrRecvEnv st msg ((evs0 ++ evs_md) ++ evs_fpb))
    (hFit_rcv : ∀ (sckaMsg : Message spqrPolyApi) (st0 : States spqrPolyApi (spqrAuthApi F))
        evs_md evs_fpb,
      Message.deserialize spqrPolyApi pre.epoch pre.remaining = .ok sckaMsg →
      States.from_pb spqrPolyApi (spqrAuthApi F) pb = .ok st0 →
      FreeOnlyEvs evs_md → StatesFromPbEnv pb evs_fpb →
      FitsEnv MC lim (MC.stepEvents ((evs0 ++ evs_md) ++ evs_fpb) st_cost)
        (StatesRecvEnv ⟨s0.sp - 3056#64, s0.sp - 1160#64, s0.sp - 4112#64, st0, sckaMsg⟩))
    (hevs_rcv : ∀ (sckaMsg : Message spqrPolyApi) (st0 : States spqrPolyApi (spqrAuthApi F))
        evs_md evs_fpb evs_rcv,
      Message.deserialize spqrPolyApi pre.epoch pre.remaining = .ok sckaMsg →
      States.from_pb spqrPolyApi (spqrAuthApi F) pb = .ok st0 →
      FreeOnlyEvs evs_md → StatesFromPbEnv pb evs_fpb →
      StatesRecvEnv ⟨s0.sp - 3056#64, s0.sp - 1160#64, s0.sp - 4112#64, st0, sckaMsg⟩ evs_rcv →
      SpqrRecvEnv st msg (((evs0 ++ evs_md) ++ evs_fpb) ++ evs_rcv))
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
    (hok_1856 : ∀ (evs_md evs_fpb evs_rcv : List AllocEvent)
      (sckaMsg : Message spqrPolyApi) (st0 : States spqrPolyApi (spqrAuthApi F))
      (v : V1Recv spqrPolyApi (spqrAuthApi F))
      (kw0 kw1 kw2 kw3 : BitVec 64) (P_key : SepProp) (s1 : State) (P1 : SepProp),
      FreeOnlyEvs evs_md →
      StatesFromPbEnv pb evs_fpb →
      StatesRecvEnv ⟨s0.sp - 3056#64, s0.sp - 1160#64, s0.sp - 4112#64, st0, sckaMsg⟩ evs_rcv →
      Message.deserialize spqrPolyApi pre.epoch pre.remaining = .ok sckaMsg →
      States.from_pb spqrPolyApi (spqrAuthApi F) pb = .ok st0 →
      States.recv K st0 sckaMsg = .ok v →
      (∀ dst : BitVec 64,
        (dst ↦₆₄ kw0) ∗ ((dst + 8#64) ↦₆₄ kw1) ∗ ((dst + 16#64) ↦₆₄ kw2) ∗ ((dst + 24#64) ↦₆₄ kw3) ∗ P_key ⊢
          optEpochSecretAt A.repAlloc dst v.key) →
      s1.pc = spqrRecvPlacedEntry + 1856#64 →
      s1.status = .Running → s1.sp = s0.sp - 4992#64 → TraceVRegs s1 s0 →
      s1.readReg64 .x0 = s0.sp - 3056#64 → s1.readReg64 .x1 = s0.sp - 4592#64 →
      s1.readReg64 .x2 = (if (w0 + 1#64 == 0#64) then 0#64 else s0.sp - 4640#64) →
      s1.readReg64 .x19 = ret → s1.readReg64 .x20 = w0 →
      s1.readReg64 .x21 = pre.index.zeroExtend 64 → s1.readReg64 .x22 = pre.epoch →
      s1.readReg64 .x23 = w0 → s1.readReg64 .x24 = kw0 →
      s1.readReg64 .x25 = kw1 → s1.readReg64 .x26 = s0.sp - 1160#64 →
      s1.readReg64 .x27 = s0.sp - 3056#64 → s1.readReg64 .x28 = 0#64 →
      s1.readReg64 .x29 = s0.sp - 96#64 →
      P1 = (spqrRecvRoPlacedAt ∗ st.at A.repAlloc ∗ msg.at A.repAlloc ∗ memRegion ret 48 ∗
        A.pool lim (MC.stepEvents (((evs0 ++ evs_md) ++ evs_fpb) ++ evs_rcv) st_cost) s1 ∗
        stackAt (s0.sp - 4992#64) spqrRecvCalleeStackX ∗ memRegion (s0.sp - 4992#64) 352 ∗
        ((s0.sp - 4640#64) ↦₆₄ w0) ∗ ((s0.sp - 4632#64) ↦₆₄ w1) ∗
        optVersionNegotiationPBTailAt A.repAlloc w0 w1 (s0.sp - 4624#64) pre_pb.versionNegotiation ∗
        optChainPBAt A.repAlloc (s0.sp - 4592#64) pre_pb.chain ∗
        memRegion (s0.sp - 4512#64) 224 ∗ memRegion (s0.sp - 4288#64) 176 ∗
        messageAt spqrPolyApi (s0.sp - 4112#64) sckaMsg ∗ memRegion (s0.sp - 4064#64) 32 ∗
        ((s0.sp - 4032#64) ↦₆₄ kw2) ∗ ((s0.sp - 4024#64) ↦₆₄ kw3) ∗ P_key ∗
        chunkedStatesAt A.repAlloc (s0.sp - 4016#64) v.state ∗
        memRegion (s0.sp - 3088#64) 2992 ∗ spqrRecvSavedRegs (s0.sp - 4992#64) s0) →
      SepWPpLS (spqrRecvPlacedProg ext) (s0.readReg64 .x30) s1 P1
        (spqrRecvPlacedPost A lim st_cost (spqrV1Recv F K) st msg ret s0 R)
        (spqrRecvBudgetPanicPost (spqrV1Recv F K) st msg s0 R)) :
    SepWPpLS (spqrRecvPlacedProg ext) (s0.readReg64 .x30) s P
      (spqrRecvPlacedPost A lim st_cost (spqrV1Recv F K) st msg ret s0 R)
      (spqrRecvBudgetPanicPost (spqrV1Recv F K) st msg s0 R) :=
  step_v1_ratchet_1532_to_1856_placed_ofEnv (SpqrRecvEnv st msg) evs0
    hC st msg ret pre remPtr pre_pb pb w0 w1 hst_len hpre hvalid hdec hinner hmv hmin
    s0 s P R
    (fun _ hd => SpqrRecvEnv.append_freeOnly hevs0 hd)
    hFit_fpb
    (fun evs_md evs_fpb _ hmd hfpb hd =>
      SpqrRecvEnv.append_freeOnly (hevs_fpb evs_md evs_fpb hmd hfpb) hd)
    hFit_rcv
    (fun sckaMsg st0 evs_md evs_fpb evs_rcv _ hmsg hfrom hmd hfpb hrcv hd =>
      SpqrRecvEnv.append_freeOnly (hevs_rcv sckaMsg st0 evs_md evs_fpb evs_rcv hmsg hfrom hmd hfpb hrcv) hd)
    hs0_align hpc hrun hsp htr hx19 hx20 hx21 hx22 hx23 hx24 hx26 hx27 hx28 hx29 hP hok_1856

end LibsignalBinary.Proofs.SpqrV1.Top.Recv.V1Ratchet3PlacedBudget
