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
public import LibsignalBinary.Proofs.SpqrV1.Poly.DecodedMessage.DefsBudget
public import LibsignalBinary.Proofs.SpqrV1.States.Leaves.Batch2DefsPlacedBudget
public import LibsignalBinary.Proofs.SpqrV1.States.Recv.ArmCt1SampledPart10PlacedBudgetAux
public import LibsignalBinary.Proofs.SpqrV1.States.Recv.ArmCt1SampledPart1PlacedBudget
public import LibsignalBinary.Proofs.SpqrV1.States.Recv.ArmCt1SampledPart2
public import LibsignalBinary.Proofs.SpqrV1.States.Recv.ArmCt1SampledPart3PlacedBudgetAux
public import LibsignalBinary.Proofs.SpqrV1.States.Recv.ArmCt1SampledPart7PlacedBudget
public import LibsignalBinary.Proofs.SpqrV1.States.Recv.ArmCt1SampledPart8PlacedBudget
public import LibsignalBinary.Proofs.SpqrV1.States.Recv.ArmCt1SampledPart9PlacedBudget
public import LibsignalBinary.Proofs.SpqrV1.States.Recv.DefsPlacedBudget
public import LibsignalBinary.Proofs.SpqrV1.Unchunked.SendCt2PlacedBudget
import LibsignalBinary.Proofs.Common.SharedHelpers
meta import LibsignalBinary.Proofs.Common.SharedHelpers -- shake: keep
import LibsignalBinary.Proofs.SpqrV1.States.FromPb.Defs
import LibsignalBinary.Proofs.SpqrV1.States.Recv.ArmCt1SampledPart1
import LibsignalBinary.Proofs.SpqrV1.States.Recv.ArmCt1SampledPart10
import LibsignalBinary.Proofs.SpqrV1.States.Recv.ArmCt1SampledPart3
import LibsignalBinary.Proofs.SpqrV1.States.Recv.ArmCt1SampledPart7
import LibsignalBinary.Proofs.SpqrV1.States.Recv.CodeSymFetch2Placed
import LibsignalBinary.Proofs.SpqrV1.States.Recv.CodeSymFetch3Placed
import ProofLib.SepLogic.WPp

/-!
# `<States>::recv` (Block `332`) — `.ct1Sampled` Arm, Part 10 (Budget-Threaded)

Composes all budget-threaded `[LibsignalPlacement]` paths of the `.ct1Sampled` arm (`tag = 0#64 ∨
tag = 1#64`) against `Ct1SampledRecvPreEnv` / `Ct1SampledRecvPostEnv` and `Ct1SampledRecvEnv`.
-/

@[expose] public section

set_option autoImplicit false

namespace LibsignalBinary.Proofs.SpqrV1.States.Recv.ArmCt1SampledPart10PlacedBudget

open Arm64 ProofLib ProofLib.ProgramReflection
open scoped CryptoVerification.RustHeap CryptoVerification.LibsignalTripleRatchet
open CryptoGames.LibsignalSession (ShaCompress)
open CryptoVerification (
  LibsignalPlacement blkPC_332 blkPl_332 lsProg_332 lsmpl withLsCodeLoaded
)
open LibsignalBinary.Proofs.Placed.ElfLsRetAddr (LsRetAddr624)
open CryptoVerification.RustHeap (vecU8)
open CryptoVerification.LibsignalTripleRatchet (
  LibsignalCodeRoLoaded extract_withLsCodeRoLoaded sepWP_seq_lscro sessionMemcpySpec
  withLsCodeRoLoaded
)
open CryptoVerification.LibsignalSpqrV1 (
  Bytes Chunk Message MlKem PolyEncoder States spqrAuthApi spqrPolyApi
)
open CryptoVerification.LibsignalSpqrV1.Chunked.SendCt (Ct1Sampled send_ct2_encoder)
open CryptoVerification.LibsignalSpqrV1.Unchunked.SendCt (Ct1SentEkReceived)
open CryptoVerification.SpqrV1.Alloc (spqrMemcpySym)
open CryptoVerification.SpqrV1.Auth (authenticatorAt)
open CryptoVerification.SpqrV1.Drop (
  chunkedCt1SampledAt chunkedStatesAt chunkedStatesSize unchunkedCt1SentAt
)
open CryptoVerification.SpqrV1.Poly (chunkAt polyDecoderAt polyEncoderAt)
open CryptoVerification.SpqrV1.Poly.AddChunk (PolyDecoderStrictSorted addChunkTotal)
open CryptoVerification.SpqrV1.Poly.DecodedMessage (decodedMessageTotal)
open CryptoVerification.SpqrV1.States.Leaves (
  optVecU8At polyDecoderAt_dup_pts_len relocatedHeap wordsAt wordsBytes
)
open CryptoVerification.SpqrV1.States.Recv (
  StatesRecvGhost TraceCalleeSaved chunkedCt1SampledAt_eq_tag_body chunkedCt1SampledBodyAt
  copyScratchStackAt ct1Sampled_send_ct2_ok_of_recv_ek_ok ct1Sent_recv_ek_eq_ofError
  epilogueStoreStackPart1At messageAt_ekCt1Ack_eq messageAt_ek_eq messagePayloadAt_other_expose
  polyEncoderTagVal polyEncoderTagVal_zero_or_one resultV1RecvAt
  sp_sub_144_add_48 sp_sub_4192_sub_48 sp_sub_4240_add_3272 sp_sub_4240_add_3856
  sp_sub_4240_add_4096 sp_sub_4240_add_4144 sp_sub_4240_add_48 sp_sub_96_add_16
  sp_sub_96_add_32 sp_sub_96_add_48 sp_sub_96_add_64 sp_sub_96_add_80 sp_sub_96_sub_4096
  statesRecvCalleeStackX statesRecvPreInv statesRecvRoPlacedAt statesRecvSavedCells
  statesRecvStackX states_recv_ct1Sampled_eq_gt states_recv_ct1Sampled_eq_lt
  states_recv_ct1Sampled_eq_none_ack states_recv_ct1Sampled_eq_none_no_ack
  states_recv_ct1Sampled_eq_other states_recv_ct1Sampled_eq_some_err
  states_recv_ct1Sampled_eq_some_ok_no_ack unchunkedCt1SentAt_epoch_expose v1RecvSize
)
open CryptoVerification.SpqrV1.Top.MessageSerialize (messageAt messagePayloadAt)
open LibsignalBinary.Proofs.SpqrV1.States.Recv (spqrDeallocSym)
open LibsignalBinary.Heap (
  AllocCostModel AllocEvent BudgetLimits FitsEnv FreeOnlyEvs RustCliAllocBudget VmPreserved
  rustCliDeallocBudgetSpec
)
open LibsignalBinary.Heap.SpecBudget (withVmPreserved)
open LibsignalBinary.Proofs.SpqrV1.Poly.AddChunk.DefsBudget (addChunkSpecX)
open LibsignalBinary.Proofs.SpqrV1.States.Leaves.Batch2DefsPlacedBudget (
  polyDecoderDecodedMessagePlacedSpec sendCt2EncoderSpec unchunkedCt1SentRecvEkSpec
)
open LibsignalBinary.Proofs.SpqrV1.States.Recv.ArmCt1SampledPart10PlacedBudgetAux (
  Ct1SampledRecvEnv Ct1SampledRecvPostEnv Ct1SampledRecvPreEnv
  ct1SampledRecvPostEnv_ekCt1Ack_err ct1SampledRecvPostEnv_ekCt1Ack_none
  ct1SampledRecvPostEnv_ek_free ct1SampledRecvPostEnv_ek_nil
  ct1SampledRecvPostEnv_nil_other ct1SampledRecvPostEnv_of_freeOnly_ne
  ct1SampledRecvPostEnv_of_pre ct1Sampled_path_some_ok_ack_placed ct1Sampled_seq_vm_lscl
  ct1Sampled_seq_vm_lscro fitsEnv_ekCt1Ack_of_pre fitsEnv_ek_of_pre
)
open LibsignalBinary.Proofs.SpqrV1.States.Recv.ArmCt1SampledPart1PlacedBudget (
  ct1Sampled_dispatch_pool_placed ct1Sampled_drop_epochOutOfRange_placed
  ct1Sampled_prologue_pool_placed
)
open LibsignalBinary.Proofs.SpqrV1.States.Recv.ArmCt1SampledPart3PlacedBudgetAux (
  ct1Sampled_path_lt_pool_placed ct1Sampled_path_other_from_12144_pool_placed
)
open LibsignalBinary.Proofs.SpqrV1.States.Recv.ArmCt1SampledPart7PlacedBudget (
  ct1Sampled_path_none_no_ack_pool_placed ct1Sampled_recv_ek_common_prefix_sepWPp_placed
)
open LibsignalBinary.Proofs.SpqrV1.States.Recv.ArmCt1SampledPart8PlacedBudget (
  ct1Sampled_path_none_ack_placed ct1Sampled_path_some_err_placed
)
open LibsignalBinary.Proofs.SpqrV1.States.Recv.ArmCt1SampledPart9PlacedBudget (
  ct1Sampled_path_some_ok_no_ack_placed
)
open LibsignalBinary.Proofs.SpqrV1.States.Recv.DefsPlacedBudget (
  sepWPp_of_statesRecv_exit_evs_placed_ofPrePostEnv
  sepWPp_of_statesRecv_exit_placed_ofPrePostEnv statesRecvVariantPlacedSpecOfEnv
  statesRecvVariantPlacedSpecOfPrePostEnv
  subroutine_ok_statesRecvVariantPlacedSpecOfPrePostEnv_weaken
)
open LibsignalBinary.Proofs.SpqrV1.States.Recv.DispatchPlacedBudget (lsmpl_base_332_eq)
open LibsignalBinary.Proofs.SpqrV1.Unchunked.SendCt2PlacedBudget (
  unchunkedCt1SentEkReceivedSendCt2PlacedSpec
)

set_option maxRecDepth 400000
set_option maxHeartbeats 400000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.constructorNameAsVariable false

set_option allowUnsafeReducibility true in
attribute [local reducible] spqrPolyApi spqrAuthApi
attribute [local irreducible]
  Program.fetch Program.externAt? Program.fnOff CryptoVerification.blkPC_332
  addChunkTotal decodedMessageTotal
attribute [local arm64_norm, local wp_norm]
  bv_sub_add_lit BitVec.toNat_zero lsmpl_base_332_eq
  sp_sub_96_add_16 sp_sub_96_add_32 sp_sub_96_add_48 sp_sub_96_add_64 sp_sub_96_add_80
  sp_sub_96_sub_4096 sp_sub_4192_sub_48 sp_sub_4240_add_48 sp_sub_4240_add_4096 sp_sub_144_add_48
  sp_sub_4240_add_4144 sp_sub_4240_add_3856 sp_sub_4240_add_3272
  RustCliAllocBudget.pool_setPC RustCliAllocBudget.pool_advancePC
  RustCliAllocBudget.pool_setPState RustCliAllocBudget.pool_writeReg64
  RustCliAllocBudget.pool_writeReg32 RustCliAllocBudget.pool_writeReg

/-! ## 1. `VmPreserved` Sequencing & Message-Kind Dispatch Helpers (`+7052`) -/

theorem ct1Sampled_sepWPp_seq_vm_lscro [LibsignalPlacement] {prog : Program} {mid ret : BitVec 64}
    {s : State} {P : SepProp} {P_mid : State → SepProp} {Q_mid : State → Prop}
    {Q Qp : State → SepProp → Prop}
    (hcro : LibsignalCodeRoLoaded lsmpl s.mem)
    (h1 : SepWP prog mid s P (fun sm Pm => VmPreserved s sm ∧ (Pm ⊢ P_mid sm) ∧ Q_mid sm))
    (h2 : ∀ sm : State, sm.pc = mid → sm.status = .Running →
      LibsignalCodeRoLoaded lsmpl sm.mem → VmPreserved s sm → Q_mid sm →
      SepWPp prog ret sm (P_mid sm) Q Qp) :
    SepWPp prog ret s P Q Qp :=
  SepWPp.of_sepWP (sepWP_seq_lscro hcro (SepWP.mono h1 fun sm _ hpc hrun ⟨hvm, hent, hq⟩ hcrom =>
    SepWP.done hpc hrun (SepWPp.weaken_pre hent (h2 sm hpc hrun hcrom hvm hq))))

theorem ct1Sampled_msg_kind_check_other_placed [LibsignalPlacement]
    {ext : String → Option (State → State)}
    (s_in : State) (msgA : BitVec 64) (msg_tag : BitVec 8) (Rest : SepProp)
    (hne2 : (BitVec.zeroExtend 32 msg_tag == 2#32) = false)
    (hne3 : (BitVec.zeroExtend 32 msg_tag != 3#32) = true)
    (hpc : s_in.pc = (blkPl_332).base + 7052#64) (hrun : s_in.status = .Running)
    (hx24 : s_in.readReg64 .x24 = msgA) :
    SepWP (lsProg_332 (Rust.withPanics ext)) ((blkPl_332).base + 12144#64) s_in
      (((msgA + 8#64) ↦₈ msg_tag) ∗ Rest)
      (fun sf Pf => VmPreserved s_in sf ∧ (Pf ⊢ ((msgA + 8#64) ↦₈ msg_tag) ∗ Rest) ∧
        sf.sp = s_in.sp ∧ sf.readReg64 .x1 = s_in.readReg64 .x1 ∧
        sf.readReg64 .x12 = s_in.readReg64 .x12 ∧ sf.readReg64 .x19 = s_in.readReg64 .x19 ∧
        sf.readReg64 .x29 = s_in.readReg64 .x29 ∧ TraceCalleeSaved sf s_in) := by
  subst hx24; dsimp only [lsProg_332, BitVec.ofNat_eq_ofNat] at hpc ⊢; by_vm_steps (wp_steps; wp_done)

theorem ct1Sampled_msg_kind_check_ek_placed [LibsignalPlacement]
    {ext : String → Option (State → State)} (s_in : State) (msgA : BitVec 64) (Rest : SepProp)
    (hpc : s_in.pc = (blkPl_332).base + 7052#64) (hrun : s_in.status = .Running)
    (hx24 : s_in.readReg64 .x24 = msgA) :
    SepWP (lsProg_332 (Rust.withPanics ext)) ((blkPl_332).base + 11404#64) s_in
      (((msgA + 8#64) ↦₈ 2#8) ∗ Rest)
      (fun sf Pf => VmPreserved s_in sf ∧ (Pf ⊢ ((msgA + 8#64) ↦₈ 2#8) ∗ Rest) ∧
        sf.sp = s_in.sp ∧ sf.readReg64 .x1 = s_in.readReg64 .x1 ∧
        sf.readReg64 .x19 = s_in.readReg64 .x19 ∧ sf.readReg64 .x20 = s_in.readReg64 .x20 ∧
        sf.readReg64 .x21 = s_in.readReg64 .x21 ∧ sf.readReg64 .x22 = 0#64 ∧
        sf.readReg64 .x23 = s_in.readReg64 .x12 ∧ sf.readReg64 .x24 = msgA ∧
        sf.readReg64 .x28 = s_in.readReg64 .x28 ∧ sf.readReg64 .x29 = s_in.readReg64 .x29 ∧
        TraceCalleeSaved sf s_in) := by
  subst hx24; dsimp only [lsProg_332, BitVec.ofNat_eq_ofNat] at hpc ⊢; by_vm_steps (wp_steps; wp_done)

theorem ct1Sampled_msg_kind_check_ekCt1Ack_placed [LibsignalPlacement]
    {ext : String → Option (State → State)} (s_in : State) (msgA : BitVec 64) (Rest : SepProp)
    (hpc : s_in.pc = (blkPl_332).base + 7052#64) (hrun : s_in.status = .Running)
    (hx24 : s_in.readReg64 .x24 = msgA) :
    SepWP (lsProg_332 (Rust.withPanics ext)) ((blkPl_332).base + 11404#64) s_in
      (((msgA + 8#64) ↦₈ 3#8) ∗ Rest)
      (fun sf Pf => VmPreserved s_in sf ∧ (Pf ⊢ ((msgA + 8#64) ↦₈ 3#8) ∗ Rest) ∧
        sf.sp = s_in.sp ∧ sf.readReg64 .x1 = s_in.readReg64 .x1 ∧
        sf.readReg64 .x19 = s_in.readReg64 .x19 ∧ sf.readReg64 .x20 = s_in.readReg64 .x20 ∧
        sf.readReg64 .x21 = s_in.readReg64 .x21 ∧ sf.readReg64 .x22 = 1#64 ∧
        sf.readReg64 .x23 = s_in.readReg64 .x12 ∧ sf.readReg64 .x24 = msgA ∧
        sf.readReg64 .x28 = s_in.readReg64 .x28 ∧ sf.readReg64 .x29 = s_in.readReg64 .x29 ∧
        TraceCalleeSaved sf s_in) := by
  subst hx24; dsimp only [lsProg_332, BitVec.ofNat_eq_ofNat] at hpc ⊢; by_vm_steps (wp_steps; wp_done)

/-! ## 2. Budget-Threaded `.ek` & `.ekCt1Ack` Sub-Arms (`+1528 -> s0.x30`) -/

set_option maxHeartbeats 2000000 in
/-- Complete budget-threaded `.ct1Sampled` arm from `+1528 -> s0.x30` for `msg.payload = .ek chunk`. -/
theorem ct1Sampled_arm_eq_ek_placed [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {F : ShaCompress} {K : MlKem}
    {PreEnv : StatesRecvGhost F → List AllocEvent → Prop}
    {ext : String → Option (State → State)}
    (hdealloc : HookSat (Rust.withPanics ext) spqrDeallocSym (rustCliDeallocBudgetSpec M A lim))
    (hmemcpy : HookSat (Rust.withPanics ext) spqrMemcpySym (withVmPreserved sessionMemcpySpec))
    (hadd_call : subroutine_ok (lsProg_332 (Rust.withPanics ext))
      (lsmpl.base 419) (withLsCodeLoaded lsmpl (addChunkSpecX M A lim)))
    (hdec_call : subroutine_ok (lsProg_332 (Rust.withPanics ext))
      (lsmpl.base 418) (withLsCodeRoLoaded lsmpl (polyDecoderDecodedMessagePlacedSpec M A lim)))
    (hrecv_ek : subroutine_ok (lsProg_332 (Rust.withPanics ext))
      (lsmpl.base 338) (withLsCodeLoaded lsmpl (unchunkedCt1SentRecvEkSpec M A lim F K)))
    (st_cost : M.σ) (s0 s2 : State) (outA selfA msgA : BitVec 64)
    (st : Ct1Sampled spqrPolyApi (spqrAuthApi F))
    (msg : Message spqrPolyApi) (chunk : Chunk) (R : SepProp)
    (hcro2 : LibsignalCodeRoLoaded lsmpl s2.mem)
    (hsort : PolyDecoderStrictSorted st.receiving_ek)
    (hfits : FitsEnv M lim st_cost (Ct1SampledRecvPreEnv K st msg))
    (heq : msg.epoch = st.uc.epoch) (hpay : msg.payload = .ek chunk)
    (hsp0_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hpc2 : s2.pc = (blkPl_332).base + 1528#64)
    (hrun2 : s2.status = .Running) (hsp2 : s2.sp = s0.sp - 4240#64)
    (hx1 : s2.readReg64 .x1 = selfA) (hx12 : s2.readReg64 .x12 = polyEncoderTagVal st.sending_ct1)
    (hx19 : s2.readReg64 .x19 = outA) (hx21 : s2.readReg64 .x21 = (s0.sp - 4240#64) + 3856#64)
    (hx24 : s2.readReg64 .x24 = msgA) (hx28 : s2.readReg64 .x28 = (s0.sp - 4240#64) + 3272#64)
    (hx29 : s2.readReg64 .x29 = s0.sp - 96#64) (htr2 : TraceCalleeSaved s2 s0) :
    SepWPp (lsProg_332 (Rust.withPanics ext)) (s0.readReg64 .x30) s2
      (memRegion outA v1RecvSize ∗ chunkedStatesAt A.repAlloc selfA (.ct1Sampled st) ∗
        messageAt spqrPolyApi msgA msg ∗ statesRecvRoPlacedAt ∗ A.pool lim st_cost s2 ∗
        stackAt (s0.sp - 4240#64) statesRecvCalleeStackX ∗
        memRegion (s0.sp - 4240#64) 4144 ∗ statesRecvSavedCells s0)
      (fun sf P_f =>
        (sf.mem ⊨ P_f ∗ R →
          sf.mem ⊨
            (statesRecvVariantPlacedSpecOfPrePostEnv M A lim F K (.ct1Sampled st) msg
              PreEnv (fun _ => Ct1SampledRecvPostEnv K st msg)).post
              ((outA, selfA, msgA), st_cost) s0 sf ∗ R) ∧
        sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf)
      (fun sf P_f =>
        sf.mem ⊨ P_f ∗ R →
          sf.mem ⊨
            (statesRecvVariantPlacedSpecOfPrePostEnv M A lim F K (.ct1Sampled st) msg
              PreEnv (fun _ => Ct1SampledRecvPostEnv K st msg)).onPanic
              ((outA, selfA, msgA), st_cost) s0 sf ∗ R) := by
  have hfsp_align : ((s0.sp - 4240#64) &&& 15#64 == 0#64) = true :=
    spAligned_sub s0.sp 4240#64 hsp0_align (by decide)
  obtain ⟨hfits_add, hfits_dec⟩ := fitsEnv_ek_of_pre (s0.sp - 4240#64) msgA heq hpay hfits
  have hpre :
      memRegion outA v1RecvSize ∗ chunkedStatesAt A.repAlloc selfA (.ct1Sampled st) ∗
        messageAt spqrPolyApi msgA msg ∗ statesRecvRoPlacedAt ∗ A.pool lim st_cost s2 ∗
        stackAt (s0.sp - 4240#64) statesRecvCalleeStackX ∗
        memRegion (s0.sp - 4240#64) 4144 ∗ statesRecvSavedCells s0 ⊢
      ⌜st.receiving_ek.pts.length = 16⌝ ∗
      (((selfA + 520#64) ↦₆₄ st.uc.epoch) ∗ (msgA ↦₆₄ st.uc.epoch) ∗
        (((msgA + 8#64) ↦₈ 2#8) ∗
          (authenticatorAt A.repAlloc (selfA + 400#64) st.uc.auth ∗
            vecU8 A.repAlloc (selfA + 448#64) st.uc.hdr ∗
            vecU8 A.repAlloc (selfA + 472#64) st.uc.es ∗
            vecU8 A.repAlloc (selfA + 496#64) st.uc.ct1) ∗
          polyEncoderAt A.repAlloc selfA st.sending_ct1 ∗
          polyDecoderAt A.repAlloc (selfA + 528#64) st.receiving_ek ∗
          memRegion (msgA + 9#64) 1 ∗ chunkAt (msgA + 10#64) chunk ∗ memRegion (msgA + 44#64) 4 ∗
          memRegion outA v1RecvSize ∗ statesRecvRoPlacedAt ∗ A.pool lim st_cost s2 ∗
          stackAt (s0.sp - 4240#64) statesRecvCalleeStackX ∗
          memRegion (s0.sp - 4240#64) 4144 ∗ statesRecvSavedCells s0)) := by
    dsimp only [chunkedStatesAt, chunkedCt1SampledAt]
    rw [unchunkedCt1SentAt_epoch_expose A.repAlloc selfA st.uc,
        messageAt_ek_eq msgA msg chunk hpay, heq]
    refine Entails.trans (sepConj_mono_right (sepConj_mono_left
      (sepConj_mono_right (sepConj_mono_right
        (polyDecoderAt_dup_pts_len A.repAlloc (selfA + 528#64) st.receiving_ek))))) ?_
    exact Entails.of_eq (by sep_ac_rfl)
  refine SepWPp.weaken_pre hpre ?_
  apply SepWPp.of_sepWP (mid := (blkPl_332).base + 11404#64)
  wp_focus_pure; intro hlen
  refine ct1Sampled_seq_vm_lscro hcro2
    (ArmCt1SampledPart1PlacedBudget.ct1Sampled_epoch_cmp_eq_placed s2 selfA msgA st.uc.epoch _ hpc2 hrun2 hx1 hx24) ?_
  intro s3 hpc3 hrun3 hcro3 hvm23
    ⟨hsp3, _, hx1_3, _, _, hx12_3, hx19_3, hx20_3, hx21_3, hx24_3, hx28_3, hx29_3, htr3⟩
  refine SepWP.weaken_pre (show _ ⊢
      ((msgA + 8#64) ↦₈ 2#8) ∗
      (polyEncoderAt A.repAlloc selfA st.sending_ct1 ∗
        unchunkedCt1SentAt A.repAlloc (selfA + 400#64) st.uc ∗
        polyDecoderAt A.repAlloc (selfA + 528#64) st.receiving_ek ∗
        chunkAt (msgA + 10#64) chunk ∗
        statesRecvRoPlacedAt ∗ A.pool lim st_cost s3 ∗
        stackAt (s0.sp - 4240#64) statesRecvCalleeStackX ∗
        memRegion (s0.sp - 4240#64) 4144 ∗
        (memRegion outA v1RecvSize ∗ statesRecvSavedCells s0 ∗
          (msgA ↦₆₄ st.uc.epoch) ∗ memRegion (msgA + 9#64) 1 ∗ memRegion (msgA + 44#64) 4)) by
    rw [unchunkedCt1SentAt_epoch_expose A.repAlloc selfA st.uc,
        ← A.pool_transport lim st_cost s2 s3 hvm23]
    exact Entails.of_eq (by sep_ac_rfl)) ?_
  refine ct1Sampled_seq_vm_lscro hcro3
    (ct1Sampled_msg_kind_check_ek_placed s3 msgA _ hpc3 hrun3 hx24_3) ?_
  intro s4 hpc4 hrun4 hcro4 hvm34
    ⟨hsp4, hx1_4, hx19_4, hx20_4, hx21_4, hx22_4, hx23_4, hx24_4, hx28_4, hx29_4, htr4⟩
  have hP4' :
      ((msgA + 8#64) ↦₈ 2#8) ∗
        (polyEncoderAt A.repAlloc selfA st.sending_ct1 ∗
          unchunkedCt1SentAt A.repAlloc (selfA + 400#64) st.uc ∗
          polyDecoderAt A.repAlloc (selfA + 528#64) st.receiving_ek ∗
          chunkAt (msgA + 10#64) chunk ∗
          statesRecvRoPlacedAt ∗ A.pool lim st_cost s3 ∗
          stackAt (s0.sp - 4240#64) statesRecvCalleeStackX ∗
          memRegion (s0.sp - 4240#64) 4144 ∗
          (memRegion outA v1RecvSize ∗ statesRecvSavedCells s0 ∗
            (msgA ↦₆₄ st.uc.epoch) ∗ memRegion (msgA + 9#64) 1 ∗ memRegion (msgA + 44#64) 4)) ⊢
      polyEncoderAt A.repAlloc selfA st.sending_ct1 ∗
        unchunkedCt1SentAt A.repAlloc (selfA + 400#64) st.uc ∗
        polyDecoderAt A.repAlloc (selfA + 528#64) st.receiving_ek ∗
        chunkAt (msgA + 10#64) chunk ∗
        statesRecvRoPlacedAt ∗ A.pool lim st_cost s4 ∗
        stackAt (s0.sp - 4240#64) statesRecvCalleeStackX ∗
        memRegion (s0.sp - 4240#64) 4144 ∗
        (memRegion outA v1RecvSize ∗ statesRecvSavedCells s0 ∗
          ((msgA + 8#64) ↦₈ 2#8) ∗ (msgA ↦₆₄ st.uc.epoch) ∗
          memRegion (msgA + 9#64) 1 ∗ memRegion (msgA + 44#64) 4) := by
    rw [← A.pool_transport lim st_cost s3 s4 hvm34]
    exact Entails.of_eq (by sep_ac_rfl)
  refine SepWP.weaken_pre hP4' ?_
  apply SepWP.done hpc4 hrun4
  have hx29_fsp : s4.readReg64 .x29 = (s0.sp - 4240#64) + 4144#64 := by
    rw [hx29_4, hx29_3, hx29, sp_sub_4240_add_4144]
  refine ct1Sampled_recv_ek_common_prefix_sepWPp_placed
    hmemcpy hadd_call hdec_call st_cost s0 s4 (s0.sp - 4240#64) selfA outA msgA 0#64 st chunk
    hlen hsort hfits_add hfits_dec _
    hcro4 hfsp_align hpc4 hrun4 (hsp4.trans (hsp3.trans hsp2)) (hx1_4.trans hx1_3)
    (hx19_4.trans (hx19_3.trans hx19)) (hx20_4.trans hx20_3) (hx21_4.trans (hx21_3.trans hx21))
    hx22_4 (hx23_4.trans (hx12_3.trans hx12)) hx24_4 (hx28_4.trans (hx28_3.trans hx28))
    hx29_fsp (htr4.trans (htr3.trans htr2)) ?_
  intro s5 c_uc sc k evsAdd evsDec hpc5 hrun5 hsp5 hx19_5 hx20_5 hx21_5 hx22_5 hx23_5 _
    hx28_5 hx29_5 htr5 _hcro5 hcl5 hevsAdd hevsDec _hsort'
  have hmsg_join :
      chunkAt (msgA + 10#64) chunk ∗ ((msgA + 8#64) ↦₈ 2#8) ∗ (msgA ↦₆₄ st.uc.epoch) ∗
        memRegion (msgA + 9#64) 1 ∗ memRegion (msgA + 44#64) 4 =
      messageAt spqrPolyApi msgA msg := by
    rw [messageAt_ek_eq msgA msg chunk hpay, heq]; sep_ac_rfl
  have hdec_cases :
      decodedMessageTotal (addChunkTotal st.receiving_ek chunk) = none ∨
      ∃ decoded, decodedMessageTotal (addChunkTotal st.receiving_ek chunk) = some decoded := by
    cases decodedMessageTotal (addChunkTotal st.receiving_ek chunk) with
    | none => exact Or.inl rfl
    | some d => exact Or.inr ⟨d, rfl⟩
  rcases hdec_cases with hdec_opt | ⟨decoded, hdec_opt⟩
  · refine SepWPp.weaken_pre (Entails.of_eq (show _ =
      optVecU8At A.repAlloc ((s0.sp - 4240#64) + 3832#64) none ∗
        polyDecoderAt A.repAlloc ((s0.sp - 4240#64) + 2752#64)
          (addChunkTotal st.receiving_ek chunk) ∗
        polyEncoderAt A.repAlloc selfA st.sending_ct1 ∗ wordsAt (selfA + 400#64) c_uc.toList ∗
        wordsAt ((s0.sp - 4240#64) + 3696#64) c_uc.toList ∗
        relocatedHeap (fun a => unchunkedCt1SentAt A.repAlloc a st.uc) (wordsBytes c_uc.toList) ∗
        memRegion (selfA + 528#64) 400 ∗ copyScratchStackAt (s0.sp - 4240#64) sc ∗
        epilogueStoreStackPart1At (s0.sp - 4240#64) k ∗ (((s0.sp - 4240#64) + 232#64) ↦₆₄ selfA) ∗
        (((s0.sp - 4240#64) + 512#64) ↦₆₄ k.w200) ∗ (((s0.sp - 4240#64) + 520#64) ↦₆₄ k.w208) ∗
        wordsAt ((s0.sp - 4240#64) + 528#64) k.tail.toList ∗
        memRegion ((s0.sp - 4240#64) + 576#64) 376 ∗ memRegion ((s0.sp - 4240#64) + 568#64) 8 ∗
        memRegion ((s0.sp - 4240#64) + 952#64) 8 ∗ memRegion ((s0.sp - 4240#64) + 976#64) 1776 ∗
        memRegion ((s0.sp - 4240#64) + 3152#64) 544 ∗ memRegion ((s0.sp - 4240#64) + 3824#64) 8 ∗
        memRegion ((s0.sp - 4240#64) + 3856#64) 288 ∗ memRegion outA v1RecvSize ∗
        A.pool lim (M.stepEvents (evsAdd ++ evsDec) st_cost) s5 ∗
        stackAt (s0.sp - 4240#64) statesRecvCalleeStackX ∗ statesRecvSavedCells s0 ∗
        (statesRecvRoPlacedAt ∗
          (chunkAt (msgA + 10#64) chunk ∗ ((msgA + 8#64) ↦₈ 2#8) ∗ (msgA ↦₆₄ st.uc.epoch) ∗
            memRegion (msgA + 9#64) 1 ∗ memRegion (msgA + 44#64) 4)) by
      rw [hdec_opt]; sep_ac_rfl)) ?_
    rw [hmsg_join]
    refine sepWPp_of_statesRecv_exit_evs_placed_ofPrePostEnv
      (PreEnv := PreEnv) (PostEnv := fun _ => Ct1SampledRecvPostEnv K st msg)
      s0 s5 outA selfA msgA (.ct1Sampled st) msg st_cost (evsAdd ++ evsDec)
      (ct1SampledRecvPostEnv_ek_nil K heq hpay hevsAdd hevsDec) _ R ?_
    rw [states_recv_ct1Sampled_eq_none_no_ack K st msg chunk heq hpay hlen hsort hdec_opt]
    refine SepWP.mono
      (ct1Sampled_path_none_no_ack_pool_placed hmemcpy
        (M.stepEvents (evsAdd ++ evsDec) st_cost) s0 s5 (s0.sp - 4240#64) selfA outA st
        (addChunkTotal st.receiving_ek chunk) c_uc sc k
        (statesRecvRoPlacedAt ∗ messageAt spqrPolyApi msgA msg)
        hfsp_align hsp0_align rfl hpc5 hrun5 hsp5 hx19_5 hx22_5 hx23_5 hx29_5 htr5) ?_
    intro sf Pf _ _ ⟨_, hPf, hsp_f, hcs_f, htr_f⟩
    exact ⟨Entails.trans hPf (Entails.of_eq (by sep_ac_rfl)), hsp_f, hcs_f, htr_f⟩
  · have hrek_eq := ct1Sent_recv_ek_eq_ofError K st.uc decoded
    dsimp only at hrek_eq
    split_ifs at hrek_eq with hpk
    · let uc_ek : Ct1SentEkReceived (spqrAuthApi F) :=
        { epoch := st.uc.epoch, auth := st.uc.auth, es := st.uc.es, ek := decoded, ct1 := st.uc.ct1 }
      have hrek : st.uc.recv_ek K st.uc.epoch decoded = .ok uc_ek := hrek_eq
      refine SepWPp.weaken_pre (Entails.of_eq (show _ =
        optVecU8At A.repAlloc ((s0.sp - 4240#64) + 3832#64) (some decoded) ∗
          polyDecoderAt A.repAlloc ((s0.sp - 4240#64) + 2752#64)
            (addChunkTotal st.receiving_ek chunk) ∗
          polyEncoderAt A.repAlloc selfA st.sending_ct1 ∗ wordsAt (selfA + 400#64) c_uc.toList ∗
          wordsAt ((s0.sp - 4240#64) + 3696#64) c_uc.toList ∗
          relocatedHeap (fun a => unchunkedCt1SentAt A.repAlloc a st.uc) (wordsBytes c_uc.toList) ∗
          memRegion (selfA + 528#64) 400 ∗ copyScratchStackAt (s0.sp - 4240#64) sc ∗
          epilogueStoreStackPart1At (s0.sp - 4240#64) k ∗ (((s0.sp - 4240#64) + 232#64) ↦₆₄ selfA) ∗
          (((s0.sp - 4240#64) + 512#64) ↦₆₄ k.w200) ∗ (((s0.sp - 4240#64) + 520#64) ↦₆₄ k.w208) ∗
          wordsAt ((s0.sp - 4240#64) + 528#64) k.tail.toList ∗
          memRegion ((s0.sp - 4240#64) + 576#64) 376 ∗ memRegion ((s0.sp - 4240#64) + 568#64) 8 ∗
          memRegion ((s0.sp - 4240#64) + 952#64) 8 ∗ memRegion ((s0.sp - 4240#64) + 976#64) 1776 ∗
          memRegion ((s0.sp - 4240#64) + 3152#64) 544 ∗ memRegion ((s0.sp - 4240#64) + 3824#64) 8 ∗
          memRegion ((s0.sp - 4240#64) + 3856#64) 288 ∗ memRegion outA v1RecvSize ∗ statesRecvRoPlacedAt ∗
          A.pool lim (M.stepEvents (evsAdd ++ evsDec) st_cost) s5 ∗
          stackAt (s0.sp - 4240#64) statesRecvCalleeStackX ∗ statesRecvSavedCells s0 ∗
          (chunkAt (msgA + 10#64) chunk ∗ ((msgA + 8#64) ↦₈ 2#8) ∗ (msgA ↦₆₄ st.uc.epoch) ∗
            memRegion (msgA + 9#64) 1 ∗ memRegion (msgA + 44#64) 4) by
        rw [hdec_opt]; sep_ac_rfl)) ?_
      rw [hmsg_join]
      refine sepWPp_of_statesRecv_exit_placed_ofPrePostEnv
        (PreEnv := PreEnv) (PostEnv := fun _ => Ct1SampledRecvPostEnv K st msg)
        s0 s5 outA selfA msgA (.ct1Sampled st) msg st_cost _ R ?_
      rw [states_recv_ct1Sampled_eq_some_ok_no_ack K st msg chunk decoded uc_ek
        heq hpay hlen hsort hdec_opt hrek]
      refine SepWP.mono
        (ArmCt1SampledPart9PlacedBudget.ct1Sampled_path_some_ok_no_ack_placed hdealloc hmemcpy hrecv_ek
          (M.stepEvents (evsAdd ++ evsDec) st_cost) s0 s5 (s0.sp - 4240#64)
          selfA outA st (addChunkTotal st.receiving_ek chunk) c_uc decoded uc_ek sc k
          (messageAt spqrPolyApi msgA msg) hcl5 hrek hfsp_align hsp0_align rfl
          hpc5 hrun5 hsp5 hx19_5 hx20_5 hx21_5 hx22_5 hx23_5 hx28_5 hx29_5 htr5) ?_
      intro sf Pf _ _ ⟨evsTail, hevsTail, hPf, hsp_f, hcs_f, htr_f⟩
      have hst_eq :
          M.stepEvents evsTail (M.stepEvents (evsAdd ++ evsDec) st_cost) =
            M.stepEvents ((evsAdd ++ evsDec) ++ evsTail) st_cost :=
        (M.stepEvents_append (evsAdd ++ evsDec) evsTail st_cost).symm
      exact ⟨⟨(evsAdd ++ evsDec) ++ evsTail,
        ct1SampledRecvPostEnv_ek_free K heq hpay hevsAdd hevsDec hevsTail,
        Entails.trans hPf (Entails.of_eq (by rw [hst_eq]; sep_ac_rfl))⟩,
        hsp_f, hcs_f, htr_f⟩
    · have hrek : st.uc.recv_ek K st.uc.epoch decoded = .error (.err .erroneousDataReceived) := hrek_eq
      refine SepWPp.weaken_pre (Entails.of_eq (show _ =
        optVecU8At A.repAlloc ((s0.sp - 4240#64) + 3832#64) (some decoded) ∗
          polyDecoderAt A.repAlloc ((s0.sp - 4240#64) + 2752#64)
            (addChunkTotal st.receiving_ek chunk) ∗
          polyEncoderAt A.repAlloc selfA st.sending_ct1 ∗ wordsAt (selfA + 400#64) c_uc.toList ∗
          wordsAt ((s0.sp - 4240#64) + 3696#64) c_uc.toList ∗
          relocatedHeap (fun a => unchunkedCt1SentAt A.repAlloc a st.uc) (wordsBytes c_uc.toList) ∗
          memRegion (selfA + 528#64) 400 ∗ copyScratchStackAt (s0.sp - 4240#64) sc ∗
          epilogueStoreStackPart1At (s0.sp - 4240#64) k ∗ (((s0.sp - 4240#64) + 232#64) ↦₆₄ selfA) ∗
          (((s0.sp - 4240#64) + 512#64) ↦₆₄ k.w200) ∗ (((s0.sp - 4240#64) + 520#64) ↦₆₄ k.w208) ∗
          wordsAt ((s0.sp - 4240#64) + 528#64) k.tail.toList ∗
          memRegion ((s0.sp - 4240#64) + 576#64) 376 ∗ memRegion ((s0.sp - 4240#64) + 568#64) 8 ∗
          memRegion ((s0.sp - 4240#64) + 952#64) 8 ∗ memRegion ((s0.sp - 4240#64) + 976#64) 1776 ∗
          memRegion ((s0.sp - 4240#64) + 3152#64) 544 ∗ memRegion ((s0.sp - 4240#64) + 3824#64) 8 ∗
          memRegion ((s0.sp - 4240#64) + 3856#64) 288 ∗ memRegion outA v1RecvSize ∗
          A.pool lim (M.stepEvents (evsAdd ++ evsDec) st_cost) s5 ∗
          stackAt (s0.sp - 4240#64) statesRecvCalleeStackX ∗ statesRecvSavedCells s0 ∗
          (statesRecvRoPlacedAt ∗
            (chunkAt (msgA + 10#64) chunk ∗ ((msgA + 8#64) ↦₈ 2#8) ∗ (msgA ↦₆₄ st.uc.epoch) ∗
              memRegion (msgA + 9#64) 1 ∗ memRegion (msgA + 44#64) 4)) by
        rw [hdec_opt]; sep_ac_rfl)) ?_
      rw [hmsg_join]
      refine sepWPp_of_statesRecv_exit_placed_ofPrePostEnv
        (PreEnv := PreEnv) (PostEnv := fun _ => Ct1SampledRecvPostEnv K st msg)
        s0 s5 outA selfA msgA (.ct1Sampled st) msg st_cost _ R ?_
      rw [states_recv_ct1Sampled_eq_some_err K st msg chunk decoded .erroneousDataReceived
        heq (Or.inl hpay) hlen hsort hdec_opt hrek]
      refine SepWP.mono
        (ArmCt1SampledPart8PlacedBudget.ct1Sampled_path_some_err_placed hdealloc hrecv_ek
          (M.stepEvents (evsAdd ++ evsDec) st_cost) s0 s5 (s0.sp - 4240#64) selfA outA st
          (addChunkTotal st.receiving_ek chunk) c_uc decoded .erroneousDataReceived sc k
          (statesRecvRoPlacedAt ∗ messageAt spqrPolyApi msgA msg)
          hcl5 hrek rfl hfsp_align hsp0_align rfl hpc5 hrun5 hsp5 hx19_5 hx20_5 htr5) ?_
      intro sf Pf _ _ ⟨evsTail, hevsTail, hPf, hsp_f, hcs_f, htr_f⟩
      have hst_eq :
          M.stepEvents evsTail (M.stepEvents (evsAdd ++ evsDec) st_cost) =
            M.stepEvents ((evsAdd ++ evsDec) ++ evsTail) st_cost :=
        (M.stepEvents_append (evsAdd ++ evsDec) evsTail st_cost).symm
      exact ⟨⟨(evsAdd ++ evsDec) ++ evsTail,
        ct1SampledRecvPostEnv_ek_free K heq hpay hevsAdd hevsDec hevsTail,
        Entails.trans hPf (Entails.of_eq (by rw [hst_eq]; sep_ac_rfl))⟩,
        hsp_f, hcs_f, htr_f⟩

set_option maxHeartbeats 2000000 in
/-- Complete budget-threaded `.ct1Sampled` arm from `+1528 -> s0.x30` for
    `msg.payload = .ekCt1Ack chunk`. -/
theorem ct1Sampled_arm_eq_ekCt1Ack_placed [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {F : ShaCompress} {K : MlKem}
    {PreEnv : StatesRecvGhost F → List AllocEvent → Prop}
    {ext : String → Option (State → State)}
    (hdealloc : HookSat (Rust.withPanics ext) spqrDeallocSym (rustCliDeallocBudgetSpec M A lim))
    (hmemcpy : HookSat (Rust.withPanics ext) spqrMemcpySym (withVmPreserved sessionMemcpySpec))
    (hadd_call : subroutine_ok (lsProg_332 (Rust.withPanics ext))
      (lsmpl.base 419) (withLsCodeLoaded lsmpl (addChunkSpecX M A lim)))
    (hdec_call : subroutine_ok (lsProg_332 (Rust.withPanics ext))
      (lsmpl.base 418) (withLsCodeRoLoaded lsmpl (polyDecoderDecodedMessagePlacedSpec M A lim)))
    (hrecv_ek : subroutine_ok (lsProg_332 (Rust.withPanics ext))
      (lsmpl.base 338) (withLsCodeLoaded lsmpl (unchunkedCt1SentRecvEkSpec M A lim F K)))
    (hsendCt2 : subroutine_ok (lsProg_332 (Rust.withPanics ext))
      (lsmpl.base 347)
      (withLsCodeLoaded lsmpl (unchunkedCt1SentEkReceivedSendCt2PlacedSpec M A lim F K)))
    (hsendCt2Enc : subroutine_ok (lsProg_332 (Rust.withPanics ext))
      (lsmpl.base 382) (withLsCodeLoaded lsmpl (sendCt2EncoderSpec M A lim)))
    (st_cost : M.σ) (s0 s2 : State) (outA selfA msgA : BitVec 64)
    (st : Ct1Sampled spqrPolyApi (spqrAuthApi F))
    (msg : Message spqrPolyApi) (chunk : Chunk) (R : SepProp)
    (hcro2 : LibsignalCodeRoLoaded lsmpl s2.mem)
    (hsort : PolyDecoderStrictSorted st.receiving_ek)
    (hfits : FitsEnv M lim st_cost (Ct1SampledRecvPreEnv K st msg))
    (h_sendCt2 : ∀ decoded (uc_ek : Ct1SentEkReceived (spqrAuthApi F)),
      decodedMessageTotal (addChunkTotal st.receiving_ek chunk) = some decoded →
      st.uc.recv_ek K st.uc.epoch decoded = .ok uc_ek →
      ∃ outUc ct2 mac outEnc,
        uc_ek.send_ct2 K = .ok (outUc, ct2, mac) ∧
        send_ct2_encoder spqrPolyApi ct2 mac = .ok outEnc)
    (heq : msg.epoch = st.uc.epoch) (hpay : msg.payload = .ekCt1Ack chunk)
    (hsp0_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hpc2 : s2.pc = (blkPl_332).base + 1528#64)
    (hrun2 : s2.status = .Running) (hsp2 : s2.sp = s0.sp - 4240#64)
    (hx1 : s2.readReg64 .x1 = selfA) (hx12 : s2.readReg64 .x12 = polyEncoderTagVal st.sending_ct1)
    (hx19 : s2.readReg64 .x19 = outA) (hx21 : s2.readReg64 .x21 = (s0.sp - 4240#64) + 3856#64)
    (hx24 : s2.readReg64 .x24 = msgA) (hx28 : s2.readReg64 .x28 = (s0.sp - 4240#64) + 3272#64)
    (hx29 : s2.readReg64 .x29 = s0.sp - 96#64) (htr2 : TraceCalleeSaved s2 s0) :
    SepWPp (lsProg_332 (Rust.withPanics ext)) (s0.readReg64 .x30) s2
      (memRegion outA v1RecvSize ∗ chunkedStatesAt A.repAlloc selfA (.ct1Sampled st) ∗
        messageAt spqrPolyApi msgA msg ∗ statesRecvRoPlacedAt ∗ A.pool lim st_cost s2 ∗
        stackAt (s0.sp - 4240#64) statesRecvCalleeStackX ∗
        memRegion (s0.sp - 4240#64) 4144 ∗ statesRecvSavedCells s0)
      (fun sf P_f =>
        (sf.mem ⊨ P_f ∗ R →
          sf.mem ⊨
            (statesRecvVariantPlacedSpecOfPrePostEnv M A lim F K (.ct1Sampled st) msg
              PreEnv (fun _ => Ct1SampledRecvPostEnv K st msg)).post
              ((outA, selfA, msgA), st_cost) s0 sf ∗ R) ∧
        sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf)
      (fun sf P_f =>
        sf.mem ⊨ P_f ∗ R →
          sf.mem ⊨
            (statesRecvVariantPlacedSpecOfPrePostEnv M A lim F K (.ct1Sampled st) msg
              PreEnv (fun _ => Ct1SampledRecvPostEnv K st msg)).onPanic
              ((outA, selfA, msgA), st_cost) s0 sf ∗ R) := by
  have hfsp_align : ((s0.sp - 4240#64) &&& 15#64 == 0#64) = true :=
    spAligned_sub s0.sp 4240#64 hsp0_align (by decide)
  obtain ⟨hfits_add, hfits_dec, hfits_tail⟩ :=
    fitsEnv_ekCt1Ack_of_pre (s0.sp - 4240#64) msgA heq hpay hfits
  have hpre :
      memRegion outA v1RecvSize ∗ chunkedStatesAt A.repAlloc selfA (.ct1Sampled st) ∗
        messageAt spqrPolyApi msgA msg ∗ statesRecvRoPlacedAt ∗ A.pool lim st_cost s2 ∗
        stackAt (s0.sp - 4240#64) statesRecvCalleeStackX ∗
        memRegion (s0.sp - 4240#64) 4144 ∗ statesRecvSavedCells s0 ⊢
      ⌜st.receiving_ek.pts.length = 16⌝ ∗
      (((selfA + 520#64) ↦₆₄ st.uc.epoch) ∗ (msgA ↦₆₄ st.uc.epoch) ∗
        (((msgA + 8#64) ↦₈ 3#8) ∗
          (authenticatorAt A.repAlloc (selfA + 400#64) st.uc.auth ∗
            vecU8 A.repAlloc (selfA + 448#64) st.uc.hdr ∗
            vecU8 A.repAlloc (selfA + 472#64) st.uc.es ∗
            vecU8 A.repAlloc (selfA + 496#64) st.uc.ct1) ∗
          polyEncoderAt A.repAlloc selfA st.sending_ct1 ∗
          polyDecoderAt A.repAlloc (selfA + 528#64) st.receiving_ek ∗
          memRegion (msgA + 9#64) 1 ∗ chunkAt (msgA + 10#64) chunk ∗ memRegion (msgA + 44#64) 4 ∗
          memRegion outA v1RecvSize ∗ statesRecvRoPlacedAt ∗ A.pool lim st_cost s2 ∗
          stackAt (s0.sp - 4240#64) statesRecvCalleeStackX ∗
          memRegion (s0.sp - 4240#64) 4144 ∗ statesRecvSavedCells s0)) := by
    dsimp only [chunkedStatesAt, chunkedCt1SampledAt]
    rw [unchunkedCt1SentAt_epoch_expose A.repAlloc selfA st.uc,
        messageAt_ekCt1Ack_eq msgA msg chunk hpay, heq]
    refine Entails.trans (sepConj_mono_right (sepConj_mono_left
      (sepConj_mono_right (sepConj_mono_right
        (polyDecoderAt_dup_pts_len A.repAlloc (selfA + 528#64) st.receiving_ek))))) ?_
    exact Entails.of_eq (by sep_ac_rfl)
  refine SepWPp.weaken_pre hpre ?_
  apply SepWPp.of_sepWP (mid := (blkPl_332).base + 11404#64)
  wp_focus_pure; intro hlen
  refine ct1Sampled_seq_vm_lscro hcro2
    (ArmCt1SampledPart1PlacedBudget.ct1Sampled_epoch_cmp_eq_placed s2 selfA msgA st.uc.epoch _ hpc2 hrun2 hx1 hx24) ?_
  intro s3 hpc3 hrun3 hcro3 hvm23
    ⟨hsp3, _, hx1_3, _, _, hx12_3, hx19_3, hx20_3, hx21_3, hx24_3, hx28_3, hx29_3, htr3⟩
  refine SepWP.weaken_pre (show _ ⊢
      ((msgA + 8#64) ↦₈ 3#8) ∗
      (polyEncoderAt A.repAlloc selfA st.sending_ct1 ∗
        unchunkedCt1SentAt A.repAlloc (selfA + 400#64) st.uc ∗
        polyDecoderAt A.repAlloc (selfA + 528#64) st.receiving_ek ∗
        chunkAt (msgA + 10#64) chunk ∗
        statesRecvRoPlacedAt ∗ A.pool lim st_cost s3 ∗
        stackAt (s0.sp - 4240#64) statesRecvCalleeStackX ∗
        memRegion (s0.sp - 4240#64) 4144 ∗
        (memRegion outA v1RecvSize ∗ statesRecvSavedCells s0 ∗
          (msgA ↦₆₄ st.uc.epoch) ∗ memRegion (msgA + 9#64) 1 ∗ memRegion (msgA + 44#64) 4)) by
    rw [unchunkedCt1SentAt_epoch_expose A.repAlloc selfA st.uc,
        ← A.pool_transport lim st_cost s2 s3 hvm23]
    exact Entails.of_eq (by sep_ac_rfl)) ?_
  refine ct1Sampled_seq_vm_lscro hcro3
    (ct1Sampled_msg_kind_check_ekCt1Ack_placed s3 msgA _ hpc3 hrun3 hx24_3) ?_
  intro s4 hpc4 hrun4 hcro4 hvm34
    ⟨hsp4, hx1_4, hx19_4, hx20_4, hx21_4, hx22_4, hx23_4, hx24_4, hx28_4, hx29_4, htr4⟩
  have hP4' :
      ((msgA + 8#64) ↦₈ 3#8) ∗
        (polyEncoderAt A.repAlloc selfA st.sending_ct1 ∗
          unchunkedCt1SentAt A.repAlloc (selfA + 400#64) st.uc ∗
          polyDecoderAt A.repAlloc (selfA + 528#64) st.receiving_ek ∗
          chunkAt (msgA + 10#64) chunk ∗
          statesRecvRoPlacedAt ∗ A.pool lim st_cost s3 ∗
          stackAt (s0.sp - 4240#64) statesRecvCalleeStackX ∗
          memRegion (s0.sp - 4240#64) 4144 ∗
          (memRegion outA v1RecvSize ∗ statesRecvSavedCells s0 ∗
            (msgA ↦₆₄ st.uc.epoch) ∗ memRegion (msgA + 9#64) 1 ∗ memRegion (msgA + 44#64) 4)) ⊢
      polyEncoderAt A.repAlloc selfA st.sending_ct1 ∗
        unchunkedCt1SentAt A.repAlloc (selfA + 400#64) st.uc ∗
        polyDecoderAt A.repAlloc (selfA + 528#64) st.receiving_ek ∗
        chunkAt (msgA + 10#64) chunk ∗
        statesRecvRoPlacedAt ∗ A.pool lim st_cost s4 ∗
        stackAt (s0.sp - 4240#64) statesRecvCalleeStackX ∗
        memRegion (s0.sp - 4240#64) 4144 ∗
        (memRegion outA v1RecvSize ∗ statesRecvSavedCells s0 ∗
          ((msgA + 8#64) ↦₈ 3#8) ∗ (msgA ↦₆₄ st.uc.epoch) ∗
          memRegion (msgA + 9#64) 1 ∗ memRegion (msgA + 44#64) 4) := by
    rw [← A.pool_transport lim st_cost s3 s4 hvm34]
    exact Entails.of_eq (by sep_ac_rfl)
  refine SepWP.weaken_pre hP4' ?_
  apply SepWP.done hpc4 hrun4
  have hx29_fsp : s4.readReg64 .x29 = (s0.sp - 4240#64) + 4144#64 := by
    rw [hx29_4, hx29_3, hx29, sp_sub_4240_add_4144]
  refine ct1Sampled_recv_ek_common_prefix_sepWPp_placed
    hmemcpy hadd_call hdec_call st_cost s0 s4 (s0.sp - 4240#64) selfA outA msgA 1#64 st chunk
    hlen hsort hfits_add hfits_dec _
    hcro4 hfsp_align hpc4 hrun4 (hsp4.trans (hsp3.trans hsp2)) (hx1_4.trans hx1_3)
    (hx19_4.trans (hx19_3.trans hx19)) (hx20_4.trans hx20_3) (hx21_4.trans (hx21_3.trans hx21))
    hx22_4 (hx23_4.trans (hx12_3.trans hx12)) hx24_4 (hx28_4.trans (hx28_3.trans hx28))
    hx29_fsp (htr4.trans (htr3.trans htr2)) ?_
  intro s5 c_uc sc k evsAdd evsDec hpc5 hrun5 hsp5 hx19_5 hx20_5 hx21_5 hx22_5 hx23_5 _
    hx28_5 hx29_5 htr5 _hcro5 hcl5 hevsAdd hevsDec _hsort'
  have hmsg_join :
      chunkAt (msgA + 10#64) chunk ∗ ((msgA + 8#64) ↦₈ 3#8) ∗ (msgA ↦₆₄ st.uc.epoch) ∗
        memRegion (msgA + 9#64) 1 ∗ memRegion (msgA + 44#64) 4 =
      messageAt spqrPolyApi msgA msg := by
    rw [messageAt_ekCt1Ack_eq msgA msg chunk hpay, heq]; sep_ac_rfl
  have hdec_cases :
      decodedMessageTotal (addChunkTotal st.receiving_ek chunk) = none ∨
      ∃ decoded, decodedMessageTotal (addChunkTotal st.receiving_ek chunk) = some decoded := by
    cases decodedMessageTotal (addChunkTotal st.receiving_ek chunk) with
    | none => exact Or.inl rfl
    | some d => exact Or.inr ⟨d, rfl⟩
  rcases hdec_cases with hdec_opt | ⟨decoded, hdec_opt⟩
  · refine SepWPp.weaken_pre (Entails.of_eq (show _ =
      optVecU8At A.repAlloc ((s0.sp - 4240#64) + 3832#64) none ∗
        polyDecoderAt A.repAlloc ((s0.sp - 4240#64) + 2752#64)
          (addChunkTotal st.receiving_ek chunk) ∗
        polyEncoderAt A.repAlloc selfA st.sending_ct1 ∗ wordsAt (selfA + 400#64) c_uc.toList ∗
        wordsAt ((s0.sp - 4240#64) + 3696#64) c_uc.toList ∗
        relocatedHeap (fun a => unchunkedCt1SentAt A.repAlloc a st.uc) (wordsBytes c_uc.toList) ∗
        memRegion (selfA + 528#64) 400 ∗ copyScratchStackAt (s0.sp - 4240#64) sc ∗
        epilogueStoreStackPart1At (s0.sp - 4240#64) k ∗ (((s0.sp - 4240#64) + 232#64) ↦₆₄ selfA) ∗
        (((s0.sp - 4240#64) + 512#64) ↦₆₄ k.w200) ∗ (((s0.sp - 4240#64) + 520#64) ↦₆₄ k.w208) ∗
        wordsAt ((s0.sp - 4240#64) + 528#64) k.tail.toList ∗
        memRegion ((s0.sp - 4240#64) + 576#64) 376 ∗ memRegion ((s0.sp - 4240#64) + 568#64) 8 ∗
        memRegion ((s0.sp - 4240#64) + 952#64) 8 ∗ memRegion ((s0.sp - 4240#64) + 976#64) 1776 ∗
        memRegion ((s0.sp - 4240#64) + 3152#64) 544 ∗ memRegion ((s0.sp - 4240#64) + 3824#64) 8 ∗
        memRegion ((s0.sp - 4240#64) + 3856#64) 288 ∗ memRegion outA v1RecvSize ∗ statesRecvRoPlacedAt ∗
        A.pool lim (M.stepEvents (evsAdd ++ evsDec) st_cost) s5 ∗
        stackAt (s0.sp - 4240#64) statesRecvCalleeStackX ∗ statesRecvSavedCells s0 ∗
        (chunkAt (msgA + 10#64) chunk ∗ ((msgA + 8#64) ↦₈ 3#8) ∗ (msgA ↦₆₄ st.uc.epoch) ∗
          memRegion (msgA + 9#64) 1 ∗ memRegion (msgA + 44#64) 4) by
      rw [hdec_opt]; sep_ac_rfl)) ?_
    rw [hmsg_join]
    refine sepWPp_of_statesRecv_exit_placed_ofPrePostEnv
      (PreEnv := PreEnv) (PostEnv := fun _ => Ct1SampledRecvPostEnv K st msg)
      s0 s5 outA selfA msgA (.ct1Sampled st) msg st_cost _ R ?_
    rw [states_recv_ct1Sampled_eq_none_ack K st msg chunk heq hpay hlen hsort hdec_opt]
    refine SepWP.mono
      (ArmCt1SampledPart8PlacedBudget.ct1Sampled_path_none_ack_placed hdealloc hmemcpy
        (M.stepEvents (evsAdd ++ evsDec) st_cost) s0 s5 (s0.sp - 4240#64) selfA outA st
        (addChunkTotal st.receiving_ek chunk) c_uc sc k
        (messageAt spqrPolyApi msgA msg)
        hcl5 hfsp_align hsp0_align rfl hpc5 hrun5 hsp5 hx19_5 hx22_5 hx28_5 htr5) ?_
    intro sf Pf _ _ ⟨evsTail, hevsTail, hPf, hsp_f, hcs_f, htr_f⟩
    have hst_eq :
        M.stepEvents evsTail (M.stepEvents (evsAdd ++ evsDec) st_cost) =
          M.stepEvents ((evsAdd ++ evsDec) ++ evsTail) st_cost :=
      (M.stepEvents_append (evsAdd ++ evsDec) evsTail st_cost).symm
    exact ⟨⟨(evsAdd ++ evsDec) ++ evsTail,
      ct1SampledRecvPostEnv_ekCt1Ack_none K heq hpay hdec_opt hevsAdd hevsDec hevsTail,
      Entails.trans hPf (Entails.of_eq (by rw [hst_eq]; sep_ac_rfl))⟩,
      hsp_f, hcs_f, htr_f⟩
  · have hrek_eq := ct1Sent_recv_ek_eq_ofError K st.uc decoded
    dsimp only at hrek_eq
    split_ifs at hrek_eq with hpk
    · let uc_ek : Ct1SentEkReceived (spqrAuthApi F) :=
        { epoch := st.uc.epoch, auth := st.uc.auth, es := st.uc.es, ek := decoded, ct1 := st.uc.ct1 }
      have hrek : st.uc.recv_ek K st.uc.epoch decoded = .ok uc_ek := hrek_eq
      obtain ⟨outUc, ct2, mac, outEnc, hsc, henc⟩ := h_sendCt2 decoded uc_ek hdec_opt hrek
      refine SepWPp.weaken_pre (Entails.of_eq (show _ =
        optVecU8At A.repAlloc ((s0.sp - 4240#64) + 3832#64) (some decoded) ∗
          polyDecoderAt A.repAlloc ((s0.sp - 4240#64) + 2752#64)
            (addChunkTotal st.receiving_ek chunk) ∗
          polyEncoderAt A.repAlloc selfA st.sending_ct1 ∗ wordsAt (selfA + 400#64) c_uc.toList ∗
          wordsAt ((s0.sp - 4240#64) + 3696#64) c_uc.toList ∗
          relocatedHeap (fun a => unchunkedCt1SentAt A.repAlloc a st.uc) (wordsBytes c_uc.toList) ∗
          memRegion (selfA + 528#64) 400 ∗ copyScratchStackAt (s0.sp - 4240#64) sc ∗
          epilogueStoreStackPart1At (s0.sp - 4240#64) k ∗ (((s0.sp - 4240#64) + 232#64) ↦₆₄ selfA) ∗
          (((s0.sp - 4240#64) + 512#64) ↦₆₄ k.w200) ∗ (((s0.sp - 4240#64) + 520#64) ↦₆₄ k.w208) ∗
          wordsAt ((s0.sp - 4240#64) + 528#64) k.tail.toList ∗
          memRegion ((s0.sp - 4240#64) + 576#64) 376 ∗ memRegion ((s0.sp - 4240#64) + 568#64) 8 ∗
          memRegion ((s0.sp - 4240#64) + 952#64) 8 ∗ memRegion ((s0.sp - 4240#64) + 976#64) 1776 ∗
          memRegion ((s0.sp - 4240#64) + 3152#64) 544 ∗ memRegion ((s0.sp - 4240#64) + 3824#64) 8 ∗
          memRegion ((s0.sp - 4240#64) + 3856#64) 288 ∗ memRegion outA v1RecvSize ∗ statesRecvRoPlacedAt ∗
          A.pool lim (M.stepEvents (evsAdd ++ evsDec) st_cost) s5 ∗
          stackAt (s0.sp - 4240#64) statesRecvCalleeStackX ∗ statesRecvSavedCells s0 ∗
          (chunkAt (msgA + 10#64) chunk ∗ ((msgA + 8#64) ↦₈ 3#8) ∗ (msgA ↦₆₄ st.uc.epoch) ∗
            memRegion (msgA + 9#64) 1 ∗ memRegion (msgA + 44#64) 4) by
        rw [hdec_opt]; sep_ac_rfl)) ?_
      rw [hmsg_join]
      exact ArmCt1SampledPart10PlacedBudgetAux.ct1Sampled_path_some_ok_ack_placed
        (PreEnv := PreEnv) hdealloc hmemcpy hrecv_ek hsendCt2 hsendCt2Enc
        st_cost evsAdd evsDec s0 s5 (s0.sp - 4240#64) selfA outA msgA st msg chunk decoded uc_ek
        outUc ct2 mac outEnc c_uc sc k R hcl5 heq hpay hlen hsort hdec_opt hrek hsc henc
        hevsAdd hevsDec (hfits_tail evsAdd evsDec hevsAdd hevsDec)
        hfsp_align hsp0_align rfl hpc5 hrun5 hsp5 hx19_5 hx20_5 hx21_5 hx22_5 hx23_5 hx28_5 hx29_5
        htr5
    · have hrek : st.uc.recv_ek K st.uc.epoch decoded = .error (.err .erroneousDataReceived) := hrek_eq
      refine SepWPp.weaken_pre (Entails.of_eq (show _ =
        optVecU8At A.repAlloc ((s0.sp - 4240#64) + 3832#64) (some decoded) ∗
          polyDecoderAt A.repAlloc ((s0.sp - 4240#64) + 2752#64)
            (addChunkTotal st.receiving_ek chunk) ∗
          polyEncoderAt A.repAlloc selfA st.sending_ct1 ∗ wordsAt (selfA + 400#64) c_uc.toList ∗
          wordsAt ((s0.sp - 4240#64) + 3696#64) c_uc.toList ∗
          relocatedHeap (fun a => unchunkedCt1SentAt A.repAlloc a st.uc) (wordsBytes c_uc.toList) ∗
          memRegion (selfA + 528#64) 400 ∗ copyScratchStackAt (s0.sp - 4240#64) sc ∗
          epilogueStoreStackPart1At (s0.sp - 4240#64) k ∗ (((s0.sp - 4240#64) + 232#64) ↦₆₄ selfA) ∗
          (((s0.sp - 4240#64) + 512#64) ↦₆₄ k.w200) ∗ (((s0.sp - 4240#64) + 520#64) ↦₆₄ k.w208) ∗
          wordsAt ((s0.sp - 4240#64) + 528#64) k.tail.toList ∗
          memRegion ((s0.sp - 4240#64) + 576#64) 376 ∗ memRegion ((s0.sp - 4240#64) + 568#64) 8 ∗
          memRegion ((s0.sp - 4240#64) + 952#64) 8 ∗ memRegion ((s0.sp - 4240#64) + 976#64) 1776 ∗
          memRegion ((s0.sp - 4240#64) + 3152#64) 544 ∗ memRegion ((s0.sp - 4240#64) + 3824#64) 8 ∗
          memRegion ((s0.sp - 4240#64) + 3856#64) 288 ∗ memRegion outA v1RecvSize ∗
          A.pool lim (M.stepEvents (evsAdd ++ evsDec) st_cost) s5 ∗
          stackAt (s0.sp - 4240#64) statesRecvCalleeStackX ∗ statesRecvSavedCells s0 ∗
          (statesRecvRoPlacedAt ∗
            (chunkAt (msgA + 10#64) chunk ∗ ((msgA + 8#64) ↦₈ 3#8) ∗ (msgA ↦₆₄ st.uc.epoch) ∗
              memRegion (msgA + 9#64) 1 ∗ memRegion (msgA + 44#64) 4)) by
        rw [hdec_opt]; sep_ac_rfl)) ?_
      rw [hmsg_join]
      refine sepWPp_of_statesRecv_exit_placed_ofPrePostEnv
        (PreEnv := PreEnv) (PostEnv := fun _ => Ct1SampledRecvPostEnv K st msg)
        s0 s5 outA selfA msgA (.ct1Sampled st) msg st_cost _ R ?_
      rw [states_recv_ct1Sampled_eq_some_err K st msg chunk decoded .erroneousDataReceived
        heq (Or.inr hpay) hlen hsort hdec_opt hrek]
      refine SepWP.mono
        (ArmCt1SampledPart8PlacedBudget.ct1Sampled_path_some_err_placed hdealloc hrecv_ek
          (M.stepEvents (evsAdd ++ evsDec) st_cost) s0 s5 (s0.sp - 4240#64) selfA outA st
          (addChunkTotal st.receiving_ek chunk) c_uc decoded .erroneousDataReceived sc k
          (statesRecvRoPlacedAt ∗ messageAt spqrPolyApi msgA msg)
          hcl5 hrek rfl hfsp_align hsp0_align rfl hpc5 hrun5 hsp5 hx19_5 hx20_5 htr5) ?_
      intro sf Pf _ _ ⟨evsTail, hevsTail, hPf, hsp_f, hcs_f, htr_f⟩
      have hst_eq :
          M.stepEvents evsTail (M.stepEvents (evsAdd ++ evsDec) st_cost) =
            M.stepEvents ((evsAdd ++ evsDec) ++ evsTail) st_cost :=
        (M.stepEvents_append (evsAdd ++ evsDec) evsTail st_cost).symm
      exact ⟨⟨(evsAdd ++ evsDec) ++ evsTail,
        ct1SampledRecvPostEnv_ekCt1Ack_err K heq hpay hdec_opt hrek hevsAdd hevsDec hevsTail,
        Entails.trans hPf (Entails.of_eq (by rw [hst_eq]; sep_ac_rfl))⟩,
        hsp_f, hcs_f, htr_f⟩

/-! ## 3. Complete `.ct1Sampled` Arm (`+1528 -> s0.x30`) & Per-Variant `subroutine_ok` Contracts -/

set_option maxHeartbeats 2000000 in
/-- Complete budget-threaded `.ct1Sampled` arm from `+1528 -> s0.x30` for all `msg`. -/
theorem states_recv_arm_ct1Sampled_placed [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {F : ShaCompress} {K : MlKem}
    {PreEnv : StatesRecvGhost F → List AllocEvent → Prop}
    {ext : String → Option (State → State)}
    (hdealloc : HookSat (Rust.withPanics ext) spqrDeallocSym (rustCliDeallocBudgetSpec M A lim))
    (hmemcpy : HookSat (Rust.withPanics ext) spqrMemcpySym (withVmPreserved sessionMemcpySpec))
    (hadd_call : subroutine_ok (lsProg_332 (Rust.withPanics ext))
      (lsmpl.base 419) (withLsCodeLoaded lsmpl (addChunkSpecX M A lim)))
    (hdec_call : subroutine_ok (lsProg_332 (Rust.withPanics ext))
      (lsmpl.base 418) (withLsCodeRoLoaded lsmpl (polyDecoderDecodedMessagePlacedSpec M A lim)))
    (hrecv_ek : subroutine_ok (lsProg_332 (Rust.withPanics ext))
      (lsmpl.base 338) (withLsCodeLoaded lsmpl (unchunkedCt1SentRecvEkSpec M A lim F K)))
    (hsendCt2 : subroutine_ok (lsProg_332 (Rust.withPanics ext))
      (lsmpl.base 347)
      (withLsCodeLoaded lsmpl (unchunkedCt1SentEkReceivedSendCt2PlacedSpec M A lim F K)))
    (hsendCt2Enc : subroutine_ok (lsProg_332 (Rust.withPanics ext))
      (lsmpl.base 382) (withLsCodeLoaded lsmpl (sendCt2EncoderSpec M A lim)))
    (st_cost : M.σ) (s0 s2 : State) (outA selfA msgA : BitVec 64)
    (st : Ct1Sampled spqrPolyApi (spqrAuthApi F))
    (msg : Message spqrPolyApi) (R : SepProp)
    (hcro2 : LibsignalCodeRoLoaded lsmpl s2.mem)
    (hsort : PolyDecoderStrictSorted st.receiving_ek)
    (hfits : FitsEnv M lim st_cost (Ct1SampledRecvPreEnv K st msg))
    (h_sendCt2 : ∀ chunk decoded (uc_ek : Ct1SentEkReceived (spqrAuthApi F)),
      msg.epoch = st.uc.epoch → msg.payload = .ekCt1Ack chunk →
      decodedMessageTotal (addChunkTotal st.receiving_ek chunk) = some decoded →
      st.uc.recv_ek K st.uc.epoch decoded = .ok uc_ek →
      ∃ outUc ct2 mac outEnc,
        uc_ek.send_ct2 K = .ok (outUc, ct2, mac) ∧
        send_ct2_encoder spqrPolyApi ct2 mac = .ok outEnc)
    (hsp0_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hpc2 : s2.pc = (blkPl_332).base + 1528#64)
    (hrun2 : s2.status = .Running) (hsp2 : s2.sp = s0.sp - 4240#64)
    (hx1 : s2.readReg64 .x1 = selfA) (hx12 : s2.readReg64 .x12 = polyEncoderTagVal st.sending_ct1)
    (hx19 : s2.readReg64 .x19 = outA) (hx21 : s2.readReg64 .x21 = (s0.sp - 4240#64) + 3856#64)
    (hx24 : s2.readReg64 .x24 = msgA) (hx28 : s2.readReg64 .x28 = (s0.sp - 4240#64) + 3272#64)
    (hx29 : s2.readReg64 .x29 = s0.sp - 96#64) (htr2 : TraceCalleeSaved s2 s0)
    (_hlr_ls : LsRetAddr624 (s0.readReg64 .x30) := by
      first
      | assumption
      | simp (config := { decide := true }) only [Reg.x30, Reg.lr, arm64_norm, wp_norm]) :
    SepWPp (lsProg_332 (Rust.withPanics ext)) (s0.readReg64 .x30) s2
      (memRegion outA v1RecvSize ∗ chunkedStatesAt A.repAlloc selfA (.ct1Sampled st) ∗
        messageAt spqrPolyApi msgA msg ∗ statesRecvRoPlacedAt ∗ A.pool lim st_cost s2 ∗
        stackAt (s0.sp - 4240#64) statesRecvCalleeStackX ∗
        memRegion (s0.sp - 4240#64) 4144 ∗ statesRecvSavedCells s0)
      (fun sf P_f =>
        (sf.mem ⊨ P_f ∗ R →
          sf.mem ⊨
            (statesRecvVariantPlacedSpecOfPrePostEnv M A lim F K (.ct1Sampled st) msg
              PreEnv (fun _ => Ct1SampledRecvPostEnv K st msg)).post
              ((outA, selfA, msgA), st_cost) s0 sf ∗ R) ∧
        sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf)
      (fun sf P_f =>
        sf.mem ⊨ P_f ∗ R →
          sf.mem ⊨
            (statesRecvVariantPlacedSpecOfPrePostEnv M A lim F K (.ct1Sampled st) msg
              PreEnv (fun _ => Ct1SampledRecvPostEnv K st msg)).onPanic
              ((outA, selfA, msgA), st_cost) s0 sf ∗ R) := by
  have hfsp_align : ((s0.sp - 4240#64) &&& 15#64 == 0#64) = true :=
    spAligned_sub s0.sp 4240#64 hsp0_align (by decide)
  by_cases hgt : msg.epoch.toNat > st.uc.epoch.toNat
  · have hne : msg.epoch ≠ st.uc.epoch := by
      intro h; rw [h] at hgt; exact Nat.lt_irrefl _ hgt
    refine sepWPp_of_statesRecv_exit_placed_ofPrePostEnv
      (PreEnv := PreEnv) (PostEnv := fun _ => Ct1SampledRecvPostEnv K st msg)
      s0 s2 outA selfA msgA (.ct1Sampled st) msg st_cost _ R ?_
    rw [states_recv_ct1Sampled_eq_gt K st msg hgt]
    have hpre :
        memRegion outA v1RecvSize ∗ chunkedStatesAt A.repAlloc selfA (.ct1Sampled st) ∗
          messageAt spqrPolyApi msgA msg ∗ statesRecvRoPlacedAt ∗ A.pool lim st_cost s2 ∗
          stackAt (s0.sp - 4240#64) statesRecvCalleeStackX ∗
          memRegion (s0.sp - 4240#64) 4144 ∗ statesRecvSavedCells s0 ⊢
        ((selfA + 520#64) ↦₆₄ st.uc.epoch) ∗ (msgA ↦₆₄ msg.epoch) ∗
        (memRegion outA v1RecvSize ∗ polyEncoderAt A.repAlloc selfA st.sending_ct1 ∗
          (authenticatorAt A.repAlloc (selfA + 400#64) st.uc.auth ∗
            vecU8 A.repAlloc (selfA + 448#64) st.uc.hdr ∗
            vecU8 A.repAlloc (selfA + 472#64) st.uc.es ∗
            vecU8 A.repAlloc (selfA + 496#64) st.uc.ct1) ∗
          polyDecoderAt A.repAlloc (selfA + 528#64) st.receiving_ek ∗
          messagePayloadAt spqrPolyApi msgA msg.payload ∗ statesRecvRoPlacedAt ∗
          A.pool lim st_cost s2 ∗ stackAt (s0.sp - 4240#64) statesRecvCalleeStackX ∗
          memRegion (s0.sp - 4240#64) 4144 ∗ statesRecvSavedCells s0) := by
      dsimp only [chunkedStatesAt, chunkedCt1SampledAt, messageAt]
      rw [unchunkedCt1SentAt_epoch_expose A.repAlloc selfA st.uc]
      exact Entails.of_eq (by sep_ac_rfl)
    refine SepWP.weaken_pre hpre ?_
    refine ct1Sampled_seq_vm_lscl hcro2.1
      (ArmCt1SampledPart1PlacedBudget.ct1Sampled_epoch_cmp_gt_placed s2 selfA msgA st.uc.epoch msg.epoch _ hgt hpc2 hrun2 hx1 hx24) ?_
    intro s3 hpc3 hrun3 hcl3 hvm23 ⟨hsp3, hx1_3, hx19_3, hx20_3, _, _, _, _, htr3⟩
    have hP3' :
        ((selfA + 520#64) ↦₆₄ st.uc.epoch) ∗ (msgA ↦₆₄ msg.epoch) ∗
          (memRegion outA v1RecvSize ∗ polyEncoderAt A.repAlloc selfA st.sending_ct1 ∗
            (authenticatorAt A.repAlloc (selfA + 400#64) st.uc.auth ∗
              vecU8 A.repAlloc (selfA + 448#64) st.uc.hdr ∗
              vecU8 A.repAlloc (selfA + 472#64) st.uc.es ∗
              vecU8 A.repAlloc (selfA + 496#64) st.uc.ct1) ∗
            polyDecoderAt A.repAlloc (selfA + 528#64) st.receiving_ek ∗
            messagePayloadAt spqrPolyApi msgA msg.payload ∗ statesRecvRoPlacedAt ∗
            A.pool lim st_cost s2 ∗ stackAt (s0.sp - 4240#64) statesRecvCalleeStackX ∗
            memRegion (s0.sp - 4240#64) 4144 ∗ statesRecvSavedCells s0) ⊢
        memRegion outA v1RecvSize ∗ chunkedStatesAt A.repAlloc selfA (.ct1Sampled st) ∗
          A.pool lim st_cost s3 ∗ stackAt (s0.sp - 4240#64) statesRecvCalleeStackX ∗
          memRegion (s0.sp - 4240#64) 4144 ∗ statesRecvSavedCells s0 ∗
          (messageAt spqrPolyApi msgA msg ∗ statesRecvRoPlacedAt) := by
      dsimp only [chunkedStatesAt, chunkedCt1SampledAt, messageAt]
      rw [unchunkedCt1SentAt_epoch_expose A.repAlloc selfA st.uc,
          ← A.pool_transport lim st_cost s2 s3 hvm23]
      exact Entails.of_eq (by sep_ac_rfl)
    refine SepWP.weaken_pre hP3' ?_
    refine SepWP.mono
      (ArmCt1SampledPart1PlacedBudget.ct1Sampled_drop_epochOutOfRange_placed hdealloc st_cost s0 s3 outA selfA msg.epoch st
        (messageAt spqrPolyApi msgA msg ∗ statesRecvRoPlacedAt)
        hcl3 hsp0_align hpc3 hrun3 (hsp3.trans hsp2) hx1_3 (hx19_3.trans hx19) hx20_3
        (htr3.trans htr2)) ?_
    intro sf Pf _ _ ⟨evs, hevs, hPf, hsp_f, _hacp, hcs_f, htr_f⟩
    exact ⟨⟨evs, ct1SampledRecvPostEnv_of_freeOnly_ne K hne hevs,
      Entails.trans hPf (Entails.of_eq (by sep_ac_rfl))⟩, hsp_f, hcs_f, htr_f⟩
  · by_cases hlt : msg.epoch.toNat < st.uc.epoch.toNat
    · have hne : msg.epoch ≠ st.uc.epoch := by
        intro h; rw [h] at hlt; exact Nat.lt_irrefl _ hlt
      refine sepWPp_of_statesRecv_exit_evs_placed_ofPrePostEnv
        (PreEnv := PreEnv) (PostEnv := fun _ => Ct1SampledRecvPostEnv K st msg)
        s0 s2 outA selfA msgA (.ct1Sampled st) msg st_cost []
        (ct1SampledRecvPostEnv_of_freeOnly_ne K hne FreeOnlyEvs.nil) _ R ?_
      rw [states_recv_ct1Sampled_eq_lt K st msg hlt, M.stepEvents_nil]
      have hpre :
          memRegion outA v1RecvSize ∗ chunkedStatesAt A.repAlloc selfA (.ct1Sampled st) ∗
            messageAt spqrPolyApi msgA msg ∗ statesRecvRoPlacedAt ∗ A.pool lim st_cost s2 ∗
            stackAt (s0.sp - 4240#64) statesRecvCalleeStackX ∗
            memRegion (s0.sp - 4240#64) 4144 ∗ statesRecvSavedCells s0 ⊢
          ((selfA + 520#64) ↦₆₄ st.uc.epoch) ∗ (msgA ↦₆₄ msg.epoch) ∗
          (memRegion outA v1RecvSize ∗ polyEncoderAt A.repAlloc selfA st.sending_ct1 ∗
            (authenticatorAt A.repAlloc (selfA + 400#64) st.uc.auth ∗
              vecU8 A.repAlloc (selfA + 448#64) st.uc.hdr ∗
              vecU8 A.repAlloc (selfA + 472#64) st.uc.es ∗
              vecU8 A.repAlloc (selfA + 496#64) st.uc.ct1) ∗
            polyDecoderAt A.repAlloc (selfA + 528#64) st.receiving_ek ∗
            messagePayloadAt spqrPolyApi msgA msg.payload ∗ statesRecvRoPlacedAt ∗
            A.pool lim st_cost s2 ∗ stackAt (s0.sp - 4240#64) statesRecvCalleeStackX ∗
            memRegion (s0.sp - 4240#64) 4144 ∗ statesRecvSavedCells s0) := by
        dsimp only [chunkedStatesAt, chunkedCt1SampledAt, messageAt]
        rw [unchunkedCt1SentAt_epoch_expose A.repAlloc selfA st.uc]
        exact Entails.of_eq (by sep_ac_rfl)
      refine SepWP.weaken_pre hpre ?_
      refine SepWP.seq
        (ArmCt1SampledPart1PlacedBudget.ct1Sampled_epoch_cmp_lt_placed s2 selfA msgA st.uc.epoch msg.epoch _ hlt hpc2 hrun2 hx1 hx24) ?_
      intro s3 P3 hpc3 hrun3
        ⟨hvm23, hP3, hsp3, _, hx1_3, _, _, hx12_3, hx19_3, _, _, _, _, hx29_3, htr3⟩
      have hP3' : P3 ⊢
          ((selfA ↦₆₄ polyEncoderTagVal st.sending_ct1) ∗
            chunkedCt1SampledBodyAt A.repAlloc (selfA + 8#64) st) ∗
          memRegion outA v1RecvSize ∗ memRegion (s0.sp - 4240#64) 4144 ∗
          stackAt (s0.sp - 4240#64) statesRecvCalleeStackX ∗ statesRecvSavedCells s0 ∗
          A.pool lim st_cost s3 ∗
          (messageAt spqrPolyApi msgA msg ∗ statesRecvRoPlacedAt) := by
        refine Entails.trans hP3 ?_
        rw [← chunkedCt1SampledAt_eq_tag_body A.repAlloc selfA st]
        dsimp only [chunkedCt1SampledAt, messageAt]
        rw [unchunkedCt1SentAt_epoch_expose A.repAlloc selfA st.uc,
            ← A.pool_transport lim st_cost s2 s3 hvm23]
        exact Entails.of_eq (by sep_ac_rfl)
      refine SepWP.weaken_pre hP3' ?_
      refine SepWP.mono
        (ct1Sampled_path_lt_pool_placed hmemcpy st_cost s0 s3 (s0.sp - 4240#64) selfA outA st
          (messageAt spqrPolyApi msgA msg ∗ statesRecvRoPlacedAt)
          hfsp_align hsp0_align rfl hpc3 hrun3 (hsp3.trans hsp2)
          hx1_3 (hx12_3.trans hx12) (hx19_3.trans hx19) (hx29_3.trans hx29) (htr3.trans htr2)) ?_
      intro sf Pf _ _ ⟨_, hPf, hsp_f, hcs_f, htr_f⟩
      exact ⟨Entails.trans hPf (Entails.of_eq (by sep_ac_rfl)), hsp_f, hcs_f, htr_f⟩
    · have heq : msg.epoch = st.uc.epoch := by apply BitVec.eq_of_toNat_eq; omega
      cases hpay : msg.payload with
      | ek chunk =>
        exact ct1Sampled_arm_eq_ek_placed hdealloc hmemcpy hadd_call hdec_call hrecv_ek
          st_cost s0 s2 outA selfA msgA st msg chunk R hcro2 hsort hfits heq hpay
          hsp0_align hpc2 hrun2 hsp2 hx1 hx12 hx19 hx21 hx24 hx28 hx29 htr2
      | ekCt1Ack chunk =>
        exact ct1Sampled_arm_eq_ekCt1Ack_placed
          hdealloc hmemcpy hadd_call hdec_call hrecv_ek hsendCt2 hsendCt2Enc
          st_cost s0 s2 outA selfA msgA st msg chunk R hcro2 hsort hfits
          (fun decoded uc_ek hdec hrek => h_sendCt2 chunk decoded uc_ek heq hpay hdec hrek)
          heq hpay hsp0_align hpc2 hrun2 hsp2 hx1 hx12 hx19 hx21 hx24 hx28 hx29 htr2
      | none | hdr _ | ct1Ack _ | ct1 _ | ct2 _ =>
        have hnot_ek : ∀ c, msg.payload ≠ .ek c := by intro c hc; rw [hpay] at hc; cases hc
        have hnot_ack : ∀ c, msg.payload ≠ .ekCt1Ack c := by intro c hc; rw [hpay] at hc; cases hc
        obtain ⟨msg_tag, Rest_msg, hne2, hne3, hmsg_pay⟩ :=
          messagePayloadAt_other_expose msgA msg.payload hnot_ek hnot_ack
        refine sepWPp_of_statesRecv_exit_evs_placed_ofPrePostEnv
          (PreEnv := PreEnv) (PostEnv := fun _ => Ct1SampledRecvPostEnv K st msg)
          s0 s2 outA selfA msgA (.ct1Sampled st) msg st_cost []
          (ct1SampledRecvPostEnv_nil_other K heq hnot_ek hnot_ack) _ R ?_
        rw [states_recv_ct1Sampled_eq_other K st msg heq hnot_ek hnot_ack, M.stepEvents_nil]
        have hpre :
            memRegion outA v1RecvSize ∗ chunkedStatesAt A.repAlloc selfA (.ct1Sampled st) ∗
              messageAt spqrPolyApi msgA msg ∗ statesRecvRoPlacedAt ∗ A.pool lim st_cost s2 ∗
              stackAt (s0.sp - 4240#64) statesRecvCalleeStackX ∗
              memRegion (s0.sp - 4240#64) 4144 ∗ statesRecvSavedCells s0 ⊢
            ((selfA + 520#64) ↦₆₄ st.uc.epoch) ∗ (msgA ↦₆₄ st.uc.epoch) ∗
            (((msgA + 8#64) ↦₈ msg_tag) ∗ Rest_msg ∗ memRegion outA v1RecvSize ∗
              polyEncoderAt A.repAlloc selfA st.sending_ct1 ∗
              (authenticatorAt A.repAlloc (selfA + 400#64) st.uc.auth ∗
                vecU8 A.repAlloc (selfA + 448#64) st.uc.hdr ∗
                vecU8 A.repAlloc (selfA + 472#64) st.uc.es ∗
                vecU8 A.repAlloc (selfA + 496#64) st.uc.ct1) ∗
              polyDecoderAt A.repAlloc (selfA + 528#64) st.receiving_ek ∗
              statesRecvRoPlacedAt ∗ A.pool lim st_cost s2 ∗
              stackAt (s0.sp - 4240#64) statesRecvCalleeStackX ∗
              memRegion (s0.sp - 4240#64) 4144 ∗ statesRecvSavedCells s0) := by
          dsimp only [chunkedStatesAt, chunkedCt1SampledAt, messageAt]
          rw [unchunkedCt1SentAt_epoch_expose A.repAlloc selfA st.uc, hmsg_pay, heq]
          exact Entails.of_eq (by sep_ac_rfl)
        refine SepWP.weaken_pre hpre ?_
        refine SepWP.seq
          (ArmCt1SampledPart1PlacedBudget.ct1Sampled_epoch_cmp_eq_placed s2 selfA msgA st.uc.epoch _ hpc2 hrun2 hx1 hx24) ?_
        intro s3 P3 hpc3 hrun3
          ⟨hvm23, hP3, hsp3, _, hx1_3, _, _, hx12_3, hx19_3, _, _, hx24_3, _, hx29_3, htr3⟩
        have hP3' : P3 ⊢
            ((msgA + 8#64) ↦₈ msg_tag) ∗
            ((selfA + 520#64) ↦₆₄ st.uc.epoch) ∗ (msgA ↦₆₄ st.uc.epoch) ∗ Rest_msg ∗
            memRegion outA v1RecvSize ∗ polyEncoderAt A.repAlloc selfA st.sending_ct1 ∗
            (authenticatorAt A.repAlloc (selfA + 400#64) st.uc.auth ∗
              vecU8 A.repAlloc (selfA + 448#64) st.uc.hdr ∗
              vecU8 A.repAlloc (selfA + 472#64) st.uc.es ∗
              vecU8 A.repAlloc (selfA + 496#64) st.uc.ct1) ∗
            polyDecoderAt A.repAlloc (selfA + 528#64) st.receiving_ek ∗
            statesRecvRoPlacedAt ∗ A.pool lim st_cost s3 ∗
            stackAt (s0.sp - 4240#64) statesRecvCalleeStackX ∗
            memRegion (s0.sp - 4240#64) 4144 ∗ statesRecvSavedCells s0 := by
          refine Entails.trans hP3 ?_
          rw [← A.pool_transport lim st_cost s2 s3 hvm23]
          exact Entails.of_eq (by sep_ac_rfl)
        refine SepWP.weaken_pre hP3' ?_
        refine SepWP.seq
          (ct1Sampled_msg_kind_check_other_placed s3 msgA msg_tag _ hne2 hne3 hpc3 hrun3 hx24_3) ?_
        intro s4 P4 hpc4 hrun4 ⟨hvm34, hP4, hsp4, hx1_4, hx12_4, hx19_4, hx29_4, htr4⟩
        have hP4' : P4 ⊢
            ((selfA ↦₆₄ polyEncoderTagVal st.sending_ct1) ∗
              chunkedCt1SampledBodyAt A.repAlloc (selfA + 8#64) st) ∗
            memRegion outA v1RecvSize ∗ memRegion (s0.sp - 4240#64) 4144 ∗
            stackAt (s0.sp - 4240#64) statesRecvCalleeStackX ∗ statesRecvSavedCells s0 ∗
            A.pool lim st_cost s4 ∗
            (messageAt spqrPolyApi msgA msg ∗ statesRecvRoPlacedAt) := by
          refine Entails.trans hP4 ?_
          rw [← chunkedCt1SampledAt_eq_tag_body A.repAlloc selfA st]
          dsimp only [chunkedCt1SampledAt, messageAt]
          rw [unchunkedCt1SentAt_epoch_expose A.repAlloc selfA st.uc, hmsg_pay, heq,
              ← A.pool_transport lim st_cost s3 s4 hvm34]
          exact Entails.of_eq (by sep_ac_rfl)
        refine SepWP.weaken_pre hP4' ?_
        refine SepWP.mono
          (ct1Sampled_path_other_from_12144_pool_placed hmemcpy st_cost s0 s4 (s0.sp - 4240#64)
            selfA outA st (messageAt spqrPolyApi msgA msg ∗ statesRecvRoPlacedAt)
            hfsp_align hsp0_align rfl hpc4 hrun4 (hsp4.trans (hsp3.trans hsp2))
            (hx1_4.trans hx1_3) (hx12_4.trans (hx12_3.trans hx12))
            (hx19_4.trans (hx19_3.trans hx19)) (hx29_4.trans (hx29_3.trans hx29))
            (htr4.trans (htr3.trans htr2))) ?_
        intro sf Pf _ _ ⟨_, hPf, hsp_f, hcs_f, htr_f⟩
        exact ⟨Entails.trans hPf (Entails.of_eq (by sep_ac_rfl)), hsp_f, hcs_f, htr_f⟩

/-- Two-envelope (`Ct1SampledRecvPreEnv` / `Ct1SampledRecvPostEnv`) relocatable per-variant
    specification proof for `States.ct1Sampled st` (`tag = 0#64 ∨ tag = 1#64`). -/
theorem states_recv_ct1Sampled_placed_ok_ext_ofPrePostEnv [LibsignalPlacement]
    (M : AllocCostModel) (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (F : ShaCompress) (K : MlKem)
    (ext : String → Option (State → State))
    (hC : DefsPlacedBudget.StatesRecvPlacedContracts M A lim F K ext)
    (st : Ct1Sampled spqrPolyApi (spqrAuthApi F))
    (msg : Message spqrPolyApi) :
    subroutine_ok (lsProg_332 (Rust.withPanics ext))
      (lsmpl.base 332)
      (withLsCodeRoLoaded lsmpl
        (statesRecvVariantPlacedSpecOfPrePostEnv M A lim F K (.ct1Sampled st) msg
          (fun _ => Ct1SampledRecvPreEnv K st msg)
          (fun _ => Ct1SampledRecvPostEnv K st msg))) := by
  apply subroutine_ok_of_sepWPp
  intro ⟨⟨outA, selfA, msgA⟩, st_cost⟩ R s0 hpc0 hrun0 hpre hsp0_align
  obtain ⟨hcro0, hpre⟩ := extract_withLsCodeRoLoaded hpre
  simp only [statesRecvVariantPlacedSpecOfPrePostEnv, sepConj_assoc, satisfies_pure_sepConj] at hpre
  rcases hpre with ⟨⟨hx0, hx1, hx2, ⟨hsort, hes, hct1, hmac⟩, hfits, hlr_ls⟩, hmem⟩
  have _hlr_x30 : LsRetAddr624 (s0.readReg64 .x30) := hlr_ls
  refine ⟨stackAt s0.sp statesRecvStackX ∗ A.pool lim st_cost s0 ∗
      (memRegion outA v1RecvSize ∗
        chunkedStatesAt A.repAlloc selfA (.ct1Sampled st) ∗
        messageAt spqrPolyApi msgA msg ∗ statesRecvRoPlacedAt),
    R, Satisfies.mono (Entails.of_eq (by sep_ac_rfl)) hmem, ?_⟩
  have hpro := ct1Sampled_prologue_pool_placed (M := M) (A := A) (lim := lim) (ext := ext)
    st_cost s0
    (memRegion outA v1RecvSize ∗ chunkedStatesAt A.repAlloc selfA (.ct1Sampled st) ∗
      messageAt spqrPolyApi msgA msg ∗ statesRecvRoPlacedAt)
    hsp0_align hpc0 hrun0
  refine ct1Sampled_sepWPp_seq_vm_lscro hcro0 hpro ?_
  intro s1 hpc1 hrun1 hcro1 _hvm01 ⟨_hacp01, hsp1, hx0_1, hx1_1, hx2_1, _, hx29_1, htr1⟩
  rw [hx0] at hx0_1; rw [hx1] at hx1_1; rw [hx2] at hx2_1
  have hP1' :
      stackAt (s0.sp - 4240#64) statesRecvCalleeStackX ∗ memRegion (s0.sp - 4240#64) 4144 ∗
        statesRecvSavedCells s0 ∗ A.pool lim st_cost s1 ∗
        (memRegion outA v1RecvSize ∗ chunkedStatesAt A.repAlloc selfA (.ct1Sampled st) ∗
          messageAt spqrPolyApi msgA msg ∗ statesRecvRoPlacedAt) ⊢
      (selfA ↦₆₄ polyEncoderTagVal st.sending_ct1) ∗ statesRecvRoPlacedAt ∗
        A.pool lim st_cost s1 ∗
        (chunkedCt1SampledBodyAt A.repAlloc (selfA + 8#64) st ∗
          memRegion outA v1RecvSize ∗ messageAt spqrPolyApi msgA msg ∗
          stackAt (s0.sp - 4240#64) statesRecvCalleeStackX ∗ memRegion (s0.sp - 4240#64) 4144 ∗
          statesRecvSavedCells s0) := by
    dsimp only [chunkedStatesAt]
    rw [chunkedCt1SampledAt_eq_tag_body A.repAlloc selfA st]
    exact Entails.of_eq (by sep_ac_rfl)
  refine SepWPp.weaken_pre hP1' ?_
  have hdisp := ct1Sampled_dispatch_pool_placed (M := M) (A := A) (lim := lim) (ext := ext)
    st_cost s1 (s0.sp - 4240#64) selfA (polyEncoderTagVal st.sending_ct1)
    (chunkedCt1SampledBodyAt A.repAlloc (selfA + 8#64) st ∗
      memRegion outA v1RecvSize ∗ messageAt spqrPolyApi msgA msg ∗
      stackAt (s0.sp - 4240#64) statesRecvCalleeStackX ∗ memRegion (s0.sp - 4240#64) 4144 ∗
      statesRecvSavedCells s0)
    (polyEncoderTagVal_zero_or_one st.sending_ct1) hpc1 hrun1 hsp1 hx1_1
  refine ct1Sampled_sepWPp_seq_vm_lscro hcro1 hdisp ?_
  intro s2 hpc2 hrun2 hcro2 _hvm12
    ⟨hsp2, _, hx1_2, _, _, _, hx12_2, hx19_2, hx21_2, hx24_2, hx28_2, hx29_2, htr2⟩
  rw [hx0_1] at hx19_2; rw [hx2_1] at hx24_2; rw [hx29_1] at hx29_2
  rw [lsmpl_base_332_eq] at hpc2
  have hP2' :
      (selfA ↦₆₄ polyEncoderTagVal st.sending_ct1) ∗ statesRecvRoPlacedAt ∗
        A.pool lim st_cost s2 ∗
        (chunkedCt1SampledBodyAt A.repAlloc (selfA + 8#64) st ∗
          memRegion outA v1RecvSize ∗ messageAt spqrPolyApi msgA msg ∗
          stackAt (s0.sp - 4240#64) statesRecvCalleeStackX ∗ memRegion (s0.sp - 4240#64) 4144 ∗
          statesRecvSavedCells s0) ⊢
      memRegion outA v1RecvSize ∗ chunkedStatesAt A.repAlloc selfA (.ct1Sampled st) ∗
        messageAt spqrPolyApi msgA msg ∗ statesRecvRoPlacedAt ∗ A.pool lim st_cost s2 ∗
        stackAt (s0.sp - 4240#64) statesRecvCalleeStackX ∗
        memRegion (s0.sp - 4240#64) 4144 ∗ statesRecvSavedCells s0 := by
    dsimp only [chunkedStatesAt]
    rw [chunkedCt1SampledAt_eq_tag_body A.repAlloc selfA st]
    exact Entails.of_eq (by sep_ac_rfl)
  refine SepWPp.weaken_pre hP2' ?_
  dsimp only [withLsCodeRoLoaded]
  exact states_recv_arm_ct1Sampled_placed (PreEnv := fun _ => Ct1SampledRecvPreEnv K st msg)
    hC.hdealloc_sat hC.hmemcpy_sat
    hC.polyAddChunk_ok hC.polyDecodedMessage_ok hC.unchunkedCt1SentRecvEk_ok
    hC.unchunkedCt1SentEkReceivedSendCt2_ok hC.sendCt2Encoder_ok
    st_cost s0 s2 outA selfA msgA st msg R hcro2 hsort hfits
    (fun _ decoded uc_ek _ _ _ hrek =>
      ct1Sampled_send_ct2_ok_of_recv_ek_ok K st decoded uc_ek hes hct1 hmac hrek)
    hsp0_align hpc2 hrun2 hsp2
    hx1_2 hx12_2 hx19_2 hx21_2 hx24_2 hx28_2 hx29_2 (htr2.trans htr1)

/-- Monotonic envelope weakening of `states_recv_ct1Sampled_placed_ok_ext_ofPrePostEnv` to any
    caller-chosen `(PreEnv, PostEnv)` pair. -/
theorem states_recv_ct1Sampled_placed_ok_ext_weaken [LibsignalPlacement]
    (M : AllocCostModel) (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (F : ShaCompress) (K : MlKem)
    {PreEnv PostEnv : StatesRecvGhost F → List AllocEvent → Prop}
    (ext : String → Option (State → State))
    (hC : DefsPlacedBudget.StatesRecvPlacedContracts M A lim F K ext)
    (st : Ct1Sampled spqrPolyApi (spqrAuthApi F))
    (msg : Message spqrPolyApi)
    (hPre : ∀ outA selfA msgA st_cost,
      FitsEnv M lim st_cost (PreEnv ⟨outA, selfA, msgA, .ct1Sampled st, msg⟩) →
      FitsEnv M lim st_cost (Ct1SampledRecvPreEnv K st msg))
    (hPost : ∀ outA selfA msgA evs,
      Ct1SampledRecvPostEnv K st msg evs →
      PostEnv ⟨outA, selfA, msgA, .ct1Sampled st, msg⟩ evs) :
    subroutine_ok (lsProg_332 (Rust.withPanics ext))
      (lsmpl.base 332)
      (withLsCodeRoLoaded lsmpl
        (statesRecvVariantPlacedSpecOfPrePostEnv M A lim F K (.ct1Sampled st) msg PreEnv PostEnv)) :=
  subroutine_ok_statesRecvVariantPlacedSpecOfPrePostEnv_weaken hPre hPost
    (states_recv_ct1Sampled_placed_ok_ext_ofPrePostEnv M A lim F K ext hC st msg)

/-- Single-envelope (`Ct1SampledRecvEnv`) relocatable per-variant specification proof for
    `States.ct1Sampled st` (`tag = 0#64 ∨ tag = 1#64`). -/
theorem states_recv_ct1Sampled_placed_ok_ext [LibsignalPlacement]
    (M : AllocCostModel) (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (F : ShaCompress) (K : MlKem)
    (ext : String → Option (State → State))
    (hC : DefsPlacedBudget.StatesRecvPlacedContracts M A lim F K ext)
    (st : Ct1Sampled spqrPolyApi (spqrAuthApi F))
    (msg : Message spqrPolyApi) :
    subroutine_ok (lsProg_332 (Rust.withPanics ext))
      (lsmpl.base 332)
      (withLsCodeRoLoaded lsmpl
        (statesRecvVariantPlacedSpecOfEnv M A lim F K (.ct1Sampled st) msg
          (fun _ => Ct1SampledRecvEnv K st msg))) :=
  states_recv_ct1Sampled_placed_ok_ext_weaken M A lim F K ext hC st msg
    (fun _ _ _ _ hfits => FitsEnv.mono (fun _ h => ct1SampledRecvPostEnv_of_pre h) hfits)
    (fun _ _ _ _ hpost => hpost)

end LibsignalBinary.Proofs.SpqrV1.States.Recv.ArmCt1SampledPart10PlacedBudget
