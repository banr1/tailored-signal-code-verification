/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Heap.IfaceBudgetLemmas
public import LibsignalBinary.Proofs.Placed.BudgetVmSteps
public meta import LibsignalBinary.Proofs.Placed.BudgetVmSteps -- shake: keep
public import LibsignalBinary.Proofs.SpqrV1.Drop.ProtoChunked2BudgetAux
public import LibsignalBinary.Proofs.SpqrV1.Drop.ProtoChunkedClPlacedBudget
public import LibsignalBinary.Proofs.SpqrV1.Drop.ProtoTop2BudgetAux
public import LibsignalBinary.Proofs.SpqrV1.Drop.ProtoTopClPlacedBudgetAux1
public import LibsignalBinary.Proofs.SpqrV1.States.Recv.DropChunkedClPlacedBudget
import LibsignalBinary.Proofs.Common.SharedHelpers
meta import LibsignalBinary.Proofs.Common.SharedHelpers -- shake: keep
import LibsignalBinary.Proofs.Placed.ElfLsRetAddr
import LibsignalBinary.Proofs.SpqrV1.Alloc.SpqrAllocCodeSym
import ProofLib.SepLogic.WP.Apply
import ProofLib.SepLogic.WPp
import GeneratedLean.LibsignalSessionObj

/-!
# Budget-Threaded Code-Loaded Loop Variants and Full Contract for `Option<InnerState>` (Block `267`)

Proves `ct1Acknowledged_cl`, `ct1Sampled_cl`, and the top-level `withLsCodeLoaded lsmpl` contract
`drop_opt_proto_inner_state_cl_placed_ok` for Block `267` under `RustCliAllocBudget M`.
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 400000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false

open CryptoVerification (
  IsLsBlockProg LibsignalCodeLoaded LibsignalPlacement blkPC_267 blkPC_270 blkPl_267 blkPl_270
  libsignalSessionLib lsProg_267 lsProg_270 ls_blockPlacement_base ls_subroutine_ok_of_block
  lscall_blk_cl lsmpl lsρ sepWP_seq_lscl subroutine_ok_withLsCodeLoaded_of_plain
  withLsCodeLoaded withMemEq
)
open CryptoVerification.LibsignalSpqrV1 (
  PqRatchetState V1State pbToProtoPolyDecoder pbToProtoPolyEncoder
)
open CryptoVerification.LibsignalTripleRatchetRepr (
  noneCap
)
open CryptoVerification.RustHeap (
  allocHookStack arrayAt vecU8
)
open CryptoVerification.SpqrV1.Alloc (
  spqr_hook_ok_of_mem
)
open CryptoVerification.SpqrV1.Drop (
  Saved48Preserved add_24_add_8 cap_add_one_beq_zero_false cap_add_three_beq_zero_false
  cap_add_two_beq_zero_false cap_lsl7_sub_lsl4 cap_mul_24 cap_ne_zero_lt_one_false
  cap_ne_zero_slt_one_false cap_xor_highBit_cc_11_false chainPBAt_entails_dealloc
  chainPBHeaders_entails_memRegion_80 cons_len_mul ct1SentToCt1SentEkReceived dropStack32
  dropStack48 dropStack96 header_cells_entails_memRegion_24 none2Cap_add_two_beq_zero none3Cap'
  noneCap_add_two_beq_zero ofNat_add_one_beq_one_false_24 ofNat_beq_zero_false_24
  ofNat_succ_eq_add_one optChainPBAt_none_entails_memRegion_80 optProtoInnerStateAt
  optProtoInnerStateAt_expose_word optProtoInnerStateAt_unexpose_word
  optProtoInnerStateJumpTableBytes optProtoInnerStateJumpTablePlacedAt
  optProtoInnerStateJumpTablePlacedExpanded optProtoInnerStateJumpTableSym
  optProtoInnerStateSize optProtoInnerStateTaggedRest
  optProtoPolyDecoder_none_entails_memRegion_40 optProtoPolyEncoder_none_entails_memRegion_56
  optProtoPolynomialDecoderAt_none' optProtoPolynomialDecoderAt_some'
  optProtoPolynomialEncoderAt_none' optProtoPolynomialEncoderAt_some' optProtoPqRatchetInnerAt
  optProtoPqRatchetInnerAt_none_entails_memRegion_224 optProtoUnchunkedCt1SentAt_none
  optProtoUnchunkedCt1SentAt_some
  optProtoUnchunkedCt1SentEkReceivedAt_none_entails_memRegion_128
  optVersionNegotiationPBAt_none_entails_memRegion_48 protoChunkedCt1AcknowledgedAt
  protoChunkedCt1SampledAt protoInnerStateAt protoPolyDecoderAt_entails_dealloc
  protoPolyDecoderHeaders_entails_memRegion_40 protoPolynomialEncoderAt_expose_cap
  protoPolynomialEncoderAt_unexpose_cap protoPqRatchetStateAt protoPqRatchetStateSize
  protoUnchunkedCt1SentAt_eq_ct1SentEkReceived protoUnchunkedCt1SentEkReceivedAt
  protoUnchunkedCt1SentEkReceivedAt_expose_cap protoUnchunkedCt1SentEkReceivedAt_unexpose_cap
  protoUnchunkedCt1SentEkReceivedSize sep_pull_body sep_push_body sep_rejoin_loop
  stackAt_dropStack96_split stackAt_dropStack96_split_bottom stackAt_sub48_eq_dropStack48
  stackAt_sub48_split_32 stack_restore_96_allocHook tag_and_two_regions_entails_224
  tail_len_mul_lt vecCapPtrDealloc vecU8_entails_capPtr_dealloc
  versionNegotiationPBAt_entails_dealloc vnHeader_entails_memRegion_48
)
open CryptoVerification.SpqrV1.Poly (
  optProtoPolynomialDecoderAt optProtoPolynomialEncoderAt protoPolynomialEncoderAt
  protoPolynomialEncoderSize
)
open CryptoVerification.SpqrV1.ProtoRepr (
  chainEpochPBAt chainEpochPBSize optChainPBAt optVersionNegotiationPBAt
)
open CryptoVerification.SpqrV1.States.Recv (
  spqrRustDeallocSym
)
open LibsignalBinary.Heap (
  AllocCallPreserved AllocCostModel AllocEvent BudgetLimits FreeOnlyEvs RustCliAllocBudget
  VmPreserved rustCliDeallocBudgetSpec rustDeallocEvents
)
open LibsignalBinary.Proofs.Placed.ElfLsRetAddr (LsRetAddr624)
open LibsignalBinary.Proofs.SpqrV1.Drop.ProtoChunked2BudgetAux (
  align_pre_st align_pre_vm deallocFreeOnlySpec sepWP_evs_dealloc sepWP_evs_nil seq_clean_evs
  seq_vm_clean subroutine_ok_deallocFreeOnly
)
open LibsignalBinary.Proofs.SpqrV1.Drop.ProtoChunkedClPlacedBudget (
  drop_proto_unchunked_ct1_sent_ek_received_mem_on
)
open LibsignalBinary.Proofs.SpqrV1.Drop.ProtoChunkedClPlacedBudgetAux (
  seq_clean_evs_lscl
)
open LibsignalBinary.Proofs.SpqrV1.Drop.ProtoTop2BudgetAux (
  drop_opt_proto_inner_state_loop_192_placed drop_opt_proto_inner_state_loop_408_placed
  sepWP_close_drop sepWP_evs_inst sepWP_sync_pool
)
open LibsignalBinary.Proofs.SpqrV1.Drop.ProtoTopBudget (
  dropOptProtoInnerStatePlacedSpec dropOptProtoInnerStatePlacedVariantSpec
  dropProtoPqRatchetStatePlacedSpec drop_opt_proto_inner_state_ct1Received_placed
  drop_opt_proto_inner_state_ct2Sampled_placed
  drop_opt_proto_inner_state_ekReceivedCt1Sampled_placed
  drop_opt_proto_inner_state_ekSentCt1Received_placed
  drop_opt_proto_inner_state_headerReceived_placed drop_opt_proto_inner_state_headerSent_placed
  drop_opt_proto_inner_state_keysSampled_placed drop_opt_proto_inner_state_keysUnsampled_placed
  drop_opt_proto_inner_state_noHeaderReceived_placed drop_opt_proto_inner_state_none_placed
)
open LibsignalBinary.Proofs.SpqrV1.Drop.ProtoTopClPlacedBudgetAux1 (
  drop_opt_proto_inner_state_ct1Received_cl drop_opt_proto_inner_state_ct2Sampled_cl
  drop_opt_proto_inner_state_ekReceivedCt1Sampled_cl
  drop_opt_proto_inner_state_ekSentCt1Received_cl drop_opt_proto_inner_state_headerReceived_cl
  drop_opt_proto_inner_state_headerSent_cl drop_opt_proto_inner_state_keysSampled_cl
  drop_opt_proto_inner_state_keysUnsampled_cl drop_opt_proto_inner_state_noHeaderReceived_cl
  drop_opt_proto_inner_state_none_cl proto_top_prologue_16_lscl
)
open LibsignalBinary.Proofs.SpqrV1.States.Recv.DropChunkedClPlacedBudget (
  drop_glue_proto_poly_encoder_mem_on
)
open LibsignalBinary.Proofs.SpqrV1.States.Recv.DropChunkedClPlacedBudgetAux (
  ls_to_blockProgram subroutine_ok_withLsCodeLoaded_intro
)

namespace LibsignalBinary.Proofs.SpqrV1.Drop.ProtoTopClPlacedBudgetAux2

open Arm64 ProofLib
open ProofLib.ProgramReflection

attribute [local irreducible] Program.fetch Program.externAt? Program.fnOff
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero
attribute [local simp, local arm64_norm] none2Cap_add_two_beq_zero noneCap_add_two_beq_zero

/-! ## Loop-Bearing Variants (`ct1Acknowledged`, `ct1Sampled`) -/

theorem drop_opt_proto_inner_state_ct1Acknowledged_cl [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {ext : String → Option (State → State)}
    (hdealloc : HookSat (Rust.withPanics ext) spqrRustDeallocSym
      (rustCliDeallocBudgetSpec M A lim))
    (st_pb : V1State.Chunked.Ct1Acknowledged) :
    subroutine_ok ((blkPC_267).rebase (blkPl_267).base (Rust.withPanics ext)) (blkPl_267).base
      (withLsCodeLoaded lsmpl (dropOptProtoInnerStatePlacedVariantSpec M A lim (some (.ct1Acknowledged st_pb)))) := by
  apply subroutine_ok_withLsCodeLoaded_intro; intro m hcl
  have hdealloc_raw : subroutine_ok ((blkPC_267).rebase (blkPl_267).base (Rust.withPanics ext))
      (lsρ spqrRustDeallocSym) (rustCliDeallocBudgetSpec M A lim) :=
    spqr_hook_ok_of_mem (prog := lsProg_267 (Rust.withPanics ext)) hdealloc
  simp only [spqrRustDeallocSym] at hdealloc_raw
  have hdealloc_fo := subroutine_ok_deallocFreeOnly hdealloc_raw
  have hloop := drop_opt_proto_inner_state_loop_192_placed hdealloc_raw
  clear hdealloc_raw
  simp only [deallocFreeOnlySpec, rustCliDeallocBudgetSpec] at hdealloc_fo
  dsimp only [withMemEq, dropOptProtoInnerStatePlacedVariantSpec, optProtoInnerStateSize, BitVec.ofNat_eq_ofNat]
    at hdealloc_fo hloop ⊢
  wp_init a_st s0
  have _hlr0_gpr : LsRetAddr624 (s0.readReg64 (Reg.gpr 30#5)) := by assumption
  rcases a_st with ⟨a, st⟩
  have hm_eq : s0.mem = m := by assumption
  subst hm_eq
  have hx0 : s0.readReg64 .x0 = a := by assumption
  dsimp only at *
  have hfsp_align : ((s0.sp - 48#64) &&& 15#64 == 0#64) = true :=
    spAligned_sub s0.sp 48#64 (by assumption) (by decide)
  have h136 : (a + 8#64) + 128#64 = a + 136#64 := BitVec.add_assoc a 8#64 128#64
  refine proto_top_prologue_16_lscl hcl (by assumption) (by assumption) (by assumption) hx0
    fun sv hpcv hrunv hcl_v hpres_v hacp_v hx0_v => ?_
  rcases hpres_v with ⟨hx23_v, hx24_v, hx25_v, hx26_v, hx27_v, hx28_v, hsp_v, htrace_v, hvregs_v⟩
  have ⟨_, _, _, _, _, _, _⟩ := hacp_v
  conv => arg 4; dsimp only [optProtoInnerStateAt, protoInnerStateAt, protoChunkedCt1AcknowledgedAt,
    optProtoInnerStateJumpTablePlacedAt, optProtoInnerStateJumpTableSym,
    optProtoInnerStateJumpTableBytes]
  refine seq_clean_evs (mid := (blkPl_267).base + 164#64)
    (P_evs := fun evs sm =>
      ((a ↦₆₄ 0x8000000000000009#64) ∗ memRegion (a + 8#64) 128 ∗
        optProtoPolynomialDecoderAt A.repAlloc (a + 136#64) (st_pb.receivingEk.map pbToProtoPolyDecoder) ∗
        memRegion (a + 176#64) 48) ∗ optProtoInnerStateJumpTablePlacedExpanded ∗
      A.pool lim (M.stepEvents evs st) sm ∗
      (memRegion (s0.sp - 4192#64) 48 ∗ stackAt (s0.sp - 48#64) allocHookStack) ∗
      (((s0.sp - 48#64) ↦₆₄ s0.readReg64 .fp) ∗ ((s0.sp - 40#64) ↦₆₄ s0.readReg64 .lr) ∗
       ((s0.sp - 32#64) ↦₆₄ s0.readReg64 .x22) ∗ ((s0.sp - 24#64) ↦₆₄ s0.readReg64 .x21) ∗
       ((s0.sp - 16#64) ↦₆₄ s0.readReg64 .x20) ∗ ((s0.sp - 8#64) ↦₆₄ s0.readReg64 .x19)))
    (Q := fun sm => Saved48Preserved s0 sm (s0.sp - 48#64) ∧ AllocCallPreserved s0 sm ∧
      sm.readReg64 .x0 = a) ?_ ?_
  · cases huc : st_pb.uc with
    | none =>
      have h16 : (a + 8#64) + 8#64 = a + 16#64 := BitVec.add_assoc a 8#64 8#64
      rw [optProtoUnchunkedCt1SentAt_none, h16]
      apply sepWP_evs_inst [] LibsignalBinary.Heap.FreeOnlyEvs.nil
      wp_steps
      have hnone128 : ((a + 8#64) ↦₆₄ noneCap) ∗ memRegion (a + 16#64) 120 ⊢ memRegion (a + 8#64) 128 := by
        rw [← h16]; exact optProtoUnchunkedCt1SentEkReceivedAt_none_entails_memRegion_128 A.repAlloc (a + 8#64)
      refine SepWP.focus_weaken hnone128 (by sep_focus) ?_
      dsimp only [optProtoInnerStateJumpTablePlacedExpanded, optProtoInnerStateJumpTableSym]
      refine sepWP_sync_pool sv (by simp only [wp_norm, arm64_norm]) (by sep_focus) ?_
      refine align_pre_st (by
        simp only [LibsignalBinary.Heap.AllocCostModel.stepEvents_nil,
          Reg.fp, Reg.lr, Reg.x19, Reg.x20, Reg.x21, Reg.x22, wp_norm, arm64_norm]
        sep_ac_rfl) ?_
      wp_done
    | some u =>
      rw [optProtoUnchunkedCt1SentAt_some, protoUnchunkedCt1SentAt_eq_ct1SentEkReceived]
      refine SepWP.focus_weaken
        (protoUnchunkedCt1SentEkReceivedAt_expose_cap A.repAlloc (a + 8#64) (ct1SentToCt1SentEkReceived u))
        (by sep_focus) ?_
      wp_pull_exists; rename_i cap ptr; wp_focus_pure; intro hcap_lt
      have hne_none := cap_add_one_beq_zero_false hcap_lt
      apply sepWP_seq_lscl hcl_v (mid := lsmpl.base 286)
      wp_steps
      apply SepWP.done (by wp_norm_lhs) (by wp_norm_lhs); intro hclc
      have hct1_sent := drop_proto_unchunked_ct1_sent_ek_received_mem_on
        (callerProg := lsProg_267 (Rust.withPanics ext)) hdealloc hclc
      dsimp only [lsProg_267, withMemEq, UnchunkedBudget.dropProtoUnchunkedCt1SentEkReceivedSpec, BitVec.ofNat_eq_ofNat] at hct1_sent
      refine SepWP.focus_weaken
        (protoUnchunkedCt1SentEkReceivedAt_unexpose_cap A.repAlloc (a + 8#64) cap ptr (ct1SentToCt1SentEkReceived u))
        (by sep_focus) ?_
      refine SepWP.focus_weaken (Entails.of_eq (stackAt_sub48_split_32 s0.sp)) (by sep_focus) ?_
      refine sepWP_sync_pool sv (by simp only [wp_norm, arm64_norm]) (by sep_focus) ?_
      wp_call hct1_sent (⟨a + 8#64, ct1SentToCt1SentEkReceived u⟩, st)
      rw [hsp_v]
      have hevs_w : FreeOnlyEvs w := by assumption
      have hacp_f : AllocCallPreserved s0 sf := hacp_v.trans (by assumption)
      rcases hacp_f with ⟨_, _, _, _, _, _, _⟩
      refine SepWP.focus_weaken (Entails.of_eq (stackAt_sub48_split_32 s0.sp).symm) (by sep_focus) ?_
      apply sepWP_evs_inst w hevs_w
      wp_steps
      dsimp only [protoUnchunkedCt1SentEkReceivedSize, optProtoInnerStateJumpTablePlacedExpanded,
        optProtoInnerStateJumpTableSym]
      refine sepWP_sync_pool sf (by simp only [wp_norm, arm64_norm]) (by sep_focus) ?_
      refine align_pre_st (by
        simp only [Reg.fp, Reg.lr, Reg.x19, Reg.x20, Reg.x21, Reg.x22, wp_norm, arm64_norm]
        sep_ac_rfl) ?_
      wp_done
  · intro evs1 s1 hevs1 hpc1 hrun1 ⟨⟨hx23_1, hx24_1, hx25_1, hx26_1, hx27_1, hx28_1, hsp_1, htrace_1, hvregs_1⟩, hacp_1, hx0_1⟩
    have ⟨_, _, _, _, _, _, _⟩ := hacp_1
    let st1 := M.stepEvents evs1 st
    have hjoin168 : memRegion (a + 8#64) 128 ∗ memRegion (a + 136#64) 40 ⊢ memRegion (a + 8#64) 168 := by
      rw [← h136, ProofLib.memRegion_split (a + 8#64) 128 40 (by decide)]; exact Entails.refl _
    have hjoin224 : (a ↦₆₄ 0x8000000000000009#64) ∗ memRegion (a + 8#64) 168 ∗ memRegion (a + 176#64) 48 ⊢ memRegion a 224 :=
      tag_and_two_regions_entails_224 a 0x8000000000000009#64 168 48 176#64 (BitVec.add_assoc a 8#64 168#64).symm rfl
    cases hek : st_pb.receivingEk with
    | none =>
      dsimp only [optProtoInnerStateJumpTablePlacedExpanded]
      simp only [Option.map_none, optProtoPolynomialDecoderAt_none']
      have h144 : (a + 136#64) + 8#64 = a + 144#64 := BitVec.add_assoc a 136#64 8#64
      rw [h144]
      refine sepWP_close_drop
        (fun sf' => memRegion a 224 ∗ optProtoInnerStateJumpTablePlacedAt ∗
          A.pool lim st1 sf' ∗ stackAt s0.sp dropStack96)
        ?_ (fun sf' _Pf hp hsp_f htr_f hacp_f hcs_f => ⟨fun hm => ?_, hsp_f, hcs_f⟩)
      · wp_steps
        have hnone40 : ((a + 136#64) ↦₆₄ noneCap) ∗ memRegion (a + 144#64) 32 ⊢ memRegion (a + 136#64) 40 := by
          rw [← h144]; exact optProtoPolyDecoder_none_entails_memRegion_40 (a + 136#64)
        refine SepWP.focus_weaken hnone40 (by sep_focus) ?_
        refine SepWP.focus_weaken hjoin168 (by sep_focus) ?_
        refine SepWP.focus_weaken hjoin224 (by sep_focus) ?_
        refine SepWP.focus_weaken (stack_restore_96_allocHook s0.sp (s0.readReg64 .fp) (s0.readReg64 .lr)
          (s0.readReg64 .x22) (s0.readReg64 .x21) (s0.readReg64 .x20) (s0.readReg64 .x19)) (by sep_focus) ?_
        dsimp only [optProtoInnerStateJumpTablePlacedAt, optProtoInnerStateJumpTableSym,
          optProtoInnerStateJumpTableBytes]
        refine sepWP_sync_pool s1 (by simp only [wp_norm, arm64_norm]) (by sep_focus) ?_
        wp_done
      · simp only [sepExists_sepConj_left, satisfies_sepExists]
        refine ⟨evs1, ?_⟩
        simp only [sepConj_assoc, satisfies_pure_sepConj]
        refine ⟨⟨htr_f, hacp_f, hevs1⟩, ?_⟩
        exact Satisfies.mono (Entails.trans (sepConj_mono_left hp) (Entails.of_eq (by sep_ac_rfl))) hm
    | some dec =>
      simp only [Option.map_some, optProtoPolynomialDecoderAt_some']
      let pb := pbToProtoPolyDecoder dec
      refine SepWP.focus_weaken (protoPolyDecoderAt_entails_dealloc A.repAlloc (a + 136#64) pb) (by sep_focus) ?_
      wp_pull_exists; rename_i g; wp_focus_pure; rintro ⟨hpts_le, hpts_cap_lt, hpts_ptr_ne⟩
      have hpts_cap_pow : g.cap.toNat < 2 ^ 63 := by omega
      have hne_none := cap_add_one_beq_zero_false hpts_cap_pow
      have h144 : (a + 136#64) + 8#64 = a + 144#64 := BitVec.add_assoc a 136#64 8#64
      have h152 : (a + 136#64) + 16#64 = a + 152#64 := BitVec.add_assoc a 136#64 16#64
      have h160 : (a + 136#64) + 24#64 = a + 160#64 := BitVec.add_assoc a 136#64 24#64
      refine seq_clean_evs (mid := (blkPl_267).base + 444#64)
        (P_evs := fun evs sm =>
          (a ↦₆₄ 0x8000000000000009#64) ∗ memRegion (a + 8#64) 128 ∗
          ((a + 136#64) ↦₆₄ g.cap) ∗ ((a + 144#64) ↦₆₄ g.ptr) ∗ ((a + 152#64) ↦₆₄ BitVec.ofNat 64 pb.pts.length) ∗
          (if g.cap = 0 then emp else A.live g.ptr (g.cap.toNat * 24) 8 ∗ memRegion g.ptr (g.cap.toNat * 24)) ∗
          memRegion (a + 160#64) 16 ∗ memRegion (a + 176#64) 48 ∗ optProtoInnerStateJumpTablePlacedExpanded ∗
          A.pool lim (M.stepEvents evs st1) sm ∗
          (memRegion (s0.sp - 4192#64) 48 ∗ stackAt (s0.sp - 48#64) allocHookStack) ∗
          (((s0.sp - 48#64) ↦₆₄ s0.readReg64 .fp) ∗ ((s0.sp - 40#64) ↦₆₄ s0.readReg64 .lr) ∗
           ((s0.sp - 32#64) ↦₆₄ s0.readReg64 .x22) ∗ ((s0.sp - 24#64) ↦₆₄ s0.readReg64 .x21) ∗
           ((s0.sp - 16#64) ↦₆₄ s0.readReg64 .x20) ∗ ((s0.sp - 8#64) ↦₆₄ s0.readReg64 .x19)))
        (Q := fun sm => Saved48Preserved s0 sm (s0.sp - 48#64) ∧ AllocCallPreserved s0 sm ∧
          sm.readReg64 .x19 = g.ptr ∧ sm.readReg64 .x20 = g.cap) ?_ ?_
      · dsimp only [LibsignalBinary.Heap.RustCliAllocBudget.repAlloc_live]
        generalize hxs : pb.pts = xs at hpts_le ⊢
        cases xs with
        | nil =>
          apply sepWP_evs_nil
          simp only [LibsignalBinary.Heap.AllocCostModel.stepEvents_nil,
            List.length_nil, Nat.zero_mul, Nat.sub_zero, BitVec.ofNat_eq_ofNat, BitVec.add_zero, arrayAt, emp_sepConj]
          wp_steps
          refine sepWP_sync_pool s1 (by simp only [wp_norm, arm64_norm]) (by sep_focus) ?_
          refine align_pre_st (by sep_ac_rfl) ?_
          wp_done
        | cons bs tl =>
          have hlen_pos : 0 < (bs :: tl).length := by simp
          have hlen_lt : (bs :: tl).length * 24 < 2 ^ 63 := by
            have : (bs :: tl).length * 24 ≤ g.cap.toNat * 24 := Nat.mul_le_mul_right 24 hpts_le
            omega
          have hne0 := ofNat_beq_zero_false_24 hlen_pos hlen_lt
          have hcap_ne : g.cap ≠ 0 := by intro hc0; rw [hc0] at hpts_le; simp at hpts_le
          simp only [hcap_ne, ↓reduceIte]
          refine seq_vm_clean (mid := (blkPl_267).base + 204#64)
            (P_mid := arrayAt (fun bs addr => vecU8 A.repAlloc addr bs) 24 g.ptr (bs :: tl) ∗
              A.pool lim st1 s1 ∗ stackAt (s0.sp - 48#64) allocHookStack ∗
              ((a ↦₆₄ 0x8000000000000009#64) ∗ memRegion (a + 8#64) 128 ∗
               ((a + 136#64) ↦₆₄ g.cap) ∗ ((a + 144#64) ↦₆₄ g.ptr) ∗ ((a + 152#64) ↦₆₄ BitVec.ofNat 64 (bs :: tl).length) ∗
               A.live g.ptr (g.cap.toNat * 24) 8 ∗
               memRegion (g.ptr + BitVec.ofNat 64 ((bs :: tl).length * 24)) ((g.cap.toNat - (bs :: tl).length) * 24) ∗
               memRegion (a + 160#64) 16 ∗ memRegion (a + 176#64) 48 ∗ optProtoInnerStateJumpTablePlacedExpanded ∗
               memRegion (s0.sp - 4192#64) 48 ∗
               (((s0.sp - 48#64) ↦₆₄ s0.readReg64 .fp) ∗ ((s0.sp - 40#64) ↦₆₄ s0.readReg64 .lr) ∗
                ((s0.sp - 32#64) ↦₆₄ s0.readReg64 .x22) ∗ ((s0.sp - 24#64) ↦₆₄ s0.readReg64 .x21) ∗
                ((s0.sp - 16#64) ↦₆₄ s0.readReg64 .x20) ∗ ((s0.sp - 8#64) ↦₆₄ s0.readReg64 .x19))))
            (Q := fun sm => Saved48Preserved s0 sm (s0.sp - 48#64) ∧ AllocCallPreserved s0 sm ∧
              sm.readReg64 .x19 = g.ptr ∧ sm.readReg64 .x20 = g.cap ∧
              sm.readReg64 .x21 = BitVec.ofNat 64 (bs :: tl).length ∧ sm.readReg64 .x22 = g.ptr + 8#64) ?_ ?_
          · by_vm_steps (
              wp_steps
              refine align_pre_vm (by sep_ac_rfl) ?_
              wp_done)
          · intro s_loop hpc_loop hrun_loop hvm_loop ⟨hpres_loop, hacp_loop, hx19_loop, hx20_loop, hx21_loop, hx22_loop⟩
            rw [← A.pool_of_vmPreserved hvm_loop]
            refine SepWP.mono
              (hloop s0 (s0.sp - 48#64) g.ptr g.cap hfsp_align (bs :: tl) g.ptr st1 s_loop _
                (List.cons_ne_nil _ _) hlen_lt hpc_loop hrun_loop hpres_loop hacp_loop hx19_loop hx20_loop hx21_loop hx22_loop)
              fun sf_l _Pf_l _ _ ⟨evs_l, hevs_l, hp_l, hq_l⟩ => ?_
            refine ⟨evs_l, hevs_l, Entails.trans hp_l ?_, hq_l⟩
            have hsplit : g.cap.toNat * 24 = (bs :: tl).length * 24 + (g.cap.toNat - (bs :: tl).length) * 24 := by
              rw [← Nat.add_mul]; congr 1; omega
            have hbound : (bs :: tl).length * 24 + (g.cap.toNat - (bs :: tl).length) * 24 ≤ 2 ^ 64 := by rw [← hsplit]; omega
            have hrejoin : memRegion g.ptr ((bs :: tl).length * 24) ∗
                memRegion (g.ptr + BitVec.ofNat 64 ((bs :: tl).length * 24)) ((g.cap.toNat - (bs :: tl).length) * 24) ⊢
                memRegion g.ptr (g.cap.toNat * 24) := by
              rw [hsplit, ProofLib.memRegion_split g.ptr ((bs :: tl).length * 24) ((g.cap.toNat - (bs :: tl).length) * 24) hbound]
              exact Entails.refl _
            refine Entails.trans (Entails.of_eq (by sep_ac_rfl))
              (Entails.trans (sepConj_mono_left hrejoin) (Entails.of_eq (by sep_ac_rfl)))
      · intro evs2 s2 hevs2 hpc2 hrun2 ⟨⟨hx23_2, hx24_2, hx25_2, hx26_2, hx27_2, hx28_2, hsp_2, htrace_2, hvregs_2⟩, hacp_2, hx19_2, hx20_2⟩
        have ⟨_, _, _, _, _, _, _⟩ := hacp_2
        let st2 := M.stepEvents evs2 st1
        dsimp only [optProtoInnerStateJumpTablePlacedExpanded]
        have hhdr40 : ((a + 136#64) ↦₆₄ g.cap) ∗ ((a + 144#64) ↦₆₄ g.ptr) ∗
            ((a + 152#64) ↦₆₄ BitVec.ofNat 64 pb.pts.length) ∗ memRegion (a + 160#64) 16 ⊢ memRegion (a + 136#64) 40 := by
          rw [← h144, ← h152, ← h160]
          exact protoPolyDecoderHeaders_entails_memRegion_40 (a + 136#64) g.cap g.ptr (BitVec.ofNat 64 pb.pts.length)
        by_cases hc : g.cap = 0
        · have hc_beq : (g.cap == 0#64) = true := by rw [beq_iff_eq]; exact hc
          simp only [hc, ↓reduceIte, emp_sepConj, sepConj_emp] at hx20_2 hhdr40 ⊢
          refine sepWP_close_drop
            (fun sf' => memRegion a 224 ∗ optProtoInnerStateJumpTablePlacedAt ∗
              A.pool lim st2 sf' ∗ stackAt s0.sp dropStack96)
            ?_ (fun sf' _Pf hp hsp_f htr_f hacp_f hcs_f => ⟨fun hm => ?_, hsp_f, hcs_f⟩)
          · wp_steps
            refine SepWP.focus_weaken hhdr40 (by sep_focus) ?_
            refine SepWP.focus_weaken hjoin168 (by sep_focus) ?_
            refine SepWP.focus_weaken hjoin224 (by sep_focus) ?_
            refine SepWP.focus_weaken (stack_restore_96_allocHook s0.sp (s0.readReg64 .fp) (s0.readReg64 .lr)
              (s0.readReg64 .x22) (s0.readReg64 .x21) (s0.readReg64 .x20) (s0.readReg64 .x19)) (by sep_focus) ?_
            dsimp only [optProtoInnerStateJumpTablePlacedAt, optProtoInnerStateJumpTableSym,
              optProtoInnerStateJumpTableBytes]
            refine sepWP_sync_pool s2 (by simp only [wp_norm, arm64_norm]) (by sep_focus) ?_
            wp_done
          · simp only [sepExists_sepConj_left, satisfies_sepExists]
            refine ⟨evs1 ++ evs2, ?_⟩
            simp only [sepConj_assoc, satisfies_pure_sepConj]
            refine ⟨⟨htr_f, hacp_f, hevs1.append hevs2⟩, ?_⟩
            have heq_st : M.stepEvents (evs1 ++ evs2) st = st2 := by
              simp only [st2, st1, LibsignalBinary.Heap.AllocCostModel.stepEvents_append]
            rw [heq_st]
            exact Satisfies.mono (Entails.trans (sepConj_mono_left hp) (Entails.of_eq (by sep_ac_rfl))) hm
        · have hc_beq : ¬((g.cap == 0#64) = true) := by rw [beq_iff_eq]; exact hc
          have hlsl := cap_mul_24 hpts_cap_lt
          simp only [hc, ↓reduceIte]
          refine sepWP_close_drop
            (fun sf' => memRegion a 224 ∗ optProtoInnerStateJumpTablePlacedAt ∗
              A.pool lim (M.stepEvents (rustDeallocEvents (g.cap.toNat * 24) 8) st2) sf' ∗
              stackAt s0.sp dropStack96)
            ?_ (fun sf' _Pf hp hsp_f htr_f hacp_f hcs_f => ⟨fun hm => ?_, hsp_f, hcs_f⟩)
          · wp_steps
            refine SepWP.focus_weaken hhdr40 (by sep_focus) ?_
            refine SepWP.focus_weaken hjoin168 (by sep_focus) ?_
            refine SepWP.focus_weaken hjoin224 (by sep_focus) ?_
            refine SepWP.focus_weaken (stack_restore_96_allocHook s0.sp (s0.readReg64 .fp) (s0.readReg64 .lr)
              (s0.readReg64 .x22) (s0.readReg64 .x21) (s0.readReg64 .x20) (s0.readReg64 .x19)) (by sep_focus) ?_
            refine SepWP.focus_weaken (Entails.of_eq (stackAt_dropStack96_split_bottom s0.sp)) (by sep_focus) ?_
            refine sepWP_sync_pool s2 (by simp only [wp_norm, arm64_norm]) (by sep_focus) ?_
            wp_call hdealloc_fo (g.ptr, g.cap.toNat * 24, 8, st2)
            have hacp_f : AllocCallPreserved s0 sf := hacp_2.trans (by assumption)
            have ⟨_, _, _, _, _, _, _⟩ := hacp_f
            refine SepWP.focus_weaken (Entails.of_eq (stackAt_dropStack96_split_bottom s0.sp).symm) (by sep_focus) ?_
            dsimp only [optProtoInnerStateJumpTablePlacedAt, optProtoInnerStateJumpTableSym,
              optProtoInnerStateJumpTableBytes]
            wp_done
          · simp only [sepExists_sepConj_left, satisfies_sepExists]
            refine ⟨(evs1 ++ evs2) ++ rustDeallocEvents (g.cap.toNat * 24) 8, ?_⟩
            simp only [sepConj_assoc, satisfies_pure_sepConj]
            refine ⟨⟨htr_f, hacp_f, (hevs1.append hevs2).append
              (LibsignalBinary.Heap.FreeOnlyEvs.singleton 8 (g.cap.toNat * 24))⟩, ?_⟩
            have heq_st : M.stepEvents ((evs1 ++ evs2) ++ rustDeallocEvents (g.cap.toNat * 24) 8) st =
                M.stepEvents (rustDeallocEvents (g.cap.toNat * 24) 8) st2 := by
              simp only [st2, st1, LibsignalBinary.Heap.AllocCostModel.stepEvents_append]
            rw [heq_st]
            exact Satisfies.mono (Entails.trans (sepConj_mono_left hp) (Entails.of_eq (by sep_ac_rfl))) hm

theorem drop_opt_proto_inner_state_ct1Sampled_cl [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {ext : String → Option (State → State)}
    (hdealloc : HookSat (Rust.withPanics ext) spqrRustDeallocSym
      (rustCliDeallocBudgetSpec M A lim))
    (st_pb : V1State.Chunked.Ct1Sampled) :
    subroutine_ok ((blkPC_267).rebase (blkPl_267).base (Rust.withPanics ext)) (blkPl_267).base
      (withLsCodeLoaded lsmpl (dropOptProtoInnerStatePlacedVariantSpec M A lim (some (.ct1Sampled st_pb)))) := by
  apply subroutine_ok_withLsCodeLoaded_intro; intro m hcl
  have hdealloc_raw : subroutine_ok ((blkPC_267).rebase (blkPl_267).base (Rust.withPanics ext))
      (lsρ spqrRustDeallocSym) (rustCliDeallocBudgetSpec M A lim) :=
    spqr_hook_ok_of_mem (prog := lsProg_267 (Rust.withPanics ext)) hdealloc
  simp only [spqrRustDeallocSym] at hdealloc_raw
  have hdealloc_fo := subroutine_ok_deallocFreeOnly hdealloc_raw
  have hloop := drop_opt_proto_inner_state_loop_408_placed hdealloc_raw
  clear hdealloc_raw
  simp only [deallocFreeOnlySpec, rustCliDeallocBudgetSpec] at hdealloc_fo
  dsimp only [withMemEq, dropOptProtoInnerStatePlacedVariantSpec, optProtoInnerStateSize, BitVec.ofNat_eq_ofNat]
    at hdealloc_fo hloop ⊢
  wp_init a_st s0
  have _hlr0_gpr : LsRetAddr624 (s0.readReg64 (Reg.gpr 30#5)) := by assumption
  rcases a_st with ⟨a, st⟩
  have hm_eq : s0.mem = m := by assumption
  subst hm_eq
  have hx0 : s0.readReg64 .x0 = a := by assumption
  dsimp only at *
  have hfsp_align : ((s0.sp - 48#64) &&& 15#64 == 0#64) = true :=
    spAligned_sub s0.sp 48#64 (by assumption) (by decide)
  refine proto_top_prologue_16_lscl hcl (by assumption) (by assumption) (by assumption) hx0
    fun sv hpcv hrunv hcl_v hpres_v hacp_v hx0_v => ?_
  rcases hpres_v with ⟨hx23_v, hx24_v, hx25_v, hx26_v, hx27_v, hx28_v, hsp_v, htrace_v, hvregs_v⟩
  have ⟨_, _, _, _, _, _, _⟩ := hacp_v
  conv => arg 4; dsimp only [optProtoInnerStateAt, protoInnerStateAt, protoChunkedCt1SampledAt,
    optProtoInnerStateJumpTablePlacedAt, optProtoInnerStateJumpTableSym,
    optProtoInnerStateJumpTableBytes]
  refine seq_clean_evs_lscl hcl_v (mid := (blkPl_267).base + 348#64)
    (P_evs := fun evs sm =>
      (memRegion a 128 ∗
        optProtoPolynomialEncoderAt A.repAlloc (a + 128#64) (st_pb.sendingCt1.map pbToProtoPolyEncoder) ∗
        optProtoPolynomialDecoderAt A.repAlloc (a + 184#64) (st_pb.receivingEk.map pbToProtoPolyDecoder)) ∗
      optProtoInnerStateJumpTablePlacedExpanded ∗
      A.pool lim (M.stepEvents evs st) sm ∗
      (memRegion (s0.sp - 4192#64) 48 ∗ stackAt (s0.sp - 48#64) allocHookStack) ∗
      (((s0.sp - 48#64) ↦₆₄ s0.readReg64 .fp) ∗ ((s0.sp - 40#64) ↦₆₄ s0.readReg64 .lr) ∗
       ((s0.sp - 32#64) ↦₆₄ s0.readReg64 .x22) ∗ ((s0.sp - 24#64) ↦₆₄ s0.readReg64 .x21) ∗
       ((s0.sp - 16#64) ↦₆₄ s0.readReg64 .x20) ∗ ((s0.sp - 8#64) ↦₆₄ s0.readReg64 .x19)))
    (Q := fun sm => Saved48Preserved s0 sm (s0.sp - 48#64) ∧ AllocCallPreserved s0 sm ∧
      sm.readReg64 .x0 = a) ?_ ?_
  · cases huc : st_pb.uc with
    | none =>
      rw [optProtoUnchunkedCt1SentAt_none]
      apply sepWP_evs_inst [] LibsignalBinary.Heap.FreeOnlyEvs.nil
      wp_steps
      have hnone128 : (a ↦₆₄ noneCap) ∗ memRegion (a + 8#64) 120 ⊢ memRegion a 128 :=
        optProtoUnchunkedCt1SentEkReceivedAt_none_entails_memRegion_128 A.repAlloc a
      refine SepWP.focus_weaken hnone128 (by sep_focus) ?_
      dsimp only [optProtoInnerStateJumpTablePlacedExpanded, optProtoInnerStateJumpTableSym]
      refine sepWP_sync_pool sv (by simp only [wp_norm, arm64_norm]) (by sep_focus) ?_
      refine align_pre_st (by
        simp only [LibsignalBinary.Heap.AllocCostModel.stepEvents_nil,
          Reg.fp, Reg.lr, Reg.x19, Reg.x20, Reg.x21, Reg.x22, wp_norm, arm64_norm]
        sep_ac_rfl) ?_
      wp_done
    | some u =>
      rw [optProtoUnchunkedCt1SentAt_some, protoUnchunkedCt1SentAt_eq_ct1SentEkReceived]
      refine SepWP.focus_weaken
        (protoUnchunkedCt1SentEkReceivedAt_expose_cap A.repAlloc a (ct1SentToCt1SentEkReceived u))
        (by sep_focus) ?_
      wp_pull_exists; rename_i cap ptr; wp_focus_pure; intro hcap_lt
      have hne_none2 := cap_add_two_beq_zero_false hcap_lt
      have hne_none1 := cap_add_one_beq_zero_false hcap_lt
      have hcc_false := cap_xor_highBit_cc_11_false hcap_lt
      apply sepWP_seq_lscl hcl_v (mid := lsmpl.base 286)
      wp_steps
      apply SepWP.done (by wp_norm_lhs) (by wp_norm_lhs); intro hclc1
      have hct1_sent := drop_proto_unchunked_ct1_sent_ek_received_mem_on
        (callerProg := lsProg_267 (Rust.withPanics ext)) hdealloc hclc1
      dsimp only [lsProg_267, withMemEq, UnchunkedBudget.dropProtoUnchunkedCt1SentEkReceivedSpec, BitVec.ofNat_eq_ofNat] at hct1_sent
      refine SepWP.focus_weaken
        (protoUnchunkedCt1SentEkReceivedAt_unexpose_cap A.repAlloc a cap ptr (ct1SentToCt1SentEkReceived u))
        (by sep_focus) ?_
      refine SepWP.focus_weaken (Entails.of_eq (stackAt_sub48_split_32 s0.sp)) (by sep_focus) ?_
      refine sepWP_sync_pool sv (by simp only [wp_norm, arm64_norm]) (by sep_focus) ?_
      wp_call hct1_sent (⟨a, ct1SentToCt1SentEkReceived u⟩, st)
      rw [hsp_v]
      have hevs_w : FreeOnlyEvs w := by assumption
      have hacp_f : AllocCallPreserved s0 sf := hacp_v.trans (by assumption)
      rcases hacp_f with ⟨_, _, _, _, _, _, _⟩
      refine SepWP.focus_weaken (Entails.of_eq (stackAt_sub48_split_32 s0.sp).symm) (by sep_focus) ?_
      apply sepWP_evs_inst w hevs_w
      wp_steps
      dsimp only [protoUnchunkedCt1SentEkReceivedSize, optProtoInnerStateJumpTablePlacedExpanded,
        optProtoInnerStateJumpTableSym]
      refine sepWP_sync_pool sf (by simp only [wp_norm, arm64_norm]) (by sep_focus) ?_
      refine align_pre_st (by
        simp only [Reg.fp, Reg.lr, Reg.x19, Reg.x20, Reg.x21, Reg.x22, wp_norm, arm64_norm]
        sep_ac_rfl) ?_
      wp_done
  · intro evs1 s1 hevs1 hpc1 hrun1 hcl1 ⟨⟨hx23_1, hx24_1, hx25_1, hx26_1, hx27_1, hx28_1, hsp_1, htrace_1, hvregs_1⟩, hacp_1, hx0_1⟩
    have ⟨_, _, _, _, _, _, _⟩ := hacp_1
    let st1 := M.stepEvents evs1 st
    refine seq_clean_evs (mid := (blkPl_267).base + 380#64)
      (P_evs := fun evs sm =>
        (memRegion a 184 ∗
          optProtoPolynomialDecoderAt A.repAlloc (a + 184#64) (st_pb.receivingEk.map pbToProtoPolyDecoder)) ∗
        optProtoInnerStateJumpTablePlacedExpanded ∗
        A.pool lim (M.stepEvents evs st1) sm ∗
        (memRegion (s0.sp - 4192#64) 48 ∗ stackAt (s0.sp - 48#64) allocHookStack) ∗
        (((s0.sp - 48#64) ↦₆₄ s0.readReg64 .fp) ∗ ((s0.sp - 40#64) ↦₆₄ s0.readReg64 .lr) ∗
         ((s0.sp - 32#64) ↦₆₄ s0.readReg64 .x22) ∗ ((s0.sp - 24#64) ↦₆₄ s0.readReg64 .x21) ∗
         ((s0.sp - 16#64) ↦₆₄ s0.readReg64 .x20) ∗ ((s0.sp - 8#64) ↦₆₄ s0.readReg64 .x19)))
      (Q := fun sm => Saved48Preserved s0 sm (s0.sp - 48#64) ∧ AllocCallPreserved s0 sm ∧
        sm.readReg64 .x0 = a) ?_ ?_
    · have hjoin184 : memRegion a 128 ∗ memRegion (a + 128#64) 56 ⊢ memRegion a 184 := by
        rw [ProofLib.memRegion_split a 128 56 (by decide)]; exact Entails.refl _
      cases hct1 : st_pb.sendingCt1 with
      | none =>
        apply sepWP_evs_nil
        simp only [LibsignalBinary.Heap.AllocCostModel.stepEvents_nil,
          Option.map_none, optProtoPolynomialEncoderAt_none']
        have h136 : (a + 128#64) + 8#64 = a + 136#64 := BitVec.add_assoc a 128#64 8#64
        rw [h136]; wp_steps
        have hnone56 : ((a + 128#64) ↦₆₄ noneCap) ∗ memRegion (a + 136#64) 48 ⊢ memRegion (a + 128#64) 56 := by
          rw [← h136]; exact optProtoPolyEncoder_none_entails_memRegion_56 (a + 128#64)
        refine SepWP.focus_weaken hnone56 (by sep_focus) ?_
        refine SepWP.focus_weaken hjoin184 (by sep_focus) ?_
        refine sepWP_sync_pool s1 (by simp only [wp_norm, arm64_norm]) (by sep_focus) ?_
        refine align_pre_st (by sep_ac_rfl) ?_
        wp_done
      | some enc =>
        simp only [Option.map_some, optProtoPolynomialEncoderAt_some']
        refine SepWP.focus_weaken
          (protoPolynomialEncoderAt_expose_cap A.repAlloc (a + 128#64) (pbToProtoPolyEncoder enc))
          (by sep_focus) ?_
        wp_pull_exists; rename_i cap ptr; wp_focus_pure; intro hcap_lt
        have hne_none := cap_add_one_beq_zero_false hcap_lt
        apply sepWP_seq_lscl hcl1 (mid := lsmpl.base 271)
        wp_steps
        apply SepWP.done (by wp_norm_lhs) (by wp_norm_lhs); intro hclc2
        have hpoly_enc := drop_glue_proto_poly_encoder_mem_on
          (callerProg := lsProg_267 (Rust.withPanics ext)) hdealloc hclc2
        dsimp only [lsProg_267, withMemEq, ProtoPolyBudget.dropProtoPolyEncoderSpec, BitVec.ofNat_eq_ofNat] at hpoly_enc
        refine SepWP.focus_weaken
          (protoPolynomialEncoderAt_unexpose_cap A.repAlloc (a + 128#64) cap ptr (pbToProtoPolyEncoder enc))
          (by sep_focus) ?_
        refine SepWP.focus_weaken (Entails.of_eq (stackAt_sub48_eq_dropStack48 s0.sp)) (by sep_focus) ?_
        refine sepWP_sync_pool s1 (by simp only [wp_norm, arm64_norm]) (by sep_focus) ?_
        wp_call hpoly_enc (⟨a + 128#64, pbToProtoPolyEncoder enc⟩, st1)
        have hacp_cf : AllocCallPreserved s1 sf := by assumption
        have hevs_w : FreeOnlyEvs w := by assumption
        have hacp_f : AllocCallPreserved s0 sf := hacp_1.trans hacp_cf
        have ⟨_, _, _, _, _, _, _⟩ := hacp_f
        have hsp_eq : stackAt s1.sp dropStack48 = memRegion (s0.sp - 4192#64) 48 ∗ stackAt (s0.sp - 48#64) allocHookStack := by
          rw [hsp_1, ← stackAt_sub48_eq_dropStack48]
        refine SepWP.mono (post := fun sm Pm =>
            (Pm ⊢
              (memRegion a 184 ∗
                optProtoPolynomialDecoderAt A.repAlloc (a + 184#64) (st_pb.receivingEk.map pbToProtoPolyDecoder)) ∗
              optProtoInnerStateJumpTablePlacedExpanded ∗
              A.pool lim (M.stepEvents w st1) sm ∗
              (memRegion (s0.sp - 4192#64) 48 ∗ stackAt (s0.sp - 48#64) allocHookStack) ∗
              (((s0.sp - 48#64) ↦₆₄ s0.readReg64 .fp) ∗ ((s0.sp - 40#64) ↦₆₄ s0.readReg64 .lr) ∗
               ((s0.sp - 32#64) ↦₆₄ s0.readReg64 .x22) ∗ ((s0.sp - 24#64) ↦₆₄ s0.readReg64 .x21) ∗
               ((s0.sp - 16#64) ↦₆₄ s0.readReg64 .x20) ∗ ((s0.sp - 8#64) ↦₆₄ s0.readReg64 .x19))) ∧
            Saved48Preserved s0 sm (s0.sp - 48#64) ∧ AllocCallPreserved s0 sm ∧
            sm.readReg64 .x0 = a)
          ?_ (fun _ _ _ _ ⟨hp, hq⟩ =>
            ⟨w, hevs_w, Entails.trans hp (Entails.of_eq (by ac_rfl)), hq⟩)
        refine SepWP.focus_weaken (Entails.of_eq hsp_eq) (by sep_focus) ?_
        wp_steps
        change _ at hjoin184
        refine SepWP.focus_weaken hjoin184 (by sep_focus) ?_
        refine sepWP_sync_pool sf (by simp only [wp_norm, arm64_norm]) (by sep_focus) ?_
        refine align_pre_st (by dsimp only [Reg.fp, Reg.lr, Reg.x19, Reg.x20, Reg.x21, Reg.x22]; sep_ac_rfl) ?_
        wp_done
    · intro evs2 s2 hevs2 hpc2 hrun2 ⟨⟨hx23_2, hx24_2, hx25_2, hx26_2, hx27_2, hx28_2, hsp_2, htrace_2, hvregs_2⟩, hacp_2, hx0_2⟩
      have ⟨_, _, _, _, _, _, _⟩ := hacp_2
      let st2 := M.stepEvents evs2 st1
      have hjoin224 : memRegion a 184 ∗ memRegion (a + 184#64) 40 ⊢ memRegion a 224 := by
        rw [ProofLib.memRegion_split a 184 40 (by decide)]; exact Entails.refl _
      cases hek : st_pb.receivingEk with
      | none =>
        dsimp only [optProtoInnerStateJumpTablePlacedExpanded]
        simp only [Option.map_none, optProtoPolynomialDecoderAt_none']
        have h192 : (a + 184#64) + 8#64 = a + 192#64 := BitVec.add_assoc a 184#64 8#64
        rw [h192]
        refine sepWP_close_drop
          (fun sf' => memRegion a 224 ∗ optProtoInnerStateJumpTablePlacedAt ∗
            A.pool lim st2 sf' ∗ stackAt s0.sp dropStack96)
          ?_ (fun sf' _Pf hp hsp_f htr_f hacp_f hcs_f => ⟨fun hm => ?_, hsp_f, hcs_f⟩)
        · wp_steps
          have hnone40 : ((a + 184#64) ↦₆₄ noneCap) ∗ memRegion (a + 192#64) 32 ⊢ memRegion (a + 184#64) 40 := by
            rw [← h192]; exact optProtoPolyDecoder_none_entails_memRegion_40 (a + 184#64)
          refine SepWP.focus_weaken hnone40 (by sep_focus) ?_
          refine SepWP.focus_weaken hjoin224 (by sep_focus) ?_
          refine SepWP.focus_weaken (stack_restore_96_allocHook s0.sp (s0.readReg64 .fp) (s0.readReg64 .lr)
            (s0.readReg64 .x22) (s0.readReg64 .x21) (s0.readReg64 .x20) (s0.readReg64 .x19)) (by sep_focus) ?_
          dsimp only [optProtoInnerStateJumpTablePlacedAt, optProtoInnerStateJumpTableSym,
            optProtoInnerStateJumpTableBytes]
          refine sepWP_sync_pool s2 (by simp only [wp_norm, arm64_norm]) (by sep_focus) ?_
          wp_done
        · simp only [sepExists_sepConj_left, satisfies_sepExists]
          refine ⟨evs1 ++ evs2, ?_⟩
          simp only [sepConj_assoc, satisfies_pure_sepConj]
          refine ⟨⟨htr_f, hacp_f, hevs1.append hevs2⟩, ?_⟩
          have heq_st : M.stepEvents (evs1 ++ evs2) st = st2 := by
            simp only [st2, st1, LibsignalBinary.Heap.AllocCostModel.stepEvents_append]
          rw [heq_st]
          exact Satisfies.mono (Entails.trans (sepConj_mono_left hp) (Entails.of_eq (by sep_ac_rfl))) hm
      | some dec =>
        simp only [Option.map_some, optProtoPolynomialDecoderAt_some']
        let pb := pbToProtoPolyDecoder dec
        refine SepWP.focus_weaken (protoPolyDecoderAt_entails_dealloc A.repAlloc (a + 184#64) pb) (by sep_focus) ?_
        wp_pull_exists; rename_i g; wp_focus_pure; rintro ⟨hpts_le, hpts_cap_lt, hpts_ptr_ne⟩
        have hpts_cap_pow : g.cap.toNat < 2 ^ 63 := by omega
        have hne_none := cap_add_one_beq_zero_false hpts_cap_pow
        have h192 : (a + 184#64) + 8#64 = a + 192#64 := BitVec.add_assoc a 184#64 8#64
        have h200 : (a + 184#64) + 16#64 = a + 200#64 := BitVec.add_assoc a 184#64 16#64
        have h208 : (a + 184#64) + 24#64 = a + 208#64 := BitVec.add_assoc a 184#64 24#64
        refine seq_clean_evs (mid := (blkPl_267).base + 444#64)
          (P_evs := fun evs sm =>
            memRegion a 184 ∗
            ((a + 184#64) ↦₆₄ g.cap) ∗ ((a + 192#64) ↦₆₄ g.ptr) ∗ ((a + 200#64) ↦₆₄ BitVec.ofNat 64 pb.pts.length) ∗
            (if g.cap = 0 then emp else A.live g.ptr (g.cap.toNat * 24) 8 ∗ memRegion g.ptr (g.cap.toNat * 24)) ∗
            memRegion (a + 208#64) 16 ∗ optProtoInnerStateJumpTablePlacedExpanded ∗
            A.pool lim (M.stepEvents evs st2) sm ∗
            (memRegion (s0.sp - 4192#64) 48 ∗ stackAt (s0.sp - 48#64) allocHookStack) ∗
            (((s0.sp - 48#64) ↦₆₄ s0.readReg64 .fp) ∗ ((s0.sp - 40#64) ↦₆₄ s0.readReg64 .lr) ∗
             ((s0.sp - 32#64) ↦₆₄ s0.readReg64 .x22) ∗ ((s0.sp - 24#64) ↦₆₄ s0.readReg64 .x21) ∗
             ((s0.sp - 16#64) ↦₆₄ s0.readReg64 .x20) ∗ ((s0.sp - 8#64) ↦₆₄ s0.readReg64 .x19)))
          (Q := fun sm => Saved48Preserved s0 sm (s0.sp - 48#64) ∧ AllocCallPreserved s0 sm ∧
            sm.readReg64 .x19 = g.ptr ∧ sm.readReg64 .x20 = g.cap) ?_ ?_
        · dsimp only [LibsignalBinary.Heap.RustCliAllocBudget.repAlloc_live]
          generalize hxs : pb.pts = xs at hpts_le ⊢
          cases xs with
          | nil =>
            apply sepWP_evs_nil
            simp only [LibsignalBinary.Heap.AllocCostModel.stepEvents_nil,
              List.length_nil, Nat.zero_mul, Nat.sub_zero, BitVec.ofNat_eq_ofNat, BitVec.add_zero, arrayAt, emp_sepConj]
            wp_steps
            refine sepWP_sync_pool s2 (by simp only [wp_norm, arm64_norm]) (by sep_focus) ?_
            refine align_pre_st (by sep_ac_rfl) ?_
            wp_done
          | cons bs tl =>
            have hlen_pos : 0 < (bs :: tl).length := by simp
            have hlen_lt : (bs :: tl).length * 24 < 2 ^ 63 := by
              have : (bs :: tl).length * 24 ≤ g.cap.toNat * 24 := Nat.mul_le_mul_right 24 hpts_le
              omega
            have hne0 := ofNat_beq_zero_false_24 hlen_pos hlen_lt
            have hcap_ne : g.cap ≠ 0 := by intro hc0; rw [hc0] at hpts_le; simp at hpts_le
            simp only [hcap_ne, ↓reduceIte]
            refine seq_vm_clean (mid := (blkPl_267).base + 420#64)
              (P_mid := arrayAt (fun bs addr => vecU8 A.repAlloc addr bs) 24 g.ptr (bs :: tl) ∗
                A.pool lim st2 s2 ∗ stackAt (s0.sp - 48#64) allocHookStack ∗
                (memRegion a 184 ∗ ((a + 184#64) ↦₆₄ g.cap) ∗ ((a + 192#64) ↦₆₄ g.ptr) ∗
                 ((a + 200#64) ↦₆₄ BitVec.ofNat 64 (bs :: tl).length) ∗ A.live g.ptr (g.cap.toNat * 24) 8 ∗
                 memRegion (g.ptr + BitVec.ofNat 64 ((bs :: tl).length * 24)) ((g.cap.toNat - (bs :: tl).length) * 24) ∗
                 memRegion (a + 208#64) 16 ∗ optProtoInnerStateJumpTablePlacedExpanded ∗ memRegion (s0.sp - 4192#64) 48 ∗
                 (((s0.sp - 48#64) ↦₆₄ s0.readReg64 .fp) ∗ ((s0.sp - 40#64) ↦₆₄ s0.readReg64 .lr) ∗
                  ((s0.sp - 32#64) ↦₆₄ s0.readReg64 .x22) ∗ ((s0.sp - 24#64) ↦₆₄ s0.readReg64 .x21) ∗
                  ((s0.sp - 16#64) ↦₆₄ s0.readReg64 .x20) ∗ ((s0.sp - 8#64) ↦₆₄ s0.readReg64 .x19))))
              (Q := fun sm => Saved48Preserved s0 sm (s0.sp - 48#64) ∧ AllocCallPreserved s0 sm ∧
                sm.readReg64 .x19 = g.ptr ∧ sm.readReg64 .x20 = g.cap ∧
                sm.readReg64 .x21 = BitVec.ofNat 64 (bs :: tl).length ∧ sm.readReg64 .x22 = g.ptr + 8#64) ?_ ?_
            · by_vm_steps (
                wp_steps
                refine align_pre_vm (by sep_ac_rfl) ?_
                wp_done)
            · intro s_loop hpc_loop hrun_loop hvm_loop ⟨hpres_loop, hacp_loop, hx19_loop, hx20_loop, hx21_loop, hx22_loop⟩
              rw [← A.pool_of_vmPreserved hvm_loop]
              refine SepWP.mono
                (hloop s0 (s0.sp - 48#64) g.ptr g.cap hfsp_align (bs :: tl) g.ptr st2 s_loop _
                  (List.cons_ne_nil _ _) hlen_lt hpc_loop hrun_loop hpres_loop hacp_loop hx19_loop hx20_loop hx21_loop hx22_loop)
                fun sf_l _Pf_l _ _ ⟨evs_l, hevs_l, hp_l, hq_l⟩ => ?_
              refine ⟨evs_l, hevs_l, Entails.trans hp_l ?_, hq_l⟩
              have hsplit : g.cap.toNat * 24 = (bs :: tl).length * 24 + (g.cap.toNat - (bs :: tl).length) * 24 := by
                rw [← Nat.add_mul]; congr 1; omega
              have hbound : (bs :: tl).length * 24 + (g.cap.toNat - (bs :: tl).length) * 24 ≤ 2 ^ 64 := by rw [← hsplit]; omega
              have hrejoin : memRegion g.ptr ((bs :: tl).length * 24) ∗
                  memRegion (g.ptr + BitVec.ofNat 64 ((bs :: tl).length * 24)) ((g.cap.toNat - (bs :: tl).length) * 24) ⊢
                  memRegion g.ptr (g.cap.toNat * 24) := by
                rw [hsplit, ProofLib.memRegion_split g.ptr ((bs :: tl).length * 24) ((g.cap.toNat - (bs :: tl).length) * 24) hbound]
                exact Entails.refl _
              refine Entails.trans (Entails.of_eq (by sep_ac_rfl))
                (Entails.trans (sepConj_mono_left hrejoin) (Entails.of_eq (by sep_ac_rfl)))
        · intro evs3 s3 hevs3 hpc3 hrun3 ⟨⟨hx23_3, hx24_3, hx25_3, hx26_3, hx27_3, hx28_3, hsp_3, htrace_3, hvregs_3⟩, hacp_3, hx19_3, hx20_3⟩
          have ⟨_, _, _, _, _, _, _⟩ := hacp_3
          let st3 := M.stepEvents evs3 st2
          dsimp only [optProtoInnerStateJumpTablePlacedExpanded]
          have hhdr40 : ((a + 184#64) ↦₆₄ g.cap) ∗ ((a + 192#64) ↦₆₄ g.ptr) ∗
              ((a + 200#64) ↦₆₄ BitVec.ofNat 64 pb.pts.length) ∗ memRegion (a + 208#64) 16 ⊢ memRegion (a + 184#64) 40 := by
            rw [← h192, ← h200, ← h208]
            exact protoPolyDecoderHeaders_entails_memRegion_40 (a + 184#64) g.cap g.ptr (BitVec.ofNat 64 pb.pts.length)
          by_cases hc : g.cap = 0
          · have hc_beq : (g.cap == 0#64) = true := by rw [beq_iff_eq]; exact hc
            simp only [hc, ↓reduceIte, emp_sepConj, sepConj_emp] at hx20_3 hhdr40 ⊢
            refine sepWP_close_drop
              (fun sf' => memRegion a 224 ∗ optProtoInnerStateJumpTablePlacedAt ∗
                A.pool lim st3 sf' ∗ stackAt s0.sp dropStack96)
              ?_ (fun sf' _Pf hp hsp_f htr_f hacp_f hcs_f => ⟨fun hm => ?_, hsp_f, hcs_f⟩)
            · wp_steps
              refine SepWP.focus_weaken hhdr40 (by sep_focus) ?_
              refine SepWP.focus_weaken hjoin224 (by sep_focus) ?_
              refine SepWP.focus_weaken (stack_restore_96_allocHook s0.sp (s0.readReg64 .fp) (s0.readReg64 .lr)
                (s0.readReg64 .x22) (s0.readReg64 .x21) (s0.readReg64 .x20) (s0.readReg64 .x19)) (by sep_focus) ?_
              dsimp only [optProtoInnerStateJumpTablePlacedAt, optProtoInnerStateJumpTableSym,
                optProtoInnerStateJumpTableBytes]
              refine sepWP_sync_pool s3 (by simp only [wp_norm, arm64_norm]) (by sep_focus) ?_
              wp_done
            · simp only [sepExists_sepConj_left, satisfies_sepExists]
              refine ⟨(evs1 ++ evs2) ++ evs3, ?_⟩
              simp only [sepConj_assoc, satisfies_pure_sepConj]
              refine ⟨⟨htr_f, hacp_f, (hevs1.append hevs2).append hevs3⟩, ?_⟩
              have heq_st : M.stepEvents ((evs1 ++ evs2) ++ evs3) st = st3 := by
                simp only [st3, st2, st1, LibsignalBinary.Heap.AllocCostModel.stepEvents_append]
              rw [heq_st]
              exact Satisfies.mono (Entails.trans (sepConj_mono_left hp) (Entails.of_eq (by sep_ac_rfl))) hm
          · have hc_beq : ¬((g.cap == 0#64) = true) := by rw [beq_iff_eq]; exact hc
            have hlsl := cap_mul_24 hpts_cap_lt
            simp only [hc, ↓reduceIte]
            refine sepWP_close_drop
              (fun sf' => memRegion a 224 ∗ optProtoInnerStateJumpTablePlacedAt ∗
                A.pool lim (M.stepEvents (rustDeallocEvents (g.cap.toNat * 24) 8) st3) sf' ∗
                stackAt s0.sp dropStack96)
              ?_ (fun sf' _Pf hp hsp_f htr_f hacp_f hcs_f => ⟨fun hm => ?_, hsp_f, hcs_f⟩)
            · wp_steps
              refine SepWP.focus_weaken hhdr40 (by sep_focus) ?_
              refine SepWP.focus_weaken hjoin224 (by sep_focus) ?_
              refine SepWP.focus_weaken (stack_restore_96_allocHook s0.sp (s0.readReg64 .fp) (s0.readReg64 .lr)
                (s0.readReg64 .x22) (s0.readReg64 .x21) (s0.readReg64 .x20) (s0.readReg64 .x19)) (by sep_focus) ?_
              refine SepWP.focus_weaken (Entails.of_eq (stackAt_dropStack96_split_bottom s0.sp)) (by sep_focus) ?_
              refine sepWP_sync_pool s3 (by simp only [wp_norm, arm64_norm]) (by sep_focus) ?_
              wp_call hdealloc_fo (g.ptr, g.cap.toNat * 24, 8, st3)
              have hacp_f : AllocCallPreserved s0 sf := hacp_3.trans (by assumption)
              have ⟨_, _, _, _, _, _, _⟩ := hacp_f
              refine SepWP.focus_weaken (Entails.of_eq (stackAt_dropStack96_split_bottom s0.sp).symm) (by sep_focus) ?_
              dsimp only [optProtoInnerStateJumpTablePlacedAt, optProtoInnerStateJumpTableSym,
                optProtoInnerStateJumpTableBytes]
              wp_done
            · simp only [sepExists_sepConj_left, satisfies_sepExists]
              refine ⟨((evs1 ++ evs2) ++ evs3) ++ rustDeallocEvents (g.cap.toNat * 24) 8, ?_⟩
              simp only [sepConj_assoc, satisfies_pure_sepConj]
              refine ⟨⟨htr_f, hacp_f, ((hevs1.append hevs2).append hevs3).append
                (LibsignalBinary.Heap.FreeOnlyEvs.singleton 8 (g.cap.toNat * 24))⟩, ?_⟩
              have heq_st : M.stepEvents (((evs1 ++ evs2) ++ evs3) ++ rustDeallocEvents (g.cap.toNat * 24) 8) st =
                  M.stepEvents (rustDeallocEvents (g.cap.toNat * 24) 8) st3 := by
                simp only [st3, st2, st1, LibsignalBinary.Heap.AllocCostModel.stepEvents_append]
              rw [heq_st]
              exact Satisfies.mono (Entails.trans (sepConj_mono_left hp) (Entails.of_eq (by sep_ac_rfl))) hm


/-! ## Top-Level Block `267` Contract (`Option<V1State.InnerState>`) -/

theorem drop_opt_proto_inner_state_cl_placed_ok [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {ext : String → Option (State → State)}
    (hdealloc : HookSat (Rust.withPanics ext) spqrRustDeallocSym
      (rustCliDeallocBudgetSpec M A lim)) :
    subroutine_ok (lsProg_267 (Rust.withPanics ext)) (lsmpl.base 267)
      (withLsCodeLoaded lsmpl (dropOptProtoInnerStatePlacedSpec M A lim)) := by
  rw [← ls_blockPlacement_base (i := 267)]
  refine subroutine_ok_outcome_intro fun ⟨⟨a, optSt⟩, st⟩ R s0 hpc hrun hpre hsp => ?_
  cases optSt with
  | none =>
    exact drop_opt_proto_inner_state_none_cl.mono_outcome
      (a, st) R s0 hpc hrun hpre hsp fun _ hout => hout
  | some st_v =>
    cases st_v with
    | keysUnsampled s =>
      exact (drop_opt_proto_inner_state_keysUnsampled_cl hdealloc s).mono_outcome
        (a, st) R s0 hpc hrun hpre hsp fun _ hout => hout
    | keysSampled s =>
      exact (drop_opt_proto_inner_state_keysSampled_cl hdealloc s).mono_outcome
        (a, st) R s0 hpc hrun hpre hsp fun _ hout => hout
    | headerSent s =>
      exact (drop_opt_proto_inner_state_headerSent_cl hdealloc s).mono_outcome
        (a, st) R s0 hpc hrun hpre hsp fun _ hout => hout
    | ct1Received s =>
      exact (drop_opt_proto_inner_state_ct1Received_cl hdealloc s).mono_outcome
        (a, st) R s0 hpc hrun hpre hsp fun _ hout => hout
    | ekSentCt1Received s =>
      exact (drop_opt_proto_inner_state_ekSentCt1Received_cl hdealloc s).mono_outcome
        (a, st) R s0 hpc hrun hpre hsp fun _ hout => hout
    | noHeaderReceived s =>
      exact (drop_opt_proto_inner_state_noHeaderReceived_cl hdealloc s).mono_outcome
        (a, st) R s0 hpc hrun hpre hsp fun _ hout => hout
    | headerReceived s =>
      exact (drop_opt_proto_inner_state_headerReceived_cl hdealloc s).mono_outcome
        (a, st) R s0 hpc hrun hpre hsp fun _ hout => hout
    | ct1Sampled s =>
      exact (drop_opt_proto_inner_state_ct1Sampled_cl hdealloc s).mono_outcome
        (a, st) R s0 hpc hrun hpre hsp fun _ hout => hout
    | ekReceivedCt1Sampled s =>
      exact (drop_opt_proto_inner_state_ekReceivedCt1Sampled_cl hdealloc s).mono_outcome
        (a, st) R s0 hpc hrun hpre hsp fun _ hout => hout
    | ct1Acknowledged s =>
      exact (drop_opt_proto_inner_state_ct1Acknowledged_cl hdealloc s).mono_outcome
        (a, st) R s0 hpc hrun hpre hsp fun _ hout => hout
    | ct2Sampled s =>
      exact (drop_opt_proto_inner_state_ct2Sampled_cl hdealloc s).mono_outcome
        (a, st) R s0 hpc hrun hpre hsp fun _ hout => hout

theorem drop_opt_proto_inner_state_cl_blockProgram [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {ext : String → Option (State → State)}
    (hdealloc : HookSat (Rust.withPanics ext) spqrRustDeallocSym
      (rustCliDeallocBudgetSpec M A lim)) :
    subroutine_ok (libsignalSessionLib.blockProgram lsmpl 267 (Rust.withPanics ext)) (lsmpl.base 267)
      (withLsCodeLoaded lsmpl (dropOptProtoInnerStatePlacedSpec M A lim)) :=
  ls_to_blockProgram (drop_opt_proto_inner_state_cl_placed_ok hdealloc)

theorem drop_opt_proto_inner_state_cl_on [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {callerProg : Program} {idx : Nat} {ext : String → Option (State → State)}
    [IsLsBlockProg callerProg idx (Rust.withPanics ext)]
    (hdealloc : HookSat (Rust.withPanics ext) spqrRustDeallocSym
      (rustCliDeallocBudgetSpec M A lim))
    (hidx : idx < 619 := by decide) :
    subroutine_ok callerProg (lsmpl.base 267)
      (withLsCodeLoaded lsmpl (dropOptProtoInnerStatePlacedSpec M A lim)) :=
  ls_subroutine_ok_of_block (drop_opt_proto_inner_state_cl_placed_ok hdealloc) hidx

theorem drop_opt_proto_inner_state_mem_on [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {callerProg : Program} {idx : Nat} {ext : String → Option (State → State)}
    [IsLsBlockProg callerProg idx (Rust.withPanics ext)] {m : Memory}
    (hdealloc : HookSat (Rust.withPanics ext) spqrRustDeallocSym
      (rustCliDeallocBudgetSpec M A lim))
    (hcl : LibsignalCodeLoaded lsmpl m) (hidx : idx < 619 := by decide) :
    subroutine_ok callerProg (lsmpl.base 267)
      (withMemEq m (dropOptProtoInnerStatePlacedSpec M A lim)) :=
  lscall_blk_cl (drop_opt_proto_inner_state_cl_placed_ok hdealloc) hcl hidx

end LibsignalBinary.Proofs.SpqrV1.Drop.ProtoTopClPlacedBudgetAux2
