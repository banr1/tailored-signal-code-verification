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
public import LibsignalBinary.Proofs.SpqrV1.Drop.ProtoTopBudget
public import LibsignalBinary.Proofs.SpqrV1.States.Recv.DropChunkedClPlacedBudget
import LibsignalBinary.Proofs.Common.SharedHelpers
meta import LibsignalBinary.Proofs.Common.SharedHelpers -- shake: keep
import LibsignalBinary.Proofs.Placed.ElfLsRetAddr
import LibsignalBinary.Proofs.SpqrV1.Alloc.SpqrAllocCodeSym
import ProofLib.SepLogic.WP.Apply
import ProofLib.SepLogic.WPp
import GeneratedLean.LibsignalSessionObj

/-!
# Budget-Threaded Code-Loaded Non-Looping Variants of `Option<InnerState>` (Block `267`)

Proves the shared `withLsCodeLoaded` prologue step (`+0` to `+16`) and the ten non-looping
variant contracts of Block `267` under `RustCliAllocBudget M` (`FreeOnlyEvs`).
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
  DropOptProtoInnerStateGhost DropProtoPqRatchetStateGhost Saved48Preserved add_24_add_8
  auth64HeadersAt auth64HeadersAt_entails_memRegion_56 auth8HeadersAt
  auth8HeadersAt_entails_memRegion_56 cap_add_one_beq_zero_false cap_add_three_beq_zero_false
  cap_add_two_beq_zero_false cap_lsl7_sub_lsl4 cap_mul_24 cap_ne_zero_lt_one_false
  cap_ne_zero_slt_one_false cap_xor_highBit_cc_11_false chainPBAt_entails_dealloc
  chainPBHeaders_entails_memRegion_80 cons_len_mul ct1SentToCt1SentEkReceived dropStack32
  dropStack48 dropStack96 header_cells_entails_memRegion_24 keysSampledToCt1Received none2Cap
  none2Cap_add_two_beq_zero none3Cap' noneCap_add_two_beq_zero ofNat_add_one_beq_one_false_24
  ofNat_beq_zero_false_24 ofNat_succ_eq_add_one optChainPBAt_none_entails_memRegion_80
  optProtoAuthenticatorAt optProtoAuthenticatorAt_64_none_entails_memRegion_56
  optProtoAuthenticatorAt_8_none_entails_memRegion_56 optProtoAuthenticatorAt_none
  optProtoAuthenticatorAt_some optProtoInnerStateAt optProtoInnerStateAt_expose_word
  optProtoInnerStateAt_unexpose_word optProtoInnerStateJumpTableBytes
  optProtoInnerStateJumpTablePlacedAt optProtoInnerStateJumpTablePlacedExpanded
  optProtoInnerStateJumpTableSym optProtoInnerStateSize optProtoInnerStateTaggedRest
  optProtoInnerState_none_entails_224 optProtoPolyDecoder_none_entails_memRegion_40
  optProtoPolyEncoder_none_entails_memRegion_56 optProtoPolynomialDecoderAt_none'
  optProtoPolynomialDecoderAt_some' optProtoPolynomialEncoderAt_none'
  optProtoPolynomialEncoderAt_some' optProtoPqRatchetInnerAt
  optProtoPqRatchetInnerAt_none_entails_memRegion_224 optProtoUnchunkedCt1SentAt_none
  optProtoUnchunkedCt1SentAt_some optProtoUnchunkedCt1SentEkReceivedAt_none
  optProtoUnchunkedCt1SentEkReceivedAt_none_entails_memRegion_128
  optProtoUnchunkedCt1SentEkReceivedAt_some optProtoUnchunkedCt2SentAt
  optProtoUnchunkedKeysUnsampledAt
  optProtoUnchunkedNoHeaderReceivedAt_none_entails_memRegion_56
  optVersionNegotiationPBAt_none_entails_memRegion_48 protoAuthenticatorAt_entails_dealloc
  protoChunkedCt1AcknowledgedAt protoChunkedCt1ReceivedAt protoChunkedCt1SampledAt
  protoChunkedCt2SampledAt protoChunkedEkReceivedCt1SampledAt protoChunkedEkSentCt1ReceivedAt
  protoChunkedHeaderReceivedAt protoChunkedHeaderSentAt
  protoChunkedKeysSampledAt_eq_ct1ReceivedAt protoChunkedKeysUnsampledAt
  protoChunkedNoHeaderReceivedAt protoInnerStateAt protoPolyDecoderAt_entails_dealloc
  protoPolyDecoderHeaders_entails_memRegion_40 protoPolynomialEncoderAt_expose_cap
  protoPolynomialEncoderAt_unexpose_cap protoPqRatchetStateAt protoPqRatchetStateSize
  protoUnchunkedCt1SentAt_eq_ct1SentEkReceived protoUnchunkedCt1SentEkReceivedAt
  protoUnchunkedCt1SentEkReceivedAt_expose_cap protoUnchunkedCt1SentEkReceivedAt_unexpose_cap
  protoUnchunkedCt1SentEkReceivedSize protoUnchunkedCt2SentAt protoUnchunkedKeysUnsampledAt
  sep_pull_body sep_push_body sep_rejoin_loop stackAt_dropStack96_split
  stackAt_dropStack96_split_48 stackAt_dropStack96_split_bottom stackAt_sub48_eq_dropStack48
  stackAt_sub48_split_32 stack_restore_96_allocHook tag_and_two_regions_entails_224
  tail_len_mul_lt twoVecHeadersAt_64_eq twoVecHeadersAt_8_eq vecCapPtrDealloc
  vecU8_entails_capPtr_dealloc versionNegotiationPBAt_entails_dealloc
  vnHeader_entails_memRegion_48
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
open LibsignalBinary.Proofs.SpqrV1.Drop.ProtoChunked1Budget (
  dropProtoChunkedCt1ReceivedSpec dropProtoChunkedEkSentCt1ReceivedSpec
  dropProtoChunkedHeaderReceivedSpec dropProtoChunkedHeaderSentSpec
  dropProtoChunkedNoHeaderReceivedSpec
)
open LibsignalBinary.Proofs.SpqrV1.Drop.ProtoChunked2BudgetAux (
  align_pre_st align_pre_vm deallocFreeOnlySpec sepWP_evs_dealloc sepWP_evs_nil seq_clean_evs
  seq_vm_clean subroutine_ok_deallocFreeOnly
)
open LibsignalBinary.Proofs.SpqrV1.Drop.ProtoChunkedClPlacedBudget (
  drop_proto_chunked_ct1_received_mem_on drop_proto_chunked_ek_sent_ct1_received_mem_on
  drop_proto_chunked_header_received_mem_on drop_proto_chunked_header_sent_mem_on
  drop_proto_chunked_no_header_received_mem_on drop_proto_unchunked_ct1_sent_ek_received_mem_on
)
open LibsignalBinary.Proofs.SpqrV1.Drop.ProtoChunkedClPlacedBudgetAux (
  seq_clean_evs_lscl
)
open LibsignalBinary.Proofs.SpqrV1.Drop.ProtoPolyBudget (
  dropProtoPolyEncoderSpec
)
open LibsignalBinary.Proofs.SpqrV1.Drop.ProtoTop2BudgetAux (
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
open LibsignalBinary.Proofs.SpqrV1.Drop.UnchunkedBudget (
  dropProtoUnchunkedCt1SentEkReceivedSpec
)
open LibsignalBinary.Proofs.SpqrV1.States.Recv.DropChunkedClPlacedBudget (
  drop_glue_proto_poly_encoder_mem_on
)
open LibsignalBinary.Proofs.SpqrV1.States.Recv.DropChunkedClPlacedBudgetAux (
  seq_vm_clean_lscl subroutine_ok_withLsCodeLoaded_intro
)

namespace LibsignalBinary.Proofs.SpqrV1.Drop.ProtoTopClPlacedBudgetAux1

open Arm64 ProofLib
open ProofLib.ProgramReflection

attribute [local irreducible] Program.fetch Program.externAt? Program.fnOff
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero
attribute [local simp, local arm64_norm] none2Cap_add_two_beq_zero noneCap_add_two_beq_zero

theorem jt_placed_eq_expanded [LibsignalPlacement] :
    optProtoInnerStateJumpTablePlacedAt = optProtoInnerStateJumpTablePlacedExpanded := by
  simp only [optProtoInnerStateJumpTablePlacedAt, optProtoInnerStateJumpTableBytes,
    optProtoInnerStateJumpTablePlacedExpanded, pointsToBytesRO_cons, pointsToBytesRO_nil,
    sepConj_emp, BitVec.add_assoc, wp_norm, arm64_norm]

/-- Shared `withLsCodeLoaded` prologue step for Block `267` from `+0` to `+16`. -/
theorem proto_top_prologue_16_lscl [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {H : String → Option (State → State)} {target : BitVec 64}
    {s0 : State} {a : BitVec 64} {st : M.σ} {Body : SepProp}
    {post : State → SepProp → Prop}
    (hcl : LibsignalCodeLoaded lsmpl s0.mem)
    (hpc0 : s0.pc = (blkPl_267).base)
    (hrun0 : s0.status = .Running)
    (hsp_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hx0 : s0.readReg64 .x0 = a)
    (hcont : ∀ sv : State,
      sv.pc = (blkPl_267).base + 16#64 →
      sv.status = .Running →
      LibsignalCodeLoaded lsmpl sv.mem →
      Saved48Preserved s0 sv (s0.sp - 48#64) →
      AllocCallPreserved s0 sv →
      sv.readReg64 .x0 = a →
      SepWP ((blkPC_267).rebase (blkPl_267).base H) target sv
        (Body ∗ optProtoInnerStateJumpTablePlacedAt ∗ A.pool lim st sv ∗
          (memRegion (s0.sp - 4192#64) 48 ∗ stackAt (s0.sp - 48#64) allocHookStack) ∗
          (((s0.sp - 48#64) ↦₆₄ s0.readReg64 .fp) ∗ ((s0.sp - 40#64) ↦₆₄ s0.readReg64 .lr) ∗
           ((s0.sp - 32#64) ↦₆₄ s0.readReg64 .x22) ∗ ((s0.sp - 24#64) ↦₆₄ s0.readReg64 .x21) ∗
           ((s0.sp - 16#64) ↦₆₄ s0.readReg64 .x20) ∗ ((s0.sp - 8#64) ↦₆₄ s0.readReg64 .x19)))
        post) :
    SepWP ((blkPC_267).rebase (blkPl_267).base H) target s0
      (Body ∗ optProtoInnerStateJumpTablePlacedAt ∗ A.pool lim st s0 ∗ stackAt s0.sp dropStack96)
      post := by
  nth_rw 1 [stackAt_dropStack96_split s0.sp]; cells_unfold; wp_pull_exists
  rename_i v_fp v_lr v_x22 v_x21 v_x20 v_x19
  refine seq_vm_clean_lscl hcl (mid := (blkPl_267).base + 16#64)
    (P_mid := Body ∗ optProtoInnerStateJumpTablePlacedAt ∗ A.pool lim st s0 ∗
      (memRegion (s0.sp - 4192#64) 48 ∗ stackAt (s0.sp - 48#64) allocHookStack) ∗
      (((s0.sp - 48#64) ↦₆₄ s0.readReg64 .fp) ∗ ((s0.sp - 40#64) ↦₆₄ s0.readReg64 .lr) ∗
       ((s0.sp - 32#64) ↦₆₄ s0.readReg64 .x22) ∗ ((s0.sp - 24#64) ↦₆₄ s0.readReg64 .x21) ∗
       ((s0.sp - 16#64) ↦₆₄ s0.readReg64 .x20) ∗ ((s0.sp - 8#64) ↦₆₄ s0.readReg64 .x19)))
    (Q := fun sv => Saved48Preserved s0 sv (s0.sp - 48#64) ∧ AllocCallPreserved s0 sv ∧
      sv.readReg64 .x0 = a)
    ?_ ?_
  · by_vm_steps (
      wp_steps
      refine align_pre_vm (by
        simp only [Reg.fp, Reg.lr, Reg.x19, Reg.x20, Reg.x21, Reg.x22, wp_norm, arm64_norm]) ?_
      wp_done)
  · intro sv hpcv hrunv hcl_v hvmv ⟨hpres_v, hacp_v, hx0_v⟩
    rw [← A.pool_of_vmPreserved hvmv]
    exact hcont sv hpcv hrunv hcl_v hpres_v hacp_v hx0_v

/-! ## Leaf Variants (`none`, `keysUnsampled`) -/

theorem drop_opt_proto_inner_state_none_cl [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {ext : String → Option (State → State)} :
    subroutine_ok ((blkPC_267).rebase (blkPl_267).base (Rust.withPanics ext)) (blkPl_267).base
      (withLsCodeLoaded lsmpl (dropOptProtoInnerStatePlacedVariantSpec M A lim none)) :=
  subroutine_ok_withLsCodeLoaded_of_plain drop_opt_proto_inner_state_none_placed

theorem drop_opt_proto_inner_state_keysUnsampled_cl [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {ext : String → Option (State → State)}
    (hdealloc : HookSat (Rust.withPanics ext) spqrRustDeallocSym
      (rustCliDeallocBudgetSpec M A lim))
    (st_pb : V1State.Chunked.KeysUnsampled) :
    subroutine_ok ((blkPC_267).rebase (blkPl_267).base (Rust.withPanics ext)) (blkPl_267).base
      (withLsCodeLoaded lsmpl (dropOptProtoInnerStatePlacedVariantSpec M A lim (some (.keysUnsampled st_pb)))) :=
  subroutine_ok_withLsCodeLoaded_of_plain
    (drop_opt_proto_inner_state_keysUnsampled_placed
      (spqr_hook_ok_of_mem (prog := lsProg_267 (Rust.withPanics ext)) hdealloc) st_pb)

/-! ## Tail-Call Variants of Block `267` -/

theorem drop_opt_proto_inner_state_keysSampled_cl [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {ext : String → Option (State → State)}
    (hdealloc : HookSat (Rust.withPanics ext) spqrRustDeallocSym
      (rustCliDeallocBudgetSpec M A lim))
    (st_pb : V1State.Chunked.KeysSampled) :
    subroutine_ok ((blkPC_267).rebase (blkPl_267).base (Rust.withPanics ext)) (blkPl_267).base
      (withLsCodeLoaded lsmpl (dropOptProtoInnerStatePlacedVariantSpec M A lim (some (.keysSampled st_pb)))) := by
  apply subroutine_ok_withLsCodeLoaded_intro; intro m hcl
  dsimp only [withMemEq, dropOptProtoInnerStatePlacedVariantSpec, optProtoInnerStateSize, BitVec.ofNat_eq_ofNat] at *
  wp_init x_st s0; rcases x_st with ⟨a, st⟩
  have _hlr0_gpr : LsRetAddr624 (s0.readReg64 (Reg.gpr 30#5)) := by assumption
  have hx0 : s0.readReg64 .x0 = a := by assumption
  have hm_eq : s0.mem = m := by assumption
  subst hm_eq
  refine proto_top_prologue_16_lscl hcl (by assumption) (by assumption) (by assumption) hx0
    fun sv hpcv hrunv hcl_v hpres_v hacp_v hx0_v => ?_
  conv => arg 4; dsimp only [optProtoInnerStateAt, protoInnerStateAt]
  rw [protoChunkedKeysSampledAt_eq_ct1ReceivedAt]
  rcases hpres_v with ⟨hx23_v, hx24_v, hx25_v, hx26_v, hx27_v, hx28_v, hsp_v, htrace_v, hvregs_v⟩
  have ⟨_, _, _, _, _, _, _⟩ := hacp_v
  conv => arg 4; dsimp only [optProtoInnerStateAt, protoInnerStateAt,
    optProtoInnerStateJumpTablePlacedAt, optProtoInnerStateJumpTableSym,
    optProtoInnerStateJumpTableBytes]
  apply sepWP_seq_lscl hcl_v (mid := lsmpl.base 282)
  wp_steps
  apply SepWP.done (by wp_norm_lhs) (by wp_norm_lhs); intro hclc
  have hcallee := drop_proto_chunked_ct1_received_mem_on (callerProg := lsProg_267 (Rust.withPanics ext)) hdealloc hclc
  dsimp only [lsProg_267, withMemEq, dropProtoChunkedCt1ReceivedSpec, BitVec.ofNat_eq_ofNat] at hcallee
  refine SepWP.focus_weaken (stack_restore_96_allocHook s0.sp (s0.readReg64 .fp) (s0.readReg64 .lr)
    (s0.readReg64 .x22) (s0.readReg64 .x21) (s0.readReg64 .x20) (s0.readReg64 .x19)) (by sep_focus) ?_
  refine SepWP.focus_weaken (Entails.of_eq (stackAt_dropStack96_split_48 s0.sp)) (by sep_focus) ?_
  refine sepWP_sync_pool sv (by simp only [wp_norm, arm64_norm]) (by sep_focus) ?_
  wp_call hcallee (⟨a + 8#64, (keysSampledToCt1Received st_pb)⟩, st)
  have hevs_w : FreeOnlyEvs w := by assumption
  have hacp_f : AllocCallPreserved s0 sf := hacp_v.trans (by assumption)
  have ⟨_, _, _, _, _, _, _⟩ := hacp_f
  refine SepWP.focus_weaken (Entails.of_eq (stackAt_dropStack96_split_48 s0.sp).symm) (by sep_focus) ?_
  refine SepWP.focus_weaken (tag_and_two_regions_entails_224 a 0x8000000000000001#64 160 56 168#64
    (BitVec.add_assoc a 8#64 (BitVec.ofNat 64 160)).symm rfl) (by sep_focus) ?_
  refine sepWP_close_drop
    (fun sf' => memRegion a 224 ∗ optProtoInnerStateJumpTablePlacedExpanded ∗
      A.pool lim (M.stepEvents w st) sf' ∗ stackAt s0.sp dropStack96)
    (by dsimp only [optProtoInnerStateJumpTablePlacedExpanded]; wp_done)
    (fun sf' _Pf hp hsp_f htr_f hacp_f' hcs_f => ⟨fun hm => ?_, hsp_f, hcs_f⟩)
  rw [← jt_placed_eq_expanded] at hp
  simp only [sepExists_sepConj_left, satisfies_sepExists]
  refine ⟨w, ?_⟩
  simp only [sepConj_assoc, satisfies_pure_sepConj]
  exact ⟨⟨htr_f, hacp_f', hevs_w⟩,
    Satisfies.mono (Entails.trans (sepConj_mono_left hp) (Entails.of_eq (by sep_ac_rfl))) hm⟩

theorem drop_opt_proto_inner_state_headerSent_cl [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {ext : String → Option (State → State)}
    (hdealloc : HookSat (Rust.withPanics ext) spqrRustDeallocSym
      (rustCliDeallocBudgetSpec M A lim))
    (st_pb : V1State.Chunked.HeaderSent) :
    subroutine_ok ((blkPC_267).rebase (blkPl_267).base (Rust.withPanics ext)) (blkPl_267).base
      (withLsCodeLoaded lsmpl (dropOptProtoInnerStatePlacedVariantSpec M A lim (some (.headerSent st_pb)))) := by
  apply subroutine_ok_withLsCodeLoaded_intro; intro m hcl
  dsimp only [withMemEq, dropOptProtoInnerStatePlacedVariantSpec, optProtoInnerStateSize, BitVec.ofNat_eq_ofNat] at *
  wp_init x_st s0; rcases x_st with ⟨a, st⟩
  have _hlr0_gpr : LsRetAddr624 (s0.readReg64 (Reg.gpr 30#5)) := by assumption
  have hx0 : s0.readReg64 .x0 = a := by assumption
  have hm_eq : s0.mem = m := by assumption
  subst hm_eq
  refine proto_top_prologue_16_lscl hcl (by assumption) (by assumption) (by assumption) hx0
    fun sv hpcv hrunv hcl_v hpres_v hacp_v hx0_v => ?_
  rcases hpres_v with ⟨hx23_v, hx24_v, hx25_v, hx26_v, hx27_v, hx28_v, hsp_v, htrace_v, hvregs_v⟩
  have ⟨_, _, _, _, _, _, _⟩ := hacp_v
  conv => arg 4; dsimp only [optProtoInnerStateAt, protoInnerStateAt,
    optProtoInnerStateJumpTablePlacedAt, optProtoInnerStateJumpTableSym,
    optProtoInnerStateJumpTableBytes]
  apply sepWP_seq_lscl hcl_v (mid := lsmpl.base 281)
  wp_steps
  apply SepWP.done (by wp_norm_lhs) (by wp_norm_lhs); intro hclc
  have hcallee := drop_proto_chunked_header_sent_mem_on (callerProg := lsProg_267 (Rust.withPanics ext)) hdealloc hclc
  dsimp only [lsProg_267, withMemEq, dropProtoChunkedHeaderSentSpec, BitVec.ofNat_eq_ofNat] at hcallee
  refine SepWP.focus_weaken (stack_restore_96_allocHook s0.sp (s0.readReg64 .fp) (s0.readReg64 .lr)
    (s0.readReg64 .x22) (s0.readReg64 .x21) (s0.readReg64 .x20) (s0.readReg64 .x19)) (by sep_focus) ?_
  refine sepWP_sync_pool sv (by simp only [wp_norm, arm64_norm]) (by sep_focus) ?_
  wp_call hcallee (⟨a + 8#64, st_pb⟩, st)
  have hevs_w : FreeOnlyEvs w := by assumption
  have hacp_f : AllocCallPreserved s0 sf := hacp_v.trans (by assumption)
  have ⟨_, _, _, _, _, _, _⟩ := hacp_f
  refine SepWP.focus_weaken (tag_and_two_regions_entails_224 a 0x8000000000000002#64 176 40 184#64
    (BitVec.add_assoc a 8#64 (BitVec.ofNat 64 176)).symm rfl) (by sep_focus) ?_
  refine sepWP_close_drop
    (fun sf' => memRegion a 224 ∗ optProtoInnerStateJumpTablePlacedExpanded ∗
      A.pool lim (M.stepEvents w st) sf' ∗ stackAt s0.sp dropStack96)
    (by dsimp only [optProtoInnerStateJumpTablePlacedExpanded]; wp_done)
    (fun sf' _Pf hp hsp_f htr_f hacp_f' hcs_f => ⟨fun hm => ?_, hsp_f, hcs_f⟩)
  rw [← jt_placed_eq_expanded] at hp
  simp only [sepExists_sepConj_left, satisfies_sepExists]
  refine ⟨w, ?_⟩
  simp only [sepConj_assoc, satisfies_pure_sepConj]
  exact ⟨⟨htr_f, hacp_f', hevs_w⟩,
    Satisfies.mono (Entails.trans (sepConj_mono_left hp) (Entails.of_eq (by sep_ac_rfl))) hm⟩

theorem drop_opt_proto_inner_state_ct1Received_cl [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {ext : String → Option (State → State)}
    (hdealloc : HookSat (Rust.withPanics ext) spqrRustDeallocSym
      (rustCliDeallocBudgetSpec M A lim))
    (st_pb : V1State.Chunked.Ct1Received) :
    subroutine_ok ((blkPC_267).rebase (blkPl_267).base (Rust.withPanics ext)) (blkPl_267).base
      (withLsCodeLoaded lsmpl (dropOptProtoInnerStatePlacedVariantSpec M A lim (some (.ct1Received st_pb)))) := by
  apply subroutine_ok_withLsCodeLoaded_intro; intro m hcl
  dsimp only [withMemEq, dropOptProtoInnerStatePlacedVariantSpec, optProtoInnerStateSize, BitVec.ofNat_eq_ofNat] at *
  wp_init x_st s0; rcases x_st with ⟨a, st⟩
  have _hlr0_gpr : LsRetAddr624 (s0.readReg64 (Reg.gpr 30#5)) := by assumption
  have hx0 : s0.readReg64 .x0 = a := by assumption
  have hm_eq : s0.mem = m := by assumption
  subst hm_eq
  refine proto_top_prologue_16_lscl hcl (by assumption) (by assumption) (by assumption) hx0
    fun sv hpcv hrunv hcl_v hpres_v hacp_v hx0_v => ?_
  rcases hpres_v with ⟨hx23_v, hx24_v, hx25_v, hx26_v, hx27_v, hx28_v, hsp_v, htrace_v, hvregs_v⟩
  have ⟨_, _, _, _, _, _, _⟩ := hacp_v
  conv => arg 4; dsimp only [optProtoInnerStateAt, protoInnerStateAt,
    optProtoInnerStateJumpTablePlacedAt, optProtoInnerStateJumpTableSym,
    optProtoInnerStateJumpTableBytes]
  apply sepWP_seq_lscl hcl_v (mid := lsmpl.base 282)
  wp_steps
  apply SepWP.done (by wp_norm_lhs) (by wp_norm_lhs); intro hclc
  have hcallee := drop_proto_chunked_ct1_received_mem_on (callerProg := lsProg_267 (Rust.withPanics ext)) hdealloc hclc
  dsimp only [lsProg_267, withMemEq, dropProtoChunkedCt1ReceivedSpec, BitVec.ofNat_eq_ofNat] at hcallee
  refine SepWP.focus_weaken (stack_restore_96_allocHook s0.sp (s0.readReg64 .fp) (s0.readReg64 .lr)
    (s0.readReg64 .x22) (s0.readReg64 .x21) (s0.readReg64 .x20) (s0.readReg64 .x19)) (by sep_focus) ?_
  refine SepWP.focus_weaken (Entails.of_eq (stackAt_dropStack96_split_48 s0.sp)) (by sep_focus) ?_
  refine sepWP_sync_pool sv (by simp only [wp_norm, arm64_norm]) (by sep_focus) ?_
  wp_call hcallee (⟨a + 8#64, st_pb⟩, st)
  have hevs_w : FreeOnlyEvs w := by assumption
  have hacp_f : AllocCallPreserved s0 sf := hacp_v.trans (by assumption)
  have ⟨_, _, _, _, _, _, _⟩ := hacp_f
  refine SepWP.focus_weaken (Entails.of_eq (stackAt_dropStack96_split_48 s0.sp).symm) (by sep_focus) ?_
  refine SepWP.focus_weaken (tag_and_two_regions_entails_224 a 0x8000000000000003#64 160 56 168#64
    (BitVec.add_assoc a 8#64 (BitVec.ofNat 64 160)).symm rfl) (by sep_focus) ?_
  refine sepWP_close_drop
    (fun sf' => memRegion a 224 ∗ optProtoInnerStateJumpTablePlacedExpanded ∗
      A.pool lim (M.stepEvents w st) sf' ∗ stackAt s0.sp dropStack96)
    (by dsimp only [optProtoInnerStateJumpTablePlacedExpanded]; wp_done)
    (fun sf' _Pf hp hsp_f htr_f hacp_f' hcs_f => ⟨fun hm => ?_, hsp_f, hcs_f⟩)
  rw [← jt_placed_eq_expanded] at hp
  simp only [sepExists_sepConj_left, satisfies_sepExists]
  refine ⟨w, ?_⟩
  simp only [sepConj_assoc, satisfies_pure_sepConj]
  exact ⟨⟨htr_f, hacp_f', hevs_w⟩,
    Satisfies.mono (Entails.trans (sepConj_mono_left hp) (Entails.of_eq (by sep_ac_rfl))) hm⟩

theorem drop_opt_proto_inner_state_ekSentCt1Received_cl [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {ext : String → Option (State → State)}
    (hdealloc : HookSat (Rust.withPanics ext) spqrRustDeallocSym
      (rustCliDeallocBudgetSpec M A lim))
    (st_pb : V1State.Chunked.EkSentCt1Received) :
    subroutine_ok ((blkPC_267).rebase (blkPl_267).base (Rust.withPanics ext)) (blkPl_267).base
      (withLsCodeLoaded lsmpl (dropOptProtoInnerStatePlacedVariantSpec M A lim (some (.ekSentCt1Received st_pb)))) := by
  apply subroutine_ok_withLsCodeLoaded_intro; intro m hcl
  dsimp only [withMemEq, dropOptProtoInnerStatePlacedVariantSpec, optProtoInnerStateSize, BitVec.ofNat_eq_ofNat] at *
  wp_init x_st s0; rcases x_st with ⟨a, st⟩
  have _hlr0_gpr : LsRetAddr624 (s0.readReg64 (Reg.gpr 30#5)) := by assumption
  have hx0 : s0.readReg64 .x0 = a := by assumption
  have hm_eq : s0.mem = m := by assumption
  subst hm_eq
  refine proto_top_prologue_16_lscl hcl (by assumption) (by assumption) (by assumption) hx0
    fun sv hpcv hrunv hcl_v hpres_v hacp_v hx0_v => ?_
  rcases hpres_v with ⟨hx23_v, hx24_v, hx25_v, hx26_v, hx27_v, hx28_v, hsp_v, htrace_v, hvregs_v⟩
  have ⟨_, _, _, _, _, _, _⟩ := hacp_v
  conv => arg 4; dsimp only [optProtoInnerStateAt, protoInnerStateAt,
    optProtoInnerStateJumpTablePlacedAt, optProtoInnerStateJumpTableSym,
    optProtoInnerStateJumpTableBytes]
  apply sepWP_seq_lscl hcl_v (mid := lsmpl.base 285)
  wp_steps
  apply SepWP.done (by wp_norm_lhs) (by wp_norm_lhs); intro hclc
  have hcallee := drop_proto_chunked_ek_sent_ct1_received_mem_on (callerProg := lsProg_267 (Rust.withPanics ext)) hdealloc hclc
  dsimp only [lsProg_267, withMemEq, dropProtoChunkedEkSentCt1ReceivedSpec, BitVec.ofNat_eq_ofNat] at hcallee
  refine SepWP.focus_weaken (stack_restore_96_allocHook s0.sp (s0.readReg64 .fp) (s0.readReg64 .lr)
    (s0.readReg64 .x22) (s0.readReg64 .x21) (s0.readReg64 .x20) (s0.readReg64 .x19)) (by sep_focus) ?_
  refine SepWP.focus_weaken (Entails.of_eq (stackAt_dropStack96_split_48 s0.sp)) (by sep_focus) ?_
  refine sepWP_sync_pool sv (by simp only [wp_norm, arm64_norm]) (by sep_focus) ?_
  wp_call hcallee (⟨a + 8#64, st_pb⟩, st)
  have hevs_w : FreeOnlyEvs w := by assumption
  have hacp_f : AllocCallPreserved s0 sf := hacp_v.trans (by assumption)
  have ⟨_, _, _, _, _, _, _⟩ := hacp_f
  refine SepWP.focus_weaken (Entails.of_eq (stackAt_dropStack96_split_48 s0.sp).symm) (by sep_focus) ?_
  refine SepWP.focus_weaken (tag_and_two_regions_entails_224 a 0x8000000000000004#64 144 72 152#64
    (BitVec.add_assoc a 8#64 (BitVec.ofNat 64 144)).symm rfl) (by sep_focus) ?_
  refine sepWP_close_drop
    (fun sf' => memRegion a 224 ∗ optProtoInnerStateJumpTablePlacedExpanded ∗
      A.pool lim (M.stepEvents w st) sf' ∗ stackAt s0.sp dropStack96)
    (by dsimp only [optProtoInnerStateJumpTablePlacedExpanded]; wp_done)
    (fun sf' _Pf hp hsp_f htr_f hacp_f' hcs_f => ⟨fun hm => ?_, hsp_f, hcs_f⟩)
  rw [← jt_placed_eq_expanded] at hp
  simp only [sepExists_sepConj_left, satisfies_sepExists]
  refine ⟨w, ?_⟩
  simp only [sepConj_assoc, satisfies_pure_sepConj]
  exact ⟨⟨htr_f, hacp_f', hevs_w⟩,
    Satisfies.mono (Entails.trans (sepConj_mono_left hp) (Entails.of_eq (by sep_ac_rfl))) hm⟩

theorem drop_opt_proto_inner_state_noHeaderReceived_cl [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {ext : String → Option (State → State)}
    (hdealloc : HookSat (Rust.withPanics ext) spqrRustDeallocSym
      (rustCliDeallocBudgetSpec M A lim))
    (st_pb : V1State.Chunked.NoHeaderReceived) :
    subroutine_ok ((blkPC_267).rebase (blkPl_267).base (Rust.withPanics ext)) (blkPl_267).base
      (withLsCodeLoaded lsmpl (dropOptProtoInnerStatePlacedVariantSpec M A lim (some (.noHeaderReceived st_pb)))) := by
  apply subroutine_ok_withLsCodeLoaded_intro; intro m hcl
  dsimp only [withMemEq, dropOptProtoInnerStatePlacedVariantSpec, optProtoInnerStateSize, BitVec.ofNat_eq_ofNat] at *
  wp_init x_st s0; rcases x_st with ⟨a, st⟩
  have _hlr0_gpr : LsRetAddr624 (s0.readReg64 (Reg.gpr 30#5)) := by assumption
  have hx0 : s0.readReg64 .x0 = a := by assumption
  have hm_eq : s0.mem = m := by assumption
  subst hm_eq
  refine proto_top_prologue_16_lscl hcl (by assumption) (by assumption) (by assumption) hx0
    fun sv hpcv hrunv hcl_v hpres_v hacp_v hx0_v => ?_
  rcases hpres_v with ⟨hx23_v, hx24_v, hx25_v, hx26_v, hx27_v, hx28_v, hsp_v, htrace_v, hvregs_v⟩
  have ⟨_, _, _, _, _, _, _⟩ := hacp_v
  conv => arg 4; dsimp only [optProtoInnerStateAt, protoInnerStateAt,
    optProtoInnerStateJumpTablePlacedAt, optProtoInnerStateJumpTableSym,
    optProtoInnerStateJumpTableBytes]
  apply sepWP_seq_lscl hcl_v (mid := lsmpl.base 284)
  wp_steps
  apply SepWP.done (by wp_norm_lhs) (by wp_norm_lhs); intro hclc
  have hcallee := drop_proto_chunked_no_header_received_mem_on (callerProg := lsProg_267 (Rust.withPanics ext)) hdealloc hclc
  dsimp only [lsProg_267, withMemEq, dropProtoChunkedNoHeaderReceivedSpec, BitVec.ofNat_eq_ofNat] at hcallee
  refine SepWP.focus_weaken (stack_restore_96_allocHook s0.sp (s0.readReg64 .fp) (s0.readReg64 .lr)
    (s0.readReg64 .x22) (s0.readReg64 .x21) (s0.readReg64 .x20) (s0.readReg64 .x19)) (by sep_focus) ?_
  refine SepWP.focus_weaken (Entails.of_eq (stackAt_dropStack96_split_48 s0.sp)) (by sep_focus) ?_
  refine sepWP_sync_pool sv (by simp only [wp_norm, arm64_norm]) (by sep_focus) ?_
  wp_call hcallee (⟨a + 8#64, st_pb⟩, st)
  have hevs_w : FreeOnlyEvs w := by assumption
  have hacp_f : AllocCallPreserved s0 sf := hacp_v.trans (by assumption)
  have ⟨_, _, _, _, _, _, _⟩ := hacp_f
  refine SepWP.focus_weaken (Entails.of_eq (stackAt_dropStack96_split_48 s0.sp).symm) (by sep_focus) ?_
  refine SepWP.focus_weaken (tag_and_two_regions_entails_224 a 0x8000000000000005#64 96 120 104#64
    (BitVec.add_assoc a 8#64 (BitVec.ofNat 64 96)).symm rfl) (by sep_focus) ?_
  refine sepWP_close_drop
    (fun sf' => memRegion a 224 ∗ optProtoInnerStateJumpTablePlacedExpanded ∗
      A.pool lim (M.stepEvents w st) sf' ∗ stackAt s0.sp dropStack96)
    (by dsimp only [optProtoInnerStateJumpTablePlacedExpanded]; wp_done)
    (fun sf' _Pf hp hsp_f htr_f hacp_f' hcs_f => ⟨fun hm => ?_, hsp_f, hcs_f⟩)
  rw [← jt_placed_eq_expanded] at hp
  simp only [sepExists_sepConj_left, satisfies_sepExists]
  refine ⟨w, ?_⟩
  simp only [sepConj_assoc, satisfies_pure_sepConj]
  exact ⟨⟨htr_f, hacp_f', hevs_w⟩,
    Satisfies.mono (Entails.trans (sepConj_mono_left hp) (Entails.of_eq (by sep_ac_rfl))) hm⟩

theorem drop_opt_proto_inner_state_headerReceived_cl [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {ext : String → Option (State → State)}
    (hdealloc : HookSat (Rust.withPanics ext) spqrRustDeallocSym
      (rustCliDeallocBudgetSpec M A lim))
    (st_pb : V1State.Chunked.HeaderReceived) :
    subroutine_ok ((blkPC_267).rebase (blkPl_267).base (Rust.withPanics ext)) (blkPl_267).base
      (withLsCodeLoaded lsmpl (dropOptProtoInnerStatePlacedVariantSpec M A lim (some (.headerReceived st_pb)))) := by
  apply subroutine_ok_withLsCodeLoaded_intro; intro m hcl
  dsimp only [withMemEq, dropOptProtoInnerStatePlacedVariantSpec, optProtoInnerStateSize, BitVec.ofNat_eq_ofNat] at *
  wp_init x_st s0; rcases x_st with ⟨a, st⟩
  have _hlr0_gpr : LsRetAddr624 (s0.readReg64 (Reg.gpr 30#5)) := by assumption
  have hx0 : s0.readReg64 .x0 = a := by assumption
  have hm_eq : s0.mem = m := by assumption
  subst hm_eq
  refine proto_top_prologue_16_lscl hcl (by assumption) (by assumption) (by assumption) hx0
    fun sv hpcv hrunv hcl_v hpres_v hacp_v hx0_v => ?_
  rcases hpres_v with ⟨hx23_v, hx24_v, hx25_v, hx26_v, hx27_v, hx28_v, hsp_v, htrace_v, hvregs_v⟩
  have ⟨_, _, _, _, _, _, _⟩ := hacp_v
  conv => arg 4; dsimp only [optProtoInnerStateAt, protoInnerStateAt,
    optProtoInnerStateJumpTablePlacedAt, optProtoInnerStateJumpTableSym,
    optProtoInnerStateJumpTableBytes]
  apply sepWP_seq_lscl hcl_v (mid := lsmpl.base 283)
  wp_steps
  apply SepWP.done (by wp_norm_lhs) (by wp_norm_lhs); intro hclc
  have hcallee := drop_proto_chunked_header_received_mem_on (callerProg := lsProg_267 (Rust.withPanics ext)) hdealloc hclc
  dsimp only [lsProg_267, withMemEq, dropProtoChunkedHeaderReceivedSpec, BitVec.ofNat_eq_ofNat] at hcallee
  refine SepWP.focus_weaken (stack_restore_96_allocHook s0.sp (s0.readReg64 .fp) (s0.readReg64 .lr)
    (s0.readReg64 .x22) (s0.readReg64 .x21) (s0.readReg64 .x20) (s0.readReg64 .x19)) (by sep_focus) ?_
  refine SepWP.focus_weaken (Entails.of_eq (stackAt_dropStack96_split_48 s0.sp)) (by sep_focus) ?_
  refine sepWP_sync_pool sv (by simp only [wp_norm, arm64_norm]) (by sep_focus) ?_
  wp_call hcallee (⟨a + 8#64, st_pb⟩, st)
  have hevs_w : FreeOnlyEvs w := by assumption
  have hacp_f : AllocCallPreserved s0 sf := hacp_v.trans (by assumption)
  have ⟨_, _, _, _, _, _, _⟩ := hacp_f
  refine SepWP.focus_weaken (Entails.of_eq (stackAt_dropStack96_split_48 s0.sp).symm) (by sep_focus) ?_
  refine SepWP.focus_weaken (tag_and_two_regions_entails_224 a 0x8000000000000006#64 120 96 128#64
    (BitVec.add_assoc a 8#64 (BitVec.ofNat 64 120)).symm rfl) (by sep_focus) ?_
  refine sepWP_close_drop
    (fun sf' => memRegion a 224 ∗ optProtoInnerStateJumpTablePlacedExpanded ∗
      A.pool lim (M.stepEvents w st) sf' ∗ stackAt s0.sp dropStack96)
    (by dsimp only [optProtoInnerStateJumpTablePlacedExpanded]; wp_done)
    (fun sf' _Pf hp hsp_f htr_f hacp_f' hcs_f => ⟨fun hm => ?_, hsp_f, hcs_f⟩)
  rw [← jt_placed_eq_expanded] at hp
  simp only [sepExists_sepConj_left, satisfies_sepExists]
  refine ⟨w, ?_⟩
  simp only [sepConj_assoc, satisfies_pure_sepConj]
  exact ⟨⟨htr_f, hacp_f', hevs_w⟩,
    Satisfies.mono (Entails.trans (sepConj_mono_left hp) (Entails.of_eq (by sep_ac_rfl))) hm⟩

/-! ## Compound Variants (`ekReceivedCt1Sampled`, `ct2Sampled`) -/

theorem drop_opt_proto_inner_state_ekReceivedCt1Sampled_cl [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {ext : String → Option (State → State)}
    (hdealloc : HookSat (Rust.withPanics ext) spqrRustDeallocSym
      (rustCliDeallocBudgetSpec M A lim))
    (st_pb : V1State.Chunked.EkReceivedCt1Sampled) :
    subroutine_ok ((blkPC_267).rebase (blkPl_267).base (Rust.withPanics ext)) (blkPl_267).base
      (withLsCodeLoaded lsmpl (dropOptProtoInnerStatePlacedVariantSpec M A lim (some (.ekReceivedCt1Sampled st_pb)))) := by
  apply subroutine_ok_withLsCodeLoaded_intro; intro m hcl
  dsimp only [withMemEq, dropOptProtoInnerStatePlacedVariantSpec, optProtoInnerStateSize, BitVec.ofNat_eq_ofNat] at *
  wp_init x_st s0; rcases x_st with ⟨a, st⟩
  have _hlr0_gpr : LsRetAddr624 (s0.readReg64 (Reg.gpr 30#5)) := by assumption
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
  conv => arg 4; dsimp only [optProtoInnerStateAt, protoInnerStateAt, protoChunkedEkReceivedCt1SampledAt,
    optProtoInnerStateJumpTablePlacedAt, optProtoInnerStateJumpTableSym,
    optProtoInnerStateJumpTableBytes]
  refine seq_clean_evs_lscl hcl_v (mid := (blkPl_267).base + 664#64)
    (P_evs := fun evs sm =>
      ((a ↦₆₄ 0x8000000000000008#64) ∗ memRegion (a + 8#64) 128 ∗
        optProtoPolynomialEncoderAt A.repAlloc (a + 136#64) (st_pb.sendingCt1.map pbToProtoPolyEncoder) ∗
        memRegion (a + 192#64) 32) ∗
      optProtoInnerStateJumpTablePlacedExpanded ∗
      A.pool lim (M.stepEvents evs st) sm ∗
      (memRegion (s0.sp - 4192#64) 48 ∗ stackAt (s0.sp - 48#64) allocHookStack) ∗
      (((s0.sp - 48#64) ↦₆₄ s0.readReg64 .fp) ∗ ((s0.sp - 40#64) ↦₆₄ s0.readReg64 .lr) ∗
       ((s0.sp - 32#64) ↦₆₄ s0.readReg64 .x22) ∗ ((s0.sp - 24#64) ↦₆₄ s0.readReg64 .x21) ∗
       ((s0.sp - 16#64) ↦₆₄ s0.readReg64 .x20) ∗ ((s0.sp - 8#64) ↦₆₄ s0.readReg64 .x19)))
    (Q := fun sm => Saved48Preserved s0 sm (s0.sp - 48#64) ∧ AllocCallPreserved s0 sm ∧
      sm.readReg64 .x0 = a)
    ?_ ?_
  · cases huc : st_pb.uc with
    | none =>
      have h16 : (a + 8#64) + 8#64 = a + 16#64 := BitVec.add_assoc a 8#64 8#64
      rw [optProtoUnchunkedCt1SentEkReceivedAt_none, h16]
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
      rw [optProtoUnchunkedCt1SentEkReceivedAt_some]
      refine SepWP.focus_weaken (protoUnchunkedCt1SentEkReceivedAt_expose_cap A.repAlloc (a + 8#64) u) (by sep_focus) ?_
      wp_pull_exists; rename_i cap ptr; wp_focus_pure; intro hcap_lt
      have hne_none := cap_add_one_beq_zero_false hcap_lt
      apply sepWP_seq_lscl hcl_v (mid := lsmpl.base 286)
      wp_steps
      apply SepWP.done (by wp_norm_lhs) (by wp_norm_lhs); intro hclc1
      have hct1_sent := drop_proto_unchunked_ct1_sent_ek_received_mem_on
        (callerProg := lsProg_267 (Rust.withPanics ext)) hdealloc hclc1
      dsimp only [lsProg_267, withMemEq, dropProtoUnchunkedCt1SentEkReceivedSpec, BitVec.ofNat_eq_ofNat] at hct1_sent
      refine SepWP.focus_weaken (protoUnchunkedCt1SentEkReceivedAt_unexpose_cap A.repAlloc (a + 8#64) cap ptr u) (by sep_focus) ?_
      refine SepWP.focus_weaken (Entails.of_eq (stackAt_sub48_split_32 s0.sp)) (by sep_focus) ?_
      refine sepWP_sync_pool sv (by simp only [wp_norm, arm64_norm]) (by sep_focus) ?_
      wp_call hct1_sent (⟨a + 8#64, u⟩, st)
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
    have hjoin184 : memRegion (a + 8#64) 128 ∗ memRegion (a + 136#64) 56 ⊢ memRegion (a + 8#64) 184 := by
      rw [← h136, ProofLib.memRegion_split (a + 8#64) 128 56 (by decide)]; exact Entails.refl _
    have hjoin224 : (a ↦₆₄ 0x8000000000000008#64) ∗ memRegion (a + 8#64) 184 ∗ memRegion (a + 192#64) 32 ⊢ memRegion a 224 :=
      tag_and_two_regions_entails_224 a 0x8000000000000008#64 184 32 192#64 (BitVec.add_assoc a 8#64 184#64).symm rfl
    cases hct1 : st_pb.sendingCt1 with
    | none =>
      simp only [Option.map_none, optProtoPolynomialEncoderAt_none']
      have h144 : (a + 136#64) + 8#64 = a + 144#64 := BitVec.add_assoc a 136#64 8#64
      rw [h144]
      refine sepWP_close_drop
        (fun sf => memRegion a 224 ∗ optProtoInnerStateJumpTablePlacedExpanded ∗
          A.pool lim st1 sf ∗ stackAt s0.sp dropStack96)
        ?_
        (fun sf _Pf hp hsp_f htr_f hacp_f hcs_f => ⟨fun hm => ?_, hsp_f, hcs_f⟩)
      · dsimp only [optProtoInnerStateJumpTablePlacedExpanded]
        wp_steps
        have hnone56 : ((a + 136#64) ↦₆₄ noneCap) ∗ memRegion (a + 144#64) 48 ⊢ memRegion (a + 136#64) 56 := by
          rw [← h144]; exact optProtoPolyEncoder_none_entails_memRegion_56 (a + 136#64)
        refine SepWP.focus_weaken hnone56 (by sep_focus) ?_
        refine SepWP.focus_weaken hjoin184 (by sep_focus) ?_
        refine SepWP.focus_weaken hjoin224 (by sep_focus) ?_
        refine SepWP.focus_weaken (stack_restore_96_allocHook s0.sp (s0.readReg64 .fp) (s0.readReg64 .lr)
          (s0.readReg64 .x22) (s0.readReg64 .x21) (s0.readReg64 .x20) (s0.readReg64 .x19)) (by sep_focus) ?_
        refine sepWP_sync_pool s1 (by simp only [wp_norm, arm64_norm]) (by sep_focus) ?_
        wp_done
      · rw [← jt_placed_eq_expanded] at hp
        simp only [sepExists_sepConj_left, satisfies_sepExists]
        refine ⟨evs1, ?_⟩
        simp only [sepConj_assoc, satisfies_pure_sepConj]
        exact ⟨⟨htr_f, hacp_f, hevs1⟩,
          Satisfies.mono (Entails.trans (sepConj_mono_left hp) (Entails.of_eq (by sep_ac_rfl))) hm⟩
    | some enc =>
      conv => arg 4; dsimp only [optProtoInnerStateJumpTablePlacedExpanded]
      simp only [Option.map_some, optProtoPolynomialEncoderAt_some']
      refine SepWP.focus_weaken (protoPolynomialEncoderAt_expose_cap A.repAlloc (a + 136#64) (pbToProtoPolyEncoder enc)) (by sep_focus) ?_
      wp_pull_exists; rename_i cap ptr; wp_focus_pure; intro hcap_lt
      have hne_none := cap_add_one_beq_zero_false hcap_lt
      apply sepWP_seq_lscl hcl1 (mid := lsmpl.base 271)
      wp_steps
      apply SepWP.done (by wp_norm_lhs) (by wp_norm_lhs); intro hclc2
      have hpoly_enc := drop_glue_proto_poly_encoder_mem_on
        (callerProg := lsProg_267 (Rust.withPanics ext)) hdealloc hclc2
      dsimp only [lsProg_267, withMemEq, dropProtoPolyEncoderSpec, BitVec.ofNat_eq_ofNat] at hpoly_enc
      refine SepWP.focus_weaken (protoPolynomialEncoderAt_unexpose_cap A.repAlloc (a + 136#64) cap ptr (pbToProtoPolyEncoder enc)) (by sep_focus) ?_
      refine SepWP.focus_weaken (stack_restore_96_allocHook s0.sp (s0.readReg64 .fp) (s0.readReg64 .lr)
        (s0.readReg64 .x22) (s0.readReg64 .x21) (s0.readReg64 .x20) (s0.readReg64 .x19)) (by sep_focus) ?_
      refine SepWP.focus_weaken (Entails.of_eq (stackAt_dropStack96_split_48 s0.sp)) (by sep_focus) ?_
      refine sepWP_sync_pool s1 (by simp only [wp_norm, arm64_norm]) (by sep_focus) ?_
      wp_call hpoly_enc (⟨a + 136#64, pbToProtoPolyEncoder enc⟩, st1)
      have hevs_w : FreeOnlyEvs w := by assumption
      have hacp_f : AllocCallPreserved s0 sf := hacp_1.trans (by assumption)
      have ⟨_, _, _, _, _, _, _⟩ := hacp_f
      refine SepWP.focus_weaken (Entails.of_eq (stackAt_dropStack96_split_48 s0.sp).symm) (by sep_focus) ?_
      refine SepWP.focus_weaken hjoin184 (by sep_focus) ?_
      refine SepWP.focus_weaken hjoin224 (by sep_focus) ?_
      refine sepWP_close_drop
        (fun sf' => memRegion a 224 ∗ optProtoInnerStateJumpTablePlacedExpanded ∗
          A.pool lim (M.stepEvents w st1) sf' ∗ stackAt s0.sp dropStack96)
        (by dsimp only [optProtoInnerStateJumpTablePlacedExpanded]; wp_done)
        (fun sf' _Pf hp hsp_f htr_f hacp_f' hcs_f => ⟨fun hm => ?_, hsp_f, hcs_f⟩)
      rw [← jt_placed_eq_expanded] at hp
      simp only [sepExists_sepConj_left, satisfies_sepExists]
      refine ⟨evs1 ++ w, ?_⟩
      simp only [sepConj_assoc, satisfies_pure_sepConj]
      refine ⟨⟨htr_f, hacp_f', hevs1.append hevs_w⟩, ?_⟩
      have heq_st : M.stepEvents (evs1 ++ w) st = M.stepEvents w st1 := by
        simp only [st1, LibsignalBinary.Heap.AllocCostModel.stepEvents_append]
      rw [heq_st]
      exact Satisfies.mono (Entails.trans (sepConj_mono_left hp) (Entails.of_eq (by sep_ac_rfl))) hm

theorem drop_opt_proto_inner_state_ct2Sampled_cl [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {ext : String → Option (State → State)}
    (hdealloc : HookSat (Rust.withPanics ext) spqrRustDeallocSym
      (rustCliDeallocBudgetSpec M A lim))
    (st_pb : V1State.Chunked.Ct2Sampled) :
    subroutine_ok ((blkPC_267).rebase (blkPl_267).base (Rust.withPanics ext)) (blkPl_267).base
      (withLsCodeLoaded lsmpl (dropOptProtoInnerStatePlacedVariantSpec M A lim (some (.ct2Sampled st_pb)))) := by
  apply subroutine_ok_withLsCodeLoaded_intro; intro m hcl
  have hdealloc_raw : subroutine_ok ((blkPC_267).rebase (blkPl_267).base (Rust.withPanics ext))
      (lsρ spqrRustDeallocSym) (rustCliDeallocBudgetSpec M A lim) :=
    spqr_hook_ok_of_mem (prog := lsProg_267 (Rust.withPanics ext)) hdealloc
  simp only [spqrRustDeallocSym] at hdealloc_raw
  have hdealloc_fo := subroutine_ok_deallocFreeOnly hdealloc_raw
  clear hdealloc_raw
  simp only [deallocFreeOnlySpec, rustCliDeallocBudgetSpec] at hdealloc_fo
  dsimp only [withMemEq, dropOptProtoInnerStatePlacedVariantSpec, optProtoInnerStateSize, BitVec.ofNat_eq_ofNat] at hdealloc_fo ⊢
  wp_init x_st s0; rcases x_st with ⟨a, st⟩
  have _hlr0_gpr : LsRetAddr624 (s0.readReg64 (Reg.gpr 30#5)) := by assumption
  have hm_eq : s0.mem = m := by assumption
  subst hm_eq
  have hx0 : s0.readReg64 .x0 = a := by assumption
  dsimp only at *
  have hfsp_align : ((s0.sp - 48#64) &&& 15#64 == 0#64) = true :=
    spAligned_sub s0.sp 48#64 (by assumption) (by decide)
  have h64 : (a + 8#64) + 56#64 = a + 64#64 := BitVec.add_assoc a 8#64 56#64
  refine proto_top_prologue_16_lscl hcl (by assumption) (by assumption) (by assumption) hx0
    fun sv hpcv hrunv hcl_v hpres_v hacp_v hx0_v => ?_
  rcases hpres_v with ⟨hx23_v, hx24_v, hx25_v, hx26_v, hx27_v, hx28_v, hsp_v, htrace_v, hvregs_v⟩
  have ⟨_, _, _, _, _, _, _⟩ := hacp_v
  conv => arg 4; dsimp only [optProtoInnerStateAt, protoInnerStateAt, protoChunkedCt2SampledAt]
  rw [h64]
  refine seq_clean_evs_lscl hcl_v (mid := (blkPl_267).base + 600#64)
    (P_evs := fun evs sm =>
      ((a ↦₆₄ 0x800000000000000a#64) ∗
        optProtoPolynomialEncoderAt A.repAlloc (a + 8#64) (st_pb.sendingCt2.map pbToProtoPolyEncoder) ∗
        memRegion (a + 64#64) 56 ∗ memRegion (a + 120#64) 104) ∗
      optProtoInnerStateJumpTablePlacedAt ∗
      A.pool lim (M.stepEvents evs st) sm ∗
      (memRegion (s0.sp - 4192#64) 48 ∗ stackAt (s0.sp - 48#64) allocHookStack) ∗
      (((s0.sp - 48#64) ↦₆₄ s0.readReg64 .fp) ∗ ((s0.sp - 40#64) ↦₆₄ s0.readReg64 .lr) ∗
       ((s0.sp - 32#64) ↦₆₄ s0.readReg64 .x22) ∗ ((s0.sp - 24#64) ↦₆₄ s0.readReg64 .x21) ∗
       ((s0.sp - 16#64) ↦₆₄ s0.readReg64 .x20) ∗ ((s0.sp - 8#64) ↦₆₄ s0.readReg64 .x19)))
    (Q := fun sm => Saved48Preserved s0 sm (s0.sp - 48#64) ∧ AllocCallPreserved s0 sm ∧
      sm.readReg64 .x0 = a)
    ?_ ?_
  · cases huc : st_pb.uc with
    | none =>
      have h72 : (a + 64#64) + 8#64 = a + 72#64 := BitVec.add_assoc a 64#64 8#64
      dsimp only [optProtoUnchunkedCt2SentAt]; rw [h72]
      apply sepWP_evs_inst [] LibsignalBinary.Heap.FreeOnlyEvs.nil
      wp_steps
      have hnone56 : ((a + 64#64) ↦₆₄ none2Cap) ∗ memRegion (a + 72#64) 48 ⊢ memRegion (a + 64#64) 56 := by
        rw [← h72]; exact optProtoUnchunkedNoHeaderReceivedAt_none_entails_memRegion_56 A.repAlloc (a + 64#64)
      refine SepWP.focus_weaken hnone56 (by sep_focus) ?_
      refine sepWP_sync_pool sv (by simp only [wp_norm, arm64_norm]) (by sep_focus) ?_
      refine align_pre_st (by
        simp only [LibsignalBinary.Heap.AllocCostModel.stepEvents_nil,
          Reg.fp, Reg.lr, Reg.x19, Reg.x20, Reg.x21, Reg.x22, wp_norm, arm64_norm]
        sep_ac_rfl) ?_
      wp_done
    | some u =>
      have h112 : (a + 64#64) + 48#64 = a + 112#64 := BitVec.add_assoc a 64#64 48#64
      dsimp only [optProtoUnchunkedCt2SentAt, protoUnchunkedCt2SentAt]; rw [h112]
      cases hauth : u.auth with
      | none =>
        have hnone64 : optProtoAuthenticatorAt A.repAlloc (a + 64#64) none =
            ((a + 64#64) ↦₆₄ noneCap) ∗ memRegion (a + 72#64) 40 := by
          rw [optProtoAuthenticatorAt_none, BitVec.add_assoc a 64#64 8#64]; rfl
        rw [hnone64]
        apply sepWP_evs_inst [] LibsignalBinary.Heap.FreeOnlyEvs.nil
        wp_steps
        refine SepWP.focus_weaken (optProtoAuthenticatorAt_64_none_entails_memRegion_56 A.repAlloc a u.epoch) (by sep_focus) ?_
        refine sepWP_sync_pool sv (by simp only [wp_norm, arm64_norm]) (by sep_focus) ?_
        refine align_pre_st (by
          simp only [LibsignalBinary.Heap.AllocCostModel.stepEvents_nil,
            Reg.fp, Reg.lr, Reg.x19, Reg.x20, Reg.x21, Reg.x22, wp_norm, arm64_norm]
          sep_ac_rfl) ?_
        wp_done
      | some auth =>
        rw [optProtoAuthenticatorAt_some]
        refine SepWP.focus_weaken (protoAuthenticatorAt_entails_dealloc A.repAlloc (a + 64#64) auth) (by sep_focus) ?_
        wp_pull_exists; rename_i ga; rw [twoVecHeadersAt_64_eq]; wp_focus_pure; intro hga_lt
        have hne_none2 := cap_add_two_beq_zero_false hga_lt
        have hne_none1 := cap_add_one_beq_zero_false hga_lt
        refine seq_clean_evs (mid := (blkPl_267).base + 568#64)
          (P_evs := fun evs sm =>
            ((a ↦₆₄ 0x800000000000000a#64) ∗
              optProtoPolynomialEncoderAt A.repAlloc (a + 8#64) (st_pb.sendingCt2.map pbToProtoPolyEncoder) ∗
              ((auth64HeadersAt a ga ∗ vecCapPtrDealloc A.repAlloc ga.v2.cap ga.v2.ptr) ∗ ((a + 112#64) ↦₆₄ u.epoch)) ∗
              memRegion (a + 120#64) 104) ∗
            optProtoInnerStateJumpTablePlacedAt ∗
            A.pool lim (M.stepEvents evs st) sm ∗
            (memRegion (s0.sp - 4192#64) 48 ∗ stackAt (s0.sp - 48#64) allocHookStack) ∗
            (((s0.sp - 48#64) ↦₆₄ s0.readReg64 .fp) ∗ ((s0.sp - 40#64) ↦₆₄ s0.readReg64 .lr) ∗
             ((s0.sp - 32#64) ↦₆₄ s0.readReg64 .x22) ∗ ((s0.sp - 24#64) ↦₆₄ s0.readReg64 .x21) ∗
             ((s0.sp - 16#64) ↦₆₄ s0.readReg64 .x20) ∗ ((s0.sp - 8#64) ↦₆₄ s0.readReg64 .x19)))
          (Q := fun sm => Saved48Preserved s0 sm (s0.sp - 48#64) ∧ AllocCallPreserved s0 sm ∧
            sm.readReg64 .x0 = a)
          ?_ ?_
        · dsimp only [auth64HeadersAt, vecCapPtrDealloc, LibsignalBinary.Heap.RustCliAllocBudget.repAlloc_live]
          by_cases hca1 : (ga.v1.cap == 0#64) = true <;>
            simp only [hca1, Bool.false_eq_true, ↓reduceIte, sepConj_emp, emp_sepConj]
          · apply sepWP_evs_inst [] LibsignalBinary.Heap.FreeOnlyEvs.nil
            wp_steps
            refine sepWP_sync_pool sv (by simp only [wp_norm, arm64_norm]) (by sep_focus) ?_
            refine align_pre_st (by
              simp only [LibsignalBinary.Heap.AllocCostModel.stepEvents_nil,
                Reg.fp, Reg.lr, Reg.x19, Reg.x20, Reg.x21, Reg.x22, wp_norm, arm64_norm]
              sep_ac_rfl) ?_
            wp_done
          · apply sepWP_evs_dealloc ga.v1.cap.toNat 1
            wp_steps
            refine sepWP_sync_pool sv (by simp only [wp_norm, arm64_norm]) (by sep_focus) ?_
            wp_call hdealloc_fo (ga.v1.ptr, ga.v1.cap.toNat, 1, st)
            rw [hsp_v]
            have hacp_f : AllocCallPreserved s0 sf := hacp_v.trans (by assumption)
            rcases hacp_f with ⟨_, _, _, _, _, _, _⟩
            wp_steps
            refine sepWP_sync_pool sf (by simp only [wp_norm, arm64_norm]) (by sep_focus) ?_
            refine align_pre_st (by
              simp only [Reg.fp, Reg.lr, Reg.x19, Reg.x20, Reg.x21, Reg.x22, wp_norm, arm64_norm]
              sep_ac_rfl) ?_
            wp_done
        · intro evsa1 sa1 hevsa1 hpca1 hruna1 ⟨⟨hx23_a1, hx24_a1, hx25_a1, hx26_a1, hx27_a1, hx28_a1, hsp_a1, htrace_a1, hvregs_a1⟩, hacp_a1, hx0_a1⟩
          have ⟨_, _, _, _, _, _, _⟩ := hacp_a1
          let sta1 := M.stepEvents evsa1 st
          dsimp only [auth64HeadersAt, vecCapPtrDealloc, LibsignalBinary.Heap.RustCliAllocBudget.repAlloc_live]
          by_cases hca2 : (ga.v2.cap == 0#64) = true <;>
            simp only [hca2, Bool.false_eq_true, ↓reduceIte, sepConj_emp, emp_sepConj]
          · apply sepWP_evs_inst evsa1 hevsa1
            wp_steps
            refine SepWP.focus_weaken (auth64HeadersAt_entails_memRegion_56 a ga u.epoch) (by sep_focus) ?_
            refine sepWP_sync_pool sa1 (by simp only [wp_norm, arm64_norm]) (by sep_focus) ?_
            refine align_pre_st (by
              simp only [sta1, Reg.fp, Reg.lr, Reg.x19, Reg.x20, Reg.x21, Reg.x22, wp_norm, arm64_norm]
              sep_ac_rfl) ?_
            wp_done
          · apply sepWP_evs_inst (evsa1 ++ rustDeallocEvents ga.v2.cap.toNat 1)
              (hevsa1.append (LibsignalBinary.Heap.FreeOnlyEvs.singleton 1 ga.v2.cap.toNat))
            wp_steps
            refine sepWP_sync_pool sa1 (by simp only [wp_norm, arm64_norm]) (by sep_focus) ?_
            wp_call hdealloc_fo (ga.v2.ptr, ga.v2.cap.toNat, 1, sta1)
            rw [hsp_a1]
            have hacp_f : AllocCallPreserved s0 sf := hacp_a1.trans (by assumption)
            rcases hacp_f with ⟨_, _, _, _, _, _, _⟩
            wp_steps
            refine SepWP.focus_weaken (auth64HeadersAt_entails_memRegion_56 a ga u.epoch) (by sep_focus) ?_
            refine sepWP_sync_pool sf (by simp only [wp_norm, arm64_norm]) (by sep_focus) ?_
            have heq_st : M.stepEvents (evsa1 ++ rustDeallocEvents ga.v2.cap.toNat 1) st =
                M.stepEvents (rustDeallocEvents ga.v2.cap.toNat 1) sta1 := by
              simp only [sta1, LibsignalBinary.Heap.AllocCostModel.stepEvents_append]
            rw [heq_st]
            refine align_pre_st (by
              simp only [Reg.fp, Reg.lr, Reg.x19, Reg.x20, Reg.x21, Reg.x22, wp_norm, arm64_norm]
              sep_ac_rfl) ?_
            wp_done
  · intro evs1 s1 hevs1 hpc1 hrun1 hcl1 ⟨⟨hx23_1, hx24_1, hx25_1, hx26_1, hx27_1, hx28_1, hsp_1, htrace_1, hvregs_1⟩, hacp_1, hx0_1⟩
    have ⟨_, _, _, _, _, _, _⟩ := hacp_1
    let st1 := M.stepEvents evs1 st
    have hjoin112 : memRegion (a + 8#64) 56 ∗ memRegion (a + 64#64) 56 ⊢ memRegion (a + 8#64) 112 := by
      rw [← h64, ProofLib.memRegion_split (a + 8#64) 56 56 (by decide)]; exact Entails.refl _
    have hjoin224 : (a ↦₆₄ 0x800000000000000a#64) ∗ memRegion (a + 8#64) 112 ∗ memRegion (a + 120#64) 104 ⊢ memRegion a 224 :=
      tag_and_two_regions_entails_224 a 0x800000000000000a#64 112 104 120#64 (BitVec.add_assoc a 8#64 112#64).symm rfl
    cases hct2 : st_pb.sendingCt2 with
    | none =>
      simp only [Option.map_none, optProtoPolynomialEncoderAt_none']
      have h16 : (a + 8#64) + 8#64 = a + 16#64 := BitVec.add_assoc a 8#64 8#64
      rw [h16]
      refine sepWP_close_drop
        (fun sf => memRegion a 224 ∗ optProtoInnerStateJumpTablePlacedAt ∗
          A.pool lim st1 sf ∗ stackAt s0.sp dropStack96)
        ?_
        (fun sf _Pf hp hsp_f htr_f hacp_f hcs_f => ⟨fun hm => ?_, hsp_f, hcs_f⟩)
      · wp_steps
        have hnone56 : ((a + 8#64) ↦₆₄ noneCap) ∗ memRegion (a + 16#64) 48 ⊢ memRegion (a + 8#64) 56 := by
          rw [← h16]; exact optProtoPolyEncoder_none_entails_memRegion_56 (a + 8#64)
        refine SepWP.focus_weaken hnone56 (by sep_focus) ?_
        refine SepWP.focus_weaken hjoin112 (by sep_focus) ?_
        refine SepWP.focus_weaken hjoin224 (by sep_focus) ?_
        refine SepWP.focus_weaken (stack_restore_96_allocHook s0.sp (s0.readReg64 .fp) (s0.readReg64 .lr)
          (s0.readReg64 .x22) (s0.readReg64 .x21) (s0.readReg64 .x20) (s0.readReg64 .x19)) (by sep_focus) ?_
        refine sepWP_sync_pool s1 (by simp only [wp_norm, arm64_norm]) (by sep_focus) ?_
        wp_done
      · simp only [sepExists_sepConj_left, satisfies_sepExists]
        refine ⟨evs1, ?_⟩
        simp only [sepConj_assoc, satisfies_pure_sepConj]
        exact ⟨⟨htr_f, hacp_f, hevs1⟩,
          Satisfies.mono (Entails.trans (sepConj_mono_left hp) (Entails.of_eq (by sep_ac_rfl))) hm⟩
    | some enc =>
      simp only [Option.map_some, optProtoPolynomialEncoderAt_some']
      refine SepWP.focus_weaken (protoPolynomialEncoderAt_expose_cap A.repAlloc (a + 8#64) (pbToProtoPolyEncoder enc)) (by sep_focus) ?_
      wp_pull_exists; rename_i cap ptr; wp_focus_pure; intro hcap_lt
      have hne_none := cap_add_one_beq_zero_false hcap_lt
      apply sepWP_seq_lscl hcl1 (mid := lsmpl.base 271)
      wp_steps
      apply SepWP.done (by wp_norm_lhs) (by wp_norm_lhs); intro hclc
      have hpoly_enc := drop_glue_proto_poly_encoder_mem_on
        (callerProg := lsProg_267 (Rust.withPanics ext)) hdealloc hclc
      dsimp only [lsProg_267, withMemEq, dropProtoPolyEncoderSpec, BitVec.ofNat_eq_ofNat] at hpoly_enc
      refine SepWP.focus_weaken (protoPolynomialEncoderAt_unexpose_cap A.repAlloc (a + 8#64) cap ptr (pbToProtoPolyEncoder enc)) (by sep_focus) ?_
      refine SepWP.focus_weaken (stack_restore_96_allocHook s0.sp (s0.readReg64 .fp) (s0.readReg64 .lr)
        (s0.readReg64 .x22) (s0.readReg64 .x21) (s0.readReg64 .x20) (s0.readReg64 .x19)) (by sep_focus) ?_
      refine SepWP.focus_weaken (Entails.of_eq (stackAt_dropStack96_split_48 s0.sp)) (by sep_focus) ?_
      refine sepWP_sync_pool s1 (by simp only [wp_norm, arm64_norm]) (by sep_focus) ?_
      wp_call hpoly_enc (⟨a + 8#64, pbToProtoPolyEncoder enc⟩, st1)
      have hevs_w : FreeOnlyEvs w := by assumption
      have hacp_f : AllocCallPreserved s0 sf := hacp_1.trans (by assumption)
      have ⟨_, _, _, _, _, _, _⟩ := hacp_f
      refine SepWP.focus_weaken (Entails.of_eq (stackAt_dropStack96_split_48 s0.sp).symm) (by sep_focus) ?_
      refine SepWP.focus_weaken hjoin112 (by sep_focus) ?_
      refine SepWP.focus_weaken hjoin224 (by sep_focus) ?_
      refine sepWP_close_drop
        (fun sf' => memRegion a 224 ∗ optProtoInnerStateJumpTablePlacedAt ∗
          A.pool lim (M.stepEvents w st1) sf' ∗ stackAt s0.sp dropStack96)
        (by wp_done)
        (fun sf' _Pf hp hsp_f htr_f hacp_f' hcs_f => ⟨fun hm => ?_, hsp_f, hcs_f⟩)
      simp only [sepExists_sepConj_left, satisfies_sepExists]
      refine ⟨evs1 ++ w, ?_⟩
      simp only [sepConj_assoc, satisfies_pure_sepConj]
      refine ⟨⟨htr_f, hacp_f', hevs1.append hevs_w⟩, ?_⟩
      have heq_st : M.stepEvents (evs1 ++ w) st = M.stepEvents w st1 := by
        simp only [st1, LibsignalBinary.Heap.AllocCostModel.stepEvents_append]
      rw [heq_st]
      exact Satisfies.mono (Entails.trans (sepConj_mono_left hp) (Entails.of_eq (by sep_ac_rfl))) hm


end LibsignalBinary.Proofs.SpqrV1.Drop.ProtoTopClPlacedBudgetAux1
