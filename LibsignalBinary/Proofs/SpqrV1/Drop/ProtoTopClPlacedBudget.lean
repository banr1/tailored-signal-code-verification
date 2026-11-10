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
public import LibsignalBinary.Proofs.SpqrV1.Drop.ProtoTop2Budget
public import LibsignalBinary.Proofs.SpqrV1.Drop.ProtoTopClPlacedBudgetAux2
import LibsignalBinary.Proofs.Common.SharedHelpers
meta import LibsignalBinary.Proofs.Common.SharedHelpers -- shake: keep
import LibsignalBinary.Proofs.Placed.ElfLsRetAddr
import LibsignalBinary.Proofs.SpqrV1.Alloc.SpqrAllocCodeSym
import ProofLib.SepLogic.WP.Apply
import ProofLib.SepLogic.WPp
import GeneratedLean.LibsignalSessionObj

/-!
# Budget-Threaded Code-Loaded Drop Glue for `PqRatchetState` (Block `270`)

Proves `withLsCodeLoaded lsmpl` subroutine contracts under `RustCliAllocBudget M` (`FreeOnlyEvs`)
for Block `270` (`drop_glue::<spqr::proto::pq_ratchet::PqRatchetState>`), re-exporting Block `267`
from `ProtoTopClPlacedBudgetAux2`.
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
open LibsignalBinary.Proofs.SpqrV1.Drop.ProtoChunkedClPlacedBudgetAux (
  drop_proto_epoch_slice_mem_on seq_clean_evs_lscl
)
open LibsignalBinary.Proofs.SpqrV1.Drop.ProtoTop2BudgetAux (
  sepWP_close_drop sepWP_sync_pool sepWP_vm_evs_nil
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
open LibsignalBinary.Proofs.SpqrV1.Drop.ProtoTopClPlacedBudgetAux2 (
  drop_opt_proto_inner_state_cl_blockProgram drop_opt_proto_inner_state_cl_on
  drop_opt_proto_inner_state_cl_placed_ok drop_opt_proto_inner_state_mem_on
)
open LibsignalBinary.Proofs.SpqrV1.States.Recv.DropChunkedClPlacedBudgetAux (
  ls_to_blockProgram subroutine_ok_withLsCodeLoaded_intro
)

namespace LibsignalBinary.Proofs.SpqrV1.Drop.ProtoTopClPlacedBudget

open Arm64 ProofLib
open ProofLib.ProgramReflection

export LibsignalBinary.Proofs.SpqrV1.Drop.ProtoTopBudget (
  dropOptProtoInnerStatePlacedSpec
  dropOptProtoInnerStatePlacedVariantSpec
  dropProtoPqRatchetStatePlacedSpec
)
export LibsignalBinary.Proofs.SpqrV1.Drop.ProtoTopClPlacedBudgetAux2 (
  drop_opt_proto_inner_state_cl_placed_ok
  drop_opt_proto_inner_state_cl_blockProgram
  drop_opt_proto_inner_state_cl_on
  drop_opt_proto_inner_state_mem_on
)

attribute [local irreducible] Program.fetch Program.externAt? Program.fnOff
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero
attribute [local simp, local arm64_norm] none2Cap_add_two_beq_zero noneCap_add_two_beq_zero

/-! ## Block `270`: `drop_glue::<spqr::proto::pq_ratchet::PqRatchetState>` -/

theorem drop_proto_pq_ratchet_state_cl_placed_ok [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {ext : String → Option (State → State)}
    (hdealloc : HookSat (Rust.withPanics ext) spqrRustDeallocSym
      (rustCliDeallocBudgetSpec M A lim)) :
    subroutine_ok (lsProg_270 (Rust.withPanics ext)) (lsmpl.base 270)
      (withLsCodeLoaded lsmpl (dropProtoPqRatchetStatePlacedSpec M A lim)) := by
  rw [← ls_blockPlacement_base (i := 270)]
  change subroutine_ok ((blkPC_270).rebase (blkPl_270).base (Rust.withPanics ext)) (blkPl_270).base _
  apply subroutine_ok_withLsCodeLoaded_intro; intro m hcl
  have hdealloc_raw : subroutine_ok ((blkPC_270).rebase (blkPl_270).base (Rust.withPanics ext))
      (lsρ spqrRustDeallocSym) (rustCliDeallocBudgetSpec M A lim) :=
    spqr_hook_ok_of_mem (prog := lsProg_270 (Rust.withPanics ext)) hdealloc
  simp only [spqrRustDeallocSym] at hdealloc_raw
  have hdealloc_fo := subroutine_ok_deallocFreeOnly hdealloc_raw
  clear hdealloc_raw
  simp only [deallocFreeOnlySpec, rustCliDeallocBudgetSpec] at hdealloc_fo
  dsimp only [withMemEq, dropProtoPqRatchetStatePlacedSpec,
    protoPqRatchetStateAt, protoPqRatchetStateSize, optProtoInnerStateSize, chainEpochPBSize,
    BitVec.ofNat_eq_ofNat] at hdealloc_fo ⊢
  wp_init x_st s0
  have _hlr0_gpr : LsRetAddr624 (s0.readReg64 (Reg.gpr 30#5)) := by assumption
  rcases x_st with ⟨⟨a, st_pb⟩, st⟩
  have hm_eq : s0.mem = m := by assumption
  subst hm_eq
  have hx0 : s0.readReg64 .x0 = a := by assumption
  dsimp only [CryptoVerification.SpqrV1.Drop.DropProtoPqRatchetStateGhost.a,
    CryptoVerification.SpqrV1.Drop.DropProtoPqRatchetStateGhost.st] at *
  have hfsp_align : ((s0.sp - 48#64) &&& 15#64 == 0#64) = true :=
    spAligned_sub s0.sp 48#64 (by assumption) (by decide)
  nth_rw 1 [stackAt_dropStack96_split s0.sp]; cells_unfold; wp_pull_exists
  rename_i v_fp v_lr v_x22 v_x21 v_x20 v_x19
  refine seq_clean_evs_lscl hcl (mid := (blkPl_270).base + 44#64)
    (P_evs := fun evs sm =>
      (memRegion a 48 ∗ optChainPBAt A.repAlloc (a + 48#64) st_pb.chain ∗
        optProtoPqRatchetInnerAt A.repAlloc (a + 128#64) st_pb.inner) ∗
      optProtoInnerStateJumpTablePlacedAt ∗
      A.pool lim (M.stepEvents evs st) sm ∗
      (memRegion (s0.sp - 4192#64) 48 ∗ stackAt (s0.sp - 48#64) allocHookStack) ∗
      (((s0.sp - 48#64) ↦₆₄ s0.readReg64 .fp) ∗ ((s0.sp - 40#64) ↦₆₄ s0.readReg64 .lr) ∗
       ((s0.sp - 32#64) ↦₆₄ s0.readReg64 .x21) ∗ ((s0.sp - 24#64) ↦₆₄ v_x21) ∗
       ((s0.sp - 16#64) ↦₆₄ s0.readReg64 .x20) ∗ ((s0.sp - 8#64) ↦₆₄ s0.readReg64 .x19)))
    (Q := fun sm => Saved48Preserved s0 sm (s0.sp - 48#64) ∧ AllocCallPreserved s0 sm ∧
      sm.readReg64 .x22 = s0.readReg64 .x22 ∧ sm.readReg64 .x19 = a) ?_ ?_
  · cases hvn : st_pb.versionNegotiation with
    | none =>
      dsimp only [optVersionNegotiationPBAt]
      refine sepWP_vm_evs_nil (fun sm hvm => by
        simp only [LibsignalBinary.Heap.AllocCostModel.stepEvents_nil, A.pool_of_vmPreserved hvm]) ?_
      by_vm_steps (
        wp_steps
        refine SepWP.focus_weaken (optVersionNegotiationPBAt_none_entails_memRegion_48 a) (by sep_focus) ?_
        refine align_pre_vm (by simp only [LibsignalBinary.Heap.AllocCostModel.stepEvents_nil,
          Reg.fp, Reg.lr, Reg.x19, Reg.x20, Reg.x21, wp_norm, arm64_norm]; try sep_ac_rfl) ?_
        wp_done)
    | some vn =>
      dsimp only [optVersionNegotiationPBAt]
      refine SepWP.focus_weaken (versionNegotiationPBAt_entails_dealloc A.repAlloc a vn) (by sep_focus) ?_
      wp_pull_exists; rename_i g; rcases g with ⟨cap, ptr⟩; wp_focus_pure; intro hcap_lt
      dsimp only [vecCapPtrDealloc, LibsignalBinary.Heap.RustCliAllocBudget.repAlloc_live] at hcap_lt ⊢
      have hne_none := cap_add_one_beq_zero_false hcap_lt
      by_cases hc0 : (cap == 0#64) = true <;>
        simp only [hc0, Bool.false_eq_true, ↓reduceIte, emp_sepConj, sepConj_emp]
      · have hc_eq : cap = 0#64 := by rwa [beq_iff_eq] at hc0
        subst hc_eq
        refine sepWP_vm_evs_nil (fun sm hvm => by
          simp only [LibsignalBinary.Heap.AllocCostModel.stepEvents_nil, A.pool_of_vmPreserved hvm]) ?_
        by_vm_steps (
          wp_steps
          refine SepWP.focus_weaken (vnHeader_entails_memRegion_48 a 0#64 ptr) (by sep_focus) ?_
          refine align_pre_vm (by simp only [LibsignalBinary.Heap.AllocCostModel.stepEvents_nil,
            Reg.fp, Reg.lr, Reg.x19, Reg.x20, Reg.x21, wp_norm, arm64_norm]; try sep_ac_rfl) ?_
          wp_done)
      · have hslt := cap_ne_zero_slt_one_false hcap_lt hc0
        have hlt_false := cap_ne_zero_lt_one_false hcap_lt hc0
        apply sepWP_evs_dealloc cap.toNat 1
        refine seq_vm_clean (mid := lsρ "_RNvCs1njKG4L9aB3_7___rustc14___rust_dealloc")
          (P_mid := A.pool lim st s0 ∗ A.live ptr cap.toNat 1 ∗ memRegion ptr cap.toNat ∗
            stackAt (s0.sp - 48#64) allocHookStack ∗
            (((a ↦₆₄ cap) ∗ ((a + 8#64) ↦₆₄ ptr) ∗ memRegion (a + 16#64) 32 ∗
              optChainPBAt A.repAlloc (a + 48#64) st_pb.chain ∗
              optProtoPqRatchetInnerAt A.repAlloc (a + 128#64) st_pb.inner) ∗
             optProtoInnerStateJumpTablePlacedAt ∗ memRegion (s0.sp - 4192#64) 48 ∗
             (((s0.sp - 48#64) ↦₆₄ s0.readReg64 .fp) ∗ ((s0.sp - 40#64) ↦₆₄ s0.readReg64 .lr) ∗
              ((s0.sp - 32#64) ↦₆₄ s0.readReg64 .x21) ∗ ((s0.sp - 24#64) ↦₆₄ v_x21) ∗
              ((s0.sp - 16#64) ↦₆₄ s0.readReg64 .x20) ∗ ((s0.sp - 8#64) ↦₆₄ s0.readReg64 .x19))))
          (Q := fun sc => Saved48Preserved s0 sc (s0.sp - 48#64) ∧ AllocCallPreserved s0 sc ∧
            sc.readReg64 .x0 = ptr ∧ sc.readReg64 .x1 = cap ∧ sc.readReg64 .x2 = 1#64 ∧
            sc.readReg64 .lr = (blkPl_270).base + 44#64 ∧
            sc.readReg64 .x22 = s0.readReg64 .x22 ∧ sc.readReg64 .x19 = a) ?_ ?_
        · by_vm_steps (
            wp_steps
            refine align_pre_vm (by simp only [Reg.fp, Reg.lr, Reg.x19, Reg.x20, Reg.x21,
              wp_norm, arm64_norm]; try sep_ac_rfl) ?_
            wp_done)
        · intro sc hpcc hrunc hvmc ⟨hpres_c, hacp_c, hx0_c, hx1_c, hx2_c, hlr_c, hx22_c, hx19_c⟩
          rcases hpres_c with ⟨hx23_c, hx24_c, hx25_c, hx26_c, hx27_c, hx28_c, hsp_c, htrace_c, hvregs_c⟩
          have ⟨_, _, _, _, _, _, _⟩ := hacp_c
          rw [← A.pool_of_vmPreserved hvmc]
          have _hlr_sc : LsRetAddr624 (sc.readReg64 (Reg.gpr 30#5)) := by
            change LsRetAddr624 (sc.readReg64 .lr); rw [hlr_c]
            simp (config := { decide := true }) only [arm64_norm, wp_norm]
          wp_call hdealloc_fo (ptr, cap.toNat, 1, st)
          rw [hsp_c]
          have hacp' : AllocCallPreserved s0 sf := hacp_c.trans (by assumption)
          rcases hacp' with ⟨_, _, _, _, _, _, _⟩
          refine SepWP.focus_weaken (vnHeader_entails_memRegion_48 a cap ptr) (by sep_focus) ?_
          refine align_pre_st (by simp only [Reg.fp, Reg.lr, Reg.x19, Reg.x20, Reg.x21,
            wp_norm, arm64_norm]; try sep_ac_rfl) ?_
          wp_done
  · intro evs1 s1 hevs1 hpc1 hrun1 hcl1 ⟨⟨hx23_1, hx24_1, hx25_1, hx26_1, hx27_1, hx28_1, hsp_1, htrace_1, hvregs_1⟩, hacp_1, hx22_1, hx19_1⟩
    have ⟨_, _, _, _, _, _, _⟩ := hacp_1
    let st1 := M.stepEvents evs1 st
    refine seq_clean_evs_lscl hcl1 (mid := (blkPl_270).base + 112#64)
      (P_evs := fun evs sm =>
        (memRegion a 128 ∗ optProtoPqRatchetInnerAt A.repAlloc (a + 128#64) st_pb.inner) ∗
        optProtoInnerStateJumpTablePlacedAt ∗
        A.pool lim (M.stepEvents evs st1) sm ∗
        (memRegion (s0.sp - 4192#64) 48 ∗ stackAt (s0.sp - 48#64) allocHookStack) ∗
        (((s0.sp - 48#64) ↦₆₄ s0.readReg64 .fp) ∗ ((s0.sp - 40#64) ↦₆₄ s0.readReg64 .lr) ∗
         ((s0.sp - 32#64) ↦₆₄ s0.readReg64 .x21) ∗ ((s0.sp - 24#64) ↦₆₄ v_x21) ∗
         ((s0.sp - 16#64) ↦₆₄ s0.readReg64 .x20) ∗ ((s0.sp - 8#64) ↦₆₄ s0.readReg64 .x19)))
      (Q := fun sm => Saved48Preserved s0 sm (s0.sp - 48#64) ∧ AllocCallPreserved s0 sm ∧
        sm.readReg64 .x22 = s0.readReg64 .x22 ∧ sm.readReg64 .x19 = a) ?_ ?_
    · have hjoin128 : memRegion a 48 ∗ memRegion (a + 48#64) 80 ⊢ memRegion a 128 := by
        rw [ProofLib.memRegion_split a 48 80 (by decide)]; exact Entails.refl _
      cases hch : st_pb.chain with
      | none =>
        apply sepWP_evs_nil
        simp only [LibsignalBinary.Heap.AllocCostModel.stepEvents_nil]
        have h56 : (a + 48#64) + 8#64 = a + 56#64 := BitVec.add_assoc a 48#64 8#64
        dsimp only [optChainPBAt]; rw [h56]; wp_steps
        have hnone80 : ((a + 48#64) ↦₆₄ noneCap) ∗ memRegion (a + 56#64) 72 ⊢ memRegion (a + 48#64) 80 := by
          rw [← h56]; exact optChainPBAt_none_entails_memRegion_80 (a + 48#64)
        refine SepWP.focus_weaken hnone80 (by sep_focus) ?_
        refine SepWP.focus_weaken hjoin128 (by sep_focus) ?_
        refine sepWP_sync_pool s1 (by simp only [wp_norm, arm64_norm]) (by sep_focus) ?_
        refine align_pre_st (by sep_ac_rfl) ?_
        wp_done
      | some ch =>
        dsimp only [optChainPBAt]
        refine SepWP.focus_weaken (chainPBAt_entails_dealloc A.repAlloc (a + 48#64) ch) (by sep_focus) ?_
        wp_pull_exists; rename_i g; wp_focus_pure; rintro ⟨hlen_le, hcap_lt, hptr_ne⟩
        have hcap_lt_pow : g.links.cap.toNat < 2 ^ 63 := by omega
        have hlen_lt : ch.links.length * 112 < 2 ^ 63 := by
          have : ch.links.length * 112 ≤ g.links.cap.toNat * 112 := Nat.mul_le_mul_right 112 hlen_le
          omega
        have hne_none := cap_add_one_beq_zero_false hcap_lt_pow
        have h56 : (a + 48#64) + 8#64 = a + 56#64 := BitVec.add_assoc a 48#64 8#64
        have h64 : (a + 48#64) + 16#64 = a + 64#64 := BitVec.add_assoc a 48#64 16#64
        have h72 : (a + 48#64) + 24#64 = a + 72#64 := BitVec.add_assoc a 48#64 24#64
        have h80 : (a + 48#64) + 32#64 = a + 80#64 := BitVec.add_assoc a 48#64 32#64
        have h88 : (a + 48#64) + 40#64 = a + 88#64 := BitVec.add_assoc a 48#64 40#64
        refine seq_clean_evs (mid := (blkPl_270).base + 92#64)
          (P_evs := fun evs sm =>
            (memRegion a 48 ∗
              ((a + 48#64) ↦₆₄ g.links.cap) ∗ ((a + 56#64) ↦₆₄ g.links.ptr) ∗
              ((a + 64#64) ↦₆₄ BitVec.ofNat 64 ch.links.length) ∗
              ((a + 72#64) ↦₆₄ g.nextRoot.cap) ∗ ((a + 80#64) ↦₆₄ g.nextRoot.ptr) ∗
              memRegion (a + 88#64) 40 ∗ vecCapPtrDealloc A.repAlloc g.nextRoot.cap g.nextRoot.ptr ∗
              optProtoPqRatchetInnerAt A.repAlloc (a + 128#64) st_pb.inner) ∗
            optProtoInnerStateJumpTablePlacedAt ∗
            A.pool lim (M.stepEvents evs st1) sm ∗
            (memRegion (s0.sp - 4192#64) 48 ∗ stackAt (s0.sp - 48#64) allocHookStack) ∗
            (((s0.sp - 48#64) ↦₆₄ s0.readReg64 .fp) ∗ ((s0.sp - 40#64) ↦₆₄ s0.readReg64 .lr) ∗
             ((s0.sp - 32#64) ↦₆₄ s0.readReg64 .x21) ∗ ((s0.sp - 24#64) ↦₆₄ v_x21) ∗
             ((s0.sp - 16#64) ↦₆₄ s0.readReg64 .x20) ∗ ((s0.sp - 8#64) ↦₆₄ s0.readReg64 .x19)))
          (Q := fun sm => Saved48Preserved s0 sm (s0.sp - 48#64) ∧ AllocCallPreserved s0 sm ∧
            sm.readReg64 .x22 = s0.readReg64 .x22 ∧ sm.readReg64 .x19 = a) ?_ ?_
        · dsimp only [LibsignalBinary.Heap.RustCliAllocBudget.repAlloc_live]
          by_cases hc : g.links.cap = 0
          · have hnil : ch.links = [] := by rw [hc] at hlen_le; simp at hlen_le; exact hlen_le
            have hc_beq : (g.links.cap == 0#64) = true := by rw [beq_iff_eq]; exact hc
            have h0 : arrayAt (fun ep addr => chainEpochPBAt A.repAlloc addr ep) 112 g.links.ptr [] = emp := rfl
            simp only [hc, hnil, List.length_nil, Nat.zero_mul, BitVec.ofNat_eq_ofNat, ↓reduceIte, emp_sepConj, sepConj_emp]
            apply sepWP_seq_lscl hcl1 (mid := lsmpl.base 288)
            wp_steps
            apply SepWP.done (by wp_norm_lhs) (by wp_norm_lhs); intro hclc_s1
            have hslice_raw := drop_proto_epoch_slice_mem_on
              (callerProg := lsProg_270 (Rust.withPanics ext)) hdealloc hclc_s1
            dsimp only [lsProg_270, withMemEq, ProtoChainBudget.dropProtoEpochSliceSpec, chainEpochPBSize, BitVec.ofNat_eq_ofNat] at hslice_raw
            conv => arg 4; rw [← sepConj_emp ((a + 48#64) ↦₆₄ 0#64), ← h0]
            refine SepWP.focus_weaken (Entails.of_eq (stackAt_sub48_split_32 s0.sp)) (by sep_focus) ?_
            refine sepWP_sync_pool s1 (by simp only [wp_norm, arm64_norm]) (by sep_focus) ?_
            wp_call hslice_raw (⟨g.links.ptr, []⟩, st1)
            have hacp_cf : AllocCallPreserved s1 sf := by assumption
            have hevs_w : FreeOnlyEvs w := by assumption
            have hacp_f : AllocCallPreserved s0 sf := hacp_1.trans hacp_cf
            have ⟨_, _, _, _, _, _, _⟩ := hacp_f
            have hsp_eq : stackAt s1.sp dropStack32 = stackAt (s0.sp - 48#64) dropStack32 := by rw [hsp_1]
            refine SepWP.mono (post := fun sm Pm =>
                (Pm ⊢
                  (memRegion a 48 ∗
                    ((a + 48#64) ↦₆₄ 0#64) ∗ ((a + 56#64) ↦₆₄ g.links.ptr) ∗
                    ((a + 64#64) ↦₆₄ 0#64) ∗
                    ((a + 72#64) ↦₆₄ g.nextRoot.cap) ∗ ((a + 80#64) ↦₆₄ g.nextRoot.ptr) ∗
                    memRegion (a + 88#64) 40 ∗ vecCapPtrDealloc A.repAlloc g.nextRoot.cap g.nextRoot.ptr ∗
                    optProtoPqRatchetInnerAt A.repAlloc (a + 128#64) st_pb.inner) ∗
                  optProtoInnerStateJumpTablePlacedAt ∗
                  A.pool lim (M.stepEvents w st1) sm ∗
                  (memRegion (s0.sp - 4192#64) 48 ∗ stackAt (s0.sp - 48#64) allocHookStack) ∗
                  (((s0.sp - 48#64) ↦₆₄ s0.readReg64 .fp) ∗ ((s0.sp - 40#64) ↦₆₄ s0.readReg64 .lr) ∗
                   ((s0.sp - 32#64) ↦₆₄ s0.readReg64 .x21) ∗ ((s0.sp - 24#64) ↦₆₄ v_x21) ∗
                   ((s0.sp - 16#64) ↦₆₄ s0.readReg64 .x20) ∗ ((s0.sp - 8#64) ↦₆₄ s0.readReg64 .x19))) ∧
                Saved48Preserved s0 sm (s0.sp - 48#64) ∧ AllocCallPreserved s0 sm ∧
                sm.readReg64 .x22 = s0.readReg64 .x22 ∧ sm.readReg64 .x19 = a)
              ?_ (fun _ _ _ _ ⟨hp, hq⟩ =>
                ⟨w, hevs_w, Entails.trans hp (Entails.of_eq (by ac_rfl)), hq⟩)
            refine SepWP.focus_weaken (Entails.of_eq hsp_eq) (by sep_focus) ?_
            refine SepWP.focus_weaken (Entails.of_eq (stackAt_sub48_split_32 s0.sp).symm) (by sep_focus) ?_
            wp_steps
            refine sepWP_sync_pool sf (by simp only [wp_norm, arm64_norm]) (by sep_focus) ?_
            refine align_pre_st (by simp only [memRegion_zero, emp_sepConj, sepConj_emp, *]; sep_ac_rfl) ?_
            wp_done
          · have hc_beq : ¬((g.links.cap == 0#64) = true) := by rw [beq_iff_eq]; exact hc
            have hlsl := cap_lsl7_sub_lsl4 hcap_lt
            have hsplit : g.links.cap.toNat * 112 = ch.links.length * 112 + (g.links.cap.toNat - ch.links.length) * 112 := by
              rw [← Nat.add_mul]; congr 1; omega
            have hbound : ch.links.length * 112 + (g.links.cap.toNat - ch.links.length) * 112 ≤ 2 ^ 64 := by rw [← hsplit]; omega
            have hrejoin : memRegion g.links.ptr (ch.links.length * 112) ∗
                memRegion (g.links.ptr + BitVec.ofNat 64 (ch.links.length * 112)) ((g.links.cap.toNat - ch.links.length) * 112) ⊢
                memRegion g.links.ptr (g.links.cap.toNat * 112) := by
              rw [hsplit, ProofLib.memRegion_split g.links.ptr (ch.links.length * 112) ((g.links.cap.toNat - ch.links.length) * 112) hbound]
              exact Entails.refl _
            simp only [hc, ↓reduceIte]; apply sepWP_seq_lscl hcl1 (mid := lsmpl.base 288)
            wp_steps
            apply SepWP.done (by wp_norm_lhs) (by wp_norm_lhs); intro hclc_s2
            have hslice_raw := drop_proto_epoch_slice_mem_on
              (callerProg := lsProg_270 (Rust.withPanics ext)) hdealloc hclc_s2
            dsimp only [lsProg_270, withMemEq, ProtoChainBudget.dropProtoEpochSliceSpec, chainEpochPBSize, BitVec.ofNat_eq_ofNat] at hslice_raw
            refine SepWP.focus_weaken (Entails.of_eq (stackAt_sub48_split_32 s0.sp)) (by sep_focus) ?_
            refine sepWP_sync_pool s1 (by simp only [wp_norm, arm64_norm]) (by sep_focus) ?_
            wp_call hslice_raw (⟨g.links.ptr, ch.links⟩, st1)
            have hacp_cf1 : AllocCallPreserved s1 sf := by assumption
            have hevs_w : FreeOnlyEvs w := by assumption
            have hacp_f1 : AllocCallPreserved s0 sf := hacp_1.trans hacp_cf1
            have ⟨_, _, _, _, _, _, _⟩ := hacp_f1
            have hsp_eq : stackAt s1.sp dropStack32 = stackAt (s0.sp - 48#64) dropStack32 := by rw [hsp_1]
            refine SepWP.mono (post := fun sm Pm =>
                (Pm ⊢
                  (memRegion a 48 ∗
                    ((a + 48#64) ↦₆₄ g.links.cap) ∗ ((a + 56#64) ↦₆₄ g.links.ptr) ∗
                    ((a + 64#64) ↦₆₄ BitVec.ofNat 64 ch.links.length) ∗
                    ((a + 72#64) ↦₆₄ g.nextRoot.cap) ∗ ((a + 80#64) ↦₆₄ g.nextRoot.ptr) ∗
                    memRegion (a + 88#64) 40 ∗ vecCapPtrDealloc A.repAlloc g.nextRoot.cap g.nextRoot.ptr ∗
                    optProtoPqRatchetInnerAt A.repAlloc (a + 128#64) st_pb.inner) ∗
                  optProtoInnerStateJumpTablePlacedAt ∗
                  A.pool lim (M.stepEvents (rustDeallocEvents (g.links.cap.toNat * 112) 8) (M.stepEvents w st1)) sm ∗
                  (memRegion (s0.sp - 4192#64) 48 ∗ stackAt (s0.sp - 48#64) allocHookStack) ∗
                  (((s0.sp - 48#64) ↦₆₄ s0.readReg64 .fp) ∗ ((s0.sp - 40#64) ↦₆₄ s0.readReg64 .lr) ∗
                   ((s0.sp - 32#64) ↦₆₄ s0.readReg64 .x21) ∗ ((s0.sp - 24#64) ↦₆₄ v_x21) ∗
                   ((s0.sp - 16#64) ↦₆₄ s0.readReg64 .x20) ∗ ((s0.sp - 8#64) ↦₆₄ s0.readReg64 .x19))) ∧
                Saved48Preserved s0 sm (s0.sp - 48#64) ∧ AllocCallPreserved s0 sm ∧
                sm.readReg64 .x22 = s0.readReg64 .x22 ∧ sm.readReg64 .x19 = a)
              ?_ (fun _ _ _ _ ⟨hp, hq⟩ =>
                ⟨w ++ rustDeallocEvents (g.links.cap.toNat * 112) 8,
                  hevs_w.append (LibsignalBinary.Heap.FreeOnlyEvs.singleton 8 (g.links.cap.toNat * 112)),
                  Entails.trans hp (Entails.of_eq (by
                    simp only [LibsignalBinary.Heap.AllocCostModel.stepEvents_append]
                    try ac_rfl)),
                  hq⟩)
            refine SepWP.focus_weaken (Entails.of_eq hsp_eq) (by sep_focus) ?_
            refine SepWP.focus_weaken (Entails.of_eq (stackAt_sub48_split_32 s0.sp).symm) (by sep_focus) ?_
            refine SepWP.focus_weaken hrejoin (by sep_focus) ?_
            wp_steps
            refine sepWP_sync_pool sf (by simp only [wp_norm, arm64_norm]) (by sep_focus) ?_
            wp_call hdealloc_fo (g.links.ptr, g.links.cap.toNat * 112, 8, M.stepEvents w st1)
            have hacp_f2 : AllocCallPreserved s0 sf_1 := hacp_f1.trans (by assumption)
            have ⟨_, _, _, _, _, _, _⟩ := hacp_f2
            refine align_pre_st (by
              simp only [*, Reg.fp, Reg.lr, Reg.x19, Reg.x20, Reg.x21, wp_norm, arm64_norm]
              try sep_ac_rfl) ?_
            wp_done
        · intro evs_ch s2 hevs_ch hpc2 hrun2 ⟨⟨hx23_2, hx24_2, hx25_2, hx26_2, hx27_2, hx28_2, hsp_2, htrace_2, hvregs_2⟩, hacp_2, hx22_2, hx19_2⟩
          have ⟨_, _, _, _, _, _, _⟩ := hacp_2
          let st_ch := M.stepEvents evs_ch st1
          have hhdr80 : ((a + 48#64) ↦₆₄ g.links.cap) ∗ ((a + 56#64) ↦₆₄ g.links.ptr) ∗
              ((a + 64#64) ↦₆₄ BitVec.ofNat 64 ch.links.length) ∗
              ((a + 72#64) ↦₆₄ g.nextRoot.cap) ∗ ((a + 80#64) ↦₆₄ g.nextRoot.ptr) ∗
              memRegion (a + 88#64) 40 ⊢ memRegion (a + 48#64) 80 := by
            rw [← h56, ← h64, ← h72, ← h80, ← h88]
            exact chainPBHeaders_entails_memRegion_80 (a + 48#64) g.links.cap g.links.ptr
              (BitVec.ofNat 64 ch.links.length) g.nextRoot.cap g.nextRoot.ptr
          dsimp only [vecCapPtrDealloc, LibsignalBinary.Heap.RustCliAllocBudget.repAlloc_live]
          by_cases hnr : (g.nextRoot.cap == 0#64) = true <;>
            simp only [hnr, Bool.false_eq_true, ↓reduceIte, emp_sepConj, sepConj_emp]
          · refine SepWP.mono (post := fun sm Pm =>
                (Pm ⊢
                  (memRegion a 128 ∗ optProtoPqRatchetInnerAt A.repAlloc (a + 128#64) st_pb.inner) ∗
                  optProtoInnerStateJumpTablePlacedAt ∗
                  A.pool lim st_ch sm ∗
                  (memRegion (s0.sp - 4192#64) 48 ∗ stackAt (s0.sp - 48#64) allocHookStack) ∗
                  (((s0.sp - 48#64) ↦₆₄ s0.readReg64 .fp) ∗ ((s0.sp - 40#64) ↦₆₄ s0.readReg64 .lr) ∗
                   ((s0.sp - 32#64) ↦₆₄ s0.readReg64 .x21) ∗ ((s0.sp - 24#64) ↦₆₄ v_x21) ∗
                   ((s0.sp - 16#64) ↦₆₄ s0.readReg64 .x20) ∗ ((s0.sp - 8#64) ↦₆₄ s0.readReg64 .x19))) ∧
                Saved48Preserved s0 sm (s0.sp - 48#64) ∧ AllocCallPreserved s0 sm ∧
                sm.readReg64 .x22 = s0.readReg64 .x22 ∧ sm.readReg64 .x19 = a)
              ?_ (fun _ _ _ _ ⟨hp, hq⟩ =>
                ⟨evs_ch, hevs_ch, Entails.trans hp (Entails.of_eq (by ac_rfl)), hq⟩)
            wp_steps
            refine SepWP.focus_weaken hhdr80 (by sep_focus) ?_
            refine SepWP.focus_weaken hjoin128 (by sep_focus) ?_
            refine sepWP_sync_pool s2 (by simp only [wp_norm, arm64_norm]) (by sep_focus) ?_
            refine align_pre_st (by sep_ac_rfl) ?_
            wp_done
          · refine SepWP.mono (post := fun sm Pm =>
                (Pm ⊢
                  (memRegion a 128 ∗ optProtoPqRatchetInnerAt A.repAlloc (a + 128#64) st_pb.inner) ∗
                  optProtoInnerStateJumpTablePlacedAt ∗
                  A.pool lim (M.stepEvents (rustDeallocEvents g.nextRoot.cap.toNat 1) st_ch) sm ∗
                  (memRegion (s0.sp - 4192#64) 48 ∗ stackAt (s0.sp - 48#64) allocHookStack) ∗
                  (((s0.sp - 48#64) ↦₆₄ s0.readReg64 .fp) ∗ ((s0.sp - 40#64) ↦₆₄ s0.readReg64 .lr) ∗
                   ((s0.sp - 32#64) ↦₆₄ s0.readReg64 .x21) ∗ ((s0.sp - 24#64) ↦₆₄ v_x21) ∗
                   ((s0.sp - 16#64) ↦₆₄ s0.readReg64 .x20) ∗ ((s0.sp - 8#64) ↦₆₄ s0.readReg64 .x19))) ∧
                Saved48Preserved s0 sm (s0.sp - 48#64) ∧ AllocCallPreserved s0 sm ∧
                sm.readReg64 .x22 = s0.readReg64 .x22 ∧ sm.readReg64 .x19 = a)
              ?_ (fun _ _ _ _ ⟨hp, hq⟩ =>
                ⟨evs_ch ++ rustDeallocEvents g.nextRoot.cap.toNat 1,
                  hevs_ch.append (LibsignalBinary.Heap.FreeOnlyEvs.singleton 1 g.nextRoot.cap.toNat),
                  Entails.trans hp (Entails.of_eq (by
                    simp only [st_ch, LibsignalBinary.Heap.AllocCostModel.stepEvents_append]
                    try ac_rfl)),
                  hq⟩)
            wp_steps
            refine sepWP_sync_pool s2 (by simp only [wp_norm, arm64_norm]) (by sep_focus) ?_
            wp_call hdealloc_fo (g.nextRoot.ptr, g.nextRoot.cap.toNat, 1, st_ch)
            have hacp' : AllocCallPreserved s0 sf := hacp_2.trans (by assumption)
            have ⟨_, _, _, _, _, _, _⟩ := hacp'
            refine SepWP.focus_weaken hhdr80 (by sep_focus) ?_
            refine SepWP.focus_weaken hjoin128 (by sep_focus) ?_
            refine align_pre_st (by
              simp only [*, Reg.fp, Reg.lr, Reg.x19, Reg.x20, Reg.x21, wp_norm, arm64_norm]
              try sep_ac_rfl) ?_
            wp_done
    · intro evs2 s3 hevs2 hpc3 hrun3 hcl_s3 ⟨⟨hx23_3, hx24_3, hx25_3, hx26_3, hx27_3, hx28_3, hsp_3, htrace_3, hvregs_3⟩, hacp_3, hx22_3, hx19_3⟩
      have ⟨_, _, _, _, _, _, _⟩ := hacp_3
      let st2 := M.stepEvents evs2 st1
      have hjoin352 : memRegion a 128 ∗ memRegion (a + 128#64) 224 ⊢ memRegion a 352 := by
        rw [ProofLib.memRegion_split a 128 224 (by decide)]; exact Entails.refl _
      cases hinner : st_pb.inner with
      | none =>
        have h136 : (a + 128#64) + 8#64 = a + 136#64 := BitVec.add_assoc a 128#64 8#64
        dsimp only [optProtoPqRatchetInnerAt, none3Cap']; rw [h136]
        refine sepWP_close_drop
          (fun sf' => memRegion a 352 ∗ optProtoInnerStateJumpTablePlacedAt ∗
            A.pool lim st2 sf' ∗ stackAt s0.sp dropStack96)
          ?_ (fun sf' _Pf hp hsp_f htr_f hacp_f hcs_f => ⟨fun hm => ?_, hsp_f, hcs_f⟩)
        · wp_steps
          have hnone224 : ((a + 128#64) ↦₆₄ 0xfffffffffffffffd#64) ∗ memRegion (a + 136#64) 216 ⊢
              memRegion (a + 128#64) 224 := by
            rw [← h136]; exact optProtoPqRatchetInnerAt_none_entails_memRegion_224 (a + 128#64)
          refine SepWP.focus_weaken hnone224 (by sep_focus) ?_
          refine SepWP.focus_weaken hjoin352 (by sep_focus) ?_
          refine SepWP.focus_weaken (stack_restore_96_allocHook s0.sp (s0.readReg64 .fp) (s0.readReg64 .lr)
            (s0.readReg64 .x21) v_x21 (s0.readReg64 .x20) (s0.readReg64 .x19)) (by sep_focus) ?_
          refine sepWP_sync_pool s3 (by simp only [wp_norm, arm64_norm]) (by sep_focus) ?_
          wp_done
        · simp only [sepExists_sepConj_left, satisfies_sepExists]
          refine ⟨evs1 ++ evs2, ?_⟩
          simp only [sepConj_assoc, satisfies_pure_sepConj]
          refine ⟨⟨htr_f, hacp_f, hevs1.append hevs2⟩, ?_⟩
          have heq_st : M.stepEvents (evs1 ++ evs2) st = st2 := by
            simp only [st2, st1, LibsignalBinary.Heap.AllocCostModel.stepEvents_append]
          rw [heq_st]
          exact Satisfies.mono (Entails.trans (sepConj_mono_left hp) (Entails.of_eq (by sep_ac_rfl))) hm
      | some innerVal =>
        cases innerVal with
        | v1 v1 =>
          dsimp only [optProtoPqRatchetInnerAt]
          refine SepWP.focus_weaken
            (optProtoInnerStateAt_expose_word A.repAlloc (a + 128#64) v1.innerState)
            (by sep_focus) ?_
          wp_pull_exists; rename_i w; wp_focus_pure; intro hne3
          apply sepWP_seq_lscl hcl_s3 (mid := lsmpl.base 267)
          wp_steps
          apply SepWP.done (by wp_norm_lhs) (by wp_norm_lhs); intro hclc_in
          have hinner_raw := drop_opt_proto_inner_state_mem_on
            (callerProg := lsProg_270 (Rust.withPanics ext)) hdealloc hclc_in
          dsimp only [lsProg_270, withMemEq, dropOptProtoInnerStatePlacedSpec, optProtoInnerStateSize, BitVec.ofNat_eq_ofNat] at hinner_raw
          refine SepWP.focus_weaken
            (optProtoInnerStateAt_unexpose_word A.repAlloc (a + 128#64) w v1.innerState)
            (by sep_focus) ?_
          refine SepWP.focus_weaken (stack_restore_96_allocHook s0.sp (s0.readReg64 .fp) (s0.readReg64 .lr)
            (s0.readReg64 .x21) v_x21 (s0.readReg64 .x20) (s0.readReg64 .x19)) (by sep_focus) ?_
          refine sepWP_sync_pool s3 (by simp only [wp_norm, arm64_norm]) (by sep_focus) ?_
          wp_call hinner_raw (⟨a + 128#64, v1.innerState⟩, st2)
          have hacp_cf : AllocCallPreserved s3 sf := by assumption
          have hevs_in : FreeOnlyEvs w_1 := by assumption
          have hacp_f : AllocCallPreserved s0 sf := hacp_3.trans hacp_cf
          have ⟨_, _, _, _, _, _, _⟩ := hacp_f
          refine SepWP.focus_weaken hjoin352 (by sep_focus) ?_
          refine sepWP_close_drop
            (fun sf' => memRegion a 352 ∗ optProtoInnerStateJumpTablePlacedAt ∗
              A.pool lim (M.stepEvents w_1 st2) sf' ∗ stackAt s0.sp dropStack96)
            (by wp_done)
            (fun sf' _Pf hp hsp_f htr_f hacp_f' hcs_f => ⟨fun hm => ?_, hsp_f, hcs_f⟩)
          simp only [sepExists_sepConj_left, satisfies_sepExists]
          refine ⟨(evs1 ++ evs2) ++ w_1, ?_⟩
          simp only [sepConj_assoc, satisfies_pure_sepConj]
          refine ⟨⟨htr_f, hacp_f', (hevs1.append hevs2).append hevs_in⟩, ?_⟩
          have heq_st : M.stepEvents ((evs1 ++ evs2) ++ w_1) st = M.stepEvents w_1 st2 := by
            simp only [st2, st1, LibsignalBinary.Heap.AllocCostModel.stepEvents_append]
          rw [heq_st]
          exact Satisfies.mono (Entails.trans (sepConj_mono_left hp) (Entails.of_eq (by sep_ac_rfl))) hm


theorem drop_proto_pq_ratchet_state_cl_blockProgram [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {ext : String → Option (State → State)}
    (hdealloc : HookSat (Rust.withPanics ext) spqrRustDeallocSym
      (rustCliDeallocBudgetSpec M A lim)) :
    subroutine_ok (libsignalSessionLib.blockProgram lsmpl 270 (Rust.withPanics ext)) (lsmpl.base 270)
      (withLsCodeLoaded lsmpl (dropProtoPqRatchetStatePlacedSpec M A lim)) :=
  ls_to_blockProgram (drop_proto_pq_ratchet_state_cl_placed_ok hdealloc)

theorem drop_proto_pq_ratchet_state_cl_on [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {callerProg : Program} {idx : Nat} {ext : String → Option (State → State)}
    [IsLsBlockProg callerProg idx (Rust.withPanics ext)]
    (hdealloc : HookSat (Rust.withPanics ext) spqrRustDeallocSym
      (rustCliDeallocBudgetSpec M A lim))
    (hidx : idx < 619 := by decide) :
    subroutine_ok callerProg (lsmpl.base 270)
      (withLsCodeLoaded lsmpl (dropProtoPqRatchetStatePlacedSpec M A lim)) :=
  ls_subroutine_ok_of_block (drop_proto_pq_ratchet_state_cl_placed_ok hdealloc) hidx

theorem drop_proto_pq_ratchet_state_mem_on [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {callerProg : Program} {idx : Nat} {ext : String → Option (State → State)}
    [IsLsBlockProg callerProg idx (Rust.withPanics ext)] {m : Memory}
    (hdealloc : HookSat (Rust.withPanics ext) spqrRustDeallocSym
      (rustCliDeallocBudgetSpec M A lim))
    (hcl : LibsignalCodeLoaded lsmpl m) (hidx : idx < 619 := by decide) :
    subroutine_ok callerProg (lsmpl.base 270)
      (withMemEq m (dropProtoPqRatchetStatePlacedSpec M A lim)) :=
  lscall_blk_cl (drop_proto_pq_ratchet_state_cl_placed_ok hdealloc) hcl hidx

end LibsignalBinary.Proofs.SpqrV1.Drop.ProtoTopClPlacedBudget
