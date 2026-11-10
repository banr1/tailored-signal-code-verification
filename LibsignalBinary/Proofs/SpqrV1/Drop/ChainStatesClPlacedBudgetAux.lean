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
public import LibsignalBinary.Proofs.Placed.ElfLsRetAddr
public import LibsignalBinary.Proofs.SpqrV1.Drop.ChainEpochPlacedBudget
public import LibsignalBinary.Proofs.SpqrV1.Drop.ProtoChainBudget
public import LibsignalBinary.Proofs.SpqrV1.Drop.ProtoChunked2BudgetAux
public import LibsignalBinary.Proofs.SpqrV1.Drop.ProtoChunkedClPlacedBudgetAux
public import LibsignalBinary.Proofs.SpqrV1.Drop.UnchunkedBudget
public import LibsignalBinary.Proofs.SpqrV1.States.Recv.DropChunkedClPlacedBudgetAux
import LibsignalBinary.Proofs.Common.SharedHelpers
meta import LibsignalBinary.Proofs.Common.SharedHelpers -- shake: keep
import LibsignalBinary.Proofs.Placed.GenLsBlock
import LibsignalBinary.Proofs.SpqrV1.Alloc.SpqrAllocCodeSym
import ProofLib.SepLogic.WP.Apply
import ProofLib.SepLogic.WPp
import GeneratedLean.LibsignalSessionObj

/-!
# Budget-Threaded Code-Loaded Drop Glue for Chains (`266, 269, 287`) and `Ct1Sent` (`279`)

Proves `withLsCodeLoaded lsmpl` subroutine contracts under `RustCliAllocBudget M` (`FreeOnlyEvs`)
for Blocks `279`, `287`, `266`, and `269` from `rustCliDeallocBudgetSpec M A lim`.
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 400000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false

open CryptoGames.LibsignalSession (
  ShaCompress
)
open CryptoVerification (
  IsLsBlockProg LibsignalCodeLoaded LibsignalHooks LibsignalPlacement blkPC_136 blkPC_266
  blkPC_279 blkPC_282 blkPl_136 blkPl_266 blkPl_279 blkPl_282 extract_withLsCodeLoaded
  libsignalSessionLib lsProg_266 lsProg_279 lsProg_282 lsProg_283 lsProg_284 lsProg_285
  lsProg_286 ls_blockPlacement_base ls_subroutine_ok_of_block lscall_blk_cl lsmpl lsρ
  sepWP_seq_lscl subroutine_ok_withLsCodeLoaded_of_plain withLsCodeLoaded withMemEq
)
open CryptoVerification.LibsignalSpqrV1 (
  ChainEpoch ChainEpochPB ChainPB EpochDirectionPB pbToProtoPolyEncoder
)
open CryptoVerification.LibsignalTripleRatchetRepr (
  noneCap
)
open CryptoVerification.RustHeap (
  RustAlloc allocHookStack arrayAt
)
open CryptoVerification.SpqrV1.Alloc (
  spqr_hook_ok_of_mem
)
open CryptoVerification.SpqrV1.ChainProofs (
  chainEpoch chainEpochAlign chainEpochAt chainEpochSize chainSize vecDequeAt vecDequeHeader
  vecDequeRingBuf vecDequeSlotsAt
)
open CryptoVerification.SpqrV1.Drop (
  DropChainEpochSliceGhost DropOptProtoSpqrChainGhost DropProtoChunkedCt1ReceivedGhost
  DropProtoChunkedEkSentCt1ReceivedGhost DropProtoChunkedHeaderReceivedGhost
  DropProtoChunkedNoHeaderReceivedGhost DropProtoEpochSliceGhost DropProtoSpqrChainGhost
  DropProtoUnchunkedCt1SentEkReceivedGhost DropSpqrChainGhost Saved32x20Preserved
  Saved48Preserved add_112_add_56 add_sub_cancel_left_bv
  arrayAt_chainEpochAt_entails_chainEpoch auth48HeadersAt auth48HeadersAt_entails_memRegion_48
  cap_add_one_beq_zero_false cap_lsl7_sub_lsl4 chainAt_entails_dealloc chainEpochHeadersAt
  chainEpochHeadersAt_entails_memRegion_112 chainEpochPB_regions_entails_112
  chainEpoch_entails_dealloc chainHeaders_entails_memRegion_88 chainPBAt_entails_dealloc
  chainPBHeaders_entails_memRegion_80 cons_len_mul dropSpqrChainStack dropStack32 dropStack48
  dropStack80 epochDirPBHeadersAt epochDirPBHeadersAt_entails_memRegion_56
  epochDirectionPBAt_entails_dealloc mul_112_add_ptr none2Cap_add_two_beq_zero
  noneCap_add_two_beq_zero not_ule_sub_of_gt ofNat_add_one_beq_one_false_112
  ofNat_beq_zero_false_112 ofNat_sub_sub_eq ofNat_succ_eq_add_one
  optChainPBAt_none_entails_memRegion_80 optEpochDirectionPBAt_none_entails_memRegion_56
  optProtoAuthenticatorAt_48_none optProtoAuthenticatorAt_48_none_entails_memRegion_48
  optProtoAuthenticatorAt_some optProtoPolyEncoder_none_entails_memRegion_56
  optProtoPolynomialEncoderAt_none' optProtoPolynomialEncoderAt_some'
  optProtoUnchunked2Vec_none_entails_memRegion_104 optProtoUnchunkedEkSentCt1ReceivedAt_none
  optProtoUnchunkedEkSentCt1ReceivedAt_some protoAuthenticatorAt_entails_dealloc
  protoChunkedCt1ReceivedAt protoChunkedCt1ReceivedSize protoPolynomialEncoderAt_expose_cap
  protoPolynomialEncoderAt_unexpose_cap protoUnchunked2VecHeadersAt
  protoUnchunked2VecHeadersAt_entails_memRegion_104'
  protoUnchunkedEkSentCt1ReceivedAt_entails_dealloc sep_pull_body sep_push_body sep_rejoin_loop
  stackAt_allocHook16_split_bottom stackAt_dropStack32_split stackAt_dropStack32_split_bottom
  stackAt_dropStack48_split stackAt_dropStack48_split32 stackAt_dropStack48_split_bottom
  stackAt_dropStack80_split stackAt_dropStack80_split_bottom stack_restore_32_allocHook
  stack_restore_48_allocHook stack_restore_48_dropStack80 stack_restore_48_from_32
  sub_eq_ofNat_sub tail_len_mul_lt twoVecHeadersAt twoVecHeadersAt_48_eq ule_sub_of_le
  ult_of_toNat_lt vecCapPtrDealloc vecDequeSlotsAt_nil_entails_memRegion
  vecDequeSlotsAt_nonwrap_entails vecDequeSlotsAt_nonwrap_rejoin vecDequeSlotsAt_wrap_entails
  vecDequeSlotsAt_wrap_rejoin
)
open CryptoVerification.SpqrV1.Drop.Blk337_338 (
  blkPC_287 blkPC_288 blkPl_287 blkPl_288 lsProg_287 lsProg_288
)
open CryptoVerification.SpqrV1.Drop.ChainEpochPlaced (
  blkPC_269 blkPl_269 lsProg_269
)
open CryptoVerification.SpqrV1.Poly (
  optProtoPolynomialEncoderAt protoPolynomialEncoderAt protoPolynomialEncoderSize
)
open CryptoVerification.SpqrV1.ProtoRepr (
  chainEpochPBAt chainEpochPBSize chainPBAt chainPBSize epochDirectionPBAt optChainPBAt
  optEpochDirectionPBAt
)
open CryptoVerification.SpqrV1.States.Recv (
  spqrRustDeallocSym
)
open LibsignalBinary.Heap (
  AllocCallPreserved AllocCostModel AllocEvent BudgetLimits FreeOnlyEvs RustCliAllocBudget
  VmPreserved rustCliDeallocBudgetSpec rustDeallocEvents
)
open LibsignalBinary.Proofs.SpqrV1.Drop.ChainEpochBudget (
  dropChainEpochSliceSpec dropSpqrChainSpec
)
open LibsignalBinary.Proofs.SpqrV1.Drop.ChainEpochPlacedBudget (
  drop_chain_epoch_slice_local2_placed_ok_ext
)
open LibsignalBinary.Proofs.SpqrV1.Drop.ProtoChainBudget (
  dropOptProtoSpqrChainSpec dropProtoEpochSliceSpec
)
open LibsignalBinary.Proofs.SpqrV1.Drop.ProtoChunked2BudgetAux (
  align_pre_st align_pre_vm deallocFreeOnlySpec drop_proto_chunked_header_received_placed_ok
  sepWP_close_drop sepWP_evs_dealloc sepWP_evs_nil sepWP_vm_evs_nil seq_clean_evs seq_vm_clean
  subroutine_ok_deallocFreeOnly
)
open LibsignalBinary.Proofs.SpqrV1.Drop.ProtoChunkedClPlacedBudgetAux (
  drop_proto_epoch_slice_mem_on
)
open LibsignalBinary.Proofs.SpqrV1.Drop.ProtoPolyBudget (
  dropProtoPolyEncoderSpec
)
open LibsignalBinary.Proofs.SpqrV1.Drop.UnchunkedBudget (
  dropProtoUnchunkedCt1SentEkReceivedSpec dropUnchunkedCt1SentSpec
  drop_proto_unchunked_ct1_sent_ek_received_placed_ok drop_unchunked_ct1_sent_local2_placed_ok
)
open LibsignalBinary.Proofs.SpqrV1.States.Recv.DropChunkedClPlacedBudgetAux (
  ls_to_blockProgram seq_vm_clean_lscl subroutine_ok_withLsCodeLoaded_intro
)

namespace LibsignalBinary.Proofs.SpqrV1.Drop.ChainStatesClPlacedBudgetAux

open Arm64 ProofLib
open ProofLib.ProgramReflection

attribute [local irreducible] Program.fetch Program.externAt? Program.fnOff
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero

/-! ## Leaf Single-Block Wrappers (`279`, `287`) -/

theorem drop_unchunked_ct1_sent_local2_cl_placed_ok [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits} {F : ShaCompress}
    {ext : String → Option (State → State)}
    (hdealloc : HookSat (Rust.withPanics ext) spqrRustDeallocSym
      (rustCliDeallocBudgetSpec M A lim)) :
    subroutine_ok (lsProg_279 (Rust.withPanics ext)) (lsmpl.base 279)
      (withLsCodeLoaded lsmpl (dropUnchunkedCt1SentSpec M A lim F)) := by
  rw [← ls_blockPlacement_base (i := 279)]
  exact subroutine_ok_withLsCodeLoaded_of_plain
    (drop_unchunked_ct1_sent_local2_placed_ok (spqr_hook_ok_of_mem hdealloc))

theorem drop_unchunked_ct1_sent_local2_cl_blockProgram [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits} {F : ShaCompress}
    {ext : String → Option (State → State)}
    (hdealloc : HookSat (Rust.withPanics ext) spqrRustDeallocSym
      (rustCliDeallocBudgetSpec M A lim)) :
    subroutine_ok (libsignalSessionLib.blockProgram lsmpl 279 (Rust.withPanics ext)) (lsmpl.base 279)
      (withLsCodeLoaded lsmpl (dropUnchunkedCt1SentSpec M A lim F)) :=
  ls_to_blockProgram (drop_unchunked_ct1_sent_local2_cl_placed_ok hdealloc)

theorem drop_unchunked_ct1_sent_local2_cl_on [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits} {F : ShaCompress}
    {callerProg : Program} {idx : Nat} {ext : String → Option (State → State)}
    [IsLsBlockProg callerProg idx (Rust.withPanics ext)]
    (hdealloc : HookSat (Rust.withPanics ext) spqrRustDeallocSym
      (rustCliDeallocBudgetSpec M A lim))
    (hidx : idx < 619 := by decide) :
    subroutine_ok callerProg (lsmpl.base 279)
      (withLsCodeLoaded lsmpl (dropUnchunkedCt1SentSpec M A lim F)) :=
  ls_subroutine_ok_of_block (drop_unchunked_ct1_sent_local2_cl_placed_ok hdealloc) hidx

theorem drop_unchunked_ct1_sent_local2_mem_on [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits} {F : ShaCompress}
    {callerProg : Program} {idx : Nat} {ext : String → Option (State → State)}
    [IsLsBlockProg callerProg idx (Rust.withPanics ext)] {m : Memory}
    (hdealloc : HookSat (Rust.withPanics ext) spqrRustDeallocSym
      (rustCliDeallocBudgetSpec M A lim))
    (hcl : LibsignalCodeLoaded lsmpl m) (hidx : idx < 619 := by decide) :
    subroutine_ok callerProg (lsmpl.base 279)
      (withMemEq m (dropUnchunkedCt1SentSpec M A lim F)) :=
  lscall_blk_cl (drop_unchunked_ct1_sent_local2_cl_placed_ok hdealloc) hcl hidx

theorem drop_chain_epoch_slice_local2_cl_placed_ok [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {ext : String → Option (State → State)}
    (hdealloc : HookSat (Rust.withPanics ext) spqrRustDeallocSym
      (rustCliDeallocBudgetSpec M A lim)) :
    subroutine_ok (lsProg_287 (Rust.withPanics ext)) (lsmpl.base 287)
      (withLsCodeLoaded lsmpl (dropChainEpochSliceSpec M A lim)) := by
  rw [← ls_blockPlacement_base (i := 287)]
  exact subroutine_ok_withLsCodeLoaded_of_plain
    (drop_chain_epoch_slice_local2_placed_ok_ext (spqr_hook_ok_of_mem hdealloc))

theorem drop_chain_epoch_slice_local2_cl_blockProgram [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {ext : String → Option (State → State)}
    (hdealloc : HookSat (Rust.withPanics ext) spqrRustDeallocSym
      (rustCliDeallocBudgetSpec M A lim)) :
    subroutine_ok (libsignalSessionLib.blockProgram lsmpl 287 (Rust.withPanics ext)) (lsmpl.base 287)
      (withLsCodeLoaded lsmpl (dropChainEpochSliceSpec M A lim)) :=
  ls_to_blockProgram (drop_chain_epoch_slice_local2_cl_placed_ok hdealloc)

theorem drop_chain_epoch_slice_local2_cl_on [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {callerProg : Program} {idx : Nat} {ext : String → Option (State → State)}
    [IsLsBlockProg callerProg idx (Rust.withPanics ext)]
    (hdealloc : HookSat (Rust.withPanics ext) spqrRustDeallocSym
      (rustCliDeallocBudgetSpec M A lim))
    (hidx : idx < 619 := by decide) :
    subroutine_ok callerProg (lsmpl.base 287)
      (withLsCodeLoaded lsmpl (dropChainEpochSliceSpec M A lim)) :=
  ls_subroutine_ok_of_block (drop_chain_epoch_slice_local2_cl_placed_ok hdealloc) hidx

theorem drop_chain_epoch_slice_local2_mem_on [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {callerProg : Program} {idx : Nat} {ext : String → Option (State → State)}
    [IsLsBlockProg callerProg idx (Rust.withPanics ext)] {m : Memory}
    (hdealloc : HookSat (Rust.withPanics ext) spqrRustDeallocSym
      (rustCliDeallocBudgetSpec M A lim))
    (hcl : LibsignalCodeLoaded lsmpl m) (hidx : idx < 619 := by decide) :
    subroutine_ok callerProg (lsmpl.base 287)
      (withMemEq m (dropChainEpochSliceSpec M A lim)) :=
  lscall_blk_cl (drop_chain_epoch_slice_local2_cl_placed_ok hdealloc) hcl hidx

/-! ## Block `266`: `drop_glue::<Option<spqr::proto::pq_ratchet::Chain>>` -/

private theorem optChainPBAt_none (A : RustAlloc) (a : BitVec 64) :
    optChainPBAt A a none = ((a ↦₆₄ noneCap) ∗ memRegion (a + 8#64) 72) := rfl

private theorem optChainPBAt_some (A : RustAlloc) (a : BitVec 64) (ch : ChainPB) :
    optChainPBAt A a (some ch) = chainPBAt A a ch := rfl

theorem drop_opt_proto_spqr_chain_cl_placed_ok [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {ext : String → Option (State → State)}
    (hdealloc : HookSat (Rust.withPanics ext) spqrRustDeallocSym
      (rustCliDeallocBudgetSpec M A lim)) :
    subroutine_ok (lsProg_266 (Rust.withPanics ext)) (lsmpl.base 266)
      (withLsCodeLoaded lsmpl (dropOptProtoSpqrChainSpec M A lim)) := by
  rw [← ls_blockPlacement_base (i := 266)]
  change subroutine_ok ((blkPC_266).rebase (blkPl_266).base (Rust.withPanics ext)) (blkPl_266).base _
  apply subroutine_ok_withLsCodeLoaded_intro; intro m hcl
  have hdealloc_raw : subroutine_ok ((blkPC_266).rebase (blkPl_266).base (Rust.withPanics ext))
      (lsρ spqrRustDeallocSym) (rustCliDeallocBudgetSpec M A lim) :=
    spqr_hook_ok_of_mem (prog := lsProg_266 (Rust.withPanics ext)) hdealloc
  simp only [spqrRustDeallocSym] at hdealloc_raw
  have hdealloc_fo := subroutine_ok_deallocFreeOnly hdealloc_raw
  clear hdealloc_raw
  simp only [deallocFreeOnlySpec, rustCliDeallocBudgetSpec] at hdealloc_fo
  dsimp only [withMemEq, dropOptProtoSpqrChainSpec, chainPBSize, chainEpochPBSize, BitVec.ofNat_eq_ofNat] at hdealloc_fo ⊢
  wp_init x_st s0
  rcases x_st with ⟨⟨a, optCh⟩, st⟩
  have hm_eq : s0.mem = m := by assumption
  subst hm_eq
  dsimp only [DropOptProtoSpqrChainGhost.a, DropOptProtoSpqrChainGhost.optCh] at *
  nth_rw 1 [stackAt_dropStack80_split s0.sp]
  cells_unfold
  wp_pull_exists
  rename_i v_fp v_lr v_x22 v_x21 v_x20 v_x19
  have hfsp_align : ((s0.sp - 48#64) &&& 15#64 == 0#64) = true :=
    spAligned_sub s0.sp 48#64 (by assumption) (by decide)
  cases optCh with
  | none =>
    rw [optChainPBAt_none]
    refine seq_vm_clean (mid := s0.readReg64 .lr)
      (P_mid := memRegion a 80 ∗ A.pool lim st s0 ∗ stackAt s0.sp dropStack80)
      (Q := fun sf => sf.sp = s0.sp ∧ sf.trace = s0.trace ∧
        AllocCallPreserved s0 sf ∧ CalleeSavedPreserved s0 sf)
      ?_ ?_
    · by_vm_steps (
        wp_steps
        refine SepWP.focus_weaken (optChainPBAt_none_entails_memRegion_80 a) (by sep_focus) ?_
        refine SepWP.focus_weaken
          (stack_restore_48_dropStack80 s0.sp (s0.readReg64 .fp) (s0.readReg64 .lr)
            (s0.readReg64 .x21) v_x21 (s0.readReg64 .x20) (s0.readReg64 .x19)) (by sep_focus) ?_
        refine align_pre_vm (by sep_ac_rfl) ?_
        wp_done)
    · intro sf hpcf hrunf hvmf ⟨hsp_f, htr_f, hacp_f, hcs_f⟩
      rw [← A.pool_of_vmPreserved hvmf]
      apply SepWP.done hpcf hrunf
      refine ⟨fun hm => ?_, hsp_f, hcs_f⟩
      rw [satisfies_sepExists]; refine ⟨[], ?_⟩
      rw [satisfies_pure_sepConj]
      refine ⟨⟨htr_f, hacp_f, LibsignalBinary.Heap.FreeOnlyEvs.nil⟩, ?_⟩
      simp only [LibsignalBinary.Heap.AllocCostModel.stepEvents_nil]
      exact Satisfies.mono (Entails.of_eq (by sep_ac_rfl)) hm
  | some ch =>
    rw [optChainPBAt_some]
    refine SepWP.weaken_pre (sepConj_mono_left (chainPBAt_entails_dealloc A.repAlloc a ch)) ?_
    dsimp only [LibsignalBinary.Heap.RustCliAllocBudget.repAlloc_live]
    wp_pull_exists; rename_i g
    wp_focus_pure; rintro ⟨hlen_le, hcap_lt, hptr_ne⟩
    have hcap_lt_pow : g.links.cap.toNat < 2 ^ 63 := by omega
    have hlen_lt : ch.links.length * 112 < 2 ^ 63 := by
      have : ch.links.length * 112 ≤ g.links.cap.toNat * 112 := Nat.mul_le_mul_right 112 hlen_le; omega
    have hne_none := cap_add_one_beq_zero_false hcap_lt_pow
    refine seq_clean_evs (mid := (blkPl_266).base + 68#64)
      (P_evs := fun evs sm =>
        (a ↦₆₄ g.links.cap) ∗ ((a + 8#64) ↦₆₄ g.links.ptr) ∗
        ((a + 16#64) ↦₆₄ BitVec.ofNat 64 ch.links.length) ∗
        ((a + 24#64) ↦₆₄ g.nextRoot.cap) ∗ ((a + 32#64) ↦₆₄ g.nextRoot.ptr) ∗
        memRegion (a + 40#64) 40 ∗ vecCapPtrDealloc A.repAlloc g.nextRoot.cap g.nextRoot.ptr ∗
        A.pool lim (M.stepEvents evs st) sm ∗ stackAt (s0.sp - 48#64) dropStack32 ∗
        (((s0.sp - 48#64) ↦₆₄ s0.readReg64 .fp) ∗ ((s0.sp - 40#64) ↦₆₄ s0.readReg64 .lr) ∗
         ((s0.sp - 32#64) ↦₆₄ s0.readReg64 .x21) ∗ ((s0.sp - 24#64) ↦₆₄ v_x21) ∗
         ((s0.sp - 16#64) ↦₆₄ s0.readReg64 .x20) ∗ ((s0.sp - 8#64) ↦₆₄ s0.readReg64 .x19)))
      (Q := fun sm => Saved48Preserved s0 sm (s0.sp - 48#64) ∧ AllocCallPreserved s0 sm ∧
        sm.readReg64 .x19 = a ∧ sm.readReg64 .x22 = s0.readReg64 .x22)
      ?_ ?_
    · by_cases hc : g.links.cap = 0
      · have hnil : ch.links = [] := by rw [hc] at hlen_le; simp at hlen_le; exact hlen_le
        have hc_beq : (g.links.cap == 0#64) = true := by rw [beq_iff_eq]; exact hc
        have h0 : arrayAt (fun ep addr => chainEpochPBAt A.repAlloc addr ep) 112 g.links.ptr [] = emp := rfl
        simp only [hc, hnil, List.length_nil, Nat.zero_mul, BitVec.ofNat_eq_ofNat, ↓reduceIte,
          emp_sepConj, sepConj_emp]
        refine seq_vm_clean_lscl hcl (mid := lsmpl.base 288)
          (P_mid :=
            arrayAt (fun ep addr => chainEpochPBAt A.repAlloc addr ep) 112 g.links.ptr [] ∗
            A.pool lim st s0 ∗ stackAt (s0.sp - 48#64) dropStack32 ∗
            ((a ↦₆₄ 0#64) ∗ ((a + 8#64) ↦₆₄ g.links.ptr) ∗ ((a + 16#64) ↦₆₄ 0#64) ∗
             ((a + 24#64) ↦₆₄ g.nextRoot.cap) ∗ ((a + 32#64) ↦₆₄ g.nextRoot.ptr) ∗
             memRegion (a + 40#64) 40 ∗ vecCapPtrDealloc A.repAlloc g.nextRoot.cap g.nextRoot.ptr ∗
             (((s0.sp - 48#64) ↦₆₄ s0.readReg64 .fp) ∗ ((s0.sp - 40#64) ↦₆₄ s0.readReg64 .lr) ∗
              ((s0.sp - 32#64) ↦₆₄ s0.readReg64 .x21) ∗ ((s0.sp - 24#64) ↦₆₄ v_x21) ∗
              ((s0.sp - 16#64) ↦₆₄ s0.readReg64 .x20) ∗ ((s0.sp - 8#64) ↦₆₄ s0.readReg64 .x19))))
          (Q := fun sc => Saved48Preserved s0 sc (s0.sp - 48#64) ∧ AllocCallPreserved s0 sc ∧
            sc.readReg64 .x0 = g.links.ptr ∧ sc.readReg64 .x1 = 0#64 ∧
            sc.readReg64 .lr = (blkPl_266).base + 44#64 ∧
            sc.readReg64 .x19 = a ∧ sc.readReg64 .x20 = g.links.ptr ∧
            sc.readReg64 .x21 = 0#64 ∧ sc.readReg64 .x22 = s0.readReg64 .x22)
          ?_ ?_
        · by_vm_steps (
            wp_steps
            rw [← sepConj_emp (a ↦₆₄ 0#64), ← h0]
            refine align_pre_vm (by sep_ac_rfl) ?_
            wp_done)
        · intro sc hpcc hrunc hclc hvmc ⟨⟨_, _, _, _, _, _, hsp_c, _, _⟩, hacp_c, hx0_c, hx1_c, hlr_c, hx19_c, hx20_c, hx21_c, hx22_c⟩
          have hslice_raw := drop_proto_epoch_slice_mem_on
            (callerProg := lsProg_266 (Rust.withPanics ext)) hdealloc hclc
          dsimp only [lsProg_266, withMemEq, dropProtoEpochSliceSpec, chainEpochPBSize, BitVec.ofNat_eq_ofNat] at hslice_raw
          have ⟨_, _, _, _, _, _, _⟩ := hacp_c
          rw [← A.pool_of_vmPreserved hvmc, ← hsp_c]
          wp_call hslice_raw (⟨g.links.ptr, []⟩, st)
          rw [hsp_c]
          have hacp_s : AllocCallPreserved sc sf := by assumption
          have hevs_s : FreeOnlyEvs w := by assumption
          have hacp_cs : AllocCallPreserved s0 sf := hacp_c.trans hacp_s
          rcases hacp_cs with ⟨_, _, _, _, _, _, _⟩
          rcases hacp_s with ⟨_, _, _, _, _, _, _⟩
          refine SepWP.mono (post := fun sm Pm =>
              (Pm ⊢
                (a ↦₆₄ 0#64) ∗ ((a + 8#64) ↦₆₄ g.links.ptr) ∗
                ((a + 16#64) ↦₆₄ 0#64) ∗
                ((a + 24#64) ↦₆₄ g.nextRoot.cap) ∗ ((a + 32#64) ↦₆₄ g.nextRoot.ptr) ∗
                memRegion (a + 40#64) 40 ∗ vecCapPtrDealloc A.repAlloc g.nextRoot.cap g.nextRoot.ptr ∗
                A.pool lim (M.stepEvents w st) sm ∗ stackAt (s0.sp - 48#64) dropStack32 ∗
                (((s0.sp - 48#64) ↦₆₄ s0.readReg64 .fp) ∗ ((s0.sp - 40#64) ↦₆₄ s0.readReg64 .lr) ∗
                 ((s0.sp - 32#64) ↦₆₄ s0.readReg64 .x21) ∗ ((s0.sp - 24#64) ↦₆₄ v_x21) ∗
                 ((s0.sp - 16#64) ↦₆₄ s0.readReg64 .x20) ∗ ((s0.sp - 8#64) ↦₆₄ s0.readReg64 .x19))) ∧
              Saved48Preserved s0 sm (s0.sp - 48#64) ∧ AllocCallPreserved s0 sm ∧
              sm.readReg64 .x19 = a ∧ sm.readReg64 .x22 = s0.readReg64 .x22)
            ?_ (fun _ _ _ _ ⟨hp, hq⟩ => ⟨w, hevs_s, hp, hq⟩)
          wp_steps
          refine align_pre_st
            (by simp only [LibsignalBinary.Heap.RustCliAllocBudget.pool_setPC]
                try simp only [memRegion_zero, emp_sepConj, sepConj_emp, *]
                sep_ac_rfl) ?_
          wp_done
      · have hc_beq : ¬((g.links.cap == 0#64) = true) := by rw [beq_iff_eq]; exact hc
        have hlsl := cap_lsl7_sub_lsl4 hcap_lt
        have hsp_sub : s0.sp - 4176#64 = (s0.sp - 48#64) - 4128#64 := by bv_omega
        have hsplit : g.links.cap.toNat * 112 =
            ch.links.length * 112 + (g.links.cap.toNat - ch.links.length) * 112 := by
          rw [← Nat.add_mul]; congr 1; omega
        have hbound : ch.links.length * 112 + (g.links.cap.toNat - ch.links.length) * 112 ≤ 2 ^ 64 := by
          rw [← hsplit]; omega
        have hrejoin :
            memRegion g.links.ptr (ch.links.length * 112) ∗
              memRegion (g.links.ptr + BitVec.ofNat 64 (ch.links.length * 112))
                ((g.links.cap.toNat - ch.links.length) * 112) ⊢
            memRegion g.links.ptr (g.links.cap.toNat * 112) := by
          rw [hsplit, ProofLib.memRegion_split g.links.ptr (ch.links.length * 112)
                ((g.links.cap.toNat - ch.links.length) * 112) hbound]
          exact Entails.refl _
        simp only [hc, ↓reduceIte]
        refine seq_vm_clean_lscl hcl (mid := lsmpl.base 288)
          (P_mid :=
            arrayAt (fun ep addr => chainEpochPBAt A.repAlloc addr ep) 112 g.links.ptr ch.links ∗
            A.pool lim st s0 ∗ stackAt (s0.sp - 48#64) dropStack32 ∗
            ((a ↦₆₄ g.links.cap) ∗ ((a + 8#64) ↦₆₄ g.links.ptr) ∗
             ((a + 16#64) ↦₆₄ BitVec.ofNat 64 ch.links.length) ∗
             A.live g.links.ptr (g.links.cap.toNat * 112) 8 ∗
             memRegion (g.links.ptr + BitVec.ofNat 64 (ch.links.length * 112))
               ((g.links.cap.toNat - ch.links.length) * 112) ∗
             ((a + 24#64) ↦₆₄ g.nextRoot.cap) ∗ ((a + 32#64) ↦₆₄ g.nextRoot.ptr) ∗
             memRegion (a + 40#64) 40 ∗ vecCapPtrDealloc A.repAlloc g.nextRoot.cap g.nextRoot.ptr ∗
             (((s0.sp - 48#64) ↦₆₄ s0.readReg64 .fp) ∗ ((s0.sp - 40#64) ↦₆₄ s0.readReg64 .lr) ∗
              ((s0.sp - 32#64) ↦₆₄ s0.readReg64 .x21) ∗ ((s0.sp - 24#64) ↦₆₄ v_x21) ∗
              ((s0.sp - 16#64) ↦₆₄ s0.readReg64 .x20) ∗ ((s0.sp - 8#64) ↦₆₄ s0.readReg64 .x19))))
          (Q := fun sc => Saved48Preserved s0 sc (s0.sp - 48#64) ∧ AllocCallPreserved s0 sc ∧
            sc.readReg64 .x0 = g.links.ptr ∧
            sc.readReg64 .x1 = BitVec.ofNat 64 ch.links.length ∧
            sc.readReg64 .lr = (blkPl_266).base + 44#64 ∧
            sc.readReg64 .x19 = a ∧ sc.readReg64 .x20 = g.links.ptr ∧
            sc.readReg64 .x21 = g.links.cap ∧ sc.readReg64 .x22 = s0.readReg64 .x22)
          ?_ ?_
        · by_vm_steps (wp_steps; refine align_pre_vm (by sep_ac_rfl) ?_; wp_done)
        · intro sc hpcc hrunc hclc hvmc ⟨⟨_, _, _, _, _, _, hsp_c, _, _⟩, hacp_c, hx0_c, hx1_c, hlr_c, hx19_c, hx20_c, hx21_c, hx22_c⟩
          have hslice_raw := drop_proto_epoch_slice_mem_on
            (callerProg := lsProg_266 (Rust.withPanics ext)) hdealloc hclc
          dsimp only [lsProg_266, withMemEq, dropProtoEpochSliceSpec, chainEpochPBSize, BitVec.ofNat_eq_ofNat] at hslice_raw
          have ⟨_, _, _, _, _, _, _⟩ := hacp_c
          rw [← A.pool_of_vmPreserved hvmc, ← hsp_c]
          wp_call hslice_raw (⟨g.links.ptr, ch.links⟩, st)
          rw [hsp_c]
          have hacp_s : AllocCallPreserved sc sf := by assumption
          have hevs_s : FreeOnlyEvs w := by assumption
          have hacp_cs : AllocCallPreserved s0 sf := hacp_c.trans hacp_s
          have ⟨_, _, _, _, _, _, _⟩ := hacp_cs
          have ⟨_, _, _, _, _, _, _⟩ := hacp_s
          refine SepWP.focus_weaken hrejoin (by sep_focus) ?_
          conv => arg 4; rw [stackAt_dropStack32_split_bottom (s0.sp - 48#64)]
          wp_steps
          wp_call hdealloc_fo (g.links.ptr, g.links.cap.toNat * 112, 8, M.stepEvents w st)
          have hacp_d : AllocCallPreserved s0 sf_1 := hacp_cs.trans (by assumption)
          rcases hacp_d with ⟨_, _, _, _, _, _, _⟩
          refine SepWP.mono (post := fun sm Pm =>
              (Pm ⊢
                (a ↦₆₄ g.links.cap) ∗ ((a + 8#64) ↦₆₄ g.links.ptr) ∗
                ((a + 16#64) ↦₆₄ BitVec.ofNat 64 ch.links.length) ∗
                ((a + 24#64) ↦₆₄ g.nextRoot.cap) ∗ ((a + 32#64) ↦₆₄ g.nextRoot.ptr) ∗
                memRegion (a + 40#64) 40 ∗ vecCapPtrDealloc A.repAlloc g.nextRoot.cap g.nextRoot.ptr ∗
                A.pool lim (M.stepEvents (w ++ rustDeallocEvents (g.links.cap.toNat * 112) 8) st) sm ∗
                stackAt (s0.sp - 48#64) dropStack32 ∗
                (((s0.sp - 48#64) ↦₆₄ s0.readReg64 .fp) ∗ ((s0.sp - 40#64) ↦₆₄ s0.readReg64 .lr) ∗
                 ((s0.sp - 32#64) ↦₆₄ s0.readReg64 .x21) ∗ ((s0.sp - 24#64) ↦₆₄ v_x21) ∗
                 ((s0.sp - 16#64) ↦₆₄ s0.readReg64 .x20) ∗ ((s0.sp - 8#64) ↦₆₄ s0.readReg64 .x19))) ∧
              Saved48Preserved s0 sm (s0.sp - 48#64) ∧ AllocCallPreserved s0 sm ∧
              sm.readReg64 .x19 = a ∧ sm.readReg64 .x22 = s0.readReg64 .x22)
            ?_ (fun _ _ _ _ ⟨hp, hq⟩ =>
              ⟨w ++ rustDeallocEvents (g.links.cap.toNat * 112) 8,
                hevs_s.append (LibsignalBinary.Heap.FreeOnlyEvs.singleton 8 (g.links.cap.toNat * 112)),
                hp, hq⟩)
          simp only [LibsignalBinary.Heap.AllocCostModel.stepEvents_append]
          refine align_pre_st (by
            try simp only [hsp_sf, hsp_c, hsp_sub, stackAt_dropStack32_split_bottom (s0.sp - 48#64), *]
            sep_ac_rfl) ?_
          wp_done
    · intro evs1 s1 hevs1 hpc1 hrun1 ⟨⟨hx23_1, hx24_1, hx25_1, hx26_1, hx27_1, hx28_1, hsp_1, htrace_1, hvregs_1⟩, hacp_1, hx19_1, hx22_1⟩
      have ⟨_, _, _, _, _, _, _⟩ := hacp_1
      let st1 := M.stepEvents evs1 st
      dsimp only [vecCapPtrDealloc, LibsignalBinary.Heap.RustCliAllocBudget.repAlloc_live]
      by_cases hnr : (g.nextRoot.cap == 0#64) = true <;>
        simp only [hnr, ↓reduceIte, emp_sepConj, sepConj_emp]
      · refine sepWP_close_drop
          (fun sf => memRegion a 80 ∗
            A.pool lim (M.stepEvents evs1 st) sf ∗ stackAt s0.sp dropStack80) ?_
          (fun sf _Pf hp hsp_f htr_f hacp_f hcs_f => ⟨fun hm => ?_, hsp_f, hcs_f⟩)
        · wp_steps
          refine SepWP.focus_weaken
            (chainPBHeaders_entails_memRegion_80 a g.links.cap g.links.ptr
              (BitVec.ofNat 64 ch.links.length) g.nextRoot.cap g.nextRoot.ptr) (by sep_focus) ?_
          refine SepWP.focus_weaken
            (stack_restore_48_dropStack80 s0.sp (s0.readReg64 .fp) (s0.readReg64 .lr)
              (s0.readReg64 .x21) v_x21 (s0.readReg64 .x20) (s0.readReg64 .x19)) (by sep_focus) ?_
          wp_done
        · rw [satisfies_sepExists]; refine ⟨evs1, ?_⟩
          rw [satisfies_pure_sepConj]; refine ⟨⟨htr_f, hacp_f, hevs1⟩, ?_⟩
          exact Satisfies.mono (Entails.trans (sepConj_mono_left hp) (Entails.of_eq (by sep_ac_rfl))) hm
      · refine sepWP_close_drop
          (fun sf => memRegion a 80 ∗
            A.pool lim (M.stepEvents (evs1 ++ rustDeallocEvents g.nextRoot.cap.toNat 1) st) sf ∗
            stackAt s0.sp dropStack80) ?_
          (fun sf _Pf hp hsp_f htr_f hacp_f hcs_f => ⟨fun hm => ?_, hsp_f, hcs_f⟩)
        · have heq_st2 : M.stepEvents (evs1 ++ rustDeallocEvents g.nextRoot.cap.toNat 1) st =
              M.stepEvents (rustDeallocEvents g.nextRoot.cap.toNat 1) st1 := by
            simp only [st1, LibsignalBinary.Heap.AllocCostModel.stepEvents_append]
          rw [heq_st2]
          have htail : SepWP ((blkPC_266).rebase (blkPl_266).base (Rust.withPanics ext)) (s0.readReg64 .lr) s1
              ((a ↦₆₄ g.links.cap) ∗ ((a + 8#64) ↦₆₄ g.links.ptr) ∗
                ((a + 16#64) ↦₆₄ BitVec.ofNat 64 ch.links.length) ∗
                ((a + 24#64) ↦₆₄ g.nextRoot.cap) ∗ ((a + 32#64) ↦₆₄ g.nextRoot.ptr) ∗
                memRegion (a + 40#64) 40 ∗
                (A.live g.nextRoot.ptr g.nextRoot.cap.toNat 1 ∗
                  memRegion g.nextRoot.ptr g.nextRoot.cap.toNat) ∗
                A.pool lim st1 s1 ∗ stackAt (s0.sp - 48#64) dropStack32 ∗
                (((s0.sp - 48#64) ↦₆₄ s0.readReg64 .fp) ∗ ((s0.sp - 40#64) ↦₆₄ s0.readReg64 .lr) ∗
                 ((s0.sp - 32#64) ↦₆₄ s0.readReg64 .x21) ∗ ((s0.sp - 24#64) ↦₆₄ v_x21) ∗
                 ((s0.sp - 16#64) ↦₆₄ s0.readReg64 .x20) ∗ ((s0.sp - 8#64) ↦₆₄ s0.readReg64 .x19)))
              (fun sf Pf =>
                (Pf ⊢ memRegion a 80 ∗
                  A.pool lim (M.stepEvents (rustDeallocEvents g.nextRoot.cap.toNat 1) st1) sf ∗
                  stackAt s0.sp dropStack80) ∧
                sf.sp = s0.sp ∧ sf.trace = s0.trace ∧
                AllocCallPreserved s1 sf ∧ CalleeSavedPreserved s0 sf) := by
            wp_steps
            refine SepWP.focus_weaken
              (chainPBHeaders_entails_memRegion_80 a g.links.cap g.links.ptr
                (BitVec.ofNat 64 ch.links.length) g.nextRoot.cap g.nextRoot.ptr) (by sep_focus) ?_
            refine SepWP.focus_weaken
              (stack_restore_48_dropStack80 s0.sp (s0.readReg64 .fp) (s0.readReg64 .lr)
                (s0.readReg64 .x21) v_x21 (s0.readReg64 .x20) (s0.readReg64 .x19)) (by sep_focus) ?_
            rw [stackAt_dropStack80_split_bottom s0.sp]
            wp_call hdealloc_fo (g.nextRoot.ptr, g.nextRoot.cap.toNat, 1, st1)
            have hpost1 : AllocCallPreserved s1 sf := by assumption
            rcases hpost1 with ⟨_, _, _, _, _, _, _⟩
            wp_done
          exact SepWP.mono htail fun _ _ _ _ ⟨hp, hsp_f, htr_f, hacp_1f, hcs_f⟩ =>
            ⟨hp, hsp_f, htr_f, hacp_1.trans hacp_1f, hcs_f⟩
        · rw [satisfies_sepExists]; refine ⟨evs1 ++ rustDeallocEvents g.nextRoot.cap.toNat 1, ?_⟩
          rw [satisfies_pure_sepConj]
          refine ⟨⟨htr_f, hacp_f, hevs1.append (LibsignalBinary.Heap.FreeOnlyEvs.singleton 1 g.nextRoot.cap.toNat)⟩, ?_⟩
          exact Satisfies.mono (Entails.trans (sepConj_mono_left hp) (Entails.of_eq (by sep_ac_rfl))) hm


theorem drop_opt_proto_spqr_chain_cl_blockProgram [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {ext : String → Option (State → State)}
    (hdealloc : HookSat (Rust.withPanics ext) spqrRustDeallocSym
      (rustCliDeallocBudgetSpec M A lim)) :
    subroutine_ok (libsignalSessionLib.blockProgram lsmpl 266 (Rust.withPanics ext)) (lsmpl.base 266)
      (withLsCodeLoaded lsmpl (dropOptProtoSpqrChainSpec M A lim)) :=
  ls_to_blockProgram (drop_opt_proto_spqr_chain_cl_placed_ok hdealloc)

theorem drop_opt_proto_spqr_chain_cl_on [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {callerProg : Program} {idx : Nat} {ext : String → Option (State → State)}
    [IsLsBlockProg callerProg idx (Rust.withPanics ext)]
    (hdealloc : HookSat (Rust.withPanics ext) spqrRustDeallocSym
      (rustCliDeallocBudgetSpec M A lim))
    (hidx : idx < 619 := by decide) :
    subroutine_ok callerProg (lsmpl.base 266)
      (withLsCodeLoaded lsmpl (dropOptProtoSpqrChainSpec M A lim)) :=
  ls_subroutine_ok_of_block (drop_opt_proto_spqr_chain_cl_placed_ok hdealloc) hidx

theorem drop_opt_proto_spqr_chain_mem_on [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {callerProg : Program} {idx : Nat} {ext : String → Option (State → State)}
    [IsLsBlockProg callerProg idx (Rust.withPanics ext)] {m : Memory}
    (hdealloc : HookSat (Rust.withPanics ext) spqrRustDeallocSym
      (rustCliDeallocBudgetSpec M A lim))
    (hcl : LibsignalCodeLoaded lsmpl m) (hidx : idx < 619 := by decide) :
    subroutine_ok callerProg (lsmpl.base 266)
      (withMemEq m (dropOptProtoSpqrChainSpec M A lim)) :=
  lscall_blk_cl (drop_opt_proto_spqr_chain_cl_placed_ok hdealloc) hcl hidx

/-! ## Block `269`: `drop_glue::<spqr::chain::Chain>` -/

theorem drop_spqr_chain_cl_placed_ok [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {ext : String → Option (State → State)}
    (hdealloc : HookSat (Rust.withPanics ext) spqrRustDeallocSym
      (rustCliDeallocBudgetSpec M A lim)) :
    subroutine_ok (lsProg_269 (Rust.withPanics ext)) (lsmpl.base 269)
      (withLsCodeLoaded lsmpl (dropSpqrChainSpec M A lim)) := by
  rw [← ls_blockPlacement_base (i := 269)]
  change subroutine_ok ((blkPC_269).rebase (blkPl_269).base (Rust.withPanics ext)) (blkPl_269).base _
  apply subroutine_ok_withLsCodeLoaded_intro; intro m hcl
  have hdealloc_raw : subroutine_ok ((blkPC_269).rebase (blkPl_269).base (Rust.withPanics ext))
      (lsρ spqrRustDeallocSym) (rustCliDeallocBudgetSpec M A lim) :=
    spqr_hook_ok_of_mem (prog := lsProg_269 (Rust.withPanics ext)) hdealloc
  simp only [spqrRustDeallocSym] at hdealloc_raw
  have hdealloc_fo := subroutine_ok_deallocFreeOnly hdealloc_raw
  clear hdealloc_raw
  simp only [deallocFreeOnlySpec, rustCliDeallocBudgetSpec] at hdealloc_fo
  dsimp only [withMemEq, dropSpqrChainSpec, chainSize, dropSpqrChainStack, BitVec.ofNat_eq_ofNat] at hdealloc_fo ⊢
  wp_init x_st s0
  rcases x_st with ⟨⟨a, G, c⟩, st⟩
  have hm_eq : s0.mem = m := by assumption
  subst hm_eq
  dsimp only [DropSpqrChainGhost.a, DropSpqrChainGhost.G, DropSpqrChainGhost.c] at *
  refine SepWP.weaken_pre (sepConj_mono_left (chainAt_entails_dealloc A.repAlloc a G c)) ?_
  unfold vecDequeAt vecDequeRingBuf vecDequeHeader
  nth_rw 1 [stackAt_dropStack80_split s0.sp]
  cells_unfold
  wp_pull_exists
  wp_focus_pure
  rintro ⟨hlen_le, hcap_lt, hptr_ne, hhead⟩
  have hfsp_align : ((s0.sp - 48#64) &&& 15#64 == 0#64) = true :=
    spAligned_sub s0.sp 48#64 (by assumption) (by decide)
  dsimp only [chainEpochSize, chainEpochAlign, LibsignalBinary.Heap.RustCliAllocBudget.repAlloc_live] at hcap_lt ⊢
  refine seq_clean_evs (mid := (blkPl_269).base + 120#64)
    (P_evs := fun evs sm =>
      vecDequeHeader a G.linksCap G.linksPtr G.linksHead
        (BitVec.ofNat 64 (G.epochs.zip c.links).length) ∗
      (if G.linksCap = 0 then emp
       else A.live G.linksPtr (G.linksCap.toNat * 112) 8 ∗
         memRegion G.linksPtr (G.linksCap.toNat * 112)) ∗
      ((a + 32#64) ↦₆₄ G.nextRoot.cap) ∗ ((a + 40#64) ↦₆₄ G.nextRoot.ptr) ∗
      memRegion (a + 48#64) 40 ∗
      vecCapPtrDealloc A.repAlloc G.nextRoot.cap G.nextRoot.ptr ∗
      A.pool lim (M.stepEvents evs st) sm ∗
      stackAt (s0.sp - 48#64) dropStack32 ∗
      (((s0.sp - 48#64) ↦₆₄ s0.readReg64 .fp) ∗ ((s0.sp - 40#64) ↦₆₄ s0.readReg64 .lr) ∗
       ((s0.sp - 32#64) ↦₆₄ s0.readReg64 .x22) ∗ ((s0.sp - 24#64) ↦₆₄ s0.readReg64 .x21) ∗
       ((s0.sp - 16#64) ↦₆₄ s0.readReg64 .x20) ∗ ((s0.sp - 8#64) ↦₆₄ s0.readReg64 .x19)))
    (Q := fun sm => Saved48Preserved s0 sm (s0.sp - 48#64) ∧ AllocCallPreserved s0 sm ∧
      sm.readReg64 .x19 = a ∧ sm.readReg64 .x21 = G.linksPtr ∧ sm.readReg64 .x22 = G.linksCap)
    ?_ ?_
  · generalize hxs : G.epochs.zip c.links = xs at hlen_le ⊢
    cases xs with
    | nil =>
      have h0 : arrayAt (chainEpoch A.repAlloc) 112 G.linksPtr [] = emp := rfl
      have hnil_ent :
          (if G.linksCap = 0 then emp
           else A.live G.linksPtr (G.linksCap.toNat * 112) 8 ∗
             vecDequeSlotsAt (chainEpochAt A.repAlloc) 112 G.linksCap.toNat G.linksHead.toNat G.linksPtr [] 0 G.linksCap.toNat) ⊢
          (if G.linksCap = 0 then emp
           else A.live G.linksPtr (G.linksCap.toNat * 112) 8 ∗
             memRegion G.linksPtr (G.linksCap.toNat * 112)) := by
        by_cases hc : G.linksCap = 0
        · simp [hc]; exact Entails.refl _
        · simp only [hc, ↓reduceIte]
          exact sepConj_mono_right (vecDequeSlotsAt_nil_entails_memRegion
            (chainEpochAt A.repAlloc) 112 G.linksCap.toNat G.linksHead.toNat G.linksPtr hcap_lt)
      refine SepWP.focus_weaken hnil_ent (by sep_focus) ?_
      simp only [List.length_nil, Nat.zero_mul, BitVec.ofNat_eq_ofNat]
      refine seq_vm_clean_lscl hcl (mid := lsmpl.base 287)
        (P_mid :=
          arrayAt (chainEpoch A.repAlloc) 112 G.linksPtr [] ∗
          A.pool lim st s0 ∗ stackAt (s0.sp - 48#64) dropStack32 ∗
          ((if G.linksCap = 0 then emp
            else A.live G.linksPtr (G.linksCap.toNat * 112) 8 ∗
              memRegion G.linksPtr (G.linksCap.toNat * 112)) ∗
           (a ↦₆₄ G.linksCap) ∗ ((a + 8#64) ↦₆₄ G.linksPtr) ∗
           ((a + 16#64) ↦₆₄ G.linksHead) ∗ ((a + 24#64) ↦₆₄ 0#64) ∗
           ((a + 32#64) ↦₆₄ G.nextRoot.cap) ∗ ((a + 40#64) ↦₆₄ G.nextRoot.ptr) ∗
           memRegion (a + 48#64) 40 ∗
           vecCapPtrDealloc A.repAlloc G.nextRoot.cap G.nextRoot.ptr ∗
           (((s0.sp - 48#64) ↦₆₄ s0.readReg64 .fp) ∗ ((s0.sp - 40#64) ↦₆₄ s0.readReg64 .lr) ∗
            ((s0.sp - 32#64) ↦₆₄ s0.readReg64 .x22) ∗ ((s0.sp - 24#64) ↦₆₄ s0.readReg64 .x21) ∗
            ((s0.sp - 16#64) ↦₆₄ s0.readReg64 .x20) ∗ ((s0.sp - 8#64) ↦₆₄ s0.readReg64 .x19))))
        (Q := fun sc => Saved48Preserved s0 sc (s0.sp - 48#64) ∧ AllocCallPreserved s0 sc ∧
          sc.readReg64 .x0 = G.linksPtr ∧ sc.readReg64 .x1 = 0#64 ∧
          sc.readReg64 .lr = (blkPl_269).base + 108#64 ∧
          sc.readReg64 .x19 = a ∧ sc.readReg64 .x20 = 0#64 ∧
          sc.readReg64 .x21 = G.linksPtr ∧ sc.readReg64 .x22 = G.linksCap)
        ?_ ?_
      · by_vm_steps (
          wp_steps
          refine align_pre_vm (by dsimp only [Reg.fp, Reg.lr, Reg.x22, Reg.x21, Reg.x20, Reg.x19]; rw [h0, emp_sepConj]; sep_ac_rfl) ?_
          wp_done)
      · intro sc hpcc hrunc hclc hvmc ⟨⟨_, _, _, _, _, _, hsp_c, _, _⟩, hacp_c, hx0_c, hx1_c, hlr_c, hx19_c, hx20_c, hx21_c, hx22_c⟩
        have hslice_raw1 := drop_chain_epoch_slice_local2_mem_on
          (callerProg := lsProg_269 (Rust.withPanics ext)) hdealloc hclc
        dsimp only [lsProg_269, withMemEq, dropChainEpochSliceSpec, BitVec.ofNat_eq_ofNat] at hslice_raw1
        have hsp_c_align : (sc.sp &&& 15#64 == 0#64) = true := hsp_c ▸ hfsp_align
        have ⟨_, _, _, _, _, _, _⟩ := hacp_c
        rw [← A.pool_of_vmPreserved hvmc, ← hsp_c]
        apply sepWP_seq_lscl hclc (mid := (blkPl_269).base + 108#64)
        wp_call hslice_raw1 (⟨G.linksPtr, []⟩, st)
        apply SepWP.done (by wp_norm_lhs) (by wp_norm_lhs); intro hclc_ret
        rw [hsp_c]
        have hacp_s1 : AllocCallPreserved sc sf := by assumption
        have hevs_s1 : FreeOnlyEvs w := by assumption
        have hacp_1 : AllocCallPreserved s0 sf := hacp_c.trans hacp_s1
        have ⟨_, _, _, _, _, _, _⟩ := hacp_s1
        apply sepWP_seq_lscl hclc_ret (mid := lsmpl.base 287)
        wp_steps
        apply SepWP.done (by wp_norm_lhs) (by wp_norm_lhs); intro hclc2
        have hslice_raw2 := drop_chain_epoch_slice_local2_mem_on
          (callerProg := lsProg_269 (Rust.withPanics ext)) hdealloc hclc2
        dsimp only [lsProg_269, withMemEq, dropChainEpochSliceSpec, BitVec.ofNat_eq_ofNat] at hslice_raw2
        rw [← sepConj_emp (a ↦₆₄ G.linksCap), ← h0]
        wp_call hslice_raw2 (⟨G.linksPtr, []⟩, M.stepEvents w st)
        have hacp_s2 : AllocCallPreserved sf sf_1 := by assumption
        have hevs_s2 : FreeOnlyEvs w_1 := by assumption
        have hacp_2 : AllocCallPreserved s0 sf_1 := hacp_1.trans hacp_s2
        rcases hacp_2 with ⟨_, _, _, _, _, _, _⟩
        rcases hacp_s2 with ⟨_, _, _, _, _, _, _⟩
        refine SepWP.mono (post := fun sm Pm =>
            (Pm ⊢
              vecDequeHeader a G.linksCap G.linksPtr G.linksHead 0#64 ∗
              (if G.linksCap = 0 then emp
               else A.live G.linksPtr (G.linksCap.toNat * 112) 8 ∗
                 memRegion G.linksPtr (G.linksCap.toNat * 112)) ∗
              ((a + 32#64) ↦₆₄ G.nextRoot.cap) ∗ ((a + 40#64) ↦₆₄ G.nextRoot.ptr) ∗
              memRegion (a + 48#64) 40 ∗
              vecCapPtrDealloc A.repAlloc G.nextRoot.cap G.nextRoot.ptr ∗
              A.pool lim (M.stepEvents (w ++ w_1) st) sm ∗
              stackAt (s0.sp - 48#64) dropStack32 ∗
              (((s0.sp - 48#64) ↦₆₄ s0.readReg64 .fp) ∗ ((s0.sp - 40#64) ↦₆₄ s0.readReg64 .lr) ∗
               ((s0.sp - 32#64) ↦₆₄ s0.readReg64 .x22) ∗ ((s0.sp - 24#64) ↦₆₄ s0.readReg64 .x21) ∗
               ((s0.sp - 16#64) ↦₆₄ s0.readReg64 .x20) ∗ ((s0.sp - 8#64) ↦₆₄ s0.readReg64 .x19))) ∧
            Saved48Preserved s0 sm (s0.sp - 48#64) ∧ AllocCallPreserved s0 sm ∧
            sm.readReg64 .x19 = a ∧ sm.readReg64 .x21 = G.linksPtr ∧ sm.readReg64 .x22 = G.linksCap)
          ?_ (fun _ _ _ _ ⟨hp, hq⟩ => ⟨w ++ w_1, hevs_s1.append hevs_s2, hp, hq⟩)
        simp only [LibsignalBinary.Heap.AllocCostModel.stepEvents_append]
        refine align_pre_st (by
          unfold vecDequeHeader
          simp only [List.length_nil, BitVec.ofNat_eq_ofNat, memRegion_zero, emp_sepConj, sepConj_emp,
            Nat.mul_comm, h0, *]
          sep_ac_rfl) ?_
        wp_done
    | cons x tl =>
      have hlen_pos : 0 < (x :: tl).length := by simp
      have hlen_lt : (x :: tl).length * 112 < 2 ^ 63 := by
        have : (x :: tl).length * 112 ≤ G.linksCap.toNat * 112 := Nat.mul_le_mul_right 112 hlen_le
        omega
      have hcap_lt_pow : G.linksCap.toNat < 2 ^ 63 := by omega
      have hne0 := ofNat_beq_zero_false_112 hlen_pos hlen_lt
      have hcap_ne : G.linksCap ≠ 0 := by
        intro hc0; rw [hc0] at hlen_le; simp at hlen_le
      simp only [hcap_ne, ↓reduceIte] at hhead ⊢
      have hult : G.linksHead.ult G.linksCap = true := ult_of_toNat_lt hhead
      have haddr1 : G.linksPtr + BitVec.ofNat 64 (G.linksHead.toNat * 112) =
          G.linksPtr + G.linksHead * 112#64 := by
        rw [← mul_112_add_ptr, BitVec.add_comm]
      by_cases hwrap : (x :: tl).length ≤ G.linksCap.toNat - G.linksHead.toNat
      · have hule := ule_sub_of_le hcap_lt_pow hhead hwrap
        obtain ⟨ys, hys_len, hys_ent⟩ := vecDequeSlotsAt_nonwrap_entails
          (chainEpochAt A.repAlloc) 112 G.linksCap.toNat G.linksHead.toNat G.linksPtr (x :: tl) hcap_lt hhead hwrap
        let eps := ys.map Prod.snd
        have heps_len : eps.length = (x :: tl).length := by simp [eps, hys_len]
        have heps_lt : eps.length * 112 < 2 ^ 63 := by rw [heps_len]; exact hlen_lt
        have hx1_eq : G.linksHead + BitVec.ofNat 64 (x :: tl).length - G.linksHead =
            BitVec.ofNat 64 eps.length := by
          rw [add_sub_cancel_left_bv, heps_len]
        have h0 : arrayAt (chainEpoch A.repAlloc) 112 G.linksPtr [] = emp := rfl
        have hent_ep :
            vecDequeSlotsAt (chainEpochAt A.repAlloc) 112 G.linksCap.toNat G.linksHead.toNat G.linksPtr (x :: tl) 0 G.linksCap.toNat ⊢
            arrayAt (chainEpoch A.repAlloc) 112 (G.linksPtr + G.linksHead * 112#64) eps ∗
            memRegion G.linksPtr (G.linksHead.toNat * 112) ∗
            memRegion (G.linksPtr + BitVec.ofNat 64 ((G.linksHead.toNat + (x :: tl).length) * 112))
              ((G.linksCap.toNat - G.linksHead.toNat - (x :: tl).length) * 112) := by
          rw [← haddr1]
          exact Entails.trans hys_ent (sepConj_mono_left (arrayAt_chainEpochAt_entails_chainEpoch A.repAlloc _ ys))
        refine SepWP.focus_weaken hent_ep (by sep_focus) ?_
        refine seq_vm_clean_lscl hcl (mid := lsmpl.base 287)
          (P_mid :=
            arrayAt (chainEpoch A.repAlloc) 112 (G.linksPtr + G.linksHead * 112#64) eps ∗
            A.pool lim st s0 ∗ stackAt (s0.sp - 48#64) dropStack32 ∗
            (memRegion G.linksPtr (G.linksHead.toNat * 112) ∗
             memRegion (G.linksPtr + BitVec.ofNat 64 ((G.linksHead.toNat + (x :: tl).length) * 112))
               ((G.linksCap.toNat - G.linksHead.toNat - (x :: tl).length) * 112) ∗
             (a ↦₆₄ G.linksCap) ∗ ((a + 8#64) ↦₆₄ G.linksPtr) ∗
             ((a + 16#64) ↦₆₄ G.linksHead) ∗ ((a + 24#64) ↦₆₄ BitVec.ofNat 64 (x :: tl).length) ∗
             A.live G.linksPtr (G.linksCap.toNat * 112) 8 ∗
             ((a + 32#64) ↦₆₄ G.nextRoot.cap) ∗ ((a + 40#64) ↦₆₄ G.nextRoot.ptr) ∗
             memRegion (a + 48#64) 40 ∗
             vecCapPtrDealloc A.repAlloc G.nextRoot.cap G.nextRoot.ptr ∗
             (((s0.sp - 48#64) ↦₆₄ s0.readReg64 .fp) ∗ ((s0.sp - 40#64) ↦₆₄ s0.readReg64 .lr) ∗
              ((s0.sp - 32#64) ↦₆₄ s0.readReg64 .x22) ∗ ((s0.sp - 24#64) ↦₆₄ s0.readReg64 .x21) ∗
              ((s0.sp - 16#64) ↦₆₄ s0.readReg64 .x20) ∗ ((s0.sp - 8#64) ↦₆₄ s0.readReg64 .x19))))
          (Q := fun sc => Saved48Preserved s0 sc (s0.sp - 48#64) ∧ AllocCallPreserved s0 sc ∧
            sc.readReg64 .x0 = G.linksPtr + G.linksHead * 112#64 ∧
            sc.readReg64 .x1 = BitVec.ofNat 64 (x :: tl).length ∧
            sc.readReg64 .lr = (blkPl_269).base + 108#64 ∧
            sc.readReg64 .x19 = a ∧ sc.readReg64 .x20 = 0#64 ∧
            sc.readReg64 .x21 = G.linksPtr ∧ sc.readReg64 .x22 = G.linksCap)
          ?_ ?_
        · by_vm_steps (wp_steps; refine align_pre_vm (by dsimp only [Reg.fp, Reg.lr, Reg.x22, Reg.x21, Reg.x20, Reg.x19]; sep_ac_rfl) ?_; wp_done)
        · intro sc hpcc hrunc hclc hvmc ⟨⟨_, _, _, _, _, _, hsp_c, _, _⟩, hacp_c, hx0_c, hx1_c, hlr_c, hx19_c, hx20_c, hx21_c, hx22_c⟩
          have hslice_raw1 := drop_chain_epoch_slice_local2_mem_on
            (callerProg := lsProg_269 (Rust.withPanics ext)) hdealloc hclc
          dsimp only [lsProg_269, withMemEq, dropChainEpochSliceSpec, BitVec.ofNat_eq_ofNat] at hslice_raw1
          have hsp_c_align : (sc.sp &&& 15#64 == 0#64) = true := hsp_c ▸ hfsp_align
          rw [← heps_len] at hx1_c
          have ⟨_, _, _, _, _, _, _⟩ := hacp_c
          rw [← A.pool_of_vmPreserved hvmc, ← hsp_c]
          apply sepWP_seq_lscl hclc (mid := (blkPl_269).base + 108#64)
          wp_call hslice_raw1 (⟨G.linksPtr + G.linksHead * 112#64, eps⟩, st)
          apply SepWP.done (by wp_norm_lhs) (by wp_norm_lhs); intro hclc_ret
          rw [hsp_c]
          have hacp_s1 : AllocCallPreserved sc sf := by assumption
          have hevs_s1 : FreeOnlyEvs w := by assumption
          have hacp_1 : AllocCallPreserved s0 sf := hacp_c.trans hacp_s1
          have ⟨_, _, _, _, _, _, _⟩ := hacp_s1
          apply sepWP_seq_lscl hclc_ret (mid := lsmpl.base 287)
          wp_steps
          apply SepWP.done (by wp_norm_lhs) (by wp_norm_lhs); intro hclc2
          have hslice_raw2 := drop_chain_epoch_slice_local2_mem_on
            (callerProg := lsProg_269 (Rust.withPanics ext)) hdealloc hclc2
          dsimp only [lsProg_269, withMemEq, dropChainEpochSliceSpec, BitVec.ofNat_eq_ofNat] at hslice_raw2
          rw [← sepConj_emp (a ↦₆₄ G.linksCap), ← h0]
          wp_call hslice_raw2 (⟨G.linksPtr, []⟩, M.stepEvents w st)
          have hacp_s2 : AllocCallPreserved sf sf_1 := by assumption
          have hevs_s2 : FreeOnlyEvs w_1 := by assumption
          have hacp_2 : AllocCallPreserved s0 sf_1 := hacp_1.trans hacp_s2
          rcases hacp_2 with ⟨_, _, _, _, _, _, _⟩
          rcases hacp_s2 with ⟨_, _, _, _, _, _, _⟩
          rw [← haddr1, heps_len]
          refine SepWP.focus_weaken
            (vecDequeSlotsAt_nonwrap_rejoin 112 G.linksCap.toNat G.linksHead.toNat (x :: tl).length
              G.linksPtr hcap_lt hhead hwrap) (by sep_focus) ?_
          refine SepWP.mono (post := fun sm Pm =>
              (Pm ⊢
                vecDequeHeader a G.linksCap G.linksPtr G.linksHead (BitVec.ofNat 64 (x :: tl).length) ∗
                (A.live G.linksPtr (G.linksCap.toNat * 112) 8 ∗
                  memRegion G.linksPtr (G.linksCap.toNat * 112)) ∗
                ((a + 32#64) ↦₆₄ G.nextRoot.cap) ∗ ((a + 40#64) ↦₆₄ G.nextRoot.ptr) ∗
                memRegion (a + 48#64) 40 ∗
                vecCapPtrDealloc A.repAlloc G.nextRoot.cap G.nextRoot.ptr ∗
                A.pool lim (M.stepEvents (w ++ w_1) st) sm ∗
                stackAt (s0.sp - 48#64) dropStack32 ∗
                (((s0.sp - 48#64) ↦₆₄ s0.readReg64 .fp) ∗ ((s0.sp - 40#64) ↦₆₄ s0.readReg64 .lr) ∗
                 ((s0.sp - 32#64) ↦₆₄ s0.readReg64 .x22) ∗ ((s0.sp - 24#64) ↦₆₄ s0.readReg64 .x21) ∗
                 ((s0.sp - 16#64) ↦₆₄ s0.readReg64 .x20) ∗ ((s0.sp - 8#64) ↦₆₄ s0.readReg64 .x19))) ∧
              Saved48Preserved s0 sm (s0.sp - 48#64) ∧ AllocCallPreserved s0 sm ∧
              sm.readReg64 .x19 = a ∧ sm.readReg64 .x21 = G.linksPtr ∧ sm.readReg64 .x22 = G.linksCap)
            ?_ (fun _ _ _ _ ⟨hp, hq⟩ => ⟨w ++ w_1, hevs_s1.append hevs_s2, hp, hq⟩)
          simp only [LibsignalBinary.Heap.AllocCostModel.stepEvents_append]
          refine align_pre_st (by
            unfold vecDequeHeader
            simp only [chainEpochSize, chainEpochAlign, Nat.mul_comm, memRegion_zero, emp_sepConj, sepConj_emp, *]
            sep_ac_rfl) ?_
          wp_done
      · have hgt : G.linksCap.toNat - G.linksHead.toNat < (x :: tl).length := by omega
        have hnule := not_ule_sub_of_gt hcap_lt_pow hhead hlen_le hgt
        obtain ⟨ys₁, ys₂, hys₁_len, hys₂_len, hys_ent⟩ := vecDequeSlotsAt_wrap_entails
          (chainEpochAt A.repAlloc) 112 G.linksCap.toNat G.linksHead.toNat G.linksPtr (x :: tl) hcap_lt hhead hlen_le hgt
        let eps₁ := ys₁.map Prod.snd
        let eps₂ := ys₂.map Prod.snd
        have heps₁_len : eps₁.length = G.linksCap.toNat - G.linksHead.toNat := by simp [eps₁, hys₁_len]
        have heps₂_len : eps₂.length = (x :: tl).length - (G.linksCap.toNat - G.linksHead.toNat) := by
          simp [eps₂, hys₂_len]
        have heps₁_lt : eps₁.length * 112 < 2 ^ 63 := by
          rw [heps₁_len]
          have : (G.linksCap.toNat - G.linksHead.toNat) * 112 ≤ G.linksCap.toNat * 112 :=
            Nat.mul_le_mul_right 112 (by omega)
          omega
        have heps₂_lt : eps₂.length * 112 < 2 ^ 63 := by
          rw [heps₂_len]
          have : ((x :: tl).length - (G.linksCap.toNat - G.linksHead.toNat)) * 112 ≤ (x :: tl).length * 112 :=
            Nat.mul_le_mul_right 112 (by omega)
          omega
        have hent_ep :
            vecDequeSlotsAt (chainEpochAt A.repAlloc) 112 G.linksCap.toNat G.linksHead.toNat G.linksPtr (x :: tl) 0 G.linksCap.toNat ⊢
            arrayAt (chainEpoch A.repAlloc) 112 (G.linksPtr + G.linksHead * 112#64) eps₁ ∗
            arrayAt (chainEpoch A.repAlloc) 112 G.linksPtr eps₂ ∗
            memRegion (G.linksPtr + BitVec.ofNat 64 (((x :: tl).length - (G.linksCap.toNat - G.linksHead.toNat)) * 112))
              ((G.linksHead.toNat - ((x :: tl).length - (G.linksCap.toNat - G.linksHead.toNat))) * 112) := by
          rw [← haddr1]
          exact Entails.trans hys_ent
            (sepConj_mono (arrayAt_chainEpochAt_entails_chainEpoch A.repAlloc _ ys₁)
              (sepConj_mono_left (arrayAt_chainEpochAt_entails_chainEpoch A.repAlloc _ ys₂)))
        refine SepWP.focus_weaken hent_ep (by sep_focus) ?_
        refine seq_vm_clean_lscl hcl (mid := lsmpl.base 287)
          (P_mid :=
            arrayAt (chainEpoch A.repAlloc) 112 (G.linksPtr + G.linksHead * 112#64) eps₁ ∗
            A.pool lim st s0 ∗ stackAt (s0.sp - 48#64) dropStack32 ∗
            (arrayAt (chainEpoch A.repAlloc) 112 G.linksPtr eps₂ ∗
             memRegion (G.linksPtr + BitVec.ofNat 64 (((x :: tl).length - (G.linksCap.toNat - G.linksHead.toNat)) * 112))
               ((G.linksHead.toNat - ((x :: tl).length - (G.linksCap.toNat - G.linksHead.toNat))) * 112) ∗
             (a ↦₆₄ G.linksCap) ∗ ((a + 8#64) ↦₆₄ G.linksPtr) ∗
             ((a + 16#64) ↦₆₄ G.linksHead) ∗ ((a + 24#64) ↦₆₄ BitVec.ofNat 64 (x :: tl).length) ∗
             A.live G.linksPtr (G.linksCap.toNat * 112) 8 ∗
             ((a + 32#64) ↦₆₄ G.nextRoot.cap) ∗ ((a + 40#64) ↦₆₄ G.nextRoot.ptr) ∗
             memRegion (a + 48#64) 40 ∗
             vecCapPtrDealloc A.repAlloc G.nextRoot.cap G.nextRoot.ptr ∗
             (((s0.sp - 48#64) ↦₆₄ s0.readReg64 .fp) ∗ ((s0.sp - 40#64) ↦₆₄ s0.readReg64 .lr) ∗
              ((s0.sp - 32#64) ↦₆₄ s0.readReg64 .x22) ∗ ((s0.sp - 24#64) ↦₆₄ s0.readReg64 .x21) ∗
              ((s0.sp - 16#64) ↦₆₄ s0.readReg64 .x20) ∗ ((s0.sp - 8#64) ↦₆₄ s0.readReg64 .x19))))
          (Q := fun sc => Saved48Preserved s0 sc (s0.sp - 48#64) ∧ AllocCallPreserved s0 sc ∧
            sc.readReg64 .x0 = G.linksPtr + G.linksHead * 112#64 ∧
            sc.readReg64 .x1 = G.linksCap - G.linksHead ∧
            sc.readReg64 .lr = (blkPl_269).base + 108#64 ∧
            sc.readReg64 .x19 = a ∧
            sc.readReg64 .x20 = BitVec.ofNat 64 (x :: tl).length - (G.linksCap - G.linksHead) ∧
            sc.readReg64 .x21 = G.linksPtr ∧ sc.readReg64 .x22 = G.linksCap)
          ?_ ?_
        · by_vm_steps (wp_steps; refine align_pre_vm (by dsimp only [Reg.fp, Reg.lr, Reg.x22, Reg.x21, Reg.x20, Reg.x19]; sep_ac_rfl) ?_; wp_done)
        · intro sc hpcc hrunc hclc hvmc ⟨⟨_, _, _, _, _, _, hsp_c, _, _⟩, hacp_c, hx0_c, hx1_c, hlr_c, hx19_c, hx20_c, hx21_c, hx22_c⟩
          have hslice_raw1 := drop_chain_epoch_slice_local2_mem_on
            (callerProg := lsProg_269 (Rust.withPanics ext)) hdealloc hclc
          dsimp only [lsProg_269, withMemEq, dropChainEpochSliceSpec, BitVec.ofNat_eq_ofNat] at hslice_raw1
          have hsp_c_align : (sc.sp &&& 15#64 == 0#64) = true := hsp_c ▸ hfsp_align
          have hx1_1 : G.linksCap - G.linksHead = BitVec.ofNat 64 eps₁.length := by
            rw [heps₁_len, sub_eq_ofNat_sub (by omega)]
          rw [hx1_1] at hx1_c
          have ⟨_, _, _, _, _, _, _⟩ := hacp_c
          rw [← A.pool_of_vmPreserved hvmc, ← hsp_c]
          apply sepWP_seq_lscl hclc (mid := (blkPl_269).base + 108#64)
          wp_call hslice_raw1 (⟨G.linksPtr + G.linksHead * 112#64, eps₁⟩, st)
          apply SepWP.done (by wp_norm_lhs) (by wp_norm_lhs); intro hclc_ret
          rw [hsp_c]
          have hacp_s1 : AllocCallPreserved sc sf := by assumption
          have hevs_s1 : FreeOnlyEvs w := by assumption
          have hacp_1 : AllocCallPreserved s0 sf := hacp_c.trans hacp_s1
          have ⟨_, _, _, _, _, _, _⟩ := hacp_s1
          apply sepWP_seq_lscl hclc_ret (mid := lsmpl.base 287)
          wp_steps
          apply SepWP.done (by wp_norm_lhs) (by wp_norm_lhs); intro hclc2
          have hslice_raw2 := drop_chain_epoch_slice_local2_mem_on
            (callerProg := lsProg_269 (Rust.withPanics ext)) hdealloc hclc2
          dsimp only [lsProg_269, withMemEq, dropChainEpochSliceSpec, BitVec.ofNat_eq_ofNat] at hslice_raw2
          have hx1_2 : BitVec.ofNat 64 (x :: tl).length - (G.linksCap - G.linksHead) =
              BitVec.ofNat 64 eps₂.length := by
            rw [heps₂_len, ofNat_sub_sub_eq hcap_lt_pow hhead (by omega) hlen_le]
          wp_call hslice_raw2 (⟨G.linksPtr, eps₂⟩, M.stepEvents w st)
          have hacp_s2 : AllocCallPreserved sf sf_1 := by assumption
          have hevs_s2 : FreeOnlyEvs w_1 := by assumption
          have hacp_2 : AllocCallPreserved s0 sf_1 := hacp_1.trans hacp_s2
          rcases hacp_2 with ⟨_, _, _, _, _, _, _⟩
          rcases hacp_s2 with ⟨_, _, _, _, _, _, _⟩
          rw [← haddr1, heps₁_len, heps₂_len]
          refine SepWP.focus_weaken
            (vecDequeSlotsAt_wrap_rejoin 112 G.linksCap.toNat G.linksHead.toNat (x :: tl).length
              G.linksPtr hcap_lt hhead hlen_le hgt) (by sep_focus) ?_
          refine SepWP.mono (post := fun sm Pm =>
              (Pm ⊢
                vecDequeHeader a G.linksCap G.linksPtr G.linksHead (BitVec.ofNat 64 (x :: tl).length) ∗
                (A.live G.linksPtr (G.linksCap.toNat * 112) 8 ∗
                  memRegion G.linksPtr (G.linksCap.toNat * 112)) ∗
                ((a + 32#64) ↦₆₄ G.nextRoot.cap) ∗ ((a + 40#64) ↦₆₄ G.nextRoot.ptr) ∗
                memRegion (a + 48#64) 40 ∗
                vecCapPtrDealloc A.repAlloc G.nextRoot.cap G.nextRoot.ptr ∗
                A.pool lim (M.stepEvents (w ++ w_1) st) sm ∗
                stackAt (s0.sp - 48#64) dropStack32 ∗
                (((s0.sp - 48#64) ↦₆₄ s0.readReg64 .fp) ∗ ((s0.sp - 40#64) ↦₆₄ s0.readReg64 .lr) ∗
                 ((s0.sp - 32#64) ↦₆₄ s0.readReg64 .x22) ∗ ((s0.sp - 24#64) ↦₆₄ s0.readReg64 .x21) ∗
                 ((s0.sp - 16#64) ↦₆₄ s0.readReg64 .x20) ∗ ((s0.sp - 8#64) ↦₆₄ s0.readReg64 .x19))) ∧
              Saved48Preserved s0 sm (s0.sp - 48#64) ∧ AllocCallPreserved s0 sm ∧
              sm.readReg64 .x19 = a ∧ sm.readReg64 .x21 = G.linksPtr ∧ sm.readReg64 .x22 = G.linksCap)
            ?_ (fun _ _ _ _ ⟨hp, hq⟩ => ⟨w ++ w_1, hevs_s1.append hevs_s2, hp, hq⟩)
          simp only [LibsignalBinary.Heap.AllocCostModel.stepEvents_append]
          refine align_pre_st (by
            unfold vecDequeHeader
            simp only [chainEpochSize, chainEpochAlign, Nat.mul_comm, *]
            sep_ac_rfl) ?_
          wp_done
  · intro evs1 s1 hevs1 hpc1 hrun1 ⟨⟨hx23_1, hx24_1, hx25_1, hx26_1, hx27_1, hx28_1, hsp_1, htrace_1, hvregs_1⟩, hacp_1, hx19_1, hx21_1, hx22_1⟩
    have ⟨_, _, _, _, _, _, _⟩ := hacp_1
    let st1 := M.stepEvents evs1 st
    have hfsp_align : ((s0.sp - 48#64) &&& 15#64 == 0#64) = true :=
      spAligned_sub s0.sp 48#64 (by assumption) (by decide)
    refine seq_clean_evs (mid := (blkPl_269).base + 144#64)
      (P_evs := fun evs sm =>
        vecDequeHeader a G.linksCap G.linksPtr G.linksHead
          (BitVec.ofNat 64 (G.epochs.zip c.links).length) ∗
        ((a + 32#64) ↦₆₄ G.nextRoot.cap) ∗ ((a + 40#64) ↦₆₄ G.nextRoot.ptr) ∗
        memRegion (a + 48#64) 40 ∗
        vecCapPtrDealloc A.repAlloc G.nextRoot.cap G.nextRoot.ptr ∗
        A.pool lim (M.stepEvents evs st1) sm ∗
        stackAt (s0.sp - 48#64) dropStack32 ∗
        (((s0.sp - 48#64) ↦₆₄ s0.readReg64 .fp) ∗ ((s0.sp - 40#64) ↦₆₄ s0.readReg64 .lr) ∗
         ((s0.sp - 32#64) ↦₆₄ s0.readReg64 .x22) ∗ ((s0.sp - 24#64) ↦₆₄ s0.readReg64 .x21) ∗
         ((s0.sp - 16#64) ↦₆₄ s0.readReg64 .x20) ∗ ((s0.sp - 8#64) ↦₆₄ s0.readReg64 .x19)))
      (Q := fun sm => Saved48Preserved s0 sm (s0.sp - 48#64) ∧ AllocCallPreserved s0 sm ∧ sm.readReg64 .x19 = a)
      ?_ ?_
    · by_cases hc : G.linksCap = 0
      · have hc_beq : (G.linksCap == 0#64) = true := by rw [beq_iff_eq]; exact hc
        simp only [hc, ↓reduceIte, emp_sepConj, sepConj_emp] at hx22_1 ⊢
        apply sepWP_evs_nil
        simp only [LibsignalBinary.Heap.AllocCostModel.stepEvents_nil]
        wp_steps
        wp_done
      · have hc_beq : ¬((G.linksCap == 0#64) = true) := by rw [beq_iff_eq]; exact hc
        have hlsl := cap_lsl7_sub_lsl4 hcap_lt
        have hsp_sub : s0.sp - 4176#64 = (s0.sp - 48#64) - 4128#64 := by bv_omega
        simp only [hc, ↓reduceIte]
        apply sepWP_evs_dealloc (G.linksCap.toNat * 112) 8
        conv => arg 4; rw [stackAt_dropStack32_split_bottom (s0.sp - 48#64)]
        wp_steps
        wp_call hdealloc_fo (G.linksPtr, G.linksCap.toNat * 112, 8, st1)
        have hacp_d : AllocCallPreserved s0 sf := hacp_1.trans (by assumption)
        rcases hacp_d with ⟨_, _, _, _, _, _, _⟩
        refine align_pre_st (by
          rw [hsp_1, hsp_sub, stackAt_dropStack32_split_bottom (s0.sp - 48#64)]
          sep_ac_rfl) ?_
        wp_done
    · intro evs2 s2 hevs2 hpc2 hrun2 ⟨⟨hx23_2, hx24_2, hx25_2, hx26_2, hx27_2, hx28_2, hsp_2, htrace_2, hvregs_2⟩, hacp_2, hx19_2⟩
      have ⟨_, _, _, _, _, _, _⟩ := hacp_2
      let st2 := M.stepEvents evs2 st1
      dsimp only [vecCapPtrDealloc, LibsignalBinary.Heap.RustCliAllocBudget.repAlloc_live]
      by_cases hnr : (G.nextRoot.cap == 0#64) = true <;>
        simp only [hnr, ↓reduceIte, emp_sepConj, sepConj_emp]
      · refine sepWP_close_drop
          (fun sf => memRegion a 88 ∗
            A.pool lim (M.stepEvents (evs1 ++ evs2) st) sf ∗ stackAt s0.sp dropStack80) ?_
          (fun sf _Pf hp hsp_f htr_f hacp_f hcs_f => ⟨fun hm => ?_, hsp_f, hcs_f⟩)
        · have heq_st2 : M.stepEvents (evs1 ++ evs2) st = st2 := by
            simp only [st1, st2, LibsignalBinary.Heap.AllocCostModel.stepEvents_append]
          rw [heq_st2]
          wp_steps
          refine SepWP.focus_weaken
            (chainHeaders_entails_memRegion_88 a G.linksCap G.linksPtr G.linksHead
              (BitVec.ofNat 64 (G.epochs.zip c.links).length) G.nextRoot.cap G.nextRoot.ptr)
            (by sep_focus) ?_
          refine SepWP.focus_weaken
            (stack_restore_48_dropStack80 s0.sp (s0.readReg64 .fp) (s0.readReg64 .lr)
              (s0.readReg64 .x22) (s0.readReg64 .x21) (s0.readReg64 .x20) (s0.readReg64 .x19))
            (by sep_focus) ?_
          wp_done
        · rw [satisfies_sepExists]; refine ⟨evs1 ++ evs2, ?_⟩
          rw [satisfies_pure_sepConj]; refine ⟨⟨htr_f, hacp_f, hevs1.append hevs2⟩, ?_⟩
          exact Satisfies.mono (Entails.trans (sepConj_mono_left hp) (Entails.of_eq (by sep_ac_rfl))) hm
      · refine sepWP_close_drop
          (fun sf => memRegion a 88 ∗
            A.pool lim (M.stepEvents (evs1 ++ evs2 ++ rustDeallocEvents G.nextRoot.cap.toNat 1) st) sf ∗
            stackAt s0.sp dropStack80) ?_
          (fun sf _Pf hp hsp_f htr_f hacp_f hcs_f => ⟨fun hm => ?_, hsp_f, hcs_f⟩)
        · have heq_st3 : M.stepEvents (evs1 ++ evs2 ++ rustDeallocEvents G.nextRoot.cap.toNat 1) st =
              M.stepEvents (rustDeallocEvents G.nextRoot.cap.toNat 1) st2 := by
            simp only [st1, st2, LibsignalBinary.Heap.AllocCostModel.stepEvents_append]
          rw [heq_st3]
          have htail : SepWP ((blkPC_269).rebase (blkPl_269).base (Rust.withPanics ext)) (s0.readReg64 .lr) s2
              (vecDequeHeader a G.linksCap G.linksPtr G.linksHead
                (BitVec.ofNat 64 (G.epochs.zip c.links).length) ∗
                ((a + 32#64) ↦₆₄ G.nextRoot.cap) ∗ ((a + 40#64) ↦₆₄ G.nextRoot.ptr) ∗
                memRegion (a + 48#64) 40 ∗
                (A.live G.nextRoot.ptr G.nextRoot.cap.toNat 1 ∗
                  memRegion G.nextRoot.ptr G.nextRoot.cap.toNat) ∗
                A.pool lim st2 s2 ∗
                stackAt (s0.sp - 48#64) dropStack32 ∗
                (((s0.sp - 48#64) ↦₆₄ s0.readReg64 .fp) ∗ ((s0.sp - 40#64) ↦₆₄ s0.readReg64 .lr) ∗
                 ((s0.sp - 32#64) ↦₆₄ s0.readReg64 .x22) ∗ ((s0.sp - 24#64) ↦₆₄ s0.readReg64 .x21) ∗
                 ((s0.sp - 16#64) ↦₆₄ s0.readReg64 .x20) ∗ ((s0.sp - 8#64) ↦₆₄ s0.readReg64 .x19)))
              (fun sf Pf =>
                (Pf ⊢ memRegion a 88 ∗
                  A.pool lim (M.stepEvents (rustDeallocEvents G.nextRoot.cap.toNat 1) st2) sf ∗
                  stackAt s0.sp dropStack80) ∧
                sf.sp = s0.sp ∧ sf.trace = s0.trace ∧
                AllocCallPreserved s2 sf ∧ CalleeSavedPreserved s0 sf) := by
            wp_steps
            refine SepWP.focus_weaken
              (chainHeaders_entails_memRegion_88 a G.linksCap G.linksPtr G.linksHead
                (BitVec.ofNat 64 (G.epochs.zip c.links).length) G.nextRoot.cap G.nextRoot.ptr)
              (by sep_focus) ?_
            refine SepWP.focus_weaken
              (stack_restore_48_dropStack80 s0.sp (s0.readReg64 .fp) (s0.readReg64 .lr)
                (s0.readReg64 .x22) (s0.readReg64 .x21) (s0.readReg64 .x20) (s0.readReg64 .x19))
              (by sep_focus) ?_
            rw [stackAt_dropStack80_split_bottom s0.sp]
            wp_call hdealloc_fo (G.nextRoot.ptr, G.nextRoot.cap.toNat, 1, st2)
            have hpost2 : AllocCallPreserved s2 sf := by assumption
            rcases hpost2 with ⟨_, _, _, _, _, _, _⟩
            wp_done
          exact SepWP.mono htail fun _ _ _ _ ⟨hp, hsp_f, htr_f, hacp_2f, hcs_f⟩ =>
            ⟨hp, hsp_f, htr_f, hacp_2.trans hacp_2f, hcs_f⟩
        · rw [satisfies_sepExists]; refine ⟨evs1 ++ evs2 ++ rustDeallocEvents G.nextRoot.cap.toNat 1, ?_⟩
          rw [satisfies_pure_sepConj]
          refine ⟨⟨htr_f, hacp_f, (hevs1.append hevs2).append (LibsignalBinary.Heap.FreeOnlyEvs.singleton 1 G.nextRoot.cap.toNat)⟩, ?_⟩
          exact Satisfies.mono (Entails.trans (sepConj_mono_left hp) (Entails.of_eq (by sep_ac_rfl))) hm


theorem drop_spqr_chain_cl_blockProgram [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {ext : String → Option (State → State)}
    (hdealloc : HookSat (Rust.withPanics ext) spqrRustDeallocSym
      (rustCliDeallocBudgetSpec M A lim)) :
    subroutine_ok (libsignalSessionLib.blockProgram lsmpl 269 (Rust.withPanics ext)) (lsmpl.base 269)
      (withLsCodeLoaded lsmpl (dropSpqrChainSpec M A lim)) :=
  ls_to_blockProgram (drop_spqr_chain_cl_placed_ok hdealloc)

theorem drop_spqr_chain_cl_on [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {callerProg : Program} {idx : Nat} {ext : String → Option (State → State)}
    [IsLsBlockProg callerProg idx (Rust.withPanics ext)]
    (hdealloc : HookSat (Rust.withPanics ext) spqrRustDeallocSym
      (rustCliDeallocBudgetSpec M A lim))
    (hidx : idx < 619 := by decide) :
    subroutine_ok callerProg (lsmpl.base 269)
      (withLsCodeLoaded lsmpl (dropSpqrChainSpec M A lim)) :=
  ls_subroutine_ok_of_block (drop_spqr_chain_cl_placed_ok hdealloc) hidx

theorem drop_spqr_chain_mem_on [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {callerProg : Program} {idx : Nat} {ext : String → Option (State → State)}
    [IsLsBlockProg callerProg idx (Rust.withPanics ext)] {m : Memory}
    (hdealloc : HookSat (Rust.withPanics ext) spqrRustDeallocSym
      (rustCliDeallocBudgetSpec M A lim))
    (hcl : LibsignalCodeLoaded lsmpl m) (hidx : idx < 619 := by decide) :
    subroutine_ok callerProg (lsmpl.base 269)
      (withMemEq m (dropSpqrChainSpec M A lim)) :=
  lscall_blk_cl (drop_spqr_chain_cl_placed_ok hdealloc) hcl hidx

end LibsignalBinary.Proofs.SpqrV1.Drop.ChainStatesClPlacedBudgetAux
