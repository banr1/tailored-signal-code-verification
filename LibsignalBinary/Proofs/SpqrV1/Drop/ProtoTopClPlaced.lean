/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SpqrV1.Drop.ProtoTop2
public import LibsignalBinary.Proofs.SpqrV1.Drop.ProtoChunkedClPlaced
import LibsignalBinary.Proofs.SpqrV1.Drop.ProtoChunked2
import LibsignalBinary.Proofs.SpqrV1.Alloc.SpqrAllocCodeSym
import ProofLib.SepLogic.WP.Apply
import ProofLib.SepLogic.WPp
import GeneratedLean.LibsignalSessionObj

/-!
# Code-Loaded `[LibsignalPlacement]` Drop Glue for `Option<InnerState>` and `PqRatchetState`

Proves `withLsCodeLoaded lsmpl` subroutine contracts from `rustDeallocSpec A` for:
- Block `267`: `core::ptr::drop_glue::<core::option::Option<spqr::proto::pq_ratchet::v1_state::InnerState>>`
- Block `270`: `core::ptr::drop_glue::<spqr::proto::pq_ratchet::PqRatchetState>`
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 400000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false

namespace LibsignalBinary.Proofs.SpqrV1.Drop.ProtoTopClPlaced

open Arm64 Arm64.Obj ProofLib ProofLib.ProgramReflection
open CryptoVerification
open CryptoVerification.RustHeap
open CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalTripleRatchetRepr
open CryptoVerification.LibsignalSpqrV1
open CryptoVerification.SpqrV1.Alloc
open CryptoVerification.SpqrV1.Poly
open CryptoVerification.SpqrV1.ProtoRepr
open CryptoVerification.SpqrV1.Drop
open CryptoVerification.SpqrV1.States.Recv
  (spqrRustDeallocSym drop_glue_proto_poly_encoder_mem_on)
open LibsignalBinary.Proofs.SpqrV1.Drop.ProtoChunkedClPlaced
  (subroutine_ok_withLsCodeLoaded_intro seq_clean_lscl ls_to_blockProgram
   drop_proto_chunked_header_received_mem_on
   drop_proto_chunked_no_header_received_mem_on
   drop_proto_chunked_ek_sent_ct1_received_mem_on
   drop_proto_unchunked_ct1_sent_ek_received_mem_on
   drop_proto_epoch_slice_mem_on
   drop_proto_chunked_ct1_received_mem_on
   drop_proto_chunked_header_sent_mem_on)

attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero
attribute [local simp, local arm64_norm] none2Cap_add_two_beq_zero noneCap_add_two_beq_zero

local macro "SavedFrame48 " s0:term:max : term =>
  `(((State.sp $s0 - 48#64) ↦₆₄ State.readReg64 $s0 .fp) ∗ ((State.sp $s0 - 40#64) ↦₆₄ State.readReg64 $s0 .lr) ∗
    ((State.sp $s0 - 32#64) ↦₆₄ State.readReg64 $s0 .x22) ∗ ((State.sp $s0 - 24#64) ↦₆₄ State.readReg64 $s0 .x21) ∗
    ((State.sp $s0 - 16#64) ↦₆₄ State.readReg64 $s0 .x20) ∗ ((State.sp $s0 - 8#64) ↦₆₄ State.readReg64 $s0 .x19))

private theorem restore_96 (s0 : State) :
    (memRegion (s0.sp - 4192#64) 48 ∗ stackAt (s0.sp - 48#64) allocHookStack) ∗ SavedFrame48 s0 ⊢
      stackAt s0.sp dropStack96 :=
  stack_restore_96_allocHook s0.sp (s0.readReg64 .fp) (s0.readReg64 .lr)
    (s0.readReg64 .x22) (s0.readReg64 .x21) (s0.readReg64 .x20) (s0.readReg64 .x19)

/-! ## Simple and Tail-Call Variants of Block `267` -/

private theorem drop_opt_proto_inner_state_none_cl [LibsignalPlacement] {A : RustAlloc}
    {ext : String → Option (State → State)} :
    subroutine_ok (lsProg_267 (Rust.withPanics ext)) (blkPl_267).base
      (withLsCodeLoaded lsmpl (dropOptProtoInnerStatePlacedVariantSpec A none)) :=
  subroutine_ok_withLsCodeLoaded_of_plain drop_opt_proto_inner_state_none_placed

private theorem drop_opt_proto_inner_state_keysUnsampled_cl [LibsignalPlacement] {A : RustAlloc}
    {ext : String → Option (State → State)}
    (hdealloc : HookSat (Rust.withPanics ext) spqrRustDeallocSym (rustDeallocSpec A))
    (st : V1State.Chunked.KeysUnsampled) :
    subroutine_ok (lsProg_267 (Rust.withPanics ext)) (blkPl_267).base
      (withLsCodeLoaded lsmpl (dropOptProtoInnerStatePlacedVariantSpec A (some (.keysUnsampled st)))) :=
  subroutine_ok_withLsCodeLoaded_of_plain
    (drop_opt_proto_inner_state_keysUnsampled_placed (spqr_hook_ok_of_mem hdealloc) st)

private theorem drop_opt_proto_inner_state_keysSampled_cl [LibsignalPlacement] {A : RustAlloc}
    {ext : String → Option (State → State)}
    (hdealloc : HookSat (Rust.withPanics ext) spqrRustDeallocSym (rustDeallocSpec A))
    (st : V1State.Chunked.KeysSampled) :
    subroutine_ok (lsProg_267 (Rust.withPanics ext)) (blkPl_267).base
      (withLsCodeLoaded lsmpl (dropOptProtoInnerStatePlacedVariantSpec A (some (.keysSampled st)))) := by
  change subroutine_ok ((blkPC_267).rebase (blkPl_267).base (Rust.withPanics ext)) (blkPl_267).base _
  apply subroutine_ok_withLsCodeLoaded_intro; intro m hcl
  dsimp only [withMemEq, dropOptProtoInnerStatePlacedVariantSpec, optProtoInnerStateAt,
    protoInnerStateAt, optProtoInnerStateJumpTablePlacedAt, optProtoInnerStateJumpTableSym,
    optProtoInnerStateJumpTableBytes, optProtoInnerStateSize, BitVec.ofNat_eq_ofNat] at ⊢
  wp_init a s0; have hx0 : s0.readReg64 .x0 = a := by assumption
  have hm : s0.mem = m := (by assumption); subst hm
  rw [protoChunkedKeysSampledAt_eq_ct1ReceivedAt]
  nth_rw 1 [stackAt_dropStack96_split s0.sp]; cells_unfold; wp_pull_exists; rename_i v_fp v_lr v_x22 v_x21 v_x20 v_x19
  apply sepWP_seq_lscl hcl (mid := lsmpl.base 282); wp_steps
  apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs); intro hcl_call
  have hcallee := drop_proto_chunked_ct1_received_mem_on (callerProg := lsProg_267 (Rust.withPanics ext)) hdealloc hcl_call
  dsimp only [lsProg_267, withMemEq, BitVec.ofNat_eq_ofNat] at hcallee
  refine SepWP.focus_weaken (restore_96 s0) (by sep_focus) ?_
  rw [stackAt_dropStack96_split_48 s0.sp]; wp_call hcallee ⟨a + 8#64, keysSampledToCt1Received st⟩
  rw [← stackAt_dropStack96_split_48 s0.sp]
  refine SepWP.focus_weaken (tag_and_two_regions_entails_224 a 0x8000000000000001#64 160 56 168#64
    (BitVec.add_assoc a 8#64 160#64).symm rfl) (by sep_focus) ?_; wp_done

private theorem drop_opt_proto_inner_state_headerSent_cl [LibsignalPlacement] {A : RustAlloc}
    {ext : String → Option (State → State)}
    (hdealloc : HookSat (Rust.withPanics ext) spqrRustDeallocSym (rustDeallocSpec A))
    (st : V1State.Chunked.HeaderSent) :
    subroutine_ok (lsProg_267 (Rust.withPanics ext)) (blkPl_267).base
      (withLsCodeLoaded lsmpl (dropOptProtoInnerStatePlacedVariantSpec A (some (.headerSent st)))) := by
  change subroutine_ok ((blkPC_267).rebase (blkPl_267).base (Rust.withPanics ext)) (blkPl_267).base _
  apply subroutine_ok_withLsCodeLoaded_intro; intro m hcl
  dsimp only [withMemEq, dropOptProtoInnerStatePlacedVariantSpec, optProtoInnerStateAt,
    protoInnerStateAt, optProtoInnerStateJumpTablePlacedAt, optProtoInnerStateJumpTableSym,
    optProtoInnerStateJumpTableBytes, optProtoInnerStateSize, BitVec.ofNat_eq_ofNat] at ⊢
  wp_init a s0; have hx0 : s0.readReg64 .x0 = a := by assumption
  have hm : s0.mem = m := (by assumption); subst hm
  nth_rw 1 [stackAt_dropStack96_split s0.sp]; cells_unfold; wp_pull_exists; rename_i v_fp v_lr v_x22 v_x21 v_x20 v_x19
  apply sepWP_seq_lscl hcl (mid := lsmpl.base 281); wp_steps
  apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs); intro hcl_call
  have hcallee := drop_proto_chunked_header_sent_mem_on (callerProg := lsProg_267 (Rust.withPanics ext)) hdealloc hcl_call
  dsimp only [lsProg_267, withMemEq, BitVec.ofNat_eq_ofNat] at hcallee
  refine SepWP.focus_weaken (restore_96 s0) (by sep_focus) ?_; wp_call hcallee ⟨a + 8#64, st⟩
  refine SepWP.focus_weaken (tag_and_two_regions_entails_224 a 0x8000000000000002#64 176 40 184#64
    (BitVec.add_assoc a 8#64 176#64).symm rfl) (by sep_focus) ?_; wp_done

private theorem drop_opt_proto_inner_state_ct1Received_cl [LibsignalPlacement] {A : RustAlloc}
    {ext : String → Option (State → State)}
    (hdealloc : HookSat (Rust.withPanics ext) spqrRustDeallocSym (rustDeallocSpec A))
    (st : V1State.Chunked.Ct1Received) :
    subroutine_ok (lsProg_267 (Rust.withPanics ext)) (blkPl_267).base
      (withLsCodeLoaded lsmpl (dropOptProtoInnerStatePlacedVariantSpec A (some (.ct1Received st)))) := by
  change subroutine_ok ((blkPC_267).rebase (blkPl_267).base (Rust.withPanics ext)) (blkPl_267).base _
  apply subroutine_ok_withLsCodeLoaded_intro; intro m hcl
  dsimp only [withMemEq, dropOptProtoInnerStatePlacedVariantSpec, optProtoInnerStateAt,
    protoInnerStateAt, optProtoInnerStateJumpTablePlacedAt, optProtoInnerStateJumpTableSym,
    optProtoInnerStateJumpTableBytes, optProtoInnerStateSize, BitVec.ofNat_eq_ofNat] at ⊢
  wp_init a s0; have hx0 : s0.readReg64 .x0 = a := by assumption
  have hm : s0.mem = m := (by assumption); subst hm
  nth_rw 1 [stackAt_dropStack96_split s0.sp]; cells_unfold; wp_pull_exists; rename_i v_fp v_lr v_x22 v_x21 v_x20 v_x19
  apply sepWP_seq_lscl hcl (mid := lsmpl.base 282); wp_steps
  apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs); intro hcl_call
  have hcallee := drop_proto_chunked_ct1_received_mem_on (callerProg := lsProg_267 (Rust.withPanics ext)) hdealloc hcl_call
  dsimp only [lsProg_267, withMemEq, BitVec.ofNat_eq_ofNat] at hcallee
  refine SepWP.focus_weaken (restore_96 s0) (by sep_focus) ?_
  rw [stackAt_dropStack96_split_48 s0.sp]; wp_call hcallee ⟨a + 8#64, st⟩; rw [← stackAt_dropStack96_split_48 s0.sp]
  refine SepWP.focus_weaken (tag_and_two_regions_entails_224 a 0x8000000000000003#64 160 56 168#64
    (BitVec.add_assoc a 8#64 160#64).symm rfl) (by sep_focus) ?_; wp_done

private theorem drop_opt_proto_inner_state_ekSentCt1Received_cl [LibsignalPlacement] {A : RustAlloc}
    {ext : String → Option (State → State)}
    (hdealloc : HookSat (Rust.withPanics ext) spqrRustDeallocSym (rustDeallocSpec A))
    (st : V1State.Chunked.EkSentCt1Received) :
    subroutine_ok (lsProg_267 (Rust.withPanics ext)) (blkPl_267).base
      (withLsCodeLoaded lsmpl (dropOptProtoInnerStatePlacedVariantSpec A (some (.ekSentCt1Received st)))) := by
  change subroutine_ok ((blkPC_267).rebase (blkPl_267).base (Rust.withPanics ext)) (blkPl_267).base _
  apply subroutine_ok_withLsCodeLoaded_intro; intro m hcl
  dsimp only [withMemEq, dropOptProtoInnerStatePlacedVariantSpec, optProtoInnerStateAt,
    protoInnerStateAt, optProtoInnerStateJumpTablePlacedAt, optProtoInnerStateJumpTableSym,
    optProtoInnerStateJumpTableBytes, optProtoInnerStateSize, BitVec.ofNat_eq_ofNat] at ⊢
  wp_init a s0; have hx0 : s0.readReg64 .x0 = a := by assumption
  have hm : s0.mem = m := (by assumption); subst hm
  nth_rw 1 [stackAt_dropStack96_split s0.sp]; cells_unfold; wp_pull_exists; rename_i v_fp v_lr v_x22 v_x21 v_x20 v_x19
  apply sepWP_seq_lscl hcl (mid := lsmpl.base 285); wp_steps
  apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs); intro hcl_call
  have hcallee := drop_proto_chunked_ek_sent_ct1_received_mem_on (callerProg := lsProg_267 (Rust.withPanics ext)) hdealloc hcl_call
  dsimp only [lsProg_267, withMemEq, BitVec.ofNat_eq_ofNat] at hcallee
  refine SepWP.focus_weaken (restore_96 s0) (by sep_focus) ?_
  rw [stackAt_dropStack96_split_48 s0.sp]; wp_call hcallee ⟨a + 8#64, st⟩; rw [← stackAt_dropStack96_split_48 s0.sp]
  refine SepWP.focus_weaken (tag_and_two_regions_entails_224 a 0x8000000000000004#64 144 72 152#64
    (BitVec.add_assoc a 8#64 144#64).symm rfl) (by sep_focus) ?_; wp_done

private theorem drop_opt_proto_inner_state_noHeaderReceived_cl [LibsignalPlacement] {A : RustAlloc}
    {ext : String → Option (State → State)}
    (hdealloc : HookSat (Rust.withPanics ext) spqrRustDeallocSym (rustDeallocSpec A))
    (st : V1State.Chunked.NoHeaderReceived) :
    subroutine_ok (lsProg_267 (Rust.withPanics ext)) (blkPl_267).base
      (withLsCodeLoaded lsmpl (dropOptProtoInnerStatePlacedVariantSpec A (some (.noHeaderReceived st)))) := by
  change subroutine_ok ((blkPC_267).rebase (blkPl_267).base (Rust.withPanics ext)) (blkPl_267).base _
  apply subroutine_ok_withLsCodeLoaded_intro; intro m hcl
  dsimp only [withMemEq, dropOptProtoInnerStatePlacedVariantSpec, optProtoInnerStateAt,
    protoInnerStateAt, optProtoInnerStateJumpTablePlacedAt, optProtoInnerStateJumpTableSym,
    optProtoInnerStateJumpTableBytes, optProtoInnerStateSize, BitVec.ofNat_eq_ofNat] at ⊢
  wp_init a s0; have hx0 : s0.readReg64 .x0 = a := by assumption
  have hm : s0.mem = m := (by assumption); subst hm
  nth_rw 1 [stackAt_dropStack96_split s0.sp]; cells_unfold; wp_pull_exists; rename_i v_fp v_lr v_x22 v_x21 v_x20 v_x19
  apply sepWP_seq_lscl hcl (mid := lsmpl.base 284); wp_steps
  apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs); intro hcl_call
  have hcallee := drop_proto_chunked_no_header_received_mem_on (callerProg := lsProg_267 (Rust.withPanics ext)) hdealloc hcl_call
  dsimp only [lsProg_267, withMemEq, BitVec.ofNat_eq_ofNat] at hcallee
  refine SepWP.focus_weaken (restore_96 s0) (by sep_focus) ?_
  rw [stackAt_dropStack96_split_48 s0.sp]; wp_call hcallee ⟨a + 8#64, st⟩; rw [← stackAt_dropStack96_split_48 s0.sp]
  refine SepWP.focus_weaken (tag_and_two_regions_entails_224 a 0x8000000000000005#64 96 120 104#64
    (BitVec.add_assoc a 8#64 96#64).symm rfl) (by sep_focus) ?_; wp_done

private theorem drop_opt_proto_inner_state_headerReceived_cl [LibsignalPlacement] {A : RustAlloc}
    {ext : String → Option (State → State)}
    (hdealloc : HookSat (Rust.withPanics ext) spqrRustDeallocSym (rustDeallocSpec A))
    (st : V1State.Chunked.HeaderReceived) :
    subroutine_ok (lsProg_267 (Rust.withPanics ext)) (blkPl_267).base
      (withLsCodeLoaded lsmpl (dropOptProtoInnerStatePlacedVariantSpec A (some (.headerReceived st)))) := by
  change subroutine_ok ((blkPC_267).rebase (blkPl_267).base (Rust.withPanics ext)) (blkPl_267).base _
  apply subroutine_ok_withLsCodeLoaded_intro; intro m hcl
  dsimp only [withMemEq, dropOptProtoInnerStatePlacedVariantSpec, optProtoInnerStateAt,
    protoInnerStateAt, optProtoInnerStateJumpTablePlacedAt, optProtoInnerStateJumpTableSym,
    optProtoInnerStateJumpTableBytes, optProtoInnerStateSize, BitVec.ofNat_eq_ofNat] at ⊢
  wp_init a s0; have hx0 : s0.readReg64 .x0 = a := by assumption
  have hm : s0.mem = m := (by assumption); subst hm
  nth_rw 1 [stackAt_dropStack96_split s0.sp]; cells_unfold; wp_pull_exists; rename_i v_fp v_lr v_x22 v_x21 v_x20 v_x19
  apply sepWP_seq_lscl hcl (mid := lsmpl.base 283); wp_steps
  apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs); intro hcl_call
  have hcallee := drop_proto_chunked_header_received_mem_on (callerProg := lsProg_267 (Rust.withPanics ext)) hdealloc hcl_call
  dsimp only [lsProg_267, withMemEq, BitVec.ofNat_eq_ofNat] at hcallee
  refine SepWP.focus_weaken (restore_96 s0) (by sep_focus) ?_
  rw [stackAt_dropStack96_split_48 s0.sp]; wp_call hcallee ⟨a + 8#64, st⟩; rw [← stackAt_dropStack96_split_48 s0.sp]
  refine SepWP.focus_weaken (tag_and_two_regions_entails_224 a 0x8000000000000006#64 120 96 128#64
    (BitVec.add_assoc a 8#64 120#64).symm rfl) (by sep_focus) ?_; wp_done

/-! ## Share-Vector Loops (`+192..+224` and `+408..+440`) for Block `267` -/

private theorem drop_opt_proto_inner_state_body_192_cl [LibsignalPlacement] {A : RustAlloc}
    {H : String → Option (State → State)}
    (hdealloc : subroutine_ok ((blkPC_267).rebase (blkPl_267).base H)
      (lsρ spqrRustDeallocSym) (rustDeallocSpec A))
    (s0 : State) (fsp ptsPtr ptsCap : BitVec 64) (hfsp_align : (fsp &&& 15#64 == 0#64) = true) :
    ∀ (cur cnt : BitVec 64) (bs : List (BitVec 8)) (s : State) (Frame : SepProp),
      s.pc = (blkPl_267).base + 204#64 → s.status = .Running → Saved48Preserved s0 s fsp →
      s.readReg64 .x19 = ptsPtr → s.readReg64 .x20 = ptsCap →
      s.readReg64 .x21 = cnt → s.readReg64 .x22 = cur + 8#64 →
      SepWP ((blkPC_267).rebase (blkPl_267).base H) ((blkPl_267).base + 192#64) s
        (vecU8 A cur bs ∗ A.pool ∗ stackAt fsp allocHookStack ∗ Frame)
        (fun sm Pm =>
          (Pm ⊢ memRegion cur 24 ∗ A.pool ∗ stackAt fsp allocHookStack ∗ Frame) ∧
          Saved48Preserved s0 sm fsp ∧ sm.readReg64 .x19 = ptsPtr ∧ sm.readReg64 .x20 = ptsCap ∧
          sm.readReg64 .x21 = cnt ∧ sm.readReg64 .x22 = cur + 8#64) := by
  simp only [rustDeallocSpec] at hdealloc
  intro cur cnt bs s Frame hpc hrun ⟨hx23, hx24, hx25, hx26, hx27, hx28, hsp, htrace, hvregs⟩ hx19 hx20 hx21 hx22
  refine SepWP.weaken_pre (sepConj_mono_left (vecU8_entails_capPtr_dealloc A cur bs)) ?_
  apply SepWP.exists_sepConj_left; intro cap; apply SepWP.exists_sepConj_left; intro vptr
  have hstep : SepWP ((blkPC_267).rebase (blkPl_267).base H) ((blkPl_267).base + 192#64) s
      (((cur ↦₆₄ cap) ∗ ((cur + 8#64) ↦₆₄ vptr) ∗ memRegion (cur + 16#64) 8 ∗ vecCapPtrDealloc A cap vptr) ∗
        A.pool ∗ stackAt fsp allocHookStack ∗ Frame)
      (fun sm Pm => (Pm ⊢ ((cur ↦₆₄ cap) ∗ ((cur + 8#64) ↦₆₄ vptr) ∗ memRegion (cur + 16#64) 8) ∗
          A.pool ∗ stackAt fsp allocHookStack ∗ Frame) ∧
        Saved48Preserved s0 sm fsp ∧ sm.readReg64 .x19 = ptsPtr ∧ sm.readReg64 .x20 = ptsCap ∧
        sm.readReg64 .x21 = cnt ∧ sm.readReg64 .x22 = cur + 8#64) := by
    dsimp only [vecCapPtrDealloc]
    by_cases hcap : (cap == 0#64) = true <;> simp only [hcap, ↓reduceIte, sepConj_emp, emp_sepConj]
    · wp_steps; wp_done
    · wp_steps; wp_apply; wp_steps; refine align_pre (by rw [hsp]; ac_rfl) ?_; wp_done
  exact SepWP.strengthen_entails_const (sepConj_mono_left (header_cells_entails_memRegion_24 cur cap vptr)) hstep

private theorem drop_opt_proto_inner_state_loop_192_cl [LibsignalPlacement] {A : RustAlloc}
    {H : String → Option (State → State)}
    (hdealloc : subroutine_ok ((blkPC_267).rebase (blkPl_267).base H)
      (lsρ spqrRustDeallocSym) (rustDeallocSpec A))
    (s0 : State) (fsp ptsPtr ptsCap : BitVec 64) (hfsp_align : (fsp &&& 15#64 == 0#64) = true) :
    ∀ (rest : List (List (BitVec 8))) (cur : BitVec 64) (s : State) (Frame : SepProp),
      rest ≠ [] → rest.length * 24 < 2 ^ 63 →
      s.pc = (blkPl_267).base + 204#64 → s.status = .Running → Saved48Preserved s0 s fsp →
      s.readReg64 .x19 = ptsPtr → s.readReg64 .x20 = ptsCap →
      s.readReg64 .x21 = BitVec.ofNat 64 rest.length → s.readReg64 .x22 = cur + 8#64 →
      SepWP ((blkPC_267).rebase (blkPl_267).base H) ((blkPl_267).base + 444#64) s
        (arrayAt (fun bs addr => vecU8 A addr bs) 24 cur rest ∗ A.pool ∗ stackAt fsp allocHookStack ∗ Frame)
        (fun sm Pm =>
          (Pm ⊢ memRegion cur (rest.length * 24) ∗ A.pool ∗ stackAt fsp allocHookStack ∗ Frame) ∧
          Saved48Preserved s0 sm fsp ∧ sm.readReg64 .x19 = ptsPtr ∧ sm.readReg64 .x20 = ptsCap) := by
  have hbody := drop_opt_proto_inner_state_body_192_cl hdealloc s0 fsp ptsPtr ptsCap hfsp_align
  intro rest; induction rest with
  | nil => intro _ _ _ hne; exact absurd rfl hne
  | cons bs tl ih =>
    intro cur s Frame _ hlen hpc hrun hpres hx19 hx20 hx21 hx22
    simp only [arrayAt, BitVec.ofNat_eq_ofNat]; rw [sep_pull_body]
    refine seq_clean (mid := (blkPl_267).base + 192#64)
      (P_mid := memRegion cur 24 ∗ A.pool ∗ stackAt fsp allocHookStack ∗
        (arrayAt (fun bs addr => vecU8 A addr bs) 24 (cur + 24#64) tl ∗ Frame))
      (Q := fun sm => Saved48Preserved s0 sm fsp ∧ sm.readReg64 .x19 = ptsPtr ∧ sm.readReg64 .x20 = ptsCap ∧
        sm.readReg64 .x21 = BitVec.ofNat 64 (bs :: tl).length ∧ sm.readReg64 .x22 = cur + 8#64)
      (hbody cur (BitVec.ofNat 64 (bs :: tl).length) bs s _ hpc hrun hpres hx19 hx20 hx21 hx22) ?_
    intro s1 hpc1 hrun1 ⟨hpres1, hx19_1, hx20_1, hx21_1, hx22_1⟩
    rcases tl with _ | ⟨bs2, tl2⟩
    · simp only [List.length_singleton, arrayAt, sepConj_emp, emp_sepConj, Nat.one_mul] at hx21_1 ⊢
      rcases hpres1 with ⟨hx23_1, hx24_1, hx25_1, hx26_1, hx27_1, hx28_1, hsp_1, htrace_1, hvregs_1⟩; wp_steps; wp_done
    · have hlen_tl : (bs2 :: tl2).length * 24 < 2 ^ 63 := tail_len_mul_lt hlen
      have hne1 := ofNat_add_one_beq_one_false_24 (n := (bs2 :: tl2).length) (by simp) hlen_tl
      rw [List.length_cons, ofNat_succ_eq_add_one] at hx21_1
      refine seq_clean (mid := (blkPl_267).base + 204#64)
        (P_mid := arrayAt (fun bs addr => vecU8 A addr bs) 24 (cur + 24#64) (bs2 :: tl2) ∗
          A.pool ∗ stackAt fsp allocHookStack ∗ (memRegion cur 24 ∗ Frame))
        (Q := fun sm => Saved48Preserved s0 sm fsp ∧ sm.readReg64 .x19 = ptsPtr ∧ sm.readReg64 .x20 = ptsCap ∧
          sm.readReg64 .x21 = BitVec.ofNat 64 (bs2 :: tl2).length ∧ sm.readReg64 .x22 = (cur + 24#64) + 8#64) ?_ ?_
      · rcases hpres1 with ⟨hx23_1, hx24_1, hx25_1, hx26_1, hx27_1, hx28_1, hsp_1, htrace_1, hvregs_1⟩
        rw [sep_push_body]; wp_steps; rw [add_24_add_8]; wp_done
      · intro s2 hpc2 hrun2 ⟨hpres2, hx19_2, hx20_2, hx21_2, hx22_2⟩
        have hrec := ih (cur + 24#64) s2 (memRegion cur 24 ∗ Frame)
          (List.cons_ne_nil _ _) hlen_tl hpc2 hrun2 hpres2 hx19_2 hx20_2 hx21_2 hx22_2
        refine SepWP.strengthen_entails_const ?_ hrec
        have hsplit := cons_len_mul bs (bs2 :: tl2) 24
        have hbound : 24 + (bs2 :: tl2).length * 24 ≤ 2 ^ 64 := by
          rw [← hsplit]; exact Nat.le_of_lt (Nat.lt_trans hlen (by decide))
        rw [sep_rejoin_loop, hsplit, ProofLib.memRegion_split cur 24 ((bs2 :: tl2).length * 24) hbound]
        exact Entails.refl _

private theorem drop_opt_proto_inner_state_body_408_cl [LibsignalPlacement] {A : RustAlloc}
    {H : String → Option (State → State)}
    (hdealloc : subroutine_ok ((blkPC_267).rebase (blkPl_267).base H)
      (lsρ spqrRustDeallocSym) (rustDeallocSpec A))
    (s0 : State) (fsp ptsPtr ptsCap : BitVec 64) (hfsp_align : (fsp &&& 15#64 == 0#64) = true) :
    ∀ (cur cnt : BitVec 64) (bs : List (BitVec 8)) (s : State) (Frame : SepProp),
      s.pc = (blkPl_267).base + 420#64 → s.status = .Running → Saved48Preserved s0 s fsp →
      s.readReg64 .x19 = ptsPtr → s.readReg64 .x20 = ptsCap →
      s.readReg64 .x21 = cnt → s.readReg64 .x22 = cur + 8#64 →
      SepWP ((blkPC_267).rebase (blkPl_267).base H) ((blkPl_267).base + 408#64) s
        (vecU8 A cur bs ∗ A.pool ∗ stackAt fsp allocHookStack ∗ Frame)
        (fun sm Pm =>
          (Pm ⊢ memRegion cur 24 ∗ A.pool ∗ stackAt fsp allocHookStack ∗ Frame) ∧
          Saved48Preserved s0 sm fsp ∧ sm.readReg64 .x19 = ptsPtr ∧ sm.readReg64 .x20 = ptsCap ∧
          sm.readReg64 .x21 = cnt ∧ sm.readReg64 .x22 = cur + 8#64) := by
  simp only [rustDeallocSpec] at hdealloc
  intro cur cnt bs s Frame hpc hrun ⟨hx23, hx24, hx25, hx26, hx27, hx28, hsp, htrace, hvregs⟩ hx19 hx20 hx21 hx22
  refine SepWP.weaken_pre (sepConj_mono_left (vecU8_entails_capPtr_dealloc A cur bs)) ?_
  apply SepWP.exists_sepConj_left; intro cap; apply SepWP.exists_sepConj_left; intro vptr
  have hstep : SepWP ((blkPC_267).rebase (blkPl_267).base H) ((blkPl_267).base + 408#64) s
      (((cur ↦₆₄ cap) ∗ ((cur + 8#64) ↦₆₄ vptr) ∗ memRegion (cur + 16#64) 8 ∗ vecCapPtrDealloc A cap vptr) ∗
        A.pool ∗ stackAt fsp allocHookStack ∗ Frame)
      (fun sm Pm => (Pm ⊢ ((cur ↦₆₄ cap) ∗ ((cur + 8#64) ↦₆₄ vptr) ∗ memRegion (cur + 16#64) 8) ∗
          A.pool ∗ stackAt fsp allocHookStack ∗ Frame) ∧
        Saved48Preserved s0 sm fsp ∧ sm.readReg64 .x19 = ptsPtr ∧ sm.readReg64 .x20 = ptsCap ∧
        sm.readReg64 .x21 = cnt ∧ sm.readReg64 .x22 = cur + 8#64) := by
    dsimp only [vecCapPtrDealloc]
    by_cases hcap : (cap == 0#64) = true <;> simp only [hcap, ↓reduceIte, sepConj_emp, emp_sepConj]
    · wp_steps; wp_done
    · wp_steps; wp_apply; wp_steps; refine align_pre (by rw [hsp]; ac_rfl) ?_; wp_done
  exact SepWP.strengthen_entails_const (sepConj_mono_left (header_cells_entails_memRegion_24 cur cap vptr)) hstep

private theorem drop_opt_proto_inner_state_loop_408_cl [LibsignalPlacement] {A : RustAlloc}
    {H : String → Option (State → State)}
    (hdealloc : subroutine_ok ((blkPC_267).rebase (blkPl_267).base H)
      (lsρ spqrRustDeallocSym) (rustDeallocSpec A))
    (s0 : State) (fsp ptsPtr ptsCap : BitVec 64) (hfsp_align : (fsp &&& 15#64 == 0#64) = true) :
    ∀ (rest : List (List (BitVec 8))) (cur : BitVec 64) (s : State) (Frame : SepProp),
      rest ≠ [] → rest.length * 24 < 2 ^ 63 →
      s.pc = (blkPl_267).base + 420#64 → s.status = .Running → Saved48Preserved s0 s fsp →
      s.readReg64 .x19 = ptsPtr → s.readReg64 .x20 = ptsCap →
      s.readReg64 .x21 = BitVec.ofNat 64 rest.length → s.readReg64 .x22 = cur + 8#64 →
      SepWP ((blkPC_267).rebase (blkPl_267).base H) ((blkPl_267).base + 444#64) s
        (arrayAt (fun bs addr => vecU8 A addr bs) 24 cur rest ∗ A.pool ∗ stackAt fsp allocHookStack ∗ Frame)
        (fun sm Pm =>
          (Pm ⊢ memRegion cur (rest.length * 24) ∗ A.pool ∗ stackAt fsp allocHookStack ∗ Frame) ∧
          Saved48Preserved s0 sm fsp ∧ sm.readReg64 .x19 = ptsPtr ∧ sm.readReg64 .x20 = ptsCap) := by
  have hbody := drop_opt_proto_inner_state_body_408_cl hdealloc s0 fsp ptsPtr ptsCap hfsp_align
  intro rest; induction rest with
  | nil => intro _ _ _ hne; exact absurd rfl hne
  | cons bs tl ih =>
    intro cur s Frame _ hlen hpc hrun hpres hx19 hx20 hx21 hx22
    simp only [arrayAt, BitVec.ofNat_eq_ofNat]; rw [sep_pull_body]
    refine seq_clean (mid := (blkPl_267).base + 408#64)
      (P_mid := memRegion cur 24 ∗ A.pool ∗ stackAt fsp allocHookStack ∗
        (arrayAt (fun bs addr => vecU8 A addr bs) 24 (cur + 24#64) tl ∗ Frame))
      (Q := fun sm => Saved48Preserved s0 sm fsp ∧ sm.readReg64 .x19 = ptsPtr ∧ sm.readReg64 .x20 = ptsCap ∧
        sm.readReg64 .x21 = BitVec.ofNat 64 (bs :: tl).length ∧ sm.readReg64 .x22 = cur + 8#64)
      (hbody cur (BitVec.ofNat 64 (bs :: tl).length) bs s _ hpc hrun hpres hx19 hx20 hx21 hx22) ?_
    intro s1 hpc1 hrun1 ⟨hpres1, hx19_1, hx20_1, hx21_1, hx22_1⟩
    rcases tl with _ | ⟨bs2, tl2⟩
    · simp only [List.length_singleton, arrayAt, sepConj_emp, emp_sepConj, Nat.one_mul] at hx21_1 ⊢
      rcases hpres1 with ⟨hx23_1, hx24_1, hx25_1, hx26_1, hx27_1, hx28_1, hsp_1, htrace_1, hvregs_1⟩; wp_steps; wp_done
    · have hlen_tl : (bs2 :: tl2).length * 24 < 2 ^ 63 := tail_len_mul_lt hlen
      have hne1 := ofNat_add_one_beq_one_false_24 (n := (bs2 :: tl2).length) (by simp) hlen_tl
      rw [List.length_cons, ofNat_succ_eq_add_one] at hx21_1
      refine seq_clean (mid := (blkPl_267).base + 420#64)
        (P_mid := arrayAt (fun bs addr => vecU8 A addr bs) 24 (cur + 24#64) (bs2 :: tl2) ∗
          A.pool ∗ stackAt fsp allocHookStack ∗ (memRegion cur 24 ∗ Frame))
        (Q := fun sm => Saved48Preserved s0 sm fsp ∧ sm.readReg64 .x19 = ptsPtr ∧ sm.readReg64 .x20 = ptsCap ∧
          sm.readReg64 .x21 = BitVec.ofNat 64 (bs2 :: tl2).length ∧ sm.readReg64 .x22 = (cur + 24#64) + 8#64) ?_ ?_
      · rcases hpres1 with ⟨hx23_1, hx24_1, hx25_1, hx26_1, hx27_1, hx28_1, hsp_1, htrace_1, hvregs_1⟩
        rw [sep_push_body]; wp_steps; rw [add_24_add_8]; wp_done
      · intro s2 hpc2 hrun2 ⟨hpres2, hx19_2, hx20_2, hx21_2, hx22_2⟩
        have hrec := ih (cur + 24#64) s2 (memRegion cur 24 ∗ Frame)
          (List.cons_ne_nil _ _) hlen_tl hpc2 hrun2 hpres2 hx19_2 hx20_2 hx21_2 hx22_2
        refine SepWP.strengthen_entails_const ?_ hrec
        have hsplit := cons_len_mul bs (bs2 :: tl2) 24
        have hbound : 24 + (bs2 :: tl2).length * 24 ≤ 2 ^ 64 := by
          rw [← hsplit]; exact Nat.le_of_lt (Nat.lt_trans hlen (by decide))
        rw [sep_rejoin_loop, hsplit, ProofLib.memRegion_split cur 24 ((bs2 :: tl2).length * 24) hbound]
        exact Entails.refl _

/-! ## Compound Variants of Block `267` -/

private theorem drop_opt_proto_inner_state_ekReceivedCt1Sampled_cl [LibsignalPlacement] {A : RustAlloc}
    {ext : String → Option (State → State)}
    (hdealloc : HookSat (Rust.withPanics ext) spqrRustDeallocSym (rustDeallocSpec A))
    (st : V1State.Chunked.EkReceivedCt1Sampled) :
    subroutine_ok (lsProg_267 (Rust.withPanics ext)) (blkPl_267).base
      (withLsCodeLoaded lsmpl (dropOptProtoInnerStatePlacedVariantSpec A (some (.ekReceivedCt1Sampled st)))) := by
  change subroutine_ok ((blkPC_267).rebase (blkPl_267).base (Rust.withPanics ext)) (blkPl_267).base _
  apply subroutine_ok_withLsCodeLoaded_intro; intro m hcl
  dsimp only [withMemEq, dropOptProtoInnerStatePlacedVariantSpec, optProtoInnerStateAt,
    protoInnerStateAt, protoChunkedEkReceivedCt1SampledAt, optProtoInnerStateJumpTablePlacedAt,
    optProtoInnerStateJumpTableSym, optProtoInnerStateJumpTableBytes, optProtoInnerStateSize, BitVec.ofNat_eq_ofNat] at ⊢
  wp_init a s0; have hx0 : s0.readReg64 .x0 = a := by assumption
  have hm : s0.mem = m := (by assumption); subst hm
  have hfsp_align : ((s0.sp - 48#64) &&& 15#64 == 0#64) = true := spAligned_sub s0.sp 48#64 (by assumption) (by decide)
  have h136 : (a + 8#64) + 128#64 = a + 136#64 := BitVec.add_assoc a 8#64 128#64
  nth_rw 1 [stackAt_dropStack96_split s0.sp]; cells_unfold; wp_pull_exists; rename_i v_fp v_lr v_x22 v_x21 v_x20 v_x19
  refine seq_clean_lscl hcl (mid := (blkPl_267).base + 664#64)
    (P_mid := ((a ↦₆₄ 0x8000000000000008#64) ∗ memRegion (a + 8#64) 128 ∗
      optProtoPolynomialEncoderAt A (a + 136#64) (st.sendingCt1.map pbToProtoPolyEncoder) ∗
      memRegion (a + 192#64) 32) ∗ optProtoInnerStateJumpTablePlacedExpanded ∗
      A.pool ∗ (memRegion (s0.sp - 4192#64) 48 ∗ stackAt (s0.sp - 48#64) allocHookStack) ∗ SavedFrame48 s0)
    (Q := fun sm => Saved48Preserved s0 sm (s0.sp - 48#64) ∧ sm.readReg64 .x0 = a) ?_ ?_
  · cases huc : st.uc with
    | none =>
      have h16 : (a + 8#64) + 8#64 = a + 16#64 := BitVec.add_assoc a 8#64 8#64
      rw [optProtoUnchunkedCt1SentEkReceivedAt_none, h16]; wp_steps
      have hnone128 : ((a + 8#64) ↦₆₄ noneCap) ∗ memRegion (a + 16#64) 120 ⊢ memRegion (a + 8#64) 128 := by
        rw [← h16]; exact optProtoUnchunkedCt1SentEkReceivedAt_none_entails_memRegion_128 A (a + 8#64)
      refine SepWP.focus_weaken hnone128 (by sep_focus) ?_
      refine align_pre (by dsimp only [Reg.fp, Reg.lr, Reg.x19, Reg.x20, Reg.x21, Reg.x22,
        optProtoInnerStateJumpTablePlacedExpanded]; ac_rfl) ?_; wp_done
    | some u =>
      rw [optProtoUnchunkedCt1SentEkReceivedAt_some]
      refine SepWP.focus_weaken (protoUnchunkedCt1SentEkReceivedAt_expose_cap A (a + 8#64) u) (by sep_focus) ?_
      wp_pull_exists; rename_i cap ptr; wp_focus_pure; intro hcap_lt
      have hne_none := cap_add_one_beq_zero_false hcap_lt
      apply sepWP_seq_lscl hcl (mid := lsmpl.base 286); wp_steps
      apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs); intro hcl_call
      have hct1_sent := drop_proto_unchunked_ct1_sent_ek_received_mem_on (callerProg := lsProg_267 (Rust.withPanics ext)) hdealloc hcl_call
      dsimp only [lsProg_267, withMemEq, BitVec.ofNat_eq_ofNat] at hct1_sent
      refine SepWP.focus_weaken (protoUnchunkedCt1SentEkReceivedAt_unexpose_cap A (a + 8#64) cap ptr u) (by sep_focus) ?_
      refine SepWP.focus_weaken (Entails.of_eq (stackAt_sub48_split_32 s0.sp)) (by sep_focus) ?_
      wp_call hct1_sent ⟨a + 8#64, u⟩
      refine SepWP.focus_weaken (Entails.of_eq (stackAt_sub48_split_32 s0.sp).symm) (by sep_focus) ?_; wp_steps
      refine align_pre (by dsimp only [Reg.fp, Reg.lr, Reg.x19, Reg.x20, Reg.x21, Reg.x22,
        protoUnchunkedCt1SentEkReceivedSize, optProtoInnerStateJumpTablePlacedExpanded]; ac_rfl) ?_; wp_done
  · intro s1 hpc1 hrun1 hcl1 ⟨⟨hx23_1, hx24_1, hx25_1, hx26_1, hx27_1, hx28_1, hsp_1, htrace_1, hvregs_1⟩, hx0_1⟩
    dsimp only [optProtoInnerStateJumpTablePlacedExpanded]
    have hjoin184 : memRegion (a + 8#64) 128 ∗ memRegion (a + 136#64) 56 ⊢ memRegion (a + 8#64) 184 := by
      rw [← h136, ProofLib.memRegion_split (a + 8#64) 128 56 (by decide)]; exact Entails.refl _
    have hjoin224 : (a ↦₆₄ 0x8000000000000008#64) ∗ memRegion (a + 8#64) 184 ∗ memRegion (a + 192#64) 32 ⊢ memRegion a 224 :=
      tag_and_two_regions_entails_224 a 0x8000000000000008#64 184 32 192#64 (BitVec.add_assoc a 8#64 184#64).symm rfl
    cases hct1 : st.sendingCt1 with
    | none =>
      simp only [Option.map_none, optProtoPolynomialEncoderAt_none']
      have h144 : (a + 136#64) + 8#64 = a + 144#64 := BitVec.add_assoc a 136#64 8#64
      rw [h144]; wp_steps
      have hnone56 : ((a + 136#64) ↦₆₄ noneCap) ∗ memRegion (a + 144#64) 48 ⊢ memRegion (a + 136#64) 56 := by
        rw [← h144]; exact optProtoPolyEncoder_none_entails_memRegion_56 (a + 136#64)
      refine SepWP.focus_weaken hnone56 (by sep_focus) ?_; refine SepWP.focus_weaken hjoin184 (by sep_focus) ?_
      refine SepWP.focus_weaken hjoin224 (by sep_focus) ?_; refine SepWP.focus_weaken (restore_96 s0) (by sep_focus) ?_; wp_done
    | some enc =>
      simp only [Option.map_some, optProtoPolynomialEncoderAt_some']
      refine SepWP.focus_weaken (protoPolynomialEncoderAt_expose_cap A (a + 136#64) (pbToProtoPolyEncoder enc)) (by sep_focus) ?_
      wp_pull_exists; rename_i cap ptr; wp_focus_pure; intro hcap_lt
      have hne_none := cap_add_one_beq_zero_false hcap_lt
      apply sepWP_seq_lscl hcl1 (mid := lsmpl.base 271); wp_steps
      apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs); intro hcl_call
      have hpoly_enc := drop_glue_proto_poly_encoder_mem_on (callerProg := lsProg_267 (Rust.withPanics ext)) hdealloc hcl_call
      dsimp only [lsProg_267, withMemEq, BitVec.ofNat_eq_ofNat] at hpoly_enc
      refine SepWP.focus_weaken (protoPolynomialEncoderAt_unexpose_cap A (a + 136#64) cap ptr (pbToProtoPolyEncoder enc)) (by sep_focus) ?_
      refine SepWP.focus_weaken (restore_96 s0) (by sep_focus) ?_
      refine SepWP.focus_weaken (Entails.of_eq (stackAt_dropStack96_split_48 s0.sp)) (by sep_focus) ?_
      wp_call hpoly_enc ⟨a + 136#64, pbToProtoPolyEncoder enc⟩
      refine SepWP.focus_weaken (Entails.of_eq (stackAt_dropStack96_split_48 s0.sp).symm) (by sep_focus) ?_
      refine SepWP.focus_weaken hjoin184 (by sep_focus) ?_; refine SepWP.focus_weaken hjoin224 (by sep_focus) ?_; wp_done

private theorem drop_opt_proto_inner_state_ct2Sampled_cl [LibsignalPlacement] {A : RustAlloc}
    {ext : String → Option (State → State)}
    (hdealloc : HookSat (Rust.withPanics ext) spqrRustDeallocSym (rustDeallocSpec A))
    (st : V1State.Chunked.Ct2Sampled) :
    subroutine_ok (lsProg_267 (Rust.withPanics ext)) (blkPl_267).base
      (withLsCodeLoaded lsmpl (dropOptProtoInnerStatePlacedVariantSpec A (some (.ct2Sampled st)))) := by
  change subroutine_ok ((blkPC_267).rebase (blkPl_267).base (Rust.withPanics ext)) (blkPl_267).base _
  apply subroutine_ok_withLsCodeLoaded_intro; intro m hcl
  have hdealloc_raw : subroutine_ok ((blkPC_267).rebase (blkPl_267).base (Rust.withPanics ext))
      (lsρ spqrRustDeallocSym) (rustDeallocSpec A) := spqr_hook_ok_of_mem hdealloc
  simp only [rustDeallocSpec] at hdealloc_raw
  dsimp only [withMemEq, dropOptProtoInnerStatePlacedVariantSpec, optProtoInnerStateAt,
    protoInnerStateAt, protoChunkedCt2SampledAt, optProtoInnerStateJumpTablePlacedAt,
    optProtoInnerStateJumpTableSym, optProtoInnerStateJumpTableBytes, optProtoInnerStateSize, BitVec.ofNat_eq_ofNat] at hdealloc_raw ⊢
  wp_init a s0; have hx0 : s0.readReg64 .x0 = a := by assumption
  have hm : s0.mem = m := (by assumption); subst hm
  have hfsp_align : ((s0.sp - 48#64) &&& 15#64 == 0#64) = true := spAligned_sub s0.sp 48#64 (by assumption) (by decide)
  have h64 : (a + 8#64) + 56#64 = a + 64#64 := BitVec.add_assoc a 8#64 56#64
  nth_rw 1 [stackAt_dropStack96_split s0.sp]; cells_unfold; wp_pull_exists; rename_i v_fp v_lr v_x22 v_x21 v_x20 v_x19
  refine seq_clean_lscl hcl (mid := (blkPl_267).base + 600#64)
    (P_mid := ((a ↦₆₄ 0x800000000000000a#64) ∗
      optProtoPolynomialEncoderAt A (a + 8#64) (st.sendingCt2.map pbToProtoPolyEncoder) ∗
      memRegion (a + 64#64) 56 ∗ memRegion (a + 120#64) 104) ∗ optProtoInnerStateJumpTablePlacedExpanded ∗
      A.pool ∗ (memRegion (s0.sp - 4192#64) 48 ∗ stackAt (s0.sp - 48#64) allocHookStack) ∗ SavedFrame48 s0)
    (Q := fun sm => Saved48Preserved s0 sm (s0.sp - 48#64) ∧ sm.readReg64 .x0 = a) ?_ ?_
  · cases huc : st.uc with
    | none =>
      have h72 : (a + 64#64) + 8#64 = a + 72#64 := BitVec.add_assoc a 64#64 8#64
      dsimp only [optProtoUnchunkedCt2SentAt]; rw [h72]; wp_steps
      have hnone56 : ((a + 64#64) ↦₆₄ none2Cap) ∗ memRegion (a + 72#64) 48 ⊢ memRegion (a + 64#64) 56 := by
        rw [← h72]; exact optProtoUnchunkedNoHeaderReceivedAt_none_entails_memRegion_56 A (a + 64#64)
      refine SepWP.focus_weaken hnone56 (by sep_focus) ?_
      refine align_pre (by dsimp only [Reg.fp, Reg.lr, Reg.x19, Reg.x20, Reg.x21, Reg.x22,
        optProtoInnerStateJumpTablePlacedExpanded]; ac_rfl) ?_; wp_done
    | some u =>
      have h112 : (a + 64#64) + 48#64 = a + 112#64 := BitVec.add_assoc a 64#64 48#64
      dsimp only [optProtoUnchunkedCt2SentAt, protoUnchunkedCt2SentAt]; rw [h112]
      cases hauth : u.auth with
      | none =>
        have hnone64 : optProtoAuthenticatorAt A (a + 64#64) none = ((a + 64#64) ↦₆₄ noneCap) ∗ memRegion (a + 72#64) 40 := by
          rw [optProtoAuthenticatorAt_none, BitVec.add_assoc a 64#64 8#64]; rfl
        rw [hnone64]; wp_steps
        refine SepWP.focus_weaken (optProtoAuthenticatorAt_64_none_entails_memRegion_56 A a u.epoch) (by sep_focus) ?_
        refine align_pre (by dsimp only [Reg.fp, Reg.lr, Reg.x19, Reg.x20, Reg.x21, Reg.x22,
          optProtoInnerStateJumpTablePlacedExpanded]; ac_rfl) ?_; wp_done
      | some auth =>
        rw [optProtoAuthenticatorAt_some]
        refine SepWP.focus_weaken (protoAuthenticatorAt_entails_dealloc A (a + 64#64) auth) (by sep_focus) ?_
        wp_pull_exists; rename_i ga; rw [twoVecHeadersAt_64_eq]; wp_focus_pure; intro hga_lt
        have hne_none2 := cap_add_two_beq_zero_false hga_lt
        have hne_none1 := cap_add_one_beq_zero_false hga_lt
        refine seq_clean (mid := (blkPl_267).base + 568#64)
          (P_mid := ((a ↦₆₄ 0x800000000000000a#64) ∗
            optProtoPolynomialEncoderAt A (a + 8#64) (st.sendingCt2.map pbToProtoPolyEncoder) ∗
            ((auth64HeadersAt a ga ∗ vecCapPtrDealloc A ga.v2.cap ga.v2.ptr) ∗ ((a + 112#64) ↦₆₄ u.epoch)) ∗
            memRegion (a + 120#64) 104) ∗ optProtoInnerStateJumpTablePlacedExpanded ∗
            A.pool ∗ (memRegion (s0.sp - 4192#64) 48 ∗ stackAt (s0.sp - 48#64) allocHookStack) ∗ SavedFrame48 s0)
          (Q := fun sm => Saved48Preserved s0 sm (s0.sp - 48#64) ∧ sm.readReg64 .x0 = a) ?_ ?_
        · dsimp only [auth64HeadersAt, vecCapPtrDealloc]
          by_cases hca1 : (ga.v1.cap == 0#64) = true <;>
            simp only [hca1, Bool.false_eq_true, ↓reduceIte, sepConj_emp, emp_sepConj]
          · wp_steps; refine align_pre (by dsimp only [Reg.fp, Reg.lr, Reg.x19, Reg.x20, Reg.x21, Reg.x22,
              optProtoInnerStateJumpTablePlacedExpanded]; ac_rfl) ?_; wp_done
          · wp_steps; wp_apply; wp_steps
            refine align_pre (by dsimp only [Reg.fp, Reg.lr, Reg.x19, Reg.x20, Reg.x21, Reg.x22,
              optProtoInnerStateJumpTablePlacedExpanded]; ac_rfl) ?_; wp_done
        · intro sa1 hpca1 hruna1 ⟨⟨hx23_a1, hx24_a1, hx25_a1, hx26_a1, hx27_a1, hx28_a1, hsp_a1, htrace_a1, hvregs_a1⟩, hx0_a1⟩
          dsimp only [auth64HeadersAt, vecCapPtrDealloc]
          by_cases hca2 : (ga.v2.cap == 0#64) = true <;>
            simp only [hca2, Bool.false_eq_true, ↓reduceIte, sepConj_emp, emp_sepConj]
          · wp_steps; refine SepWP.focus_weaken (auth64HeadersAt_entails_memRegion_56 a ga u.epoch) (by sep_focus) ?_
            refine align_pre (by dsimp only [Reg.fp, Reg.lr, Reg.x19, Reg.x20, Reg.x21, Reg.x22,
              optProtoInnerStateJumpTablePlacedExpanded]; ac_rfl) ?_; wp_done
          · wp_steps; wp_apply; wp_steps
            refine SepWP.focus_weaken (auth64HeadersAt_entails_memRegion_56 a ga u.epoch) (by sep_focus) ?_
            refine align_pre (by rw [hsp_a1]; dsimp only [Reg.fp, Reg.lr, Reg.x19, Reg.x20, Reg.x21, Reg.x22,
              optProtoInnerStateJumpTablePlacedExpanded]; ac_rfl) ?_; wp_done
  · intro s1 hpc1 hrun1 hcl1 ⟨⟨hx23_1, hx24_1, hx25_1, hx26_1, hx27_1, hx28_1, hsp_1, htrace_1, hvregs_1⟩, hx0_1⟩
    dsimp only [optProtoInnerStateJumpTablePlacedExpanded]
    have hjoin112 : memRegion (a + 8#64) 56 ∗ memRegion (a + 64#64) 56 ⊢ memRegion (a + 8#64) 112 := by
      rw [← h64, ProofLib.memRegion_split (a + 8#64) 56 56 (by decide)]; exact Entails.refl _
    have hjoin224 : (a ↦₆₄ 0x800000000000000a#64) ∗ memRegion (a + 8#64) 112 ∗ memRegion (a + 120#64) 104 ⊢ memRegion a 224 :=
      tag_and_two_regions_entails_224 a 0x800000000000000a#64 112 104 120#64 (BitVec.add_assoc a 8#64 112#64).symm rfl
    cases hct2 : st.sendingCt2 with
    | none =>
      simp only [Option.map_none, optProtoPolynomialEncoderAt_none']
      have h16 : (a + 8#64) + 8#64 = a + 16#64 := BitVec.add_assoc a 8#64 8#64
      rw [h16]; wp_steps
      have hnone56 : ((a + 8#64) ↦₆₄ noneCap) ∗ memRegion (a + 16#64) 48 ⊢ memRegion (a + 8#64) 56 := by
        rw [← h16]; exact optProtoPolyEncoder_none_entails_memRegion_56 (a + 8#64)
      refine SepWP.focus_weaken hnone56 (by sep_focus) ?_; refine SepWP.focus_weaken hjoin112 (by sep_focus) ?_
      refine SepWP.focus_weaken hjoin224 (by sep_focus) ?_; refine SepWP.focus_weaken (restore_96 s0) (by sep_focus) ?_; wp_done
    | some enc =>
      simp only [Option.map_some, optProtoPolynomialEncoderAt_some']
      refine SepWP.focus_weaken (protoPolynomialEncoderAt_expose_cap A (a + 8#64) (pbToProtoPolyEncoder enc)) (by sep_focus) ?_
      wp_pull_exists; rename_i cap ptr; wp_focus_pure; intro hcap_lt
      have hne_none := cap_add_one_beq_zero_false hcap_lt
      apply sepWP_seq_lscl hcl1 (mid := lsmpl.base 271); wp_steps
      apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs); intro hcl_call
      have hpoly_enc := drop_glue_proto_poly_encoder_mem_on (callerProg := lsProg_267 (Rust.withPanics ext)) hdealloc hcl_call
      dsimp only [lsProg_267, withMemEq, BitVec.ofNat_eq_ofNat] at hpoly_enc
      refine SepWP.focus_weaken (protoPolynomialEncoderAt_unexpose_cap A (a + 8#64) cap ptr (pbToProtoPolyEncoder enc)) (by sep_focus) ?_
      refine SepWP.focus_weaken (restore_96 s0) (by sep_focus) ?_
      refine SepWP.focus_weaken (Entails.of_eq (stackAt_dropStack96_split_48 s0.sp)) (by sep_focus) ?_
      wp_call hpoly_enc ⟨a + 8#64, pbToProtoPolyEncoder enc⟩
      refine SepWP.focus_weaken (Entails.of_eq (stackAt_dropStack96_split_48 s0.sp).symm) (by sep_focus) ?_
      refine SepWP.focus_weaken hjoin112 (by sep_focus) ?_; refine SepWP.focus_weaken hjoin224 (by sep_focus) ?_; wp_done

private theorem drop_opt_proto_inner_state_ct1Acknowledged_cl [LibsignalPlacement] {A : RustAlloc}
    {ext : String → Option (State → State)}
    (hdealloc : HookSat (Rust.withPanics ext) spqrRustDeallocSym (rustDeallocSpec A))
    (st : V1State.Chunked.Ct1Acknowledged) :
    subroutine_ok (lsProg_267 (Rust.withPanics ext)) (blkPl_267).base
      (withLsCodeLoaded lsmpl (dropOptProtoInnerStatePlacedVariantSpec A (some (.ct1Acknowledged st)))) := by
  change subroutine_ok ((blkPC_267).rebase (blkPl_267).base (Rust.withPanics ext)) (blkPl_267).base _
  apply subroutine_ok_withLsCodeLoaded_intro; intro m hcl
  have hdealloc_raw : subroutine_ok ((blkPC_267).rebase (blkPl_267).base (Rust.withPanics ext))
      (lsρ spqrRustDeallocSym) (rustDeallocSpec A) := spqr_hook_ok_of_mem hdealloc
  have hloop := drop_opt_proto_inner_state_loop_192_cl hdealloc_raw
  simp only [rustDeallocSpec] at hdealloc_raw
  dsimp only [withMemEq, dropOptProtoInnerStatePlacedVariantSpec, optProtoInnerStateAt,
    protoInnerStateAt, protoChunkedCt1AcknowledgedAt, optProtoInnerStateJumpTablePlacedAt,
    optProtoInnerStateJumpTableSym, optProtoInnerStateJumpTableBytes, optProtoInnerStateSize, BitVec.ofNat_eq_ofNat] at hdealloc_raw hloop ⊢
  wp_init a s0; have hx0 : s0.readReg64 .x0 = a := by assumption
  have hm : s0.mem = m := (by assumption); subst hm
  have hfsp_align : ((s0.sp - 48#64) &&& 15#64 == 0#64) = true := spAligned_sub s0.sp 48#64 (by assumption) (by decide)
  have h136 : (a + 8#64) + 128#64 = a + 136#64 := BitVec.add_assoc a 8#64 128#64
  nth_rw 1 [stackAt_dropStack96_split s0.sp]; cells_unfold; wp_pull_exists; rename_i v_fp v_lr v_x22 v_x21 v_x20 v_x19
  refine seq_clean (mid := (blkPl_267).base + 164#64)
    (P_mid := ((a ↦₆₄ 0x8000000000000009#64) ∗ memRegion (a + 8#64) 128 ∗
      optProtoPolynomialDecoderAt A (a + 136#64) (st.receivingEk.map pbToProtoPolyDecoder) ∗
      memRegion (a + 176#64) 48) ∗ optProtoInnerStateJumpTablePlacedExpanded ∗
      A.pool ∗ (memRegion (s0.sp - 4192#64) 48 ∗ stackAt (s0.sp - 48#64) allocHookStack) ∗ SavedFrame48 s0)
    (Q := fun sm => Saved48Preserved s0 sm (s0.sp - 48#64) ∧ sm.readReg64 .x0 = a) ?_ ?_
  · cases huc : st.uc with
    | none =>
      have h16 : (a + 8#64) + 8#64 = a + 16#64 := BitVec.add_assoc a 8#64 8#64
      rw [optProtoUnchunkedCt1SentAt_none, h16]; wp_steps
      have hnone128 : ((a + 8#64) ↦₆₄ noneCap) ∗ memRegion (a + 16#64) 120 ⊢ memRegion (a + 8#64) 128 := by
        rw [← h16]; exact optProtoUnchunkedCt1SentEkReceivedAt_none_entails_memRegion_128 A (a + 8#64)
      refine SepWP.focus_weaken hnone128 (by sep_focus) ?_
      refine align_pre (by dsimp only [Reg.fp, Reg.lr, Reg.x19, Reg.x20, Reg.x21, Reg.x22,
        optProtoInnerStateJumpTablePlacedExpanded]; ac_rfl) ?_; wp_done
    | some u =>
      rw [optProtoUnchunkedCt1SentAt_some, protoUnchunkedCt1SentAt_eq_ct1SentEkReceived]
      refine SepWP.focus_weaken (protoUnchunkedCt1SentEkReceivedAt_expose_cap A (a + 8#64) (ct1SentToCt1SentEkReceived u)) (by sep_focus) ?_
      wp_pull_exists; rename_i cap ptr; wp_focus_pure; intro hcap_lt
      have hne_none := cap_add_one_beq_zero_false hcap_lt
      apply sepWP_seq_lscl hcl (mid := lsmpl.base 286); wp_steps
      apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs); intro hcl_call
      have hct1_sent := drop_proto_unchunked_ct1_sent_ek_received_mem_on (callerProg := lsProg_267 (Rust.withPanics ext)) hdealloc hcl_call
      dsimp only [lsProg_267, withMemEq, BitVec.ofNat_eq_ofNat] at hct1_sent
      refine SepWP.focus_weaken (protoUnchunkedCt1SentEkReceivedAt_unexpose_cap A (a + 8#64) cap ptr (ct1SentToCt1SentEkReceived u)) (by sep_focus) ?_
      refine SepWP.focus_weaken (Entails.of_eq (stackAt_sub48_split_32 s0.sp)) (by sep_focus) ?_
      wp_call hct1_sent ⟨a + 8#64, ct1SentToCt1SentEkReceived u⟩
      refine SepWP.focus_weaken (Entails.of_eq (stackAt_sub48_split_32 s0.sp).symm) (by sep_focus) ?_; wp_steps
      refine align_pre (by dsimp only [Reg.fp, Reg.lr, Reg.x19, Reg.x20, Reg.x21, Reg.x22,
        protoUnchunkedCt1SentEkReceivedSize, optProtoInnerStateJumpTablePlacedExpanded]; ac_rfl) ?_; wp_done
  · intro s1 hpc1 hrun1 ⟨⟨hx23_1, hx24_1, hx25_1, hx26_1, hx27_1, hx28_1, hsp_1, htrace_1, hvregs_1⟩, hx0_1⟩
    have hjoin168 : memRegion (a + 8#64) 128 ∗ memRegion (a + 136#64) 40 ⊢ memRegion (a + 8#64) 168 := by
      rw [← h136, ProofLib.memRegion_split (a + 8#64) 128 40 (by decide)]; exact Entails.refl _
    have hjoin224 : (a ↦₆₄ 0x8000000000000009#64) ∗ memRegion (a + 8#64) 168 ∗ memRegion (a + 176#64) 48 ⊢ memRegion a 224 :=
      tag_and_two_regions_entails_224 a 0x8000000000000009#64 168 48 176#64 (BitVec.add_assoc a 8#64 168#64).symm rfl
    cases hek : st.receivingEk with
    | none =>
      dsimp only [optProtoInnerStateJumpTablePlacedExpanded]
      simp only [Option.map_none, optProtoPolynomialDecoderAt_none']
      have h144 : (a + 136#64) + 8#64 = a + 144#64 := BitVec.add_assoc a 136#64 8#64
      rw [h144]; wp_steps
      have hnone40 : ((a + 136#64) ↦₆₄ noneCap) ∗ memRegion (a + 144#64) 32 ⊢ memRegion (a + 136#64) 40 := by
        rw [← h144]; exact optProtoPolyDecoder_none_entails_memRegion_40 (a + 136#64)
      refine SepWP.focus_weaken hnone40 (by sep_focus) ?_; refine SepWP.focus_weaken hjoin168 (by sep_focus) ?_
      refine SepWP.focus_weaken hjoin224 (by sep_focus) ?_; refine SepWP.focus_weaken (restore_96 s0) (by sep_focus) ?_; wp_done
    | some dec =>
      simp only [Option.map_some, optProtoPolynomialDecoderAt_some']
      let pb := pbToProtoPolyDecoder dec
      refine SepWP.focus_weaken (protoPolyDecoderAt_entails_dealloc A (a + 136#64) pb) (by sep_focus) ?_
      wp_pull_exists; rename_i g; wp_focus_pure; rintro ⟨hpts_le, hpts_cap_lt, hpts_ptr_ne⟩
      have hpts_cap_pow : g.cap.toNat < 2 ^ 63 := by omega
      have hne_none := cap_add_one_beq_zero_false hpts_cap_pow
      have h144 : (a + 136#64) + 8#64 = a + 144#64 := BitVec.add_assoc a 136#64 8#64
      have h152 : (a + 136#64) + 16#64 = a + 152#64 := BitVec.add_assoc a 136#64 16#64
      have h160 : (a + 136#64) + 24#64 = a + 160#64 := BitVec.add_assoc a 136#64 24#64
      refine seq_clean (mid := (blkPl_267).base + 444#64)
        (P_mid := (a ↦₆₄ 0x8000000000000009#64) ∗ memRegion (a + 8#64) 128 ∗
          ((a + 136#64) ↦₆₄ g.cap) ∗ ((a + 144#64) ↦₆₄ g.ptr) ∗ ((a + 152#64) ↦₆₄ BitVec.ofNat 64 pb.pts.length) ∗
          (if g.cap = 0 then emp else A.live g.ptr (g.cap.toNat * 24) 8 ∗ memRegion g.ptr (g.cap.toNat * 24)) ∗
          memRegion (a + 160#64) 16 ∗ memRegion (a + 176#64) 48 ∗ optProtoInnerStateJumpTablePlacedExpanded ∗
          A.pool ∗ (memRegion (s0.sp - 4192#64) 48 ∗ stackAt (s0.sp - 48#64) allocHookStack) ∗ SavedFrame48 s0)
        (Q := fun sm => Saved48Preserved s0 sm (s0.sp - 48#64) ∧ sm.readReg64 .x19 = g.ptr ∧ sm.readReg64 .x20 = g.cap) ?_ ?_
      · generalize hxs : pb.pts = xs at hpts_le ⊢
        cases xs with
        | nil =>
          simp only [List.length_nil, Nat.zero_mul, Nat.sub_zero, BitVec.ofNat_eq_ofNat, BitVec.add_zero, arrayAt, emp_sepConj]
          wp_steps; refine align_pre (by ac_rfl) ?_; wp_done
        | cons bs tl =>
          have hlen_pos : 0 < (bs :: tl).length := by simp
          have hlen_lt : (bs :: tl).length * 24 < 2 ^ 63 := by
            have : (bs :: tl).length * 24 ≤ g.cap.toNat * 24 := Nat.mul_le_mul_right 24 hpts_le; omega
          have hne0 := ofNat_beq_zero_false_24 hlen_pos hlen_lt
          have hcap_ne : g.cap ≠ 0 := by intro hc0; rw [hc0] at hpts_le; simp at hpts_le
          simp only [hcap_ne, ↓reduceIte]
          refine seq_clean (mid := (blkPl_267).base + 204#64)
            (P_mid := arrayAt (fun bs addr => vecU8 A addr bs) 24 g.ptr (bs :: tl) ∗ A.pool ∗ stackAt (s0.sp - 48#64) allocHookStack ∗
              ((a ↦₆₄ 0x8000000000000009#64) ∗ memRegion (a + 8#64) 128 ∗
               ((a + 136#64) ↦₆₄ g.cap) ∗ ((a + 144#64) ↦₆₄ g.ptr) ∗ ((a + 152#64) ↦₆₄ BitVec.ofNat 64 (bs :: tl).length) ∗
               A.live g.ptr (g.cap.toNat * 24) 8 ∗
               memRegion (g.ptr + BitVec.ofNat 64 ((bs :: tl).length * 24)) ((g.cap.toNat - (bs :: tl).length) * 24) ∗
               memRegion (a + 160#64) 16 ∗ memRegion (a + 176#64) 48 ∗ optProtoInnerStateJumpTablePlacedExpanded ∗ memRegion (s0.sp - 4192#64) 48 ∗ SavedFrame48 s0))
            (Q := fun sm => Saved48Preserved s0 sm (s0.sp - 48#64) ∧ sm.readReg64 .x19 = g.ptr ∧ sm.readReg64 .x20 = g.cap ∧
              sm.readReg64 .x21 = BitVec.ofNat 64 (bs :: tl).length ∧ sm.readReg64 .x22 = g.ptr + 8#64) ?_ ?_
          · wp_steps; refine align_pre (by ac_rfl) ?_; wp_done
          · intro s_loop hpc_loop hrun_loop ⟨hpres_loop, hx19_loop, hx20_loop, hx21_loop, hx22_loop⟩
            refine SepWP.strengthen_entails_const ?_
              (hloop s0 (s0.sp - 48#64) g.ptr g.cap hfsp_align (bs :: tl) g.ptr s_loop _
                (List.cons_ne_nil _ _) hlen_lt hpc_loop hrun_loop hpres_loop hx19_loop hx20_loop hx21_loop hx22_loop)
            have hsplit : g.cap.toNat * 24 = (bs :: tl).length * 24 + (g.cap.toNat - (bs :: tl).length) * 24 := by
              rw [← Nat.add_mul]; congr 1; omega
            have hbound : (bs :: tl).length * 24 + (g.cap.toNat - (bs :: tl).length) * 24 ≤ 2 ^ 64 := by rw [← hsplit]; omega
            conv_rhs =>
              arg 2; arg 2; arg 2; arg 2; arg 2; arg 1; arg 2
              rw [hsplit, ProofLib.memRegion_split g.ptr ((bs :: tl).length * 24) ((g.cap.toNat - (bs :: tl).length) * 24) hbound]
            exact Entails.of_eq (by ac_rfl)
      · intro s2 hpc2 hrun2 ⟨⟨hx23_2, hx24_2, hx25_2, hx26_2, hx27_2, hx28_2, hsp_2, htrace_2, hvregs_2⟩, hx19_2, hx20_2⟩
        dsimp only [optProtoInnerStateJumpTablePlacedExpanded]
        have hhdr40 : ((a + 136#64) ↦₆₄ g.cap) ∗ ((a + 144#64) ↦₆₄ g.ptr) ∗
            ((a + 152#64) ↦₆₄ BitVec.ofNat 64 pb.pts.length) ∗ memRegion (a + 160#64) 16 ⊢ memRegion (a + 136#64) 40 := by
          rw [← h144, ← h152, ← h160]
          exact protoPolyDecoderHeaders_entails_memRegion_40 (a + 136#64) g.cap g.ptr (BitVec.ofNat 64 pb.pts.length)
        by_cases hc : g.cap = 0
        · have hc_beq : (g.cap == 0#64) = true := by rw [beq_iff_eq]; exact hc
          simp only [hc, ↓reduceIte, emp_sepConj, sepConj_emp] at hx20_2 hhdr40 ⊢; wp_steps
          refine SepWP.focus_weaken hhdr40 (by sep_focus) ?_; refine SepWP.focus_weaken hjoin168 (by sep_focus) ?_
          refine SepWP.focus_weaken hjoin224 (by sep_focus) ?_; refine SepWP.focus_weaken (restore_96 s0) (by sep_focus) ?_; wp_done
        · have hc_beq : ¬((g.cap == 0#64) = true) := by rw [beq_iff_eq]; exact hc
          have hlsl := cap_mul_24 hpts_cap_lt; simp only [hc, ↓reduceIte]; wp_steps
          refine SepWP.focus_weaken hhdr40 (by sep_focus) ?_; refine SepWP.focus_weaken hjoin168 (by sep_focus) ?_
          refine SepWP.focus_weaken hjoin224 (by sep_focus) ?_; refine SepWP.focus_weaken (restore_96 s0) (by sep_focus) ?_
          refine SepWP.focus_weaken (Entails.of_eq (stackAt_dropStack96_split_bottom s0.sp)) (by sep_focus) ?_
          wp_call hdealloc_raw (g.ptr, g.cap.toNat * 24, 8)
          refine SepWP.focus_weaken (Entails.of_eq (stackAt_dropStack96_split_bottom s0.sp).symm) (by sep_focus) ?_; wp_done

private theorem drop_opt_proto_inner_state_ct1Sampled_cl [LibsignalPlacement] {A : RustAlloc}
    {ext : String → Option (State → State)}
    (hdealloc : HookSat (Rust.withPanics ext) spqrRustDeallocSym (rustDeallocSpec A))
    (st : V1State.Chunked.Ct1Sampled) :
    subroutine_ok (lsProg_267 (Rust.withPanics ext)) (blkPl_267).base
      (withLsCodeLoaded lsmpl (dropOptProtoInnerStatePlacedVariantSpec A (some (.ct1Sampled st)))) := by
  change subroutine_ok ((blkPC_267).rebase (blkPl_267).base (Rust.withPanics ext)) (blkPl_267).base _
  apply subroutine_ok_withLsCodeLoaded_intro; intro m hcl
  have hdealloc_raw : subroutine_ok ((blkPC_267).rebase (blkPl_267).base (Rust.withPanics ext))
      (lsρ spqrRustDeallocSym) (rustDeallocSpec A) := spqr_hook_ok_of_mem hdealloc
  have hloop := drop_opt_proto_inner_state_loop_408_cl hdealloc_raw
  simp only [rustDeallocSpec] at hdealloc_raw
  dsimp only [withMemEq, dropOptProtoInnerStatePlacedVariantSpec, optProtoInnerStateAt,
    protoInnerStateAt, protoChunkedCt1SampledAt, optProtoInnerStateJumpTablePlacedAt,
    optProtoInnerStateJumpTableSym, optProtoInnerStateJumpTableBytes, optProtoInnerStateSize, BitVec.ofNat_eq_ofNat] at hdealloc_raw hloop ⊢
  wp_init a s0; have hx0 : s0.readReg64 .x0 = a := by assumption
  have hm : s0.mem = m := (by assumption); subst hm
  have hfsp_align : ((s0.sp - 48#64) &&& 15#64 == 0#64) = true := spAligned_sub s0.sp 48#64 (by assumption) (by decide)
  nth_rw 1 [stackAt_dropStack96_split s0.sp]; cells_unfold; wp_pull_exists; rename_i v_fp v_lr v_x22 v_x21 v_x20 v_x19
  refine seq_clean_lscl hcl (mid := (blkPl_267).base + 348#64)
    (P_mid := (memRegion a 128 ∗
      optProtoPolynomialEncoderAt A (a + 128#64) (st.sendingCt1.map pbToProtoPolyEncoder) ∗
      optProtoPolynomialDecoderAt A (a + 184#64) (st.receivingEk.map pbToProtoPolyDecoder)) ∗ optProtoInnerStateJumpTablePlacedExpanded ∗
      A.pool ∗ (memRegion (s0.sp - 4192#64) 48 ∗ stackAt (s0.sp - 48#64) allocHookStack) ∗ SavedFrame48 s0)
    (Q := fun sm => Saved48Preserved s0 sm (s0.sp - 48#64) ∧ sm.readReg64 .x0 = a) ?_ ?_
  · cases huc : st.uc with
    | none =>
      rw [optProtoUnchunkedCt1SentAt_none]; wp_steps
      have hnone128 : (a ↦₆₄ noneCap) ∗ memRegion (a + 8#64) 120 ⊢ memRegion a 128 :=
        optProtoUnchunkedCt1SentEkReceivedAt_none_entails_memRegion_128 A a
      refine SepWP.focus_weaken hnone128 (by sep_focus) ?_
      refine align_pre (by dsimp only [Reg.fp, Reg.lr, Reg.x19, Reg.x20, Reg.x21, Reg.x22,
        optProtoInnerStateJumpTablePlacedExpanded]; ac_rfl) ?_; wp_done
    | some u =>
      rw [optProtoUnchunkedCt1SentAt_some, protoUnchunkedCt1SentAt_eq_ct1SentEkReceived]
      refine SepWP.focus_weaken (protoUnchunkedCt1SentEkReceivedAt_expose_cap A a (ct1SentToCt1SentEkReceived u)) (by sep_focus) ?_
      wp_pull_exists; rename_i cap ptr; wp_focus_pure; intro hcap_lt
      have hne_none2 := cap_add_two_beq_zero_false hcap_lt
      have hne_none1 := cap_add_one_beq_zero_false hcap_lt
      have hcc_false := cap_xor_highBit_cc_11_false hcap_lt
      apply sepWP_seq_lscl hcl (mid := lsmpl.base 286); wp_steps
      apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs); intro hcl_call
      have hct1_sent := drop_proto_unchunked_ct1_sent_ek_received_mem_on (callerProg := lsProg_267 (Rust.withPanics ext)) hdealloc hcl_call
      dsimp only [lsProg_267, withMemEq, BitVec.ofNat_eq_ofNat] at hct1_sent
      refine SepWP.focus_weaken (protoUnchunkedCt1SentEkReceivedAt_unexpose_cap A a cap ptr (ct1SentToCt1SentEkReceived u)) (by sep_focus) ?_
      refine SepWP.focus_weaken (Entails.of_eq (stackAt_sub48_split_32 s0.sp)) (by sep_focus) ?_
      wp_call hct1_sent ⟨a, ct1SentToCt1SentEkReceived u⟩
      refine SepWP.focus_weaken (Entails.of_eq (stackAt_sub48_split_32 s0.sp).symm) (by sep_focus) ?_; wp_steps
      refine align_pre (by dsimp only [Reg.fp, Reg.lr, Reg.x19, Reg.x20, Reg.x21, Reg.x22,
        protoUnchunkedCt1SentEkReceivedSize, optProtoInnerStateJumpTablePlacedExpanded]; ac_rfl) ?_; wp_done
  · intro s1 hpc1 hrun1 hcl1 ⟨⟨hx23_1, hx24_1, hx25_1, hx26_1, hx27_1, hx28_1, hsp_1, htrace_1, hvregs_1⟩, hx0_1⟩
    refine seq_clean (mid := (blkPl_267).base + 380#64)
      (P_mid := (memRegion a 184 ∗
        optProtoPolynomialDecoderAt A (a + 184#64) (st.receivingEk.map pbToProtoPolyDecoder)) ∗ optProtoInnerStateJumpTablePlacedExpanded ∗
        A.pool ∗ (memRegion (s0.sp - 4192#64) 48 ∗ stackAt (s0.sp - 48#64) allocHookStack) ∗ SavedFrame48 s0)
      (Q := fun sm => Saved48Preserved s0 sm (s0.sp - 48#64) ∧ sm.readReg64 .x0 = a) ?_ ?_
    · have hjoin184 : memRegion a 128 ∗ memRegion (a + 128#64) 56 ⊢ memRegion a 184 := by
        rw [ProofLib.memRegion_split a 128 56 (by decide)]; exact Entails.refl _
      cases hct1 : st.sendingCt1 with
      | none =>
        simp only [Option.map_none, optProtoPolynomialEncoderAt_none']
        have h136 : (a + 128#64) + 8#64 = a + 136#64 := BitVec.add_assoc a 128#64 8#64
        rw [h136]; wp_steps
        have hnone56 : ((a + 128#64) ↦₆₄ noneCap) ∗ memRegion (a + 136#64) 48 ⊢ memRegion (a + 128#64) 56 := by
          rw [← h136]; exact optProtoPolyEncoder_none_entails_memRegion_56 (a + 128#64)
        refine SepWP.focus_weaken hnone56 (by sep_focus) ?_; refine SepWP.focus_weaken hjoin184 (by sep_focus) ?_
        refine align_pre (by ac_rfl) ?_; wp_done
      | some enc =>
        simp only [Option.map_some, optProtoPolynomialEncoderAt_some']
        refine SepWP.focus_weaken (protoPolynomialEncoderAt_expose_cap A (a + 128#64) (pbToProtoPolyEncoder enc)) (by sep_focus) ?_
        wp_pull_exists; rename_i cap ptr; wp_focus_pure; intro hcap_lt
        have hne_none := cap_add_one_beq_zero_false hcap_lt
        apply sepWP_seq_lscl hcl1 (mid := lsmpl.base 271); wp_steps
        apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs); intro hcl_call
        have hpoly_enc := drop_glue_proto_poly_encoder_mem_on (callerProg := lsProg_267 (Rust.withPanics ext)) hdealloc hcl_call
        dsimp only [lsProg_267, withMemEq, BitVec.ofNat_eq_ofNat] at hpoly_enc
        refine SepWP.focus_weaken (protoPolynomialEncoderAt_unexpose_cap A (a + 128#64) cap ptr (pbToProtoPolyEncoder enc)) (by sep_focus) ?_
        refine SepWP.focus_weaken (Entails.of_eq (stackAt_sub48_eq_dropStack48 s0.sp)) (by sep_focus) ?_
        wp_call hpoly_enc ⟨a + 128#64, pbToProtoPolyEncoder enc⟩
        have hsp_eq : stackAt s1.sp dropStack48 = memRegion (s0.sp - 4192#64) 48 ∗ stackAt (s0.sp - 48#64) allocHookStack := by
          rw [hsp_1, ← stackAt_sub48_eq_dropStack48]
        refine SepWP.focus_weaken (Entails.of_eq hsp_eq) (by sep_focus) ?_; wp_steps
        change _ at hjoin184; refine SepWP.focus_weaken hjoin184 (by sep_focus) ?_
        refine align_pre (by dsimp only [Reg.fp, Reg.lr, Reg.x19, Reg.x20, Reg.x21, Reg.x22]; ac_rfl) ?_; wp_done
    · intro s2 hpc2 hrun2 ⟨⟨hx23_2, hx24_2, hx25_2, hx26_2, hx27_2, hx28_2, hsp_2, htrace_2, hvregs_2⟩, hx0_2⟩
      have hjoin224 : memRegion a 184 ∗ memRegion (a + 184#64) 40 ⊢ memRegion a 224 := by
        rw [ProofLib.memRegion_split a 184 40 (by decide)]; exact Entails.refl _
      cases hek : st.receivingEk with
      | none =>
        dsimp only [optProtoInnerStateJumpTablePlacedExpanded]
        simp only [Option.map_none, optProtoPolynomialDecoderAt_none']
        have h192 : (a + 184#64) + 8#64 = a + 192#64 := BitVec.add_assoc a 184#64 8#64
        rw [h192]; wp_steps
        have hnone40 : ((a + 184#64) ↦₆₄ noneCap) ∗ memRegion (a + 192#64) 32 ⊢ memRegion (a + 184#64) 40 := by
          rw [← h192]; exact optProtoPolyDecoder_none_entails_memRegion_40 (a + 184#64)
        refine SepWP.focus_weaken hnone40 (by sep_focus) ?_; refine SepWP.focus_weaken hjoin224 (by sep_focus) ?_
        refine SepWP.focus_weaken (restore_96 s0) (by sep_focus) ?_; wp_done
      | some dec =>
        simp only [Option.map_some, optProtoPolynomialDecoderAt_some']
        let pb := pbToProtoPolyDecoder dec
        refine SepWP.focus_weaken (protoPolyDecoderAt_entails_dealloc A (a + 184#64) pb) (by sep_focus) ?_
        wp_pull_exists; rename_i g; wp_focus_pure; rintro ⟨hpts_le, hpts_cap_lt, hpts_ptr_ne⟩
        have hpts_cap_pow : g.cap.toNat < 2 ^ 63 := by omega
        have hne_none := cap_add_one_beq_zero_false hpts_cap_pow
        have h192 : (a + 184#64) + 8#64 = a + 192#64 := BitVec.add_assoc a 184#64 8#64
        have h200 : (a + 184#64) + 16#64 = a + 200#64 := BitVec.add_assoc a 184#64 16#64
        have h208 : (a + 184#64) + 24#64 = a + 208#64 := BitVec.add_assoc a 184#64 24#64
        refine seq_clean (mid := (blkPl_267).base + 444#64)
          (P_mid := memRegion a 184 ∗
            ((a + 184#64) ↦₆₄ g.cap) ∗ ((a + 192#64) ↦₆₄ g.ptr) ∗ ((a + 200#64) ↦₆₄ BitVec.ofNat 64 pb.pts.length) ∗
            (if g.cap = 0 then emp else A.live g.ptr (g.cap.toNat * 24) 8 ∗ memRegion g.ptr (g.cap.toNat * 24)) ∗
            memRegion (a + 208#64) 16 ∗ optProtoInnerStateJumpTablePlacedExpanded ∗
            A.pool ∗ (memRegion (s0.sp - 4192#64) 48 ∗ stackAt (s0.sp - 48#64) allocHookStack) ∗ SavedFrame48 s0)
          (Q := fun sm => Saved48Preserved s0 sm (s0.sp - 48#64) ∧ sm.readReg64 .x19 = g.ptr ∧ sm.readReg64 .x20 = g.cap) ?_ ?_
        · generalize hxs : pb.pts = xs at hpts_le ⊢
          cases xs with
          | nil =>
            simp only [List.length_nil, Nat.zero_mul, Nat.sub_zero, BitVec.ofNat_eq_ofNat, BitVec.add_zero, arrayAt, emp_sepConj]
            wp_steps; refine align_pre (by ac_rfl) ?_; wp_done
          | cons bs tl =>
            have hlen_pos : 0 < (bs :: tl).length := by simp
            have hlen_lt : (bs :: tl).length * 24 < 2 ^ 63 := by
              have : (bs :: tl).length * 24 ≤ g.cap.toNat * 24 := Nat.mul_le_mul_right 24 hpts_le; omega
            have hne0 := ofNat_beq_zero_false_24 hlen_pos hlen_lt
            have hcap_ne : g.cap ≠ 0 := by intro hc0; rw [hc0] at hpts_le; simp at hpts_le
            simp only [hcap_ne, ↓reduceIte]
            refine seq_clean (mid := (blkPl_267).base + 420#64)
              (P_mid := arrayAt (fun bs addr => vecU8 A addr bs) 24 g.ptr (bs :: tl) ∗ A.pool ∗ stackAt (s0.sp - 48#64) allocHookStack ∗
                (memRegion a 184 ∗ ((a + 184#64) ↦₆₄ g.cap) ∗ ((a + 192#64) ↦₆₄ g.ptr) ∗
                 ((a + 200#64) ↦₆₄ BitVec.ofNat 64 (bs :: tl).length) ∗ A.live g.ptr (g.cap.toNat * 24) 8 ∗
                 memRegion (g.ptr + BitVec.ofNat 64 ((bs :: tl).length * 24)) ((g.cap.toNat - (bs :: tl).length) * 24) ∗
                 memRegion (a + 208#64) 16 ∗ optProtoInnerStateJumpTablePlacedExpanded ∗ memRegion (s0.sp - 4192#64) 48 ∗ SavedFrame48 s0))
              (Q := fun sm => Saved48Preserved s0 sm (s0.sp - 48#64) ∧ sm.readReg64 .x19 = g.ptr ∧ sm.readReg64 .x20 = g.cap ∧
                sm.readReg64 .x21 = BitVec.ofNat 64 (bs :: tl).length ∧ sm.readReg64 .x22 = g.ptr + 8#64) ?_ ?_
            · wp_steps; refine align_pre (by ac_rfl) ?_; wp_done
            · intro s_loop hpc_loop hrun_loop ⟨hpres_loop, hx19_loop, hx20_loop, hx21_loop, hx22_loop⟩
              refine SepWP.strengthen_entails_const ?_
                (hloop s0 (s0.sp - 48#64) g.ptr g.cap hfsp_align (bs :: tl) g.ptr s_loop _
                  (List.cons_ne_nil _ _) hlen_lt hpc_loop hrun_loop hpres_loop hx19_loop hx20_loop hx21_loop hx22_loop)
              have hsplit : g.cap.toNat * 24 = (bs :: tl).length * 24 + (g.cap.toNat - (bs :: tl).length) * 24 := by
                rw [← Nat.add_mul]; congr 1; omega
              have hbound : (bs :: tl).length * 24 + (g.cap.toNat - (bs :: tl).length) * 24 ≤ 2 ^ 64 := by rw [← hsplit]; omega
              conv_rhs =>
                arg 2; arg 2; arg 2; arg 2; arg 1; arg 2
                rw [hsplit, ProofLib.memRegion_split g.ptr ((bs :: tl).length * 24) ((g.cap.toNat - (bs :: tl).length) * 24) hbound]
              exact Entails.of_eq (by ac_rfl)
        · intro s3 hpc3 hrun3 ⟨⟨hx23_3, hx24_3, hx25_3, hx26_3, hx27_3, hx28_3, hsp_3, htrace_3, hvregs_3⟩, hx19_3, hx20_3⟩
          dsimp only [optProtoInnerStateJumpTablePlacedExpanded]
          have hhdr40 : ((a + 184#64) ↦₆₄ g.cap) ∗ ((a + 192#64) ↦₆₄ g.ptr) ∗
              ((a + 200#64) ↦₆₄ BitVec.ofNat 64 pb.pts.length) ∗ memRegion (a + 208#64) 16 ⊢ memRegion (a + 184#64) 40 := by
            rw [← h192, ← h200, ← h208]
            exact protoPolyDecoderHeaders_entails_memRegion_40 (a + 184#64) g.cap g.ptr (BitVec.ofNat 64 pb.pts.length)
          by_cases hc : g.cap = 0
          · have hc_beq : (g.cap == 0#64) = true := by rw [beq_iff_eq]; exact hc
            simp only [hc, ↓reduceIte, emp_sepConj, sepConj_emp] at hx20_3 hhdr40 ⊢; wp_steps
            refine SepWP.focus_weaken hhdr40 (by sep_focus) ?_; refine SepWP.focus_weaken hjoin224 (by sep_focus) ?_
            refine SepWP.focus_weaken (restore_96 s0) (by sep_focus) ?_; wp_done
          · have hc_beq : ¬((g.cap == 0#64) = true) := by rw [beq_iff_eq]; exact hc
            have hlsl := cap_mul_24 hpts_cap_lt; simp only [hc, ↓reduceIte]; wp_steps
            refine SepWP.focus_weaken hhdr40 (by sep_focus) ?_; refine SepWP.focus_weaken hjoin224 (by sep_focus) ?_
            refine SepWP.focus_weaken (restore_96 s0) (by sep_focus) ?_
            refine SepWP.focus_weaken (Entails.of_eq (stackAt_dropStack96_split_bottom s0.sp)) (by sep_focus) ?_
            wp_call hdealloc_raw (g.ptr, g.cap.toNat * 24, 8)
            refine SepWP.focus_weaken (Entails.of_eq (stackAt_dropStack96_split_bottom s0.sp).symm) (by sep_focus) ?_; wp_done

/-! ## Top-Level Block `267` Contract (`Option<V1State.InnerState>`) -/

theorem drop_opt_proto_inner_state_cl_placed_ok [LibsignalPlacement] {A : RustAlloc}
    {ext : String → Option (State → State)}
    (hdealloc : HookSat (Rust.withPanics ext) spqrRustDeallocSym (rustDeallocSpec A)) :
    subroutine_ok (lsProg_267 (Rust.withPanics ext)) (lsmpl.base 267)
      (withLsCodeLoaded lsmpl (dropOptProtoInnerStatePlacedSpec A)) := by
  rw [← ls_blockPlacement_base (i := 267)]
  refine subroutine_ok_outcome_intro fun ⟨a, optSt⟩ R s0 hpc hrun hpre hsp => ?_
  cases optSt with
  | none =>
    exact drop_opt_proto_inner_state_none_cl.mono_outcome a R s0 hpc hrun hpre hsp fun _ hout => hout
  | some st =>
    cases st with
    | keysUnsampled s =>
      exact (drop_opt_proto_inner_state_keysUnsampled_cl hdealloc s).mono_outcome a R s0 hpc hrun hpre hsp fun _ hout => hout
    | keysSampled s =>
      exact (drop_opt_proto_inner_state_keysSampled_cl hdealloc s).mono_outcome a R s0 hpc hrun hpre hsp fun _ hout => hout
    | headerSent s =>
      exact (drop_opt_proto_inner_state_headerSent_cl hdealloc s).mono_outcome a R s0 hpc hrun hpre hsp fun _ hout => hout
    | ct1Received s =>
      exact (drop_opt_proto_inner_state_ct1Received_cl hdealloc s).mono_outcome a R s0 hpc hrun hpre hsp fun _ hout => hout
    | ekSentCt1Received s =>
      exact (drop_opt_proto_inner_state_ekSentCt1Received_cl hdealloc s).mono_outcome a R s0 hpc hrun hpre hsp fun _ hout => hout
    | noHeaderReceived s =>
      exact (drop_opt_proto_inner_state_noHeaderReceived_cl hdealloc s).mono_outcome a R s0 hpc hrun hpre hsp fun _ hout => hout
    | headerReceived s =>
      exact (drop_opt_proto_inner_state_headerReceived_cl hdealloc s).mono_outcome a R s0 hpc hrun hpre hsp fun _ hout => hout
    | ct1Sampled s =>
      exact (drop_opt_proto_inner_state_ct1Sampled_cl hdealloc s).mono_outcome a R s0 hpc hrun hpre hsp fun _ hout => hout
    | ekReceivedCt1Sampled s =>
      exact (drop_opt_proto_inner_state_ekReceivedCt1Sampled_cl hdealloc s).mono_outcome a R s0 hpc hrun hpre hsp fun _ hout => hout
    | ct1Acknowledged s =>
      exact (drop_opt_proto_inner_state_ct1Acknowledged_cl hdealloc s).mono_outcome a R s0 hpc hrun hpre hsp fun _ hout => hout
    | ct2Sampled s =>
      exact (drop_opt_proto_inner_state_ct2Sampled_cl hdealloc s).mono_outcome a R s0 hpc hrun hpre hsp fun _ hout => hout

theorem drop_opt_proto_inner_state_cl_blockProgram [LibsignalPlacement] {A : RustAlloc}
    {ext : String → Option (State → State)}
    (hdealloc : HookSat (Rust.withPanics ext) spqrRustDeallocSym (rustDeallocSpec A)) :
    subroutine_ok (libsignalSessionLib.blockProgram lsmpl 267 (Rust.withPanics ext)) (lsmpl.base 267)
      (withLsCodeLoaded lsmpl (dropOptProtoInnerStatePlacedSpec A)) :=
  ls_to_blockProgram (drop_opt_proto_inner_state_cl_placed_ok hdealloc)

theorem drop_opt_proto_inner_state_mem_on [LibsignalPlacement] {A : RustAlloc}
    {callerProg : Program} {idx : Nat} {ext : String → Option (State → State)}
    [IsLsBlockProg callerProg idx (Rust.withPanics ext)] {m : Memory}
    (hdealloc : HookSat (Rust.withPanics ext) spqrRustDeallocSym (rustDeallocSpec A))
    (hcl : LibsignalCodeLoaded lsmpl m) (hidx : idx < 619 := by decide) :
    subroutine_ok callerProg (lsmpl.base 267)
      (withMemEq m (dropOptProtoInnerStatePlacedSpec A)) :=
  lscall_blk_cl (drop_opt_proto_inner_state_cl_placed_ok hdealloc) hcl hidx

/-! ## Block `270`: `drop_glue::<spqr::proto::pq_ratchet::PqRatchetState>` -/

theorem drop_proto_pq_ratchet_state_cl_placed_ok [LibsignalPlacement] {A : RustAlloc}
    {ext : String → Option (State → State)}
    (hdealloc : HookSat (Rust.withPanics ext) spqrRustDeallocSym (rustDeallocSpec A)) :
    subroutine_ok (lsProg_270 (Rust.withPanics ext)) (lsmpl.base 270)
      (withLsCodeLoaded lsmpl (dropProtoPqRatchetStatePlacedSpec A)) := by
  rw [← ls_blockPlacement_base (i := 270)]
  change subroutine_ok ((blkPC_270).rebase (blkPl_270).base (Rust.withPanics ext)) (blkPl_270).base _
  apply subroutine_ok_withLsCodeLoaded_intro; intro m hcl
  have hdealloc_raw : subroutine_ok ((blkPC_270).rebase (blkPl_270).base (Rust.withPanics ext))
      (lsρ spqrRustDeallocSym) (rustDeallocSpec A) := spqr_hook_ok_of_mem hdealloc
  simp only [rustDeallocSpec] at hdealloc_raw
  dsimp only [withMemEq, dropProtoPqRatchetStatePlacedSpec, protoPqRatchetStateAt,
    protoPqRatchetStateSize, optProtoInnerStateSize, chainEpochPBSize,
    BitVec.ofNat_eq_ofNat] at hdealloc_raw ⊢
  wp_init x s0
  rcases x with ⟨a, st⟩
  have hx0 : s0.readReg64 .x0 = a := by assumption
  have hm : s0.mem = m := by assumption
  subst hm
  dsimp only [DropProtoPqRatchetStateGhost.a, DropProtoPqRatchetStateGhost.st] at *
  have hfsp_align : ((s0.sp - 48#64) &&& 15#64 == 0#64) = true := spAligned_sub s0.sp 48#64 (by assumption) (by decide)
  nth_rw 1 [stackAt_dropStack96_split s0.sp]; cells_unfold; wp_pull_exists
  rename_i v_fp v_lr v_x22 v_x21 v_x20 v_x19
  refine seq_clean_lscl hcl (mid := (blkPl_270).base + 44#64)
    (P_mid := (memRegion a 48 ∗ optChainPBAt A (a + 48#64) st.chain ∗
      optProtoPqRatchetInnerAt A (a + 128#64) st.inner) ∗ optProtoInnerStateJumpTablePlacedAt ∗
      A.pool ∗ (memRegion (s0.sp - 4192#64) 48 ∗ stackAt (s0.sp - 48#64) allocHookStack) ∗
      (((s0.sp - 48#64) ↦₆₄ s0.readReg64 .fp) ∗ ((s0.sp - 40#64) ↦₆₄ s0.readReg64 .lr) ∗
       ((s0.sp - 32#64) ↦₆₄ s0.readReg64 .x21) ∗ ((s0.sp - 24#64) ↦₆₄ v_x21) ∗
       ((s0.sp - 16#64) ↦₆₄ s0.readReg64 .x20) ∗ ((s0.sp - 8#64) ↦₆₄ s0.readReg64 .x19)))
    (Q := fun sm => Saved48Preserved s0 sm (s0.sp - 48#64) ∧ sm.readReg64 .x22 = s0.readReg64 .x22 ∧ sm.readReg64 .x19 = a) ?_ ?_
  · cases hvn : st.versionNegotiation with
    | none =>
      dsimp only [optVersionNegotiationPBAt]; wp_steps
      refine SepWP.focus_weaken (optVersionNegotiationPBAt_none_entails_memRegion_48 a) (by sep_focus) ?_
      refine align_pre (by simp only [Reg.fp, Reg.lr, Reg.x19, Reg.x20, Reg.x21]; try ac_rfl) ?_; wp_done
    | some vn =>
      dsimp only [optVersionNegotiationPBAt]
      refine SepWP.focus_weaken (versionNegotiationPBAt_entails_dealloc A a vn) (by sep_focus) ?_
      wp_pull_exists; rename_i g; rcases g with ⟨cap, ptr⟩; wp_focus_pure; intro hcap_lt
      dsimp only [vecCapPtrDealloc] at hcap_lt ⊢
      have hne_none := cap_add_one_beq_zero_false hcap_lt
      by_cases hc0 : (cap == 0#64) = true <;>
        simp only [hc0, Bool.false_eq_true, ↓reduceIte, emp_sepConj, sepConj_emp]
      · have hc_eq : cap = 0#64 := by rwa [beq_iff_eq] at hc0
        subst hc_eq; wp_steps
        refine SepWP.focus_weaken (vnHeader_entails_memRegion_48 a 0#64 ptr) (by sep_focus) ?_
        refine align_pre (by simp only [Reg.fp, Reg.lr, Reg.x19, Reg.x20, Reg.x21]; try ac_rfl) ?_; wp_done
      · have hslt := cap_ne_zero_slt_one_false hcap_lt hc0
        have hlt_false := cap_ne_zero_lt_one_false hcap_lt hc0
        wp_steps; wp_apply
        refine SepWP.focus_weaken (vnHeader_entails_memRegion_48 a cap ptr) (by sep_focus) ?_
        refine align_pre (by simp only [Reg.fp, Reg.lr, Reg.x19, Reg.x20, Reg.x21]; try ac_rfl) ?_; wp_done
  · intro s1 hpc1 hrun1 hcl1 ⟨⟨hx23_1, hx24_1, hx25_1, hx26_1, hx27_1, hx28_1, hsp_1, htrace_1, hvregs_1⟩, hx22_1, hx19_1⟩
    refine seq_clean_lscl hcl1 (mid := (blkPl_270).base + 112#64)
      (P_mid := (memRegion a 128 ∗ optProtoPqRatchetInnerAt A (a + 128#64) st.inner) ∗ optProtoInnerStateJumpTablePlacedAt ∗
        A.pool ∗ (memRegion (s0.sp - 4192#64) 48 ∗ stackAt (s0.sp - 48#64) allocHookStack) ∗
        (((s0.sp - 48#64) ↦₆₄ s0.readReg64 .fp) ∗ ((s0.sp - 40#64) ↦₆₄ s0.readReg64 .lr) ∗
         ((s0.sp - 32#64) ↦₆₄ s0.readReg64 .x21) ∗ ((s0.sp - 24#64) ↦₆₄ v_x21) ∗
         ((s0.sp - 16#64) ↦₆₄ s0.readReg64 .x20) ∗ ((s0.sp - 8#64) ↦₆₄ s0.readReg64 .x19)))
      (Q := fun sm => Saved48Preserved s0 sm (s0.sp - 48#64) ∧ sm.readReg64 .x22 = s0.readReg64 .x22 ∧ sm.readReg64 .x19 = a) ?_ ?_
    · have hjoin128 : memRegion a 48 ∗ memRegion (a + 48#64) 80 ⊢ memRegion a 128 := by
        rw [ProofLib.memRegion_split a 48 80 (by decide)]; exact Entails.refl _
      cases hch : st.chain with
      | none =>
        have h56 : (a + 48#64) + 8#64 = a + 56#64 := BitVec.add_assoc a 48#64 8#64
        dsimp only [optChainPBAt]; rw [h56]; wp_steps
        have hnone80 : ((a + 48#64) ↦₆₄ noneCap) ∗ memRegion (a + 56#64) 72 ⊢ memRegion (a + 48#64) 80 := by
          rw [← h56]; exact optChainPBAt_none_entails_memRegion_80 (a + 48#64)
        refine SepWP.focus_weaken hnone80 (by sep_focus) ?_
        refine SepWP.focus_weaken hjoin128 (by sep_focus) ?_
        refine align_pre (by ac_rfl) ?_; wp_done
      | some ch =>
        dsimp only [optChainPBAt]
        refine SepWP.focus_weaken (chainPBAt_entails_dealloc A (a + 48#64) ch) (by sep_focus) ?_
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
        refine seq_clean (mid := (blkPl_270).base + 92#64)
          (P_mid := (memRegion a 48 ∗
            ((a + 48#64) ↦₆₄ g.links.cap) ∗ ((a + 56#64) ↦₆₄ g.links.ptr) ∗
            ((a + 64#64) ↦₆₄ BitVec.ofNat 64 ch.links.length) ∗
            ((a + 72#64) ↦₆₄ g.nextRoot.cap) ∗ ((a + 80#64) ↦₆₄ g.nextRoot.ptr) ∗
            memRegion (a + 88#64) 40 ∗ vecCapPtrDealloc A g.nextRoot.cap g.nextRoot.ptr ∗
            optProtoPqRatchetInnerAt A (a + 128#64) st.inner) ∗ optProtoInnerStateJumpTablePlacedAt ∗
            A.pool ∗ (memRegion (s0.sp - 4192#64) 48 ∗ stackAt (s0.sp - 48#64) allocHookStack) ∗
            (((s0.sp - 48#64) ↦₆₄ s0.readReg64 .fp) ∗ ((s0.sp - 40#64) ↦₆₄ s0.readReg64 .lr) ∗
             ((s0.sp - 32#64) ↦₆₄ s0.readReg64 .x21) ∗ ((s0.sp - 24#64) ↦₆₄ v_x21) ∗
             ((s0.sp - 16#64) ↦₆₄ s0.readReg64 .x20) ∗ ((s0.sp - 8#64) ↦₆₄ s0.readReg64 .x19)))
          (Q := fun sm => Saved48Preserved s0 sm (s0.sp - 48#64) ∧ sm.readReg64 .x22 = s0.readReg64 .x22 ∧ sm.readReg64 .x19 = a) ?_ ?_
        · by_cases hc : g.links.cap = 0
          · have hnil : ch.links = [] := by rw [hc] at hlen_le; simp at hlen_le; exact hlen_le
            have hc_beq : (g.links.cap == 0#64) = true := by rw [beq_iff_eq]; exact hc
            have h0 : arrayAt (fun ep addr => chainEpochPBAt A addr ep) 112 g.links.ptr [] = emp := rfl
            simp only [hc, hnil, List.length_nil, Nat.zero_mul, BitVec.ofNat_eq_ofNat, ↓reduceIte, emp_sepConj, sepConj_emp]
            apply sepWP_seq_lscl hcl1 (mid := lsmpl.base 288); wp_steps
            apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs); intro hcl_call
            have hslice_raw := drop_proto_epoch_slice_mem_on
              (callerProg := lsProg_270 (Rust.withPanics ext)) hdealloc hcl_call
            dsimp only [lsProg_270, withMemEq, dropProtoEpochSliceSpec, chainEpochPBSize, BitVec.ofNat_eq_ofNat] at hslice_raw
            rw [← sepConj_emp ((a + 48#64) ↦₆₄ 0#64), ← h0]
            refine SepWP.focus_weaken (Entails.of_eq (stackAt_sub48_split_32 s0.sp)) (by sep_focus) ?_
            wp_call hslice_raw ⟨g.links.ptr, []⟩
            have hsp_eq : stackAt s1.sp dropStack32 = stackAt (s0.sp - 48#64) dropStack32 := by rw [hsp_1]
            refine SepWP.focus_weaken (Entails.of_eq hsp_eq) (by sep_focus) ?_
            refine SepWP.focus_weaken (Entails.of_eq (stackAt_sub48_split_32 s0.sp).symm) (by sep_focus) ?_
            wp_steps; refine align_pre (by simp only [memRegion_zero, emp_sepConj, sepConj_emp, *]; ac_rfl) ?_; wp_done
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
            simp only [hc, ↓reduceIte]
            apply sepWP_seq_lscl hcl1 (mid := lsmpl.base 288); wp_steps
            apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs); intro hcl_call
            have hslice_raw := drop_proto_epoch_slice_mem_on
              (callerProg := lsProg_270 (Rust.withPanics ext)) hdealloc hcl_call
            dsimp only [lsProg_270, withMemEq, dropProtoEpochSliceSpec, chainEpochPBSize, BitVec.ofNat_eq_ofNat] at hslice_raw
            refine SepWP.focus_weaken (Entails.of_eq (stackAt_sub48_split_32 s0.sp)) (by sep_focus) ?_
            wp_call hslice_raw ⟨g.links.ptr, ch.links⟩
            have hsp_eq : stackAt s1.sp dropStack32 = stackAt (s0.sp - 48#64) dropStack32 := by rw [hsp_1]
            refine SepWP.focus_weaken (Entails.of_eq hsp_eq) (by sep_focus) ?_
            refine SepWP.focus_weaken (Entails.of_eq (stackAt_sub48_split_32 s0.sp).symm) (by sep_focus) ?_
            refine SepWP.focus_weaken hrejoin (by sep_focus) ?_
            wp_steps; wp_apply
            refine align_pre (by simp only [hsp_1, Reg.fp, Reg.lr, Reg.x19, Reg.x20, Reg.x21, *]; ac_rfl) ?_; wp_done
        · intro s2 hpc2 hrun2 ⟨⟨hx23_2, hx24_2, hx25_2, hx26_2, hx27_2, hx28_2, hsp_2, htrace_2, hvregs_2⟩, hx22_2, hx19_2⟩
          have hhdr80 : ((a + 48#64) ↦₆₄ g.links.cap) ∗ ((a + 56#64) ↦₆₄ g.links.ptr) ∗
              ((a + 64#64) ↦₆₄ BitVec.ofNat 64 ch.links.length) ∗
              ((a + 72#64) ↦₆₄ g.nextRoot.cap) ∗ ((a + 80#64) ↦₆₄ g.nextRoot.ptr) ∗
              memRegion (a + 88#64) 40 ⊢ memRegion (a + 48#64) 80 := by
            rw [← h56, ← h64, ← h72, ← h80, ← h88]
            exact chainPBHeaders_entails_memRegion_80 (a + 48#64) g.links.cap g.links.ptr
              (BitVec.ofNat 64 ch.links.length) g.nextRoot.cap g.nextRoot.ptr
          dsimp only [vecCapPtrDealloc]
          by_cases hnr : (g.nextRoot.cap == 0#64) = true <;>
            simp only [hnr, Bool.false_eq_true, ↓reduceIte, emp_sepConj, sepConj_emp]
          · wp_steps; refine SepWP.focus_weaken hhdr80 (by sep_focus) ?_
            refine SepWP.focus_weaken hjoin128 (by sep_focus) ?_; refine align_pre (by ac_rfl) ?_; wp_done
          · wp_steps; wp_apply; refine SepWP.focus_weaken hhdr80 (by sep_focus) ?_
            refine SepWP.focus_weaken hjoin128 (by sep_focus) ?_; refine align_pre (by rw [hsp_2]; ac_rfl) ?_; wp_done
    · intro s3 hpc3 hrun3 hcl3 ⟨⟨hx23_3, hx24_3, hx25_3, hx26_3, hx27_3, hx28_3, hsp_3, htrace_3, hvregs_3⟩, hx22_3, hx19_3⟩
      have hjoin352 : memRegion a 128 ∗ memRegion (a + 128#64) 224 ⊢ memRegion a 352 := by
        rw [ProofLib.memRegion_split a 128 224 (by decide)]; exact Entails.refl _
      cases hinner : st.inner with
      | none =>
        have h136 : (a + 128#64) + 8#64 = a + 136#64 := BitVec.add_assoc a 128#64 8#64
        dsimp only [optProtoPqRatchetInnerAt, none3Cap']; rw [h136]; wp_steps
        have hnone224 : ((a + 128#64) ↦₆₄ 0xfffffffffffffffd#64) ∗ memRegion (a + 136#64) 216 ⊢
            memRegion (a + 128#64) 224 := by
          rw [← h136]; exact optProtoPqRatchetInnerAt_none_entails_memRegion_224 (a + 128#64)
        refine SepWP.focus_weaken hnone224 (by sep_focus) ?_; refine SepWP.focus_weaken hjoin352 (by sep_focus) ?_
        refine SepWP.focus_weaken (stack_restore_96_allocHook s0.sp (s0.readReg64 .fp) (s0.readReg64 .lr)
          (s0.readReg64 .x21) v_x21 (s0.readReg64 .x20) (s0.readReg64 .x19)) (by sep_focus) ?_; wp_done
      | some innerVal =>
        cases innerVal with
        | v1 v1 =>
          dsimp only [optProtoPqRatchetInnerAt]
          refine SepWP.focus_weaken (optProtoInnerStateAt_expose_word A (a + 128#64) v1.innerState) (by sep_focus) ?_
          wp_pull_exists; rename_i w; wp_focus_pure; intro hne3
          apply sepWP_seq_lscl hcl3 (mid := lsmpl.base 267); wp_steps
          apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs); intro hcl_call
          have hinner_raw := drop_opt_proto_inner_state_mem_on
            (callerProg := lsProg_270 (Rust.withPanics ext)) hdealloc hcl_call
          dsimp only [lsProg_270, withMemEq, dropOptProtoInnerStatePlacedSpec, optProtoInnerStateSize, BitVec.ofNat_eq_ofNat] at hinner_raw
          refine SepWP.focus_weaken (optProtoInnerStateAt_unexpose_word A (a + 128#64) w v1.innerState) (by sep_focus) ?_
          refine SepWP.focus_weaken (stack_restore_96_allocHook s0.sp (s0.readReg64 .fp) (s0.readReg64 .lr)
            (s0.readReg64 .x21) v_x21 (s0.readReg64 .x20) (s0.readReg64 .x19)) (by sep_focus) ?_
          wp_call hinner_raw ⟨a + 128#64, v1.innerState⟩
          refine SepWP.focus_weaken hjoin352 (by sep_focus) ?_; wp_done

theorem drop_proto_pq_ratchet_state_cl_blockProgram [LibsignalPlacement] {A : RustAlloc}
    {ext : String → Option (State → State)}
    (hdealloc : HookSat (Rust.withPanics ext) spqrRustDeallocSym (rustDeallocSpec A)) :
    subroutine_ok (libsignalSessionLib.blockProgram lsmpl 270 (Rust.withPanics ext)) (lsmpl.base 270)
      (withLsCodeLoaded lsmpl (dropProtoPqRatchetStatePlacedSpec A)) :=
  ls_to_blockProgram (drop_proto_pq_ratchet_state_cl_placed_ok hdealloc)

end LibsignalBinary.Proofs.SpqrV1.Drop.ProtoTopClPlaced
