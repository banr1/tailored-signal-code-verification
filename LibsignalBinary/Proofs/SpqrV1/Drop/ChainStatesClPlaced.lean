/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SpqrV1.Drop.ProtoChain
public import LibsignalBinary.Proofs.SpqrV1.Drop.ChainEpochPlaced
public import LibsignalBinary.Proofs.SpqrV1.Drop.States2
public import LibsignalBinary.Proofs.SpqrV1.Drop.ProtoChunkedClPlaced
public import LibsignalBinary.Proofs.SpqrV1.States.Recv.DropChunkedClPlaced
import LibsignalBinary.Proofs.Placed.GenLsBlock
import LibsignalBinary.Proofs.SpqrV1.Alloc.SpqrAllocCodeSym
import ProofLib.SepLogic.WP.Apply
import ProofLib.SepLogic.WPp
import GeneratedLean.LibsignalSessionObj

/-!
# Code-Loaded `[LibsignalPlacement]` Drop Glue for Chains and `States`

Proves `withLsCodeLoaded lsmpl` subroutine contracts from `rustDeallocSpec A` for:
- Block `279`: `core::ptr::drop_glue::<spqr::v1::unchunked::send_ct::Ct1Sent> [local#2]`
- Block `287`: `core::ptr::drop_glue::<[spqr::chain::ChainEpoch]> [local#2]`
- Block `266`: `core::ptr::drop_glue::<core::option::Option<spqr::proto::pq_ratchet::Chain>>`
- Block `269`: `core::ptr::drop_glue::<spqr::chain::Chain>`
- Block `273`: `core::ptr::drop_glue::<spqr::v1::chunked::states::States> [local#2]`
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 400000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false

namespace LibsignalBinary.Proofs.SpqrV1.Drop.ChainStatesClPlaced

open Arm64 Arm64.Obj ProofLib ProofLib.ProgramReflection
open CryptoGames.LibsignalSession (ShaCompress)
open CryptoVerification
open CryptoVerification.SpqrV1.ChainProofs
open CryptoVerification.SpqrV1.Drop.ChainEpochPlaced
open CryptoVerification.SpqrV1.Drop.Blk337_338
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
  (spqrRustDeallocSym
   drop_glue_sorted_set_pt16_mem_on
   drop_glue_poly16_mem_on
   drop_chunked_ek_received_ct1_sampled_mem_on
   drop_chunked_header_sent_mem_on
   drop_chunked_ct1_received_mem_on
   drop_chunked_ek_sent_ct1_received_mem_on)
open LibsignalBinary.Proofs.SpqrV1.Drop.ProtoChunkedClPlaced
  (subroutine_ok_withLsCodeLoaded_intro seq_clean_lscl ls_to_blockProgram
   drop_proto_epoch_slice_mem_on)

attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero

/-! ## Leaf Single-Block Wrappers (`279`, `287`) -/

theorem drop_unchunked_ct1_sent_local2_cl_placed_ok [LibsignalPlacement]
    {A : RustAlloc} {F : ShaCompress} {ext : String → Option (State → State)}
    (hdealloc : HookSat (Rust.withPanics ext) spqrRustDeallocSym (rustDeallocSpec A)) :
    subroutine_ok (lsProg_279 (Rust.withPanics ext)) (lsmpl.base 279)
      (withLsCodeLoaded lsmpl (dropUnchunkedCt1SentSpec A F)) := by
  rw [← ls_blockPlacement_base (i := 279)]
  exact subroutine_ok_withLsCodeLoaded_of_plain
    (drop_unchunked_ct1_sent_local2_placed_ok (spqr_hook_ok_of_mem hdealloc))

theorem drop_unchunked_ct1_sent_local2_cl_blockProgram [LibsignalPlacement]
    {A : RustAlloc} {F : ShaCompress} {ext : String → Option (State → State)}
    (hdealloc : HookSat (Rust.withPanics ext) spqrRustDeallocSym (rustDeallocSpec A)) :
    subroutine_ok (libsignalSessionLib.blockProgram lsmpl 279 (Rust.withPanics ext)) (lsmpl.base 279)
      (withLsCodeLoaded lsmpl (dropUnchunkedCt1SentSpec A F)) :=
  ls_to_blockProgram (drop_unchunked_ct1_sent_local2_cl_placed_ok hdealloc)

theorem drop_unchunked_ct1_sent_local2_mem_on [LibsignalPlacement]
    {A : RustAlloc} {F : ShaCompress} {callerProg : Program} {idx : Nat}
    {ext : String → Option (State → State)}
    [IsLsBlockProg callerProg idx (Rust.withPanics ext)] {m : Memory}
    (hdealloc : HookSat (Rust.withPanics ext) spqrRustDeallocSym (rustDeallocSpec A))
    (hcl : LibsignalCodeLoaded lsmpl m) (hidx : idx < 619 := by decide) :
    subroutine_ok callerProg (lsmpl.base 279)
      (withMemEq m (dropUnchunkedCt1SentSpec A F)) :=
  lscall_blk_cl (drop_unchunked_ct1_sent_local2_cl_placed_ok hdealloc) hcl hidx

theorem drop_chain_epoch_slice_local2_cl_placed_ok [LibsignalPlacement]
    {A : RustAlloc} {ext : String → Option (State → State)}
    (hdealloc : HookSat (Rust.withPanics ext) spqrRustDeallocSym (rustDeallocSpec A)) :
    subroutine_ok (lsProg_287 (Rust.withPanics ext)) (lsmpl.base 287)
      (withLsCodeLoaded lsmpl (dropChainEpochSliceSpec A)) := by
  rw [← ls_blockPlacement_base (i := 287)]
  exact subroutine_ok_withLsCodeLoaded_of_plain
    (drop_chain_epoch_slice_local2_placed_ok_ext (spqr_hook_ok_of_mem hdealloc))

theorem drop_chain_epoch_slice_local2_cl_blockProgram [LibsignalPlacement]
    {A : RustAlloc} {ext : String → Option (State → State)}
    (hdealloc : HookSat (Rust.withPanics ext) spqrRustDeallocSym (rustDeallocSpec A)) :
    subroutine_ok (libsignalSessionLib.blockProgram lsmpl 287 (Rust.withPanics ext)) (lsmpl.base 287)
      (withLsCodeLoaded lsmpl (dropChainEpochSliceSpec A)) :=
  ls_to_blockProgram (drop_chain_epoch_slice_local2_cl_placed_ok hdealloc)

theorem drop_chain_epoch_slice_local2_mem_on [LibsignalPlacement]
    {A : RustAlloc} {callerProg : Program} {idx : Nat}
    {ext : String → Option (State → State)}
    [IsLsBlockProg callerProg idx (Rust.withPanics ext)] {m : Memory}
    (hdealloc : HookSat (Rust.withPanics ext) spqrRustDeallocSym (rustDeallocSpec A))
    (hcl : LibsignalCodeLoaded lsmpl m) (hidx : idx < 619 := by decide) :
    subroutine_ok callerProg (lsmpl.base 287)
      (withMemEq m (dropChainEpochSliceSpec A)) :=
  lscall_blk_cl (drop_chain_epoch_slice_local2_cl_placed_ok hdealloc) hcl hidx

/-! ## Block `266`: `drop_glue::<Option<spqr::proto::pq_ratchet::Chain>>` -/

theorem drop_opt_proto_spqr_chain_cl_placed_ok [LibsignalPlacement] {A : RustAlloc}
    {ext : String → Option (State → State)}
    (hdealloc : HookSat (Rust.withPanics ext) spqrRustDeallocSym (rustDeallocSpec A)) :
    subroutine_ok (lsProg_266 (Rust.withPanics ext)) (lsmpl.base 266)
      (withLsCodeLoaded lsmpl (dropOptProtoSpqrChainSpec A)) := by
  rw [← ls_blockPlacement_base (i := 266)]
  change subroutine_ok ((blkPC_266).rebase (blkPl_266).base (Rust.withPanics ext)) (blkPl_266).base _
  apply subroutine_ok_withLsCodeLoaded_intro; intro m hcl
  have hdealloc_raw : subroutine_ok ((blkPC_266).rebase (blkPl_266).base (Rust.withPanics ext))
      (lsρ spqrRustDeallocSym) (rustDeallocSpec A) := spqr_hook_ok_of_mem hdealloc
  simp only [rustDeallocSpec] at hdealloc_raw
  dsimp only [withMemEq, dropOptProtoSpqrChainSpec, chainPBSize, chainEpochPBSize,
    BitVec.ofNat_eq_ofNat] at hdealloc_raw ⊢
  wp_init x s0; rcases x with ⟨a, optCh⟩
  have hm : s0.mem = m := (by assumption); subst hm
  dsimp only [DropOptProtoSpqrChainGhost.a, DropOptProtoSpqrChainGhost.optCh] at *
  nth_rw 1 [stackAt_dropStack80_split s0.sp]; cells_unfold; wp_pull_exists
  rename_i v_fp v_lr v_x22 v_x21 v_x20 v_x19
  have hfsp_align : ((s0.sp - 48#64) &&& 15#64 == 0#64) = true :=
    spAligned_sub s0.sp 48#64 (by assumption) (by decide)
  cases optCh with
  | none =>
    dsimp only [optChainPBAt]; wp_steps
    refine SepWP.focus_weaken (optChainPBAt_none_entails_memRegion_80 a) (by sep_focus) ?_
    refine SepWP.focus_weaken
      (stack_restore_48_dropStack80 s0.sp (s0.readReg64 .fp) (s0.readReg64 .lr)
        (s0.readReg64 .x21) v_x21 (s0.readReg64 .x20) (s0.readReg64 .x19)) (by sep_focus) ?_
    wp_done
  | some ch =>
    dsimp only [optChainPBAt]
    refine SepWP.weaken_pre (sepConj_mono_left (chainPBAt_entails_dealloc A a ch)) ?_
    wp_pull_exists; rename_i g; wp_focus_pure; rintro ⟨hlen_le, hcap_lt, hptr_ne⟩
    have hcap_lt_pow : g.links.cap.toNat < 2 ^ 63 := by omega
    have hlen_lt : ch.links.length * 112 < 2 ^ 63 := by
      have : ch.links.length * 112 ≤ g.links.cap.toNat * 112 := Nat.mul_le_mul_right 112 hlen_le; omega
    have hne_none := cap_add_one_beq_zero_false hcap_lt_pow
    refine seq_clean (mid := (blkPl_266).base + 68#64)
      (P_mid := (a ↦₆₄ g.links.cap) ∗ ((a + 8#64) ↦₆₄ g.links.ptr) ∗
        ((a + 16#64) ↦₆₄ BitVec.ofNat 64 ch.links.length) ∗
        ((a + 24#64) ↦₆₄ g.nextRoot.cap) ∗ ((a + 32#64) ↦₆₄ g.nextRoot.ptr) ∗
        memRegion (a + 40#64) 40 ∗ vecCapPtrDealloc A g.nextRoot.cap g.nextRoot.ptr ∗
        A.pool ∗ stackAt (s0.sp - 48#64) dropStack32 ∗
        (((s0.sp - 48#64) ↦₆₄ s0.readReg64 .fp) ∗ ((s0.sp - 40#64) ↦₆₄ s0.readReg64 .lr) ∗
         ((s0.sp - 32#64) ↦₆₄ s0.readReg64 .x21) ∗ ((s0.sp - 24#64) ↦₆₄ v_x21) ∗
         ((s0.sp - 16#64) ↦₆₄ s0.readReg64 .x20) ∗ ((s0.sp - 8#64) ↦₆₄ s0.readReg64 .x19)))
      (Q := fun sm => Saved48Preserved s0 sm (s0.sp - 48#64) ∧
        sm.readReg64 .x19 = a ∧ sm.readReg64 .x22 = s0.readReg64 .x22) ?_ ?_
    · by_cases hc : g.links.cap = 0
      · have hnil : ch.links = [] := by rw [hc] at hlen_le; simp at hlen_le; exact hlen_le
        have hc_beq : (g.links.cap == 0#64) = true := by rw [beq_iff_eq]; exact hc
        have h0 : arrayAt (fun ep addr => chainEpochPBAt A addr ep) 112 g.links.ptr [] = emp := rfl
        simp only [hc, hnil, List.length_nil, Nat.zero_mul, BitVec.ofNat_eq_ofNat, ↓reduceIte,
          emp_sepConj, sepConj_emp]
        apply sepWP_seq_lscl hcl (mid := lsmpl.base 288); wp_steps
        apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs); intro hcl_call
        have hslice_raw := drop_proto_epoch_slice_mem_on
          (callerProg := lsProg_266 (Rust.withPanics ext)) hdealloc hcl_call
        dsimp only [lsProg_266, withMemEq, dropProtoEpochSliceSpec, chainEpochPBSize, BitVec.ofNat_eq_ofNat] at hslice_raw
        rw [← sepConj_emp (a ↦₆₄ 0#64), ← h0]
        wp_call hslice_raw ⟨g.links.ptr, []⟩
        wp_steps
        refine align_pre (by simp only [memRegion_zero, emp_sepConj, sepConj_emp, *]; ac_rfl) ?_
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
        apply sepWP_seq_lscl hcl (mid := lsmpl.base 288); wp_steps
        apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs); intro hcl_call
        have hslice_raw := drop_proto_epoch_slice_mem_on
          (callerProg := lsProg_266 (Rust.withPanics ext)) hdealloc hcl_call
        dsimp only [lsProg_266, withMemEq, dropProtoEpochSliceSpec, chainEpochPBSize, BitVec.ofNat_eq_ofNat] at hslice_raw
        wp_call hslice_raw ⟨g.links.ptr, ch.links⟩
        refine SepWP.focus_weaken hrejoin (by sep_focus) ?_
        conv => arg 4; rw [stackAt_dropStack32_split_bottom (s0.sp - 48#64)]
        wp_steps
        wp_call hdealloc_raw (g.links.ptr, g.links.cap.toNat * 112, 8)
        refine align_pre (by
          simp only [hsp_sub, stackAt_dropStack32_split_bottom (s0.sp - 48#64), *]
          ac_rfl) ?_
        wp_done
    · intro s1 hpc1 hrun1 ⟨⟨hx23_1, hx24_1, hx25_1, hx26_1, hx27_1, hx28_1, hsp_1, htrace_1, hvregs_1⟩, hx19_1, hx22_1⟩
      dsimp only [vecCapPtrDealloc]
      by_cases hnr : (g.nextRoot.cap == 0#64) = true <;> simp only [hnr, ↓reduceIte, emp_sepConj, sepConj_emp]
      · wp_steps
        refine SepWP.focus_weaken
          (chainPBHeaders_entails_memRegion_80 a g.links.cap g.links.ptr
            (BitVec.ofNat 64 ch.links.length) g.nextRoot.cap g.nextRoot.ptr) (by sep_focus) ?_
        refine SepWP.focus_weaken
          (stack_restore_48_dropStack80 s0.sp (s0.readReg64 .fp) (s0.readReg64 .lr)
            (s0.readReg64 .x21) v_x21 (s0.readReg64 .x20) (s0.readReg64 .x19)) (by sep_focus) ?_
        wp_done
      · wp_steps
        refine SepWP.focus_weaken
          (chainPBHeaders_entails_memRegion_80 a g.links.cap g.links.ptr
            (BitVec.ofNat 64 ch.links.length) g.nextRoot.cap g.nextRoot.ptr) (by sep_focus) ?_
        refine SepWP.focus_weaken
          (stack_restore_48_dropStack80 s0.sp (s0.readReg64 .fp) (s0.readReg64 .lr)
            (s0.readReg64 .x21) v_x21 (s0.readReg64 .x20) (s0.readReg64 .x19)) (by sep_focus) ?_
        rw [stackAt_dropStack80_split_bottom s0.sp]
        wp_call hdealloc_raw (g.nextRoot.ptr, g.nextRoot.cap.toNat, 1)
        rw [← stackAt_dropStack80_split_bottom s0.sp]; wp_done

theorem drop_opt_proto_spqr_chain_cl_blockProgram [LibsignalPlacement] {A : RustAlloc}
    {ext : String → Option (State → State)}
    (hdealloc : HookSat (Rust.withPanics ext) spqrRustDeallocSym (rustDeallocSpec A)) :
    subroutine_ok (libsignalSessionLib.blockProgram lsmpl 266 (Rust.withPanics ext)) (lsmpl.base 266)
      (withLsCodeLoaded lsmpl (dropOptProtoSpqrChainSpec A)) :=
  ls_to_blockProgram (drop_opt_proto_spqr_chain_cl_placed_ok hdealloc)

/-! ## Block `269`: `drop_glue::<spqr::chain::Chain>` -/

theorem drop_spqr_chain_cl_placed_ok [LibsignalPlacement] {A : RustAlloc}
    {ext : String → Option (State → State)}
    (hdealloc : HookSat (Rust.withPanics ext) spqrRustDeallocSym (rustDeallocSpec A)) :
    subroutine_ok (lsProg_269 (Rust.withPanics ext)) (lsmpl.base 269)
      (withLsCodeLoaded lsmpl (dropSpqrChainSpec A)) := by
  rw [← ls_blockPlacement_base (i := 269)]
  change subroutine_ok ((blkPC_269).rebase (blkPl_269).base (Rust.withPanics ext)) (blkPl_269).base _
  apply subroutine_ok_withLsCodeLoaded_intro; intro m hcl
  have hslice_cl := ls_subroutine_ok_cl_of_block
    (callerProg := lsProg_269 (Rust.withPanics ext))
    (drop_chain_epoch_slice_local2_cl_placed_ok hdealloc)
  dsimp only [lsProg_269, withLsCl, dropChainEpochSliceSpec, BitVec.ofNat_eq_ofNat] at hslice_cl
  have hdealloc_raw : subroutine_ok ((blkPC_269).rebase (blkPl_269).base (Rust.withPanics ext))
      (lsρ spqrRustDeallocSym) (rustDeallocSpec A) := spqr_hook_ok_of_mem hdealloc
  simp only [rustDeallocSpec] at hdealloc_raw
  dsimp only [withMemEq, dropSpqrChainSpec, chainSize, dropSpqrChainStack,
    BitVec.ofNat_eq_ofNat] at hdealloc_raw ⊢
  wp_init x s0; rcases x with ⟨a, G, c⟩
  have hm : s0.mem = m := (by assumption); subst hm
  dsimp only [DropSpqrChainGhost.a, DropSpqrChainGhost.G, DropSpqrChainGhost.c] at *
  refine SepWP.weaken_pre (sepConj_mono_left (chainAt_entails_dealloc A a G c)) ?_
  unfold vecDequeAt vecDequeRingBuf vecDequeHeader
  nth_rw 1 [stackAt_dropStack80_split s0.sp]; cells_unfold; wp_pull_exists; wp_focus_pure
  rintro ⟨hlen_le, hcap_lt, hptr_ne, hhead⟩
  dsimp only [chainEpochSize, chainEpochAlign] at hcap_lt ⊢
  refine seq_clean (mid := (blkPl_269).base + 120#64)
    (P_mid :=
      vecDequeHeader a G.linksCap G.linksPtr G.linksHead
        (BitVec.ofNat 64 (G.epochs.zip c.links).length) ∗
      (if G.linksCap = 0 then emp
       else A.live G.linksPtr (G.linksCap.toNat * 112) 8 ∗
         memRegion G.linksPtr (G.linksCap.toNat * 112)) ∗
      ((a + 32#64) ↦₆₄ G.nextRoot.cap) ∗ ((a + 40#64) ↦₆₄ G.nextRoot.ptr) ∗
      memRegion (a + 48#64) 40 ∗
      vecCapPtrDealloc A G.nextRoot.cap G.nextRoot.ptr ∗
      A.pool ∗
      stackAt (s0.sp - 48#64) dropStack32 ∗
      (((s0.sp - 48#64) ↦₆₄ s0.readReg64 .fp) ∗ ((s0.sp - 40#64) ↦₆₄ s0.readReg64 .lr) ∗
       ((s0.sp - 32#64) ↦₆₄ s0.readReg64 .x22) ∗ ((s0.sp - 24#64) ↦₆₄ s0.readReg64 .x21) ∗
       ((s0.sp - 16#64) ↦₆₄ s0.readReg64 .x20) ∗ ((s0.sp - 8#64) ↦₆₄ s0.readReg64 .x19)))
    (Q := fun sm => Saved48Preserved s0 sm (s0.sp - 48#64) ∧
      sm.readReg64 .x19 = a ∧ sm.readReg64 .x21 = G.linksPtr ∧ sm.readReg64 .x22 = G.linksCap)
    ?_ ?_
  · generalize hxs : G.epochs.zip c.links = xs at hlen_le ⊢
    cases xs with
    | nil =>
      have h0 : arrayAt (chainEpoch A) 112 G.linksPtr [] = emp := rfl
      have hnil_ent :
          (if G.linksCap = 0 then emp
           else A.live G.linksPtr (G.linksCap.toNat * 112) 8 ∗
             vecDequeSlotsAt (chainEpochAt A) 112 G.linksCap.toNat G.linksHead.toNat G.linksPtr [] 0 G.linksCap.toNat) ⊢
          (if G.linksCap = 0 then emp
           else A.live G.linksPtr (G.linksCap.toNat * 112) 8 ∗
             memRegion G.linksPtr (G.linksCap.toNat * 112)) := by
        by_cases hc : G.linksCap = 0
        · simp [hc]; exact Entails.refl _
        · simp only [hc, ↓reduceIte]
          exact sepConj_mono_right (vecDequeSlotsAt_nil_entails_memRegion
            (chainEpochAt A) 112 G.linksCap.toNat G.linksHead.toNat G.linksPtr hcap_lt)
      refine SepWP.focus_weaken hnil_ent (by sep_focus) ?_
      simp only [List.length_nil, Nat.zero_mul, BitVec.ofNat_eq_ofNat]
      wp_steps_lscl (lsmpl.base 287)
      rw [← sepConj_emp (a ↦₆₄ G.linksCap), ← h0]
      wp_call hslice_cl ⟨G.linksPtr, []⟩
      wp_steps_lscl (lsmpl.base 287)
      rw [← sepConj_emp (a ↦₆₄ G.linksCap), ← h0]
      wp_call hslice_cl ⟨G.linksPtr, []⟩
      refine align_pre (by
        unfold vecDequeHeader
        simp only [List.length_nil, BitVec.ofNat_eq_ofNat, memRegion_zero, emp_sepConj, sepConj_emp,
          Nat.mul_comm, h0, *]
        ac_rfl) ?_
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
          (chainEpochAt A) 112 G.linksCap.toNat G.linksHead.toNat G.linksPtr (x :: tl) hcap_lt hhead hwrap
        let eps := ys.map Prod.snd
        have heps_len : eps.length = (x :: tl).length := by simp [eps, hys_len]
        have heps_lt : eps.length * 112 < 2 ^ 63 := by rw [heps_len]; exact hlen_lt
        have hx1_eq : G.linksHead + BitVec.ofNat 64 (x :: tl).length - G.linksHead =
            BitVec.ofNat 64 eps.length := by
          rw [SpqrV1.Drop.add_sub_cancel_left_bv, heps_len]
        have h0 : arrayAt (chainEpoch A) 112 G.linksPtr [] = emp := rfl
        have hent_ep :
            vecDequeSlotsAt (chainEpochAt A) 112 G.linksCap.toNat G.linksHead.toNat G.linksPtr (x :: tl) 0 G.linksCap.toNat ⊢
            arrayAt (chainEpoch A) 112 (G.linksPtr + G.linksHead * 112#64) eps ∗
            memRegion G.linksPtr (G.linksHead.toNat * 112) ∗
            memRegion (G.linksPtr + BitVec.ofNat 64 ((G.linksHead.toNat + (x :: tl).length) * 112))
              ((G.linksCap.toNat - G.linksHead.toNat - (x :: tl).length) * 112) := by
          rw [← haddr1]
          exact Entails.trans hys_ent (sepConj_mono_left (arrayAt_chainEpochAt_entails_chainEpoch A _ ys))
        refine SepWP.focus_weaken hent_ep (by sep_focus) ?_
        wp_steps_lscl (lsmpl.base 287)
        wp_call hslice_cl ⟨G.linksPtr + G.linksHead * 112#64, eps⟩
        wp_steps_lscl (lsmpl.base 287)
        rw [← sepConj_emp (a ↦₆₄ G.linksCap), ← h0]
        wp_call hslice_cl ⟨G.linksPtr, []⟩
        rw [← haddr1, heps_len]
        refine SepWP.focus_weaken
          (vecDequeSlotsAt_nonwrap_rejoin 112 G.linksCap.toNat G.linksHead.toNat (x :: tl).length
            G.linksPtr hcap_lt hhead hwrap) (by sep_focus) ?_
        refine align_pre (by
          unfold vecDequeHeader
          simp only [chainEpochSize, chainEpochAlign, Nat.mul_comm, memRegion_zero, emp_sepConj, sepConj_emp, *]
          ac_rfl) ?_
        wp_done
      · have hgt : G.linksCap.toNat - G.linksHead.toNat < (x :: tl).length := by omega
        have hnule := not_ule_sub_of_gt hcap_lt_pow hhead hlen_le hgt
        obtain ⟨ys₁, ys₂, hys₁_len, hys₂_len, hys_ent⟩ := vecDequeSlotsAt_wrap_entails
          (chainEpochAt A) 112 G.linksCap.toNat G.linksHead.toNat G.linksPtr (x :: tl) hcap_lt hhead hlen_le hgt
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
            vecDequeSlotsAt (chainEpochAt A) 112 G.linksCap.toNat G.linksHead.toNat G.linksPtr (x :: tl) 0 G.linksCap.toNat ⊢
            arrayAt (chainEpoch A) 112 (G.linksPtr + G.linksHead * 112#64) eps₁ ∗
            arrayAt (chainEpoch A) 112 G.linksPtr eps₂ ∗
            memRegion (G.linksPtr + BitVec.ofNat 64 (((x :: tl).length - (G.linksCap.toNat - G.linksHead.toNat)) * 112))
              ((G.linksHead.toNat - ((x :: tl).length - (G.linksCap.toNat - G.linksHead.toNat))) * 112) := by
          rw [← haddr1]
          exact Entails.trans hys_ent
            (sepConj_mono (arrayAt_chainEpochAt_entails_chainEpoch A _ ys₁)
              (sepConj_mono_left (arrayAt_chainEpochAt_entails_chainEpoch A _ ys₂)))
        refine SepWP.focus_weaken hent_ep (by sep_focus) ?_
        wp_steps_lscl (lsmpl.base 287)
        have hx1_1 : G.linksCap - G.linksHead = BitVec.ofNat 64 eps₁.length := by
          rw [heps₁_len, sub_eq_ofNat_sub (by omega)]
        wp_call hslice_cl ⟨G.linksPtr + G.linksHead * 112#64, eps₁⟩
        wp_steps_lscl (lsmpl.base 287)
        have hx1_2 : BitVec.ofNat 64 (x :: tl).length - (G.linksCap - G.linksHead) =
            BitVec.ofNat 64 eps₂.length := by
          rw [heps₂_len, ofNat_sub_sub_eq hcap_lt_pow hhead (by omega) hlen_le]
        wp_call hslice_cl ⟨G.linksPtr, eps₂⟩
        rw [← haddr1, heps₁_len, heps₂_len]
        refine SepWP.focus_weaken
          (vecDequeSlotsAt_wrap_rejoin 112 G.linksCap.toNat G.linksHead.toNat (x :: tl).length
            G.linksPtr hcap_lt hhead hlen_le hgt) (by sep_focus) ?_
        refine align_pre (by
          unfold vecDequeHeader
          simp only [chainEpochSize, chainEpochAlign, Nat.mul_comm, *]
          ac_rfl) ?_
        wp_done
  · intro s1 hpc1 hrun1 ⟨⟨hx23_1, hx24_1, hx25_1, hx26_1, hx27_1, hx28_1, hsp_1, htrace_1, hvregs_1⟩, hx19_1, hx21_1, hx22_1⟩
    have hfsp_align : ((s0.sp - 48#64) &&& 15#64 == 0#64) = true :=
      spAligned_sub s0.sp 48#64 (by assumption) (by decide)
    refine seq_clean (mid := (blkPl_269).base + 144#64)
      (P_mid :=
        vecDequeHeader a G.linksCap G.linksPtr G.linksHead
          (BitVec.ofNat 64 (G.epochs.zip c.links).length) ∗
        ((a + 32#64) ↦₆₄ G.nextRoot.cap) ∗ ((a + 40#64) ↦₆₄ G.nextRoot.ptr) ∗
        memRegion (a + 48#64) 40 ∗
        vecCapPtrDealloc A G.nextRoot.cap G.nextRoot.ptr ∗
        A.pool ∗
        stackAt (s0.sp - 48#64) dropStack32 ∗
        (((s0.sp - 48#64) ↦₆₄ s0.readReg64 .fp) ∗ ((s0.sp - 40#64) ↦₆₄ s0.readReg64 .lr) ∗
         ((s0.sp - 32#64) ↦₆₄ s0.readReg64 .x22) ∗ ((s0.sp - 24#64) ↦₆₄ s0.readReg64 .x21) ∗
         ((s0.sp - 16#64) ↦₆₄ s0.readReg64 .x20) ∗ ((s0.sp - 8#64) ↦₆₄ s0.readReg64 .x19)))
      (Q := fun sm => Saved48Preserved s0 sm (s0.sp - 48#64) ∧ sm.readReg64 .x19 = a)
      ?_ ?_
    · by_cases hc : G.linksCap = 0
      · have hc_beq : (G.linksCap == 0#64) = true := by rw [beq_iff_eq]; exact hc
        simp only [hc, ↓reduceIte, emp_sepConj, sepConj_emp] at hx22_1 ⊢
        wp_steps; wp_done
      · have hc_beq : ¬((G.linksCap == 0#64) = true) := by rw [beq_iff_eq]; exact hc
        have hlsl := cap_lsl7_sub_lsl4 hcap_lt
        have hsp_sub : s0.sp - 4176#64 = (s0.sp - 48#64) - 4128#64 := by bv_omega
        simp only [hc, ↓reduceIte]
        conv => arg 4; rw [stackAt_dropStack32_split_bottom (s0.sp - 48#64)]
        wp_steps
        wp_call hdealloc_raw (G.linksPtr, G.linksCap.toNat * 112, 8)
        refine align_pre (by
          rw [hsp_1, hsp_sub, stackAt_dropStack32_split_bottom (s0.sp - 48#64)]
          ac_rfl) ?_
        wp_done
    · intro s2 hpc2 hrun2 ⟨⟨hx23_2, hx24_2, hx25_2, hx26_2, hx27_2, hx28_2, hsp_2, htrace_2, hvregs_2⟩, hx19_2⟩
      dsimp only [vecCapPtrDealloc]
      by_cases hnr : (G.nextRoot.cap == 0#64) = true <;>
        simp only [hnr, ↓reduceIte, emp_sepConj, sepConj_emp]
      · wp_steps
        refine SepWP.focus_weaken
          (chainHeaders_entails_memRegion_88 a G.linksCap G.linksPtr G.linksHead
            (BitVec.ofNat 64 (G.epochs.zip c.links).length) G.nextRoot.cap G.nextRoot.ptr)
          (by sep_focus) ?_
        refine SepWP.focus_weaken
          (stack_restore_48_dropStack80 s0.sp (s0.readReg64 .fp) (s0.readReg64 .lr)
            (s0.readReg64 .x22) (s0.readReg64 .x21) (s0.readReg64 .x20) (s0.readReg64 .x19))
          (by sep_focus) ?_
        wp_done
      · wp_steps
        refine SepWP.focus_weaken
          (chainHeaders_entails_memRegion_88 a G.linksCap G.linksPtr G.linksHead
            (BitVec.ofNat 64 (G.epochs.zip c.links).length) G.nextRoot.cap G.nextRoot.ptr)
          (by sep_focus) ?_
        refine SepWP.focus_weaken
          (stack_restore_48_dropStack80 s0.sp (s0.readReg64 .fp) (s0.readReg64 .lr)
            (s0.readReg64 .x22) (s0.readReg64 .x21) (s0.readReg64 .x20) (s0.readReg64 .x19))
          (by sep_focus) ?_
        rw [stackAt_dropStack80_split_bottom s0.sp]
        wp_call hdealloc_raw (G.nextRoot.ptr, G.nextRoot.cap.toNat, 1)
        rw [← stackAt_dropStack80_split_bottom s0.sp]
        wp_done

theorem drop_spqr_chain_cl_blockProgram [LibsignalPlacement] {A : RustAlloc}
    {ext : String → Option (State → State)}
    (hdealloc : HookSat (Rust.withPanics ext) spqrRustDeallocSym (rustDeallocSpec A)) :
    subroutine_ok (libsignalSessionLib.blockProgram lsmpl 269 (Rust.withPanics ext)) (lsmpl.base 269)
      (withLsCodeLoaded lsmpl (dropSpqrChainSpec A)) :=
  ls_to_blockProgram (drop_spqr_chain_cl_placed_ok hdealloc)

/-! ## Block `273`: `drop_glue::<spqr::v1::chunked::states::States> [local#2]` -/

local macro "SavedFrame32 " s0:term:max v_x19:term:max : term =>
  `(((State.sp $s0 - 32#64) ↦₆₄ State.readReg64 $s0 .fp) ∗ ((State.sp $s0 - 24#64) ↦₆₄ State.readReg64 $s0 .lr) ∗
    ((State.sp $s0 - 16#64) ↦₆₄ State.readReg64 $s0 .x19) ∗ ((State.sp $s0 - 8#64) ↦₆₄ $v_x19))

private theorem drop_chunked_states_local2_keysUnsampled_cl [LibsignalPlacement]
    {A : RustAlloc} {F : ShaCompress} {ext : String → Option (State → State)}
    (hdealloc : HookSat (Rust.withPanics ext) spqrRustDeallocSym (rustDeallocSpec A))
    (st : Chunked.SendEk.KeysUnsampled (spqrAuthApi F)) :
    subroutine_ok (lsProg_273 (Rust.withPanics ext)) (blkPl_273).base
      (withLsCodeLoaded lsmpl (dropChunkedStatesLocal2PlacedVariantSpec A (.keysUnsampled st))) :=
  subroutine_ok_withLsCodeLoaded_of_plain
    (drop_chunked_states_local2_keysUnsampled_placed (spqr_hook_ok_of_mem hdealloc) st)

private theorem drop_chunked_states_local2_ct1Received_cl [LibsignalPlacement]
    {A : RustAlloc} {F : ShaCompress} {ext : String → Option (State → State)}
    (hdealloc : HookSat (Rust.withPanics ext) spqrRustDeallocSym (rustDeallocSpec A))
    (st : Chunked.SendEk.Ct1Received spqrPolyApi (spqrAuthApi F)) :
    subroutine_ok (lsProg_273 (Rust.withPanics ext)) (blkPl_273).base
      (withLsCodeLoaded lsmpl (dropChunkedStatesLocal2PlacedVariantSpec A (.ct1Received st))) := by
  change subroutine_ok ((blkPC_273).rebase (blkPl_273).base (Rust.withPanics ext)) (blkPl_273).base _
  apply subroutine_ok_withLsCodeLoaded_intro; intro m hcl
  dsimp only [withMemEq, dropChunkedStatesLocal2PlacedVariantSpec, chunkedStatesAt,
    chunkedStatesLocal2JumpTablePlacedAt, chunkedStatesLocal2JumpTableSym,
    chunkedStatesLocal2JumpTableBytes, chunkedStatesSize, BitVec.ofNat_eq_ofNat] at ⊢
  wp_init a s0; have hm : s0.mem = m := (by assumption); subst hm
  nth_rw 1 [stackAt_dropStackPoly64_split s0.sp]; cells_unfold; wp_pull_exists
  rename_i v_fp v_lr v_x20 v_x19
  apply sepWP_seq_lscl hcl (mid := lsmpl.base 277); wp_steps
  apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs); intro hcl_call
  have hsub_raw := drop_chunked_ct1_received_mem_on
    (callerProg := lsProg_273 (Rust.withPanics ext)) (F := F) hdealloc hcl_call
  dsimp only [lsProg_273, withMemEq, dropChunkedCt1ReceivedSpec, chunkedCt1ReceivedSize, BitVec.ofNat_eq_ofNat] at hsub_raw
  refine SepWP.focus_weaken
    (stack_restore_64_dropStack32 s0.sp (s0.readReg64 .fp) (s0.readReg64 .lr) (s0.readReg64 .x19) v_x19)
    (by sep_focus) ?_
  refine SepWP.focus_weaken (Entails.of_eq (stackAt_dropStackPoly64_split_bottom s0.sp)) (by sep_focus) ?_
  wp_call hsub_raw ⟨a + 8#64, st⟩
  refine SepWP.focus_weaken (Entails.of_eq (stackAt_dropStackPoly64_split_bottom s0.sp).symm) (by sep_focus) ?_
  refine SepWP.focus_weaken (tag_and_two_regions_entails_928 a 5#64 504 416 512#64
    (BitVec.add_assoc a 8#64 504#64).symm rfl) (by sep_focus) ?_; wp_done

private theorem drop_chunked_states_local2_keysSampled_cl [LibsignalPlacement]
    {A : RustAlloc} {F : ShaCompress} {ext : String → Option (State → State)}
    (hdealloc : HookSat (Rust.withPanics ext) spqrRustDeallocSym (rustDeallocSpec A))
    (st : Chunked.SendEk.KeysSampled spqrPolyApi (spqrAuthApi F)) :
    subroutine_ok (lsProg_273 (Rust.withPanics ext)) (blkPl_273).base
      (withLsCodeLoaded lsmpl (dropChunkedStatesLocal2PlacedVariantSpec A (.keysSampled st))) := by
  change subroutine_ok ((blkPC_273).rebase (blkPl_273).base (Rust.withPanics ext)) (blkPl_273).base _
  apply subroutine_ok_withLsCodeLoaded_intro; intro m hcl
  dsimp only [withMemEq, dropChunkedStatesLocal2PlacedVariantSpec, chunkedStatesAt,
    chunkedStatesLocal2JumpTablePlacedAt, chunkedStatesLocal2JumpTableSym,
    chunkedStatesLocal2JumpTableBytes, chunkedStatesSize, BitVec.ofNat_eq_ofNat] at ⊢
  wp_init a s0; have hm : s0.mem = m := (by assumption); subst hm
  rw [chunkedKeysSampledAt_eq_ct1ReceivedAt]
  nth_rw 1 [stackAt_dropStackPoly64_split s0.sp]; cells_unfold; wp_pull_exists
  rename_i v_fp v_lr v_x20 v_x19
  apply sepWP_seq_lscl hcl (mid := lsmpl.base 277); wp_steps
  apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs); intro hcl_call
  have hsub_raw := drop_chunked_ct1_received_mem_on
    (callerProg := lsProg_273 (Rust.withPanics ext)) (F := F) hdealloc hcl_call
  dsimp only [lsProg_273, withMemEq, dropChunkedCt1ReceivedSpec, chunkedCt1ReceivedSize, BitVec.ofNat_eq_ofNat] at hsub_raw
  refine SepWP.focus_weaken
    (stack_restore_64_dropStack32 s0.sp (s0.readReg64 .fp) (s0.readReg64 .lr) (s0.readReg64 .x19) v_x19)
    (by sep_focus) ?_
  refine SepWP.focus_weaken (Entails.of_eq (stackAt_dropStackPoly64_split_bottom s0.sp)) (by sep_focus) ?_
  wp_call hsub_raw ⟨a + 8#64, chunkedKeysSampledToCt1Received st⟩
  refine SepWP.focus_weaken (Entails.of_eq (stackAt_dropStackPoly64_split_bottom s0.sp).symm) (by sep_focus) ?_
  refine SepWP.focus_weaken (tag_and_two_regions_entails_928 a 3#64 504 416 512#64
    (BitVec.add_assoc a 8#64 504#64).symm rfl) (by sep_focus) ?_; wp_done

private theorem drop_chunked_states_local2_headerSent_cl [LibsignalPlacement]
    {A : RustAlloc} {F : ShaCompress} {ext : String → Option (State → State)}
    (hdealloc : HookSat (Rust.withPanics ext) spqrRustDeallocSym (rustDeallocSpec A))
    (st : Chunked.SendEk.HeaderSent spqrPolyApi (spqrAuthApi F)) :
    subroutine_ok (lsProg_273 (Rust.withPanics ext)) (blkPl_273).base
      (withLsCodeLoaded lsmpl (dropChunkedStatesLocal2PlacedVariantSpec A (.headerSent st))) := by
  change subroutine_ok ((blkPC_273).rebase (blkPl_273).base (Rust.withPanics ext)) (blkPl_273).base _
  apply subroutine_ok_withLsCodeLoaded_intro; intro m hcl
  dsimp only [withMemEq, dropChunkedStatesLocal2PlacedVariantSpec, chunkedStatesAt,
    chunkedStatesLocal2JumpTablePlacedAt, chunkedStatesLocal2JumpTableSym,
    chunkedStatesLocal2JumpTableBytes, chunkedStatesSize, BitVec.ofNat_eq_ofNat] at ⊢
  wp_init a s0; have hm : s0.mem = m := (by assumption); subst hm
  nth_rw 1 [stackAt_dropStackPoly64_split s0.sp]; cells_unfold; wp_pull_exists
  rename_i v_fp v_lr v_x20 v_x19
  apply sepWP_seq_lscl hcl (mid := lsmpl.base 276); wp_steps
  apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs); intro hcl_call
  have hsub_raw := drop_chunked_header_sent_mem_on
    (callerProg := lsProg_273 (Rust.withPanics ext)) (F := F) hdealloc hcl_call
  dsimp only [lsProg_273, withMemEq, dropChunkedHeaderSentSpec, chunkedHeaderSentSize, BitVec.ofNat_eq_ofNat] at hsub_raw
  refine SepWP.focus_weaken
    (stack_restore_64_dropStack32 s0.sp (s0.readReg64 .fp) (s0.readReg64 .lr) (s0.readReg64 .x19) v_x19)
    (by sep_focus) ?_
  wp_call hsub_raw ⟨a + 8#64, st⟩
  refine SepWP.focus_weaken (tag_and_two_regions_entails_928 a 4#64 880 40 888#64
    (BitVec.add_assoc a 8#64 880#64).symm rfl) (by sep_focus) ?_; wp_done

private theorem drop_chunked_states_local2_ekSentCt1Received_cl [LibsignalPlacement]
    {A : RustAlloc} {F : ShaCompress} {ext : String → Option (State → State)}
    (hdealloc : HookSat (Rust.withPanics ext) spqrRustDeallocSym (rustDeallocSpec A))
    (st : Chunked.SendEk.EkSentCt1Received spqrPolyApi (spqrAuthApi F)) :
    subroutine_ok (lsProg_273 (Rust.withPanics ext)) (blkPl_273).base
      (withLsCodeLoaded lsmpl (dropChunkedStatesLocal2PlacedVariantSpec A (.ekSentCt1Received st))) := by
  change subroutine_ok ((blkPC_273).rebase (blkPl_273).base (Rust.withPanics ext)) (blkPl_273).base _
  apply subroutine_ok_withLsCodeLoaded_intro; intro m hcl
  dsimp only [withMemEq, dropChunkedStatesLocal2PlacedVariantSpec, chunkedStatesAt,
    chunkedStatesLocal2JumpTablePlacedAt, chunkedStatesLocal2JumpTableSym,
    chunkedStatesLocal2JumpTableBytes, chunkedStatesSize, BitVec.ofNat_eq_ofNat] at ⊢
  wp_init a s0; have hm : s0.mem = m := (by assumption); subst hm
  nth_rw 1 [stackAt_dropStackPoly64_split s0.sp]; cells_unfold; wp_pull_exists
  rename_i v_fp v_lr v_x20 v_x19
  apply sepWP_seq_lscl hcl (mid := lsmpl.base 278); wp_steps
  apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs); intro hcl_call
  have hsub_raw := drop_chunked_ek_sent_ct1_received_mem_on
    (callerProg := lsProg_273 (Rust.withPanics ext)) (F := F) hdealloc hcl_call
  dsimp only [lsProg_273, withMemEq, dropChunkedEkSentCt1ReceivedSpec, chunkedEkSentCt1ReceivedSize, BitVec.ofNat_eq_ofNat] at hsub_raw
  refine SepWP.focus_weaken
    (stack_restore_64_dropStack32 s0.sp (s0.readReg64 .fp) (s0.readReg64 .lr) (s0.readReg64 .x19) v_x19)
    (by sep_focus) ?_
  refine SepWP.focus_weaken (Entails.of_eq (stackAt_dropStackPoly64_split_bottom s0.sp)) (by sep_focus) ?_
  wp_call hsub_raw ⟨a + 8#64, st⟩
  refine SepWP.focus_weaken (Entails.of_eq (stackAt_dropStackPoly64_split_bottom s0.sp).symm) (by sep_focus) ?_
  refine SepWP.focus_weaken (tag_and_two_regions_entails_928 a 6#64 504 416 512#64
    (BitVec.add_assoc a 8#64 504#64).symm rfl) (by sep_focus) ?_; wp_done

private theorem drop_chunked_states_local2_ekReceivedCt1Sampled_cl [LibsignalPlacement]
    {A : RustAlloc} {F : ShaCompress} {ext : String → Option (State → State)}
    (hdealloc : HookSat (Rust.withPanics ext) spqrRustDeallocSym (rustDeallocSpec A))
    (st : Chunked.SendCt.EkReceivedCt1Sampled spqrPolyApi (spqrAuthApi F)) :
    subroutine_ok (lsProg_273 (Rust.withPanics ext)) (blkPl_273).base
      (withLsCodeLoaded lsmpl (dropChunkedStatesLocal2PlacedVariantSpec A (.ekReceivedCt1Sampled st))) := by
  change subroutine_ok ((blkPC_273).rebase (blkPl_273).base (Rust.withPanics ext)) (blkPl_273).base _
  apply subroutine_ok_withLsCodeLoaded_intro; intro m hcl
  dsimp only [withMemEq, dropChunkedStatesLocal2PlacedVariantSpec, chunkedStatesAt,
    chunkedStatesLocal2JumpTablePlacedAt, chunkedStatesLocal2JumpTableSym,
    chunkedStatesLocal2JumpTableBytes, chunkedStatesSize, BitVec.ofNat_eq_ofNat] at ⊢
  wp_init a s0; have hm : s0.mem = m := (by assumption); subst hm
  nth_rw 1 [stackAt_dropStackPoly64_split s0.sp]; cells_unfold; wp_pull_exists
  rename_i v_fp v_lr v_x20 v_x19
  apply sepWP_seq_lscl hcl (mid := lsmpl.base 275); wp_steps
  apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs); intro hcl_call
  have hsub_raw := drop_chunked_ek_received_ct1_sampled_mem_on
    (callerProg := lsProg_273 (Rust.withPanics ext)) (F := F) hdealloc hcl_call
  dsimp only [lsProg_273, withMemEq, dropChunkedEkReceivedCt1SampledSpec, chunkedEkReceivedCt1SampledSize, BitVec.ofNat_eq_ofNat] at hsub_raw
  refine SepWP.focus_weaken
    (stack_restore_64_dropStack32 s0.sp (s0.readReg64 .fp) (s0.readReg64 .lr) (s0.readReg64 .x19) v_x19)
    (by sep_focus) ?_
  refine SepWP.focus_weaken (Entails.of_eq (stackAt_dropStackPoly64_split_bottom s0.sp)) (by sep_focus) ?_
  wp_call hsub_raw ⟨a + 8#64, st⟩
  refine SepWP.focus_weaken (Entails.of_eq (stackAt_dropStackPoly64_split_bottom s0.sp).symm) (by sep_focus) ?_
  refine SepWP.focus_weaken (tag_and_two_regions_entails_928 a 10#64 528 392 536#64
    (BitVec.add_assoc a 8#64 528#64).symm rfl) (by sep_focus) ?_; wp_done

private theorem drop_chunked_states_local2_noHeaderReceived_cl [LibsignalPlacement]
    {A : RustAlloc} {F : ShaCompress} {ext : String → Option (State → State)}
    (hdealloc : HookSat (Rust.withPanics ext) spqrRustDeallocSym (rustDeallocSpec A))
    (st : Chunked.SendCt.NoHeaderReceived spqrPolyApi (spqrAuthApi F)) :
    subroutine_ok (lsProg_273 (Rust.withPanics ext)) (blkPl_273).base
      (withLsCodeLoaded lsmpl (dropChunkedStatesLocal2PlacedVariantSpec A (.noHeaderReceived st))) := by
  change subroutine_ok ((blkPC_273).rebase (blkPl_273).base (Rust.withPanics ext)) (blkPl_273).base _
  apply subroutine_ok_withLsCodeLoaded_intro; intro m hcl
  have hdealloc_raw : subroutine_ok ((blkPC_273).rebase (blkPl_273).base (Rust.withPanics ext))
      (lsρ spqrRustDeallocSym) (rustDeallocSpec A) := spqr_hook_ok_of_mem hdealloc
  simp only [rustDeallocSpec] at hdealloc_raw
  dsimp only [withMemEq, dropChunkedStatesLocal2PlacedVariantSpec, chunkedStatesAt,
    chunkedNoHeaderReceivedAt, chunkedStatesLocal2JumpTablePlacedAt, chunkedStatesLocal2JumpTableSym,
    chunkedStatesLocal2JumpTableBytes, chunkedStatesSize, polyArrayBytes, dropGluePoly16Stack,
    spqrPolyApi, BitVec.ofNat_eq_ofNat] at hdealloc_raw ⊢
  wp_init a s0; have hm : s0.mem = m := (by assumption); subst hm
  have hfsp_align : ((s0.sp - 32#64) &&& 15#64 == 0#64) = true :=
    spAligned_sub s0.sp 32#64 (by assumption) (by decide)
  rw [unchunkedNoHeaderReceivedAt_eq_ct2SentAt]
  refine SepWP.focus_weaken (unchunkedCt2Sent8_entails_dealloc A a { epoch := st.uc.epoch, auth := st.uc.auth })
    (by sep_focus) ?_
  wp_pull_exists; rename_i g
  refine SepWP.focus_weaken (polyDecoder64_entails_vecs_tail A a st.receiving_hdr) (by sep_focus) ?_
  wp_pull_exists; rename_i vecs; wp_focus_pure; intro hvecs_len
  dsimp only [twoVec8HeadersAt, vecCapPtrDealloc]
  nth_rw 1 [stackAt_dropStackPoly64_split s0.sp]; cells_unfold; wp_pull_exists
  rename_i v_fp v_lr v_x20 v_x19
  have hsplit32 := stackAt_dropStack32_split_sub32 s0.sp
  refine SepWP.focus_weaken (Entails.of_eq hsplit32) (by sep_focus) ?_
  refine seq_clean_lscl hcl (mid := (blkPl_273).base + 240#64)
    (P_mid := ((a ↦₆₄ 7#64) ∗
      ((a + 8#64) ↦₆₄ g.v1.cap) ∗ ((a + 16#64) ↦₆₄ g.v1.ptr) ∗ memRegion (a + 24#64) 8 ∗
      ((a + 32#64) ↦₆₄ g.v2.cap) ∗ ((a + 40#64) ↦₆₄ g.v2.ptr) ∗ memRegion (a + 48#64) 16 ∗
      (if (g.v2.cap == 0#64) = true then emp
       else A.live g.v2.ptr g.v2.cap.toNat 1 ∗ memRegion g.v2.ptr g.v2.cap.toNat) ∗
      vecPtListOf A (a + 64#64) vecs ∗ memRegion (a + 448#64) 16 ∗ memRegion (a + 464#64) 464) ∗
      chunkedStatesLocal2JumpTablePlacedExpanded ∗
      A.pool ∗ (memRegion (s0.sp - 4160#64) 32 ∗ stackAt (s0.sp - 32#64) allocHookStack) ∗
      SavedFrame32 s0 v_x19)
    (Q := fun sm => Saved32x19Preserved s0 sm (s0.sp - 32#64) ∧ sm.readReg64 .x19 = a) ?_ ?_
  · by_cases hc1 : (g.v1.cap == 0#64) = true <;>
      simp only [hc1, Bool.false_eq_true, ↓reduceIte, emp_sepConj, sepConj_emp]
    · wp_steps
      refine align_pre (by simp only [Reg.fp, Reg.lr, Reg.x19, chunkedStatesLocal2JumpTablePlacedExpanded, chunkedStatesLocal2JumpTableSym]; ac_rfl) ?_; wp_done
    · wp_steps; wp_apply
      refine align_pre (by simp only [Reg.fp, Reg.lr, Reg.x19, chunkedStatesLocal2JumpTablePlacedExpanded, chunkedStatesLocal2JumpTableSym]; ac_rfl) ?_; wp_done
  · intro s1 hpc1 hrun1 hcl1 ⟨⟨hx20_1, hx21_1, hx22_1, hx23_1, hx24_1, hx25_1, hx26_1, hx27_1, hx28_1, hsp_1, htrace_1, hvregs_1⟩, hx19_1⟩
    refine seq_clean_lscl hcl1 (mid := (blkPl_273).base + 260#64)
      (P_mid := ((a ↦₆₄ 7#64) ∗ memRegion (a + 8#64) 56 ∗
        vecPtListOf A (a + 64#64) vecs ∗ memRegion (a + 448#64) 16 ∗ memRegion (a + 464#64) 464) ∗
        chunkedStatesLocal2JumpTablePlacedExpanded ∗
        A.pool ∗ stackAt (s0.sp - 32#64) dropStack32 ∗ SavedFrame32 s0 v_x19)
      (Q := fun sm => Saved32x19Preserved s0 sm (s0.sp - 32#64) ∧ sm.readReg64 .x19 = a) ?_ ?_
    · have hhdr56 := twoVec8HeadersAt_entails_memRegion_56 a g
      dsimp only [twoVec8HeadersAt] at hhdr56
      by_cases hc2 : (g.v2.cap == 0#64) = true <;>
        simp only [hc2, Bool.false_eq_true, ↓reduceIte, emp_sepConj, sepConj_emp]
      · wp_steps
        refine SepWP.focus_weaken hhdr56 (by sep_focus) ?_
        refine SepWP.focus_weaken (Entails.of_eq hsplit32.symm) (by sep_focus) ?_
        refine align_pre (by simp only [Reg.fp, Reg.lr, Reg.x19, chunkedStatesLocal2JumpTablePlacedExpanded, chunkedStatesLocal2JumpTableSym]; ac_rfl) ?_; wp_done
      · wp_steps; wp_apply
        refine SepWP.focus_weaken hhdr56 (by sep_focus) ?_
        have hsp_eq : stackAt s1.sp allocHookStack = stackAt (s0.sp - 32#64) allocHookStack := by rw [hsp_1]
        refine SepWP.focus_weaken (Entails.of_eq hsp_eq) (by sep_focus) ?_
        refine SepWP.focus_weaken (Entails.of_eq hsplit32.symm) (by sep_focus) ?_
        refine align_pre (by simp only [Reg.fp, Reg.lr, Reg.x19, chunkedStatesLocal2JumpTablePlacedExpanded, chunkedStatesLocal2JumpTableSym]; ac_rfl) ?_; wp_done
    · intro s2 hpc2 hrun2 hcl2 ⟨⟨hx20_2, hx21_2, hx22_2, hx23_2, hx24_2, hx25_2, hx26_2, hx27_2, hx28_2, hsp_2, htrace_2, hvregs_2⟩, hx19_2⟩
      dsimp only [chunkedStatesLocal2JumpTablePlacedExpanded, chunkedStatesLocal2JumpTableSym]
      apply sepWP_seq_lscl hcl2 (mid := lsmpl.base 264); wp_steps
      apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs); intro hcl_call
      have hpt16_raw := drop_glue_sorted_set_pt16_mem_on
        (callerProg := lsProg_273 (Rust.withPanics ext)) hdealloc hcl_call
      dsimp only [lsProg_273, withMemEq, dropGlueSortedSetPt16Spec, polyArrayBytes, dropGluePoly16Stack, BitVec.ofNat_eq_ofNat] at hpt16_raw
      refine SepWP.focus_weaken
        (stack_restore_64_dropStack32 s0.sp (s0.readReg64 .fp) (s0.readReg64 .lr) (s0.readReg64 .x19) v_x19)
        (by sep_focus) ?_
      refine SepWP.focus_weaken (Entails.of_eq (stackAt_dropStackPoly64_split_bottom s0.sp)) (by sep_focus) ?_
      wp_call hpt16_raw ⟨a + 64#64, vecs⟩
      refine SepWP.focus_weaken (Entails.of_eq (stackAt_dropStackPoly64_split_bottom s0.sp).symm) (by sep_focus) ?_
      refine SepWP.focus_weaken (polyDecoder64_post_join a) (by sep_focus) ?_
      have hjoin456 : memRegion (a + 8#64) 56 ∗ memRegion (a + 64#64) polyDecoderSize ⊢
          memRegion (a + 8#64) 456 := by
        have h64 : (a + 8#64) + 56#64 = a + 64#64 := BitVec.add_assoc a 8#64 56#64
        rw [← h64, show (456 : Nat) = 56 + polyDecoderSize from rfl,
            ProofLib.memRegion_split (a + 8#64) 56 polyDecoderSize (by decide)]
        exact Entails.refl _
      refine SepWP.focus_weaken hjoin456 (by sep_focus) ?_
      refine SepWP.focus_weaken (tag_and_two_regions_entails_928 a 7#64 456 464 464#64
        (BitVec.add_assoc a 8#64 456#64).symm rfl) (by sep_focus) ?_; wp_done

private theorem drop_chunked_states_local2_headerReceived_cl [LibsignalPlacement]
    {A : RustAlloc} {F : ShaCompress} {ext : String → Option (State → State)}
    (hdealloc : HookSat (Rust.withPanics ext) spqrRustDeallocSym (rustDeallocSpec A))
    (st : Chunked.SendCt.HeaderReceived spqrPolyApi (spqrAuthApi F)) :
    subroutine_ok (lsProg_273 (Rust.withPanics ext)) (blkPl_273).base
      (withLsCodeLoaded lsmpl (dropChunkedStatesLocal2PlacedVariantSpec A (.headerReceived st))) := by
  change subroutine_ok ((blkPC_273).rebase (blkPl_273).base (Rust.withPanics ext)) (blkPl_273).base _
  apply subroutine_ok_withLsCodeLoaded_intro; intro m hcl
  have hdealloc_raw : subroutine_ok ((blkPC_273).rebase (blkPl_273).base (Rust.withPanics ext))
      (lsρ spqrRustDeallocSym) (rustDeallocSpec A) := spqr_hook_ok_of_mem hdealloc
  simp only [rustDeallocSpec] at hdealloc_raw
  dsimp only [withMemEq, dropChunkedStatesLocal2PlacedVariantSpec, chunkedStatesAt,
    chunkedHeaderReceivedAt, chunkedStatesLocal2JumpTablePlacedAt, chunkedStatesLocal2JumpTableSym,
    chunkedStatesLocal2JumpTableBytes, chunkedStatesSize, polyArrayBytes, dropGluePoly16Stack,
    spqrPolyApi, BitVec.ofNat_eq_ofNat] at hdealloc_raw ⊢
  wp_init a s0; have hm : s0.mem = m := (by assumption); subst hm
  have hfsp_align : ((s0.sp - 32#64) &&& 15#64 == 0#64) = true :=
    spAligned_sub s0.sp 32#64 (by assumption) (by decide)
  rw [unchunkedHeaderReceivedAt_eq_ekSentAt]
  refine SepWP.focus_weaken
    (unchunkedEkSent8_entails_dealloc A a { epoch := st.uc.epoch, auth := st.uc.auth, dk := st.uc.hdr })
    (by sep_focus) ?_
  wp_pull_exists; rename_i g
  refine SepWP.focus_weaken (polyDecoder88_entails_vecs_tail A a st.receiving_ek) (by sep_focus) ?_
  wp_pull_exists; rename_i vecs; wp_focus_pure; intro hvecs_len
  dsimp only [threeVec8HeadersAt, vecCapPtrDealloc]
  nth_rw 1 [stackAt_dropStackPoly64_split s0.sp]; cells_unfold; wp_pull_exists
  rename_i v_fp v_lr v_x20 v_x19
  have hsplit32 := stackAt_dropStack32_split_sub32 s0.sp
  refine SepWP.focus_weaken (Entails.of_eq hsplit32) (by sep_focus) ?_
  refine seq_clean_lscl hcl (mid := (blkPl_273).base + 296#64)
    (P_mid := ((a ↦₆₄ 8#64) ∗
      ((a + 8#64) ↦₆₄ g.v1.cap) ∗ ((a + 16#64) ↦₆₄ g.v1.ptr) ∗ memRegion (a + 24#64) 8 ∗
      ((a + 32#64) ↦₆₄ g.v2.cap) ∗ ((a + 40#64) ↦₆₄ g.v2.ptr) ∗ memRegion (a + 48#64) 8 ∗
      ((a + 56#64) ↦₆₄ g.v3.cap) ∗ ((a + 64#64) ↦₆₄ g.v3.ptr) ∗ memRegion (a + 72#64) 16 ∗
      (if (g.v2.cap == 0#64) = true then emp
       else A.live g.v2.ptr g.v2.cap.toNat 1 ∗ memRegion g.v2.ptr g.v2.cap.toNat) ∗
      (if (g.v3.cap == 0#64) = true then emp
       else A.live g.v3.ptr g.v3.cap.toNat 1 ∗ memRegion g.v3.ptr g.v3.cap.toNat) ∗
      vecPtListOf A (a + 88#64) vecs ∗ memRegion (a + 472#64) 16 ∗ memRegion (a + 488#64) 440) ∗
      chunkedStatesLocal2JumpTablePlacedExpanded ∗
      A.pool ∗ (memRegion (s0.sp - 4160#64) 32 ∗ stackAt (s0.sp - 32#64) allocHookStack) ∗
      SavedFrame32 s0 v_x19)
    (Q := fun sm => Saved32x19Preserved s0 sm (s0.sp - 32#64) ∧ sm.readReg64 .x19 = a) ?_ ?_
  · by_cases hc1 : (g.v1.cap == 0#64) = true <;>
      simp only [hc1, Bool.false_eq_true, ↓reduceIte, emp_sepConj, sepConj_emp]
    · wp_steps
      refine align_pre (by simp only [Reg.fp, Reg.lr, Reg.x19, chunkedStatesLocal2JumpTablePlacedExpanded, chunkedStatesLocal2JumpTableSym]; ac_rfl) ?_; wp_done
    · wp_steps; wp_apply
      refine align_pre (by simp only [Reg.fp, Reg.lr, Reg.x19, chunkedStatesLocal2JumpTablePlacedExpanded, chunkedStatesLocal2JumpTableSym]; ac_rfl) ?_; wp_done
  · intro s1 hpc1 hrun1 hcl1 ⟨⟨hx20_1, hx21_1, hx22_1, hx23_1, hx24_1, hx25_1, hx26_1, hx27_1, hx28_1, hsp_1, htrace_1, hvregs_1⟩, hx19_1⟩
    refine seq_clean_lscl hcl1 (mid := (blkPl_273).base + 316#64)
      (P_mid := ((a ↦₆₄ 8#64) ∗
        ((a + 8#64) ↦₆₄ g.v1.cap) ∗ ((a + 16#64) ↦₆₄ g.v1.ptr) ∗ memRegion (a + 24#64) 8 ∗
        ((a + 32#64) ↦₆₄ g.v2.cap) ∗ ((a + 40#64) ↦₆₄ g.v2.ptr) ∗ memRegion (a + 48#64) 8 ∗
        ((a + 56#64) ↦₆₄ g.v3.cap) ∗ ((a + 64#64) ↦₆₄ g.v3.ptr) ∗ memRegion (a + 72#64) 16 ∗
        (if (g.v3.cap == 0#64) = true then emp
         else A.live g.v3.ptr g.v3.cap.toNat 1 ∗ memRegion g.v3.ptr g.v3.cap.toNat) ∗
        vecPtListOf A (a + 88#64) vecs ∗ memRegion (a + 472#64) 16 ∗ memRegion (a + 488#64) 440) ∗
        chunkedStatesLocal2JumpTablePlacedExpanded ∗
        A.pool ∗ (memRegion (s0.sp - 4160#64) 32 ∗ stackAt (s0.sp - 32#64) allocHookStack) ∗
        SavedFrame32 s0 v_x19)
      (Q := fun sm => Saved32x19Preserved s0 sm (s0.sp - 32#64) ∧ sm.readReg64 .x19 = a) ?_ ?_
    · by_cases hc2 : (g.v2.cap == 0#64) = true <;>
        simp only [hc2, Bool.false_eq_true, ↓reduceIte, emp_sepConj, sepConj_emp]
      · wp_steps
        refine align_pre (by simp only [Reg.fp, Reg.lr, Reg.x19, chunkedStatesLocal2JumpTablePlacedExpanded, chunkedStatesLocal2JumpTableSym]) ?_; wp_done
      · wp_steps; wp_apply
        refine align_pre (by rw [hsp_1]; simp only [Reg.fp, Reg.lr, Reg.x19, chunkedStatesLocal2JumpTablePlacedExpanded, chunkedStatesLocal2JumpTableSym]; ac_rfl) ?_; wp_done
    · intro s2 hpc2 hrun2 hcl2 ⟨⟨hx20_2, hx21_2, hx22_2, hx23_2, hx24_2, hx25_2, hx26_2, hx27_2, hx28_2, hsp_2, htrace_2, hvregs_2⟩, hx19_2⟩
      refine seq_clean_lscl hcl2 (mid := (blkPl_273).base + 336#64)
        (P_mid := ((a ↦₆₄ 8#64) ∗ memRegion (a + 8#64) 80 ∗
          vecPtListOf A (a + 88#64) vecs ∗ memRegion (a + 472#64) 16 ∗ memRegion (a + 488#64) 440) ∗
          chunkedStatesLocal2JumpTablePlacedExpanded ∗
          A.pool ∗ stackAt (s0.sp - 32#64) dropStack32 ∗ SavedFrame32 s0 v_x19)
        (Q := fun sm => Saved32x19Preserved s0 sm (s0.sp - 32#64) ∧ sm.readReg64 .x19 = a) ?_ ?_
      · have hhdr80 := threeVec8HeadersAt_entails_memRegion_80 a g
        dsimp only [threeVec8HeadersAt] at hhdr80
        by_cases hc3 : (g.v3.cap == 0#64) = true <;>
          simp only [hc3, Bool.false_eq_true, ↓reduceIte, emp_sepConj, sepConj_emp]
        · wp_steps
          refine SepWP.focus_weaken hhdr80 (by sep_focus) ?_
          refine SepWP.focus_weaken (Entails.of_eq hsplit32.symm) (by sep_focus) ?_
          refine align_pre (by simp only [Reg.fp, Reg.lr, Reg.x19, chunkedStatesLocal2JumpTablePlacedExpanded, chunkedStatesLocal2JumpTableSym]; ac_rfl) ?_; wp_done
        · wp_steps; wp_apply
          refine SepWP.focus_weaken hhdr80 (by sep_focus) ?_
          have hsp_eq : stackAt s2.sp allocHookStack = stackAt (s0.sp - 32#64) allocHookStack := by rw [hsp_2]
          refine SepWP.focus_weaken (Entails.of_eq hsp_eq) (by sep_focus) ?_
          refine SepWP.focus_weaken (Entails.of_eq hsplit32.symm) (by sep_focus) ?_
          refine align_pre (by simp only [Reg.fp, Reg.lr, Reg.x19, chunkedStatesLocal2JumpTablePlacedExpanded, chunkedStatesLocal2JumpTableSym]; ac_rfl) ?_; wp_done
      · intro s3 hpc3 hrun3 hcl3 ⟨⟨hx20_3, hx21_3, hx22_3, hx23_3, hx24_3, hx25_3, hx26_3, hx27_3, hx28_3, hsp_3, htrace_3, hvregs_3⟩, hx19_3⟩
        dsimp only [chunkedStatesLocal2JumpTablePlacedExpanded, chunkedStatesLocal2JumpTableSym]
        apply sepWP_seq_lscl hcl3 (mid := lsmpl.base 264); wp_steps
        apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs); intro hcl_call
        have hpt16_raw := drop_glue_sorted_set_pt16_mem_on
          (callerProg := lsProg_273 (Rust.withPanics ext)) hdealloc hcl_call
        dsimp only [lsProg_273, withMemEq, dropGlueSortedSetPt16Spec, polyArrayBytes, dropGluePoly16Stack, BitVec.ofNat_eq_ofNat] at hpt16_raw
        refine SepWP.focus_weaken
          (stack_restore_64_dropStack32 s0.sp (s0.readReg64 .fp) (s0.readReg64 .lr) (s0.readReg64 .x19) v_x19)
          (by sep_focus) ?_
        refine SepWP.focus_weaken (Entails.of_eq (stackAt_dropStackPoly64_split_bottom s0.sp)) (by sep_focus) ?_
        wp_call hpt16_raw ⟨a + 88#64, vecs⟩
        refine SepWP.focus_weaken (Entails.of_eq (stackAt_dropStackPoly64_split_bottom s0.sp).symm) (by sep_focus) ?_
        refine SepWP.focus_weaken (polyDecoder88_post_join a) (by sep_focus) ?_
        have hjoin480 : memRegion (a + 8#64) 80 ∗ memRegion (a + 88#64) polyDecoderSize ⊢
            memRegion (a + 8#64) 480 := by
          have h88 : (a + 8#64) + 80#64 = a + 88#64 := BitVec.add_assoc a 8#64 80#64
          rw [← h88, show (480 : Nat) = 80 + polyDecoderSize from rfl,
              ProofLib.memRegion_split (a + 8#64) 80 polyDecoderSize (by decide)]
          exact Entails.refl _
        refine SepWP.focus_weaken hjoin480 (by sep_focus) ?_
        refine SepWP.focus_weaken (tag_and_two_regions_entails_928 a 8#64 480 440 488#64
          (BitVec.add_assoc a 8#64 480#64).symm rfl) (by sep_focus) ?_; wp_done

private theorem drop_chunked_states_local2_ct1Acknowledged_cl [LibsignalPlacement]
    {A : RustAlloc} {F : ShaCompress} {ext : String → Option (State → State)}
    (hdealloc : HookSat (Rust.withPanics ext) spqrRustDeallocSym (rustDeallocSpec A))
    (st : Chunked.SendCt.Ct1Acknowledged spqrPolyApi (spqrAuthApi F)) :
    subroutine_ok (lsProg_273 (Rust.withPanics ext)) (blkPl_273).base
      (withLsCodeLoaded lsmpl (dropChunkedStatesLocal2PlacedVariantSpec A (.ct1Acknowledged st))) := by
  change subroutine_ok ((blkPC_273).rebase (blkPl_273).base (Rust.withPanics ext)) (blkPl_273).base _
  apply subroutine_ok_withLsCodeLoaded_intro; intro m hcl
  dsimp only [withMemEq, dropChunkedStatesLocal2PlacedVariantSpec, chunkedStatesAt,
    chunkedCt1AcknowledgedAt, chunkedStatesLocal2JumpTablePlacedAt, chunkedStatesLocal2JumpTableSym,
    chunkedStatesLocal2JumpTableBytes, chunkedStatesSize, polyArrayBytes, dropGluePoly16Stack,
    spqrPolyApi, BitVec.ofNat_eq_ofNat] at ⊢
  wp_init a s0; have hm : s0.mem = m := (by assumption); subst hm
  have hfsp_align : ((s0.sp - 32#64) &&& 15#64 == 0#64) = true :=
    spAligned_sub s0.sp 32#64 (by assumption) (by decide)
  refine SepWP.focus_weaken (polyDecoderAt_entails_vecs_tail A (a + 136#64) st.receiving_ek) (by sep_focus) ?_
  wp_pull_exists; rename_i vecs; wp_focus_pure; intro hvecs_len
  nth_rw 1 [stackAt_dropStackPoly64_split s0.sp]; cells_unfold; wp_pull_exists
  rename_i v_fp v_lr v_x20 v_x19
  apply sepWP_seq_lscl hcl (mid := lsmpl.base 279); wp_steps
  apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs); intro hcl_c1
  have hct1_raw := drop_unchunked_ct1_sent_local2_mem_on
    (callerProg := lsProg_273 (Rust.withPanics ext)) (F := F) hdealloc hcl_c1
  dsimp only [lsProg_273, withMemEq, dropUnchunkedCt1SentSpec, unchunkedCt1SentSize, dropGluePoly16Stack, BitVec.ofNat_eq_ofNat] at hct1_raw
  apply sepWP_seq_lscl hcl_c1 (mid := lsmpl.base 264)
  wp_call hct1_raw ⟨a + 8#64, st.uc⟩
  wp_steps
  apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs); intro hcl_c2
  have hpt16_raw := drop_glue_sorted_set_pt16_mem_on
    (callerProg := lsProg_273 (Rust.withPanics ext)) hdealloc hcl_c2
  dsimp only [lsProg_273, withMemEq, dropGlueSortedSetPt16Spec, polyArrayBytes, dropGluePoly16Stack, BitVec.ofNat_eq_ofNat] at hpt16_raw
  refine SepWP.focus_weaken
    (stack_restore_64_dropStack32 s0.sp (s0.readReg64 .fp) (s0.readReg64 .lr) (s0.readReg64 .x19) v_x19)
    (by sep_focus) ?_
  refine SepWP.focus_weaken (Entails.of_eq (stackAt_dropStackPoly64_split_bottom s0.sp)) (by sep_focus) ?_
  wp_call hpt16_raw ⟨a + 136#64, vecs⟩
  refine SepWP.focus_weaken (Entails.of_eq (stackAt_dropStackPoly64_split_bottom s0.sp).symm) (by sep_focus) ?_
  refine SepWP.focus_weaken (polyDecoder_post_join (a + 136#64)) (by sep_focus) ?_
  have hjoin528 : memRegion (a + 8#64) 128 ∗ memRegion (a + 136#64) polyDecoderSize ⊢
      memRegion (a + 8#64) 528 := by
    have h136 : (a + 8#64) + 128#64 = a + 136#64 := BitVec.add_assoc a 8#64 128#64
    rw [← h136, show (528 : Nat) = 128 + polyDecoderSize from rfl,
        ProofLib.memRegion_split (a + 8#64) 128 polyDecoderSize (by decide)]
    exact Entails.refl _
  refine SepWP.focus_weaken hjoin528 (by sep_focus) ?_
  refine SepWP.focus_weaken (tag_and_two_regions_entails_928 a 11#64 528 392 536#64
    (BitVec.add_assoc a 8#64 528#64).symm rfl) (by sep_focus) ?_; wp_done

private theorem drop_chunked_states_local2_ct1Sampled_cl [LibsignalPlacement]
    {A : RustAlloc} {F : ShaCompress} {ext : String → Option (State → State)}
    (hdealloc : HookSat (Rust.withPanics ext) spqrRustDeallocSym (rustDeallocSpec A))
    (st : Chunked.SendCt.Ct1Sampled spqrPolyApi (spqrAuthApi F)) :
    subroutine_ok (lsProg_273 (Rust.withPanics ext)) (blkPl_273).base
      (withLsCodeLoaded lsmpl (dropChunkedStatesLocal2PlacedVariantSpec A (.ct1Sampled st))) := by
  change subroutine_ok ((blkPC_273).rebase (blkPl_273).base (Rust.withPanics ext)) (blkPl_273).base _
  apply subroutine_ok_withLsCodeLoaded_intro; intro m hcl
  dsimp only [withMemEq, dropChunkedStatesLocal2PlacedVariantSpec, chunkedStatesAt,
    chunkedCt1SampledAt, chunkedStatesLocal2JumpTablePlacedAt, chunkedStatesLocal2JumpTableSym,
    chunkedStatesLocal2JumpTableBytes, chunkedStatesSize, unchunkedCt1SentSize, polyArrayBytes,
    dropGluePoly16Stack, spqrPolyApi, BitVec.ofNat_eq_ofNat] at ⊢
  wp_init a s0; have hm : s0.mem = m := (by assumption); subst hm
  have hfsp_align : ((s0.sp - 32#64) &&& 15#64 == 0#64) = true :=
    spAligned_sub s0.sp 32#64 (by assumption) (by decide)
  refine SepWP.focus_weaken (polyEncoderAt_expose_tag A a st.sending_ct1) (by sep_focus) ?_
  wp_pull_exists; rename_i w; wp_focus_pure; intro hw
  nth_rw 1 [stackAt_dropStackPoly64_split s0.sp]; cells_unfold; wp_pull_exists
  rename_i v_fp v_lr v_x20 v_x19
  refine seq_clean_lscl hcl (mid := (blkPl_273).base + 188#64)
    (P_mid := (polyEncoderAt A a st.sending_ct1 ∗
      unchunkedCt1SentAt A (a + 400#64) st.uc ∗
      polyDecoderAt A (a + 528#64) st.receiving_ek) ∗
      chunkedStatesLocal2JumpTablePlacedExpanded ∗
      A.pool ∗ stackAt (s0.sp - 32#64) dropStack32 ∗ SavedFrame32 s0 v_x19)
    (Q := fun sm => Saved32x19Preserved s0 sm (s0.sp - 32#64) ∧ sm.readReg64 .x19 = a) ?_ ?_
  · rcases hw with rfl | rfl
    · wp_steps
      refine SepWP.focus_weaken (polyEncoderAt_unexpose_tag A a 0#64 st.sending_ct1) (by sep_focus) ?_
      refine align_pre (by simp only [Reg.fp, Reg.lr, Reg.x19, chunkedStatesLocal2JumpTablePlacedExpanded, chunkedStatesLocal2JumpTableSym]; ac_rfl) ?_; wp_done
    · wp_steps
      refine SepWP.focus_weaken (polyEncoderAt_unexpose_tag A a 1#64 st.sending_ct1) (by sep_focus) ?_
      refine align_pre (by simp only [Reg.fp, Reg.lr, Reg.x19, chunkedStatesLocal2JumpTablePlacedExpanded, chunkedStatesLocal2JumpTableSym]; ac_rfl) ?_; wp_done
  · intro s1 hpc1 hrun1 hcl1 ⟨⟨hx20_1, hx21_1, hx22_1, hx23_1, hx24_1, hx25_1, hx26_1, hx27_1, hx28_1, hsp_1, htrace_1, hvregs_1⟩, hx19_1⟩
    dsimp only [chunkedStatesLocal2JumpTablePlacedExpanded, chunkedStatesLocal2JumpTableSym]
    refine SepWP.focus_weaken (polyEncoderAt_entails_tag_vecs_tail A a st.sending_ct1) (by sep_focus) ?_
    wp_pull_exists; rename_i tag enc_vecs; wp_focus_pure; intro henc_len
    refine SepWP.focus_weaken (polyDecoderAt_entails_vecs_tail A (a + 528#64) st.receiving_ek) (by sep_focus) ?_
    wp_pull_exists; rename_i dec_vecs; wp_focus_pure; intro hdec_len
    apply sepWP_seq_lscl hcl1 (mid := lsmpl.base 279); wp_steps
    apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs); intro hcl_c1
    have hct1_raw := drop_unchunked_ct1_sent_local2_mem_on
      (callerProg := lsProg_273 (Rust.withPanics ext)) (F := F) hdealloc hcl_c1
    dsimp only [lsProg_273, withMemEq, dropUnchunkedCt1SentSpec, unchunkedCt1SentSize, dropGluePoly16Stack, BitVec.ofNat_eq_ofNat] at hct1_raw
    apply sepWP_seq_lscl hcl_c1 (mid := lsmpl.base 265)
    wp_call hct1_raw ⟨a + 400#64, st.uc⟩
    wp_steps
    apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs); intro hcl_c2
    have hpoly16_raw := drop_glue_poly16_mem_on
      (callerProg := lsProg_273 (Rust.withPanics ext)) hdealloc hcl_c2
    dsimp only [lsProg_273, withMemEq, dropGluePoly16Spec, polyArrayBytes, dropGluePoly16Stack, BitVec.ofNat_eq_ofNat] at hpoly16_raw
    apply sepWP_seq_lscl hcl_c2 (mid := lsmpl.base 264)
    wp_call hpoly16_raw ⟨a + 8#64, enc_vecs⟩
    wp_steps
    apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs); intro hcl_c3
    have hpt16_raw := drop_glue_sorted_set_pt16_mem_on
      (callerProg := lsProg_273 (Rust.withPanics ext)) hdealloc hcl_c3
    dsimp only [lsProg_273, withMemEq, dropGlueSortedSetPt16Spec, polyArrayBytes, dropGluePoly16Stack, BitVec.ofNat_eq_ofNat] at hpt16_raw
    conv => arg 4; simp only [hsp_1, *]
    refine SepWP.focus_weaken
      (stack_restore_64_dropStack32 s0.sp (s0.readReg64 .fp) (s0.readReg64 .lr) (s0.readReg64 .x19) v_x19)
      (by sep_focus) ?_
    refine SepWP.focus_weaken (Entails.of_eq (stackAt_dropStackPoly64_split_bottom s0.sp)) (by sep_focus) ?_
    wp_call hpt16_raw ⟨a + 528#64, dec_vecs⟩
    refine SepWP.focus_weaken (Entails.of_eq (stackAt_dropStackPoly64_split_bottom s0.sp).symm) (by sep_focus) ?_
    refine SepWP.focus_weaken (polyDecoder_post_join (a + 528#64)) (by sep_focus) ?_
    refine SepWP.focus_weaken (chunked_400_join a tag 128 528 rfl (by decide)) (by sep_focus) ?_
    have hjoin928 : memRegion a 528 ∗ memRegion (a + 528#64) polyDecoderSize ⊢ memRegion a 928 := by
      rw [show (928 : Nat) = 528 + polyDecoderSize from rfl,
          ProofLib.memRegion_split a 528 polyDecoderSize (by decide)]
      exact Entails.refl _
    refine SepWP.focus_weaken hjoin928 (by sep_focus) ?_; wp_done

private theorem drop_chunked_states_local2_ct2Sampled_cl [LibsignalPlacement]
    {A : RustAlloc} {F : ShaCompress} {ext : String → Option (State → State)}
    (hdealloc : HookSat (Rust.withPanics ext) spqrRustDeallocSym (rustDeallocSpec A))
    (st : Chunked.SendCt.Ct2Sampled spqrPolyApi (spqrAuthApi F)) :
    subroutine_ok (lsProg_273 (Rust.withPanics ext)) (blkPl_273).base
      (withLsCodeLoaded lsmpl (dropChunkedStatesLocal2PlacedVariantSpec A (.ct2Sampled st))) := by
  change subroutine_ok ((blkPC_273).rebase (blkPl_273).base (Rust.withPanics ext)) (blkPl_273).base _
  apply subroutine_ok_withLsCodeLoaded_intro; intro m hcl
  have hdealloc_raw : subroutine_ok ((blkPC_273).rebase (blkPl_273).base (Rust.withPanics ext))
      (lsρ spqrRustDeallocSym) (rustDeallocSpec A) := spqr_hook_ok_of_mem hdealloc
  simp only [rustDeallocSpec] at hdealloc_raw
  dsimp only [withMemEq, dropChunkedStatesLocal2PlacedVariantSpec, chunkedStatesAt,
    chunkedCt2SampledAt, chunkedStatesLocal2JumpTablePlacedAt, chunkedStatesLocal2JumpTableSym,
    chunkedStatesLocal2JumpTableBytes, chunkedStatesSize, polyArrayBytes, dropGluePoly16Stack,
    spqrPolyApi, BitVec.ofNat_eq_ofNat] at hdealloc_raw ⊢
  wp_init a s0; have hm : s0.mem = m := (by assumption); subst hm
  have hfsp_align : ((s0.sp - 32#64) &&& 15#64 == 0#64) = true :=
    spAligned_sub s0.sp 32#64 (by assumption) (by decide)
  refine SepWP.focus_weaken (unchunkedCt2Sent408_entails_dealloc A a st.uc) (by sep_focus) ?_
  wp_pull_exists; rename_i g
  refine SepWP.focus_weaken (polyEncoder8_entails_tag_vecs_tail A a st.sending_ct2) (by sep_focus) ?_
  wp_pull_exists; rename_i tag vecs; wp_focus_pure; intro hvecs_len
  dsimp only [twoVec408HeadersAt, vecCapPtrDealloc]
  nth_rw 1 [stackAt_dropStackPoly64_split s0.sp]; cells_unfold; wp_pull_exists
  rename_i v_fp v_lr v_x20 v_x19
  have hsplit32 := stackAt_dropStack32_split_sub32 s0.sp
  refine SepWP.focus_weaken (Entails.of_eq hsplit32) (by sep_focus) ?_
  refine seq_clean_lscl hcl (mid := (blkPl_273).base + 372#64)
    (P_mid := ((a ↦₆₄ 12#64) ∗
      ((a + 8#64) ↦₆₄ tag) ∗ vecGF16ListOf A (a + 16#64) vecs ∗ memRegion (a + 400#64) 8 ∗
      ((a + 408#64) ↦₆₄ g.v1.cap) ∗ ((a + 416#64) ↦₆₄ g.v1.ptr) ∗ memRegion (a + 424#64) 8 ∗
      ((a + 432#64) ↦₆₄ g.v2.cap) ∗ ((a + 440#64) ↦₆₄ g.v2.ptr) ∗ memRegion (a + 448#64) 16 ∗
      (if (g.v2.cap == 0#64) = true then emp
       else A.live g.v2.ptr g.v2.cap.toNat 1 ∗ memRegion g.v2.ptr g.v2.cap.toNat) ∗
      memRegion (a + 464#64) 464) ∗
      chunkedStatesLocal2JumpTablePlacedExpanded ∗
      A.pool ∗ (memRegion (s0.sp - 4160#64) 32 ∗ stackAt (s0.sp - 32#64) allocHookStack) ∗
      SavedFrame32 s0 v_x19)
    (Q := fun sm => Saved32x19Preserved s0 sm (s0.sp - 32#64) ∧ sm.readReg64 .x19 = a) ?_ ?_
  · by_cases hc1 : (g.v1.cap == 0#64) = true <;>
      simp only [hc1, Bool.false_eq_true, ↓reduceIte, emp_sepConj, sepConj_emp]
    · wp_steps
      refine align_pre (by simp only [Reg.fp, Reg.lr, Reg.x19, chunkedStatesLocal2JumpTablePlacedExpanded, chunkedStatesLocal2JumpTableSym]; ac_rfl) ?_; wp_done
    · wp_steps; wp_apply
      refine align_pre (by simp only [Reg.fp, Reg.lr, Reg.x19, chunkedStatesLocal2JumpTablePlacedExpanded, chunkedStatesLocal2JumpTableSym]; ac_rfl) ?_; wp_done
  · intro s1 hpc1 hrun1 hcl1 ⟨⟨hx20_1, hx21_1, hx22_1, hx23_1, hx24_1, hx25_1, hx26_1, hx27_1, hx28_1, hsp_1, htrace_1, hvregs_1⟩, hx19_1⟩
    refine seq_clean_lscl hcl1 (mid := (blkPl_273).base + 392#64)
      (P_mid := ((a ↦₆₄ 12#64) ∗
        ((a + 8#64) ↦₆₄ tag) ∗ vecGF16ListOf A (a + 16#64) vecs ∗ memRegion (a + 400#64) 8 ∗
        memRegion (a + 408#64) 56 ∗ memRegion (a + 464#64) 464) ∗
        chunkedStatesLocal2JumpTablePlacedExpanded ∗
        A.pool ∗ stackAt (s0.sp - 32#64) dropStack32 ∗ SavedFrame32 s0 v_x19)
      (Q := fun sm => Saved32x19Preserved s0 sm (s0.sp - 32#64) ∧ sm.readReg64 .x19 = a) ?_ ?_
    · have hhdr56 := twoVec408HeadersAt_entails_memRegion_56 a g
      dsimp only [twoVec408HeadersAt] at hhdr56
      by_cases hc2 : (g.v2.cap == 0#64) = true <;>
        simp only [hc2, Bool.false_eq_true, ↓reduceIte, emp_sepConj, sepConj_emp]
      · wp_steps
        refine SepWP.focus_weaken hhdr56 (by sep_focus) ?_
        refine SepWP.focus_weaken (Entails.of_eq hsplit32.symm) (by sep_focus) ?_
        refine align_pre (by simp only [Reg.fp, Reg.lr, Reg.x19, chunkedStatesLocal2JumpTablePlacedExpanded, chunkedStatesLocal2JumpTableSym]; ac_rfl) ?_; wp_done
      · wp_steps; wp_apply
        refine SepWP.focus_weaken hhdr56 (by sep_focus) ?_
        have hsp_eq : stackAt s1.sp allocHookStack = stackAt (s0.sp - 32#64) allocHookStack := by rw [hsp_1]
        refine SepWP.focus_weaken (Entails.of_eq hsp_eq) (by sep_focus) ?_
        refine SepWP.focus_weaken (Entails.of_eq hsplit32.symm) (by sep_focus) ?_
        refine align_pre (by simp only [Reg.fp, Reg.lr, Reg.x19, chunkedStatesLocal2JumpTablePlacedExpanded, chunkedStatesLocal2JumpTableSym]; ac_rfl) ?_; wp_done
    · intro s2 hpc2 hrun2 hcl2 ⟨⟨hx20_2, hx21_2, hx22_2, hx23_2, hx24_2, hx25_2, hx26_2, hx27_2, hx28_2, hsp_2, htrace_2, hvregs_2⟩, hx19_2⟩
      dsimp only [chunkedStatesLocal2JumpTablePlacedExpanded, chunkedStatesLocal2JumpTableSym]
      apply sepWP_seq_lscl hcl2 (mid := lsmpl.base 265); wp_steps
      apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs); intro hcl_call
      have hpoly16_raw := drop_glue_poly16_mem_on
        (callerProg := lsProg_273 (Rust.withPanics ext)) hdealloc hcl_call
      dsimp only [lsProg_273, withMemEq, dropGluePoly16Spec, polyArrayBytes, dropGluePoly16Stack, BitVec.ofNat_eq_ofNat] at hpoly16_raw
      refine SepWP.focus_weaken
        (stack_restore_64_dropStack32 s0.sp (s0.readReg64 .fp) (s0.readReg64 .lr) (s0.readReg64 .x19) v_x19)
        (by sep_focus) ?_
      refine SepWP.focus_weaken (Entails.of_eq (stackAt_dropStackPoly64_split_bottom s0.sp)) (by sep_focus) ?_
      wp_call hpoly16_raw ⟨a + 16#64, vecs⟩
      refine SepWP.focus_weaken (Entails.of_eq (stackAt_dropStackPoly64_split_bottom s0.sp).symm) (by sep_focus) ?_
      refine SepWP.focus_weaken (polyEncoder_local2_8_post_join a tag) (by sep_focus) ?_
      have hjoin456 : memRegion (a + 8#64) 400 ∗ memRegion (a + 408#64) 56 ⊢
          memRegion (a + 8#64) 456 := by
        have h408 : (a + 8#64) + 400#64 = a + 408#64 := BitVec.add_assoc a 8#64 400#64
        rw [← h408, show (456 : Nat) = 400 + 56 from rfl,
            ProofLib.memRegion_split (a + 8#64) 400 56 (by decide)]
        exact Entails.refl _
      refine SepWP.focus_weaken hjoin456 (by sep_focus) ?_
      refine SepWP.focus_weaken (tag_and_two_regions_entails_928 a 12#64 456 464 464#64
        (BitVec.add_assoc a 8#64 456#64).symm rfl) (by sep_focus) ?_; wp_done

theorem drop_chunked_states_local2_cl_placed_ok [LibsignalPlacement]
    {A : RustAlloc} {F : ShaCompress} {ext : String → Option (State → State)}
    (hdealloc : HookSat (Rust.withPanics ext) spqrRustDeallocSym (rustDeallocSpec A)) :
    subroutine_ok (lsProg_273 (Rust.withPanics ext)) (lsmpl.base 273)
      (withLsCodeLoaded lsmpl (dropChunkedStatesLocal2PlacedSpec A F)) := by
  rw [← ls_blockPlacement_base (i := 273)]
  refine subroutine_ok_outcome_intro fun ⟨a, st⟩ R s0 hpc hrun hpre hsp => ?_
  cases st with
  | keysUnsampled s =>
    exact (drop_chunked_states_local2_keysUnsampled_cl hdealloc s).mono_outcome a R s0 hpc hrun hpre hsp fun _ hout => hout
  | keysSampled s =>
    exact (drop_chunked_states_local2_keysSampled_cl hdealloc s).mono_outcome a R s0 hpc hrun hpre hsp fun _ hout => hout
  | headerSent s =>
    exact (drop_chunked_states_local2_headerSent_cl hdealloc s).mono_outcome a R s0 hpc hrun hpre hsp fun _ hout => hout
  | ct1Received s =>
    exact (drop_chunked_states_local2_ct1Received_cl hdealloc s).mono_outcome a R s0 hpc hrun hpre hsp fun _ hout => hout
  | ekSentCt1Received s =>
    exact (drop_chunked_states_local2_ekSentCt1Received_cl hdealloc s).mono_outcome a R s0 hpc hrun hpre hsp fun _ hout => hout
  | noHeaderReceived s =>
    exact (drop_chunked_states_local2_noHeaderReceived_cl hdealloc s).mono_outcome a R s0 hpc hrun hpre hsp fun _ hout => hout
  | headerReceived s =>
    exact (drop_chunked_states_local2_headerReceived_cl hdealloc s).mono_outcome a R s0 hpc hrun hpre hsp fun _ hout => hout
  | ct1Sampled s =>
    exact (drop_chunked_states_local2_ct1Sampled_cl hdealloc s).mono_outcome a R s0 hpc hrun hpre hsp fun _ hout => hout
  | ekReceivedCt1Sampled s =>
    exact (drop_chunked_states_local2_ekReceivedCt1Sampled_cl hdealloc s).mono_outcome a R s0 hpc hrun hpre hsp fun _ hout => hout
  | ct1Acknowledged s =>
    exact (drop_chunked_states_local2_ct1Acknowledged_cl hdealloc s).mono_outcome a R s0 hpc hrun hpre hsp fun _ hout => hout
  | ct2Sampled s =>
    exact (drop_chunked_states_local2_ct2Sampled_cl hdealloc s).mono_outcome a R s0 hpc hrun hpre hsp fun _ hout => hout

theorem drop_chunked_states_local2_cl_blockProgram [LibsignalPlacement]
    {A : RustAlloc} {F : ShaCompress} {ext : String → Option (State → State)}
    (hdealloc : HookSat (Rust.withPanics ext) spqrRustDeallocSym (rustDeallocSpec A)) :
    subroutine_ok (libsignalSessionLib.blockProgram lsmpl 273 (Rust.withPanics ext)) (lsmpl.base 273)
      (withLsCodeLoaded lsmpl (dropChunkedStatesLocal2PlacedSpec A F)) :=
  ls_to_blockProgram (drop_chunked_states_local2_cl_placed_ok hdealloc)

end LibsignalBinary.Proofs.SpqrV1.Drop.ChainStatesClPlaced
