/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SpqrV1.Drop.ProtoChain
public import LibsignalBinary.Proofs.SpqrV1.Drop.ProtoChunked1
public import LibsignalBinary.Proofs.SpqrV1.Drop.ProtoChunked2
public import LibsignalBinary.Proofs.SpqrV1.Drop.Unchunked
public import LibsignalBinary.Proofs.SpqrV1.States.Recv.DropChunkedClPlaced
import LibsignalBinary.Proofs.SpqrV1.Alloc.SpqrAllocCodeSym
import ProofLib.SepLogic.WP.Apply
import ProofLib.SepLogic.WPp
import GeneratedLean.LibsignalSessionObj

/-!
# Code-Loaded `[LibsignalPlacement]` Drop Glue for Protobuf Chunked and Leaf Slice Types

Proves `withLsCodeLoaded lsmpl` subroutine contracts from `rustDeallocSpec A` for Blocks `281`
(`HeaderSent`), `282` (`Ct1Received`), `283` (`HeaderReceived`), `284` (`NoHeaderReceived`),
`285` (`EkSentCt1Received`), `286` (`unchunked::Ct1SentEkReceived`), and `288` (`[chain::Epoch]`).
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 400000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false

namespace LibsignalBinary.Proofs.SpqrV1.Drop.ProtoChunkedClPlaced

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

attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero

/-! ## `withLsCodeLoaded` Helpers and Share-Vector Deallocation Loop Macros -/

theorem subroutine_ok_withLsCodeLoaded_intro [LibsignalPlacement] {α : Type}
    {prog : Program} {entry : BitVec 64} {spec : Spec α}
    (h : ∀ m : Memory, LibsignalCodeLoaded lsmpl m →
      subroutine_ok prog entry (withMemEq m spec)) :
    subroutine_ok prog entry (withLsCodeLoaded lsmpl spec) := by
  refine subroutine_ok_outcome_intro fun x R s0 hpc hrun hpre halign => ?_
  obtain ⟨hcl, hpre'⟩ := extract_withLsCodeLoaded hpre
  refine (h s0.mem hcl).mono_outcome x R s0 hpc hrun ?_ halign fun _ hout => hout
  dsimp only [withMemEq]
  rw [sepConj_assoc, sepConj_left_comm, satisfies_pure_sepConj]
  exact ⟨rfl, hpre'⟩

theorem seq_clean_lscl [LibsignalPlacement] {prog : Program} {mid target : BitVec 64}
    {s : State} {P P_mid : SepProp} {Q : State → Prop} {post : State → SepProp → Prop}
    (hcl : LibsignalCodeLoaded lsmpl s.mem)
    (h1 : SepWP prog mid s P (fun sm Pm => (Pm ⊢ P_mid) ∧ Q sm))
    (h2 : ∀ sm : State, sm.pc = mid → sm.status = .Running →
      LibsignalCodeLoaded lsmpl sm.mem → Q sm → SepWP prog target sm P_mid post) :
    SepWP prog target s P post :=
  sepWP_seq_lscl hcl (SepWP.mono h1 fun sm Pm hpc hrun ⟨hPm, hQ⟩ hcl' =>
    SepWP.weaken_pre hPm (h2 sm hpc hrun hcl' hQ))

theorem ls_to_blockProgram [LibsignalPlacement] {α : Type}
    {calleeProg : Program} {j : Nat} {H : LibsignalHooks}
    [hcallee : IsLsBlockProg calleeProg j H] {spec : Spec α}
    (h : subroutine_ok calleeProg (lsmpl.base j) spec) :
    subroutine_ok (libsignalSessionLib.blockProgram lsmpl j H) (lsmpl.base j) spec :=
  hcallee.eq_blockProgram ▸ h

/-! ## Leaf Single-Block Wrappers (`283, 284, 285, 286, 288`) -/

theorem drop_proto_chunked_header_received_cl_placed_ok [LibsignalPlacement] {A : RustAlloc}
    {ext : String → Option (State → State)}
    (hdealloc : HookSat (Rust.withPanics ext) spqrRustDeallocSym (rustDeallocSpec A)) :
    subroutine_ok (lsProg_283 (Rust.withPanics ext)) (lsmpl.base 283)
      (withLsCodeLoaded lsmpl (dropProtoChunkedHeaderReceivedSpec A)) := by
  rw [← ls_blockPlacement_base (i := 283)]
  exact subroutine_ok_withLsCodeLoaded_of_plain
    (drop_proto_chunked_header_received_placed_ok (spqr_hook_ok_of_mem hdealloc))

theorem drop_proto_chunked_header_received_mem_on [LibsignalPlacement] {A : RustAlloc}
    {callerProg : Program} {idx : Nat} {ext : String → Option (State → State)}
    [IsLsBlockProg callerProg idx (Rust.withPanics ext)] {m : Memory}
    (hdealloc : HookSat (Rust.withPanics ext) spqrRustDeallocSym (rustDeallocSpec A))
    (hcl : LibsignalCodeLoaded lsmpl m) (hidx : idx < 619 := by decide) :
    subroutine_ok callerProg (lsmpl.base 283)
      (withMemEq m (dropProtoChunkedHeaderReceivedSpec A)) :=
  lscall_blk_cl (drop_proto_chunked_header_received_cl_placed_ok hdealloc) hcl hidx

theorem drop_proto_chunked_no_header_received_cl_placed_ok [LibsignalPlacement] {A : RustAlloc}
    {ext : String → Option (State → State)}
    (hdealloc : HookSat (Rust.withPanics ext) spqrRustDeallocSym (rustDeallocSpec A)) :
    subroutine_ok (lsProg_284 (Rust.withPanics ext)) (lsmpl.base 284)
      (withLsCodeLoaded lsmpl (dropProtoChunkedNoHeaderReceivedSpec A)) := by
  rw [← ls_blockPlacement_base (i := 284)]
  exact subroutine_ok_withLsCodeLoaded_of_plain
    (drop_proto_chunked_no_header_received_placed_ok (spqr_hook_ok_of_mem hdealloc))

theorem drop_proto_chunked_no_header_received_mem_on [LibsignalPlacement] {A : RustAlloc}
    {callerProg : Program} {idx : Nat} {ext : String → Option (State → State)}
    [IsLsBlockProg callerProg idx (Rust.withPanics ext)] {m : Memory}
    (hdealloc : HookSat (Rust.withPanics ext) spqrRustDeallocSym (rustDeallocSpec A))
    (hcl : LibsignalCodeLoaded lsmpl m) (hidx : idx < 619 := by decide) :
    subroutine_ok callerProg (lsmpl.base 284)
      (withMemEq m (dropProtoChunkedNoHeaderReceivedSpec A)) :=
  lscall_blk_cl (drop_proto_chunked_no_header_received_cl_placed_ok hdealloc) hcl hidx

theorem drop_proto_chunked_ek_sent_ct1_received_cl_placed_ok [LibsignalPlacement] {A : RustAlloc}
    {ext : String → Option (State → State)}
    (hdealloc : HookSat (Rust.withPanics ext) spqrRustDeallocSym (rustDeallocSpec A)) :
    subroutine_ok (lsProg_285 (Rust.withPanics ext)) (lsmpl.base 285)
      (withLsCodeLoaded lsmpl (dropProtoChunkedEkSentCt1ReceivedSpec A)) := by
  rw [← ls_blockPlacement_base (i := 285)]
  exact subroutine_ok_withLsCodeLoaded_of_plain
    (drop_proto_chunked_ek_sent_ct1_received_placed_ok (spqr_hook_ok_of_mem hdealloc))

theorem drop_proto_chunked_ek_sent_ct1_received_mem_on [LibsignalPlacement] {A : RustAlloc}
    {callerProg : Program} {idx : Nat} {ext : String → Option (State → State)}
    [IsLsBlockProg callerProg idx (Rust.withPanics ext)] {m : Memory}
    (hdealloc : HookSat (Rust.withPanics ext) spqrRustDeallocSym (rustDeallocSpec A))
    (hcl : LibsignalCodeLoaded lsmpl m) (hidx : idx < 619 := by decide) :
    subroutine_ok callerProg (lsmpl.base 285)
      (withMemEq m (dropProtoChunkedEkSentCt1ReceivedSpec A)) :=
  lscall_blk_cl (drop_proto_chunked_ek_sent_ct1_received_cl_placed_ok hdealloc) hcl hidx

theorem drop_proto_unchunked_ct1_sent_ek_received_cl_placed_ok [LibsignalPlacement] {A : RustAlloc}
    {ext : String → Option (State → State)}
    (hdealloc : HookSat (Rust.withPanics ext) spqrRustDeallocSym (rustDeallocSpec A)) :
    subroutine_ok (lsProg_286 (Rust.withPanics ext)) (lsmpl.base 286)
      (withLsCodeLoaded lsmpl (dropProtoUnchunkedCt1SentEkReceivedSpec A)) := by
  rw [← ls_blockPlacement_base (i := 286)]
  exact subroutine_ok_withLsCodeLoaded_of_plain
    (drop_proto_unchunked_ct1_sent_ek_received_placed_ok (spqr_hook_ok_of_mem hdealloc))

theorem drop_proto_unchunked_ct1_sent_ek_received_mem_on [LibsignalPlacement] {A : RustAlloc}
    {callerProg : Program} {idx : Nat} {ext : String → Option (State → State)}
    [IsLsBlockProg callerProg idx (Rust.withPanics ext)] {m : Memory}
    (hdealloc : HookSat (Rust.withPanics ext) spqrRustDeallocSym (rustDeallocSpec A))
    (hcl : LibsignalCodeLoaded lsmpl m) (hidx : idx < 619 := by decide) :
    subroutine_ok callerProg (lsmpl.base 286)
      (withMemEq m (dropProtoUnchunkedCt1SentEkReceivedSpec A)) :=
  lscall_blk_cl (drop_proto_unchunked_ct1_sent_ek_received_cl_placed_ok hdealloc) hcl hidx

theorem drop_proto_epoch_slice_cl_placed_ok [LibsignalPlacement] {A : RustAlloc}
    {ext : String → Option (State → State)}
    (hdealloc : HookSat (Rust.withPanics ext) spqrRustDeallocSym (rustDeallocSpec A)) :
    subroutine_ok (Blk337_338.lsProg_288 (Rust.withPanics ext)) (lsmpl.base 288)
      (withLsCodeLoaded lsmpl (dropProtoEpochSliceSpec A)) := by
  rw [← ls_blockPlacement_base (i := 288)]
  exact subroutine_ok_withLsCodeLoaded_of_plain
    (CryptoVerification.SpqrV1.Drop.drop_proto_epoch_slice_placed_ok (spqr_hook_ok_of_mem hdealloc))

theorem drop_proto_epoch_slice_mem_on [LibsignalPlacement] {A : RustAlloc}
    {callerProg : Program} {idx : Nat} {ext : String → Option (State → State)}
    [IsLsBlockProg callerProg idx (Rust.withPanics ext)] {m : Memory}
    (hdealloc : HookSat (Rust.withPanics ext) spqrRustDeallocSym (rustDeallocSpec A))
    (hcl : LibsignalCodeLoaded lsmpl m) (hidx : idx < 619 := by decide) :
    subroutine_ok callerProg (lsmpl.base 288)
      (withMemEq m (dropProtoEpochSliceSpec A)) :=
  lscall_blk_cl (drop_proto_epoch_slice_cl_placed_ok hdealloc) hcl hidx

/-! ## Block `282`: `drop_glue::<proto::pq_ratchet::v1_state::chunked::Ct1Received>` -/

theorem drop_proto_chunked_ct1_received_cl_placed_ok [LibsignalPlacement] {A : RustAlloc}
    {ext : String → Option (State → State)}
    (hdealloc : HookSat (Rust.withPanics ext) spqrRustDeallocSym (rustDeallocSpec A)) :
    subroutine_ok (lsProg_282 (Rust.withPanics ext)) (lsmpl.base 282)
      (withLsCodeLoaded lsmpl (dropProtoChunkedCt1ReceivedSpec A)) := by
  rw [← ls_blockPlacement_base (i := 282)]
  change subroutine_ok ((blkPC_282).rebase (blkPl_282).base (Rust.withPanics ext)) (blkPl_282).base _
  apply subroutine_ok_withLsCodeLoaded_intro; intro m hcl
  have hdealloc_raw : subroutine_ok (lsProg_282 (Rust.withPanics ext))
      (lsρ spqrRustDeallocSym) (rustDeallocSpec A) := spqr_hook_ok_of_mem hdealloc
  simp only [rustDeallocSpec] at hdealloc_raw
  dsimp only [lsProg_282, withMemEq, dropProtoChunkedCt1ReceivedSpec, protoChunkedCt1ReceivedSize] at hdealloc_raw ⊢
  wp_init x s0
  rcases x with ⟨a, st⟩
  have hx0 : s0.readReg64 .x0 = a := by assumption
  have hm : s0.mem = m := by assumption
  subst hm
  dsimp only [DropProtoChunkedCt1ReceivedGhost.a, DropProtoChunkedCt1ReceivedGhost.st,
    protoChunkedCt1ReceivedAt] at *
  have hfsp_align : ((s0.sp - 32#64) &&& 15#64 == 0#64) = true :=
    spAligned_sub s0.sp 32#64 (by assumption) (by decide)
  have hsub_4144 : (s0.sp - 32#64) - 4112#64 = s0.sp - 4144#64 := by bv_omega
  nth_rw 1 [stackAt_dropStack48_split32 s0.sp]
  nth_rw 1 [stackAt_allocHook16_split_bottom (s0.sp - 32#64)]
  rw [hsub_4144]
  cells_unfold
  wp_pull_exists
  rename_i fp_old lr_old x20_old x19_old
  refine seq_clean_lscl hcl (mid := (blkPl_282).base + 116#64)
    (P_mid := (memRegion a 104 ∗
      optProtoPolynomialEncoderAt A (a + 104#64) (st.sendingEk.map pbToProtoPolyEncoder)) ∗
      A.pool ∗
      (memRegion (s0.sp - 4144#64) 16 ∗ stackAt (s0.sp - 32#64) allocHookStack) ∗
      (((s0.sp - 32#64) ↦₆₄ s0.readReg64 .fp) ∗ ((s0.sp - 24#64) ↦₆₄ s0.readReg64 .lr) ∗
       ((s0.sp - 16#64) ↦₆₄ s0.readReg64 .x20) ∗ ((s0.sp - 8#64) ↦₆₄ s0.readReg64 .x19)))
    (Q := fun sm => Saved32x20Preserved s0 sm (s0.sp - 32#64) ∧ sm.readReg64 .x19 = a)
    ?_ ?_
  · cases huc : st.uc with
    | none =>
      rw [optProtoUnchunkedEkSentCt1ReceivedAt_none]
      wp_steps
      refine SepWP.focus_weaken
        (optProtoUnchunked2Vec_none_entails_memRegion_104 a)
        (by sep_focus) ?_
      refine align_pre (by dsimp only [Reg.fp, Reg.lr, Reg.x19, Reg.x20]; ac_rfl) ?_; wp_done
    | some u =>
      rw [optProtoUnchunkedEkSentCt1ReceivedAt_some]
      refine SepWP.weaken_pre
        (sepConj_mono_left (protoUnchunkedEkSentCt1ReceivedAt_entails_dealloc A a u)) ?_
      wp_pull_exists; rename_i g
      wp_focus_pure; intro hcap1_lt
      have hne_none1 := cap_add_one_beq_zero_false hcap1_lt
      refine seq_clean (mid := (blkPl_282).base + 76#64)
        (P_mid := ((protoUnchunked2VecHeadersAt a g ∗
          memRegion (a + 48#64) 48 ∗ memRegion (a + 96#64) 8 ∗
          vecCapPtrDealloc A g.v1.cap g.v1.ptr ∗
          vecCapPtrDealloc A g.v2.cap g.v2.ptr) ∗
          optProtoPolynomialEncoderAt A (a + 104#64) (st.sendingEk.map pbToProtoPolyEncoder)) ∗
          A.pool ∗
          (memRegion (s0.sp - 4144#64) 16 ∗ stackAt (s0.sp - 32#64) allocHookStack) ∗
          (((s0.sp - 32#64) ↦₆₄ s0.readReg64 .fp) ∗ ((s0.sp - 24#64) ↦₆₄ s0.readReg64 .lr) ∗
           ((s0.sp - 16#64) ↦₆₄ s0.readReg64 .x20) ∗ ((s0.sp - 8#64) ↦₆₄ s0.readReg64 .x19)))
        (Q := fun sm => Saved32x20Preserved s0 sm (s0.sp - 32#64) ∧
          sm.readReg64 .x19 = a ∧ sm.readReg64 .x20 = g.v1.cap)
        ?_ ?_
      · cases hauth : u.auth with
        | none =>
          rw [optProtoAuthenticatorAt_48_none]
          dsimp only [protoUnchunked2VecHeadersAt, twoVecHeadersAt]
          wp_steps
          refine SepWP.focus_weaken
            (optProtoAuthenticatorAt_48_none_entails_memRegion_48 A a)
            (by sep_focus) ?_
          refine align_pre (by dsimp only [Reg.fp, Reg.lr, Reg.x19, Reg.x20]; ac_rfl) ?_; wp_done
        | some auth =>
          rw [optProtoAuthenticatorAt_some]
          refine SepWP.focus_weaken
            (protoAuthenticatorAt_entails_dealloc A (a + 48#64) auth)
            (by sep_focus) ?_
          wp_pull_exists; rename_i ga
          rw [twoVecHeadersAt_48_eq]
          wp_focus_pure; intro hga_lt
          have hne_nonea := cap_add_one_beq_zero_false hga_lt
          refine seq_clean (mid := (blkPl_282).base + 56#64)
            (P_mid := ((protoUnchunked2VecHeadersAt a g ∗
              (auth48HeadersAt a ga ∗ vecCapPtrDealloc A ga.v2.cap ga.v2.ptr) ∗
              memRegion (a + 96#64) 8 ∗
              vecCapPtrDealloc A g.v1.cap g.v1.ptr ∗
              vecCapPtrDealloc A g.v2.cap g.v2.ptr) ∗
              optProtoPolynomialEncoderAt A (a + 104#64) (st.sendingEk.map pbToProtoPolyEncoder)) ∗
              A.pool ∗
              (memRegion (s0.sp - 4144#64) 16 ∗ stackAt (s0.sp - 32#64) allocHookStack) ∗
              (((s0.sp - 32#64) ↦₆₄ s0.readReg64 .fp) ∗ ((s0.sp - 24#64) ↦₆₄ s0.readReg64 .lr) ∗
               ((s0.sp - 16#64) ↦₆₄ s0.readReg64 .x20) ∗ ((s0.sp - 8#64) ↦₆₄ s0.readReg64 .x19)))
            (Q := fun sm => Saved32x20Preserved s0 sm (s0.sp - 32#64) ∧
              sm.readReg64 .x19 = a ∧ sm.readReg64 .x20 = g.v1.cap)
            ?_ ?_
          · dsimp only [protoUnchunked2VecHeadersAt, twoVecHeadersAt, auth48HeadersAt, vecCapPtrDealloc]
            by_cases hca1 : (ga.v1.cap == 0#64) = true <;>
              simp only [hca1, Bool.false_eq_true, ↓reduceIte, sepConj_emp, emp_sepConj]
            · wp_steps; refine align_pre (by dsimp only [Reg.fp, Reg.lr, Reg.x19, Reg.x20]; ac_rfl) ?_; wp_done
            · wp_steps; wp_apply; refine align_pre (by dsimp only [Reg.fp, Reg.lr, Reg.x19, Reg.x20]; ac_rfl) ?_; wp_done
          · intro sa1 hpca1 hruna1 ⟨⟨hx21_a1, hx22_a1, hx23_a1, hx24_a1, hx25_a1, hx26_a1, hx27_a1, hx28_a1, hsp_a1, htrace_a1, hvregs_a1⟩, hx19_a1, hx20_a1⟩
            dsimp only [auth48HeadersAt, vecCapPtrDealloc]
            by_cases hca2 : (ga.v2.cap == 0#64) = true <;>
              simp only [hca2, Bool.false_eq_true, ↓reduceIte, sepConj_emp, emp_sepConj]
            · wp_steps
              refine SepWP.focus_weaken (auth48HeadersAt_entails_memRegion_48 a ga) (by sep_focus) ?_
              refine align_pre (by dsimp only [Reg.fp, Reg.lr, Reg.x19, Reg.x20]; ac_rfl) ?_; wp_done
            · wp_steps; wp_apply
              refine SepWP.focus_weaken (auth48HeadersAt_entails_memRegion_48 a ga) (by sep_focus) ?_
              refine align_pre (by rw [hsp_a1]; dsimp only [Reg.fp, Reg.lr, Reg.x19, Reg.x20]; ac_rfl) ?_; wp_done
      · intro s1 hpc1 hrun1 ⟨⟨hx21_1, hx22_1, hx23_1, hx24_1, hx25_1, hx26_1, hx27_1, hx28_1, hsp_1, htrace_1, hvregs_1⟩, hx19_1, hx20_1⟩
        refine seq_clean (mid := (blkPl_282).base + 96#64)
          (P_mid := ((protoUnchunked2VecHeadersAt a g ∗
            memRegion (a + 48#64) 48 ∗ memRegion (a + 96#64) 8 ∗
            vecCapPtrDealloc A g.v2.cap g.v2.ptr) ∗
            optProtoPolynomialEncoderAt A (a + 104#64) (st.sendingEk.map pbToProtoPolyEncoder)) ∗
            A.pool ∗
            (memRegion (s0.sp - 4144#64) 16 ∗ stackAt (s0.sp - 32#64) allocHookStack) ∗
            (((s0.sp - 32#64) ↦₆₄ s0.readReg64 .fp) ∗ ((s0.sp - 24#64) ↦₆₄ s0.readReg64 .lr) ∗
             ((s0.sp - 16#64) ↦₆₄ s0.readReg64 .x20) ∗ ((s0.sp - 8#64) ↦₆₄ s0.readReg64 .x19)))
          (Q := fun sm => Saved32x20Preserved s0 sm (s0.sp - 32#64) ∧ sm.readReg64 .x19 = a)
          ?_ ?_
        · dsimp only [protoUnchunked2VecHeadersAt, twoVecHeadersAt, vecCapPtrDealloc]
          by_cases hc1 : (g.v1.cap == 0#64) = true <;>
            simp only [hc1, Bool.false_eq_true, ↓reduceIte, sepConj_emp, emp_sepConj]
          · wp_steps; wp_done
          · wp_steps; wp_apply; refine align_pre (by rw [hsp_1]; dsimp only [Reg.fp, Reg.lr, Reg.x19, Reg.x20]; ac_rfl) ?_; wp_done
        · intro s2 hpc2 hrun2 ⟨⟨hx21_2, hx22_2, hx23_2, hx24_2, hx25_2, hx26_2, hx27_2, hx28_2, hsp_2, htrace_2, hvregs_2⟩, hx19_2⟩
          dsimp only [protoUnchunked2VecHeadersAt, twoVecHeadersAt, vecCapPtrDealloc]
          by_cases hc2 : (g.v2.cap == 0#64) = true <;>
            simp only [hc2, Bool.false_eq_true, ↓reduceIte, sepConj_emp, emp_sepConj]
          · wp_steps
            refine SepWP.focus_weaken
              (protoUnchunked2VecHeadersAt_entails_memRegion_104' a g)
              (by sep_focus) ?_
            wp_done
          · wp_steps; wp_apply
            refine SepWP.focus_weaken
              (protoUnchunked2VecHeadersAt_entails_memRegion_104' a g)
              (by sep_focus) ?_
            refine align_pre (by rw [hsp_2]; dsimp only [Reg.fp, Reg.lr, Reg.x19, Reg.x20]; ac_rfl) ?_; wp_done
  · intro s3 hpc3 hrun3 hcl3 ⟨⟨hx21_3, hx22_3, hx23_3, hx24_3, hx25_3, hx26_3, hx27_3, hx28_3, hsp_3, htrace_3, hvregs_3⟩, hx19_3⟩
    have hpoly_enc_raw := drop_glue_proto_poly_encoder_mem_on
      (callerProg := lsProg_282 (Rust.withPanics ext)) hdealloc hcl3
    dsimp only [lsProg_282, withMemEq, dropProtoPolyEncoderSpec] at hpoly_enc_raw ⊢
    cases hek : st.sendingEk with
    | none =>
      simp only [Option.map_none, optProtoPolynomialEncoderAt_none']
      have h112 : (a + 104#64) + 8#64 = a + 112#64 := BitVec.add_assoc a 104#64 8#64
      rw [h112]
      wp_steps
      have hjoin : memRegion a 104 ∗ ((a + 104#64) ↦₆₄ noneCap) ∗ memRegion (a + 112#64) 48 ⊢
          memRegion a 160 := by
        rw [← h112,
            ProofLib.memRegion_split' (b := a) (n := 104) (k := 56) (b' := a + 104#64) rfl rfl (by decide)]
        exact sepConj_mono_right (optProtoPolyEncoder_none_entails_memRegion_56 (a + 104#64))
      refine SepWP.focus_weaken hjoin (by sep_focus) ?_
      refine SepWP.focus_weaken
        (stack_restore_48_from_32 s0.sp (s0.readReg64 .fp) (s0.readReg64 .lr)
          (s0.readReg64 .x20) (s0.readReg64 .x19))
        (by sep_focus) ?_
      wp_done
    | some enc =>
      simp only [Option.map_some, optProtoPolynomialEncoderAt_some']
      refine SepWP.focus_weaken
        (protoPolynomialEncoderAt_expose_cap A (a + 104#64) (pbToProtoPolyEncoder enc))
        (by sep_focus) ?_
      wp_pull_exists; rename_i cap ptr
      wp_focus_pure; intro hcap_lt
      have hne_none := cap_add_one_beq_zero_false hcap_lt
      wp_steps
      refine SepWP.focus_weaken
        (protoPolynomialEncoderAt_unexpose_cap A (a + 104#64) cap ptr (pbToProtoPolyEncoder enc))
        (by sep_focus) ?_
      refine SepWP.focus_weaken
        (stack_restore_48_from_32 s0.sp (s0.readReg64 .fp) (s0.readReg64 .lr)
          (s0.readReg64 .x20) (s0.readReg64 .x19))
        (by sep_focus) ?_
      wp_call hpoly_enc_raw ⟨a + 104#64, pbToProtoPolyEncoder enc⟩
      have hjoin : memRegion a 104 ∗ memRegion (a + 104#64) protoPolynomialEncoderSize ⊢
          memRegion a 160 := by
        rw [show (160 : Nat) = 104 + protoPolynomialEncoderSize from rfl,
            ProofLib.memRegion_split a 104 protoPolynomialEncoderSize (by decide)]
        exact Entails.refl _
      refine SepWP.focus_weaken hjoin (by sep_focus) ?_
      wp_done

theorem drop_proto_chunked_ct1_received_mem_on [LibsignalPlacement] {A : RustAlloc}
    {callerProg : Program} {idx : Nat} {ext : String → Option (State → State)}
    [IsLsBlockProg callerProg idx (Rust.withPanics ext)] {m : Memory}
    (hdealloc : HookSat (Rust.withPanics ext) spqrRustDeallocSym (rustDeallocSpec A))
    (hcl : LibsignalCodeLoaded lsmpl m) (hidx : idx < 619 := by decide) :
    subroutine_ok callerProg (lsmpl.base 282)
      (withMemEq m (dropProtoChunkedCt1ReceivedSpec A)) :=
  lscall_blk_cl (drop_proto_chunked_ct1_received_cl_placed_ok hdealloc) hcl hidx

/-! ## Block `281`: `drop_glue::<proto::pq_ratchet::v1_state::chunked::HeaderSent>` -/

private theorem drop_proto_chunked_header_sent_body_cl [LibsignalPlacement] {A : RustAlloc}
    {H : String → Option (State → State)}
    (hdealloc : subroutine_ok ((blkPC_281).rebase (blkPl_281).base H)
      (lsρ spqrRustDeallocSym) (rustDeallocSpec A))
    (s0 : State) (fsp ptsPtr ptsCap : BitVec 64) (hfsp_align : (fsp &&& 15#64 == 0#64) = true) :
    ∀ (cur cnt : BitVec 64) (bs : List (BitVec 8)) (s : State) (Frame : SepProp),
      s.pc = (blkPl_281).base + 160#64 → s.status = .Running → Saved48Preserved s0 s fsp →
      s.readReg64 .x19 = ptsPtr → s.readReg64 .x20 = ptsCap → s.readReg64 .x21 = cnt → s.readReg64 .x22 = cur + 8#64 →
      SepWP ((blkPC_281).rebase (blkPl_281).base H) ((blkPl_281).base + 148#64) s
        (vecU8 A cur bs ∗ A.pool ∗ stackAt fsp allocHookStack ∗ Frame)
        (fun sm Pm => (Pm ⊢ memRegion cur 24 ∗ A.pool ∗ stackAt fsp allocHookStack ∗ Frame) ∧
          Saved48Preserved s0 sm fsp ∧ sm.readReg64 .x19 = ptsPtr ∧ sm.readReg64 .x20 = ptsCap ∧
          sm.readReg64 .x21 = cnt ∧ sm.readReg64 .x22 = cur + 8#64) := by
  simp only [rustDeallocSpec] at hdealloc
  intro cur cnt bs s Frame hpc hrun ⟨hx23, hx24, hx25, hx26, hx27, hx28, hsp, htrace, hvregs⟩ hx19 hx20 hx21 hx22
  refine SepWP.weaken_pre (sepConj_mono_left (vecU8_entails_capPtr_dealloc A cur bs)) ?_
  apply SepWP.exists_sepConj_left; intro cap; apply SepWP.exists_sepConj_left; intro vptr
  have hstep : SepWP ((blkPC_281).rebase (blkPl_281).base H) ((blkPl_281).base + 148#64) s
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

private theorem drop_proto_chunked_header_sent_loop_cl [LibsignalPlacement] {A : RustAlloc}
    {H : String → Option (State → State)}
    (hdealloc : subroutine_ok ((blkPC_281).rebase (blkPl_281).base H)
      (lsρ spqrRustDeallocSym) (rustDeallocSpec A))
    (s0 : State) (fsp ptsPtr ptsCap : BitVec 64) (hfsp_align : (fsp &&& 15#64 == 0#64) = true) :
    ∀ (rest : List (List (BitVec 8))) (cur : BitVec 64) (s : State) (Frame : SepProp),
      rest ≠ [] → rest.length * 24 < 2 ^ 63 →
      s.pc = (blkPl_281).base + 160#64 → s.status = .Running → Saved48Preserved s0 s fsp →
      s.readReg64 .x19 = ptsPtr → s.readReg64 .x20 = ptsCap →
      s.readReg64 .x21 = BitVec.ofNat 64 rest.length → s.readReg64 .x22 = cur + 8#64 →
      SepWP ((blkPC_281).rebase (blkPl_281).base H) ((blkPl_281).base + 184#64) s
        (arrayAt (fun bs addr => vecU8 A addr bs) 24 cur rest ∗ A.pool ∗ stackAt fsp allocHookStack ∗ Frame)
        (fun sm Pm => (Pm ⊢ memRegion cur (rest.length * 24) ∗ A.pool ∗ stackAt fsp allocHookStack ∗ Frame) ∧
          Saved48Preserved s0 sm fsp ∧ sm.readReg64 .x19 = ptsPtr ∧ sm.readReg64 .x20 = ptsCap) := by
  have hbody := drop_proto_chunked_header_sent_body_cl hdealloc s0 fsp ptsPtr ptsCap hfsp_align
  intro rest; induction rest with
  | nil => intro _ _ _ hne; exact absurd rfl hne
  | cons bs tl ih =>
    intro cur s Frame _ hlen hpc hrun hpres hx19 hx20 hx21 hx22
    simp only [arrayAt, BitVec.ofNat_eq_ofNat]; rw [sep_pull_body]
    refine seq_clean (mid := (blkPl_281).base + 148#64)
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
      refine seq_clean (mid := (blkPl_281).base + 160#64)
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

theorem drop_proto_chunked_header_sent_cl_placed_ok [LibsignalPlacement] {A : RustAlloc}
    {ext : String → Option (State → State)}
    (hdealloc : HookSat (Rust.withPanics ext) spqrRustDeallocSym (rustDeallocSpec A)) :
    subroutine_ok (lsProg_281 (Rust.withPanics ext)) (lsmpl.base 281)
      (withLsCodeLoaded lsmpl (dropProtoChunkedHeaderSentSpec A)) := by
  rw [← ls_blockPlacement_base (i := 281)]
  change subroutine_ok ((blkPC_281).rebase (blkPl_281).base (Rust.withPanics ext)) (blkPl_281).base _
  apply subroutine_ok_withLsCodeLoaded_intro; intro m hcl
  have hdealloc_raw : subroutine_ok ((blkPC_281).rebase (blkPl_281).base (Rust.withPanics ext))
      (lsρ spqrRustDeallocSym) (rustDeallocSpec A) := spqr_hook_ok_of_mem hdealloc
  have hloop := drop_proto_chunked_header_sent_loop_cl hdealloc_raw
  simp only [rustDeallocSpec] at hdealloc_raw
  dsimp only [withMemEq, dropProtoChunkedHeaderSentSpec, protoChunkedHeaderSentSize] at hloop hdealloc_raw ⊢
  wp_init x s0; rcases x with ⟨a, st⟩
  have hx0 : s0.readReg64 .x0 = a := by assumption
  have hm : s0.mem = m := by assumption
  subst hm
  dsimp only [DropProtoChunkedHeaderSentGhost.a, DropProtoChunkedHeaderSentGhost.st, protoChunkedHeaderSentAt] at *
  have hfsp_align : ((s0.sp - 48#64) &&& 15#64 == 0#64) = true := spAligned_sub s0.sp 48#64 (by assumption) (by decide)
  nth_rw 1 [stackAt_dropStack96_split s0.sp]; cells_unfold; wp_pull_exists
  rename_i v_fp v_lr v_x22 v_x21 v_x20 v_x19
  refine seq_clean_lscl hcl (mid := (blkPl_281).base + 100#64)
    (P_mid := (memRegion a 80 ∗
      optProtoPolynomialEncoderAt A (a + 80#64) (st.sendingEk.map pbToProtoPolyEncoder) ∗
      optProtoPolynomialDecoderAt A (a + 136#64) (st.receivingCt1.map pbToProtoPolyDecoder)) ∗
      A.pool ∗ (memRegion (s0.sp - 4192#64) 48 ∗ stackAt (s0.sp - 48#64) allocHookStack) ∗
      (((s0.sp - 48#64) ↦₆₄ s0.readReg64 .fp) ∗ ((s0.sp - 40#64) ↦₆₄ s0.readReg64 .lr) ∗
       ((s0.sp - 32#64) ↦₆₄ s0.readReg64 .x22) ∗ ((s0.sp - 24#64) ↦₆₄ s0.readReg64 .x21) ∗
       ((s0.sp - 16#64) ↦₆₄ s0.readReg64 .x20) ∗ ((s0.sp - 8#64) ↦₆₄ s0.readReg64 .x19)))
    (Q := fun sm => Saved48Preserved s0 sm (s0.sp - 48#64) ∧ sm.readReg64 .x19 = a) ?_ ?_
  · cases huc : st.uc with
    | none =>
      rw [optProtoUnchunkedEkSentAt_none]; wp_steps
      refine SepWP.focus_weaken (optProtoUnchunked1Vec_none_entails_memRegion_80 a) (by sep_focus) ?_
      refine align_pre (by dsimp only [Reg.fp, Reg.lr, Reg.x19, Reg.x20, Reg.x21, Reg.x22]; ac_rfl) ?_; wp_done
    | some u =>
      rw [optProtoUnchunkedEkSentAt_some]
      refine SepWP.weaken_pre (sepConj_mono_left (protoUnchunkedEkSentAt_entails_dealloc A a u)) ?_
      wp_pull_exists; rename_i v1; wp_focus_pure; intro hcap1_lt
      have hne_none1 := cap_add_one_beq_zero_false hcap1_lt
      refine seq_clean (mid := (blkPl_281).base + 80#64)
        (P_mid := ((protoUnchunked1VecHeadersAt a v1 ∗ memRegion (a + 24#64) 48 ∗ memRegion (a + 72#64) 8 ∗
          vecCapPtrDealloc A v1.cap v1.ptr) ∗
          optProtoPolynomialEncoderAt A (a + 80#64) (st.sendingEk.map pbToProtoPolyEncoder) ∗
          optProtoPolynomialDecoderAt A (a + 136#64) (st.receivingCt1.map pbToProtoPolyDecoder)) ∗
          A.pool ∗ (memRegion (s0.sp - 4192#64) 48 ∗ stackAt (s0.sp - 48#64) allocHookStack) ∗
          (((s0.sp - 48#64) ↦₆₄ s0.readReg64 .fp) ∗ ((s0.sp - 40#64) ↦₆₄ s0.readReg64 .lr) ∗
           ((s0.sp - 32#64) ↦₆₄ s0.readReg64 .x22) ∗ ((s0.sp - 24#64) ↦₆₄ s0.readReg64 .x21) ∗
           ((s0.sp - 16#64) ↦₆₄ s0.readReg64 .x20) ∗ ((s0.sp - 8#64) ↦₆₄ s0.readReg64 .x19)))
        (Q := fun sm => Saved48Preserved s0 sm (s0.sp - 48#64) ∧ sm.readReg64 .x19 = a ∧ sm.readReg64 .x20 = v1.cap) ?_ ?_
      · cases hauth : u.auth with
        | none =>
          rw [optProtoAuthenticatorAt_24_none]; dsimp only [protoUnchunked1VecHeadersAt]; wp_steps
          refine SepWP.focus_weaken (optProtoAuthenticatorAt_24_none_entails_memRegion_48 A a) (by sep_focus) ?_
          refine align_pre (by dsimp only [Reg.fp, Reg.lr, Reg.x19, Reg.x20, Reg.x21, Reg.x22]; ac_rfl) ?_; wp_done
        | some auth =>
          rw [optProtoAuthenticatorAt_some]
          refine SepWP.focus_weaken (protoAuthenticatorAt_entails_dealloc A (a + 24#64) auth) (by sep_focus) ?_
          wp_pull_exists; rename_i ga; rw [twoVecHeadersAt_24_eq]; wp_focus_pure; intro hga_lt
          have hne_nonea := cap_add_one_beq_zero_false hga_lt
          refine seq_clean (mid := (blkPl_281).base + 60#64)
            (P_mid := ((protoUnchunked1VecHeadersAt a v1 ∗ (auth24HeadersAt a ga ∗ vecCapPtrDealloc A ga.v2.cap ga.v2.ptr) ∗
              memRegion (a + 72#64) 8 ∗ vecCapPtrDealloc A v1.cap v1.ptr) ∗
              optProtoPolynomialEncoderAt A (a + 80#64) (st.sendingEk.map pbToProtoPolyEncoder) ∗
              optProtoPolynomialDecoderAt A (a + 136#64) (st.receivingCt1.map pbToProtoPolyDecoder)) ∗
              A.pool ∗ (memRegion (s0.sp - 4192#64) 48 ∗ stackAt (s0.sp - 48#64) allocHookStack) ∗
              (((s0.sp - 48#64) ↦₆₄ s0.readReg64 .fp) ∗ ((s0.sp - 40#64) ↦₆₄ s0.readReg64 .lr) ∗
               ((s0.sp - 32#64) ↦₆₄ s0.readReg64 .x22) ∗ ((s0.sp - 24#64) ↦₆₄ s0.readReg64 .x21) ∗
               ((s0.sp - 16#64) ↦₆₄ s0.readReg64 .x20) ∗ ((s0.sp - 8#64) ↦₆₄ s0.readReg64 .x19)))
            (Q := fun sm => Saved48Preserved s0 sm (s0.sp - 48#64) ∧ sm.readReg64 .x19 = a ∧ sm.readReg64 .x20 = v1.cap) ?_ ?_
          · dsimp only [protoUnchunked1VecHeadersAt, auth24HeadersAt, vecCapPtrDealloc]
            by_cases hca1 : (ga.v1.cap == 0#64) = true <;> simp only [hca1, Bool.false_eq_true, ↓reduceIte, sepConj_emp, emp_sepConj]
            · wp_steps; refine align_pre (by dsimp only [Reg.fp, Reg.lr, Reg.x19, Reg.x20, Reg.x21, Reg.x22]; ac_rfl) ?_; wp_done
            · wp_steps; wp_apply; refine align_pre (by dsimp only [Reg.fp, Reg.lr, Reg.x19, Reg.x20, Reg.x21, Reg.x22]; ac_rfl) ?_; wp_done
          · intro sa1 hpca1 hruna1 ⟨⟨hx23_a1, hx24_a1, hx25_a1, hx26_a1, hx27_a1, hx28_a1, hsp_a1, htrace_a1, hvregs_a1⟩, hx19_a1, hx20_a1⟩
            dsimp only [auth24HeadersAt, vecCapPtrDealloc]
            by_cases hca2 : (ga.v2.cap == 0#64) = true <;> simp only [hca2, Bool.false_eq_true, ↓reduceIte, sepConj_emp, emp_sepConj]
            · wp_steps; refine SepWP.focus_weaken (auth24HeadersAt_entails_memRegion_48 a ga) (by sep_focus) ?_
              refine align_pre (by dsimp only [Reg.fp, Reg.lr, Reg.x19, Reg.x20, Reg.x21, Reg.x22]; ac_rfl) ?_; wp_done
            · wp_steps; wp_apply; refine SepWP.focus_weaken (auth24HeadersAt_entails_memRegion_48 a ga) (by sep_focus) ?_
              refine align_pre (by rw [hsp_a1]; dsimp only [Reg.fp, Reg.lr, Reg.x19, Reg.x20, Reg.x21, Reg.x22]; ac_rfl) ?_; wp_done
      · intro s1 hpc1 hrun1 ⟨⟨hx23_1, hx24_1, hx25_1, hx26_1, hx27_1, hx28_1, hsp_1, htrace_1, hvregs_1⟩, hx19_1, hx20_1⟩
        dsimp only [protoUnchunked1VecHeadersAt, vecCapPtrDealloc]
        by_cases hc1 : (v1.cap == 0#64) = true <;> simp only [hc1, Bool.false_eq_true, ↓reduceIte, sepConj_emp, emp_sepConj]
        · wp_steps; refine SepWP.focus_weaken (protoUnchunked1VecHeadersAt_entails_memRegion_80' a v1) (by sep_focus) ?_; wp_done
        · wp_steps; wp_apply; refine SepWP.focus_weaken (protoUnchunked1VecHeadersAt_entails_memRegion_80' a v1) (by sep_focus) ?_
          refine align_pre (by rw [hsp_1]; dsimp only [Reg.fp, Reg.lr, Reg.x19, Reg.x20, Reg.x21, Reg.x22]; ac_rfl) ?_; wp_done
  · intro s2 hpc2 hrun2 hcl2 ⟨⟨hx23_2, hx24_2, hx25_2, hx26_2, hx27_2, hx28_2, hsp_2, htrace_2, hvregs_2⟩, hx19_2⟩
    have hpoly_enc_raw := drop_glue_proto_poly_encoder_mem_on
      (callerProg := lsProg_281 (Rust.withPanics ext)) hdealloc hcl2
    dsimp only [lsProg_281, withMemEq, dropProtoPolyEncoderSpec] at hpoly_enc_raw ⊢
    refine seq_clean (mid := (blkPl_281).base + 120#64)
      (P_mid := (memRegion a 136 ∗
        optProtoPolynomialDecoderAt A (a + 136#64) (st.receivingCt1.map pbToProtoPolyDecoder)) ∗
        A.pool ∗ (memRegion (s0.sp - 4192#64) 48 ∗ stackAt (s0.sp - 48#64) allocHookStack) ∗
        (((s0.sp - 48#64) ↦₆₄ s0.readReg64 .fp) ∗ ((s0.sp - 40#64) ↦₆₄ s0.readReg64 .lr) ∗
         ((s0.sp - 32#64) ↦₆₄ s0.readReg64 .x22) ∗ ((s0.sp - 24#64) ↦₆₄ s0.readReg64 .x21) ∗
         ((s0.sp - 16#64) ↦₆₄ s0.readReg64 .x20) ∗ ((s0.sp - 8#64) ↦₆₄ s0.readReg64 .x19)))
      (Q := fun sm => Saved48Preserved s0 sm (s0.sp - 48#64) ∧ sm.readReg64 .x19 = a) ?_ ?_
    · cases hek : st.sendingEk with
      | none =>
        simp only [Option.map_none, optProtoPolynomialEncoderAt_none']
        have h88 : (a + 80#64) + 8#64 = a + 88#64 := BitVec.add_assoc a 80#64 8#64
        rw [h88]; wp_steps
        have hjoin136 : memRegion a 80 ∗ ((a + 80#64) ↦₆₄ noneCap) ∗ memRegion (a + 88#64) 48 ⊢ memRegion a 136 := by
          rw [← h88, ProofLib.memRegion_split' (b := a) (n := 80) (k := 56) (b' := a + 80#64) rfl rfl (by decide)]
          exact sepConj_mono_right (optProtoPolyEncoder_none_entails_memRegion_56 (a + 80#64))
        refine SepWP.focus_weaken hjoin136 (by sep_focus) ?_; wp_done
      | some enc =>
        simp only [Option.map_some, optProtoPolynomialEncoderAt_some']
        refine SepWP.focus_weaken (protoPolynomialEncoderAt_expose_cap A (a + 80#64) (pbToProtoPolyEncoder enc)) (by sep_focus) ?_
        wp_pull_exists; rename_i cap ptr; wp_focus_pure; intro hcap_lt
        have hne_none := cap_add_one_beq_zero_false hcap_lt
        wp_steps
        refine SepWP.focus_weaken (protoPolynomialEncoderAt_unexpose_cap A (a + 80#64) cap ptr (pbToProtoPolyEncoder enc)) (by sep_focus) ?_
        have hstack_fold : memRegion (s0.sp - 4192#64) 48 ∗ stackAt (s0.sp - 48#64) allocHookStack ⊢ stackAt (s0.sp - 48#64) dropStack48 :=
          Entails.of_eq (stackAt_dropStack48_sub48_split_bottom s0.sp).symm
        refine SepWP.focus_weaken hstack_fold (by sep_focus) ?_
        wp_call hpoly_enc_raw ⟨a + 80#64, pbToProtoPolyEncoder enc⟩
        rw [hsp_2, stackAt_dropStack48_sub48_split_bottom s0.sp]
        have hjoin136 : memRegion a 80 ∗ memRegion (a + 80#64) protoPolynomialEncoderSize ⊢ memRegion a 136 := by
          rw [show (136 : Nat) = 80 + protoPolynomialEncoderSize from rfl,
              ProofLib.memRegion_split a 80 protoPolynomialEncoderSize (by decide)]
          exact Entails.refl _
        refine SepWP.focus_weaken hjoin136 (by sep_focus) ?_
        refine align_pre (by dsimp only [Reg.fp, Reg.lr, Reg.x19, Reg.x20, Reg.x21, Reg.x22]; ac_rfl) ?_; wp_done
    · intro s3 hpc3 hrun3 ⟨⟨hx23_3, hx24_3, hx25_3, hx26_3, hx27_3, hx28_3, hsp_3, htrace_3, hvregs_3⟩, hx19_3⟩
      have hjoin176_from_40 : memRegion a 136 ∗ memRegion (a + 136#64) 40 ⊢ memRegion a 176 := by
        rw [ProofLib.memRegion_split' (b := a) (n := 136) (k := 40) (b' := a + 136#64) rfl rfl (by decide)]
        exact Entails.refl _
      have h144 : (a + 136#64) + 8#64 = a + 144#64 := BitVec.add_assoc a 136#64 8#64
      have h152 : (a + 136#64) + 16#64 = a + 152#64 := BitVec.add_assoc a 136#64 16#64
      have h160 : (a + 136#64) + 24#64 = a + 160#64 := BitVec.add_assoc a 136#64 24#64
      cases hct1 : st.receivingCt1 with
      | none =>
        simp only [Option.map_none, optProtoPolynomialDecoderAt_none']
        rw [h144]; wp_steps
        have hnone40 : ((a + 136#64) ↦₆₄ noneCap) ∗ memRegion (a + 144#64) 32 ⊢ memRegion (a + 136#64) 40 := by
          rw [← h144]; exact optProtoPolyDecoder_none_entails_memRegion_40 (a + 136#64)
        refine SepWP.focus_weaken hnone40 (by sep_focus) ?_
        refine SepWP.focus_weaken hjoin176_from_40 (by sep_focus) ?_
        refine SepWP.focus_weaken
          (stack_restore_96_allocHook s0.sp (s0.readReg64 .fp) (s0.readReg64 .lr)
            (s0.readReg64 .x22) (s0.readReg64 .x21) (s0.readReg64 .x20) (s0.readReg64 .x19))
          (by sep_focus) ?_
        wp_done
      | some dec =>
        simp only [Option.map_some, optProtoPolynomialDecoderAt_some']
        let pb := pbToProtoPolyDecoder dec
        refine SepWP.focus_weaken (protoPolyDecoderAt_entails_dealloc A (a + 136#64) pb) (by sep_focus) ?_
        wp_pull_exists; rename_i g; rw [h144, h152, h160]
        wp_focus_pure; rintro ⟨hpts_le, hpts_cap_lt, hpts_ptr_ne⟩
        have hpts_cap_pow : g.cap.toNat < 2 ^ 63 := by omega
        have hne_none := cap_add_one_beq_zero_false hpts_cap_pow
        have hhdr40 (cap : BitVec 64) :
            ((a + 136#64) ↦₆₄ cap) ∗ ((a + 144#64) ↦₆₄ g.ptr) ∗
              ((a + 152#64) ↦₆₄ BitVec.ofNat 64 pb.pts.length) ∗ memRegion (a + 160#64) 16 ⊢
            memRegion (a + 136#64) 40 := by
          rw [← h144, ← h152, ← h160]
          exact protoPolyDecoderHeaders_entails_memRegion_40 (a + 136#64) cap g.ptr (BitVec.ofNat 64 pb.pts.length)
        refine seq_clean (mid := (blkPl_281).base + 184#64)
          (P_mid := memRegion a 136 ∗ ((a + 136#64) ↦₆₄ g.cap) ∗ ((a + 144#64) ↦₆₄ g.ptr) ∗
            ((a + 152#64) ↦₆₄ BitVec.ofNat 64 pb.pts.length) ∗
            (if g.cap = 0 then emp else A.live g.ptr (g.cap.toNat * 24) 8 ∗ memRegion g.ptr (g.cap.toNat * 24)) ∗
            memRegion (a + 160#64) 16 ∗ A.pool ∗
            (memRegion (s0.sp - 4192#64) 48 ∗ stackAt (s0.sp - 48#64) allocHookStack) ∗
            (((s0.sp - 48#64) ↦₆₄ s0.readReg64 .fp) ∗ ((s0.sp - 40#64) ↦₆₄ s0.readReg64 .lr) ∗
             ((s0.sp - 32#64) ↦₆₄ s0.readReg64 .x22) ∗ ((s0.sp - 24#64) ↦₆₄ s0.readReg64 .x21) ∗
             ((s0.sp - 16#64) ↦₆₄ s0.readReg64 .x20) ∗ ((s0.sp - 8#64) ↦₆₄ s0.readReg64 .x19)))
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
            refine seq_clean (mid := (blkPl_281).base + 160#64)
              (P_mid := arrayAt (fun bs addr => vecU8 A addr bs) 24 g.ptr (bs :: tl) ∗
                A.pool ∗ stackAt (s0.sp - 48#64) allocHookStack ∗
                (memRegion a 136 ∗ ((a + 136#64) ↦₆₄ g.cap) ∗ ((a + 144#64) ↦₆₄ g.ptr) ∗
                 ((a + 152#64) ↦₆₄ BitVec.ofNat 64 (bs :: tl).length) ∗ A.live g.ptr (g.cap.toNat * 24) 8 ∗
                 memRegion (g.ptr + BitVec.ofNat 64 ((bs :: tl).length * 24)) ((g.cap.toNat - (bs :: tl).length) * 24) ∗
                 memRegion (a + 160#64) 16 ∗ memRegion (s0.sp - 4192#64) 48 ∗
                 (((s0.sp - 48#64) ↦₆₄ s0.readReg64 .fp) ∗ ((s0.sp - 40#64) ↦₆₄ s0.readReg64 .lr) ∗
                  ((s0.sp - 32#64) ↦₆₄ s0.readReg64 .x22) ∗ ((s0.sp - 24#64) ↦₆₄ s0.readReg64 .x21) ∗
                  ((s0.sp - 16#64) ↦₆₄ s0.readReg64 .x20) ∗ ((s0.sp - 8#64) ↦₆₄ s0.readReg64 .x19))))
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
        · intro s4 hpc4 hrun4 ⟨⟨hx23_4, hx24_4, hx25_4, hx26_4, hx27_4, hx28_4, hsp_4, htrace_4, hvregs_4⟩, hx19_4, hx20_4⟩
          by_cases hc : g.cap = 0
          · have hc_beq : (g.cap == 0#64) = true := by rw [beq_iff_eq]; exact hc
            simp only [hc, ↓reduceIte, emp_sepConj, sepConj_emp] at hx20_4 ⊢; wp_steps
            refine SepWP.focus_weaken (hhdr40 0) (by sep_focus) ?_
            refine SepWP.focus_weaken hjoin176_from_40 (by sep_focus) ?_
            refine SepWP.focus_weaken
              (stack_restore_96_allocHook s0.sp (s0.readReg64 .fp) (s0.readReg64 .lr)
                (s0.readReg64 .x22) (s0.readReg64 .x21) (s0.readReg64 .x20) (s0.readReg64 .x19)) (by sep_focus) ?_
            wp_done
          · have hc_beq : ¬((g.cap == 0#64) = true) := by rw [beq_iff_eq]; exact hc
            have hlsl := cap_mul_24 hpts_cap_lt
            simp only [hc, ↓reduceIte]; wp_steps
            refine SepWP.focus_weaken (hhdr40 g.cap) (by sep_focus) ?_
            refine SepWP.focus_weaken hjoin176_from_40 (by sep_focus) ?_
            refine SepWP.focus_weaken
              (stack_restore_96_allocHook s0.sp (s0.readReg64 .fp) (s0.readReg64 .lr)
                (s0.readReg64 .x22) (s0.readReg64 .x21) (s0.readReg64 .x20) (s0.readReg64 .x19)) (by sep_focus) ?_
            rw [stackAt_dropStack96_split_bottom s0.sp]
            wp_call hdealloc_raw (g.ptr, g.cap.toNat * 24, 8)
            rw [← stackAt_dropStack96_split_bottom s0.sp]
            wp_done

theorem drop_proto_chunked_header_sent_mem_on [LibsignalPlacement] {A : RustAlloc}
    {callerProg : Program} {idx : Nat} {ext : String → Option (State → State)}
    [IsLsBlockProg callerProg idx (Rust.withPanics ext)] {m : Memory}
    (hdealloc : HookSat (Rust.withPanics ext) spqrRustDeallocSym (rustDeallocSpec A))
    (hcl : LibsignalCodeLoaded lsmpl m) (hidx : idx < 619 := by decide) :
    subroutine_ok callerProg (lsmpl.base 281)
      (withMemEq m (dropProtoChunkedHeaderSentSpec A)) :=
  lscall_blk_cl (drop_proto_chunked_header_sent_cl_placed_ok hdealloc) hcl hidx

end LibsignalBinary.Proofs.SpqrV1.Drop.ProtoChunkedClPlaced
