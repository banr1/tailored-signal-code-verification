/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SpqrV1.Drop.Chunked
public import LibsignalBinary.Proofs.SpqrV1.Drop.ProtoPoly
public import LibsignalBinary.Proofs.SpqrV1.Drop.PolyEncoder
import LibsignalBinary.Proofs.SpqrV1.Alloc.SpqrAllocCodeSym
import LibsignalBinary.Proofs.SpqrV1.Drop.PolyDecoder
import ProofLib.SepLogic.WP.Apply
import ProofLib.SepLogic.WPp
import GeneratedLean.LibsignalSessionObj

/-!
# Relocatable Code-Loaded Drop Glue for `SpqrV1/States/Recv`

Code-loaded `[LibsignalPlacement]` `subroutine_ok` proofs for `drop_glue::<[SortedSet<Pt>; 16]>` (Block `264`),
`[Poly; 16]` (Block `265`), `PolyDecoder` (Block `137`), `PolynomialEncoder` (Block `271`),
`Ct2Sampled` (Block `274`), `HeaderSent` (Block `276`), and `EkSentCt1Received` (Block `278`).
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 400000
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false

namespace CryptoVerification.SpqrV1.States.Recv

open Arm64 Arm64.Obj ProofLib ProofLib.ProgramReflection
open CryptoGames.LibsignalSession (ShaCompress)
open CryptoVerification
open CryptoVerification.RustHeap
open CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalTripleRatchetRepr
open CryptoVerification.LibsignalSpqrV1
open CryptoVerification.SpqrV1.Alloc
open CryptoVerification.SpqrV1.Poly
open CryptoVerification.SpqrV1.Drop

attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero

abbrev spqrRustDeallocSym : String :=
  "_RNvCs1njKG4L9aB3_7___rustc14___rust_dealloc"

/-! ## `withLsCodeLoaded` Sequencing & Introduction Helpers -/

private theorem subroutine_ok_withLsCodeLoaded_intro [LibsignalPlacement] {α : Type}
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

private theorem seq_clean_lscl [LibsignalPlacement] {prog : Program} {mid target : BitVec 64}
    {s : State} {P P_mid : SepProp} {Q : State → Prop} {post : State → SepProp → Prop}
    (hcl : LibsignalCodeLoaded lsmpl s.mem)
    (h1 : SepWP prog mid s P (fun sm Pm => (Pm ⊢ P_mid) ∧ Q sm))
    (h2 : ∀ sm : State, sm.pc = mid → sm.status = .Running →
      LibsignalCodeLoaded lsmpl sm.mem → Q sm → SepWP prog target sm P_mid post) :
    SepWP prog target s P post :=
  sepWP_seq_lscl hcl (SepWP.mono h1 fun sm Pm hpc hrun ⟨hPm, hQ⟩ hcl' =>
    SepWP.weaken_pre hPm (h2 sm hpc hrun hcl' hQ))

private theorem ls_to_blockProgram [LibsignalPlacement] {α : Type}
    {calleeProg : Program} {j : Nat} {H : LibsignalHooks}
    [hcallee : IsLsBlockProg calleeProg j H] {spec : Spec α}
    (h : subroutine_ok calleeProg (lsmpl.base j) spec) :
    subroutine_ok (libsignalSessionLib.blockProgram lsmpl j H) (lsmpl.base j) spec :=
  hcallee.eq_blockProgram ▸ h

private abbrev SavedFrameCells (s0 : State) (w3_old : BitVec 64) : SepProp :=
  ((s0.sp - 32#64) ↦₆₄ s0.readReg64 .fp) ∗ ((s0.sp - 24#64) ↦₆₄ s0.readReg64 .lr) ∗
  ((s0.sp - 16#64) ↦₆₄ s0.readReg64 .x19) ∗ ((s0.sp - 8#64) ↦₆₄ w3_old)

private abbrev SavedMid (s0 : State) (a : BitVec 64) (sm : State) : Prop :=
  Saved32x19Preserved s0 sm (s0.sp - 32#64) ∧ sm.readReg64 .x19 = a

/-! ## Leaf Drop Blocks (`264`, `265`, `137`, `271`) -/

theorem drop_glue_sorted_set_pt16_cl_placed_ok [LibsignalPlacement] {A : RustAlloc}
    {ext : String → Option (State → State)}
    (hdealloc : HookSat (Rust.withPanics ext) spqrRustDeallocSym (rustDeallocSpec A)) :
    subroutine_ok (lsProg_264 (Rust.withPanics ext)) (lsmpl.base 264)
      (withLsCodeLoaded lsmpl (dropGlueSortedSetPt16Spec A)) := by
  rw [← ls_blockPlacement_base (i := 264)]
  exact subroutine_ok_withLsCodeLoaded_of_plain
    (drop_glue_sorted_set_pt16_placed_ok (spqr_hook_ok_of_mem hdealloc))

theorem drop_glue_sorted_set_pt16_cl_blockProgram [LibsignalPlacement] {A : RustAlloc}
    {ext : String → Option (State → State)}
    (hdealloc : HookSat (Rust.withPanics ext) spqrRustDeallocSym (rustDeallocSpec A)) :
    subroutine_ok (libsignalSessionLib.blockProgram lsmpl 264 (Rust.withPanics ext)) (lsmpl.base 264)
      (withLsCodeLoaded lsmpl (dropGlueSortedSetPt16Spec A)) :=
  ls_to_blockProgram (drop_glue_sorted_set_pt16_cl_placed_ok hdealloc)

theorem drop_glue_sorted_set_pt16_cl_on [LibsignalPlacement] {A : RustAlloc}
    {callerProg : Program} {idx : Nat} {ext : String → Option (State → State)}
    [IsLsBlockProg callerProg idx (Rust.withPanics ext)]
    (hdealloc : HookSat (Rust.withPanics ext) spqrRustDeallocSym (rustDeallocSpec A))
    (hidx : idx < 619 := by decide) :
    subroutine_ok callerProg (lsmpl.base 264)
      (withLsCodeLoaded lsmpl (dropGlueSortedSetPt16Spec A)) :=
  ls_subroutine_ok_of_block (drop_glue_sorted_set_pt16_cl_placed_ok hdealloc) hidx

theorem drop_glue_sorted_set_pt16_mem_on [LibsignalPlacement] {A : RustAlloc}
    {callerProg : Program} {idx : Nat} {ext : String → Option (State → State)}
    [IsLsBlockProg callerProg idx (Rust.withPanics ext)] {m : Memory}
    (hdealloc : HookSat (Rust.withPanics ext) spqrRustDeallocSym (rustDeallocSpec A))
    (hcl : LibsignalCodeLoaded lsmpl m) (hidx : idx < 619 := by decide) :
    subroutine_ok callerProg (lsmpl.base 264)
      (withMemEq m (dropGlueSortedSetPt16Spec A)) :=
  lscall_blk_cl (drop_glue_sorted_set_pt16_cl_placed_ok hdealloc) hcl hidx

theorem drop_glue_poly16_cl_placed_ok [LibsignalPlacement] {A : RustAlloc}
    {ext : String → Option (State → State)}
    (hdealloc : HookSat (Rust.withPanics ext) spqrRustDeallocSym (rustDeallocSpec A)) :
    subroutine_ok (lsProg_265 (Rust.withPanics ext)) (lsmpl.base 265)
      (withLsCodeLoaded lsmpl (dropGluePoly16Spec A)) := by
  rw [← ls_blockPlacement_base (i := 265)]
  exact subroutine_ok_withLsCodeLoaded_of_plain
    (drop_glue_poly16_placed_ok (spqr_hook_ok_of_mem hdealloc))

theorem drop_glue_poly16_cl_blockProgram [LibsignalPlacement] {A : RustAlloc}
    {ext : String → Option (State → State)}
    (hdealloc : HookSat (Rust.withPanics ext) spqrRustDeallocSym (rustDeallocSpec A)) :
    subroutine_ok (libsignalSessionLib.blockProgram lsmpl 265 (Rust.withPanics ext)) (lsmpl.base 265)
      (withLsCodeLoaded lsmpl (dropGluePoly16Spec A)) :=
  ls_to_blockProgram (drop_glue_poly16_cl_placed_ok hdealloc)

theorem drop_glue_poly16_cl_on [LibsignalPlacement] {A : RustAlloc}
    {callerProg : Program} {idx : Nat} {ext : String → Option (State → State)}
    [IsLsBlockProg callerProg idx (Rust.withPanics ext)]
    (hdealloc : HookSat (Rust.withPanics ext) spqrRustDeallocSym (rustDeallocSpec A))
    (hidx : idx < 619 := by decide) :
    subroutine_ok callerProg (lsmpl.base 265)
      (withLsCodeLoaded lsmpl (dropGluePoly16Spec A)) :=
  ls_subroutine_ok_of_block (drop_glue_poly16_cl_placed_ok hdealloc) hidx

theorem drop_glue_poly16_mem_on [LibsignalPlacement] {A : RustAlloc}
    {callerProg : Program} {idx : Nat} {ext : String → Option (State → State)}
    [IsLsBlockProg callerProg idx (Rust.withPanics ext)] {m : Memory}
    (hdealloc : HookSat (Rust.withPanics ext) spqrRustDeallocSym (rustDeallocSpec A))
    (hcl : LibsignalCodeLoaded lsmpl m) (hidx : idx < 619 := by decide) :
    subroutine_ok callerProg (lsmpl.base 265)
      (withMemEq m (dropGluePoly16Spec A)) :=
  lscall_blk_cl (drop_glue_poly16_cl_placed_ok hdealloc) hcl hidx

theorem drop_glue_poly_decoder_cl_placed_ok [LibsignalPlacement] {A : RustAlloc}
    {ext : String → Option (State → State)}
    (hdealloc : HookSat (Rust.withPanics ext) spqrRustDeallocSym (rustDeallocSpec A)) :
    subroutine_ok (lsProg_137 (Rust.withPanics ext)) (lsmpl.base 137)
      (withLsCodeLoaded lsmpl (dropGlueSortedSetPt16Spec A)) := by
  rw [← ls_blockPlacement_base (i := 137)]
  exact subroutine_ok_withLsCodeLoaded_of_plain
    (drop_glue_poly_decoder_placed_ok (spqr_hook_ok_of_mem hdealloc))

theorem drop_glue_poly_decoder_cl_blockProgram [LibsignalPlacement] {A : RustAlloc}
    {ext : String → Option (State → State)}
    (hdealloc : HookSat (Rust.withPanics ext) spqrRustDeallocSym (rustDeallocSpec A)) :
    subroutine_ok (libsignalSessionLib.blockProgram lsmpl 137 (Rust.withPanics ext)) (lsmpl.base 137)
      (withLsCodeLoaded lsmpl (dropGlueSortedSetPt16Spec A)) :=
  ls_to_blockProgram (drop_glue_poly_decoder_cl_placed_ok hdealloc)

theorem drop_glue_poly_decoder_cl_on [LibsignalPlacement] {A : RustAlloc}
    {callerProg : Program} {idx : Nat} {ext : String → Option (State → State)}
    [IsLsBlockProg callerProg idx (Rust.withPanics ext)]
    (hdealloc : HookSat (Rust.withPanics ext) spqrRustDeallocSym (rustDeallocSpec A))
    (hidx : idx < 619 := by decide) :
    subroutine_ok callerProg (lsmpl.base 137)
      (withLsCodeLoaded lsmpl (dropGlueSortedSetPt16Spec A)) :=
  ls_subroutine_ok_of_block (drop_glue_poly_decoder_cl_placed_ok hdealloc) hidx

theorem drop_glue_proto_poly_encoder_cl_placed_ok [LibsignalPlacement] {A : RustAlloc}
    {ext : String → Option (State → State)}
    (hdealloc : HookSat (Rust.withPanics ext) spqrRustDeallocSym (rustDeallocSpec A)) :
    subroutine_ok (lsProg_271 (Rust.withPanics ext)) (lsmpl.base 271)
      (withLsCodeLoaded lsmpl (dropProtoPolyEncoderSpec A)) := by
  rw [← ls_blockPlacement_base (i := 271)]
  exact subroutine_ok_withLsCodeLoaded_of_plain
    (drop_glue_proto_poly_encoder_placed_ok (spqr_hook_ok_of_mem hdealloc))

theorem drop_glue_proto_poly_encoder_cl_blockProgram [LibsignalPlacement] {A : RustAlloc}
    {ext : String → Option (State → State)}
    (hdealloc : HookSat (Rust.withPanics ext) spqrRustDeallocSym (rustDeallocSpec A)) :
    subroutine_ok (libsignalSessionLib.blockProgram lsmpl 271 (Rust.withPanics ext)) (lsmpl.base 271)
      (withLsCodeLoaded lsmpl (dropProtoPolyEncoderSpec A)) :=
  ls_to_blockProgram (drop_glue_proto_poly_encoder_cl_placed_ok hdealloc)

theorem drop_glue_proto_poly_encoder_cl_on [LibsignalPlacement] {A : RustAlloc}
    {callerProg : Program} {idx : Nat} {ext : String → Option (State → State)}
    [IsLsBlockProg callerProg idx (Rust.withPanics ext)]
    (hdealloc : HookSat (Rust.withPanics ext) spqrRustDeallocSym (rustDeallocSpec A))
    (hidx : idx < 619 := by decide) :
    subroutine_ok callerProg (lsmpl.base 271)
      (withLsCodeLoaded lsmpl (dropProtoPolyEncoderSpec A)) :=
  ls_subroutine_ok_of_block (drop_glue_proto_poly_encoder_cl_placed_ok hdealloc) hidx

theorem drop_glue_proto_poly_encoder_mem_on [LibsignalPlacement] {A : RustAlloc}
    {callerProg : Program} {idx : Nat} {ext : String → Option (State → State)}
    [IsLsBlockProg callerProg idx (Rust.withPanics ext)] {m : Memory}
    (hdealloc : HookSat (Rust.withPanics ext) spqrRustDeallocSym (rustDeallocSpec A))
    (hcl : LibsignalCodeLoaded lsmpl m) (hidx : idx < 619 := by decide) :
    subroutine_ok callerProg (lsmpl.base 271)
      (withMemEq m (dropProtoPolyEncoderSpec A)) :=
  lscall_blk_cl (drop_glue_proto_poly_encoder_cl_placed_ok hdealloc) hcl hidx

/-! ## Block `272`: `drop_glue::<PolyEncoder> [local#2]` -/

theorem drop_glue_poly_encoder_local2_cl_placed_ok [LibsignalPlacement] {A : RustAlloc}
    {ext : String → Option (State → State)}
    (hdealloc : HookSat (Rust.withPanics ext) spqrRustDeallocSym (rustDeallocSpec A)) :
    subroutine_ok (lsProg_272 (Rust.withPanics ext)) (lsmpl.base 272)
      (withLsCodeLoaded lsmpl (dropGluePolyEncoderSpec A)) := by
  rw [← ls_blockPlacement_base (i := 272)]
  change subroutine_ok ((blkPC_272).rebase (blkPl_272).base (Rust.withPanics ext)) (blkPl_272).base _
  apply subroutine_ok_withLsCodeLoaded_intro
  intro m hcl
  have hpoly16_raw := drop_glue_poly16_mem_on
    (callerProg := lsProg_272 (Rust.withPanics ext)) hdealloc hcl
  simp only [lsProg_272, withMemEq, dropGluePoly16Spec, dropGluePolyEncoderSpec] at hpoly16_raw ⊢
  wp_init x s0; obtain ⟨encA, enc⟩ := x
  subst ‹s0.readReg64 (Reg.gpr 0#5) = encA› ‹s0.mem = m›
  dsimp only at *
  refine SepWP.weaken_pre
    (sepConj_mono_left (polyEncoderAt_entails_tag_vecs_tail A (s0.readReg64 (Reg.gpr 0#5)) enc)) ?_
  apply SepWP.exists_sepConj_left; intro tag
  apply SepWP.exists_sepConj_left; intro vecs
  wp_focus_pure; intro hvecs_len; wp_steps
  wp_call hpoly16_raw ⟨s0.readReg64 (Reg.gpr 0#5) + 8#64, vecs⟩
  refine SepWP.focus_weaken
    (polyEncoder_local2_post_join (s0.readReg64 (Reg.gpr 0#5)) tag) (by sep_focus) ?_
  wp_done

theorem drop_glue_poly_encoder_local2_cl_blockProgram [LibsignalPlacement] {A : RustAlloc}
    {ext : String → Option (State → State)}
    (hdealloc : HookSat (Rust.withPanics ext) spqrRustDeallocSym (rustDeallocSpec A)) :
    subroutine_ok (libsignalSessionLib.blockProgram lsmpl 272 (Rust.withPanics ext)) (lsmpl.base 272)
      (withLsCodeLoaded lsmpl (dropGluePolyEncoderSpec A)) :=
  ls_to_blockProgram (drop_glue_poly_encoder_local2_cl_placed_ok hdealloc)

theorem drop_glue_poly_encoder_local2_cl_on [LibsignalPlacement] {A : RustAlloc}
    {callerProg : Program} {idx : Nat} {ext : String → Option (State → State)}
    [IsLsBlockProg callerProg idx (Rust.withPanics ext)]
    (hdealloc : HookSat (Rust.withPanics ext) spqrRustDeallocSym (rustDeallocSpec A))
    (hidx : idx < 619 := by decide) :
    subroutine_ok callerProg (lsmpl.base 272)
      (withLsCodeLoaded lsmpl (dropGluePolyEncoderSpec A)) :=
  ls_subroutine_ok_of_block (drop_glue_poly_encoder_local2_cl_placed_ok hdealloc) hidx

theorem drop_glue_poly_encoder_local2_mem_on [LibsignalPlacement] {A : RustAlloc}
    {callerProg : Program} {idx : Nat} {ext : String → Option (State → State)}
    [IsLsBlockProg callerProg idx (Rust.withPanics ext)] {m : Memory}
    (hdealloc : HookSat (Rust.withPanics ext) spqrRustDeallocSym (rustDeallocSpec A))
    (hcl : LibsignalCodeLoaded lsmpl m) (hidx : idx < 619 := by decide) :
    subroutine_ok callerProg (lsmpl.base 272)
      (withMemEq m (dropGluePolyEncoderSpec A)) :=
  lscall_blk_cl (drop_glue_poly_encoder_local2_cl_placed_ok hdealloc) hcl hidx

/-! ## Block `274`: `drop_glue::<chunked::send_ct::Ct2Sampled>` -/

theorem drop_chunked_ct2_sampled_cl_placed_ok [LibsignalPlacement] {A : RustAlloc} {F : ShaCompress}
    {ext : String → Option (State → State)}
    (hdealloc : HookSat (Rust.withPanics ext) spqrRustDeallocSym (rustDeallocSpec A)) :
    subroutine_ok (lsProg_274 (Rust.withPanics ext)) (lsmpl.base 274)
      (withLsCodeLoaded lsmpl (dropChunkedCt2SampledSpec A F)) := by
  rw [← ls_blockPlacement_base (i := 274)]
  change subroutine_ok ((blkPC_274).rebase (blkPl_274).base (Rust.withPanics ext)) (blkPl_274).base _
  apply subroutine_ok_withLsCodeLoaded_intro; intro m hcl
  have hdealloc_raw : subroutine_ok (lsProg_274 (Rust.withPanics ext))
      (lsρ spqrRustDeallocSym) (rustDeallocSpec A) := spqr_hook_ok_of_mem hdealloc
  simp only [rustDeallocSpec] at hdealloc_raw
  dsimp only [lsProg_274, withMemEq, dropChunkedCt2SampledSpec, chunkedCt2SampledSize] at hdealloc_raw ⊢
  wp_init x s0; rcases x with ⟨a, st⟩
  have hx0 : s0.readReg64 .x0 = a := by assumption
  have hm : s0.mem = m := by assumption
  subst hm
  dsimp only [DropChunkedCt2SampledGhost.a, DropChunkedCt2SampledGhost.st, chunkedCt2SampledAt] at *
  have hfsp_align : ((s0.sp - 32#64) &&& 15#64 == 0#64) = true :=
    spAligned_sub s0.sp 32#64 (by assumption) (by decide)
  nth_rw 1 [stackAt_dropStack32_split s0.sp]; cells_unfold; wp_pull_exists
  rename_i fp_old lr_old x19_old w3_old
  refine SepWP.weaken_pre
    (sepConj_mono_right (sepConj_mono_left (unchunkedCt2Sent400_entails_dealloc A a st.uc))) ?_
  wp_pull_exists; rename_i g
  refine seq_clean_lscl hcl (mid := (blkPl_274).base + 56#64)
    (P_mid := (polyEncoderAt A a st.sending_ct2 ∗ memRegion (a + 400#64) 56) ∗
      A.pool ∗ stackAt (s0.sp - 32#64) allocHookStack ∗ SavedFrameCells s0 w3_old)
    (Q := SavedMid s0 a) ?_ ?_
  · refine Drop.seq_clean (mid := (blkPl_274).base + 36#64)
      (P_mid := (polyEncoderAt A a st.sending_ct2 ∗
        (twoVec400HeadersAt a g ∗ vecCapPtrDealloc A g.v2.cap g.v2.ptr)) ∗
        A.pool ∗ stackAt (s0.sp - 32#64) allocHookStack ∗ SavedFrameCells s0 w3_old)
      (Q := SavedMid s0 a) ?_ ?_
    · dsimp only [twoVec400HeadersAt, vecCapPtrDealloc, SavedFrameCells, SavedMid]
      by_cases hc1 : (g.v1.cap == 0#64) = true <;>
        simp only [hc1, Bool.false_eq_true, ↓reduceIte, sepConj_emp, emp_sepConj]
      · wp_steps; refine Drop.align_pre (by dsimp only [Reg.fp, Reg.lr, Reg.x19]; ac_rfl) ?_; wp_done
      · wp_steps; wp_apply; refine Drop.align_pre (by dsimp only [Reg.fp, Reg.lr, Reg.x19]; ac_rfl) ?_; wp_done
    · intro s1 hpc1 hrun1 ⟨⟨hx20_1, hx21_1, hx22_1, hx23_1, hx24_1, hx25_1, hx26_1, hx27_1, hx28_1, hsp_1, htrace_1, hvregs_1⟩, hx19_1⟩
      refine SepWP.strengthen_entails_const
        (sepConj_mono_left (sepConj_mono_right (twoVec400HeadersAt_entails_memRegion_56 a g))) ?_
      change SepWP _ _ s1 _ (fun sm Pm => (Pm ⊢ (polyEncoderAt A a st.sending_ct2 ∗ twoVec400HeadersAt a g) ∗
        A.pool ∗ stackAt (s0.sp - 32#64) allocHookStack ∗ SavedFrameCells s0 w3_old) ∧ SavedMid s0 a sm)
      dsimp only [twoVec400HeadersAt, vecCapPtrDealloc, SavedFrameCells, SavedMid]
      by_cases hc2 : (g.v2.cap == 0#64) = true <;>
        simp only [hc2, Bool.false_eq_true, ↓reduceIte, sepConj_emp, emp_sepConj]
      · wp_steps; wp_done
      · wp_steps; wp_apply; refine Drop.align_pre (by rw [hsp_1]; ac_rfl) ?_; wp_done
  · intro s2 hpc2 hrun2 hcl2 ⟨⟨hx20_2, hx21_2, hx22_2, hx23_2, hx24_2, hx25_2, hx26_2, hx27_2, hx28_2, hsp_2, htrace_2, hvregs_2⟩, hx19_2⟩
    have hpoly16_raw := drop_glue_poly16_mem_on
      (callerProg := lsProg_274 (Rust.withPanics ext)) hdealloc hcl2
    dsimp only [lsProg_274, withMemEq, dropGluePoly16Spec, SavedFrameCells] at hpoly16_raw ⊢
    refine SepWP.weaken_pre
      (sepConj_mono_left (sepConj_mono_left (polyEncoderAt_entails_tag_vecs_tail A a st.sending_ct2))) ?_
    rw [sepExists_sepConj_left, sepExists_sepConj_left]; apply ProofLib.SepWP.exists_left; intro tag
    rw [sepExists_sepConj_left, sepExists_sepConj_left]; apply ProofLib.SepWP.exists_left; intro vecs
    wp_focus_pure; intro hvecs_len; wp_steps
    refine SepWP.focus_weaken
      (stack_restore_32_allocHook s0.sp (s0.readReg64 .fp) (s0.readReg64 .lr) (s0.readReg64 .x19) w3_old)
      (by sep_focus) ?_
    wp_call hpoly16_raw ⟨a + 8#64, vecs⟩
    refine SepWP.weaken_pre
      (Entails.trans
        (Entails.of_eq (show _ = ((a ↦₆₄ tag) ∗ memRegion (a + 8#64) polyArrayBytes ∗
          memRegion (a + 392#64) 8 ∗ memRegion (a + 400#64) 56) ∗
          A.pool ∗ stackAt s0.sp dropGluePoly16Stack by ac_rfl))
        (sepConj_mono_left (chunked_400_join a tag 56 456 rfl (by decide)))) ?_
    wp_done

theorem drop_chunked_ct2_sampled_cl_blockProgram [LibsignalPlacement] {A : RustAlloc} {F : ShaCompress}
    {ext : String → Option (State → State)}
    (hdealloc : HookSat (Rust.withPanics ext) spqrRustDeallocSym (rustDeallocSpec A)) :
    subroutine_ok (libsignalSessionLib.blockProgram lsmpl 274 (Rust.withPanics ext)) (lsmpl.base 274)
      (withLsCodeLoaded lsmpl (dropChunkedCt2SampledSpec A F)) :=
  ls_to_blockProgram (drop_chunked_ct2_sampled_cl_placed_ok hdealloc)

theorem drop_chunked_ct2_sampled_cl_on [LibsignalPlacement] {A : RustAlloc} {F : ShaCompress}
    {callerProg : Program} {idx : Nat} {ext : String → Option (State → State)}
    [IsLsBlockProg callerProg idx (Rust.withPanics ext)]
    (hdealloc : HookSat (Rust.withPanics ext) spqrRustDeallocSym (rustDeallocSpec A))
    (hidx : idx < 619 := by decide) :
    subroutine_ok callerProg (lsmpl.base 274)
      (withLsCodeLoaded lsmpl (dropChunkedCt2SampledSpec A F)) :=
  ls_subroutine_ok_of_block (drop_chunked_ct2_sampled_cl_placed_ok hdealloc) hidx

theorem drop_chunked_ct2_sampled_mem_on [LibsignalPlacement] {A : RustAlloc} {F : ShaCompress}
    {callerProg : Program} {idx : Nat} {ext : String → Option (State → State)}
    [IsLsBlockProg callerProg idx (Rust.withPanics ext)] {m : Memory}
    (hdealloc : HookSat (Rust.withPanics ext) spqrRustDeallocSym (rustDeallocSpec A))
    (hcl : LibsignalCodeLoaded lsmpl m) (hidx : idx < 619 := by decide) :
    subroutine_ok callerProg (lsmpl.base 274)
      (withMemEq m (dropChunkedCt2SampledSpec A F)) :=
  lscall_blk_cl (drop_chunked_ct2_sampled_cl_placed_ok hdealloc) hcl hidx

/-! ## Block `275`: `drop_glue::<chunked::send_ct::EkReceivedCt1Sampled>` -/

theorem drop_chunked_ek_received_ct1_sampled_cl_placed_ok [LibsignalPlacement]
    {A : RustAlloc} {F : ShaCompress} {ext : String → Option (State → State)}
    (hdealloc : HookSat (Rust.withPanics ext) spqrRustDeallocSym (rustDeallocSpec A)) :
    subroutine_ok (lsProg_275 (Rust.withPanics ext)) (lsmpl.base 275)
      (withLsCodeLoaded lsmpl (dropChunkedEkReceivedCt1SampledSpec A F)) := by
  rw [← ls_blockPlacement_base (i := 275)]
  change subroutine_ok ((blkPC_275).rebase (blkPl_275).base (Rust.withPanics ext)) (blkPl_275).base _
  apply subroutine_ok_withLsCodeLoaded_intro; intro m hcl
  have hdealloc_raw : subroutine_ok (lsProg_275 (Rust.withPanics ext))
      (lsρ spqrRustDeallocSym) (rustDeallocSpec A) := spqr_hook_ok_of_mem hdealloc
  simp only [rustDeallocSpec] at hdealloc_raw
  dsimp only [lsProg_275, withMemEq, dropChunkedEkReceivedCt1SampledSpec, chunkedEkReceivedCt1SampledSize] at hdealloc_raw ⊢
  wp_init x s0; rcases x with ⟨a, st⟩
  have hx0 : s0.readReg64 .x0 = a := by assumption
  have hm : s0.mem = m := by assumption
  subst hm
  dsimp only [DropChunkedEkReceivedCt1SampledGhost.a, DropChunkedEkReceivedCt1SampledGhost.st, chunkedEkReceivedCt1SampledAt] at *
  have hfsp_align : ((s0.sp - 32#64) &&& 15#64 == 0#64) = true :=
    spAligned_sub s0.sp 32#64 (by assumption) (by decide)
  nth_rw 1 [stackAt_dropStack32_split s0.sp]; cells_unfold; wp_pull_exists
  rename_i fp_old lr_old x19_old w3_old
  refine SepWP.weaken_pre
    (sepConj_mono_right (sepConj_mono_left (unchunkedCt1SentEkReceived400_entails_dealloc A a st.uc))) ?_
  wp_pull_exists; rename_i g
  refine seq_clean_lscl hcl (mid := (blkPl_275).base + 116#64)
    (P_mid := (polyEncoderAt A a st.sending_ct1 ∗ memRegion (a + 400#64) 128) ∗
      A.pool ∗ stackAt (s0.sp - 32#64) allocHookStack ∗ SavedFrameCells s0 w3_old)
    (Q := SavedMid s0 a) ?_ ?_
  · refine Drop.seq_clean (mid := (blkPl_275).base + 36#64)
      (P_mid := (polyEncoderAt A a st.sending_ct1 ∗
        (fiveVec400HeadersAt a g ∗ vecCapPtrDealloc A g.v2.cap g.v2.ptr ∗
         vecCapPtrDealloc A g.v3.cap g.v3.ptr ∗ vecCapPtrDealloc A g.v4.cap g.v4.ptr ∗
         vecCapPtrDealloc A g.v5.cap g.v5.ptr)) ∗
        A.pool ∗ stackAt (s0.sp - 32#64) allocHookStack ∗ SavedFrameCells s0 w3_old)
      (Q := SavedMid s0 a) ?_ ?_
    · dsimp only [fiveVec400HeadersAt, vecCapPtrDealloc, SavedFrameCells, SavedMid]
      by_cases hc1 : (g.v1.cap == 0#64) = true <;>
        simp only [hc1, Bool.false_eq_true, ↓reduceIte, sepConj_emp, emp_sepConj]
      · wp_steps; refine Drop.align_pre (by dsimp only [Reg.fp, Reg.lr, Reg.x19]; ac_rfl) ?_; wp_done
      · wp_steps; wp_apply; refine Drop.align_pre (by dsimp only [Reg.fp, Reg.lr, Reg.x19]; ac_rfl) ?_; wp_done
    · intro s1 hpc1 hrun1 ⟨⟨hx20_1, hx21_1, hx22_1, hx23_1, hx24_1, hx25_1, hx26_1, hx27_1, hx28_1, hsp_1, htrace_1, hvregs_1⟩, hx19_1⟩
      refine Drop.seq_clean (mid := (blkPl_275).base + 56#64)
        (P_mid := (polyEncoderAt A a st.sending_ct1 ∗
          (fiveVec400HeadersAt a g ∗ vecCapPtrDealloc A g.v3.cap g.v3.ptr ∗
           vecCapPtrDealloc A g.v4.cap g.v4.ptr ∗ vecCapPtrDealloc A g.v5.cap g.v5.ptr)) ∗
          A.pool ∗ stackAt (s0.sp - 32#64) allocHookStack ∗ SavedFrameCells s0 w3_old)
        (Q := SavedMid s0 a) ?_ ?_
      · dsimp only [fiveVec400HeadersAt, vecCapPtrDealloc, SavedFrameCells, SavedMid]
        by_cases hc2 : (g.v2.cap == 0#64) = true <;>
          simp only [hc2, Bool.false_eq_true, ↓reduceIte, sepConj_emp, emp_sepConj]
        · wp_steps; wp_done
        · wp_steps; wp_apply; refine Drop.align_pre (by rw [hsp_1]; ac_rfl) ?_; wp_done
      · intro s2 hpc2 hrun2 ⟨⟨hx20_2, hx21_2, hx22_2, hx23_2, hx24_2, hx25_2, hx26_2, hx27_2, hx28_2, hsp_2, htrace_2, hvregs_2⟩, hx19_2⟩
        refine Drop.seq_clean (mid := (blkPl_275).base + 76#64)
          (P_mid := (polyEncoderAt A a st.sending_ct1 ∗
            (fiveVec400HeadersAt a g ∗ vecCapPtrDealloc A g.v4.cap g.v4.ptr ∗
             vecCapPtrDealloc A g.v5.cap g.v5.ptr)) ∗
            A.pool ∗ stackAt (s0.sp - 32#64) allocHookStack ∗ SavedFrameCells s0 w3_old)
          (Q := SavedMid s0 a) ?_ ?_
        · dsimp only [fiveVec400HeadersAt, vecCapPtrDealloc, SavedFrameCells, SavedMid]
          by_cases hc3 : (g.v3.cap == 0#64) = true <;>
            simp only [hc3, Bool.false_eq_true, ↓reduceIte, sepConj_emp, emp_sepConj]
          · wp_steps; wp_done
          · wp_steps; wp_apply; refine Drop.align_pre (by rw [hsp_2]; ac_rfl) ?_; wp_done
        · intro s3 hpc3 hrun3 ⟨⟨hx20_3, hx21_3, hx22_3, hx23_3, hx24_3, hx25_3, hx26_3, hx27_3, hx28_3, hsp_3, htrace_3, hvregs_3⟩, hx19_3⟩
          refine Drop.seq_clean (mid := (blkPl_275).base + 96#64)
            (P_mid := (polyEncoderAt A a st.sending_ct1 ∗
              (fiveVec400HeadersAt a g ∗ vecCapPtrDealloc A g.v5.cap g.v5.ptr)) ∗
              A.pool ∗ stackAt (s0.sp - 32#64) allocHookStack ∗ SavedFrameCells s0 w3_old)
            (Q := SavedMid s0 a) ?_ ?_
          · dsimp only [fiveVec400HeadersAt, vecCapPtrDealloc, SavedFrameCells, SavedMid]
            by_cases hc4 : (g.v4.cap == 0#64) = true <;>
              simp only [hc4, Bool.false_eq_true, ↓reduceIte, sepConj_emp, emp_sepConj]
            · wp_steps; wp_done
            · wp_steps; wp_apply; refine Drop.align_pre (by rw [hsp_3]; ac_rfl) ?_; wp_done
          · intro s4 hpc4 hrun4 ⟨⟨hx20_4, hx21_4, hx22_4, hx23_4, hx24_4, hx25_4, hx26_4, hx27_4, hx28_4, hsp_4, htrace_4, hvregs_4⟩, hx19_4⟩
            refine SepWP.strengthen_entails_const
              (sepConj_mono_left (sepConj_mono_right (fiveVec400HeadersAt_entails_memRegion_128 a g))) ?_
            change SepWP _ _ s4 _ (fun sm Pm => (Pm ⊢ (polyEncoderAt A a st.sending_ct1 ∗ fiveVec400HeadersAt a g) ∗
              A.pool ∗ stackAt (s0.sp - 32#64) allocHookStack ∗ SavedFrameCells s0 w3_old) ∧ SavedMid s0 a sm)
            dsimp only [fiveVec400HeadersAt, vecCapPtrDealloc, SavedFrameCells, SavedMid]
            by_cases hc5 : (g.v5.cap == 0#64) = true <;>
              simp only [hc5, Bool.false_eq_true, ↓reduceIte, sepConj_emp, emp_sepConj]
            · wp_steps; wp_done
            · wp_steps; wp_apply; refine Drop.align_pre (by rw [hsp_4]; ac_rfl) ?_; wp_done
  · intro s5 hpc5 hrun5 hcl5 ⟨⟨hx20_5, hx21_5, hx22_5, hx23_5, hx24_5, hx25_5, hx26_5, hx27_5, hx28_5, hsp_5, htrace_5, hvregs_5⟩, hx19_5⟩
    have hpoly16_raw := drop_glue_poly16_mem_on
      (callerProg := lsProg_275 (Rust.withPanics ext)) hdealloc hcl5
    dsimp only [lsProg_275, withMemEq, dropGluePoly16Spec, SavedFrameCells] at hpoly16_raw ⊢
    refine SepWP.weaken_pre
      (sepConj_mono_left (sepConj_mono_left (polyEncoderAt_entails_tag_vecs_tail A a st.sending_ct1))) ?_
    rw [sepExists_sepConj_left, sepExists_sepConj_left]; apply ProofLib.SepWP.exists_left; intro tag
    rw [sepExists_sepConj_left, sepExists_sepConj_left]; apply ProofLib.SepWP.exists_left; intro vecs
    wp_focus_pure; intro hvecs_len; wp_steps
    refine SepWP.focus_weaken
      (stack_restore_32_allocHook s0.sp (s0.readReg64 .fp) (s0.readReg64 .lr) (s0.readReg64 .x19) w3_old)
      (by sep_focus) ?_
    wp_call hpoly16_raw ⟨a + 8#64, vecs⟩
    refine SepWP.weaken_pre
      (Entails.trans
        (Entails.of_eq (show _ = ((a ↦₆₄ tag) ∗ memRegion (a + 8#64) polyArrayBytes ∗
          memRegion (a + 392#64) 8 ∗ memRegion (a + 400#64) 128) ∗
          A.pool ∗ stackAt s0.sp dropGluePoly16Stack by ac_rfl))
        (sepConj_mono_left (chunked_400_join a tag 128 528 rfl (by decide)))) ?_
    wp_done

theorem drop_chunked_ek_received_ct1_sampled_cl_blockProgram [LibsignalPlacement]
    {A : RustAlloc} {F : ShaCompress} {ext : String → Option (State → State)}
    (hdealloc : HookSat (Rust.withPanics ext) spqrRustDeallocSym (rustDeallocSpec A)) :
    subroutine_ok (libsignalSessionLib.blockProgram lsmpl 275 (Rust.withPanics ext)) (lsmpl.base 275)
      (withLsCodeLoaded lsmpl (dropChunkedEkReceivedCt1SampledSpec A F)) :=
  ls_to_blockProgram (drop_chunked_ek_received_ct1_sampled_cl_placed_ok hdealloc)

theorem drop_chunked_ek_received_ct1_sampled_cl_on [LibsignalPlacement] {A : RustAlloc} {F : ShaCompress}
    {callerProg : Program} {idx : Nat} {ext : String → Option (State → State)}
    [IsLsBlockProg callerProg idx (Rust.withPanics ext)]
    (hdealloc : HookSat (Rust.withPanics ext) spqrRustDeallocSym (rustDeallocSpec A))
    (hidx : idx < 619 := by decide) :
    subroutine_ok callerProg (lsmpl.base 275)
      (withLsCodeLoaded lsmpl (dropChunkedEkReceivedCt1SampledSpec A F)) :=
  ls_subroutine_ok_of_block (drop_chunked_ek_received_ct1_sampled_cl_placed_ok hdealloc) hidx

theorem drop_chunked_ek_received_ct1_sampled_mem_on [LibsignalPlacement] {A : RustAlloc} {F : ShaCompress}
    {callerProg : Program} {idx : Nat} {ext : String → Option (State → State)}
    [IsLsBlockProg callerProg idx (Rust.withPanics ext)] {m : Memory}
    (hdealloc : HookSat (Rust.withPanics ext) spqrRustDeallocSym (rustDeallocSpec A))
    (hcl : LibsignalCodeLoaded lsmpl m) (hidx : idx < 619 := by decide) :
    subroutine_ok callerProg (lsmpl.base 275)
      (withMemEq m (dropChunkedEkReceivedCt1SampledSpec A F)) :=
  lscall_blk_cl (drop_chunked_ek_received_ct1_sampled_cl_placed_ok hdealloc) hcl hidx

/-! ## Block `277`: `drop_glue::<chunked::send_ek::Ct1Received>` -/

theorem drop_chunked_ct1_received_cl_placed_ok [LibsignalPlacement]
    {A : RustAlloc} {F : ShaCompress} {ext : String → Option (State → State)}
    (hdealloc : HookSat (Rust.withPanics ext) spqrRustDeallocSym (rustDeallocSpec A)) :
    subroutine_ok (lsProg_277 (Rust.withPanics ext)) (lsmpl.base 277)
      (withLsCodeLoaded lsmpl (dropChunkedCt1ReceivedSpec A F)) := by
  rw [← ls_blockPlacement_base (i := 277)]
  change subroutine_ok ((blkPC_277).rebase (blkPl_277).base (Rust.withPanics ext)) (blkPl_277).base _
  apply subroutine_ok_withLsCodeLoaded_intro; intro m hcl
  have hdealloc_raw : subroutine_ok (lsProg_277 (Rust.withPanics ext))
      (lsρ spqrRustDeallocSym) (rustDeallocSpec A) := spqr_hook_ok_of_mem hdealloc
  simp only [rustDeallocSpec] at hdealloc_raw
  dsimp only [lsProg_277, withMemEq, dropChunkedCt1ReceivedSpec, chunkedCt1ReceivedSize] at hdealloc_raw ⊢
  wp_init x s0; rcases x with ⟨a, st⟩
  have hx0 : s0.readReg64 .x0 = a := by assumption
  have hm : s0.mem = m := by assumption
  subst hm
  dsimp only [DropChunkedCt1ReceivedGhost.a, DropChunkedCt1ReceivedGhost.st, chunkedCt1ReceivedAt] at *
  have hfsp_align : ((s0.sp - 32#64) &&& 15#64 == 0#64) = true :=
    spAligned_sub s0.sp 32#64 (by assumption) (by decide)
  nth_rw 1 [stackAt_dropStack32_split s0.sp]; cells_unfold; wp_pull_exists
  rename_i fp_old lr_old x19_old w3_old
  refine SepWP.weaken_pre
    (sepConj_mono_right (sepConj_mono_left (unchunkedEkSentCt1Received400_entails_dealloc A a st.uc))) ?_
  wp_pull_exists; rename_i g
  refine seq_clean_lscl hcl (mid := (blkPl_277).base + 96#64)
    (P_mid := (polyEncoderAt A a st.sending_ek ∗ memRegion (a + 400#64) 104) ∗
      A.pool ∗ stackAt (s0.sp - 32#64) allocHookStack ∗ SavedFrameCells s0 w3_old)
    (Q := SavedMid s0 a) ?_ ?_
  · refine Drop.seq_clean (mid := (blkPl_277).base + 36#64)
      (P_mid := (polyEncoderAt A a st.sending_ek ∗
        (fourVec400HeadersAt a g ∗ vecCapPtrDealloc A g.v2.cap g.v2.ptr ∗
         vecCapPtrDealloc A g.v3.cap g.v3.ptr ∗ vecCapPtrDealloc A g.v4.cap g.v4.ptr)) ∗
        A.pool ∗ stackAt (s0.sp - 32#64) allocHookStack ∗ SavedFrameCells s0 w3_old)
      (Q := SavedMid s0 a) ?_ ?_
    · dsimp only [fourVec400HeadersAt, vecCapPtrDealloc, SavedFrameCells, SavedMid]
      by_cases hc1 : (g.v1.cap == 0#64) = true <;>
        simp only [hc1, Bool.false_eq_true, ↓reduceIte, sepConj_emp, emp_sepConj]
      · wp_steps; refine Drop.align_pre (by dsimp only [Reg.fp, Reg.lr, Reg.x19]; ac_rfl) ?_; wp_done
      · wp_steps; wp_apply; refine Drop.align_pre (by dsimp only [Reg.fp, Reg.lr, Reg.x19]; ac_rfl) ?_; wp_done
    · intro s1 hpc1 hrun1 ⟨⟨hx20_1, hx21_1, hx22_1, hx23_1, hx24_1, hx25_1, hx26_1, hx27_1, hx28_1, hsp_1, htrace_1, hvregs_1⟩, hx19_1⟩
      refine Drop.seq_clean (mid := (blkPl_277).base + 56#64)
        (P_mid := (polyEncoderAt A a st.sending_ek ∗
          (fourVec400HeadersAt a g ∗ vecCapPtrDealloc A g.v3.cap g.v3.ptr ∗
           vecCapPtrDealloc A g.v4.cap g.v4.ptr)) ∗
          A.pool ∗ stackAt (s0.sp - 32#64) allocHookStack ∗ SavedFrameCells s0 w3_old)
        (Q := SavedMid s0 a) ?_ ?_
      · dsimp only [fourVec400HeadersAt, vecCapPtrDealloc, SavedFrameCells, SavedMid]
        by_cases hc2 : (g.v2.cap == 0#64) = true <;>
          simp only [hc2, Bool.false_eq_true, ↓reduceIte, sepConj_emp, emp_sepConj]
        · wp_steps; wp_done
        · wp_steps; wp_apply; refine Drop.align_pre (by rw [hsp_1]; ac_rfl) ?_; wp_done
      · intro s2 hpc2 hrun2 ⟨⟨hx20_2, hx21_2, hx22_2, hx23_2, hx24_2, hx25_2, hx26_2, hx27_2, hx28_2, hsp_2, htrace_2, hvregs_2⟩, hx19_2⟩
        refine Drop.seq_clean (mid := (blkPl_277).base + 76#64)
          (P_mid := (polyEncoderAt A a st.sending_ek ∗
            (fourVec400HeadersAt a g ∗ vecCapPtrDealloc A g.v4.cap g.v4.ptr)) ∗
            A.pool ∗ stackAt (s0.sp - 32#64) allocHookStack ∗ SavedFrameCells s0 w3_old)
          (Q := SavedMid s0 a) ?_ ?_
        · dsimp only [fourVec400HeadersAt, vecCapPtrDealloc, SavedFrameCells, SavedMid]
          by_cases hc3 : (g.v3.cap == 0#64) = true <;>
            simp only [hc3, Bool.false_eq_true, ↓reduceIte, sepConj_emp, emp_sepConj]
          · wp_steps; wp_done
          · wp_steps; wp_apply; refine Drop.align_pre (by rw [hsp_2]; ac_rfl) ?_; wp_done
        · intro s3 hpc3 hrun3 ⟨⟨hx20_3, hx21_3, hx22_3, hx23_3, hx24_3, hx25_3, hx26_3, hx27_3, hx28_3, hsp_3, htrace_3, hvregs_3⟩, hx19_3⟩
          refine SepWP.strengthen_entails_const
            (sepConj_mono_left (sepConj_mono_right (fourVec400HeadersAt_entails_memRegion_104 a g))) ?_
          change SepWP _ _ s3 _ (fun sm Pm => (Pm ⊢ (polyEncoderAt A a st.sending_ek ∗ fourVec400HeadersAt a g) ∗
            A.pool ∗ stackAt (s0.sp - 32#64) allocHookStack ∗ SavedFrameCells s0 w3_old) ∧ SavedMid s0 a sm)
          dsimp only [fourVec400HeadersAt, vecCapPtrDealloc, SavedFrameCells, SavedMid]
          by_cases hc4 : (g.v4.cap == 0#64) = true <;>
            simp only [hc4, Bool.false_eq_true, ↓reduceIte, sepConj_emp, emp_sepConj]
          · wp_steps; wp_done
          · wp_steps; wp_apply; refine Drop.align_pre (by rw [hsp_3]; ac_rfl) ?_; wp_done
  · intro s4 hpc4 hrun4 hcl4 ⟨⟨hx20_4, hx21_4, hx22_4, hx23_4, hx24_4, hx25_4, hx26_4, hx27_4, hx28_4, hsp_4, htrace_4, hvregs_4⟩, hx19_4⟩
    have hpoly16_raw := drop_glue_poly16_mem_on
      (callerProg := lsProg_277 (Rust.withPanics ext)) hdealloc hcl4
    dsimp only [lsProg_277, withMemEq, dropGluePoly16Spec, SavedFrameCells] at hpoly16_raw ⊢
    refine SepWP.weaken_pre
      (sepConj_mono_left (sepConj_mono_left (polyEncoderAt_entails_tag_vecs_tail A a st.sending_ek))) ?_
    rw [sepExists_sepConj_left, sepExists_sepConj_left]; apply ProofLib.SepWP.exists_left; intro tag
    rw [sepExists_sepConj_left, sepExists_sepConj_left]; apply ProofLib.SepWP.exists_left; intro vecs
    wp_focus_pure; intro hvecs_len; wp_steps
    refine SepWP.focus_weaken
      (stack_restore_32_allocHook s0.sp (s0.readReg64 .fp) (s0.readReg64 .lr) (s0.readReg64 .x19) w3_old)
      (by sep_focus) ?_
    wp_call hpoly16_raw ⟨a + 8#64, vecs⟩
    refine SepWP.weaken_pre
      (Entails.trans
        (Entails.of_eq (show _ = ((a ↦₆₄ tag) ∗ memRegion (a + 8#64) polyArrayBytes ∗
          memRegion (a + 392#64) 8 ∗ memRegion (a + 400#64) 104) ∗
          A.pool ∗ stackAt s0.sp dropGluePoly16Stack by ac_rfl))
        (sepConj_mono_left (chunked_400_join a tag 104 504 rfl (by decide)))) ?_
    wp_done

theorem drop_chunked_ct1_received_cl_blockProgram [LibsignalPlacement]
    {A : RustAlloc} {F : ShaCompress} {ext : String → Option (State → State)}
    (hdealloc : HookSat (Rust.withPanics ext) spqrRustDeallocSym (rustDeallocSpec A)) :
    subroutine_ok (libsignalSessionLib.blockProgram lsmpl 277 (Rust.withPanics ext)) (lsmpl.base 277)
      (withLsCodeLoaded lsmpl (dropChunkedCt1ReceivedSpec A F)) :=
  ls_to_blockProgram (drop_chunked_ct1_received_cl_placed_ok hdealloc)

theorem drop_chunked_ct1_received_cl_on [LibsignalPlacement] {A : RustAlloc} {F : ShaCompress}
    {callerProg : Program} {idx : Nat} {ext : String → Option (State → State)}
    [IsLsBlockProg callerProg idx (Rust.withPanics ext)]
    (hdealloc : HookSat (Rust.withPanics ext) spqrRustDeallocSym (rustDeallocSpec A))
    (hidx : idx < 619 := by decide) :
    subroutine_ok callerProg (lsmpl.base 277)
      (withLsCodeLoaded lsmpl (dropChunkedCt1ReceivedSpec A F)) :=
  ls_subroutine_ok_of_block (drop_chunked_ct1_received_cl_placed_ok hdealloc) hidx

theorem drop_chunked_ct1_received_mem_on [LibsignalPlacement] {A : RustAlloc} {F : ShaCompress}
    {callerProg : Program} {idx : Nat} {ext : String → Option (State → State)}
    [IsLsBlockProg callerProg idx (Rust.withPanics ext)] {m : Memory}
    (hdealloc : HookSat (Rust.withPanics ext) spqrRustDeallocSym (rustDeallocSpec A))
    (hcl : LibsignalCodeLoaded lsmpl m) (hidx : idx < 619 := by decide) :
    subroutine_ok callerProg (lsmpl.base 277)
      (withMemEq m (dropChunkedCt1ReceivedSpec A F)) :=
  lscall_blk_cl (drop_chunked_ct1_received_cl_placed_ok hdealloc) hcl hidx

/-! ## Block `278`: `drop_glue::<chunked::send_ek::EkSentCt1Received>` -/

theorem drop_chunked_ek_sent_ct1_received_cl_placed_ok [LibsignalPlacement]
    {A : RustAlloc} {F : ShaCompress} {ext : String → Option (State → State)}
    (hdealloc : HookSat (Rust.withPanics ext) spqrRustDeallocSym (rustDeallocSpec A)) :
    subroutine_ok (lsProg_278 (Rust.withPanics ext)) (lsmpl.base 278)
      (withLsCodeLoaded lsmpl (dropChunkedEkSentCt1ReceivedSpec A F)) := by
  rw [← ls_blockPlacement_base (i := 278)]
  change subroutine_ok ((blkPC_278).rebase (blkPl_278).base (Rust.withPanics ext)) (blkPl_278).base _
  apply subroutine_ok_withLsCodeLoaded_intro; intro m hcl
  have hdealloc_raw : subroutine_ok (lsProg_278 (Rust.withPanics ext))
      (lsρ spqrRustDeallocSym) (rustDeallocSpec A) := spqr_hook_ok_of_mem hdealloc
  simp only [rustDeallocSpec] at hdealloc_raw
  dsimp only [lsProg_278, withMemEq, dropChunkedEkSentCt1ReceivedSpec, chunkedEkSentCt1ReceivedSize] at hdealloc_raw ⊢
  wp_init x s0; rcases x with ⟨a, st⟩
  have hx0 : s0.readReg64 .x0 = a := by assumption
  have hm : s0.mem = m := by assumption
  subst hm
  dsimp only [DropChunkedEkSentCt1ReceivedGhost.a, DropChunkedEkSentCt1ReceivedGhost.st, chunkedEkSentCt1ReceivedAt] at *
  have hfsp_align : ((s0.sp - 32#64) &&& 15#64 == 0#64) = true :=
    spAligned_sub s0.sp 32#64 (by assumption) (by decide)
  nth_rw 1 [stackAt_dropStack32_split s0.sp]; cells_unfold; wp_pull_exists
  rename_i fp_old lr_old x19_old w3_old
  refine SepWP.weaken_pre
    (sepConj_mono_left (unchunkedEkSentCt1ReceivedAt_entails_dealloc A a st.uc)) ?_
  wp_pull_exists; rename_i g
  refine seq_clean_lscl hcl (mid := (blkPl_278).base + 96#64)
    (P_mid := (memRegion a 104 ∗ polyDecoderAt A (a + 104#64) st.receiving_ct2) ∗
      A.pool ∗ stackAt (s0.sp - 32#64) allocHookStack ∗ SavedFrameCells s0 w3_old)
    (Q := SavedMid s0 a) ?_ ?_
  · refine Drop.seq_clean (mid := (blkPl_278).base + 36#64)
      (P_mid := ((fourVec104HeadersAt a g ∗ vecCapPtrDealloc A g.v2.cap g.v2.ptr ∗
         vecCapPtrDealloc A g.v3.cap g.v3.ptr ∗ vecCapPtrDealloc A g.v4.cap g.v4.ptr) ∗
        polyDecoderAt A (a + 104#64) st.receiving_ct2) ∗
        A.pool ∗ stackAt (s0.sp - 32#64) allocHookStack ∗ SavedFrameCells s0 w3_old)
      (Q := SavedMid s0 a) ?_ ?_
    · dsimp only [fourVec104HeadersAt, vecCapPtrDealloc, SavedFrameCells, SavedMid]
      by_cases hc1 : (g.v1.cap == 0#64) = true <;>
        simp only [hc1, Bool.false_eq_true, ↓reduceIte, sepConj_emp, emp_sepConj]
      · wp_steps; refine Drop.align_pre (by dsimp only [Reg.fp, Reg.lr, Reg.x19]; ac_rfl) ?_; wp_done
      · wp_steps; wp_apply; refine Drop.align_pre (by dsimp only [Reg.fp, Reg.lr, Reg.x19]; ac_rfl) ?_; wp_done
    · intro s1 hpc1 hrun1 ⟨⟨hx20_1, hx21_1, hx22_1, hx23_1, hx24_1, hx25_1, hx26_1, hx27_1, hx28_1, hsp_1, htrace_1, hvregs_1⟩, hx19_1⟩
      refine Drop.seq_clean (mid := (blkPl_278).base + 56#64)
        (P_mid := ((fourVec104HeadersAt a g ∗ vecCapPtrDealloc A g.v3.cap g.v3.ptr ∗
           vecCapPtrDealloc A g.v4.cap g.v4.ptr) ∗
          polyDecoderAt A (a + 104#64) st.receiving_ct2) ∗
          A.pool ∗ stackAt (s0.sp - 32#64) allocHookStack ∗ SavedFrameCells s0 w3_old)
        (Q := SavedMid s0 a) ?_ ?_
      · dsimp only [fourVec104HeadersAt, vecCapPtrDealloc, SavedFrameCells, SavedMid]
        by_cases hc2 : (g.v2.cap == 0#64) = true <;>
          simp only [hc2, Bool.false_eq_true, ↓reduceIte, sepConj_emp, emp_sepConj]
        · wp_steps; wp_done
        · wp_steps; wp_apply; refine Drop.align_pre (by rw [hsp_1]; ac_rfl) ?_; wp_done
      · intro s2 hpc2 hrun2 ⟨⟨hx20_2, hx21_2, hx22_2, hx23_2, hx24_2, hx25_2, hx26_2, hx27_2, hx28_2, hsp_2, htrace_2, hvregs_2⟩, hx19_2⟩
        refine Drop.seq_clean (mid := (blkPl_278).base + 76#64)
          (P_mid := ((fourVec104HeadersAt a g ∗ vecCapPtrDealloc A g.v4.cap g.v4.ptr) ∗
            polyDecoderAt A (a + 104#64) st.receiving_ct2) ∗
            A.pool ∗ stackAt (s0.sp - 32#64) allocHookStack ∗ SavedFrameCells s0 w3_old)
          (Q := SavedMid s0 a) ?_ ?_
        · dsimp only [fourVec104HeadersAt, vecCapPtrDealloc, SavedFrameCells, SavedMid]
          by_cases hc3 : (g.v3.cap == 0#64) = true <;>
            simp only [hc3, Bool.false_eq_true, ↓reduceIte, sepConj_emp, emp_sepConj]
          · wp_steps; wp_done
          · wp_steps; wp_apply; refine Drop.align_pre (by rw [hsp_2]; ac_rfl) ?_; wp_done
        · intro s3 hpc3 hrun3 ⟨⟨hx20_3, hx21_3, hx22_3, hx23_3, hx24_3, hx25_3, hx26_3, hx27_3, hx28_3, hsp_3, htrace_3, hvregs_3⟩, hx19_3⟩
          refine SepWP.strengthen_entails_const
            (sepConj_mono_left (sepConj_mono_left (fourVec104HeadersAt_entails_memRegion_104 a g))) ?_
          change SepWP _ _ s3 _ (fun sm Pm => (Pm ⊢ (fourVec104HeadersAt a g ∗ polyDecoderAt A (a + 104#64) st.receiving_ct2) ∗
            A.pool ∗ stackAt (s0.sp - 32#64) allocHookStack ∗ SavedFrameCells s0 w3_old) ∧ SavedMid s0 a sm)
          dsimp only [fourVec104HeadersAt, vecCapPtrDealloc, SavedFrameCells, SavedMid]
          by_cases hc4 : (g.v4.cap == 0#64) = true <;>
            simp only [hc4, Bool.false_eq_true, ↓reduceIte, sepConj_emp, emp_sepConj]
          · wp_steps; wp_done
          · wp_steps; wp_apply; refine Drop.align_pre (by rw [hsp_3]; ac_rfl) ?_; wp_done
  · intro s4 hpc4 hrun4 hcl4 ⟨⟨hx20_4, hx21_4, hx22_4, hx23_4, hx24_4, hx25_4, hx26_4, hx27_4, hx28_4, hsp_4, htrace_4, hvregs_4⟩, hx19_4⟩
    have hpt16_raw := drop_glue_sorted_set_pt16_mem_on
      (callerProg := lsProg_278 (Rust.withPanics ext)) hdealloc hcl4
    dsimp only [lsProg_278, withMemEq, dropGlueSortedSetPt16Spec, SavedFrameCells] at hpt16_raw ⊢
    refine SepWP.weaken_pre
      (sepConj_mono_left (sepConj_mono_right (polyDecoderAt_entails_vecs_tail A (a + 104#64) st.receiving_ct2))) ?_
    rw [sepExists_sepConj_right, sepExists_sepConj_left]; apply ProofLib.SepWP.exists_left; intro vecs
    have h488 : (a + 104#64) + 384#64 = a + 488#64 := by bv_omega
    rw [h488]; wp_focus_pure; intro hvecs_len; wp_steps
    refine SepWP.focus_weaken
      (stack_restore_32_allocHook s0.sp (s0.readReg64 .fp) (s0.readReg64 .lr) (s0.readReg64 .x19) w3_old)
      (by sep_focus) ?_
    wp_call hpt16_raw ⟨a + 104#64, vecs⟩
    refine SepWP.weaken_pre
      (Entails.trans
        (Entails.of_eq (show _ = (memRegion a 104 ∗ memRegion (a + 104#64) polyArrayBytes ∗
          memRegion (a + 488#64) 16) ∗ A.pool ∗ stackAt s0.sp dropGluePoly16Stack by ac_rfl))
        (sepConj_mono_left (chunked_104_400_join a))) ?_
    wp_done

theorem drop_chunked_ek_sent_ct1_received_cl_blockProgram [LibsignalPlacement]
    {A : RustAlloc} {F : ShaCompress} {ext : String → Option (State → State)}
    (hdealloc : HookSat (Rust.withPanics ext) spqrRustDeallocSym (rustDeallocSpec A)) :
    subroutine_ok (libsignalSessionLib.blockProgram lsmpl 278 (Rust.withPanics ext)) (lsmpl.base 278)
      (withLsCodeLoaded lsmpl (dropChunkedEkSentCt1ReceivedSpec A F)) :=
  ls_to_blockProgram (drop_chunked_ek_sent_ct1_received_cl_placed_ok hdealloc)

theorem drop_chunked_ek_sent_ct1_received_cl_on [LibsignalPlacement] {A : RustAlloc} {F : ShaCompress}
    {callerProg : Program} {idx : Nat} {ext : String → Option (State → State)}
    [IsLsBlockProg callerProg idx (Rust.withPanics ext)]
    (hdealloc : HookSat (Rust.withPanics ext) spqrRustDeallocSym (rustDeallocSpec A))
    (hidx : idx < 619 := by decide) :
    subroutine_ok callerProg (lsmpl.base 278)
      (withLsCodeLoaded lsmpl (dropChunkedEkSentCt1ReceivedSpec A F)) :=
  ls_subroutine_ok_of_block (drop_chunked_ek_sent_ct1_received_cl_placed_ok hdealloc) hidx

theorem drop_chunked_ek_sent_ct1_received_mem_on [LibsignalPlacement] {A : RustAlloc} {F : ShaCompress}
    {callerProg : Program} {idx : Nat} {ext : String → Option (State → State)}
    [IsLsBlockProg callerProg idx (Rust.withPanics ext)] {m : Memory}
    (hdealloc : HookSat (Rust.withPanics ext) spqrRustDeallocSym (rustDeallocSpec A))
    (hcl : LibsignalCodeLoaded lsmpl m) (hidx : idx < 619 := by decide) :
    subroutine_ok callerProg (lsmpl.base 278)
      (withMemEq m (dropChunkedEkSentCt1ReceivedSpec A F)) :=
  lscall_blk_cl (drop_chunked_ek_sent_ct1_received_cl_placed_ok hdealloc) hcl hidx

/-! ## Block `276`: `drop_glue::<chunked::send_ek::HeaderSent>` -/

theorem drop_chunked_header_sent_cl_placed_ok [LibsignalPlacement]
    {A : RustAlloc} {F : ShaCompress} {ext : String → Option (State → State)}
    (hdealloc : HookSat (Rust.withPanics ext) spqrRustDeallocSym (rustDeallocSpec A)) :
    subroutine_ok (lsProg_276 (Rust.withPanics ext)) (lsmpl.base 276)
      (withLsCodeLoaded lsmpl (dropChunkedHeaderSentSpec A F)) := by
  rw [← ls_blockPlacement_base (i := 276)]
  change subroutine_ok ((blkPC_276).rebase (blkPl_276).base (Rust.withPanics ext)) (blkPl_276).base _
  apply subroutine_ok_withLsCodeLoaded_intro; intro m hcl
  have hdealloc_raw : subroutine_ok (lsProg_276 (Rust.withPanics ext))
      (lsρ spqrRustDeallocSym) (rustDeallocSpec A) := spqr_hook_ok_of_mem hdealloc
  simp only [rustDeallocSpec] at hdealloc_raw
  dsimp only [lsProg_276, withMemEq, dropChunkedHeaderSentSpec, chunkedHeaderSentSize] at hdealloc_raw ⊢
  wp_init x s0; rcases x with ⟨a, st⟩
  have hx0 : s0.readReg64 .x0 = a := by assumption
  have hm : s0.mem = m := by assumption
  subst hm
  dsimp only [DropChunkedHeaderSentGhost.a, DropChunkedHeaderSentGhost.st, chunkedHeaderSentAt] at *
  have hfsp_align : ((s0.sp - 32#64) &&& 15#64 == 0#64) = true :=
    spAligned_sub s0.sp 32#64 (by assumption) (by decide)
  have hsub_4160 : (s0.sp - 32#64) - 4128#64 = s0.sp - 4160#64 := by bv_omega
  nth_rw 1 [stackAt_dropStackPoly64_split s0.sp]
  nth_rw 1 [stackAt_dropStack32_split_bottom (s0.sp - 32#64)]
  rw [hsub_4160]; cells_unfold; wp_pull_exists; rename_i fp_old lr_old x19_old w3_old
  refine SepWP.weaken_pre
    (sepConj_mono_right (sepConj_mono_left (unchunkedEkSent400_entails_dealloc A a st.uc))) ?_
  wp_pull_exists; rename_i g
  refine seq_clean_lscl hcl (mid := (blkPl_276).base + 76#64)
    (P_mid := (polyEncoderAt A a st.sending_ek ∗ memRegion (a + 400#64) 80 ∗
      polyDecoderAt A (a + 480#64) st.receiving_ct1) ∗
      A.pool ∗ stackAt (s0.sp - 32#64) dropGluePoly16Stack ∗ SavedFrameCells s0 w3_old)
    (Q := SavedMid s0 a) ?_ ?_
  · refine Drop.seq_clean (mid := (blkPl_276).base + 36#64)
      (P_mid := (polyEncoderAt A a st.sending_ek ∗
        (threeVec400HeadersAt a g ∗ vecCapPtrDealloc A g.v2.cap g.v2.ptr ∗
         vecCapPtrDealloc A g.v3.cap g.v3.ptr) ∗
        polyDecoderAt A (a + 480#64) st.receiving_ct1) ∗ A.pool ∗
        (memRegion (s0.sp - 4160#64) 32 ∗ stackAt (s0.sp - 32#64) allocHookStack) ∗ SavedFrameCells s0 w3_old)
      (Q := SavedMid s0 a) ?_ ?_
    · dsimp only [threeVec400HeadersAt, vecCapPtrDealloc, SavedFrameCells, SavedMid]
      by_cases hc1 : (g.v1.cap == 0#64) = true <;>
        simp only [hc1, Bool.false_eq_true, ↓reduceIte, sepConj_emp, emp_sepConj]
      · wp_steps; refine Drop.align_pre (by dsimp only [Reg.fp, Reg.lr, Reg.x19]; ac_rfl) ?_; wp_done
      · wp_steps; wp_apply; refine Drop.align_pre (by dsimp only [Reg.fp, Reg.lr, Reg.x19]; ac_rfl) ?_; wp_done
    · intro s1 hpc1 hrun1 ⟨⟨hx20_1, hx21_1, hx22_1, hx23_1, hx24_1, hx25_1, hx26_1, hx27_1, hx28_1, hsp_1, htrace_1, hvregs_1⟩, hx19_1⟩
      refine Drop.seq_clean (mid := (blkPl_276).base + 56#64)
        (P_mid := (polyEncoderAt A a st.sending_ek ∗
          (threeVec400HeadersAt a g ∗ vecCapPtrDealloc A g.v3.cap g.v3.ptr) ∗
          polyDecoderAt A (a + 480#64) st.receiving_ct1) ∗ A.pool ∗
          (memRegion (s0.sp - 4160#64) 32 ∗ stackAt (s0.sp - 32#64) allocHookStack) ∗ SavedFrameCells s0 w3_old)
        (Q := SavedMid s0 a) ?_ ?_
      · dsimp only [threeVec400HeadersAt, vecCapPtrDealloc, SavedFrameCells, SavedMid]
        by_cases hc2 : (g.v2.cap == 0#64) = true <;>
          simp only [hc2, Bool.false_eq_true, ↓reduceIte, sepConj_emp, emp_sepConj]
        · wp_steps; wp_done
        · wp_steps; wp_apply; refine Drop.align_pre (by rw [hsp_1]; dsimp only [Reg.fp, Reg.lr, Reg.x19]; ac_rfl) ?_; wp_done
      · intro s2 hpc2 hrun2 ⟨⟨hx20_2, hx21_2, hx22_2, hx23_2, hx24_2, hx25_2, hx26_2, hx27_2, hx28_2, hsp_2, htrace_2, hvregs_2⟩, hx19_2⟩
        have hstack_join : memRegion (s0.sp - 4160#64) 32 ∗ stackAt (s0.sp - 32#64) allocHookStack ⊢
            stackAt (s0.sp - 32#64) dropGluePoly16Stack := by
          rw [← hsub_4160]; exact Entails.of_eq (stackAt_dropStack32_split_bottom (s0.sp - 32#64)).symm
        refine SepWP.strengthen_entails_const
          (sepConj_mono
            (sepConj_mono_right (sepConj_mono_left (threeVec400HeadersAt_entails_memRegion_80 a g)))
            (sepConj_mono_right (sepConj_mono_left hstack_join))) ?_
        change SepWP _ _ s2 _ (fun sm Pm => (Pm ⊢ (polyEncoderAt A a st.sending_ek ∗ threeVec400HeadersAt a g ∗
          polyDecoderAt A (a + 480#64) st.receiving_ct1) ∗ A.pool ∗
          (memRegion (s0.sp - 4160#64) 32 ∗ stackAt (s0.sp - 32#64) allocHookStack) ∗ SavedFrameCells s0 w3_old) ∧
          SavedMid s0 a sm)
        dsimp only [threeVec400HeadersAt, vecCapPtrDealloc, SavedFrameCells, SavedMid]
        by_cases hc3 : (g.v3.cap == 0#64) = true <;>
          simp only [hc3, Bool.false_eq_true, ↓reduceIte, sepConj_emp, emp_sepConj]
        · wp_steps; wp_done
        · wp_steps; wp_apply; refine Drop.align_pre (by rw [hsp_2]; dsimp only [Reg.fp, Reg.lr, Reg.x19]; ac_rfl) ?_; wp_done
  · intro s3 hpc3 hrun3 hcl3 ⟨⟨hx20_3, hx21_3, hx22_3, hx23_3, hx24_3, hx25_3, hx26_3, hx27_3, hx28_3, hsp_3, htrace_3, hvregs_3⟩, hx19_3⟩
    refine seq_clean_lscl hcl3 (mid := (blkPl_276).base + 84#64)
      (P_mid := (memRegion a 480 ∗ polyDecoderAt A (a + 480#64) st.receiving_ct1) ∗
        A.pool ∗ stackAt (s0.sp - 32#64) dropGluePoly16Stack ∗ SavedFrameCells s0 w3_old)
      (Q := SavedMid s0 a) ?_ ?_
    · have hpoly16_raw := drop_glue_poly16_mem_on
        (callerProg := lsProg_276 (Rust.withPanics ext)) hdealloc hcl3
      dsimp only [lsProg_276, withMemEq, dropGluePoly16Spec, SavedFrameCells, SavedMid] at hpoly16_raw ⊢
      refine SepWP.weaken_pre
        (sepConj_mono_left (sepConj_mono_left (polyEncoderAt_entails_tag_vecs_tail A a st.sending_ek))) ?_
      rw [sepExists_sepConj_left, sepExists_sepConj_left]; apply ProofLib.SepWP.exists_left; intro tag
      rw [sepExists_sepConj_left, sepExists_sepConj_left]; apply ProofLib.SepWP.exists_left; intro vecs
      wp_focus_pure; intro hvecs_len; wp_steps
      wp_call hpoly16_raw ⟨a + 8#64, vecs⟩
      refine SepWP.weaken_pre
        (Entails.trans
          (Entails.of_eq (show _ = (((a ↦₆₄ tag) ∗ memRegion (a + 8#64) polyArrayBytes ∗
            memRegion (a + 392#64) 8 ∗ memRegion (a + 400#64) 80) ∗
            polyDecoderAt A (a + 480#64) st.receiving_ct1) ∗ A.pool ∗
            stackAt (s0.sp - 32#64) dropGluePoly16Stack ∗ SavedFrameCells s0 w3_old by
            dsimp only [SavedFrameCells]; rw [hsp_3]; ac_rfl))
          (sepConj_mono_left (sepConj_mono_left (chunked_400_join a tag 80 480 rfl (by decide))))) ?_
      wp_done
    · intro s4 hpc4 hrun4 hcl4 ⟨⟨hx20_4, hx21_4, hx22_4, hx23_4, hx24_4, hx25_4, hx26_4, hx27_4, hx28_4, hsp_4, htrace_4, hvregs_4⟩, hx19_4⟩
      have hpt16_raw := drop_glue_sorted_set_pt16_mem_on
        (callerProg := lsProg_276 (Rust.withPanics ext)) hdealloc hcl4
      dsimp only [lsProg_276, withMemEq, dropGlueSortedSetPt16Spec, SavedFrameCells] at hpt16_raw ⊢
      refine SepWP.weaken_pre
        (sepConj_mono_left (sepConj_mono_right (polyDecoderAt_entails_vecs_tail A (a + 480#64) st.receiving_ct1))) ?_
      rw [sepExists_sepConj_right, sepExists_sepConj_left]; apply ProofLib.SepWP.exists_left; intro vecs
      have h864 : (a + 480#64) + 384#64 = a + 864#64 := by bv_omega
      rw [h864]; wp_focus_pure; intro hvecs_len; wp_steps
      refine SepWP.focus_weaken
        (Entails.trans
          (stack_restore_64_dropStack32 s0.sp (s0.readReg64 .fp) (s0.readReg64 .lr) (s0.readReg64 .x19) w3_old)
          (Entails.of_eq (stackAt_dropStackPoly64_split_bottom s0.sp)))
        (by sep_focus) ?_
      wp_call hpt16_raw ⟨a + 480#64, vecs⟩
      have hstack64_join : memRegion (s0.sp - 4160#64) 32 ∗ stackAt s0.sp dropGluePoly16Stack ⊢
          stackAt s0.sp dropStackPoly64 :=
        Entails.of_eq (stackAt_dropStackPoly64_split_bottom s0.sp).symm
      refine SepWP.weaken_pre
        (Entails.trans
          (Entails.of_eq (show _ = (memRegion a 480 ∗ memRegion (a + 480#64) polyArrayBytes ∗
            memRegion (a + 864#64) 16) ∗ A.pool ∗
            (memRegion (s0.sp - 4160#64) 32 ∗ stackAt s0.sp dropGluePoly16Stack) by ac_rfl))
          (sepConj_mono (chunked_880_join a) (sepConj_mono_right hstack64_join))) ?_
      wp_done

theorem drop_chunked_header_sent_cl_blockProgram [LibsignalPlacement]
    {A : RustAlloc} {F : ShaCompress} {ext : String → Option (State → State)}
    (hdealloc : HookSat (Rust.withPanics ext) spqrRustDeallocSym (rustDeallocSpec A)) :
    subroutine_ok (libsignalSessionLib.blockProgram lsmpl 276 (Rust.withPanics ext)) (lsmpl.base 276)
      (withLsCodeLoaded lsmpl (dropChunkedHeaderSentSpec A F)) :=
  ls_to_blockProgram (drop_chunked_header_sent_cl_placed_ok hdealloc)

theorem drop_chunked_header_sent_cl_on [LibsignalPlacement] {A : RustAlloc} {F : ShaCompress}
    {callerProg : Program} {idx : Nat} {ext : String → Option (State → State)}
    [IsLsBlockProg callerProg idx (Rust.withPanics ext)]
    (hdealloc : HookSat (Rust.withPanics ext) spqrRustDeallocSym (rustDeallocSpec A))
    (hidx : idx < 619 := by decide) :
    subroutine_ok callerProg (lsmpl.base 276)
      (withLsCodeLoaded lsmpl (dropChunkedHeaderSentSpec A F)) :=
  ls_subroutine_ok_of_block (drop_chunked_header_sent_cl_placed_ok hdealloc) hidx

theorem drop_chunked_header_sent_mem_on [LibsignalPlacement] {A : RustAlloc} {F : ShaCompress}
    {callerProg : Program} {idx : Nat} {ext : String → Option (State → State)}
    [IsLsBlockProg callerProg idx (Rust.withPanics ext)] {m : Memory}
    (hdealloc : HookSat (Rust.withPanics ext) spqrRustDeallocSym (rustDeallocSpec A))
    (hcl : LibsignalCodeLoaded lsmpl m) (hidx : idx < 619 := by decide) :
    subroutine_ok callerProg (lsmpl.base 276)
      (withMemEq m (dropChunkedHeaderSentSpec A F)) :=
  lscall_blk_cl (drop_chunked_header_sent_cl_placed_ok hdealloc) hcl hidx

end CryptoVerification.SpqrV1.States.Recv
