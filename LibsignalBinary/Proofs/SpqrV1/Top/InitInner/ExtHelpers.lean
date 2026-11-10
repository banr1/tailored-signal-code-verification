/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SpqrV1.Top.InitInner.Steps
import all Init.Data.String.Defs
import all Init.Data.String.Pattern.Basic
import all Init.Data.String.Pattern.String
import all Init.Data.String.Slice
import all Init.Data.String.TakeDrop
import GeneratedLean.LibsignalSessionCode -- shake: keep
import LibsignalBinary.Proofs.SpqrV1.Layout.Stubs
import LibsignalBinary.Proofs.SpqrV1.Poly.DecoderPb.IntoPbProof
import LibsignalBinary.Proofs.SpqrV1.States.IntoPb.Part4
import LibsignalBinary.Proofs.SpqrV1.States.IntoPb.Part4a
import ProofLib.SepLogic.WPp

/-!
# Helpers & 4K-Hook `into_pb` Lemmas for `spqr::init_inner` (`0x532dc`)

Provides stack-frame split helpers, stack-slack monotonicity lifts (`17680`B to `18912`B),
and 4K-hook `<PolyDecoder>::into_pb` / `<States>::into_pb` proofs on `initV1State`.
-/

@[expose] public section

set_option autoImplicit false

namespace CryptoVerification.SpqrV1.Top.InitInner

open Arm64 ProofLib ProofLib.ProgramReflection
open CryptoGames.LibsignalSession (ShaCompress)
open CryptoVerification.RustHeap
open CryptoVerification.LibsignalSession
open CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalTripleRatchetRepr
open CryptoVerification.LibsignalSpqrV1
open CryptoVerification.SpqrV1.Auth
open CryptoVerification.SpqrV1.Poly
open CryptoVerification.SpqrV1.Poly.DecoderPb
open CryptoVerification.SpqrV1.Drop
open CryptoVerification.SpqrV1.ProtoRepr
open CryptoVerification.SpqrV1.States.IntoPb
open CryptoVerification.CodeLayout

set_option maxRecDepth 200000
set_option maxHeartbeats 400000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

attribute [local irreducible] Program.fetch Program.externAt? Program.fnOff
attribute [local arm64_norm, local wp_norm] bv_sub_add_lit BitVec.toNat_zero
  bv_sub_sub_lit' bv_add_add_lit' sessionMemcpySpec libcMemcpySpec

ls_attribute [local simp, local arm64_norm ↓, local wp_norm ↓]
  (ls_lemma% fnOff "spqr::init_inner")
  (ls_lemma% fnOff "<spqr::authenticator::Authenticator>::new")
  (ls_lemma% fnOff "<spqr::v1::chunked::states::States>::into_pb")
  (ls_lemma% fnOff "<spqr::encoding::polynomial::PolyDecoder>::into_pb")
  (ls_stub% "__rustc::__rust_no_alloc_shim_is_unstable_v2")
  (ls_stub% "__rustc::__rust_alloc")
  (ls_stub% "__rustc::__rust_dealloc")
  (ls_stub% "memcpy")
  (ls_stub% "alloc::raw_vec::handle_error")

/-! ## 1. Relative Call-Address Helpers & Stack Monotonicity (`+1232`B) -/

theorem fnAddr_rel64_ext {b : BitVec 64} {H : String → Option (State → State)}
    {caller callee : String} {o1 o2 : Nat} {rel : BitVec 64}
    (h1 : libsignalSessionCode.fnOff caller = o1)
    (h2 : libsignalSessionCode.fnOff callee = o2)
    (hrel : BitVec.ofNat 64 o1 + rel = BitVec.ofNat 64 o2) :
    (libsignalSessionCode.rebase b H).fnAddr caller + rel =
      (libsignalSessionCode.rebase b H).fnAddr callee := by
  rw [Program.fnAddr_rebase, Program.fnAddr_rebase, h1, h2, BitVec.add_assoc, hrel]

theorem stackAt_initInnerExt_split_base (sp : BitVec 64) :
    stackAt sp initInnerStackExt =
      stackAt sp initInnerStack ∗ memRegion (sp - 18912#64) 1232 := by
  change memRegion (sp - 18912#64) 18912 =
    memRegion (sp - 17680#64) 17680 ∗ memRegion (sp - 18912#64) 1232
  rw [ProofLib.memRegion_split' (b := sp - 18912#64) (n := 1232) (k := 17680)
        (b' := sp - 17680#64) rfl (by bv_omega) (by decide), sepConj_comm]

theorem stackAt_initInnerExt_split (sp : BitVec 64) :
    stackAt sp initInnerStackExt =
      stackAt (sp - 1040#64) authNewStackExt ∗
      memRegion (sp - 1040#64) 992 ∗
      cells (sp - 48#64) 6 := by
  change memRegion (sp - 18912#64) 18912 =
    memRegion ((sp - 1040#64) - 17872#64) 17872 ∗
    memRegion (sp - 1040#64) 992 ∗
    cells (sp - 48#64) 6
  have hsub : (sp - 1040#64) - 17872#64 = sp - 18912#64 := by bv_omega
  rw [hsub,
      ProofLib.memRegion_split' (b := sp - 18912#64) (n := 17872) (k := 1040)
        (b' := sp - 1040#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := sp - 1040#64) (n := 992) (k := 48)
        (b' := sp - 48#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_cells (sp - 48#64) 6 (by decide)]

theorem stack_restore_initInnerExt (s0 : State) :
    stackAt (s0.sp - 1040#64) authNewStackExt ∗
    memRegion (s0.sp - 1040#64) 992 ∗
    initInnerSavedCells s0 ⊢
    stackAt s0.sp initInnerStackExt := by
  rw [stackAt_initInnerExt_split s0.sp, ← ProofLib.memRegion_cells (s0.sp - 48#64) 6 (by decide)]
  exact sepConj_mono_right (sepConj_mono_right (initInnerSavedCells_entails_memRegion s0))

theorem stackAt_authNewExt_split_authNewX (sp : BitVec 64) :
    stackAt sp authNewStackExt =
      stackAt sp authNewStackX ∗ memRegion (sp - 17872#64) 1232 := by
  change memRegion (sp - 17872#64) 17872 =
    memRegion (sp - 16640#64) 16640 ∗ memRegion (sp - 17872#64) 1232
  rw [ProofLib.memRegion_split' (b := sp - 17872#64) (n := 1232) (k := 16640)
        (b' := sp - 16640#64) rfl (by bv_omega) (by decide), sepConj_comm]

theorem stackAt_authNewExt_split_statesIntoPb (sp : BitVec 64) :
    stackAt sp authNewStackExt =
      stackAt sp statesIntoPbStack ∗ memRegion (sp - 17872#64) 12000 := by
  change memRegion (sp - 17872#64) 17872 =
    memRegion (sp - 5872#64) 5872 ∗ memRegion (sp - 17872#64) 12000
  rw [ProofLib.memRegion_split' (b := sp - 17872#64) (n := 12000) (k := 5872)
        (b' := sp - 5872#64) rfl (by bv_omega) (by decide), sepConj_comm]

theorem stackAt_authNewExt_split_allocHook (sp : BitVec 64) :
    stackAt sp authNewStackExt =
      stackAt sp allocHookStack ∗ memRegion (sp - 17872#64) 13776 := by
  change memRegion (sp - 17872#64) 17872 =
    memRegion (sp - 4096#64) 4096 ∗ memRegion (sp - 17872#64) 13776
  rw [ProofLib.memRegion_split' (b := sp - 17872#64) (n := 13776) (k := 4096)
        (b' := sp - 4096#64) rfl (by bv_omega) (by decide), sepConj_comm]

/-- Stack-slack monotonicity: `InitInnerOkExt` (`17680`B) implies `InitInnerBaseOkExt` (`18912`B). -/
theorem InitInnerOkExt.toBaseExt {b : BitVec 64} {A : RustAlloc} {F : ShaCompress}
    {ext : String → Option (State → State)} (h : InitInnerOkExt b A F ext) :
    InitInnerBaseOkExt b A F ext := by
  apply subroutine_ok_outcome_intro
  intro x R s0 hpc hrun hpre hal
  let F_stk : SepProp := memRegion (s0.sp - 18912#64) 1232
  have hpre' : s0.mem ⊨ (initInnerSpec A F b).pre x s0 ∗ (F_stk ∗ R) := by
    dsimp only [initInnerSpecExt] at hpre
    dsimp only [initInnerSpec, F_stk]
    rw [stackAt_initInnerExt_split_base s0.sp] at hpre
    exact Satisfies.mono (Entails.of_eq (by ac_rfl)) hpre
  refine (h.to_outcome x (F_stk ∗ R) s0 hpc hrun hpre' hal).mono_outcome fun sf hout => ?_
  rcases hout with ⟨hret, hpres, hpost⟩ | ⟨hpan, hpost⟩ | ⟨_, _, hpost⟩ | ⟨_, hpost⟩
  · refine Or.inl ⟨hret, hpres, ?_⟩
    dsimp only [initInnerSpec, F_stk] at hpost
    dsimp only [initInnerSpecExt]
    rw [stackAt_initInnerExt_split_base s0.sp]
    exact Satisfies.mono (Entails.of_eq (by ac_rfl)) hpost
  · refine Or.inr (Or.inl ⟨hpan, ?_⟩)
    dsimp only [initInnerSpec, initInnerSpecExt, initInnerOnPanic, F_stk] at hpost ⊢
    have hpost' : sf.mem ⊨ ((⌜allocFailedIn s0 sf ∧ s0.trace <+: sf.trace⌝ ∗ anyHeap) ∗
        memRegion (s0.sp - 18912#64) 1232) ∗ R :=
      Satisfies.mono (Entails.of_eq (by ac_rfl)) hpost
    simpa only [sepConj_assoc] using ProofLib.allowPanic_frame id hpost'
  · exact (ProofLib.allowPanic_not_exited hpost).elim
  · exact (not_satisfies_false_sepConj hpost).elim

/-- Stack-slack monotonicity: `InitInnerOkX` (`17680`B) implies `InitInnerOkXExt` (`18912`B). -/
theorem InitInnerOkX.toExt {img : Obj.Image} {A : RustAlloc} {F : ShaCompress}
    {ext : String → Option (State → State)} (h : InitInnerOkX img A F ext) :
    InitInnerOkXExt img A F ext := by
  apply subroutine_ok_outcome_intro
  intro x R s0 hpc hrun hpre hal
  let F_stk : SepProp := memRegion (s0.sp - 18912#64) 1232
  have hpre' : s0.mem ⊨ ((initInnerSpecX A F img.base).inImage img).pre x s0 ∗ (F_stk ∗ R) := by
    dsimp only [Spec.inImage, initInnerSpecExt] at hpre
    dsimp only [Spec.inImage, initInnerSpecX, initInnerSpec, F_stk]
    rw [stackAt_initInnerExt_split_base s0.sp] at hpre
    exact Satisfies.mono (Entails.of_eq (by ac_rfl)) hpre
  refine (h.to_outcome x (F_stk ∗ R) s0 hpc hrun hpre' hal).mono_outcome fun sf hout => ?_
  rcases hout with ⟨hret, hpres, hpost⟩ | ⟨hpan, hpost⟩ | ⟨_, _, hpost⟩ | ⟨_, hpost⟩
  · refine Or.inl ⟨hret, hpres, ?_⟩
    dsimp only [Spec.inImage, initInnerSpecX, initInnerSpec, F_stk] at hpost
    dsimp only [Spec.inImage, initInnerSpecExt]
    rw [stackAt_initInnerExt_split_base s0.sp]
    exact Satisfies.mono (Entails.of_eq (by ac_rfl)) hpost
  · refine Or.inr (Or.inl ⟨hpan, ?_⟩)
    dsimp only [Spec.inImage, initInnerSpecX, initInnerSpec, initInnerSpecExt, initInnerOnPanic, F_stk] at hpost ⊢
    have hpost' : sf.mem ⊨ ((⌜allocFailedIn s0 sf ∧ s0.trace <+: sf.trace⌝ ∗ anyHeap) ∗
        memRegion (s0.sp - 18912#64) 1232) ∗ R :=
      Satisfies.mono (Entails.of_eq (by ac_rfl)) hpost
    simpa only [sepConj_assoc] using ProofLib.allowPanic_frame id hpost'
  · exact (ProofLib.allowPanic_not_exited hpost).elim
  · exact (not_satisfies_false_sepConj hpost).elim

/-! ## 2. 4K-Hook `<PolyDecoder>::into_pb` & `<States>::into_pb` on `initV1State` -/

private theorem sub_ok_decoder_drop_pt16 {A : RustAlloc} {b : BitVec 64}
    {ext : String → Option (State → State)} (hdealloc : DeallocOkExt b A ext) :
    subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr decoderIntoPbName +
        bv% (2 ^ 64 - ls_rel%
          "core::ptr::drop_glue::<[sorted_vec::SortedSet<spqr::encoding::polynomial::Pt>; 16]>"
          "<spqr::encoding::polynomial::PolyDecoder>::into_pb"))
      (dropGlueSortedSetPt16Spec A) := by
  have h := Drop.drop_glue_sorted_set_pt16_ok_ext hdealloc
  unfold dropProgAtExt at h
  exact sub_ok_of_addr_eq
    (fnAddr_rel64_ext (b := b) (H := Rust.withPanics ext)
      (rel := bv% (2 ^ 64 - ls_rel%
        "core::ptr::drop_glue::<[sorted_vec::SortedSet<spqr::encoding::polynomial::Pt>; 16]>"
        "<spqr::encoding::polynomial::PolyDecoder>::into_pb"))
      (ls_lemma% fnOff "<spqr::encoding::polynomial::PolyDecoder>::into_pb")
      dropSortedSetPt16_fnOff (by decide)).symm h

private theorem decoder_into_pb_ok_of_sub {b : BitVec 64} {A : RustAlloc}
    {ext : String → Option (State → State)}
    (halloc : subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr allocName) (rustAllocSpec A))
    (hdealloc : DeallocOkExt b A ext)
    (hshim : subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr shimName) sessionShimSpec) :
    DecoderIntoPbOkExt b A ext := by
  unfold DecoderIntoPbOkExt
  have hshim_raw := sub_ok_of_addr_eq
    (fnAddr_rel64_ext (b := b) (H := Rust.withPanics ext)
      (rel := bv% (ls_rel% "<spqr::encoding::polynomial::PolyDecoder>::into_pb"
        "__rustc::__rust_no_alloc_shim_is_unstable_v2"))
      (ls_lemma% fnOff "<spqr::encoding::polynomial::PolyDecoder>::into_pb")
      (ls_stub% "__rustc::__rust_no_alloc_shim_is_unstable_v2") (by decide)).symm hshim
  have halloc_raw := sub_ok_of_addr_eq
    (fnAddr_rel64_ext (b := b) (H := Rust.withPanics ext)
      (rel := bv% (ls_rel% "<spqr::encoding::polynomial::PolyDecoder>::into_pb"
        "__rustc::__rust_alloc"))
      (ls_lemma% fnOff "<spqr::encoding::polynomial::PolyDecoder>::into_pb")
      (ls_stub% "__rustc::__rust_alloc") (by decide)).symm halloc
  have hdrop := sub_ok_decoder_drop_pt16 hdealloc
  apply subroutine_ok_of_sepWPp
  intro ⟨out, decA, dec⟩ R s0 hpc hrun hpre hsp0
  simp only [decoderIntoPbSpec, sepConj_assoc, satisfies_pure_sepConj] at hpre
  rcases hpre with ⟨⟨hx0, hx1⟩, hmem⟩
  refine ⟨memRegion out protoPolynomialDecoderSize ∗
      polyDecoderAt A decA dec ∗
      A.pool ∗ stackAt s0.sp decoderIntoPbStack,
    R, ?_, ?_⟩
  · simpa [sepConj_assoc] using hmem
  dsimp only [decoderIntoPbSpec, polyDecoderAt, polyDecoderPtsNeededOff, polyDecoderIsCompleteOff,
    polyDecoderPadOff, polyDecoderPadSize, protoPolynomialDecoderSize, polyDecoderSize,
    BitVec.ofNat_eq_ofNat] at *
  let fsp := s0.sp - 160#64
  have hfsp : DecoderPb.HiddenEq fsp (s0.sp - 160#64) := ⟨rfl⟩
  have hfsp_align : (fsp &&& 15#64 == 0#64) = true :=
    spAligned_sub s0.sp 160#64 hsp0 (by decide)
  conv => arg 4; rw [stackAt_decoderIntoPb_split s0.sp, ← hfsp.eq, DecoderPb.stackAt_dropGluePoly16_split_bottom fsp]
  conv => arg 4; simp only [sepConj_assoc]
  refine SepWPp.weaken_pre (P' :=
      ⌜dec.pts.length = NUM_POLYS ∧ dec.ptsNeeded < 2 ^ 64⌝ ∗
      memRegion out 40 ∗ cells fsp 20 ∗
      sortedSetPtListOf A decA dec.pts ∗
      ((decA + 384#64) ↦₆₄ BitVec.ofNat 64 dec.ptsNeeded) ∗
      ((decA + 392#64) ↦₈ boolByte dec.isComplete) ∗
      memRegion (decA + 393#64) 7 ∗
      A.pool ∗ memRegion (fsp - 4128#64) 32 ∗ stackAt fsp allocHookStack)
    (Entails.of_eq (by ac_rfl)) ?_
  refine DecoderPb.sepWPp_elim_pure fun ⟨hpts_len, _⟩ => ?_
  rw [sortedSetPtListOf_eq_vecPtListOf]
  conv => arg 4; simp only [memRegion_40_split out, cells20_fsp_eq fsp, sepConj_assoc, sepExists_sepConj_left]
  conv => arg 4; simp only [sepExists_sepConj_right, sepConj_assoc]
  refine SepWPp.exists_elim fun d0 => SepWPp.exists_elim fun d1 => SepWPp.exists_elim fun d2 =>
    SepWPp.exists_elim fun d3 => SepWPp.exists_elim fun d4 => SepWPp.exists_elim fun v0 =>
    SepWPp.exists_elim fun v1 => SepWPp.exists_elim fun v2 => SepWPp.exists_elim fun v3 =>
    SepWPp.exists_elim fun v4 => SepWPp.exists_elim fun v5 => SepWPp.exists_elim fun v6 =>
    SepWPp.exists_elim fun v7 => SepWPp.exists_elim fun v8 => SepWPp.exists_elim fun v9 =>
    SepWPp.exists_elim fun v10 => SepWPp.exists_elim fun v11 => SepWPp.exists_elim fun v12 =>
    SepWPp.exists_elim fun v13 => SepWPp.exists_elim fun v14 => SepWPp.exists_elim fun v15 =>
    SepWPp.exists_elim fun v16 => SepWPp.exists_elim fun v17 => SepWPp.exists_elim fun v18 =>
    SepWPp.exists_elim fun v19 => ?_
  refine SepWPp.weaken_pre (Entails.of_eq (by ac_rfl))
    (into_pb_prologue_and_init hshim_raw halloc_raw s0 fsp out decA hfsp hfsp_align
      dec.ptsNeeded dec.isComplete
      v0 v1 v2 v3 v4 v8 v9 v10 v12 v13 v14 v15 v16 v17 v18 v19
      (vecPtListOf A decA (dec.pts.map SortedSetPt.vec) ∗
        (out ↦₆₄ d0) ∗ ((out + 8#64) ↦₆₄ d1) ∗ ((out + 16#64) ↦₆₄ d2) ∗
        ((out + 24#64) ↦₆₄ d3) ∗ ((out + 32#64) ↦₆₄ d4) ∗
        ((fsp + 40#64) ↦₆₄ v5) ∗ ((fsp + 48#64) ↦₆₄ v6) ∗ ((fsp + 56#64) ↦₆₄ v7) ∗
        ((fsp + 88#64) ↦₆₄ v11) ∗
        memRegion (fsp - 4128#64) 32)
      ‹_› ‹_› ‹_› ‹_› ?_)
  intro s1 ptr_pts hptr_pts hpc1 hrun1 hsp1 hx29_1 hx19_1 hx20_1 hx22_1 hx23_1 hx24_1 hx28_1 htr1 hvregs1
  let s_ref := withSaved19_20 s0 decA out
  have hrem_len : (dec.pts.map SortedSetPt.vec).length = 16 := by
    simp [hpts_len, NUM_POLYS, CHUNK_SIZE]
  have hrem_ne : dec.pts.map SortedSetPt.vec ≠ [] := by
    intro h; simp [h] at hrem_len
  generalize hQ_goal : (fun (sf : State) (P_f : SepProp) => _ ∧ sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf) = Q_goal
  have hloop := pts_outer_loop (R := R) (Q := Q_goal) hshim_raw halloc_raw s_ref fsp ptr_pts hfsp_align
    (dec.pts.map SortedSetPt.vec) hrem_ne 0 (by omega) v5 v6 v7 s1
    (((fsp + 24#64) ↦₃₂ BitVec.ofNat 32 dec.ptsNeeded) ∗ ((fsp + 28#64) ↦₃₂ 16#32) ∗
      ((fsp + 32#64) ↦₈ boolByte dec.isComplete) ∗ ((fsp + 33#64) ↦ₛ (unpack64 v4).tail) ∗
      ((fsp + 64#64) ↦₆₄ s0.readReg64 .x29) ∗ ((fsp + 72#64) ↦₆₄ s0.readReg64 .x30) ∗
      ((fsp + 80#64) ↦₆₄ s0.readReg64 .x27) ∗ ((fsp + 88#64) ↦₆₄ v11) ∗
      ((fsp + 96#64) ↦₆₄ s0.readReg64 .x26) ∗ ((fsp + 104#64) ↦₆₄ s0.readReg64 .x25) ∗
      ((fsp + 112#64) ↦₆₄ s0.readReg64 .x24) ∗ ((fsp + 120#64) ↦₆₄ s0.readReg64 .x23) ∗
      ((fsp + 128#64) ↦₆₄ s0.readReg64 .x22) ∗ ((fsp + 136#64) ↦₆₄ s0.readReg64 .x21) ∗
      ((fsp + 144#64) ↦₆₄ s0.readReg64 .x20) ∗ ((fsp + 152#64) ↦₆₄ s0.readReg64 .x19) ∗
      (out ↦₆₄ d0) ∗ ((out + 8#64) ↦₆₄ d1) ∗ ((out + 16#64) ↦₆₄ d2) ∗
      ((out + 24#64) ↦₆₄ d3) ∗ ((out + 32#64) ↦₆₄ d4) ∗
      memRegion (decA + 384#64) 16 ∗
      A.live ptr_pts 384 8 ∗
      memRegion (fsp - 4128#64) 32)
    hpc1 hrun1 hsp1 hx29_1
    (by simpa [s_ref] using hx19_1)
    (by simpa [s_ref] using hx20_1)
    hx22_1 hx23_1 hx24_1
    (by simpa [s_ref] using hx28_1)
    (by simpa [s_ref] using htr1)
    (by simpa [s_ref] using hvregs1)
  dsimp only [s_ref] at hloop
  simp only [withSaved19_20_lr, withSaved19_20_x19, withSaved19_20_x20, withSaved19_20_x28,
    withSaved19_20_trace, withSaved19_20_vregs, withSaved19_20_onPanic, Nat.mul_zero, BitVec.ofNat_eq_ofNat,
    BitVec.add_zero, hrem_len] at hloop
  change _ → SepWPp _ _ _ _ _ _ at hloop
  refine SepWPp.weaken_pre (by dsimp only [vecPtListOf]; exact Entails.of_eq (by ac_rfl)) (hloop ?_)
  intro s2 w40 w48 w56 hpc2 hrun2 hsp2 hx29_2 hx19_2 hx20_2 hx28_2 htr2 hvregs2
  have hep := into_pb_epilogue hdrop s0 fsp out decA hfsp
    (BitVec.ofNat 32 dec.ptsNeeded) 16#32 v4 (boolByte dec.isComplete)
    hfsp_align (dec.pts.map SortedSetPt.vec) (by simp [hpts_len])
    16#64 ptr_pts 16#64 w40 w48 w56 v11
    d0 d1 d2 d3 d4 s2
    (arrayAt (fun bs addr => vecU8 A addr bs) 24 ptr_pts
        ((dec.pts.map SortedSetPt.vec).map serializePtList) ∗
      A.live ptr_pts 384 8)
    hpc2 hrun2 hsp2 hx29_2 hx19_2 hx20_2 htr2 hvregs2
  have hpre2 :
      ((fsp ↦₆₄ 16#64) ∗ ((fsp + 8#64) ↦₆₄ ptr_pts) ∗ ((fsp + 16#64) ↦₆₄ 16#64) ∗
        ((fsp + 40#64) ↦₆₄ w40) ∗ ((fsp + 48#64) ↦₆₄ w48) ∗ ((fsp + 56#64) ↦₆₄ w56) ∗
        arrayAt (fun pts addr => vecPtOf A addr pts) 24 decA (dec.pts.map SortedSetPt.vec) ∗
        arrayAt (fun bs addr => vecU8 A addr bs) 24 ptr_pts
          ((dec.pts.map SortedSetPt.vec).map serializePtList) ∗
        A.pool ∗ stackAt fsp allocHookStack ∗
        (((fsp + 24#64) ↦₃₂ BitVec.ofNat 32 dec.ptsNeeded) ∗ ((fsp + 28#64) ↦₃₂ 16#32) ∗
          ((fsp + 32#64) ↦₈ boolByte dec.isComplete) ∗ ((fsp + 33#64) ↦ₛ (unpack64 v4).tail) ∗
          ((fsp + 64#64) ↦₆₄ s0.readReg64 .x29) ∗ ((fsp + 72#64) ↦₆₄ s0.readReg64 .x30) ∗
          ((fsp + 80#64) ↦₆₄ s0.readReg64 .x27) ∗ ((fsp + 88#64) ↦₆₄ v11) ∗
          ((fsp + 96#64) ↦₆₄ s0.readReg64 .x26) ∗ ((fsp + 104#64) ↦₆₄ s0.readReg64 .x25) ∗
          ((fsp + 112#64) ↦₆₄ s0.readReg64 .x24) ∗ ((fsp + 120#64) ↦₆₄ s0.readReg64 .x23) ∗
          ((fsp + 128#64) ↦₆₄ s0.readReg64 .x22) ∗ ((fsp + 136#64) ↦₆₄ s0.readReg64 .x21) ∗
          ((fsp + 144#64) ↦₆₄ s0.readReg64 .x20) ∗ ((fsp + 152#64) ↦₆₄ s0.readReg64 .x19) ∗
          (out ↦₆₄ d0) ∗ ((out + 8#64) ↦₆₄ d1) ∗ ((out + 16#64) ↦₆₄ d2) ∗
          ((out + 24#64) ↦₆₄ d3) ∗ ((out + 32#64) ↦₆₄ d4) ∗
          memRegion (decA + 384#64) 16 ∗
          A.live ptr_pts 384 8 ∗
          memRegion (fsp - 4128#64) 32)) ⊢
      ((fsp ↦₆₄ 16#64) ∗ ((fsp + 8#64) ↦₆₄ ptr_pts) ∗ ((fsp + 16#64) ↦₆₄ 16#64) ∗
        ((fsp + 24#64) ↦₃₂ BitVec.ofNat 32 dec.ptsNeeded) ∗ ((fsp + 28#64) ↦₃₂ 16#32) ∗
        ((fsp + 32#64) ↦₈ boolByte dec.isComplete) ∗ ((fsp + 33#64) ↦ₛ (unpack64 v4).tail) ∗
        ((fsp + 40#64) ↦₆₄ w40) ∗ ((fsp + 48#64) ↦₆₄ w48) ∗ ((fsp + 56#64) ↦₆₄ w56) ∗
        ((fsp + 64#64) ↦₆₄ s0.readReg64 .x29) ∗ ((fsp + 72#64) ↦₆₄ s0.readReg64 .x30) ∗
        ((fsp + 80#64) ↦₆₄ s0.readReg64 .x27) ∗ ((fsp + 88#64) ↦₆₄ v11) ∗
        ((fsp + 96#64) ↦₆₄ s0.readReg64 .x26) ∗ ((fsp + 104#64) ↦₆₄ s0.readReg64 .x25) ∗
        ((fsp + 112#64) ↦₆₄ s0.readReg64 .x24) ∗ ((fsp + 120#64) ↦₆₄ s0.readReg64 .x23) ∗
        ((fsp + 128#64) ↦₆₄ s0.readReg64 .x22) ∗ ((fsp + 136#64) ↦₆₄ s0.readReg64 .x21) ∗
        ((fsp + 144#64) ↦₆₄ s0.readReg64 .x20) ∗ ((fsp + 152#64) ↦₆₄ s0.readReg64 .x19) ∗
        (out ↦₆₄ d0) ∗ ((out + 8#64) ↦₆₄ d1) ∗ ((out + 16#64) ↦₆₄ d2) ∗
        ((out + 24#64) ↦₆₄ d3) ∗ ((out + 32#64) ↦₆₄ d4) ∗
        vecPtListOf A decA (dec.pts.map SortedSetPt.vec) ∗
        memRegion (decA + 384#64) 16 ∗
        A.pool ∗ stackAt fsp dropGluePoly16Stack ∗
        (arrayAt (fun bs addr => vecU8 A addr bs) 24 ptr_pts
            ((dec.pts.map SortedSetPt.vec).map serializePtList) ∗
          A.live ptr_pts 384 8)) := by
    rw [DecoderPb.stackAt_dropGluePoly16_split_bottom fsp]
    dsimp only [vecPtListOf]
    exact Entails.of_eq (by ac_rfl)
  refine SepWPp.weaken_pre hpre2 (CryptoVerification.SpqrV1.Poly.DecoderPb.SepWPp.seq_clean hep ?_)
  intro sf hpcf hrunf ⟨hspf, hx19f, hx20f, hx21f, hx22f, hx23f, hx24f, hx25f, hx26f, hx27f, hx28f, hx29f, hx30f, htrf, hvregsf⟩
  have hpost_dec := protoPolynomialDecoderAt_entails A out ptr_pts dec hpts_len hptr_pts
  subst hQ_goal
  refine SepWPp.done hpcf hrunf ⟨fun hmem_f => Satisfies.mono (sepConj_mono_left ?_) hmem_f,
    hspf, ⟨hx19f, hx20f, hx21f, hx22f, hx23f, hx24f, hx25f, hx26f, hx27f, hx28f.trans hx28_2, hx29f, hvregsf⟩⟩
  exact Entails.pure_right htrf (Entails.trans (Entails.of_eq (by ac_rfl))
    (Entails.trans (sepConj_mono_left (Q := memRegion decA 400 ∗ A.pool ∗ stackAt s0.sp decoderIntoPbStack) hpost_dec)
      (Entails.of_eq (by ac_rfl))))

/-- 4K-hook (`AllocHooks` + `sessionShimSpec`) verification of `<PolyDecoder>::into_pb`. -/
theorem decoder_into_pb_ok_of_hooks4k {b : BitVec 64} {A : RustAlloc}
    {ext : String → Option (State → State)}
    (hAlloc : AllocHooks A ext)
    (hShim : HookSat ext shimName sessionShimSpec) :
    DecoderIntoPbOkExt b A ext := by
  have halloc : subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr allocName) (rustAllocSpec A) := by
    simpa only [BitVec.ofNat_eq_ofNat, BitVec.add_zero] using
      alloc_ok_at_ext b A ext hAlloc allocName 0 (Nat.add_zero _)
  have hdealloc : DeallocOkExt b A ext := by
    simpa only [DeallocOkExt, dropProgAtExt, BitVec.ofNat_eq_ofNat, BitVec.add_zero] using
      dealloc_ok_at_ext b A ext hAlloc LibsignalTripleRatchet.deallocName 0 (Nat.add_zero _)
  have hshim : subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr shimName) sessionShimSpec := by
    simpa only [BitVec.ofNat_eq_ofNat, BitVec.add_zero] using
      (hook_ok_at (hname := shimName) rfl (Nat.add_zero _) (by simp only [arm64_norm])
        (fun _ => by simp only [arm64_norm]) (by decide +kernel) hShim :
        subroutine_ok (tripleRatchetProgAtExt b ext)
          ((tripleRatchetProgAtExt b ext).fnAddr shimName + BitVec.ofNat 64 0) sessionShimSpec)
  exact decoder_into_pb_ok_of_sub halloc hdealloc hshim

private theorem stackAt_encoderIntoPb_split_allocHook (sp : BitVec 64) :
    stackAt sp EncoderIntoPb.encoderIntoPbStack =
      stackAt sp allocHookStack ∗ memRegion (sp - 4352#64) 256 := by
  change memRegion (sp - 4352#64) 4352 =
    memRegion (sp - 4096#64) 4096 ∗ memRegion (sp - 4352#64) 256
  rw [ProofLib.memRegion_split' (b := sp - 4352#64) (n := 256) (k := 4096)
        (b' := sp - 4096#64) rfl (by bv_omega) (by decide), sepConj_comm]

private theorem call_memcpy4k_keep_relocate {b memcpy_pc : BitVec 64}
    {ext : String → Option (State → State)}
    (hmemcpy_raw : subroutine_ok (tripleRatchetProgAtExt b ext)
      memcpy_pc (sessionMemcpySpec allocHookStack))
    {k m n : Nat} {off : BitVec 64}
    {F G : BitVec 64 → SepProp}
    (hoff : off = BitVec.ofNat 64 k)
    (hkm : k + m = n)
    (hF : Relocatable k F)
    (hG : Relocatable m G)
    (dst src : BitVec 64)
    {s0 s : State} {ret_pc : BitVec 64} {P Frame R : SepProp}
    {Q : State → SepProp → Prop}
    (hpc : s.pc = memcpy_pc)
    (hrun : s.status = .Running)
    (hsp : s.sp = s0.sp - 1520#64)
    (hsp_align : ((s0.sp - 1520#64) &&& 15#64 == 0#64) = true)
    (hlr : s.readReg64 .x30 = ret_pc)
    (htrace : TraceCalleeSaved s s0)
    (hx0 : s.readReg64 .x0 = dst)
    (hx1 : s.readReg64 .x1 = src)
    (hx2 : (s.readReg64 .x2).toNat = n)
    (hsplit : P = (memRegion dst n ∗ (F src ∗ G (src + off)) ∗
      stackAt (s0.sp - 1520#64) allocHookStack) ∗ Frame)
    (hnext : ∀ sf : State,
      sf.pc = ret_pc →
      sf.status = .Running →
      sf.sp = s0.sp - 1520#64 →
      CalleeSavedPreserved s sf →
      TraceCalleeSaved sf s0 →
      SepWPp (tripleRatchetProgAtExt b ext) (s0.readReg64 .x30) sf
        (((memRegion dst k ∗ G (dst + off)) ∗
          (F src ∗ memRegion (src + off) m) ∗
          stackAt (s0.sp - 1520#64) allocHookStack) ∗ Frame)
        Q (StatesIntoPbPanic s0 R)) :
    SepWPp (tripleRatchetProgAtExt b ext) (s0.readReg64 .x30) s P
      Q (StatesIntoPbPanic s0 R) := by
  have hpre_split :
      P ⊢ ∃∗ bs1 : List (BitVec 8), ∃∗ bs2 : List (BitVec 8),
        ⌜bs1.length = k ∧ bs2.length = m ∧ (bs1 ++ bs2).length = n⌝ ∗
        (memRegion dst n ∗ (src ↦ₛ (bs1 ++ bs2)) ∗ stackAt (s0.sp - 1520#64) allocHookStack) ∗
        (relocatedHeap F bs1 ∗ relocatedHeap G bs2 ∗ Frame) := by
    rw [hsplit]
    refine Entails.trans (sepConj_mono_left (sepConj_mono_right (sepConj_mono_left
      (memcpy_keep_relocate_split hoff hkm hF hG dst src)))) ?_
    simp only [sepExists_sepConj_left, sepExists_sepConj_right]
    apply Entails.sepExists_elim; intro bs1
    apply Entails.sepExists_elim; intro bs2
    have hpull_pure :
        (memRegion dst n ∗
          (⌜bs1.length = k ∧ bs2.length = m ∧ (bs1 ++ bs2).length = n⌝ ∗
            (src ↦ₛ (bs1 ++ bs2)) ∗ relocatedHeap F bs1 ∗ relocatedHeap G bs2) ∗
          stackAt (s0.sp - 1520#64) allocHookStack) ∗ Frame =
        ⌜bs1.length = k ∧ bs2.length = m ∧ (bs1 ++ bs2).length = n⌝ ∗
          ((memRegion dst n ∗ (src ↦ₛ (bs1 ++ bs2)) ∗ stackAt (s0.sp - 1520#64) allocHookStack) ∗
            (relocatedHeap F bs1 ∗ relocatedHeap G bs2 ∗ Frame)) := by ac_rfl
    rw [hpull_pure]
    apply Entails.pure_left; intro hpure
    refine Entails.sepExists_right bs1 (Entails.sepExists_right bs2 ?_)
    exact Entails.pure_right hpure (Entails.refl _)
  refine SepWPp.weaken_pre hpre_split ?_
  refine SepWPp.exists_elim fun bs1 => SepWPp.exists_elim fun bs2 => ?_
  refine SepWPp.pure_left fun ⟨hlen1, hlen2, hlen12⟩ => ?_
  refine SepWPp.call hmemcpy_raw (x := (dst, src, bs1 ++ bs2))
    (F := relocatedHeap F bs1 ∗ relocatedHeap G bs2 ∗ Frame)
    hpc hrun (by rw [State.spAligned, hsp]; exact hsp_align) hlr ?_
    (fun _ _ _ _ h => by
      dsimp only [sessionMemcpySpec, libcMemcpySpec] at h
      simp only [sepConj_assoc, satisfies_pure_sepConj] at h
      exact h.1.elim)
    (fun _ _ h => by
      dsimp only [sessionMemcpySpec, libcMemcpySpec] at h
      simp only [sepConj_assoc, satisfies_pure_sepConj] at h
      exact h.1.elim)
    (fun sf hpc_sf hrun_sf hsp_sf hcs_sf => ?_)
  · intro R' hm
    dsimp only [sessionMemcpySpec, libcMemcpySpec]
    rw [hsp, hlen12]
    simp only [sepConj_assoc, satisfies_pure_sepConj] at hm ⊢
    exact ⟨⟨hx0, hx1, hx2⟩, by simpa [sepConj_assoc] using hm⟩
  · dsimp only [sessionMemcpySpec, libcMemcpySpec]
    rw [hsp, sepConj_assoc]
    refine SepWPp.pure_left fun ⟨_, htr⟩ => ?_
    have hrec := memcpy_keep_relocate_recombine (F := F) (G := G) hoff hlen1 hlen2 dst src
    have hpost_ent :
        (((dst ↦ₛ (bs1 ++ bs2)) ∗ (src ↦ₛ (bs1 ++ bs2)) ∗
          stackAt (s0.sp - 1520#64) allocHookStack) ∗
          (relocatedHeap F bs1 ∗ relocatedHeap G bs2 ∗ Frame)) ⊢
        (((memRegion dst k ∗ G (dst + off)) ∗
          (F src ∗ memRegion (src + off) m) ∗
          stackAt (s0.sp - 1520#64) allocHookStack) ∗ Frame) := by
      have hreord :
          (((dst ↦ₛ (bs1 ++ bs2)) ∗ (src ↦ₛ (bs1 ++ bs2)) ∗
            stackAt (s0.sp - 1520#64) allocHookStack) ∗
            (relocatedHeap F bs1 ∗ relocatedHeap G bs2 ∗ Frame)) =
          ((dst ↦ₛ (bs1 ++ bs2)) ∗ (src ↦ₛ (bs1 ++ bs2)) ∗
            relocatedHeap F bs1 ∗ relocatedHeap G bs2) ∗
          (stackAt (s0.sp - 1520#64) allocHookStack ∗ Frame) := by ac_rfl
      rw [hreord]
      refine Entails.trans (sepConj_mono_left hrec) ?_
      exact Entails.of_eq (by ac_rfl)
    refine SepWPp.weaken_pre hpost_ent ?_
    exact hnext sf hpc_sf hrun_sf (hsp_sf.trans hsp) hcs_sf
      ⟨htr.trans htrace.1, hcs_sf.2.2.2.2.2.2.2.2.2.2.2.trans htrace.2⟩

set_option maxHeartbeats 800000 in
private theorem states_into_pb_noHeaderReceived_of_sub {A : RustAlloc} {F : ShaCompress}
    {b : BitVec 64} {ext : String → Option (State → State)}
    (hdec : DecoderIntoPbOkExt b A ext)
    (hmemcpy4k : subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr memcpyName) (sessionMemcpySpec allocHookStack))
    (s : Chunked.SendCt.NoHeaderReceived spqrPolyApi (spqrAuthApi F)) :
    subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr statesIntoPbName)
      (statesIntoPbVariantSpec A F b (.noHeaderReceived s)) := by
  have hdec_raw := sub_ok_decoderIntoPb_raw hdec
  have hmemcpy_raw : subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr statesIntoPbName +
        bv% (ls_rel% "<spqr::v1::chunked::states::States>::into_pb" "memcpy"))
      (sessionMemcpySpec allocHookStack) :=
    sub_ok_of_addr_eq
      (fnAddr_rel64_ext (b := b) (H := Rust.withPanics ext)
        statesIntoPb_fnOff (ls_stub% "memcpy") (by decide)).symm
      hmemcpy4k
  apply subroutine_ok_of_sepWPp
  intro ⟨out, stA⟩ R s0 hpc hrun hpre hsp0_align
  simp only [statesIntoPbVariantSpec, sepConj_assoc, satisfies_pure_sepConj] at hpre
  rcases hpre with ⟨⟨hx8, hx0, hb⟩, hmem⟩
  refine ⟨memRegion out optProtoInnerStateSize ∗
      chunkedStatesAt A stA (.noHeaderReceived s) ∗
      statesIntoPbJumpTableAt b ∗ A.pool ∗ stackAt s0.sp statesIntoPbStack,
    R, ?_, ?_⟩
  · simpa [sepConj_assoc] using hmem
  refine sepWPp_of_states_into_pb_wpp s0 s0 out stA (.noHeaderReceived s) _ R ?_
  refine SepWPp.weaken_pre (sepConj_mono_right (sepConj_mono_left
    (chunkedNoHeaderReceived_expose A stA s))) ?_
  have hpull :
      memRegion out optProtoInnerStateSize ∗
        (∃∗ a0 : BitVec 64, ∃∗ a1 : BitVec 64, ∃∗ a2 : BitVec 64,
         ∃∗ a3 : BitVec 64, ∃∗ a4 : BitVec 64, ∃∗ a5 : BitVec 64,
          (stA ↦₆₄ 7#64) ∗
          (((stA + 8#64) ↦₆₄ a0) ∗ ((stA + 16#64) ↦₆₄ a1) ∗
           ((stA + 24#64) ↦₆₄ a2) ∗ ((stA + 32#64) ↦₆₄ a3) ∗
           ((stA + 40#64) ↦₆₄ a4) ∗ ((stA + 48#64) ↦₆₄ a5)) ∗
          (((stA + 56#64) ↦₆₄ s.uc.epoch) ∗
           polyDecoderAt A (stA + 64#64) s.receiving_hdr) ∗
          authenticatorHeap A a0 a1 a2 a3 a4 a5 s.uc.auth ∗
          memRegion (stA + 464#64) 464) ∗
        statesIntoPbJumpTableAt b ∗ A.pool ∗ stackAt s0.sp statesIntoPbStack ⊢
      ∃∗ a0 : BitVec 64, ∃∗ a1 : BitVec 64, ∃∗ a2 : BitVec 64,
      ∃∗ a3 : BitVec 64, ∃∗ a4 : BitVec 64, ∃∗ a5 : BitVec 64,
        stackAt s0.sp statesIntoPbStack ∗
        (stA ↦₆₄ 7#64) ∗
        ((((stA + 8#64) ↦₆₄ a0) ∗ ((stA + 16#64) ↦₆₄ a1) ∗
          ((stA + 24#64) ↦₆₄ a2) ∗ ((stA + 32#64) ↦₆₄ a3) ∗
          ((stA + 40#64) ↦₆₄ a4) ∗ ((stA + 48#64) ↦₆₄ a5)) ∗
         (((stA + 56#64) ↦₆₄ s.uc.epoch) ∗
          polyDecoderAt A (stA + 64#64) s.receiving_hdr) ∗
         authenticatorHeap A a0 a1 a2 a3 a4 a5 s.uc.auth ∗
         memRegion (stA + 464#64) 464 ∗
         memRegion out optProtoInnerStateSize ∗
         statesIntoPbJumpTableAt b ∗ A.pool) := by
    simp only [sepExists_sepConj_left, sepExists_sepConj_right]
    apply Entails.sepExists_elim; intro a0
    apply Entails.sepExists_elim; intro a1
    apply Entails.sepExists_elim; intro a2
    apply Entails.sepExists_elim; intro a3
    apply Entails.sepExists_elim; intro a4
    apply Entails.sepExists_elim; intro a5
    refine Entails.sepExists_right a0 (Entails.sepExists_right a1
      (Entails.sepExists_right a2 (Entails.sepExists_right a3
        (Entails.sepExists_right a4 (Entails.sepExists_right a5 ?_)))))
    exact Entails.of_eq (by ac_rfl)
  refine SepWPp.weaken_pre hpull ?_
  refine SepWPp.exists_elim fun a0 => SepWPp.exists_elim fun a1 =>
    SepWPp.exists_elim fun a2 => SepWPp.exists_elim fun a3 =>
    SepWPp.exists_elim fun a4 => SepWPp.exists_elim fun a5 => ?_
  have hpro := states_into_pb_prologue_60 s0 out stA 7#64
    ((((stA + 8#64) ↦₆₄ a0) ∗ ((stA + 16#64) ↦₆₄ a1) ∗
      ((stA + 24#64) ↦₆₄ a2) ∗ ((stA + 32#64) ↦₆₄ a3) ∗
      ((stA + 40#64) ↦₆₄ a4) ∗ ((stA + 48#64) ↦₆₄ a5)) ∗
     (((stA + 56#64) ↦₆₄ s.uc.epoch) ∗
      polyDecoderAt A (stA + 64#64) s.receiving_hdr) ∗
     authenticatorHeap A a0 a1 a2 a3 a4 a5 s.uc.auth ∗
     memRegion (stA + 464#64) 464 ∗
     memRegion out optProtoInnerStateSize ∗
     statesIntoPbJumpTableAt b ∗ A.pool)
    hsp0_align hpc hrun hx8 hx0
  refine statesIntoPb_seq_sepWP hpro fun s1 hpc1 hrun1
    ⟨hsp1, hx29_1, hx28_1, hx27_1, hx26_1, hx20_1, hx19_1, hx8_1, htr1⟩ => ?_
  rw [stack_1416_split_noHeaderReceived s0.sp]
  have hpre1 := states_into_pb_noHeaderReceived_pre1 s0 s1 out stA
    hb hsp0_align hpc1 hrun1 hsp1 hx29_1 hx28_1 hx27_1 hx26_1 hx20_1 hx19_1 hx8_1 htr1
    (stackAt (s0.sp - 1520#64) EncoderIntoPb.encoderIntoPbStack ∗
     ((s0.sp - 1520#64) ↦₆₄ 0#64) ∗
     cells (s0.sp - 1512#64) 19 ∗
     memRegion (s0.sp - 1360#64) 456 ∗
     memRegion (s0.sp - 904#64) 424 ∗
     memRegion (s0.sp - 480#64) protoPolynomialDecoderSize ∗
     cells (s0.sp - 440#64) 6 ∗
     memRegion (s0.sp - 392#64) 88 ∗
     cells (s0.sp - 304#64) 6 ∗
     cells (s0.sp - 256#64) 6 ∗
     memRegion (s0.sp - 208#64) 112 ∗
     statesIntoPbSavedCells s0 ∗
     (stA ↦₆₄ 7#64) ∗
     (((stA + 8#64) ↦₆₄ a0) ∗ ((stA + 16#64) ↦₆₄ a1) ∗
      ((stA + 24#64) ↦₆₄ a2) ∗ ((stA + 32#64) ↦₆₄ a3) ∗
      ((stA + 40#64) ↦₆₄ a4) ∗ ((stA + 48#64) ↦₆₄ a5)) ∗
     (((stA + 56#64) ↦₆₄ s.uc.epoch) ∗
      polyDecoderAt A (stA + 64#64) s.receiving_hdr) ∗
     authenticatorHeap A a0 a1 a2 a3 a4 a5 s.uc.auth ∗
     memRegion (stA + 464#64) 464 ∗
     memRegion out optProtoInnerStateSize ∗
     A.pool)
  refine SepWPp.weaken_pre (Entails.of_eq (by ac_rfl))
    (statesIntoPb_seq_sepWP hpre1 fun s2 hpc2 hrun2
      ⟨hsp2, hlr2, hx0_2, hx1_2, hx2_2, hx29_2, hx28_2, hx26_2, hx21_2, hx20_2, hx19_2, htr2⟩ => ?_)
  have hfsp_align : ((s0.sp - 1520#64) &&& 15#64 == 0#64) = true :=
    ProofLib.spAligned_sub s0.sp 1520#64 hsp0_align (by decide)
  let F_words : BitVec 64 → SepProp := fun a =>
    (a ↦₆₄ a0) ∗ ((a + 8#64) ↦₆₄ a1) ∗ ((a + 16#64) ↦₆₄ a2) ∗
    ((a + 24#64) ↦₆₄ a3) ∗ ((a + 32#64) ↦₆₄ a4) ∗ ((a + 40#64) ↦₆₄ a5)
  let G_dec : BitVec 64 → SepProp := fun a =>
    (a ↦₆₄ s.uc.epoch) ∗ polyDecoderAt A (a + 8#64) s.receiving_hdr
  have hF_src : F_words (stA + 8#64) =
      (((stA + 8#64) ↦₆₄ a0) ∗ ((stA + 16#64) ↦₆₄ a1) ∗
       ((stA + 24#64) ↦₆₄ a2) ∗ ((stA + 32#64) ↦₆₄ a3) ∗
       ((stA + 40#64) ↦₆₄ a4) ∗ ((stA + 48#64) ↦₆₄ a5)) := by
    dsimp only [F_words]
    simp only [BitVec.add_assoc, BitVec.reduceAdd]
  have hG_src : G_dec ((stA + 8#64) + 48#64) =
      (((stA + 56#64) ↦₆₄ s.uc.epoch) ∗
       polyDecoderAt A (stA + 64#64) s.receiving_hdr) := by
    dsimp only [G_dec]
    simp only [BitVec.add_assoc, BitVec.reduceAdd]
  have hG_dst : G_dec ((s0.sp - 1360#64) + 48#64) =
      (((s0.sp - 1312#64) ↦₆₄ s.uc.epoch) ∗
       polyDecoderAt A (s0.sp - 1304#64) s.receiving_hdr) := by
    dsimp only [G_dec]
    simp only [arm64_norm]
  have hsrc_off : (stA + 8#64) + 48#64 = stA + 56#64 := by
    simp only [BitVec.add_assoc, BitVec.reduceAdd]
  refine call_memcpy4k_keep_relocate hmemcpy_raw
    (k := 48) (m := 408) (n := 456) (off := 48#64)
    (F := F_words) (G := G_dec)
    rfl rfl
    (Relocatable.words6 a0 a1 a2 a3 a4 a5)
    (Relocatable.epoch_polyDecoderAt A s.uc.epoch s.receiving_hdr)
    (s0.sp - 1360#64) (stA + 8#64)
    (Frame :=
      memRegion ((s0.sp - 1520#64) - 4352#64) 256 ∗
      ((s0.sp - 1520#64) ↦₆₄ 0#64) ∗
      cells (s0.sp - 1512#64) 19 ∗
      memRegion (s0.sp - 904#64) 424 ∗
      memRegion (s0.sp - 480#64) protoPolynomialDecoderSize ∗
      cells (s0.sp - 440#64) 6 ∗
      memRegion (s0.sp - 392#64) 88 ∗
      cells (s0.sp - 304#64) 6 ∗
      cells (s0.sp - 256#64) 6 ∗
      memRegion (s0.sp - 208#64) 112 ∗
      statesIntoPbSavedCells s0 ∗
      (stA ↦₆₄ 7#64) ∗
      authenticatorHeap A a0 a1 a2 a3 a4 a5 s.uc.auth ∗
      memRegion (stA + 464#64) 464 ∗
      memRegion out optProtoInnerStateSize ∗
      statesIntoPbJumpTableAt b ∗ A.pool)
    hpc2 hrun2 hsp2 hfsp_align hlr2 htr2 hx0_2 hx1_2 hx2_2
    (by rw [hF_src, hG_src, stackAt_encoderIntoPb_split_allocHook (s0.sp - 1520#64)]; ac_rfl)
    fun s3 hpc3 hrun3 hsp3 hcs3 htr3 => ?_
  rw [hF_src, hG_dst, hsrc_off]
  have hx19_3 : s3.readReg64 .x19 = out := hcs3.1.trans hx19_2
  have hx20_3 : s3.readReg64 .x20 = stA := hcs3.2.1.trans hx20_2
  have hx21_3 : s3.readReg64 .x21 = s0.sp - 1360#64 := hcs3.2.2.1.trans hx21_2
  have hx26_3 : s3.readReg64 .x26 = s0.sp - 480#64 := hcs3.2.2.2.2.2.2.2.1.trans hx26_2
  have hx28_3 : s3.readReg64 .x28 = s0.sp - 256#64 := hcs3.2.2.2.2.2.2.2.2.2.1.trans hx28_2
  have hx29_3 : s3.readReg64 .x29 = s0.sp - 96#64 := hcs3.2.2.2.2.2.2.2.2.2.2.1.trans hx29_2
  have hpre2 := states_into_pb_noHeaderReceived_pre2 s0 s3 out stA
    a0 a1 a2 a3 a4 a5 s.uc.epoch
    hsp0_align hpc3 hrun3 hsp3 hx29_3 hx28_3 hx26_3 hx21_3 hx20_3 hx19_3 htr3
    (memRegion (s0.sp - 1360#64) 48 ∗
     polyDecoderAt A (s0.sp - 1304#64) s.receiving_hdr ∗
     memRegion (stA + 56#64) 408 ∗
     stackAt (s0.sp - 1520#64) EncoderIntoPb.encoderIntoPbStack ∗
     ((s0.sp - 1520#64) ↦₆₄ 0#64) ∗
     cells (s0.sp - 1512#64) 19 ∗
     memRegion (s0.sp - 904#64) 424 ∗
     memRegion (s0.sp - 480#64) protoPolynomialDecoderSize ∗
     cells (s0.sp - 440#64) 6 ∗
     memRegion (s0.sp - 392#64) 88 ∗
     cells (s0.sp - 304#64) 6 ∗
     memRegion (s0.sp - 208#64) 112 ∗
     statesIntoPbSavedCells s0 ∗
     (stA ↦₆₄ 7#64) ∗
     authenticatorHeap A a0 a1 a2 a3 a4 a5 s.uc.auth ∗
     memRegion (stA + 464#64) 464 ∗
     memRegion out optProtoInnerStateSize ∗
     statesIntoPbJumpTableAt b ∗ A.pool)
  refine SepWPp.weaken_pre
    (by rw [stackAt_encoderIntoPb_split_allocHook (s0.sp - 1520#64)]; exact Entails.of_eq (by ac_rfl))
    (statesIntoPb_seq_sepWP hpre2 fun s4 hpc4 hrun4
      ⟨hsp4, hlr4, hx0_4, hx1_4, hx29_4, hx26_4, hx20_4, hx19_4, htr4⟩ => ?_)
  refine call_decoderIntoPb_expose hdec_raw (s0.sp - 480#64) (s0.sp - 1304#64) s.receiving_hdr
    (Frame :=
      cells (s0.sp - 1512#64) 19 ∗
      cells (s0.sp - 440#64) 6 ∗
      cells (s0.sp - 304#64) 6 ∗
      (((s0.sp - 256#64) ↦₆₄ a0) ∗ ((s0.sp - 248#64) ↦₆₄ a1) ∗
       ((s0.sp - 240#64) ↦₆₄ a2) ∗ ((s0.sp - 232#64) ↦₆₄ a3) ∗
       ((s0.sp - 224#64) ↦₆₄ a4) ∗ ((s0.sp - 216#64) ↦₆₄ a5)) ∗
      memRegion (s0.sp - 208#64) 112 ∗
      ((s0.sp - 1520#64) ↦₆₄ 0#64) ∗
      memRegion (s0.sp - 1360#64) 48 ∗
      ((s0.sp - 1312#64) ↦₆₄ s.uc.epoch) ∗
      memRegion (s0.sp - 904#64) 424 ∗
      memRegion (s0.sp - 392#64) 88 ∗
      statesIntoPbSavedCells s0 ∗
      (stA ↦₆₄ 7#64) ∗
      (((stA + 8#64) ↦₆₄ a0) ∗ ((stA + 16#64) ↦₆₄ a1) ∗
       ((stA + 24#64) ↦₆₄ a2) ∗ ((stA + 32#64) ↦₆₄ a3) ∗
       ((stA + 40#64) ↦₆₄ a4) ∗ ((stA + 48#64) ↦₆₄ a5)) ∗
      memRegion (stA + 56#64) 408 ∗
      authenticatorHeap A a0 a1 a2 a3 a4 a5 s.uc.auth ∗
      memRegion (stA + 464#64) 464 ∗
      memRegion out optProtoInnerStateSize ∗
      statesIntoPbJumpTableAt b)
    hpc4 hrun4 hsp4 hfsp_align hlr4 htr4 hx0_4 hx1_4
    (by ac_rfl)
    fun sf d0 d1 d2 d3 d4 hpcf hrunf hspf hcsf htrf => ?_
  have hx19_f : sf.readReg64 .x19 = out := hcsf.1.trans hx19_4
  have hx20_f : sf.readReg64 .x20 = s.uc.epoch := hcsf.2.1.trans hx20_4
  have hx26_f : sf.readReg64 .x26 = s0.sp - 480#64 := hcsf.2.2.2.2.2.2.2.1.trans hx26_4
  have hx29_f : sf.readReg64 .x29 = s0.sp - 96#64 := hcsf.2.2.2.2.2.2.2.2.2.2.1.trans hx29_4
  apply SepWPp.of_sepWP_ret
  have hpost_step := states_into_pb_noHeaderReceived_post A F s0 sf out stA s
    a0 a1 a2 a3 a4 a5 d0 d1 d2 d3 d4
    hsp0_align hpcf hrunf hspf hx29_f hx26_f hx20_f hx19_f htrf
  refine SepWP.weaken_pre (Entails.of_eq ?_) hpost_step
  simp only [arm64_norm]
  ac_rfl

theorem states_into_pb_initV1State_of_sub {A : RustAlloc} {F : ShaCompress}
    {b : BitVec 64} {ext : String → Option (State → State)}
    (halloc : subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr allocName) (rustAllocSpec A))
    (hdealloc : DeallocOkExt b A ext)
    (hshim : subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr shimName) sessionShimSpec)
    (hmemcpy4k : subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr memcpyName) (sessionMemcpySpec allocHookStack))
    (d : Direction) (authKey : Bytes) :
    subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr statesIntoPbName)
      (statesIntoPbVariantSpec A F b (initV1State F d authKey)) := by
  cases d with
  | a2b => exact states_into_pb_keysUnsampled _
  | b2a =>
    exact states_into_pb_noHeaderReceived_of_sub
      (decoder_into_pb_ok_of_sub halloc hdealloc hshim) hmemcpy4k _

/-- 4K-hook `<States>::into_pb` on `initV1State F d authKey` (`.keysUnsampled` / `.noHeaderReceived`). -/
theorem states_into_pb_initV1State_of_hooks4k {A : RustAlloc} {F : ShaCompress}
    {b : BitVec 64} {ext : String → Option (State → State)}
    (hAlloc : AllocHooks A ext)
    (hShim : HookSat ext shimName sessionShimSpec)
    (hMemcpy : HookSat ext memcpyName (sessionMemcpySpec allocHookStack))
    (d : Direction) (authKey : Bytes) :
    subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr statesIntoPbName)
      (statesIntoPbVariantSpec A F b (initV1State F d authKey)) := by
  cases d with
  | a2b => exact states_into_pb_keysUnsampled _
  | b2a =>
    have hmemcpy4k : subroutine_ok (tripleRatchetProgAtExt b ext)
        ((tripleRatchetProgAtExt b ext).fnAddr memcpyName) (sessionMemcpySpec allocHookStack) := by
      simpa only [BitVec.ofNat_eq_ofNat, BitVec.add_zero] using
        (hook_ok_at (hname := memcpyName) rfl (Nat.add_zero _) (by simp only [arm64_norm])
          (fun _ => by simp only [arm64_norm]) (by decide +kernel) hMemcpy :
          subroutine_ok (tripleRatchetProgAtExt b ext)
            ((tripleRatchetProgAtExt b ext).fnAddr memcpyName + BitVec.ofNat 64 0)
            (sessionMemcpySpec allocHookStack))
    exact states_into_pb_noHeaderReceived_of_sub
      (decoder_into_pb_ok_of_hooks4k hAlloc hShim) hmemcpy4k _

/-! ## 3. Shared Layout & `SepWPp` Helpers for `spqr::init_inner` (`initInnerStackExt`) -/

theorem memRegion_24_and_cells_5_eq_cells_8_ext (sp : BitVec 64) :
    memRegion (sp - 1032#64) 24 ∗ cells (sp - 1008#64) 5 = cells (sp - 1032#64) 8 := by
  rw [← ProofLib.memRegion_cells (sp - 1008#64) 5 (by decide),
      ← ProofLib.memRegion_cells (sp - 1032#64) 8 (by decide)]
  exact (ProofLib.memRegion_split' (b := sp - 1032#64) (n := 24) (k := 40)
    (b' := sp - 1008#64) rfl (by bv_omega) (by decide)).symm

theorem memRegion_24_and_cells_17_eq_cells_20_ext (sp : BitVec 64) :
    memRegion (sp - 1032#64) 24 ∗ cells (sp - 1008#64) 17 = cells (sp - 1032#64) 20 := by
  rw [← ProofLib.memRegion_cells (sp - 1008#64) 17 (by decide),
      ← ProofLib.memRegion_cells (sp - 1032#64) 20 (by decide)]
  exact (ProofLib.memRegion_split' (b := sp - 1032#64) (n := 24) (k := 136)
    (b' := sp - 1008#64) rfl (by bv_omega) (by decide)).symm

theorem memRegion_992_split_a2b_ext (sp : BitVec 64) :
    memRegion (sp - 1040#64) 992 =
      cells (sp - 1032#64) 3 ∗ memRegion (sp - 104#64) authenticatorSize ∗
      cells (sp - 1008#64) 5 ∗ memRegion (sp - 968#64) 864 ∗
      memRegion (sp - 1040#64) 8 ∗ memRegion (sp - 56#64) 8 := by
  change memRegion (sp - 1040#64) 992 =
    cells (sp - 1032#64) 3 ∗ memRegion (sp - 104#64) 48 ∗
    cells (sp - 1008#64) 5 ∗ memRegion (sp - 968#64) 864 ∗
    memRegion (sp - 1040#64) 8 ∗ memRegion (sp - 56#64) 8
  rw [ProofLib.memRegion_split' (b := sp - 1040#64) (n := 8) (k := 984) (b' := sp - 1032#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := sp - 1032#64) (n := 24) (k := 960) (b' := sp - 1008#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := sp - 1008#64) (n := 40) (k := 920) (b' := sp - 968#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := sp - 968#64) (n := 864) (k := 56) (b' := sp - 104#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := sp - 104#64) (n := 48) (k := 8) (b' := sp - 56#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_cells (sp - 1032#64) 3 (by decide),
      ProofLib.memRegion_cells (sp - 1008#64) 5 (by decide)]
  ac_rfl

theorem memRegion_48_and_8_eq_56_ext (sp : BitVec 64) :
    memRegion (sp - 104#64) 48 ∗ memRegion (sp - 56#64) 8 = memRegion (sp - 104#64) 56 :=
  (ProofLib.memRegion_split' (b := sp - 104#64) (n := 48) (k := 8)
    (b' := sp - 56#64) rfl (by bv_omega) (by decide)).symm

theorem memRegion_992_split_b2a_ext (sp : BitVec 64) :
    memRegion (sp - 1040#64) 992 =
      cells (sp - 1032#64) 3 ∗ memRegion (sp - 104#64) authenticatorSize ∗
      cells (sp - 56#64) 1 ∗ cells (sp - 1008#64) 17 ∗ cells (sp - 872#64) 20 ∗
      cells (sp - 712#64) 17 ∗ (∃∗ b0 : BitVec 8, (sp - 576#64) ↦₈ b0) ∗
      memRegion (sp - 575#64) 7 ∗ memRegion (sp - 568#64) 464 ∗
      memRegion (sp - 1040#64) 8 := by
  change memRegion (sp - 1040#64) 992 =
    cells (sp - 1032#64) 3 ∗ memRegion (sp - 104#64) 48 ∗ cells (sp - 56#64) 1 ∗
    cells (sp - 1008#64) 17 ∗ cells (sp - 872#64) 20 ∗ cells (sp - 712#64) 17 ∗
    (∃∗ b0 : BitVec 8, (sp - 576#64) ↦₈ b0) ∗ memRegion (sp - 575#64) 7 ∗
    memRegion (sp - 568#64) 464 ∗ memRegion (sp - 1040#64) 8
  rw [ProofLib.memRegion_split' (b := sp - 1040#64) (n := 8) (k := 984) (b' := sp - 1032#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := sp - 1032#64) (n := 24) (k := 960) (b' := sp - 1008#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := sp - 1008#64) (n := 136) (k := 824) (b' := sp - 872#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := sp - 872#64) (n := 160) (k := 664) (b' := sp - 712#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := sp - 712#64) (n := 136) (k := 528) (b' := sp - 576#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := sp - 576#64) (n := 1) (k := 527) (b' := sp - 575#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := sp - 575#64) (n := 7) (k := 520) (b' := sp - 568#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := sp - 568#64) (n := 464) (k := 56) (b' := sp - 104#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := sp - 104#64) (n := 48) (k := 8) (b' := sp - 56#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_one (sp - 576#64), ProofLib.memRegion_cells (sp - 1032#64) 3 (by decide),
      ProofLib.memRegion_cells (sp - 1008#64) 17 (by decide), ProofLib.memRegion_cells (sp - 872#64) 20 (by decide),
      ProofLib.memRegion_cells (sp - 712#64) 17 (by decide), ProofLib.memRegion_cells (sp - 56#64) 1 (by decide)]
  ac_rfl

theorem memRegion_992_rejoin_b2a_ext (sp : BitVec 64) :
    memRegion (sp - 1032#64) chunkedStatesSize ∗ memRegion (sp - 104#64) 56 ∗
    memRegion (sp - 1040#64) 8 = memRegion (sp - 1040#64) 992 := by
  change memRegion (sp - 1032#64) 928 ∗ memRegion (sp - 104#64) 56 ∗
    memRegion (sp - 1040#64) 8 = memRegion (sp - 1040#64) 992
  rw [ProofLib.memRegion_split' (b := sp - 1040#64) (n := 8) (k := 984) (b' := sp - 1032#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := sp - 1032#64) (n := 928) (k := 56) (b' := sp - 104#64) rfl (by bv_omega) (by decide)]
  ac_rfl

def InitInnerPostExt (A : RustAlloc) (F : ShaCompress) (b : BitVec 64)
    (s0 : State) (x : InitInnerGhost) : State → SepProp → Prop :=
  fun sf Pf =>
    (Pf ⊢
      initInnerResultAt A (F := F) x.out x.v x.d x.authKey ∗
      (x.akPtr ↦ₛ x.authKey) ∗ statesIntoPbJumpTableAt b ∗
      A.pool ∗ stackAt s0.sp initInnerStackExt) ∧
    sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf ∧ sf.trace = s0.trace

def InitInnerPanicExt (s0 : State) (R : SepProp) : State → SepProp → Prop :=
  fun sf P_f =>
    (sf.mem ⊨ P_f ∗ R) →
      (sf.mem ⊨ ⌜allocFailedIn s0 sf ∧ s0.trace <+: sf.trace⌝ ∗ anyHeap ∗ R)

theorem sepWPp_of_init_inner_wpp_ext {A : RustAlloc} {F : ShaCompress}
    {b : BitVec 64} {ext : String → Option (State → State)}
    (s0 s : State) (x : InitInnerGhost) (P R : SepProp)
    (hwpp : SepWPp (tripleRatchetProgAtExt b ext) (s0.readReg64 .x30) s P
      (InitInnerPostExt A F b s0 x) (InitInnerPanicExt s0 R)) :
    SepWPp (tripleRatchetProgAtExt b ext) (s0.readReg64 .x30) s P
      (fun sf P_f =>
        ((sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ (initInnerSpecExt A F b).post x s0 sf ∗ R)) ∧
        sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf)
      (fun sf P_f =>
        (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ (initInnerSpecExt A F b).onPanic x s0 sf ∗ R)) := by
  intro R' hm hL
  obtain ⟨sf, hsteps, ⟨hpcf, hrunf, P_f, hmf, ⟨hent, hspf, hcsf, htrf⟩⟩ | ⟨hpan, P_f, hmf, hqp⟩ | hoom⟩ :=
    hwpp R' hm hL
  · refine ⟨sf, hsteps, Or.inl ⟨hpcf, hrunf, P_f, hmf, ⟨?_, hspf, hcsf⟩⟩⟩
    intro hmR; dsimp only [initInnerSpecExt]; rw [sepConj_assoc, satisfies_pure_sepConj]
    exact ⟨htrf, by simpa [sepConj_assoc] using Satisfies.mono (sepConj_mono_left hent) hmR⟩
  · refine ⟨sf, hsteps, Or.inr (Or.inl ⟨hpan, P_f, hmf, ?_⟩)⟩
    intro hmR; dsimp only [initInnerSpecExt, initInnerOnPanic]
    simpa [sepConj_assoc] using hqp hmR
  · exact ⟨sf, hsteps, Or.inr (Or.inr hoom)⟩

theorem sepWPp_of_sepWP_keepInv_ext {prog : Program} {mid ret : BitVec 64}
    {s : State} {P : SepProp} {Q Qp : State → SepProp → Prop}
    (h : SepWP prog mid s P (fun sm Pm =>
      (∀ img, ImgCallInv img s → ImgCallInv img sm) → SepWPp prog ret sm Pm Q Qp)) :
    SepWPp prog ret s P Q Qp := by
  intro R hm hL
  obtain ⟨sm, hsteps, ⟨-, -, Pm, hmm, hnext⟩ | hoom⟩ := h.elim hm hL
  · obtain ⟨sf, hsteps', hout⟩ := hnext (fun _ hinv => hinv.of_steps hsteps) R hmm (hsteps.codeLoaded hL)
    exact ⟨sf, hsteps.trans hsteps', hout⟩
  · exact ⟨sm, hsteps, Or.inr (Or.inr hoom)⟩

theorem initInner_seq_sepWP_ext {prog : Program} {ret mid : BitVec 64} {s : State}
    {P P' : SepProp} {Post : State → Prop} {Q Qp : State → SepProp → Prop}
    (hstep : SepWP prog mid s P (fun s' P1 => (P1 ⊢ P') ∧ Post s'))
    (hnext : ∀ s' : State, s'.pc = mid → s'.status = .Running →
      (∀ img, ImgCallInv img s → ImgCallInv img s') → Post s' →
      SepWPp prog ret s' P' Q Qp) :
    SepWPp prog ret s P Q Qp := by
  refine sepWPp_of_sepWP_keepInv_ext (mid := mid) ?_
  refine SepWP.mono hstep fun s' P1 hpc' hrun' ⟨hent, hpost⟩ hinv' =>
    SepWPp.weaken_pre hent (hnext s' hpc' hrun' hinv' hpost)

theorem authenticatorAt_expose_frame_ext (A : RustAlloc) (F : ShaCompress) (sp : BitVec 64)
    (authKey : Bytes) (Frame : SepProp) :
    (authenticatorAt A (sp - 104#64) (Authenticator.new F authKey 1#64) ∗
      memRegion (sp - 1032#64) 24 ∗ A.pool ∗ stackAt (sp - 1040#64) authNewStackExt) ∗ Frame ⊢
    ∃∗ a0 : BitVec 64, ∃∗ a1 : BitVec 64, ∃∗ a2 : BitVec 64,
    ∃∗ a3 : BitVec 64, ∃∗ a4 : BitVec 64, ∃∗ a5 : BitVec 64,
      (((((sp - 104#64) ↦₆₄ a0) ∗ ((sp - 96#64) ↦₆₄ a1) ∗ ((sp - 88#64) ↦₆₄ a2) ∗
         ((sp - 80#64) ↦₆₄ a3) ∗ ((sp - 72#64) ↦₆₄ a4) ∗ ((sp - 64#64) ↦₆₄ a5)) ∗
        authenticatorHeap A a0 a1 a2 a3 a4 a5 (Authenticator.new F authKey 1#64) ∗
        memRegion (sp - 1032#64) 24 ∗ A.pool ∗ stackAt (sp - 1040#64) authNewStackExt) ∗ Frame) := by
  have ha := authenticatorAt_expose A (sp - 104#64) (Authenticator.new F authKey 1#64)
  simp only [arm64_norm] at ha
  refine Entails.trans (sepConj_mono_left (sepConj_mono_left ha)) ?_
  simp only [sepExists_sepConj_left]
  apply Entails.sepExists_elim; intro a0; apply Entails.sepExists_elim; intro a1
  apply Entails.sepExists_elim; intro a2; apply Entails.sepExists_elim; intro a3
  apply Entails.sepExists_elim; intro a4; apply Entails.sepExists_elim; intro a5
  refine Entails.sepExists_right a0 (Entails.sepExists_right a1 (Entails.sepExists_right a2
    (Entails.sepExists_right a3 (Entails.sepExists_right a4 (Entails.sepExists_right a5 ?_)))))
  exact Entails.of_eq (by ac_rfl)

end CryptoVerification.SpqrV1.Top.InitInner
