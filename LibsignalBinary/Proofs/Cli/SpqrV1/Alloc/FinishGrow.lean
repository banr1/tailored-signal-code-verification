/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SpqrV1.Alloc.FinishGrow
import GeneratedLean.LibsignalSessionCode -- shake: keep
import LibsignalBinary.Proofs.Cli.SpqrV1.Alloc.Fetch
import LibsignalBinary.Proofs.CodeLayout
import ProofLib.SepLogic.WP.Apply
import ProofLib.SepLogic.WPp

/-!
# CLI SPQR V1 `RawVecInner::finish_grow [local#8]`

Proves `finish_grow_2_ok_ext` (`finishGrow1Spec A`) for
`<alloc::raw_vec::RawVecInner>::finish_grow [local#8]` on `tripleRatchetProgAtExt`.
-/

@[expose] public section

namespace CryptoVerification.SpqrV1.Alloc

open Arm64 ProofLib CryptoVerification.RustHeap
  CryptoGames.LibsignalSession CryptoVerification.LibsignalTripleRatchetRepr
  CryptoVerification.LibsignalSession CryptoVerification.LibsignalTripleRatchet
  CryptoVerification.CodeLayout

set_option maxRecDepth 200000

set_option maxHeartbeats 400000

attribute [local irreducible] Program.fetch Program.externAt? Program.fnOff

attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero

/-- Symbol name of `<alloc::raw_vec::RawVecInner>::finish_grow [local#8]`. -/
abbrev _root_.CryptoVerification.Cli.SpqrV1.Alloc.finishGrow2Name : String :=
  "<alloc::raw_vec::RawVecInner>::finish_grow [local#8]"

private theorem getLsbD_63_eq_false {new : BitVec 64} (h : new.toNat < 2 ^ 63) :
    new.getLsbD 63 = false := by
  rw [BitVec.getLsbD_eq_getElem (by decide), BitVec.getElem_eq_testBit_toNat]
  exact Nat.testBit_lt_two_pow h

private theorem getElem_63_eq_false {new : BitVec 64} (h : new.toNat < 2 ^ 63) :
    new[63] = false := by
  rw [BitVec.getElem_eq_testBit_toNat]
  exact Nat.testBit_lt_two_pow h

private theorem beq_zero_eq_false {new : BitVec 64} (h0 : 0 < new.toNat) :
    (new == 0#64) = false := by
  rw [beq_eq_false_iff_ne]
  intro heq
  have ht := congrArg BitVec.toNat heq
  change new.toNat = 0 at ht
  omega

private theorem stackAt_finishGrow32 (sp : BitVec 64) :
    stackAt sp finishGrow32Stack =
      stackAt (sp - 32#64) allocHookStack ∗ cells (sp - 32#64) 4 :=
  ProofLib.stackAt_split_cells sp 4096 4 (by decide)

/-! ## 1. `<alloc::raw_vec::RawVecInner>::finish_grow [local#8]` -/

private def finishGrow1AllocSpec (A : RustAlloc) : Spec FinishGrow1Call :=
  { finishGrow1Spec A with
    pre := fun x s =>
      ⌜s.readReg64 .x0 = x.out ∧ s.readReg64 .x1 = x.cap ∧ s.readReg64 .x2 = x.ptr ∧
        s.readReg64 .x3 = x.new ∧ x.cap = 0#64 ∧ x.bs = [] ∧
        x.cap.toNat ≤ x.new.toNat ∧ 0 < x.new.toNat ∧ x.new.toNat + 1 ≤ 2 ^ 63⌝ ∗
      memRegion x.out 24 ∗ A.pool ∗ stackAt s.sp finishGrow32Stack }

private def finishGrow1ReallocSpec (A : RustAlloc) : Spec FinishGrow1Call :=
  { finishGrow1Spec A with
    pre := fun x s =>
      ⌜s.readReg64 .x0 = x.out ∧ s.readReg64 .x1 = x.cap ∧ s.readReg64 .x2 = x.ptr ∧
        s.readReg64 .x3 = x.new ∧ x.cap ≠ 0#64 ∧ x.bs.length ≤ x.cap.toNat ∧
        x.cap.toNat ≤ x.new.toNat ∧ 0 < x.new.toNat ∧ x.new.toNat + 1 ≤ 2 ^ 63⌝ ∗
      memRegion x.out 24 ∗
      A.live x.ptr x.cap.toNat 1 ∗ (x.ptr ↦ₛ x.bs) ∗
      memRegion (x.ptr + BitVec.ofNat 64 x.bs.length) (x.cap.toNat - x.bs.length) ∗
      A.pool ∗ stackAt s.sp finishGrow32Stack }

private theorem _root_.CryptoVerification.Cli.SpqrV1.Alloc.finish_grow_2_zero_ok_ext {A : RustAlloc} {b : BitVec 64}
    {ext : String → Option (State → State)} (hA : AllocContracts b A ext) :
    subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr CryptoVerification.Cli.SpqrV1.Alloc.finishGrow2Name)
      (finishGrow1AllocSpec A) := by
  unfold finishGrow1AllocSpec finishGrow1Spec
  simp only [memRegion_24, stackAt_finishGrow32, sepExists_sepConj_left, sepExists_sepConj_right]
  cells_unfold
  have hfn : libsignalSessionCode.fnOff CryptoVerification.Cli.SpqrV1.Alloc.finishGrow2Name = (ls_off% "<alloc::raw_vec::RawVecInner>::finish_grow [local#8]") :=
    (ls_lemma% fnOff "<alloc::raw_vec::RawVecInner>::finish_grow [local#8]")
  have hshim := shim_ok_at2_ext hA (name := CryptoVerification.Cli.SpqrV1.Alloc.finishGrow2Name)
    (k := num% (ls_off% "__rustc::__rust_no_alloc_shim_is_unstable_v2" - (ls_off% "<alloc::raw_vec::RawVecInner>::finish_grow [local#8]")))
  have halloc := alloc_ok_at_norm_ext hA (name := CryptoVerification.Cli.SpqrV1.Alloc.finishGrow2Name)
    (k := num% (ls_off% "__rustc::__rust_alloc" - (ls_off% "<alloc::raw_vec::RawVecInner>::finish_grow [local#8]")))
  code_fetches CryptoVerification.libsignalSessionCode spqrAllocBinCli b
    (Rust.withPanics ext) hfn (ls_off% "<alloc::raw_vec::RawVecInner>::finish_grow [local#8]") 168
  wp_init x s0
  examples_generalize_entry
  examples_hide_fetches
  obtain ⟨out, cap, ptr, new, bs⟩ := x
  dsimp only at *
  subst cap
  subst bs
  have hmsb := getLsbD_63_eq_false (new := new) (by omega)
  have hmsb' := getElem_63_eq_false (new := new) (by omega)
  have hcbz := beq_zero_eq_false h_8
  have hpow : ∃ k, 1 = 2 ^ k := ⟨0, rfl⟩
  wp_steps
  wp_apply
  wp_steps
  wp_apply
  wp_steps
  wp_if hoom
  · have hoom' : sf_1.readReg64 Reg.x0 ≠ 0 := hoom
    simp only [hoom', ite_false]
    wp_steps
    apply SepWP.instantiate_post_exists 0#64
    apply SepWP.instantiate_post_exists (sf_1.readReg64 Reg.x0)
    simp only [(by decide : (0#64 : BitVec 64) = 1#64 ↔ False), ite_false,
      pointsToBytes_nil, List.length_nil, BitVec.add_zero, Nat.sub_zero, emp_sepConj]
    wp_done
  · simp only [hoom, BitVec.ofNat_eq_ofNat, ite_true]
    wp_steps
    apply SepWP.instantiate_post_exists 1#64
    apply SepWP.instantiate_post_exists 1#64
    simp only [ite_true, FinishGrow1Call.oldBuf]
    wp_done

private theorem _root_.CryptoVerification.Cli.SpqrV1.Alloc.finish_grow_2_ne_ok_ext {A : RustAlloc} {b : BitVec 64}
    {ext : String → Option (State → State)} (hA : AllocContracts b A ext) :
    subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr CryptoVerification.Cli.SpqrV1.Alloc.finishGrow2Name)
      (finishGrow1ReallocSpec A) := by
  unfold finishGrow1ReallocSpec finishGrow1Spec
  simp only [memRegion_24, stackAt_finishGrow32, sepExists_sepConj_left, sepExists_sepConj_right]
  cells_unfold
  have hfn : libsignalSessionCode.fnOff CryptoVerification.Cli.SpqrV1.Alloc.finishGrow2Name = (ls_off% "<alloc::raw_vec::RawVecInner>::finish_grow [local#8]") :=
    (ls_lemma% fnOff "<alloc::raw_vec::RawVecInner>::finish_grow [local#8]")
  have hrealloc := realloc_ok_at_norm_ext hA (name := CryptoVerification.Cli.SpqrV1.Alloc.finishGrow2Name)
    (k := num% (ls_off% "__rustc::__rust_realloc" - (ls_off% "<alloc::raw_vec::RawVecInner>::finish_grow [local#8]")))
  code_fetches CryptoVerification.libsignalSessionCode spqrAllocBinCli b
    (Rust.withPanics ext) hfn (ls_off% "<alloc::raw_vec::RawVecInner>::finish_grow [local#8]") 168
  wp_init x s0
  examples_generalize_entry
  examples_hide_fetches
  obtain ⟨out, cap, ptr, new, bs⟩ := x
  dsimp only at *
  have hmsb := getLsbD_63_eq_false (new := new) (by omega)
  have hmsb' := getElem_63_eq_false (new := new) (by omega)
  have hcap_beq : (cap == 0#64) = false := beq_eq_false_iff_ne.mpr h_5
  have hle_new : bs.length ≤ new.toNat := by omega
  have hpow : ∃ k, 1 = 2 ^ k := ⟨0, rfl⟩
  wp_steps
  wp_apply
  wp_steps
  wp_if hoom
  · have hoom' : sf.readReg64 Reg.x0 ≠ 0 := hoom
    simp only [hoom', ite_false]
    wp_steps
    apply SepWP.instantiate_post_exists 0#64
    apply SepWP.instantiate_post_exists (sf.readReg64 Reg.x0)
    simp only [(by decide : (0#64 : BitVec 64) = 1#64 ↔ False), ite_false]
    wp_done
  · simp only [hoom, BitVec.ofNat_eq_ofNat, ite_true]
    wp_steps
    apply SepWP.instantiate_post_exists 1#64
    apply SepWP.instantiate_post_exists 1#64
    simp only [ite_true, FinishGrow1Call.oldBuf, h_5, ite_false]
    wp_done

/-- `<alloc::raw_vec::RawVecInner>::finish_grow [local#8]` meets `finishGrow1Spec A`
on `tripleRatchetProgAtExt b ext`. -/
theorem _root_.CryptoVerification.Cli.SpqrV1.Alloc.finish_grow_2_ok_ext {A : RustAlloc} {b : BitVec 64}
    {ext : String → Option (State → State)} (hA : AllocContracts b A ext) :
    subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr CryptoVerification.Cli.SpqrV1.Alloc.finishGrow2Name)
      (finishGrow1Spec A) := by
  refine subroutine_ok_outcome_intro fun x R s0 hpc hrun hpre hsp => ?_
  by_cases hcap0 : x.cap = 0#64
  · refine (subroutine_ok_apply_outcome
      (CryptoVerification.Cli.SpqrV1.Alloc.finish_grow_2_zero_ok_ext hA) x R hpc hrun ?_ hsp).mono_outcome
      fun _ => id
    simp only [finishGrow1Spec, finishGrow1AllocSpec, FinishGrow1Call.oldBuf, hcap0, ite_true,
      emp_sepConj, sepConj_assoc, satisfies_pure_sepConj] at hpre ⊢
    rcases hpre with ⟨⟨hx0, hx1, hx2, hx3, hbs0, _, hle, hnew, hlay⟩, hmem⟩
    exact ⟨⟨hx0, hx1, hx2, hx3, trivial, hbs0 trivial, hle, hnew, hlay⟩, hmem⟩
  · refine (subroutine_ok_apply_outcome
      (CryptoVerification.Cli.SpqrV1.Alloc.finish_grow_2_ne_ok_ext hA) x R hpc hrun ?_ hsp).mono_outcome
      fun _ => id
    simp only [finishGrow1Spec, finishGrow1ReallocSpec, FinishGrow1Call.oldBuf, hcap0, ite_false,
      sepConj_assoc, satisfies_pure_sepConj] at hpre ⊢
    rcases hpre with ⟨⟨hx0, hx1, hx2, hx3, _, hbs, hle, hnew, hlay⟩, hmem⟩
    exact ⟨⟨hx0, hx1, hx2, hx3, hcap0, hbs, hle, hnew, hlay⟩, hmem⟩

end CryptoVerification.SpqrV1.Alloc
