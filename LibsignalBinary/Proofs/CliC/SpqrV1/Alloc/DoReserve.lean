/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SpqrV1.Alloc.DoReserve
import GeneratedLean.LibsignalSessionCode -- shake: keep
import LibsignalBinary.Proofs.CliC.SpqrV1.Alloc.Fetch
import LibsignalBinary.Proofs.CliC.SpqrV1.Alloc.FinishGrow
import LibsignalBinary.Proofs.CodeLayout
import LibsignalBinary.Proofs.TripleRatchet.GeneralizeEntry
import ProofLib.SepLogic.WP.Apply
import ProofLib.SepLogic.WPp

/-!
# `RawVecInner::do_reserve_and_handle` Proofs for `CliC`

Proves `doReserveStrideRawSpec`, `doReserveRawSpec`, and `doReserveSpec` (plus `AllocContractsX`
variants) for `RawVecInner::reserve::do_reserve_and_handle` in the CLI image.
-/

@[expose] public section

namespace CryptoVerification.SpqrV1.Alloc

open Arm64 ProofLib CryptoGames CryptoGames.HMAC CryptoGames.LibsignalSession

open CryptoVerification.RustHeap CryptoVerification.LibsignalSessionRepr

open CryptoVerification.LibsignalTripleRatchet CryptoVerification.CodeLayout

set_option maxRecDepth 200000

set_option maxHeartbeats 400000

attribute [local irreducible] Program.fetch Program.externAt? Program.fnOff

attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero

namespace DoReserveNorm

end DoReserveNorm

open DoReserveNorm

/-! ## Symbol Names and Capacity Helpers -/

abbrev _root_.CryptoVerification.CliC.SpqrV1.Alloc.doReserve7Name : String :=
  "<alloc::raw_vec::RawVecInner<_>>::reserve::do_reserve_and_handle::<alloc::alloc::Global> [local#9]"

private theorem stackAt_doReserve (sp : BitVec 64) :
    stackAt sp doReserveStack =
      stackAt (sp - 64#64) finishGrowStack ∗
        (∃∗ v0 : BitVec 64, ∃∗ v1 : BitVec 64, ∃∗ v2 : BitVec 64, ∃∗ v3 : BitVec 64,
         ∃∗ v4 : BitVec 64, ∃∗ v5 : BitVec 64, ∃∗ v6 : BitVec 64, ∃∗ v7 : BitVec 64,
          ((sp - 64#64) ↦₆₄ v0) ∗ ((sp - 56#64) ↦₆₄ v1) ∗ ((sp - 48#64) ↦₆₄ v2) ∗
          ((sp - 40#64) ↦₆₄ v3) ∗ ((sp - 32#64) ↦₆₄ v4) ∗ ((sp - 24#64) ↦₆₄ v5) ∗
          ((sp - 16#64) ↦₆₄ v6) ∗ ((sp - 8#64) ↦₆₄ v7)) := by
  have h1 := ProofLib.stackAt_split_cells sp 4144 8 (by decide)
  change stackAt sp doReserveStack =
    stackAt (sp - 64#64) finishGrowStack ∗ cells (sp - 64#64) 8 at h1
  have hc8 : cells (sp - 64#64) 8 =
      (∃∗ v0 : BitVec 64, ∃∗ v1 : BitVec 64, ∃∗ v2 : BitVec 64, ∃∗ v3 : BitVec 64,
       ∃∗ v4 : BitVec 64, ∃∗ v5 : BitVec 64, ∃∗ v6 : BitVec 64, ∃∗ v7 : BitVec 64,
        ((sp - 64#64) ↦₆₄ v0) ∗ ((sp - 56#64) ↦₆₄ v1) ∗ ((sp - 48#64) ↦₆₄ v2) ∗
        ((sp - 40#64) ↦₆₄ v3) ∗ ((sp - 32#64) ↦₆₄ v4) ∗ ((sp - 24#64) ↦₆₄ v5) ∗
        ((sp - 16#64) ↦₆₄ v6) ∗ ((sp - 8#64) ↦₆₄ v7)) := by
    cells_unfold
  rw [h1, hc8]

private def finishGrow8ZeroCellsSpec (A : RustAlloc) : Spec FG8Ghost where
  pre := fun (out, cap, ptr, new, align, stride, bs, o0, o1, o2, fsp) s =>
    ⌜s.readReg64 .x0 = out ∧ s.readReg64 .x1 = cap ∧ s.readReg64 .x2 = ptr ∧
      s.readReg64 .x3 = new ∧ s.readReg64 .x4 = align ∧ s.readReg64 .x5 = stride ∧
      s.sp = fsp ∧ cap = 0#64 ∧ bs = [] ∧ cap.toNat ≤ new.toNat ∧
      0 < new.toNat ∧ 0 < stride.toNat ∧ LayoutOk (new.toNat * stride.toNat) align.toNat⌝ ∗
    (out ↦₆₄ o0) ∗ ((out + 8#64) ↦₆₄ o1) ∗ ((out + 16#64) ↦₆₄ o2) ∗
    A.pool ∗ stackAt fsp finishGrowStack
  post := fun (out, _cap, _ptr, new, align, stride, _bs, _o0, _o1, _o2, fsp) s0 sf =>
    ∃∗ tag : BitVec 64, ∃∗ p' : BitVec 64, ∃∗ o2' : BitVec 64,
      (if tag = 1#64 then
        ⌜sf.trace = s0.trace ++ [allocFailedEvent]⌝
       else
        ⌜tag = 0#64 ∧ p' ≠ 0#64 ∧ p'.toNat % align.toNat = 0 ∧ sf.trace = s0.trace⌝ ∗
          A.live p' (new.toNat * stride.toNat) align.toNat ∗
          memRegion p' (new.toNat * stride.toNat)) ∗
      A.pool ∗ stackAt fsp finishGrowStack ∗
      (out ↦₆₄ tag) ∗ ((out + 8#64) ↦₆₄ p') ∗ ((out + 16#64) ↦₆₄ o2')

private theorem _root_.CryptoVerification.CliC.SpqrV1.Alloc.finish_grow_8_zero_cells_ok_ext {A : RustAlloc} {b : BitVec 64}
    {ext : String → Option (State → State)} (hA : AllocContracts b A ext) :
    subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr CryptoVerification.CliC.SpqrV1.Alloc.finishGrow8Name)
      (finishGrow8ZeroCellsSpec A) := by
  refine subroutine_ok_outcome_intro ?_
  intro ⟨out, cap, ptr, new, align, stride, bs, o0, o1, o2, fsp⟩ R s0 hpc hrun hpre hsp
  simp only [finishGrow8ZeroCellsSpec, sepConj_assoc, satisfies_pure_sepConj] at hpre
  rcases hpre with ⟨⟨hx0, hx1, hx2, hx3, hx4, hx5, hfsp, hcap0, hbs, hle, hpos, hstr, hlay⟩, hmem⟩
  subst hfsp; subst hcap0; subst hbs
  let hcall : FinishGrowCall := ⟨out, 0#64, ptr, new, align, stride, []⟩
  have hpre' : s0.mem ⊨ (finishGrowSpec A).pre hcall s0 ∗ R := by
    simp only [finishGrowSpec, hcall, FinishGrowCall.oldBuf, ite_true,
      memRegion_24, emp_sepConj, sepExists_sepConj_left, sepExists_sepConj_right,
      satisfies_sepExists]
    refine ⟨o2, o1, o0, ?_⟩
    rw [sepConj_assoc, satisfies_pure_sepConj]
    exact ⟨⟨hx0, hx1, hx2, hx3, hx4, hx5, fun _ => trivial, Nat.zero_le _, hle, hpos, hstr, hlay⟩,
      by simpa only [sepConj_assoc] using hmem⟩
  refine subroutine_ok.mono_outcome (CryptoVerification.CliC.SpqrV1.Alloc.finish_grow_8_ok_ext hA)
    hcall R s0 hpc hrun hpre' hsp ?_
  rintro sf (⟨hret, hcc, hq⟩ | hfail)
  · refine Or.inl ⟨hret, hcc, ?_⟩
    simp only [finishGrowSpec, finishGrow8ZeroCellsSpec, hcall, FinishGrowCall.oldBuf,
      ite_true, pointsToBytes_nil, List.length_nil,
      BitVec.add_zero, Nat.sub_zero, emp_sepConj, sepConj_emp,
      sepExists_sepConj_left, satisfies_sepExists] at hq ⊢
    rcases hq with ⟨tag, p', hq⟩
    refine ⟨tag, p', BitVec.ofNat 64 (new.toNat * stride.toNat), ?_⟩
    by_cases htag : tag = 1#64
    · simp only [htag, ite_true] at hq ⊢
      rw [pull_fg0_err, satisfies_pure_sepConj] at hq
      rw [sepConj_assoc, satisfies_pure_sepConj]
      exact ⟨hq.1.2, hq.2⟩
    · simp only [htag, ite_false] at hq ⊢
      rw [pull_fg0_ok, satisfies_pure_sepConj] at hq
      rw [sepConj_assoc, sepConj_assoc, satisfies_pure_sepConj]
      exact ⟨hq.1, by simpa only [sepConj_assoc] using hq.2⟩
  · exact Or.inr hfail

private def finishGrow8NeCellsSpec (A : RustAlloc) : Spec FG8Ghost where
  pre := fun (out, cap, ptr, new, align, stride, bs, o0, o1, o2, fsp) s =>
    ⌜s.readReg64 .x0 = out ∧ s.readReg64 .x1 = cap ∧ s.readReg64 .x2 = ptr ∧
      s.readReg64 .x3 = new ∧ s.readReg64 .x4 = align ∧ s.readReg64 .x5 = stride ∧
      s.sp = fsp ∧ cap ≠ 0#64 ∧ bs.length ≤ cap.toNat * stride.toNat ∧ cap.toNat ≤ new.toNat ∧
      0 < new.toNat ∧ 0 < stride.toNat ∧ LayoutOk (new.toNat * stride.toNat) align.toNat⌝ ∗
    (out ↦₆₄ o0) ∗ ((out + 8#64) ↦₆₄ o1) ∗ ((out + 16#64) ↦₆₄ o2) ∗
    A.live ptr (cap.toNat * stride.toNat) align.toNat ∗ (ptr ↦ₛ bs) ∗
    memRegion (ptr + BitVec.ofNat 64 bs.length) (cap.toNat * stride.toNat - bs.length) ∗
    A.pool ∗ stackAt fsp finishGrowStack
  post := fun (out, cap, ptr, new, align, stride, bs, _o0, _o1, _o2, fsp) s0 sf =>
    ∃∗ tag : BitVec 64, ∃∗ p' : BitVec 64, ∃∗ o2' : BitVec 64,
      (if tag = 1#64 then
        ⌜sf.trace = s0.trace ++ [allocFailedEvent]⌝ ∗
          A.live ptr (cap.toNat * stride.toNat) align.toNat ∗ (ptr ↦ₛ bs) ∗
          memRegion (ptr + BitVec.ofNat 64 bs.length) (cap.toNat * stride.toNat - bs.length)
       else
        ⌜tag = 0#64 ∧ p' ≠ 0#64 ∧ p'.toNat % align.toNat = 0 ∧ sf.trace = s0.trace⌝ ∗
          A.live p' (new.toNat * stride.toNat) align.toNat ∗ (p' ↦ₛ bs) ∗
          memRegion (p' + BitVec.ofNat 64 bs.length) (new.toNat * stride.toNat - bs.length)) ∗
      A.pool ∗ stackAt fsp finishGrowStack ∗
      (out ↦₆₄ tag) ∗ ((out + 8#64) ↦₆₄ p') ∗ ((out + 16#64) ↦₆₄ o2')

private theorem _root_.CryptoVerification.CliC.SpqrV1.Alloc.finish_grow_8_ne_cells_ok_ext {A : RustAlloc} {b : BitVec 64}
    {ext : String → Option (State → State)} (hA : AllocContracts b A ext) :
    subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr CryptoVerification.CliC.SpqrV1.Alloc.finishGrow8Name)
      (finishGrow8NeCellsSpec A) := by
  refine subroutine_ok_outcome_intro ?_
  intro ⟨out, cap, ptr, new, align, stride, bs, o0, o1, o2, fsp⟩ R s0 hpc hrun hpre hsp
  simp only [finishGrow8NeCellsSpec, sepConj_assoc, satisfies_pure_sepConj] at hpre
  rcases hpre with ⟨⟨hx0, hx1, hx2, hx3, hx4, hx5, hfsp, hcap, hbs, hle, hpos, hstr, hlay⟩, hmem⟩
  subst hfsp
  let hcall : FinishGrowCall := ⟨out, cap, ptr, new, align, stride, bs⟩
  have hpre' : s0.mem ⊨ (finishGrowSpec A).pre hcall s0 ∗ R := by
    simp only [finishGrowSpec, hcall, FinishGrowCall.oldBuf, hcap, ite_false,
      memRegion_24, sepExists_sepConj_left, sepExists_sepConj_right,
      satisfies_sepExists]
    refine ⟨o2, o1, o0, ?_⟩
    rw [sepConj_assoc, satisfies_pure_sepConj]
    exact ⟨⟨hx0, hx1, hx2, hx3, hx4, hx5, False.elim, hbs, hle, hpos, hstr, hlay⟩,
      by simpa only [sepConj_assoc] using hmem⟩
  refine subroutine_ok.mono_outcome (CryptoVerification.CliC.SpqrV1.Alloc.finish_grow_8_ok_ext hA)
    hcall R s0 hpc hrun hpre' hsp ?_
  rintro sf (⟨hret, hcc, hq⟩ | hfail)
  · refine Or.inl ⟨hret, hcc, ?_⟩
    simp only [finishGrowSpec, finishGrow8NeCellsSpec, hcall, FinishGrowCall.oldBuf,
      hcap, ite_false, sepExists_sepConj_left, satisfies_sepExists] at hq ⊢
    rcases hq with ⟨tag, p', hq⟩
    refine ⟨tag, p', BitVec.ofNat 64 (new.toNat * stride.toNat), ?_⟩
    by_cases htag : tag = 1#64
    · simp only [htag, ite_true] at hq ⊢
      rw [pull_fg1_post, satisfies_pure_sepConj] at hq
      rw [sepConj_assoc, sepConj_assoc, satisfies_pure_sepConj]
      exact ⟨hq.1.2, by simpa only [sepConj_assoc] using hq.2⟩
    · simp only [htag, ite_false] at hq ⊢
      rw [pull_fg1_post, satisfies_pure_sepConj] at hq
      rw [sepConj_assoc, sepConj_assoc, satisfies_pure_sepConj]
      exact ⟨hq.1, by simpa only [sepConj_assoc] using hq.2⟩
  · exact Or.inr hfail

/-! ## `do_reserve_and_handle` Contracts -/

theorem _root_.CryptoVerification.CliC.SpqrV1.Alloc.do_reserve_7_stride_raw_ok_ext {A : RustAlloc} {b : BitVec 64}
    {ext : String → Option (State → State)} (hA : AllocContracts b A ext) :
    subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr CryptoVerification.CliC.SpqrV1.Alloc.doReserve7Name)
      (doReserveStrideRawSpec A) := by
  simp only [doReserveStrideRawSpec, stackAt_doReserve, sepExists_sepConj_right]
  have hfn : libsignalSessionCode.fnOff CryptoVerification.CliC.SpqrV1.Alloc.doReserve7Name = (ls_off% "<alloc::raw_vec::RawVecInner<_>>::reserve::do_reserve_and_handle::<alloc::alloc::Global> [local#9]") :=
    (ls_lemma% fnOff "<alloc::raw_vec::RawVecInner<_>>::reserve::do_reserve_and_handle::<alloc::alloc::Global> [local#9]")
  have hpanic := panic_at_handle_error_norm_ext (b := b) (ext := ext)
    (name := CryptoVerification.CliC.SpqrV1.Alloc.doReserve7Name) (k := num% (ls_off% "alloc::raw_vec::handle_error" - (ls_off% "<alloc::raw_vec::RawVecInner<_>>::reserve::do_reserve_and_handle::<alloc::alloc::Global> [local#9]")))
    (by rw [hfn, (ls_stub% "alloc::raw_vec::handle_error")])
  have hfg0 := CryptoVerification.CliC.SpqrV1.Alloc.finish_grow_8_zero_cells_ok_ext hA
  have hfg1 := CryptoVerification.CliC.SpqrV1.Alloc.finish_grow_8_ne_cells_ok_ext hA
  rw [Program.fnAddr_rel (name := CryptoVerification.CliC.SpqrV1.Alloc.doReserve7Name)
    hfn (ls_lemma% fnOff "<alloc::raw_vec::RawVecInner>::finish_grow [local#10]") (k := (num% (ls_off% "<alloc::raw_vec::RawVecInner>::finish_grow [local#10]" - ls_off% "<alloc::raw_vec::RawVecInner<_>>::reserve::do_reserve_and_handle::<alloc::alloc::Global> [local#9]"))) (by decide)] at hfg0 hfg1
  code_fetches CryptoVerification.libsignalSessionCode spqrAllocBinCliC b
    (Rust.withPanics ext) hfn (ls_off% "<alloc::raw_vec::RawVecInner<_>>::reserve::do_reserve_and_handle::<alloc::alloc::Global> [local#9]") 140
  dsimp only [tripleRatchetProgAtExt] at hpanic hfg0 hfg1 ⊢
  clear hfn hA
  generalize_entry (libsignalSessionCode.rebase b
    (Rust.withPanics ext)).fnAddr CryptoVerification.CliC.SpqrV1.Alloc.doReserve7Name = entry
  generalize_entry (libsignalSessionCode.rebase b
    (Rust.withPanics ext)) = prog
    reverting [Program.fetch, Program.externAt?, subroutine_ok]
  examples_hide_fetches
  wpp_init x s0
  obtain ⟨v, cap, ptr, bs, len, additional, align, stride⟩ := x
  dsimp only at *
  have hsz_pos : 0 < reserveCapStride stride.toNat cap.toNat len additional * stride.toNat := h.1
  have hpow : ∃ k, align.toNat = 2 ^ k := h.2.1
  have hbound :
      reserveCapStride stride.toNat cap.toNat len additional * stride.toNat + align.toNat ≤ 2 ^ 63 :=
    h.2.2
  have halign_pos : 1 ≤ align.toNat := by
    rcases hpow with ⟨k, hk⟩; rw [hk]; exact Nat.one_le_two_pow
  have hmin_ge : 4 ≤ reserveMinCap stride.toNat := by
    unfold reserveMinCap; split <;> omega
  have hnew_lt63 : reserveCapStride stride.toNat cap.toNat len additional < 2 ^ 63 := by
    have : reserveCapStride stride.toNat cap.toNat len additional * 1 ≤
        reserveCapStride stride.toNat cap.toNat len additional * stride.toNat :=
      Nat.mul_le_mul_left _ h_9
    omega
  have hmax : max (max (len + additional) (2 * cap.toNat)) (reserveMinCap stride.toNat) < 2 ^ 63 :=
    hnew_lt63
  have hcs := adds_cs_eq_false (x2 := s0.readReg64 .x2) (x1 := s0.readReg64 .x1) (by
    rw [h_3, h_2]; omega)
  have hnew_eq := reserve_new_cap_stride_eq (stride := stride) (cap := cap) h_2 h_3 hnew_lt63
  let new := BitVec.ofNat 64 (reserveCapStride stride.toNat cap.toNat len additional)
  have hnew_toNat : new.toNat = reserveCapStride stride.toNat cap.toNat len additional := by
    dsimp [new]; rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  have hcap_le_new : cap.toNat ≤ new.toNat := by
    rw [hnew_toNat]; dsimp [reserveCapStride]; omega
  have hnew_pos : 0 < new.toNat := by
    rw [hnew_toNat]; dsimp [reserveCapStride]; omega
  have hnew_lay : LayoutOk (new.toNat * stride.toNat) align.toNat := by
    rw [hnew_toNat]; exact h
  by_cases hcap0 : cap = 0#64
  · subst hcap0
    have h0_mul : (0#64 : BitVec 64).toNat * stride.toNat = 0 := Nat.zero_mul stride.toNat
    have hbs : bs = [] := List.eq_nil_of_length_eq_zero (by omega)
    subst hbs
    have hnew_eq0 :
        (if (if (stride == 1#64) = true then 8#64 else 4#64).ult
              (if (0#64).ult (s0.readReg64 .x2 + s0.readReg64 .x1) = true then
                s0.readReg64 .x2 + s0.readReg64 .x1
               else 0#64) = true then
          if (0#64).ult (s0.readReg64 .x2 + s0.readReg64 .x1) = true then
            s0.readReg64 .x2 + s0.readReg64 .x1
          else 0#64
         else if (stride == 1#64) = true then 8#64 else 4#64) = new := hnew_eq
    have hmul_eq : reserveCapStride stride.toNat 0 len additional * stride.toNat =
        new.toNat * stride.toNat := by
      rw [hnew_toNat]; rfl
    simp only [ite_true, emp_sepConj, pointsToBytes_nil,
      List.length_nil, BitVec.add_zero, Nat.sub_zero, BitVec.toNat_ofNat, Nat.zero_mod, hmul_eq]
    apply SepWPp.of_sepWP (mid := entry + 88#64)
    wp_steps
    wp_apply
    apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
    by_cases htag : w = 1#64
    · simp only [htag, ite_true, sepConj_assoc]
      refine SepWPp.pure_elim fun htrace => ?_
      apply SepWPp.of_sepWP (mid := entry + bv% ((2^64 + ls_off% "alloc::raw_vec::handle_error" - (ls_off% "<alloc::raw_vec::RawVecInner<_>>::reserve::do_reserve_and_handle::<alloc::alloc::Global> [local#9]")) % 2^64))
      wp_steps
      apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
      refine SepWPp.panic (by simp only [wp_norm, arm64_norm, *]) (by wp_norm_lhs) fun hm => ?_
      simpa only [sepConj_assoc] using
        allowPanic_panicked (allocFailedIn_of_eq (by simp only [Rust.panicked, wp_norm, arm64_norm, *])) hm
    · simp only [htag, ite_false, sepConj_assoc]
      refine SepWPp.pure_elim fun ⟨hw0, hp', halign, htrace⟩ => ?_
      subst hw0
      apply SepWPp.of_sepWP_ret
      wp_steps
      wp_done
  · simp only [hcap0, ite_false, sepConj_assoc]
    have hsub_eq :
        reserveCapStride stride.toNat cap.toNat len additional * stride.toNat - bs.length =
          new.toNat * stride.toNat - bs.length := by rw [hnew_toNat]
    have hmul_eq :
        reserveCapStride stride.toNat cap.toNat len additional * stride.toNat =
          new.toNat * stride.toNat := by rw [hnew_toNat]
    rw [hsub_eq, hmul_eq]
    apply SepWPp.of_sepWP (mid := entry + 88#64)
    wp_steps
    wp_apply
    apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
    by_cases htag : w = 1#64
    · simp only [htag, ite_true, sepConj_assoc]
      refine SepWPp.pure_elim fun htrace => ?_
      apply SepWPp.of_sepWP (mid := entry + bv% ((2^64 + ls_off% "alloc::raw_vec::handle_error" - (ls_off% "<alloc::raw_vec::RawVecInner<_>>::reserve::do_reserve_and_handle::<alloc::alloc::Global> [local#9]")) % 2^64))
      wp_steps
      apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
      refine SepWPp.panic (by simp only [wp_norm, arm64_norm, *]) (by wp_norm_lhs) fun hm => ?_
      simpa only [sepConj_assoc] using
        allowPanic_panicked (allocFailedIn_of_eq (by simp only [Rust.panicked, wp_norm, arm64_norm, *])) hm
    · simp only [htag, ite_false, sepConj_assoc]
      refine SepWPp.pure_elim fun ⟨hw0, hp', halign, htrace⟩ => ?_
      subst hw0
      apply SepWPp.of_sepWP_ret
      wp_steps
      wp_done

theorem _root_.CryptoVerification.CliC.SpqrV1.Alloc.do_reserve_7_raw_ok_ext {A : RustAlloc} {b : BitVec 64}
    {ext : String → Option (State → State)} (hA : AllocContracts b A ext) :
    subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr CryptoVerification.CliC.SpqrV1.Alloc.doReserve7Name)
      (doReserveRawSpec A) := by
  refine subroutine_ok_outcome_intro ?_
  intro x R s0 hpc hrun hpre hsp
  simp only [doReserveRawSpec, sepConj_assoc, satisfies_pure_sepConj] at hpre
  rcases hpre with ⟨⟨hx0, hx1, hx2, hx3, hx4, hlen, hptr, hbound⟩, hmem⟩
  let xs : DoReserveStrideCall := ⟨x.v, x.cap, x.ptr, x.bs, x.bs.length, x.additional, 1#64, 1#64⟩
  have hlay : LayoutOk (reserveCap x.cap.toNat x.bs.length x.additional) 1 := by
    refine ⟨by dsimp [reserveCap]; omega, ⟨0, rfl⟩, by omega⟩
  have hpre' : s0.mem ⊨ (doReserveStrideRawSpec A).pre xs s0 ∗ R := by
    simp only [doReserveStrideRawSpec, xs, BitVec.toNat_ofNat, Nat.one_mod,
      reserveCapStride_one, Nat.mul_one, sepConj_assoc, satisfies_pure_sepConj]
    exact ⟨⟨hx0, hx1, hx2, hx3, hx4, hlen, hlen, hptr, by decide, hlay⟩, hmem⟩
  refine subroutine_ok.mono_outcome
    (CryptoVerification.CliC.SpqrV1.Alloc.do_reserve_7_stride_raw_ok_ext hA)
    xs R s0 hpc hrun hpre' hsp ?_
  rintro sf (⟨hret, hcc, hq⟩ | hfail)
  · refine Or.inl ⟨hret, hcc, ?_⟩
    simp only [doReserveStrideRawSpec, doReserveRawSpec, xs, BitVec.toNat_ofNat, Nat.one_mod,
      reserveCapStride_one, Nat.mul_one, Nat.mod_one, and_true] at hq ⊢
    exact hq
  · exact Or.inr hfail

private theorem vecU8At_eq (A : RustAlloc) (v cap ptr : BitVec 64) (bs : List (BitVec 8)) :
    vecU8At A v cap ptr bs =
      ⌜bs.length ≤ cap.toNat ∧ cap.toNat < 2 ^ 63 ∧ ptr ≠ 0#64⌝ ∗
      (v ↦₆₄ cap) ∗ ((v + 8#64) ↦₆₄ ptr) ∗ ((v + 16#64) ↦₆₄ BitVec.ofNat 64 bs.length) ∗
      (if cap = 0#64 then emp
       else A.live ptr cap.toNat 1 ∗ (ptr ↦ₛ bs) ∗
         memRegion (ptr + BitVec.ofNat 64 bs.length) (cap.toNat - bs.length)) := by
  simp only [vecU8At, vecHeader, BitVec.ofNat_eq_ofNat]
  ac_rfl

private theorem do_reserve_vec_of_raw {A : RustAlloc} {b : BitVec 64}
    {ext : String → Option (State → State)} {name : String}
    (hraw : subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr name) (doReserveRawSpec A)) :
    subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr name)
      (doReserveSpec A) := by
  refine subroutine_ok_outcome_intro ?_
  intro x R s0 hpc hrun hpre hsp
  simp only [doReserveSpec, vecU8At_eq, sepConj_assoc, satisfies_pure_sepConj] at hpre
  rcases hpre with ⟨⟨hx0, hx1, hx2, hx3, hx4, hbound⟩, ⟨hlen, hcap63, hptr⟩, hmem⟩
  have hpre' : s0.mem ⊨ (doReserveRawSpec A).pre x s0 ∗
      (((x.v + 16#64) ↦₆₄ BitVec.ofNat 64 x.bs.length) ∗ R) := by
    simp only [doReserveRawSpec, sepConj_assoc, satisfies_pure_sepConj]
    refine ⟨⟨hx0, hx1, hx2, hx3, hx4, hlen, hptr, hbound⟩, ?_⟩
    rwa [doReserve_pre_repack]
  refine subroutine_ok.mono_outcome hraw x
    (((x.v + 16#64) ↦₆₄ BitVec.ofNat 64 x.bs.length) ∗ R) s0 hpc hrun hpre' hsp ?_
  rintro sf (⟨hret, hcc, hq⟩ | ⟨hpan, hq⟩ | ⟨code, hex, hq⟩ | ⟨hoom, hq⟩)
  · refine Or.inl ⟨hret, hcc, ?_⟩
    simp only [doReserveRawSpec, doReserveSpec, vecU8At_eq] at hq ⊢
    rw [sepConj_assoc, satisfies_pure_sepConj] at hq
    rcases hq with ⟨htrace, hq⟩
    simp only [sepExists_sepConj_left, satisfies_sepExists] at hq
    rcases hq with ⟨p', hq⟩
    rw [sepConj_assoc, sepConj_assoc, satisfies_pure_sepConj] at hq
    rcases hq with ⟨hp', hmem⟩
    have hlt : reserveCap x.cap.toNat x.bs.length x.additional < 2 ^ 64 := by
      dsimp [reserveCap] at hbound ⊢; omega
    have htoNat : (BitVec.ofNat 64 (reserveCap x.cap.toNat x.bs.length x.additional)).toNat =
        reserveCap x.cap.toNat x.bs.length x.additional := by
      rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hlt]
    have hlen_le : x.bs.length ≤ reserveCap x.cap.toNat x.bs.length x.additional := by
      dsimp [reserveCap]; omega
    have hcap63' : reserveCap x.cap.toNat x.bs.length x.additional < 2 ^ 63 := by
      omega
    have hcap_ne : BitVec.ofNat 64 (reserveCap x.cap.toNat x.bs.length x.additional) ≠ 0#64 := by
      intro heq
      have := congrArg BitVec.toNat heq
      rw [htoNat] at this
      change reserveCap x.cap.toNat x.bs.length x.additional = 0 at this
      dsimp [reserveCap] at this; omega
    rw [sepConj_assoc, satisfies_pure_sepConj]
    refine ⟨htrace, ?_⟩
    simp only [sepExists_sepConj_left, satisfies_sepExists]
    refine ⟨p', ?_⟩
    simp only [hcap_ne, ite_false, htoNat]
    rw [sepConj_assoc, sepConj_assoc, satisfies_pure_sepConj]
    refine ⟨⟨hlen_le, hcap63', hp'⟩, ?_⟩
    rwa [doReserve_post_repack]
  · refine Or.inr (Or.inl ⟨hpan, ?_⟩)
    dsimp only [doReserveRawSpec, doReserveSpec] at hq ⊢
    exact allowPanic_frame id (by rwa [sepConj_assoc])
  · exact (allowPanic_not_exited hq).elim
  · exact (allowPanic_not_exited hq).elim

theorem _root_.CryptoVerification.CliC.SpqrV1.Alloc.do_reserve_7_ok_ext {A : RustAlloc} {b : BitVec 64}
    {ext : String → Option (State → State)} (hA : AllocContracts b A ext) :
    subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr CryptoVerification.CliC.SpqrV1.Alloc.doReserve7Name)
      (doReserveSpec A) :=
  do_reserve_vec_of_raw (CryptoVerification.CliC.SpqrV1.Alloc.do_reserve_7_raw_ok_ext hA)

theorem _root_.CryptoVerification.CliC.SpqrV1.Alloc.do_reserve_7_ok_ext_x {img : Obj.Image} {A : RustAlloc}
    {ext : String → Option (State → State)} (hA : AllocContracts img.base A ext) :
    subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr CryptoVerification.CliC.SpqrV1.Alloc.doReserve7Name) ((doReserveSpecX A).inImage img) :=
  subroutine_ok_inImage_of_subroutine_ok img (doReserveSpecX_of_doReserveSpec (CryptoVerification.CliC.SpqrV1.Alloc.do_reserve_7_ok_ext hA))

end CryptoVerification.SpqrV1.Alloc
