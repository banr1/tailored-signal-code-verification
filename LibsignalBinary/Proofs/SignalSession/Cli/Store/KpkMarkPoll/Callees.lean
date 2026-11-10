/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SignalSession.Cli.Specs
public import LibsignalBinary.Proofs.SpqrV1.Varint.EncodeVarintPlacedCommon
import GeneratedLean.LibsignalSessionCode -- shake: keep
import LibsignalBinary.Proofs.SignalSession.Cli.Dir.FinishGrow
import LibsignalBinary.Proofs.SignalSession.Cli.Dir.GrowOne.Layout
import LibsignalBinary.Proofs.SignalSession.Cli.Store.KpkMarkPoll.Fetches
import LibsignalBinary.Proofs.SpqrV1.Alloc.DoReserve
import LibsignalBinary.Proofs.TripleRatchet.GeneralizeEntry
import LibsignalBinary.Proofs.TripleRatchet.Prost.BytesMerge.Phase23
import ProofLib.SepLogic.WP.Apply
import ProofLib.SepLogic.WPp

/-!
# Self-Contained Callee Contracts for `KpkMarkPoll`

Proves directly from `AllocContractsX img A ext`:
1. `kpkReserve_ok`: `do_reserve_and_handle [local#11]` (`cliDoReserveName`) meets
   `(SpqrV1.Varint.doReserveSpecOf resStack A).inImage img` for `doReserveStackX ≤ resStack`.
2. `kpkConcat2_pos_ok`: `<[&[u8]] as alloc::slice::Concat<u8>>::concat [local#3]` meets
   `(kpkConcat2PosSpec A stk).inImage img` on two non-empty owned byte slices.
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 400000

namespace CryptoVerification.SignalSession.Cli.Store.KpkMarkPoll.Helpers

open Arm64 ProofLib ProofLib.ProgramReflection CryptoGames.LibsignalSession
open CryptoVerification.RustHeap CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchetRepr CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalSession CryptoVerification.CodeLayout
open CryptoVerification.SignalSession.Cli
open CryptoVerification.SpqrV1.Alloc.DoReserveNorm

attribute [local irreducible] Program.fetch Program.externAt? Program.fnOff
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero

abbrev cliConcatName : String := "<[&[u8]] as alloc::slice::Concat<u8>>::concat [local#3]"

private theorem cliConcat_fnOff :
    libsignalSessionCode.fnOff cliConcatName =
      ls_off% "<[&[u8]] as alloc::slice::Concat<u8>>::concat [local#3]" :=
  ls_lemma% fnOff "<[&[u8]] as alloc::slice::Concat<u8>>::concat [local#3]"

private abbrev cliConcatStack : Nat := 96 + extHookStack

private theorem stackAt_split_ge (sp : BitVec 64) {n m : Nat} (hle : n ≤ m) (hlt : m ≤ 2 ^ 64) :
    stackAt sp m = memRegion (sp - BitVec.ofNat 64 m) (m - n) ∗ stackAt sp n := by
  have h := ProofLib.stackAt_split_bottom sp n (m - n) (by omega)
  have heq : n + (m - n) = m := by omega
  simpa only [heq] using h

private theorem subroutine_ok_frame_weaken {α : Type} {prog : Program} {entry : BitVec 64}
    {spec spec' : Spec α} (F : α → State → SepProp)
    (h : subroutine_ok prog entry spec)
    (hpre : ∀ x s0, spec'.pre x s0 ⊢ spec.pre x s0 ∗ F x s0)
    (hpost : ∀ x s0 sf, spec.post x s0 sf ∗ F x s0 ⊢ spec'.post x s0 sf)
    (hpan : ∀ x s0 sf, spec.onPanic x s0 sf ∗ F x s0 ⊢ spec'.onPanic x s0 sf)
    (hexit : ∀ x code s0 sf, spec.onExit x code s0 sf = ⌜False⌝)
    (hoom : ∀ x s0 sf, spec.onOom x s0 sf = ⌜False⌝ := by intros; rfl) :
    subroutine_ok prog entry spec' := by
  refine subroutine_ok_outcome_intro fun x R s0 hpc hrun hp hsp => ?_
  have hp' : s0.mem ⊨ spec.pre x s0 ∗ (F x s0 ∗ R) := by
    rw [← sepConj_assoc]
    exact Satisfies.mono (sepConj_mono_left (hpre x s0)) hp
  refine h.mono_outcome x (F x s0 ∗ R) s0 hpc hrun hp' hsp fun sf hout => ?_
  rcases hout with ⟨hret, hcc, hq⟩ | ⟨hpan_st, hq⟩ | ⟨code, _, hq⟩ | ⟨_, hq⟩
  · refine Or.inl ⟨hret, hcc, ?_⟩
    rw [← sepConj_assoc] at hq
    exact Satisfies.mono (sepConj_mono_left (hpost x s0 sf)) hq
  · refine Or.inr (Or.inl ⟨hpan_st, ?_⟩)
    rw [← sepConj_assoc] at hq
    exact Satisfies.mono (sepConj_mono_left (hpan x s0 sf)) hq
  · rw [hexit] at hq
    exact (not_satisfies_false_sepConj hq).elim
  · rw [hoom] at hq
    exact (not_satisfies_false_sepConj hq).elim

/-! ## 1. `do_reserve_and_handle [local#11]` (`kpkReserve_ok`) -/

private theorem adds_cs_eq_false {x2 x1 : BitVec 64}
    (h : x2.toNat + x1.toNat < 2 ^ 64) :
    (x2 + x1).ult x2 = false := by
  rw [BitVec.ult_eq_decide, decide_eq_false_iff_not, BitVec.toNat_add, Nat.mod_eq_of_lt h]
  omega

private theorem reserve_new_cap_stride_eq {stride cap x1 x2 : BitVec 64} {len additional : Nat}
    (hx1 : x1.toNat = len) (hx2 : x2.toNat = additional)
    (h : SpqrV1.Alloc.reserveCapStride stride.toNat cap.toNat len additional < 2 ^ 63) :
    (if (if (stride == 1#64) = true then 8#64 else 4#64).ult
          (if (cap <<< 1).ult (x2 + x1) = true then x2 + x1 else cap <<< 1) = true then
      if (cap <<< 1).ult (x2 + x1) = true then x2 + x1 else cap <<< 1
     else if (stride == 1#64) = true then 8#64 else 4#64) =
      BitVec.ofNat 64 (SpqrV1.Alloc.reserveCapStride stride.toNat cap.toNat len additional) := by
  have hmin_ge : 4 ≤ SpqrV1.Alloc.reserveMinCap stride.toNat := by
    unfold SpqrV1.Alloc.reserveMinCap; split <;> omega
  have hmax : max (max (len + additional) (2 * cap.toNat)) (SpqrV1.Alloc.reserveMinCap stride.toNat) < 2 ^ 63 := h
  have hadd : (x2 + x1).toNat = len + additional := by
    rw [BitVec.toNat_add, hx2, hx1, Nat.mod_eq_of_lt (by omega)]
    omega
  have hsh : (cap <<< 1).toNat = 2 * cap.toNat := by
    rw [BitVec.toNat_shiftLeft, Nat.shiftLeft_eq]
    change (cap.toNat * 2) % 2 ^ 64 = 2 * cap.toNat
    rw [Nat.mod_eq_of_lt (by omega)]
    omega
  have hm0 : (if (stride == 1#64) = true then 8#64 else 4#64).toNat =
      SpqrV1.Alloc.reserveMinCap stride.toNat := by
    by_cases hs : (stride == 1#64) = true
    · have hs' : stride = 1#64 := beq_iff_eq.mp hs
      subst hs'; rfl
    · have hs' : stride.toNat ≠ 1 := fun h1 => hs (beq_iff_eq.mpr (BitVec.eq_of_toNat_eq h1))
      simp only [hs, Bool.false_eq_true, ite_false, SpqrV1.Alloc.reserveMinCap, hs']
      rfl
  have hm1 : (if (cap <<< 1).ult (x2 + x1) = true then x2 + x1 else cap <<< 1).toNat =
      max (len + additional) (2 * cap.toNat) := by
    by_cases hc : (cap <<< 1).ult (x2 + x1) = true
    · simp only [hc, ite_true, hadd]
      rw [BitVec.ult_eq_decide, decide_eq_true_eq, hsh, hadd] at hc; omega
    · simp only [hc, Bool.false_eq_true, ite_false, hsh]
      rw [BitVec.ult_eq_decide, decide_eq_true_eq, hsh, hadd] at hc; omega
  apply BitVec.eq_of_toNat_eq
  dsimp only [SpqrV1.Alloc.reserveCapStride]
  rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  generalize (if (stride == 1#64) = true then 8#64 else 4#64) = m0 at hm0 ⊢
  generalize (if (cap <<< 1).ult (x2 + x1) = true then x2 + x1 else cap <<< 1) = m1 at hm1 ⊢
  by_cases hc2 : m0.ult m1 = true
  · simp only [hc2, ite_true, hm1]
    rw [BitVec.ult_eq_decide, decide_eq_true_eq, hm0, hm1] at hc2; omega
  · simp only [hc2, Bool.false_eq_true, ite_false, hm0]
    rw [BitVec.ult_eq_decide, decide_eq_true_eq, hm0, hm1] at hc2; omega

private def kpkDoReserveRawSpec (A : RustAlloc) : Spec SpqrV1.Alloc.DoReserveStrideCall where
  pre := fun x s =>
    let newCap := SpqrV1.Alloc.reserveCapStride x.stride.toNat x.cap.toNat x.len x.additional
    ⌜s.readReg64 .x0 = x.v ∧ (s.readReg64 .x1).toNat = x.len ∧
      (s.readReg64 .x2).toNat = x.additional ∧ s.readReg64 .x3 = x.align ∧
      s.readReg64 .x4 = x.stride ∧
      x.len ≤ x.cap.toNat ∧ x.bs.length ≤ x.cap.toNat * x.stride.toNat ∧
      x.ptr ≠ 0#64 ∧ 0 < x.stride.toNat ∧ LayoutOk (newCap * x.stride.toNat) x.align.toNat⌝ ∗
    (x.v ↦₆₄ x.cap) ∗ ((x.v + 8#64) ↦₆₄ x.ptr) ∗
    (if x.cap = 0#64 then emp
     else A.live x.ptr (x.cap.toNat * x.stride.toNat) x.align.toNat ∗ (x.ptr ↦ₛ x.bs) ∗
       memRegion (x.ptr + BitVec.ofNat 64 x.bs.length)
         (x.cap.toNat * x.stride.toNat - x.bs.length)) ∗
    A.pool ∗ stackAt s.sp doReserveStackX
  post := fun x s0 sf =>
    let newCap := SpqrV1.Alloc.reserveCapStride x.stride.toNat x.cap.toNat x.len x.additional
    ⌜sf.trace = s0.trace⌝ ∗
    (∃∗ p' : BitVec 64,
      ⌜p' ≠ 0#64 ∧ p'.toNat % x.align.toNat = 0⌝ ∗
      (x.v ↦₆₄ BitVec.ofNat 64 newCap) ∗ ((x.v + 8#64) ↦₆₄ p') ∗
      A.live p' (newCap * x.stride.toNat) x.align.toNat ∗ (p' ↦ₛ x.bs) ∗
      memRegion (p' + BitVec.ofNat 64 x.bs.length)
        (newCap * x.stride.toNat - x.bs.length)) ∗
    A.pool ∗ stackAt s0.sp doReserveStackX
  onPanic := fun _ s0 sf => ⌜allocFailedIn s0 sf ∧ s0.trace <+: sf.trace⌝ ∗ anyHeap

private theorem kpkReserve_raw_ok {img : Obj.Image} {A : RustAlloc}
    {ext : String → Option (State → State)} (hA : AllocContractsX img A ext) :
    subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr cliDoReserveName)
      ((kpkDoReserveRawSpec A).inImage img) := by
  unfold Spec.inImage
  simp only [kpkDoReserveRawSpec, GrowOne.Helpers.stackAt_cliGrowOne, sepExists_sepConj_right]
  have hfn : libsignalSessionCode.fnOff cliDoReserveName =
      num% (ls_off% "<alloc::raw_vec::RawVecInner<_>>::reserve::do_reserve_and_handle::<alloc::alloc::Global> [local#9]") :=
    cliDoReserve_fnOff
  have hpanic := panic_at_handle_error_norm_ext (b := img.base) (ext := ext)
    (name := cliDoReserveName)
    (k := num% (ls_rel%
      "<alloc::raw_vec::RawVecInner<_>>::reserve::do_reserve_and_handle::<alloc::alloc::Global> [local#9]"
      "alloc::raw_vec::handle_error"))
    (by rw [hfn, (ls_stub% "alloc::raw_vec::handle_error")])
  have hfg := FinishGrow.cliFinishGrow_ok_x hA
  have hfg0 := GrowOne.Helpers.finish_grow_zero_cells_ok_x hfg
  have hfg1 := GrowOne.Helpers.finish_grow_ne_cells_ok_x hfg
  rw [Program.fnAddr_rel (name := cliDoReserveName)
    hfn cliFinishGrow_fnOff
    (k := num% (ls_rel%
      "<alloc::raw_vec::RawVecInner<_>>::reserve::do_reserve_and_handle::<alloc::alloc::Global> [local#9]"
      "<alloc::raw_vec::RawVecInner>::finish_grow [local#10]"))
    (by decide)] at hfg0 hfg1
  code_fetches CryptoVerification.libsignalSessionCode cliKpkReserveBin img.base
    (Rust.withPanics ext) hfn
    (num% (ls_off% "<alloc::raw_vec::RawVecInner<_>>::reserve::do_reserve_and_handle::<alloc::alloc::Global> [local#9]")) 140
  dsimp only [tripleRatchetProgAtExt] at hpanic hfg0 hfg1 ⊢
  clear hfn hA hfg
  generalize_entry (libsignalSessionCode.rebase img.base
    (Rust.withPanics ext)).fnAddr cliDoReserveName = fnBase
  generalize_entry (libsignalSessionCode.rebase img.base
    (Rust.withPanics ext)) = prog
    reverting [Program.fetch, Program.externAt?, subroutine_ok]
  examples_hide_fetches
  wpp_init x s0
  obtain ⟨v, cap, ptr, bs, len, additional, align, stride⟩ := x
  dsimp only at *
  have hinv0 : ImgCallInv img s0 := ⟨by assumption, by assumption⟩
  have hx1_eq : (s0.readReg64 .x1).toNat = len := by assumption
  have hx2_eq : (s0.readReg64 .x2).toNat = additional := by assumption
  have hlen_le_cap : len ≤ cap.toNat := by assumption
  have hbs_le_cap : bs.length ≤ cap.toNat * stride.toNat := by assumption
  have hptr_ne : ptr ≠ 0#64 := by assumption
  have hstr_pos : 0 < stride.toNat := by assumption
  have hpow : ∃ k, align.toNat = 2 ^ k := h.2.1
  have hbound :
      SpqrV1.Alloc.reserveCapStride stride.toNat cap.toNat len additional * stride.toNat + align.toNat ≤ 2 ^ 63 :=
    h.2.2
  have halign_pos : 1 ≤ align.toNat := by
    rcases hpow with ⟨k, hk⟩; rw [hk]; exact Nat.one_le_two_pow
  have hnew_lt63 : SpqrV1.Alloc.reserveCapStride stride.toNat cap.toNat len additional < 2 ^ 63 := by
    have : SpqrV1.Alloc.reserveCapStride stride.toNat cap.toNat len additional * 1 ≤
        SpqrV1.Alloc.reserveCapStride stride.toNat cap.toNat len additional * stride.toNat :=
      Nat.mul_le_mul_left _ hstr_pos
    omega
  have hmax : max (max (len + additional) (2 * cap.toNat)) (SpqrV1.Alloc.reserveMinCap stride.toNat) < 2 ^ 63 :=
    hnew_lt63
  have hcs := adds_cs_eq_false (x2 := s0.readReg64 .x2) (x1 := s0.readReg64 .x1) (by
    rw [hx2_eq, hx1_eq]; omega)
  have hnew_eq := reserve_new_cap_stride_eq (stride := stride) (cap := cap) hx1_eq hx2_eq hnew_lt63
  let new := BitVec.ofNat 64 (SpqrV1.Alloc.reserveCapStride stride.toNat cap.toNat len additional)
  have hnew_toNat : new.toNat = SpqrV1.Alloc.reserveCapStride stride.toNat cap.toNat len additional := by
    dsimp [new]; rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  have hmin_ge : 4 ≤ SpqrV1.Alloc.reserveMinCap stride.toNat := by
    unfold SpqrV1.Alloc.reserveMinCap; split <;> omega
  have hcap_le_new : cap.toNat ≤ new.toNat := by
    rw [hnew_toNat]; dsimp [SpqrV1.Alloc.reserveCapStride]; omega
  have hnew_pos : 0 < new.toNat := by
    rw [hnew_toNat]; dsimp [SpqrV1.Alloc.reserveCapStride]; omega
  have hnew_mul_pos : 0 < new.toNat * stride.toNat := Nat.mul_pos hnew_pos hstr_pos
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
    have hmul_eq : SpqrV1.Alloc.reserveCapStride stride.toNat 0 len additional * stride.toNat =
        new.toNat * stride.toNat := by
      rw [hnew_toNat]; rfl
    simp only [ite_true, emp_sepConj, pointsToBytes_nil,
      List.length_nil, BitVec.add_zero, Nat.sub_zero, BitVec.toNat_ofNat, Nat.zero_mod, hmul_eq]
    apply SepWPp.of_sepWP (mid := fnBase + bv% (88))
    apply SepWP.seq_inImage
      (mid := fnBase + bv% (ls_rel%
        "<alloc::raw_vec::RawVecInner<_>>::reserve::do_reserve_and_handle::<alloc::alloc::Global> [local#9]"
        "<alloc::raw_vec::RawVecInner>::finish_grow [local#10]"))
      hinv0
    wp_steps
    apply SepWP.done (by rfl) (by wp_norm_lhs)
    rintro ⟨hF1, hsym1⟩
    wp_call hfg0 (s0.sp - 56#64, 0#64, ptr, new, align, stride, [], v_stk_1, v_stk_2, v_stk_3, s0.sp - 64#64)
    apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
    by_cases htag : w = 1#64
    · simp only [htag, ite_true, sepConj_assoc]
      refine SepWPp.pure_elim fun htrace => ?_
      apply SepWPp.of_sepWP
        (mid := fnBase + bv% (ls_rel%
          "<alloc::raw_vec::RawVecInner<_>>::reserve::do_reserve_and_handle::<alloc::alloc::Global> [local#9]"
          "alloc::raw_vec::handle_error"))
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
        SpqrV1.Alloc.reserveCapStride stride.toNat cap.toNat len additional * stride.toNat - bs.length =
          new.toNat * stride.toNat - bs.length := by rw [hnew_toNat]
    have hmul_eq :
        SpqrV1.Alloc.reserveCapStride stride.toNat cap.toNat len additional * stride.toNat =
          new.toNat * stride.toNat := by rw [hnew_toNat]
    rw [hsub_eq, hmul_eq]
    apply SepWPp.of_sepWP (mid := fnBase + bv% (88))
    apply SepWP.seq_inImage
      (mid := fnBase + bv% (ls_rel%
        "<alloc::raw_vec::RawVecInner<_>>::reserve::do_reserve_and_handle::<alloc::alloc::Global> [local#9]"
        "<alloc::raw_vec::RawVecInner>::finish_grow [local#10]"))
      hinv0
    wp_steps
    apply SepWP.done (by rfl) (by wp_norm_lhs)
    rintro ⟨hF1, hsym1⟩
    wp_call hfg1 (s0.sp - 56#64, cap, ptr, new, align, stride, bs, v_stk_1, v_stk_2, v_stk_3, s0.sp - 64#64)
    apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
    by_cases htag : w = 1#64
    · simp only [htag, ite_true, sepConj_assoc]
      refine SepWPp.pure_elim fun htrace => ?_
      apply SepWPp.of_sepWP
        (mid := fnBase + bv% (ls_rel%
          "<alloc::raw_vec::RawVecInner<_>>::reserve::do_reserve_and_handle::<alloc::alloc::Global> [local#9]"
          "alloc::raw_vec::handle_error"))
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

private theorem vecU8At_eq_flat (A : RustAlloc) (v cap ptr : BitVec 64) (bs : List (BitVec 8)) :
    vecU8At A v cap ptr bs =
      ⌜bs.length ≤ cap.toNat ∧ cap.toNat < 2 ^ 63 ∧ ptr ≠ 0#64⌝ ∗
      (v ↦₆₄ cap) ∗ ((v + 8#64) ↦₆₄ ptr) ∗ ((v + 16#64) ↦₆₄ BitVec.ofNat 64 bs.length) ∗
      (if cap = 0#64 then emp
       else A.live ptr cap.toNat 1 ∗ (ptr ↦ₛ bs) ∗
         memRegion (ptr + BitVec.ofNat 64 bs.length) (cap.toNat - bs.length)) := by
  simp only [vecU8At, vecHeader, BitVec.ofNat_eq_ofNat]
  ac_rfl

/-- `cliDoReserveName` meets `(SpqrV1.Varint.doReserveSpecOf resStack A).inImage img`
directly from `hA : AllocContractsX img A ext` and `doReserveStackX ≤ resStack`. -/
theorem kpkReserve_ok {img : Obj.Image} {A : RustAlloc}
    {ext : String → Option (State → State)} {resStack : Nat}
    (hA : AllocContractsX img A ext)
    (hstk : doReserveStackX ≤ resStack) :
    subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr cliDoReserveName)
      ((SpqrV1.Varint.doReserveSpecOf resStack A).inImage img) := by
  have hraw := kpkReserve_raw_ok hA
  refine subroutine_ok_outcome_intro fun x R s0 hpc hrun hpre hsp => ?_
  simp only [Spec.inImage, SpqrV1.Varint.doReserveSpecOf, vecU8At_eq_flat,
    sepConj_assoc, satisfies_pure_sepConj] at hpre
  rcases hpre with ⟨hinv, ⟨hx0, hx1, hx2, hx3, hx4, hbound⟩, ⟨hlen, hcap63, hptr⟩, hmem⟩
  have hhi : resStack ≤ 2 ^ 64 := by
    have hm := hmem
    have hrepack :
        (x.v ↦₆₄ x.cap) ∗ ((x.v + 8#64) ↦₆₄ x.ptr) ∗
          ((x.v + 16#64) ↦₆₄ BitVec.ofNat 64 x.bs.length) ∗
          (if x.cap = 0#64 then emp
           else A.live x.ptr x.cap.toNat 1 ∗ (x.ptr ↦ₛ x.bs) ∗
             memRegion (x.ptr + BitVec.ofNat 64 x.bs.length) (x.cap.toNat - x.bs.length)) ∗
          A.pool ∗ stackAt s0.sp resStack ∗ R =
        stackAt s0.sp resStack ∗
          ((x.v ↦₆₄ x.cap) ∗ (((x.v + 8#64) ↦₆₄ x.ptr) ∗
            ((x.v + 16#64) ↦₆₄ BitVec.ofNat 64 x.bs.length) ∗
            (if x.cap = 0#64 then emp
             else A.live x.ptr x.cap.toNat 1 ∗ (x.ptr ↦ₛ x.bs) ∗
               memRegion (x.ptr + BitVec.ofNat 64 x.bs.length) (x.cap.toNat - x.bs.length)) ∗
            A.pool ∗ R)) := by
      ac_rfl
    rw [hrepack, stackAt] at hm
    exact GrowOne.Helpers.memRegion_bound_of_pointsTo64 hm
  have hlo : 64 + finishGrowStackX ≤ resStack := by
    have : 64 + finishGrowStackX = doReserveStackX := by decide
    omega
  have hsplit : stackAt s0.sp resStack =
      memRegion (s0.sp - BitVec.ofNat 64 resStack) (resStack - doReserveStackX) ∗
        stackAt s0.sp doReserveStackX :=
    GrowOne.Helpers.stackAt_split_stk s0.sp hlo hhi
  have hrepack_pre :
      (x.v ↦₆₄ x.cap) ∗ ((x.v + 8#64) ↦₆₄ x.ptr) ∗
        ((x.v + 16#64) ↦₆₄ BitVec.ofNat 64 x.bs.length) ∗
        (if x.cap = 0#64 then emp
         else A.live x.ptr x.cap.toNat 1 ∗ (x.ptr ↦ₛ x.bs) ∗
           memRegion (x.ptr + BitVec.ofNat 64 x.bs.length) (x.cap.toNat - x.bs.length)) ∗
        A.pool ∗
        (memRegion (s0.sp - BitVec.ofNat 64 resStack) (resStack - doReserveStackX) ∗
          stackAt s0.sp doReserveStackX) ∗ R =
      (x.v ↦₆₄ x.cap) ∗ ((x.v + 8#64) ↦₆₄ x.ptr) ∗
        (if x.cap = 0#64 then emp
         else A.live x.ptr x.cap.toNat 1 ∗ (x.ptr ↦ₛ x.bs) ∗
           memRegion (x.ptr + BitVec.ofNat 64 x.bs.length) (x.cap.toNat - x.bs.length)) ∗
        A.pool ∗ stackAt s0.sp doReserveStackX ∗
        (((x.v + 16#64) ↦₆₄ BitVec.ofNat 64 x.bs.length) ∗
          memRegion (s0.sp - BitVec.ofNat 64 resStack) (resStack - doReserveStackX) ∗ R) := by
    ac_rfl
  rw [hsplit, hrepack_pre] at hmem
  let xs : SpqrV1.Alloc.DoReserveStrideCall :=
    ⟨x.v, x.cap, x.ptr, x.bs, x.bs.length, x.additional, 1#64, 1#64⟩
  have hlay : LayoutOk (reserveCap x.cap.toNat x.bs.length x.additional) 1 :=
    ⟨by dsimp [reserveCap]; omega, ⟨0, rfl⟩, by omega⟩
  let F : SepProp :=
    ((x.v + 16#64) ↦₆₄ BitVec.ofNat 64 x.bs.length) ∗
      memRegion (s0.sp - BitVec.ofNat 64 resStack) (resStack - doReserveStackX) ∗ R
  have hpre' : s0.mem ⊨ ((kpkDoReserveRawSpec A).inImage img).pre xs s0 ∗ F := by
    simp only [Spec.inImage, kpkDoReserveRawSpec, xs, BitVec.toNat_ofNat, Nat.one_mod,
      SpqrV1.Alloc.reserveCapStride_one, Nat.mul_one, sepConj_assoc, satisfies_pure_sepConj]
    exact ⟨hinv, ⟨hx0, hx1, hx2, hx3, hx4, hlen, hlen, hptr, by decide, hlay⟩, hmem⟩
  refine hraw.mono_outcome xs F s0 hpc hrun hpre' hsp fun sf hout => ?_
  rcases hout with ⟨hret, hcc, hq⟩ | ⟨hpan, hq⟩ | ⟨_, _, hq⟩ | ⟨_, hq⟩
  · refine Or.inl ⟨hret, hcc, ?_⟩
    simp only [Spec.inImage, kpkDoReserveRawSpec, SpqrV1.Varint.doReserveSpecOf, vecU8At_eq_flat,
      xs, BitVec.toNat_ofNat, Nat.one_mod, SpqrV1.Alloc.reserveCapStride_one, Nat.mul_one,
      Nat.mod_one, and_true] at hq ⊢
    rw [sepConj_assoc, satisfies_pure_sepConj] at hq
    rcases hq with ⟨htrace, hq⟩
    simp only [sepExists_sepConj_left, satisfies_sepExists] at hq
    rcases hq with ⟨p', hq⟩
    rw [sepConj_assoc, sepConj_assoc, satisfies_pure_sepConj] at hq
    rcases hq with ⟨hp', hpost_mem⟩
    have hlt : reserveCap x.cap.toNat x.bs.length x.additional < 2 ^ 64 := by
      dsimp [reserveCap] at hbound ⊢; omega
    have hlen_le : x.bs.length ≤ reserveCap x.cap.toNat x.bs.length x.additional := by
      dsimp [reserveCap]; omega
    have hcap63' : reserveCap x.cap.toNat x.bs.length x.additional < 2 ^ 63 := by omega
    have hcap_ne : BitVec.ofNat 64 (reserveCap x.cap.toNat x.bs.length x.additional) ≠ 0#64 := by
      intro heq
      have ht := congrArg BitVec.toNat heq
      rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hlt] at ht
      change reserveCap x.cap.toNat x.bs.length x.additional = 0 at ht
      dsimp [reserveCap] at ht; omega
    rw [sepConj_assoc, satisfies_pure_sepConj]
    refine ⟨htrace, ?_⟩
    simp only [sepExists_sepConj_left, satisfies_sepExists]
    refine ⟨p', ?_⟩
    simp only [hcap_ne, ite_false, Nat.mod_eq_of_lt hlt, hsplit]
    rw [sepConj_assoc, sepConj_assoc, satisfies_pure_sepConj]
    refine ⟨⟨hlen_le, hcap63', hp'⟩, ?_⟩
    dsimp only [F] at hpost_mem
    exact Satisfies.mono (Entails.of_eq (by ac_rfl)) hpost_mem
  · refine Or.inr (Or.inl ⟨hpan, ?_⟩)
    dsimp only [Spec.inImage, kpkDoReserveRawSpec, SpqrV1.Varint.doReserveSpecOf,
      doReserveSpec, F] at hq ⊢
    rw [sepConj_assoc, satisfies_pure_sepConj] at hq ⊢
    refine ⟨hq.1, ?_⟩
    have hrepack_any :
        anyHeap ∗ (((x.v + 16#64) ↦₆₄ BitVec.ofNat 64 x.bs.length) ∗
          memRegion (s0.sp - BitVec.ofNat 64 resStack) (resStack - doReserveStackX) ∗ R) =
        (anyHeap ∗ ((x.v + 16#64) ↦₆₄ BitVec.ofNat 64 x.bs.length) ∗
          memRegion (s0.sp - BitVec.ofNat 64 resStack) (resStack - doReserveStackX)) ∗ R := by
      ac_rfl
    rw [hrepack_any] at hq
    exact Satisfies.mono (sepConj_mono_left (entails_anyHeap _)) hq.2
  · exact (allowPanic_not_exited hq).elim
  · exact (allowPanic_not_exited hq).elim

/-! ## 2. `concat [local#3]` on Two Non-Empty Owned Slices (`kpkConcat2_pos_ok`) -/

structure Concat2PosCall where
  outVec : BitVec 64
  slicesA : BitVec 64
  p0 : BitVec 64
  bs0 : List (BitVec 8)
  p1 : BitVec 64
  bs1 : List (BitVec 8)

def kpkConcat2PosSpec (A : RustAlloc) (stk : Nat) : Spec Concat2PosCall where
  pre := fun x s =>
    ⌜s.readReg64 .x0 = x.outVec ∧ s.readReg64 .x1 = x.slicesA ∧ s.readReg64 .x2 = 2#64 ∧
      0 < x.bs0.length ∧ 0 < x.bs1.length ∧ x.bs0.length + x.bs1.length < 2 ^ 63⌝ ∗
      memRegion x.outVec 24 ∗
      (x.slicesA ↦₆₄ x.p0) ∗ ((x.slicesA + 8#64) ↦₆₄ BitVec.ofNat 64 x.bs0.length) ∗
      ((x.slicesA + 16#64) ↦₆₄ x.p1) ∗ ((x.slicesA + 24#64) ↦₆₄ BitVec.ofNat 64 x.bs1.length) ∗
      (x.p0 ↦ₛ x.bs0) ∗ (x.p1 ↦ₛ x.bs1) ∗
      A.pool ∗ stackAt s.sp stk
  post := fun x s0 sf =>
    ⌜sf.trace = s0.trace⌝ ∗
      vecU8 A x.outVec (x.bs0 ++ x.bs1) ∗
      (x.slicesA ↦₆₄ x.p0) ∗ ((x.slicesA + 8#64) ↦₆₄ BitVec.ofNat 64 x.bs0.length) ∗
      ((x.slicesA + 16#64) ↦₆₄ x.p1) ∗ ((x.slicesA + 24#64) ↦₆₄ BitVec.ofNat 64 x.bs1.length) ∗
      (x.p0 ↦ₛ x.bs0) ∗ (x.p1 ↦ₛ x.bs1) ∗
      A.pool ∗ stackAt s0.sp stk
  onPanic := fun _ s0 sf => ⌜allocFailedIn s0 sf ∧ s0.trace <+: sf.trace⌝ ∗ anyHeap

private theorem memRegion_24_cells (a : BitVec 64) :
    memRegion a 24 =
      (∃∗ v0 : BitVec 64, ∃∗ v1 : BitVec 64, ∃∗ v2 : BitVec 64,
        (a ↦₆₄ v2) ∗ ((a + 8#64) ↦₆₄ v1) ∗ ((a + 16#64) ↦₆₄ v0)) := by
  rw [show (24 : Nat) = 8 + (8 + 8) by rfl, ProofLib.memRegion_split a 8 (8 + 8) (by decide),
    ProofLib.memRegion_split (a + 8#64) 8 8 (by decide), ProofLib.memRegion_eight,
    ProofLib.memRegion_eight, ProofLib.memRegion_eight]
  simp only [sepExists_sepConj_left, sepExists_sepConj_right, BitVec.add_assoc, BitVec.reduceAdd]

private theorem stackAt_cliConcat (sp : BitVec 64) :
    stackAt sp cliConcatStack =
      stackAt (sp - 96#64) extHookStack ∗
      (∃∗ v0 : BitVec 64, ∃∗ v1 : BitVec 64, ∃∗ v2 : BitVec 64, ∃∗ v3 : BitVec 64,
       ∃∗ v4 : BitVec 64, ∃∗ v5 : BitVec 64, ∃∗ v6 : BitVec 64, ∃∗ v7 : BitVec 64,
       ∃∗ v8 : BitVec 64, ∃∗ v9 : BitVec 64, ∃∗ v10 : BitVec 64, ∃∗ v11 : BitVec 64,
        ((sp - 96#64) ↦₆₄ v0) ∗ ((sp - 88#64) ↦₆₄ v1) ∗
        ((sp - 80#64) ↦₆₄ v2) ∗ ((sp - 72#64) ↦₆₄ v3) ∗
        ((sp - 64#64) ↦₆₄ v4) ∗ ((sp - 56#64) ↦₆₄ v5) ∗
        ((sp - 48#64) ↦₆₄ v6) ∗ ((sp - 40#64) ↦₆₄ v7) ∗
        ((sp - 32#64) ↦₆₄ v8) ∗ ((sp - 24#64) ↦₆₄ v9) ∗
        ((sp - 16#64) ↦₆₄ v10) ∗ ((sp - 8#64) ↦₆₄ v11)) := by
  have h1 := ProofLib.stackAt_split_cells sp 16384 12 (by decide)
  have hsum : 16384 + 8 * 12 = cliConcatStack := by decide
  rw [hsum] at h1
  change stackAt sp cliConcatStack =
    stackAt (sp - 96#64) extHookStack ∗ cells (sp - 96#64) 12 at h1
  have hc12 : cells (sp - 96#64) 12 =
      (∃∗ v0 : BitVec 64, ∃∗ v1 : BitVec 64, ∃∗ v2 : BitVec 64, ∃∗ v3 : BitVec 64,
       ∃∗ v4 : BitVec 64, ∃∗ v5 : BitVec 64, ∃∗ v6 : BitVec 64, ∃∗ v7 : BitVec 64,
       ∃∗ v8 : BitVec 64, ∃∗ v9 : BitVec 64, ∃∗ v10 : BitVec 64, ∃∗ v11 : BitVec 64,
        ((sp - 96#64) ↦₆₄ v0) ∗ ((sp - 88#64) ↦₆₄ v1) ∗
        ((sp - 80#64) ↦₆₄ v2) ∗ ((sp - 72#64) ↦₆₄ v3) ∗
        ((sp - 64#64) ↦₆₄ v4) ∗ ((sp - 56#64) ↦₆₄ v5) ∗
        ((sp - 48#64) ↦₆₄ v6) ∗ ((sp - 40#64) ↦₆₄ v7) ∗
        ((sp - 32#64) ↦₆₄ v8) ∗ ((sp - 24#64) ↦₆₄ v9) ∗
        ((sp - 16#64) ↦₆₄ v10) ∗ ((sp - 8#64) ↦₆₄ v11)) := by
    cells_unfold
  rw [h1, hc12]

private theorem ofNat_getLsbD_63_false {n : Nat} (h : n < 2 ^ 63) :
    (BitVec.ofNat 64 n).getLsbD 63 = false := by
  rw [BitVec.getLsbD_eq_getElem (by decide), BitVec.getElem_eq_testBit_toNat,
    BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  exact Nat.testBit_lt_two_pow h

private theorem ofNat_getElem_63_false {n : Nat} (h : n < 2 ^ 63) :
    (BitVec.ofNat 64 n)[63] = false :=
  ofNat_getLsbD_63_false h

private theorem ofNat_beq_zero_false {n : Nat} (h0 : 0 < n) (hlt : n < 2 ^ 64) :
    (BitVec.ofNat 64 n == 0#64) = false := by
  apply beq_false_of_ne
  intro h
  have ht := congrArg BitVec.toNat h
  rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hlt] at ht
  change n = 0 at ht
  omega

private theorem ofNat_ult_of_le {a b : Nat} (hle : a ≤ b) (hb : b < 2 ^ 64) :
    (BitVec.ofNat 64 b).ult (BitVec.ofNat 64 a) = false := by
  have ha : a < 2 ^ 64 := by omega
  simp only [BitVec.ult, BitVec.toNat_ofNat, Nat.mod_eq_of_lt ha, Nat.mod_eq_of_lt hb,
    decide_eq_false_iff_not]
  omega

private theorem pull_alloc_pure (P1 P2 R : SepProp) (φ : Prop) :
    P1 ∗ P2 ∗ ⌜φ⌝ ∗ R = ⌜φ⌝ ∗ (P1 ∗ P2 ∗ R) := by ac_rfl

private theorem vecU8_of_append_pos (A : RustAlloc) (v p' : BitVec 64)
    (bs0 bs1 : List (BitVec 8))
    (hpos : 0 < bs0.length + bs1.length) (hlt : bs0.length + bs1.length < 2 ^ 63)
    (hp' : p' ≠ 0#64) :
    (v ↦₆₄ BitVec.ofNat 64 (bs0.length + bs1.length)) ∗ ((v + 8#64) ↦₆₄ p') ∗
      ((v + 16#64) ↦₆₄ BitVec.ofNat 64 (bs0.length + bs1.length)) ∗
      A.live p' (bs0.length + bs1.length) 1 ∗ (p' ↦ₛ (bs0 ++ bs1)) ⊢
      vecU8 A v (bs0 ++ bs1) := by
  have hlen : (bs0 ++ bs1).length = bs0.length + bs1.length := List.length_append
  rw [← hlen]
  have hne0 : BitVec.ofNat 64 (bs0 ++ bs1).length ≠ 0 := by
    intro h
    have ht := congrArg BitVec.toNat h
    rw [BitVec.toNat_ofNat, hlen, Nat.mod_eq_of_lt (by omega)] at ht
    change bs0.length + bs1.length = 0 at ht; omega
  have htoNat : (BitVec.ofNat 64 (bs0 ++ bs1).length).toNat = (bs0 ++ bs1).length := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by rw [hlen]; omega)]
  have hlt' : (bs0 ++ bs1).length < 2 ^ 63 := by rw [hlen]; exact hlt
  unfold vecU8 vecU8At vecHeader
  refine Entails.trans ?_ (Entails.sepExists_intro (BitVec.ofNat 64 (bs0 ++ bs1).length))
  refine Entails.trans ?_ (Entails.sepExists_intro p')
  simp only [hne0, htoNat, Nat.le_refl, hlt', ↓reduceIte,
    Nat.sub_self, memRegion_zero, sepConj_emp, sepConj_assoc]
  rw [show (v ↦₆₄ BitVec.ofNat 64 (bs0 ++ bs1).length) ∗ ((v + 8#64) ↦₆₄ p') ∗
        ((v + 16#64) ↦₆₄ BitVec.ofNat 64 (bs0 ++ bs1).length) ∗ ⌜True ∧ True ∧ p' ≠ 0⌝ ∗
        A.live p' (bs0 ++ bs1).length 1 ∗ (p' ↦ₛ (bs0 ++ bs1)) =
      ⌜True ∧ True ∧ p' ≠ 0⌝ ∗ ((v ↦₆₄ BitVec.ofNat 64 (bs0 ++ bs1).length) ∗ ((v + 8#64) ↦₆₄ p') ∗
        ((v + 16#64) ↦₆₄ BitVec.ofNat 64 (bs0 ++ bs1).length) ∗
        A.live p' (bs0 ++ bs1).length 1 ∗ (p' ↦ₛ (bs0 ++ bs1))) by ac_rfl]
  exact Entails.pure_right ⟨trivial, trivial, hp'⟩ (Entails.refl _)

set_option maxHeartbeats 1600000 in
private theorem kpkConcat2_pos_exact_ok {A : RustAlloc} {img : Obj.Image}
    {ext : String → Option (State → State)} (hA : AllocContractsX img A ext) :
    subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr cliConcatName)
      ((kpkConcat2PosSpec A cliConcatStack).inImage img) := by
  unfold Spec.inImage kpkConcat2PosSpec
  simp only [memRegion_24_cells, stackAt_cliConcat, sepExists_sepConj_left, sepExists_sepConj_right]
  have hfn : libsignalSessionCode.fnOff cliConcatName =
      ls_off% "<[&[u8]] as alloc::slice::Concat<u8>>::concat [local#3]" :=
    cliConcat_fnOff
  have hshim := shim_ok_at2_ext_x hA (name := cliConcatName)
    (k := ls_rel% "<[&[u8]] as alloc::slice::Concat<u8>>::concat [local#3]"
      "__rustc::__rust_no_alloc_shim_is_unstable_v2")
    (by rw [hfn, (ls_stub% "__rustc::__rust_no_alloc_shim_is_unstable_v2")])
  have halloc := alloc_ok_at_norm_ext_x hA (name := cliConcatName)
    (k := ls_rel% "<[&[u8]] as alloc::slice::Concat<u8>>::concat [local#3]"
      "__rustc::__rust_alloc")
    (by rw [hfn, (ls_stub% "__rustc::__rust_alloc")])
  have hmc := memcpy_ok_at2_ext_x hA (name := cliConcatName)
    (k := ls_rel% "<[&[u8]] as alloc::slice::Concat<u8>>::concat [local#3]" "memcpy")
    (by rw [hfn, (ls_stub% "memcpy")])
  have hpanic := panic_at_handle_error_norm_ext (b := img.base) (ext := ext)
    (name := cliConcatName)
    (k := ls_rel% "<[&[u8]] as alloc::slice::Concat<u8>>::concat [local#3]"
      "alloc::raw_vec::handle_error")
    (by rw [hfn, (ls_stub% "alloc::raw_vec::handle_error")])
  code_fetches_range CryptoVerification.libsignalSessionCode cliKpkConcatBin img.base
    (Rust.withPanics ext) hfn
    (num% (ls_off% "<[&[u8]] as alloc::slice::Concat<u8>>::concat [local#3]")) 0 364
  dsimp only [tripleRatchetProgAtExt] at hshim halloc hmc hpanic ⊢
  clear hfn hA
  generalize_entry (libsignalSessionCode.rebase img.base
    (Rust.withPanics ext)).fnAddr cliConcatName = entry
  generalize_entry (libsignalSessionCode.rebase img.base
    (Rust.withPanics ext)) = prog
    reverting [Program.fetch, Program.externAt?, subroutine_ok]
  examples_hide_fetches
  wpp_init x s0
  obtain ⟨outVec, slicesA, p0, bs0, p1, bs1⟩ := x
  dsimp only at *
  have hinv0 : ImgCallInv img s0 := ⟨‹_›, ‹_›⟩
  have hpos0 : 0 < bs0.length := ‹_›
  have hpos1 : 0 < bs1.length := ‹_›
  have hmax : bs0.length + bs1.length < 2 ^ 63 := ‹_›
  have hpow1 : ∃ k, 1 = 2 ^ k := ⟨0, rfl⟩
  have h0_lt64 : bs0.length < 2 ^ 64 := by omega
  have h1_lt64 : bs1.length < 2 ^ 64 := by omega
  have h0_le64 : bs0.length ≤ 2 ^ 64 := by omega
  have h1_le64 : bs1.length ≤ 2 ^ 64 := by omega
  have hadd_bv : BitVec.ofNat 64 bs1.length + BitVec.ofNat 64 bs0.length =
      BitVec.ofNat 64 (bs0.length + bs1.length) := by
    rw [← BitVec.ofNat_add, Nat.add_comm]
  have hadd01_bv : BitVec.ofNat 64 bs0.length + BitVec.ofNat 64 bs1.length =
      BitVec.ofNat 64 (bs0.length + bs1.length) := by
    rw [← BitVec.ofNat_add]
  have hsub_bv : BitVec.ofNat 64 (bs0.length + bs1.length) - BitVec.ofNat 64 bs0.length =
      BitVec.ofNat 64 bs1.length := by
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_sub_of_le]
    · rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega),
          BitVec.toNat_ofNat, Nat.mod_eq_of_lt h0_lt64,
          BitVec.toNat_ofNat, Nat.mod_eq_of_lt h1_lt64]
      omega
    · simp only [BitVec.le_def, BitVec.toNat_ofNat]; omega
  have hcs1 : (BitVec.ofNat 64 (bs0.length + bs1.length)).ult (BitVec.ofNat 64 bs1.length) = false :=
    ofNat_ult_of_le (by omega) (by omega)
  have hbit63 : (BitVec.ofNat 64 (bs0.length + bs1.length)).getLsbD 63 = false :=
    ofNat_getLsbD_63_false (by omega)
  have helem63 : (BitVec.ofNat 64 (bs0.length + bs1.length))[63] = false :=
    ofNat_getElem_63_false (by omega)
  have htot_toNat : (BitVec.ofNat 64 (bs0.length + bs1.length)).toNat = bs0.length + bs1.length := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  have h0_toNat : (BitVec.ofNat 64 bs0.length).toNat = bs0.length := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt h0_lt64]
  have h1_toNat : (BitVec.ofNat 64 bs1.length).toNat = bs1.length := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt h1_lt64]
  have hhi0 : (BitVec.ofNat 64 (bs0.length + bs1.length)).ult (BitVec.ofNat 64 bs0.length) = false :=
    ofNat_ult_of_le (by omega) (by omega)
  have hhi1 : (BitVec.ofNat 64 bs1.length).ult (BitVec.ofNat 64 bs1.length) = false :=
    ProofLib.bitvec_ult_self _
  have htot_ne0 : (BitVec.ofNat 64 (bs0.length + bs1.length) == 0#64) = false :=
    ofNat_beq_zero_false (by omega) (by omega)
  have h0_ne0 : (BitVec.ofNat 64 bs0.length == 0#64) = false :=
    ofNat_beq_zero_false hpos0 h0_lt64
  have h1_ne0 : (BitVec.ofNat 64 bs1.length == 0#64) = false :=
    ofNat_beq_zero_false hpos1 h1_lt64
  have hlay : LayoutOk (bs0.length + bs1.length) 1 := ⟨by omega, hpow1, by omega⟩
  apply SepWPp.of_sepWP_inImage (mid := entry + bv% (108)) hinv0
  apply SepWP.seq_inImage
    (mid := entry + bv% (ls_rel% "<[&[u8]] as alloc::slice::Concat<u8>>::concat [local#3]"
      "__rustc::__rust_no_alloc_shim_is_unstable_v2")) hinv0
  wp_steps
  apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
  intro hinv1
  have ⟨hF1, hsym1⟩ := hinv1
  apply SepWP.seq_inImage
    (mid := entry + bv% (ls_rel% "<[&[u8]] as alloc::slice::Concat<u8>>::concat [local#3]"
      "__rustc::__rust_alloc")) hinv1
  wp_apply
  wp_steps
  apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
  rintro ⟨hF2, hsym2⟩
  wp_apply
  apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
  intro hinv_sf1
  by_cases hoom : sf_1.readReg64 Reg.x0 = 0#64
  · simp only [hoom, BitVec.ofNat_eq_ofNat, ite_true, sepConj_assoc]
    rw [pull_alloc_pure]
    refine SepWPp.pure_elim fun htrace => ?_
    apply SepWPp.of_sepWP
      (mid := entry + bv% (ls_rel% "<[&[u8]] as alloc::slice::Concat<u8>>::concat [local#3]"
        "alloc::raw_vec::handle_error"))
    wp_steps
    apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
    refine SepWPp.panic (by simp only [wp_norm, arm64_norm, *]) (by wp_norm_lhs) fun hm => ?_
    simpa only [sepConj_assoc] using
      allowPanic_panicked (allocFailedIn_of_eq (by simp only [Rust.panicked, wp_norm, arm64_norm, *])) hm
  · simp only [hoom, BitVec.ofNat_eq_ofNat, ite_false, sepConj_assoc]
    have hoom_beq : (sf_1.readReg64 Reg.x0 == 0#64) = false := beq_false_of_ne hoom
    rw [pull_alloc_pure]
    refine SepWPp.pure_elim fun ⟨_, htr1⟩ => ?_
    have htr_sf1 : sf_1.trace = s0.trace := by
      rw [htr1]; simp only [wp_norm, arm64_norm, *]
    rw [ProofLib.memRegion_split (sf_1.readReg64 Reg.x0) bs0.length bs1.length (by omega)]
    apply SepWPp.of_sepWP_ret
    apply SepWP.seq_inImage
      (mid := entry + bv% (ls_rel% "<[&[u8]] as alloc::slice::Concat<u8>>::concat [local#3]"
        "memcpy")) hinv_sf1
    wp_steps
    apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
    intro hinv3
    have ⟨hF3, hsym3⟩ := hinv3
    apply SepWP.seq_inImage (mid := entry + bv% (172)) hinv3
    wp_apply using hmc
    apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
    intro hinv3'
    apply SepWP.seq_inImage
      (mid := entry + bv% (ls_rel% "<[&[u8]] as alloc::slice::Concat<u8>>::concat [local#3]"
        "memcpy")) hinv3'
    wp_steps
    apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
    rintro ⟨hF4, hsym4⟩
    wp_apply using hmc
    wp_steps
    apply SepWP.fold (Entails.of_eq (pointsToBytes_append (sf_1.readReg64 Reg.x0) bs0 bs1).symm) (by sep_focus)
    apply SepWP.fold (vecU8_of_append_pos A outVec (sf_1.readReg64 Reg.x0) bs0 bs1
      (by omega) hmax hoom) (by sep_focus)
    wp_done

/-- `cliConcatName` meets `(kpkConcat2PosSpec A stk).inImage img` for any `96 + extHookStack ≤ stk ≤ 2 ^ 64`. -/
theorem kpkConcat2_pos_ok {A : RustAlloc} {img : Obj.Image}
    {ext : String → Option (State → State)} (hA : AllocContractsX img A ext)
    (stk : Nat) (hstk : 96 + extHookStack ≤ stk) (hstk64 : stk ≤ 2 ^ 64) :
    subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr cliConcatName)
      ((kpkConcat2PosSpec A stk).inImage img) := by
  refine subroutine_ok_frame_weaken
    (fun _ s0 => memRegion (s0.sp - BitVec.ofNat 64 stk) (stk - cliConcatStack))
    (kpkConcat2_pos_exact_ok hA) ?_ ?_ ?_ (fun _ _ _ _ => rfl)
  · intro x s0
    dsimp only [Spec.inImage, kpkConcat2PosSpec]
    rw [stackAt_split_ge s0.sp hstk hstk64]
    exact Entails.of_eq (by ac_rfl)
  · intro x s0 sf
    dsimp only [Spec.inImage, kpkConcat2PosSpec]
    rw [stackAt_split_ge s0.sp hstk hstk64]
    exact Entails.of_eq (by ac_rfl)
  · intro _ s0 sf
    dsimp only [Spec.inImage, kpkConcat2PosSpec]
    rw [sepConj_assoc]
    exact sepConj_mono_right (entails_anyHeap _)

end CryptoVerification.SignalSession.Cli.Store.KpkMarkPoll.Helpers
