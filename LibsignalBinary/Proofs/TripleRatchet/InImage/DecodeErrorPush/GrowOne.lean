/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.TripleRatchet.InImage.DecodeErrorPush.Core
public import LibsignalBinary.Proofs.CodeLayout
import GeneratedLean.LibsignalSessionCode -- shake: keep
import LibsignalBinary.Proofs.TripleRatchet.GeneralizeEntry
import ProofLib.SepLogic.WP.Apply
import ProofLib.SepLogic.WPp

/-!
# `grow_amortized` and `grow_one` for `<DecodeError>::push`

Verifies `RawVecInner::grow_amortized` and `RawVec::grow_one` for growing the
`DecodeError` context vector.
-/

@[expose] public section

namespace CryptoVerification.LibsignalTripleRatchet.InImage.DecodeErrorPush

open Arm64 ProofLib CryptoGames CryptoGames.HMAC CryptoGames.LibsignalSession
open CryptoVerification.RustHeap CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchet CryptoVerification.CodeLayout
open BS31

set_option maxRecDepth 200000
set_option maxHeartbeats 400000

attribute [local irreducible] Program.fetch Program.externAt? Program.fnOff
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero

/-! ## `grow_amortized` specification and verification -/

def newCap (cap : BitVec 64) : BitVec 64 :=
  BitVec.ofNat 64 (max (2 * cap.toNat) 4)

theorem newCap_toNat {cap : BitVec 64} (h : cap.toNat < 2 ^ 32) :
    (newCap cap).toNat = max (2 * cap.toNat) 4 := by
  unfold newCap
  rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]

abbrev GrowAmortizedGhost :=
  BitVec 64 × BitVec 64 × BitVec 64 × BitVec 64

def growAmortizedSpec (A : RustAlloc) : Spec GrowAmortizedGhost where
  pre := fun (v, cap, ptr, gsp) s =>
    ⌜s.readReg64 .x0 = v ∧ s.readReg64 .x1 = cap ∧ s.sp = gsp ∧
      cap.toNat < 2 ^ 32 ∧ ptr ≠ 0#64⌝ ∗
    (v ↦₆₄ cap) ∗ ((v + 8#64) ↦₆₄ ptr) ∗
    (if cap = 0#64 then emp
     else A.live ptr (cap.toNat * 32) 8 ∗ memRegion ptr (cap.toNat * 32)) ∗
    A.pool ∗ cells (gsp - 64#64) 8 ∗ cells (gsp - 96#64) 4 ∗
    stackAt (gsp - 96#64) allocHookStack
  post := fun (v, cap, ptr, gsp) s0 sf =>
    ∃∗ res : BitVec 64, ∃∗ p' : BitVec 64,
      (if res = 0xffffffffffffffff#64 then
        ⌜sf.readReg64 .x0 = 0xffffffffffffffff#64 ∧ p' ≠ 0#64 ∧ sf.trace = s0.trace⌝ ∗
        (v ↦₆₄ newCap cap) ∗ ((v + 8#64) ↦₆₄ p') ∗
        A.live p' ((newCap cap).toNat * 32) 8 ∗ memRegion p' ((newCap cap).toNat * 32)
       else
        ⌜res = 8#64 ∧ sf.readReg64 .x0 = 8#64 ∧ sf.trace = s0.trace ++ [allocFailedEvent]⌝ ∗
        (v ↦₆₄ cap) ∗ ((v + 8#64) ↦₆₄ ptr) ∗
        (if cap = 0#64 then emp
         else A.live ptr (cap.toNat * 32) 8 ∗ memRegion ptr (cap.toNat * 32))) ∗
      A.pool ∗ cells (gsp - 64#64) 8 ∗ cells (gsp - 96#64) 4 ∗
      stackAt (gsp - 96#64) allocHookStack

theorem grow_amortized_new_eq {cap : BitVec 64} (h : cap.toNat < 2 ^ 32) :
    (if (4#64).ult (if (cap + 1#64).ule (cap <<< 1) = true then cap <<< 1 else cap + 1#64) = true then
      if (cap + 1#64).ule (cap <<< 1) = true then cap <<< 1 else cap + 1#64
    else 4#64) = newCap cap := by
  have hadd : (cap + 1#64).toNat = cap.toNat + 1 := by
    rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  have hsh : (cap <<< 1).toNat = 2 * cap.toNat := by
    rw [BitVec.toNat_shiftLeft, Nat.shiftLeft_eq]
    change (cap.toNat * 2) % 2 ^ 64 = 2 * cap.toNat
    rw [Nat.mod_eq_of_lt (by omega)]
    omega
  have hm1 : (if (cap + 1#64).ule (cap <<< 1) = true then cap <<< 1 else cap + 1#64).toNat =
      max (2 * cap.toNat) (cap.toNat + 1) := by
    by_cases hc1 : (cap + 1#64).ule (cap <<< 1) = true
    · simp only [hc1, ite_true, hsh]
      rw [BitVec.ule_eq_decide, decide_eq_true_eq, hadd, hsh] at hc1
      omega
    · simp only [hc1, Bool.false_eq_true, ite_false, hadd]
      rw [BitVec.ule_eq_decide, decide_eq_true_eq, hadd, hsh] at hc1
      omega
  apply BitVec.eq_of_toNat_eq
  rw [newCap_toNat h]
  generalize (if (cap + 1#64).ule (cap <<< 1) = true then cap <<< 1 else cap + 1#64) = m1 at hm1 ⊢
  by_cases hc2 : (4#64).ult m1 = true
  · simp only [hc2, ite_true, hm1]
    rw [BitVec.ult_eq_decide, decide_eq_true_eq, hm1] at hc2
    change 4 < max (2 * cap.toNat) (cap.toNat + 1) at hc2
    omega
  · simp only [hc2, Bool.false_eq_true, ite_false]
    rw [BitVec.ult_eq_decide, decide_eq_true_eq, hm1] at hc2
    change ¬ 4 < max (2 * cap.toNat) (cap.toNat + 1) at hc2
    change 4 = max (2 * cap.toNat) 4
    omega

theorem fnAddr_back_164 {P : Program} {b : BitVec 64} {X : String → Option (State → State)}
    {name callee : String} {off coff : Nat}
    (h1 : P.fnOff name = off) (h2 : P.fnOff callee = coff)
    (hk : coff + 164 = off) :
    (P.rebase b X).fnAddr callee =
      (P.rebase b X).fnAddr name + bv% (2 ^ 64 + (ls_off% "<alloc::raw_vec::RawVecInner>::finish_grow [local#6]") - (ls_off% "<alloc::raw_vec::RawVecInner>::grow_amortized")) := by
  rw [Program.fnAddr_rebase, Program.fnAddr_rebase, h1, h2, ← hk]
  bv_omega

theorem grow_amortized_ok_trap {A : RustAlloc} {b : BitVec 64}
    {C : Crypto}
    {abs : String → Option (State → State)} (hA : AllocHooks A abs) :
    subroutine_ok (trTrapProgAt b C abs)
      ((trTrapProgAt b C abs).fnAddr growAmortizedName)
      (growAmortizedSpec A) := by
  unfold growAmortizedSpec
  have hc8 : ∀ gsp : BitVec 64, cells (gsp - 64#64) 8 =
      (∃∗ v0 : BitVec 64, ∃∗ v1 : BitVec 64, ∃∗ v2 : BitVec 64, ∃∗ v3 : BitVec 64,
       ∃∗ v4 : BitVec 64, ∃∗ v5 : BitVec 64, ∃∗ v6 : BitVec 64, ∃∗ v7 : BitVec 64,
        ((gsp - 64#64) ↦₆₄ v0) ∗ ((gsp - 56#64) ↦₆₄ v1) ∗ ((gsp - 48#64) ↦₆₄ v2) ∗
        ((gsp - 40#64) ↦₆₄ v3) ∗ ((gsp - 32#64) ↦₆₄ v4) ∗ ((gsp - 24#64) ↦₆₄ v5) ∗
        ((gsp - 16#64) ↦₆₄ v6) ∗ ((gsp - 8#64) ↦₆₄ v7)) := by
    intro gsp; cells_unfold
  simp only [hc8]
  clear hc8
  have hfn := (ls_lemma% fnOff "<alloc::raw_vec::RawVecInner>::grow_amortized")
  have hfg0 := finish_grow_7_zero_ok_trap (b := b) (C := C) hA
  have hfg1 := finish_grow_7_ne_ok_trap (b := b) (C := C) hA
  rw [fnAddr_back_164 (name := "<alloc::raw_vec::RawVecInner>::grow_amortized")
    hfn (ls_lemma% fnOff "<alloc::raw_vec::RawVecInner>::finish_grow [local#6]") (by decide)] at hfg0 hfg1
  code_fetches CryptoVerification.libsignalSessionCode libsignalSessionBin b
    (Rust.withPanics (trTrapExterns C abs)) hfn (num% (ls_off% "<alloc::raw_vec::RawVecInner>::grow_amortized")) 124
  dsimp only [trTrapProgAt, growAmortizedName] at hfg0 hfg1 ⊢
  clear hfn hA
  generalize_entry (libsignalSessionCode.rebase b
    (Rust.withPanics (trTrapExterns C abs))).fnAddr
    "<alloc::raw_vec::RawVecInner>::grow_amortized" = entry
  generalize_entry (libsignalSessionCode.rebase b
    (Rust.withPanics (trTrapExterns C abs))) = prog
    reverting [Program.fetch, Program.externAt?, subroutine_ok]
  examples_hide_fetches
  wp_init x s0
  obtain ⟨v, cap, ptr, gsp⟩ := x
  dsimp only at *
  subst gsp
  have hnew_eq := grow_amortized_new_eq h_4
  have hnew_toNat : (newCap cap).toNat = max (2 * cap.toNat) 4 := newCap_toNat h_4
  have hnew_pos : 0 < (newCap cap).toNat := by omega
  have hnew_bound : (newCap cap).toNat * 32 + 8 ≤ 2 ^ 63 := by omega
  by_cases hcap0 : cap = 0#64
  · subst hcap0
    simp only [ite_true, emp_sepConj]
    wp_steps
    wp_apply
    by_cases htag : w = 1#64
    · subst htag
      wp_simp_pre [ite_true, sepConj_assoc]
      apply SepWP.focus_pure (by sep_focus)
      rintro ⟨hw1, htrace⟩
      subst hw1
      wp_steps
      apply SepWP.instantiate_post_exists 8#64
      apply SepWP.instantiate_post_exists 0#64
      simp only [(by decide : (8#64 : BitVec 64) = 0xffffffffffffffff#64 ↔ False), ite_false]
      wp_done
    · wp_simp_pre [htag, ite_false, sepConj_assoc]
      apply SepWP.focus_pure (by sep_focus)
      rintro ⟨hw0, hp', htrace⟩
      subst hw0
      wp_steps
      apply SepWP.instantiate_post_exists 0xffffffffffffffff#64
      apply SepWP.instantiate_post_exists w_1
      simp only [ite_true, (by decide : newCap 0#64 = 4#64)]
      wp_done
  · wp_simp_pre [hcap0, ite_false]
    have hcap_bound : cap.toNat * 32 < 2 ^ 63 := by omega
    wp_steps
    wp_apply
    by_cases htag : w = 1#64
    · subst htag
      wp_simp_pre [ite_true, sepConj_assoc]
      apply SepWP.focus_pure (by sep_focus)
      rintro ⟨hw1, htrace⟩
      subst hw1
      wp_steps
      apply SepWP.instantiate_post_exists 8#64
      apply SepWP.instantiate_post_exists 0#64
      simp only [(by decide : (8#64 : BitVec 64) = 0xffffffffffffffff#64 ↔ False), hcap0, ite_false]
      wp_done
    · wp_simp_pre [htag, ite_false, sepConj_assoc]
      apply SepWP.focus_pure (by sep_focus)
      rintro ⟨hw0, hp', htrace⟩
      subst hw0
      wp_steps
      apply SepWP.instantiate_post_exists 0xffffffffffffffff#64
      apply SepWP.instantiate_post_exists w_1
      simp only [ite_true]
      wp_done

theorem grow_amortized_ok {A : RustAlloc} {b : BitVec 64}
    {C : Crypto} {ctl : BitVec 64}
    {abs : String → Option (State → State)} (hA : AllocHooks A abs) :
    subroutine_ok (tripleRatchetProgAt b C ctl abs)
      ((tripleRatchetProgAt b C ctl abs).fnAddr growAmortizedName)
      (growAmortizedSpec A) := by
  rw [← (trapsOnly_trTrap_kit b C ctl abs).fnAddr growAmortizedName]
  exact subroutine_ok_kit_of_trTrap (grow_amortized_ok_trap hA)

/-! ## `grow_one` specification and verification -/

def growOneStrPairSpec (A : RustAlloc) : Spec GrowAmortizedGhost where
  pre := fun (v, cap, ptr, osp) s =>
    ⌜s.readReg64 .x0 = v ∧ s.sp = osp ∧ cap.toNat < 2 ^ 32 ∧ ptr ≠ 0#64⌝ ∗
    (v ↦₆₄ cap) ∗ ((v + 8#64) ↦₆₄ ptr) ∗
    (if cap = 0#64 then emp
     else A.live ptr (cap.toNat * 32) 8 ∗ memRegion ptr (cap.toNat * 32)) ∗
    A.pool ∗ cells (osp - 16#64) 2 ∗ cells (osp - 80#64) 8 ∗ cells (osp - 112#64) 4 ∗
    stackAt (osp - 112#64) allocHookStack
  post := fun (v, cap, _ptr, osp) s0 sf =>
    ∃∗ p' : BitVec 64,
      ⌜p' ≠ 0#64 ∧ sf.trace = s0.trace⌝ ∗
      (v ↦₆₄ newCap cap) ∗ ((v + 8#64) ↦₆₄ p') ∗
      A.live p' ((newCap cap).toNat * 32) 8 ∗ memRegion p' ((newCap cap).toNat * 32) ∗
      A.pool ∗ cells (osp - 16#64) 2 ∗ cells (osp - 80#64) 8 ∗ cells (osp - 112#64) 4 ∗
      stackAt (osp - 112#64) allocHookStack
  onPanic := fun _ s0 sf => ⌜allocFailedIn s0 sf ∧ s0.trace <+: sf.trace⌝ ∗ anyHeap

theorem grow_one_str_pair_ok_trap {A : RustAlloc} {b : BitVec 64}
    {C : Crypto}
    {abs : String → Option (State → State)} (hA : AllocHooks A abs) :
    subroutine_ok (trTrapProgAt b C abs)
      ((trTrapProgAt b C abs).fnAddr growOneStrPairName)
      (growOneStrPairSpec A) := by
  unfold growOneStrPairSpec
  have hc2 : ∀ osp : BitVec 64, cells (osp - 16#64) 2 =
      (∃∗ v0 : BitVec 64, ∃∗ v1 : BitVec 64,
        ((osp - 16#64) ↦₆₄ v0) ∗ ((osp - 8#64) ↦₆₄ v1)) := by
    intro osp; cells_unfold
  simp only [hc2]
  clear hc2
  have hfn := (ls_lemma% fnOff "<alloc::raw_vec::RawVec<(&str, &str)>>::grow_one")
  have hpanic := panic_at_handle_error_trap (b := b) (C := C) (abs := abs) hfn
    (k := num% (ls_off% "alloc::raw_vec::handle_error" - ls_off% "<alloc::raw_vec::RawVec<(&str, &str)>>::grow_one")) (by decide)
  have hga := grow_amortized_ok_trap (b := b) (C := C) hA
  rw [Program.fnAddr_rel (name := "<alloc::raw_vec::RawVec<(&str, &str)>>::grow_one")
    hfn (ls_lemma% fnOff "<alloc::raw_vec::RawVecInner>::grow_amortized") (k := 200) (by decide)] at hga
  code_fetches CryptoVerification.libsignalSessionCode libsignalSessionBin b
    (Rust.withPanics (trTrapExterns C abs)) hfn (num% (ls_off% "<alloc::raw_vec::RawVec<(&str, &str)>>::grow_one")) 36
  dsimp only [trTrapProgAt, growOneStrPairName] at hpanic hga ⊢
  clear hfn hA
  generalize_entry (libsignalSessionCode.rebase b
    (Rust.withPanics (trTrapExterns C abs))).fnAddr
    "<alloc::raw_vec::RawVec<(&str, &str)>>::grow_one" = entry
  generalize_entry (libsignalSessionCode.rebase b
    (Rust.withPanics (trTrapExterns C abs))) = prog
    reverting [Program.fetch, Program.externAt?, subroutine_ok]
  examples_hide_fetches
  wpp_init x s0
  obtain ⟨v, cap, ptr, osp⟩ := x
  dsimp only at *
  subst osp
  apply SepWPp.of_sepWP (mid := entry + bv% (16))
  wp_steps
  wp_apply
  apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
  by_cases hres : w = 0xffffffffffffffff#64
  · conv => arg 4; simp only [hres, ite_true, sepConj_assoc]
    refine SepWPp.pure_elim fun ⟨hx0, hp', htrace⟩ => ?_
    apply SepWPp.of_sepWP_ret
    wp_steps
    apply SepWP.instantiate_post_exists w_1
    wp_done
  · conv => arg 4; simp only [hres, ite_false, sepConj_assoc]
    refine SepWPp.pure_elim fun ⟨hw8, hx0, htrace⟩ => ?_
    apply SepWPp.of_sepWP (mid := entry + bv% (ls_off% "alloc::raw_vec::handle_error" - ls_off% "<alloc::raw_vec::RawVec<(&str, &str)>>::grow_one"))
    wp_steps
    apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
    refine SepWPp.panic (by simp only [wp_norm, arm64_norm, *]) (by wp_norm_lhs) fun hm => ?_
    simpa only [sepConj_assoc] using
      allowPanic_panicked (allocFailedIn_of_eq (by simp only [Rust.panicked, wp_norm, arm64_norm, *])) hm

theorem grow_one_str_pair_ok {A : RustAlloc} {b : BitVec 64}
    {C : Crypto} {ctl : BitVec 64}
    {abs : String → Option (State → State)} (hA : AllocHooks A abs) :
    subroutine_ok (tripleRatchetProgAt b C ctl abs)
      ((tripleRatchetProgAt b C ctl abs).fnAddr growOneStrPairName)
      (growOneStrPairSpec A) := by
  rw [← (trapsOnly_trTrap_kit b C ctl abs).fnAddr growOneStrPairName]
  exact subroutine_ok_kit_of_trTrap (grow_one_str_pair_ok_trap hA)

end CryptoVerification.LibsignalTripleRatchet.InImage.DecodeErrorPush
