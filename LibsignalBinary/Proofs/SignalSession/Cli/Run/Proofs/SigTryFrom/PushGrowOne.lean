/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.TripleRatchet.InImage.DecodeErrorPush.GrowOne
public import LibsignalBinary.Proofs.TripleRatchet.Hooks2
import GeneratedLean.LibsignalSessionCode -- shake: keep
import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.SigTryFrom.PushCore
import LibsignalBinary.Proofs.TripleRatchet.Alloc.Defs
import LibsignalBinary.Proofs.TripleRatchet.GeneralizeEntry
import ProofLib.SepLogic.WP.Apply
import ProofLib.SepLogic.WPp

@[expose] public section

set_option autoImplicit false

namespace CryptoVerification.SignalSession.Cli.RunProofs.SigTryFromHelpers

open Arm64 ProofLib CryptoGames CryptoGames.HMAC CryptoGames.LibsignalSession
open CryptoVerification.RustHeap CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchet CryptoVerification.CodeLayout
open CryptoVerification.LibsignalTripleRatchet.InImage.DecodeErrorPush
open BS31

set_option maxRecDepth 200000
set_option maxHeartbeats 400000

attribute [local irreducible] Program.fetch Program.externAt? Program.fnOff
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero

attribute [local arm64_norm ↓, local wp_norm ↓]
  sp_setPC_pre_x sp_setMem_setPC_pre_x
  readReg64_setPC_pre_x readReg64_setMem_setPC_pre_x
  readReg32_setPC_pre_x readReg32_setMem_setPC_pre_x
  readReg_setPC_pre_x readReg_setMem_setPC_pre_x

theorem pre_inImage_merge {P Q : Prop} {S : SepProp} :
    ⌜P⌝ ∗ (⌜Q⌝ ∗ S) = ⌜P ∧ Q⌝ ∗ S := by
  rw [← sepConj_assoc, pure_sepConj_pure]

def growAmortizedSpecX (A : RustAlloc) : Spec GrowAmortizedGhost where
  pre := fun (v, cap, ptr, gsp) s =>
    ⌜s.readReg64 .x0 = v ∧ s.readReg64 .x1 = cap ∧ s.sp = gsp ∧
      cap.toNat < 2 ^ 32 ∧ ptr ≠ 0#64⌝ ∗
    (v ↦₆₄ cap) ∗ ((v + 8#64) ↦₆₄ ptr) ∗
    (if cap = 0#64 then emp
     else A.live ptr (cap.toNat * 32) 8 ∗ memRegion ptr (cap.toNat * 32)) ∗
    A.pool ∗ cells (gsp - 64#64) 8 ∗ cells (gsp - 96#64) 4 ∗
    stackAt (gsp - 96#64) extHookStack
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
      stackAt (gsp - 96#64) extHookStack

theorem grow_amortized_ok_ext_x {img : Obj.Image} {A : RustAlloc}
    {ext : String → Option (State → State)} (hA : AllocContractsX img A ext) :
    subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr growAmortizedName)
      ((growAmortizedSpecX A).inImage img) := by
  unfold Spec.inImage growAmortizedSpecX
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
  have hfg0 := finish_grow_7_zero_ok_ext_x hA
  have hfg1 := finish_grow_7_ne_ok_ext_x hA
  rw [fnAddr_back_164 (name := "<alloc::raw_vec::RawVecInner>::grow_amortized")
    hfn (ls_lemma% fnOff "<alloc::raw_vec::RawVecInner>::finish_grow [local#6]") (by decide)] at hfg0 hfg1
  code_fetches CryptoVerification.libsignalSessionCode
    CryptoVerification.LibsignalTripleRatchet.InImage.DecodeErrorPush.libsignalSessionBin img.base
    (Rust.withPanics ext) hfn (num% (ls_off% "<alloc::raw_vec::RawVecInner>::grow_amortized")) 124
  dsimp only [tripleRatchetProgAtExt, growAmortizedName] at hfg0 hfg1 ⊢
  clear hfn hA
  generalize_entry (libsignalSessionCode.rebase img.base
    (Rust.withPanics ext)).fnAddr
    "<alloc::raw_vec::RawVecInner>::grow_amortized" = entry
  generalize_entry (libsignalSessionCode.rebase img.base
    (Rust.withPanics ext)) = prog
    reverting [Program.fetch, Program.externAt?, subroutine_ok]
  examples_hide_fetches
  wp_init x s0
  obtain ⟨v, cap, ptr, gsp⟩ := x
  dsimp only at *
  have hinv0 : ImgCallInv img s0 := ⟨by assumption, by assumption⟩
  have hcap_lt : cap.toNat < 2 ^ 32 := by assumption
  subst gsp
  have hnew_eq := grow_amortized_new_eq hcap_lt
  have hnew_toNat : (newCap cap).toNat = max (2 * cap.toNat) 4 := newCap_toNat hcap_lt
  have hnew_pos : 0 < (newCap cap).toNat := by omega
  have hnew_bound : (newCap cap).toNat * 32 + 8 ≤ 2 ^ 63 := by omega
  by_cases hcap0 : cap = 0#64
  · subst hcap0
    simp only [ite_true, emp_sepConj]
    apply SepWP.seq_inImage
      (mid := entry + bv% (2 ^ 64 + (ls_off% "<alloc::raw_vec::RawVecInner>::finish_grow [local#6]") - (ls_off% "<alloc::raw_vec::RawVecInner>::grow_amortized"))) hinv0
    wp_steps
    apply SepWP.done (by rfl) (by wp_norm_lhs)
    rintro ⟨hF1, hsym1⟩
    wp_apply
    by_cases htag : w = 1#64
    · subst htag
      wp_simp_pre [ite_true, sepConj_assoc]
      apply SepWP.focus_pure (by sep_focus)
      rintro ⟨hw1, htrace⟩
      subst hw1
      wp_steps
      apply CryptoVerification.LibsignalTripleRatchet.SepWP.instantiate_post_exists 8#64
      apply CryptoVerification.LibsignalTripleRatchet.SepWP.instantiate_post_exists 0#64
      simp only [(by decide : (8#64 : BitVec 64) = 0xffffffffffffffff#64 ↔ False), ite_false]
      wp_done
    · wp_simp_pre [htag, ite_false, sepConj_assoc]
      apply SepWP.focus_pure (by sep_focus)
      rintro ⟨hw0, hp', htrace⟩
      subst hw0
      wp_steps
      apply CryptoVerification.LibsignalTripleRatchet.SepWP.instantiate_post_exists 0xffffffffffffffff#64
      apply CryptoVerification.LibsignalTripleRatchet.SepWP.instantiate_post_exists w_1
      simp only [ite_true, (by decide : newCap 0#64 = 4#64)]
      wp_done
  · wp_simp_pre [hcap0, ite_false]
    have hcap_bound : cap.toNat * 32 < 2 ^ 63 := by omega
    apply SepWP.seq_inImage
      (mid := entry + bv% (2 ^ 64 + (ls_off% "<alloc::raw_vec::RawVecInner>::finish_grow [local#6]") - (ls_off% "<alloc::raw_vec::RawVecInner>::grow_amortized"))) hinv0
    wp_steps
    apply SepWP.done (by rfl) (by wp_norm_lhs)
    rintro ⟨hF1, hsym1⟩
    wp_apply
    by_cases htag : w = 1#64
    · subst htag
      wp_simp_pre [ite_true, sepConj_assoc]
      apply SepWP.focus_pure (by sep_focus)
      rintro ⟨hw1, htrace⟩
      subst hw1
      wp_steps
      apply CryptoVerification.LibsignalTripleRatchet.SepWP.instantiate_post_exists 8#64
      apply CryptoVerification.LibsignalTripleRatchet.SepWP.instantiate_post_exists 0#64
      simp only [(by decide : (8#64 : BitVec 64) = 0xffffffffffffffff#64 ↔ False), hcap0, ite_false]
      wp_done
    · wp_simp_pre [htag, ite_false, sepConj_assoc]
      apply SepWP.focus_pure (by sep_focus)
      rintro ⟨hw0, hp', htrace⟩
      subst hw0
      wp_steps
      apply CryptoVerification.LibsignalTripleRatchet.SepWP.instantiate_post_exists 0xffffffffffffffff#64
      apply CryptoVerification.LibsignalTripleRatchet.SepWP.instantiate_post_exists w_1
      simp only [ite_true]
      wp_done

def growOneStrPairSpecX (A : RustAlloc) : Spec GrowAmortizedGhost where
  pre := fun (v, cap, ptr, osp) s =>
    ⌜s.readReg64 .x0 = v ∧ s.sp = osp ∧ cap.toNat < 2 ^ 32 ∧ ptr ≠ 0#64⌝ ∗
    (v ↦₆₄ cap) ∗ ((v + 8#64) ↦₆₄ ptr) ∗
    (if cap = 0#64 then emp
     else A.live ptr (cap.toNat * 32) 8 ∗ memRegion ptr (cap.toNat * 32)) ∗
    A.pool ∗ cells (osp - 16#64) 2 ∗ cells (osp - 80#64) 8 ∗ cells (osp - 112#64) 4 ∗
    stackAt (osp - 112#64) extHookStack
  post := fun (v, cap, _ptr, osp) s0 sf =>
    ∃∗ p' : BitVec 64,
      ⌜p' ≠ 0#64 ∧ sf.trace = s0.trace⌝ ∗
      (v ↦₆₄ newCap cap) ∗ ((v + 8#64) ↦₆₄ p') ∗
      A.live p' ((newCap cap).toNat * 32) 8 ∗ memRegion p' ((newCap cap).toNat * 32) ∗
      A.pool ∗ cells (osp - 16#64) 2 ∗ cells (osp - 80#64) 8 ∗ cells (osp - 112#64) 4 ∗
      stackAt (osp - 112#64) extHookStack
  onPanic := fun _ s0 sf => ⌜allocFailedIn s0 sf ∧ s0.trace <+: sf.trace⌝ ∗ anyHeap

theorem grow_one_str_pair_ok_ext_x {img : Obj.Image} {A : RustAlloc}
    {ext : String → Option (State → State)} (hA : AllocContractsX img A ext) :
    subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr growOneStrPairName)
      ((growOneStrPairSpecX A).inImage img) := by
  unfold Spec.inImage growOneStrPairSpecX
  have hc2 : ∀ osp : BitVec 64, cells (osp - 16#64) 2 =
      (∃∗ v0 : BitVec 64, ∃∗ v1 : BitVec 64,
        ((osp - 16#64) ↦₆₄ v0) ∗ ((osp - 8#64) ↦₆₄ v1)) := by
    intro osp; cells_unfold
  simp only [hc2]
  clear hc2
  have hfn := (ls_lemma% fnOff "<alloc::raw_vec::RawVec<(&str, &str)>>::grow_one")
  have hpanic := panic_at_handle_error_norm_ext (b := img.base) (ext := ext)
    (name := growOneStrPairName)
    (k := num% (ls_off% "alloc::raw_vec::handle_error" - ls_off% "<alloc::raw_vec::RawVec<(&str, &str)>>::grow_one"))
    (by rw [hfn, (ls_stub% "alloc::raw_vec::handle_error")])
  have hga := grow_amortized_ok_ext_x hA
  rw [Program.fnAddr_rel (name := "<alloc::raw_vec::RawVec<(&str, &str)>>::grow_one")
    hfn (ls_lemma% fnOff "<alloc::raw_vec::RawVecInner>::grow_amortized") (k := 200) (by decide)] at hga
  code_fetches CryptoVerification.libsignalSessionCode
    CryptoVerification.LibsignalTripleRatchet.InImage.DecodeErrorPush.libsignalSessionBin img.base
    (Rust.withPanics ext) hfn (num% (ls_off% "<alloc::raw_vec::RawVec<(&str, &str)>>::grow_one")) 36
  dsimp only [tripleRatchetProgAtExt, growOneStrPairName] at hpanic hga ⊢
  clear hfn hA
  generalize_entry (libsignalSessionCode.rebase img.base
    (Rust.withPanics ext)).fnAddr
    "<alloc::raw_vec::RawVec<(&str, &str)>>::grow_one" = entry
  generalize_entry (libsignalSessionCode.rebase img.base
    (Rust.withPanics ext)) = prog
    reverting [Program.fetch, Program.externAt?, subroutine_ok]
  examples_hide_fetches
  wpp_init x s0
  obtain ⟨v, cap, ptr, osp⟩ := x
  dsimp only at *
  have hinv0 : ImgCallInv img s0 := ⟨by assumption, by assumption⟩
  subst osp
  apply SepWPp.of_sepWP (mid := entry + bv% (16))
  apply SepWP.seq_inImage (mid := entry + bv% (200)) hinv0
  wp_steps
  apply SepWP.done (by rfl) (by wp_norm_lhs)
  rintro ⟨hF1, hsym1⟩
  wp_apply
  apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
  by_cases hres : w = 0xffffffffffffffff#64
  · conv => arg 4; simp only [hres, ite_true, sepConj_assoc]
    refine SepWPp.pure_elim fun ⟨hx0, hp', htrace⟩ => ?_
    apply SepWPp.of_sepWP_ret
    wp_steps
    apply CryptoVerification.LibsignalTripleRatchet.SepWP.instantiate_post_exists w_1
    wp_done
  · conv => arg 4; simp only [hres, ite_false, sepConj_assoc]
    refine SepWPp.pure_elim fun ⟨hw8, hx0, htrace⟩ => ?_
    apply SepWPp.of_sepWP
      (mid := entry + bv% (ls_off% "alloc::raw_vec::handle_error" - ls_off% "<alloc::raw_vec::RawVec<(&str, &str)>>::grow_one"))
    wp_steps
    apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
    refine SepWPp.panic (by simp only [wp_norm, arm64_norm, *]) (by wp_norm_lhs) fun hm => ?_
    simpa only [sepConj_assoc] using
      allowPanic_panicked
        (CryptoVerification.LibsignalTripleRatchet.allocFailedIn_of_eq
          (by simp only [Rust.panicked, wp_norm, arm64_norm, *])) hm

end CryptoVerification.SignalSession.Cli.RunProofs.SigTryFromHelpers
