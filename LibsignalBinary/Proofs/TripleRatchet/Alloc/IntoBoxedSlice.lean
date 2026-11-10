/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.TripleRatchet.Alloc.OptContracts
public import LibsignalBinary.Proofs.TripleRatchet.Alloc.AllocCodeSym
public import LibsignalBinary.Proofs.ConsumeMessageKey.GrowOneProofs.GrowOneCodeSym
import GeneratedLean.LibsignalTripleRatchet -- shake: keep
import LibsignalBinary.Proofs.CodeLayout
import LibsignalBinary.Proofs.Placed.GenLsBlock
import ProofLib.SepLogic.WPp

/-!
# `<alloc::vec::Vec<u8>>::into_boxed_slice` (`0x1afd4`)

Verifies `<alloc::vec::Vec<u8>>::into_boxed_slice` (`0x1afd4`, 31 instructions) against
`intoBoxedSliceSpec A` on `tripleRatchetProgAt`, covering:
1. `cap.toNat = bytes.length` (no allocator call),
2. `bytes.length < cap.toNat` and `bytes = []` (`__rust_dealloc`),
3. `bytes.length < cap.toNat` and `bytes ≠ []` (`__rust_realloc`, plus OOM panic via `handle_error`).
-/

@[expose] public section

namespace CryptoVerification.LibsignalTripleRatchet

open Arm64 ProofLib CryptoVerification.RustHeap
  CryptoGames.LibsignalSession CryptoVerification.LibsignalTripleRatchetRepr
  CryptoVerification.LibsignalSession CryptoVerification.InImageLift

set_option maxRecDepth 200000
set_option maxHeartbeats 1600000

attribute [local irreducible] Program.fetch Program.externAt?
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero

private theorem stackAt_intoBoxedSlice_opt {hookStack : Nat}
    (hstack : hookStack + 32 ≤ 2 ^ 64) (sp : BitVec 64) :
    stackAt sp (hookStack + 32) =
      stackAt (sp - 32#64) hookStack ∗ cells (sp - 32#64) 4 :=
  stackAt_split_cells sp hookStack 4 hstack

theorem ule_eq_false_of_lt {cap : BitVec 64} {n : Nat}
    (hlt : n < cap.toNat) :
    cap.ule (BitVec.ofNat 64 n) = false := by
  have h64 : cap.toNat < 2 ^ 64 := cap.isLt
  rw [BitVec.ule_eq_decide, decide_eq_false_iff_not, BitVec.toNat_ofNat,
    Nat.mod_eq_of_lt (by omega)]
  omega

private theorem ofNat_ne_zero_of_pos {n : Nat} (hpos : 0 < n) (h64 : n < 2 ^ 64) :
    BitVec.ofNat 64 n ≠ 0#64 := by
  intro heq
  have ht := congrArg BitVec.toNat heq
  rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt h64] at ht
  change n = 0 at ht
  omega

private theorem beq_ofNat_zero_eq_false {n : Nat} (hpos : 0 < n) (h64 : n < 2 ^ 64) :
    (BitVec.ofNat 64 n == 0#64) = false := by
  rw [beq_eq_false_iff_ne]
  exact ofNat_ne_zero_of_pos hpos h64

private theorem sepWPp_pure_mid {prog : Program} {ret : BitVec 64} {s : State}
    {A B C : SepProp} {φ : Prop} {Q Qp : State → SepProp → Prop}
    (h : φ → SepWPp prog ret s (A ∗ B ∗ C) Q Qp) :
    SepWPp prog ret s (A ∗ B ∗ ⌜φ⌝ ∗ C) Q Qp := by
  rw [show A ∗ B ∗ ⌜φ⌝ ∗ C = ⌜φ⌝ ∗ A ∗ B ∗ C by ac_rfl]
  exact SepWPp.pure_elim h

theorem into_boxed_slice_ok_of_hooks_opt {oimg : Option Obj.Image} {A : RustAlloc}
    {b : BitVec 64} {ext : String → Option (State → State)} {hookStack : Nat}
    (hstack : hookStack + 32 ≤ 2 ^ 64 := by decide)
    (hdealloc : subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr intoBoxedSliceName +
        BitVec.ofNat 64 (num% (ls_off% "__rustc::__rust_dealloc" -
          ls_off% "<alloc::vec::Vec<u8>>::into_boxed_slice")))
      (specWithOptInv oimg (rustDeallocExternSpecWithStack A hookStack)))
    (hrealloc : subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr intoBoxedSliceName +
        BitVec.ofNat 64 (num% (ls_off% "__rustc::__rust_realloc" -
          ls_off% "<alloc::vec::Vec<u8>>::into_boxed_slice")))
      (specWithOptInv oimg (rustReallocExternSpecWithStack A hookStack))) :
    subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr intoBoxedSliceName)
      (specWithOptInv oimg (intoBoxedSliceSpecWithStack A hookStack)) := by
  unfold specWithOptInv
  simp only [intoBoxedSliceSpecWithStack, VecArg.at, vecU8At, vecHeader, boxU8Buf,
    stackAt_intoBoxedSlice_opt hstack]
  cells_unfold
  have hfn : libsignalSessionCode.fnOff intoBoxedSliceName = num% (ls_off% "<alloc::vec::Vec<u8>>::into_boxed_slice") :=
    (ls_lemma% fnOff "<alloc::vec::Vec<u8>>::into_boxed_slice")
  have hpanic := panic_at_handle_error_norm_ext (b := b) (ext := ext)
    (name := intoBoxedSliceName) (k := num% (ls_off% "alloc::raw_vec::handle_error" - ls_off% "<alloc::vec::Vec<u8>>::into_boxed_slice"))
  code_fetches CryptoVerification.libsignalSessionCode
    CryptoVerification.LibsignalTripleRatchet.libsignalTripleRatchetBin b
    (Rust.withPanics ext) hfn (num% (ls_off% "<alloc::vec::Vec<u8>>::into_boxed_slice")) 124
  wpp_init x s0
  examples_generalize_entry
  examples_hide_fetches
  obtain ⟨v, cap, ptr, bs⟩ := x
  dsimp only at *
  have hinv0 : OptCallInv oimg s0 := by assumption
  have hbs_le_cap : bs.length ≤ cap.toNat := by assumption
  have hlen_lt63 : bs.length < 2 ^ 63 := by omega
  have hlen_toNat : (BitVec.ofNat 64 bs.length).toNat = bs.length := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  have hpow2 : ∃ k, 1 = 2 ^ k := ⟨0, rfl⟩
  rcases Nat.eq_or_lt_of_le hbs_le_cap with hcap_eq | hcap_lt
  · -- Case 1: `bs.length = cap.toNat` (`b.ls` taken to `+0x44`)
    have hcap_bv : BitVec.ofNat 64 bs.length = cap := by
      apply BitVec.eq_of_toNat_eq
      rw [hlen_toNat, hcap_eq]
    rw [hcap_bv]
    have hule : cap.ule cap = true := by
      rw [BitVec.ule_eq_decide, decide_eq_true_iff]
    by_cases hcap0 : cap = 0
    · subst hcap0
      have hbs : bs = [] := List.eq_nil_of_length_eq_zero hcap_eq
      subst hbs
      simp only [ite_true, sepConj_emp]
      apply SepWPp.of_sepWP_ret
      wp_steps
      wp_done
    · have hbs_ne : bs ≠ [] := by
        intro hnil
        apply hcap0
        apply BitVec.eq_of_toNat_eq
        rw [← hcap_eq, hnil]
        rfl
      simp only [hcap0, hbs_ne, ← hcap_eq, Nat.sub_self, memRegion_zero,
        ite_false, sepConj_emp]
      apply SepWPp.of_sepWP_ret
      wp_steps
      wp_done
  · -- Case 2 & 3: `bs.length < cap.toNat` (`b.ls` not taken)
    have hcap0 : cap ≠ 0 := by
      intro heq
      subst heq
      change bs.length < 0 at hcap_lt
      omega
    have hpos_cap : 0 < cap.toNat := by omega
    have hbound_cap : cap.toNat + 1 ≤ 2 ^ 63 := by omega
    have hlay_cap : LayoutOk cap.toNat 1 := ⟨hpos_cap, hpow2, hbound_cap⟩
    have hule : cap.ule (BitVec.ofNat 64 bs.length) = false :=
      ule_eq_false_of_lt hcap_lt
    by_cases hbs : bs = []
    · -- Case 2: `bs = []` (`cbz x19` taken to `+0x58`, calls `__rust_dealloc`)
      subst hbs
      have hule0 : cap.ule 0#64 = false := hule
      simp only [hcap0, ite_false, List.length_nil,
        pointsToBytes_nil, BitVec.add_zero, Nat.sub_zero, ite_true, emp_sepConj, sepConj_emp]
      apply SepWPp.of_sepWP_ret
      apply SepWP.seq_optImage (mid := entry + bv% (ls_off% "__rustc::__rust_dealloc" - ls_off% "<alloc::vec::Vec<u8>>::into_boxed_slice")) hinv0
      wp_steps
      apply SepWP.done (by rfl) (by wp_norm_lhs)
      intro hinv1
      wp_call hdealloc (ptr, cap.toNat, 1)
      wp_steps
      wp_done
    · -- Case 3: `bs ≠ []` (`cbz x19` not taken, calls `__rust_realloc`)
      have hpos : 0 < bs.length := List.length_pos_iff.mpr hbs
      have hbound_bs : bs.length + 1 ≤ 2 ^ 63 := by omega
      have hlen_ne0 : BitVec.ofNat 64 bs.length ≠ 0#64 :=
        ofNat_ne_zero_of_pos hpos (by omega)
      have hlen_beq0 : (BitVec.ofNat 64 bs.length == 0#64) = false :=
        beq_ofNat_zero_eq_false hpos (by omega)
      have hlay_new : LayoutOk bs.length 1 := ⟨hpos, hpow2, hbound_bs⟩
      have hmin : bs.length ≤ min cap.toNat bs.length := by omega
      simp only [hcap0, hbs, ite_false, sepConj_assoc]
      apply SepWPp.of_sepWP (mid := entry + bv% (48))
      apply SepWP.seq_optImage (mid := entry + bv% (ls_off% "__rustc::__rust_realloc" - ls_off% "<alloc::vec::Vec<u8>>::into_boxed_slice")) hinv0
      wp_steps
      apply SepWP.done (by rfl) (by wp_norm_lhs)
      intro hinv1
      wp_call hrealloc (ptr, cap.toNat, 1, bs.length, bs)
      apply SepWP.done (by simp_all) (by simp_all)
      by_cases hoom : sf.readReg64 (Reg.gpr 0#5) = 0
      · have hoom64 : sf.readReg64 (Reg.gpr 0#5) = 0#64 := hoom
        simp only [hoom, ite_true, sepConj_assoc]
        refine sepWPp_pure_mid fun htrace => ?_
        apply SepWPp.of_sepWP (mid := entry + bv% (ls_off% "alloc::raw_vec::handle_error" - ls_off% "<alloc::vec::Vec<u8>>::into_boxed_slice"))
        wp_steps
        apply SepWP.done (by simp_all) (by simp_all)
        refine SepWPp.panic (by simp_all) (by simp_all) fun hm => ?_
        simpa only [sepConj_assoc] using
          allowPanic_panicked (allocFailedIn_of_eq (by simp_all [Rust.panicked])) hm
      · have hoom64 : sf.readReg64 (Reg.gpr 0#5) ≠ 0#64 := hoom
        simp only [hoom, Nat.sub_self, memRegion_zero, sepConj_emp, ite_false, sepConj_assoc]
        refine sepWPp_pure_mid fun ⟨hmod, htrace⟩ => ?_
        apply SepWPp.of_sepWP_ret
        wp_steps
        wp_done

theorem into_boxed_slice_ok_ext {A : RustAlloc} {b : BitVec 64}
    {ext : String → Option (State → State)} (hA : AllocContracts b A ext) :
    subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr intoBoxedSliceName)
      (intoBoxedSliceSpec A) :=
  subroutine_ok_of_optNone <|
    into_boxed_slice_ok_of_hooks_opt (by decide)
      (dealloc_opt_of_base hA (name := intoBoxedSliceName)
        (k := num% (ls_off% "__rustc::__rust_dealloc" - ls_off% "<alloc::vec::Vec<u8>>::into_boxed_slice")))
      (realloc_opt_of_base hA (name := intoBoxedSliceName)
        (k := num% (ls_off% "__rustc::__rust_realloc" - ls_off% "<alloc::vec::Vec<u8>>::into_boxed_slice")))

/-- `<alloc::vec::Vec<u8>>::into_boxed_slice` (`0x1afd4`) meets `intoBoxedSliceSpec A` on `tripleRatchetProgAt`. -/
theorem into_boxed_slice_ok {A : RustAlloc} {b : BitVec 64}
    {C : Crypto} {ctl : BitVec 64}
    {abs : String → Option (State → State)} (hA : AllocHooks A abs) :
    subroutine_ok (tripleRatchetProgAt b C ctl abs)
      ((tripleRatchetProgAt b C ctl abs).fnAddr intoBoxedSliceName)
      (intoBoxedSliceSpec A) :=
  into_boxed_slice_ok_ext (AllocContracts.of_tripleRatchetProgAt b C A ctl abs hA)

theorem into_boxed_slice_ok_ext_x {img : Obj.Image} {A : RustAlloc}
    {ext : String → Option (State → State)} (hA : AllocContractsX img A ext) :
    subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr intoBoxedSliceName)
      ((intoBoxedSliceSpecX A).inImage img) :=
  into_boxed_slice_ok_of_hooks_opt (oimg := some img) (by decide)
    (dealloc_opt_of_x hA (name := intoBoxedSliceName)
      (k := num% (ls_off% "__rustc::__rust_dealloc" - ls_off% "<alloc::vec::Vec<u8>>::into_boxed_slice")))
    (realloc_opt_of_x hA (name := intoBoxedSliceName)
      (k := num% (ls_off% "__rustc::__rust_realloc" - ls_off% "<alloc::vec::Vec<u8>>::into_boxed_slice")))

/-! ## Relocatable `[LibsignalPlacement]` Contract (Block `56`) -/

theorem into_boxed_slice_placed_ok_of_hooks [LibsignalPlacement] {A : RustAlloc}
    {H : String → Option (State → State)} {hookStack : Nat}
    (hstack : hookStack + 32 ≤ 2 ^ 64 := by decide)
    (hdealloc : subroutine_ok ((blkPC_56).rebase (blkPl_56).base H)
      (lsρ lsRustDeallocSym) (rustDeallocExternSpecWithStack A hookStack))
    (hrealloc : subroutine_ok ((blkPC_56).rebase (blkPl_56).base H)
      (lsρ lsRustReallocSym) (rustReallocExternSpecWithStack A hookStack))
    (hpanic : ((blkPC_56).rebase (blkPl_56).base H).externAt? (lsρ lsHandleErrorSym) =
      some Rust.panicked) :
    subroutine_ok ((blkPC_56).rebase (blkPl_56).base H) (blkPl_56).base
      (intoBoxedSliceSpecWithStack A hookStack) := by
  simp only [intoBoxedSliceSpecWithStack, VecArg.at, vecU8At, vecHeader, boxU8Buf,
    stackAt_intoBoxedSlice_opt hstack]
  cells_unfold
  wpp_init x s0
  obtain ⟨v, cap, ptr, bs⟩ := x
  dsimp only at *
  have hbs_le_cap : bs.length ≤ cap.toNat := by assumption
  have hlen_lt63 : bs.length < 2 ^ 63 := by omega
  have hlen_toNat : (BitVec.ofNat 64 bs.length).toNat = bs.length := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  have hpow2 : ∃ k, 1 = 2 ^ k := ⟨0, rfl⟩
  rcases Nat.eq_or_lt_of_le hbs_le_cap with hcap_eq | hcap_lt
  · -- Case 1: `bs.length = cap.toNat` (`b.ls` taken to `+0x44`)
    have hcap_bv : BitVec.ofNat 64 bs.length = cap := by
      apply BitVec.eq_of_toNat_eq
      rw [hlen_toNat, hcap_eq]
    rw [hcap_bv]
    have hule : cap.ule cap = true := by
      rw [BitVec.ule_eq_decide, decide_eq_true_iff]
    by_cases hcap0 : cap = 0
    · subst hcap0
      have hbs : bs = [] := List.eq_nil_of_length_eq_zero hcap_eq
      subst hbs
      simp only [ite_true, sepConj_emp]
      apply SepWPp.of_sepWP_ret
      wp_steps
      wp_done
    · have hbs_ne : bs ≠ [] := by
        intro hnil
        apply hcap0
        apply BitVec.eq_of_toNat_eq
        rw [← hcap_eq, hnil]
        rfl
      simp only [hcap0, hbs_ne, ← hcap_eq, Nat.sub_self, memRegion_zero,
        ite_false, sepConj_emp]
      apply SepWPp.of_sepWP_ret
      wp_steps
      wp_done
  · -- Case 2 & 3: `bs.length < cap.toNat` (`b.ls` not taken)
    have hcap0 : cap ≠ 0 := by
      intro heq
      subst heq
      change bs.length < 0 at hcap_lt
      omega
    have hpos_cap : 0 < cap.toNat := by omega
    have hbound_cap : cap.toNat + 1 ≤ 2 ^ 63 := by omega
    have hlay_cap : LayoutOk cap.toNat 1 := ⟨hpos_cap, hpow2, hbound_cap⟩
    have hule : cap.ule (BitVec.ofNat 64 bs.length) = false :=
      ule_eq_false_of_lt hcap_lt
    by_cases hbs : bs = []
    · -- Case 2: `bs = []` (`cbz x19` taken to `+0x58`, calls `__rust_dealloc`)
      subst hbs
      have hule0 : cap.ule 0#64 = false := hule
      simp only [hcap0, ite_false, List.length_nil,
        pointsToBytes_nil, BitVec.add_zero, Nat.sub_zero, ite_true, emp_sepConj, sepConj_emp]
      apply SepWPp.of_sepWP_ret
      wp_steps
      wp_call hdealloc (ptr, cap.toNat, 1)
      wp_steps
      wp_done
    · -- Case 3: `bs ≠ []` (`cbz x19` not taken, calls `__rust_realloc`)
      have hpos : 0 < bs.length := List.length_pos_iff.mpr hbs
      have hbound_bs : bs.length + 1 ≤ 2 ^ 63 := by omega
      have hlen_ne0 : BitVec.ofNat 64 bs.length ≠ 0#64 :=
        ofNat_ne_zero_of_pos hpos (by omega)
      have hlen_beq0 : (BitVec.ofNat 64 bs.length == 0#64) = false :=
        beq_ofNat_zero_eq_false hpos (by omega)
      have hlay_new : LayoutOk bs.length 1 := ⟨hpos, hpow2, hbound_bs⟩
      have hmin : bs.length ≤ min cap.toNat bs.length := by omega
      simp only [hcap0, hbs, ite_false, sepConj_assoc]
      apply SepWPp.of_sepWP (mid := (blkPl_56).base + bv% (48))
      wp_steps
      wp_call hrealloc (ptr, cap.toNat, 1, bs.length, bs)
      apply SepWP.done (by simp_all) (by simp_all)
      by_cases hoom : sf.readReg64 (Reg.gpr 0#5) = 0
      · have hoom64 : sf.readReg64 (Reg.gpr 0#5) = 0#64 := hoom
        simp only [hoom, ite_true, sepConj_assoc]
        refine sepWPp_pure_mid fun htrace => ?_
        apply SepWPp.of_sepWP (mid := lsρ lsHandleErrorSym)
        wp_steps
        apply SepWP.done (by simp_all) (by simp_all)
        refine SepWPp.panic (by simp_all) (by simp_all) fun hm => ?_
        simpa only [sepConj_assoc] using
          allowPanic_panicked (allocFailedIn_of_eq (by simp_all [Rust.panicked])) hm
      · have hoom64 : sf.readReg64 (Reg.gpr 0#5) ≠ 0#64 := hoom
        simp only [hoom, Nat.sub_self, memRegion_zero, sepConj_emp, ite_false, sepConj_assoc]
        refine sepWPp_pure_mid fun ⟨hmod, htrace⟩ => ?_
        apply SepWPp.of_sepWP_ret
        wp_steps
        wp_done

/-- Relocatable `<alloc::vec::Vec<u8>>::into_boxed_slice` (Block `56`) meets
`intoBoxedSliceSpec A`. -/
theorem into_boxed_slice_placed_ok [LibsignalPlacement] {A : RustAlloc}
    {H : String → Option (State → State)}
    (hdealloc : HookSat H lsRustDeallocSym (rustDeallocSpec A))
    (hrealloc : HookSat H lsRustReallocSym (rustReallocSpec A))
    (hpanic : H lsHandleErrorSym = some Rust.panicked) :
    subroutine_ok ((blkPC_56).rebase (blkPl_56).base H) (blkPl_56).base
      (intoBoxedSliceSpec A) :=
  into_boxed_slice_placed_ok_of_hooks (hookStack := allocHookStack) (by decide)
    (rustDeallocExternWithStack_of_rustDealloc (ls_hook_ok_of_mem hdealloc) (by decide) (by decide))
    (rustReallocExternWithStack_of_rustRealloc (ls_hook_ok_of_mem hrealloc) (by decide) (by decide))
    ((ls_externAt?_of_mem).trans hpanic)

theorem into_boxed_slice_placed_ok_x [LibsignalPlacement] {A : RustAlloc}
    {H : String → Option (State → State)}
    (hdealloc : HookSat H lsRustDeallocSym (rustDeallocSpec A))
    (hrealloc : HookSat H lsRustReallocSym (rustReallocSpec A))
    (hpanic : H lsHandleErrorSym = some Rust.panicked) :
    subroutine_ok ((blkPC_56).rebase (blkPl_56).base H) (blkPl_56).base
      (intoBoxedSliceSpecX A) :=
  into_boxed_slice_placed_ok_of_hooks (hookStack := extHookStack) (by decide)
    (rustDeallocExternWithStack_of_rustDealloc (ls_hook_ok_of_mem hdealloc) (by decide) (by decide))
    (rustReallocExternWithStack_of_rustRealloc (ls_hook_ok_of_mem hrealloc) (by decide) (by decide))
    ((ls_externAt?_of_mem).trans hpanic)

end CryptoVerification.LibsignalTripleRatchet
