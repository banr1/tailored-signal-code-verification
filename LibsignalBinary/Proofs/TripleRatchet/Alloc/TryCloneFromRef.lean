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
import ProofLib.SepLogic.WPp

/-!
# `<alloc::boxed::Box<[u8]>>::try_clone_from_ref_in` (`0xd0a0`)

Verifies `<alloc::boxed::Box<[u8]>>::try_clone_from_ref_in` (`0xd0a0`, 28 instructions) against
`tryCloneFromRefSpec A` on `tripleRatchetProgAt`, covering:
1. `bs = []` (`cbz x1` taken to `0xd0f8`, returning `x0 = 1, x1 = 0` without calling the allocator),
2. `bs ≠ []` (`shim` + `__rust_alloc` + `memcpy` on success, or returning `x0 = 0, x1 = bs.length`
   with `allocFailedEvent` on allocator failure).
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

private theorem stackAt_tryCloneFromRef_opt {hookStack : Nat}
    (hstack : hookStack + 48 ≤ 2 ^ 64) (sp : BitVec 64) :
    stackAt sp (hookStack + 48) =
      stackAt (sp - 48#64) hookStack ∗ cells (sp - 48#64) 6 :=
  stackAt_split_cells sp hookStack 6 hstack

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

private theorem sepWP_pure_mid {prog : Program} {ret : BitVec 64} {s : State}
    {A B C : SepProp} {φ : Prop} {post : State → SepProp → Prop}
    (h : φ → SepWP prog ret s (A ∗ B ∗ C) post) :
    SepWP prog ret s (A ∗ B ∗ ⌜φ⌝ ∗ C) post := by
  rw [show A ∗ B ∗ ⌜φ⌝ ∗ C = ⌜φ⌝ ∗ A ∗ B ∗ C by ac_rfl]
  exact SepWP.pure_elim h

theorem try_clone_from_ref_ok_of_hooks_opt {oimg : Option Obj.Image} {A : RustAlloc}
    {b : BitVec 64} {ext : String → Option (State → State)} {hookStack : Nat}
    (hstack : hookStack + 48 ≤ 2 ^ 64 := by decide)
    (hshim : subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr tryCloneFromRefName +
        BitVec.ofNat 64 (num% (ls_off% "__rustc::__rust_no_alloc_shim_is_unstable_v2" -
          ls_off% "<alloc::boxed::Box<[u8]>>::try_clone_from_ref_in")))
      (specWithOptInv oimg (shimSpecWithStack hookStack)))
    (halloc : subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr tryCloneFromRefName +
        BitVec.ofNat 64 (num% (ls_off% "__rustc::__rust_alloc" -
          ls_off% "<alloc::boxed::Box<[u8]>>::try_clone_from_ref_in")))
      (specWithOptInv oimg (rustAllocSpecWithStack A hookStack)))
    (hmemcpy : subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr tryCloneFromRefName +
        BitVec.ofNat 64 (num% (ls_off% "memcpy" -
          ls_off% "<alloc::boxed::Box<[u8]>>::try_clone_from_ref_in")))
      (specWithOptInv oimg (memcpySpecWithStack hookStack))) :
    subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr tryCloneFromRefName)
      (specWithOptInv oimg (tryCloneFromRefSpecWithStack A hookStack)) := by
  unfold specWithOptInv
  simp only [tryCloneFromRefSpecWithStack, boxU8Buf, stackAt_tryCloneFromRef_opt hstack]
  cells_unfold
  have hfn : libsignalSessionCode.fnOff tryCloneFromRefName = num% (ls_off% "<alloc::boxed::Box<[u8]>>::try_clone_from_ref_in") :=
    (ls_lemma% fnOff "<alloc::boxed::Box<[u8]>>::try_clone_from_ref_in")
  code_fetches CryptoVerification.libsignalSessionCode
    CryptoVerification.LibsignalTripleRatchet.libsignalTripleRatchetBin b
    (Rust.withPanics ext) hfn (num% (ls_off% "<alloc::boxed::Box<[u8]>>::try_clone_from_ref_in")) 112
  wp_init x s0
  examples_generalize_entry
  examples_hide_fetches
  obtain ⟨src, bs⟩ := x
  dsimp only at *
  have hinv0 : OptCallInv oimg s0 := by assumption
  have hx1_eq : (s0.readReg64 Reg.x1).toNat = bs.length := by assumption
  have hx1_bv : s0.readReg64 Reg.x1 = BitVec.ofNat 64 bs.length := by
    apply BitVec.eq_of_toNat_eq
    rw [hx1_eq, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  by_cases hbs : bs = []
  · subst hbs
    simp only [List.length_nil, ite_true, sepConj_emp] at hx1_bv ⊢
    wp_steps
    wp_done
  · have hpos : 0 < bs.length := List.length_pos_iff.mpr hbs
    have hlen_lt63 : bs.length < 2 ^ 63 := by omega
    have hlen_ne0 : BitVec.ofNat 64 bs.length ≠ 0#64 :=
      ofNat_ne_zero_of_pos hpos (by omega)
    have hlen_beq0 : (BitVec.ofNat 64 bs.length == 0#64) = false :=
      beq_ofNat_zero_eq_false hpos (by omega)
    have hpow2 : ∃ k, 1 = 2 ^ k := ⟨0, rfl⟩
    have hbound : bs.length + 1 ≤ 2 ^ 63 := by omega
    have hlay : LayoutOk bs.length 1 := ⟨hpos, hpow2, hbound⟩
    simp only [hbs, ite_false]
    apply SepWP.seq_optImage (mid := entry + bv% (ls_off% "__rustc::__rust_no_alloc_shim_is_unstable_v2" - ls_off% "<alloc::boxed::Box<[u8]>>::try_clone_from_ref_in")) hinv0
    wp_steps
    apply SepWP.done (by rfl) (by wp_norm_lhs)
    intro hinv1
    apply SepWP.seq_optImage (mid := entry + bv% (ls_off% "__rustc::__rust_alloc" - ls_off% "<alloc::boxed::Box<[u8]>>::try_clone_from_ref_in")) hinv1
    wp_call hshim ()
    wp_steps
    apply SepWP.done (by rfl) (by wp_norm_lhs)
    intro hinv2
    apply SepWP.seq_optImage (mid := entry + bv% (44)) hinv2
    wp_call halloc (bs.length, 1)
    apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
    intro hinv3
    by_cases hoom : sf_1.readReg64 (Reg.gpr 0#5) = 0
    · have hoom64 : sf_1.readReg64 (Reg.gpr 0#5) = 0#64 := hoom
      simp only [hoom, ite_true]
      refine sepWP_pure_mid fun htrace => ?_
      wp_steps
      wp_done
    · have hoom64 : sf_1.readReg64 (Reg.gpr 0#5) ≠ 0#64 := hoom
      simp only [hoom, ite_false, sepConj_assoc]
      refine sepWP_pure_mid fun ⟨hmod, htrace⟩ => ?_
      apply SepWP.seq_optImage (mid := entry + bv% (ls_off% "memcpy" - ls_off% "<alloc::boxed::Box<[u8]>>::try_clone_from_ref_in")) hinv3
      wp_steps
      apply SepWP.done (by rfl) (by wp_norm_lhs)
      intro hinv4
      wp_call hmemcpy (sf_1.readReg64 Reg.x0, src, bs)
      wp_steps
      wp_done

theorem try_clone_from_ref_ok_ext {A : RustAlloc} {b : BitVec 64}
    {ext : String → Option (State → State)} (hA : AllocContracts b A ext) :
    subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr tryCloneFromRefName)
      (tryCloneFromRefSpec A) :=
  subroutine_ok_of_optNone <|
    try_clone_from_ref_ok_of_hooks_opt (by decide)
      (shim_opt_of_base hA (name := tryCloneFromRefName)
        (k := num% (ls_off% "__rustc::__rust_no_alloc_shim_is_unstable_v2" - ls_off% "<alloc::boxed::Box<[u8]>>::try_clone_from_ref_in")))
      (alloc_opt_of_base hA (name := tryCloneFromRefName)
        (k := num% (ls_off% "__rustc::__rust_alloc" - ls_off% "<alloc::boxed::Box<[u8]>>::try_clone_from_ref_in")))
      (memcpy_opt_of_base hA (name := tryCloneFromRefName)
        (k := num% (ls_off% "memcpy" - ls_off% "<alloc::boxed::Box<[u8]>>::try_clone_from_ref_in")))

/-- `<alloc::boxed::Box<[u8]>>::try_clone_from_ref_in` (`0xd0a0`) meets `tryCloneFromRefSpec A`
on `tripleRatchetProgAt`. -/
theorem try_clone_from_ref_ok {A : RustAlloc} {b : BitVec 64}
    {C : Crypto} {ctl : BitVec 64}
    {abs : String → Option (State → State)} (hA : AllocHooks A abs) :
    subroutine_ok (tripleRatchetProgAt b C ctl abs)
      ((tripleRatchetProgAt b C ctl abs).fnAddr tryCloneFromRefName)
      (tryCloneFromRefSpec A) :=
  try_clone_from_ref_ok_ext (AllocContracts.of_tripleRatchetProgAt b C A ctl abs hA)

theorem try_clone_from_ref_ok_ext_x {img : Obj.Image} {A : RustAlloc}
    {ext : String → Option (State → State)} (hA : AllocContractsX img A ext) :
    subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr tryCloneFromRefName)
      ((tryCloneFromRefSpecX A).inImage img) :=
  try_clone_from_ref_ok_of_hooks_opt (oimg := some img) (by decide)
    (shim_opt_of_x hA (name := tryCloneFromRefName)
      (k := num% (ls_off% "__rustc::__rust_no_alloc_shim_is_unstable_v2" - ls_off% "<alloc::boxed::Box<[u8]>>::try_clone_from_ref_in")))
    (alloc_opt_of_x hA (name := tryCloneFromRefName)
      (k := num% (ls_off% "__rustc::__rust_alloc" - ls_off% "<alloc::boxed::Box<[u8]>>::try_clone_from_ref_in")))
    (memcpy_opt_of_x hA (name := tryCloneFromRefName)
      (k := num% (ls_off% "memcpy" - ls_off% "<alloc::boxed::Box<[u8]>>::try_clone_from_ref_in")))

/-! ## Relocatable `[LibsignalPlacement]` Contract (Block `23`) -/

private theorem shimWithStack_of_noAllocShim {prog : Program} {addr : BitVec 64} (hookStack : Nat)
    (h : subroutine_ok prog addr noAllocShimSpec) :
    subroutine_ok prog addr (shimSpecWithStack hookStack) := by
  refine subroutine_ok_mono (subroutine_ok_withStack_of_subroutine_ok h hookStack)
    (fun x R s0 hpre => ?_) (fun _ _ _ _ hpost => hpost)
  dsimp only [withStack, noAllocShimSpec, shimSpecWithStack] at hpre ⊢
  simpa only [emp_sepConj, sepConj_assoc] using hpre

private theorem memcpyWithStack_of_framelessMemcpy {prog : Program} {addr : BitVec 64} (hookStack : Nat)
    (h : subroutine_ok prog addr framelessMemcpySpec) :
    subroutine_ok prog addr (memcpySpecWithStack hookStack) := by
  refine subroutine_ok_mono (subroutine_ok_withStack_of_subroutine_ok h hookStack)
    (fun x R s0 hpre => ?_) (fun x R s0 sf hpost => ?_)
  · dsimp only [withStack, framelessMemcpySpec, memcpySpecWithStack] at hpre ⊢
    simpa only [sepConj_assoc] using hpre
  · dsimp only [withStack, framelessMemcpySpec, memcpySpecWithStack] at hpost ⊢
    simpa only [sepConj_assoc] using hpost

theorem try_clone_from_ref_placed_ok_of_hooks [LibsignalPlacement] {A : RustAlloc}
    {H : String → Option (State → State)} {hookStack : Nat}
    (hstack : hookStack + 48 ≤ 2 ^ 64 := by decide)
    (hshim : subroutine_ok ((blkPC_23).rebase (blkPl_23).base H)
      (lsρ lsRustNoAllocShimSym) (shimSpecWithStack hookStack))
    (halloc : subroutine_ok ((blkPC_23).rebase (blkPl_23).base H)
      (lsρ lsRustAllocSym) (rustAllocSpecWithStack A hookStack))
    (hmemcpy : subroutine_ok ((blkPC_23).rebase (blkPl_23).base H)
      (lsρ lsMemcpySym) (memcpySpecWithStack hookStack)) :
    subroutine_ok ((blkPC_23).rebase (blkPl_23).base H) (blkPl_23).base
      (tryCloneFromRefSpecWithStack A hookStack) := by
  simp only [tryCloneFromRefSpecWithStack, boxU8Buf, stackAt_tryCloneFromRef_opt hstack]
  cells_unfold
  wp_init x s0
  obtain ⟨src, bs⟩ := x
  dsimp only at *
  have hx1_eq : (s0.readReg64 Reg.x1).toNat = bs.length := by assumption
  have hx1_bv : s0.readReg64 Reg.x1 = BitVec.ofNat 64 bs.length := by
    apply BitVec.eq_of_toNat_eq
    rw [hx1_eq, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  by_cases hbs : bs = []
  · subst hbs
    simp only [List.length_nil, ite_true, sepConj_emp] at hx1_bv ⊢
    wp_steps
    wp_done
  · have hpos : 0 < bs.length := List.length_pos_iff.mpr hbs
    have hlen_lt63 : bs.length < 2 ^ 63 := by omega
    have hlen_ne0 : BitVec.ofNat 64 bs.length ≠ 0#64 :=
      ofNat_ne_zero_of_pos hpos (by omega)
    have hlen_beq0 : (BitVec.ofNat 64 bs.length == 0#64) = false :=
      beq_ofNat_zero_eq_false hpos (by omega)
    have hpow2 : ∃ k, 1 = 2 ^ k := ⟨0, rfl⟩
    have hbound : bs.length + 1 ≤ 2 ^ 63 := by omega
    have hlay : LayoutOk bs.length 1 := ⟨hpos, hpow2, hbound⟩
    simp only [hbs, ite_false]
    wp_steps
    wp_call hshim ()
    wp_steps
    wp_call halloc (bs.length, 1)
    by_cases hoom : sf_1.readReg64 (Reg.gpr 0#5) = 0
    · have hoom64 : sf_1.readReg64 (Reg.gpr 0#5) = 0#64 := hoom
      simp only [hoom, ite_true]
      refine sepWP_pure_mid fun htrace => ?_
      wp_steps
      wp_done
    · have hoom64 : sf_1.readReg64 (Reg.gpr 0#5) ≠ 0#64 := hoom
      simp only [hoom, ite_false, sepConj_assoc]
      refine sepWP_pure_mid fun ⟨hmod, htrace⟩ => ?_
      wp_steps
      wp_call hmemcpy (sf_1.readReg64 Reg.x0, src, bs)
      wp_steps
      wp_done

/-- Relocatable `<alloc::boxed::Box<[u8]>>::try_clone_from_ref_in` (Block `23`) meets
`tryCloneFromRefSpec A`. -/
theorem try_clone_from_ref_placed_ok [LibsignalPlacement] {A : RustAlloc}
    {H : String → Option (State → State)}
    (hshim : HookSat H lsRustNoAllocShimSym noAllocShimSpec)
    (halloc : HookSat H lsRustAllocSym (rustAllocSpec A))
    (hmemcpy : HookSat H lsMemcpySym framelessMemcpySpec) :
    subroutine_ok ((blkPC_23).rebase (blkPl_23).base H) (blkPl_23).base
      (tryCloneFromRefSpec A) :=
  try_clone_from_ref_placed_ok_of_hooks (hookStack := allocHookStack) (by decide)
    (shimWithStack_of_noAllocShim allocHookStack (ls_hook_ok_of_mem hshim))
    (ls_hook_ok_of_mem halloc)
    (memcpyWithStack_of_framelessMemcpy allocHookStack (ls_hook_ok_of_mem hmemcpy))

theorem try_clone_from_ref_placed_ok_x [LibsignalPlacement] {A : RustAlloc}
    {H : String → Option (State → State)}
    (hshim : HookSat H lsRustNoAllocShimSym noAllocShimSpec)
    (halloc : HookSat H lsRustAllocSym (rustAllocSpec A))
    (hmemcpy : HookSat H lsMemcpySym framelessMemcpySpec) :
    subroutine_ok ((blkPC_23).rebase (blkPl_23).base H) (blkPl_23).base
      (tryCloneFromRefSpecX A) :=
  try_clone_from_ref_placed_ok_of_hooks (hookStack := extHookStack) (by decide)
    (shimWithStack_of_noAllocShim extHookStack (ls_hook_ok_of_mem hshim))
    (rustAllocWithStack_of_rustAlloc (ls_hook_ok_of_mem halloc) (by decide) (by decide))
    (memcpyWithStack_of_framelessMemcpy extHookStack (ls_hook_ok_of_mem hmemcpy))

end CryptoVerification.LibsignalTripleRatchet
