/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SignalSession.Cli.Main.Callees
import LibsignalBinary.Proofs.FnOffEq

/-!
# `AllocContractsFs` Call-Site Helpers

`.keepsFs` call-site wrappers for `AllocContractsFs`, together with `@[simp, arm64_norm]` `.fs`
preservation lemmas across `State.writeReg` and `setTpidrEl0`.
-/

@[expose] public section

set_option autoImplicit false

namespace CryptoVerification.SignalSession.Cli.MainHops

open Arm64 ProofLib CryptoGames.LibsignalSession CryptoVerification.RustHeap
open CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchetRepr CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalSession

@[simp, arm64_norm]
theorem fs_writeReg (s : State) (w : Width) (r : Reg) (v : BitVec 64) :
    (s.writeReg w r v).fs = s.fs := by
  cases s; cases w <;> cases r <;> rfl

@[simp, arm64_norm]
theorem fs_setTpidrEl0 (s : State) (v : BitVec 64) :
    (setTpidrEl0 s v).fs = s.fs := by
  cases s; rfl

theorem subroutine_ok_of_keepsFs {α : Type} {P : Program} {entry : BitVec 64}
    {spec : Spec α} {img : Obj.Image}
    (h : subroutine_ok P entry (spec.keepsFs.inImage img)) :
    subroutine_ok P entry (spec.inImage img) := by
  refine subroutine_ok_outcome_intro fun x R s0 hpc hrun hpre hal => ?_
  refine h.mono_outcome x R s0 hpc hrun hpre hal fun sf hout => ?_
  rcases hout with ⟨hret, hcc, hpost⟩ | hpan | hex
  · refine Or.inl ⟨hret, hcc, ?_⟩
    dsimp only [Spec.inImage, Spec.keepsFs] at hpost ⊢
    rw [sepConj_assoc, satisfies_pure_sepConj] at hpost
    exact hpost.2
  · exact Or.inr (Or.inl hpan)
  · exact Or.inr (Or.inr hex)

namespace AllocContractsFs

variable {img : Obj.Image} {A : RustAlloc} {ext : String → Option (State → State)}

theorem toAllocContractsX (hA : AllocContractsFs img A ext) : AllocContractsX img A ext where
  alloc := subroutine_ok_of_keepsFs hA.alloc
  dealloc := subroutine_ok_of_keepsFs hA.dealloc
  realloc := subroutine_ok_of_keepsFs hA.realloc
  shim stk h1 h2 := subroutine_ok_of_keepsFs (hA.shim stk h1 h2)
  memcpy stk h1 h2 := subroutine_ok_of_keepsFs (hA.memcpy stk h1 h2)
  session_memcpy stk h1 h2 := subroutine_ok_of_keepsFs (hA.session_memcpy stk h1 h2)
  memcpy_region stk h1 h2 := subroutine_ok_of_keepsFs (hA.memcpy_region stk h1 h2)
  session_memcpy_region stk h1 h2 := subroutine_ok_of_keepsFs (hA.session_memcpy_region stk h1 h2)
  memmove stk h1 h2 := subroutine_ok_of_keepsFs (hA.memmove stk h1 h2)
  session_memmove stk h1 h2 := subroutine_ok_of_keepsFs (hA.session_memmove stk h1 h2)
  memset stk h1 h2 := subroutine_ok_of_keepsFs (hA.memset stk h1 h2)
  session_memset stk h1 h2 := subroutine_ok_of_keepsFs (hA.session_memset stk h1 h2)
  memset_region stk h1 h2 := subroutine_ok_of_keepsFs (hA.memset_region stk h1 h2)
  session_memset_region stk h1 h2 := subroutine_ok_of_keepsFs (hA.session_memset_region stk h1 h2)

theorem alloc_ok_at (hA : AllocContractsFs img A ext) (name : String) (k : Nat)
    (hk : libsignalSessionCode.fnOff name + k = libsignalSessionCode.fnOff allocName := by
      fnoff_eq) :
    subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr name + BitVec.ofNat 64 k)
      ((rustAllocSpecWithStack A extHookStack).keepsFs.inImage img) :=
  sub_ok_at_of_fnAddr hA.alloc name k hk

theorem dealloc_ok_at (hA : AllocContractsFs img A ext) (name : String) (k : Nat)
    (hk : libsignalSessionCode.fnOff name + k = libsignalSessionCode.fnOff deallocName := by
      fnoff_eq) :
    subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr name + BitVec.ofNat 64 k)
      ((rustDeallocExternSpecWithStack A extHookStack).keepsFs.inImage img) :=
  sub_ok_at_of_fnAddr hA.dealloc name k hk

theorem realloc_ok_at (hA : AllocContractsFs img A ext) (name : String) (k : Nat)
    (hk : libsignalSessionCode.fnOff name + k = libsignalSessionCode.fnOff reallocName := by
      fnoff_eq) :
    subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr name + BitVec.ofNat 64 k)
      ((rustReallocExternSpecWithStack A extHookStack).keepsFs.inImage img) :=
  sub_ok_at_of_fnAddr hA.realloc name k hk

theorem shim_ok_at (hA : AllocContractsFs img A ext) (name : String) (k : Nat)
    (hookStack : Nat := extHookStack)
    (hstack : extHookStack ≤ hookStack := by decide)
    (hstack_le : hookStack ≤ 2 ^ 64 := by decide)
    (hk : libsignalSessionCode.fnOff name + k = libsignalSessionCode.fnOff shimName := by
      fnoff_eq) :
    subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr name + BitVec.ofNat 64 k)
      ((withStack sessionShimSpec hookStack).keepsFs.inImage img) :=
  sub_ok_at_of_fnAddr (hA.shim hookStack hstack hstack_le) name k hk

theorem session_shim_ok_at (hA : AllocContractsFs img A ext) (name : String) (k : Nat)
    (hookStack : Nat := extHookStack)
    (hstack : extHookStack ≤ hookStack := by decide)
    (hstack_le : hookStack ≤ 2 ^ 64 := by decide)
    (hk : libsignalSessionCode.fnOff name + k = libsignalSessionCode.fnOff shimName := by
      fnoff_eq) :
    subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr name + BitVec.ofNat 64 k)
      ((withStack sessionShimSpec hookStack).keepsFs.inImage img) :=
  sub_ok_at_of_fnAddr (hA.shim hookStack hstack hstack_le) name k hk

theorem memcpy_ok_at (hA : AllocContractsFs img A ext) (name : String) (k : Nat)
    (hookStack : Nat := extHookStack)
    (hstack : extHookStack ≤ hookStack := by decide)
    (hstack_le : hookStack ≤ 2 ^ 64 := by decide)
    (hk : libsignalSessionCode.fnOff name + k = libsignalSessionCode.fnOff memcpyName := by
      fnoff_eq) :
    subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr name + BitVec.ofNat 64 k)
      ((libcMemcpySpec hookStack).keepsFs.inImage img) :=
  sub_ok_at_of_fnAddr (hA.memcpy hookStack hstack hstack_le) name k hk

theorem session_memcpy_ok_at (hA : AllocContractsFs img A ext) (name : String) (k : Nat)
    (hookStack : Nat := extHookStack)
    (hstack : extHookStack ≤ hookStack := by decide)
    (hstack_le : hookStack ≤ 2 ^ 64 := by decide)
    (hk : libsignalSessionCode.fnOff name + k = libsignalSessionCode.fnOff memcpyName := by
      fnoff_eq) :
    subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr name + BitVec.ofNat 64 k)
      ((sessionMemcpySpec hookStack).keepsFs.inImage img) :=
  sub_ok_at_of_fnAddr (hA.session_memcpy hookStack hstack hstack_le) name k hk

theorem memcpy_region_ok_at (hA : AllocContractsFs img A ext) (name : String) (k : Nat)
    (hookStack : Nat := extHookStack)
    (hstack : extHookStack ≤ hookStack := by decide)
    (hstack_le : hookStack ≤ 2 ^ 64 := by decide)
    (hk : libsignalSessionCode.fnOff name + k = libsignalSessionCode.fnOff memcpyName := by
      fnoff_eq) :
    subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr name + BitVec.ofNat 64 k)
      ((withStack memcpyRegionSpec hookStack).keepsFs.inImage img) :=
  sub_ok_at_of_fnAddr (hA.memcpy_region hookStack hstack hstack_le) name k hk

theorem session_memcpy_region_ok_at (hA : AllocContractsFs img A ext) (name : String) (k : Nat)
    (hookStack : Nat := extHookStack)
    (hstack : extHookStack ≤ hookStack := by decide)
    (hstack_le : hookStack ≤ 2 ^ 64 := by decide)
    (hk : libsignalSessionCode.fnOff name + k = libsignalSessionCode.fnOff memcpyName := by
      fnoff_eq) :
    subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr name + BitVec.ofNat 64 k)
      ((withStack sessionMemcpyRegionSpec hookStack).keepsFs.inImage img) :=
  sub_ok_at_of_fnAddr (hA.session_memcpy_region hookStack hstack hstack_le) name k hk

theorem memmove_ok_at (hA : AllocContractsFs img A ext) (name : String) (k : Nat)
    (hookStack : Nat := extHookStack)
    (hstack : extHookStack ≤ hookStack := by decide)
    (hstack_le : hookStack ≤ 2 ^ 64 := by decide)
    (hk : libsignalSessionCode.fnOff name + k = libsignalSessionCode.fnOff memmoveName := by
      fnoff_eq) :
    subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr name + BitVec.ofNat 64 k)
      ((libcMemmoveSpec hookStack).keepsFs.inImage img) :=
  sub_ok_at_of_fnAddr (hA.memmove hookStack hstack hstack_le) name k hk

theorem session_memmove_ok_at (hA : AllocContractsFs img A ext) (name : String) (k : Nat)
    (hookStack : Nat := extHookStack)
    (hstack : extHookStack ≤ hookStack := by decide)
    (hstack_le : hookStack ≤ 2 ^ 64 := by decide)
    (hk : libsignalSessionCode.fnOff name + k = libsignalSessionCode.fnOff memmoveName := by
      fnoff_eq) :
    subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr name + BitVec.ofNat 64 k)
      ((sessionMemmoveSpec hookStack).keepsFs.inImage img) :=
  sub_ok_at_of_fnAddr (hA.session_memmove hookStack hstack hstack_le) name k hk

theorem memset_ok_at (hA : AllocContractsFs img A ext) (name : String) (k : Nat)
    (hookStack : Nat := extHookStack)
    (hstack : extHookStack ≤ hookStack := by decide)
    (hstack_le : hookStack ≤ 2 ^ 64 := by decide)
    (hk : libsignalSessionCode.fnOff name + k = libsignalSessionCode.fnOff memsetName := by
      fnoff_eq) :
    subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr name + BitVec.ofNat 64 k)
      ((libcMemsetSpec hookStack).keepsFs.inImage img) :=
  sub_ok_at_of_fnAddr (hA.memset hookStack hstack hstack_le) name k hk

theorem session_memset_ok_at (hA : AllocContractsFs img A ext) (name : String) (k : Nat)
    (hookStack : Nat := extHookStack)
    (hstack : extHookStack ≤ hookStack := by decide)
    (hstack_le : hookStack ≤ 2 ^ 64 := by decide)
    (hk : libsignalSessionCode.fnOff name + k = libsignalSessionCode.fnOff memsetName := by
      fnoff_eq) :
    subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr name + BitVec.ofNat 64 k)
      ((sessionMemsetSpec hookStack).keepsFs.inImage img) :=
  sub_ok_at_of_fnAddr (hA.session_memset hookStack hstack hstack_le) name k hk

theorem memset_region_ok_at (hA : AllocContractsFs img A ext) (name : String) (k : Nat)
    (hookStack : Nat := extHookStack)
    (hstack : extHookStack ≤ hookStack := by decide)
    (hstack_le : hookStack ≤ 2 ^ 64 := by decide)
    (hk : libsignalSessionCode.fnOff name + k = libsignalSessionCode.fnOff memsetName := by
      fnoff_eq) :
    subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr name + BitVec.ofNat 64 k)
      ((withStack memsetRegionSpec hookStack).keepsFs.inImage img) :=
  sub_ok_at_of_fnAddr (hA.memset_region hookStack hstack hstack_le) name k hk

theorem session_memset_region_ok_at (hA : AllocContractsFs img A ext) (name : String) (k : Nat)
    (hookStack : Nat := extHookStack)
    (hstack : extHookStack ≤ hookStack := by decide)
    (hstack_le : hookStack ≤ 2 ^ 64 := by decide)
    (hk : libsignalSessionCode.fnOff name + k = libsignalSessionCode.fnOff memsetName := by
      fnoff_eq) :
    subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr name + BitVec.ofNat 64 k)
      ((withStack sessionMemsetRegionSpec hookStack).keepsFs.inImage img) :=
  sub_ok_at_of_fnAddr (hA.session_memset_region hookStack hstack hstack_le) name k hk

end AllocContractsFs

/-! ## `TripleRatchet.Alloc.Defs`-style `.keepsFs` Call-Site Helpers -/

theorem shim_ok_at2_ext_xFs {img : Obj.Image} {A : RustAlloc}
    {ext : String → Option (State → State)} (hA : AllocContractsFs img A ext)
    {name : String} {k : Nat}
    (hk : libsignalSessionCode.fnOff name + k =
      libsignalSessionCode.fnOff "__rustc::__rust_no_alloc_shim_is_unstable_v2" := by
        fnoff_eq) :
    subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr name + BitVec.ofNat 64 k)
      (session2ShimSpecX.keepsFs.inImage img) := by
  have h := hA.shim_ok_at name k extHookStack (by decide) (by decide) hk
  refine subroutine_ok_outcome_intro fun x R s0 hpc hrun hpre hal => ?_
  dsimp only [Spec.inImage, Spec.keepsFs, session2ShimSpecX] at hpre
  have hpre' : s0.mem ⊨ ((withStack sessionShimSpec extHookStack).keepsFs.inImage img).pre x s0 ∗ R := by
    dsimp only [Spec.inImage, Spec.keepsFs, withStack, sessionShimSpec]
    rw [emp_sepConj]
    exact hpre
  refine h.mono_outcome x R s0 hpc hrun hpre' hal fun sf hout => ?_
  rcases hout with ⟨hret, hcc, hpost⟩ | hpan | hex
  · exact Or.inl ⟨hret, hcc, hpost⟩
  · exact Or.inr (Or.inl hpan)
  · exact Or.inr (Or.inr hex)

theorem memcpy_ok_at2_ext_xFs {img : Obj.Image} {A : RustAlloc}
    {ext : String → Option (State → State)} (hA : AllocContractsFs img A ext)
    {name : String} {k : Nat}
    (hk : libsignalSessionCode.fnOff name + k =
      libsignalSessionCode.fnOff "memcpy" := by fnoff_eq) :
    subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr name + BitVec.ofNat 64 k)
      (session2MemcpySpecX.keepsFs.inImage img) := by
  have h := hA.session_memcpy_region_ok_at name k extHookStack (by decide) (by decide) hk
  refine subroutine_ok_outcome_intro fun x R s0 hpc hrun hpre hal => ?_
  have hpre' : s0.mem ⊨ ((withStack sessionMemcpyRegionSpec extHookStack).keepsFs.inImage img).pre x s0 ∗ R := by
    dsimp only [Spec.inImage, Spec.keepsFs, withStack, sessionMemcpyRegionSpec,
      memcpyRegionSpec, session2MemcpySpecX] at hpre ⊢
    simpa only [sepConj_assoc] using hpre
  refine h.mono_outcome x R s0 hpc hrun hpre' hal fun sf hout => ?_
  rcases hout with ⟨hret, hcc, hpost⟩ | hpan | hex
  · refine Or.inl ⟨hret, hcc, ?_⟩
    dsimp only [Spec.inImage, Spec.keepsFs, withStack, sessionMemcpyRegionSpec,
      memcpyRegionSpec, session2MemcpySpecX] at hpost ⊢
    simpa only [sepConj_assoc] using hpost
  · exact Or.inr (Or.inl hpan)
  · exact Or.inr (Or.inr hex)

theorem alloc_ok_at_norm_ext_xFs {img : Obj.Image} {A : RustAlloc}
    {ext : String → Option (State → State)} (hA : AllocContractsFs img A ext)
    {name : String} {k : Nat}
    (hk : libsignalSessionCode.fnOff name + k =
      libsignalSessionCode.fnOff "__rustc::__rust_alloc" := by fnoff_eq) :
    subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr name + BitVec.ofNat 64 k)
      ((rustAllocSpecWithStack A extHookStack).keepsFs.inImage img) :=
  hA.alloc_ok_at name k hk

theorem dealloc_ok_at_norm_ext_xFs {img : Obj.Image} {A : RustAlloc}
    {ext : String → Option (State → State)} (hA : AllocContractsFs img A ext)
    {name : String} {k : Nat}
    (hk : libsignalSessionCode.fnOff name + k =
      libsignalSessionCode.fnOff "__rustc::__rust_dealloc" := by fnoff_eq) :
    subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr name + BitVec.ofNat 64 k)
      ((rustDeallocExternSpecWithStack A extHookStack).keepsFs.inImage img) :=
  hA.dealloc_ok_at name k hk

theorem realloc_ok_at_norm_ext_xFs {img : Obj.Image} {A : RustAlloc}
    {ext : String → Option (State → State)} (hA : AllocContractsFs img A ext)
    {name : String} {k : Nat}
    (hk : libsignalSessionCode.fnOff name + k =
      libsignalSessionCode.fnOff "__rustc::__rust_realloc" := by fnoff_eq) :
    subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr name + BitVec.ofNat 64 k)
      ((rustReallocExternSpecWithStack A extHookStack).keepsFs.inImage img) :=
  hA.realloc_ok_at name k hk

end CryptoVerification.SignalSession.Cli.MainHops
