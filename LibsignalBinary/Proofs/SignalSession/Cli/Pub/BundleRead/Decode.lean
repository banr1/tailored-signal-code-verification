/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SignalSession.Cli.PublicSpecs
public import LibsignalBinary.Proofs.CodeLayout
import all Init.Data.String.Defs
import all Init.Data.String.Pattern.Basic
import all Init.Data.String.Pattern.String
import all Init.Data.String.Slice
import all Init.Data.String.TakeDrop
public import GeneratedLean.LibsignalSessionCode -- shake: keep
public import LibsignalBinary.Proofs.SignalSession.Cli.Specs
import ProofLib.SepLogic.WP.Access

@[expose] public section

set_option autoImplicit false

namespace CryptoVerification.SignalSession.Cli.BundleRead.Helpers

open Arm64 ProofLib ProofLib.ProgramReflection
open CryptoGames.LibsignalSession CryptoVerification.RustHeap
open CryptoVerification.LibsignalTripleRatchetRepr CryptoVerification.LibsignalTripleRatchet

/-! ## Instruction Decode and Rebase Fetch Lemmas -/

gen_decodes libsignalSessionCode_tree bundleReadBin [
  (ls_off% bundleReadName) → (ls_off% bundleReadName + 208)
]

@[scoped simp, scoped arm64_norm] gen_rebase_fetches libsignalSessionCode bundleRead [
  (ls_off% bundleReadName) → (ls_off% bundleReadName + 208)
]

/-! ## `.rodata` String Literal Lemmas -/

theorem img_data_len_ge {n : Nat} (h : n ≤ num% (ls_field% dataLen)) :
    n ≤ libsignalSessionImage.data.length :=
  Nat.le_trans h (Nat.le_of_ble_eq_true (by rfl_kernel))

theorem rodata_unreadable_bytes_eq :
    (libsignalSessionImage.data.drop
      (num% (ls_xref% (ls_off% bundleReadName + 132) (ls_off% bundleReadName + 136)) -
        num% (ls_field% dataOff))).take 22 =
      utf8 "file could not be read" := by
  rfl_kernel

theorem rodata_unreadable_intro {img : Obj.Image} (himg : Obj.Loads libsignalSessionImage img)
    {m : Memory} {P : SepProp} (hro : img.RoDataLoaded m) (hP : m ⊨ P) :
    m ⊨ ((img.base + bv% (ls_xref% (ls_off% bundleReadName + 132) (ls_off% bundleReadName + 136)))
      ↦ᵣ utf8 "file could not be read") ∗ P := by
  rw [← rodata_unreadable_bytes_eq]
  exact ProofLib.Satisfies.of_rodata_loads himg
    (dataOff := num% (ls_field% dataOff)) rfl
    (List.mem_of_elem_eq_true (by rfl_kernel)) (by decide) (by decide)
    (img_data_len_ge (by decide)) (by rfl_kernel) hro hP

theorem rodata_read_sec_eq :
    (libsignalSessionImage.data.drop
      (num% (ls_xref% (ls_off% bundleReadName + 176) (ls_off% bundleReadName + 180) - 12) -
        num% (ls_field% dataOff))).take 16 =
      ((libsignalSessionImage.data.drop
        (num% (ls_xref% (ls_off% bundleReadName + 176) (ls_off% bundleReadName + 180) - 12) -
          num% (ls_field% dataOff))).take 12) ++ utf8 "read" := by
  rfl_kernel

theorem rodata_read_intro {img : Obj.Image} (himg : Obj.Loads libsignalSessionImage img)
    {m : Memory} {P : SepProp} (hro : img.RoDataLoaded m) (hP : m ⊨ P) :
    m ⊨ ((img.base + bv% (ls_xref% (ls_off% bundleReadName + 176) (ls_off% bundleReadName + 180)))
      ↦ᵣ utf8 "read") ∗ P := by
  have hfull := ProofLib.Satisfies.of_rodata_loads himg
    (dataOff := num% (ls_field% dataOff)) rfl
    (secOff := num% (ls_xref% (ls_off% bundleReadName + 176) (ls_off% bundleReadName + 180) - 12))
    (secLen := 16)
    (List.mem_of_elem_eq_true (by rfl_kernel)) (by decide) (by decide)
    (img_data_len_ge (by decide)) (by rfl_kernel) hro hP
  rw [rodata_read_sec_eq, pointsToBytesRO_append] at hfull
  have hge := img_data_len_ge (n := num% (ls_xref% (ls_off% bundleReadName + 176)
      (ls_off% bundleReadName + 180) - 12) - num% (ls_field% dataOff) + 12) (by decide)
  have hlen : ((libsignalSessionImage.data.drop
      (num% (ls_xref% (ls_off% bundleReadName + 176) (ls_off% bundleReadName + 180) - 12) -
        num% (ls_field% dataOff))).take 12).length = 12 :=
    List.length_take_of_le (by rw [List.length_drop]; omega)
  rw [hlen, BitVec.add_assoc] at hfull
  have hmid : m ⊨ emp ∗ ((img.base + bv% (ls_xref% (ls_off% bundleReadName + 176) (ls_off% bundleReadName + 180) - 12))
      ↦ᵣ (libsignalSessionImage.data.drop
        (num% (ls_xref% (ls_off% bundleReadName + 176) (ls_off% bundleReadName + 180) - 12) -
          num% (ls_field% dataOff))).take 12) ∗
      (((img.base + bv% (ls_xref% (ls_off% bundleReadName + 176) (ls_off% bundleReadName + 180)))
        ↦ᵣ utf8 "read") ∗ P) := by
    simpa [emp_sepConj, sepConj_assoc] using hfull
  simpa [emp_sepConj] using Satisfies.drop_mid hmid

/-! ## `adrp` Page-Alignment Lemmas -/

theorem adrp_unreadable_page {b : BitVec 64} {H : String → Option (State → State)}
    (hb : (b &&& 0xfff#64) = 0#64) :
    (((libsignalSessionCode.rebase b H).fnAddr bundleReadName + bv% (132)) &&&
      0xfffffffffffff000#64) =
      b + bv% (page% (ls_off% bundleReadName + 132)) := by
  rw [Program.fnAddr_rebase, bundleRead_fnOff, BitVec.add_assoc, adrp_page_of_aligned hb]
  rfl

theorem adrp_read_page {b : BitVec 64} {H : String → Option (State → State)}
    (hb : (b &&& 0xfff#64) = 0#64) :
    (((libsignalSessionCode.rebase b H).fnAddr bundleReadName + bv% (176)) &&&
      0xfffffffffffff000#64) =
      b + bv% (page% (ls_off% bundleReadName + 176)) := by
  rw [Program.fnAddr_rebase, bundleRead_fnOff, BitVec.add_assoc, adrp_page_of_aligned hb]
  rfl

/-! ## Call-Target and Panic-Stub Resolution Lemmas -/

theorem path_addr_eq (b : BitVec 64) (ext : String → Option (State → State)) :
    (tripleRatchetProgAtExt b ext).fnAddr bundleReadName +
      bv% (ls_rel% bundleReadName pathName) =
      (tripleRatchetProgAtExt b ext).fnAddr pathName := by
  have hk : BitVec.ofNat 64 (libsignalSessionCode.fnOff bundleReadName) +
      bv% (ls_rel% bundleReadName pathName) =
      BitVec.ofNat 64 (libsignalSessionCode.fnOff pathName) := by
    rw [bundleRead_fnOff, path_fnOff]; rfl
  simp only [tripleRatchetProgAtExt, Program.fnAddr_rebase, BitVec.add_assoc, hk]

theorem shim_ok_at_bundleRead {img : Obj.Image} {A : RustAlloc}
    {ext : String → Option (State → State)}
    (hC : AllocContractsX img A ext) (hookStack : Nat)
    (hstack : extHookStack ≤ hookStack) (hstack_le : hookStack ≤ 2 ^ 64) :
    subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr bundleReadName +
        bv% (ls_rel% bundleReadName "__rustc::__rust_no_alloc_shim_is_unstable_v2"))
      ((withStack sessionShimSpec hookStack).inImage img) :=
  AllocContractsX.shim_ok_at hC bundleReadName
    (num% (ls_rel% bundleReadName "__rustc::__rust_no_alloc_shim_is_unstable_v2"))
    hookStack hstack hstack_le (by rw [bundleRead_fnOff]; simp only [arm64_norm])

theorem alloc_ok_at_bundleRead {img : Obj.Image} {A : RustAlloc}
    {ext : String → Option (State → State)}
    (hC : AllocContractsX img A ext) :
    subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr bundleReadName +
        bv% (ls_rel% bundleReadName "__rustc::__rust_alloc"))
      ((rustAllocSpecWithStack A extHookStack).inImage img) :=
  AllocContractsX.alloc_ok_at hC bundleReadName
    (num% (ls_rel% bundleReadName "__rustc::__rust_alloc"))
    (by rw [bundleRead_fnOff]; simp only [arm64_norm])

theorem dealloc_ok_at_bundleRead {img : Obj.Image} {A : RustAlloc}
    {ext : String → Option (State → State)}
    (hC : AllocContractsX img A ext) :
    subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr bundleReadName +
        bv% (ls_rel% bundleReadName "__rustc::__rust_dealloc"))
      ((rustDeallocExternSpecWithStack A extHookStack).inImage img) :=
  AllocContractsX.dealloc_ok_at hC bundleReadName
    (num% (ls_rel% bundleReadName "__rustc::__rust_dealloc"))
    (by rw [bundleRead_fnOff]; simp only [arm64_norm])

theorem panic_at_handle_error_bundleRead (b : BitVec 64)
    (ext : String → Option (State → State)) :
    (tripleRatchetProgAtExt b ext).externAt?
      ((tripleRatchetProgAtExt b ext).fnAddr bundleReadName +
        bv% (ls_rel% bundleReadName "alloc::raw_vec::handle_error")) =
      some Rust.panicked := by
  have h : Rust.isPanicSymbol "alloc::raw_vec::handle_error" = true := by rfl_kernel
  exact (Program.externAt?_fnAddr_add
      (stub := num% (ls_off% "alloc::raw_vec::handle_error"))
      bundleRead_fnOff (by rfl) (by decide)).trans
    (((ls_hook% "alloc::raw_vec::handle_error") (Rust.withPanics ext)).trans
      (by simp [Rust.withPanics, h]))

end CryptoVerification.SignalSession.Cli.BundleRead.Helpers
