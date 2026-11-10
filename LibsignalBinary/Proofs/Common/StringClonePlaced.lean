/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Arm64
public import ProofLib
public import ProofLib.StdStartup.MemOps
public import LibsignalBinary.Proofs.Placed.GenLsBlock
public meta import LibsignalBinary.Proofs.Placed.GenLsBlock -- shake: keep
public import LibsignalBinary.Proofs.Common.StringCloneFlat
public import LibsignalBinary.Specifications.LibsignalPublicApi
public import LibsignalBinary.Proofs.TripleRatchet.Hooks

/-!
# Placed `<String as Clone>::clone` Proofs

Placed (`lsProg_623`, Block 623) machine-code proofs for `<alloc::string::String as Clone>::clone`
satisfying `stringCloneSpec A`, lifted across blocks via `withLsCodeLoaded` and `withLsCl`.
-/

set_option autoImplicit false
set_option maxRecDepth 2000000

@[expose] public section

namespace LibsignalBinary.Proofs.Common.StringClonePlaced

open Arm64 ProofLib SepProp
open Arm64.Obj (MultiPlacement)
open ProofLib.StdStartup (hasInstrs)
open CryptoVerification
  (LibsignalHooks LibsignalPlacement LsBlockBound IsLsBlockProg lsmpl lsρ
   libsignalSessionLib libsignalSessionExterns libsignalMutatedBlocks
   withLsCodeLoaded withLsCl subroutine_ok_withLsCodeLoaded_of_plain
   ls_subroutine_ok_of_block ls_subroutine_ok_cl_of_plain
   ls_hook_ok ls_externAt?_of_blockProg
   ls_blockPlacement_ρ_extern ls_resolve_block)
open CryptoVerification.RustHeap (RustAlloc rustAllocSpec)
open CryptoVerification.LibsignalPublicApi (stringCloneSpec)
open CryptoVerification.LibsignalTripleRatchet (sessionShimSpec sessionMemcpyRegionSpec)
open LibsignalBinary.Proofs.Common.StringCloneFlat (rustStringCloneInstrs stringClone_hasInstrs_ok)

abbrev lsStringClonePlacedSym : String :=
  "<alloc::string::String as core::clone::Clone>::clone"

abbrev lsRustNoAllocShimPlacedSym : String :=
  "_RNvCs1njKG4L9aB3_7___rustc35___rust_no_alloc_shim_is_unstable_v2"

abbrev lsRustAllocPlacedSym : String :=
  "_RNvCs1njKG4L9aB3_7___rustc12___rust_alloc"

abbrev lsHandleErrorPlacedSym : String :=
  "_RNvNtCs69KKACWg7bl_5alloc7raw_vec12handle_error"

@[simp, arm64_norm, wp_norm]
theorem ls_resolve_stringClone (pl : MultiPlacement) :
    libsignalSessionLib.resolve pl
      "<alloc::string::String as core::clone::Clone>::clone" =
      pl.base 623 :=
  ls_resolve_block (by decide +kernel)

set_option maxHeartbeats 32000000 in
gen_ls_blk 623

private theorem sub_sub_eq_sub_add_bv (a b c : BitVec 64) :
    a - b - c = a - (b + c) := by
  bv_omega

local macro "close_fetch623 " h:term : tactic =>
  `(tactic| (dsimp only [Nat.reduceMul, List.getElem_cons_zero, List.getElem_cons_succ]; exact $h))

theorem lsProg_623_hasInstrs [LibsignalPlacement] (H : LibsignalHooks) :
    hasInstrs (lsProg_623 H) (lsmpl.base 623)
      (rustStringCloneInstrs
        (lsmpl.base 623)
        (lsρ lsRustNoAllocShimPlacedSym)
        (lsρ lsRustAllocPlacedSym)
        (lsρ "memcpy")
        (lsρ lsHandleErrorPlacedSym)) := by
  have hρ_shim : blkPl_623.ρ lsRustNoAllocShimPlacedSym = lsρ lsRustNoAllocShimPlacedSym :=
    ls_blockPlacement_ρ_extern (by decide)
  have hρ_alloc : blkPl_623.ρ lsRustAllocPlacedSym = lsρ lsRustAllocPlacedSym :=
    ls_blockPlacement_ρ_extern (by decide)
  have hρ_memcpy : blkPl_623.ρ "memcpy" = lsρ "memcpy" :=
    ls_blockPlacement_ρ_extern (by decide)
  have hρ_herr : blkPl_623.ρ lsHandleErrorPlacedSym = lsρ lsHandleErrorPlacedSym :=
    ls_blockPlacement_ρ_extern (by decide)
  have h8 := blkPC_623_rebase_fetch_0x20 (lsmpl.base 623) H
  rw [hρ_shim, show blkPl_623.base = lsmpl.base 623 from rfl, sub_sub_eq_sub_add_bv] at h8
  have h11 := blkPC_623_rebase_fetch_0x2c (lsmpl.base 623) H
  rw [hρ_alloc, show blkPl_623.base = lsmpl.base 623 from rfl, sub_sub_eq_sub_add_bv] at h11
  have h16 := blkPC_623_rebase_fetch_0x40 (lsmpl.base 623) H
  rw [hρ_memcpy, show blkPl_623.base = lsmpl.base 623 from rfl, sub_sub_eq_sub_add_bv] at h16
  have h32 := blkPC_623_rebase_fetch_0x80 (lsmpl.base 623) H
  rw [hρ_herr, show blkPl_623.base = lsmpl.base 623 from rfl, sub_sub_eq_sub_add_bv] at h32
  intro i hi
  dsimp only [rustStringCloneInstrs, List.length_cons, List.length_nil] at hi
  dsimp only [lsProg_623, rustStringCloneInstrs]
  change (blkPC_623.rebase (lsmpl.base 623) H).fetch (lsmpl.base 623 + BitVec.ofNat 64 (4 * i)) = _
  match i, hi with
  | 0, _ =>
    rw [show BitVec.ofNat 64 (4 * 0) = 0#64 from rfl, BitVec.add_zero]
    dsimp only [List.getElem_cons_zero]
    exact blkPC_623_rebase_fetch_base (lsmpl.base 623) H
  | 1, _ => close_fetch623 (blkPC_623_rebase_fetch_0x4 (lsmpl.base 623) H)
  | 2, _ => close_fetch623 (blkPC_623_rebase_fetch_0x8 (lsmpl.base 623) H)
  | 3, _ => close_fetch623 (blkPC_623_rebase_fetch_0xc (lsmpl.base 623) H)
  | 4, _ => close_fetch623 (blkPC_623_rebase_fetch_0x10 (lsmpl.base 623) H)
  | 5, _ => close_fetch623 (blkPC_623_rebase_fetch_0x14 (lsmpl.base 623) H)
  | 6, _ => close_fetch623 (blkPC_623_rebase_fetch_0x18 (lsmpl.base 623) H)
  | 7, _ => close_fetch623 (blkPC_623_rebase_fetch_0x1c (lsmpl.base 623) H)
  | 8, _ => close_fetch623 h8
  | 9, _ => close_fetch623 (blkPC_623_rebase_fetch_0x24 (lsmpl.base 623) H)
  | 10, _ => close_fetch623 (blkPC_623_rebase_fetch_0x28 (lsmpl.base 623) H)
  | 11, _ => close_fetch623 h11
  | 12, _ => close_fetch623 (blkPC_623_rebase_fetch_0x30 (lsmpl.base 623) H)
  | 13, _ => close_fetch623 (blkPC_623_rebase_fetch_0x34 (lsmpl.base 623) H)
  | 14, _ => close_fetch623 (blkPC_623_rebase_fetch_0x38 (lsmpl.base 623) H)
  | 15, _ => close_fetch623 (blkPC_623_rebase_fetch_0x3c (lsmpl.base 623) H)
  | 16, _ => close_fetch623 h16
  | 17, _ => close_fetch623 (blkPC_623_rebase_fetch_0x44 (lsmpl.base 623) H)
  | 18, _ => close_fetch623 (blkPC_623_rebase_fetch_0x48 (lsmpl.base 623) H)
  | 19, _ => close_fetch623 (blkPC_623_rebase_fetch_0x4c (lsmpl.base 623) H)
  | 20, _ => close_fetch623 (blkPC_623_rebase_fetch_0x50 (lsmpl.base 623) H)
  | 21, _ => close_fetch623 (blkPC_623_rebase_fetch_0x54 (lsmpl.base 623) H)
  | 22, _ => close_fetch623 (blkPC_623_rebase_fetch_0x58 (lsmpl.base 623) H)
  | 23, _ => close_fetch623 (blkPC_623_rebase_fetch_0x5c (lsmpl.base 623) H)
  | 24, _ => close_fetch623 (blkPC_623_rebase_fetch_0x60 (lsmpl.base 623) H)
  | 25, _ => close_fetch623 (blkPC_623_rebase_fetch_0x64 (lsmpl.base 623) H)
  | 26, _ => close_fetch623 (blkPC_623_rebase_fetch_0x68 (lsmpl.base 623) H)
  | 27, _ => close_fetch623 (blkPC_623_rebase_fetch_0x6c (lsmpl.base 623) H)
  | 28, _ => close_fetch623 (blkPC_623_rebase_fetch_0x70 (lsmpl.base 623) H)
  | 29, _ => close_fetch623 (blkPC_623_rebase_fetch_0x74 (lsmpl.base 623) H)
  | 30, _ => close_fetch623 (blkPC_623_rebase_fetch_0x78 (lsmpl.base 623) H)
  | 31, _ => close_fetch623 (blkPC_623_rebase_fetch_0x7c (lsmpl.base 623) H)
  | 32, _ => close_fetch623 h32
  | n + 33, hi => omega

private theorem ls_hook_ok_623 [LibsignalPlacement] {α : Type} {H : LibsignalHooks} {sym : String}
    {spec : Spec α} (hmem : sym ∈ libsignalSessionExterns := by decide) (h : HookSat H sym spec) :
    subroutine_ok (lsProg_623 H) (lsρ sym) spec := by
  obtain ⟨k, hlt, hk⟩ := List.getElem_of_mem hmem
  exact ls_hook_ok (prog := lsProg_623 H) (i := 623) (k := k)
    (by rw [List.getElem?_eq_getElem hlt, hk]) h

private theorem ls_externAt?_623 [LibsignalPlacement] {H : LibsignalHooks} {sym : String}
    (hmem : sym ∈ libsignalSessionExterns := by decide) :
    (lsProg_623 H).externAt? (lsρ sym) = H sym := by
  obtain ⟨k, hlt, hk⟩ := List.getElem_of_mem hmem
  exact ls_externAt?_of_blockProg (prog := lsProg_623 H) (i := 623) (k := k)
    (by rw [List.getElem?_eq_getElem hlt, hk])

/-- Block-623 correctness of `<String as Clone>::clone` under `HookSat` and panic-hook hypotheses. -/
theorem stringClone_blk623_ok [LibsignalPlacement] {A : RustAlloc} {H : LibsignalHooks}
    (hShim : HookSat H lsRustNoAllocShimPlacedSym sessionShimSpec)
    (hAlloc : HookSat H lsRustAllocPlacedSym (rustAllocSpec A))
    (hMemcpy : HookSat H "memcpy" sessionMemcpyRegionSpec)
    (hHandleErr : H lsHandleErrorPlacedSym = some Rust.panicked) :
    subroutine_ok (lsProg_623 H) (lsmpl.base 623) (stringCloneSpec A) :=
  stringClone_hasInstrs_ok A (lsProg_623_hasInstrs H)
    (ls_hook_ok_623 (by decide) hShim)
    (ls_hook_ok_623 (by decide) hAlloc)
    (ls_hook_ok_623 (by decide) hMemcpy)
    ((ls_externAt?_623 (sym := lsHandleErrorPlacedSym) (by decide)).trans hHandleErr)

theorem stringClone_placed_codeLoaded_ok [LibsignalPlacement] {A : RustAlloc}
    {callerProg : Program} {i : Nat} {H : LibsignalHooks} [IsLsBlockProg callerProg i H]
    (hShim : HookSat H lsRustNoAllocShimPlacedSym sessionShimSpec)
    (hAlloc : HookSat H lsRustAllocPlacedSym (rustAllocSpec A))
    (hMemcpy : HookSat H "memcpy" sessionMemcpyRegionSpec)
    (hHandleErr : H lsHandleErrorPlacedSym = some Rust.panicked)
    {bi : Nat} [LsBlockBound bi] (hi : i < bi := by decide) :
    subroutine_ok callerProg (lsmpl.base 623) (withLsCodeLoaded lsmpl (stringCloneSpec A)) :=
  ls_subroutine_ok_of_block (callerProg := callerProg)
    (subroutine_ok_withLsCodeLoaded_of_plain (stringClone_blk623_ok hShim hAlloc hMemcpy hHandleErr))
    hi (by decide) (by decide)

theorem stringClone_placed_cl_ok [LibsignalPlacement] {A : RustAlloc}
    {callerProg : Program} {i : Nat} {H : LibsignalHooks} [IsLsBlockProg callerProg i H]
    (hShim : HookSat H lsRustNoAllocShimPlacedSym sessionShimSpec)
    (hAlloc : HookSat H lsRustAllocPlacedSym (rustAllocSpec A))
    (hMemcpy : HookSat H "memcpy" sessionMemcpyRegionSpec)
    (hHandleErr : H lsHandleErrorPlacedSym = some Rust.panicked)
    {bi : Nat} [LsBlockBound bi] (hi : i < bi := by decide) :
    subroutine_ok callerProg (lsmpl.base 623) (withLsCl lsmpl (stringCloneSpec A)) :=
  ls_subroutine_ok_cl_of_plain (callerProg := callerProg)
    (stringClone_blk623_ok hShim hAlloc hMemcpy hHandleErr)
    hi (by decide) (by decide)

theorem stringClone_blk623_panics_ok [LibsignalPlacement] {A : RustAlloc} {hooks : LibsignalHooks}
    (hShim : HookSat hooks lsRustNoAllocShimPlacedSym sessionShimSpec)
    (hAlloc : HookSat hooks lsRustAllocPlacedSym (rustAllocSpec A))
    (hMemcpy : HookSat hooks "memcpy" sessionMemcpyRegionSpec)
    (hHandleErr : hooks lsHandleErrorPlacedSym = some Rust.panicked) :
    subroutine_ok (lsProg_623 (Rust.withPanics hooks)) (lsmpl.base 623) (stringCloneSpec A) := by
  refine stringClone_blk623_ok ?_ ?_ ?_ ?_
  · obtain ⟨f, hf, hok⟩ := hShim
    have hnp : Rust.isPanicSymbol lsRustNoAllocShimPlacedSym = false := by
      simp [lsRustNoAllocShimPlacedSym, Rust.isPanicSymbol]
    exact ⟨f, by simp [Rust.withPanics, hnp, hf], hok⟩
  · obtain ⟨f, hf, hok⟩ := hAlloc
    have hnp : Rust.isPanicSymbol lsRustAllocPlacedSym = false := by
      simp [lsRustAllocPlacedSym, Rust.isPanicSymbol]
    exact ⟨f, by simp [Rust.withPanics, hnp, hf], hok⟩
  · obtain ⟨f, hf, hok⟩ := hMemcpy
    have hnp : Rust.isPanicSymbol "memcpy" = false := by simp [Rust.isPanicSymbol]
    exact ⟨f, by simp [Rust.withPanics, hnp, hf], hok⟩
  · have hnp : Rust.isPanicSymbol lsHandleErrorPlacedSym = false := by
      simp [lsHandleErrorPlacedSym, Rust.isPanicSymbol]
    simp [Rust.withPanics, hnp, hHandleErr]

theorem stringClone_placed_panics_codeLoaded_ok [LibsignalPlacement] {A : RustAlloc}
    {callerProg : Program} {i : Nat} {hooks : LibsignalHooks}
    [IsLsBlockProg callerProg i (Rust.withPanics hooks)]
    (hShim : HookSat hooks lsRustNoAllocShimPlacedSym sessionShimSpec)
    (hAlloc : HookSat hooks lsRustAllocPlacedSym (rustAllocSpec A))
    (hMemcpy : HookSat hooks "memcpy" sessionMemcpyRegionSpec)
    (hHandleErr : hooks lsHandleErrorPlacedSym = some Rust.panicked)
    {bi : Nat} [LsBlockBound bi] (hi : i < bi := by decide) :
    subroutine_ok callerProg (lsmpl.base 623) (withLsCodeLoaded lsmpl (stringCloneSpec A)) :=
  ls_subroutine_ok_of_block (callerProg := callerProg)
    (subroutine_ok_withLsCodeLoaded_of_plain
      (stringClone_blk623_panics_ok hShim hAlloc hMemcpy hHandleErr))
    hi (by decide) (by decide)

theorem stringClone_placed_panics_cl_ok [LibsignalPlacement] {A : RustAlloc}
    {callerProg : Program} {i : Nat} {hooks : LibsignalHooks}
    [IsLsBlockProg callerProg i (Rust.withPanics hooks)]
    (hShim : HookSat hooks lsRustNoAllocShimPlacedSym sessionShimSpec)
    (hAlloc : HookSat hooks lsRustAllocPlacedSym (rustAllocSpec A))
    (hMemcpy : HookSat hooks "memcpy" sessionMemcpyRegionSpec)
    (hHandleErr : hooks lsHandleErrorPlacedSym = some Rust.panicked)
    {bi : Nat} [LsBlockBound bi] (hi : i < bi := by decide) :
    subroutine_ok callerProg (lsmpl.base 623) (withLsCl lsmpl (stringCloneSpec A)) :=
  ls_subroutine_ok_cl_of_plain (callerProg := callerProg)
    (stringClone_blk623_panics_ok hShim hAlloc hMemcpy hHandleErr)
    hi (by decide) (by decide)

end LibsignalBinary.Proofs.Common.StringClonePlaced
