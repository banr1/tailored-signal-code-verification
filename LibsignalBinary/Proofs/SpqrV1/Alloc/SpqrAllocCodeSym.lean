/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.Placed.PlacedCallSym
public import ProofLib.GenPlacedFetches
import LibsignalBinary.Proofs.Placed.BridgeReloc
import LibsignalBinary.Proofs.Placed.GenLsBlock

/-!
# Relocatable Per-Block Fetches for `SpqrV1/Alloc`

Generates per-block code symbols (`gen_ls_blk`) for SPQR V1 allocator blocks
157, 160, 218, 221, 258..260, 320, 353, 356..361, and 386.
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 2000000

namespace CryptoVerification

open Arm64 Arm64.Obj ProofLib ProofLib.ProgramReflection ProofLib.GenPlacedFetches

gen_ls_blk 157
gen_ls_blk 160
gen_ls_blk 218
gen_ls_blk 221
gen_ls_blk 258
gen_ls_blk 259
gen_ls_blk 260
gen_ls_blk 320
gen_ls_blk 353
gen_ls_blk 356
gen_ls_blk 357
gen_ls_blk 358
gen_ls_blk 359
gen_ls_blk 360
gen_ls_blk 361
gen_ls_blk 386

namespace SpqrV1.Alloc

abbrev spqrRustAllocSym : String :=
  "_RNvCs1njKG4L9aB3_7___rustc12___rust_alloc"

abbrev spqrRustReallocSym : String :=
  "_RNvCs1njKG4L9aB3_7___rustc14___rust_realloc"

abbrev spqrRustNoAllocShimSym : String :=
  "_RNvCs1njKG4L9aB3_7___rustc35___rust_no_alloc_shim_is_unstable_v2"

abbrev spqrHandleErrorSym : String :=
  "_RNvNtCs69KKACWg7bl_5alloc7raw_vec12handle_error"

abbrev spqrMemcpySym : String :=
  "memcpy"

abbrev spqrMemmoveSym : String :=
  "memmove"

abbrev spqrPanicConstAddOverflowSym : String :=
  "_RNvNtNtCskxtBwYRO61I_4core9panicking11panic_const24panic_const_add_overflow"

theorem spqr_externAt?_of_mem [LibsignalPlacement] {prog : Program} {i : Nat}
    {H : LibsignalHooks} [hprog : IsLsBlockProg prog i H]
    {sym : String} (hmem : sym ∈ libsignalSessionExterns := by decide)
    (hi : i < 619 := by decide) (hunmut : (i ∈ libsignalMutatedBlocks) = false := by decide) :
    prog.externAt? (lsρ sym) = H sym :=
  ls_externAt?_of_mem hmem hi hunmut

theorem spqr_hook_ok_of_mem [LibsignalPlacement] {α : Type} {prog : Program} {i : Nat}
    {H : LibsignalHooks} [hprog : IsLsBlockProg prog i H]
    {sym : String} {spec : Spec α} (hsat : HookSat H sym spec)
    (hmem : sym ∈ libsignalSessionExterns := by decide)
    (hi : i < 619 := by decide) (hunmut : (i ∈ libsignalMutatedBlocks) = false := by decide) :
    subroutine_ok prog (lsρ sym) spec := by
  obtain ⟨k, hk, hget⟩ := List.getElem_of_mem hmem
  exact ls_hook_ok (k := k) (by simp [hk, hget]) hsat hi hunmut

end SpqrV1.Alloc

end CryptoVerification
