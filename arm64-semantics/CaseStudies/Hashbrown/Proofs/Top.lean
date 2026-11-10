/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import CaseStudies.Hashbrown.Proofs.Simple
public import CaseStudies.Hashbrown.Proofs.WithCapacity
public import CaseStudies.Hashbrown.Proofs.Lookup
public import CaseStudies.Hashbrown.Proofs.Remove
public import CaseStudies.Hashbrown.Proofs.RehashInPlace
public import CaseStudies.Hashbrown.Proofs.ReserveRehash
public import CaseStudies.Hashbrown.Proofs.Insert

/-!
# Relocatable `hashbrown` Library Verification

Assembles unconditional `reserve_rehash` and `hashbrown_insert` contracts with the remaining
`hashbrownLib` exports into `HashbrownPlacedContracts`, proved over any `hashbrownLib.Placeable`
placement and specialized to `Arm64.Rust.GlobalAlloc`.
-/

set_option autoImplicit false

@[expose] public section

namespace CaseStudies.Hashbrown.Proofs

open Arm64 Arm64.Obj Arm64.Rust ProofLib ProofLib.StdStartup CaseStudies.Hashbrown

/-! ## Unconditional `reserve_rehash` and `hashbrown_insert` Contracts -/

theorem hashbrown_reserve_rehash_one_infallible_full_ok (P : HbPlaced) (A : HbAlloc)
    (X : String → Option (State → State) := fun _ => none)
    (hext : HbExterns ((hbProg P).rebase P.pl.base X) P.pl A) :
    let prog := (hbProg P).rebase P.pl.base X
    subroutine_ok prog (prog.fnAddr hbReserveRehashSym)
      (withCodeInv A (hashbrownReserveRehashOneInfallibleSpec P.pl A)) :=
  hashbrown_reserve_rehash_one_infallible_ok P A X hext (hbRehashInPlace_wp P A X)

theorem hashbrown_reserve_rehash_one_full_ok (P : HbPlaced) (A : HbAlloc)
    (X : String → Option (State → State) := fun _ => none)
    (hext : HbExterns ((hbProg P).rebase P.pl.base X) P.pl A) :
    let prog := (hbProg P).rebase P.pl.base X
    subroutine_ok prog (prog.fnAddr hbReserveRehashSym)
      (hashbrownLib.withCodeLoaded P.mpl (withCodeInv A (hashbrownReserveRehashOneSpec P.pl A))) :=
  hashbrown_reserve_rehash_one_ok P A X hext (hbRehashInPlace_wp P A X)

theorem hashbrown_insert_infallible_full_ok (P : HbPlaced) (A : HbAlloc)
    (X : String → Option (State → State) := fun _ => none)
    (hext0 : HbExterns ((hbProg P).rebase P.pl.base X) P.pl A) :
    let prog := (hbProg5 P).rebase P.pl5.base X
    subroutine_ok prog (prog.fnAddr "hashbrown_insert")
      (hashbrownLib.withCodeLoaded P.mpl (withCodeInv A (hashbrownInsertInfallibleSpec P.pl A))) :=
  hashbrown_insert_infallible_ok P A X
    (hashbrown_reserve_rehash_one_infallible_full_ok P A X hext0)

theorem hashbrown_insert_full_ok (P : HbPlaced) (A : HbAlloc)
    (X : String → Option (State → State) := fun _ => none)
    (hext0 : HbExterns ((hbProg P).rebase P.pl.base X) P.pl A) :
    let prog := (hbProg5 P).rebase P.pl5.base X
    subroutine_ok prog (prog.fnAddr "hashbrown_insert")
      (hashbrownLib.withCodeLoaded P.mpl (withCodeInv A (hashbrownInsertSpec P.pl A))) :=
  hashbrown_insert_ok P A X
    (hashbrown_reserve_rehash_one_infallible_full_ok P A X hext0)
    (hashbrown_reserve_rehash_one_full_ok P A X hext0)

/-! ## Placement-Family `MultiPlacedLib.subroutineOk` Contracts -/

set_option maxRecDepth 200000 in
theorem hashbrown_new_placed_ok (A : Obj.MultiPlacement → HbAlloc)
    (X : String → Option (State → State) := fun _ => none) :
    hashbrownLib.subroutineOk "hashbrown_new"
      (fun mpl => withCodeInv (A mpl) (hashbrownNewSpec (mplAsPl mpl) (A mpl))) X :=
  hbMultiSubroutineOk_of_plain "hashbrown_new" 8 (off := 0) (fun P X' => hbProg8_rebase P X')
    (fun mpl => withCodeInv (A mpl) (hashbrownNewSpec (mplAsPl mpl) (A mpl))) X
    (hok := fun P => hbPl_eq_mplAsPl P ▸ hashbrown_new_codeInv_ok P (A P.mpl) X)

set_option maxRecDepth 200000 in
theorem hashbrown_len_placed_ok (A : Obj.MultiPlacement → HbAlloc)
    (X : String → Option (State → State) := fun _ => none) :
    hashbrownLib.subroutineOk "hashbrown_len"
      (fun mpl => withCodeInv (A mpl) (hashbrownLenSpec (mplAsPl mpl) (A mpl))) X :=
  hbMultiSubroutineOk_of_plain "hashbrown_len" 7 (off := 0) (fun P X' => hbProg7_rebase P X')
    (fun mpl => withCodeInv (A mpl) (hashbrownLenSpec (mplAsPl mpl) (A mpl))) X
    (hok := fun P => hbPl_eq_mplAsPl P ▸ hashbrown_len_codeInv_ok P (A P.mpl) X)

set_option maxRecDepth 200000 in
theorem hashbrown_is_empty_placed_ok (A : Obj.MultiPlacement → HbAlloc)
    (X : String → Option (State → State) := fun _ => none) :
    hashbrownLib.subroutineOk "hashbrown_is_empty"
      (fun mpl => withCodeInv (A mpl) (hashbrownIsEmptySpec (mplAsPl mpl) (A mpl))) X :=
  hbMultiSubroutineOk_of_plain "hashbrown_is_empty" 6 (off := 0) (fun P X' => hbProg6_rebase P X')
    (fun mpl => withCodeInv (A mpl) (hashbrownIsEmptySpec (mplAsPl mpl) (A mpl))) X
    (hok := fun P => hbPl_eq_mplAsPl P ▸ hashbrown_is_empty_codeInv_ok P (A P.mpl) X)

set_option maxRecDepth 200000 in
theorem hashbrown_get_placed_ok (A : Obj.MultiPlacement → HbAlloc)
    (X : String → Option (State → State) := fun _ => none) :
    hashbrownLib.subroutineOk "hashbrown_get"
      (fun mpl => withCodeInv (A mpl) (hashbrownGetSpec (mplAsPl mpl) (A mpl))) X :=
  hbMultiSubroutineOk_of_plain "hashbrown_get" 4 (off := 0) (fun P X' => hbProg4_rebase P X')
    (fun mpl => withCodeInv (A mpl) (hashbrownGetSpec (mplAsPl mpl) (A mpl))) X
    (hok := fun P => hbPl_eq_mplAsPl P ▸ hashbrown_get_withCodeInv_ok P (A P.mpl) X)

set_option maxRecDepth 200000 in
theorem hashbrown_contains_key_placed_ok (A : Obj.MultiPlacement → HbAlloc)
    (X : String → Option (State → State) := fun _ => none) :
    hashbrownLib.subroutineOk "hashbrown_contains_key"
      (fun mpl => withCodeInv (A mpl) (hashbrownContainsKeySpec (mplAsPl mpl) (A mpl))) X :=
  hbMultiSubroutineOk_of_plain "hashbrown_contains_key" 2 (off := 0) (fun P X' => hbProg2_rebase P X')
    (fun mpl => withCodeInv (A mpl) (hashbrownContainsKeySpec (mplAsPl mpl) (A mpl))) X
    (hok := fun P => hbPl_eq_mplAsPl P ▸ hashbrown_contains_key_withCodeInv_ok P (A P.mpl) X)

set_option maxRecDepth 200000 in
theorem hashbrown_remove_placed_ok (A : Obj.MultiPlacement → HbAlloc)
    (X : String → Option (State → State) := fun _ => none) :
    hashbrownLib.subroutineOk "hashbrown_remove"
      (fun mpl => withCodeInv (A mpl) (hashbrownRemoveSpec (mplAsPl mpl) (A mpl))) X :=
  hashbrown_remove_withCodeInv_subroutineOk A X

set_option maxRecDepth 200000 in
theorem hashbrown_clear_placed_ok (A : Obj.MultiPlacement → HbAlloc)
    (X : String → Option (State → State) := fun _ => none)
    (hext : ∀ mpl, hashbrownLib.Placeable mpl → HbMultiExterns mpl X (A mpl)) :
    hashbrownLib.subroutineOk "hashbrown_clear"
      (fun mpl => withCodeInv (A mpl) (hashbrownClearSpec (mplAsPl mpl) (A mpl))) X :=
  hbMultiSubroutineOk_of_plain "hashbrown_clear" 1 (off := 0) (fun P X' => hbProg1_rebase P X')
    (fun mpl => withCodeInv (A mpl) (hashbrownClearSpec (mplAsPl mpl) (A mpl))) X
    (hok := fun P => hbPl_eq_mplAsPl P ▸ hashbrown_clear_ok P (A P.mpl) X
      (HbMultiExterns.forProg (hext P.mpl P.mplPlaceable) (by decide)
        (hbProg1_rebase P X) (hbPl1_eq P)))

set_option maxRecDepth 200000 in
theorem hashbrown_drop_placed_ok (A : Obj.MultiPlacement → HbAlloc)
    (X : String → Option (State → State) := fun _ => none)
    (hext : ∀ mpl, hashbrownLib.Placeable mpl → HbMultiExterns mpl X (A mpl)) :
    hashbrownLib.subroutineOk "hashbrown_drop"
      (fun mpl => withCodeInv (A mpl) (hashbrownDropSpec (mplAsPl mpl) (A mpl))) X :=
  hbMultiSubroutineOk_of_plain "hashbrown_drop" 3 (off := 0) (fun P X' => hbProg3_rebase P X')
    (fun mpl => withCodeInv (A mpl) (hashbrownDropSpec (mplAsPl mpl) (A mpl))) X
    (hok := fun P => hbPl_eq_mplAsPl P ▸ hashbrown_drop_ok P (A P.mpl) X
      (HbMultiExterns.forProg (hext P.mpl P.mplPlaceable) (by decide)
        (hbProg3_rebase P X) (hbPl3_eq P)))

set_option maxRecDepth 200000 in
theorem hashbrown_insert_infallible_placed_ok (A : Obj.MultiPlacement → HbAlloc)
    (X : String → Option (State → State) := fun _ => none)
    (hext : ∀ mpl, hashbrownLib.Placeable mpl → HbMultiExterns mpl X (A mpl)) :
    hashbrownLib.subroutineOk "hashbrown_insert"
      (fun mpl => withCodeInv (A mpl) (hashbrownInsertInfallibleSpec (mplAsPl mpl) (A mpl))) X :=
  hashbrown_insert_infallible_subroutineOk A X fun P =>
    hashbrown_reserve_rehash_one_infallible_full_ok P (A P.mpl) X
      (HbMultiExterns.forProg (hext P.mpl P.mplPlaceable) (by decide)
        (hbProg_rebase P X) (hbPl0_eq P))

set_option maxRecDepth 200000 in
theorem hashbrown_insert_placed_ok (A : Obj.MultiPlacement → HbAlloc)
    (X : String → Option (State → State) := fun _ => none)
    (hext : ∀ mpl, hashbrownLib.Placeable mpl → HbMultiExterns mpl X (A mpl)) :
    hashbrownLib.subroutineOk "hashbrown_insert"
      (fun mpl => withCodeInv (A mpl) (hashbrownInsertSpec (mplAsPl mpl) (A mpl))) X :=
  hashbrown_insert_subroutineOk A X
    (fun P => hashbrown_reserve_rehash_one_infallible_full_ok P (A P.mpl) X
      (HbMultiExterns.forProg (hext P.mpl P.mplPlaceable) (by decide)
        (hbProg_rebase P X) (hbPl0_eq P)))
    (fun P => hashbrown_reserve_rehash_one_full_ok P (A P.mpl) X
      (HbMultiExterns.forProg (hext P.mpl P.mplPlaceable) (by decide)
        (hbProg_rebase P X) (hbPl0_eq P)))

/-! ## Bundled Relocatable Library Contracts -/

/-- Relocatable `MultiPlacedLib.subroutineOk` contracts for all 10 `hashbrownLib` exports. -/
structure HashbrownPlacedContracts (A : Obj.MultiPlacement → HbAlloc)
    (X : String → Option (State → State) := fun _ => none) : Prop where
  new_ok :
    hashbrownLib.subroutineOk "hashbrown_new"
      (fun mpl => withCodeInv (A mpl) (hashbrownNewSpec (mplAsPl mpl) (A mpl))) X
  with_capacity_infallible_ok :
    hashbrownLib.subroutineOk "hashbrown_with_capacity"
      (fun mpl => withCodeInv (A mpl) (hashbrownWithCapacityInfallibleSpec (mplAsPl mpl) (A mpl))) X
  with_capacity_ok :
    hashbrownLib.subroutineOk "hashbrown_with_capacity"
      (fun mpl => withCodeInv (A mpl) (hashbrownWithCapacitySpec (mplAsPl mpl) (A mpl))) X
  insert_infallible_ok :
    hashbrownLib.subroutineOk "hashbrown_insert"
      (fun mpl => withCodeInv (A mpl) (hashbrownInsertInfallibleSpec (mplAsPl mpl) (A mpl))) X
  insert_ok :
    hashbrownLib.subroutineOk "hashbrown_insert"
      (fun mpl => withCodeInv (A mpl) (hashbrownInsertSpec (mplAsPl mpl) (A mpl))) X
  get_ok :
    hashbrownLib.subroutineOk "hashbrown_get"
      (fun mpl => withCodeInv (A mpl) (hashbrownGetSpec (mplAsPl mpl) (A mpl))) X
  contains_key_ok :
    hashbrownLib.subroutineOk "hashbrown_contains_key"
      (fun mpl => withCodeInv (A mpl) (hashbrownContainsKeySpec (mplAsPl mpl) (A mpl))) X
  remove_ok :
    hashbrownLib.subroutineOk "hashbrown_remove"
      (fun mpl => withCodeInv (A mpl) (hashbrownRemoveSpec (mplAsPl mpl) (A mpl))) X
  len_ok :
    hashbrownLib.subroutineOk "hashbrown_len"
      (fun mpl => withCodeInv (A mpl) (hashbrownLenSpec (mplAsPl mpl) (A mpl))) X
  is_empty_ok :
    hashbrownLib.subroutineOk "hashbrown_is_empty"
      (fun mpl => withCodeInv (A mpl) (hashbrownIsEmptySpec (mplAsPl mpl) (A mpl))) X
  clear_ok :
    hashbrownLib.subroutineOk "hashbrown_clear"
      (fun mpl => withCodeInv (A mpl) (hashbrownClearSpec (mplAsPl mpl) (A mpl))) X
  drop_ok :
    hashbrownLib.subroutineOk "hashbrown_drop"
      (fun mpl => withCodeInv (A mpl) (hashbrownDropSpec (mplAsPl mpl) (A mpl))) X

/-- Relocatable functional correctness for `hashbrownLib` over any `HbMultiExterns` realization. -/
theorem hashbrownFunctionalCorrectness_ok (A : Obj.MultiPlacement → HbAlloc)
    (X : String → Option (State → State) := fun _ => none)
    (hext : ∀ mpl, hashbrownLib.Placeable mpl → HbMultiExterns mpl X (A mpl)) :
    HashbrownPlacedContracts A X where
  new_ok                      := hashbrown_new_placed_ok A X
  with_capacity_infallible_ok := hashbrown_with_capacity_infallible_subroutineOk A X hext
  with_capacity_ok            := hashbrown_with_capacity_subroutineOk A X hext
  insert_infallible_ok        := hashbrown_insert_infallible_placed_ok A X hext
  insert_ok                   := hashbrown_insert_placed_ok A X hext
  get_ok                      := hashbrown_get_placed_ok A X
  contains_key_ok             := hashbrown_contains_key_placed_ok A X
  remove_ok                   := hashbrown_remove_placed_ok A X
  len_ok                      := hashbrown_len_placed_ok A X
  is_empty_ok                 := hashbrown_is_empty_placed_ok A X
  clear_ok                    := hashbrown_clear_placed_ok A X hext
  drop_ok                     := hashbrown_drop_placed_ok A X hext

/-- Specialization of `HashbrownPlacedContracts` to any `Arm64.Rust.GlobalAlloc` family on
    multi-placements satisfying `HbSep`. -/
theorem hashbrownGlobalAlloc_ok
    {addrs : Obj.MultiPlacement → GlobalAllocAddrs}
    {X : String → Option (State → State)}
    (G0 : ∀ mpl, GlobalAlloc (hashbrownLib.blockProgram mpl 0 X) (addrs mpl))
    (halloc_ok : ∀ mpl, hashbrownLib.Placeable mpl → ∀ i < 13,
      subroutine_ok (hashbrownLib.blockProgram mpl i X) (addrs mpl).alloc (G0 mpl).allocSpec)
    (hdealloc_ok : ∀ mpl, hashbrownLib.Placeable mpl → ∀ i < 13,
      subroutine_ok (hashbrownLib.blockProgram mpl i X) (addrs mpl).dealloc (G0 mpl).deallocSpec)
    (hsep : ∀ mpl, hashbrownLib.Placeable mpl → HbSep mpl)
    (halloc : ∀ mpl, hashbrownLib.Placeable mpl → (addrs mpl).alloc = mpl.ρ hbAllocSym)
    (hdealloc : ∀ mpl, hashbrownLib.Placeable mpl → (addrs mpl).dealloc = mpl.ρ hbDeallocSym)
    (hshim : HookSat X hbAllocShimSym hbAllocShimSpec)
    (hmemset : HookSat X hbMemsetSym stdMemsetSpec)
    (hmemmove : HookSat X hbMemmoveSym stdMemcpySpec)
    (hpan1 : X hbPanicFmtSym = some Rust.panicked)
    (hpan2 : X hbAllocErrSym = some Rust.panicked) :
    HashbrownPlacedContracts (fun mpl => HbAlloc.ofGlobalAlloc (G0 mpl)) X :=
  hashbrownFunctionalCorrectness_ok (fun mpl => HbAlloc.ofGlobalAlloc (G0 mpl)) X
    fun mpl hMpl =>
      HbMultiExterns.ofGlobalAlloc (hsep mpl hMpl) (G0 mpl)
        (halloc_ok mpl hMpl) (hdealloc_ok mpl hMpl) (halloc mpl hMpl) (hdealloc mpl hMpl)
        hshim hmemset hmemmove hpan1 hpan2

end CaseStudies.Hashbrown.Proofs
