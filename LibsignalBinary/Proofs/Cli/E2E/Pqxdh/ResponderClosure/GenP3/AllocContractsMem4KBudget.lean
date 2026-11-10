/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.GenP3.AllocContractsMem4K
public import LibsignalBinary.Proofs.TripleRatchet.Alloc.DefsBudget
public import LibsignalBinary.Proofs.TripleRatchet.Hooks.DefsBudget
public import LibsignalBinary.Proofs.TripleRatchet.Hooks2Budget
public import LibsignalBinary.Heap.IfaceBudgetBase
import GeneratedLean.LibsignalSessionCode -- shake: keep
import LibsignalBinary.Proofs.CodeLayout
import LibsignalBinary.Proofs.FnOffEq
import ProofLib.SepLogic.WP.StateNorm

@[expose] public section

set_option autoImplicit false
set_option linter.dupNamespace false

/-!
# Budget-Threaded 4K-Stack Extern Contract Bundle (`AllocContractsMem4KBudget`)

`subroutine_ok` contracts on `tripleRatchetProgAtExt b ext` for `rustCliAllocBudgetSpec`,
`rustCliDeallocBudgetSpec`, `rustCliReallocBudgetSpec`, `sessionShimBudgetSpec`, and
4096-byte-stack `sessionMemcpyBudgetSpec` / `sessionMemmoveBudgetSpec` /
`sessionMemsetBudgetSpec` (`allocHookStack = 4096`), matching `CliExternsBudgetOk`.
-/

namespace LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.GenP3.AllocContractsMem4KBudget

open Arm64 ProofLib ProofLib.ProgramReflection
open CryptoVerification (libsignalSessionCode)
open CryptoVerification.RustHeap (allocHookStack)
open CryptoVerification.LibsignalTripleRatchet
  (allocName deallocName reallocName shimName memcpyName memmoveName memsetName
   tripleRatchetProgAtExt sub_ok_at_of_fnAddr)
open LibsignalBinary.Heap
  (AllocCostModel BudgetLimits RustCliAllocBudget
   rustCliAllocBudgetSpecBase rustCliAllocNoOomSpecBase
   rustCliDeallocBudgetSpecBase rustCliDeallocNoOomSpecBase
   rustCliReallocBudgetSpecBase rustCliReallocNoOomSpecBase
   subroutine_ok_allocNoOom_of_budgetBase subroutine_ok_reallocNoOom_of_budgetBase)
open LibsignalBinary.Heap.SpecBudget (AllocHooksBudgetBase)
open LibsignalBinary.Proofs.TripleRatchet.Hooks.DefsBudget
  (sessionShimBudgetSpec sessionMemcpyBudgetSpec sessionMemmoveBudgetSpec sessionMemsetBudgetSpec)
open LibsignalBinary.Proofs.TripleRatchet.Alloc.DefsBudget
  (AllocContractsBudget noAllocShimBudgetSpec subroutine_ok_noAllocShim_of_sessionShimBudget)

/-- Budget-threaded `subroutine_ok` contracts on `tripleRatchetProgAtExt b ext` for the Rust
allocator (`alloc`, `dealloc`, `realloc`), `shim`, and 4096-byte-stack `memcpy` / `memmove` /
`memset` (`allocHookStack = 4096`), matching `CliExternsBudgetOk` directly. -/
structure AllocContractsMem4KBudget (b : BitVec 64) (M : AllocCostModel)
    (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (ext : String → Option (State → State)) : Prop where
  alloc :
    subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr allocName) (rustCliAllocBudgetSpecBase M A lim false)
  dealloc :
    subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr deallocName) (rustCliDeallocBudgetSpecBase M A lim)
  realloc :
    subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr reallocName) (rustCliReallocBudgetSpecBase M A lim)
  shim :
    subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr shimName) sessionShimBudgetSpec
  session_memcpy :
    subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr memcpyName) (sessionMemcpyBudgetSpec allocHookStack)
  session_memmove :
    subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr memmoveName) (sessionMemmoveBudgetSpec allocHookStack)
  session_memset :
    subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr memsetName) (sessionMemsetBudgetSpec allocHookStack)

abbrev AllocContractsMem4K := @AllocContractsMem4KBudget

namespace AllocContractsMem4KBudget

variable {b : BitVec 64} {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
  {ext : String → Option (State → State)}

theorem allocNoOom (hA : AllocContractsMem4KBudget b M A lim ext) :
    subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr allocName) (rustCliAllocNoOomSpecBase M A lim false) :=
  subroutine_ok_allocNoOom_of_budgetBase hA.alloc

theorem deallocNoOom (hA : AllocContractsMem4KBudget b M A lim ext) :
    subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr deallocName) (rustCliDeallocNoOomSpecBase M A lim) :=
  hA.dealloc

theorem reallocNoOom (hA : AllocContractsMem4KBudget b M A lim ext) :
    subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr reallocName) (rustCliReallocNoOomSpecBase M A lim) :=
  subroutine_ok_reallocNoOom_of_budgetBase hA.realloc

theorem alloc_ok_at (hA : AllocContractsMem4KBudget b M A lim ext) (name : String) (k : Nat)
    (hk : libsignalSessionCode.fnOff name + k = libsignalSessionCode.fnOff allocName := by
      fnoff_eq) :
    subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr name + BitVec.ofNat 64 k)
      (rustCliAllocBudgetSpecBase M A lim false) :=
  sub_ok_at_of_fnAddr (b := b) (ext := ext) (sym := allocName) hA.alloc name k hk

theorem allocNoOom_ok_at (hA : AllocContractsMem4KBudget b M A lim ext) (name : String) (k : Nat)
    (hk : libsignalSessionCode.fnOff name + k = libsignalSessionCode.fnOff allocName := by
      fnoff_eq) :
    subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr name + BitVec.ofNat 64 k)
      (rustCliAllocNoOomSpecBase M A lim false) :=
  sub_ok_at_of_fnAddr (b := b) (ext := ext) (sym := allocName) hA.allocNoOom name k hk

theorem dealloc_ok_at (hA : AllocContractsMem4KBudget b M A lim ext) (name : String) (k : Nat)
    (hk : libsignalSessionCode.fnOff name + k = libsignalSessionCode.fnOff deallocName := by
      fnoff_eq) :
    subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr name + BitVec.ofNat 64 k)
      (rustCliDeallocBudgetSpecBase M A lim) :=
  sub_ok_at_of_fnAddr (b := b) (ext := ext) (sym := deallocName) hA.dealloc name k hk

theorem realloc_ok_at (hA : AllocContractsMem4KBudget b M A lim ext) (name : String) (k : Nat)
    (hk : libsignalSessionCode.fnOff name + k = libsignalSessionCode.fnOff reallocName := by
      fnoff_eq) :
    subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr name + BitVec.ofNat 64 k)
      (rustCliReallocBudgetSpecBase M A lim) :=
  sub_ok_at_of_fnAddr (b := b) (ext := ext) (sym := reallocName) hA.realloc name k hk

theorem reallocNoOom_ok_at (hA : AllocContractsMem4KBudget b M A lim ext) (name : String) (k : Nat)
    (hk : libsignalSessionCode.fnOff name + k = libsignalSessionCode.fnOff reallocName := by
      fnoff_eq) :
    subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr name + BitVec.ofNat 64 k)
      (rustCliReallocNoOomSpecBase M A lim) :=
  sub_ok_at_of_fnAddr (b := b) (ext := ext) (sym := reallocName) hA.reallocNoOom name k hk

theorem shim_ok_at (hA : AllocContractsMem4KBudget b M A lim ext) (name : String) (k : Nat)
    (hk : libsignalSessionCode.fnOff name + k = libsignalSessionCode.fnOff shimName := by
      fnoff_eq) :
    subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr name + BitVec.ofNat 64 k)
      sessionShimBudgetSpec :=
  sub_ok_at_of_fnAddr (b := b) (ext := ext) (sym := shimName) hA.shim name k hk

theorem noAllocShim_ok_at (hA : AllocContractsMem4KBudget b M A lim ext) (name : String) (k : Nat)
    (hk : libsignalSessionCode.fnOff name + k = libsignalSessionCode.fnOff shimName := by
      fnoff_eq) :
    subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr name + BitVec.ofNat 64 k)
      noAllocShimBudgetSpec :=
  sub_ok_at_of_fnAddr (b := b) (ext := ext) (sym := shimName)
    (subroutine_ok_noAllocShim_of_sessionShimBudget hA.shim) name k hk

theorem session_shim_ok_at (hA : AllocContractsMem4KBudget b M A lim ext) (name : String) (k : Nat)
    (hk : libsignalSessionCode.fnOff name + k = libsignalSessionCode.fnOff shimName := by
      fnoff_eq) :
    subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr name + BitVec.ofNat 64 k)
      sessionShimBudgetSpec :=
  sub_ok_at_of_fnAddr (b := b) (ext := ext) (sym := shimName) hA.shim name k hk

theorem session_memcpy_ok_at (hA : AllocContractsMem4KBudget b M A lim ext) (name : String)
    (k : Nat)
    (hk : libsignalSessionCode.fnOff name + k = libsignalSessionCode.fnOff memcpyName := by
      fnoff_eq) :
    subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr name + BitVec.ofNat 64 k)
      (sessionMemcpyBudgetSpec allocHookStack) :=
  sub_ok_at_of_fnAddr (b := b) (ext := ext) (sym := memcpyName) hA.session_memcpy name k hk

theorem session_memmove_ok_at (hA : AllocContractsMem4KBudget b M A lim ext) (name : String)
    (k : Nat)
    (hk : libsignalSessionCode.fnOff name + k = libsignalSessionCode.fnOff memmoveName := by
      fnoff_eq) :
    subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr name + BitVec.ofNat 64 k)
      (sessionMemmoveBudgetSpec allocHookStack) :=
  sub_ok_at_of_fnAddr (b := b) (ext := ext) (sym := memmoveName) hA.session_memmove name k hk

theorem session_memset_ok_at (hA : AllocContractsMem4KBudget b M A lim ext) (name : String)
    (k : Nat)
    (hk : libsignalSessionCode.fnOff name + k = libsignalSessionCode.fnOff memsetName := by
      fnoff_eq) :
    subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr name + BitVec.ofNat 64 k)
      (sessionMemsetBudgetSpec allocHookStack) :=
  sub_ok_at_of_fnAddr (b := b) (ext := ext) (sym := memsetName) hA.session_memset name k hk

/-- Every `AllocContractsBudget b M A lim ext` trivially implies
`AllocContractsMem4KBudget b M A lim ext`. -/
theorem of_AllocContracts (hA : AllocContractsBudget b M A lim ext) :
    AllocContractsMem4KBudget b M A lim ext where
  alloc := hA.alloc
  dealloc := hA.dealloc
  realloc := hA.realloc
  shim := hA.shim
  session_memcpy := hA.session_memcpy allocHookStack
  session_memmove := hA.session_memmove allocHookStack
  session_memset := hA.session_memset allocHookStack (by decide)

section HookHelpers

attribute [local irreducible] Program.fetch Program.externAt? Program.fnOff

ls_attribute [local simp, local arm64_norm ↓]
  (ls_stub% "__rustc::__rust_alloc") (ls_stub% "__rustc::__rust_dealloc")
  (ls_stub% "__rustc::__rust_realloc") (ls_stub% "__rustc::__rust_no_alloc_shim_is_unstable_v2")
  (ls_stub% "memcpy") (ls_stub% "memmove") (ls_stub% "memset")

private theorem sub_ok_fnAddr_of_hookSat {α : Type} (b : BitVec 64)
    (ext : String → Option (State → State)) (name : String) (spec : Spec α)
    (hs : libsignalSessionCode.fnOff name < 2 ^ 64)
    (hstub : ∀ X, (libsignalSessionCode.rebase 0 X).hookAtOff? (libsignalSessionCode.fnOff name) = X name)
    (hnp : Rust.isPanicSymbol name = false)
    (hsat : HookSat ext name spec) :
    subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr name) spec := by
  simpa only [BitVec.ofNat_eq_ofNat, BitVec.add_zero] using
    hook_ok_at (P := libsignalSessionCode) (hname := name) rfl (Nat.add_zero _) hs hstub hnp hsat

/-- Construct `AllocContractsMem4KBudget b M A lim ext` directly from `AllocHooksBudget M A lim ext`
and `HookSat` hypotheses for `shim`, `memcpy`, `memmove`, and `memset` at `allocHookStack` (`= 4096`),
matching `CliExternsBudgetOk`. -/
theorem of_hooks (b : BitVec 64) (M : AllocCostModel) (A : RustCliAllocBudget M)
    (lim : BudgetLimits) (ext : String → Option (State → State))
    (hAlloc : AllocHooksBudgetBase M A lim ext)
    (hShim : HookSat ext shimName sessionShimBudgetSpec)
    (hMemcpy : HookSat ext memcpyName (sessionMemcpyBudgetSpec allocHookStack))
    (hMemmove : HookSat ext memmoveName (sessionMemmoveBudgetSpec allocHookStack))
    (hMemset : HookSat ext memsetName (sessionMemsetBudgetSpec allocHookStack)) :
    AllocContractsMem4KBudget b M A lim ext where
  alloc := sub_ok_fnAddr_of_hookSat b ext allocName _ (by simp only [arm64_norm])
    (fun _ => by simp only [arm64_norm]) (by simp [Rust.isPanicSymbol, allocName]) hAlloc.alloc
  dealloc := sub_ok_fnAddr_of_hookSat b ext deallocName _ (by simp only [arm64_norm])
    (fun _ => by simp only [arm64_norm]) (by simp [Rust.isPanicSymbol, deallocName]) hAlloc.dealloc
  realloc := sub_ok_fnAddr_of_hookSat b ext reallocName _ (by simp only [arm64_norm])
    (fun _ => by simp only [arm64_norm]) (by simp [Rust.isPanicSymbol, reallocName]) hAlloc.realloc
  shim := sub_ok_fnAddr_of_hookSat b ext shimName _ (by simp only [arm64_norm])
    (fun _ => by simp only [arm64_norm]) (by simp [Rust.isPanicSymbol, shimName]) hShim
  session_memcpy := sub_ok_fnAddr_of_hookSat b ext memcpyName _ (by simp only [arm64_norm])
    (fun _ => by simp only [arm64_norm]) (by simp [Rust.isPanicSymbol, memcpyName]) hMemcpy
  session_memmove := sub_ok_fnAddr_of_hookSat b ext memmoveName _ (by simp only [arm64_norm])
    (fun _ => by simp only [arm64_norm]) (by simp [Rust.isPanicSymbol, memmoveName]) hMemmove
  session_memset := sub_ok_fnAddr_of_hookSat b ext memsetName _ (by simp only [arm64_norm])
    (fun _ => by simp only [arm64_norm]) (by simp [Rust.isPanicSymbol, memsetName]) hMemset

end HookHelpers

end AllocContractsMem4KBudget

section StandaloneDeallocHook

attribute [local irreducible] Program.fetch Program.externAt? Program.fnOff

ls_attribute [local simp, local arm64_norm ↓] (ls_stub% "__rustc::__rust_dealloc")

theorem dealloc_ok_at_ext (b : BitVec 64) (M : AllocCostModel) (A : RustCliAllocBudget M)
    (lim : BudgetLimits) (ext : String → Option (State → State))
    (hDealloc : HookSat ext deallocName (rustCliDeallocBudgetSpecBase M A lim))
    (name : String) (k : Nat)
    (hk : libsignalSessionCode.fnOff name + k = libsignalSessionCode.fnOff deallocName := by
      fnoff_eq) :
    subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr name + BitVec.ofNat 64 k)
      (rustCliDeallocBudgetSpecBase M A lim) := by
  have hfn : subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr deallocName)
      (rustCliDeallocBudgetSpecBase M A lim) := by
    simpa only [BitVec.ofNat_eq_ofNat, BitVec.add_zero] using
      hook_ok_at (P := libsignalSessionCode) (hname := deallocName) rfl (Nat.add_zero _)
        (by simp only [arm64_norm]) (fun _ => by simp only [arm64_norm])
        (by simp [Rust.isPanicSymbol, deallocName]) hDealloc
  exact sub_ok_at_of_fnAddr (b := b) (ext := ext) (sym := deallocName) hfn name k hk

end StandaloneDeallocHook

end LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.GenP3.AllocContractsMem4KBudget
