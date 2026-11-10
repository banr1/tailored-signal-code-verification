/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.TripleRatchet.Hooks2
import GeneratedLean.LibsignalSessionCode -- shake: keep
import LibsignalBinary.Proofs.CodeLayout
import LibsignalBinary.Proofs.FnOffEq
import ProofLib.SepLogic.WP.StateNorm

@[expose] public section

set_option autoImplicit false

/-!
# 4K-Stack Extern Contract Bundle (`AllocContractsMem4K`)

`subroutine_ok` contracts on `tripleRatchetProgAtExt b ext` for the Rust allocator (`alloc`,
`dealloc`, `realloc`), `shim`, and 4096-byte-stack `memcpy` / `memmove` / `memset`
(`allocHookStack = 4096`), matching `CliExternsOk`.
-/

namespace CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.GenP3

open Arm64 ProofLib ProofLib.ProgramReflection
open CryptoVerification.RustHeap
open CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchet

/-- `subroutine_ok` contracts on `tripleRatchetProgAtExt b ext` for the Rust allocator
(`alloc`, `dealloc`, `realloc`), `shim`, and 4096-byte-stack `memcpy` / `memmove` / `memset`
(`allocHookStack = 4096`), matching `CliExternsOk` directly without 0-stack `memcpyRegionSpec`. -/
structure AllocContractsMem4K (b : BitVec 64) (A : RustAlloc)
    (ext : String → Option (State → State)) : Prop where
  alloc :
    subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr allocName) (rustAllocSpec A)
  dealloc :
    subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr deallocName) (rustDeallocSpec A)
  realloc :
    subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr reallocName) (rustReallocSpec A)
  shim :
    subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr shimName)
      CryptoVerification.LibsignalTripleRatchet.sessionShimSpec
  session_memcpy :
    subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr memcpyName) (sessionMemcpySpec allocHookStack)
  session_memmove :
    subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr memmoveName) (sessionMemmoveSpec allocHookStack)
  session_memset :
    subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr memsetName) (sessionMemsetSpec allocHookStack)

namespace AllocContractsMem4K

variable {b : BitVec 64} {A : RustAlloc} {ext : String → Option (State → State)}

theorem alloc_ok_at (hA : AllocContractsMem4K b A ext) (name : String) (k : Nat)
    (hk : libsignalSessionCode.fnOff name + k = libsignalSessionCode.fnOff allocName := by
      fnoff_eq) :
    subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr name + BitVec.ofNat 64 k) (rustAllocSpec A) :=
  sub_ok_at_of_fnAddr (b := b) (ext := ext) (sym := allocName) hA.alloc name k hk

theorem dealloc_ok_at (hA : AllocContractsMem4K b A ext) (name : String) (k : Nat)
    (hk : libsignalSessionCode.fnOff name + k = libsignalSessionCode.fnOff deallocName := by
      fnoff_eq) :
    subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr name + BitVec.ofNat 64 k) (rustDeallocSpec A) :=
  sub_ok_at_of_fnAddr (b := b) (ext := ext) (sym := deallocName) hA.dealloc name k hk

theorem realloc_ok_at (hA : AllocContractsMem4K b A ext) (name : String) (k : Nat)
    (hk : libsignalSessionCode.fnOff name + k = libsignalSessionCode.fnOff reallocName := by
      fnoff_eq) :
    subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr name + BitVec.ofNat 64 k) (rustReallocSpec A) :=
  sub_ok_at_of_fnAddr (b := b) (ext := ext) (sym := reallocName) hA.realloc name k hk

theorem shim_ok_at (hA : AllocContractsMem4K b A ext) (name : String) (k : Nat)
    (hk : libsignalSessionCode.fnOff name + k = libsignalSessionCode.fnOff shimName := by
      fnoff_eq) :
    subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr name + BitVec.ofNat 64 k)
      CryptoVerification.LibsignalTripleRatchet.sessionShimSpec :=
  sub_ok_at_of_fnAddr (b := b) (ext := ext) (sym := shimName) hA.shim name k hk

theorem session_shim_ok_at (hA : AllocContractsMem4K b A ext) (name : String) (k : Nat)
    (hk : libsignalSessionCode.fnOff name + k = libsignalSessionCode.fnOff shimName := by
      fnoff_eq) :
    subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr name + BitVec.ofNat 64 k)
      CryptoVerification.LibsignalTripleRatchet.sessionShimSpec :=
  sub_ok_at_of_fnAddr (b := b) (ext := ext) (sym := shimName) hA.shim name k hk

theorem session_memcpy_ok_at (hA : AllocContractsMem4K b A ext) (name : String) (k : Nat)
    (hk : libsignalSessionCode.fnOff name + k = libsignalSessionCode.fnOff memcpyName := by
      fnoff_eq) :
    subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr name + BitVec.ofNat 64 k)
      (sessionMemcpySpec allocHookStack) :=
  sub_ok_at_of_fnAddr (b := b) (ext := ext) (sym := memcpyName) hA.session_memcpy name k hk

theorem session_memmove_ok_at (hA : AllocContractsMem4K b A ext) (name : String) (k : Nat)
    (hk : libsignalSessionCode.fnOff name + k = libsignalSessionCode.fnOff memmoveName := by
      fnoff_eq) :
    subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr name + BitVec.ofNat 64 k)
      (sessionMemmoveSpec allocHookStack) :=
  sub_ok_at_of_fnAddr (b := b) (ext := ext) (sym := memmoveName) hA.session_memmove name k hk

theorem session_memset_ok_at (hA : AllocContractsMem4K b A ext) (name : String) (k : Nat)
    (hk : libsignalSessionCode.fnOff name + k = libsignalSessionCode.fnOff memsetName := by
      fnoff_eq) :
    subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr name + BitVec.ofNat 64 k)
      (sessionMemsetSpec allocHookStack) :=
  sub_ok_at_of_fnAddr (b := b) (ext := ext) (sym := memsetName) hA.session_memset name k hk

/-- Every legacy `AllocContracts b A ext` trivially implies `AllocContractsMem4K b A ext`. -/
theorem of_AllocContracts (hA : AllocContracts b A ext) : AllocContractsMem4K b A ext where
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

/-- Construct `AllocContractsMem4K b A ext` directly from `AllocHooks A ext` and `HookSat`
hypotheses for `shim`, `memcpy`, `memmove`, and `memset` at `allocHookStack` (`= 4096`),
matching `CliExternsOk` (`hOk.alloc`, `hOk.shim`, `hOk.memcpy`, `hOk.memmove`, `hOk.memset`). -/
theorem of_hooks (b : BitVec 64) (A : RustAlloc) (ext : String → Option (State → State))
    (hAlloc : AllocHooks A ext)
    (hShim : HookSat ext shimName CryptoVerification.LibsignalTripleRatchet.sessionShimSpec)
    (hMemcpy : HookSat ext memcpyName (sessionMemcpySpec allocHookStack))
    (hMemmove : HookSat ext memmoveName (sessionMemmoveSpec allocHookStack))
    (hMemset : HookSat ext memsetName (sessionMemsetSpec allocHookStack)) :
    AllocContractsMem4K b A ext where
  alloc := sub_ok_fnAddr_of_hookSat b ext allocName _ (by simp only [arm64_norm]) (fun _ => by simp only [arm64_norm]) (by simp [Rust.isPanicSymbol, allocName]) hAlloc.alloc
  dealloc := sub_ok_fnAddr_of_hookSat b ext deallocName _ (by simp only [arm64_norm]) (fun _ => by simp only [arm64_norm]) (by simp [Rust.isPanicSymbol, deallocName]) hAlloc.dealloc
  realloc := sub_ok_fnAddr_of_hookSat b ext reallocName _ (by simp only [arm64_norm]) (fun _ => by simp only [arm64_norm]) (by simp [Rust.isPanicSymbol, reallocName]) hAlloc.realloc
  shim := sub_ok_fnAddr_of_hookSat b ext shimName _ (by simp only [arm64_norm]) (fun _ => by simp only [arm64_norm]) (by simp [Rust.isPanicSymbol, shimName]) hShim
  session_memcpy := sub_ok_fnAddr_of_hookSat b ext memcpyName _ (by simp only [arm64_norm]) (fun _ => by simp only [arm64_norm]) (by simp [Rust.isPanicSymbol, memcpyName]) hMemcpy
  session_memmove := sub_ok_fnAddr_of_hookSat b ext memmoveName _ (by simp only [arm64_norm]) (fun _ => by simp only [arm64_norm]) (by simp [Rust.isPanicSymbol, memmoveName]) hMemmove
  session_memset := sub_ok_fnAddr_of_hookSat b ext memsetName _ (by simp only [arm64_norm]) (fun _ => by simp only [arm64_norm]) (by simp [Rust.isPanicSymbol, memsetName]) hMemset

end HookHelpers

end AllocContractsMem4K

end CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.GenP3
