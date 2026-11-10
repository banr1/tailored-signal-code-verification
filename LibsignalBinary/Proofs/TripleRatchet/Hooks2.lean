/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

import all Init.Data.String.Pattern.Basic
import all Init.Data.String.Pattern.String
import all Init.Data.String.Slice
import all Init.Data.String.TakeDrop
public import GeneratedLean.LibsignalSessionCodeShard0
public import LibsignalBinary.Proofs.TripleRatchet.Hooks.Defs
public import LibsignalBinary.Specifications.LibsignalTripleRatchet
public import ProofLib
public import LibsignalBinary.Proofs.TripleRatchet.TrapRng
public import LibsignalBinary.Proofs.TripleRatchet.InImageCallees.Defs
import GeneratedLean.LibsignalSessionCode
import LibsignalBinary.Proofs.TripleRatchet.Hooks
import LibsignalBinary.Proofs.TripleRatchet.InImage.Uuid
import ProofLib.SepLogic.WP.Structural

set_option warningAsError false

/-!
# Generic Extern-Hook Program and Contract Bundles

Defines the generic rebased program `tripleRatchetProgAtExt b ext` and the subroutine contract
bundles `AllocContracts`, `Stage2Contracts`, `AllocContractsX`, and `Stage2ContractsX`, together
with stack-lifting helpers and concrete instantiations from `AllocHooks` and `TripleRatchetHooks`.
-/

@[expose] public section

namespace CryptoVerification.LibsignalTripleRatchet

open Arm64 ProofLib CryptoGames CryptoGames.HMAC CryptoGames.HKDF CryptoGames.LibsignalSession
open CryptoVerification.RustHeap CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchetRepr CryptoVerification.LibsignalProtoCodec

set_option maxRecDepth 200000
set_option maxHeartbeats 800000

/-! ## Generic rebased program and entry helpers -/

/-- `libsignalSessionCode` rebased at `b` with arbitrary extern hooks `ext` (wrapped in `Rust.withPanics`). -/
noncomputable abbrev tripleRatchetProgAtExt (b : BitVec 64) (ext : String → Option (State → State)) : Program :=
  libsignalSessionCode.rebase b (Rust.withPanics ext)

theorem tripleRatchetProgAt_eq_tripleRatchetProgAtExt_trap (b : BitVec 64) (C : Crypto)
    (abs : String → Option (State → State)) :
    trTrapProgAt b C abs = tripleRatchetProgAtExt b (trTrapExterns C abs) :=
  rfl

theorem tripleRatchetProgAt_eq_tripleRatchetProgAtExt (b : BitVec 64) (C : Crypto) (ctl : BitVec 64)
    (abs : String → Option (State → State)) :
    tripleRatchetProgAt b C ctl abs = tripleRatchetProgAtExt b (tripleRatchetExterns C ctl abs) :=
  rfl

theorem ofImage_eq_tripleRatchetProgAtExt {img : Obj.Image} (ext : String → Option (State → State))
    (himg : Obj.Loads libsignalSessionImage img) :
    Program.ofImage img (Rust.withPanics ext) = tripleRatchetProgAtExt img.base ext :=
  libsignalSessionCode_ofImage himg

theorem entryOf_eq_tripleRatchetProgAtExt {img : Obj.Image} (ext : String → Option (State → State))
    (himg : Obj.Loads libsignalSessionImage img) (name : String) :
    entryOf img name = (tripleRatchetProgAtExt img.base ext).fnAddr name := by
  unfold entryOf tripleRatchetProgAtExt
  rw [libsignalSessionCode_ofImage himg, Program.fnAddr_rebase, Program.fnAddr_rebase]

/-- From a per-function lemma on `tripleRatchetProgAtExt img.base ext` to `Program.ofImage img (Rust.withPanics ext)`
(such as `H.prog` or `tripleRatchetProg img C ctl abs`). -/
theorem root_of_tripleRatchetProgAtExt {α : Type} {img : Obj.Image} {ext : String → Option (State → State)}
    {name : String} {spec : Spec α} (himg : Obj.Loads libsignalSessionImage img)
    (h : subroutine_ok (tripleRatchetProgAtExt img.base ext) ((tripleRatchetProgAtExt img.base ext).fnAddr name) spec) :
    subroutine_ok (Program.ofImage img (Rust.withPanics ext)) (entryOf img name) spec := by
  rw [ofImage_eq_tripleRatchetProgAtExt ext himg, entryOf_eq_tripleRatchetProgAtExt ext himg name]
  exact h

/-- Convert a `subroutine_ok` at `(tripleRatchetProgAtExt b ext).fnAddr sym` into a call-site offset
`(tripleRatchetProgAtExt b ext).fnAddr name + BitVec.ofNat 64 k` whenever `fnOff name + k = fnOff sym`. -/
theorem sub_ok_at_of_fnAddr {α : Type} {b : BitVec 64} {ext : String → Option (State → State)}
    {sym : String} {spec : Spec α}
    (h : subroutine_ok (tripleRatchetProgAtExt b ext) ((tripleRatchetProgAtExt b ext).fnAddr sym) spec)
    (name : String) (k : Nat)
    (hk : libsignalSessionCode.fnOff name + k = libsignalSessionCode.fnOff sym := by
      simp only [arm64_norm]) :
    subroutine_ok (tripleRatchetProgAtExt b ext) ((tripleRatchetProgAtExt b ext).fnAddr name + BitVec.ofNat 64 k) spec := by
  rw [← Program.fnAddr_rel rfl rfl hk]
  exact h

/-! ## Panic-stub trap lemmas -/

theorem panic_at_handle_error_ext (b : BitVec 64) (ext : String → Option (State → State))
    (name : String) (k : Nat)
    (hk : libsignalSessionCode.fnOff name + k = libsignalSessionCode.fnOff handleErrorName := by
      simp only [arm64_norm]) :
    (tripleRatchetProgAtExt b ext).externAt?
      ((tripleRatchetProgAtExt b ext).fnAddr name + BitVec.ofNat 64 k) = some Rust.panicked :=
  panic_at_panicSymbol (hname := handleErrorName) rfl hk (by simp only [arm64_norm])
    (fun _ => by simp only [arm64_norm]) (by decide +kernel)

theorem panic_at_handle_alloc_error_ext (b : BitVec 64) (ext : String → Option (State → State))
    (name : String) (k : Nat)
    (hk : libsignalSessionCode.fnOff name + k = libsignalSessionCode.fnOff handleAllocErrorName := by
      simp only [arm64_norm]) :
    (tripleRatchetProgAtExt b ext).externAt?
      ((tripleRatchetProgAtExt b ext).fnAddr name + BitVec.ofNat 64 k) = some Rust.panicked :=
  panic_at_panicSymbol (hname := handleAllocErrorName) rfl hk (by simp only [arm64_norm])
    (fun _ => by simp only [arm64_norm]) (by decide +kernel)

theorem panic_at_sym_ext (b : BitVec 64) (ext : String → Option (State → State))
    (name sym : String) (k : Nat)
    (hk : libsignalSessionCode.fnOff name + k = libsignalSessionCode.fnOff sym)
    (hs : libsignalSessionCode.fnOff sym < 2 ^ 64 := by simp only [arm64_norm])
    (hstub : ∀ H, (libsignalSessionCode.rebase 0 H).hookAtOff? (libsignalSessionCode.fnOff sym) = H sym :=
      by intro _; simp only [arm64_norm])
    (hp : Rust.isPanicSymbol sym = true := by rfl) :
    (tripleRatchetProgAtExt b ext).externAt?
      ((tripleRatchetProgAtExt b ext).fnAddr name + BitVec.ofNat 64 k) = some Rust.panicked :=
  panic_at_panicSymbol (hname := sym) rfl hk hs hstub hp

theorem panic_at_vec_remove_assert_failed_ext (b : BitVec 64) (ext : String → Option (State → State))
    (hpan : (tripleRatchetProgAtExt b ext).externAt? ((tripleRatchetProgAtExt b ext).fnAddr vecRemoveAssertFailedName) = some Rust.panicked)
    (name : String) (k : Nat)
    (hk : libsignalSessionCode.fnOff name + k =
      libsignalSessionCode.fnOff vecRemoveAssertFailedName := by simp only [arm64_norm]) :
    (tripleRatchetProgAtExt b ext).externAt?
      ((tripleRatchetProgAtExt b ext).fnAddr name + BitVec.ofNat 64 k) = some Rust.panicked := by
  rw [← Program.fnAddr_rel rfl rfl hk]
  exact hpan

/-! ## Direct call-site lemmas from `HookSat` -/

theorem alloc_ok_at_ext (b : BitVec 64) (A : RustAlloc) (ext : String → Option (State → State))
    (hA : AllocHooks A ext) (name : String) (k : Nat)
    (hk : libsignalSessionCode.fnOff name + k = libsignalSessionCode.fnOff allocName := by
      simp only [arm64_norm]) :
    subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr name + BitVec.ofNat 64 k) (rustAllocSpec A) :=
  hook_ok_at (hname := allocName) rfl hk (by simp only [arm64_norm])
    (fun _ => by simp only [arm64_norm]) (by decide +kernel) hA.alloc

theorem dealloc_ok_at_ext (b : BitVec 64) (A : RustAlloc) (ext : String → Option (State → State))
    (hA : AllocHooks A ext) (name : String) (k : Nat)
    (hk : libsignalSessionCode.fnOff name + k = libsignalSessionCode.fnOff deallocName := by
      simp only [arm64_norm]) :
    subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr name + BitVec.ofNat 64 k) (rustDeallocSpec A) :=
  hook_ok_at (hname := deallocName) rfl hk (by simp only [arm64_norm])
    (fun _ => by simp only [arm64_norm]) (by decide +kernel) hA.dealloc

theorem realloc_ok_at_ext (b : BitVec 64) (A : RustAlloc) (ext : String → Option (State → State))
    (hA : AllocHooks A ext) (name : String) (k : Nat)
    (hk : libsignalSessionCode.fnOff name + k = libsignalSessionCode.fnOff reallocName := by
      simp only [arm64_norm]) :
    subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr name + BitVec.ofNat 64 k) (rustReallocSpec A) :=
  hook_ok_at (hname := reallocName) rfl hk (by simp only [arm64_norm])
    (fun _ => by simp only [arm64_norm]) (by decide +kernel) hA.realloc

theorem alloc_zeroed_ok_at_ext (b : BitVec 64) (A : RustAlloc) (ext : String → Option (State → State))
    (hZero : HookSat ext allocZeroedName (rustAllocZeroedSpec A)) (name : String) (k : Nat)
    (hk : libsignalSessionCode.fnOff name + k = libsignalSessionCode.fnOff allocZeroedName := by
      simp only [arm64_norm]) :
    subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr name + BitVec.ofNat 64 k) (rustAllocZeroedSpec A) :=
  hook_ok_at (hname := allocZeroedName) rfl hk (by simp only [arm64_norm])
    (fun _ => by simp only [arm64_norm]) (by decide +kernel) hZero

theorem aes_enc_ok_at_ext (b : BitVec 64) (C : Crypto) (A : RustAlloc) (ext : String → Option (State → State))
    (hEnc : HookSat ext aesEncName (aesEncSpec C.E A)) (name : String) (k : Nat)
    (hk : libsignalSessionCode.fnOff name + k = libsignalSessionCode.fnOff aesEncName := by
      simp only [arm64_norm]) :
    subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr name + BitVec.ofNat 64 k) (aesEncSpec C.E A) :=
  hook_ok_at (hname := aesEncName) rfl hk (by simp only [arm64_norm])
    (fun _ => by simp only [arm64_norm]) (by decide +kernel) hEnc

theorem aes_dec_ok_at_ext (b : BitVec 64) (C : Crypto) (A : RustAlloc) (ext : String → Option (State → State))
    (hDec : HookSat ext aesDecName (aesDecSpec C.D A)) (name : String) (k : Nat)
    (hk : libsignalSessionCode.fnOff name + k = libsignalSessionCode.fnOff aesDecName := by
      simp only [arm64_norm]) :
    subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr name + BitVec.ofNat 64 k) (aesDecSpec C.D A) :=
  hook_ok_at (hname := aesDecName) rfl hk (by simp only [arm64_norm])
    (fun _ => by simp only [arm64_norm]) (by decide +kernel) hDec

theorem format_inner_ok_at_ext (b : BitVec 64) (A : RustAlloc) (ext : String → Option (State → State))
    (hFmt : HookSat ext formatInnerName (formatInnerSpec A)) (name : String) (k : Nat)
    (hk : libsignalSessionCode.fnOff name + k = libsignalSessionCode.fnOff formatInnerName := by
      simp only [arm64_norm]) :
    subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr name + BitVec.ofNat 64 k) (formatInnerSpec A) :=
  hook_ok_at (hname := formatInnerName) rfl hk (by simp only [arm64_norm])
    (fun _ => by simp only [arm64_norm]) (by decide +kernel) hFmt

theorem fmt_write_ok_at_ext (b : BitVec 64) (A : RustAlloc) (ext : String → Option (State → State))
    (hW : HookSat ext fmtWriteName (fmtWriteSpec A)) (name : String) (k : Nat)
    (hk : libsignalSessionCode.fnOff name + k = libsignalSessionCode.fnOff fmtWriteName := by
      simp only [arm64_norm]) :
    subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr name + BitVec.ofNat 64 k) (fmtWriteSpec A) :=
  hook_ok_at (hname := fmtWriteName) rfl hk (by simp only [arm64_norm])
    (fun _ => by simp only [arm64_norm]) (by decide +kernel) hW

/-! ## `AllocContracts` bundle -/

/-- `subroutine_ok` contracts on `tripleRatchetProgAtExt b ext` for the Rust allocator (`alloc`, `dealloc`, `realloc`),
the no-alloc shim (`shim`), and `memcpy` / `memmove` / `memset`. -/
structure AllocContracts (b : BitVec 64) (A : RustAlloc)
    (ext : String → Option (State → State)) : Prop where
  alloc : subroutine_ok (tripleRatchetProgAtExt b ext) ((tripleRatchetProgAtExt b ext).fnAddr allocName) (rustAllocSpec A)
  dealloc : subroutine_ok (tripleRatchetProgAtExt b ext) ((tripleRatchetProgAtExt b ext).fnAddr deallocName) (rustDeallocSpec A)
  realloc : subroutine_ok (tripleRatchetProgAtExt b ext) ((tripleRatchetProgAtExt b ext).fnAddr reallocName) (rustReallocSpec A)
  shim : subroutine_ok (tripleRatchetProgAtExt b ext) ((tripleRatchetProgAtExt b ext).fnAddr shimName) sessionShimSpec
  memcpy : ∀ (hookStack : Nat),
    subroutine_ok (tripleRatchetProgAtExt b ext) ((tripleRatchetProgAtExt b ext).fnAddr memcpyName) (libcMemcpySpec hookStack)
  session_memcpy : ∀ (hookStack : Nat),
    subroutine_ok (tripleRatchetProgAtExt b ext) ((tripleRatchetProgAtExt b ext).fnAddr memcpyName) (sessionMemcpySpec hookStack)
  memcpy_region :
    subroutine_ok (tripleRatchetProgAtExt b ext) ((tripleRatchetProgAtExt b ext).fnAddr memcpyName) memcpyRegionSpec
  session_memcpy_region :
    subroutine_ok (tripleRatchetProgAtExt b ext) ((tripleRatchetProgAtExt b ext).fnAddr memcpyName) sessionMemcpyRegionSpec
  memmove : ∀ (hookStack : Nat),
    subroutine_ok (tripleRatchetProgAtExt b ext) ((tripleRatchetProgAtExt b ext).fnAddr memmoveName) (libcMemmoveSpec hookStack)
  session_memmove : ∀ (hookStack : Nat),
    subroutine_ok (tripleRatchetProgAtExt b ext) ((tripleRatchetProgAtExt b ext).fnAddr memmoveName) (sessionMemmoveSpec hookStack)
  memset : ∀ (hookStack : Nat), 0 < hookStack →
    subroutine_ok (tripleRatchetProgAtExt b ext) ((tripleRatchetProgAtExt b ext).fnAddr memsetName) (libcMemsetSpec hookStack)
  session_memset : ∀ (hookStack : Nat), 0 < hookStack →
    subroutine_ok (tripleRatchetProgAtExt b ext) ((tripleRatchetProgAtExt b ext).fnAddr memsetName) (sessionMemsetSpec hookStack)
  memset_region :
    subroutine_ok (tripleRatchetProgAtExt b ext) ((tripleRatchetProgAtExt b ext).fnAddr memsetName) memsetRegionSpec
  session_memset_region :
    subroutine_ok (tripleRatchetProgAtExt b ext) ((tripleRatchetProgAtExt b ext).fnAddr memsetName) sessionMemsetRegionSpec

namespace AllocContracts

variable {b : BitVec 64} {A : RustAlloc} {ext : String → Option (State → State)}

theorem alloc_ok_at (hA : AllocContracts b A ext) (name : String) (k : Nat)
    (hk : libsignalSessionCode.fnOff name + k = libsignalSessionCode.fnOff allocName := by
      simp only [arm64_norm]) :
    subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr name + BitVec.ofNat 64 k) (rustAllocSpec A) :=
  sub_ok_at_of_fnAddr hA.alloc name k hk

theorem dealloc_ok_at (hA : AllocContracts b A ext) (name : String) (k : Nat)
    (hk : libsignalSessionCode.fnOff name + k = libsignalSessionCode.fnOff deallocName := by
      simp only [arm64_norm]) :
    subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr name + BitVec.ofNat 64 k) (rustDeallocSpec A) :=
  sub_ok_at_of_fnAddr hA.dealloc name k hk

theorem realloc_ok_at (hA : AllocContracts b A ext) (name : String) (k : Nat)
    (hk : libsignalSessionCode.fnOff name + k = libsignalSessionCode.fnOff reallocName := by
      simp only [arm64_norm]) :
    subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr name + BitVec.ofNat 64 k) (rustReallocSpec A) :=
  sub_ok_at_of_fnAddr hA.realloc name k hk

theorem shim_ok_at (hA : AllocContracts b A ext) (name : String) (k : Nat)
    (hk : libsignalSessionCode.fnOff name + k = libsignalSessionCode.fnOff shimName := by
      simp only [arm64_norm]) :
    subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr name + BitVec.ofNat 64 k) sessionShimSpec :=
  sub_ok_at_of_fnAddr hA.shim name k hk

theorem session_shim_ok_at (hA : AllocContracts b A ext) (name : String) (k : Nat)
    (hk : libsignalSessionCode.fnOff name + k = libsignalSessionCode.fnOff shimName := by
      simp only [arm64_norm]) :
    subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr name + BitVec.ofNat 64 k) sessionShimSpec :=
  sub_ok_at_of_fnAddr hA.shim name k hk

theorem memcpy_ok_at (hA : AllocContracts b A ext) (name : String) (k : Nat)
    (hookStack : Nat := 4096)
    (hk : libsignalSessionCode.fnOff name + k = libsignalSessionCode.fnOff memcpyName := by
      simp only [arm64_norm]) :
    subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr name + BitVec.ofNat 64 k) (libcMemcpySpec hookStack) :=
  sub_ok_at_of_fnAddr (hA.memcpy hookStack) name k hk

theorem session_memcpy_ok_at (hA : AllocContracts b A ext) (name : String) (k : Nat)
    (hookStack : Nat := 4096)
    (hk : libsignalSessionCode.fnOff name + k = libsignalSessionCode.fnOff memcpyName := by
      simp only [arm64_norm]) :
    subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr name + BitVec.ofNat 64 k) (sessionMemcpySpec hookStack) :=
  sub_ok_at_of_fnAddr (hA.session_memcpy hookStack) name k hk

theorem memcpy_region_ok_at (hA : AllocContracts b A ext) (name : String) (k : Nat)
    (hk : libsignalSessionCode.fnOff name + k = libsignalSessionCode.fnOff memcpyName := by
      simp only [arm64_norm]) :
    subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr name + BitVec.ofNat 64 k) memcpyRegionSpec :=
  sub_ok_at_of_fnAddr hA.memcpy_region name k hk

theorem session_memcpy_region_ok_at (hA : AllocContracts b A ext) (name : String) (k : Nat)
    (hk : libsignalSessionCode.fnOff name + k = libsignalSessionCode.fnOff memcpyName := by
      simp only [arm64_norm]) :
    subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr name + BitVec.ofNat 64 k) sessionMemcpyRegionSpec :=
  sub_ok_at_of_fnAddr hA.session_memcpy_region name k hk

theorem memmove_ok_at (hA : AllocContracts b A ext) (name : String) (k : Nat)
    (hookStack : Nat := 4096)
    (hk : libsignalSessionCode.fnOff name + k = libsignalSessionCode.fnOff memmoveName := by
      simp only [arm64_norm]) :
    subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr name + BitVec.ofNat 64 k) (libcMemmoveSpec hookStack) :=
  sub_ok_at_of_fnAddr (hA.memmove hookStack) name k hk

theorem session_memmove_ok_at (hA : AllocContracts b A ext) (name : String) (k : Nat)
    (hookStack : Nat := 4096)
    (hk : libsignalSessionCode.fnOff name + k = libsignalSessionCode.fnOff memmoveName := by
      simp only [arm64_norm]) :
    subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr name + BitVec.ofNat 64 k) (sessionMemmoveSpec hookStack) :=
  sub_ok_at_of_fnAddr (hA.session_memmove hookStack) name k hk

theorem memset_ok_at (hA : AllocContracts b A ext) (name : String) (k : Nat)
    (hookStack : Nat := 4096) (hstack : 0 < hookStack := by decide)
    (hk : libsignalSessionCode.fnOff name + k = libsignalSessionCode.fnOff memsetName := by
      simp only [arm64_norm]) :
    subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr name + BitVec.ofNat 64 k) (libcMemsetSpec hookStack) :=
  sub_ok_at_of_fnAddr (hA.memset hookStack hstack) name k hk

theorem session_memset_ok_at (hA : AllocContracts b A ext) (name : String) (k : Nat)
    (hookStack : Nat := 4096) (hstack : 0 < hookStack := by decide)
    (hk : libsignalSessionCode.fnOff name + k = libsignalSessionCode.fnOff memsetName := by
      simp only [arm64_norm]) :
    subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr name + BitVec.ofNat 64 k) (sessionMemsetSpec hookStack) :=
  sub_ok_at_of_fnAddr (hA.session_memset hookStack hstack) name k hk

theorem memset_region_ok_at (hA : AllocContracts b A ext) (name : String) (k : Nat)
    (hk : libsignalSessionCode.fnOff name + k = libsignalSessionCode.fnOff memsetName := by
      simp only [arm64_norm]) :
    subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr name + BitVec.ofNat 64 k) memsetRegionSpec :=
  sub_ok_at_of_fnAddr hA.memset_region name k hk

theorem session_memset_region_ok_at (hA : AllocContracts b A ext) (name : String) (k : Nat)
    (hk : libsignalSessionCode.fnOff name + k = libsignalSessionCode.fnOff memsetName := by
      simp only [arm64_norm]) :
    subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr name + BitVec.ofNat 64 k) sessionMemsetRegionSpec :=
  sub_ok_at_of_fnAddr hA.session_memset_region name k hk

theorem of_tripleRatchetProgAt_trap (b : BitVec 64) (C : Crypto) (A : RustAlloc)
    (abs : String → Option (State → State))
    (hA : AllocHooks A abs) :
    AllocContracts b A (trTrapExterns C abs) where
  alloc := by
    simpa only [BitVec.ofNat_eq_ofNat, BitVec.add_zero] using
      CryptoVerification.LibsignalTripleRatchet.alloc_ok_at_trap b C A abs hA allocName 0 (Nat.add_zero _)
  dealloc := by
    simpa only [BitVec.ofNat_eq_ofNat, BitVec.add_zero] using
      CryptoVerification.LibsignalTripleRatchet.dealloc_ok_at_trap b C A abs hA deallocName 0 (Nat.add_zero _)
  realloc := by
    simpa only [BitVec.ofNat_eq_ofNat, BitVec.add_zero] using
      CryptoVerification.LibsignalTripleRatchet.realloc_ok_at_trap b C A abs hA reallocName 0 (Nat.add_zero _)
  shim := by
    simpa only [BitVec.ofNat_eq_ofNat, BitVec.add_zero] using
      CryptoVerification.LibsignalTripleRatchet.shim_ok_at_trap b C abs shimName 0 (Nat.add_zero _)
  memcpy hookStack := by
    simpa only [BitVec.ofNat_eq_ofNat, BitVec.add_zero] using
      CryptoVerification.LibsignalTripleRatchet.memcpy_ok_at_trap b C abs memcpyName 0 hookStack (Nat.add_zero _)
  session_memcpy hookStack := by
    simpa only [BitVec.ofNat_eq_ofNat, BitVec.add_zero] using
      CryptoVerification.LibsignalTripleRatchet.session_memcpy_ok_at_trap b C abs memcpyName 0 hookStack (Nat.add_zero _)
  memcpy_region := by
    simpa only [BitVec.ofNat_eq_ofNat, BitVec.add_zero] using
      CryptoVerification.LibsignalTripleRatchet.memcpy_region_ok_at_trap b C abs memcpyName 0 (Nat.add_zero _)
  session_memcpy_region := by
    simpa only [BitVec.ofNat_eq_ofNat, BitVec.add_zero] using
      CryptoVerification.LibsignalTripleRatchet.session_memcpy_region_ok_at_trap b C abs memcpyName 0 (Nat.add_zero _)
  memmove hookStack := by
    simpa only [BitVec.ofNat_eq_ofNat, BitVec.add_zero] using
      CryptoVerification.LibsignalTripleRatchet.memmove_ok_at_trap b C abs memmoveName 0 hookStack (Nat.add_zero _)
  session_memmove hookStack := by
    simpa only [BitVec.ofNat_eq_ofNat, BitVec.add_zero] using
      CryptoVerification.LibsignalTripleRatchet.session_memmove_ok_at_trap b C abs memmoveName 0 hookStack (Nat.add_zero _)
  memset hookStack hstack := by
    simpa only [BitVec.ofNat_eq_ofNat, BitVec.add_zero] using
      CryptoVerification.LibsignalTripleRatchet.memset_ok_at_trap b C abs memsetName 0 hookStack hstack (Nat.add_zero _)
  session_memset hookStack hstack := by
    simpa only [BitVec.ofNat_eq_ofNat, BitVec.add_zero] using
      CryptoVerification.LibsignalTripleRatchet.session_memset_ok_at_trap b C abs memsetName 0 hookStack hstack (Nat.add_zero _)
  memset_region := by
    simpa only [BitVec.ofNat_eq_ofNat, BitVec.add_zero] using
      CryptoVerification.LibsignalTripleRatchet.memset_region_ok_at_trap b C abs memsetName 0 (Nat.add_zero _)
  session_memset_region := by
    simpa only [BitVec.ofNat_eq_ofNat, BitVec.add_zero] using
      CryptoVerification.LibsignalTripleRatchet.session_memset_region_ok_at_trap b C abs memsetName 0 (Nat.add_zero _)

theorem of_tripleRatchetProgAt (b : BitVec 64) (C : Crypto) (A : RustAlloc) (ctl : BitVec 64)
    (abs : String → Option (State → State))
    (hA : AllocHooks A abs) :
    AllocContracts b A (tripleRatchetExterns C ctl abs) where
  alloc := by
    change subroutine_ok (tripleRatchetProgAt b C ctl abs) ((tripleRatchetProgAt b C ctl abs).fnAddr allocName) _
    rw [← (trapsOnly_trTrap_kit b C ctl abs).fnAddr allocName]
    exact subroutine_ok_kit_of_trTrap (of_tripleRatchetProgAt_trap b C A abs hA).alloc
  dealloc := by
    change subroutine_ok (tripleRatchetProgAt b C ctl abs) ((tripleRatchetProgAt b C ctl abs).fnAddr deallocName) _
    rw [← (trapsOnly_trTrap_kit b C ctl abs).fnAddr deallocName]
    exact subroutine_ok_kit_of_trTrap (of_tripleRatchetProgAt_trap b C A abs hA).dealloc
  realloc := by
    change subroutine_ok (tripleRatchetProgAt b C ctl abs) ((tripleRatchetProgAt b C ctl abs).fnAddr reallocName) _
    rw [← (trapsOnly_trTrap_kit b C ctl abs).fnAddr reallocName]
    exact subroutine_ok_kit_of_trTrap (of_tripleRatchetProgAt_trap b C A abs hA).realloc
  shim := by
    change subroutine_ok (tripleRatchetProgAt b C ctl abs) ((tripleRatchetProgAt b C ctl abs).fnAddr shimName) _
    rw [← (trapsOnly_trTrap_kit b C ctl abs).fnAddr shimName]
    exact subroutine_ok_kit_of_trTrap (of_tripleRatchetProgAt_trap b C A abs hA).shim
  memcpy hookStack := by
    change subroutine_ok (tripleRatchetProgAt b C ctl abs) ((tripleRatchetProgAt b C ctl abs).fnAddr memcpyName) _
    rw [← (trapsOnly_trTrap_kit b C ctl abs).fnAddr memcpyName]
    exact subroutine_ok_kit_of_trTrap ((of_tripleRatchetProgAt_trap b C A abs hA).memcpy hookStack)
  session_memcpy hookStack := by
    change subroutine_ok (tripleRatchetProgAt b C ctl abs) ((tripleRatchetProgAt b C ctl abs).fnAddr memcpyName) _
    rw [← (trapsOnly_trTrap_kit b C ctl abs).fnAddr memcpyName]
    exact subroutine_ok_kit_of_trTrap ((of_tripleRatchetProgAt_trap b C A abs hA).session_memcpy hookStack)
  memcpy_region := by
    change subroutine_ok (tripleRatchetProgAt b C ctl abs) ((tripleRatchetProgAt b C ctl abs).fnAddr memcpyName) _
    rw [← (trapsOnly_trTrap_kit b C ctl abs).fnAddr memcpyName]
    exact subroutine_ok_kit_of_trTrap (of_tripleRatchetProgAt_trap b C A abs hA).memcpy_region
  session_memcpy_region := by
    change subroutine_ok (tripleRatchetProgAt b C ctl abs) ((tripleRatchetProgAt b C ctl abs).fnAddr memcpyName) _
    rw [← (trapsOnly_trTrap_kit b C ctl abs).fnAddr memcpyName]
    exact subroutine_ok_kit_of_trTrap (of_tripleRatchetProgAt_trap b C A abs hA).session_memcpy_region
  memmove hookStack := by
    change subroutine_ok (tripleRatchetProgAt b C ctl abs) ((tripleRatchetProgAt b C ctl abs).fnAddr memmoveName) _
    rw [← (trapsOnly_trTrap_kit b C ctl abs).fnAddr memmoveName]
    exact subroutine_ok_kit_of_trTrap ((of_tripleRatchetProgAt_trap b C A abs hA).memmove hookStack)
  session_memmove hookStack := by
    change subroutine_ok (tripleRatchetProgAt b C ctl abs) ((tripleRatchetProgAt b C ctl abs).fnAddr memmoveName) _
    rw [← (trapsOnly_trTrap_kit b C ctl abs).fnAddr memmoveName]
    exact subroutine_ok_kit_of_trTrap ((of_tripleRatchetProgAt_trap b C A abs hA).session_memmove hookStack)
  memset hookStack hstack := by
    change subroutine_ok (tripleRatchetProgAt b C ctl abs) ((tripleRatchetProgAt b C ctl abs).fnAddr memsetName) _
    rw [← (trapsOnly_trTrap_kit b C ctl abs).fnAddr memsetName]
    exact subroutine_ok_kit_of_trTrap ((of_tripleRatchetProgAt_trap b C A abs hA).memset hookStack hstack)
  session_memset hookStack hstack := by
    change subroutine_ok (tripleRatchetProgAt b C ctl abs) ((tripleRatchetProgAt b C ctl abs).fnAddr memsetName) _
    rw [← (trapsOnly_trTrap_kit b C ctl abs).fnAddr memsetName]
    exact subroutine_ok_kit_of_trTrap ((of_tripleRatchetProgAt_trap b C A abs hA).session_memset hookStack hstack)
  memset_region := by
    change subroutine_ok (tripleRatchetProgAt b C ctl abs) ((tripleRatchetProgAt b C ctl abs).fnAddr memsetName) _
    rw [← (trapsOnly_trTrap_kit b C ctl abs).fnAddr memsetName]
    exact subroutine_ok_kit_of_trTrap (of_tripleRatchetProgAt_trap b C A abs hA).memset_region
  session_memset_region := by
    change subroutine_ok (tripleRatchetProgAt b C ctl abs) ((tripleRatchetProgAt b C ctl abs).fnAddr memsetName) _
    rw [← (trapsOnly_trTrap_kit b C ctl abs).fnAddr memsetName]
    exact subroutine_ok_kit_of_trTrap (of_tripleRatchetProgAt_trap b C A abs hA).session_memset_region

theorem of_tripleRatchetProgAt'_trap {b : BitVec 64} {C : Crypto} {A : RustAlloc}
    {abs : String → Option (State → State)}
    (hA : AllocHooks A abs) :
    AllocContracts b A (trTrapExterns C abs) :=
  of_tripleRatchetProgAt_trap b C A abs hA

theorem of_tripleRatchetProgAt' {b : BitVec 64} {C : Crypto} {A : RustAlloc} {ctl : BitVec 64}
    {abs : String → Option (State → State)}
    (hA : AllocHooks A abs) :
    AllocContracts b A (tripleRatchetExterns C ctl abs) :=
  of_tripleRatchetProgAt b C A ctl abs hA

end AllocContracts

/-! ## `Stage2Contracts` bundle -/

/-- `subroutine_ok` contract bundle for all concrete and abstract extern stubs on
`tripleRatchetProgAtExt b ext` (excluding RNG fill), plus in-image `<uuid::Uuid>::try_parse`. -/
structure Stage2Contracts_trap (b : BitVec 64) (C : Crypto) (A : RustAlloc)
    (parse : UuidParser) (S : SpqrModel) (ext : String → Option (State → State)) : Prop extends
    AllocContracts b A ext where
  black_box :
    subroutine_ok (tripleRatchetProgAtExt b ext) ((tripleRatchetProgAtExt b ext).fnAddr blackBoxName) blackBoxSpec
  compress256 :
    subroutine_ok (tripleRatchetProgAtExt b ext) ((tripleRatchetProgAtExt b ext).fnAddr compress256Name) (compress256Spec C.F)
  dh :
    subroutine_ok (tripleRatchetProgAtExt b ext) ((tripleRatchetProgAtExt b ext).fnAddr dhName) (diffieHellmanSpec C.X)
  pub_from_secret :
    subroutine_ok (tripleRatchetProgAtExt b ext) ((tripleRatchetProgAtExt b ext).fnAddr pubFromSecretName) (pubFromSecretSpec C.pubKey)
  static_drop :
    subroutine_ok (tripleRatchetProgAtExt b ext) ((tripleRatchetProgAtExt b ext).fnAddr staticDropName) zeroizeSecretSpec
  shared_drop :
    subroutine_ok (tripleRatchetProgAtExt b ext) ((tripleRatchetProgAtExt b ext).fnAddr sharedDropName) zeroizeSecretSpec
  uuid_try_parse :
    subroutine_ok (tripleRatchetProgAtExt b ext) ((tripleRatchetProgAtExt b ext).fnAddr uuidTryParseName) (uuidTryParseCodeSpec parse)
  decode_varint_slow :
    subroutine_ok (tripleRatchetProgAtExt b ext) ((tripleRatchetProgAtExt b ext).fnAddr varintSlowName) (decodeVarintSlowSpec A)
  alloc_zeroed :
    subroutine_ok (tripleRatchetProgAtExt b ext) ((tripleRatchetProgAtExt b ext).fnAddr allocZeroedName) (rustAllocZeroedSpec A)
  decode_state_empty :
    subroutine_ok (tripleRatchetProgAtExt b ext) ((tripleRatchetProgAtExt b ext).fnAddr decodeStateName) (decodeStateEmptySpec A)
  aes_enc :
    subroutine_ok (tripleRatchetProgAtExt b ext) ((tripleRatchetProgAtExt b ext).fnAddr aesEncName) (aesEncSpec C.E A)
  aes_dec :
    subroutine_ok (tripleRatchetProgAtExt b ext) ((tripleRatchetProgAtExt b ext).fnAddr aesDecName) (aesDecSpec C.D A)
  format_inner :
    subroutine_ok (tripleRatchetProgAtExt b ext) ((tripleRatchetProgAtExt b ext).fnAddr formatInnerName) (formatInnerSpec A)
  fmt_write :
    subroutine_ok (tripleRatchetProgAtExt b ext) ((tripleRatchetProgAtExt b ext).fnAddr fmtWriteName) (fmtWriteSpec A)
  decode_error_from :
    subroutine_ok (tripleRatchetProgAtExt b ext) ((tripleRatchetProgAtExt b ext).fnAddr decodeErrorFromName) (decodeErrorFromSpec A)
  decode_error_push :
    subroutine_ok (tripleRatchetProgAtExt b ext) ((tripleRatchetProgAtExt b ext).fnAddr decodeErrorPushName) (decodeErrorPushSpec A)
  vec_remove_assert_failed_panics :
    (tripleRatchetProgAtExt b ext).externAt? ((tripleRatchetProgAtExt b ext).fnAddr vecRemoveAssertFailedName) = some Rust.panicked

structure Stage2Contracts (b : BitVec 64) (C : Crypto) (A : RustAlloc) (ctl : BitVec 64)
    (parse : UuidParser) (S : SpqrModel) (ext : String → Option (State → State)) : Prop extends
    AllocContracts b A ext where
  black_box :
    subroutine_ok (tripleRatchetProgAtExt b ext) ((tripleRatchetProgAtExt b ext).fnAddr blackBoxName) blackBoxSpec
  compress256 :
    subroutine_ok (tripleRatchetProgAtExt b ext) ((tripleRatchetProgAtExt b ext).fnAddr compress256Name) (compress256Spec C.F)
  dh :
    subroutine_ok (tripleRatchetProgAtExt b ext) ((tripleRatchetProgAtExt b ext).fnAddr dhName) (diffieHellmanSpec C.X)
  pub_from_secret :
    subroutine_ok (tripleRatchetProgAtExt b ext) ((tripleRatchetProgAtExt b ext).fnAddr pubFromSecretName) (pubFromSecretSpec C.pubKey)
  static_drop :
    subroutine_ok (tripleRatchetProgAtExt b ext) ((tripleRatchetProgAtExt b ext).fnAddr staticDropName) zeroizeSecretSpec
  shared_drop :
    subroutine_ok (tripleRatchetProgAtExt b ext) ((tripleRatchetProgAtExt b ext).fnAddr sharedDropName) zeroizeSecretSpec
  rng_fill :
    subroutine_ok (tripleRatchetProgAtExt b ext) ((tripleRatchetProgAtExt b ext).fnAddr rngFillName) (rngFillSpec ctl)
  uuid_try_parse :
    subroutine_ok (tripleRatchetProgAtExt b ext) ((tripleRatchetProgAtExt b ext).fnAddr uuidTryParseName) (uuidTryParseCodeSpec parse)
  decode_varint_slow :
    subroutine_ok (tripleRatchetProgAtExt b ext) ((tripleRatchetProgAtExt b ext).fnAddr varintSlowName) (decodeVarintSlowSpec A)
  alloc_zeroed :
    subroutine_ok (tripleRatchetProgAtExt b ext) ((tripleRatchetProgAtExt b ext).fnAddr allocZeroedName) (rustAllocZeroedSpec A)
  decode_state_empty :
    subroutine_ok (tripleRatchetProgAtExt b ext) ((tripleRatchetProgAtExt b ext).fnAddr decodeStateName) (decodeStateEmptySpec A)
  aes_enc :
    subroutine_ok (tripleRatchetProgAtExt b ext) ((tripleRatchetProgAtExt b ext).fnAddr aesEncName) (aesEncSpec C.E A)
  aes_dec :
    subroutine_ok (tripleRatchetProgAtExt b ext) ((tripleRatchetProgAtExt b ext).fnAddr aesDecName) (aesDecSpec C.D A)
  format_inner :
    subroutine_ok (tripleRatchetProgAtExt b ext) ((tripleRatchetProgAtExt b ext).fnAddr formatInnerName) (formatInnerSpec A)
  fmt_write :
    subroutine_ok (tripleRatchetProgAtExt b ext) ((tripleRatchetProgAtExt b ext).fnAddr fmtWriteName) (fmtWriteSpec A)
  decode_error_from :
    subroutine_ok (tripleRatchetProgAtExt b ext) ((tripleRatchetProgAtExt b ext).fnAddr decodeErrorFromName) (decodeErrorFromSpec A)
  decode_error_push :
    subroutine_ok (tripleRatchetProgAtExt b ext) ((tripleRatchetProgAtExt b ext).fnAddr decodeErrorPushName) (decodeErrorPushSpec A)
  vec_remove_assert_failed_panics :
    (tripleRatchetProgAtExt b ext).externAt? ((tripleRatchetProgAtExt b ext).fnAddr vecRemoveAssertFailedName) = some Rust.panicked

theorem uuid_try_parse_ok_at_trap (b : BitVec 64) (C : Crypto)
    (abs : String → Option (State → State)) (name : String) (k : Nat)
    (hk : libsignalSessionCode.fnOff name + k = libsignalSessionCode.fnOff uuidTryParseName) :
    subroutine_ok (trTrapProgAt b C abs)
      ((trTrapProgAt b C abs).fnAddr name + BitVec.ofNat 64 k) (uuidTryParseCodeSpec uuidTryParse) :=
  uuidTryParse_ok_at_trap b C abs name k hk

theorem uuid_try_parse_ok_at (b : BitVec 64) (C : Crypto) (ctl : BitVec 64)
    (abs : String → Option (State → State)) (name : String) (k : Nat)
    (hk : libsignalSessionCode.fnOff name + k = libsignalSessionCode.fnOff uuidTryParseName) :
    subroutine_ok (tripleRatchetProgAt b C ctl abs)
      ((tripleRatchetProgAt b C ctl abs).fnAddr name + BitVec.ofNat 64 k) (uuidTryParseCodeSpec uuidTryParse) := by
  rw [← (trapsOnly_trTrap_kit b C ctl abs).fnAddr name]
  exact subroutine_ok_kit_of_trTrap (uuid_try_parse_ok_at_trap b C abs name k hk)

theorem fmt_write_ok_at_trap (b : BitVec 64) (C : Crypto) (A : RustAlloc)
    (abs : String → Option (State → State))
    (hW : HookSat abs fmtWriteName (fmtWriteSpec A)) (name : String) (k : Nat)
    (hk : libsignalSessionCode.fnOff name + k = libsignalSessionCode.fnOff fmtWriteName) :
    subroutine_ok (trTrapProgAt b C abs)
      ((trTrapProgAt b C abs).fnAddr name + BitVec.ofNat 64 k) (fmtWriteSpec A) :=
  hook_ok_at (hname := fmtWriteName) rfl hk (by simp only [arm64_norm])
    (fun _ => by simp only [arm64_norm]) (by decide +kernel)
    (hookSat_trTrapExterns (by decide) (by decide) hW)

theorem fmt_write_ok_at (b : BitVec 64) (C : Crypto) (A : RustAlloc) (ctl : BitVec 64)
    (abs : String → Option (State → State))
    (hW : HookSat abs fmtWriteName (fmtWriteSpec A)) (name : String) (k : Nat)
    (hk : libsignalSessionCode.fnOff name + k = libsignalSessionCode.fnOff fmtWriteName) :
    subroutine_ok (tripleRatchetProgAt b C ctl abs)
      ((tripleRatchetProgAt b C ctl abs).fnAddr name + BitVec.ofNat 64 k) (fmtWriteSpec A) := by
  rw [← (trapsOnly_trTrap_kit b C ctl abs).fnAddr name]
  exact subroutine_ok_kit_of_trTrap (fmt_write_ok_at_trap b C A abs hW name k hk)

namespace Stage2Contracts

variable {b : BitVec 64} {C : Crypto} {A : RustAlloc} {ctl : BitVec 64}
  {S : SpqrModel} {ext : String → Option (State → State)}

theorem black_box_ok_at (hC : Stage2Contracts b C A ctl uuidTryParse S ext) (name : String) (k : Nat)
    (hk : libsignalSessionCode.fnOff name + k = libsignalSessionCode.fnOff blackBoxName := by
      simp only [arm64_norm]) :
    subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr name + BitVec.ofNat 64 k) blackBoxSpec :=
  sub_ok_at_of_fnAddr hC.black_box name k hk

theorem compress256_ok_at (hC : Stage2Contracts b C A ctl uuidTryParse S ext) (name : String) (k : Nat)
    (hk : libsignalSessionCode.fnOff name + k = libsignalSessionCode.fnOff compress256Name := by
      simp only [arm64_norm]) :
    subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr name + BitVec.ofNat 64 k) (compress256Spec C.F) :=
  sub_ok_at_of_fnAddr hC.compress256 name k hk

theorem dh_ok_at (hC : Stage2Contracts b C A ctl uuidTryParse S ext) (name : String) (k : Nat)
    (hk : libsignalSessionCode.fnOff name + k = libsignalSessionCode.fnOff dhName := by
      simp only [arm64_norm]) :
    subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr name + BitVec.ofNat 64 k) (diffieHellmanSpec C.X) :=
  sub_ok_at_of_fnAddr hC.dh name k hk

theorem pub_from_secret_ok_at (hC : Stage2Contracts b C A ctl uuidTryParse S ext) (name : String) (k : Nat)
    (hk : libsignalSessionCode.fnOff name + k = libsignalSessionCode.fnOff pubFromSecretName := by
      simp only [arm64_norm]) :
    subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr name + BitVec.ofNat 64 k) (pubFromSecretSpec C.pubKey) :=
  sub_ok_at_of_fnAddr hC.pub_from_secret name k hk

theorem static_drop_ok_at (hC : Stage2Contracts b C A ctl uuidTryParse S ext) (name : String) (k : Nat)
    (hk : libsignalSessionCode.fnOff name + k = libsignalSessionCode.fnOff staticDropName := by
      simp only [arm64_norm]) :
    subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr name + BitVec.ofNat 64 k) zeroizeSecretSpec :=
  sub_ok_at_of_fnAddr hC.static_drop name k hk

theorem shared_drop_ok_at (hC : Stage2Contracts b C A ctl uuidTryParse S ext) (name : String) (k : Nat)
    (hk : libsignalSessionCode.fnOff name + k = libsignalSessionCode.fnOff sharedDropName := by
      simp only [arm64_norm]) :
    subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr name + BitVec.ofNat 64 k) zeroizeSecretSpec :=
  sub_ok_at_of_fnAddr hC.shared_drop name k hk

theorem rng_fill_ok_at (hC : Stage2Contracts b C A ctl uuidTryParse S ext) (name : String) (k : Nat)
    (hk : libsignalSessionCode.fnOff name + k = libsignalSessionCode.fnOff rngFillName := by
      simp only [arm64_norm]) :
    subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr name + BitVec.ofNat 64 k) (rngFillSpec ctl) :=
  sub_ok_at_of_fnAddr hC.rng_fill name k hk

theorem uuid_try_parse_ok_at (hC : Stage2Contracts b C A ctl uuidTryParse S ext) (name : String) (k : Nat)
    (hk : libsignalSessionCode.fnOff name + k = libsignalSessionCode.fnOff uuidTryParseName := by
      simp only [arm64_norm]) :
    subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr name + BitVec.ofNat 64 k) (uuidTryParseCodeSpec uuidTryParse) :=
  sub_ok_at_of_fnAddr hC.uuid_try_parse name k hk

theorem decode_varint_slow_ok_at (hC : Stage2Contracts b C A ctl uuidTryParse S ext) (name : String) (k : Nat)
    (hk : libsignalSessionCode.fnOff name + k = libsignalSessionCode.fnOff varintSlowName := by
      simp only [arm64_norm]) :
    subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr name + BitVec.ofNat 64 k) (decodeVarintSlowSpec A) :=
  sub_ok_at_of_fnAddr hC.decode_varint_slow name k hk

theorem alloc_zeroed_ok_at (hC : Stage2Contracts b C A ctl uuidTryParse S ext) (name : String) (k : Nat)
    (hk : libsignalSessionCode.fnOff name + k = libsignalSessionCode.fnOff allocZeroedName := by
      simp only [arm64_norm]) :
    subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr name + BitVec.ofNat 64 k) (rustAllocZeroedSpec A) :=
  sub_ok_at_of_fnAddr hC.alloc_zeroed name k hk

theorem decode_state_empty_ok_at (hC : Stage2Contracts b C A ctl uuidTryParse S ext) (name : String) (k : Nat)
    (hk : libsignalSessionCode.fnOff name + k = libsignalSessionCode.fnOff decodeStateName := by
      simp only [arm64_norm]) :
    subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr name + BitVec.ofNat 64 k) (decodeStateEmptySpec A) :=
  sub_ok_at_of_fnAddr hC.decode_state_empty name k hk

theorem aes_enc_ok_at (hC : Stage2Contracts b C A ctl uuidTryParse S ext) (name : String) (k : Nat)
    (hk : libsignalSessionCode.fnOff name + k = libsignalSessionCode.fnOff aesEncName := by
      simp only [arm64_norm]) :
    subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr name + BitVec.ofNat 64 k) (aesEncSpec C.E A) :=
  sub_ok_at_of_fnAddr hC.aes_enc name k hk

theorem aes_dec_ok_at (hC : Stage2Contracts b C A ctl uuidTryParse S ext) (name : String) (k : Nat)
    (hk : libsignalSessionCode.fnOff name + k = libsignalSessionCode.fnOff aesDecName := by
      simp only [arm64_norm]) :
    subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr name + BitVec.ofNat 64 k) (aesDecSpec C.D A) :=
  sub_ok_at_of_fnAddr hC.aes_dec name k hk

theorem format_inner_ok_at (hC : Stage2Contracts b C A ctl uuidTryParse S ext) (name : String) (k : Nat)
    (hk : libsignalSessionCode.fnOff name + k = libsignalSessionCode.fnOff formatInnerName := by
      simp only [arm64_norm]) :
    subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr name + BitVec.ofNat 64 k) (formatInnerSpec A) :=
  sub_ok_at_of_fnAddr hC.format_inner name k hk

theorem fmt_write_ok_at (hC : Stage2Contracts b C A ctl uuidTryParse S ext) (name : String) (k : Nat)
    (hk : libsignalSessionCode.fnOff name + k = libsignalSessionCode.fnOff fmtWriteName := by
      simp only [arm64_norm]) :
    subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr name + BitVec.ofNat 64 k) (fmtWriteSpec A) :=
  sub_ok_at_of_fnAddr hC.fmt_write name k hk

theorem decode_error_from_ok_at (hC : Stage2Contracts b C A ctl uuidTryParse S ext) (name : String) (k : Nat)
    (hk : libsignalSessionCode.fnOff name + k = libsignalSessionCode.fnOff decodeErrorFromName := by
      simp only [arm64_norm]) :
    subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr name + BitVec.ofNat 64 k) (decodeErrorFromSpec A) :=
  sub_ok_at_of_fnAddr hC.decode_error_from name k hk

theorem decode_error_push_ok_at (hC : Stage2Contracts b C A ctl uuidTryParse S ext) (name : String) (k : Nat)
    (hk : libsignalSessionCode.fnOff name + k = libsignalSessionCode.fnOff decodeErrorPushName := by
      simp only [arm64_norm]) :
    subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr name + BitVec.ofNat 64 k) (decodeErrorPushSpec A) :=
  sub_ok_at_of_fnAddr hC.decode_error_push name k hk

theorem panic_at_vec_remove_assert_failed (hC : Stage2Contracts b C A ctl uuidTryParse S ext)
    (name : String) (k : Nat)
    (hk : libsignalSessionCode.fnOff name + k =
      libsignalSessionCode.fnOff vecRemoveAssertFailedName := by simp only [arm64_norm]) :
    (tripleRatchetProgAtExt b ext).externAt?
      ((tripleRatchetProgAtExt b ext).fnAddr name + BitVec.ofNat 64 k) = some Rust.panicked :=
  panic_at_vec_remove_assert_failed_ext b ext hC.vec_remove_assert_failed_panics name k hk

theorem to_trap {parse : UuidParser} (hC : Stage2Contracts b C A ctl parse S ext) :
    Stage2Contracts_trap b C A parse S ext where
  toAllocContracts := hC.toAllocContracts
  black_box := hC.black_box
  compress256 := hC.compress256
  dh := hC.dh
  pub_from_secret := hC.pub_from_secret
  static_drop := hC.static_drop
  shared_drop := hC.shared_drop
  uuid_try_parse := hC.uuid_try_parse
  decode_varint_slow := hC.decode_varint_slow
  alloc_zeroed := hC.alloc_zeroed
  decode_state_empty := hC.decode_state_empty
  aes_enc := hC.aes_enc
  aes_dec := hC.aes_dec
  format_inner := hC.format_inner
  fmt_write := hC.fmt_write
  decode_error_from := hC.decode_error_from
  decode_error_push := hC.decode_error_push
  vec_remove_assert_failed_panics := hC.vec_remove_assert_failed_panics

theorem _root_.CryptoVerification.LibsignalTripleRatchet.Stage2Contracts_trap.of_tripleRatchetProgAt_trap
    (b : BitVec 64) (C : Crypto) (A : RustAlloc)
    (S : SpqrModel) (abs : String → Option (State → State))
    (hHooks : TripleRatchetHooks C A S abs) :
    Stage2Contracts_trap b C A uuidTryParse S (trTrapExterns C abs) where
  toAllocContracts := AllocContracts.of_tripleRatchetProgAt_trap b C A abs hHooks.alloc
  black_box := by
    simpa only [BitVec.ofNat_eq_ofNat, BitVec.add_zero] using
      CryptoVerification.LibsignalTripleRatchet.black_box_ok_at_trap b C abs blackBoxName 0 (Nat.add_zero _)
  compress256 := by
    simpa only [BitVec.ofNat_eq_ofNat, BitVec.add_zero] using
      CryptoVerification.LibsignalTripleRatchet.compress256_ok_at_trap b C abs compress256Name 0 (Nat.add_zero _)
  dh := by
    simpa only [BitVec.ofNat_eq_ofNat, BitVec.add_zero] using
      CryptoVerification.LibsignalTripleRatchet.dh_ok_at_trap b C abs dhName 0 (Nat.add_zero _)
  pub_from_secret := by
    simpa only [BitVec.ofNat_eq_ofNat, BitVec.add_zero] using
      CryptoVerification.LibsignalTripleRatchet.pub_from_secret_ok_at_trap b C abs pubFromSecretName 0 (Nat.add_zero _)
  static_drop := by
    simpa only [BitVec.ofNat_eq_ofNat, BitVec.add_zero] using
      CryptoVerification.LibsignalTripleRatchet.static_drop_ok_at_trap b C abs staticDropName 0 (Nat.add_zero _)
  shared_drop := by
    simpa only [BitVec.ofNat_eq_ofNat, BitVec.add_zero] using
      CryptoVerification.LibsignalTripleRatchet.shared_drop_ok_at_trap b C abs sharedDropName 0 (Nat.add_zero _)
  uuid_try_parse := by
    simpa only [BitVec.ofNat_eq_ofNat, BitVec.add_zero] using
      CryptoVerification.LibsignalTripleRatchet.uuid_try_parse_ok_at_trap b C abs uuidTryParseName 0 (Nat.add_zero _)
  decode_varint_slow := by
    simpa only [BitVec.ofNat_eq_ofNat, BitVec.add_zero] using
      CryptoVerification.LibsignalTripleRatchet.decode_varint_slow_ok_at_trap b C A abs
        hHooks.alloc varintSlowName 0 (Nat.add_zero _)
  alloc_zeroed := by
    simpa only [BitVec.ofNat_eq_ofNat, BitVec.add_zero] using
      CryptoVerification.LibsignalTripleRatchet.alloc_zeroed_ok_at_trap b C A abs
        hHooks.allocZeroed allocZeroedName 0 (Nat.add_zero _)
  decode_state_empty := by
    simpa only [BitVec.ofNat_eq_ofNat, BitVec.add_zero] using
      CryptoVerification.LibsignalTripleRatchet.decode_state_empty_ok_at_trap b C A abs
        decodeStateName 0 (Nat.add_zero _)
  aes_enc := by
    simpa only [BitVec.ofNat_eq_ofNat, BitVec.add_zero] using
      CryptoVerification.LibsignalTripleRatchet.aes_enc_ok_at_trap b C A abs
        hHooks.aesEnc aesEncName 0 (Nat.add_zero _)
  aes_dec := by
    simpa only [BitVec.ofNat_eq_ofNat, BitVec.add_zero] using
      CryptoVerification.LibsignalTripleRatchet.aes_dec_ok_at_trap b C A abs
        hHooks.aesDec aesDecName 0 (Nat.add_zero _)
  format_inner := by
    simpa only [BitVec.ofNat_eq_ofNat, BitVec.add_zero] using
      CryptoVerification.LibsignalTripleRatchet.format_inner_ok_at_trap b C A abs
        hHooks.formatInner formatInnerName 0 (Nat.add_zero _)
  fmt_write := by
    simpa only [BitVec.ofNat_eq_ofNat, BitVec.add_zero] using
      CryptoVerification.LibsignalTripleRatchet.fmt_write_ok_at_trap b C A abs
        hHooks.fmtWrite fmtWriteName 0 (Nat.add_zero _)
  decode_error_from := by
    simpa only [BitVec.ofNat_eq_ofNat, BitVec.add_zero] using
      CryptoVerification.LibsignalTripleRatchet.decode_error_from_ok_at_trap b C A abs
        hHooks.alloc decodeErrorFromName 0 (Nat.add_zero _)
  decode_error_push := by
    simpa only [BitVec.ofNat_eq_ofNat, BitVec.add_zero] using
      CryptoVerification.LibsignalTripleRatchet.decode_error_push_ok_at_trap b C A abs
        hHooks.alloc decodeErrorPushName 0 (Nat.add_zero _)
  vec_remove_assert_failed_panics := by
    simpa only [BitVec.ofNat_eq_ofNat, BitVec.add_zero] using
      CryptoVerification.LibsignalTripleRatchet.panic_at_vec_remove_assert_failed_trap b C abs
        vecRemoveAssertFailedName 0 (Nat.add_zero _)

theorem _root_.CryptoVerification.LibsignalTripleRatchet.Stage2Contracts_trap.of_tripleRatchetProgAt'_trap
    {b : BitVec 64} {C : Crypto} {A : RustAlloc}
    {S : SpqrModel} {abs : String → Option (State → State)}
    (hHooks : TripleRatchetHooks C A S abs) :
    Stage2Contracts_trap b C A uuidTryParse S (trTrapExterns C abs) :=
  Stage2Contracts_trap.of_tripleRatchetProgAt_trap b C A S abs hHooks

theorem of_tripleRatchetProgAt (b : BitVec 64) (C : Crypto) (A : RustAlloc) (ctl : BitVec 64)
    (S : SpqrModel) (abs : String → Option (State → State))
    (hHooks : TripleRatchetHooks C A S abs) :
    Stage2Contracts b C A ctl uuidTryParse S (tripleRatchetExterns C ctl abs) where
  toAllocContracts := AllocContracts.of_tripleRatchetProgAt b C A ctl abs hHooks.alloc
  black_box := by
    change subroutine_ok (tripleRatchetProgAt b C ctl abs) ((tripleRatchetProgAt b C ctl abs).fnAddr blackBoxName) _
    rw [← (trapsOnly_trTrap_kit b C ctl abs).fnAddr blackBoxName]
    exact subroutine_ok_kit_of_trTrap (Stage2Contracts_trap.of_tripleRatchetProgAt_trap b C A S abs hHooks).black_box
  compress256 := by
    change subroutine_ok (tripleRatchetProgAt b C ctl abs) ((tripleRatchetProgAt b C ctl abs).fnAddr compress256Name) _
    rw [← (trapsOnly_trTrap_kit b C ctl abs).fnAddr compress256Name]
    exact subroutine_ok_kit_of_trTrap (Stage2Contracts_trap.of_tripleRatchetProgAt_trap b C A S abs hHooks).compress256
  dh := by
    change subroutine_ok (tripleRatchetProgAt b C ctl abs) ((tripleRatchetProgAt b C ctl abs).fnAddr dhName) _
    rw [← (trapsOnly_trTrap_kit b C ctl abs).fnAddr dhName]
    exact subroutine_ok_kit_of_trTrap (Stage2Contracts_trap.of_tripleRatchetProgAt_trap b C A S abs hHooks).dh
  pub_from_secret := by
    change subroutine_ok (tripleRatchetProgAt b C ctl abs) ((tripleRatchetProgAt b C ctl abs).fnAddr pubFromSecretName) _
    rw [← (trapsOnly_trTrap_kit b C ctl abs).fnAddr pubFromSecretName]
    exact subroutine_ok_kit_of_trTrap (Stage2Contracts_trap.of_tripleRatchetProgAt_trap b C A S abs hHooks).pub_from_secret
  static_drop := by
    change subroutine_ok (tripleRatchetProgAt b C ctl abs) ((tripleRatchetProgAt b C ctl abs).fnAddr staticDropName) _
    rw [← (trapsOnly_trTrap_kit b C ctl abs).fnAddr staticDropName]
    exact subroutine_ok_kit_of_trTrap (Stage2Contracts_trap.of_tripleRatchetProgAt_trap b C A S abs hHooks).static_drop
  shared_drop := by
    change subroutine_ok (tripleRatchetProgAt b C ctl abs) ((tripleRatchetProgAt b C ctl abs).fnAddr sharedDropName) _
    rw [← (trapsOnly_trTrap_kit b C ctl abs).fnAddr sharedDropName]
    exact subroutine_ok_kit_of_trTrap (Stage2Contracts_trap.of_tripleRatchetProgAt_trap b C A S abs hHooks).shared_drop
  rng_fill := by
    simpa only [BitVec.ofNat_eq_ofNat, BitVec.add_zero] using
      CryptoVerification.LibsignalTripleRatchet.rng_fill_ok_at b C ctl abs rngFillName 0 (Nat.add_zero _)
  uuid_try_parse := by
    change subroutine_ok (tripleRatchetProgAt b C ctl abs) ((tripleRatchetProgAt b C ctl abs).fnAddr uuidTryParseName) _
    rw [← (trapsOnly_trTrap_kit b C ctl abs).fnAddr uuidTryParseName]
    exact subroutine_ok_kit_of_trTrap (Stage2Contracts_trap.of_tripleRatchetProgAt_trap b C A S abs hHooks).uuid_try_parse
  decode_varint_slow := by
    change subroutine_ok (tripleRatchetProgAt b C ctl abs) ((tripleRatchetProgAt b C ctl abs).fnAddr varintSlowName) _
    rw [← (trapsOnly_trTrap_kit b C ctl abs).fnAddr varintSlowName]
    exact subroutine_ok_kit_of_trTrap (Stage2Contracts_trap.of_tripleRatchetProgAt_trap b C A S abs hHooks).decode_varint_slow
  alloc_zeroed := by
    change subroutine_ok (tripleRatchetProgAt b C ctl abs) ((tripleRatchetProgAt b C ctl abs).fnAddr allocZeroedName) _
    rw [← (trapsOnly_trTrap_kit b C ctl abs).fnAddr allocZeroedName]
    exact subroutine_ok_kit_of_trTrap (Stage2Contracts_trap.of_tripleRatchetProgAt_trap b C A S abs hHooks).alloc_zeroed
  decode_state_empty := by
    change subroutine_ok (tripleRatchetProgAt b C ctl abs) ((tripleRatchetProgAt b C ctl abs).fnAddr decodeStateName) _
    rw [← (trapsOnly_trTrap_kit b C ctl abs).fnAddr decodeStateName]
    exact subroutine_ok_kit_of_trTrap (Stage2Contracts_trap.of_tripleRatchetProgAt_trap b C A S abs hHooks).decode_state_empty
  aes_enc := by
    change subroutine_ok (tripleRatchetProgAt b C ctl abs) ((tripleRatchetProgAt b C ctl abs).fnAddr aesEncName) _
    rw [← (trapsOnly_trTrap_kit b C ctl abs).fnAddr aesEncName]
    exact subroutine_ok_kit_of_trTrap (Stage2Contracts_trap.of_tripleRatchetProgAt_trap b C A S abs hHooks).aes_enc
  aes_dec := by
    change subroutine_ok (tripleRatchetProgAt b C ctl abs) ((tripleRatchetProgAt b C ctl abs).fnAddr aesDecName) _
    rw [← (trapsOnly_trTrap_kit b C ctl abs).fnAddr aesDecName]
    exact subroutine_ok_kit_of_trTrap (Stage2Contracts_trap.of_tripleRatchetProgAt_trap b C A S abs hHooks).aes_dec
  format_inner := by
    change subroutine_ok (tripleRatchetProgAt b C ctl abs) ((tripleRatchetProgAt b C ctl abs).fnAddr formatInnerName) _
    rw [← (trapsOnly_trTrap_kit b C ctl abs).fnAddr formatInnerName]
    exact subroutine_ok_kit_of_trTrap (Stage2Contracts_trap.of_tripleRatchetProgAt_trap b C A S abs hHooks).format_inner
  fmt_write := by
    change subroutine_ok (tripleRatchetProgAt b C ctl abs) ((tripleRatchetProgAt b C ctl abs).fnAddr fmtWriteName) _
    rw [← (trapsOnly_trTrap_kit b C ctl abs).fnAddr fmtWriteName]
    exact subroutine_ok_kit_of_trTrap (Stage2Contracts_trap.of_tripleRatchetProgAt_trap b C A S abs hHooks).fmt_write
  decode_error_from := by
    change subroutine_ok (tripleRatchetProgAt b C ctl abs) ((tripleRatchetProgAt b C ctl abs).fnAddr decodeErrorFromName) _
    rw [← (trapsOnly_trTrap_kit b C ctl abs).fnAddr decodeErrorFromName]
    exact subroutine_ok_kit_of_trTrap (Stage2Contracts_trap.of_tripleRatchetProgAt_trap b C A S abs hHooks).decode_error_from
  decode_error_push := by
    change subroutine_ok (tripleRatchetProgAt b C ctl abs) ((tripleRatchetProgAt b C ctl abs).fnAddr decodeErrorPushName) _
    rw [← (trapsOnly_trTrap_kit b C ctl abs).fnAddr decodeErrorPushName]
    exact subroutine_ok_kit_of_trTrap (Stage2Contracts_trap.of_tripleRatchetProgAt_trap b C A S abs hHooks).decode_error_push
  vec_remove_assert_failed_panics := by
    have h := (Stage2Contracts_trap.of_tripleRatchetProgAt_trap b C A S abs hHooks).vec_remove_assert_failed_panics
    change (tripleRatchetProgAt b C ctl abs).externAt? ((tripleRatchetProgAt b C ctl abs).fnAddr vecRemoveAssertFailedName) = _
    rw [← (trapsOnly_trTrap_kit b C ctl abs).fnAddr vecRemoveAssertFailedName]
    rcases (trapsOnly_trTrap_kit b C ctl abs).hook ((trTrapProgAt b C abs).fnAddr vecRemoveAssertFailedName) with
      heq | ⟨f, hf, ht⟩
    · exact heq.symm.trans h
    · cases h.symm.trans hf
      exact False.elim (ht default (ProofLib.Variant.OutcomeStatus.of_panicked rfl))

theorem of_tripleRatchetProgAt' {b : BitVec 64} {C : Crypto} {A : RustAlloc} {ctl : BitVec 64}
    {S : SpqrModel} {abs : String → Option (State → State)}
    (hHooks : TripleRatchetHooks C A S abs) :
    Stage2Contracts b C A ctl uuidTryParse S (tripleRatchetExterns C ctl abs) :=
  of_tripleRatchetProgAt b C A ctl S abs hHooks

end Stage2Contracts

/-! ## Image-invariant and configurable-stack contract bundles -/

/-- Augment a `Spec α` with `stackAt s.sp hookStack` in `pre` and `stackAt s0.sp hookStack` in `post`. -/
def withStack {α : Type} (spec : Spec α) (hookStack : Nat := extHookStack) : Spec α :=
  { spec with
    pre := fun x s => spec.pre x s ∗ stackAt s.sp hookStack
    post := fun x s0 sf => spec.post x s0 sf ∗ stackAt s0.sp hookStack }

theorem subroutine_ok_inImage_of_subroutine_ok {α : Type} {P : Program} {addr : BitVec 64}
    {spec : Spec α} (img : Obj.Image) (h : subroutine_ok P addr spec) :
    subroutine_ok P addr (spec.inImage img) := by
  refine subroutine_ok_outcome_intro fun x R s0 hpc hrun hpre hal => ?_
  dsimp only [Spec.inImage] at hpre
  rw [sepConj_assoc, satisfies_pure_sepConj] at hpre
  exact h.mono_outcome x R s0 hpc hrun hpre.2 hal (fun _ hout => hout)

theorem subroutine_ok_withStack_of_subroutine_ok {α : Type} {P : Program} {addr : BitVec 64}
    {spec : Spec α} (h : subroutine_ok P addr spec) (hookStack : Nat)
    (hpan : ∀ x s0 sf, spec.onPanic x s0 sf = ⌜False⌝ := by intros; rfl)
    (hex : ∀ x code s0 sf, spec.onExit x code s0 sf = ⌜False⌝ := by intros; rfl)
    (hoom : ∀ x s0 sf, spec.onOom x s0 sf = ⌜False⌝ := by intros; rfl) :
    subroutine_ok P addr (withStack spec hookStack) := by
  refine subroutine_ok_outcome_intro fun x R s0 hpc hrun hpre hal => ?_
  dsimp only [withStack] at hpre
  rw [sepConj_assoc] at hpre
  refine h.mono_outcome x (stackAt s0.sp hookStack ∗ R) s0 hpc hrun hpre hal fun sf hout => ?_
  rcases hout with ⟨hret, hcc, hpost⟩ | ⟨_, hpan_sat⟩ | ⟨code, _, hex_sat⟩ | ⟨_, hoom_sat⟩
  · refine Or.inl ⟨hret, hcc, ?_⟩
    dsimp only [withStack]
    rwa [sepConj_assoc]
  · rw [hpan x s0 sf, satisfies_pure_sepConj] at hpan_sat
    exact False.elim hpan_sat.1
  · rw [hex x code s0 sf, satisfies_pure_sepConj] at hex_sat
    exact False.elim hex_sat.1
  · rw [hoom x s0 sf, satisfies_pure_sepConj] at hoom_sat
    exact False.elim hoom_sat.1

/-- `rustAllocSpec A` with configurable stack budget `hookStack` (`= rustAllocSpec A` at `allocHookStack`). -/
def rustAllocSpecWithStack (A : RustAlloc) (hookStack : Nat := extHookStack) : Spec (Nat × Nat) where
  pre := fun (size, align) s =>
    ⌜(s.readReg64 .x0).toNat = size ∧ (s.readReg64 .x1).toNat = align ∧ LayoutOk size align⌝ ∗
      A.pool ∗ stackAt s.sp hookStack
  post := fun (size, align) s0 sf =>
    A.pool ∗ stackAt s0.sp hookStack ∗
      (if sf.readReg64 .x0 = 0 then ⌜sf.trace = s0.trace ++ [allocFailedEvent]⌝
       else ⌜(sf.readReg64 .x0).toNat % align = 0 ∧ sf.trace = s0.trace⌝ ∗
         A.live (sf.readReg64 .x0) size align ∗ memRegion (sf.readReg64 .x0) size)

/-- `rustDeallocSpec A` with configurable stack budget `hookStack` (`= rustDeallocSpec A` at `allocHookStack`). -/
def rustDeallocSpecWithStack (A : RustAlloc)
    (hookStack : Nat := extHookStack) : Spec (BitVec 64 × Nat × Nat) where
  pre := fun (p, size, align) s =>
    ⌜s.readReg64 .x0 = p ∧ (s.readReg64 .x1).toNat = size ∧ (s.readReg64 .x2).toNat = align⌝ ∗
      A.pool ∗ A.live p size align ∗ memRegion p size ∗ stackAt s.sp hookStack
  post := fun _ s0 sf => ⌜sf.trace = s0.trace⌝ ∗ A.pool ∗ stackAt s0.sp hookStack

/-- `rustDeallocSpec A` with `LayoutOk size align` in `pre` and configurable stack budget `hookStack`,
matching `Externs.deallocSpec` at both `A_layout` and `A₀`. -/
def rustDeallocExternSpecWithStack (A : RustAlloc)
    (hookStack : Nat := extHookStack) : Spec (BitVec 64 × Nat × Nat) where
  pre := fun (p, size, align) s =>
    ⌜s.readReg64 .x0 = p ∧ (s.readReg64 .x1).toNat = size ∧ (s.readReg64 .x2).toNat = align ∧
      LayoutOk size align⌝ ∗
      A.pool ∗ A.live p size align ∗ memRegion p size ∗ stackAt s.sp hookStack
  post := fun _ s0 sf => ⌜sf.trace = s0.trace⌝ ∗ A.pool ∗ stackAt s0.sp hookStack

/-- `rustReallocSpec A` with configurable stack budget `hookStack` (`= rustReallocSpec A` at `allocHookStack`). -/
def rustReallocSpecWithStack (A : RustAlloc)
    (hookStack : Nat := extHookStack) :
    Spec (BitVec 64 × Nat × Nat × Nat × List (BitVec 8)) where
  pre := fun (p, old, align, new, bs) s =>
    ⌜s.readReg64 .x0 = p ∧ (s.readReg64 .x1).toNat = old ∧ (s.readReg64 .x2).toNat = align ∧
      (s.readReg64 .x3).toNat = new ∧ LayoutOk new align ∧ bs.length ≤ old ∧ bs.length ≤ new⌝ ∗
      A.pool ∗ A.live p old align ∗ (p ↦ₛ bs) ∗
      memRegion (p + BitVec.ofNat 64 bs.length) (old - bs.length) ∗ stackAt s.sp hookStack
  post := fun (p, old, align, new, bs) s0 sf =>
    A.pool ∗ stackAt s0.sp hookStack ∗
      (if sf.readReg64 .x0 = 0 then
        ⌜sf.trace = s0.trace ++ [allocFailedEvent]⌝ ∗
          A.live p old align ∗ (p ↦ₛ bs) ∗
          memRegion (p + BitVec.ofNat 64 bs.length) (old - bs.length)
       else
        ⌜(sf.readReg64 .x0).toNat % align = 0 ∧ sf.trace = s0.trace⌝ ∗
          A.live (sf.readReg64 .x0) new align ∗ (sf.readReg64 .x0 ↦ₛ bs) ∗
          memRegion (sf.readReg64 .x0 + BitVec.ofNat 64 bs.length) (new - bs.length))

/-- `rustReallocSpec A` with `LayoutOk old align` in `pre` and configurable stack budget `hookStack`,
matching `Externs.reallocSpec` at both `A_layout` and `A₀`. -/
def rustReallocExternSpecWithStack (A : RustAlloc)
    (hookStack : Nat := extHookStack) :
    Spec (BitVec 64 × Nat × Nat × Nat × List (BitVec 8)) where
  pre := fun (p, old, align, new, bs) s =>
    ⌜s.readReg64 .x0 = p ∧ (s.readReg64 .x1).toNat = old ∧ (s.readReg64 .x2).toNat = align ∧
      (s.readReg64 .x3).toNat = new ∧ LayoutOk old align ∧ LayoutOk new align ∧
      bs.length ≤ old ∧ bs.length ≤ new⌝ ∗
      A.pool ∗ A.live p old align ∗ (p ↦ₛ bs) ∗
      memRegion (p + BitVec.ofNat 64 bs.length) (old - bs.length) ∗ stackAt s.sp hookStack
  post := (rustReallocSpecWithStack A hookStack).post

theorem rustAllocSpecWithStack_eq_rustAllocSpec (A : RustAlloc) :
    rustAllocSpecWithStack A allocHookStack = rustAllocSpec A := rfl

theorem rustDeallocSpecWithStack_eq_rustDeallocSpec (A : RustAlloc) :
    rustDeallocSpecWithStack A allocHookStack = rustDeallocSpec A := rfl

theorem rustReallocSpecWithStack_eq_rustReallocSpec (A : RustAlloc) :
    rustReallocSpecWithStack A allocHookStack = rustReallocSpec A := rfl

theorem rustAllocWithStack_of_rustAlloc {P : Program} {addr : BitVec 64} {A : RustAlloc}
    {hookStack : Nat} (h : subroutine_ok P addr (rustAllocSpec A))
    (hle : allocHookStack ≤ hookStack := by decide)
    (hmax : hookStack ≤ 2 ^ 64 := by decide) :
    subroutine_ok P addr (rustAllocSpecWithStack A hookStack) := by
  refine subroutine_ok_outcome_intro fun ⟨size, align⟩ R s0 hpc hrun hpre hal => ?_
  have hsplit : stackAt s0.sp hookStack =
      memRegion (s0.sp - BitVec.ofNat 64 hookStack) (hookStack - allocHookStack) ∗
        stackAt s0.sp allocHookStack := by
    have h1 := stackAt_split_bottom s0.sp allocHookStack (hookStack - allocHookStack) (by omega)
    rwa [Nat.add_sub_of_le hle] at h1
  let R' : SepProp := memRegion (s0.sp - BitVec.ofNat 64 hookStack) (hookStack - allocHookStack) ∗ R
  have hpre' : s0.mem ⊨ (rustAllocSpec A).pre (size, align) s0 ∗ R' := by
    dsimp only [rustAllocSpecWithStack, rustAllocSpec, R'] at hpre ⊢
    rw [hsplit] at hpre
    ac_nf at hpre ⊢
  refine h.mono_outcome (size, align) R' s0 hpc hrun hpre' hal fun sf hout => ?_
  rcases hout with ⟨hret, hcc, hpost⟩ | ⟨_, hpan⟩ | ⟨code, _, hex⟩ | ⟨_, hoom⟩
  · refine Or.inl ⟨hret, hcc, ?_⟩
    dsimp only [rustAllocSpecWithStack, rustAllocSpec, R'] at hpost ⊢
    rw [hsplit]
    ac_nf at hpost ⊢
  · dsimp only [rustAllocSpec] at hpan
    rw [satisfies_pure_sepConj] at hpan
    exact False.elim hpan.1
  · dsimp only [rustAllocSpec] at hex
    rw [satisfies_pure_sepConj] at hex
    exact False.elim hex.1
  · dsimp only [rustAllocSpec] at hoom
    rw [satisfies_pure_sepConj] at hoom
    exact False.elim hoom.1

theorem rustDeallocExternWithStack_of_rustDealloc {P : Program} {addr : BitVec 64} {A : RustAlloc}
    {hookStack : Nat} (h : subroutine_ok P addr (rustDeallocSpec A))
    (hle : allocHookStack ≤ hookStack := by decide)
    (hmax : hookStack ≤ 2 ^ 64 := by decide) :
    subroutine_ok P addr (rustDeallocExternSpecWithStack A hookStack) := by
  refine subroutine_ok_outcome_intro fun ⟨p, size, align⟩ R s0 hpc hrun hpre hal => ?_
  have hsplit : stackAt s0.sp hookStack =
      memRegion (s0.sp - BitVec.ofNat 64 hookStack) (hookStack - allocHookStack) ∗
        stackAt s0.sp allocHookStack := by
    have h1 := stackAt_split_bottom s0.sp allocHookStack (hookStack - allocHookStack) (by omega)
    rwa [Nat.add_sub_of_le hle] at h1
  let R' : SepProp := memRegion (s0.sp - BitVec.ofNat 64 hookStack) (hookStack - allocHookStack) ∗ R
  have hpre' : s0.mem ⊨ (rustDeallocSpec A).pre (p, size, align) s0 ∗ R' := by
    dsimp only [rustDeallocExternSpecWithStack, rustDeallocSpec, R'] at hpre ⊢
    rw [hsplit] at hpre
    simp only [sepConj_assoc, satisfies_pure_sepConj] at hpre ⊢
    rcases hpre with ⟨hpure, hmem⟩
    refine ⟨⟨hpure.1, hpure.2.1, hpure.2.2.1⟩, ?_⟩
    ac_nf at hmem ⊢
  refine h.mono_outcome (p, size, align) R' s0 hpc hrun hpre' hal fun sf hout => ?_
  rcases hout with ⟨hret, hcc, hpost⟩ | ⟨_, hpan⟩ | ⟨code, _, hex⟩ | ⟨_, hoom⟩
  · refine Or.inl ⟨hret, hcc, ?_⟩
    dsimp only [rustDeallocExternSpecWithStack, rustDeallocSpec, R'] at hpost ⊢
    rw [hsplit]
    ac_nf at hpost ⊢
  · dsimp only [rustDeallocSpec] at hpan
    rw [satisfies_pure_sepConj] at hpan
    exact False.elim hpan.1
  · dsimp only [rustDeallocSpec] at hex
    rw [satisfies_pure_sepConj] at hex
    exact False.elim hex.1
  · dsimp only [rustDeallocSpec] at hoom
    rw [satisfies_pure_sepConj] at hoom
    exact False.elim hoom.1

theorem rustReallocExternWithStack_of_rustRealloc {P : Program} {addr : BitVec 64} {A : RustAlloc}
    {hookStack : Nat} (h : subroutine_ok P addr (rustReallocSpec A))
    (hle : allocHookStack ≤ hookStack := by decide)
    (hmax : hookStack ≤ 2 ^ 64 := by decide) :
    subroutine_ok P addr (rustReallocExternSpecWithStack A hookStack) := by
  refine subroutine_ok_outcome_intro fun ⟨p, old, align, new, bs⟩ R s0 hpc hrun hpre hal => ?_
  have hsplit : stackAt s0.sp hookStack =
      memRegion (s0.sp - BitVec.ofNat 64 hookStack) (hookStack - allocHookStack) ∗
        stackAt s0.sp allocHookStack := by
    have h1 := stackAt_split_bottom s0.sp allocHookStack (hookStack - allocHookStack) (by omega)
    rwa [Nat.add_sub_of_le hle] at h1
  let R' : SepProp := memRegion (s0.sp - BitVec.ofNat 64 hookStack) (hookStack - allocHookStack) ∗ R
  have hpre' : s0.mem ⊨ (rustReallocSpec A).pre (p, old, align, new, bs) s0 ∗ R' := by
    dsimp only [rustReallocExternSpecWithStack, rustReallocSpec, R'] at hpre ⊢
    rw [hsplit] at hpre
    simp only [sepConj_assoc, satisfies_pure_sepConj] at hpre ⊢
    rcases hpre with ⟨hpure, hmem⟩
    refine ⟨⟨hpure.1, hpure.2.1, hpure.2.2.1, hpure.2.2.2.1,
      hpure.2.2.2.2.2.1, hpure.2.2.2.2.2.2⟩, ?_⟩
    ac_nf at hmem ⊢
  refine h.mono_outcome (p, old, align, new, bs) R' s0 hpc hrun hpre' hal fun sf hout => ?_
  rcases hout with ⟨hret, hcc, hpost⟩ | ⟨_, hpan⟩ | ⟨code, _, hex⟩ | ⟨_, hoom⟩
  · refine Or.inl ⟨hret, hcc, ?_⟩
    dsimp only [rustReallocExternSpecWithStack, rustReallocSpecWithStack, rustReallocSpec, R'] at hpost ⊢
    rw [hsplit]
    ac_nf at hpost ⊢
  · dsimp only [rustReallocSpec] at hpan
    rw [satisfies_pure_sepConj] at hpan
    exact False.elim hpan.1
  · dsimp only [rustReallocSpec] at hex
    rw [satisfies_pure_sepConj] at hex
    exact False.elim hex.1
  · dsimp only [rustReallocSpec] at hoom
    rw [satisfies_pure_sepConj] at hoom
    exact False.elim hoom.1

/-- `decodeErrorFromSpec A` with configurable stack budget `hookStack` (`= decodeErrorFromSpec A` at `decodeErrorHookStack`). -/
def decodeErrorFromSpecWithStack (A : RustAlloc)
    (hookStack : Nat := extHookStack) : Spec (BitVec 64 × BitVec 64) where
  pre := fun (k, w) s =>
    ⌜s.readReg64 .x0 = k ∧ KindNoHeap w⌝ ∗ (k ↦₆₄ w) ∗ memRegion (k + 8#64) 40 ∗
      A.pool ∗ stackAt s.sp hookStack
  post := fun (k, _) s0 sf =>
    ⌜sf.readReg64 .x0 ≠ 0#64 ∧ sf.trace = s0.trace⌝ ∗
      decodeErrorAtStackLen A (sf.readReg64 .x0) 0 ∗
      memRegion k 48 ∗ A.pool ∗ stackAt s0.sp hookStack
  onPanic := fun _ s0 sf => ⌜allocFailedIn s0 sf ∧ s0.trace <+: sf.trace⌝ ∗ anyHeap

/-- `decodeErrorPushSpec A` with configurable stack budget `hookStack` (`= decodeErrorPushSpec A` at `decodeErrorHookStack`). -/
def decodeErrorPushSpecWithStack (A : RustAlloc)
    (hookStack : Nat := extHookStack) : Spec (BitVec 64 × BitVec 64 × Nat) where
  pre := fun (d, e, n) s =>
    ⌜s.readReg64 .x0 = d ∧ n < 2 ^ 32⌝ ∗ (d ↦₆₄ e) ∗
      decodeErrorAtStackLen A e n ∗
      A.pool ∗ stackAt s.sp hookStack
  post := fun (d, e, n) s0 sf =>
    ⌜sf.trace = s0.trace⌝ ∗ (d ↦₆₄ e) ∗
      decodeErrorAtStackLen A e (n + 1) ∗
      A.pool ∗ stackAt s0.sp hookStack
  onPanic := fun _ s0 sf => ⌜allocFailedIn s0 sf ∧ s0.trace <+: sf.trace⌝ ∗ anyHeap

/-- `decodeErrorPushSpecWithStack` existentializing the updated box pointer `e'` at slot `d` in `post`. -/
def decodeErrorPushExternSpecWithStack (A : RustAlloc)
    (hookStack : Nat := extHookStack) : Spec (BitVec 64 × BitVec 64 × Nat) where
  pre := fun (d, e, n) s =>
    ⌜s.readReg64 .x0 = d ∧ e ≠ 0#64 ∧ n < 2 ^ 32⌝ ∗ (d ↦₆₄ e) ∗
      decodeErrorAtStackLen A e n ∗
      A.pool ∗ stackAt s.sp hookStack
  post := fun (d, _, n) s0 sf =>
    ⌜sf.trace = s0.trace⌝ ∗
      (∃∗ e' : BitVec 64, ⌜e' ≠ 0#64⌝ ∗ (d ↦₆₄ e') ∗
        decodeErrorAtStackLen A e' (n + 1)) ∗
      A.pool ∗ stackAt s0.sp hookStack
  onPanic := fun _ s0 sf => ⌜allocFailedIn s0 sf ∧ s0.trace <+: sf.trace⌝ ∗ anyHeap

theorem decodeErrorPushExtern_of_decodeErrorPush
    {P : Program} {addr : BitVec 64} {A : RustAlloc} {hookStack : Nat}
    (h : subroutine_ok P addr (decodeErrorPushSpecWithStack A hookStack)) :
    subroutine_ok P addr (decodeErrorPushExternSpecWithStack A hookStack) := by
  refine subroutine_ok_outcome_intro fun ⟨d, e, n⟩ R s0 hpc hrun hpre hal => ?_
  simp only [decodeErrorPushExternSpecWithStack, sepConj_assoc, satisfies_pure_sepConj] at hpre
  rcases hpre with ⟨⟨hx0, he_ne, hn⟩, hmem⟩
  have hpre' : s0.mem ⊨ (decodeErrorPushSpecWithStack A hookStack).pre (d, e, n) s0 ∗ R := by
    simp only [decodeErrorPushSpecWithStack, sepConj_assoc, satisfies_pure_sepConj]
    exact ⟨⟨hx0, hn⟩, hmem⟩
  refine h.mono_outcome (d, e, n) R s0 hpc hrun hpre' hal fun sf hout => ?_
  rcases hout with ⟨hret, hcc, hpost⟩ | hpan | hex
  · refine Or.inl ⟨hret, hcc, ?_⟩
    simp only [decodeErrorPushSpecWithStack, decodeErrorPushExternSpecWithStack,
      sepConj_assoc, sepExists_sepConj_left, satisfies_pure_sepConj, satisfies_sepExists] at hpost ⊢
    exact ⟨hpost.1, e, he_ne, hpost.2⟩
  · exact Or.inr (Or.inl hpan)
  · exact Or.inr (Or.inr hex)

/-- `decodeVarintSlowSpec A` with configurable stack budget `hookStack` (`= decodeVarintSlowSpec A` at `varintSlowStack`). -/
def decodeVarintSlowSpecWithStack (A : RustAlloc)
    (hookStack : Nat := extHookStack) :
    Spec (BitVec 64 × BitVec 64 × BitVec 64 × List (BitVec 8)) where
  pre := fun (slotA, slot, ptr, bs) s =>
    ⌜s.readReg64 .x0 = slotA ∧ bs.length < 2 ^ 64⌝ ∗
      (slotA ↦₆₄ slot) ∗ (slot ↦₆₄ ptr) ∗ ((slot + 8#64) ↦₆₄ BitVec.ofNat 64 bs.length) ∗
      (ptr ↦ₛ bs) ∗ A.pool ∗ stackAt s.sp hookStack
  post := fun (slotA, slot, ptr, bs) s0 sf =>
    ⌜sf.trace = s0.trace⌝ ∗
      (slotA ↦₆₄ slot) ∗ (ptr ↦ₛ bs) ∗ A.pool ∗ stackAt s0.sp hookStack ∗
      match varintSlow bs with
      | some (v, k) =>
        ⌜sf.readReg64 .x0 = 0#64 ∧ sf.readReg64 .x1 = v⌝ ∗
          (slot ↦₆₄ (ptr + BitVec.ofNat 64 k)) ∗
          ((slot + 8#64) ↦₆₄ BitVec.ofNat 64 (bs.length - k))
      | none =>
        ⌜sf.readReg64 .x0 = 1#64 ∧ sf.readReg64 .x1 ≠ 0#64⌝ ∗
          decodeErrorAtStackLen A (sf.readReg64 .x1) 0 ∗
          (slot ↦₆₄ (ptr + BitVec.ofNat 64 (min 10 bs.length))) ∗
          ((slot + 8#64) ↦₆₄ BitVec.ofNat 64 (bs.length - min 10 bs.length))
  onPanic := fun _ s0 sf => ⌜allocFailedIn s0 sf ∧ s0.trace <+: sf.trace⌝ ∗ anyHeap

private theorem satisfies_anyHeap_frame {m : Memory} {P F R : SepProp}
    (h : m ⊨ (P ∗ anyHeap) ∗ F ∗ R) :
    m ⊨ (P ∗ anyHeap) ∗ R := by
  have h1 : (P ∗ anyHeap) ∗ F ∗ R ⊢ (P ∗ anyHeap) ∗ R := by
    rw [sepConj_assoc P anyHeap (F ∗ R), ← sepConj_assoc anyHeap F R, sepConj_assoc P anyHeap R]
    exact sepConj_mono_right (sepConj_mono_left (entails_anyHeap (anyHeap ∗ F)))
  exact Satisfies.mono h1 h

theorem decodeErrorFromWithStack_of_decodeErrorFrom {P : Program} {addr : BitVec 64} {A : RustAlloc}
    {hookStack : Nat} (h : subroutine_ok P addr (decodeErrorFromSpec A))
    (hle : decodeErrorHookStack ≤ hookStack := by decide)
    (hmax : hookStack ≤ 2 ^ 64 := by decide) :
    subroutine_ok P addr (decodeErrorFromSpecWithStack A hookStack) := by
  refine subroutine_ok_outcome_intro fun ⟨k, w⟩ R s0 hpc hrun hpre hal => ?_
  have hsplit : stackAt s0.sp hookStack =
      memRegion (s0.sp - BitVec.ofNat 64 hookStack) (hookStack - decodeErrorHookStack) ∗
        stackAt s0.sp decodeErrorHookStack := by
    have h1 := stackAt_split_bottom s0.sp decodeErrorHookStack (hookStack - decodeErrorHookStack) (by omega)
    rwa [Nat.add_sub_of_le hle] at h1
  let R' : SepProp := memRegion (s0.sp - BitVec.ofNat 64 hookStack) (hookStack - decodeErrorHookStack) ∗ R
  have hpre' : s0.mem ⊨ (decodeErrorFromSpec A).pre (k, w) s0 ∗ R' := by
    dsimp only [decodeErrorFromSpecWithStack, decodeErrorFromSpec, R'] at hpre ⊢
    rw [hsplit] at hpre
    ac_nf at hpre ⊢
  refine h.mono_outcome (k, w) R' s0 hpc hrun hpre' hal fun sf hout => ?_
  rcases hout with ⟨hret, hcc, hpost⟩ | ⟨hpan, hpost⟩ | ⟨code, _, hex⟩ | ⟨_, hoom⟩
  · refine Or.inl ⟨hret, hcc, ?_⟩
    dsimp only [decodeErrorFromSpecWithStack, decodeErrorFromSpec, R'] at hpost ⊢
    rw [hsplit]
    ac_nf at hpost ⊢
  · exact Or.inr (Or.inl ⟨hpan, satisfies_anyHeap_frame hpost⟩)
  · dsimp only [decodeErrorFromSpec] at hex
    rw [satisfies_pure_sepConj] at hex
    exact False.elim hex.1
  · dsimp only [decodeErrorFromSpec] at hoom
    rw [satisfies_pure_sepConj] at hoom
    exact False.elim hoom.1

theorem decodeErrorPushWithStack_of_decodeErrorPush {P : Program} {addr : BitVec 64} {A : RustAlloc}
    {hookStack : Nat} (h : subroutine_ok P addr (decodeErrorPushSpec A))
    (hle : decodeErrorHookStack ≤ hookStack := by decide)
    (hmax : hookStack ≤ 2 ^ 64 := by decide) :
    subroutine_ok P addr (decodeErrorPushSpecWithStack A hookStack) := by
  refine subroutine_ok_outcome_intro fun ⟨d, e, n⟩ R s0 hpc hrun hpre hal => ?_
  have hsplit : stackAt s0.sp hookStack =
      memRegion (s0.sp - BitVec.ofNat 64 hookStack) (hookStack - decodeErrorHookStack) ∗
        stackAt s0.sp decodeErrorHookStack := by
    have h1 := stackAt_split_bottom s0.sp decodeErrorHookStack (hookStack - decodeErrorHookStack) (by omega)
    rwa [Nat.add_sub_of_le hle] at h1
  let R' : SepProp := memRegion (s0.sp - BitVec.ofNat 64 hookStack) (hookStack - decodeErrorHookStack) ∗ R
  have hpre' : s0.mem ⊨ (decodeErrorPushSpec A).pre (d, e, n) s0 ∗ R' := by
    dsimp only [decodeErrorPushSpecWithStack, decodeErrorPushSpec, R'] at hpre ⊢
    rw [hsplit] at hpre
    ac_nf at hpre ⊢
  refine h.mono_outcome (d, e, n) R' s0 hpc hrun hpre' hal fun sf hout => ?_
  rcases hout with ⟨hret, hcc, hpost⟩ | ⟨hpan, hpost⟩ | ⟨code, _, hex⟩ | ⟨_, hoom⟩
  · refine Or.inl ⟨hret, hcc, ?_⟩
    dsimp only [decodeErrorPushSpecWithStack, decodeErrorPushSpec, R'] at hpost ⊢
    rw [hsplit]
    ac_nf at hpost ⊢
  · exact Or.inr (Or.inl ⟨hpan, satisfies_anyHeap_frame hpost⟩)
  · dsimp only [decodeErrorPushSpec] at hex
    rw [satisfies_pure_sepConj] at hex
    exact False.elim hex.1
  · dsimp only [decodeErrorPushSpec] at hoom
    rw [satisfies_pure_sepConj] at hoom
    exact False.elim hoom.1

theorem decodeVarintSlowWithStack_of_decodeVarintSlow {P : Program} {addr : BitVec 64} {A : RustAlloc}
    {hookStack : Nat} (h : subroutine_ok P addr (decodeVarintSlowSpec A))
    (hle : varintSlowStack ≤ hookStack := by decide)
    (hmax : hookStack ≤ 2 ^ 64 := by decide) :
    subroutine_ok P addr (decodeVarintSlowSpecWithStack A hookStack) := by
  refine subroutine_ok_outcome_intro fun ⟨slotA, slot, ptr, bs⟩ R s0 hpc hrun hpre hal => ?_
  have hsplit : stackAt s0.sp hookStack =
      memRegion (s0.sp - BitVec.ofNat 64 hookStack) (hookStack - varintSlowStack) ∗
        stackAt s0.sp varintSlowStack := by
    have h1 := stackAt_split_bottom s0.sp varintSlowStack (hookStack - varintSlowStack) (by omega)
    rwa [Nat.add_sub_of_le hle] at h1
  let R' : SepProp := memRegion (s0.sp - BitVec.ofNat 64 hookStack) (hookStack - varintSlowStack) ∗ R
  have hpre' : s0.mem ⊨ (decodeVarintSlowSpec A).pre (slotA, slot, ptr, bs) s0 ∗ R' := by
    dsimp only [decodeVarintSlowSpecWithStack, decodeVarintSlowSpec, R'] at hpre ⊢
    rw [hsplit] at hpre
    ac_nf at hpre ⊢
  refine h.mono_outcome (slotA, slot, ptr, bs) R' s0 hpc hrun hpre' hal fun sf hout => ?_
  rcases hout with ⟨hret, hcc, hpost⟩ | ⟨hpan, hpost⟩ | ⟨code, _, hex⟩ | ⟨_, hoom⟩
  · refine Or.inl ⟨hret, hcc, ?_⟩
    dsimp only [decodeVarintSlowSpecWithStack, decodeVarintSlowSpec, R'] at hpost ⊢
    rw [hsplit]
    ac_nf at hpost ⊢
  · exact Or.inr (Or.inl ⟨hpan, satisfies_anyHeap_frame hpost⟩)
  · dsimp only [decodeVarintSlowSpec] at hex
    rw [satisfies_pure_sepConj] at hex
    exact False.elim hex.1
  · dsimp only [decodeVarintSlowSpec] at hoom
    rw [satisfies_pure_sepConj] at hoom
    exact False.elim hoom.1

theorem decodeErrorFromSpecWithStack_inImage_le {P : Program} {addr : BitVec 64} {img : Obj.Image}
    {A : RustAlloc} {s1 s2 : Nat}
    (h : subroutine_ok P addr ((decodeErrorFromSpecWithStack A s1).inImage img))
    (hle : s1 ≤ s2 := by decide) (hmax : s2 ≤ 2 ^ 64 := by decide) :
    subroutine_ok P addr ((decodeErrorFromSpecWithStack A s2).inImage img) := by
  refine subroutine_ok_outcome_intro fun ⟨k, w⟩ R s0 hpc hrun hpre hal => ?_
  have hsplit : stackAt s0.sp s2 =
      memRegion (s0.sp - BitVec.ofNat 64 s2) (s2 - s1) ∗ stackAt s0.sp s1 := by
    have h1 := stackAt_split_bottom s0.sp s1 (s2 - s1) (by omega)
    rwa [Nat.add_sub_of_le hle] at h1
  let R' : SepProp := memRegion (s0.sp - BitVec.ofNat 64 s2) (s2 - s1) ∗ R
  have hpre' : s0.mem ⊨ ((decodeErrorFromSpecWithStack A s1).inImage img).pre (k, w) s0 ∗ R' := by
    dsimp only [Spec.inImage, decodeErrorFromSpecWithStack, R'] at hpre ⊢
    rw [hsplit] at hpre
    ac_nf at hpre ⊢
  refine h.mono_outcome (k, w) R' s0 hpc hrun hpre' hal fun sf hout => ?_
  rcases hout with ⟨hret, hcc, hpost⟩ | ⟨hpan, hpost⟩ | ⟨code, _, hex⟩ | ⟨_, hoom⟩
  · refine Or.inl ⟨hret, hcc, ?_⟩
    dsimp only [Spec.inImage, decodeErrorFromSpecWithStack, R'] at hpost ⊢
    rw [hsplit]
    ac_nf at hpost ⊢
  · exact Or.inr (Or.inl ⟨hpan, satisfies_anyHeap_frame hpost⟩)
  · dsimp only [Spec.inImage, decodeErrorFromSpecWithStack] at hex
    rw [satisfies_pure_sepConj] at hex
    exact False.elim hex.1
  · dsimp only [Spec.inImage, decodeErrorFromSpecWithStack] at hoom
    rw [satisfies_pure_sepConj] at hoom
    exact False.elim hoom.1

theorem decodeErrorPushExternSpecWithStack_inImage_le {P : Program} {addr : BitVec 64} {img : Obj.Image}
    {A : RustAlloc} {s1 s2 : Nat}
    (h : subroutine_ok P addr ((decodeErrorPushExternSpecWithStack A s1).inImage img))
    (hle : s1 ≤ s2 := by decide) (hmax : s2 ≤ 2 ^ 64 := by decide) :
    subroutine_ok P addr ((decodeErrorPushExternSpecWithStack A s2).inImage img) := by
  refine subroutine_ok_outcome_intro fun ⟨d, e, n⟩ R s0 hpc hrun hpre hal => ?_
  have hsplit : stackAt s0.sp s2 =
      memRegion (s0.sp - BitVec.ofNat 64 s2) (s2 - s1) ∗ stackAt s0.sp s1 := by
    have h1 := stackAt_split_bottom s0.sp s1 (s2 - s1) (by omega)
    rwa [Nat.add_sub_of_le hle] at h1
  let R' : SepProp := memRegion (s0.sp - BitVec.ofNat 64 s2) (s2 - s1) ∗ R
  have hpre' : s0.mem ⊨ ((decodeErrorPushExternSpecWithStack A s1).inImage img).pre (d, e, n) s0 ∗ R' := by
    dsimp only [Spec.inImage, decodeErrorPushExternSpecWithStack, R'] at hpre ⊢
    rw [hsplit] at hpre
    ac_nf at hpre ⊢
  refine h.mono_outcome (d, e, n) R' s0 hpc hrun hpre' hal fun sf hout => ?_
  rcases hout with ⟨hret, hcc, hpost⟩ | ⟨hpan, hpost⟩ | ⟨code, _, hex⟩ | ⟨_, hoom⟩
  · refine Or.inl ⟨hret, hcc, ?_⟩
    dsimp only [Spec.inImage, decodeErrorPushExternSpecWithStack, R'] at hpost ⊢
    rw [hsplit]
    ac_nf at hpost ⊢
  · exact Or.inr (Or.inl ⟨hpan, satisfies_anyHeap_frame hpost⟩)
  · dsimp only [Spec.inImage, decodeErrorPushExternSpecWithStack] at hex
    rw [satisfies_pure_sepConj] at hex
    exact False.elim hex.1
  · dsimp only [Spec.inImage, decodeErrorPushExternSpecWithStack] at hoom
    rw [satisfies_pure_sepConj] at hoom
    exact False.elim hoom.1

theorem decodeVarintSlowSpecWithStack_inImage_le {P : Program} {addr : BitVec 64} {img : Obj.Image}
    {A : RustAlloc} {s1 s2 : Nat}
    (h : subroutine_ok P addr ((decodeVarintSlowSpecWithStack A s1).inImage img))
    (hle : s1 ≤ s2 := by decide) (hmax : s2 ≤ 2 ^ 64 := by decide) :
    subroutine_ok P addr ((decodeVarintSlowSpecWithStack A s2).inImage img) := by
  refine subroutine_ok_outcome_intro fun ⟨slotA, slot, ptr, bs⟩ R s0 hpc hrun hpre hal => ?_
  have hsplit : stackAt s0.sp s2 =
      memRegion (s0.sp - BitVec.ofNat 64 s2) (s2 - s1) ∗ stackAt s0.sp s1 := by
    have h1 := stackAt_split_bottom s0.sp s1 (s2 - s1) (by omega)
    rwa [Nat.add_sub_of_le hle] at h1
  let R' : SepProp := memRegion (s0.sp - BitVec.ofNat 64 s2) (s2 - s1) ∗ R
  have hpre' : s0.mem ⊨ ((decodeVarintSlowSpecWithStack A s1).inImage img).pre (slotA, slot, ptr, bs) s0 ∗ R' := by
    dsimp only [Spec.inImage, decodeVarintSlowSpecWithStack, R'] at hpre ⊢
    rw [hsplit] at hpre
    ac_nf at hpre ⊢
  refine h.mono_outcome (slotA, slot, ptr, bs) R' s0 hpc hrun hpre' hal fun sf hout => ?_
  rcases hout with ⟨hret, hcc, hpost⟩ | ⟨hpan, hpost⟩ | ⟨code, _, hex⟩ | ⟨_, hoom⟩
  · refine Or.inl ⟨hret, hcc, ?_⟩
    dsimp only [Spec.inImage, decodeVarintSlowSpecWithStack, R'] at hpost ⊢
    rw [hsplit]
    ac_nf at hpost ⊢
  · exact Or.inr (Or.inl ⟨hpan, satisfies_anyHeap_frame hpost⟩)
  · dsimp only [Spec.inImage, decodeVarintSlowSpecWithStack] at hex
    rw [satisfies_pure_sepConj] at hex
    exact False.elim hex.1
  · dsimp only [Spec.inImage, decodeVarintSlowSpecWithStack] at hoom
    rw [satisfies_pure_sepConj] at hoom
    exact False.elim hoom.1

/-- `subtle::black_box::<u8>(v: u8) -> u8`: preserves the low byte `(sf.readReg64 .x0).setWidth 8 = v.setWidth 8`
and trace. -/
def blackBoxU8Spec : Spec (BitVec 64) where
  pre := fun v s => ⌜s.readReg64 .x0 = v⌝
  post := fun v s0 sf =>
    ⌜(sf.readReg64 .x0).setWidth 8 = v.setWidth 8 ∧ sf.trace = s0.trace⌝

theorem blackBoxU8_of_blackBox {P : Program} {addr : BitVec 64}
    (h : subroutine_ok P addr blackBoxSpec) :
    subroutine_ok P addr blackBoxU8Spec := by
  refine subroutine_ok_outcome_intro fun v R s0 hpc hrun hpre hal =>
    h.mono_outcome v R s0 hpc hrun hpre hal fun sf hout => ?_
  rcases hout with ⟨hret, hcc, hpost⟩ | hpan | hex
  · refine Or.inl ⟨hret, hcc, ?_⟩
    simp only [blackBoxSpec, blackBoxU8Spec, satisfies_pure_sepConj] at hpost ⊢
    rcases hpost with ⟨⟨hx0, htr⟩, hR⟩
    have h8 : (sf.readReg64 .x0).setWidth 8 = v.setWidth 8 := by
      rw [hx0]
      change ((v.setWidth 8).setWidth 64).setWidth 8 = v.setWidth 8
      rw [BitVec.setWidth_setWidth_of_le (v.setWidth 8) (by decide : 8 ≤ 64), BitVec.setWidth_eq]
    exact ⟨⟨h8, htr⟩, hR⟩
  · exact Or.inr (Or.inl hpan)
  · exact Or.inr (Or.inr hex)

/-- Result layout of `<uuid::Uuid>::try_parse` at `out` (32 bytes) allowing any non-`Ok` tag
`tag ≠ uuidOkTag` on `.none`, matching both `uuidResultAt out (parse bs)` and `Externs.uuidTryParseSpec`. -/
def uuidTryParseAnyResultAt (out : BitVec 64) : SepProp :=
  ∃∗ res : Option (List.Vector (BitVec 8) 16),
    match res with
    | some u => (out ↦₃₂ uuidOkTag) ∗ ((out + 4#64) ↦ₛ u.toList) ∗ memRegion (out + 20#64) 12
    | none => ∃∗ tag : BitVec 32, ⌜tag ≠ uuidOkTag⌝ ∗ (out ↦₃₂ tag) ∗ memRegion (out + 4#64) 28

/-- Nondeterministic `<uuid::Uuid>::try_parse(x0 = ptr, x1 = len)` contract (sret `x8`, 32 bytes):
writes `uuidTryParseAnyResultAt out` and preserves `(p ↦ₛ bs)` and trace. -/
def uuidTryParseAnySpec : Spec (BitVec 64 × List (BitVec 8) × BitVec 64) where
  pre := fun (p, bs, out) s =>
    ⌜s.readReg64 .x0 = p ∧ (s.readReg64 .x1).toNat = bs.length ∧ s.readReg64 .x8 = out⌝ ∗
      (p ↦ₛ bs) ∗ memRegion out 32
  post := fun (p, bs, out) s0 sf =>
    ⌜sf.trace = s0.trace⌝ ∗ (p ↦ₛ bs) ∗ uuidTryParseAnyResultAt out

theorem uuidResultAt_entails_any (out : BitVec 64) (r : Option (List.Vector (BitVec 8) 16)) :
    uuidResultAt out r ⊢ uuidTryParseAnyResultAt out := by
  unfold uuidTryParseAnyResultAt
  refine Entails.sepExists_right r ?_
  cases r with
  | some u => exact Entails.refl _
  | none =>
    unfold uuidResultAt
    refine Entails.sepExists_right uuidErrParseOther ?_
    rw [show (⌜uuidErrParseOther ≠ uuidOkTag⌝ : SepProp) = emp by simp [uuidErrParseOther, uuidOkTag],
      emp_sepConj]
    exact Entails.refl _

theorem uuidTryParseAny_of_spec {P : Program} {addr : BitVec 64}
    (h : subroutine_ok P addr (uuidTryParseSpec uuidTryParse)) :
    subroutine_ok P addr uuidTryParseAnySpec := by
  refine subroutine_ok_outcome_intro fun ⟨p, bs, out⟩ R s0 hpc hrun hpre hal =>
    h.mono_outcome (p, bs, out) R s0 hpc hrun hpre hal fun sf hout => ?_
  rcases hout with ⟨hret, hcc, hpost⟩ | hpan | hex
  · refine Or.inl ⟨hret, hcc, ?_⟩
    simp only [uuidTryParseSpec, uuidTryParseAnySpec, sepConj_assoc,
      satisfies_pure_sepConj] at hpost ⊢
    rcases hpost with ⟨htr, hmem⟩
    refine ⟨htr, ?_⟩
    exact Satisfies.mono
      (sepConj_mono_right (sepConj_mono_left (uuidResultAt_entails_any out (uuidTryParse bs)))) hmem
  · exact Or.inr (Or.inl hpan)
  · exact Or.inr (Or.inr hex)

theorem uuidTryParseAnyWithStack_of_code {P : Program} {addr : BitVec 64} {hookStack : Nat}
    (h : subroutine_ok P addr (uuidTryParseCodeSpec uuidTryParse))
    (hle : uuidTryParseStack ≤ hookStack := by decide)
    (hmax : hookStack ≤ 2 ^ 64 := by decide) :
    subroutine_ok P addr (withStack uuidTryParseAnySpec hookStack) := by
  refine subroutine_ok_outcome_intro fun ⟨p, bs, out⟩ R s0 hpc hrun hpre hal => ?_
  have hsplit : stackAt s0.sp hookStack =
      memRegion (s0.sp - BitVec.ofNat 64 hookStack) (hookStack - uuidTryParseStack) ∗
        stackAt s0.sp uuidTryParseStack := by
    have h1 := stackAt_split_bottom s0.sp uuidTryParseStack (hookStack - uuidTryParseStack) (by omega)
    rwa [Nat.add_sub_of_le hle] at h1
  let R' : SepProp := memRegion (s0.sp - BitVec.ofNat 64 hookStack) (hookStack - uuidTryParseStack) ∗ R
  have hpre' : s0.mem ⊨ (uuidTryParseCodeSpec uuidTryParse).pre (p, bs, out) s0 ∗ R' := by
    dsimp only [withStack, uuidTryParseAnySpec, uuidTryParseCodeSpec, uuidTryParseSpec, R'] at hpre ⊢
    rw [hsplit] at hpre
    ac_nf at hpre ⊢
  refine h.mono_outcome (p, bs, out) R' s0 hpc hrun hpre' hal fun sf hout => ?_
  rcases hout with ⟨hret, hcc, hpost⟩ | hpan | hex
  · refine Or.inl ⟨hret, hcc, ?_⟩
    dsimp only [uuidTryParseCodeSpec, uuidTryParseSpec, R'] at hpost
    have hpost' : sf.mem ⊨ ((⌜sf.trace = s0.trace⌝ ∗ (p ↦ₛ bs) ∗ uuidTryParseAnyResultAt out) ∗
        stackAt s0.sp uuidTryParseStack) ∗
        (memRegion (s0.sp - BitVec.ofNat 64 hookStack) (hookStack - uuidTryParseStack) ∗ R) :=
      Satisfies.mono (sepConj_mono_left (sepConj_mono_left (sepConj_mono_right (sepConj_mono_right
        (uuidResultAt_entails_any out (uuidTryParse bs)))))) hpost
    dsimp only [withStack, uuidTryParseAnySpec]
    rw [hsplit]
    ac_nf at hpost' ⊢
  · rcases hpan with ⟨_, hpan_sat⟩
    have h0 : (uuidTryParseCodeSpec uuidTryParse).onPanic (p, bs, out) s0 sf = ⌜False⌝ := rfl
    rw [h0, satisfies_pure_sepConj] at hpan_sat
    exact False.elim hpan_sat.1
  · rcases hex with ⟨code, _, hex_sat⟩ | ⟨_, hoom_sat⟩
    · have h0 : (uuidTryParseCodeSpec uuidTryParse).onExit (p, bs, out) code s0 sf = ⌜False⌝ := rfl
      rw [h0, satisfies_pure_sepConj] at hex_sat
      exact False.elim hex_sat.1
    · have h0 : (uuidTryParseCodeSpec uuidTryParse).onOom (p, bs, out) s0 sf = ⌜False⌝ := rfl
      rw [h0, satisfies_pure_sepConj] at hoom_sat
      exact False.elim hoom_sat.1

/-- Nondeterministic `libsignal_session_rng_fill(dst = x0, len = x1)` contract:
overwrites `memRegion dst len` with some `bs` of length `len` and preserves trace. -/
def rngFillAnySpec : Spec (BitVec 64 × Nat) where
  pre := fun (dst, len) s =>
    ⌜s.readReg64 .x0 = dst ∧ (s.readReg64 .x1).toNat = len⌝ ∗
      memRegion dst len
  post := fun (dst, len) s0 sf =>
    ⌜sf.trace = s0.trace⌝ ∗
      (∃∗ bs : List (BitVec 8), ⌜bs.length = len⌝ ∗ (dst ↦ₛ bs))

/-- Separate RNG contract structure (`Stage2RngContract b ctl ext`), split out from
`Stage2ContractsX` so RNG-free code and `faultOnRngExt` instantiations do not depend on `rng_fill`. -/
structure Stage2RngContract (b : BitVec 64) (ctl : BitVec 64)
    (ext : String → Option (State → State)) : Prop where
  rng_fill :
    subroutine_ok (tripleRatchetProgAtExt b ext) ((tripleRatchetProgAtExt b ext).fnAddr rngFillName) (rngFillSpec ctl)

namespace Stage2RngContract

variable {b : BitVec 64} {ctl : BitVec 64} {ext : String → Option (State → State)}

theorem rng_fill_ok_at (hR : Stage2RngContract b ctl ext) (name : String) (k : Nat)
    (hk : libsignalSessionCode.fnOff name + k = libsignalSessionCode.fnOff rngFillName := by
      simp only [arm64_norm]) :
    subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr name + BitVec.ofNat 64 k) (rngFillSpec ctl) :=
  sub_ok_at_of_fnAddr hR.rng_fill name k hk

theorem of_Stage2Contracts {C : Crypto} {A : RustAlloc} {S : SpqrModel}
    (hC : Stage2Contracts b C A ctl uuidTryParse S ext) :
    Stage2RngContract b ctl ext :=
  ⟨hC.rng_fill⟩

theorem of_tripleRatchetProgAt (b : BitVec 64) (C : Crypto) (ctl : BitVec 64)
    (abs : String → Option (State → State)) :
    Stage2RngContract b ctl (tripleRatchetExterns C ctl abs) where
  rng_fill := by
    simpa only [BitVec.ofNat_eq_ofNat, BitVec.add_zero] using
      CryptoVerification.LibsignalTripleRatchet.rng_fill_ok_at b C ctl abs rngFillName 0 (Nat.add_zero _)

end Stage2RngContract

/-- Whole-function AES-256-CBC encrypt contract parameterized by `encFn : Bytes → Bytes → Bytes → Bytes`
(`aesEncSpec E A = aesEncFnSpec (fun pt k iv => aesCbcEncrypt E (HKDF.bytesToKey32 k) (CBC.bytesToBlock iv) pt) A`). -/
def aesEncFnSpec
    (encFn : List (BitVec 8) → List (BitVec 8) → List (BitVec 8) → List (BitVec 8))
    (A : RustAlloc) : Spec AesCall where
  pre := fun x s => x.pre A s
  post := fun x s0 sf =>
    ⌜sf.trace = s0.trace⌝ ∗ x.frame ∗
      vecU8 A x.ret (encFn x.input x.key x.iv) ∗
      A.pool ∗ stackAt s0.sp extHookStack
  onPanic := fun _ s0 sf => ⌜allocFailedIn s0 sf ∧ s0.trace <+: sf.trace⌝ ∗ anyHeap

@[simp]
theorem aesEncFnSpec_block_eq (E : CBC.AesKey → CBC.Block → CBC.Block) (A : RustAlloc) :
    aesEncFnSpec (fun pt k iv => aesCbcEncrypt E (HKDF.bytesToKey32 k) (CBC.bytesToBlock iv) pt) A =
      aesEncSpec E A :=
  rfl

/-- Ciphertext length bound `(encFn pt k iv).length ≤ pt.length + 16` for PKCS#7-padded
AES-256-CBC encryption. -/
def AesEncLenBound
    (encFn : List (BitVec 8) → List (BitVec 8) → List (BitVec 8) → List (BitVec 8)) : Prop :=
  ∀ pt k iv, (encFn pt k iv).length ≤ pt.length + 16

theorem aesEncLenBound_aesCbcEncrypt (E : CBC.AesKey → CBC.Block → CBC.Block) :
    AesEncLenBound (fun pt k iv => aesCbcEncrypt E (HKDF.bytesToKey32 k) (CBC.bytesToBlock iv) pt) := by
  intro pt k iv
  have hblk : ∀ l : List CBC.Block,
      (l.flatMap CBC.blockToBytesLE).length = 16 * l.length := by
    intro l
    induction l with
    | nil => rfl
    | cons h t ih =>
      simp only [List.flatMap_cons, List.length_append, ih, List.length_cons, CBC.blockToBytesLE,
        List.length_ofFn]
      omega
  unfold aesCbcEncrypt
  rw [hblk, List.Vector.toList_length]
  change 16 * (pt.length / 16 + 1) ≤ pt.length + 16
  omega

/-- Whole-function AES-256-CBC decrypt contract parameterized by
`decFn : Bytes → Bytes → Bytes → Option Bytes`, with `Externs.aesDecSpec`'s `.none` layout
(`(x.ret ↦₆₄ errTag) ∗ memRegion (x.ret + 8#64) 16`, without requiring `p ≠ 0` at `+8`). -/
def aesDecFnSpec
    (decFn : List (BitVec 8) → List (BitVec 8) → List (BitVec 8) → Option (List (BitVec 8)))
    (A : RustAlloc) : Spec AesCall where
  pre := fun x s => x.pre A s
  post := fun x s0 sf =>
    ⌜sf.trace = s0.trace⌝ ∗ x.frame ∗
      (match decFn x.input x.key x.iv with
       | some pt => vecU8 A x.ret pt
       | none => (x.ret ↦₆₄ errTag) ∗ memRegion (x.ret + 8#64) 16) ∗
      A.pool ∗ stackAt s0.sp extHookStack
  onPanic := fun _ s0 sf => ⌜allocFailedIn s0 sf ∧ s0.trace <+: sf.trace⌝ ∗ anyHeap

/-- Block-cipher specialization of `aesDecFnSpec` (dropping `p ≠ 0` on `.none`). -/
abbrev aesDecWeakSpec (D : CBC.AesKey → CBC.Block → CBC.Block) (A : RustAlloc) : Spec AesCall :=
  aesDecFnSpec (fun ct k iv => aesCbcDecrypt D (HKDF.bytesToKey32 k) (CBC.bytesToBlock iv) ct) A

theorem aesDecWeak_of_aesDec {P : Program} {addr : BitVec 64}
    {D : CBC.AesKey → CBC.Block → CBC.Block} {A : RustAlloc}
    (h : subroutine_ok P addr (aesDecSpec D A)) :
    subroutine_ok P addr (aesDecWeakSpec D A) := by
  refine subroutine_ok_outcome_intro fun x R s0 hpc hrun hpre hal =>
    h.mono_outcome x R s0 hpc hrun hpre hal fun sf hout => ?_
  rcases hout with ⟨hret, hcc, hpost⟩ | hpan | hex
  · refine Or.inl ⟨hret, hcc, ?_⟩
    simp only [aesDecSpec, aesDecWeakSpec, aesDecFnSpec,
      sepConj_assoc, satisfies_pure_sepConj] at hpost ⊢
    rcases hpost with ⟨htr, hmem_post⟩
    refine ⟨htr, ?_⟩
    cases hdec : aesCbcDecrypt D (HKDF.bytesToKey32 x.key) (CBC.bytesToBlock x.iv) x.input with
    | some pt =>
      simpa only [hdec, sepConj_assoc] using hmem_post
    | none =>
      simp only [hdec, sepConj_assoc, sepExists_sepConj_left, sepExists_sepConj_right,
        satisfies_sepExists] at hmem_post ⊢
      rcases hmem_post with ⟨p, hmem_p⟩
      have h1 : sf.mem ⊨ ⌜p ≠ 0⌝ ∗ (x.frame ∗ (x.ret ↦₆₄ errTag) ∗
          (((x.ret + 8#64) ↦₆₄ p) ∗ memRegion (x.ret + 16#64) 8) ∗
          A.pool ∗ stackAt s0.sp extHookStack ∗ R) := by
        ac_nf at hmem_p ⊢
      rw [satisfies_pure_sepConj] at h1
      rcases h1 with ⟨_, hrest⟩
      rw [memRegion_split' (b := x.ret + 8#64) (b' := x.ret + 16#64) (n := 8) (k := 8)
        (by decide) (by bv_omega) (by decide), memRegion_eight]
      simp only [sepConj_assoc, sepExists_sepConj_left, sepExists_sepConj_right, satisfies_sepExists]
      exact ⟨p, by ac_nf at hrest ⊢⟩
  · exact Or.inr (Or.inl hpan)
  · exact Or.inr (Or.inr hex)

/-- Relational empty-state `spqr::recv` contract (`st.bytes = []` at `spqrRecvStack`): writes
`spqrRecvResultAt A ret res` with `res = .ok ([], none)` or `msg.bytes ≠ [] ∧ ∃ sd, res = .error sd`. -/
def spqrRecvEmptyAnySpec (A : RustAlloc) : Spec (VecArg × VecArg × BitVec 64) where
  pre := fun (st, msg, ret) s =>
    ⌜s.readReg64 .x0 = st.v ∧ s.readReg64 .x1 = msg.v ∧ s.readReg64 .x8 = ret ∧ st.bytes = []⌝ ∗
      st.at A ∗ msg.at A ∗ memRegion ret 48 ∗ A.pool ∗ stackAt s.sp spqrRecvStack
  post := fun (st, msg, ret) s0 sf =>
    ⌜sf.trace = s0.trace⌝ ∗ st.at A ∗ msg.at A ∗
      (∃∗ res : Except Bool (List (BitVec 8) × Salt),
        ⌜res = .ok ([], none) ∨ (msg.bytes ≠ [] ∧ ∃ sd, res = .error sd)⌝ ∗
          spqrRecvResultAt A ret res) ∗
      A.pool ∗ stackAt s0.sp spqrRecvStack
  onPanic := fun _ s0 sf =>
    ⌜allocFailedIn s0 sf ∧ s0.trace <+: sf.trace⌝ ∗ anyHeap

/-- Image-invariant allocator, memory, and shim contract bundle on
`tripleRatchetProgAtExt img.base ext` at `extHookStack`. -/
structure AllocContractsX (img : Obj.Image) (A : RustAlloc)
    (ext : String → Option (State → State)) : Prop where
  alloc :
    subroutine_ok (tripleRatchetProgAtExt img.base ext) ((tripleRatchetProgAtExt img.base ext).fnAddr allocName)
      ((rustAllocSpecWithStack A extHookStack).inImage img)
  dealloc :
    subroutine_ok (tripleRatchetProgAtExt img.base ext) ((tripleRatchetProgAtExt img.base ext).fnAddr deallocName)
      ((rustDeallocExternSpecWithStack A extHookStack).inImage img)
  realloc :
    subroutine_ok (tripleRatchetProgAtExt img.base ext) ((tripleRatchetProgAtExt img.base ext).fnAddr reallocName)
      ((rustReallocExternSpecWithStack A extHookStack).inImage img)
  shim : ∀ (hookStack : Nat), extHookStack ≤ hookStack → hookStack ≤ 2 ^ 64 →
    subroutine_ok (tripleRatchetProgAtExt img.base ext) ((tripleRatchetProgAtExt img.base ext).fnAddr shimName)
      ((withStack sessionShimSpec hookStack).inImage img)
  memcpy : ∀ (hookStack : Nat), extHookStack ≤ hookStack → hookStack ≤ 2 ^ 64 →
    subroutine_ok (tripleRatchetProgAtExt img.base ext) ((tripleRatchetProgAtExt img.base ext).fnAddr memcpyName)
      ((libcMemcpySpec hookStack).inImage img)
  session_memcpy : ∀ (hookStack : Nat), extHookStack ≤ hookStack → hookStack ≤ 2 ^ 64 →
    subroutine_ok (tripleRatchetProgAtExt img.base ext) ((tripleRatchetProgAtExt img.base ext).fnAddr memcpyName)
      ((sessionMemcpySpec hookStack).inImage img)
  memcpy_region : ∀ (hookStack : Nat), extHookStack ≤ hookStack → hookStack ≤ 2 ^ 64 →
    subroutine_ok (tripleRatchetProgAtExt img.base ext) ((tripleRatchetProgAtExt img.base ext).fnAddr memcpyName)
      ((withStack memcpyRegionSpec hookStack).inImage img)
  session_memcpy_region : ∀ (hookStack : Nat), extHookStack ≤ hookStack → hookStack ≤ 2 ^ 64 →
    subroutine_ok (tripleRatchetProgAtExt img.base ext) ((tripleRatchetProgAtExt img.base ext).fnAddr memcpyName)
      ((withStack sessionMemcpyRegionSpec hookStack).inImage img)
  memmove : ∀ (hookStack : Nat), extHookStack ≤ hookStack → hookStack ≤ 2 ^ 64 →
    subroutine_ok (tripleRatchetProgAtExt img.base ext) ((tripleRatchetProgAtExt img.base ext).fnAddr memmoveName)
      ((libcMemmoveSpec hookStack).inImage img)
  session_memmove : ∀ (hookStack : Nat), extHookStack ≤ hookStack → hookStack ≤ 2 ^ 64 →
    subroutine_ok (tripleRatchetProgAtExt img.base ext) ((tripleRatchetProgAtExt img.base ext).fnAddr memmoveName)
      ((sessionMemmoveSpec hookStack).inImage img)
  memset : ∀ (hookStack : Nat), extHookStack ≤ hookStack → hookStack ≤ 2 ^ 64 →
    subroutine_ok (tripleRatchetProgAtExt img.base ext) ((tripleRatchetProgAtExt img.base ext).fnAddr memsetName)
      ((libcMemsetSpec hookStack).inImage img)
  session_memset : ∀ (hookStack : Nat), extHookStack ≤ hookStack → hookStack ≤ 2 ^ 64 →
    subroutine_ok (tripleRatchetProgAtExt img.base ext) ((tripleRatchetProgAtExt img.base ext).fnAddr memsetName)
      ((sessionMemsetSpec hookStack).inImage img)
  memset_region : ∀ (hookStack : Nat), extHookStack ≤ hookStack → hookStack ≤ 2 ^ 64 →
    subroutine_ok (tripleRatchetProgAtExt img.base ext) ((tripleRatchetProgAtExt img.base ext).fnAddr memsetName)
      ((withStack memsetRegionSpec hookStack).inImage img)
  session_memset_region : ∀ (hookStack : Nat), extHookStack ≤ hookStack → hookStack ≤ 2 ^ 64 →
    subroutine_ok (tripleRatchetProgAtExt img.base ext) ((tripleRatchetProgAtExt img.base ext).fnAddr memsetName)
      ((withStack sessionMemsetRegionSpec hookStack).inImage img)

namespace AllocContractsX

variable {img : Obj.Image} {A : RustAlloc} {ext : String → Option (State → State)}

theorem alloc_ok_at (hA : AllocContractsX img A ext) (name : String) (k : Nat)
    (hk : libsignalSessionCode.fnOff name + k = libsignalSessionCode.fnOff allocName := by
      simp only [arm64_norm]) :
    subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr name + BitVec.ofNat 64 k)
      ((rustAllocSpecWithStack A extHookStack).inImage img) :=
  sub_ok_at_of_fnAddr hA.alloc name k hk

theorem dealloc_ok_at (hA : AllocContractsX img A ext) (name : String) (k : Nat)
    (hk : libsignalSessionCode.fnOff name + k = libsignalSessionCode.fnOff deallocName := by
      simp only [arm64_norm]) :
    subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr name + BitVec.ofNat 64 k)
      ((rustDeallocExternSpecWithStack A extHookStack).inImage img) :=
  sub_ok_at_of_fnAddr hA.dealloc name k hk

theorem realloc_ok_at (hA : AllocContractsX img A ext) (name : String) (k : Nat)
    (hk : libsignalSessionCode.fnOff name + k = libsignalSessionCode.fnOff reallocName := by
      simp only [arm64_norm]) :
    subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr name + BitVec.ofNat 64 k)
      ((rustReallocExternSpecWithStack A extHookStack).inImage img) :=
  sub_ok_at_of_fnAddr hA.realloc name k hk

theorem shim_ok_at (hA : AllocContractsX img A ext) (name : String) (k : Nat)
    (hookStack : Nat := extHookStack)
    (hstack : extHookStack ≤ hookStack := by decide)
    (hstack_le : hookStack ≤ 2 ^ 64 := by decide)
    (hk : libsignalSessionCode.fnOff name + k = libsignalSessionCode.fnOff shimName := by
      simp only [arm64_norm]) :
    subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr name + BitVec.ofNat 64 k)
      ((withStack sessionShimSpec hookStack).inImage img) :=
  sub_ok_at_of_fnAddr (hA.shim hookStack hstack hstack_le) name k hk

theorem session_shim_ok_at (hA : AllocContractsX img A ext) (name : String) (k : Nat)
    (hookStack : Nat := extHookStack)
    (hstack : extHookStack ≤ hookStack := by decide)
    (hstack_le : hookStack ≤ 2 ^ 64 := by decide)
    (hk : libsignalSessionCode.fnOff name + k = libsignalSessionCode.fnOff shimName := by
      simp only [arm64_norm]) :
    subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr name + BitVec.ofNat 64 k)
      ((withStack sessionShimSpec hookStack).inImage img) :=
  sub_ok_at_of_fnAddr (hA.shim hookStack hstack hstack_le) name k hk

theorem memcpy_ok_at (hA : AllocContractsX img A ext) (name : String) (k : Nat)
    (hookStack : Nat := extHookStack)
    (hstack : extHookStack ≤ hookStack := by decide)
    (hstack_le : hookStack ≤ 2 ^ 64 := by decide)
    (hk : libsignalSessionCode.fnOff name + k = libsignalSessionCode.fnOff memcpyName := by
      simp only [arm64_norm]) :
    subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr name + BitVec.ofNat 64 k)
      ((libcMemcpySpec hookStack).inImage img) :=
  sub_ok_at_of_fnAddr (hA.memcpy hookStack hstack hstack_le) name k hk

theorem session_memcpy_ok_at (hA : AllocContractsX img A ext) (name : String) (k : Nat)
    (hookStack : Nat := extHookStack)
    (hstack : extHookStack ≤ hookStack := by decide)
    (hstack_le : hookStack ≤ 2 ^ 64 := by decide)
    (hk : libsignalSessionCode.fnOff name + k = libsignalSessionCode.fnOff memcpyName := by
      simp only [arm64_norm]) :
    subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr name + BitVec.ofNat 64 k)
      ((sessionMemcpySpec hookStack).inImage img) :=
  sub_ok_at_of_fnAddr (hA.session_memcpy hookStack hstack hstack_le) name k hk

theorem memcpy_region_ok_at (hA : AllocContractsX img A ext) (name : String) (k : Nat)
    (hookStack : Nat := extHookStack)
    (hstack : extHookStack ≤ hookStack := by decide)
    (hstack_le : hookStack ≤ 2 ^ 64 := by decide)
    (hk : libsignalSessionCode.fnOff name + k = libsignalSessionCode.fnOff memcpyName := by
      simp only [arm64_norm]) :
    subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr name + BitVec.ofNat 64 k)
      ((withStack memcpyRegionSpec hookStack).inImage img) :=
  sub_ok_at_of_fnAddr (hA.memcpy_region hookStack hstack hstack_le) name k hk

theorem session_memcpy_region_ok_at (hA : AllocContractsX img A ext) (name : String) (k : Nat)
    (hookStack : Nat := extHookStack)
    (hstack : extHookStack ≤ hookStack := by decide)
    (hstack_le : hookStack ≤ 2 ^ 64 := by decide)
    (hk : libsignalSessionCode.fnOff name + k = libsignalSessionCode.fnOff memcpyName := by
      simp only [arm64_norm]) :
    subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr name + BitVec.ofNat 64 k)
      ((withStack sessionMemcpyRegionSpec hookStack).inImage img) :=
  sub_ok_at_of_fnAddr (hA.session_memcpy_region hookStack hstack hstack_le) name k hk

theorem memmove_ok_at (hA : AllocContractsX img A ext) (name : String) (k : Nat)
    (hookStack : Nat := extHookStack)
    (hstack : extHookStack ≤ hookStack := by decide)
    (hstack_le : hookStack ≤ 2 ^ 64 := by decide)
    (hk : libsignalSessionCode.fnOff name + k = libsignalSessionCode.fnOff memmoveName := by
      simp only [arm64_norm]) :
    subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr name + BitVec.ofNat 64 k)
      ((libcMemmoveSpec hookStack).inImage img) :=
  sub_ok_at_of_fnAddr (hA.memmove hookStack hstack hstack_le) name k hk

theorem session_memmove_ok_at (hA : AllocContractsX img A ext) (name : String) (k : Nat)
    (hookStack : Nat := extHookStack)
    (hstack : extHookStack ≤ hookStack := by decide)
    (hstack_le : hookStack ≤ 2 ^ 64 := by decide)
    (hk : libsignalSessionCode.fnOff name + k = libsignalSessionCode.fnOff memmoveName := by
      simp only [arm64_norm]) :
    subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr name + BitVec.ofNat 64 k)
      ((sessionMemmoveSpec hookStack).inImage img) :=
  sub_ok_at_of_fnAddr (hA.session_memmove hookStack hstack hstack_le) name k hk

theorem memset_ok_at (hA : AllocContractsX img A ext) (name : String) (k : Nat)
    (hookStack : Nat := extHookStack)
    (hstack : extHookStack ≤ hookStack := by decide)
    (hstack_le : hookStack ≤ 2 ^ 64 := by decide)
    (hk : libsignalSessionCode.fnOff name + k = libsignalSessionCode.fnOff memsetName := by
      simp only [arm64_norm]) :
    subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr name + BitVec.ofNat 64 k)
      ((libcMemsetSpec hookStack).inImage img) :=
  sub_ok_at_of_fnAddr (hA.memset hookStack hstack hstack_le) name k hk

theorem session_memset_ok_at (hA : AllocContractsX img A ext) (name : String) (k : Nat)
    (hookStack : Nat := extHookStack)
    (hstack : extHookStack ≤ hookStack := by decide)
    (hstack_le : hookStack ≤ 2 ^ 64 := by decide)
    (hk : libsignalSessionCode.fnOff name + k = libsignalSessionCode.fnOff memsetName := by
      simp only [arm64_norm]) :
    subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr name + BitVec.ofNat 64 k)
      ((sessionMemsetSpec hookStack).inImage img) :=
  sub_ok_at_of_fnAddr (hA.session_memset hookStack hstack hstack_le) name k hk

theorem memset_region_ok_at (hA : AllocContractsX img A ext) (name : String) (k : Nat)
    (hookStack : Nat := extHookStack)
    (hstack : extHookStack ≤ hookStack := by decide)
    (hstack_le : hookStack ≤ 2 ^ 64 := by decide)
    (hk : libsignalSessionCode.fnOff name + k = libsignalSessionCode.fnOff memsetName := by
      simp only [arm64_norm]) :
    subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr name + BitVec.ofNat 64 k)
      ((withStack memsetRegionSpec hookStack).inImage img) :=
  sub_ok_at_of_fnAddr (hA.memset_region hookStack hstack hstack_le) name k hk

theorem session_memset_region_ok_at (hA : AllocContractsX img A ext) (name : String) (k : Nat)
    (hookStack : Nat := extHookStack)
    (hstack : extHookStack ≤ hookStack := by decide)
    (hstack_le : hookStack ≤ 2 ^ 64 := by decide)
    (hk : libsignalSessionCode.fnOff name + k = libsignalSessionCode.fnOff memsetName := by
      simp only [arm64_norm]) :
    subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr name + BitVec.ofNat 64 k)
      ((withStack sessionMemsetRegionSpec hookStack).inImage img) :=
  sub_ok_at_of_fnAddr (hA.session_memset_region hookStack hstack hstack_le) name k hk

theorem of_AllocContracts (hA : AllocContracts img.base A ext) :
    AllocContractsX img A ext where
  alloc := subroutine_ok_inImage_of_subroutine_ok img (rustAllocWithStack_of_rustAlloc hA.alloc)
  dealloc := subroutine_ok_inImage_of_subroutine_ok img (rustDeallocExternWithStack_of_rustDealloc hA.dealloc)
  realloc := subroutine_ok_inImage_of_subroutine_ok img (rustReallocExternWithStack_of_rustRealloc hA.realloc)
  shim := fun hookStack _ _ =>
    subroutine_ok_inImage_of_subroutine_ok img (subroutine_ok_withStack_of_subroutine_ok hA.shim hookStack)
  memcpy := fun hookStack _ _ =>
    subroutine_ok_inImage_of_subroutine_ok img (hA.memcpy hookStack)
  session_memcpy := fun hookStack _ _ =>
    subroutine_ok_inImage_of_subroutine_ok img (hA.session_memcpy hookStack)
  memcpy_region := fun hookStack _ _ =>
    subroutine_ok_inImage_of_subroutine_ok img (subroutine_ok_withStack_of_subroutine_ok hA.memcpy_region hookStack)
  session_memcpy_region := fun hookStack _ _ =>
    subroutine_ok_inImage_of_subroutine_ok img (subroutine_ok_withStack_of_subroutine_ok hA.session_memcpy_region hookStack)
  memmove := fun hookStack _ _ =>
    subroutine_ok_inImage_of_subroutine_ok img (hA.memmove hookStack)
  session_memmove := fun hookStack _ _ =>
    subroutine_ok_inImage_of_subroutine_ok img (hA.session_memmove hookStack)
  memset := fun hookStack hstack _ =>
    subroutine_ok_inImage_of_subroutine_ok img (hA.memset hookStack (by unfold extHookStack at hstack; omega))
  session_memset := fun hookStack hstack _ =>
    subroutine_ok_inImage_of_subroutine_ok img (hA.session_memset hookStack (by unfold extHookStack at hstack; omega))
  memset_region := fun hookStack _ _ =>
    subroutine_ok_inImage_of_subroutine_ok img (subroutine_ok_withStack_of_subroutine_ok hA.memset_region hookStack)
  session_memset_region := fun hookStack _ _ =>
    subroutine_ok_inImage_of_subroutine_ok img (subroutine_ok_withStack_of_subroutine_ok hA.session_memset_region hookStack)

theorem of_tripleRatchetProgAt_trap (img : Obj.Image) (C : Crypto) (A : RustAlloc)
    (abs : String → Option (State → State))
    (hA : AllocHooks A abs) :
    AllocContractsX img A (trTrapExterns C abs) :=
  of_AllocContracts (AllocContracts.of_tripleRatchetProgAt_trap img.base C A abs hA)

theorem of_tripleRatchetProgAt (img : Obj.Image) (C : Crypto) (A : RustAlloc) (ctl : BitVec 64)
    (abs : String → Option (State → State))
    (hA : AllocHooks A abs) :
    AllocContractsX img A (tripleRatchetExterns C ctl abs) :=
  of_AllocContracts (AllocContracts.of_tripleRatchetProgAt img.base C A ctl abs hA)

end AllocContractsX

/-- Image-invariant contract bundle on `tripleRatchetProgAtExt img.base ext` extending
`AllocContractsX` with cryptographic primitives, UUID/ServiceId/PublicKey parsers, Prost
`DecodeError` and slow-varint helpers (at `2 * extHookStack` and `64 + 2 * extHookStack`),
relational empty-state `spqr::recv`, and whole-function AES-256-CBC `encFn`/`decFn` contracts. -/
structure Stage2ContractsX (img : Obj.Image) (C : Crypto) (A : RustAlloc)
    (encFn : List (BitVec 8) → List (BitVec 8) → List (BitVec 8) → List (BitVec 8))
    (decFn : List (BitVec 8) → List (BitVec 8) → List (BitVec 8) → Option (List (BitVec 8)))
    (ext : String → Option (State → State)) : Prop extends
    AllocContractsX img A ext where
  black_box :
    subroutine_ok (tripleRatchetProgAtExt img.base ext) ((tripleRatchetProgAtExt img.base ext).fnAddr blackBoxName)
      ((withStack blackBoxU8Spec extHookStack).inImage img)
  compress256 :
    subroutine_ok (tripleRatchetProgAtExt img.base ext) ((tripleRatchetProgAtExt img.base ext).fnAddr compress256Name)
      ((withStack (compress256Spec C.F) extHookStack).inImage img)
  dh :
    subroutine_ok (tripleRatchetProgAtExt img.base ext) ((tripleRatchetProgAtExt img.base ext).fnAddr dhName)
      ((withStack (diffieHellmanSpec C.X) extHookStack).inImage img)
  pub_from_secret :
    subroutine_ok (tripleRatchetProgAtExt img.base ext) ((tripleRatchetProgAtExt img.base ext).fnAddr pubFromSecretName)
      ((withStack (pubFromSecretSpec C.pubKey) extHookStack).inImage img)
  static_drop :
    subroutine_ok (tripleRatchetProgAtExt img.base ext) ((tripleRatchetProgAtExt img.base ext).fnAddr staticDropName)
      ((withStack zeroizeSecretSpec extHookStack).inImage img)
  shared_drop :
    subroutine_ok (tripleRatchetProgAtExt img.base ext) ((tripleRatchetProgAtExt img.base ext).fnAddr sharedDropName)
      ((withStack zeroizeSecretSpec extHookStack).inImage img)
  uuid_try_parse :
    subroutine_ok (tripleRatchetProgAtExt img.base ext) ((tripleRatchetProgAtExt img.base ext).fnAddr uuidTryParseName)
      ((withStack uuidTryParseAnySpec extHookStack).inImage img)
  decode_varint_slow :
    subroutine_ok (tripleRatchetProgAtExt img.base ext) ((tripleRatchetProgAtExt img.base ext).fnAddr varintSlowName)
      ((decodeVarintSlowSpecWithStack A (64 + 2 * extHookStack)).inImage img)
  aes_enc :
    subroutine_ok (tripleRatchetProgAtExt img.base ext) ((tripleRatchetProgAtExt img.base ext).fnAddr aesEncName)
      ((aesEncFnSpec encFn A).inImage img)
  aes_dec :
    subroutine_ok (tripleRatchetProgAtExt img.base ext) ((tripleRatchetProgAtExt img.base ext).fnAddr aesDecName)
      ((aesDecFnSpec decFn A).inImage img)
  spqr_recv :
    subroutine_ok (tripleRatchetProgAtExt img.base ext) ((tripleRatchetProgAtExt img.base ext).fnAddr spqrRecvName)
      ((spqrRecvEmptyAnySpec A).inImage img)
  format_inner :
    subroutine_ok (tripleRatchetProgAtExt img.base ext) ((tripleRatchetProgAtExt img.base ext).fnAddr formatInnerName)
      ((formatInnerSpec A).inImage img)
  fmt_write :
    subroutine_ok (tripleRatchetProgAtExt img.base ext) ((tripleRatchetProgAtExt img.base ext).fnAddr fmtWriteName)
      ((fmtWriteSpec A).inImage img)
  decode_error_from :
    subroutine_ok (tripleRatchetProgAtExt img.base ext) ((tripleRatchetProgAtExt img.base ext).fnAddr decodeErrorFromName)
      ((decodeErrorFromSpecWithStack A (2 * extHookStack)).inImage img)
  decode_error_push :
    subroutine_ok (tripleRatchetProgAtExt img.base ext) ((tripleRatchetProgAtExt img.base ext).fnAddr decodeErrorPushName)
      ((decodeErrorPushExternSpecWithStack A (2 * extHookStack)).inImage img)

/-- Block-cipher specialization of `Stage2ContractsX` using `C.E` and `C.D`. -/
abbrev Stage2ContractsWeak (img : Obj.Image) (C : Crypto) (A : RustAlloc)
    (ext : String → Option (State → State)) : Prop :=
  Stage2ContractsX img C A
    (fun pt k iv => aesCbcEncrypt C.E (HKDF.bytesToKey32 k) (CBC.bytesToBlock iv) pt)
    (fun ct k iv => aesCbcDecrypt C.D (HKDF.bytesToKey32 k) (CBC.bytesToBlock iv) ct)
    ext

namespace Stage2ContractsX

variable {img : Obj.Image} {C : Crypto} {A : RustAlloc}
  {encFn : List (BitVec 8) → List (BitVec 8) → List (BitVec 8) → List (BitVec 8)}
  {decFn : List (BitVec 8) → List (BitVec 8) → List (BitVec 8) → Option (List (BitVec 8))}
  {ext : String → Option (State → State)}

theorem black_box_ok_at (hC : Stage2ContractsX img C A encFn decFn ext) (name : String) (k : Nat)
    (hk : libsignalSessionCode.fnOff name + k = libsignalSessionCode.fnOff blackBoxName := by
      simp only [arm64_norm]) :
    subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr name + BitVec.ofNat 64 k)
      ((withStack blackBoxU8Spec extHookStack).inImage img) :=
  sub_ok_at_of_fnAddr hC.black_box name k hk

theorem compress256_ok_at (hC : Stage2ContractsX img C A encFn decFn ext) (name : String) (k : Nat)
    (hk : libsignalSessionCode.fnOff name + k = libsignalSessionCode.fnOff compress256Name := by
      simp only [arm64_norm]) :
    subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr name + BitVec.ofNat 64 k)
      ((withStack (compress256Spec C.F) extHookStack).inImage img) :=
  sub_ok_at_of_fnAddr hC.compress256 name k hk

theorem dh_ok_at (hC : Stage2ContractsX img C A encFn decFn ext) (name : String) (k : Nat)
    (hk : libsignalSessionCode.fnOff name + k = libsignalSessionCode.fnOff dhName := by
      simp only [arm64_norm]) :
    subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr name + BitVec.ofNat 64 k)
      ((withStack (diffieHellmanSpec C.X) extHookStack).inImage img) :=
  sub_ok_at_of_fnAddr hC.dh name k hk

theorem pub_from_secret_ok_at (hC : Stage2ContractsX img C A encFn decFn ext) (name : String) (k : Nat)
    (hk : libsignalSessionCode.fnOff name + k = libsignalSessionCode.fnOff pubFromSecretName := by
      simp only [arm64_norm]) :
    subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr name + BitVec.ofNat 64 k)
      ((withStack (pubFromSecretSpec C.pubKey) extHookStack).inImage img) :=
  sub_ok_at_of_fnAddr hC.pub_from_secret name k hk

theorem static_drop_ok_at (hC : Stage2ContractsX img C A encFn decFn ext) (name : String) (k : Nat)
    (hk : libsignalSessionCode.fnOff name + k = libsignalSessionCode.fnOff staticDropName := by
      simp only [arm64_norm]) :
    subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr name + BitVec.ofNat 64 k)
      ((withStack zeroizeSecretSpec extHookStack).inImage img) :=
  sub_ok_at_of_fnAddr hC.static_drop name k hk

theorem shared_drop_ok_at (hC : Stage2ContractsX img C A encFn decFn ext) (name : String) (k : Nat)
    (hk : libsignalSessionCode.fnOff name + k = libsignalSessionCode.fnOff sharedDropName := by
      simp only [arm64_norm]) :
    subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr name + BitVec.ofNat 64 k)
      ((withStack zeroizeSecretSpec extHookStack).inImage img) :=
  sub_ok_at_of_fnAddr hC.shared_drop name k hk

theorem uuid_try_parse_ok_at (hC : Stage2ContractsX img C A encFn decFn ext) (name : String) (k : Nat)
    (hk : libsignalSessionCode.fnOff name + k = libsignalSessionCode.fnOff uuidTryParseName := by
      simp only [arm64_norm]) :
    subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr name + BitVec.ofNat 64 k)
      ((withStack uuidTryParseAnySpec extHookStack).inImage img) :=
  sub_ok_at_of_fnAddr hC.uuid_try_parse name k hk

theorem decode_varint_slow_ok_at (hC : Stage2ContractsX img C A encFn decFn ext) (name : String) (k : Nat)
    (hk : libsignalSessionCode.fnOff name + k = libsignalSessionCode.fnOff varintSlowName := by
      simp only [arm64_norm]) :
    subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr name + BitVec.ofNat 64 k)
      ((decodeVarintSlowSpecWithStack A (64 + 2 * extHookStack)).inImage img) :=
  sub_ok_at_of_fnAddr hC.decode_varint_slow name k hk

theorem aes_enc_ok_at (hC : Stage2ContractsX img C A encFn decFn ext) (name : String) (k : Nat)
    (hk : libsignalSessionCode.fnOff name + k = libsignalSessionCode.fnOff aesEncName := by
      simp only [arm64_norm]) :
    subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr name + BitVec.ofNat 64 k)
      ((aesEncFnSpec encFn A).inImage img) :=
  sub_ok_at_of_fnAddr hC.aes_enc name k hk

theorem aes_dec_ok_at (hC : Stage2ContractsX img C A encFn decFn ext) (name : String) (k : Nat)
    (hk : libsignalSessionCode.fnOff name + k = libsignalSessionCode.fnOff aesDecName := by
      simp only [arm64_norm]) :
    subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr name + BitVec.ofNat 64 k)
      ((aesDecFnSpec decFn A).inImage img) :=
  sub_ok_at_of_fnAddr hC.aes_dec name k hk

theorem spqr_recv_ok_at (hC : Stage2ContractsX img C A encFn decFn ext) (name : String) (k : Nat)
    (hk : libsignalSessionCode.fnOff name + k = libsignalSessionCode.fnOff spqrRecvName := by
      simp only [arm64_norm]) :
    subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr name + BitVec.ofNat 64 k)
      ((spqrRecvEmptyAnySpec A).inImage img) :=
  sub_ok_at_of_fnAddr hC.spqr_recv name k hk

theorem format_inner_ok_at (hC : Stage2ContractsX img C A encFn decFn ext) (name : String) (k : Nat)
    (hk : libsignalSessionCode.fnOff name + k = libsignalSessionCode.fnOff formatInnerName := by
      simp only [arm64_norm]) :
    subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr name + BitVec.ofNat 64 k)
      ((formatInnerSpec A).inImage img) :=
  sub_ok_at_of_fnAddr hC.format_inner name k hk

theorem fmt_write_ok_at (hC : Stage2ContractsX img C A encFn decFn ext) (name : String) (k : Nat)
    (hk : libsignalSessionCode.fnOff name + k = libsignalSessionCode.fnOff fmtWriteName := by
      simp only [arm64_norm]) :
    subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr name + BitVec.ofNat 64 k)
      ((fmtWriteSpec A).inImage img) :=
  sub_ok_at_of_fnAddr hC.fmt_write name k hk

theorem decode_error_from_ok_at (hC : Stage2ContractsX img C A encFn decFn ext) (name : String) (k : Nat)
    (hk : libsignalSessionCode.fnOff name + k = libsignalSessionCode.fnOff decodeErrorFromName := by
      simp only [arm64_norm]) :
    subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr name + BitVec.ofNat 64 k)
      ((decodeErrorFromSpecWithStack A (2 * extHookStack)).inImage img) :=
  sub_ok_at_of_fnAddr hC.decode_error_from name k hk

theorem decode_error_push_ok_at (hC : Stage2ContractsX img C A encFn decFn ext) (name : String) (k : Nat)
    (hk : libsignalSessionCode.fnOff name + k = libsignalSessionCode.fnOff decodeErrorPushName := by
      simp only [arm64_norm]) :
    subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr name + BitVec.ofNat 64 k)
      ((decodeErrorPushExternSpecWithStack A (2 * extHookStack)).inImage img) :=
  sub_ok_at_of_fnAddr hC.decode_error_push name k hk

/-- `Stage2Contracts_trap` together with the empty-state `spqr::recv` contract `hRecv` entails
`Stage2ContractsWeak img C A ext`. -/
theorem of_Stage2Contracts_trap {S : SpqrModel}
    (hC : Stage2Contracts_trap img.base C A uuidTryParse S ext)
    (hRecv : subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr spqrRecvName) ((spqrRecvEmptyAnySpec A).inImage img)) :
    Stage2ContractsWeak img C A ext where
  toAllocContractsX := AllocContractsX.of_AllocContracts hC.toAllocContracts
  black_box := subroutine_ok_inImage_of_subroutine_ok img
    (subroutine_ok_withStack_of_subroutine_ok (blackBoxU8_of_blackBox hC.black_box) extHookStack)
  compress256 := subroutine_ok_inImage_of_subroutine_ok img
    (subroutine_ok_withStack_of_subroutine_ok hC.compress256 extHookStack)
  dh := subroutine_ok_inImage_of_subroutine_ok img
    (subroutine_ok_withStack_of_subroutine_ok hC.dh extHookStack)
  pub_from_secret := subroutine_ok_inImage_of_subroutine_ok img
    (subroutine_ok_withStack_of_subroutine_ok hC.pub_from_secret extHookStack)
  static_drop := subroutine_ok_inImage_of_subroutine_ok img
    (subroutine_ok_withStack_of_subroutine_ok hC.static_drop extHookStack)
  shared_drop := subroutine_ok_inImage_of_subroutine_ok img
    (subroutine_ok_withStack_of_subroutine_ok hC.shared_drop extHookStack)
  uuid_try_parse := subroutine_ok_inImage_of_subroutine_ok img
    (uuidTryParseAnyWithStack_of_code hC.uuid_try_parse)
  decode_varint_slow := subroutine_ok_inImage_of_subroutine_ok img
    (decodeVarintSlowWithStack_of_decodeVarintSlow hC.decode_varint_slow)
  aes_enc := subroutine_ok_inImage_of_subroutine_ok img hC.aes_enc
  aes_dec := subroutine_ok_inImage_of_subroutine_ok img (aesDecWeak_of_aesDec hC.aes_dec)
  spqr_recv := hRecv
  format_inner := subroutine_ok_inImage_of_subroutine_ok img hC.format_inner
  fmt_write := subroutine_ok_inImage_of_subroutine_ok img hC.fmt_write
  decode_error_from := subroutine_ok_inImage_of_subroutine_ok img
    (decodeErrorFromWithStack_of_decodeErrorFrom hC.decode_error_from)
  decode_error_push := subroutine_ok_inImage_of_subroutine_ok img
    (decodeErrorPushExtern_of_decodeErrorPush (decodeErrorPushWithStack_of_decodeErrorPush hC.decode_error_push))

theorem of_Stage2Contracts {ctl : BitVec 64} {S : SpqrModel}
    (hC : Stage2Contracts img.base C A ctl uuidTryParse S ext)
    (hRecv : subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr spqrRecvName) ((spqrRecvEmptyAnySpec A).inImage img)) :
    Stage2ContractsWeak img C A ext where
  toAllocContractsX := (of_Stage2Contracts_trap hC.to_trap hRecv).toAllocContractsX
  black_box := (of_Stage2Contracts_trap hC.to_trap hRecv).black_box
  compress256 := (of_Stage2Contracts_trap hC.to_trap hRecv).compress256
  dh := (of_Stage2Contracts_trap hC.to_trap hRecv).dh
  pub_from_secret := (of_Stage2Contracts_trap hC.to_trap hRecv).pub_from_secret
  static_drop := (of_Stage2Contracts_trap hC.to_trap hRecv).static_drop
  shared_drop := (of_Stage2Contracts_trap hC.to_trap hRecv).shared_drop
  uuid_try_parse := (of_Stage2Contracts_trap hC.to_trap hRecv).uuid_try_parse
  decode_varint_slow := (of_Stage2Contracts_trap hC.to_trap hRecv).decode_varint_slow
  aes_enc := (of_Stage2Contracts_trap hC.to_trap hRecv).aes_enc
  aes_dec := (of_Stage2Contracts_trap hC.to_trap hRecv).aes_dec
  spqr_recv := hRecv
  format_inner := (of_Stage2Contracts_trap hC.to_trap hRecv).format_inner
  fmt_write := (of_Stage2Contracts_trap hC.to_trap hRecv).fmt_write
  decode_error_from := (of_Stage2Contracts_trap hC.to_trap hRecv).decode_error_from
  decode_error_push := (of_Stage2Contracts_trap hC.to_trap hRecv).decode_error_push

theorem of_tripleRatchetProgAt_trap (img : Obj.Image) (C : Crypto) (A : RustAlloc)
    (S : SpqrModel) (abs : String → Option (State → State))
    (hHooks : TripleRatchetHooks C A S abs)
    (hRecv : subroutine_ok (trTrapProgAt img.base C abs)
      ((trTrapProgAt img.base C abs).fnAddr spqrRecvName) ((spqrRecvEmptyAnySpec A).inImage img)) :
    Stage2ContractsWeak img C A (trTrapExterns C abs) :=
  of_Stage2Contracts_trap (Stage2Contracts_trap.of_tripleRatchetProgAt_trap img.base C A S abs hHooks) hRecv

theorem of_tripleRatchetProgAt (img : Obj.Image) (C : Crypto) (A : RustAlloc) (ctl : BitVec 64)
    (S : SpqrModel) (abs : String → Option (State → State))
    (hHooks : TripleRatchetHooks C A S abs)
    (hRecv : subroutine_ok (tripleRatchetProgAt img.base C ctl abs)
      ((tripleRatchetProgAt img.base C ctl abs).fnAddr spqrRecvName) ((spqrRecvEmptyAnySpec A).inImage img)) :
    Stage2ContractsWeak img C A (tripleRatchetExterns C ctl abs) :=
  of_Stage2Contracts (ctl := ctl) (Stage2Contracts.of_tripleRatchetProgAt img.base C A ctl S abs hHooks) hRecv

theorem of_tripleRatchetProgAt'_trap {img : Obj.Image} {C : Crypto} {A : RustAlloc}
    {S : SpqrModel} {abs : String → Option (State → State)}
    (hHooks : TripleRatchetHooks C A S abs)
    (hRecv : subroutine_ok (trTrapProgAt img.base C abs)
      ((trTrapProgAt img.base C abs).fnAddr spqrRecvName) ((spqrRecvEmptyAnySpec A).inImage img)) :
    Stage2ContractsWeak img C A (trTrapExterns C abs) :=
  of_tripleRatchetProgAt_trap img C A S abs hHooks hRecv

theorem of_tripleRatchetProgAt' {img : Obj.Image} {C : Crypto} {A : RustAlloc} {ctl : BitVec 64}
    {S : SpqrModel} {abs : String → Option (State → State)}
    (hHooks : TripleRatchetHooks C A S abs)
    (hRecv : subroutine_ok (tripleRatchetProgAt img.base C ctl abs)
      ((tripleRatchetProgAt img.base C ctl abs).fnAddr spqrRecvName) ((spqrRecvEmptyAnySpec A).inImage img)) :
    Stage2ContractsWeak img C A (tripleRatchetExterns C ctl abs) :=
  of_tripleRatchetProgAt img C A ctl S abs hHooks hRecv

end Stage2ContractsX

end CryptoVerification.LibsignalTripleRatchet
