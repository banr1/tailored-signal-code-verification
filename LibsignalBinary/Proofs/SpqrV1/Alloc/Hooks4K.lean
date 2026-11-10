/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.TripleRatchet.Hooks2
import GeneratedLean.LibsignalSessionCode -- shake: keep
import ProofLib.SepLogic.WP.StateNorm

@[expose] public section

set_option autoImplicit false

/-!
# 4 KiB Stack Allocator and Memory Contract Bundle (`AllocContracts4K`)

Packages `allocHookStack` (`4096` B) `subroutine_ok` contracts on
`tripleRatchetProgAtExt b ext` for `alloc`, `dealloc`, `realloc`, `shim`, `memcpy`
(including read-only `sessionMemcpyROSpec4K`), `memmove`, and `memset`.
-/

namespace CryptoVerification.SpqrV1.Alloc

open Arm64 ProofLib CryptoGames CryptoGames.LibsignalSession
open CryptoVerification CryptoVerification.RustHeap
open CryptoVerification.LibsignalSessionRepr CryptoVerification.LibsignalTripleRatchetRepr
open CryptoVerification.LibsignalTripleRatchet CryptoVerification.LibsignalSession

set_option maxRecDepth 200000
set_option maxHeartbeats 400000

/-- Read-only `memcpy(dst, src, len)` region contract (`src ↦ᵣ bs`) with trace preservation. -/
def sessionMemcpyROSpec4K : Spec (BitVec 64 × BitVec 64 × List (BitVec 8)) where
  pre := fun (dst, src, bs) s0 =>
    ⌜s0.readReg64 .x0 = dst ∧
     s0.readReg64 .x1 = src ∧
     (s0.readReg64 .x2).toNat = bs.length ∧
     bs.length ≤ 2 ^ 64⌝ ∗
    memRegion dst bs.length ∗
    (src ↦ᵣ bs)
  post := fun (dst, src, bs) s0 sf =>
    ⌜sf.readReg64 .x0 = dst ∧ sf.trace = s0.trace⌝ ∗ (dst ↦ₛ bs) ∗ (src ↦ᵣ bs)

theorem hookMemcpy_sessionMemcpyROSpec4K_ok : HookOk hookMemcpy sessionMemcpyROSpec4K := by
  refine retHook_ok fun ⟨dst, src, bs⟩ R s0 _ hpre _ => ?_
  simp only [sessionMemcpyROSpec4K, sepConj_assoc, satisfies_pure_sepConj] at hpre
  rcases hpre with ⟨⟨hx0, hx1, hx2, hlen⟩, hmem⟩
  have hsrc_front : s0.mem ⊨ (src ↦ᵣ bs) ∗ (memRegion dst bs.length ∗ R) := by
    rwa [← sepConj_assoc, sepConj_comm (memRegion dst bs.length), sepConj_assoc] at hmem
  have hread := (IsBlockRO.pointsToBytesRO src bs hlen).read hsrc_front
  refine ⟨?_, rfl, ‹_›, ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩, ?_⟩
  · dsimp only; rw [hx0, hx1, hx2, hread]; exact keepsFrozen_writeBytes_of_memRegion bs hlen hmem
  · simp only [sessionMemcpyROSpec4K, retHook, State.readReg64_setPC, State.readReg64_setMem,
      hx0, hx1, hx2, hread, sepConj_assoc, satisfies_pure_sepConj]
    exact ⟨⟨trivial, rfl⟩, satisfies_writeBytes bs hlen hmem⟩

theorem libcMemcpyRO_of_sessionMemcpyRO4K {prog : Program} {addr : BitVec 64} {stk : Nat}
    (h : subroutine_ok prog addr (withStack sessionMemcpyROSpec4K stk)) :
    subroutine_ok prog addr (libcMemcpyROSpec stk) := by
  refine subroutine_ok_map h ?_
  rintro ⟨dst, src, bs⟩ R s0 hpre
  refine ⟨(dst, src, bs), R, ?_, ?_⟩
  · dsimp only [libcMemcpyROSpec, withStack, sessionMemcpyROSpec4K] at hpre ⊢
    simp only [sepConj_assoc, satisfies_pure_sepConj] at hpre ⊢
    rcases hpre with ⟨⟨hx0, hx1, hx2⟩, hm⟩
    have hle : bs.length ≤ 2 ^ 64 := by rw [← hx2]; exact Nat.le_of_lt (s0.readReg64 .x2).isLt
    exact ⟨⟨hx0, hx1, hx2, hle⟩, hm⟩
  · intro sf hpost
    dsimp only [libcMemcpyROSpec, withStack, sessionMemcpyROSpec4K] at hpost ⊢
    simp only [sepConj_assoc, satisfies_pure_sepConj] at hpost ⊢
    exact ⟨hpost.1.1, hpost.2⟩

/-- 4 KiB (`allocHookStack`) allocator, memory, and shim contract bundle on `tripleRatchetProgAtExt b ext`. -/
structure AllocContracts4K (b : BitVec 64) (A : RustAlloc)
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
      ((tripleRatchetProgAtExt b ext).fnAddr shimName) sessionShimSpec
  memcpy : ∀ (hookStack : Nat), allocHookStack ≤ hookStack → hookStack ≤ 2 ^ 64 →
    subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr memcpyName) (libcMemcpySpec hookStack)
  session_memcpy : ∀ (hookStack : Nat), allocHookStack ≤ hookStack → hookStack ≤ 2 ^ 64 →
    subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr memcpyName) (sessionMemcpySpec hookStack)
  memcpy_ro : ∀ (hookStack : Nat), allocHookStack ≤ hookStack → hookStack ≤ 2 ^ 64 →
    subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr memcpyName) (libcMemcpyROSpec hookStack)
  session_memcpy_region_ro : ∀ (hookStack : Nat), allocHookStack ≤ hookStack → hookStack ≤ 2 ^ 64 →
    subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr memcpyName)
      (withStack sessionMemcpyROSpec4K hookStack)
  memcpy_region : ∀ (hookStack : Nat), allocHookStack ≤ hookStack → hookStack ≤ 2 ^ 64 →
    subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr memcpyName) (withStack memcpyRegionSpec hookStack)
  session_memcpy_region : ∀ (hookStack : Nat), allocHookStack ≤ hookStack → hookStack ≤ 2 ^ 64 →
    subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr memcpyName)
      (withStack sessionMemcpyRegionSpec hookStack)
  memmove : ∀ (hookStack : Nat), allocHookStack ≤ hookStack → hookStack ≤ 2 ^ 64 →
    subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr memmoveName) (libcMemmoveSpec hookStack)
  session_memmove : ∀ (hookStack : Nat), allocHookStack ≤ hookStack → hookStack ≤ 2 ^ 64 →
    subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr memmoveName) (sessionMemmoveSpec hookStack)
  memset : ∀ (hookStack : Nat), allocHookStack ≤ hookStack → hookStack ≤ 2 ^ 64 →
    subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr memsetName) (libcMemsetSpec hookStack)
  session_memset : ∀ (hookStack : Nat), allocHookStack ≤ hookStack → hookStack ≤ 2 ^ 64 →
    subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr memsetName) (sessionMemsetSpec hookStack)
  memset_region : ∀ (hookStack : Nat), allocHookStack ≤ hookStack → hookStack ≤ 2 ^ 64 →
    subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr memsetName) (withStack memsetRegionSpec hookStack)
  session_memset_region : ∀ (hookStack : Nat), allocHookStack ≤ hookStack → hookStack ≤ 2 ^ 64 →
    subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr memsetName)
      (withStack sessionMemsetRegionSpec hookStack)

namespace AllocContracts4K

variable {b : BitVec 64} {A : RustAlloc} {ext : String → Option (State → State)}

theorem alloc_ok_at (hA : AllocContracts4K b A ext) (name : String) (k : Nat)
    (hk : libsignalSessionCode.fnOff name + k = libsignalSessionCode.fnOff allocName := by
      simp only [arm64_norm]) :
    subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr name + BitVec.ofNat 64 k) (rustAllocSpec A) :=
  sub_ok_at_of_fnAddr hA.alloc name k hk

theorem dealloc_ok_at (hA : AllocContracts4K b A ext) (name : String) (k : Nat)
    (hk : libsignalSessionCode.fnOff name + k = libsignalSessionCode.fnOff deallocName := by
      simp only [arm64_norm]) :
    subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr name + BitVec.ofNat 64 k) (rustDeallocSpec A) :=
  sub_ok_at_of_fnAddr hA.dealloc name k hk

theorem realloc_ok_at (hA : AllocContracts4K b A ext) (name : String) (k : Nat)
    (hk : libsignalSessionCode.fnOff name + k = libsignalSessionCode.fnOff reallocName := by
      simp only [arm64_norm]) :
    subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr name + BitVec.ofNat 64 k) (rustReallocSpec A) :=
  sub_ok_at_of_fnAddr hA.realloc name k hk

theorem shim_ok_at (hA : AllocContracts4K b A ext) (name : String) (k : Nat)
    (hk : libsignalSessionCode.fnOff name + k = libsignalSessionCode.fnOff shimName := by
      simp only [arm64_norm]) :
    subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr name + BitVec.ofNat 64 k) sessionShimSpec :=
  sub_ok_at_of_fnAddr hA.shim name k hk

theorem session_shim_ok_at (hA : AllocContracts4K b A ext) (name : String) (k : Nat)
    (hk : libsignalSessionCode.fnOff name + k = libsignalSessionCode.fnOff shimName := by
      simp only [arm64_norm]) :
    subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr name + BitVec.ofNat 64 k) sessionShimSpec :=
  sub_ok_at_of_fnAddr hA.shim name k hk

theorem memcpy_ok_at (hA : AllocContracts4K b A ext) (name : String) (k : Nat)
    (hookStack : Nat := allocHookStack)
    (hstack : allocHookStack ≤ hookStack := by decide)
    (hstack_le : hookStack ≤ 2 ^ 64 := by decide)
    (hk : libsignalSessionCode.fnOff name + k = libsignalSessionCode.fnOff memcpyName := by
      simp only [arm64_norm]) :
    subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr name + BitVec.ofNat 64 k) (libcMemcpySpec hookStack) :=
  sub_ok_at_of_fnAddr (hA.memcpy hookStack hstack hstack_le) name k hk

theorem session_memcpy_ok_at (hA : AllocContracts4K b A ext) (name : String) (k : Nat)
    (hookStack : Nat := allocHookStack)
    (hstack : allocHookStack ≤ hookStack := by decide)
    (hstack_le : hookStack ≤ 2 ^ 64 := by decide)
    (hk : libsignalSessionCode.fnOff name + k = libsignalSessionCode.fnOff memcpyName := by
      simp only [arm64_norm]) :
    subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr name + BitVec.ofNat 64 k)
      (sessionMemcpySpec hookStack) :=
  sub_ok_at_of_fnAddr (hA.session_memcpy hookStack hstack hstack_le) name k hk

theorem memcpy_ro_ok_at (hA : AllocContracts4K b A ext) (name : String) (k : Nat)
    (hookStack : Nat := allocHookStack)
    (hstack : allocHookStack ≤ hookStack := by decide)
    (hstack_le : hookStack ≤ 2 ^ 64 := by decide)
    (hk : libsignalSessionCode.fnOff name + k = libsignalSessionCode.fnOff memcpyName := by
      simp only [arm64_norm]) :
    subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr name + BitVec.ofNat 64 k)
      (libcMemcpyROSpec hookStack) :=
  sub_ok_at_of_fnAddr (hA.memcpy_ro hookStack hstack hstack_le) name k hk

theorem session_memcpy_region_ro_ok_at (hA : AllocContracts4K b A ext) (name : String) (k : Nat)
    (hookStack : Nat := allocHookStack)
    (hstack : allocHookStack ≤ hookStack := by decide)
    (hstack_le : hookStack ≤ 2 ^ 64 := by decide)
    (hk : libsignalSessionCode.fnOff name + k = libsignalSessionCode.fnOff memcpyName := by
      simp only [arm64_norm]) :
    subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr name + BitVec.ofNat 64 k)
      (withStack sessionMemcpyROSpec4K hookStack) :=
  sub_ok_at_of_fnAddr (hA.session_memcpy_region_ro hookStack hstack hstack_le) name k hk

theorem memcpy_region_ok_at (hA : AllocContracts4K b A ext) (name : String) (k : Nat)
    (hookStack : Nat := allocHookStack)
    (hstack : allocHookStack ≤ hookStack := by decide)
    (hstack_le : hookStack ≤ 2 ^ 64 := by decide)
    (hk : libsignalSessionCode.fnOff name + k = libsignalSessionCode.fnOff memcpyName := by
      simp only [arm64_norm]) :
    subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr name + BitVec.ofNat 64 k)
      (withStack memcpyRegionSpec hookStack) :=
  sub_ok_at_of_fnAddr (hA.memcpy_region hookStack hstack hstack_le) name k hk

theorem session_memcpy_region_ok_at (hA : AllocContracts4K b A ext) (name : String) (k : Nat)
    (hookStack : Nat := allocHookStack)
    (hstack : allocHookStack ≤ hookStack := by decide)
    (hstack_le : hookStack ≤ 2 ^ 64 := by decide)
    (hk : libsignalSessionCode.fnOff name + k = libsignalSessionCode.fnOff memcpyName := by
      simp only [arm64_norm]) :
    subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr name + BitVec.ofNat 64 k)
      (withStack sessionMemcpyRegionSpec hookStack) :=
  sub_ok_at_of_fnAddr (hA.session_memcpy_region hookStack hstack hstack_le) name k hk

theorem memmove_ok_at (hA : AllocContracts4K b A ext) (name : String) (k : Nat)
    (hookStack : Nat := allocHookStack)
    (hstack : allocHookStack ≤ hookStack := by decide)
    (hstack_le : hookStack ≤ 2 ^ 64 := by decide)
    (hk : libsignalSessionCode.fnOff name + k = libsignalSessionCode.fnOff memmoveName := by
      simp only [arm64_norm]) :
    subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr name + BitVec.ofNat 64 k)
      (libcMemmoveSpec hookStack) :=
  sub_ok_at_of_fnAddr (hA.memmove hookStack hstack hstack_le) name k hk

theorem session_memmove_ok_at (hA : AllocContracts4K b A ext) (name : String) (k : Nat)
    (hookStack : Nat := allocHookStack)
    (hstack : allocHookStack ≤ hookStack := by decide)
    (hstack_le : hookStack ≤ 2 ^ 64 := by decide)
    (hk : libsignalSessionCode.fnOff name + k = libsignalSessionCode.fnOff memmoveName := by
      simp only [arm64_norm]) :
    subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr name + BitVec.ofNat 64 k)
      (sessionMemmoveSpec hookStack) :=
  sub_ok_at_of_fnAddr (hA.session_memmove hookStack hstack hstack_le) name k hk

theorem memset_ok_at (hA : AllocContracts4K b A ext) (name : String) (k : Nat)
    (hookStack : Nat := allocHookStack)
    (hstack : allocHookStack ≤ hookStack := by decide)
    (hstack_le : hookStack ≤ 2 ^ 64 := by decide)
    (hk : libsignalSessionCode.fnOff name + k = libsignalSessionCode.fnOff memsetName := by
      simp only [arm64_norm]) :
    subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr name + BitVec.ofNat 64 k)
      (libcMemsetSpec hookStack) :=
  sub_ok_at_of_fnAddr (hA.memset hookStack hstack hstack_le) name k hk

theorem session_memset_ok_at (hA : AllocContracts4K b A ext) (name : String) (k : Nat)
    (hookStack : Nat := allocHookStack)
    (hstack : allocHookStack ≤ hookStack := by decide)
    (hstack_le : hookStack ≤ 2 ^ 64 := by decide)
    (hk : libsignalSessionCode.fnOff name + k = libsignalSessionCode.fnOff memsetName := by
      simp only [arm64_norm]) :
    subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr name + BitVec.ofNat 64 k)
      (sessionMemsetSpec hookStack) :=
  sub_ok_at_of_fnAddr (hA.session_memset hookStack hstack hstack_le) name k hk

theorem memset_region_ok_at (hA : AllocContracts4K b A ext) (name : String) (k : Nat)
    (hookStack : Nat := allocHookStack)
    (hstack : allocHookStack ≤ hookStack := by decide)
    (hstack_le : hookStack ≤ 2 ^ 64 := by decide)
    (hk : libsignalSessionCode.fnOff name + k = libsignalSessionCode.fnOff memsetName := by
      simp only [arm64_norm]) :
    subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr name + BitVec.ofNat 64 k)
      (withStack memsetRegionSpec hookStack) :=
  sub_ok_at_of_fnAddr (hA.memset_region hookStack hstack hstack_le) name k hk

theorem session_memset_region_ok_at (hA : AllocContracts4K b A ext) (name : String) (k : Nat)
    (hookStack : Nat := allocHookStack)
    (hstack : allocHookStack ≤ hookStack := by decide)
    (hstack_le : hookStack ≤ 2 ^ 64 := by decide)
    (hk : libsignalSessionCode.fnOff name + k = libsignalSessionCode.fnOff memsetName := by
      simp only [arm64_norm]) :
    subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr name + BitVec.ofNat 64 k)
      (withStack sessionMemsetRegionSpec hookStack) :=
  sub_ok_at_of_fnAddr (hA.session_memset_region hookStack hstack hstack_le) name k hk

theorem of_allocContracts (hA : AllocContracts b A ext)
    (hRO : ∀ (hookStack : Nat), allocHookStack ≤ hookStack → hookStack ≤ 2 ^ 64 →
      subroutine_ok (tripleRatchetProgAtExt b ext)
        ((tripleRatchetProgAtExt b ext).fnAddr memcpyName)
        (withStack sessionMemcpyROSpec4K hookStack)) :
    AllocContracts4K b A ext where
  alloc := hA.alloc
  dealloc := hA.dealloc
  realloc := hA.realloc
  shim := hA.shim
  memcpy stk _ _ := hA.memcpy stk
  session_memcpy stk _ _ := hA.session_memcpy stk
  memcpy_ro stk hlo hhi := libcMemcpyRO_of_sessionMemcpyRO4K (hRO stk hlo hhi)
  session_memcpy_region_ro stk hlo hhi := hRO stk hlo hhi
  memcpy_region stk _ _ := subroutine_ok_withStack_of_subroutine_ok hA.memcpy_region stk
  session_memcpy_region stk _ _ :=
    subroutine_ok_withStack_of_subroutine_ok hA.session_memcpy_region stk
  memmove stk _ _ := hA.memmove stk
  session_memmove stk _ _ := hA.session_memmove stk
  memset stk hle _ := hA.memset stk (Nat.lt_of_lt_of_le (by decide : 0 < allocHookStack) hle)
  session_memset stk hle _ :=
    hA.session_memset stk (Nat.lt_of_lt_of_le (by decide : 0 < allocHookStack) hle)
  memset_region stk _ _ := subroutine_ok_withStack_of_subroutine_ok hA.memset_region stk
  session_memset_region stk _ _ :=
    subroutine_ok_withStack_of_subroutine_ok hA.session_memset_region stk

private theorem stub_sessionMemcpyRO4K_of_hookSat (b : BitVec 64)
    {ext : String → Option (State → State)}
    (hRO : HookSat ext memcpyName sessionMemcpyROSpec4K) (stk : Nat) :
    subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr memcpyName)
      (withStack sessionMemcpyROSpec4K stk) := by
  have h0 : subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr memcpyName) sessionMemcpyROSpec4K := by
    have h := hook_ok_at (P := libsignalSessionCode) (b := b) (hooks := ext)
      (name := memcpyName) (hname := memcpyName) (stub := libsignalSessionCode.fnOff memcpyName)
      (k := 0) rfl (Nat.add_zero _) (by simp only [arm64_norm])
      (fun _ => by simp only [arm64_norm]) (by simp [Rust.isPanicSymbol, memcpyName]) hRO
    simpa only [BitVec.ofNat_eq_ofNat, BitVec.add_zero] using h
  exact subroutine_ok_withStack_of_subroutine_ok h0 stk

theorem of_tripleRatchetProgAt (b : BitVec 64) (C : Crypto) (A : RustAlloc) (ctl : BitVec 64)
    (abs : String → Option (State → State)) (hA : AllocHooks A abs) :
    AllocContracts4K b A (tripleRatchetExterns C ctl abs) :=
  of_allocContracts (AllocContracts.of_tripleRatchetProgAt b C A ctl abs hA) fun stk _ _ =>
    stub_sessionMemcpyRO4K_of_hookSat b ⟨hookMemcpy, rfl, hookMemcpy_sessionMemcpyROSpec4K_ok⟩ stk

theorem of_tripleRatchetProgAt_trap (b : BitVec 64) (C : Crypto) (A : RustAlloc)
    (abs : String → Option (State → State)) (hA : AllocHooks A abs) :
    AllocContracts4K b A (trTrapExterns C abs) :=
  of_allocContracts (AllocContracts.of_tripleRatchetProgAt_trap b C A abs hA) fun stk _ _ =>
    stub_sessionMemcpyRO4K_of_hookSat b ⟨hookMemcpy, rfl, hookMemcpy_sessionMemcpyROSpec4K_ok⟩ stk

end AllocContracts4K

end CryptoVerification.SpqrV1.Alloc
