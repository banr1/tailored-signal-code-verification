/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Arm64
public import ProofLib.SepLogic.WP.Defs

/-!
# Call-Site-Indexed Symbolic Allocator and `free` Contracts

Defines the call-site-indexed symbolic allocator model `ProofLib.Allocator` together with
spatial ownership predicates (`optRegion`, `optZeroBytes`, `allocAt`, `callocAt`, `allocSeq`)
and ownership-consuming `free` specifications (`libcFreeSpec`, `freeRegionSpec`).
Corresponding `HookOk` soundness witnesses are proved in `ProofLib.Hoare.LibcHooks`.
-/

@[expose] public section

namespace ProofLib

open Arm64

/-- Call-site-indexed symbolic allocator model: maps `(callIdx, reqBytes)` to the returned
    pointer (`0#64` on allocation failure, or a non-null region pointer on success),
    so consecutive allocations with identical `reqBytes` at distinct call indices `0, 1, ...`
    never alias.
    Marked `protected` so `open ProofLib` does not shadow or collide with `Arm64.Allocator`
    (use `ProofLib.Allocator`). -/
protected structure Allocator where
  /-- Returned pointer for allocation call site `idx` requesting `req` bytes (`0#64` on OOM). -/
  ptr : Nat → BitVec 64 → BitVec 64


namespace Allocator

/-- Optional uninitialized heap region: `emp` when `ptr = 0#64`, `memRegion ptr len` otherwise. -/
def optRegion (ptr : BitVec 64) (len : Nat) : SepProp :=
  if ptr = 0#64 then emp else memRegion ptr len

/-- Optional zero-initialized heap region (`calloc`): `emp` when `ptr = 0#64`,
    `ptr ↦ₛ List.replicate len 0#8` otherwise. -/
def optZeroBytes (ptr : BitVec 64) (len : Nat) : SepProp :=
  if ptr = 0#64 then emp else (ptr ↦ₛ List.replicate len 0#8)

/-- Spatial region for allocation call site `idx` requesting `req` bytes of length `len`. -/
def allocAt (alloc : ProofLib.Allocator) (idx : Nat) (req : BitVec 64) (len : Nat := req.toNat) : SepProp :=
  optRegion (alloc.ptr idx req) len

/-- Spatial zero-initialized region for `calloc` call site `idx` with `(nmemb, size)`.
    By default `len := (nmemb * size).toNat` matches the 64-bit byte request `nmemb * size`
    passed to `alloc.ptr` (which equals `nmemb.toNat * size.toNat` whenever `nmemb.toNat * size.toNat < 2 ^ 64`). -/
def callocAt (alloc : ProofLib.Allocator) (idx : Nat) (nmemb size : BitVec 64)
    (len : Nat := (nmemb * size).toNat) : SepProp :=
  optZeroBytes (alloc.ptr idx (nmemb * size)) len

/-- Sequence of call-site-indexed allocations starting at index `startIdx`:
    `allocSeq alloc startIdx [(req₀, len₀), (req₁, len₁), ...]` expands to the separating
    conjunction `alloc.allocAt startIdx req₀ len₀ ∗ alloc.allocAt (startIdx + 1) req₁ len₁ ∗ ...`,
    guaranteeing that all non-null allocations in the sequence are mutually disjoint even when
    multiple calls pass the same `req`. -/
def allocSeq (alloc : ProofLib.Allocator) : Nat → List (BitVec 64 × Nat) → SepProp
  | _, [] => emp
  | idx, (req, len) :: rest =>
    alloc.allocAt idx req len ∗ allocSeq alloc (idx + 1) rest

end Allocator

/-- Convenience alias for `ProofLib.Allocator.allocSeq`. -/
abbrev allocSeq := ProofLib.Allocator.allocSeq

/-- Ownership-consuming specification for `void free(void *ptr)` with a `hookStack`-byte stack frame:
    consumes `ProofLib.Allocator.optRegion ptr len` (`emp` when `ptr = 0#64`, `memRegion ptr len` when
    `ptr ≠ 0#64`) in the precondition and retains only the caller's `hookStack`-byte stack region in
    the postcondition. -/
def libcFreeSpec (hookStack : Nat := 4096) : Spec (BitVec 64 × Nat) where
  pre := fun (ptr, len) s0 =>
    ⌜s0.readReg64 .x0 = ptr⌝ ∗
    ProofLib.Allocator.optRegion ptr len ∗
    memRegion (s0.sp - BitVec.ofNat 64 hookStack) hookStack
  post := fun _ s0 _ =>
    memRegion (s0.sp - BitVec.ofNat 64 hookStack) hookStack

/-- Ownership-consuming specification for `void free(void *ptr)` without a stack-frame conjunct:
    consumes `ProofLib.Allocator.optRegion ptr len` in `pre` and leaves `emp` in `post`. -/
def freeRegionSpec : Spec (BitVec 64 × Nat) where
  pre := fun (ptr, len) s0 =>
    ⌜s0.readReg64 .x0 = ptr⌝ ∗
    ProofLib.Allocator.optRegion ptr len
  post := fun _ _ _ =>
    emp

end ProofLib
