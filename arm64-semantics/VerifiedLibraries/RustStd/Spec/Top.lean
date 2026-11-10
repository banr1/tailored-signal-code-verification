/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Arm64
public import Arm64.Trusted.Spec.RustHeap

/-!
# Shared Rust Allocator and Memory Hook Specifications

Re-exports the core `Arm64.Rust` allocator and `Vec<u8>` / `Box<[u8]>` predicates from
`Arm64.Trusted.Spec.RustHeap` and defines external hook contracts (`wrapperStack`, `wrapperFrame`,
`reallocSpec`, `memcpySpec`, `listMove`, `memmoveSpec`).
-/

@[expose] public section

namespace VerifiedLibraries.RustStd

open Arm64

export Arm64.Rust (Allocator hookStack hookFrame SmallLen vecBuf vecHeader vecAt vecOf boxAt
  allocSpec deallocSpec shimSpec)

/-- Stack bytes below `sp` that a `Vec`/`String` wrapper may use (its own frames plus the
    frames of the internal functions it calls plus `hookStack`). -/
abbrev wrapperStack : Nat := 4352

/-- The wrapper's stack: `wrapperStack` bytes below `sp`. -/
abbrev wrapperFrame (sp : BitVec 64) : SepProp :=
  memRegion (sp - BitVec.ofNat 64 wrapperStack) wrapperStack

/-- `__rust_realloc(p, old, 1, new)`, where the first `bs.length ≤ min old new` bytes are
    initialized. On failure (null) the old block is unchanged. Ghost: `(p, old, new, bs, sp)`. -/
rust_spec reallocSpec (ctx A : Allocator)
    (p : ptr) (old : u64) (_ : u64 := 1#64) (new : u64)
    (ghost bs : List (BitVec 8)) (sp : sp) : (ret : u64)
  requires_cond new ≠ 0 ∧ SmallLen new.toNat ∧ bs.length ≤ old.toNat ∧ bs.length ≤ new.toNat
  preserves     A.pool
  requires      A.live p old.toNat ∗ (p ↦ₛ bs) ∗
                memRegion (p + BitVec.ofNat 64 bs.length) (old.toNat - bs.length)
  preserves     hookFrame sp
  ensures       if ret = 0 then
                  A.live p old.toNat ∗ (p ↦ₛ bs) ∗
                    memRegion (p + BitVec.ofNat 64 bs.length) (old.toNat - bs.length)
                else
                  A.live ret new.toNat ∗ (ret ↦ₛ bs) ∗
                    memRegion (ret + BitVec.ofNat 64 bs.length) (new.toNat - bs.length)

/-- `memcpy(dst, src, bs.length)` for disjoint buffers. Ghost: `(dst, src, bs, sp)`. -/
rust_spec memcpySpec
    (dst : ptr) (src : slice8 bs) (ghost bs : List (BitVec 8)) (sp : sp)
  requires  memRegion dst bs.length
  ensures   (dst ↦ₛ bs)
  preserves (src ↦ₛ bs) ∗ hookFrame sp

/-- `buf` with its `len` bytes at `src` copied to `dst` (`memmove` semantics). -/
def listMove (buf : List (BitVec 8)) (dst src len : Nat) : List (BitVec 8) :=
  buf.take dst ++ (buf.drop src).take len ++ buf.drop (dst + len)

/-- `memmove(base + dst, base + src, len)` within one buffer `base ↦ₛ buf`.
    Ghost: `(base, buf, dst, src, len, sp)`. -/
rust_spec memmoveSpec
    (ghost base : ptr) (ghost buf : List (BitVec 8)) (ghost dst src len : Nat)
    (_ : ptr := base + BitVec.ofNat 64 dst)
    (_ : ptr := base + BitVec.ofNat 64 src)
    (_ : u64 := BitVec.ofNat 64 len)
    (sp : sp)
  requires_cond dst + len ≤ buf.length ∧ src + len ≤ buf.length
  requires      (base ↦ₛ buf)
  ensures       (base ↦ₛ listMove buf dst src len)
  preserves     hookFrame sp

end VerifiedLibraries.RustStd
