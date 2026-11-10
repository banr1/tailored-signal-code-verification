/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Arm64.Trusted.Spec.SepLogic

/-!
# Separation-Logic Frame Complement and Mapping Assertions

Defines caller-stack preservation (`StackPreserved`), non-lazy read-write coverage (`Memory.RW`),
the total-memory heap complement (`Heap.complement`, `SepProp.complementSep`), and virtual-address
mapping reservation tokens (`mappedHeap`, `memMapped`). `SepProp.complementSep` and `memMapped` are
declared outside `@[expose]` to match `SepProp` connective opacity.
-/

namespace Arm64

@[expose] public section

/-- The caller's `len`-byte parent stack `[sp0, sp0 + len)` above `sp0` has identical byte
    contents in `m0` and `mf`. -/
def StackPreserved (m0 mf : Memory) (sp0 : BitVec 64) (len : Nat) : Prop :=
  ∀ a : BitVec 64, InRegion sp0 len a → mf.read8 a = m0.read8 a

/-- Every byte of `[base, base + len)` is mapped read-write (`some Perm.rw`) and not `lazyFree`
    (`m.permNoLazy a = some Perm.rw`) in `m`. -/
def Memory.RW (m : Memory) (base : BitVec 64) (len : Nat) : Prop :=
  ∀ a : BitVec 64, InRegion base len a → m.permNoLazy a = some Perm.rw

/-- The complement of partial heap `h` with respect to total memory `m`: `none` wherever `h` is
    defined or the byte is neither read-write nor `PROT_NONE`, `some .lazy` / `some (.rw (m.read8 a))`
    at every read-write byte where `h.phys a = none` (depending on `m.isLazyFree a`),
    `some .protNoneLazy` / `some (.protNone (m.read8 a))` at every `PROT_NONE` byte where
    `h.phys a = none` (depending on `m.isLazyFree a`), and `mapped` at every non-frozen anonymous
    mapped byte where `h.mapped a = false` (with empty ghost slots). -/
def Heap.complement (h : Heap) (m : Memory) : Heap :=
  { phys := fun a =>
      match h.phys a with
      | some _ => none
      | none   =>
        if m.perm a = some Perm.rw then
          if m.isLazyFree a then some .lazy else some (.rw (m.read8 a))
        else if m.perm a = some Perm.protNone then
          if m.isLazyFree a then some .protNoneLazy else some (.protNone (m.read8 a))
        else none
    mapped := fun a => !h.mapped a && (m.perm a).mapped && !(m.perm a).frozen && m.isAnon a }

/-- Partial heap owning the virtual-address mapping reservation token on `[base, base + len)`
    (with no physical byte cells or ghost state). -/
def mappedHeap (base : BitVec 64) (len : Nat) : Heap :=
  { phys := fun _ => none, mapped := fun a => decide (InRegion base len a) }

end -- @[expose] public section

public section

/-- Complement assertion of `P` in memory `m`: holds on `h.complement m` for some heap `h`
    satisfying `P.holds h` and `h.Matches m`. -/
@[inline] def SepProp.complementSep (P : SepProp) (m : Memory) : SepProp :=
  ⟨fun hc => ∃ h : Heap, P.holds h ∧ h.Matches m ∧ hc = h.complement m⟩

export SepProp (complementSep)

/-- Separation logic assertion owning the virtual-address mapping reservation token on
    `[base, base + len)`: witnesses that every byte in `[base, base + len)` is mapped in `Memory`
    (`(m.perm a).mapped = true`) without owning its physical byte cell `phys a`, so it can be
    held alongside `memRegion base len` (`memRegion base len ∗ memMapped base len`). -/
@[inline] def memMapped (base : BitVec 64) (len : Nat) : SepProp :=
  ⟨fun h => h = mappedHeap base len⟩

end -- public section

end Arm64
