/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Arm64.Legacy.Object.Loader
public import Arm64.Trusted.Spec.SepLogic
public import Arm64.Trusted.Spec.Hoare
public import Arm64.Trusted.Spec.GlobalAlloc

/-!
# Legacy `LinkedImage` Specification Helpers

Defines `imageInitialDataBss` and `imageDataBss` for `.rodata`/`.data`/`.bss` segments of a
loaded `Obj.LinkedImage`, position-independent `Obj.LinkedImage.subroutineOk`, and
`Rust.GlobalAllocAddrs.ofLinkedImage`.
-/

namespace Arm64

public section

/-- `.rodata`/`.data`/`.bss` segment of ELF object `obj` loaded at `base` in its freshly relocated
    initial state (`.ro` cells for `.rodata`, `.rw` cells for `.data`/`.bss`), with empty ghost state. -/
@[inline] def imageInitialDataBss (obj : Obj.LinkedImage) (base : BitVec 64) : SepProp :=
  ⟨fun h =>
    h.auth = (fun _ _ => none) ∧
    h.frag = (fun _ _ => none) ∧
    h.mapped = (fun _ => false) ∧
    ∃ img : Obj.Image,
      obj.load base = .ok img ∧
      ∀ a : BitVec 64,
        if hlt : (a - img.dataAddr).toNat < img.data.length then
          let b := img.data[(a - img.dataAddr).toNat]
          h.phys a = some (if img.isRoData a then HeapCell.ro b else HeapCell.rw b)
        else
          h.phys a = none⟩

/-- `.rodata`/`.data`/`.bss` segment of ELF object `obj` loaded at `base` after execution:
    `.rodata` bytes remain at their initial relocated values, while `.data`/`.bss` bytes own arbitrary
    writable values, with empty ghost state. -/
@[inline] def imageDataBss (obj : Obj.LinkedImage) (base : BitVec 64) : SepProp :=
  ⟨fun h =>
    h.auth = (fun _ _ => none) ∧
    h.frag = (fun _ _ => none) ∧
    h.mapped = (fun _ => false) ∧
    ∃ img : Obj.Image,
      obj.load base = .ok img ∧
      ∀ a : BitVec 64,
        if hlt : (a - img.dataAddr).toNat < img.data.length then
          let b := img.data[(a - img.dataAddr).toNat]
          if img.isRoData a then h.phys a = some (HeapCell.ro b)
          else ∃ b' : BitVec 8, h.phys a = some (HeapCell.rw b')
        else
          h.phys a = none⟩

end -- public section

@[expose] public section

/-- Position-independent subroutine correctness for a `LinkedImage` across all loaded
    images `Obj.Loads li img` (with universal quantification over the image and its
    load base `img.base` built in). -/
abbrev Obj.LinkedImage.subroutineOk {S α : Type} [ToBaseSpec S α] (li : Obj.LinkedImage)
    (fnName : String) (spec : S)
    (externs : String → Option (State → State) := fun _ => none)
    (overrides : String → Option (State → State) := fun _ => none) : Prop :=
  ∀ (img : Obj.Image), Obj.Loads li img →
    (Program.ofImage img externs overrides).subroutineOk fnName (ToBaseSpec.toSpec spec img.base)

namespace Rust.GlobalAllocAddrs

/-- Resolve `GlobalAllocAddrs` from a `LinkedImage` loaded at `base`. -/
def ofLinkedImage (li : Obj.LinkedImage) (base : BitVec 64)
    (allocSym : String := "__rust_alloc")
    (deallocSym : String := "__rust_dealloc")
    (reallocSym : String := "__rust_realloc")
    (allocZeroedSym : String := "__rust_alloc_zeroed") : GlobalAllocAddrs where
  alloc        := li.fnAddr base allocSym
  dealloc      := li.fnAddr base deallocSym
  realloc      := li.fnAddr base reallocSym
  alloc_zeroed := li.fnAddr base allocZeroedSym

end Rust.GlobalAllocAddrs

end -- @[expose] public section

end Arm64
