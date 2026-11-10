/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Arm64.Legacy.Object.Loader
public import Arm64.Trusted.Spec.RustRuntime
public import Arm64.Trusted.Spec.Hoare

/-!
# Legacy Compositional Library Specifications

Compositional multi-object library verification judgment (`library_ok`), per-symbol contracts
(`Contract`), library dependency DAGs (`LibrarySpec`), object-vs-extern linkage predicates
(`LinksIn`), and trusted dependency assumptions (`TrustedLibrariesOK`).
-/

@[expose] public section

namespace Arm64

/-- Function contract pairing a demangled symbol name `sym` with a `Spec α` over an
    existentially packaged ghost-state type `α`. -/
structure Contract where
  sym : String
  {α : Type}
  spec : Spec α

abbrev Contract.name (c : Contract) : String := c.sym

/-- Specification of a library (compiled object or hook-only interface) and its dependency DAG. -/
structure LibrarySpec where
  /-- Library identifier. -/
  name : String
  /-- Linker record of the object implementing the library, or `none` for a hook-only interface. -/
  obj : Option Obj.ObjectInfo := none
  /-- Direct library dependencies. -/
  deps : List LibrarySpec := []
  /-- Exported function contracts. -/
  contracts : List Contract := []

namespace LibrarySpec

/-- Dependency-first transitive closure of the library DAG rooted at `L`. -/
def closure : LibrarySpec → List LibrarySpec
  | ⟨name, obj, deps, contracts⟩ =>
    let rec go : List LibrarySpec → List LibrarySpec
      | [] => []
      | D :: rest => D.closure ++ go rest
    go deps ++ [⟨name, obj, deps, contracts⟩]

/-- Runtime entry address of `sym` for library `D` in `img`:
    - if `D.obj = some o` and `o.name` is a loaded object in `img.objSymbols`, looks up `sym`
      uniquely in `o`'s symbols (`some (img.base + off)` iff `sym` appears in `o` exactly once);
    - if `D.obj = some o` and `o` is not loaded (`D` is provided as externs), the address of
      `sym`'s extern stub in `img.stubs`, if any;
    - otherwise (an object-less library), resolves `sym` globally or as an extern stub
      (`img.symtab "" sym`). -/
def addr? (D : LibrarySpec) (img : Obj.Image) (sym : String) : Option (BitVec 64) :=
  match D.obj with
  | some o =>
    match Obj.lookup o.name img.objSymbols with
    | some syms => (Obj.lookupUnique sym syms).map fun off => img.base + BitVec.ofNat 64 off
    | none => (Obj.lookup sym img.stubs).map fun off => img.base + BitVec.ofNat 64 off
  | none =>
    img.symtab "" sym

/-- `D`'s object (if any) is linked into `li` (see `Obj.LinkedImage.honours`). -/
def ObjectLoaded (D : LibrarySpec) (li : Obj.LinkedImage) : Prop :=
  ∀ o, D.obj = some o → o ∈ li.objects

/-- `D` is supplied as externs instead of its object:
    - if `D.obj = some o`, no object linked into `li` has `o`'s name; and
    - no contracted symbol of `D` is defined in `li`, so calls resolve to its extern stub
      (`Obj.LinkedImage.resolveSym`), where `LibrarySpec.addr?` places `D`'s contracts. -/
def ProvidedAsExterns (D : LibrarySpec) (li : Obj.LinkedImage) : Prop :=
  (∀ o, D.obj = some o → Obj.lookup o.name li.objSymbols = none) ∧
  ∀ c ∈ D.contracts, Obj.lookup c.sym li.symbols = none

end LibrarySpec

/-- `img` is a loaded image containing every library of `specs`: `Obj.Loads li img` for some
    linked image `li`, and each `D ∈ specs` either has its object linked in (`D.ObjectLoaded li`)
    or belongs to `trusted` and is provided as externs (`D.ProvidedAsExterns li`). -/
def LinksIn (specs : List LibrarySpec) (img : Obj.Image)
    (trusted : List LibrarySpec := []) : Prop :=
  ∃ li : Obj.LinkedImage,
    (∀ D ∈ specs, D.ObjectLoaded li ∨ (D ∈ trusted ∧ D.ProvidedAsExterns li)) ∧
    Obj.Loads li img

/-- `spec` enriched with the image's frozen-memory and symbol-table invariant in its precondition. -/
def Spec.inImage {α : Type} (spec : Spec α) (img : Obj.Image) : Spec α :=
  { spec with pre := fun x s => ⌜img.FrozenLoaded s ∧ s.symtab = img.symtab⌝ ∗ spec.pre x s }

/-- Contract `c` of library `D` holds in `(img, X)` under explicit supervisor-call handler `svc`. -/
def Contract.HoldsWithSvc (svc : State → State) (D : LibrarySpec) (img : Obj.Image)
    (X : String → Option (State → State)) (c : Contract) : Prop :=
  ∃ a, D.addr? img c.sym = some a ∧
    subroutine_ok (Program.ofImageWithSvc svc img (Rust.withPanics X)) a (c.spec.inImage img)

/-- Every contract of every trusted library in `deps` holds at its resolved address in `img`
    under explicit supervisor-call handler `svc`. -/
def TrustedLibrariesOKWithSvc (svc : State → State) (trusted : List LibrarySpec) (img : Obj.Image)
    (X : String → Option (State → State)) (deps : List LibrarySpec := trusted) : Prop :=
  ∀ D ∈ deps, D ∈ trusted → ∀ c ∈ D.contracts, ∀ a,
    D.addr? img c.sym = some a →
    subroutine_ok (Program.ofImageWithSvc svc img (Rust.withPanics X)) a (c.spec.inImage img)

/-- Compositional library correctness judgment under explicit supervisor-call handler `svc`. -/
def library_ok_withSvc (svc : State → State) (L : LibrarySpec)
    (trusted : List LibrarySpec := []) : Prop :=
  (∀ D ∈ L.closure, D ∉ trusted → D.obj.isSome) ∧
  ∀ (img : Obj.Image) (X : String → Option (State → State)),
    LinksIn L.closure img trusted →
    TrustedLibrariesOKWithSvc svc trusted img X L.closure →
    ∀ D ∈ L.closure, D ∉ trusted → ∀ c ∈ D.contracts,
      Contract.HoldsWithSvc svc D img X c

/-- Contract `c` of library `D` holds in `(img, X)` when `c.sym` resolves via `D.addr?` to an
    entry address `a` satisfying `subroutine_ok` for `c.spec.inImage img` in
    `Program.ofImage img (Rust.withPanics X)`. -/
def Contract.Holds (D : LibrarySpec) (img : Obj.Image)
    (X : String → Option (State → State)) (c : Contract) : Prop :=
  ∃ a, D.addr? img c.sym = some a ∧
    subroutine_ok (Program.ofImage img (Rust.withPanics X)) a (c.spec.inImage img)

/-- Every contract of every trusted library in `deps` holds at its resolved address in `img`. -/
def TrustedLibrariesOK (trusted : List LibrarySpec) (img : Obj.Image)
    (X : String → Option (State → State)) (deps : List LibrarySpec := trusted) : Prop :=
  ∀ D ∈ deps, D ∈ trusted → ∀ c ∈ D.contracts, ∀ a,
    D.addr? img c.sym = some a →
    subroutine_ok (Program.ofImage img (Rust.withPanics X)) a (c.spec.inImage img)

/-- Compositional library correctness judgment: every non-trusted library in `L.closure` is backed
    by a concrete object, and in any linked image `img` satisfying `LinksIn` and
    `TrustedLibrariesOK`, every contract of every non-trusted library in `L.closure` holds. -/
def library_ok (L : LibrarySpec) (trusted : List LibrarySpec := []) : Prop :=
  (∀ D ∈ L.closure, D ∉ trusted → D.obj.isSome) ∧
  ∀ (img : Obj.Image) (X : String → Option (State → State)),
    LinksIn L.closure img trusted →
    TrustedLibrariesOK trusted img X L.closure →
    ∀ D ∈ L.closure, D ∉ trusted → ∀ c ∈ D.contracts,
      Contract.Holds D img X c

end Arm64
