/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Arm64.Legacy.Object.LinkedImage
public import Arm64.Trusted.Object.Placed
public import Arm64.Trusted.ISA.Semantics

/-!
# Legacy Segment Loader and Initial Memory Predicates

Converts a relocated `Obj.Image` into a `Program` (`Program.ofImage`) and defines the initial
memory-mapping predicates for loaded images (`Obj.Image.Loaded`, `Obj.Image.FrozenLoaded`,
`Obj.Image.RoDataLoaded`, and `Obj.Loads`).

`Obj.Image.Loaded` asserts that code and stubs at `Obj.Image.base` are mapped `r-x`,
`Obj.Image.roData` ranges `r--`, writable data/bss at `Obj.Image.dataAddr` `rw-`, the GOT at
`Obj.Image.gotAddr` `r--` (RELRO), `s.symtab = img.symtab`, and
`s.brkStart = img.brkStart ∧ s.brk = img.brkStart` (the page-aligned end of `.data`/`.bss`),
leaving extern data and all other addresses unconstrained. Pinning
`s.brkStart = s.brk = img.brkStart` models the unrandomized initial program break immediately
after `.data`/`.bss` (`randomize_va_space = 0`), without Linux's `arch_randomize_brk` ASLR
offset above `.bss`.
-/

@[expose] public section

namespace Arm64

namespace Program

/-- The code of `img` as a `Program`, with explicit supervisor-call handler `svc` (without
    referencing `Syscall.standard` in its constant closure) and hooks `externs` / `overrides`. -/
def ofImageWithSvc (svc : State → State) (img : Obj.Image)
    (externs : String → Option (State → State) := fun _ => none)
    (overrides : String → Option (State → State) := fun _ => none) : Program :=
  { base := img.base, code := img.code, symbols := img.symbols, stubs := img.stubs,
    externs, overrides, svc }

/-- The code of `img` as a `Program`, with hooks `externs` and `overrides` under `Syscall.standard`. -/
def ofImage (img : Obj.Image)
    (externs : String → Option (State → State) := fun _ => none)
    (overrides : String → Option (State → State) := fun _ => none) : Program :=
  { base := img.base, code := img.code, symbols := img.symbols, stubs := img.stubs,
    externs, overrides, svc := Syscall.standard }

end Program

namespace Obj

/-- The canonical program of `li` at base 0, without hooks, under explicit supervisor-call bundle
    `svc` (without referencing `Syscall.standard` in its constant closure). -/
def LinkedImage.toProgramWithSvc (svc : State → State) (li : LinkedImage) : Program :=
  { base := 0#64, code := li.code, symbols := li.symbols, stubs := li.stubs,
    externs := fun _ => none, overrides := fun _ => none, svc := svc }

/-- The canonical program of `li` at base 0, without hooks, under `Syscall.standard`. -/
def LinkedImage.toProgram (li : LinkedImage) : Program :=
  { base := 0#64, code := li.code, symbols := li.symbols, stubs := li.stubs,
    externs := fun _ => none, overrides := fun _ => none, svc := Syscall.standard }

/-- Runtime address of symbol or stub `name` when `li` is loaded at `base`. -/
def LinkedImage.fnAddr (li : LinkedImage) (base : BitVec 64) (name : String) : BitVec 64 :=
  ((li.toProgramWithSvc noSyscalls).rebase base).fnAddr name

/-- `img` is the result of loading `li` at its base `img.base`. -/
def Loads (li : LinkedImage) (img : Image) : Prop :=
  li.load img.base = .ok img

/-- Little-endian bytes of the GOT slots. -/
def Image.gotBytes (img : Image) : List (BitVec 8) :=
  img.got.flatMap (bytesLE 8)

/-- `a` lies in one of the image's rodata sections. -/
def Image.isRoData (img : Image) (a : BitVec 64) : Bool :=
  img.roData.any fun r => decide ((a - r.1).toNat < r.2)

/-- Permission of the data byte at `a`: read-only in rodata, read-write elsewhere. -/
def Image.dataPerm (img : Image) (a : BitVec 64) : Perm :=
  if img.isRoData a then Perm.ro else Perm.rw

/-- Every read-only byte of `img.data` (`img.isRoData (img.dataAddr + i)`) is in `m` with
    permission `some .ro` and not marked `lazyFree`. -/
def Image.RoDataLoaded (img : Image) (m : Memory) : Prop :=
  ∀ (i : Nat) (hi : i < img.data.length),
    let a := img.dataAddr + BitVec.ofNat 64 i
    img.isRoData a = true → m.read8 a = img.data[i] ∧ m.perm a = some Perm.ro ∧ m.isLazyFree a = false

/-- The frozen (read-only / executable) parts of `img` (code and stubs `r-x`, rodata `r--`,
    and the GOT `r--`) are in `s.mem` with their frozen permissions. Preserved by every
    execution step (`Step.frozenLoaded`).

    Irreducible; reason about it via `Obj.Image.frozenLoaded_iff` and the accessor lemmas in
    `ProofLib.Invariant`. -/
@[irreducible] def Image.FrozenLoaded (img : Image) (s : State) : Prop :=
  (Program.ofImageWithSvc noSyscalls img).CodeLoaded s.mem ∧
  img.RoDataLoaded s.mem ∧
  HoldsBytes s.mem img.gotAddr img.gotBytes (fun _ => Perm.ro)

/-- The image is in the memory of `s`, with the permissions in the module docs: code `r-x`
    (`CodeLoaded`), rodata `r--` and the rest of data/bss `rw-`, GOT `r--`,
    `s.symtab = img.symtab`, and `s.brkStart = img.brkStart ∧ s.brk = img.brkStart` (modeling the
    unrandomized initial program break at the page-aligned end of `.data`/`.bss`, without Linux's
    `arch_randomize_brk` ASLR offset).

    Irreducible (like `Program.CodeLoaded`); reason about it via `Obj.Image.loaded_iff` and the
    accessor lemmas in `ProofLib.Invariant`. -/
@[irreducible] def Image.Loaded (img : Image) (s : State) : Prop :=
  (Program.ofImageWithSvc noSyscalls img).CodeLoaded s.mem ∧
  HoldsBytes s.mem img.dataAddr img.data img.dataPerm ∧
  HoldsBytes s.mem img.gotAddr img.gotBytes (fun _ => Perm.ro) ∧
  s.symtab = img.symtab ∧
  s.brkStart = img.brkStart ∧
  s.brk = img.brkStart

end Obj

end Arm64
