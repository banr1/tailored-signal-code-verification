/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Arm64.Legacy.Object.Loader

/-!
# Executable ELF Region Materialization

Decomposes a relocated `Arm64.Obj.Image` into contiguous, uniformly permissioned `LoadedRegion`s
matching `Obj.Image.Loaded` and materializes them into a concrete `Memory` for differential test
harnesses.
-/

@[expose] public section

namespace Arm64

namespace Obj

/-- A contiguous memory region mapped by the loader, with its byte contents and uniform
    permission (`Perm.rx`, `Perm.ro`, or `Perm.rw`). -/
structure LoadedRegion where
  vaddr : BitVec 64
  bytes : List (BitVec 8)
  perm : Perm
  deriving DecidableEq, Repr, Inhabited

/-- Group a byte sequence starting at `addr` into contiguous `LoadedRegion`s with uniform
    permission `permOf (addr + i)`. -/
def groupByPerm (addr : BitVec 64) (permOf : BitVec 64 → Perm) (bytes : List (BitVec 8)) :
    List LoadedRegion :=
  let rec go : Nat → List (BitVec 8) → Option (BitVec 64 × Perm × List (BitVec 8)) →
      List LoadedRegion → List LoadedRegion
    | _, [], none, acc => acc.reverse
    | _, [], some ( startAddr, p, curRev ), acc =>
      ({ vaddr := startAddr, bytes := curRev.reverse, perm := p } :: acc).reverse
    | idx, b :: bs, none, acc =>
      let a := addr + BitVec.ofNat 64 idx
      go (idx + 1) bs (some (a, permOf a, [b])) acc
    | idx, b :: bs, some (startAddr, p, curRev), acc =>
      let a := addr + BitVec.ofNat 64 idx
      let p' := permOf a
      if p' == p then
        go (idx + 1) bs (some (startAddr, p, b :: curRev)) acc
      else
        let closed : LoadedRegion := { vaddr := startAddr, bytes := curRev.reverse, perm := p }
        go (idx + 1) bs (some (a, p', [b])) (closed :: acc)
  go 0 bytes none []

/-- Decompose an `Image` into the memory regions `Image.Loaded` describes (`code` as `r-x`,
    `roData` as `r--`, writable `data`/`.bss` as `rw-`, and `got` as `r--`). -/
def Image.toLoadedRegions (img : Image) : List LoadedRegion :=
  let codeReg := if img.code.isEmpty then [] else
    [{ vaddr := img.base, bytes := img.code, perm := .rx : LoadedRegion }]
  let dataRegs := groupByPerm img.dataAddr img.dataPerm img.data
  let gotBytes := img.gotBytes
  let gotReg := if gotBytes.isEmpty then [] else
    [{ vaddr := img.gotAddr, bytes := gotBytes, perm := .ro : LoadedRegion }]
  codeReg ++ dataRegs ++ gotReg

/-- Write the bytes and permissions of a `LoadedRegion` into `m`. -/
def LoadedRegion.applyToMemory (r : LoadedRegion) (m : Memory) : Memory :=
  let rec go : Nat → List (BitVec 8) → Memory → Memory
    | _, [], mem => mem
    | i, b :: bs, mem =>
      let a := r.vaddr + BitVec.ofNat 64 i
      let mem' : Memory := ⟨fun x => if x = a then some (some r.perm, b) else mem.cells x⟩
      go (i + 1) bs mem'
  go 0 r.bytes m

/-- Write a list of `LoadedRegion`s into `m`. -/
def applyRegions (m : Memory) (rs : List LoadedRegion) : Memory :=
  rs.foldl (fun acc r => r.applyToMemory acc) m

/-- Populate `m` with all loaded regions of `img`. -/
def Image.loadIntoMemory (img : Image) (m : Memory := Memory.empty) : Memory :=
  applyRegions m img.toLoadedRegions

end Obj

end Arm64
