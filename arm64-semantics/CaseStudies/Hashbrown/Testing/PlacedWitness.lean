/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public meta import CaseStudies.Hashbrown.Generated.HashbrownPlacedWitness
public meta import Arm64.Trusted.Process
public meta import ProofLib.Process.ByteArray

/-!
# Multi-Block Placed-Library Witness Smoke Test

Evaluates the `MultiPlacedLib.InElf` conditions for `hashbrownLib` under `hashbrownPlacement`
against `hashbrown_cli.elf`, checking patched code segments, patched data segments, and unique
`.symtab` export entries.
-/

@[expose] public section

namespace CaseStudies.Hashbrown.Testing.PlacedWitness

open Arm64 Arm64.Obj Arm64.Process CaseStudies.Hashbrown

/-- Returns `n` bytes at `addr` with segment permissions when `[addr, addr + n)` lies within a
    single loaded segment of `img`. -/
meta def sliceAt (img : ElfImage) (addr : BitVec 64) (n : Nat) : Option (Perm × List (BitVec 8)) :=
  img.segments.findSome? fun r =>
    let i := (addr - r.start).toNat
    if i + n ≤ r.bytes.length then some (r.perm, (r.bytes.drop i).take n) else none

meta def mapsAt (img : ElfImage) (addr : BitVec 64) (bytes : List (BitVec 8)) (ok : Perm → Bool) :
    Bool :=
  match sliceAt img addr bytes.length with
  | some (p, bs) => ok p && bs == bytes
  | none => false

meta def elfPaths : List System.FilePath :=
  ["Implementation/hashbrown_cli.elf", "CaseStudies/Hashbrown/Implementation/hashbrown_cli.elf"]

/-- Checks all `MultiPlacedLib.InElf` obligations for `hashbrownLib` against `hashbrown_cli.elf`. -/
meta def checkInElf : IO Unit := do
  let some path ← elfPaths.findM? (·.pathExists)
    | throw <| .userError "hashbrown_cli.elf not found"
  let img ← match ElfImage.parseByteArray (← IO.FS.readBinFile path) with
    | .ok img => pure img
    | .error e => throw <| .userError e
  unless hashbrownLib.blocks.length == 13 do
    throw <| .userError s!"expected 13 blocks, got {hashbrownLib.blocks.length}"
  for i in [:hashbrownLib.blocks.length] do
    let b := hashbrownLib.blocks[i]!
    let text := b.patched (hashbrownLib.blockPlacement hashbrownPlacement i)
    unless mapsAt img (hashbrownPlacement.base i) text (· == Perm.rx) do
      throw <| .userError s!"patched block {i} ({b.symbols.map (·.1)}) differs from the ELF bytes"
  for d in hashbrownLib.data do
    let bytes := hashbrownLib.patchedData hashbrownPlacement d
    unless mapsAt img (hashbrownPlacement.ρ d.sym) bytes
        (fun p => if d.readOnly then p.r else p == Perm.rw) do
      throw <| .userError s!"data object {d.sym} differs from the ELF"
  for e in hashbrownLib.exports do
    let hits := hashbrownLib.blocks.zipIdx.filterMap fun (b, i) =>
      (lookup e b.symbols).map (i, ·)
    let ok := match hits with
      | [(i, off)] =>
        lookupUnique e img.symbols == some (hashbrownPlacement.base i + BitVec.ofNat 64 off)
      | _ => false
    unless ok do throw <| .userError s!"export {e} has no unique .symtab entry at its address"

/-- info: ok -/
#guard_msgs in
#eval do checkInElf; IO.println "ok"

end CaseStudies.Hashbrown.Testing.PlacedWitness
