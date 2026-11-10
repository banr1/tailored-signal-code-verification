/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Arm64
public import ProofLib.Process.FastParse
public import LibsignalBinary.Specifications.SignalSession.CliProcess
public import Symbolic.BugInjection.Proofs.CliExec.CompHooks0Placed
public import Symbolic.BugInjection.Proofs.CliExec.RadixMemAux
public import Symbolic.BugInjection.Proofs.CliExec.RadixMem
public import Symbolic.BugInjection.Proofs.CliExec.RadixMemLine
public import Symbolic.BugInjection.Proofs.CliExec.RadixMemPlaced
public import Symbolic.BugInjection.Proofs.CliExec.FastHooksPlaced
public import Symbolic.BugInjection.Proofs.CliExec.PlacedExecCore
public import Symbolic.BugInjection.Proofs.CliExec.ElfFullSpecPlacedCore

/-!
# Placed ELF Prebuilder

Constructs a `PrebuiltElfPlaced` bundle from a placed `ElfImage`, token-patch addresses,
`mallocng` subroutine addresses, and hooked symbol stubs. Validates ELF header and segment bounds,
rejects hooked `"grow_one"`, applies placed token patches to initial segment lines, and checks
depth-4 radix-tree spine fullness.
-/

@[expose] public section

set_option autoImplicit false

namespace Symbolic.BugInjection.Proofs.CliExec.PrebuildPlaced

open Arm64 Arm64.Process ProofLib
open CryptoVerification.SignalSession (CliHooks)
open Symbolic.BugInjection.Proofs.CliExec.CompHooks0Placed (compHooks0)
open Symbolic.BugInjection.Proofs.CliExec.RadixMemAux (BinTree Line64 withForcedBinTree
  withForcedBinTree_eq)
open Symbolic.BugInjection.Proofs.CliExec.RadixMem (FastMem)
open Symbolic.BugInjection.Proofs.CliExec.RadixMemLine (loadRegionsLines)
open Symbolic.BugInjection.Proofs.CliExec.RadixMemPlaced (patchTokenFastMemPlaced)
open Symbolic.BugInjection.Proofs.CliExec.FastHooksPlaced (MallocngCallAddrs)
open Symbolic.BugInjection.Proofs.CliExec.PlacedExecCore (PrebuiltElfPlaced checkElfPrebuildOkPlaced
  overlayHooksPlaced progPlacedDepth)
open Symbolic.BugInjection.Proofs.CliExec.ElfFullSpecPlacedCore (ElfFullSpecPlaced isFullDepth3
  isFullDepth4 prebuiltOfFullPlaced)

/-- Depth-bounded check whether `target` occurs as a `.twig` value in a `BinTree String`. -/
def binTreeHasString : Nat → String → BinTree String → Bool
  | _, _, .empty => false
  | _, target, .twig _ v => v == target
  | 0, _, .branch _ _ => false
  | d + 1, target, .branch l r => binTreeHasString d target l || binTreeHasString d target r

theorem isFullDepth3_of_isFullDepth4 {α : Type} {t : BinTree α}
    (h : isFullDepth4 t = true) : isFullDepth3 t = true := by
  cases t with
  | empty | twig _ _ => nomatch h
  | branch l r =>
    simp only [isFullDepth4, Bool.and_eq_true] at h
    rcases h with ⟨hl, hr⟩
    unfold isFullDepth3 at hl hr
    split at hl
    · split at hr
      · rfl
      · nomatch hr
    · nomatch hl

/-- Variant of `prebuildElfPlaced` taking precomputed `(region, length)` pairs `regsWithLen`.
Checks header and segment bounds, rejects `"grow_one"` in the hook tree, applies token patches,
and requires depth-4 spine fullness on `baseLines`. -/
def prebuildElfPlacedWithLens (W : CliHooks) (elf : ElfImage)
    (regsWithLen : List (Snapshot.Region × Nat))
    (tokStorageAddr tokOnceAddr : BitVec 64)
    (addrs : MallocngCallAddrs)
    (stubs : List (String × Nat)) : Option PrebuiltElfPlaced :=
  if elf.phent == 56 && checkElfPrebuildOkPlaced elf regsWithLen tokStorageAddr tokOnceAddr then
    let hooks := overlayHooksPlaced W stubs .empty
    if binTreeHasString (progPlacedDepth + 1) "grow_one" hooks then
      none
    else
      let fm0 : FastMem := { lines := loadRegionsLines elf.segments, stackBase := 0, stackTop := 0 }
      withForcedBinTree (patchTokenFastMemPlaced tokStorageAddr tokOnceAddr fm0).lines fun baseLines =>
        if isFullDepth3 baseLines && isFullDepth4 baseLines then
          some {
            baseLines := baseLines
            prog := { addrs := addrs, hooks := hooks, rxLines := baseLines }
          }
        else
          none
  else
    none

/-- Build a `PrebuiltElfPlaced` bundle from `elf`, token-patch addresses, `mallocng` call addresses,
and hook stubs. -/
def prebuildElfPlaced (W : CliHooks) (elf : ElfImage)
    (tokStorageAddr tokOnceAddr : BitVec 64)
    (addrs : MallocngCallAddrs)
    (stubs : List (String × Nat)) : Option PrebuiltElfPlaced :=
  prebuildElfPlacedWithLens W elf (mapRegionsWithLen elf.segments)
    tokStorageAddr tokOnceAddr addrs stubs

theorem prebuildElfPlacedWithLens_eq_prebuildElfPlaced (W : CliHooks) (elf : ElfImage)
    {regsWithLen : List (Snapshot.Region × Nat)}
    (hlens : regsWithLen = elf.segments.map (fun r => (r, r.bytes.length)))
    (tokStorageAddr tokOnceAddr : BitVec 64)
    (addrs : MallocngCallAddrs)
    (stubs : List (String × Nat)) :
    prebuildElfPlacedWithLens W elf regsWithLen tokStorageAddr tokOnceAddr addrs stubs =
      prebuildElfPlaced W elf tokStorageAddr tokOnceAddr addrs stubs := by
  rw [prebuildElfPlaced, mapRegionsWithLen_eq, hlens]

abbrev prebuildElfPlaced0 :
    ElfImage → BitVec 64 → BitVec 64 → MallocngCallAddrs → List (String × Nat) →
      Option PrebuiltElfPlaced :=
  prebuildElfPlaced compHooks0

/-- Validity of a serialized `ElfFullSpecPlaced` witness `fs` against `elf`: `prebuildElfPlaced`
produces `prebuiltOfFullPlaced fs` and the ELF header and `brkStart` fields match. -/
def ElfFullValidPlacedFor (W : CliHooks) (elf : ElfImage)
    (tokStorageAddr tokOnceAddr : BitVec 64)
    (addrs : MallocngCallAddrs) (stubs : List (String × Nat))
    (fs : ElfFullSpecPlaced) : Prop :=
  prebuildElfPlaced W elf tokStorageAddr tokOnceAddr addrs stubs =
    some (prebuiltOfFullPlaced fs) ∧
  elf.entry = fs.entry ∧
  elf.phdrVaddr = fs.phdrVaddr ∧
  elf.phent = 56 ∧
  elf.phnum = fs.phnum ∧
  elf.brkStart = fs.brkStart

/-- Assemble `prebuildElfPlaced = some _` from pre-checked component equalities without
re-evaluating `elf.segments`. -/
theorem prebuildElfPlaced_eq_some_of_parts
    {W : CliHooks} {elf : ElfImage} {tokStorageAddr tokOnceAddr : BitVec 64}
    {addrs : MallocngCallAddrs} {stubs : List (String × Nat)}
    {hooks : BinTree String} {baseLines : BinTree Line64}
    (hphent : elf.phent = 56)
    (hpre : checkElfPrebuildOkPlaced elf (mapRegionsWithLen elf.segments)
      tokStorageAddr tokOnceAddr = true)
    (hhooks : overlayHooksPlaced W stubs .empty = hooks)
    (hgrow : binTreeHasString (progPlacedDepth + 1) "grow_one" hooks = false)
    (hd4 : isFullDepth4 baseLines = true)
    (hbl : (patchTokenFastMemPlaced tokStorageAddr tokOnceAddr
      { lines := loadRegionsLines elf.segments, stackBase := 0, stackTop := 0 }).lines = baseLines) :
    prebuildElfPlaced W elf tokStorageAddr tokOnceAddr addrs stubs =
      some { baseLines := baseLines,
             prog := { addrs := addrs, hooks := hooks, rxLines := baseLines } } := by
  unfold prebuildElfPlaced prebuildElfPlacedWithLens
  have hcond1 :
      (elf.phent == 56 &&
        checkElfPrebuildOkPlaced elf (mapRegionsWithLen elf.segments)
          tokStorageAddr tokOnceAddr) = true := by
    simp only [hphent, hpre, beq_self_eq_true, Bool.and_self]
  rw [hcond1]
  simp only [↓reduceIte, withForcedBinTree_eq, hhooks, hgrow, Bool.false_eq_true, hbl,
    isFullDepth3_of_isFullDepth4 hd4, hd4, Bool.and_self]

end Symbolic.BugInjection.Proofs.CliExec.PrebuildPlaced
