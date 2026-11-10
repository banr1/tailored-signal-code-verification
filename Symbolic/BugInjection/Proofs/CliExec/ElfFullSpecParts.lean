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
public import Symbolic.BugInjection.Proofs.Common.CompFitsSatisfiable
public import Symbolic.BugInjection.Proofs.CliExec.RadixMemAux
public import Symbolic.BugInjection.Proofs.CliExec.RadixMem
public import Symbolic.BugInjection.Proofs.CliExec.RadixMemLine
public import Symbolic.BugInjection.Proofs.CliExec.FastStepInit
public import Symbolic.BugInjection.Proofs.CliExec.FastStep
public import Symbolic.BugInjection.Proofs.CliExec.ElfFullSpec

/-!
# Factored `ElfFullValid` Construction and `BinTree` Splits

Assembles `ElfFullValid elf fs` from decoupled scalar, hook-tree, and `baseLines` checks, with
low-bit-first depth-3 (`8`-way) and depth-4 (`16`-way) `BinTree` split and reassembly lemmas.
-/

@[expose] public section

set_option autoImplicit false

namespace Symbolic.BugInjection.Proofs.CliExec.ElfFullSpecParts

open Arm64 Arm64.Obj Arm64.Process ProofLib
open Symbolic.BugInjection.Proofs.Common.CompFitsSatisfiable (compHooks0)
open Symbolic.BugInjection.Proofs.CliExec.RadixMemAux (BinTree Line64
  withForcedBinTree withForcedBinTree_eq)
open Symbolic.BugInjection.Proofs.CliExec.RadixMem (FastMem)
open Symbolic.BugInjection.Proofs.CliExec.RadixMemLine (loadRegionsLines)
open Symbolic.BugInjection.Proofs.CliExec.FastStepInit (buildFastProgWithLens checkElfPrebuildOk
  overlayHooks patchTokenFastMem prebuildElf prebuildElfWithLens)
open Symbolic.BugInjection.Proofs.CliExec.FastStep (treeL treeR isFullDepth3 treeSub3 mkDepth3
  eq_mkDepth3)
open Symbolic.BugInjection.Proofs.CliExec.ElfFullSpec (ElfFullSpec prebuiltOfFull
  ElfFullValidFor ElfFullValid)

export Symbolic.BugInjection.Proofs.CliExec.FastStep (treeL treeR isFullDepth3 treeSub3 mkDepth3
  eq_mkDepth3)

/-- Validate `elf.phent = 56` and `checkElfPrebuildOk elf (mapRegionsWithLen elf.segments)`,
and return `(entry, phdrVaddr, phnum, brkStart)`. -/
def extractElfScalarsAndOk (elf : ElfImage) :
    Option (BitVec 64 × BitVec 64 × Nat × BitVec 64) :=
  let regsWithLen := mapRegionsWithLen elf.segments
  if elf.phent == 56 && checkElfPrebuildOk elf regsWithLen then
    some (elf.entry, elf.phdrVaddr, elf.phnum, elf.brkStart)
  else
    none

def checkElfScalarsAndOk (elf : ElfImage) (fs : ElfFullSpec) : Bool :=
  let regsWithLen := mapRegionsWithLen elf.segments
  elf.phent == 56 &&
    elf.entry == fs.entry &&
    elf.phdrVaddr == fs.phdrVaddr &&
    elf.phnum == fs.phnum &&
    elf.brkStart == fs.brkStart &&
    checkElfPrebuildOk elf regsWithLen

def extractImageHooks (li : LinkedImage) : BinTree String :=
  overlayHooks compHooks0 li.stubs .empty

def extractElfRawLines (elf : ElfImage) : BinTree Line64 :=
  loadRegionsLines elf.segments

def patchTokenLines (lines : BinTree Line64) : BinTree Line64 :=
  (patchTokenFastMem { lines := lines, stackBase := 0, stackTop := 0 }).lines

def extractElfBaseLines (elf : ElfImage) : BinTree Line64 :=
  patchTokenLines (extractElfRawLines elf)

def checkElfBaseLinesDepth3 (elf : ElfImage) : Bool :=
  isFullDepth3 (extractElfBaseLines elf)

def checkElfRawLinesDepth3 (elf : ElfImage) : Bool :=
  isFullDepth3 (extractElfRawLines elf)

def isFullDepth4 {α : Type} : BinTree α → Bool
  | .branch l r => isFullDepth3 l && isFullDepth3 r
  | _ => false

/-- Extract depth-4 subtree `m ∈ 0..15` for low-bit residue `hi % 16 = m`. -/
def treeSub4 {α : Type} (m : Nat) (t : BinTree α) : BinTree α :=
  match m with
  | 0  => treeSub3 0 (treeL t)
  | 1  => treeSub3 0 (treeR t)
  | 2  => treeSub3 1 (treeL t)
  | 3  => treeSub3 1 (treeR t)
  | 4  => treeSub3 2 (treeL t)
  | 5  => treeSub3 2 (treeR t)
  | 6  => treeSub3 3 (treeL t)
  | 7  => treeSub3 3 (treeR t)
  | 8  => treeSub3 4 (treeL t)
  | 9  => treeSub3 4 (treeR t)
  | 10 => treeSub3 5 (treeL t)
  | 11 => treeSub3 5 (treeR t)
  | 12 => treeSub3 6 (treeL t)
  | 13 => treeSub3 6 (treeR t)
  | 14 => treeSub3 7 (treeL t)
  | _  => treeSub3 7 (treeR t)

/-- Reassemble a depth-4 `BinTree` from its 16 low-bit residue subtrees `b0..b15` (`hi % 16 = m`). -/
def mkDepth4 {α : Type}
    (b0 b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 b11 b12 b13 b14 b15 : BinTree α) : BinTree α :=
  .branch
    (mkDepth3 b0 b2 b4 b6 b8 b10 b12 b14)
    (mkDepth3 b1 b3 b5 b7 b9 b11 b13 b15)

/-- Reconstruct `t = mkDepth4 b0 .. b15` from `isFullDepth4 t = true` and 16 `treeSub4` equalities. -/
theorem eq_mkDepth4 {α : Type}
    {t b0 b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 b11 b12 b13 b14 b15 : BinTree α}
    (hf : isFullDepth4 t = true)
    (h0 : treeSub4 0 t = b0) (h1 : treeSub4 1 t = b1)
    (h2 : treeSub4 2 t = b2) (h3 : treeSub4 3 t = b3)
    (h4 : treeSub4 4 t = b4) (h5 : treeSub4 5 t = b5)
    (h6 : treeSub4 6 t = b6) (h7 : treeSub4 7 t = b7)
    (h8 : treeSub4 8 t = b8) (h9 : treeSub4 9 t = b9)
    (h10 : treeSub4 10 t = b10) (h11 : treeSub4 11 t = b11)
    (h12 : treeSub4 12 t = b12) (h13 : treeSub4 13 t = b13)
    (h14 : treeSub4 14 t = b14) (h15 : treeSub4 15 t = b15) :
    t = mkDepth4 b0 b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 b11 b12 b13 b14 b15 := by
  cases t with
  | empty => nomatch hf
  | twig _ _ => nomatch hf
  | branch l r =>
    simp only [isFullDepth4, Bool.and_eq_true] at hf
    dsimp only [treeSub4, treeL, treeR] at h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 h14 h15
    rw [eq_mkDepth3 hf.1 h0 h2 h4 h6 h8 h10 h12 h14,
        eq_mkDepth3 hf.2 h1 h3 h5 h7 h9 h11 h13 h15]
    rfl

def checkElfBaseLinesDepth4 (elf : ElfImage) : Bool :=
  isFullDepth4 (extractElfBaseLines elf)

def checkElfRawLinesDepth4 (elf : ElfImage) : Bool :=
  isFullDepth4 (extractElfRawLines elf)

theorem extractElfScalarsAndOk_of_check {elf : ElfImage} {fs : ElfFullSpec}
    (hok : checkElfScalarsAndOk elf fs = true) :
    extractElfScalarsAndOk elf = some (fs.entry, fs.phdrVaddr, fs.phnum, fs.brkStart) := by
  unfold checkElfScalarsAndOk at hok
  dsimp only at hok
  simp only [Bool.and_eq_true, beq_iff_eq] at hok
  rcases hok with ⟨⟨⟨⟨⟨hphent, hentry⟩, hphdr⟩, hphnum⟩, hbrk⟩, hpbok⟩
  unfold extractElfScalarsAndOk
  dsimp only
  have hcond : (elf.phent == 56 && checkElfPrebuildOk elf (mapRegionsWithLen elf.segments)) = true := by
    simp only [Bool.and_eq_true, beq_iff_eq]
    exact ⟨hphent, hpbok⟩
  rw [hcond]
  simp only [↓reduceIte, hentry, hphdr, hphnum, hbrk]

/-- Assemble `ElfFullValidFor li elf fs` from `extractElfScalarsAndOk`, `extractImageHooks`, and
`extractElfBaseLines`. -/
theorem elfFullValidFor_of_parts
    {li : LinkedImage} {elf : ElfImage} {fs : ElfFullSpec}
    (hsc : extractElfScalarsAndOk elf = some (fs.entry, fs.phdrVaddr, fs.phnum, fs.brkStart))
    (hhk : extractImageHooks li = fs.hooks)
    (hbl : extractElfBaseLines elf = fs.baseLines) :
    ElfFullValidFor li elf fs := by
  unfold extractElfScalarsAndOk at hsc
  dsimp only at hsc
  split at hsc; swap; · nomatch hsc
  rename_i hcond
  injection hsc with htup
  have hentry : elf.entry = fs.entry := congrArg Prod.fst htup
  have hphdr : elf.phdrVaddr = fs.phdrVaddr := congrArg (Prod.fst ∘ Prod.snd) htup
  have hphnum : elf.phnum = fs.phnum := congrArg (Prod.fst ∘ Prod.snd ∘ Prod.snd) htup
  have hbrk : elf.brkStart = fs.brkStart := congrArg (Prod.snd ∘ Prod.snd ∘ Prod.snd) htup
  simp only [Bool.and_eq_true, beq_iff_eq] at hcond
  rcases hcond with ⟨hphent, hok⟩
  refine ⟨?_, hentry, hphdr, hphent, hphnum, hbrk⟩
  unfold prebuildElf prebuildElfWithLens buildFastProgWithLens prebuiltOfFull
  unfold extractImageHooks at hhk
  unfold extractElfBaseLines patchTokenLines extractElfRawLines at hbl
  simp only [hok, ↓reduceIte, withForcedBinTree_eq, hhk, hbl]

theorem elfFullValid_of_parts
    {elf : ElfImage} {fs : ElfFullSpec}
    (hsc : extractElfScalarsAndOk elf = some (fs.entry, fs.phdrVaddr, fs.phnum, fs.brkStart))
    (hhk : extractImageHooks CryptoVerification.libsignalSessionImage = fs.hooks)
    (hbl : extractElfBaseLines elf = fs.baseLines) :
    ElfFullValid elf fs :=
  elfFullValidFor_of_parts hsc hhk hbl

/-- Assemble `ElfFullValidFor li elf fs` from `extractElfScalarsAndOk`, `extractImageHooks`,
`checkElfBaseLinesDepth3 elf = true`, and 8 `treeSub3` subtree equalities. -/
theorem elfFullValidFor_of_depth3
    {li : LinkedImage} {elf : ElfImage} {fs : ElfFullSpec}
    {b0 b1 b2 b3 b4 b5 b6 b7 : BinTree Line64}
    (hsc : extractElfScalarsAndOk elf = some (fs.entry, fs.phdrVaddr, fs.phnum, fs.brkStart))
    (hhk : extractImageHooks li = fs.hooks)
    (hd3 : checkElfBaseLinesDepth3 elf = true)
    (h0 : treeSub3 0 (extractElfBaseLines elf) = b0)
    (h1 : treeSub3 1 (extractElfBaseLines elf) = b1)
    (h2 : treeSub3 2 (extractElfBaseLines elf) = b2)
    (h3 : treeSub3 3 (extractElfBaseLines elf) = b3)
    (h4 : treeSub3 4 (extractElfBaseLines elf) = b4)
    (h5 : treeSub3 5 (extractElfBaseLines elf) = b5)
    (h6 : treeSub3 6 (extractElfBaseLines elf) = b6)
    (h7 : treeSub3 7 (extractElfBaseLines elf) = b7)
    (hbl : mkDepth3 b0 b1 b2 b3 b4 b5 b6 b7 = fs.baseLines) :
    ElfFullValidFor li elf fs :=
  elfFullValidFor_of_parts hsc hhk ((eq_mkDepth3 hd3 h0 h1 h2 h3 h4 h5 h6 h7).trans hbl)

theorem elfFullValid_of_depth3
    {elf : ElfImage} {fs : ElfFullSpec}
    {b0 b1 b2 b3 b4 b5 b6 b7 : BinTree Line64}
    (hsc : extractElfScalarsAndOk elf = some (fs.entry, fs.phdrVaddr, fs.phnum, fs.brkStart))
    (hhk : extractImageHooks CryptoVerification.libsignalSessionImage = fs.hooks)
    (hd3 : checkElfBaseLinesDepth3 elf = true)
    (h0 : treeSub3 0 (extractElfBaseLines elf) = b0)
    (h1 : treeSub3 1 (extractElfBaseLines elf) = b1)
    (h2 : treeSub3 2 (extractElfBaseLines elf) = b2)
    (h3 : treeSub3 3 (extractElfBaseLines elf) = b3)
    (h4 : treeSub3 4 (extractElfBaseLines elf) = b4)
    (h5 : treeSub3 5 (extractElfBaseLines elf) = b5)
    (h6 : treeSub3 6 (extractElfBaseLines elf) = b6)
    (h7 : treeSub3 7 (extractElfBaseLines elf) = b7)
    (hbl : mkDepth3 b0 b1 b2 b3 b4 b5 b6 b7 = fs.baseLines) :
    ElfFullValid elf fs :=
  elfFullValidFor_of_depth3 hsc hhk hd3 h0 h1 h2 h3 h4 h5 h6 h7 hbl

/-- Assemble `ElfFullValidFor li elf fs` from `extractElfScalarsAndOk`, `extractImageHooks`,
`checkElfBaseLinesDepth4 elf = true`, and 16 `treeSub4` subtree equalities. -/
theorem elfFullValidFor_of_depth4
    {li : LinkedImage} {elf : ElfImage} {fs : ElfFullSpec}
    {b0 b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 b11 b12 b13 b14 b15 : BinTree Line64}
    (hsc : extractElfScalarsAndOk elf = some (fs.entry, fs.phdrVaddr, fs.phnum, fs.brkStart))
    (hhk : extractImageHooks li = fs.hooks)
    (hd4 : checkElfBaseLinesDepth4 elf = true)
    (h0 : treeSub4 0 (extractElfBaseLines elf) = b0)
    (h1 : treeSub4 1 (extractElfBaseLines elf) = b1)
    (h2 : treeSub4 2 (extractElfBaseLines elf) = b2)
    (h3 : treeSub4 3 (extractElfBaseLines elf) = b3)
    (h4 : treeSub4 4 (extractElfBaseLines elf) = b4)
    (h5 : treeSub4 5 (extractElfBaseLines elf) = b5)
    (h6 : treeSub4 6 (extractElfBaseLines elf) = b6)
    (h7 : treeSub4 7 (extractElfBaseLines elf) = b7)
    (h8 : treeSub4 8 (extractElfBaseLines elf) = b8)
    (h9 : treeSub4 9 (extractElfBaseLines elf) = b9)
    (h10 : treeSub4 10 (extractElfBaseLines elf) = b10)
    (h11 : treeSub4 11 (extractElfBaseLines elf) = b11)
    (h12 : treeSub4 12 (extractElfBaseLines elf) = b12)
    (h13 : treeSub4 13 (extractElfBaseLines elf) = b13)
    (h14 : treeSub4 14 (extractElfBaseLines elf) = b14)
    (h15 : treeSub4 15 (extractElfBaseLines elf) = b15)
    (hbl : mkDepth4 b0 b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 b11 b12 b13 b14 b15 = fs.baseLines) :
    ElfFullValidFor li elf fs :=
  elfFullValidFor_of_parts hsc hhk
    ((eq_mkDepth4 hd4 h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 h14 h15).trans hbl)

theorem elfFullValid_of_depth4
    {elf : ElfImage} {fs : ElfFullSpec}
    {b0 b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 b11 b12 b13 b14 b15 : BinTree Line64}
    (hsc : extractElfScalarsAndOk elf = some (fs.entry, fs.phdrVaddr, fs.phnum, fs.brkStart))
    (hhk : extractImageHooks CryptoVerification.libsignalSessionImage = fs.hooks)
    (hd4 : checkElfBaseLinesDepth4 elf = true)
    (h0 : treeSub4 0 (extractElfBaseLines elf) = b0)
    (h1 : treeSub4 1 (extractElfBaseLines elf) = b1)
    (h2 : treeSub4 2 (extractElfBaseLines elf) = b2)
    (h3 : treeSub4 3 (extractElfBaseLines elf) = b3)
    (h4 : treeSub4 4 (extractElfBaseLines elf) = b4)
    (h5 : treeSub4 5 (extractElfBaseLines elf) = b5)
    (h6 : treeSub4 6 (extractElfBaseLines elf) = b6)
    (h7 : treeSub4 7 (extractElfBaseLines elf) = b7)
    (h8 : treeSub4 8 (extractElfBaseLines elf) = b8)
    (h9 : treeSub4 9 (extractElfBaseLines elf) = b9)
    (h10 : treeSub4 10 (extractElfBaseLines elf) = b10)
    (h11 : treeSub4 11 (extractElfBaseLines elf) = b11)
    (h12 : treeSub4 12 (extractElfBaseLines elf) = b12)
    (h13 : treeSub4 13 (extractElfBaseLines elf) = b13)
    (h14 : treeSub4 14 (extractElfBaseLines elf) = b14)
    (h15 : treeSub4 15 (extractElfBaseLines elf) = b15)
    (hbl : mkDepth4 b0 b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 b11 b12 b13 b14 b15 = fs.baseLines) :
    ElfFullValid elf fs :=
  elfFullValidFor_of_depth4 hsc hhk hd4 h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 h14 h15 hbl

abbrev parsedFullValidFor_of_parts := @elfFullValidFor_of_parts
abbrev parsedFullValid_of_parts := @elfFullValid_of_parts
abbrev parsedFullValidFor_of_depth3 := @elfFullValidFor_of_depth3
abbrev parsedFullValid_of_depth3 := @elfFullValid_of_depth3
abbrev parsedFullValidFor_of_depth4 := @elfFullValidFor_of_depth4
abbrev parsedFullValid_of_depth4 := @elfFullValid_of_depth4

end Symbolic.BugInjection.Proofs.CliExec.ElfFullSpecParts
