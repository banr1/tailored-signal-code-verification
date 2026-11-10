/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Arm64
public import ProofLib.Invariant
public import ProofLib.Placed
public import ProofLib.Process.FastParse
public import ProofLib.ProgramReflection
public import VerifiedLibraries.Mallocng.Spec
public import LibsignalBinary.Specifications.SignalSession.CliProcess
public import LibsignalBinary.Specifications.SignalSession.CliBinaryPq
public import Symbolic.BugInjection.Proofs.CliExec.CompHooks0Placed
public import Symbolic.BugInjection.Proofs.CliExec.RadixMemAux
public import Symbolic.BugInjection.Proofs.CliExec.RadixMem
public import Symbolic.BugInjection.Proofs.CliExec.RadixMemLine
public import Symbolic.BugInjection.Proofs.CliExec.RadixMemPlaced
public import Symbolic.BugInjection.Proofs.CliExec.FastHooksAux
public import Symbolic.BugInjection.Proofs.CliExec.FastHooksPlaced
public import Symbolic.BugInjection.Proofs.CliExec.PlacedExecCore
public import Symbolic.BugInjection.Proofs.CliExec.ElfFullSpecPlacedCore
public import Symbolic.BugInjection.Proofs.CliExec.PrebuildPlaced
public meta import Lean
public meta import Arm64
public meta import GeneratedLean.LibsignalSessionPlacedObj

/-!
# Placed ELF Validation and Extractors

Ties an image-free `fs : ElfFullSpecPlaced` to `(mpl, mmpl, elf)` via `PrebuildPlaced.prebuildElfPlaced`.
Reflects the closed extern symbol table `block617Externs` of `libsignalSessionLib` block `617` at
elaboration time, defines placement scalar projections and alignment guards, and provides
depth-4 split constructors for `ElfFullValidPlaced`.
-/

@[expose] public section

set_option autoImplicit false

namespace Symbolic.BugInjection.Proofs.CliExec.ElfFullSpecPlaced

open Arm64 Arm64.Obj Arm64.Process ProofLib ProofLib.ProgramReflection
open CryptoVerification.SignalSession (CliHooks libsignalSessionLib)
open Symbolic.BugInjection.Proofs.CliExec.CompHooks0Placed (compHooks0)
open Symbolic.BugInjection.Proofs.CliExec.RadixMemAux (BinTree Line64)
open Symbolic.BugInjection.Proofs.CliExec.RadixMem (FastMem)
open Symbolic.BugInjection.Proofs.CliExec.RadixMemLine (loadRegionsLines)
open Symbolic.BugInjection.Proofs.CliExec.RadixMemPlaced (patchTokenFastMemPlaced)
open Symbolic.BugInjection.Proofs.CliExec.FastHooksAux (panicPrefixBs strUtf8Bytes)
open Symbolic.BugInjection.Proofs.CliExec.FastHooksPlaced (MallocngCallAddrs)
open Symbolic.BugInjection.Proofs.CliExec.PlacedExecCore (checkElfPrebuildOkPlaced
  hasHookPlacedBs hookPlacedExactNamesBs overlayHooksPlaced
  progPlacedDepth progPlacedWordBound withForcedNameTablePlaced withForcedUInt8ListPlaced)
open Symbolic.BugInjection.Proofs.CliExec.PrebuildPlaced (ElfFullValidPlacedFor
  binTreeHasString isFullDepth3_of_isFullDepth4 prebuildElfPlaced prebuildElfPlaced0
  prebuildElfPlacedWithLens prebuildElfPlaced_eq_some_of_parts)

set_option linter.dupNamespace false in
export Symbolic.BugInjection.Proofs.CliExec.ElfFullSpecPlacedCore (
  ElfFullSpecPlaced headerElfOfFullPlaced addrsOfFullPlaced prebuiltOfFullPlaced
  MkCkpt ckptInit initFastStateFromBasePlaced_congr
  treeL treeR isFullDepth3 treeSub3 mkDepth3 eq_mkDepth3
  isFullDepth4 treeSub4 mkDepth4 eq_mkDepth4
  runElfChunkPlacedLHS runElfChunkPlacedRHS
  checkElfFinalChunkPlacedExited0 checkElfFinalChunkPlacedExited checkElfFinalChunkPlacedAborted
  ElfCkptReachablePlaced
)
export Symbolic.BugInjection.Proofs.CliExec.PrebuildPlaced (
  ElfFullValidPlacedFor prebuildElfPlaced prebuildElfPlaced0 prebuildElfPlacedWithLens
)

section GenBlock617Externs

open Lean Elab Command Meta

private meta def whnfBlock617Ctor (ctor : Name) (arity : Nat) (e : Expr) : MetaM Expr := do
  let e' ← whnf e
  if e'.isAppOfArity ctor arity then return e'
  let eAll ← withTransparency .all (whnf e)
  if eAll.isAppOfArity ctor arity then return eAll
  throwError "gen_block617_externs: expected {ctor}/{arity}, got {eAll}"

private meta partial def block617ListElems (e : Expr) : MetaM (Array Expr) := do
  let mut cur := e
  let mut out : Array Expr := #[]
  while true do
    let c ← whnf cur
    if c.isAppOfArity ``List.nil 1 then return out
    if c.isAppOfArity ``List.cons 3 then
      out := out.push (c.getArg! 1)
      cur := c.getArg! 2
    else
      let cAll ← withTransparency .all (whnf cur)
      if cAll.isAppOfArity ``List.nil 1 then return out
      if cAll.isAppOfArity ``List.cons 3 then
        out := out.push (cAll.getArg! 1)
        cur := cAll.getArg! 2
      else
        throwError "gen_block617_externs: expected List, got {cAll}"
  return out

private meta def block617StrVal (e : Expr) : MetaM String := do
  if let .lit (.strVal s) := e then return s
  let e' ← withTransparency .all (whnf e)
  if let .lit (.strVal s) := e' then return s
  throwError "gen_block617_externs: expected string literal, got {e'}"

local elab "gen_block617_externs" : command => do
  let lits : Array (TSyntax `term) ← liftTermElabM do
    let libC ← whnfBlock617Ctor ``Obj.MultiPlacedLib.mk 5
      (Lean.mkConst ``CryptoVerification.libsignalSessionMultiLib)
    let blkEs ← block617ListElems (libC.getArg! 1)
    let some b617Raw := blkEs[617]?
      | throwError "gen_block617_externs: block 617 out of bounds ({blkEs.size})"
    let b617C ← whnfBlock617Ctor ``Obj.CodeBlock.mk 6 b617Raw
    let extEs ← block617ListElems (b617C.getArg! 4)
    let extStrs ← (extEs.mapM block617StrVal : MetaM (Array String))
    return extStrs.map fun s => (Syntax.mkStrLit s : TSyntax `term)
  let defId := mkIdent `block617Externs
  elabCommand (← `(command|
    /-- Closed extern symbol list of `libsignalSessionLib` block `617` (`main`), reflected at
    elaboration time and certified by `block617Externs_eq` and `block617Externs_all_nonBlock`. -/
    def $defId:ident : List String := [$lits,*]))

gen_block617_externs

end GenBlock617Externs

set_option maxRecDepth 2000000 in
set_option maxHeartbeats 1600000 in
theorem block617Externs_eq :
    (libsignalSessionLib.blocks.getD 617 { code := [] }).externs = block617Externs := by
  rfl_kernel

set_option maxRecDepth 2000000 in
set_option maxHeartbeats 1600000 in
theorem block617Externs_all_nonBlock :
    (block617Externs.all fun e => lookupBlockSym e libsignalSessionLib.blocks == none) = true := by
  rfl_kernel

theorem lookupBlockSym_eq_none_of_mem_block617Externs {e : String}
    (he : e ∈ block617Externs) :
    lookupBlockSym e libsignalSessionLib.blocks = none := by
  have hall := List.all_eq_true.mp block617Externs_all_nonBlock e he
  exact beq_iff_eq.mp hall

theorem resolve_block617Extern {e : String} (he : e ∈ block617Externs) (mpl : MultiPlacement) :
    libsignalSessionLib.resolve mpl e = mpl.ρ e := by
  unfold MultiPlacedLib.resolve
  rw [lookupBlockSym_eq_none_of_mem_block617Externs he]

/-- Extern `(name, va)` table of `libsignalSessionLib` block `617` under `mpl`. -/
def stubsOfMpl (mpl : MultiPlacement) : List (String × Nat) :=
  block617Externs.map fun e => (e, (mpl.ρ e).toNat)

/-- Placed address of SPQR `use_accelerated::STORAGE.0`. -/
def tokStorageAddrPlaced (mpl : MultiPlacement) : BitVec 64 :=
  mpl.ρ CryptoVerification.LibsignalSpqrV1.tokenStorageName

/-- Placed base address of SPQR `check_accelerated::TOKEN` (`+ 8#64` selects the `Once` word). -/
def tokOnceAddrPlaced (mpl : MultiPlacement) : BitVec 64 :=
  mpl.ρ CryptoVerification.LibsignalSpqrV1.tokenName

/-- `MallocngCallAddrs` projection of `mmpl` (`calloc` = block `2`, `free` = block `3`,
`malloc` = block `4` of `VerifiedLibraries.mallocngLib`). -/
def mallocngCallAddrsPlaced (mmpl : MultiPlacement) : MallocngCallAddrs where
  callocAddr     := mmpl.base 2
  callocSentinel := mmpl.base 2 + 1#64
  mallocAddr     := mmpl.base 4
  mallocSentinel := mmpl.base 4 + 1#64
  freeAddr       := mmpl.base 3
  freeSentinel   := mmpl.base 3 + 1#64

theorem mallocngCallAddrsPlaced_fnAddr (mmpl : MultiPlacement) :
    (mallocngCallAddrsPlaced mmpl).callocAddr =
      VerifiedLibraries.mallocngLib.fnAddr mmpl "calloc" ∧
    (mallocngCallAddrsPlaced mmpl).mallocAddr =
      VerifiedLibraries.mallocngLib.fnAddr mmpl "malloc" ∧
    (mallocngCallAddrsPlaced mmpl).freeAddr =
      VerifiedLibraries.mallocngLib.fnAddr mmpl "free" := by
  have hc : lookupBlockSym "calloc" VerifiedLibraries.mallocngLib.blocks = some (2, 0) := rfl
  have hm : lookupBlockSym "malloc" VerifiedLibraries.mallocngLib.blocks = some (4, 0) := rfl
  have hf : lookupBlockSym "free" VerifiedLibraries.mallocngLib.blocks = some (3, 0) := rfl
  unfold mallocngCallAddrsPlaced MultiPlacedLib.fnAddr
  rw [hc, hm, hf]
  exact ⟨(BitVec.add_zero _).symm, (BitVec.add_zero _).symm, (BitVec.add_zero _).symm⟩

/-- Check that all 5 `VerifiedLibraries.mallocngLib` block bases in `mmpl` are 4-byte-aligned
and do not wrap `2 ^ 64`. -/
def checkMallocngBlocksAligned (mmpl : MultiPlacement) : Bool :=
  (List.range VerifiedLibraries.mallocngLib.blocks.length).all fun i =>
    let blk := VerifiedLibraries.mallocngLib.blocks.getD i { code := [] }
    Nat.beq (Nat.mod (mmpl.base i).toNat 4) 0 &&
      decide ((mmpl.base i).toNat + blk.code.length ≤ 2 ^ 64)

/-- Check that every hooked extern in `block617Externs` is 4-byte-aligned under `mpl`
and within `progPlacedWordBound = 2 ^ 62`. -/
def checkHooksAlignedPlacedW (W : CliHooks) (mpl : MultiPlacement) : Bool :=
  withForcedUInt8ListPlaced panicPrefixBs fun pfx =>
  withForcedNameTablePlaced (hookPlacedExactNamesBs W) fun tbl =>
    block617Externs.all fun e =>
      !(hasHookPlacedBs pfx tbl (strUtf8Bytes e)) ||
        (Nat.beq (Nat.mod (mpl.ρ e).toNat 4) 0 &&
          Nat.blt (Nat.div (mpl.ρ e).toNat 4) progPlacedWordBound)

abbrev checkHooksAlignedPlaced (mpl : MultiPlacement) : Bool :=
  checkHooksAlignedPlacedW compHooks0 mpl

def extractElfRawLinesPlaced (elf : ElfImage) : BinTree Line64 :=
  loadRegionsLines elf.segments

def extractImageHooksPlaced (mpl : MultiPlacement) : BinTree String :=
  overlayHooksPlaced compHooks0 (stubsOfMpl mpl) .empty

/-- Extract and validate the 12 header and placement scalars of `elf` under `(mpl, mmpl)` when
prebuild, hook-alignment, and `mallocng` alignment guards hold. -/
def extractElfScalarsAndOkPlaced (mpl mmpl : MultiPlacement) (elf : ElfImage) :
    Option (BitVec 64 × BitVec 64 × Nat × BitVec 64 × BitVec 64 × BitVec 64 ×
            BitVec 64 × BitVec 64 × BitVec 64 × BitVec 64 × BitVec 64 × BitVec 64) :=
  let tokS := tokStorageAddrPlaced mpl
  let tokO := tokOnceAddrPlaced mpl
  let addrs := mallocngCallAddrsPlaced mmpl
  if elf.phent == 56 &&
      checkElfPrebuildOkPlaced elf (mapRegionsWithLen elf.segments) tokS tokO &&
      !(binTreeHasString (progPlacedDepth + 1) "grow_one" (extractImageHooksPlaced mpl)) &&
      checkHooksAlignedPlaced mpl &&
      checkMallocngBlocksAligned mmpl then
    some (elf.entry, elf.phdrVaddr, elf.phnum, elf.brkStart,
          tokS, tokO, addrs.callocAddr, addrs.callocSentinel,
          addrs.mallocAddr, addrs.mallocSentinel, addrs.freeAddr, addrs.freeSentinel)
  else
    none

def extractElfBaseLinesPlaced (mpl : MultiPlacement) (elf : ElfImage) : BinTree Line64 :=
  (patchTokenFastMemPlaced (tokStorageAddrPlaced mpl) (tokOnceAddrPlaced mpl)
    { lines := extractElfRawLinesPlaced elf, stackBase := 0, stackTop := 0 }).lines

/-- Check that `extractElfRawLinesPlaced elf` maps the 5 token-patch bytes as writable and that
`extractElfBaseLinesPlaced mpl elf` has a full depth-4 `BinTree` spine. -/
def checkElfBaseLinesPlacedDepth4 (mpl : MultiPlacement) (elf : ElfImage) : Bool :=
  (({ lines := extractElfRawLinesPlaced elf, stackBase := 0, stackTop := 0 } : FastMem).canWrite
      (tokStorageAddrPlaced mpl) 1 &&
    ({ lines := extractElfRawLinesPlaced elf, stackBase := 0, stackTop := 0 } : FastMem).canWrite
      (tokOnceAddrPlaced mpl + 8#64) 4) &&
    isFullDepth4 (extractElfBaseLinesPlaced mpl elf)

/-- Validity invariant tying an image-free `fs : ElfFullSpecPlaced` to `(mpl, mmpl, elf)` via
`prebuildElfPlaced`. -/
structure ElfFullValidPlaced (mpl mmpl : MultiPlacement) (elf : ElfImage)
    (fs : ElfFullSpecPlaced) : Prop where
  prebuild_eq           : prebuildElfPlaced compHooks0 elf
                            (tokStorageAddrPlaced mpl) (tokOnceAddrPlaced mpl)
                            (mallocngCallAddrsPlaced mmpl) (stubsOfMpl mpl) =
                            some (prebuiltOfFullPlaced fs)
  entry_eq              : elf.entry = fs.entry
  phdrVaddr_eq          : elf.phdrVaddr = fs.phdrVaddr
  phent_eq              : elf.phent = 56
  phnum_eq              : elf.phnum = fs.phnum
  brkStart_eq           : elf.brkStart = fs.brkStart
  tokStorage_eq         : fs.tokStorageAddr = tokStorageAddrPlaced mpl
  tokOnce_eq            : fs.tokOnceAddr = tokOnceAddrPlaced mpl
  addrs_eq              : addrsOfFullPlaced fs = mallocngCallAddrsPlaced mmpl
  hooksAligned          : checkHooksAlignedPlaced mpl = true
  tokCanWrite           :
    (({ lines := extractElfRawLinesPlaced elf, stackBase := 0, stackTop := 0 } : FastMem).canWrite
        (tokStorageAddrPlaced mpl) 1 &&
      ({ lines := extractElfRawLinesPlaced elf, stackBase := 0, stackTop := 0 } : FastMem).canWrite
        (tokOnceAddrPlaced mpl + 8#64) 4) = true
  mallocng_inElf        : VerifiedLibraries.mallocngLib.InElf elf mmpl
  mallocngBlocksAligned : checkMallocngBlocksAligned mmpl = true

theorem ElfFullValidPlaced.toValidFor
    {mpl mmpl : MultiPlacement} {elf : ElfImage} {fs : ElfFullSpecPlaced}
    (hv : ElfFullValidPlaced mpl mmpl elf fs) :
    ElfFullValidPlacedFor compHooks0 elf
      (tokStorageAddrPlaced mpl) (tokOnceAddrPlaced mpl)
      (mallocngCallAddrsPlaced mmpl) (stubsOfMpl mpl) fs :=
  ⟨hv.prebuild_eq, hv.entry_eq, hv.phdrVaddr_eq, hv.phent_eq, hv.phnum_eq, hv.brkStart_eq⟩

/-- `ElfFullValidPlaced` implies `VerifiedLibraries.mallocngLib.CodeLoaded mmpl s.mem` on any
initial `elf.loadState` state `s`. -/
theorem ElfFullValidPlaced.mallocng_codeLoaded
    {mpl mmpl : MultiPlacement} {elf : ElfImage} {fs : ElfFullSpecPlaced}
    (hv : ElfFullValidPlaced mpl mmpl elf fs)
    {inputs : ProcessInputs} {s : State}
    (hload : elf.loadState inputs = .ok s) :
    VerifiedLibraries.mallocngLib.CodeLoaded mmpl s.mem := by
  intro i hi
  have hall := List.all_eq_true.mp hv.mallocngBlocksAligned i (List.mem_range.mpr hi)
  simp only [Bool.and_eq_true, Nat.beq_eq, decide_eq_true_eq] at hall
  have hblk_eq :
      VerifiedLibraries.mallocngLib.blocks.getD i { code := [] } =
        VerifiedLibraries.mallocngLib.blocks[i] :=
    VerifiedLibraries.mallocngLib.blockLib_text hi
  rw [hblk_eq] at hall
  have hmap : ElfMaps elf (mmpl.base i)
      ((VerifiedLibraries.mallocngLib.blockLib i).text.patched
        (VerifiedLibraries.mallocngLib.blockPlacement mmpl i)) (· == Perm.rx) := by
    simpa [VerifiedLibraries.mallocngLib.blockLib_text hi] using hv.mallocng_inElf.blocks i hi
  have hhb := ElfMaps.holdsBytes hload (p := Perm.rx) (fun q hq => by simpa using hq) hmap
  refine Program.CodeLoaded.intro hall.1 ?_ fun j hj => hhb j hj
  dsimp only [MultiPlacedLib.blockProgram, PlacedLib.program, MultiPlacedLib.blockPlacement]
  rw [CodeBlock.length_patched, VerifiedLibraries.mallocngLib.blockLib_text hi]
  have hdiv :
      4 * (VerifiedLibraries.mallocngLib.blocks[i].code.length / 4) ≤
        VerifiedLibraries.mallocngLib.blocks[i].code.length :=
    Nat.mul_div_le _ 4
  omega

/-- Assemble `ElfFullValidPlaced mpl mmpl elf fs` from `mallocngLib.InElf`, `extractElfScalarsAndOkPlaced`,
`extractImageHooksPlaced`, `tokCanWrite`, `isFullDepth4 fs.baseLines = true`, and
`extractElfBaseLinesPlaced mpl elf = fs.baseLines`. -/
theorem elfFullValidPlaced_of_parts
    {mpl mmpl : MultiPlacement} {elf : ElfImage} {fs : ElfFullSpecPlaced}
    (hin : VerifiedLibraries.mallocngLib.InElf elf mmpl)
    (hsc : extractElfScalarsAndOkPlaced mpl mmpl elf = some (
      fs.entry, fs.phdrVaddr, fs.phnum, fs.brkStart,
      fs.tokStorageAddr, fs.tokOnceAddr, fs.callocAddr, fs.callocSentinel,
      fs.mallocAddr, fs.mallocSentinel, fs.freeAddr, fs.freeSentinel))
    (hhk : extractImageHooksPlaced mpl = fs.hooks)
    (htw :
      (({ lines := extractElfRawLinesPlaced elf, stackBase := 0, stackTop := 0 } : FastMem).canWrite
          (tokStorageAddrPlaced mpl) 1 &&
        ({ lines := extractElfRawLinesPlaced elf, stackBase := 0, stackTop := 0 } : FastMem).canWrite
          (tokOnceAddrPlaced mpl + 8#64) 4) = true)
    (hd4_fs : isFullDepth4 fs.baseLines = true)
    (hbl : extractElfBaseLinesPlaced mpl elf = fs.baseLines) :
    ElfFullValidPlaced mpl mmpl elf fs := by
  rw [extractElfScalarsAndOkPlaced] at hsc
  split at hsc
  · rename_i hcond
    simp only [Bool.and_eq_true, Bool.not_eq_true', beq_iff_eq] at hcond
    rcases hcond with ⟨⟨⟨⟨hphent, hpre⟩, hnogrow⟩, halk⟩, hmba⟩
    injection hsc with hsc
    rcases Prod.mk.inj hsc with ⟨hentry, hsc⟩
    rcases Prod.mk.inj hsc with ⟨hphdr, hsc⟩
    rcases Prod.mk.inj hsc with ⟨hphnum, hsc⟩
    rcases Prod.mk.inj hsc with ⟨hbrk, hsc⟩
    rcases Prod.mk.inj hsc with ⟨htokS, hsc⟩
    rcases Prod.mk.inj hsc with ⟨htokO, hsc⟩
    rcases Prod.mk.inj hsc with ⟨hca, hsc⟩
    rcases Prod.mk.inj hsc with ⟨hcs, hsc⟩
    rcases Prod.mk.inj hsc with ⟨hma, hsc⟩
    rcases Prod.mk.inj hsc with ⟨hms, hsc⟩
    rcases Prod.mk.inj hsc with ⟨hfa, hfs⟩
    have haddrs : addrsOfFullPlaced fs = mallocngCallAddrsPlaced mmpl := by
      unfold addrsOfFullPlaced
      rw [← hca, ← hcs, ← hma, ← hms, ← hfa, ← hfs]
    have hnogrow' : binTreeHasString (progPlacedDepth + 1) "grow_one" fs.hooks = false :=
      hhk ▸ hnogrow
    have hpb_eq :
        prebuildElfPlaced compHooks0 elf
          (tokStorageAddrPlaced mpl) (tokOnceAddrPlaced mpl)
          (mallocngCallAddrsPlaced mmpl) (stubsOfMpl mpl) =
          some (prebuiltOfFullPlaced fs) := by
      have h1 := prebuildElfPlaced_eq_some_of_parts
        (addrs := mallocngCallAddrsPlaced mmpl)
        hphent hpre hhk hnogrow' hd4_fs hbl
      unfold prebuiltOfFullPlaced
      rw [haddrs]
      exact h1
    exact {
      prebuild_eq           := hpb_eq
      entry_eq              := hentry
      phdrVaddr_eq          := hphdr
      phent_eq              := hphent
      phnum_eq              := hphnum
      brkStart_eq           := hbrk
      tokStorage_eq         := htokS.symm
      tokOnce_eq            := htokO.symm
      addrs_eq              := haddrs
      hooksAligned          := halk
      tokCanWrite           := htw
      mallocng_inElf        := hin
      mallocngBlocksAligned := hmba
    }
  · nomatch hsc

/-- Assemble `ElfFullValidPlaced mpl mmpl elf fs` from `mallocngLib.InElf`,
`extractElfScalarsAndOkPlaced`, `extractImageHooksPlaced`, `checkElfBaseLinesPlacedDepth4`,
and 16 `treeSub4` subtree equalities. -/
theorem elfFullValidPlaced_of_depth4
    {mpl mmpl : MultiPlacement} {elf : ElfImage} {fs : ElfFullSpecPlaced}
    {b0 b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 b11 b12 b13 b14 b15 : BinTree Line64}
    (hin : VerifiedLibraries.mallocngLib.InElf elf mmpl)
    (hsc : extractElfScalarsAndOkPlaced mpl mmpl elf = some (
      fs.entry, fs.phdrVaddr, fs.phnum, fs.brkStart,
      fs.tokStorageAddr, fs.tokOnceAddr, fs.callocAddr, fs.callocSentinel,
      fs.mallocAddr, fs.mallocSentinel, fs.freeAddr, fs.freeSentinel))
    (hhk : extractImageHooksPlaced mpl = fs.hooks)
    (hd4 : checkElfBaseLinesPlacedDepth4 mpl elf = true)
    (h0 : treeSub4 0 (extractElfBaseLinesPlaced mpl elf) = b0)
    (h1 : treeSub4 1 (extractElfBaseLinesPlaced mpl elf) = b1)
    (h2 : treeSub4 2 (extractElfBaseLinesPlaced mpl elf) = b2)
    (h3 : treeSub4 3 (extractElfBaseLinesPlaced mpl elf) = b3)
    (h4 : treeSub4 4 (extractElfBaseLinesPlaced mpl elf) = b4)
    (h5 : treeSub4 5 (extractElfBaseLinesPlaced mpl elf) = b5)
    (h6 : treeSub4 6 (extractElfBaseLinesPlaced mpl elf) = b6)
    (h7 : treeSub4 7 (extractElfBaseLinesPlaced mpl elf) = b7)
    (h8 : treeSub4 8 (extractElfBaseLinesPlaced mpl elf) = b8)
    (h9 : treeSub4 9 (extractElfBaseLinesPlaced mpl elf) = b9)
    (h10 : treeSub4 10 (extractElfBaseLinesPlaced mpl elf) = b10)
    (h11 : treeSub4 11 (extractElfBaseLinesPlaced mpl elf) = b11)
    (h12 : treeSub4 12 (extractElfBaseLinesPlaced mpl elf) = b12)
    (h13 : treeSub4 13 (extractElfBaseLinesPlaced mpl elf) = b13)
    (h14 : treeSub4 14 (extractElfBaseLinesPlaced mpl elf) = b14)
    (h15 : treeSub4 15 (extractElfBaseLinesPlaced mpl elf) = b15)
    (hbl : mkDepth4 b0 b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 b11 b12 b13 b14 b15 = fs.baseLines) :
    ElfFullValidPlaced mpl mmpl elf fs := by
  have hd4' :
      (({ lines := extractElfRawLinesPlaced elf, stackBase := 0, stackTop := 0 } : FastMem).canWrite
          (tokStorageAddrPlaced mpl) 1 &&
        ({ lines := extractElfRawLinesPlaced elf, stackBase := 0, stackTop := 0 } : FastMem).canWrite
          (tokOnceAddrPlaced mpl + 8#64) 4) = true ∧
      isFullDepth4 (extractElfBaseLinesPlaced mpl elf) = true := by
    rw [checkElfBaseLinesPlacedDepth4, Bool.and_eq_true] at hd4
    exact hd4
  have hbl_eq : extractElfBaseLinesPlaced mpl elf = fs.baseLines :=
    (eq_mkDepth4 hd4'.2 h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 h14 h15).trans hbl
  have hd4_fs : isFullDepth4 fs.baseLines = true :=
    hbl_eq ▸ hd4'.2
  exact elfFullValidPlaced_of_parts hin hsc hhk hd4'.1 hd4_fs hbl_eq

example (b0 b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 b11 b12 b13 b14 b15 : BinTree Line64) :
    mkDepth4 b0 b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 b11 b12 b13 b14 b15 =
      mkDepth3
        (.branch b0 b8) (.branch b1 b9) (.branch b2 b10) (.branch b3 b11)
        (.branch b4 b12) (.branch b5 b13) (.branch b6 b14) (.branch b7 b15) :=
  rfl

end Symbolic.BugInjection.Proofs.CliExec.ElfFullSpecPlaced
