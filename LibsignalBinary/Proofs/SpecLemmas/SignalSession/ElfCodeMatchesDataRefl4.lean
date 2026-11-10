/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Arm64
public import GeneratedLean.LibsignalSessionPlacedObj
public import LibsignalBinary.Heap.Fine.F3LayoutData
public import LibsignalBinary.Proofs.Placed.GenLsBlock
public import LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfCodeMatchesDataGen
public import LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfCodeMatchesDataRefl1
public import LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfCodeMatchesDataRefl2
public import LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfCodeMatchesDataRefl3
public import LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfMultiHelpers
public import LibsignalBinary.Specifications.SignalSession.CliBinaryPq
public import ProofLib.Placed.Multi
public import ProofLib.ProgramReflection
public import VerifiedLibraries.Mallocng.Proofs.PlacedInterned

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 200000

/-!
# Symbol-Pinning, `mallocngLib` Relocation-Inversion, and Hook-Table Reflection Shard 4

Proves symbol-pinning certificates (`f3NoShim_pin_ok`, `f3HandleError_pin_ok`), the 66-step
relocation-inversion DAG for `VerifiedLibraries.mallocngLib`, and compact hook-table reflection
identities for `ElfCodeMatchesPlaced`.
-/

namespace LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfCodeMatchesData

open Arm64 Arm64.Obj Arm64.Obj.Interned

noncomputable section ReflectionLemmas

open ProofLib ProofLib.ProgramReflection
open CryptoVerification.LibsignalSpqrV1 (tokenName tokenStorageName)
open CryptoVerification.SignalSession
  (cliDehookedSymsPlaced libsignalSessionLib lsRustNoAllocShimSymCli)
open LibsignalBinary.Heap.Fine
  (f3MallocngMpl f3StdLayout f3StubNoShimAddr)
open VerifiedLibraries.Mallocng.Proofs
  (mallocngMultiL mallocngNameChars)


theorem f3NoShim_pin_ok :
    (Nat.blt f3NoShimIdx lsInternedMultiLib.names.length &&
     (lsInternedMultiLib.names.getD f3NoShimIdx "" == lsRustNoAllocShimSymCli) &&
     (Obj.Interned.lookupBlockSymId f3NoShimIdx lsInternedMultiLib.blocks == none) &&
     (f3LsSymAddrs.getD f3NoShimIdx 0#64 == f3StubNoShimAddr)) = true := by
  rfl_kernel

/-- Mangled `alloc::raw_vec::handle_error` symbol name (`CliIoHandleErrorTiedByName`). -/
abbrev f3HandleErrorSym : String :=
  "_RNvNtCs69KKACWg7bl_5alloc7raw_vec12handle_error"

theorem f3HandleError_pin_ok :
    (Nat.blt f3HandleErrorIdx lsInternedMultiLib.names.length &&
     (lsInternedMultiLib.names.getD f3HandleErrorIdx "" == f3HandleErrorSym) &&
     (Obj.Interned.lookupBlockSymId f3HandleErrorIdx lsInternedMultiLib.blocks == none)) = true := by
  rfl_kernel

/-- Static 66-step relocation-inversion DAG for `VerifiedLibraries.mallocngLib`
(6 global exports resolving 24 blocks and 42 symbols). -/
def mallocngRelocInvSteps : List Obj.Interned.InvStep :=
  [ .exportSym 29 4 0, .exportSym 28 3 0, .exportSym 24 2 0,
    .exportSym 40 13 0, .exportSym 22 12 0, .exportSym 39 11 0,
    .symOfBlock 2 24 0, .symOfBlock 3 28 0, .symOfBlock 4 27 0,
    .symOfBlock 4 29 0, .symOfBlock 4 5 0, .symOfBlock 11 39 0,
    .symOfBlock 12 22 0, .symOfBlock 13 40 0, .branch 2 88 32 0,
    .branch 2 152 0 0, .branch 2 172 10 0, .adrpLo12 2 44 48 13 0,
    .branch 3 0 4 0, .branch 4 0 6 0, .adrpLo12 12 64 68 1 0,
    .adrpLo12 12 304 308 11 0, .adrpLo12 12 340 344 14 0, .branch 13 0 7 0,
    .blockOfSym 0 0 0, .blockOfSym 4 6 0, .blockOfSym 6 9 0,
    .blockOfSym 7 14 0, .blockOfSym 10 10 0, .blockOfSym 32 21 0,
    .branch 6 704 38 0, .branch 6 720 20 0, .branch 6 748 37 0,
    .branch 6 764 8 0, .adrpLo12 6 524 532 3 0, .adrpLo12 6 680 716 12 0,
    .branch 9 508 15 0, .branch 9 576 9 0, .branch 9 764 23 0,
    .adrpLo12 9 88 96 25 0, .branch 14 640 31 0, .branch 14 988 17 0,
    .adrpLo12 14 496 504 26 0, .symOfBlock 0 2 0, .blockOfSym 8 22 0,
    .blockOfSym 9 7 0, .blockOfSym 15 16 0, .blockOfSym 17 18 0,
    .blockOfSym 20 23 0, .blockOfSym 23 8 0, .blockOfSym 31 20 0,
    .blockOfSym 37 19 0, .blockOfSym 38 5 0, .branch 7 560 35 0,
    .adrpLo12 8 704 708 41 0, .adrpLo12 8 760 764 30 0, .branch 16 120 19 0,
    .branch 16 172 21 0, .symOfBlock 16 33 0, .symOfBlock 16 34 0,
    .symOfBlock 18 36 0, .symOfBlock 19 18 0, .blockOfSym 19 1 0,
    .blockOfSym 21 15 0, .blockOfSym 35 17 0, .symOfBlock 17 16 0 ]

theorem mallocngRelocInv_ok :
    Obj.Interned.checkRelocInvStepsB mallocngMultiL mallocngNameChars mallocngRelocInvSteps = true := by
  rfl_kernel

theorem f3MallocngMpl_relax_false (i o : Nat) :
    f3MallocngMpl.relax i o = false := by
  cases i <;> rfl

theorem checkMallocngLibcPin_ok :
    (mallocngMultiL.names.contains "__libc" &&
     (Obj.lookupBlockSym "__libc" VerifiedLibraries.mallocngLib.blocks == none) &&
     (f3MallocngMpl.ρ "__libc" == f3StdLayout.libcAddr)) = true := by
  rfl_kernel

theorem f3LsCodeHi_lt_2pow64 : Nat.blt f3LsCodeHi 18446744073709551616 = true := by
  rfl_kernel

theorem f3LsBlockBases_lt_codeHi :
    (f3LsBlockBases.all fun b => Nat.blt b.toNat f3LsCodeHi) = true := by
  rfl_kernel

def checkMallocngCodeBoundsB : Bool :=
  Nat.beq VerifiedLibraries.mallocngLib.blocks.length 24 &&
  Nat.ble f3LsCodeHi f3MngCodeLo &&
  Nat.ble f3MngCodeHi 18446744073709551616 &&
  (List.range 24).all fun j =>
    let b := (f3MallocngMpl.base j).toNat
    let len := (VerifiedLibraries.mallocngLib.blocks.getD j { code := [] }).code.length
    Nat.ble f3MngCodeLo b && Nat.ble (b + len) f3MngCodeHi

theorem checkMallocngCodeBounds_ok : checkMallocngCodeBoundsB = true := by
  rfl_kernel

theorem f3Ls_mng_base0_lt :
    Nat.blt (f3LsMpl.base 0).toNat (f3MallocngMpl.base 0).toNat = true := by
  rfl_kernel

/-- 3-band `libsignalSessionLib` data-bounds predicate on stock `ld.lld`:
every `d ∈ lsInternedMultiLib.data` lies in `[0, f3LsRoHi)` (`.rodata`),
`[f3LsRw1Lo, f3LsRw1Hi)` (`.data`), or `[f3LsRw2Lo, f3LsRw2Hi)` (`.bss`). -/
def lsDataInStockBandsB (a len : Nat) : Bool :=
  Nat.ble (a + len) f3LsRoHi ||
  (Nat.ble f3LsRw1Lo a && Nat.ble (a + len) f3LsRw1Hi) ||
  (Nat.ble f3LsRw2Lo a && Nat.ble (a + len) f3LsRw2Hi)

def checkLsDataBoundsB : Bool :=
  lsInternedMultiLib.data.all fun d =>
    Nat.blt d.sym lsInternedMultiLib.names.length &&
    lsDataInStockBandsB (f3LsSymAddrs.getD d.sym 0#64).toNat (d.bytes.length + d.zeroTail)

private def checkLsDataBoundsFastB : Bool :=
  Obj.Interned.withVecTree 0#64 f3LsSymAddrs fun tAddr =>
    lsInternedMultiLib.data.all fun d =>
      Nat.blt d.sym f3LsNamesLen &&
      lsDataInStockBandsB (tAddr.getD 0#64 d.sym).toNat
        (Arm64.Process.fastLen512 512 d.bytes + d.zeroTail)

private theorem checkLsDataBoundsFast_ok : checkLsDataBoundsFastB = true := by
  rfl_kernel

private theorem f3LsSymAddrs_len_lt : f3LsSymAddrs.length < 2 ^ 20 := by
  have h : Nat.blt f3LsSymAddrs.length 1048576 = true := by rfl_kernel
  rw [Nat.blt_eq] at h
  exact h

theorem checkLsDataBounds_ok : checkLsDataBoundsB = true := by
  have hfast := checkLsDataBoundsFast_ok
  unfold checkLsDataBoundsFastB at hfast
  rw [Obj.Interned.withVecTree_eq] at hfast
  have hpred :
      (fun d : Obj.Interned.Data =>
        Nat.blt d.sym f3LsNamesLen &&
        lsDataInStockBandsB (((Obj.Interned.toVecTree 0#64 f3LsSymAddrs).getD 0#64 d.sym).toNat)
          (Arm64.Process.fastLen512 512 d.bytes + d.zeroTail)) =
      (fun d : Obj.Interned.Data =>
        Nat.blt d.sym lsInternedMultiLib.names.length &&
        lsDataInStockBandsB (f3LsSymAddrs.getD d.sym 0#64).toNat
          (d.bytes.length + d.zeroTail)) := by
    funext d
    rw [← ls_names_len_exact,
      Obj.Interned.toVecTree_getD_all 0#64 f3LsSymAddrs f3LsSymAddrs_len_lt d.sym,
      Arm64.Process.fastLen512_eq_length]
  rw [hpred] at hfast
  exact hfast

/-- 5-band RO/RW separation check between `libsignalSessionLib` and `mallocngLib`
(`[0, f3LsRoHi) ≤ [f3MngRoLo, f3MngRoHi) ≤ [f3LsRw1Lo, f3LsRw1Hi) ≤ [f3MngRwLo, f3MngRwHi) ≤ [f3LsRw2Lo, f3LsRw2Hi) ≤ 2^64`),
keeping `Arm64.Obj.MultiPlacedLib.DataDisjoint` completely untouched. -/
def checkMallocngDataBoundsB : Bool :=
  Nat.ble f3LsRoHi f3MngRoLo &&
  Nat.ble f3MngRoLo f3MngRoHi &&
  Nat.ble f3MngRoHi f3LsRw1Lo &&
  Nat.ble f3LsRw1Lo f3LsRw1Hi &&
  Nat.ble f3LsRw1Hi f3MngRwLo &&
  Nat.ble f3MngRwLo f3StdLayout.libcAddr.toNat &&
  Nat.ble (f3StdLayout.libcAddr.toNat + 104) f3MngRwHi &&
  Nat.ble f3MngRwLo f3MngRwHi &&
  Nat.ble f3MngRwHi f3LsRw2Lo &&
  Nat.ble f3LsRw2Lo f3LsRw2Hi &&
  Nat.ble f3LsRw2Hi 18446744073709551616 &&
  (VerifiedLibraries.mallocngLib.data.all fun d =>
    let a := (f3MallocngMpl.ρ d.sym).toNat
    let e := a + (d.bytes.length + d.zeroTail)
    mallocngMultiL.names.contains d.sym &&
    ((Nat.ble f3MngRoLo a && Nat.ble e f3MngRoHi) ||
     (!d.readOnly && Nat.ble f3MngRwLo a && Nat.ble e f3MngRwHi)))

theorem checkMallocngDataBounds_ok : checkMallocngDataBoundsB = true := by
  rfl_kernel

theorem lsPlacedCompactLit_in_seg1 :
    ((lsPlacedCompactLit.all fun p =>
        Nat.ble stockTextStartNat p.1 &&
        Nat.blt p.1 (stockTextStartNat + stockTextLenNat)) &&
     Nat.ble (stockTextStartNat + stockTextLenNat) 18446744073709551616) = true := by
  rfl_kernel

theorem f3TokenPins_ok :
    (Nat.blt f3TokenIdx lsInternedMultiLib.names.length &&
     (lsInternedMultiLib.names.getD f3TokenIdx "" == tokenName) &&
     (Obj.Interned.lookupBlockSymId f3TokenIdx lsInternedMultiLib.blocks == none) &&
     Nat.blt f3TokenStorageIdx lsInternedMultiLib.names.length &&
     (lsInternedMultiLib.names.getD f3TokenStorageIdx "" == tokenStorageName) &&
     (Obj.Interned.lookupBlockSymId f3TokenStorageIdx lsInternedMultiLib.blocks == none)) = true := by
  rfl_kernel

theorem f3StaticsPins_ok :
    (Nat.blt f3LogFilterIdx lsInternedMultiLib.names.length &&
     (lsInternedMultiLib.names.getD f3LogFilterIdx "" == CryptoVerification.lsLogFilterSym) &&
     (Obj.Interned.lookupBlockSymId f3LogFilterIdx lsInternedMultiLib.blocks == none) &&
     Nat.blt f3CoinsNextIdx lsInternedMultiLib.names.length &&
     (lsInternedMultiLib.names.getD f3CoinsNextIdx "" == "libsignal_cli::coins::NEXT.0") &&
     (Obj.Interned.lookupBlockSymId f3CoinsNextIdx lsInternedMultiLib.blocks == none) &&
     Nat.blt f3CoinsLeftIdx lsInternedMultiLib.names.length &&
     (lsInternedMultiLib.names.getD f3CoinsLeftIdx "" == "libsignal_cli::coins::LEFT.0") &&
     (Obj.Interned.lookupBlockSymId f3CoinsLeftIdx lsInternedMultiLib.blocks == none)) = true := by
  rfl_kernel

private theorem lsInternedBlocks_617_lt : 617 < lsInternedMultiLib.blocks.length := by
  have h1 : Nat.ble 618 f3LsBlocksLen = true := by rfl_kernel
  have h2 : lsInternedMultiLib.blocks.length = f3LsBlocksLen :=
    Nat.eq_of_beq_eq_true lsInternedBlocks_len
  rw [Nat.ble_eq] at h1
  omega

private theorem lsInternedBlocks_617_externs :
    (lsInternedMultiLib.blocks[617]'lsInternedBlocks_617_lt).externs = lsSharedExterns := by
  rfl_kernel

theorem ls_block617_externs_eq :
    (libsignalSessionLib.blockLib 617).text.externs =
      lsSharedExterns.map (fun idx => lsInternedMultiLib.names.getD idx "") := by
  have hlen : libsignalSessionLib.blocks.length = lsInternedMultiLib.blocks.length := by
    rw [ls_toMultiPlacedLib_eq, Obj.Interned.MultiLib.toMultiPlacedLib_blocks, List.length_map]
  have h617 : 617 < libsignalSessionLib.blocks.length := hlen ▸ lsInternedBlocks_617_lt
  rw [Obj.MultiPlacedLib.blockLib_text h617]
  simp only [ls_toMultiPlacedLib_eq, Obj.Interned.MultiLib.toMultiPlacedLib_blocks,
    List.getElem_map, Obj.Interned.Block.toCodeBlock]
  rw [lsInternedBlocks_617_externs]

theorem ls_sharedExterns_lt :
    lsSharedExterns.all (fun idx => Nat.blt idx lsInternedMultiLib.names.length) = true := by
  rfl_kernel

theorem lsPlacedStubPairs_eq :
    lsPlacedStubPairs = lsSharedExterns.map fun idx =>
      (lsInternedMultiLib.names.getD idx "", f3LsSymAddrs.getD idx 0#64) := by
  rfl_kernel

theorem lsPlacedCompactLit_lt_mngCodeLo :
    (lsPlacedCompactLit.all fun p => Nat.blt p.1 f3MngCodeLo) = true := by
  rfl_kernel

theorem cliDehookedSymsPlaced_eq_entries :
    cliDehookedSymsPlaced = f3DehookedEntries.map (fun e => String.ofList e.2.1) := by
  rfl_kernel

end ReflectionLemmas

end LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfCodeMatchesData
