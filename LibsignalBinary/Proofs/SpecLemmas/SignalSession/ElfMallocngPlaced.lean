/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public meta import Lean
public meta import Arm64
public meta import ProofLib.ProgramReflection
public meta import ProofLib.Placed.Multi
public meta import VerifiedLibraries.Mallocng.Proofs.PlacedInterned
public meta import LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfMultiHelpers
public meta import LibsignalBinary.Specifications.SignalSession.CliElf
public meta import LibsignalBinary.Proofs.SignalSession.Cli.CliElfProof
public meta import LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfSymChars
public import ProofLib.Placed.Multi
public import VerifiedLibraries.Mallocng.Proofs.PlacedInterned
public import LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfMultiHelpers
public import LibsignalBinary.Specifications.SignalSession.CliElf
public import LibsignalBinary.Proofs.SignalSession.Cli.CliElfProof
public import LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfSymChars

/-!
# `VerifiedLibraries.mallocngLib` Placement and Uniqueness in `cliElfBytes`

**Checked by Lean.** Certifies `Placeable`, `InElf`, `DataDisjoint`, `LinkedAt`, `LinkedIn`, and
66-step relocation-inversion uniqueness (`inElf_unique`, `linkedAt_unique`) for
`VerifiedLibraries.mallocngLib` (`24` code blocks, `9` data objects, `6` global exports) in
`cliElfBytes`. Block bases (`cliElfMallocngBlockBases`) and symbol addresses
(`cliElfMallocngSymAddrs`) are decoded at elaboration time from `.symtab` and `PT_LOAD` segment
bytes via `gen_elf_mallocng_interned`.
-/

set_option autoImplicit false
set_option maxRecDepth 400000

@[expose] public section

namespace LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfMallocngPlaced

open Arm64 Arm64.Obj Arm64.Obj.Interned Arm64.Process
open ProofLib ProofLib.ObjectLoad ProofLib.ProgramReflection
open VerifiedLibraries.Mallocng.Proofs (
  mallocngMultiL mallocngMultiL_names mallocngMultiL_toMultiPlacedLib mallocngNameChars
)
open CryptoVerification.SignalSession (cliElfBytes cliElfImage cliElf_parse)
open LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfSymChars (
  cliElfSymChars cliElf_symbols_eq
)

/-! ## Target ELF Aliases -/

noncomputable abbrev targetElfBytes : List (BitVec 8) := cliElfBytes

noncomputable abbrev targetElfImage : ElfImage := cliElfImage

noncomputable abbrev targetElfSymChars : List (List Char × BitVec 64) := cliElfSymChars

theorem targetElf_parse : ElfImage.parse targetElfBytes = .ok targetElfImage :=
  cliElf_parse

theorem targetElfSyms_eq :
    targetElfImage.symbols = ProofLib.ProgramReflection.toStringAssoc targetElfSymChars :=
  cliElf_symbols_eq

/-! ## Relocation-Inversion DAG and Elaborated Layout -/

/-- Static 66-step relocation-inversion DAG for `VerifiedLibraries.mallocngLib`
(6 global `.symtab` exports resolving 24 blocks and 42 symbols). -/
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

section MetaGenElfMallocngInterned

open Lean Meta Elab Term Command ProofLib.ProgramReflection

private meta def mallocngRelocInvStepsMeta : List Obj.Interned.InvStep :=
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

private meta def whnfAllMwit (e : Expr) : MetaM Expr :=
  withTransparency .all (whnf e)

private meta def evalStrLitMwit (e : Expr) : MetaM String := do
  if let .lit (.strVal s) := e then return s
  let r ← whnfAllMwit e
  if let .lit (.strVal s) := r then return s
  let r2 ← withTransparency .all (reduce e)
  if let .lit (.strVal s) := r2 then return s
  throwError "gen_elf_mallocng_interned: expected String literal, got {r2}"

private meta def evalNatExprMwit (e : Expr) : MetaM Nat := do
  if let .lit (.natVal n) := e then return n
  if let some n := e.rawNatLit? then return n
  let r ← whnfAllMwit e
  if let .lit (.natVal n) := r then return n
  if let some n := r.rawNatLit? then return n
  let r2 ← withTransparency .all (reduce e)
  if let .lit (.natVal n) := r2 then return n
  if let some n := r2.rawNatLit? then return n
  throwError "gen_elf_mallocng_interned: expected Nat literal, got {r2}"

private meta def evalBv64ToNatMwit (e : Expr) : MetaM Nat :=
  evalNatExprMwit (mkApp2 (Lean.mkConst ``BitVec.toNat) (mkNatLit 64) e)

private meta def evalBv8ToUInt8Mwit (e : Expr) : MetaM UInt8 := do
  let n ← evalNatExprMwit (mkApp2 (Lean.mkConst ``BitVec.toNat) (mkNatLit 8) e)
  return UInt8.ofNat n

private meta def readBv8ListIterMwit (listE : Expr) : MetaM ByteArray := do
  let mut cur := listE
  let mut out := ByteArray.emptyWithCapacity 65536
  let mut done := false
  while !done do
    if cur.isAppOfArity ``List.cons 3 then
      out := out.push (← evalBv8ToUInt8Mwit (cur.getArg! 1))
      cur := cur.getArg! 2
    else if cur.isAppOfArity ``List.nil 1 then
      done := true
    else
      cur ← whnfAllMwit cur
      if cur.isAppOfArity ``List.cons 3 then
        out := out.push (← evalBv8ToUInt8Mwit (cur.getArg! 1))
        cur := cur.getArg! 2
      else if cur.isAppOfArity ``List.nil 1 then
        done := true
      else
        throwError "gen_elf_mallocng_interned: unexpected byte list spine head"
  return out

private meta def mkListExprMwit (elemTy : Expr) (elems : Array Expr) : Expr :=
  let nilE := mkApp (Lean.mkConst ``List.nil [Level.zero]) elemTy
  let consFn := mkApp (Lean.mkConst ``List.cons [Level.zero]) elemTy
  elems.foldr (fun x acc => mkApp2 consFn x acc) nilE

private meta def mkBv64LitExprMwit (n : Nat) : Expr :=
  mkApp2 (Lean.mkConst ``BitVec.ofNat) (mkNatLit 64) (mkNatLit n)

private meta def addSafeDefMwit (nm : Name) (ty val : Expr) : TermElabM Unit := do
  Lean.withExporting (isExporting := true) do
    let env ← getEnv
    addDecl <| Declaration.defnDecl {
      name := nm
      levelParams := []
      type := ty
      value := val
      hints := .regular (getMaxHeight env val + 1)
      safety := .safe
    }

private meta def readByteSegsMwit (segs : Array (BitVec 64 × ByteArray)) (va : BitVec 64) :
    Option UInt8 := Id.run do
  for (start, bs) in segs do
    let off := (va - start).toNat
    if off < bs.size then
      return some (bs.get! off)
  return none

private meta def readWord32SegsMwit (segs : Array (BitVec 64 × ByteArray)) (va : BitVec 64) :
    Option UInt32 := do
  let b0 ← readByteSegsMwit segs va
  let b1 ← readByteSegsMwit segs (va + BitVec.ofNat 64 1)
  let b2 ← readByteSegsMwit segs (va + BitVec.ofNat 64 2)
  let b3 ← readByteSegsMwit segs (va + BitVec.ofNat 64 3)
  return b0.toUInt32 ||| (b1.toUInt32 <<< 8) ||| (b2.toUInt32 <<< 16) ||| (b3.toUInt32 <<< 24)

private meta def readWord64SegsMwit (segs : Array (BitVec 64 × ByteArray)) (va : BitVec 64) :
    Option (BitVec 64) := do
  let mut acc : Nat := 0
  for k in [:8] do
    let bk ← readByteSegsMwit segs (va + BitVec.ofNat 64 k)
    acc := acc ||| (bk.toNat <<< (8 * k))
  return BitVec.ofNat 64 acc

syntax "gen_elf_mallocng_interned" : command

elab_rules : command
  | `(command| gen_elf_mallocng_interned) => liftTermElabM do
    let currNs ← getCurrNamespace
    let bv64Ty := mkApp (Lean.mkConst ``BitVec) (mkNatLit 64)
    let ml := VerifiedLibraries.Mallocng.Proofs.mallocngMultiL
    let namesArr := ml.names.toArray
    let blksArr := ml.blocks.toArray
    let datasArr := ml.data.toArray

    let mut exportSymLookup : Std.HashMap Nat Nat := {}
    for (kIdx, vIdx) in ml.exportSyms do
      exportSymLookup := exportSymLookup.insert kIdx vIdx

    let elfConst := Lean.mkConst (currNs ++ `targetElfImage)
    let imgSymsRaw ← listElemsWhnf (mkApp (Lean.mkConst ``Arm64.Process.ElfImage.symbols) elfConst)
    let mut symTabAll : Std.HashMap String (Array (BitVec 64)) := {}
    for pairRaw in imgSymsRaw do
      let pairE ← whnfAllMwit pairRaw
      let s ← evalStrLitMwit (pairE.getArg! 2)
      let vNat ← evalBv64ToNatMwit (pairE.getArg! 3)
      symTabAll := symTabAll.insert s ((symTabAll.getD s #[]).push (BitVec.ofNat 64 vNat))

    let lookupUniqueMeta (s : String) : TermElabM (BitVec 64) := do
      match symTabAll[s]? with
      | some #[va] => return va
      | some arr =>
        throwError "gen_elf_mallocng_interned: non-unique symbol {s} in targetElfImage ({arr.size} hits)"
      | none =>
        throwError "gen_elf_mallocng_interned: missing symbol {s} in targetElfImage"

    let segsRaw ← listElemsWhnf (mkApp (Lean.mkConst ``Arm64.Process.ElfImage.segments) elfConst)
    let mut segsArr : Array (BitVec 64 × ByteArray) := #[]
    for segRaw in segsRaw do
      let segE ← whnfAllMwit segRaw
      let startNat ← evalBv64ToNatMwit (segE.getArg! 0)
      let bs ← readBv8ListIterMwit (segE.getArg! 2)
      segsArr := segsArr.push (BitVec.ofNat 64 startNat, bs)

    let mut blkBases : Array (Option (BitVec 64)) := Array.replicate blksArr.size none
    let mut symAddrs : Array (Option (BitVec 64)) := Array.replicate namesArr.size none

    for step in mallocngRelocInvStepsMeta do
      match step with
      | .exportSym e bi off =>
        let elfSymIdx := exportSymLookup.getD e e
        let va ← lookupUniqueMeta namesArr[elfSymIdx]!
        blkBases := blkBases.set! bi (some (va - BitVec.ofNat 64 off))
      | .symOfBlock bi sym off =>
        let some b := blkBases[bi]!
          | throwError "gen_elf_mallocng_interned: symOfBlock unknown block {bi}"
        symAddrs := symAddrs.set! sym (some (b + BitVec.ofNat 64 off))
      | .blockOfSym sym bi off =>
        let some a := symAddrs[sym]!
          | throwError "gen_elf_mallocng_interned: blockOfSym unknown sym {sym}"
        blkBases := blkBases.set! bi (some (a - BitVec.ofNat 64 off))
      | .branch bi off sym addend =>
        let some b := blkBases[bi]!
          | throwError "gen_elf_mallocng_interned: branch unknown block {bi}"
        let pc := b + BitVec.ofNat 64 off
        let some w ← pure (readWord32SegsMwit segsArr pc)
          | throwError "gen_elf_mallocng_interned: branch unmapped at {pc.toNat}"
        let imm26 := w.toNat % (1 <<< 26)
        let dispBytes : Int :=
          (if imm26 >= (1 <<< 25) then (imm26 : Int) - ((1 <<< 26) : Int) else (imm26 : Int)) * 4
        let target := Obj.addSignedAddr pc dispBytes
        symAddrs := symAddrs.set! sym (some (Obj.addSignedAddr target (-addend)))
      | .adrpLo12 bi off1 off2 sym addend =>
        let some b := blkBases[bi]!
          | throwError "gen_elf_mallocng_interned: adrpLo12 unknown block {bi}"
        let blk := blksArr[bi]!
        let some r2 := blk.relocs.find? (·.off == off2)
          | throwError "gen_elf_mallocng_interned: missing lo12 reloc at blk {bi} off {off2}"
        let some scale := Obj.Interned.lo12Scale? r2.kind
          | throwError "gen_elf_mallocng_interned: non-lo12 reloc kind at blk {bi} off {off2}"
        let pc1 := b + BitVec.ofNat 64 off1
        let pc2 := b + BitVec.ofNat 64 off2
        let some w1 ← pure (readWord32SegsMwit segsArr pc1)
          | throwError "gen_elf_mallocng_interned: adrp unmapped at {pc1.toNat}"
        let some w2 ← pure (readWord32SegsMwit segsArr pc2)
          | throwError "gen_elf_mallocng_interned: lo12 unmapped at {pc2.toNat}"
        let immlo := (w1.toNat >>> 29) % 4
        let immhi := (w1.toNat >>> 5) % (1 <<< 19)
        let imm21 := (immhi <<< 2) ||| immlo
        let pgDisp : Int :=
          (if imm21 >= (1 <<< 20) then (imm21 : Int) - ((1 <<< 21) : Int) else (imm21 : Int)) * 4096
        let targetPage := Obj.addSignedAddr (Obj.pageOf pc1) pgDisp
        let imm12 := (w2.toNat >>> 10) % 4096
        let target := targetPage + BitVec.ofNat 64 (imm12 <<< scale)
        symAddrs := symAddrs.set! sym (some (Obj.addSignedAddr target (-addend)))
      | .dataAbs64 di off sym addend =>
        let d := datasArr[di]!
        let some dAddr := symAddrs[d.sym]!
          | throwError "gen_elf_mallocng_interned: dataAbs64 unknown data sym {d.sym}"
        let some target ← pure (readWord64SegsMwit segsArr (dAddr + BitVec.ofNat 64 off))
          | throwError "gen_elf_mallocng_interned: dataAbs64 unmapped at {dAddr.toNat + off}"
        symAddrs := symAddrs.set! sym (some (Obj.addSignedAddr target (-addend)))

    let mut basesExprArr : Array Expr := #[]
    for bi in [:blkBases.size] do
      let some b := blkBases[bi]!
        | throwError "gen_elf_mallocng_interned: block {bi} base unresolved"
      basesExprArr := basesExprArr.push (mkBv64LitExprMwit b.toNat)

    let mut addrsExprArr : Array Expr := #[]
    for si in [:symAddrs.size] do
      let some a := symAddrs[si]!
        | throwError "gen_elf_mallocng_interned: symbol {si} ({namesArr[si]!}) unresolved"
      addrsExprArr := addrsExprArr.push (mkBv64LitExprMwit a.toNat)

    addSafeDefMwit (currNs ++ `cliElfMallocngBlockBases)
      (mkApp (Lean.mkConst ``List [Level.zero]) bv64Ty)
      (mkListExprMwit bv64Ty basesExprArr)
    addSafeDefMwit (currNs ++ `cliElfMallocngSymAddrs)
      (mkApp (Lean.mkConst ``List [Level.zero]) bv64Ty)
      (mkListExprMwit bv64Ty addrsExprArr)

end MetaGenElfMallocngInterned

gen_elf_mallocng_interned

/-! ## `Placeable`, `InElf`, `DataDisjoint`, and `LinkedIn` -/

/-- Like `Obj.Interned.checkMultiMetaCoreFastB`, but falls back from `rangesSorted` to pairwise
    `checkRangesDisjoint` when blocks are laid out out-of-index-order in the stock `ld.lld` ELF
    (`memcpy`/`memset` in `.text.b_pre` at `0x469650`/`0x4697e0` ahead of blocks `0..19` in `.text`). -/
def checkMultiMetaCoreAnyOrderB (ML : Obj.Interned.MultiLib)
    (mly : Obj.Interned.MultiLayout) (nameChars : List (List Char)) : Bool :=
  Nat.blt mly.bases.length 1048576 &&
  Nat.blt mly.addrs.length 1048576 &&
  Nat.blt mly.relax.length 1048576 &&
  Nat.blt mly.b2b.length 1048576 &&
  Nat.blt nameChars.length 1048576 &&
  Obj.Interned.namesNodup nameChars &&
  Obj.Interned.multiIdsOkFast ML &&
  Obj.Interned.withVecTree 0#64 mly.bases fun tBase =>
  Obj.Interned.withVecTree 0#64 mly.addrs fun tAddr =>
  Obj.Interned.withNat ML.names.length fun nNames =>
  match Obj.Interned.insertAllBlocks 0 ML.blocks (Obj.Interned.mkNoneTree 20 nNames) with
  | none => false
  | some tSym =>
    match Obj.Interned.insertBlockSyms 0 (ML.data.map fun d => (d.sym, 0)) tSym with
    | none => false
    | some _ =>
      Obj.Interned.blockSymsMatchTree ML tBase tAddr &&
      Obj.Interned.textPlaceableTreeMulti ML tBase tAddr &&
      (rangesSorted (Obj.Interned.blockRanges tBase 0 ML.blocks) ||
        Obj.allIdx (fun i b1 =>
          Obj.allIdx (fun j b2 =>
            !Nat.blt i j ||
              checkRangesDisjoint (mly.bases.getD i 0#64).toNat b1.code.length
                (mly.bases.getD j 0#64).toNat b2.code.length)
            0 ML.blocks) 0 ML.blocks)

private theorem checkMultiSplitAnyOrder_spec {lib : Obj.MultiPlacedLib}
    {ML : Obj.Interned.MultiLib} {mly : Obj.Interned.MultiLayout}
    {nameChars : List (List Char)} {img : ElfImage} {symChars : List (List Char × BitVec 64)}
    (hlib : lib = ML.toMultiPlacedLib)
    (hnames : ML.names = nameChars.map String.ofList)
    (hsyms : img.symbols = toStringAssoc symChars)
    (hcore : checkMultiMetaCoreAnyOrderB ML mly nameChars = true)
    (hdata : Obj.Interned.checkMultiMetaDataFastB ML mly = true)
    (hexp : Obj.Interned.checkMultiMetaExportsFastB ML mly nameChars symChars = true)
    (hdwalk : Obj.Interned.checkMultiDataWalkFastB ML mly img = true)
    (htwalk : Obj.Interned.checkMultiTextWalkFastB ML mly img = true) :
    let mpl := mly.toMultiPlacement ML.names
    lib.Placeable mpl ∧ lib.InElf img mpl ∧ lib.DataDisjoint mpl := by
  subst hlib
  unfold checkMultiMetaCoreAnyOrderB at hcore
  unfold Obj.Interned.checkMultiMetaDataFastB at hdata
  unfold Obj.Interned.checkMultiMetaExportsFastB at hexp
  unfold Obj.Interned.checkMultiDataWalkFastB at hdwalk
  unfold Obj.Interned.checkMultiTextWalkFastB at htwalk
  simp only [withVecTree_eq, withRegionsWithLen_eq, buildEncSymTable_eq, withNat_eq,
    multiIdsOkFast_eq, Bool.and_eq_true, Nat.blt_eq] at hcore hdata hexp hdwalk htwalk
  obtain ⟨⟨⟨⟨⟨⟨⟨hb, ha⟩, hrx⟩, hb2b⟩, hnc⟩, hnn⟩, hids⟩, hrest⟩ := hcore
  cases hsym : insertAllBlocks 0 ML.blocks (mkNoneTree 20 ML.names.length) with
  | none => rw [hsym] at hrest; nomatch hrest
  | some tSym =>
    rw [hsym] at hrest hexp
    dsimp only at hrest hexp
    cases hdsym : insertBlockSyms 0 (ML.data.map fun d => (d.sym, 0)) tSym with
    | none => rw [hdsym] at hrest; nomatch hrest
    | some tSymData =>
      rw [hdsym] at hrest
      dsimp only at hrest
      simp only [Bool.and_eq_true] at hrest
      obtain ⟨⟨hmatch, htp⟩, hdisj_or⟩ := hrest
      have hdisj' : Obj.allIdx (fun i b1 =>
          Obj.allIdx (fun j b2 =>
            !Nat.blt i j ||
              checkRangesDisjoint (mly.bases.getD i 0#64).toNat b1.code.length
                (mly.bases.getD j 0#64).toNat b2.code.length)
            0 ML.blocks) 0 ML.blocks = true := by
        rw [Bool.or_eq_true] at hdisj_or
        rcases hdisj_or with hsorted | hpw
        · exact blocksDisjoint_of_rangesSorted hb hsorted
        · exact hpw
      obtain ⟨hnd_syms, _, hget_sym⟩ := insertAllBlocks_spec 0 ML.blocks _ tSym hsym
      obtain ⟨hnd_data_raw, hnone_data_raw, _⟩ :=
        insertBlockSyms_spec 0 (ML.data.map fun d => (d.sym, 0)) tSym tSymData hdsym
      have hmap_data : ((ML.data.map fun d => (d.sym, 0)).map (·.1)) = ML.data.map (·.sym) := by
        simp [List.map_map, Function.comp_def]
      rw [hmap_data] at hnd_data_raw hnone_data_raw
      have hlookup : ∀ q, tSym.getD none q = lookupBlockSymId q ML.blocks := by
        intro q
        rw [hget_sym q, getD_mkNoneTree]
        rfl
      rw [blockSymsMatchTree_eq ML mly hb ha] at hmatch
      rw [textPlaceableTreeMulti_eq ML mly hb ha] at htp
      have hnd_b : natNodupFast ((ML.blocks.flatMap (·.symbols)).map (·.1)) = true := by
        simp [natNodupFast, natNodup_of_nodup hnd_syms]
      have hdp' := dataPlaceableTreeMulti_imp ML mly ha hnd_data_raw hdata.1
      have hdnone' : (ML.data.all fun d => (lookupBlockSymId d.sym ML.blocks).isNone) = true := by
        rw [List.all_eq_true]
        intro d hd
        have hnone := hnone_data_raw d.sym (List.mem_map_of_mem hd)
        rw [hlookup d.sym] at hnone
        simp [hnone]
      rw [multiTextWalkTree_eq ML mly hb ha hrx hb2b] at htwalk
      rw [dataWalkTreeMulti_eq ML mly ha] at hdwalk
      rw [multiExportsOkTree_eq ML mly nameChars _ tSym hb hnc hlookup] at hexp
      have hddisj' := multiDataDisjointTree_imp ha hdata.2
      have hmp : multiPlaceableB ML mly = true := by
        simp only [multiPlaceableB, Bool.and_eq_true]
        exact ⟨⟨⟨⟨htp, (Bool.or_eq_true _ _).mpr (Or.inr hdisj')⟩, hnd_b⟩, hdp'⟩, hdnone'⟩
      apply checkMultiDisjoint_spec hnames hsyms
      simp only [checkMultiDisjoint, checkMulti, Bool.and_eq_true]
      exact ⟨⟨⟨⟨⟨⟨⟨hnn, hids⟩, hmatch⟩, hmp⟩, htwalk⟩, hdwalk⟩, hexp⟩, hddisj'⟩

/-- Interned `MultiLayout` for `mallocngMultiL` decoded from `targetElfImage`. -/
noncomputable def cliElfMallocngMultiLayout : Obj.Interned.MultiLayout where
  bases := cliElfMallocngBlockBases
  addrs := cliElfMallocngSymAddrs

/-- Concrete `MultiPlacement` for `VerifiedLibraries.mallocngLib` in `targetElfBytes`. -/
noncomputable def cliElfMallocngPlacement : Obj.MultiPlacement :=
  cliElfMallocngMultiLayout.toMultiPlacement mallocngMultiL.names

theorem cliElf_mallocng_metaCore_ok :
    checkMultiMetaCoreAnyOrderB mallocngMultiL cliElfMallocngMultiLayout
      mallocngNameChars = true := by
  rfl_kernel

theorem cliElf_mallocng_metaData_ok :
    Obj.Interned.checkMultiMetaDataFastB mallocngMultiL cliElfMallocngMultiLayout = true := by
  rfl_kernel

theorem cliElf_mallocng_metaExports_ok :
    Obj.Interned.checkMultiMetaExportsFastB mallocngMultiL cliElfMallocngMultiLayout
      mallocngNameChars targetElfSymChars = true := by
  rfl_kernel

theorem cliElf_mallocng_dataWalk_ok :
    Obj.Interned.checkMultiDataWalkFastB mallocngMultiL cliElfMallocngMultiLayout
      targetElfImage = true := by
  rfl_kernel

theorem cliElf_mallocng_textWalk_ok :
    Obj.Interned.checkMultiTextWalkFastB mallocngMultiL cliElfMallocngMultiLayout
      targetElfImage = true := by
  rfl_kernel

/-- `Placeable ∧ InElf targetElfImage ∧ DataDisjoint` for `VerifiedLibraries.mallocngLib` at
`cliElfMallocngPlacement`. -/
theorem cliElf_mallocng_placed :
    VerifiedLibraries.mallocngLib.Placeable cliElfMallocngPlacement ∧
    VerifiedLibraries.mallocngLib.InElf targetElfImage cliElfMallocngPlacement ∧
    VerifiedLibraries.mallocngLib.DataDisjoint cliElfMallocngPlacement :=
  checkMultiSplitAnyOrder_spec mallocngMultiL_toMultiPlacedLib.symm
    mallocngMultiL_names targetElfSyms_eq
    cliElf_mallocng_metaCore_ok cliElf_mallocng_metaData_ok cliElf_mallocng_metaExports_ok
    cliElf_mallocng_dataWalk_ok cliElf_mallocng_textWalk_ok

theorem cliElf_mallocng_linkedAt :
    VerifiedLibraries.mallocngLib.LinkedAt targetElfBytes cliElfMallocngPlacement :=
  ⟨targetElfImage, targetElf_parse, cliElf_mallocng_placed.1, cliElf_mallocng_placed.2.1⟩

/-- `VerifiedLibraries.mallocngLib.LinkedIn targetElfBytes` holds. -/
theorem cliElf_mallocng_linkedIn :
    VerifiedLibraries.mallocngLib.LinkedIn targetElfBytes :=
  ⟨cliElfMallocngPlacement, cliElf_mallocng_linkedAt⟩

/-! ## Relocation-Inversion Uniqueness -/

theorem cliElf_mallocng_relocInv_ok :
    Obj.Interned.checkRelocInvStepsB mallocngMultiL mallocngNameChars
      mallocngRelocInvSteps = true := by
  rfl_kernel

theorem cliElf_mallocng_relax_false (i o : Nat) :
    cliElfMallocngPlacement.relax i o = false := by
  cases i <;> rfl

/-- Relocation-inversion uniqueness and `DataDisjoint` for any `InElf targetElfImage` placement of
`VerifiedLibraries.mallocngLib`. -/
theorem cliElf_mallocng_inElf_unique {mmpl : Obj.MultiPlacement}
    (hpl : VerifiedLibraries.mallocngLib.Placeable mmpl)
    (hin : VerifiedLibraries.mallocngLib.InElf targetElfImage mmpl) :
    (∀ i < VerifiedLibraries.mallocngLib.blocks.length,
      mmpl.base i = cliElfMallocngPlacement.base i) ∧
    (∀ s ∈ mallocngMultiL.names,
      VerifiedLibraries.mallocngLib.resolve mmpl s =
        VerifiedLibraries.mallocngLib.resolve cliElfMallocngPlacement s) ∧
    (∀ s ∈ mallocngMultiL.names,
      Obj.lookupBlockSym s VerifiedLibraries.mallocngLib.blocks = none →
        mmpl.ρ s = cliElfMallocngPlacement.ρ s) ∧
    VerifiedLibraries.mallocngLib.DataDisjoint mmpl :=
  Obj.Interned.checkRelocInvStepsB_sound mallocngMultiL_toMultiPlacedLib.symm
    mallocngMultiL_names cliElf_mallocng_relocInv_ok cliElf_mallocng_relax_false
    cliElf_mallocng_placed ⟨hpl, hin⟩

/-- Relocation-inversion uniqueness and `DataDisjoint` for any `LinkedAt targetElfBytes` placement
of `VerifiedLibraries.mallocngLib`. -/
theorem cliElf_mallocng_linkedAt_unique {mmpl : Obj.MultiPlacement}
    (hlink : VerifiedLibraries.mallocngLib.LinkedAt targetElfBytes mmpl) :
    (∀ i < VerifiedLibraries.mallocngLib.blocks.length,
      mmpl.base i = cliElfMallocngPlacement.base i) ∧
    (∀ s ∈ mallocngMultiL.names,
      VerifiedLibraries.mallocngLib.resolve mmpl s =
        VerifiedLibraries.mallocngLib.resolve cliElfMallocngPlacement s) ∧
    (∀ s ∈ mallocngMultiL.names,
      Obj.lookupBlockSym s VerifiedLibraries.mallocngLib.blocks = none →
        mmpl.ρ s = cliElfMallocngPlacement.ρ s) ∧
    VerifiedLibraries.mallocngLib.DataDisjoint mmpl := by
  obtain ⟨img, hparse, hpl, hin⟩ := hlink
  cases targetElf_parse.symm.trans hparse
  exact cliElf_mallocng_inElf_unique hpl hin

theorem cliElf_mallocng_dataDisjoint_of_linkedAt {mmpl : Obj.MultiPlacement}
    (hlink : VerifiedLibraries.mallocngLib.LinkedAt targetElfBytes mmpl) :
    VerifiedLibraries.mallocngLib.DataDisjoint mmpl :=
  (cliElf_mallocng_linkedAt_unique hlink).2.2.2

theorem cliElf_mallocng_blocks_pos : 0 < VerifiedLibraries.mallocngLib.blocks.length :=
  Nat.lt_of_sub_eq_succ rfl

/-- `dataInit` holds in any `loadState` of `targetElfImage` for any `LinkedAt targetElfBytes`
placement of `VerifiedLibraries.mallocngLib`. -/
theorem cliElf_mallocng_dataInit_of_linkedAt {mmpl : Obj.MultiPlacement}
    {inputs : ProcessInputs} {s : State}
    (hlink : VerifiedLibraries.mallocngLib.LinkedAt targetElfBytes mmpl)
    (hload : targetElfImage.loadState inputs = .ok s) :
    s.mem ⊨ VerifiedLibraries.mallocngLib.dataInit mmpl := by
  have hdd := cliElf_mallocng_dataDisjoint_of_linkedAt hlink
  obtain ⟨img, hparse, hpl, hin⟩ := hlink
  cases targetElf_parse.symm.trans hparse
  exact VerifiedLibraries.mallocngLib.satisfies_dataInit_of_inElf
    hpl hin hload cliElf_mallocng_blocks_pos hdd

end LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfMallocngPlaced
