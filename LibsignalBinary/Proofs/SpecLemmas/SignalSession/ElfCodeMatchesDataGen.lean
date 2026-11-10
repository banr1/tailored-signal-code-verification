/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

meta import Lean
meta import Arm64
meta import ProofLib.ProgramReflection
meta import GeneratedLean.LibsignalSessionPlacedObj
meta import LibsignalBinary.Heap.Fine.F3LayoutData
meta import LibsignalBinary.Proofs.Placed.GenLsBlock -- shake: keep
meta import LibsignalBinary.Proofs.SignalSession.Cli.CliElfProof
meta import LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfMultiHelpers
meta import LibsignalBinary.Specifications.SignalSession.CliBinaryPq
meta import VerifiedLibraries.Mallocng.Proofs.PlacedInterned
public import Arm64
public import GeneratedLean.LibsignalSessionPlacedObj
public import LibsignalBinary.Heap.Fine.F3LayoutData
public import LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfMultiHelpers
public import LibsignalBinary.Specifications.SignalSession.CliBinaryPq
public import ProofLib.Placed.Multi
public import ProofLib.ProgramReflection
public import VerifiedLibraries.Mallocng.Proofs.PlacedInterned

/-!
# Meta-Reflected Interned Layout and Relocation-Inversion Data

Elaborates the interned `lsInternedMultiLib` library representation, relocation-inversion DAG steps,
block and symbol address tables decoded from `cliElfImage`, and `cliHookTablePlaced` /
`cliDehookedSymsPlaced` tag tables so `ElfCodeMatchesPlaced` checks placement without re-reducing
`libsignalSessionLib` in the kernel.
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 200000

namespace LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfCodeMatchesData

open Arm64 Arm64.Obj Arm64.Obj.Interned

section MetaGenF3LsInterned

open Lean Meta Elab Term Command ProofLib.ProgramReflection

private meta def whnfAllF3 (e : Expr) : MetaM Expr :=
  withTransparency .all (whnf e)

private meta def evalStrLitF3 (e : Expr) : MetaM String := do
  if let .lit (.strVal s) := e then return s
  let r ← whnfAllF3 e
  if let .lit (.strVal s) := r then return s
  let r2 ← withTransparency .all (reduce e)
  if let .lit (.strVal s) := r2 then return s
  throwError "gen_f3_ls_interned: expected String literal, got {r2}"

private meta def evalNatExprF3 (e : Expr) : MetaM Nat := do
  if let .lit (.natVal n) := e then return n
  if let some n := e.rawNatLit? then return n
  let r ← whnfAllF3 e
  if let .lit (.natVal n) := r then return n
  if let some n := r.rawNatLit? then return n
  let r2 ← withTransparency .all (reduce e)
  if let .lit (.natVal n) := r2 then return n
  if let some n := r2.rawNatLit? then return n
  throwError "gen_f3_ls_interned: expected Nat literal, got {r2}"

private meta def evalBv64ToNatF3 (e : Expr) : MetaM Nat :=
  evalNatExprF3 (mkApp2 (Lean.mkConst ``BitVec.toNat) (mkNatLit 64) e)

private meta def evalBv8ToUInt8F3 (e : Expr) : MetaM UInt8 := do
  let n ← evalNatExprF3 (mkApp2 (Lean.mkConst ``BitVec.toNat) (mkNatLit 8) e)
  return UInt8.ofNat n

private meta def readBv8ListIterF3 (listE : Expr) : MetaM ByteArray := do
  let mut cur := listE
  let mut out := ByteArray.emptyWithCapacity 65536
  let mut done := false
  while !done do
    if cur.isAppOfArity ``List.cons 3 then
      out := out.push (← evalBv8ToUInt8F3 (cur.getArg! 1))
      cur := cur.getArg! 2
    else if cur.isAppOfArity ``List.nil 1 then
      done := true
    else
      cur ← whnfAllF3 cur
      if cur.isAppOfArity ``List.cons 3 then
        out := out.push (← evalBv8ToUInt8F3 (cur.getArg! 1))
        cur := cur.getArg! 2
      else if cur.isAppOfArity ``List.nil 1 then
        done := true
      else
        throwError "gen_f3_ls_interned: unexpected byte list spine head"
  return out

private meta def mkListExprF3 (elemTy : Expr) (elems : Array Expr) : Expr :=
  let nilE := mkApp (Lean.mkConst ``List.nil [Level.zero]) elemTy
  let consFn := mkApp (Lean.mkConst ``List.cons [Level.zero]) elemTy
  elems.foldr (fun x acc => mkApp2 consFn x acc) nilE

private meta def mkBv64LitExprF3 (n : Nat) : Expr :=
  mkApp2 (Lean.mkConst ``BitVec.ofNat) (mkNatLit 64) (mkNatLit n)

private meta def mkOptNatExprF3 : Option Nat → Expr
  | none => mkApp (Lean.mkConst ``Option.none [Level.zero]) (Lean.mkConst ``Nat)
  | some n => mkApp2 (Lean.mkConst ``Option.some [Level.zero]) (Lean.mkConst ``Nat) (mkNatLit n)

private meta def addSafeDefF3 (nm : Name) (ty val : Expr) (markNoncomp : Bool := true) :
    TermElabM Unit := do
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
    let _ := markNoncomp
    modifyEnv (addNoncomputable · nm)

private meta def invStepToExprF3 : Obj.Interned.InvStep → Expr
  | .exportSym e bi off =>
    mkApp3 (Lean.mkConst ``Obj.Interned.InvStep.exportSym)
      (mkNatLit e) (mkNatLit bi) (mkNatLit off)
  | .symOfBlock bi sym off =>
    mkApp3 (Lean.mkConst ``Obj.Interned.InvStep.symOfBlock)
      (mkNatLit bi) (mkNatLit sym) (mkNatLit off)
  | .blockOfSym sym bi off =>
    mkApp3 (Lean.mkConst ``Obj.Interned.InvStep.blockOfSym)
      (mkNatLit sym) (mkNatLit bi) (mkNatLit off)
  | .branch bi off sym addend =>
    mkApp4 (Lean.mkConst ``Obj.Interned.InvStep.branch)
      (mkNatLit bi) (mkNatLit off) (mkNatLit sym) (toExpr addend)
  | .adrpLo12 bi off1 off2 sym addend =>
    mkApp5 (Lean.mkConst ``Obj.Interned.InvStep.adrpLo12)
      (mkNatLit bi) (mkNatLit off1) (mkNatLit off2) (mkNatLit sym) (toExpr addend)
  | .dataAbs64 di off sym addend =>
    mkApp4 (Lean.mkConst ``Obj.Interned.InvStep.dataAbs64)
      (mkNatLit di) (mkNatLit off) (mkNatLit sym) (toExpr addend)

private meta def wordAtArrF3 (code : Array (BitVec 8)) (off : Nat) : BitVec 32 :=
  if off + 4 ≤ code.size then
    code[off + 3]! ++ code[off + 2]! ++ code[off + 1]! ++ code[off]!
  else 0#32

private meta def buildRelocInvStepsF3 (symMap : Std.HashMap String Nat) :
    TermElabM (Array Obj.Interned.InvStep × Array (Array (BitVec 8) × Obj.Interned.Block) ×
      Array Obj.Interned.Data) := do
  let lib := CryptoVerification.libsignalSessionMultiLib
  let getSym (s : String) : TermElabM Nat := do
    let some idx := symMap[s]?
      | throwError "gen_f3_ls_interned: symbol not found: {s}"
    return idx
  let sharedExts ← (match lib.blocks.head? with | some b0 => b0.externs | none => []).mapM getSym
  let blks ← lib.blocks.toArray.mapM fun b => do
    let syms ← b.symbols.mapM fun (s, off) => do pure (← getSym s, off)
    let relocs ← b.relocs.mapM fun r => do
      pure ({ off := r.off, kind := r.kind, sym := ← getSym r.sym,
              addend := r.addend, localSym := r.localSym } : Obj.Interned.Reloc)
    let weakRefs ← b.weakRefs.mapM getSym
    return (b.code.toArray,
      ({ code := b.code, align := b.align, symbols := syms, relocs := relocs,
         externs := sharedExts, weakRefs := weakRefs } : Obj.Interned.Block))
  let datas ← lib.data.toArray.mapM fun d => do
    let relocs ← d.relocs.mapM fun r => do
      pure ({ off := r.off, kind := r.kind, sym := ← getSym r.sym,
              addend := r.addend, localSym := r.localSym } : Obj.Interned.Reloc)
    return ({ sym := ← getSym d.sym, align := d.align, readOnly := d.readOnly,
              bytes := d.bytes, zeroTail := d.zeroTail, relocs := relocs } : Obj.Interned.Data)
  let exports ← lib.exports.mapM getSym

  let mut tSym : Std.HashMap Nat (Nat × Nat) := {}
  for bi in [:blks.size] do
    let (_, blk) := blks[bi]!
    let mut seenInBlk : Std.HashSet Nat := {}
    for (sym, off) in blk.symbols do
      if !seenInBlk.contains sym then
        seenInBlk := seenInBlk.insert sym
        if !tSym.contains sym then
          tSym := tSym.insert sym (bi, off)

  let mut dataBySym : Std.HashMap Nat (Array Nat) := {}
  for di in [:datas.size] do
    let d := datas[di]!
    dataBySym := dataBySym.insert d.sym ((dataBySym.getD d.sym #[]).push di)

  let mut blkKnown : Std.HashSet Nat := {}
  let mut symKnown : Std.HashSet Nat := {}
  let mut steps : Array Obj.Interned.InvStep := #[]
  let mut qBlk : Array Nat := #[]
  let mut qSym : Array Nat := #[]
  let mut qBlkIdx : Nat := 0
  let mut qSymIdx : Nat := 0

  for e in exports do
    if let some (bi, off) := tSym[e]? then
      if !blkKnown.contains bi then
        blkKnown := blkKnown.insert bi
        steps := steps.push (.exportSym e bi off)
        qBlk := qBlk.push bi

  while qBlkIdx < qBlk.size || qSymIdx < qSym.size do
    while qBlkIdx < qBlk.size do
      let bi := qBlk[qBlkIdx]!
      qBlkIdx := qBlkIdx + 1
      let (codeArr, blk) := blks[bi]!
      let mut blkSymSet : Std.HashSet Nat := {}
      for (s, _) in blk.symbols do
        blkSymSet := blkSymSet.insert s
      let mut weakSet : Std.HashSet Nat := {}
      for w in blk.weakRefs do
        weakSet := weakSet.insert w
      for (sym, off) in blk.symbols do
        if !symKnown.contains sym && tSym[sym]? == some (bi, off) then
          symKnown := symKnown.insert sym
          steps := steps.push (.symOfBlock bi sym off)
          qSym := qSym.push sym
      let mut firstRelocOffs : Array Nat := #[]
      let mut firstRelocMap : Std.HashMap Nat Obj.Interned.Reloc := {}
      for r in blk.relocs do
        if !firstRelocMap.contains r.off then
          firstRelocOffs := firstRelocOffs.push r.off
          firstRelocMap := firstRelocMap.insert r.off r
      for off in firstRelocOffs do
        let r := firstRelocMap[off]!
        if !symKnown.contains r.sym && off % 4 == 0 && (r.kind == .call26 || r.kind == .jump26) then
          if !blkSymSet.contains r.sym && !weakSet.contains r.sym then
            let w := wordAtArrF3 codeArr off
            if (w &&& 0x7c000000#32) == 0x14000000#32 then
              symKnown := symKnown.insert r.sym
              steps := steps.push (.branch bi off r.sym r.addend)
              qSym := qSym.push r.sym
      let mut adrpKeys : Array (Nat × Int) := #[]
      let mut adrps : Std.HashMap (Nat × Int) Nat := {}
      let mut lo12s : Std.HashMap (Nat × Int) Nat := {}
      for off in firstRelocOffs do
        if off % 4 == 0 then
          let r := firstRelocMap[off]!
          let w := wordAtArrF3 codeArr off
          let key := (r.sym, r.addend)
          if r.kind == .adrpHi21 && (w &&& 0x9f000000#32) == 0x90000000#32 then
            if !adrps.contains key then
              adrpKeys := adrpKeys.push key
              adrps := adrps.insert key off
          else if (Obj.Interned.lo12Scale? r.kind).isSome &&
              (w &&& 0x9f000000#32) != 0x95000000#32 &&
              (w &&& 0x9f000000#32) != 0x10000000#32 then
            if !lo12s.contains key then
              lo12s := lo12s.insert key off
      for (sym, addend) in adrpKeys do
        if !symKnown.contains sym then
          if let some off2 := lo12s[(sym, addend)]? then
            let off1 := adrps[(sym, addend)]!
            symKnown := symKnown.insert sym
            steps := steps.push (.adrpLo12 bi off1 off2 sym addend)
            qSym := qSym.push sym

    while qSymIdx < qSym.size do
      let sym := qSym[qSymIdx]!
      qSymIdx := qSymIdx + 1
      if let some (bi, off) := tSym[sym]? then
        if !blkKnown.contains bi then
          blkKnown := blkKnown.insert bi
          steps := steps.push (.blockOfSym sym bi off)
          qBlk := qBlk.push bi
      for di in dataBySym.getD sym #[] do
        let d := datas[di]!
        let blen := d.bytes.length
        for r in d.relocs do
          if !symKnown.contains r.sym && r.kind == .abs64 then
            if Obj.Interned.hasUnoverwrittenAbs64 blen r.off r.sym r.addend d.relocs then
              symKnown := symKnown.insert r.sym
              steps := steps.push (.dataAbs64 di r.off r.sym r.addend)
              qSym := qSym.push r.sym

  return (steps, blks, datas)

private meta def readByteSegsF3 (segs : Array (BitVec 64 × ByteArray)) (va : BitVec 64) :
    Option UInt8 := Id.run do
  for (start, bs) in segs do
    let off := (va - start).toNat
    if off < bs.size then
      return some (bs.get! off)
  return none

private meta def readWord32SegsF3 (segs : Array (BitVec 64 × ByteArray)) (va : BitVec 64) :
    Option UInt32 := do
  let b0 ← readByteSegsF3 segs va
  let b1 ← readByteSegsF3 segs (va + BitVec.ofNat 64 1)
  let b2 ← readByteSegsF3 segs (va + BitVec.ofNat 64 2)
  let b3 ← readByteSegsF3 segs (va + BitVec.ofNat 64 3)
  return b0.toUInt32 ||| (b1.toUInt32 <<< 8) ||| (b2.toUInt32 <<< 16) ||| (b3.toUInt32 <<< 24)

private meta def readWord64SegsF3 (segs : Array (BitVec 64 × ByteArray)) (va : BitVec 64) :
    Option (BitVec 64) := do
  let mut acc : Nat := 0
  for k in [:8] do
    let bk ← readByteSegsF3 segs (va + BitVec.ofNat 64 k)
    acc := acc ||| (bk.toNat <<< (8 * k))
  return BitVec.ofNat 64 acc

private meta def isPanicSymbolFastMetaF3 (name : String) : Bool :=
  name.startsWith "core::panicking::" ||
  [ "core::result::unwrap_failed",
    "core::option::unwrap_failed",
    "core::option::expect_failed",
    "core::slice::index::slice_start_index_len_fail",
    "core::slice::index::slice_end_index_len_fail",
    "core::slice::index::slice_index_order_fail",
    "core::slice::index::slice_index_fail",
    "alloc::raw_vec::handle_error",
    "alloc::raw_vec::capacity_overflow",
    "alloc::alloc::handle_alloc_error" ].contains name

local syntax "gen_f3_ls_interned" : command

local elab_rules : command
  | `(command| gen_f3_ls_interned) => liftTermElabM do
    let currNs ← getCurrNamespace
    let strTy := Lean.mkConst ``String
    let natTy := Lean.mkConst ``Nat
    let charTy := Lean.mkConst ``Char
    let charListTy := mkApp (Lean.mkConst ``List [Level.zero]) charTy
    let bv64Ty := mkApp (Lean.mkConst ``BitVec) (mkNatLit 64)

    -- Collect sorted deduplicated symbol names across `libsignalSessionMultiLib`.
    let lib := CryptoVerification.libsignalSessionMultiLib
    let mut nameSet : Std.HashSet String := {}
    for b in lib.blocks do
      for (s, _) in b.symbols do nameSet := nameSet.insert s
      for r in b.relocs do nameSet := nameSet.insert r.sym
      for e in b.externs do nameSet := nameSet.insert e
      for w in b.weakRefs do nameSet := nameSet.insert w
    for d in lib.data do
      nameSet := nameSet.insert d.sym
      for r in d.relocs do nameSet := nameSet.insert r.sym
    for e in lib.exports do nameSet := nameSet.insert e
    for (k, v) in lib.exportSyms do
      nameSet := nameSet.insert k
      nameSet := nameSet.insert v

    let sortedNames := nameSet.toArray.qsort (· < ·)
    let mut symMap : Std.HashMap String Nat := {}
    let mut namesArr : Array Expr := #[]
    let mut nameCharsArr : Array Expr := #[]
    for idx in [:sortedNames.size] do
      let s := sortedNames[idx]!
      symMap := symMap.insert s idx
      namesArr := namesArr.push (mkStrLit s)
      nameCharsArr := nameCharsArr.push (toExpr s.toList)

    let lsNamesNm := currNs ++ `lsNames
    let lsNameCharsNm := currNs ++ `lsNameChars
    addSafeDefF3 lsNamesNm (mkApp (Lean.mkConst ``List [Level.zero]) strTy)
      (mkListExprF3 strTy namesArr) (markNoncomp := false)
    addSafeDefF3 lsNameCharsNm (mkApp (Lean.mkConst ``List [Level.zero]) charListTy)
      (mkListExprF3 charListTy nameCharsArr) (markNoncomp := false)

    -- Build relocation-inversion steps (`buildRelocInvStepsF3`).
    let (invSteps, blksMeta, datasMeta) ← buildRelocInvStepsF3 symMap
    let invStepTy := Lean.mkConst ``Arm64.Obj.Interned.InvStep
    addSafeDefF3 (currNs ++ `lsRelocInvSteps)
      (mkApp (Lean.mkConst ``List [Level.zero]) invStepTy)
      (mkListExprF3 invStepTy (invSteps.map invStepToExprF3)) (markNoncomp := false)

    -- Reflect `cliElfImage.symbols` and segments, then replay `invSteps` to decode
    -- `f3LsBlockBases` and `f3LsSymAddrs`.
    let f3ElfConst := Lean.mkConst
      ``CryptoVerification.SignalSession.cliElfImage
    let imgSymsRaw ← listElemsWhnf (mkApp (Lean.mkConst ``Arm64.Process.ElfImage.symbols) f3ElfConst)
    let mut symTabAll : Std.HashMap String (Array (BitVec 64)) := {}
    for pairRaw in imgSymsRaw do
      let pairE ← whnfAllF3 pairRaw
      let s ← evalStrLitF3 (pairE.getArg! 2)
      let vNat ← evalBv64ToNatF3 (pairE.getArg! 3)
      symTabAll := symTabAll.insert s ((symTabAll.getD s #[]).push (BitVec.ofNat 64 vNat))

    let lookupUniqueMeta (s : String) : TermElabM (BitVec 64) := do
      match symTabAll[s]? with
      | some #[va] => return va
      | some arr =>
        throwError "gen_f3_ls_interned: non-unique symbol {s} in f3TrialElf ({arr.size} hits)"
      | none =>
        throwError "gen_f3_ls_interned: missing symbol {s} in f3TrialElf"

    let segsRaw ← listElemsWhnf (mkApp (Lean.mkConst ``Arm64.Process.ElfImage.segments) f3ElfConst)
    let mut segsArr : Array (BitVec 64 × ByteArray) := #[]
    for segRaw in segsRaw do
      let segE ← whnfAllF3 segRaw
      let startNat ← evalBv64ToNatF3 (segE.getArg! 0)
      let bs ← readBv8ListIterF3 (segE.getArg! 2)
      segsArr := segsArr.push (BitVec.ofNat 64 startNat, bs)

    let mut exportSymLookup : Std.HashMap Nat Nat := {}
    for (kStr, vStr) in lib.exportSyms do
      if let (some kIdx, some vIdx) := (symMap[kStr]?, symMap[vStr]?) then
        exportSymLookup := exportSymLookup.insert kIdx vIdx

    let mut blkBases : Array (Option (BitVec 64)) := Array.replicate blksMeta.size none
    let mut symAddrs : Array (Option (BitVec 64)) := Array.replicate sortedNames.size none

    for step in invSteps do
      match step with
      | .exportSym e bi off =>
        let elfSymIdx := exportSymLookup.getD e e
        let va ← lookupUniqueMeta sortedNames[elfSymIdx]!
        blkBases := blkBases.set! bi (some (va - BitVec.ofNat 64 off))
      | .symOfBlock bi sym off =>
        let some b := blkBases[bi]!
          | throwError "gen_f3_ls_interned: symOfBlock unknown block {bi}"
        symAddrs := symAddrs.set! sym (some (b + BitVec.ofNat 64 off))
      | .blockOfSym sym bi off =>
        let some a := symAddrs[sym]!
          | throwError "gen_f3_ls_interned: blockOfSym unknown sym {sym}"
        blkBases := blkBases.set! bi (some (a - BitVec.ofNat 64 off))
      | .branch bi off sym addend =>
        let some b := blkBases[bi]!
          | throwError "gen_f3_ls_interned: branch unknown block {bi}"
        let pc := b + BitVec.ofNat 64 off
        let some w ← pure (readWord32SegsF3 segsArr pc)
          | throwError "gen_f3_ls_interned: branch unmapped at {pc.toNat}"
        let imm26 := (w &&& 0x03ffffff).toNat
        let dispBytes : Int :=
          (if imm26 >= 0x02000000 then (imm26 : Int) - (0x04000000 : Int) else (imm26 : Int)) * 4
        let target := Obj.addSignedAddr pc dispBytes
        symAddrs := symAddrs.set! sym (some (Obj.addSignedAddr target (-addend)))
      | .adrpLo12 bi off1 off2 sym addend =>
        let some b := blkBases[bi]!
          | throwError "gen_f3_ls_interned: adrpLo12 unknown block {bi}"
        let (_, blk) := blksMeta[bi]!
        let some r2 := blk.relocs.find? (·.off == off2)
          | throwError "gen_f3_ls_interned: missing lo12 reloc at blk {bi} off {off2}"
        let some scale := Obj.Interned.lo12Scale? r2.kind
          | throwError "gen_f3_ls_interned: non-lo12 reloc kind at blk {bi} off {off2}"
        let pc1 := b + BitVec.ofNat 64 off1
        let pc2 := b + BitVec.ofNat 64 off2
        let some w1 ← pure (readWord32SegsF3 segsArr pc1)
          | throwError "gen_f3_ls_interned: adrp unmapped at {pc1.toNat}"
        let some w2 ← pure (readWord32SegsF3 segsArr pc2)
          | throwError "gen_f3_ls_interned: lo12 unmapped at {pc2.toNat}"
        let immlo := (w1 >>> 29) &&& 0x3
        let immhi := (w1 >>> 5) &&& 0x7ffff
        let imm21 := ((immhi <<< 2) ||| immlo).toNat
        let pgDisp : Int :=
          (if imm21 >= (1 <<< 20) then (imm21 : Int) - ((1 <<< 21) : Int) else (imm21 : Int)) * 4096
        let targetPage := Obj.addSignedAddr (Obj.pageOf pc1) pgDisp
        let imm12 := ((w2 >>> 10) &&& 0xfff).toNat
        let target := targetPage + BitVec.ofNat 64 (imm12 <<< scale)
        symAddrs := symAddrs.set! sym (some (Obj.addSignedAddr target (-addend)))
      | .dataAbs64 di off sym addend =>
        let d := datasMeta[di]!
        let some dAddr := symAddrs[d.sym]!
          | throwError "gen_f3_ls_interned: dataAbs64 unknown data sym {d.sym}"
        let some target ← pure (readWord64SegsF3 segsArr (dAddr + BitVec.ofNat 64 off))
          | throwError "gen_f3_ls_interned: dataAbs64 unmapped at {dAddr.toNat + off}"
        symAddrs := symAddrs.set! sym (some (Obj.addSignedAddr target (-addend)))

    let mut basesExprArr : Array Expr := #[]
    let mut basesNatArr : Array Nat := #[]
    for bi in [:blkBases.size] do
      let some b := blkBases[bi]!
        | throwError "gen_f3_ls_interned: block {bi} base unresolved"
      basesExprArr := basesExprArr.push (mkBv64LitExprF3 b.toNat)
      basesNatArr := basesNatArr.push b.toNat

    let mut addrsExprArr : Array Expr := #[]
    let mut addrsNatArr : Array Nat := #[]
    for si in [:symAddrs.size] do
      let some a := symAddrs[si]!
        | throwError "gen_f3_ls_interned: symbol {si} ({sortedNames[si]!}) unresolved"
      addrsExprArr := addrsExprArr.push (mkBv64LitExprF3 a.toNat)
      addrsNatArr := addrsNatArr.push a.toNat

    addSafeDefF3 (currNs ++ `f3LsBlockBases) (mkApp (Lean.mkConst ``List [Level.zero]) bv64Ty)
      (mkListExprF3 bv64Ty basesExprArr) (markNoncomp := false)
    addSafeDefF3 (currNs ++ `f3LsSymAddrs) (mkApp (Lean.mkConst ``List [Level.zero]) bv64Ty)
      (mkListExprF3 bv64Ty addrsExprArr) (markNoncomp := false)

    -- Reflect `libsignalSessionMultiLib` into `lsSharedExterns` and `lsInternedMultiLib`.
    let lookupSymIdx (strE : Expr) : MetaM Expr := do
      let s ← evalStrLitF3 strE
      let some idx := symMap[s]?
        | throwError "gen_f3_ls_interned: symbol missing in symMap: {s}"
      return mkNatLit idx

    let internRelocs (relocsListE : Expr) : MetaM Expr := do
      let rElems ← listElemsWhnf relocsListE
      let relocTy := Lean.mkConst ``Arm64.Obj.Interned.Reloc
      let relocMk := Lean.mkConst ``Arm64.Obj.Interned.Reloc.mk
      let mut out : Array Expr := #[]
      for rRaw in rElems do
        let rE ← whnfAllF3 rRaw
        let symIdxE ← lookupSymIdx (rE.getArg! 2)
        out := out.push (mkApp5 relocMk (rE.getArg! 0) (rE.getArg! 1) symIdxE (rE.getArg! 3) (rE.getArg! 4))
      return mkListExprF3 relocTy out

    let libE ← whnfAllF3 (Lean.mkConst ``CryptoVerification.libsignalSessionMultiLib)
    let libNameE := libE.getArg! 0
    let blocksRaw ← listElemsWhnf (libE.getArg! 1)
    let dataRaw ← listElemsWhnf (libE.getArg! 2)
    let exportsRaw ← listElemsWhnf (libE.getArg! 3)
    let exportSymsRaw ← listElemsWhnf (libE.getArg! 4)

    let b0E ← whnfAllF3 blocksRaw[0]!
    let extsRaw ← listElemsWhnf (b0E.getArg! 4)
    let mut sharedExtsArr : Array Expr := #[]
    for extStrE in extsRaw do
      sharedExtsArr := sharedExtsArr.push (← lookupSymIdx extStrE)
    let lsSharedExternsNm := currNs ++ `lsSharedExterns
    addSafeDefF3 lsSharedExternsNm (mkApp (Lean.mkConst ``List [Level.zero]) natTy)
      (mkListExprF3 natTy sharedExtsArr) (markNoncomp := false)
    let sharedExtsConst := Lean.mkConst lsSharedExternsNm

    let prodNatNatTy := mkApp2 (Lean.mkConst ``Prod [Level.zero, Level.zero]) natTy natTy
    let prodNatNatMk := mkApp2 (Lean.mkConst ``Prod.mk [Level.zero, Level.zero]) natTy natTy
    let blkTy := Lean.mkConst ``Arm64.Obj.Interned.Block
    let blkMk := Lean.mkConst ``Arm64.Obj.Interned.Block.mk
    let mut blksArr : Array Expr := #[]
    for bRaw in blocksRaw do
      let bE ← whnfAllF3 bRaw
      let codeE := bE.getArg! 0
      let alignE := bE.getArg! 1
      let symsRaw ← listElemsWhnf (bE.getArg! 2)
      let mut symsArr : Array Expr := #[]
      for sRaw in symsRaw do
        let sE ← whnfAllF3 sRaw
        let symIdxE ← lookupSymIdx (sE.getArg! 2)
        symsArr := symsArr.push (mkApp2 prodNatNatMk symIdxE (sE.getArg! 3))
      let symsInternedE := mkListExprF3 prodNatNatTy symsArr
      let relocsInternedE ← internRelocs (bE.getArg! 3)
      let weakRefsRaw ← listElemsWhnf (bE.getArg! 5)
      let mut weakRefsArr : Array Expr := #[]
      for wStrE in weakRefsRaw do
        weakRefsArr := weakRefsArr.push (← lookupSymIdx wStrE)
      let weakRefsInternedE := mkListExprF3 natTy weakRefsArr
      blksArr := blksArr.push
        (mkApp6 blkMk codeE alignE symsInternedE relocsInternedE sharedExtsConst weakRefsInternedE)

    let dataTy := Lean.mkConst ``Arm64.Obj.Interned.Data
    let dataMk := Lean.mkConst ``Arm64.Obj.Interned.Data.mk
    let mut dataArr : Array Expr := #[]
    for dRaw in dataRaw do
      let dE ← whnfAllF3 dRaw
      let symIdxE ← lookupSymIdx (dE.getArg! 0)
      let alignE := dE.getArg! 1
      let roE := dE.getArg! 2
      let bytesE := dE.getArg! 3
      let ztE := dE.getArg! 4
      let relocsInternedE ← internRelocs (dE.getArg! 5)
      dataArr := dataArr.push (mkApp6 dataMk symIdxE alignE roE bytesE ztE relocsInternedE)

    let mut exportsArr : Array Expr := #[]
    for expStrE in exportsRaw do
      exportsArr := exportsArr.push (← lookupSymIdx expStrE)

    let mut exportSymsArr : Array Expr := #[]
    for esRaw in exportSymsRaw do
      let esE ← whnfAllF3 esRaw
      let kIdxE ← lookupSymIdx (esE.getArg! 2)
      let vIdxE ← lookupSymIdx (esE.getArg! 3)
      exportSymsArr := exportSymsArr.push (mkApp2 prodNatNatMk kIdxE vIdxE)

    let multiLibVal := mkApp6 (Lean.mkConst ``Arm64.Obj.Interned.MultiLib.mk)
      libNameE
      (Lean.mkConst lsNamesNm)
      (mkListExprF3 blkTy blksArr)
      (mkListExprF3 dataTy dataArr)
      (mkListExprF3 natTy exportsArr)
      (mkListExprF3 prodNatNatTy exportSymsArr)
    addSafeDefF3 (currNs ++ `lsInternedMultiLib) (Lean.mkConst ``Arm64.Obj.Interned.MultiLib)
      multiLibVal (markNoncomp := false)

    -- Reflect `cliHookTablePlaced mmpl W` into `lsHookNamesPlaced`, `lsPlacedStubPairs`,
    -- `lsPlacedTagTableLit`, and `lsPlacedCompactLit`.
    let hookNamesStrArr ←
      withLocalDeclD `mmpl (Lean.mkConst ``Arm64.Obj.MultiPlacement) fun mmplE =>
        withLocalDeclD `W (Lean.mkConst ``CryptoVerification.SignalSession.CliHooks) fun wE => do
          let rows ← listElemsWhnf
            (mkApp2 (Lean.mkConst ``CryptoVerification.SignalSession.cliHookTablePlaced) mmplE wE)
          rows.mapM fun row => do
            let p ← whnfAllF3 row
            evalStrLitF3 (p.getArg! 2)
    addSafeDefF3 (currNs ++ `lsHookNamesPlaced)
      (mkApp (Lean.mkConst ``List [Level.zero]) strTy)
      (mkListExprF3 strTy (hookNamesStrArr.map mkStrLit)) (markNoncomp := false)

    let placedPanicsRaw ← listElemsWhnf
      (Lean.mkConst ``CryptoVerification.SignalSession.cliPanicSymbolsPlaced)
    let placedPanics : Array String ← (placedPanicsRaw.mapM evalStrLitF3 : MetaM (Array String))

    let prodStrBvTy := mkApp2 (Lean.mkConst ``Prod [Level.zero, Level.zero]) strTy bv64Ty
    let prodStrBvMk := mkApp2 (Lean.mkConst ``Prod.mk [Level.zero, Level.zero]) strTy bv64Ty
    let optNatTy := mkApp (Lean.mkConst ``Option [Level.zero]) natTy
    let prodBvOptTy := mkApp2 (Lean.mkConst ``Prod [Level.zero, Level.zero]) bv64Ty optNatTy
    let prodBvOptMk := mkApp2 (Lean.mkConst ``Prod.mk [Level.zero, Level.zero]) bv64Ty optNatTy

    let mut placedStubPairsArr : Array Expr := #[]
    let mut tagTableArr : Array Expr := #[]
    let mut compactArr : Array Expr := #[]
    for extStrE in extsRaw do
      let s ← evalStrLitF3 extStrE
      let some idx := symMap[s]?
        | throwError "gen_f3_ls_interned: extern missing in symMap: {s}"
      let aNat := addrsNatArr[idx]!
      let aE := addrsExprArr[idx]!
      placedStubPairsArr := placedStubPairsArr.push (mkApp2 prodStrBvMk namesArr[idx]! aE)
      let tag : Option Nat :=
        if placedPanics.contains s || isPanicSymbolFastMetaF3 s then some 0
        else (hookNamesStrArr.findIdx? (· == s)).map Nat.succ
      tagTableArr := tagTableArr.push (mkApp2 prodBvOptMk aE (mkOptNatExprF3 tag))
      if let some t := tag then
        compactArr := compactArr.push (mkApp2 prodNatNatMk (mkNatLit aNat) (mkNatLit t))

    addSafeDefF3 (currNs ++ `lsPlacedStubPairs)
      (mkApp (Lean.mkConst ``List [Level.zero]) prodStrBvTy)
      (mkListExprF3 prodStrBvTy placedStubPairsArr) (markNoncomp := false)
    addSafeDefF3 (currNs ++ `lsPlacedTagTableLit)
      (mkApp (Lean.mkConst ``List [Level.zero]) prodBvOptTy)
      (mkListExprF3 prodBvOptTy tagTableArr) (markNoncomp := false)
    addSafeDefF3 (currNs ++ `lsPlacedCompactLit)
      (mkApp (Lean.mkConst ``List [Level.zero]) prodNatNatTy)
      (mkListExprF3 prodNatNatTy compactArr) (markNoncomp := false)

    -- Emit `f3DehookedEntries` for the `cliDehookedSymsPlaced` symbols.
    let dehookedRaw ← listElemsWhnf
      (Lean.mkConst ``CryptoVerification.SignalSession.cliDehookedSymsPlaced)
    let prodBvBvTy := mkApp2 (Lean.mkConst ``Prod [Level.zero, Level.zero]) bv64Ty bv64Ty
    let prodBvBvMk := mkApp2 (Lean.mkConst ``Prod.mk [Level.zero, Level.zero]) bv64Ty bv64Ty
    let prodCharBvBvTy := mkApp2 (Lean.mkConst ``Prod [Level.zero, Level.zero]) charListTy prodBvBvTy
    let prodCharBvBvMk := mkApp2 (Lean.mkConst ``Prod.mk [Level.zero, Level.zero]) charListTy prodBvBvTy
    let entryTy := mkApp2 (Lean.mkConst ``Prod [Level.zero, Level.zero]) natTy prodCharBvBvTy
    let entryMk := mkApp2 (Lean.mkConst ``Prod.mk [Level.zero, Level.zero]) natTy prodCharBvBvTy
    let mut dehookedArr : Array Expr := #[]
    for dhRaw in dehookedRaw do
      let s ← evalStrLitF3 dhRaw
      let some idx := symMap[s]?
        | throwError "gen_f3_ls_interned: dehooked sym missing in symMap: {s}"
      let stubE := addrsExprArr[idx]!
      let targetVa ← lookupUniqueMeta s
      let inner1 := mkApp2 prodBvBvMk stubE (mkBv64LitExprF3 targetVa.toNat)
      let inner2 := mkApp2 prodCharBvBvMk (toExpr s.toList) inner1
      dehookedArr := dehookedArr.push (mkApp2 entryMk (mkNatLit idx) inner2)
    addSafeDefF3 (currNs ++ `f3DehookedEntries)
      (mkApp (Lean.mkConst ``List [Level.zero]) entryTy)
      (mkListExprF3 entryTy dehookedArr) (markNoncomp := false)

    -- Emit symbol indices and region bounds.
    let reqIdx (nm : String) : TermElabM Nat := do
      let some idx := symMap[nm]?
        | throwError "gen_f3_ls_interned: required symbol missing: {nm}"
      return idx
    let tokIdx ← reqIdx CryptoVerification.LibsignalSpqrV1.tokenName
    let tokStoIdx ← reqIdx CryptoVerification.LibsignalSpqrV1.tokenStorageName
    let logFilterIdx ← reqIdx CryptoVerification.lsLogFilterSym
    let coinsNextIdx ← reqIdx "libsignal_cli::coins::NEXT.0"
    let coinsLeftIdx ← reqIdx "libsignal_cli::coins::LEFT.0"
    let noShimIdx ← reqIdx CryptoVerification.SignalSession.lsRustNoAllocShimSymCli
    let handleErrIdx ← reqIdx "_RNvNtCs69KKACWg7bl_5alloc7raw_vec12handle_error"

    let (seg1Start, seg1Bs) := segsArr[1]!
    let stockTextStartNat := seg1Start.toNat
    let stockTextLenNat := seg1Bs.size
    let lsCodeHi := seg1Start.toNat + seg1Bs.size

    let mngMly := LibsignalBinary.Heap.Fine.f3MallocngMly
    let mngML := VerifiedLibraries.Mallocng.Proofs.mallocngMultiL
    let mngBases := mngMly.bases.toArray
    let mngAddrs := mngMly.addrs.toArray
    let mngBlks := mngML.blocks.toArray
    let mut mngCodeLo : Nat := (mngBases[0]!).toNat
    let mut mngCodeHi : Nat := 0
    for j in [:mngBlks.size] do
      let bNat := (mngBases[j]!).toNat
      let eNat := bNat + mngBlks[j]!.code.length
      if bNat < mngCodeLo then mngCodeLo := bNat
      if eNat > mngCodeHi then mngCodeHi := eNat

    let mut mngDataLo : Nat := (mngAddrs[(mngML.data.head!).sym]!).toNat
    let mut mngDataHi : Nat := 0
    let mut mngRoLo : Nat := 18446744073709551615
    let mut mngRoHi : Nat := 0
    let libcNat := LibsignalBinary.Heap.Fine.f3StdLayout.libcAddr.toNat
    let mut mngRwLo : Nat := libcNat
    let mut mngRwHi : Nat := libcNat + 104
    for d in mngML.data do
      let aNat := (mngAddrs[d.sym]!).toNat
      let eNat := aNat + d.bytes.length + d.zeroTail
      if aNat < mngDataLo then mngDataLo := aNat
      if eNat > mngDataHi then mngDataHi := eNat
      if d.readOnly then
        if aNat < mngRoLo then mngRoLo := aNat
        if eNat > mngRoHi then mngRoHi := eNat
      else
        if aNat < mngRwLo then mngRwLo := aNat
        if eNat > mngRwHi then mngRwHi := eNat
    if mngRoLo > mngRoHi then
      mngRoLo := mngDataLo
      mngRoHi := mngDataLo

    -- 5-band disjoint RO/RW layout on stock `ld.lld`:
    --   [0, lsRoHi)  ≤  [mngRoLo, mngRoHi)  ≤  [lsRw1Lo, lsRw1Hi)  ≤  [mngRwLo, mngRwHi)  ≤  [lsRw2Lo, lsRw2Hi)
    let mut lsDataHi : Nat := 0
    let mut lsRoHi : Nat := 0
    let mut lsRw1Lo : Nat := 18446744073709551615
    let mut lsRw1Hi : Nat := 0
    let mut lsRw2Lo : Nat := 18446744073709551615
    let mut lsRw2Hi : Nat := 0
    for d in datasMeta do
      let aNat := addrsNatArr[d.sym]!
      let endNat := aNat + d.bytes.length + d.zeroTail
      if endNat > lsDataHi then lsDataHi := endNat
      if aNat < mngRoLo then
        if endNat > lsRoHi then lsRoHi := endNat
      else if aNat < mngRwLo then
        if aNat < lsRw1Lo then lsRw1Lo := aNat
        if endNat > lsRw1Hi then lsRw1Hi := endNat
      else
        if aNat < lsRw2Lo then lsRw2Lo := aNat
        if endNat > lsRw2Hi then lsRw2Hi := endNat
    if lsRw1Lo > lsRw1Hi then
      lsRw1Lo := mngRoHi
      lsRw1Hi := mngRoHi
    if lsRw2Lo > lsRw2Hi then
      lsRw2Lo := mngRwHi
      lsRw2Hi := mngRwHi

    let emitNat (nm : Name) (v : Nat) : TermElabM Unit :=
      addSafeDefF3 (currNs ++ nm) natTy (mkNatLit v) (markNoncomp := false)

    emitNat `f3LsBlocksLen blksMeta.size
    emitNat `f3LsNamesLen sortedNames.size
    emitNat `f3TokenIdx tokIdx
    emitNat `f3TokenStorageIdx tokStoIdx
    emitNat `f3LogFilterIdx logFilterIdx
    emitNat `f3CoinsNextIdx coinsNextIdx
    emitNat `f3CoinsLeftIdx coinsLeftIdx
    emitNat `f3NoShimIdx noShimIdx
    emitNat `f3HandleErrorIdx handleErrIdx
    emitNat `stockTextStartNat stockTextStartNat
    emitNat `stockTextLenNat stockTextLenNat
    emitNat `f3LsCodeHi lsCodeHi
    emitNat `f3MngCodeLo mngCodeLo
    emitNat `f3MngCodeHi mngCodeHi
    emitNat `f3LsDataHi lsDataHi
    emitNat `f3LsRoHi lsRoHi
    emitNat `f3LsRw1Lo lsRw1Lo
    emitNat `f3LsRw1Hi lsRw1Hi
    emitNat `f3LsRw2Lo lsRw2Lo
    emitNat `f3LsRw2Hi lsRw2Hi
    emitNat `f3MngDataLo mngDataLo
    emitNat `f3MngDataHi mngDataHi
    emitNat `f3MngRoLo mngRoLo
    emitNat `f3MngRoHi mngRoHi
    emitNat `f3MngRwLo mngRwLo
    emitNat `f3MngRwHi mngRwHi


gen_f3_ls_interned

end MetaGenF3LsInterned

end LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfCodeMatchesData
