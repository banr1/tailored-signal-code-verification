/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public meta import Lean
public meta import Arm64
public meta import LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfMultiHelpers
public meta import ProofLib.Placed.Multi
public meta import ProofLib.ProgramReflection
public meta import GeneratedLean.LibsignalSessionPlacedObj
public meta import GeneratedLean.BugInjectionMutantImage
public import Arm64
public import ProofLib.Placed.Multi

/-!
# Mutant Placement Elaborator

Defines `gen_mutant_ls_placement`, which reflects `CryptoVerification.libsignalSessionMultiLib` and
`CryptoVerification.BugInjection.mutantCliElfImage` (under `CV_BUG_INJECTION=<bug>`) to synthesize
`lsNames`, `lsNameChars`, `mutantBlocksLen`, `f3LsBlockBases`, and `f3LsSymAddrs` in the caller's
namespace by inverting ELF symbol addresses and relocated instructions.
-/

@[expose] public section

set_option autoImplicit false

namespace Symbolic.BugInjection.Disproofs.Impl.MutantLink.GenPlacement

open Lean Meta Elab Term Command ProofLib.ProgramReflection
open Arm64 Arm64.Obj Arm64.Obj.Interned

meta def whnfAllMut (e : Expr) : MetaM Expr :=
  withTransparency .all (whnf e)

meta def evalStrLitMut (e : Expr) : MetaM String := do
  if let .lit (.strVal s) := e then return s
  let r ← whnfAllMut e
  if let .lit (.strVal s) := r then return s
  let r2 ← withTransparency .all (reduce e)
  if let .lit (.strVal s) := r2 then return s
  throwError "gen_mutant_ls_placement: expected String literal, got {r2}"

meta def evalNatExprMut (e : Expr) : MetaM Nat := do
  if let .lit (.natVal n) := e then return n
  if let some n := e.rawNatLit? then return n
  let r ← whnfAllMut e
  if let .lit (.natVal n) := r then return n
  if let some n := r.rawNatLit? then return n
  let r2 ← withTransparency .all (reduce e)
  if let .lit (.natVal n) := r2 then return n
  if let some n := r2.rawNatLit? then return n
  throwError "gen_mutant_ls_placement: expected Nat literal, got {r2}"

meta def evalBv64ToNatMut (e : Expr) : MetaM Nat :=
  evalNatExprMut (mkApp2 (Lean.mkConst ``BitVec.toNat) (mkNatLit 64) e)

meta def evalBv8ToUInt8Mut (e : Expr) : MetaM UInt8 := do
  let n ← evalNatExprMut (mkApp2 (Lean.mkConst ``BitVec.toNat) (mkNatLit 8) e)
  return UInt8.ofNat n

meta def readBv8ListIterMut (listE : Expr) : MetaM ByteArray := do
  let mut cur := listE
  let mut out := ByteArray.emptyWithCapacity 65536
  let mut done := false
  while !done do
    if cur.isAppOfArity ``List.cons 3 then
      out := out.push (← evalBv8ToUInt8Mut (cur.getArg! 1))
      cur := cur.getArg! 2
    else if cur.isAppOfArity ``List.nil 1 then
      done := true
    else
      cur ← whnfAllMut cur
      if cur.isAppOfArity ``List.cons 3 then
        out := out.push (← evalBv8ToUInt8Mut (cur.getArg! 1))
        cur := cur.getArg! 2
      else if cur.isAppOfArity ``List.nil 1 then
        done := true
      else
        throwError "gen_mutant_ls_placement: unexpected byte list spine head"
  return out

meta def mkListExprMut (elemTy : Expr) (elems : Array Expr) : Expr :=
  let nilE := mkApp (Lean.mkConst ``List.nil [Level.zero]) elemTy
  let consFn := mkApp (Lean.mkConst ``List.cons [Level.zero]) elemTy
  elems.foldr (fun x acc => mkApp2 consFn x acc) nilE

meta def mkBv64LitExprMut (n : Nat) : Expr :=
  mkApp2 (Lean.mkConst ``BitVec.ofNat) (mkNatLit 64) (mkNatLit n)

meta def addCompiledDefMut (nm : Name) (ty val : Expr) : TermElabM Unit := do
  Lean.withExporting (isExporting := true) do
    withOptions (fun o => maxRecDepth.set o 2000000) do
      let env ← getEnv
      addAndCompile <| Declaration.defnDecl {
        name := nm
        levelParams := []
        type := ty
        value := val
        hints := .regular (getMaxHeight env val + 1)
        safety := .safe
      }

meta def addNoncompDefMutP (nm : Name) (ty val : Expr) : TermElabM Unit := do
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
    modifyEnv (addNoncomputable · nm)

meta def wordAtArrMut (code : Array (BitVec 8)) (off : Nat) : BitVec 32 :=
  if off + 4 ≤ code.size then
    code[off + 3]! ++ code[off + 2]! ++ code[off + 1]! ++ code[off]!
  else 0#32

meta def buildRelocInvStepsMut (symMap : Std.HashMap String Nat) :
    TermElabM (Array Obj.Interned.InvStep × Array (Array (BitVec 8) × Obj.Interned.Block) ×
      Array Obj.Interned.Data) := do
  let lib := CryptoVerification.libsignalSessionMultiLib
  let getSym (s : String) : TermElabM Nat := do
    let some idx := symMap[s]?
      | throwError "gen_mutant_ls_placement: symbol not found: {s}"
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
            let w := wordAtArrMut codeArr off
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
          let w := wordAtArrMut codeArr off
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

meta def readByteSegsMut (segs : Array (BitVec 64 × ByteArray)) (va : BitVec 64) :
    Option UInt8 := Id.run do
  for (start, bs) in segs do
    let off := (va - start).toNat
    if off < bs.size then
      return some (bs.get! off)
  return none

meta def readWord32SegsMut (segs : Array (BitVec 64 × ByteArray)) (va : BitVec 64) :
    Option UInt32 := do
  let b0 ← readByteSegsMut segs va
  let b1 ← readByteSegsMut segs (va + BitVec.ofNat 64 1)
  let b2 ← readByteSegsMut segs (va + BitVec.ofNat 64 2)
  let b3 ← readByteSegsMut segs (va + BitVec.ofNat 64 3)
  return b0.toUInt32 ||| (b1.toUInt32 <<< 8) ||| (b2.toUInt32 <<< 16) ||| (b3.toUInt32 <<< 24)

meta def readWord64SegsMut (segs : Array (BitVec 64 × ByteArray)) (va : BitVec 64) :
    Option (BitVec 64) := do
  let mut acc : Nat := 0
  for k in [:8] do
    let bk ← readByteSegsMut segs (va + BitVec.ofNat 64 k)
    acc := acc ||| (bk.toNat <<< (8 * k))
  return BitVec.ofNat 64 acc

meta def collectSortedLsNames : Array String := Id.run do
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
  return nameSet.toArray.qsort (· < ·)

syntax "gen_mutant_ls_placement" : command

elab_rules : command
  | `(command| gen_mutant_ls_placement) => liftTermElabM do
    let currNs ← getCurrNamespace
    let strTy := Lean.mkConst ``String
    let natTy := Lean.mkConst ``Nat
    let charTy := Lean.mkConst ``Char
    let charListTy := mkApp (Lean.mkConst ``List [Level.zero]) charTy
    let bv64Ty := mkApp (Lean.mkConst ``BitVec) (mkNatLit 64)

    let lib := CryptoVerification.libsignalSessionMultiLib
    let sortedNames := collectSortedLsNames
    let mut symMap : Std.HashMap String Nat := {}
    let mut namesArr : Array Expr := #[]
    let mut nameCharsArr : Array Expr := #[]
    for idx in [:sortedNames.size] do
      let s := sortedNames[idx]!
      symMap := symMap.insert s idx
      namesArr := namesArr.push (mkStrLit s)
      nameCharsArr := nameCharsArr.push (toExpr s.toList)

    addCompiledDefMut (currNs ++ `lsNames) (mkApp (Lean.mkConst ``List [Level.zero]) strTy)
      (mkListExprMut strTy namesArr)
    addNoncompDefMutP (currNs ++ `lsNameChars) (mkApp (Lean.mkConst ``List [Level.zero]) charListTy)
      (mkListExprMut charListTy nameCharsArr)

    let (invSteps, blksMeta, datasMeta) ← buildRelocInvStepsMut symMap
    addCompiledDefMut (currNs ++ `mutantBlocksLen) natTy (mkNatLit blksMeta.size)

    let mutElfConst := Lean.mkConst ``CryptoVerification.BugInjection.mutantCliElfImage
    let imgSymsRaw ← listElemsWhnf (mkApp (Lean.mkConst ``Arm64.Process.ElfImage.symbols) mutElfConst)
    let mut symTabAll : Std.HashMap String (Array (BitVec 64)) := {}
    for pairRaw in imgSymsRaw do
      let pairE ← whnfAllMut pairRaw
      let s ← evalStrLitMut (pairE.getArg! 2)
      let vNat ← evalBv64ToNatMut (pairE.getArg! 3)
      symTabAll := symTabAll.insert s ((symTabAll.getD s #[]).push (BitVec.ofNat 64 vNat))

    let lookupUniqueMeta (s : String) : TermElabM (BitVec 64) := do
      match symTabAll[s]? with
      | some #[va] => return va
      | some arr =>
        throwError "gen_mutant_ls_placement: non-unique symbol {s} in mutantCliElfImage ({arr.size} hits)"
      | none =>
        throwError "gen_mutant_ls_placement: missing symbol {s} in mutantCliElfImage"

    let segsRaw ← listElemsWhnf (mkApp (Lean.mkConst ``Arm64.Process.ElfImage.segments) mutElfConst)
    let mut segsArr : Array (BitVec 64 × ByteArray) := #[]
    for segRaw in segsRaw do
      let segE ← whnfAllMut segRaw
      let startNat ← evalBv64ToNatMut (segE.getArg! 0)
      let bs ← readBv8ListIterMut (segE.getArg! 2)
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
          | throwError "gen_mutant_ls_placement: symOfBlock unknown block {bi}"
        symAddrs := symAddrs.set! sym (some (b + BitVec.ofNat 64 off))
      | .blockOfSym sym bi off =>
        let some a := symAddrs[sym]!
          | throwError "gen_mutant_ls_placement: blockOfSym unknown sym {sym}"
        blkBases := blkBases.set! bi (some (a - BitVec.ofNat 64 off))
      | .branch bi off sym addend =>
        let some b := blkBases[bi]!
          | throwError "gen_mutant_ls_placement: branch unknown block {bi}"
        let pc := b + BitVec.ofNat 64 off
        let some w ← pure (readWord32SegsMut segsArr pc)
          | throwError "gen_mutant_ls_placement: branch unmapped at {pc.toNat}"
        let imm26 := (w &&& 0x03ffffff).toNat
        let dispBytes : Int :=
          (if imm26 >= 0x02000000 then (imm26 : Int) - (0x04000000 : Int) else (imm26 : Int)) * 4
        let target := Obj.addSignedAddr pc dispBytes
        symAddrs := symAddrs.set! sym (some (Obj.addSignedAddr target (-addend)))
      | .adrpLo12 bi off1 off2 sym addend =>
        let some b := blkBases[bi]!
          | throwError "gen_mutant_ls_placement: adrpLo12 unknown block {bi}"
        let (_, blk) := blksMeta[bi]!
        let some r2 := blk.relocs.find? (·.off == off2)
          | throwError "gen_mutant_ls_placement: missing lo12 reloc at blk {bi} off {off2}"
        let some scale := Obj.Interned.lo12Scale? r2.kind
          | throwError "gen_mutant_ls_placement: non-lo12 reloc kind at blk {bi} off {off2}"
        let pc1 := b + BitVec.ofNat 64 off1
        let pc2 := b + BitVec.ofNat 64 off2
        let some w1 ← pure (readWord32SegsMut segsArr pc1)
          | throwError "gen_mutant_ls_placement: adrp unmapped at {pc1.toNat}"
        let some w2 ← pure (readWord32SegsMut segsArr pc2)
          | throwError "gen_mutant_ls_placement: lo12 unmapped at {pc2.toNat}"
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
          | throwError "gen_mutant_ls_placement: dataAbs64 unknown data sym {d.sym}"
        let some target ← pure (readWord64SegsMut segsArr (dAddr + BitVec.ofNat 64 off))
          | throwError "gen_mutant_ls_placement: dataAbs64 unmapped at {dAddr.toNat + off}"
        symAddrs := symAddrs.set! sym (some (Obj.addSignedAddr target (-addend)))

    let mut basesExprArr : Array Expr := #[]
    for bi in [:blkBases.size] do
      let some b := blkBases[bi]!
        | throwError "gen_mutant_ls_placement: block {bi} base unresolved"
      basesExprArr := basesExprArr.push (mkBv64LitExprMut b.toNat)

    let mut addrsExprArr : Array Expr := #[]
    for si in [:symAddrs.size] do
      let some a := symAddrs[si]!
        | throwError "gen_mutant_ls_placement: symbol {si} ({sortedNames[si]!}) unresolved"
      addrsExprArr := addrsExprArr.push (mkBv64LitExprMut a.toNat)

    addCompiledDefMut (currNs ++ `f3LsBlockBases) (mkApp (Lean.mkConst ``List [Level.zero]) bv64Ty)
      (mkListExprMut bv64Ty basesExprArr)
    addCompiledDefMut (currNs ++ `f3LsSymAddrs) (mkApp (Lean.mkConst ``List [Level.zero]) bv64Ty)
      (mkListExprMut bv64Ty addrsExprArr)

end Symbolic.BugInjection.Disproofs.Impl.MutantLink.GenPlacement
