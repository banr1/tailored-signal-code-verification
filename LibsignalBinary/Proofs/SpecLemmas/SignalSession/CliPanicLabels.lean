/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Specifications.SignalSession.CliLabels
public import ProofLib.Placed.LabelsCoverage
public import ProofLib.Placed.LabelsInterned
public import ProofLib.ProgramReflection
public meta import Lean
public meta import Arm64
public meta import ProofLib.ProgramReflection
public meta import ProofLib.Placed.LabelsCoverage
public meta import ProofLib.Placed.LabelsInterned
public meta import GeneratedLean.LibsignalSessionExtractedObj
public meta import GeneratedLean.LibsignalSessionPlacedObj
public meta import LibsignalBinary.Specifications.SignalSession.CliLabels

@[expose] public section

set_option autoImplicit false

/-!
# Panic Label Soundness and Completeness (`CliPanicLabelsSound`)

**Checked by Lean.** Proves `cliPanicLabelsSound : CliPanicLabelsSound` and
`cliPanicLabelsComplete` via `Obj.checkGateALabelsB` and `Obj.gateALabels_of_check`, and certifies
that `Vec::remove::assert_failed` (`cliPanicExtraRawSym`) is the unique extern in
`cliPanicSymbolsPlaced` outside `Rust.isPanicSymbol`.
-/

namespace LibsignalBinary.Proofs.SpecLemmas.SignalSession.CliPanicLabels

open Arm64
open ProofLib.ProgramReflection (IdxTree)
open CryptoVerification.SignalSession (
  CliPanicLabelsSound
  cliLinkObjs
  cliPanicExtraDemangled
  cliPanicSymbolsPlaced
  isCliPanicSymbolPlaced
  libsignalSessionLib
)

section MetaGenP2b

open Lean Elab Command Meta

private meta def p2bWhnfCtor (ctor : Name) (arity : Nat) (e : Expr) : MetaM Expr := do
  let e' ← whnf e
  if e'.isAppOfArity ctor arity then return e'
  let eAll ← withTransparency .all (whnf e)
  if eAll.isAppOfArity ctor arity then return eAll
  throwError "p2bWhnfCtor: expected {ctor}/{arity}, got {eAll}"

private meta partial def p2bListElems (e : Expr) : MetaM (Array Expr) := do
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
        throwError "p2bListElems: expected List, got {cAll}"
  return out

private meta def p2bStrVal (e : Expr) : MetaM String := do
  if let .lit (.strVal s) := e then return s
  let e' ← withTransparency .all (whnf e)
  if let .lit (.strVal s) := e' then return s
  throwError "p2bStrVal: expected string literal, got {e'}"

private meta def p2bCharCodeLt : List Char → List Char → Bool
  | [], [] => false
  | [], _ :: _ => true
  | _ :: _, [] => false
  | a :: as, b :: bs =>
    if a.toNat < b.toNat then true
    else if b.toNat < a.toNat then false
    else p2bCharCodeLt as bs

private meta def p2bMkList (ty : Expr) (xs : Array Expr) : Expr :=
  xs.foldr (fun x acc => mkApp3 (Lean.mkConst ``List.cons [Level.zero]) ty x acc)
    (mkApp (Lean.mkConst ``List.nil [Level.zero]) ty)

private meta def p2bDecodeSymBindKey (e : Expr) : MetaM String := do
  let c ← withTransparency .all (whnf e)
  if c.isConstOf ``Obj.SymBind.local then return "local"
  if c.isConstOf ``Obj.SymBind.global then return "global"
  if c.isConstOf ``Obj.SymBind.weak then return "weak"
  return "other"

private meta def p2bDecodeSymSecKey (e : Expr) : MetaM String := do
  let c ← withTransparency .all (whnf e)
  if c.isConstOf ``Obj.SymSec.undef then return "undef"
  if c.isAppOfArity ``Obj.SymSec.sec 1 then
    let n ← withTransparency .all (whnf (c.getArg! 0))
    return s!"sec:{n}"
  return "other"

elab "gen_p2b_interned" : command => do
  let currNs ← getCurrNamespace
  let _ ← liftTermElabM do
    let objEs ← p2bListElems (Lean.mkConst ``CryptoVerification.libsignalSessionExtractedObjs)
    let libC ← p2bWhnfCtor ``Obj.MultiPlacedLib.mk 5
      (Lean.mkConst ``CryptoVerification.libsignalSessionMultiLib)
    let blkEs ← p2bListElems (libC.getArg! 1)
    let b0C ← p2bWhnfCtor ``Obj.CodeBlock.mk 6 blkEs[0]!
    let extEs ← p2bListElems (b0C.getArg! 4)
    let extStrs ← (extEs.mapM p2bStrVal : MetaM (Array String))
    let panicEs ← p2bListElems (Lean.mkConst ``CryptoVerification.SignalSession.cliPanicSymbolsPlaced)
    let panicStrs ← (panicEs.mapM p2bStrVal : MetaM (Array String))

    let exactPanicEs ← p2bListElems (Lean.mkConst ``Obj.rustPanicExactNames)
    let exactPanicStrs ← (exactPanicEs.mapM p2bStrVal : MetaM (Array String))

    let mut panicRawSet : Std.HashSet String := Std.HashSet.emptyWithCapacity 64
    for s in panicStrs do panicRawSet := panicRawSet.insert s

    let mut targetRawSet : Std.HashSet String := Std.HashSet.emptyWithCapacity 256
    for s in extStrs do targetRawSet := targetRawSet.insert s
    for s in panicStrs do targetRawSet := targetRawSet.insert s

    let mut nameSet : Std.HashSet String := Std.HashSet.emptyWithCapacity 8192
    nameSet := nameSet.insert ""
    for s in extStrs do nameSet := nameSet.insert s
    for s in panicStrs do nameSet := nameSet.insert s

    let mut rawObjSymEs : Array (Array (String × String × Expr)) := #[]
    for oE in objEs do
      let oC ← p2bWhnfCtor ``Obj.ExtractedObj.mk 4 oE
      let symEs ← p2bListElems (oC.getArg! 2)
      let mut arr : Array (String × String × Expr) := Array.mkEmpty symEs.size
      for syE in symEs do
        let syC ← p2bWhnfCtor ``Obj.RawSym.mk 7 syE
        let rn ← p2bStrVal (syC.getArg! 0)
        let dn ← p2bStrVal (syC.getArg! 1)
        nameSet := nameSet.insert rn
        nameSet := nameSet.insert dn
        arr := arr.push (rn, dn, syC)
      rawObjSymEs := rawObjSymEs.push arr

    let sortedNames := nameSet.toArray.qsort (fun a b => p2bCharCodeLt a.toList b.toList)
    let N := sortedNames.size
    let mut idMap : Std.HashMap String Nat := Std.HashMap.emptyWithCapacity (N * 2)
    for idx in [:N] do
      idMap := idMap.insert sortedNames[idx]! idx
    let idOf (s : String) : Nat := idMap.getD s 0

    let mut targetIdSet : Std.HashSet Nat := Std.HashSet.emptyWithCapacity 256
    for s in extStrs do targetIdSet := targetIdSet.insert (idOf s)
    for s in panicStrs do targetIdSet := targetIdSet.insert (idOf s)

    let strTy := Lean.mkConst ``String
    let charListTy := mkApp (Lean.mkConst ``List [Level.zero]) (Lean.mkConst ``Char)
    let natTy := Lean.mkConst ``Nat
    let natListTy := mkApp (Lean.mkConst ``List [Level.zero]) natTy
    let boolTy := Lean.mkConst ``Bool
    let trueE := Lean.mkConst ``Bool.true
    let falseE := Lean.mkConst ``Bool.false
    let iSymTy := Lean.mkConst ``Obj.LabelsInterned.ISym
    let rawSymTy := Lean.mkConst ``Obj.RawSym
    let rawRelocTy := Lean.mkConst ``Obj.RawReloc
    let rawSecTy := Lean.mkConst ``Obj.RawSec
    let mkTreeTy (t : Expr) := mkApp (Lean.mkConst ``IdxTree [Level.zero]) t
    let iSymTreeTy := mkTreeTy iSymTy
    let natPairTy := mkApp2 (Lean.mkConst ``Prod [Level.zero, Level.zero]) natTy natTy
    let summaryWitTy := mkApp2 (Lean.mkConst ``Prod [Level.zero, Level.zero]) iSymTy natPairTy

    let namesTreeVal := ProofLib.ProgramReflection.mkIdxTreeExpr Level.zero strTy
      (sortedNames.map mkStrLit)
    let charsTreeVal := ProofLib.ProgramReflection.mkIdxTreeExpr Level.zero charListTy
      (sortedNames.map ProofLib.ProgramReflection.mkStrCharsExpr)

    let mut isTargetArr : Array Expr := Array.mkEmpty N
    for idx in [:N] do
      isTargetArr := isTargetArr.push (if targetIdSet.contains idx then trueE else falseE)
    let isTargetTreeVal := ProofLib.ProgramReflection.mkIdxTreeExpr Level.zero boolTy isTargetArr

    let zeroLit := mkRawNatLit 0
    let mut objSymTrees : Array Expr := Array.mkEmpty rawObjSymEs.size
    let mut seenSummary : Std.HashSet String := Std.HashSet.emptyWithCapacity 256
    let mut panicItems : Array (String × Nat × String × Expr × Expr × Nat × Nat) := #[]
    let mut otherItems : Array (String × Nat × String × Expr × Expr × Nat × Nat) := #[]

    for oi in [:rawObjSymEs.size] do
      let syms := rawObjSymEs[oi]!
      let mut isyms : Array Expr := Array.mkEmpty syms.size
      for si in [:syms.size] do
        let (rn, dn, syC) := syms[si]!
        let rid := idOf rn
        let nid := idOf dn
        let isyE := mkAppN (Lean.mkConst ``Obj.LabelsInterned.ISym.mk) #[
          mkRawNatLit rid,
          mkRawNatLit nid,
          zeroLit,
          syC.getArg! 6,
          syC.getArg! 5,
          syC.getArg! 2,
          syC.getArg! 3,
          syC.getArg! 4
        ]
        isyms := isyms.push isyE
        if targetRawSet.contains rn then
          let bk ← p2bDecodeSymBindKey (syC.getArg! 6)
          if bk != "local" then
            let sk ← p2bDecodeSymSecKey (syC.getArg! 2)
            let key := s!"{rid}:{nid}:{sk}:{bk}"
            if !seenSummary.contains key then
              seenSummary := seenSummary.insert key
              if panicRawSet.contains rn then
                panicItems := panicItems.push (rn, rid, sk, isyE, syC, oi, si)
              else
                otherItems := otherItems.push (rn, rid, sk, isyE, syC, oi, si)
      objSymTrees := objSymTrees.push
        (ProofLib.ProgramReflection.mkIdxTreeExpr Level.zero iSymTy isyms)

    let allItems := panicItems ++ otherItems
    let numPanicSummary := panicItems.size
    let mut summaryISyms : Array Expr := Array.mkEmpty allItems.size
    let mut summaryRawSyms : Array Expr := Array.mkEmpty allItems.size
    let mut panicSummaryISyms : Array Expr := Array.mkEmpty numPanicSummary
    let mut panicSummaryWits : Array Expr := Array.mkEmpty numPanicSummary
    let mut panicSummaryRawSyms : Array Expr := Array.mkEmpty numPanicSummary
    let mut bucketsByRaw : Std.HashMap Nat (Array Nat) := Std.HashMap.emptyWithCapacity 256
    let mut undefIdxByRaw : Std.HashMap String Nat := Std.HashMap.emptyWithCapacity 256

    for sIdx in [:allItems.size] do
      let (rn, rid, sk, isyE, syC, oi, si) := allItems[sIdx]!
      summaryISyms := summaryISyms.push isyE
      summaryRawSyms := summaryRawSyms.push syC
      if sIdx < numPanicSummary then
        panicSummaryISyms := panicSummaryISyms.push isyE
        panicSummaryRawSyms := panicSummaryRawSyms.push syC
        let pair2 := mkApp4 (Lean.mkConst ``Prod.mk [Level.zero, Level.zero])
          natTy natTy (mkRawNatLit oi) (mkRawNatLit si)
        let witE := mkApp4 (Lean.mkConst ``Prod.mk [Level.zero, Level.zero])
          iSymTy natPairTy isyE pair2
        panicSummaryWits := panicSummaryWits.push witE
      let prev := bucketsByRaw.getD rid #[]
      bucketsByRaw := bucketsByRaw.insert rid (prev.push sIdx)
      if sk == "undef" && !undefIdxByRaw.contains rn then
        undefIdxByRaw := undefIdxByRaw.insert rn sIdx

    let objSymsTreeVal :=
      ProofLib.ProgramReflection.mkIdxTreeExpr Level.zero iSymTreeTy objSymTrees
    let summaryTreeVal :=
      ProofLib.ProgramReflection.mkIdxTreeExpr Level.zero iSymTy summaryISyms
    let panicSummaryTreeVal :=
      ProofLib.ProgramReflection.mkIdxTreeExpr Level.zero iSymTy panicSummaryISyms

    let emptyNatList := mkApp (Lean.mkConst ``List.nil [Level.zero]) natTy
    let mut bucketArr : Array Expr := Array.mkEmpty N
    for idx in [:N] do
      match bucketsByRaw[idx]? with
      | none => bucketArr := bucketArr.push emptyNatList
      | some ks => bucketArr := bucketArr.push (p2bMkList natTy (ks.map mkRawNatLit))
    let targetBucketTreeVal :=
      ProofLib.ProgramReflection.mkIdxTreeExpr Level.zero natListTy bucketArr

    let someCall26 := mkApp2 (Lean.mkConst ``Option.some [Level.zero])
      (Lean.mkConst ``Obj.RelocKind) (Lean.mkConst ``Obj.RelocKind.call26)
    let zeroInt := mkIntLit 0
    let mut summaryRelocs : Array Expr := Array.mkEmpty panicStrs.size
    for ps in panicStrs do
      let some symIdx := undefIdxByRaw[ps]?
        | throwError "gen_p2b_interned: missing .undef symbol for panic {ps}"
      if symIdx >= numPanicSummary then
        throwError "gen_p2b_interned: panic .undef index {symIdx} >= {numPanicSummary}"
      let rrE := mkAppN (Lean.mkConst ``Obj.RawReloc.mk) #[
        zeroLit, someCall26, mkRawNatLit symIdx, zeroInt
      ]
      summaryRelocs := summaryRelocs.push rrE

    let bv8Ty := mkApp (Lean.mkConst ``BitVec) (mkRawNatLit 8)
    let emptyBytes := mkApp (Lean.mkConst ``List.nil [Level.zero]) bv8Ty
    let secE := mkAppN (Lean.mkConst ``Obj.RawSec.mk) #[
      mkStrLit ".text",
      emptyBytes,
      zeroLit,
      mkRawNatLit 4,
      trueE,
      trueE,
      falseE,
      falseE,
      p2bMkList rawRelocTy summaryRelocs
    ]
    let emptyGroups := mkApp (Lean.mkConst ``List.nil [Level.zero]) (Lean.mkConst ``Obj.RawGroup)
    let panicSummaryObjVal := mkAppN (Lean.mkConst ``Obj.ExtractedObj.mk) #[
      mkStrLit "panic_summary.o",
      p2bMkList rawSecTy #[secE],
      p2bMkList rawSymTy panicSummaryRawSyms,
      emptyGroups
    ]

    let addD (nm : Name) (ty val : Expr) : MetaM Unit := do
      let env ← getEnv
      addDecl (.defnDecl {
        name := currNs ++ nm
        levelParams := []
        type := ty
        value := val
        hints := .regular (getMaxHeight env val + 1)
        safety := .safe
      })
      modifyEnv (addNoncomputable · (currNs ++ nm))

    addD `p2bNumNames natTy (mkRawNatLit N)
    addD `p2bNumBlocks natTy (mkRawNatLit blkEs.size)
    addD `p2bNamesTree (mkTreeTy strTy) namesTreeVal
    addD `p2bCharsTree (mkTreeTy charListTy) charsTreeVal
    addD `p2bIsTargetTree (mkTreeTy boolTy) isTargetTreeVal
    addD `p2bTargetBucketTree (mkTreeTy natListTy) targetBucketTreeVal
    addD `p2bObjSymsTree (mkTreeTy iSymTreeTy) objSymsTreeVal
    addD `p2bSummaryTree iSymTreeTy summaryTreeVal
    addD `p2bAllSummarySyms (mkApp (Lean.mkConst ``List [Level.zero]) rawSymTy)
      (p2bMkList rawSymTy summaryRawSyms)
    addD `p2bPanicSummaryTree iSymTreeTy panicSummaryTreeVal
    addD `p2bPanicSummaryWits (mkApp (Lean.mkConst ``List [Level.zero]) summaryWitTy)
      (p2bMkList summaryWitTy panicSummaryWits)
    addD `p2bPanicSummaryObj (Lean.mkConst ``Obj.ExtractedObj) panicSummaryObjVal
    addD `p2bExternIds natListTy
      (p2bMkList natTy (extStrs.map (mkRawNatLit ∘ idOf)))
    addD `p2bPanicIds natListTy
      (p2bMkList natTy (panicStrs.map (mkRawNatLit ∘ idOf)))
    let charListListTy := mkApp (Lean.mkConst ``List [Level.zero]) charListTy
    addD `p2bPanicChars charListListTy
      (p2bMkList charListTy (panicStrs.map ProofLib.ProgramReflection.mkStrCharsExpr))
    addD `p2bRustExactPanicChars charListListTy
      (p2bMkList charListTy (exactPanicStrs.map ProofLib.ProgramReflection.mkStrCharsExpr))
    addD `p2bExtraRawChars charListTy
      (ProofLib.ProgramReflection.mkStrCharsExpr
        "_RNvNvMs_NtCs69KKACWg7bl_5alloc3vecINtB6_3VecppE6remove13assert_failed")
    addD `p2bExtraDemangledChars charListTy
      (ProofLib.ProgramReflection.mkStrCharsExpr
        "<alloc::vec::Vec<_, _>>::remove::assert_failed")
    addD `cliAllExterns (mkApp (Lean.mkConst ``List [Level.zero]) strTy)
      (p2bMkList strTy (extStrs.map mkStrLit))
    return ()

gen_p2b_interned

end MetaGenP2b

private theorem p2b_names_sz : p2bNamesTree.size? = some p2bNumNames := by
  open ProofLib.ProgramReflection in rfl_kernel

private theorem p2b_names_eq :
    p2bNamesTree.toList = p2bCharsTree.toList.map String.ofList := by
  open ProofLib.ProgramReflection in rfl_kernel

private theorem p2b_names_nodup :
    Obj.Interned.namesNodup p2bCharsTree.toList = true := by
  open ProofLib.ProgramReflection in rfl_kernel

private theorem p2b_objs_syms_eq :
    cliLinkObjs.map Obj.ExtractedObj.symbols =
      p2bObjSymsTree.toList.map
        (fun t => t.toList.map (Obj.LabelsInterned.ISym.toRawSym p2bNamesTree)) := by
  open ProofLib.ProgramReflection in rfl_kernel

private theorem p2b_summary_syms_eq :
    p2bAllSummarySyms =
      p2bSummaryTree.toList.map (Obj.LabelsInterned.ISym.toRawSym p2bNamesTree) := by
  open ProofLib.ProgramReflection in rfl_kernel

private theorem p2b_panic_summary_syms_eq :
    p2bPanicSummaryObj.symbols =
      p2bPanicSummaryTree.toList.map (Obj.LabelsInterned.ISym.toRawSym p2bNamesTree) := by
  open ProofLib.ProgramReflection in rfl_kernel

private theorem p2b_panic_summary_wits_eq :
    p2bPanicSummaryTree.toList = p2bPanicSummaryWits.map Prod.fst := by
  open ProofLib.ProgramReflection in rfl_kernel

private theorem p2b_externs_eq :
    cliAllExterns = p2bExternIds.map (Obj.LabelsInterned.symAt p2bNamesTree) := by
  open ProofLib.ProgramReflection in rfl_kernel

private theorem p2b_panics_eq :
    cliPanicSymbolsPlaced = p2bPanicIds.map (Obj.LabelsInterned.symAt p2bNamesTree) := by
  open ProofLib.ProgramReflection in rfl_kernel

private theorem p2b_blocks_externs_eq :
    libsignalSessionLib.blocks.map Obj.CodeBlock.externs =
      List.replicate p2bNumBlocks cliAllExterns := by
  open ProofLib.ProgramReflection in rfl_kernel

private theorem cliBlock_externs_eq {b : Obj.CodeBlock} (hb : b ∈ libsignalSessionLib.blocks) :
    b.externs = cliAllExterns := by
  have hmem : b.externs ∈ libsignalSessionLib.blocks.map Obj.CodeBlock.externs :=
    List.mem_map_of_mem hb
  rw [p2b_blocks_externs_eq] at hmem
  exact List.eq_of_mem_replicate hmem

private def isymMatches (a b : Obj.LabelsInterned.ISym) : Bool :=
  Nat.beq a.rawId b.rawId && Nat.beq a.nameId b.nameId && (a.sec == b.sec) && (a.bind == b.bind)

private noncomputable def p2bTargetIdOk (extId : Nat) : Bool :=
  Nat.blt extId p2bNumNames && (p2bIsTargetTree.get? extId == some true)

private noncomputable def p2bSummaryWitOk
    (w : Obj.LabelsInterned.ISym × Nat × Nat) : Bool :=
  match p2bObjSymsTree.get? w.2.1 with
  | none => false
  | some t =>
    match t.get? w.2.2 with
    | none => false
    | some isy => isymMatches isy w.1

private noncomputable def p2bPanicBucketEntryOk (k : Nat) : Bool :=
  match p2bSummaryTree.get? k with
  | none => false
  | some s1 =>
    match p2bPanicSummaryTree.get? k with
    | none => false
    | some s2 => isymMatches s1 s2

private noncomputable def p2bPanicBucketsOk : Bool :=
  p2bPanicIds.all fun extId =>
    match p2bTargetBucketTree.get? extId with
    | none => false
    | some ks => ks.all p2bPanicBucketEntryOk

private noncomputable def p2bSymOk (isy : Obj.LabelsInterned.ISym) : Bool :=
  Nat.blt isy.rawId p2bNumNames &&
  match p2bIsTargetTree.get? isy.rawId with
  | some true =>
    if isy.bind != .local then
      match p2bTargetBucketTree.get? isy.rawId with
      | none => false
      | some ks =>
        ks.any fun k =>
          match p2bSummaryTree.get? k with
          | none => false
          | some s => isymMatches isy s
    else true
  | _ => true

private noncomputable def p2bSubsumesB : Bool :=
  (p2bExternIds ++ p2bPanicIds).all p2bTargetIdOk &&
  p2bPanicSummaryWits.all p2bSummaryWitOk &&
  p2bPanicBucketsOk &&
  p2bObjSymsTree.all (fun t => t.all p2bSymOk)

private theorem p2bSubsumesB_ok : p2bSubsumesB = true := by
  open ProofLib.ProgramReflection in rfl_kernel

private theorem isymMatches_props {a b : Obj.LabelsInterned.ISym} (h : isymMatches a b = true) :
    a.rawId = b.rawId ∧ a.nameId = b.nameId ∧ a.sec = b.sec ∧ a.bind = b.bind := by
  unfold isymMatches at h
  rcases Eq.mp (Bool.and_eq_true _ _) h with ⟨h123, hbd⟩
  rcases Eq.mp (Bool.and_eq_true _ _) h123 with ⟨h12, hsec⟩
  rcases Eq.mp (Bool.and_eq_true _ _) h12 with ⟨hr, hn⟩
  exact ⟨Nat.eq_of_beq_eq_true hr, Nat.eq_of_beq_eq_true hn,
    beq_iff_eq.mp hsec, beq_iff_eq.mp hbd⟩

private theorem summary_has_matching_sym {x : String}
    (hx : x ∈ cliAllExterns ∨ x ∈ cliPanicSymbolsPlaced)
    {o : Obj.ExtractedObj} (ho : o ∈ cliLinkObjs)
    {sy : Obj.RawSym} (hsy : sy ∈ o.symbols)
    (hraw : sy.rawName = x) (hbind : sy.bind ≠ .local) :
    ∃ sy' ∈ p2bAllSummarySyms,
      sy'.rawName = sy.rawName ∧ sy'.name = sy.name ∧
      sy'.sec = sy.sec ∧ sy'.bind = sy.bind := by
  have hnd : p2bNamesTree.toList.Nodup :=
    Obj.Interned.nodup_of_namesNodup p2b_names_eq p2b_names_nodup
  rcases Eq.mp (Bool.and_eq_true _ _) p2bSubsumesB_ok with ⟨h123, htree_b⟩
  rcases Eq.mp (Bool.and_eq_true _ _) h123 with ⟨h12, _⟩
  rcases Eq.mp (Bool.and_eq_true _ _) h12 with ⟨htids_b, _⟩
  have htids : ∀ extId ∈ p2bExternIds ++ p2bPanicIds, p2bTargetIdOk extId = true :=
    List.all_eq_true.mp htids_b
  rw [IdxTree.all_eq_toList_all] at htree_b
  have hall_objs : ∀ t ∈ p2bObjSymsTree.toList, t.all p2bSymOk = true :=
    List.all_eq_true.mp htree_b
  have hid_ex : ∃ extId ∈ p2bExternIds ++ p2bPanicIds,
      x = Obj.LabelsInterned.symAt p2bNamesTree extId := by
    rcases hx with hext | hpan
    · rw [p2b_externs_eq, List.mem_map] at hext
      obtain ⟨extId, hid, rfl⟩ := hext
      exact ⟨extId, List.mem_append_left _ hid, rfl⟩
    · rw [p2b_panics_eq, List.mem_map] at hpan
      obtain ⟨extId, hid, rfl⟩ := hpan
      exact ⟨extId, List.mem_append_right _ hid, rfl⟩
  obtain ⟨extId, hid_mem, rfl⟩ := hid_ex
  have htid_ok := htids extId hid_mem
  unfold p2bTargetIdOk at htid_ok
  rcases Eq.mp (Bool.and_eq_true _ _) htid_ok with ⟨hext_lt_b, hext_tree_b⟩
  have hext_lt : extId < p2bNumNames := Obj.Interned.blt_iff.mp hext_lt_b
  have hext_tree : p2bIsTargetTree.get? extId = some true := beq_iff_eq.mp hext_tree_b
  have ho_map :
      o.symbols ∈
        p2bObjSymsTree.toList.map
          (fun t => t.toList.map (Obj.LabelsInterned.ISym.toRawSym p2bNamesTree)) := by
    rw [← p2b_objs_syms_eq]
    exact List.mem_map_of_mem ho
  obtain ⟨t, ht_mem, ht_eq⟩ := List.mem_map.mp ho_map
  rw [← ht_eq] at hsy
  obtain ⟨isy, hisy_mem, rfl⟩ := List.mem_map.mp hsy
  have ht_ok := hall_objs t ht_mem
  rw [IdxTree.all_eq_toList_all] at ht_ok
  have hisy_ok : p2bSymOk isy = true := List.all_eq_true.mp ht_ok isy hisy_mem
  unfold p2bSymOk at hisy_ok
  rcases Eq.mp (Bool.and_eq_true _ _) hisy_ok with ⟨hisy_lt_b, hisy_tgt⟩
  have hisy_lt : isy.rawId < p2bNumNames := Obj.Interned.blt_iff.mp hisy_lt_b
  have hid_eq : isy.rawId = extId :=
    Obj.LabelsInterned.symAt_inj p2b_names_sz hnd hisy_lt hext_lt hraw
  rw [hid_eq, hext_tree] at hisy_tgt
  dsimp only at hisy_tgt
  have hbn : (isy.bind != .local) = true := bne_iff_ne.mpr hbind
  rw [hbn] at hisy_tgt
  simp only [↓reduceIte] at hisy_tgt
  cases hbucket : p2bTargetBucketTree.get? extId with
  | none => rw [hbucket] at hisy_tgt; cases hisy_tgt
  | some ks =>
    rw [hbucket] at hisy_tgt
    dsimp only at hisy_tgt
    obtain ⟨k, _, hk_ok⟩ := List.any_eq_true.mp hisy_tgt
    cases hget_s : p2bSummaryTree.get? k with
    | none => rw [hget_s] at hk_ok; cases hk_ok
    | some s =>
      rw [hget_s] at hk_ok
      dsimp only at hk_ok
      obtain ⟨hr, hn, hsec, hbd⟩ := isymMatches_props hk_ok
      refine ⟨s.toRawSym p2bNamesTree, ?_, ?_⟩
      · rw [p2b_summary_syms_eq]
        exact List.mem_map_of_mem (IdxTree.mem_toList_of_get? hget_s)
      · dsimp only [Obj.LabelsInterned.ISym.toRawSym]
        exact ⟨congrArg _ hr.symm, congrArg _ hn.symm, hsec.symm, hbd.symm⟩

private theorem panic_summary_has_matching_sym {x : String}
    (hx : x ∈ cliPanicSymbolsPlaced)
    {o : Obj.ExtractedObj} (ho : o ∈ cliLinkObjs)
    {sy : Obj.RawSym} (hsy : sy ∈ o.symbols)
    (hraw : sy.rawName = x) (hbind : sy.bind ≠ .local) :
    ∃ sy' ∈ p2bPanicSummaryObj.symbols,
      sy'.rawName = sy.rawName ∧ sy'.name = sy.name ∧
      sy'.sec = sy.sec ∧ sy'.bind = sy.bind := by
  have hnd : p2bNamesTree.toList.Nodup :=
    Obj.Interned.nodup_of_namesNodup p2b_names_eq p2b_names_nodup
  rcases Eq.mp (Bool.and_eq_true _ _) p2bSubsumesB_ok with ⟨h123, htree_b⟩
  rcases Eq.mp (Bool.and_eq_true _ _) h123 with ⟨h12, hpbuckets_b⟩
  rcases Eq.mp (Bool.and_eq_true _ _) h12 with ⟨htids_b, _⟩
  have htids : ∀ extId ∈ p2bExternIds ++ p2bPanicIds, p2bTargetIdOk extId = true :=
    List.all_eq_true.mp htids_b
  have hpbuckets := List.all_eq_true.mp hpbuckets_b
  rw [IdxTree.all_eq_toList_all] at htree_b
  have hall_objs : ∀ t ∈ p2bObjSymsTree.toList, t.all p2bSymOk = true :=
    List.all_eq_true.mp htree_b
  rw [p2b_panics_eq, List.mem_map] at hx
  obtain ⟨extId, hid_pan, rfl⟩ := hx
  have htid_ok := htids extId (List.mem_append_right _ hid_pan)
  unfold p2bTargetIdOk at htid_ok
  rcases Eq.mp (Bool.and_eq_true _ _) htid_ok with ⟨hext_lt_b, hext_tree_b⟩
  have hext_lt : extId < p2bNumNames := Obj.Interned.blt_iff.mp hext_lt_b
  have hext_tree : p2bIsTargetTree.get? extId = some true := beq_iff_eq.mp hext_tree_b
  have ho_map :
      o.symbols ∈
        p2bObjSymsTree.toList.map
          (fun t => t.toList.map (Obj.LabelsInterned.ISym.toRawSym p2bNamesTree)) := by
    rw [← p2b_objs_syms_eq]
    exact List.mem_map_of_mem ho
  obtain ⟨t, ht_mem, ht_eq⟩ := List.mem_map.mp ho_map
  rw [← ht_eq] at hsy
  obtain ⟨isy, hisy_mem, rfl⟩ := List.mem_map.mp hsy
  have ht_ok := hall_objs t ht_mem
  rw [IdxTree.all_eq_toList_all] at ht_ok
  have hisy_ok : p2bSymOk isy = true := List.all_eq_true.mp ht_ok isy hisy_mem
  unfold p2bSymOk at hisy_ok
  rcases Eq.mp (Bool.and_eq_true _ _) hisy_ok with ⟨hisy_lt_b, hisy_tgt⟩
  have hisy_lt : isy.rawId < p2bNumNames := Obj.Interned.blt_iff.mp hisy_lt_b
  have hid_eq : isy.rawId = extId :=
    Obj.LabelsInterned.symAt_inj p2b_names_sz hnd hisy_lt hext_lt hraw
  rw [hid_eq, hext_tree] at hisy_tgt
  dsimp only at hisy_tgt
  have hbn : (isy.bind != .local) = true := bne_iff_ne.mpr hbind
  rw [hbn] at hisy_tgt
  simp only [↓reduceIte] at hisy_tgt
  have hpb := hpbuckets extId hid_pan
  cases hbucket : p2bTargetBucketTree.get? extId with
  | none => rw [hbucket] at hisy_tgt; cases hisy_tgt
  | some ks =>
    rw [hbucket] at hisy_tgt hpb
    dsimp only at hisy_tgt hpb
    obtain ⟨k, hk_mem, hk_ok⟩ := List.any_eq_true.mp hisy_tgt
    have hk_ent : p2bPanicBucketEntryOk k = true := List.all_eq_true.mp hpb k hk_mem
    unfold p2bPanicBucketEntryOk at hk_ent
    cases hget_s : p2bSummaryTree.get? k with
    | none => rw [hget_s] at hk_ok; cases hk_ok
    | some s =>
      rw [hget_s] at hk_ok hk_ent
      dsimp only at hk_ok hk_ent
      cases hget_p : p2bPanicSummaryTree.get? k with
      | none => rw [hget_p] at hk_ent; cases hk_ent
      | some s2 =>
        rw [hget_p] at hk_ent
        dsimp only at hk_ent
        obtain ⟨hr1, hn1, hsec1, hbd1⟩ := isymMatches_props hk_ok
        obtain ⟨hr2, hn2, hsec2, hbd2⟩ := isymMatches_props hk_ent
        refine ⟨s2.toRawSym p2bNamesTree, ?_, ?_⟩
        · rw [p2b_panic_summary_syms_eq]
          exact List.mem_map_of_mem (IdxTree.mem_toList_of_get? hget_p)
        · dsimp only [Obj.LabelsInterned.ISym.toRawSym]
          exact ⟨congrArg _ (hr1.trans hr2).symm, congrArg _ (hn1.trans hn2).symm,
            (hsec1.trans hsec2).symm, (hbd1.trans hbd2).symm⟩

private theorem panic_objs_has_matching_sym {sy' : Obj.RawSym}
    (hsy' : sy' ∈ p2bPanicSummaryObj.symbols) :
    ∃ o ∈ cliLinkObjs, ∃ sy ∈ o.symbols,
      sy.rawName = sy'.rawName ∧ sy.name = sy'.name ∧
      sy.sec = sy'.sec ∧ sy.bind = sy'.bind := by
  rcases Eq.mp (Bool.and_eq_true _ _) p2bSubsumesB_ok with ⟨h123, _⟩
  rcases Eq.mp (Bool.and_eq_true _ _) h123 with ⟨h12, _⟩
  rcases Eq.mp (Bool.and_eq_true _ _) h12 with ⟨_, hwits_b⟩
  have hwits : ∀ w ∈ p2bPanicSummaryWits, p2bSummaryWitOk w = true := List.all_eq_true.mp hwits_b
  rw [p2b_panic_summary_syms_eq, p2b_panic_summary_wits_eq, List.map_map] at hsy'
  obtain ⟨w, hw_mem, rfl⟩ := List.mem_map.mp hsy'
  have hw_ok := hwits w hw_mem
  unfold p2bSummaryWitOk at hw_ok
  cases hget_o : p2bObjSymsTree.get? w.2.1 with
  | none => rw [hget_o] at hw_ok; cases hw_ok
  | some t =>
    rw [hget_o] at hw_ok
    dsimp only at hw_ok
    cases hget_s : t.get? w.2.2 with
    | none => rw [hget_s] at hw_ok; cases hw_ok
    | some isy =>
      rw [hget_s] at hw_ok
      dsimp only at hw_ok
      obtain ⟨hr, hn, hsec, hbd⟩ := isymMatches_props hw_ok
      have ht_mem : t ∈ p2bObjSymsTree.toList := IdxTree.mem_toList_of_get? hget_o
      have hisy_mem : isy ∈ t.toList := IdxTree.mem_toList_of_get? hget_s
      have hmap :
          t.toList.map (Obj.LabelsInterned.ISym.toRawSym p2bNamesTree) ∈
            cliLinkObjs.map Obj.ExtractedObj.symbols := by
        rw [p2b_objs_syms_eq]
        exact List.mem_map_of_mem ht_mem
      obtain ⟨o, ho, ho_syms⟩ := List.mem_map.mp hmap
      refine ⟨o, ho, isy.toRawSym p2bNamesTree, ?_, ?_⟩
      · rw [ho_syms]
        exact List.mem_map_of_mem hisy_mem
      · dsimp only [Function.comp_apply, Obj.LabelsInterned.ISym.toRawSym]
        exact ⟨congrArg _ hr, congrArg _ hn, hsec, hbd⟩

private theorem list_contains_eq_any_toList (xs : List String) (s : String) :
    xs.contains s = (xs.map String.toList).any (fun p => s.toList == p) := by
  induction xs with
  | nil => rfl
  | cons x rest ih =>
    simp only [List.contains_cons, List.map_cons, List.any_cons, ih]
    congr 1
    apply Bool.eq_iff_iff.2
    simp only [beq_iff_eq, String.ext_iff]

private theorem p2b_panic_toList_eq :
    cliPanicSymbolsPlaced.map String.toList = p2bPanicChars := by
  open ProofLib.ProgramReflection in rfl_kernel

private theorem p2b_exact_panic_toList_eq :
    Obj.rustPanicExactNames.map String.toList = p2bRustExactPanicChars := by
  open ProofLib.ProgramReflection in rfl_kernel

private noncomputable def isRustPanicSymbolUltraFast (name : String) : Bool :=
  let cs := name.toList
  List.isPrefixOf
    ['c', 'o', 'r', 'e', ':', ':', 'p', 'a', 'n', 'i', 'c', 'k', 'i', 'n', 'g', ':', ':'] cs ||
    p2bRustExactPanicChars.any (fun p => cs == p)

private theorem rust_isPanicSymbol_eq_ultraFast (s : String) :
    Rust.isPanicSymbol s = isRustPanicSymbolUltraFast s := by
  rw [Obj.rust_isPanicSymbol_eq_fast]
  unfold Obj.isPanicSymbolFast Obj.isPanicSymbolChars isRustPanicSymbolUltraFast
  rw [p2b_exact_panic_toList_eq]

private noncomputable def isCliPanicSymbolPlacedFast (name : String) : Bool :=
  let cs := name.toList
  p2bPanicChars.any (fun p => cs == p) ||
    (List.isPrefixOf
      ['c', 'o', 'r', 'e', ':', ':', 'p', 'a', 'n', 'i', 'c', 'k', 'i', 'n', 'g', ':', ':'] cs ||
      p2bRustExactPanicChars.any (fun p => cs == p))

private theorem isCliPanicSymbolPlaced_eq_fast (s : String) :
    isCliPanicSymbolPlaced s = isCliPanicSymbolPlacedFast s := by
  unfold isCliPanicSymbolPlaced isCliPanicSymbolPlacedFast
  rw [list_contains_eq_any_toList, p2b_panic_toList_eq, rust_isPanicSymbol_eq_ultraFast]
  rfl

private def cliEmptyBlocksLib : Obj.MultiPlacedLib :=
  { name := "", blocks := [] }

private theorem cliGateAPanicCheck_ok :
    Obj.checkGateALabelsB
      [p2bPanicSummaryObj]
      cliEmptyBlocksLib
      (fun _ => default)
      cliPanicSymbolsPlaced
      []
      []
      []
      cliPanicSymbolsPlaced
      cliPanicExtraDemangled
      isCliPanicSymbolPlacedFast
      0
      [] = true := by
  open ProofLib.ProgramReflection in rfl_kernel

private theorem cliGateAPanicAnchored :
    Obj.GateALabelsAnchored
      [p2bPanicSummaryObj]
      cliEmptyBlocksLib
      (fun _ => default)
      cliPanicSymbolsPlaced
      []
      []
      []
      cliPanicSymbolsPlaced
      cliPanicExtraDemangled
      isCliPanicSymbolPlacedFast
      0
      [] :=
  Obj.gateALabels_of_check cliGateAPanicCheck_ok

private theorem cliAllExterns_not_std_panic :
    (cliAllExterns.all fun x => !isRustPanicSymbolUltraFast x) = true := by
  open ProofLib.ProgramReflection in rfl_kernel

/-- Every non-local `.o` symbol matching an extern in `libsignalSessionLib` with
`isCliPanicSymbolPlaced x = true` demangles to a Rust panic entry point (`Rust.isPanicSymbol` or
`cliPanicExtraDemangled`). -/
theorem cliPanicLabelsSound : CliPanicLabelsSound := by
  have hG := cliGateAPanicAnchored
  intro b hb x hx hpanic o ho sy hsy hraw hbind
  rw [cliBlock_externs_eq hb] at hx
  rw [isCliPanicSymbolPlaced_eq_fast] at hpanic
  have hx_mem : x ∈ cliPanicSymbolsPlaced := by
    rcases Eq.mp (Bool.or_eq_true _ _) hpanic with hin | hstd
    · have hcont : cliPanicSymbolsPlaced.contains x = true := by
        rw [list_contains_eq_any_toList, p2b_panic_toList_eq]
        exact hin
      exact List.contains_iff_mem.1 hcont
    · have hnot : (!isRustPanicSymbolUltraFast x) = true :=
        List.all_eq_true.mp cliAllExterns_not_std_panic x hx
      change isRustPanicSymbolUltraFast x = true at hstd
      rw [hstd] at hnot
      cases hnot
  obtain ⟨sy', hsy', hraw', hname', _, hbind'⟩ :=
    panic_summary_has_matching_sym hx_mem ho hsy hraw hbind
  have hplus : Obj.isRustPanicPlus cliPanicExtraDemangled sy'.name = true :=
    ((hG.panics_demangled x hx_mem).2 p2bPanicSummaryObj (List.mem_singleton.2 rfl)
      sy' hsy' (hraw'.trans hraw) (hbind' ▸ hbind)).2
  rw [hname'] at hplus
  unfold Obj.isRustPanicPlus at hplus
  rcases Eq.mp (Bool.or_eq_true _ _) hplus with hstd | hextra
  · exact Or.inl hstd
  · exact Or.inr (List.contains_iff_mem.1 hextra)

/-- Mangled `.strtab` name of the unique extern in `cliPanicSymbolsPlaced` outside
`Rust.isPanicSymbol`. -/
def cliPanicExtraRawSym : String :=
  "_RNvNvMs_NtCs69KKACWg7bl_5alloc3vecINtB6_3VecppE6remove13assert_failed"

/-- Demangled `.o` symbol name corresponding to `cliPanicExtraRawSym`. -/
def cliPanicExtraDemangledSym : String :=
  "<alloc::vec::Vec<_, _>>::remove::assert_failed"

private theorem p2b_extra_raw_toList_eq :
    cliPanicExtraRawSym.toList = p2bExtraRawChars := by
  open ProofLib.ProgramReflection in rfl_kernel

private theorem p2b_extra_demangled_toList_eq :
    cliPanicExtraDemangledSym.toList = p2bExtraDemangledChars := by
  open ProofLib.ProgramReflection in rfl_kernel

private noncomputable def p2bSummarySymCompleteOk (sy' : Obj.RawSym) : Bool :=
  !(sy'.sec == .undef) ||
  !(isRustPanicSymbolUltraFast sy'.name || (sy'.name.toList == p2bExtraDemangledChars)) ||
  p2bPanicChars.any (fun pc => sy'.rawName.toList == pc)

private theorem p2bAllSummaryComplete_ok :
    p2bAllSummarySyms.all p2bSummarySymCompleteOk = true := by
  open ProofLib.ProgramReflection in rfl_kernel

/-- Completeness converse of `cliPanicLabelsSound`: every extern of `libsignalSessionLib` whose
non-local `.undef` symbol in `cliLinkObjs` demangles to `Rust.isPanicSymbol` or
`cliPanicExtraDemangled` satisfies `isCliPanicSymbolPlaced x = true`. -/
theorem cliPanicLabelsComplete :
    ∀ b ∈ libsignalSessionLib.blocks, ∀ x ∈ b.externs,
      ∀ o ∈ cliLinkObjs, ∀ sy ∈ o.symbols,
        sy.rawName = x → sy.bind ≠ .local → sy.sec = .undef →
        (Rust.isPanicSymbol sy.name = true ∨ sy.name ∈ cliPanicExtraDemangled) →
        isCliPanicSymbolPlaced x = true := by
  intro b hb x hx o ho sy hsy hraw hbind hsec hdem
  rw [cliBlock_externs_eq hb] at hx
  obtain ⟨sy', hsy', hraw', hname', hsec', _⟩ :=
    summary_has_matching_sym (Or.inl hx) ho hsy hraw hbind
  have hok : p2bSummarySymCompleteOk sy' = true :=
    List.all_eq_true.mp p2bAllSummaryComplete_ok sy' hsy'
  unfold p2bSummarySymCompleteOk at hok
  rcases Eq.mp (Bool.or_eq_true _ _) hok with h12 | hany
  · rcases Eq.mp (Bool.or_eq_true _ _) h12 with hnot_sec | hnot_dem
    · have hsec_b : (sy'.sec == .undef) = true := beq_iff_eq.2 (hsec'.trans hsec)
      rw [hsec_b] at hnot_sec
      cases hnot_sec
    · have hdem_b : (isRustPanicSymbolUltraFast sy'.name ||
          (sy'.name.toList == p2bExtraDemangledChars)) = true := by
        rw [hname']
        apply Eq.mpr (Bool.or_eq_true _ _)
        rcases hdem with hstd | hextra
        · rw [← rust_isPanicSymbol_eq_ultraFast]
          exact Or.inl hstd
        · have hextra_eq : cliPanicExtraDemangled = [cliPanicExtraDemangledSym] := rfl
          rw [hextra_eq, List.mem_singleton] at hextra
          rw [hextra, p2b_extra_demangled_toList_eq]
          exact Or.inr (beq_self_eq_true _)
      rw [hdem_b] at hnot_dem
      cases hnot_dem
  · rw [hraw', hraw] at hany
    rw [isCliPanicSymbolPlaced_eq_fast]
    exact Eq.mpr (Bool.or_eq_true _ _) (Or.inl hany)

private theorem cliPanicExtraDemangled_summary_check :
    Obj.checkExternDataDemangledB [p2bPanicSummaryObj]
      [(cliPanicExtraRawSym, cliPanicExtraDemangledSym)] = true := by
  open ProofLib.ProgramReflection in rfl_kernel

private noncomputable def p2bOtherPanicSymStdOk (sy' : Obj.RawSym) : Bool :=
  !(sy'.bind != .local) ||
  (sy'.rawName.toList == p2bExtraRawChars) ||
  isRustPanicSymbolUltraFast sy'.name

private theorem p2bOtherPanicsStd_ok :
    p2bPanicSummaryObj.symbols.all p2bOtherPanicSymStdOk = true := by
  open ProofLib.ProgramReflection in rfl_kernel

private theorem cliPanicExtraRawSym_contains_fast :
    p2bPanicChars.any (fun p => cliPanicExtraRawSym.toList == p) = true := by
  open ProofLib.ProgramReflection in rfl_kernel

/-- Pinning certificate for `cliPanicExtraRawSym`: it belongs to `cliPanicSymbolsPlaced`, occurs as
a non-local `.undef` symbol in `cliLinkObjs` with demangled name `cliPanicExtraDemangledSym` outside
`Rust.isPanicSymbol`, while every other symbol in `cliPanicSymbolsPlaced` satisfies
`Rust.isPanicSymbol`. -/
theorem cliPanicExtraSym_is_extraDemangled :
    [cliPanicExtraDemangledSym] = cliPanicExtraDemangled ∧
    Rust.isPanicSymbol cliPanicExtraDemangledSym = false ∧
    cliPanicExtraRawSym ∈ cliPanicSymbolsPlaced ∧
    Obj.NonVacuousUndefSymDemangled cliLinkObjs cliPanicExtraRawSym cliPanicExtraDemangledSym ∧
    (∀ p ∈ cliPanicSymbolsPlaced, p ≠ cliPanicExtraRawSym →
      ∀ o ∈ cliLinkObjs, ∀ sy ∈ o.symbols,
        sy.rawName = p → sy.bind ≠ .local → Rust.isPanicSymbol sy.name = true) := by
  have hpan_contains : cliPanicSymbolsPlaced.contains cliPanicExtraRawSym = true := by
    rw [list_contains_eq_any_toList, p2b_panic_toList_eq]
    exact cliPanicExtraRawSym_contains_fast
  have hpan_mem : cliPanicExtraRawSym ∈ cliPanicSymbolsPlaced :=
    List.contains_iff_mem.1 hpan_contains
  refine ⟨rfl, ?_, hpan_mem, ?_, ?_⟩
  · rw [rust_isPanicSymbol_eq_ultraFast]
    open ProofLib.ProgramReflection in rfl_kernel
  · have hsum := Obj.externDataDemangled_of_check cliPanicExtraDemangled_summary_check
      (cliPanicExtraRawSym, cliPanicExtraDemangledSym) (List.mem_singleton.2 rfl)
    obtain ⟨⟨so, hso, ssy, hssy, hsraw, hsbind, hssec, hsdem⟩, hsall⟩ := hsum
    rw [List.mem_singleton] at hso
    subst hso
    obtain ⟨o0, ho0, sy0, hsy0, hr0, hn0, hsc0, hbd0⟩ := panic_objs_has_matching_sym hssy
    refine ⟨⟨o0, ho0, sy0, hsy0, hr0.trans hsraw, hbd0.symm ▸ hsbind, hsc0.trans hssec,
      hn0.trans hsdem⟩, ?_⟩
    intro o ho sy hsy hraw hbind
    obtain ⟨sy', hsy', hr', hn', hsc', hbd'⟩ :=
      panic_summary_has_matching_sym hpan_mem ho hsy hraw hbind
    have h1 := hsall p2bPanicSummaryObj (List.mem_singleton.2 rfl) sy' hsy'
      (hr'.trans hraw) (hbd' ▸ hbind)
    exact ⟨hsc'.symm.trans h1.1, hn'.symm.trans h1.2⟩
  · intro p hp hp_ne o ho sy hsy hraw hbind
    obtain ⟨sy', hsy', hr', hn', _, hbd'⟩ :=
      panic_summary_has_matching_sym hp ho hsy hraw hbind
    have hok : p2bOtherPanicSymStdOk sy' = true :=
      List.all_eq_true.mp p2bOtherPanicsStd_ok sy' hsy'
    unfold p2bOtherPanicSymStdOk at hok
    rcases Eq.mp (Bool.or_eq_true _ _) hok with h12 | hstd
    · rcases Eq.mp (Bool.or_eq_true _ _) h12 with hloc | hextra
      · have hbn : (sy'.bind != .local) = true := bne_iff_ne.2 (hbd' ▸ hbind)
        rw [hbn] at hloc
        cases hloc
      · have hrc_eq : sy'.rawName.toList = cliPanicExtraRawSym.toList := by
          rw [p2b_extra_raw_toList_eq]
          exact beq_iff_eq.1 hextra
        have hp_eq : p = cliPanicExtraRawSym := by
          rw [← hraw, ← hr']
          exact String.ext_iff.2 hrc_eq
        exact absurd hp_eq hp_ne
    · rw [← hn', rust_isPanicSymbol_eq_ultraFast]
      exact hstd

/-- `cliPanicExtraRawSym` occurs as a non-local `.undef` symbol in `cliLinkObjs`, and every
non-local occurrence has `[sy.name] = cliPanicExtraDemangled`. -/
theorem cliPanicExtraRawSym_demangled_eq :
    (∃ o ∈ cliLinkObjs, ∃ sy ∈ o.symbols,
      sy.rawName = cliPanicExtraRawSym ∧ sy.bind ≠ .local ∧ sy.sec = .undef ∧
      [sy.name] = cliPanicExtraDemangled) ∧
    (∀ o ∈ cliLinkObjs, ∀ sy ∈ o.symbols,
      sy.rawName = cliPanicExtraRawSym → sy.bind ≠ .local →
      [sy.name] = cliPanicExtraDemangled) := by
  obtain ⟨hlist_eq, _, _, ⟨⟨o0, ho0, sy0, hsy0, hr0, hb0, hs0, hd0⟩, hall⟩, _⟩ :=
    cliPanicExtraSym_is_extraDemangled
  refine ⟨⟨o0, ho0, sy0, hsy0, hr0, hb0, hs0, hd0 ▸ hlist_eq⟩, ?_⟩
  intro o ho sy hsy hraw hbind
  have hd := (hall o ho sy hsy hraw hbind).2
  exact hd ▸ hlist_eq

end LibsignalBinary.Proofs.SpecLemmas.SignalSession.CliPanicLabels
