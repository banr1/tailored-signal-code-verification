/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Specifications.SignalSession.CliLabels
meta import LibsignalBinary.Specifications.SignalSession.CliLabels
public import ProofLib.Placed.LabelsInterned
meta import ProofLib.Placed.LabelsInterned
meta import ProofLib.ProgramReflection
meta import ProofLib.ProgramReflection.IdxTree
meta import Lean

@[expose] public section

set_option autoImplicit false

/-!
# Interned `LabelsFromObjects` Certificate Trees and Metadata Checks

**Checked by Lean.** Synthesizes the interned `IdxTree` provenance certificate for `cliLinkObjs`
and `libsignalSessionLib` (resolving unique `bO` and `dO` slice origins from the relocation graph)
and discharges the 12 structural and metadata split checks.
-/

namespace LibsignalBinary.Proofs.SpecLemmas.SignalSession.CliLabelsLfoCert

open Arm64 Arm64.Obj Arm64.Obj.LabelsInterned
open ProofLib.ProgramReflection
open Lean Elab Command Term Meta
open CryptoVerification.SignalSession (cliLinkObjs libsignalSessionLib)

private meta instance : Inhabited SymSec := ⟨.undef⟩
private meta instance : Inhabited SymKind := ⟨.other⟩
private meta instance : Inhabited SymBind := ⟨.other⟩
private meta instance : Inhabited SliceOrigin := ⟨⟨0, 0, 0, 0⟩⟩

private meta inductive MSymRole where
  | other
  | blockSym (bi j off : Nat)
  | dataSym (di : Nat)
  deriving DecidableEq, BEq, Inhabited

private meta inductive MRawIdStatus where
  | other
  | globalDef (oi k si : Nat)
  | allNonLocalUndef
  | weakOnlyUndef (wOi wKi : Nat)
  deriving DecidableEq, BEq, Inhabited

private meta structure DecRawReloc where
  off : Nat
  kindName? : Option Name
  symIdx : Nat
  addend : Int
  deriving Inhabited

private meta structure DecRawSec where
  name : String
  bytesE : Expr
  size : Nat
  align : Nat
  isExec : Bool
  readOnly : Bool
  isNobits : Bool
  isTls : Bool
  relocs : Array DecRawReloc
  relocsE : Expr
  deriving Inhabited

private meta structure DecRawSym where
  rawName : String
  name : String
  sec : SymSec
  value : Nat
  size : Nat
  kind : SymKind
  bind : SymBind
  deriving Inhabited

private meta structure DecObj where
  name : String
  sections : Array DecRawSec
  symbols : Array DecRawSym
  groupsE : Expr
  deriving Inhabited

private meta structure DecReloc where
  off : Nat
  kindName : Name
  kindE : Expr
  sym : String
  addend : Int
  localSym : Bool
  deriving Inhabited

private meta structure DecBlock where
  code : ByteArray
  codeE : Expr
  align : Nat
  symbols : Array (String × Nat)
  relocs : Array DecReloc
  externs : Array String
  weakRefs : Array String
  deriving Inhabited

private meta structure DecData where
  sym : String
  align : Nat
  readOnly : Bool
  bytesLen : Nat
  bytesE : Expr
  zeroTail : Nat
  relocs : Array DecReloc
  deriving Inhabited

private meta structure DecMultiLib where
  name : String
  blocks : Array DecBlock
  data : Array DecData
  exports : Array String
  exportSyms : Array (String × String)
  deriving Inhabited

private meta def decodeNatVal (e : Expr) : MetaM Nat := do
  if let some n := e.rawNatLit? then return n
  if let some n ← (evalNat e).run then return n
  let e ← whnf e
  match e.rawNatLit? with
  | some n => return n
  | none =>
    if let some n ← (evalNat e).run then return n
    throwError "gen_cli_labels_from_objects_cert: expected Nat literal, got{indentExpr e}"

private meta def decodeBoolVal (e : Expr) : MetaM Bool := do
  let c := e.consumeMData
  if c.isConstOf ``Bool.true then return true
  if c.isConstOf ``Bool.false then return false
  let w ← whnf c
  if w.isConstOf ``Bool.true then return true
  if w.isConstOf ``Bool.false then return false
  throwError "gen_cli_labels_from_objects_cert: expected Bool literal, got{indentExpr w}"

private meta def decodeStrVal (e : Expr) : MetaM String := do
  let c := e.consumeMData
  if let .lit (.strVal s) := c then return s
  match (← whnf c) with
  | .lit (.strVal s) => return s
  | w => throwError "gen_cli_labels_from_objects_cert: expected String literal, got{indentExpr w}"

private meta partial def decodeIntVal (e : Expr) : MetaM Int := do
  let c := e.consumeMData
  if c.isAppOfArity ``OfNat.ofNat 3 then
    if let some n := (c.getArg! 1).rawNatLit? then return (n : Int)
  if c.isAppOfArity ``Neg.neg 3 then
    return -(← decodeIntVal (c.getArg! 2))
  let w ← whnf c
  if w.isAppOfArity ``Int.ofNat 1 then
    return ((← decodeNatVal (w.getArg! 0)) : Int)
  if w.isAppOfArity ``Int.negSucc 1 then
    return -(((← decodeNatVal (w.getArg! 0)) + 1 : Nat) : Int)
  throwError "gen_cli_labels_from_objects_cert: expected Int literal, got{indentExpr w}"

private meta partial def decodeListElems (e : Expr) : MetaM (Array Expr) := do
  let rec go (cur : Expr) (acc : Array Expr) : MetaM (Array Expr) := do
    let c := cur.consumeMData
    if c.isAppOfArity ``List.nil 1 then return acc
    else if c.isAppOfArity ``List.cons 3 then go (c.getArg! 2) (acc.push (c.getArg! 1))
    else if c.isAppOfArity ``HAppend.hAppend 6 then go (c.getArg! 5) (← go (c.getArg! 4) acc)
    else if c.isAppOfArity ``List.append 3 then go (c.getArg! 2) (← go (c.getArg! 1) acc)
    else if let some c' ← unfoldDefinition? c then go c' acc
    else
      let w ← whnf c
      if w == c then throwError "gen_cli_labels_from_objects_cert: expected List, got{indentExpr w}"
      go w acc
  go e #[]

private meta def decodeByteVal (hd : Expr) : MetaM UInt8 := do
  let c := hd.consumeMData
  if c.isAppOfArity ``BitVec.ofNat 2 then
    if let some n := (c.getArg! 1).rawNatLit? then return n.toUInt8
  if c.isAppOfArity ``OfNat.ofNat 3 then
    if let some n := (c.getArg! 1).rawNatLit? then return n.toUInt8
  let w ← whnf c
  if w.isAppOfArity ``BitVec.ofFin 2 then
    let finE ← whnf (w.getArg! 1)
    if finE.isAppOfArity ``Fin.mk 3 then return (← decodeNatVal (finE.getArg! 1)).toUInt8
  if w.isAppOfArity ``BitVec.ofNat 2 then return (← decodeNatVal (w.getArg! 1)).toUInt8
  throwError "gen_cli_labels_from_objects_cert: expected BitVec 8 literal, got{indentExpr w}"

private meta partial def decodeBytes (e : Expr) : MetaM ByteArray := do
  let rec go (cur : Expr) (acc : ByteArray) : MetaM ByteArray := do
    let c := cur.consumeMData
    if c.isAppOfArity ``List.nil 1 then return acc
    else if c.isAppOfArity ``List.cons 3 then go (c.getArg! 2) (acc.push (← decodeByteVal (c.getArg! 1)))
    else if c.isAppOfArity ``List.flatten 2 then
      let chunks ← decodeListElems (c.getArg! 1)
      let mut out := acc
      for ch in chunks do out ← go ch out
      return out
    else if c.isAppOfArity ``HAppend.hAppend 6 then go (c.getArg! 5) (← go (c.getArg! 4) acc)
    else if c.isAppOfArity ``List.append 3 then go (c.getArg! 2) (← go (c.getArg! 1) acc)
    else if let some c' ← unfoldDefinition? c then go c' acc
    else
      let w ← whnf c
      if w == c then throwError "gen_cli_labels_from_objects_cert: expected List (BitVec 8), got{indentExpr w}"
      go w acc
  go e ByteArray.empty

private meta partial def unfoldToCtor (ctorName : Name) (arity : Nat) (e : Expr) : MetaM Expr := do
  let c := e.consumeMData
  if c.isAppOfArity ctorName arity then return c
  if let some c' ← unfoldDefinition? c then return ← unfoldToCtor ctorName arity c'
  let w ← whnf c
  if w.isAppOfArity ctorName arity then return w
  throwError "gen_cli_labels_from_objects_cert: expected {ctorName}, got{indentExpr w}"

private meta def decodeSymSec (e : Expr) : MetaM SymSec := do
  let w ← whnf e
  if w.isConstOf ``SymSec.undef then return .undef
  if w.isConstOf ``SymSec.other then return .other
  if w.isAppOfArity ``SymSec.sec 1 then return .sec (← decodeNatVal (w.getArg! 0))
  throwError "gen_cli_labels_from_objects_cert: expected SymSec, got{indentExpr w}"

private meta def decodeSymKind (e : Expr) : MetaM SymKind := do
  let w ← whnf e
  if w.isConstOf ``SymKind.func then return .func
  if w.isConstOf ``SymKind.object then return .object
  if w.isConstOf ``SymKind.tls then return .tls
  if w.isConstOf ``SymKind.section then return .section
  if w.isConstOf ``SymKind.other then return .other
  throwError "gen_cli_labels_from_objects_cert: expected SymKind, got{indentExpr w}"

private meta def decodeSymBind (e : Expr) : MetaM SymBind := do
  let w ← whnf e
  if w.isConstOf ``SymBind.local then return .local
  if w.isConstOf ``SymBind.global then return .global
  if w.isConstOf ``SymBind.weak then return .weak
  if w.isConstOf ``SymBind.other then return .other
  throwError "gen_cli_labels_from_objects_cert: expected SymBind, got{indentExpr w}"

private meta def decodeRelocKindName (e : Expr) : MetaM (Name × Expr) := do
  let c := e.consumeMData
  if let some nm := c.constName? then
    if nm.getPrefix == ``RelocKind then return (nm, c)
  let w ← whnf c
  if let some nm := w.constName? then return (nm, Lean.mkConst nm)
  throwError "gen_cli_labels_from_objects_cert: expected RelocKind, got{indentExpr w}"

private meta def decodeRawReloc (e : Expr) : MetaM DecRawReloc := do
  let c ← unfoldToCtor ``RawReloc.mk 4 e
  let off ← decodeNatVal (c.getArg! 0)
  let kOpt ← whnf (c.getArg! 1)
  let kindName? ←
    if kOpt.isAppOfArity ``Option.none 1 then pure none
    else if kOpt.isAppOfArity ``Option.some 2 then pure (some (← decodeRelocKindName (kOpt.getArg! 1)).1)
    else throwError "gen_cli_labels_from_objects_cert: expected Option RelocKind, got{indentExpr kOpt}"
  return { off, kindName?, symIdx := ← decodeNatVal (c.getArg! 2), addend := ← decodeIntVal (c.getArg! 3) }

private meta def decodeRawSec (e : Expr) : MetaM DecRawSec := do
  let c ← unfoldToCtor ``RawSec.mk 9 e
  let bytesE := c.getArg! 1
  let relocsE := c.getArg! 8
  return {
    name := ← decodeStrVal (c.getArg! 0)
    bytesE
    size := ← decodeNatVal (c.getArg! 2)
    align := ← decodeNatVal (c.getArg! 3)
    isExec := ← decodeBoolVal (c.getArg! 4)
    readOnly := ← decodeBoolVal (c.getArg! 5)
    isNobits := ← decodeBoolVal (c.getArg! 6)
    isTls := ← decodeBoolVal (c.getArg! 7)
    relocs := ← (← decodeListElems relocsE).mapM decodeRawReloc
    relocsE
  }

private meta def decodeRawSym (e : Expr) : MetaM DecRawSym := do
  let c ← unfoldToCtor ``RawSym.mk 7 e
  return {
    rawName := ← decodeStrVal (c.getArg! 0)
    name := ← decodeStrVal (c.getArg! 1)
    sec := ← decodeSymSec (c.getArg! 2)
    value := ← decodeNatVal (c.getArg! 3)
    size := ← decodeNatVal (c.getArg! 4)
    kind := ← decodeSymKind (c.getArg! 5)
    bind := ← decodeSymBind (c.getArg! 6)
  }

private meta def decodeExtractedObj (e : Expr) : MetaM DecObj := do
  let c ← unfoldToCtor ``ExtractedObj.mk 4 e
  return {
    name := ← decodeStrVal (c.getArg! 0)
    sections := ← (← decodeListElems (c.getArg! 1)).mapM decodeRawSec
    symbols := ← (← decodeListElems (c.getArg! 2)).mapM decodeRawSym
    groupsE := c.getArg! 3
  }

private meta def decodeRelocEntry (e : Expr) : MetaM DecReloc := do
  let c ← unfoldToCtor ``RelocEntry.mk 5 e
  let (kindName, kindE) ← decodeRelocKindName (c.getArg! 1)
  return {
    off := ← decodeNatVal (c.getArg! 0)
    kindName, kindE
    sym := ← decodeStrVal (c.getArg! 2)
    addend := ← decodeIntVal (c.getArg! 3)
    localSym := ← decodeBoolVal (c.getArg! 4)
  }

private meta def decodeCodeBlock (e : Expr) : MetaM DecBlock := do
  let c ← unfoldToCtor ``CodeBlock.mk 6 e
  let codeE := c.getArg! 0
  return {
    code := ← decodeBytes codeE
    codeE
    align := ← decodeNatVal (c.getArg! 1)
    symbols := ← (← decodeListElems (c.getArg! 2)).mapM fun p => do
      let pc ← unfoldToCtor ``Prod.mk 4 p
      pure (← decodeStrVal (pc.getArg! 2), ← decodeNatVal (pc.getArg! 3))
    relocs := ← (← decodeListElems (c.getArg! 3)).mapM decodeRelocEntry
    externs := ← (← decodeListElems (c.getArg! 4)).mapM decodeStrVal
    weakRefs := ← (← decodeListElems (c.getArg! 5)).mapM decodeStrVal
  }

private meta def decodeSymDataInfo (e : Expr) : MetaM DecData := do
  let c ← unfoldToCtor ``SymDataInfo.mk 6 e
  let bytesE := c.getArg! 3
  return {
    sym := ← decodeStrVal (c.getArg! 0)
    align := ← decodeNatVal (c.getArg! 1)
    readOnly := ← decodeBoolVal (c.getArg! 2)
    bytesLen := (← decodeListElems bytesE).size
    bytesE
    zeroTail := ← decodeNatVal (c.getArg! 4)
    relocs := ← (← decodeListElems (c.getArg! 5)).mapM decodeRelocEntry
  }

private meta def decodeMultiPlacedLib (e : Expr) : MetaM DecMultiLib := do
  let c ← unfoldToCtor ``MultiPlacedLib.mk 5 e
  return {
    name := ← decodeStrVal (c.getArg! 0)
    blocks := ← (← decodeListElems (c.getArg! 1)).mapM decodeCodeBlock
    data := ← (← decodeListElems (c.getArg! 2)).mapM decodeSymDataInfo
    exports := ← (← decodeListElems (c.getArg! 3)).mapM decodeStrVal
    exportSyms := ← (← decodeListElems (c.getArg! 4)).mapM fun p => do
      let pc ← unfoldToCtor ``Prod.mk 4 p
      pure (← decodeStrVal (pc.getArg! 2), ← decodeStrVal (pc.getArg! 3))
  }

private meta def bytesSubEq (sec : ByteArray) (start : Nat) (sub : ByteArray) : Bool := Id.run do
  if start + sub.size > sec.size then return false
  for i in [:sub.size] do
    if sec[start + i]! != sub[i]! then return false
  return true

private meta def sliceFreeIn (claimed : Array (Nat × Nat)) (start len : Nat) : Bool :=
  claimed.all fun (s, l) => start + len ≤ s || s + l ≤ start

private meta def rawRelocOffsetsMatch (sec : DecRawSec) (start len : Nat) (rs : Array DecReloc) : Bool := Id.run do
  let rawOffs := (sec.relocs.filter fun rr => start ≤ rr.off && rr.off < start + len).map
    (fun rr => rr.off - start)
  if rawOffs.size != rs.size then return false
  return rawOffs.qsort (· < ·) == (rs.map (·.off)).qsort (· < ·)

private meta def symDerivedFrom (sym base objName : String) : Bool :=
  sym == base || sym == s!"{base} [{objName}]"

private meta def addPrebuiltDef (declName : Name) (ty val : Expr) : TermElabM Unit := do
  let env ← getEnv
  addDecl (.defnDecl {
    name := declName
    levelParams := []
    type := ty
    value := val
    hints := .regular (getMaxHeight env val + 1)
    safety := .safe
  }) (forceExpose := true)
  modifyEnv (addNoncomputable · declName)

private meta def mkBoolE (b : Bool) : Expr :=
  Lean.mkConst (if b then ``Bool.true else ``Bool.false)

private meta def mkListE (ty : Expr) (xs : Array Expr) : Expr :=
  xs.foldr (fun x acc => mkApp3 (Lean.mkConst ``List.cons [0]) ty x acc)
    (mkApp (Lean.mkConst ``List.nil [0]) ty)

private meta def mkOptE (ty : Expr) : Option Expr → Expr
  | none => mkApp (Lean.mkConst ``Option.none [0]) ty
  | some e => mkApp2 (Lean.mkConst ``Option.some [0]) ty e

private meta def mkPairE (t1 t2 e1 e2 : Expr) : Expr :=
  mkApp4 (Lean.mkConst ``Prod.mk [0, 0]) t1 t2 e1 e2

private meta def mkSymBindE : SymBind → Expr
  | .local => Lean.mkConst ``SymBind.local
  | .global => Lean.mkConst ``SymBind.global
  | .weak => Lean.mkConst ``SymBind.weak
  | .other => Lean.mkConst ``SymBind.other

private meta def mkSymKindE : SymKind → Expr
  | .func => Lean.mkConst ``SymKind.func
  | .object => Lean.mkConst ``SymKind.object
  | .tls => Lean.mkConst ``SymKind.tls
  | .section => Lean.mkConst ``SymKind.section
  | .other => Lean.mkConst ``SymKind.other

private meta def mkSymSecE : SymSec → Expr
  | .undef => Lean.mkConst ``SymSec.undef
  | .sec idx => mkApp (Lean.mkConst ``SymSec.sec) (mkRawNatLit idx)
  | .other => Lean.mkConst ``SymSec.other

private meta def mkSliceOriginE (o : SliceOrigin) : Expr :=
  mkApp4 (Lean.mkConst ``SliceOrigin.mk)
    (mkRawNatLit o.oi) (mkRawNatLit o.si) (mkRawNatLit o.start) (mkRawNatLit o.len)

private meta def mkSymRoleE : MSymRole → Expr
  | .other => Lean.mkConst ``SymRole.other
  | .blockSym bi j off =>
    mkApp3 (Lean.mkConst ``SymRole.blockSym) (mkRawNatLit bi) (mkRawNatLit j) (mkRawNatLit off)
  | .dataSym di => mkApp (Lean.mkConst ``SymRole.dataSym) (mkRawNatLit di)

private meta def mkRawIdStatusE : MRawIdStatus → Expr
  | .other => Lean.mkConst ``RawIdStatus.other
  | .globalDef oi k si =>
    mkApp3 (Lean.mkConst ``RawIdStatus.globalDef) (mkRawNatLit oi) (mkRawNatLit k) (mkRawNatLit si)
  | .allNonLocalUndef => Lean.mkConst ``RawIdStatus.allNonLocalUndef
  | .weakOnlyUndef wOi wKi =>
    mkApp2 (Lean.mkConst ``RawIdStatus.weakOnlyUndef) (mkRawNatLit wOi) (mkRawNatLit wKi)

/-- Checks that every interned object's COMDAT groups have empty member lists (`¬Discarded`). -/
def checkIObjsGroupsEmptyB (objsTree : IdxTree IObj) : Bool :=
  objsTree.all fun io => io.groups.all fun g => g.members.isEmpty

local syntax (name := genCliLabelsFromObjectsCert)
  "gen_cli_labels_from_objects_cert " ident term:max term:max : command

@[local command_elab genCliLabelsFromObjectsCert]
private meta def elabGenCliLabelsFromObjectsCert : CommandElab := fun stx => do
  match stx with
  | `(gen_cli_labels_from_objects_cert $thmId:ident $objsTerm:term $libTerm:term) =>
    let currNs ← getCurrNamespace
    let base := thmId.getId
    let mkHelper (sfx : String) : Name × Name × Ident :=
      let s := base.appendAfter sfx
      (s, currNs ++ s, mkIdentFrom thmId s)
    let (_, _, nConstId) := mkHelper "_N"
    let (_, _, bConstId) := mkHelper "_B"
    let (_, _, dConstId) := mkHelper "_D"
    let (_, namesTreeFull, namesTreeId) := mkHelper "_namesTree"
    let (_, charsTreeFull, charsTreeId) := mkHelper "_charsTree"
    let (_, objsTreeFull, objsTreeId) := mkHelper "_objsTree"
    let (_, iLibFull, iLibId) := mkHelper "_iLib"
    let (_, bOTreeFull, bOTreeId) := mkHelper "_bOTree"
    let (_, dOTreeFull, dOTreeId) := mkHelper "_dOTree"
    let (_, symRoleFull, symRoleId) := mkHelper "_symRole"
    let (_, rawSummaryFull, rawSummaryId) := mkHelper "_rawSummary"
    let (_, rawClaimedFull, _) := mkHelper "_rawClaimed"
    let (_, textGroupsFull, textGroupsId) := mkHelper "_textGroups"
    let (_, dataGroupsFull, dataGroupsId) := mkHelper "_dataGroups"
    let (_, textToGroupFull, textToGroupId) := mkHelper "_textToGroup"
    let (_, dataToGroupFull, dataToGroupId) := mkHelper "_dataToGroup"
    let (_, branchCalledFull, branchCalledId) := mkHelper "_branchCalled"
    let (_, commonExtSetFull, commonExtSetId) := mkHelper "_commonExtSet"
    let (_, _, hszId) := mkHelper "_names_sz"
    let (_, _, hcszId) := mkHelper "_chars_sz"
    let (_, _, hnamesEqId) := mkHelper "_names_eq"
    let (_, _, hnnId) := mkHelper "_names_nodup"
    let (_, _, h0Id) := mkHelper "_names_zero"
    let (_, _, hBId) := mkHelper "_blocks_sz"
    let (_, _, hDId) := mkHelper "_data_sz"
    let (_, _, hrolesId) := mkHelper "_roles_ok"
    let (_, _, hgroupsId) := mkHelper "_groups_ok"
    let (_, _, hbdisjId) := mkHelper "_bdisj_ok"
    let (_, _, hddisjId) := mkHelper "_ddisj_ok"
    let (_, _, hexportsId) := mkHelper "_exports_ok"
    let (_, _, hexternsId) := mkHelper "_externs_ok"

    let (numNames, numBlocks, numData) ← liftTermElabM do
      let listObjTy := mkApp (Lean.mkConst ``List [0]) (Lean.mkConst ``ExtractedObj)
      let objsE ← instantiateMVars (← elabTerm objsTerm (some listObjTy))
      let libE ← instantiateMVars (← elabTerm libTerm (some (Lean.mkConst ``MultiPlacedLib)))
      let objElemEs ← (decodeListElems objsE : MetaM _)
      let objs ← (objElemEs.mapM decodeExtractedObj : MetaM _)
      let lib ← (decodeMultiPlacedLib libE : MetaM _)

      -- Build sorted interned string table ("" at index 0).
      let mut strSet : Std.HashSet String := {}
      strSet := strSet.insert ""
      strSet := strSet.insert lib.name
      for e in lib.exports do strSet := strSet.insert e
      for (a, b) in lib.exportSyms do strSet := (strSet.insert a).insert b
      for blk in lib.blocks do
        for (s, _) in blk.symbols do strSet := strSet.insert s
        for r in blk.relocs do strSet := strSet.insert r.sym
        for x in blk.externs do strSet := strSet.insert x
        for w in blk.weakRefs do strSet := strSet.insert w
      for d in lib.data do
        strSet := strSet.insert d.sym
        for r in d.relocs do strSet := strSet.insert r.sym
      for obj in objs do
        strSet := strSet.insert obj.name
        for sec in obj.sections do strSet := strSet.insert sec.name
        for sy in obj.symbols do
          strSet := (strSet.insert sy.rawName).insert sy.name
          if sy.rawName != "" then strSet := strSet.insert s!"{sy.name} [{obj.name}]"

      let mut nameItems : Array (List Char × String) := Array.mkEmpty strSet.size
      for s in strSet do nameItems := nameItems.push (s.toList, s)
      let sortedNames := nameItems.qsort fun a b => charListLt a.1 b.1
      let N := sortedNames.size
      let mut strToId : Std.HashMap String Nat := {}
      for i in [:N] do strToId := strToId.insert sortedNames[i]!.2 i
      let idOf (s : String) : Nat := strToId[s]!

      -- Synthesize `symRole`, `rawClaimed`, and `rawSummary`.
      let B := lib.blocks.size
      let D := lib.data.size
      if B != 624 || D != 1248 then
        throwError "gen_cli_labels_from_objects_cert: expected B=624, D=1248, got B={B}, D={D}"
      let mut symRoleArr : Array MSymRole := Array.replicate N .other
      for bi in [:B] do
        let blk := lib.blocks[bi]!
        for j in [:blk.symbols.size] do
          let (s, off) := blk.symbols[j]!
          let sid := idOf s
          if symRoleArr[sid]! != .other then
            throwError "gen_cli_labels_from_objects_cert: duplicate block symbol {repr s}"
          symRoleArr := symRoleArr.set! sid (.blockSym bi j off)
      for di in [:D] do
        let sid := idOf lib.data[di]!.sym
        if symRoleArr[sid]! != .other then
          throwError "gen_cli_labels_from_objects_cert: colliding data symbol {repr lib.data[di]!.sym}"
        symRoleArr := symRoleArr.set! sid (.dataSym di)

      let mut rawClaimedArr : Array Bool := Array.replicate N false
      for obj in objs do
        for sy in obj.symbols do
          if sy.rawName != "" then
            rawClaimedArr := rawClaimedArr.set! (idOf sy.rawName) true
            rawClaimedArr := rawClaimedArr.set! (idOf sy.name) true
            rawClaimedArr := rawClaimedArr.set! (idOf s!"{sy.name} [{obj.name}]") true

      let mut rawOccs : Array (Array (Nat × Nat × DecRawSym)) := Array.replicate N #[]
      for oi in [:objs.size] do
        let obj := objs[oi]!
        for k in [:obj.symbols.size] do
          let sy := obj.symbols[k]!
          let rid := idOf sy.rawName
          if rid != 0 then rawOccs := rawOccs.set! rid (rawOccs[rid]!.push (oi, k, sy))
      let mut rawSummaryArr : Array MRawIdStatus := Array.replicate N .other
      for rid in [1:N] do
        let occs := rawOccs[rid]!
        if !occs.isEmpty then
          let nonLocalDefs := occs.filter fun (_, _, sy) => sy.bind != .local && sy.sec != .undef
          if nonLocalDefs.size == 1 then
            let (oi, k, sy) := nonLocalDefs[0]!
            if sy.bind == .global || sy.bind == .weak then
              if let .sec si := sy.sec then
                rawSummaryArr := rawSummaryArr.set! rid (.globalDef oi k si)
          else if nonLocalDefs.isEmpty then
            let weakWit? := occs.findSome? fun (oi, k, sy) =>
              if sy.sec == .undef && sy.bind == .weak then some (oi, k) else none
            let allWeakOk := occs.all fun (_, _, sy) =>
              (if sy.sec == .undef then sy.bind == .weak else true) &&
              (match sy.sec with | .sec _ => false | _ => true)
            match weakWit?, allWeakOk with
            | some (wOi, wKi), true => rawSummaryArr := rawSummaryArr.set! rid (.weakOnlyUndef wOi wKi)
            | _, _ => rawSummaryArr := rawSummaryArr.set! rid .allNonLocalUndef

      -- Synthesize `bO` with uniqueness guard across objects, sections, and symbols.
      let mut claimedText : Std.HashMap (Nat × Nat) (Array (Nat × Nat)) := {}
      let mut bOArr : Array SliceOrigin := Array.mkEmpty B
      let mut blkSymWits : Array (Array (Nat × Nat × Option Nat)) := Array.mkEmpty B
      for bi in [:B] do
        let blk := lib.blocks[bi]!
        let len := blk.code.size
        let mut found? : Option SliceOrigin := none
        for (sym0, off0) in blk.symbols do
          for oi in [:objs.size] do
            let obj := objs[oi]!
            for sy in obj.symbols do
              if let .sec si := sy.sec then
                if sy.kind == .func && sy.rawName != "" && sy.value ≥ off0 &&
                   symDerivedFrom sym0 sy.name obj.name && si < obj.sections.size then
                  let sec := obj.sections[si]!
                  let start := sy.value - off0
                  let prev := claimedText.getD (oi, si) #[]
                  if sec.isExec && sec.readOnly && !sec.isNobits && !sec.isTls &&
                     len > 0 && start % 4 == 0 && len % 4 == 0 &&
                     start + len ≤ sec.size &&
                     sec.align > 0 && blk.align % Nat.gcd sec.align start == 0 &&
                     sliceFreeIn prev start len &&
                     rawRelocOffsetsMatch sec start len blk.relocs then
                    let secBytes ← decodeBytes sec.bytesE
                    if secBytes.size == sec.size && bytesSubEq secBytes start blk.code then
                      let cand : SliceOrigin := { oi, si, start, len }
                      match found? with
                      | none => found? := some cand
                      | some prevOrig =>
                        if prevOrig != cand then
                          throwError "gen_cli_labels_from_objects_cert: ambiguous SliceOrigin for block {bi}"
        let some o := found?
          | throwError "gen_cli_labels_from_objects_cert: could not locate SliceOrigin for block {bi}"
        bOArr := bOArr.push o
        claimedText := claimedText.insert (o.oi, o.si)
          ((claimedText.getD (o.oi, o.si) #[]).push (o.start, o.len))
        let obj := objs[o.oi]!
        let mut swArr : Array (Nat × Nat × Option Nat) := Array.mkEmpty blk.symbols.size
        for (sym, off) in blk.symbols do
          let sid := idOf sym
          let mut wit? : Option Nat := none
          for k in [:obj.symbols.size] do
            if wit?.isNone then
              let sy := obj.symbols[k]!
              if sy.kind == .func && sy.sec == .sec o.si && sy.rawName != "" &&
                 sy.value == o.start + off && symDerivedFrom sym sy.name obj.name then
                wit? := some k
          swArr := swArr.push (sid, off, wit?)
        blkSymWits := blkSymWits.push swArr
      if bOArr.size != 624 then
        throwError "gen_cli_labels_from_objects_cert: expected 624 bO origins, got {bOArr.size}"

      -- Synthesize `dO` via relocation BFS from `bO` with uniqueness guard.
      let resolveRawTarget (oi : Nat) (rr : DecRawReloc) : Option (Nat × Nat × Int) :=
        if rr.symIdx < objs[oi]!.symbols.size then
          let sy := objs[oi]!.symbols[rr.symIdx]!
          match sy.sec with
          | .sec sj =>
            if sy.bind == .local then
              some (oi, sj, (sy.value : Int) + rr.addend)
            else
              match rawSummaryArr[idOf sy.rawName]! with
              | .globalDef oj gk sj' =>
                if oj == oi && gk == rr.symIdx && sj' == sj then
                  some (oi, sj, (sy.value : Int) + rr.addend)
                else none
              | _ => none
          | .undef =>
            if sy.bind == .local then none
            else
              match rawSummaryArr[idOf sy.rawName]! with
              | .globalDef oj gk sj => some (oj, sj, (objs[oj]!.symbols[gk]!.value : Int) + rr.addend)
              | _ => none
          | .other => none
        else none

      let mut dOOpt : Array (Option SliceOrigin) := Array.replicate D none
      let mut bfsQueue : Array Nat := #[]
      let enqueueFromSlice (o : SliceOrigin) (rs : Array DecReloc)
          (dOOpt : Array (Option SliceOrigin)) (bfsQueue : Array Nat) :
          MetaM (Array (Option SliceOrigin) × Array Nat) := do
        let sec := objs[o.oi]!.sections[o.si]!
        let raw := sec.relocs.filter fun rr => o.start ≤ rr.off && rr.off < o.start + o.len
        let mut dOOpt := dOOpt
        let mut bfsQueue := bfsQueue
        for r in rs do
          if let .dataSym di := symRoleArr[idOf r.sym]! then
            for rr in raw do
              if r.off + o.start == rr.off && rr.kindName? == some r.kindName then
                if let some (oj, sj, t) := resolveRawTarget o.oi rr then
                  let secT := objs[oj]!.sections[sj]!
                  let d := lib.data[di]!
                  let len := if secT.isNobits then d.zeroTail else d.bytesLen
                  let startInt := t - r.addend
                  if startInt ≥ 0 then
                    let want : SliceOrigin := { oi := oj, si := sj, start := startInt.toNat, len }
                    match dOOpt[di]! with
                    | none =>
                      dOOpt := dOOpt.set! di (some want)
                      bfsQueue := bfsQueue.push di
                    | some prev =>
                      if prev != want then
                        throwError "gen_cli_labels_from_objects_cert: conflicting origins for data[{di}]"
        return (dOOpt, bfsQueue)

      for bi in [:B] do
        let (dOOpt', q') ← enqueueFromSlice bOArr[bi]! lib.blocks[bi]!.relocs dOOpt bfsQueue
        dOOpt := dOOpt'; bfsQueue := q'
      let mut qIdx := 0
      while qIdx < bfsQueue.size do
        let di := bfsQueue[qIdx]!
        qIdx := qIdx + 1
        let (dOOpt', q') ← enqueueFromSlice (dOOpt[di]!.get!) lib.data[di]!.relocs dOOpt bfsQueue
        dOOpt := dOOpt'; bfsQueue := q'

      let mut dOArr : Array SliceOrigin := Array.mkEmpty D
      let mut dataCovWits : Array (Option Nat) := Array.mkEmpty D
      for di in [:D] do
        let d := lib.data[di]!
        let some o := dOOpt[di]!
          | throwError "gen_cli_labels_from_objects_cert: unreached data[{di}] ({repr d.sym})"
        let obj := objs[o.oi]!
        let mut covWit : Option Nat := none
        for k in [:obj.symbols.size] do
          if covWit.isNone then
            let sy := obj.symbols[k]!
            if sy.kind == .object && sy.sec == .sec o.si && sy.value == o.start &&
               sy.size == o.len && sy.rawName != "" && symDerivedFrom d.sym sy.name obj.name then
              covWit := some k
        dOArr := dOArr.push o
        dataCovWits := dataCovWits.push covWit
      if dOArr.size != 1248 then
        throwError "gen_cli_labels_from_objects_cert: expected 1248 dO origins, got {dOArr.size}"

      -- Build relocation permutations and TLS symbol witnesses.
      let matchSliceRelocs (sliceLabel : String) (o : SliceOrigin) (rs : Array DecReloc) :
          MetaM (Array Nat × Array Nat × Array Nat) := do
        let obj := objs[o.oi]!
        let sec := obj.sections[o.si]!
        let raw := sec.relocs.filter fun rr => o.start ≤ rr.off && rr.off < o.start + o.len
        if raw.size != rs.size then
          throwError "gen_cli_labels_from_objects_cert: {sliceLabel} reloc count mismatch"
        let mut tlsWits : Array Nat := Array.replicate rs.size 0
        let mut perm : Array Nat := Array.mkEmpty raw.size
        let mut invPerm : Array Nat := Array.replicate raw.size 0
        let mut used : Array Bool := Array.replicate rs.size false
        for k in [:raw.size] do
          let rr := raw[k]!
          let mut hit? : Option (Nat × Nat) := none
          for pk in [:rs.size] do
            if hit?.isNone && !used[pk]! then
              let r := rs[pk]!
              if r.off + o.start == rr.off && rr.kindName? == some r.kindName &&
                 rr.symIdx < obj.symbols.size then
                let sy := obj.symbols[rr.symIdx]!
                let rSymId := idOf r.sym
                match resolveRawTarget o.oi rr with
                | some (oj, sj, t) =>
                  if oj < objs.size && sj < objs[oj]!.sections.size then
                    let ojObj := objs[oj]!
                    let secT := ojObj.sections[sj]!
                    if secT.isExec then
                      if let .blockSym bj _ off := symRoleArr[rSymId]! then
                        let bo := bOArr[bj]!
                        if bo.oi == oj && bo.si == sj &&
                           (0 : Int) ≤ (off : Int) + r.addend &&
                           (off : Int) + r.addend ≤ (bo.len : Int) &&
                           ((bo.start + off : Int) + r.addend) == t then
                          hit? := some (pk, 0)
                    else if !secT.isTls then
                      if let .dataSym dj := symRoleArr[rSymId]! then
                        let do_ := dOArr[dj]!
                        if do_.oi == oj && do_.si == sj &&
                           (0 : Int) ≤ r.addend && r.addend ≤ (do_.len : Int) &&
                           ((do_.start : Int) + r.addend) == t then
                          hit? := some (pk, 0)
                    else if symRoleArr[rSymId]! == .other then
                      for tk in [:ojObj.symbols.size] do
                        if hit?.isNone then
                          let ts := ojObj.symbols[tk]!
                          if ts.sec == .sec sj && ts.kind == .tls && ts.rawName != "" &&
                             r.sym == ts.rawName && ((ts.value : Int) + r.addend) == t then
                            hit? := some (pk, tk)
                | none =>
                  if sy.sec == .undef && sy.rawName == r.sym && rSymId != 0 &&
                     r.addend == rr.addend && symRoleArr[rSymId]! == .other then
                    match rawSummaryArr[rSymId]! with
                    | .allNonLocalUndef | .weakOnlyUndef _ _ => hit? := some (pk, 0)
                    | _ => pure ()
          let some (pk, tw) := hit?
            | throwError "gen_cli_labels_from_objects_cert: {sliceLabel} raw reloc #{k} at off={rr.off} unmatched"
          used := used.set! pk true
          perm := perm.push pk
          invPerm := invPerm.set! pk k
          tlsWits := tlsWits.set! pk tw
        return (perm, invPerm, tlsWits)

      let mut blkPerms : Array (Array Nat × Array Nat × Array Nat) := Array.mkEmpty B
      for bi in [:B] do
        blkPerms := blkPerms.push (← matchSliceRelocs s!"block[{bi}]" bOArr[bi]! lib.blocks[bi]!.relocs)
      let mut dataPerms : Array (Array Nat × Array Nat × Array Nat) := Array.mkEmpty D
      for di in [:D] do
        dataPerms := dataPerms.push (← matchSliceRelocs s!"data[{di}]" dOArr[di]! lib.data[di]!.relocs)

      -- Build sorted `SliceGroup`s and `toGroup` inverse maps.
      let buildGroups (origins : Array SliceOrigin) :
          Array (Nat × Nat × Array Nat) × Array (Nat × Nat) := Id.run do
        let M := origins.size
        let mut bySec : Std.HashMap (Nat × Nat) (Array Nat) := {}
        for i in [:M] do
          let o := origins[i]!
          bySec := bySec.insert (o.oi, o.si) ((bySec.getD (o.oi, o.si) #[]).push i)
        let mut keys : Array (Nat × Nat) := Array.mkEmpty bySec.size
        for (k, _) in bySec do keys := keys.push k
        let sortedKeys := keys.qsort fun a b => if a.1 == b.1 then a.2 < b.2 else a.1 < b.1
        let mut groups : Array (Nat × Nat × Array Nat) := Array.mkEmpty sortedKeys.size
        let mut toGroup : Array (Nat × Nat) := Array.replicate M (0, 0)
        for gi in [:sortedKeys.size] do
          let (oi, si) := sortedKeys[gi]!
          let sortedIdxs := bySec[(oi, si)]!.qsort fun i1 i2 =>
            let o1 := origins[i1]!; let o2 := origins[i2]!
            if o1.start == o2.start then o1.len < o2.len else o1.start < o2.start
          for pi in [:sortedIdxs.size] do toGroup := toGroup.set! sortedIdxs[pi]! (gi, pi)
          groups := groups.push (oi, si, sortedIdxs)
        return (groups, toGroup)

      let (tGroups, tToGroup) := buildGroups bOArr
      let (dGroups, dToGroup) := buildGroups dOArr

      -- Build `commonExterns`, `commonWeakRefs`, `commonExtSet`, and `branchCalled`.
      let commonExterns : Array Nat := if B > 0 then lib.blocks[0]!.externs.map idOf else #[]
      let commonWeakRefs : Array Nat := if B > 0 then lib.blocks[0]!.weakRefs.map idOf else #[]
      let mut commonExtSetArr : Array Bool := Array.replicate N false
      for eid in commonExterns do commonExtSetArr := commonExtSetArr.set! eid true
      let mut branchCalledArr : Array (Option (Nat × Nat)) := Array.replicate N none
      for bi in [:B] do
        let blk := lib.blocks[bi]!
        for ri in [:blk.relocs.size] do
          let r := blk.relocs[ri]!
          if r.kindName == ``RelocKind.call26 || r.kindName == ``RelocKind.jump26 then
            let sid := idOf r.sym
            if branchCalledArr[sid]!.isNone then branchCalledArr := branchCalledArr.set! sid (some (bi, ri))

      -- Emit exposed prebuilt `IdxTree` and `IMultiLib` definitions.
      let mkTreeTy (t : Expr) := mkApp (Lean.mkConst ``IdxTree [0]) t
      let natTy := Lean.mkConst ``Nat
      let boolTy := Lean.mkConst ``Bool
      let strTy := Lean.mkConst ``String
      let listCharTy := mkApp (Lean.mkConst ``List [0]) (Lean.mkConst ``Char)
      let listNatTy := mkApp (Lean.mkConst ``List [0]) natTy
      let optNatTy := mkApp (Lean.mkConst ``Option [0]) natTy
      let natOptNatTy := mkApp2 (Lean.mkConst ``Prod [0, 0]) natTy optNatTy
      let symTripleTy := mkApp2 (Lean.mkConst ``Prod [0, 0]) natTy natOptNatTy
      let natNatTy := mkApp2 (Lean.mkConst ``Prod [0, 0]) natTy natTy
      let optNatNatTy := mkApp (Lean.mkConst ``Option [0]) natNatTy
      let sliceOriginTy := Lean.mkConst ``SliceOrigin
      let iSymTy := Lean.mkConst ``ISym
      let iSecTy := Lean.mkConst ``ISec
      let iObjTy := Lean.mkConst ``IObj
      let iRelocTy := Lean.mkConst ``IReloc
      let iBlockTy := Lean.mkConst ``IBlock
      let iDataTy := Lean.mkConst ``IData
      let symRoleTy := Lean.mkConst ``SymRole
      let rawStatusTy := Lean.mkConst ``RawIdStatus
      let sliceGroupTy := Lean.mkConst ``SliceGroup

      let mkIdxTreeExpr := ProofLib.ProgramReflection.mkIdxTreeExpr
      let mkCharListExpr := ProofLib.ProgramReflection.mkCharListExpr
      Meta.resetCache

      addPrebuiltDef namesTreeFull (mkTreeTy strTy)
        (mkIdxTreeExpr Level.zero strTy (sortedNames.map fun (_, s) => mkStrLit s))
      addPrebuiltDef charsTreeFull (mkTreeTy listCharTy)
        (mkIdxTreeExpr Level.zero listCharTy (sortedNames.map fun (_, s) => mkCharListExpr s))

      let mut iObjExprs : Array Expr := Array.mkEmpty objs.size
      for oi in [:objs.size] do
        let obj := objs[oi]!
        let secExprs := obj.sections.map fun sec =>
          mkAppN (Lean.mkConst ``ISec.mk) #[
            mkRawNatLit (idOf sec.name),
            mkBoolE sec.isExec, mkBoolE sec.readOnly, mkBoolE sec.isNobits, mkBoolE sec.isTls,
            mkRawNatLit sec.align, mkRawNatLit sec.size, sec.bytesE, sec.relocsE]
        let symExprs := obj.symbols.map fun sy =>
          let rid := idOf sy.rawName
          let did := if rid != 0 then idOf s!"{sy.name} [{obj.name}]" else 0
          mkAppN (Lean.mkConst ``ISym.mk) #[
            mkRawNatLit rid, mkRawNatLit (idOf sy.name), mkRawNatLit did,
            mkSymBindE sy.bind, mkSymKindE sy.kind, mkSymSecE sy.sec,
            mkRawNatLit sy.value, mkRawNatLit sy.size]
        iObjExprs := iObjExprs.push (mkAppN (Lean.mkConst ``IObj.mk) #[
          mkRawNatLit (idOf obj.name), mkCharListExpr obj.name,
          mkIdxTreeExpr Level.zero iSecTy secExprs,
          mkIdxTreeExpr Level.zero iSymTy symExprs,
          obj.groupsE])
      addPrebuiltDef objsTreeFull (mkTreeTy iObjTy) (mkIdxTreeExpr Level.zero iObjTy iObjExprs)

      let mut iBlockExprs : Array Expr := Array.mkEmpty B
      for bi in [:B] do
        let blk := lib.blocks[bi]!
        let (perm, invPerm, tlsWits) := blkPerms[bi]!
        let swExprs := blkSymWits[bi]!.map fun (s, off, w?) =>
          mkPairE natTy natOptNatTy (mkRawNatLit s)
            (mkPairE natTy optNatTy (mkRawNatLit off) (mkOptE natTy (w?.map mkRawNatLit)))
        let mut relExprs : Array Expr := Array.mkEmpty blk.relocs.size
        for ri in [:blk.relocs.size] do
          let r := blk.relocs[ri]!
          relExprs := relExprs.push (mkAppN (Lean.mkConst ``IReloc.mk) #[
            mkRawNatLit r.off, r.kindE, mkRawNatLit (idOf r.sym),
            toExpr r.addend, mkBoolE r.localSym, mkRawNatLit tlsWits[ri]!])
        let extIds := blk.externs.map idOf
        let weakIds := blk.weakRefs.map idOf
        let extOvE := if extIds == commonExterns then mkOptE listNatTy none
          else mkOptE listNatTy (some (mkListE natTy (extIds.map mkRawNatLit)))
        let weakOvE := if weakIds == commonWeakRefs then mkOptE listNatTy none
          else mkOptE listNatTy (some (mkListE natTy (weakIds.map mkRawNatLit)))
        iBlockExprs := iBlockExprs.push (mkAppN (Lean.mkConst ``IBlock.mk) #[
          blk.codeE, mkRawNatLit blk.align, mkListE symTripleTy swExprs,
          mkIdxTreeExpr Level.zero iRelocTy relExprs, extOvE, weakOvE,
          mkListE natTy (perm.map mkRawNatLit),
          mkIdxTreeExpr Level.zero natTy (invPerm.map mkRawNatLit)])

      let mut iDataExprs : Array Expr := Array.mkEmpty D
      for di in [:D] do
        let d := lib.data[di]!
        let (perm, invPerm, tlsWits) := dataPerms[di]!
        let mut relExprs : Array Expr := Array.mkEmpty d.relocs.size
        for ri in [:d.relocs.size] do
          let r := d.relocs[ri]!
          relExprs := relExprs.push (mkAppN (Lean.mkConst ``IReloc.mk) #[
            mkRawNatLit r.off, r.kindE, mkRawNatLit (idOf r.sym),
            toExpr r.addend, mkBoolE r.localSym, mkRawNatLit tlsWits[ri]!])
        iDataExprs := iDataExprs.push (mkAppN (Lean.mkConst ``IData.mk) #[
          mkRawNatLit (idOf d.sym), mkRawNatLit d.align, mkBoolE d.readOnly,
          d.bytesE, mkRawNatLit d.zeroTail,
          mkIdxTreeExpr Level.zero iRelocTy relExprs,
          mkOptE natTy (dataCovWits[di]!.map mkRawNatLit),
          mkListE natTy (perm.map mkRawNatLit),
          mkIdxTreeExpr Level.zero natTy (invPerm.map mkRawNatLit)])

      addPrebuiltDef iLibFull (Lean.mkConst ``IMultiLib) (mkAppN (Lean.mkConst ``IMultiLib.mk) #[
        mkRawNatLit (idOf lib.name),
        mkListE natTy (commonExterns.map mkRawNatLit),
        mkListE natTy (commonWeakRefs.map mkRawNatLit),
        mkIdxTreeExpr Level.zero iBlockTy iBlockExprs,
        mkIdxTreeExpr Level.zero iDataTy iDataExprs,
        mkListE natTy (lib.exports.map (mkRawNatLit ∘ idOf)),
        mkListE natNatTy (lib.exportSyms.map fun (a, b) =>
          mkPairE natTy natTy (mkRawNatLit (idOf a)) (mkRawNatLit (idOf b)))])

      addPrebuiltDef bOTreeFull (mkTreeTy sliceOriginTy)
        (mkIdxTreeExpr Level.zero sliceOriginTy (bOArr.map mkSliceOriginE))
      addPrebuiltDef dOTreeFull (mkTreeTy sliceOriginTy)
        (mkIdxTreeExpr Level.zero sliceOriginTy (dOArr.map mkSliceOriginE))
      addPrebuiltDef symRoleFull (mkTreeTy symRoleTy)
        (mkIdxTreeExpr Level.zero symRoleTy (symRoleArr.map mkSymRoleE))
      addPrebuiltDef rawSummaryFull (mkTreeTy rawStatusTy)
        (mkIdxTreeExpr Level.zero rawStatusTy (rawSummaryArr.map mkRawIdStatusE))
      addPrebuiltDef rawClaimedFull (mkTreeTy boolTy)
        (mkIdxTreeExpr Level.zero boolTy (rawClaimedArr.map mkBoolE))

      let mkGroupExprs (gs : Array (Nat × Nat × Array Nat)) : Array Expr :=
        gs.map fun (oi, si, idxs) =>
          mkApp3 (Lean.mkConst ``SliceGroup.mk) (mkRawNatLit oi) (mkRawNatLit si)
            (mkIdxTreeExpr Level.zero natTy (idxs.map mkRawNatLit))
      let mkToGroupExprs (tg : Array (Nat × Nat)) : Array Expr :=
        tg.map fun (gi, pi) => mkPairE natTy natTy (mkRawNatLit gi) (mkRawNatLit pi)

      addPrebuiltDef textGroupsFull (mkTreeTy sliceGroupTy)
        (mkIdxTreeExpr Level.zero sliceGroupTy (mkGroupExprs tGroups))
      addPrebuiltDef dataGroupsFull (mkTreeTy sliceGroupTy)
        (mkIdxTreeExpr Level.zero sliceGroupTy (mkGroupExprs dGroups))
      addPrebuiltDef textToGroupFull (mkTreeTy natNatTy)
        (mkIdxTreeExpr Level.zero natNatTy (mkToGroupExprs tToGroup))
      addPrebuiltDef dataToGroupFull (mkTreeTy natNatTy)
        (mkIdxTreeExpr Level.zero natNatTy (mkToGroupExprs dToGroup))
      addPrebuiltDef branchCalledFull (mkTreeTy optNatNatTy)
        (mkIdxTreeExpr Level.zero optNatNatTy (branchCalledArr.map fun w? =>
          mkOptE natNatTy (w?.map fun (bi, ri) => mkPairE natTy natTy (mkRawNatLit bi) (mkRawNatLit ri))))
      addPrebuiltDef commonExtSetFull (mkTreeTy boolTy)
        (mkIdxTreeExpr Level.zero boolTy (commonExtSetArr.map mkBoolE))

      return (N, B, D)

    let nLit := Syntax.mkNumLit (toString numNames)
    let bLit := Syntax.mkNumLit (toString numBlocks)
    let dLit := Syntax.mkNumLit (toString numData)

    elabCommand (← `(command| @[expose] def $nConstId : Nat := $nLit))
    elabCommand (← `(command| @[expose] def $bConstId : Nat := $bLit))
    elabCommand (← `(command| @[expose] def $dConstId : Nat := $dLit))

    elabCommand (← `(command|
      theorem $hszId : ($namesTreeId).size? = some $nConstId := by rfl_kernel))
    elabCommand (← `(command|
      theorem $hcszId : ($charsTreeId).size? = some $nConstId := by rfl_kernel))
    elabCommand (← `(command|
      theorem $hnamesEqId :
          ($namesTreeId).toList = ($charsTreeId).toList.map String.ofList := by rfl_kernel))
    elabCommand (← `(command|
      theorem $hnnId :
          Arm64.Obj.Interned.namesNodup ($charsTreeId).toList = true := by rfl_kernel))
    elabCommand (← `(command|
      theorem $h0Id : ($namesTreeId).get? 0 = some "" := by rfl_kernel))
    elabCommand (← `(command|
      theorem $hBId : ($iLibId).blocks.size? = some $bConstId := by rfl_kernel))
    elabCommand (← `(command|
      theorem $hDId : ($iLibId).data.size? = some $dConstId := by rfl_kernel))
    elabCommand (← `(command|
      theorem $hrolesId :
          Arm64.Obj.LabelsInterned.checkSymRolesB $nConstId $iLibId $symRoleId = true := by
        rfl_kernel))
    elabCommand (← `(command|
      theorem $hgroupsId :
          checkIObjsGroupsEmptyB $objsTreeId = true := by rfl_kernel))
    elabCommand (← `(command|
      theorem $hbdisjId :
          Arm64.Obj.LabelsInterned.checkGroupsDisjointB $bConstId $bOTreeId
            $textGroupsId $textToGroupId = true := by rfl_kernel))
    elabCommand (← `(command|
      theorem $hddisjId :
          Arm64.Obj.LabelsInterned.checkGroupsDisjointB $dConstId $dOTreeId
            $dataGroupsId $dataToGroupId = true := by rfl_kernel))
    elabCommand (← `(command|
      theorem $hexportsId :
          Arm64.Obj.LabelsInterned.checkIExportsB $nConstId $objsTreeId $iLibId
            $bOTreeId $symRoleId $rawSummaryId = true := by rfl_kernel))
    elabCommand (← `(command|
      theorem $hexternsId :
          Arm64.Obj.LabelsInterned.checkIExternsB $nConstId $iLibId $symRoleId $rawSummaryId
            $branchCalledId $commonExtSetId = true := by rfl_kernel))
  | _ => throwUnsupportedSyntax

set_option maxRecDepth 2000000 in
gen_cli_labels_from_objects_cert cliLabelsLfo cliLinkObjs libsignalSessionLib

end LibsignalBinary.Proofs.SpecLemmas.SignalSession.CliLabelsLfoCert
