/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Arm64
public import ProofLib.RelocDecode
public import ProofLib.ProgramReflection.IdxTree
public meta import ProofLib.ProgramReflection.IdxTree
public meta import Lean

/-!
# Generated `Relocs` and `Words` Literals for Relocated Functions

Elaborator commands extracting relocation tables and instruction-word templates from
`Obj.ObjectInfo.relocFns`, together with the `obj_mem` membership tactic:
- `gen_reloc_fn_index <idx> <obj>` certifies an `O(log F)` `Obj.RelocFnIndex <obj>` once per object.
- `gen_reloc_fn <prefix> <obj> "<sym>" [using <idx>] [in <image>]` emits `<prefix>Relocs`,
  `<prefix>Words`, `<prefix>_checked`, `<prefix>_check` (via `rfl_kernel` and `decide +kernel`),
  and optionally `<prefix>_mem : <obj> ∈ <image>.objects`.

```lean
gen_reloc_fn_index myLibObjIdx myLibObj
gen_reloc_fn myFn myLibObj "my_fn" in myLibImage
theorem myFn_ok {img} (hl : Obj.Loads myLibImage img) :
    (Program.ofImage img).subroutineOk "my_fn" mySpec :=
  Obj.Loads.subroutineOk_of_relocFn hl myFn_mem myFn_check fun a resolve hctx hrange hwords =>
    myFn_ok_abstract _ a resolve hctx hrange hwords
```
-/

@[expose] public meta section

namespace ProofLib.RelocFnGen

open Lean Elab Command Term Meta Arm64

/-- One relocation entry read back from an `Obj.RelocEntry` expression. -/
structure RelocLit where
  off : Nat
  kind : Name
  sym : String
  addend : Int
  localSym : Bool

/-- Elements of a `List` expression, reducing each spine cell with `whnf`. -/
partial def listElems (e : Expr) : MetaM (Array Expr) := do
  let rec go (e : Expr) (acc : Array Expr) : MetaM (Array Expr) := do
    let e ← whnf e
    if e.isAppOfArity ``List.cons 3 then go (e.getArg! 2) (acc.push (e.getArg! 1))
    else if e.isAppOfArity ``List.nil 1 then return acc
    else throwError "gen_reloc_fn: expected a concrete list, got{indentExpr e}"
  go e #[]

def natVal (e : Expr) : MetaM Nat := do
  if let some n := e.rawNatLit? then return n
  if let some n ← (evalNat e).run then return n
  let e ← whnf e
  match e.rawNatLit? with
  | some n => return n
  | none => throwError "gen_reloc_fn: expected a natural number literal, got{indentExpr e}"

def byteVal (e : Expr) : MetaM Nat := do
  if e.isAppOfArity ``BitVec.ofNat 2 then
    return (← natVal (e.getArg! 1)) % 256
  match ← getBitVecValue? e with
  | some ⟨8, v⟩ => return v.toNat
  | _ =>
    -- Computed bytes (e.g. `wordsToBytesLE ws`): reduce `BitVec.toNat e` to a literal.
    let n ← withTransparency .all <| reduce (mkApp2 (mkConst ``BitVec.toNat) (mkNatLit 8) e)
    match (← instantiateMVars n).rawNatLit? with
    | some n => return n % 256
    | none => match (← (evalNat n).run) with
      | some n => return n % 256
      | none => throwError "gen_reloc_fn: expected a `BitVec 8` literal, got{indentExpr e}"

def strVal (e : Expr) : MetaM String := do
  match (← whnf e) with
  | .lit (.strVal s) => return s
  | e => throwError "gen_reloc_fn: expected a string literal, got{indentExpr e}"

def intVal (e : Expr) : MetaM Int := do
  if let some i ← getIntValue? e then return i
  let e ← whnf e
  if e.isAppOfArity ``Int.ofNat 1 then return Int.ofNat (← natVal (e.getArg! 0))
  if e.isAppOfArity ``Int.negSucc 1 then return Int.negSucc (← natVal (e.getArg! 0))
  throwError "gen_reloc_fn: expected an integer literal, got{indentExpr e}"

def boolVal (e : Expr) : MetaM Bool := do
  let e ← whnf e
  if e.isConstOf ``Bool.true then return true
  if e.isConstOf ``Bool.false then return false
  throwError "gen_reloc_fn: expected a Boolean literal, got{indentExpr e}"

/-- Project field `f` out of `e` and reduce it to weak head normal form. -/
def field (f : Name) (e : Expr) : MetaM Expr := do
  whnf (← mkAppM f #[e])

def relocLit (e : Expr) : MetaM RelocLit := do
  let kind ← field ``Obj.RelocEntry.kind e
  let some kindName := kind.constName?
    | throwError "gen_reloc_fn: expected a `RelocKind` constructor, got{indentExpr kind}"
  return {
    off := ← natVal (← field ``Obj.RelocEntry.off e)
    kind := kindName
    sym := ← strVal (← field ``Obj.RelocEntry.sym e)
    addend := ← intVal (← field ``Obj.RelocEntry.addend e)
    localSym := ← boolVal (← field ``Obj.RelocEntry.localSym e) }

/-- Strip a trailing `" [<archive>]"` tag attached by the static linker to archive-local symbols,
    leaving the base symbol name (e.g. `"alpha_alloc [alpha_static]"` to `"alpha_alloc"`). -/
def stripArchiveSuffix (s : String) : String :=
  let parts := s.splitOn " ["
  if parts.length ≥ 2 then
    let last := parts.getLast?.getD ""
    if last.endsWith "]" && (last.splitOn "[").length == 1 then
      " [".intercalate parts.dropLast
    else s
  else s

/-- Strip leading underscores and trailing `.`-delimited compiler clone suffixes (`.part.0`,
    `.llvm.*`, `.cold`) for stem comparison. -/
def symbolStem (s : String) : String :=
  let noUnder := String.ofList (s.toList.dropWhile (· == '_'))
  let base := if noUnder.isEmpty then s else noUnder
  match base.splitOn "." with
  | h :: _ => if h.isEmpty then base else h
  | [] => base

def containsSubstr (haystack needle : String) : Bool :=
  !needle.isEmpty && (haystack.splitOn needle).length > 1

/-- Bounded Levenshtein edit distance on lowercase symbol strings. -/
def editDistance (a b : String) : Nat := Id.run do
  let xs := a.toList.toArray
  let ys := b.toList.toArray
  let m := xs.size
  let n := ys.size
  let mut prev := Array.range (n + 1)
  for i in [:m] do
    let mut curr := Array.replicate (n + 1) 0
    curr := curr.set! 0 (i + 1)
    for j in [:n] do
      let cost := if xs[i]! == ys[j]! then 0 else 1
      let del := prev[j + 1]! + 1
      let ins := curr[j]! + 1
      let sub := prev[j]! + cost
      curr := curr.set! (j + 1) (Nat.min del (Nat.min ins sub))
    prev := curr
  return prev[n]!

/-- Rank how closely `cand` matches `query` (`some 0` = exact, lower = closer, `none` = unrelated).
    Prioritizes exact, archive-stripped base-symbol, case-insensitive, stem, substring, and small
    edit-distance matches. -/
def symbolMatchRank? (query cand : String) : Option (Nat × Nat) :=
  let qBase := stripArchiveSuffix query
  let cBase := stripArchiveSuffix cand
  let qLow := qBase.toLower
  let cLow := cBase.toLower
  let qStem := symbolStem qLow
  let cStem := symbolStem cLow
  let lenDiff := Int.natAbs ((cBase.length : Int) - (qBase.length : Int))
  if cand == query then some (0, 0)
  else if !qBase.isEmpty && cBase == qBase then some (1, 0)
  else if cand.toLower == query.toLower || (!qLow.isEmpty && cLow == qLow) then some (2, lenDiff)
  else if !qStem.isEmpty && cStem == qStem then some (3, lenDiff)
  else if (qLow.length ≥ 3 && containsSubstr cLow qLow) ||
          (cLow.length ≥ 3 && containsSubstr qLow cLow) ||
          (qLow.length > 0 && qLow.length < 3 && (cLow.startsWith qLow || cLow.endsWith qLow)) then
    some (4, lenDiff)
  else if (qStem.length ≥ 3 && containsSubstr cStem qStem) ||
          (cStem.length ≥ 3 && containsSubstr qStem cStem) then
    some (5, lenDiff)
  else if qLow.length ≥ 4 && cLow.length ≥ 4 && lenDiff ≤ 3 &&
          editDistance qLow cLow ≤ Nat.max 2 (qLow.length / 4) then
    some (6, editDistance qLow cLow)
  else none

/-- Return close matches to `query` in `cands`, ordered from closest to furthest (preserving
    input order on ties) and deduplicated. -/
def rankSymbolMatches (query : String) (cands : Array String) (limit : Nat := 6) :
    Array (Nat × String) := Id.run do
  let mut scored : Array (Nat × Nat × Nat × String) := #[]
  for h : idx in [:cands.size] do
    let c := cands[idx]
    if let some (rank, dist) := symbolMatchRank? query c then
      scored := scored.push (rank, dist, idx, c)
  let sorted := scored.qsort fun (r1, d1, i1, _) (r2, d2, i2, _) =>
    r1 < r2 || (r1 == r2 && (d1 < d2 || (d1 == d2 && i1 < i2)))
  let mut out : Array (Nat × String) := #[]
  for (r, _, _, c) in sorted do
    if out.size < limit && !out.any (fun (_, prev) => prev == c) then
      out := out.push (r, c)
  return out

/-- Best-effort extraction of relocation-free symbol names from `obj.fns`. -/
def relocFreeFnNames (obj : Expr) : MetaM (Array String) := do
  try
    let entries ← listElems (← mkAppM ``Obj.ObjectInfo.fns #[obj])
    let mut res : Array String := #[]
    for entry in entries do
      try
        res := res.push (← strVal (← field ``Prod.fst entry))
      catch _ =>
        pure ()
    return res
  catch _ =>
    return #[]

/-- Find `sym` in `obj.relocFns`; return its 0-based index, relocations, and code bytes. -/
def findRelocFnIdx (obj : Expr) (sym : String) : MetaM (Nat × Array RelocLit × Array Nat) := do
  let fns ← listElems (← mkAppM ``Obj.ObjectInfo.relocFns #[obj])
  for h : idx in [:fns.size] do
    let fn := fns[idx]
    if (← strVal (← field ``Obj.SymCodeInfo.sym fn)) == sym then
      let relocs ← (← listElems (← mkAppM ``Obj.SymCodeInfo.relocs #[fn])).mapM relocLit
      let code ← (← listElems (← mkAppM ``Obj.SymCodeInfo.code #[fn])).mapM byteVal
      return (idx, relocs, code)
  let names ← fns.mapM fun fn => do strVal (← field ``Obj.SymCodeInfo.sym fn)
  let freeNames ← relocFreeFnNames obj
  let relocMatches := rankSymbolMatches sym names
  let freeMatches := rankSymbolMatches sym freeNames (limit := 1)
  let sampleAvail : String :=
    if names.size ≤ 8 then s!"available: [{", ".intercalate names.toList}]"
    else s!"available (first 8 of {names.size}): [{", ".intercalate (names.toList.take 8)}]"
  let bestRelocRank? := relocMatches[0]?.map (·.1)
  if let some (freeRank, freeSym) := freeMatches[0]? then
    let preferFreeNote :=
      freeRank == 0 ||
      match bestRelocRank? with
      | none => true
      | some relocRank => freeRank < relocRank
    if preferFreeNote then
      throwError "gen_reloc_fn: no `relocFns` entry named {repr sym}; {sampleAvail}\n\
        note: {repr freeSym} is already in obj.fns (relocation-free) — use obj.fns directly; gen_reloc_fn is not needed"
  if !relocMatches.isEmpty then
    let didYouMean := ", ".intercalate (relocMatches.toList.map (reprStr ·.2))
    throwError "gen_reloc_fn: no `relocFns` entry named {repr sym}; did you mean: [{didYouMean}]; {sampleAvail}"
  throwError "gen_reloc_fn: no `relocFns` entry named {repr sym}; {sampleAvail}"

/-- Find `sym` in `obj.relocFns`; return its relocations and code bytes. -/
def findRelocFn (obj : Expr) (sym : String) : MetaM (Array RelocLit × Array Nat) := do
  let (_, relocs, code) ← findRelocFnIdx obj sym
  return (relocs, code)

/-- Little-endian 32-bit words of `code` (length must be a positive multiple of 4). -/
def wordsOfBytes (code : Array Nat) : Except String (Array Nat) := do
  if code.size == 0 || code.size % 4 != 0 then
    throw s!"code length {code.size} is not a positive multiple of 4"
  return (Array.range (code.size / 4)).map fun j =>
    code[4*j]! + 256 * code[4*j+1]! + 65536 * code[4*j+2]! + 16777216 * code[4*j+3]!

def intStx (i : Int) : MacroM Term :=
  if i < 0 then `(- $(quote i.natAbs)) else pure (quote i.toNat)

def relocStx (r : RelocLit) : MacroM Term := do
  let kind := mkCIdent r.kind
  let addend ← intStx r.addend
  let localSym : Term ← if r.localSym then `(true) else `(false)
  `({ off := $(quote r.off), kind := $kind, sym := $(quote r.sym), addend := $addend,
      localSym := $localSym : Obj.RelocEntry })

def wordStx (w : Nat) : MacroM Term :=
  `(BitVec.ofNat 32 $(Syntax.mkNumLit s!"0x{String.ofList (Nat.toDigits 16 w)}"))

/-- Build the `List.Mem` proof `x ∈ l` by locating `x` (up to syntactic equality after
    instantiation) in the `whnf`-reduced spine of `l`. -/
partial def memProof (x l : Expr) : MetaM Expr := do
  let l' ← whnf l
  unless l'.isAppOfArity ``List.cons 3 do
    throwError "obj_mem: element not found in list{indentExpr x}"
  let α := l'.getArg! 0
  let hd := l'.getArg! 1
  let tl := l'.getArg! 2
  let u ← getDecLevel α
  if hd == x then
    return mkApp3 (mkConst ``List.Mem.head [u]) α hd tl
  let p ← memProof x tl
  return mkApp5 (mkConst ``List.Mem.tail [u]) α x hd tl p

/-- `obj_mem`: close `x ∈ l` where `l` reduces to a concrete list literal containing `x`
    syntactically (e.g. `myObj ∈ myImage.objects`). The kernel re-checks the proof. -/
elab "obj_mem" : tactic => Tactic.withMainContext do
  let g ← Tactic.getMainGoal
  let ty ← instantiateMVars (← g.getType)
  let ty ← whnfR ty
  unless ty.isAppOfArity ``Membership.mem 5 do
    throwError "obj_mem: expected a goal `x ∈ l`, got{indentExpr ty}"
  let l := ty.getArg! 3
  let x := ty.getArg! 4
  let p ← memProof x l
  g.assign (← mkExpectedTypeHint p ty)
  Tactic.replaceMainGoal []

/-- Persistent registry mapping an `Obj.ObjectInfo` constant name to a precomputed
    `Obj.RelocFnIndex` constant name registered via `gen_reloc_fn_index`. -/
initialize relocFnIndexExt : SimplePersistentEnvExtension (Name × Name) (NameMap Name) ←
  registerSimplePersistentEnvExtension {
    addEntryFn := fun m (objNm, idxNm) => m.insert objNm idxNm
    addImportedFn := fun arrs =>
      arrs.foldl (init := {}) fun m arr =>
        arr.foldl (init := m) fun m (objNm, idxNm) => m.insert objNm idxNm
  }

/-- Add a kernel-checked `noncomputable def` without re-elaborating a large prebuilt `Expr`. -/
def addPrebuiltNoncomputableDef (declName : Name) (ty val : Expr) : TermElabM Unit := do
  let env ← getEnv
  addDecl (.defnDecl {
    name := declName
    levelParams := []
    type := ty
    value := val
    hints := .regular (getMaxHeight env val + 1)
    safety := .safe
  })
  modifyEnv (addNoncomputable · declName)

/-- Emit `def <id> : List <elemTy> := ...`, chunking via `List.flatten` into slices of 256 items
    when `items.size > 512` so macro expansion and elaboration stay bounded in recursion depth. -/
def elabChunkedListDef (id : Ident) (elemTy : Term) (items : Array Term) :
    CommandElabM Unit := do
  if items.size ≤ 512 then
    elabCommand (← `(command| def $id : List $elemTy := [$items,*]))
  else
    let mut chunks : Array Term := #[]
    let mut start := 0
    while start < items.size do
      let stop := Nat.min (start + 256) items.size
      let slice := items.extract start stop
      chunks := chunks.push (← `([$slice,*]))
      start := stop
    elabCommand (← `(command|
      def $id : List $elemTy := ([$chunks,*] : List (List $elemTy)).flatten))

/-- `gen_reloc_fn_index <idx> <obj>`: build and kernel-certify an `O(log F)`
    `Obj.RelocFnIndex <obj>` over `<obj>.relocFns`, registering it for subsequent `gen_reloc_fn`
    commands on `<obj>`. -/
syntax (name := genRelocFnIndex) "gen_reloc_fn_index " ident ppSpace ident : command

@[command_elab genRelocFnIndex]
def elabGenRelocFnIndex : CommandElab := fun stx => do
  match stx with
  | `(gen_reloc_fn_index $idxId:ident $obj:ident) =>
    let currNs ← getCurrNamespace
    let base := idxId.getId
    let mkHelper (sfx : String) : Name × Ident :=
      let s := base.appendAfter sfx
      (currNs ++ s, mkIdentFrom idxId s)
    let (fnsTreeFull, fnsTreeId) := mkHelper "_fnsTree"
    let (bucketsFull, bucketsId) := mkHelper "_symBuckets"
    let (symBSTFull, symBSTId) := mkHelper "_symBST"
    let (symRanksFull, symRanksId) := mkHelper "_symRanks"
    let (_, toListEqId) := mkHelper "_toList_eq"
    let (_, nodupId) := mkHelper "_syms_nodup"
    let objConstName? ← liftTermElabM do
      let objE ← instantiateMVars (← elabTerm obj (some (Lean.mkConst ``Obj.ObjectInfo)))
      let fns ← listElems (← mkAppM ``Obj.ObjectInfo.relocFns #[objE])
      let syms ← fns.mapM fun fn => do strVal (← field ``Obj.SymCodeInfo.sym fn)
      let mut seen : Std.HashMap String Nat := {}
      for h : i in [:syms.size] do
        let s := syms[i]
        if let some prev := seen[s]? then
          throwError "gen_reloc_fn_index: duplicate symbol {repr s} in `{obj}.relocFns` \
            (indices {prev} and {i})"
        seen := seen.insert s i
      let symCodeTy := Lean.mkConst ``Obj.SymCodeInfo
      let fnsTreeTy := mkApp (Lean.mkConst ``ProofLib.ProgramReflection.IdxTree [0]) symCodeTy
      let fnsTreeExpr :=
        ProofLib.ProgramReflection.mkIdxTreeExpr Level.zero symCodeTy fns
      addPrebuiltNoncomputableDef fnsTreeFull fnsTreeTy fnsTreeExpr
      let charTy := Lean.mkConst ``Char
      let listCharTy := mkApp (Lean.mkConst ``List [0]) charTy
      let natTy := Lean.mkConst ``Nat
      let pairTy := mkApp2 (Lean.mkConst ``Prod [0, 0]) listCharTy natTy
      let listPairTy := mkApp (Lean.mkConst ``List [0]) pairTy
      let mut buckets : Array (Array Expr) := Array.replicate 1024 #[]
      let mut bstItems : Array (List Char × Nat × Expr × Expr) := Array.mkEmpty syms.size
      for h : i in [:syms.size] do
        let s := syms[i]
        let cs := s.toList
        let csExpr := ProofLib.ProgramReflection.mkCharListExpr s
        let idxExpr := mkRawNatLit i
        let bIdx := ProofLib.ProgramReflection.hashChars1024 cs
        let pairExpr :=
          mkApp4 (Lean.mkConst ``Prod.mk [0, 0]) listCharTy natTy csExpr idxExpr
        buckets := buckets.set! bIdx (buckets[bIdx]!.push pairExpr)
        bstItems := bstItems.push (cs, i, csExpr, idxExpr)
      let bucketExprs ← buckets.mapM fun b => mkListLit pairTy b.toList
      let bucketsTy := mkApp (Lean.mkConst ``ProofLib.ProgramReflection.IdxTree [0]) listPairTy
      let bucketsExpr :=
        ProofLib.ProgramReflection.mkIdxTreeExpr Level.zero listPairTy bucketExprs
      addPrebuiltNoncomputableDef bucketsFull bucketsTy bucketsExpr
      let sorted := bstItems.qsort fun a b => ProofLib.ProgramReflection.charListLt a.1 b.1
      let mut ranksArr := Array.replicate syms.size 0
      for r in [:sorted.size] do
        ranksArr := ranksArr.set! sorted[r]!.2.1 r
      let bstTy := mkApp (Lean.mkConst ``ProofLib.ProgramReflection.SymBST) natTy
      let bstExpr := ProofLib.ProgramReflection.mkSymBSTExpr natTy
        (sorted.map fun (_, _, ke, ve) => (ke, ve))
      addPrebuiltNoncomputableDef symBSTFull bstTy bstExpr
      let ranksExpr ← mkListLit natTy (ranksArr.toList.map mkRawNatLit)
      addPrebuiltNoncomputableDef symRanksFull (mkApp (Lean.mkConst ``List [0]) natTy) ranksExpr
      return objE.constName?
    elabCommand (← `(command|
      open ProofLib.ProgramReflection in
      theorem $toListEqId : ($fnsTreeId).toList = ($obj : Obj.ObjectInfo).relocFns := by rfl_kernel))
    elabCommand (← `(command|
      open ProofLib.ProgramReflection in
      theorem $nodupId : ((($obj : Obj.ObjectInfo).relocFns).map (·.sym)).Nodup :=
        ProofLib.ProgramReflection.nodup_of_symBST_ranks
          (t := $symBSTId) (ranks := $symRanksId) (by rfl_kernel) (by rfl_kernel)))
    elabCommand (← `(command|
      noncomputable def $idxId : Obj.RelocFnIndex $obj := {
        fnsTree := $fnsTreeId
        symBuckets := $bucketsId
        toList_eq := $toListEqId
        syms_nodup := $nodupId
      }))
    if let some objNm := objConstName? then
      let idxConstName := currNs ++ base
      modifyEnv (relocFnIndexExt.addEntry · (objNm, idxConstName))
  | _ => throwUnsupportedSyntax

/-- `gen_reloc_fn <prefix> <obj> "<sym>" [using <idx>] [in <image>]`: emit `<prefix>Relocs`,
    `<prefix>Words`, `<prefix>_checked`, `<prefix>_check` (and `<prefix>_mem` with `in <image>`)
    for entry `<sym>` of `<obj>.relocFns`. -/
syntax (name := genRelocFn) "gen_reloc_fn " ident ppSpace ident ppSpace str
  (" using " ident)? (" in " ident)? : command

@[command_elab genRelocFn]
def elabGenRelocFn : CommandElab := fun stx => do
  match stx with
  | `(gen_reloc_fn $pfx:ident $obj:ident $sym:str $[using $idx?:ident]? $[in $img?:ident]?) =>
    let env ← getEnv
    let (fnIdx, relocs, code, regIdx?) ← liftTermElabM do
      let objE ← instantiateMVars (← elabTerm obj (some (Lean.mkConst ``Obj.ObjectInfo)))
      let (fnIdx, relocs, code) ← findRelocFnIdx objE sym.getString
      let regIdx? := objE.constName?.bind (relocFnIndexExt.getState env).find?
      return (fnIdx, relocs, code, regIdx?)
    let words ← match wordsOfBytes code with
      | .ok w => pure w
      | .error msg => throwError "gen_reloc_fn: {msg}"
    let base := pfx.getId
    let relocsId := mkIdentFrom pfx (base.appendAfter "Relocs")
    let wordsId := mkIdentFrom pfx (base.appendAfter "Words")
    let checkedId := mkIdentFrom pfx (base.appendAfter "_checked")
    let checkId := mkIdentFrom pfx (base.appendAfter "_check")
    let relocTerms ← liftMacroM (relocs.mapM relocStx)
    let wordTerms ← liftMacroM (words.mapM wordStx)
    elabChunkedListDef relocsId (← `(Obj.RelocEntry)) relocTerms
    elabChunkedListDef wordsId (← `(BitVec 32)) wordTerms
    let resolvedIdx? : Option Ident :=
      match idx? with
      | some id => some id
      | none => regIdx?.map mkCIdent
    if let some idxTerm := resolvedIdx? then
      elabCommand (← `(command|
        open ProofLib.ProgramReflection in
        theorem $checkedId : ($obj : Obj.ObjectInfo).RelocFnChecked $sym $relocsId $wordsId :=
          Obj.RelocFnIndex.checked_of_at $idxTerm (i := $(quote fnIdx))
            (by rfl_kernel) (by decide +kernel)))
      elabCommand (← `(command|
        theorem $checkId : checkRelocFn $obj $sym $relocsId $wordsId = true :=
          checkRelocFn_of_checked ($idxTerm).syms_nodup $checkedId))
    else
      elabCommand (← `(command|
        open ProofLib.ProgramReflection in
        theorem $checkId : checkRelocFn $obj $sym $relocsId $wordsId = true :=
          checkRelocFn_of_firstAt (idx := $(quote fnIdx))
            (by rfl_kernel) (by decide +kernel)))
      elabCommand (← `(command|
        theorem $checkedId : ($obj : Obj.ObjectInfo).RelocFnChecked $sym $relocsId $wordsId :=
          Obj.ObjectInfo.RelocFnChecked.of_checkRelocFn $checkId))
    if let some img := img? then
      let memId := mkIdentFrom pfx (base.appendAfter "_mem")
      elabCommand (← `(command|
        theorem $memId : $obj ∈ ($img : Obj.LinkedImage).objects := by obj_mem))
  | _ => throwUnsupportedSyntax

end ProofLib.RelocFnGen
