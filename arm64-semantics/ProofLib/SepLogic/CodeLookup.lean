/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public meta import Lean
public meta import Arm64.Trusted.ISA.Syntax
public import ProofLib.ProgramReflection
import Arm64.Trusted.Spec.SepLogic

/-!
# Name-Based Code Layout and Cut-Point Lookup

Elaboration-time lookup of symbol offsets, generated layout lemmas, relocation call offsets, and
instruction-pattern cut points by symbol name or instruction encoding, producing ordinary numeral
or generated-lemma terms checked by the kernel:
- `code_off% <code> "<sym>"`: byte offset of a function or extern stub.
- `code_rel% <code> "<from>" "<to>"`: relative byte distance `fnOff to - fnOff from` (`BitVec.ofNat w k` at `BitVec w`).
- `code_lemma% <code> <kind> "<sym>"`: generated layout lemma of `kind` (`fnOff`, `stubOff`, `off`, `fnSize`, `frameBytes`, `hookAtOff`).
- `reloc_call_off% <relocs> "<sym>" [k]` and `reloc_call_insns% <relocs> "<sym>" [k]`: function-relative byte offset or instruction index of the `k`-th call/branch relocation targeting `"<sym>"`.
- `words_ret_off%`, `words_condbr_off%`, and `words_insn_off%`: function-relative byte offset of the `k`-th matching instruction word.
- `code_call_off% <code> <entry> <target> [k]` and `code_call_addr% <code> <entry> <target> [k]`: function-relative offset or address of the `k`-th `BL` or `B` from `<entry>` to `<target>`.
-/

@[expose] public section

namespace ProofLib

/-- Top-level alias for `ProofLib.ProgramReflection.WordTree` for concrete `CodeTree` cut-point lookup. -/
abbrev CodeTree := ProofLib.ProgramReflection.WordTree

end ProofLib

namespace Arm64.Obj

/-- True when `k` is a branch or call relocation kind (`.call26`, `.jump26`, `.condbr19`, `.tstbr14`). -/
def RelocKind.isCallOrBranch : RelocKind → Bool
  | .call26 | .jump26 | .condbr19 | .tstbr14 => true
  | _ => false

/-- Uniform view of relocation tables (`List RelocEntry`, `Array RelocEntry`,
    `List (Nat × String)`, `Array (Nat × String)`, `SymCodeInfo`) as `List RelocEntry`. -/
class ToRelocEntries (R : Type) where
  toRelocEntries : R → List RelocEntry

attribute [reducible] ToRelocEntries.toRelocEntries

@[reducible, default_instance]
instance instToRelocEntriesList : ToRelocEntries (List RelocEntry) where
  toRelocEntries rs := rs

@[reducible]
instance instToRelocEntriesArray : ToRelocEntries (Array RelocEntry) where
  toRelocEntries rs := rs.toList

@[reducible]
instance instToRelocEntriesCallList : ToRelocEntries (List (Nat × String)) where
  toRelocEntries cs := cs.map fun (off, sym) => { off, kind := .call26, sym }

@[reducible]
instance instToRelocEntriesCallArray : ToRelocEntries (Array (Nat × String)) where
  toRelocEntries cs := cs.toList.map fun (off, sym) => { off, kind := .call26, sym }

@[reducible]
instance instToRelocEntriesSymCodeInfo : ToRelocEntries SymCodeInfo where
  toRelocEntries info := info.relocs

/-- Uniform view of instruction word sequences (`List (BitVec 32)`, `Array (BitVec 32)`,
    `FnCode`, `ProofLib.CodeTree`) as `List (BitVec 32)`. -/
class ToWordList (W : Type) where
  toWordList : W → List (BitVec 32)

attribute [reducible] ToWordList.toWordList

@[reducible, default_instance]
instance instToWordListList : ToWordList (List (BitVec 32)) where
  toWordList ws := ws

@[reducible]
instance instToWordListArray : ToWordList (Array (BitVec 32)) where
  toWordList ws := ws.toList

@[reducible]
instance instToWordListFnCode : ToWordList FnCode where
  toWordList c := c.hex

@[reducible]
instance instToWordListWordTree : ToWordList ProofLib.ProgramReflection.WordTree where
  toWordList t := t.toWords

/-- Computable lookup of the `k`-th (0-indexed) call/branch relocation targeting `sym` in `relocs`,
    returning its function-relative byte offset (`4 * insnIdx`) as `Option Nat`. -/
def findCallOffNat? {R : Type} [ToRelocEntries R] (relocs : R) (sym : String) (k : Nat := 0) :
    Option Nat :=
  let matching := (ToRelocEntries.toRelocEntries relocs).filter fun r =>
    r.sym == sym && r.kind.isCallOrBranch
  (matching[k]?).map (·.off)

/-- Computable lookup of the `k`-th (0-indexed) call/branch relocation targeting `sym` in `relocs`,
    returning its function-relative byte offset as `Option (BitVec 64)`. -/
def findCallOff? {R : Type} [ToRelocEntries R] (relocs : R) (sym : String) (k : Nat := 0) :
    Option (BitVec 64) :=
  (findCallOffNat? relocs sym k).map (BitVec.ofNat 64)

/-- Computable lookup of the `k`-th (0-indexed) call/branch relocation targeting `sym` in `relocs`,
    returning its function-relative byte offset (`BitVec 64`, defaulting to `0#64` if absent). -/
def findCallOff {R : Type} [ToRelocEntries R] (relocs : R) (sym : String) (k : Nat := 0) :
    BitVec 64 :=
  (findCallOff? relocs sym k).getD 0#64

/-- True when 32-bit word `w` encodes an ARM64 `RET` instruction (`RET Rn`, `0xd65f03c0#32` for `X30`). -/
def isRetWord (w : BitVec 32) : Bool :=
  (w &&& 0xfffffc1f#32) == 0xd65f0000#32

/-- True when 32-bit word `w` encodes an ARM64 conditional branch (`B.cond`, `CBZ`, `CBNZ`, `TBZ`, `TBNZ`). -/
def isCondBranchWord (w : BitVec 32) : Bool :=
  (w &&& 0x7e000000#32) == 0x34000000#32 ||
  (w &&& 0x7e000000#32) == 0x36000000#32 ||
  (w &&& 0xff000010#32) == 0x54000000#32

/-- True when 32-bit word `w` encodes an ARM64 `BL` instruction (`0x94000000#32..0x97ffffff#32`). -/
def isBlWord (w : BitVec 32) : Bool :=
  (w &&& 0xfc000000#32) == 0x94000000#32

/-- True when 32-bit word `w` encodes an ARM64 unconditional immediate branch (`B` or `BL`). -/
def isBranchImmWord (w : BitVec 32) : Bool :=
  (w &&& 0x7c000000#32) == 0x14000000#32

/-- Find the byte offset (`4 * insnIdx`) of the `k`-th instruction word in `words` satisfying `pred`. -/
def findWordOffNat? {W : Type} [ToWordList W] (words : W) (pred : BitVec 32 → Bool)
    (k : Nat := 0) : Option Nat :=
  let rec go (ws : List (BitVec 32)) (idx rem : Nat) : Option Nat :=
    match ws with
    | [] => none
    | w :: rest =>
      if pred w then
        match rem with
        | 0 => some (4 * idx)
        | rem' + 1 => go rest (idx + 1) rem'
      else
        go rest (idx + 1) rem
  go (ToWordList.toWordList words) 0 k

/-- Find the byte offset (`BitVec 64`) of the `k`-th instruction word in `words` satisfying `pred`. -/
def findWordOff? {W : Type} [ToWordList W] (words : W) (pred : BitVec 32 → Bool)
    (k : Nat := 0) : Option (BitVec 64) :=
  (findWordOffNat? words pred k).map (BitVec.ofNat 64)

/-- Find the byte offset (`BitVec 64`, defaulting to `0#64`) of the `k`-th word satisfying `pred`. -/
def findWordOff {W : Type} [ToWordList W] (words : W) (pred : BitVec 32 → Bool)
    (k : Nat := 0) : BitVec 64 :=
  (findWordOff? words pred k).getD 0#64

/-- Find the byte offset (`BitVec 64`, defaulting to `0#64`) of the `k`-th `RET` instruction in `words`. -/
def findRetOff {W : Type} [ToWordList W] (words : W) (k : Nat := 0) : BitVec 64 :=
  findWordOff words isRetWord k

/-- Find the byte offset (`BitVec 64`, defaulting to `0#64`) of the `k`-th conditional branch in `words`. -/
def findCondBrOff {W : Type} [ToWordList W] (words : W) (k : Nat := 0) : BitVec 64 :=
  findWordOff words isCondBranchWord k

/-- Target address `pc + ((imm26.signExtend 64) <<< 2)` of a `BL` (or `B`) instruction word `w` at `pc`. -/
def blTargetAddr? (pc : BitVec 64) (w : BitVec 32) : Option (BitVec 64) :=
  if isBranchImmWord w then
    let imm26 : BitVec 26 := w.extractLsb' 0 26
    some (pc + ((imm26.signExtend 64) <<< 2))
  else
    none

/-- Computable lookup of the `k`-th (0-indexed) `BL`/`B` instruction in `words` (loaded at `entry`)
    targeting `target`, returning its function-relative byte offset as `Option Nat`. -/
def findBlOffNat? {W : Type} [ToWordList W] (words : W) (entry target : BitVec 64)
    (k : Nat := 0) : Option Nat :=
  let rec go (ws : List (BitVec 32)) (idx rem : Nat) : Option Nat :=
    match ws with
    | [] => none
    | w :: rest =>
      let pc := entry + BitVec.ofNat 64 (4 * idx)
      if blTargetAddr? pc w == some target then
        match rem with
        | 0 => some (4 * idx)
        | rem' + 1 => go rest (idx + 1) rem'
      else
        go rest (idx + 1) rem
  go (ToWordList.toWordList words) 0 k

/-- Computable lookup of the `k`-th (0-indexed) `BL`/`B` instruction in `words` (loaded at `entry`)
    targeting `target`, returning its function-relative byte offset as `Option (BitVec 64)`. -/
def findBlOff? {W : Type} [ToWordList W] (words : W) (entry target : BitVec 64)
    (k : Nat := 0) : Option (BitVec 64) :=
  (findBlOffNat? words entry target k).map (BitVec.ofNat 64)

/-- Computable lookup of the `k`-th (0-indexed) `BL`/`B` instruction in `words` (loaded at `entry`)
    targeting `target`, returning its function-relative byte offset (`BitVec 64`, default `0#64`). -/
def findBlOff {W : Type} [ToWordList W] (words : W) (entry target : BitVec 64)
    (k : Nat := 0) : BitVec 64 :=
  (findBlOff? words entry target k).getD 0#64

end Arm64.Obj

end

public meta section

namespace ProofLib.CodeLookup

open Lean Meta Elab Term

/-- The kinds of per-symbol layout lemmas emitted by `rust-obj2lean`. -/
inductive Kind where
  | fnOff | stubOff | fnSize | frameBytes | hookAtOff
  deriving BEq, Hashable, Repr, Inhabited

/-- The infix of the generated lemma name (`<code>_<tag>_0x<hex>`). -/
def Kind.tag : Kind → String
  | .fnOff => "fnOff"
  | .stubOff => "stubOff"
  | .fnSize => "fnSize"
  | .frameBytes => "frameBytes"
  | .hookAtOff => "hookAtOff?"

/-- One generated layout lemma `decl` stating that symbol `sym` has value `val`. -/
structure Entry where
  decl : Name
  sym : String
  val : Nat
  deriving Inhabited

private partial def natLit? : Expr → Option Nat
  | .lit (.natVal n) => some n
  | .mdata _ e => natLit? e
  | e => if e.isAppOfArity ``OfNat.ofNat 3 then natLit? (e.getArg! 1) else none

private partial def strLit? : Expr → Option String
  | .lit (.strVal s) => some s
  | .mdata _ e => strLit? e
  | _ => none

private partial def stripForall : Expr → Expr
  | .forallE _ _ b _ => stripForall b
  | .mdata _ e => stripForall e
  | e => e

private def parseEntry (k : Kind) (decl : Name) (ty : Expr) : Option Entry := do
  let ty := stripForall ty
  if !ty.isAppOfArity ``Eq 3 then none else
  let lhs := ty.getArg! 1
  let rhs := ty.getArg! 2
  match k with
  | .hookAtOff =>
    let n ← natLit? lhs.getAppArgs.back!
    let s ← strLit? rhs.getAppArgs.back!
    pure ⟨decl, s, n⟩
  | _ =>
    let s ← strLit? lhs.getAppArgs.back!
    let n ← natLit? rhs
    pure ⟨decl, s, n⟩

private def stripShardSuffix (s : String) : String :=
  let rev := s.toList.reverse
  let digits := rev.takeWhile Char.isDigit
  if digits.isEmpty then s
  else
    match rev.drop digits.length with
    | 'd' :: 'r' :: 'a' :: 'h' :: 'S' :: stemRev => String.ofList stemRev.reverse
    | _ => s

private def isCompanionShardModule (modName cand : Name) : Bool :=
  match modName, cand with
  | .str pfx1 s1, .str pfx2 s2 =>
    pfx1 == pfx2 && stripShardSuffix s1 == stripShardSuffix s2
  | _, _ => modName == cand

private initialize entriesCache :
    IO.Ref (Std.HashMap (UInt64 × Name × Kind) (Array Entry)) ← IO.mkRef {}

/-- All generated lemmas of kind `k` for the code constant `codeName`. Scans the module defining
    `codeName` together with any companion `<Prefix>Shard<k>` modules in the environment header. -/
def entries (codeName : Name) (k : Kind) : MetaM (Array Entry) := do
  let env ← getEnv
  let .str pfx last := codeName
    | throwError "code lookup: `{codeName}` is not a string name"
  let start := s!"{last}_{k.tag}_0x"
  match env.getModuleIdxFor? codeName with
  | some idx =>
    let headerKey := env.header.moduleNames.foldl (fun h m => mixHash h m.hash) 7
    let cacheKey := (headerKey, codeName, k)
    if let some cached := (← entriesCache.get)[cacheKey]? then
      return cached
    let defMod := env.header.moduleNames[idx.toNat]!
    let mut out := #[]
    for i in [:env.header.moduleNames.size] do
      if isCompanionShardModule defMod env.header.moduleNames[i]! then
        for n in env.header.moduleData[i]!.constNames do
          if let .str p s := n then
            if p == pfx && s.startsWith start then
              if let some ci := env.find? n then
                if let some e := parseEntry k n ci.type then
                  out := out.push e
    entriesCache.modify (·.insert cacheKey out)
    return out
  | none =>
    let mut out := #[]
    for (n, ci) in env.constants.map₂ do
      if let .str p s := n then
        if p == pfx && s.startsWith start then
          if let some e := parseEntry k n ci.type then
            out := out.push e
    return out

/-- The generated lemma of kind `k` about symbol `sym` of `codeName`. -/
def lookup (codeName : Name) (k : Kind) (sym : String) : MetaM Entry := do
  let es ← entries codeName k
  match es.find? (·.sym == sym) with
  | some e => return e
  | none =>
    throwError "code lookup: no `{k.tag}` lemma for symbol {repr sym} of `{codeName}` \
      (is the symbol in the image, and is its name spelled exactly as in the generated \
      `*Code.lean` / `*Index.json`?)"

/-- The offset lemma (`fnOff`, else `stubOff`) of a function or extern stub. -/
def lookupOff (codeName : Name) (sym : String) : MetaM Entry := do
  if let some e := (← entries codeName .fnOff).find? (·.sym == sym) then return e
  if let some e := (← entries codeName .stubOff).find? (·.sym == sym) then return e
  throwError "code lookup: no `fnOff`/`stubOff` lemma for symbol {repr sym} of `{codeName}` \
    (is the symbol in the image, and is its name spelled exactly as in the generated \
    `*Code.lean` / `*Index.json`?)"

/-- Parse a lookup-kind identifier; `off` means `fnOff` or `stubOff`. -/
def lookupByKindName (codeName : Name) (kind : Name) (sym : String) : MetaM Entry :=
  match kind with
  | `fnOff => lookup codeName .fnOff sym
  | `stubOff => lookup codeName .stubOff sym
  | `off => lookupOff codeName sym
  | `fnSize => lookup codeName .fnSize sym
  | `frameBytes => lookup codeName .frameBytes sym
  | `hookAtOff => lookup codeName .hookAtOff sym
  | _ => throwError "code lookup: unknown kind `{kind}` (expected fnOff, stubOff, off, fnSize, \
      frameBytes or hookAtOff)"

/-- Elaborate numeral `n` at `expectedType?`, emitting `BitVec.ofNat w n` (matching `n#w`) for
    `BitVec w` and an `OfNat` numeral otherwise. Postpones when `expectedType?` is `none` or an
    unassigned metavariable so binary operators (`binop%`) can unify leaf types with `BitVec 64`
    before elaboration resumes, avoiding unsimplified `@OfNat.ofNat (BitVec 64) n _` terms. -/
def elabNumeral (n : Nat) (expectedType? : Option Expr) : TermElabM Expr := do
  let lit := Syntax.mkNumLit (toString n)
  match expectedType? with
  | none => tryPostpone
  | some ety => tryPostponeIfMVar ety
  if let some ety := expectedType? then
    let ety ← whnfR (← instantiateMVars ety)
    if ety.isAppOfArity ``BitVec 1 then
      return ← elabTerm (← `(BitVec.ofNat _ $lit)) ety
  elabTerm lit expectedType?

/-- `code_off% <code> "<sym>"`: offset of function or extern stub `sym` in `<code>`. -/
syntax (name := codeOffStx) "code_off% " ident str : term

/-- `code_rel% <code> "<from>" "<to>"`: `fnOff to - fnOff from` (each a function or stub). -/
syntax (name := codeRelStx) "code_rel% " ident str str : term

/-- `code_lemma% <code> <kind> "<sym>"`: the generated layout lemma of `kind` about `sym`. -/
syntax (name := codeLemmaStx) "code_lemma% " ident ident str : term

@[term_elab codeOffStx] def elabCodeOff : TermElab := fun stx expectedType? => do
  match stx with
  | `(code_off% $c:ident $s:str) =>
    let codeName ← realizeGlobalConstNoOverloadWithInfo c
    let e ← lookupOff codeName s.getString
    elabNumeral e.val expectedType?
  | _ => throwUnsupportedSyntax

@[term_elab codeRelStx] def elabCodeRel : TermElab := fun stx expectedType? => do
  match stx with
  | `(code_rel% $c:ident $f:str $t:str) =>
    let codeName ← realizeGlobalConstNoOverloadWithInfo c
    let ef ← lookupOff codeName f.getString
    let et ← lookupOff codeName t.getString
    unless ef.val ≤ et.val do
      throwError "code_rel%: {repr t.getString} (offset {et.val}) precedes \
        {repr f.getString} (offset {ef.val})"
    elabNumeral (et.val - ef.val) expectedType?
  | _ => throwUnsupportedSyntax

@[term_elab codeLemmaStx] def elabCodeLemma : TermElab := fun stx expectedType? => do
  match stx with
  | `(code_lemma% $c:ident $k:ident $s:str) =>
    let codeName ← realizeGlobalConstNoOverloadWithInfo c
    let e ← lookupByKindName codeName k.getId.eraseMacroScopes s.getString
    elabTerm (mkCIdentFrom stx e.decl) expectedType?
  | _ => throwUnsupportedSyntax

/-- `nat_lit% t`: evaluate the closed `Nat` term `t` (e.g. `2^64 - code_rel% c "f" "g"`) and
    elaborate the result as a numeral at the expected type (`k#w` at `BitVec w`). -/
syntax (name := natLitStx) "nat_lit% " term:max : term

@[term_elab natLitStx] def elabNatLit : TermElab := fun stx expectedType? => do
  match stx with
  | `(nat_lit% $t) =>
    let e ← elabTermEnsuringType t (mkConst ``Nat)
    synthesizeSyntheticMVarsNoPostponing
    let e ← instantiateMVars e
    if e.hasMVar || e.hasFVar then
      throwError "nat_lit%: {e} is not a closed `Nat` term"
    let r ← withTransparency .all <| reduce e
    let some n := natLit? r
      | throwError "nat_lit%: {e} does not reduce to a numeral (got {r})"
    elabNumeral n expectedType?
  | _ => throwUnsupportedSyntax

/-! ## Cut-Point Elaborators -/

/-- Elaborate a byte offset `n : Nat` at `expectedType?`, defaulting to `BitVec 64`
    (`BitVec.ofNat 64 n`, the exact term `n#64` denotes) when `expectedType?` is `none`,
    `BitVec 64`, or an unassigned metavariable, and elaborating as a `Nat` literal when
    `expectedType?` is explicitly `Nat` (or `BitVec.ofNat w n` when `BitVec w`). -/
def elabByteOffBitVec64 (n : Nat) (expectedType? : Option Expr) : TermElabM Expr := do
  let lit := Syntax.mkNumLit (toString n)
  if let some ety := expectedType? then
    tryPostponeIfMVar ety
    let ety ← whnfR (← instantiateMVars ety)
    if ety.isConstOf ``Nat then
      return ← elabTerm lit ety
    if ety.isAppOfArity ``BitVec 1 then
      return ← elabTerm (← `(BitVec.ofNat _ $lit)) ety
  elabTerm (← `(BitVec.ofNat 64 $lit)) expectedType?

/-- Evaluate an `Expr` to a concrete `Nat` if possible. -/
partial def evalNatExpr? (e : Expr) : MetaM (Option Nat) := do
  let e := e.consumeMData
  if let some n := natLit? e then return some n
  if let some n ← getNatValue? e then return some n
  if e.hasFVar || e.hasMVar then return none
  let e' ← withTransparency .all (whnf e)
  if let some n := natLit? e' then return some n
  getNatValue? e'

/-- Evaluate a ground `BitVec w` expression to `(w, val % 2^w)`. -/
partial def evalBitVecExpr? (e : Expr) : MetaM (Option (Nat × Nat)) := do
  let e := e.consumeMData
  if e.isAppOfArity ``BitVec.ofNat 2 then
    if let some w ← evalNatExpr? (e.getArg! 0) then
      if let some v ← evalNatExpr? (e.getArg! 1) then
        return some (w, v % (1 <<< w))
  if e.isAppOfArity ``OfNat.ofNat 3 then
    let ty ← withTransparency .all (whnf (e.getArg! 0))
    if ty.isAppOfArity ``BitVec 1 then
      if let some w ← evalNatExpr? (ty.getArg! 0) then
        if let some v ← evalNatExpr? (e.getArg! 1) then
          return some (w, v % (1 <<< w))
  if e.isAppOfArity ``HAdd.hAdd 6 then
    if let some (w1, v1) ← evalBitVecExpr? (e.getArg! 4) then
      if let some (w2, v2) ← evalBitVecExpr? (e.getArg! 5) then
        if w1 == w2 then
          return some (w1, (v1 + v2) % (1 <<< w1))
  if e.isAppOfArity ``HSub.hSub 6 then
    if let some (w1, v1) ← evalBitVecExpr? (e.getArg! 4) then
      if let some (w2, v2) ← evalBitVecExpr? (e.getArg! 5) then
        if w1 == w2 then
          let m := 1 <<< w1
          return some (w1, (v1 + m - (v2 % m)) % m)
  if e.isAppOfArity ``Neg.neg 3 then
    if let some (w, v) ← evalBitVecExpr? (e.getArg! 2) then
      let m := 1 <<< w
      return some (w, (m - (v % m)) % m)
  if e.hasFVar || e.hasMVar then return none
  let e' ← withTransparency .all (whnf e)
  if e'.isAppOfArity ``BitVec.ofNat 2 then
    if let some w ← evalNatExpr? (e'.getArg! 0) then
      if let some v ← evalNatExpr? (e'.getArg! 1) then
        return some (w, v % (1 <<< w))
  if e'.isAppOfArity ``BitVec.ofFin 2 then
    if let some w ← evalNatExpr? (e'.getArg! 0) then
      let finExpr ← withTransparency .all (whnf (e'.getArg! 1))
      if finExpr.isAppOfArity ``Fin.mk 3 then
        if let some v ← evalNatExpr? (finExpr.getArg! 1) then
          return some (w, v % (1 <<< w))
  return none

/-- Evaluate an `Expr` to a concrete `String` if possible. -/
partial def evalStringExpr? (e : Expr) : MetaM (Option String) := do
  let e := e.consumeMData
  if let some s := strLit? e then return some s
  if e.hasFVar || e.hasMVar then return none
  let e' ← withTransparency .all (whnf e)
  if let some s := strLit? e' then return some s
  if e'.isAppOfArity ``String.ofList 1 then
    let chars ← ProofLib.ProgramReflection.listElemsWhnf (e'.getArg! 0)
    let mut out : Array Char := #[]
    for cExpr in chars do
      let cExpr ← withTransparency .all (whnf cExpr)
      if cExpr.isAppOfArity ``Char.mk 2 then
        let uExpr ← withTransparency .all (whnf (cExpr.getArg! 0))
        if let some n ← evalNatExpr? uExpr then
          out := out.push (Char.ofNat n)
        else return none
      else return none
    return some (String.ofList out.toList)
  return none

/-- Extract the element `Expr`s of a `List α` or `Array α` expression in $O(N)$. -/
def extractListOrArrayElems (e : Expr) : MetaM (Array Expr) := do
  let mut cur := e.consumeMData
  while cur.isLet do
    cur := (cur.letBody!.instantiate1 cur.letValue!).consumeMData
  if cur.isAppOfArity ``Array.mk 2 || cur.isAppOfArity ``List.toArray 2 then
    return ← ProofLib.ProgramReflection.listElemsWhnf (cur.getArg! 1)
  let ty ← withTransparency .all (whnf (← inferType cur))
  if ty.isAppOfArity ``Array 1 then
    let cur' ← withTransparency .all (whnf cur)
    if cur'.isAppOfArity ``Array.mk 2 || cur'.isAppOfArity ``List.toArray 2 then
      return ← ProofLib.ProgramReflection.listElemsWhnf (cur'.getArg! 1)
    let toListExpr ← mkAppM ``Array.toList #[cur]
    return ← ProofLib.ProgramReflection.listElemsWhnf toListExpr
  ProofLib.ProgramReflection.listElemsWhnf cur

/-- True if `kindExpr` WHNF-reduces to a branch or call relocation kind
    (`.call26`, `.jump26`, `.condbr19`, `.tstbr14`). -/
def isCallOrBranchRelocKindExpr (kindExpr : Expr) : MetaM Bool := do
  let k ← withTransparency .all (whnf kindExpr)
  return k.isConstOf ``Arm64.Obj.RelocKind.call26 ||
    k.isConstOf ``Arm64.Obj.RelocKind.jump26 ||
    k.isConstOf ``Arm64.Obj.RelocKind.condbr19 ||
    k.isConstOf ``Arm64.Obj.RelocKind.tstbr14

/-- Extract `(off, sym)` pairs for all call/branch relocations in `relocsExpr`
    (supporting `List Obj.RelocEntry`, `Array Obj.RelocEntry`, `List (Nat × String)`,
    `Array (Nat × String)`, and `Obj.SymCodeInfo`). -/
def extractCallRelocs (relocsExpr : Expr) : MetaM (Array (Nat × String)) := do
  let mut src := relocsExpr.consumeMData
  let ty ← withTransparency .all (whnf (← inferType src))
  if ty.isConstOf ``Arm64.Obj.SymCodeInfo then
    src := mkApp (mkConst ``Arm64.Obj.SymCodeInfo.relocs) src
  let elems ← extractListOrArrayElems src
  let mut out : Array (Nat × String) := #[]
  for elem in elems do
    let e := elem.consumeMData
    let e ← if e.isAppOfArity ``Arm64.Obj.RelocEntry.mk 5 || e.isAppOfArity ``Prod.mk 4 then
        pure e
      else
        withTransparency .all (whnf e)
    if e.isAppOfArity ``Arm64.Obj.RelocEntry.mk 5 then
      let offExpr := e.getArg! 0
      let kindExpr := e.getArg! 1
      let symExpr := e.getArg! 2
      if ← isCallOrBranchRelocKindExpr kindExpr then
        let some off ← evalNatExpr? offExpr
          | throwError "reloc_call_off%: could not evaluate relocation byte offset `{offExpr}`"
        let some s ← evalStringExpr? symExpr
          | throwError "reloc_call_off%: could not evaluate relocation symbol `{symExpr}`"
        out := out.push (off, s)
    else if e.isAppOfArity ``Prod.mk 4 then
      let offExpr := e.getArg! 2
      let symExpr := e.getArg! 3
      let some off ← evalNatExpr? offExpr
        | throwError "reloc_call_off%: could not evaluate call byte offset `{offExpr}`"
      let some s ← evalStringExpr? symExpr
        | throwError "reloc_call_off%: could not evaluate call symbol `{symExpr}`"
      out := out.push (off, s)
    else
      throwError "reloc_call_off%: expected `Obj.RelocEntry` or `Nat × String` element, got `{e}`"
  return out

/-- Find the byte offset (`4 * insnIdx`) of the `k`-th (0-indexed) call/branch relocation targeting
    `sym` in `relocsExpr`. Throws an elaboration error with available symbols if not found. -/
def lookupRelocCallOff (relocsExpr : Expr) (sym : String) (k : Nat := 0) : MetaM Nat := do
  let calls ← extractCallRelocs relocsExpr
  let matching := calls.filterMap fun (off, s) => if s == sym then some off else none
  if matching.isEmpty then
    let mut avail : Array String := #[]
    for (_, s) in calls do
      if !avail.contains s then
        avail := avail.push s
    let availDesc := if avail.isEmpty then "none" else String.intercalate ", " (avail.toList.map reprStr)
    throwError "reloc_call_off%: no call/branch relocation targeting {repr sym} \
      (available call symbols: {availDesc})"
  if h : k < matching.size then
    return matching[k]
  else
    throwError "reloc_call_off%: occurrence index {k} out of range for symbol {repr sym} \
      (found {matching.size} call(s) at byte offset(s) {matching.toList})"

/-- `reloc_call_off% <relocs> "<sym>" [k]`: function-relative byte offset (`BitVec 64` by default,
    or `Nat` when expected type is `Nat`) of the `k`-th (0-indexed, default `0`) call/branch
    relocation targeting `"<sym>"` in `<relocs>`. -/
syntax (name := relocCallOffStx) "reloc_call_off% " term:max str : term
syntax (name := relocCallOffIdxStx) "reloc_call_off% " term:max str num : term

@[term_elab relocCallOffStx, term_elab relocCallOffIdxStx]
def elabRelocCallOff : TermElab := fun stx expectedType? => do
  let (relocsStx, symStx, k) ← match stx with
    | `(reloc_call_off% $r:term $s:str) => pure (r, s, 0)
    | `(reloc_call_off% $r:term $s:str $k:num) => pure (r, s, k.getNat)
    | _ => throwUnsupportedSyntax
  let relocsExpr ← elabTerm relocsStx none
  synthesizeSyntheticMVarsNoPostponing
  let relocsExpr ← instantiateMVars relocsExpr
  let off ← lookupRelocCallOff relocsExpr symStx.getString k
  elabByteOffBitVec64 off expectedType?

/-- `reloc_call_insns% <relocs> "<sym>" [k]`: instruction count (`byteOff / 4 : Nat`) from function
    entry to the `k`-th call/branch relocation targeting `"<sym>"`. -/
syntax (name := relocCallInsnsStx) "reloc_call_insns% " term:max str : term
syntax (name := relocCallInsnsIdxStx) "reloc_call_insns% " term:max str num : term

@[term_elab relocCallInsnsStx, term_elab relocCallInsnsIdxStx]
def elabRelocCallInsns : TermElab := fun stx expectedType? => do
  let (relocsStx, symStx, k) ← match stx with
    | `(reloc_call_insns% $r:term $s:str) => pure (r, s, 0)
    | `(reloc_call_insns% $r:term $s:str $k:num) => pure (r, s, k.getNat)
    | _ => throwUnsupportedSyntax
  let relocsExpr ← elabTerm relocsStx none
  synthesizeSyntheticMVarsNoPostponing
  let relocsExpr ← instantiateMVars relocsExpr
  let off ← lookupRelocCallOff relocsExpr symStx.getString k
  elabNumeral (off / 4) expectedType?

/-- Evaluate a `BitVec 8` or `Nat` byte expression to `UInt32` (`0..255`). -/
def evalByteUInt32? (e : Expr) : MetaM (Option UInt32) := do
  if let some (8, v) ← evalBitVecExpr? e then return some (v % 256).toUInt32
  if let some v ← evalNatExpr? e then return some (v % 256).toUInt32
  return none

/-- Evaluate a `BitVec 32` or `Nat` word expression to `UInt32`. -/
def evalWord32UInt32? (e : Expr) : MetaM (Option UInt32) := do
  if let some (32, v) ← evalBitVecExpr? e then return some v.toUInt32
  if let some v ← evalNatExpr? e then return some (v % (1 <<< 32)).toUInt32
  return none

/-- Extract the 32-bit little-endian instruction words from a `WordTree` (`CodeTree`) in $O(N)$. -/
partial def extractWordsFromWordTree (e : Expr) : MetaM (Array UInt32) := do
  let mut cur := e.consumeMData
  if !cur.isConstOf ``ProofLib.ProgramReflection.WordTree.empty &&
     !cur.isAppOfArity ``ProofLib.ProgramReflection.WordTree.leaf 4 &&
     !cur.isAppOfArity ``ProofLib.ProgramReflection.WordTree.node 3 then
    cur ← withTransparency .all (whnf cur)
  if cur.isConstOf ``ProofLib.ProgramReflection.WordTree.empty then
    return #[]
  else if cur.isAppOfArity ``ProofLib.ProgramReflection.WordTree.leaf 4 then
    let some b0 ← evalByteUInt32? (cur.getArg! 0)
      | throwError "extractWordsFromWordTree: could not evaluate byte 0 `{cur.getArg! 0}`"
    let some b1 ← evalByteUInt32? (cur.getArg! 1)
      | throwError "extractWordsFromWordTree: could not evaluate byte 1 `{cur.getArg! 1}`"
    let some b2 ← evalByteUInt32? (cur.getArg! 2)
      | throwError "extractWordsFromWordTree: could not evaluate byte 2 `{cur.getArg! 2}`"
    let some b3 ← evalByteUInt32? (cur.getArg! 3)
      | throwError "extractWordsFromWordTree: could not evaluate byte 3 `{cur.getArg! 3}`"
    return #[(b3 <<< 24) ||| (b2 <<< 16) ||| (b1 <<< 8) ||| b0]
  else if cur.isAppOfArity ``ProofLib.ProgramReflection.WordTree.node 3 then
    let l ← extractWordsFromWordTree (cur.getArg! 1)
    let r ← extractWordsFromWordTree (cur.getArg! 2)
    return l ++ r
  else
    throwError "extractWordsFromWordTree: unexpected `WordTree` term `{cur}`"

/-- Pack an array of byte `Expr`s (`BitVec 8`) into 32-bit little-endian `UInt32` words. -/
def packByteExprsLE (byteExprs : Array Expr) : MetaM (Array UInt32) := do
  let nWords := byteExprs.size / 4
  let mut out : Array UInt32 := Array.mkEmpty nWords
  for i in [0 : nWords] do
    let base := 4 * i
    let some b0 ← evalByteUInt32? byteExprs[base]!
      | throwError "packByteExprsLE: could not evaluate byte `{byteExprs[base]!}`"
    let some b1 ← evalByteUInt32? byteExprs[base + 1]!
      | throwError "packByteExprsLE: could not evaluate byte `{byteExprs[base + 1]!}`"
    let some b2 ← evalByteUInt32? byteExprs[base + 2]!
      | throwError "packByteExprsLE: could not evaluate byte `{byteExprs[base + 2]!}`"
    let some b3 ← evalByteUInt32? byteExprs[base + 3]!
      | throwError "packByteExprsLE: could not evaluate byte `{byteExprs[base + 3]!}`"
    out := out.push ((b3 <<< 24) ||| (b2 <<< 16) ||| (b1 <<< 8) ||| b0)
  return out

/-- Extract 32-bit instruction words (`Array UInt32`) from a `List (BitVec 32)`,
    `Array (BitVec 32)`, `FnCode`, `WordTree` (`CodeTree`), `Program`, `Obj.LinkedImage`,
    `Obj.SymCodeInfo`, `List (BitVec 8)`, or `Array (BitVec 8)`. -/
partial def extractWordsFromExpr (e : Expr) : MetaM (Array UInt32) := do
  let e := e.consumeMData
  let ty ← withTransparency .all (whnf (← inferType e))
  if ty.isConstOf ``ProofLib.ProgramReflection.WordTree then
    return ← extractWordsFromWordTree e
  if ty.isConstOf ``Arm64.FnCode then
    return ← extractWordsFromExpr (mkApp (mkConst ``Arm64.FnCode.hex) e)
  if ty.isConstOf ``Arm64.Obj.SymCodeInfo then
    return ← extractWordsFromExpr (mkApp (mkConst ``Arm64.Obj.SymCodeInfo.code) e)
  if ty.isConstOf ``Arm64.Program then
    return ← extractWordsFromExpr (mkApp (mkConst ``Arm64.Program.code) e)
  if ty.isConstOf `Arm64.Obj.LinkedImage then
    return ← extractWordsFromExpr (mkApp (mkConst `Arm64.Obj.LinkedImage.code) e)
  if ty.isAppOfArity ``List 1 || ty.isAppOfArity ``Array 1 then
    let elemTy ← withTransparency .all (whnf (ty.getArg! 0))
    let elems ← extractListOrArrayElems e
    if elemTy.isAppOfArity ``BitVec 1 then
      let some w ← evalNatExpr? (elemTy.getArg! 0)
        | throwError "extractWordsFromExpr: unknown BitVec width in `{elemTy}`"
      if w == 32 then
        let mut out : Array UInt32 := Array.mkEmpty elems.size
        for wExpr in elems do
          let some u ← evalWord32UInt32? wExpr
            | throwError "extractWordsFromExpr: could not evaluate 32-bit word `{wExpr}`"
          out := out.push u
        return out
      else if w == 8 then
        return ← packByteExprsLE elems
  throwError "extractWordsFromExpr: expected `List/Array (BitVec 32)`, `CodeTree`/`WordTree`, \
    `FnCode`, `Program`, or `Obj.LinkedImage`, got term of type `{ty}`"

/-- True when `w` is an ARM64 `RET` (`RET Rn`, `0xd65f03c0` for `X30`). -/
def isRetUInt32 (w : UInt32) : Bool :=
  (w &&& 0xfffffc1f) == 0xd65f0000

/-- True when `w` is an ARM64 conditional branch (`B.cond`, `CBZ`, `CBNZ`, `TBZ`, `TBNZ`). -/
def isCondBrUInt32 (w : UInt32) : Bool :=
  (w &&& 0x7e000000) == 0x34000000 ||
  (w &&& 0x7e000000) == 0x36000000 ||
  (w &&& 0xff000010) == 0x54000000

/-- True when `w` is an ARM64 `BL` (branch with link) instruction (`0x94000000..0x97ffffff`). -/
def isBlUInt32 (w : UInt32) : Bool :=
  (w &&& 0xfc000000) == 0x94000000

/-- True when `w` is an ARM64 unconditional immediate branch (`B` or `BL`). -/
def isBranchImmUInt32 (w : UInt32) : Bool :=
  (w &&& 0x7c000000) == 0x14000000

/-- Find the byte offset (`4 * insnIdx`) of the `k`-th (0-indexed) instruction word in `wordsExpr`
    satisfying `pred`. -/
def lookupWordsPredOff (wordsExpr : Expr) (tag : String) (desc : String)
    (pred : UInt32 → Bool) (k : Nat := 0) : MetaM Nat := do
  let words ← extractWordsFromExpr wordsExpr
  let mut matching : Array Nat := #[]
  for idx in [0 : words.size] do
    if pred words[idx]! then
      matching := matching.push (4 * idx)
  if matching.isEmpty then
    throwError "{tag}: no {desc} instruction found in sequence ({words.size} word(s) scanned)"
  if h : k < matching.size then
    return matching[k]
  else
    throwError "{tag}: occurrence index {k} out of range for {desc} \
      (found {matching.size} match(es) at byte offset(s) {matching.toList})"

/-- Find the byte offset (`4 * insnIdx`) of the `k`-th `RET` instruction in `wordsExpr`. -/
def lookupWordsRetOff (wordsExpr : Expr) (k : Nat := 0) : MetaM Nat :=
  lookupWordsPredOff wordsExpr "words_ret_off%" "RET" isRetUInt32 k

/-- Find the byte offset (`4 * insnIdx`) of the `k`-th conditional branch in `wordsExpr`. -/
def lookupWordsCondBrOff (wordsExpr : Expr) (k : Nat := 0) : MetaM Nat :=
  lookupWordsPredOff wordsExpr "words_condbr_off%" "conditional branch" isCondBrUInt32 k

/-- Resolve a category string (`"ret"`, `"condbr"`, `"bl"`, `"b"`, `"cbz"`, `"cbnz"`, `"tbz"`,
    `"tbnz"`, `"b.cond"`) to an instruction-word predicate. -/
def categoryPredOfStr? (s : String) : Option (String × (UInt32 → Bool)) :=
  match s.toLower with
  | "ret" => some ("RET", isRetUInt32)
  | "condbr" | "branch" | "b.cond_any" => some ("conditional branch", isCondBrUInt32)
  | "b.cond" => some ("B.cond", fun w => (w &&& 0xff000010) == 0x54000000)
  | "cbz" => some ("CBZ", fun w => (w &&& 0x7f000000) == 0x34000000)
  | "cbnz" => some ("CBNZ", fun w => (w &&& 0x7f000000) == 0x35000000)
  | "tbz" => some ("TBZ", fun w => (w &&& 0x7f000000) == 0x36000000)
  | "tbnz" => some ("TBNZ", fun w => (w &&& 0x7f000000) == 0x37000000)
  | "bl" => some ("BL", isBlUInt32)
  | "b" => some ("B", fun w => (w &&& 0xfc000000) == 0x14000000)
  | "br" => some ("BR", fun w => (w &&& 0xfffffc1f) == 0xd61f0000)
  | "blr" => some ("BLR", fun w => (w &&& 0xfffffc1f) == 0xd63f0000)
  | _ => none

/-- Find the byte offset (`4 * insnIdx`) of the `k`-th instruction in `wordsExpr` matching
    `targetExpr` (a category string, a 32-bit instruction word, or a `BitVec 32 → Bool` predicate). -/
def lookupWordsInsnOff (wordsExpr targetExpr : Expr) (k : Nat := 0) : MetaM Nat := do
  if let some s ← evalStringExpr? targetExpr then
    let some (desc, pred) := categoryPredOfStr? s
      | throwError "words_insn_off%: unknown instruction category {repr s} \
          (expected \"ret\", \"condbr\", \"b.cond\", \"cbz\", \"cbnz\", \"tbz\", \"tbnz\", \"bl\", \"b\", \"br\", or \"blr\")"
    return ← lookupWordsPredOff wordsExpr "words_insn_off%" desc pred k
  if let some u ← evalWord32UInt32? targetExpr then
    return ← lookupWordsPredOff wordsExpr "words_insn_off%" s!"word 0x{String.ofList (Nat.toDigits 16 u.toNat)}" (· == u) k
  let words ← extractWordsFromExpr wordsExpr
  let mut matching : Array Nat := #[]
  for idx in [0 : words.size] do
    let wBv := toExpr (BitVec.ofNat 32 words[idx]!.toNat)
    let app ← withTransparency .all (whnf (mkApp targetExpr wBv))
    if app.isConstOf ``true then
      matching := matching.push (4 * idx)
  if matching.isEmpty then
    throwError "words_insn_off%: no instruction matching `{targetExpr}` found ({words.size} word(s) scanned)"
  if h : k < matching.size then
    return matching[k]
  else
    throwError "words_insn_off%: occurrence index {k} out of range for `{targetExpr}` \
      (found {matching.size} match(es) at byte offset(s) {matching.toList})"

/-- `words_ret_off% <words> [k]`: function-relative byte offset (`BitVec 64` by default, or `Nat`
    when expected type is `Nat`) of the `k`-th (0-indexed, default `0`) `RET` instruction in `<words>`. -/
syntax (name := wordsRetOffStx) "words_ret_off% " term:max : term
syntax (name := wordsRetOffIdxStx) "words_ret_off% " term:max num : term

@[term_elab wordsRetOffStx, term_elab wordsRetOffIdxStx]
def elabWordsRetOff : TermElab := fun stx expectedType? => do
  let (wordsStx, k) ← match stx with
    | `(words_ret_off% $w:term) => pure (w, 0)
    | `(words_ret_off% $w:term $k:num) => pure (w, k.getNat)
    | _ => throwUnsupportedSyntax
  let wordsExpr ← elabTerm wordsStx none
  synthesizeSyntheticMVarsNoPostponing
  let wordsExpr ← instantiateMVars wordsExpr
  let off ← lookupWordsRetOff wordsExpr k
  elabByteOffBitVec64 off expectedType?

/-- `words_condbr_off% <words> [k]`: function-relative byte offset (`BitVec 64` by default) of the
    `k`-th (0-indexed, default `0`) conditional branch (`B.cond`, `CBZ`, `CBNZ`, `TBZ`, `TBNZ`)
    in `<words>`. -/
syntax (name := wordsCondBrOffStx) "words_condbr_off% " term:max : term
syntax (name := wordsCondBrOffIdxStx) "words_condbr_off% " term:max num : term

@[term_elab wordsCondBrOffStx, term_elab wordsCondBrOffIdxStx]
def elabWordsCondBrOff : TermElab := fun stx expectedType? => do
  let (wordsStx, k) ← match stx with
    | `(words_condbr_off% $w:term) => pure (w, 0)
    | `(words_condbr_off% $w:term $k:num) => pure (w, k.getNat)
    | _ => throwUnsupportedSyntax
  let wordsExpr ← elabTerm wordsStx none
  synthesizeSyntheticMVarsNoPostponing
  let wordsExpr ← instantiateMVars wordsExpr
  let off ← lookupWordsCondBrOff wordsExpr k
  elabByteOffBitVec64 off expectedType?

/-- `words_insn_off% <words> <target> [k]`: function-relative byte offset (`BitVec 64` by default)
    of the `k`-th (0-indexed, default `0`) instruction in `<words>` matching `<target>` (a 32-bit
    instruction word literal, a category string `"ret"` / `"condbr"` / `"bl"` / `"b"` / `"cbz"` /
    `"cbnz"` / `"tbz"` / `"tbnz"` / `"b.cond"`, or a predicate `BitVec 32 → Bool`). -/
syntax (name := wordsInsnOffStx) "words_insn_off% " term:max term:max : term
syntax (name := wordsInsnOffIdxStx) "words_insn_off% " term:max term:max num : term

@[term_elab wordsInsnOffStx, term_elab wordsInsnOffIdxStx]
def elabWordsInsnOff : TermElab := fun stx expectedType? => do
  let (wordsStx, targetStx, k) ← match stx with
    | `(words_insn_off% $w:term $t:term) => pure (w, t, 0)
    | `(words_insn_off% $w:term $t:term $k:num) => pure (w, t, k.getNat)
    | _ => throwUnsupportedSyntax
  let wordsExpr ← elabTerm wordsStx none
  let targetExpr ← elabTerm targetStx none
  synthesizeSyntheticMVarsNoPostponing
  let wordsExpr ← instantiateMVars wordsExpr
  let targetExpr ← instantiateMVars targetExpr
  let off ← lookupWordsInsnOff wordsExpr targetExpr k
  elabByteOffBitVec64 off expectedType?

/-- Look up symbol `sym` in a `List (String × Nat)` expression (`symbols` or `stubs`). -/
def findSymbolInAssocExpr? (listExpr : Expr) (sym : String) : MetaM (Option Nat) := do
  let elems ← ProofLib.ProgramReflection.listElemsWhnf listExpr
  for elem in elems do
    let e ← if elem.isAppOfArity ``Prod.mk 4 then pure elem
      else withTransparency .all (whnf elem)
    if e.isAppOfArity ``Prod.mk 4 then
      if let some s ← evalStringExpr? (e.getArg! 2) then
        if s == sym then
          if let some off ← evalNatExpr? (e.getArg! 3) then
            return some off
  return none

/-- Look up symbol `sym`'s byte offset in `codeExpr` (`Program`, `Obj.LinkedImage`, `FnCode`,
    `CodeBundle`, or generated `*Code` / `*Code_tree` constant). -/
partial def lookupSymOffInCode? (codeExpr : Expr) (sym : String) : MetaM (Option Nat) := do
  let e := codeExpr.consumeMData
  if let some c := e.getAppFn.constName? then
    let cStr := c.toString
    let baseConst? : Option Name :=
      if cStr.endsWith "_tree" then
        if let .str p s := c then some (.str p (s.dropEnd 5).toString) else none
      else some c
    if let some bc := baseConst? then
      if let some entry ← (try some <$> lookupOff bc sym catch _ => pure none) then
        return some entry.val
      if let some info := ProofLib.ProgramReflection.lookupFnEntry? (← getEnv) sym (some bc) then
        return some info.off
  if let some info := ProofLib.ProgramReflection.lookupFnEntry? (← getEnv) sym none then
    return some info.off
  let ty ← withTransparency .all (whnf (← inferType e))
  if ty.isConstOf ``Arm64.Program then
    if let some off ← findSymbolInAssocExpr? (mkApp (mkConst ``Arm64.Program.symbols) e) sym then
      return some off
    if let some off ← findSymbolInAssocExpr? (mkApp (mkConst ``Arm64.Program.stubs) e) sym then
      return some off
  if ty.isConstOf `Arm64.Obj.LinkedImage then
    if let some off ← findSymbolInAssocExpr? (mkApp (mkConst `Arm64.Obj.LinkedImage.symbols) e) sym then
      return some off
    if let some off ← findSymbolInAssocExpr? (mkApp (mkConst `Arm64.Obj.LinkedImage.stubs) e) sym then
      return some off
  if ty.isConstOf ``Arm64.FnCode then
    let fnNameExpr := mkApp (mkConst ``Arm64.FnCode.fnName) e
    if (← evalStringExpr? fnNameExpr) == some sym then
      let pinExpr ← withTransparency .all (whnf (mkApp (mkConst ``Arm64.FnCode.pin) e))
      if pinExpr.isAppOfArity ``Arm64.FnPin.off 1 then
        return ← evalNatExpr? (pinExpr.getArg! 0)
      if pinExpr.isAppOfArity ``Arm64.FnPin.addr 1 then
        if let some (64, v) ← evalBitVecExpr? (pinExpr.getArg! 0) then
          return some v
      return some 0
  if ty.isAppOfArity ``List 1 then
    let elemTy ← withTransparency .all (whnf (ty.getArg! 0))
    if elemTy.isConstOf ``Arm64.FnCode then
      let elems ← ProofLib.ProgramReflection.listElemsWhnf e
      for fnExpr in elems do
        if let some off ← lookupSymOffInCode? fnExpr sym then
          return some off
  return none

/-- Look up symbol `sym`'s size in bytes in `codeExpr` if known. -/
def lookupSymSizeInCode? (codeExpr : Expr) (sym : String) : MetaM (Option Nat) := do
  let e := codeExpr.consumeMData
  if let some c := e.getAppFn.constName? then
    let bc : Name :=
      if let .str p s := c then
        if s.endsWith "_tree" then .str p (s.dropEnd 5).toString else c
      else c
    if let some entry ← (try some <$> lookup bc .fnSize sym catch _ => pure none) then
      return some entry.val
    if let some info := ProofLib.ProgramReflection.lookupFnEntry? (← getEnv) sym (some bc) then
      return some info.sizeBytes
  if let some info := ProofLib.ProgramReflection.lookupFnEntry? (← getEnv) sym none then
    return some info.sizeBytes
  return none

/-- Decompose an address/offset expression (or symbol name in `codeExpr`) into
    `(symbolicBase?, byteOff : UInt64)`. -/
partial def resolveAddrOrSymOff? (codeExpr : Expr) (e : Expr) :
    MetaM (Option (Option Expr × UInt64 × Option String)) := do
  let e := e.consumeMData
  if let some sym ← evalStringExpr? e then
    if let some off ← lookupSymOffInCode? codeExpr sym then
      return some (none, off.toUInt64, some sym)
    else
      return none
  if e.isAppOfArity ``Arm64.Program.fnAddr 2 then
    let progExpr := e.getArg! 0
    if let some sym ← evalStringExpr? (e.getArg! 1) then
      if let some off ← lookupSymOffInCode? progExpr sym then
        let baseExpr := mkApp (mkConst ``Arm64.Program.base) progExpr
        if let some (64, bVal) ← evalBitVecExpr? baseExpr then
          return some (none, bVal.toUInt64 + off.toUInt64, some sym)
        else
          let bNorm ← withTransparency .default (whnf baseExpr)
          return some (some bNorm, off.toUInt64, some sym)
  if e.isAppOfArity `Arm64.Obj.LinkedImage.fnAddr 3 then
    let liExpr := e.getArg! 0
    let bExpr := e.getArg! 1
    if let some sym ← evalStringExpr? (e.getArg! 2) then
      if let some off ← lookupSymOffInCode? liExpr sym then
        if let some (64, bVal) ← evalBitVecExpr? bExpr then
          return some (none, bVal.toUInt64 + off.toUInt64, some sym)
        else
          return some (some bExpr, off.toUInt64, some sym)
  if let some (64, v) ← evalBitVecExpr? e then
    return some (none, v.toUInt64, none)
  if let some v ← evalNatExpr? e then
    return some (none, v.toUInt64, none)
  if e.isAppOfArity ``HAdd.hAdd 6 then
    if let some (64, c) ← evalBitVecExpr? (e.getArg! 5) then
      if let some (b?, o, sym?) ← resolveAddrOrSymOff? codeExpr (e.getArg! 4) then
        return some (b?, o + c.toUInt64, sym?)
      else
        return some (some (e.getArg! 4), c.toUInt64, none)
    if let some (64, c) ← evalBitVecExpr? (e.getArg! 4) then
      if let some (b?, o, sym?) ← resolveAddrOrSymOff? codeExpr (e.getArg! 5) then
        return some (b?, c.toUInt64 + o, sym?)
      else
        return some (some (e.getArg! 5), c.toUInt64, none)
  if e.isAppOfArity ``HSub.hSub 6 then
    if let some (64, c) ← evalBitVecExpr? (e.getArg! 5) then
      if let some (b?, o, sym?) ← resolveAddrOrSymOff? codeExpr (e.getArg! 4) then
        return some (b?, o - c.toUInt64, sym?)
      else
        return some (some (e.getArg! 4), (0 : UInt64) - c.toUInt64, none)
  return none

/-- Decode the 64-bit signed byte displacement `((imm26.signExtend 64) <<< 2)` of a `B`/`BL` word `w`. -/
def branchDispUInt64 (w : UInt32) : UInt64 :=
  let imm26 : UInt64 := (w &&& 0x03ffffff).toUInt64
  let signedImm26 : UInt64 :=
    if (imm26 &&& 0x02000000) != 0 then
      imm26 ||| 0xfffffffffc000000
    else
      imm26
  signedImm26 <<< 2

/-- Scan a slice `[startWordIdx, endWordIdx)` of `words` for `BL` (or tail-call `B`) instructions
    whose displacement `relOff + branchDisp` from `entry` equals `targetDisp`. -/
def scanWordsForBlTarget (words : Array UInt32) (startWordIdx endWordIdx : Nat)
    (targetDisp : UInt64) : Array Nat × Array (Nat × UInt64) := Id.run do
  let hi := Nat.min endWordIdx words.size
  let mut matching : Array Nat := #[]
  let mut allCalls : Array (Nat × UInt64) := #[]
  for i in [0 : hi - startWordIdx] do
    let w := words[startWordIdx + i]!
    if isBranchImmUInt32 w then
      let relOff : UInt64 := (4 * i).toUInt64
      let disp := branchDispUInt64 w
      let callTargetDisp := relOff + disp
      allCalls := allCalls.push (4 * i, callTargetDisp)
      if callTargetDisp == targetDisp then
        matching := matching.push (4 * i)
  return (matching, allCalls)

/-- Find the function-relative byte offset (`4 * insnIdx`) of the `k`-th (0-indexed) `BL` (or `B`)
    instruction in `codeExpr` starting from `entryExpr` and targeting `targetExpr`. -/
def lookupCodeCallOff (codeExpr entryExpr targetExpr : Expr) (k : Nat := 0) : MetaM Nat := do
  let some (bEntry?, entryOff, entrySym?) ← resolveAddrOrSymOff? codeExpr entryExpr
    | throwError "code_call_off%: could not resolve function entry `{entryExpr}`"
  let some (bTarget?, targetOff, _targetSym?) ← resolveAddrOrSymOff? codeExpr targetExpr
    | throwError "code_call_off%: could not resolve target `{targetExpr}`"
  if bEntry?.isSome || bTarget?.isSome then
    unless bEntry? == bTarget? do
      throwError "code_call_off%: entry `{entryExpr}` and target `{targetExpr}` do not share the same base address"
  let targetDisp : UInt64 := targetOff - entryOff
  let mut effectiveCode := codeExpr.consumeMData
  let codeTy ← withTransparency .all (whnf (← inferType effectiveCode))
  if codeTy.isAppOfArity ``List 1 then
    let elemTy ← withTransparency .all (whnf (codeTy.getArg! 0))
    if elemTy.isConstOf ``Arm64.FnCode then
      let elems ← ProofLib.ProgramReflection.listElemsWhnf effectiveCode
      let mut foundFn? : Option Expr := none
      for fnExpr in elems do
        if let some sym := entrySym? then
          if (← evalStringExpr? (mkApp (mkConst ``Arm64.FnCode.fnName) fnExpr)) == some sym then
            foundFn? := some fnExpr
            break
        else if let some off ← lookupSymOffInCode? fnExpr "" then
          if off.toUInt64 == entryOff then
            foundFn? := some fnExpr
            break
      if let some fnExpr := foundFn? then
        effectiveCode := fnExpr
      else if h : 0 < elems.size then
        effectiveCode := elems[0]
  let words ← extractWordsFromExpr effectiveCode
  let effTy ← withTransparency .all (whnf (← inferType effectiveCode))
  let mut startWordIdx : Nat := 0
  let mut endWordIdx : Nat := words.size
  if effTy.isConstOf ``Arm64.Program || effTy.isConstOf `Arm64.Obj.LinkedImage then
    let progBaseOff : UInt64 ←
      if effTy.isConstOf ``Arm64.Program then
        let bExpr := mkApp (mkConst ``Arm64.Program.base) effectiveCode
        if let some (64, bv) ← evalBitVecExpr? bExpr then pure bv.toUInt64 else pure 0
      else pure 0
    let relEntryByte := (entryOff - progBaseOff).toNat
    if relEntryByte / 4 < words.size then
      startWordIdx := relEntryByte / 4
      if let some sym := entrySym? then
        if let some sz ← lookupSymSizeInCode? effectiveCode sym then
          endWordIdx := Nat.min words.size (startWordIdx + sz / 4)
  else if let some sym := entrySym? then
    if entryOff.toNat / 4 < words.size then
      startWordIdx := entryOff.toNat / 4
      if let some sz ← lookupSymSizeInCode? effectiveCode sym then
        endWordIdx := Nat.min words.size (startWordIdx + sz / 4)
  let (matching0, allCalls0) := scanWordsForBlTarget words startWordIdx endWordIdx targetDisp
  let mut matching := matching0
  let mut allCalls := allCalls0
  -- Whole-image `WordTree` fallback when `entryOff` is an image-relative byte offset.
  if matching.isEmpty && startWordIdx == 0 && entryOff.toNat > 0 &&
     entryOff.toNat % 4 == 0 && entryOff.toNat / 4 < words.size then
    let altStart := entryOff.toNat / 4
    let (m2, c2) := scanWordsForBlTarget words altStart words.size targetDisp
    if !m2.isEmpty then
      matching := m2
      allCalls := c2
  if matching.isEmpty then
    let callsDesc := allCalls.toList.map fun (off, d) =>
      let absTgt := entryOff + d
      s!"+{off} -> 0x{String.ofList (Nat.toDigits 16 absTgt.toNat)}"
    let callsStr := if callsDesc.isEmpty then "none" else String.intercalate ", " callsDesc
    throwError "code_call_off%: no BL/B call targeting `{targetExpr}` (displacement 0x{String.ofList (Nat.toDigits 16 targetDisp.toNat)}) \
      found in function (calls in function: {callsStr})"
  if h : k < matching.size then
    return matching[k]
  else
    throwError "code_call_off%: occurrence index {k} out of range for target `{targetExpr}` \
      (found {matching.size} call(s) at byte offset(s) {matching.toList})"

/-- `code_call_off% <code> <entry> <target> [k]`: function-relative byte offset (`BitVec 64` by
    default, or `Nat` when expected type is `Nat`) of the `k`-th (0-indexed, default `0`) `BL`
    (or tail-call `B`) instruction in `<code>` from function `<entry>` targeting `<target>`. -/
syntax (name := codeCallOffStx) "code_call_off% " term:max term:max term:max : term
syntax (name := codeCallOffIdxStx) "code_call_off% " term:max term:max term:max num : term

@[term_elab codeCallOffStx, term_elab codeCallOffIdxStx]
def elabCodeCallOff : TermElab := fun stx expectedType? => do
  let (codeStx, entryStx, targetStx, k) ← match stx with
    | `(code_call_off% $c:term $e:term $t:term) => pure (c, e, t, 0)
    | `(code_call_off% $c:term $e:term $t:term $k:num) => pure (c, e, t, k.getNat)
    | _ => throwUnsupportedSyntax
  let codeExpr ← elabTerm codeStx none
  let entryExpr ← elabTerm entryStx none
  let targetExpr ← elabTerm targetStx none
  synthesizeSyntheticMVarsNoPostponing
  let codeExpr ← instantiateMVars codeExpr
  let entryExpr ← instantiateMVars entryExpr
  let targetExpr ← instantiateMVars targetExpr
  let off ← lookupCodeCallOff codeExpr entryExpr targetExpr k
  elabByteOffBitVec64 off expectedType?

/-- `code_call_addr% <code> <entry> <target> [k]`: cut address
    `<entry> + code_call_off% <code> <entry> <target> [k]` (`BitVec 64`). -/
syntax (name := codeCallAddrStx) "code_call_addr% " term:max term:max term:max : term
syntax (name := codeCallAddrIdxStx) "code_call_addr% " term:max term:max term:max num : term

@[term_elab codeCallAddrStx, term_elab codeCallAddrIdxStx]
def elabCodeCallAddr : TermElab := fun stx expectedType? => do
  let (codeStx, entryStx, targetStx, k) ← match stx with
    | `(code_call_addr% $c:term $e:term $t:term) => pure (c, e, t, 0)
    | `(code_call_addr% $c:term $e:term $t:term $k:num) => pure (c, e, t, k.getNat)
    | _ => throwUnsupportedSyntax
  let codeExpr ← elabTerm codeStx none
  let entryExpr ← elabTerm entryStx none
  let targetExpr ← elabTerm targetStx none
  synthesizeSyntheticMVarsNoPostponing
  let codeExpr ← instantiateMVars codeExpr
  let entryExpr ← instantiateMVars entryExpr
  let targetExpr ← instantiateMVars targetExpr
  let off ← lookupCodeCallOff codeExpr entryExpr targetExpr k
  let lit := Syntax.mkNumLit (toString off)
  elabTerm (← `(($entryStx : BitVec 64) + BitVec.ofNat 64 $lit)) expectedType?

end ProofLib.CodeLookup
