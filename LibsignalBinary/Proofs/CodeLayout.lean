/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import ProofLib.SepLogic.CodeLookup
public import ProofLib.ProgramReflection
public import ProofLib.GenDecodes
public import ProofLib.VCGen
public import Arm64.Legacy.Object.LinkedImage
public import GeneratedLean.LibsignalSessionObj
public meta import Lean
public meta import ProofLib.SepLogic.CodeLookup
public meta import ProofLib.ProgramReflection
public meta import ProofLib.GenDecodes
public meta import ProofLib.VCGen
public meta import Arm64.Legacy.Object.LinkedImage
public meta import GeneratedLean.LibsignalSessionObj -- shake: keep

/-!
# Layout-Independent Image Lookups and Generated Decode Lemmas

Provides elaboration-time symbol, data, relocation, and cross-reference lookups along with
instruction-decode and rebase-fetch command generators, all evaluating to plain numerals or
kernel-checked `Eq.refl` theorems so re-exporting a linked image does not break proofs:
- **Closed `Nat`/`BitVec` numerals**: `num% t`, `bv% t`, `pageOf`, and `page% t`.
- **`LinkedImage` data lookups**: `img_sym%`, `img_str%`, `img_bytes%`, `img_reloc%`, and
  `img_field%` (failing at elaboration if missing or non-unique).
- **Code cross-references**: `code_xref% tree pc [pc₂]` for `b`/`bl`/`adr` targets and
  `adrp` + `add`/`ldr`/`str` pairs.
- **Decode and rebase-fetch generators**: `gen_decodes` and `gen_rebase_fetches`.
- **Libsignal session image shorthands**: `ls_off%`, `ls_rel%`, `ls_hook%`, `ls_stub%`,
  `ls_lemma%`, `ls_sym%`, `ls_str%`, `ls_bytes%`, `ls_reloc%`, `ls_field%`, `ls_xref%`,
  `ls_decode%`, `ls_fetch%`, `ls_rebase_fetch%`, and `ls_attribute`.
-/

@[expose] public section

namespace CryptoVerification.CodeLayout

open Lean Meta Elab Term Command Arm64 ProofLib.ProgramReflection

public meta section

/-! ## Numerals -/

partial def natLit? : Expr → Option Nat
  | .lit (.natVal n) => some n
  | .mdata _ e => natLit? e
  | e => if e.isAppOfArity ``OfNat.ofNat 3 then natLit? (e.getArg! 1) else none

/-- Evaluate a closed `Nat` term to a numeral.

`withSynthesize` scopes the synthesis to the mvars created while elaborating `t`. A bare
`synthesizeSyntheticMVarsNoPostponing` would also force every synthetic mvar still pending in the
enclosing term (postponed field notation such as `sf.pc` in `∀ sf Pf, sf.pc = …`, or an earlier
`(by ac_rfl)` argument whose type is not known yet), so a `num%`/`bv%`/`ls_*%` form could change
how the surrounding term elaborates. -/
def evalNat (t : Term) (what : String) : TermElabM Nat := do
  let e ← withSynthesize <| elabTermEnsuringType t (mkConst ``Nat)
  let e ← instantiateMVars e
  if e.hasMVar || e.hasFVar then
    throwError "{what}: {e} is not a closed `Nat` term"
  let r ← withTransparency .all <| reduce e
  let some n := natLit? r
    | throwError "{what}: {e} does not reduce to a numeral (got {r})"
  return n

/-- `num% t`: the closed `Nat` term `t` evaluated and elaborated as a bare numeral at the expected
    type (the same term the numeral itself elaborates to, also at `BitVec w`). -/
syntax:max (name := numStx) "num% " term:max : term

@[term_elab numStx] def elabNum : TermElab := fun stx expectedType? => do
  match stx with
  | `(num% $t) =>
    let n ← evalNat t "num%"
    elabTerm (Syntax.mkNumLit (toString n)) expectedType?
  | _ => throwUnsupportedSyntax

/-- `bv% t`: `BitVec.ofNat 64 (num% t)`, the term `n#64` elaborates to. -/
macro:max "bv% " t:term:max : term => `(BitVec.ofNat 64 (num% $t))

end

/-- Start of the 4 KiB page of `a` (what `adrp` computes, relative to a page-aligned base). -/
@[reducible] def pageOf (a : Nat) : Nat := a / 4096 * 4096

public meta section

/-- `page% t`: `pageOf t` without opening the namespace (for use inside `num%` / `bv%`). -/
macro:max "page% " t:term:max : term => `(($t) / 4096 * 4096)

/-! ## Linked-image data lookups -/

/-- What the lookups need from a `LinkedImage` constant. Offsets are image offsets. -/
structure ImageInfo where
  dataOff : Nat
  data : ByteArray
  gotOff : Nat
  /-- `(slot offset, width, target)`, slot offsets absolute. -/
  relocs : Array (Nat × Nat × Nat)
  symbols : Array (String × Nat)
  stubs : Array (String × Nat)
  externData : Array (String × Nat × Nat)
  deriving Inhabited

initialize imageInfoCache : IO.Ref (Std.HashMap Name ImageInfo) ← IO.mkRef {}

def whnfAll (e : Expr) : MetaM Expr := withTransparency .all (whnf e)

partial def natOf (e : Expr) : MetaM Nat := do
  if let some n := natLit? e then return n
  let e' ← whnfAll e
  if let some n := natLit? e' then return n
  let r ← withTransparency .all (reduce e)
  match natLit? r with
  | some n => return n
  | none => throwError "image info: expected a numeral, got {e}"

partial def strOf (e : Expr) : MetaM String := do
  match e with
  | .lit (.strVal s) => return s
  | .mdata _ e => strOf e
  | _ =>
    match ← whnfAll e with
    | .lit (.strVal s) => return s
    | e' => throwError "image info: expected a string literal, got {e'}"

/-- Byte value of a `BitVec 8` element (`BitVec.ofNat 8 n`, or anything reducing to a numeral). -/
partial def byteOf (e : Expr) : MetaM Nat := do
  if e.isAppOfArity ``BitVec.ofNat 2 then
    if let some n := natLit? (e.getArg! 1) then return n % 256
  let e' ← whnfAll e
  if e'.isAppOfArity ``BitVec.ofNat 2 then
    return (← natOf (e'.getArg! 1)) % 256
  if e'.isAppOfArity ``BitVec.ofFin 2 then
    let fin ← whnfAll (e'.getArg! 1)
    if fin.isAppOfArity ``Fin.mk 3 then return (← natOf (fin.getArg! 1)) % 256
  throwError "image info: expected a byte, got {e}"

def ctorArgs (e : Expr) (ctor : Name) (n : Nat) : MetaM (Array Expr) := do
  let e ← if e.isAppOfArity ctor n then pure e else whnfAll e
  unless e.isAppOfArity ctor n do throwError "image info: expected `{ctor}`, got {e}"
  return e.getAppArgs

def field (img : Name) (f : Name) : MetaM Expr :=
  whnfAll (mkApp (mkConst f) (mkConst img))

def parseImage (img : Name) : MetaM ImageInfo := do
  let dataOff ← natOf (← field img ``Obj.LinkedImage.dataOff)
  let gotOff ← natOf (← field img ``Obj.LinkedImage.gotOff)
  let dataElems ← listElemsWhnf (mkApp (mkConst ``Obj.LinkedImage.data) (mkConst img))
  let mut data := ByteArray.emptyWithCapacity dataElems.size
  for b in dataElems do data := data.push (← byteOf b).toUInt8
  let mut relocs := #[]
  for r in ← listElemsWhnf (mkApp (mkConst ``Obj.LinkedImage.relocs) (mkConst img)) do
    let a ← ctorArgs r ``Obj.DataReloc.mk 3
    relocs := relocs.push (dataOff + (← natOf a[0]!), ← natOf a[1]!, ← natOf a[2]!)
  let pairs (f : Name) : MetaM (Array (String × Nat)) := do
    let mut out := #[]
    for p in ← listElemsWhnf (mkApp (mkConst f) (mkConst img)) do
      let a ← ctorArgs p ``Prod.mk 4
      out := out.push (← strOf a[2]!, ← natOf a[3]!)
    return out
  let symbols ← pairs ``Obj.LinkedImage.symbols
  let stubs ← pairs ``Obj.LinkedImage.stubs
  let mut externData := #[]
  for p in ← listElemsWhnf (mkApp (mkConst ``Obj.LinkedImage.externData) (mkConst img)) do
    let a ← ctorArgs p ``Prod.mk 4
    let b ← ctorArgs a[3]! ``Prod.mk 4
    externData := externData.push (← strOf a[2]!, ← natOf b[2]!, ← natOf b[3]!)
  return { dataOff, data, gotOff, relocs, symbols, stubs, externData }

/-- The (cached) `ImageInfo` of the `LinkedImage` constant `img`. -/
def imageInfo (img : Name) : MetaM ImageInfo := do
  if let some i := (← imageInfoCache.get).get? img then return i
  let i ← parseImage img
  imageInfoCache.modify (·.insert img i)
  return i

/-- Absolute offsets of every occurrence of `needle` in the data region. -/
def ImageInfo.occurrences (ii : ImageInfo) (needle : ByteArray) : Array Nat := Id.run do
  let n := needle.size
  let d := ii.data
  let mut out := #[]
  if n == 0 || n > d.size then return out
  for i in [0 : d.size - n + 1] do
    let mut ok := true
    for j in [0 : n] do
      if d.get! (i + j) != needle.get! j then
        ok := false
        break
    if ok then out := out.push (ii.dataOff + i)
  return out

/-- End of the code (after the last extern stub). -/
def ImageInfo.codeLen (ii : ImageInfo) : Nat :=
  ii.stubs.foldl (fun m (_, o) => max m (o + 4)) 0

/-- End of the text (the first extern stub; the code length if there are none). -/
def ImageInfo.textEnd (ii : ImageInfo) : Nat :=
  ii.stubs.foldl (fun m (_, o) => min m o) ii.codeLen

def unique (what : String) (key : String) (xs : Array Nat) : TermElabM Nat := do
  match xs with
  | #[a] => return a
  | #[] => throwError "{what}: {key} not found in the image"
  | _ => throwError "{what}: {key} is not unique in the image (at {xs.toList.map toHexString})"
where toHexString (n : Nat) : String := "0x" ++ String.ofList (Nat.toDigits 16 n)

def parseHex (s : String) : Option ByteArray := Id.run do
  let cs := s.toList.filter (· != '_')
  if cs.length % 2 != 0 then return none
  let digit (c : Char) : Option Nat :=
    if '0' ≤ c && c ≤ '9' then some (c.toNat - '0'.toNat)
    else if 'a' ≤ c && c ≤ 'f' then some (c.toNat - 'a'.toNat + 10)
    else if 'A' ≤ c && c ≤ 'F' then some (c.toNat - 'A'.toNat + 10)
    else none
  let mut out := ByteArray.empty
  let mut rest := cs
  while true do
    match rest with
    | h :: l :: t =>
      let some a := digit h | return none
      let some b := digit l | return none
      out := out.push (16 * a + b).toUInt8
      rest := t
    | _ => break
  return some out

/-- `img_sym% img "name"`: offset of defined symbol, extern stub or extern data object `name`. -/
syntax:max (name := imgSymStx) "img_sym% " ident str : term
/-- `img_str% img "text"`: offset of the unique occurrence of `text` (UTF-8) in the data region. -/
syntax:max (name := imgStrStx) "img_str% " ident str : term
/-- `img_bytes% img "hex"`: offset of the unique occurrence of the hex bytes in the data region. -/
syntax:max (name := imgBytesStx) "img_bytes% " ident str : term
/-- `img_reloc% img t`: offset of the unique data relocation slot holding `base + t`. -/
syntax:max (name := imgRelocStx) "img_reloc% " ident term:max : term
/-- `img_field% img f` for `f ∈ {dataOff, gotOff, codeLen, textEnd, dataLen}`. -/
syntax:max (name := imgFieldStx) "img_field% " ident ident : term

@[term_elab imgSymStx] def elabImgSym : TermElab := fun stx expectedType? => do
  match stx with
  | `(img_sym% $i:ident $s:str) =>
    let ii ← imageInfo (← realizeGlobalConstNoOverloadWithInfo i)
    let name := s.getString
    let hits := (ii.symbols.filter (·.1 == name)).map (·.2)
    let hits := if hits.isEmpty then (ii.stubs.filter (·.1 == name)).map (·.2) else hits
    let hits := if hits.isEmpty then (ii.externData.filter (·.1 == name)).map (·.2.1) else hits
    let a ← unique "img_sym%" (repr name).pretty hits
    elabTerm (Syntax.mkNumLit (toString a)) expectedType?
  | _ => throwUnsupportedSyntax

@[term_elab imgStrStx] def elabImgStr : TermElab := fun stx expectedType? => do
  match stx with
  | `(img_str% $i:ident $s:str) =>
    let ii ← imageInfo (← realizeGlobalConstNoOverloadWithInfo i)
    let a ← unique "img_str%" (repr s.getString).pretty
      (ii.occurrences s.getString.toUTF8)
    elabTerm (Syntax.mkNumLit (toString a)) expectedType?
  | _ => throwUnsupportedSyntax

@[term_elab imgBytesStx] def elabImgBytes : TermElab := fun stx expectedType? => do
  match stx with
  | `(img_bytes% $i:ident $s:str) =>
    let ii ← imageInfo (← realizeGlobalConstNoOverloadWithInfo i)
    let some bs := parseHex s.getString
      | throwError "img_bytes%: {repr s.getString} is not a hex byte string"
    let a ← unique "img_bytes%" s.getString (ii.occurrences bs)
    elabTerm (Syntax.mkNumLit (toString a)) expectedType?
  | _ => throwUnsupportedSyntax

@[term_elab imgRelocStx] def elabImgReloc : TermElab := fun stx expectedType? => do
  match stx with
  | `(img_reloc% $i:ident $t) =>
    let ii ← imageInfo (← realizeGlobalConstNoOverloadWithInfo i)
    let tgt ← evalNat t "img_reloc%"
    let a ← unique "img_reloc%" s!"a relocation to {tgt}"
      ((ii.relocs.filter (·.2.2 == tgt)).map (·.1))
    elabTerm (Syntax.mkNumLit (toString a)) expectedType?
  | _ => throwUnsupportedSyntax

@[term_elab imgFieldStx] def elabImgField : TermElab := fun stx expectedType? => do
  match stx with
  | `(img_field% $i:ident $f:ident) =>
    let ii ← imageInfo (← realizeGlobalConstNoOverloadWithInfo i)
    let v ← match f.getId.eraseMacroScopes with
      | `dataOff => pure ii.dataOff
      | `gotOff => pure ii.gotOff
      | `codeLen => pure ii.codeLen
      | `textEnd => pure ii.textEnd
      | `dataLen => pure ii.data.size
      | k => throwError "img_field%: unknown field `{k}` (expected dataOff, gotOff, codeLen, \
          textEnd or dataLen)"
    elabTerm (Syntax.mkNumLit (toString v)) expectedType?
  | _ => throwUnsupportedSyntax

/-! ## Generated decode and rebase-fetch lemmas -/

/-- The 4 bytes of the instruction at code offset `off` of the tree constant `tree`. -/
def quadOf (tree : Name) (off : Nat) : MetaM (Nat × Nat × Nat × Nat) := do
  ProofLib.GenDecodes.quadOfTreeVal (← ProofLib.GenDecodes.treeValueOf tree) off

/-! ## Code cross-references -/

/-- The 32-bit instruction word at code offset `off` of the tree constant `tree`. -/
def wordAt (tree : Name) (off : Nat) : MetaM Nat := do
  let (b0, b1, b2, b3) ← quadOf tree off
  return b0 + 0x100 * b1 + 0x00010000 * b2 + 0x1000000 * b3

def sext (v bits : Nat) : Int :=
  if v ≥ 2 ^ (bits - 1) then (v : Int) - 2 ^ bits else v

/-- The target of the PC-relative instruction at `pc`: the address of a `b` / `bl` / `adr`, the
    page of an `adrp`. -/
def pcRelTarget (tree : Name) (pc : Nat) : MetaM Int := do
  let w ← wordAt tree pc
  let imm21 := (((w >>> 5) &&& 0x0007FFFF) <<< 2) ||| ((w >>> 29) &&& 3)
  if w &&& 0x7C000000 == 0x14000000 then
    return pc + 4 * sext (w &&& 0x3FFFFFF) 26
  else if w &&& 0x9F000000 == 0x90000000 then
    return (pc / 4096 * 4096 : Nat) + 4096 * sext imm21 21
  else if w &&& 0x9F000000 == 0x10000000 then
    return pc + sext imm21 21
  else
    throwError "code_xref%: the instruction at {pc} is not `adrp`, `adr`, `b` or `bl`"

/-- `(base register, low-12 byte offset)` of the `add` (immediate, unshifted) or `ldr` / `str`
    (unsigned offset) at `pc`. -/
def lo12At (tree : Name) (pc : Nat) : MetaM (Nat × Nat) := do
  let w ← wordAt tree pc
  let rn := (w >>> 5) &&& 31
  let imm12 := (w >>> 10) &&& 0xFFF
  if w &&& 0x7F800000 == 0x11000000 && (w >>> 22) &&& 1 == 0 then
    return (rn, imm12)
  else if w &&& 0x3B000000 == 0x39000000 then
    let (size, v, opc) := (w >>> 30, (w >>> 26) &&& 1, (w >>> 22) &&& 3)
    return (rn, imm12 * (if v == 1 && size == 0 && opc &&& 2 != 0 then 16 else 2 ^ size))
  else
    throwError "code_xref%: the instruction at {pc} is not an unshifted `add` (immediate) or an \
      unsigned-offset `ldr` / `str`"

/-- The address the code at `pc` refers to: with one offset, the target of the `b` / `bl` / `adr`
    (or the page of the `adrp`) there; with two, `adrp` at `pc` plus the low-12 offset of the
    `add` / `ldr` / `str` at `pc₂`, which must use the register the `adrp` writes. -/
def xrefTarget (tree : Name) (pc : Nat) (pc₂? : Option Nat) : MetaM Nat := do
  let t ← pcRelTarget tree pc
  let t ← match pc₂? with
    | none => pure t
    | some pc₂ =>
      let w ← wordAt tree pc
      unless w &&& 0x9F000000 == 0x90000000 do
        throwError "code_xref%: the instruction at {pc} is not `adrp`"
      let (rn, lo) ← lo12At tree pc₂
      unless rn == w &&& 31 do
        throwError "code_xref%: the instruction at {pc₂} does not use the register the `adrp` \
          at {pc} writes"
      pure (t + lo)
  unless t ≥ 0 do throwError "code_xref%: negative target {t}"
  return t.toNat

/-- `code_xref% tree pc` / `code_xref% tree pc pc₂`: the address the code of the `WordTree`
    constant `tree` refers to at `pc` (see `xrefTarget`). Code offsets survive a re-export, so this
    keys data that has no unique content (identical strings or vtables). -/
syntax:max (name := codeXrefStx) "code_xref% " ident term:max (ppSpace term:max)? : term

@[term_elab codeXrefStx] def elabCodeXref : TermElab := fun stx expectedType? => do
  match stx with
  | `(code_xref% $t:ident $a:term $[$b?:term]?) =>
    let tree ← realizeGlobalConstNoOverloadWithInfo t
    let aVal ← evalNat a "code_xref%"
    let bVal? ← b?.mapM (evalNat · "code_xref%")
    let v ← xrefTarget tree aVal bVal?
    elabTerm (Syntax.mkNumLit (toString v)) expectedType?
  | _ => throwUnsupportedSyntax

/-- The statement `tree.fetchDecodeAt off = some i` of a generated decode lemma for a pre-fetched
    `WordTree` value `treeVal`, delegating instruction decoding and operand normalization to
    `ProofLib.GenDecodes`. With `raw := true`, negative 64-bit immediates stay plain unsigned
    numerals `(2^64 - k)#64`. -/
def decodeStmtOfTreeVal (tree : Name) (treeVal : Expr) (off : Nat) (raw : Bool := false) :
    MetaM Expr := do
  let (w, rhs?) ← ProofLib.GenDecodes.instrRhs? treeVal off raw
  let some rhs := rhs?
    | throwError "gen_decodes: the word {w} at offset {off} does not decode"
  return ProofLib.GenDecodes.decodeStmtOf tree off rhs

/-- The statement `tree.fetchDecodeAt off = some i` of a generated decode lemma, delegating
    instruction decoding and operand normalization to `ProofLib.GenDecodes`. -/
def decodeStmt (tree : Name) (off : Nat) (raw : Bool := false) : MetaM Expr := do
  decodeStmtOfTreeVal tree (← ProofLib.GenDecodes.treeValueOf tree) off raw

syntax "(" term ")" : decodeRange
syntax "(" term ")" " → " "(" term ")" : decodeRange
syntax num " → " "(" term ")" : decodeRange
syntax "(" term ")" " → " num : decodeRange
syntax &"raw " "(" term ")" : decodeRange
syntax &"raw " num " → " num : decodeRange
syntax &"raw " "(" term ")" " → " "(" term ")" : decodeRange
syntax &"raw " num " → " "(" term ")" : decodeRange
syntax &"raw " "(" term ")" " → " num : decodeRange

/-- `gen_decodes <tree> <prefix> [a, b → c, raw d, raw b → c, …]`: the decode lemmas
    `<prefix>_decode_0x<off> : <tree>.fetchDecodeAt off = some …` for the listed offsets
    (`b → c`: every 4-byte offset from `b` to `c`, inclusive; `raw …`: with `raw := true`). -/

def rangeBounds (a b : Nat) (r : Syntax) (raw : Bool := false) :
    CommandElabM (Array (Nat × Bool)) := do
  unless a ≤ b && (b - a) % 4 == 0 do
    throwErrorAt r "gen_decodes: bad range {a} → {b}"
  return (List.range ((b - a) / 4 + 1)).toArray.map (a + 4 * ·, raw)

def rangeOffsets (r : TSyntax `decodeRange) : CommandElabM (Array (Nat × Bool)) := do
  match r with
  | `(decodeRange| $a:num) => return #[(a.getNat, false)]
  | `(decodeRange| raw $a:num) => return #[(a.getNat, true)]
  | `(decodeRange| $a:num → $b:num) => rangeBounds a.getNat b.getNat r
  | `(decodeRange| raw $a:num → $b:num) => rangeBounds a.getNat b.getNat r true
  | `(decodeRange| ($a:term)) =>
    return #[(← liftTermElabM <| evalNat a "gen_decodes", false)]
  | `(decodeRange| raw ($a:term)) =>
    return #[(← liftTermElabM <| evalNat a "gen_decodes", true)]
  | `(decodeRange| ($a:term) → ($b:term)) =>
    let na ← liftTermElabM <| evalNat a "gen_decodes"
    let nb ← liftTermElabM <| evalNat b "gen_decodes"
    rangeBounds na nb r
  | `(decodeRange| raw ($a:term) → ($b:term)) =>
    let na ← liftTermElabM <| evalNat a "gen_decodes"
    let nb ← liftTermElabM <| evalNat b "gen_decodes"
    rangeBounds na nb r true
  | `(decodeRange| $a:num → ($b:term)) =>
    let nb ← liftTermElabM <| evalNat b "gen_decodes"
    rangeBounds a.getNat nb r
  | `(decodeRange| raw $a:num → ($b:term)) =>
    let nb ← liftTermElabM <| evalNat b "gen_decodes"
    rangeBounds a.getNat nb r true
  | `(decodeRange| ($a:term) → $b:num) =>
    let na ← liftTermElabM <| evalNat a "gen_decodes"
    rangeBounds na b.getNat r
  | `(decodeRange| raw ($a:term) → $b:num) =>
    let na ← liftTermElabM <| evalNat a "gen_decodes"
    rangeBounds na b.getNat r true
  | _ => throwUnsupportedSyntax

@[command_elab ProofLib.GenDecodes.genDecodesStx] def elabGenDecodes : CommandElab := fun stx => do
  match stx with
  | `($mods:declModifiers gen_decodes $tree:ident $pfx:ident [$rs:decodeRange,*]) =>
    let mut offs := #[]
    for r in rs.getElems do offs := offs ++ (← rangeOffsets r)
    let modifiers ← elabModifiers mods
    -- Inside a module, name visibility follows the enclosing `public section` (as for `theorem`).
    let isPublic := (← getScope).isPublic
    let pfxStr := pfx.getId.eraseMacroScopes.toString
    liftTermElabM do
      let treeName ← realizeGlobalConstNoOverloadWithInfo tree
      let treeVal ← ProofLib.GenDecodes.treeValueOf treeName
      for (off, raw) in offs do
        let hex := String.ofList (Nat.toDigits 16 off)
        let short := Name.mkSimple s!"{pfxStr}_decode_0x{hex}"
        let declName ← withExporting (isExporting := isPublic) <|
          mkDeclName (← getCurrNamespace) modifiers short
        let ty ← decodeStmtOfTreeVal treeName treeVal off raw
        let lhs := ty.appFn!.appArg!
        ProofLib.GenDecodes.addThm declName.1 ty
          (mkApp2 (mkConst ``Eq.refl [.succ .zero]) ProofLib.GenDecodes.optInstr lhs)
        applyAttributesAt declName.1 modifiers.attrs .afterTypeChecking
        applyAttributesAt declName.1 modifiers.attrs .afterCompilation
  | _ => throwUnsupportedSyntax

/-- `[mods] gen_rebase_fetches <code> [<prefix>] [a, b → c, raw d, …]`: emits kernel-checked
    `[<prefix>_]rebase_fetch_0x<off>` theorems in the current namespace from `<code>_tree` and
    `<code>_fetch_rebase_text`, applying `mods` (e.g. `@[scoped simp, arm64_norm]`). -/
syntax (name := genRebaseFetchesStx)
  declModifiers "gen_rebase_fetches " ident (ident)? " [" decodeRange,* "]" : command

@[command_elab genRebaseFetchesStx] def elabGenRebaseFetches : CommandElab := fun stx => do
  match stx with
  | `($mods:declModifiers gen_rebase_fetches $code:ident $[$pfx?:ident]? [$rs:decodeRange,*]) =>
    let mut offs := #[]
    for r in rs.getElems do offs := offs ++ (← rangeOffsets r)
    let modifiers ← elabModifiers mods
    let isPublic := (← getScope).isPublic
    let stem := match pfx? with
      | some pfx => s!"{pfx.getId.eraseMacroScopes.toString}_rebase_fetch_0x"
      | none => "rebase_fetch_0x"
    liftTermElabM do
      let codeName ← realizeGlobalConstNoOverloadWithInfo code
      let treeName := codeName.appendAfter "_tree"
      let treeVal ← ProofLib.GenDecodes.treeValueOf treeName
      let fetchRebaseText := codeName.appendAfter "_fetch_rebase_text"
      let ci ← getConstInfo fetchRebaseText
      let stripAuto (e : Expr) : Expr := if e.isAppOfArity ``autoParam 2 then e.getArg! 0 else e
      let (bTy, xTy, textEndE, pow64E) ← forallTelescope ci.type fun xs _ => do
        unless xs.size == 7 do
          throwError "gen_rebase_fetches: unexpected arity {xs.size} for `{fetchRebaseText}`"
        let bTy ← inferType xs[0]!
        let xTy ← inferType xs[1]!
        let htextProp := stripAuto (← inferType xs[5]!)
        let hoffProp := stripAuto (← inferType xs[6]!)
        return (bTy, xTy, htextProp.getArg! 3, hoffProp.getArg! 3)
      let natTy := Lean.mkConst ``Nat
      let instLTNatE := Lean.mkConst ``instLTNat
      let reflTrue := mkApp2 (mkConst ``Eq.refl [1]) (Lean.mkConst ``Bool) (Lean.mkConst ``Bool.true)
      let mkLtPrf (aE boundE : Expr) : Expr :=
        let propE := mkApp4 (mkConst ``LT.lt [0]) natTy instLTNatE aE boundE
        let instE := mkApp2 (Lean.mkConst ``Nat.decLt) aE boundE
        mkApp3 (Lean.mkConst ``of_decide_eq_true) propE instE reflTrue
      let currNs ← getCurrNamespace
      withLocalDeclD `b bTy fun b => withLocalDeclD `X xTy fun X => do
        for (off, raw) in offs do
          let (w, rhs?) ← ProofLib.GenDecodes.instrRhs? treeVal off raw
          let some rhs := rhs?
            | throwError "gen_rebase_fetches: the word {w} at offset {off} does not decode"
          let hex := String.ofList (Nat.toDigits 16 off)
          let short := Name.mkSimple s!"{stem}{hex}"
          let declName ← withExporting (isExporting := isPublic) <| mkDeclName currNs modifiers short
          let dTy := ProofLib.GenDecodes.decodeStmtOf treeName off rhs
          let dPrf := mkApp2 (mkConst ``Eq.refl [.succ .zero]) ProofLib.GenDecodes.optInstr
            dTy.appFn!.appArg!
          let offE := mkNatLit off
          let p := mkAppN (Lean.mkConst fetchRebaseText)
            #[b, X, offE, rhs.appArg!, dPrf, mkLtPrf offE textEndE, mkLtPrf offE pow64E]
          let rTy ← mkForallFVars #[b, X] (← inferType p)
          let rPrf ← mkLambdaFVars #[b, X] p
          ProofLib.GenDecodes.addThm declName.1 rTy rPrf
          applyAttributesAt declName.1 modifiers.attrs .afterTypeChecking
          applyAttributesAt declName.1 modifiers.attrs .afterCompilation
  | _ => throwUnsupportedSyntax

/-! ## Symbolic `code_fetches` -/

open Lean.Elab.Tactic in
def addCodeFetchesRangeSym (codeId decPrefix : Ident) (b H : Term) (hfn : Ident)
    (off start len : Nat) : TacticM Unit := do
  let n := len / 4
  if n == 0 then return
  let codeBase := codeId.getId.eraseMacroScopes
  let decBase := decPrefix.getId.eraseMacroScopes
  let fetchEntry := mkIdent (codeBase.appendAfter "_fetch_fnAddr_entry")
  let fetchAdd := mkIdent (codeBase.appendAfter "_fetch_fnAddr")
  if start == 0 then
    let dec0 := mkIdent (decBase.appendAfter s!"_decode_0x{String.ofList (Nat.toDigits 16 off)}")
    evalTactic (← `(tactic|
      have := $fetchEntry (b := $b) (H := $H) $hfn (by decide) $dec0))
  let i0 := if start == 0 then 1 else 0
  if n <= i0 then return
  let k0 := start + 4 * i0
  let dec0Add := mkIdent (decBase.appendAfter s!"_decode_0x{String.ofList (Nat.toDigits 16 (off + k0))}")
  let k0q := Syntax.mkNumLit (toString k0)
  let stx0 ← `($fetchAdd (b := $b) (H := $H) (k := $k0q) $hfn (by decide) $dec0Add)
  let g ← getMainGoal
  let fastOk ← g.withContext do
    tryCatchRuntimeEx (do
      let e4 ← instantiateMVars (← Term.elabTermAndSynthesize stx0 none)
      let ty4 ← instantiateMVars (← inferType e4)
      let fn := e4.getAppFn
      let args := e4.getAppArgs
      if args.size == 10 && ty4.isAppOfArity ``Eq 3 && (ty4.getArg! 1).isAppOfArity ``Program.fetch 2 then
        let offExpr := args[3]!
        let textEndExpr := (args[7]!.getArg! 0).getArg! 3
        let pow64Expr := (args[9]!.getArg! 0).getArg! 3
        let natTy := Lean.mkConst ``Nat
        let instLTNatE := Lean.mkConst ``instLTNat
        let hAddNatFn := mkApp4 (Lean.mkConst ``HAdd.hAdd [0, 0, 0]) natTy natTy natTy
          (mkApp2 (Lean.mkConst ``instHAdd [0]) natTy (Lean.mkConst ``instAddNat))
        let reflTrue := mkApp2 (Lean.mkConst ``Eq.refl [1]) (Lean.mkConst ``Bool) (Lean.mkConst ``Bool.true)
        let mkDecLtProof (kExpr boundExpr : Expr) : Expr :=
          let sumE := mkApp2 hAddNatFn offExpr kExpr
          let propE := mkApp4 (Lean.mkConst ``LT.lt [0]) natTy instLTNatE sumE boundExpr
          let instE := mkApp2 (Lean.mkConst ``Nat.decLt) sumE boundExpr
          mkApp3 (Lean.mkConst ``of_decide_eq_true) propE instE reflTrue
        let optInstrTy := ty4.getArg! 0
        let fetchLhs4 := ty4.getArg! 1
        let progExpr := fetchLhs4.getArg! 0
        let addAddr4 := fetchLhs4.getArg! 1
        let addPrefix := addAddr4.appFn!
        let bvOfNatPrefix := (addAddr4.getArg! 5).appFn!
        let env ← getEnv
        let mut hyps : Array Hypothesis := #[{ userName := `this, type := ty4, value := e4 }]
        for i in [i0 + 1 : n] do
          let k := start + 4 * i
          let decName := decBase.appendAfter s!"_decode_0x{String.ofList (Nat.toDigits 16 (off + k))}"
          let some info := env.find? decName | return false
          let someInstExpr := info.type.getArg! 2
          let instExpr := someInstExpr.getArg! 1
          let kExpr := mkNatLit k
          let valK := mkApp10 fn args[0]! args[1]! args[2]! offExpr kExpr instExpr args[6]!
            (mkDecLtProof kExpr textEndExpr) (Lean.mkConst decName) (mkDecLtProof kExpr pow64Expr)
          let tyK := mkApp3 (Lean.mkConst ``Eq [1]) optInstrTy
            (mkApp2 (Lean.mkConst ``Program.fetch) progExpr (mkApp addPrefix (mkApp bvOfNatPrefix kExpr)))
            someInstExpr
          hyps := hyps.push { userName := `this, type := tyK, value := valK }
        let (_, g') ← g.assertHypotheses hyps
        replaceMainGoal [g']
        return true
      else
        return false
    ) (fun _ => pure false)
  if !fastOk then
    for i in [i0 : n] do
      let k := start + 4 * i
      let dec := mkIdent (decBase.appendAfter s!"_decode_0x{String.ofList (Nat.toDigits 16 (off + k))}")
      let kq := Syntax.mkNumLit (toString k)
      evalTactic (← `(tactic|
        have := $fetchAdd (b := $b) (H := $H) (k := $kq) $hfn (by decide) $dec))

open Lean.Elab.Tactic in
def resolveHfnIdent (hfn : Term) : TacticM (Ident × Bool) := do
  if hfn.raw.isIdent then
    return (⟨hfn.raw⟩, false)
  let g ← getMainGoal
  let constName? ← g.withContext do
    tryCatchRuntimeEx (do
      let e ← instantiateMVars (← Term.elabTermAndSynthesize hfn none)
      let e := e.consumeMData
      if e.isConst then
        return some e.constName!
      else
        return none) (fun _ => pure none)
  if let some c := constName? then
    return (mkCIdentFrom hfn c, false)
  let hfnId := mkIdent `_hfn_layout
  evalTactic (← `(tactic| have $hfnId := $hfn))
  return (hfnId, true)

open Lean.Elab.Tactic in
def hideHfnLayoutIfNeeded (added : Bool) : TacticM Unit := do
  if !added then return
  let g ← getMainGoal
  g.withContext do
    let mut lctx ← getLCtx
    if let some decl := lctx.findFromUserName? `_hfn_layout then
      lctx := lctx.setKind decl.fvarId .implDetail
      let g' ← mkFreshExprMVarAt lctx (← getLocalInstances) (← g.getType) .syntheticOpaque (← g.getTag)
      g.assign g'
      replaceMainGoal [g'.mvarId!]

elab "code_fetches " codeId:ident decPrefix:ident b:term:max H:term:max hfn:term:max
    off:term:max len:term:max : tactic => do
  let offVal ← evalNat off "code_fetches"
  let lenVal ← evalNat len "code_fetches"
  let (hfnId, added) ← resolveHfnIdent hfn
  addCodeFetchesRangeSym codeId decPrefix b H hfnId offVal 0 lenVal
  hideHfnLayoutIfNeeded added

elab "code_fetches_range " codeId:ident decPrefix:ident b:term:max H:term:max hfn:term:max
    off:term:max start:term:max len:term:max : tactic => do
  let offVal ← evalNat off "code_fetches_range"
  let startVal ← evalNat start "code_fetches_range"
  let lenVal ← evalNat len "code_fetches_range"
  let (hfnId, added) ← resolveHfnIdent hfn
  addCodeFetchesRangeSym codeId decPrefix b H hfnId offVal startVal lenVal
  hideHfnLayoutIfNeeded added

/-! ## Symbolic decode/fetch lemma lookup and identifier symbol lookups -/

/-- Evaluate a closed `String` term (such as a string literal or `abbrev` identifier) to `String`. -/
def evalStr (t : Term) (what : String) : TermElabM String := do
  if let some s := t.raw.isStrLit? then return s
  let e ← withSynthesize <| elabTermEnsuringType t (mkConst ``String)
  let e ← instantiateMVars e
  if e.hasMVar || e.hasFVar then
    throwError "{what}: {e} is not a closed `String` term"
  strOf e

syntax:max (name := codeOffIdentStx) "code_off% " ident ident : term
syntax:max (name := codeLemmaIdentStx) "code_lemma% " ident ident ident : term
syntax:max (name := imgSymIdentStx) "img_sym% " ident ident : term

def elabCodeOffByName (c : Ident) (s : Term) (expectedType? : Option Expr) : TermElabM Expr := do
  let str ← evalStr s "code_off%"
  let codeName ← realizeGlobalConstNoOverloadWithInfo c
  let e ← ProofLib.CodeLookup.lookupOff codeName str
  ProofLib.CodeLookup.elabNumeral e.val expectedType?

def elabCodeRelByName (c : Ident) (f t : Term) (expectedType? : Option Expr) : TermElabM Expr := do
  let fStr ← evalStr f "code_rel%"
  let tStr ← evalStr t "code_rel%"
  let codeName ← realizeGlobalConstNoOverloadWithInfo c
  let ef ← ProofLib.CodeLookup.lookupOff codeName fStr
  let et ← ProofLib.CodeLookup.lookupOff codeName tStr
  unless ef.val ≤ et.val do
    throwError "code_rel%: {repr tStr} (offset {et.val}) precedes {repr fStr} (offset {ef.val})"
  ProofLib.CodeLookup.elabNumeral (et.val - ef.val) expectedType?

def elabCodeLemmaByName (ref : Syntax) (c : Ident) (kind : Name) (s : Term)
    (expectedType? : Option Expr) : TermElabM Expr := do
  let str ← evalStr s "code_lemma%"
  let code ← realizeGlobalConstNoOverloadWithInfo c
  let e ← ProofLib.CodeLookup.lookupByKindName code kind.eraseMacroScopes str
  let lId := mkCIdentFrom ref e.decl
  if kind.eraseMacroScopes == `fnOff && s.raw.isStrLit?.isNone then
    let offLit := Syntax.mkNumLit (toString e.val)
    let cId := mkCIdentFrom c code
    elabTerm (← `(($lId : Arm64.Program.fnOff $cId $s = $offLit))) expectedType?
  else
    elabTerm lId expectedType?

def elabImgSymByName (i : Ident) (s : Term) (expectedType? : Option Expr) : TermElabM Expr := do
  let ii ← imageInfo (← realizeGlobalConstNoOverloadWithInfo i)
  let name ← evalStr s "img_sym%"
  let hits := (ii.symbols.filter (·.1 == name)).map (·.2)
  let hits := if hits.isEmpty then (ii.stubs.filter (·.1 == name)).map (·.2) else hits
  let hits := if hits.isEmpty then (ii.externData.filter (·.1 == name)).map (·.2.1) else hits
  let a ← unique "img_sym%" (repr name).pretty hits
  elabTerm (Syntax.mkNumLit (toString a)) expectedType?

@[term_elab codeOffIdentStx] def elabCodeOffIdent : TermElab := fun stx expectedType? => do
  match stx with
  | `(code_off% $c:ident $s:ident) => elabCodeOffByName c s expectedType?
  | _ => throwUnsupportedSyntax

@[term_elab codeLemmaIdentStx] def elabCodeLemmaIdent : TermElab := fun stx expectedType? => do
  match stx with
  | `(code_lemma% $c:ident $k:ident $s:ident) => elabCodeLemmaByName stx c k.getId s expectedType?
  | _ => throwUnsupportedSyntax

@[term_elab imgSymIdentStx] def elabImgSymIdent : TermElab := fun stx expectedType? => do
  match stx with
  | `(img_sym% $i:ident $s:ident) => elabImgSymByName i s expectedType?
  | _ => throwUnsupportedSyntax

def mkHexOffIdent (ref : Syntax) (pfx : Ident) (kind : String) (off : Nat) : Ident :=
  let hex := String.ofList (Nat.toDigits 16 off)
  mkIdentFrom ref (pfx.getId.appendAfter s!"_{kind}_0x{hex}")

/-- `ls_decode% pfx off`: elaborates to the identifier `<pfx>_decode_0x<hex>`. -/
syntax:max (name := lsDecodeStx) "ls_decode% " ident term:max : term
/-- `ls_fetch% pfx off`: elaborates to the identifier `<pfx>_fetch_0x<hex>`. -/
syntax:max (name := lsFetchStx) "ls_fetch% " ident term:max : term
/-- `ls_rebase_fetch% pfx off`: elaborates to the identifier `<pfx>_rebase_fetch_0x<hex>`. -/
syntax:max (name := lsRebaseFetchStx) "ls_rebase_fetch% " ident term:max : term

@[term_elab lsDecodeStx] def elabLsDecode : TermElab := fun stx expectedType? => do
  match stx with
  | `(ls_decode% $pfx:ident $t:term) =>
    let off ← evalNat t "ls_decode%"
    elabTerm (mkHexOffIdent stx pfx "decode" off) expectedType?
  | _ => throwUnsupportedSyntax

@[term_elab lsFetchStx] def elabLsFetch : TermElab := fun stx expectedType? => do
  match stx with
  | `(ls_fetch% $pfx:ident $t:term) =>
    let off ← evalNat t "ls_fetch%"
    elabTerm (mkHexOffIdent stx pfx "fetch" off) expectedType?
  | _ => throwUnsupportedSyntax

@[term_elab lsRebaseFetchStx] def elabLsRebaseFetch : TermElab := fun stx expectedType? => do
  match stx with
  | `(ls_rebase_fetch% $pfx:ident $t:term) =>
    let off ← evalNat t "ls_rebase_fetch%"
    elabTerm (mkHexOffIdent stx pfx "rebase_fetch" off) expectedType?
  | _ => throwUnsupportedSyntax

/-! ## Shorthands for the libsignal session image -/

/-- `ls_off% "sym"` (or `ls_off% symIdent`): `code_off% libsignalSessionCode sym`. -/
syntax:max (name := lsOffStx) "ls_off% " term:max : term
/-- `ls_rel% "from" "to"`: `code_rel% libsignalSessionCode "from" "to"`. -/
syntax:max (name := lsRelStx) "ls_rel% " term:max term:max : term
/-- `ls_hook% "sym"`: the generated `libsignalSessionCode_hookAtOff?_0x…` lemma of stub `sym`. -/
syntax:max (name := lsHookStx) "ls_hook% " term:max : term
/-- `ls_stub% "sym"`: the generated `libsignalSessionCode_stubOff_0x…` lemma of stub `sym`. -/
syntax:max (name := lsStubStx) "ls_stub% " term:max : term
/-- `ls_lemma% kind "sym"`: `code_lemma% libsignalSessionCode kind "sym"`. -/
syntax:max (name := lsLemmaStx) "ls_lemma% " ident term:max : term
/-- `ls_sym% "name"`: `img_sym% libsignalSessionImage "name"`. -/
syntax:max (name := lsSymStx) "ls_sym% " term:max : term

@[term_elab lsOffStx] def elabLsOff : TermElab := fun stx expectedType? => do
  match stx with
  | `(ls_off% $s:term) =>
    elabCodeOffByName (mkIdentFrom stx `CryptoVerification.libsignalSessionCode) s expectedType?
  | _ => throwUnsupportedSyntax

@[term_elab lsRelStx] def elabLsRel : TermElab := fun stx expectedType? => do
  match stx with
  | `(ls_rel% $f:term $t:term) =>
    elabCodeRelByName (mkIdentFrom stx `CryptoVerification.libsignalSessionCode) f t expectedType?
  | _ => throwUnsupportedSyntax

@[term_elab lsHookStx] def elabLsHook : TermElab := fun stx expectedType? => do
  match stx with
  | `(ls_hook% $s:term) =>
    elabCodeLemmaByName stx (mkIdentFrom stx `CryptoVerification.libsignalSessionCode) `hookAtOff s expectedType?
  | _ => throwUnsupportedSyntax

@[term_elab lsStubStx] def elabLsStub : TermElab := fun stx expectedType? => do
  match stx with
  | `(ls_stub% $s:term) =>
    elabCodeLemmaByName stx (mkIdentFrom stx `CryptoVerification.libsignalSessionCode) `stubOff s expectedType?
  | _ => throwUnsupportedSyntax

@[term_elab lsLemmaStx] def elabLsLemma : TermElab := fun stx expectedType? => do
  match stx with
  | `(ls_lemma% $k:ident $s:term) =>
    elabCodeLemmaByName stx (mkIdentFrom stx `CryptoVerification.libsignalSessionCode) k.getId s expectedType?
  | _ => throwUnsupportedSyntax

@[term_elab lsSymStx] def elabLsSym : TermElab := fun stx expectedType? => do
  match stx with
  | `(ls_sym% $s:term) =>
    elabImgSymByName (mkIdentFrom stx `CryptoVerification.libsignalSessionImage) s expectedType?
  | _ => throwUnsupportedSyntax

/-- `ls_str% "text"`: `img_str% libsignalSessionImage "text"`. -/
macro:max "ls_str% " s:str : term =>
  `(img_str% $(mkIdent `CryptoVerification.libsignalSessionImage) $s)
/-- `ls_bytes% "hex"`: `img_bytes% libsignalSessionImage "hex"`. -/
macro:max "ls_bytes% " s:str : term =>
  `(img_bytes% $(mkIdent `CryptoVerification.libsignalSessionImage) $s)
/-- `ls_reloc% t`: `img_reloc% libsignalSessionImage t`. -/
macro:max "ls_reloc% " t:term:max : term =>
  `(img_reloc% $(mkIdent `CryptoVerification.libsignalSessionImage) $t)
/-- `ls_field% f`: `img_field% libsignalSessionImage f`. -/
macro:max "ls_field% " f:ident : term =>
  `(img_field% $(mkIdent `CryptoVerification.libsignalSessionImage) $f)
/-- `ls_xref% pc [pc₂]`: `code_xref% libsignalSessionCode_tree pc [pc₂]`. -/
syntax:max "ls_xref% " term:max (ppSpace term:max)? : term
macro_rules
  | `(ls_xref% $a:term) => `(code_xref% $(mkIdent `CryptoVerification.libsignalSessionCode_tree) $a)
  | `(ls_xref% $a:term $b:term) =>
    `(code_xref% $(mkIdent `CryptoVerification.libsignalSessionCode_tree) $a $b)

/-- An item of `ls_attribute`: a lemma name, or a generated layout lemma named by its symbol. -/
declare_syntax_cat lsAttrItem
syntax ident : lsAttrItem
syntax "(" "ls_hook% " term:max ")" : lsAttrItem
syntax "(" "ls_stub% " term:max ")" : lsAttrItem
syntax "(" "ls_lemma% " ident term:max ")" : lsAttrItem
syntax "(" "code_lemma% " ident ident term:max ")" : lsAttrItem
syntax "(" "ls_decode% " ident term:max ")" : lsAttrItem
syntax "(" "ls_fetch% " ident term:max ")" : lsAttrItem
syntax "(" "ls_rebase_fetch% " ident term:max ")" : lsAttrItem

/-- `ls_attribute [attrs] item*`: `attribute [attrs] name*`, where an item may also be
`(ls_hook% "sym")`, `(ls_stub% "sym")`, `(ls_lemma% kind "sym")`, `(code_lemma% code kind "sym")`,
`(ls_decode% pfx off)`, `(ls_fetch% pfx off)` or `(ls_rebase_fetch% pfx off)` (an `attribute`
command takes identifiers only): each is replaced by the name of that generated lemma. -/
syntax (name := lsAttribute) "ls_attribute " "[" sepBy1(Lean.Parser.Term.attrInstance, ", ") "]"
  (ppSpace lsAttrItem)+ : command

@[command_elab lsAttribute] def elabLsAttribute : CommandElab := fun stx => do
  let defaultCode := `CryptoVerification.libsignalSessionCode
  let resolve (ref : Syntax) (code : Name) (kind : Name) (sym : String) : CommandElabM Syntax := do
    let e ← liftTermElabM <| ProofLib.CodeLookup.lookupByKindName code kind sym
    return mkCIdentFrom ref e.decl
  let ids ← stx[4].getArgs.mapM fun it => do
    match it with
    | `(lsAttrItem| $i:ident) => pure i.raw
    | `(lsAttrItem| (ls_hook% $s:term)) =>
      resolve it defaultCode `hookAtOff (← liftTermElabM <| evalStr s "ls_attribute")
    | `(lsAttrItem| (ls_stub% $s:term)) =>
      resolve it defaultCode `stubOff (← liftTermElabM <| evalStr s "ls_attribute")
    | `(lsAttrItem| (ls_lemma% $k:ident $s:term)) =>
      resolve it defaultCode k.getId (← liftTermElabM <| evalStr s "ls_attribute")
    | `(lsAttrItem| (code_lemma% $c:ident $k:ident $s:term)) =>
      let code ← liftTermElabM <| realizeGlobalConstNoOverloadWithInfo c
      resolve it code k.getId (← liftTermElabM <| evalStr s "ls_attribute")
    | `(lsAttrItem| (ls_decode% $pfx:ident $t:term)) =>
      let off ← liftTermElabM <| evalNat t "ls_decode%"
      pure (mkHexOffIdent it pfx "decode" off).raw
    | `(lsAttrItem| (ls_fetch% $pfx:ident $t:term)) =>
      let off ← liftTermElabM <| evalNat t "ls_fetch%"
      pure (mkHexOffIdent it pfx "fetch" off).raw
    | `(lsAttrItem| (ls_rebase_fetch% $pfx:ident $t:term)) =>
      let off ← liftTermElabM <| evalNat t "ls_rebase_fetch%"
      pure (mkHexOffIdent it pfx "rebase_fetch" off).raw
    | _ => throwErrorAt it "ls_attribute: unexpected item"
  elabCommand <| Syntax.node SourceInfo.none ``Lean.Parser.Command.attribute
    #[mkAtom "attribute", mkAtom "[", stx[2], mkAtom "]", mkNullNode ids]

end

end CryptoVerification.CodeLayout
