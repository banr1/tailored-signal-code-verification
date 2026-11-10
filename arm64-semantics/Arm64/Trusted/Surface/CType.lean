/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Lean
public import Arm64.Trusted.Surface.Abi

/-!
# Semantic C Type Judgements

Defines `SemType` and the `c_type_spec` surface command for ownership-typed C function contracts
with categorized caveats. Every C parameter and return value is assigned a semantic type
`T : SemType M` together with an ownership mode (`Own`, `ShrRef`, `MutRef`, `UninitSlot`, `OutPtr`,
or `Val`). Any pure precondition beyond argument well-formedness must be tagged as
`caveat [TAG] "why" : P` with `TAG` in `{API_RESTRICTION, CALLER_TYPESTATE, C_ARITH_BOUND, PARTIAL_SPEC}`;
raw `requires_cond`, `requires_pure`, `guard`, and `preserves` clauses are rejected.

`c_type_spec f ...` elaborates via `lowerParam` to an ordinary `c_spec f ...` (`f : Spec α`) plus a
metadata record `f.cTypeInfo : CTypeSpecInfo` used by `#c_type_report` and `tools/spec-review`.

| Clause | Precondition adds | Postcondition adds |
| :--- | :--- | :--- |
| `c_arg x : Own T m` (consumed) | `⌜T.pureWf x m⌝ ∗ T.interp x m` | - |
| `c_arg x : ShrRef T m` | `⌜T.pureWf x m⌝ ∗ T.interp x m` | `T.interp x m` |
| `c_arg x : MutRef T m ⇝ m'` | `⌜T.pureWf x m⌝ ∗ T.interp x m` | `⌜T.pureWf x m'⌝ ∗ T.interp x m'` |
| `c_arg x : UninitSlot n ⇝ T m'` | `memRegion x n` | `⌜T.pureWf x m'⌝ ∗ T.interp x m'` |
| `c_arg x : OutPtr T m` | `memRegion x 8` | `outPtrPost T x m` |
| `c_arg x : Val T` | `⌜T.valWf x⌝` | - |
| `c_ret : Own T m` (named `(ret : ..)` header) | - | `⌜T.pureWf ret m⌝ ∗ T.interp ret m` |
| `c_ret : ShrRef T m` / `MutRef T m` | - | `⌜T.pureWf ret m⌝` (footprint stays in parent `c_arg` / `c_env`) |
| `c_ret : Val T` | - | `⌜T.valWf ret⌝` |
| `caveat [TAG] "why" : P` | `⌜P⌝` | - |
| `c_env R` / `c_env R ⇝ R'` (allocator pool, globals) | `R` | `R` / `R'` |
| `c_exists (x : X)` | - | wraps the typed/`ensures` postcondition in `∃∗ x : X, ...` |
| `c_stack n` (callee stack budget) | `stackFrameAt s0.sp n` | `stackFrameAt sf.sp n` |
| `requires R` (untyped, flagged in metadata) | `R` | - |

Also forwarded to `c_spec` unchanged: `ensures`, `ensures_pure`, `returns`, `on_panic`, `oom_when`,
`on_oom`, `stack`, `stack16`, `stack32`, `let`, and `load_addr`. Every named register binder must
have a matching `c_arg` clause.

Separating conjunction between spatial argument footprints implies distinct pointer arguments do
not alias (for example, a `ShrRef CStr` source is disjoint from a `MutRef` destination buffer).
-/

public section

namespace Arm64.CType

@[expose] section

open Arm64

/-! ## Semantic Types and Caveat Metadata -/

/-- A semantic C type: canonical representation predicate `interp v m` (pointer or scalar register
    value `v` representing logical model `m`) paired with a pure well-formedness invariant `pureWf`
    required of every typed argument or return of this type. -/
structure SemType (M : Type) where
  /-- C-level type name shown to auditors (e.g. `"struct dynbuf"`). -/
  tyName : String
  /-- Spatial footprint of a value `v` representing model `m`. -/
  interp : BitVec 64 → M → SepProp
  /-- Pure invariant (e.g. `dynbufValid`) on register value/pointer `v : BitVec 64` (arg 1) and
      logical model `m : M` (arg 2). For value-only types used with `Val T`, arg 1 is unused
      (`0#64`) and arg 2 is the register value `x : M` itself. -/
  pureWf : BitVec 64 → M → Prop := fun _ _ => True

/-- Well-formedness of a scalar value of a value type (`Val T`): the register value `x : M` is
    passed as the model argument (arg 2) of `T.pureWf`, with dummy pointer `0#64` as arg 1. -/
@[reducible] def SemType.valWf {M : Type} (T : SemType M) (x : M) : Prop :=
  T.pureWf 0#64 x

/-- The four caveat categories of a `c_type_spec`. -/
inductive CaveatKind where
  /-- Genuine C API precondition: violating it is UB even with well-typed arguments. -/
  | apiRestriction
  /-- Lifecycle / protocol state restriction on a handle. -/
  | callerTypestate
  /-- C integer width / overflow bound. -/
  | cArithBound
  /-- Verification scope limitation: the C function accepts more, the proof covers less. -/
  | partialSpec
  deriving Repr, Inhabited, BEq

/-- Surface tag of a caveat kind (`API_RESTRICTION`, ...). -/
def CaveatKind.tag : CaveatKind → String
  | .apiRestriction => "API_RESTRICTION"
  | .callerTypestate => "CALLER_TYPESTATE"
  | .cArithBound => "C_ARITH_BOUND"
  | .partialSpec => "PARTIAL_SPEC"

/-- One tagged caveat: category, human explanation, and source text of the proposition. -/
structure CaveatClause where
  kind : CaveatKind
  desc : String
  prop : String
  deriving Repr, Inhabited

/-- Metadata of one typed parameter or return value (`mode` ∈ `Own`, `ShrRef`, `MutRef`,
    `UninitSlot`, `OutPtr`, `Val`; `ty` is the source text of the semantic type). -/
structure CParamInfo where
  name : String
  mode : String
  ty : String
  deriving Repr, Inhabited

/-- Structured metadata emitted by `c_type_spec f` as `f.cTypeInfo`. -/
structure CTypeSpecInfo where
  spec : String
  params : List CParamInfo
  ret : Option CParamInfo
  caveats : List CaveatClause
  env : List String
  untypedRequires : List String
  deriving Repr, Inhabited

/-! ## Value Types and Spatial Scalar Cells -/

/-- Unconstrained register scalar of C type `name` (empty spatial footprint; valid only with `Val`). -/
def scalarTy (w : Nat) (name : String) : SemType (BitVec w) :=
  { tyName := name, interp := fun _ _ => emp, pureWf := fun _ _ => True }

abbrev U8 : SemType (BitVec 8) := scalarTy 8 "uint8_t"
abbrev I8 : SemType (BitVec 8) := scalarTy 8 "int8_t"
abbrev U16 : SemType (BitVec 16) := scalarTy 16 "uint16_t"
abbrev I16 : SemType (BitVec 16) := scalarTy 16 "int16_t"
abbrev U32 : SemType (BitVec 32) := scalarTy 32 "uint32_t"
abbrev U64 : SemType (BitVec 64) := scalarTy 64 "uint64_t"
abbrev I32 : SemType (BitVec 32) := scalarTy 32 "int"
abbrev I64 : SemType (BitVec 64) := scalarTy 64 "int64_t"
abbrev SizeT : SemType (BitVec 64) := scalarTy 64 "size_t"
abbrev SSizeT : SemType (BitVec 64) := scalarTy 64 "ssize_t"
abbrev PtrdiffT : SemType (BitVec 64) := scalarTy 64 "ptrdiff_t"

/-- Spatial 1-byte scalar cell `p ↦₈ v` for pointer modes (`Own`, `ShrRef`, `MutRef`, `UninitSlot`, `OutPtr`). -/
def U8Cell : SemType (BitVec 8) :=
  { tyName := "uint8_t", interp := fun p v => p ↦₈ v, pureWf := fun _ _ => True }
def I8Cell : SemType (BitVec 8) :=
  { tyName := "int8_t", interp := fun p v => p ↦₈ v, pureWf := fun _ _ => True }

/-- Spatial 2-byte scalar cell `p ↦₁₆ v` for pointer modes (`Own`, `ShrRef`, `MutRef`, `UninitSlot`, `OutPtr`). -/
def U16Cell : SemType (BitVec 16) :=
  { tyName := "uint16_t", interp := fun p v => p ↦₁₆ v, pureWf := fun _ _ => True }
def I16Cell : SemType (BitVec 16) :=
  { tyName := "int16_t", interp := fun p v => p ↦₁₆ v, pureWf := fun _ _ => True }

/-- Spatial 4-byte scalar cell `p ↦₃₂ v` for pointer modes (`Own`, `ShrRef`, `MutRef`, `UninitSlot`, `OutPtr`). -/
def U32Cell : SemType (BitVec 32) :=
  { tyName := "uint32_t", interp := fun p v => p ↦₃₂ v, pureWf := fun _ _ => True }
def I32Cell : SemType (BitVec 32) :=
  { tyName := "int", interp := fun p v => p ↦₃₂ v, pureWf := fun _ _ => True }

/-- Spatial 8-byte scalar cell `p ↦₆₄ v` for pointer modes (`Own`, `ShrRef`, `MutRef`, `UninitSlot`, `OutPtr`). -/
def U64Cell : SemType (BitVec 64) :=
  { tyName := "uint64_t", interp := fun p v => p ↦₆₄ v, pureWf := fun _ _ => True }
def I64Cell : SemType (BitVec 64) :=
  { tyName := "int64_t", interp := fun p v => p ↦₆₄ v, pureWf := fun _ _ => True }
def SizeTCell : SemType (BitVec 64) :=
  { tyName := "size_t", interp := fun p v => p ↦₆₄ v, pureWf := fun _ _ => True }
def SSizeTCell : SemType (BitVec 64) :=
  { tyName := "ssize_t", interp := fun p v => p ↦₆₄ v, pureWf := fun _ _ => True }
def PtrdiffTCell : SemType (BitVec 64) :=
  { tyName := "ptrdiff_t", interp := fun p v => p ↦₆₄ v, pureWf := fun _ _ => True }

/-- Status/return code drawn from the listed values. -/
def StatusCode {w : Nat} (codes : List (BitVec w)) : SemType (BitVec w) :=
  { tyName := "status code", interp := fun _ _ => emp, pureWf := fun _ r => r ∈ codes }

/-- Length register coupled to a byte-slice model `bs`: `n.toNat = bs.length`. -/
def SliceLen {w : Nat} (bs : List (BitVec 8)) : SemType (BitVec w) :=
  { tyName := "size_t (slice length)", interp := fun _ _ => emp,
    pureWf := fun _ n => n.toNat = bs.length }

/-! ## Pointer, Buffer, and String Types -/

/-- Nullable pointer: `none` corresponds to `NULL`, `some m` to a `T` at a non-null address. -/
def OptOwn {M : Type} (T : SemType M) : SemType (Option M) :=
  { tyName := T.tyName ++ " (nullable)",
    interp := fun p om => match om with
      | none => ⌜p = 0#64⌝
      | some m => T.interp p m,
    pureWf := fun p om => match om with
      | none => True
      | some m => p ≠ 0#64 ∧ T.pureWf p m }

/-- Byte buffer `p ↦ₛ bs` (read-write points-to; pair with `SliceLen bs` for the length). -/
def Bytes : SemType (List (BitVec 8)) :=
  { tyName := "uint8_t[]", interp := fun p bs => p ↦ₛ bs, pureWf := fun _ _ => True }

/-- Shared byte slice (`const uint8_t *p` with `len`): use as `ShrRef ShrSlice8 bs`. -/
abbrev ShrSlice8 : SemType (List (BitVec 8)) := Bytes
/-- Mutable byte slice (`uint8_t *p` with `len`): use as `MutRef MutSlice8 bs ⇝ bs'`. -/
abbrev MutSlice8 : SemType (List (BitVec 8)) := Bytes

/-- NUL-terminated C string: `p ↦ₛ (bs ++ [0])` with no interior NUL. -/
def CStr : SemType (List (BitVec 8)) :=
  { tyName := "char * (NUL-terminated)", interp := fun p bs => p ↦ₛ (bs ++ [0#8]),
    pureWf := fun _ bs => 0#8 ∉ bs }

/-- Nullable C string. -/
abbrev OptCStr : SemType (Option (List (BitVec 8))) := OptOwn CStr

/-- Postcondition of an output pointer `T **out`: the slot now holds some `v` representing `m`. -/
def outPtrPost {M : Type} (T : SemType M) (p : BitVec 64) (m : M) : SepProp :=
  ∃∗ v : BitVec 64, ⌜T.pureWf v m⌝ ∗ (p ↦₆₄ v) ∗ T.interp v m

/-- Fallible output-pointer payload `OutPtrOnOk T ok`: behaves as `T` when `ok` holds, and has
    empty spatial footprint and trivial `pureWf` when `¬ ok`. Paired with `OutPtr`:
    `c_arg out : OutPtr (OutPtrOnOk T (ret = 0#32)) m` requires `memRegion out 8` and yields
    `outPtrPost T out m` on success (`ret = 0#32`) and `out ↦₆₄ v` on error. -/
def OutPtrOnOk {M : Type} (T : SemType M) (ok : Prop) [Decidable ok] : SemType M :=
  { tyName := T.tyName ++ " (on ok)",
    interp := fun v m => if ok then T.interp v m else emp,
    pureWf := fun v m => if ok then T.pureWf v m else True }

/-- Optional 8-byte output-pointer slot `OptOutPtr T`: `none` is an uninitialized 8-byte slot
    `memRegion p 8`; `some m` is an initialized output slot `outPtrPost T p m`. Pair with
    `MutRef (OptOutPtr T) none ⇝ (if ret = 0#32 then some m else none)` or `UninitSlot 8`. -/
def OptOutPtr {M : Type} (T : SemType M) : SemType (Option M) :=
  { tyName := T.tyName ++ " * (out-slot)",
    interp := fun p om => match om with
      | none => memRegion p 8
      | some m => outPtrPost T p m,
    pureWf := fun _ _ => True }

/-- Conditionally-owned pointer `CondOwn T`: `some m` holds full ownership `T.interp p m` with
    `T.pureWf p m`; `none` means ownership was consumed/transferred (`emp`, without constraining
    the register value `p`). Pair with `MutRef` for fallible ownership transfer or `realloc`-style
    consumption: `c_arg p : MutRef (CondOwn T) (some m) ⇝ (if ok then none else some m)`. -/
def CondOwn {M : Type} (T : SemType M) : SemType (Option M) :=
  { tyName := T.tyName ++ " (cond-own)",
    interp := fun p om => match om with
      | none => emp
      | some m => T.interp p m,
    pureWf := fun p om => match om with
      | none => True
      | some m => T.pureWf p m }

/-- Borrowed interior pointer `InteriorPtr tyName` whose spatial footprint remains inside a
    borrowed parent container: `interp` is `emp` and `pureWf p target` asserts `p = target`.
    Use with `c_ret : ShrRef (InteriorPtr "const T *") targetAddr` (or `MutRef`). -/
def InteriorPtr (tyName : String) : SemType (BitVec 64) :=
  { tyName := tyName, interp := fun _ _ => emp, pureWf := fun p target => p = target }

end

/-! ## The `c_type_spec` Command -/

meta section Macro

open Lean

/-- Clauses of a `c_type_spec` declaration. -/
declare_syntax_cat ctyClause
syntax "c_arg " ident " : " ident (term:max)* : ctyClause
syntax "c_arg " ident " : " ident (term:max)* " ⇝ " (term:max)+ : ctyClause
syntax "c_ret" " : " ident (term:max)* : ctyClause
syntax "caveat " "[" ident "] " str " : " term : ctyClause
syntax "c_env " term " ⇝ " term : ctyClause
syntax "c_env " term : ctyClause
syntax "c_exists " "(" ident+ " : " term ")" : ctyClause
syntax "c_stack " term:max : ctyClause
syntax specClause : ctyClause

private def stxText (s : Syntax) : String :=
  let raw := (s.reprint.getD (toString s)).toList
  let step := fun (acc : List Char × Bool) (c : Char) =>
    if c.isWhitespace then (acc.1, true)
    else if acc.2 && !acc.1.isEmpty then (c :: ' ' :: acc.1, false) else (c :: acc.1, false)
  String.ofList (raw.foldl step ([], false)).1.reverse

private def strLit (s : String) : Term := Syntax.mkStrLit s

private structure Lowered where
  preWf : Array Term := #[]
  pre : Array Term := #[]
  postWf : Array Term := #[]
  post : Array Term := #[]
  mode : String
  ty : String

/-- Reject value-only scalar `SemType`s (`U8`..`I64`, `SizeT`, `StatusCode`, `SliceLen`) in pointer
    ownership modes, since their spatial `interp` is `emp`. -/
private def checkNotValueOnlyScalarAux (mode : Ident) (T : Term) : Nat → MacroM Unit
  | 0 => pure ()
  | fuel + 1 => do
    let checkIdent (id : Ident) : MacroM Unit := do
      let base := id.getId.eraseMacroScopes.getString!
      match base with
      | "U8" | "I8" | "U16" | "I16" | "U32" | "I32" | "U64" | "I64"
      | "SizeT" | "SSizeT" | "PtrdiffT" =>
        Macro.throwErrorAt T
          s!"c_type_spec: value-only scalar type '{stxText T}' has an empty spatial footprint (`emp`) \
            and cannot be used with pointer mode '{mode.getId}'; use '{base}Cell' \
            (e.g. `U32Cell`, `U64Cell`, `SizeTCell`) for memory cells or `Val {stxText T}` for register values"
      | "scalarTy" | "StatusCode" | "SliceLen" =>
        Macro.throwErrorAt T
          s!"c_type_spec: value-only scalar type '{stxText T}' has an empty spatial footprint (`emp`) \
            and cannot be used with pointer mode '{mode.getId}'; use `Val {stxText T}` or a spatial `SemType`"
      | _ => pure ()
    match T with
    | `($id:ident) => checkIdent id
    | `(($inner:term)) => checkNotValueOnlyScalarAux mode inner fuel
    | `($fn:ident $args*) =>
      checkIdent fn
      let fnBase := fn.getId.eraseMacroScopes.getString!
      if fnBase ∈ ["OptOwn", "CondOwn", "OutPtrOnOk", "OptOutPtr"] && !args.isEmpty then
        let arg0 : Term := ⟨args[0]!.raw⟩
        checkNotValueOnlyScalarAux mode arg0 fuel
    | _ => pure ()

private def checkNotValueOnlyScalar (mode : Ident) (T : Term) : MacroM Unit :=
  checkNotValueOnlyScalarAux mode T 16

/-- Lower an ownership mode clause into pre/post well-formedness and spatial conditions. -/
private def lowerParam (x : Term) (mode : Ident) (args posts : Array Term) (isRet : Bool) :
    MacroM Lowered := do
  let m := mode.getId.toString
  let bad {α} : MacroM α := Macro.throwErrorAt mode
    s!"unsupported c_type_spec mode '{m}' with {args.size} argument(s) and {posts.size} post \
      argument(s); expected `Own T m`, `ShrRef T m`, `MutRef T m ⇝ m'`, \
      `UninitSlot n ⇝ T m'`, `OutPtr T m`, or `Val T`"
  if isRet then
    match m, args, posts with
    | "Own", #[T, mv], #[] =>
      checkNotValueOnlyScalar mode T
      return { postWf := #[← `(SemType.pureWf $T $x $mv)], post := #[← `(SemType.interp $T $x $mv)],
               mode := m, ty := stxText T }
    | "ShrRef", #[T, mv], #[]
    | "MutRef", #[T, mv], #[] =>
      checkNotValueOnlyScalar mode T
      return { postWf := #[← `(SemType.pureWf $T $x $mv)], mode := m, ty := stxText T }
    | "Val", #[T], #[] =>
      return { postWf := #[← `(SemType.valWf $T $x)], mode := m, ty := stxText T }
    | _, _, _ =>
      Macro.throwErrorAt mode
        s!"c_ret supports only `Own T m`, `ShrRef T m`, `MutRef T m`, and `Val T` (got '{m}')"
  match m, args, posts with
  | "Own", #[T, mv], #[] =>
    checkNotValueOnlyScalar mode T
    return { preWf := #[← `(SemType.pureWf $T $x $mv)], pre := #[← `(SemType.interp $T $x $mv)],
             mode := m, ty := stxText T }
  | "ShrRef", #[T, mv], #[] =>
    checkNotValueOnlyScalar mode T
    let sp ← `(SemType.interp $T $x $mv)
    return { preWf := #[← `(SemType.pureWf $T $x $mv)], pre := #[sp], post := #[sp],
             mode := m, ty := stxText T }
  | "MutRef", #[T, mv], #[mv'] =>
    checkNotValueOnlyScalar mode T
    return { preWf := #[← `(SemType.pureWf $T $x $mv)], pre := #[← `(SemType.interp $T $x $mv)],
             postWf := #[← `(SemType.pureWf $T $x $mv')],
             post := #[← `(SemType.interp $T $x $mv')], mode := m, ty := stxText T }
  | "UninitSlot", #[n], #[T, mv'] =>
    checkNotValueOnlyScalar mode T
    return { pre := #[← `(memRegion $x $n)], postWf := #[← `(SemType.pureWf $T $x $mv')],
             post := #[← `(SemType.interp $T $x $mv')], mode := m,
             ty := s!"{stxText n} bytes ⇝ {stxText T}" }
  | "OutPtr", #[T, mv], #[] =>
    checkNotValueOnlyScalar mode T
    return { pre := #[← `(memRegion $x 8)], post := #[← `(outPtrPost $T $x $mv)],
             mode := m, ty := stxText T }
  | "Val", #[T], #[] =>
    return { preWf := #[← `(SemType.valWf $T $x)], mode := m, ty := stxText T }
  | _, _, _ => bad

private def caveatKindOf (tag : Ident) : MacroM (Term × String) := do
  match tag.getId.toString with
  | "API_RESTRICTION" => return (← `(CaveatKind.apiRestriction), "API_RESTRICTION")
  | "CALLER_TYPESTATE" => return (← `(CaveatKind.callerTypestate), "CALLER_TYPESTATE")
  | "C_ARITH_BOUND" => return (← `(CaveatKind.cArithBound), "C_ARITH_BOUND")
  | "PARTIAL_SPEC" => return (← `(CaveatKind.partialSpec), "PARTIAL_SPEC")
  | t =>
    Macro.throwErrorAt tag s!"unknown caveat tag '{t}'; expected API_RESTRICTION, CALLER_TYPESTATE, C_ARITH_BOUND, or PARTIAL_SPEC"

/-- Names of register-bound (non-ghost, non-context) parameters in a `c_spec` header. -/
private def registerParamNames (bs : Array (TSyntax `abiParamBinder)) : Array Name := Id.run do
  let mut out := #[]
  for b in bs do
    match b with
    | `(abiParamBinder| ($tag:ident $[$xs:ident]* : $ty:term)) =>
      if !((tag.getId == `ctx || tag.getId == `context) && !xs.isEmpty) then
        let isBase := match ty with
          | `($t:ident) => t.getId == `base
          | _ => false
        if !isBase then
          for x in #[tag] ++ xs do out := out.push x.getId
    | `(abiParamBinder| ($x:ident : $_ty:term @ $_r:term)) => out := out.push x.getId
    | `(abiParamBinder| ($x:ident : $ty:term)) =>
      let skip := match ty with
        | `($t:ident) => t.getId == `base || t.getId == `sp
        | _ => false
      if !skip then out := out.push x.getId
    | _ => pure ()
  return out

private def mkSepConj (ps : Array Term) (sps : Array Term) : MacroM Term := do
  let mut atoms := sps
  if !ps.isEmpty then
    let mut p := ps.back!
    for q in (ps.pop).reverse do p ← `($q ∧ $p)
    atoms := #[← `(⌜$p⌝)] ++ atoms
  if atoms.isEmpty then return ← `(emp)
  let mut acc := atoms.back!
  for a in (atoms.pop).reverse do acc ← `($a ∗ $acc)
  return acc

/-- Expand a `c_type_spec` into a `c_spec` command plus a `<name>.cTypeInfo` metadata constant. -/
def expandCTypeSpec (isAbbrev : Bool) (doc? : Option (TSyntax `Lean.Parser.Command.docComment))
    (name : Ident) (bs : Array (TSyntax `abiParamBinder)) (ret? : Option (TSyntax `abiRetSpec))
    (cs : Array (TSyntax `ctyClause)) : MacroM Syntax := do
  let retId? : Option Ident ← match ret? with
    | some r => match r with
      | `(abiRetSpec| : ($rid:ident : $_t:term @ $_r:term)) => pure (some rid)
      | `(abiRetSpec| : ($rid:ident : $_t:term)) => pure (some rid)
      | _ => pure none
    | none => pure none
  let regNames := registerParamNames bs
  let mut typed : Array Name := #[]
  let mut lowered : Array Lowered := #[]
  let mut paramInfos : Array Term := #[]
  let mut retLowered? : Option Lowered := none
  let mut retInfo? : Option Term := none
  let mut caveatConds : Array Term := #[]
  let mut caveatInfos : Array Term := #[]
  let mut envInfos : Array Term := #[]
  let mut untypedInfos : Array Term := #[]
  let mut exists_ : Array (Ident × Term) := #[]
  let mut userEnsures : Array Term := #[]
  let mut userEnsuresPure : Array Term := #[]
  let mut passthrough : Array (TSyntax `specClause) := #[]
  let mut stackPre : Array Term := #[]
  let mut stackPost : Array Term := #[]
  let hasExists := cs.any fun c => match c with
    | `(ctyClause| c_exists ($_xs:ident* : $_ty:term)) => true
    | _ => false
  for c in cs do
    match c with
    | `(ctyClause| c_arg $x:ident : $mode:ident $args:term* ⇝ $posts:term*) =>
      if typed.contains x.getId then Macro.throwErrorAt x s!"duplicate c_arg for '{x.getId}'"
      typed := typed.push x.getId
      let l ← lowerParam x mode args posts false
      lowered := lowered.push l
      paramInfos := paramInfos.push (← `(CParamInfo.mk $(strLit x.getId.toString) $(strLit l.mode) $(strLit l.ty)))
    | `(ctyClause| c_arg $x:ident : $mode:ident $args:term*) =>
      if typed.contains x.getId then Macro.throwErrorAt x s!"duplicate c_arg for '{x.getId}'"
      typed := typed.push x.getId
      let l ← lowerParam x mode args #[] false
      lowered := lowered.push l
      paramInfos := paramInfos.push (← `(CParamInfo.mk $(strLit x.getId.toString) $(strLit l.mode) $(strLit l.ty)))
    | `(ctyClause| c_ret : $mode:ident $args:term*) =>
      let some rid := retId?
        | Macro.throwErrorAt c "c_ret requires a named return in the header, e.g. `: (ret : u64)`"
      if retLowered?.isSome then Macro.throwErrorAt c "duplicate c_ret clause"
      let l ← lowerParam rid mode args #[] true
      retLowered? := some l
      retInfo? := some (← `(CParamInfo.mk $(strLit rid.getId.toString) $(strLit l.mode) $(strLit l.ty)))
    | `(ctyClause| caveat [$tag:ident] $desc:str : $p:term) =>
      let (kind, _) ← caveatKindOf tag
      caveatConds := caveatConds.push p
      caveatInfos := caveatInfos.push (← `(CaveatClause.mk $kind $desc $(strLit (stxText p))))
    | `(ctyClause| c_env $r:term ⇝ $r':term) =>
      passthrough := passthrough.push (← `(specClause| requires $r))
      if !hasExists then passthrough := passthrough.push (← `(specClause| ensures $r'))
      else userEnsures := userEnsures.push r'
      envInfos := envInfos.push (strLit s!"{stxText r} ⇝ {stxText r'}")
    | `(ctyClause| c_env $r:term) =>
      passthrough := passthrough.push (← `(specClause| preserves $r))
      envInfos := envInfos.push (strLit (stxText r))
    | `(ctyClause| c_exists ($xs:ident* : $ty:term)) =>
      for x in xs do exists_ := exists_.push (x, ty)
    | `(ctyClause| c_stack $n:term) =>
      let s0sp := mkIdent `s0.sp
      let sfsp := mkIdent `sf.sp
      stackPre := stackPre.push (← `(stackFrameAt $s0sp $n))
      stackPost := stackPost.push (← `(stackFrameAt $sfsp $n))
      envInfos := envInfos.push (strLit s!"stack frame: {stxText n} bytes below sp")
    | `(ctyClause| $sc:specClause) =>
      match sc with
      | `(specClause| requires_cond $_) | `(specClause| requires_pure $_)
      | `(specClause| guard $_) =>
        Macro.throwErrorAt sc "c_type_spec: extra pure preconditions must be tagged \
          `caveat [API_RESTRICTION|CALLER_TYPESTATE|C_ARITH_BOUND|PARTIAL_SPEC] \"why\" : P`"
      | `(specClause| preserves $_) =>
        Macro.throwErrorAt sc "c_type_spec: use `c_arg x : ShrRef T m` for typed arguments or \
          `c_env R` for environment resources instead of `preserves`"
      | `(specClause| panics_when $_) | `(specClause| on_exit $_)
      | `(specClause| on_exit $_ => $_) =>
        Macro.throwErrorAt sc "c_type_spec: panics_when/on_exit clauses are not supported for C functions"
      | `(specClause| on_panic $r) =>
        caveatInfos := caveatInfos.push
          (← `(CaveatClause.mk CaveatKind.apiRestriction "non-local exit / panic path (on_panic)" $(strLit (stxText r))))
        passthrough := passthrough.push sc
      | `(specClause| requires $r) =>
        untypedInfos := untypedInfos.push (strLit (stxText r))
        passthrough := passthrough.push sc
      | `(specClause| ensures $r) =>
        if !hasExists then passthrough := passthrough.push sc
        else userEnsures := userEnsures.push r
      | `(specClause| ensures_pure $p) =>
        if !hasExists then passthrough := passthrough.push sc
        else userEnsuresPure := userEnsuresPure.push p
      | _ => passthrough := passthrough.push sc
    | _ => Macro.throwUnsupported
  for n in regNames do
    if !typed.contains n then
      Macro.throwErrorAt name s!"c_type_spec: register parameter '{n}' has no `c_arg {n} : <Mode> <Type> ...` clause"
  for n in typed do
    if !regNames.contains n then
      Macro.throwErrorAt name s!"c_type_spec: `c_arg {n}` does not name a register parameter of the header"
  let all := lowered ++ (retLowered?.map (#[·])).getD #[]
  let mut clauses : Array (TSyntax `specClause) := #[]
  for w in (lowered.flatMap (·.preWf)) ++ caveatConds do
    clauses := clauses.push (← `(specClause| requires_cond $w))
  for r in lowered.flatMap (·.pre) ++ stackPre do
    clauses := clauses.push (← `(specClause| requires $r))
  let postWf := all.flatMap (·.postWf)
  let postSp := all.flatMap (·.post)
  if !hasExists then
    for w in postWf do clauses := clauses.push (← `(specClause| ensures_pure $w))
    for r in postSp ++ stackPost do clauses := clauses.push (← `(specClause| ensures $r))
  else
    let mut body ← mkSepConj (postWf ++ userEnsuresPure) (postSp ++ userEnsures ++ stackPost)
    for (x, ty) in exists_.reverse do body ← `(∃∗ $x:ident : $ty, $body)
    clauses := clauses.push (← `(specClause| ensures $body))
  clauses := clauses ++ passthrough
  let specCmd ← expandSpecDecl isAbbrev doc? name bs ret? clauses
  let infoName := mkIdent (name.getId ++ `cTypeInfo)
  let retTerm ← match retInfo? with
    | some r => `(some $r)
    | none => `(none)
  let infoCmd ← `(command|
    /-- `c_type_spec` metadata (typed parameters and tagged caveats) for auditing tools. -/
    def $infoName : CTypeSpecInfo :=
      CTypeSpecInfo.mk $(strLit name.getId.toString) [$paramInfos,*] $retTerm
        [$caveatInfos,*] [$envInfos,*] [$untypedInfos,*])
  return mkNullNode #[specCmd, infoCmd]

/-- Semantic C type judgement that lowers to `c_spec` and `<name>.cTypeInfo`. -/
syntax (docComment)? ("abbrev ")? "c_type_spec " ident
    (abiParamBinder)* (abiRetSpec)? ("where")? (ctyClause)* : command

macro_rules
  | `($[$doc?:docComment]? c_type_spec $name:ident $[$bs:abiParamBinder]* $[$ret?:abiRetSpec]? $[where]? $[$cs:ctyClause]*) =>
    expandCTypeSpec false doc? name bs ret? cs
  | `($[$doc?:docComment]? abbrev c_type_spec $name:ident $[$bs:abiParamBinder]* $[$ret?:abiRetSpec]? $[where]? $[$cs:ctyClause]*) =>
    expandCTypeSpec true doc? name bs ret? cs

end Macro

end Arm64.CType
