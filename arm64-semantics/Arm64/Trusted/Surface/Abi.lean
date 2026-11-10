/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Lean
public import Arm64.Trusted.Spec.Hoare
public import Arm64.Trusted.Spec.RustAbi

/-!
# Declarative Function Specification DSL

Declarative `c_spec` and `rust_spec` commands that elaborate AAPCS64 and Rust ABI parameter
binders, return encoders (`RustAbi.*`, `decodeNiche64`), and separation-logic clauses into plain
`Spec α` (or `BaseSpec α`) definitions over register reads and `SepProp`.

## Examples
```lean
c_spec cSwapU64Spec (pa : ptr) (pb : ptr) (ghost va : u64) (ghost vb : u64)
  requires (pa ↦₆₄ va) ∗ (pb ↦₆₄ vb)
  ensures  (pa ↦₆₄ vb) ∗ (pb ↦₆₄ va)

c_spec hasNodeSpec (p : ptr) (ghost g : Graph) (n : usize) : bool64
  preserves graphAt p g
  returns   g.nodes n.toNat

rust_spec rustCheckedAddU64Spec (a : u64) (b : u64) : option_u64
  returns (if BitVec.ult (a + b) a then 0#32 else 1#32, a + b)

rust_spec rustCheckedAddU64OptSpec (a : u64) (b : u64) : RustAbi.optionU64
  returns if BitVec.ult (a + b) a then none else some (a + b)

abbrev c_spec rotateCtxSpec [a : RotateCtxArgs] (a.slotA : ptr) (a.slotB : ptr) (a.ctx : ptr) : u64
  requires (a.slotA ↦₆₄ a.vA) ∗ (a.slotB ↦₆₄ a.vB)
  stack32
  returns  rotateCtxDigest a.vA a.vB a.vAcc
  ensures  (a.slotA ↦₆₄ a.vB) ∗ (a.slotB ↦₆₄ a.vA)
```
-/

public section

namespace Arm64

/-- Decode a niche-optimized 64-bit value (`0` = `none`, non-zero `v` = `some v`). -/
@[expose] def decodeNiche64 (r : BitVec 64) : Option (BitVec 64) :=
  if r = 0#64 then none else some r

/-! ## Specification Macro DSL -/

meta section SpecDSL

open Lean

/-- Parameter binder in `c_spec` / `rust_spec`:
    - `{α : Type}` (implicit outer context parameter on the Lean `def` / `abbrev`)
    - `(ctx A : Allocator)` / `(context b fnMalloc : u64)` (explicit outer context parameters)
    - `[a : StructType]` (struct-backed `Spec StructType` binder)
    - `(x : u64)` / `(p : ptr)` / `(n : usize)` / `(x : u32)` / `(x : u16)` / `(x : u8)`
    - `(x : sret)` (binds `Reg.x8` without advancing `x0..x7`)
    - `(x : sp)` (binds `s0.sp` without advancing `x0..x7`)
    - `(p : slice8 bs)` / `(p : slice64 ws)` (fat pointer across 2 GP registers `(p, bs.length)`)
    - `(x : u64 @ .x1)` (explicit register binding without advancing `x0..x7`)
    - `(_ : u64 := expr)` / `(_ : u64 @ .x1 := expr)` (constant/expression register precondition without adding a ghost tuple element)
    - `(_ : u64)` (skips the next GP register `x0..x7` without adding a ghost tuple element or equality)
    - `(ghost g : Graph)` / `(ghost x y : u64)` (ghost parameters in the `Spec` tuple, not bound to registers)
    - `(load_addr base)` (binds the loaded image base address; same as the `load_addr base` clause) -/
declare_syntax_cat abiParamBinder
syntax "(" "load_addr " ident ")" : abiParamBinder
syntax "{" ident+ ":" term "}" : abiParamBinder
syntax "[" ident ":" term "]" : abiParamBinder
syntax "(" "ghost" ident+ ":" term ")" : abiParamBinder
syntax "(" ident ident+ ":" term ")" : abiParamBinder
syntax "(" "_" ":" term "@" term ":=" term ")" : abiParamBinder
syntax "(" "_" ":" term ":=" term ")" : abiParamBinder
syntax "(" "_" ":" term ")" : abiParamBinder
syntax "(" ident ":" term ("@" term)? ")" : abiParamBinder

/-- Return specification on a `c_spec` / `rust_spec` header (`: u64`, `: (ret : u64)`, `: bool64`,
    `: option_u64`, `: pair_u64`, `: u64 @ .x3`, `: (ret : u32 @ .x0)`, etc.). -/
declare_syntax_cat abiRetSpec
syntax ":" "(" ident ":" term ("@" term)? ")" : abiRetSpec
syntax ":" term ("@" term)? : abiRetSpec

/-- Clause in a `c_spec` or `rust_spec` body.

    `load_addr b` binds `b : BitVec 64` to the load (base) address of the ELF image containing the
    function. It is emitted as the final curried parameter of the generated `def` (after every
    `(ctx ...)` parameter), so after applying the `ctx` arguments the spec has type
    `BaseSpec α = BitVec 64 → Spec α`, and `Program.subroutineOk` / `Obj.PlacedLib.subroutineOk` /
    `Spec.liftedSubroutineHook` instantiate `b` with the program's base via `ToBaseSpec`. -/
declare_syntax_cat specClause
syntax "load_addr " ident : specClause
syntax "guard " term : specClause
syntax "requires_pure " term : specClause
syntax "requires_cond " term : specClause
syntax "requires " term : specClause
syntax "preserves " term : specClause
syntax "ensures " term : specClause
syntax "ensures_pure " term : specClause
syntax "returns " term : specClause
syntax "stack " term : specClause
syntax "stack16" : specClause
syntax "stack32" : specClause
syntax "let " ident (" : " term)? " := " term : specClause
syntax "panics_when " term : specClause
syntax "on_panic " term : specClause
syntax "on_exit " ident " => " term : specClause
syntax "on_exit " term : specClause
syntax "oom_when " term : specClause
syntax "on_oom " term : specClause

private def gpRegDotTerm (idx : Nat) : MacroM Term := do
  match idx with
  | 0 => `(.x0)
  | 1 => `(.x1)
  | 2 => `(.x2)
  | 3 => `(.x3)
  | 4 => `(.x4)
  | 5 => `(.x5)
  | 6 => `(.x6)
  | 7 => `(.x7)
  | _ => Macro.throwError s!"ABI argument index {idx} exceeds register arguments x0..x7"

private def resolveAbiLeanType (ty : Term) : MacroM Term := do
  match ty with
  | `($id:ident) =>
    match id.getId.toString with
    | "u64" | "i64" | "usize" | "isize" | "ptr" | "sret" | "sp" => `(BitVec 64)
    | "u32" | "i32" => `(BitVec 32)
    | "u16" | "i16" => `(BitVec 16)
    | "u8"  | "i8"  => `(BitVec 8)
    | "bool" | "bool32" | "rust_bool" | "bool64" => `(Bool)
    | "slice8" | "slice64" => `(BitVec 64 × BitVec 64)
    | _ => pure ty
  | `($fn:ident $_arg:term) =>
    match fn.getId.toString with
    | "slice8" | "slice64" | "slice_ptr" => `(BitVec 64)
    | _ => pure ty
  | _ => pure ty

private def expandAbiParam (s0 : Ident) (x : Term) (ty : Term) (regOverride? : Option Term)
    (regIdx : Nat) : MacroM (Option Term × Array Term × Nat) := do
  let getReg : MacroM (Term × Nat) := do
    match regOverride? with
    | some r => pure (r, regIdx)
    | none =>
      let r ← gpRegDotTerm regIdx
      pure (r, regIdx + 1)
  match ty with
  | `($id:ident) =>
    match id.getId.toString with
    | "u64" | "i64" | "usize" | "isize" | "ptr" =>
      let (r, nextIdx) ← getReg
      let eq ← `(State.readReg64 $s0 $r = $x)
      return (some (← `(BitVec 64)), #[eq], nextIdx)
    | "u32" | "i32" =>
      let (r, nextIdx) ← getReg
      let eq ← `(State.readReg32 $s0 $r = $x)
      return (some (← `(BitVec 32)), #[eq], nextIdx)
    | "u16" | "i16" =>
      let (r, nextIdx) ← getReg
      let eq ← `((State.readReg32 $s0 $r).truncate 16 = $x)
      return (some (← `(BitVec 16)), #[eq], nextIdx)
    | "u8" | "i8" =>
      let (r, nextIdx) ← getReg
      let eq ← `((State.readReg32 $s0 $r).truncate 8 = $x)
      return (some (← `(BitVec 8)), #[eq], nextIdx)
    | "bool" =>
      -- AAPCS64 (`ARM IHI 0055`, section 5.1 Table 1, section 6.8.2 Rule C.14/C.15): C `_Bool` /
      -- C++ `bool` is a 1-byte unsigned integer (`0` = `false`, `1` = `true`) in `W[7:0]`, and
      -- upper bits `[63:8]` (`W[31:8]`) are unspecified at the ABI boundary. Clang and GCC on
      -- `aarch64-linux-gnu` lower `_Bool` parameters to LLVM `i1` without `zeroext`, so
      -- conforming callers need only set `W[7:0] ∈ {0, 1}` and callees mask/test the low byte.
      let (r, nextIdx) ← getReg
      let eq ← `((State.readReg32 $s0 $r).truncate 8 = if $x then 1#8 else 0#8)
      return (some (← `(Bool)), #[eq], nextIdx)
    | "bool32" | "rust_bool" =>
      -- 32-bit zero-extended boolean (`W ∈ {0, 1}`). `rust_bool` is an alias for `bool32`
      -- matching `rustc`'s `i1 noundef zeroext` ABI on `aarch64-unknown-linux-gnu` (`rust-lang/rust#97712`).
      let (r, nextIdx) ← getReg
      let eq ← `(State.readReg32 $s0 $r = if $x then 1#32 else 0#32)
      return (some (← `(Bool)), #[eq], nextIdx)
    | "bool64" =>
      let (r, nextIdx) ← getReg
      let eq ← `(State.readReg64 $s0 $r = if $x then 1 else 0)
      return (some (← `(Bool)), #[eq], nextIdx)
    | "sret" =>
      let r ← match regOverride? with | some r => pure r | none => `(.x8)
      let eq ← `(State.readReg64 $s0 $r = $x)
      return (some (← `(BitVec 64)), #[eq], regIdx)
    | "sp" =>
      if regOverride?.isSome then
        Macro.throwError "Explicit register override is not supported for 'sp' binders"
      let eq ← `(State.sp $s0 = $x)
      return (some (← `(BitVec 64)), #[eq], regIdx)
    | "slice8" | "slice64" =>
      if regOverride?.isSome then
        Macro.throwError s!"Explicit register override is not supported for fat-pointer slice binders '{ty}'"
      let r0 ← gpRegDotTerm regIdx
      let r1 ← gpRegDotTerm (regIdx + 1)
      let eq0 ← `(State.readReg64 $s0 $r0 = ($x).1)
      let eq1 ← `(State.readReg64 $s0 $r1 = ($x).2)
      return (some (← `(BitVec 64 × BitVec 64)), #[eq0, eq1], regIdx + 2)
    | other =>
      Macro.throwErrorAt id
        s!"unknown ABI parameter type '{other}'; expected u8, i8, u16, i16, u32, i32, u64, i64, \
          usize, isize, ptr, bool, rust_bool, bool32, bool64, sret, sp, slice8, or slice64 \
          (use `(ghost {x.raw.reprint.getD "x"} : {other})` for ghost parameters)"
  | `($fn:ident $listArg:term) =>
    match fn.getId.toString with
    | "slice8" | "slice64" | "slice_ptr" =>
      if regOverride?.isSome then
        Macro.throwError s!"Explicit register override is not supported for fat-pointer slice binders '{ty}'"
      let r0 ← gpRegDotTerm regIdx
      let r1 ← gpRegDotTerm (regIdx + 1)
      let eq0 ← `(State.readReg64 $s0 $r0 = $x)
      let eq1 ← `(State.readReg64 $s0 $r1 = BitVec.ofNat 64 ($listArg).length)
      return (some (← `(BitVec 64)), #[eq0, eq1], regIdx + 2)
    | _ =>
      let (r, nextIdx) ← getReg
      let eq ← `(State.readReg64 $s0 $r = $x)
      return (some ty, #[eq], nextIdx)
  | _ =>
    let (r, nextIdx) ← getReg
    let eq ← `(State.readReg64 $s0 $r = $x)
    return (some ty, #[eq], nextIdx)

private def expandAbiReturn (sf : Ident) (retSpec? : Option (Term × Option Term))
    (retExpr : Term) : MacroM (Array Term) := do
  let (retTy, regOverride?) ← match retSpec? with
    | some p => pure p
    | none => pure (← `(u64), none)
  let r ← match regOverride? with
    | some reg => pure reg
    | none => `(.x0)
  match retTy with
  | `($id:ident) =>
    -- Typed Rust `Option`/`Result` encoders (`Arm64.Trusted.Spec.RustAbi`): `: RustAbi.optionU64`
    -- + `returns e` means `RustAbi.optionU64.holds sf e`. The encoder fixes the registers.
    if id.getId.getRoot == `RustAbi then
      if let some reg := regOverride? then
        Macro.throwError s!"Explicit register override '@ {reg}' is not supported for Rust ABI return encoder '{retTy}'"
      let enc := mkIdentFrom id (`Arm64 ++ id.getId)
      return #[← `(Arm64.RustAbi.RetEnc.holds $enc $sf $retExpr)]
    match id.getId.toString with
    | "u64" | "i64" | "usize" | "isize" | "ptr" | "void" | "unit" =>
      return #[← `(State.readReg64 $sf $r = $retExpr)]
    | "u32" | "i32" =>
      return #[← `(State.readReg32 $sf $r = $retExpr)]
    | "u16" | "i16" =>
      return #[← `((State.readReg32 $sf $r).truncate 16 = $retExpr)]
    | "u8" | "i8" =>
      return #[← `((State.readReg32 $sf $r).truncate 8 = $retExpr)]
    | "bool" =>
      -- AAPCS64 (`ARM IHI 0055`, section 5.1 Table 1, section 6.9): a `_Bool` result is returned
      -- like a first named `_Bool` argument, with `0` or `1` in `W[7:0]` and `[63:8]` unspecified.
      return #[← `((State.readReg32 $sf $r).truncate 8 = if $retExpr then 1#8 else 0#8)]
    | "bool32" | "rust_bool" =>
      return #[← `(State.readReg32 $sf $r = if $retExpr then 1#32 else 0#32)]
    | "bool64" =>
      return #[← `(State.readReg64 $sf $r = if $retExpr then 1 else 0)]
    | "pair_u64" | "result_u64" =>
      if let some reg := regOverride? then
        Macro.throwError s!"Explicit register override '@ {reg}' is not supported for multi-register return type '{retTy}'"
      match retExpr with
      | `(($a, $b)) =>
        return #[← `(State.readReg64 $sf .x0 = $a), ← `(State.readReg64 $sf .x1 = $b)]
      | _ =>
        return #[← `(State.readReg64 $sf .x0 = ($retExpr).1), ← `(State.readReg64 $sf .x1 = ($retExpr).2)]
    | "option_u64" =>
      if let some reg := regOverride? then
        Macro.throwError s!"Explicit register override '@ {reg}' is not supported for multi-register return type '{retTy}'"
      match retExpr with
      | `(($disc, $payload)) =>
        return #[← `(State.readReg32 $sf .x0 = $disc), ← `(State.readReg64 $sf .x1 = $payload)]
      | _ =>
        return #[← `(State.readReg32 $sf .x0 = ($retExpr).1), ← `(State.readReg64 $sf .x1 = ($retExpr).2)]
    | "option_u8" =>
      if let some reg := regOverride? then
        Macro.throwError s!"Explicit register override '@ {reg}' is not supported for multi-register return type '{retTy}'"
      match retExpr with
      | `(($disc, $payload)) =>
        return #[← `(State.readReg32 $sf .x0 = $disc), ← `((State.readReg32 $sf .x1).truncate 8 = $payload)]
      | _ =>
        return #[← `(State.readReg32 $sf .x0 = ($retExpr).1),
                 ← `((State.readReg32 $sf .x1).truncate 8 = ($retExpr).2)]
    | "niche_u64" =>
      return #[← `(Arm64.decodeNiche64 (State.readReg64 $sf $r) = $retExpr)]
    | other =>
      Macro.throwErrorAt id
        s!"unknown ABI return type '{other}'; expected u8, i8, u16, i16, u32, i32, u64, i64, \
          usize, isize, ptr, bool, rust_bool, bool32, bool64, pair_u64, result_u64, option_u64, option_u8, niche_u64, or a `RustAbi.*` encoder"
  | _ =>
    return #[← `(State.readReg64 $sf $r = $retExpr)]

private def expandAbiReturnAccess (sf : Ident) (retTy : Term) (regOverride? : Option Term) :
    MacroM (Term × Array Term) := do
  let r ← match regOverride? with
    | some reg => pure reg
    | none => `(.x0)
  match retTy with
  | `($id:ident) =>
    if id.getId.getRoot == `RustAbi then
      Macro.throwErrorAt id
        s!"Rust ABI return encoder '{id.getId}' cannot be used with a named return binder; \
          use an unnamed return type with `returns <Option/Except value>`"
    match id.getId.toString with
    | "u64" | "i64" | "usize" | "isize" | "ptr" | "void" | "unit" =>
      return (← `(State.readReg64 $sf $r), #[])
    | "u32" | "i32" =>
      return (← `(State.readReg32 $sf $r), #[])
    | "u16" | "i16" =>
      return (← `((State.readReg32 $sf $r).truncate 16), #[])
    | "u8"  | "i8"  =>
      return (← `((State.readReg32 $sf $r).truncate 8), #[])
    | "bool" =>
      -- Enforce canonical {0, 1} register slices so non-canonical values (e.g. W0 = 2) are rejected.
      let access ← `((State.readReg32 $sf $r).truncate 8 != 0#8)
      let canon ← `((State.readReg32 $sf $r).truncate 8 = if $access then 1#8 else 0#8)
      return (access, #[canon])
    | "bool32" | "rust_bool" =>
      let access ← `((State.readReg32 $sf $r) != 0#32)
      let canon ← `(State.readReg32 $sf $r = if $access then 1#32 else 0#32)
      return (access, #[canon])
    | "bool64" =>
      let access ← `((State.readReg64 $sf $r) != 0#64)
      let canon ← `(State.readReg64 $sf $r = if $access then 1 else 0)
      return (access, #[canon])
    | "niche_u64" =>
      return (← `(Arm64.decodeNiche64 (State.readReg64 $sf $r)), #[])
    | "pair_u64" | "result_u64" =>
      return (← `((State.readReg64 $sf .x0, State.readReg64 $sf .x1)), #[])
    | "option_u64" =>
      return (← `((State.readReg32 $sf .x0, State.readReg64 $sf .x1)), #[])
    | "option_u8" =>
      return (← `((State.readReg32 $sf .x0, (State.readReg32 $sf .x1).truncate 8)), #[])
    | other =>
      Macro.throwErrorAt id
        s!"unknown ABI return type '{other}'; expected u8, i8, u16, i16, u32, i32, u64, i64, \
          usize, isize, ptr, bool, rust_bool, bool32, bool64, pair_u64, result_u64, option_u64, option_u8, or niche_u64"
  | _ => return (← `(State.readReg64 $sf $r), #[])

private def replaceIdentInStx (target : Name) (replacement : Syntax) : Nat → Syntax → Syntax
  | 0, stx => stx
  | _ + 1, stx@(Syntax.ident info rawVal val preresolved) =>
    if val == target then
      replacement
    else if val.getRoot == target then
      match replacement with
      | Syntax.ident _ _ repName _ =>
        let view := extractMacroScopes repName
        Syntax.ident info rawVal ({ view with name := val.replacePrefix target view.name }.review) preresolved
      | _ =>
        match val with
        | Name.str p field =>
          if p == target then
            Syntax.node info ``Lean.Parser.Term.proj
              #[replacement, mkAtom ".", mkIdent (Name.mkSimple field)]
          else stx
        | _ => stx
    else
      stx
  | fuel + 1, Syntax.node info kind args =>
    if kind == ``Lean.Parser.Term.proj && args.size ≥ 3 then
      Syntax.node info kind (args.set! 0 (replaceIdentInStx target replacement fuel args[0]!))
    else
      Syntax.node info kind (args.map (replaceIdentInStx target replacement fuel))
  | _ + 1, stx => stx

private def replaceIdentInTerm (target : Name) (replacement : Term) (t : Term) : Term :=
  ⟨replaceIdentInStx target replacement.raw 64 t.raw⟩

private def collectSepConjAtoms : Nat → Term → Array Term
  | 0, t => #[t]
  | fuel + 1, t =>
    match t with
    | `($a ∗ $b) => collectSepConjAtoms fuel a ++ collectSepConjAtoms fuel b
    | _ => #[t]

private def collectAndAtoms : Nat → Term → Array Term
  | 0, t => #[t]
  | fuel + 1, t =>
    match t with
    | `($a ∧ $b) => collectAndAtoms fuel a ++ collectAndAtoms fuel b
    | _ => #[t]

private def foldSepConjRight (ts : Array Term) : MacroM Term := do
  match ts.toList.reverse with
  | [] => `(emp)
  | last :: revInit =>
    revInit.foldlM (fun acc t => `($t ∗ $acc)) last

private def foldAndRight (ts : Array Term) : MacroM (Option Term) := do
  match ts.toList.reverse with
  | [] => pure none
  | last :: revInit =>
    let conj ← revInit.foldlM (fun acc t => `($t ∧ $acc)) last
    pure (some conj)

private def mkSepBody (pureTerms : Array Term) (spatialTerms : Array Term) : MacroM Term := do
  let pureOpt ← foldAndRight pureTerms
  match pureOpt with
  | some p =>
    let pureSep ← `(⌜$p⌝)
    if spatialTerms.isEmpty then
      pure pureSep
    else
      foldSepConjRight (#[pureSep] ++ spatialTerms)
  | none =>
    if spatialTerms.isEmpty then
      `(emp)
    else
      foldSepConjRight spatialTerms

private def stxMentionsIdent (stx : Syntax) (id : Ident) : Bool :=
  (stx.find? fun s => s.isIdent && (s.getId == id.getId || s.getId.getRoot == id.getId)).isSome

private def stxMentionsFreeIdent (target : Name) : Nat → Syntax → Bool
  | 0, _ => false
  | _ + 1, Syntax.ident _ _ val _ =>
    val == target || val.getRoot == target
  | fuel + 1, Syntax.node _ kind args =>
    if kind == ``Lean.Parser.Term.proj && args.size ≥ 3 then
      stxMentionsFreeIdent target fuel args[0]!
    else if kind == ``Lean.Parser.Term.structInstField && args.size ≥ 1 then
      let hasAssign := ((Syntax.node .none kind args).find? fun s => s.isAtom && s.getAtomVal == ":=").isSome
      if hasAssign then
        (args.extract 1 args.size).any (stxMentionsFreeIdent target fuel)
      else
        args.any (stxMentionsFreeIdent target fuel)
    else
      args.any (stxMentionsFreeIdent target fuel)
  | _ + 1, _ => false

private def wrapUsedLets (lets : Array (Ident × Option Term × Term)) (body : Term) : MacroM Term := do
  lets.toList.reverse.foldlM (fun acc (id, ty?, val) => do
    if stxMentionsIdent acc.raw id then
      match ty? with
      | some ty => `(let $id : $ty := $val; $acc)
      | none    => `(let $id := $val; $acc)
    else
      pure acc
  ) body

private def parseRetSpec? (retOpt? : Option (TSyntax `abiRetSpec)) :
    MacroM (Option (Option Ident × Term × Option Term)) := do
  match retOpt? with
  | none => pure none
  | some retStx =>
    match retStx with
    | `(abiRetSpec| : ($retId:ident : $ty:term @ $reg:term)) => pure (some (some retId, ty, some reg))
    | `(abiRetSpec| : ($retId:ident : $ty:term)) => pure (some (some retId, ty, none))
    | `(abiRetSpec| : $ty:term @ $reg:term) => pure (some (none, ty, some reg))
    | `(abiRetSpec| : $ty:term) => pure (some (none, ty, none))
    | _ => Macro.throwUnsupported

private def expandSpecClauses (s0 sf : Ident) (regEqs : Array Term)
    (retSpec? : Option (Option Ident × Term × Option Term))
    (clauses : Array (TSyntax `specClause)) :
    MacroM (Term × Term × Option Term × Option (Ident × Term) × Option Term) := do
  let retTypeAndReg? := retSpec?.map fun (_, ty, r?) => (ty, r?)
  let mut preGuards : Array Term := #[]
  let mut preConds : Array Term := #[]
  let mut preSpatial : Array Term := #[]
  let mut postPure : Array Term := #[]
  let mut postSpatial : Array Term := #[]
  let mut specLets : Array (Ident × Option Term × Term) := #[]
  let mut onPanic? : Option Term := none
  let mut onExit? : Option (Ident × Term) := none
  let mut onOom? : Option Term := none
  for c in clauses do
    match c with
    | `(specClause| load_addr $_:ident) => pure ()
    | `(specClause| guard $p:term) =>
      preGuards := preGuards ++ collectAndAtoms 32 p
    | `(specClause| requires_pure $p:term) =>
      preGuards := preGuards ++ collectAndAtoms 32 p
    | `(specClause| requires_cond $p:term) =>
      preConds := preConds ++ collectAndAtoms 32 p
    | `(specClause| requires $sp:term) =>
      preSpatial := preSpatial ++ collectSepConjAtoms 32 sp
    | `(specClause| preserves $sp:term) =>
      let atoms := collectSepConjAtoms 32 sp
      preSpatial := preSpatial ++ atoms
      postSpatial := postSpatial ++ atoms
    | `(specClause| ensures $sp:term) =>
      postSpatial := postSpatial ++ collectSepConjAtoms 32 sp
    | `(specClause| ensures_pure $p:term) =>
      postPure := postPure ++ collectAndAtoms 32 p
    | `(specClause| returns $r:term) =>
      let rEqs ← expandAbiReturn sf retTypeAndReg? r
      postPure := postPure ++ rEqs
    | `(specClause| stack $len:term) =>
      preSpatial := preSpatial.push (← `(stackFrame $s0 $len))
      postSpatial := postSpatial.push (← `(stackFrame $sf $len))
    | `(specClause| stack16) =>
      preSpatial := preSpatial.push (← `(stackFrame16 $s0))
      postSpatial := postSpatial.push (← `(stackFrame16 $sf))
    | `(specClause| stack32) =>
      preSpatial := preSpatial.push (← `(stackFrame32 $s0))
      postSpatial := postSpatial.push (← `(stackFrame32 $sf))
    | `(specClause| let $id:ident : $ty:term := $val:term) =>
      specLets := specLets.push (id, some ty, val)
    | `(specClause| let $id:ident := $val:term) =>
      specLets := specLets.push (id, none, val)
    | `(specClause| panics_when $p:term) =>
      if onPanic?.isSome then
        Macro.throwError "duplicate 'panics_when' or 'on_panic' clause"
      onPanic? := some (← `(⌜$p⌝))
    | `(specClause| on_panic $sp:term) =>
      if onPanic?.isSome then
        Macro.throwError "duplicate 'panics_when' or 'on_panic' clause"
      onPanic? := some sp
    | `(specClause| on_exit $codeId:ident => $sp:term) =>
      if onExit?.isSome then
        Macro.throwError "duplicate 'on_exit' clause"
      onExit? := some (codeId, sp)
    | `(specClause| on_exit $sp:term) =>
      if onExit?.isSome then
        Macro.throwError "duplicate 'on_exit' clause"
      onExit? := some (mkIdent `_, sp)
    | `(specClause| oom_when $p:term) =>
      if onOom?.isSome then
        Macro.throwError "duplicate 'oom_when' or 'on_oom' clause"
      onOom? := some (← `(⌜$p⌝))
    | `(specClause| on_oom $sp:term) =>
      if onOom?.isSome then
        Macro.throwError "duplicate 'oom_when' or 'on_oom' clause"
      onOom? := some sp
    | _ => Macro.throwUnsupported
  let prePure := preGuards ++ regEqs ++ preConds
  let preInner ← mkSepBody prePure preSpatial
  let preBody ← wrapUsedLets specLets preInner
  let (retAccess?, retCanon) ← match retSpec? with
    | some (some retId, retTy, regOverride?) =>
      let (retAccess, canon) ← expandAbiReturnAccess sf retTy regOverride?
      pure (some (retId, retAccess), canon)
    | _ => pure (none, #[])
  postPure := retCanon ++ postPure
  let postInner ← mkSepBody postPure postSpatial
  let postWithLets ← wrapUsedLets specLets postInner
  let postBody := match retAccess? with
    | some (retId, retAccess) => replaceIdentInTerm retId.getId retAccess postWithLets
    | none => postWithLets
  let onPanicBody? ← match onPanic? with
    | some p => some <$> wrapUsedLets specLets p
    | none   => pure none
  let onExitBody? ← match onExit? with
    | some (cId, eBody) =>
      let wrapped ← wrapUsedLets specLets eBody
      pure (some (cId, wrapped))
    | none => pure none
  let onOomBody? ← match onOom? with
    | some o => some <$> wrapUsedLets specLets o
    | none   => pure none
  return (preBody, postBody, onPanicBody?, onExitBody?, onOomBody?)

private def mkSpecDeclCmd (isAbbrev : Bool) (doc? : Option (TSyntax `Lean.Parser.Command.docComment))
    (name : Ident) (ctxBinders : Array (TSyntax ``Lean.Parser.Term.bracketedBinder))
    (specType : Term) (binderPat : Term) (s0 sf : Ident)
    (preBody postBody : Term) (onPanic? : Option Term)
    (onExit? : Option (Ident × Term)) (onOom? : Option Term) : MacroM Command := do
  match isAbbrev, onPanic?, onExit?, onOom? with
  | false, none, none, none =>
    `($[$doc?:docComment]?
      def $name $[$ctxBinders:bracketedBinder]* : Spec ($specType) where
        pre  := fun $binderPat $s0 => $preBody
        post := fun $binderPat $s0 $sf => $postBody)
  | false, some panicBody, none, none =>
    `($[$doc?:docComment]?
      def $name $[$ctxBinders:bracketedBinder]* : Spec ($specType) where
        pre     := fun $binderPat $s0 => $preBody
        post    := fun $binderPat $s0 $sf => $postBody
        onPanic := fun $binderPat $s0 $sf => $panicBody)
  | false, none, some (exitId, exitBody), none =>
    `($[$doc?:docComment]?
      def $name $[$ctxBinders:bracketedBinder]* : Spec ($specType) where
        pre    := fun $binderPat $s0 => $preBody
        post   := fun $binderPat $s0 $sf => $postBody
        onExit := fun $binderPat $exitId $s0 $sf => $exitBody)
  | false, some panicBody, some (exitId, exitBody), none =>
    `($[$doc?:docComment]?
      def $name $[$ctxBinders:bracketedBinder]* : Spec ($specType) where
        pre     := fun $binderPat $s0 => $preBody
        post    := fun $binderPat $s0 $sf => $postBody
        onPanic := fun $binderPat $s0 $sf => $panicBody
        onExit  := fun $binderPat $exitId $s0 $sf => $exitBody)
  | false, none, none, some oomBody =>
    `($[$doc?:docComment]?
      def $name $[$ctxBinders:bracketedBinder]* : Spec ($specType) where
        pre   := fun $binderPat $s0 => $preBody
        post  := fun $binderPat $s0 $sf => $postBody
        onOom := fun $binderPat $s0 $sf => $oomBody)
  | false, some panicBody, none, some oomBody =>
    `($[$doc?:docComment]?
      def $name $[$ctxBinders:bracketedBinder]* : Spec ($specType) where
        pre     := fun $binderPat $s0 => $preBody
        post    := fun $binderPat $s0 $sf => $postBody
        onPanic := fun $binderPat $s0 $sf => $panicBody
        onOom   := fun $binderPat $s0 $sf => $oomBody)
  | false, none, some (exitId, exitBody), some oomBody =>
    `($[$doc?:docComment]?
      def $name $[$ctxBinders:bracketedBinder]* : Spec ($specType) where
        pre    := fun $binderPat $s0 => $preBody
        post   := fun $binderPat $s0 $sf => $postBody
        onExit := fun $binderPat $exitId $s0 $sf => $exitBody
        onOom  := fun $binderPat $s0 $sf => $oomBody)
  | false, some panicBody, some (exitId, exitBody), some oomBody =>
    `($[$doc?:docComment]?
      def $name $[$ctxBinders:bracketedBinder]* : Spec ($specType) where
        pre     := fun $binderPat $s0 => $preBody
        post    := fun $binderPat $s0 $sf => $postBody
        onPanic := fun $binderPat $s0 $sf => $panicBody
        onExit  := fun $binderPat $exitId $s0 $sf => $exitBody
        onOom   := fun $binderPat $s0 $sf => $oomBody)
  | true, none, none, none =>
    `($[$doc?:docComment]?
      abbrev $name $[$ctxBinders:bracketedBinder]* : Spec ($specType) where
        pre  := fun $binderPat $s0 => $preBody
        post := fun $binderPat $s0 $sf => $postBody)
  | true, some panicBody, none, none =>
    `($[$doc?:docComment]?
      abbrev $name $[$ctxBinders:bracketedBinder]* : Spec ($specType) where
        pre     := fun $binderPat $s0 => $preBody
        post    := fun $binderPat $s0 $sf => $postBody
        onPanic := fun $binderPat $s0 $sf => $panicBody)
  | true, none, some (exitId, exitBody), none =>
    `($[$doc?:docComment]?
      abbrev $name $[$ctxBinders:bracketedBinder]* : Spec ($specType) where
        pre    := fun $binderPat $s0 => $preBody
        post   := fun $binderPat $s0 $sf => $postBody
        onExit := fun $binderPat $exitId $s0 $sf => $exitBody)
  | true, some panicBody, some (exitId, exitBody), none =>
    `($[$doc?:docComment]?
      abbrev $name $[$ctxBinders:bracketedBinder]* : Spec ($specType) where
        pre     := fun $binderPat $s0 => $preBody
        post    := fun $binderPat $s0 $sf => $postBody
        onPanic := fun $binderPat $s0 $sf => $panicBody
        onExit  := fun $binderPat $exitId $s0 $sf => $exitBody)
  | true, none, none, some oomBody =>
    `($[$doc?:docComment]?
      abbrev $name $[$ctxBinders:bracketedBinder]* : Spec ($specType) where
        pre   := fun $binderPat $s0 => $preBody
        post  := fun $binderPat $s0 $sf => $postBody
        onOom := fun $binderPat $s0 $sf => $oomBody)
  | true, some panicBody, none, some oomBody =>
    `($[$doc?:docComment]?
      abbrev $name $[$ctxBinders:bracketedBinder]* : Spec ($specType) where
        pre     := fun $binderPat $s0 => $preBody
        post    := fun $binderPat $s0 $sf => $postBody
        onPanic := fun $binderPat $s0 $sf => $panicBody
        onOom   := fun $binderPat $s0 $sf => $oomBody)
  | true, none, some (exitId, exitBody), some oomBody =>
    `($[$doc?:docComment]?
      abbrev $name $[$ctxBinders:bracketedBinder]* : Spec ($specType) where
        pre    := fun $binderPat $s0 => $preBody
        post   := fun $binderPat $s0 $sf => $postBody
        onExit := fun $binderPat $exitId $s0 $sf => $exitBody
        onOom  := fun $binderPat $s0 $sf => $oomBody)
  | true, some panicBody, some (exitId, exitBody), some oomBody =>
    `($[$doc?:docComment]?
      abbrev $name $[$ctxBinders:bracketedBinder]* : Spec ($specType) where
        pre     := fun $binderPat $s0 => $preBody
        post    := fun $binderPat $s0 $sf => $postBody
        onPanic := fun $binderPat $s0 $sf => $panicBody
        onExit  := fun $binderPat $exitId $s0 $sf => $exitBody
        onOom   := fun $binderPat $s0 $sf => $oomBody)

/-- Expand a `c_spec` or `rust_spec` declaration (either tuple-backed or struct-backed `[a : T]`)
    into a `def` or `abbrev` of type `Spec α`.

    If the load address is bound (`load_addr b` clause, `(load_addr b)` header binder, or an
    implicit free `base` in the clauses), `(b : BitVec 64)` is emitted as
    the final binder after all `ctx` / `{...}` binders, so that a partial application to the
    context arguments is a `BaseSpec α`. -/
def expandSpecDecl (isAbbrev : Bool) (doc? : Option (TSyntax `Lean.Parser.Command.docComment))
    (name : Ident) (binders : Array (TSyntax `abiParamBinder))
    (retOpt? : Option (TSyntax `abiRetSpec))
    (clauses : Array (TSyntax `specClause)) : MacroM Command := do
  let s0 := mkIdent `s0
  let sf := mkIdent `sf
  let mut ctxBinders : Array (TSyntax ``Lean.Parser.Term.bracketedBinder) := #[]
  let mut structSpec? : Option (Ident × Term) := none
  let mut binderIds : Array Ident := #[]
  let mut binderTypes : Array Term := #[]
  let mut userNames : Array Name := #[]
  let mut regEqs : Array Term := #[]
  let mut regIdx : Nat := 0
  let mut loadAddr? : Option Ident := none
  let dupLoadAddrMsg :=
    "duplicate load address binding: at most one 'load_addr <ident>' may appear in a specification"
  for c in clauses do
    if let `(specClause| load_addr $b:ident) := c then
      if loadAddr?.isSome then Macro.throwErrorAt c dupLoadAddrMsg
      loadAddr? := some b
  for b in binders do
    match b with
    | `(abiParamBinder| (load_addr $x:ident)) =>
      if loadAddr?.isSome then Macro.throwErrorAt b dupLoadAddrMsg
      loadAddr? := some x
    | `(abiParamBinder| {$[$xs:ident]* : $ty:term}) =>
      let resolvedTy ← resolveAbiLeanType ty
      let bb ← `(bracketedBinder| {$[$xs:ident]* : $resolvedTy})
      ctxBinders := ctxBinders.push bb
      for x in xs do userNames := userNames.push x.getId
    | `(abiParamBinder| ($tag:ident $[$xs:ident]* : $ty:term)) =>
      if (tag.getId == `ctx || tag.getId == `context) && !xs.isEmpty then
        let resolvedTy ← resolveAbiLeanType ty
        let bb ← `(bracketedBinder| ($[$xs:ident]* : $resolvedTy))
        ctxBinders := ctxBinders.push bb
        for x in xs do userNames := userNames.push x.getId
      else
        for x in #[tag] ++ xs do
          let (some leanTy, eqs, nextIdx) ← expandAbiParam s0 x ty none regIdx
            | Macro.throwUnsupported
          binderIds := binderIds.push x
          binderTypes := binderTypes.push leanTy
          userNames := userNames.push x.getId
          regEqs := regEqs ++ eqs
          regIdx := nextIdx
    | `(abiParamBinder| [$sv:ident : $st:term]) =>
      if structSpec?.isSome then
        Macro.throwError "duplicate struct-backed '[var : Type]' binder in specification header"
      structSpec? := some (sv, st)
      userNames := userNames.push sv.getId
    | `(abiParamBinder| (ghost $[$xs:ident]* : $ty:term)) =>
      let resolvedTy ← resolveAbiLeanType ty
      for x in xs do
        binderIds := binderIds.push x
        binderTypes := binderTypes.push resolvedTy
        userNames := userNames.push x.getId
    | `(abiParamBinder| (_ : $ty:term @ $reg:term := $val:term)) =>
      let (_, eqs, nextIdx) ← expandAbiParam s0 val ty (some reg) regIdx
      regEqs := regEqs ++ eqs
      regIdx := nextIdx
    | `(abiParamBinder| (_ : $ty:term := $val:term)) =>
      let (_, eqs, nextIdx) ← expandAbiParam s0 val ty none regIdx
      regEqs := regEqs ++ eqs
      regIdx := nextIdx
    | `(abiParamBinder| (_ : $ty:term)) =>
      let (_, _, nextIdx) ← expandAbiParam s0 (← `(_)) ty none regIdx
      regIdx := nextIdx
    | `(abiParamBinder| ($x:ident : $ty:term @ $reg:term)) =>
      let (some leanTy, eqs, nextIdx) ← expandAbiParam s0 x ty (some reg) regIdx
        | Macro.throwUnsupported
      binderIds := binderIds.push x
      binderTypes := binderTypes.push leanTy
      userNames := userNames.push x.getId
      regEqs := regEqs ++ eqs
      regIdx := nextIdx
    | `(abiParamBinder| ($x:ident : $ty:term)) =>
      let (some leanTy, eqs, nextIdx) ← expandAbiParam s0 x ty none regIdx
        | Macro.throwUnsupported
      binderIds := binderIds.push x
      binderTypes := binderTypes.push leanTy
      userNames := userNames.push x.getId
      regEqs := regEqs ++ eqs
      regIdx := nextIdx
    | _ => Macro.throwUnsupported
  let (specType, binderPat) ← match structSpec? with
    | some (sv, st) =>
      for x in binderIds do
        if !x.getId.toString.startsWith s!"{sv.getId}." then
          Macro.throwError s!"In struct-backed specifications '[{sv.getId} : {st}]', declare ghost variable '{x.getId}' as a field of '{st}' instead of a tuple binder"
      pure (st, ← `($sv))
    | none =>
      let gTy : Term ← match binderTypes.toList.reverse with
        | [] => `(Unit)
        | last :: revInit => revInit.foldlM (fun acc ty => `($ty × $acc)) last
      let bPat : Term ← match binderIds.toList.reverse with
        | [] => `(_)
        | [single] => `($single)
        | last :: revInit =>
          revInit.foldlM (fun acc (id : Ident) => `(($id, $acc))) (← `($last))
      pure (gTy, bPat)
  let retSpec? ← parseRetSpec? retOpt?
  let (preRaw, postRaw, onPanicRaw?, onExitRaw?, onOomRaw?) ← expandSpecClauses s0 sf regEqs retSpec? clauses
  -- Implicit fallback: a free `base` in the clauses (with no explicit load-address binding and no
  -- user binder named `base`) binds the load address as `base`.
  let usesFreeBase := loadAddr?.isNone && !userNames.contains `base &&
    (stxMentionsFreeIdent `base 64 preRaw.raw ||
     stxMentionsFreeIdent `base 64 postRaw.raw ||
     (onPanicRaw?.map (fun t => stxMentionsFreeIdent `base 64 t.raw)).getD false ||
     (onExitRaw?.map (fun (_, t) => stxMentionsFreeIdent `base 64 t.raw)).getD false ||
     (onOomRaw?.map (fun t => stxMentionsFreeIdent `base 64 t.raw)).getD false)
  let baseId := mkIdent `base
  if usesFreeBase then
    loadAddr? := some baseId
  -- The load-address binder is always the final curried parameter (after every `ctx` binder), so
  -- `name ctxArgs.. : BaseSpec α` works with `ToBaseSpec` regardless of the number of `ctx` args.
  if let some b := loadAddr? then
    if userNames.contains b.getId then
      Macro.throwErrorAt b s!"load address name '{b.getId}' clashes with another specification binder"
    let baseBb ← `(bracketedBinder| ($b : BitVec 64))
    ctxBinders := ctxBinders.push baseBb
  let substStates (t : Term) : Term :=
    let t1 := if userNames.contains `s0 then t else replaceIdentInTerm `s0 s0 t
    let t2 := if userNames.contains `sf then t1 else replaceIdentInTerm `sf sf t1
    if usesFreeBase then replaceIdentInTerm `base baseId t2 else t2
  let preBody := substStates preRaw
  let postBody := substStates postRaw
  let onPanic? := onPanicRaw?.map substStates
  let onExit? := onExitRaw?.map fun (cId, eBody) => (cId, substStates eBody)
  let onOom? := onOomRaw?.map substStates
  mkSpecDeclCmd isAbbrev doc? name ctxBinders specType binderPat s0 sf preBody postBody onPanic? onExit? onOom?

/-- Declarative C/AAPCS64 function specification command (`def` or `abbrev`). -/
syntax (docComment)? ("abbrev ")? "c_spec " ident
    (abiParamBinder)* (abiRetSpec)? ("where")? (specClause)* : command

macro_rules
  | `($[$doc?:docComment]? c_spec $name:ident $[$bs:abiParamBinder]* $[$ret?:abiRetSpec]? $[where]? $[$cs:specClause]*) =>
    expandSpecDecl false doc? name bs ret? cs
  | `($[$doc?:docComment]? abbrev c_spec $name:ident $[$bs:abiParamBinder]* $[$ret?:abiRetSpec]? $[where]? $[$cs:specClause]*) =>
    expandSpecDecl true doc? name bs ret? cs

end SpecDSL

meta section RustSpecDSL

open Lean

/-- Declarative Rust function specification command (`def` or `abbrev`); same DSL and expansion
    as `c_spec`. -/
syntax (docComment)? ("abbrev ")? "rust_spec " ident
    (abiParamBinder)* (abiRetSpec)? ("where")? (specClause)* : command

macro_rules
  | `($[$doc?:docComment]? rust_spec $name:ident $[$bs:abiParamBinder]* $[$ret?:abiRetSpec]? $[where]? $[$cs:specClause]*) =>
    expandSpecDecl false doc? name bs ret? cs
  | `($[$doc?:docComment]? abbrev rust_spec $name:ident $[$bs:abiParamBinder]* $[$ret?:abiRetSpec]? $[where]? $[$cs:specClause]*) =>
    expandSpecDecl true doc? name bs ret? cs

end RustSpecDSL

end Arm64
