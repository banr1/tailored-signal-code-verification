/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import ProofLib
public import ProofLib.Placed
public import ProofLib.GenPlacedFetches
meta import ProofLib.SepLogic.WP.ProjGuardAttr

/-!
# `wp_entry` on Placed Libraries

Regression tests for `wp_entry` and `wpp_entry` on placed programs (`gen_placed_fnOffs`,
shifted-base reducible wrappers, local callee bridging, table-projection guards, and
`MultiPlacedLib.SymIndex` diagnostics).
-/

@[expose] public section

namespace Examples.Testing.PlacedEntry

open Arm64 Arm64.Obj ProofLib ProofLib.ProgramReflection

set_option linter.literalFetch false

/-- `alpha: NOP; RET; widget: NOP; NOP; RET`, with no relocations. -/
def widgetBlk : CodeBlock where
  code := bytesOfWordLE 0xd503201f#32 ++ bytesOfWordLE 0xd65f03c0#32 ++
    bytesOfWordLE 0xd503201f#32 ++ bytesOfWordLE 0xd503201f#32 ++ bytesOfWordLE 0xd65f03c0#32
  symbols := [("alpha", 0), ("widget", 8)]

def widgetLib : PlacedLib where
  name := "widget"
  text := widgetBlk
  exports := ["alpha", "widget"]

def widgetPC (pl : Placement) : Program := widgetLib.program pl

def widgetTextProg : Program := { code := widgetBlk.code, symbols := widgetBlk.symbols }

def widgetTree : WordTree := word_tree_of% widgetTextProg

theorem widget_code_eq : widgetLib.text.code = widgetTree.toBytes := by rfl_kernel

theorem widget_tree_size : widgetTree.checkSize? = some 5 := by rfl_kernel

def widgetSymChars : List (List Char × Nat) := sym_chars_of% widgetTextProg

theorem widget_symbols_eq : widgetLib.text.symbols = toStringSymbols widgetSymChars := by
  rfl_kernel

theorem widget_symbols_fresh : allFreshCharSymbols widgetSymChars = true := by rfl_kernel

gen_placed_fetches widgetPC widgetLib widgetTree widget_code_eq widget_tree_size [0x0 → 0x10]
gen_placed_fnOffs widgetPC widgetLib widgetSymChars widget_symbols_eq widget_symbols_fresh

class WidgetPlacement where
  pl : Placement
  placeable : widgetLib.Placeable pl

def widgetCC [WidgetPlacement] : Program := widgetLib.program WidgetPlacement.pl

gen_placed_fetches widgetCC widgetLib widgetTree widget_code_eq widget_tree_size
  via_placement WidgetPlacement.pl WidgetPlacement.placeable [0x0 → 0x10]
gen_placed_fnOffs widgetCC widgetLib widgetSymChars widget_symbols_eq widget_symbols_fresh

def keepX0 : Spec (BitVec 64) where
  pre := fun v s0 => ⌜s0.readReg64 .x0 = v⌝
  post := fun v _ sf => ⌜sf.readReg64 .x0 = v⌝

/-! ## Registry -/

/-- info: [(alpha, (0, (8, true))), (widget, (8, (0, true)))] -/
#guard_msgs in
run_meta do
  let env ← Lean.getEnv
  let es := (fnEntryExt.getState env).filter (·.codeConst == ``widgetPC)
  Lean.logInfo m!"{es.toList.map fun e => (e.sym, e.off, e.sizeBytes, e.placed)}"

/-! ## Entry Resolution Tests -/

example (pl : Placement) (b : BitVec 64) (H : String → Option (State → State)) :
    subroutine_ok ((widgetPC pl).rebase b H) (((widgetPC pl).rebase b H).fnAddr "widget")
      keepX0 := by
  wp_entry "widget" v s0
  wp_steps
  wp_done

example (pl : Placement) (b : BitVec 64) (H : String → Option (State → State)) :
    subroutine_ok ((widgetPC pl).rebase b H) (((widgetPC pl).rebase b H).fnAddr "alpha")
      keepX0 := by
  wp_entry "alpha" v s0
  wp_steps
  wp_done

example (pl : Placement) (b : BitVec 64) (H : String → Option (State → State)) :
    subroutine_ok ((widgetPC pl).rebase b H) (b + 0x8#64) keepX0 := by
  wp_entry
  wp_steps
  wp_done

example (pl : Placement) (b : BitVec 64) (H : String → Option (State → State)) :
    subroutine_ok ((widgetPC pl).rebase b H) b keepX0 := by
  wp_entry "alpha"
  wp_steps
  wp_done

example [WidgetPlacement] (b : BitVec 64) (H : String → Option (State → State)) :
    subroutine_ok (widgetCC.rebase b H) ((widgetCC.rebase b H).fnAddr "widget") keepX0 := by
  wp_entry "widget" v s0
  wp_steps
  wp_done

example [WidgetPlacement] (b : BitVec 64) (H : String → Option (State → State)) :
    subroutine_ok (widgetCC.rebase b H) ((widgetCC.rebase b H).fnAddr "alpha") keepX0 := by
  wpp_entry "alpha" v s0
  apply SepWPp.of_sepWP_ret
  wp_steps
  wp_done

example [WidgetPlacement] (b : BitVec 64) (H : String → Option (State → State))
    (_hw : subroutine_ok (widgetCC.rebase b H) ((widgetCC.rebase b H).fnAddr "widget") keepX0) :
    subroutine_ok (widgetCC.rebase b H) ((widgetCC.rebase b H).fnAddr "alpha") keepX0 := by
  wp_entry "alpha" v s0
  guard_hyp _hw : subroutine_ok (widgetCC.rebase b H) (b + BitVec.ofNat 64 8) _
  wp_steps
  wp_done

/-- Rewriting an earlier local callee hypothesis refreshes `FVarId`s for subsequent callees. -/
example [WidgetPlacement] (b : BitVec 64) (H : String → Option (State → State))
    (_hw1 : subroutine_ok (widgetCC.rebase b H) ((widgetCC.rebase b H).fnAddr "alpha") keepX0)
    (_hw2 : subroutine_ok (widgetCC.rebase b H) ((widgetCC.rebase b H).fnAddr "widget") keepX0) :
    subroutine_ok (widgetCC.rebase b H) ((widgetCC.rebase b H).fnAddr "alpha") keepX0 := by
  wp_entry "alpha" v s0
  guard_hyp _hw1 : subroutine_ok (widgetCC.rebase b H) (b + BitVec.ofNat 64 0) _
  guard_hyp _hw2 : subroutine_ok (widgetCC.rebase b H) (b + BitVec.ofNat 64 8) _
  wp_steps
  wp_done

/-! ## Rejection Checks -/

/-- error: wp_entry: no registered function entry found (symbol: some (gamma)) -/
#guard_msgs (substring := true) in
example (pl : Placement) (b : BitVec 64) (H : String → Option (State → State)) :
    subroutine_ok ((widgetPC pl).rebase b H) (((widgetPC pl).rebase b H).fnAddr "gamma")
      keepX0 := by
  wp_entry "gamma"

-- A callee hypothesis on a different base `b'` is left untouched by `bridgeLocalCallees`.
/-- error: Hypothesis `_hother` has type
  subroutine_ok (widgetCC.rebase b' H) ((widgetCC.rebase b' H).fnAddr "widget") -/
#guard_msgs (substring := true) in
example [WidgetPlacement] (b b' : BitVec 64) (H : String → Option (State → State))
    (_hother : subroutine_ok (widgetCC.rebase b' H) ((widgetCC.rebase b' H).fnAddr "widget") keepX0) :
    subroutine_ok (widgetCC.rebase b H) ((widgetCC.rebase b H).fnAddr "alpha") keepX0 := by
  wp_entry "alpha" v s0
  guard_hyp _hother : subroutine_ok (widgetCC.rebase b' H) (b' + BitVec.ofNat 64 8) _
  wp_steps
  wp_done

/-! ## Shifted-Base Reducible Wrapper (`b + bOff#64`) -/

/-- Reducible wrapper rebasing `widgetPC pl` at `b + 0x100#64` (virtual-origin block convention). -/
abbrev widgetShifted (pl : Placement) (b : BitVec 64)
    (H : String → Option (State → State)) : Program :=
  (widgetPC pl).rebase (b + 0x100#64) H

example (pl : Placement) (b : BitVec 64) (H : String → Option (State → State)) :
    subroutine_ok (widgetShifted pl b H) (b + 0x100#64) keepX0 := by
  wp_entry
  wp_steps
  wp_done

example (pl : Placement) (b : BitVec 64) (H : String → Option (State → State)) :
    subroutine_ok (widgetShifted pl b H) (b + 0x108#64) keepX0 := by
  wp_entry
  wp_steps
  wp_done

/-- error: wp_entry: no registered function entry found -/
#guard_msgs (substring := true) in
example (pl : Placement) (b : BitVec 64) (H : String → Option (State → State)) :
    subroutine_ok (widgetShifted pl b H) (b + 0x80#64) keepX0 := by
  wp_entry

/-- error: wp_step: could not fetch/decode instruction at PC `b + 252#64` -/
#guard_msgs (substring := true) in
example (pl : Placement) (b : BitVec 64) (s : State)
    (hpc : s.pc = b + 0xfc#64) (hrun : s.status = .Running)
    (Q : State → SepProp → Prop) :
    SepWP (widgetShifted pl b (fun _ => none)) (b + 0x104#64) s emp Q (fun _ => emp) := by
  wp_step

/-! ## Table-Projection Guards and `maxRecDepth` Diagnostics -/

-- Build a 600-entry symbol/name spine directly in `MetaM` so `largeImage`, `largeLinkedImage`,
-- `largeInternedLib`, `largeInternedLayout`, and `largeMultiLib` have a concrete 600-deep
-- `List.cons` spine without large source literals.
section

run_meta do
  let u0 : Lean.Level := .zero
  let strTy := Lean.mkConst ``String
  let natTy := Lean.mkConst ``Nat
  let bv64Ty := Lean.mkApp (Lean.mkConst ``BitVec) (Lean.toExpr (64 : Nat))
  let pairStrNatTy := Lean.mkApp2 (Lean.mkConst ``Prod [u0, u0]) strTy natTy
  let pairNatNatTy := Lean.mkApp2 (Lean.mkConst ``Prod [u0, u0]) natTy natTy
  let mut symElems : Array Lean.Expr := #[]
  let mut nameElems : Array Lean.Expr := #[]
  let mut idSymElems : Array Lean.Expr := #[]
  let mut addrElems : Array Lean.Expr := #[]
  for i in [:600] do
    let s := Lean.mkStrLit s!"sym_{i}"
    let n := Lean.toExpr i
    let off := Lean.toExpr (4 * i)
    symElems := symElems.push (Lean.mkApp4 (Lean.mkConst ``Prod.mk [u0, u0]) strTy natTy s off)
    nameElems := nameElems.push s
    idSymElems := idSymElems.push (Lean.mkApp4 (Lean.mkConst ``Prod.mk [u0, u0]) natTy natTy n off)
    addrElems := addrElems.push (Lean.toExpr (BitVec.ofNat 64 (0x400000 + 4 * i)))
  let mkList (ty : Lean.Expr) (xs : Array Lean.Expr) : Lean.Expr :=
    xs.foldr (fun x acc => Lean.mkApp3 (Lean.mkConst ``List.cons [u0]) ty x acc)
      (Lean.mkApp (Lean.mkConst ``List.nil [u0]) ty)
  let symsList := mkList pairStrNatTy symElems
  let namesList := mkList strTy nameElems
  let idSymsList := mkList pairNatNatTy idSymElems
  let addrsList := mkList bv64Ty addrElems
  for (nm, ty, val) in #[
    (`Examples.Testing.PlacedEntry.largeSyms, Lean.mkApp (Lean.mkConst ``List [u0]) pairStrNatTy, symsList),
    (`Examples.Testing.PlacedEntry.largeNames, Lean.mkApp (Lean.mkConst ``List [u0]) strTy, namesList),
    (`Examples.Testing.PlacedEntry.largeIdSyms, Lean.mkApp (Lean.mkConst ``List [u0]) pairNatNatTy, idSymsList),
    (`Examples.Testing.PlacedEntry.largeAddrs, Lean.mkApp (Lean.mkConst ``List [u0]) bv64Ty, addrsList)
  ] do
    Lean.addDecl (.defnDecl {
      name := nm
      levelParams := []
      type := ty
      value := val
      hints := .abbrev
      safety := .safe
    })
    Lean.modifyEnv (Lean.addNoncomputable · nm)

noncomputable def largeImage : Obj.Image where
  base := 0x400000#64
  code := widgetBlk.code
  dataAddr := 0x410000#64
  data := []
  roData := []
  externData := []
  gotAddr := 0x420000#64
  got := []
  symbols := largeSyms
  stubs := []

noncomputable def largeLinkedImage : Obj.LinkedImage where
  code := widgetBlk.code
  dataOff := 0x10000
  data := []
  gotOff := 0x20000
  symbols := largeSyms
  stubs := []

noncomputable abbrev largeInternedLib : Obj.Interned.Lib where
  name := "large_widget"
  names := largeNames
  code := widgetBlk.code
  symbols := largeIdSyms

noncomputable abbrev largeInternedLayout : Obj.Interned.Layout where
  base := 0x400000#64
  addrs := largeAddrs

noncomputable def largeMultiLib : Obj.MultiPlacedLib where
  name := "large_multi"
  blocks := [{ code := widgetBlk.code, symbols := largeSyms }]

/-- Spec referencing both ground and symbolic 600-entry `Obj.Image`, `Obj.LinkedImage`,
    `Obj.Interned.Lib` / `Layout` (`abbrev`), and `Obj.MultiPlacedLib` table projections. -/
noncomputable def keepX0WithLargeTables (mpl : MultiPlacement) (syms : List (String × Nat)) : Spec (BitVec 64) where
  pre := fun v s0 =>
    ⌜s0.readReg64 .x0 = v ∧
      largeImage.symbols = largeLinkedImage.symbols ∧
      largeImage.symbols = syms ∧
      largeInternedLib.names.length = largeInternedLayout.addrs.length⌝ ∗
    (largeMultiLib.resolve mpl "ro_slot" ↦₆₄ᵣ largeMultiLib.fnAddr mpl "sym_0")
  post := fun v _ sf =>
    ⌜sf.readReg64 .x0 = v ∧
      largeImage.symbols = largeLinkedImage.symbols ∧
      largeImage.symbols = syms ∧
      largeInternedLib.names.length = largeInternedLayout.addrs.length⌝ ∗
    (largeMultiLib.resolve mpl "ro_slot" ↦₆₄ᵣ largeMultiLib.fnAddr mpl "sym_0")

-- Build a spec whose body directly embeds an unguarded 500-deep `And` chain so `wp_unfold_specs`
-- inside `wp_entry` reliably hits `maxRecDepth 350` without overflowing theorem-header elaboration.
run_meta do
  let mut deepProp : Lean.Expr := Lean.mkConst ``True
  for _ in [:500] do
    deepProp := Lean.mkApp2 (Lean.mkConst ``And) (Lean.mkConst ``True) deepProp
  let bv64Ty := Lean.mkApp (Lean.mkConst ``BitVec) (Lean.toExpr (64 : Nat))
  let stateTy := Lean.mkConst ``Arm64.State
  let preExpr :=
    Lean.mkLambda `v .default bv64Ty <|
      Lean.mkLambda `s0 .default stateTy <|
        Lean.mkApp (Lean.mkConst ``Arm64.SepProp.pure) deepProp
  let postExpr :=
    Lean.mkLambda `v .default bv64Ty <|
      Lean.mkLambda `s0 .default stateTy <|
        Lean.mkLambda `sf .default stateTy <|
          Lean.mkConst ``Arm64.SepProp.emp
  let falsePred3 :=
    Lean.mkLambda `v .default bv64Ty <|
      Lean.mkLambda `s0 .default stateTy <|
        Lean.mkLambda `sf .default stateTy <|
          Lean.mkApp (Lean.mkConst ``Arm64.SepProp.pure) (Lean.mkConst ``False)
  let exitExpr :=
    Lean.mkLambda `v .default bv64Ty <|
      Lean.mkLambda `code .default bv64Ty <|
        Lean.mkLambda `s0 .default stateTy <|
          Lean.mkLambda `sf .default stateTy <|
            Lean.mkApp (Lean.mkConst ``Arm64.SepProp.pure) (Lean.mkConst ``False)
  let specVal ← Lean.Meta.mkAppM ``Arm64.Spec.mk #[preExpr, postExpr, falsePred3, exitExpr, falsePred3]
  let specTy ← Lean.Meta.inferType specVal
  Lean.addDecl (.defnDecl {
    name := `Examples.Testing.PlacedEntry.deepUnfoldedSpec
    levelParams := []
    type := specTy
    value := specVal
    hints := .regular 0
    safety := .safe
  })
  Lean.modifyEnv (Lean.addNoncomputable · `Examples.Testing.PlacedEntry.deepUnfoldedSpec)

set_option maxRecDepth 350 in
example (pl : Placement) (mpl : MultiPlacement) (b : BitVec 64)
    (H : String → Option (State → State)) (syms : List (String × Nat))
    (_hfn : largeMultiLib.fnAddr mpl "sym_599" =
      (largeInternedLayout.toPlacement largeInternedLib.names).ρ "sym_599") :
    subroutine_ok ((widgetPC pl).rebase b H) (((widgetPC pl).rebase b H).fnAddr "widget")
      (keepX0WithLargeTables mpl syms) := by
  wp_entry "widget" v s0
  wp_steps
  wp_done

set_option maxRecDepth 350 in
example (pl : Placement) (mpl : MultiPlacement) (b : BitVec 64)
    (H : String → Option (State → State)) (syms : List (String × Nat)) :
    subroutine_ok ((widgetPC pl).rebase b H) (((widgetPC pl).rebase b H).fnAddr "alpha")
      (keepX0WithLargeTables mpl syms) := by
  wpp_entry "alpha" v s0
  apply SepWPp.of_sepWP_ret
  wp_steps
  wp_done

/-- error: wp_entry: unreduced symbol/address lookup (`Arm64.Obj.MultiPlacedLib.fnAddr`) in entry expression
  largeMultiLib.fnAddr mpl "widget"
hint: pre-fold the entry address before calling `wp_entry` -/
#guard_msgs (substring := true) in
set_option maxRecDepth 350 in
example (pl : Placement) (mpl : MultiPlacement) (b : BitVec 64)
    (H : String → Option (State → State)) :
    subroutine_ok ((widgetPC pl).rebase b H) (largeMultiLib.fnAddr mpl "widget") keepX0 := by
  wp_entry

/-- error: wp_entry: unreduced symbol/address lookup (`Arm64.Obj.PlacedLib.fnAddr`) in entry expression
  widgetLib.fnAddr pl "widget"
hint: pre-fold the entry address before calling `wp_entry` -/
#guard_msgs (substring := true) in
example (pl : Placement) (b : BitVec 64) (H : String → Option (State → State)) :
    subroutine_ok ((widgetPC pl).rebase b H) (widgetLib.fnAddr pl "widget") keepX0 := by
  wp_entry "widget"

/-- error: wp_entry: could not extract `<codeConst>.rebase b H` from program
  largeMultiLib.blockProgram mpl 0
hint: program uses unrewritten `PlacedLib.program` / `MultiPlacedLib.blockProgram` -/
#guard_msgs (substring := true) in
set_option maxRecDepth 350 in
example (mpl : MultiPlacement) :
    subroutine_ok (largeMultiLib.blockProgram mpl 0) (largeMultiLib.fnAddr mpl "sym_0") keepX0 := by
  wp_entry

/-- error: wp_entry: maximum recursion depth (`maxRecDepth`) reached during entry setup (saw `Arm64.Obj.MultiPlacedLib.fnAddr` in goal/context)
hint: pre-fold concrete `Obj.Image` / `Obj.LinkedImage` / `Obj.Interned` / `PlacedLib` / symbol-table or address projections before calling `wp_entry` -/
#guard_msgs (substring := true) in
set_option maxRecDepth 350 in
example (pl : Placement) (mpl : MultiPlacement) (b : BitVec 64)
    (H : String → Option (State → State))
    (_hfn : largeMultiLib.fnAddr mpl "sym_0" = b) :
    subroutine_ok ((widgetPC pl).rebase b H) (((widgetPC pl).rebase b H).fnAddr "widget")
      deepUnfoldedSpec := by
  wp_entry "widget" v s0

-- Unit check: `hasConcreteGuardedTableTerm` inspects the `blocks` receiver (arg 1 for
-- `lookupBlockSym`, arg 2 for `lookupBlockSymAux`), not the leading `name : String` argument.
run_meta do
  let strTy := Lean.mkConst ``String
  let blocksTy ← Lean.Meta.mkAppM ``List #[Lean.mkConst ``Obj.CodeBlock]
  Lean.Meta.withLocalDeclD `blocks blocksTy fun blocksFVar =>
  Lean.Meta.withLocalDeclD `sym strTy fun symFVar => do
    let varRecv1 ← Lean.Meta.mkAppM ``Obj.lookupBlockSym #[Lean.toExpr "widget", blocksFVar]
    let varRecv2 ← Lean.Meta.mkAppM ``Obj.lookupBlockSymAux #[Lean.toExpr "widget", Lean.toExpr (0 : Nat), blocksFVar]
    let concreteBlocks ← Lean.Meta.mkAppM ``Obj.MultiPlacedLib.blocks #[Lean.mkConst ``largeMultiLib]
    let concRecv1 ← Lean.Meta.mkAppM ``Obj.lookupBlockSym #[symFVar, concreteBlocks]
    let concRecv2 ← Lean.Meta.mkAppM ``Obj.lookupBlockSymAux #[symFVar, Lean.toExpr (0 : Nat), concreteBlocks]
    if ProofLib.hasConcreteGuardedTableTerm varRecv1 then
      throwError "expected false on FVar `blocks` receiver in `lookupBlockSym`"
    if ProofLib.hasConcreteGuardedTableTerm varRecv2 then
      throwError "expected false on FVar `blocks` receiver in `lookupBlockSymAux`"
    unless ProofLib.hasConcreteGuardedTableTerm concRecv1 do
      throwError "expected true on concrete `blocks` receiver in `lookupBlockSym`"
    unless ProofLib.hasConcreteGuardedTableTerm concRecv2 do
      throwError "expected true on concrete `blocks` receiver in `lookupBlockSymAux`"

-- Regression: preserving `largeMultiLib.dataInit mpl` (`SepProp`) must keep `decide := true`
-- active on ground arithmetic conditions in `wp_norm_goal` / `wp_done`, and local `CodeBlock.target`
-- rewrite hypotheses on `def`-backed libraries remain eligible in `wp_norm_goal`.
noncomputable def keepX0WithDataInitAndGroundCond (mpl : MultiPlacement) (pl : Placement) : Spec (BitVec 64) where
  pre := fun v s0 =>
    ⌜s0.readReg64 .x0 = v ∧
      widgetLib.text.target pl { off := 0, kind := .adrpHi21, sym := "ext" } = pl.ρ "ext"⌝ ∗
    largeMultiLib.dataInit mpl
  post := fun v _ sf =>
    ⌜sf.readReg64 .x0 = v ∧
      (if (3#64 + 1#64 : BitVec 64).toNat = 4 then
        widgetLib.text.target pl { off := 0, kind := .adrpHi21, sym := "ext" } = pl.ρ "ext"
       else False)⌝ ∗
    largeMultiLib.dataInit mpl

set_option maxRecDepth 350 in
example (pl : Placement) (mpl : MultiPlacement) (b : BitVec 64)
    (H : String → Option (State → State)) :
    subroutine_ok ((widgetPC pl).rebase b H) (((widgetPC pl).rebase b H).fnAddr "widget")
      (keepX0WithDataInitAndGroundCond mpl pl) := by
  wp_entry "widget" v s0
  wp_steps
  wp_done

/-! ## Registered `Program.fnOff` in Goal Entry and Local Callee Hypotheses -/

theorem widgetTextProg_fnOff_0x0 : widgetTextProg.fnOff "alpha" = 0 := by decide
theorem widgetTextProg_fnOff_0x8 : widgetTextProg.fnOff "widget" = 8 := by decide

register_fn_entry "alpha" widgetTextProg widgetTextProg widgetTextProg_fnOff_0x0 0 0
register_fn_entry "widget" widgetTextProg widgetTextProg widgetTextProg_fnOff_0x8 8 0

example (pl : Placement) (b : BitVec 64) (H : String → Option (State → State))
    (_hw : subroutine_ok ((widgetPC pl).rebase b H)
      (b + BitVec.ofNat 64 ((widgetPC pl).fnOff "alpha")) keepX0) :
    subroutine_ok ((widgetPC pl).rebase b H)
      (b + BitVec.ofNat 64 ((widgetPC pl).fnOff "widget")) keepX0 := by
  wp_entry
  guard_hyp _hw : subroutine_ok ((widgetPC pl).rebase b H) (b + BitVec.ofNat 64 0) _
  wp_steps
  wp_done

example (b : BitVec 64) (H : String → Option (State → State))
    (hfetch : (widgetTextProg.rebase b H).fetch
      ((widgetTextProg.rebase b H).fnAddr "alpha") = some (.b 8#64))
    (hcal : subroutine_ok (widgetTextProg.rebase b H)
      (b + BitVec.ofNat 64 (widgetTextProg.fnOff "widget")) keepX0) :
    subroutine_ok (widgetTextProg.rebase b H)
      (b + BitVec.ofNat 64 (widgetTextProg.fnOff "alpha")) keepX0 := by
  wp_entry
  guard_hyp hcal : subroutine_ok (widgetTextProg.rebase b H) (_ + 8#64) _
  wp_tailcall hcal
  wp_done

example (pl : Placement) (b : BitVec 64) (H : String → Option (State → State))
    (_hw1 : subroutine_ok ((widgetPC pl).rebase b H)
      (b + BitVec.ofNat 64 ((widgetPC pl).fnOff "alpha")) keepX0)
    (_hw2 : subroutine_ok ((widgetPC pl).rebase b H)
      (((widgetPC pl).rebase b H).fnAddr "alpha") keepX0) :
    subroutine_ok ((widgetPC pl).rebase b H)
      (b + BitVec.ofNat 64 ((widgetPC pl).fnOff "widget")) keepX0 := by
  wp_entry
  guard_hyp _hw1 : subroutine_ok ((widgetPC pl).rebase b H) (b + BitVec.ofNat 64 0) _
  guard_hyp _hw2 : subroutine_ok ((widgetPC pl).rebase b H) (b + 0#64) _
  wp_steps
  wp_done

def multiCalleeProg : Program where
  code := widgetBlk.code
  symbols := [("alpha", 0), ("widget", 8), ("omega_fn", 12)]

theorem multiCalleeProg_fnOff_0x0 : multiCalleeProg.fnOff "alpha" = 0 := by decide
theorem multiCalleeProg_fnOff_0x8 : multiCalleeProg.fnOff "widget" = 8 := by decide
theorem multiCalleeProg_fnOff_0xc : multiCalleeProg.fnOff "omega_fn" = 12 := by decide

register_fn_entry "alpha" multiCalleeProg multiCalleeProg multiCalleeProg_fnOff_0x0 0 0
register_fn_entry "widget" multiCalleeProg multiCalleeProg multiCalleeProg_fnOff_0x8 8 0
register_fn_entry "omega_fn" multiCalleeProg multiCalleeProg multiCalleeProg_fnOff_0xc 12 0

example (b : BitVec 64) (H : String → Option (State → State))
    (hfetch : (multiCalleeProg.rebase b H).fetch
      ((multiCalleeProg.rebase b H).fnAddr "alpha") = some (.b 12#64))
    (_hcal1 : subroutine_ok (multiCalleeProg.rebase b H)
      (b + BitVec.ofNat 64 (multiCalleeProg.fnOff "widget")) keepX0)
    (hcal2 : subroutine_ok (multiCalleeProg.rebase b H)
      (b + BitVec.ofNat 64 (multiCalleeProg.fnOff "omega_fn")) keepX0) :
    subroutine_ok (multiCalleeProg.rebase b H)
      (b + BitVec.ofNat 64 (multiCalleeProg.fnOff "alpha")) keepX0 := by
  wp_entry
  guard_hyp _hcal1 : subroutine_ok (multiCalleeProg.rebase b H) (_ + 8#64) _
  guard_hyp hcal2 : subroutine_ok (multiCalleeProg.rebase b H) (_ + 12#64) _
  wp_tailcall hcal2
  wp_done

-- An unregistered `Program.fnOff` reports an unreduced-lookup error without unfolding symbol tables.
/-- error: wp_entry: unreduced symbol/address lookup (`Arm64.Program.fnOff`) in entry expression -/
#guard_msgs (substring := true) in
set_option maxRecDepth 350 in
example (pl : Placement) (b : BitVec 64) (H : String → Option (State → State)) :
    subroutine_ok ((widgetPC pl).rebase b H)
      (b + BitVec.ofNat 64 ((Program.ofImage largeImage).fnOff "sym_599")) keepX0 := by
  wp_entry

/-! ## `MultiPlacedLib.SymIndex` and `Obj.RelocFnIndex` Guard Coverage -/

def smallIndexedMultiLib : MultiPlacedLib where
  name := "small_indexed"
  blocks := [widgetBlk]
  exports := ["alpha", "widget"]

gen_multi_sym_index smallMultiSymIdx smallIndexedMultiLib

/-- error: wp_entry: unreduced symbol/address lookup (`Arm64.Obj.MultiPlacedLib.SymIndex.fnAddr`) in entry expression -/
#guard_msgs (substring := true) in
example (pl : Placement) (mpl : MultiPlacement) (b : BitVec 64)
    (H : String → Option (State → State)) (idx : smallIndexedMultiLib.SymIndex) :
    subroutine_ok ((widgetPC pl).rebase b H) (idx.fnAddr mpl "widget") keepX0 := by
  wp_entry

/-- error: wp_entry: unreduced symbol/address lookup (`Arm64.Obj.MultiPlacedLib.SymIndex.lookupBlockSym`) in entry expression -/
#guard_msgs (substring := true) in
example (pl : Placement) (b : BitVec 64) (H : String → Option (State → State))
    (idx : smallIndexedMultiLib.SymIndex) :
    subroutine_ok ((widgetPC pl).rebase b H)
      (b + BitVec.ofNat 64 (((idx.lookupBlockSym "widget").map (·.2)).getD 0)) keepX0 := by
  wp_entry

/-- error: wp_entry: unreduced symbol/address lookup (`Arm64.Obj.lookupSymInLists`) in entry expression -/
#guard_msgs (substring := true) in
example (pl : Placement) (b : BitVec 64) (H : String → Option (State → State))
    (symLists : List (List (String × Nat))) :
    subroutine_ok ((widgetPC pl).rebase b H)
      (b + BitVec.ofNat 64 (((lookupSymInLists "widget" 0 symLists).map (·.2)).getD 0)) keepX0 := by
  wp_entry

-- Unit checks:
-- 1. Every single-backtick constant name referenced in `ProjGuardAttr.lean`, `ControlTactics.lean`,
--    and `Entry.lean` resolves in `Lean.getEnv`.
-- 2. `hasConcreteGuardedTableTerm` inspects `recvIdx = 1` for `SymIndex` / `RelocFnIndex` methods
--    (treating symbolic `idx` FVars as non-concrete and concrete `smallMultiSymIdx` as concrete).
run_meta do
  let env ← Lean.getEnv
  for nm in [
      `Arm64.Obj.MultiPlacedLib.SymIndex,
      `Arm64.Obj.MultiPlacedLib.SymIndex.lookupBlockCharSym,
      `Arm64.Obj.MultiPlacedLib.SymIndex.lookupBlockSym,
      `Arm64.Obj.MultiPlacedLib.SymIndex.findDataSymChars,
      `Arm64.Obj.MultiPlacedLib.SymIndex.findDataSym,
      `Arm64.Obj.MultiPlacedLib.SymIndex.resolve,
      `Arm64.Obj.MultiPlacedLib.SymIndex.fnAddr,
      `Arm64.Obj.lookupSymInLists,
      `Arm64.Obj.RelocFnIndex,
      `Arm64.Obj.RelocFnIndex.lookupIdxChars,
      `Arm64.Obj.RelocFnIndex.lookupIdx,
      `Arm64.Obj.RelocFnIndex.findFn?] do
    unless env.contains nm do
      throwError "missing constant referenced in guarded-lookup classifiers: {nm}"
  let idxTy ← Lean.Meta.mkAppM ``Obj.MultiPlacedLib.SymIndex #[Lean.mkConst ``smallIndexedMultiLib]
  let mplTy := Lean.mkConst ``Obj.MultiPlacement
  Lean.Meta.withLocalDeclD `idx idxTy fun idxFVar =>
  Lean.Meta.withLocalDeclD `mpl mplTy fun mplFVar => do
    let varLookup ← Lean.Meta.mkAppM ``Obj.MultiPlacedLib.SymIndex.lookupBlockSym
      #[idxFVar, Lean.toExpr "widget"]
    let varResolve ← Lean.Meta.mkAppM ``Obj.MultiPlacedLib.SymIndex.resolve
      #[idxFVar, mplFVar, Lean.toExpr "widget"]
    let concLookup ← Lean.Meta.mkAppM ``Obj.MultiPlacedLib.SymIndex.lookupBlockSym
      #[Lean.mkConst ``smallMultiSymIdx, Lean.toExpr "widget"]
    let concResolve ← Lean.Meta.mkAppM ``Obj.MultiPlacedLib.SymIndex.resolve
      #[Lean.mkConst ``smallMultiSymIdx, mplFVar, Lean.toExpr "widget"]
    if ProofLib.hasConcreteGuardedTableTerm varLookup then
      throwError "expected false on FVar `idx` receiver in `SymIndex.lookupBlockSym`"
    if ProofLib.hasConcreteGuardedTableTerm varResolve then
      throwError "expected false on FVar `idx` receiver in `SymIndex.resolve`"
    unless ProofLib.hasConcreteGuardedTableTerm concLookup do
      throwError "expected true on concrete `SymIndex` receiver in `SymIndex.lookupBlockSym`"
    unless ProofLib.hasConcreteGuardedTableTerm concResolve do
      throwError "expected true on concrete `SymIndex` receiver in `SymIndex.resolve`"

end

end Examples.Testing.PlacedEntry
